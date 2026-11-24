/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM8CoreParityProofBve0
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullDenseWatchLemmas1
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.MemLemmas
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat M8 Core Parity (`FullM8CoreParity`) K6 Extract/Solve Helpers (`BveK6c0`)

UNSAT-only `Func.wp` sub-phase helpers (`public section`, clean `std3`) for
`full_k6_extract_and_solve_m8_wp`:
1. `M8P6Scr` & `M8K6cTactics` scoped scratch-buffer tactics (`16384 ≤ cap`).
2. Pure BitVec, `TmkZero`, `FullBveEntryOkW`, and `M8K6BufOk` helpers.
3. `m8_k6c_watch_solve_wp` (watch loop, `full_k6_solve_m8`, `full_k6_core_m8`, mask clear/mark).
4. `m8_k6c_copy_clause_wp` (copy `tmp[0..csz)` to `scr[15744 + alen ..]`, header + unit record).
5. `m8_k6c_scan_large_wp` (large-clause literal scan `m < sz`, var registration, `tmp` fill).
6. `m8_k6c_init_solve_wp` (`22` K6 header words, var/lit init loops, `M8K6BufOk` construction).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM8CoreParity

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullDenseWatchHelpers
open LeanQbe.T.Examples.Kissat.FullFastBveBudgets
open LeanQbe.T.Examples.Kissat.FullM6BveFwd
open LeanQbe.T.Examples.Kissat.FullM7BveGates
open Kraken.Bedrock2.Test

open scoped FullArenaTactics

local macro "m8_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

/-! ## 1. `M8P6Scr` & Scoped Scratch Tactics -/

/-- Scratch buffer invariant for fast `u32 *scr` stores in `BveK6c` (`16384 ≤ cap`). -/
def M8P6Scr (cap : Nat) (pScr : BitVec 64) (scr : List (BitVec 32)) : Mem 64 → Prop :=
  fun m => 16384 ≤ cap ∧ scr.length = cap ∧ array (t := i32) pScr scr m

private theorem M8P6Scr_eq (cap : Nat) (pScr : BitVec 64) (scr : List (BitVec 32)) :
    M8P6Scr cap pScr scr =
      (fun m => 16384 ≤ cap ∧ scr.length = cap ∧ array (t := i32) pScr scr m) := rfl

namespace M8K6cTactics

@[scoped bv_c0] theorem m8k6c_fullState_core (co : FullCoreState) (sc : FullScratch) :
    ({ core := co, scratch := sc } : FullState).core = co := rfl

@[scoped bv_c0] theorem m8k6c_fullCore_vals (k : FullCoreState) (t : List (BitVec 32)) :
    ({ k with tmp := t } : FullCoreState).vals = k.vals := rfl

@[scoped bv_c0] theorem m8k6c_fullCore_tmp (k : FullCoreState) (t : List (BitVec 32)) :
    ({ k with tmp := t } : FullCoreState).tmp = t := rfl

@[scoped bv_c0] theorem m8k6c_fullCore_arena (k : FullCoreState) (t : List (BitVec 32)) :
    ({ k with tmp := t } : FullCoreState).arena = k.arena := rfl

@[scoped bv_c0] theorem m8k6c_fullState_scratch (co : FullCoreState) (sc : FullScratch) :
    ({ core := co, scratch := sc } : FullState).scratch = sc := rfl

@[scoped bv_c0] theorem m8k6c_fullScratch_tmk_set2 (s : FullScratch)
    (ws tm : List (BitVec 32)) :
    ({ s with wsort := ws, tarjan_mark := tm } : FullScratch).tarjan_mark = tm := rfl

@[scoped bv_c0] theorem m8k6c_fullScratch_wsort_set2 (s : FullScratch)
    (ws tm : List (BitVec 32)) :
    ({ s with wsort := ws, tarjan_mark := tm } : FullScratch).wsort = ws := rfl

@[scoped bv_c0] theorem m8k6c_fullScratch_buf_set (s : FullScratch)
    (scr : List (BitVec 32)) :
    ({ s with scratch_buf := scr } : FullScratch).scratch_buf = scr := rfl

@[scoped bv_c0] theorem m8k6c_fullState_scratch_buf_set (co : FullCoreState) (sc : FullScratch)
    (scr : List (BitVec 32)) :
    ({ core := co, scratch := { sc with scratch_buf := scr } } :
      FullState).scratch.scratch_buf = scr := rfl

@[scoped bv_c0] theorem m8k6c_fullState_with_scratch_buf_set (s : FullState)
    (scr : List (BitVec 32)) :
    ({ s with scratch := { s.scratch with scratch_buf := scr } } :
      FullState).scratch.scratch_buf = scr := rfl

@[scoped bv_c0] theorem m8k6c_list_length_set {α : Type} (xs : List α) (i : Nat) (v : α) :
    (xs.set i v).length = xs.length := List.length_set

@[scoped bv_c0] theorem m8k6c_fullScratch_buf_set3 (s : FullScratch)
    (ws tm scr : List (BitVec 32)) :
    ({ s with wsort := ws, tarjan_mark := tm, scratch_buf := scr } :
      FullScratch).scratch_buf = scr := rfl

@[scoped bv_c0] theorem m8k6c_fullScratch_tmk_set3 (s : FullScratch)
    (ws tm scr : List (BitVec 32)) :
    ({ s with wsort := ws, tarjan_mark := tm, scratch_buf := scr } :
      FullScratch).tarjan_mark = tm := rfl

@[scoped bv_c0] theorem m8k6c_fullScratch_wsort_set3 (s : FullScratch)
    (ws tm scr : List (BitVec 32)) :
    ({ s with wsort := ws, tarjan_mark := tm, scratch_buf := scr } :
      FullScratch).wsort = ws := rfl

@[scoped bv_c0] theorem m8k6c_bv32_ushiftRight (x : BitVec 32) (k : Nat) :
    (x >>> k).toNat = x.toNat / 2 ^ k := by
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

@[scoped bv_c0] theorem m8k6c_bv64_ofNat_toNat (n : Nat) :
    (BitVec.ofNat 64 n).toNat = n % 2 ^ 64 :=
  @BitVec.toNat_ofNat n 64

@[scoped bv_c0] theorem m8k6c_bv64_ofNat_ofNat_toNat (n : Nat) :
    (@BitVec.ofNat (@OfNat.ofNat Nat 64 (instOfNatNat 64)) n).toNat = n % 2 ^ 64 :=
  @BitVec.toNat_ofNat n 64

@[scoped bv_c0] theorem m8k6c_bv32_ofNat_toNat (n : Nat) :
    (BitVec.ofNat 32 n).toNat = n % 2 ^ 32 :=
  @BitVec.toNat_ofNat n 32

@[scoped c0_store] theorem c0_store_m8_scr_nat {cap : Nat} {pScr : BitVec 64}
    {scr : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64} {i : Nat} (v : BitVec 32)
    (hi : i < 16384) (hm : (M8P6Scr cap pScr scr ⋆ R) m) :
    storeOk m i32 (pScr + BitVec.ofNat 64 (4 * i)) ∧
      (M8P6Scr cap pScr (scr.set i v) ⋆ R)
        (storeMem m i32 (pScr + BitVec.ofNat 64 (4 * i)) v) := by
  rw [M8P6Scr_eq, sep_pure_l, sep_pure_l] at hm ⊢
  obtain ⟨h16, hlen, ha⟩ := hm
  obtain ⟨hok, hst⟩ := store_array (t := i32) (i := i) v (by decide) (by omega) ha
  exact ⟨hok, h16, by simp [hlen], hst⟩

@[scoped c0_store] theorem c0_store_m8_scr_bv_lt16384 {cap : Nat} {pScr : BitVec 64}
    {scr : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64} (v : BitVec 32)
    (hi : i.toNat < 16384) (hm : (M8P6Scr cap pScr scr ⋆ R) m) :
    storeOk m i32 (pScr + i * 4) ∧
      (M8P6Scr cap pScr (scr.set i.toNat v) ⋆ R) (storeMem m i32 (pScr + i * 4) v) := by
  rw [show pScr + i * 4 = pScr + BitVec.ofNat 64 (4 * i.toNat) from by
    rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_mul_ofNat]]
  exact c0_store_m8_scr_nat v hi hm

@[scoped c0_store] theorem c0_store_m8_scr_bv {cap : Nat} {pScr : BitVec 64}
    {scr : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64} (v : BitVec 32)
    (hi : i.toNat < cap) (hm : (M8P6Scr cap pScr scr ⋆ R) m) :
    storeOk m i32 (pScr + i * 4) ∧
      (M8P6Scr cap pScr (scr.set i.toNat v) ⋆ R) (storeMem m i32 (pScr + i * 4) v) := by
  rw [show pScr + i * 4 = pScr + BitVec.ofNat 64 (4 * i.toNat) from by
    rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_mul_ofNat]]
  rw [M8P6Scr_eq, sep_pure_l, sep_pure_l] at hm ⊢
  obtain ⟨h16, hlen, ha⟩ := hm
  obtain ⟨hok, hst⟩ := store_array (t := i32) (i := i.toNat) v (by decide) (by omega) ha
  exact ⟨hok, h16, by simp [hlen], hst⟩

end M8K6cTactics

open scoped M8K6cTactics

/-! ## 2. Pure & Separation Helpers -/

theorem m8_k6c_xor_two_mul (n : Nat) : (2 * n) ^^^ 1 = 2 * n + 1 := by
  apply Nat.eq_of_testBit_eq; intro k
  cases k with
  | zero => simp [Nat.testBit_zero, Nat.mul_mod_right, show (2 * n + 1) % 2 = 1 by omega]
  | succ j =>
    rw [Nat.testBit_xor, Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ]
    simp [Nat.mul_div_right _ (by omega : 0 < 2), Nat.mul_add_div (by omega : 0 < 2)]

theorem m8_k6c_xor_two_mul_add1 (n : Nat) : (2 * n + 1) ^^^ 1 = 2 * n := by
  rw [← m8_k6c_xor_two_mul n, Nat.xor_assoc, show (1 ^^^ 1 : Nat) = 0 from rfl, Nat.xor_zero]

def m8_k6c_fullWithoutScr (c : FullCfg) (s : FullState) : Mem 64 → Prop :=
  dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
  array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆
  FullCoreArrays c s.core ⋆
  (FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆ FullScrWksArrs c s.scratch ⋆
   FullScrMetaArrs c s.scratch ⋆
   (array (t := i32) c.pDelayed s.scratch.delayed ⋆
    array (t := i32) c.pRedRefs s.scratch.red_refs ⋆
    array (t := i32) c.pExtendStk s.scratch.extend_stk)) ⋆ c.pad

theorem m8_k6c_scrBuf_split {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (h16384 : 16384 ≤ c.scratch_cap)
    (hlen : s.scratch.scratch_buf.length = c.scratch_cap)
    (hm : (FullMem c s ⋆ R) m) :
    (M8P6Scr c.scratch_cap c.pScratchBuf s.scratch.scratch_buf ⋆
      (m8_k6c_fullWithoutScr c s ⋆ R)) m := by
  have heq : (FullMem c s ⋆ R) =
      (array (t := i32) c.pScratchBuf s.scratch.scratch_buf ⋆
        (m8_k6c_fullWithoutScr c s ⋆ R)) := by
    unfold FullMem FullScratchArrays FullScrDynArrs m8_k6c_fullWithoutScr; ac_rfl
  rw [M8P6Scr_eq, sep_pure_l, sep_pure_l]
  exact ⟨h16384, hlen, heq ▸ hm⟩

theorem m8_k6c_scrBuf_unsplit {c : FullCfg} {s : FullState} {scr' : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (M8P6Scr c.scratch_cap c.pScratchBuf scr' ⋆
      (m8_k6c_fullWithoutScr c s ⋆ R)) m) :
    (FullMem c { s with scratch := { s.scratch with scratch_buf := scr' } } ⋆ R) m := by
  let sf : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
  have houter : m8_k6c_fullWithoutScr c sf = m8_k6c_fullWithoutScr c s := rfl
  have heq : (FullMem c sf ⋆ R) =
      (array (t := i32) c.pScratchBuf scr' ⋆ (m8_k6c_fullWithoutScr c sf ⋆ R)) := by
    unfold FullMem FullScratchArrays FullScrDynArrs m8_k6c_fullWithoutScr
    dsimp only [sf]; ac_rfl
  rw [houter] at heq
  rw [M8P6Scr_eq, sep_pure_l, sep_pure_l] at hm
  exact heq.symm ▸ hm.2.2

theorem m8_k6c_scrBuf_unsplit_eq {c : FullCfg} {s : FullState}
    {scr' scr_h : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (M8P6Scr c.scratch_cap c.pScratchBuf scr' ⋆
      (m8_k6c_fullWithoutScr c s ⋆ R)) m)
    (heq : scr' = scr_h := by rfl) :
    (FullMem c { s with scratch := { s.scratch with scratch_buf := scr_h } } ⋆ R) m :=
  heq ▸ m8_k6c_scrBuf_unsplit hm

theorem m8_k6c_tmk_clear_step {cv nv i : Nat} {tmk exp : List (BitVec 32)} {v : BitVec 32}
    (_hi : i < nv) (hexp : (exp[i]?.getD 0#32).toNat = v.toNat) (hv_len : v.toNat < tmk.length)
    (ht : ∀ u < cv, tmk[u]?.getD 0#32 ≠ 0#32 →
      ∃ k, i ≤ k ∧ k < nv ∧ (exp[k]?.getD 0#32).toNat = u) :
    ∀ u < cv, (tmk.set v.toNat 0#32)[u]?.getD 0#32 ≠ 0#32 →
      ∃ k, i + 1 ≤ k ∧ k < nv ∧ (exp[k]?.getD 0#32).toNat = u := by
  intro u hu hne
  by_cases huv : u = v.toNat
  · subst huv; rw [List.getElem?_set_self hv_len, Option.getD_some] at hne
    exact absurd rfl hne
  · rw [List.getElem?_set_ne (Ne.symm huv)] at hne
    obtain ⟨k, hik, hkn, hwk⟩ := ht u hu hne
    have hkne : k ≠ i := fun hke => huv (by rw [← hwk, hke, hexp])
    exact ⟨k, by omega, hkn, hwk⟩

theorem m8_k6c_tmk_clear_done {cv nv : Nat} {tmk exp : List (BitVec 32)}
    (ht : ∀ u < cv, tmk[u]?.getD 0#32 ≠ 0#32 →
      ∃ k, nv ≤ k ∧ k < nv ∧ (exp[k]?.getD 0#32).toNat = u) :
    ∀ u < cv, tmk[u]?.getD 0#32 = 0#32 := by
  intro u hu; exact Classical.byContradiction fun hne => by
    obtain ⟨_, h1, h2, _⟩ := ht u hu hne; omega

theorem m8_k6c_mask_widx (eid mbase : BitVec 32)
    (hmb : mbase = 4002#32 ∨ mbase = 4066#32) :
    let idx := eid &&& 0x7FF#32
    4002 ≤ (mbase + (idx >>> (5 : Nat))).toNat ∧
    (mbase + (idx >>> (5 : Nat))).toNat < 4130 := by
  intro idx
  have hidx : idx.toNat < 2048 := by
    dsimp only [idx]
    rw [BitVec.toNat_and, show (0x7FF#32 : BitVec 32).toNat = 2 ^ 11 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod]
    omega
  have hsh : (idx >>> (5 : Nat)).toNat < 64 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, show 2 ^ 5 = 32 from rfl]; omega
  rcases hmb with rfl | rfl
  · rw [BitVec.toNat_add, show (4002#32 : BitVec 32).toNat = 4002 from rfl,
      Nat.mod_eq_of_lt (by omega)]; omega
  · rw [BitVec.toNat_add, show (4066#32 : BitVec 32).toNat = 4066 from rfl,
      Nat.mod_eq_of_lt (by omega)]; omega

theorem m8_k6c_add1_toNat {x : BitVec 32} (hx : x.toNat + 1 < 2 ^ 32) :
    (x + 1#32).toNat = x.toNat + 1 := by
  rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl, Nat.mod_eq_of_lt hx]

theorem m8_k6c_off_add (n : Nat) (hn : n < 2 ^ 32)
    (i : BitVec 32) (hi : n + i.toNat < 2 ^ 32) :
    (BitVec.setWidth 64 ((@OfNat.ofNat (BitVec 32) n (BitVec.instOfNat)) + i)).toNat =
      n + i.toNat := by
  rw [m6_zext32_toNat, BitVec.toNat_add,
    show (@OfNat.ofNat (BitVec 32) n (BitVec.instOfNat)).toNat = n from by
      rw [show (@OfNat.ofNat (BitVec 32) n (BitVec.instOfNat)) = BitVec.ofNat 32 n from rfl,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn],
    Nat.mod_eq_of_lt hi]

theorem m8_k6c_fullMem_subst {c : FullCfg} {s1 s2 : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (FullMem c s1 ⋆ R) m)
    (hc : s1.core = s2.core := by rfl) (hs : s1.scratch = s2.scratch := by rfl) :
    (FullMem c s2 ⋆ R) m := by
  cases s1; cases s2; simp only at hc hs; subst hc; subst hs; exact hm

theorem m8_k6c_entry_bin_bounds {F_cur : List (List Nat)} {s : FullState}
    {lit : Nat} {w : BitVec 32} (h : FullBveEntryOkW F_cur s lit w)
    (hbin : (w &&& 0x80000000#32) ≠ 0#32) :
    (w &&& 0x7FFFFFFF#32).toNat < 2 * s.core.cur_vars := by
  unfold FullBveEntryOkW at h; rw [ite_eq_left hbin] at h; exact h.1

theorem m8_k6c_entry_large_bounds {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hdw : FullDenseInvW c F0 F_cur s)
    {lit : Nat} {w : BitVec 32} (h : FullBveEntryOkW F_cur s lit w)
    (hlarge : (w &&& 0x80000000#32) = 0#32) :
    let sz := (s.core.arena[w.toNat + 2]?.getD 0#32).toNat
    w.toNat + 3 + sz ≤ s.core.arena_len ∧
    ∀ j < sz, (s.core.arena[w.toNat + 3 + j]?.getD 0#32).toNat < 2 * s.core.cur_vars := by
  unfold FullBveEntryOkW at h
  simp only [hlarge, ne_eq, not_true_eq_false, ↓reduceIte] at h
  have hwf := hdw.2.1.arena.refs_wf w.toNat h.1
  have hle : w.toNat + 3 + fullArenaClauseSize s w.toNat ≤ s.core.arena_len :=
    Nat.le_trans hwf.2.2.1 hwf.2.2.2.1
  have hle_ar : w.toNat + 3 + fullArenaClauseSize s w.toNat ≤ s.core.arena.length := by
    have := hdw.1.core_ok.arena_len_arr; have := hdw.1.core_ok.arena_len_le; omega
  have hsz_eq : (s.core.arena[w.toNat + 2]?.getD 0#32).toNat = fullArenaClauseSize s w.toNat := rfl
  rw [hsz_eq]
  refine ⟨hle, fun j hj => ?_⟩
  have hj_ar : w.toNat + 3 + j < s.core.arena.length := by omega
  have hmem : (s.core.arena[w.toNat + 3 + j]?.getD 0#32).toNat ∈
      fullArenaClauseLits s w.toNat := by
    rw [List.getElem?_eq_getElem hj_ar, Option.getD_some]
    exact (mem_fullArenaClauseLitsCore_iff hle_ar).mpr ⟨j, hj, rfl⟩
  exact hdw.2.1.arena.lits_lt w.toNat h.1 h.2 _ hmem

theorem m8_k6c_shr1_lt {n : Nat} {l : BitVec 32} (hl : l.toNat < 2 * n) :
    (l >>> (1 : Nat)).toNat = l.toNat / 2 ∧ (l >>> (1 : Nat)).toNat < n := by
  have h1 : (l >>> (1 : Nat)).toNat = l.toNat / 2 := by
    simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  exact ⟨h1, by omega⟩

theorem m8_k6c_tmk_reg {cv mc : Nat} {nv : BitVec 32}
    {exp tmk : List (BitVec 32)} {lv : BitVec 32}
    (hnv_lt : nv.toNat < 256) (hnv_cv : nv.toNat < 2 * cv)
    (hexpl : nv.toNat < exp.length) (htmkl : tmk.length = 2 * mc)
    (hcv_le : cv ≤ mc) (hlv : lv.toNat < cv)
    (hexp_bnd : ∀ k < nv.toNat, (exp[k]?.getD 0#32).toNat < cv)
    (htmk_inv : ∀ u < cv, tmk[u]?.getD 0#32 ≠ 0#32 →
      1 ≤ (tmk[u]?.getD 0#32).toNat ∧ (tmk[u]?.getD 0#32).toNat ≤ nv.toNat ∧
      ∃ k < nv.toNat, (exp[k]?.getD 0#32).toNat = u) :
    let exp' := exp.set nv.toNat lv
    let nv' := nv + 1#32
    let tmk' := tmk.set lv.toNat nv'
    nv'.toNat = nv.toNat + 1 ∧
    nv'.toNat ≤ 256 ∧ nv'.toNat ≤ 2 * cv ∧
    (∀ k < nv'.toNat, (exp'[k]?.getD 0#32).toNat < cv) ∧
    (∀ u < cv, tmk'[u]?.getD 0#32 ≠ 0#32 →
      1 ≤ (tmk'[u]?.getD 0#32).toNat ∧ (tmk'[u]?.getD 0#32).toNat ≤ nv'.toNat ∧
      ∃ k < nv'.toNat, (exp'[k]?.getD 0#32).toNat = u) ∧
    1 ≤ (tmk'[lv.toNat]?.getD 0#32).toNat ∧ (tmk'[lv.toNat]?.getD 0#32).toNat ≤ nv'.toNat := by
  intro exp' nv' tmk'
  have hlv_tmk : lv.toNat < tmk.length := by omega
  have hnv1 : nv'.toNat = nv.toNat + 1 := by
    dsimp only [nv']; rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl,
      Nat.mod_eq_of_lt (by omega)]
  have hset_lv : tmk'[lv.toNat]?.getD 0#32 = nv' := by
    dsimp only [tmk']; rw [List.getElem?_set_self hlv_tmk, Option.getD_some]
  refine ⟨hnv1, by omega, by omega, fun k hk => ?_, fun u hu hnz => ?_,
    by rw [hset_lv, hnv1]; omega, by rw [hset_lv, hnv1]; omega⟩
  · dsimp only [exp']
    rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp (hnv1 ▸ hk)) with hlt | rfl
    · rw [List.getElem?_set_ne (by omega)]; exact hexp_bnd k hlt
    · rw [List.getElem?_set_self hexpl, Option.getD_some]; exact hlv
  · dsimp only [tmk']
    by_cases hul : u = lv.toNat
    · subst hul; rw [List.getElem?_set_self hlv_tmk, Option.getD_some, hnv1]
      refine ⟨by omega, by omega, nv.toNat, by omega, ?_⟩
      dsimp only [exp']; rw [List.getElem?_set_self hexpl, Option.getD_some]
    · rw [List.getElem?_set_ne (Ne.symm hul)] at hnz ⊢
      obtain ⟨h1, h2, k, hk, hwk⟩ := htmk_inv u hu hnz
      refine ⟨h1, by omega, k, by omega, ?_⟩
      dsimp only [exp']; rw [List.getElem?_set_ne (by omega)]; exact hwk

theorem m8_k6c_bufOk_of_init {scr : List (BitVec 32)}
    (hcap : 15744 + (scr[4207]?.getD 0#32).toNat ≤ scr.length)
    (hlt30 : scr.length < 2 ^ 30)
    (hnc : (scr[4193]?.getD 0#32).toNat ≤ 512)
    (halen : (scr[4206]?.getD 0#32).toNat ≤ (scr[4207]?.getD 0#32).toNat)
    (hcl : ∀ cid < (scr[4193]?.getD 0#32).toNat,
      (scr[11648 + cid]?.getD 0#32).toNat + ((scr[12672 + cid]?.getD 0#32) &&& 0xFFFF#32).toNat ≤
        (scr[4207]?.getD 0#32).toNat ∧
      ((scr[12672 + cid]?.getD 0#32) &&& 0x40000000#32) = 0#32) :
    M8K6BufOk scr :=
  M8K6BufOk.mk_of hcap hlt30 (by omega) halen fun cid hcid =>
    let hc := hcl cid hcid
    ⟨hc.1, fun hnz => absurd hc.2 hnz⟩

private theorem m8_k6c_lt2pow30_and_bit30 {x : BitVec 32} (hx : x.toNat < 2 ^ 30) :
    (x &&& 0x40000000#32) = 0#32 := by
  apply BitVec.eq_of_toNat_eq
  apply Nat.eq_of_testBit_eq; intro k
  rw [BitVec.toNat_and,
    show (0x40000000#32 : BitVec 32).toNat = 2 ^ 30 from rfl,
    Nat.testBit_and, Nat.testBit_two_pow,
    show (0#32 : BitVec 32).toNat = 0 from rfl,
    Nat.zero_testBit]
  by_cases hk : 30 = k
  · subst hk; simp [Nat.testBit_lt_two_pow hx]
  · simp [hk]

private theorem m8_k6c_lengthsOk_scr {c : FullCfg} {s : FullState} (hl : s.LengthsOk c)
    {scr' : List (BitVec 32)} (hs : scr'.length = c.scratch_cap) :
    ({ s with scratch := { s.scratch with scratch_buf := scr' } } : FullState).LengthsOk c :=
  ⟨hl.core_ok, { hl.scratch_ok with scratch_buf_len := hs }⟩

private theorem m8_k6c_lengthsOk_scr_fuel {c : FullCfg} {s : FullState} (hl : s.LengthsOk c)
    {scr' : List (BitVec 32)} (hs : scr'.length = c.scratch_cap) (fl' : BitVec 64) :
    ({ s with
      core := { s.core with fuel := fl' }
      scratch := { s.scratch with scratch_buf := scr' } } : FullState).LengthsOk c :=
  ⟨{ hl.core_ok with arena_len_le := hl.core_ok.arena_len_le },
   { hl.scratch_ok with scratch_buf_len := hs }⟩

/-! ## 3. K6 Watch/Solve/Core/Mask Sub-Phase (`m8_k6c_watch_solve_wp`) -/

private def m8K6cWatchBody (hdr pScr : BitVec 64) (i sz : BitVec 32)
    (k : Expr Val Cont [.bool]) : Expr Val Cont [.bool] :=
  Expr.let_ ⟨OpCode.add i32, (Arg.imm 11648, Arg.var i, ())⟩ fun p1 =>
  Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p1.fst, ())⟩ fun p2 =>
  Expr.let_ ⟨OpCode.mul i64, (Arg.var p2.fst, Arg.imm 4, ())⟩ fun p3 =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var pScr, Arg.var p3.fst, ())⟩ fun p4 =>
  Expr.load i32 (Arg.var p4.fst) fun ld0 =>
  Expr.let_ ⟨OpCode.add i32, (Arg.imm 15744, Arg.var ld0, ())⟩ fun p5 =>
  Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p5.fst, ())⟩ fun p6 =>
  Expr.let_ ⟨OpCode.mul i64, (Arg.var p6.fst, Arg.imm 4, ())⟩ fun p7 =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var pScr, Arg.var p7.fst, ())⟩ fun p8 =>
  Expr.load i32 (Arg.var p8.fst) fun ld1 =>
  Expr.let_ ⟨OpCode.add i32, (Arg.imm 15744, Arg.var ld0, ())⟩ fun p9 =>
  Expr.let_ ⟨OpCode.add i32, (Arg.var p9.fst, Arg.imm 1, ())⟩ fun p10 =>
  Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p10.fst, ())⟩ fun p11 =>
  Expr.let_ ⟨OpCode.mul i64, (Arg.var p11.fst, Arg.imm 4, ())⟩ fun p12 =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var pScr, Arg.var p12.fst, ())⟩ fun p13 =>
  Expr.load i32 (Arg.var p13.fst) fun ld2 =>
  Expr.call (as := [i64, i32, i32, i32, i32]) (bs := []) "full_k6_watch_m8"
    (Arg.var hdr, Arg.var i, Arg.var ld1, Arg.var ld2, Arg.var sz, ()) fun _ => k

private def m8K6cCoreMaskExpr (pScr : BitVec 64) (eid : BitVec 32)
    (k : Expr Val Cont [.bool]) : Expr Val Cont [.bool] :=
  Expr.let_ ⟨OpCode.and i32, (Arg.var eid, Arg.imm 2047, ())⟩ fun pidx =>
  Expr.group (fun (_Js : Tup Cont [[i32]]) => Blocks.cons (fun pm =>
    Expr.let_ ⟨OpCode.lshr i32, (Arg.var pidx.fst, Arg.imm 5, ())⟩ fun p1 =>
    Expr.let_ ⟨OpCode.add i32, (Arg.var pm.fst, Arg.var p1.fst, ())⟩ fun p2 =>
    Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p2.fst, ())⟩ fun p3 =>
    Expr.let_ ⟨OpCode.mul i64, (Arg.var p3.fst, Arg.imm 4, ())⟩ fun p4 =>
    Expr.let_ ⟨OpCode.add i64, (Arg.var pScr, Arg.var p4.fst, ())⟩ fun p5 =>
    Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p2.fst, ())⟩ fun p6 =>
    Expr.let_ ⟨OpCode.mul i64, (Arg.var p6.fst, Arg.imm 4, ())⟩ fun p7 =>
    Expr.let_ ⟨OpCode.add i64, (Arg.var pScr, Arg.var p7.fst, ())⟩ fun p8 =>
    Expr.load i32 (Arg.var p8.fst) fun ld =>
    Expr.let_ ⟨OpCode.and i32, (Arg.var pidx.fst, Arg.imm 31, ())⟩ fun p9 =>
    Expr.let_ ⟨OpCode.shl i32, (Arg.imm 1, Arg.var p9.fst, ())⟩ fun p10 =>
    Expr.let_ ⟨OpCode.or i32, (Arg.var ld, Arg.var p10.fst, ())⟩ fun p11 =>
    Expr.store (t := i32) (Arg.var p11.fst) (Arg.var p5.fst) k) Blocks.nil) fun Js =>
  Expr.let_ ⟨OpCode.lshr i32, (Arg.var eid, Arg.imm 11, ())⟩ fun p1 =>
  Expr.let_ ⟨OpCode.cmp CmpOp.eq i32 Ty.bool rfl, (Arg.var p1.fst, Arg.imm 0, ())⟩ fun p2 =>
  Expr.jnz (Arg.var p2.fst) (Expr.jump Js.fst (Arg.imm 4002, ()))
    (Expr.jump Js.fst (Arg.imm 4066, ()))

private def m8K6cStoreFlagExpr (pScr : BitVec 64) (off : Nat)
    (k : Expr Val Cont [.bool]) : Expr Val Cont [.bool] :=
  Expr.let_ ⟨OpCode.zext 32 64, (Arg.imm off, ())⟩ fun p1 =>
  Expr.let_ ⟨OpCode.mul i64, (Arg.var p1.fst, Arg.imm 4, ())⟩ fun p2 =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var pScr, Arg.var p2.fst, ())⟩ fun p3 =>
  Expr.store (t := i32) (Arg.imm 1) (Arg.var p3.fst) k

private def m8K6cWatchSolveExpr (hdr pScr : BitVec 64) (nc tick_lim : BitVec 32) :
    Expr Val Cont [.bool] :=
  Expr.group (fun (Js3 : Tup Cont [[i32]]) => Blocks.cons (fun p =>
    Expr.let_ ⟨OpCode.cmp CmpOp.ult i32 Ty.bool rfl, (Arg.var p.fst, Arg.var nc, ())⟩ fun pc =>
    Expr.jnz (Arg.var pc.fst)
      (Expr.let_ ⟨OpCode.add i32, (Arg.imm 12672, Arg.var p.fst, ())⟩ fun p7 =>
      Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p7.fst, ())⟩ fun p8 =>
      Expr.let_ ⟨OpCode.mul i64, (Arg.var p8.fst, Arg.imm 4, ())⟩ fun p9 =>
      Expr.let_ ⟨OpCode.add i64, (Arg.var pScr, Arg.var p9.fst, ())⟩ fun p10 =>
      Expr.load i32 (Arg.var p10.fst) fun ld =>
      Expr.let_ ⟨OpCode.and i32, (Arg.var ld, Arg.imm 65535, ())⟩ fun psz =>
      Expr.group (fun (_ : Tup Cont [[]]) => Blocks.cons (fun _ =>
        Expr.let_ ⟨OpCode.add i32, (Arg.var p.fst, Arg.imm 1, ())⟩ fun pi =>
        Expr.jump Js3.fst (Arg.var pi.fst, ())) Blocks.nil) fun JsN =>
      Expr.let_ ⟨OpCode.cmp CmpOp.uge i32 Ty.bool rfl, (Arg.var psz.fst, Arg.imm 2, ())⟩
        fun pg =>
      Expr.jnz (Arg.var pg.fst)
        (m8K6cWatchBody hdr pScr p.fst psz.fst (Expr.jump JsN.fst ()))
        (Expr.jump JsN.fst ()))
      (Expr.call (as := [i64, i32]) (bs := [i64]) "full_k6_solve_m8"
        (Arg.var hdr, Arg.var tick_lim, ()) fun ps =>
      Expr.let_ ⟨OpCode.cmp CmpOp.ne i64 Ty.bool rfl, (Arg.var ps.fst, Arg.imm 20, ())⟩ fun pn =>
      Expr.jnz (Arg.var pn.fst) (Expr.ret (Arg.imm false, ()))
        (Expr.call (as := [i64]) (bs := []) "full_k6_core_m8" (Arg.var hdr, ()) fun _ =>
        Expr.group (fun (JsZ : Tup Cont [[i32]]) => Blocks.cons (fun pz =>
          Expr.let_ ⟨OpCode.cmp CmpOp.ult i32 Ty.bool rfl, (Arg.var pz.fst, Arg.imm 128, ())⟩
            fun pzc =>
          Expr.jnz (Arg.var pzc.fst)
            (Expr.let_ ⟨OpCode.add i32, (Arg.imm 4002, Arg.var pz.fst, ())⟩ fun z1 =>
            Expr.let_ ⟨OpCode.zext 32 64, (Arg.var z1.fst, ())⟩ fun z2 =>
            Expr.let_ ⟨OpCode.mul i64, (Arg.var z2.fst, Arg.imm 4, ())⟩ fun z3 =>
            Expr.let_ ⟨OpCode.add i64, (Arg.var pScr, Arg.var z3.fst, ())⟩ fun z4 =>
            Expr.store (t := i32) (Arg.imm 0) (Arg.var z4.fst)
              (Expr.let_ ⟨OpCode.add i32, (Arg.var pz.fst, Arg.imm 1, ())⟩ fun z5 =>
              Expr.jump JsZ.fst (Arg.var z5.fst, ())))
            (Expr.let_ ⟨OpCode.zext 32 64, (Arg.imm 4194, ())⟩ fun q1 =>
            Expr.let_ ⟨OpCode.mul i64, (Arg.var q1.fst, Arg.imm 4, ())⟩ fun q2 =>
            Expr.let_ ⟨OpCode.add i64, (Arg.var pScr, Arg.var q2.fst, ())⟩ fun q3 =>
            Expr.load i32 (Arg.var q3.fst) fun onc =>
            Expr.group (fun (Js4 : Tup Cont [[i32, .bool]]) => Blocks.cons (fun p4 =>
              Expr.let_ ⟨OpCode.cmp CmpOp.ult i32 Ty.bool rfl, (Arg.var p4.fst, Arg.var onc, ())⟩
                fun p7 =>
              Expr.jnz (Arg.var p7.fst)
                (Expr.group (fun (_ : Tup Cont [[.bool]]) => Blocks.cons (fun p8 =>
                  Expr.let_ ⟨OpCode.add i32, (Arg.var p4.fst, Arg.imm 1, ())⟩ fun pi =>
                  Expr.jump Js4.fst (Arg.var pi.fst, Arg.var p8.fst, ())) Blocks.nil) fun JsS =>
                Expr.let_ ⟨OpCode.add i32, (Arg.imm 12672, Arg.var p4.fst, ())⟩ fun p8 =>
                Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p8.fst, ())⟩ fun p9 =>
                Expr.let_ ⟨OpCode.mul i64, (Arg.var p9.fst, Arg.imm 4, ())⟩ fun p10 =>
                Expr.let_ ⟨OpCode.add i64, (Arg.var pScr, Arg.var p10.fst, ())⟩ fun p11 =>
                Expr.load i32 (Arg.var p11.fst) fun ld =>
                Expr.let_ ⟨OpCode.and i32, (Arg.var ld, Arg.imm 2147483648, ())⟩ fun p12 =>
                Expr.let_ ⟨OpCode.cmp CmpOp.ne i32 Ty.bool rfl, (Arg.var p12.fst, Arg.imm 0, ())⟩
                  fun p13 =>
                Expr.jnz (Arg.var p13.fst)
                  (Expr.let_ ⟨OpCode.add i32, (Arg.imm 13696, Arg.var p4.fst, ())⟩ fun r1 =>
                  Expr.let_ ⟨OpCode.zext 32 64, (Arg.var r1.fst, ())⟩ fun r2 =>
                  Expr.let_ ⟨OpCode.mul i64, (Arg.var r2.fst, Arg.imm 4, ())⟩ fun r3 =>
                  Expr.let_ ⟨OpCode.add i64, (Arg.var pScr, Arg.var r3.fst, ())⟩ fun r4 =>
                  Expr.load i32 (Arg.var r4.fst) fun eid =>
                  m8K6cCoreMaskExpr pScr eid (Expr.jump JsS.fst (Arg.imm true, ())))
                  (Expr.jump JsS.fst (Arg.var p4.snd.fst, ())))
                (Expr.group (fun (_JsR : Tup Cont [[]]) => Blocks.cons (fun _ =>
                    Expr.ret (Arg.var p4.snd.fst, ())) Blocks.nil) fun JsR =>
                  Expr.jnz (Arg.var p4.snd.fst)
                    (m8K6cStoreFlagExpr pScr 4130
                      (m8K6cStoreFlagExpr pScr 4131 (Expr.jump JsR.fst ())))
                    (Expr.jump JsR.fst ()))) Blocks.nil) fun Js4 =>
              Expr.jump Js4.fst (Arg.imm 0, Arg.imm false, ()))) Blocks.nil) fun JsZ =>
          Expr.jump JsZ.fst (Arg.imm 0, ()))))
    Blocks.nil) fun Js3 => Expr.jump Js3.fst (Arg.imm 0, ())

theorem m8_k6c_watch_solve_wp (Γ : Env)
    (hWatch : ∀ a m Q X, m8K6WatchSpec a m Q X →
      Γ "full_k6_watch_m8" [i64, i32, i32, i32, i32] [] a m Q X)
    (hSolve : ∀ a m Q X, m8K6SolveSpec a m Q X →
      Γ "full_k6_solve_m8" [i64, i32] [i64] a m Q X)
    (hCore : ∀ a m Q X, m8K6CoreSpec a m Q X →
      Γ "full_k6_core_m8" [i64] [] a m Q X)
    (c : FullCfg) (s0 s_clr : FullState) (R : Mem 64 → Prop)
    (scr2 : List (BitVec 32)) (nc_s tick_lim : BitVec 32)
    (m2 : Mem 64) (Q : Post [.bool]) (X : XPost)
    (hlen_clr : s_clr.LengthsOk c)
    (hsc16384 : 16384 ≤ c.scratch_cap)
    (hnc512 : nc_s.toNat ≤ 512)
    (hclr_fl : s_clr.core.fuel = s0.core.fuel)
    (hscr2_l : scr2.length = c.scratch_cap)
    (hscr2_ok : M8K6BufOk scr2)
    (hpre2 : ∀ k < 4192, scr2[k]? = s0.scratch.scratch_buf[k]?)
    (hs2_1 : scr2[4193]? = some nc_s) (hs2_2 : scr2[4194]? = some nc_s)
    (hm2 : (FullMem c { s_clr with scratch := { s_clr.scratch with scratch_buf := scr2 } } ⋆ R) m2)
    (hQ : ∀ (ok : Bool) fl' scr' m',
      fl'.toNat ≤ s0.core.fuel.toNat → scr'.length = c.scratch_cap →
      (∀ k < 4002, scr'[k]? = s0.scratch.scratch_buf[k]?) →
      (∀ k, 4132 ≤ k → k < 4192 → scr'[k]? = s0.scratch.scratch_buf[k]?) →
      (FullMem c { s_clr with
        core := { s_clr.core with fuel := fl' }
        scratch := { s_clr.scratch with scratch_buf := scr' } } ⋆ R) m' →
      Q (ok, ()) m') :
    wp Γ Q X (Expr.group (fun (Js3 : Tup Cont [[i32]]) => Blocks.cons (fun p =>
      Expr.let_ ⟨OpCode.cmp CmpOp.ult i32 Ty.bool rfl, (Arg.var p.fst, Arg.var nc_s, ())⟩
        fun pc =>
      Expr.jnz (Arg.var pc.fst)
        (Expr.let_ ⟨OpCode.add i32, (Arg.imm 12672, Arg.var p.fst, ())⟩ fun p7 =>
        Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p7.fst, ())⟩ fun p8 =>
        Expr.let_ ⟨OpCode.mul i64, (Arg.var p8.fst, Arg.imm 4, ())⟩ fun p9 =>
        Expr.let_ ⟨OpCode.add i64, (Arg.var c.pScratchBuf, Arg.var p9.fst, ())⟩ fun p10 =>
        Expr.load i32 (Arg.var p10.fst) fun ld =>
        Expr.let_ ⟨OpCode.and i32, (Arg.var ld, Arg.imm 65535, ())⟩ fun psz =>
        Expr.group (fun (_ : Tup Cont [[]]) => Blocks.cons (fun _ =>
          Expr.let_ ⟨OpCode.add i32, (Arg.var p.fst, Arg.imm 1, ())⟩ fun pi =>
          Expr.jump Js3.fst (Arg.var pi.fst, ())) Blocks.nil) fun JsN =>
        Expr.let_ ⟨OpCode.cmp CmpOp.uge i32 Ty.bool rfl, (Arg.var psz.fst, Arg.imm 2, ())⟩
          fun pg =>
        Expr.jnz (Arg.var pg.fst)
          (Expr.let_ ⟨OpCode.add i32, (Arg.imm 11648, Arg.var p.fst, ())⟩ fun w1 =>
          Expr.let_ ⟨OpCode.zext 32 64, (Arg.var w1.fst, ())⟩ fun w2 =>
          Expr.let_ ⟨OpCode.mul i64, (Arg.var w2.fst, Arg.imm 4, ())⟩ fun w3 =>
          Expr.let_ ⟨OpCode.add i64, (Arg.var c.pScratchBuf, Arg.var w3.fst, ())⟩ fun w4 =>
          Expr.load i32 (Arg.var w4.fst) fun ld0 =>
          Expr.let_ ⟨OpCode.add i32, (Arg.imm 15744, Arg.var ld0, ())⟩ fun w5 =>
          Expr.let_ ⟨OpCode.zext 32 64, (Arg.var w5.fst, ())⟩ fun w6 =>
          Expr.let_ ⟨OpCode.mul i64, (Arg.var w6.fst, Arg.imm 4, ())⟩ fun w7 =>
          Expr.let_ ⟨OpCode.add i64, (Arg.var c.pScratchBuf, Arg.var w7.fst, ())⟩ fun w8 =>
          Expr.load i32 (Arg.var w8.fst) fun ld1 =>
          Expr.let_ ⟨OpCode.add i32, (Arg.imm 15744, Arg.var ld0, ())⟩ fun w9 =>
          Expr.let_ ⟨OpCode.add i32, (Arg.var w9.fst, Arg.imm 1, ())⟩ fun w10 =>
          Expr.let_ ⟨OpCode.zext 32 64, (Arg.var w10.fst, ())⟩ fun w11 =>
          Expr.let_ ⟨OpCode.mul i64, (Arg.var w11.fst, Arg.imm 4, ())⟩ fun w12 =>
          Expr.let_ ⟨OpCode.add i64, (Arg.var c.pScratchBuf, Arg.var w12.fst, ())⟩ fun w13 =>
          Expr.load i32 (Arg.var w13.fst) fun ld2 =>
          Expr.call (as := [i64, i32, i32, i32, i32]) (bs := []) "full_k6_watch_m8"
            (Arg.var c.hdr, Arg.var p.fst, Arg.var ld1, Arg.var ld2, Arg.var psz.fst, ())
            fun _ => Expr.jump JsN.fst ())
          (Expr.jump JsN.fst ()))
        (Expr.call (as := [i64, i32]) (bs := [i64]) "full_k6_solve_m8"
          (Arg.var c.hdr, Arg.var tick_lim, ()) fun ps =>
        Expr.let_ ⟨OpCode.cmp CmpOp.ne i64 Ty.bool rfl, (Arg.var ps.fst, Arg.imm 20, ())⟩
          fun pn =>
        Expr.jnz (Arg.var pn.fst) (Expr.ret (Arg.imm false, ()))
          (Expr.call (as := [i64]) (bs := []) "full_k6_core_m8" (Arg.var c.hdr, ()) fun _ =>
          Expr.group (fun (JsZ : Tup Cont [[i32]]) => Blocks.cons (fun pz =>
            Expr.let_ ⟨OpCode.cmp CmpOp.ult i32 Ty.bool rfl, (Arg.var pz.fst, Arg.imm 128, ())⟩
              fun pzc =>
            Expr.jnz (Arg.var pzc.fst)
              (Expr.let_ ⟨OpCode.add i32, (Arg.imm 4002, Arg.var pz.fst, ())⟩ fun z1 =>
              Expr.let_ ⟨OpCode.zext 32 64, (Arg.var z1.fst, ())⟩ fun z2 =>
              Expr.let_ ⟨OpCode.mul i64, (Arg.var z2.fst, Arg.imm 4, ())⟩ fun z3 =>
              Expr.let_ ⟨OpCode.add i64, (Arg.var c.pScratchBuf, Arg.var z3.fst, ())⟩ fun z4 =>
              Expr.store (t := i32) (Arg.imm 0) (Arg.var z4.fst)
                (Expr.let_ ⟨OpCode.add i32, (Arg.var pz.fst, Arg.imm 1, ())⟩ fun z5 =>
                Expr.jump JsZ.fst (Arg.var z5.fst, ())))
              (Expr.let_ ⟨OpCode.zext 32 64, (Arg.imm 4194, ())⟩ fun q1 =>
              Expr.let_ ⟨OpCode.mul i64, (Arg.var q1.fst, Arg.imm 4, ())⟩ fun q2 =>
              Expr.let_ ⟨OpCode.add i64, (Arg.var c.pScratchBuf, Arg.var q2.fst, ())⟩ fun q3 =>
              Expr.load i32 (Arg.var q3.fst) fun onc =>
              Expr.group (fun (Js4 : Tup Cont [[i32, .bool]]) => Blocks.cons (fun p4 =>
                Expr.let_ ⟨OpCode.cmp CmpOp.ult i32 Ty.bool rfl, (Arg.var p4.fst, Arg.var onc, ())⟩
                  fun p7 =>
                Expr.jnz (Arg.var p7.fst)
                  (Expr.group (fun (_ : Tup Cont [[.bool]]) => Blocks.cons (fun p8 =>
                    Expr.let_ ⟨OpCode.add i32, (Arg.var p4.fst, Arg.imm 1, ())⟩ fun pi =>
                    Expr.jump Js4.fst (Arg.var pi.fst, Arg.var p8.fst, ())) Blocks.nil) fun JsS =>
                  Expr.let_ ⟨OpCode.add i32, (Arg.imm 12672, Arg.var p4.fst, ())⟩ fun p8 =>
                  Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p8.fst, ())⟩ fun p9 =>
                  Expr.let_ ⟨OpCode.mul i64, (Arg.var p9.fst, Arg.imm 4, ())⟩ fun p10 =>
                  Expr.let_ ⟨OpCode.add i64, (Arg.var c.pScratchBuf, Arg.var p10.fst, ())⟩
                    fun p11 =>
                  Expr.load i32 (Arg.var p11.fst) fun ld =>
                  Expr.let_ ⟨OpCode.and i32, (Arg.var ld, Arg.imm 2147483648, ())⟩ fun p12 =>
                  Expr.let_ ⟨OpCode.cmp CmpOp.ne i32 Ty.bool rfl, (Arg.var p12.fst, Arg.imm 0, ())⟩
                    fun p13 =>
                  Expr.jnz (Arg.var p13.fst)
                    (Expr.let_ ⟨OpCode.add i32, (Arg.imm 13696, Arg.var p4.fst, ())⟩ fun r1 =>
                    Expr.let_ ⟨OpCode.zext 32 64, (Arg.var r1.fst, ())⟩ fun r2 =>
                    Expr.let_ ⟨OpCode.mul i64, (Arg.var r2.fst, Arg.imm 4, ())⟩ fun r3 =>
                    Expr.let_ ⟨OpCode.add i64, (Arg.var c.pScratchBuf, Arg.var r3.fst, ())⟩
                      fun r4 =>
                    Expr.load i32 (Arg.var r4.fst) fun eid =>
                    Expr.let_ ⟨OpCode.and i32, (Arg.var eid, Arg.imm 2047, ())⟩ fun pidx =>
                    Expr.group (fun (_Js : Tup Cont [[i32]]) => Blocks.cons (fun pm =>
                      Expr.let_ ⟨OpCode.lshr i32, (Arg.var pidx.fst, Arg.imm 5, ())⟩ fun k1 =>
                      Expr.let_ ⟨OpCode.add i32, (Arg.var pm.fst, Arg.var k1.fst, ())⟩ fun k2 =>
                      Expr.let_ ⟨OpCode.zext 32 64, (Arg.var k2.fst, ())⟩ fun k3 =>
                      Expr.let_ ⟨OpCode.mul i64, (Arg.var k3.fst, Arg.imm 4, ())⟩ fun k4 =>
                      Expr.let_ ⟨OpCode.add i64, (Arg.var c.pScratchBuf, Arg.var k4.fst, ())⟩
                        fun k5 =>
                      Expr.let_ ⟨OpCode.zext 32 64, (Arg.var k2.fst, ())⟩ fun k6 =>
                      Expr.let_ ⟨OpCode.mul i64, (Arg.var k6.fst, Arg.imm 4, ())⟩ fun k7 =>
                      Expr.let_ ⟨OpCode.add i64, (Arg.var c.pScratchBuf, Arg.var k7.fst, ())⟩
                        fun k8 =>
                      Expr.load i32 (Arg.var k8.fst) fun kld =>
                      Expr.let_ ⟨OpCode.and i32, (Arg.var pidx.fst, Arg.imm 31, ())⟩ fun k9 =>
                      Expr.let_ ⟨OpCode.shl i32, (Arg.imm 1, Arg.var k9.fst, ())⟩ fun k10 =>
                      Expr.let_ ⟨OpCode.or i32, (Arg.var kld, Arg.var k10.fst, ())⟩ fun k11 =>
                      Expr.store (t := i32) (Arg.var k11.fst) (Arg.var k5.fst)
                        (Expr.jump JsS.fst (Arg.imm true, ()))) Blocks.nil) fun Js =>
                    Expr.let_ ⟨OpCode.lshr i32, (Arg.var eid, Arg.imm 11, ())⟩ fun m1 =>
                    Expr.let_ ⟨OpCode.cmp CmpOp.eq i32 Ty.bool rfl, (Arg.var m1.fst, Arg.imm 0, ())⟩
                      fun m2 =>
                    Expr.jnz (Arg.var m2.fst) (Expr.jump Js.fst (Arg.imm 4002, ()))
                      (Expr.jump Js.fst (Arg.imm 4066, ())))
                    (Expr.jump JsS.fst (Arg.var p4.snd.fst, ())))
                  (Expr.group (fun (_JsR : Tup Cont [[]]) => Blocks.cons (fun _ =>
                      Expr.ret (Arg.var p4.snd.fst, ())) Blocks.nil) fun JsR =>
                    Expr.jnz (Arg.var p4.snd.fst)
                      (Expr.let_ ⟨OpCode.zext 32 64, (Arg.imm 4130, ())⟩ fun s1 =>
                      Expr.let_ ⟨OpCode.mul i64, (Arg.var s1.fst, Arg.imm 4, ())⟩ fun s2 =>
                      Expr.let_ ⟨OpCode.add i64, (Arg.var c.pScratchBuf, Arg.var s2.fst, ())⟩
                        fun s3 =>
                      Expr.store (t := i32) (Arg.imm 1) (Arg.var s3.fst)
                        (Expr.let_ ⟨OpCode.zext 32 64, (Arg.imm 4131, ())⟩ fun t1 =>
                        Expr.let_ ⟨OpCode.mul i64, (Arg.var t1.fst, Arg.imm 4, ())⟩ fun t2 =>
                        Expr.let_ ⟨OpCode.add i64, (Arg.var c.pScratchBuf, Arg.var t2.fst, ())⟩
                          fun t3 =>
                        Expr.store (t := i32) (Arg.imm 1) (Arg.var t3.fst) (Expr.jump JsR.fst ())))
                      (Expr.jump JsR.fst ()))) Blocks.nil) fun Js4 =>
                Expr.jump Js4.fst (Arg.imm 0, Arg.imm false, ()))) Blocks.nil) fun JsZ =>
            Expr.jump JsZ.fst (Arg.imm 0, ()))))
      Blocks.nil) fun Js3 => Expr.jump Js3.fst (Arg.imm 0, ())) m2 := by
  change wp Γ Q X (m8K6cWatchSolveExpr c.hdr c.pScratchBuf nc_s tick_lim) m2
  unfold m8K6cWatchSolveExpr
  c0_hsteps_nogrp
  refine wp_loop_group (ts := [i32])
    (fun rem3 (i, ()) m3 => ∃ scr3 : List (BitVec 32),
      let s3 : FullState := { s_clr with scratch := { s_clr.scratch with scratch_buf := scr3 } }
      M8K6BufOk scr3 ∧ scr3.length = c.scratch_cap ∧
      i.toNat ≤ nc_s.toNat ∧ rem3 = nc_s.toNat - i.toNat ∧
      (∀ idx < c.scratch_cap, (idx < 7040 ∨ 11648 ≤ idx) → scr3[idx]? = scr2[idx]?) ∧
      (FullMem c s3 ⋆ R) m3) ?_ ?_
  · rintro L3 rem3 ⟨i, ⟨⟩⟩ m3 hL3 ⟨scr3, hok3, hsc3_l, hi_le, rfl, h3_keep, hm3⟩
    have h3_1 : scr3[4193]? = some nc_s := by
      rw [h3_keep 4193 (by omega) (Or.inl (by decide)), hs2_1]
    have h3_2 : scr3[4194]? = some nc_s := by
      rw [h3_keep 4194 (by omega) (Or.inl (by decide)), hs2_2]
    c0_hsplit
    · have hi_lt : i.toNat < nc_s.toNat := hc
      have hi1 : (i + 1#32).toNat = i.toNat + 1 := m8_k6c_add1_toNat (by omega)
      have hbd_12672 :
          (((@OfNat.ofNat (BitVec 32) 12672 (BitVec.instOfNat)) + i).setWidth 64).toNat <
            scr3.length := by
        rw [m8_k6c_off_add 12672 (by decide) i (by omega), hsc3_l]; omega
      c0_hsteps_nogrp; c0_hstep; c0_hsplit
      · have hsz_ge2 :
            2 ≤ (scr3[(12672 + i.toNat) % 2 ^ 64]?.getD 0#32 &&& 0xFFFF#32).toNat := by
          simpa [show (12672 : BitVec 32).toNat = 12672 from rfl,
            show (2 : BitVec 32).toNat = 2 from rfl,
            Nat.mod_eq_of_lt (by omega : 12672 + i.toNat < 2 ^ 32),
            Nat.mod_eq_of_lt (by omega : 12672 + i.toNat < 2 ^ 64),
            List.getElem?_eq_getElem (by rw [hsc3_l]; omega : 12672 + i.toNat < scr3.length)]
            using hc
        have hci_lt1 : i.toNat < (scr3[4193]?.getD 0#32).toNat := by
          rw [h3_1, Option.getD_some]; exact hi_lt
        have hcl3 := hok3.clause_ok hci_lt1
        have hcap_ge := hok3.length_ge
        have hcap_lt := hok3.length_lt
        have hoff_bd : (scr3[11648 + i.toNat]?.getD 0#32).toNat + 1 <
            (scr3[4207]?.getD 0#32).toNat := by
          have hmod : (12672 + i.toNat) % 2 ^ 64 = 12672 + i.toNat :=
            Nat.mod_eq_of_lt (by omega)
          rw [hmod] at hsz_ge2
          have hget_m : scr3[12672 + i.toNat]?.getD 0#32 =
              scr3[12672 + i.toNat]'(by rw [hsc3_l]; omega) := by
            rw [List.getElem?_eq_getElem (by rw [hsc3_l]; omega), Option.getD_some]
          omega
        have h11648_bd :
            (((@OfNat.ofNat (BitVec 32) 11648 (BitVec.instOfNat)) + i).setWidth 64).toNat <
              scr3.length := by
          rw [m8_k6c_off_add 11648 (by decide) i (by omega), hsc3_l]; omega
        have hoff_eq :
            (scr3[(((@OfNat.ofNat (BitVec 32) 11648 (BitVec.instOfNat)) + i).setWidth
              64).toNat]'h11648_bd).toNat = (scr3[11648 + i.toNat]?.getD 0#32).toNat := by
          rw [List.getElem?_eq_getElem (by rw [hsc3_l]; omega), Option.getD_some]
          exact congrArg BitVec.toNat
            (m6_getElem_congr (m8_k6c_off_add 11648 (by decide) i (by omega)) _ _)
        have h15744_bd0 :
            (((@OfNat.ofNat (BitVec 32) 15744 (BitVec.instOfNat)) +
              scr3[(((@OfNat.ofNat (BitVec 32) 11648 (BitVec.instOfNat)) + i).setWidth
                64).toNat]'h11648_bd).setWidth 64).toNat < scr3.length := by
          rw [m8_k6c_off_add 15744 (by decide) _ (by omega)]; omega
        have h15744_bd1 :
            ((((@OfNat.ofNat (BitVec 32) 15744 (BitVec.instOfNat)) +
              scr3[(((@OfNat.ofNat (BitVec 32) 11648 (BitVec.instOfNat)) + i).setWidth
                64).toNat]'h11648_bd) + 1#32).setWidth 64).toNat < scr3.length := by
          rw [m6_zext32_toNat, BitVec.toNat_add, BitVec.toNat_add,
            show (@OfNat.ofNat (BitVec 32) 15744 (BitVec.instOfNat)).toNat = 15744 from rfl,
            show (1#32 : BitVec 32).toNat = 1 from rfl,
            Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
          omega
        unfold m8K6cWatchBody
        c0_hsteps_nogrp
        m8_call hWatch
        refine m8K6WatchSpec_intro rfl (m8_k6c_lengthsOk_scr hlen_clr hsc3_l) hsc16384 hm3 ?_
        intro scrw mw hlenw hkeepw hmw
        have hokw := m8_k6BufOk_watch_frame hok3 (hlenw.trans hsc3_l.symm)
          (fun idx hi hor => hkeepw idx (hsc3_l ▸ hi) hor)
        have hkeepw' : ∀ idx < c.scratch_cap, (idx < 7040 ∨ 11648 ≤ idx) →
            scrw[idx]? = scr2[idx]? := fun idx hi hor => by
          rw [hkeepw idx hi hor]; exact h3_keep idx hi hor
        c0_hsteps!
        exact hL3 (nc_s.toNat - (i + 1#32).toNat) (i + 1#32, ()) mw (by omega)
          ⟨scrw, hokw, hlenw, by omega, rfl, hkeepw', hmw⟩
      · c0_hsteps!
        exact hL3 (nc_s.toNat - (i + 1#32).toNat) (i + 1#32, ()) m3 (by omega)
          ⟨scr3, hok3, hsc3_l, by omega, rfl, h3_keep, hm3⟩
    · c0_hsteps_nogrp
      m8_call hSolve
      refine m8K6SolveSpec_intro rfl (m8_k6c_lengthsOk_scr hlen_clr hsc3_l) hsc16384 hok3
        (by rw [h3_1, h3_2]; exact Nat.le_refl _) hm3 ?_
      intro res4 scr4 fuel4 m4 _ _ hok4 hlen4 h4_pre h4_onc _ _ hfl4 hm4
      have hfl4' : fuel4.toNat ≤ s0.core.fuel.toNat := hclr_fl ▸ hfl4
      have h4_pre0 : ∀ k < 4192, scr4[k]? = s0.scratch.scratch_buf[k]? := fun k hk => by
        rw [h4_pre k hk, h3_keep k (by omega) (Or.inl (by omega)), hpre2 k hk]
      have h4_onc_eq : scr4[4194]? = some nc_s := by rw [h4_onc, h3_2]
      c0_hsplit
      · c0_hsteps!
        exact hQ false fuel4 scr4 m4 hfl4' hlen4
          (fun k hk => h4_pre0 k (by omega))
          (fun k hk1 hk2 => h4_pre0 k hk2) hm4
      · m8_call hCore
        refine m8K6CoreSpec_intro rfl (m8_k6c_lengthsOk_scr_fuel hlen_clr hlen4 fuel4) hsc16384
          hok4 hm4 ?_
        intro scr5 m5 hlen5 h5_keep hok5 hm5
        have h5_pre0 : ∀ k < 4192, scr5[k]? = s0.scratch.scratch_buf[k]? := fun k hk => by
          rw [h5_keep k (by omega) (Or.inl (by omega)), h4_pre0 k hk]
        have h5_onc : scr5[4194]? = some nc_s := by
          rw [h5_keep 4194 (by omega) (Or.inl (by decide)), h4_onc_eq]
        let s5 : FullState :=
          { s_clr with
            core := { s_clr.core with fuel := fuel4 }
            scratch := { s_clr.scratch with scratch_buf := scr5 } }
        c0_hsteps_nogrp
        refine wp_loop_group (ts := [i32])
          (fun remz (z, ()) mz => ∃ scrz : List (BitVec 32),
            let sz : FullState := { s5 with scratch := { s5.scratch with scratch_buf := scrz } }
            scrz.length = c.scratch_cap ∧ z.toNat ≤ 128 ∧ remz = 128 - z.toNat ∧
            (∀ k < 4002, scrz[k]? = s0.scratch.scratch_buf[k]?) ∧
            (∀ k, 4132 ≤ k → k < 4192 → scrz[k]? = s0.scratch.scratch_buf[k]?) ∧
            scrz[4194]? = some nc_s ∧
            (FullMem c sz ⋆ R) mz) ?_ ?_
        · rintro Lz remz ⟨z, ⟨⟩⟩ mz hLz ⟨scrz, hscz_l, hz_le, rfl, hpre_z, hmid_z, honc_z, hmz⟩
          c0_hsplit
          · have hz_lt : z.toNat < 128 := hc
            have hz1 : (z + 1#32).toNat = z.toNat + 1 := m8_k6c_add1_toNat (by omega)
            have hbd_z :
                (((@OfNat.ofNat (BitVec 32) 4002 (BitVec.instOfNat)) + z).setWidth 64).toNat <
                  scrz.length := by
              rw [m8_k6c_off_add 4002 (by decide) z (by omega), hscz_l]; omega
            c0_hsteps!
            rw [m8_k6c_off_add 4002 (by decide) z (by omega)] at hm
            let scrz' := scrz.set (4002 + z.toNat) 0#32
            exact hLz (128 - (z + 1#32).toNat) (z + 1#32, ()) _ (by omega)
              ⟨scrz', by simp [scrz', hscz_l], by omega, rfl,
               fun k hk => by
                 dsimp only [scrz']; rw [List.getElem?_set_ne (by omega)]; exact hpre_z k hk,
               fun k hk1 hk2 => by
                 dsimp only [scrz']; rw [List.getElem?_set_ne (by omega)]
                 exact hmid_z k hk1 hk2,
               by dsimp only [scrz']; rw [List.getElem?_set_ne (by omega)]; exact honc_z,
               m8_k6c_fullMem_subst hm⟩
          · have h4194_bd :
                (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 4194)).toNat < scrz.length :=
              m8_scr_imm_lt hscz_l hsc16384 (by decide)
            have honc_val :
                (scrz[(BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 4194)).toNat]'h4194_bd) =
                  nc_s := by
              have hgd : (some (scrz[(BitVec.ofNat (OfNat.ofNat 64)
                  (OfNat.ofNat 4194)).toNat]'h4194_bd)).getD 0#32 =
                  scrz[(BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 4194)).toNat]'h4194_bd := rfl
              rw [← hgd, ← List.getElem?_eq_getElem h4194_bd,
                show (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 4194)).toNat = 4194 from rfl,
                honc_z, Option.getD_some]
            c0_hsteps_nogrp
            refine wp_loop_group (ts := [i32, .bool])
              (fun rem4 (i, any4, ()) m4' => ∃ scr4' : List (BitVec 32),
                let s4' : FullState :=
                  { s5 with scratch := { s5.scratch with scratch_buf := scr4' } }
                scr4'.length = c.scratch_cap ∧
                i.toNat ≤ nc_s.toNat ∧ rem4 = nc_s.toNat - i.toNat ∧
                (∀ k < 4002, scr4'[k]? = s0.scratch.scratch_buf[k]?) ∧
                (∀ k, 4132 ≤ k → k < 4192 → scr4'[k]? = s0.scratch.scratch_buf[k]?) ∧
                (FullMem c s4' ⋆ R) m4') ?_ ?_
            · rintro L4 rem4 ⟨i, any4, ⟨⟩⟩ m4' hL4
                ⟨scr4', hsc4'_l, hi_le, rfl, hpre4', hmid4', hm4'⟩
              c0_hsplit
              · have hi_lt : i.toNat < nc_s.toNat := by
                  rw [← honc_val]; exact hc
                have hi1 : (i + 1#32).toNat = i.toNat + 1 := m8_k6c_add1_toNat (by omega)
                have hm_bd :
                    (((@OfNat.ofNat (BitVec 32) 12672 (BitVec.instOfNat)) + i).setWidth
                      64).toNat < scr4'.length := by
                  rw [m8_k6c_off_add 12672 (by decide) i (by omega), hsc4'_l]; omega
                have ha_bd :
                    (((@OfNat.ofNat (BitVec 32) 13696 (BitVec.instOfNat)) + i).setWidth
                      64).toNat < scr4'.length := by
                  rw [m8_k6c_off_add 13696 (by decide) i (by omega), hsc4'_l]; omega
                c0_hsteps_nogrp; c0_hstep; c0_hsplit
                · unfold m8K6cCoreMaskExpr
                  let eid4 :=
                    scr4'[(((@OfNat.ofNat (BitVec 32) 13696 (BitVec.instOfNat)) + i).setWidth
                      64).toNat]'ha_bd
                  let idx4 := eid4 &&& 0x7FF#32
                  c0_hsteps_nogrp
                  refine wp_join_state_pure (ts := [i32]) (α := BitVec 32) (fun m => (m, ()))
                    (fun mb => mb = 4002#32 ∨ mb = 4066#32) ?_ ?_
                  · intro _ mb hmb
                    have hwi := m8_k6c_mask_widx eid4 mb hmb
                    have hwi_lo : 4002 ≤ ((mb + (idx4 >>> (5 : Nat))).setWidth 64).toNat := by
                      rw [m6_zext32_toNat]; exact hwi.1
                    have hwi_hi : ((mb + (idx4 >>> (5 : Nat))).setWidth 64).toNat < 4130 := by
                      rw [m6_zext32_toNat]; exact hwi.2
                    have hwi_sc : ((mb + (idx4 >>> (5 : Nat))).setWidth 64).toNat <
                        scr4'.length := by rw [hsc4'_l]; omega
                    c0_hsteps!
                    let scr4'' := scr4'.set ((mb + (idx4 >>> (5 : Nat))).setWidth 64).toNat
                      (scr4'[((mb + (idx4 >>> (5 : Nat))).setWidth 64).toNat]'hwi_sc |||
                        (1#32 <<< ((idx4 &&& 31#32).toNat % 32)))
                    exact hL4 (nc_s.toNat - (i + 1#32).toNat) (i + 1#32, true, ()) _ (by omega)
                      ⟨scr4'', by simp [scr4'', hsc4'_l], by omega, rfl,
                        fun k hk => by
                          dsimp only [scr4'']; rw [List.getElem?_set_ne (by omega)]
                          exact hpre4' k hk,
                        fun k hk1 hk2 => by
                          dsimp only [scr4'']; rw [List.getElem?_set_ne (by omega)]
                          exact hmid4' k hk1 hk2,
                        hm⟩
                  · intro _ hJm; c0_hsplit
                    · c0_hsteps!; exact hJm 4002#32 (Or.inl rfl)
                    · c0_hsteps!; exact hJm 4066#32 (Or.inr rfl)
                · c0_hsteps!
                  exact hL4 (nc_s.toNat - (i + 1#32).toNat) (i + 1#32, any4, ()) m4'
                    (by omega) ⟨scr4', hsc4'_l, by omega, rfl, hpre4', hmid4', hm4'⟩
              · unfold m8K6cStoreFlagExpr
                c0_hsteps_nogrp; c0_hstep; c0_hsplit
                · have hm_s := m8_k6c_scrBuf_split hsc16384 hsc4'_l hm4'
                  c0_hsteps!
                  let scrf := (scr4'.set 4130 1#32).set 4131 1#32
                  have hscrf_l : scrf.length = c.scratch_cap := by simp [scrf, hsc4'_l]
                  have hm' := m8_k6c_scrBuf_unsplit_eq hm rfl
                  refine hQ any4 fuel4 scrf _ hfl4' hscrf_l
                    (fun k hk => ?_) (fun k hk1 hk2 => ?_) (m8_k6c_fullMem_subst hm')
                  · dsimp only [scrf]
                    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
                    exact hpre4' k hk
                  · dsimp only [scrf]
                    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
                    exact hmid4' k hk1 hk2
                · c0_hsteps!
                  exact hQ any4 fuel4 scr4' m4' hfl4' hsc4'_l hpre4' hmid4' hm4'
            · intro L4 hL4; c0_hsteps!
              exact hL4 nc_s.toNat (0#32, false, ()) mz
                ⟨scrz, hscz_l, Nat.zero_le _, rfl, hpre_z, hmid_z, hmz⟩
        · intro Lz hLz; c0_hsteps!
          exact hLz 128 (0#32, ()) m5
            ⟨scr5, hlen5, Nat.zero_le _, rfl,
             fun k hk => h5_pre0 k (by omega),
             fun k hk1 hk2 => h5_pre0 k hk2,
             h5_onc, hm5⟩
  · intro L3 hL3; c0_hsteps!
    exact hL3 nc_s.toNat (0#32, ()) m2
      ⟨scr2, hscr2_ok, hscr2_l, Nat.zero_le _, rfl, fun _ _ _ => rfl, hm2⟩

/-! ## 4. Clause-Copy + Unit-Registration Sub-Phase (`m8_k6c_copy_clause_wp`) -/

/-- Copies `csz_m` normalized literals from `tmp` into `scr[15744 + al_i ..]`, writes clause
header `(al_i, csz_m, eid)` at clause `nc_i`, records unit clause if `csz_m == 1`, and jumps
into `J`. -/
theorem m8_k6c_copy_clause_wp (Γ : Env) (Q : Post [.bool]) (X : XPost)
    (J : Cont [i32, i32, i32, i32, .bool, i32])
    (c : FullCfg) (s_base : FullState) (R : Mem 64 → Prop)
    (pScr pTmp : BitVec 64)
    (nc_i al_i nu_i eid te_s csz_m : BitVec 32) (ab_m : Bool)
    (scr_pre : Nat → Option (BitVec 32)) (m_init : Mem 64)
    (hpScr : pScr = c.pScratchBuf) (hpTmp : pTmp = c.pTmp)
    (h16384 : 16384 ≤ c.scratch_cap) (hsc28 : c.scratch_cap < 2 * 2 ^ 28)
    (hscl : s_base.scratch.scratch_buf.length = c.scratch_cap)
    (htmp_len : s_base.core.tmp.length = c.max_vars)
    (hcsz_pos : 0 < csz_m.toNat) (hcsz_le100 : csz_m.toNat ≤ 100)
    (hcsz_mc : csz_m.toNat ≤ c.max_vars)
    (hnc512 : nc_i.toNat < 512) (hnu_le : nu_i.toNat ≤ nc_i.toNat)
    (halc_le : al_i.toNat + csz_m.toNat ≤ c.scratch_cap - 15744)
    (hpre0 : ∀ k < 4192, s_base.scratch.scratch_buf[k]? = scr_pre k)
    (hcls0 : ∀ cid < nc_i.toNat,
      (s_base.scratch.scratch_buf[11648 + cid]?.getD 0#32).toNat +
        ((s_base.scratch.scratch_buf[12672 + cid]?.getD 0#32) &&&
          0xFFFF#32).toNat ≤ al_i.toNat ∧
      ((s_base.scratch.scratch_buf[12672 + cid]?.getD 0#32) &&&
        0x40000000#32) = 0#32)
    (hm_init : (FullMem c s_base ⋆ R) m_init)
    (hJ : ∀ (nu_j m_done : BitVec 32) (scr_j : List (BitVec 32)) (mj : Mem 64),
      scr_j.length = c.scratch_cap →
      nu_j.toNat ≤ nc_i.toNat + 1 →
      (∀ k < 4192, scr_j[k]? = scr_pre k) →
      (∀ cid < nc_i.toNat + 1,
        (scr_j[11648 + cid]?.getD 0#32).toNat +
          ((scr_j[12672 + cid]?.getD 0#32) &&& 0xFFFF#32).toNat ≤
          al_i.toNat + csz_m.toNat ∧
        ((scr_j[12672 + cid]?.getD 0#32) &&& 0x40000000#32) = 0#32) →
      (FullMem c
        { s_base with scratch := { s_base.scratch with scratch_buf := scr_j } } ⋆ R) mj →
      J (nc_i + 1#32, al_i + csz_m, nu_j, te_s, ab_m, m_done, ()) mj) :
    wp Γ Q X
      (Expr.group
        (fun (Lc : Tup Cont [[i32]]) =>
          Blocks.cons (fun pmc =>
            Expr.let_ ⟨OpCode.cmp CmpOp.ult i32 Ty.bool rfl,
                (Arg.var pmc.fst, Arg.var csz_m, ())⟩ fun pc =>
            Expr.jnz (Arg.var pc.fst)
              (Expr.let_ ⟨OpCode.add i32, (Arg.imm 15744, Arg.var al_i, ())⟩ fun p2 =>
               Expr.let_ ⟨OpCode.add i32, (Arg.var p2.fst, Arg.var pmc.fst, ())⟩ fun p3 =>
               Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p3.fst, ())⟩ fun p4 =>
               Expr.let_ ⟨OpCode.mul i64, (Arg.var p4.fst, Arg.imm 4, ())⟩ fun p5 =>
               Expr.let_ ⟨OpCode.add i64, (Arg.var pScr, Arg.var p5.fst, ())⟩ fun p6 =>
               Expr.let_ ⟨OpCode.zext 32 64, (Arg.var pmc.fst, ())⟩ fun p7 =>
               Expr.let_ ⟨OpCode.mul i64, (Arg.var p7.fst, Arg.imm 4, ())⟩ fun p8 =>
               Expr.let_ ⟨OpCode.add i64, (Arg.var pTmp, Arg.var p8.fst, ())⟩ fun p9 =>
               Expr.load i32 (Arg.var p9.fst) fun ld =>
               Expr.store (t := i32) (Arg.var ld) (Arg.var p6.fst)
                 (Expr.let_ ⟨OpCode.add i32, (Arg.var pmc.fst, Arg.imm 1, ())⟩ fun p1 =>
                  Expr.jump Lc.fst (Arg.var p1.fst, ())))
              (Expr.let_ ⟨OpCode.add i32, (Arg.imm 11648, Arg.var nc_i, ())⟩ fun p2 =>
               Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p2.fst, ())⟩ fun p3 =>
               Expr.let_ ⟨OpCode.mul i64, (Arg.var p3.fst, Arg.imm 4, ())⟩ fun p4 =>
               Expr.let_ ⟨OpCode.add i64, (Arg.var pScr, Arg.var p4.fst, ())⟩ fun p5 =>
               Expr.store (t := i32) (Arg.var al_i) (Arg.var p5.fst)
                 (Expr.let_ ⟨OpCode.add i32, (Arg.imm 12672, Arg.var nc_i, ())⟩ fun p6 =>
                  Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p6.fst, ())⟩ fun p7 =>
                  Expr.let_ ⟨OpCode.mul i64, (Arg.var p7.fst, Arg.imm 4, ())⟩ fun p8 =>
                  Expr.let_ ⟨OpCode.add i64, (Arg.var pScr, Arg.var p8.fst, ())⟩ fun p9 =>
                  Expr.store (t := i32) (Arg.var csz_m) (Arg.var p9.fst)
                    (Expr.let_ ⟨OpCode.add i32, (Arg.imm 13696, Arg.var nc_i, ())⟩ fun p10 =>
                     Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p10.fst, ())⟩ fun p11 =>
                     Expr.let_ ⟨OpCode.mul i64, (Arg.var p11.fst, Arg.imm 4, ())⟩ fun p12 =>
                     Expr.let_ ⟨OpCode.add i64, (Arg.var pScr, Arg.var p12.fst, ())⟩ fun p13 =>
                     Expr.store (t := i32) (Arg.var eid) (Arg.var p13.fst)
                       (Expr.group
                         (fun (_Js : Tup Cont [[i32]]) =>
                           Blocks.cons (fun p14 =>
                             Expr.let_ ⟨OpCode.add i32, (Arg.var nc_i, Arg.imm 1, ())⟩
                               fun p15 =>
                             Expr.let_ ⟨OpCode.add i32, (Arg.var al_i, Arg.var csz_m, ())⟩
                               fun p16 =>
                             Expr.jump J
                               (Arg.var p15.fst, Arg.var p16.fst, Arg.var p14.fst,
                                Arg.var te_s, Arg.var ab_m, Arg.var pmc.fst, ()))
                             Blocks.nil)
                         fun Js =>
                         Expr.let_ ⟨OpCode.cmp CmpOp.eq i32 Ty.bool rfl,
                             (Arg.var csz_m, Arg.imm 1, ())⟩ fun p =>
                         Expr.jnz (Arg.var p.fst)
                           (Expr.let_ ⟨OpCode.add i32, (Arg.imm 14720, Arg.var nu_i, ())⟩
                              fun pu1 =>
                            Expr.let_ ⟨OpCode.zext 32 64, (Arg.var pu1.fst, ())⟩ fun pu2 =>
                            Expr.let_ ⟨OpCode.mul i64, (Arg.var pu2.fst, Arg.imm 4, ())⟩
                              fun pu3 =>
                            Expr.let_ ⟨OpCode.add i64, (Arg.var pScr, Arg.var pu3.fst, ())⟩
                              fun pu4 =>
                            Expr.store (t := i32) (Arg.var nc_i) (Arg.var pu4.fst)
                              (Expr.let_ ⟨OpCode.add i32, (Arg.var nu_i, Arg.imm 1, ())⟩
                                 fun pu5 =>
                               Expr.jump Js.fst (Arg.var pu5.fst, ())))
                           (Expr.jump Js.fst (Arg.var nu_i, ())))))))
            Blocks.nil)
        fun Lc => Expr.jump Lc.fst (Arg.imm 0, ())) m_init := by
  subst hpScr hpTmp
  refine wp_loop_group (ts := [i32])
    (fun rem_c (mc_i, ()) mc_m =>
      ∃ scr_c : List (BitVec 32),
      let sc_m : FullState :=
        { s_base with scratch := { s_base.scratch with scratch_buf := scr_c } }
      scr_c.length = c.scratch_cap ∧
      mc_i.toNat ≤ csz_m.toNat ∧ rem_c = csz_m.toNat - mc_i.toNat ∧
      (∀ k < 4192, scr_c[k]? = scr_pre k) ∧
      (∀ cid < nc_i.toNat,
        (scr_c[11648 + cid]?.getD 0#32).toNat +
          ((scr_c[12672 + cid]?.getD 0#32) &&& 0xFFFF#32).toNat ≤ al_i.toNat ∧
        ((scr_c[12672 + cid]?.getD 0#32) &&& 0x40000000#32) = 0#32) ∧
      (FullMem c sc_m ⋆ R) mc_m) ?_ ?_
  · rintro Lc rem_c ⟨mc_i, ⟨⟩⟩ mc_m hLc ⟨scr_c, hscc_l, hmc_le, rfl, hpre_c, hcls_c, hmc_m⟩
    c0_hsplit
    · have hmc_lt : mc_i.toNat < csz_m.toNat := hc
      have hmc1 : (mc_i + 1#32).toNat = mc_i.toNat + 1 := m8_k6c_add1_toNat (by omega)
      have htmp_bd : (mc_i.setWidth 64).toNat < s_base.core.tmp.length := by
        rw [htmp_len, m6_zext32_toNat]; omega
      have hsc_bd_eq : (((15744 : BitVec 32) + al_i + mc_i).setWidth 64).toNat =
          15744 + al_i.toNat + mc_i.toNat := by
        rw [m6_zext32_toNat, BitVec.toNat_add, BitVec.toNat_add,
          show (15744 : BitVec 32).toNat = 15744 from rfl,
          Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      have hsc_bd' : (((15744 : BitVec 32) + al_i + mc_i).setWidth 64).toNat <
          c.scratch_cap := by rw [hsc_bd_eq]; omega
      have hmc_scr := m8_k6c_scrBuf_split h16384 hscc_l hmc_m
      c0_hsteps!
      have hm := m8_k6c_scrBuf_unsplit hm
      rw [hsc_bd_eq] at hm
      let scr_c' := scr_c.set (15744 + al_i.toNat + mc_i.toNat)
        (s_base.core.tmp[(mc_i.setWidth 64).toNat]'htmp_bd)
      refine hLc (csz_m.toNat - (mc_i + 1#32).toNat) (mc_i + 1#32, ()) _ (by omega)
        ⟨scr_c', by simp [scr_c', hscc_l], by omega, rfl,
         fun k hk => by
           dsimp only [scr_c']; rw [List.getElem?_set_ne (by omega)]; exact hpre_c k hk,
         fun cid hcid => by
           dsimp only [scr_c']
           rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
           exact hcls_c cid hcid,
         m8_k6c_fullMem_subst hm⟩
    · have hbd_o : (((@OfNat.ofNat (BitVec 32) 11648 (BitVec.instOfNat)) +
          nc_i).setWidth 64).toNat < 16384 := by
        rw [m8_k6c_off_add 11648 (by decide) nc_i (by omega)]; omega
      have hbd_m : (((@OfNat.ofNat (BitVec 32) 12672 (BitVec.instOfNat)) +
          nc_i).setWidth 64).toNat < 16384 := by
        rw [m8_k6c_off_add 12672 (by decide) nc_i (by omega)]; omega
      have hbd_a : (((@OfNat.ofNat (BitVec 32) 13696 (BitVec.instOfNat)) +
          nc_i).setWidth 64).toNat < 16384 := by
        rw [m8_k6c_off_add 13696 (by decide) nc_i (by omega)]; omega
      have hcsz_ff : (csz_m &&& 0xFFFF#32).toNat = csz_m.toNat := by
        rw [BitVec.toNat_and, show (0xFFFF#32 : BitVec 32).toNat = 2 ^ 16 - 1 from rfl,
          Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by omega)]
      have hcsz_lrn : (csz_m &&& 0x40000000#32) = 0#32 :=
        m8_k6c_lt2pow30_and_bit30 (by omega)
      have hmc_scr := m8_k6c_scrBuf_split h16384 hscc_l hmc_m
      c0_hsteps_nogrp
      let scr_m := ((scr_c.set (11648 + nc_i.toNat) al_i).set
        (12672 + nc_i.toNat) csz_m).set (13696 + nc_i.toNat) eid
      have hm_m := m8_k6c_scrBuf_unsplit hm
      rw [m8_k6c_off_add 11648 (by decide) nc_i (by omega),
        m8_k6c_off_add 12672 (by decide) nc_i (by omega),
        m8_k6c_off_add 13696 (by decide) nc_i (by omega)] at hm_m
      have hscm_l : scr_m.length = c.scratch_cap := by simp [scr_m, hscc_l]
      refine wp_join_group (ts := [i32])
        (fun (nu_j, ()) mj =>
          ∃ scr_j : List (BitVec 32),
          scr_j.length = c.scratch_cap ∧ nu_j.toNat ≤ nc_i.toNat + 1 ∧
          (∀ k < 4192, scr_j[k]? = scr_pre k) ∧
          (∀ cid < nc_i.toNat + 1,
            (scr_j[11648 + cid]?.getD 0#32).toNat +
              ((scr_j[12672 + cid]?.getD 0#32) &&& 0xFFFF#32).toNat ≤
              al_i.toNat + csz_m.toNat ∧
            ((scr_j[12672 + cid]?.getD 0#32) &&& 0x40000000#32) = 0#32) ∧
          (FullMem c { s_base with scratch := { s_base.scratch with scratch_buf := scr_j } } ⋆ R)
            mj) ?_ ?_
      · rintro _ ⟨nu_j, ⟨⟩⟩ mj ⟨scr_j, hscj_l, hnu_j, hpre_j, hcls_j, hmj⟩
        c0_hsteps!
        exact hJ nu_j mc_i scr_j mj hscj_l hnu_j hpre_j hcls_j hmj
      · intro _ hJ1
        c0_hsplit
        · have hnu1 : (nu_i + 1#32).toNat = nu_i.toNat + 1 := m8_k6c_add1_toNat (by omega)
          have hbd_u : (((@OfNat.ofNat (BitVec 32) 14720 (BitVec.instOfNat)) +
              nu_i).setWidth 64).toNat < 16384 := by
            rw [m8_k6c_off_add 14720 (by decide) nu_i (by omega)]; omega
          have hm_u_scr := m8_k6c_scrBuf_split h16384 hscm_l (m8_k6c_fullMem_subst hm_m)
          c0_hsteps!
          have hm := m8_k6c_scrBuf_unsplit hm
          rw [m8_k6c_off_add 14720 (by decide) nu_i (by omega)] at hm
          let scr_u := scr_m.set (14720 + nu_i.toNat) nc_i
          refine hJ1 _ _ ⟨scr_u, by simp [scr_u, hscm_l],
            by rw [show (nu_i + 1 : BitVec 32).toNat = nu_i.toNat + 1 from
              m8_k6c_add1_toNat (by omega)]; omega,
            fun k hk => by
              dsimp only [scr_u, scr_m]
              repeat rw [List.getElem?_set_ne (by omega)]
              exact hpre_c k hk,
            fun cid hcid => ?_, m8_k6c_fullMem_subst hm⟩
          dsimp only [scr_u, scr_m]
          rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hcid) with hlt | rfl
          · repeat rw [List.getElem?_set_ne (by omega)]
            have hp := hcls_c cid hlt
            exact ⟨Nat.le_trans hp.1 (by omega), hp.2⟩
          · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
              List.getElem?_set_ne (by omega), List.getElem?_set_self (by simp [hscc_l]; omega),
              List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
              List.getElem?_set_self (by simp [hscc_l]; omega),
              Option.getD_some, Option.getD_some, hcsz_ff]
            exact ⟨Nat.le_refl _, hcsz_lrn⟩
        · c0_hsteps!
          refine hJ1 _ _ ⟨scr_m, hscm_l, by omega,
            (fun k hk => by
              dsimp only [scr_m]
              repeat rw [List.getElem?_set_ne (by omega)]
              exact hpre_c k hk),
            fun cid hcid => ?_, m8_k6c_fullMem_subst hm_m⟩
          dsimp only [scr_m]
          rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hcid) with hlt | rfl
          · repeat rw [List.getElem?_set_ne (by omega)]
            have hp := hcls_c cid hlt
            exact ⟨Nat.le_trans hp.1 (by omega), hp.2⟩
          · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
              List.getElem?_set_self (by simp [hscc_l]; omega), List.getElem?_set_ne (by omega),
              List.getElem?_set_self (by simp [hscc_l]; omega),
              Option.getD_some, Option.getD_some, hcsz_ff]
            exact ⟨Nat.le_refl _, hcsz_lrn⟩
  · intro Lc hLc; c0_hsteps!
    exact hLc csz_m.toNat (0#32, ()) m_init
      ⟨s_base.scratch.scratch_buf, hscl, Nat.zero_le _, rfl, hpre0, hcls0,
       m8_k6c_fullMem_subst hm_init⟩

/-! ## 5. Large-Clause Literal Scan Sub-Phase (`m8_k6c_scan_large_wp`) -/

/-- Scans literals `m ∈ [0..sz)` of large clause `w`, filtering `except`, breaking early on
satisfied or overflowed clauses, registering unseen variables in `exp`/`tmk`, and normalizing
unassigned literals into `tmp[0..csz)`. -/
theorem m8_k6c_scan_large_wp (Γ : Env) (Q : Post [.bool]) (X : XPost)
    (Bm : Cont [i32, .bool, .bool, i32, i32])
    (c : FullCfg) (s_base : FullState) (R : Mem 64 → Prop)
    (pAr pVals pTmk pExp pTmp : BitVec 64)
    (nv_i except w sz mc : BitVec 32) (ab_i : Bool) (m_init : Mem 64)
    (hpAr : pAr = c.pArena) (hpVals : pVals = c.pVals) (hpTmk : pTmk = c.pTarjanMark)
    (hpExp : pExp = c.pWsort) (hpTmp : pTmp = c.pTmp)
    (har_len : s_base.core.arena.length = c.arena_cap)
    (har_le : s_base.core.arena_len ≤ c.arena_cap)
    (hvals_len : s_base.core.vals.length = 2 * c.max_vars)
    (hcv_le : s_base.core.cur_vars ≤ c.max_vars)
    (hmx28 : c.max_vars < 2 * 2 ^ 28)
    (hw_sz_bd : w.toNat + 3 + sz.toNat ≤ s_base.core.arena_len)
    (hw_lits_lt : ∀ j < sz.toNat,
      (s_base.core.arena[w.toNat + 3 + j]?.getD 0#32).toNat < 2 * s_base.core.cur_vars)
    (hexp_l : s_base.scratch.wsort.length = 2 * c.max_vars)
    (htmk_l : s_base.scratch.tarjan_mark.length = 2 * c.max_vars)
    (htmp_l : s_base.core.tmp.length = c.max_vars)
    (hmc_lo : 1 ≤ mc.toNat) (hmc_hi : mc.toNat ≤ 100) (hmc_cv : mc.toNat ≤ c.max_vars)
    (hnv256 : nv_i.toNat ≤ 256) (hnvcv : nv_i.toNat ≤ 2 * s_base.core.cur_vars)
    (hab_fi : ab_i = false)
    (hexp_bnd : ∀ k < nv_i.toNat, (s_base.scratch.wsort[k]?.getD 0#32).toNat < s_base.core.cur_vars)
    (htmk_inv : ∀ u < s_base.core.cur_vars, s_base.scratch.tarjan_mark[u]?.getD 0#32 ≠ 0#32 →
      1 ≤ (s_base.scratch.tarjan_mark[u]?.getD 0#32).toNat ∧
      (s_base.scratch.tarjan_mark[u]?.getD 0#32).toNat ≤ nv_i.toNat ∧
      ∃ k < nv_i.toNat, (s_base.scratch.wsort[k]?.getD 0#32).toNat = u)
    (hm_init : (FullMem c s_base ⋆ R) m_init)
    (hBm : ∀ (nv_m : BitVec 32) (ab_m sat_m : Bool) (csz_m m_idx : BitVec 32)
      (exp_m tmk_m tmp_m : List (BitVec 32)) (mm : Mem 64),
      exp_m.length = 2 * c.max_vars → tmk_m.length = 2 * c.max_vars →
      tmp_m.length = c.max_vars → nv_m.toNat ≤ 256 → nv_m.toNat ≤ 2 * s_base.core.cur_vars →
      csz_m.toNat ≤ mc.toNat →
      (∀ k < nv_m.toNat, (exp_m[k]?.getD 0#32).toNat < s_base.core.cur_vars) →
      (∀ u < s_base.core.cur_vars, tmk_m[u]?.getD 0#32 ≠ 0#32 →
        1 ≤ (tmk_m[u]?.getD 0#32).toNat ∧ (tmk_m[u]?.getD 0#32).toNat ≤ nv_m.toNat ∧
        ∃ k < nv_m.toNat, (exp_m[k]?.getD 0#32).toNat = u) →
      (FullMem c
        { s_base with
          core := { s_base.core with tmp := tmp_m }
          scratch := { s_base.scratch with wsort := exp_m, tarjan_mark := tmk_m } } ⋆ R) mm →
      Bm (nv_m, ab_m, sat_m, csz_m, m_idx, ()) mm) :
    wp Γ Q X
      (Expr.group
        (fun (Lm : Tup Cont [[i32, i32, i32]]) =>
          Blocks.cons (fun p =>
            Expr.let_ ⟨OpCode.cmp CmpOp.ult i32 Ty.bool rfl,
                (Arg.var p.snd.snd.fst, Arg.var sz, ())⟩ fun p1 =>
            Expr.jnz (Arg.var p1.fst)
              (Expr.let_ ⟨OpCode.zext 32 64, (Arg.var w, ())⟩ fun p2 =>
               Expr.let_ ⟨OpCode.add i64, (Arg.var p2.fst, Arg.imm 3, ())⟩ fun p3 =>
               Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p.snd.snd.fst, ())⟩ fun p4 =>
               Expr.let_ ⟨OpCode.add i64, (Arg.var p3.fst, Arg.var p4.fst, ())⟩ fun p5 =>
               Expr.let_ ⟨OpCode.mul i64, (Arg.var p5.fst, Arg.imm 4, ())⟩ fun p6 =>
               Expr.let_ ⟨OpCode.add i64, (Arg.var pAr, Arg.var p6.fst, ())⟩ fun p7 =>
               Expr.load i32 (Arg.var p7.fst) fun ld_l =>
               Expr.group
                 (fun (_ : Tup Cont [[i32, .bool, .bool, i32]]) =>
                   Blocks.cons (fun p8 =>
                     Expr.let_ ⟨OpCode.add i32, (Arg.var p.snd.snd.fst, Arg.imm 1, ())⟩
                       fun pm1 =>
                     Expr.jump Lm.fst
                       (Arg.var p8.fst, Arg.var p8.snd.snd.snd.fst, Arg.var pm1.fst, ()))
                     Blocks.nil)
                 fun Js2 =>
               Expr.let_ ⟨OpCode.cmp CmpOp.ne i32 Ty.bool rfl,
                   (Arg.var ld_l, Arg.var except, ())⟩ fun p8 =>
               Expr.jnz (Arg.var p8.fst)
                 (Expr.let_ ⟨OpCode.zext 32 64, (Arg.var ld_l, ())⟩ fun p9 =>
                  Expr.let_ ⟨OpCode.add i64, (Arg.var pVals, Arg.var p9.fst, ())⟩ fun p10 =>
                  Expr.load i8 (Arg.var p10.fst) fun ld1 =>
                  Expr.let_ ⟨OpCode.trunc 32 8, (Arg.imm 0, ())⟩ fun p11 =>
                  Expr.let_ ⟨OpCode.sext 8 32, (Arg.var ld1, ())⟩ fun p12 =>
                  Expr.let_ ⟨OpCode.sext 8 32, (Arg.var p11.fst, ())⟩ fun p13 =>
                  Expr.let_ ⟨OpCode.cmp CmpOp.sgt i32 Ty.bool rfl,
                      (Arg.var p12.fst, Arg.var p13.fst, ())⟩ fun p14 =>
                  Expr.jnz (Arg.var p14.fst)
                    (Expr.jump Bm
                      (Arg.var p.fst, Arg.var ab_i, Arg.imm true, Arg.var p.snd.fst,
                       Arg.var p.snd.snd.fst, ()))
                    (Expr.group
                      (fun (_ : Tup Cont [[i32, .bool, i32]]) =>
                        Blocks.cons (fun ps =>
                          Expr.jump Js2.fst
                            (Arg.var ps.fst, Arg.var ps.snd.fst, Arg.imm false,
                             Arg.var ps.snd.snd.fst, ())) Blocks.nil)
                      fun Js3 =>
                    Expr.let_ ⟨OpCode.trunc 32 8, (Arg.imm 0, ())⟩ fun p15 =>
                    Expr.let_ ⟨OpCode.sext 8 32, (Arg.var ld1, ())⟩ fun p16 =>
                    Expr.let_ ⟨OpCode.sext 8 32, (Arg.var p15.fst, ())⟩ fun p17 =>
                    Expr.let_ ⟨OpCode.cmp CmpOp.eq i32 Ty.bool rfl,
                        (Arg.var p16.fst, Arg.var p17.fst, ())⟩ fun p18 =>
                    Expr.jnz (Arg.var p18.fst)
                      (Expr.let_ ⟨OpCode.lshr i32, (Arg.var ld_l, Arg.imm 1, ())⟩ fun p19 =>
                       Expr.group
                         (fun (_ : Tup Cont [[i32, .bool]]) =>
                           Blocks.cons (fun p20 =>
                             Expr.let_ ⟨OpCode.cmp CmpOp.uge i32 Ty.bool rfl,
                                 (Arg.var p.snd.fst, Arg.var mc, ())⟩ fun p21 =>
                             Expr.jnz (Arg.var p21.fst)
                               (Expr.jump Bm
                                 (Arg.var p20.fst, Arg.imm true, Arg.imm false,
                                  Arg.var p.snd.fst, Arg.var p.snd.snd.fst, ()))
                               (Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p.snd.fst, ())⟩ fun p22 =>
                                Expr.let_ ⟨OpCode.mul i64, (Arg.var p22.fst, Arg.imm 4, ())⟩
                                  fun p23 =>
                                Expr.let_ ⟨OpCode.add i64, (Arg.var pTmp, Arg.var p23.fst, ())⟩
                                  fun p24 =>
                                Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p19.fst, ())⟩ fun p25 =>
                                Expr.let_ ⟨OpCode.mul i64, (Arg.var p25.fst, Arg.imm 4, ())⟩
                                  fun p26 =>
                                Expr.let_ ⟨OpCode.add i64, (Arg.var pTmk, Arg.var p26.fst, ())⟩
                                  fun p27 =>
                                Expr.load i32 (Arg.var p27.fst) fun ld2 =>
                                Expr.let_ ⟨OpCode.sub i32, (Arg.var ld2, Arg.imm 1, ())⟩ fun p28 =>
                                Expr.let_ ⟨OpCode.shl i32, (Arg.var p28.fst, Arg.imm 1, ())⟩
                                  fun p29 =>
                                Expr.let_ ⟨OpCode.and i32, (Arg.var ld_l, Arg.imm 1, ())⟩ fun p30 =>
                                Expr.let_ ⟨OpCode.or i32, (Arg.var p29.fst, Arg.var p30.fst, ())⟩
                                  fun p31 =>
                                Expr.store (t := i32) (Arg.var p31.fst) (Arg.var p24.fst)
                                  (Expr.let_ ⟨OpCode.add i32, (Arg.var p.snd.fst, Arg.imm 1, ())⟩
                                     fun pc1 =>
                                   Expr.jump Js3.fst
                                     (Arg.var p20.fst, Arg.var p20.snd.fst, Arg.var pc1.fst, ()))))
                             Blocks.nil)
                         fun Js4 =>
                       Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p19.fst, ())⟩ fun p20 =>
                       Expr.let_ ⟨OpCode.mul i64, (Arg.var p20.fst, Arg.imm 4, ())⟩ fun p21 =>
                       Expr.let_ ⟨OpCode.add i64, (Arg.var pTmk, Arg.var p21.fst, ())⟩ fun p22 =>
                       Expr.load i32 (Arg.var p22.fst) fun ld3 =>
                       Expr.let_ ⟨OpCode.cmp CmpOp.eq i32 Ty.bool rfl,
                           (Arg.var ld3, Arg.imm 0, ())⟩ fun p23 =>
                       Expr.jnz (Arg.var p23.fst)
                         (Expr.let_ ⟨OpCode.cmp CmpOp.uge i32 Ty.bool rfl,
                              (Arg.var p.fst, Arg.imm 256, ())⟩ fun p24 =>
                          Expr.jnz (Arg.var p24.fst)
                            (Expr.jump Bm
                              (Arg.var p.fst, Arg.imm true, Arg.imm false, Arg.var p.snd.fst,
                               Arg.var p.snd.snd.fst, ()))
                            (Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p.fst, ())⟩ fun p25 =>
                             Expr.let_ ⟨OpCode.add i64, (Arg.var c.hdr, Arg.imm 776, ())⟩ fun p26 =>
                             Expr.load i64 (Arg.var p26.fst) fun ld4 =>
                             Expr.let_ ⟨OpCode.sext 32 64, (Arg.imm 1, ())⟩ fun p27 =>
                             Expr.let_ ⟨OpCode.shl i64, (Arg.var ld4, Arg.var p27.fst, ())⟩
                               fun p28 =>
                             Expr.let_ ⟨OpCode.cmp CmpOp.uge i64 Ty.bool rfl,
                                 (Arg.var p25.fst, Arg.var p28.fst, ())⟩ fun p29 =>
                             Expr.jnz (Arg.var p29.fst)
                               (Expr.jump Bm
                                 (Arg.var p.fst, Arg.imm true, Arg.imm false, Arg.var p.snd.fst,
                                  Arg.var p.snd.snd.fst, ()))
                               (Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p.fst, ())⟩ fun p30 =>
                                Expr.let_ ⟨OpCode.mul i64, (Arg.var p30.fst, Arg.imm 4, ())⟩
                                  fun p31 =>
                                Expr.let_ ⟨OpCode.add i64, (Arg.var pExp, Arg.var p31.fst, ())⟩
                                  fun p32 =>
                                Expr.store (t := i32) (Arg.var p19.fst) (Arg.var p32.fst)
                                  (Expr.let_ ⟨OpCode.add i32, (Arg.var p.fst, Arg.imm 1, ())⟩
                                     fun pn1 =>
                                   Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p19.fst, ())⟩ fun p33 =>
                                   Expr.let_ ⟨OpCode.mul i64, (Arg.var p33.fst, Arg.imm 4, ())⟩
                                     fun p34 =>
                                   Expr.let_ ⟨OpCode.add i64, (Arg.var pTmk, Arg.var p34.fst, ())⟩
                                     fun p35 =>
                                   Expr.store (t := i32) (Arg.var pn1.fst) (Arg.var p35.fst)
                                     (Expr.jump Js4.fst (Arg.var pn1.fst, Arg.var ab_i, ()))))))
                         (Expr.jump Js4.fst (Arg.var p.fst, Arg.var ab_i, ())))
                      (Expr.jump Js3.fst (Arg.var p.fst, Arg.var ab_i, Arg.var p.snd.fst, ()))))
                 (Expr.jump Js2.fst
                   (Arg.var p.fst, Arg.var ab_i, Arg.imm false, Arg.var p.snd.fst, ())))
              (Expr.jump Bm
                (Arg.var p.fst, Arg.var ab_i, Arg.imm false, Arg.var p.snd.fst,
                 Arg.var p.snd.snd.fst, ())))
            Blocks.nil)
        fun Lm => Expr.jump Lm.fst (Arg.var nv_i, Arg.imm 0, Arg.imm 0, ())) m_init := by
  subst hpAr hpVals hpTmk hpExp hpTmp
  refine wp_loop_group (ts := [i32, i32, i32])
    (fun rem_m (nv_m, csz_m, m_idx, ()) mm =>
      ∃ (exp_m tmk_m tmp_m : List (BitVec 32)),
        let sm : FullState :=
          { s_base with
            core := { s_base.core with tmp := tmp_m }
            scratch := { s_base.scratch with wsort := exp_m, tarjan_mark := tmk_m } }
        exp_m.length = 2 * c.max_vars ∧ tmk_m.length = 2 * c.max_vars ∧
        tmp_m.length = c.max_vars ∧ m_idx.toNat ≤ sz.toNat ∧
        rem_m = sz.toNat - m_idx.toNat ∧
        nv_m.toNat ≤ 256 ∧ nv_m.toNat ≤ 2 * s_base.core.cur_vars ∧ csz_m.toNat ≤ mc.toNat ∧
        (∀ k < nv_m.toNat, (exp_m[k]?.getD 0#32).toNat < s_base.core.cur_vars) ∧
        (∀ u < s_base.core.cur_vars, tmk_m[u]?.getD 0#32 ≠ 0#32 →
          1 ≤ (tmk_m[u]?.getD 0#32).toNat ∧ (tmk_m[u]?.getD 0#32).toNat ≤ nv_m.toNat ∧
          ∃ k < nv_m.toNat, (exp_m[k]?.getD 0#32).toNat = u) ∧
        (FullMem c sm ⋆ R) mm) ?_ ?_
  · rintro Lm rem_m ⟨nv_m, csz_m, m_idx, ⟨⟩⟩ mm hLm
      ⟨exp_m, tmk_m, tmp_m, hexpm, htmkm, htmpm, hm_le, rfl, hnv256m, hnvcvm, hcszm, hexpbm,
       htmkinvm, hmm⟩
    c0_hsplit
    · have hm_lt : m_idx.toNat < sz.toNat := hc
      have hm1 : (m_idx + 1#32).toNat = m_idx.toNat + 1 := m8_k6c_add1_toNat (by omega)
      have har_lt29 : c.arena_cap < 2 * 2 ^ 28 := c.harena
      have hm_ar_eq : (w.setWidth 64 + 3#64 + m_idx.setWidth 64).toNat =
          w.toNat + 3 + m_idx.toNat := by
        rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_setWidth,
          show (3#64 : BitVec 64).toNat = 3 from rfl,
          Nat.mod_eq_of_lt (by have := w.isLt; omega),
          Nat.mod_eq_of_lt (by omega),
          Nat.mod_eq_of_lt (by have := m_idx.isLt; omega),
          Nat.mod_eq_of_lt (by omega)]
      have hm_ar_bd : (w.setWidth 64 + 3#64 + m_idx.setWidth 64).toNat <
          s_base.core.arena.length := by rw [har_len, hm_ar_eq]; omega
      let l := s_base.core.arena[(w.setWidth 64 + 3#64 + m_idx.setWidth 64).toNat]'hm_ar_bd
      have hl_lt : l.toNat < 2 * s_base.core.cur_vars := by
        dsimp only [l]
        have hget : (s_base.core.arena[w.toNat + 3 + m_idx.toNat]?.getD 0#32).toNat =
            (s_base.core.arena[(w.setWidth 64 + 3#64 + m_idx.setWidth 64).toNat]'
              hm_ar_bd).toNat := by
          rw [List.getElem?_eq_getElem (by rw [har_len]; omega), Option.getD_some]
          exact congrArg BitVec.toNat (m6_getElem_congr hm_ar_eq.symm _ _)
        rw [← hget]; exact hw_lits_lt m_idx.toNat hm_lt
      c0_hsteps_nogrp
      refine wp_join_group (ts := [i32, .bool, .bool, i32])
        (fun (nv_o, _ab_o, _sat_o, csz_o, ()) mo =>
          ∃ (exp_o tmk_o tmp_o : List (BitVec 32)),
            let so : FullState :=
              { s_base with
                core := { s_base.core with tmp := tmp_o }
                scratch := { s_base.scratch with wsort := exp_o, tarjan_mark := tmk_o } }
            exp_o.length = 2 * c.max_vars ∧ tmk_o.length = 2 * c.max_vars ∧
            tmp_o.length = c.max_vars ∧ nv_o.toNat ≤ 256 ∧ nv_o.toNat ≤ 2 * s_base.core.cur_vars ∧
            csz_o.toNat ≤ mc.toNat ∧
            (∀ k < nv_o.toNat, (exp_o[k]?.getD 0#32).toNat < s_base.core.cur_vars) ∧
            (∀ u < s_base.core.cur_vars, tmk_o[u]?.getD 0#32 ≠ 0#32 →
              1 ≤ (tmk_o[u]?.getD 0#32).toNat ∧ (tmk_o[u]?.getD 0#32).toNat ≤ nv_o.toNat ∧
              ∃ k < nv_o.toNat, (exp_o[k]?.getD 0#32).toNat = u) ∧
            (FullMem c so ⋆ R) mo) ?_ ?_
      · rintro _ ⟨nv_o, _ab_o, _sat_o, csz_o, ⟨⟩⟩ mo
          ⟨exp_o, tmk_o, tmp_o, hexpo, htmko, htmpo, hnv256o, hnvcvo, hcszo, hexpbo, htmkinvo, hmo⟩
        c0_hsteps!
        exact hLm (sz.toNat - (m_idx + 1#32).toNat) (nv_o, csz_o, m_idx + 1#32, ()) mo
          (by simp [hm1]; omega)
          ⟨exp_o, tmk_o, tmp_o, hexpo, htmko, htmpo, by omega, by simp [hm1], hnv256o, hnvcvo,
           hcszo, hexpbo, htmkinvo, hmo⟩
      · intro _ hJ2
        c0_hsplit
        · have hl_val_bd : (l.setWidth 64).toNat < s_base.core.vals.length := by
            rw [hvals_len, m6_zext32_toNat]; omega
          c0_hsplit
          · c0_hsteps!
            exact hBm nv_m ab_i true csz_m m_idx exp_m tmk_m tmp_m mm
              hexpm htmkm htmpm hnv256m hnvcvm hcszm hexpbm htmkinvm hmm
          · clear hc
            c0_hsteps_nogrp
            refine wp_join_group (ts := [i32, .bool, i32])
              (fun (nv_o, ab_o, csz_o, ()) mo =>
                ab_o = false ∧
                ∃ (exp_o tmk_o tmp_o : List (BitVec 32)),
                  let so : FullState :=
                    { s_base with
                      core := { s_base.core with tmp := tmp_o }
                      scratch := { s_base.scratch with wsort := exp_o, tarjan_mark := tmk_o } }
                  exp_o.length = 2 * c.max_vars ∧ tmk_o.length = 2 * c.max_vars ∧
                  tmp_o.length = c.max_vars ∧ nv_o.toNat ≤ 256 ∧
                  nv_o.toNat ≤ 2 * s_base.core.cur_vars ∧ csz_o.toNat ≤ mc.toNat ∧
                  (∀ k < nv_o.toNat, (exp_o[k]?.getD 0#32).toNat < s_base.core.cur_vars) ∧
                  (∀ u < s_base.core.cur_vars, tmk_o[u]?.getD 0#32 ≠ 0#32 →
                    1 ≤ (tmk_o[u]?.getD 0#32).toNat ∧ (tmk_o[u]?.getD 0#32).toNat ≤ nv_o.toNat ∧
                    ∃ k < nv_o.toNat, (exp_o[k]?.getD 0#32).toNat = u) ∧
                  (FullMem c so ⋆ R) mo) ?_ ?_
            · rintro _ ⟨nv_o, ab_o, csz_o, ⟨⟩⟩ mo
                ⟨rfl, exp_o, tmk_o, tmp_o, hexpo, htmko, htmpo, hnv256o, hnvcvo, hcszo, hexpbo,
                 htmkinvo, hmo⟩
              c0_hsteps!
              exact hJ2 _ _ ⟨exp_o, tmk_o, tmp_o, hexpo, htmko, htmpo, hnv256o, hnvcvo, hcszo,
                hexpbo, htmkinvo, hmo⟩
            · intro _ hJ3
              c0_hsplit
              · have hlv := m8_k6c_shr1_lt hl_lt
                let lv := l >>> (1 : Nat)
                have hlv_cv : lv.toNat < s_base.core.cur_vars := hlv.2
                have hlv_tmk : (lv.setWidth 64).toNat < tmk_m.length := by
                  dsimp only [lv]; rw [htmkm, m6_zext32_toNat]; omega
                c0_hsteps_nogrp
                refine wp_join_group (ts := [i32, .bool])
                  (fun (nv_n, ab_n, ()) mn =>
                    ab_n = false ∧
                    ∃ (exp_n tmk_n : List (BitVec 32)),
                      let sn : FullState :=
                        { s_base with
                          core := { s_base.core with tmp := tmp_m }
                          scratch :=
                            { s_base.scratch with wsort := exp_n, tarjan_mark := tmk_n } }
                      exp_n.length = 2 * c.max_vars ∧ tmk_n.length = 2 * c.max_vars ∧
                      nv_n.toNat ≤ 256 ∧ nv_n.toNat ≤ 2 * s_base.core.cur_vars ∧
                      (∀ k < nv_n.toNat, (exp_n[k]?.getD 0#32).toNat < s_base.core.cur_vars) ∧
                      (∀ u < s_base.core.cur_vars, tmk_n[u]?.getD 0#32 ≠ 0#32 →
                        1 ≤ (tmk_n[u]?.getD 0#32).toNat ∧ (tmk_n[u]?.getD 0#32).toNat ≤ nv_n.toNat ∧
                        ∃ k < nv_n.toNat, (exp_n[k]?.getD 0#32).toNat = u) ∧
                      1 ≤ (tmk_n[lv.toNat]?.getD 0#32).toNat ∧
                      (tmk_n[lv.toNat]?.getD 0#32).toNat ≤ nv_n.toNat ∧
                      (FullMem c sn ⋆ R) mn) ?_ ?_
                · rintro _ ⟨nv_n, ab_n, ⟨⟩⟩ mn
                    ⟨hab_fn, exp_n, tmk_n, hexpn, htmkn, hnv256n, hnvcvn, hexpbn, htmkinvn, ht1n,
                     ht2n, hmn⟩
                  c0_hsplit
                  · c0_hsteps!
                    exact hBm nv_n true false csz_m m_idx exp_n tmk_n tmp_m mn
                      hexpn htmkn htmpm hnv256n hnvcvn hcszm hexpbn htmkinvn hmn
                  · have hcsz_lt : csz_m.toNat < mc.toNat := Nat.lt_of_not_le hc
                    have hcsz1 : (csz_m + 1#32).toNat = csz_m.toNat + 1 :=
                      m8_k6c_add1_toNat (by omega)
                    have hcsz_tmp : (csz_m.setWidth 64).toNat < tmp_m.length := by
                      rw [htmpm, m6_zext32_toNat]; omega
                    have hlv_tmkn : (lv.setWidth 64).toNat < tmk_n.length := by
                      dsimp only [lv]; rw [htmkn, m6_zext32_toNat]; omega
                    c0_hsteps!
                    exact hJ3 _ _ ⟨hab_fn, exp_n, tmk_n, tmp_m.set (csz_m.setWidth 64).toNat _,
                      hexpn, htmkn, by simp [htmpm], hnv256n, hnvcvn,
                      by rw [show (csz_m + 1 : BitVec 32).toNat = csz_m.toNat + 1 from
                        m8_k6c_add1_toNat (by omega)]; omega,
                      hexpbn, htmkinvn, hm⟩
                · intro _ hJ4
                  c0_hsplit
                  · have htmk0_lv : tmk_m[lv.toNat]?.getD 0#32 = 0#32 := by
                      rw [List.getElem?_eq_getElem (by rw [htmkm]; omega), Option.getD_some]
                      simpa [lv, l, m6_zext32_toNat, BitVec.toNat_ushiftRight,
                        Nat.shiftRight_eq_div_pow,
                        Nat.mod_eq_of_lt (by omega : w.toNat + 3 + m_idx.toNat < 2 ^ 64)] using hc
                    c0_hsplit
                    · c0_hsteps!
                      exact hBm nv_m true false csz_m m_idx exp_m tmk_m tmp_m mm
                        hexpm htmkm htmpm hnv256m hnvcvm hcszm hexpbm htmkinvm hmm
                    · have hnv256_lt : nv_m.toNat < 256 :=
                        Nat.lt_of_not_le (show ¬ 256 ≤ nv_m.toNat from hc)
                      clear hc
                      c0_hsplit
                      · c0_hsteps!
                        exact hBm nv_m true false csz_m m_idx exp_m tmk_m tmp_m mm
                          hexpm htmkm htmpm hnv256m hnvcvm hcszm hexpbm htmkinvm hmm
                      · have hnvcv_lt : nv_m.toNat < 2 * s_base.core.cur_vars := by
                          have hlt' : nv_m.toNat < (2 * (s_base.core.cur_vars % 2 ^ 64)) % 2 ^ 64 :=
                            by simpa [m6_zext32_toNat] using Nat.lt_of_not_le hc
                          rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hlt'
                          exact hlt'
                        have hexp_bd : (nv_m.setWidth 64).toNat < exp_m.length := by
                          rw [hexpm, m6_zext32_toNat]; omega
                        have hreg := m8_k6c_tmk_reg hnv256_lt hnvcv_lt (by rw [hexpm]; omega) htmkm
                          hcv_le hlv_cv hexpbm htmkinvm
                        c0_hsteps!
                        rw [m6_zext32_toNat] at hm
                        exact hJ4 _ _ ⟨hab_fi, exp_m.set nv_m.toNat lv,
                          tmk_m.set lv.toNat (nv_m + 1#32), by simp [hexpm], by simp [htmkm],
                          hreg.2.1, hreg.2.2.1, hreg.2.2.2.1, hreg.2.2.2.2.1, hreg.2.2.2.2.2.1,
                          hreg.2.2.2.2.2.2, hm⟩
                  · have htmk_nz : tmk_m[lv.toNat]?.getD 0#32 ≠ 0#32 := by
                      rw [List.getElem?_eq_getElem (by rw [htmkm]; omega), Option.getD_some]
                      intro h0; apply hc
                      simpa [lv, l, m6_zext32_toNat, hm_ar_eq, BitVec.toNat_ushiftRight,
                        Nat.shiftRight_eq_div_pow,
                        Nat.mod_eq_of_lt (by omega : w.toNat + 3 + m_idx.toNat < 2 ^ 64)] using h0
                    have hinv_lv := htmkinvm lv.toNat hlv_cv htmk_nz
                    c0_hsteps!
                    exact hJ4 _ _ ⟨hab_fi, exp_m, tmk_m, hexpm, htmkm, hnv256m, hnvcvm,
                      hexpbm, htmkinvm, hinv_lv.1, hinv_lv.2.1, hmm⟩
              · c0_hsteps!
                exact hJ3 _ _ ⟨hab_fi, exp_m, tmk_m, tmp_m, hexpm, htmkm, htmpm, hnv256m, hnvcvm,
                  hcszm, hexpbm, htmkinvm, hmm⟩
        · c0_hsteps!
          exact hJ2 _ _ ⟨exp_m, tmk_m, tmp_m, hexpm, htmkm, htmpm, hnv256m, hnvcvm, hcszm, hexpbm,
            htmkinvm, hmm⟩
    · c0_hsteps!
      exact hBm nv_m ab_i false csz_m m_idx exp_m tmk_m tmp_m mm
        hexpm htmkm htmpm hnv256m hnvcvm hcszm hexpbm htmkinvm hmm
  · intro Lm hLm; c0_hsteps!
    exact hLm sz.toNat (nv_i, 0#32, 0#32, ()) m_init
      ⟨s_base.scratch.wsort, s_base.scratch.tarjan_mark, s_base.core.tmp, hexp_l, htmk_l, htmp_l,
       Nat.zero_le _, rfl, hnv256, hnvcv, Nat.zero_le _, hexp_bnd, htmk_inv,
       m8_k6c_fullMem_subst hm_init⟩

/-! ## 6. K6 Header/Workspace Initialization Sub-Phase (`m8_k6c_init_solve_wp`) -/

private def m8_k6c_scr_h (scr_e : List (BitVec 32))
    (nv_s nc_s tick_lim alen_s acap_w nunits_s : BitVec 32) : List (BitVec 32) :=
  (((((((((((((((((((((scr_e.set 4192 nv_s).set 4193 nc_s).set
    4194 nc_s).set 4195 0#32).set 4196 0#32).set 4197 0#32).set
    4198 nv_s).set 4199 0xFFFFFFFF#32).set 4200 0#32).set
    4201 (nv_s - 1#32)).set 4202 (nv_s - 1#32)).set
    4203 nv_s).set 4204 0#32).set 4205 tick_lim).set
    4206 alen_s).set 4207 acap_w).set
    4208 0#32).set 4209 0#32).set 4210 0#32).set
    4211 nunits_s).set 4212 0#32).set 4213 0#32

private theorem m8_k6c_scr_h_props {scr_e : List (BitVec 32)} {cap : Nat}
    (hlen : scr_e.length = cap) (h16384 : 16384 ≤ cap)
    (nv_s nc_s tick_lim alen_s acap_w nunits_s : BitVec 32) :
    let scr_h := m8_k6c_scr_h scr_e nv_s nc_s tick_lim alen_s acap_w nunits_s
    scr_h.length = cap ∧
    (∀ k < 4192, scr_h[k]? = scr_e[k]?) ∧
    (∀ k, 11648 ≤ k → k < 14720 → scr_h[k]? = scr_e[k]?) ∧
    scr_h[4193]? = some nc_s ∧ scr_h[4194]? = some nc_s ∧
    scr_h[4206]? = some alen_s ∧ scr_h[4207]? = some acap_w := by
  refine ⟨by simp [m8_k6c_scr_h, hlen], fun k hk => ?_, fun k hk1 hk2 => ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [m8_k6c_scr_h]; repeat rw [List.getElem?_set_ne (by omega)]
  · dsimp only [m8_k6c_scr_h]; repeat rw [List.getElem?_set_ne (by omega)]
  · dsimp only [m8_k6c_scr_h]; repeat rw [List.getElem?_set_ne (by decide)]
    exact List.getElem?_set_self (by simp [hlen]; omega)
  · dsimp only [m8_k6c_scr_h]; repeat rw [List.getElem?_set_ne (by decide)]
    exact List.getElem?_set_self (by simp [hlen]; omega)
  · dsimp only [m8_k6c_scr_h]; repeat rw [List.getElem?_set_ne (by decide)]
    exact List.getElem?_set_self (by simp [hlen]; omega)
  · dsimp only [m8_k6c_scr_h]; repeat rw [List.getElem?_set_ne (by decide)]
    exact List.getElem?_set_self (by simp [hlen]; omega)

/-- Initializes `22` K6 header words `scr[4192..4213]`, variable arrays `M8_KO_{LVL..QNEXT}`,
and literal arrays `M8_KO_{VALS,WHEAD}` inside `s_clr.scratch.scratch_buf`, constructs
`M8K6BufOk scr2`, and transfers to `hw_wp`. -/
theorem m8_k6c_init_solve_wp (Γ : Env) (Q : Post [.bool]) (X : XPost)
    (c : FullCfg) (s0 s_clr : FullState) (R : Mem 64 → Prop)
    (pScr : BitVec 64) (nv_s nc_s tick_lim alen_s acap_v nunits_s : BitVec 32)
    (scr_e : List (BitVec 32)) (m_init : Mem 64) (k_watch : Expr Val Cont [.bool])
    (hpScr : pScr = c.pScratchBuf)
    (hsc28 : c.scratch_cap < 2 * 2 ^ 28) (h16384 : 16384 ≤ c.scratch_cap)
    (hscre_l : scr_e.length = c.scratch_cap)
    (hscre_s : s_clr.scratch.scratch_buf = scr_e)
    (hnv_pos : 0 < nv_s.toNat) (hnv256 : nv_s.toNat ≤ 256)
    (hnc_ge2 : 2 ≤ nc_s.toNat) (hnc512 : nc_s.toNat ≤ 512)
    (hal_le : alen_s.toNat ≤ c.scratch_cap - 15744)
    (hacap_eq : acap_v = BitVec.ofNat 32 (c.scratch_cap - 15744))
    (hscre_pre : ∀ k < 4192, scr_e[k]? = s0.scratch.scratch_buf[k]?)
    (hcls_e : ∀ cid < nc_s.toNat,
      (scr_e[11648 + cid]?.getD 0#32).toNat +
        ((scr_e[12672 + cid]?.getD 0#32) &&& 0xFFFF#32).toNat ≤ alen_s.toNat ∧
      ((scr_e[12672 + cid]?.getD 0#32) &&& 0x40000000#32) = 0#32)
    (hm_init : (FullMem c s_clr ⋆ R) m_init)
    (hw_wp : ∀ (scr2 : List (BitVec 32)) (m2 : Mem 64),
      scr2.length = c.scratch_cap →
      (∀ k < 4192, scr2[k]? = s0.scratch.scratch_buf[k]?) →
      M8K6BufOk scr2 →
      scr2[4193]? = some nc_s → scr2[4194]? = some nc_s →
      (FullMem c { s_clr with scratch := { s_clr.scratch with scratch_buf := scr2 } } ⋆ R) m2 →
      wp Γ Q X k_watch m2) :
    wp Γ Q X
      (Expr.let_ ⟨OpCode.zext 32 64, (Arg.imm 4192, ())⟩ fun p =>
       Expr.let_ ⟨OpCode.mul i64, (Arg.var p.fst, Arg.imm 4, ())⟩ fun p =>
       Expr.let_ ⟨OpCode.add i64, (Arg.var pScr, Arg.var p.fst, ())⟩ fun p =>
       Expr.store (t := i32) (Arg.var nv_s) (Arg.var p.fst)
       (Expr.let_ ⟨OpCode.zext 32 64, (Arg.imm 4193, ())⟩ fun p =>
        Expr.let_ ⟨OpCode.mul i64, (Arg.var p.fst, Arg.imm 4, ())⟩ fun p =>
        Expr.let_ ⟨OpCode.add i64, (Arg.var pScr, Arg.var p.fst, ())⟩ fun p =>
        Expr.store (t := i32) (Arg.var nc_s) (Arg.var p.fst)
        (Expr.let_ ⟨OpCode.zext 32 64, (Arg.imm 4194, ())⟩ fun p =>
         Expr.let_ ⟨OpCode.mul i64, (Arg.var p.fst, Arg.imm 4, ())⟩ fun p =>
         Expr.let_ ⟨OpCode.add i64, (Arg.var pScr, Arg.var p.fst, ())⟩ fun p =>
         Expr.store (t := i32) (Arg.var nc_s) (Arg.var p.fst)
         (Expr.let_ ⟨OpCode.zext 32 64, (Arg.imm 4195, ())⟩ fun p =>
          Expr.let_ ⟨OpCode.mul i64, (Arg.var p.fst, Arg.imm 4, ())⟩ fun p =>
          Expr.let_ ⟨OpCode.add i64, (Arg.var pScr, Arg.var p.fst, ())⟩ fun p =>
          Expr.store (t := i32) (Arg.imm 0) (Arg.var p.fst)
          (Expr.let_ ⟨OpCode.zext 32 64, (Arg.imm 4196, ())⟩ fun p =>
           Expr.let_ ⟨OpCode.mul i64, (Arg.var p.fst, Arg.imm 4, ())⟩ fun p =>
           Expr.let_ ⟨OpCode.add i64, (Arg.var pScr, Arg.var p.fst, ())⟩ fun p =>
           Expr.store (t := i32) (Arg.imm 0) (Arg.var p.fst)
           (Expr.let_ ⟨OpCode.zext 32 64, (Arg.imm 4197, ())⟩ fun p =>
            Expr.let_ ⟨OpCode.mul i64, (Arg.var p.fst, Arg.imm 4, ())⟩ fun p =>
            Expr.let_ ⟨OpCode.add i64, (Arg.var pScr, Arg.var p.fst, ())⟩ fun p =>
            Expr.store (t := i32) (Arg.imm 0) (Arg.var p.fst)
            (Expr.let_ ⟨OpCode.zext 32 64, (Arg.imm 4198, ())⟩ fun p =>
             Expr.let_ ⟨OpCode.mul i64, (Arg.var p.fst, Arg.imm 4, ())⟩ fun p =>
             Expr.let_ ⟨OpCode.add i64, (Arg.var pScr, Arg.var p.fst, ())⟩ fun p =>
             Expr.store (t := i32) (Arg.var nv_s) (Arg.var p.fst)
             (Expr.let_ ⟨OpCode.zext 32 64, (Arg.imm 4199, ())⟩ fun p =>
              Expr.let_ ⟨OpCode.mul i64, (Arg.var p.fst, Arg.imm 4, ())⟩ fun p =>
              Expr.let_ ⟨OpCode.add i64, (Arg.var pScr, Arg.var p.fst, ())⟩ fun p =>
              Expr.store (t := i32) (Arg.imm 4294967295) (Arg.var p.fst)
              (Expr.let_ ⟨OpCode.zext 32 64, (Arg.imm 4200, ())⟩ fun p =>
               Expr.let_ ⟨OpCode.mul i64, (Arg.var p.fst, Arg.imm 4, ())⟩ fun p =>
               Expr.let_ ⟨OpCode.add i64, (Arg.var pScr, Arg.var p.fst, ())⟩ fun p =>
               Expr.store (t := i32) (Arg.imm 0) (Arg.var p.fst)
               (Expr.let_ ⟨OpCode.zext 32 64, (Arg.imm 4201, ())⟩ fun p =>
                Expr.let_ ⟨OpCode.mul i64, (Arg.var p.fst, Arg.imm 4, ())⟩ fun p =>
                Expr.let_ ⟨OpCode.add i64, (Arg.var pScr, Arg.var p.fst, ())⟩ fun p =>
                Expr.let_ ⟨OpCode.sub i32, (Arg.var nv_s, Arg.imm 1, ())⟩ fun ps1 =>
                Expr.store (t := i32) (Arg.var ps1.fst) (Arg.var p.fst)
                (Expr.let_ ⟨OpCode.zext 32 64, (Arg.imm 4202, ())⟩ fun p =>
                 Expr.let_ ⟨OpCode.mul i64, (Arg.var p.fst, Arg.imm 4, ())⟩ fun p =>
                 Expr.let_ ⟨OpCode.add i64, (Arg.var pScr, Arg.var p.fst, ())⟩ fun p =>
                 Expr.let_ ⟨OpCode.sub i32, (Arg.var nv_s, Arg.imm 1, ())⟩ fun ps2 =>
                 Expr.store (t := i32) (Arg.var ps2.fst) (Arg.var p.fst)
                 (Expr.let_ ⟨OpCode.zext 32 64, (Arg.imm 4203, ())⟩ fun p =>
                  Expr.let_ ⟨OpCode.mul i64, (Arg.var p.fst, Arg.imm 4, ())⟩ fun p =>
                  Expr.let_ ⟨OpCode.add i64, (Arg.var pScr, Arg.var p.fst, ())⟩ fun p =>
                  Expr.store (t := i32) (Arg.var nv_s) (Arg.var p.fst)
                  (Expr.let_ ⟨OpCode.zext 32 64, (Arg.imm 4204, ())⟩ fun p =>
                   Expr.let_ ⟨OpCode.mul i64, (Arg.var p.fst, Arg.imm 4, ())⟩ fun p =>
                   Expr.let_ ⟨OpCode.add i64, (Arg.var pScr, Arg.var p.fst, ())⟩ fun p =>
                   Expr.store (t := i32) (Arg.imm 0) (Arg.var p.fst)
                   (Expr.let_ ⟨OpCode.zext 32 64, (Arg.imm 4205, ())⟩ fun p =>
                    Expr.let_ ⟨OpCode.mul i64, (Arg.var p.fst, Arg.imm 4, ())⟩ fun p =>
                    Expr.let_ ⟨OpCode.add i64, (Arg.var pScr, Arg.var p.fst, ())⟩ fun p =>
                    Expr.store (t := i32) (Arg.var tick_lim) (Arg.var p.fst)
                    (Expr.let_ ⟨OpCode.zext 32 64, (Arg.imm 4206, ())⟩ fun p =>
                     Expr.let_ ⟨OpCode.mul i64, (Arg.var p.fst, Arg.imm 4, ())⟩ fun p =>
                     Expr.let_ ⟨OpCode.add i64, (Arg.var pScr, Arg.var p.fst, ())⟩ fun p =>
                     Expr.store (t := i32) (Arg.var alen_s) (Arg.var p.fst)
                     (Expr.let_ ⟨OpCode.zext 32 64, (Arg.imm 4207, ())⟩ fun p =>
                      Expr.let_ ⟨OpCode.mul i64, (Arg.var p.fst, Arg.imm 4, ())⟩ fun p =>
                      Expr.let_ ⟨OpCode.add i64, (Arg.var pScr, Arg.var p.fst, ())⟩ fun p =>
                      Expr.store (t := i32) (Arg.var acap_v) (Arg.var p.fst)
                      (Expr.let_ ⟨OpCode.zext 32 64, (Arg.imm 4208, ())⟩ fun p =>
                       Expr.let_ ⟨OpCode.mul i64, (Arg.var p.fst, Arg.imm 4, ())⟩ fun p =>
                       Expr.let_ ⟨OpCode.add i64, (Arg.var pScr, Arg.var p.fst, ())⟩ fun p =>
                       Expr.store (t := i32) (Arg.imm 0) (Arg.var p.fst)
                       (Expr.let_ ⟨OpCode.zext 32 64, (Arg.imm 4209, ())⟩ fun p =>
                        Expr.let_ ⟨OpCode.mul i64, (Arg.var p.fst, Arg.imm 4, ())⟩ fun p =>
                        Expr.let_ ⟨OpCode.add i64, (Arg.var pScr, Arg.var p.fst, ())⟩ fun p =>
                        Expr.store (t := i32) (Arg.imm 0) (Arg.var p.fst)
                        (Expr.let_ ⟨OpCode.zext 32 64, (Arg.imm 4210, ())⟩ fun p =>
                         Expr.let_ ⟨OpCode.mul i64, (Arg.var p.fst, Arg.imm 4, ())⟩ fun p =>
                         Expr.let_ ⟨OpCode.add i64, (Arg.var pScr, Arg.var p.fst, ())⟩ fun p =>
                         Expr.store (t := i32) (Arg.imm 0) (Arg.var p.fst)
                         (Expr.let_ ⟨OpCode.zext 32 64, (Arg.imm 4211, ())⟩ fun p =>
                          Expr.let_ ⟨OpCode.mul i64, (Arg.var p.fst, Arg.imm 4, ())⟩ fun p =>
                          Expr.let_ ⟨OpCode.add i64, (Arg.var pScr, Arg.var p.fst, ())⟩ fun p =>
                          Expr.store (t := i32) (Arg.var nunits_s) (Arg.var p.fst)
                          (Expr.let_ ⟨OpCode.zext 32 64, (Arg.imm 4212, ())⟩ fun p =>
                           Expr.let_ ⟨OpCode.mul i64, (Arg.var p.fst, Arg.imm 4, ())⟩ fun p =>
                           Expr.let_ ⟨OpCode.add i64, (Arg.var pScr, Arg.var p.fst, ())⟩ fun p =>
                           Expr.store (t := i32) (Arg.imm 0) (Arg.var p.fst)
                           (Expr.let_ ⟨OpCode.zext 32 64, (Arg.imm 4213, ())⟩ fun p =>
                            Expr.let_ ⟨OpCode.mul i64, (Arg.var p.fst, Arg.imm 4, ())⟩ fun p =>
                            Expr.let_ ⟨OpCode.add i64, (Arg.var pScr, Arg.var p.fst, ())⟩ fun p =>
                            Expr.store (t := i32) (Arg.imm 0) (Arg.var p.fst)
                            (Expr.group (fun (L1 : Tup Cont [[i32]]) =>
                              Blocks.cons (fun (p : Tup Val [i32]) =>
                              Expr.let_ ⟨OpCode.cmp CmpOp.ult i32 Ty.bool rfl,
                                  (Arg.var p.fst, Arg.var nv_s, ())⟩ fun p3 =>
                              Expr.jnz (Arg.var p3.fst)
                                (Expr.let_ ⟨OpCode.add i32, (Arg.imm 4224, Arg.var p.fst, ())⟩
                                   fun p4 =>
                                 Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p4.fst, ())⟩ fun p5 =>
                                 Expr.let_ ⟨OpCode.mul i64, (Arg.var p5.fst, Arg.imm 4, ())⟩
                                   fun p6 =>
                                 Expr.let_ ⟨OpCode.add i64, (Arg.var pScr, Arg.var p6.fst, ())⟩
                                   fun p7 =>
                                 Expr.store (t := i32) (Arg.imm 0) (Arg.var p7.fst)
                                   (Expr.let_ ⟨OpCode.add i32, (Arg.imm 4480, Arg.var p.fst, ())⟩
                                      fun p8 =>
                                    Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p8.fst, ())⟩ fun p9 =>
                                    Expr.let_ ⟨OpCode.mul i64, (Arg.var p9.fst, Arg.imm 4, ())⟩
                                      fun p10 =>
                                    Expr.let_ ⟨OpCode.add i64, (Arg.var pScr, Arg.var p10.fst, ())⟩
                                      fun p11 =>
                                    Expr.store (t := i32) (Arg.imm 4294967295) (Arg.var p11.fst)
                                      (Expr.let_ ⟨OpCode.add i32,
                                          (Arg.imm 5760, Arg.var p.fst, ())⟩ fun p12 =>
                                       Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p12.fst, ())⟩
                                         fun p13 =>
                                       Expr.let_ ⟨OpCode.mul i64, (Arg.var p13.fst, Arg.imm 4, ())⟩
                                         fun p14 =>
                                       Expr.let_ ⟨OpCode.add i64,
                                           (Arg.var pScr, Arg.var p14.fst, ())⟩ fun p15 =>
                                       Expr.store (t := i32) (Arg.imm 0) (Arg.var p15.fst)
                                         (Expr.let_ ⟨OpCode.add i32,
                                             (Arg.imm 5248, Arg.var p.fst, ())⟩ fun p16 =>
                                          Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p16.fst, ())⟩
                                            fun p17 =>
                                          Expr.let_ ⟨OpCode.mul i64,
                                              (Arg.var p17.fst, Arg.imm 4, ())⟩ fun p18 =>
                                          Expr.let_ ⟨OpCode.add i64,
                                              (Arg.var pScr, Arg.var p18.fst, ())⟩ fun p19 =>
                                          Expr.let_ ⟨OpCode.add i32, (Arg.var p.fst, Arg.imm 1, ())⟩
                                            fun p20 =>
                                          Expr.store (t := i32) (Arg.var p20.fst) (Arg.var p19.fst)
                                            (Expr.let_ ⟨OpCode.add i32,
                                                (Arg.imm 4736, Arg.var p.fst, ())⟩ fun p21 =>
                                             Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p21.fst, ())⟩
                                               fun p22 =>
                                             Expr.let_ ⟨OpCode.mul i64,
                                                 (Arg.var p22.fst, Arg.imm 4, ())⟩ fun p23 =>
                                             Expr.let_ ⟨OpCode.add i64,
                                                 (Arg.var pScr, Arg.var p23.fst, ())⟩ fun p24 =>
                                             Expr.group (fun (_ : Tup Cont [[i32]]) =>
                                               Blocks.cons (fun p25 =>
                                                 Expr.store (t := i32) (Arg.var p25.fst)
                                                   (Arg.var p24.fst)
                                                   (Expr.let_ ⟨OpCode.add i32,
                                                       (Arg.imm 4992, Arg.var p.fst, ())⟩ fun p26 =>
                                                    Expr.let_ ⟨OpCode.zext 32 64,
                                                        (Arg.var p26.fst, ())⟩ fun p27 =>
                                                    Expr.let_ ⟨OpCode.mul i64,
                                                        (Arg.var p27.fst, Arg.imm 4, ())⟩ fun p28 =>
                                                    Expr.let_ ⟨OpCode.add i64,
                                                        (Arg.var pScr, Arg.var p28.fst, ())⟩
                                                      fun p29 =>
                                                    Expr.group (fun (_ : Tup Cont [[i32]]) =>
                                                      Blocks.cons (fun p30 =>
                                                        Expr.store (t := i32) (Arg.var p30.fst)
                                                          (Arg.var p29.fst)
                                                          (Expr.let_ ⟨OpCode.add i32,
                                                              (Arg.var p.fst, Arg.imm 1, ())⟩
                                                             fun pi =>
                                                           Expr.jump L1.fst (Arg.var pi.fst, ())))
                                                        Blocks.nil)
                                                      fun Js2 =>
                                                    Expr.let_ ⟨OpCode.add i32,
                                                        (Arg.var p.fst, Arg.imm 1, ())⟩ fun p30 =>
                                                    Expr.let_ ⟨OpCode.cmp CmpOp.uge i32 Ty.bool rfl,
                                                        (Arg.var p30.fst, Arg.var nv_s, ())⟩
                                                      fun p31 =>
                                                    Expr.jnz (Arg.var p31.fst)
                                                      (Expr.jump Js2.fst (Arg.imm 4294967295, ()))
                                                      (Expr.let_ ⟨OpCode.add i32,
                                                          (Arg.var p.fst, Arg.imm 1, ())⟩ fun pi =>
                                                       Expr.jump Js2.fst (Arg.var pi.fst, ()))))
                                                 Blocks.nil)
                                               fun Js1 =>
                                             Expr.let_ ⟨OpCode.cmp CmpOp.eq i32 Ty.bool rfl,
                                                 (Arg.var p.fst, Arg.imm 0, ())⟩ fun p25 =>
                                             Expr.jnz (Arg.var p25.fst)
                                               (Expr.jump Js1.fst (Arg.imm 4294967295, ()))
                                               (Expr.let_ ⟨OpCode.sub i32,
                                                   (Arg.var p.fst, Arg.imm 1, ())⟩ fun pm1 =>
                                                Expr.jump Js1.fst (Arg.var pm1.fst, ())))))))
                                (Expr.group (fun (L2 : Tup Cont [[i32]]) =>
                                  Blocks.cons (fun (p : Tup Val [i32]) =>
                                  Expr.let_ ⟨OpCode.shl i32, (Arg.var nv_s, Arg.imm 1, ())⟩
                                    fun p4 =>
                                  Expr.let_ ⟨OpCode.cmp CmpOp.ult i32 Ty.bool rfl,
                                      (Arg.var p.fst, Arg.var p4.fst, ())⟩ fun p5 =>
                                  Expr.jnz (Arg.var p5.fst)
                                    (Expr.let_ ⟨OpCode.add i32, (Arg.imm 6528, Arg.var p.fst, ())⟩
                                       fun p6 =>
                                     Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p6.fst, ())⟩ fun p7 =>
                                     Expr.let_ ⟨OpCode.mul i64, (Arg.var p7.fst, Arg.imm 4, ())⟩
                                       fun p8 =>
                                     Expr.let_ ⟨OpCode.add i64, (Arg.var pScr, Arg.var p8.fst, ())⟩
                                       fun p9 =>
                                     Expr.store (t := i32) (Arg.imm 0) (Arg.var p9.fst)
                                       (Expr.let_ ⟨OpCode.add i32,
                                           (Arg.imm 7040, Arg.var p.fst, ())⟩ fun p10 =>
                                        Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p10.fst, ())⟩
                                          fun p11 =>
                                        Expr.let_ ⟨OpCode.mul i64, (Arg.var p11.fst, Arg.imm 4, ())⟩
                                          fun p12 =>
                                        Expr.let_ ⟨OpCode.add i64,
                                            (Arg.var pScr, Arg.var p12.fst, ())⟩ fun p13 =>
                                        Expr.store (t := i32) (Arg.imm 4294967295) (Arg.var p13.fst)
                                          (Expr.let_ ⟨OpCode.add i32,
                                              (Arg.var p.fst, Arg.imm 1, ())⟩ fun pi =>
                                            Expr.jump L2.fst (Arg.var pi.fst, ()))))
                                    k_watch) Blocks.nil)
                                  fun L2 => Expr.jump L2.fst (Arg.imm 0, ()))) Blocks.nil)
                              fun L1 => Expr.jump L1.fst
                                (Arg.imm 0, ())))))))))))))))))))))))) m_init := by
  subst hpScr hacap_eq
  have hacap_n_eq : (BitVec.ofNat 32 (c.scratch_cap - 15744)).toNat = c.scratch_cap - 15744 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hm_scr : (M8P6Scr c.scratch_cap c.pScratchBuf scr_e ⋆
      (m8_k6c_fullWithoutScr c s_clr ⋆ R)) m_init := by
    rw [← hscre_s]
    exact m8_k6c_scrBuf_split h16384 (by rw [hscre_s]; exact hscre_l) hm_init
  c0_hsteps!
  let scr_h := m8_k6c_scr_h scr_e nv_s nc_s tick_lim alen_s
    (BitVec.ofNat 32 (c.scratch_cap - 15744)) nunits_s
  have hhm_h :
      (FullMem c { s_clr with scratch := { s_clr.scratch with scratch_buf := scr_h } } ⋆ R) _ :=
    m8_k6c_scrBuf_unsplit_eq hm (by
      dsimp only [scr_h, m8_k6c_scr_h, OfNat.ofNat, instOfNatNat]
      simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod])
  obtain ⟨hscrh_l, hscrh_pre0, hscrh_meta, hscrh_1, hscrh_2, hscrh_14, hscrh_15⟩ :=
    m8_k6c_scr_h_props hscre_l h16384 nv_s nc_s tick_lim alen_s
      (BitVec.ofNat 32 (c.scratch_cap - 15744)) nunits_s
  have hscrh_pre : ∀ k < 4192, scr_h[k]? = s0.scratch.scratch_buf[k]? := fun k hk =>
    (hscrh_pre0 k hk).trans (hscre_pre k hk)
  refine wp_loop_group (ts := [i32])
    (fun rem1 (i, ()) m1 => ∃ scr1 : List (BitVec 32),
      let s1 : FullState := { s_clr with scratch := { s_clr.scratch with scratch_buf := scr1 } }
      scr1.length = c.scratch_cap ∧ i.toNat ≤ nv_s.toNat ∧ rem1 = nv_s.toNat - i.toNat ∧
      (∀ k < 4192, scr1[k]? = s0.scratch.scratch_buf[k]?) ∧
      scr1[4193]? = some nc_s ∧ scr1[4194]? = some nc_s ∧
      scr1[4206]? = some alen_s ∧
      scr1[4207]? = some (BitVec.ofNat 32 (c.scratch_cap - 15744)) ∧
      (∀ k, 11648 ≤ k → k < 14720 → scr1[k]? = scr_e[k]?) ∧
      (FullMem c s1 ⋆ R) m1) ?_ ?_
  · rintro L1 rem1 ⟨i, ⟨⟩⟩ m1 hL1
      ⟨scr1, hsc1_l, hi_le, rfl, hpre1, hs1_1, hs1_2, hs1_14, hs1_15, hmeta1, hm1⟩
    c0_hsplit
    · have hi_lt : i.toNat < nv_s.toNat := hc
      have hi1 : (i + 1#32).toNat = i.toNat + 1 := m8_k6c_add1_toNat (by omega)
      have hbd_4224 : (((@OfNat.ofNat (BitVec 32) 4224 (BitVec.instOfNat)) +
          i).setWidth 64).toNat < scr1.length := by
        rw [m8_k6c_off_add 4224 (by decide) i (by omega), hsc1_l]; omega
      have hbd_4480 : (((@OfNat.ofNat (BitVec 32) 4480 (BitVec.instOfNat)) +
          i).setWidth 64).toNat < scr1.length := by
        rw [m8_k6c_off_add 4480 (by decide) i (by omega), hsc1_l]; omega
      have hbd_5760 : (((@OfNat.ofNat (BitVec 32) 5760 (BitVec.instOfNat)) +
          i).setWidth 64).toNat < scr1.length := by
        rw [m8_k6c_off_add 5760 (by decide) i (by omega), hsc1_l]; omega
      have hbd_5248 : (((@OfNat.ofNat (BitVec 32) 5248 (BitVec.instOfNat)) +
          i).setWidth 64).toNat < scr1.length := by
        rw [m8_k6c_off_add 5248 (by decide) i (by omega), hsc1_l]; omega
      have hbd_4736 : (((@OfNat.ofNat (BitVec 32) 4736 (BitVec.instOfNat)) +
          i).setWidth 64).toNat < scr1.length := by
        rw [m8_k6c_off_add 4736 (by decide) i (by omega), hsc1_l]; omega
      have hbd_4992 : (((@OfNat.ofNat (BitVec 32) 4992 (BitVec.instOfNat)) +
          i).setWidth 64).toNat < scr1.length := by
        rw [m8_k6c_off_add 4992 (by decide) i (by omega), hsc1_l]; omega
      c0_hsteps_nogrp
      let scr1a :=
        (((scr1.set (4224 + i.toNat) 0#32).set
          (4480 + i.toNat) 0xFFFFFFFF#32).set
          (5760 + i.toNat) 0#32).set (5248 + i.toNat) (i + 1#32)
      have hsc1a_l : scr1a.length = c.scratch_cap := by simp [scr1a, hsc1_l]
      have h1a_pre : ∀ k < 4192, scr1a[k]? = s0.scratch.scratch_buf[k]? := fun k hk => by
        dsimp only [scr1a]
        repeat rw [List.getElem?_set_ne (by omega)]
        exact hpre1 k hk
      have h1a_meta : ∀ k, 11648 ≤ k → k < 14720 → scr1a[k]? = scr_e[k]? :=
        fun k hk1 hk2 => by
          dsimp only [scr1a]
          repeat rw [List.getElem?_set_ne (by omega)]
          exact hmeta1 k hk1 hk2
      have h1a_1 : scr1a[4193]? = some nc_s := by
        dsimp only [scr1a]; repeat rw [List.getElem?_set_ne (by omega)]
        exact hs1_1
      have h1a_2 : scr1a[4194]? = some nc_s := by
        dsimp only [scr1a]; repeat rw [List.getElem?_set_ne (by omega)]
        exact hs1_2
      have h1a_14 : scr1a[4206]? = some alen_s := by
        dsimp only [scr1a]; repeat rw [List.getElem?_set_ne (by omega)]
        exact hs1_14
      have h1a_15 : scr1a[4207]? = some (BitVec.ofNat 32 (c.scratch_cap - 15744)) := by
        dsimp only [scr1a]; repeat rw [List.getElem?_set_ne (by omega)]
        exact hs1_15
      refine wp_join_state_pure (ts := [i32]) (α := BitVec 32)
        (fun x => (x, ())) (fun _ => True) ?_ ?_
      · intro Jp pv _
        c0_hsteps_nogrp
        let scr1b := scr1a.set (4736 + i.toNat) pv
        have hsc1b_l : scr1b.length = c.scratch_cap := by simp [scr1b, hsc1a_l]
        refine wp_join_state_pure (ts := [i32]) (α := BitVec 32)
          (fun x => (x, ())) (fun _ => True) ?_ ?_
        · intro Jn nx _
          c0_hsteps!
          rw [m8_k6c_off_add 4224 (by decide) i (by omega),
            m8_k6c_off_add 4480 (by decide) i (by omega),
            m8_k6c_off_add 5760 (by decide) i (by omega),
            m8_k6c_off_add 5248 (by decide) i (by omega),
            m8_k6c_off_add 4736 (by decide) i (by omega),
            m8_k6c_off_add 4992 (by decide) i (by omega)] at hm
          let scr1c := scr1b.set (4992 + i.toNat) nx
          refine hL1 (nv_s.toNat - (i + 1#32).toNat) (i + 1#32, ()) _ (by omega)
            ⟨scr1c, by simp [scr1c, hsc1b_l], by omega, rfl,
              fun k hk => by
                dsimp only [scr1c, scr1b]
                rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
                exact h1a_pre k hk,
              by dsimp only [scr1c, scr1b]
                 rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]; exact h1a_1,
              by dsimp only [scr1c, scr1b]
                 rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]; exact h1a_2,
              by dsimp only [scr1c, scr1b]
                 rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
                 exact h1a_14,
              by dsimp only [scr1c, scr1b]
                 rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
                 exact h1a_15,
              fun k hk1 hk2 => by
                dsimp only [scr1c, scr1b]
                rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
                exact h1a_meta k hk1 hk2,
              m8_k6c_fullMem_subst hm⟩
        · intro _ hJn
          c0_hsplit
          · c0_hsteps!; exact hJn 0xFFFFFFFF#32 trivial
          · c0_hsteps!; exact hJn (i + 1#32) trivial
      · intro _ hJp
        c0_hsplit
        · c0_hsteps!; exact hJp 0xFFFFFFFF#32 trivial
        · c0_hsteps!; exact hJp (i - 1#32) trivial
    · have hi_eq : i.toNat = nv_s.toNat := by omega
      c0_hsteps_nogrp
      refine wp_loop_group (ts := [i32])
        (fun rem2 (i, ()) m2 => ∃ scr2 : List (BitVec 32),
          let s2 : FullState := { s_clr with scratch := { s_clr.scratch with scratch_buf := scr2 } }
          scr2.length = c.scratch_cap ∧ i.toNat ≤ 2 * nv_s.toNat ∧
          rem2 = 2 * nv_s.toNat - i.toNat ∧
          (∀ k < 4192, scr2[k]? = s0.scratch.scratch_buf[k]?) ∧
          scr2[4193]? = some nc_s ∧ scr2[4194]? = some nc_s ∧
          scr2[4206]? = some alen_s ∧
          scr2[4207]? = some (BitVec.ofNat 32 (c.scratch_cap - 15744)) ∧
          (∀ k, 11648 ≤ k → k < 14720 → scr2[k]? = scr_e[k]?) ∧
          (FullMem c s2 ⋆ R) m2) ?_ ?_
      · rintro L2 rem2 ⟨i, ⟨⟩⟩ m2 hL2
          ⟨scr2, hsc2_l, hi_le, rfl, hpre2, hs2_1, hs2_2, hs2_14, hs2_15, hmeta2, hm2⟩
        c0_hsplit
        · have hi_lt : i.toNat < 2 * nv_s.toNat := by
            rw [show (nv_s <<< OfNat.ofNat 1 : BitVec 32) = (nv_s <<< (1 : Nat)) from rfl,
              m8_bv32_shl1_toNat (by omega)] at hc; exact hc
          have hi1 : (i + 1#32).toNat = i.toNat + 1 := m8_k6c_add1_toNat (by omega)
          have hbd_6528 : (((@OfNat.ofNat (BitVec 32) 6528 (BitVec.instOfNat)) +
              i).setWidth 64).toNat < scr2.length := by
            rw [m8_k6c_off_add 6528 (by decide) i (by omega), hsc2_l]; omega
          have hbd_7040 : (((@OfNat.ofNat (BitVec 32) 7040 (BitVec.instOfNat)) +
              i).setWidth 64).toNat < scr2.length := by
            rw [m8_k6c_off_add 7040 (by decide) i (by omega), hsc2_l]; omega
          c0_hsteps!
          rw [m8_k6c_off_add 6528 (by decide) i (by omega),
            m8_k6c_off_add 7040 (by decide) i (by omega)] at hm
          let scr2' :=
            (scr2.set (6528 + i.toNat) 0#32).set (7040 + i.toNat) 0xFFFFFFFF#32
          refine hL2 (2 * nv_s.toNat - (i + 1#32).toNat) (i + 1#32, ()) _ (by omega)
            ⟨scr2', by simp [scr2', hsc2_l], by omega, rfl,
              fun k hk => by
                dsimp only [scr2']
                rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
                exact hpre2 k hk,
              by dsimp only [scr2']
                 rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]; exact hs2_1,
              by dsimp only [scr2']
                 rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]; exact hs2_2,
              by dsimp only [scr2']
                 rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
                 exact hs2_14,
              by dsimp only [scr2']
                 rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
                 exact hs2_15,
              fun k hk1 hk2 => by
                dsimp only [scr2']
                rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
                exact hmeta2 k hk1 hk2,
              m8_k6c_fullMem_subst hm⟩
        · have hscr2_ok : M8K6BufOk scr2 := by
            refine m8_k6c_bufOk_of_init ?_ ?_ ?_ ?_ fun cid hcid => ?_
            · rw [hs2_15, Option.getD_some, hacap_n_eq, hsc2_l]; omega
            · rw [hsc2_l]; omega
            · rw [hs2_1, Option.getD_some]; exact hnc512
            · rw [hs2_14, hs2_15, Option.getD_some, Option.getD_some, hacap_n_eq]
              exact hal_le
            · rw [hs2_1, Option.getD_some] at hcid
              rw [hs2_15, Option.getD_some, hacap_n_eq,
                hmeta2 (11648 + cid) (by omega) (by omega),
                hmeta2 (12672 + cid) (by omega) (by omega)]
              have hco := hcls_e cid hcid
              exact ⟨Nat.le_trans hco.1 hal_le, hco.2⟩
          c0_hsteps_nogrp
          exact hw_wp scr2 m2 hsc2_l hpre2 hscr2_ok hs2_1 hs2_2 hm2
      · intro L2 hL2; c0_hsteps!
        exact hL2 (2 * nv_s.toNat) (0#32, ()) _
          ⟨scr1, hsc1_l, Nat.zero_le _, rfl, hpre1, hs1_1, hs1_2, hs1_14, hs1_15, hmeta1, hm1⟩
  · intro L1 hL1; c0_hsteps!
    exact hL1 nv_s.toNat (0#32, ()) _
      ⟨scr_h, hscrh_l, Nat.zero_le _, rfl, hscrh_pre, hscrh_1, hscrh_2, hscrh_14, hscrh_15,
       hscrh_meta, hhm_h⟩

end LeanQbe.T.Examples.Kissat.FullM8CoreParity
