/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM8CoreParity
public import LeanQbe.T.Examples.Kissat.FullM7BveGatesProof0
public import LeanQbe.T.Examples.Kissat.FullM6BveFwdProof6
public import LeanQbe.T.Examples.Kissat.FullBveVarLemmas1
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullDenseWatchLemmas1
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat M8 Core Parity (`FullM8CoreParity`) Rank #8 Proofs — Part 0 (`Bve0`)

UNSAT-only `Func.wp` specifications and shared helpers (`XPost := False`, strictly `std3`):
1. Pure BitVec, scratch, `FullDenseInvW`, and `M8K6BufOk` helpers.
2. Specifications (`m8Bve*`, `m8K6*`) with `_noExit`, `_intro`, `_elim`.
3. `full_bve_var_key_m7_m8_wp` (certifying `m8BveVarKeySpec`, `M8` `2000` cap).
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

/-! ## 1. Pure BitVec, Scratch, `FullDenseInvW`, & `M8K6BufOk` Helpers -/

theorem m8_bv32_shl1_toNat {x : BitVec 32} (hx : 2 * x.toNat < 2 ^ 32) :
    (x <<< (1 : Nat)).toNat = 2 * x.toNat := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]; omega

theorem m8_bv32_shl1_or1_toNat {x : BitVec 32} (hx : 2 * x.toNat + 1 < 2 ^ 32) :
    ((x <<< (1 : Nat)) ||| 1#32).toNat = 2 * x.toNat + 1 := by
  have h1 : (x <<< (1 : Nat)).toNat = 2 * x.toNat := m8_bv32_shl1_toNat (by omega)
  rw [BitVec.toNat_or, h1, show (1#32 : BitVec 32).toNat = 1 from rfl]
  apply Nat.eq_of_testBit_eq; intro i
  cases i with
  | zero =>
    rw [Nat.testBit_or, Nat.testBit_zero, Nat.testBit_zero, Nat.testBit_zero, Nat.mul_mod_right]
    simp [show (2 * x.toNat + 1) % 2 = 1 by omega]
  | succ j =>
    rw [Nat.testBit_or, Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ]
    simp [Nat.mul_add_div (by omega : 0 < 2)]

theorem m8_bv32_lshr1_toNat (x : BitVec 32) :
    (x >>> (1 : Nat)).toNat = x.toNat / 2 := by
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem m8_bv32_add1_toNat {x : BitVec 32} {lim : Nat} (hx : x.toNat < lim) (hl : lim < 2 ^ 32) :
    (x + 1#32).toNat = x.toNat + 1 := by
  rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]

theorem m8_bv32_sub1_toNat {x : BitVec 32} (hx : 0 < x.toNat) :
    (x - 1#32).toNat = x.toNat - 1 := by
  rw [BitVec.toNat_sub, show (1#32 : BitVec 32).toNat = 1 from rfl]
  have := x.isLt; omega

theorem m8_bv32_xor1_lt {n : Nat} (l : BitVec 32) (hl : l.toNat < 2 * n) :
    (l ^^^ 1#32).toNat = l.toNat ^^^ 1 ∧ (l ^^^ 1#32).toNat < 2 * n := by
  have h1 : (l ^^^ 1#32).toNat = l.toNat ^^^ 1 := by
    rw [BitVec.toNat_xor, show (1#32 : BitVec 32).toNat = 1 from rfl]
  have := fullInv_var_xor1 l.toNat
  exact ⟨h1, by omega⟩

theorem m8_pl_nl_eq (v : BitVec 32) (hv : v.toNat < 2 * 2 ^ 28) :
    (v <<< (1 : Nat)).toNat = 2 * v.toNat ∧
    ((v <<< (1 : Nat)) ||| 1#32).toNat = 2 * v.toNat + 1 :=
  ⟨m8_bv32_shl1_toNat (by omega), m8_bv32_shl1_or1_toNat (by omega)⟩

theorem m8_mask_idx_lo (base idx : BitVec 32)
    (hb : base = 4002#32 ∨ base = 4066#32) (hi : idx.toNat < 2001) :
    (base + (idx >>> (5 : Nat))).toNat = base.toNat + idx.toNat / 32 ∧
    (base + (idx >>> (5 : Nat))).toNat < 4130 := by
  have hsh : (idx >>> (5 : Nat)).toNat = idx.toNat / 32 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hlt : base.toNat + idx.toNat / 32 < 4130 := by
    rcases hb with rfl | rfl <;> simp only [BitVec.toNat_ofNat] <;> omega
  rw [BitVec.toNat_add, hsh, Nat.mod_eq_of_lt (by omega)]
  exact ⟨rfl, hlt⟩

theorem m8_u32_and7fff_or8000 (j : BitVec 32) (hj : j.toNat < 2001) :
    ((j ||| 0x80000000#32) &&& 0x7FFFFFFF#32).toNat = j.toNat := by
  apply Nat.eq_of_testBit_eq; intro k
  rw [BitVec.toNat_and, Nat.testBit_and, BitVec.toNat_or, Nat.testBit_or]
  rw [show (0x80000000#32 : BitVec 32).toNat = 2 ^ 31 from rfl,
    show (0x7FFFFFFF#32 : BitVec 32).toNat = 2 ^ 31 - 1 from rfl]
  by_cases hk : k < 31
  · have h8 : Nat.testBit (2 ^ 31) k = false := Nat.testBit_two_pow_of_ne (by omega)
    have h7 : Nat.testBit (2 ^ 31 - 1) k = true := by
      rw [Nat.testBit_two_pow_sub_one]; exact decide_eq_true hk
    simp [h8, h7]
  · have h7 : Nat.testBit (2 ^ 31 - 1) k = false := by
      rw [Nat.testBit_two_pow_sub_one]; exact decide_eq_false hk
    have hj_tb : Nat.testBit j.toNat k = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hj
        (Nat.le_trans (by decide : 2001 ≤ 2 ^ 31) (Nat.pow_le_pow_right (by decide) (by omega))))
    simp [h7, hj_tb]

theorem m8_fullDenseInvW_lm_scr {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s)
    {lm' : List (BitVec 8)} (hlm_len : lm'.length = 2 * c.max_vars)
    (hlm_clr : ∀ l < 2 * c.max_vars, lm'[l]?.getD 0#8 = 0#8)
    {scr' : List (BitVec 32)} (hscr_len : scr'.length = c.scratch_cap) :
    FullDenseInvW c F0 F_cur
      { s with
        core := { s.core with lit_mark := lm' }
        scratch := { s.scratch with scratch_buf := scr' } } :=
  ⟨⟨{ h.1.core_ok with lit_mark_len := hlm_len },
    { h.1.scratch_ok with scratch_buf_len := hscr_len }⟩,
   { h.2.1 with
     arena := { h.2.1.arena with len_ok := h.2.1.arena.len_ok }
     watches := h.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) },
   ⟨h.2.2.1.1, hlm_clr⟩, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

theorem m8_fullDenseInvW_scr {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s)
    {scr' : List (BitVec 32)} (hscr_len : scr'.length = c.scratch_cap) :
    FullDenseInvW c F0 F_cur { s with scratch := { s.scratch with scratch_buf := scr' } } :=
  m8_fullDenseInvW_lm_scr h h.1.core_ok.lit_mark_len h.2.2.1.2 hscr_len

theorem m8_fullDenseInvW_scr_fuel {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s)
    {scr' : List (BitVec 32)} (hscr_len : scr'.length = c.scratch_cap) (fuel' : BitVec 64) :
    FullDenseInvW c F0 F_cur
      { s with
        core := { s.core with fuel := fuel' }
        scratch := { s.scratch with scratch_buf := scr' } } :=
  ⟨⟨{ h.1.core_ok with arena_len_le := h.1.core_ok.arena_len_le },
    { h.1.scratch_ok with scratch_buf_len := hscr_len }⟩,
   { h.2.1 with
     arena := { h.2.1.arena with len_ok := h.2.1.arena.len_ok }
     watches := h.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) },
   h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

theorem m8_bveEntry_congr_core {F_cur : List (List Nat)} {s s' : FullState}
    {lit : Nat} {w : BitVec 32} (h : FullBveEntryOkW F_cur s lit w)
    (hcv : s'.core.cur_vars = s.core.cur_vars) (har : s'.core.arena = s.core.arena)
    (hal : s'.core.arena_len = s.core.arena_len) :
    FullBveEntryOkW F_cur s' lit w := by
  unfold FullBveEntryOkW at h ⊢
  by_cases hb : (w &&& 0x80000000#32) ≠ 0#32
  · rw [ite_eq_left hb] at h ⊢; exact ⟨by rw [hcv]; exact h.1, h.2⟩
  · rw [ite_eq_right hb] at h ⊢
    have hrefs : fullArenaClauseRefs s' = fullArenaClauseRefs s := by
      unfold fullArenaClauseRefs fullArenaClauseRefsCore; rw [har, hal]
    have hgb : fullArenaClauseGarb s' w.toNat = fullArenaClauseGarb s w.toNat := by
      unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore; rw [har]
    rw [hrefs, hgb]; exact h

theorem m8_lm_set_at {c : FullCfg} {lm : List (BitVec 8)} {P : Nat → Prop} {l : Nat}
    {v : BitVec 8} (_hlm : lm.length = 2 * c.max_vars) (hl : l < 2 * c.max_vars)
    (hprev : ∀ x < 2 * c.max_vars, lm[x]?.getD 0#8 ≠ 0#8 → P x) (hp : P l) :
    ∀ x < 2 * c.max_vars, (lm.set l v)[x]?.getD 0#8 ≠ 0#8 → P x := by
  intro x hx hnz
  by_cases hxl : x = l
  · subst hxl; exact hp
  · rw [List.getElem?_set_ne (Ne.symm hxl)] at hnz; exact hprev x hx hnz

theorem m8_lm_clear_step {lm : List (BitVec 8)} {l : Nat} {P : Nat → Prop}
    (hlm : l < lm.length)
    (hprev : ∀ x < lm.length, lm[x]?.getD 0#8 ≠ 0#8 → x = l ∨ P x) :
    ∀ x < lm.length, (lm.set l 0#8)[x]?.getD 0#8 ≠ 0#8 → P x := by
  intro x hx hnz
  by_cases hxl : x = l
  · subst hxl; simp [List.getElem?_set_self hlm] at hnz
  · rw [List.getElem?_set_ne (Ne.symm hxl)] at hnz
    exact (hprev x hx hnz).resolve_left hxl

theorem m8_lm_clear2_step {c : FullCfg} {lm : List (BitVec 8)} {x0 x1 : Nat}
    {P : Nat → Prop} (hlm : lm.length = 2 * c.max_vars)
    (hx0 : x0 < 2 * c.max_vars) (hx1 : x1 < 2 * c.max_vars)
    (hprev : ∀ x < 2 * c.max_vars, lm[x]?.getD 0#8 ≠ 0#8 → x = x0 ∨ x = x1 ∨ P x) :
    ∀ x < 2 * c.max_vars, ((lm.set x0 0#8).set x1 0#8)[x]?.getD 0#8 ≠ 0#8 → P x := by
  intro x hx hnz
  by_cases h1 : x = x1
  · subst h1
    rw [List.getElem?_set_self (by rw [List.length_set, hlm]; exact hx1)] at hnz
    exact absurd rfl hnz
  · rw [List.getElem?_set_ne (Ne.symm h1)] at hnz
    by_cases h0 : x = x0
    · subst h0
      rw [List.getElem?_set_self (by rw [hlm]; exact hx0)] at hnz
      exact absurd rfl hnz
    · rw [List.getElem?_set_ne (Ne.symm h0)] at hnz
      exact ((hprev x hx hnz).resolve_left h0).resolve_left h1

theorem m8_bv32_bit_disj (x mask target : BitVec 32) (hm : (mask &&& target) = 0#32) :
    ((x ||| mask) &&& target) = (x &&& target) ∧
    ((x &&& ~~~mask) &&& target) = (x &&& target) := by
  have h1 : ((x ||| mask) &&& target) = (x &&& target) := by
    ext i hi
    have hmi := congrArg (·[i]) hm
    simp only [BitVec.getElem_and, BitVec.getElem_zero] at hmi
    simp only [BitVec.getElem_and, BitVec.getElem_or]
    rw [Bool.and_or_distrib_right, hmi, Bool.or_false]
  have h2 : ((x &&& ~~~mask) &&& target) = (x &&& target) := by
    ext i hi
    have hmi := congrArg (·[i]) hm
    simp only [BitVec.getElem_and, BitVec.getElem_zero] at hmi
    simp only [BitVec.getElem_and, BitVec.getElem_not]
    cases ht : target[i]
    · simp
    · simp only [ht, Bool.and_true] at hmi ⊢
      simp [hmi]
  exact ⟨h1, h2⟩

theorem m8_km_core_clear_pres (x : BitVec 32) :
    ((x &&& ~~~0x80000000#32) &&& 0xFFFF#32) = (x &&& 0xFFFF#32) ∧
    ((x &&& ~~~0x80000000#32) &&& 0x40000000#32) = (x &&& 0x40000000#32) :=
  ⟨(m8_bv32_bit_disj x 0x80000000#32 0xFFFF#32 (by decide)).2,
   (m8_bv32_bit_disj x 0x80000000#32 0x40000000#32 (by decide)).2⟩

theorem m8_km_core_or_pres (x : BitVec 32) :
    ((x ||| 0x80000000#32) &&& 0xFFFF#32) = (x &&& 0xFFFF#32) ∧
    ((x ||| 0x80000000#32) &&& 0x40000000#32) = (x &&& 0x40000000#32) :=
  ⟨(m8_bv32_bit_disj x 0x80000000#32 0xFFFF#32 (by decide)).1,
   (m8_bv32_bit_disj x 0x80000000#32 0x40000000#32 (by decide)).1⟩

theorem m8_and_ffff_le (cm : BitVec 32) : (cm &&& 0xFFFF#32).toNat ≤ 65535 := by
  rw [BitVec.toNat_and, show (0xFFFF#32 : BitVec 32).toNat = 2 ^ 16 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]
  omega

/-- Structural & arena bounds invariant for the M8 K6 solver embedded inside `scr[4192..)`. -/
def M8K6BufOk (scr : List (BitVec 32)) : Prop :=
  let nc := scr[4193]?.getD 0#32
  let alen := scr[4206]?.getD 0#32
  let acap := scr[4207]?.getD 0#32
  15744 + acap.toNat ≤ scr.length ∧ scr.length < 2 ^ 30 ∧
  nc.toNat ≤ 1024 ∧ alen.toNat ≤ acap.toNat ∧
  ∀ cid < nc.toNat,
    let off := (scr[11648 + cid]?.getD 0#32).toNat
    let cm := scr[12672 + cid]?.getD 0#32
    let sz := (cm &&& 0xFFFF#32).toNat
    let aux := (scr[13696 + cid]?.getD 0#32).toNat
    off + sz ≤ acap.toNat ∧ ((cm &&& 0x40000000#32) ≠ 0#32 → off + sz + aux ≤ acap.toNat)

theorem M8K6BufOk.mk_of {scr : List (BitVec 32)}
    (hlen_ge : 15744 + (scr[4207]?.getD 0#32).toNat ≤ scr.length)
    (hlen_lt : scr.length < 2 ^ 30)
    (hnc : (scr[4193]?.getD 0#32).toNat ≤ 1024)
    (halen : (scr[4206]?.getD 0#32).toNat ≤ (scr[4207]?.getD 0#32).toNat)
    (hcl : ∀ cid < (scr[4193]?.getD 0#32).toNat,
      let off := (scr[11648 + cid]?.getD 0#32).toNat
      let cm := scr[12672 + cid]?.getD 0#32
      let sz := (cm &&& 0xFFFF#32).toNat
      let aux := (scr[13696 + cid]?.getD 0#32).toNat
      off + sz ≤ (scr[4207]?.getD 0#32).toNat ∧
        ((cm &&& 0x40000000#32) ≠ 0#32 → off + sz + aux ≤ (scr[4207]?.getD 0#32).toNat)) :
    M8K6BufOk scr :=
  ⟨hlen_ge, hlen_lt, hnc, halen, hcl⟩

theorem M8K6BufOk.length_ge {scr : List (BitVec 32)} (h : M8K6BufOk scr) :
    15744 + (scr[4207]?.getD 0#32).toNat ≤ scr.length := h.1

theorem M8K6BufOk.length_lt {scr : List (BitVec 32)} (h : M8K6BufOk scr) :
    scr.length < 2 ^ 30 := h.2.1

theorem M8K6BufOk.nc_le {scr : List (BitVec 32)} (h : M8K6BufOk scr) :
    (scr[4193]?.getD 0#32).toNat ≤ 1024 := h.2.2.1

theorem M8K6BufOk.alen_le {scr : List (BitVec 32)} (h : M8K6BufOk scr) :
    (scr[4206]?.getD 0#32).toNat ≤ (scr[4207]?.getD 0#32).toNat := h.2.2.2.1

theorem M8K6BufOk.clause_ok {scr : List (BitVec 32)} (h : M8K6BufOk scr) {cid : Nat}
    (hcid : cid < (scr[4193]?.getD 0#32).toNat) :
    let off := (scr[11648 + cid]?.getD 0#32).toNat
    let cm := scr[12672 + cid]?.getD 0#32
    let sz := (cm &&& 0xFFFF#32).toNat
    let aux := (scr[13696 + cid]?.getD 0#32).toNat
    off + sz ≤ (scr[4207]?.getD 0#32).toNat ∧
      ((cm &&& 0x40000000#32) ≠ 0#32 → off + sz + aux ≤ (scr[4207]?.getD 0#32).toNat) :=
  h.2.2.2.2 cid hcid

theorem M8K6BufOk.base_ge {scr : List (BitVec 32)} (h : M8K6BufOk scr) :
    15744 ≤ scr.length := by have := h.length_ge; omega

theorem m8K6BufOk_of_frame {scr scr' : List (BitVec 32)} (h : M8K6BufOk scr)
    (hlen : scr'.length = scr.length)
    (hkeep : ∀ idx < scr.length,
      (idx = 4193 ∨ idx = 4206 ∨ idx = 4207 ∨ (11648 ≤ idx ∧ idx < 14720)) →
      scr'[idx]? = scr[idx]?) :
    M8K6BufOk scr' := by
  have hb := h.base_ge
  have hk1 : scr'[4193]? = scr[4193]? := hkeep 4193 (by omega) (Or.inl rfl)
  have hk14 : scr'[4206]? = scr[4206]? := hkeep 4206 (by omega) (Or.inr (Or.inl rfl))
  have hk15 : scr'[4207]? = scr[4207]? := hkeep 4207 (by omega) (Or.inr (Or.inr (Or.inl rfl)))
  refine ⟨by rw [hk15, hlen]; exact h.length_ge, by rw [hlen]; exact h.length_lt,
    by rw [hk1]; exact h.nc_le, by rw [hk14, hk15]; exact h.alen_le, fun cid hcid => ?_⟩
  rw [hk1] at hcid
  have hnc := h.nc_le
  have ho : scr'[11648 + cid]? = scr[11648 + cid]? :=
    hkeep (11648 + cid) (by omega) (Or.inr (Or.inr (Or.inr (by omega))))
  have hm : scr'[12672 + cid]? = scr[12672 + cid]? :=
    hkeep (12672 + cid) (by omega) (Or.inr (Or.inr (Or.inr (by omega))))
  have ha : scr'[13696 + cid]? = scr[13696 + cid]? :=
    hkeep (13696 + cid) (by omega) (Or.inr (Or.inr (Or.inr (by omega))))
  rw [ho, hm, ha, hk15]
  exact h.clause_ok hcid

theorem m8K6BufOk_set_core_meta {scr : List (BitVec 32)} (h : M8K6BufOk scr)
    {cid : Nat} (hcid : cid < 1024) {v : BitVec 32}
    (hsz : (v &&& 0xFFFF#32) = ((scr[12672 + cid]?.getD 0#32) &&& 0xFFFF#32))
    (hlrn : (v &&& 0x40000000#32) = ((scr[12672 + cid]?.getD 0#32) &&& 0x40000000#32)) :
    M8K6BufOk (scr.set (12672 + cid) v) := by
  have hb := h.base_ge
  have hk1 : (scr.set (12672 + cid) v)[4193]? = scr[4193]? := List.getElem?_set_ne (by omega)
  have hk14 : (scr.set (12672 + cid) v)[4206]? = scr[4206]? := List.getElem?_set_ne (by omega)
  have hk15 : (scr.set (12672 + cid) v)[4207]? = scr[4207]? := List.getElem?_set_ne (by omega)
  refine ⟨by rw [hk15, List.length_set]; exact h.length_ge,
    by rw [List.length_set]; exact h.length_lt,
    by rw [hk1]; exact h.nc_le, by rw [hk14, hk15]; exact h.alen_le, fun j hj => ?_⟩
  rw [hk1] at hj
  have hnc := h.nc_le
  have ho : (scr.set (12672 + cid) v)[11648 + j]? = scr[11648 + j]? :=
    List.getElem?_set_ne (by omega)
  have ha : (scr.set (12672 + cid) v)[13696 + j]? = scr[13696 + j]? :=
    List.getElem?_set_ne (by omega)
  rw [ho, ha, hk15]
  by_cases heq : j = cid
  · subst heq
    dsimp only
    rw [List.getElem?_set_self (by omega), Option.getD_some, hsz, hlrn]
    exact h.clause_ok hj
  · rw [List.getElem?_set_ne (by omega)]
    exact h.clause_ok hj

theorem m8K6BufOk_set_flags {scr : List (BitVec 32)} (h : M8K6BufOk scr)
    {i : Nat} (hi : i < 256) (v : BitVec 32) :
    M8K6BufOk (scr.set (5760 + i) v) :=
  m8K6BufOk_of_frame h List.length_set fun idx _ hor => by
    rcases hor with rfl | rfl | rfl | ⟨_, _⟩ <;> exact List.getElem?_set_ne (by omega)

theorem m8_k6BufOk_watch_frame {scr scr' : List (BitVec 32)} (h : M8K6BufOk scr)
    (hlen : scr'.length = scr.length)
    (hkeep : ∀ idx < scr.length, (idx < 7040 ∨ 11648 ≤ idx) → scr'[idx]? = scr[idx]?) :
    M8K6BufOk scr' :=
  m8K6BufOk_of_frame h hlen fun idx hi hor => by
    rcases hor with rfl | rfl | rfl | ⟨_, _⟩
    · exact hkeep 4193 (by omega) (Or.inl (by decide))
    · exact hkeep 4206 (by omega) (Or.inl (by decide))
    · exact hkeep 4207 (by omega) (Or.inl (by decide))
    · exact hkeep idx hi (Or.inr (by omega))

theorem m8_k6BufOk_core_frame {scr scr' : List (BitVec 32)} (h : M8K6BufOk scr)
    (hlen : scr'.length = scr.length)
    (hkeep : ∀ idx < scr.length,
      (idx < 5760 ∨ (6016 ≤ idx ∧ idx < 12672) ∨ 13696 ≤ idx) → scr'[idx]? = scr[idx]?)
    (hm : ∀ cid < (scr[4193]?.getD 0#32).toNat,
      let m0 := scr[12672 + cid]?.getD 0#32
      let m1 := scr'[12672 + cid]?.getD 0#32
      (m1 &&& 0xFFFF#32) = (m0 &&& 0xFFFF#32) ∧
      (m1 &&& 0x40000000#32) = (m0 &&& 0x40000000#32)) :
    M8K6BufOk scr' := by
  have hb := h.base_ge
  have hk1 : scr'[4193]? = scr[4193]? := hkeep 4193 (by omega) (Or.inl (by decide))
  have hk14 : scr'[4206]? = scr[4206]? := hkeep 4206 (by omega) (Or.inl (by decide))
  have hk15 : scr'[4207]? = scr[4207]? := hkeep 4207 (by omega) (Or.inl (by decide))
  refine M8K6BufOk.mk_of (by rw [hk15, hlen]; exact h.length_ge)
    (by rw [hlen]; exact h.length_lt)
    (by rw [hk1]; exact h.nc_le) (by rw [hk14, hk15]; exact h.alen_le) fun cid hcid => ?_
  rw [hk1] at hcid
  have hnc := h.nc_le
  have ho : scr'[11648 + cid]? = scr[11648 + cid]? :=
    hkeep (11648 + cid) (by omega) (Or.inr (Or.inl (by omega)))
  have ha : scr'[13696 + cid]? = scr[13696 + cid]? :=
    hkeep (13696 + cid) (by omega) (Or.inr (Or.inr (by omega)))
  have hmc := hm cid hcid
  dsimp only at hmc ⊢
  rw [ho, ha, hk15, hmc.1, hmc.2]
  exact h.clause_ok hcid

/-! ## 2. Specifications (`m8Bve*`, `m8K6*`) & `_noExit` / `_intro` / `_elim` -/

/-- Contract for `full_bve_find_equiv_m8`. -/
def m8BveFindEquivSpec : Spec [i64, i32, i32] [.bool] := fun (h, np, nn, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ 16384 ≤ c.scratch_cap ∧
    np.toNat ≤ 2001 ∧ nn.toNat ≤ 2001 ∧
    (∀ i < np.toNat, let w := s.scratch.scratch_buf[i]?.getD 0#32;
      (w &&& 0x80000000#32) ≠ 0#32 → (w &&& 0x7FFFFFFF#32).toNat < 2 * s.core.cur_vars) ∧
    (∀ j < nn.toNat, let w := s.scratch.scratch_buf[2001 + j]?.getD 0#32;
      (w &&& 0x80000000#32) ≠ 0#32 → (w &&& 0x7FFFFFFF#32).toNat < 2 * s.core.cur_vars) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) lm' scr' m',
      let s' : FullState :=
        { s with core := { s.core with lit_mark := lm' }
                 scratch := { s.scratch with scratch_buf := scr' } }
      FullDenseInvW c F0 F_cur s' → scr'.length = c.scratch_cap →
      (∀ i < c.scratch_cap, (i < 4002 ∨ 4132 ≤ i) →
        scr'[i]? = s.scratch.scratch_buf[i]?) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

theorem m8BveFindEquivSpec_noExit :
    ∀ xs m Q X, m8BveFindEquivSpec xs m Q X →
      m8BveFindEquivSpec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

theorem m8BveFindEquivSpec_intro {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {R : Mem 64 → Prop} {h : BitVec 64} {np nn : BitVec 32}
    {m : Mem 64} {Q : Post [.bool]} {X : XPost}
    (hh : h = c.hdr) (hdw : FullDenseInvW c F0 F_cur s) (hsc : 16384 ≤ c.scratch_cap)
    (hnp : np.toNat ≤ 2001) (hnn : nn.toNat ≤ 2001)
    (hp : ∀ i < np.toNat, let w := s.scratch.scratch_buf[i]?.getD 0#32;
      (w &&& 0x80000000#32) ≠ 0#32 → (w &&& 0x7FFFFFFF#32).toNat < 2 * s.core.cur_vars)
    (hn : ∀ j < nn.toNat, let w := s.scratch.scratch_buf[2001 + j]?.getD 0#32;
      (w &&& 0x80000000#32) ≠ 0#32 → (w &&& 0x7FFFFFFF#32).toNat < 2 * s.core.cur_vars)
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ (ok : Bool) lm' scr' m',
      let s' : FullState :=
        { s with core := { s.core with lit_mark := lm' }
                 scratch := { s.scratch with scratch_buf := scr' } }
      FullDenseInvW c F0 F_cur s' → scr'.length = c.scratch_cap →
      (∀ i < c.scratch_cap, (i < 4002 ∨ 4132 ≤ i) →
        scr'[i]? = s.scratch.scratch_buf[i]?) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    m8BveFindEquivSpec (h, np, nn, ()) m Q X :=
  ⟨c, F0, F_cur, s, R, hh, hdw, hsc, hnp, hnn, hp, hn, hm, hQ⟩

theorem m8BveFindEquivSpec_elim {a m Q X} (h : m8BveFindEquivSpec a m Q X) :
    let (hp, np, nn, _) := a
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      hp = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ 16384 ≤ c.scratch_cap ∧
      np.toNat ≤ 2001 ∧ nn.toNat ≤ 2001 ∧
      (∀ i < np.toNat, let w := s.scratch.scratch_buf[i]?.getD 0#32;
        (w &&& 0x80000000#32) ≠ 0#32 → (w &&& 0x7FFFFFFF#32).toNat < 2 * s.core.cur_vars) ∧
      (∀ j < nn.toNat, let w := s.scratch.scratch_buf[2001 + j]?.getD 0#32;
        (w &&& 0x80000000#32) ≠ 0#32 → (w &&& 0x7FFFFFFF#32).toNat < 2 * s.core.cur_vars) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ok : Bool) lm' scr' m',
        let s' : FullState :=
          { s with core := { s.core with lit_mark := lm' }
                   scratch := { s.scratch with scratch_buf := scr' } }
        FullDenseInvW c F0 F_cur s' → scr'.length = c.scratch_cap →
        (∀ i < c.scratch_cap, (i < 4002 ∨ 4132 ≤ i) →
          scr'[i]? = s.scratch.scratch_buf[i]?) →
        (FullMem c s' ⋆ R) m' → Q (ok, ()) m' := by
  rcases a with ⟨hp, np, nn, ⟨⟩⟩; exact h

/-- Contract for `full_bve_find_and_m8`. -/
def m8BveFindAndSpec : Spec [i64, i32, i32, i32] [.bool] :=
  fun (h, lit, lit_n, opp_n, ()) m Q _ =>
    let lit_off : Nat := if (lit &&& 1#32) ≠ 0#32 then 2001 else 0
    let opp_off : Nat := if (lit &&& 1#32) ≠ 0#32 then 0 else 2001
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ 16384 ≤ c.scratch_cap ∧
      lit_n.toNat ≤ 2001 ∧ opp_n.toNat ≤ 2001 ∧
      (∀ i < lit_n.toNat, FullBveEntryOkW F_cur s lit.toNat
        (s.scratch.scratch_buf[lit_off + i]?.getD 0#32)) ∧
      (∀ j < opp_n.toNat, FullBveEntryOkW F_cur s ((lit ^^^ 1#32).toNat)
        (s.scratch.scratch_buf[opp_off + j]?.getD 0#32)) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ok : Bool) lm' scr' m',
        let s' : FullState :=
          { s with core := { s.core with lit_mark := lm' }
                   scratch := { s.scratch with scratch_buf := scr' } }
        FullDenseInvW c F0 F_cur s' → scr'.length = c.scratch_cap →
        (∀ i < c.scratch_cap, (i < 4002 ∨ 4132 ≤ i) →
          scr'[i]? = s.scratch.scratch_buf[i]?) →
        (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

theorem m8BveFindAndSpec_noExit :
    ∀ xs m Q X, m8BveFindAndSpec xs m Q X → m8BveFindAndSpec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

theorem m8BveFindAndSpec_intro {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {R : Mem 64 → Prop} {h : BitVec 64} {lit lit_n opp_n : BitVec 32}
    {m : Mem 64} {Q : Post [.bool]} {X : XPost}
    (hh : h = c.hdr) (hdw : FullDenseInvW c F0 F_cur s) (hsc : 16384 ≤ c.scratch_cap)
    (hln : lit_n.toNat ≤ 2001) (hon : opp_n.toNat ≤ 2001)
    (hl : ∀ i < lit_n.toNat, FullBveEntryOkW F_cur s lit.toNat
      (s.scratch.scratch_buf[(if (lit &&& 1#32) ≠ 0#32 then 2001 else 0) + i]?.getD 0#32))
    (ho : ∀ j < opp_n.toNat, FullBveEntryOkW F_cur s ((lit ^^^ 1#32).toNat)
      (s.scratch.scratch_buf[(if (lit &&& 1#32) ≠ 0#32 then 0 else 2001) + j]?.getD 0#32))
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ (ok : Bool) lm' scr' m',
      let s' : FullState :=
        { s with core := { s.core with lit_mark := lm' }
                 scratch := { s.scratch with scratch_buf := scr' } }
      FullDenseInvW c F0 F_cur s' → scr'.length = c.scratch_cap →
      (∀ i < c.scratch_cap, (i < 4002 ∨ 4132 ≤ i) →
        scr'[i]? = s.scratch.scratch_buf[i]?) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    m8BveFindAndSpec (h, lit, lit_n, opp_n, ()) m Q X :=
  ⟨c, F0, F_cur, s, R, hh, hdw, hsc, hln, hon, hl, ho, hm, hQ⟩

theorem m8BveFindAndSpec_elim {a m Q X} (h : m8BveFindAndSpec a m Q X) :
    let (hp, lit, lit_n, opp_n, _) := a
    let lit_off : Nat := if (lit &&& 1#32) ≠ 0#32 then 2001 else 0
    let opp_off : Nat := if (lit &&& 1#32) ≠ 0#32 then 0 else 2001
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      hp = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ 16384 ≤ c.scratch_cap ∧
      lit_n.toNat ≤ 2001 ∧ opp_n.toNat ≤ 2001 ∧
      (∀ i < lit_n.toNat, FullBveEntryOkW F_cur s lit.toNat
        (s.scratch.scratch_buf[lit_off + i]?.getD 0#32)) ∧
      (∀ j < opp_n.toNat, FullBveEntryOkW F_cur s ((lit ^^^ 1#32).toNat)
        (s.scratch.scratch_buf[opp_off + j]?.getD 0#32)) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ok : Bool) lm' scr' m',
        let s' : FullState :=
          { s with core := { s.core with lit_mark := lm' }
                   scratch := { s.scratch with scratch_buf := scr' } }
        FullDenseInvW c F0 F_cur s' → scr'.length = c.scratch_cap →
        (∀ i < c.scratch_cap, (i < 4002 ∨ 4132 ≤ i) →
          scr'[i]? = s.scratch.scratch_buf[i]?) →
        (FullMem c s' ⋆ R) m' → Q (ok, ()) m' := by
  rcases a with ⟨hp, lit, lit_n, opp_n, ⟨⟩⟩; exact h

/-- Contract for `full_bve_match_tern_m8`. -/
def m8BveMatchTernSpec : Spec [i64, i32, i32, i32, i32, i32] [i32] :=
  fun (h, opp_lit, _x, _y, opp_off, opp_n, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ 16384 ≤ c.scratch_cap ∧
      opp_off.toNat + opp_n.toNat ≤ 4002 ∧ opp_n.toNat ≤ 2001 ∧
      (∀ j < opp_n.toNat, FullBveEntryOkW F_cur s opp_lit.toNat
        (s.scratch.scratch_buf[opp_off.toNat + j]?.getD 0#32)) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (r : BitVec 32) scr' m',
        let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
        scr'.length = c.scratch_cap →
        (∀ i < c.scratch_cap, (i < 4132 ∨ 4133 ≤ i) →
          scr'[i]? = s.scratch.scratch_buf[i]?) →
        (r = 0xFFFFFFFF#32 ∨ (r &&& 0x7FFFFFFF#32).toNat < opp_n.toNat) →
        (FullMem c s' ⋆ R) m' → Q (r, ()) m'

theorem m8BveMatchTernSpec_noExit :
    ∀ xs m Q X, m8BveMatchTernSpec xs m Q X →
      m8BveMatchTernSpec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

theorem m8BveMatchTernSpec_intro {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {R : Mem 64 → Prop} {h : BitVec 64} {opp_lit x y opp_off opp_n : BitVec 32}
    {m : Mem 64} {Q : Post [i32]} {X : XPost}
    (hh : h = c.hdr) (hdw : FullDenseInvW c F0 F_cur s) (hsc : 16384 ≤ c.scratch_cap)
    (hoff : opp_off.toNat + opp_n.toNat ≤ 4002) (hon : opp_n.toNat ≤ 2001)
    (hn : ∀ j < opp_n.toNat, FullBveEntryOkW F_cur s opp_lit.toNat
      (s.scratch.scratch_buf[opp_off.toNat + j]?.getD 0#32))
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ (r : BitVec 32) scr' m',
      let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
      scr'.length = c.scratch_cap →
      (∀ i < c.scratch_cap, (i < 4132 ∨ 4133 ≤ i) →
        scr'[i]? = s.scratch.scratch_buf[i]?) →
      (r = 0xFFFFFFFF#32 ∨ (r &&& 0x7FFFFFFF#32).toNat < opp_n.toNat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m') :
    m8BveMatchTernSpec (h, opp_lit, x, y, opp_off, opp_n, ()) m Q X :=
  ⟨c, F0, F_cur, s, R, hh, hdw, hsc, hoff, hon, hn, hm, hQ⟩

theorem m8BveMatchTernSpec_elim {a m Q X} (h : m8BveMatchTernSpec a m Q X) :
    let (hp, opp_lit, _x, _y, opp_off, opp_n, _) := a
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      hp = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ 16384 ≤ c.scratch_cap ∧
      opp_off.toNat + opp_n.toNat ≤ 4002 ∧ opp_n.toNat ≤ 2001 ∧
      (∀ j < opp_n.toNat, FullBveEntryOkW F_cur s opp_lit.toNat
        (s.scratch.scratch_buf[opp_off.toNat + j]?.getD 0#32)) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (r : BitVec 32) scr' m',
        let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
        scr'.length = c.scratch_cap →
        (∀ i < c.scratch_cap, (i < 4132 ∨ 4133 ≤ i) →
          scr'[i]? = s.scratch.scratch_buf[i]?) →
        (r = 0xFFFFFFFF#32 ∨ (r &&& 0x7FFFFFFF#32).toNat < opp_n.toNat) →
        (FullMem c s' ⋆ R) m' → Q (r, ()) m' := by
  rcases a with ⟨hp, opp_lit, _x, _y, opp_off, opp_n, ⟨⟩⟩; exact h

/-- Contract for `full_bve_find_ite_side_m8`. -/
def m8BveFindIteSideSpec : Spec [i64, i32, i32, i32, .bool] [.bool] :=
  fun (h, v, np, nn, _neg, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ 16384 ≤ c.scratch_cap ∧
      v.toNat < s.core.cur_vars ∧ np.toNat ≤ 2001 ∧ nn.toNat ≤ 2001 ∧
      (∀ i < np.toNat, FullBveEntryOkW F_cur s (2 * v.toNat)
        (s.scratch.scratch_buf[i]?.getD 0#32)) ∧
      (∀ j < nn.toNat, FullBveEntryOkW F_cur s (2 * v.toNat + 1)
        (s.scratch.scratch_buf[2001 + j]?.getD 0#32)) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ok : Bool) scr' m',
        let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
        scr'.length = c.scratch_cap →
        (∀ i < c.scratch_cap, (i < 4002 ∨ 4138 ≤ i) →
          scr'[i]? = s.scratch.scratch_buf[i]?) →
        (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

theorem m8BveFindIteSideSpec_noExit :
    ∀ xs m Q X, m8BveFindIteSideSpec xs m Q X →
      m8BveFindIteSideSpec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

theorem m8BveFindIteSideSpec_intro {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {R : Mem 64 → Prop} {h : BitVec 64} {v np nn : BitVec 32} {neg : Bool}
    {m : Mem 64} {Q : Post [.bool]} {X : XPost}
    (hh : h = c.hdr) (hdw : FullDenseInvW c F0 F_cur s) (hsc : 16384 ≤ c.scratch_cap)
    (hv : v.toNat < s.core.cur_vars) (hnp : np.toNat ≤ 2001) (hnn : nn.toNat ≤ 2001)
    (hp : ∀ i < np.toNat, FullBveEntryOkW F_cur s (2 * v.toNat)
      (s.scratch.scratch_buf[i]?.getD 0#32))
    (hn : ∀ j < nn.toNat, FullBveEntryOkW F_cur s (2 * v.toNat + 1)
      (s.scratch.scratch_buf[2001 + j]?.getD 0#32))
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ (ok : Bool) scr' m',
      let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
      scr'.length = c.scratch_cap →
      (∀ i < c.scratch_cap, (i < 4002 ∨ 4138 ≤ i) →
        scr'[i]? = s.scratch.scratch_buf[i]?) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    m8BveFindIteSideSpec (h, v, np, nn, neg, ()) m Q X :=
  ⟨c, F0, F_cur, s, R, hh, hdw, hsc, hv, hnp, hnn, hp, hn, hm, hQ⟩

theorem m8BveFindIteSideSpec_elim {a m Q X} (h : m8BveFindIteSideSpec a m Q X) :
    let (hp, v, np, nn, _neg, _) := a
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      hp = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ 16384 ≤ c.scratch_cap ∧
      v.toNat < s.core.cur_vars ∧ np.toNat ≤ 2001 ∧ nn.toNat ≤ 2001 ∧
      (∀ i < np.toNat, FullBveEntryOkW F_cur s (2 * v.toNat)
        (s.scratch.scratch_buf[i]?.getD 0#32)) ∧
      (∀ j < nn.toNat, FullBveEntryOkW F_cur s (2 * v.toNat + 1)
        (s.scratch.scratch_buf[2001 + j]?.getD 0#32)) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ok : Bool) scr' m',
        let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
        scr'.length = c.scratch_cap →
        (∀ i < c.scratch_cap, (i < 4002 ∨ 4138 ≤ i) →
          scr'[i]? = s.scratch.scratch_buf[i]?) →
        (FullMem c s' ⋆ R) m' → Q (ok, ()) m' := by
  rcases a with ⟨hp, v, np, nn, _neg, ⟨⟩⟩; exact h

/-- Contract for `full_bve_find_ite_m8`. -/
def m8BveFindIteSpec : Spec [i64, i32, i32, i32] [.bool] := fun (h, v, np, nn, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ 16384 ≤ c.scratch_cap ∧
    v.toNat < s.core.cur_vars ∧ np.toNat ≤ 2001 ∧ nn.toNat ≤ 2001 ∧
    (∀ i < np.toNat, FullBveEntryOkW F_cur s (2 * v.toNat)
      (s.scratch.scratch_buf[i]?.getD 0#32)) ∧
    (∀ j < nn.toNat, FullBveEntryOkW F_cur s (2 * v.toNat + 1)
      (s.scratch.scratch_buf[2001 + j]?.getD 0#32)) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) scr' m',
      let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
      scr'.length = c.scratch_cap →
      (∀ i < c.scratch_cap, (i < 4002 ∨ 4138 ≤ i) →
        scr'[i]? = s.scratch.scratch_buf[i]?) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

theorem m8BveFindIteSpec_noExit :
    ∀ xs m Q X, m8BveFindIteSpec xs m Q X → m8BveFindIteSpec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

theorem m8BveFindIteSpec_intro {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {R : Mem 64 → Prop} {h : BitVec 64} {v np nn : BitVec 32}
    {m : Mem 64} {Q : Post [.bool]} {X : XPost}
    (hh : h = c.hdr) (hdw : FullDenseInvW c F0 F_cur s) (hsc : 16384 ≤ c.scratch_cap)
    (hv : v.toNat < s.core.cur_vars) (hnp : np.toNat ≤ 2001) (hnn : nn.toNat ≤ 2001)
    (hp : ∀ i < np.toNat, FullBveEntryOkW F_cur s (2 * v.toNat)
      (s.scratch.scratch_buf[i]?.getD 0#32))
    (hn : ∀ j < nn.toNat, FullBveEntryOkW F_cur s (2 * v.toNat + 1)
      (s.scratch.scratch_buf[2001 + j]?.getD 0#32))
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ (ok : Bool) scr' m',
      let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
      scr'.length = c.scratch_cap →
      (∀ i < c.scratch_cap, (i < 4002 ∨ 4138 ≤ i) →
        scr'[i]? = s.scratch.scratch_buf[i]?) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    m8BveFindIteSpec (h, v, np, nn, ()) m Q X :=
  ⟨c, F0, F_cur, s, R, hh, hdw, hsc, hv, hnp, hnn, hp, hn, hm, hQ⟩

theorem m8BveFindIteSpec_elim {a m Q X} (h : m8BveFindIteSpec a m Q X) :
    let (hp, v, np, nn, _) := a
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      hp = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ 16384 ≤ c.scratch_cap ∧
      v.toNat < s.core.cur_vars ∧ np.toNat ≤ 2001 ∧ nn.toNat ≤ 2001 ∧
      (∀ i < np.toNat, FullBveEntryOkW F_cur s (2 * v.toNat)
        (s.scratch.scratch_buf[i]?.getD 0#32)) ∧
      (∀ j < nn.toNat, FullBveEntryOkW F_cur s (2 * v.toNat + 1)
        (s.scratch.scratch_buf[2001 + j]?.getD 0#32)) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ok : Bool) scr' m',
        let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
        scr'.length = c.scratch_cap →
        (∀ i < c.scratch_cap, (i < 4002 ∨ 4138 ≤ i) →
          scr'[i]? = s.scratch.scratch_buf[i]?) →
        (FullMem c s' ⋆ R) m' → Q (ok, ()) m' := by
  rcases a with ⟨hp, v, np, nn, ⟨⟩⟩; exact h

/-- Contract for `full_bve_find_xor_m8`. -/
def m8BveFindXorSpec : Spec [i64, i32, i32, i32] [.bool] := fun (h, v, np, nn, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ 16384 ≤ c.scratch_cap ∧
    v.toNat < s.core.cur_vars ∧ np.toNat ≤ 2001 ∧ nn.toNat ≤ 2001 ∧
    (∀ i < np.toNat, FullBveEntryOkW F_cur s (2 * v.toNat)
      (s.scratch.scratch_buf[i]?.getD 0#32)) ∧
    (∀ j < nn.toNat, FullBveEntryOkW F_cur s (2 * v.toNat + 1)
      (s.scratch.scratch_buf[2001 + j]?.getD 0#32)) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) lm' scr' m',
      let s' : FullState :=
        { s with core := { s.core with lit_mark := lm' }
                 scratch := { s.scratch with scratch_buf := scr' } }
      FullDenseInvW c F0 F_cur s' → scr'.length = c.scratch_cap →
      (∀ i < c.scratch_cap, (i < 4002 ∨ 4170 ≤ i) →
        scr'[i]? = s.scratch.scratch_buf[i]?) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

theorem m8BveFindXorSpec_noExit :
    ∀ xs m Q X, m8BveFindXorSpec xs m Q X → m8BveFindXorSpec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

theorem m8BveFindXorSpec_intro {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {R : Mem 64 → Prop} {h : BitVec 64} {v np nn : BitVec 32}
    {m : Mem 64} {Q : Post [.bool]} {X : XPost}
    (hh : h = c.hdr) (hdw : FullDenseInvW c F0 F_cur s) (hsc : 16384 ≤ c.scratch_cap)
    (hv : v.toNat < s.core.cur_vars) (hnp : np.toNat ≤ 2001) (hnn : nn.toNat ≤ 2001)
    (hp : ∀ i < np.toNat, FullBveEntryOkW F_cur s (2 * v.toNat)
      (s.scratch.scratch_buf[i]?.getD 0#32))
    (hn : ∀ j < nn.toNat, FullBveEntryOkW F_cur s (2 * v.toNat + 1)
      (s.scratch.scratch_buf[2001 + j]?.getD 0#32))
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ (ok : Bool) lm' scr' m',
      let s' : FullState :=
        { s with core := { s.core with lit_mark := lm' }
                 scratch := { s.scratch with scratch_buf := scr' } }
      FullDenseInvW c F0 F_cur s' → scr'.length = c.scratch_cap →
      (∀ i < c.scratch_cap, (i < 4002 ∨ 4170 ≤ i) →
        scr'[i]? = s.scratch.scratch_buf[i]?) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    m8BveFindXorSpec (h, v, np, nn, ()) m Q X :=
  ⟨c, F0, F_cur, s, R, hh, hdw, hsc, hv, hnp, hnn, hp, hn, hm, hQ⟩

theorem m8BveFindXorSpec_elim {a m Q X} (h : m8BveFindXorSpec a m Q X) :
    let (hp, v, np, nn, _) := a
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      hp = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ 16384 ≤ c.scratch_cap ∧
      v.toNat < s.core.cur_vars ∧ np.toNat ≤ 2001 ∧ nn.toNat ≤ 2001 ∧
      (∀ i < np.toNat, FullBveEntryOkW F_cur s (2 * v.toNat)
        (s.scratch.scratch_buf[i]?.getD 0#32)) ∧
      (∀ j < nn.toNat, FullBveEntryOkW F_cur s (2 * v.toNat + 1)
        (s.scratch.scratch_buf[2001 + j]?.getD 0#32)) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ok : Bool) lm' scr' m',
        let s' : FullState :=
          { s with core := { s.core with lit_mark := lm' }
                   scratch := { s.scratch with scratch_buf := scr' } }
        FullDenseInvW c F0 F_cur s' → scr'.length = c.scratch_cap →
        (∀ i < c.scratch_cap, (i < 4002 ∨ 4170 ≤ i) →
          scr'[i]? = s.scratch.scratch_buf[i]?) →
        (FullMem c s' ⋆ R) m' → Q (ok, ()) m' := by
  rcases a with ⟨hp, v, np, nn, ⟨⟩⟩; exact h

/-- Contract for `full_k6_watch_m8`. -/
def m8K6WatchSpec : Spec [i64, i32, i32, i32, i32] [] :=
  fun (h, _cid, _l0, _l1, _sz, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ 16384 ≤ c.scratch_cap ∧ (FullMem c s ⋆ R) m ∧
      ∀ scr' m', scr'.length = c.scratch_cap →
        (∀ idx < c.scratch_cap, (idx < 7040 ∨ 11648 ≤ idx) →
          scr'[idx]? = s.scratch.scratch_buf[idx]?) →
        (FullMem c { s with scratch := { s.scratch with scratch_buf := scr' } } ⋆ R) m' → Q () m'

theorem m8K6WatchSpec_noExit :
    ∀ xs m Q X, m8K6WatchSpec xs m Q X → m8K6WatchSpec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

theorem m8K6WatchSpec_intro {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {h : BitVec 64} {cid l0 l1 sz : BitVec 32} {m : Mem 64} {Q : Post []} {X : XPost}
    (hh : h = c.hdr) (hlen : s.LengthsOk c) (hsc : 16384 ≤ c.scratch_cap)
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ scr' m', scr'.length = c.scratch_cap →
      (∀ idx < c.scratch_cap, (idx < 7040 ∨ 11648 ≤ idx) →
        scr'[idx]? = s.scratch.scratch_buf[idx]?) →
      (FullMem c { s with scratch := { s.scratch with scratch_buf := scr' } } ⋆ R) m' → Q () m') :
    m8K6WatchSpec (h, cid, l0, l1, sz, ()) m Q X :=
  ⟨c, s, R, hh, hlen, hsc, hm, hQ⟩

theorem m8K6WatchSpec_elim {a m Q X} (h : m8K6WatchSpec a m Q X) :
    let (hp, _, _, _, _, _) := a
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      hp = c.hdr ∧ s.LengthsOk c ∧ 16384 ≤ c.scratch_cap ∧ (FullMem c s ⋆ R) m ∧
      ∀ scr' m', scr'.length = c.scratch_cap →
        (∀ idx < c.scratch_cap, (idx < 7040 ∨ 11648 ≤ idx) →
          scr'[idx]? = s.scratch.scratch_buf[idx]?) →
        (FullMem c { s with scratch := { s.scratch with scratch_buf := scr' } } ⋆ R) m' →
        Q () m' := by
  rcases a with ⟨hp, cid, l0, l1, sz, ⟨⟩⟩; exact h

/-- Contract for `full_k6_assign_m8`. -/
def m8K6AssignSpec : Spec [i64, i32, i32] [] :=
  fun (h, _lit, _rsn_cid, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ 16384 ≤ c.scratch_cap ∧ (FullMem c s ⋆ R) m ∧
      ∀ scr' m', scr'.length = c.scratch_cap →
        (∀ idx < c.scratch_cap, idx ≠ 4197 → idx ≠ 4198 →
          (idx < 4224 ∨ 4736 ≤ idx) → (idx < 5504 ∨ 6016 ≤ idx) →
          (idx < 6528 ∨ 7040 ≤ idx) → scr'[idx]? = s.scratch.scratch_buf[idx]?) →
        (FullMem c { s with scratch := { s.scratch with scratch_buf := scr' } } ⋆ R) m' → Q () m'

theorem m8K6AssignSpec_noExit :
    ∀ xs m Q X, m8K6AssignSpec xs m Q X → m8K6AssignSpec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

theorem m8K6AssignSpec_intro {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {h : BitVec 64} {lit rsn_cid : BitVec 32} {m : Mem 64} {Q : Post []} {X : XPost}
    (hh : h = c.hdr) (hlen : s.LengthsOk c) (hsc : 16384 ≤ c.scratch_cap)
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ scr' m', scr'.length = c.scratch_cap →
      (∀ idx < c.scratch_cap, idx ≠ 4197 → idx ≠ 4198 →
        (idx < 4224 ∨ 4736 ≤ idx) → (idx < 5504 ∨ 6016 ≤ idx) →
        (idx < 6528 ∨ 7040 ≤ idx) → scr'[idx]? = s.scratch.scratch_buf[idx]?) →
      (FullMem c { s with scratch := { s.scratch with scratch_buf := scr' } } ⋆ R) m' → Q () m') :
    m8K6AssignSpec (h, lit, rsn_cid, ()) m Q X :=
  ⟨c, s, R, hh, hlen, hsc, hm, hQ⟩

theorem m8K6AssignSpec_elim {a m Q X} (h : m8K6AssignSpec a m Q X) :
    let (hp, _, _, _) := a
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      hp = c.hdr ∧ s.LengthsOk c ∧ 16384 ≤ c.scratch_cap ∧ (FullMem c s ⋆ R) m ∧
      ∀ scr' m', scr'.length = c.scratch_cap →
        (∀ idx < c.scratch_cap, idx ≠ 4197 → idx ≠ 4198 →
          (idx < 4224 ∨ 4736 ≤ idx) → (idx < 5504 ∨ 6016 ≤ idx) →
          (idx < 6528 ∨ 7040 ≤ idx) → scr'[idx]? = s.scratch.scratch_buf[idx]?) →
        (FullMem c { s with scratch := { s.scratch with scratch_buf := scr' } } ⋆ R) m' →
        Q () m' := by
  rcases a with ⟨hp, lit, rsn_cid, ⟨⟩⟩; exact h

/-- Contract for `full_k6_mtf_m8`. -/
def m8K6MtfSpec : Spec [i64, i32] [] :=
  fun (h, _v, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ 16384 ≤ c.scratch_cap ∧ (FullMem c s ⋆ R) m ∧
      ∀ scr' m', scr'.length = c.scratch_cap →
        (∀ idx < c.scratch_cap, (idx < 4200 ∨ (4204 ≤ idx ∧ idx < 4736) ∨ 5504 ≤ idx) →
          scr'[idx]? = s.scratch.scratch_buf[idx]?) →
        (FullMem c { s with scratch := { s.scratch with scratch_buf := scr' } } ⋆ R) m' → Q () m'

theorem m8K6MtfSpec_noExit :
    ∀ xs m Q X, m8K6MtfSpec xs m Q X → m8K6MtfSpec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

theorem m8K6MtfSpec_intro {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {h : BitVec 64} {v : BitVec 32} {m : Mem 64} {Q : Post []} {X : XPost}
    (hh : h = c.hdr) (hlen : s.LengthsOk c) (hsc : 16384 ≤ c.scratch_cap)
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ scr' m', scr'.length = c.scratch_cap →
      (∀ idx < c.scratch_cap, (idx < 4200 ∨ (4204 ≤ idx ∧ idx < 4736) ∨ 5504 ≤ idx) →
        scr'[idx]? = s.scratch.scratch_buf[idx]?) →
      (FullMem c { s with scratch := { s.scratch with scratch_buf := scr' } } ⋆ R) m' → Q () m') :
    m8K6MtfSpec (h, v, ()) m Q X :=
  ⟨c, s, R, hh, hlen, hsc, hm, hQ⟩

theorem m8K6MtfSpec_elim {a m Q X} (h : m8K6MtfSpec a m Q X) :
    let (hp, _, _) := a
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      hp = c.hdr ∧ s.LengthsOk c ∧ 16384 ≤ c.scratch_cap ∧ (FullMem c s ⋆ R) m ∧
      ∀ scr' m', scr'.length = c.scratch_cap →
        (∀ idx < c.scratch_cap, (idx < 4200 ∨ (4204 ≤ idx ∧ idx < 4736) ∨ 5504 ≤ idx) →
          scr'[idx]? = s.scratch.scratch_buf[idx]?) →
        (FullMem c { s with scratch := { s.scratch with scratch_buf := scr' } } ⋆ R) m' →
        Q () m' := by
  rcases a with ⟨hp, v, ⟨⟩⟩; exact h

/-- Contract for `full_k6_backtrack_m8`. -/
def m8K6BacktrackSpec : Spec [i64, i32] [] :=
  fun (h, _target_lvl, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ 16384 ≤ c.scratch_cap ∧ (FullMem c s ⋆ R) m ∧
      ∀ scr' m', scr'.length = c.scratch_cap →
        (∀ idx < c.scratch_cap,
          (idx < 4195 ∨ (4199 ≤ idx ∧ idx < 4224) ∨ (4736 ≤ idx ∧ idx < 6528) ∨ 7040 ≤ idx) →
          scr'[idx]? = s.scratch.scratch_buf[idx]?) →
        (FullMem c { s with scratch := { s.scratch with scratch_buf := scr' } } ⋆ R) m' → Q () m'

theorem m8K6BacktrackSpec_noExit :
    ∀ xs m Q X, m8K6BacktrackSpec xs m Q X →
      m8K6BacktrackSpec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

theorem m8K6BacktrackSpec_intro {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {h : BitVec 64} {target_lvl : BitVec 32} {m : Mem 64} {Q : Post []} {X : XPost}
    (hh : h = c.hdr) (hlen : s.LengthsOk c) (hsc : 16384 ≤ c.scratch_cap)
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ scr' m', scr'.length = c.scratch_cap →
      (∀ idx < c.scratch_cap,
        (idx < 4195 ∨ (4199 ≤ idx ∧ idx < 4224) ∨ (4736 ≤ idx ∧ idx < 6528) ∨ 7040 ≤ idx) →
        scr'[idx]? = s.scratch.scratch_buf[idx]?) →
      (FullMem c { s with scratch := { s.scratch with scratch_buf := scr' } } ⋆ R) m' → Q () m') :
    m8K6BacktrackSpec (h, target_lvl, ()) m Q X :=
  ⟨c, s, R, hh, hlen, hsc, hm, hQ⟩

theorem m8K6BacktrackSpec_elim {a m Q X} (h : m8K6BacktrackSpec a m Q X) :
    let (hp, _, _) := a
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      hp = c.hdr ∧ s.LengthsOk c ∧ 16384 ≤ c.scratch_cap ∧ (FullMem c s ⋆ R) m ∧
      ∀ scr' m', scr'.length = c.scratch_cap →
        (∀ idx < c.scratch_cap,
          (idx < 4195 ∨ (4199 ≤ idx ∧ idx < 4224) ∨ (4736 ≤ idx ∧ idx < 6528) ∨ 7040 ≤ idx) →
          scr'[idx]? = s.scratch.scratch_buf[idx]?) →
        (FullMem c { s with scratch := { s.scratch with scratch_buf := scr' } } ⋆ R) m' →
        Q () m' := by
  rcases a with ⟨hp, target_lvl, ⟨⟩⟩; exact h

/-- Contract for `full_k6_core_m8`. -/
def m8K6CoreSpec : Spec [i64] [] :=
  fun (h, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ 16384 ≤ c.scratch_cap ∧
      M8K6BufOk s.scratch.scratch_buf ∧ (FullMem c s ⋆ R) m ∧
      ∀ scr' m', scr'.length = c.scratch_cap →
        (∀ idx < c.scratch_cap,
          (idx < 5760 ∨ (6016 ≤ idx ∧ idx < 12672) ∨ 13696 ≤ idx) →
          scr'[idx]? = s.scratch.scratch_buf[idx]?) →
        M8K6BufOk scr' →
        (FullMem c { s with scratch := { s.scratch with scratch_buf := scr' } } ⋆ R) m' → Q () m'

theorem m8K6CoreSpec_noExit :
    ∀ xs m Q X, m8K6CoreSpec xs m Q X → m8K6CoreSpec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

theorem m8K6CoreSpec_intro {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {h : BitVec 64} {m : Mem 64} {Q : Post []} {X : XPost}
    (hh : h = c.hdr) (hlen : s.LengthsOk c) (hsc : 16384 ≤ c.scratch_cap)
    (hok : M8K6BufOk s.scratch.scratch_buf) (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ scr' m', scr'.length = c.scratch_cap →
      (∀ idx < c.scratch_cap,
        (idx < 5760 ∨ (6016 ≤ idx ∧ idx < 12672) ∨ 13696 ≤ idx) →
        scr'[idx]? = s.scratch.scratch_buf[idx]?) →
      M8K6BufOk scr' →
      (FullMem c { s with scratch := { s.scratch with scratch_buf := scr' } } ⋆ R) m' → Q () m') :
    m8K6CoreSpec (h, ()) m Q X :=
  ⟨c, s, R, hh, hlen, hsc, hok, hm, hQ⟩

theorem m8K6CoreSpec_elim {a m Q X} (h : m8K6CoreSpec a m Q X) :
    let (hp, _) := a
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      hp = c.hdr ∧ s.LengthsOk c ∧ 16384 ≤ c.scratch_cap ∧
      M8K6BufOk s.scratch.scratch_buf ∧ (FullMem c s ⋆ R) m ∧
      ∀ scr' m', scr'.length = c.scratch_cap →
        (∀ idx < c.scratch_cap,
          (idx < 5760 ∨ (6016 ≤ idx ∧ idx < 12672) ∨ 13696 ≤ idx) →
          scr'[idx]? = s.scratch.scratch_buf[idx]?) →
        M8K6BufOk scr' →
        (FullMem c { s with scratch := { s.scratch with scratch_buf := scr' } } ⋆ R) m' →
        Q () m' := by
  rcases a with ⟨hp, ⟨⟩⟩; exact h

/-- Contract for `full_k6_prop_m8`. -/
def m8K6PropSpec : Spec [i64] [i32] :=
  fun (h, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ 16384 ≤ c.scratch_cap ∧
      M8K6BufOk s.scratch.scratch_buf ∧ (FullMem c s ⋆ R) m ∧
      ∀ (r : BitVec 32) scr' m',
        let scr := s.scratch.scratch_buf
        M8K6BufOk scr' → scr'.length = c.scratch_cap →
        (∀ i < 4195, scr'[i]? = scr[i]?) →
        (∀ i, 4199 ≤ i → i < 4204 → scr'[i]? = scr[i]?) →
        (∀ i, 4205 ≤ i → i < 4224 → scr'[i]? = scr[i]?) →
        (∀ i, 4736 ≤ i → i < 5504 → scr'[i]? = scr[i]?) →
        (∀ i, 6016 ≤ i → i < 6528 → scr'[i]? = scr[i]?) →
        (∀ i, 11648 ≤ i → i < 15744 → scr'[i]? = scr[i]?) →
        (FullMem c { s with scratch := { s.scratch with scratch_buf := scr' } } ⋆ R) m' →
        Q (r, ()) m'

theorem m8K6PropSpec_noExit :
    ∀ xs m Q X, m8K6PropSpec xs m Q X → m8K6PropSpec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

theorem m8K6PropSpec_intro {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {h : BitVec 64} {m : Mem 64} {Q : Post [i32]} {X : XPost}
    (hh : h = c.hdr) (hlen : s.LengthsOk c) (hsc : 16384 ≤ c.scratch_cap)
    (hok : M8K6BufOk s.scratch.scratch_buf) (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ (r : BitVec 32) scr' m',
      let scr := s.scratch.scratch_buf
      M8K6BufOk scr' → scr'.length = c.scratch_cap →
      (∀ i < 4195, scr'[i]? = scr[i]?) →
      (∀ i, 4199 ≤ i → i < 4204 → scr'[i]? = scr[i]?) →
      (∀ i, 4205 ≤ i → i < 4224 → scr'[i]? = scr[i]?) →
      (∀ i, 4736 ≤ i → i < 5504 → scr'[i]? = scr[i]?) →
      (∀ i, 6016 ≤ i → i < 6528 → scr'[i]? = scr[i]?) →
      (∀ i, 11648 ≤ i → i < 15744 → scr'[i]? = scr[i]?) →
      (FullMem c { s with scratch := { s.scratch with scratch_buf := scr' } } ⋆ R) m' →
      Q (r, ()) m') :
    m8K6PropSpec (h, ()) m Q X :=
  ⟨c, s, R, hh, hlen, hsc, hok, hm, hQ⟩

theorem m8K6PropSpec_elim {a m Q X} (h : m8K6PropSpec a m Q X) :
    let (hp, _) := a
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      hp = c.hdr ∧ s.LengthsOk c ∧ 16384 ≤ c.scratch_cap ∧
      M8K6BufOk s.scratch.scratch_buf ∧ (FullMem c s ⋆ R) m ∧
      ∀ (r : BitVec 32) scr' m',
        let scr := s.scratch.scratch_buf
        M8K6BufOk scr' → scr'.length = c.scratch_cap →
        (∀ i < 4195, scr'[i]? = scr[i]?) →
        (∀ i, 4199 ≤ i → i < 4204 → scr'[i]? = scr[i]?) →
        (∀ i, 4205 ≤ i → i < 4224 → scr'[i]? = scr[i]?) →
        (∀ i, 4736 ≤ i → i < 5504 → scr'[i]? = scr[i]?) →
        (∀ i, 6016 ≤ i → i < 6528 → scr'[i]? = scr[i]?) →
        (∀ i, 11648 ≤ i → i < 15744 → scr'[i]? = scr[i]?) →
        (FullMem c { s with scratch := { s.scratch with scratch_buf := scr' } } ⋆ R) m' →
        Q (r, ()) m' := by
  rcases a with ⟨hp, ⟨⟩⟩; exact h

/-- Contract for `full_k6_ana_cl_m8`. -/
def m8K6AnaClSpec : Spec [i64, i32, i32] [] :=
  fun (h, _cid, _skip_v, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ 16384 ≤ c.scratch_cap ∧
      M8K6BufOk s.scratch.scratch_buf ∧ (FullMem c s ⋆ R) m ∧
      ∀ scr' m', scr'.length = c.scratch_cap →
        (∀ idx < c.scratch_cap,
          idx ≠ 4208 → idx ≠ 4209 → idx ≠ 4210 → idx ≠ 4212 →
          (idx < 5760 ∨ 6528 ≤ idx) → (idx < 15232 ∨ 15744 ≤ idx) →
          scr'[idx]? = s.scratch.scratch_buf[idx]?) →
        (FullMem c { s with scratch := { s.scratch with scratch_buf := scr' } } ⋆ R) m' → Q () m'

theorem m8K6AnaClSpec_noExit :
    ∀ xs m Q X, m8K6AnaClSpec xs m Q X → m8K6AnaClSpec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

theorem m8K6AnaClSpec_intro {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {h : BitVec 64} {cid skip_v : BitVec 32} {m : Mem 64} {Q : Post []} {X : XPost}
    (hh : h = c.hdr) (hlen : s.LengthsOk c) (hsc : 16384 ≤ c.scratch_cap)
    (hok : M8K6BufOk s.scratch.scratch_buf) (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ scr' m', scr'.length = c.scratch_cap →
      (∀ idx < c.scratch_cap,
        idx ≠ 4208 → idx ≠ 4209 → idx ≠ 4210 → idx ≠ 4212 →
        (idx < 5760 ∨ 6528 ≤ idx) → (idx < 15232 ∨ 15744 ≤ idx) →
        scr'[idx]? = s.scratch.scratch_buf[idx]?) →
      (FullMem c { s with scratch := { s.scratch with scratch_buf := scr' } } ⋆ R) m' → Q () m') :
    m8K6AnaClSpec (h, cid, skip_v, ()) m Q X :=
  ⟨c, s, R, hh, hlen, hsc, hok, hm, hQ⟩

theorem m8K6AnaClSpec_elim {a m Q X} (h : m8K6AnaClSpec a m Q X) :
    let (hp, _, _, _) := a
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      hp = c.hdr ∧ s.LengthsOk c ∧ 16384 ≤ c.scratch_cap ∧
      M8K6BufOk s.scratch.scratch_buf ∧ (FullMem c s ⋆ R) m ∧
      ∀ scr' m', scr'.length = c.scratch_cap →
        (∀ idx < c.scratch_cap,
          idx ≠ 4208 → idx ≠ 4209 → idx ≠ 4210 → idx ≠ 4212 →
          (idx < 5760 ∨ 6528 ≤ idx) → (idx < 15232 ∨ 15744 ≤ idx) →
          scr'[idx]? = s.scratch.scratch_buf[idx]?) →
        (FullMem c { s with scratch := { s.scratch with scratch_buf := scr' } } ⋆ R) m' →
        Q () m' := by
  rcases a with ⟨hp, cid, skip_v, ⟨⟩⟩; exact h

/-- Contract for `full_k6_analyze_m8`. -/
def m8K6AnalyzeSpec : Spec [i64, i32] [.bool] :=
  fun (h, _confl_cid, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ 16384 ≤ c.scratch_cap ∧
      M8K6BufOk s.scratch.scratch_buf ∧ (FullMem c s ⋆ R) m ∧
      ∀ (ok : Bool) scr' m',
        let scr := s.scratch.scratch_buf
        M8K6BufOk scr' → scr'.length = c.scratch_cap →
        (∀ i < 4193, scr'[i]? = scr[i]?) →
        scr'[4194]? = scr[4194]? →
        (scr[4193]?.getD 0#32).toNat ≤ (scr'[4193]?.getD 0#32).toNat →
        (∀ cid < (scr[4193]?.getD 0#32).toNat, scr'[13696 + cid]? = scr[13696 + cid]?) →
        scr'[4199]? = scr[4199]? →
        scr'[4205]? = scr[4205]? →
        scr'[4207]? = scr[4207]? →
        scr'[4211]? = scr[4211]? →
        scr'[4213]? = scr[4213]? →
        (∀ i, 14720 ≤ i → i < 15232 → scr'[i]? = scr[i]?) →
        (FullMem c { s with scratch := { s.scratch with scratch_buf := scr' } } ⋆ R) m' →
        Q (ok, ()) m'

theorem m8K6AnalyzeSpec_noExit :
    ∀ xs m Q X, m8K6AnalyzeSpec xs m Q X → m8K6AnalyzeSpec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

theorem m8K6AnalyzeSpec_intro {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {h : BitVec 64} {confl_cid : BitVec 32} {m : Mem 64} {Q : Post [.bool]} {X : XPost}
    (hh : h = c.hdr) (hlen : s.LengthsOk c) (hsc : 16384 ≤ c.scratch_cap)
    (hok : M8K6BufOk s.scratch.scratch_buf) (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ (ok : Bool) scr' m',
      let scr := s.scratch.scratch_buf
      M8K6BufOk scr' → scr'.length = c.scratch_cap →
      (∀ i < 4193, scr'[i]? = scr[i]?) →
      scr'[4194]? = scr[4194]? →
      (scr[4193]?.getD 0#32).toNat ≤ (scr'[4193]?.getD 0#32).toNat →
      (∀ cid < (scr[4193]?.getD 0#32).toNat, scr'[13696 + cid]? = scr[13696 + cid]?) →
      scr'[4199]? = scr[4199]? →
      scr'[4205]? = scr[4205]? →
      scr'[4207]? = scr[4207]? →
      scr'[4211]? = scr[4211]? →
      scr'[4213]? = scr[4213]? →
      (∀ i, 14720 ≤ i → i < 15232 → scr'[i]? = scr[i]?) →
      (FullMem c { s with scratch := { s.scratch with scratch_buf := scr' } } ⋆ R) m' →
      Q (ok, ()) m') :
    m8K6AnalyzeSpec (h, confl_cid, ()) m Q X :=
  ⟨c, s, R, hh, hlen, hsc, hok, hm, hQ⟩

theorem m8K6AnalyzeSpec_elim {a m Q X} (h : m8K6AnalyzeSpec a m Q X) :
    let (hp, _, _) := a
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      hp = c.hdr ∧ s.LengthsOk c ∧ 16384 ≤ c.scratch_cap ∧
      M8K6BufOk s.scratch.scratch_buf ∧ (FullMem c s ⋆ R) m ∧
      ∀ (ok : Bool) scr' m',
        let scr := s.scratch.scratch_buf
        M8K6BufOk scr' → scr'.length = c.scratch_cap →
        (∀ i < 4193, scr'[i]? = scr[i]?) →
        scr'[4194]? = scr[4194]? →
        (scr[4193]?.getD 0#32).toNat ≤ (scr'[4193]?.getD 0#32).toNat →
        (∀ cid < (scr[4193]?.getD 0#32).toNat, scr'[13696 + cid]? = scr[13696 + cid]?) →
        scr'[4199]? = scr[4199]? →
        scr'[4205]? = scr[4205]? →
        scr'[4207]? = scr[4207]? →
        scr'[4211]? = scr[4211]? →
        scr'[4213]? = scr[4213]? →
        (∀ i, 14720 ≤ i → i < 15232 → scr'[i]? = scr[i]?) →
        (FullMem c { s with scratch := { s.scratch with scratch_buf := scr' } } ⋆ R) m' →
        Q (ok, ()) m' := by
  rcases a with ⟨hp, confl_cid, ⟨⟩⟩; exact h

/-- Contract for `full_k6_solve_m8`. -/
def m8K6SolveSpec : Spec [i64, i32] [i64] :=
  fun (h, _tick_lim, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ 16384 ≤ c.scratch_cap ∧
      M8K6BufOk s.scratch.scratch_buf ∧
      (s.scratch.scratch_buf[4194]?.getD 0#32).toNat ≤
        (s.scratch.scratch_buf[4193]?.getD 0#32).toNat ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (r : BitVec 64) scr' fuel' m',
        let scr := s.scratch.scratch_buf
        let s' : FullState :=
          { s with
            core := { s.core with fuel := fuel' }
            scratch := { s.scratch with scratch_buf := scr' } }
        M8K6BufOk scr' → scr'.length = c.scratch_cap →
        (∀ i < 4192, scr'[i]? = scr[i]?) →
        scr'[4194]? = scr[4194]? →
        (scr[4194]?.getD 0#32).toNat ≤ (scr'[4193]?.getD 0#32).toNat →
        (∀ cid < (scr[4194]?.getD 0#32).toNat, scr'[13696 + cid]? = scr[13696 + cid]?) →
        fuel'.toNat ≤ s.core.fuel.toNat →
        (FullMem c s' ⋆ R) m' → Q (r, ()) m'

theorem m8K6SolveSpec_noExit :
    ∀ xs m Q X, m8K6SolveSpec xs m Q X → m8K6SolveSpec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

theorem m8K6SolveSpec_intro {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {h : BitVec 64} {tick_lim : BitVec 32} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hh : h = c.hdr) (hlen : s.LengthsOk c) (hsc : 16384 ≤ c.scratch_cap)
    (hok : M8K6BufOk s.scratch.scratch_buf)
    (honc : (s.scratch.scratch_buf[4194]?.getD 0#32).toNat ≤
      (s.scratch.scratch_buf[4193]?.getD 0#32).toNat)
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ (r : BitVec 64) scr' fuel' m',
      let scr := s.scratch.scratch_buf
      let s' : FullState :=
        { s with
          core := { s.core with fuel := fuel' }
          scratch := { s.scratch with scratch_buf := scr' } }
      M8K6BufOk scr' → scr'.length = c.scratch_cap →
      (∀ i < 4192, scr'[i]? = scr[i]?) →
      scr'[4194]? = scr[4194]? →
      (scr[4194]?.getD 0#32).toNat ≤ (scr'[4193]?.getD 0#32).toNat →
      (∀ cid < (scr[4194]?.getD 0#32).toNat, scr'[13696 + cid]? = scr[13696 + cid]?) →
      fuel'.toNat ≤ s.core.fuel.toNat →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m') :
    m8K6SolveSpec (h, tick_lim, ()) m Q X :=
  ⟨c, s, R, hh, hlen, hsc, hok, honc, hm, hQ⟩

theorem m8K6SolveSpec_elim {a m Q X} (h : m8K6SolveSpec a m Q X) :
    let (hp, _, _) := a
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      hp = c.hdr ∧ s.LengthsOk c ∧ 16384 ≤ c.scratch_cap ∧
      M8K6BufOk s.scratch.scratch_buf ∧
      (s.scratch.scratch_buf[4194]?.getD 0#32).toNat ≤
        (s.scratch.scratch_buf[4193]?.getD 0#32).toNat ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (r : BitVec 64) scr' fuel' m',
        let scr := s.scratch.scratch_buf
        let s' : FullState :=
          { s with
            core := { s.core with fuel := fuel' }
            scratch := { s.scratch with scratch_buf := scr' } }
        M8K6BufOk scr' → scr'.length = c.scratch_cap →
        (∀ i < 4192, scr'[i]? = scr[i]?) →
        scr'[4194]? = scr[4194]? →
        (scr[4194]?.getD 0#32).toNat ≤ (scr'[4193]?.getD 0#32).toNat →
        (∀ cid < (scr[4194]?.getD 0#32).toNat, scr'[13696 + cid]? = scr[13696 + cid]?) →
        fuel'.toNat ≤ s.core.fuel.toNat →
        (FullMem c s' ⋆ R) m' → Q (r, ()) m' := by
  rcases a with ⟨hp, tick_lim, ⟨⟩⟩; exact h

/-- Contract for `full_k6_extract_and_solve_m8`. -/
def m8K6ExtractSolveSpec : Spec [i64, i32, i32, i32, .bool, i32] [.bool] :=
  fun (h, v, np, nn, _second_pass, _tick_lim, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ TmkZero s ∧ 16384 ≤ c.scratch_cap ∧
      v.toNat < s.core.cur_vars ∧ np.toNat ≤ 512 ∧ nn.toNat ≤ 512 ∧
      (∀ i < np.toNat, FullBveEntryOkW F_cur s (2 * v.toNat)
        (s.scratch.scratch_buf[i]?.getD 0#32)) ∧
      (∀ j < nn.toNat, FullBveEntryOkW F_cur s (2 * v.toNat + 1)
        (s.scratch.scratch_buf[2001 + j]?.getD 0#32)) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ok : Bool) s' m',
        FullDenseInvW c F0 F_cur s' → TmkZero s' →
        s'.core.cur_vars = s.core.cur_vars → s'.core.arena = s.core.arena →
        s'.core.arena_len = s.core.arena_len → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
        (∀ i < 4002, s'.scratch.scratch_buf[i]? = s.scratch.scratch_buf[i]?) →
        (∀ i, 4132 ≤ i → i < 4192 → s'.scratch.scratch_buf[i]? = s.scratch.scratch_buf[i]?) →
        (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

theorem m8K6ExtractSolveSpec_noExit :
    ∀ xs m Q X, m8K6ExtractSolveSpec xs m Q X →
      m8K6ExtractSolveSpec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

theorem m8K6ExtractSolveSpec_intro {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {R : Mem 64 → Prop} {h : BitVec 64} {v np nn tick_lim : BitVec 32}
    {second_pass : Bool} {m : Mem 64} {Q : Post [.bool]} {X : XPost}
    (hh : h = c.hdr) (hdw : FullDenseInvW c F0 F_cur s) (htmk : TmkZero s)
    (hsc : 16384 ≤ c.scratch_cap) (hv : v.toNat < s.core.cur_vars)
    (hnp : np.toNat ≤ 512) (hnn : nn.toNat ≤ 512)
    (hp : ∀ i < np.toNat, FullBveEntryOkW F_cur s (2 * v.toNat)
      (s.scratch.scratch_buf[i]?.getD 0#32))
    (hn : ∀ j < nn.toNat, FullBveEntryOkW F_cur s (2 * v.toNat + 1)
      (s.scratch.scratch_buf[2001 + j]?.getD 0#32))
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ (ok : Bool) s' m',
      FullDenseInvW c F0 F_cur s' → TmkZero s' →
      s'.core.cur_vars = s.core.cur_vars → s'.core.arena = s.core.arena →
      s'.core.arena_len = s.core.arena_len → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (∀ i < 4002, s'.scratch.scratch_buf[i]? = s.scratch.scratch_buf[i]?) →
      (∀ i, 4132 ≤ i → i < 4192 → s'.scratch.scratch_buf[i]? = s.scratch.scratch_buf[i]?) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    m8K6ExtractSolveSpec (h, v, np, nn, second_pass, tick_lim, ()) m Q X :=
  ⟨c, F0, F_cur, s, R, hh, hdw, htmk, hsc, hv, hnp, hnn, hp, hn, hm, hQ⟩

theorem m8K6ExtractSolveSpec_elim {a m Q X} (h : m8K6ExtractSolveSpec a m Q X) :
    let (hp, v, np, nn, _, _, _) := a
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      hp = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ TmkZero s ∧ 16384 ≤ c.scratch_cap ∧
      v.toNat < s.core.cur_vars ∧ np.toNat ≤ 512 ∧ nn.toNat ≤ 512 ∧
      (∀ i < np.toNat, FullBveEntryOkW F_cur s (2 * v.toNat)
        (s.scratch.scratch_buf[i]?.getD 0#32)) ∧
      (∀ j < nn.toNat, FullBveEntryOkW F_cur s (2 * v.toNat + 1)
        (s.scratch.scratch_buf[2001 + j]?.getD 0#32)) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ok : Bool) s' m',
        FullDenseInvW c F0 F_cur s' → TmkZero s' →
        s'.core.cur_vars = s.core.cur_vars → s'.core.arena = s.core.arena →
        s'.core.arena_len = s.core.arena_len → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
        (∀ i < 4002, s'.scratch.scratch_buf[i]? = s.scratch.scratch_buf[i]?) →
        (∀ i, 4132 ≤ i → i < 4192 → s'.scratch.scratch_buf[i]? = s.scratch.scratch_buf[i]?) →
        (FullMem c s' ⋆ R) m' → Q (ok, ()) m' := by
  rcases a with ⟨hp, v, np, nn, sp, tl, ⟨⟩⟩; exact h

/-- Contract for `full_bve_gates_m8` and `full_bve_def_k6_m8`. -/
def m8BveGatesSpec : Spec [i64, i32, i32, i32] [] := fun (h, v, np, nn, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ TmkZero s ∧ 16384 ≤ c.scratch_cap ∧
    v.toNat < s.core.cur_vars ∧ np.toNat ≤ 2001 ∧ nn.toNat ≤ 2001 ∧
    (∀ i < np.toNat, FullBveEntryOkW F_cur s (2 * v.toNat)
      (s.scratch.scratch_buf[i]?.getD 0#32)) ∧
    (∀ j < nn.toNat, FullBveEntryOkW F_cur s (2 * v.toNat + 1)
      (s.scratch.scratch_buf[2001 + j]?.getD 0#32)) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ s' m',
      FullDenseInvW c F0 F_cur s' → TmkZero s' →
      s'.core.cur_vars = s.core.cur_vars → s'.core.arena = s.core.arena →
      s'.core.arena_len = s.core.arena_len → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (∀ i < np.toNat, s'.scratch.scratch_buf[i]? = s.scratch.scratch_buf[i]?) →
      (∀ j < nn.toNat, s'.scratch.scratch_buf[2001 + j]? = s.scratch.scratch_buf[2001 + j]?) →
      (FullMem c s' ⋆ R) m' → Q () m'

theorem m8BveGatesSpec_noExit :
    ∀ xs m Q X, m8BveGatesSpec xs m Q X → m8BveGatesSpec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

theorem m8BveGatesSpec_intro {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {R : Mem 64 → Prop} {h : BitVec 64} {v np nn : BitVec 32}
    {m : Mem 64} {Q : Post []} {X : XPost}
    (hh : h = c.hdr) (hdw : FullDenseInvW c F0 F_cur s) (htmk : TmkZero s)
    (hsc : 16384 ≤ c.scratch_cap) (hv : v.toNat < s.core.cur_vars)
    (hnp : np.toNat ≤ 2001) (hnn : nn.toNat ≤ 2001)
    (hp : ∀ i < np.toNat, FullBveEntryOkW F_cur s (2 * v.toNat)
      (s.scratch.scratch_buf[i]?.getD 0#32))
    (hn : ∀ j < nn.toNat, FullBveEntryOkW F_cur s (2 * v.toNat + 1)
      (s.scratch.scratch_buf[2001 + j]?.getD 0#32))
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ s' m',
      FullDenseInvW c F0 F_cur s' → TmkZero s' →
      s'.core.cur_vars = s.core.cur_vars → s'.core.arena = s.core.arena →
      s'.core.arena_len = s.core.arena_len → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (∀ i < np.toNat, s'.scratch.scratch_buf[i]? = s.scratch.scratch_buf[i]?) →
      (∀ j < nn.toNat, s'.scratch.scratch_buf[2001 + j]? = s.scratch.scratch_buf[2001 + j]?) →
      (FullMem c s' ⋆ R) m' → Q () m') :
    m8BveGatesSpec (h, v, np, nn, ()) m Q X :=
  ⟨c, F0, F_cur, s, R, hh, hdw, htmk, hsc, hv, hnp, hnn, hp, hn, hm, hQ⟩

theorem m8BveGatesSpec_elim {a m Q X} (h : m8BveGatesSpec a m Q X) :
    let (hp, v, np, nn, _) := a
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      hp = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ TmkZero s ∧ 16384 ≤ c.scratch_cap ∧
      v.toNat < s.core.cur_vars ∧ np.toNat ≤ 2001 ∧ nn.toNat ≤ 2001 ∧
      (∀ i < np.toNat, FullBveEntryOkW F_cur s (2 * v.toNat)
        (s.scratch.scratch_buf[i]?.getD 0#32)) ∧
      (∀ j < nn.toNat, FullBveEntryOkW F_cur s (2 * v.toNat + 1)
        (s.scratch.scratch_buf[2001 + j]?.getD 0#32)) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ s' m',
        FullDenseInvW c F0 F_cur s' → TmkZero s' →
        s'.core.cur_vars = s.core.cur_vars → s'.core.arena = s.core.arena →
        s'.core.arena_len = s.core.arena_len → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
        (∀ i < np.toNat, s'.scratch.scratch_buf[i]? = s.scratch.scratch_buf[i]?) →
        (∀ j < nn.toNat, s'.scratch.scratch_buf[2001 + j]? = s.scratch.scratch_buf[2001 + j]?) →
        (FullMem c s' ⋆ R) m' → Q () m' := by
  rcases a with ⟨hp, v, np, nn, ⟨⟩⟩; exact h

/-- Contract for `full_bve_bce_side_m8`. -/
def m8BveBceSideSpec : Spec [i64, i32, i32, i32, i32, i32] [] :=
  fun (h, lit, off, cnt, opp_off, opp_n, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ TmkZero s ∧
      lit.toNat < 2 * s.core.cur_vars ∧
      off.toNat + cnt.toNat ≤ c.scratch_cap ∧ opp_off.toNat + opp_n.toNat ≤ c.scratch_cap ∧
      (∀ i < cnt.toNat, FullBveVarSpecs.FullBveTryBceEntryOk c s
        (s.scratch.scratch_buf[off.toNat + i]?.getD 0#32) ∧
        ((s.scratch.scratch_buf[off.toNat + i]?.getD 0#32 &&& 0x80000000#32) ≠ 0#32 →
          (s.scratch.scratch_buf[off.toNat + i]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat <
            2 * s.core.cur_vars)) ∧
      (∀ j < opp_n.toNat, FullBveVarSpecs.FullBveTryBceOppOk c s
        (s.scratch.scratch_buf[opp_off.toNat + j]?.getD 0#32)) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ s' m',
        FullDenseInvW c F0 F_cur s' → TmkZero s' →
        s'.core.cur_vars = s.core.cur_vars → s'.core.arena_len = s.core.arena_len →
        s'.core.fuel = s.core.fuel → s'.scratch.scratch_buf = s.scratch.scratch_buf →
        fullArenaClauseRefs s' = fullArenaClauseRefs s →
        (∀ r ∈ fullArenaClauseRefs s,
          fullArenaClauseSize s' r = fullArenaClauseSize s r ∧
          fullArenaClauseLits s' r = fullArenaClauseLits s r) →
        (FullMem c s' ⋆ R) m' → Q () m'

theorem m8BveBceSideSpec_noExit :
    ∀ xs m Q X, m8BveBceSideSpec xs m Q X → m8BveBceSideSpec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

theorem m8BveBceSideSpec_intro {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {R : Mem 64 → Prop} {h : BitVec 64} {lit off cnt opp_off opp_n : BitVec 32}
    {m : Mem 64} {Q : Post []} {X : XPost}
    (hh : h = c.hdr) (hdw : FullDenseInvW c F0 F_cur s) (htmk : TmkZero s)
    (hlit : lit.toNat < 2 * s.core.cur_vars)
    (hoff : off.toNat + cnt.toNat ≤ c.scratch_cap)
    (hopp : opp_off.toNat + opp_n.toNat ≤ c.scratch_cap)
    (hc : ∀ i < cnt.toNat, FullBveVarSpecs.FullBveTryBceEntryOk c s
      (s.scratch.scratch_buf[off.toNat + i]?.getD 0#32) ∧
      ((s.scratch.scratch_buf[off.toNat + i]?.getD 0#32 &&& 0x80000000#32) ≠ 0#32 →
        (s.scratch.scratch_buf[off.toNat + i]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat <
          2 * s.core.cur_vars))
    (ho : ∀ j < opp_n.toNat, FullBveVarSpecs.FullBveTryBceOppOk c s
      (s.scratch.scratch_buf[opp_off.toNat + j]?.getD 0#32))
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ s' m',
      FullDenseInvW c F0 F_cur s' → TmkZero s' →
      s'.core.cur_vars = s.core.cur_vars → s'.core.arena_len = s.core.arena_len →
      s'.core.fuel = s.core.fuel → s'.scratch.scratch_buf = s.scratch.scratch_buf →
      fullArenaClauseRefs s' = fullArenaClauseRefs s →
      (∀ r ∈ fullArenaClauseRefs s,
        fullArenaClauseSize s' r = fullArenaClauseSize s r ∧
        fullArenaClauseLits s' r = fullArenaClauseLits s r) →
      (FullMem c s' ⋆ R) m' → Q () m') :
    m8BveBceSideSpec (h, lit, off, cnt, opp_off, opp_n, ()) m Q X :=
  ⟨c, F0, F_cur, s, R, hh, hdw, htmk, hlit, hoff, hopp, hc, ho, hm, hQ⟩

theorem m8BveBceSideSpec_elim {a m Q X} (h : m8BveBceSideSpec a m Q X) :
    let (hp, lit, off, cnt, opp_off, opp_n, _) := a
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      hp = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ TmkZero s ∧
      lit.toNat < 2 * s.core.cur_vars ∧
      off.toNat + cnt.toNat ≤ c.scratch_cap ∧ opp_off.toNat + opp_n.toNat ≤ c.scratch_cap ∧
      (∀ i < cnt.toNat, FullBveVarSpecs.FullBveTryBceEntryOk c s
        (s.scratch.scratch_buf[off.toNat + i]?.getD 0#32) ∧
        ((s.scratch.scratch_buf[off.toNat + i]?.getD 0#32 &&& 0x80000000#32) ≠ 0#32 →
          (s.scratch.scratch_buf[off.toNat + i]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat <
            2 * s.core.cur_vars)) ∧
      (∀ j < opp_n.toNat, FullBveVarSpecs.FullBveTryBceOppOk c s
        (s.scratch.scratch_buf[opp_off.toNat + j]?.getD 0#32)) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ s' m',
        FullDenseInvW c F0 F_cur s' → TmkZero s' →
        s'.core.cur_vars = s.core.cur_vars → s'.core.arena_len = s.core.arena_len →
        s'.core.fuel = s.core.fuel → s'.scratch.scratch_buf = s.scratch.scratch_buf →
        fullArenaClauseRefs s' = fullArenaClauseRefs s →
        (∀ r ∈ fullArenaClauseRefs s,
          fullArenaClauseSize s' r = fullArenaClauseSize s r ∧
          fullArenaClauseLits s' r = fullArenaClauseLits s r) →
        (FullMem c s' ⋆ R) m' → Q () m' := by
  rcases a with ⟨hp, lit, off, cnt, opp_off, opp_n, ⟨⟩⟩; exact h

/-! ## 3. `full_bve_var_key_m7_m8_wp` (`m8BveVarKeySpec`) -/

/-- Pure read-only BVE priority key contract for `full_bve_var_key_m7` (`M8` `2000` cap). -/
def m8BveVarKeySpec : Spec [i64, i32] [i64] := fun (h, _v, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧ ∀ r : BitVec 64, Q (r, ()) m

theorem m8BveVarKeySpec_noExit :
    ∀ xs m Q X, m8BveVarKeySpec xs m Q X →
      m8BveVarKeySpec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

theorem m8BveVarKeySpec_intro {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {h : BitVec 64} {v : BitVec 32} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hh : h = c.hdr) (hlen : s.LengthsOk c) (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ r : BitVec 64, Q (r, ()) m) :
    m8BveVarKeySpec (h, v, ()) m Q X :=
  ⟨c, s, R, hh, hlen, hm, hQ⟩

theorem m8BveVarKeySpec_elim {a m Q X} (h : m8BveVarKeySpec a m Q X) :
    let (hp, _v, _) := a
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      hp = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧ ∀ r : BitVec 64, Q (r, ()) m := by
  rcases a with ⟨hp, v, ⟨⟩⟩; exact h

/-- Certifies `m8BveVarKeySpec` for M8 `full_bve_var_key_m7` (`M8` `2000` cap). -/
theorem full_bve_var_key_m7_m8_wp (Γ : Env) :
    ∀ a m Q X, m8BveVarKeySpec a m Q X →
      Func.wp Γ FullM8CoreParity.full_bve_var_key_m7_body a m Q X := by
  rintro ⟨h, v, ⟨⟩⟩ m0 Q X hSpec
  obtain ⟨c, s, R, rfl, hlen, hm0, hQ⟩ := m8BveVarKeySpec_elim hSpec
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv_le := hlen.core_ok.cur_vars_le
  unfold Func.wp FullM8CoreParity.full_bve_var_key_m7_body
  c0_hsplit
  · c0_hsteps!; exact hQ 0#64
  · have hv_lt : v.toNat < s.core.cur_vars := by
      rw [Nat.mod_eq_of_lt (by omega)] at hc; omega
    have hwv1 : ((v.setWidth 64 <<< (2 : Nat)) + 1#64).toNat < s.core.wvec.length := by
      rw [hlen.core_ok.wvec_len]; c0_bound
    have hwv3 : ((v.setWidth 64 <<< (2 : Nat)) + 3#64).toNat < s.core.wvec.length := by
      rw [hlen.core_ok.wvec_len]; c0_bound
    have hv_sc : (v.setWidth 64).toNat < s.scratch.score.length := by
      rw [hlen.scratch_ok.score_len, m6_zext32_toNat]; omega
    have hv_qs : (v.setWidth 64).toNat < s.scratch.q_stamp.length := by
      rw [hlen.scratch_ok.q_stamp_len, m6_zext32_toNat]; omega
    c0_hsteps_nogrp
    refine wp_join_state_pure (ts := [i64]) (α := BitVec 64) (fun x => (x, ())) (fun _ => True)
      (fun _ _ _ => by
        c0_hsteps_nogrp
        refine wp_join_state_pure (ts := [i64]) (α := BitVec 64) (fun x => (x, ())) (fun _ => True)
          (fun _ _ _ => by
            c0_hsteps_nogrp
            refine wp_join_state_pure (ts := [i64]) (α := BitVec 64) (fun x => (x, ()))
              (fun _ => True)
              (fun _ _ _ => by c0_hsteps!; exact hQ _)
              (fun Jr hJr => by c0_hsplit <;> (c0_hsteps!; exact hJr _ trivial)))
          (fun Jn hJn => by c0_hsplit <;> (c0_hsteps!; exact hJn _ trivial)))
      (fun Jp hJp => by c0_hsplit <;> (c0_hsteps!; exact hJp _ trivial))


/-- Contract for `full_bve_heap_push_m7` against `m8BveVarKeySpec` (mirrors
`FullM6BveFwd.fullBveHeapPushM6Spec`, which is unexposed). -/
def m8BveHeapPushSpec : Spec [i64, i64, i32] [i64] := fun (h, hlen, _v, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
    ∀ hlen' ws1' ss' m',
      ws1'.length = 2 * c.max_vars → ss'.length = c.max_vars →
      (hlen.toNat ≤ s.core.cur_vars → hlen'.toNat ≤ s.core.cur_vars) →
      (FullMem c { s with scratch := { s.scratch with work_stk1 := ws1', sim_sig := ss' } } ⋆
        R) m' →
      Q (hlen', ()) m'

theorem m8BveHeapPushSpec_noExit :
    ∀ xs m Q X, m8BveHeapPushSpec xs m Q X →
      m8BveHeapPushSpec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

theorem m8BveHeapPushSpec_intro {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {h hlen : BitVec 64} {v : BitVec 32} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hh : h = c.hdr) (hl : s.LengthsOk c) (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ hlen' ws1' ss' m',
      ws1'.length = 2 * c.max_vars → ss'.length = c.max_vars →
      (hlen.toNat ≤ s.core.cur_vars → hlen'.toNat ≤ s.core.cur_vars) →
      (FullMem c { s with scratch := { s.scratch with work_stk1 := ws1', sim_sig := ss' } } ⋆
        R) m' →
      Q (hlen', ()) m') :
    m8BveHeapPushSpec (h, hlen, v, ()) m Q X :=
  ⟨c, s, R, hh, hl, hm, hQ⟩

theorem m8BveHeapPushSpec_elim {a m Q X} (h : m8BveHeapPushSpec a m Q X) :
    let (hp, hlen, _v, _) := a
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      hp = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
      ∀ hlen' ws1' ss' m',
        ws1'.length = 2 * c.max_vars → ss'.length = c.max_vars →
        (hlen.toNat ≤ s.core.cur_vars → hlen'.toNat ≤ s.core.cur_vars) →
        (FullMem c { s with scratch := { s.scratch with work_stk1 := ws1', sim_sig := ss' } } ⋆
          R) m' →
        Q (hlen', ()) m' := by
  rcases a with ⟨hp, hlen, v, ⟨⟩⟩; exact h

/-! ## 4. Shared Scratch & K6 Helpers for BVE Proof Shards -/

theorem m8_scr_imm_lt {c : FullCfg} {scr : List (BitVec 32)} {k : Nat}
    (hlen : scr.length = c.scratch_cap) (hsc : 16384 ≤ c.scratch_cap) (hk : k < 16384) :
    (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat k)).toNat < scr.length := by
  change (BitVec.ofNat 64 k).toNat < scr.length
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hlen]
  omega

theorem m8_k6_get_eq {xs : List (BitVec 32)} {i : Nat} (hi : i < xs.length) :
    xs[i]?.getD 0#32 = xs[i]'hi := by
  rw [List.getElem?_eq_getElem hi, Option.getD_some]

theorem m8_k6_get_congr {α : Type} {xs : List α} {i j : Nat}
    (h : i = j) (hi : i < xs.length) (hj : j < xs.length) : xs[i]'hi = xs[j]'hj := by
  subst h; rfl

theorem m8_k6_set_congr {α : Type} {xs : List α} {i j : Nat} {a b : α}
    (hi : i = j) (ha : a = b) : xs.set i a = xs.set j b := by
  subst hi ha; rfl

theorem m8_k6_elem_of_opt {xs ys : List (BitVec 32)} {i : Nat}
    (h : xs[i]? = ys[i]?) (hx : i < xs.length) (hy : i < ys.length) :
    xs[i]'hx = ys[i]'hy := by
  rw [List.getElem?_eq_getElem hx, List.getElem?_eq_getElem hy] at h
  exact Option.some.inj h

theorem m8_bv64_sub1_toNat {a : BitVec 64} (ha : 0 < a.toNat) :
    (a - 1#64).toNat = a.toNat - 1 := by
  rw [BitVec.toNat_sub, show (1#64 : BitVec 64).toNat = 1 from rfl]
  have := a.isLt; omega

theorem m8_fullDenseInvW_def {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s)
    {tmp' exp' tmk' scr' : List (BitVec 32)}
    (htl : tmp'.length = c.max_vars) (hel : exp'.length = 2 * c.max_vars)
    (html : tmk'.length = 2 * c.max_vars) (hscl : scr'.length = c.scratch_cap) :
    FullDenseInvW c F0 F_cur
      { s with
        core := { s.core with tmp := tmp' }
        scratch := { s.scratch with wsort := exp', tarjan_mark := tmk', scratch_buf := scr' } } :=
  ⟨⟨{ h.1.core_ok with tmp_len_arr := htl },
    { h.1.scratch_ok with wsort_len := hel, tarjan_mark_len := html, scratch_buf_len := hscl }⟩,
   { h.2.1 with
     arena := { h.2.1.arena with len_ok := h.2.1.arena.len_ok }
     watches := h.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) },
   h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

theorem m8_fullDenseInvW_fuel {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) (fl' : BitVec 64) :
    FullDenseInvW c F0 F_cur { s with core := { s.core with fuel := fl' } } :=
  ⟨⟨{ h.1.core_ok with tmp_len_arr := h.1.core_ok.tmp_len_arr }, h.1.scratch_ok⟩,
   { h.2.1 with
     arena := { h.2.1.arena with len_ok := h.2.1.arena.len_ok }
     watches := h.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) },
   h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

end LeanQbe.T.Examples.Kissat.FullM8CoreParity
