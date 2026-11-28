/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Definition.SpecHelpers
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
public import LeanQbe.T.Examples.Kissat.Proof.Spec.MemBridges
public import LeanQbe.T.Logic.C0Step
public import LeanQbe.T.Logic.C0HeadStep
public import LeanQbe.T.Logic.ControlComb
public import LeanQbe.T.Logic.MemLemmas
public import Kraken.Mem
public import Kraken.Separation

/-!
# Shared Invariants, Memory Tactics, and State Framing (`Proof.Definition.Inv`)

Zero legacy imports (`0` `Full*`, `0` `import all`), zero `@[expose]` on theorems/sections:
1. Pure `BitVec` / `List` / `FullBveEntryOkW` arithmetic & bounds helpers.
2. `FullDenseInvW` frame/transition lemmas (`m8_fullDenseInvW_*`, `assignLvl0_preserves_denseInvW`,
   `m6_markGarb_preserves_denseInvW`, `m6_denseInvW_set_inconsistent`, level-0 entailment helpers).
3. Scoped memory tactics and state wrappers shared across M7 and fidelity WP shards:
   - `K6Tactics`, `P6Scr`, `P6Tactics` (M7 K6 & `def_k6_m7`)
   - `m8ScrSt`, `m8ScrFuelSt`, `M8K6bTactics` (Fid K6 `prop` / `analyze` / `solve` / `core`)
   - `FidP6Scr`, `FidP6Work`, `FidK6cTactics`, `certMkState`, `CertMkTactics` (`extract` / `cert`)
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Definition

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Definition.Spec
open Kraken.Bedrock2.Test

open scoped FullArenaTactics FidK6Tactics

public section

/-! ## 1. Pure BitVec, List, & `FullBveEntryOkW` Helpers -/

theorem m6_zext32_toNat (x : BitVec 32) : (x.setWidth 64).toNat = x.toNat :=
  bv_c0_zext32_64 x

theorem m7_p6_xor_two_mul (n : Nat) : (2 * n) ^^^ 1 = 2 * n + 1 := by
  apply Nat.eq_of_testBit_eq; intro k
  cases k with
  | zero => simp [Nat.testBit_zero, Nat.mul_mod_right, show (2 * n + 1) % 2 = 1 by omega]
  | succ j =>
    rw [Nat.testBit_xor, Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ]
    simp [Nat.mul_div_right _ (by omega : 0 < 2), Nat.mul_add_div (by omega : 0 < 2)]

theorem m7_p6_xor_two_mul_add1 (n : Nat) : (2 * n + 1) ^^^ 1 = 2 * n := by
  rw [← m7_p6_xor_two_mul n, Nat.xor_assoc, show (1 ^^^ 1 : Nat) = 0 from rfl, Nat.xor_zero]

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

theorem m7_p6_pl_nl_eq (v : BitVec 32) (hv : v.toNat < 2 * 2 ^ 28) :
    (v <<< (1 : Nat)).toNat = 2 * v.toNat ∧
    ((v <<< (1 : Nat)) ||| 1#32).toNat = 2 * v.toNat + 1 :=
  ⟨m8_bv32_shl1_toNat (by omega), m8_bv32_shl1_or1_toNat (by omega)⟩

theorem m8_pl_nl_eq (v : BitVec 32) (hv : v.toNat < 2 * 2 ^ 28) :
    (v <<< (1 : Nat)).toNat = 2 * v.toNat ∧
    ((v <<< (1 : Nat)) ||| 1#32).toNat = 2 * v.toNat + 1 :=
  m7_p6_pl_nl_eq v hv

theorem m8_bv32_lshr1_toNat (x : BitVec 32) : (x >>> (1 : Nat)).toNat = x.toNat / 2 := by
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem m8_bv32_add1_toNat {x : BitVec 32} {lim : Nat} (hx : x.toNat < lim) (hl : lim < 2 ^ 32) :
    (x + 1#32).toNat = x.toNat + 1 := by
  rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]

theorem m8_bv32_sub1_toNat {x : BitVec 32} (hx : 0 < x.toNat) :
    (x - 1#32).toNat = x.toNat - 1 := by
  rw [BitVec.toNat_sub, show (1#32 : BitVec 32).toNat = 1 from rfl]
  have := x.isLt; omega

theorem m8_bv64_sub1_toNat {a : BitVec 64} (ha : 0 < a.toNat) :
    (a - 1#64).toNat = a.toNat - 1 := by
  rw [BitVec.toNat_sub, show (1#64 : BitVec 64).toNat = 1 from rfl]
  have := a.isLt; omega

theorem m8_bv32_xor1_lt {n : Nat} (l : BitVec 32) (hl : l.toNat < 2 * n) :
    (l ^^^ 1#32).toNat = l.toNat ^^^ 1 ∧ (l ^^^ 1#32).toNat < 2 * n := by
  have h1 : (l ^^^ 1#32).toNat = l.toNat ^^^ 1 := by
    rw [BitVec.toNat_xor, show (1#32 : BitVec 32).toNat = 1 from rfl]
  have := fullInv_var_xor1 l.toNat
  exact ⟨h1, by omega⟩

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
    · simp only [ht, Bool.and_true] at hmi ⊢; simp [hmi]
  exact ⟨h1, h2⟩

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

theorem m7_p6_add2_u64 {a b : BitVec 32} (ha : a.toNat < 2 ^ 32) (hb : b.toNat < 2 ^ 32) :
    (a.setWidth 64 + b.setWidth 64).toNat = a.toNat + b.toNat := by
  simp only [BitVec.toNat_add, BitVec.toNat_setWidth]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

theorem m7_p6_sub1_toNat {x : BitVec 32} (hx : 0 < x.toNat) :
    (x - 1#32).toNat = x.toNat - 1 := by
  rw [BitVec.toNat_sub, show (1#32 : BitVec 32).toNat = 1 from rfl]; omega

theorem m7_p6_add1_toNat {x : BitVec 32} (hx : x.toNat + 1 < 2 ^ 32) :
    (x + 1#32).toNat = x.toNat + 1 := by
  rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl, Nat.mod_eq_of_lt hx]

theorem m7_p6_off_add (n : Nat) (hn : n < 2 ^ 32)
    (i : BitVec 32) (hi : n + i.toNat < 2 ^ 32) :
    (BitVec.setWidth 64 ((@OfNat.ofNat (BitVec 32) n (BitVec.instOfNat)) + i)).toNat =
      n + i.toNat := by
  rw [m6_zext32_toNat, BitVec.toNat_add,
    show (@OfNat.ofNat (BitVec 32) n (BitVec.instOfNat)).toNat = n from by
      rw [show (@OfNat.ofNat (BitVec 32) n (BitVec.instOfNat)) = BitVec.ofNat 32 n from rfl,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn],
    Nat.mod_eq_of_lt hi]

theorem m7_p6_shr1_lt {n : Nat} {l : BitVec 32} (hl : l.toNat < 2 * n) :
    (l >>> (1 : Nat)).toNat = l.toNat / 2 ∧ (l >>> (1 : Nat)).toNat < n := by
  have h1 : (l >>> (1 : Nat)).toNat = l.toNat / 2 := by
    simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  exact ⟨h1, by omega⟩

theorem m7_p6_local_lit_lt {tmkv l : BitVec 32}
    (ht : 1 ≤ tmkv.toNat) (htle : tmkv.toNat ≤ 64) :
    (((tmkv - 1#32) <<< (1 : Nat)) ||| (l &&& 1#32)).toNat < 128 := by
  have hm1 : (tmkv - 1#32).toNat = tmkv.toNat - 1 := by
    rw [BitVec.toNat_sub, show (1#32 : BitVec 32).toNat = 1 from rfl]; omega
  have hsh : ((tmkv - 1#32) <<< (1 : Nat)).toNat = 2 * (tmkv.toNat - 1) := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, hm1, Nat.mod_eq_of_lt (by omega)]; omega
  have hand : (l &&& 1#32).toNat < 2 := by
    rw [BitVec.toNat_and, show (1#32 : BitVec 32).toNat = 1 from rfl]
    have := Nat.and_le_right (n := l.toNat) (m := 1); omega
  rw [BitVec.toNat_or, hsh]
  exact Nat.or_lt_two_pow (by omega : 2 * (tmkv.toNat - 1) < 2 ^ 7) (by omega)

/-! ## 2. `FullDenseInvW`, `FullBveEntryOkW`, & Level-0 Transition Helpers -/

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

theorem m7_p6_fullDenseInvW_def {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s)
    {tmp' exp' tmk' scr' : List (BitVec 32)}
    (htl : tmp'.length = c.max_vars) (hel : exp'.length = 2 * c.max_vars)
    (html : tmk'.length = 2 * c.max_vars) (hscl : scr'.length = c.scratch_cap) :
    FullDenseInvW c F0 F_cur
      { s with
        core := { s.core with tmp := tmp' }
        scratch := { s.scratch with wsort := exp', tarjan_mark := tmk', scratch_buf := scr' } } :=
  m8_fullDenseInvW_def h htl hel html hscl

theorem m7_p6_fullDenseInvW_fuel {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) (fl' : BitVec 64) :
    FullDenseInvW c F0 F_cur { s with core := { s.core with fuel := fl' } } :=
  m8_fullDenseInvW_fuel h fl'

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

theorem m7_p6_fullBveEntry_mono {F_cur : List (List Nat)} {s : FullState}
    {tmp' : List (BitVec 32)} {fuel' : BitVec 64} {exp' tmk' scr' : List (BitVec 32)}
    {lit : Nat} {w : BitVec 32} (h : FullBveEntryOkW F_cur s lit w) :
    FullBveEntryOkW F_cur
      { s with
        core := { s.core with tmp := tmp', fuel := fuel' }
        scratch := { s.scratch with wsort := exp', tarjan_mark := tmk', scratch_buf := scr' } }
      lit w :=
  m8_bveEntry_congr_core h rfl rfl rfl

theorem m7_p6_entry_bin_bounds {F_cur : List (List Nat)} {s : FullState}
    {lit : Nat} {w : BitVec 32} (h : FullBveEntryOkW F_cur s lit w)
    (hbin : (w &&& 0x80000000#32) ≠ 0#32) :
    (w &&& 0x7FFFFFFF#32).toNat < 2 * s.core.cur_vars := by
  unfold FullBveEntryOkW at h; rw [ite_eq_left hbin] at h; exact h.1

theorem m7_p6_entry_large_bounds {c : FullCfg} {F0 : CNF Nat}
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

theorem m6_lvl0_false_entails {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (hcl0 : k.cur_level = 0)
    {l : Nat} (hlt : l < 2 * k.cur_vars) (hf : k.vals[l]?.getD 0#8 = 0xFF#8) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause [l ^^^ 1]) := by
  obtain ⟨i, hi, htrl⟩ := (hw.vals_false_iff l hlt).mp hf
  have hl0 : (k.lvl[(k.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by
    have := hw.lvl_le i hi; omega
  have hent := hw.level0_sound i hi hl0
  rwa [htrl] at hent

theorem m6_entails_resolve_unit {F : CNF Nat} {p q : Nat}
    (hp : F.EntailsClause (cnfClause [p ^^^ 1])) (hpq : F.EntailsClause (cnfClause [p, q])) :
    F.EntailsClause (cnfClause [q]) := by
  rw [CNF.entails_clause_def] at hp hpq ⊢
  intro β hβ
  have h1 := hp β hβ
  have h2 := hpq β hβ
  rw [show p ^^^ 1 = litNeg p from rfl, sat_cnfClause_litNeg_iff] at h1
  obtain ⟨x, hx, hxs⟩ := (clause_sat_cnfClause_iff β [p, q]).mp h2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with hxp | hxq
  · exact absurd ((sat_cnfClause_singleton β p).mpr (hxp ▸ hxs)) h1
  · exact (sat_cnfClause_singleton β q).mpr (hxq ▸ hxs)

theorem m6_lvl0_clause_unit_entails {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hw : FullWitnessInv c F0 F_cur s.core) (hcl0 : s.core.cur_level = 0)
    {cr unit : Nat} (hcr : cr ∈ fullArenaClauseRefs s)
    (hng : fullArenaClauseGarb s cr = false)
    (hall : ∀ l ∈ fullArenaClauseLits s cr, l = unit ∨ s.core.vals[l]?.getD 0#8 = 0xFF#8) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause [unit]) := by
  rw [CNF.entails_clause_def]; intro β hβ
  have hent_cr := CNF.entails_clause_def.mp (hw.arena.entails cr hcr hng) β hβ
  obtain ⟨l, hl, hs⟩ := (clause_sat_cnfClause_iff β _).mp hent_cr
  rcases hall l hl with rfl | hf
  · exact (sat_cnfClause_singleton β l).mpr hs
  · exfalso
    have hlt := hw.arena.lits_lt cr hcr hng l hl
    have hent_l := CNF.entails_clause_def.mp (m6_lvl0_false_entails hw hcl0 hlt hf) β hβ
    have hneg := (sat_cnfClause_litNeg_iff β l).mp hent_l
    exact absurd ((sat_cnfClause_singleton β l).mpr hs) hneg

theorem m6_lvl0_unit_contra_unsat {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (hcl0 : k.cur_level = 0)
    {l : Nat} (hlt : l < 2 * k.cur_vars) (hf : k.vals[l]?.getD 0#8 = 0xFF#8)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [l])) :
    (cnfOfClauses F_cur).Unsat := by
  refine unsat_of_entails_nil (entails_of_mem_or_false hent fun x hx => ?_)
  simp only [List.mem_singleton] at hx; rw [hx]; right
  obtain ⟨i, hi, htrl⟩ := (hw.vals_false_iff l hlt).mp hf
  have hl0 : (k.lvl[(k.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by
    have := hw.lvl_le i hi; omega
  have hs := hw.level0_sound i hi hl0; rwa [htrl] at hs

/-- Fixed-`F_cur` level-0 `full_assign_lvl` transition preserving `FullDenseInvW`. -/
theorem assignLvl0_preserves_denseInvW {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hinv : FullDenseInvW c F0 F_cur s) {lit : BitVec 32}
    {flags' : List (BitVec 32)} {unassigned' unflushed' : BitVec 64} {phases' : List (BitVec 8)}
    (hfll : flags'.length = c.max_vars) (hphl : phases'.length = c.max_vars)
    (hlit : lit.toNat < 2 * s.core.cur_vars)
    (hun : s.core.vals[lit.toNat]?.getD 0#8 = 0#8)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [lit.toNat])) :
    let v := lit.toNat / 2
    let s' : FullState :=
      { s with
        core :=
          { s.core with
            vals := (s.core.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8
            flags := flags', lvl := s.core.lvl.set v 0#32
            rsns := s.core.rsns.set v 0xFFFFFFFF#32
            trl := s.core.trl.set s.core.trail_end lit
            trail_pos := s.core.trail_pos.set v (BitVec.ofNat 32 s.core.trail_end)
            trail_end := s.core.trail_end + 1
            unassigned := unassigned', unflushed := unflushed' }
        scratch := { s.scratch with phases := phases' } }
    FullDenseInvW c F0 F_cur s' ∧ fullArenaClauseRefs s' = fullArenaClauseRefs s := by
  intro v s'
  have hcl := hinv.1.core_ok; have hsc := hinv.1.scratch_ok; have hw := hinv.2.1
  have hcl0 := hinv.2.2.2.2.2.1
  have hte_lt : s.core.trail_end < s.core.cur_vars := hw.trail_end_lt_of_unassigned hlit hun
  have hnot_var : ∀ i < s.core.trail_end, (s.core.trl[i]?.getD 0#32).toNat / 2 ≠ v :=
    (hw.vals_zero_iff hlit).mp hun
  have hne_lit : lit.toNat ^^^ 1 ≠ lit.toNat := litNeg_ne_self lit.toNat
  have hv_lt : v < c.max_vars := by have := hcl.cur_vars_le; omega
  have hte_max : s.core.trail_end < c.max_vars := by have := hcl.cur_vars_le; omega
  have hte_lt32 : s.core.trail_end < 2 ^ 32 := by have := fullInv_max_vars_lt32 c; omega
  have htrl_get : ∀ i < s.core.trail_end + 1,
      (s'.core.trl[i]?.getD 0#32).toNat =
        if i = s.core.trail_end then lit.toNat else (s.core.trl[i]?.getD 0#32).toNat :=
    fun i _ => by
      by_cases he : i = s.core.trail_end
      · subst he; simp [s', List.getElem?_set_self (by rw [hcl.trl_len]; exact hte_max)]
      · simp [s', he, List.getElem?_set_ne (Ne.symm he)]
  have hlvl_get : ∀ w < s.core.cur_vars,
      (s'.core.lvl[w]?.getD 0#32).toNat =
        if w = v then 0 else (s.core.lvl[w]?.getD 0#32).toNat := fun w _ => by
    by_cases he : w = v
    · subst he; simp [s', List.getElem?_set_self (by rw [hcl.lvl_len]; exact hv_lt)]
    · simp [s', he, List.getElem?_set_ne (Ne.symm he)]
  have hvals_get : ∀ l < 2 * s.core.cur_vars,
      s'.core.vals[l]?.getD 0#8 =
        if l = lit.toNat ^^^ 1 then 0xFF#8 else if l = lit.toNat then 1#8
        else s.core.vals[l]?.getD 0#8 := fun l hl => by
    have hcm := hcl.cur_vars_le
    by_cases h1 : l = lit.toNat ^^^ 1
    · subst h1; dsimp only [s']; simp only [↓reduceIte]
      rw [List.getElem?_set_self (by simp [hcl.vals_len]; omega)]; rfl
    · dsimp only [s']; simp only [h1, ↓reduceIte]; rw [List.getElem?_set_ne (Ne.symm h1)]
      by_cases h2 : l = lit.toNat
      · subst h2; simp only [↓reduceIte]
        rw [List.getElem?_set_self (by rw [hcl.vals_len]; omega)]; rfl
      · simp only [h2, ↓reduceIte]; rw [List.getElem?_set_ne (Ne.symm h2)]
  have hrsn_get : ∀ w < s.core.cur_vars,
      s'.core.rsns[w]?.getD 0xFFFFFFFF#32 =
        if w = v then 0xFFFFFFFF#32 else s.core.rsns[w]?.getD 0xFFFFFFFF#32 := fun w _ => by
    by_cases he : w = v
    · subst he; simp [s', List.getElem?_set_self (by rw [hcl.rsns_len]; exact hv_lt)]
    · simp [s', he, List.getElem?_set_ne (Ne.symm he)]
  have hlen' : s'.LengthsOk c :=
    ⟨{ hcl with
       vals_len := by simp [s', hcl.vals_len], flags_len := hfll,
       lvl_len := by simp [s', hcl.lvl_len], rsns_len := by simp [s', hcl.rsns_len],
       trl_len := by simp [s', hcl.trl_len], trail_pos_len := by simp [s', hcl.trail_pos_len],
       trail_end_le := by dsimp [s']; omega,
       propagated_le := by have := hcl.propagated_le; dsimp [s']; omega },
     { hsc with phases_len := hphl }⟩
  have hw' : FullWitnessInv c F0 F_cur s'.core :=
    { ext_sound := hw.ext_sound, inconsistent_sound := hw.inconsistent_sound
      arena := { hw.arena with len_ok := hw.arena.len_ok }
      watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r)
      cur_level_le := by change s.core.cur_level ≤ s.core.trail_end + 1; omega
      trail_lits_lt := fun i hi => by
        change i < s.core.trail_end + 1 at hi
        change (s'.core.trl[i]?.getD 0#32).toNat < 2 * s.core.cur_vars
        rw [htrl_get i hi]; split
        · exact hlit
        · exact hw.trail_lits_lt i (by omega)
      trail_vars_nodup := fun i j hi hj hveq => by
        change i < s.core.trail_end + 1 at hi; change j < s.core.trail_end + 1 at hj
        change (s'.core.trl[i]?.getD 0#32).toNat / 2 =
          (s'.core.trl[j]?.getD 0#32).toNat / 2 at hveq
        rw [htrl_get i hi, htrl_get j hj] at hveq
        split at hveq <;> split at hveq
        · omega
        · exact absurd hveq.symm (hnot_var j (by omega))
        · exact absurd hveq (hnot_var i (by omega))
        · exact hw.trail_vars_nodup i j (by omega) (by omega) hveq
      vals_domain := fun l hl => by
        change l < 2 * s.core.cur_vars at hl; rw [hvals_get l hl]
        split; · exact Or.inr (Or.inr rfl)
        split; · exact Or.inr (Or.inl rfl)
        exact hw.vals_domain l hl
      vals_true_iff := fun l hl => by
        change l < 2 * s.core.cur_vars at hl
        change s'.core.vals[l]?.getD 0#8 = 1#8 ↔
          ∃ i < s.core.trail_end + 1, (s'.core.trl[i]?.getD 0#32).toNat = l
        rw [hvals_get l hl]; constructor
        · intro h1; by_cases hneg : l = lit.toNat ^^^ 1
          · simp [hneg] at h1
          · simp only [hneg, ↓reduceIte] at h1; by_cases hpos : l = lit.toNat
            · exact ⟨s.core.trail_end, by omega, by rw [htrl_get _ (by omega)]; simp [hpos]⟩
            · simp only [hpos, ↓reduceIte] at h1
              obtain ⟨i, hi, heq⟩ := (hw.vals_true_iff l hl).mp h1
              exact ⟨i, by omega,
                by rw [htrl_get i (by omega)]; simp [show i ≠ s.core.trail_end by omega, heq]⟩
        · rintro ⟨i, hi, heq⟩; rw [htrl_get i hi] at heq
          by_cases hie : i = s.core.trail_end
          · simp only [hie, ↓reduceIte] at heq; subst heq; simp [Ne.symm hne_lit]
          · simp only [hie, ↓reduceIte] at heq
            have hlv : l / 2 ≠ v := by rw [← heq]; exact hnot_var i (by omega)
            have h1 : l ≠ lit.toNat ^^^ 1 := fun h => hlv (by rw [h, fullInv_var_xor1])
            have h2 : l ≠ lit.toNat := fun h => hlv (by rw [h])
            simp only [h1, h2, ↓reduceIte]; exact (hw.vals_true_iff l hl).mpr ⟨i, by omega, heq⟩
      vals_false_iff := fun l hl => by
        change l < 2 * s.core.cur_vars at hl
        change s'.core.vals[l]?.getD 0#8 = 0xFF#8 ↔
          ∃ i < s.core.trail_end + 1, (s'.core.trl[i]?.getD 0#32).toNat = l ^^^ 1
        rw [hvals_get l hl]; constructor
        · intro h1; by_cases hneg : l = lit.toNat ^^^ 1
          · exact ⟨s.core.trail_end, by omega, by
              rw [htrl_get _ (by omega)]; simp only [↓reduceIte, hneg]
              exact (litNeg_litNeg _).symm⟩
          · simp only [hneg, ↓reduceIte] at h1; by_cases hpos : l = lit.toNat
            · simp [hpos] at h1
            · simp only [hpos, ↓reduceIte] at h1
              obtain ⟨i, hi, heq⟩ := (hw.vals_false_iff l hl).mp h1
              exact ⟨i, by omega,
                by rw [htrl_get i (by omega)]; simp [show i ≠ s.core.trail_end by omega, heq]⟩
        · rintro ⟨i, hi, heq⟩; rw [htrl_get i hi] at heq
          by_cases hie : i = s.core.trail_end
          · simp only [hie, ↓reduceIte] at heq
            have hl_eq : l = lit.toNat ^^^ 1 := by
              have h := congrArg litNeg heq; have h1 : litNeg (l ^^^ 1) = l := litNeg_litNeg l
              rw [h1] at h; exact h.symm
            simp [hl_eq]
          · simp only [hie, ↓reduceIte] at heq
            have hlv : l / 2 ≠ v := by
              have h := hnot_var i (by omega); rw [heq] at h; rwa [fullInv_var_xor1] at h
            have h1 : l ≠ lit.toNat ^^^ 1 := fun h => hlv (by rw [h, fullInv_var_xor1])
            have h2 : l ≠ lit.toNat := fun h => hlv (by rw [h])
            simp only [h1, h2, ↓reduceIte]; exact (hw.vals_false_iff l hl).mpr ⟨i, by omega, heq⟩
      lvl_le := fun i hi => by
        change i < s.core.trail_end + 1 at hi
        change (s'.core.lvl[(s'.core.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
          s.core.cur_level
        rw [htrl_get i hi]; by_cases hie : i = s.core.trail_end
        · simp only [hie, ↓reduceIte]; rw [hlvl_get v (by omega)]; simp
        · have hilt : i < s.core.trail_end := by omega
          simp only [hie, ↓reduceIte]; rw [hlvl_get _ (by have := hw.trail_lits_lt i hilt; omega)]
          simp only [hnot_var i hilt, ↓reduceIte]; exact hw.lvl_le i hilt
      dec_earliest := fun i j hi hj hleq hdec => by
        change i < s.core.trail_end + 1 at hi; change j < s.core.trail_end + 1 at hj
        change _ = _ at hleq; change 0 < _ ∧ _ at hdec
        rw [htrl_get i hi] at hleq; rw [htrl_get j hj] at hleq hdec
        by_cases hje : j = s.core.trail_end
        · subst hje; simp only [↓reduceIte] at hdec
          rw [hlvl_get v (by omega)] at hdec; simp at hdec
        · by_cases hie : i = s.core.trail_end
          · subst hie; simp only [↓reduceIte] at hleq
            have hjlt : j < s.core.trail_end := by omega
            simp only [hje, ↓reduceIte] at hleq hdec
            rw [hlvl_get v (by omega),
              hlvl_get _ (by have := hw.trail_lits_lt j hjlt; omega)] at hleq
            rw [hlvl_get _ (by have := hw.trail_lits_lt j hjlt; omega)] at hdec
            simp only [↓reduceIte, hnot_var j hjlt] at hleq hdec; omega
          · have hilt : i < s.core.trail_end := by omega
            have hjlt : j < s.core.trail_end := by omega
            simp only [hie, hje, ↓reduceIte] at hleq hdec
            rw [hlvl_get _ (by have := hw.trail_lits_lt i hilt; omega),
              hlvl_get _ (by have := hw.trail_lits_lt j hjlt; omega)] at hleq
            rw [hlvl_get _ (by have := hw.trail_lits_lt j hjlt; omega),
              hrsn_get _ (by have := hw.trail_lits_lt j hjlt; omega)] at hdec
            simp only [hnot_var i hilt, hnot_var j hjlt, ↓reduceIte] at hleq hdec
            exact hw.dec_earliest i j hilt hjlt hleq hdec
      levels_inhabited := fun L hL1 hLle => by change L ≤ s.core.cur_level at hLle; omega
      level0_sound := fun i hi hli => by
        change i < s.core.trail_end + 1 at hi
        change (s'.core.lvl[(s'.core.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 at hli
        change (cnfOfClauses F_cur).EntailsClause (cnfClause [(s'.core.trl[i]?.getD 0#32).toNat])
        rw [htrl_get i hi] at hli ⊢
        by_cases hie : i = s.core.trail_end
        · simp only [hie, ↓reduceIte] at hli ⊢; exact hent
        · have hilt : i < s.core.trail_end := by omega
          simp only [hie, ↓reduceIte] at hli ⊢
          rw [hlvl_get _ (by have := hw.trail_lits_lt i hilt; omega)] at hli
          simp only [hnot_var i hilt, ↓reduceIte] at hli; exact hw.level0_sound i hilt hli
      trail_pos_inv := fun i hi => by
        change i < s.core.trail_end + 1 at hi
        change (s'.core.trail_pos[(s'.core.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = i
        rw [htrl_get i hi]; by_cases hie : i = s.core.trail_end
        · subst hie; simp only [↓reduceIte]; dsimp only [s']
          rw [List.getElem?_set_self (by rw [hcl.trail_pos_len]; exact hv_lt),
            Option.getD_some, bv32_ofNat_toNat hte_lt32]
        · have hilt : i < s.core.trail_end := by omega
          simp only [hie, ↓reduceIte]; dsimp only [s']
          rw [List.getElem?_set_ne (Ne.symm (hnot_var i hilt))]; exact hw.trail_pos_inv i hilt
      level0_rsn_none := fun idx hidx hli => by
        change idx < s.core.trail_end + 1 at hidx
        change (s'.core.lvl[(s'.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 at hli
        change s'.core.rsns[(s'.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 =
          0xFFFFFFFF#32
        rw [htrl_get idx hidx] at hli ⊢
        by_cases hie : idx = s.core.trail_end
        · simp only [hie, ↓reduceIte]; rw [hrsn_get v (by omega)]; simp
        · have hilt : idx < s.core.trail_end := by omega
          simp only [hie, ↓reduceIte] at hli ⊢
          rw [hlvl_get _ (by have := hw.trail_lits_lt idx hilt; omega)] at hli
          rw [hrsn_get _ (by have := hw.trail_lits_lt idx hilt; omega)]
          simp only [hnot_var idx hilt, ↓reduceIte] at hli ⊢
          exact hw.level0_rsn_none idx hilt hli
      frame_trail_lt := fun L hL => by
        change L ≤ s.core.cur_level at hL
        exact Nat.le_trans (hw.frame_trail_lt L hL) (Nat.le_succ _)
      frame_trail_mono := hw.frame_trail_mono
      frame_trail_before_lt := fun L hL1 hLle => by change L ≤ s.core.cur_level at hLle; omega
      frame_dec_lt := fun L hL1 hLle => by change L ≤ s.core.cur_level at hLle; omega
      reason_inv := fun idx hidx hne => by
        change idx < s.core.trail_end + 1 at hidx
        change s'.core.rsns[(s'.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 ≠
          0xFFFFFFFF#32 at hne
        rw [htrl_get idx hidx] at hne
        have hilt : idx < s.core.trail_end := by
          by_cases hie : idx = s.core.trail_end
          · simp only [hie, ↓reduceIte] at hne; rw [hrsn_get v (by omega)] at hne; simp at hne
          · omega
        have hl0 : (s.core.lvl[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by
          have := hw.lvl_le idx hilt; omega
        simp only [show idx ≠ s.core.trail_end by omega, ↓reduceIte] at hne
        rw [hrsn_get _ (by have := hw.trail_lits_lt idx hilt; omega)] at hne
        simp only [hnot_var idx hilt, ↓reduceIte] at hne
        exact absurd (hw.level0_rsn_none idx hilt hl0) hne
      reason_lit_mem := fun idx hidx hne _ => by
        change idx < s.core.trail_end + 1 at hidx
        change s'.core.rsns[(s'.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 ≠
          0xFFFFFFFF#32 at hne
        rw [htrl_get idx hidx] at hne
        have hilt : idx < s.core.trail_end := by
          by_cases hie : idx = s.core.trail_end
          · simp only [hie, ↓reduceIte] at hne; rw [hrsn_get v (by omega)] at hne; simp at hne
          · omega
        have hl0 : (s.core.lvl[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by
          have := hw.lvl_le idx hilt; omega
        simp only [show idx ≠ s.core.trail_end by omega, ↓reduceIte] at hne
        rw [hrsn_get _ (by have := hw.trail_lits_lt idx hilt; omega)] at hne
        simp only [hnot_var idx hilt, ↓reduceIte] at hne
        exact absurd (hw.level0_rsn_none idx hilt hl0) hne }
  exact ⟨⟨hlen', hw', hinv.2.2.1, hinv.2.2.2.1, hinv.2.2.2.2.1, hcl0, hinv.2.2.2.2.2.2⟩, rfl⟩

theorem m6_denseInvW_set_inconsistent {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hinv : FullDenseInvW c F0 F_cur s)
    (ct c0 c1 cr : BitVec 64) (huns : (cnfOfClauses F_cur).Unsat) :
    FullDenseInvW c F0 F_cur
      { s with core :=
        { s.core with inconsistent := 1#64, confl_type := ct,
                      confl_lit0 := c0, confl_lit1 := c1, confl_ref := cr } } := by
  have hcl := hinv.1.core_ok; have hw := hinv.2.1
  let s' : FullState :=
    { s with core :=
      { s.core with inconsistent := 1#64, confl_type := ct,
                    confl_lit0 := c0, confl_lit1 := c1, confl_ref := cr } }
  have hlen' : s'.LengthsOk c := ⟨{ hcl with vals_len := hcl.vals_len }, hinv.1.scratch_ok⟩
  have hw' : FullWitnessInv c F0 F_cur s'.core :=
    { hw with
      inconsistent_sound := fun _ => huns
      arena := { hw.arena with len_ok := hw.arena.len_ok }
      watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) }
  exact ⟨hlen', hw', hinv.2.2.1, hinv.2.2.2.1, hinv.2.2.2.2.1, hinv.2.2.2.2.2.1,
    hinv.2.2.2.2.2.2⟩

/-! ## 3. Shared M7 K6 & Scratch Tactics (`K6Tactics`, `P6Scr`, `P6Tactics`) -/

namespace K6Tactics

private theorem k6_m4 (a i : BitVec 64) :
    a + i * 4 = a + BitVec.ofNat 64 (4 * i.toNat) := by
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_mul_ofNat]

private theorem k6_m4_base (a i : BitVec 64) :
    a + 1096#64 * 4#64 + i * 4 = a + BitVec.ofNat 64 (4 * (1096 + i.toNat)) := by
  rw [BitVec.add_assoc]; congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
  simp only [Nat.reducePow, Nat.reduceMod]
  rw [show BitVec.toNat 4 = 4 from rfl, Nat.mul_add, Nat.add_mod_mod]
  congr 1; omega

private theorem k6_fuel_addr (h : BitVec 64) :
    h + 168#64 = (h + 32) + BitVec.ofNat 64 (8 * 17) := by
  rw [BitVec.add_assoc]; congr 1

@[scoped c0_load] theorem c0_load_k6_base {pk : BitVec 64} {kbuf : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64}
    (hi : i.toNat < 2912) (hlen : 2912 ≤ kbuf.length)
    (hm : (array (t := i32) pk kbuf ⋆ R) m) :
    loadVal m i32 (pk + i * 4) = some (kbuf[i.toNat]'(by omega)) := by
  rw [k6_m4]; exact loadVal_array (t := i32) (by decide) (by omega) hm

@[scoped c0_store] theorem c0_store_k6_base {pk : BitVec 64} {kbuf : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64} (v : BitVec 32)
    (hi : i.toNat < 2912) (hlen : 2912 ≤ kbuf.length)
    (hm : (array (t := i32) pk kbuf ⋆ R) m) :
    storeOk m i32 (pk + i * 4) ∧
      (array (t := i32) pk (kbuf.set i.toNat v) ⋆ R)
        (storeMem m i32 (pk + i * 4) v) := by
  rw [k6_m4]; exact store_array (t := i32) v (by decide) (by omega) hm

@[scoped c0_load] theorem c0_load_k6 {pk : BitVec 64} {kbuf : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64} (hi : i.toNat < kbuf.length)
    (hm : (array (t := i32) pk kbuf ⋆ R) m) :
    loadVal m i32 (pk + i * 4) = some kbuf[i.toNat] := by
  rw [k6_m4]; exact loadVal_array (t := i32) (by decide) hi hm

@[scoped c0_store] theorem c0_store_k6 {pk : BitVec 64} {kbuf : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64} (v : BitVec 32)
    (hi : i.toNat < kbuf.length) (hm : (array (t := i32) pk kbuf ⋆ R) m) :
    storeOk m i32 (pk + i * 4) ∧
      (array (t := i32) pk (kbuf.set i.toNat v) ⋆ R)
        (storeMem m i32 (pk + i * 4) v) := by
  rw [k6_m4]; exact store_array (t := i32) v (by decide) hi hm

@[scoped c0_load] theorem c0_load_k6_fuel {h : BitVec 64} {hdr : List (BitVec 64)}
    {R : Mem 64 → Prop} {m : Mem 64} (hh : 17 < hdr.length)
    (hm : (array64 (h + 32) hdr ⋆ R) m) :
    loadVal m i64 (h + 168#64) = some hdr[17] := by
  rw [k6_fuel_addr]; exact loadVal_array64 hh hm

@[scoped c0_store] theorem c0_store_k6_fuel {h : BitVec 64} {hdr : List (BitVec 64)}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 64) (hh : 17 < hdr.length)
    (hm : (array64 (h + 32) hdr ⋆ R) m) :
    storeOk m i64 (h + 168#64) ∧
      (array64 (h + 32) (hdr.set 17 v) ⋆ R) (storeMem m i64 (h + 168#64) v) := by
  rw [k6_fuel_addr]; exact store_array64 v hh hm

@[scoped c0_load] theorem c0_load_full_scratch_k6 {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64}
    (hi : 1096 + i.toNat < s.scratch.scratch_buf.length)
    (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 (c.pScratchBuf + 1096#64 * 4#64 + i * 4) =
      some s.scratch.scratch_buf[1096 + i.toNat] := by
  rw [k6_m4_base]; exact FullArenaTactics.load_full_scratch_buf hi hm

@[scoped c0_store] theorem c0_store_full_scratch_k6 {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64} (v : BitVec 32)
    (hi : 1096 + i.toNat < s.scratch.scratch_buf.length)
    (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 (c.pScratchBuf + 1096#64 * 4#64 + i * 4) ∧
      (FullMem c
        { s with
          scratch := { s.scratch with
            scratch_buf := s.scratch.scratch_buf.set (1096 + i.toNat) v } } ⋆ R)
        (storeMem m i32 (c.pScratchBuf + 1096#64 * 4#64 + i * 4) v) := by
  rw [k6_m4_base]; exact FullArenaTactics.store_full_scratch_buf v hi hm

@[scoped bv_c0] theorem k6_bv32_shl1 (x : BitVec 32) :
    (x <<< (1 : Nat)).toNat = (2 * x.toNat) % 2 ^ 32 := by
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm]

@[scoped bv_c0] theorem k6_bv32_shl1_or1 (x : BitVec 32) :
    ((x <<< (1 : Nat)) ||| (1 : BitVec 32)).toNat = (2 * x.toNat + 1) % 2 ^ 32 :=
  m8_bv32_shl1_or1_toNat_gen x
where
  m8_bv32_shl1_or1_toNat_gen (y : BitVec 32) :
      ((y <<< (1 : Nat)) ||| (1 : BitVec 32)).toNat = (2 * y.toNat + 1) % 2 ^ 32 := by
    have h1 : (y <<< (1 : Nat)).toNat = (2 * y.toNat) % 2 ^ 32 := k6_bv32_shl1 y
    rw [BitVec.toNat_or, h1, show (1 : BitVec 32).toNat = 1 from rfl]
    apply Nat.eq_of_testBit_eq; intro i
    cases i with
    | zero =>
      rw [Nat.testBit_or, Nat.testBit_zero, Nat.testBit_zero, Nat.testBit_zero]
      have h0 : (2 * y.toNat % 2 ^ 32) % 2 = 0 := by omega
      have h1m : (2 * y.toNat + 1) % 2 ^ 32 % 2 = 1 := by omega
      rw [h0, h1m]; decide
    | succ j =>
      rw [Nat.testBit_or, Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ]
      have h1d : (1 : Nat) / 2 = 0 := rfl
      rw [h1d, Nat.zero_testBit, Bool.or_false]; congr 1; omega

@[scoped bv_c0] theorem k6_bv32_lshr1 (x : BitVec 32) :
    (x >>> (1 : Nat)).toNat = x.toNat / 2 := by
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

end K6Tactics

/-- Scratch buffer invariant for `def_k6_m7` `u32 *scr` and `u32 *k` (`scr + 1096`) stores. -/
@[expose] def P6Scr (cap : Nat) (pk : BitVec 64) (scr : List (BitVec 32)) : Mem 64 → Prop :=
  fun m => 8192 ≤ cap ∧ scr.length = cap ∧ array (t := i32) pk scr m

theorem P6Scr_eq (cap : Nat) (pk : BitVec 64) (scr : List (BitVec 32)) :
    P6Scr cap pk scr =
      (fun m => 8192 ≤ cap ∧ scr.length = cap ∧ array (t := i32) pk scr m) := rfl

@[expose] def m7_p6_fullWithoutScr (c : FullCfg) (s : FullState) : Mem 64 → Prop :=
  dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
  array64 (c.hdr + 32) (hdrTailWords c s) ⋆
  FullCoreArrays c s.core ⋆
  (FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆ FullScrWksArrs c s.scratch ⋆
   FullScrMetaArrs c s.scratch ⋆
   (array (t := i32) c.pDelayed s.scratch.delayed ⋆
    array (t := i32) c.pRedRefs s.scratch.red_refs ⋆
    array (t := i32) c.pExtendStk s.scratch.extend_stk)) ⋆ c.pad

theorem m7_p6_scrBuf_split {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (h8192 : 8192 ≤ c.scratch_cap) (hlen : s.scratch.scratch_buf.length = c.scratch_cap)
    (hm : (FullMem c s ⋆ R) m) :
    (P6Scr c.scratch_cap c.pScratchBuf s.scratch.scratch_buf ⋆
      (m7_p6_fullWithoutScr c s ⋆ R)) m := by
  have heq : (FullMem c s ⋆ R) =
      (array (t := i32) c.pScratchBuf s.scratch.scratch_buf ⋆
        (m7_p6_fullWithoutScr c s ⋆ R)) := by
    unfold FullMem FullScratchArrays FullScrDynArrs m7_p6_fullWithoutScr; ac_rfl
  rw [P6Scr_eq, sep_pure_l, sep_pure_l]
  exact ⟨h8192, hlen, heq ▸ hm⟩

theorem m7_p6_scrBuf_unsplit {c : FullCfg} {s : FullState} {scr' : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (P6Scr c.scratch_cap c.pScratchBuf scr' ⋆
      (m7_p6_fullWithoutScr c s ⋆ R)) m) :
    (FullMem c { s with scratch := { s.scratch with scratch_buf := scr' } } ⋆ R) m := by
  let sf : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
  have houter : m7_p6_fullWithoutScr c sf = m7_p6_fullWithoutScr c s := rfl
  have heq : (FullMem c sf ⋆ R) =
      (array (t := i32) c.pScratchBuf scr' ⋆ (m7_p6_fullWithoutScr c sf ⋆ R)) := by
    unfold FullMem FullScratchArrays FullScrDynArrs m7_p6_fullWithoutScr
    dsimp only [sf]; ac_rfl
  rw [houter] at heq; rw [P6Scr_eq, sep_pure_l, sep_pure_l] at hm
  exact heq.symm ▸ hm.2.2

theorem m7_p6_scrBuf_unsplit_eq {c : FullCfg} {s : FullState}
    {scr' scr_h : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (P6Scr c.scratch_cap c.pScratchBuf scr' ⋆
      (m7_p6_fullWithoutScr c s ⋆ R)) m)
    (heq : scr' = scr_h := by rfl) :
    (FullMem c { s with scratch := { s.scratch with scratch_buf := scr_h } } ⋆ R) m :=
  heq ▸ m7_p6_scrBuf_unsplit hm

@[expose] def m7_p6_fullK6Outer (c : FullCfg) (s : FullState) : Mem 64 → Prop :=
  dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
  FullCoreArrays c s.core ⋆
  (FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆ FullScrWksArrs c s.scratch ⋆
   FullScrMetaArrs c s.scratch ⋆
   (array (t := i32) c.pDelayed s.scratch.delayed ⋆
    array (t := i32) c.pRedRefs s.scratch.red_refs ⋆
    array (t := i32) c.pExtendStk s.scratch.extend_stk)) ⋆ c.pad

theorem m7_p6_hdrTail_set_fuel (c : FullCfg) (s : FullState) (fl' : BitVec 64) :
    (hdrTailWords c s).set 17 fl' =
      hdrTailWords c { s with core := { s.core with fuel := fl' } } := rfl

theorem m7_p6_fullMem_split_k6 {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hsc_len : 1096 ≤ s.scratch.scratch_buf.length)
    (hm : (FullMem c s ⋆ R) m) :
    (array64 (c.hdr + 32) (hdrTailWords c s) ⋆
      array (t := i32) (c.pScratchBuf + BitVec.ofNat 64 1096 * 4)
        (s.scratch.scratch_buf.drop 1096) ⋆
      (array (t := i32) c.pScratchBuf (s.scratch.scratch_buf.take 1096) ⋆
        m7_p6_fullK6Outer c s ⋆ R)) m := by
  have htake : (s.scratch.scratch_buf.take 1096).length = 1096 :=
    List.length_take_of_le hsc_len
  have hsb : array (t := i32) c.pScratchBuf s.scratch.scratch_buf =
      (array (t := i32) c.pScratchBuf (s.scratch.scratch_buf.take 1096) ⋆
       array (t := i32) (c.pScratchBuf + BitVec.ofNat 64 1096 * 4)
         (s.scratch.scratch_buf.drop 1096)) := by
    have ha := array_append (t := i32) c.pScratchBuf
      (s.scratch.scratch_buf.take 1096) (s.scratch.scratch_buf.drop 1096)
    rw [List.take_append_drop, htake,
      show BitVec.ofNat 64 (Ty.bytes i32 * 1096) = BitVec.ofNat 64 1096 * 4 from rfl] at ha
    exact ha
  have heq : (FullMem c s ⋆ R) =
      (array64 (c.hdr + 32) (hdrTailWords c s) ⋆
       array (t := i32) (c.pScratchBuf + BitVec.ofNat 64 1096 * 4)
         (s.scratch.scratch_buf.drop 1096) ⋆
       (array (t := i32) c.pScratchBuf (s.scratch.scratch_buf.take 1096) ⋆
        m7_p6_fullK6Outer c s ⋆ R)) := by
    unfold FullMem FullScratchArrays FullScrDynArrs m7_p6_fullK6Outer
    rw [hsb]; ac_rfl
  exact heq ▸ hm

theorem m7_p6_fullMem_unsplit_k6 {c : FullCfg} {s : FullState}
    {fl' : BitVec 64} {scr_pre kb' : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hpre : scr_pre.length = 1096)
    (hm : (array64 (c.hdr + 32) (hdrTailWords c s |>.set 17 fl') ⋆
      array (t := i32) (c.pScratchBuf + BitVec.ofNat 64 1096 * 4) kb' ⋆
      (array (t := i32) c.pScratchBuf scr_pre ⋆ m7_p6_fullK6Outer c s ⋆ R)) m) :
    (FullMem c
      { s with
        core := { s.core with fuel := fl' }
        scratch := { s.scratch with scratch_buf := scr_pre ++ kb' } } ⋆ R) m := by
  let sf : FullState :=
    { s with
      core := { s.core with fuel := fl' }
      scratch := { s.scratch with scratch_buf := scr_pre ++ kb' } }
  have houter : m7_p6_fullK6Outer c sf = m7_p6_fullK6Outer c s := rfl
  have hsb : array (t := i32) c.pScratchBuf (scr_pre ++ kb') =
      (array (t := i32) c.pScratchBuf scr_pre ⋆
       array (t := i32) (c.pScratchBuf + BitVec.ofNat 64 1096 * 4) kb') := by
    have ha := array_append (t := i32) c.pScratchBuf scr_pre kb'
    rw [hpre, show BitVec.ofNat 64 (Ty.bytes i32 * 1096) = BitVec.ofNat 64 1096 * 4 from rfl]
      at ha
    exact ha
  rw [m7_p6_hdrTail_set_fuel] at hm
  have heq : (FullMem c sf ⋆ R) =
      (array64 (c.hdr + 32) (hdrTailWords c sf) ⋆
       array (t := i32) (c.pScratchBuf + BitVec.ofNat 64 1096 * 4) kb' ⋆
       (array (t := i32) c.pScratchBuf scr_pre ⋆ m7_p6_fullK6Outer c sf ⋆ R)) := by
    unfold FullMem FullScratchArrays FullScrDynArrs m7_p6_fullK6Outer
    dsimp only [sf]; rw [hsb]; ac_rfl
  rw [houter] at heq
  exact heq.symm ▸ hm

namespace P6Tactics

private theorem p6_k_ptr_bv (p i : BitVec 64) :
    p + BitVec.ofNat 64 1096 * 4 + i * 4 =
      p + BitVec.ofNat 64 (4 * (1096 + i.toNat)) := by
  rw [BitVec.add_assoc]; congr 1
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat,
    Nat.mod_add_mod, Nat.add_mod_mod]
  congr 1; omega

@[scoped bv_c0] theorem p6_fullState_core (co : FullCoreState) (sc : FullScratch) :
    ({ core := co, scratch := sc } : FullState).core = co := rfl
@[scoped bv_c0] theorem p6_fullCore_vals (k : FullCoreState) (t : List (BitVec 32)) :
    ({ k with tmp := t } : FullCoreState).vals = k.vals := rfl
@[scoped bv_c0] theorem p6_fullCore_tmp (k : FullCoreState) (t : List (BitVec 32)) :
    ({ k with tmp := t } : FullCoreState).tmp = t := rfl
@[scoped bv_c0] theorem p6_fullCore_arena (k : FullCoreState) (t : List (BitVec 32)) :
    ({ k with tmp := t } : FullCoreState).arena = k.arena := rfl
@[scoped bv_c0] theorem p6_fullState_scratch (co : FullCoreState) (sc : FullScratch) :
    ({ core := co, scratch := sc } : FullState).scratch = sc := rfl
@[scoped bv_c0] theorem p6_fullScratch_tmk_set2 (s : FullScratch) (ws tm : List (BitVec 32)) :
    ({ s with wsort := ws, tarjan_mark := tm } : FullScratch).tarjan_mark = tm := rfl
@[scoped bv_c0] theorem p6_fullScratch_wsort_set2 (s : FullScratch) (ws tm : List (BitVec 32)) :
    ({ s with wsort := ws, tarjan_mark := tm } : FullScratch).wsort = ws := rfl
@[scoped bv_c0] theorem p6_fullScratch_buf_set (s : FullScratch) (scr : List (BitVec 32)) :
    ({ s with scratch_buf := scr } : FullScratch).scratch_buf = scr := rfl
@[scoped bv_c0] theorem p6_fullState_scratch_buf_set (co : FullCoreState) (sc : FullScratch)
    (scr : List (BitVec 32)) :
    ({ core := co, scratch := { sc with scratch_buf := scr } } :
      FullState).scratch.scratch_buf = scr := rfl
@[scoped bv_c0] theorem p6_fullState_with_scratch_buf_set (s : FullState) (scr : List (BitVec 32)) :
    ({ s with scratch := { s.scratch with scratch_buf := scr } } :
      FullState).scratch.scratch_buf = scr := rfl
@[scoped bv_c0] theorem p6_list_length_set {α : Type} (xs : List α) (i : Nat) (v : α) :
    (xs.set i v).length = xs.length := List.length_set
@[scoped bv_c0] theorem p6_fullScratch_buf_set3 (s : FullScratch)
    (ws tm scr : List (BitVec 32)) :
    ({ s with wsort := ws, tarjan_mark := tm, scratch_buf := scr } :
      FullScratch).scratch_buf = scr := rfl
@[scoped bv_c0] theorem p6_fullScratch_tmk_set3 (s : FullScratch)
    (ws tm scr : List (BitVec 32)) :
    ({ s with wsort := ws, tarjan_mark := tm, scratch_buf := scr } :
      FullScratch).tarjan_mark = tm := rfl
@[scoped bv_c0] theorem p6_fullScratch_wsort_set3 (s : FullScratch)
    (ws tm scr : List (BitVec 32)) :
    ({ s with wsort := ws, tarjan_mark := tm, scratch_buf := scr } :
      FullScratch).wsort = ws := rfl
@[scoped bv_c0] theorem p6_bv32_ushiftRight (x : BitVec 32) (k : Nat) :
    (x >>> k).toNat = x.toNat / 2 ^ k := by
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
@[scoped bv_c0] theorem p6_bv64_ofNat_toNat (n : Nat) :
    (BitVec.ofNat 64 n).toNat = n % 2 ^ 64 := @BitVec.toNat_ofNat n 64
@[scoped bv_c0] theorem p6_bv64_ofNat_ofNat_toNat (n : Nat) :
    (@BitVec.ofNat (@OfNat.ofNat Nat 64 (instOfNatNat 64)) n).toNat = n % 2 ^ 64 :=
  @BitVec.toNat_ofNat n 64
@[scoped bv_c0] theorem p6_bv32_ofNat_toNat (n : Nat) :
    (BitVec.ofNat 32 n).toNat = n % 2 ^ 32 := @BitVec.toNat_ofNat n 32

@[scoped c0_load] theorem c0_load_p6_k_bv {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64}
    (hi : 1096 + i.toNat < s.scratch.scratch_buf.length) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 (c.pScratchBuf + BitVec.ofNat 64 1096 * 4 + i * 4) =
      some (s.scratch.scratch_buf[1096 + i.toNat]'hi) := by
  rw [p6_k_ptr_bv]; exact FullArenaTactics.load_full_scratch_buf hi hm

@[scoped c0_store] theorem c0_store_p6_k_bv {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64} (v : BitVec 32)
    (hi : 1096 + i.toNat < s.scratch.scratch_buf.length) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 (c.pScratchBuf + BitVec.ofNat 64 1096 * 4 + i * 4) ∧
      (FullMem c { s with scratch :=
        { s.scratch with scratch_buf := s.scratch.scratch_buf.set (1096 + i.toNat) v } } ⋆ R)
        (storeMem m i32 (c.pScratchBuf + BitVec.ofNat 64 1096 * 4 + i * 4) v) := by
  rw [p6_k_ptr_bv]; exact FullArenaTactics.store_full_scratch_buf v hi hm

@[scoped c0_store] theorem c0_store_p6_scr_nat {cap : Nat} {pk : BitVec 64}
    {scr : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64} {i : Nat} (v : BitVec 32)
    (hi : i < 8192) (hm : (P6Scr cap pk scr ⋆ R) m) :
    storeOk m i32 (pk + BitVec.ofNat 64 (4 * i)) ∧
      (P6Scr cap pk (scr.set i v) ⋆ R) (storeMem m i32 (pk + BitVec.ofNat 64 (4 * i)) v) := by
  rw [P6Scr_eq, sep_pure_l, sep_pure_l] at hm ⊢
  obtain ⟨h8, hlen, ha⟩ := hm
  obtain ⟨hok, hst⟩ := store_array (t := i32) (i := i) v (by decide) (by omega) ha
  exact ⟨hok, h8, by simp [hlen], hst⟩

@[scoped c0_store] theorem c0_store_p6_scr_bv {cap : Nat} {pk : BitVec 64}
    {scr : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64} (v : BitVec 32)
    (hi : i.toNat < 8192) (hm : (P6Scr cap pk scr ⋆ R) m) :
    storeOk m i32 (pk + i * 4) ∧
      (P6Scr cap pk (scr.set i.toNat v) ⋆ R) (storeMem m i32 (pk + i * 4) v) := by
  rw [show pk + i * 4 = pk + BitVec.ofNat 64 (4 * i.toNat) from by
    rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_mul_ofNat]]
  exact c0_store_p6_scr_nat v hi hm

@[scoped c0_store] theorem c0_store_p6_scr_k_bv_lt8192 {cap : Nat} {pk : BitVec 64}
    {scr : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64} (v : BitVec 32)
    (hi : 1096 + i.toNat < 8192) (hm : (P6Scr cap pk scr ⋆ R) m) :
    storeOk m i32 (pk + BitVec.ofNat 64 1096 * 4 + i * 4) ∧
      (P6Scr cap pk (scr.set (1096 + i.toNat) v) ⋆ R)
        (storeMem m i32 (pk + BitVec.ofNat 64 1096 * 4 + i * 4) v) := by
  rw [p6_k_ptr_bv]; rw [P6Scr_eq, sep_pure_l, sep_pure_l] at hm ⊢
  obtain ⟨h8, hlen, ha⟩ := hm
  obtain ⟨hok, hst⟩ := store_array (t := i32) (i := 1096 + i.toNat) v (by decide) (by omega) ha
  exact ⟨hok, h8, by simp [hlen], hst⟩

@[scoped c0_store] theorem c0_store_p6_scr_k_bv {cap : Nat} {pk : BitVec 64}
    {scr : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64} (v : BitVec 32)
    (hi : 1096 + i.toNat < cap) (hm : (P6Scr cap pk scr ⋆ R) m) :
    storeOk m i32 (pk + BitVec.ofNat 64 1096 * 4 + i * 4) ∧
      (P6Scr cap pk (scr.set (1096 + i.toNat) v) ⋆ R)
        (storeMem m i32 (pk + BitVec.ofNat 64 1096 * 4 + i * 4) v) := by
  rw [p6_k_ptr_bv]; rw [P6Scr_eq, sep_pure_l, sep_pure_l] at hm ⊢
  obtain ⟨h8, hlen, ha⟩ := hm
  obtain ⟨hok, hst⟩ := store_array (t := i32) (i := 1096 + i.toNat) v (by decide) (by omega) ha
  exact ⟨hok, h8, by simp [hlen], hst⟩

end P6Tactics

/-! ## 4. Fidelity Scratch/Work State Wrappers & Tactics (`m8ScrSt`, `FidK6cTactics`) -/

@[expose] def m8ScrSt (s : FullState) (scr : List (BitVec 32)) : FullState :=
  { s with scratch := { s.scratch with scratch_buf := scr } }

@[expose] def m8ScrFuelSt (s : FullState) (fl : BitVec 64) (scr : List (BitVec 32)) : FullState :=
  { s with core := { s.core with fuel := fl }
           scratch := { s.scratch with scratch_buf := scr } }

theorem m8ScrSt_eq (s : FullState) (scr : List (BitVec 32)) :
    m8ScrSt s scr = { s with scratch := { s.scratch with scratch_buf := scr } } := rfl
theorem m8ScrSt_self (s : FullState) : m8ScrSt s s.scratch.scratch_buf = s := rfl
theorem m8ScrFuelSt_eq (s : FullState) (fl : BitVec 64) (scr : List (BitVec 32)) :
    m8ScrFuelSt s fl scr =
      { s with core := { s.core with fuel := fl }
               scratch := { s.scratch with scratch_buf := scr } } := rfl
theorem m8ScrFuelSt_self (s : FullState) (scr : List (BitVec 32)) :
    m8ScrFuelSt s s.core.fuel scr = m8ScrSt s scr := rfl
theorem m8ScrSt_lengthsOk {c : FullCfg} {s : FullState} (h : s.LengthsOk c)
    {scr' : List (BitVec 32)} (hscr : scr'.length = c.scratch_cap) :
    (m8ScrSt s scr').LengthsOk c :=
  ⟨h.core_ok, { h.scratch_ok with scratch_buf_len := hscr }⟩
theorem m8ScrFuelSt_lengthsOk {c : FullCfg} {s : FullState} (h : s.LengthsOk c)
    {scr' : List (BitVec 32)} (hscr : scr'.length = c.scratch_cap) (fl' : BitVec 64) :
    (m8ScrFuelSt s fl' scr').LengthsOk c :=
  ⟨{ h.core_ok with arena_len_le := h.core_ok.arena_len_le },
    { h.scratch_ok with scratch_buf_len := hscr }⟩
theorem m8ScrSt_upd (s : FullState) (scr scr' : List (BitVec 32)) :
    { m8ScrSt s scr with scratch := { (m8ScrSt s scr).scratch with scratch_buf := scr' } } =
      m8ScrSt s scr' := rfl
theorem m8ScrFuelSt_upd (s : FullState) (fl : BitVec 64) (scr scr' : List (BitVec 32)) :
    { m8ScrFuelSt s fl scr with
        scratch := { (m8ScrFuelSt s fl scr).scratch with scratch_buf := scr' } } =
      m8ScrFuelSt s fl scr' := rfl
theorem m8ScrFuelSt_upd_fuel (s : FullState) (fl fl' : BitVec 64) (scr : List (BitVec 32)) :
    { m8ScrFuelSt s fl scr with core := { (m8ScrFuelSt s fl scr).core with fuel := fl' } } =
      m8ScrFuelSt s fl' scr := rfl
theorem m8ScrSt_buf (s : FullState) (scr : List (BitVec 32)) :
    (m8ScrSt s scr).scratch.scratch_buf = scr := rfl
theorem m8ScrFuelSt_buf (s : FullState) (fl : BitVec 64) (scr : List (BitVec 32)) :
    (m8ScrFuelSt s fl scr).scratch.scratch_buf = scr := rfl
theorem m8ScrFuelSt_fuel (s : FullState) (fl : BitVec 64) (scr : List (BitVec 32)) :
    (m8ScrFuelSt s fl scr).core.fuel = fl := rfl

namespace M8K6bTactics

attribute [scoped bv_c0 high] bv_c0_zext32_64
attribute [scoped bv_c0] bv32_lshr_1 bv32_and_1 bv32_xor_1 List.length_set Bool.false_eq_true

@[scoped bv_c0] theorem m8k6_bv32_shl1 (x : BitVec 32) :
    (x <<< (1 : Nat)).toNat = (2 * x.toNat) % 2 ^ 32 := by
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm]

@[scoped bv_c0] theorem m8k6_bv32_shl1_or1 (x : BitVec 32) :
    ((x <<< (1 : Nat)) ||| (1 : BitVec 32)).toNat = (2 * x.toNat + 1) % 2 ^ 32 :=
  K6Tactics.k6_bv32_shl1_or1 x

@[scoped c0_load] theorem c0_load_m8ScrSt_ptr {c : FullCfg} {s : FullState}
    {scr : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem c (m8ScrSt s scr) ⋆ R) m) :
    loadVal m i64 (c.hdr + 920) = some c.pScratchBuf :=
  FullArenaTactics.load_full_scratch_buf_ptr hm

@[scoped c0_load] theorem c0_load_m8ScrSt_imm {c : FullCfg} {s : FullState}
    {scr : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64} {k : Nat}
    (hk : k < 15744) (hlen : 15744 ≤ scr.length)
    (hm : (FullMem c (m8ScrSt s scr) ⋆ R) m) :
    loadVal m i32 (c.pScratchBuf + BitVec.ofNat 64 k * 4) = some (scr[k]'(by omega)) := by
  have hk_eq : (BitVec.ofNat 64 k).toNat = k := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h1 := FullArenaTactics.c0_load_full_scratch_buf (i := BitVec.ofNat 64 k)
    (by rw [m8ScrSt_buf, hk_eq]; omega) hm
  simpa only [m8ScrSt_buf, hk_eq] using h1

@[scoped c0_load] theorem c0_load_m8ScrSt {c : FullCfg} {s : FullState}
    {scr : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64}
    (hi : i.toNat < scr.length) (hm : (FullMem c (m8ScrSt s scr) ⋆ R) m) :
    loadVal m i32 (c.pScratchBuf + i * 4) = some scr[i.toNat] := by
  simpa only [m8ScrSt_buf] using
    FullArenaTactics.c0_load_full_scratch_buf (i := i) (by rw [m8ScrSt_buf]; exact hi) hm

@[scoped c0_store] theorem c0_store_m8ScrSt_imm {c : FullCfg} {s : FullState}
    {scr : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64} {k : Nat} (v : BitVec 32)
    (hk : k < 15744) (hlen : 15744 ≤ scr.length)
    (hm : (FullMem c (m8ScrSt s scr) ⋆ R) m) :
    storeOk m i32 (c.pScratchBuf + BitVec.ofNat 64 k * 4) ∧
      (FullMem c (m8ScrSt s (scr.set k v)) ⋆ R)
        (storeMem m i32 (c.pScratchBuf + BitVec.ofNat 64 k * 4) v) := by
  have hk_eq : (BitVec.ofNat 64 k).toNat = k := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h1 := FullArenaTactics.c0_store_full_scratch_buf (i := BitVec.ofNat 64 k) v
    (by rw [m8ScrSt_buf, hk_eq]; omega) hm
  simpa only [m8ScrSt_buf, m8ScrSt_upd, hk_eq] using h1

@[scoped c0_store] theorem c0_store_m8ScrSt {c : FullCfg} {s : FullState}
    {scr : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64} (v : BitVec 32)
    (hi : i.toNat < scr.length) (hm : (FullMem c (m8ScrSt s scr) ⋆ R) m) :
    storeOk m i32 (c.pScratchBuf + i * 4) ∧
      (FullMem c (m8ScrSt s (scr.set i.toNat v)) ⋆ R)
        (storeMem m i32 (c.pScratchBuf + i * 4) v) := by
  simpa only [m8ScrSt_buf, m8ScrSt_upd] using
    FullArenaTactics.c0_store_full_scratch_buf (i := i) v (by rw [m8ScrSt_buf]; exact hi) hm

@[scoped c0_load] theorem c0_load_m8ScrFuelSt_ptr {c : FullCfg} {s : FullState}
    {fl : BitVec 64} {scr : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem c (m8ScrFuelSt s fl scr) ⋆ R) m) :
    loadVal m i64 (c.hdr + 920) = some c.pScratchBuf :=
  FullArenaTactics.load_full_scratch_buf_ptr hm

@[scoped c0_load] theorem c0_load_m8ScrFuelSt_fuel {c : FullCfg} {s : FullState}
    {fl : BitVec 64} {scr : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem c (m8ScrFuelSt s fl scr) ⋆ R) m) :
    loadVal m i64 (c.hdr + 168) = some fl := by
  simpa only [m8ScrFuelSt_fuel] using FullArenaTactics.load_full_fuel hm

@[scoped c0_store] theorem c0_store_m8ScrFuelSt_fuel {c : FullCfg} {s : FullState}
    {fl : BitVec 64} {scr : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 64)
    (hm : (FullMem c (m8ScrFuelSt s fl scr) ⋆ R) m) :
    storeOk m i64 (c.hdr + 168) ∧
      (FullMem c (m8ScrFuelSt s v scr) ⋆ R) (storeMem m i64 (c.hdr + 168) v) := by
  simpa only [m8ScrFuelSt_upd_fuel] using FullArenaTactics.store_full_fuel v hm

@[scoped c0_load] theorem c0_load_m8ScrFuelSt_imm {c : FullCfg} {s : FullState}
    {fl : BitVec 64} {scr : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64} {k : Nat}
    (hk : k < 15744) (hlen : 15744 ≤ scr.length)
    (hm : (FullMem c (m8ScrFuelSt s fl scr) ⋆ R) m) :
    loadVal m i32 (c.pScratchBuf + BitVec.ofNat 64 k * 4) = some (scr[k]'(by omega)) := by
  have hk_eq : (BitVec.ofNat 64 k).toNat = k := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h1 := FullArenaTactics.c0_load_full_scratch_buf (i := BitVec.ofNat 64 k)
    (by rw [m8ScrFuelSt_buf, hk_eq]; omega) hm
  simpa only [m8ScrFuelSt_buf, hk_eq] using h1

@[scoped c0_load] theorem c0_load_m8ScrFuelSt {c : FullCfg} {s : FullState}
    {fl : BitVec 64} {scr : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64}
    (hi : i.toNat < scr.length) (hm : (FullMem c (m8ScrFuelSt s fl scr) ⋆ R) m) :
    loadVal m i32 (c.pScratchBuf + i * 4) = some scr[i.toNat] := by
  simpa only [m8ScrFuelSt_buf] using
    FullArenaTactics.c0_load_full_scratch_buf (i := i) (by rw [m8ScrFuelSt_buf]; exact hi) hm

@[scoped c0_store] theorem c0_store_m8ScrFuelSt_imm {c : FullCfg} {s : FullState}
    {fl : BitVec 64} {scr : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64} {k : Nat}
    (v : BitVec 32) (hk : k < 15744) (hlen : 15744 ≤ scr.length)
    (hm : (FullMem c (m8ScrFuelSt s fl scr) ⋆ R) m) :
    storeOk m i32 (c.pScratchBuf + BitVec.ofNat 64 k * 4) ∧
      (FullMem c (m8ScrFuelSt s fl (scr.set k v)) ⋆ R)
        (storeMem m i32 (c.pScratchBuf + BitVec.ofNat 64 k * 4) v) := by
  have hk_eq : (BitVec.ofNat 64 k).toNat = k := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h1 := FullArenaTactics.c0_store_full_scratch_buf (i := BitVec.ofNat 64 k) v
    (by rw [m8ScrFuelSt_buf, hk_eq]; omega) hm
  simpa only [m8ScrFuelSt_buf, m8ScrFuelSt_upd, hk_eq] using h1

@[scoped c0_store] theorem c0_store_m8ScrFuelSt {c : FullCfg} {s : FullState}
    {fl : BitVec 64} {scr : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64}
    (v : BitVec 32) (hi : i.toNat < scr.length)
    (hm : (FullMem c (m8ScrFuelSt s fl scr) ⋆ R) m) :
    storeOk m i32 (c.pScratchBuf + i * 4) ∧
      (FullMem c (m8ScrFuelSt s fl (scr.set i.toNat v)) ⋆ R)
        (storeMem m i32 (c.pScratchBuf + i * 4) v) := by
  simpa only [m8ScrFuelSt_buf, m8ScrFuelSt_upd] using
    FullArenaTactics.c0_store_full_scratch_buf (i := i) v (by rw [m8ScrFuelSt_buf]; exact hi) hm

end M8K6bTactics

abbrev FidP6Scr (s : FullState) (scr' : List (BitVec 32)) : FullState :=
  { s with scratch := { s.scratch with scratch_buf := scr' } }

abbrev FidP6Work (s : FullState)
    (tmp' wsort' tmk' scr' : List (BitVec 32)) : FullState :=
  { s with
    core := { s.core with tmp := tmp' }
    scratch := { s.scratch with wsort := wsort', tarjan_mark := tmk', scratch_buf := scr' } }

theorem fid_k6c_work_self (s : FullState) :
    FidP6Work s s.core.tmp s.scratch.wsort s.scratch.tarjan_mark
      s.scratch.scratch_buf = s := rfl

theorem fid_k6c_scr_self (s : FullState) :
    FidP6Scr s s.scratch.scratch_buf = s := rfl

theorem fid_k6c_work_to_scr (s : FullState) (tmp' wsort' tmk' scr' : List (BitVec 32)) :
    FidP6Work s tmp' wsort' tmk' scr' =
      FidP6Scr (FidP6Work s tmp' wsort' tmk' s.scratch.scratch_buf) scr' := rfl

theorem fid_k6c_scrBuf_split {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (h : (FullMem c s ⋆ R) m) :
    (FullMem c (FidP6Scr s s.scratch.scratch_buf) ⋆ R) m := by
  rwa [fid_k6c_scr_self]

theorem fid_k6c_scrBuf_unsplit {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {scr' : List (BitVec 32)} (h : (FullMem c (FidP6Scr s scr') ⋆ R) m)
    (heq : scr' = s.scratch.scratch_buf) :
    (FullMem c s ⋆ R) m := by
  subst heq; rwa [fid_k6c_scr_self] at h

theorem fid_k6c_fullMem_subst {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {scr1 scr2 : List (BitVec 32)} (heq : scr1 = scr2)
    (h : (FullMem c (FidP6Scr s scr1) ⋆ R) m) :
    (FullMem c (FidP6Scr s scr2) ⋆ R) m := heq ▸ h

theorem fid_k6c_workMem_subst {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {tmp1 tmp2 w1 w2 t1 t2 scr1 scr2 : List (BitVec 32)}
    (ht : tmp1 = tmp2) (hw : w1 = w2) (htm : t1 = t2) (hs : scr1 = scr2)
    (h : (FullMem c (FidP6Work s tmp1 w1 t1 scr1) ⋆ R) m) :
    (FullMem c (FidP6Work s tmp2 w2 t2 scr2) ⋆ R) m := by
  subst ht hw htm hs; exact h

theorem fid_k6c_work_lengthsOk {c : FullCfg} {s : FullState}
    {tmp' wsort' tmk' scr' : List (BitVec 32)}
    (hl : s.LengthsOk c) (ht : tmp'.length = c.max_vars)
    (hw : wsort'.length = 2 * c.max_vars) (htm : tmk'.length = 2 * c.max_vars)
    (hs : scr'.length = c.scratch_cap) :
    (FidP6Work s tmp' wsort' tmk' scr').LengthsOk c :=
  ⟨{ hl.core_ok with tmp_len_arr := ht },
   { hl.scratch_ok with wsort_len := hw, tarjan_mark_len := htm, scratch_buf_len := hs }⟩

theorem fid_k6c_fullDenseInvW_work {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState}
    {tmp' wsort' tmk' scr' : List (BitVec 32)}
    (hi : FullDenseInvW c F0 F_cur s) (ht : tmp'.length = c.max_vars)
    (hw : wsort'.length = 2 * c.max_vars) (htm : tmk'.length = 2 * c.max_vars)
    (hs : scr'.length = c.scratch_cap) :
    FullDenseInvW c F0 F_cur (FidP6Work s tmp' wsort' tmk' scr') :=
  m8_fullDenseInvW_def hi ht hw htm hs

namespace FidK6cTactics

@[scoped c0_load] theorem c0_load_fid_scr {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {scr : List (BitVec 32)} {i : BitVec 64}
    (hi : i.toNat < scr.length) (hm : (FullMem c (FidP6Scr s scr) ⋆ R) m) :
    loadVal m i32 (c.pScratchBuf + i * 4) = some scr[i.toNat] :=
  FullArenaTactics.c0_load_full_scratch_buf (s := FidP6Scr s scr) hi hm

@[scoped c0_store] theorem c0_store_fid_scr {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {scr : List (BitVec 32)} {i : BitVec 64}
    (v : BitVec 32) (hi : i.toNat < scr.length)
    (hm : (FullMem c (FidP6Scr s scr) ⋆ R) m) :
    storeOk m i32 (c.pScratchBuf + i * 4) ∧
      (FullMem c (FidP6Scr s (scr.set i.toNat v)) ⋆ R)
        (storeMem m i32 (c.pScratchBuf + i * 4) v) :=
  FullArenaTactics.c0_store_full_scratch_buf (s := FidP6Scr s scr) v hi hm

@[scoped c0_load] theorem c0_load_fid_w_scr {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {tmp wsort tmk scr : List (BitVec 32)} {i : BitVec 64}
    (hi : i.toNat < scr.length)
    (hm : (FullMem c (FidP6Work s tmp wsort tmk scr) ⋆ R) m) :
    loadVal m i32 (c.pScratchBuf + i * 4) = some scr[i.toNat] :=
  FullArenaTactics.c0_load_full_scratch_buf (s := FidP6Work s tmp wsort tmk scr) hi hm

@[scoped c0_store] theorem c0_store_fid_w_scr {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {tmp wsort tmk scr : List (BitVec 32)} {i : BitVec 64}
    (v : BitVec 32) (hi : i.toNat < scr.length)
    (hm : (FullMem c (FidP6Work s tmp wsort tmk scr) ⋆ R) m) :
    storeOk m i32 (c.pScratchBuf + i * 4) ∧
      (FullMem c (FidP6Work s tmp wsort tmk (scr.set i.toNat v)) ⋆ R)
        (storeMem m i32 (c.pScratchBuf + i * 4) v) :=
  FullArenaTactics.c0_store_full_scratch_buf (s := FidP6Work s tmp wsort tmk scr) v hi hm

@[scoped c0_load] theorem c0_load_fid_w_tmk {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {tmp wsort tmk scr : List (BitVec 32)} {i : BitVec 64}
    (hi : i.toNat < tmk.length)
    (hm : (FullMem c (FidP6Work s tmp wsort tmk scr) ⋆ R) m) :
    loadVal m i32 (c.pTarjanMark + i * 4) = some tmk[i.toNat] :=
  FullArenaTactics.c0_load_full_tarjan_mark (s := FidP6Work s tmp wsort tmk scr) hi hm

@[scoped c0_store] theorem c0_store_fid_w_tmk {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {tmp wsort tmk scr : List (BitVec 32)} {i : BitVec 64}
    (v : BitVec 32) (hi : i.toNat < tmk.length)
    (hm : (FullMem c (FidP6Work s tmp wsort tmk scr) ⋆ R) m) :
    storeOk m i32 (c.pTarjanMark + i * 4) ∧
      (FullMem c (FidP6Work s tmp wsort (tmk.set i.toNat v) scr) ⋆ R)
        (storeMem m i32 (c.pTarjanMark + i * 4) v) :=
  FullArenaTactics.c0_store_full_tarjan_mark (s := FidP6Work s tmp wsort tmk scr) v hi hm

@[scoped c0_load] theorem c0_load_fid_w_wsort {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {tmp wsort tmk scr : List (BitVec 32)} {i : BitVec 64}
    (hi : i.toNat < wsort.length)
    (hm : (FullMem c (FidP6Work s tmp wsort tmk scr) ⋆ R) m) :
    loadVal m i32 (c.pWsort + i * 4) = some wsort[i.toNat] :=
  FullArenaTactics.c0_load_full_wsort (s := FidP6Work s tmp wsort tmk scr) hi hm

@[scoped c0_store] theorem c0_store_fid_w_wsort {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {tmp wsort tmk scr : List (BitVec 32)} {i : BitVec 64}
    (v : BitVec 32) (hi : i.toNat < wsort.length)
    (hm : (FullMem c (FidP6Work s tmp wsort tmk scr) ⋆ R) m) :
    storeOk m i32 (c.pWsort + i * 4) ∧
      (FullMem c (FidP6Work s tmp (wsort.set i.toNat v) tmk scr) ⋆ R)
        (storeMem m i32 (c.pWsort + i * 4) v) :=
  FullArenaTactics.c0_store_full_wsort (s := FidP6Work s tmp wsort tmk scr) v hi hm

@[scoped c0_load] theorem c0_load_fid_w_tmp {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {tmp wsort tmk scr : List (BitVec 32)} {i : BitVec 64}
    (hi : i.toNat < tmp.length)
    (hm : (FullMem c (FidP6Work s tmp wsort tmk scr) ⋆ R) m) :
    loadVal m i32 (c.pTmp + i * 4) = some tmp[i.toNat] :=
  FullArenaTactics.c0_load_full_tmp (s := FidP6Work s tmp wsort tmk scr) hi hm

@[scoped c0_store] theorem c0_store_fid_w_tmp {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {tmp wsort tmk scr : List (BitVec 32)} {i : BitVec 64}
    (v : BitVec 32) (hi : i.toNat < tmp.length)
    (hm : (FullMem c (FidP6Work s tmp wsort tmk scr) ⋆ R) m) :
    storeOk m i32 (c.pTmp + i * 4) ∧
      (FullMem c (FidP6Work s (tmp.set i.toNat v) wsort tmk scr) ⋆ R)
        (storeMem m i32 (c.pTmp + i * 4) v) :=
  FullArenaTactics.c0_store_full_tmp (s := FidP6Work s tmp wsort tmk scr) v hi hm

@[scoped c0_load] theorem c0_load_fid_w_arena {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {tmp wsort tmk scr : List (BitVec 32)} {i : BitVec 64}
    (hi : i.toNat < s.core.arena.length)
    (hm : (FullMem c (FidP6Work s tmp wsort tmk scr) ⋆ R) m) :
    loadVal m i32 (c.pArena + i * 4) = some s.core.arena[i.toNat] :=
  FullArenaTactics.c0_load_full_arena (s := FidP6Work s tmp wsort tmk scr) hi hm

@[scoped c0_load] theorem c0_load_fid_w_vals {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {tmp wsort tmk scr : List (BitVec 32)} {i : BitVec 64}
    (hi : i.toNat < s.core.vals.length)
    (hm : (FullMem c (FidP6Work s tmp wsort tmk scr) ⋆ R) m) :
    loadVal m i8 (c.pVals + i) = some s.core.vals[i.toNat] :=
  FullArenaTactics.c0_load_full_vals (s := FidP6Work s tmp wsort tmk scr) hi hm

@[scoped c0_store] theorem c0_store_fid_scr_nat {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {scr : List (BitVec 32)} {n : Nat}
    (v : BitVec 32) (hn : n < scr.length) (hn64 : n < 2 ^ 30)
    (hm : (FullMem c (FidP6Scr s scr) ⋆ R) m) :
    storeOk m i32 (c.pScratchBuf +
      BitVec.ofNat (@OfNat.ofNat Nat 64 (instOfNatNat 64))
        (@OfNat.ofNat Nat n (instOfNatNat n)) * 4) ∧
      (FullMem c (FidP6Scr s (scr.set n v)) ⋆ R)
        (storeMem m i32 (c.pScratchBuf +
          BitVec.ofNat (@OfNat.ofNat Nat 64 (instOfNatNat 64))
            (@OfNat.ofNat Nat n (instOfNatNat n)) * 4) v) := by
  have hi : (BitVec.ofNat 64 n).toNat < scr.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hn
  have h := c0_store_fid_scr (i := BitVec.ofNat 64 n) v hi hm
  change storeOk m i32 (c.pScratchBuf + BitVec.ofNat 64 n * 4) ∧
    (FullMem c (FidP6Scr s (scr.set (BitVec.ofNat 64 n).toNat v)) ⋆ R)
      (storeMem m i32 (c.pScratchBuf + BitVec.ofNat 64 n * 4) v) at h
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h
  exact h

@[scoped c0_store] theorem c0_store_fid_w_scr_nat {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {tmp wsort tmk scr : List (BitVec 32)} {n : Nat}
    (v : BitVec 32) (hn : n < scr.length) (hn64 : n < 2 ^ 30)
    (hm : (FullMem c (FidP6Work s tmp wsort tmk scr) ⋆ R) m) :
    storeOk m i32 (c.pScratchBuf +
      BitVec.ofNat (@OfNat.ofNat Nat 64 (instOfNatNat 64))
        (@OfNat.ofNat Nat n (instOfNatNat n)) * 4) ∧
      (FullMem c (FidP6Work s tmp wsort tmk (scr.set n v)) ⋆ R)
        (storeMem m i32 (c.pScratchBuf +
          BitVec.ofNat (@OfNat.ofNat Nat 64 (instOfNatNat 64))
            (@OfNat.ofNat Nat n (instOfNatNat n)) * 4) v) := by
  have hi : (BitVec.ofNat 64 n).toNat < scr.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hn
  have h := c0_store_fid_w_scr (i := BitVec.ofNat 64 n) v hi hm
  change storeOk m i32 (c.pScratchBuf + BitVec.ofNat 64 n * 4) ∧
    (FullMem c (FidP6Work s tmp wsort tmk (scr.set (BitVec.ofNat 64 n).toNat v)) ⋆ R)
      (storeMem m i32 (c.pScratchBuf + BitVec.ofNat 64 n * 4) v) at h
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h
  exact h

@[scoped c0_store] theorem c0_store_fid_w_wsort_nat {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {tmp wsort tmk scr : List (BitVec 32)} {n : Nat}
    (v : BitVec 32) (hn : n < wsort.length) (hn64 : n < 2 ^ 30)
    (hm : (FullMem c (FidP6Work s tmp wsort tmk scr) ⋆ R) m) :
    storeOk m i32 (c.pWsort + BitVec.ofNat 64 n * 4) ∧
      (FullMem c (FidP6Work s tmp (wsort.set n v) tmk scr) ⋆ R)
        (storeMem m i32 (c.pWsort + BitVec.ofNat 64 n * 4) v) := by
  have hi : (BitVec.ofNat 64 n).toNat < wsort.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hn
  have h := c0_store_fid_w_wsort (i := BitVec.ofNat 64 n) v hi hm
  change storeOk m i32 (c.pWsort + BitVec.ofNat 64 n * 4) ∧
    (FullMem c (FidP6Work s tmp (wsort.set (BitVec.ofNat 64 n).toNat v) tmk scr) ⋆ R)
      (storeMem m i32 (c.pWsort + BitVec.ofNat 64 n * 4) v) at h
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h
  exact h

@[scoped c0_store] theorem c0_store_fid_w_tmk_nat {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {tmp wsort tmk scr : List (BitVec 32)} {n : Nat}
    (v : BitVec 32) (hn : n < tmk.length) (hn64 : n < 2 ^ 30)
    (hm : (FullMem c (FidP6Work s tmp wsort tmk scr) ⋆ R) m) :
    storeOk m i32 (c.pTarjanMark + BitVec.ofNat 64 n * 4) ∧
      (FullMem c (FidP6Work s tmp wsort (tmk.set n v) scr) ⋆ R)
        (storeMem m i32 (c.pTarjanMark + BitVec.ofNat 64 n * 4) v) := by
  have hi : (BitVec.ofNat 64 n).toNat < tmk.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hn
  have h := c0_store_fid_w_tmk (i := BitVec.ofNat 64 n) v hi hm
  change storeOk m i32 (c.pTarjanMark + BitVec.ofNat 64 n * 4) ∧
    (FullMem c (FidP6Work s tmp wsort (tmk.set (BitVec.ofNat 64 n).toNat v) scr) ⋆ R)
      (storeMem m i32 (c.pTarjanMark + BitVec.ofNat 64 n * 4) v) at h
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h
  exact h

end FidK6cTactics

end

end LeanQbe.T.Examples.Kissat.Proof.Definition
