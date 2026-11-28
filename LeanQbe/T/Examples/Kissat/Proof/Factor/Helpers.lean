/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Factor.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts4
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics1
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Shared Proof Helpers for `Kissat.Proof.Factor`

Architecture-free (`0` legacy imports) BitVec, list, arena-block, dense-watch, and
`FidBvaMatrixInv` preservation helpers shared across `Proof/Factor/Wp*.lean`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Factor

public section

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.C0Step LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Spec.FullBvaHeapHelpers
open LeanQbe.T.Examples.Kissat.Proof.Factor.Spec
open Kraken.Bedrock2.Test

/-! ## 1. BitVec & Arithmetic Helpers -/

theorem fid_bv64_32 (x : BitVec 32) : (BitVec.setWidth 64 x).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (lt_trans (BitVec.isLt x) (by decide))

theorem fid_bv64_add1 {x : BitVec 64} (h : x.toNat + 1 < 2 ^ 64) :
    (x + 1#64).toNat = x.toNat + 1 := by
  rw [BitVec.toNat_add, show (1#64 : BitVec 64).toNat = 1 from rfl, Nat.mod_eq_of_lt h]

theorem fid_bv64_add2 {x : BitVec 64} (h : x.toNat + 2 < 2 ^ 64) :
    (x + 2#64).toNat = x.toNat + 2 := by
  rw [BitVec.toNat_add, show (2#64 : BitVec 64).toNat = 2 from rfl, Nat.mod_eq_of_lt h]

theorem fid_bv32_add1 {x : BitVec 32} (h : x.toNat + 1 < 2 ^ 32) :
    (x + 1#32).toNat = x.toNat + 1 := by
  rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl, Nat.mod_eq_of_lt h]

theorem fid_bv64_trunc32 {x : BitVec 64} (h : x.toNat < 2 ^ 32) :
    (x.setWidth 32).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt h]

theorem fid_bv64_add3_u32 {p : BitVec 64} {k : BitVec 32}
    (h : p.toNat + 3 + k.toNat < 2 ^ 64) :
    (p + 3#64 + BitVec.setWidth 64 k).toNat = p.toNat + 3 + k.toNat := by
  rw [BitVec.toNat_add, BitVec.toNat_add, fid_bv64_32,
    show (3#64 : BitVec 64).toNat = 3 from rfl,
    Nat.mod_eq_of_lt (by omega : p.toNat + 3 < 2 ^ 64), Nat.mod_eq_of_lt h]

theorem fid_bv32_ne_sent {x : BitVec 32} (h : x.toNat < 2 ^ 31) : x ≠ 0xFFFFFFFF#32 :=
  fun he => by have := congrArg BitVec.toNat he; simp at this; omega

theorem fid_bv32_bin_flag_zero_of_lt {x : BitVec 32} (h : x.toNat < 2 ^ 31) :
    (x &&& 0x80000000#32) = 0#32 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (0x80000000#32).toNat = 2 ^ 31 from rfl,
    show (0#32).toNat = 0 from rfl]
  apply Nat.eq_of_testBit_eq; intro k
  rw [Nat.testBit_and, Nat.zero_testBit, Nat.testBit_two_pow]
  by_cases hk : k = 31
  · subst hk; simp [Nat.testBit_lt_two_pow h]
  · simp [Ne.symm hk]

theorem fid_bv32_garb_zero_of_and_480000 {x : BitVec 32}
    (h : (x &&& 0x00480000#32) = 0#32) : (x &&& 0x00080000#32) = 0#32 := by
  have h1 := congrArg (· &&& 0x00080000#32) h
  rw [BitVec.and_assoc, show (0x00480000#32 &&& 0x00080000#32) = 0x00080000#32 from rfl,
    BitVec.zero_and] at h1
  exact h1

theorem fid_bv32_garb_zero_of_and_02480000 {x : BitVec 32}
    (h : (x &&& 0x02480000#32) = 0#32) : (x &&& 0x00080000#32) = 0#32 := by
  have h1 := congrArg (· &&& 0x00080000#32) h
  rw [BitVec.and_assoc, show (0x02480000#32 &&& 0x00080000#32) = 0x00080000#32 from rfl,
    BitVec.zero_and] at h1
  exact h1

theorem fid_bv32_bvaq_zero_of_and_02480000 {x : BitVec 32}
    (h : (x &&& 0x02480000#32) = 0#32) : (x &&& 0x02000000#32) = 0#32 := by
  have h1 := congrArg (· &&& 0x02000000#32) h
  rw [BitVec.and_assoc, show (0x02480000#32 &&& 0x02000000#32) = 0x02000000#32 from rfl,
    BitVec.zero_and] at h1
  exact h1

theorem fid_bv32_and_7fff_lt (x : BitVec 32) :
    (x &&& (2147483647 : BitVec 32)).toNat < 2 ^ 31 := by
  rw [BitVec.toNat_and, show ((2147483647 : BitVec 32)).toNat = 2 ^ 31 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt _ (by decide)

theorem bv32_sub1_ushr1 {p : BitVec 32} (h : 0 < p.toNat) :
    ((p - (1 : BitVec 32)) >>> (1 : BitVec 32)).toNat = (p.toNat - 1) / 2 := by
  simp [BitVec.toNat_ushiftRight, BitVec.toNat_sub, Nat.shiftRight_eq_div_pow]; omega

theorem bv32_shl1_add1 {p : BitVec 32} (h : p.toNat < 2 ^ 30) :
    ((p <<< (1 : BitVec 32)) + (1 : BitVec 32)).toNat = 2 * p.toNat + 1 := by
  simp [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega

theorem bv32_shl1_add2 {p : BitVec 32} (h : p.toNat < 2 ^ 30) :
    (((p <<< (1 : BitVec 32)) + (1 : BitVec 32)) + (1 : BitVec 32)).toNat = 2 * p.toNat + 2 := by
  simp [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega

theorem bv32_lshr1_nat (x : BitVec 32) : (x >>> (1 : Nat)).toNat = x.toNat / 2 :=
  bv32_lshr_1 x

theorem s9_bv32_add1 {x : BitVec 32} (h : x.toNat + 1 < 2 ^ 32) :
    (x + 1#32).toNat = x.toNat + 1 :=
  fid_bv32_add1 h

theorem s9_bv32_sub1 {x : BitVec 32} (h : 0 < x.toNat) :
    (x - 1#32).toNat = x.toNat - 1 := by
  have hle : (1#32 : BitVec 32).toNat ≤ x.toNat := h
  rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr hle)]; rfl

private theorem testBit_two_pow_pred : ∀ (n i : Nat), i < n →
    Nat.testBit (2 ^ n - 1) i = true
  | 0, _, hi => absurd hi (by omega)
  | n + 1, 0, _ => by
    rw [Nat.testBit_zero, decide_eq_true_eq, Nat.pow_succ]
    have := @Nat.one_le_two_pow n; omega
  | n + 1, i + 1, hi => by
    rw [Nat.testBit_succ]
    have hdiv : (2 ^ (n + 1) - 1) / 2 = 2 ^ n - 1 := by
      rw [Nat.pow_succ]; have := @Nat.one_le_two_pow n; omega
    rw [hdiv]; exact testBit_two_pow_pred n i (by omega)

theorem bv64_pack32_hi (hsz tl : BitVec 32) :
    BitVec.setWidth 32
      (((BitVec.setWidth 64 hsz <<< (32 : Nat)) ||| BitVec.setWidth 64 tl) >>> (32 : Nat)) =
    hsz := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have h1 : ¬ (32 + i < 32) := by omega
  have h2 : 32 + i < 64 := by omega
  have h3 : i < 64 := by omega
  simp [hi, h1, h2, h3]

theorem bv64_pack32_lo (hsz tl : BitVec 32) :
    BitVec.setWidth 32
      (((BitVec.setWidth 64 hsz <<< (32 : Nat)) ||| BitVec.setWidth 64 tl) &&&
        (4294967295 : BitVec 64)) = tl := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have h1 : i < 64 := by omega
  have htb : Nat.testBit 4294967295 i = true := testBit_two_pow_pred 32 i hi
  rw [show (4294967295 : BitVec 64) = BitVec.ofNat 64 4294967295 from rfl]
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_and, BitVec.getLsbD_or,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ofNat, hi, h1, htb, decide_true,
    Bool.true_and, Bool.not_true, Bool.false_and, Bool.false_or, Bool.and_true]

/-! ## 2. Arena, List, and Dense-Watch Helpers -/

theorem take_succ_filter_eq {l : List Nat} {i : Nat} {x : Nat} (hi : i < l.length) :
    (l.take (i + 1)).filter (· != x) =
      (l.take i).filter (· != x) ++ if l[i] != x then [l[i]] else [] := by
  rw [List.take_succ_eq_append_getElem hi, List.filter_append, List.filter_cons, List.filter_nil]

theorem fullArenaClauseLitsCore_getElem {k : FullCoreState} {r j : Nat}
    (hj : j < fullArenaClauseSizeCore k r) (hb : r + 3 + j < k.arena.length) :
    (fullArenaClauseLitsCore k r)[j]? = some (k.arena[r + 3 + j]'hb).toNat := by
  unfold fullArenaClauseLitsCore
  rw [List.getElem?_map, List.getElem?_take_of_lt hj, List.getElem?_drop,
    List.getElem?_eq_getElem hb, Option.map_some]

theorem fullArenaClauseLitsCore_length {k : FullCoreState} {r : Nat}
    (hb : r + 3 + fullArenaClauseSizeCore k r ≤ k.arena.length) :
    (fullArenaClauseLitsCore k r).length = fullArenaClauseSizeCore k r := by
  unfold fullArenaClauseLitsCore; simp only [List.length_map, List.length_take, List.length_drop]
  omega

theorem fullArenaScanRefs_next_mem {ar : List (BitVec 32)} {alen : Nat} :
    ∀ {fuel pos r : Nat}, alen - pos ≤ fuel →
      r ∈ fullArenaScanRefs ar alen pos fuel →
      (fullArenaNextOff ar alen r = alen ∨ fullArenaNextOff ar alen r + 3 ≤ alen) →
      fullArenaNextOff ar alen r = alen ∨
        fullArenaNextOff ar alen r ∈ fullArenaScanRefs ar alen pos fuel
  | 0, _, _, _, hr, _ => by simp [fullArenaScanRefs] at hr
  | fuel + 1, pos, r, hfl, hr, hch => by
    unfold fullArenaScanRefs at hr ⊢
    split at hr
    · rename_i hle
      simp only [hle, ↓reduceIte, List.mem_cons] at hr ⊢
      have hnb := fullArenaNextOff_bounds (ar := ar) (alen := alen) (cref := pos) hle
      rcases hr with rfl | hrest
      · rcases hch with he | h3
        · exact Or.inl he
        · refine Or.inr (Or.inr ?_)
          cases fuel with
          | zero => omega
          | succ f' => simp [fullArenaScanRefs, h3]
      · rcases fullArenaScanRefs_next_mem (by omega) hrest hch with he | hm
        · exact Or.inl he
        · exact Or.inr (Or.inr hm)
    · simp at hr

theorem fullArenaClauseRefs_next_mem {c : FullCfg} {F_cur : List (List Nat)} {k : FullCoreState}
    (ha : FullArenaClausesInv c F_cur k) {r : Nat} (hr : r ∈ fullArenaClauseRefsCore k) :
    fullArenaNextOff k.arena k.arena_len r = k.arena_len ∨
      fullArenaNextOff k.arena k.arena_len r ∈ fullArenaClauseRefsCore k :=
  fullArenaScanRefs_next_mem (by omega) hr (ha.refs_wf r hr).2.2.2.2

theorem denseWatchSliceOk_step {F_cur : List (List Nat)} {k : FullCoreState}
    {lit p rem : Nat} (h : DenseWatchSliceOk F_cur k lit p rem) (hpos : 0 < rem) :
    (∃ w0, k.wstk[p]? = some w0 ∧ (w0 &&& 0x80000000#32) ≠ 0#32 ∧ w0 ≠ 0xFFFFFFFF#32 ∧
      (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k.cur_vars ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause [lit, (w0 &&& 0x7FFFFFFF#32).toNat]) ∧
      DenseWatchSliceOk F_cur k lit (p + 1) (rem - 1)) ∨
    (∃ w0 cr, 2 ≤ rem ∧ k.wstk[p]? = some w0 ∧ k.wstk[p + 1]? = some cr ∧
      (w0 &&& 0x80000000#32) = 0#32 ∧ 3 ≤ w0.toNat ∧ cr.toNat < 0x80000000 ∧
      cr.toNat ∈ fullArenaClauseRefsCore k ∧
      DenseWatchSliceOk F_cur k lit (p + 2) (rem - 2)) := by
  cases h with
  | empty => omega
  | @bin _ r w0 hp hf hne hlt hent hrest =>
    exact Or.inl ⟨w0, hp, hf, hne, hlt, hent, by simpa using hrest⟩
  | @occ _ r w0 cr hp hp1 hf hsz hlt hr hrest =>
    exact Or.inr ⟨w0, cr, by omega, hp, hp1, hf, hsz, hlt, hr, by simpa using hrest⟩

theorem bva_slice_bin_info {F_cur : List (List Nat)} {k : FullCoreState}
    {lit p rem : Nat} (h : DenseWatchSliceOk F_cur k lit p rem)
    (hp_lt : 0 < rem) (hp_ws : p < k.wstk.length)
    (hflag : (k.wstk[p]'hp_ws &&& 0x80000000#32) ≠ 0#32) :
    let ot := k.wstk[p]'hp_ws &&& 0x7FFFFFFF#32
    ot.toNat < 2 * k.cur_vars ∧ (cnfOfClauses F_cur).EntailsClause (cnfClause [lit, ot.toNat]) ∧
    DenseWatchSliceOk F_cur k lit (p + 1) (rem - 1) := by
  rcases denseWatchSliceOk_step h hp_lt with
    ⟨w0, hw0_some, _, _, hot_lt, hent, hrest⟩ | ⟨w0, _, _, hw0_some, _, hbin_eq, _, _, _, _⟩
  · have hw0_val : k.wstk[p]'hp_ws = w0 := by
      rw [List.getElem?_eq_getElem hp_ws] at hw0_some; exact Option.some.inj hw0_some
    rw [hw0_val]; exact ⟨hot_lt, hent, hrest⟩
  · have hw0_val : k.wstk[p]'hp_ws = w0 := by
      rw [List.getElem?_eq_getElem hp_ws] at hw0_some; exact Option.some.inj hw0_some
    exact absurd (hw0_val.symm ▸ hbin_eq) hflag

theorem bva_slice_occ_info {F_cur : List (List Nat)} {k : FullCoreState} {lit p rem : Nat}
    (h : DenseWatchSliceOk F_cur k lit p rem) (hp_lt : 0 < rem) (hp_ws : p < k.wstk.length)
    (hflag : (k.wstk[p]'hp_ws &&& 0x80000000#32) = 0#32) :
    2 ≤ rem ∧ DenseWatchSliceOk F_cur k lit (p + 2) (rem - 2) := by
  rcases denseWatchSliceOk_step h hp_lt with
    ⟨w0, hw0_some, hbin_ne, _, _, _, _⟩ | ⟨_, _, h2le, _, _, _, _, _, _, hrest⟩
  · have hw0_val : k.wstk[p]'hp_ws = w0 := by
      rw [List.getElem?_eq_getElem hp_ws] at hw0_some; exact Option.some.inj hw0_some
    exact absurd (hw0_val ▸ hflag) hbin_ne
  · exact ⟨h2le, hrest⟩

theorem fwd_slice_occ_info {F_cur : List (List Nat)} {k : FullCoreState}
    {lit p rem : Nat} (h : DenseWatchSliceOk F_cur k lit p rem)
    (hp_lt : 0 < rem) (hp_ws : p < k.wstk.length) (hp1_ws : p + 1 < k.wstk.length)
    (hflag : (k.wstk[p]'hp_ws &&& 0x80000000#32) = 0#32) :
    2 ≤ rem ∧ (k.wstk[p + 1]'hp1_ws).toNat ∈ fullArenaClauseRefsCore k ∧
    DenseWatchSliceOk F_cur k lit (p + 2) (rem - 2) := by
  rcases denseWatchSliceOk_step h hp_lt with
    ⟨w0, hw0_some, hbin_ne, _, _, _, _⟩ | ⟨_, w1, h2le, _, hw1_some, _, _, _, hcr_mem, hrest⟩
  · have hw0_val : k.wstk[p]'hp_ws = w0 := by
      rw [List.getElem?_eq_getElem hp_ws] at hw0_some; exact Option.some.inj hw0_some
    exact absurd (hw0_val ▸ hflag) hbin_ne
  · have hw1_val : k.wstk[p + 1]'hp1_ws = w1 := by
      rw [List.getElem?_eq_getElem hp1_ws] at hw1_some; exact Option.some.inj hw1_some
    exact ⟨h2le, hw1_val ▸ hcr_mem, hrest⟩

theorem denseWatchSliceOk_relocate {F0 F1 : List (List Nat)} {k k' : FullCoreState}
    {lit p p' rem : Nat} (hF : (cnfOfClauses F1).Entails (cnfOfClauses F0))
    (hvars : k.cur_vars ≤ k'.cur_vars)
    (hsub : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k')
    (hwstk : ∀ i < rem, k'.wstk[p' + i]? = k.wstk[p + i]?)
    (h : DenseWatchSliceOk F0 k lit p rem) : DenseWatchSliceOk F1 k' lit p' rem := by
  induction h generalizing p' with
  | empty => exact .empty
  | @bin p rem w0 hp hflag hne hlt hent _ ih =>
    refine .bin (by simpa using (hwstk 0 (by omega)).trans hp) hflag hne (by omega)
      (CNF.entails_clause_trans hF hent)
      (ih (p' := p' + 1) fun i hi => by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hwstk (i + 1) (by omega))
  | @occ p rem w0 cref hp hp1 hflag hsz hlt href _ ih =>
    refine .occ (by simpa using (hwstk 0 (by omega)).trans hp)
      (by simpa using (hwstk 1 (by omega)).trans hp1) hflag hsz hlt (hsub _ href)
      (ih (p' := p' + 2) fun i hi => by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hwstk (i + 2) (by omega))

theorem denseWatchSliceOk_append_occ {F_cur : List (List Nat)} {k k' : FullCoreState}
    {lit p p' rem : Nat} {w0 cref : BitVec 32}
    (hvars : k.cur_vars ≤ k'.cur_vars)
    (hsub : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k')
    (hwstk : ∀ i < rem, k'.wstk[p' + i]? = k.wstk[p + i]?)
    (h : DenseWatchSliceOk F_cur k lit p rem)
    (hw0 : k'.wstk[p' + rem]? = some w0) (hw1 : k'.wstk[p' + rem + 1]? = some cref)
    (hflag : (w0 &&& 0x80000000#32) = 0#32) (hsz : 3 ≤ w0.toNat)
    (hlt : cref.toNat < 0x80000000) (href : cref.toNat ∈ fullArenaClauseRefsCore k') :
    DenseWatchSliceOk F_cur k' lit p' (rem + 2) := by
  induction h generalizing p' with
  | empty => exact .occ (by simpa using hw0) (by simpa using hw1) hflag hsz hlt href .empty
  | @bin p rem w hp hf hne hl he _ ih =>
    refine .bin (by simpa using (hwstk 0 (by omega)).trans hp) hf hne (by omega) he ?_
    exact ih (p' := p' + 1)
      (fun i hi => by simpa [show p' + 1 + i = p' + (i + 1) by omega,
        show p + 1 + i = p + (i + 1) by omega] using hwstk (i + 1) (by omega))
      (by simpa [show p' + 1 + rem = p' + (rem + 1) by omega] using hw0)
      (by simpa [show p' + 1 + rem + 1 = p' + (rem + 1) + 1 by omega] using hw1)
  | @occ p rem w cr hp hp1 hf hs hl hr _ ih =>
    refine .occ (by simpa using (hwstk 0 (by omega)).trans hp)
      (by simpa using (hwstk 1 (by omega)).trans hp1) hf hs hl (hsub _ hr) ?_
    exact ih (p' := p' + 2)
      (fun i hi => by simpa [show p' + 2 + i = p' + (i + 2) by omega,
        show p + 2 + i = p + (i + 2) by omega] using hwstk (i + 2) (by omega))
      (by simpa [show p' + 2 + rem = p' + (rem + 2) by omega] using hw0)
      (by simpa [show p' + 2 + rem + 1 = p' + (rem + 2) + 1 by omega] using hw1)

theorem fullWatchPush_preserves_denseWatchesInv {F_cur : List (List Nat)} {s s' : FullState}
    {lit w0 w1 : BitVec 32} {ok : Bool}
    (hw : DenseWatchesInv F_cur s.core) (hlay : WatchStackLayout s'.core)
    (hvars : s'.core.cur_vars = s.core.cur_vars)
    (hsub : ∀ r ∈ fullArenaClauseRefsCore s.core, r ∈ fullArenaClauseRefsCore s'.core)
    (hflag : (w0 &&& 0x80000000#32) = 0#32) (hsz : 3 ≤ w0.toNat)
    (hlt : w1.toNat < 0x80000000) (href : w1.toNat ∈ fullArenaClauseRefsCore s'.core)
    (hother : ∀ l < 2 * s.core.cur_vars, l ≠ lit.toNat →
      fullWatchSize s' l = fullWatchSize s l ∧
      ∀ i < fullWatchSize s l,
        s'.core.wstk[fullWatchOff s' l + i]? = s.core.wstk[fullWatchOff s l + i]?)
    (hok_true : ok = true →
      lit.toNat < 2 * s.core.cur_vars ∧
      fullWatchSize s' lit.toNat = fullWatchSize s lit.toNat + 2 ∧
      (∀ i < fullWatchSize s lit.toNat,
        s'.core.wstk[fullWatchOff s' lit.toNat + i]? =
          s.core.wstk[fullWatchOff s lit.toNat + i]?) ∧
      s'.core.wstk[fullWatchOff s' lit.toNat + fullWatchSize s lit.toNat]? = some w0 ∧
      s'.core.wstk[fullWatchOff s' lit.toNat + fullWatchSize s lit.toNat + 1]? = some w1)
    (hok_false : ok = false → lit.toNat < 2 * s.core.cur_vars →
      fullWatchSize s' lit.toNat = fullWatchSize s lit.toNat ∧
      ∀ i < fullWatchSize s lit.toNat,
        s'.core.wstk[fullWatchOff s' lit.toNat + i]? =
          s.core.wstk[fullWatchOff s lit.toNat + i]?) :
    DenseWatchesInv F_cur s'.core := by
  refine ⟨hlay, fun l hl => ?_⟩
  have hl0 : l < 2 * s.core.cur_vars := hvars ▸ hl
  have hent_refl : (cnfOfClauses F_cur).Entails (cnfOfClauses F_cur) := by
    rw [CNF.entails_def]; exact fun _ h => h
  by_cases hle : l = lit.toNat
  · subst hle
    cases ok with
    | false =>
      obtain ⟨hs, hslice⟩ := hok_false rfl hl0
      change DenseWatchSliceOk F_cur s'.core lit.toNat (fullWatchOff s' lit.toNat)
        (fullWatchSize s' lit.toNat)
      rw [hs]
      exact denseWatchSliceOk_relocate hent_refl (by omega) hsub hslice (hw.slices _ hl0)
    | true =>
      obtain ⟨_, hs, hpre, hw0, hw1⟩ := hok_true rfl
      change DenseWatchSliceOk F_cur s'.core lit.toNat (fullWatchOff s' lit.toNat)
        (fullWatchSize s' lit.toNat)
      rw [hs]
      exact denseWatchSliceOk_append_occ (by omega) hsub hpre (hw.slices _ hl0) hw0 hw1 hflag
        hsz hlt href
  · obtain ⟨hs, hslice⟩ := hother l hl0 hle
    change DenseWatchSliceOk F_cur s'.core l (fullWatchOff s' l) (fullWatchSize s' l)
    rw [hs]
    exact denseWatchSliceOk_relocate hent_refl (by omega) hsub hslice (hw.slices l hl0)

theorem m6_denseWatchesInv_of_w {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) : DenseWatchesInv F_cur s.core := by
  have := h.2.1.watches; unfold ModeWatchesInv at this; rwa [ite_eq_right h.2.2.2.2.2.2] at this

theorem m6_fullDenseInvW_of_watchPush_occ {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) {lit w0 w1 : BitVec 32} {ok : Bool}
    {wvec' wstk' wsort' : List (BitVec 32)} {wlen' : Nat} {wu' : BitVec 64}
    (hlen' : ({ s with
      core := { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' }
      scratch := { s.scratch with wsort := wsort' } } : FullState).LengthsOk c)
    (hlay' : WatchStackLayout
      { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' })
    (hflag : (w0 &&& 0x80000000#32) = 0#32) (hsz : 3 ≤ w0.toNat)
    (hlt : w1.toNat < 0x80000000) (href : w1.toNat ∈ fullArenaClauseRefs s)
    (hother : ∀ l < 2 * s.core.cur_vars, l ≠ lit.toNat →
      fullWatchSizeCore
        { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' } l =
        fullWatchSize s l ∧
      ∀ i < fullWatchSize s l,
        wstk'[fullWatchOffCore
          { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' } l + i]? =
        s.core.wstk[fullWatchOff s l + i]?)
    (hok_t : ok = true →
      lit.toNat < 2 * s.core.cur_vars ∧
      fullWatchSizeCore
        { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' } lit.toNat =
        fullWatchSize s lit.toNat + 2 ∧
      (∀ i < fullWatchSize s lit.toNat,
        wstk'[fullWatchOffCore
          { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' }
          lit.toNat + i]? = s.core.wstk[fullWatchOff s lit.toNat + i]?) ∧
      wstk'[fullWatchOffCore
        { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' }
        lit.toNat + fullWatchSize s lit.toNat]? = some w0 ∧
      wstk'[fullWatchOffCore
        { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' }
        lit.toNat + fullWatchSize s lit.toNat + 1]? = some w1)
    (hok_f : ok = false → lit.toNat < 2 * s.core.cur_vars →
      fullWatchSizeCore
        { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' } lit.toNat =
        fullWatchSize s lit.toNat ∧
      ∀ i < fullWatchSize s lit.toNat,
        wstk'[fullWatchOffCore
          { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' }
          lit.toNat + i]? = s.core.wstk[fullWatchOff s lit.toNat + i]?) :
    FullDenseInvW c F0 F_cur
      { s with
        core := { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' }
        scratch := { s.scratch with wsort := wsort' } } := by
  let s' : FullState :=
    { s with
      core := { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' }
      scratch := { s.scratch with wsort := wsort' } }
  have hdm := h.2.2.2.2.2.2
  have hdw : DenseWatchesInv F_cur s.core := m6_denseWatchesInv_of_w h
  have hdw' := fullWatchPush_preserves_denseWatchesInv (s := s) (s' := s') (ok := ok)
    hdw hlay' rfl (fun _ hr => hr) hflag hsz hlt href hother hok_t hok_f
  have hw' : FullWitnessInv c F0 F_cur s'.core :=
    { h.2.1 with
      arena := { h.2.1.arena with len_ok := h.2.1.arena.len_ok }
      watches := by unfold ModeWatchesInv; rw [ite_eq_right hdm]; exact hdw' }
  exact ⟨hlen', hw', h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, hdm⟩

/-! ## 3. Shared Dynamic-Matrix Congruence & State Mutators -/

theorem fidBvaRowEntryOk_congr {F_cur : List (List Nat)} {s s' : FullState}
    {fr : Nat} {w : BitVec 32} {res : List Nat} (hcv : s'.core.cur_vars = s.core.cur_vars)
    (har : s'.core.arena = s.core.arena) (hal : s'.core.arena_len = s.core.arena_len)
    (h : FidBvaRowEntryOk F_cur s fr w res) : FidBvaRowEntryOk F_cur s' fr w res := by
  unfold FidBvaRowEntryOk at h ⊢
  by_cases hbin : (w &&& 0x80000000#32) ≠ 0#32
  · rw [ite_eq_left hbin] at h ⊢; rwa [hcv]
  · rw [ite_eq_right hbin] at h ⊢
    simp only [fullArenaClauseRefs, fullArenaClauseGarb, fullArenaClauseSize,
      fullArenaClauseLits, fullArenaClauseRefsCore, fullArenaClauseGarbCore,
      fullArenaClauseSizeCore, fullArenaClauseLitsCore, fullArenaHdrCore, har, hal] at h ⊢
    exact h

theorem fidBvaMatrixInv_congr {c : FullCfg} {F_cur : List (List Nat)} {s s' : FullState}
    {step bump : Nat} (hcv : s'.core.cur_vars = s.core.cur_vars)
    (har : s'.core.arena = s.core.arena) (hal : s'.core.arena_len = s.core.arena_len)
    (hsb : s'.scratch.scratch_buf = s.scratch.scratch_buf)
    (h : FidBvaMatrixInv c F_cur s step bump) : FidBvaMatrixInv c F_cur s' step bump := by
  rcases h with ⟨hsc, hs1, hss, hb1, hb2, hrows⟩
  refine ⟨hsc, hs1, hss, hb1, hb2, fun r hr => ?_⟩
  rcases hrows r hr with ⟨hfr, hro1, hq2, hro2, hpo, hm⟩
  refine ⟨by rw [hsb, hcv]; exact hfr, by rw [hsb]; exact hro1, by rw [hsb]; exact hq2,
    by rw [hsb]; exact hro2, by intro hr0; rw [hsb]; exact hpo hr0, fun m hm_lt => ?_⟩
  rw [hsb] at hm_lt
  rcases hm m hm_lt with ⟨res, hres_lt, hres_nd, hok, hent, hpar⟩
  refine ⟨res, fun x hx => by rw [hcv]; exact hres_lt x hx, hres_nd, ?_, ?_, ?_⟩
  · rw [hsb]; exact fidBvaRowEntryOk_congr hcv har hal hok
  · intro t ht; rw [hsb]; exact hent t ht
  · intro hr0; rw [hsb]; obtain ⟨hpi, hpok⟩ := hpar hr0
    exact ⟨hpi, fidBvaRowEntryOk_congr hcv har hal hpok⟩

theorem fullDenseInvW_set_scr_arrs {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s)
    {tm ws1 ws2 : List (BitVec 32)}
    (htm : tm.length = 2 * c.max_vars) (hws1 : ws1.length = 2 * c.max_vars)
    (hws2 : ws2.length = 2 * c.max_vars) :
    FullDenseInvW c F0 F_cur
      { s with scratch := { s.scratch with tarjan_mark := tm, work_stk1 := ws1,
                                           work_stk2 := ws2 } } :=
  ⟨⟨h.1.core_ok, { h.1.scratch_ok with
      tarjan_mark_len := htm, work_stk1_len := hws1, work_stk2_len := hws2 }⟩,
   h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

theorem fullDenseInvW_set_repr {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s)
    {rp : List (BitVec 32)} (hrp : rp.length = 2 * c.max_vars) :
    FullDenseInvW c F0 F_cur { s with core := { s.core with repr := rp } } :=
  fullDenseInv_with_core_aux (tc' := s.core.tmp_cnt) (tl' := s.core.tmp_len) (sc' := s.scratch)
    h hrp h.1.core_ok.min_clr_len_arr h.1.core_ok.tmp_len_arr h.1.core_ok.flags_len
    h.1.core_ok.tmp_len_le h.1.scratch_ok rfl rfl

theorem fullDenseInvW_set_oom {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) (oom' : BitVec 64) :
    FullDenseInvW c F0 F_cur { s with core := { s.core with oom := oom' } } :=
  ⟨⟨{ h.1.core_ok with arena_len_le := h.1.core_ok.arena_len_le }, h.1.scratch_ok⟩,
   { h.2.1 with
     arena := { h.2.1.arena with len_ok := h.2.1.arena.len_ok }
     watches := h.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) },
   h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

end

end LeanQbe.T.Examples.Kissat.Proof.Factor
