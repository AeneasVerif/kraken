/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityCong
public import LeanQbe.T.Examples.Kissat.FullM6CongSubstProof0
public import LeanQbe.T.Examples.Kissat.FullM8CongEnqEvalProof
public import LeanQbe.T.Examples.Kissat.FullM7CongIteProof0
public import LeanQbe.T.Examples.Kissat.FullM7CongHashProof0
import LeanQbe.T.Examples.Kissat.FullCongLemmas1
import LeanQbe.T.Examples.Kissat.FullCongLemmas2

/-!
# Kissat 4.0.4 Congruence Parity Proofs — Part 0 (`FullFidelityCongProof0`)

Defines the parameterized wide-arity gate invariants (`FidGateAt`, `FidGateSeqOk`, `FidCongHtInv`,
`FidOccNodesOk`, `FidCongHtCtrlOk`), all pure semantic lemmas closing `GAP-CONG-01..04` +
`BUG-CONG-00` (64-bit AND mask, 4-lit XOR normalizer & sorting network, XOR LHS self-cancellation,
ITE-to-AND/XOR rewriting, `u32` pair-swap preservation), and all `Spec` contracts for
`FullFidelityCong`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityCong

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullCongHelpers
open LeanQbe.T.Examples.Kissat.FullM3CongBva
open LeanQbe.T.Examples.Kissat.FullM6CongSubst
open LeanQbe.T.Examples.Kissat.FullM7CongHash
open LeanQbe.T.Examples.Kissat.FullM7CongIte
open LeanQbe.T.Examples.Kissat.FullM8FidV12
open Kraken.Bedrock2.Test

/-! ## 1. Parameterized Congruence Gate, Hash Table & Pair-Sort Invariants -/

section Invariants

/-- Maximum dynamic scratch hash-table bucket count (`1,048,576 = 16 * 2^16`). -/
def fidCongHashMaxSz : Nat := 1048576

/-- Valid extracted gate parameterized by maximum AND arity `maxA` (`31` for M6, `64` for
`GAP-CONG-01`). XOR gates have `2 ≤ arity ≤ 4`; ITE gates have `arity = 3`. -/
def FidGateAt (maxA : Nat) (F_cur : List (List Nat)) (cur_vars : Nat) (scr : List (BitVec 32))
    (g_len g : Nat) : Prop :=
  ∃ (lhs mword : BitVec 32),
    scr[g]? = some lhs ∧ scr[g + 1]? = some mword ∧
    lhs.toNat < 2 * cur_vars ∧
    let tag := (mword >>> 28).toNat
    let arity := (mword &&& 0xFF#32).toNat
    g + 2 + arity ≤ g_len ∧ arity ≤ cur_vars ∧ arity ≤ maxA ∧
    (∀ k < arity, ∃ r : BitVec 32, scr[g + 2 + k]? = some r ∧ r.toNat < 2 * cur_vars) ∧
    ((tag = 0 ∧ 2 ≤ arity ∧
        AndGateDef (cnfOfClauses F_cur) lhs.toNat
          (((scr.drop (g + 2)).take arity).map BitVec.toNat)) ∨
     (tag = 1 ∧ 2 ≤ arity ∧ arity ≤ 4 ∧
        XorListGateDef (cnfOfClauses F_cur) lhs.toNat
          (((scr.drop (g + 2)).take arity).map BitVec.toNat)) ∨
     (tag = 2 ∧ arity = 3 ∧
        IteGateDef (cnfOfClauses F_cur) lhs.toNat
          (scr[g + 2]?.getD 0#32).toNat (scr[g + 3]?.getD 0#32).toNat
          (scr[g + 4]?.getD 0#32).toNat))

/-- Contiguous sequence of valid `FidGateAt maxA` gates in `scr[g ..< g_len)`. -/
inductive FidGateSeqOk (maxA : Nat) (F_cur : List (List Nat)) (cur_vars : Nat)
    (scr : List (BitVec 32)) (g_len : Nat) : Nat → Prop where
  | done : FidGateSeqOk maxA F_cur cur_vars scr g_len g_len
  | step {g : Nat} (hg : FidGateAt maxA F_cur cur_vars scr g_len g) :
      FidGateSeqOk maxA F_cur cur_vars scr g_len
        (g + 2 + ((scr[g + 1]?.getD 0#32) &&& 0xFF#32).toNat) →
      FidGateSeqOk maxA F_cur cur_vars scr g_len g

/-- Every non-empty hash slot in `scr[ht_off ..< ht_off + ht_sz)` points to a valid
`FidGateAt maxA` gate in `scr0[0 ..< g_len)`. -/
def FidCongHtInv (maxA : Nat) (F_cur : List (List Nat)) (cur_vars : Nat)
    (scr0 scr : List (BitVec 32)) (g_len ht_off ht_sz : Nat) : Prop :=
  ∀ k < ht_sz,
    let ent := scr[ht_off + k]?.getD 0xFFFFFFFF#32
    ent = 0xFFFFFFFF#32 ∨ FidGateAt maxA F_cur cur_vars scr0 g_len ent.toNat

/-- Occurrence bucket heads and 2-word occurrence nodes in `scr[g_len ..< occ_end)` point only to
valid `FidGateAt maxA` gates and valid node pointers. -/
def FidOccNodesOk (maxA : Nat) (F_cur : List (List Nat))
    (cv g_len occ_end ctrl_off bkt_off occ_bkt : Nat) (scr0 scr : List (BitVec 32)) : Prop :=
  g_len ≤ occ_end ∧ occ_end ≤ ctrl_off ∧
  (∀ b < occ_bkt, M6OccNodePtrOk g_len occ_end (scr[bkt_off + b]?.getD 0xFFFFFFFF#32)) ∧
  (∀ nd, g_len ≤ nd → nd + 1 < occ_end → (nd - g_len) % 2 = 0 →
    let entry := scr[nd]?.getD 0#32
    let gn := (entry &&& 0x00FFFFFF#32).toNat
    let slot := (entry >>> 24).toNat
    gn < g_len ∧ FidGateAt maxA F_cur cv scr0 g_len gn ∧
    slot ≤ ((scr0[gn + 1]?.getD 0#32) &&& 0xFF#32).toNat ∧
    M6OccNodePtrOk g_len occ_end (scr[nd + 1]?.getD 0xFFFFFFFF#32))

/-- Valid power-of-2 congruence hash-table control block up to `1,048,576` (`16 * 2^16`) buckets. -/
abbrev FidCongHtCtrlOk (c : FullCfg) (scr : List (BitVec 32))
    (ctrl_off ht_off ht_sz : Nat) : Prop :=
  scr.length = c.scratch_cap ∧
  ctrl_off + 8 ≤ ht_off ∧
  ht_off + ht_sz ≤ c.scratch_cap ∧
  ht_off ≤ 0x7FFFFFFF ∧
  (∃ k ≤ 16, ht_sz = 16 * 2 ^ k) ∧
  scr[ctrl_off + 6]? = some (BitVec.ofNat 32 ht_off) ∧
  scr[ctrl_off + 7]? = some (BitVec.ofNat 32 ht_sz)

/-- Pointwise invariant over `n` consecutive `(u32, u32)` pairs stored in `a[0 ..< 2*n)`. -/
def FidPairsOk (P : BitVec 32 → BitVec 32 → Prop) (a : List (BitVec 32)) (n : Nat) : Prop :=
  ∀ i < n, P (a[2 * i]?.getD 0#32) (a[2 * i + 1]?.getD 0#32)

end Invariants

/-! ## 2. Bridges Between `FidGateAt` / `M6GateAt` and Monotonicity Lemmas -/

section Bridges

theorem fidGateAt_mono {maxA maxB : Nat} (hle : maxA ≤ maxB)
    {F_cur : List (List Nat)} {cv : Nat} {scr : List (BitVec 32)} {g_len g : Nat}
    (h : FidGateAt maxA F_cur cv scr g_len g) : FidGateAt maxB F_cur cv scr g_len g := by
  obtain ⟨lhs, mword, h0, h1, hlhs, hbd, hcv, ha, hrhs, hsem⟩ := h
  exact ⟨lhs, mword, h0, h1, hlhs, hbd, hcv, Nat.le_trans ha hle, hrhs, hsem⟩

theorem fidGateAt_of_m6 {F_cur : List (List Nat)} {cv : Nat} {scr : List (BitVec 32)}
    {g_len g : Nat} (h : M6GateAt F_cur cv scr g_len g) :
    FidGateAt 31 F_cur cv scr g_len g := h

theorem fidGateAt_to_m6 {F_cur : List (List Nat)} {cv : Nat} {scr : List (BitVec 32)}
    {g_len g : Nat} (h : FidGateAt 31 F_cur cv scr g_len g) :
    M6GateAt F_cur cv scr g_len g := h

theorem fidGateAt_to_m6_of_xor {maxA : Nat} {F_cur : List (List Nat)} {cv : Nat}
    {scr : List (BitVec 32)} {g_len g : Nat}
    (h : FidGateAt maxA F_cur cv scr g_len g)
    (htag : (scr[g + 1]?.getD 0#32 >>> 28) = 1#32) :
    M6GateAt F_cur cv scr g_len g := by
  obtain ⟨lhs, mword, h0, h1, hlhs, hbd, hcv, _, hrhs, hsem⟩ := h
  have ht1 : (mword >>> 28).toNat = 1 := by
    rw [h1, Option.getD_some] at htag; rw [htag]; rfl
  rcases hsem with ⟨h0t, _⟩ | ⟨_, h2, h4, hxor⟩ | ⟨h2t, _⟩
  · omega
  · exact ⟨lhs, mword, h0, h1, hlhs, hbd, hcv, by omega, hrhs, Or.inr (Or.inl ⟨ht1, h2, h4, hxor⟩)⟩
  · omega

theorem fidGateAt_frame {maxA : Nat} {F_cur : List (List Nat)} {cv g_len g : Nat}
    {scr scr' : List (BitVec 32)}
    (hpref : ∀ idx < g_len, scr'[idx]? = scr[idx]?)
    (h : FidGateAt maxA F_cur cv scr g_len g) : FidGateAt maxA F_cur cv scr' g_len g := by
  obtain ⟨lhs, mword, h0, h1, hlhs, hbd, hcv, ha, hrhs, hsem⟩ := h
  have hdt : (scr'.drop (g + 2)).take (mword &&& 0xFF#32).toNat =
      (scr.drop (g + 2)).take (mword &&& 0xFF#32).toNat := by
    have hle1 : g + 2 + (mword &&& 0xFF#32).toNat ≤ scr.length := by
      have h1l : g + 1 < scr.length := (List.getElem?_eq_some_iff.mp h1).1
      rcases Nat.eq_zero_or_pos (mword &&& 0xFF#32).toNat with hz | hp
      · omega
      · obtain ⟨_, hr, _⟩ := hrhs ((mword &&& 0xFF#32).toNat - 1) (by omega)
        have hrl : g + 2 + ((mword &&& 0xFF#32).toNat - 1) < scr.length :=
          (List.getElem?_eq_some_iff.mp hr).1
        omega
    have hle2 : g + 2 + (mword &&& 0xFF#32).toNat ≤ scr'.length := by
      have h1' := (hpref (g + 1) (by omega)).trans h1
      have h1l : g + 1 < scr'.length := (List.getElem?_eq_some_iff.mp h1').1
      rcases Nat.eq_zero_or_pos (mword &&& 0xFF#32).toNat with hz | hp
      · omega
      · obtain ⟨_, hr, _⟩ := hrhs ((mword &&& 0xFF#32).toNat - 1) (by omega)
        have hr' := (hpref (g + 2 + ((mword &&& 0xFF#32).toNat - 1)) (by omega)).trans hr
        have hrl : g + 2 + ((mword &&& 0xFF#32).toNat - 1) < scr'.length :=
          (List.getElem?_eq_some_iff.mp hr').1
        omega
    refine List.ext_getElem
      (by simp only [List.length_take, List.length_drop]; omega) fun k hk1 hk2 => ?_
    simp only [List.getElem_take, List.getElem_drop]
    have hk_lt : k < (mword &&& 0xFF#32).toNat := by
      simp only [List.length_take, List.length_drop] at hk1; omega
    have heq := hpref (g + 2 + k) (by omega)
    rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at heq
    exact Option.some.inj heq
  refine ⟨lhs, mword, (hpref g (by omega)).trans h0, (hpref (g + 1) (by omega)).trans h1,
    hlhs, hbd, hcv, ha, fun k hk => ?_, ?_⟩
  · obtain ⟨r, hr, hlt⟩ := hrhs k hk
    exact ⟨r, (hpref (g + 2 + k) (by omega)).trans hr, hlt⟩
  · rcases hsem with ⟨ht, h2, hand⟩ | ⟨ht, h2, h4, hxor⟩ | ⟨ht, h3, hite⟩
    · exact Or.inl ⟨ht, h2, by rwa [hdt]⟩
    · exact Or.inr (Or.inl ⟨ht, h2, h4, by rwa [hdt]⟩)
    · refine Or.inr (Or.inr ⟨ht, h3, ?_⟩)
      rw [hpref (g + 2) (by omega), hpref (g + 3) (by omega), hpref (g + 4) (by omega)]
      exact hite

theorem fidGateAt_ext_len {maxA : Nat} {F_cur : List (List Nat)} {cv g_len g_len' g : Nat}
    {scr : List (BitVec 32)} (hle : g_len ≤ g_len')
    (h : FidGateAt maxA F_cur cv scr g_len g) : FidGateAt maxA F_cur cv scr g_len' g := by
  obtain ⟨lhs, mword, h0, h1, hlhs, hbd, hcv, ha, hrhs, hsem⟩ := h
  exact ⟨lhs, mword, h0, h1, hlhs, Nat.le_trans hbd hle, hcv, ha, hrhs, hsem⟩

theorem fidGateSeqOk_mono {maxA maxB : Nat} (hle : maxA ≤ maxB)
    {F_cur : List (List Nat)} {cv : Nat} {scr : List (BitVec 32)} {g_len g : Nat}
    (h : FidGateSeqOk maxA F_cur cv scr g_len g) : FidGateSeqOk maxB F_cur cv scr g_len g := by
  induction h with
  | done => exact .done
  | step hg _ ih => exact .step (fidGateAt_mono hle hg) ih

theorem fidGateSeqOk_of_m6 {F_cur : List (List Nat)} {cv : Nat} {scr : List (BitVec 32)}
    {g_len g : Nat} (h : M6GateSeqOk F_cur cv scr g_len g) :
    FidGateSeqOk 31 F_cur cv scr g_len g := by
  induction h with
  | done => exact .done
  | step hg _ ih => exact .step hg ih

theorem fidGateSeqOk_append_gate {maxA : Nat} {F_cur : List (List Nat)} {cv g_len g_len' g : Nat}
    {scr scr' : List (BitVec 32)}
    (hpref : ∀ idx < g_len, scr'[idx]? = scr[idx]?)
    (hseq : FidGateSeqOk maxA F_cur cv scr g_len g)
    (htail : FidGateSeqOk maxA F_cur cv scr' g_len' g_len)
    (hle : g_len ≤ g_len') :
    FidGateSeqOk maxA F_cur cv scr' g_len' g := by
  induction hseq with
  | done => exact htail
  | @step g0 hg _ ih =>
    have hg' := fidGateAt_ext_len hle (fidGateAt_frame hpref hg)
    obtain ⟨_, mword, _, h1, _, hbd, _, _, _, _⟩ := hg
    have hm_eq : scr'[g0 + 1]?.getD 0#32 = scr[g0 + 1]?.getD 0#32 := by
      rw [hpref (g0 + 1) (by omega)]
    exact .step hg' (by rw [hm_eq]; exact ih)

theorem fidCongHtInv_of_m6 {F_cur : List (List Nat)} {cv : Nat} {scr0 scr : List (BitVec 32)}
    {g_len ht_off ht_sz : Nat} (h : M6CongHtInv F_cur cv scr0 scr g_len ht_off ht_sz) :
    FidCongHtInv 31 F_cur cv scr0 scr g_len ht_off ht_sz := h

theorem fidCongHtInv_to_m6 {F_cur : List (List Nat)} {cv : Nat} {scr0 scr : List (BitVec 32)}
    {g_len ht_off ht_sz : Nat} (h : FidCongHtInv 31 F_cur cv scr0 scr g_len ht_off ht_sz) :
    M6CongHtInv F_cur cv scr0 scr g_len ht_off ht_sz := h

theorem fidCongHtInv_mono {maxA maxB : Nat} (hle : maxA ≤ maxB)
    {F_cur : List (List Nat)} {cv : Nat} {scr0 scr : List (BitVec 32)} {g_len ht_off ht_sz : Nat}
    (h : FidCongHtInv maxA F_cur cv scr0 scr g_len ht_off ht_sz) :
    FidCongHtInv maxB F_cur cv scr0 scr g_len ht_off ht_sz := fun k hk =>
  (h k hk).elim Or.inl fun hg => Or.inr (fidGateAt_mono hle hg)

theorem fidCongHtInv_clear {maxA : Nat} {F_cur : List (List Nat)} {cv g_len ht_off ht_sz : Nat}
    {scr0 scr : List (BitVec 32)}
    (hall : ∀ k < ht_sz, scr[ht_off + k]? = some 0xFFFFFFFF#32) :
    FidCongHtInv maxA F_cur cv scr0 scr g_len ht_off ht_sz := fun k hk => by
  left; rw [hall k hk, Option.getD_some]

theorem fidCongHtInv_set_gate {maxA : Nat} {F_cur : List (List Nat)} {cv g_len ht_off ht_sz : Nat}
    {scr0 scr : List (BitVec 32)} {slot : Nat} {g : BitVec 32}
    (hinv : FidCongHtInv maxA F_cur cv scr0 scr g_len ht_off ht_sz)
    (hslot : slot < ht_sz) (harr : ht_off + slot < scr.length)
    (hg : FidGateAt maxA F_cur cv scr0 g_len g.toNat) :
    FidCongHtInv maxA F_cur cv scr0 (scr.set (ht_off + slot) g) g_len ht_off ht_sz := by
  intro k hk
  by_cases hks : k = slot
  · subst hks; right; rw [List.getElem?_set_self harr, Option.getD_some]; exact hg
  · rw [List.getElem?_set_ne (by omega)]; exact hinv k hk

end Bridges

/-! ## 3. Pure Semantic Lemmas (`GAP-CONG-01..04` + `BUG-CONG-00`) -/

section PureSem

/-- 64-bit full bitmask lemma for `GAP-CONG-01` (`2 ≤ ua ≤ 64`, UB-free `ua = 64`). -/
theorem testBit_full_mask_iff64 {ua : BitVec 32} (hlo : 2 ≤ ua.toNat) (hhi : ua.toNat ≤ 64)
    {k : Nat} (hk : k < ua.toNat) :
    (if ua = 64#32 then 0xFFFFFFFFFFFFFFFF#64
     else (1#64 <<< ua.setWidth 64) - 1#64).toNat.testBit k = true := by
  by_cases h64 : ua = 64#32
  · simp only [h64, ↓reduceIte]
    rw [show (0xFFFFFFFFFFFFFFFF#64 : BitVec 64).toNat = 2 ^ 64 - 1 from by decide]
    rw [Nat.testBit_two_pow_sub_one]; exact decide_eq_true (by subst h64; exact hk)
  · simp only [h64, ↓reduceIte]
    have hua_lt : ua.toNat < 64 := by
      have hne : ua.toNat ≠ 64 := fun h => h64 (BitVec.eq_of_toNat_eq h)
      omega
    have hzw : (ua.setWidth 64).toNat = ua.toNat := by
      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
    have hpow_lt : 2 ^ ua.toNat < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) hua_lt
    have hshl : (1#64 <<< ua.setWidth 64 : BitVec 64).toNat = 2 ^ ua.toNat := by
      change (1#64 <<< (ua.setWidth 64).toNat : BitVec 64).toNat = 2 ^ ua.toNat
      rw [hzw, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
      change (1 * 2 ^ ua.toNat) % 2 ^ 64 = 2 ^ ua.toNat
      rw [Nat.one_mul, Nat.mod_eq_of_lt hpow_lt]
    have hpow_pos : 1 ≤ 2 ^ ua.toNat := Nat.one_le_two_pow
    have hsub : ((1#64 <<< ua.setWidth 64) - 1#64 : BitVec 64).toNat = 2 ^ ua.toNat - 1 := by
      rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by rw [hshl]; exact hpow_pos)), hshl]
      rfl
    rw [hsub, Nat.testBit_two_pow_sub_one]; exact decide_eq_true hk

theorem bv64_or_shl_testBit (mask : BitVec 64) {k : Nat} (hk : k < 64) (i : Nat) :
    (mask ||| (1#64 <<< BitVec.ofNat 64 k)).toNat.testBit i =
      (mask.toNat.testBit i || decide (i = k)) := by
  have hk_bv : (BitVec.ofNat 64 k).toNat = k := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hshl : (1#64 <<< BitVec.ofNat 64 k : BitVec 64).toNat = 2 ^ k := by
    change (1#64 <<< (BitVec.ofNat 64 k).toNat : BitVec 64).toNat = 2 ^ k
    rw [hk_bv, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    change (1 * 2 ^ k) % 2 ^ 64 = 2 ^ k
    rw [Nat.one_mul, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hk)]
  rw [BitVec.toNat_or, Nat.testBit_or, hshl, Nat.testBit_two_pow]
  by_cases hik : i = k
  · subst hik; simp
  · simp [hik, Ne.symm hik]

theorem xorEvalList_triple (α : Nat → Bool) (a b c : Nat) :
    xorEvalList α [a, b, c] = (evalLitVal α a != (evalLitVal α b != evalLitVal α c)) := by
  rw [xorEvalList_cons, xorEvalList_cons, xorEvalList_cons, xorEvalList_nil]
  cases evalLitVal α a <;> cases evalLitVal α b <;> cases evalLitVal α c <;> rfl

/-- Three-element sorting network produces a permutation of `[r0, r1, r2]`. -/
theorem sort3_perm (r0 r1 r2 : BitVec 32) :
    let (a0, a1) := if r1 < r0 then (r1, r0) else (r0, r1)
    let (b1, b2) := if r2 < a1 then (r2, a1) else (a1, r2)
    let (c0, c1) := if b1 < a0 then (b1, a0) else (a0, b1)
    List.Perm [c0, c1, b2] [r0, r1, r2] := by
  have h2 : ∀ x y : BitVec 32,
      List.Perm [(if y < x then (y, x) else (x, y)).1, (if y < x then (y, x) else (x, y)).2]
        [x, y] := fun x y => by
    split
    · exact .swap _ _ _
    · exact .refl _
  dsimp only
  exact (List.Perm.append_right [_] (h2 _ _)).trans
    ((List.Perm.cons _ (h2 _ _)).trans (List.Perm.append_right [_] (h2 _ _)))

private theorem bv32_bit0_eval (α : Nat → Bool) (x : BitVec 32) :
    evalLitVal α x.toNat =
      (evalLitVal α (x &&& ~~~1#32).toNat != decide ((x &&& 1#32) ≠ 0#32)) := by
  have hev := m6_bv32_and_not1_toNat x
  rw [hev]
  unfold evalLitVal litVar litSign
  have hdiv : (2 * (x.toNat / 2)) / 2 = x.toNat / 2 := by omega
  have hmod0 : (2 * (x.toNat / 2)) % 2 = 0 := by omega
  have hb0 : decide ((x &&& 1#32) ≠ 0#32) = decide (x.toNat % 2 = 1) := by
    have h1 : (x &&& 1#32).toNat = x.toNat % 2 := by
      rw [BitVec.toNat_and, show (1#32 : BitVec 32).toNat = 1 from rfl, Nat.and_one_is_mod]
    by_cases hm : x.toNat % 2 = 0
    · have hz : (x &&& 1#32) = 0#32 := BitVec.eq_of_toNat_eq (by rw [h1, hm]; rfl)
      simp [hz, hm]
    · have ho : x.toNat % 2 = 1 := by omega
      have hnz : (x &&& 1#32) ≠ 0#32 := fun hz => by
        have := congrArg BitVec.toNat hz; rw [h1, ho] at this; cases this
      simp [hnz, ho]
  rw [hdiv, hmod0, hb0]
  cases α (x.toNat / 2) <;> rcases Nat.mod_two_eq_zero_or_one x.toNat with hm | hm <;> simp [hm]

private theorem bool_xor4_norm :
    ∀ a0 a1 a2 a3 b0 b1 b2 b3 : Bool,
      ((!(a0 != b0)) = ((a1 != b1) != ((a2 != b2) != (a3 != b3)))) →
      (a0 != ((((true != b0) != b1) != b2) != b3)) = (a1 != (a2 != a3)) := by
  decide

/-- Semantic soundness of `full_cong_emit_xor4` (`GAP-CONG-02` 4-literal XOR normalizer). -/
theorem fid_emit_xor4_sem {F_cur : List (List Nat)} {x0 x1 x2 x3 : BitVec 32}
    (hxor : XorListGateDef (cnfOfClauses F_cur) (litNeg x0.toNat) [x1.toNat, x2.toNat, x3.toNat]) :
    let lhs := (x0 &&& ~~~1#32) ||| ((1#32 ^^^ x0 ^^^ x1 ^^^ x2 ^^^ x3) &&& 1#32)
    let r0 := x1 &&& ~~~1#32; let r1 := x2 &&& ~~~1#32; let r2 := x3 &&& ~~~1#32
    XorListGateDef (cnfOfClauses F_cur) lhs.toNat [r0.toNat, r1.toNat, r2.toNat] := by
  intro lhs r0 r1 r2 α hα
  have hx := hxor α hα
  rw [evalLitVal_litNeg, xorEvalList_triple] at hx
  rw [xorEvalList_triple]
  have hbit : ∀ y : BitVec 32, decide ((y &&& 1#32) ≠ 0#32) = y.getLsbD 0 := fun y => by
    have h0 : (y &&& 1#32).toNat = if y.getLsbD 0 then 1 else 0 := by
      rw [BitVec.toNat_and, show (1#32 : BitVec 32).toNat = 1 from rfl, Nat.and_one_is_mod,
        BitVec.getLsbD, Nat.testBit_zero]
      cases hm : y.toNat % 2 == 1 <;> simp_all <;> omega
    cases hg : y.getLsbD 0
    · simp only [hg, Bool.false_eq_true, ↓reduceIte] at h0
      have hz : (y &&& 1#32) = 0#32 := BitVec.eq_of_toNat_eq h0
      simp [hz]
    · simp only [hg, ↓reduceIte] at h0
      have hnz : (y &&& 1#32) ≠ 0#32 := fun hz => by
        have := congrArg BitVec.toNat hz; rw [h0] at this; cases this
      simp [hnz]
  have hlhs_ev : evalLitVal α lhs.toNat =
      (evalLitVal α (x0 &&& ~~~1#32).toNat !=
        ((((true != x0.getLsbD 0) != x1.getLsbD 0) != x2.getLsbD 0) != x3.getLsbD 0)) := by
    rw [bv32_bit0_eval α lhs, hbit]
    have h1 : (lhs &&& ~~~1#32) = (x0 &&& ~~~1#32) := by
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      simp only [lhs, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not]
      cases i with
      | zero => simp [hi]
      | succ k => simp [hi]
    have h2 : lhs.getLsbD 0 =
        ((((true != x0.getLsbD 0) != x1.getLsbD 0) != x2.getLsbD 0) != x3.getLsbD 0) := by
      simp [lhs]
    rw [h1, h2]
  rw [hlhs_ev]
  rw [bv32_bit0_eval α x0, bv32_bit0_eval α x1, bv32_bit0_eval α x2, bv32_bit0_eval α x3,
    hbit, hbit, hbit, hbit] at hx
  exact bool_xor4_norm _ _ _ _ _ _ _ _ hx

private theorem list_perm_cons_eraseIdx {α : Type _} :
    ∀ (xs : List α) (i : Nat) (hi : i < xs.length),
      List.Perm xs (xs[i]'hi :: xs.eraseIdx i)
  | [], _, hi => nomatch hi
  | _ :: _, 0, _ => .refl _
  | a :: t, i + 1, hi =>
    .trans (.cons a (list_perm_cons_eraseIdx t i (by simp at hi; omega))) (.swap _ _ _)

/-- XOR LHS self-cancellation (`GAP-CONG-02`): if `lhs &&& ~~~1` appears at index `self_i` of `xs`,
cancelling it yields `((lhs &&& 1) ≠ 0) = xorEvalList α (xs.eraseIdx self_i)`. -/
theorem fid_xor_self_cancel_sem {α : Nat → Bool} {lhs : BitVec 32} {xs : List Nat} {self_i : Nat}
    (hsi : self_i < xs.length) (hget : xs[self_i]'hsi = (lhs &&& ~~~1#32).toNat)
    (hxeq : evalLitVal α lhs.toNat = xorEvalList α xs) :
    decide ((lhs &&& 1#32) ≠ 0#32) = xorEvalList α (xs.eraseIdx self_i) := by
  have hperm : List.Perm xs ((lhs &&& ~~~1#32).toNat :: xs.eraseIdx self_i) := by
    rw [← hget]; exact list_perm_cons_eraseIdx xs self_i hsi
  rw [xorEvalList_perm α hperm, xorEvalList_cons, bv32_bit0_eval α lhs] at hxeq
  generalize hb : decide ((lhs &&& 1#32) ≠ 0#32) = b at hxeq ⊢
  cases h1 : evalLitVal α (lhs &&& ~~~1#32).toNat <;> cases b <;>
    cases h2 : xorEvalList α (xs.eraseIdx self_i) <;> simp_all

theorem fid_xor_cancel_unsat {F_cur : List (List Nat)} {lhs : BitVec 32}
    (h : ∀ α, (cnfOfClauses F_cur).Sat α → decide ((lhs &&& 1#32) ≠ 0#32) = false)
    (hnz : (lhs &&& 1#32) ≠ 0#32) : (cnfOfClauses F_cur).Unsat := by
  intro α
  cases hev : (cnfOfClauses F_cur).eval α with
  | false => rfl
  | true =>
    have h1 := h α hev
    simp [hnz] at h1

theorem fid_xor_cancel_unit {F_cur : List (List Nat)} {lhs t0 : BitVec 32}
    (h : ∀ α, (cnfOfClauses F_cur).Sat α →
      decide ((lhs &&& 1#32) ≠ 0#32) = evalLitVal α t0.toNat) :
    (cnfOfClauses F_cur).EntailsClause
      (cnfClause [(t0 ^^^ (1#32 ^^^ (lhs &&& 1#32))).toNat]) := by
  rw [CNF.entails_clause_def]; intro α hα
  rw [← clauseEvalVal_iff, clauseEvalVal]
  simp only [List.any_cons, List.any_nil, Bool.or_false]
  have h1 := h α hα
  have h01 : (lhs &&& 1#32) = 0#32 ∨ (lhs &&& 1#32) = 1#32 := by
    have hlt : (lhs &&& 1#32).toNat < 2 := by
      rw [BitVec.toNat_and, show (1#32 : BitVec 32).toNat = 1 from rfl, Nat.and_one_is_mod]
      exact Nat.mod_lt _ (by decide)
    rcases (by omega : (lhs &&& 1#32).toNat = 0 ∨ (lhs &&& 1#32).toNat = 1) with h0 | h1'
    · exact Or.inl (BitVec.eq_of_toNat_eq h0)
    · exact Or.inr (BitVec.eq_of_toNat_eq h1')
  rcases h01 with hz | ho
  · rw [hz] at h1 ⊢
    rw [show (1#32 ^^^ 0#32 : BitVec 32) = 1#32 from rfl,
      show (t0 ^^^ 1#32).toNat = litNeg t0.toNat from bv32_xor1_litNeg t0, evalLitVal_litNeg]
    simp at h1; simp [h1]
  · rw [ho] at h1 ⊢
    rw [show (1#32 ^^^ 1#32 : BitVec 32) = 0#32 from rfl, BitVec.xor_zero]
    simp at h1; exact h1

theorem fid_xor_cancel_equiv {F_cur : List (List Nat)} {lhs t0 t1 : BitVec 32}
    (h : ∀ α, (cnfOfClauses F_cur).Sat α →
      decide ((lhs &&& 1#32) ≠ 0#32) = (evalLitVal α t0.toNat != evalLitVal α t1.toNat)) :
    LitEquiv (cnfOfClauses F_cur) (t0 ^^^ (lhs &&& 1#32)).toNat t1.toNat := by
  have hev : ∀ α, (cnfOfClauses F_cur).Sat α →
      evalLitVal α (t0 ^^^ (lhs &&& 1#32)).toNat = evalLitVal α t1.toNat := by
    intro α hα
    have h1 := h α hα
    have h01 : (lhs &&& 1#32) = 0#32 ∨ (lhs &&& 1#32) = 1#32 := by
      have hlt : (lhs &&& 1#32).toNat < 2 := by
        rw [BitVec.toNat_and, show (1#32 : BitVec 32).toNat = 1 from rfl, Nat.and_one_is_mod]
        exact Nat.mod_lt _ (by decide)
      rcases (by omega : (lhs &&& 1#32).toNat = 0 ∨ (lhs &&& 1#32).toNat = 1) with h0 | h1'
      · exact Or.inl (BitVec.eq_of_toNat_eq h0)
      · exact Or.inr (BitVec.eq_of_toNat_eq h1')
    rcases h01 with hz | ho
    · rw [hz] at h1 ⊢; simp only [BitVec.xor_zero]
      cases ht0 : evalLitVal α t0.toNat <;> cases ht1 : evalLitVal α t1.toNat <;> simp_all
    · rw [ho] at h1 ⊢
      rw [show (t0 ^^^ 1#32).toNat = litNeg t0.toNat from bv32_xor1_litNeg t0, evalLitVal_litNeg]
      cases ht0 : evalLitVal α t0.toNat <;> cases ht1 : evalLitVal α t1.toNat <;> simp_all
  constructor
  · rw [CNF.entails_clause_def]; intro α hα; rw [← clauseEvalVal_iff, clauseEvalVal]
    simp only [List.any_cons, List.any_nil, Bool.or_false, evalLitVal_litNeg, hev α hα]
    cases evalLitVal α t1.toNat <;> rfl
  · rw [CNF.entails_clause_def]; intro α hα; rw [← clauseEvalVal_iff, clauseEvalVal]
    simp only [List.any_cons, List.any_nil, Bool.or_false, evalLitVal_litNeg, hev α hα]
    cases evalLitVal α t1.toNat <;> rfl

/-- ITE-to-XOR rewrite (`congruence.c:2009-2052`): `ITE(c, t, ~t) = ~(c ^ t)`. -/
theorem fid_ite_to_xor_sem {F_cur : List (List Nat)} {lhs c t : BitVec 32}
    (hite : IteGateDef (cnfOfClauses F_cur) lhs.toNat c.toNat t.toNat (litNeg t.toNat)) :
    let lhs' := lhs ^^^ ((1#32 ^^^ c ^^^ t) &&& 1#32)
    ∀ α, (cnfOfClauses F_cur).Sat α →
      evalLitVal α lhs'.toNat =
        (evalLitVal α (c &&& ~~~1#32).toNat != evalLitVal α (t &&& ~~~1#32).toNat) := by
  intro lhs' α hα
  have hi := iteGateDef_eval hα hite
  rw [evalLitVal_litNeg] at hi
  have hbit : ∀ y : BitVec 32, decide ((y &&& 1#32) ≠ 0#32) = y.getLsbD 0 := fun y => by
    have h0 : (y &&& 1#32).toNat = if y.getLsbD 0 then 1 else 0 := by
      rw [BitVec.toNat_and, show (1#32 : BitVec 32).toNat = 1 from rfl, Nat.and_one_is_mod,
        BitVec.getLsbD, Nat.testBit_zero]
      cases hm : y.toNat % 2 == 1 <;> simp_all <;> omega
    cases hg : y.getLsbD 0
    · simp only [hg, Bool.false_eq_true, ↓reduceIte] at h0
      have hz : (y &&& 1#32) = 0#32 := BitVec.eq_of_toNat_eq h0; simp [hz]
    · simp only [hg, ↓reduceIte] at h0
      have hnz : (y &&& 1#32) ≠ 0#32 := fun hz => by
        have := congrArg BitVec.toNat hz; rw [h0] at this; cases this
      simp [hnz]
  have hl' : evalLitVal α lhs'.toNat =
      (evalLitVal α lhs.toNat != ((true != c.getLsbD 0) != t.getLsbD 0)) := by
    rw [bv32_bit0_eval α lhs', bv32_bit0_eval α lhs, hbit, hbit]
    have h1 : (lhs' &&& ~~~1#32) = (lhs &&& ~~~1#32) := by
      apply BitVec.eq_of_getLsbD_eq; intro i hi'
      simp only [lhs', BitVec.getLsbD_and, BitVec.getLsbD_xor, BitVec.getLsbD_not]
      cases i with
      | zero => simp [hi']
      | succ k => simp [hi']
    have h2 : lhs'.getLsbD 0 = (lhs.getLsbD 0 != ((true != c.getLsbD 0) != t.getLsbD 0)) := by
      simp [lhs']
    rw [h1, h2]
    cases evalLitVal α (lhs &&& ~~~1#32).toNat <;> cases lhs.getLsbD 0 <;>
      cases c.getLsbD 0 <;> cases t.getLsbD 0 <;> rfl
  rw [hl', hi]
  rw [bv32_bit0_eval α c, bv32_bit0_eval α t, hbit, hbit]
  cases evalLitVal α (c &&& ~~~1#32).toNat <;> cases evalLitVal α (t &&& ~~~1#32).toNat <;>
    cases c.getLsbD 0 <;> cases t.getLsbD 0 <;> rfl

/-- ITE-to-AND simplifications (`congruence.c:1872-2055`). -/
theorem fid_ite_and_vt_true {F_cur : List (List Nat)} {lhs c t e : Nat}
    (hite : IteGateDef (cnfOfClauses F_cur) lhs c t e)
    (ht : ∀ α, (cnfOfClauses F_cur).Sat α → evalLitVal α t = true) :
    ∀ α, (cnfOfClauses F_cur).Sat α →
      evalLitVal α (litNeg lhs) = (evalLitVal α (litNeg c) && evalLitVal α (litNeg e)) := by
  intro α hα; have hi := iteGateDef_eval hα hite; rw [ht α hα] at hi
  simp only [evalLitVal_litNeg, hi]; cases evalLitVal α c <;> cases evalLitVal α e <;> rfl

theorem fid_ite_and_vt_false {F_cur : List (List Nat)} {lhs c t e : Nat}
    (hite : IteGateDef (cnfOfClauses F_cur) lhs c t e)
    (ht : ∀ α, (cnfOfClauses F_cur).Sat α → evalLitVal α t = false) :
    ∀ α, (cnfOfClauses F_cur).Sat α →
      evalLitVal α lhs = (evalLitVal α (litNeg c) && evalLitVal α e) := fun α hα => by
  have hi := iteGateDef_eval hα hite; rw [ht α hα] at hi
  simp only [evalLitVal_litNeg, hi]; cases evalLitVal α c <;> cases evalLitVal α e <;> rfl

theorem fid_ite_and_ve_true {F_cur : List (List Nat)} {lhs c t e : Nat}
    (hite : IteGateDef (cnfOfClauses F_cur) lhs c t e)
    (he : ∀ α, (cnfOfClauses F_cur).Sat α → evalLitVal α e = true) :
    ∀ α, (cnfOfClauses F_cur).Sat α →
      evalLitVal α (litNeg lhs) = (evalLitVal α c && evalLitVal α (litNeg t)) := fun α hα => by
  have hi := iteGateDef_eval hα hite; rw [he α hα] at hi
  simp only [evalLitVal_litNeg, hi]; cases evalLitVal α c <;> cases evalLitVal α t <;> rfl

theorem fid_ite_and_ve_false {F_cur : List (List Nat)} {lhs c t e : Nat}
    (hite : IteGateDef (cnfOfClauses F_cur) lhs c t e)
    (he : ∀ α, (cnfOfClauses F_cur).Sat α → evalLitVal α e = false) :
    ∀ α, (cnfOfClauses F_cur).Sat α →
      evalLitVal α lhs = (evalLitVal α c && evalLitVal α t) := fun α hα => by
  have hi := iteGateDef_eval hα hite; rw [he α hα] at hi
  simp only [hi]; cases evalLitVal α c <;> cases evalLitVal α t <;> rfl

theorem fid_ite_and_c_eq_t {F_cur : List (List Nat)} {lhs c e : Nat}
    (hite : IteGateDef (cnfOfClauses F_cur) lhs c c e) :
    ∀ α, (cnfOfClauses F_cur).Sat α →
      evalLitVal α (litNeg lhs) = (evalLitVal α (litNeg c) && evalLitVal α (litNeg e)) := by
  intro α hα; have hi := iteGateDef_eval hα hite
  simp only [evalLitVal_litNeg, hi]; cases evalLitVal α c <;> cases evalLitVal α e <;> rfl

theorem fid_ite_and_c_eq_nt {F_cur : List (List Nat)} {lhs c e : Nat}
    (hite : IteGateDef (cnfOfClauses F_cur) lhs c (litNeg c) e) :
    ∀ α, (cnfOfClauses F_cur).Sat α →
      evalLitVal α lhs = (evalLitVal α (litNeg c) && evalLitVal α e) := fun α hα => by
  have hi := iteGateDef_eval hα hite
  simp only [evalLitVal_litNeg, hi]; cases evalLitVal α c <;> cases evalLitVal α e <;> rfl

theorem fid_ite_and_c_eq_ne {F_cur : List (List Nat)} {lhs c t : Nat}
    (hite : IteGateDef (cnfOfClauses F_cur) lhs c t (litNeg c)) :
    ∀ α, (cnfOfClauses F_cur).Sat α →
      evalLitVal α (litNeg lhs) = (evalLitVal α c && evalLitVal α (litNeg t)) := fun α hα => by
  have hi := iteGateDef_eval hα hite
  simp only [evalLitVal_litNeg, hi]; cases evalLitVal α c <;> cases evalLitVal α t <;> rfl

theorem fid_ite_and_c_eq_e {F_cur : List (List Nat)} {lhs c t : Nat}
    (hite : IteGateDef (cnfOfClauses F_cur) lhs c t c) :
    ∀ α, (cnfOfClauses F_cur).Sat α →
      evalLitVal α lhs = (evalLitVal α c && evalLitVal α t) := fun α hα => by
  have hi := iteGateDef_eval hα hite
  simp only [hi]; cases evalLitVal α c <;> cases evalLitVal α t <;> rfl

/-- Swapping two `(u32, u32)` pairs inside `a[0 ..< 2*n)` preserves `FidPairsOk P` and all
elements at indices `≥ 2*n`. -/
theorem fidPairsOk_swap {P : BitVec 32 → BitVec 32 → Prop} {a : List (BitVec 32)} {n i j : Nat}
    (hok : FidPairsOk P a n) (hi : i < n) (hj : j < n) (hlen : 2 * n ≤ a.length) :
    let si := a[2 * i]?.getD 0#32; let ri := a[2 * i + 1]?.getD 0#32
    let sj := a[2 * j]?.getD 0#32; let rj := a[2 * j + 1]?.getD 0#32
    let a' := (((a.set (2 * i) sj).set (2 * i + 1) rj).set (2 * j) si).set (2 * j + 1) ri
    a'.length = a.length ∧ FidPairsOk P a' n ∧
      (∀ idx, 2 * n ≤ idx → a'[idx]? = a[idx]?) := by
  intro si ri sj rj a'
  refine ⟨by simp [a'], ?_, fun idx hidx => by
    simp only [a']; repeat rw [List.getElem?_set_ne (by omega)]⟩
  intro k hk
  by_cases hkj : k = j
  · subst hkj
    have h0 : a'[2 * k]? = some si := by
      simp only [a']; rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by simp; omega)]
    have h1 : a'[2 * k + 1]? = some ri := by
      simp only [a']; rw [List.getElem?_set_self (by simp; omega)]
    rw [h0, h1, Option.getD_some, Option.getD_some]; exact hok i hi
  · by_cases hki : k = i
    · subst hki
      have h0 : a'[2 * k]? = some sj := by
        simp only [a']
        rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
          List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega)]
      have h1 : a'[2 * k + 1]? = some rj := by
        simp only [a']
        rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
          List.getElem?_set_self (by simp; omega)]
      rw [h0, h1, Option.getD_some, Option.getD_some]; exact hok j hj
    · have h0 : a'[2 * k]? = a[2 * k]? := by
        simp only [a']; repeat rw [List.getElem?_set_ne (by omega)]
      have h1 : a'[2 * k + 1]? = a[2 * k + 1]? := by
        simp only [a']; repeat rw [List.getElem?_set_ne (by omega)]
      rw [h0, h1]; exact hok k hk

theorem pow2_16_mul_le_1m (k : Nat) (hk : k ≤ 16) : 16 * 2 ^ k ≤ fidCongHashMaxSz := by
  have hpow : 2 ^ k ≤ 2 ^ 16 := Nat.pow_le_pow_right (by omega) hk
  have h16 : (2 : Nat) ^ 16 = 65536 := by decide
  unfold fidCongHashMaxSz; omega

end PureSem

/-! ## 4. Owned Function `Spec` Contracts (`FullFidelityCong`) -/

section Specs

/-- `full_cong_emit_xor` parameterized over `maxA ≤ 64`. -/
def fidCongEmitXorSpec : Spec [i64, i64, i32, i32, i32] [i64] :=
  fun (scr_ptr, g_len, x0, x1, x2, ()) m Q _ =>
    ∃ (maxA : Nat) (F_cur : List (List Nat)) (cur_vars : Nat) (scr : List (BitVec 32))
      (R : Mem 64 → Prop),
      2 ≤ maxA ∧ maxA ≤ 64 ∧
      x0.toNat < 2 * cur_vars ∧ x1.toNat < 2 * cur_vars ∧ x2.toNat < 2 * cur_vars ∧
      2 ≤ cur_vars ∧ g_len.toNat + 4 ≤ scr.length ∧ scr.length < 2 ^ 32 ∧
      XorGateDef (cnfOfClauses F_cur) (litNeg x0.toNat) x1.toNat x2.toNat ∧
      FidGateSeqOk maxA F_cur cur_vars scr g_len.toNat 0 ∧
      (array (t := i32) scr_ptr scr ⋆ R) m ∧
      ∀ (scr' : List (BitVec 32)) (m' : Mem 64),
        scr'.length = scr.length →
        (∀ idx < g_len.toNat, scr'[idx]? = scr[idx]?) →
        FidGateSeqOk maxA F_cur cur_vars scr' (g_len.toNat + 4) 0 →
        (array (t := i32) scr_ptr scr' ⋆ R) m' → Q (g_len + 4#64, ()) m'

/-- `full_cong_emit_xor4` (`GAP-CONG-02` 4-literal / `k=3`-input XOR normalizer). -/
def fidCongEmitXor4Spec : Spec [i64, i64, i32, i32, i32, i32] [i64] :=
  fun (scr_ptr, g_len, x0, x1, x2, x3, ()) m Q _ =>
    ∃ (maxA : Nat) (F_cur : List (List Nat)) (cur_vars : Nat) (scr : List (BitVec 32))
      (R : Mem 64 → Prop),
      3 ≤ maxA ∧ maxA ≤ 64 ∧
      x0.toNat < 2 * cur_vars ∧ x1.toNat < 2 * cur_vars ∧
      x2.toNat < 2 * cur_vars ∧ x3.toNat < 2 * cur_vars ∧
      3 ≤ cur_vars ∧ g_len.toNat + 5 ≤ scr.length ∧ scr.length < 2 ^ 32 ∧
      XorListGateDef (cnfOfClauses F_cur) (litNeg x0.toNat) [x1.toNat, x2.toNat, x3.toNat] ∧
      FidGateSeqOk maxA F_cur cur_vars scr g_len.toNat 0 ∧
      (array (t := i32) scr_ptr scr ⋆ R) m ∧
      ∀ (scr' : List (BitVec 32)) (m' : Mem 64),
        scr'.length = scr.length →
        (∀ idx < g_len.toNat, scr'[idx]? = scr[idx]?) →
        FidGateSeqOk maxA F_cur cur_vars scr' (g_len.toNat + 5) 0 →
        (array (t := i32) scr_ptr scr' ⋆ R) m' → Q (g_len + 5#64, ()) m'

/-- `full_cong_extract_xor_k` parameterized over `maxA ≤ 64`. -/
def fidCongExtractXorKSpec : Spec [i64, i32, i32, i64, i64] [i64] :=
  fun (h, k, neg_p, g_len, g_cap, ()) m Q _ =>
    ∃ (maxA : Nat) (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (R : Mem 64 → Prop),
      4 ≤ maxA ∧ maxA ≤ 64 ∧
      h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
      FullLitMarksClear c s ∧ FullArenaVarsNodup s ∧ s.core.cur_level = 0 ∧
      3 ≤ k.toNat ∧ k.toNat ≤ 5 ∧ k.toNat ≤ s.core.cur_vars ∧
      g_len.toNat ≤ g_cap.toNat ∧ g_cap.toNat ≤ c.scratch_cap ∧
      FidGateSeqOk maxA F_cur s.core.cur_vars s.scratch.scratch_buf g_len.toNat 0 ∧
      (∀ i < k.toNat, (s.scratch.work_stk2[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
      (neg_p &&& 1#32).toNat = (List.range k.toNat).foldl
        (fun acc i => acc ^^^ ((s.scratch.work_stk2[i]?.getD 0#32).toNat % 2)) 0 ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause
        ((List.range k.toNat).map fun i => (s.scratch.work_stk2[i]?.getD 0#32).toNat)) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ret : BitVec 64) (s' : FullState) (m' : Mem 64),
        s'.LengthsOk c →
        { s'.core with tmp := s.core.tmp, lit_mark := s.core.lit_mark } = s.core →
        { s'.scratch with scratch_buf := s.scratch.scratch_buf } = s.scratch →
        FullLitMarksClear c s' →
        g_len.toNat ≤ ret.toNat → ret.toNat ≤ g_cap.toNat →
        (∀ idx < g_len.toNat, s'.scratch.scratch_buf[idx]? = s.scratch.scratch_buf[idx]?) →
        FidGateSeqOk maxA F_cur s.core.cur_vars s'.scratch.scratch_buf ret.toNat 0 →
        (FullMem c s' ⋆ R) m' → Q (ret, ()) m'

/-- `full_cong_try_xor_ite` parameterized over `maxA ≤ 64`. -/
def fidCongTryXorIteSpec : Spec [i64, i32, i32, i32, i64, i64] [i64] :=
  fun (h, a, b, cl, g_len, g_cap, ()) m Q _ =>
    ∃ (maxA : Nat) (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (R : Mem 64 → Prop),
      2 ≤ maxA ∧ maxA ≤ 64 ∧
      h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
      FullArenaVarsNodup s ∧ s.core.cur_level = 0 ∧
      a.toNat < 2 * s.core.cur_vars ∧ b.toNat < 2 * s.core.cur_vars ∧
      cl.toNat < 2 * s.core.cur_vars ∧
      a.toNat / 2 ≠ b.toNat / 2 ∧ a.toNat / 2 ≠ cl.toNat / 2 ∧ b.toNat / 2 ≠ cl.toNat / 2 ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause [a.toNat, b.toNat, cl.toNat]) ∧
      g_len.toNat + 5 ≤ g_cap.toNat ∧ g_cap.toNat ≤ c.scratch_cap ∧
      FidGateSeqOk maxA F_cur s.core.cur_vars s.scratch.scratch_buf g_len.toNat 0 ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ret : BitVec 64) (scr' : List (BitVec 32)) (m' : Mem 64),
        let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
        scr'.length = c.scratch_cap →
        g_len.toNat ≤ ret.toNat → ret.toNat ≤ g_cap.toNat →
        (∀ idx < g_len.toNat, scr'[idx]? = s.scratch.scratch_buf[idx]?) →
        FidGateSeqOk maxA F_cur s.core.cur_vars scr' ret.toNat 0 →
        (FullMem c s' ⋆ R) m' → Q (ret, ()) m'

/-- `full_cong_extract` emitting `FidGateSeqOk 64` (wide AND up to arity `64`, XOR `k=3..5`). -/
def fidCongExtractSpec : Spec [i64, i64, i64] [i64] := fun (h, g_cap, _tick_lim, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ g_cap.toNat ≤ c.scratch_cap ∧ (FullMem c s ⋆ R) m ∧
    ∀ (ret : BitVec 64) (s' : FullState) (m' : Mem 64),
      FullDenseInvW c F0 F_cur s' →
      s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
      s'.core.repr = s.core.repr → s'.core.inconsistent = s.core.inconsistent →
      ret.toNat ≤ g_cap.toNat →
      FidGateSeqOk 64 F_cur s.core.cur_vars s'.scratch.scratch_buf ret.toNat 0 →
      (FullMem c s' ⋆ R) m' → Q (ret, ()) m'

/-- `full_cong_and_match` parameterized over `maxA ≤ 64` (`GAP-CONG-01` 64-bit mask). -/
def fidCongAndMatchSpec : Spec [i64, i32, i32] [.bool] := fun (h, ent, ua, ()) m Q _ =>
  ∃ (maxA : Nat) (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
    (scr0 : List (BitVec 32)) (g_len : Nat) (R : Mem 64 → Prop),
    maxA ≤ 64 ∧ h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
    s.core.cur_level = 0 ∧ FullCongReprInv F_cur (2 * s.core.cur_vars) s.core.repr ∧
    g_len ≤ c.scratch_cap ∧
    (∀ idx < g_len, s.scratch.scratch_buf[idx]? = scr0[idx]?) ∧
    FidGateAt maxA F_cur s.core.cur_vars scr0 g_len ent.toNat ∧
    (scr0[ent.toNat + 1]?.getD 0#32 >>> 28) = 0#32 ∧
    ua.toNat ≤ s.core.cur_vars ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) repr' m',
      let s' : FullState := { s with core := { s.core with repr := repr' } }
      repr'.length = 2 * c.max_vars →
      FullCongReprInv F_cur (2 * s.core.cur_vars) repr' →
      (ok = true → 2 ≤ ua.toNat ∧ ua.toNat ≤ 64 ∧
        ∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α →
          evalLitVal α (scr0[ent.toNat]?.getD 0#32).toNat =
            (List.range ua.toNat).all fun k =>
              evalLitVal α (s.core.tmp[k]?.getD 0#32).toNat) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

/-- `full_cong_eval_gate` parameterized over `maxA ≤ 64` (`maxA = 31` recovers `m8CongEvalGateSpec`,
`maxA = 64` supports wide AND-64, XOR LHS self-cancel, and ITE-to-AND/XOR rewrites). -/
def fidCongEvalGateSpec : Spec [i64, i64, i64, i64, i32, i64] [i64] :=
  fun (h, g, ht_off, ht_sz, _next_ep, ctrl_off, ()) m Q _ =>
    ∃ (maxA : Nat) (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (scr0 : List (BitVec 32)) (g_len : Nat) (R : Mem 64 → Prop),
      maxA ≤ 64 ∧ h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧
      FullCongReprInv F_cur (2 * s.core.cur_vars) s.core.repr ∧
      0 < ht_sz.toNat ∧ ht_sz.toNat < 2 ^ 30 ∧
      g.toNat < g_len ∧ g_len ≤ ht_off.toNat ∧ ht_off.toNat + ht_sz.toNat ≤ c.scratch_cap ∧
      (∀ idx < g_len, s.scratch.scratch_buf[idx]? = scr0[idx]?) ∧
      FidGateAt maxA F_cur s.core.cur_vars scr0 g_len g.toNat ∧
      FidCongHtInv maxA F_cur s.core.cur_vars scr0 s.scratch.scratch_buf
        g_len ht_off.toNat ht_sz.toNat ∧
      M8QueueCtx c s.scratch.scratch_buf g_len ctrl_off.toNat ht_off.toNat ht_sz.toNat ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (r : BitVec 64) s' m',
        FullDenseInvW c F0 F_cur s' →
        s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
        s'.core.arena = s.core.arena → s'.core.arena_len = s.core.arena_len →
        FullCongReprInv F_cur (2 * s'.core.cur_vars) s'.core.repr →
        (∀ idx < g_len, s'.scratch.scratch_buf[idx]? = scr0[idx]?) →
        FidCongHtInv maxA F_cur s'.core.cur_vars scr0 s'.scratch.scratch_buf
          g_len ht_off.toNat ht_sz.toNat →
        M8QueueCtx c s'.scratch.scratch_buf g_len ctrl_off.toNat ht_off.toNat ht_sz.toNat →
        ((r &&& 2#64) = 0#64 →
          (∀ idx < c.scratch_cap, idx < ht_off.toNat →
            (ctrl_off.toNat = c.scratch_cap →
              s'.scratch.scratch_buf[idx]? = s.scratch.scratch_buf[idx]?) ∧
            (∀ occ_bkt bkt_off inq_off q_off,
              M8CtrlLayout c s.scratch.scratch_buf g_len ctrl_off.toNat occ_bkt bkt_off inq_off
                q_off ht_off.toNat ht_sz.toNat →
              idx ≠ ctrl_off.toNat + 5 →
              ¬ (q_off ≤ idx ∧ idx < q_off + occ_bkt) →
              ¬ (inq_off ≤ idx ∧ idx < inq_off + occ_bkt) →
              s'.scratch.scratch_buf[idx]? = s.scratch.scratch_buf[idx]?))) →
        ((r &&& 2#64) ≠ 0#64 → F0.Unsat) →
        (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-- `full_cong_worklist` supporting `FidGateSeqOk 64` and dynamic in-place HT doubling up to
`1,048,576` (`1M`) buckets (`GAP-CONG-03`). -/
def fidCongWorklistSpec : Spec [i64, i64, i64, i64] [i64] :=
  fun (h, g_len, ctrl_off, _tick_lim, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (scr0 : List (BitVec 32)) (occ_bkt bkt_off inq_off q_off ht_off ht_sz : Nat)
      (R : Mem 64 → Prop),
      h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧
      FullCongReprInv F_cur (2 * s.core.cur_vars) s.core.repr ∧
      0 < g_len.toNat ∧ ht_sz ≤ fidCongHashMaxSz ∧
      M8CtrlLayout c s.scratch.scratch_buf g_len.toNat ctrl_off.toNat occ_bkt bkt_off inq_off
        q_off ht_off ht_sz ∧
      FidGateSeqOk 64 F_cur s.core.cur_vars scr0 g_len.toNat 0 ∧
      (∀ idx < g_len.toNat, s.scratch.scratch_buf[idx]? = scr0[idx]?) ∧
      FidCongHtInv 64 F_cur s.core.cur_vars scr0 s.scratch.scratch_buf g_len.toNat ht_off ht_sz ∧
      (FullMem c s ⋆ R) m ∧
      ∀ r s' m',
        FullDenseInvW c F0 F_cur s' →
        s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
        FullCongReprInv F_cur (2 * s'.core.cur_vars) s'.core.repr →
        (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
        (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-- `full_cong_sift_pairs_fid`: swaps `(u32, u32)` pairs inside `a[0 ..< 2*n)`, preserving any
pointwise pair predicate `P` and tail indices `≥ 2*n`. -/
def fidCongSiftPairsSpec : Spec [i64, i64, i64] [] := fun (ap, start, n, ()) m Q _ =>
  ∃ (P : BitVec 32 → BitVec 32 → Prop) (a : List (BitVec 32)) (R : Mem 64 → Prop),
    start.toNat < n.toNat ∧ 2 * n.toNat ≤ a.length ∧ a.length < 2 ^ 61 ∧
    FidPairsOk P a n.toNat ∧ (array (t := i32) ap a ⋆ R) m ∧
    ∀ a' m',
      a'.length = a.length → FidPairsOk P a' n.toNat →
      (∀ idx, 2 * n.toNat ≤ idx → a'[idx]? = a[idx]?) →
      (array (t := i32) ap a' ⋆ R) m' → Q () m'

/-- `full_cong_sort_pairs_fid`: in-place heapsort of `(u32, u32)` pairs in `a[0 ..< 2*n)`. -/
def fidCongSortPairsSpec : Spec [i64, i64] [] := fun (ap, n, ()) m Q _ =>
  ∃ (P : BitVec 32 → BitVec 32 → Prop) (a : List (BitVec 32)) (R : Mem 64 → Prop),
    2 * n.toNat ≤ a.length ∧ a.length < 2 ^ 61 ∧
    FidPairsOk P a n.toNat ∧ (array (t := i32) ap a ⋆ R) m ∧
    ∀ a' m',
      a'.length = a.length → FidPairsOk P a' n.toNat →
      (∀ idx, 2 * n.toNat ≤ idx → a'[idx]? = a[idx]?) →
      (array (t := i32) ap a' ⋆ R) m' → Q () m'

/-- `full_cong_copy_condbin_m7` (`GAP-CONG-04`, scans `sz >= 3u` clauses with `3` unassigned). -/
abbrev fidCongCopyCondbinSpec : Spec [i64, i32, i64, i64] [i64] := m7CopyCondbinSpec

/-- `full_cong_merge_condeq_m7` parameterized over `maxA ≤ 64` (emits trivial `e == t` ITEs). -/
def fidCongMergeCondeqSpec : Spec [i64, i32, i64, i64, i32, i32] [i32] :=
  fun (h, cond, pos_n, neg_n, g_len, g_cap, ()) m Q _ =>
    ∃ (maxA : Nat) (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (wk1 wk2 : List (BitVec 64)) (R : Mem 64 → Prop),
      3 ≤ maxA ∧ maxA ≤ 64 ∧
      h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
      3 ≤ s.core.cur_vars ∧ cond.toNat < 2 * s.core.cur_vars ∧
      g_cap.toNat ≤ c.scratch_cap ∧
      pos_n.toNat ≤ wk1.length ∧ neg_n.toNat ≤ wk2.length ∧
      wk1.length < 2 ^ 61 ∧ wk2.length < 2 ^ 61 ∧
      (∀ k < pos_n.toNat,
        CondEqElemOk F_cur s.core.cur_vars (litNeg cond.toNat) (wk1[k]?.getD 0#64)) ∧
      (∀ k < neg_n.toNat,
        CondEqElemOk F_cur s.core.cur_vars cond.toNat (wk2[k]?.getD 0#64)) ∧
      FidGateSeqOk maxA F_cur s.core.cur_vars s.scratch.scratch_buf g_len.toNat 0 ∧
      (FullMemNoWks3 c s ⋆ array64 c.pWorkStk1 wk1 ⋆ array64 c.pWorkStk2 wk2 ⋆ R) m ∧
      ∀ (ret : BitVec 32) (scr' : List (BitVec 32)) m',
        let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
        scr'.length = c.scratch_cap →
        (g_len.toNat ≤ g_cap.toNat → g_len.toNat ≤ ret.toNat ∧ ret.toNat ≤ g_cap.toNat) →
        (∀ idx < g_len.toNat, scr'[idx]? = s.scratch.scratch_buf[idx]?) →
        FidGateSeqOk maxA F_cur s.core.cur_vars scr' ret.toNat 0 →
        (FullMemNoWks3 c s' ⋆ array64 c.pWorkStk1 wk1 ⋆ array64 c.pWorkStk2 wk2 ⋆ R) m' →
        Q (ret, ()) m'

/-- `full_cong_extract_ite_all_m7` parameterized over `maxA ≤ 64`. -/
def fidCongExtractIteAllSpec : Spec [i64, i32, i32, i64] [i32] :=
  fun (h, g_len, g_cap, _tick_lim, ()) m Q _ =>
    ∃ (maxA : Nat) (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (R : Mem 64 → Prop),
      3 ≤ maxA ∧ maxA ≤ 64 ∧
      h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧
      g_len.toNat ≤ g_cap.toNat ∧ g_cap.toNat ≤ c.scratch_cap ∧
      FidGateSeqOk maxA F_cur s.core.cur_vars s.scratch.scratch_buf g_len.toNat 0 ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ret : BitVec 32) (s' : FullState) m',
        FullDenseInvW c F0 F_cur s' →
        s'.core = s.core →
        s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
        s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
        s'.scratch.extend_stk = s.scratch.extend_stk →
        s'.scratch.extend_len = s.scratch.extend_len →
        s'.scratch.last_learned = s.scratch.last_learned →
        s'.scratch.ant_sz = s.scratch.ant_sz →
        s'.scratch.res_sz = s.scratch.res_sz →
        g_len.toNat ≤ ret.toNat → ret.toNat ≤ g_cap.toNat →
        (∀ idx < g_len.toNat, s'.scratch.scratch_buf[idx]? = s.scratch.scratch_buf[idx]?) →
        FidGateSeqOk maxA F_cur s.core.cur_vars s'.scratch.scratch_buf ret.toNat 0 →
        (FullMem c s' ⋆ R) m' → Q (ret, ()) m'

/-- Upgraded `FullM7CongHash` specs (`arity ≤ 64`, `ht_sz ≤ 1,048,576`). -/
abbrev fidCongHtHashEntSpec : Spec [i64, i32, i64] [i64] := m7CongHtHashEntSpec

def fidCongHtInitSpec : Spec [i64, i64, i64, i64] [i64] :=
  fun (h, ctrl_off, ht_off, _max_sz, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
      ∀ (ret : BitVec 64) (scr' : List (BitVec 32)) (rsz' : BitVec 64) (m' : Mem 64),
        let s' : FullState :=
          { s with scratch := { s.scratch with scratch_buf := scr', res_sz := rsz' } }
        scr'.length = c.scratch_cap → s'.LengthsOk c →
        PreservesCoreSlice FullState.core s s' → FullExtScratchPres s s' →
        (ret ≠ 0#64 →
          FidCongHtCtrlOk c scr' ctrl_off.toNat ht_off.toNat ret.toNat ∧ rsz' = 0#64 ∧
          (∀ j < ret.toNat, scr'[ht_off.toNat + j]? = some 0xFFFFFFFF#32)) →
        (FullMem c s' ⋆ R) m' → Q (ret, ()) m'

def fidCongHtGrowSpec : Spec [i64, i64] [i64] :=
  fun (h, ctrl_off, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
      ∀ (ret : BitVec 64) (scr' : List (BitVec 32)) (m' : Mem 64),
        let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
        scr'.length = c.scratch_cap → s'.LengthsOk c →
        PreservesCoreSlice FullState.core s s' → FullExtScratchPres s s' →
        (∀ ht_off old_sz,
          FidCongHtCtrlOk c s.scratch.scratch_buf ctrl_off.toNat ht_off old_sz →
          (old_sz < fidCongHashMaxSz → ht_off + 2 * old_sz ≤ c.scratch_cap →
            ret.toNat = 2 * old_sz ∧
            FidCongHtCtrlOk c scr' ctrl_off.toNat ht_off (2 * old_sz) ∧
            (∀ idx < ht_off, idx ≠ ctrl_off.toNat + 7 →
              scr'[idx]? = s.scratch.scratch_buf[idx]?) ∧
            (∀ j < 2 * old_sz,
              scr'[ht_off + j]? = some 0xFFFFFFFF#32 ∨
              ∃ k0 < old_sz, ∃ raw : BitVec 32,
                s.scratch.scratch_buf[ht_off + k0]? = some raw ∧
                raw ≠ 0xFFFFFFFF#32 ∧
                scr'[ht_off + j]? = some (raw &&& 0x7FFFFFFF#32)))) →
        (FullMem c s' ⋆ R) m' → Q (ret, ()) m'

def fidCongHtGrowClearSpec : Spec [i64, i64] [i64] :=
  fun (h, ctrl_off, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
      ∀ (ret : BitVec 64) (scr' : List (BitVec 32)) (rsz' : BitVec 64) (m' : Mem 64),
        let s' : FullState :=
          { s with scratch := { s.scratch with scratch_buf := scr', res_sz := rsz' } }
        scr'.length = c.scratch_cap → s'.LengthsOk c →
        PreservesCoreSlice FullState.core s s' → FullExtScratchPres s s' →
        (∀ ht_off old_sz,
          FidCongHtCtrlOk c s.scratch.scratch_buf ctrl_off.toNat ht_off old_sz →
          (old_sz < fidCongHashMaxSz → ht_off + 2 * old_sz ≤ c.scratch_cap →
            ret.toNat = 2 * old_sz ∧
            FidCongHtCtrlOk c scr' ctrl_off.toNat ht_off (2 * old_sz) ∧
            rsz' = 0#64 ∧
            (∀ idx < ht_off, idx ≠ ctrl_off.toNat + 7 →
              scr'[idx]? = s.scratch.scratch_buf[idx]?) ∧
            (∀ j < 2 * old_sz, scr'[ht_off + j]? = some 0xFFFFFFFF#32))) →
        (FullMem c s' ⋆ R) m' → Q (ret, ()) m'

def fidCongHtLookupSpec : Spec [i64, i64, i32, i32] [i32] :=
  fun (h, _ctrl_off, _htag, _harity, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
      ∀ ret : BitVec 32, Q (ret, ()) m

def fidCongHtInsertSpec : Spec [i64, i64, i32] [i32] :=
  fun (h, _ctrl_off, _ent, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
      ∀ (ret : BitVec 32) (scr' : List (BitVec 32)) (rsz' : BitVec 64) (m' : Mem 64),
        let s' : FullState :=
          { s with scratch := { s.scratch with scratch_buf := scr', res_sz := rsz' } }
        scr'.length = c.scratch_cap → s'.LengthsOk c →
        PreservesCoreSlice FullState.core s s' → FullExtScratchPres s s' →
        (FullMem c s' ⋆ R) m' → Q (ret, ()) m'

/-- `m8CongEvalGateSpec` implies `fidCongEvalGateSpec` (`maxA = 31`). -/
theorem m8CongEvalGateSpec_to_fid {a m Q X} (h : m8CongEvalGateSpec a m Q X) :
    fidCongEvalGateSpec a m Q X := by
  rcases a with ⟨hh, g, ht_off, ht_sz, next_ep, ctrl_off, ⟨⟩⟩
  rcases h with ⟨c, F0, F_cur, s, scr0, g_len, R, rfl, hdw, hrepr, hht_pos, hht_bnd, hg_lt,
    hg_le_ht, hht_le, hpref, hgat, hht, hq, hm, hQ⟩
  exact ⟨31, c, F0, F_cur, s, scr0, g_len, R, by decide, rfl, hdw, hrepr, hht_pos, hht_bnd,
    hg_lt, hg_le_ht, hht_le, hpref, hgat, hht, hq, hm, hQ⟩

/-- `m6CongEvalGateSpec` implies `fidCongEvalGateSpec` when the queue is inactive
(`ctrl_off = c.scratch_cap`, as called by `full_cong_work_step`). -/
theorem m6CongEvalGateSpec_inactive_to_fid
    {hh g ht_off ht_sz ctrl_off : BitVec 64} {next_ep32 : BitVec 32} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (h : ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (scr0 : List (BitVec 32)) (g_len : Nat) (R : Mem 64 → Prop),
      hh = c.hdr ∧ ctrl_off.toNat = c.scratch_cap ∧ FullDenseInvW c F0 F_cur s ∧
      FullCongReprInv F_cur (2 * s.core.cur_vars) s.core.repr ∧
      0 < ht_sz.toNat ∧ ht_sz.toNat < 2 ^ 30 ∧
      g.toNat < g_len ∧ g_len ≤ ht_off.toNat ∧ ht_off.toNat + ht_sz.toNat ≤ c.scratch_cap ∧
      (∀ idx < g_len, s.scratch.scratch_buf[idx]? = scr0[idx]?) ∧
      M6GateAt F_cur s.core.cur_vars scr0 g_len g.toNat ∧
      M6CongHtInv F_cur s.core.cur_vars scr0 s.scratch.scratch_buf g_len ht_off.toNat ht_sz.toNat ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (r : BitVec 64) s' m',
        FullDenseInvW c F0 F_cur s' →
        s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
        s'.core.arena = s.core.arena → s'.core.arena_len = s.core.arena_len →
        FullCongReprInv F_cur (2 * s'.core.cur_vars) s'.core.repr →
        (∀ idx < g_len, s'.scratch.scratch_buf[idx]? = scr0[idx]?) →
        M6CongHtInv F_cur s'.core.cur_vars scr0 s'.scratch.scratch_buf
          g_len ht_off.toNat ht_sz.toNat →
        ((r &&& 2#64) = 0#64 →
          ∀ idx < c.scratch_cap, idx < ht_off.toNat →
            s'.scratch.scratch_buf[idx]? = s.scratch.scratch_buf[idx]?) →
        ((r &&& 2#64) ≠ 0#64 → F0.Unsat) →
        (FullMem c s' ⋆ R) m' → Q (r, ()) m') :
    fidCongEvalGateSpec (hh, g, ht_off, ht_sz, next_ep32, ctrl_off, ()) m Q X := by
  rcases h with ⟨c, F0, F_cur, s, scr0, g_len, R, rfl, hcap, hdw, hrepr, hht_pos, hht_bnd, hg_lt,
    hg_le_ht, hht_le, hpref, hgat, hht, hm, hQ⟩
  refine ⟨31, c, F0, F_cur, s, scr0, g_len, R, by decide, rfl, hdw, hrepr, hht_pos, hht_bnd,
    hg_lt, hg_le_ht, hht_le, hpref, hgat, hht, Or.inl hcap, hm, ?_⟩
  intro r s' m' hdw' hcv' hfl' har' hal' hrepr' hpref' hht' _hq' hfr' huns' hm'
  exact hQ r s' m' hdw' hcv' hfl' har' hal' hrepr' hpref' hht'
    (fun hr2 idx h1 h2 => (hfr' hr2 idx h1 h2).1 hcap) huns' hm'

end Specs

end LeanQbe.T.Examples.Kissat.FullFidelityCong
