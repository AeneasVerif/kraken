/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Src.Factor
public import LeanQbe.T.Examples.Kissat.Proof.Factor.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Factor.Helpers
public import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts4
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics1
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Candidate-Scan Helpers & Inner Loops for `Src.Factor` (`Proof.Factor.WpScan0`)

Zero-legacy (`0` `Full*` imports, `0` placeholders, `XPost`-polymorphic) invariants,
sub-AST navigators, and inner-loop WP proofs (`s13_scan_bin_wp`, `s13_scan_mp_cand_wp`,
`s13_scan_mp_wp`) for `full_bva_scan_cands`.
-/

set_option autoImplicit false

local macro "fid_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

namespace LeanQbe.T.Examples.Kissat.Proof.Factor

public section

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.C0Step LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Factor
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Spec.FullBvaHeapHelpers
open LeanQbe.T.Examples.Kissat.Proof.Spec.FullBvaHeapTactics
open LeanQbe.T.Examples.Kissat.Proof.Spec.FullBvaHeapScanHelpers
open LeanQbe.T.Examples.Kissat.Proof.Factor.Spec
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullBvaHeapTactics

@[local bv_c0] private theorem bv64_one_toNat : (1 : BitVec 64).toNat = 1 := rfl
@[local bv_c0] private theorem bv32_one_toNat : (1 : BitVec 32).toNat = 1 := rfl
@[local bv_c0] private theorem bv64_two_toNat : (2 : BitVec 64).toNat = 2 := rfl
@[local bv_c0] private theorem bv64_three_toNat : (3 : BitVec 64).toNat = 3 := rfl

private theorem bv32_lshr1_bv (x : BitVec 32) :
    (x >>> (1 : BitVec 32)).toNat = x.toNat / 2 := by
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

/-! ## 1. BitVec, Arena & Scan Invariants -/

private theorem s13_bv32_or_bvaq_garb (x : BitVec 32) :
    ((x ||| 0x02000000#32) &&& 0x00080000#32) = (x &&& 0x00080000#32) := by
  rw [BitVec.and_or_distrib_right,
    show (0x02000000#32 &&& 0x00080000#32) = 0#32 from rfl, BitVec.or_zero]

private theorem s13_bv32_or_bvaq_shrk (x : BitVec 32) :
    ((x ||| 0x02000000#32) &&& 0x00800000#32) = (x &&& 0x00800000#32) := by
  rw [BitVec.and_or_distrib_right,
    show (0x02000000#32 &&& 0x00800000#32) = 0#32 from rfl, BitVec.or_zero]

private theorem s13_bv32_bvaq_roundtrip {x : BitVec 32} (h : (x &&& 0x02000000#32) = 0#32) :
    ((x ||| 0x02000000#32) &&& ~~~0x02000000#32) = x := by
  rw [BitVec.and_or_distrib_right,
    show (0x02000000#32 &&& ~~~0x02000000#32) = 0#32 from rfl, BitVec.or_zero]
  have h1 : x = x &&& (~~~0x02000000#32 ||| 0x02000000#32) := by
    rw [show (~~~0x02000000#32 ||| 0x02000000#32) = BitVec.allOnes 32 from rfl, BitVec.and_allOnes]
  conv => rhs; rw [h1, BitVec.and_or_distrib_left, h, BitVec.or_zero]

private theorem s13_bv32_clear_bvaq_of_zero {x : BitVec 32} (hx : (x &&& 0x02000000#32) = 0#32) :
    (x &&& ~~~0x02000000#32) = x := by
  have h1 : x = x &&& (~~~0x02000000#32 ||| 0x02000000#32) := by
    rw [show (~~~0x02000000#32 ||| 0x02000000#32) = BitVec.allOnes 32 from rfl, BitVec.and_allOnes]
  conv => rhs; rw [h1, BitVec.and_or_distrib_left, hx, BitVec.or_zero]

private theorem s13_list_eq_of_getElem?_eq {α : Type} {l1 l2 : List α}
    (hlen : l1.length = l2.length) (hget : ∀ i < l1.length, l1[i]? = l2[i]?) : l1 = l2 := by
  apply List.ext_getElem?; intro i
  by_cases hi : i < l1.length
  · exact hget i hi
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

private theorem s13ArBvaq_congr {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hcl : s.core.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core)
    {ar : List (BitVec 32)}
    (hpt : ∀ i < c.arena_cap, ar[i]? = s.core.arena[i]? ∨ (i ∈ fullArenaClauseRefsCore s.core ∧
        ar[i]? = some (s.core.arena[i]?.getD 0#32 ||| 0x02000000#32))) :
    fullArenaClauseRefsCore { s.core with arena := ar } = fullArenaClauseRefsCore s.core ∧
    (∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaClauseGarbCore { s.core with arena := ar } r = fullArenaClauseGarbCore s.core r ∧
      fullArenaClauseSizeCore { s.core with arena := ar } r = fullArenaClauseSizeCore s.core r ∧
      fullArenaClauseLitsCore { s.core with arena := ar } r =
        fullArenaClauseLitsCore s.core r) := by
  have hal_le := hcl.arena_len_le
  have hgt_eq : ∀ r ∈ fullArenaClauseRefsCore s.core, ∀ i,
      r < i → i < fullArenaNextOff s.core.arena s.core.arena_len r →
      ar[i]? = s.core.arena[i]? := by
    intro r hr i hgt hlt; have hwf := hw.arena.refs_wf r hr
    rcases hpt i (by omega) with heq | ⟨hi_ref, _⟩
    · exact heq
    · exfalso; have := fullArenaScanRefs_disjoint hr hi_ref hgt; omega
  have hnxt : ∀ r ∈ fullArenaClauseRefsCore s.core, fullArenaNextOff ar s.core.arena_len r =
      fullArenaNextOff s.core.arena s.core.arena_len r := by
    intro r hr; have hwf := hw.arena.refs_wf r hr
    have h2eq : ar[r + 2]? = s.core.arena[r + 2]? := hgt_eq r hr (r + 2) (by omega) (by omega)
    rcases hpt r (by omega) with heq | ⟨_, hset_r⟩
    · exact fullArenaNextOff_congr_block heq h2eq fun i hi1 hi2 => hgt_eq r hr i (by omega) hi2
    · have h1 : ¬ (r + 3 > s.core.arena_len) := by omega
      have h2 : ¬ (r + 3 + (s.core.arena[r + 2]?.getD 0#32).toNat > s.core.arena_len) := by
        unfold fullArenaClauseSizeCore at hwf; omega
      unfold fullArenaNextOff
      simp only [h1, ↓reduceIte, h2eq, h2, hset_r, Option.getD_some, s13_bv32_or_bvaq_shrk]
      split
      · rename_i hshrk
        have hnxt_eq : fullArenaNextOff s.core.arena s.core.arena_len r =
            fullArenaSkipShrk s.core.arena s.core.arena_len
              (r + 3 + (s.core.arena[r + 2]?.getD 0#32).toNat)
              (s.core.arena_len - (r + 3 + (s.core.arena[r + 2]?.getD 0#32).toNat)) := by
          unfold fullArenaNextOff; simp only [h1, ↓reduceIte, h2]; rw [ite_eq_left hshrk]
        exact fullArenaSkipShrk_congr fun i hi1 hi2 =>
          hgt_eq r hr i (by omega) (by rw [hnxt_eq]; exact hi2)
      · rfl
  refine ⟨fullArenaClauseRefsCore_congr rfl hnxt, fun r hr => ?_⟩
  have hwf := hw.arena.refs_wf r hr
  have h2eq : ar[r + 2]? = s.core.arena[r + 2]? := hgt_eq r hr (r + 2) (by omega) (by omega)
  have hsz : fullArenaClauseSizeCore { s.core with arena := ar } r =
      fullArenaClauseSizeCore s.core r := by unfold fullArenaClauseSizeCore; rw [h2eq]
  refine ⟨?_, hsz, ?_⟩
  · unfold fullArenaClauseGarbCore fullArenaHdrCore
    rcases hpt r (by omega) with heq | ⟨_, hset_r⟩
    · rw [heq]
    · rw [hset_r, Option.getD_some, s13_bv32_or_bvaq_garb]
  · exact fullArenaClauseLitsCore_congr hsz fun j hj =>
      hgt_eq r hr (r + 3 + j) (by omega) (by omega)

@[expose] def S13ScanArBvaqInv (c : FullCfg) (s : FullState) (ar ql : List (BitVec 32))
    (lo hi : Nat) : Prop :=
  ar.length = c.arena_cap ∧ ql.length = 2 * c.max_vars ∧ hi ≤ c.max_vars ∧
  (∀ t, lo ≤ t → t < hi → (ql[t]?.getD 0#32).toNat ∈ fullArenaClauseRefsCore s.core ∧
    (s.core.arena[(ql[t]?.getD 0#32).toNat]?.getD 0#32 &&& 0x02000000#32) = 0#32) ∧
  (∀ idx < c.arena_cap, ar[idx]? = s.core.arena[idx]? ∨
    (∃ t, lo ≤ t ∧ t < hi ∧ (ql[t]?.getD 0#32).toNat = idx ∧
      (s.core.arena[idx]?.getD 0#32 &&& 0x02000000#32) = 0#32 ∧
      ar[idx]? = some (s.core.arena[idx]?.getD 0#32 ||| 0x02000000#32)))

theorem s13ScanArBvaqInv_init {c : FullCfg} {s : FullState} (hlen : s.LengthsOk c) :
    S13ScanArBvaqInv c s s.core.arena s.scratch.work_stk2 0 0 :=
  ⟨hlen.core_ok.arena_len_arr, hlen.scratch_ok.work_stk2_len, Nat.zero_le _,
   fun _ _ h => by omega, fun _ _ => Or.inl rfl⟩

theorem s13ScanArBvaqInv_set_ql_hi {c : FullCfg} {s : FullState} {ar ql : List (BitVec 32)}
    {nql : Nat} (h : S13ScanArBvaqInv c s ar ql 0 nql) {idx : Nat} (hidx : c.max_vars ≤ idx)
    (v : BitVec 32) : S13ScanArBvaqInv c s ar (ql.set idx v) 0 nql := by
  obtain ⟨har, hql, hhi, hdom, hall⟩ := h
  refine ⟨har, by simp [hql], hhi, fun t h0 ht => ?_, fun i hi => ?_⟩
  · rw [List.getElem?_set_ne (by omega)]; exact hdom t h0 ht
  · rcases hall i hi with heq | ⟨t, h0, ht, hqt, h0v, hset⟩
    · exact Or.inl heq
    · exact Or.inr ⟨t, h0, ht, by rw [List.getElem?_set_ne (by omega)]; exact hqt, h0v, hset⟩

theorem s13ScanArBvaqInv_push {c : FullCfg} {s : FullState} {ar ql : List (BitVec 32)}
    {nql : Nat} (h : S13ScanArBvaqInv c s ar ql 0 nql) {dr : BitVec 32}
    (hnql_lt : nql < c.max_vars) (hdr_ref : dr.toNat ∈ fullArenaClauseRefsCore s.core)
    (hdr_lt : dr.toNat < c.arena_cap)
    (hdr_nbvaq : (ar[dr.toNat]'(by rw [h.1]; exact hdr_lt) &&& 0x02000000#32) = 0#32) :
    (s.core.arena[dr.toNat]?.getD 0#32 &&& 0x02000000#32) = 0#32 ∧ S13ScanArBvaqInv c s
      (ar.set dr.toNat ((ar[dr.toNat]'(by rw [h.1]; exact hdr_lt)) ||| 0x02000000#32))
      (ql.set nql dr) 0 (nql + 1) := by
  obtain ⟨har, hql, hhi, hdom, hall⟩ := h
  have horig : ar[dr.toNat]? = s.core.arena[dr.toNat]? := by
    rcases hall dr.toNat hdr_lt with heq | ⟨_, _, _, _, h0v, hset⟩
    · exact heq
    · rw [List.getElem?_eq_getElem (by omega)] at hset
      have hval := Option.some.inj hset
      have h1 : ((s.core.arena[dr.toNat]?.getD 0#32 ||| 0x02000000#32) &&& 0x02000000#32) =
          0x02000000#32 := by
        rw [BitVec.and_or_distrib_right,
          show (0x02000000#32 &&& 0x02000000#32) = 0x02000000#32 from rfl, h0v, BitVec.zero_or]
      rw [hval] at hdr_nbvaq; exact absurd (hdr_nbvaq.symm.trans h1) (by decide)
  have hs_nbvaq : (s.core.arena[dr.toNat]?.getD 0#32 &&& 0x02000000#32) = 0#32 := by
    rw [← horig, List.getElem?_eq_getElem (by omega), Option.getD_some]; exact hdr_nbvaq
  refine ⟨hs_nbvaq, by simp [har], by simp [hql], by omega, fun t h0 ht => ?_, fun i hi => ?_⟩
  · by_cases htn : t = nql
    · subst htn; rw [List.getElem?_set_self (by omega), Option.getD_some]; exact ⟨hdr_ref, hs_nbvaq⟩
    · rw [List.getElem?_set_ne (Ne.symm htn)]; exact hdom t h0 (by omega)
  · by_cases hid : i = dr.toNat
    · subst hid
      refine Or.inr ⟨nql, Nat.zero_le _, by omega,
        by rw [List.getElem?_set_self (by omega), Option.getD_some], hs_nbvaq, ?_⟩
      rw [List.getElem?_set_self (by omega)]
      have har_eq : ar[dr.toNat]'(by omega) = s.core.arena[dr.toNat]?.getD 0#32 := by
        rw [← horig, List.getElem?_eq_getElem (by omega), Option.getD_some]
      rw [har_eq]
    · rw [List.getElem?_set_ne (Ne.symm hid)]
      rcases hall i hi with heq | ⟨t, h0, ht, hqt, h0v, hset⟩
      · exact Or.inl heq
      · exact Or.inr ⟨t, h0, by omega,
          by rw [List.getElem?_set_ne (by omega)]; exact hqt, h0v, hset⟩

theorem s13ScanArBvaqInv_clear_step {c : FullCfg} {s : FullState}
    {ar ql : List (BitVec 32)} {ci nql : Nat} (_hs_ar : s.core.arena.length = c.arena_cap)
    (h : S13ScanArBvaqInv c s ar ql ci nql) (hci : ci < nql)
    (hidx_lt : (ql[ci]'(by rw [h.2.1]; have := h.2.2.1; omega)).toNat < c.arena_cap) :
    let idx := (ql[ci]'(by rw [h.2.1]; have := h.2.2.1; omega)).toNat
    S13ScanArBvaqInv c s
      (ar.set idx ((ar[idx]'(by rw [h.1]; exact hidx_lt)) &&& ~~~0x02000000#32))
      ql (ci + 1) nql := by
  obtain ⟨har, hql, hhi, hdom, hall⟩ := h
  intro idx
  have hidx_eq : (ql[ci]?.getD 0#32).toNat = idx := by
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
  have hidx_s0 : (s.core.arena[idx]?.getD 0#32 &&& 0x02000000#32) = 0#32 := by
    have := (hdom ci (Nat.le_refl _) hci).2; rwa [hidx_eq] at this
  have har_idx_clr :
      ((ar[idx]'(by omega)) &&& ~~~0x02000000#32) = s.core.arena[idx]?.getD 0#32 := by
    rcases hall idx hidx_lt with heq | ⟨_, _, _, _, _, hset⟩
    · have : ar[idx]'(by omega) = s.core.arena[idx]?.getD 0#32 := by
        rw [← heq, List.getElem?_eq_getElem (by omega), Option.getD_some]
      rw [this]; exact s13_bv32_clear_bvaq_of_zero hidx_s0
    · rw [List.getElem?_eq_getElem (by omega)] at hset
      rw [Option.some.inj hset]; exact s13_bv32_bvaq_roundtrip hidx_s0
  refine ⟨by simp [har], hql, hhi, fun t ht1 ht2 => hdom t (by omega) ht2, fun i hi => ?_⟩
  by_cases hid : i = idx
  · subst hid; left
    rw [List.getElem?_set_self (by omega), har_idx_clr,
      List.getElem?_eq_getElem (by omega), Option.getD_some]
  · rw [List.getElem?_set_ne (Ne.symm hid)]
    rcases hall i hi with heq | ⟨t, ht1, ht2, hqt, h0v, hset⟩
    · exact Or.inl heq
    · have htne : t ≠ ci := fun h => by subst h; rw [hidx_eq] at hqt; exact hid hqt.symm
      exact Or.inr ⟨t, by omega, ht2, hqt, h0v, hset⟩

theorem s13ScanArBvaqInv_done {c : FullCfg} {s : FullState} {ar ql : List (BitVec 32)}
    {nql : Nat} (hs_ar : s.core.arena.length = c.arena_cap)
    (h : S13ScanArBvaqInv c s ar ql nql nql) : ar = s.core.arena := by
  have har_l := h.1
  apply s13_list_eq_of_getElem?_eq (by rw [har_l, hs_ar])
  intro i hi
  rcases h.2.2.2.2 i (by omega) with heq | ⟨t, ht1, ht2, _⟩
  · exact heq
  · omega

@[expose] def S13LmBit4Inv (c : FullCfg) (lm1 : List (BitVec 8)) (ql : List (BitVec 32))
    (lo hi : Nat) (lm : List (BitVec 8)) : Prop :=
  lm.length = 2 * c.max_vars ∧ hi ≤ c.max_vars ∧
  (∀ t, lo ≤ t → t < hi → (ql[c.max_vars + t]?.getD 0#32).toNat < 2 * c.max_vars) ∧
  ∀ l < 2 * c.max_vars, lm[l]? = lm1[l]? ∨
    (∃ t, lo ≤ t ∧ t < hi ∧ (ql[c.max_vars + t]?.getD 0#32).toNat = l ∧
      lm[l]? = some (lm1[l]?.getD 0#8 ||| 4#8))

theorem s13LmBit4Inv_init {c : FullCfg} {lm1 : List (BitVec 8)} {ql : List (BitVec 32)}
    (hlm1 : lm1.length = 2 * c.max_vars) : S13LmBit4Inv c lm1 ql 0 0 lm1 :=
  ⟨hlm1, Nat.zero_le _, fun _ _ h => by omega, fun _ _ => Or.inl rfl⟩

theorem s13LmBit4Inv_set_ql_lo {c : FullCfg} {lm1 lm : List (BitVec 8)}
    {ql : List (BitVec 32)} {hi idx : Nat} (h : S13LmBit4Inv c lm1 ql 0 hi lm)
    (hidx : idx < c.max_vars) (v : BitVec 32) : S13LmBit4Inv c lm1 (ql.set idx v) 0 hi lm := by
  obtain ⟨hlm, hhi, hdom, hall⟩ := h
  refine ⟨hlm, hhi, fun t h0 ht => ?_, fun l hl => ?_⟩
  · rw [List.getElem?_set_ne (by omega)]; exact hdom t h0 ht
  · rcases hall l hl with heq | ⟨t, h0, ht, hqt, hset⟩
    · exact Or.inl heq
    · exact Or.inr ⟨t, h0, ht, by rw [List.getElem?_set_ne (by omega)]; exact hqt, hset⟩

theorem s13LmBit4Inv_push {c : FullCfg} {lm1 lm : List (BitVec 8)} {ql : List (BitVec 32)}
    {nnou : Nat} (hql : ql.length = 2 * c.max_vars) (h : S13LmBit4Inv c lm1 ql 0 nnou lm)
    {cand : BitVec 32} (hnn : nnou < c.max_vars) (hc_lt : cand.toNat < 2 * c.max_vars) :
    S13LmBit4Inv c lm1 (ql.set (c.max_vars + nnou) cand) 0 (nnou + 1)
      (lm.set cand.toNat ((lm[cand.toNat]'(by rw [h.1]; exact hc_lt)) ||| 4#8)) := by
  obtain ⟨hlm, hhi, hdom, hall⟩ := h
  refine ⟨by simp [hlm], by omega, fun t h0 ht => ?_, fun l hl => ?_⟩
  · by_cases htn : t = nnou
    · subst htn; rw [List.getElem?_set_self (by omega), Option.getD_some]; exact hc_lt
    · rw [List.getElem?_set_ne (by omega)]; exact hdom t h0 (by omega)
  · by_cases hlc : l = cand.toNat
    · subst hlc
      refine Or.inr ⟨nnou, Nat.zero_le _, by omega,
        by rw [List.getElem?_set_self (by omega), Option.getD_some], ?_⟩
      rw [List.getElem?_set_self (by omega)]
      rcases hall cand.toNat hc_lt with heq | ⟨_, _, _, _, hset⟩
      · have : lm[cand.toNat]'(by omega) = lm1[cand.toNat]?.getD 0#8 := by
          rw [← heq, List.getElem?_eq_getElem (by omega), Option.getD_some]
        rw [this]
      · rw [List.getElem?_eq_getElem (by omega)] at hset
        rw [Option.some.inj hset, bv8_or4_idem]
    · rw [List.getElem?_set_ne (Ne.symm hlc)]
      rcases hall l hl with heq | ⟨t, h0, ht, hqt, hset⟩
      · exact Or.inl heq
      · exact Or.inr ⟨t, h0, by omega, by rw [List.getElem?_set_ne (by omega)]; exact hqt, hset⟩

theorem s13LmBit4Inv_clear_step {c : FullCfg} {lm1 lm : List (BitVec 8)}
    {ql : List (BitVec 32)} {j nnou : Nat} (hlm1 : lm1.length = 2 * c.max_vars)
    (_hql : ql.length = 2 * c.max_vars)
    (hlm1_b2 : ∀ l < 2 * c.max_vars, (lm1[l]?.getD 0#8 &&& 4#8) = 0#8)
    (h : S13LmBit4Inv c lm1 ql j nnou lm) (hj : j < nnou) :
    let cl := (ql[c.max_vars + j]'(by have := h.2.1; omega)).toNat
    cl < 2 * c.max_vars ∧ S13LmBit4Inv c lm1 ql (j + 1) nnou
      (lm.set cl ((lm[cl]'(by
        have hdom := h.2.2.1 j (Nat.le_refl _) hj
        rw [List.getElem?_eq_getElem (by have := h.2.1; omega), Option.getD_some] at hdom
        rw [h.1]; exact hdom)) &&& 0xFB#8)) := by
  obtain ⟨hlm, hhi, hdom, hall⟩ := h; intro cl
  have hcl_eq : (ql[c.max_vars + j]?.getD 0#32).toNat = cl := by
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
  have hcl_lt : cl < 2 * c.max_vars := by have := hdom j (Nat.le_refl _) hj; rwa [hcl_eq] at this
  have hclr : ((lm[cl]'(by omega)) &&& 0xFB#8) = lm1[cl]?.getD 0#8 := by
    apply bv8_clear_bit2_eq_of_or4 (hlm1_b2 cl hcl_lt)
    rcases hall cl hcl_lt with heq | ⟨_, _, _, _, hset⟩
    · left; rw [← heq, List.getElem?_eq_getElem (by omega), Option.getD_some]
    · right; rw [List.getElem?_eq_getElem (by omega)] at hset; exact Option.some.inj hset
  refine ⟨hcl_lt, by simp [hlm], hhi, fun t ht1 ht2 => hdom t (by omega) ht2, fun i hi => ?_⟩
  by_cases hic : i = cl
  · subst hic; left
    rw [List.getElem?_set_self (by omega), hclr,
      List.getElem?_eq_getElem (by omega), Option.getD_some]
  · rw [List.getElem?_set_ne (Ne.symm hic)]
    rcases hall i hi with heq | ⟨t, ht1, ht2, hqt, hset⟩
    · exact Or.inl heq
    · have htne : t ≠ j := fun h => by subst h; rw [hcl_eq] at hqt; exact hic hqt.symm
      exact Or.inr ⟨t, by omega, ht2, hqt, hset⟩

theorem s13LmBit4Inv_done {c : FullCfg} {lm1 lm : List (BitVec 8)} {ql : List (BitVec 32)}
    {nnou : Nat} (hlm1 : lm1.length = 2 * c.max_vars)
    (h : S13LmBit4Inv c lm1 ql nnou nnou lm) : lm = lm1 := by
  have hlm_l := h.1
  apply s13_list_eq_of_getElem?_eq (by rw [hlm_l, hlm1])
  intro i hi
  rcases h.2.2.2 i (by omega) with heq | ⟨t, ht1, ht2, _⟩
  · exact heq
  · omega

theorem s13_scan_cands_ar_lits_eq {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {ar ql : List (BitVec 32)} {nql : Nat}
    (hcl : s.core.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core)
    (hbvaq : S13ScanArBvaqInv c s ar ql 0 nql) {r : Nat} (hr : r ∈ fullArenaClauseRefsCore s.core) :
    ar[r + 2]? = s.core.arena[r + 2]? ∧
    (∀ j < fullArenaClauseSizeCore s.core r, ar[r + 3 + j]? = s.core.arena[r + 3 + j]?) := by
  have hwf := hw.arena.refs_wf r hr; have hal := hcl.arena_len_le
  constructor
  · rcases hbvaq.2.2.2.2 (r + 2) (by omega) with heq | ⟨t, _, ht, hqt, _, _⟩
    · exact heq
    · exfalso; have ht_ref := (hbvaq.2.2.2.1 t (Nat.zero_le _) ht).1; rw [hqt] at ht_ref
      rcases Nat.lt_or_gt_of_ne (by omega : r ≠ r + 2) with hlt | hgt
      · have := fullArenaScanRefs_disjoint hr ht_ref hlt; omega
      · omega
  · intro j hj
    rcases hbvaq.2.2.2.2 (r + 3 + j) (by omega) with heq | ⟨t, _, ht, hqt, _, _⟩
    · exact heq
    · exfalso; have ht_ref := (hbvaq.2.2.2.1 t (Nat.zero_le _) ht).1; rw [hqt] at ht_ref
      have := fullArenaScanRefs_disjoint hr ht_ref (by omega); omega

theorem s13_scan_cands_stepB_inv {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {arp qlA : List (BitVec 32)} {lm1 lmA : List (BitVec 8)}
    {nqlp nn1 : Nat} {dr : BitVec 32}
    (hcl : s.core.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core)
    (hwp : FullWitnessInv c F0 F_cur { s.core with arena := arp }) (hl0 : s.core.cur_level = 0)
    (hbvaqA : S13ScanArBvaqInv c s arp qlA 0 nqlp) (hlm4A : S13LmBit4Inv c lm1 qlA 0 nn1 lmA)
    (hnq_lt : nqlp < c.max_vars) (hdr_ref : dr.toNat ∈ fullArenaClauseRefsCore s.core)
    (hdr_lt : dr.toNat < c.arena_cap)
    (hdr_nbvaq : (arp[dr.toNat]'(by rw [hbvaqA.1]; exact hdr_lt) &&& 0x02000000#32) = 0#32) :
    let ar1 := arp.set dr.toNat ((arp[dr.toNat]'(by rw [hbvaqA.1]; exact hdr_lt)) ||| 0x02000000#32)
    S13ScanArBvaqInv c s ar1 (qlA.set nqlp dr) 0 (nqlp + 1) ∧
    S13LmBit4Inv c lm1 (qlA.set nqlp dr) 0 nn1 lmA ∧
    FullWitnessInv c F0 F_cur { s.core with arena := ar1 } := by
  have harp_l := hbvaqA.1
  have hcl_ar : ({ s.core with arena := arp }).LengthsOk c := { hcl with arena_len_arr := harp_l }
  have ⟨_, hbvaq_next⟩ := s13ScanArBvaqInv_push hbvaqA hnq_lt hdr_ref hdr_lt hdr_nbvaq
  have hlm4_next := s13LmBit4Inv_set_ql_lo hlm4A hnq_lt dr
  have hwp_refs : dr.toNat ∈ fullArenaClauseRefsCore { s.core with arena := arp } := by
    have h1 := (s13ArBvaq_congr hcl hw fun i hi => by
      rcases hbvaqA.2.2.2.2 i hi with heq | ⟨t, h0, ht, hqt, _, hset'⟩
      · exact Or.inl heq
      · have ht_ref := (hbvaqA.2.2.2.1 t h0 ht).1; rw [hqt] at ht_ref
        exact Or.inr ⟨ht_ref, hset'⟩).1
    rw [h1]; exact hdr_ref
  have ⟨_, _, hw_next, _⟩ := fullWitnessInv_set_hdr_bit20 hcl_ar hwp hl0 hwp_refs
    ((arp[dr.toNat]'(by omega)) ||| 0x02000000#32)
    (by unfold fullArenaHdrCore; dsimp only
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; exact s13_bv32_or_bvaq_garb _)
    (by unfold fullArenaHdrCore; dsimp only
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; exact s13_bv32_or_bvaq_shrk _)
  exact ⟨hbvaq_next, hlm4_next, hw_next⟩

theorem s13_scan_cands_lmj_lift {c : FullCfg} {ar : List (BitVec 32)}
    {lm0 lmj : List (BitVec 8)} {qw j csz : Nat}
    (h : LmBit2Inv c ar lm0 qw 0 j lmj) (_hj : j ≤ csz) :
    LmBit2Inv c ar lm0 qw 0 csz lmj :=
  ⟨h.1, fun l hl => by
    rcases h.2 l hl with heq | ⟨k, h0, hk, har', hset'⟩
    · exact Or.inl heq
    · exact Or.inr ⟨k, h0, by omega, har', hset'⟩⟩

/-! ## 2. `full_bva_scan_cands` Structural Navigators -/

@[expose] def s13DummyVal : (t : Ty) → Val t
  | .bits _ => 0 | .bool => true | .float _ => 0 | .pair a b => (s13DummyVal a, s13DummyVal b)
@[expose] def s13DummyTup : (ts : List Ty) → Tup Val ts
  | [] => () | t :: ts => (s13DummyVal t, s13DummyTup ts)
@[expose] def s13Step {rs : List Ty} : Expr Val Cont rs → Expr Val Cont rs
  | .let_ (ts := ts) _ k => k (s13DummyTup ts)
  | .load t _ k => k (s13DummyVal t)
  | .store _ _ k => k
  | .call (bs := bs) _ _ k => k (s13DummyTup bs)
  | _ => .hlt
@[expose] def s13Steps {rs : List Ty} : Nat → Expr Val Cont rs → Expr Val Cont rs
  | 0, e => e | n + 1, e => s13Steps n (s13Step e)
@[expose] def s13StepZ {rs : List Ty} : Expr Val Cont rs → Expr Val Cont rs
  | .let_ (Op.mk (.zext _ m) (a, ())) k => k (BitVec.setWidth m a.val, ())
  | .let_ (Op.mk (.add (.bits 64)) (a, b, ())) k => k (a.val + b.val, ())
  | e => s13Step e
@[expose] def s13StepsZ {rs : List Ty} : Nat → Expr Val Cont rs → Expr Val Cont rs
  | 0, e => e | n + 1, e => s13StepsZ n (s13StepZ e)
@[expose] def s13Ld64 {rs : List Ty} (v : Val i64) : Expr Val Cont rs → Expr Val Cont rs
  | .load (.bits 64) _ k => k v | _ => .hlt
@[expose] def s13Ld32 {rs : List Ty} (v : Val i32) : Expr Val Cont rs → Expr Val Cont rs
  | .load (.bits 32) _ k => k v | _ => .hlt
@[expose] def s13Call64 {rs : List Ty} (v : Val i64) : Expr Val Cont rs → Expr Val Cont rs
  | .call (bs := [.bits 64]) _ _ k => k (v, ()) | _ => .hlt
@[expose] def s13Then {rs : List Ty} : Expr Val Cont rs → Expr Val Cont rs
  | .jnz _ t _ => t | _ => .hlt
@[expose] def s13Else {rs : List Ty} : Expr Val Cont rs → Expr Val Cont rs
  | .jnz _ _ e => e | _ => .hlt
@[expose] def s13GrpK4q {rs : List Ty} (J : Cont [i32, i32, i32, i64]) :
    Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 32, .bits 32, .bits 32, .bits 64]]) _ k => k (J, ()) | _ => .hlt
@[expose] def s13GrpB4q {rs : List Ty} (v : Tup Val [i32, i32, i32, i64])
    (J : Cont [i32, i32, i32, i64]) : Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 32, .bits 32, .bits 32, .bits 64]]) bs _ =>
    match bs (J, ()) with | .cons f .nil => f v
  | _ => .hlt
@[expose] def s13GrpK3s {rs : List Ty} (J : Cont [i32, i32, i64]) :
    Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 32, .bits 32, .bits 64]]) _ k => k (J, ()) | _ => .hlt
@[expose] def s13GrpB4m {rs : List Ty} (v : Tup Val [i32, i32, i32, i32])
    (J : Cont [i32, i32, i32, i32]) : Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 32, .bits 32, .bits 32, .bits 32]]) bs _ =>
    match bs (J, ()) with | .cons f .nil => f v
  | _ => .hlt
@[expose] def s13GrpK4c {rs : List Ty} (J : Cont [i32, i32, i64, i32]) :
    Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 32, .bits 32, .bits 64, .bits 32]]) _ k => k (J, ()) | _ => .hlt
@[expose] def s13GrpK5mp {rs : List Ty} (J : Cont [i32, i32, i64, i64, i32]) :
    Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 32, .bits 32, .bits 64, .bits 64, .bits 32]]) _ k => k (J, ())
  | _ => .hlt

@[expose] def s13MkSt (s : FullState) (ant : BitVec 64) (arx : List (BitVec 32))
    (lmx : List (BitVec 8)) (wsx ws1x qlx : List (BitVec 32)) : FullState :=
  { core := { s.core with arena := arx, lit_mark := lmx },
    scratch :=
      { s.scratch with wsort := wsx, work_stk1 := ws1x, work_stk2 := qlx, ant_sz := ant } }

@[expose] def s13ScanHdr (row_off cur_qn : Val i32) (h64 init_lits : Val i64)
    (pVals pWv pWs pAr pLm pScr pCnt pCntd pFl pQl pDeg r_clines : Val i64)
    (J Jq : Cont [i32, i32, i32, i64])
    (nql ncntd qi : Val i32) (ticks : Val i64) (qw : Val i32)
    (Js : Cont [i32, i32, i64]) : Expr Val Cont [i32] :=
  full_bva_scan_cands_body Val Cont (h64, row_off, cur_qn, init_lits, ())
    |> s13Step |> s13Ld64 pVals |> s13Step |> s13Ld64 pWv |> s13Step |> s13Ld64 pWs
    |> s13Step |> s13Ld64 pAr |> s13Step |> s13Ld64 pLm |> s13Step |> s13Ld64 pScr
    |> s13Step |> s13Ld64 pCnt |> s13Step |> s13Ld64 pCntd |> s13Step |> s13Ld64 pFl
    |> s13Step |> s13Ld64 pQl |> s13Step |> s13Ld64 pDeg |> s13Step |> s13Call64 r_clines
    |> s13Step |> s13GrpK4q J |> s13GrpB4q (nql, ncntd, qi, ticks, ()) Jq
    |> s13Step |> s13Then |> s13Steps 4 |> s13Ld32 qw |> s13GrpK3s Js

@[expose] def s13ScanBin (row_off cur_qn : Val i32) (h64 init_lits : Val i64)
    (pVals pWv pWs pAr pLm pScr pCnt pCntd pFl pQl pDeg r_clines : Val i64)
    (J Jq : Cont [i32, i32, i32, i64]) (nql ncntd qi : Val i32) (ticks : Val i64)
    (qw : Val i32) (Js : Cont [i32, i32, i64]) : Expr Val Cont [i32] :=
  s13ScanHdr row_off cur_qn h64 init_lits pVals pWv pWs pAr pLm pScr pCnt pCntd pFl pQl pDeg
    r_clines J Jq nql ncntd qi ticks qw Js |> s13Steps 2 |> s13Then

@[expose] def s13ScanLarge (row_off cur_qn : Val i32) (h64 init_lits : Val i64)
    (pVals pWv pWs pAr pLm pScr pCnt pCntd pFl pQl pDeg r_clines : Val i64)
    (J Jq : Cont [i32, i32, i32, i64]) (nql ncntd qi : Val i32) (ticks : Val i64)
    (qw : Val i32) (Js : Cont [i32, i32, i64]) : Expr Val Cont [i32] :=
  s13ScanHdr row_off cur_qn h64 init_lits pVals pWv pWs pAr pLm pScr pCnt pCntd pFl pQl pDeg
    r_clines J Jq nql ncntd qi ticks qw Js |> s13StepsZ 2 |> s13Else

@[expose] def s13ScanMp (row_off cur_qn : Val i32) (h64 init_lits : Val i64)
    (pVals pWv pWs pAr pLm pScr pCnt pCntd pFl pQl pDeg r_clines : Val i64)
    (J Jq : Cont [i32, i32, i32, i64]) (nql ncntd qi : Val i32) (ticks : Val i64)
    (qw : Val i32) (Js : Cont [i32, i32, i64]) (csz : Val i32) (Jm : Cont [i32, i32, i32, i32])
    (min_l min_d fc jf : Val i32) (Jc_join : Cont [i32, i32, i64, i32])
    (moff msz : Val i32) (mxv r_clines_min : Val i64)
    (Jmp : Cont [i32, i32, i64, i64, i32]) : Expr Val Cont [i32] :=
  s13ScanLarge row_off cur_qn h64 init_lits pVals pWv pWs pAr pLm pScr pCnt pCntd pFl pQl pDeg
    r_clines J Jq nql ncntd qi ticks qw Js
    |> s13StepsZ 4 |> s13Ld32 csz |> s13StepZ
    |> s13GrpB4m (min_l, min_d, fc, jf, ()) Jm
    |> s13GrpK4c Jc_join |> s13StepZ |> s13Then |> s13StepZ |> s13Then
    |> s13StepsZ 5 |> s13Ld32 moff |> s13StepsZ 7 |> s13Ld32 msz |> s13StepsZ 3
    |> s13Ld64 mxv |> s13StepsZ 2 |> s13Call64 r_clines_min |> s13StepZ
    |> s13GrpK5mp Jmp

/-! ## 3. Binary & Large-Occurrence Inner Loops (`s13_scan_bin_wp`, `s13_scan_mp_wp`) -/

theorem s13_scan_bin_wp {Γ : Env} {Q : Post [i32]} {X : XPost}
    (hClines : ∀ a m Q X, fidBvaClinesSpec a m Q X → Γ "full_bva_clines_fid" [i64] [i64] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState} {R : Mem 64 → Prop}
    {row_off cur_qn : Val i32} {init_lits : Val i64} {J Jq : Cont [i32, i32, i32, i64]}
    {nql ncntd qi : Val i32} {ticks r_clines : Val i64} {qw : Val i32}
    {Js : Cont [i32, i32, i64]} {ar ws ws1 ws2 : List (BitVec 32)} {ant : BitVec 64} {ml : Mem 64}
    (hslen : s.LengthsOk c) (_hw : FullWitnessInv c F0 F_cur s.core)
    (hdw : DenseWatchesInv F_cur s.core)
    (hws_l : ws.length = 2 * c.max_vars) (hws1_l : ws1.length = 2 * c.max_vars)
    (_hws2_l : ws2.length = 2 * c.max_vars) (_har_l : ar.length = c.arena_cap)
    (hnc_le : ncntd.toNat ≤ 2 * c.max_vars)
    (hcntd_ok : ∀ i < ncntd.toNat,
      (ws1[i]?.getD 0#32).toNat ≤ init_lits.toNat ∧ (ws1[i]?.getD 0#32).toNat < 2 * s.core.cur_vars)
    (hq_lt : (qw &&& 0x7FFFFFFF#32).toNat < 2 * s.core.cur_vars)
    (hml : (FullMem c
      { core := { s.core with arena := ar },
        scratch :=
          { s.scratch with wsort := ws, work_stk1 := ws1, work_stk2 := ws2, ant_sz := ant } } ⋆
      R) ml)
    (hExit : ∀ (nc' : BitVec 32) (ticks' : BitVec 64) wsp ws1p mlp,
      nc'.toNat ≤ 2 * c.max_vars → wsp.length = 2 * c.max_vars → ws1p.length = 2 * c.max_vars →
      (∀ i < nc'.toNat,
        (ws1p[i]?.getD 0#32).toNat ≤ init_lits.toNat ∧
        (ws1p[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) →
      (FullMem c
        { core := { s.core with arena := ar },
          scratch :=
            { s.scratch with
              wsort := wsp, work_stk1 := ws1p, work_stk2 := ws2, ant_sz := ant } } ⋆ R) mlp →
      Js (nql, nc', ticks', ()) mlp) :
    wp Γ Q X (s13ScanBin row_off cur_qn c.hdr init_lits c.pVals c.pWvec c.pWstk c.pArena
      c.pLitMark c.pScratchBuf c.pWsort c.pWorkStk1 c.pFlags c.pWorkStk2 c.pRepr r_clines
      J Jq nql ncntd qi ticks qw Js) ml := by
  have hmx := c.hmaxv; have har_b := c.harena; unfold dimacsBound at hmx har_b
  have hcl := hslen.core_ok; have hcv_le := hcl.cur_vars_le; have hwv_len := hcl.wvec_len
  have hws_len := hcl.wstk_len_arr; have hwlen_le := hcl.wlen_le
  have hlm_len := hcl.lit_mark_len; have hvals_len := hcl.vals_len
  have hfl_len := hcl.flags_len; have hrepr_len := hcl.repr_len
  have hset : ∀ x : BitVec 32, (BitVec.setWidth 64 x).toNat = x.toNat := bv64_setWidth_32
  let q := qw &&& 0x7FFFFFFF#32
  have hq_lt' : q.toNat < 2 * s.core.cur_vars := hq_lt
  have h2q_n : (BitVec.setWidth 64 q <<< (1 : Nat)).toNat = 2 * q.toNat := by c0_bound
  have h2q1_n : ((BitVec.setWidth 64 q <<< (1 : Nat)) + 1).toNat = 2 * q.toNat + 1 := by
    change ((BitVec.setWidth 64 q <<< (1 : Nat)) + 1#64).toNat = _; c0_bound
  have hq_bd := hdw.layout.bounds q.toNat hq_lt; have hq_sl := hdw.slices q.toNat hq_lt
  have hoff_eq : (s.core.wvec[2 * q.toNat]'(by omega)).toNat = fullWatchOffCore s.core q.toNat := by
    unfold fullWatchOffCore; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
  have hsz_eq : (s.core.wvec[2 * q.toNat + 1]'(by omega)).toNat =
      fullWatchSizeCore s.core q.toNat := by
    unfold fullWatchSizeCore; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
  let qoff0 := fullWatchOffCore s.core q.toNat
  let qsz0 := fullWatchSizeCore s.core q.toNat
  have h2147 : (2147483647 : BitVec 32) = 0x7FFFFFFF#32 := rfl
  have hq_ast : qw &&& (2147483647 : BitVec 32) = q := by rw [h2147]
  have h2q_wv : (BitVec.setWidth 64 (qw &&& (2147483647 : BitVec 32)) <<< (1 : Nat)).toNat <
      s.core.wvec.length := by rw [hq_ast, h2q_n]; omega
  have h2q1_wv : ((BitVec.setWidth 64 (qw &&& (2147483647 : BitVec 32)) <<< (1 : Nat)) +
      1).toNat < s.core.wvec.length := by rw [hq_ast, h2q1_n]; omega
  have hq_repr : (BitVec.setWidth 64 (qw &&& (2147483647 : BitVec 32))).toNat <
      s.core.repr.length := by rw [hq_ast, bv64_setWidth_32, hrepr_len]; have := hq_lt; omega
  dsimp only [s13ScanBin, s13ScanHdr, s13Step, s13Steps, s13StepZ, s13StepsZ, s13Ld64, s13Ld32,
    s13Call64, s13Then, s13Else, s13GrpK4q, s13GrpB4q, s13GrpK3s, s13GrpB4m, s13GrpK4c, s13GrpK5mp,
    s13DummyVal, s13DummyTup, full_bva_scan_cands_body]
  c0_hfast_nogrp
  fid_call hClines
  intro r_clines_bin
  c0_hfast_nogrp
  refine wp_loop_inv
    (fun (nc, qp, ()) mlp => ∃ wsp ws1p,
      qoff0 ≤ qp.toNat ∧ qp.toNat ≤ qoff0 + qsz0 ∧ nc.toNat ≤ 2 * c.max_vars ∧
      wsp.length = 2 * c.max_vars ∧ ws1p.length = 2 * c.max_vars ∧
      DenseWatchSliceOk F_cur s.core q.toNat qp.toNat (qoff0 + qsz0 - qp.toNat) ∧
      (∀ i < nc.toNat,
        (ws1p[i]?.getD 0#32).toNat ≤ init_lits.toNat ∧
        (ws1p[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
      (FullMem c
        { core := { s.core with arena := ar },
          scratch :=
            { s.scratch with
              wsort := wsp, work_stk1 := ws1p, work_stk2 := ws2, ant_sz := ant } } ⋆ R) mlp)
    (fun (_, qp, _) _ => qoff0 + qsz0 - qp.toNat)
    (fun Jp hJp => by
      c0_hfast
      have h1 : (BitVec.setWidth 64 (s.core.wvec[(BitVec.setWidth 64
          (qw &&& (2147483647 : BitVec 32)) <<< (1 : Nat)).toNat]'(by
          rw [hq_ast, h2q_n]; omega))).toNat = qoff0 := by
        simp only [hq_ast, h2q_n, hset, hoff_eq]; rfl
      refine hJp (ncntd, _, ()) ml ⟨ws, ws1, by rw [h1]; exact Nat.le_refl _,
        by rw [h1]; omega, hnc_le, hws_l, hws1_l,
        by simpa only [h1, Nat.add_sub_cancel_left] using hq_sl, hcntd_ok, hml⟩)
    (fun Jp (nc, qp, ()) mlp
        ⟨wsp, ws1p, hqp_ge, hqp_le, hncp_le, hwsp_l, hws1p_l, hrem, hcntdp, hmlp⟩ ihp => ?_)
  clear hml
  c0_hsplit
  · have hqp_lt_raw := hc; clear hc
    have hqp_lt : qp.toNat < qoff0 + qsz0 := by
      have h2q_mod : 2 * q.toNat % 2 ^ 64 = 2 * q.toNat := Nat.mod_eq_of_lt (by omega)
      have hqend_mod : ((s.core.wvec[2 * q.toNat % 2 ^ 64]'(by rw [h2q_mod]; omega)).toNat +
          (s.core.wvec[(2 * q.toNat + 1) % 2 ^ 64]'(by
            rw [Nat.mod_eq_of_lt (by omega : 2 * q.toNat + 1 < 2 ^ 64)]; omega)).toNat) %
          2 ^ 64 = qoff0 + qsz0 := by
        simp only [h2q_mod, Nat.mod_eq_of_lt (by omega : 2 * q.toNat + 1 < 2 ^ 64),
          hoff_eq, hsz_eq]
        exact Nat.mod_eq_of_lt (by omega)
      rw [← hqend_mod]; simpa only [h2147, show (qw &&& 0x7FFFFFFF#32) = q from rfl] using
        hqp_lt_raw
    have hqp_ws : qp.toNat < s.core.wstk.length := by omega
    have hqp1_n : (qp + 1#64).toNat = qp.toNat + 1 := by simp only [bv_c0]; omega
    c0_hfast_nogrp; c0_hstep; c0_hsplit
    · have ⟨hc_lt2, _, hrem_next⟩ :=
        bva_slice_bin_info hrem (by omega) hqp_ws (by assumption)
      let cand := s.core.wstk[qp.toNat]'hqp_ws &&& 0x7FFFFFFF#32
      have hcand_lt : cand.toNat < 2 * s.core.cur_vars := hc_lt2
      have hcand_shr : (cand >>> (1 : Nat)).toNat < c.max_vars := by rw [bv32_lshr1_nat]; omega
      have hcand_ws : (BitVec.setWidth 64 cand).toNat < wsp.length := by rw [hset, hwsp_l]; omega
      c0_hfast_nogrp
      refine wp_join_state1 (t := i32)
        (α := BitVec 32 × List (BitVec 32) × List (BitVec 32)) (fun st => st.1)
        (fun ⟨nc1, wsp1, ws1p1⟩ mf =>
          nc1.toNat ≤ 2 * c.max_vars ∧ wsp1.length = 2 * c.max_vars ∧
          ws1p1.length = 2 * c.max_vars ∧
          (∀ i < nc1.toNat,
            (ws1p1[i]?.getD 0#32).toNat ≤ init_lits.toNat ∧
            (ws1p1[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
          (FullMem c
            { core := { s.core with arena := ar },
              scratch :=
                { s.scratch with
                  wsort := wsp1, work_stk1 := ws1p1, work_stk2 := ws2, ant_sz := ant } } ⋆ R) mf)
        (fun _ ⟨nc1, wsp1, ws1p1⟩ mf ⟨hnc1, hwsp1, hws1p1, hcntd1, hmf⟩ => by
          c0_hfast
          exact ihp (nc1, qp + 1#64, ()) mf (by dsimp only; rw [hqp1_n]; omega)
            ⟨wsp1, ws1p1, by rw [hqp1_n]; omega, by rw [hqp1_n]; omega, hnc1, hwsp1, hws1p1,
             by rw [hqp1_n, show qoff0 + qsz0 - (qp.toNat + 1) = qoff0 + qsz0 - qp.toNat - 1
                  by omega]; exact hrem_next, hcntd1, hmf⟩)
        (fun Jc hJc => ?_)
      have hcand_lm : (BitVec.setWidth 64 (s.core.wstk[qp.toNat]'hqp_ws &&&
          (2147483647 : BitVec 32))).toNat < s.core.lit_mark.length := by
        rw [h2147, bv64_setWidth_32, hlm_len]; omega
      have hcand_fl : (BitVec.setWidth 64 (((s.core.wstk[qp.toNat]'hqp_ws &&&
          (2147483647 : BitVec 32))) >>> (1 : BitVec 32))).toNat < s.core.flags.length := by
        rw [h2147, bv64_setWidth_32, hfl_len]
        have hshr : ∀ x : BitVec 32, (x >>> (1 : BitVec 32)).toNat = x.toNat / 2 :=
          fun x => by simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
        rw [hshr]; omega
      have hcand_v : (BitVec.setWidth 64 (s.core.wstk[qp.toNat]'hqp_ws &&&
          (2147483647 : BitVec 32))).toNat < s.core.vals.length := by
        rw [h2147, bv64_setWidth_32, hvals_len]; omega
      have hcand_ws' : (BitVec.setWidth 64 (s.core.wstk[qp.toNat]'hqp_ws &&&
          (2147483647 : BitVec 32))).toNat < wsp.length := by
        rw [h2147, bv64_setWidth_32, hwsp_l]; omega
      have hmx_shl : (BitVec.ofNat 64 c.max_vars <<< (1 : Nat)).toNat = 2 * c.max_vars := by
        c0_bound
      have hnc_ws1 : (BitVec.setWidth 64 nc).toNat < ws1p.length →
          nc.toNat < ws1p.length := fun h => by rwa [hset] at h
      c0_hfast
      all_goals
        first
        | (refine hJc ⟨nc, _, ws1p⟩ _ ⟨hncp_le, ?_, hws1p_l, hcntdp, by assumption⟩
           try simp only [List.length_set]
           exact hwsp_l)
        | (have hnc_lt2 : nc.toNat < 2 * c.max_vars := by
             simp only [bv_c0, hset] at *; omega
           refine hJc ⟨_, _, _⟩ _ ⟨?_, ?_, ?_, ?_, by assumption⟩
           · first
             | exact hncp_le
             | (simp only [show (1 : BitVec 32) = 1#32 from rfl, bv_c0] at *; omega)
           · (try simp only [List.length_set]); exact hwsp_l
           · (try simp only [List.length_set]); exact hws1p_l
           · intro i hi
             first
             | exact hcntdp i hi
             | (have hcand_il : (s.core.wstk[qp.toNat]'hqp_ws &&&
                    (2147483647 : BitVec 32)).toNat ≤ init_lits.toNat := by
                  simp only [bv_c0] at *; omega
                have hnc1 : (nc + (1 : BitVec 32)).toNat = nc.toNat + 1 := by
                  simp only [show (1 : BitVec 32) = 1#32 from rfl, bv_c0] at *; omega
                rw [hnc1] at hi
                by_cases hie : i = nc.toNat
                · subst hie; rw [hset, List.getElem?_set_self (by rw [hws1p_l]; omega),
                    Option.getD_some]
                  exact ⟨hcand_il, by rwa [h2147]⟩
                · rw [hset, List.getElem?_set_ne (Ne.symm hie)]; exact hcntdp i (by omega)))
    · have ⟨h2le, hrem_next⟩ :=
        bva_slice_occ_info hrem (by omega) hqp_ws (by assumption)
      have hqp2_n : (qp + 2#64).toNat = qp.toNat + 2 := by simp only [bv_c0]; omega
      c0_hfast
      exact ihp (nc, qp + 2#64, ()) mlp (by dsimp only; rw [hqp2_n]; omega)
        ⟨wsp, ws1p, by rw [hqp2_n]; omega, by rw [hqp2_n]; omega, hncp_le, hwsp_l, hws1p_l,
         by rw [hqp2_n, show qoff0 + qsz0 - (qp.toNat + 2) = qoff0 + qsz0 - qp.toNat - 2
              by omega]; exact hrem_next, hcntdp, hmlp⟩
  · c0_hfast_nogrp
    exact hExit nc _ wsp ws1p mlp hncp_le hwsp_l hws1p_l hcntdp hmlp

private def s13McZext (a : Arg Val i32) (k : Val i64 → Expr Val Cont [i32]) :
    Expr Val Cont [i32] :=
  Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (a, ()) } fun p => k p.fst
private def s13McOp64 (op : OpCode [i64, i64] [i64]) (a b : Arg Val i64)
    (k : Val i64 → Expr Val Cont [i32]) : Expr Val Cont [i32] :=
  Expr.let_ { sig := [i64, i64], code := op, args := (a, b, ()) } fun p => k p.fst
private def s13McOp32 (op : OpCode [i32, i32] [i32]) (a b : Arg Val i32)
    (k : Val i32 → Expr Val Cont [i32]) : Expr Val Cont [i32] :=
  Expr.let_ { sig := [i32, i32], code := op, args := (a, b, ()) } fun p => k p.fst
private def s13McCmp32 (op : CmpOp) (a b : Arg Val i32)
    (k : Val .bool → Expr Val Cont [i32]) : Expr Val Cont [i32] :=
  Expr.let_ { sig := [i32, i32], code := OpCode.cmp op i32, args := (a, b, ()) } fun p => k p.fst
private def s13McPtr32 (base : Val i64) (idx : Val i32) (k : Val i64 → Expr Val Cont [i32]) :
    Expr Val Cont [i32] :=
  s13McZext (Arg.var idx) fun i64v =>
  s13McOp64 (.mul i64) (Arg.var i64v) (Arg.imm 4) fun off =>
  s13McOp64 (.add i64) (Arg.var base) (Arg.var off) k

private def s13MpCandExpr (h init_lits pVals pAr pLm pWs pWs1 pFl pQl mxv : Val i64)
    (nqlp ncp nnoup dr cand : Val i32) (ok : Val .bool) (ticks1 mp2 : Val i64)
    (JmpL : Cont [i32, i32, i64, i64, i32]) : Expr Val Cont [i32] :=
  Expr.group (fun _ => Blocks.cons (fun (p : Tup Val [i32, i32, i32]) =>
    Expr.jump JmpL (Arg.var p.fst, Arg.var p.snd.fst, Arg.var ticks1, Arg.var mp2,
      Arg.var p.snd.snd.fst, ())) Blocks.nil) fun Jcont =>
  let jFail : Expr Val Cont [i32] :=
    Expr.jump Jcont.fst (Arg.var nqlp, Arg.var ncp, Arg.var nnoup, ())
  Expr.jnz (Arg.var ok)
    (s13McCmp32 .ne (Arg.var cand) (Arg.imm 4294967295) fun cne =>
     Expr.jnz (Arg.var cne)
       (s13McZext (Arg.var cand) fun c64 =>
        Expr.let_ { sig := [i64, i64], code := OpCode.cmp .ule i64,
                    args := (Arg.var c64, Arg.var init_lits, ()) } fun cule =>
        Expr.jnz (Arg.var cule.fst)
          (s13McOp32 (.lshr i32) (Arg.var cand) (Arg.imm 1) fun csh =>
           s13McPtr32 pFl csh fun pfl => Expr.load i32 (Arg.var pfl) fun flv =>
           s13McOp32 (.and i32) (Arg.var flv) (Arg.imm 1) fun fla =>
           s13McCmp32 .ne (Arg.var fla) (Arg.imm 0) fun cact =>
           Expr.jnz (Arg.var cact)
             (s13McZext (Arg.var cand) fun c64v =>
              s13McOp64 (.add i64) (Arg.var pVals) (Arg.var c64v) fun pv =>
              Expr.load i8 (Arg.var pv) fun vv =>
              Expr.let_ { sig := [i32], code := OpCode.trunc 32 8, args := (Arg.imm 0, ()) }
                fun z8 =>
              Expr.let_ { sig := [i8], code := OpCode.sext 8 32, args := (Arg.var vv, ()) }
                fun v32 =>
              Expr.let_ { sig := [i8], code := OpCode.sext 8 32, args := (Arg.var z8.fst, ()) }
                fun z32 =>
              s13McCmp32 .eq (Arg.var v32.fst) (Arg.var z32.fst) fun cv0 =>
              Expr.jnz (Arg.var cv0)
                (Expr.group (fun _ => Blocks.cons (fun (pnn : Tup Val [i32]) =>
                  Expr.group (fun _ => Blocks.cons (fun (pnq : Tup Val [i32]) =>
                    Expr.group (fun _ => Blocks.cons (fun (pnc : Tup Val [i32]) =>
                      Expr.group (fun _ => Blocks.cons (fun (_ : Tup Val []) =>
                        Expr.jump Jcont.fst (Arg.var pnq.fst, Arg.var pnc.fst, Arg.var pnn.fst,
                          ())) Blocks.nil) fun Jc2 =>
                      s13McPtr32 pWs cand fun pc0 => Expr.load i32 (Arg.var pc0) fun cv =>
                      s13McCmp32 .ult (Arg.var cv) (Arg.imm 4294967295) fun cult =>
                      Expr.jnz (Arg.var cult)
                        (s13McPtr32 pWs cand fun pc1 =>
                         s13McPtr32 pWs cand fun pc2 => Expr.load i32 (Arg.var pc2) fun cv2 =>
                         s13McOp32 (.add i32) (Arg.var cv2) (Arg.imm 1) fun cv3 =>
                         Expr.store (Arg.var cv3) (Arg.var pc1) (Expr.jump Jc2.fst ()))
                        (Expr.jump Jc2.fst ())) Blocks.nil) fun Jc1 =>
                    s13McPtr32 pWs cand fun pc3 => Expr.load i32 (Arg.var pc3) fun cv4 =>
                    s13McCmp32 .eq (Arg.var cv4) (Arg.imm 0) fun ceq0 =>
                    Expr.jnz (Arg.var ceq0)
                      (Expr.group (fun _ => Blocks.cons (fun (pnc2 : Tup Val [i32]) =>
                        Expr.jump Jc1.fst (Arg.var pnc2.fst, ())) Blocks.nil) fun Jnc =>
                       s13McZext (Arg.var ncp) fun nc64 =>
                       s13McOp64 (.add i64) (Arg.var h) (Arg.imm 768) fun hmv =>
                       Expr.load i64 (Arg.var hmv) fun mv64 =>
                       Expr.let_
                         { sig := [i32], code := OpCode.sext 32 64, args := (Arg.imm 1, ()) }
                         fun o64 =>
                       s13McOp64 (.shl i64) (Arg.var mv64) (Arg.var o64.fst) fun mv2 =>
                       Expr.let_ { sig := [i64, i64], code := OpCode.cmp .ult i64,
                                   args := (Arg.var nc64, Arg.var mv2, ()) } fun cnc =>
                       Expr.jnz (Arg.var cnc.fst)
                         (s13McPtr32 pWs1 ncp fun pws1 => Expr.store (Arg.var cand) (Arg.var pws1)
                          (s13McOp32 (.add i32) (Arg.var ncp) (Arg.imm 1) fun nc1 =>
                           Expr.jump Jnc.fst (Arg.var nc1, ())))
                         (Expr.jump Jnc.fst (Arg.var ncp, ())))
                      (Expr.jump Jc1.fst (Arg.var ncp, ()))) Blocks.nil) fun Jb =>
                  s13McZext (Arg.var nqlp) fun nq64 =>
                  Expr.let_ { sig := [i64, i64], code := OpCode.cmp .ult i64,
                              args := (Arg.var nq64, Arg.var mxv, ()) } fun cnq =>
                  Expr.jnz (Arg.var cnq.fst)
                    (s13McPtr32 pAr dr fun par1 => s13McPtr32 pAr dr fun par2 =>
                     Expr.load i32 (Arg.var par2) fun arv =>
                     s13McOp32 (.or i32) (Arg.var arv) (Arg.imm 33554432) fun nar =>
                     Expr.store (Arg.var nar) (Arg.var par1)
                       (s13McPtr32 pQl nqlp fun pql => Expr.store (Arg.var dr) (Arg.var pql)
                        (s13McOp32 (.add i32) (Arg.var nqlp) (Arg.imm 1) fun nq1 =>
                         Expr.jump Jb.fst (Arg.var nq1, ()))))
                    (Expr.jump Jb.fst (Arg.var nqlp, ()))) Blocks.nil) fun Ja =>
                 s13McZext (Arg.var nnoup) fun nn64 =>
                 Expr.let_ { sig := [i64, i64], code := OpCode.cmp .ult i64,
                             args := (Arg.var nn64, Arg.var mxv, ()) } fun cnn =>
                 Expr.jnz (Arg.var cnn.fst)
                   (s13McZext (Arg.var cand) fun c64a =>
                    s13McOp64 (.add i64) (Arg.var pLm) (Arg.var c64a) fun plm1 =>
                    s13McZext (Arg.var cand) fun c64b =>
                    s13McOp64 (.add i64) (Arg.var pLm) (Arg.var c64b) fun plm2 =>
                    Expr.load i8 (Arg.var plm2) fun lmv =>
                    Expr.let_ { sig := [i32], code := OpCode.trunc 32 8, args := (Arg.imm 4, ()) }
                      fun f4 =>
                    Expr.let_ { sig := [i8], code := OpCode.zext 8 32, args := (Arg.var lmv, ()) }
                      fun l32 =>
                    Expr.let_
                      { sig := [i8], code := OpCode.zext 8 32, args := (Arg.var f4.fst, ()) }
                      fun f32 =>
                    s13McOp32 (.or i32) (Arg.var l32.fst) (Arg.var f32.fst) fun lor =>
                    Expr.let_ { sig := [i32], code := OpCode.trunc 32 8, args := (Arg.var lor, ()) }
                      fun l8 =>
                    Expr.store (Arg.var l8.fst) (Arg.var plm1)
                      (s13McZext (Arg.var nnoup) fun nn64b =>
                       s13McOp64 (.add i64) (Arg.var mxv) (Arg.var nn64b) fun qidx =>
                       s13McOp64 (.mul i64) (Arg.var qidx) (Arg.imm 4) fun qoff =>
                       s13McOp64 (.add i64) (Arg.var pQl) (Arg.var qoff) fun pqlh =>
                       Expr.store (Arg.var cand) (Arg.var pqlh)
                         (s13McOp32 (.add i32) (Arg.var nnoup) (Arg.imm 1) fun nn1 =>
                          Expr.jump Ja.fst (Arg.var nn1, ()))))
                   (Expr.jump Ja.fst (Arg.var nnoup, ())))
                jFail)
             jFail)
          jFail)
       jFail)
    jFail

private theorem s13_scan_mp_cand_wp {Γ : Env} {Q : Post [i32]} {X : XPost}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState} {R : Mem 64 → Prop}
    {init_lits ticks1 mp2 : Val i64} {nqlp ncp nnoup dr cand : Val i32} {ok : Val .bool}
    {JmpL : Cont [i32, i32, i64, i64, i32]}
    {lm1 : List (BitVec 8)} {arp wsp ws1p qlp : List (BitVec 32)} {lmp : List (BitVec 8)}
    {ant : BitVec 64} {mlm : Mem 64}
    (hcl : s.core.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core)
    (hcl0 : s.core.cur_level = 0)
    (hncp_le : ncp.toNat ≤ 2 * c.max_vars)
    (hwsp_l : wsp.length = 2 * c.max_vars) (hws1p_l : ws1p.length = 2 * c.max_vars)
    (hbvaqp : S13ScanArBvaqInv c s arp qlp 0 nqlp.toNat)
    (hlm4p : S13LmBit4Inv c lm1 qlp 0 nnoup.toNat lmp)
    (hwp : FullWitnessInv c F0 F_cur { s.core with arena := arp })
    (hcntdp : ∀ i < ncp.toNat,
      (ws1p[i]?.getD 0#32).toNat ≤ init_lits.toNat ∧
      (ws1p[i]?.getD 0#32).toNat < 2 * s.core.cur_vars)
    (hdr_ref : dr.toNat ∈ fullArenaClauseRefsCore s.core)
    (hdr_nbvaq : (arp[dr.toNat]'(by
      have := (hw.arena.refs_wf _ hdr_ref).1; rw [hbvaqp.1]; have := hcl.arena_len_le
      omega) &&& 0x02000000#32) = 0#32)
    (hcand_ok : cand ≠ 0xFFFFFFFF#32 → cand.toNat < 2 * s.core.cur_vars)
    (hmlm : (FullMem c (s13MkSt s ant arp lmp wsp ws1p qlp) ⋆ R) mlm)
    (hCont : ∀ (nq1 nc1 nn1 : BitVec 32) arB lmB wsB ws1B qlB mB,
      nc1.toNat ≤ 2 * c.max_vars → wsB.length = 2 * c.max_vars →
      ws1B.length = 2 * c.max_vars → S13ScanArBvaqInv c s arB qlB 0 nq1.toNat →
      S13LmBit4Inv c lm1 qlB 0 nn1.toNat lmB →
      FullWitnessInv c F0 F_cur { s.core with arena := arB } →
      (∀ i < nc1.toNat,
        (ws1B[i]?.getD 0#32).toNat ≤ init_lits.toNat ∧
        (ws1B[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) →
      (FullMem c (s13MkSt s ant arB lmB wsB ws1B qlB) ⋆ R) mB →
      JmpL (nq1, nc1, ticks1, mp2, nn1, ()) mB) :
    wp Γ Q X (s13MpCandExpr c.hdr init_lits c.pVals c.pArena c.pLitMark c.pWsort
      c.pWorkStk1 c.pFlags c.pWorkStk2 (BitVec.ofNat 64 c.max_vars)
      nqlp ncp nnoup dr cand ok ticks1 mp2 JmpL) mlm := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv_le := hcl.cur_vars_le; have hal_le := hcl.arena_len_le
  have hlm_len := hcl.lit_mark_len; have hvals_len := hcl.vals_len; have hfl_len := hcl.flags_len
  have hset : ∀ x : BitVec 32, (BitVec.setWidth 64 x).toNat = x.toNat := bv64_setWidth_32
  have harp_l := hbvaqp.1; have hqlp_l := hbvaqp.2.1; have hnqlp_le := hbvaqp.2.2.1
  have hlmp_l := hlm4p.1; have hnnoup_le := hlm4p.2.1
  have hdr_lt_ar : dr.toNat + 3 ≤ arp.length := by
    have := (hw.arena.refs_wf _ hdr_ref).1; omega
  dsimp only [s13MpCandExpr, s13McZext, s13McOp64, s13McOp32, s13McCmp32, s13McPtr32, s13MkSt]
    at hmlm ⊢
  refine wp_join_state (α := BitVec 32 × BitVec 32 × BitVec 32 × List (BitVec 32) ×
      List (BitVec 8) × List (BitVec 32) × List (BitVec 32) × List (BitVec 32))
    (fun ⟨nq1, nc1, nn1, _, _, _, _, _⟩ => (nq1, nc1, nn1, ()))
    (fun ⟨nq1, nc1, nn1, arB, lmB, wsB, ws1B, qlB⟩ mB =>
      nc1.toNat ≤ 2 * c.max_vars ∧ wsB.length = 2 * c.max_vars ∧
      ws1B.length = 2 * c.max_vars ∧ S13ScanArBvaqInv c s arB qlB 0 nq1.toNat ∧
      S13LmBit4Inv c lm1 qlB 0 nn1.toNat lmB ∧
      FullWitnessInv c F0 F_cur { s.core with arena := arB } ∧
      (∀ i < nc1.toNat,
        (ws1B[i]?.getD 0#32).toNat ≤ init_lits.toNat ∧
        (ws1B[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
      (FullMem c (s13MkSt s ant arB lmB wsB ws1B qlB) ⋆ R) mB)
    (fun _ ⟨nq1, nc1, nn1, arB, lmB, wsB, ws1B, qlB⟩ mB
        ⟨hnc1, hwsB_l, hws1B_l, hbvaqB, hlm4B, hwB, hcntdB, hmB⟩ => by
      c0_hfast
      exact hCont nq1 nc1 nn1 arB lmB wsB ws1B qlB mB
        hnc1 hwsB_l hws1B_l hbvaqB hlm4B hwB hcntdB hmB)
    (fun Jcont hJcont => ?_)
  have hFail : wp Γ Q X (Expr.jump (Jcont, ()).fst
      (Arg.var nqlp, Arg.var ncp, Arg.var nnoup, ())) mlm := by
    dsimp only; c0_hfast
    exact hJcont ⟨nqlp, ncp, nnoup, arp, lmp, wsp, ws1p, qlp⟩ mlm
      ⟨hncp_le, hwsp_l, hws1p_l, hbvaqp, hlm4p, hwp, hcntdp, hmlm⟩
  c0_hsplit
  · c0_hsplit
    · c0_hsplit
      · have hcand_il : cand.toNat ≤ init_lits.toNat := by
          have h1 : BitVec.setWidth 64 cand ≤ init_lits := by assumption
          rw [BitVec.le_def, hset] at h1; exact h1
        have hcand_cv : cand.toNat < 2 * s.core.cur_vars := hcand_ok (by assumption)
        have hcand_lt : cand.toNat < 2 * c.max_vars := by omega
        have hcand_fl : (BitVec.setWidth 64 (cand >>> (1 : BitVec 32))).toNat <
            s.core.flags.length := by rw [hset, bv32_lshr1_bv, hfl_len]; omega
        c0_hsplit
        · have hcand_v : (BitVec.setWidth 64 cand).toNat < s.core.vals.length := by
            rw [hset, hvals_len]; omega
          c0_hsplit
          · refine wp_join_state (α := BitVec 32 × List (BitVec 8) × List (BitVec 32))
              (fun ⟨nn1, _, _⟩ => (nn1, ()))
              (fun ⟨nn1, lmA, qlA⟩ mA =>
                S13ScanArBvaqInv c s arp qlA 0 nqlp.toNat ∧
                S13LmBit4Inv c lm1 qlA 0 nn1.toNat lmA ∧
                (FullMem c (s13MkSt s ant arp lmA wsp ws1p qlA) ⋆ R) mA)
              (fun _ ⟨nn1, lmA, qlA⟩ mA ⟨hbvaqA, hlm4A, hmA⟩ => ?_)
              (fun Ja hJa => ?_)
            · have hqlA_l := hbvaqA.2.1
              dsimp only [s13MkSt] at hmA
              c0_hfast_nogrp
              refine wp_join_state (α := BitVec 32 × List (BitVec 32) × List (BitVec 32))
                (fun ⟨nq1, _, _⟩ => (nq1, ()))
                (fun ⟨nq1, arB, qlB⟩ mB =>
                  S13ScanArBvaqInv c s arB qlB 0 nq1.toNat ∧
                  S13LmBit4Inv c lm1 qlB 0 nn1.toNat lmA ∧
                  FullWitnessInv c F0 F_cur { s.core with arena := arB } ∧
                  (FullMem c (s13MkSt s ant arB lmA wsp ws1p qlB) ⋆ R) mB)
                (fun _ ⟨nq1, arB, qlB⟩ mB ⟨hbvaqB, hlm4B, hwB, hmB⟩ => ?_)
                (fun Jb hJb => ?_)
              · clear hmA; dsimp only [s13MkSt] at hmB
                have hcand_ws : (BitVec.setWidth 64 cand).toNat < wsp.length := by
                  rw [hset, hwsp_l]; omega
                have hmx_shl : (BitVec.ofNat 64 c.max_vars <<< (1 : Nat)).toNat =
                    2 * c.max_vars := by
                  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
                    Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]
                  omega
                c0_hfast_nogrp
                refine wp_join_state1 (t := i32) (α := BitVec 32 × List (BitVec 32))
                  (fun st => st.1)
                  (fun ⟨nc1, ws1C⟩ mC =>
                    nc1.toNat ≤ 2 * c.max_vars ∧ ws1C.length = 2 * c.max_vars ∧
                    (∀ i < nc1.toNat,
                      (ws1C[i]?.getD 0#32).toNat ≤ init_lits.toNat ∧
                      (ws1C[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
                    (FullMem c (s13MkSt s ant arB lmA wsp ws1C qlB) ⋆ R) mC)
                  (fun _ ⟨nc1, ws1C⟩ mC ⟨hnc1, hws1C_l, hcntdC, hmC⟩ => ?_)
                  (fun Jc1 hJc1 => ?_)
                · clear hmB; dsimp only [s13MkSt] at hmC; c0_hfast
                  · refine hJcont ⟨nq1, nc1, nn1, arB, lmA, _, ws1C, qlB⟩ _
                      ⟨hnc1, ?_, hws1C_l, hbvaqB, hlm4B, hwB, hcntdC, by assumption⟩
                    simp [hwsp_l]
                  · exact hJcont ⟨nq1, nc1, nn1, arB, lmA, wsp, ws1C, qlB⟩ mC
                      ⟨hnc1, hwsp_l, hws1C_l, hbvaqB, hlm4B, hwB, hcntdC, hmC⟩
                · c0_hfast
                  · have hnc_lt2 : ncp.toNat < 2 * c.max_vars := by
                      have h1 : (BitVec.setWidth 64 ncp).toNat <
                          (BitVec.ofNat 64 c.max_vars <<< (1 : Nat)).toNat :=
                        BitVec.lt_def.mp (by assumption)
                      rw [bv64_setWidth_32, hmx_shl] at h1; exact h1
                    have hnc_ws1 : (BitVec.setWidth 64 ncp).toNat < ws1p.length := by
                      rw [hset, hws1p_l]; exact hnc_lt2
                    have hnc1_n : (ncp + 1#32).toNat = ncp.toNat + 1 := by c0_bound
                    c0_hfast
                    refine hJc1 ⟨ncp + 1#32, _⟩ _ ⟨by rw [hnc1_n]; omega,
                      ?_, fun i hi => ?_, by assumption⟩
                    · simp [hws1p_l]
                    · rw [hnc1_n] at hi
                      by_cases hie : i = ncp.toNat
                      · subst hie
                        rw [hset, List.getElem?_set_self (by rw [hws1p_l]; omega), Option.getD_some]
                        exact ⟨hcand_il, hcand_cv⟩
                      · rw [hset, List.getElem?_set_ne (Ne.symm hie)]
                        exact hcntdp i (by omega)
                  · exact hJc1 ⟨ncp, ws1p⟩ mB ⟨hncp_le, hws1p_l, hcntdp, hmB⟩
                  · exact hJc1 ⟨ncp, ws1p⟩ mB ⟨hncp_le, hws1p_l, hcntdp, hmB⟩
              · c0_hsplit
                · have hnq_lt : nqlp.toNat < c.max_vars := by
                    have h1 : (BitVec.setWidth 64 nqlp).toNat <
                        (BitVec.ofNat 64 c.max_vars).toNat :=
                      BitVec.lt_def.mp (by assumption)
                    have h2 : (BitVec.ofNat 64 c.max_vars).toNat = c.max_vars := by c0_bound
                    rw [hset, h2] at h1; exact h1
                  have hnq1 : (nqlp + 1#32).toNat = nqlp.toNat + 1 := by c0_bound
                  have hnq_ql : (BitVec.setWidth 64 nqlp).toNat < qlA.length := by
                    rw [hset, hqlA_l]; omega
                  have hdr_ar_b : (BitVec.setWidth 64 dr).toNat < arp.length := by
                    rw [hset]; omega
                  c0_hfast
                  have ⟨hbvaq_next, hlm4_next, hw_next⟩ :=
                    s13_scan_cands_stepB_inv hcl hw hwp hcl0 hbvaqA hlm4A hnq_lt
                      hdr_ref (by omega) hdr_nbvaq
                  simp only [hset, show (33554432 : BitVec 32) = 0x02000000#32 from rfl] at hm
                  exact hJb ⟨nqlp + 1#32, _, _⟩ m
                    ⟨by rw [hnq1]; exact hbvaq_next, hlm4_next, hw_next, hm⟩
                · c0_hfast; exact hJb ⟨nqlp, arp, qlA⟩ mA ⟨hbvaqA, hlm4A, hwp, hmA⟩
            · c0_hsplit
              · have hnn_lt : nnoup.toNat < c.max_vars := by
                  have h1 : (BitVec.setWidth 64 nnoup).toNat <
                      (BitVec.ofNat 64 c.max_vars).toNat :=
                    BitVec.lt_def.mp (by assumption)
                  have h2 : (BitVec.ofNat 64 c.max_vars).toNat = c.max_vars := by c0_bound
                  rw [hset, h2] at h1; exact h1
                have hnn1 : (nnoup + 1#32).toNat = nnoup.toNat + 1 := by c0_bound
                have hmxnn : (BitVec.ofNat 64 c.max_vars + BitVec.setWidth 64 nnoup).toNat =
                    c.max_vars + nnoup.toNat := by c0_bound
                have hmxnn_ql : (BitVec.ofNat 64 c.max_vars +
                    BitVec.setWidth 64 nnoup).toNat < qlp.length := by
                  rw [hmxnn, hqlp_l]
                  exact Nat.lt_of_lt_of_eq (Nat.add_lt_add_left hnn_lt c.max_vars)
                    (Nat.two_mul c.max_vars).symm
                have hcand_lm : (BitVec.setWidth 64 cand).toNat < lmp.length := by
                  rw [hset, hlmp_l]; omega
                c0_hfast
                simp only [hmxnn] at hm; simp only [hset] at hm
                try simp only [bv8_trunc_or_4] at hm
                exact hJa ⟨nnoup + 1#32, _, _⟩ _
                  ⟨s13ScanArBvaqInv_set_ql_hi hbvaqp (idx := c.max_vars + nnoup.toNat) (by omega)
                     cand,
                   by rw [hnn1]; exact (s13LmBit4Inv_push hqlp_l hlm4p hnn_lt hcand_lt), hm⟩
              · c0_hfast; exact hJa ⟨nnoup, lmp, qlp⟩ mlm ⟨hbvaqp, hlm4p, hmlm⟩
          · exact hFail
        · exact hFail
      · exact hFail
    · exact hFail
  · exact hFail

theorem s13_scan_mp_wp {Γ : Env} {Q : Post [i32]} {X : XPost}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState} {R : Mem 64 → Prop}
    {row_off cur_qn : Val i32} {init_lits : Val i64} {J Jq : Cont [i32, i32, i32, i64]}
    {nql ncntd qi : Val i32} {ticks r_clines : Val i64} {qw : Val i32}
    {Js : Cont [i32, i32, i64]} {csz_bv : Val i32} {Jm : Cont [i32, i32, i32, i32]}
    {min_l min_d fc jf : Val i32} {Jc_join : Cont [i32, i32, i64, i32]}
    {moff msz : Val i32} {r_clines_min : Val i64} {Jmp : Cont [i32, i32, i64, i64, i32]}
    {ar ws ws1 ws2 : List (BitVec 32)} {lm1 : List (BitVec 8)} {ant : BitVec 64} {mf : Mem 64}
    (hslen : s.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core)
    (hdw : DenseWatchesInv F_cur s.core) (hcl0 : s.core.cur_level = 0)
    (_hqw_lits0 : ∀ x ∈ fullArenaClauseLitsCore s.core qw.toNat,
      (s.core.lit_mark[x]?.getD 0#8 &&& 1#8) ≠ 0#8 ∨ x < 2 * s.core.cur_vars)
    (_hlm_clr : ∀ l < 2 * s.core.cur_vars, (s.core.lit_mark[l]?.getD 0#8 &&& 6#8) = 0#8)
    (hqw_ref : qw.toNat ∈ fullArenaClauseRefsCore s.core)
    (hcsz_nat : csz_bv.toNat = fullArenaClauseSizeCore s.core qw.toNat)
    (hlm1_inv : LmBit2Inv c s.core.arena s.core.lit_mark qw.toNat 0 csz_bv.toNat lm1)
    (hml_lt : min_l.toNat < 2 * s.core.cur_vars)
    (hmoff_eq : moff.toNat = fullWatchOffCore s.core min_l.toNat)
    (hmsz_eq : msz.toNat = fullWatchSizeCore s.core min_l.toNat)
    (hnc_le : ncntd.toNat ≤ 2 * c.max_vars)
    (hws_l : ws.length = 2 * c.max_vars) (hws1_l : ws1.length = 2 * c.max_vars)
    (hbvaq : S13ScanArBvaqInv c s ar ws2 0 nql.toNat)
    (hw_ar : FullWitnessInv c F0 F_cur { s.core with arena := ar })
    (hcntd_ok : ∀ i < ncntd.toNat,
      (ws1[i]?.getD 0#32).toNat ≤ init_lits.toNat ∧ (ws1[i]?.getD 0#32).toNat < 2 * s.core.cur_vars)
    (hmf : (FullMem c
      { core := { s.core with arena := ar, lit_mark := lm1 },
        scratch :=
          { s.scratch with wsort := ws, work_stk1 := ws1, work_stk2 := ws2, ant_sz := ant } } ⋆
      R) mf)
    (hJmp : ∀ (nql2 nc2 : BitVec 32) (ticks2 mp2 : BitVec 64) (nnou2 : BitVec 32)
      ar2 lm2 ws2' ws12 ql2 mmp,
      nc2.toNat ≤ 2 * c.max_vars → ws2'.length = 2 * c.max_vars →
      ws12.length = 2 * c.max_vars → S13ScanArBvaqInv c s ar2 ql2 0 nql2.toNat →
      S13LmBit4Inv c lm1 ql2 0 nnou2.toNat lm2 →
      FullWitnessInv c F0 F_cur { s.core with arena := ar2 } →
      (∀ i < nc2.toNat,
        (ws12[i]?.getD 0#32).toNat ≤ init_lits.toNat ∧
        (ws12[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) →
      (FullMem c
        { core := { s.core with arena := ar2, lit_mark := lm2 },
          scratch :=
            { s.scratch with
              wsort := ws2', work_stk1 := ws12, work_stk2 := ql2, ant_sz := ant } } ⋆ R) mmp →
      Jmp (nql2, nc2, ticks2, mp2, nnou2, ()) mmp) :
    wp Γ Q X (s13ScanMp row_off cur_qn c.hdr init_lits c.pVals c.pWvec c.pWstk c.pArena
      c.pLitMark c.pScratchBuf c.pWsort c.pWorkStk1 c.pFlags c.pWorkStk2 c.pRepr r_clines
      J Jq nql ncntd qi ticks qw Js csz_bv Jm min_l min_d fc jf Jc_join moff msz
      (BitVec.ofNat 64 c.max_vars) r_clines_min Jmp) mf := by
  have hmx := c.hmaxv; have hwcap := c.hwcap; have har_b := c.harena
  unfold dimacsBound at hmx hwcap har_b
  have hcl := hslen.core_ok; have hcv_le := hcl.cur_vars_le; have hwv_len := hcl.wvec_len
  have hws_len := hcl.wstk_len_arr; have har_len := hcl.arena_len_arr
  have hal_le := hcl.arena_len_le; have hwlen_le := hcl.wlen_le
  have hlm_len := hcl.lit_mark_len; have hvals_len := hcl.vals_len
  have hfl_len := hcl.flags_len
  have hset : ∀ x : BitVec 32, (BitVec.setWidth 64 x).toNat = x.toNat := bv64_setWidth_32
  have hml_bd := hdw.layout.bounds min_l.toNat hml_lt
  have hml_sl := hdw.slices min_l.toNat hml_lt
  let moff0 := fullWatchOffCore s.core min_l.toNat
  let msz0 := fullWatchSizeCore s.core min_l.toNat
  have hqw_wf := hw.arena.refs_wf qw.toNat hqw_ref
  have har_l := hbvaq.1; have hws2_l := hbvaq.2.1
  dsimp only [s13ScanMp, s13ScanLarge, s13ScanHdr, s13Step, s13Steps, s13StepZ, s13StepsZ, s13Ld64,
    s13Ld32, s13Call64, s13Then, s13Else, s13GrpK4q, s13GrpB4q, s13GrpK3s, s13GrpB4m, s13GrpK4c,
    s13GrpK5mp, s13DummyVal, s13DummyTup, full_bva_scan_cands_body]
  refine wp_loop_inv
    (fun (nqlp, ncp, ticks_p, mp, nnoup, ()) mlm => ∃ arp lmp wsp ws1p qlp,
      moff0 ≤ mp.toNat ∧ mp.toNat ≤ moff0 + msz0 ∧ ncp.toNat ≤ 2 * c.max_vars ∧
      wsp.length = 2 * c.max_vars ∧ ws1p.length = 2 * c.max_vars ∧
      S13ScanArBvaqInv c s arp qlp 0 nqlp.toNat ∧
      S13LmBit4Inv c lm1 qlp 0 nnoup.toNat lmp ∧
      FullWitnessInv c F0 F_cur { s.core with arena := arp } ∧
      DenseWatchSliceOk F_cur s.core min_l.toNat mp.toNat (moff0 + msz0 - mp.toNat) ∧
      (∀ i < ncp.toNat,
        (ws1p[i]?.getD 0#32).toNat ≤ init_lits.toNat ∧
        (ws1p[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
      (FullMem c (s13MkSt s ant arp lmp wsp ws1p qlp) ⋆ R) mlm)
    (fun (_, _, _, mp, _, ()) _ => moff0 + msz0 - mp.toNat)
    (fun JmpL hJmpL => by
      c0_hfast
      have h1 : (BitVec.setWidth 64 moff).toNat = moff0 := by
        simp only [hset, hmoff_eq]; rfl
      exact hJmpL (nql, ncntd, _, _, 0#32, ()) mf
        ⟨ar, lm1, ws, ws1, ws2, by rw [h1]; exact Nat.le_refl _, by rw [h1]; omega,
         hnc_le, hws_l, hws1_l, hbvaq, s13LmBit4Inv_init hlm1_inv.1, hw_ar,
         by simpa only [h1, Nat.add_sub_cancel_left] using hml_sl, hcntd_ok, hmf⟩)
    (fun JmpL (nqlp, ncp, ticks_p, mp, nnoup, ()) mlm
        ⟨arp, lmp, wsp, ws1p, qlp, hmp_ge, hmp_le, hncp_le, hwsp_l, hws1p_l, hbvaqp,
         hlm4p, hwp, hrem, hcntdp, hmlm⟩ ihmp => ?_)
  dsimp only [s13MkSt] at hmlm
  have harp_l := hbvaqp.1; have hqlp_l := hbvaqp.2.1; have hnqlp_le := hbvaqp.2.2.1
  have hlmp_l := hlm4p.1; have hnnoup_le := hlm4p.2.1
  have hm_end_mod : (BitVec.setWidth 64 moff + BitVec.setWidth 64 msz).toNat = moff0 + msz0 := by
    rw [BitVec.toNat_add, hset, hset, hmoff_eq, hmsz_eq]; exact Nat.mod_eq_of_lt (by omega)
  c0_hsplit
  · have hmp_lt : mp.toNat < moff0 + msz0 := by rw [← hm_end_mod]; assumption
    have hmp_ws : mp.toNat < s.core.wstk.length := by omega
    have hmp1_n : (mp + 1#64).toNat = mp.toNat + 1 := by simp only [bv_c0]; omega
    c0_hsplit
    · have ⟨_, _, hrem_next⟩ :=
        bva_slice_bin_info hrem (by omega) hmp_ws (by assumption)
      c0_hfast
      exact ihmp (nqlp, ncp, ticks_p, mp + 1#64, nnoup, ()) mlm
        (by dsimp only; rw [hmp1_n]; omega)
        ⟨arp, lmp, wsp, ws1p, qlp, by rw [hmp1_n]; omega, by rw [hmp1_n]; omega,
         hncp_le, hwsp_l, hws1p_l, hbvaqp, hlm4p, hwp,
         by rw [hmp1_n, show moff0 + msz0 - (mp.toNat + 1) =
              moff0 + msz0 - mp.toNat - 1 by omega]; exact hrem_next,
         hcntdp, hmlm⟩
    · c0_hsplit
      · c0_hfast
        exact hJmp nqlp ncp ticks_p (mp + 1#64) nnoup arp lmp wsp ws1p qlp mlm
          hncp_le hwsp_l hws1p_l hbvaqp hlm4p hwp hcntdp hmlm
      · have ⟨h2le, hrem_next⟩ :=
          bva_slice_occ_info hrem (by omega) hmp_ws (by assumption)
        have hmp1_ws : mp.toNat + 1 < s.core.wstk.length := by omega
        have hmp1_mod : (mp.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 =
            mp.toNat + 1 := by
          rw [show BitVec.toNat (1 : BitVec 64) = 1 from rfl]; omega
        have ⟨_, hdr_ref, _⟩ :=
          fwd_slice_occ_info hrem (by omega) hmp_ws hmp1_ws (by assumption)
        have hdr_wf := hw.arena.refs_wf _ hdr_ref
        have hmp2_n : (mp + 1#64 + 1#64).toNat = mp.toNat + 2 := by simp only [bv_c0]; omega
        let dr := s.core.wstk[mp.toNat + 1]'hmp1_ws
        have hdr_lt_ar : dr.toNat + 3 ≤ arp.length := by
          dsimp only [dr]; have := hdr_wf.1; have := hcl.arena_len_le; omega
        have hdr_eq : s.core.wstk[(mp + 1#64).toNat]'(by rw [hmp1_n]; exact hmp1_ws) = dr := by
          dsimp only [dr]; simp only [hmp1_n]
        have hdr_mod : s.core.wstk[(mp.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(
            by rw [hmp1_mod]; exact hmp1_ws) = dr := by
          dsimp only [dr]; simp only [hmp1_mod]
        have hdr2_n : (BitVec.setWidth 64 dr + 2).toNat = dr.toNat + 2 := by
          change (BitVec.setWidth 64 dr + 2#64).toNat = _; simp only [bv_c0]; omega
        have hdr0_ar : (BitVec.setWidth 64 (s.core.wstk[(mp.toNat +
            BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
              rw [hmp1_mod]; exact hmp1_ws))).toNat < arp.length := by
          rw [hdr_mod, hset]; omega
        have hdr2_ar : (BitVec.setWidth 64 (s.core.wstk[(mp.toNat +
            BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
              rw [hmp1_mod]; exact hmp1_ws)) + 2).toNat < arp.length := by
          rw [hdr_mod, hdr2_n]; omega
        have hdr0_ar' : (BitVec.setWidth 64 (s.core.wstk[(mp + 1#64).toNat]'(by
            rw [hmp1_n]; exact hmp1_ws))).toNat < arp.length := by
          rw [hdr_eq, hset]; omega
        have hdr2_ar' : (BitVec.setWidth 64 (s.core.wstk[(mp + 1#64).toNat]'(by
            rw [hmp1_n]; exact hmp1_ws)) + 2).toNat < arp.length := by
          rw [hdr_eq, hdr2_n]; omega
        c0_hsplit
        · exact ihmp (nqlp, ncp, ticks_p, mp + 1#64 + 1#64, nnoup, ()) mlm
            (by dsimp only; rw [hmp2_n]; omega)
            ⟨arp, lmp, wsp, ws1p, qlp, by rw [hmp2_n]; omega,
             by rw [hmp2_n]; omega, hncp_le, hwsp_l, hws1p_l, hbvaqp, hlm4p, hwp,
             by rw [hmp2_n, show moff0 + msz0 - (mp.toNat + 2) =
                  moff0 + msz0 - mp.toNat - 2 by omega]; exact hrem_next,
             hcntdp, hmlm⟩
        · have hcont := ihmp (nqlp, ncp, ticks_p + 1#64, mp + 1#64 + 1#64, nnoup, ()) mlm
              (by dsimp only; rw [hmp2_n]; omega)
              ⟨arp, lmp, wsp, ws1p, qlp, by rw [hmp2_n]; omega,
               by rw [hmp2_n]; omega, hncp_le, hwsp_l, hws1p_l, hbvaqp, hlm4p, hwp,
               by rw [hmp2_n, show moff0 + msz0 - (mp.toNat + 2) =
                    moff0 + msz0 - mp.toNat - 2 by omega]; exact hrem_next,
               hcntdp, hmlm⟩
          c0_hsplit
          · exact hcont
          · c0_hsplit
            · exact hcont
            · have hdr_0248 : (arp[dr.toNat]'(by omega) &&& 0x02480000#32) = 0#32 := by
                have h1 : (arp[(BitVec.setWidth 64 (s.core.wstk[(mp.toNat +
                    BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
                      rw [hmp1_mod]; exact hmp1_ws))).toNat]'(by
                        rw [hdr_mod, hset]; omega) &&& (38273024 : BitVec 32)) = 0#32 := by
                  simpa only [← hdr_mod] using (by assumption : _)
                simp only [hdr_mod] at h1
                simpa only [hset, show (38273024 : BitVec 32) = 0x02480000#32 from rfl] using h1
              have hdr_sz_ar : arp[dr.toNat + 2]'(by omega) = csz_bv := by
                have hst1 : s.core.wstk[(BitVec.toNat mp + 1) % 2 ^ 64]'(by
                    rw [Nat.mod_eq_of_lt (by change mp.toNat + 1 < 2 ^ 64; omega)]
                    exact hmp1_ws) = dr := by
                  have hmpe : (BitVec.toNat mp + 1) % 2 ^ 64 =
                      (mp.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 := rfl
                  simp only [hmpe]; exact hdr_mod
                have heq1 : dr.toNat + 2 =
                    ((s.core.wstk[(BitVec.toNat mp + 1) % 2 ^ 64]'(by
                      rw [Nat.mod_eq_of_lt (by change mp.toNat + 1 < 2 ^ 64; omega)]
                      exact hmp1_ws)).toNat + 2) % 2 ^ 64 := by
                  rw [hst1]; exact (Nat.mod_eq_of_lt (by omega : dr.toNat + 2 < 2 ^ 64)).symm
                have h1 := congrArg (fun k => arp[k]?) heq1
                rw [List.getElem?_eq_getElem (by omega),
                  List.getElem?_eq_getElem (by rw [← heq1]; omega)] at h1
                exact Option.some.inj (h1.trans (congrArg some (by assumption)))
              have hdr_nbvaq := fid_bv32_bvaq_zero_of_and_02480000 hdr_0248
              have hdr_ng_s : fullArenaClauseGarbCore s.core dr.toNat = false := by
                have hdr_ng_ar := fid_bv32_garb_zero_of_and_02480000 hdr_0248
                unfold fullArenaClauseGarbCore fullArenaHdrCore
                rcases hbvaqp.2.2.2.2 dr.toNat (by omega) with heq | ⟨_, _, _, _, _, hset'⟩
                · rw [← heq, List.getElem?_eq_getElem (by omega), Option.getD_some]
                  simp [hdr_ng_ar]
                · rw [List.getElem?_eq_getElem (by omega)] at hset'
                  rw [Option.some.inj hset', s13_bv32_or_bvaq_garb] at hdr_ng_ar; simp [hdr_ng_ar]
              have hdr_sz_eq : fullArenaClauseSizeCore s.core dr.toNat = csz_bv.toNat := by
                have h2 := (s13_scan_cands_ar_lits_eq hcl hw hbvaqp hdr_ref).1
                unfold fullArenaClauseSizeCore
                rw [← h2, List.getElem?_eq_getElem (by omega), Option.getD_some, hdr_sz_ar]
              c0_hfast_nogrp
              try clear hdw hml_sl hqw_wf hrem hw_ar hcntd_ok hmf
              refine wp_join_state (α := BitVec 32 × Bool × BitVec 32)
                (fun ⟨cand, ok, djf⟩ => (cand, ok, djf, ()))
                (fun ⟨cand, _ok, _djf⟩ mdj =>
                  mdj = mlm ∧ (cand ≠ 0xFFFFFFFF#32 → cand.toNat < 2 * s.core.cur_vars))
                (fun _ ⟨cand, ok, _djf⟩ mdj ⟨hmdj, hcand_ok⟩ => by
                  subst hmdj
                  have hmlm' : (FullMem c (s13MkSt s ant arp lmp wsp ws1p qlp) ⋆ R) mdj := hmlm
                  have hdr_ref' :
                      (s.core.wstk[(mp + 1#64).toNat]'(by rw [hmp1_n]; exact hmp1_ws)).toNat ∈
                        fullArenaClauseRefsCore s.core := by
                    rw [hdr_eq]; exact hdr_ref
                  have hdr_nbvaq' :
                      (arp[(s.core.wstk[(mp + 1#64).toNat]'(by
                        rw [hmp1_n]; exact hmp1_ws)).toNat]'(by
                          have := (hw.arena.refs_wf _ hdr_ref').1; rw [harp_l]
                          have := hcl.arena_len_le; omega) &&& 0x02000000#32) = 0#32 := by
                    have hidx : (s.core.wstk[(mp + 1#64).toNat]'(by
                        rw [hmp1_n]; exact hmp1_ws)).toNat = dr.toNat :=
                      congrArg BitVec.toNat hdr_eq
                    simp only [hidx]; exact hdr_nbvaq
                  have hcand_e := s13_scan_mp_cand_wp (Γ := Γ) (Q := Q) (X := X) (R := R)
                    (init_lits := init_lits) (ticks1 := ticks_p + 1#64) (mp2 := mp + 1#64 + 1#64)
                    (nqlp := nqlp) (ncp := ncp) (nnoup := nnoup)
                    (dr := s.core.wstk[(mp + 1#64).toNat]'(by rw [hmp1_n]; exact hmp1_ws))
                    (cand := cand) (ok := ok)
                    (JmpL := JmpL) hcl hw hcl0 hncp_le hwsp_l hws1p_l hbvaqp hlm4p hwp hcntdp
                    hdr_ref' hdr_nbvaq' hcand_ok hmlm'
                    fun nq1 nc1 nn1 arB lmB wsB ws1B qlB mB
                      hnc1 hwsB hws1B hbvaqB hlm4B hwB hcntdB hmB =>
                      ihmp (nq1, nc1, ticks_p + 1#64, mp + 1#64 + 1#64, nn1, ()) mB
                        (by dsimp only; rw [hmp2_n]; omega)
                        ⟨arB, lmB, wsB, ws1B, qlB, by rw [hmp2_n]; omega,
                         by rw [hmp2_n]; omega, hnc1, hwsB, hws1B, hbvaqB, hlm4B, hwB,
                         by rw [hmp2_n, show moff0 + msz0 - (mp.toNat + 2) =
                              moff0 + msz0 - mp.toNat - 2 by omega]; exact hrem_next,
                         hcntdB, hmB⟩
                  dsimp only [s13MpCandExpr, s13McZext, s13McOp64, s13McOp32, s13McCmp32,
                    s13McPtr32] at hcand_e
                  exact hcand_e)
                (fun Jdj hJdj => ?_)
              · refine wp_loop_inv
                  (fun (cand, dj, ()) mdj => mdj = mlm ∧ dj.toNat ≤ csz_bv.toNat ∧
                    (cand ≠ 0xFFFFFFFF#32 → cand.toNat < 2 * s.core.cur_vars))
                  (fun (_, dj, _) _ => csz_bv.toNat - dj.toNat)
                  (fun Jd hJd => by
                    c0_hfast; exact hJd (0xFFFFFFFF#32, 0#32, ()) mlm
                      ⟨rfl, Nat.zero_le _, fun h => absurd rfl h⟩)
                  (fun Jd (cand, dj, ()) mdj ⟨hmdj, hdj_le, hcand_ok⟩ ihd => ?_)
                rcases hmdj with rfl
                c0_hsplit
                · have hdj_lt : dj.toNat < csz_bv.toNat := by assumption
                  have hdj1 : (dj + 1#32).toNat = dj.toNat + 1 := by c0_bound
                  have hdr_end : dr.toNat + 3 + csz_bv.toNat ≤ s.core.arena_len := by
                    have h1 : dr.toNat + 3 + fullArenaClauseSizeCore s.core dr.toNat ≤
                        fullArenaNextOff s.core.arena s.core.arena_len dr.toNat := by
                      simpa [dr] using hdr_wf.2.2.1
                    have h2 : fullArenaNextOff s.core.arena s.core.arena_len dr.toNat ≤
                        s.core.arena_len := by
                      simpa [dr] using hdr_wf.2.2.2.1
                    rw [← hdr_sz_eq]; omega
                  have hdj_sz : dj.toNat < fullArenaClauseSizeCore s.core dr.toNat := by
                    rw [hdr_sz_eq]; exact hdj_lt
                  have hdrj_n : (BitVec.setWidth 64 dr + 3 + BitVec.setWidth 64 dj).toNat =
                      dr.toNat + 3 + dj.toNat := by
                    change (BitVec.setWidth 64 dr + 3#64 + BitVec.setWidth 64 dj).toNat = _
                    c0_bound
                  have hdl_eq : arp[dr.toNat + 3 + dj.toNat]'(by omega) =
                      s.core.arena[dr.toNat + 3 + dj.toNat]'(by omega) := by
                    have h1 : arp[dr.toNat + 3 + dj.toNat]? =
                        s.core.arena[dr.toNat + 3 + dj.toNat]? :=
                      (s13_scan_cands_ar_lits_eq hcl hw hbvaqp hdr_ref).2 dj.toNat hdj_sz
                    rw [List.getElem?_eq_getElem (by omega),
                      List.getElem?_eq_getElem (by omega)] at h1
                    exact Option.some.inj h1
                  have hdl_lt : (arp[dr.toNat + 3 + dj.toNat]'(by omega)).toNat <
                      2 * s.core.cur_vars := by
                    rw [hdl_eq]
                    exact hw.arena.lits_lt dr.toNat hdr_ref hdr_ng_s _ (List.mem_of_getElem?
                      (fullArenaClauseLitsCore_getElem hdj_sz (by omega)))
                  have hdrj_ar : (BitVec.setWidth 64 (s.core.wstk[(mp.toNat +
                      BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
                        rw [hmp1_mod]; exact hmp1_ws)) + 3 + BitVec.setWidth 64 dj).toNat <
                      arp.length := by rw [hdr_mod, hdrj_n, harp_l]; omega
                  have hdl_lm : (BitVec.setWidth 64 (arp[(BitVec.setWidth 64
                      (s.core.wstk[(mp.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
                        rw [hmp1_mod]; exact hmp1_ws)) + 3 +
                      BitVec.setWidth 64 dj).toNat]'hdrj_ar)).toNat < lmp.length := by
                    simp only [hdr_mod]; simp only [hdrj_n, hset]; omega
                  have hdrj_ar' : (BitVec.setWidth 64 (s.core.wstk[(mp + 1#64).toNat]'(by
                      rw [hmp1_n]; exact hmp1_ws)) + 3 + BitVec.setWidth 64 dj).toNat <
                      arp.length := by rw [hdr_eq, hdrj_n, harp_l]; omega
                  have hdl_lm' : (BitVec.setWidth 64 (arp[(BitVec.setWidth 64
                      (s.core.wstk[(mp + 1#64).toNat]'(by rw [hmp1_n]; exact hmp1_ws)) + 3 +
                      BitVec.setWidth 64 dj).toNat]'hdrj_ar')).toNat < lmp.length := by
                    simp only [hdr_eq]; simp only [hdrj_n, hset]; omega
                  c0_hfast
                  · exact hJdj ⟨cand, false, dj⟩ mdj ⟨rfl, hcand_ok⟩
                  · exact hJdj ⟨cand, false, dj⟩ mdj ⟨rfl, hcand_ok⟩
                  · exact ihd (_, dj + 1#32, ()) mdj (by dsimp only; rw [hdj1]; omega)
                      ⟨rfl, by rw [hdj1]; omega,
                       fun _ => by
                         simpa only [show (1 : BitVec 64) = 1#64 from rfl, hdr_eq, hdrj_n,
                           hset] using hdl_lt⟩
                  · exact ihd (cand, dj + 1#32, ()) mdj (by dsimp only; rw [hdj1]; omega)
                      ⟨rfl, by rw [hdj1]; omega, hcand_ok⟩
                · c0_hfast; exact hJdj ⟨cand, true, dj⟩ mdj ⟨rfl, hcand_ok⟩
  · c0_hfast
    exact hJmp nqlp ncp ticks_p mp nnoup arp lmp wsp ws1p qlp mlm
      hncp_le hwsp_l hws1p_l hbvaqp hlm4p hwp hcntdp hmlm

end

end LeanQbe.T.Examples.Kissat.Proof.Factor
