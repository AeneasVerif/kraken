/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Src.Factor
public import LeanQbe.T.Examples.Kissat.Proof.Factor.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Factor.Helpers
public import LeanQbe.T.Examples.Kissat.Proof.Factor.Wp0
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
# Filter-Row Helpers, Sub-AST Navigators & Inner Loops (`Proof.Factor.WpFilter0`)

Zero-legacy (`0` `Full*` imports, `0` placeholders, `XPost`-polymorphic) invariants,
sub-AST navigators, and inner-loop WP proofs (`flt_bin_loop_wp`, `flt_clr_lm_wp`,
`flt_mark_loop_wp`, `flt_match_loop_wp`) for `full_bva_filter_row`.
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

/-! ## 1. BitVec, Arena `PH_BVA_Q`, and Filter-Row Invariants -/

@[local bv_c0] private theorem flt_bv64_one : (1 : BitVec 64).toNat = 1 := rfl
@[local bv_c0] private theorem flt_bv32_one : (1 : BitVec 32).toNat = 1 := rfl
@[local bv_c0] private theorem flt_bv64_two : (2 : BitVec 64).toNat = 2 := rfl
@[local bv_c0] private theorem flt_bv64_three : (3 : BitVec 64).toNat = 3 := rfl

private theorem flt_bv8_bit0_zero_of_u32 {x : BitVec 8}
    (h : (BitVec.setWidth 32 x &&& BitVec.ofNat 32 1) = BitVec.ofNat 32 0) :
    (x &&& 1#8) = 0#8 := by
  have h1 := congrArg (BitVec.setWidth 8) h
  simpa only [show BitVec.setWidth 8 (BitVec.ofNat 32 0) = 0#8 from rfl] using
    (bv8_trunc_and_w x 1#8).symm.trans h1

private theorem flt_bv32_or_bvaq_garb (x : BitVec 32) :
    ((x ||| 0x02000000#32) &&& 0x00080000#32) = (x &&& 0x00080000#32) := by
  rw [BitVec.and_or_distrib_right,
    show (0x02000000#32 &&& 0x00080000#32) = 0#32 from rfl, BitVec.or_zero]

private theorem flt_bv32_or_bvaq_shrk (x : BitVec 32) :
    ((x ||| 0x02000000#32) &&& 0x00800000#32) = (x &&& 0x00800000#32) := by
  rw [BitVec.and_or_distrib_right,
    show (0x02000000#32 &&& 0x00800000#32) = 0#32 from rfl, BitVec.or_zero]

theorem flt_bv32_bvaq_roundtrip {x : BitVec 32} (h : (x &&& 0x02000000#32) = 0#32) :
    ((x ||| 0x02000000#32) &&& ~~~0x02000000#32) = x := by
  rw [BitVec.and_or_distrib_right,
    show (0x02000000#32 &&& ~~~0x02000000#32) = 0#32 from rfl, BitVec.or_zero]
  have h1 : x = x &&& (~~~0x02000000#32 ||| 0x02000000#32) := by
    rw [show (~~~0x02000000#32 ||| 0x02000000#32) = BitVec.allOnes 32 from rfl, BitVec.and_allOnes]
  conv => rhs; rw [h1, BitVec.and_or_distrib_left, h, BitVec.or_zero]

theorem flt_bv32_clear_bvaq_of_zero {x : BitVec 32} (hx : (x &&& 0x02000000#32) = 0#32) :
    (x &&& ~~~0x02000000#32) = x := by
  have h1 : x = x &&& (~~~0x02000000#32 ||| 0x02000000#32) := by
    rw [show (~~~0x02000000#32 ||| 0x02000000#32) = BitVec.allOnes 32 from rfl, BitVec.and_allOnes]
  conv => rhs; rw [h1, BitVec.and_or_distrib_left, hx, BitVec.or_zero]

private theorem flt_list_eq_of_getElem?_eq {α : Type} {l1 l2 : List α}
    (hlen : l1.length = l2.length) (hget : ∀ i < l1.length, l1[i]? = l2[i]?) : l1 = l2 := by
  apply List.ext_getElem?; intro i
  by_cases hi : i < l1.length
  · exact hget i hi
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

theorem fltArBvaq_congr {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
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
      simp only [h1, ↓reduceIte, h2eq, h2, hset_r, Option.getD_some, flt_bv32_or_bvaq_shrk]
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
    · rw [hset_r, Option.getD_some, flt_bv32_or_bvaq_garb]
  · exact fullArenaClauseLitsCore_congr hsz fun j hj =>
      hgt_eq r hr (r + 3 + j) (by omega) (by omega)

@[expose] def FidFilterArInv (c : FullCfg) (s : FullState) (nrow_off lo hi : Nat)
    (sb ar : List (BitVec 32)) : Prop :=
  ar.length = c.arena_cap ∧ sb.length = c.scratch_cap ∧ nrow_off + hi ≤ c.scratch_cap ∧
  (∀ t, lo ≤ t → t < hi →
    let w := sb[nrow_off + t]?.getD 0#32
    (w &&& 0x80000000#32) = 0#32 →
      w.toNat ∈ fullArenaClauseRefsCore s.core ∧ w.toNat < c.arena_cap ∧
      (s.core.arena[w.toNat]?.getD 0#32 &&& 0x02000000#32) = 0#32 ∧
      ar[w.toNat]? = some (s.core.arena[w.toNat]?.getD 0#32 ||| 0x02000000#32)) ∧
  (∀ t1 t2, lo ≤ t1 → t1 < t2 → t2 < hi →
    (sb[nrow_off + t1]?.getD 0#32 &&& 0x80000000#32) = 0#32 →
    (sb[nrow_off + t2]?.getD 0#32 &&& 0x80000000#32) = 0#32 →
    sb[nrow_off + t1]?.getD 0#32 ≠ sb[nrow_off + t2]?.getD 0#32) ∧
  (∀ idx < c.arena_cap, ar[idx]? = s.core.arena[idx]? ∨
    (∃ t, lo ≤ t ∧ t < hi ∧
      (sb[nrow_off + t]?.getD 0#32 &&& 0x80000000#32) = 0#32 ∧
      (sb[nrow_off + t]?.getD 0#32).toNat = idx ∧
      (s.core.arena[idx]?.getD 0#32 &&& 0x02000000#32) = 0#32 ∧
      ar[idx]? = some (s.core.arena[idx]?.getD 0#32 ||| 0x02000000#32)))

theorem fidFilterArInv_init {c : FullCfg} {s : FullState} {nrow_off : Nat}
    (hlen : s.LengthsOk c) (hno : nrow_off ≤ c.scratch_cap) :
    FidFilterArInv c s nrow_off 0 0 s.scratch.scratch_buf s.core.arena :=
  ⟨hlen.core_ok.arena_len_arr, hlen.scratch_ok.scratch_buf_len, hno,
   fun _ _ h => by omega, fun _ _ _ _ h => by omega, fun _ _ => Or.inl rfl⟩

theorem fidFilterArInv_set_par {c : FullCfg} {s : FullState} {nrow_off par_off lo hi : Nat}
    {sb ar : List (BitVec 32)} (h : FidFilterArInv c s nrow_off lo hi sb ar)
    (hno_po : nrow_off + hi ≤ par_off) {idx : Nat} (hidx : par_off ≤ idx) (v : BitVec 32) :
    FidFilterArInv c s nrow_off lo hi (sb.set idx v) ar := by
  obtain ⟨har, hsb, hbd, hdom, hnd, hall⟩ := h
  refine ⟨har, by simp [hsb], hbd, fun t ht1 ht2 hw => ?_, fun t1 t2 h1 h2 h3 hw1 hw2 => ?_,
    fun i hi_c => ?_⟩
  · have hne : idx ≠ nrow_off + t := by omega
    rw [List.getElem?_set_ne hne] at hw ⊢; exact hdom t ht1 ht2 hw
  · have hne1 : idx ≠ nrow_off + t1 := by omega
    have hne2 : idx ≠ nrow_off + t2 := by omega
    rw [List.getElem?_set_ne hne1] at hw1
    rw [List.getElem?_set_ne hne2] at hw2
    rw [List.getElem?_set_ne hne1, List.getElem?_set_ne hne2]
    exact hnd t1 t2 h1 h2 h3 hw1 hw2
  · rcases hall i hi_c with heq | ⟨t, ht1, ht2, hwb, hwt, h0, hset⟩
    · exact Or.inl heq
    · have hne : idx ≠ nrow_off + t := by omega
      exact Or.inr ⟨t, ht1, ht2, by rw [List.getElem?_set_ne hne]; exact hwb,
        by rw [List.getElem?_set_ne hne]; exact hwt, h0, hset⟩

theorem fidFilterArInv_push_bin {c : FullCfg} {s : FullState} {nrow_off par_off hi : Nat}
    {sb ar : List (BitVec 32)} (h : FidFilterArInv c s nrow_off 0 hi sb ar)
    (hhi1 : nrow_off + (hi + 1) ≤ par_off) (hpo : par_off + (hi + 1) ≤ c.scratch_cap)
    {qw par_idx : BitVec 32} (hbin : (qw &&& 0x80000000#32) ≠ 0#32) :
    FidFilterArInv c s nrow_off 0 (hi + 1)
      ((sb.set (nrow_off + hi) qw).set (par_off + hi) par_idx) ar := by
  have h0 : FidFilterArInv c s nrow_off 0 (hi + 1) (sb.set (nrow_off + hi) qw) ar := by
    obtain ⟨har, hsb, hbd, hdom, hnd, hall⟩ := h
    refine ⟨har, by simp [hsb], by omega, fun t ht1 ht2 hw => ?_,
      fun t1 t2 h1 h2 h3 hw1 hw2 => ?_, fun i hi_c => ?_⟩
    · by_cases ht : t = hi
      · subst ht; rw [List.getElem?_set_self (by omega), Option.getD_some] at hw
        exact absurd hw hbin
      · have hne : nrow_off + hi ≠ nrow_off + t := by omega
        rw [List.getElem?_set_ne hne] at hw ⊢; exact hdom t ht1 (by omega) hw
    · by_cases ht : t2 = hi
      · subst ht; rw [List.getElem?_set_self (by omega), Option.getD_some] at hw2
        exact absurd hw2 hbin
      · have hne1 : nrow_off + hi ≠ nrow_off + t1 := by omega
        have hne2 : nrow_off + hi ≠ nrow_off + t2 := by omega
        rw [List.getElem?_set_ne hne1] at hw1; rw [List.getElem?_set_ne hne2] at hw2
        rw [List.getElem?_set_ne hne1, List.getElem?_set_ne hne2]
        exact hnd t1 t2 h1 h2 (by omega) hw1 hw2
    · rcases hall i hi_c with heq | ⟨t, ht1, ht2, hwb, hwt, h0v, hset⟩
      · exact Or.inl heq
      · have hne : nrow_off + hi ≠ nrow_off + t := by omega
        exact Or.inr ⟨t, ht1, by omega, by rw [List.getElem?_set_ne hne]; exact hwb,
          by rw [List.getElem?_set_ne hne]; exact hwt, h0v, hset⟩
  exact fidFilterArInv_set_par h0 (by omega) (by omega) par_idx

theorem fidFilterArInv_push_large {c : FullCfg} {s : FullState}
    {nrow_off par_off hi : Nat} {sb ar : List (BitVec 32)}
    (h : FidFilterArInv c s nrow_off 0 hi sb ar)
    (hhi1 : nrow_off + (hi + 1) ≤ par_off) (hpo : par_off + (hi + 1) ≤ c.scratch_cap)
    {dr par_idx : BitVec 32} (hbin : (dr &&& 0x80000000#32) = 0#32)
    (hdr_ref : dr.toNat ∈ fullArenaClauseRefsCore s.core) (hdr_lt : dr.toNat < c.arena_cap)
    (hdr_nbvaq : (ar[dr.toNat]'(by rw [h.1]; exact hdr_lt) &&& 0x02000000#32) = 0#32) :
    (s.core.arena[dr.toNat]?.getD 0#32 &&& 0x02000000#32) = 0#32 ∧
    FidFilterArInv c s nrow_off 0 (hi + 1)
      ((sb.set (nrow_off + hi) dr).set (par_off + hi) par_idx)
      (ar.set dr.toNat ((ar[dr.toNat]'(by rw [h.1]; exact hdr_lt)) ||| 0x02000000#32)) := by
  obtain ⟨har, hsb, hbd, hdom, hnd, hall⟩ := h
  have horig : ar[dr.toNat]? = s.core.arena[dr.toNat]? := by
    rcases hall dr.toNat hdr_lt with heq | ⟨_, _, _, _, _, h0v, hset⟩
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
  have har_eq : ar[dr.toNat]'(by omega) = s.core.arena[dr.toNat]?.getD 0#32 := by
    rw [← horig, List.getElem?_eq_getElem (by omega), Option.getD_some]
  have hne_prev : ∀ t < hi, (sb[nrow_off + t]?.getD 0#32 &&& 0x80000000#32) = 0#32 →
      sb[nrow_off + t]?.getD 0#32 ≠ dr := by
    intro t ht hw1 heq
    have ⟨_, _, h0t, hart⟩ := hdom t (Nat.zero_le _) ht hw1
    have hidx : (sb[nrow_off + t]?.getD 0#32).toNat = dr.toNat := congrArg BitVec.toNat heq
    rw [hidx, List.getElem?_eq_getElem (by omega)] at hart
    have hval := Option.some.inj hart
    have h1 : ((s.core.arena[dr.toNat]?.getD 0#32 ||| 0x02000000#32) &&& 0x02000000#32) =
        0x02000000#32 := by
      rw [BitVec.and_or_distrib_right,
        show (0x02000000#32 &&& 0x02000000#32) = 0x02000000#32 from rfl,
        hs_nbvaq, BitVec.zero_or]
    rw [hval] at hdr_nbvaq; exact absurd (hdr_nbvaq.symm.trans h1) (by decide)
  have h1 : FidFilterArInv c s nrow_off 0 (hi + 1) (sb.set (nrow_off + hi) dr)
      (ar.set dr.toNat ((ar[dr.toNat]'(by rw [har]; exact hdr_lt)) ||| 0x02000000#32)) := by
    refine ⟨by simp [har], by simp [hsb], by omega, fun t ht1 ht2 hw_b => ?_,
      fun t1 t2 h1 h2 h3 hw1 hw2 => ?_, fun i hi_c => ?_⟩
    · by_cases ht : t = hi
      · subst ht; rw [List.getElem?_set_self (by omega), Option.getD_some]
        refine ⟨hdr_ref, hdr_lt, hs_nbvaq, ?_⟩
        rw [List.getElem?_set_self (by omega), har_eq]
      · have hne_sb : nrow_off + hi ≠ nrow_off + t := by omega
        rw [List.getElem?_set_ne hne_sb] at hw_b ⊢
        obtain ⟨hr_t, hlt_t, h0_t, har_t⟩ := hdom t ht1 (by omega) hw_b
        have hne_nat : dr.toNat ≠ (sb[nrow_off + t]?.getD 0#32).toNat := fun h =>
          hne_prev t (by omega) hw_b (BitVec.eq_of_toNat_eq h.symm)
        refine ⟨hr_t, hlt_t, h0_t, ?_⟩
        rw [List.getElem?_set_ne hne_nat]; exact har_t
    · by_cases ht2' : t2 = hi
      · rw [ht2']; rw [List.getElem?_set_self (by omega), Option.getD_some]
        have hne1 : nrow_off + hi ≠ nrow_off + t1 := by omega
        rw [List.getElem?_set_ne hne1] at hw1 ⊢; exact hne_prev t1 (by omega) hw1
      · have hne1 : nrow_off + hi ≠ nrow_off + t1 := by omega
        have hne2 : nrow_off + hi ≠ nrow_off + t2 := by omega
        rw [List.getElem?_set_ne hne1] at hw1; rw [List.getElem?_set_ne hne2] at hw2
        rw [List.getElem?_set_ne hne1, List.getElem?_set_ne hne2]
        exact hnd t1 t2 h1 h2 (by omega) hw1 hw2
    · by_cases hid : i = dr.toNat
      · subst hid
        refine Or.inr ⟨hi, Nat.zero_le _, by omega,
          by rw [List.getElem?_set_self (by omega), Option.getD_some]; exact hbin,
          by rw [List.getElem?_set_self (by omega), Option.getD_some], hs_nbvaq, ?_⟩
        rw [List.getElem?_set_self (by omega), har_eq]
      · rw [List.getElem?_set_ne (Ne.symm hid)]
        rcases hall i hi_c with heq | ⟨t, ht1, ht2, hwb, hwt, h0v, hset⟩
        · exact Or.inl heq
        · have hne : nrow_off + hi ≠ nrow_off + t := by omega
          exact Or.inr ⟨t, ht1, by omega, by rw [List.getElem?_set_ne hne]; exact hwb,
            by rw [List.getElem?_set_ne hne]; exact hwt, h0v, hset⟩
  exact ⟨hs_nbvaq, fidFilterArInv_set_par h1 (by omega) (by omega) par_idx⟩

theorem fidFilterArInv_clear_skip {c : FullCfg} {s : FullState} {nrow_off ci hi : Nat}
    {sb ar : List (BitVec 32)} (h : FidFilterArInv c s nrow_off ci hi sb ar) (hci : ci < hi)
    (hbin : (sb[nrow_off + ci]?.getD 0#32 &&& 0x80000000#32) ≠ 0#32) :
    FidFilterArInv c s nrow_off (ci + 1) hi sb ar := by
  obtain ⟨har, hsb, hbd, hdom, hnd, hall⟩ := h
  refine ⟨har, hsb, hbd, fun t ht1 ht2 => hdom t (by omega) ht2,
    fun t1 t2 h1 h2 h3 => hnd t1 t2 (by omega) h2 h3, fun idx hidx => ?_⟩
  rcases hall idx hidx with heq | ⟨t, ht1, ht2, hwb, hwt, h0v, hset⟩
  · exact Or.inl heq
  · have htne : t ≠ ci := fun h => by subst h; exact hbin hwb
    exact Or.inr ⟨t, by omega, ht2, hwb, hwt, h0v, hset⟩

theorem fidFilterArInv_clear_step {c : FullCfg} {s : FullState} {nrow_off ci hi : Nat}
    {sb ar : List (BitVec 32)} (hs_ar : s.core.arena.length = c.arena_cap)
    (h : FidFilterArInv c s nrow_off ci hi sb ar) (hci : ci < hi)
    (hnb : (sb[nrow_off + ci]?.getD 0#32 &&& 0x80000000#32) = 0#32) :
    let idx := (sb[nrow_off + ci]?.getD 0#32).toNat
    idx < c.arena_cap ∧ FidFilterArInv c s nrow_off (ci + 1) hi sb
      (ar.set idx ((ar[idx]'(by rw [h.1]; exact (h.2.2.2.1 ci (by omega) hci hnb).2.1)) &&&
        ~~~0x02000000#32)) := by
  obtain ⟨har, hsb, hbd, hdom, hnd, hall⟩ := h
  intro idx
  obtain ⟨_, hidx_lt, h0_s, har_ci⟩ := hdom ci (Nat.le_refl _) hci hnb
  have hclr : (ar[idx]'(by omega) &&& ~~~0x02000000#32) = s.core.arena[idx]?.getD 0#32 := by
    rw [List.getElem?_eq_getElem (by omega)] at har_ci
    rw [Option.some.inj har_ci]; exact flt_bv32_bvaq_roundtrip h0_s
  refine ⟨hidx_lt, by simp [har], hsb, hbd, fun t ht1 ht2 hw => ?_,
    fun t1 t2 h1 h2 h3 => hnd t1 t2 (by omega) h2 h3, fun i hi_c => ?_⟩
  · obtain ⟨hr_t, hlt_t, h0_t, har_t⟩ := hdom t (by omega) ht2 hw
    have hne : sb[nrow_off + ci]?.getD 0#32 ≠ sb[nrow_off + t]?.getD 0#32 :=
      hnd ci t (Nat.le_refl _) (by omega) ht2 hnb hw
    have hne_nat : idx ≠ (sb[nrow_off + t]?.getD 0#32).toNat := fun h =>
      hne (BitVec.eq_of_toNat_eq h)
    refine ⟨hr_t, hlt_t, h0_t, ?_⟩
    rw [List.getElem?_set_ne hne_nat]; exact har_t
  · by_cases hid : i = idx
    · subst hid; left
      rw [List.getElem?_set_self (by omega), hclr,
        List.getElem?_eq_getElem (by rw [hs_ar]; exact hidx_lt), Option.getD_some]
    · rw [List.getElem?_set_ne (Ne.symm hid)]
      rcases hall i hi_c with heq | ⟨t, ht1, ht2, hwb, hwt, h0v, hset⟩
      · exact Or.inl heq
      · have htne : t ≠ ci := fun h => by subst h; exact hid hwt.symm
        exact Or.inr ⟨t, by omega, ht2, hwb, hwt, h0v, hset⟩

theorem fidFilterArInv_done {c : FullCfg} {s : FullState} {nrow_off hi : Nat}
    {sb ar : List (BitVec 32)} (hs_ar : s.core.arena.length = c.arena_cap)
    (h : FidFilterArInv c s nrow_off hi hi sb ar) : ar = s.core.arena := by
  apply flt_list_eq_of_getElem?_eq (by rw [h.1, hs_ar])
  intro i hi_lt
  rcases h.2.2.2.2.2 i (by rw [← h.1]; exact hi_lt) with heq | ⟨t, ht1, ht2, _⟩
  · exact heq
  · omega

@[expose] def FidFilterOutInv (c : FullCfg) (F_cur : List (List Nat)) (s : FullState)
    (step row_off nrow_off par_off cur_qn best_lit new_qn : Nat)
    (sb : List (BitVec 32)) : Prop :=
  let max_new := par_off - nrow_off
  sb.length = c.scratch_cap ∧ new_qn ≤ max_new ∧
  (∀ idx < c.scratch_cap,
    ¬ (nrow_off ≤ idx ∧ idx < nrow_off + max_new) →
    ¬ (par_off ≤ idx ∧ idx < par_off + max_new) →
    sb[idx]? = s.scratch.scratch_buf[idx]?) ∧
  ∀ nm < new_qn,
    let pi := (sb[par_off + nm]?.getD 0#32).toNat
    let nw := sb[nrow_off + nm]?.getD 0#32
    pi < cur_qn ∧
    ∃ res : List Nat,
      (∀ x ∈ res, x < 2 * s.core.cur_vars) ∧ (res.map (· / 2)).Nodup ∧
      FidBvaRowEntryOk F_cur s (s.scratch.scratch_buf[step - 1]?.getD 0#32).toNat
        (s.scratch.scratch_buf[row_off + pi]?.getD 0#32) res ∧
      FidBvaRowEntryOk F_cur s best_lit nw res ∧
      (∀ t < step, (cnfOfClauses F_cur).EntailsClause
        (cnfClause ((s.scratch.scratch_buf[t]?.getD 0#32).toNat :: res))) ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause (best_lit :: res))

theorem fidFilterOutInv_init {c : FullCfg} {F_cur : List (List Nat)} {s : FullState}
    {step row_off nrow_off par_off cur_qn best_lit : Nat}
    (hsb : s.scratch.scratch_buf.length = c.scratch_cap) :
    FidFilterOutInv c F_cur s step row_off nrow_off par_off cur_qn best_lit 0
      s.scratch.scratch_buf :=
  ⟨hsb, Nat.zero_le _, fun _ _ _ _ => rfl, fun _ h => by omega⟩

theorem fidFilterOutInv_push {c : FullCfg} {F_cur : List (List Nat)} {s : FullState}
    {step row_off nrow_off par_off cur_qn best_lit new_qn : Nat}
    {sb : List (BitVec 32)}
    (h : FidFilterOutInv c F_cur s step row_off nrow_off par_off cur_qn best_lit new_qn sb)
    (hno_le : nrow_off ≤ par_off) (hpo_fit : par_off + (par_off - nrow_off) ≤ c.scratch_cap)
    (hnew_lt : new_qn < par_off - nrow_off) {qi : Nat} (hqi : qi < cur_qn)
    (hqi_lt32 : qi < 2 ^ 32) {nw : BitVec 32}
    {res : List Nat} (hres_lt : ∀ x ∈ res, x < 2 * s.core.cur_vars)
    (hres_nd : (res.map (· / 2)).Nodup)
    (hok_old : FidBvaRowEntryOk F_cur s (s.scratch.scratch_buf[step - 1]?.getD 0#32).toNat
      (s.scratch.scratch_buf[row_off + qi]?.getD 0#32) res)
    (hok_new : FidBvaRowEntryOk F_cur s best_lit nw res)
    (hent_prev : ∀ t < step, (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((s.scratch.scratch_buf[t]?.getD 0#32).toNat :: res)))
    (hent_best : (cnfOfClauses F_cur).EntailsClause (cnfClause (best_lit :: res))) :
    FidFilterOutInv c F_cur s step row_off nrow_off par_off cur_qn best_lit (new_qn + 1)
      ((sb.set (nrow_off + new_qn) nw).set (par_off + new_qn) (BitVec.ofNat 32 qi)) := by
  obtain ⟨hsb, hle, hpres, hrows⟩ := h
  have hlt_no : nrow_off + new_qn < c.scratch_cap := by omega
  have hlt_po : par_off + new_qn < c.scratch_cap := by omega
  refine ⟨by simp [hsb], by omega, fun idx hidx hno hpo => ?_, fun nm hnm => ?_⟩
  · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
    exact hpres idx hidx hno hpo
  · by_cases hnm' : nm = new_qn
    · rw [hnm']
      have hpi : (((sb.set (nrow_off + new_qn) nw).set (par_off + new_qn)
          (BitVec.ofNat 32 qi))[par_off + new_qn]?.getD 0#32).toNat = qi := by
        rw [List.getElem?_set_self (by simp [hsb]; omega), Option.getD_some, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega)]
      have hnw : ((sb.set (nrow_off + new_qn) nw).set (par_off + new_qn)
          (BitVec.ofNat 32 qi))[nrow_off + new_qn]?.getD 0#32 = nw := by
        rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by rw [hsb]; omega),
          Option.getD_some]
      rw [hpi, hnw]
      exact ⟨hqi, res, hres_lt, hres_nd, hok_old, hok_new, hent_prev, hent_best⟩
    · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
        List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
      exact hrows nm (by omega)

@[expose] def fltMkSt (s : FullState) (ant : BitVec 64) (arx : List (BitVec 32))
    (lmx : List (BitVec 8)) (sbx : List (BitVec 32)) : FullState :=
  { core := { s.core with arena := arx, lit_mark := lmx },
    scratch := { s.scratch with scratch_buf := sbx, ant_sz := ant } }

theorem fltMkSt_lengthsOk {c : FullCfg} {s : FullState} (hlen : s.LengthsOk c)
    {ant : BitVec 64} {arx : List (BitVec 32)} {lmx : List (BitVec 8)} {sbx : List (BitVec 32)}
    (har : arx.length = c.arena_cap) (hlm : lmx.length = 2 * c.max_vars)
    (hsb : sbx.length = c.scratch_cap) :
    (fltMkSt s ant arx lmx sbx).LengthsOk c :=
  ⟨{ hlen.core_ok with arena_len_arr := har, lit_mark_len := hlm },
   { hlen.scratch_ok with scratch_buf_len := hsb }⟩

/-! ## 2. `full_bva_filter_row` Structural Navigators -/

@[expose] def fltDummyVal : (t : Ty) → Val t
  | .bits _ => 0 | .bool => true | .float _ => 0 | .pair a b => (fltDummyVal a, fltDummyVal b)

@[expose] def fltDummyTup : (ts : List Ty) → Tup Val ts
  | [] => () | t :: ts => (fltDummyVal t, fltDummyTup ts)

@[expose] def fltStep {rs : List Ty} : Expr Val Cont rs → Expr Val Cont rs
  | .let_ (ts := ts) _ k => k (fltDummyTup ts)
  | .load t _ k => k (fltDummyVal t)
  | .store _ _ k => k
  | .call (bs := bs) _ _ k => k (fltDummyTup bs)
  | _ => .hlt

@[expose] def fltSteps {rs : List Ty} : Nat → Expr Val Cont rs → Expr Val Cont rs
  | 0, e => e | n + 1, e => fltSteps n (fltStep e)

@[expose] def fltStepZ {rs : List Ty} : Expr Val Cont rs → Expr Val Cont rs
  | .let_ (Op.mk (.zext _ m) (a, ())) k => k (BitVec.setWidth m a.val, ())
  | .let_ (Op.mk (.add (.bits 64)) (a, b, ())) k => k (a.val + b.val, ())
  | e => fltStep e

@[expose] def fltStepsZ {rs : List Ty} : Nat → Expr Val Cont rs → Expr Val Cont rs
  | 0, e => e | n + 1, e => fltStepsZ n (fltStepZ e)

@[expose] def fltLd64 {rs : List Ty} (v : Val i64) : Expr Val Cont rs → Expr Val Cont rs
  | .load (.bits 64) _ k => k v | _ => .hlt

@[expose] def fltLd32 {rs : List Ty} (v : Val i32) : Expr Val Cont rs → Expr Val Cont rs
  | .load (.bits 32) _ k => k v | _ => .hlt

@[expose] def fltCall64 {rs : List Ty} (v : Val i64) : Expr Val Cont rs → Expr Val Cont rs
  | .call (bs := [.bits 64]) _ _ k => k (v, ()) | _ => .hlt

@[expose] def fltThen {rs : List Ty} : Expr Val Cont rs → Expr Val Cont rs
  | .jnz _ t _ => t | _ => .hlt

@[expose] def fltElse {rs : List Ty} : Expr Val Cont rs → Expr Val Cont rs
  | .jnz _ _ e => e | _ => .hlt

@[expose] def fltGrpK0 {rs : List Ty} (J : Cont []) : Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[]]) _ k => k (J, ()) | _ => .hlt

@[expose] def fltGrpB0 {rs : List Ty} (J : Cont []) : Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[]]) bs _ => match bs (J, ()) with | .cons f .nil => f ()
  | _ => .hlt

@[expose] def fltGrpK1_32 {rs : List Ty} (J : Cont [i32]) : Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 32]]) _ k => k (J, ()) | _ => .hlt

@[expose] def fltGrpB1_32 {rs : List Ty} (v : Val i32) (J : Cont [i32]) :
    Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 32]]) bs _ => match bs (J, ()) with | .cons f .nil => f (v, ())
  | _ => .hlt

@[expose] def fltGrpB1_64 {rs : List Ty} (v : Val i64) (J : Cont [i64]) :
    Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 64]]) bs _ => match bs (J, ()) with | .cons f .nil => f (v, ())
  | _ => .hlt

@[expose] def fltGrpK1_64 {rs : List Ty} (J : Cont [i64]) : Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 64]]) _ k => k (J, ()) | _ => .hlt

@[expose] def fltGrpK2 {rs : List Ty} (J : Cont [i32, i64]) : Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 32, .bits 64]]) _ k => k (J, ()) | _ => .hlt

@[expose] def fltGrpB2_64 {rs : List Ty} (v : Tup Val [i64, i64]) (J : Cont [i64, i64]) :
    Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 64, .bits 64]]) bs _ => match bs (J, ()) with | .cons f .nil => f v
  | _ => .hlt

@[expose] def fltGrpK2_64 {rs : List Ty} (J : Cont [i64, i64]) :
    Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 64, .bits 64]]) _ k => k (J, ()) | _ => .hlt

@[expose] def fltGrpK3 {rs : List Ty} (J : Cont [i32, i32, i64]) :
    Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 32, .bits 32, .bits 64]]) _ k => k (J, ()) | _ => .hlt

@[expose] def fltGrpB3 {rs : List Ty} (v : Tup Val [i32, i32, i64])
    (J : Cont [i32, i32, i64]) : Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 32, .bits 32, .bits 64]]) bs _ =>
    match bs (J, ()) with | .cons f .nil => f v
  | _ => .hlt

@[expose] def fltGrpK3_64 {rs : List Ty} (J : Cont [i32, i64, i64]) :
    Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 32, .bits 64, .bits 64]]) _ k => k (J, ()) | _ => .hlt

@[expose] def fltGrpK4 {rs : List Ty} (J : Cont [i32, i32, i32, i32]) :
    Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 32, .bits 32, .bits 32, .bits 32]]) _ k => k (J, ()) | _ => .hlt

@[expose] def fltGrpB4 {rs : List Ty} (v : Tup Val [i32, i32, i32, i32])
    (J : Cont [i32, i32, i32, i32]) : Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 32, .bits 32, .bits 32, .bits 32]]) bs _ =>
    match bs (J, ()) with | .cons f .nil => f v
  | _ => .hlt

@[expose] def fltHdrExpr (h row_off nrow_off par_off cur_qn best_lit : Val i32)
    (h64 pWv pWs pAr pLm pSb pRp r_cl : Val i64) : Expr Val Cont [i32] :=
  let _ := h
  full_bva_filter_row_body Val Cont (h64, row_off, nrow_off, par_off, cur_qn, best_lit, ())
    |> fltStep |> fltLd64 pWv |> fltStep |> fltLd64 pWs
    |> fltStep |> fltLd64 pAr |> fltStep |> fltLd64 pLm
    |> fltStep |> fltLd64 pSb |> fltStep |> fltLd64 pRp
    |> fltStep |> fltStep |> fltCall64 r_cl |> fltStep

@[expose] def fltOuterContExpr (row_off nrow_off par_off cur_qn best_lit : Val i32)
    (h64 pWv pWs pAr pLm pSb pRp r_cl : Val i64) (J_out : Cont [i32, i32, i64])
    (new_qn qi : Val i32) (ticks : Val i64) (J_cond : Cont []) : Expr Val Cont [i32] :=
  fltHdrExpr 0#32 row_off nrow_off par_off cur_qn best_lit h64 pWv pWs pAr pLm pSb pRp r_cl
    |> fltGrpB3 (new_qn, qi, ticks, ()) J_out
    |> fltGrpK0 J_cond

@[expose] def fltStepExpr (row_off nrow_off par_off cur_qn best_lit : Val i32)
    (h64 pWv pWs pAr pLm pSb pRp r_cl : Val i64) (J_out : Cont [i32, i32, i64])
    (new_qn qi : Val i32) (ticks : Val i64) (J_cond : Cont []) (qw : Val i32)
    (J_step : Cont [i32, i64]) : Expr Val Cont [i32] :=
  fltOuterContExpr row_off nrow_off par_off cur_qn best_lit h64 pWv pWs pAr pLm pSb pRp r_cl
      J_out new_qn qi ticks J_cond
    |> fltStep |> fltThen |> fltStep |> fltThen |> fltSteps 4 |> fltLd32 qw
    |> fltGrpK2 J_step

@[expose] def fltBinLoopExpr (row_off nrow_off par_off cur_qn best_lit : Val i32)
    (h64 pWv pWs pAr pLm pSb pRp r_cl : Val i64) (J_out : Cont [i32, i32, i64])
    (new_qn qi : Val i32) (ticks : Val i64) (J_cond : Cont []) (qw : Val i32)
    (J_step J_bin : Cont [i32, i64]) (qoff qsz : Val i32) (deg : Val i32)
    (r_cl_bin : Val i64) (qp : Val i64) (J_qp : Cont [i64]) : Expr Val Cont [i32] :=
  fltStepExpr row_off nrow_off par_off cur_qn best_lit h64 pWv pWs pAr pLm pSb pRp r_cl
      J_out new_qn qi ticks J_cond qw J_step
    |> fltSteps 2 |> fltThen
    |> fltStepsZ 6 |> fltLd32 qoff |> fltStepZ
    |> fltStepsZ 6 |> fltLd32 qsz |> fltStepsZ 3
    |> fltStepsZ 3 |> fltLd32 deg |> fltStepZ |> fltCall64 r_cl_bin |> fltStepZ
    |> fltGrpK2 J_bin
    |> fltGrpK1_64 J_qp |> fltGrpB1_64 qp J_qp

@[expose] def fltLargeHdrExpr (row_off nrow_off par_off cur_qn best_lit : Val i32)
    (h64 pWv pWs pAr pLm pSb pRp r_cl : Val i64) (J_out : Cont [i32, i32, i64])
    (new_qn qi : Val i32) (ticks : Val i64) (J_cond : Cont []) (qw : Val i32)
    (J_step : Cont [i32, i64]) (csz : Val i32) : Expr Val Cont [i32] :=
  fltStepExpr row_off nrow_off par_off cur_qn best_lit h64 pWv pWs pAr pLm pSb pRp r_cl
      J_out new_qn qi ticks J_cond qw J_step
    |> fltSteps 2 |> fltElse
    |> fltStepsZ 4 |> fltLd32 csz |> fltStepZ

@[expose] def fltMarkLoopExpr (row_off nrow_off par_off cur_qn best_lit : Val i32)
    (h64 pWv pWs pAr pLm pSb pRp r_cl : Val i64) (J_out : Cont [i32, i32, i64])
    (new_qn qi : Val i32) (ticks : Val i64) (J_cond : Cont []) (qw : Val i32)
    (J_step : Cont [i32, i64]) (csz : Val i32)
    (J_post : Cont [i32, i32, i32, i32]) (min_l min_d fc k : Val i32)
    (J_mark : Cont [i32, i32, i32, i32]) : Expr Val Cont [i32] :=
  fltLargeHdrExpr row_off nrow_off par_off cur_qn best_lit h64 pWv pWs pAr pLm pSb pRp r_cl
      J_out new_qn qi ticks J_cond qw J_step csz
    |> fltGrpK4 J_post |> fltGrpB4 (min_l, min_d, fc, k, ()) J_mark

@[expose] def fltPostMarkExpr (row_off nrow_off par_off cur_qn best_lit : Val i32)
    (h64 pWv pWs pAr pLm pSb pRp r_cl : Val i64) (J_out : Cont [i32, i32, i64])
    (new_qn qi : Val i32) (ticks : Val i64) (J_cond : Cont []) (qw : Val i32)
    (J_step : Cont [i32, i64]) (csz min_l min_d fc k : Val i32)
    (J_post : Cont [i32, i32, i32, i32]) (J_clr : Cont [i32, i64]) : Expr Val Cont [i32] :=
  fltLargeHdrExpr row_off nrow_off par_off cur_qn best_lit h64 pWv pWs pAr pLm pSb pRp r_cl
      J_out new_qn qi ticks J_cond qw J_step csz
    |> fltGrpB4 (min_l, min_d, fc, k, ()) J_post
    |> fltGrpK2 J_clr

@[expose] def fltGrpB2 {rs : List Ty} (v : Tup Val [i32, i64]) (J : Cont [i32, i64]) :
    Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 32, .bits 64]]) bs _ => match bs (J, ()) with | .cons f .nil => f v
  | _ => .hlt

@[expose] def fltClrLmExpr (row_off nrow_off par_off cur_qn best_lit : Val i32)
    (h64 pWv pWs pAr pLm pSb pRp r_cl : Val i64) (J_out : Cont [i32, i32, i64])
    (new_qn qi : Val i32) (ticks : Val i64) (J_cond : Cont []) (qw : Val i32)
    (J_step : Cont [i32, i64]) (csz min_l min_d fc k : Val i32)
    (J_post : Cont [i32, i32, i32, i32]) (nq_c : Val i32) (tk_c : Val i64)
    (J_clr : Cont [i32, i64]) (j : Val i32) (J_j : Cont [i32]) : Expr Val Cont [i32] :=
  fltLargeHdrExpr row_off nrow_off par_off cur_qn best_lit h64 pWv pWs pAr pLm pSb pRp r_cl
      J_out new_qn qi ticks J_cond qw J_step csz
    |> fltGrpB4 (min_l, min_d, fc, k, ()) J_post
    |> fltGrpB2 (nq_c, tk_c, ()) J_clr
    |> fltGrpK1_32 J_j |> fltGrpB1_32 j J_j

@[expose] def fltMatchLoopExpr (row_off nrow_off par_off cur_qn best_lit : Val i32)
    (h64 pWv pWs pAr pLm pSb pRp r_cl : Val i64) (J_out : Cont [i32, i32, i64])
    (new_qn qi : Val i32) (ticks : Val i64) (J_cond : Cont []) (qw : Val i32)
    (J_step : Cont [i32, i64]) (csz min_l min_d fc k : Val i32)
    (J_post : Cont [i32, i32, i32, i32]) (J_clr : Cont [i32, i64])
    (qoff qsz : Val i32) (r_cl_m : Val i64) (J_mexit : Cont [i32, i64, i64])
    (tk_m qp : Val i64) (J_qp : Cont [i64, i64]) : Expr Val Cont [i32] :=
  fltLargeHdrExpr row_off nrow_off par_off cur_qn best_lit h64 pWv pWs pAr pLm pSb pRp r_cl
      J_out new_qn qi ticks J_cond qw J_step csz
    |> fltGrpB4 (min_l, min_d, fc, k, ()) J_post
    |> fltGrpK2 J_clr
    |> fltStepZ |> fltThen |> fltStepZ |> fltThen
    |> fltStepsZ 5 |> fltLd32 qoff |> fltStepZ
    |> fltStepsZ 6 |> fltLd32 qsz |> fltStepsZ 4 |> fltCall64 r_cl_m |> fltStepZ
    |> fltGrpK3_64 J_mexit
    |> fltGrpK2_64 J_qp |> fltGrpB2_64 (tk_m, qp, ()) J_qp

/-! ## 3. Inner Loop WP Proofs -/

theorem flt_bin_loop_wp {Γ : Env} {Q : Post [i32]} {X : XPost}
    {c : FullCfg} {F_cur : List (List Nat)} {s : FullState}
    {R : Mem 64 → Prop} {row_off nrow_off par_off cur_qn best_lit new_qn qi : Val i32}
    {ticks r_cl r_cl_bin : Val i64} {J_out : Cont [i32, i32, i64]} {J_cond : Cont []}
    {qw : Val i32} {J_step J_bin : Cont [i32, i64]}
    {step bump : Nat} {ar sb : List (BitVec 32)} {ant : BitVec 64} {ml : Mem 64}
    (hslen : s.LengthsOk c)
    (hdw : DenseWatchesInv F_cur s.core)
    (hstep : 1 ≤ step) (hro_n : row_off.toNat = (s.scratch.scratch_buf[fidStepsCap c.scratch_cap +
      (step - 1)]?.getD 0#32).toNat)
    (hcqn_n : cur_qn.toNat = (s.scratch.scratch_buf[2 * fidStepsCap c.scratch_cap +
      (step - 1)]?.getD 0#32).toNat)
    (hnro_n : nrow_off.toNat = bump) (hno_le : nrow_off.toNat ≤ par_off.toNat)
    (hpo_fit : par_off.toNat + (par_off.toNat - nrow_off.toNat) ≤ c.scratch_cap)
    (hnew_lt : new_qn.toNat < par_off.toNat - nrow_off.toNat)
    (hqi_lt : qi.toNat < cur_qn.toNat)
    (hmat : FidBvaMatrixInv c F_cur s step bump)
    (hout : FidFilterOutInv c F_cur s step row_off.toNat nrow_off.toNat par_off.toNat
      cur_qn.toNat best_lit.toNat new_qn.toNat sb)
    (har_inv : FidFilterArInv c s nrow_off.toNat 0 new_qn.toNat sb ar)
    (hbin : (qw &&& 0x80000000#32) ≠ 0#32)
    (hqw_eq : qw = s.scratch.scratch_buf[row_off.toNat + qi.toNat]?.getD 0#32)
    (hml : (FullMem c (fltMkSt s ant ar s.core.lit_mark sb) ⋆ R) ml)
    (hBin : ∀ (nq' : BitVec 32) (qp' : BitVec 64) (sb' : List (BitVec 32)) (mp : Mem 64),
      FidFilterOutInv c F_cur s step row_off.toNat nrow_off.toNat par_off.toNat
        cur_qn.toNat best_lit.toNat nq'.toNat sb' →
      FidFilterArInv c s nrow_off.toNat 0 nq'.toNat sb' ar →
      (FullMem c (fltMkSt s ant ar s.core.lit_mark sb') ⋆ R) mp →
      J_bin (nq', qp', ()) mp) :
    let q := (qw &&& 0x7FFFFFFF#32).toNat
    let qoff := BitVec.ofNat 32 (fullWatchOffCore s.core q)
    let qsz := BitVec.ofNat 32 (fullWatchSizeCore s.core q)
    wp Γ Q X (fltStepExpr row_off nrow_off par_off cur_qn best_lit c.hdr c.pWvec c.pWstk c.pArena
      c.pLitMark c.pScratchBuf c.pRepr r_cl J_out new_qn qi ticks J_cond qw J_step
      |> fltSteps 2 |> fltThen |> fltStepsZ 6 |> fltLd32 qoff |> fltStepZ |> fltStepsZ 6
      |> fltLd32 qsz |> fltStepsZ 3 |> fltStepsZ 3 |> fltLd32 0#32 |> fltStepZ
      |> fltCall64 r_cl_bin |> fltStepZ |> fltGrpK2 J_bin) ml := by
  intro q qoff qsz
  have hmx := c.hmaxv; have hwcap := c.hwcap; have hscr := c.hscr; unfold dimacsBound at *
  have hcl := hslen.core_ok; have hcv_le := hcl.cur_vars_le; have hwv_len := hcl.wvec_len
  have hws_len := hcl.wstk_len_arr; have hwlen_le := hcl.wlen_le
  have hsb_len : sb.length = c.scratch_cap := hout.1
  have hfr_res := hmat.2.2.2.2.2 (step - 1) (by omega)
  have ⟨res, hres_lt, hres_nd, hok_old, hent_prev, _⟩ := hfr_res.2.2.2.2.2 qi.toNat (by omega)
  rw [← hro_n, ← hqw_eq] at hok_old
  have hbin_info : q < 2 * s.core.cur_vars ∧ res = [q] ∧
      (cnfOfClauses F_cur).EntailsClause
        (cnfClause [(s.scratch.scratch_buf[step - 1]?.getD 0#32).toNat, q]) := by
    unfold FidBvaRowEntryOk at hok_old; rw [ite_eq_left hbin] at hok_old; exact hok_old
  have hq_lt : q < 2 * s.core.cur_vars := hbin_info.1
  have hq_bd := hdw.layout.bounds q hq_lt; have hq_sl := hdw.slices q hq_lt
  have hqoff_nat : (BitVec.setWidth 64 qoff).toNat = fullWatchOffCore s.core q := by
    rw [fid_bv64_32, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hqsz_nat : (BitVec.setWidth 64 qsz).toNat = fullWatchSizeCore s.core q := by
    rw [fid_bv64_32, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hqend_nat : (BitVec.setWidth 64 qoff + BitVec.setWidth 64 qsz).toNat =
      fullWatchOffCore s.core q + fullWatchSizeCore s.core q := by
    rw [BitVec.toNat_add, hqoff_nat, hqsz_nat, Nat.mod_eq_of_lt (by omega)]
  dsimp only [fltStepExpr, fltOuterContExpr, fltHdrExpr, fltSteps, fltStep, fltStepsZ, fltStepZ,
    fltLd64, fltLd32, fltCall64, fltThen, fltElse, fltGrpK0, fltGrpK2, fltGrpB3, fltDummyVal,
    fltDummyTup, full_bva_filter_row_body]
  refine wp_while_state1 (t := i64) (α := BitVec 64) id
    (fun qp => fullWatchOffCore s.core q + fullWatchSizeCore s.core q - qp.toNat)
    (fun qp mp => fullWatchOffCore s.core q ≤ qp.toNat ∧
      qp.toNat ≤ fullWatchOffCore s.core q + fullWatchSizeCore s.core q ∧
      DenseWatchSliceOk F_cur s.core q qp.toNat
        (fullWatchOffCore s.core q + fullWatchSizeCore s.core q - qp.toNat) ∧
      (FullMem c (fltMkSt s ant ar s.core.lit_mark sb) ⋆ R) mp)
    (fun Jp hJp => by
      c0_hfast
      refine hJp (BitVec.setWidth 64 qoff) ml ⟨by rw [hqoff_nat]; exact Nat.le_refl _,
        by rw [hqoff_nat]; omega, ?_, hml⟩
      simpa only [hqoff_nat, Nat.add_sub_cancel_left] using hq_sl)
    (fun Jp qp mp ⟨hqp_ge, hqp_le, hsl, hmp⟩ ihp => ?_)
  clear hml
  dsimp only [fltMkSt] at hmp
  c0_hfast_nogrp
  rotate_left 1
  · c0_hfast; exact hBin new_qn qp sb mp hout har_inv hmp
  have hqp_lt : qp.toNat < fullWatchOffCore s.core q + fullWatchSizeCore s.core q := by
    rw [← hqend_nat]; exact BitVec.lt_def.mp (by assumption)
  have hrem_pos : 0 < fullWatchOffCore s.core q + fullWatchSizeCore s.core q - qp.toNat := by omega
  have hqp_ws : qp.toNat < s.core.wstk.length := by omega
  c0_hfast_nogrp
  refine wp_join_state (α := BitVec 32 × BitVec 64) (fun x => (x.1, x.2, ()))
    (fun (nq1, qp1) mp1 => nq1 = new_qn ∧
      fullWatchOffCore s.core q ≤ qp1.toNat ∧
      qp1.toNat ≤ fullWatchOffCore s.core q + fullWatchSizeCore s.core q ∧
      qp1.toNat - qp.toNat ≥ 1 ∧
      DenseWatchSliceOk F_cur s.core q qp1.toNat
        (fullWatchOffCore s.core q + fullWatchSizeCore s.core q - qp1.toNat) ∧
      (FullMem c (fltMkSt s ant ar s.core.lit_mark sb) ⋆ R) mp1)
    (fun _ (nq1, qp1) mp1 ⟨_, h1, h2, hgt, hsl1, hm1⟩ => by
      c0_hfast; exact ihp qp1 mp1 (by omega) ⟨h1, h2, hsl1, hm1⟩)
    (fun Jnext hJnext => ?_)
  c0_hfast_nogrp
  · have hnw := bva_slice_bin_info hsl hrem_pos hqp_ws (by assumption)
    have hno_sb : (BitVec.setWidth 64 (nrow_off + new_qn)).toNat < sb.length := by
      rw [fid_bv64_32, hsb_len]; change (nrow_off + new_qn).toNat < _; c0_bound
    have hpo_sb : (BitVec.setWidth 64 (par_off + new_qn)).toNat < sb.length := by
      rw [fid_bv64_32, hsb_len]; change (par_off + new_qn).toNat < _; c0_bound
    have hnew1 : (new_qn + 1#32).toNat = new_qn.toNat + 1 := by c0_bound
    have hno_eq : (nrow_off + new_qn).toNat = nrow_off.toNat + new_qn.toNat := by c0_bound
    have hpo_eq : (par_off + new_qn).toNat = par_off.toNat + new_qn.toNat := by c0_bound
    have hqi32 : BitVec.ofNat 32 qi.toNat = qi := BitVec.eq_of_toNat_eq (by simp)
    have hbl_eq : ((s.core.wstk[qp.toNat]'hqp_ws &&& 0x7FFFFFFF#32)).toNat = best_lit.toNat := by
      exact congrArg BitVec.toNat (by assumption)
    have hent_q_bl : (cnfOfClauses F_cur).EntailsClause (cnfClause [q, best_lit.toNat]) := by
      rw [← hbl_eq]; exact hnw.2.1
    have hent_bl_q : (cnfOfClauses F_cur).EntailsClause (cnfClause [best_lit.toNat, q]) :=
      bva_bin_swap_entails hent_q_bl
    have hok_new : FidBvaRowEntryOk F_cur s best_lit.toNat qw [q] := by
      unfold FidBvaRowEntryOk; rw [ite_eq_left hbin]; exact ⟨hq_lt, rfl, hent_bl_q⟩
    have hres_eq : res = [q] := hbin_info.2.1
    have hout' : FidFilterOutInv c F_cur s step row_off.toNat nrow_off.toNat par_off.toNat
        cur_qn.toNat best_lit.toNat (new_qn + 1#32).toNat
        ((sb.set (nrow_off.toNat + new_qn.toNat) qw).set
          (par_off.toNat + new_qn.toNat) qi) := by
      rw [hnew1, ← hqi32]
      exact fidFilterOutInv_push hout hno_le hpo_fit hnew_lt hqi_lt qi.isLt hres_lt hres_nd
        (by rw [← hqw_eq]; exact hok_old) (by rw [hres_eq]; exact hok_new)
        (fun t ht => hent_prev t (by omega)) (by rw [hres_eq]; exact hent_bl_q)
    have har' : FidFilterArInv c s nrow_off.toNat 0 (new_qn + 1#32).toNat
        ((sb.set (nrow_off.toNat + new_qn.toNat) qw).set
          (par_off.toNat + new_qn.toNat) qi) ar := by
      rw [hnew1]
      exact fidFilterArInv_push_bin har_inv (by omega) (by omega) hbin
    c0_hfast
    simp only [fid_bv64_32, hno_eq, hpo_eq] at hm
    exact hBin (new_qn + 1#32) qp _ _ hout' har' hm
  · have hnw := bva_slice_bin_info hsl hrem_pos hqp_ws (by assumption)
    have hqp1 : (qp + 1#64).toNat = qp.toNat + 1 := by c0_bound
    c0_hfast
    exact hJnext (new_qn, qp + 1#64) mp ⟨rfl, by rw [hqp1]; omega, by rw [hqp1]; omega,
      by rw [hqp1]; omega,
      by rw [hqp1, show fullWatchOffCore s.core q + fullWatchSizeCore s.core q -
           (qp.toNat + 1) = fullWatchOffCore s.core q + fullWatchSizeCore s.core q -
           qp.toNat - 1 from by omega]; exact hnw.2.2,
      hmp⟩
  · have hocc := bva_slice_occ_info hsl hrem_pos hqp_ws (by assumption)
    have hqp2 : (qp + 2#64).toNat = qp.toNat + 2 := by c0_bound
    c0_hfast
    exact hJnext (new_qn, qp + 2#64) mp ⟨rfl, by rw [hqp2]; omega, by rw [hqp2]; omega,
      by rw [hqp2]; omega,
      by rw [hqp2, show fullWatchOffCore s.core q + fullWatchSizeCore s.core q -
           (qp.toNat + 2) = fullWatchOffCore s.core q + fullWatchSizeCore s.core q -
           qp.toNat - 2 from by omega]; exact hocc.2,
      hmp⟩

theorem flt_clr_lm_wp {Γ : Env} {Q : Post [i32]} {X : XPost}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {R : Mem 64 → Prop} {row_off nrow_off par_off cur_qn best_lit new_qn qi : Val i32}
    {ticks r_cl : Val i64} {J_out : Cont [i32, i32, i64]} {J_cond : Cont []}
    {qw : Val i32} {J_step : Cont [i32, i64]}
    {csz min_l min_d fc k nq_c : Val i32} {tk_c : Val i64}
    {J_post : Cont [i32, i32, i32, i32]} {J_clr : Cont [i32, i64]}
    {ar sb : List (BitVec 32)} {lm0 lm : List (BitVec 8)} {ant : BitVec 64} {mj : Mem 64}
    (hslen : s.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core)
    (har_l : ar.length = c.arena_cap)
    (hlm0_l : lm0.length = 2 * c.max_vars)
    (hlm0_b1 : ∀ l < 2 * c.max_vars, (lm0[l]?.getD 0#8 &&& 2#8) = 0#8)
    (hqw_ref : qw.toNat ∈ fullArenaClauseRefsCore s.core)
    (hqw_garb : fullArenaClauseGarbCore s.core qw.toNat = false)
    (hcsz_eq : csz.toNat = fullArenaClauseSizeCore s.core qw.toNat)
    (har_eq : ar[qw.toNat + 2]? = s.core.arena[qw.toNat + 2]? ∧
      ∀ j < csz.toNat, ar[qw.toNat + 3 + j]? = s.core.arena[qw.toNat + 3 + j]?)
    (hlm2 : LmBit2Inv c ar lm0 qw.toNat 0 csz.toNat lm)
    (hmj : (FullMem c (fltMkSt s ant ar lm sb) ⋆ R) mj)
    (hExit : ∀ mp, (FullMem c (fltMkSt s ant ar lm0 sb) ⋆ R) mp → J_step (nq_c, tk_c, ()) mp) :
    wp Γ Q X (fltLargeHdrExpr row_off nrow_off par_off cur_qn best_lit c.hdr c.pWvec c.pWstk
      c.pArena c.pLitMark c.pScratchBuf c.pRepr r_cl J_out new_qn qi ticks J_cond qw J_step csz
      |> fltGrpB4 (min_l, min_d, fc, k, ()) J_post
      |> fltGrpB2 (nq_c, tk_c, ()) J_clr) mj := by
  have hmx := c.hmaxv; have har_b := c.harena; unfold dimacsBound at *
  have hcl := hslen.core_ok; have hcv_le := hcl.cur_vars_le; have hlm_len := hcl.lit_mark_len
  have hwf := hw.arena.refs_wf qw.toNat hqw_ref
  have hcsz_bd : qw.toNat + 3 + csz.toNat ≤ c.arena_cap := by
    have := hcl.arena_len_le; omega
  dsimp only [fltLargeHdrExpr, fltStepExpr, fltOuterContExpr, fltHdrExpr, fltSteps, fltStep,
    fltStepsZ, fltStepZ, fltLd64, fltLd32, fltCall64, fltThen, fltElse, fltGrpK0, fltGrpK2,
    fltGrpB2, fltGrpB3, fltGrpB4, fltDummyVal, fltDummyTup, full_bva_filter_row_body]
  refine wp_while_state1 (t := i32) (α := BitVec 32 × List (BitVec 8)) (fun p => p.1)
    (fun (j, _) => csz.toNat - j.toNat)
    (fun (j, lmj) mp => j.toNat ≤ csz.toNat ∧ LmBit2Inv c ar lm0 qw.toNat j.toNat csz.toNat lmj ∧
      (FullMem c (fltMkSt s ant ar lmj sb) ⋆ R) mp)
    (fun Jj hJj => by c0_hfast; exact hJj (0#32, lm) mj ⟨Nat.zero_le _, hlm2, hmj⟩)
    (fun Jj (j, lmj) mp ⟨hj_le, hlmj, hmp⟩ ihj => ?_)
  clear hmj
  dsimp only [fltMkSt] at hmp
  have hlmj_l := hlmj.1
  c0_hfast_nogrp
  rotate_left 1
  · have hdone : j.toNat = csz.toNat := by
      have : ¬ (j.toNat < csz.toNat) := by assumption
      omega
    rw [hdone] at hlmj
    rw [lmBit2Inv_done hlm0_l hlmj] at hmp
    c0_hfast; exact hExit mp hmp
  have hj_lt : j.toNat < csz.toNat := by assumption
  have hj_idx : (BitVec.setWidth 64 qw + (3 : BitVec 64) + BitVec.setWidth 64 j).toNat =
      qw.toNat + 3 + j.toNat := by c0_bound
  have hj_ar : (BitVec.setWidth 64 qw + (3 : BitVec 64) + BitVec.setWidth 64 j).toNat <
      ar.length := by
    rw [hj_idx, har_l]; omega
  have hl_s : (ar[qw.toNat + 3 + j.toNat]'(by rw [har_l]; omega)).toNat =
      (s.core.arena[qw.toNat + 3 + j.toNat]'(by rw [hcl.arena_len_arr]; omega)).toNat := by
    have he := har_eq.2 j.toNat hj_lt
    rw [List.getElem?_eq_getElem (by rw [har_l]; omega),
      List.getElem?_eq_getElem (by rw [hcl.arena_len_arr]; omega)] at he
    exact congrArg BitVec.toNat (Option.some.inj he)
  have hl_lt_cv : (s.core.arena[qw.toNat + 3 + j.toNat]'(by
      rw [hcl.arena_len_arr]; omega)).toNat < 2 * s.core.cur_vars := by
    refine hw.arena.lits_lt qw.toNat hqw_ref hqw_garb _ ?_
    rw [mem_fullArenaClauseLitsCore_iff]
    · exact ⟨j.toNat, by omega, by
        first | rfl | (rw [List.getElem?_eq_getElem (by rw [hcl.arena_len_arr]; omega),
          Option.getD_some])⟩
    · rw [hcl.arena_len_arr]; have := hcl.arena_len_le; omega
  have hl_lt : (ar[qw.toNat + 3 + j.toNat]'(by rw [har_l]; omega)).toNat < 2 * c.max_vars := by
    rw [hl_s]; omega
  have hl_lm : (BitVec.setWidth 64 (ar[(BitVec.setWidth 64 qw + (3 : BitVec 64) +
      BitVec.setWidth 64 j).toNat]'hj_ar)).toNat < lmj.length := by
    rw [fid_bv64_32, hlmj_l]; simp only [hj_idx]; exact hl_lt
  have hj1 : (j + 1#32).toNat = j.toNat + 1 := by c0_bound
  c0_hfast
  have hnext := lmBit2Inv_clear_step hlm0_l hlm0_b1 hlmj hj_lt (by rw [har_l]; omega) hl_lt
  have hcj_eq : (ar[(BitVec.setWidth 64 qw + (3 : BitVec 64) +
      BitVec.setWidth 64 j).toNat]'hj_ar).toNat =
      (ar[qw.toNat + 3 + j.toNat]'(by rw [har_l]; omega)).toNat := by
    apply congrArg BitVec.toNat; apply Option.some.inj
    rw [← List.getElem?_eq_getElem hj_ar,
      ← List.getElem?_eq_getElem (by rw [har_l]; omega), hj_idx]
  simp only [fid_bv64_32, bv8_trunc_and_fd] at hm
  refine ihj (j + 1#32, _) m (by dsimp only; rw [hj1]; omega)
    ⟨by rw [hj1]; omega, by rw [hj1]; simpa only [← hcj_eq] using hnext, hm⟩

theorem flt_mark_loop_wp {Γ : Env} {Q : Post [i32]} {X : XPost}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {R : Mem 64 → Prop} {row_off nrow_off par_off cur_qn best_lit new_qn qi : Val i32}
    {ticks r_cl : Val i64} {J_out : Cont [i32, i32, i64]} {J_cond : Cont []}
    {qw : Val i32} {J_step : Cont [i32, i64]} {csz : Val i32}
    {J_post : Cont [i32, i32, i32, i32]}
    {ar sb : List (BitVec 32)} {lm0 : List (BitVec 8)} {ant : BitVec 64} {mk : Mem 64}
    (hslen : s.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core)
    (har_l : ar.length = c.arena_cap)
    (hlm0_l : lm0.length = 2 * c.max_vars)
    (hlm0_b1 : ∀ l < 2 * c.max_vars, (lm0[l]?.getD 0#8 &&& 2#8) = 0#8)
    (hqw_ref : qw.toNat ∈ fullArenaClauseRefsCore s.core)
    (hqw_garb : fullArenaClauseGarbCore s.core qw.toNat = false)
    (hcsz_eq : csz.toNat = fullArenaClauseSizeCore s.core qw.toNat)
    (har_eq : ar[qw.toNat + 2]? = s.core.arena[qw.toNat + 2]? ∧
      ∀ j < csz.toNat, ar[qw.toNat + 3 + j]? = s.core.arena[qw.toNat + 3 + j]?)
    (hmk : (FullMem c (fltMkSt s ant ar lm0 sb) ⋆ R) mk)
    (hPost : ∀ (min_l min_d fc k : BitVec 32) (lm' : List (BitVec 8)) (mp : Mem 64),
      k.toNat ≤ csz.toNat →
      LmBit2Inv c ar lm0 qw.toNat 0 k.toNat lm' →
      (∀ l < 2 * c.max_vars, (lm'[l]?.getD 0#8 &&& 2#8) ≠ 0#8 →
        (lm0[l]?.getD 0#8 &&& 1#8) = 0#8) →
      (min_l ≠ 0xFFFFFFFF#32 → min_l.toNat < 2 * s.core.cur_vars) →
      (FullMem c (fltMkSt s ant ar lm' sb) ⋆ R) mp →
      J_post (min_l, min_d, fc, k, ()) mp) :
    wp Γ Q X (fltLargeHdrExpr row_off nrow_off par_off cur_qn best_lit c.hdr c.pWvec c.pWstk
      c.pArena c.pLitMark c.pScratchBuf c.pRepr r_cl J_out new_qn qi ticks J_cond qw J_step csz
      |> fltGrpK4 J_post) mk := by
  have hmx := c.hmaxv; have har_b := c.harena; unfold dimacsBound at *
  have hcl := hslen.core_ok; have hcv_le := hcl.cur_vars_le; have hrepr_l := hcl.repr_len
  have hwf := hw.arena.refs_wf qw.toNat hqw_ref
  have hcsz_bd : qw.toNat + 3 + csz.toNat ≤ c.arena_cap := by
    have := hcl.arena_len_le; omega
  dsimp only [fltLargeHdrExpr, fltStepExpr, fltOuterContExpr, fltHdrExpr, fltSteps, fltStep,
    fltStepsZ, fltStepZ, fltLd64, fltLd32, fltCall64, fltThen, fltElse, fltGrpK0, fltGrpK2,
    fltGrpK4, fltGrpB3, fltDummyVal, fltDummyTup, full_bva_filter_row_body]
  refine wp_while_state (α := BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 × List (BitVec 8))
    (fun p => (p.1, p.2.1, p.2.2.1, p.2.2.2.1, ()))
    (fun p => csz.toNat - p.2.2.2.1.toNat)
    (fun (min_l, min_d, fc, k, lmk) mp =>
      k.toNat ≤ csz.toNat ∧ fc.toNat ≤ 1 ∧ LmBit2Inv c ar lm0 qw.toNat 0 k.toNat lmk ∧
      (∀ l < 2 * c.max_vars, (lmk[l]?.getD 0#8 &&& 2#8) ≠ 0#8 →
        (lm0[l]?.getD 0#8 &&& 1#8) = 0#8) ∧
      (min_l ≠ 0xFFFFFFFF#32 → min_l.toNat < 2 * s.core.cur_vars) ∧
      (FullMem c (fltMkSt s ant ar lmk sb) ⋆ R) mp)
    (fun Jm hJm => by
      c0_hfast
      exact hJm (0xFFFFFFFF#32, 0xFFFFFFFF#32, 0#32, 0#32, lm0) mk
        ⟨Nat.zero_le _, Nat.zero_le _, lmBit2Inv_init hlm0_l,
         fun l hl h2 => absurd (hlm0_b1 l hl) h2, fun h => absurd rfl h, hmk⟩)
    (fun Jm (min_l, min_d, fc, k, lmk) mp
        ⟨hk_le, hfc_le, hlmk, hb1_zero, hmin_lt, hmp⟩ ihm => ?_)
  clear hmk
  dsimp only [fltMkSt] at hmp
  have hlmk_l := hlmk.1
  c0_hfast_nogrp
  rotate_left 1
  · c0_hfast; exact hPost min_l min_d fc k lmk mp hk_le hlmk hb1_zero hmin_lt hmp
  have hk_lt : k.toNat < csz.toNat := by assumption
  have hk_idx : (BitVec.setWidth 64 qw + (3 : BitVec 64) + BitVec.setWidth 64 k).toNat =
      qw.toNat + 3 + k.toNat := by c0_bound
  have hk_ar : (BitVec.setWidth 64 qw + (3 : BitVec 64) + BitVec.setWidth 64 k).toNat <
      ar.length := by
    rw [hk_idx, har_l]; omega
  let l := ar[qw.toNat + 3 + k.toNat]'(by rw [har_l]; omega)
  have hl_s : l.toNat =
      (s.core.arena[qw.toNat + 3 + k.toNat]'(by rw [hcl.arena_len_arr]; omega)).toNat := by
    have he := har_eq.2 k.toNat hk_lt
    rw [List.getElem?_eq_getElem (by rw [har_l]; omega),
      List.getElem?_eq_getElem (by rw [hcl.arena_len_arr]; omega)] at he
    exact congrArg BitVec.toNat (Option.some.inj he)
  have hl_lt_cv : l.toNat < 2 * s.core.cur_vars := by
    rw [hl_s]; refine hw.arena.lits_lt qw.toNat hqw_ref hqw_garb _ ?_
    rw [mem_fullArenaClauseLitsCore_iff]
    · exact ⟨k.toNat, by omega, by
        first | rfl | (rw [List.getElem?_eq_getElem (by rw [hcl.arena_len_arr]; omega),
          Option.getD_some])⟩
    · rw [hcl.arena_len_arr]; have := hcl.arena_len_le; omega
  have hl_lt : l.toNat < 2 * c.max_vars := by omega
  have hl_lm : (BitVec.setWidth 64 (ar[(BitVec.setWidth 64 qw + (3 : BitVec 64) +
      BitVec.setWidth 64 k).toNat]'hk_ar)).toNat < lmk.length := by
    rw [fid_bv64_32, hlmk_l]; simp only [hk_idx]; exact hl_lt
  have hk1 : (k + 1#32).toNat = k.toNat + 1 := by c0_bound
  c0_hfast_nogrp
  refine wp_join_state (α := BitVec 32 × BitVec 32 × BitVec 32 × List (BitVec 8))
    (fun x => (x.1, x.2.1, x.2.2.1, ()))
    (fun (ml', md', fc', lm') mp' =>
      fc'.toNat ≤ 1 ∧ LmBit2Inv c ar lm0 qw.toNat 0 (k.toNat + 1) lm' ∧
      (∀ x < 2 * c.max_vars, (lm'[x]?.getD 0#8 &&& 2#8) ≠ 0#8 →
        (lm0[x]?.getD 0#8 &&& 1#8) = 0#8) ∧
      (ml' ≠ 0xFFFFFFFF#32 → ml'.toNat < 2 * s.core.cur_vars) ∧
      (FullMem c (fltMkSt s ant ar lm' sb) ⋆ R) mp')
    (fun _ (ml', md', fc', lm') mp' ⟨hfc', hlm', hb1', hml', hmp'⟩ => by
      c0_hfast
      exact ihm (ml', md', fc', k + 1#32, lm') mp' (by dsimp only; rw [hk1]; omega)
        ⟨by rw [hk1]; omega, hfc', by rw [hk1]; exact hlm', hb1', hml', hmp'⟩)
    (fun Jinc hJinc => ?_)
  c0_hfast_nogrp
  · c0_hfast
    exact hPost min_l min_d (fc + 1#32) k lmk mp hk_le hlmk hb1_zero hmin_lt hmp
  · have hfc1 : (fc + 1#32).toNat = fc.toNat + 1 := by c0_bound
    c0_hfast
    exact hJinc (min_l, min_d, fc + 1#32, lmk) mp
      ⟨by rw [hfc1]; omega, lmBit2Inv_skip hlmk, hb1_zero, hmin_lt, hmp⟩
  · have hk_mod : (qw.toNat + 3 + k.toNat) % 2 ^ 64 = qw.toNat + 3 + k.toNat :=
      Nat.mod_eq_of_lt (by omega)
    have hk_ar_m : (qw.toNat + 3 + k.toNat) % 2 ^ 64 < ar.length := by
      rw [har_l, hk_mod]; omega
    have hk_lm_m : (ar[(qw.toNat + 3 + k.toNat) % 2 ^ 64]'hk_ar_m).toNat < lmk.length := by
      simp only [hlmk_l, hk_mod]; exact hl_lt
    have hk_raw : BitVec.setWidth 32
        (lmk[(ar[(qw.toNat + 3 + k.toNat) % 2 ^ 64]'hk_ar_m).toNat]'hk_lm_m) &&&
        BitVec.ofNat 32 1 = BitVec.ofNat 32 0 := by assumption
    have hl_b0_u32 : (BitVec.setWidth 32 (lmk[l.toNat]'(by omega)) &&& BitVec.ofNat 32 1) =
        BitVec.ofNat 32 0 := by
      simpa only [hk_mod] using hk_raw
    have hl_b0_cur : (lmk[l.toNat]'(by omega) &&& 1#8) = 0#8 :=
      flt_bv8_bit0_zero_of_u32 hl_b0_u32
    have hl_b0_lm0 : (lm0[l.toNat]?.getD 0#8 &&& 1#8) = 0#8 := by
      have hp0 := lmBit2Inv_preserves_bit0 hlmk hl_lt
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some, hl_b0_cur] at hp0
      exact hp0.symm
    have hl_repr : (BitVec.setWidth 64 (ar[(BitVec.setWidth 64 qw + (3 : BitVec 64) +
        BitVec.setWidth 64 k).toNat]'hk_ar)).toNat < s.core.repr.length := by
      rw [fid_bv64_32, hrepr_l]; simp only [hk_idx]; change l.toNat < _; omega
    c0_hfast_nogrp
    let lmw := lmk.set l.toNat ((lmk[l.toNat]'(by omega)) ||| 2#8)
    have hlmw_inv : LmBit2Inv c ar lm0 qw.toNat 0 (k.toNat + 1) lmw := by
      simpa only [hk_idx] using lmBit2Inv_or2 hlm0_l hlmk (by rw [har_l]; omega) hl_lt
    have hb1_w : ∀ x < 2 * c.max_vars, (lmw[x]?.getD 0#8 &&& 2#8) ≠ 0#8 →
        (lm0[x]?.getD 0#8 &&& 1#8) = 0#8 := by
      intro x hx hx2
      by_cases hxl : x = l.toNat
      · subst hxl; exact hl_b0_lm0
      · rw [List.getElem?_set_ne (Ne.symm hxl)] at hx2; exact hb1_zero x hx hx2
    refine wp_join_state (α := BitVec 32 × BitVec 32) (fun x => (x.1, x.2, ()))
      (fun (ml', md') mp' => (ml' ≠ 0xFFFFFFFF#32 → ml'.toNat < 2 * s.core.cur_vars) ∧
        mp' = m)
      (fun _ (ml', md') mp' ⟨hml', hmp'⟩ => by
        rw [hmp']; c0_hfast
        refine hJinc (ml', md', fc, lmw) m ⟨hfc_le, hlmw_inv, hb1_w, hml', ?_⟩
        simpa only [fltMkSt, lmw, l, fid_bv64_32, hk_idx, bv8_trunc_or_2] using hm)
      (fun Jupd hJupd => ?_)
    c0_hfast
    · refine hJupd (_, _) m ⟨fun _ => ?_, rfl⟩
      simp only [hk_idx]; exact hl_lt_cv
    · refine hJupd (_, _) m ⟨fun _ => ?_, rfl⟩
      simp only [hk_idx]; exact hl_lt_cv
    · exact hJupd (min_l, min_d) m ⟨hmin_lt, rfl⟩

theorem flt_match_loop_wp {Γ : Env} {Q : Post [i32]} {X : XPost}
    (hClines : ∀ a m Q X, fidBvaClinesSpec a m Q X → Γ "full_bva_clines_fid" [i64] [i64] a m Q X)
    (hMatch : ∀ a m Q X, fidBvaMatchLargeBvaSpec a m Q X →
      Γ "full_bva_match_large_bva_fid" [i64, i32, i32, i32] [.bool] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {R : Mem 64 → Prop} {row_off nrow_off par_off cur_qn best_lit new_qn qi : Val i32}
    {ticks r_cl : Val i64} {J_out : Cont [i32, i32, i64]} {J_cond : Cont []}
    {qw : Val i32} {J_step : Cont [i32, i64]}
    {csz min_l min_d fc k : Val i32} {J_post : Cont [i32, i32, i32, i32]}
    {J_clr : Cont [i32, i64]} {step bump : Nat}
    {ar sb : List (BitVec 32)} {lm0 lm : List (BitVec 8)} {ant : BitVec 64} {mm : Mem 64}
    (hslen : s.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core)
    (hnodup : FullArenaVarsNodup s) (hdw : DenseWatchesInv F_cur s.core)
    (hl0 : s.core.cur_level = 0) (hdm0 : s.core.dense_mode ≠ 0#64)
    (hstep : 1 ≤ step) (hro_n : row_off.toNat = (s.scratch.scratch_buf[fidStepsCap c.scratch_cap +
      (step - 1)]?.getD 0#32).toNat)
    (hcqn_n : cur_qn.toNat = (s.scratch.scratch_buf[2 * fidStepsCap c.scratch_cap +
      (step - 1)]?.getD 0#32).toNat)
    (hnro_n : nrow_off.toNat = bump) (hno_le : nrow_off.toNat ≤ par_off.toNat)
    (hpo_fit : par_off.toNat + (par_off.toNat - nrow_off.toNat) ≤ c.scratch_cap)
    (hnew_lt : new_qn.toNat < par_off.toNat - nrow_off.toNat)
    (hqi_lt : qi.toNat < cur_qn.toNat)
    (hmat : FidBvaMatrixInv c F_cur s step bump)
    (hout : FidFilterOutInv c F_cur s step row_off.toNat nrow_off.toNat par_off.toNat
      cur_qn.toNat best_lit.toNat new_qn.toNat sb)
    (har_inv : FidFilterArInv c s nrow_off.toNat 0 new_qn.toNat sb ar)
    (hlm0_l : lm0.length = 2 * c.max_vars)
    (hlm0_b1 : ∀ l < 2 * c.max_vars, (lm0[l]?.getD 0#8 &&& 2#8) = 0#8)
    (hlm_b0 : ∀ r < step, (lm0[(s.scratch.scratch_buf[r]?.getD 0#32).toNat]?.getD 0#8 &&&
      1#8) ≠ 0#8)
    (hbvaq : (qw &&& 0x80000000#32) = 0#32)
    (hqw_eq : qw = s.scratch.scratch_buf[row_off.toNat + qi.toNat]?.getD 0#32)
    (hcsz_eq : csz.toNat = fullArenaClauseSizeCore s.core qw.toNat)
    (hk_le : k.toNat ≤ csz.toNat)
    (hfc_eq : fc = 1#32) (hml_ne : min_l ≠ 0xFFFFFFFF#32)
    (hml_lt : min_l.toNat < 2 * s.core.cur_vars)
    (hlm2 : LmBit2Inv c ar lm0 qw.toNat 0 k.toNat lm)
    (hb1_zero : ∀ l < 2 * c.max_vars, (lm[l]?.getD 0#8 &&& 2#8) ≠ 0#8 →
      (lm0[l]?.getD 0#8 &&& 1#8) = 0#8)
    (hw_ar : FullWitnessInv c F0 F_cur { s.core with arena := ar })
    (hrefs_ar :
      fullArenaClauseRefsCore { s.core with arena := ar } = fullArenaClauseRefsCore s.core ∧
      ∀ r ∈ fullArenaClauseRefsCore s.core,
        fullArenaClauseGarbCore { s.core with arena := ar } r = fullArenaClauseGarbCore s.core r ∧
        fullArenaClauseSizeCore { s.core with arena := ar } r = fullArenaClauseSizeCore s.core r ∧
        fullArenaClauseLitsCore { s.core with arena := ar } r =
          fullArenaClauseLitsCore s.core r)
    (har_qw : ar[qw.toNat + 2]? = s.core.arena[qw.toNat + 2]? ∧
      ∀ j < csz.toNat, ar[qw.toNat + 3 + j]? = s.core.arena[qw.toNat + 3 + j]?)
    (hmm : (FullMem c (fltMkSt s ant ar lm sb) ⋆ R) mm)
    (hExit : ∀ (nq' : BitVec 32) (tk' : BitVec 64) (ar' sb' : List (BitVec 32)) (mp : Mem 64),
      FidFilterOutInv c F_cur s step row_off.toNat nrow_off.toNat par_off.toNat
        cur_qn.toNat best_lit.toNat nq'.toNat sb' →
      FidFilterArInv c s nrow_off.toNat 0 nq'.toNat sb' ar' →
      FullWitnessInv c F0 F_cur { s.core with arena := ar' } →
      (fullArenaClauseRefsCore { s.core with arena := ar' } = fullArenaClauseRefsCore s.core ∧
        ∀ r ∈ fullArenaClauseRefsCore s.core,
          fullArenaClauseGarbCore { s.core with arena := ar' } r =
            fullArenaClauseGarbCore s.core r ∧
          fullArenaClauseSizeCore { s.core with arena := ar' } r =
            fullArenaClauseSizeCore s.core r ∧
          fullArenaClauseLitsCore { s.core with arena := ar' } r =
            fullArenaClauseLitsCore s.core r) →
      (FullMem c (fltMkSt s ant ar' lm sb') ⋆ R) mp →
      J_clr (nq', tk', ()) mp) :
    wp Γ Q X (fltLargeHdrExpr row_off nrow_off par_off cur_qn best_lit c.hdr c.pWvec c.pWstk
      c.pArena c.pLitMark c.pScratchBuf c.pRepr r_cl J_out new_qn qi ticks J_cond qw J_step csz
      |> fltGrpB4 (min_l, min_d, fc, k, ()) J_post
      |> fltGrpK2 J_clr) mm := by
  have hmx := c.hmaxv; have har_b := c.harena; have hwcap := c.hwcap; have hscr := c.hscr
  unfold dimacsBound at *
  have hcl := hslen.core_ok; have hcv_le := hcl.cur_vars_le; have hwv_len := hcl.wvec_len
  have hws_len := hcl.wstk_len_arr; have hwlen_le := hcl.wlen_le
  have har_l := har_inv.1; have hsb_l := hout.1; have hlm_l := hlm2.1
  have hfr_res := hmat.2.2.2.2.2 (step - 1) (by omega)
  have ⟨res, hres_lt, hres_nd, hok_old, hent_prev, _⟩ := hfr_res.2.2.2.2.2 qi.toNat (by omega)
  rw [← hro_n, ← hqw_eq] at hok_old
  have hlar_info : qw.toNat ∈ fullArenaClauseRefs s ∧ fullArenaClauseGarb s qw.toNat = false ∧
      3 ≤ fullArenaClauseSize s qw.toNat ∧ fullArenaClauseSize s qw.toNat ≤ 5 ∧
      (s.scratch.scratch_buf[step - 1]?.getD 0#32).toNat ∈ fullArenaClauseLits s qw.toNat ∧
      res.Perm ((fullArenaClauseLits s qw.toNat).filter
        (· != (s.scratch.scratch_buf[step - 1]?.getD 0#32).toNat)) ∧
      (fullArenaClauseLits s qw.toNat).Perm
        ((s.scratch.scratch_buf[step - 1]?.getD 0#32).toNat :: res) := by
    unfold FidBvaRowEntryOk at hok_old; rw [ite_eq_right (by simp [hbvaq])] at hok_old
    exact hok_old
  have hqw_ref := hlar_info.1
  have hqw_garb := hlar_info.2.1
  have hq_bd := hdw.layout.bounds min_l.toNat hml_lt
  have hq_sl := hdw.slices min_l.toNat hml_lt
  let qoff := BitVec.setWidth 64 (s.core.wvec[2 * min_l.toNat]'(by omega))
  let qsz := BitVec.setWidth 64 (s.core.wvec[2 * min_l.toNat + 1]'(by omega))
  have hqoff_nat : qoff.toNat = fullWatchOffCore s.core min_l.toNat := by
    dsimp only [qoff]; rw [fid_bv64_32]
    unfold fullWatchOffCore; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
  have hqsz_nat : qsz.toNat = fullWatchSizeCore s.core min_l.toNat := by
    dsimp only [qsz]; rw [fid_bv64_32]
    unfold fullWatchSizeCore; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
  have hqend_nat : (qoff + qsz).toNat = qoff.toNat + qsz.toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by rw [hqoff_nat, hqsz_nat]; omega)]
  have hmin_shl1 : (BitVec.setWidth 64 min_l <<< (1 : Nat)).toNat = 2 * min_l.toNat := by c0_bound
  have hmin_shl1_bv : (BitVec.setWidth 64 min_l <<< BitVec.signExtend 64 (1 : BitVec 32)).toNat =
      2 * min_l.toNat := by
    rw [show BitVec.signExtend 64 (1 : BitVec 32) = (1 : BitVec 64) from rfl]; c0_bound
  have h2ml_wv : (BitVec.setWidth 64 min_l <<< (1 : BitVec 64)).toNat < s.core.wvec.length := by
    change (BitVec.setWidth 64 min_l <<< BitVec.signExtend 64 (1 : BitVec 32)).toNat < _
    rw [hmin_shl1_bv, hwv_len]; omega
  have h2ml1_wv : ((BitVec.setWidth 64 min_l <<< (1 : BitVec 64)) + 1#64).toNat <
      s.core.wvec.length := by
    rw [BitVec.toNat_add, show BitVec.toNat (1#64 : BitVec 64) = 1 from rfl,
      show (BitVec.setWidth 64 min_l <<< (1 : BitVec 64)).toNat = 2 * min_l.toNat from by
        change (BitVec.setWidth 64 min_l <<< BitVec.signExtend 64 (1 : BitVec 32)).toNat = _
        exact hmin_shl1_bv,
      Nat.mod_eq_of_lt (by omega), hwv_len]; omega
  dsimp only [fltLargeHdrExpr, fltStepExpr, fltOuterContExpr, fltHdrExpr, fltSteps, fltStep,
    fltStepsZ, fltStepZ, fltLd64, fltLd32, fltCall64, fltThen, fltElse, fltGrpK0, fltGrpK2,
    fltGrpB3, fltGrpB4, fltDummyVal, fltDummyTup, full_bva_filter_row_body]
  subst hfc_eq
  c0_hfast_nogrp
  · fid_call hClines; intro r_cl2
    c0_hfast_nogrp
    refine wp_join_state (α := BitVec 32 × BitVec 64 × BitVec 64 × List (BitVec 32) ×
        List (BitVec 32)) (fun x => (x.1, x.2.1, x.2.2.1, ()))
      (fun (nq', tk', _, ar', sb') mp =>
        FidFilterOutInv c F_cur s step row_off.toNat nrow_off.toNat par_off.toNat
          cur_qn.toNat best_lit.toNat nq'.toNat sb' ∧
        FidFilterArInv c s nrow_off.toNat 0 nq'.toNat sb' ar' ∧
        FullWitnessInv c F0 F_cur { s.core with arena := ar' } ∧
        (fullArenaClauseRefsCore { s.core with arena := ar' } = fullArenaClauseRefsCore s.core ∧
          ∀ r ∈ fullArenaClauseRefsCore s.core,
            fullArenaClauseGarbCore { s.core with arena := ar' } r =
              fullArenaClauseGarbCore s.core r ∧
            fullArenaClauseSizeCore { s.core with arena := ar' } r =
              fullArenaClauseSizeCore s.core r ∧
            fullArenaClauseLitsCore { s.core with arena := ar' } r =
              fullArenaClauseLitsCore s.core r) ∧
        (FullMem c (fltMkSt s ant ar' lm sb') ⋆ R) mp)
      (fun _ (nq', tk', _, ar', sb') mp ⟨ho', ha', hwa', hra', hm'⟩ => by
        c0_hfast; exact hExit nq' tk' ar' sb' mp ho' ha' hwa' hra' hm')
      (fun Jmexit hJmexit => ?_)
    refine wp_while_state (α := BitVec 64 × BitVec 64) (fun x => (x.1, x.2, ()))
      (fun x => qoff.toNat + qsz.toNat - x.2.toNat)
      (fun (tk_m, qp) mp => qoff.toNat ≤ qp.toNat ∧ qp.toNat ≤ qoff.toNat + qsz.toNat ∧
        DenseWatchSliceOk F_cur s.core min_l.toNat qp.toNat (qoff.toNat + qsz.toNat - qp.toNat) ∧
        (FullMem c (fltMkSt s ant ar lm sb) ⋆ R) mp)
      (fun Jp hJp => by
        c0_hfast
        have hqoff_bv : BitVec.setWidth 64 (s.core.wvec[(BitVec.setWidth 64 min_l <<<
            (1 : Nat)).toNat]'(by simp only [hmin_shl1]; omega)) = qoff := by
          apply BitVec.eq_of_toNat_eq; dsimp only [qoff]; rw [fid_bv64_32, fid_bv64_32]
          simp only [hmin_shl1]
        refine Eq.mpr (congrArg (fun v => Jp (_, v, ()) mm) hqoff_bv) ?_
        refine hJp (_, qoff) mm ⟨Nat.le_refl _, Nat.le_add_right _ _, ?_, hmm⟩
        simpa only [Nat.add_sub_cancel_left, hqoff_nat, hqsz_nat] using hq_sl)
      (fun Jp (tk_m, qp) mp ⟨hqp_ge, hqp_le, hsl, hmp⟩ ihp => ?_)
    clear hmm
    dsimp only [fltMkSt] at hmp
    c0_hfast_nogrp
    rotate_left 1
    · c0_hfast
      exact hJmexit (new_qn, tk_m, qp, ar, sb) mp ⟨hout, har_inv, hw_ar, hrefs_ar, hmp⟩
    have hq_sum_eq :
        (s.core.wvec[2 * min_l.toNat % 2 ^ 64]'(by
          rw [hwv_len, Nat.mod_eq_of_lt (by omega)]; omega)).toNat +
        (s.core.wvec[(2 * min_l.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
          rw [hwv_len, show BitVec.toNat (1 : BitVec 64) = 1 from rfl,
            Nat.mod_eq_of_lt (by omega)]; omega)).toNat = qoff.toNat + qsz.toNat := by
      simp only [show 2 * min_l.toNat % 2 ^ 64 = 2 * min_l.toNat from Nat.mod_eq_of_lt (by omega),
        show BitVec.toNat (1 : BitVec 64) = 1 from rfl,
        show (2 * min_l.toNat + 1) % 2 ^ 64 = 2 * min_l.toNat + 1 from Nat.mod_eq_of_lt (by omega)]
      dsimp only [qoff, qsz]; rw [fid_bv64_32, fid_bv64_32]
    have hqp_lt : qp.toNat < qoff.toNat + qsz.toNat := by
      have hq_lt64 : qoff.toNat + qsz.toNat < 2 ^ 64 := by rw [hqoff_nat, hqsz_nat]; omega
      have hc' : qp.toNat < ((s.core.wvec[2 * min_l.toNat % 2 ^ 64]'(by
          rw [hwv_len, Nat.mod_eq_of_lt (by omega)]; omega)).toNat +
          (s.core.wvec[(2 * min_l.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
            rw [hwv_len, show BitVec.toNat (1 : BitVec 64) = 1 from rfl,
              Nat.mod_eq_of_lt (by omega)]; omega)).toNat) % 2 ^ 64 := by
        simpa only [hmin_shl1] using by assumption
      rw [hq_sum_eq, Nat.mod_eq_of_lt hq_lt64] at hc'; exact hc'
    have hrem_pos : 0 < qoff.toNat + qsz.toNat - qp.toNat := by
      rw [hqoff_nat, hqsz_nat] at hqp_lt ⊢; omega
    have hqp_ws : qp.toNat < s.core.wstk.length := by
      rw [hws_len]; rw [hqoff_nat, hqsz_nat] at hqp_lt; omega
    have hqp1 : (qp + 1#64).toNat = qp.toNat + 1 := by
      rw [BitVec.toNat_add, show (1#64 : BitVec 64).toNat = 1 from rfl,
        Nat.mod_eq_of_lt (by rw [hqoff_nat, hqsz_nat] at hqp_lt; omega)]
    c0_hfast_nogrp
    · have hbin := bva_slice_bin_info (by simpa only [hqoff_nat, hqsz_nat] using hsl)
        hrem_pos hqp_ws (by assumption)
      c0_hfast
      exact ihp (tk_m, qp + 1#64) mp (by dsimp only; rw [hqp1]; omega)
        ⟨by rw [hqp1]; omega, by rw [hqp1]; omega,
         by rw [hqp1, show qoff.toNat + qsz.toNat - (qp.toNat + 1) =
              qoff.toNat + qsz.toNat - qp.toNat - 1 from by omega]
            simpa only [hqoff_nat, hqsz_nat] using hbin.2.2, hmp⟩
    · c0_hfast
      exact hJmexit (new_qn, tk_m, qp + 1#64, ar, sb) mp ⟨hout, har_inv, hw_ar, hrefs_ar, hmp⟩
    ·
        have hrem_pos_n : 0 < fullWatchOffCore s.core min_l.toNat +
            fullWatchSizeCore s.core min_l.toNat - qp.toNat := by
          simpa only [hqoff_nat, hqsz_nat] using hrem_pos
        have hsl_n : DenseWatchSliceOk F_cur s.core min_l.toNat qp.toNat
            (fullWatchOffCore s.core min_l.toNat + fullWatchSizeCore s.core min_l.toNat -
              qp.toNat) := by simpa only [hqoff_nat, hqsz_nat] using hsl
        have hqp1_ws : qp.toNat + 1 < s.core.wstk.length := by
          have h2 := (bva_slice_occ_info hsl_n hrem_pos_n hqp_ws (by assumption)).1
          rw [hws_len]; rw [hqoff_nat, hqsz_nat] at hqp_lt; omega
        have hqp1_ws' : (qp + 1#64).toNat < s.core.wstk.length := by rwa [hqp1]
        have ⟨h2le, hdr_ref_s, hrem_next⟩ :=
          fwd_slice_occ_info hsl_n hrem_pos_n hqp_ws hqp1_ws (by assumption)
        have hqp2 : (qp + 2#64).toNat = qp.toNat + 2 := by
          rw [BitVec.toNat_add, show (2#64 : BitVec 64).toNat = 2 from rfl,
            Nat.mod_eq_of_lt (by rw [hqoff_nat, hqsz_nat] at hqp_lt; omega)]
        have hqp2_bv : qp + (1 : BitVec 64) + (1 : BitVec 64) = qp + 2#64 := by
          rw [BitVec.add_assoc]; rfl
        c0_hfast_nogrp
        · c0_hfast; rw [hqp2_bv]
          exact ihp (tk_m, qp + 2#64) mp (by dsimp only; rw [hqp2]; omega)
            ⟨by rw [hqp2]; omega, by rw [hqp2]; omega,
             by rw [hqp2, show qoff.toNat + qsz.toNat - (qp.toNat + 2) =
                  qoff.toNat + qsz.toNat - qp.toNat - 2 from by omega]
                simpa only [hqoff_nat, hqsz_nat] using hrem_next, hmp⟩
        · let dr := s.core.wstk[(qp + 1#64).toNat]'hqp1_ws'
          have hdr_s : dr = s.core.wstk[qp.toNat + 1]'hqp1_ws := by
            dsimp only [dr]; simp only [hqp1]
          have hdr_ref_orig : dr.toNat ∈ fullArenaClauseRefsCore s.core := by
            rw [hdr_s]; exact hdr_ref_s
          have hdr_lt_bv31 : dr.toNat < 0x80000000 := by
            rcases denseWatchSliceOk_step hsl_n hrem_pos_n with ⟨_, hw0_s, hne, _⟩ |
                ⟨_, cr, _, _, hw1_s, _, _, hcr_lt, _, _⟩
            · have : s.core.wstk[qp.toNat]'hqp_ws = _ := Option.some.inj
                ((List.getElem?_eq_getElem hqp_ws).symm.trans hw0_s)
              exfalso; apply (by assumption : (s.core.wstk[qp.toNat]'hqp_ws &&& 0x80000000#32) =
                0#32) |> fun h => hne (by simpa [this] using h)
            · have heq : dr = cr := by
                rw [hdr_s, ← Option.some_inj]
                rw [← List.getElem?_eq_getElem hqp1_ws]; exact hw1_s
              rwa [heq]
          have hdr_bin0 : (dr &&& 0x80000000#32) = 0#32 :=
            fid_bv32_bin_flag_zero_of_lt hdr_lt_bv31
          fid_call hMatch
          let sm : FullState := fltMkSt s ant ar lm sb
          have hslen_m : sm.LengthsOk c := fltMkSt_lengthsOk hslen har_l hlm_l hsb_l
          have hw_m : FullWitnessInv c F0 F_cur sm.core := fullWitnessInv_with_litMark hw_ar lm
          have hnodup_m : FullArenaVarsNodup sm := by
            intro r hr hgb
            have hr' : r ∈ fullArenaClauseRefsCore s.core := by rwa [← hrefs_ar.1]
            have hl_eq := hrefs_ar.2 r hr'
            have hgb' : fullArenaClauseGarbCore s.core r = false := by
              rw [← hl_eq.1]; exact hgb
            have hnd := hnodup r hr' hgb'
            unfold fullArenaClauseLits fullArenaClauseLitsCore at hnd ⊢
            change ((fullArenaClauseLitsCore { s.core with arena := ar } r).map (· / 2)).Nodup
            rwa [hl_eq.2.2]
          have hqw_ref_m : qw.toNat ∈ fullArenaClauseRefs sm := by
            change qw.toNat ∈ fullArenaClauseRefsCore { s.core with arena := ar }
            rw [hrefs_ar.1]; exact hqw_ref
          have hqw_garb_m : fullArenaClauseGarb sm qw.toNat = false := by
            change fullArenaClauseGarbCore { s.core with arena := ar } qw.toNat = false
            rw [(hrefs_ar.2 qw.toNat hqw_ref).1]; exact hqw_garb
          have hdr_ref_m : dr.toNat ∈ fullArenaClauseRefs sm := by
            change dr.toNat ∈ fullArenaClauseRefsCore { s.core with arena := ar }
            rw [hrefs_ar.1]; exact hdr_ref_orig
          have hres_nd_list : res.Nodup := nodup_of_map_div2 hres_nd
          have hwf := hw.arena.refs_wf qw.toNat hqw_ref
          have hlen_le := hcl.arena_len_le
          have hqw_len_m : fullArenaClauseSize sm qw.toNat = res.length + 1 := by
            change fullArenaClauseSizeCore { s.core with arena := ar } qw.toNat = res.length + 1
            rw [(hrefs_ar.2 qw.toNat hqw_ref).2.1]
            have hl_len := fullArenaClauseLitsCore_length (k := s.core) (r := qw.toNat)
              (by rw [hcl.arena_len_arr]; omega)
            have hp_len := hlar_info.2.2.2.2.2.2.length_eq
            simp only [List.length_cons] at hp_len
            unfold fullArenaClauseLits at hl_len hp_len; omega
          have hlm_sub_res : ∀ l < 2 * sm.core.cur_vars,
              (sm.core.lit_mark[l]?.getD 0#8 &&& 2#8) ≠ 0#8 → l ∈ res := by
            intro l hl hl_b2
            change (lm[l]?.getD 0#8 &&& 2#8) ≠ 0#8 at hl_b2
            have hl_mx : l < 2 * c.max_vars := by change l < 2 * s.core.cur_vars at hl; omega
            rcases hlm2.2 l hl_mx with heq_lm0 | ⟨j, _, hjk, harj, _⟩
            · rw [heq_lm0] at hl_b2; exact absurd (hlm0_b1 l hl_mx) hl_b2
            · have harj_s : (s.core.arena[qw.toNat + 3 + j]?.getD 0#32).toNat = l := by
                rw [← har_qw.2 j (by omega)]; exact harj
              have hl_in_qw : l ∈ fullArenaClauseLits s qw.toNat := by
                rw [fullArenaClauseLits, mem_fullArenaClauseLitsCore_iff]
                · exact ⟨j, by rw [← hcsz_eq]; omega, by
                    first
                    | exact harj_s
                    | (rw [List.getElem?_eq_getElem (by rw [hcl.arena_len_arr]; omega),
                        Option.getD_some] at harj_s; exact harj_s)⟩
                · rw [hcl.arena_len_arr]; omega
              have hb1_l : (lm0[l]?.getD 0#8 &&& 1#8) = 0#8 := hb1_zero l hl_mx hl_b2
              have hne_fr : l ≠ (s.scratch.scratch_buf[step - 1]?.getD 0#32).toNat := by
                intro heq; rw [heq] at hb1_l; exact hlm_b0 (step - 1) (by omega) hb1_l
              have hl_filt : l ∈ (fullArenaClauseLits s qw.toNat).filter
                  (· != (s.scratch.scratch_buf[step - 1]?.getD 0#32).toNat) :=
                List.mem_filter.mpr ⟨hl_in_qw, by simp [hne_fr]⟩
              exact hlar_info.2.2.2.2.2.1.symm.subset hl_filt
          refine ⟨c, F0, F_cur, sm, R, res, rfl, hslen_m, hw_m, hnodup_m, hl0, hdm0, hqw_ref_m,
            hqw_garb_m, hdr_ref_m, hres_nd_list, hres_lt, hqw_len_m, hlm_sub_res, hmp,
            fun ok hok => ?_⟩
          cases ok
          · simp at hok; c0_hfast; rw [hqp2_bv]
            exact ihp (tk_m + 1#64, qp + 2#64) mp (by dsimp only; rw [hqp2]; omega)
              ⟨by rw [hqp2]; omega, by rw [hqp2]; omega,
               by rw [hqp2, show qoff.toNat + qsz.toNat - (qp.toNat + 2) =
                    qoff.toNat + qsz.toNat - qp.toNat - 2 from by omega]
                  simpa only [hqoff_nat, hqsz_nat] using hrem_next, hmp⟩
          · obtain ⟨hdr_g_m, hdr_nbvaq_m, hdr_sz_m, hbl_mem_m, hdr_perm_m, hdr_filt_m,
                hdr_ent_m⟩ := hok rfl
            have hdr_wf := hw.arena.refs_wf dr.toNat hdr_ref_orig
            have hdr_lt_cap : dr.toNat < c.arena_cap := by have := hcl.arena_len_le; omega
            have hdr_ar_len : (BitVec.setWidth 64 dr).toNat < ar.length := by
              rw [fid_bv64_32, har_l]; exact hdr_lt_cap
            have hno_sb : (BitVec.setWidth 64 (nrow_off + new_qn)).toNat < sb.length := by
              rw [fid_bv64_32, hsb_l]; change (nrow_off + new_qn).toNat < _; c0_bound
            have hpo_sb : (BitVec.setWidth 64 (par_off + new_qn)).toNat < sb.length := by
              rw [fid_bv64_32, hsb_l]; change (par_off + new_qn).toNat < _; c0_bound
            have hdr_nbvaq_ar : (ar[dr.toNat]'(by rw [har_l]; exact hdr_lt_cap) &&&
                0x02000000#32) = 0#32 := by
              unfold fullArenaHdr fullArenaHdrCore at hdr_nbvaq_m
              dsimp only [sm, fltMkSt] at hdr_nbvaq_m
              rwa [List.getElem?_eq_getElem (by rw [har_l]; exact hdr_lt_cap),
                Option.getD_some] at hdr_nbvaq_m
            have hnew1 : (new_qn + 1#32).toNat = new_qn.toNat + 1 := by c0_bound
            have hno_eq : (nrow_off + new_qn).toNat = nrow_off.toNat + new_qn.toNat := by c0_bound
            have hpo_eq : (par_off + new_qn).toNat = par_off.toNat + new_qn.toNat := by c0_bound
            have hqi32 : BitVec.ofNat 32 qi.toNat = qi := by simp
            have hdr_eq_ar := hrefs_ar.2 dr.toNat hdr_ref_orig
            have hdr_g_s : fullArenaClauseGarb s dr.toNat = false := by
              change fullArenaClauseGarbCore s.core dr.toNat = false
              rw [← hdr_eq_ar.1]; exact hdr_g_m
            have hdr_sz_s : fullArenaClauseSize s dr.toNat = fullArenaClauseSize s qw.toNat := by
              have h1 := hdr_eq_ar.2.1; have h2 := (hrefs_ar.2 qw.toNat hqw_ref).2.1
              change fullArenaClauseSizeCore s.core dr.toNat =
                fullArenaClauseSizeCore s.core qw.toNat
              rw [← h1, ← h2]; exact hdr_sz_m
            have hdr_lits_eq : fullArenaClauseLitsCore s.core dr.toNat =
                fullArenaClauseLitsCore { s.core with arena := ar } dr.toNat := hdr_eq_ar.2.2.symm
            have hok_new : FidBvaRowEntryOk F_cur s best_lit.toNat dr res := by
              unfold FidBvaRowEntryOk; rw [ite_eq_right (fun h => h hdr_bin0)]
              refine ⟨hdr_ref_orig, hdr_g_s, by rw [hdr_sz_s]; exact hlar_info.2.2.1,
                by rw [hdr_sz_s]; exact hlar_info.2.2.2.1, ?_, ?_, ?_⟩
              · unfold fullArenaClauseLits; rw [hdr_lits_eq]; exact hbl_mem_m
              · unfold fullArenaClauseLits; rw [hdr_lits_eq]; exact hdr_filt_m.symm
              · unfold fullArenaClauseLits; rw [hdr_lits_eq]; exact hdr_perm_m
            let ar' := ar.set dr.toNat ((ar[dr.toNat]'(by rw [har_l]; exact hdr_lt_cap)) |||
              0x02000000#32)
            let sb' := (sb.set (nrow_off.toNat + new_qn.toNat) dr).set
              (par_off.toNat + new_qn.toNat) qi
            have hout' : FidFilterOutInv c F_cur s step row_off.toNat nrow_off.toNat par_off.toNat
                cur_qn.toNat best_lit.toNat (new_qn + 1#32).toNat sb' := by
              dsimp only [sb']; rw [hnew1, ← hqi32]
              exact fidFilterOutInv_push hout hno_le hpo_fit hnew_lt hqi_lt qi.isLt hres_lt hres_nd
                (by rw [← hqw_eq]; exact hok_old) hok_new (fun t ht => hent_prev t (by omega))
                hdr_ent_m
            have ⟨_, har_inv'⟩ := fidFilterArInv_push_large (par_off := par_off.toNat)
              (par_idx := qi) har_inv (by omega) (by omega) hdr_bin0 hdr_ref_orig hdr_lt_cap
              hdr_nbvaq_ar
            have hrefs_ar' := fltArBvaq_congr hcl hw fun i hi => by
              by_cases hid : i = dr.toNat
              · subst hid; right
                have h_s : (sb'[nrow_off.toNat + new_qn.toNat]?.getD 0#32) = dr := by
                  dsimp only [sb']; rw [List.getElem?_set_ne (by omega),
                    List.getElem?_set_self (by omega), Option.getD_some]
                have har_or := har_inv'.2.2.2.1 new_qn.toNat (by omega) (by omega) (by
                  rw [h_s]; exact hdr_bin0)
                rw [h_s] at har_or
                exact ⟨hdr_ref_orig, har_or.2.2.2⟩
              · rcases har_inv.2.2.2.2.2 i hi with heq | ⟨t, _, _, hwb, hwt, _, hset⟩
                · left; rw [List.getElem?_set_ne (Ne.symm hid)]; exact heq
                · right; have ht_ref := (har_inv.2.2.2.1 t (Nat.zero_le _) (by omega) hwb).1
                  rw [hwt] at ht_ref; rw [List.getElem?_set_ne (Ne.symm hid)]
                  exact ⟨ht_ref, hset⟩
            have hw_ar_cl : ({ s.core with arena := ar }).LengthsOk c :=
              { hcl with arena_len_arr := har_l }
            have hdr_ref_ar : dr.toNat ∈ fullArenaClauseRefsCore { s.core with arena := ar } := by
              rw [hrefs_ar.1]; exact hdr_ref_orig
            have ⟨_, _, hw_ar', _⟩ := fullWitnessInv_set_hdr_bit20 hw_ar_cl hw_ar hl0 hdr_ref_ar
              ((ar[dr.toNat]'(by rw [har_l]; exact hdr_lt_cap)) ||| 0x02000000#32)
              (by unfold fullArenaHdrCore; dsimp only
                  rw [List.getElem?_eq_getElem (by rw [har_l]; exact hdr_lt_cap), Option.getD_some]
                  exact flt_bv32_or_bvaq_garb _)
              (by unfold fullArenaHdrCore; dsimp only
                  rw [List.getElem?_eq_getElem (by rw [har_l]; exact hdr_lt_cap), Option.getD_some]
                  exact flt_bv32_or_bvaq_shrk _)
            c0_hfast
            simp only [fid_bv64_32, hno_eq, hpo_eq, show (33554432 : BitVec 32) =
              0x02000000#32 from rfl] at hm
            rw [hqp2_bv]
            exact hJmexit (new_qn + 1#32, tk_m + 1#64, qp + 2#64, ar', sb') m
              ⟨hout', by rwa [hnew1], hw_ar', hrefs_ar', by
                simpa only [fltMkSt, ar', sb', dr,
                  show qp + (1 : BitVec 64) = qp + 1#64 from rfl] using hm⟩
            exact absurd (by assumption : true = false) (by decide)
  · exfalso; first
      | exact hml_ne (by assumption)
      | exact (by assumption : ¬min_l ≠ 0xFFFFFFFF#32) hml_ne
  · exfalso; exact (by assumption : (1#32 : BitVec 32) ≠ 1#32) rfl

end

end LeanQbe.T.Examples.Kissat.Proof.Factor
