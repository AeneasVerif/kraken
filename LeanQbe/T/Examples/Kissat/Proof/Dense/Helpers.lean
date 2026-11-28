/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Dense.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics1
import LeanQbe.T.Examples.Kissat.Proof.Spec.WitnessInv1
import LeanQbe.T.Logic.C0Agrees

/-!
# Shared Helpers for Kissat `Proof.Dense` (`0` Legacy Imports)

Reusable `BitVec`, CNF/clause unit-resolution, `DenseWatchSliceOk`, `FullWitnessInv`,
`FullDenseInvW`, and arena clause-body preservation lemmas shared across the modular
`Proof.Dense.Wp*` proofs (`0` legacy imports, `0` `@[expose]` on theorems/lemmas/sections).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Dense

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.C0Step
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec

/-! ## 1. `BitVec`, Domain & Indexing Helpers -/

theorem dense_getElem_congr {α : Type} {xs : List α} {i j : Nat} (h : i = j)
    (hi : i < xs.length) (hj : j < xs.length) : xs[i]'hi = xs[j]'hj := by
  subst h; rfl

theorem dense_zext32_toNat (x : BitVec 32) : (BitVec.setWidth 64 x).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans x.isLt (by decide))]

theorem dense_bv32_xor1_toNat (x : BitVec 32) : (x ^^^ 1#32).toNat = x.toNat ^^^ 1 := by
  simp [BitVec.toNat_xor]

theorem dense_bv32_xor1_ofnat (x : BitVec 32) :
    (x ^^^ (1 : BitVec 32)).toNat = x.toNat ^^^ 1 :=
  dense_bv32_xor1_toNat x

theorem dense_bv64_shl1_bv (x : BitVec 64) (h : 2 * x.toNat < 2 ^ 64) :
    (x <<< 1#64).toNat = 2 * x.toNat := by
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm, Nat.mod_eq_of_lt h]

theorem dense_bv64_shl1_nat (x : BitVec 64) (h : 2 * x.toNat < 2 ^ 64) :
    (x <<< (1 : Nat)).toNat = 2 * x.toNat := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm, Nat.mod_eq_of_lt h]

theorem bv32_mask_7fffffff_props {sz : BitVec 32} (hge : 3 ≤ sz.toNat) (hlt : sz.toNat < 2 ^ 31) :
    ((sz &&& 0x7FFFFFFF#32) &&& 0x80000000#32) = 0#32 ∧
    (sz &&& 0x7FFFFFFF#32) ≠ 0xFFFFFFFF#32 ∧
    3 ≤ (sz &&& 0x7FFFFFFF#32).toNat := by
  have hbit : ((sz &&& 0x7FFFFFFF#32) &&& 0x80000000#32) = 0#32 := by
    rw [BitVec.and_assoc, show (0x7FFFFFFF#32 &&& 0x80000000#32) = 0#32 by decide, BitVec.and_zero]
  have hne : (sz &&& 0x7FFFFFFF#32) ≠ 0xFFFFFFFF#32 := by
    intro heq; rw [heq] at hbit; revert hbit; decide
  have hto : (sz &&& 0x7FFFFFFF#32).toNat = sz.toNat := by
    rw [BitVec.toNat_and, show (0x7FFFFFFF#32).toNat = 2 ^ 31 - 1 by decide,
      Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hlt]
  exact ⟨hbit, hne, by omega⟩

theorem bv32_or_garb_bits (hdr : BitVec 32) :
    let h' := hdr ||| 0x00080000#32
    (h' &&& 0x00080000#32) ≠ 0#32 ∧
    (h' &&& 0x00200000#32) = (hdr &&& 0x00200000#32) ∧
    (h' &&& 0x00800000#32) = (hdr &&& 0x00800000#32) := by
  intro h'
  have h19 : (h' &&& 0x00080000#32) ≠ 0#32 := by
    intro h0; have := congrArg (·[19]) h0
    revert this; simp [h', show (0x00080000#32)[19] = true from rfl]
  have hdisj : ∀ mask : BitVec 32, (0x00080000#32 &&& mask) = 0#32 →
      (h' &&& mask) = (hdr &&& mask) := fun mask hm => by
    ext i hi
    have hi0 := congrArg (·[i]) hm
    simp only [BitVec.getElem_and, BitVec.getElem_zero] at hi0
    simp only [h', BitVec.getElem_and, BitVec.getElem_or]
    rw [Bool.and_or_distrib_right, hi0, Bool.or_false]
  exact ⟨h19, hdisj 0x00200000#32 (by decide), hdisj 0x00800000#32 (by decide)⟩

theorem bv32_and_garb_red_eq_zero {hdr : BitVec 32}
    (h : (hdr &&& 0x00480000#32) = 0#32) : (hdr &&& 0x00080000#32) = 0#32 := by
  ext i hi
  have hi0 := congrArg (·[i]) h
  simp only [BitVec.getElem_and, BitVec.getElem_zero] at hi0 ⊢
  by_cases h19 : i = 19
  · subst h19
    have h48 : (0x00480000#32 : BitVec 32).toNat.testBit 19 = true := by decide
    have h08 : (0x00080000#32 : BitVec 32).toNat.testBit 19 = true := by decide
    rw [BitVec.getElem_eq_testBit_toNat, BitVec.getElem_eq_testBit_toNat, h48, Bool.and_true] at hi0
    rw [BitVec.getElem_eq_testBit_toNat, BitVec.getElem_eq_testBit_toNat, h08, Bool.and_true]
    exact hi0
  · have hz : (0x00080000#32 : BitVec 32)[i] = false := by
      have hmask : (0x00080000#32).toNat = 2 ^ 19 := by decide
      rw [BitVec.getElem_eq_testBit_toNat, hmask, Nat.testBit_two_pow]; simp [Ne.symm h19]
    rw [hz, Bool.and_false]

theorem bv32_bit24_disj (hdr mask : BitVec 32) (hm : (0x01000000#32 &&& mask) = 0#32) :
    ((hdr ||| 0x01000000#32) &&& mask) = (hdr &&& mask) ∧
    ((hdr &&& 0xFEFFFFFF#32) &&& mask) = (hdr &&& mask) := by
  have hm_eq : (0xFEFFFFFF#32 &&& mask) = mask := by
    ext i hi
    have h1 := congrArg (·[i]) hm
    simp only [BitVec.getElem_and, BitVec.getElem_zero] at h1
    simp only [BitVec.getElem_and]
    have hinv : (0xFEFFFFFF#32 : BitVec 32)[i] = !((0x01000000#32 : BitVec 32)[i]) := by
      have hc : (0xFEFFFFFF#32 : BitVec 32) = ~~~(0x01000000#32 : BitVec 32) := by decide
      rw [hc, BitVec.getElem_not]
    rw [hinv]; cases h : (0x01000000#32 : BitVec 32)[i] <;> simp_all
  refine ⟨?_, ?_⟩
  · ext i hi
    have h1 := congrArg (·[i]) hm
    simp only [BitVec.getElem_and, BitVec.getElem_zero] at h1
    simp only [BitVec.getElem_and, BitVec.getElem_or]
    rw [Bool.and_or_distrib_right, h1, Bool.or_false]
  · rw [BitVec.and_assoc, hm_eq]

theorem bv8_sext32_sgt0_iff {b : BitVec 8} (hb : b = 0#8 ∨ b = 1#8 ∨ b = 0xFF#8) :
    ((0#32 : BitVec 32).slt (b.signExtend 32) = true) ↔ b = 1#8 := by
  rcases hb with rfl | rfl | rfl <;> decide

theorem bv8_sext32_slt0_iff {b : BitVec 8} (hb : b = 0#8 ∨ b = 1#8 ∨ b = 0xFF#8) :
    ((b.signExtend 32).slt 0#32 = true) ↔ b = 0xFF#8 := by
  rcases hb with rfl | rfl | rfl <;> decide

theorem bv8_sext32_sge0_iff {b : BitVec 8} (hb : b = 0#8 ∨ b = 1#8 ∨ b = 0xFF#8) :
    ((b.signExtend 32).slt 0#32 = false) ↔ (b = 0#8 ∨ b = 1#8) := by
  rcases hb with rfl | rfl | rfl <;> decide

theorem bv8_sext32_eq0_iff {b : BitVec 8} (hb : b = 0#8 ∨ b = 1#8 ∨ b = 0xFF#8) :
    b.signExtend 32 = 0#32 ↔ b = 0#8 := by
  rcases hb with rfl | rfl | rfl <;> decide

theorem bv8_dom_neg_of_not_pos_ne0 {b : BitVec 8} (hb : b = 0#8 ∨ b = 1#8 ∨ b = 0xFF#8)
    (hnp : ¬ ((0#32 : BitVec 32).slt (b.signExtend 32) = true))
    (hnz : b.signExtend 32 ≠ 0#32) : b = 0xFF#8 := by
  rcases hb with rfl | rfl | rfl
  · exact absurd rfl hnz
  · exact absurd (by decide) hnp
  · rfl

theorem bv8_dom_zero_of_not_pos_neg {b : BitVec 8} (hb : b = 0#8 ∨ b = 1#8 ∨ b = 0xFF#8)
    (hnp : ¬ ((0#32 : BitVec 32).slt (b.signExtend 32) = true))
    (hnn : ¬ ((b.signExtend 32).slt 0#32 = true)) : b = 0#8 := by
  rcases hb with rfl | rfl | rfl
  · rfl
  · exact absurd (by decide) hnp
  · exact absurd (by decide) hnn

/-! ## 2. Separation-Logic `vals`/`lvl` Focus & Swap Helpers -/

@[expose] def FullValsLvlRest (c : FullCfg) (s : FullState) : Mem 64 → Prop :=
  dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
  array64 (c.hdr + 32) (hdrTailWords c s) ⋆
  array (t := i8) c.pLitMark s.core.lit_mark ⋆ array (t := i8) c.pMark s.core.mrk ⋆
  array (t := i32) c.pFlags s.core.flags ⋆ array (t := i32) c.pReason s.core.rsns ⋆
  array (t := i32) c.pTrail s.core.trl ⋆ array (t := i32) c.pTrailPos s.core.trail_pos ⋆
  array (t := i32) c.pTmp s.core.tmp ⋆ array (t := i32) c.pMinClr s.core.min_clr ⋆
  FullCoreU32B c s.core ⋆ FullCoreDynArrs c s.core ⋆ FullScratchArrays c s.scratch ⋆ c.pad

theorem focus_full_vals_lvl {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem c s ⋆ R) m) :
    (array (t := i8) c.pVals s.core.vals ⋆ array (t := i32) c.pLevel s.core.lvl ⋆
      (FullValsLvlRest c s ⋆ R)) m := by
  unfold FullMem FullCoreArrays FullCoreByteArrs FullCoreU32A at hm
  unfold FullValsLvlRest; ecancel

private theorem list_set_swap_perm_lt {α : Type} (xs : List α) {a b : Nat}
    (hab : a < b) (hb : b < xs.length) :
    List.Perm ((xs.set a (xs[b]'hb)).set b (xs[a]'(by omega))) xs := by
  let pre := xs.take a
  let mid := (xs.drop (a + 1)).take (b - a - 1)
  let suf := xs.drop (b + 1)
  have hpre : pre.length = a := by simp [pre]; omega
  have hmid : mid.length = b - a - 1 := by simp [mid]; omega
  have hsuf : suf.length = xs.length - b - 1 := by simp [suf]; omega
  have hsplit : ∀ (ys : List α) (x y : α) (hl : ys.length = xs.length),
      ys[a]'(by omega) = x → ys[b]'(by omega) = y →
      (∀ j (hj : j < ys.length), j ≠ a → j ≠ b → ys[j]'hj = xs[j]'(by omega)) →
      ys = pre ++ (x :: (mid ++ [y])) ++ suf := by
    intro ys x y hl hya hyb hoth
    refine List.ext_getElem (by simp [hpre, hmid, hsuf]; omega) fun j hj1 _ => ?_
    by_cases h1 : j < a
    · rw [List.getElem_append_left (by simp [hpre, hmid]; omega),
        List.getElem_append_left (by omega)]
      simp only [pre, List.getElem_take]; exact hoth j hj1 (by omega) (by omega)
    · by_cases h2 : j = a
      · subst j; rw [List.getElem_append_left (by simp [hpre, hmid]),
          List.getElem_append_right (by omega)]; simp [hpre, hya]
      · by_cases h3 : j < b
        · rw [List.getElem_append_left (by simp [hpre, hmid]; omega),
            List.getElem_append_right (by omega)]
          simp only [show j - pre.length = (j - a - 1) + 1 by omega, List.getElem_cons_succ]
          rw [List.getElem_append_left (by omega)]
          simp only [mid, List.getElem_take, List.getElem_drop,
            show a + 1 + (j - a - 1) = j by omega]
          exact hoth j hj1 (by omega) (by omega)
        · by_cases h4 : j = b
          · subst j; rw [List.getElem_append_left (by simp [hpre, hmid]; omega),
              List.getElem_append_right (by omega)]
            simp only [show b - pre.length = (b - a - 1) + 1 by omega, List.getElem_cons_succ]
            rw [List.getElem_append_right (by omega)]; simp [hmid, hyb]
          · rw [List.getElem_append_right (by simp [hpre, hmid]; omega)]
            simp only [suf, List.getElem_drop,
              show b + 1 + (j - (pre ++ x :: (mid ++ [y])).length) = j by
                simp [hpre, hmid]; omega]
            exact hoth j hj1 h2 h4
  have hxs := hsplit xs (xs[a]'(by omega)) (xs[b]'hb) rfl rfl rfl (fun _ _ _ _ => rfl)
  have hsw := hsplit ((xs.set a (xs[b]'hb)).set b (xs[a]'(by omega))) (xs[b]'hb)
    (xs[a]'(by omega)) (by simp)
    (by rw [List.getElem_set_ne (by omega), List.getElem_set_self (by simp; omega)])
    (by rw [List.getElem_set_self (by simp; omega)])
    (fun j _ hja hjb => by
      rw [List.getElem_set_ne (Ne.symm hjb), List.getElem_set_ne (Ne.symm hja)])
  have h1 : List.Perm (mid ++ [xs[a]'(by omega)]) (xs[a]'(by omega) :: mid) := by simp
  have h2 : List.Perm (xs[b]'hb :: mid) (mid ++ [xs[b]'hb]) := by
    simpa using (List.perm_middle (l₁ := mid) (l₂ := []) (a := xs[b]'hb)).symm
  have hp : List.Perm (pre ++ (xs[b]'hb :: (mid ++ [xs[a]'(by omega)])) ++ suf)
      (pre ++ (xs[a]'(by omega) :: (mid ++ [xs[b]'hb])) ++ suf) :=
    (((h1.cons _).trans ((List.Perm.swap _ _ mid).trans (h2.cons _))).append_left pre).append_right
      suf
  exact (List.Perm.of_eq hsw).trans (hp.trans (List.Perm.of_eq hxs.symm))

theorem swapClauseLits_perm {ar : List (BitVec 32)} {p sz a b : Nat}
    (ha : a < sz) (hb : b < sz) (hbd : p + 3 + sz ≤ ar.length) :
    let pa := p + 3 + a; let pb := p + 3 + b
    let ar' := (ar.set pa (ar[pb]'(by omega))).set pb (ar[pa]'(by omega))
    List.Perm (((ar'.drop (p + 3)).take sz).map BitVec.toNat)
      (((ar.drop (p + 3)).take sz).map BitVec.toNat) := by
  intro pa pb ar'
  have hlen1 : ((ar.drop (p + 3)).take sz).length = sz := by simp; omega
  have h1 : (ar'.drop (p + 3)).take sz =
      (((ar.drop (p + 3)).take sz).set a (((ar.drop (p + 3)).take sz)[b]'(by omega))).set b
        (((ar.drop (p + 3)).take sz)[a]'(by omega)) := by
    refine List.ext_getElem (by simp [ar']) fun j hj1 _ => ?_
    have hjsz : j < sz := by simp [ar'] at hj1; omega
    simp only [List.getElem_take, List.getElem_drop, ar', pa, pb]
    by_cases hjb : j = b
    · subst hjb; rw [List.getElem_set_self (by simp; omega), List.getElem_set_self (by simp; omega)]
    · rw [List.getElem_set_ne (by omega), List.getElem_set_ne (Ne.symm hjb)]
      by_cases hja : j = a
      · subst hja
        rw [List.getElem_set_self (by simp; omega), List.getElem_set_self (by simp; omega)]
      · rw [List.getElem_set_ne (by omega), List.getElem_set_ne (Ne.symm hja)]
        simp only [List.getElem_take, List.getElem_drop]
  rw [h1]
  rcases lt_trichotomy a b with hlt | rfl | hgt
  · exact (list_set_swap_perm_lt ((ar.drop (p + 3)).take sz) hlt (by omega)).map BitVec.toNat
  · have heq :
        (((ar.drop (p + 3)).take sz).set a (((ar.drop (p + 3)).take sz)[a]'(by omega))).set a
          (((ar.drop (p + 3)).take sz)[a]'(by omega)) =
        (ar.drop (p + 3)).take sz := by
      refine List.ext_getElem (by simp) fun j hj _ => ?_
      by_cases hja : j = a
      · subst hja; simp
      · rw [List.getElem_set_ne (Ne.symm hja), List.getElem_set_ne (Ne.symm hja)]
    rw [heq]
  · have hswap :
        (((ar.drop (p + 3)).take sz).set a (((ar.drop (p + 3)).take sz)[b]'(by omega))).set b
          (((ar.drop (p + 3)).take sz)[a]'(by omega)) =
        (((ar.drop (p + 3)).take sz).set b (((ar.drop (p + 3)).take sz)[a]'(by omega))).set a
          (((ar.drop (p + 3)).take sz)[b]'(by omega)) := by
      refine List.ext_getElem (by simp) fun j hj _ => ?_
      by_cases hjb : j = b
      · subst hjb; rw [List.getElem_set_self (by simp; omega), List.getElem_set_ne (by omega),
          List.getElem_set_self (by simp; omega)]
      · by_cases hja : j = a
        · subst hja; rw [List.getElem_set_ne (Ne.symm hjb),
            List.getElem_set_self (by simp; omega), List.getElem_set_self (by simp; omega)]
        · rw [List.getElem_set_ne (Ne.symm hjb), List.getElem_set_ne (Ne.symm hja),
            List.getElem_set_ne (Ne.symm hja), List.getElem_set_ne (Ne.symm hjb)]
    rw [hswap]
    exact (list_set_swap_perm_lt ((ar.drop (p + 3)).take sz) hgt (by omega)).map BitVec.toNat

/-! ## 3. Arena Chain, Witness Mode-Flip & M6 Extension Helpers -/

theorem dense_arenaPermEq_trans {k1 k2 k3 : FullCoreState}
    (h1 : FullArenaPermEq k1 k2) (h2 : FullArenaPermEq k2 k3) : FullArenaPermEq k1 k3 :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, fun r hr =>
    let ⟨s1, g1, p1⟩ := h1.2.2 r hr
    let ⟨s2, g2, p2⟩ := h2.2.2 r (h1.2.1.symm ▸ hr)
    ⟨s2.trans s1, g2.trans g1, p2.trans p1⟩⟩

theorem fullArenaScanRefs_next_mem {ar : List (BitVec 32)} {alen : Nat} :
    ∀ {fuel pos r : Nat}, alen - pos ≤ fuel →
      r ∈ fullArenaScanRefs ar alen pos fuel →
      (∀ x ∈ fullArenaScanRefs ar alen pos fuel,
        fullArenaNextOff ar alen x = alen ∨ fullArenaNextOff ar alen x + 3 ≤ alen) →
      fullArenaNextOff ar alen r = alen ∨
        fullArenaNextOff ar alen r ∈ fullArenaScanRefs ar alen pos fuel
  | 0, _, _, _, hr, _ => by simp [fullArenaScanRefs] at hr
  | fuel + 1, pos, r, hfl, hr, hchain => by
    unfold fullArenaScanRefs at hr hchain ⊢; split at hr
    · rename_i hle
      simp only [hle, ↓reduceIte, List.mem_cons] at hr hchain ⊢
      have hb := fullArenaNextOff_bounds (ar := ar) (alen := alen) (cref := pos) hle
      rcases hr with rfl | hrest
      · rcases hchain r (Or.inl rfl) with hend | hmore
        · exact Or.inl hend
        · right; right
          cases fuel with
          | zero => omega
          | succ f' => unfold fullArenaScanRefs; simp [hmore]
      · rcases fullArenaScanRefs_next_mem (fuel := fuel) (pos := fullArenaNextOff ar alen pos)
            (r := r) (by omega) hrest (fun x hx => hchain x (Or.inr hx)) with hend | hmem
        · exact Or.inl hend
        · exact Or.inr (Or.inr hmem)
    · simp at hr

theorem fullArenaClauseRefs_zero_mem {c : FullCfg} {F_cur : List (List Nat)} {k : FullCoreState}
    (ha : FullArenaClausesInv c F_cur k) (hpos : 0 < k.arena_len) :
    0 ∈ fullArenaClauseRefsCore k := by
  have h3 : 3 ≤ k.arena_len := ha.len_ok.resolve_left (by omega)
  unfold fullArenaClauseRefsCore
  cases h : k.arena_len with
  | zero => omega
  | succ f => unfold fullArenaScanRefs; simp [← h, h3]

theorem fullArenaClauseRefs_next_mem {c : FullCfg} {F_cur : List (List Nat)} {k : FullCoreState}
    (ha : FullArenaClausesInv c F_cur k) {r : Nat} (hr : r ∈ fullArenaClauseRefsCore k) :
    fullArenaNextOff k.arena k.arena_len r = k.arena_len ∨
      fullArenaNextOff k.arena k.arena_len r ∈ fullArenaClauseRefsCore k :=
  fullArenaScanRefs_next_mem (by omega) hr fun x hx => (ha.refs_wf x hx).2.2.2.2

theorem fullWitnessInv_with_dense_mode_zero {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) :
    FullWitnessInv c F0 F_cur { k with dense_mode := 0#64 } := by
  have hwat : ModeWatchesInv F_cur { k with dense_mode := 0#64 } := by
    simp only [ModeWatchesInv, ↓reduceIte]
    have h0 := hw.watches
    by_cases hc : k.dense_mode = 0#64
    · simp only [ModeWatchesInv, hc, ↓reduceIte] at h0
      refine ⟨h0.layout.with_wstk rfl rfl rfl rfl, fun l hl => ?_⟩
      simpa [fullWatchOffCore, fullWatchSizeCore] using
        (h0.slices l hl).mono (k := k) (k' := { k with dense_mode := 0#64 })
          (by rw [CNF.entails_def]; exact fun _ p => p)
          (Nat.le_refl k.cur_vars) (fun _ r => r) (fun _ _ _ => rfl)
    · simp only [ModeWatchesInv, hc, ↓reduceIte] at h0
      have hw0 := h0.toWatchesInv
      refine ⟨hw0.layout.with_wstk rfl rfl rfl rfl, fun l hl => ?_⟩
      simpa [fullWatchOffCore, fullWatchSizeCore] using
        (hw0.slices l hl).mono (k := k) (k' := { k with dense_mode := 0#64 })
          (by rw [CNF.entails_def]; exact fun _ p => p)
          (Nat.le_refl k.cur_vars) (fun _ r => r) (fun _ _ _ => rfl)
  exact { hw with arena := { hw.arena with len_ok := hw.arena.len_ok }, watches := hwat }

theorem fullWitnessInv_with_dense_mode_nz {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k)
    (hd : DenseWatchesInv F_cur k) {dm : BitVec 64} (hdm : dm ≠ 0#64) :
    FullWitnessInv c F0 F_cur { k with dense_mode := dm } := by
  have hwat : ModeWatchesInv F_cur { k with dense_mode := dm } := by
    simp only [ModeWatchesInv, hdm, ↓reduceIte]
    refine ⟨hd.layout.with_wstk rfl rfl rfl rfl, fun l hl => ?_⟩
    simpa [fullWatchOffCore, fullWatchSizeCore] using
      (hd.slices l hl).mono (k := k) (k' := { k with dense_mode := dm })
        (by rw [CNF.entails_def]; exact fun _ p => p)
        (Nat.le_refl k.cur_vars) (fun _ r => r) (fun _ _ _ => rfl)
  exact { hw with arena := { hw.arena with len_ok := hw.arena.len_ok }, watches := hwat }

theorem fullWitnessInv_with_unflushed {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (u' : BitVec 64) :
    FullWitnessInv c F0 F_cur { k with unflushed := u' } :=
  { hw with arena := { hw.arena with len_ok := hw.arena.len_ok }
            watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) }

theorem fullWitnessInv_with_oom {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (o' : BitVec 64) :
    FullWitnessInv c F0 F_cur { k with oom := o' } :=
  { hw with arena := { hw.arena with len_ok := hw.arena.len_ok }
            watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) }

theorem dense_fullCore_inconsistent_unsat {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hinv : FullCoreInv c F0 s) (hinc : s.core.inconsistent ≠ 0#64) : F0.Unsat :=
  hinv.inconsistent_unsat hinc

theorem dense_m6_extInit_trans {ext0 ext1 ext2 : List (BitVec 64)}
    (h1 : M6HdrExtInitOk ext0 → M6HdrExtInitOk ext1 ∧ M6ExtW2bPres ext0 ext1)
    (h2 : M6HdrExtInitOk ext1 → M6HdrExtInitOk ext2 ∧ M6ExtW2bPres ext1 ext2) :
    M6HdrExtInitOk ext0 → M6HdrExtInitOk ext2 ∧ M6ExtW2bPres ext0 ext2 := fun hi0 =>
  let ⟨hi1, hw01⟩ := h1 hi0
  let ⟨hi2, hw12⟩ := h2 hi1
  ⟨hi2, hw01.trans hw12⟩

theorem modifyClauseBody_preserves_witness {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {k : FullCoreState} (hlen : k.LengthsOk c)
    (hw : FullWitnessInv c F0 F_cur k) {p : Nat} (hp : p ∈ fullArenaClauseRefsCore k)
    {ar' : List (BitVec 32)} (hlen_ar : ar'.length = c.arena_cap)
    (hout : OutsideSliceAgrees (p + 1) (p + 3 + fullArenaClauseSizeCore k p) k.arena ar')
    (h2 : ar'[p + 2]? = k.arena[p + 2]?)
    (hmem : ∀ l, l ∈ fullArenaClauseLitsCore { k with arena := ar' } p ↔
      l ∈ fullArenaClauseLitsCore k p) :
    let k' := { k with arena := ar' }
    fullArenaClauseRefsCore k' = fullArenaClauseRefsCore k ∧
    (∀ r ∈ fullArenaClauseRefsCore k,
      fullArenaHdrCore k' r = fullArenaHdrCore k r ∧
      fullArenaClauseSizeCore k' r = fullArenaClauseSizeCore k r ∧
      fullArenaClauseGarbCore k' r = fullArenaClauseGarbCore k r) ∧
    (∀ r ∈ fullArenaClauseRefsCore k, r ≠ p →
      fullArenaClauseLitsCore k' r = fullArenaClauseLitsCore k r) ∧
    FullWitnessInv c F0 F_cur k' := by
  intro k'
  have hpwf := hw.arena.refs_wf p hp
  have hne_out : ∀ r ∈ fullArenaClauseRefsCore k, r ≠ p →
      (r + 3 + fullArenaClauseSizeCore k r ≤ p ∧ fullArenaNextOff k.arena k.arena_len r ≤ p) ∨
      (p + 3 + fullArenaClauseSizeCore k p ≤ fullArenaNextOff k.arena k.arena_len p ∧
        fullArenaNextOff k.arena k.arena_len p ≤ r) := fun r hr hne => by
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · exact Or.inl ⟨by have := fullArenaScanRefs_disjoint hr hp hlt
                       have := (hw.arena.refs_wf r hr).2.2.1; omega,
        fullArenaScanRefs_disjoint hr hp hlt⟩
    · exact Or.inr ⟨hpwf.2.2.1, fullArenaScanRefs_disjoint hp hr hgt⟩
  have hnxt : ∀ r ∈ fullArenaClauseRefsCore k,
      fullArenaNextOff ar' k.arena_len r = fullArenaNextOff k.arena k.arena_len r := by
    intro r hr; by_cases hrc : r = p
    · subst r
      exact fullArenaNextOff_congr_block (hout.getElem?_lt (by omega)) h2
        (fun i hi _ => hout.getElem?_ge hi)
    · refine fullArenaNextOff_congr_block ?_ ?_ ?_
      · rcases hne_out r hr hrc with ⟨_, _⟩ | ⟨_, _⟩
        · exact hout.getElem?_lt (by omega)
        · exact hout.getElem?_ge (by omega)
      · rcases hne_out r hr hrc with ⟨_, _⟩ | ⟨_, _⟩
        · exact hout.getElem?_lt (by omega)
        · exact hout.getElem?_ge (by omega)
      · intro idx _ hi2; rcases hne_out r hr hrc with ⟨_, hle⟩ | ⟨_, hgt⟩
        · exact hout.getElem?_lt (by omega)
        · exact hout.getElem?_ge (by have := (hw.arena.refs_wf r hr).2.2.1; omega)
  have hrefs : fullArenaClauseRefsCore k' = fullArenaClauseRefsCore k :=
    fullArenaClauseRefsCore_congr rfl hnxt
  have hmeta : ∀ r ∈ fullArenaClauseRefsCore k,
      fullArenaHdrCore k' r = fullArenaHdrCore k r ∧
      fullArenaClauseSizeCore k' r = fullArenaClauseSizeCore k r ∧
      fullArenaClauseGarbCore k' r = fullArenaClauseGarbCore k r := fun r hr => by
    by_cases hrp : r = p
    · subst r; have h0 := hout.getElem?_lt (i := p) (by omega)
      exact ⟨by unfold fullArenaHdrCore k'; rw [h0],
        by unfold fullArenaClauseSizeCore k'; rw [h2],
        by unfold fullArenaClauseGarbCore fullArenaHdrCore k'; rw [h0]⟩
    · rcases hne_out r hr hrp with ⟨_, _⟩ | ⟨_, _⟩
      · have h0 := hout.getElem?_lt (i := r) (by omega)
        have hs := hout.getElem?_lt (i := r + 2) (by omega)
        exact ⟨by unfold fullArenaHdrCore k'; rw [h0],
          by unfold fullArenaClauseSizeCore k'; rw [hs],
          by unfold fullArenaClauseGarbCore fullArenaHdrCore k'; rw [h0]⟩
      · have h0 := hout.getElem?_ge (i := r) (by omega)
        have hs := hout.getElem?_ge (i := r + 2) (by omega)
        exact ⟨by unfold fullArenaHdrCore k'; rw [h0],
          by unfold fullArenaClauseSizeCore k'; rw [hs],
          by unfold fullArenaClauseGarbCore fullArenaHdrCore k'; rw [h0]⟩
  have hlits_other : ∀ r ∈ fullArenaClauseRefsCore k, r ≠ p →
      fullArenaClauseLitsCore k' r = fullArenaClauseLitsCore k r := fun r hr hrp => by
    have hbd1 : r + 3 + fullArenaClauseSizeCore k r ≤ k.arena.length := by
      have := (hw.arena.refs_wf r hr).2.2.1; have := (hw.arena.refs_wf r hr).2.2.2.1
      have := hlen.arena_len_le; have := hlen.arena_len_arr; omega
    have hbd2 : r + 3 + fullArenaClauseSizeCore k r ≤ ar'.length := by
      rw [hlen_ar, ← hlen.arena_len_arr]; exact hbd1
    exact fullArenaClauseLitsCore_eq_of_hold (k := k) (k' := k') hbd1 hbd2
      (hmeta r hr).2.1 fun j _ => by
        rcases hne_out r hr hrp with ⟨_, _⟩ | ⟨_, _⟩
        · exact hout.getElem?_lt (by omega)
        · exact hout.getElem?_ge (by omega)
  have hmem_all : ∀ r ∈ fullArenaClauseRefsCore k,
      ∀ l, l ∈ fullArenaClauseLitsCore k' r ↔ l ∈ fullArenaClauseLitsCore k r := fun r hr l => by
    by_cases hrp : r = p
    · subst r; exact hmem l
    · rw [hlits_other r hr hrp]
  have harena' : FullArenaClausesInv c F_cur k' := by
    refine ⟨hw.arena.len_ok, ?_, ?_, ?_, ?_⟩
    · intro r hr; rw [hrefs] at hr; have h := hw.arena.refs_wf r hr
      dsimp only [k'] at hnxt ⊢; rw [hnxt r hr, (hmeta r hr).2.1]; exact h
    · intro r hr hsh; rw [hrefs] at hr; rw [(hmeta r hr).1] at hsh
      obtain ⟨t, ht1, ht2, hsent⟩ := hw.arena.shrk_term r hr hsh
      have hr3 := (hw.arena.refs_wf r hr).1
      have hget_r : k.arena[r]? = some (fullArenaHdrCore k r) := by
        have : r < k.arena.length := by have := hlen.arena_len_le; have := hlen.arena_len_arr; omega
        unfold fullArenaHdrCore; rw [List.getElem?_eq_getElem this, Option.getD_some]
      obtain ⟨t0, ht0_lo, _, _, ht0_sent⟩ := fullArenaNextOff_hits_sentinel hr3
        (by rw [hget_r, Option.getD_some]; exact hsh) ht1 ht2 hsent
      have hnxt_le := (hw.arena.refs_wf r hr).2.2.2.1
      refine ⟨t0, by rw [(hmeta r hr).2.1]; exact ht0_lo, by dsimp only [k']; omega, ?_⟩
      dsimp only [k']; by_cases hrp : r = p
      · subst r; rw [hout.getElem?_ge ht0_lo]; exact ht0_sent
      · rcases hne_out r hr hrp with ⟨_, _⟩ | ⟨_, _⟩
        · rw [hout.getElem?_lt (by omega)]; exact ht0_sent
        · rw [hout.getElem?_ge (by have := (hw.arena.refs_wf r hr).2.2.1; omega)]; exact ht0_sent
    · intro r hr hng l hl; rw [hrefs] at hr
      rw [(hmeta r hr).2.2] at hng; rw [hmem_all r hr l] at hl; exact hw.arena.lits_lt r hr hng l hl
    · intro r hr hng; rw [hrefs] at hr; rw [(hmeta r hr).2.2] at hng
      exact entails_of_mem_or_false (hw.arena.entails r hr hng) fun l hl =>
        Or.inl ((hmem_all r hr l).mpr hl)
  refine ⟨hrefs, hmeta, hlits_other, { hw with
    arena := harena'
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun r hr => hrefs ▸ hr)
    reason_inv := fun idx hidx hne => by
      have hrs := hw.reason_inv idx hidx hne; dsimp only [k'] at hrs ⊢
      by_cases hb : (k.rsns[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD
          0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32
      · rw [ite_eq_left hb] at hrs ⊢; exact hrs
      · rw [ite_eq_right hb] at hrs ⊢
        exact ⟨hrefs ▸ hrs.1, (hmeta _ hrs.1).2.2.trans hrs.2.1,
          fun q hq => hrs.2.2 q ((hmem_all _ hrs.1 q).mp hq)⟩
    reason_lit_mem := fun idx hidx hne hlg => by
      have hrs := hw.reason_inv idx hidx hne
      have hb : ¬ (k.rsns[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD
          0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32 := fun h => absurd hlg h
      rw [ite_eq_right hb] at hrs
      exact (hmem_all _ hrs.1 _).mpr (hw.reason_lit_mem idx hidx hne hlg) }⟩

/-! ## 4. Dense Propagation (`DenseWatchSliceOk`, CNF Unit Resolution & `FullDenseInvW`) -/

theorem dense_denseWatchesInv_of_w {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) : DenseWatchesInv F_cur s.core := by
  simpa [ModeWatchesInv, h.2.2.2.2.2.2] using h.2.1.watches

theorem denseSlice_step_bin {F_cur : List (List Nat)} {k : FullCoreState} {lit p rem : Nat}
    {w0 : BitVec 32} (hslice : DenseWatchSliceOk F_cur k lit p rem) (hpos : 0 < rem)
    (hp : k.wstk[p]? = some w0) (hbin : (w0 &&& 0x80000000#32) ≠ 0#32) :
    1 ≤ rem ∧ (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k.cur_vars ∧
    (cnfOfClauses F_cur).EntailsClause (cnfClause [lit, (w0 &&& 0x7FFFFFFF#32).toNat]) ∧
    DenseWatchSliceOk F_cur k lit (p + 1) (rem - 1) := by
  cases hslice with
  | empty => simp at hpos
  | @bin _ rem' w0' hp' _ _ hlt hent hrest =>
    rw [hp'] at hp; cases hp; exact ⟨by omega, hlt, hent, hrest⟩
  | @occ _ _ _ _ hp' _ hocc =>
    rw [hp'] at hp; cases hp; exact absurd hocc hbin

theorem denseSlice_step_occ {F_cur : List (List Nat)} {k : FullCoreState} {lit p rem : Nat}
    {w0 : BitVec 32} (hslice : DenseWatchSliceOk F_cur k lit p rem) (hpos : 0 < rem)
    (hp : k.wstk[p]? = some w0) (hocc : (w0 &&& 0x80000000#32) = 0#32) :
    ∃ (cref : BitVec 32),
      2 ≤ rem ∧ k.wstk[p + 1]? = some cref ∧ 3 ≤ w0.toNat ∧ cref.toNat < 0x80000000 ∧
      cref.toNat ∈ fullArenaClauseRefsCore k ∧
      DenseWatchSliceOk F_cur k lit (p + 2) (rem - 2) := by
  cases hslice with
  | empty => simp at hpos
  | @bin _ _ _ hp' hbin =>
    rw [hp'] at hp; cases hp; exact absurd hocc hbin
  | @occ _ rem' w0' cref hp' hp1 _ hsz hlt href hrest =>
    rw [hp'] at hp; cases hp
    exact ⟨cref, by omega, hp1, hsz, hlt, href, hrest⟩

theorem denseSlice_congr {F_cur : List (List Nat)} {k : FullCoreState} {lit p p' rem rem' : Nat}
    (hp : p = p') (hrem : rem = rem')
    (h : DenseWatchSliceOk F_cur k lit p rem) :
    DenseWatchSliceOk F_cur k lit p' rem' := by
  subst hp hrem; exact h

theorem dense_vals_true_entails {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (hl0 : k.cur_level = 0)
    {l : Nat} (hlt : l < 2 * k.cur_vars) (htrue : k.vals[l]?.getD 0#8 = 1#8) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause [l]) := by
  obtain ⟨i, hi, heq⟩ := (hw.vals_true_iff l hlt).mp htrue
  have := hw.level0_sound i hi (by have := hw.lvl_le i hi; omega)
  rwa [heq] at this

theorem dense_vals_false_entails {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (hl0 : k.cur_level = 0)
    {l : Nat} (hlt : l < 2 * k.cur_vars) (hfalse : k.vals[l]?.getD 0#8 = 0xFF#8) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause [l ^^^ 1]) := by
  obtain ⟨i, hi, heq⟩ := (hw.vals_false_iff l hlt).mp hfalse
  have := hw.level0_sound i hi (by have := hw.lvl_le i hi; omega)
  rwa [heq] at this

theorem dense_resolve_bin_unit {F : CNF Nat} {l a b : Nat}
    (hbin : F.EntailsClause (cnfClause [a, b])) (heq : a = l ∨ b = l)
    (hneg : F.EntailsClause (cnfClause [l ^^^ 1])) :
    F.EntailsClause (cnfClause [if a = l then b else a]) := by
  rw [CNF.entails_clause_def]
  intro α hα
  have s1 := (clauseEvalVal_iff α _).mpr (CNF.entails_clause_def.mp hbin α hα)
  have s2 := (clauseEvalVal_iff α _).mpr (CNF.entails_clause_def.mp hneg α hα)
  rw [← clauseEvalVal_iff]
  simp only [clauseEvalVal, List.any_cons, List.any_nil, Bool.or_false] at s1 s2 ⊢
  have hnl : evalLitVal α (l ^^^ 1) = !(evalLitVal α l) := by
    simpa [litNeg] using evalLitVal_litNeg α l
  rw [hnl] at s2
  rcases heq with rfl | rfl
  · cases ha : evalLitVal α a <;> cases hb : evalLitVal α b <;> simp_all
  · by_cases hal : a = b
    · subst hal; cases ha : evalLitVal α a <;> simp_all
    · simp only [hal, ↓reduceIte]
      cases ha : evalLitVal α a <;> cases hb : evalLitVal α b <;> simp_all

theorem dense_unsat_of_lit_neg {F : CNF Nat} {l : Nat}
    (hp : F.EntailsClause (cnfClause [l])) (hn : F.EntailsClause (cnfClause [l ^^^ 1])) :
    F.Unsat := by
  refine unsat_of_entails_nil (CNF.entails_clause_def.mpr fun α hα => ?_)
  have s1 := (clauseEvalVal_iff α _).mpr (CNF.entails_clause_def.mp hp α hα)
  have s2 := (clauseEvalVal_iff α _).mpr (CNF.entails_clause_def.mp hn α hα)
  simp only [clauseEvalVal, List.any_cons, List.any_nil, Bool.or_false] at s1 s2
  have hnl : evalLitVal α (l ^^^ 1) = !(evalLitVal α l) := by
    simpa [litNeg] using evalLitVal_litNeg α l
  rw [hnl, s1] at s2; simp at s2

theorem dense_clause_all_false_unsat {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (hl0 : k.cur_level = 0)
    {cl : List Nat} (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause cl))
    (hlts : ∀ l ∈ cl, l < 2 * k.cur_vars)
    (hvals : ∀ l ∈ cl, k.vals[l]?.getD 0#8 = 0xFF#8) :
    (cnfOfClauses F_cur).Unsat := by
  refine unsat_of_entails_nil (entails_of_mem_or_false hent fun l hl => Or.inr ?_)
  exact dense_vals_false_entails hw hl0 (hlts l hl) (hvals l hl)

theorem dense_clause_one_unass_entails {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (hl0 : k.cur_level = 0)
    {cl : List Nat} (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause cl))
    (hlts : ∀ l ∈ cl, l < 2 * k.cur_vars) {u : Nat}
    (hother : ∀ l ∈ cl, l ≠ u → k.vals[l]?.getD 0#8 = 0xFF#8) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause [u]) := by
  refine entails_of_mem_or_false hent fun l hl => ?_
  by_cases hlu : l = u
  · subst hlu; exact Or.inl List.mem_cons_self
  · exact Or.inr (dense_vals_false_entails hw hl0 (hlts l hl) (hother l hl hlu))

/-- Shared frame predicate preserved across `full_m6_dense_prop*` and
`full_dense_{prop_unit,flush_units}_m7`. -/
@[expose] def DensePropPres (s0 s1 : FullState) : Prop :=
  s1.core.cur_vars = s0.core.cur_vars ∧
  s1.core.arena_len = s0.core.arena_len ∧
  s1.core.fuel = s0.core.fuel ∧
  s1.core.repr = s0.core.repr ∧
  fullArenaClauseRefs s1 = fullArenaClauseRefs s0 ∧
  s1.scratch.tarjan_mark = s0.scratch.tarjan_mark ∧
  s1.scratch.tarjan_reach = s0.scratch.tarjan_reach ∧
  s1.scratch.red_refs = s0.scratch.red_refs ∧
  s1.scratch.scratch_buf = s0.scratch.scratch_buf ∧
  s1.scratch.work_stk1 = s0.scratch.work_stk1 ∧
  s1.scratch.work_stk2 = s0.scratch.work_stk2 ∧
  s1.scratch.sim_sig = s0.scratch.sim_sig ∧
  s1.scratch.glue_used = s0.scratch.glue_used

theorem densePropPres_refl (s : FullState) : DensePropPres s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem densePropPres_trans {s0 s1 s2 : FullState}
    (h1 : DensePropPres s0 s1) (h2 : DensePropPres s1 s2) : DensePropPres s0 s2 :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1,
    h2.2.2.2.1.trans h1.2.2.2.1, h2.2.2.2.2.1.trans h1.2.2.2.2.1,
    h2.2.2.2.2.2.1.trans h1.2.2.2.2.2.1, h2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.1,
    h2.2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.2.1,
    h2.2.2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.2.2.1,
    h2.2.2.2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.2.2.2.1,
    h2.2.2.2.2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.2.2.2.2.1,
    h2.2.2.2.2.2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.2.2.2.2.2.1,
    h2.2.2.2.2.2.2.2.2.2.2.2.2.trans h1.2.2.2.2.2.2.2.2.2.2.2.2⟩

private theorem dense_fullWitnessInv_set_arena_hdr_bit24 {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hlen : s.LengthsOk c)
    (hw : FullWitnessInv c F0 F_cur s.core) {cref : Nat} (href : cref ∈ fullArenaClauseRefs s)
    (v : BitVec 32)
    (h24 : v = fullArenaHdr s cref ||| 0x01000000#32 ∨
      v = fullArenaHdr s cref &&& 0xFEFFFFFF#32) :
    let s' : FullState := { s with core := { s.core with arena := s.core.arena.set cref v } }
    s'.LengthsOk c ∧ FullWitnessInv c F0 F_cur s'.core ∧
    fullArenaClauseRefs s' = fullArenaClauseRefs s ∧
    (∀ r ∈ fullArenaClauseRefs s,
      fullArenaClauseSize s' r = fullArenaClauseSize s r ∧
      fullArenaClauseGarb s' r = fullArenaClauseGarb s r ∧
      fullArenaClauseLits s' r = fullArenaClauseLits s r) := by
  intro s'
  have hcl := hlen.core_ok
  have har_len : cref < s.core.arena.length := by
    have := (hw.arena.refs_wf cref href).1
    have := hcl.arena_len_le; have := hcl.arena_len_arr; omega
  have hget_c : s.core.arena[cref]? = some (fullArenaHdr s cref) := by
    unfold fullArenaHdr fullArenaHdrCore; rw [List.getElem?_eq_getElem har_len, Option.getD_some]
  have hdisj : ∀ mask : BitVec 32, (0x01000000#32 &&& mask) = 0#32 →
      (v &&& mask) = (fullArenaHdr s cref &&& mask) := fun mask hm => by
    rcases h24 with rfl | rfl
    · exact (bv32_bit24_disj (fullArenaHdr s cref) mask hm).1
    · exact (bv32_bit24_disj (fullArenaHdr s cref) mask hm).2
  have hshrk_eq : (v &&& 0x00800000#32) = (fullArenaHdr s cref &&& 0x00800000#32) :=
    hdisj 0x00800000#32 (by decide)
  have hgarb_eq : (v &&& 0x00080000#32) = (fullArenaHdr s cref &&& 0x00080000#32) :=
    hdisj 0x00080000#32 (by decide)
  have hdisj_c : ∀ r ∈ fullArenaClauseRefsCore s.core, r ≠ cref →
      (r + 3 + fullArenaClauseSizeCore s.core r ≤ cref ∧
        fullArenaNextOff s.core.arena s.core.arena_len r ≤ cref) ∨
      (cref + 3 + fullArenaClauseSizeCore s.core cref ≤
        fullArenaNextOff s.core.arena s.core.arena_len cref ∧
        fullArenaNextOff s.core.arena s.core.arena_len cref ≤ r) := fun r hr hne => by
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · exact Or.inl ⟨by have := fullArenaScanRefs_disjoint hr href hlt
                       have := (hw.arena.refs_wf r hr).2.2.1; omega,
        fullArenaScanRefs_disjoint hr href hlt⟩
    · exact Or.inr ⟨(hw.arena.refs_wf cref href).2.2.1, fullArenaScanRefs_disjoint href hr hgt⟩
  have hnxt : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaNextOff s'.core.arena s.core.arena_len r =
        fullArenaNextOff s.core.arena s.core.arena_len r := by
    intro r hr; by_cases hrc : r = cref
    · subst r
      have hwf := hw.arena.refs_wf cref hr
      have h1 : ¬ (cref + 3 > s.core.arena_len) := by omega
      have h2 : ¬ (cref + 3 + (s.core.arena[cref + 2]?.getD 0#32).toNat > s.core.arena_len) := by
        unfold fullArenaClauseSizeCore at hwf; omega
      have h2eq : s'.core.arena[cref + 2]? = s.core.arena[cref + 2]? :=
        List.getElem?_set_ne (by omega)
      unfold fullArenaNextOff
      simp only [h1, ↓reduceIte, h2eq, h2, show s'.core.arena[cref]? = some v from
        List.getElem?_set_self har_len, Option.getD_some, hshrk_eq]
      rw [show fullArenaHdr s cref = s.core.arena[cref]?.getD 0#32 from rfl]
      split
      · exact fullArenaSkipShrk_congr fun i hi _ => List.getElem?_set_ne (by omega)
      · rfl
    · refine fullArenaNextOff_congr_block (List.getElem?_set_ne (Ne.symm hrc)) ?_ ?_
      · rcases hdisj_c r hr hrc with ⟨h1, _⟩ | ⟨h3, h2⟩
        · have := (hw.arena.refs_wf r hr).2.1; exact List.getElem?_set_ne (by omega)
        · exact List.getElem?_set_ne (by omega)
      · intro i _ _; rcases hdisj_c r hr hrc with ⟨_, hle⟩ | ⟨h3, hgt⟩
        · exact List.getElem?_set_ne (by omega)
        · have := (hw.arena.refs_wf r hr).2.2.1; exact List.getElem?_set_ne (by omega)
  have hrefs : fullArenaClauseRefsCore s'.core = fullArenaClauseRefsCore s.core :=
    fullArenaClauseRefsCore_congr rfl hnxt
  have hper : ∀ r ∈ fullArenaClauseRefs s,
      fullArenaClauseSizeCore s'.core r = fullArenaClauseSizeCore s.core r ∧
      fullArenaClauseGarbCore s'.core r = fullArenaClauseGarbCore s.core r ∧
      fullArenaClauseLitsCore s'.core r = fullArenaClauseLitsCore s.core r := by
    intro r hr
    have hbd : r + 3 + fullArenaClauseSizeCore s.core r ≤ s.core.arena.length := by
      have := (hw.arena.refs_wf r hr).2.2.1; have := (hw.arena.refs_wf r hr).2.2.2.1
      have := hcl.arena_len_le; have := hcl.arena_len_arr; omega
    by_cases hrc : r = cref
    · subst r
      have hsz : fullArenaClauseSizeCore s'.core cref = fullArenaClauseSizeCore s.core cref := by
        unfold fullArenaClauseSizeCore s'
        rw [List.getElem?_set_ne (by omega)]
      have hlits : fullArenaClauseLitsCore s'.core cref = fullArenaClauseLitsCore s.core cref :=
        fullArenaClauseLitsCore_eq_of_hold hbd (by simp [s', hbd]) hsz fun j _ =>
          List.getElem?_set_ne (by omega)
      have hgarb : fullArenaClauseGarbCore s'.core cref = fullArenaClauseGarbCore s.core cref := by
        unfold fullArenaClauseGarbCore fullArenaHdrCore s'
        rw [List.getElem?_set_self har_len, Option.getD_some, hgarb_eq]
        rfl
      exact ⟨hsz, hgarb, hlits⟩
    · have hout : r + 3 + fullArenaClauseSizeCore s.core r ≤ cref ∨ cref + 3 ≤ r := by
        rcases hdisj_c r hr hrc with ⟨h1, _⟩ | ⟨h3, h2⟩ <;> omega
      have hlo := fullArenaClauseLitsCore_set_outside (v := v) hbd hout
      have hgarb : fullArenaClauseGarbCore s'.core r = fullArenaClauseGarbCore s.core r := by
        unfold fullArenaClauseGarbCore fullArenaHdrCore s'
        rw [List.getElem?_set_ne (Ne.symm hrc)]
      exact ⟨hlo.1, hgarb, hlo.2⟩
  have hlen' : s'.LengthsOk c :=
    ⟨{ hcl with arena_len_arr := by simp [s', hcl.arena_len_arr] }, hlen.scratch_ok⟩
  have harena' : FullArenaClausesInv c F_cur s'.core := by
    refine ⟨hw.arena.len_ok, ?_, ?_, ?_, ?_⟩
    · intro r hr; rw [hrefs] at hr; have hwf := hw.arena.refs_wf r hr
      dsimp only [s'] at hnxt ⊢; rw [hnxt r hr, (hper r hr).1]; exact hwf
    · intro r hr hsh; rw [hrefs] at hr
      have hsh0 : (fullArenaHdrCore s.core r &&& 0x00800000#32) ≠ 0#32 := by
        by_cases hrc : r = cref
        · subst r; unfold fullArenaHdrCore at hsh ⊢
          rw [List.getElem?_set_self har_len, Option.getD_some, hshrk_eq] at hsh
          rwa [hget_c, Option.getD_some]
        · unfold fullArenaHdrCore at hsh ⊢
          simpa [s', List.getElem?_set_ne (Ne.symm hrc)] using hsh
      obtain ⟨t, ht1, ht2, hsent⟩ := hw.arena.shrk_term r hr hsh0
      have hget_r : s.core.arena[r]? = some (fullArenaHdrCore s.core r) := by
        have : r < s.core.arena.length := by
          have := (hw.arena.refs_wf r hr).1; have := hcl.arena_len_le
          have := hcl.arena_len_arr; omega
        unfold fullArenaHdrCore; rw [List.getElem?_eq_getElem this, Option.getD_some]
      obtain ⟨t0, ht0_lo, _, _, ht0_sent⟩ := fullArenaNextOff_hits_sentinel
        (hw.arena.refs_wf r hr).1 (by rwa [hget_r, Option.getD_some]) ht1 ht2 hsent
      have ht0_ne : t0 ≠ cref := by
        by_cases hrc : r = cref
        · subst r; have := (hw.arena.refs_wf cref hr).2.1; omega
        · rcases hdisj_c r hr hrc with ⟨_, hle⟩ | ⟨h3, hgt⟩
          · omega
          · have := (hw.arena.refs_wf r hr).2.1; omega
      refine ⟨t0, by rw [(hper r hr).1]; exact ht0_lo,
        by dsimp only [s']; have := (hw.arena.refs_wf r hr).2.2.2.1; omega, ?_⟩
      dsimp only [s']; rw [List.getElem?_set_ne ht0_ne.symm]; exact ht0_sent
    · intro r hr hng l hl; rw [hrefs] at hr
      rw [(hper r hr).2.1] at hng; rw [(hper r hr).2.2] at hl
      exact hw.arena.lits_lt r hr hng l hl
    · intro r hr hng; rw [hrefs] at hr
      rw [(hper r hr).2.1] at hng; rw [(hper r hr).2.2]
      exact hw.arena.entails r hr hng
  exact ⟨hlen', { hw with
    arena := harena'
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun r hr => hrefs ▸ hr)
    reason_inv := fun idx hidx hne => by
      have hrs := hw.reason_inv idx hidx hne; dsimp only [s'] at hrs ⊢
      by_cases hb : (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
          0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32
      · rw [ite_eq_left hb] at hrs ⊢; exact hrs
      · rw [ite_eq_right hb] at hrs ⊢
        have hp := hper _ hrs.1
        have hq : ∀ q, q ∈ fullArenaClauseLitsCore s'.core
            (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat →
            q ∈ fullArenaClauseLitsCore s.core
            (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat := by
          intro q hqi; rwa [hp.2.2] at hqi
        exact ⟨hrefs ▸ hrs.1, hp.2.1.trans hrs.2.1, fun q hqi => hrs.2.2 q (hq q hqi)⟩
    reason_lit_mem := fun idx hidx hne hlg => by
      have hrs := hw.reason_inv idx hidx hne
      have hb : ¬ (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
          0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32 := fun h => absurd hlg h
      rw [ite_eq_right hb] at hrs
      have hp := (hper _ hrs.1).2.2
      change (s.core.trl[idx]?.getD 0#32).toNat ∈ fullArenaClauseLitsCore s'.core
        (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat
      rw [hp]; exact hw.reason_lit_mem idx hidx hne hlg }, hrefs, hper⟩

theorem fullDenseInvW_set_hdr_bit24 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hdw : FullDenseInvW c F0 F_cur s) {cref : Nat}
    (href : cref ∈ fullArenaClauseRefs s) (v : BitVec 32)
    (h24 : v = fullArenaHdr s cref ||| 0x01000000#32 ∨
      v = fullArenaHdr s cref &&& 0xFEFFFFFF#32) :
    let s' : FullState := { s with core := { s.core with arena := s.core.arena.set cref v } }
    FullDenseInvW c F0 F_cur s' ∧ fullArenaClauseRefs s' = fullArenaClauseRefs s ∧
    (∀ r ∈ fullArenaClauseRefs s,
      fullArenaClauseSize s' r = fullArenaClauseSize s r ∧
      fullArenaClauseGarb s' r = fullArenaClauseGarb s r ∧
      fullArenaClauseLits s' r = fullArenaClauseLits s r) := by
  intro s'
  obtain ⟨hlen', hw', hrefs, hper⟩ :=
    dense_fullWitnessInv_set_arena_hdr_bit24 hdw.1 hdw.2.1 href v h24
  have hnd' : FullArenaVarsNodup s' := fun r hr hng => by
    change r ∈ fullArenaClauseRefs s' at hr; rw [hrefs] at hr
    change fullArenaClauseGarb s' r = false at hng
    rw [(hper r hr).2.1] at hng; change ((fullArenaClauseLits s' r).map (· / 2)).Nodup
    rw [(hper r hr).2.2]; exact hdw.2.2.2.1 r hr hng
  have hll' : FullLastLearnedWf s' := hdw.2.2.2.2.1.1.of_refs_subset rfl (fun r hr => hrefs ▸ hr)
  exact ⟨⟨hlen', hw', hdw.2.2.1, hnd', ⟨hll', hdw.2.2.2.2.1.2⟩,
    hdw.2.2.2.2.2.1, hdw.2.2.2.2.2.2⟩, hrefs, hper⟩

theorem fullDenseInvW_markGarb {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hdw : FullDenseInvW c F0 F_cur s) {cref : Nat}
    (href : cref ∈ fullArenaClauseRefs s) {arena' : List (BitVec 32)} {ag' : BitVec 64}
    (har_len : arena'.length = c.arena_cap)
    (hset : arena' = s.core.arena.set cref (fullArenaHdr s cref ||| 0x00080000#32)) :
    let s' : FullState := { s with core := { s.core with arena := arena', arena_garbage := ag' } }
    FullDenseInvW c F0 F_cur s' ∧ fullArenaClauseRefs s' = fullArenaClauseRefs s := by
  intro s'
  subst hset
  have hcl := hdw.1.core_ok
  have hw := hdw.2.1
  have hmg := hw.arena.markGarb hcl href ag'
  have hrefs : fullArenaClauseRefsCore s'.core = fullArenaClauseRefsCore s.core := hmg.1
  have hnonact : ∀ idx < s.core.trail_end,
      let rsn := s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32
      rsn ≠ 0xFFFFFFFF#32 → (rsn &&& 0x80000000#32) = 0#32 → rsn.toNat ≠ cref :=
    fun idx hidx hne _ _ => hne (hw.level0_rsn_none idx hidx (by
      have := hw.lvl_le idx hidx; have := hdw.2.2.2.2.2.1; omega))
  have har_lt : cref < s.core.arena.length := by
    have := (hw.arena.refs_wf cref href).1; have := hcl.arena_len_le
    have := hcl.arena_len_arr; omega
  have hdisj_lits : ∀ {r : Nat}, r ∈ fullArenaClauseRefsCore s.core → r ≠ cref →
      fullArenaClauseLitsCore s'.core r = fullArenaClauseLitsCore s.core r := fun {r} hr hne => by
    have hdisj : r + 3 + fullArenaClauseSizeCore s.core r ≤ cref ∨ cref + 3 ≤ r := by
      rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
      · exact Or.inl (hw.arena.disjoint hr href hlt)
      · exact Or.inr (by have := hw.arena.disjoint href hr hgt; omega)
    have hbd : r + 3 + fullArenaClauseSizeCore s.core r ≤ s.core.arena.length := by
      have := (hw.arena.refs_wf r hr).2.2.1; have := (hw.arena.refs_wf r hr).2.2.2.1
      have := hcl.arena_len_le; have := hcl.arena_len_arr; omega
    exact (fullArenaClauseLitsCore_set_outside hbd hdisj).2
  have hw' : FullWitnessInv c F0 F_cur s'.core :=
    { hw with
      arena := hmg.2
      watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun r hr => hrefs ▸ hr)
      reason_inv := fun idx hidx hne => by
        have hrs := hw.reason_inv idx hidx hne; dsimp only [s'] at hrs ⊢
        by_cases hbin : (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
            0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32
        · rw [ite_eq_left hbin] at hrs ⊢; exact hrs
        · have hlg' : (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
              0xFFFFFFFF#32 &&& 0x80000000#32) = 0#32 :=
            Classical.byContradiction fun h => hbin h
          rw [ite_eq_right hbin] at hrs ⊢
          have hne_c := hnonact idx hidx hne hlg'
          exact ⟨hrefs ▸ hrs.1, by
            unfold fullArenaClauseGarbCore fullArenaHdrCore
            rw [List.getElem?_set_ne hne_c.symm]; exact hrs.2.1,
            fun q hq => hrs.2.2 q (hdisj_lits hrs.1 hne_c ▸ hq)⟩
      reason_lit_mem := fun idx hidx hne hlg => by
        have hrs := hw.reason_inv idx hidx hne
        have hb : ¬ (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
            0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32 := fun h => absurd hlg h
        rw [ite_eq_right hb] at hrs
        exact hdisj_lits hrs.1 (hnonact idx hidx hne hlg) ▸ hw.reason_lit_mem idx hidx hne hlg }
  have hlen' : s'.LengthsOk c :=
    ⟨{ hcl with arena_len_arr := har_len }, hdw.1.scratch_ok⟩
  have hnd' : FullArenaVarsNodup s' :=
    FullArenaVarsNodup.of_markGarb ⟨hdw.1, F_cur, hw⟩ hdw.2.2.2.1 href ag'
  have hll' : FullLastLearnedWf s' := hdw.2.2.2.2.1.1.of_refs_subset rfl (fun r hr => by
    change r ∈ fullArenaClauseRefsCore s'.core; rw [hrefs]; exact hr)
  exact ⟨⟨hlen', hw', hdw.2.2.1, hnd', ⟨hll', hdw.2.2.2.2.1.2⟩,
    hdw.2.2.2.2.2.1, hdw.2.2.2.2.2.2⟩, hrefs⟩

theorem fullDenseInvW_with_prop {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hdw : FullDenseInvW c F0 F_cur s)
    {prop' : Nat} (hprop : prop' ≤ s.core.trail_end) :
    FullDenseInvW c F0 F_cur { s with core := { s.core with propagated := prop' } } := by
  refine ⟨⟨{ hdw.1.core_ok with propagated_le := hprop }, hdw.1.scratch_ok⟩,
    { hdw.2.1 with arena := { hdw.2.1.arena with len_ok := hdw.2.1.arena.len_ok },
                   watches := hdw.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) },
    hdw.2.2.1, hdw.2.2.2.1, hdw.2.2.2.2.1, hdw.2.2.2.2.2.1, hdw.2.2.2.2.2.2⟩

theorem fullDenseInvW_set_inc {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hdw : FullDenseInvW c F0 F_cur s)
    (huns : (cnfOfClauses F_cur).Unsat) :
    FullDenseInvW c F0 F_cur { s with core := { s.core with inconsistent := 1#64 } } :=
  ⟨⟨{ hdw.1.core_ok with vals_len := hdw.1.core_ok.vals_len }, hdw.1.scratch_ok⟩,
    { hdw.2.1 with
      arena := { hdw.2.1.arena with len_ok := hdw.2.1.arena.len_ok },
      watches := hdw.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r),
      inconsistent_sound := fun _ => huns },
    hdw.2.2.1, hdw.2.2.2.1, hdw.2.2.2.2.1, hdw.2.2.2.2.2.1, hdw.2.2.2.2.2.2⟩

theorem fullDenseInvW_with_oom {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hdw : FullDenseInvW c F0 F_cur s) (o' : BitVec 64) :
    FullDenseInvW c F0 F_cur { s with core := { s.core with oom := o' } } :=
  ⟨⟨{ hdw.1.core_ok with vals_len := hdw.1.core_ok.vals_len }, hdw.1.scratch_ok⟩,
    fullWitnessInv_with_oom hdw.2.1 o', hdw.2.2.1, hdw.2.2.2.1, hdw.2.2.2.2.1,
    hdw.2.2.2.2.2.1, hdw.2.2.2.2.2.2⟩

theorem fullDenseInvW_of_addUnit {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s s' : FullState} (hdw : FullDenseInvW c F0 F_cur s)
    (hlen' : s'.LengthsOk c) (hw' : FullWitnessInv c F0 F_cur s'.core)
    (hl0' : s'.core.cur_level = 0) (_hcv' : s'.core.cur_vars = s.core.cur_vars)
    (hdm' : s'.core.dense_mode = s.core.dense_mode)
    (hlm' : s'.core.lit_mark = s.core.lit_mark)
    (hmrk' : s'.core.mrk = s.core.mrk)
    (harena' : s'.core.arena = s.core.arena) (hal' : s'.core.arena_len = s.core.arena_len)
    (hll' : s'.scratch.last_learned = s.scratch.last_learned)
    (hext' : s'.scratch.extend_len = s.scratch.extend_len) :
    FullDenseInvW c F0 F_cur s' := by
  have hrefs' : fullArenaClauseRefs s' = fullArenaClauseRefs s := by
    unfold fullArenaClauseRefs fullArenaClauseRefsCore; rw [harena', hal']
  have hmc' : FullLitMarksClear c s' := by
    unfold FullLitMarksClear FullMrkZero; rw [hmrk', hlm']; exact hdw.2.2.1
  have hnd' : FullArenaVarsNodup s' := by
    unfold FullArenaVarsNodup fullArenaClauseRefs fullArenaClauseRefsCore
      fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
      fullArenaClauseLits fullArenaClauseLitsCore fullArenaClauseSizeCore
    rw [harena', hal']; exact hdw.2.2.2.1
  have hll_wf' : FullLastLearnedWf s' := fun i hi => by
    change s'.scratch.last_learned[i]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 ∨
      (s'.scratch.last_learned[i]?.getD 0xFFFFFFFF#32).toNat ∈ fullArenaClauseRefs s'
    rw [hll', hrefs']; exact hdw.2.2.2.2.1.1 i hi
  have hext_ok' : FullExtScratchOk c s' := ⟨hll_wf', by rw [hext']; exact hdw.2.2.2.2.1.2⟩
  exact ⟨hlen', hw', hmc', hnd', hext_ok', hl0', by rw [hdm']; exact hdw.2.2.2.2.2.2⟩

theorem fullDenseInvW_of_wstackDefrag {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hdw : FullDenseInvW c F0 F_cur s)
    {wvec' wstk' : List (BitVec 32)} {wlen' : Nat} {wu' : BitVec 64}
    (hlen' : ({ s with core := { s.core with wvec := wvec', wstk := wstk',
                                             wlen := wlen', wusable := wu' } } :
      FullState).LengthsOk c)
    (hwat' : ModeWatchesInv F_cur { s.core with wvec := wvec', wstk := wstk',
                                                wlen := wlen', wusable := wu' }) :
    FullDenseInvW c F0 F_cur { s with core := { s.core with wvec := wvec', wstk := wstk',
                                                            wlen := wlen', wusable := wu' } } :=
  ⟨hlen',
    { hdw.2.1 with arena := { hdw.2.1.arena with len_ok := hdw.2.1.arena.len_ok }
                   watches := hwat' },
    hdw.2.2.1, hdw.2.2.2.1, hdw.2.2.2.2.1, hdw.2.2.2.2.2.1, hdw.2.2.2.2.2.2⟩

theorem fullDenseInvW_of_shrink_watch {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hdw : FullDenseInvW c F0 F_cur s)
    {lit : Nat} (hlt : lit < 2 * s.core.cur_vars)
    {wvec' wstk' : List (BitVec 32)} {wu' : BitVec 64}
    (hwv_len : wvec'.length = 4 * c.max_vars)
    (hwst_len : wstk'.length = c.wcap)
    (hlay' : WatchStackLayout { s.core with wvec := wvec', wstk := wstk', wusable := wu' })
    (hoth : ∀ l < 2 * s.core.cur_vars, l ≠ lit →
      fullWatchSizeCore { s.core with wvec := wvec', wstk := wstk', wusable := wu' } l =
        fullWatchSize s l ∧
      ∀ i < fullWatchSize s l,
        let k' : FullCoreState := { s.core with wvec := wvec', wstk := wstk', wusable := wu' }
        wstk'[fullWatchOffCore k' l + i]? = s.core.wstk[fullWatchOff s l + i]?)
    (hlit_slice :
      let k' : FullCoreState := { s.core with wvec := wvec', wstk := wstk', wusable := wu' }
      DenseWatchSliceOk F_cur k' lit (fullWatchOffCore k' lit) (fullWatchSizeCore k' lit)) :
    FullDenseInvW c F0 F_cur
      { s with core := { s.core with wvec := wvec', wstk := wstk', wusable := wu' } } := by
  let s' : FullState :=
    { s with core := { s.core with wvec := wvec', wstk := wstk', wusable := wu' } }
  have hcl := hdw.1.core_ok
  have hlen' : s'.LengthsOk c :=
    ⟨{ hcl with wvec_len := hwv_len, wstk_len_arr := hwst_len }, hdw.1.scratch_ok⟩
  have hdw0 := dense_denseWatchesInv_of_w hdw
  have hent_refl : (cnfOfClauses F_cur).Entails (cnfOfClauses F_cur) := by
    rw [CNF.entails_def]; exact fun _ h => h
  have hdw' : DenseWatchesInv F_cur s'.core := by
    refine ⟨hlay', fun l hl => ?_⟩
    by_cases hle : l = lit
    · subst hle; exact hlit_slice
    · obtain ⟨hsz, hpre⟩ := hoth l hl hle
      change DenseWatchSliceOk F_cur s'.core l (fullWatchOffCore s'.core l)
        (fullWatchSizeCore s'.core l)
      rw [hsz]
      exact (hdw0.slices l hl).relocate (k := s.core) (k' := s'.core)
        (p := fullWatchOff s l) (p' := fullWatchOffCore s'.core l)
        hent_refl (Nat.le_refl _) (fun _ r => r)
        (fun i hi => by simpa [s'] using hpre i hi)
  have hwat' : ModeWatchesInv F_cur s'.core := by
    simp only [ModeWatchesInv, show s'.core.dense_mode = s.core.dense_mode from rfl,
      hdw.2.2.2.2.2.2, ↓reduceIte]
    exact hdw'
  exact ⟨hlen',
    { hdw.2.1 with
      arena := { hdw.2.1.arena with len_ok := hdw.2.1.arena.len_ok },
      watches := hwat' },
    hdw.2.2.1, hdw.2.2.2.1, hdw.2.2.2.2.1, hdw.2.2.2.2.2.1, hdw.2.2.2.2.2.2⟩

theorem fullDenseInvW_assignLvl0 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hdw : FullDenseInvW c F0 F_cur s)
    {lit : BitVec 32} (hlit : lit.toNat < 2 * s.core.cur_vars)
    (hun : s.core.vals[lit.toNat]?.getD 0#8 = 0#8)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [lit.toNat]))
    {flags' : List (BitVec 32)} (hfl_len : flags'.length = c.max_vars)
    (unass' unfl' : BitVec 64) :
    let v := lit.toNat / 2
    let s' : FullState :=
      { s with core :=
        { s.core with
          vals := (s.core.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8
          flags := flags'
          lvl := s.core.lvl.set v 0#32
          rsns := s.core.rsns.set v 0xFFFFFFFF#32
          trl := s.core.trl.set s.core.trail_end lit
          trail_pos := s.core.trail_pos.set v (BitVec.ofNat 32 s.core.trail_end)
          trail_end := s.core.trail_end + 1
          unassigned := unass'
          unflushed := unfl' } }
    FullDenseInvW c F0 F_cur s' := by
  intro v s'
  have hcl := hdw.1.core_ok
  have hw := hdw.2.1
  have hl0 : s.core.cur_level = 0 := hdw.2.2.2.2.2.1
  have hte_lt : s.core.trail_end < s.core.cur_vars := hw.trail_end_lt_of_unassigned hlit hun
  have hnot_var : ∀ i < s.core.trail_end, (s.core.trl[i]?.getD 0#32).toNat / 2 ≠ v :=
    (hw.vals_zero_iff hlit).mp hun
  have hnlit_lt : (lit.toNat ^^^ 1) < 2 * s.core.cur_vars := litNeg_lt_two_mul hlit
  have hne_lit : lit.toNat ^^^ 1 ≠ lit.toNat := litNeg_ne_self lit.toNat
  have hv_lt : v < c.max_vars := by have := hcl.cur_vars_le; omega
  have hte_max : s.core.trail_end < c.max_vars := by have := hcl.cur_vars_le; omega
  have hte_lt32 : s.core.trail_end < 2 ^ 32 := by have := fullInv_max_vars_lt32 c; omega
  have hlen' : s'.LengthsOk c :=
    ⟨{ hcl with
       vals_len := by simp [s', hcl.vals_len]
       flags_len := hfl_len
       lvl_len := by simp [s', hcl.lvl_len]
       rsns_len := by simp [s', hcl.rsns_len]
       trl_len := by simp [s', hcl.trl_len]
       trail_pos_len := by simp [s', hcl.trail_pos_len]
       trail_end_le := by dsimp [s']; omega
       propagated_le := by have := hcl.propagated_le; dsimp [s']; omega }, hdw.1.scratch_ok⟩
  have htrl_get : ∀ i < s.core.trail_end + 1,
      (s'.core.trl[i]?.getD 0#32).toNat =
        if i = s.core.trail_end then lit.toNat else (s.core.trl[i]?.getD 0#32).toNat :=
    fun i _ => by
      by_cases he : i = s.core.trail_end
      · subst he; simp [s', List.getElem?_set_self (by rw [hcl.trl_len]; exact hte_max)]
      · simp [s', he, List.getElem?_set_ne (Ne.symm he)]
  have hvals_get : ∀ l < 2 * s.core.cur_vars,
      s'.core.vals[l]?.getD 0#8 =
        if l = lit.toNat ^^^ 1 then 0xFF#8 else if l = lit.toNat then 1#8
        else s.core.vals[l]?.getD 0#8 := fun l hl => by
    have hcm := hcl.cur_vars_le
    by_cases hn : l = lit.toNat ^^^ 1
    · subst hn; simp only [↓reduceIte]; dsimp only [s']
      rw [List.getElem?_set_self (by rw [List.length_set, hcl.vals_len]; omega)]; rfl
    · simp only [hn, ↓reduceIte]
      by_cases hp : l = lit.toNat
      · subst hp; simp only [↓reduceIte]; dsimp only [s']
        rw [List.getElem?_set_ne (Ne.symm hn), List.getElem?_set_self (by rw [hcl.vals_len]; omega)]
        rfl
      · simp only [hp, ↓reduceIte]; dsimp only [s']
        rw [List.getElem?_set_ne (Ne.symm hn), List.getElem?_set_ne (Ne.symm hp)]
  have hlvl_zero : ∀ i < s.core.trail_end + 1,
      (s'.core.lvl[(s'.core.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := fun i hi => by
    rw [htrl_get i hi]; by_cases hie : i = s.core.trail_end
    · subst hie; simp only [↓reduceIte]; dsimp only [s', v]
      rw [List.getElem?_set_self (by rw [hcl.lvl_len]; exact hv_lt)]; rfl
    · have hilt : i < s.core.trail_end := by omega
      simp only [hie, ↓reduceIte]; dsimp only [s']
      rw [List.getElem?_set_ne (Ne.symm (hnot_var i hilt))]
      have := hw.lvl_le i hilt; omega
  have hrsn_all : ∀ i < s.core.trail_end + 1,
      s'.core.rsns[(s'.core.trl[i]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 =
        0xFFFFFFFF#32 := fun i hi => by
    rw [htrl_get i hi]; by_cases hie : i = s.core.trail_end
    · subst hie; simp only [↓reduceIte]; dsimp only [s', v]
      rw [List.getElem?_set_self (by rw [hcl.rsns_len]; exact hv_lt)]; rfl
    · have hilt : i < s.core.trail_end := by omega
      simp only [hie, ↓reduceIte]; dsimp only [s']
      rw [List.getElem?_set_ne (Ne.symm (hnot_var i hilt))]
      exact hw.level0_rsn_none i hilt (by have := hw.lvl_le i hilt; omega)
  have hw' : FullWitnessInv c F0 F_cur s'.core :=
    { ext_sound := hw.ext_sound
      inconsistent_sound := hw.inconsistent_sound
      arena := { hw.arena with len_ok := hw.arena.len_ok }
      watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r)
      cur_level_le := by rw [show s'.core.cur_level = 0 from hl0]; omega
      trail_lits_lt := fun i hi => by
        change i < s.core.trail_end + 1 at hi
        rw [htrl_get i hi]; split
        · exact hlit
        · exact hw.trail_lits_lt i (by omega)
      trail_vars_nodup := fun i j hi hj hdv => by
        change i < s.core.trail_end + 1 at hi; change j < s.core.trail_end + 1 at hj
        rw [htrl_get i hi, htrl_get j hj] at hdv
        by_cases hie : i = s.core.trail_end
        · by_cases hje : j = s.core.trail_end
          · exact hie.trans hje.symm
          · simp [hie, hje] at hdv; exact absurd hdv.symm (hnot_var j (by omega))
        · by_cases hje : j = s.core.trail_end
          · simp [hie, hje] at hdv; exact absurd hdv (hnot_var i (by omega))
          · simp [hie, hje] at hdv; exact hw.trail_vars_nodup i j (by omega) (by omega) hdv
      vals_domain := fun l hl => by
        rw [hvals_get l hl]
        by_cases hn : l = lit.toNat ^^^ 1
        · simp [hn]
        · simp only [hn, ↓reduceIte]
          by_cases hp : l = lit.toNat
          · simp [hp]
          · simp only [hp, ↓reduceIte]; exact hw.vals_domain l hl
      vals_true_iff := fun l hl => by
        rw [hvals_get l hl]; dsimp only [s']; constructor
        · intro h1; by_cases hn : l = lit.toNat ^^^ 1
          · simp [hn] at h1
          · simp only [hn, ↓reduceIte] at h1; by_cases hp : l = lit.toNat
            · exact ⟨s.core.trail_end, by omega, by rw [htrl_get _ (by omega)]; simp [hp]⟩
            · simp only [hp, ↓reduceIte] at h1
              obtain ⟨i, hi, heq⟩ := (hw.vals_true_iff l hl).mp h1
              exact ⟨i, by omega,
                by rw [htrl_get i (by omega)]; simp [show i ≠ s.core.trail_end by omega, heq]⟩
        · rintro ⟨i, hi, heq⟩; change i < s.core.trail_end + 1 at hi; rw [htrl_get i hi] at heq
          by_cases hie : i = s.core.trail_end
          · simp only [hie, ↓reduceIte] at heq; subst heq; simp [Ne.symm hne_lit]
          · simp only [hie, ↓reduceIte] at heq
            have hlv : l / 2 ≠ v := by rw [← heq]; exact hnot_var i (by omega)
            have h1 : l ≠ lit.toNat ^^^ 1 := fun h => hlv (by rw [h, fullInv_var_xor1])
            have h2 : l ≠ lit.toNat := fun h => hlv (by rw [h])
            simp only [h1, h2, ↓reduceIte]; exact (hw.vals_true_iff l hl).mpr ⟨i, by omega, heq⟩
      vals_false_iff := fun l hl => by
        rw [hvals_get l hl]; dsimp only [s']; constructor
        · intro h1; by_cases hn : l = lit.toNat ^^^ 1
          · exact ⟨s.core.trail_end, by omega, by
              rw [htrl_get _ (by omega)]; simp only [↓reduceIte, hn]; exact (litNeg_litNeg _).symm⟩
          · simp only [hn, ↓reduceIte] at h1; by_cases hp : l = lit.toNat
            · simp [hp] at h1
            · simp only [hp, ↓reduceIte] at h1
              obtain ⟨i, hi, heq⟩ := (hw.vals_false_iff l hl).mp h1
              exact ⟨i, by omega,
                by rw [htrl_get i (by omega)]; simp [show i ≠ s.core.trail_end by omega, heq]⟩
        · rintro ⟨i, hi, heq⟩; change i < s.core.trail_end + 1 at hi; rw [htrl_get i hi] at heq
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
        change i < s.core.trail_end + 1 at hi; rw [hlvl_zero i hi]; omega
      dec_earliest := fun _ j _ hj _ _ => by
        exfalso; change j < s.core.trail_end + 1 at hj; have := hlvl_zero j hj; omega
      levels_inhabited := fun L hL1 hLle => by
        rw [show s'.core.cur_level = 0 from hl0] at hLle; omega
      level0_sound := fun i hi _ => by
        change i < s.core.trail_end + 1 at hi; rw [htrl_get i hi]; split
        · exact hent
        · rename_i hne; exact hw.level0_sound i (by omega)
            (by have := hw.lvl_le i (by omega); omega)
      trail_pos_inv := fun i hi => by
        change i < s.core.trail_end + 1 at hi
        rw [htrl_get i hi]; by_cases hie : i = s.core.trail_end
        · subst hie; simp only [↓reduceIte]; dsimp only [s', v]
          rw [List.getElem?_set_self (by rw [hcl.trail_pos_len]; exact hv_lt),
            Option.getD_some, bv32_ofNat_toNat hte_lt32]
        · have hilt : i < s.core.trail_end := by omega
          simp only [hie, ↓reduceIte]; dsimp only [s']
          rw [List.getElem?_set_ne (Ne.symm (hnot_var i hilt))]; exact hw.trail_pos_inv i hilt
      level0_rsn_none := fun idx hidx _ => hrsn_all idx hidx
      frame_trail_lt := fun L hL => by
        have : L = 0 := by rw [show s'.core.cur_level = 0 from hl0] at hL; omega
        subst this; have := hw.frame_trail_lt 0 (by omega); dsimp only [s']; omega
      frame_trail_mono := fun L1 L2 h12 h2 => by
        rw [show s'.core.cur_level = 0 from hl0] at h2
        exact hw.frame_trail_mono L1 L2 h12 (by omega)
      frame_trail_before_lt := fun L hL1 hL2 => by
        rw [show s'.core.cur_level = 0 from hl0] at hL2; omega
      frame_dec_lt := fun L hL1 hL2 => by
        rw [show s'.core.cur_level = 0 from hl0] at hL2; omega
      reason_inv := fun idx hidx hne => absurd (hrsn_all idx hidx) hne
      reason_lit_mem := fun idx hidx hne => absurd (hrsn_all idx hidx) hne }
  exact ⟨hlen', hw', hdw.2.2.1, hdw.2.2.2.1, hdw.2.2.2.2.1, hl0, hdw.2.2.2.2.2.2⟩

end LeanQbe.T.Examples.Kissat.Proof.Dense
