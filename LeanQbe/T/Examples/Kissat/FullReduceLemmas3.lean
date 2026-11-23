/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullReduceLemmas2
import all Kraken.Mem
import all Kraken.Separation

/-!
# Stage-4 (`D-Full`) GC / Sweep `Func.wp` Proofs — Part 3 (`full_sweep_copy`, `full_rewatch_arena`)

Pure compaction, body-swap, trail-reason uniqueness, and level-0 unit-assignment preservation
lemmas, followed by `Func.wp` proofs for:
8. `full_sweep_copy` (`Full1.lean:1202-1243`)
9. `full_rewatch_arena` (`Full2.lean:106-147`)
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.C0Step
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test
open LeanQbe.T.Examples.Kissat.Full.FullReduceSpecs
open LeanQbe.T.Examples.Kissat.Full.FullReduceHelpers
open scoped FullArenaTactics FullReduceTactics

/-! ## 1. Swap, level-0 unit-assignment, & compaction helpers (`FullReduceHelpers`) -/

namespace FullReduceHelpers

private theorem list_set_swap_perm_lt {α : Type} (xs : List α) {a b : Nat}
    (hab : a < b) (hb : b < xs.length) :
    List.Perm ((xs.set a (xs[b]'hb)).set b (xs[a]'(by omega))) xs := by
  let pre := xs.take a; let mid := (xs.drop (a + 1)).take (b - a - 1); let suf := xs.drop (b + 1)
  have hpre : pre.length = a := by simp [pre]; omega
  have hmid : mid.length = b - a - 1 := by simp [mid]; omega
  have hsuf : suf.length = xs.length - (b + 1) := by simp [suf]
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
              show b + 1 + (j - (pre ++ x :: (mid ++ [y])).length) = j by simp [hpre, hmid]; omega]
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

private theorem list_set_swap_perm {α : Type} (xs : List α) {a b : Nat}
    (ha : a < xs.length) (hb : b < xs.length) :
    List.Perm ((xs.set a (xs[b]'hb)).set b (xs[a]'ha)) xs := by
  rcases lt_trichotomy a b with hlt | rfl | hgt
  · exact list_set_swap_perm_lt xs hlt hb
  · rw [show (xs.set a (xs[a]'ha)).set a (xs[a]'ha) = xs from List.ext_getElem (by simp)
      fun j _ _ => by
        by_cases hj : j = a
        · subst hj; simp
        · rw [List.getElem_set_ne (Ne.symm hj), List.getElem_set_ne (Ne.symm hj)]]
  · rw [show (xs.set a (xs[b]'hb)).set b (xs[a]'ha) =
        (xs.set b (xs[a]'ha)).set a (xs[b]'hb) from List.ext_getElem (by simp) fun j _ _ => by
      by_cases hjb : j = b
      · subst hjb; rw [List.getElem_set_self (by simp; omega), List.getElem_set_ne (by omega),
          List.getElem_set_self (by simp; omega)]
      · by_cases hja : j = a
        · subst hja
          rw [List.getElem_set_ne (Ne.symm hjb), List.getElem_set_self (by simp; omega),
            List.getElem_set_self (by simp; omega)]
        · rw [List.getElem_set_ne (Ne.symm hjb), List.getElem_set_ne (Ne.symm hja),
            List.getElem_set_ne (Ne.symm hja), List.getElem_set_ne (Ne.symm hjb)]]
    exact list_set_swap_perm_lt xs hgt ha

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
  exact (list_set_swap_perm ((ar.drop (p + 3)).take sz) (by omega) (by omega)).map BitVec.toNat

/-- Level-0 unit assignment (`full_assign_lvl` with `alvl = 0`) preserving `FullWitnessInv` for
the SAME `F_cur` (used by `full_sweep_copy` on `{ s.core with arena_len := dst }`). -/
theorem level0Assign_preserves_witness {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hlen : k.LengthsOk c) (hw : FullWitnessInv c F0 F_cur k)
    (hcl0 : k.cur_level = 0) {lit : BitVec 32} (hlit : lit.toNat < 2 * k.cur_vars)
    (hun : k.vals[lit.toNat]?.getD 0#8 = 0#8)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [lit.toNat]))
    (flags' : List (BitVec 32)) (unass' unfl' : BitVec 64) :
    let v := lit.toNat / 2
    let k' : FullCoreState :=
      { k with
        vals := (k.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8
        flags := flags'
        lvl := k.lvl.set v 0#32
        rsns := k.rsns.set v 0xFFFFFFFF#32
        trl := k.trl.set k.trail_end lit
        trail_pos := k.trail_pos.set v (BitVec.ofNat 32 k.trail_end)
        trail_end := k.trail_end + 1
        unassigned := unass', unflushed := unfl' }
    FullWitnessInv c F0 F_cur k' := by
  intro v k'
  have hte_lt : k.trail_end < k.cur_vars := hw.trail_end_lt_of_unassigned hlit hun
  have hnot_var : ∀ i < k.trail_end, (k.trl[i]?.getD 0#32).toNat / 2 ≠ v :=
    (hw.vals_zero_iff hlit).mp hun
  have hnlit_lt : (lit.toNat ^^^ 1) < 2 * k.cur_vars := litNeg_lt_two_mul hlit
  have hne_lit : lit.toNat ^^^ 1 ≠ lit.toNat := litNeg_ne_self lit.toNat
  have hv_lt : v < c.max_vars := by have := hlen.cur_vars_le; omega
  have hte_max : k.trail_end < c.max_vars := by have := hlen.cur_vars_le; omega
  have hte_lt32 : k.trail_end < 2 ^ 32 := by have := fullInv_max_vars_lt32 c; omega
  have htrl_get : ∀ i < k.trail_end + 1,
      (k'.trl[i]?.getD 0#32).toNat =
        if i = k.trail_end then lit.toNat else (k.trl[i]?.getD 0#32).toNat := fun i _ => by
    by_cases he : i = k.trail_end
    · subst he; simp [k', List.getElem?_set_self (by rw [hlen.trl_len]; exact hte_max)]
    · simp [k', he, List.getElem?_set_ne (Ne.symm he)]
  have hlvl_zero : ∀ i < k.trail_end + 1,
      (k'.lvl[(k'.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := fun i hi => by
    rw [htrl_get i hi]; by_cases hie : i = k.trail_end
    · subst hie; simp only [↓reduceIte]; dsimp only [k', v]
      rw [List.getElem?_set_self (by rw [hlen.lvl_len]; exact hv_lt)]; rfl
    · have hilt : i < k.trail_end := by omega
      simp only [hie, ↓reduceIte]; dsimp only [k']
      rw [List.getElem?_set_ne (Ne.symm (hnot_var i hilt))]
      have := hw.lvl_le i hilt; omega
  have hrsn_all : ∀ i < k.trail_end + 1,
      k'.rsns[(k'.trl[i]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 :=
    fun i hi => by
      rw [htrl_get i hi]; by_cases hie : i = k.trail_end
      · subst hie; simp only [↓reduceIte]; dsimp only [k', v]
        rw [List.getElem?_set_self (by rw [hlen.rsns_len]; exact hv_lt)]; rfl
      · have hilt : i < k.trail_end := by omega
        simp only [hie, ↓reduceIte]; dsimp only [k']
        rw [List.getElem?_set_ne (Ne.symm (hnot_var i hilt))]
        exact hw.level0_rsn_none i hilt (by have := hw.lvl_le i hilt; omega)
  have hvals_get : ∀ l < 2 * k.cur_vars,
      k'.vals[l]?.getD 0#8 =
        if l = lit.toNat ^^^ 1 then 0xFF#8 else if l = lit.toNat then 1#8
        else k.vals[l]?.getD 0#8 := fun l hl => by
    have hcm := hlen.cur_vars_le
    by_cases h1 : l = lit.toNat ^^^ 1
    · subst h1; dsimp only [k']; simp only [↓reduceIte]
      rw [List.getElem?_set_self (by simp [hlen.vals_len]; omega)]; rfl
    · dsimp only [k']; simp only [h1, ↓reduceIte]; rw [List.getElem?_set_ne (Ne.symm h1)]
      by_cases h2 : l = lit.toNat
      · subst h2; simp only [↓reduceIte]
        rw [List.getElem?_set_self (by rw [hlen.vals_len]; omega)]; rfl
      · simp only [h2, ↓reduceIte]; rw [List.getElem?_set_ne (Ne.symm h2)]
  refine {
    ext_sound := hw.ext_sound, inconsistent_sound := hw.inconsistent_sound
    arena := { hw.arena with len_ok := hw.arena.len_ok }
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr)
    cur_level_le := by dsimp [k']; omega
    trail_lits_lt := fun i hi => by
      rw [htrl_get i hi]; split
      · exact hlit
      · exact hw.trail_lits_lt i (by dsimp [k'] at hi; omega)
    trail_vars_nodup := fun i j hi hj hveq => by
      dsimp only [k'] at hi hj
      rw [htrl_get i hi, htrl_get j hj] at hveq
      split at hveq <;> split at hveq
      · omega
      · exact absurd hveq.symm (hnot_var j (by omega))
      · exact absurd hveq (hnot_var i (by omega))
      · exact hw.trail_vars_nodup i j (by omega) (by omega) hveq
    vals_domain := fun l hl => by
      rw [hvals_get l hl]; split; · exact Or.inr (Or.inr rfl)
      split; · exact Or.inr (Or.inl rfl)
      exact hw.vals_domain l hl
    vals_true_iff := fun l hl => by
      rw [hvals_get l hl]; dsimp only [k']; constructor
      · intro h1; by_cases hneg : l = lit.toNat ^^^ 1
        · simp [hneg] at h1
        · simp only [hneg, ↓reduceIte] at h1; by_cases hpos : l = lit.toNat
          · exact ⟨k.trail_end, by omega, by rw [htrl_get _ (by omega)]; simp [hpos]⟩
          · simp only [hpos, ↓reduceIte] at h1
            obtain ⟨i, hi, heq⟩ := (hw.vals_true_iff l hl).mp h1
            exact ⟨i, by omega,
              by rw [htrl_get i (by omega)]; simp [show i ≠ k.trail_end by omega, heq]⟩
      · rintro ⟨i, hi, heq⟩; rw [htrl_get i hi] at heq
        by_cases hie : i = k.trail_end
        · simp only [hie, ↓reduceIte] at heq; subst heq; simp [Ne.symm hne_lit]
        · simp only [hie, ↓reduceIte] at heq
          have hlv : l / 2 ≠ v := by rw [← heq]; exact hnot_var i (by omega)
          have h1 : l ≠ lit.toNat ^^^ 1 := fun h => hlv (by rw [h, fullInv_var_xor1])
          have h2 : l ≠ lit.toNat := fun h => hlv (by rw [h])
          simp only [h1, h2, ↓reduceIte]; exact (hw.vals_true_iff l hl).mpr ⟨i, by omega, heq⟩
    vals_false_iff := fun l hl => by
      rw [hvals_get l hl]; dsimp only [k']; constructor
      · intro h1; by_cases hneg : l = lit.toNat ^^^ 1
        · exact ⟨k.trail_end, by omega, by
            rw [htrl_get _ (by omega)]; simp only [↓reduceIte, hneg]; exact (litNeg_litNeg _).symm⟩
        · simp only [hneg, ↓reduceIte] at h1; by_cases hpos : l = lit.toNat
          · simp [hpos] at h1
          · simp only [hpos, ↓reduceIte] at h1
            obtain ⟨i, hi, heq⟩ := (hw.vals_false_iff l hl).mp h1
            exact ⟨i, by omega,
              by rw [htrl_get i (by omega)]; simp [show i ≠ k.trail_end by omega, heq]⟩
      · rintro ⟨i, hi, heq⟩; rw [htrl_get i hi] at heq
        by_cases hie : i = k.trail_end
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
    lvl_le := fun i hi => by rw [hlvl_zero i hi]; omega
    dec_earliest := fun _ j _ hj _ hdec => by rw [hlvl_zero j hj] at hdec; omega
    levels_inhabited := fun _ hL1 hLle => by dsimp [k'] at hLle; omega
    level0_sound := fun i hi _ => by
      dsimp only [k'] at hi; rw [htrl_get i hi]
      by_cases hie : i = k.trail_end
      · simp only [hie, ↓reduceIte]; exact hent
      · simp only [hie, ↓reduceIte]
        exact hw.level0_sound i (by omega) (by have := hw.lvl_le i (by omega); omega)
    trail_pos_inv := fun i hi => by
      dsimp only [k'] at hi; rw [htrl_get i hi]
      by_cases hie : i = k.trail_end
      · subst hie; simp only [↓reduceIte]; dsimp only [k', v]
        rw [List.getElem?_set_self (by rw [hlen.trail_pos_len]; exact hv_lt),
          Option.getD_some, bv32_ofNat_toNat hte_lt32]
      · simp only [hie, ↓reduceIte]; dsimp only [k']
        rw [List.getElem?_set_ne (Ne.symm (hnot_var i (by omega)))]
        exact hw.trail_pos_inv i (by omega)
    level0_rsn_none := fun idx hidx _ => hrsn_all idx hidx
    frame_trail_lt := fun L hL => by
      have := hw.frame_trail_lt L hL; dsimp only [k']; omega
    frame_trail_mono := fun L1 L2 h1 h2 => hw.frame_trail_mono L1 L2 h1 h2
    frame_trail_before_lt := fun _ hL1 hLle => by dsimp [k'] at hLle; omega
    frame_dec_lt := fun _ hL1 hLle => by dsimp [k'] at hLle; omega
    reason_inv := fun idx hidx hne => absurd (hrsn_all idx hidx) hne
    reason_lit_mem := fun idx hidx hne => absurd (hrsn_all idx hidx) hne }

theorem level0_entails_of_filter {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) {orig kept : List Nat}
    (horig : (cnfOfClauses F_cur).EntailsClause (cnfClause orig))
    (hdrop : ∀ l ∈ orig, l ∈ kept ∨
      (l < 2 * k.cur_vars ∧ (k.lvl[l / 2]?.getD 0#32).toNat = 0 ∧ k.vals[l]?.getD 0#8 = 0xFF#8)) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause kept) := by
  refine entails_of_mem_or_false horig fun l hl => ?_
  rcases hdrop l hl with hin | ⟨hlt, hl0, hff⟩
  · exact Or.inl hin
  · right; obtain ⟨i, hi, hieq⟩ := (hw.vals_false_iff l hlt).mp hff
    have hvar : (k.trl[i]?.getD 0#32).toNat / 2 = l / 2 := by rw [hieq]; exact fullInv_var_xor1 l
    have hs := hw.level0_sound i hi (by rw [hvar]; exact hl0); rwa [hieq] at hs

theorem level0_unsat_of_entails_nil {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k)
    (hnil : (cnfOfClauses F_cur).EntailsClause (cnfClause [])) : F0.Unsat :=
  hw.ext_sound.2 (unsat_of_entails_nil hnil)

theorem level0_unsat_of_unit_false {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (hcl0 : k.cur_level = 0)
    {l : Nat} (hlt : l < 2 * k.cur_vars)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [l]))
    (hff : k.vals[l]?.getD 0#8 = 0xFF#8) : F0.Unsat := by
  refine level0_unsat_of_entails_nil hw (level0_entails_of_filter hw hent fun q hq => Or.inr ?_)
  simp only [List.mem_singleton] at hq; subst hq
  obtain ⟨i, hi, hieq⟩ := (hw.vals_false_iff q hlt).mp hff
  have hvar : (k.trl[i]?.getD 0#32).toNat / 2 = q / 2 := by rw [hieq]; exact fullInv_var_xor1 q
  exact ⟨hlt, by have := hw.lvl_le i hi; rw [hvar] at this; omega, hff⟩

end FullReduceHelpers

private theorem sweep_copy_witness_with_ar {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {dst : Nat} {ar' : List (BitVec 32)}
    (har_len : s.core.arena.length = c.arena_cap) (hdst_le : dst ≤ c.arena_cap)
    (hcl0 : s.core.cur_level = 0)
    (hw_dst : FullWitnessInv c F0 F_cur { s.core with arena_len := dst })
    (har' : ar'.length = c.arena_cap) (hpre : PrefixAgrees dst s.core.arena ar') :
    FullWitnessInv c F0 F_cur { s.core with arena := ar', arena_len := dst } := by
  let k0 : FullCoreState := { s.core with arena_len := dst }
  let k1 : FullCoreState := { s.core with arena := ar', arena_len := dst }
  have hnxt : ∀ r ∈ fullArenaClauseRefsCore k0,
      fullArenaNextOff k1.arena k0.arena_len r = fullArenaNextOff k0.arena k0.arena_len r :=
    fun r hr => hw_dst.arena.arenaNextOff_extend (Nat.le_refl _) (fun i hi => hpre i hi) r hr
  have hrefs : fullArenaClauseRefsCore k1 = fullArenaClauseRefsCore k0 :=
    fullArenaClauseRefsCore_congr rfl hnxt
  have hmeta : ∀ r ∈ fullArenaClauseRefsCore k0,
      fullArenaHdrCore k1 r = fullArenaHdrCore k0 r ∧
      fullArenaClauseSizeCore k1 r = fullArenaClauseSizeCore k0 r ∧
      fullArenaClauseGarbCore k1 r = fullArenaClauseGarbCore k0 r ∧
      fullArenaClauseLitsCore k1 r = fullArenaClauseLitsCore k0 r := fun r hr => by
    have hwf := hw_dst.arena.refs_wf r hr
    have h1 : r + 3 + fullArenaClauseSizeCore k0 r ≤ fullArenaNextOff k0.arena dst r := hwf.2.2.1
    have h3 : fullArenaNextOff k0.arena dst r ≤ dst := hwf.2.2.2.1
    have hk0_len : k0.arena.length = c.arena_cap := har_len
    have hk1_len : k1.arena.length = c.arena_cap := har'
    have h0 := hpre r (by omega); have h2 := hpre (r + 2) (by omega)
    have hsz : fullArenaClauseSizeCore k1 r = fullArenaClauseSizeCore k0 r := by
      unfold fullArenaClauseSizeCore k1 k0; rw [h2]
    refine ⟨by unfold fullArenaHdrCore k1 k0; rw [h0], hsz,
      by unfold fullArenaClauseGarbCore fullArenaHdrCore k1 k0; rw [h0],
      fullArenaClauseLitsCore_eq_of_hold (by omega) (by omega) hsz
        fun j hj => hpre (r + 3 + j) (by omega)⟩
  have harena1 : FullArenaClausesInv c F_cur k1 := by
    refine ⟨hw_dst.arena.len_ok, ?_, ?_, ?_, ?_⟩
    · intro r hr; rw [hrefs] at hr; have h := hw_dst.arena.refs_wf r hr
      dsimp only [k1, k0] at hnxt h ⊢; rw [hnxt r hr, (hmeta r hr).2.1]; exact h
    · intro r hr hsh; rw [hrefs] at hr; rw [(hmeta r hr).1] at hsh
      obtain ⟨t, ht1, ht2, hsent⟩ := hw_dst.arena.shrk_term r hr hsh
      dsimp only [k0] at ht2
      exact ⟨t, by rw [(hmeta r hr).2.1]; exact ht1, ht2,
        by dsimp only [k1]; rw [hpre t ht2]; exact hsent⟩
    · intro r hr hng l hl; rw [hrefs] at hr
      rw [(hmeta r hr).2.2.1] at hng; rw [(hmeta r hr).2.2.2] at hl
      exact hw_dst.arena.lits_lt r hr hng l hl
    · intro r hr hng; rw [hrefs] at hr
      rw [(hmeta r hr).2.2.1] at hng; rw [(hmeta r hr).2.2.2]
      exact hw_dst.arena.entails r hr hng
  exact { hw_dst with
    arena := harena1
    watches := hw_dst.watches.with_wstk rfl rfl rfl rfl rfl (fun r hr => hrefs ▸ hr)
    reason_inv := fun idx hidx hne => absurd (hw_dst.level0_rsn_none idx hidx
      (by have := hw_dst.lvl_le idx hidx; change _ ≤ s.core.cur_level at this; omega)) hne
    reason_lit_mem := fun idx hidx hne => absurd (hw_dst.level0_rsn_none idx hidx
      (by have := hw_dst.lvl_le idx hidx; change _ ≤ s.core.cur_level at this; omega)) hne }

private theorem fullWitnessInv_with_binWatches {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {k : FullCoreState} {arL wvec' wstk' : List (BitVec 32)}
    {dst wlen' : Nat} {wu' nb' oom' : BitVec 64}
    (hw : FullWitnessInv c F0 F_cur { k with arena := arL, arena_len := dst })
    (hbin : BinOnlyWatchesInv F_cur
      { k with arena := arL, wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu',
               num_binary := nb', oom := oom' }) :
    FullWitnessInv c F0 F_cur
      { k with arena := arL, arena_len := dst, wvec := wvec', wstk := wstk', wlen := wlen',
               wusable := wu', num_binary := nb', oom := oom' } :=
  { hw with
    arena := { hw.arena with len_ok := hw.arena.len_ok }
    watches := (hbin.with_core
      (k' := { k with arena := arL, arena_len := dst, wvec := wvec', wstk := wstk',
                      wlen := wlen', wusable := wu', num_binary := nb', oom := oom' })
      rfl rfl rfl rfl).toModeWatchesInv }

private theorem sweep_copy_new1_prep {F_cur : List (List Nat)} {arL : List (BitVec 32)}
    {dst : BitVec 64} {cur_vars : Nat}
    (hd3_eq : (dst + (3 : BitVec 64)).toNat = dst.toNat + 3)
    (hd3_lt : (dst + (3 : BitVec 64)).toNat < arL.length)
    (hlt0 : (arL[dst.toNat + 3 + 0]?.getD 0#32).toNat < 2 * cur_vars)
    (hent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause (((arL.drop (dst.toNat + 3)).take 1).map BitVec.toNat))) :
    let ulit := arL[(dst + (3 : BitVec 64)).toNat]'hd3_lt
    ulit = arL[dst.toNat + 3]'(by omega) ∧ ulit.toNat < 2 * cur_vars ∧
    (cnfOfClauses F_cur).EntailsClause (cnfClause [ulit.toNat]) := by
  intro ulit
  have hulit_eq : ulit = arL[dst.toNat + 3]'(by omega) := by dsimp only [ulit]; simp only [hd3_eq]
  refine ⟨hulit_eq, ?_, ?_⟩
  · rw [Nat.add_zero, List.getElem?_eq_getElem (by omega : dst.toNat + 3 < arL.length),
      Option.getD_some, ← hulit_eq] at hlt0; exact hlt0
  · rw [show (1 : Nat) = 0 + 1 from rfl,
      drop_take_succ (by omega : dst.toNat + 3 + 0 < arL.length)] at hent
    simpa [hulit_eq] using hent

private theorem sweep_copy_new2_prep {F_cur : List (List Nat)} {arL : List (BitVec 32)}
    {dst : BitVec 64} {cur_vars : Nat}
    (hcv_lt : cur_vars < 2 * 2 ^ 28)
    (hd3_eq : (dst + (3 : BitVec 64)).toNat = dst.toNat + 3)
    (hd4_eq : (dst + (4 : BitVec 64)).toNat = dst.toNat + 4)
    (hd3_lt : (dst + (3 : BitVec 64)).toNat < arL.length)
    (hd4_lt : (dst + (4 : BitVec 64)).toNat < arL.length)
    (hlt0 : (arL[dst.toNat + 3 + 0]?.getD 0#32).toNat < 2 * cur_vars)
    (hlt1 : (arL[dst.toNat + 3 + 1]?.getD 0#32).toNat < 2 * cur_vars)
    (hent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause (((arL.drop (dst.toNat + 3)).take 2).map BitVec.toNat))) :
    let l0 := arL[(dst + (3 : BitVec 64)).toNat]'hd3_lt
    let l1 := arL[(dst + (4 : BitVec 64)).toNat]'hd4_lt
    l0.toNat < 2 * cur_vars ∧ l1.toNat < 2 * cur_vars ∧
    (cnfOfClauses F_cur).EntailsClause (cnfClause [l0.toNat, l1.toNat]) ∧
    (cnfOfClauses F_cur).EntailsClause (cnfClause [l1.toNat, l0.toNat]) ∧
    l0.toNat < 0x7FFFFFFF ∧ l1.toNat < 0x7FFFFFFF := by
  intro l0 l1
  have hl0_eq : l0 = arL[dst.toNat + 3]'(by omega) := by dsimp only [l0]; simp only [hd3_eq]
  have hl1_eq : l1 = arL[dst.toNat + 4]'(by omega) := by dsimp only [l1]; simp only [hd4_eq]
  have hl0_lt : l0.toNat < 2 * cur_vars := by
    rw [Nat.add_zero, List.getElem?_eq_getElem (by omega : dst.toNat + 3 < arL.length),
      Option.getD_some, ← hl0_eq] at hlt0; exact hlt0
  have hl1_lt : l1.toNat < 2 * cur_vars := by
    rw [show dst.toNat + 3 + 1 = dst.toNat + 4 by omega,
      List.getElem?_eq_getElem (by omega : dst.toNat + 4 < arL.length),
      Option.getD_some, ← hl1_eq] at hlt1; exact hlt1
  have hent_01 : (cnfOfClauses F_cur).EntailsClause (cnfClause [l0.toNat, l1.toNat]) := by
    have htk : (arL.drop (dst.toNat + 3)).take 2 = [l0, l1] := by
      apply List.ext_getElem (by simp; omega)
      intro j hj1 _; have hj : j < 2 := by simp at hj1; omega
      simp only [List.getElem_take, List.getElem_drop]
      match j, hj with
      | 0, _ => simp [hl0_eq]
      | 1, _ => simp [hl1_eq, show dst.toNat + 3 + 1 = dst.toNat + 4 by omega]
    rw [htk] at hent; simpa using hent
  have hent_10 : (cnfOfClauses F_cur).EntailsClause (cnfClause [l1.toNat, l0.toNat]) :=
    entails_of_mem_or_false hent_01 fun q hq =>
      Or.inl (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hq ⊢
                 rcases hq with rfl | rfl <;> simp)
  exact ⟨hl0_lt, hl1_lt, hent_01, hent_10, by omega, by omega⟩

private theorem sweep_copy_keep_inv {c : FullCfg} {s : FullState} {src dst : BitVec 64}
    {new_sz i : BitVec 32} {arL : List (BitVec 32)} {lit : BitVec 32}
    (harL : arL.length = c.arena_cap)
    (hdst_idx : (dst + (3 : BitVec 64) + new_sz.setWidth 64).toNat = dst.toNat + 3 + new_sz.toNat)
    (hdst_lt : (dst + (3 : BitVec 64) + new_sz.setWidth 64).toNat < arL.length)
    (hnsz1_eq : (new_sz + (1 : BitVec 32)).toNat = new_sz.toNat + 1)
    (hlit_cv : lit.toNat < 2 * s.core.cur_vars)
    (houtL : OutsideSliceAgrees (dst.toNat + 3) (dst.toNat + 3 + new_sz.toNat) s.core.arena arL)
    (hltL : ∀ j < new_sz.toNat, (arL[dst.toNat + 3 + j]?.getD 0#32).toNat < 2 * s.core.cur_vars)
    (hsubL : List.Sublist (((arL.drop (dst.toNat + 3)).take new_sz.toNat).map BitVec.toNat)
      (((s.core.arena.drop (src.toNat + 3)).take i.toNat).map BitVec.toNat))
    (hdropL : ∀ l ∈ ((s.core.arena.drop (src.toNat + 3)).take i.toNat).map BitVec.toNat,
      l ∈ ((arL.drop (dst.toNat + 3)).take new_sz.toNat).map BitVec.toNat ∨
        (l < 2 * s.core.cur_vars ∧ (s.core.lvl[l / 2]?.getD 0#32).toNat = 0 ∧
          s.core.vals[l]?.getD 0#8 = 0xFF#8))
    (horig_succ : ((s.core.arena.drop (src.toNat + 3)).take (i.toNat + 1)).map BitVec.toNat =
      ((s.core.arena.drop (src.toNat + 3)).take i.toNat).map BitVec.toNat ++ [lit.toNat]) :
    let ar' := arL.set (dst + (3 : BitVec 64) + new_sz.setWidth 64).toNat lit
    ar'.length = c.arena_cap ∧
    OutsideSliceAgrees (dst.toNat + 3) (dst.toNat + 3 + (new_sz + (1 : BitVec 32)).toNat)
      s.core.arena ar' ∧
    (∀ j < (new_sz + (1 : BitVec 32)).toNat,
      (ar'[dst.toNat + 3 + j]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
    List.Sublist (((ar'.drop (dst.toNat + 3)).take (new_sz + (1 : BitVec 32)).toNat).map
      BitVec.toNat) (((s.core.arena.drop (src.toNat + 3)).take (i.toNat + 1)).map BitVec.toNat) ∧
    (∀ l ∈ ((s.core.arena.drop (src.toNat + 3)).take (i.toNat + 1)).map BitVec.toNat,
      l ∈ ((ar'.drop (dst.toNat + 3)).take (new_sz + (1 : BitVec 32)).toNat).map BitVec.toNat ∨
        (l < 2 * s.core.cur_vars ∧ (s.core.lvl[l / 2]?.getD 0#32).toNat = 0 ∧
          s.core.vals[l]?.getD 0#8 = 0xFF#8)) := by
  intro ar'
  have hkept_succ :
      ((ar'.drop (dst.toNat + 3)).take (new_sz.toNat + 1)).map BitVec.toNat =
      ((arL.drop (dst.toNat + 3)).take new_sz.toNat).map BitVec.toNat ++ [lit.toNat] := by
    dsimp only [ar']
    rw [hdst_idx, drop_take_set_append (by omega : dst.toNat + 3 + new_sz.toNat < arL.length),
      List.map_append, List.map_singleton]
  refine ⟨by simp [ar', harL], ?_, ?_, ?_, ?_⟩
  · intro idx hidx; rw [hnsz1_eq] at hidx; dsimp only [ar']
    rw [List.getElem?_set_ne (by omega)]; exact houtL idx (by omega)
  · intro j hj; rw [hnsz1_eq] at hj; dsimp only [ar']
    by_cases hje : j = new_sz.toNat
    · subst hje; rw [← hdst_idx, List.getElem?_set_self hdst_lt, Option.getD_some]; exact hlit_cv
    · rw [List.getElem?_set_ne (by omega)]; exact hltL j (by omega)
  · rw [hnsz1_eq, hkept_succ, horig_succ]; exact hsubL.append (List.Sublist.refl _)
  · intro l hl; rw [horig_succ, List.mem_append, List.mem_singleton] at hl
    rw [hnsz1_eq, hkept_succ, List.mem_append, List.mem_singleton]
    rcases hl with hl | rfl
    · rcases hdropL l hl with hin | hd
      · exact Or.inl (Or.inl hin)
      · exact Or.inr hd
    · exact Or.inl (Or.inr rfl)

/-! ## 2. `full_sweep_copy_wp` (`Full1.lean:1202-1243`) -/

private def SweepCopyLoopInv (c : FullCfg) (s : FullState) (R : Mem 64 → Prop)
    (src dst : BitVec 64) (old_sz : BitVec 32) (p : Tup Val [i32, i32]) (mL : Mem 64) : Prop :=
  let (new_sz, i, ()) := p
  new_sz.toNat ≤ i.toNat ∧ i.toNat ≤ old_sz.toNat ∧
  ∃ arL : List (BitVec 32), arL.length = c.arena_cap ∧
    OutsideSliceAgrees (dst.toNat + 3) (dst.toNat + 3 + new_sz.toNat) s.core.arena arL ∧
    (∀ j < new_sz.toNat, (arL[dst.toNat + 3 + j]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
    List.Sublist (((arL.drop (dst.toNat + 3)).take new_sz.toNat).map BitVec.toNat)
      (((s.core.arena.drop (src.toNat + 3)).take i.toNat).map BitVec.toNat) ∧
    (∀ l ∈ ((s.core.arena.drop (src.toNat + 3)).take i.toNat).map BitVec.toNat,
      l ∈ ((arL.drop (dst.toNat + 3)).take new_sz.toNat).map BitVec.toNat ∨
        (l < 2 * s.core.cur_vars ∧ (s.core.lvl[l / 2]?.getD 0#32).toNat = 0 ∧
          s.core.vals[l]?.getD 0#8 = 0xFF#8)) ∧
    (FullMem c { s with core := { s.core with arena := arL } } ⋆ R) mL

private def SweepCopyJoinInv (c : FullCfg) (s : FullState) (R : Mem 64 → Prop)
    (src dst : BitVec 64) (i : BitVec 32) (p : Tup Val [i32]) (m' : Mem 64) : Prop :=
  let (new_sz', ()) := p
  new_sz'.toNat ≤ i.toNat + 1 ∧
  ∃ ar' : List (BitVec 32), ar'.length = c.arena_cap ∧
    OutsideSliceAgrees (dst.toNat + 3) (dst.toNat + 3 + new_sz'.toNat) s.core.arena ar' ∧
    (∀ j < new_sz'.toNat, (ar'[dst.toNat + 3 + j]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
    List.Sublist (((ar'.drop (dst.toNat + 3)).take new_sz'.toNat).map BitVec.toNat)
      (((s.core.arena.drop (src.toNat + 3)).take (i.toNat + 1)).map BitVec.toNat) ∧
    (∀ l ∈ ((s.core.arena.drop (src.toNat + 3)).take (i.toNat + 1)).map BitVec.toNat,
      l ∈ ((ar'.drop (dst.toNat + 3)).take new_sz'.toNat).map BitVec.toNat ∨
        (l < 2 * s.core.cur_vars ∧ (s.core.lvl[l / 2]?.getD 0#32).toNat = 0 ∧
          s.core.vals[l]?.getD 0#8 = 0xFF#8)) ∧
    (FullMem c { s with core := { s.core with arena := ar' } } ⋆ R) m'

private def SweepCopyOomInv (c : FullCfg) (F_cur : List (List Nat)) (s : FullState)
    (R : Mem 64 → Prop) (arL : List (BitVec 32)) (_ : Tup Val []) (mOom : Mem 64) : Prop :=
  ∃ wvecO wstkO wlenO wuO wsO,
    let sO : FullState :=
      { core := { s.core with arena := arL, wvec := wvecO, wstk := wstkO, wlen := wlenO,
                              wusable := wuO }
        scratch := { s.scratch with wsort := wsO } }
    sO.LengthsOk c ∧ BinOnlyWatchesInv F_cur sO.core ∧ (FullMem c sO ⋆ R) mOom

private theorem sweep_copy_ret_sat {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {R : Mem 64 → Prop} {src dst : BitVec 64} {old_sz : BitVec 32}
    {at_root : Bool} {Q : Post [i64]} {arL : List (BitVec 32)} {mL : Mem 64}
    (hlen : s.LengthsOk c) (hdst_le : dst.toNat ≤ c.arena_cap) (hsz_lt : old_sz.toNat < 2 * 2 ^ 28)
    (har_t : at_root = true) (hcl0 : s.core.cur_level = 0)
    (hw_dst : FullWitnessInv c F0 F_cur { s.core with arena_len := dst.toNat })
    (hbin0 : BinOnlyWatchesInv F_cur s.core)
    (hQ : fullSweepCopyPost c F0 F_cur s R src dst old_sz at_root Q)
    (harL : arL.length = c.arena_cap)
    (hout : OutsideSliceAgrees (dst.toNat + 3) (dst.toNat + 3 + old_sz.toNat) s.core.arena arL)
    (hmL : (FullMem c { s with core := { s.core with arena := arL } } ⋆ R) mL) :
    Q (0xFFFFFFFF#64, ()) mL :=
  hQ 0xFFFFFFFF#64 arL s.core.vals s.core.flags s.core.lvl s.core.rsns s.core.trl s.core.trail_pos
    s.core.trail_end s.core.unassigned s.core.unflushed s.core.wvec s.core.wstk s.core.wlen
    s.core.wusable s.core.num_binary s.core.oom s.scratch.phases s.scratch.wsort mL
    ⟨{ hlen.core_ok with arena_len_arr := harL }, hlen.scratch_ok⟩ hout
    ⟨fun hf => Bool.noConfusion (har_t.symm.trans hf),
     fun _ => ⟨sweep_copy_witness_with_ar (s := s) hlen.core_ok.arena_len_arr hdst_le hcl0 hw_dst
         harL (fun idx hidx => hout.getElem?_lt (by omega)),
       hbin0.with_core rfl rfl rfl rfl, Nat.le_refl _, Or.inr (Or.inr (Or.inr (Or.inl rfl))),
       (fun h => by cases h), (fun h => by cases h), (fun _ => rfl), (fun h => by cases h),
       (fun ⟨_, hle⟩ => by revert hle; simp; omega)⟩⟩ hmL

private theorem sweep_copy_ret_unsat {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {R : Mem 64 → Prop} {src dst : BitVec 64} {old_sz : BitVec 32}
    {at_root : Bool} {Q : Post [i64]} {arL : List (BitVec 32)} {mL : Mem 64}
    (hlen : s.LengthsOk c) (hdst_le : dst.toNat ≤ c.arena_cap) (hsz_lt : old_sz.toNat < 2 * 2 ^ 28)
    (har_t : at_root = true) (hcl0 : s.core.cur_level = 0)
    (hw_dst : FullWitnessInv c F0 F_cur { s.core with arena_len := dst.toNat })
    (hbin0 : BinOnlyWatchesInv F_cur s.core)
    (hQ : fullSweepCopyPost c F0 F_cur s R src dst old_sz at_root Q)
    (harL : arL.length = c.arena_cap)
    (hout : OutsideSliceAgrees (dst.toNat + 3) (dst.toNat + 3 + old_sz.toNat) s.core.arena arL)
    (hunsat : F0.Unsat)
    (hmL : (FullMem c { s with core := { s.core with arena := arL } } ⋆ R) mL) :
    Q (0xFFFFFFFE#64, ()) mL :=
  hQ 0xFFFFFFFE#64 arL s.core.vals s.core.flags s.core.lvl s.core.rsns s.core.trl s.core.trail_pos
    s.core.trail_end s.core.unassigned s.core.unflushed s.core.wvec s.core.wstk s.core.wlen
    s.core.wusable s.core.num_binary s.core.oom s.scratch.phases s.scratch.wsort mL
    ⟨{ hlen.core_ok with arena_len_arr := harL }, hlen.scratch_ok⟩ hout
    ⟨fun hf => Bool.noConfusion (har_t.symm.trans hf),
     fun _ => ⟨sweep_copy_witness_with_ar (s := s) hlen.core_ok.arena_len_arr hdst_le hcl0 hw_dst
         harL (fun idx hidx => hout.getElem?_lt (by omega)),
       hbin0.with_core rfl rfl rfl rfl, Nat.le_refl _, Or.inl rfl, (fun _ => hunsat),
       (fun h => by cases h), (fun _ => rfl), (fun h => by cases h),
       (fun ⟨_, hle⟩ => by revert hle; simp; omega)⟩⟩ hmL

theorem full_sweep_copy_wp (Γ : Env)
    (hassign : ∀ a m Q X, fullAssignLvlSpec a m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] a m Q X)
    (hpush : ∀ a m Q X, fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, fullSweepCopySpec a m Q X → Func.wp Γ full_sweep_copy_body a m Q X := by
  rintro ⟨h, src, dst, old_sz, at_root, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hlen, hdst_src, hsz3, hsrc_fit, hat_eq, hlits_lt, hroot_pre, hm, hQ⟩
  change fullSweepCopyPost c F0 F_cur s R src dst old_sz at_root Q at hQ
  have hcap_lt : c.arena_cap < 2 * 2 ^ 28 := c.harena
  have hmax_lt : c.max_vars < 2 * 2 ^ 28 := c.hmaxv
  have hal_le := hlen.core_ok.arena_len_le
  have har_len := hlen.core_ok.arena_len_arr
  have hcv_le := hlen.core_ok.cur_vars_le
  have hv_len := hlen.core_ok.vals_len
  have hl_len := hlen.core_ok.lvl_len
  have hfit_cap : src.toNat + 3 + old_sz.toNat ≤ c.arena_cap := by omega
  have hdst_fit : dst.toNat + 3 + old_sz.toNat ≤ c.arena_cap := by omega
  fr_steps
  fr_split
  · -- `at_root = true` (`s.core.cur_level = 0`)
    have har_t : at_root = true := by simpa using hc
    have hcl0 : s.core.cur_level = 0 := of_decide_eq_true (hat_eq.symm.trans har_t)
    obtain ⟨hw_dst, hbin0, hent0⟩ := hroot_pre har_t
    clear hroot_pre hat_eq
    fr_steps
    refine wp_loop_inv (SweepCopyLoopInv c s R src dst old_sz)
      (fun (_, i, ()) _ => old_sz.toNat - i.toNat) (fun J hLoop => ?_) ?_
    · fr_steps
      exact hLoop (0#32, 0#32, ()) m ⟨Nat.le_refl _, Nat.zero_le _, s.core.arena, har_len,
        fun _ _ => rfl, fun _ hj => by simp at hj, by simp, fun _ hl => by simp at hl, hm⟩
    · rintro J ⟨new_sz, i, ⟨⟩⟩ mL ⟨hni, hi_le, arL, harL, houtL, hltL, hsubL, hdropL, hmL⟩ hLoop
      fr_split
      · have hi_lt : i.toNat < old_sz.toNat := by c0_bound
        have hi1_eq : (i + (1 : BitVec 32)).toNat = i.toNat + 1 := bv32_add1 (by omega)
        have hnsz1_eq : (new_sz + (1 : BitVec 32)).toNat = new_sz.toNat + 1 :=
          bv32_add1 (by omega)
        have hsrc_idx : (src + (3 : BitVec 64) + i.setWidth 64).toNat = src.toNat + 3 + i.toNat :=
          bv64_add3_zext_toNat (by omega)
        have hdst_idx : (dst + (3 : BitVec 64) + new_sz.setWidth 64).toNat =
            dst.toNat + 3 + new_sz.toNat := bv64_add3_zext_toNat (by omega)
        have hsrc_lt : (src + (3 : BitVec 64) + i.setWidth 64).toNat < arL.length := by omega
        have hdst_lt : (dst + (3 : BitVec 64) + new_sz.setWidth 64).toNat < arL.length := by omega
        let lit := arL[(src + (3 : BitVec 64) + i.setWidth 64).toNat]'hsrc_lt
        have hlit_eq : lit = arL[src.toNat + 3 + i.toNat]'(by omega) := by
          dsimp only [lit]; simp only [hsrc_idx]
        have hlit_orig : lit = s.core.arena[src.toNat + 3 + i.toNat]'(by omega) := by
          have h1 := houtL.getElem?_ge (i := src.toNat + 3 + i.toNat) (by omega)
          rw [List.getElem?_eq_getElem (by omega : src.toNat + 3 + i.toNat < arL.length),
            List.getElem?_eq_getElem (by omega : src.toNat + 3 + i.toNat < s.core.arena.length)]
            at h1
          rw [hlit_eq]; exact Option.some.inj h1
        have hlit_cv : lit.toNat < 2 * s.core.cur_vars := by
          have := hlits_lt i.toNat hi_lt
          rw [List.getElem?_eq_getElem (by omega : src.toNat + 3 + i.toNat < s.core.arena.length),
            Option.getD_some, ← hlit_orig] at this; exact this
        have horig_succ : ((s.core.arena.drop (src.toNat + 3)).take (i.toNat + 1)).map BitVec.toNat
            = ((s.core.arena.drop (src.toNat + 3)).take i.toNat).map BitVec.toNat ++
                [lit.toNat] := by
          rw [drop_take_succ (by omega : src.toNat + 3 + i.toNat < s.core.arena.length),
            List.map_append, List.map_singleton, hlit_orig]
        fr_to_group
        refine wp_join_group (SweepCopyJoinInv c s R src dst i) ?_ ?_
        · rintro _ ⟨new_sz', ⟨⟩⟩ m' ⟨hni', ar', har', hout', hlt', hsub', hdrop', hm'⟩
          fr_steps
          exact hLoop (new_sz', i + (1 : BitVec 32), ()) m' (by dsimp only; rw [hi1_eq]; omega)
            ⟨by rw [hi1_eq]; exact hni', by rw [hi1_eq]; omega, ar', har', hout', hlt',
             by rw [hi1_eq]; exact hsub', by rw [hi1_eq]; exact hdrop', hm'⟩
        · intro Ji hJi
          clear hLoop J hassign hpush hent0 hlits_lt
          have hlit_vlen : (arL[(src + (3 : BitVec 64) + i.setWidth 64).toNat]'hsrc_lt).toNat <
              s.core.vals.length := by change lit.toNat < _; omega
          have hidx_mod : (src.toNat + (3 : BitVec 64).toNat + i.toNat) % 2 ^ 64 =
              src.toNat + 3 + i.toNat := by
            rw [show (3 : BitVec 64).toNat = 3 from rfl, Nat.mod_eq_of_lt (by omega)]
          have ha_lit : arL[(src.toNat + (3 : BitVec 64).toNat + i.toNat) % 2 ^ 64]'(by
              rw [hidx_mod]; omega) = lit := by rw [hlit_eq]; simp only [hidx_mod]
          fr_to_group
          refine wp_join_group (fun () m' => m' = mL) ?_ ?_
          · rintro _ ⟨⟩ _ rfl
            fr_steps
            obtain ⟨har', hout', hlt', hsub', hdrop'⟩ := sweep_copy_keep_inv harL
              hdst_idx hdst_lt hnsz1_eq hlit_cv houtL hltL hsubL hdropL horig_succ
            exact hJi (new_sz + (1 : BitVec 32), ()) m
              ⟨by rw [hnsz1_eq]; omega, _, har', hout', hlt', hsub', hdrop', hm⟩
          · intro Je hJe
            fr_split
            · -- `(u64)v < cv` (auto-discharged or split)
              fr_split
              · -- `lvl[v] == 0`
                have hlvl_z : (s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat = 0 := by
                  have h1 : s.core.lvl[lit.toNat / 2]'(by omega) = (0 : BitVec 32) := by
                    simpa only [ha_lit] using hc
                  rw [List.getElem?_eq_getElem (by omega), Option.getD_some, h1]; rfl
                fr_split
                · -- `vals[lit] ≠ 0`
                  have hval_ne : s.core.vals[lit.toNat]'(by omega) ≠ 0#8 := fun h0 => by
                    have h1 : (s.core.vals[lit.toNat]'(by omega)).signExtend 32 ≠ 0#32 := by
                      simpa only [ha_lit] using hc
                    rw [h0] at h1; exact h1 rfl
                  fr_split
                  · -- `vals[lit] > 0`: satisfied; return `0xFFFFFFFF#64`
                    fr_steps
                    exact sweep_copy_ret_sat hlen (by omega) (by omega) har_t hcl0 hw_dst hbin0 hQ
                      harL (fun idx hidx => houtL idx (by omega)) hmL
                  · -- `¬ (vals[lit] > 0)`: falsified at level 0, drop
                    have hval_ff : s.core.vals[lit.toNat]?.getD 0#8 = 0xFF#8 := by
                      have hdom := hw_dst.vals_domain lit.toNat hlit_cv
                      have hv_get : s.core.vals[lit.toNat]?.getD 0#8 =
                          s.core.vals[lit.toNat]'(by omega) := by
                        rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                      have hng : (0#32).slt ((s.core.vals[lit.toNat]'(by omega)).signExtend 32) =
                          false := by simpa only [ha_lit] using hc
                      rw [hv_get] at hdom ⊢
                      rcases hdom with h0 | h1 | hff
                      · exact absurd h0 hval_ne
                      · exact absurd ((bv8_gt0_of_dom (Or.inr (Or.inl h1))).1.mpr h1)
                          (by simp [hng])
                      · exact hff
                    fr_steps
                    refine hJi (new_sz, ()) mL
                      ⟨by omega, arL, harL, houtL, hltL, ?_, ?_, hmL⟩
                    · rw [horig_succ]; exact hsubL.trans (List.sublist_append_left _ _)
                    · intro l hl; rw [horig_succ, List.mem_append, List.mem_singleton] at hl
                      rcases hl with hl | rfl
                      · exact hdropL l hl
                      · exact Or.inr ⟨hlit_cv, hlvl_z, hval_ff⟩
                · fr_steps; exact hJe () mL rfl
              · fr_steps; exact hJe () mL rfl
      · -- Loop exit (`i = old_sz`)
        have hi_eq : i.toNat = old_sz.toNat := by c0_bound
        have hpre : PrefixAgrees dst.toNat s.core.arena arL :=
          fun idx hidx => houtL.getElem?_lt (by omega)
        have hwL : FullWitnessInv c F0 F_cur { s.core with arena := arL, arena_len := dst.toNat } :=
          sweep_copy_witness_with_ar har_len (by omega) hcl0 hw_dst harL hpre
        have hsub_fin : List.Sublist
            (((arL.drop (dst.toNat + 3)).take new_sz.toNat).map BitVec.toNat)
            (((s.core.arena.drop (src.toNat + 3)).take old_sz.toNat).map BitVec.toNat) :=
          hi_eq ▸ hsubL
        have hent_kept : (cnfOfClauses F_cur).EntailsClause
            (cnfClause (((arL.drop (dst.toNat + 3)).take new_sz.toNat).map BitVec.toNat)) :=
          level0_entails_of_filter hw_dst hent0 (hi_eq ▸ hdropL)
        have hout_fin : OutsideSliceAgrees (dst.toNat + 3) (dst.toNat + 3 + old_sz.toNat)
            s.core.arena arL := fun idx hidx => houtL idx (by omega)
        have hlenL : ({ s with core := { s.core with arena := arL } } : FullState).LengthsOk c :=
          ⟨{ hlen.core_ok with arena_len_arr := harL }, hlen.scratch_ok⟩
        have hbinL : BinOnlyWatchesInv F_cur { s.core with arena := arL } :=
          hbin0.with_core rfl rfl rfl rfl
        fr_split
        · -- `new_sz == 0`: empty clause -> UNSAT (`0xFFFFFFFE#64`)
          have hnsz0 : new_sz.toNat = 0 := by c0_bound
          rw [hnsz0] at hent_kept; simp only [List.take_zero, List.map_nil] at hent_kept
          fr_steps
          exact sweep_copy_ret_unsat hlen (by omega) (by omega) har_t hcl0 hw_dst hbin0 hQ harL
            hout_fin (level0_unsat_of_entails_nil hwL hent_kept) hmL
        · fr_split
          · -- `new_sz == 1`: unit clause `[ulit]`
            have hnsz1 : new_sz.toNat = 1 := by c0_bound
            have hd3_eq : (dst + (3 : BitVec 64)).toNat = dst.toNat + 3 := bv64_add3 (by omega)
            have hd3_lt : (dst + (3 : BitVec 64)).toNat < arL.length := by omega
            let ulit := arL[(dst + (3 : BitVec 64)).toNat]'hd3_lt
            obtain ⟨hulit_eq, hulit_lt, hent_u⟩ :=
              sweep_copy_new1_prep hd3_eq hd3_lt (hltL 0 (by omega)) (hnsz1 ▸ hent_kept)
            have hulit_lt' : ulit.toNat < 2 * s.core.cur_vars := hulit_lt
            have hulit_vlen : (arL[(dst + (3 : BitVec 64)).toNat]'hd3_lt).toNat <
                s.core.vals.length := by omega
            clear hLoop J hsub_fin hent_kept hent0 hlits_lt hpush hltL hsubL hdropL houtL hpre
            fr_split
            · -- `vals[ulit] < 0` (`= 0xFF#8`) -> UNSAT
              have hff : s.core.vals[ulit.toNat]?.getD 0#8 = 0xFF#8 := by
                have hdom := hwL.vals_domain ulit.toNat hulit_lt'
                have hget :
                    s.core.vals[ulit.toNat]?.getD 0#8 = s.core.vals[ulit.toNat]'(by omega) := by
                  rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                rw [hget] at hdom ⊢
                exact (bv8_gt0_of_dom hdom).2.mp hc
              fr_steps
              exact sweep_copy_ret_unsat hlen (by omega) (by omega) har_t hcl0 hw_dst hbin0 hQ harL
                hout_fin (level0_unsat_of_unit_false hwL hcl0 hulit_lt' hent_u hff) hmL
            · fr_split
              · -- `vals[ulit] == 0`: call `full_assign_lvl(h, ulit, 0xFFFFFFFFu, 0u)`
                have hun : s.core.vals[ulit.toNat]?.getD 0#8 = 0#8 := by
                  have hdm : (dst.toNat + (3 : BitVec 64).toNat) % 2 ^ 64 = dst.toNat + 3 := by
                    rw [show (3 : BitVec 64).toNat = 3 from rfl, Nat.mod_eq_of_lt (by omega)]
                  have hua : arL[(dst.toNat + (3 : BitVec 64).toNat) % 2 ^ 64]'(by
                      rw [hdm]; omega) = ulit := by
                    dsimp only [ulit]; rw [hulit_eq]; simp only [hdm]
                  have hsext0 : (s.core.vals[ulit.toNat]'(by omega)).signExtend 32 = 0#32 := by
                    simpa only [hua] using hc
                  have hdom := hwL.vals_domain ulit.toNat hulit_lt'
                  have hg : s.core.vals[ulit.toNat]?.getD 0#8 =
                      s.core.vals[ulit.toNat]'(by omega) := by
                    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                  rw [hg] at hdom ⊢
                  exact (bv8_sext32_eq0_of_dom hdom).mp hsext0
                have hte_lt : s.core.trail_end < s.core.cur_vars :=
                  hwL.trail_end_lt_of_unassigned hulit_lt' hun
                have hnot_skip : ¬ (s.core.cur_vars ≤ ulit.toNat / 2 ∨
                    c.max_vars ≤ s.core.trail_end ∨ s.core.vals[ulit.toNat]?.getD 0#8 ≠ 0#8) := by
                  simp only [hun, ne_eq, not_true_eq_false, or_false]; omega
                fr_steps; c0_call hassign
                refine ⟨c, { s with core := { s.core with arena := arL } }, R, rfl, hlenL, hmL, ?_⟩
                split
                · rename_i hskip; exact absurd hskip hnot_skip
                · dsimp only
                  intro flags' unass' phases' m' hfl' hph' hm'
                  have hw' := level0Assign_preserves_witness
                    (k := { s.core with arena := arL, arena_len := dst.toNat })
                    { hlenL.core_ok with arena_len_le := by change dst.toNat ≤ c.arena_cap; omega }
                    hwL hcl0 hulit_lt' hun hent_u flags' unass' (s.core.unflushed + 1#64)
                  fr_steps
                  exact hQ 1#64 arL ((s.core.vals.set ulit.toNat 1#8).set (ulit.toNat ^^^ 1) 0xFF#8)
                    flags' (s.core.lvl.set (ulit.toNat / 2) 0#32)
                    (s.core.rsns.set (ulit.toNat / 2) 0xFFFFFFFF#32)
                    (s.core.trl.set s.core.trail_end ulit)
                    (s.core.trail_pos.set (ulit.toNat / 2) (BitVec.ofNat 32 s.core.trail_end))
                    (s.core.trail_end + 1) unass' (s.core.unflushed + 1#64) s.core.wvec s.core.wstk
                    s.core.wlen s.core.wusable s.core.num_binary s.core.oom phases' s.scratch.wsort
                    m'
                    ⟨{ hlenL.core_ok with
                       vals_len := by simp [hlenL.core_ok.vals_len], flags_len := hfl'
                       lvl_len := by simp [hlenL.core_ok.lvl_len]
                       rsns_len := by simp [hlenL.core_ok.rsns_len]
                       trl_len := by simp [hlenL.core_ok.trl_len]
                       trail_pos_len := by simp [hlenL.core_ok.trail_pos_len]
                       trail_end_le := hte_lt
                       propagated_le := Nat.le_succ_of_le hlenL.core_ok.propagated_le },
                     { hlenL.scratch_ok with phases_len := hph' }⟩
                    hout_fin ⟨fun hf => Bool.noConfusion (har_t.symm.trans hf),
                     fun _ => ⟨hw', hbinL.with_core rfl rfl rfl rfl, by dsimp only; omega,
                       Or.inr (Or.inr (Or.inl rfl)), (fun h => by cases h), (fun h => by cases h),
                       (fun _ => rfl), (fun _ => by dsimp only; omega),
                       (fun ⟨h3, _⟩ => by exfalso; revert h3; decide)⟩⟩ hm'
              · -- `vals[ulit] > 0`: already satisfied, return `0xFFFFFFFF#64`
                fr_steps
                exact sweep_copy_ret_sat hlen (by omega) (by omega) har_t hcl0 hw_dst hbin0 hQ
                  harL hout_fin hmL
          · fr_split
            · -- `new_sz == 2`: push binary watches `(l0, l1)` and `(l1, l0)`
              have hnsz2 : new_sz.toNat = 2 := by c0_bound
              have hd3_eq : (dst + (3 : BitVec 64)).toNat = dst.toNat + 3 := bv64_add3 (by omega)
              have hd4_eq : (dst + (4 : BitVec 64)).toNat = dst.toNat + 4 := bv64_add4 (by omega)
              have hd3_lt : (dst + (3 : BitVec 64)).toNat < arL.length := by omega
              have hd4_lt : (dst + (4 : BitVec 64)).toNat < arL.length := by omega
              let l0 := arL[(dst + (3 : BitVec 64)).toNat]'hd3_lt
              let l1 := arL[(dst + (4 : BitVec 64)).toNat]'hd4_lt
              obtain ⟨hl0_lt, hl1_lt, hent_01, hent_10, hl0_b, hl1_b⟩ :=
                sweep_copy_new2_prep (by omega) hd3_eq hd4_eq hd3_lt hd4_lt
                  (hltL 0 (by omega)) (hltL 1 (by omega)) (hnsz2 ▸ hent_kept)
              have hb0 := bv32_bin_word_props hl1_b
              have hb1 := bv32_bin_word_props hl0_b
              have hsz_lt_cap : old_sz.toNat < 2 * 2 ^ 28 := by omega
              clear hLoop J hsub_fin hent_kept hw_dst hent0 hlits_lt
                hassign hltL hsubL hdropL houtL hpre hbin0
                hcap_lt hmax_lt hal_le har_len hcv_le hv_len hl_len hfit_cap hdst_fit
                hcl0 hlen hdst_src hsz3 hsrc_fit hnsz2 hl0_b hl1_b
              fr_to_group
              refine wp_join_group (SweepCopyOomInv c F_cur s R arL) ?_ ?_
              · rintro _ ⟨⟩ mOom ⟨wvecO, wstkO, wlenO, wuO, wsO, hlenO, hbinO, hmO⟩
                have hbinO' : BinOnlyWatchesInv F_cur
                    { s.core with arena := arL, wvec := wvecO, wstk := wstkO, wlen := wlenO,
                                  wusable := wuO, oom := 1#64 } :=
                  hbinO.with_core rfl rfl rfl rfl
                have hwO := fullWitnessInv_with_binWatches hwL hbinO'
                fr_steps
                exact hQ 0xFFFFFFFD#64 arL s.core.vals s.core.flags s.core.lvl s.core.rsns
                  s.core.trl s.core.trail_pos s.core.trail_end s.core.unassigned s.core.unflushed
                  wvecO wstkO wlenO wuO s.core.num_binary 1#64 s.scratch.phases wsO m
                  ⟨{ hlenO.core_ok with }, hlenO.scratch_ok⟩ hout_fin
                  ⟨fun hf => Bool.noConfusion (har_t.symm.trans hf),
                   fun _ => ⟨hwO, hbinO', Nat.le_refl _, Or.inr (Or.inl rfl),
                     (fun h => by cases h), (fun _ => rfl), (fun h => absurd rfl h),
                     (fun h => by cases h),
                     (fun ⟨_, hle⟩ => by revert hle; simp; omega)⟩⟩ (fullMem_cast hm rfl)
              · intro Joom hJoom
                fr_steps; c0_call hpush
                refine ⟨c, { s with core := { s.core with arena := arL } }, R, rfl, hlenL,
                  hbinL.layout, fun _ => hb0.2.1, fun h => by exfalso; revert h; decide, hmL,
                  fun ok1 wvec1 wstk1 wlen1 wu1 ws1 m1 hlen1 hlay1 hoth1 hok1t hok1f hm1 => ?_⟩
                have hbin1 : BinOnlyWatchesInv F_cur
                    { s.core with arena := arL, wvec := wvec1, wstk := wstk1, wlen := wlen1,
                                  wusable := wu1 } :=
                  fullWatchPush_preserves_binOnly hbinL hlay1 rfl
                    ⟨hb0.1, hb0.2.1, by rw [hb0.2.2]; exact hl1_lt, by rw [hb0.2.2]; exact hent_01⟩
                    hoth1 (fun h => by obtain ⟨a, _, b, c, d, _⟩ := hok1t h; exact ⟨a, b, c, d⟩)
                    hok1f
                clear hbinL hb0 hl1_lt hent_01 hoth1 hok1t hok1f hlenL hmL
                fr_split
                · -- `ok1 = true`: push second binary watch `(l1, b1)`
                  fr_steps; c0_call hpush
                  refine ⟨c, { core := { s.core with arena := arL, wvec := wvec1, wstk := wstk1,
                                                     wlen := wlen1, wusable := wu1 }
                               scratch := { s.scratch with wsort := ws1 } }, R, rfl, hlen1,
                    hlay1, fun _ => hb1.2.1, fun h => by exfalso; revert h; decide, hm1,
                    fun ok2 wvec2 wstk2 wlen2 wu2 ws2 m2 hlen2 hlay2 hoth2 hok2t hok2f hm2 => ?_⟩
                  have hbin2 : BinOnlyWatchesInv F_cur
                      { s.core with arena := arL, wvec := wvec2, wstk := wstk2, wlen := wlen2,
                                    wusable := wu2 } :=
                    fullWatchPush_preserves_binOnly hbin1 hlay2 rfl
                      ⟨hb1.1, hb1.2.1, by rw [hb1.2.2]; exact hl0_lt,
                        by rw [hb1.2.2]; exact hent_10⟩
                      hoth2 (fun h => by obtain ⟨a, _, b, c, d, _⟩ := hok2t h; exact ⟨a, b, c, d⟩)
                      hok2f
                  clear hbin1 hb1 hl0_lt hent_10 hoth2 hok2t hok2f hlen1 hlay1 hm1 hpush
                  fr_split
                  · -- `ok2 = true`: `num_binary++`, return `0xFFFFFFFF#64`
                    have hbin2' : BinOnlyWatchesInv F_cur
                        { s.core with arena := arL, wvec := wvec2, wstk := wstk2, wlen := wlen2,
                                      wusable := wu2, num_binary := s.core.num_binary + 1#64 } :=
                      hbin2.with_core rfl rfl rfl rfl
                    have hw2 := fullWitnessInv_with_binWatches hwL hbin2'
                    fr_steps
                    exact hQ 0xFFFFFFFF#64 arL s.core.vals s.core.flags s.core.lvl s.core.rsns
                      s.core.trl s.core.trail_pos s.core.trail_end s.core.unassigned
                      s.core.unflushed wvec2 wstk2 wlen2 wu2 (s.core.num_binary + 1#64) s.core.oom
                      s.scratch.phases ws2 m ⟨{ hlen2.core_ok with }, hlen2.scratch_ok⟩ hout_fin
                      ⟨fun hf => Bool.noConfusion (har_t.symm.trans hf),
                       fun _ => ⟨hw2, hbin2', Nat.le_refl _,
                         Or.inr (Or.inr (Or.inr (Or.inl rfl))),
                         (fun h => by cases h), (fun h => by cases h), (fun _ => rfl),
                         (fun h => by cases h),
                         (fun ⟨_, hle⟩ => by revert hle; simp; omega)⟩⟩ (fullMem_cast hm rfl)
                  · fr_steps; exact hJoom () m2 ⟨wvec2, wstk2, wlen2, wu2, ws2, hlen2, hbin2, hm2⟩
                · fr_steps; exact hJoom () m1 ⟨wvec1, wstk1, wlen1, wu1, ws1, hlen1, hbin1, hm1⟩
            · -- `3 ≤ new_sz ≤ old_sz`: return `(u64)new_sz`
              have hge3 : 3 ≤ new_sz.toNat := by
                have h0 : new_sz.toNat ≠ 0 := by c0_bound
                have h1 : new_sz.toNat ≠ 1 := by c0_bound
                have h2 : new_sz.toNat ≠ 2 := by c0_bound
                omega
              have hnsz64 : (new_sz.setWidth 64).toNat = new_sz.toNat := zext_toNat _ (by decide)
              fr_steps
              exact hQ (new_sz.setWidth 64) arL s.core.vals s.core.flags s.core.lvl s.core.rsns
                s.core.trl s.core.trail_pos s.core.trail_end s.core.unassigned s.core.unflushed
                s.core.wvec s.core.wstk s.core.wlen s.core.wusable s.core.num_binary s.core.oom
                s.scratch.phases s.scratch.wsort mL hlenL hout_fin
                ⟨fun hf => Bool.noConfusion (har_t.symm.trans hf),
                 fun _ => ⟨hwL, hbinL, Nat.le_refl _,
                   Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))),
                   fun h => by have := congrArg BitVec.toNat h; rw [hnsz64] at this; simp at this
                               omega,
                   fun h => by have := congrArg BitVec.toNat h; rw [hnsz64] at this; simp at this
                               omega,
                   fun _ => rfl,
                   fun h => by have := congrArg BitVec.toNat h; rw [hnsz64] at this; simp at this
                               omega,
                   fun _ => ⟨by simpa [hnsz64] using hltL, by simpa [hnsz64] using hsub_fin,
                     by simpa [hnsz64] using hent_kept⟩⟩⟩ hmL
  · -- `!at_root`: copy `old_sz` words verbatim from `src + 3` to `dst + 3`
    have har_f : at_root = false := by simpa using hc
    clear hassign hpush hroot_pre hat_eq hlits_lt hv_len hl_len hcv_le hmax_lt
    fr_steps
    refine wp_loop_inv
      (fun (i, ()) mL =>
        i.toNat ≤ old_sz.toNat ∧
        ∃ arL : List (BitVec 32), arL.length = c.arena_cap ∧
          OutsideSliceAgrees (dst.toNat + 3) (dst.toNat + 3 + i.toNat) s.core.arena arL ∧
          (∀ j < i.toNat, arL[dst.toNat + 3 + j]? = s.core.arena[src.toNat + 3 + j]?) ∧
          (FullMem c { s with core := { s.core with arena := arL } } ⋆ R) mL)
      (fun (i, ()) _ => old_sz.toNat - i.toNat)
      (fun J hLoop => ?_) ?_
    · fr_steps
      exact hLoop (0#32, ()) m ⟨Nat.zero_le _, s.core.arena, har_len,
        fun _ _ => rfl, fun _ hj => by simp at hj, hm⟩
    · rintro J ⟨i, ⟨⟩⟩ mL ⟨hi_le, arL, harL, houtL, hcpL, hmL⟩ hLoop
      fr_split
      · have hi_lt : i.toNat < old_sz.toNat := by c0_bound
        have hi1_eq : (i + (1 : BitVec 32)).toNat = i.toNat + 1 := bv32_add1 (by omega)
        have hsrc_idx : (src + (3 : BitVec 64) + i.setWidth 64).toNat = src.toNat + 3 + i.toNat :=
          bv64_add3_zext_toNat (by omega)
        have hdst_idx : (dst + (3 : BitVec 64) + i.setWidth 64).toNat = dst.toNat + 3 + i.toNat :=
          bv64_add3_zext_toNat (by omega)
        have hsrc_lt : (src + (3 : BitVec 64) + i.setWidth 64).toNat < arL.length := by omega
        have hdst_lt : (dst + (3 : BitVec 64) + i.setWidth 64).toNat < arL.length := by omega
        have hread_orig : arL[(src + (3 : BitVec 64) + i.setWidth 64).toNat]'hsrc_lt =
            s.core.arena[src.toNat + 3 + i.toNat]'(by omega) := by
          have h1 := houtL.getElem?_ge (i := src.toNat + 3 + i.toNat) (by omega)
          rw [List.getElem?_eq_getElem (by omega : src.toNat + 3 + i.toNat < arL.length),
            List.getElem?_eq_getElem (by omega : src.toNat + 3 + i.toNat < s.core.arena.length)]
            at h1
          simp only [hsrc_idx]; exact Option.some.inj h1
        fr_steps
        let ar' := arL.set (dst + (3 : BitVec 64) + i.setWidth 64).toNat
          (arL[(src + (3 : BitVec 64) + i.setWidth 64).toNat]'hsrc_lt)
        refine hLoop (i + (1 : BitVec 32), ()) m (by dsimp only; rw [hi1_eq]; omega)
          ⟨by rw [hi1_eq]; omega, ar', by simp [ar', harL], ?_, ?_, hm⟩
        · intro idx hidx
          rw [hi1_eq] at hidx; dsimp only [ar']
          rw [List.getElem?_set_ne (by omega)]
          exact houtL idx (by omega)
        · intro j hj; rw [hi1_eq] at hj
          by_cases hje : j = i.toNat
          · subst hje; dsimp only [ar']
            rw [← hdst_idx, List.getElem?_set_self hdst_lt, hread_orig,
              List.getElem?_eq_getElem (by omega)]
          · dsimp only [ar']; rw [List.getElem?_set_ne (by omega)]; exact hcpL j (by omega)
      · have hi_eq : i.toNat = old_sz.toNat := by c0_bound
        fr_steps
        exact hQ (old_sz.setWidth 64) arL s.core.vals s.core.flags s.core.lvl s.core.rsns
          s.core.trl s.core.trail_pos s.core.trail_end s.core.unassigned s.core.unflushed
          s.core.wvec s.core.wstk s.core.wlen s.core.wusable s.core.num_binary s.core.oom
          s.scratch.phases s.scratch.wsort mL
          ⟨{ hlen.core_ok with arena_len_arr := harL }, hlen.scratch_ok⟩
          (hi_eq ▸ houtL)
          ⟨fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
             rfl, rfl, rfl, hi_eq ▸ hcpL⟩,
           fun ht => Bool.noConfusion (har_f.symm.trans ht)⟩ hmL

end LeanQbe.T.Examples.Kissat.Full
