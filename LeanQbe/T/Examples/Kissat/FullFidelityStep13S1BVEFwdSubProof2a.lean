/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S1BVEFwdSub
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S1Spec
public import LeanQbe.T.Examples.Kissat.FullFidelityBveProof0
public import LeanQbe.T.Examples.Kissat.FullM6SweepProofSpec
public import LeanQbe.T.Examples.Kissat.FullM8CoreParityProofBve0
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullFidelityBveTactics
import LeanQbe.T.Examples.Kissat.FullM6SweepProofDenseProp
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Fidelity Step 13 Shard S1-B Proofs — Part 2a (`full_bve_certify_unit_fid` Helpers & Loop 1)

`0` `import all`, `0` `@[expose]` on theorems/lemmas, `<= 100` cols, `< 1,400` LOC, every theorem
`<= 420` lines. Provides pure BitVec/pigeonhole/model-set helpers, `certMkStateGu`,
`cert_{undo_tmk,finish_unit,loop2_large,loop1_large,loop1}_wp` for Step-13 `S1-B`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S1

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullDenseWatchHelpers
open LeanQbe.T.Examples.Kissat.Full.FullDenseWatchSpecs
open LeanQbe.T.Examples.Kissat.FullFastBveBudgets
open LeanQbe.T.Examples.Kissat.FullM4Sweep
open LeanQbe.T.Examples.Kissat.FullM6Sweep
open LeanQbe.T.Examples.Kissat.FullM8CoreParity
open LeanQbe.T.Examples.Kissat.FullFidelityBve

open scoped FullArenaTactics

/-! ## 1. Pure Propositional, BitVec, & Pigeonhole Helpers -/

public section

theorem cert_zext64_toNat (x : BitVec 32) :
    (BitVec.zeroExtend 64 x).toNat = x.toNat := by
  rw [show BitVec.zeroExtend 64 x = BitVec.setWidth 64 x from rfl, BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (by have := x.isLt; omega)

theorem cert_shr1_toNat (x : BitVec 32) : (x >>> 1#32).toNat = x.toNat / 2 := by
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem cert_shr5_toNat (x : BitVec 32) : (x >>> 5#32).toNat = x.toNat / 32 := by
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem cert_getElemD {α : Type} {xs : List α} {i : Nat} (hi : i < xs.length) (d : α) :
    xs[i]?.getD d = xs[i] := by
  rw [List.getElem?_eq_getElem hi, Option.getD_some]

theorem cert_list_getElem_eq {α : Type} {xs ys : List α} {i j : Nat}
    (hxy : xs = ys) (hij : i = j) (hi : i < xs.length) (_hj : j < ys.length) :
    xs[i] = ys[j] := by
  subst hxy; subst hij; rfl

private theorem cert_nat_xor1 (l : Nat) :
    l ^^^ 1 = if l % 2 = 0 then l + 1 else l - 1 := by
  apply Nat.eq_of_testBit_eq
  intro k
  cases k with
  | zero =>
    simp only [Nat.testBit_xor, Nat.testBit_one_zero]
    by_cases h : l % 2 = 0
    · simp only [h, ↓reduceIte]
      have h0 : l.testBit 0 = false := by simp [Nat.testBit_zero]; omega
      have h1 : (l + 1).testBit 0 = true := by simp [Nat.testBit_zero]; omega
      rw [h0, h1]; decide
    · simp only [h, ↓reduceIte]
      have h0 : l.testBit 0 = true := by simp [Nat.testBit_zero]; omega
      have h1 : (l - 1).testBit 0 = false := by simp [Nat.testBit_zero]; omega
      rw [h0, h1]; decide
  | succ k' =>
    have h1 : Nat.testBit 1 (k' + 1) = false := by simp [Nat.testBit_succ]
    simp only [Nat.testBit_xor, h1, Bool.xor_false]
    by_cases h : l % 2 = 0
    · simp only [h, ↓reduceIte]; simp [Nat.testBit_succ, show l / 2 = (l + 1) / 2 by omega]
    · simp only [h, ↓reduceIte]; simp [Nat.testBit_succ, show l / 2 = (l - 1) / 2 by omega]

theorem cert_packed_lit_toNat (loc l : BitVec 32)
    (hge : 1 ≤ loc.toNat) (hle : loc.toNat ≤ 8192) :
    (((loc - 1#32) <<< 1#32) ||| (l &&& 1#32)).toNat = 2 * (loc.toNat - 1) + l.toNat % 2 := by
  have hsub : (loc - 1#32).toNat = loc.toNat - 1 := by simp [BitVec.toNat_sub]; omega
  have hshl : ((loc - 1#32) <<< 1#32).toNat = 2 * (loc.toNat - 1) := by
    simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, hsub]; omega
  have hand : (l &&& 1#32).toNat = l.toNat % 2 := by simp [BitVec.toNat_and, Nat.and_one_is_mod]
  rw [BitVec.toNat_or, hshl, hand]; apply Nat.eq_of_testBit_eq; intro k; rw [Nat.testBit_or]
  cases k with
  | zero =>
    rcases Nat.mod_two_eq_zero_or_one l.toNat with h | h <;> simp [Nat.testBit_zero, h]
  | succ j =>
    have hlt : l.toNat % 2 < 2 := Nat.mod_lt _ (by decide)
    have hbit : (l.toNat % 2).testBit (j + 1) = false := by
      rw [Nat.testBit_lt_two_pow]; exact Nat.lt_of_lt_of_le hlt (Nat.le_self_pow (by omega) 2)
    rw [hbit, Bool.or_false]; simp only [Nat.testBit, Nat.shiftRight_eq_div_pow]
    rcases (⟨2 ^ j, by rw [Nat.pow_succ, Nat.mul_comm]⟩ : 2 ∣ 2 ^ (j + 1)) with ⟨q, hq⟩
    have hdiv : (2 * (loc.toNat - 1) + l.toNat % 2) / 2 = 2 * (loc.toNat - 1) / 2 := by omega
    rw [hq, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, hdiv]

private theorem cert_pigeonhole_inj_le :
    ∀ (m n : Nat) (f : Nat → Nat),
      (∀ i < n, f i < m) → (∀ i j, i < n → j < n → f i = f j → i = j) → n ≤ m := by
  intro m; induction m with
  | zero =>
    intro n f hlt _; cases n with
    | zero => exact Nat.le_refl 0
    | succ n' => exact absurd (hlt 0 (Nat.zero_lt_succ n')) (Nat.not_lt_zero _)
  | succ m ih =>
    intro n f hlt hinj; cases n with
    | zero => exact Nat.zero_le _
    | succ n' =>
      by_cases hhit : ∃ k < n', f k = m
      · rcases hhit with ⟨k, hk, hfk⟩
        let f' : Nat → Nat := fun i => if i = k then f n' else f i
        have hne : f n' ≠ m := fun h => by
          have := hinj k n' (by omega) (by omega) (by omega); omega
        have hlt' : ∀ i < n', f' i < m := fun i hi => by
          dsimp [f']; split
          · have := hlt n' (by omega); omega
          · next hne_ik =>
            have h1 := hlt i (by omega)
            have : f i ≠ m := fun heq => hne_ik (hinj i k (by omega) (by omega) (by omega))
            omega
        have hinj' : ∀ i j, i < n' → j < n' → f' i = f' j → i = j := fun i j hi hj heq => by
          dsimp [f'] at heq; split at heq <;> split at heq
          · subst_vars; rfl
          · have := hinj n' j (by omega) (by omega) heq; omega
          · have := hinj i n' (by omega) (by omega) heq; omega
          · exact hinj i j (by omega) (by omega) heq
        exact Nat.succ_le_succ (ih n' f' hlt' hinj')
      · have hlt' : ∀ i < n', f i < m := fun i hi => by
          have h1 := hlt i (by omega); have : f i ≠ m := fun heq => hhit ⟨i, hi, heq⟩; omega
        exact Nat.succ_le_succ
          (ih n' f hlt' fun i j hi hj heq => hinj i j (by omega) (by omega) heq)

theorem cert_trail_end_lt_of_val0 {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hw : FullWitnessInv c F0 F_cur s.core)
    (htr : s.core.trail_end ≤ s.core.cur_vars) {lit : Nat} (hlit : lit < 2 * s.core.cur_vars)
    (hv0 : s.core.vals[lit]?.getD 0#8 = 0#8) : s.core.trail_end < s.core.cur_vars := by
  let v := lit / 2
  have hno : ∀ i < s.core.trail_end, (s.core.trl[i]?.getD 0#32).toNat / 2 ≠ v := by
    intro i hi hdiv; have hlt := hw.trail_lits_lt i hi
    let p := (s.core.trl[i]?.getD 0#32).toNat
    have hp : p = lit ∨ p = lit ^^^ 1 := by
      rw [cert_nat_xor1 lit]; change p / 2 = lit / 2 at hdiv; split <;> omega
    rcases hp with hpeq | hpeq
    · have h1 := (hw.vals_true_iff lit hlit).mpr ⟨i, hi, hpeq⟩
      rw [hv0] at h1; exact absurd h1 (by decide)
    · have h2 := (hw.vals_false_iff lit hlit).mpr ⟨i, hi, hpeq⟩
      rw [hv0] at h2; exact absurd h2 (by decide)
  let g : Nat → Nat := fun i =>
    let x := (s.core.trl[i]?.getD 0#32).toNat / 2; if x < v then x else x - 1
  have hglt : ∀ i < s.core.trail_end, g i < s.core.cur_vars - 1 := fun i hi => by
    have := hw.trail_lits_lt i hi; have := hno i hi; dsimp [g]; split <;> omega
  have hginj : ∀ i j, i < s.core.trail_end → j < s.core.trail_end → g i = g j → i = j := by
    intro i j hi hj heq; have := hno i hi; have := hno j hj; dsimp [g] at heq
    have hdiv : (s.core.trl[i]?.getD 0#32).toNat / 2 = (s.core.trl[j]?.getD 0#32).toNat / 2 := by
      split at heq <;> split at heq <;> omega
    exact hw.trail_vars_nodup i j hi hj hdiv
  have := cert_pigeonhole_inj_le (s.core.cur_vars - 1) s.core.trail_end g hglt hginj; omega

private theorem cert_litOf_litToLiteral (q : Nat) : litOfLiteral (litToLiteral q) = q := by
  simp only [litOfLiteral, litToLiteral, litVar, litSign, mkLit]
  by_cases hmod : q % 2 = 0
  · have hb : (q % 2 == 1) = false := by simp; omega
    simp [hb]; omega
  · have hb : (q % 2 == 1) = true := by simp; omega
    simp [hb]; omega

private theorem cert_clause_unit_sat_iff (l : Nat) (α : Nat → Bool) :
    (cnfClause [l]).Sat α ↔ α (l / 2) = decide (l % 2 = 0) := by
  rw [CNF.Clause.sat_iff_exists_mem_eq]
  constructor
  · rintro ⟨⟨v, p⟩, hm, heq⟩
    rw [mem_cnfClause_iff] at hm; simp only [List.mem_singleton] at hm
    cases p
    · simp only [litOfLiteral, mkLit, Bool.false_eq_true, ↓reduceIte] at hm
      have hv : v = l / 2 := by omega
      have hm1 : l % 2 ≠ 0 := by omega
      simpa [hv, hm1] using heq
    · simp only [litOfLiteral, mkLit, ↓reduceIte] at hm
      have hv : v = l / 2 := by omega
      have hm0 : l % 2 = 0 := by omega
      simpa [hv, hm0] using heq
  · intro heq
    refine ⟨litToLiteral l, mem_cnfClause_iff.mpr ?_, ?_⟩
    · simp only [List.mem_singleton]; exact cert_litOf_litToLiteral l
    · by_cases hmod : l % 2 = 0
      · have hb : (l % 2 == 1) = false := by simp; omega
        have hdec : decide (l % 2 = 0) = true := decide_eq_true hmod
        simpa [litToLiteral, litVar, litSign, hb, hdec] using heq
      · have hb : (l % 2 == 1) = true := by simp; omega
        have hdec : decide (l % 2 = 0) = false := decide_eq_false hmod
        simpa [litToLiteral, litVar, litSign, hb, hdec] using heq

theorem cert_clause_sat_iff_mem (lits : List Nat) (α : Nat → Bool) :
    (cnfClause lits).Sat α ↔ ∃ q ∈ lits, (cnfClause [q]).Sat α := by
  rw [CNF.Clause.sat_iff_exists_mem_eq]
  constructor
  · rintro ⟨⟨v, p⟩, hm, heq⟩
    rw [mem_cnfClause_iff] at hm
    refine ⟨litOfLiteral (v, p), hm, ?_⟩
    rw [cert_clause_unit_sat_iff]
    cases p
    · have hd : mkLit v false / 2 = v := by simp only [mkLit, Bool.false_eq_true, ↓reduceIte]; omega
      have hm1 : ¬ (mkLit v false % 2 = 0) := by
        simp only [mkLit, Bool.false_eq_true, ↓reduceIte]; omega
      simpa [litOfLiteral, hd, hm1] using heq
    · have hd : mkLit v true / 2 = v := by simp only [mkLit, ↓reduceIte]; omega
      have hm0 : mkLit v true % 2 = 0 := by simp only [mkLit, ↓reduceIte]; omega
      simpa [litOfLiteral, hd, hm0] using heq
  · rintro ⟨q, hq, hsat⟩
    rw [cert_clause_unit_sat_iff] at hsat
    refine ⟨litToLiteral q, mem_cnfClause_iff.mpr ?_, ?_⟩
    · simpa [cert_litOf_litToLiteral] using hq
    · by_cases hmod : q % 2 = 0
      · have hb : (q % 2 == 1) = false := by simp; omega
        have hdec : decide (q % 2 = 0) = true := decide_eq_true hmod
        simpa [litToLiteral, litVar, litSign, hb, hdec] using hsat
      · have hb : (q % 2 == 1) = true := by simp; omega
        have hdec : decide (q % 2 = 0) = false := decide_eq_false hmod
        simpa [litToLiteral, litVar, litSign, hb, hdec] using hsat

theorem cert_clause_sat_xor_neg (l : Nat) (α : Nat → Bool) :
    (cnfClause [l ^^^ 1]).Sat α ↔ ¬ (cnfClause [l]).Sat α := by
  rw [cert_clause_unit_sat_iff, cert_clause_unit_sat_iff, cert_nat_xor1 l]
  by_cases hm : l % 2 = 0
  · have hd : (l + 1) / 2 = l / 2 := by omega
    have hne : (l + 1) % 2 ≠ 0 := by omega
    simp [hm, hd, hne]
  · have hd : (l - 1) / 2 = l / 2 := by omega
    have he0 : (l - 1) % 2 = 0 := by omega
    simp [hm, hd, he0]

theorem cert_lvl0_false_entails {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState}
    (hw : FullWitnessInv c F0 F_cur s.core) (hlvl : s.core.cur_level = 0)
    {l : Nat} (hl : l < 2 * s.core.cur_vars) (hf : s.core.vals[l]?.getD 0#8 = 255#8) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause [l ^^^ 1]) := by
  rcases (hw.vals_false_iff l hl).mp hf with ⟨i, hi, htrl⟩
  have hli := hw.lvl_le i hi
  rw [hlvl] at hli
  have h0 : (s.core.lvl[(s.core.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by omega
  have hent := hw.level0_sound i hi h0
  rwa [htrl] at hent

theorem cert_entails_resolve_unit {F_cur : List (List Nat)} {u ot : Nat}
    (h1 : (cnfOfClauses F_cur).EntailsClause (cnfClause [u, ot]))
    (h2 : (cnfOfClauses F_cur).EntailsClause (cnfClause [ot ^^^ 1])) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause [u]) := by
  refine entails_of_mem_or_false h1 fun q hq => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · exact Or.inl (by simp)
  · exact Or.inr (by simpa [litNeg] using h2)

theorem cert_lvl0_clause_unit_entails {F_cur : List (List Nat)} {lits : List Nat}
    {u : Nat} (h1 : (cnfOfClauses F_cur).EntailsClause (cnfClause lits))
    (h2 : ∀ q ∈ lits, q ≠ u → (cnfOfClauses F_cur).EntailsClause (cnfClause [q ^^^ 1])) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause [u]) := by
  refine entails_of_mem_or_false h1 fun q hq => ?_
  by_cases hqu : q = u
  · subst hqu; exact Or.inl (by simp)
  · exact Or.inr (by simpa [litNeg] using h2 q hq hqu)

theorem cert_lvl0_unit_contra_unsat {F_cur : List (List Nat)} {u : Nat}
    (h1 : (cnfOfClauses F_cur).EntailsClause (cnfClause [u]))
    (h2 : (cnfOfClauses F_cur).EntailsClause (cnfClause [u ^^^ 1])) :
    (cnfOfClauses F_cur).Unsat := by
  refine unsat_of_entails_nil (entails_of_mem_or_false h1 fun q hq => ?_)
  simp only [List.mem_singleton] at hq; subst hq
  exact Or.inr (by simpa [litNeg] using h2)

theorem cert_denseInvW_set_inconsistent {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState}
    (hinv : FullDenseInvW c F0 F_cur s) (hunsat : (cnfOfClauses F_cur).Unsat) :
    FullDenseInvW c F0 F_cur { s with core := { s.core with inconsistent := 1#64 } } := by
  rcases hinv with ⟨hlen, hw, hlm, hnodup, hext, hlvl, hdm⟩
  refine ⟨⟨{ hlen.core_ok with vals_len := hlen.core_ok.vals_len }, hlen.scratch_ok⟩,
    ?_, hlm, hnodup, hext, hlvl, hdm⟩
  exact { hw with
    inconsistent_sound := fun _ => hunsat
    arena := { hw.arena with len_ok := hw.arena.len_ok }
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) }

theorem cert_i8_slt_zero_eq_255 (v : BitVec 8)
    (hdom : v = 0#8 ∨ v = 1#8 ∨ v = 255#8)
    (hslt : (BitVec.signExtend 32 v).slt (BitVec.signExtend 32 (BitVec.truncate 8 0#32)) = true) :
    v = 255#8 := by
  rcases hdom with rfl | rfl | rfl <;> revert hslt <;> decide

theorem cert_i8_slt0_eq_255 (v : BitVec 8)
    (hdom : v = 0#8 ∨ v = 1#8 ∨ v = 255#8) (hslt : v.slt 0#8 = true) : v = 255#8 := by
  rcases hdom with rfl | rfl | rfl <;> revert hslt <;> decide

theorem cert_i8_dom_255_bv8 (v : BitVec 8)
    (hdom : v = 0#8 ∨ v = 1#8 ∨ v = 255#8)
    (hns : (0#8 : BitVec 8).slt v = false) (hne : v ≠ 0#8) : v = 255#8 := by
  rcases hdom with rfl | rfl | rfl
  · exact absurd rfl hne
  · exfalso; revert hns; decide
  · rfl

theorem cert_fullDenseInvW_mk {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s)
    {tmp exp tmk scr gu : List (BitVec 32)}
    (htmp : tmp.length = c.max_vars) (hexp : exp.length = 2 * c.max_vars)
    (htmk : tmk.length = 2 * c.max_vars) (hscr : scr.length = c.scratch_cap)
    (hgu : gu.length = 64) :
    FullDenseInvW c F0 F_cur
      { core := { s.core with tmp := tmp }
        scratch := { s.scratch with
          wsort := exp, tarjan_mark := tmk, scratch_buf := scr, glue_used := gu } } :=
  let hs0 := h.1.scratch_ok
  ⟨⟨{ h.1.core_ok with tmp_len_arr := htmp },
    { walk_vals_len := hs0.walk_vals_len, phases_len := hs0.phases_len,
      phases_target_len := hs0.phases_target_len, phases_best_len := hs0.phases_best_len,
      walk_best_len := hs0.walk_best_len, heap_len_arr := hs0.heap_len_arr,
      pos_len := hs0.pos_len, shrink_stk_len := hs0.shrink_stk_len,
      q_prev_len := hs0.q_prev_len, q_next_len := hs0.q_next_len,
      q_stamp_len := hs0.q_stamp_len, wsort_len := hexp,
      work_stk1_len := hs0.work_stk1_len, work_stk2_len := hs0.work_stk2_len,
      tarjan_mark_len := htmk, tarjan_reach_len := hs0.tarjan_reach_len,
      score_len := hs0.score_len, sim_sig_len := hs0.sim_sig_len,
      glue_used_len := hgu, last_learned_len := hs0.last_learned_len,
      delayed_len_arr := hs0.delayed_len_arr, red_refs_len := hs0.red_refs_len,
      extend_stk_len := hs0.extend_stk_len, scratch_buf_len := hscr }⟩,
   { h.2.1 with
     arena := { h.2.1.arena with len_ok := h.2.1.arena.len_ok }
     watches := h.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) },
   h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

theorem cert_fullDenseInvW_fuel {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) (fl' : BitVec 64) :
    FullDenseInvW c F0 F_cur { s with core := { s.core with fuel := fl' } } :=
  ⟨⟨{ h.1.core_ok with arena_len_le := h.1.core_ok.arena_len_le }, h.1.scratch_ok⟩,
   { h.2.1 with
     arena := { h.2.1.arena with len_ok := h.2.1.arena.len_ok }
     watches := h.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) },
   h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

private theorem cert_focus_4 {A B C G H S L T : Mem 64 → Prop} {m : Mem 64}
    (h : (A ⋆ B ⋆ (C ⋆ H ⋆ G ⋆ L) ⋆ S ⋆ T) m) :
    (A ⋆ B ⋆ G ⋆ S ⋆ (C ⋆ H ⋆ L ⋆ T)) m := sep_ac h

private theorem cert_unfocus_4 {A B C G H S L T : Mem 64 → Prop} {m : Mem 64}
    (h : (A ⋆ B ⋆ G ⋆ S ⋆ (C ⋆ H ⋆ L) ⋆ T) m) :
    (A ⋆ B ⋆ (C ⋆ H ⋆ G ⋆ L) ⋆ S ⋆ T) m := sep_ac h

theorem cert_focus_addCl_tmp {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (Full.FullMem c s ⋆ R) m) :
    (array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆
      array (t := i32) c.pScratchBuf s.scratch.scratch_buf ⋆
      array (t := i32) c.pGlueUsed s.scratch.glue_used ⋆
      array (t := i32) c.pTmp s.core.tmp ⋆
      (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
        FullCoreByteArrs c s.core ⋆
        (array (t := i32) c.pFlags s.core.flags ⋆ array (t := i32) c.pLevel s.core.lvl ⋆
         array (t := i32) c.pReason s.core.rsns ⋆ array (t := i32) c.pTrail s.core.trl ⋆
         array (t := i32) c.pTrailPos s.core.trail_pos ⋆
         array (t := i32) c.pMinClr s.core.min_clr) ⋆
        FullCoreU32B c s.core ⋆ FullCoreDynArrs c s.core ⋆ FullScrByteArrs c s.scratch ⋆
        FullScrU32A c s.scratch ⋆ FullScrWksArrs c s.scratch ⋆
        (array64 c.pScore s.scratch.score ⋆ array64 c.pSimSig s.scratch.sim_sig ⋆
         array (t := i32) c.pLastLearned s.scratch.last_learned) ⋆
        (array (t := i32) c.pDelayed s.scratch.delayed ⋆
         array (t := i32) c.pRedRefs s.scratch.red_refs ⋆
         array (t := i32) c.pExtendStk s.scratch.extend_stk) ⋆ c.pad ⋆ R)) m := by
  rw [Full.FullMem] at hm
  dsimp [FullCoreArrays, FullCoreU32A, FullScratchArrays, FullScrDynArrs] at hm
  have h1 : (array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆
      array (t := i32) c.pScratchBuf s.scratch.scratch_buf ⋆
      FullScrMetaArrs c s.scratch ⋆ array (t := i32) c.pTmp s.core.tmp ⋆
      (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
       FullCoreByteArrs c s.core ⋆
       (array (t := i32) c.pFlags s.core.flags ⋆ array (t := i32) c.pLevel s.core.lvl ⋆
        array (t := i32) c.pReason s.core.rsns ⋆ array (t := i32) c.pTrail s.core.trl ⋆
        array (t := i32) c.pTrailPos s.core.trail_pos ⋆
        array (t := i32) c.pMinClr s.core.min_clr) ⋆
       FullCoreU32B c s.core ⋆ FullCoreDynArrs c s.core ⋆ FullScrByteArrs c s.scratch ⋆
       FullScrU32A c s.scratch ⋆ FullScrWksArrs c s.scratch ⋆
       (array (t := i32) c.pDelayed s.scratch.delayed ⋆
        array (t := i32) c.pRedRefs s.scratch.red_refs ⋆
        array (t := i32) c.pExtendStk s.scratch.extend_stk) ⋆ c.pad ⋆ R)) m := sep_ac hm
  dsimp [FullScrMetaArrs] at h1
  exact sep_ac (cert_focus_4 h1)

theorem cert_unfocus_addCl_tmp {c : FullCfg} {s : FullState}
    {scr' gu' : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (array64 (c.hdr + 32)
        (Full.hdrTailWords c
          { s with scratch := { s.scratch with scratch_buf := scr', glue_used := gu' } }) ⋆
      array (t := i32) c.pScratchBuf scr' ⋆
      array (t := i32) c.pGlueUsed gu' ⋆
      array (t := i32) c.pTmp s.core.tmp ⋆
      (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
        FullCoreByteArrs c s.core ⋆
        (array (t := i32) c.pFlags s.core.flags ⋆ array (t := i32) c.pLevel s.core.lvl ⋆
         array (t := i32) c.pReason s.core.rsns ⋆ array (t := i32) c.pTrail s.core.trl ⋆
         array (t := i32) c.pTrailPos s.core.trail_pos ⋆
         array (t := i32) c.pMinClr s.core.min_clr) ⋆
        FullCoreU32B c s.core ⋆ FullCoreDynArrs c s.core ⋆ FullScrByteArrs c s.scratch ⋆
        FullScrU32A c s.scratch ⋆ FullScrWksArrs c s.scratch ⋆
        (array64 c.pScore s.scratch.score ⋆ array64 c.pSimSig s.scratch.sim_sig ⋆
         array (t := i32) c.pLastLearned s.scratch.last_learned) ⋆
        (array (t := i32) c.pDelayed s.scratch.delayed ⋆
         array (t := i32) c.pRedRefs s.scratch.red_refs ⋆
         array (t := i32) c.pExtendStk s.scratch.extend_stk) ⋆ c.pad ⋆ R)) m) :
    (Full.FullMem c { s with scratch := { s.scratch with scratch_buf := scr', glue_used := gu' } }
      ⋆ R) m := by
  rw [Full.FullMem]
  dsimp [FullCoreArrays, FullCoreU32A, FullScratchArrays, FullScrDynArrs, FullScrMetaArrs]
  exact sep_ac hm

end

/-! ## 2. Exposed Cert State, Expressions, & Invariants (`def`/`abbrev` only) -/

@[expose] public section

def certMkState (s : FullState) (tmp exp tmk scr : List (BitVec 32)) : FullState :=
  { core := { s.core with tmp := tmp }
    scratch := { s.scratch with wsort := exp, tarjan_mark := tmk, scratch_buf := scr } }

def certMkStateGu (s : FullState) (tmp exp tmk scr gu : List (BitVec 32)) : FullState :=
  { core := { s.core with tmp := tmp }
    scratch := { s.scratch with
      wsort := exp, tarjan_mark := tmk, scratch_buf := scr, glue_used := gu } }

def certModelSet (F_cur : List (List Nat)) (exp : List (BitVec 32))
    (nv unit : Nat) (β : Nat → Bool) : Prop :=
  ∃ α : Nat → Bool, (cnfOfClauses F_cur).Sat α ∧
    ¬ (cnfClause [unit]).Sat α ∧ ∀ i < nv, β i = α (exp[i]?.getD 0#32).toNat

def certExportOk (cur_vars nv : Nat) (tmk exp : List (BitVec 32)) : Prop :=
  (∀ u < cur_vars, tmk[u]?.getD 0#32 ≠ 0#32 →
    1 ≤ (tmk[u]?.getD 0#32).toNat ∧ (tmk[u]?.getD 0#32).toNat ≤ nv ∧
    (exp[(tmk[u]?.getD 0#32).toNat - 1]?.getD 0#32).toNat = u) ∧
  (∀ j < nv, (exp[j]?.getD 0#32).toNat < cur_vars ∧
    (tmk[(exp[j]?.getD 0#32).toNat]?.getD 0#32).toNat = j + 1)

def certUndoInv (cur_vars nv : Nat) (exp tmk : List (BitVec 32)) : Nat → Prop
  | j => ∀ u < cur_vars, tmk[u]?.getD 0#32 ≠ 0#32 →
      ∃ k, j ≤ k ∧ k < nv ∧ (exp[k]?.getD 0#32).toNat = u

abbrev certL1Inv (c : FullCfg) (s : FullState) (R : Mem 64 → Prop) (mv_nat : Nat)
    (nv : BitVec 32) (tmk exp : List (BitVec 32)) (m_n : Mem 64) : Prop :=
  nv.toNat ≤ mv_nat ∧ nv.toNat ≤ s.core.cur_vars ∧ tmk.length = 2 * c.max_vars ∧
  exp.length = 2 * c.max_vars ∧ certExportOk s.core.cur_vars nv.toNat tmk exp ∧
  (Full.FullMem c (certMkState s s.core.tmp exp tmk s.scratch.scratch_buf) ⋆ R) m_n

abbrev certL2Inv (c : FullCfg) (s : FullState) (R : Mem 64 → Prop) (L : K6Layout)
    (P : (Nat → Bool) → Prop) (nv : BitVec 32) (exp tmk : List (BitVec 32)) (ok2 : Bool)
    (tmp' scr' gu' : List (BitVec 32)) (m' : Mem 64) : Prop :=
  tmp'.length = c.max_vars ∧ scr'.length = c.scratch_cap ∧ gu'.length = 64 ∧
  (∀ i < 4192, scr'[i]? = s.scratch.scratch_buf[i]?) ∧
  (ok2 = true → K6Inv L P (k6StateOfScratch L scr') ∧ K6TrailSynced (k6StateOfScratch L scr') ∧
    (k6StateOfScratch L scr').lvl = 0#32 ∧ (k6StateOfScratch L scr').nv = nv ∧
    k6AssumpLitsS L scr' = [] ∧
    K6HwmClean L (gu'[33]?.getD 0#32) (k6StateOfScratch L scr')) ∧
  (Full.FullMem c (certMkStateGu s tmp' exp tmk scr' gu') ⋆ R) m'

def certUndoTmkExpr (pExp pTmk : BitVec 64) (nv : BitVec 32)
    (k : Expr Val Cont [.bool]) : Expr Val Cont [.bool] :=
  Expr.group (fun (Js : Tup Cont [[i32]]) => Blocks.cons (fun j =>
    Expr.let_ ⟨OpCode.cmp CmpOp.ult i32 Ty.bool rfl, (Arg.var j.fst, Arg.var nv, ())⟩ fun pc =>
    Expr.jnz (Arg.var pc.fst)
      (Expr.let_ ⟨OpCode.zext 32 64, (Arg.var j.fst, ())⟩ fun p1 =>
       Expr.let_ ⟨OpCode.mul i64, (Arg.var p1.fst, Arg.imm 4, ())⟩ fun p2 =>
       Expr.let_ ⟨OpCode.add i64, (Arg.var pExp, Arg.var p2.fst, ())⟩ fun p3 =>
       Expr.load i32 (Arg.var p3.fst) fun ld =>
       Expr.let_ ⟨OpCode.zext 32 64, (Arg.var ld, ())⟩ fun p4 =>
       Expr.let_ ⟨OpCode.mul i64, (Arg.var p4.fst, Arg.imm 4, ())⟩ fun p5 =>
       Expr.let_ ⟨OpCode.add i64, (Arg.var pTmk, Arg.var p5.fst, ())⟩ fun p6 =>
       Expr.store (t := i32) (Arg.imm 0) (Arg.var p6.fst)
         (Expr.let_ ⟨OpCode.add i32, (Arg.var j.fst, Arg.imm 1, ())⟩ fun j1 =>
          Expr.jump Js.fst (Arg.var j1.fst, ())))
      k) Blocks.nil) fun Js => Expr.jump Js.fst (Arg.imm 0, ())

def certFinishUnitExpr (pHdr pVals : BitVec 64) (unit : BitVec 32) :
    Expr Val Cont [.bool] :=
  Expr.let_ ⟨OpCode.zext 32 64, (Arg.var unit, ())⟩ fun p1 =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var pVals, Arg.var p1.fst, ())⟩ fun p2 =>
  Expr.load i8 (Arg.var p2.fst) fun ld =>
  Expr.group (fun (_ : Tup Cont [[]]) =>
    Blocks.cons (fun _ => Expr.ret (Arg.imm true, ())) Blocks.nil) fun Js =>
  Expr.let_ ⟨OpCode.trunc 32 8, (Arg.imm 0, ())⟩ fun p3 =>
  Expr.let_ ⟨OpCode.sext 8 32, (Arg.var ld, ())⟩ fun p4 =>
  Expr.let_ ⟨OpCode.sext 8 32, (Arg.var p3.fst, ())⟩ fun p5 =>
  Expr.let_ ⟨OpCode.cmp CmpOp.slt i32 Ty.bool rfl, (Arg.var p4.fst, Arg.var p5.fst, ())⟩ fun p6 =>
  Expr.jnz (Arg.var p6.fst)
    (Expr.let_ ⟨OpCode.add i64, (Arg.var pHdr, Arg.imm 1024, ())⟩ fun p7 =>
     Expr.store (t := i64) (Arg.imm 1) (Arg.var p7.fst) (Expr.jump Js.fst ()))
    (Expr.group (fun (_ : Tup Cont [[]]) =>
       Blocks.cons (fun _ => Expr.jump Js.fst ()) Blocks.nil) fun Js1 =>
     Expr.let_ ⟨OpCode.trunc 32 8, (Arg.imm 0, ())⟩ fun p7 =>
     Expr.let_ ⟨OpCode.sext 8 32, (Arg.var ld, ())⟩ fun p8 =>
     Expr.let_ ⟨OpCode.sext 8 32, (Arg.var p7.fst, ())⟩ fun p9 =>
     Expr.let_ ⟨OpCode.cmp CmpOp.eq i32 Ty.bool rfl,
         (Arg.var p8.fst, Arg.var p9.fst, ())⟩ fun p10 =>
     Expr.jnz (Arg.var p10.fst)
       (Expr.call (as := [i64, i32, i32, i32]) (bs := []) "full_assign_lvl"
         (Arg.var pHdr, Arg.var unit, Arg.imm 4294967295, Arg.imm 0, ()) fun _ =>
        Expr.jump Js1.fst ())
       (Expr.jump Js1.fst ()))

def certPostLoop2Expr (pHdr pVals : BitVec 64) (unit : BitVec 32)
    (ok2 : Bool) : Expr Val Cont [.bool] :=
  Expr.jnz (Arg.var ok2)
    (Expr.let_ ⟨OpCode.zext 32 64, (Arg.imm 1000000, ())⟩ fun p1 =>
     Expr.call (as := [i64, i64]) (bs := [i64]) "full_k6_solve"
       (Arg.var pHdr, Arg.var p1.fst, ()) fun p2 =>
     Expr.let_ ⟨OpCode.cmp CmpOp.ne i64 Ty.bool rfl, (Arg.var p2.fst, Arg.imm 20, ())⟩ fun p3 =>
     Expr.jnz (Arg.var p3.fst) (Expr.ret (Arg.imm false, ())) (certFinishUnitExpr pHdr pVals unit))
    (Expr.ret (Arg.imm false, ()))

def certLoop2LargeExpr (Js : Cont [.bool, .bool, i32, i32])
    (pAr pVals pTmk pTmp : BitVec 64) (w lsz unit nv max_csz : BitVec 32)
    (ok2 : Bool) : Expr Val Cont [.bool] :=
  Expr.group (fun (Js4 : Tup Cont [[i32, i32]]) => Blocks.cons (fun p39 =>
    Expr.let_ ⟨OpCode.cmp CmpOp.ult i32 Ty.bool rfl,
        (Arg.var p39.snd.fst, Arg.var lsz, ())⟩ fun p40 =>
    Expr.jnz (Arg.var p40.fst)
      (Expr.let_ ⟨OpCode.zext 32 64, (Arg.var w, ())⟩ fun p41 =>
       Expr.let_ ⟨OpCode.add i64, (Arg.var p41.fst, Arg.imm 3, ())⟩ fun p42 =>
       Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p39.snd.fst, ())⟩ fun p43 =>
       Expr.let_ ⟨OpCode.add i64, (Arg.var p42.fst, Arg.var p43.fst, ())⟩ fun p44 =>
       Expr.let_ ⟨OpCode.mul i64, (Arg.var p44.fst, Arg.imm 4, ())⟩ fun p45 =>
       Expr.let_ ⟨OpCode.add i64, (Arg.var pAr, Arg.var p45.fst, ())⟩ fun p46 =>
       Expr.load i32 (Arg.var p46.fst) fun ld =>
       Expr.group (fun (_ : Tup Cont [[.bool, .bool, i32]]) => Blocks.cons (fun p =>
         Expr.let_ ⟨OpCode.add i32, (Arg.var p39.snd.fst, Arg.imm 1, ())⟩ fun p47 =>
         Expr.jump Js4.fst (Arg.var p.snd.snd.fst, Arg.var p47.fst, ())) Blocks.nil) fun Js5 =>
       Expr.let_ ⟨OpCode.cmp CmpOp.ne i32 Ty.bool rfl, (Arg.var ld, Arg.var unit, ())⟩ fun p =>
       Expr.jnz (Arg.var p.fst)
         (Expr.let_ ⟨OpCode.zext 32 64, (Arg.var ld, ())⟩ fun p =>
          Expr.let_ ⟨OpCode.add i64, (Arg.var pVals, Arg.var p.fst, ())⟩ fun p =>
          Expr.load i8 (Arg.var p.fst) fun ld9 =>
          Expr.let_ ⟨OpCode.trunc 32 8, (Arg.imm 0, ())⟩ fun p =>
          Expr.let_ ⟨OpCode.sext 8 32, (Arg.var ld9, ())⟩ fun p47 =>
          Expr.let_ ⟨OpCode.sext 8 32, (Arg.var p.fst, ())⟩ fun p =>
          Expr.let_ ⟨OpCode.cmp CmpOp.sgt i32 Ty.bool rfl, (Arg.var p47.fst, Arg.var p.fst, ())⟩
            fun p =>
          Expr.jnz (Arg.var p.fst)
            (Expr.jump Js (Arg.var ok2, Arg.imm true, Arg.var p39.fst, Arg.var p39.snd.fst, ()))
            (Expr.group (fun (_ : Tup Cont [[.bool, i32]]) => Blocks.cons (fun p =>
               Expr.jump Js5.fst (Arg.var p.fst, Arg.imm false, Arg.var p.snd.fst, ()))
               Blocks.nil) fun Js6 =>
             Expr.let_ ⟨OpCode.trunc 32 8, (Arg.imm 0, ())⟩ fun p =>
             Expr.let_ ⟨OpCode.sext 8 32, (Arg.var ld9, ())⟩ fun p48 =>
             Expr.let_ ⟨OpCode.sext 8 32, (Arg.var p.fst, ())⟩ fun p =>
             Expr.let_ ⟨OpCode.cmp CmpOp.eq i32 Ty.bool rfl, (Arg.var p48.fst, Arg.var p.fst, ())⟩
               fun p =>
             Expr.jnz (Arg.var p.fst)
               (Expr.let_ ⟨OpCode.lshr i32, (Arg.var ld, Arg.imm 1, ())⟩ fun p =>
                Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p.fst, ())⟩ fun p =>
                Expr.let_ ⟨OpCode.mul i64, (Arg.var p.fst, Arg.imm 4, ())⟩ fun p =>
                Expr.let_ ⟨OpCode.add i64, (Arg.var pTmk, Arg.var p.fst, ())⟩ fun p =>
                Expr.load i32 (Arg.var p.fst) fun ld10 =>
                Expr.let_ ⟨OpCode.cmp CmpOp.eq i32 Ty.bool rfl, (Arg.var ld10, Arg.imm 0, ())⟩
                  fun p =>
                Expr.jnz (Arg.var p.fst)
                  (Expr.jump Js
                    (Arg.imm false, Arg.imm false, Arg.var p39.fst, Arg.var p39.snd.fst, ()))
                  (Expr.let_ ⟨OpCode.cmp CmpOp.ugt i32 Ty.bool rfl, (Arg.var ld10, Arg.var nv, ())⟩
                     fun p =>
                   Expr.jnz (Arg.var p.fst)
                     (Expr.jump Js
                       (Arg.imm false, Arg.imm false, Arg.var p39.fst, Arg.var p39.snd.fst, ()))
                     (Expr.let_ ⟨OpCode.cmp CmpOp.uge i32 Ty.bool rfl,
                          (Arg.var p39.fst, Arg.var max_csz, ())⟩ fun p =>
                      Expr.jnz (Arg.var p.fst)
                        (Expr.jump Js
                          (Arg.imm false, Arg.imm false, Arg.var p39.fst, Arg.var p39.snd.fst, ()))
                        (Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p39.fst, ())⟩ fun p =>
                         Expr.let_ ⟨OpCode.mul i64, (Arg.var p.fst, Arg.imm 4, ())⟩ fun p =>
                         Expr.let_ ⟨OpCode.add i64, (Arg.var pTmp, Arg.var p.fst, ())⟩ fun p =>
                         Expr.let_ ⟨OpCode.sub i32, (Arg.var ld10, Arg.imm 1, ())⟩ fun p49 =>
                         Expr.let_ ⟨OpCode.shl i32, (Arg.var p49.fst, Arg.imm 1, ())⟩ fun p50 =>
                         Expr.let_ ⟨OpCode.and i32, (Arg.var ld, Arg.imm 1, ())⟩ fun p51 =>
                         Expr.let_ ⟨OpCode.or i32, (Arg.var p50.fst, Arg.var p51.fst, ())⟩
                           fun p52 =>
                         Expr.store (t := i32) (Arg.var p52.fst) (Arg.var p.fst)
                           (Expr.let_ ⟨OpCode.add i32, (Arg.var p39.fst, Arg.imm 1, ())⟩ fun p =>
                            Expr.jump Js6.fst (Arg.var ok2, Arg.var p.fst, ()))))))
               (Expr.jump Js6.fst (Arg.var ok2, Arg.var p39.fst, ()))))
         (Expr.jump Js5.fst (Arg.var ok2, Arg.imm false, Arg.var p39.fst, ())))
      (Expr.jump Js (Arg.var ok2, Arg.imm false, Arg.var p39.fst, Arg.var p39.snd.fst, ())))
    Blocks.nil) fun Js4 => Expr.jump Js4.fst (Arg.imm 0, Arg.imm 0, ())

def certLoop1LargeExpr (Js : Cont [i32, .bool, .bool, i32, i32])
    (pHdr pAr pVals pTmk pExp : BitVec 64) (w lsz unit nv mv : BitVec 32)
    (ab : Bool) : Expr Val Cont [.bool] :=
  Expr.group (fun (Js4 : Tup Cont [[i32, i32, i32]]) => Blocks.cons (fun p32 =>
    Expr.let_ ⟨OpCode.cmp CmpOp.ult i32 Ty.bool rfl, (Arg.var p32.snd.snd.fst, Arg.var lsz, ())⟩
      fun p33 =>
    Expr.jnz (Arg.var p33.fst)
      (Expr.let_ ⟨OpCode.zext 32 64, (Arg.var w, ())⟩ fun p34 =>
       Expr.let_ ⟨OpCode.add i64, (Arg.var p34.fst, Arg.imm 3, ())⟩ fun p35 =>
       Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p32.snd.snd.fst, ())⟩ fun p36 =>
       Expr.let_ ⟨OpCode.add i64, (Arg.var p35.fst, Arg.var p36.fst, ())⟩ fun p37 =>
       Expr.let_ ⟨OpCode.mul i64, (Arg.var p37.fst, Arg.imm 4, ())⟩ fun p38 =>
       Expr.let_ ⟨OpCode.add i64, (Arg.var pAr, Arg.var p38.fst, ())⟩ fun p39 =>
       Expr.load i32 (Arg.var p39.fst) fun ld =>
       Expr.group (fun (_ : Tup Cont [[i32, .bool, .bool, i32]]) => Blocks.cons (fun p =>
         Expr.let_ ⟨OpCode.add i32, (Arg.var p32.snd.snd.fst, Arg.imm 1, ())⟩ fun p40 =>
         Expr.jump Js4.fst (Arg.var p.fst, Arg.var p.snd.snd.snd.fst, Arg.var p40.fst, ()))
         Blocks.nil) fun Js5 =>
       Expr.let_ ⟨OpCode.cmp CmpOp.ne i32 Ty.bool rfl, (Arg.var ld, Arg.var unit, ())⟩ fun p40 =>
       Expr.jnz (Arg.var p40.fst)
         (Expr.let_ ⟨OpCode.zext 32 64, (Arg.var ld, ())⟩ fun p41 =>
          Expr.let_ ⟨OpCode.add i64, (Arg.var pVals, Arg.var p41.fst, ())⟩ fun p42 =>
          Expr.load i8 (Arg.var p42.fst) fun ld9 =>
          Expr.let_ ⟨OpCode.trunc 32 8, (Arg.imm 0, ())⟩ fun p43 =>
          Expr.let_ ⟨OpCode.sext 8 32, (Arg.var ld9, ())⟩ fun p44 =>
          Expr.let_ ⟨OpCode.sext 8 32, (Arg.var p43.fst, ())⟩ fun p45 =>
          Expr.let_ ⟨OpCode.cmp CmpOp.sgt i32 Ty.bool rfl, (Arg.var p44.fst, Arg.var p45.fst, ())⟩
            fun p46 =>
          Expr.jnz (Arg.var p46.fst)
            (Expr.jump Js (Arg.var p32.fst, Arg.var ab, Arg.imm true,
              Arg.var p32.snd.fst, Arg.var p32.snd.snd.fst, ()))
            (Expr.group (fun (_ : Tup Cont [[i32, .bool, i32]]) => Blocks.cons (fun p =>
               Expr.jump Js5.fst (Arg.var p.fst, Arg.var p.snd.fst, Arg.imm false,
                 Arg.var p.snd.snd.fst, ())) Blocks.nil) fun Js6 =>
             Expr.let_ ⟨OpCode.trunc 32 8, (Arg.imm 0, ())⟩ fun p47 =>
             Expr.let_ ⟨OpCode.sext 8 32, (Arg.var ld9, ())⟩ fun p48 =>
             Expr.let_ ⟨OpCode.sext 8 32, (Arg.var p47.fst, ())⟩ fun p49 =>
             Expr.let_ ⟨OpCode.cmp CmpOp.eq i32 Ty.bool rfl, (Arg.var p48.fst, Arg.var p49.fst, ())⟩
               fun p50 =>
             Expr.jnz (Arg.var p50.fst)
               (Expr.let_ ⟨OpCode.lshr i32, (Arg.var ld, Arg.imm 1, ())⟩ fun p51 =>
                Expr.group (fun (_ : Tup Cont [[i32, .bool]]) => Blocks.cons (fun p =>
                  Expr.let_ ⟨OpCode.add i32, (Arg.var p32.snd.fst, Arg.imm 1, ())⟩ fun p52 =>
                  Expr.jump Js6.fst (Arg.var p.fst, Arg.var p.snd.fst, Arg.var p52.fst, ()))
                  Blocks.nil) fun Js7 =>
                Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p51.fst, ())⟩ fun p52 =>
                Expr.let_ ⟨OpCode.mul i64, (Arg.var p52.fst, Arg.imm 4, ())⟩ fun p53 =>
                Expr.let_ ⟨OpCode.add i64, (Arg.var pTmk, Arg.var p53.fst, ())⟩ fun p54 =>
                Expr.load i32 (Arg.var p54.fst) fun ld10 =>
                Expr.let_ ⟨OpCode.cmp CmpOp.eq i32 Ty.bool rfl, (Arg.var ld10, Arg.imm 0, ())⟩
                  fun p55 =>
                Expr.jnz (Arg.var p55.fst)
                  (Expr.let_ ⟨OpCode.cmp CmpOp.uge i32 Ty.bool rfl,
                      (Arg.var p32.fst, Arg.var mv, ())⟩ fun p56 =>
                   Expr.jnz (Arg.var p56.fst)
                     (Expr.jump Js (Arg.var p32.fst, Arg.imm true, Arg.imm false,
                       Arg.var p32.snd.fst, Arg.var p32.snd.snd.fst, ()))
                     (Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p32.fst, ())⟩ fun p57 =>
                      Expr.let_ ⟨OpCode.add i64, (Arg.var pHdr, Arg.imm 776, ())⟩ fun p =>
                      Expr.load i64 (Arg.var p.fst) fun ld11 =>
                      Expr.let_ ⟨OpCode.cmp CmpOp.uge i64 Ty.bool rfl,
                          (Arg.var p57.fst, Arg.var ld11, ())⟩ fun p =>
                      Expr.jnz (Arg.var p.fst)
                        (Expr.jump Js (Arg.var p32.fst, Arg.imm true, Arg.imm false,
                          Arg.var p32.snd.fst, Arg.var p32.snd.snd.fst, ()))
                        (Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p32.fst, ())⟩ fun p =>
                         Expr.let_ ⟨OpCode.mul i64, (Arg.var p.fst, Arg.imm 4, ())⟩ fun p =>
                         Expr.let_ ⟨OpCode.add i64, (Arg.var pExp, Arg.var p.fst, ())⟩ fun p =>
                         Expr.store (t := i32) (Arg.var p51.fst) (Arg.var p.fst)
                           (Expr.let_ ⟨OpCode.add i32, (Arg.var p32.fst, Arg.imm 1, ())⟩ fun p =>
                            Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p51.fst, ())⟩ fun p58 =>
                            Expr.let_ ⟨OpCode.mul i64, (Arg.var p58.fst, Arg.imm 4, ())⟩ fun p59 =>
                            Expr.let_ ⟨OpCode.add i64, (Arg.var pTmk, Arg.var p59.fst, ())⟩
                              fun p60 =>
                            Expr.store (t := i32) (Arg.var p.fst) (Arg.var p60.fst)
                              (Expr.jump Js7.fst (Arg.var p.fst, Arg.var ab, ()))))))
                  (Expr.jump Js7.fst (Arg.var p32.fst, Arg.var ab, ())))
               (Expr.jump Js6.fst (Arg.var p32.fst, Arg.var ab, Arg.var p32.snd.fst, ()))))
         (Expr.jump Js5.fst (Arg.var p32.fst, Arg.var ab, Arg.imm false, Arg.var p32.snd.fst, ())))
      (Expr.jump Js (Arg.var p32.fst, Arg.var ab, Arg.imm false,
        Arg.var p32.snd.fst, Arg.var p32.snd.snd.fst, ())))
    Blocks.nil) fun Js4 => Expr.jump Js4.fst (Arg.var nv, Arg.imm 0, Arg.imm 0, ())

def certLoop1Expr (Js : Cont [i32, .bool, .bool, i32])
    (pHdr pScr pAr pVals pTmk pExp : BitVec 64)
    (unit side_off side_cnt side_mask mv max_csz : BitVec 32) : Expr Val Cont [.bool] :=
  Expr.group (fun (Js1 : Tup Cont [[i32, .bool, i32]]) => Blocks.cons (fun p11 =>
    Expr.let_ ⟨OpCode.cmp CmpOp.ult i32 Ty.bool rfl,
        (Arg.var p11.snd.snd.fst, Arg.var side_cnt, ())⟩ fun p12 =>
    Expr.jnz (Arg.var p12.fst)
      (Expr.jnz (Arg.imm false)
        (Expr.jump Js (Arg.var p11.fst, Arg.imm false, Arg.var p11.snd.fst, Arg.var p11.snd.snd.fst,
          ()))
        (Expr.jnz (Arg.var p11.snd.fst)
          (Expr.jump Js (Arg.var p11.fst, Arg.imm false,
            Arg.var p11.snd.fst, Arg.var p11.snd.snd.fst, ()))
          (Expr.group (fun (_ : Tup Cont [[i32, .bool, .bool]]) => Blocks.cons (fun p =>
             Expr.let_ ⟨OpCode.add i32, (Arg.var p11.snd.snd.fst, Arg.imm 1, ())⟩ fun p13 =>
             Expr.jump Js1.fst (Arg.var p.fst, Arg.var p.snd.snd.fst, Arg.var p13.fst, ()))
             Blocks.nil) fun Js2 =>
           Expr.let_ ⟨OpCode.lshr i32, (Arg.var p11.snd.snd.fst, Arg.imm 5, ())⟩ fun p13 =>
           Expr.let_ ⟨OpCode.add i32, (Arg.var side_mask, Arg.var p13.fst, ())⟩ fun p14 =>
           Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p14.fst, ())⟩ fun p15 =>
           Expr.let_ ⟨OpCode.mul i64, (Arg.var p15.fst, Arg.imm 4, ())⟩ fun p16 =>
           Expr.let_ ⟨OpCode.add i64, (Arg.var pScr, Arg.var p16.fst, ())⟩ fun p17 =>
           Expr.load i32 (Arg.var p17.fst) fun ld7 =>
           Expr.let_ ⟨OpCode.and i32, (Arg.var p11.snd.snd.fst, Arg.imm 31, ())⟩ fun p18 =>
           Expr.let_ ⟨OpCode.lshr i32, (Arg.var ld7, Arg.var p18.fst, ())⟩ fun p19 =>
           Expr.let_ ⟨OpCode.and i32, (Arg.var p19.fst, Arg.imm 1, ())⟩ fun p20 =>
           Expr.let_ ⟨OpCode.cmp CmpOp.ne i32 Ty.bool rfl,
               (Arg.var p20.fst, Arg.imm 0, ())⟩ fun p21 =>
           Expr.jnz (Arg.var p21.fst)
             (Expr.let_ ⟨OpCode.add i32, (Arg.var side_off, Arg.var p11.snd.snd.fst, ())⟩ fun p22 =>
              Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p22.fst, ())⟩ fun p23 =>
              Expr.let_ ⟨OpCode.mul i64, (Arg.var p23.fst, Arg.imm 4, ())⟩ fun p24 =>
              Expr.let_ ⟨OpCode.add i64, (Arg.var pScr, Arg.var p24.fst, ())⟩ fun p25 =>
              Expr.load i32 (Arg.var p25.fst) fun ld =>
              Expr.group (fun (_ : Tup Cont [[i32, .bool, .bool]]) => Blocks.cons (fun p =>
                Expr.jump Js2.fst (Arg.var p.fst, Arg.var p.snd.fst, Arg.var p.snd.snd.fst, ()))
                Blocks.nil) fun Js3 =>
              Expr.let_ ⟨OpCode.and i32, (Arg.var ld, Arg.imm 2147483648, ())⟩ fun p26 =>
              Expr.let_ ⟨OpCode.cmp CmpOp.ne i32 Ty.bool rfl, (Arg.var p26.fst, Arg.imm 0, ())⟩
                fun p27 =>
              Expr.jnz (Arg.var p27.fst)
                (Expr.let_ ⟨OpCode.and i32, (Arg.var ld, Arg.imm 2147483647, ())⟩ fun p28 =>
                 Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p28.fst, ())⟩ fun p29 =>
                 Expr.let_ ⟨OpCode.add i64, (Arg.var pVals, Arg.var p29.fst, ())⟩ fun p30 =>
                 Expr.load i8 (Arg.var p30.fst) fun ld =>
                 Expr.let_ ⟨OpCode.trunc 32 8, (Arg.imm 0, ())⟩ fun p31 =>
                 Expr.let_ ⟨OpCode.sext 8 32, (Arg.var ld, ())⟩ fun p32 =>
                 Expr.let_ ⟨OpCode.sext 8 32, (Arg.var p31.fst, ())⟩ fun p33 =>
                 Expr.let_ ⟨OpCode.cmp CmpOp.slt i32 Ty.bool rfl,
                     (Arg.var p32.fst, Arg.var p33.fst, ())⟩ fun p34 =>
                 Expr.jnz (Arg.var p34.fst)
                   (Expr.jump Js (Arg.var p11.fst, Arg.imm true,
                     Arg.var p11.snd.fst, Arg.var p11.snd.snd.fst, ()))
                   (Expr.group (fun (_ : Tup Cont [[i32, .bool]]) => Blocks.cons (fun p =>
                      Expr.jump Js3.fst (Arg.var p.fst, Arg.imm false, Arg.var p.snd.fst, ()))
                      Blocks.nil) fun Js4 =>
                    Expr.let_ ⟨OpCode.trunc 32 8, (Arg.imm 0, ())⟩ fun p35 =>
                    Expr.let_ ⟨OpCode.sext 8 32, (Arg.var ld, ())⟩ fun p36 =>
                    Expr.let_ ⟨OpCode.sext 8 32, (Arg.var p35.fst, ())⟩ fun p37 =>
                    Expr.let_ ⟨OpCode.cmp CmpOp.eq i32 Ty.bool rfl,
                        (Arg.var p36.fst, Arg.var p37.fst, ())⟩ fun p38 =>
                    Expr.jnz (Arg.var p38.fst)
                      (Expr.let_ ⟨OpCode.lshr i32, (Arg.var p28.fst, Arg.imm 1, ())⟩ fun p39 =>
                       Expr.group (fun (_ : Tup Cont [[i32, .bool]]) => Blocks.cons (fun p =>
                         Expr.jump Js4.fst (Arg.var p.fst, Arg.var p.snd.fst, ())) Blocks.nil)
                         fun Js5 =>
                       Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p39.fst, ())⟩ fun p40 =>
                       Expr.let_ ⟨OpCode.mul i64, (Arg.var p40.fst, Arg.imm 4, ())⟩ fun p41 =>
                       Expr.let_ ⟨OpCode.add i64, (Arg.var pTmk, Arg.var p41.fst, ())⟩ fun p42 =>
                       Expr.load i32 (Arg.var p42.fst) fun ld =>
                       Expr.let_ ⟨OpCode.cmp CmpOp.eq i32 Ty.bool rfl, (Arg.var ld, Arg.imm 0, ())⟩
                         fun p43 =>
                       Expr.jnz (Arg.var p43.fst)
                         (Expr.let_ ⟨OpCode.cmp CmpOp.uge i32 Ty.bool rfl,
                              (Arg.var p11.fst, Arg.var mv, ())⟩ fun p44 =>
                          Expr.jnz (Arg.var p44.fst)
                            (Expr.jump Js (Arg.var p11.fst, Arg.imm false,
                              Arg.imm true, Arg.var p11.snd.snd.fst, ()))
                            (Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p11.fst, ())⟩ fun p45 =>
                             Expr.let_ ⟨OpCode.add i64, (Arg.var pHdr, Arg.imm 776, ())⟩ fun p =>
                             Expr.load i64 (Arg.var p.fst) fun ld =>
                             Expr.let_ ⟨OpCode.cmp CmpOp.uge i64 Ty.bool rfl,
                                 (Arg.var p45.fst, Arg.var ld, ())⟩ fun p =>
                             Expr.jnz (Arg.var p.fst)
                               (Expr.jump Js (Arg.var p11.fst, Arg.imm false,
                                 Arg.imm true, Arg.var p11.snd.snd.fst, ()))
                               (Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p11.fst, ())⟩ fun p =>
                                Expr.let_ ⟨OpCode.mul i64, (Arg.var p.fst, Arg.imm 4, ())⟩ fun p =>
                                Expr.let_ ⟨OpCode.add i64, (Arg.var pExp, Arg.var p.fst, ())⟩
                                  fun p =>
                                Expr.store (t := i32) (Arg.var p39.fst) (Arg.var p.fst)
                                  (Expr.let_ ⟨OpCode.add i32, (Arg.var p11.fst, Arg.imm 1, ())⟩
                                     fun p =>
                                   Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p39.fst, ())⟩ fun p46 =>
                                   Expr.let_ ⟨OpCode.mul i64, (Arg.var p46.fst, Arg.imm 4, ())⟩
                                     fun p47 =>
                                   Expr.let_ ⟨OpCode.add i64, (Arg.var pTmk, Arg.var p47.fst, ())⟩
                                     fun p48 =>
                                   Expr.store (t := i32) (Arg.var p.fst) (Arg.var p48.fst)
                                     (Expr.jump Js5.fst
                                       (Arg.var p.fst, Arg.var p11.snd.fst, ()))))))
                         (Expr.jump Js5.fst (Arg.var p11.fst, Arg.var p11.snd.fst, ())))
                      (Expr.jump Js4.fst (Arg.var p11.fst, Arg.var p11.snd.fst, ()))))
                (Expr.let_ ⟨OpCode.zext 32 64, (Arg.var ld, ())⟩ fun p28 =>
                 Expr.let_ ⟨OpCode.add i64, (Arg.var p28.fst, Arg.imm 2, ())⟩ fun p29 =>
                 Expr.let_ ⟨OpCode.mul i64, (Arg.var p29.fst, Arg.imm 4, ())⟩ fun p30 =>
                 Expr.let_ ⟨OpCode.add i64, (Arg.var pAr, Arg.var p30.fst, ())⟩ fun p31 =>
                 Expr.load i32 (Arg.var p31.fst) fun ld8 =>
                 Expr.group (fun (_ : Tup Cont [[i32, .bool, .bool, i32, i32]]) =>
                   Blocks.cons (fun p =>
                     Expr.jnz (Arg.var p.snd.fst)
                       (Expr.jump Js (Arg.var p.fst, Arg.imm false,
                         Arg.var p.snd.fst, Arg.var p11.snd.snd.fst, ()))
                       (Expr.group (fun (_ : Tup Cont [[.bool, .bool]]) => Blocks.cons (fun p32 =>
                          Expr.jump Js3.fst
                            (Arg.var p.fst, Arg.var p32.fst, Arg.var p32.snd.fst, ()))
                          Blocks.nil) fun Js5 =>
                        Expr.jnz (Arg.var p.snd.snd.fst)
                          (Expr.jump Js5.fst (Arg.imm false, Arg.var p.snd.fst, ()))
                          (Expr.let_ ⟨OpCode.cmp CmpOp.eq i32 Ty.bool rfl,
                              (Arg.var p.snd.snd.snd.fst, Arg.imm 0, ())⟩ fun p32 =>
                           Expr.jnz (Arg.var p32.fst)
                             (Expr.jump Js (Arg.var p.fst, Arg.imm true,
                               Arg.var p.snd.fst, Arg.var p11.snd.snd.fst, ()))
                             (Expr.let_ ⟨OpCode.cmp CmpOp.ugt i32 Ty.bool rfl,
                                 (Arg.var p.snd.snd.snd.fst, Arg.var max_csz, ())⟩ fun p33 =>
                              Expr.jnz (Arg.var p33.fst)
                                (Expr.jump Js (Arg.var p.fst, Arg.imm false,
                                  Arg.imm true, Arg.var p11.snd.snd.fst, ()))
                                (Expr.jump Js5.fst (Arg.imm false, Arg.var p.snd.fst, ()))))))
                     Blocks.nil)
                   fun Js4 => certLoop1LargeExpr Js4.fst pHdr pAr pVals pTmk pExp
                     ld ld8 unit p11.fst mv p11.snd.fst))
             (Expr.jump Js2.fst (Arg.var p11.fst, Arg.imm false, Arg.var p11.snd.fst, ())))))
      (Expr.jump Js (Arg.var p11.fst, Arg.imm false, Arg.var p11.snd.fst, Arg.var p11.snd.snd.fst,
        ())))
    Blocks.nil) fun Js1 => Expr.jump Js1.fst (Arg.imm 0, Arg.imm false, Arg.imm 0, ())

end

/-! ## 3. Scoped `CertMkTactics` & Export/Model Helpers -/

public section

namespace CertMkTactics
@[scoped bv_c0] theorem certMkState_vals (s : FullState) (t e k r : List (BitVec 32)) :
    (certMkState s t e k r).core.vals = s.core.vals := by unfold certMkState; rfl
@[scoped bv_c0] theorem certMkState_tmp (s : FullState) (t e k r : List (BitVec 32)) :
    (certMkState s t e k r).core.tmp = t := by unfold certMkState; rfl
@[scoped bv_c0] theorem certMkState_arena (s : FullState) (t e k r : List (BitVec 32)) :
    (certMkState s t e k r).core.arena = s.core.arena := by unfold certMkState; rfl
@[scoped bv_c0] theorem certMkState_wsort (s : FullState) (t e k r : List (BitVec 32)) :
    (certMkState s t e k r).scratch.wsort = e := by unfold certMkState; rfl
@[scoped bv_c0] theorem certMkState_tmk (s : FullState) (t e k r : List (BitVec 32)) :
    (certMkState s t e k r).scratch.tarjan_mark = k := by unfold certMkState; rfl
@[scoped bv_c0] theorem certMkState_buf (s : FullState) (t e k r : List (BitVec 32)) :
    (certMkState s t e k r).scratch.scratch_buf = r := by unfold certMkState; rfl
@[scoped bv_c0] theorem certMkState_upd_tmk (s : FullState) (t e k k' r : List (BitVec 32)) :
    { certMkState s t e k r with
      scratch := { (certMkState s t e k r).scratch with tarjan_mark := k' } } =
      certMkState s t e k' r := by unfold certMkState; rfl
@[scoped bv_c0] theorem certMkState_upd_tmp (s : FullState) (t t' e k r : List (BitVec 32)) :
    { certMkState s t e k r with
      core := { (certMkState s t e k r).core with tmp := t' } } =
      certMkState s t' e k r := by unfold certMkState; rfl
@[scoped bv_c0] theorem certMkState_upd_exp (s : FullState) (t e e' k r : List (BitVec 32)) :
    { certMkState s t e k r with
      scratch := { (certMkState s t e k r).scratch with wsort := e' } } =
      certMkState s t e' k r := by unfold certMkState; rfl
@[scoped bv_c0] theorem certMkStateGu_buf (s : FullState) (t e k r g : List (BitVec 32)) :
    (certMkStateGu s t e k r g).scratch.scratch_buf = r := by unfold certMkStateGu; rfl
@[scoped bv_c0] theorem certMkStateGu_tmk (s : FullState) (t e k r g : List (BitVec 32)) :
    (certMkStateGu s t e k r g).scratch.tarjan_mark = k := by unfold certMkStateGu; rfl
@[scoped bv_c0] theorem certMkStateGu_tmp (s : FullState) (t e k r g : List (BitVec 32)) :
    (certMkStateGu s t e k r g).core.tmp = t := by unfold certMkStateGu; rfl
@[scoped bv_c0] theorem certMkStateGu_arena (s : FullState) (t e k r g : List (BitVec 32)) :
    (certMkStateGu s t e k r g).core.arena = s.core.arena := by unfold certMkStateGu; rfl
@[scoped bv_c0] theorem certMkStateGu_vals (s : FullState) (t e k r g : List (BitVec 32)) :
    (certMkStateGu s t e k r g).core.vals = s.core.vals := by unfold certMkStateGu; rfl
end CertMkTactics

open scoped CertMkTactics
open CertMkTactics

theorem cert_modelSet_unsat_entails {F_cur : List (List Nat)}
    {exp : List (BitVec 32)} {nv unit : Nat}
    (hunsat : ∀ β : Nat → Bool, ¬ certModelSet F_cur exp nv unit β) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause [unit]) := by
  rw [CNF.entails_clause_def]; intro α hsat
  exact Classical.byContradiction fun hnsat =>
    hunsat (fun i => α (exp[i]?.getD 0#32).toNat) ⟨α, hsat, hnsat, fun _ _ => rfl⟩

theorem cert_entails_in_modelSet {F_cur : List (List Nat)} {lits : List Nat}
    {unit : Nat} (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause lits))
    {α : Nat → Bool} (hsat : (cnfOfClauses F_cur).Sat α)
    (hnu : ¬ (cnfClause [unit]).Sat α) :
    ∃ q ∈ lits, q ≠ unit ∧ (cnfClause [q]).Sat α := by
  rw [CNF.entails_clause_def] at hent
  rcases (cert_clause_sat_iff_mem lits α).mp (hent α hsat) with ⟨q, hq, hqs⟩
  exact ⟨q, hq, fun heq => hnu (heq ▸ hqs), hqs⟩

theorem cert_mapped_lit_sat {α β : Nat → Bool} {exp : List (BitVec 32)}
    {nv loc q : Nat} (hloc1 : 1 ≤ loc) (hloc2 : loc ≤ nv)
    (hexp : (exp[loc - 1]?.getD 0#32).toNat = q / 2)
    (hmap : ∀ i < nv, β i = α (exp[i]?.getD 0#32).toNat)
    {ml : Nat} (hml_div : ml / 2 = loc - 1) (hml_mod : ml % 2 = q % 2)
    (hqs : (cnfClause [q]).Sat α) : (cnfClause [ml]).Sat β := by
  rw [cert_clause_unit_sat_iff] at hqs ⊢
  rw [hml_div, hml_mod, hmap (loc - 1) (by omega), hexp]; exact hqs

theorem cert_export_zero {cur_vars : Nat} {tmk exp : List (BitVec 32)}
    (htmk : ∀ u < cur_vars, tmk[u]?.getD 0#32 = 0#32) :
    certExportOk cur_vars 0 tmk exp :=
  ⟨fun u hu hnz => absurd (htmk u hu) hnz, fun _ hj => absurd hj (Nat.not_lt_zero _)⟩

private theorem cert_export_add {cur_vars nv u0 : Nat} {tmk exp : List (BitVec 32)}
    (hok : certExportOk cur_vars nv tmk exp) (hu0 : u0 < cur_vars)
    (ht0 : tmk[u0]?.getD 0#32 = 0#32) (hnv_lt : nv < exp.length) (hu0_lt : u0 < tmk.length)
    (hinv_bound : nv + 1 < 2 ^ 32) (hu0_bound : u0 < 2 ^ 32) :
    certExportOk cur_vars (nv + 1)
      (tmk.set u0 (BitVec.ofNat 32 (nv + 1))) (exp.set nv (BitVec.ofNat 32 u0)) := by
  refine ⟨fun u hu hnz => ?_, fun j hj => ?_⟩
  · by_cases hueq : u = u0
    · subst hueq
      have hget : (tmk.set u (BitVec.ofNat 32 (nv + 1)))[u]?.getD 0#32 =
          BitVec.ofNat 32 (nv + 1) := by simp [hu0_lt]
      have hto : (BitVec.ofNat 32 (nv + 1)).toNat = nv + 1 := Nat.mod_eq_of_lt hinv_bound
      have heget : (exp.set nv (BitVec.ofNat 32 u))[nv]?.getD 0#32 = BitVec.ofNat 32 u := by
        simp [hnv_lt]
      rw [hget, hto]; refine ⟨by omega, by omega, ?_⟩
      simpa [Nat.add_sub_cancel, heget] using Nat.mod_eq_of_lt hu0_bound
    · have hget : (tmk.set u0 (BitVec.ofNat 32 (nv + 1)))[u]?.getD 0#32 = tmk[u]?.getD 0#32 := by
        simp [List.getElem?_set_ne (Ne.symm hueq)]
      rw [hget] at hnz ⊢; rcases hok.1 u hu hnz with ⟨hle1, hlenv, heeq⟩
      have heget : (exp.set nv (BitVec.ofNat 32 u0))[(tmk[u]?.getD 0#32).toNat - 1]?.getD 0#32 =
          exp[(tmk[u]?.getD 0#32).toNat - 1]?.getD 0#32 := by
        simp [List.getElem?_set_ne (by omega : nv ≠ (tmk[u]?.getD 0#32).toNat - 1)]
      rw [heget]; exact ⟨hle1, by omega, heeq⟩
  · by_cases hjeq : j = nv
    · subst hjeq
      have heget : (exp.set j (BitVec.ofNat 32 u0))[j]?.getD 0#32 = BitVec.ofNat 32 u0 := by
        simp [hnv_lt]
      have htget : (tmk.set u0 (BitVec.ofNat 32 (j + 1)))[u0]?.getD 0#32 =
          BitVec.ofNat 32 (j + 1) := by simp [hu0_lt]
      rw [heget, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hu0_bound, htget]
      exact ⟨hu0, Nat.mod_eq_of_lt hinv_bound⟩
    · have heget : (exp.set nv (BitVec.ofNat 32 u0))[j]?.getD 0#32 = exp[j]?.getD 0#32 := by
        simp [List.getElem?_set_ne (by omega : nv ≠ j)]
      rw [heget]; rcases hok.2 j (by omega) with ⟨hlt, hteq⟩
      have hne : (exp[j]?.getD 0#32).toNat ≠ u0 := fun heq => by rw [heq, ht0] at hteq; simp at hteq
      have htget : (tmk.set u0 (BitVec.ofNat 32 (nv + 1)))[(exp[j]?.getD 0#32).toNat]?.getD 0#32 =
          tmk[(exp[j]?.getD 0#32).toNat]?.getD 0#32 := by
        simp [List.getElem?_set_ne (Ne.symm hne)]
      rw [htget]; exact ⟨hlt, hteq⟩

theorem cert_export_add_bv {cur_vars max_vars : Nat} {nv u : BitVec 32}
    {tmk exp : List (BitVec 32)} (hok : certExportOk cur_vars nv.toNat tmk exp)
    (hu_cv : u.toNat / 2 < cur_vars) (ht0 : tmk[u.toNat / 2]?.getD 0#32 = 0#32)
    (hnv_exp : (BitVec.zeroExtend 64 nv).toNat < exp.length)
    (hu_tmk : (BitVec.zeroExtend 64 (u >>> 1#32)).toNat < tmk.length)
    (hcv_le : cur_vars ≤ max_vars) (hmaxv_lt : max_vars < 2 ^ 32) (hnv_cv : nv.toNat < cur_vars) :
    let exp' := exp.set (BitVec.zeroExtend 64 nv).toNat (u >>> 1#32)
    let tmk' := tmk.set (BitVec.zeroExtend 64 (u >>> 1#32)).toNat (nv + 1#32)
    certExportOk cur_vars (nv + 1#32).toNat tmk' exp' := by
  have hu_eq : (u >>> 1#32).toNat = u.toNat / 2 := cert_shr1_toNat u
  have hnv1 : nv.toNat + 1 < 2 ^ 32 := by omega
  have hnv1_eq : (nv + 1#32).toNat = nv.toNat + 1 := by
    simp [BitVec.toNat_add, Nat.mod_eq_of_lt hnv1]
  rw [cert_zext64_toNat] at hnv_exp; rw [cert_zext64_toNat, hu_eq] at hu_tmk
  have hadd := cert_export_add hok hu_cv ht0 hnv_exp hu_tmk hnv1 (by omega)
  have hb1 : BitVec.ofNat 32 (nv.toNat + 1) = nv + 1#32 := BitVec.eq_of_toNat_eq (by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnv1, hnv1_eq])
  have hb2 : BitVec.ofNat 32 (u.toNat / 2) = u >>> 1#32 := BitVec.eq_of_toNat_eq (by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : u.toNat / 2 < 2 ^ 32), hu_eq])
  rw [hnv1_eq]; dsimp only
  rw [cert_zext64_toNat nv, cert_zext64_toNat (u >>> 1#32), hu_eq, ← hb1, ← hb2]; exact hadd

private theorem cert_undo_init {cur_vars nv : Nat} {tmk exp : List (BitVec 32)}
    (hok : certExportOk cur_vars nv tmk exp) : certUndoInv cur_vars nv exp tmk 0 := by
  intro u hu hnz
  rcases hok.1 u hu hnz with ⟨h1, _, heq⟩
  exact ⟨(tmk[u]?.getD 0#32).toNat - 1, Nat.zero_le _, by omega, heq⟩

private theorem cert_undo_step {cur_vars nv j : Nat} {exp tmk : List (BitVec 32)}
    (hj : j < nv) (hinv : certUndoInv cur_vars nv exp tmk j)
    (hu_lt : (exp[j]?.getD 0#32).toNat < tmk.length) :
    certUndoInv cur_vars nv exp (tmk.set (exp[j]?.getD 0#32).toNat 0#32) (j + 1) := by
  intro u hu hnz
  have hne : u ≠ (exp[j]?.getD 0#32).toNat := by
    intro heq; subst heq
    have hset : (tmk.set (exp[j]?.getD 0#32).toNat 0#32)[(exp[j]?.getD 0#32).toNat]?.getD 0#32 =
        0#32 := by simp [hu_lt]
    exact hnz hset
  have hget : (tmk.set (exp[j]?.getD 0#32).toNat 0#32)[u]?.getD 0#32 = tmk[u]?.getD 0#32 := by
    simp [List.getElem?_set_ne (Ne.symm hne)]
  rw [hget] at hnz
  rcases hinv u hu hnz with ⟨k, hjk, hknv, heqk⟩
  have hkj : k ≠ j := fun h => by subst h; exact hne heqk.symm
  exact ⟨k, by omega, hknv, heqk⟩

private theorem cert_undo_done {cur_vars nv : Nat} {exp tmk : List (BitVec 32)}
    (hinv : certUndoInv cur_vars nv exp tmk nv) :
    ∀ u < cur_vars, tmk[u]?.getD 0#32 = 0#32 := by
  intro u hu
  exact Classical.byContradiction fun hnz => by
    rcases hinv u hu hnz with ⟨k, hle, hlt, _⟩; omega

/-! ## 4. Cert Sub-Loop & Finalizer `wp` Lemmas -/

theorem cert_undo_tmk_wp (Γ : Env) (Q : Post [.bool]) (X : XPost)
    (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s s_base : FullState) (R : Mem 64 → Prop) (tmp exp tmk scr : List (BitVec 32))
    (nv : BitVec 32) (m0 : Mem 64) (k : Expr Val Cont [.bool]) (_hinv : FullDenseInvW c F0 F_cur s)
    (hdw : FullDenseInvW c F0 F_cur (certMkState s_base tmp exp tmk scr))
    (hnv_cv : nv.toNat ≤ s.core.cur_vars) (hs_cv : s_base.core.cur_vars = s.core.cur_vars)
    (hcv_le : s.core.cur_vars ≤ c.max_vars) (_hmaxv32 : c.max_vars < 2 ^ 32)
    (htmp_len : tmp.length = c.max_vars) (hexp_len : exp.length = 2 * c.max_vars)
    (htmk_len : tmk.length = 2 * c.max_vars) (hscr_len : scr.length = c.scratch_cap)
    (hgu_len : s_base.scratch.glue_used.length = 64)
    (hok : certExportOk s.core.cur_vars nv.toNat tmk exp)
    (hm0 : (Full.FullMem c (certMkState s_base tmp exp tmk scr) ⋆ R) m0)
    (hk : ∀ (tmk' : List (BitVec 32)) (m' : Mem 64), tmk'.length = 2 * c.max_vars →
      TmkZero (certMkState s_base tmp exp tmk' scr) →
      FullDenseInvW c F0 F_cur (certMkState s_base tmp exp tmk' scr) →
      (Full.FullMem c (certMkState s_base tmp exp tmk' scr) ⋆ R) m' → wp Γ Q X k m') :
    wp Γ Q X (certUndoTmkExpr c.pWsort c.pTarjanMark nv k) m0 := by
  unfold certUndoTmkExpr; c0_hsteps_nogrp
  refine wp_while_state1 (fun st : BitVec 32 × List (BitVec 32) => st.1)
    (fun (j, _) => nv.toNat - j.toNat)
    (fun (j, tmk') m' => j.toNat ≤ nv.toNat ∧ tmk'.length = 2 * c.max_vars ∧
      certUndoInv s.core.cur_vars nv.toNat exp tmk' j.toNat ∧
      (Full.FullMem c (certMkState s_base tmp exp tmk' scr) ⋆ R) m')
    (fun J_t hJt => by
      c0_hsteps; exact hJt (0#32, tmk) m0 ⟨Nat.zero_le _, htmk_len, cert_undo_init hok, hm0⟩)
    (fun J_t (j, tmk') m' ⟨hj_le, htmk'_len, hundo, hm'⟩ ih => ?_)
  c0_hsteps
  · have hj_lt : j.toNat < nv.toNat := by c0_bound
    have hj_arr : j.toNat < exp.length := by omega
    have hj_wsort : (BitVec.zeroExtend 64 j).toNat < exp.length := by rw [cert_zext64_toNat]; omega
    have hu_cv : (exp[j.toNat]?.getD 0#32).toNat < s.core.cur_vars := (hok.2 j.toNat hj_lt).1
    have hu_eq' : (exp[j.toNat]?.getD 0#32).toNat = exp[j.toNat].toNat := by
      rw [cert_getElemD hj_arr]
    have hu_tmk64 : (BitVec.zeroExtend 64 exp[(BitVec.zeroExtend 64 j).toNat]).toNat <
        tmk'.length := by rw [cert_zext64_toNat]; simp only [cert_zext64_toNat]; omega
    c0_hsteps
    let tmk'' := tmk'.set (BitVec.zeroExtend 64 exp[(BitVec.zeroExtend 64 j).toNat]).toNat 0#32
    have htmk''_eq : tmk'' = tmk'.set exp[j.toNat].toNat 0#32 := by
      dsimp only [tmk'']; simp only [cert_zext64_toNat]
    have hundo' : certUndoInv s.core.cur_vars nv.toNat exp tmk'' (j.toNat + 1) := by
      rw [htmk''_eq]; have hu_tmk : (exp[j.toNat]?.getD 0#32).toNat < tmk'.length := by omega
      have hget := cert_getElemD hj_arr 0#32
      simpa [hget] using cert_undo_step hj_lt hundo (by simpa [hget] using hu_tmk)
    have hj1_lt : j.toNat + 1 < 2 ^ 32 := by omega
    refine ih (j + 1#32, tmk'') _ (by simp [BitVec.toNat_add]; omega)
      ⟨by simp [BitVec.toNat_add]; omega, by simp [tmk'', htmk'_len],
       by simpa [BitVec.toNat_add, Nat.mod_eq_of_lt hj1_lt] using hundo', by assumption⟩
  · have hj_eq : j.toNat = nv.toNat := by c0_bound
    have htmkF : TmkZero (certMkState s_base tmp exp tmk' scr) := fun u hu => by
      rw [certMkState_tmk]; exact cert_undo_done (hj_eq ▸ hundo) u (hs_cv ▸ hu)
    have hinvF : FullDenseInvW c F0 F_cur (certMkState s_base tmp exp tmk' scr) := by
      unfold certMkState
      exact cert_fullDenseInvW_mk hdw htmp_len hexp_len htmk'_len hscr_len hgu_len
    exact hk tmk' m' htmk'_len htmkF hinvF hm'

end

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S1
