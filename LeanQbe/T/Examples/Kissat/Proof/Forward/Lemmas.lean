/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Forward.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics1
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Shared Lemmas for `Kissat/Proof/Forward` (`Proof.Forward.Lemmas`)

Pure `BitVec`, `CNF`, `ModeWatchSliceOk`, `ModeWatchesInv`, `FullDenseInvW`, and arena-shrink /
literal-mark helpers (`0` legacy imports, `0` `@[expose]` on theorems/lemmas, `<= 100` cols).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Forward

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open Kraken.Bedrock2.Test

open scoped FullArenaTactics

/-! ## 1. Pure `Nat`, `BitVec` & `List` Transport Helpers -/

theorem fwd_getElem_congr {α : Type _} {xs : List α} {i j : Nat} (h : i = j)
    (hi : i < xs.length) (hj : j < xs.length) : xs[i]'hi = xs[j]'hj := by
  subst h; rfl

theorem fwd_zext32_toNat (x : BitVec 32) : (x.setWidth 64).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := x.isLt; omega)]

theorem fwd_xor1_mod2 (a : Nat) : (a ^^^ 1) % 2 = 1 - a % 2 := by
  have htb : (a ^^^ 1).testBit 0 = !(a.testBit 0) := by
    rw [Nat.testBit_xor]; cases a.testBit 0 <;> decide
  have h1 : ∀ n : Nat, n.testBit 0 = decide (n % 2 = 1) := fun n => Nat.testBit_zero n
  rw [h1, h1] at htb
  have ha : a % 2 = 0 ∨ a % 2 = 1 := by omega
  have hb : (a ^^^ 1) % 2 = 0 ∨ (a ^^^ 1) % 2 = 1 := by omega
  rcases ha with h0 | h1' <;> rcases hb with k0 | k1 <;> simp_all

theorem fwd_bv8_dom_pos_sle {v : BitVec 8} (hd : v = 0#8 ∨ v = 1#8 ∨ v = 0xFF#8)
    (h : (v.signExtend 32).sle (BitVec.ofNat 32 0) = false) : v = 1#8 := by
  rcases hd with rfl | rfl | rfl <;> simp_all

theorem fwd_bv8_dom_pos_slt {v : BitVec 8} (hd : v = 0#8 ∨ v = 1#8 ∨ v = 0xFF#8)
    (h : (BitVec.ofNat 32 0).slt (v.signExtend 32) = true) : v = 1#8 := by
  rcases hd with rfl | rfl | rfl <;> simp_all

theorem fwd_bv8_dom_neg_slt {v : BitVec 8} (hd : v = 0#8 ∨ v = 1#8 ∨ v = 0xFF#8)
    (h : (v.signExtend 32).slt (BitVec.ofNat 32 0) = true) : v = 0xFF#8 := by
  rcases hd with rfl | rfl | rfl <;> simp_all

theorem fwd_bv8_dom_neg_of_not_pos_ne0 {v : BitVec 8}
    (hd : v = 0#8 ∨ v = 1#8 ∨ v = 0xFF#8)
    (h1 : (BitVec.ofNat 32 0).slt (v.signExtend 32) = false)
    (h2 : v.signExtend 32 ≠ 0#32) : v = 0xFF#8 := by
  rcases hd with rfl | rfl | rfl
  · exact absurd rfl h2
  · simp at h1
  · rfl

theorem fwd_bv8_dom_zero_of_not_pos_neg {v : BitVec 8}
    (hd : v = 0#8 ∨ v = 1#8 ∨ v = 0xFF#8)
    (h1 : (BitVec.ofNat 32 0).slt (v.signExtend 32) = false)
    (h2 : (v.signExtend 32).slt (BitVec.ofNat 32 0) = false) : v = 0#8 := by
  rcases hd with rfl | rfl | rfl <;> simp_all

private theorem fwd_bv32_bit_disj (x mask target : BitVec 32)
    (hm : (target &&& mask) = 0#32) :
    ((x ||| target) &&& mask) = (x &&& mask) ∧
    ((x &&& ~~~target) &&& mask) = (x &&& mask) := by
  have h1 : ((x ||| target) &&& mask) = (x &&& mask) := by
    ext i hi
    have hmi := congrArg (·[i]) hm
    simp only [BitVec.getElem_and, BitVec.getElem_zero] at hmi
    simp only [BitVec.getElem_and, BitVec.getElem_or]
    rw [Bool.and_or_distrib_right, hmi, Bool.or_false]
  have h2 : ((x &&& ~~~target) &&& mask) = (x &&& mask) := by
    ext i hi
    have hmi := congrArg (·[i]) hm
    simp only [BitVec.getElem_and, BitVec.getElem_zero] at hmi
    simp only [BitVec.getElem_and, BitVec.getElem_not]
    cases h : mask[i]
    · simp
    · simp only [h, Bool.and_true] at hmi ⊢
      simp [hmi]
  exact ⟨h1, h2⟩

theorem fwd_or_garb_bits (x : BitVec 32) :
    ((x ||| 0x00080000#32) &&& 0x00080000#32) ≠ 0#32 ∧
    ((x ||| 0x00080000#32) &&& 0x00800000#32) = (x &&& 0x00800000#32) := by
  refine ⟨fun h => ?_, (fwd_bv32_bit_disj x 0x00800000#32 0x00080000#32 (by decide)).1⟩
  have h19 := congrArg (·[19]) h
  revert h19; simp [show (0x00080000#32 : BitVec 32)[19] = true by decide]

theorem fwd_bit24_or_pres (x : BitVec 32) :
    ((x ||| 0x01000000#32) &&& 0x00080000#32) = (x &&& 0x00080000#32) ∧
    ((x ||| 0x01000000#32) &&& 0x00800000#32) = (x &&& 0x00800000#32) :=
  ⟨(fwd_bv32_bit_disj x 0x00080000#32 0x01000000#32 (by decide)).1,
   (fwd_bv32_bit_disj x 0x00800000#32 0x01000000#32 (by decide)).1⟩

theorem fwd_bit24_clear_pres (x : BitVec 32) :
    ((x &&& ~~~0x01000000#32) &&& 0x00080000#32) = (x &&& 0x00080000#32) ∧
    ((x &&& ~~~0x01000000#32) &&& 0x00800000#32) = (x &&& 0x00800000#32) :=
  ⟨(fwd_bv32_bit_disj x 0x00080000#32 0x01000000#32 (by decide)).2,
   (fwd_bv32_bit_disj x 0x00800000#32 0x01000000#32 (by decide)).2⟩

theorem fwd_garb_sub_bits (x : BitVec 32) :
    (((x ||| 0x00080000#32) ||| 0x01000000#32) &&& 0x00080000#32) ≠ 0#32 ∧
    (((x ||| 0x00080000#32) ||| 0x01000000#32) &&& 0x00800000#32) = (x &&& 0x00800000#32) := by
  have h1 := fwd_or_garb_bits x
  have h2 := fwd_bit24_or_pres (x ||| 0x00080000#32)
  exact ⟨by rw [h2.1]; exact h1.1, by rw [h2.2]; exact h1.2⟩

theorem fwd_sz_and_mask_eq {sz : BitVec 32} (hlt : sz.toNat < 2 ^ 31) :
    (sz &&& 0x7FFFFFFF#32) = sz :=
  FullBvaFwdTactics.bv32_and_mask_eq hlt

theorem fwd_sz_and_mask_no_bin {sz : BitVec 32} :
    ((sz &&& 0x7FFFFFFF#32) &&& 0x80000000#32) = 0#32 := by
  ext i hi; simp only [BitVec.getElem_and, BitVec.getElem_zero]
  have h0 : ((0x7FFFFFFF#32 &&& 0x80000000#32) : BitVec 32)[i] = false := by
    have : (0x7FFFFFFF#32 &&& 0x80000000#32) = 0#32 := by decide
    rw [this]; simp
  simp only [BitVec.getElem_and] at h0
  rw [Bool.and_assoc, h0, Bool.and_false]

theorem fwd_bv32_ne_sent_of_lt {x : BitVec 32} (hlt : x.toNat < 2 ^ 31) :
    x ≠ 0xFFFFFFFF#32 := fun h => by
  have := congrArg BitVec.toNat h; simp at this; omega

theorem fwd_and_garb_zero_of_mask {hdr : BitVec 32}
    (h : (hdr &&& (0x00080000#32 ||| 0x00400000#32)) = 0#32) :
    (hdr &&& 0x00080000#32) = 0#32 := by
  have hmask : ((0x00080000#32 ||| 0x00400000#32) &&& 0x00080000#32) = 0x00080000#32 := by
    decide
  calc hdr &&& 0x00080000#32
      = hdr &&& ((0x00080000#32 ||| 0x00400000#32) &&& 0x00080000#32) := by rw [hmask]
    _ = (hdr &&& (0x00080000#32 ||| 0x00400000#32)) &&& 0x00080000#32 := by
      rw [BitVec.and_assoc]
    _ = 0#32 := by rw [h, BitVec.zero_and]

/-! ## 2. Pure CNF, Entailment & Arena Reference Helpers -/

theorem fwd_vals_pos_entails {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (hl0 : k.cur_level = 0)
    {l : Nat} (hl : l < 2 * k.cur_vars) (h1 : k.vals[l]?.getD 0#8 = 1#8) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause [l]) := by
  obtain ⟨idx, hidx, htrl⟩ := (hw.vals_true_iff l hl).mp h1
  have hv0 : (k.lvl[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by
    have := hw.lvl_le idx hidx; omega
  have hs := hw.level0_sound idx hidx hv0
  rwa [htrl] at hs

theorem fwd_vals_neg_entails {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (hl0 : k.cur_level = 0)
    {l : Nat} (hl : l < 2 * k.cur_vars) (hff : k.vals[l]?.getD 0#8 = 0xFF#8) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause [l ^^^ 1]) := by
  obtain ⟨idx, hidx, htrl⟩ := (hw.vals_false_iff l hl).mp hff
  have hv0 : (k.lvl[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by
    have := hw.lvl_le idx hidx; omega
  have hs := hw.level0_sound idx hidx hv0
  rwa [htrl] at hs

theorem fwd_resolve_bin_unit {F : CNF Nat} {a b : Nat}
    (hbin : F.EntailsClause (cnfClause [a ^^^ 1, b]))
    (hu : F.EntailsClause (cnfClause [a])) :
    F.EntailsClause (cnfClause [b]) := by
  rw [CNF.entails_clause_def] at hbin hu ⊢
  intro α hα
  have h1 := hbin α hα
  have h2 := hu α hα
  rw [clause_sat_cnfClause_iff] at h1 h2 ⊢
  obtain ⟨l2, hl2, hs2⟩ := h2
  rw [List.mem_singleton] at hl2
  rw [hl2] at hs2
  obtain ⟨l1, hl1, hs1⟩ := h1
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl1
  rcases hl1 with h1a | h1b
  · exfalso
    rw [h1a] at hs1
    simp only [litVar, litSign] at hs1 hs2
    have hdiv := fullInv_var_xor1 a
    have hmod := fwd_xor1_mod2 a
    rw [hdiv, hmod] at hs1
    cases h : α (a / 2) <;> simp [h] at hs1 hs2 <;> omega
  · rw [h1b] at hs1
    exact ⟨b, List.mem_singleton_self b, hs1⟩

theorem fwd_unsat_of_lit_and_neg {F : CNF Nat} {a : Nat}
    (h1 : F.EntailsClause (cnfClause [a]))
    (h2 : F.EntailsClause (cnfClause [a ^^^ 1])) : F.Unsat := by
  rw [CNF.unsat_iff_not_sat]; intro α hα
  have s1 := (CNF.entails_clause_def.mp h1) α hα
  have s2 := (CNF.entails_clause_def.mp h2) α hα
  rw [clause_sat_cnfClause_iff] at s1 s2
  obtain ⟨l1, hl1, hs1⟩ := s1; obtain ⟨l2, hl2, hs2⟩ := s2
  rw [List.mem_singleton] at hl1 hl2
  rw [hl1] at hs1; rw [hl2] at hs2
  simp only [litVar, litSign] at hs1 hs2
  have hdiv := fullInv_var_xor1 a
  have hmod := fwd_xor1_mod2 a
  rw [hdiv, hmod] at hs2
  cases h : α (a / 2) <;> simp [h] at hs1 hs2 <;> omega

theorem fwd_clause_all_false_unsat {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (hl0 : k.cur_level = 0)
    {cl : List Nat} (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause cl))
    (hlt : ∀ l ∈ cl, l < 2 * k.cur_vars)
    (hfalse : ∀ l ∈ cl, k.vals[l]?.getD 0#8 = 0xFF#8) :
    (cnfOfClauses F_cur).Unsat := by
  rw [CNF.unsat_iff_not_sat]; intro α hα
  have hs := (CNF.entails_clause_def.mp hent) α hα
  rw [clause_sat_cnfClause_iff] at hs
  obtain ⟨l, hl, hsl⟩ := hs
  have hneg := fwd_vals_neg_entails hw hl0 (hlt l hl) (hfalse l hl)
  have hsn := (CNF.entails_clause_def.mp hneg) α hα
  rw [clause_sat_cnfClause_iff] at hsn
  obtain ⟨l', hl', hsl'⟩ := hsn
  rw [List.mem_singleton] at hl'; rw [hl'] at hsl'
  simp only [litVar, litSign] at hsl hsl'
  have hdiv := fullInv_var_xor1 l
  have hmod := fwd_xor1_mod2 l
  rw [hdiv, hmod] at hsl'
  cases h : α (l / 2) <;> simp [h] at hsl hsl' <;> omega

theorem fwd_clause_one_unass_entails {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (hl0 : k.cur_level = 0)
    {cl : List Nat} {u : Nat} (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause cl))
    (hlt : ∀ l ∈ cl, l < 2 * k.cur_vars)
    (hoth : ∀ l ∈ cl, l ≠ u → k.vals[l]?.getD 0#8 = 0xFF#8) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause [u]) := by
  rw [CNF.entails_clause_def]; intro α hα
  have hs := (CNF.entails_clause_def.mp hent) α hα
  rw [clause_sat_cnfClause_iff] at hs ⊢
  obtain ⟨l, hl, hsl⟩ := hs
  by_cases hlu : l = u
  · subst hlu; exact ⟨l, List.mem_singleton_self _, hsl⟩
  · exfalso
    have hneg := fwd_vals_neg_entails hw hl0 (hlt l hl) (hoth l hl hlu)
    have hsn := (CNF.entails_clause_def.mp hneg) α hα
    rw [clause_sat_cnfClause_iff] at hsn
    obtain ⟨l', hl', hsl'⟩ := hsn
    rw [List.mem_singleton] at hl'; rw [hl'] at hsl'
    simp only [litVar, litSign] at hsl hsl'
    have hdiv := fullInv_var_xor1 l
    have hmod := fwd_xor1_mod2 l
    rw [hdiv, hmod] at hsl'
    cases h : α (l / 2) <;> simp [h] at hsl hsl' <;> omega

theorem fwd_lit_compl_conflict {α : Nat → Bool} {l : Nat}
    (h1 : α (litVar l) = !litSign l)
    (h2 : α (litVar (l ^^^ 1)) = !litSign (l ^^^ 1)) : False := by
  simp only [litVar, litSign] at h1 h2
  rw [fullInv_var_xor1 l, fwd_xor1_mod2 l] at h2
  rcases Nat.mod_two_eq_zero_or_one l with hm | hm <;>
    cases h : α (l / 2) <;> simp_all

theorem fwd_drop_false_lit {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (hl0 : k.cur_level = 0)
    {C : List Nat} {drop : Nat} (hC : (cnfOfClauses F_cur).EntailsClause (cnfClause C))
    (hlt : drop < 2 * k.cur_vars) (hff : k.vals[drop]?.getD 0#8 = 0xFF#8) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause (C.filter (· != drop))) := by
  have hneg := fwd_vals_neg_entails hw hl0 hlt hff
  rw [CNF.entails_clause_def] at hC hneg ⊢
  intro α hα
  have hc := (clause_sat_cnfClause_iff α _).mp (hC α hα)
  have hn := (clause_sat_cnfClause_iff α _).mp (hneg α hα)
  obtain ⟨l', hl', hs'⟩ := hn
  rw [List.mem_singleton] at hl'; rw [hl'] at hs'
  rw [clause_sat_cnfClause_iff]
  obtain ⟨lc, hlc, hsc⟩ := hc
  refine ⟨lc, List.mem_filter.mpr ⟨hlc, bne_iff_ne.mpr fun heq => ?_⟩, hsc⟩
  rw [heq] at hsc; exact fwd_lit_compl_conflict hsc hs'

theorem fwd_unsat_of_entails_nil {F : CNF Nat} (h : F.EntailsClause (cnfClause [])) :
    F.Unsat := by
  rw [CNF.unsat_iff_not_sat]; intro α hα
  have hs := (clause_sat_cnfClause_iff α []).mp ((CNF.entails_clause_def.mp h) α hα)
  obtain ⟨_, hm, _⟩ := hs; cases hm

theorem fwd_sublist_map_nodup {xs ys : List Nat} (hsub : ys.Sublist xs)
    (hnd : (xs.map (· / 2)).Nodup) : (ys.map (· / 2)).Nodup :=
  (hsub.map (· / 2)).nodup hnd

private theorem fwd_nodup_lt_len_le : ∀ (n : Nat) (xs : List Nat),
    xs.Nodup → (∀ x ∈ xs, x < n) → xs.length ≤ n
  | 0, [], _, _ => Nat.le_refl 0
  | 0, x :: _, _, hlt => by have := hlt x List.mem_cons_self; omega
  | n + 1, xs, hnd, hlt => by
    by_cases hm : n ∈ xs
    · have hlen := fwd_nodup_lt_len_le n (xs.erase n) (hnd.erase n) fun x hx => by
        have hne : x ≠ n := fun heq => by
          subst heq
          have hnm := (List.Nodup.mem_erase_iff hnd).mp hx
          exact hnm.1 rfl
        have := hlt x (List.mem_of_mem_erase hx); omega
      have her := List.length_erase_of_mem hm
      omega
    · have hlen := fwd_nodup_lt_len_le n xs hnd fun x hx => by
        have hne : x ≠ n := fun heq => hm (heq ▸ hx)
        have := hlt x hx; omega
      omega

theorem fwd_clause_nodup_len_le {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) {cref : Nat}
    (href : cref ∈ fullArenaClauseRefs s) (hng : fullArenaClauseGarb s cref = false) :
    fullArenaClauseSize s cref ≤ s.core.cur_vars := by
  have hnd := h.2.2.2.1 cref href hng
  have hwf := h.2.1.arena.refs_wf cref href
  have hal := h.1.core_ok.arena_len_le
  have haa := h.1.core_ok.arena_len_arr
  have hlen : ((fullArenaClauseLits s cref).map (· / 2)).length = fullArenaClauseSize s cref := by
    unfold fullArenaClauseLits fullArenaClauseLitsCore
    simp only [List.length_map, List.length_take, List.length_drop]
    exact Nat.min_eq_left (by omega)
  rw [← hlen]
  refine fwd_nodup_lt_len_le s.core.cur_vars _ hnd fun v hv => ?_
  rw [List.mem_map] at hv
  obtain ⟨l, hl, rfl⟩ := hv
  have hlt := h.2.1.arena.lits_lt cref href hng l hl
  omega

theorem fwd_zero_mem_arenaRefs {c : FullCfg} {F_cur : List (List Nat)}
    {k : FullCoreState} (ha : FullArenaClausesInv c F_cur k) (hpos : 0 < k.arena_len) :
    0 ∈ fullArenaClauseRefsCore k := by
  rcases ha.len_ok with hz | h3
  · omega
  · unfold fullArenaClauseRefsCore
    cases hal : k.arena_len with
    | zero => omega
    | succ n =>
      rw [fullArenaScanRefs]
      have hle : 0 + 3 ≤ n + 1 := by omega
      simp [hle]

/-! ## 3. Mode-Indexed Watch Slice Helpers (Sparse & Dense) -/

/-- Mode-unified watch slice invariant for `full_fwd_flush_large_m7`: matches
`WatchSliceOk` when `k.dense_mode = 0` and `DenseWatchSliceOk` when `k.dense_mode ≠ 0`. -/
@[expose] def ModeWatchSliceOk (F_cur : List (List Nat)) (k : FullCoreState)
    (lit p rem : Nat) : Prop :=
  if k.dense_mode = 0#64 then WatchSliceOk F_cur k lit p rem
  else DenseWatchSliceOk F_cur k lit p rem

theorem ModeWatchSliceOk.empty {F_cur : List (List Nat)} {k : FullCoreState} {lit p : Nat} :
    ModeWatchSliceOk F_cur k lit p 0 := by
  unfold ModeWatchSliceOk; split
  · exact .empty
  · exact .empty

theorem ModeWatchSliceOk.of_modeWatchesInv {F_cur : List (List Nat)} {k : FullCoreState}
    (hm : ModeWatchesInv F_cur k) {l : Nat} (hl : l < 2 * k.cur_vars) :
    ModeWatchSliceOk F_cur k l (fullWatchOffCore k l) (fullWatchSizeCore k l) := by
  unfold ModeWatchesInv at hm; unfold ModeWatchSliceOk
  by_cases hc : k.dense_mode = 0#64 <;> simp only [hc, ↓reduceIte] at hm ⊢
  · exact hm.slices l hl
  · exact hm.slices l hl

theorem ModeWatchSliceOk.mono {F F' : List (List Nat)} {k k' : FullCoreState} {lit p rem : Nat}
    (hF : (cnfOfClauses F').Entails (cnfOfClauses F)) (hdm : k'.dense_mode = k.dense_mode)
    (hvars : k.cur_vars ≤ k'.cur_vars)
    (hsub : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k')
    (hwstk : ∀ idx, p ≤ idx → idx < p + rem → k'.wstk[idx]? = k.wstk[idx]?)
    (h : ModeWatchSliceOk F k lit p rem) : ModeWatchSliceOk F' k' lit p rem := by
  unfold ModeWatchSliceOk at h ⊢; rw [hdm]
  by_cases hc : k.dense_mode = 0#64 <;> simp only [hc, ↓reduceIte] at h ⊢
  · exact h.mono hF hvars hsub hwstk
  · exact h.mono hF hvars hsub hwstk

theorem ModeWatchSliceOk.append_bin {F_cur : List (List Nat)} {k k' : FullCoreState}
    {lit p rem : Nat} {w0 : BitVec 32}
    (hdm : k'.dense_mode = k.dense_mode) (hvars : k.cur_vars ≤ k'.cur_vars)
    (hsub : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k')
    (hwstk : ∀ i < rem, k'.wstk[p + i]? = k.wstk[p + i]?)
    (h : ModeWatchSliceOk F_cur k lit p rem)
    (hw0 : k'.wstk[p + rem]? = some w0) (hflag : (w0 &&& 0x80000000#32) ≠ 0#32)
    (hne : w0 ≠ 0xFFFFFFFF#32) (hlt : (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k'.cur_vars)
    (hent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause [lit, (w0 &&& 0x7FFFFFFF#32).toNat])) :
    ModeWatchSliceOk F_cur k' lit p (rem + 1) := by
  unfold ModeWatchSliceOk at h ⊢; rw [hdm]
  by_cases hc : k.dense_mode = 0#64 <;> simp only [hc, ↓reduceIte] at h ⊢
  · exact fullWatchSlice_append_bin hvars hsub hwstk h hw0 hflag hne hlt hent
  · exact DenseWatchSliceOk.append_bin hvars hsub hwstk h hw0 hflag hne hlt hent

theorem ModeWatchSliceOk.cases_step {F_cur : List (List Nat)} {k : FullCoreState}
    {lit p rem : Nat} (h : ModeWatchSliceOk F_cur k lit p rem) (hpos : 0 < rem) :
    (∃ r1 w0, rem = r1 + 1 ∧ k.wstk[p]? = some w0 ∧ (w0 &&& 0x80000000#32) ≠ 0#32 ∧
      w0 ≠ 0xFFFFFFFF#32 ∧ (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k.cur_vars ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause [lit, (w0 &&& 0x7FFFFFFF#32).toNat]) ∧
      ModeWatchSliceOk F_cur k lit (p + 1) r1) ∨
    (∃ r2 w0 cref, rem = r2 + 2 ∧ k.wstk[p]? = some w0 ∧ k.wstk[p + 1]? = some cref ∧
      (w0 &&& 0x80000000#32) = 0#32 ∧ ModeWatchSliceOk F_cur k lit (p + 2) r2) := by
  unfold ModeWatchSliceOk at h
  by_cases hc : k.dense_mode = 0#64
  · simp only [hc, ↓reduceIte] at h
    cases h with
    | empty => omega
    | @bin _ r1 w0 hw hf hn hl he hr =>
      exact Or.inl ⟨r1, w0, rfl, hw, hf, hn, hl, he, by
        unfold ModeWatchSliceOk; simp only [hc, ↓reduceIte]; exact hr⟩
    | @large _ r2 w0 cr hw hw1 hf _ _ hr =>
      exact Or.inr ⟨r2, w0, cr, rfl, hw, hw1, hf, by
        unfold ModeWatchSliceOk; simp only [hc, ↓reduceIte]; exact hr⟩
  · simp only [hc, ↓reduceIte] at h
    cases h with
    | empty => omega
    | @bin _ r1 w0 hw hf hn hl he hr =>
      exact Or.inl ⟨r1, w0, rfl, hw, hf, hn, hl, he, by
        unfold ModeWatchSliceOk; simp only [hc, ↓reduceIte]; exact hr⟩
    | @occ _ r2 w0 cr hw hw1 hf _ _ _ hr =>
      exact Or.inr ⟨r2, w0, cr, rfl, hw, hw1, hf, by
        unfold ModeWatchSliceOk; simp only [hc, ↓reduceIte]; exact hr⟩

theorem fwd_witnessInv_of_shrink_watch {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hlen : s.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core)
    {l nsz : Nat} (hl : l < 2 * s.core.cur_vars) (hnsz : nsz ≤ fullWatchSizeCore s.core l)
    {wstk' : List (BitVec 32)} {wu' : BitVec 64}
    (hwl : wstk'.length = c.wcap)
    (hout : ∀ idx,
      idx < fullWatchOffCore s.core l ∨
      fullWatchOffCore s.core l + fullWatchSizeCore s.core l ≤ idx →
      wstk'[idx]? = s.core.wstk[idx]?)
    (hpref : ModeWatchSliceOk F_cur { s.core with wstk := wstk' } l
      (fullWatchOffCore s.core l) nsz) :
    let wvec' := s.core.wvec.set (2 * l + 1) (BitVec.ofNat 32 nsz)
    let s' : FullState :=
      { s with core := { s.core with wvec := wvec', wstk := wstk', wusable := wu' } }
    s'.LengthsOk c ∧ FullWitnessInv c F0 F_cur s'.core := by
  intro wvec' s'
  have hlay := hw.watches.layout
  have hcl := hlen.core_ok
  have hwc := c.hwcap; unfold dimacsBound at hwc
  have hbd_l := hlay.bounds l hl
  have hnsz32 : nsz < 2 ^ 32 := by have := hcl.wlen_le; omega
  have hwv_len : wvec'.length = 4 * c.max_vars := by simp [wvec', hcl.wvec_len]
  have hoff' : ∀ x < 2 * s.core.cur_vars,
      fullWatchOffCore s'.core x = fullWatchOffCore s.core x := by
    intro x _; unfold fullWatchOffCore; dsimp only [s', wvec']
    rw [List.getElem?_set_ne (by omega)]
  have hsz' : ∀ x < 2 * s.core.cur_vars,
      fullWatchSizeCore s'.core x =
        if x = l then nsz else fullWatchSizeCore s.core x := by
    intro x hx; unfold fullWatchSizeCore; dsimp only [s', wvec']
    by_cases hxl : x = l
    · subst hxl; simp only [↓reduceIte]
      rw [List.getElem?_set_self (by rw [hcl.wvec_len]; have := hcl.cur_vars_le; omega),
        Option.getD_some, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnsz32]
    · simp only [hxl, ↓reduceIte]; rw [List.getElem?_set_ne (by omega)]
  have hb' : ∀ x < 2 * s'.core.cur_vars,
      fullWatchOffCore s'.core x + fullWatchSizeCore s'.core x ≤ s'.core.wlen := by
    intro x hx; have hx0 : x < 2 * s.core.cur_vars := hx
    rw [hoff' x hx0, hsz' x hx0]
    change fullWatchOffCore s.core x + _ ≤ s.core.wlen
    split
    · subst ‹x = l›; omega
    · exact hlay.bounds x hx0
  have hp' : ∀ x < 2 * s'.core.cur_vars,
      0 < fullWatchSizeCore s'.core x → 1 ≤ fullWatchOffCore s'.core x := by
    intro x hx hp; have hx0 : x < 2 * s.core.cur_vars := hx
    rw [hoff' x hx0]; rw [hsz' x hx0] at hp
    split at hp
    · exact hlay.pos_off x hx0 (by rw [‹x = l›]; omega)
    · exact hlay.pos_off x hx0 hp
  have hd' : ∀ l1 l2, l1 < 2 * s'.core.cur_vars → l2 < 2 * s'.core.cur_vars → l1 ≠ l2 →
      0 < fullWatchSizeCore s'.core l1 → 0 < fullWatchSizeCore s'.core l2 →
      fullWatchOffCore s'.core l1 + fullWatchSizeCore s'.core l1 ≤ fullWatchOffCore s'.core l2 ∨
      fullWatchOffCore s'.core l2 + fullWatchSizeCore s'.core l2 ≤ fullWatchOffCore s'.core l1 := by
    intro l1 l2 h1 h2 hne hp1 hp2
    have h10 : l1 < 2 * s.core.cur_vars := h1
    have h20 : l2 < 2 * s.core.cur_vars := h2
    rw [hoff' l1 h10, hoff' l2 h20, hsz' l1 h10, hsz' l2 h20]
    rw [hsz' l1 h10] at hp1; rw [hsz' l2 h20] at hp2
    have h1p : 0 < fullWatchSizeCore s.core l1 := by
      by_cases h1l : l1 = l
      · simp only [h1l, ↓reduceIte] at hp1; rw [h1l]; omega
      · simp only [h1l, ↓reduceIte] at hp1; exact hp1
    have h2p : 0 < fullWatchSizeCore s.core l2 := by
      by_cases h2l : l2 = l
      · simp only [h2l, ↓reduceIte] at hp2; rw [h2l]; omega
      · simp only [h2l, ↓reduceIte] at hp2; exact hp2
    rcases hlay.disjoint l1 l2 h10 h20 hne h1p h2p with hd | hd
    · left; by_cases h1l : l1 = l
      · simp only [h1l, ↓reduceIte]; rw [h1l] at hd; omega
      · simp only [h1l, ↓reduceIte]; exact hd
    · right; by_cases h2l : l2 = l
      · simp only [h2l, ↓reduceIte]; rw [h2l] at hd; omega
      · simp only [h2l, ↓reduceIte]; exact hd
  have hent_refl : (cnfOfClauses F_cur).Entails (cnfOfClauses F_cur) := by
    rw [CNF.entails_def]; exact fun _ hx => hx
  have hwat' : ModeWatchesInv F_cur s'.core := by
    have hwm := hw.watches
    unfold ModeWatchesInv at hwm ⊢
    by_cases hc : s.core.dense_mode = 0#64
    · have hc' : s'.core.dense_mode = 0#64 := hc
      simp only [hc, hc', ↓reduceIte] at hwm ⊢
      refine WatchesInv.of_slices hb' hp' hd' fun x hx => ?_
      have hx0 : x < 2 * s.core.cur_vars := hx
      rw [hoff' x hx0, hsz' x hx0]
      by_cases hxl : x = l
      · subst hxl; simp only [↓reduceIte]
        have hpr : WatchSliceOk F_cur { s.core with wstk := wstk' } x
            (fullWatchOffCore s.core x) nsz := by
          simpa only [ModeWatchSliceOk, hc, ↓reduceIte] using hpref
        exact hpr.mono (k := { s.core with wstk := wstk' }) (k' := s'.core)
          hent_refl (Nat.le_refl _) (fun _ hr => hr) (fun _ _ _ => rfl)
      · simp only [hxl, ↓reduceIte]
        by_cases hpx : fullWatchSizeCore s.core x = 0
        · rw [hpx]; exact .empty
        · by_cases hpl : fullWatchSizeCore s.core l = 0
          · exact (hwm.slices x hx0).mono (k := s.core) (k' := s'.core)
              hent_refl (Nat.le_refl _) (fun _ hr => hr)
              fun idx _ _ => by dsimp only [s']; exact hout idx (by omega)
          · have hdj := hlay.disjoint x l hx0 hl hxl (by omega) (by omega)
            exact (hwm.slices x hx0).mono (k := s.core) (k' := s'.core)
              hent_refl (Nat.le_refl _) (fun _ hr => hr)
              fun idx hi1 hi2 => by
                dsimp only [s']; exact hout idx (by rcases hdj with h1 | h2 <;> omega)
    · have hc' : ¬ s'.core.dense_mode = 0#64 := hc
      simp only [hc, hc', ↓reduceIte] at hwm ⊢
      refine DenseWatchesInv.of_slices hb' hp' hd' fun x hx => ?_
      have hx0 : x < 2 * s.core.cur_vars := hx
      rw [hoff' x hx0, hsz' x hx0]
      by_cases hxl : x = l
      · subst hxl; simp only [↓reduceIte]
        have hpr : DenseWatchSliceOk F_cur { s.core with wstk := wstk' } x
            (fullWatchOffCore s.core x) nsz := by
          simpa only [ModeWatchSliceOk, hc, ↓reduceIte] using hpref
        exact hpr.mono (k := { s.core with wstk := wstk' }) (k' := s'.core)
          hent_refl (Nat.le_refl _) (fun _ hr => hr) (fun _ _ _ => rfl)
      · simp only [hxl, ↓reduceIte]
        by_cases hpx : fullWatchSizeCore s.core x = 0
        · rw [hpx]; exact .empty
        · by_cases hpl : fullWatchSizeCore s.core l = 0
          · exact (hwm.slices x hx0).mono (k := s.core) (k' := s'.core)
              hent_refl (Nat.le_refl _) (fun _ hr => hr)
              fun idx _ _ => by dsimp only [s']; exact hout idx (by omega)
          · have hdj := hlay.disjoint x l hx0 hl hxl (by omega) (by omega)
            exact (hwm.slices x hx0).mono (k := s.core) (k' := s'.core)
              hent_refl (Nat.le_refl _) (fun _ hr => hr)
              fun idx hi1 hi2 => by
                dsimp only [s']; exact hout idx (by rcases hdj with h1 | h2 <;> omega)
  exact ⟨⟨{ hcl with wvec_len := hwv_len, wstk_len_arr := hwl }, hlen.scratch_ok⟩,
    { hw with arena := { hw.arena with len_ok := hw.arena.len_ok }, watches := hwat' }⟩

theorem fwd_witnessInv_of_wstackDefrag {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (_hlen : s.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core)
    {wvec' wstk' wsort' : List (BitVec 32)} {wlen' : Nat}
    (hlen' : ({ s with
      core := { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := 0#64 }
      scratch := { s.scratch with wsort := wsort' } } : FullState).LengthsOk c)
    (hlay' : WatchStackLayout
      { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := 0#64 })
    (hslice : ∀ l < 2 * s.core.cur_vars,
      fullWatchSizeCore
        { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := 0#64 } l =
        fullWatchSize s l ∧
      ∀ k < fullWatchSize s l,
        wstk'[fullWatchOffCore
          { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := 0#64 } l + k]? =
        s.core.wstk[fullWatchOff s l + k]?) :
    let s' : FullState :=
      { s with
        core := { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := 0#64 }
        scratch := { s.scratch with wsort := wsort' } }
    s'.LengthsOk c ∧ FullWitnessInv c F0 F_cur s'.core := by
  intro s'
  have hwat' := fullWstackDefrag_preserves_modeWatchesInv hw.watches hlay' rfl rfl
    (fun _ hr => hr) hslice
  exact ⟨hlen', { hw with arena := { hw.arena with len_ok := hw.arena.len_ok }, watches := hwat' }⟩

/-! ## 4. `FullDenseInvW` Transport Helpers -/

theorem fwd_denseWatchesInv_of_w {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) : DenseWatchesInv F_cur s.core := by
  have := h.2.1.watches; unfold ModeWatchesInv at this; rwa [ite_eq_right h.2.2.2.2.2.2] at this

theorem fwd_denseInvW_with_scratch {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) {sc' : FullScratch}
    (hok : sc'.LengthsOk c) (hll : sc'.last_learned = s.scratch.last_learned)
    (hext : sc'.extend_len = s.scratch.extend_len) :
    FullDenseInvW c F0 F_cur { s with scratch := sc' } :=
  ⟨⟨h.1.core_ok, hok⟩, h.2.1, h.2.2.1, h.2.2.2.1,
   ⟨fun i hi => by
      change sc'.last_learned[i]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 ∨
        (sc'.last_learned[i]?.getD 0xFFFFFFFF#32).toNat ∈ fullArenaClauseRefs s
      rw [hll]; exact h.2.2.2.2.1.1 i hi,
    hext ▸ h.2.2.2.2.1.2⟩,
   h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

theorem fwd_denseInvW_with_flags {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) {fl' : List (BitVec 32)}
    (hfl : fl'.length = c.max_vars) :
    FullDenseInvW c F0 F_cur { s with core := { s.core with flags := fl' } } :=
  fullDenseInvW_set_flags h hfl

theorem fwd_denseInvW_with_tmp {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) {tmp' : List (BitVec 32)}
    (htl : tmp'.length = c.max_vars) :
    FullDenseInvW c F0 F_cur { s with core := { s.core with tmp := tmp' } } :=
  ⟨⟨{ h.1.core_ok with tmp_len_arr := htl }, h.1.scratch_ok⟩,
   { h.2.1 with
     arena := { h.2.1.arena with len_ok := h.2.1.arena.len_ok }
     watches := h.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) },
   h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

theorem fwd_denseInvW_with_prop {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) {p' : Nat} (hp : p' ≤ s.core.trail_end) :
    FullDenseInvW c F0 F_cur { s with core := { s.core with propagated := p' } } :=
  ⟨⟨{ h.1.core_ok with propagated_le := hp }, h.1.scratch_ok⟩,
   { h.2.1 with
     arena := { h.2.1.arena with len_ok := h.2.1.arena.len_ok }
     watches := h.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) },
   h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

theorem fwd_denseInvW_with_oom {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) (o' : BitVec 64) :
    FullDenseInvW c F0 F_cur { s with core := { s.core with oom := o' } } :=
  ⟨⟨{ h.1.core_ok with arena_len_le := h.1.core_ok.arena_len_le }, h.1.scratch_ok⟩,
   { h.2.1 with
     arena := { h.2.1.arena with len_ok := h.2.1.arena.len_ok }
     watches := h.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) },
   h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

theorem fwd_denseInvW_with_lit_mark {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (h : FullDenseInvW c F0 F_cur s)
    {lm' : List (BitVec 8)} (hlm_len : lm'.length = 2 * c.max_vars)
    (hlm_clr : ∀ l < 2 * c.max_vars, lm'[l]?.getD 0#8 = 0#8) :
    FullDenseInvW c F0 F_cur { s with core := { s.core with lit_mark := lm' } } :=
  ⟨⟨{ h.1.core_ok with lit_mark_len := hlm_len }, h.1.scratch_ok⟩,
   { h.2.1 with
     arena := { h.2.1.arena with len_ok := h.2.1.arena.len_ok }
     watches := h.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) },
   ⟨h.2.2.1.1, hlm_clr⟩, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

theorem fwd_denseInvW_set_inc {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) (hu : (cnfOfClauses F_cur).Unsat) :
    FullDenseInvW c F0 F_cur { s with core := { s.core with inconsistent := 1#64 } } :=
  ⟨⟨{ h.1.core_ok with arena_len_le := h.1.core_ok.arena_len_le }, h.1.scratch_ok⟩,
   { h.2.1 with
     inconsistent_sound := fun _ => hu
     arena := { h.2.1.arena with len_ok := h.2.1.arena.len_ok }
     watches := h.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) },
   h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

theorem fwd_denseInvW_of_addUnit {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s s' : FullState} (h : FullDenseInvW c F0 F_cur s)
    (hlen' : s'.LengthsOk c) (hw' : FullWitnessInv c F0 F_cur s'.core)
    (hcl' : s'.core.cur_level = 0) (hmrk : s'.core.mrk = s.core.mrk)
    (hlm : s'.core.lit_mark = s.core.lit_mark) (har : s'.core.arena = s.core.arena)
    (hal : s'.core.arena_len = s.core.arena_len) (hdm : s'.core.dense_mode = s.core.dense_mode)
    (hll : s'.scratch.last_learned = s.scratch.last_learned)
    (hext : s'.scratch.extend_len = s.scratch.extend_len) :
    FullDenseInvW c F0 F_cur s' := by
  refine ⟨hlen', hw', ⟨fun v hv => by rw [hmrk]; exact h.2.2.1.1 v hv,
    fun l hl => by rw [hlm]; exact h.2.2.1.2 l hl⟩, ?_, ?_, hcl', hdm ▸ h.2.2.2.2.2.2⟩
  · intro r hr hng
    have hrefs : fullArenaClauseRefs s' = fullArenaClauseRefs s := by
      unfold fullArenaClauseRefs fullArenaClauseRefsCore; rw [har, hal]
    have hgb : fullArenaClauseGarb s' r = fullArenaClauseGarb s r := by
      unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore; rw [har]
    have hlits : fullArenaClauseLits s' r = fullArenaClauseLits s r := by
      unfold fullArenaClauseLits fullArenaClauseLitsCore fullArenaClauseSizeCore; rw [har]
    rw [hrefs] at hr; rw [hgb] at hng; rw [hlits]; exact h.2.2.2.1 r hr hng
  · refine ⟨fun i hi => ?_, hext ▸ h.2.2.2.2.1.2⟩
    have hrefs : fullArenaClauseRefs s' = fullArenaClauseRefs s := by
      unfold fullArenaClauseRefs fullArenaClauseRefsCore; rw [har, hal]
    dsimp only; rw [hll, hrefs]; exact h.2.2.2.2.1.1 i hi

theorem fwd_denseInvW_of_addBin {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s s' : FullState} (h : FullDenseInvW c F0 F_cur s)
    (hlen' : s'.LengthsOk c) (hw' : FullWitnessInv c F0 F_cur s'.core)
    (hmrk : s'.core.mrk = s.core.mrk) (hlm : s'.core.lit_mark = s.core.lit_mark)
    (har : s'.core.arena = s.core.arena) (hal : s'.core.arena_len = s.core.arena_len)
    (hcl : s'.core.cur_level = s.core.cur_level) (hdm : s'.core.dense_mode = s.core.dense_mode)
    (hll : s'.scratch.last_learned = s.scratch.last_learned)
    (hext : s'.scratch.extend_len = s.scratch.extend_len) :
    FullDenseInvW c F0 F_cur s' :=
  fwd_denseInvW_of_addUnit h hlen' hw' (hcl.trans h.2.2.2.2.2.1) hmrk hlm har hal hdm hll hext

theorem fwd_denseInvW_of_unwatch {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (h : FullDenseInvW c F0 F_cur s)
    {wvec' wstk' : List (BitVec 32)} {wu' : BitVec 64}
    (hlen' : ({ s with core :=
      { s.core with wvec := wvec', wstk := wstk', wusable := wu' } } :
      FullState).LengthsOk c)
    (hw' : ModeWatchesInv F_cur { s.core with wvec := wvec', wstk := wstk', wusable := wu' }) :
    FullDenseInvW c F0 F_cur
      { s with core := { s.core with wvec := wvec', wstk := wstk', wusable := wu' } } :=
  ⟨hlen', { h.2.1 with arena := { h.2.1.arena with len_ok := h.2.1.arena.len_ok }, watches := hw' },
   h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

theorem fwd_denseInvW_of_watchPush_occ {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
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
  let k' : FullCoreState :=
    { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' }
  have hwat' := fullWatchPush_preserves_modeWatchesInv (lit := lit) (w0 := w0) (w1 := w1)
    (cnt := 2#32) (ok := ok) h.2.1.watches hlay' rfl rfl (fun _ hr => hr)
    (fun h2 => by cases h2) (fun _ => ⟨hflag, fun _ => hsz, hlt, href⟩) hother
    (fun ht => let ⟨h1, h2, h3, h4, h5⟩ := hok_t ht
      ⟨h1, Or.inr rfl, h2, h3, h4, fun _ => h5⟩)
    hok_f
  exact ⟨hlen',
    { h.2.1 with arena := { h.2.1.arena with len_ok := h.2.1.arena.len_ok }, watches := hwat' },
    h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

theorem fwd_denseInvW_set_hdr_bit24 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) {cref : Nat}
    (href : cref ∈ fullArenaClauseRefs s) {v' : BitVec 32}
    (h19 : (v' &&& 0x00080000#32) = (fullArenaHdr s cref &&& 0x00080000#32))
    (h23 : (v' &&& 0x00800000#32) = (fullArenaHdr s cref &&& 0x00800000#32)) :
    let s' : FullState := { s with core := { s.core with arena := s.core.arena.set cref v' } }
    FullDenseInvW c F0 F_cur s' ∧
    fullArenaClauseRefs s' = fullArenaClauseRefs s ∧
    (∀ r ∈ fullArenaClauseRefs s,
      fullArenaClauseSize s' r = fullArenaClauseSize s r ∧
      fullArenaClauseGarb s' r = fullArenaClauseGarb s r ∧
      fullArenaClauseLits s' r = fullArenaClauseLits s r) := by
  intro s'
  have hcl := h.1.core_ok; have hw := h.2.1
  have hcref_wf := hw.arena.refs_wf cref href
  have har_len : cref < s.core.arena.length := by
    have := hcl.arena_len_le; have := hcl.arena_len_arr; omega
  have ha_cref : s'.core.arena[cref]? = some v' := List.getElem?_set_self har_len
  have hne_outside : ∀ r ∈ fullArenaClauseRefsCore s.core, r ≠ cref →
      (r + 3 + fullArenaClauseSizeCore s.core r ≤ cref ∧
        fullArenaNextOff s.core.arena s.core.arena_len r ≤ cref) ∨
      (cref + 3 ≤ fullArenaNextOff s.core.arena s.core.arena_len cref ∧
        fullArenaNextOff s.core.arena s.core.arena_len cref ≤ r) := by
    intro r hr hne; rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · exact Or.inl ⟨by have := fullArenaScanRefs_disjoint hr href hlt
                       have := (hw.arena.refs_wf r hr).2.2.1; omega,
        fullArenaScanRefs_disjoint hr href hlt⟩
    · exact Or.inr ⟨by omega, fullArenaScanRefs_disjoint href hr hgt⟩
  have hnxt : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaNextOff s'.core.arena s.core.arena_len r =
        fullArenaNextOff s.core.arena s.core.arena_len r := by
    intro r hr; by_cases hrc : r = cref
    · subst r
      have h2eq : s'.core.arena[cref + 2]? = s.core.arena[cref + 2]? :=
        List.getElem?_set_ne (by omega)
      have h1 : ¬ (cref + 3 > s.core.arena_len) := by omega
      have h2 : ¬ (cref + 3 + (s.core.arena[cref + 2]?.getD 0#32).toNat > s.core.arena_len) := by
        unfold fullArenaClauseSizeCore at hcref_wf; omega
      unfold fullArenaNextOff
      simp only [h1, ↓reduceIte, h2eq, h2, ha_cref, Option.getD_some]
      rw [h23, show fullArenaHdr s cref = s.core.arena[cref]?.getD 0#32 from rfl]
      split
      · exact fullArenaSkipShrk_congr fun i hi _ => List.getElem?_set_ne (by omega)
      · rfl
    · refine fullArenaNextOff_congr_block (List.getElem?_set_ne (Ne.symm hrc)) ?_ ?_
      · rcases hne_outside r hr hrc with ⟨hlt, _⟩ | ⟨_, hgt⟩
        · have := (hw.arena.refs_wf r hr).2.1; exact List.getElem?_set_ne (by omega)
        · exact List.getElem?_set_ne (by omega)
      · intro i hi1 _
        rcases hne_outside r hr hrc with ⟨_, hle⟩ | ⟨_, hgt⟩
        · exact List.getElem?_set_ne (by omega)
        · have := (hw.arena.refs_wf r hr).2.2.1; exact List.getElem?_set_ne (by omega)
  have hrefs : fullArenaClauseRefsCore s'.core = fullArenaClauseRefsCore s.core :=
    fullArenaClauseRefsCore_congr rfl hnxt
  have hper : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaClauseSizeCore s'.core r = fullArenaClauseSizeCore s.core r ∧
      fullArenaClauseGarbCore s'.core r = fullArenaClauseGarbCore s.core r ∧
      fullArenaClauseLitsCore s'.core r = fullArenaClauseLitsCore s.core r := by
    intro r hr; have hwf := hw.arena.refs_wf r hr
    have hbd : r + 3 + fullArenaClauseSizeCore s.core r ≤ s.core.arena.length := by
      have := hcl.arena_len_le; have := hcl.arena_len_arr; omega
    by_cases hrc : r = cref
    · subst r
      have hsz : fullArenaClauseSizeCore s'.core cref = fullArenaClauseSizeCore s.core cref := by
        unfold fullArenaClauseSizeCore; dsimp only [s']; rw [List.getElem?_set_ne (by omega)]
      have hgb : fullArenaClauseGarbCore s'.core cref = fullArenaClauseGarbCore s.core cref := by
        unfold fullArenaClauseGarbCore fullArenaHdrCore; rw [ha_cref, Option.getD_some, h19]; rfl
      have hlits : fullArenaClauseLitsCore s'.core cref = fullArenaClauseLitsCore s.core cref :=
        fullArenaClauseLitsCore_eq_of_hold hbd (by simp [s', hbd]) hsz fun j _ =>
          List.getElem?_set_ne (by omega)
      exact ⟨hsz, hgb, hlits⟩
    · have hout : r + 3 + fullArenaClauseSizeCore s.core r ≤ cref ∨ cref + 3 ≤ r :=
        (hne_outside r hr hrc).imp (fun h => h.1) (fun h => by omega)
      have hpair := fullArenaClauseLitsCore_set_outside (v := v') hbd hout
      have hgb : fullArenaClauseGarbCore s'.core r = fullArenaClauseGarbCore s.core r := by
        unfold fullArenaClauseGarbCore fullArenaHdrCore; dsimp only [s']
        rw [List.getElem?_set_ne (Ne.symm hrc)]
      exact ⟨hpair.1, hgb, hpair.2⟩
  have hlen' : s'.LengthsOk c :=
    ⟨{ hcl with arena_len_arr := by simp [s', hcl.arena_len_arr] }, h.1.scratch_ok⟩
  have harena' : FullArenaClausesInv c F_cur s'.core := by
    refine ⟨hw.arena.len_ok, ?_, ?_, ?_, ?_⟩
    · intro r hr; rw [hrefs] at hr; have hwf := hw.arena.refs_wf r hr
      dsimp only [s'] at hnxt ⊢; rw [hnxt r hr, (hper r hr).1]; exact hwf
    · intro r hr hsh; rw [hrefs] at hr
      have hsh0 : (fullArenaHdrCore s.core r &&& 0x00800000#32) ≠ 0#32 := by
        by_cases hrc : r = cref
        · subst r; unfold fullArenaHdrCore at hsh; rw [ha_cref, Option.getD_some, h23] at hsh
          exact hsh
        · unfold fullArenaHdrCore at hsh ⊢
          simpa [s', List.getElem?_set_ne (Ne.symm hrc)] using hsh
      obtain ⟨t, ht1, ht2, hsent⟩ := hw.arena.shrk_term r hr hsh0
      have hget_r : s.core.arena[r]? = some (fullArenaHdrCore s.core r) := by
        have hr3 := (hw.arena.refs_wf r hr).1
        have : r < s.core.arena.length := by
          have := hcl.arena_len_le; have := hcl.arena_len_arr; omega
        unfold fullArenaHdrCore; rw [List.getElem?_eq_getElem this, Option.getD_some]
      obtain ⟨t0, ht0_lo, _, _, ht0_sent⟩ :=
        fullArenaNextOff_hits_sentinel (hw.arena.refs_wf r hr).1
          (by rw [hget_r, Option.getD_some]; exact hsh0) ht1 ht2 hsent
      have ht0_ne : t0 ≠ cref := by
        by_cases hrc : r = cref
        · subst r; have := (hw.arena.refs_wf cref hr).2.1; omega
        · rcases hne_outside r hr hrc with ⟨_, hle⟩ | ⟨_, hgt⟩
          · omega
          · have := (hw.arena.refs_wf r hr).2.1; omega
      refine ⟨t0, by rw [(hper r hr).1]; exact ht0_lo, by dsimp only [s']; omega, ?_⟩
      dsimp only [s']; rw [List.getElem?_set_ne ht0_ne.symm]; exact ht0_sent
    · intro r hr hng l hl; rw [hrefs] at hr
      rw [(hper r hr).2.1] at hng; rw [(hper r hr).2.2] at hl
      exact hw.arena.lits_lt r hr hng l hl
    · intro r hr hng; rw [hrefs] at hr
      rw [(hper r hr).2.1] at hng; rw [(hper r hr).2.2]
      exact hw.arena.entails r hr hng
  have hw' : FullWitnessInv c F0 F_cur s'.core :=
    { hw with
      arena := harena'
      watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun r hr => hrefs.symm ▸ hr)
      reason_inv := fun idx hidx hne => by
        have := hw.lvl_le idx hidx; have hl0 := h.2.2.2.2.2.1
        exact absurd (hw.level0_rsn_none idx hidx (by omega)) hne
      reason_lit_mem := fun idx hidx hne => by
        have := hw.lvl_le idx hidx; have hl0 := h.2.2.2.2.2.1
        exact absurd (hw.level0_rsn_none idx hidx (by omega)) hne }
  refine ⟨⟨hlen', hw', h.2.2.1, fun r hr hng => ?_,
    ⟨fun i hi => by
      change _ = 0xFFFFFFFF#32 ∨ _ ∈ fullArenaClauseRefsCore s'.core
      rw [hrefs]; exact h.2.2.2.2.1.1 i hi, h.2.2.2.2.1.2⟩,
    h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩, hrefs, hper⟩
  change r ∈ fullArenaClauseRefsCore s'.core at hr; rw [hrefs] at hr
  change fullArenaClauseGarbCore s'.core r = false at hng; rw [(hper r hr).2.1] at hng
  change ((fullArenaClauseLitsCore s'.core r).map (· / 2)).Nodup; rw [(hper r hr).2.2]
  exact h.2.2.2.1 r hr hng

theorem fwd_denseInvW_markGarb {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) {cref : Nat}
    (href : cref ∈ fullArenaClauseRefs s) {arena' : List (BitVec 32)} {ag' : BitVec 64}
    (hal : arena'.length = c.arena_cap)
    (hhdr' : arena'[cref]? = some (fullArenaHdr s cref ||| 0x00080000#32) ∨
      arena'[cref]? = some ((fullArenaHdr s cref ||| 0x00080000#32) ||| 0x01000000#32))
    (hout : ∀ i, i ≠ cref → (i < cref + 3 ∨ cref + 3 + fullArenaClauseSizeCore s.core cref ≤ i) →
      arena'[i]? = s.core.arena[i]?) :
    let s' : FullState := { s with core := { s.core with arena := arena', arena_garbage := ag' } }
    FullDenseInvW c F0 F_cur s' ∧ fullArenaClauseRefs s' = fullArenaClauseRefs s := by
  intro s'
  have hcl := h.1.core_ok; have hw := h.2.1
  have hcref_wf := hw.arena.refs_wf cref href
  have hgarb_bit : (fullArenaHdrCore s'.core cref &&& 0x00080000#32) ≠ 0#32 := by
    unfold fullArenaHdrCore; dsimp only [s']
    rcases hhdr' with h1 | h2
    · rw [h1, Option.getD_some]; exact (fwd_or_garb_bits _).1
    · rw [h2, Option.getD_some]; exact (fwd_garb_sub_bits _).1
  have hshrk_bit : (fullArenaHdrCore s'.core cref &&& 0x00800000#32) =
      (fullArenaHdrCore s.core cref &&& 0x00800000#32) := by
    unfold fullArenaHdrCore; dsimp only [s']
    rcases hhdr' with h1 | h2
    · rw [h1, Option.getD_some]; exact (fwd_or_garb_bits _).2
    · rw [h2, Option.getD_some]; exact (fwd_garb_sub_bits _).2
  have hne_outside : ∀ r ∈ fullArenaClauseRefsCore s.core, r ≠ cref →
      (r + 3 + fullArenaClauseSizeCore s.core r ≤ cref ∧
        fullArenaNextOff s.core.arena s.core.arena_len r ≤ cref) ∨
      (cref + 3 + fullArenaClauseSizeCore s.core cref ≤ r ∧
        fullArenaNextOff s.core.arena s.core.arena_len cref ≤ r) := by
    intro r hr hne; rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · have := fullArenaScanRefs_disjoint hr href hlt
      have := (hw.arena.refs_wf r hr).2.2.1; exact Or.inl ⟨by omega, by omega⟩
    · have := fullArenaScanRefs_disjoint href hr hgt; exact Or.inr ⟨by omega, by omega⟩
  have hnxt : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaNextOff arena' s.core.arena_len r =
        fullArenaNextOff s.core.arena s.core.arena_len r := by
    intro r hr; by_cases hrc : r = cref
    · subst r
      have h2eq : arena'[cref + 2]? = s.core.arena[cref + 2]? :=
        hout (cref + 2) (by omega) (Or.inl (by omega))
      have h1 : ¬ (cref + 3 > s.core.arena_len) := by omega
      have h2 : ¬ (cref + 3 + (s.core.arena[cref + 2]?.getD 0#32).toNat > s.core.arena_len) := by
        unfold fullArenaClauseSizeCore at hcref_wf; omega
      unfold fullArenaNextOff
      simp only [h1, ↓reduceIte, h2eq, h2]
      have h23 : (arena'[cref]?.getD 0#32 &&& 0x00800000#32) =
          (s.core.arena[cref]?.getD 0#32 &&& 0x00800000#32) := hshrk_bit
      rw [h23]; split
      · exact fullArenaSkipShrk_congr fun i hi _ => hout i (by omega) (Or.inr hi)
      · rfl
    · refine fullArenaNextOff_congr_block
        (hout r hrc ((hne_outside r hr hrc).imp (fun h => by omega) (fun h => by omega)))
        (hout (r + 2) (by rcases hne_outside r hr hrc with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)
          ((hne_outside r hr hrc).imp (fun h => by
            have := (hw.arena.refs_wf r hr).2.1; omega) (fun h => by omega)))
        fun i hi1 _ => hout i (by rcases hne_outside r hr hrc with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)
          ((hne_outside r hr hrc).imp (fun h => by omega) (fun h => by
            have := (hw.arena.refs_wf r hr).2.2.1; omega))
  have hrefs : fullArenaClauseRefsCore s'.core = fullArenaClauseRefsCore s.core :=
    fullArenaClauseRefsCore_congr rfl hnxt
  have hsz_eq : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaClauseSizeCore s'.core r = fullArenaClauseSizeCore s.core r := fun r hr => by
    unfold fullArenaClauseSizeCore; dsimp only [s']
    by_cases hrc : r = cref
    · subst r; rw [hout (cref + 2) (by omega) (Or.inl (by omega))]
    · rw [hout (r + 2) (by rcases hne_outside r hr hrc with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)
        ((hne_outside r hr hrc).imp (fun h => by
          have := (hw.arena.refs_wf r hr).2.1; omega) (fun h => by omega))]
  have hother : ∀ r ∈ fullArenaClauseRefsCore s.core, r ≠ cref →
      fullArenaClauseGarbCore s'.core r = fullArenaClauseGarbCore s.core r ∧
      fullArenaClauseLitsCore s'.core r = fullArenaClauseLitsCore s.core r := fun r hr hne => by
    have hwf := hw.arena.refs_wf r hr
    have hbd : r + 3 + fullArenaClauseSizeCore s.core r ≤ s.core.arena.length := by
      have := hcl.arena_len_le; have := hcl.arena_len_arr; omega
    have hgb : fullArenaClauseGarbCore s'.core r = fullArenaClauseGarbCore s.core r := by
      unfold fullArenaClauseGarbCore fullArenaHdrCore; dsimp only [s']
      rw [hout r hne ((hne_outside r hr hne).imp (fun h => by omega) (fun h => by omega))]
    have hlits : fullArenaClauseLitsCore s'.core r = fullArenaClauseLitsCore s.core r :=
      fullArenaClauseLitsCore_eq_of_hold hbd
        (by dsimp only [s']; rw [hal, ← hcl.arena_len_arr]; omega)
        (hsz_eq r hr) fun j hj => hout (r + 3 + j)
          (by rcases hne_outside r hr hne with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)
          ((hne_outside r hr hne).imp (fun h => by omega) (fun h => by omega))
    exact ⟨hgb, hlits⟩
  have hlen' : s'.LengthsOk c := ⟨{ hcl with arena_len_arr := hal }, h.1.scratch_ok⟩
  have harena' : FullArenaClausesInv c F_cur s'.core := by
    refine ⟨hw.arena.len_ok, ?_, ?_, ?_, ?_⟩
    · intro r hr; rw [hrefs] at hr; have hwf := hw.arena.refs_wf r hr
      dsimp only [s'] at hnxt ⊢; rw [hnxt r hr, hsz_eq r hr]; exact hwf
    · intro r hr hsh; rw [hrefs] at hr
      have hsh0 : (fullArenaHdrCore s.core r &&& 0x00800000#32) ≠ 0#32 := by
        by_cases hrc : r = cref
        · subst r; rwa [hshrk_bit] at hsh
        · unfold fullArenaHdrCore at hsh ⊢
          have hget := hout r hrc
            ((hne_outside r hr hrc).imp (fun h => by omega) (fun h => by omega))
          simpa [s', hget] using hsh
      obtain ⟨t, ht1, ht2, hsent⟩ := hw.arena.shrk_term r hr hsh0
      have hget_r : s.core.arena[r]? = some (fullArenaHdrCore s.core r) := by
        have hr3 := (hw.arena.refs_wf r hr).1
        have : r < s.core.arena.length := by
          have := hcl.arena_len_le; have := hcl.arena_len_arr; omega
        unfold fullArenaHdrCore; rw [List.getElem?_eq_getElem this, Option.getD_some]
      obtain ⟨t0, ht0_lo, _, _, ht0_sent⟩ :=
        fullArenaNextOff_hits_sentinel (hw.arena.refs_wf r hr).1
          (by rw [hget_r, Option.getD_some]; exact hsh0) ht1 ht2 hsent
      refine ⟨t0, by rw [hsz_eq r hr]; exact ht0_lo, by dsimp only [s']; omega, ?_⟩
      dsimp only [s']
      have ht0_out :
          t0 ≠ cref ∧ (t0 < cref + 3 ∨ cref + 3 + fullArenaClauseSizeCore s.core cref ≤ t0) := by
        by_cases hrc : r = cref
        · subst r; exact ⟨by omega, Or.inr ht0_lo⟩
        · rcases hne_outside r hr hrc with ⟨_, hle⟩ | ⟨_, hgt⟩
          · exact ⟨by omega, Or.inl (by omega)⟩
          · exact ⟨by omega, Or.inr (by omega)⟩
      rw [hout t0 ht0_out.1 ht0_out.2]; exact ht0_sent
    · intro r hr hng l hl; rw [hrefs] at hr
      have hne : r ≠ cref := by
        rintro rfl; unfold fullArenaClauseGarbCore at hng
        simp [hgarb_bit] at hng
      rw [(hother r hr hne).1] at hng; rw [(hother r hr hne).2] at hl
      exact hw.arena.lits_lt r hr hng l hl
    · intro r hr hng; rw [hrefs] at hr
      have hne : r ≠ cref := by
        rintro rfl; unfold fullArenaClauseGarbCore at hng
        simp [hgarb_bit] at hng
      rw [(hother r hr hne).1] at hng; rw [(hother r hr hne).2]
      exact hw.arena.entails r hr hng
  have hw' : FullWitnessInv c F0 F_cur s'.core :=
    { hw with
      arena := harena'
      watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun r hr => hrefs.symm ▸ hr)
      reason_inv := fun idx hidx hne => by
        have := hw.lvl_le idx hidx; have hl0 := h.2.2.2.2.2.1
        exact absurd (hw.level0_rsn_none idx hidx (by omega)) hne
      reason_lit_mem := fun idx hidx hne => by
        have := hw.lvl_le idx hidx; have hl0 := h.2.2.2.2.2.1
        exact absurd (hw.level0_rsn_none idx hidx (by omega)) hne }
  refine ⟨⟨hlen', hw', h.2.2.1, fun r hr hng => ?_,
    ⟨fun i hi => by
      change _ = 0xFFFFFFFF#32 ∨ _ ∈ fullArenaClauseRefsCore s'.core
      rw [hrefs]; exact h.2.2.2.2.1.1 i hi, h.2.2.2.2.1.2⟩,
    h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩, hrefs⟩
  change r ∈ fullArenaClauseRefsCore s'.core at hr; rw [hrefs] at hr
  have hne : r ≠ cref := by
    intro heq; subst heq; change fullArenaClauseGarbCore s'.core r = false at hng
    unfold fullArenaClauseGarbCore at hng; simp [hgarb_bit] at hng
  change fullArenaClauseGarbCore s'.core r = false at hng; rw [(hother r hr hne).1] at hng
  change ((fullArenaClauseLitsCore s'.core r).map (· / 2)).Nodup; rw [(hother r hr hne).2]
  exact h.2.2.2.1 r hr hng

end LeanQbe.T.Examples.Kissat.Proof.Forward
