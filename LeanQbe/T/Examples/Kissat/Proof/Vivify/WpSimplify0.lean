/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Vivify.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Vivify.Tactics
public import LeanQbe.T.Examples.Kissat.Proof.Vivify.InvArena
public import LeanQbe.T.Examples.Kissat.Proof.Vivify.Inv

/-!
# Vivify Simplify Pure Arena & Witness Helpers (`Proof.Vivify.WpSimplify0`)

Pure arithmetic, clause-entailment, variable-`Nodup`, and shrink preparation lemmas
supporting `Proof.Vivify.WpSimplify`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Vivify

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.C0Step LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Watch.Spec
open LeanQbe.T.Examples.Kissat.Proof.Vivify.Spec
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Proof.Vivify.VivTactics
open Kraken.Bedrock2.Test

public section

theorem bv32_replace_lo_and_eq (hdr x m mask : BitVec 32) (h : m &&& mask = 0#32) :
    (((hdr &&& ~~~m) ||| (x &&& m)) &&& mask) = (hdr &&& mask) := by
  ext i hi
  have hi0 : (m[i] && mask[i]) = false := by
    rw [← BitVec.getElem_and, h]; exact BitVec.getElem_zero hi
  simp only [BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_not]
  by_cases hm : m[i] <;> by_cases hk : mask[i] <;> simp_all

private theorem pairwise_lt_len_le : ∀ {lo hi : Nat} (xs : List Nat),
    List.Pairwise (· < ·) xs → (∀ q ∈ xs, lo ≤ q ∧ q < hi) → xs.length ≤ hi - lo
  | _, _, [], _, _ => by simp
  | _, hi, a :: tl, hpw, hq => by
    have ha := hq a (by simp)
    have ⟨hhead, htl⟩ := List.pairwise_cons.mp hpw
    have ih := pairwise_lt_len_le (lo := a + 1) (hi := hi) tl htl fun q hqm =>
      ⟨by have := hhead q hqm; omega, (hq q (by simp [hqm])).2⟩
    simp only [List.length_cons]
    omega

private theorem pairwise_lt_len_lt_of_missing_aux : ∀ {lo hi : Nat} (xs : List Nat),
    List.Pairwise (· < ·) xs → (∀ q ∈ xs, lo ≤ q ∧ q < hi) →
    ∀ {j_miss : Nat}, lo ≤ j_miss → j_miss < hi → j_miss ∉ xs → xs.length < hi - lo
  | _, _, [], _, _, _, hlo, hhi, _ => by simp; omega
  | _, hi, a :: tl, hpw, hq, j_miss, _, hhi, hnot => by
    have ha := hq a (by simp)
    have ⟨hhead, htl⟩ := List.pairwise_cons.mp hpw
    have hne : j_miss ≠ a := fun h => hnot (by simp [h])
    have hnot_tl : j_miss ∉ tl := fun h => hnot (by simp [h])
    rcases Nat.lt_or_gt_of_ne hne with hlt | _
    · have hle := pairwise_lt_len_le (lo := a + 1) (hi := hi) tl htl fun q hqm =>
        ⟨by have := hhead q hqm; omega, (hq q (by simp [hqm])).2⟩
      simp only [List.length_cons]
      omega
    · have ih := pairwise_lt_len_lt_of_missing_aux (lo := a + 1) (hi := hi) tl htl
        (fun q hqm => ⟨by have := hhead q hqm; omega, (hq q (by simp [hqm])).2⟩)
        (by omega) hhi hnot_tl
      simp only [List.length_cons]
      omega

theorem pairwise_lt_len_lt_of_missing {xs : List Nat} {hi j_miss : Nat}
    (hpw : List.Pairwise (· < ·) xs) (hq : ∀ q ∈ xs, q < hi)
    (hhi : j_miss < hi) (hnot : j_miss ∉ xs) : xs.length < hi := by
  have h := pairwise_lt_len_lt_of_missing_aux (lo := 0) (hi := hi) xs hpw
    (fun q hqm => ⟨Nat.zero_le q, hq q hqm⟩) (Nat.zero_le j_miss) hhi hnot
  omega

theorem fullSparseInvW_with_inconsistent {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hsp : FullSparseInvW c F0 F_cur s)
    (huns : (cnfOfClauses F_cur).Unsat) :
    FullSparseInvW c F0 F_cur { s with core := { s.core with inconsistent := 1#64 } } :=
  ⟨⟨{ hsp.1.core_ok with cur_vars_le := hsp.1.core_ok.cur_vars_le }, hsp.1.scratch_ok⟩,
   { hsp.2.1 with
     inconsistent_sound := fun _ => huns
     arena := { hsp.2.1.arena with len_ok := hsp.2.1.arena.len_ok }
     watches := hsp.2.1.watches.with_wstk rfl rfl rfl rfl rfl fun _ r => r },
   hsp.2.2.1, hsp.2.2.2.1, hsp.2.2.2.2.1, hsp.2.2.2.2.2⟩

theorem simplify_lit_unsat_contra {F_cur : List (List Nat)} {l : Nat}
    {α : Nat → Bool} (hl_mem_ent : (cnfOfClauses F_cur).EntailsClause (cnfClause [l ^^^ 1]))
    (hα : (cnfOfClauses F_cur).eval α = true)
    (hl_sat : α (litVar l) = !litSign l) : False := by
  have hneg := CNF.entails_clause_def.mp hl_mem_ent α hα
  obtain ⟨l', hl', hns⟩ := (clause_sat_cnfClause_iff α [l ^^^ 1]).mp hneg
  simp only [List.mem_singleton] at hl'
  subst hl'
  have hv : litVar (l ^^^ 1) = litVar l := litVar_litNeg l
  have hbit : (l ^^^ 1).testBit 0 = !(l.testBit 0) := by rw [Nat.testBit_xor]; simp
  rw [Nat.testBit_zero, Nat.testBit_zero] at hbit
  rcases Nat.mod_two_eq_zero_or_one l with h0 | h1 <;>
    rcases Nat.mod_two_eq_zero_or_one (l ^^^ 1) with h0' | h1'
  · simp only [h0, h0'] at hbit; cases hbit
  · have hs : litSign (l ^^^ 1) = !litSign l := by simp only [litSign, h0, h1']; decide
    rw [hv, hs, Bool.not_not, hl_sat] at hns; revert hns; cases litSign l <;> decide
  · have hs : litSign (l ^^^ 1) = !litSign l := by simp only [litSign, h1, h0']; decide
    rw [hv, hs, Bool.not_not, hl_sat] at hns; revert hns; cases litSign l <;> decide
  · simp only [h1, h1'] at hbit; cases hbit

theorem simplify_lits_entails_of_idxs {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s2 : FullState} {cref sz : Nat} {idxs : List Nat}
    (hw2 : FullWitnessInv c F0 F_cur s2.core) (_hcl2 : s2.core.cur_level = 0)
    (href2 : cref ∈ fullArenaClauseRefs s2) (hg2 : fullArenaClauseGarb s2 cref = false)
    (hsz2 : fullArenaClauseSizeCore s2.core cref = sz)
    (hbd2 : cref + 3 + fullArenaClauseSizeCore s2.core cref ≤ s2.core.arena.length)
    (hdrop : ∀ j < sz, j ∈ idxs ∨
      ((s2.core.arena[cref + 3 + j]?.getD 0#32).toNat < 2 * s2.core.cur_vars ∧
        s2.core.vals[(s2.core.arena[cref + 3 + j]?.getD 0#32).toNat]?.getD 0#8 = 255#8)) :
    (cnfOfClauses F_cur).EntailsClause
      (cnfClause (idxs.map fun j => (s2.core.arena[cref + 3 + j]?.getD 0#32).toNat)) := by
  rw [CNF.entails_clause_def]
  intro α hα
  have hbase := (CNF.entails_clause_def.mp (hw2.arena.entails cref href2 hg2)) α hα
  obtain ⟨l, hl_mem, hl_sat⟩ := (clause_sat_cnfClause_iff α _).mp hbase
  obtain ⟨j, hj, rfl⟩ := (mem_fullArenaClauseLitsCore_iff hbd2).mp hl_mem
  have hj_ar : cref + 3 + j < s2.core.arena.length := by omega
  have hj_eq : (s2.core.arena[cref + 3 + j]?.getD 0#32).toNat =
      (s2.core.arena[cref + 3 + j]'hj_ar).toNat := by
    rw [List.getElem?_eq_getElem hj_ar, Option.getD_some]
  rcases hdrop j (hsz2 ▸ hj) with hmem | ⟨hlt, hff⟩
  · exact (clause_sat_cnfClause_iff α _).mpr ⟨_, List.mem_map.mpr ⟨j, hmem, hj_eq⟩, hl_sat⟩
  · rw [hj_eq] at hlt hff
    obtain ⟨ti, hti, hteq⟩ := (hw2.vals_false_iff _ hlt).mp hff
    have hent1 : (cnfOfClauses F_cur).EntailsClause
        (cnfClause [(s2.core.arena[cref + 3 + j]'hj_ar).toNat ^^^ 1]) := by
      rw [← hteq]
      exact hw2.level0_sound ti hti (by have := hw2.lvl_le ti hti; omega)
    exact False.elim (simplify_lit_unsat_contra hent1 hα hl_sat)

private theorem nodup_map_range {n : Nat} {f : Nat → Nat}
    (hinj : ∀ i j, i < n → j < n → i < j → f i ≠ f j) :
    ((List.range n).map f).Nodup := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.map_cons, List.map_nil, List.nodup_append]
    refine ⟨ih fun i j hi hj hij => hinj i j (by omega) (by omega) hij,
      by simp, fun a ha b hb => ?_⟩
    simp only [List.mem_map, List.mem_range, List.mem_singleton] at ha hb
    rcases ha with ⟨i, hi, rfl⟩
    subst hb
    exact hinj i k (by omega) (by omega) hi

private theorem nodup_getElem_ne {α : Type} : ∀ {xs : List α}, xs.Nodup →
    ∀ {i j : Nat} (hi : i < xs.length) (hj : j < xs.length), i < j → xs[i] ≠ xs[j]
  | [], _, _, _, hi, _, _ => absurd hi (Nat.not_lt_zero _)
  | _ :: _, hnd, 0, j + 1, _, hj, _ => by
    have ⟨hnx, _⟩ := List.nodup_cons.mp hnd
    intro heq
    simp only [List.getElem_cons_zero, List.getElem_cons_succ] at heq
    exact hnx (by rw [heq]; exact List.getElem_mem (by simp only [List.length_cons] at hj; omega))
  | _ :: _, hnd, i + 1, j + 1, hi, hj, hij => by
    have ⟨_, hnd'⟩ := List.nodup_cons.mp hnd
    exact nodup_getElem_ne hnd' (by simp at hi; omega) (by simp at hj; omega) (by omega)

theorem simplify_compact_nodup {s2 : FullState} (hnd : FullArenaVarsNodup s2)
    {cref sz n : Nat} (href : cref ∈ fullArenaClauseRefs s2)
    (hg : fullArenaClauseGarb s2 cref = false)
    (hsz : fullArenaClauseSize s2 cref = sz)
    (hbd : cref + 3 + fullArenaClauseSizeCore s2.core cref ≤ s2.core.arena.length)
    {ar_c : List (BitVec 32)} {idxs : List Nat}
    (hlen : idxs.length = n) (hpw : List.Pairwise (· < ·) idxs)
    (hq : ∀ q ∈ idxs, q < sz)
    (hmap : ∀ t < n, ar_c[cref + 3 + t]? = s2.core.arena[cref + 3 + idxs[t]?.getD 0]?)
    (_har_len : cref + 3 + n ≤ ar_c.length) :
    (((List.range n).map fun t => (ar_c[cref + 3 + t]?.getD 0#32).toNat).map (· / 2)).Nodup := by
  have hnodup_s2 := hnd cref href hg
  have hsz_core : fullArenaClauseSizeCore s2.core cref = sz := hsz
  have hcl_len : (fullArenaClauseLits s2 cref).length = sz := by
    unfold fullArenaClauseLits fullArenaClauseLitsCore
    rw [List.length_map, List.length_take, List.length_drop, hsz_core]; omega
  rw [List.map_map]
  refine nodup_map_range fun i j hi_len hj_len hij heq => ?_
  dsimp only [Function.comp_def] at heq
  have hmap_i : (ar_c[cref + 3 + i]?.getD 0#32).toNat =
      (s2.core.arena[cref + 3 + idxs[i]?.getD 0]?.getD 0#32).toNat := by rw [hmap i hi_len]
  have hmap_j : (ar_c[cref + 3 + j]?.getD 0#32).toNat =
      (s2.core.arena[cref + 3 + idxs[j]?.getD 0]?.getD 0#32).toNat := by rw [hmap j hj_len]
  rw [hmap_i, hmap_j] at heq
  have hi_q := hq (idxs[i]'(by omega)) (List.getElem_mem _)
  have hj_q := hq (idxs[j]'(by omega)) (List.getElem_mem _)
  have hlt_idxs : idxs[i]'(by omega) < idxs[j]'(by omega) :=
    List.pairwise_iff_getElem.mp hpw i j (by omega) (by omega) hij
  have hid_i : idxs[i]?.getD 0 = idxs[i]'(by omega) := by
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
  have hid_j : idxs[j]?.getD 0 = idxs[j]'(by omega) := by
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
  have hg_i : ((fullArenaClauseLits s2 cref).map (· / 2))[idxs[i]'(by omega)]'(by
      rw [List.length_map, hcl_len]; exact hi_q) =
      (s2.core.arena[cref + 3 + idxs[i]?.getD 0]?.getD 0#32).toNat / 2 := by
    unfold fullArenaClauseLits fullArenaClauseLitsCore
    rw [List.getElem_map, List.getElem_map, List.getElem_take, List.getElem_drop,
      hid_i, List.getElem?_eq_getElem (by omega), Option.getD_some]
  have hg_j : ((fullArenaClauseLits s2 cref).map (· / 2))[idxs[j]'(by omega)]'(by
      rw [List.length_map, hcl_len]; exact hj_q) =
      (s2.core.arena[cref + 3 + idxs[j]?.getD 0]?.getD 0#32).toNat / 2 := by
    unfold fullArenaClauseLits fullArenaClauseLitsCore
    rw [List.getElem_map, List.getElem_map, List.getElem_take, List.getElem_drop,
      hid_j, List.getElem?_eq_getElem (by omega), Option.getD_some]
  have hne := nodup_getElem_ne hnodup_s2
    (by rw [List.length_map, hcl_len]; exact hi_q)
    (by rw [List.length_map, hcl_len]; exact hj_q) hlt_idxs
  exact hne (by rw [hg_i, hg_j]; exact heq)

theorem simplify_nsz0_unsat {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s2 : FullState} {cref sz : Nat}
    {ar_c : List (BitVec 32)} {idxs : List Nat}
    (hsp2 : FullSparseInvW c F0 F_cur s2) (hcl2 : s2.core.cur_level = 0)
    (href2 : cref ∈ fullArenaClauseRefs s2) (hg2 : fullArenaClauseGarb s2 cref = false)
    (hsz2 : fullArenaClauseSizeCore s2.core cref = sz)
    (hbd2 : cref + 3 + fullArenaClauseSizeCore s2.core cref ≤ s2.core.arena.length)
    (harc_len : ar_c.length = c.arena_cap) (hlen_i : idxs.length = 0)
    (hout_i : ∀ p, (p < cref + 3 ∨ cref + 3 + 0 ≤ p) → ar_c[p]? = s2.core.arena[p]?)
    (hdrop_i : ∀ j < sz, j ∈ idxs ∨
      ((s2.core.arena[cref + 3 + j]?.getD 0#32).toNat < 2 * s2.core.cur_vars ∧
        s2.core.vals[(s2.core.arena[cref + 3 + j]?.getD 0#32).toNat]?.getD 0#8 = 255#8)) :
    ar_c = s2.core.arena ∧ F0.Unsat ∧
    FullSparseInvW c F0 F_cur { s2 with core := { s2.core with inconsistent := 1#64 } } := by
  have hnil : idxs = [] := List.eq_nil_of_length_eq_zero hlen_i
  have har_eq : ar_c = s2.core.arena :=
    List.ext_getElem (by rw [harc_len, hsp2.1.core_ok.arena_len_arr]) fun p hp1 hp2 =>
      Option.some.inj (by
        rw [← List.getElem?_eq_getElem hp1, hout_i p (by omega), ← List.getElem?_eq_getElem hp2])
  have hent := simplify_lits_entails_of_idxs hsp2.2.1 hcl2 href2 hg2 hsz2 hbd2 hdrop_i
  rw [hnil, List.map_nil] at hent
  have huns_cur := unsat_of_entails_nil hent
  exact ⟨har_eq, hsp2.2.1.ext_sound.2 huns_cur, fullSparseInvW_with_inconsistent hsp2 huns_cur⟩

theorem simplify_nsz_ge3_prep {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s2 : FullState} {cref sz nsz : Nat}
    {ar_c : List (BitVec 32)} {idxs : List Nat}
    (hsp2 : FullSparseInvW c F0 F_cur s2) (hcl2 : s2.core.cur_level = 0)
    (href2 : cref ∈ fullArenaClauseRefs s2) (hg2 : fullArenaClauseGarb s2 cref = false)
    (hsz2 : fullArenaClauseSizeCore s2.core cref = sz)
    (hnsz3 : 3 ≤ nsz) (hnsz_lt : nsz < sz)
    (hbd2 : cref + 3 + fullArenaClauseSizeCore s2.core cref ≤ s2.core.arena.length)
    (harc_len : ar_c.length = c.arena_cap) (hlen_i : idxs.length = nsz)
    (hpw_i : List.Pairwise (· < ·) idxs) (hq_i : ∀ q ∈ idxs, q < sz)
    (_hout_i : ∀ p, (p < cref + 3 ∨ cref + 3 + nsz ≤ p) → ar_c[p]? = s2.core.arena[p]?)
    (hmap_i : ∀ t < nsz, ar_c[cref + 3 + t]? = s2.core.arena[cref + 3 + idxs[t]?.getD 0]?)
    (hdrop_i : ∀ j < sz, j ∈ idxs ∨
      ((s2.core.arena[cref + 3 + j]?.getD 0#32).toNat < 2 * s2.core.cur_vars ∧
        s2.core.vals[(s2.core.arena[cref + 3 + j]?.getD 0#32).toNat]?.getD 0#8 = 255#8))
    {ar_f : List (BitVec 32)} {nhdr2 : BitVec 32}
    (harf_len : ar_f.length = c.arena_cap)
    (hng2 : (nhdr2 &&& 0x80000#32) = 0#32) (hsh2 : (nhdr2 &&& 0x800000#32) ≠ 0#32)
    (hhdr_f : ar_f[cref]? = some nhdr2)
    (hsz_f : (ar_f[cref + 2]?.getD 0#32).toNat = nsz)
    (hpay_f : ∀ j < nsz, ar_f[cref + 3 + j]? = ar_c[cref + 3 + j]?)
    (hout_f : ∀ p, (p < cref ∨ cref + 3 + sz ≤ p) → ar_f[p]? = s2.core.arena[p]?)
    (hpad_f : M6ShrkPad ar_f s2.core.arena cref sz nsz) :
    let s_f : FullState := { s2 with core := { s2.core with arena := ar_f } }
    FullSparseInvW c F0 F_cur s_f ∧ fullArenaClauseRefs s_f = fullArenaClauseRefs s2 ∧
    (ar_f[cref + 3]?.getD 0#32).toNat < 2 * s_f.core.cur_vars ∧
    (ar_f[cref + 4]?.getD 0#32).toNat < 2 * s_f.core.cur_vars := by
  intro s_f
  have hcl2_ok := hsp2.1.core_ok
  have hw2 := hsp2.2.1
  have hsz2' : fullArenaClauseSize s2 cref = sz := hsz2
  have harc_bd : cref + 3 + nsz ≤ ar_c.length := by
    rw [harc_len, ← hcl2_ok.arena_len_arr]; omega
  have hnd_range := simplify_compact_nodup hsp2.2.2.2.1 href2 hg2 hsz2' hbd2 hlen_i hpw_i hq_i
    hmap_i harc_bd
  have hlits_lt : ∀ j < nsz, (ar_f[cref + 3 + j]?.getD 0#32).toNat < 2 * s2.core.cur_vars := by
    intro j hj
    rw [hpay_f j hj, hmap_i j hj]
    have hq_j : idxs[j]?.getD 0 < sz := by
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      exact hq_i _ (List.getElem_mem (by rw [hlen_i]; exact hj))
    have hbd_idx : cref + 3 + idxs[j]?.getD 0 < s2.core.arena.length := by omega
    exact hw2.arena.lits_lt cref href2 hg2 _
      ((mem_fullArenaClauseLitsCore_iff hbd2).mpr ⟨idxs[j]?.getD 0, by rw [hsz2]; exact hq_j,
        by rw [List.getElem?_eq_getElem hbd_idx, Option.getD_some]⟩)
  have harf_bd : cref + 3 + fullArenaClauseSizeCore s_f.core cref ≤ ar_f.length := by
    change cref + 3 + (ar_f[cref + 2]?.getD 0#32).toNat ≤ ar_f.length
    rw [hsz_f, harf_len, ← hcl2_ok.arena_len_arr]; omega
  have hlits_eq : fullArenaClauseLitsCore s_f.core cref =
      (List.range nsz).map fun t => (ar_c[cref + 3 + t]?.getD 0#32).toNat := by
    have hlen_l : (fullArenaClauseLitsCore s_f.core cref).length = nsz := by
      unfold fullArenaClauseLitsCore fullArenaClauseSizeCore
      change (((ar_f.drop (cref + 3)).take
        (ar_f[cref + 2]?.getD 0#32).toNat).map BitVec.toNat).length = nsz
      rw [List.length_map, List.length_take, List.length_drop, hsz_f,
        harf_len, ← hcl2_ok.arena_len_arr]
      omega
    refine List.ext_getElem (by rw [hlen_l, List.length_map, List.length_range]) fun t ht1 _ => ?_
    rw [hlen_l] at ht1
    have hgt : (fullArenaClauseLitsCore s_f.core cref)[t]'(by rw [hlen_l]; exact ht1) =
        (ar_f[cref + 3 + t]?.getD 0#32).toNat := by
      unfold fullArenaClauseLitsCore
      simp only [List.getElem_map, List.getElem_take, List.getElem_drop]
      rw [List.getElem?_eq_getElem (by rw [harf_len, ← hcl2_ok.arena_len_arr]; omega),
        Option.getD_some]
    rw [hgt, List.getElem_map, List.getElem_range, hpay_f t ht1]
  have hnd_f : ((fullArenaClauseLitsCore s_f.core cref).map (· / 2)).Nodup := by
    rw [hlits_eq]; exact hnd_range
  have hent_f : (cnfOfClauses F_cur).EntailsClause
      (cnfClause (fullArenaClauseLitsCore s_f.core cref)) := by
    have hent_i := simplify_lits_entails_of_idxs hw2 hcl2 href2 hg2 hsz2 hbd2 hdrop_i
    rw [CNF.entails_clause_def] at hent_i ⊢
    intro α hα
    obtain ⟨l, hl, hsat⟩ := (clause_sat_cnfClause_iff α _).mp (hent_i α hα)
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hl
    obtain ⟨t, ht, hteq⟩ := List.mem_iff_getElem.mp hj
    have ht_lt : t < nsz := by rwa [hlen_i] at ht
    rw [hlits_eq]
    have hlt_eq : (ar_c[cref + 3 + t]?.getD 0#32).toNat =
        (s2.core.arena[cref + 3 + j]?.getD 0#32).toNat := by
      rw [hmap_i t ht_lt]
      have hg_d : idxs[t]?.getD 0 = j := by
        rw [List.getElem?_eq_getElem ht, Option.getD_some, hteq]
      rw [hg_d]
    exact (clause_sat_cnfClause_iff α _).mpr ⟨_, List.mem_map.mpr ⟨t, List.mem_range.mpr ht_lt,
      hlt_eq⟩, hsat⟩
  obtain ⟨hsp_out, hrefs_out, _, _⟩ := fullSparseInvW_of_inPlaceShrink_hnonact hsp2 href2
    (nonActiveReason_of_level0 hw2 hcl2 cref) hg2 hnsz3 (hsz2'.symm ▸ hnsz_lt) harf_len
    (fun p hp => hout_f p (by rcases hp with h | h; exact Or.inl h; exact Or.inr (hsz2' ▸ h)))
    (by rw [hhdr_f, Option.getD_some]; exact hng2)
    (by rw [hhdr_f, Option.getD_some]; exact hsh2)
    hsz_f (hsz2' ▸ hpad_f) hlits_lt hnd_f hent_f
  exact ⟨hsp_out, hrefs_out, hlits_lt 0 (by omega), hlits_lt 1 (by omega)⟩

abbrev simplifyDecrExpr (h : Val i64) (hdr_v : Val i32) (Js : Cont []) :
    Expr Val Cont [i64] :=
  fvOp (OpCode.and i32) (Arg.var hdr_v, Arg.imm 4194304, ()) fun p =>
  fvOp (OpCode.cmp .ne i32 .bool (by decide)) (Arg.var p.fst, Arg.imm 0, ()) fun p =>
  Expr.jnz (Arg.var p.fst)
    (Expr.group (sig := [[]]) (fun _ => Blocks.cons (fun (_ : Tup Val []) =>
      Expr.jump Js ()) Blocks.nil) fun Js2 =>
     fvOp (OpCode.add i64) (Arg.var h, Arg.imm 496, ()) fun p =>
     Expr.load i64 (Arg.var p.fst) fun ld =>
     fvOp (OpCode.cmp .ugt i64 .bool (by decide)) (Arg.var ld, Arg.imm 0, ()) fun p =>
     Expr.jnz (Arg.var p.fst)
       (fvOp (OpCode.add i64) (Arg.var h, Arg.imm 496, ()) fun p =>
        Expr.load i64 (Arg.var p.fst) fun ld =>
        fvOp (OpCode.sub i64) (Arg.var ld, Arg.imm 1, ()) fun p =>
        fvOp (OpCode.add i64) (Arg.var h, Arg.imm 496, ()) fun p4 =>
        Expr.store (Arg.var p.fst) (Arg.var p4.fst) (Expr.jump Js2.fst ()))
       (Expr.jump Js2.fst ()))
    (Expr.group (sig := [[]]) (fun _ => Blocks.cons (fun (_ : Tup Val []) =>
      Expr.jump Js ()) Blocks.nil) fun Js2 =>
     fvOp (OpCode.add i64) (Arg.var h, Arg.imm 488, ()) fun p =>
     Expr.load i64 (Arg.var p.fst) fun ld =>
     fvOp (OpCode.cmp .ugt i64 .bool (by decide)) (Arg.var ld, Arg.imm 0, ()) fun p =>
     Expr.jnz (Arg.var p.fst)
       (fvOp (OpCode.add i64) (Arg.var h, Arg.imm 488, ()) fun p =>
        Expr.load i64 (Arg.var p.fst) fun ld =>
        fvOp (OpCode.sub i64) (Arg.var ld, Arg.imm 1, ()) fun p =>
        fvOp (OpCode.add i64) (Arg.var h, Arg.imm 488, ()) fun p4 =>
        Expr.store (Arg.var p.fst) (Arg.var p4.fst) (Expr.jump Js2.fst ()))
       (Expr.jump Js2.fst ()))

theorem simplify_decr_wp (Γ : Env) {c : FullCfg} {s_b : FullState}
    {R : Mem 64 → Prop} {hdr_v : Val i32} {Js : Cont []} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (hm : (FullMem c s_b ⋆ R) m)
    (hJ : ∀ ni' nr' md,
      (FullMem c { s_b with core :=
        { s_b.core with num_irred := ni', num_redundant := nr' } } ⋆ R) md →
      Js () md) :
    wp Γ Q X (simplifyDecrExpr c.hdr hdr_v Js) m := by
  dsimp only [simplifyDecrExpr, fvOp]
  viv_step; viv_step
  · refine wp_join0 (fun md => ∃ nr',
        (FullMem c { s_b with core := { s_b.core with num_redundant := nr' } } ⋆ R) md)
      (fun _ md ⟨nr', hmd⟩ => hJ s_b.core.num_irred nr' md hmd)
      (fun J3 hJ3 => by
        viv_steps
        · viv_steps; refine hJ3 _ ⟨s_b.core.num_redundant - 1#64, ?_⟩; assumption
        · viv_steps; exact hJ3 _ ⟨_, hm⟩)
  · refine wp_join0 (fun md => ∃ ni',
        (FullMem c { s_b with core := { s_b.core with num_irred := ni' } } ⋆ R) md)
      (fun _ md ⟨ni', hmd⟩ => hJ ni' s_b.core.num_redundant md hmd)
      (fun J3 hJ3 => by
        viv_steps
        · viv_steps; refine hJ3 _ ⟨s_b.core.num_irred - 1#64, ?_⟩; assumption
        · viv_steps; exact hJ3 _ ⟨_, hm⟩)

abbrev simplifyNszGe3Expr (c : FullCfg) (cref hdr_v old_sz nsz_v : Val i32)
    (k_ok k_oom : Expr Val Cont [i64]) : Expr Val Cont [i64] :=
  Expr.store (Arg.var nsz_v)
    (Arg.var (c.pArena + (BitVec.setWidth 64 cref + 2) * 4))
    (fvOp (OpCode.zext 32 64) (Arg.var cref, ()) fun p =>
     fvOp (OpCode.add i64) (Arg.var p.fst, Arg.imm 1, ()) fun p =>
     fvOp (OpCode.mul i64) (Arg.var p.fst, Arg.imm 4, ()) fun p =>
     fvOp (OpCode.add i64) (Arg.var c.pArena, Arg.var p.fst, ()) fun p =>
     Expr.store (Arg.imm (t := i32) 2) (Arg.var p.fst)
       (Expr.group (sig := [[i32]]) (fun Js => Blocks.cons (fun (nhdr : Tup Val [i32]) =>
         Expr.group (sig := [[i32]]) (fun Js2 => Blocks.cons (fun (nhdr2 : Tup Val [i32]) =>
           fvOp (OpCode.zext 32 64) (Arg.var cref, ()) fun p1 =>
           fvOp (OpCode.mul i64) (Arg.var p1.fst, Arg.imm 4, ()) fun p2 =>
           fvOp (OpCode.add i64) (Arg.var c.pArena, Arg.var p2.fst, ()) fun p3 =>
           Expr.store (Arg.var nhdr2.fst) (Arg.var p3.fst)
             (fvOp (OpCode.zext 32 64) (Arg.var cref, ()) fun p =>
              fvOp (OpCode.add i64) (Arg.var p.fst, Arg.imm 3, ()) fun p =>
              fvOp (OpCode.mul i64) (Arg.var p.fst, Arg.imm 4, ()) fun p =>
              fvOp (OpCode.add i64) (Arg.var c.pArena, Arg.var p.fst, ()) fun p =>
              Expr.load i32 (Arg.var p.fst) fun ld =>
              fvOp (OpCode.zext 32 64) (Arg.var cref, ()) fun p =>
              fvOp (OpCode.add i64) (Arg.var p.fst, Arg.imm 4, ()) fun p =>
              fvOp (OpCode.mul i64) (Arg.var p.fst, Arg.imm 4, ()) fun p =>
              fvOp (OpCode.add i64) (Arg.var c.pArena, Arg.var p.fst, ()) fun p =>
              Expr.load i32 (Arg.var p.fst) fun ld1 =>
              watch2Expr c.hdr cref ld ld1 k_ok k_oom)) Blocks.nil)
           fun Js2 =>
           fvOp (OpCode.and i32) (Arg.var nhdr.fst, Arg.imm 8388608, ()) fun p1 =>
           fvOp (OpCode.cmp .eq i32 .bool (by decide)) (Arg.var p1.fst, Arg.imm 0, ()) fun p2 =>
           Expr.jnz (Arg.var p2.fst)
             (fvOp (OpCode.zext 32 64) (Arg.var cref, ()) fun p3 =>
              fvOp (OpCode.add i64) (Arg.var p3.fst, Arg.imm 3, ()) fun p4 =>
              fvOp (OpCode.zext 32 64) (Arg.var old_sz, ()) fun p5 =>
              fvOp (OpCode.add i64) (Arg.var p4.fst, Arg.var p5.fst, ()) fun p6 =>
              fvOp (OpCode.sub i64) (Arg.var p6.fst, Arg.imm 1, ()) fun p7 =>
              fvOp (OpCode.mul i64) (Arg.var p7.fst, Arg.imm 4, ()) fun p8 =>
              fvOp (OpCode.add i64) (Arg.var c.pArena, Arg.var p8.fst, ()) fun p9 =>
              Expr.store (Arg.imm (t := i32) 4294967295) (Arg.var p9.fst)
                (fvOp (OpCode.or i32) (Arg.var nhdr.fst, Arg.imm 8388608, ()) fun p =>
                 Expr.jump Js2.fst (Arg.var p.fst, ())))
             (Expr.jump Js2.fst (Arg.var nhdr.fst, ()))) Blocks.nil)
         fun Js =>
         fvOp (OpCode.and i32) (Arg.var hdr_v, Arg.imm 4194304, ()) fun p =>
         fvOp (OpCode.cmp .ne i32 .bool (by decide)) (Arg.var p.fst, Arg.imm 0, ()) fun p =>
         Expr.jnz (Arg.var p.fst)
           (fvOp (OpCode.and i32) (Arg.var hdr_v, Arg.imm 524287, ()) fun p =>
            Expr.group (sig := [[i32]]) (fun _ => Blocks.cons (fun p =>
              Expr.jump Js.fst (Arg.var p.fst, ())) Blocks.nil)
              fun Js1 =>
              fvOp (OpCode.cmp .uge i32 .bool (by decide)) (Arg.var p.fst, Arg.var nsz_v, ())
                fun p =>
                Expr.jnz (Arg.var p.fst)
                  (fvOp (OpCode.not i32) (Arg.imm 524287, ()) fun p =>
                   fvOp (OpCode.and i32) (Arg.var hdr_v, Arg.var p.fst, ()) fun p =>
                   fvOp (OpCode.sub i32) (Arg.var nsz_v, Arg.imm 1, ()) fun p1 =>
                   fvOp (OpCode.and i32) (Arg.var p1.fst, Arg.imm 524287, ()) fun p2 =>
                   fvOp (OpCode.or i32) (Arg.var p.fst, Arg.var p2.fst, ()) fun p =>
                   Expr.jump Js1.fst (Arg.var p.fst, ()))
                  (Expr.jump Js1.fst (Arg.var hdr_v, ())))
           (Expr.jump Js.fst (Arg.var hdr_v, ()))))

private theorem bv32_bit23_true : (0x800000#32)[23] = true := by decide

theorem simplify_nsz_ge3_wp (Γ : Env)
    (hWpush : Γ.Has "full_watch_push" fullWatchPushSpec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s0 s2 : FullState}
    {R : Mem 64 → Prop} {cref old_sz hdr_v nsz_v : Val i32}
    {k_ok k_oom : Expr Val Cont [i64]} {ar_c : List (BitVec 32)} {idxs : List Nat}
    {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hsp2 : FullSparseInvW c F0 F_cur s2) (hcl2 : s2.core.cur_level = 0)
    (hs2_ar : s2.core.arena = s0.core.arena) (hs2_cv : s2.core.cur_vars = s0.core.cur_vars)
    (hs2_al : s2.core.arena_len = s0.core.arena_len) (hs2_pr : s2.core.probing = s0.core.probing)
    (hs2_fu : s2.core.fuel = s0.core.fuel)
    (hrefs2 : fullArenaClauseRefs s2 = fullArenaClauseRefs s0)
    (href0 : cref.toNat ∈ fullArenaClauseRefs s0) (hg0 : fullArenaClauseGarb s0 cref.toNat = false)
    (hhdr_v : hdr_v = fullArenaHdr s2 cref.toNat)
    (hsz0 : fullArenaClauseSize s0 cref.toNat = old_sz.toNat)
    (hbd2 : cref.toNat + 3 + fullArenaClauseSizeCore s2.core cref.toNat ≤ s2.core.arena.length)
    (hnsz3 : 3 ≤ nsz_v.toNat) (hnsz_lt : nsz_v.toNat < old_sz.toNat)
    (harc_len : ar_c.length = c.arena_cap) (hlen_i : idxs.length = nsz_v.toNat)
    (hpw_i : List.Pairwise (· < ·) idxs) (hq_i : ∀ q ∈ idxs, q < old_sz.toNat)
    (hout_i : ∀ p, (p < cref.toNat + 3 ∨ cref.toNat + 3 + nsz_v.toNat ≤ p) →
      ar_c[p]? = s2.core.arena[p]?)
    (hmap_i : ∀ t < nsz_v.toNat,
      ar_c[cref.toNat + 3 + t]? = s2.core.arena[cref.toNat + 3 + idxs[t]?.getD 0]?)
    (hdrop_i : ∀ j < old_sz.toNat, j ∈ idxs ∨
      ((s2.core.arena[cref.toNat + 3 + j]?.getD 0#32).toNat < 2 * s2.core.cur_vars ∧
        s2.core.vals[(s2.core.arena[cref.toNat + 3 + j]?.getD 0#32).toNat]?.getD 0#8 = 255#8))
    (hm : (FullMem c { s2 with core := { s2.core with arena := ar_c } } ⋆ R) m)
    (hok : ∀ s' m', FullSparseInvW c F0 F_cur s' → s'.core.cur_level = 0 →
      s'.core.cur_vars = s0.core.cur_vars → s'.core.arena_len = s0.core.arena_len →
      s'.core.probing = s0.core.probing → s'.core.fuel = s0.core.fuel →
      fullArenaClauseRefs s' = fullArenaClauseRefs s0 →
      s'.scratch.red_refs = s2.scratch.red_refs →
      s'.scratch.tarjan_reach = s2.scratch.tarjan_reach →
      cref.toNat ∈ fullArenaClauseRefs s' → fullArenaClauseGarb s' cref.toNat = false →
      (FullMem c s' ⋆ R) m' → wp Γ Q X k_ok m')
    (hoom : ∀ s' m', FullSparseInvW c F0 F_cur s' → s'.core.cur_level = 0 →
      s'.core.cur_vars = s0.core.cur_vars → s'.core.arena_len = s0.core.arena_len →
      s'.core.probing = s0.core.probing → s'.core.fuel = s0.core.fuel →
      fullArenaClauseRefs s' = fullArenaClauseRefs s0 →
      s'.scratch.red_refs = s2.scratch.red_refs →
      s'.scratch.tarjan_reach = s2.scratch.tarjan_reach →
      (FullMem c s' ⋆ R) m' → wp Γ Q X k_oom m') :
    wp Γ Q X (simplifyNszGe3Expr c cref hdr_v old_sz nsz_v k_ok k_oom) m := by
  subst hhdr_v
  have hcl2_ok := hsp2.1.core_ok
  have hsz2 : fullArenaClauseSizeCore s2.core cref.toNat = old_sz.toNat := by
    unfold fullArenaClauseSizeCore; rw [hs2_ar]; exact hsz0
  have href2 : cref.toNat ∈ fullArenaClauseRefs s2 := hrefs2.symm ▸ href0
  have hg2 : fullArenaClauseGarb s2 cref.toNat = false := by
    unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore; rw [hs2_ar]; exact hg0
  have hhdr0_ng : (fullArenaHdr s2 cref.toNat &&& 0x80000#32) = 0#32 := by
    unfold fullArenaClauseGarb fullArenaClauseGarbCore at hg2; simpa using hg2
  have hwf2 := hsp2.2.1.arena.refs_wf cref.toNat href2
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have harc_len' : cref.toNat + 3 + old_sz.toNat ≤ ar_c.length := by
    rw [harc_len, ← hcl2_ok.arena_len_arr]; omega
  have hcref1_lt : cref.toNat + 1 < ar_c.length := by omega
  have hcref2_lt : cref.toNat + 2 < ar_c.length := by omega
  have hc0_idx : (BitVec.setWidth 64 cref).toNat = cref.toNat := by bv_omega
  have hc1_idx : (BitVec.setWidth 64 cref + 1#64).toNat = cref.toNat + 1 := by bv_omega
  have hc2_idx : (BitVec.setWidth 64 cref + 2#64).toNat = cref.toNat + 2 := by bv_omega
  have hcref2_bv_lt : (BitVec.setWidth 64 cref + 2#64).toNat < ar_c.length :=
    hc2_idx ▸ hcref2_lt
  have hc3_idx : (BitVec.setWidth 64 cref + 3#64).toNat = cref.toNat + 3 := by bv_omega
  have hc4_idx : (BitVec.setWidth 64 cref + 4#64).toNat = cref.toNat + 4 := by bv_omega
  have hterm_idx : (BitVec.setWidth 64 cref + 3#64 + BitVec.setWidth 64 old_sz - 1#64).toNat =
      cref.toNat + 3 + old_sz.toNat - 1 := by bv_omega
  let ar_sz := (ar_c.set (cref.toNat + 2) nsz_v).set (cref.toNat + 1) 2#32
  have harsz_len : ar_sz.length = c.arena_cap := by simp [ar_sz, harc_len]
  dsimp only [simplifyNszGe3Expr, fvOp]
  viv_to_group
  refine wp_join_group (ts := [i32])
    (fun (nhdr, ()) m_g => (FullMem c { s2 with core := { s2.core with arena := ar_sz } } ⋆ R) m_g ∧
      (nhdr &&& 0x80000#32) = 0#32 ∧
      (nhdr &&& 0x800000#32) = (fullArenaHdr s2 cref.toNat &&& 0x800000#32))
    ?_ ?_
  · rintro _ ⟨nhdr, ⟨⟩⟩ m_g ⟨hm_g, hng_nh, hsh_nh⟩
    refine wp_join_group (ts := [i32])
      (fun (nhdr2, ()) m_p => ∃ ar_p : List (BitVec 32), ar_p.length = c.arena_cap ∧
        (nhdr2 &&& 0x80000#32) = 0#32 ∧ (nhdr2 &&& 0x800000#32) ≠ 0#32 ∧
        (∀ p, (p < cref.toNat ∨ cref.toNat + 3 + old_sz.toNat ≤ p) →
          ar_p[p]? = s2.core.arena[p]?) ∧
        (ar_p[cref.toNat + 2]?.getD 0#32).toNat = nsz_v.toNat ∧
        (∀ j < nsz_v.toNat, ar_p[cref.toNat + 3 + j]? = ar_c[cref.toNat + 3 + j]?) ∧
        M6ShrkPad ar_p s2.core.arena cref.toNat old_sz.toNat nsz_v.toNat ∧
        (FullMem c { s2 with core := { s2.core with arena := ar_p } } ⋆ R) m_p) ?_ ?_
    · rintro _ ⟨nhdr2, ⟨⟩⟩ m_p ⟨ar_p, harp_len, hng2, hsh2, hout_p, hsz_p, hpay_p, hpad_p, hm_p⟩
      viv_to_group
      let ar_f := ar_p.set cref.toNat nhdr2
      let s_f : FullState := { s2 with core := { s2.core with arena := ar_f } }
      have harf_len : ar_f.length = c.arena_cap := by simp [ar_f, harp_len]
      have hout_f : ∀ p, (p < cref.toNat ∨ cref.toNat + 3 + old_sz.toNat ≤ p) →
          ar_f[p]? = s2.core.arena[p]? := fun p hp => by
        dsimp only [ar_f]; rw [List.getElem?_set_ne (by omega)]; exact hout_p p hp
      have hpay_f : ∀ j < nsz_v.toNat, ar_f[cref.toNat + 3 + j]? =
          ar_c[cref.toNat + 3 + j]? := fun j hj => by
        dsimp only [ar_f]; rw [List.getElem?_set_ne (by omega)]; exact hpay_p j hj
      have hpad_f : M6ShrkPad ar_f s2.core.arena cref.toNat old_sz.toNat nsz_v.toNat := by
        unfold M6ShrkPad at hpad_p ⊢; split
        · rename_i h0; rw [ite_eq_left h0] at hpad_p
          exact ⟨fun k hk1 hk2 => by
              dsimp only [ar_f]; rw [List.getElem?_set_ne (by omega)]; exact hpad_p.1 k hk1 hk2,
            by dsimp only [ar_f]; rw [List.getElem?_set_ne (by omega)]; exact hpad_p.2⟩
        · rename_i hne; rw [ite_eq_right hne] at hpad_p
          exact fun k hk1 hk2 => by
            dsimp only [ar_f]; rw [List.getElem?_set_ne (by omega)]; exact hpad_p k hk1 hk2
      obtain ⟨hsp_f, hrefs_f, hl0_lt, hl1_lt⟩ := simplify_nsz_ge3_prep hsp2 hcl2 href2
        hg2 hsz2 hnsz3 hnsz_lt hbd2 harc_len hlen_i hpw_i hq_i hout_i hmap_i hdrop_i
        harf_len hng2 hsh2 (by dsimp only [ar_f]; rw [List.getElem?_set_self (by omega)])
        (by dsimp only [ar_f]; rw [List.getElem?_set_ne (by omega)]; exact hsz_p)
        hpay_f hout_f hpad_f
      have href_f : cref.toNat ∈ fullArenaClauseRefs s_f := hrefs_f.symm ▸ href2
      have hgarb_f : fullArenaClauseGarb s_f cref.toNat = false := by
        unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
        change ((ar_f[cref.toNat]?.getD 0#32 &&& 0x80000#32) != 0#32) = false
        rw [List.getElem?_set_self (by omega), Option.getD_some, hng2]
        exact bne_self_eq_false _
      have hsref_s0 : fullArenaClauseRefs s_f = fullArenaClauseRefs s0 := hrefs_f.trans hrefs2
      have hcref_b32 : cref.toNat < 0x80000000 := by
        have hcap := c.harena; unfold dimacsBound at hcap
        have := hwf2.1; have := hcl2_ok.arena_len_le; omega
      refine watch2_calls_wp Γ hWpush hsp_f hcref_b32 href0 hsref_s0
        ⟨hs2_al, hs2_cv, hs2_pr, hs2_fu⟩ ?_
        (fun so mo hspo haro halo hcvo hpro hfuo hclo hrro htro hrefso hmo => by
          have hgarb_o : fullArenaClauseGarb so cref.toNat = false := by
            unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
            rw [haro]; exact hgarb_f
          exact hok so mo hspo (hclo.trans hcl2) hcvo halo hpro hfuo hrefso hrro htro
            (hrefso.symm ▸ href0) hgarb_o hmo)
        (fun so mo hspo _ halo hcvo hpro hfuo hclo hrro htro hrefso hmo =>
          hoom so mo hspo (hclo.trans hcl2) hcvo halo hpro hfuo hrefso hrro htro hmo)
      · dsimp only [s_f, ar_f]; rw [← hc0_idx]; assumption
    · intro Jp hJp
      viv_steps
      · have hng_o : ((nhdr ||| 0x800000#32) &&& 0x80000#32) = 0#32 := by
          rw [BitVec.and_or_distrib_right, hng_nh,
            show (0x800000#32 &&& 0x80000#32) = 0#32 from by decide]; simp
        have hsh_o : ((nhdr ||| 0x800000#32) &&& 0x800000#32) ≠ 0#32 := by
          intro h; have h23 := congrArg (·[23]) h
          simp [bv32_bit23_true] at h23
        have hsh0_zero : (fullArenaHdr s2 cref.toNat &&& 0x800000#32) = 0#32 := by
          rw [← hsh_nh]; exact hc
        let tidx := (BitVec.setWidth 64 cref + 3#64 + BitVec.setWidth 64 old_sz - 1#64).toNat
        let ar_p := ar_sz.set tidx 0xFFFFFFFF#32
        refine hJp (nhdr ||| 0x800000#32, ()) _
          ⟨ar_p, by simp [ar_p, harsz_len], hng_o, hsh_o, ?_, ?_, ?_, ?_, ?_⟩
        · intro p hp
          dsimp only [ar_p, ar_sz]
          rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
            List.getElem?_set_ne (by omega)]
          exact hout_i p (by omega)
        · dsimp only [ar_p, ar_sz]
          rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
            List.getElem?_set_self (by rw [harc_len, ← hcl2_ok.arena_len_arr]; omega),
            Option.getD_some]
        · intro j hj
          dsimp only [ar_p, ar_sz]
          rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
            List.getElem?_set_ne (by omega)]
        · unfold M6ShrkPad; split
          · refine ⟨fun k hk1 hk2 => ?_, ?_⟩
            · dsimp only [ar_p, ar_sz]
              rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
                List.getElem?_set_ne (by omega)]
              exact hout_i k (Or.inr hk1)
            · dsimp only [ar_p, ar_sz]
              have ht_eq : cref.toNat + 3 + old_sz.toNat - 1 = tidx := hterm_idx.symm
              rw [ht_eq, List.getElem?_set_self (by rw [harsz_len, ← hcl2_ok.arena_len_arr]; omega)]
          · rename_i hne; exact False.elim (hne hsh0_zero)
        · assumption
      · have hsz_p : (ar_sz[cref.toNat + 2]?.getD 0#32).toNat = nsz_v.toNat := by
          dsimp only [ar_sz]
          rw [List.getElem?_set_ne (by omega),
            List.getElem?_set_self (by rw [harc_len, ← hcl2_ok.arena_len_arr]; omega),
            Option.getD_some]
        have hout_p : ∀ p, (p < cref.toNat ∨ cref.toNat + 3 + old_sz.toNat ≤ p) →
            ar_sz[p]? = s2.core.arena[p]? := fun p hp => by
          dsimp only [ar_sz]
          rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
          exact hout_i p (by omega)
        have hpay_p : ∀ j < nsz_v.toNat, ar_sz[cref.toNat + 3 + j]? =
            ar_c[cref.toNat + 3 + j]? := fun j hj => by
          dsimp only [ar_sz]
          rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
        have hpad_p : M6ShrkPad ar_sz s2.core.arena cref.toNat old_sz.toNat nsz_v.toNat := by
          have hsh0_ne : (fullArenaHdr s2 cref.toNat &&& 0x800000#32) ≠ 0#32 := by
            rw [← hsh_nh]; assumption
          unfold M6ShrkPad; split
          · rename_i h0; exact False.elim (hsh0_ne h0)
          · intro k hk1 hk2
            dsimp only [ar_sz]
            rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
            exact hout_i k (Or.inr hk1)
        exact hJp (nhdr, ()) _ ⟨ar_sz, harsz_len, hng_nh, by assumption, hout_p,
          hsz_p, hpay_p, hpad_p, hm_g⟩
  · intro Jg hJg
    have hm_sz : (FullMem c { s2 with core := { s2.core with arena := ar_sz } } ⋆ R) m := by
      simpa [ar_sz, hc1_idx, hc2_idx] using hm
    viv_step; viv_step
    · viv_to_group
      refine wp_join_group (ts := [i32])
        (fun (nhdr, ()) mg =>
          (FullMem c { s2 with core := { s2.core with arena := ar_sz } } ⋆ R) mg ∧
          (nhdr &&& 0x80000#32) = 0#32 ∧
          (nhdr &&& 0x800000#32) = (fullArenaHdr s2 cref.toNat &&& 0x800000#32))
        (fun _ ⟨nhdr, ⟨⟩⟩ mg h => hJg (nhdr, ()) mg h)
        (fun Ji hJi => by
          viv_steps
          · refine hJi (_, ()) _ ⟨hm_sz, ?_, ?_⟩
            · rw [← hhdr0_ng]
              exact bv32_replace_lo_and_eq _ (nsz_v - 1#32) 524287#32 0x80000#32 (by decide)
            · exact bv32_replace_lo_and_eq _ (nsz_v - 1#32) 524287#32 0x800000#32 (by decide)
          · exact hJi (_, ()) _ ⟨hm_sz, hhdr0_ng, rfl⟩)
    · viv_steps
      exact hJg (_, ()) _ ⟨hm_sz, hhdr0_ng, rfl⟩

theorem viv_bv32_ge3_of_ne (x : BitVec 32)
    (h0 : x ≠ 0#32) (h1 : x ≠ 1#32) (h2 : x ≠ 2#32) : 3 ≤ x.toNat := by
  have hn0 : x.toNat ≠ 0 := fun h => h0 (BitVec.eq_of_toNat_eq h)
  have hn1 : x.toNat ≠ 1 := fun h => h1 (BitVec.eq_of_toNat_eq h)
  have hn2 : x.toNat ≠ 2 := fun h => h2 (BitVec.eq_of_toNat_eq h)
  omega

theorem viv_range_entails_1 {F : CNF Nat} {ar : List (BitVec 32)} {cref nsz : Nat}
    (h1 : nsz = 1) (hbd : cref + 3 + 1 ≤ ar.length)
    (h : F.EntailsClause
      (cnfClause ((List.range nsz).map fun t => (ar[cref + 3 + t]?.getD 0#32).toNat))) :
    F.EntailsClause (cnfClause [(ar[cref + 3]'(by omega)).toNat]) := by
  subst h1
  have h0 := List.getElem?_eq_getElem (by omega : cref + 3 < ar.length)
  simpa [List.range_succ, h0, Option.getD_some] using h

theorem viv_range_entails_2 {F : CNF Nat} {ar : List (BitVec 32)} {cref nsz : Nat}
    (h2 : nsz = 2) (hbd : cref + 3 + 2 ≤ ar.length)
    (h : F.EntailsClause
      (cnfClause ((List.range nsz).map fun t => (ar[cref + 3 + t]?.getD 0#32).toNat))) :
    F.EntailsClause
      (cnfClause [(ar[cref + 3]'(by omega)).toNat, (ar[cref + 4]'(by omega)).toNat]) := by
  subst h2
  have h0 := List.getElem?_eq_getElem (by omega : cref + 3 < ar.length)
  have h1 := List.getElem?_eq_getElem (by omega : cref + 4 < ar.length)
  simpa [List.range_succ, show cref + 3 + 1 = cref + 4 by omega, h0, h1, Option.getD_some] using h

theorem viv_bv64_zext32_lshr1 (x : BitVec 32) :
    (BitVec.setWidth 64 x >>> 1#64).toNat = x.toNat / 2 := by
  have hlt64 : x.toNat < 2 ^ 64 := Nat.lt_trans x.isLt (by decide)
  have h : (BitVec.setWidth 64 x >>> 1#64).toNat = (BitVec.setWidth 64 x).toNat >>> 1 := by
    simp [BitVec.toNat_ushiftRight]
  rw [h, BitVec.toNat_setWidth, Nat.mod_eq_of_lt hlt64, Nat.shiftRight_eq_div_pow, Nat.pow_one]

theorem simplify_lit_idx_facts {ar ar0 : List (BitVec 32)} {vals : List (BitVec 8)}
    {cref i : BitVec 32} {idx cv mv : Nat}
    (hidx : idx = cref.toNat + 3 + i.toNat)
    (hbd_ar : cref.toNat + 3 + i.toNat < ar.length)
    (hbd_ar0 : cref.toNat + 3 + i.toNat < ar0.length)
    (heq_ar : ar[cref.toNat + 3 + i.toNat]? = ar0[cref.toNat + 3 + i.toNat]?)
    (hlit : (ar0[cref.toNat + 3 + i.toNat]?.getD 0#32).toNat < 2 * cv)
    (hcv : cv ≤ mv) (hvl : vals.length = 2 * mv) :
    ar[idx]'(by rw [hidx]; exact hbd_ar) = ar0[cref.toNat + 3 + i.toNat] ∧
    ∃ (hvl_bd : (ar[idx]'(by rw [hidx]; exact hbd_ar)).toNat < vals.length),
    vals[(ar0[cref.toNat + 3 + i.toNat]?.getD 0#32).toNat]?.getD 0#8 =
      vals[(ar[idx]'(by rw [hidx]; exact hbd_ar)).toNat] := by
  subst hidx
  have hlit_eq : ar[cref.toNat + 3 + i.toNat] = ar0[cref.toNat + 3 + i.toNat] :=
    Option.some.inj (by
      rw [← List.getElem?_eq_getElem hbd_ar, heq_ar, ← List.getElem?_eq_getElem hbd_ar0])
  rw [List.getElem?_eq_getElem hbd_ar0, Option.getD_some] at hlit
  have hvl_bd : ar[cref.toNat + 3 + i.toNat].toNat < vals.length := by rw [hlit_eq]; omega
  have hval_eq : vals[(ar0[cref.toNat + 3 + i.toNat]?.getD 0#32).toNat]?.getD 0#8 =
      vals[ar[cref.toNat + 3 + i.toNat].toNat] := by
    rw [List.getElem?_eq_getElem hbd_ar0, Option.getD_some, ← hlit_eq,
      List.getElem?_eq_getElem hvl_bd, Option.getD_some]
  exact ⟨hlit_eq, hvl_bd, hval_eq⟩

end

end LeanQbe.T.Examples.Kissat.Proof.Vivify
