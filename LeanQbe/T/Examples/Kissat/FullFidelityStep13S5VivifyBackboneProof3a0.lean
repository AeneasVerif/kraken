/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S5VivifyBackboneProof0a
public import LeanQbe.T.Examples.Kissat.FullM6VivBackboneProof4a
public import LeanQbe.T.Examples.Kissat.FullM3BackboneLemmas1
import LeanQbe.T.Examples.Kissat.FullVivTopLemmas1
import LeanQbe.T.Examples.Kissat.FullTransLemmas1
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb

/-!
# Kissat Fidelity Step 13 Shard S5-B — Backbone `keep`, `prop`, `analyze` (`Proof3a0`)

Proves UNSAT-sound `Func.wp` (`XPost := False`, `0` `@[expose]` on theorems/lemmas, `<= 100`
cols, every theorem `<= 420` lines) for:
1. `full_backbone_keep_m6_s5_wp` (`FullM6VivBackbone.fullBackboneKeepM6Spec`)
2. `full_backbone_prop_m6_s5_wp` (`step13BackbonePropM6Spec`)
3. `full_backbone_analyze_m6_s5_wp` (`step13BackboneAnalyzeM6Spec`)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S5

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Full
open Kraken.Bedrock2.Test
open FullVivTopTactics FullM6VivBackbone
open scoped FullArenaTactics FullVivTopTactics

/-! ## 1. Pure & Trail Invariant Helpers (`BbS5Helpers`) -/

section BbS5Helpers

private theorem s13_bb_bv32_lshr1 (x : BitVec 32) : (x >>> 1#32).toNat = x.toNat / 2 := by
  change (x >>> (1 : Nat)).toNat = x.toNat / 2
  rw [BitVec.toNat_ushiftRight]; simp [Nat.shiftRight_eq_div_pow]
private theorem s13_bb_bv32_xor1 (x : BitVec 32) : (x ^^^ 1#32).toNat = x.toNat ^^^ 1 := by
  rw [BitVec.toNat_xor]; rfl
private theorem s13_bb_bv64_shl1_nat (x : BitVec 64) (hx : x.toNat < 2 ^ 63) :
    (x <<< (1 : Nat)).toNat = 2 * x.toNat := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.pow_one, Nat.mul_comm,
    Nat.mod_eq_of_lt (by omega)]
private theorem s13_bb_bv64_shl1_sext (x : BitVec 64) (hx : x.toNat < 2 ^ 63) :
    (x <<< (BitVec.signExtend 64 1#32)).toNat = 2 * x.toNat :=
  s13_bb_bv64_shl1_nat x hx
private theorem s13_bb_bv8_dom_slt0 {x : BitVec 8} (h : x = 0#8 ∨ x = 1#8 ∨ x = 0xFF#8) :
    (x.signExtend 32).slt 0#32 = true ↔ x = 0xFF#8 := by rcases h with rfl | rfl | rfl <;> decide
private theorem s13_bb_bv8_sext32_eq0 : ∀ x : BitVec 8, x.signExtend 32 = 0#32 ↔ x = 0#8 := by
  decide
private theorem s13_bb_bv8_zext32_eq0 : ∀ x : BitVec 8, x.setWidth 32 = 0#32 ↔ x = 0#8 := by
  decide
private theorem s13_bb_xor1_xor1 (n : Nat) : (n ^^^ 1) ^^^ 1 = n := by
  apply Nat.eq_of_testBit_eq; intro i; simp [Nat.testBit_xor]
private theorem s13_bb_entails_comm2 {F : CNF Nat} {a b : Nat}
    (h : F.EntailsClause (cnfClause [a, b])) : F.EntailsClause (cnfClause [b, a]) := by
  rw [CNF.entails_clause_def] at h ⊢; intro α hα
  obtain ⟨l, hm, hs⟩ := (clause_sat_cnfClause_iff α _).mp (h α hα)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  exact (clause_sat_cnfClause_iff α _).mpr ⟨l, by simp [hm.symm], hs⟩
private theorem s13_bb_fullMem_eq {c : FullCfg} {s1 s2 : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} (h : s1 = s2) (hm : (FullMem c s1 ⋆ R) m) : (FullMem c s2 ⋆ R) m := h ▸ hm
private theorem s13_bb_fullMem_symm {c : FullCfg} {s1 s2 : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} (hm : (FullMem c s1 ⋆ R) m) (h : s1 = s2) : (FullMem c s2 ⋆ R) m := h ▸ hm

private theorem s13_bb_sparseW_with_flags {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullSparseInvW c F0 F_cur s) {fl' : List (BitVec 32)}
    (hfl : fl'.length = c.max_vars) :
    FullSparseInvW c F0 F_cur { s with core := { s.core with flags := fl' } } :=
  ⟨⟨{ h.1.core_ok with flags_len := hfl }, h.1.scratch_ok⟩,
    { h.2.1 with
      arena := { h.2.1.arena with len_ok := h.2.1.arena.len_ok }
      watches := h.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) },
    h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

private theorem s13_bb_mask7f_or_bin (x : BitVec 32) :
    (((x &&& 0x7FFFFFFF#32) ||| 0x80000000#32) &&& 0x80000000#32) ≠ 0#32 ∧
    (((x &&& 0x7FFFFFFF#32) ||| 0x80000000#32) &&& 0x7FFFFFFF#32) = (x &&& 0x7FFFFFFF#32) := by
  constructor
  · intro hz; have hbit := congrArg (fun b : BitVec 32 => b[31]) hz; simp at hbit
  · rw [BitVec.and_or_distrib_right, show (0x80000000#32 &&& 0x7FFFFFFF#32) = 0#32 from rfl,
      BitVec.or_zero, BitVec.and_assoc,
      show (0x7FFFFFFF#32 &&& 0x7FFFFFFF#32) = 0x7FFFFFFF#32 from rfl]

private theorem s13_bb_mask7f_eq_of_lt {x : BitVec 32} (h : x.toNat < 2 ^ 31) :
    (x &&& 0x7FFFFFFF#32).toNat = x.toNat := by
  have heq : x &&& 0x7FFFFFFF#32 = x := by
    apply BitVec.eq_of_getElem_eq; intro i hi; simp only [BitVec.getElem_and]
    by_cases h31 : i = 31
    · subst h31; have hf : x[31] = false := by
        rw [BitVec.getElem_eq_testBit_toNat, Nat.testBit_eq_decide_div_mod_eq]
        simp [Nat.div_eq_of_lt h]
      simp [hf]
    · have ht : (0x7FFFFFFF#32)[i] = true := by
        rw [BitVec.getElem_eq_testBit_toNat]; have : i < 31 := by omega
        revert i this; decide
      simp [ht]
  rw [heq]

theorem s13_bb_var_unassigned {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st : FullState} {saved0 max_lvl l : Nat}
    (hbt : BbTrailInv c F0 F_cur s0 st saved0 max_lvl)
    (_hl : l < 2 * s0.core.cur_vars) (h0 : st.core.vals[l]?.getD 0#8 = 0#8) :
    ∀ i < st.core.trail_end, (st.core.trl[i]?.getD 0#32).toNat / 2 ≠ l / 2 := by
  intro i hi heq; obtain ⟨hv1, hvff⟩ := hbt.trl_vals_ok i hi
  rcases (litVar_eq_iff _ _).mp heq with hl1 | hl2
  · rw [hl1, h0] at hv1; cases hv1
  · change (st.core.trl[i]?.getD 0#32).toNat = l ^^^ 1 at hl2
    rw [show (st.core.trl[i]?.getD 0#32).toNat ^^^ 1 = l by rw [hl2]; exact litNeg_litNeg l,
      h0] at hvff; cases hvff

private theorem s13_bb_with_ant_sz {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st : FullState} {saved0 max_lvl : Nat}
    (hbt : BbTrailInv c F0 F_cur s0 st saved0 max_lvl) (asz' : BitVec 64) :
    BbTrailInv c F0 F_cur s0 { st with scratch := { st.scratch with ant_sz := asz' } }
      saved0 max_lvl :=
  { hbt with
    len_ok := ⟨hbt.len_ok.core_ok, { hbt.len_ok.scratch_ok with }⟩
    same_scratch := by dsimp only; rw [hbt.same_scratch] }

private theorem s13_bb_with_confl_asz {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st : FullState} {saved0 max_lvl : Nat}
    (hbt : BbTrailInv c F0 F_cur s0 st saved0 max_lvl) (c0' c1' asz' : BitVec 64) :
    BbTrailInv c F0 F_cur s0
      { st with core := { st.core with confl_lit0 := c0', confl_lit1 := c1' }
                scratch := { st.scratch with ant_sz := asz' } } saved0 max_lvl :=
  { hbt with
    len_ok := ⟨{ hbt.len_ok.core_ok with }, { hbt.len_ok.scratch_ok with }⟩
    same_core := by dsimp only; rw [hbt.same_core]
    same_scratch := by dsimp only; rw [hbt.same_scratch] }

private theorem s13_bb_probeSeg_push {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st : FullState} {saved0 max_lvl saved target_lvl : Nat}
    (hbt : BbTrailInv c F0 F_cur s0 st saved0 max_lvl)
    (hseg : BackboneProbeSeg F_cur st saved target_lvl)
    {ot not_lit lv_bv : BitVec 32} {idx_p : Nat}
    (hot_lt : ot.toNat < 2 * s0.core.cur_vars)
    (h0 : st.core.vals[ot.toNat]?.getD 0#8 = 0#8)
    (hte_lt : st.core.trail_end < c.max_vars) (hlv_eq : lv_bv.toNat = target_lvl)
    (hnl_lt : not_lit.toNat < 2 * s0.core.cur_vars)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [ot.toNat, not_lit.toNat]))
    (hidx_ge : saved ≤ idx_p) (hidx_lt : idx_p < st.core.trail_end)
    (hidx_eq : (st.core.trl[idx_p]?.getD 0#32).toNat = not_lit.toNat ^^^ 1) :
    let v := ot.toNat / 2
    let rsn := (not_lit &&& 0x7FFFFFFF#32) ||| 0x80000000#32
    let st' : FullState :=
      { st with core := { st.core with
        vals := (st.core.vals.set ot.toNat 1#8).set (ot.toNat ^^^ 1) 0xFF#8
        lvl := st.core.lvl.set v lv_bv, rsns := st.core.rsns.set v rsn
        trl := st.core.trl.set st.core.trail_end ot, trail_end := st.core.trail_end + 1 } }
    BackboneProbeSeg F_cur st' saved target_lvl := by
  intro v rsn st'
  have hcl := hbt.len_ok.core_ok
  have hcv_eq : st.core.cur_vars = s0.core.cur_vars := by rw [hbt.same_core]
  have hcv_le : s0.core.cur_vars ≤ c.max_vars := hcv_eq ▸ hcl.cur_vars_le
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hmiss := s13_bb_var_unassigned hbt hot_lt h0
  have hte_trl : st.core.trail_end < st.core.trl.length := by rw [hcl.trl_len]; omega
  have hv_lvl : v < st.core.lvl.length := by rw [hcl.lvl_len]; omega
  have hv_rsn : v < st.core.rsns.length := by rw [hcl.rsns_len]; omega
  refine ⟨by dsimp only [st']; have := hseg.1; omega, fun i hi => ?_, fun i hi1 hi2 => ?_⟩
  · have hi_te : i < st.core.trail_end := by have := hseg.1; omega
    have hti : (st.core.trl.set st.core.trail_end ot)[i]? = st.core.trl[i]? :=
      List.getElem?_set_ne (by omega)
    dsimp only [st']; rw [hti, List.getElem?_set_ne (Ne.symm (hmiss i hi_te))]
    exact hseg.2.1 i hi
  · dsimp only [st'] at hi2 ⊢
    by_cases he : i = st.core.trail_end
    · subst he
      rw [List.getElem?_set_self hte_trl, Option.getD_some]
      refine ⟨by rw [List.getElem?_set_self hv_lvl, Option.getD_some]; exact hlv_eq, fun _ => ?_⟩
      rw [List.getElem?_set_self hv_rsn, Option.getD_some]
      obtain ⟨hbf, hm7⟩ := s13_bb_mask7f_or_bin not_lit
      have hm7_nat : (rsn &&& 0x7FFFFFFF#32).toNat = not_lit.toNat := by
        dsimp only [rsn]; rw [hm7]; exact s13_bb_mask7f_eq_of_lt (by omega)
      refine ⟨hbf, by rw [hm7_nat, hcv_eq]; exact hnl_lt, by rw [hm7_nat]; exact hent,
        idx_p, hidx_ge, hidx_lt, by rw [hm7_nat, List.getElem?_set_ne (by omega)]; exact hidx_eq⟩
    · have hi_te : i < st.core.trail_end := by omega
      rw [List.getElem?_set_ne (Ne.symm he), List.getElem?_set_ne (Ne.symm (hmiss i hi_te))]
      obtain ⟨hlv_i, hrsn_i⟩ := hseg.2.2 i hi1 hi_te
      refine ⟨hlv_i, fun hgt => ?_⟩
      rw [List.getElem?_set_ne (Ne.symm (hmiss i hi_te))]
      obtain ⟨hbf, hnq, hent_i, m, hm1, hm2, hmeq⟩ := hrsn_i hgt
      exact ⟨hbf, hnq, hent_i, m, hm1, hm2, by rw [List.getElem?_set_ne (by omega)]; exact hmeq⟩

private theorem s13_bb_probeSeg_with_confl_asz {F_cur : List (List Nat)} {st : FullState}
    {saved target_lvl : Nat} (hseg : BackboneProbeSeg F_cur st saved target_lvl)
    (c0' c1' asz' : BitVec 64) :
    BackboneProbeSeg F_cur
      { st with core := { st.core with confl_lit0 := c0', confl_lit1 := c1' }
                scratch := { st.scratch with ant_sz := asz' } } saved target_lvl := hseg

private theorem s13_bb_getD_set2_ne {α : Type} {xs : List α} {a b i : Nat} {x y d : α}
    (ha : i ≠ a) (hb : i ≠ b) : ((xs.set a x).set b y)[i]?.getD d = xs[i]?.getD d := by
  rw [List.getElem?_set_ne hb.symm, List.getElem?_set_ne ha.symm]

private theorem s13_bb_var_ne_xor {x y : Nat} (h : x / 2 ≠ y / 2) :
    x ≠ y ∧ x ≠ y ^^^ 1 ∧ x ^^^ 1 ≠ y ∧ x ^^^ 1 ≠ y ^^^ 1 :=
  ⟨fun e => h (by rw [e]), fun e => h (by rw [e, fullInv_var_xor1]),
   fun e => h (by rw [← e, fullInv_var_xor1]),
   fun e => h (by have := congrArg (· / 2) e; simpa only [fullInv_var_xor1] using this)⟩

private theorem s13_bb_pigeonhole_le :
    ∀ (n m : Nat) (f : Nat → Nat),
      (∀ i < m, f i < n) → (∀ i j, i < m → j < m → f i = f j → i = j) → m ≤ n
  | 0, m, f, hlt, _ => by
    cases m with
    | zero => exact Nat.le_refl 0
    | succ m' => exact absurd (hlt 0 (Nat.zero_lt_succ m')) (Nat.not_lt_zero _)
  | n + 1, m, f, hlt, hinj => by
    by_cases hex : ∃ k < m, f k = n
    · obtain ⟨k, hk, hfk⟩ := hex
      let g (i : Nat) : Nat := if i < k then f i else f (i + 1)
      have hg : m - 1 ≤ n := s13_bb_pigeonhole_le n (m - 1) g
        (fun i hi => by
          dsimp only [g]; split
          · have h1 := hlt i (by omega)
            have hne : f i ≠ n := fun h => by
              have := hinj i k (by omega) hk (h.trans hfk.symm); omega
            omega
          · have h1 := hlt (i + 1) (by omega)
            have hne : f (i + 1) ≠ n := fun h => by
              have := hinj (i + 1) k (by omega) hk (h.trans hfk.symm); omega
            omega)
        (fun i j hi hj heq => by
          dsimp only [g] at heq; split at heq <;> split at heq
          · exact hinj i j (by omega) (by omega) heq
          · have := hinj i (j + 1) (by omega) (by omega) heq; omega
          · have := hinj (i + 1) j (by omega) (by omega) heq; omega
          · have := hinj (i + 1) (j + 1) (by omega) (by omega) heq; omega)
      omega
    · have hlt' : ∀ i < m, f i < n := fun i hi => by
        have := hlt i hi; have hne : f i ≠ n := fun h => hex ⟨i, hi, h⟩; omega
      exact Nat.le_trans (s13_bb_pigeonhole_le n m f hlt' hinj) (Nat.le_succ n)

theorem s13_bb_push {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st : FullState} {saved0 max_lvl new_max : Nat}
    (hbt : BbTrailInv c F0 F_cur s0 st saved0 max_lvl)
    (hmax : max_lvl ≤ new_max) {lit rsn : BitVec 32} {lv_bv : BitVec 32} {cl' : Nat}
    (hlit : lit.toNat < 2 * s0.core.cur_vars) (h0 : st.core.vals[lit.toNat]?.getD 0#8 = 0#8)
    (hte_lt : st.core.trail_end < c.max_vars) (hlv_le : lv_bv.toNat ≤ new_max)
    (hcl_le : cl' ≤ new_max)
    (hl0_ent : lv_bv.toNat = 0 → (cnfOfClauses F_cur).EntailsClause (cnfClause [lit.toNat])) :
    let v := lit.toNat / 2
    let st' : FullState :=
      { st with core := { st.core with
        vals := (st.core.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8
        lvl := st.core.lvl.set v lv_bv
        rsns := st.core.rsns.set v rsn
        trl := st.core.trl.set st.core.trail_end lit
        trail_end := st.core.trail_end + 1
        cur_level := cl' } }
    BbTrailInv c F0 F_cur s0 st' saved0 new_max := by
  intro v st'
  have hcl := hbt.len_ok.core_ok
  have hcv_eq : st.core.cur_vars = s0.core.cur_vars := by rw [hbt.same_core]
  have hcv_le : s0.core.cur_vars ≤ c.max_vars := hcv_eq ▸ hcl.cur_vars_le
  have hmiss := s13_bb_var_unassigned hbt hlit h0
  have hne_lit : lit.toNat ≠ lit.toNat ^^^ 1 := (litNeg_ne_self lit.toNat).symm
  have hnot_lt : lit.toNat ^^^ 1 < 2 * s0.core.cur_vars := litNeg_lt_two_mul hlit
  have h0_s0 : s0.core.vals[lit.toNat]?.getD 0#8 = 0#8 :=
    Classical.byContradiction fun hnz => by rw [hbt.vals_prefix _ hlit hnz] at h0; exact hnz h0
  have h0_not : st.core.vals[lit.toNat ^^^ 1]?.getD 0#8 = 0#8 := by
    rcases hbt.vals_dom _ hnot_lt with hz | h1 | hff
    · exact hz
    · obtain ⟨i, hi, heq⟩ := hbt.vals_true_trl _ hnot_lt h1
      exact absurd (by rw [heq, fullInv_var_xor1]) (hmiss i hi)
    · obtain ⟨i, hi, heq⟩ := hbt.vals_false_trl _ hnot_lt hff
      rw [show (lit.toNat ^^^ 1) ^^^ 1 = lit.toNat from litNeg_litNeg _] at heq
      exact absurd (by rw [heq]) (hmiss i hi)
  have h0_not_s0 : s0.core.vals[lit.toNat ^^^ 1]?.getD 0#8 = 0#8 :=
    Classical.byContradiction fun hnz => by
      rw [hbt.vals_prefix _ hnot_lt hnz] at h0_not; exact hnz h0_not
  have hv_len := hcl.vals_len; have hl_len := hcl.lvl_len
  have hr_len := hcl.rsns_len; have ht_len := hcl.trl_len
  have hv_lt : v < c.max_vars := by omega
  have hte_lt_cv : st.core.trail_end < s0.core.cur_vars := by
    let f (i : Nat) : Nat :=
      if i < st.core.trail_end then (st.core.trl[i]?.getD 0#32).toNat / 2 else v
    have hle := s13_bb_pigeonhole_le s0.core.cur_vars (st.core.trail_end + 1) f
      (fun i hi => by
        dsimp only [f]; split
        · rename_i hlt; have := hbt.trl_lits_lt i hlt; omega
        · omega)
      (fun i j hi hj heq => by
        dsimp only [f] at heq; split at heq <;> split at heq
        · exact hbt.trl_vars_nodup i j ‹_› ‹_› heq
        · exact absurd heq (hmiss i ‹_›)
        · exact absurd heq.symm (hmiss j ‹_›)
        · omega)
    omega
  have hte_eq_len : st.core.trail_end < st.core.trl.length := by omega
  exact
    { len_ok := ⟨{ hcl with
        vals_len := by simp [st', hv_len], lvl_len := by simp [st', hl_len]
        rsns_len := by simp [st', hr_len], trl_len := by simp [st', ht_len]
        trail_end_le := by simp [st', hcv_eq]; omega
        propagated_le := by simp [st']; have := hcl.propagated_le; omega }, hbt.len_ok.scratch_ok⟩
      s0_l0 := hbt.s0_l0, same_core := by dsimp only [st']; rw [hbt.same_core]
      same_scratch := hbt.same_scratch, saved0_eq := hbt.saved0_eq
      saved0_le := by dsimp only [st']; have := hbt.saved0_le; omega
      cur_le_max := hcl_le
      trl_prefix := fun i hi => by
        dsimp only [st']; rw [List.getElem?_set_ne (by have := hbt.saved0_le; omega)]
        exact hbt.trl_prefix i hi
      vals_prefix := fun l hl hnz => by
        dsimp only [st']
        rw [s13_bb_getD_set2_ne (fun e => hnz (by rw [e]; exact h0_s0))
          (fun e => hnz (by rw [e]; exact h0_not_s0))]
        exact hbt.vals_prefix l hl hnz
      vals_hi := fun l hl => by
        dsimp only [st']
        rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
        exact hbt.vals_hi l hl
      lvl_prefix := fun i hi => by
        have hti := hbt.trl_prefix i hi
        have hne_v : (s0.core.trl[i]?.getD 0#32).toNat / 2 ≠ v := by
          rw [← hti]; exact hmiss i (by have := hbt.saved0_le; omega)
        dsimp only [st']
        rw [List.getElem?_set_ne hne_v.symm, List.getElem?_set_ne hne_v.symm]
        exact hbt.lvl_prefix i hi
      trl_lits_lt := fun i hi => by
        dsimp only [st'] at hi ⊢
        by_cases he : i = st.core.trail_end
        · subst he; rw [List.getElem?_set_self hte_eq_len, Option.getD_some]; exact hlit
        · rw [List.getElem?_set_ne (Ne.symm he)]; exact hbt.trl_lits_lt i (by omega)
      trl_vars_nodup := fun i j hi hj heq => by
        dsimp only [st'] at hi hj heq
        by_cases hie : i = st.core.trail_end <;> by_cases hje : j = st.core.trail_end
        · omega
        · subst hie; rw [List.getElem?_set_self hte_eq_len, Option.getD_some,
            List.getElem?_set_ne (Ne.symm hje)] at heq
          exact absurd heq.symm (hmiss j (by omega))
        · subst hje; rw [List.getElem?_set_self hte_eq_len, Option.getD_some,
            List.getElem?_set_ne (Ne.symm hie)] at heq
          exact absurd heq (hmiss i (by omega))
        · rw [List.getElem?_set_ne (Ne.symm hie), List.getElem?_set_ne (Ne.symm hje)] at heq
          exact hbt.trl_vars_nodup i j (by omega) (by omega) heq
      trl_vals_ok := fun i hi => by
        dsimp only [st'] at hi ⊢
        by_cases he : i = st.core.trail_end
        · subst he; rw [List.getElem?_set_self hte_eq_len, Option.getD_some]
          refine ⟨by rw [List.getElem?_set_ne hne_lit.symm,
                       List.getElem?_set_self (by omega), Option.getD_some],
                  by rw [List.getElem?_set_self (by simp [hv_len]; omega), Option.getD_some]⟩
        · rw [List.getElem?_set_ne (Ne.symm he)]
          obtain ⟨h1, h2, h3, h4⟩ := s13_bb_var_ne_xor (hmiss i (by omega))
          rw [s13_bb_getD_set2_ne h1 h2, s13_bb_getD_set2_ne h3 h4]
          exact hbt.trl_vals_ok i (by omega)
      vals_dom := fun l hl => by
        dsimp only [st']
        by_cases h1 : l = lit.toNat ^^^ 1
        · subst h1; right; right
          rw [List.getElem?_set_self (by simp [hv_len]; omega), Option.getD_some]
        · rw [List.getElem?_set_ne (Ne.symm h1)]
          by_cases h2 : l = lit.toNat
          · subst h2; right; left
            rw [List.getElem?_set_self (by omega), Option.getD_some]
          · rw [List.getElem?_set_ne (Ne.symm h2)]; exact hbt.vals_dom l hl
      vals_true_trl := fun l hl hv1 => by
        dsimp only [st'] at hv1 ⊢
        by_cases h1 : l = lit.toNat ^^^ 1
        · subst h1; rw [List.getElem?_set_self (by simp [hv_len]; omega), Option.getD_some] at hv1
          cases hv1
        · rw [List.getElem?_set_ne (Ne.symm h1)] at hv1
          by_cases h2 : l = lit.toNat
          · subst h2; exact ⟨st.core.trail_end, by omega, by
              rw [List.getElem?_set_self hte_eq_len, Option.getD_some]⟩
          · rw [List.getElem?_set_ne (Ne.symm h2)] at hv1
            obtain ⟨i, hi, heq⟩ := hbt.vals_true_trl l hl hv1
            exact ⟨i, by omega, by rw [List.getElem?_set_ne (by omega)]; exact heq⟩
      vals_false_trl := fun l hl hvff => by
        dsimp only [st'] at hvff ⊢
        by_cases h1 : l = lit.toNat ^^^ 1
        · subst h1; exact ⟨st.core.trail_end, by omega, by
            rw [List.getElem?_set_self hte_eq_len, Option.getD_some,
              show (lit.toNat ^^^ 1) ^^^ 1 = lit.toNat from litNeg_litNeg _]⟩
        · rw [List.getElem?_set_ne (Ne.symm h1)] at hvff
          by_cases h2 : l = lit.toNat
          · subst h2; rw [List.getElem?_set_self (by omega), Option.getD_some] at hvff; cases hvff
          · rw [List.getElem?_set_ne (Ne.symm h2)] at hvff
            obtain ⟨i, hi, heq⟩ := hbt.vals_false_trl l hl hvff
            exact ⟨i, by omega, by rw [List.getElem?_set_ne (by omega)]; exact heq⟩
      lvl_le_max := fun i hi => by
        dsimp only [st'] at hi ⊢
        by_cases he : i = st.core.trail_end
        · subst he; rw [List.getElem?_set_self hte_eq_len, Option.getD_some,
            List.getElem?_set_self (by omega), Option.getD_some]; exact hlv_le
        · rw [List.getElem?_set_ne (Ne.symm he),
            List.getElem?_set_ne (Ne.symm (hmiss i (by omega)))]
          exact Nat.le_trans (hbt.lvl_le_max i (by omega)) hmax
      l0_entails := fun i hi hlv0 => by
        dsimp only [st'] at hi hlv0 ⊢
        by_cases he : i = st.core.trail_end
        · subst he; rw [List.getElem?_set_self hte_eq_len, Option.getD_some] at hlv0 ⊢
          rw [List.getElem?_set_self (by omega), Option.getD_some] at hlv0
          exact hl0_ent hlv0
        · rw [List.getElem?_set_ne (Ne.symm he)] at hlv0 ⊢
          rw [List.getElem?_set_ne (Ne.symm (hmiss i (by omega)))] at hlv0
          exact hbt.l0_entails i (by omega) hlv0 }

theorem s13_bb_init {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 : FullState} (hsp : FullSparseInvW c F0 F_cur s0) (hl0 : s0.core.cur_level = 0) :
    BbTrailInv c F0 F_cur s0 s0 s0.core.trail_end 0 := by
  have hw := hsp.2.1
  exact
    { len_ok := hsp.1, s0_l0 := hl0, same_core := rfl, same_scratch := rfl,
      saved0_eq := rfl, saved0_le := Nat.le_refl _, cur_le_max := by omega,
      trl_prefix := fun _ _ => rfl, vals_prefix := fun _ _ _ => rfl,
      vals_hi := fun _ _ => rfl, lvl_prefix := fun _ _ => ⟨rfl, rfl⟩,
      trl_lits_lt := hw.trail_lits_lt, trl_vars_nodup := hw.trail_vars_nodup,
      trl_vals_ok := fun i hi => by
        have hlt := hw.trail_lits_lt i hi
        exact ⟨(hw.vals_true_iff _ hlt).mpr ⟨i, hi, rfl⟩,
          (hw.vals_false_iff _ (litNeg_lt_two_mul hlt)).mpr
            ⟨i, hi, (litNeg_litNeg _).symm⟩⟩,
      vals_dom := hw.vals_domain,
      vals_true_trl := fun l hl h1 => (hw.vals_true_iff l hl).mp h1,
      vals_false_trl := fun l hl hff => (hw.vals_false_iff l hl).mp hff,
      lvl_le_max := fun i hi => by have := hw.lvl_le i hi; omega,
      l0_entails := hw.level0_sound }

end BbS5Helpers

/-! ## 2. `full_backbone_keep_m6_s5_wp` (`fullBackboneKeepM6Spec`) -/

section BackboneKeepS5

theorem full_backbone_keep_m6_s5_wp (Γ : Env) :
    ∀ a m Q X, fullBackboneKeepM6Spec a m Q X →
      Func.wp Γ FullFidelityStep13S5VivifyBackbone.full_backbone_keep_m6_body a m Q X := by
  rintro ⟨h, cand_n, ⟨⟩⟩ m0 Q X ⟨c, F0, F_cur, s, R, rfl, hsp, hcn_le, hlt_c, hm0, hQ⟩
  have hcl := hsp.1.core_ok; have hscl := hsp.1.scratch_ok
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv_le := hcl.cur_vars_le; have hfl_len := hcl.flags_len
  have hws1_len := hscl.work_stk1_len
  unfold Func.wp FullFidelityStep13S5VivifyBackbone.full_backbone_keep_m6_body
  c0_hsteps_nogrp
  refine wp_loop_inv (ts := [i64, i64, i64])
    (fun (prio, rem, i, ()) m1 => i.toNat ≤ cand_n.toNat ∧ m1 = m0)
    (fun (_, _, i, ()) _ => cand_n.toNat - i.toNat) ?_ ?_
  · intro J1 hJ1; c0_hsteps; exact hJ1 (0#64, 0#64, 0#64, ()) m0 ⟨Nat.zero_le _, rfl⟩
  · rintro J1 ⟨prio, rem, i, ⟨⟩⟩ m1 ⟨hi_le, hm1_eq⟩ ih1
    rw [hm1_eq]
    c0_hstraight
    c0_hsplit
    · have hi_lt : i.toNat < cand_n.toNat := by c0_bound
      have hi_ws1 : i.toNat < s.scratch.work_stk1.length := by omega
      have hi1 : (i + 1#64).toNat = i.toNat + 1 := by bv_omega
      let lit := s.scratch.work_stk1[i.toNat]'hi_ws1
      have hlit_lt : lit.toNat < 2 * s.core.cur_vars := by
        have := hlt_c i.toNat hi_lt; rwa [List.getElem?_eq_getElem hi_ws1, Option.getD_some] at this
      have hlv_fl : (lit >>> 1#32).toNat < s.core.flags.length := by
        rw [s13_bb_bv32_lshr1, hfl_len]; omega
      c0_hstraight
      refine wp_join_group (ts := [i64, i64]) (fun _ m2 => m2 = m0)
        (fun _ ⟨prio', rem', ⟨⟩⟩ m2 hm2 => by
          rw [hm2]; c0_hsteps
          exact ih1 (prio', rem', i + 1#64, ()) m0 (by dsimp only; omega) ⟨by omega, rfl⟩)
        (fun Jn hJn => by
          c0_hsplit
          · c0_hsteps_nogrp
            refine wp_join_group (ts := [i32]) (fun _ mb => mb = m0)
              (fun _ ⟨_bit, ⟨⟩⟩ mb hmb => by
                rw [hmb]; c0_hsteps_nogrp
                refine wp_join_group (ts := [i64]) (fun _ mc => mc = m0)
                  (fun _ ⟨prio', ⟨⟩⟩ mc hmc => by
                    rw [hmc]; c0_hsteps
                    exact hJn (prio', rem + 1#64, ()) m0 rfl)
                  (fun Jp hJp => by
                    c0_hsplit
                    · c0_hsteps; exact hJp _ m0 rfl
                    · c0_hsteps; exact hJp _ m0 rfl))
              (fun Jb hJb => by
                c0_hsplit
                · c0_hsteps; exact hJb _ m0 rfl
                · c0_hsteps; exact hJb _ m0 rfl)
          · c0_hsteps; exact hJn (prio, rem, ()) m0 rfl)
    · clear hc ih1 J1
      c0_hsplit
      · c0_hsteps; exact hQ s.core.flags m0 hsp hm0
      c0_hsplit
      · c0_hsteps; exact hQ s.core.flags m0 hsp hm0
      c0_hsplit
      · c0_hsteps; exact hQ s.core.flags m0 hsp hm0
      c0_hsteps_nogrp
      refine wp_loop_inv (ts := [i64])
        (fun (i2, ()) m2 => ∃ fl2 : List (BitVec 32), fl2.length = c.max_vars ∧
          i2.toNat ≤ cand_n.toNat ∧
          (FullMem c { s with core := { s.core with flags := fl2 } } ⋆ R) m2)
        (fun (i2, ()) _ => cand_n.toNat - i2.toNat) ?_ ?_
      · intro J2 hJ2; c0_hsteps
        exact hJ2 (0#64, ()) m0 ⟨s.core.flags, hfl_len, Nat.zero_le _, hm0⟩
      · rintro J2 ⟨i2, ⟨⟩⟩ m2 ⟨fl2, hfl2, hi_le2, hm2⟩ ih2
        c0_hsteps_nogrp
        c0_hsplit
        · have hi_lt : i2.toNat < cand_n.toNat := by c0_bound
          have hi_ws1 : i2.toNat < s.scratch.work_stk1.length := by omega
          have hi1 : (i2 + 1#64).toNat = i2.toNat + 1 := by bv_omega
          let lit := s.scratch.work_stk1[i2.toNat]'hi_ws1
          have hlit_lt : lit.toNat < 2 * s.core.cur_vars := by
            have := hlt_c i2.toNat hi_lt
            rwa [List.getElem?_eq_getElem hi_ws1, Option.getD_some] at this
          have hlv_fl : (lit >>> 1#32).toNat < fl2.length := by rw [s13_bb_bv32_lshr1]; omega
          c0_hsteps_nogrp
          refine wp_join_group (ts := [])
            (fun _ m3 => ∃ fl3 : List (BitVec 32), fl3.length = c.max_vars ∧
              (FullMem c { s with core := { s.core with flags := fl3 } } ⋆ R) m3)
            (fun _ _ m3 ⟨fl3, hfl3, hm3⟩ => by
              c0_hsteps
              exact ih2 (i2 + 1#64, ()) m3 (by dsimp only; omega) ⟨fl3, hfl3, by omega, hm3⟩)
            (fun Jn hJn => by
              c0_hsplit
              · c0_hsteps_nogrp
                refine wp_join_group (ts := [])
                  (fun _ m3 => ∃ fl3 : List (BitVec 32), fl3.length = c.max_vars ∧
                    (FullMem c { s with core := { s.core with flags := fl3 } } ⋆ R) m3)
                  (fun _ _ m3 h => hJn () m3 h)
                  (fun Jb hJb => by
                    have hlv_fl64 : (BitVec.setWidth 64 (lit >>> 1#32)).toNat < fl2.length := by
                      have : (BitVec.setWidth 64 (lit >>> 1#32)).toNat = (lit >>> 1#32).toNat := by
                        bv_omega
                      omega
                    c0_hsplit
                    · c0_hsteps
                      refine hJb () _ ⟨fl2.set (BitVec.setWidth 64 (lit >>> 1#32)).toNat
                          (fl2[(BitVec.setWidth 64 (lit >>> 1#32)).toNat] ||| 128#32),
                        by simp [hfl2], ?_⟩
                      refine s13_bb_fullMem_symm ‹(FullMem c _ ⋆ R) _› ?_
                      dsimp only [lit]; rfl
                    · c0_hsteps
                      refine hJb () _ ⟨fl2.set (BitVec.setWidth 64 (lit >>> 1#32)).toNat
                          (fl2[(BitVec.setWidth 64 (lit >>> 1#32)).toNat] ||| 256#32),
                        by simp [hfl2], ?_⟩
                      refine s13_bb_fullMem_symm ‹(FullMem c _ ⋆ R) _› ?_
                      dsimp only [lit]; rfl)
              · c0_hsteps; exact hJn () m2 ⟨fl2, hfl2, hm2⟩)
        · c0_hsteps
          exact hQ fl2 m2 (s13_bb_sparseW_with_flags hsp hfl2) hm2

end BackboneKeepS5

/-! ## 3. `full_backbone_prop_m6_s5_wp` (`step13BackbonePropM6Spec`) -/

section BackbonePropS5

private def S13BbPropStInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s0 st : FullState) (saved0 max_lvl prop_start : Nat)
    (R : Mem 64 → Prop) (vals' : List (BitVec 8)) (lvl' rsns' trl' : List (BitVec 32))
    (te' : Nat) (c0' c1' asz' : BitVec 64) (m : Mem 64) : Prop :=
  let st' : FullState :=
    { st with
      core := { st.core with
        vals := vals', lvl := lvl', rsns := rsns', trl := trl', trail_end := te',
        confl_lit0 := c0', confl_lit1 := c1' }
      scratch := { st.scratch with ant_sz := asz' } }
  BbTrailInv c F0 F_cur s0 st' saved0 max_lvl ∧ st.core.trail_end ≤ te' ∧
  (∀ i < st.core.trail_end, trl'[i]? = st.core.trl[i]?) ∧
  (∀ i < st.core.trail_end,
    let v := (st.core.trl[i]?.getD 0#32).toNat / 2
    lvl'[v]? = st.core.lvl[v]? ∧ rsns'[v]? = st.core.rsns[v]?) ∧
  (st.core.cur_level = 0 → ∀ i, prop_start ≤ i → i < te' →
    (lvl'[(trl'[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0) ∧
  (∀ saved, saved0 ≤ saved → saved ≤ prop_start → 0 < st.core.cur_level →
    BackboneProbeSeg F_cur st saved st.core.cur_level →
    BackboneProbeSeg F_cur st' saved st.core.cur_level) ∧
  (FullMem c st' ⋆ R) m

theorem full_backbone_prop_m6_s5_wp (Γ : Env) :
    ∀ a m Q X, step13BackbonePropM6Spec a m Q X →
      Func.wp Γ FullFidelityStep13S5VivifyBackbone.full_backbone_prop_m6_body a m Q X := by
  rintro ⟨h, prop_start, stop_early, ⟨⟩⟩ m0 Q X
    ⟨c, F0, F_cur, s0, st, saved0, max_lvl, R, rfl, hsp0, hbt0, hs0_le, hps_le, hmode, hm0, hQ⟩
  have hmx := c.hmaxv; have hwc := c.hwcap; unfold dimacsBound at hmx hwc
  have hcv_le : s0.core.cur_vars ≤ c.max_vars := hsp0.1.core_ok.cur_vars_le
  have hcv_st : st.core.cur_vars = s0.core.cur_vars := by rw [hbt0.same_core]
  have hmw : WatchesInv F_cur s0.core := by
    have h := hsp0.2.1.watches; simp only [ModeWatchesInv, hsp0.2.2.2.2.2, ↓reduceIte] at h
    exact h
  have hwl_le : s0.core.wlen ≤ c.wcap := hsp0.1.core_ok.wlen_le
  have hcl_lt32 : st.core.cur_level < 2 ^ 32 := by
    rcases hmode with ⟨hc0, _⟩ | ⟨_, hcm⟩ <;> omega
  have hcl_tr : ((BitVec.ofNat 64 st.core.cur_level).truncate 32).toNat = st.core.cur_level := by
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : st.core.cur_level < 2 ^ 64), Nat.mod_eq_of_lt hcl_lt32]
  have hnlits_eq :
      ((BitVec.ofNat 64 st.core.cur_vars) <<< (BitVec.signExtend 64 1#32)).toNat =
        2 * s0.core.cur_vars := by
    rw [hcv_st,
      s13_bb_bv64_shl1_sext _ (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega),
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  unfold Func.wp FullFidelityStep13S5VivifyBackbone.full_backbone_prop_m6_body
  c0_hsteps_nogrp
  refine wp_loop_inv (ts := [i64, i64])
    (fun (tk, prop, ()) m1 =>
      ∃ vals1 lvl1 rsns1 trl1 te1 c01 c11 asz1,
        prop_start.toNat ≤ prop.toNat ∧ prop.toNat ≤ te1 ∧
        S13BbPropStInv c F0 F_cur s0 st saved0 max_lvl prop_start.toNat R
          vals1 lvl1 rsns1 trl1 te1 c01 c11 asz1 m1)
    (fun (_, prop, ()) _ => c.max_vars - prop.toNat) ?_ ?_
  · intro J1 hJ1; fvt_steps
    exact hJ1 (st.scratch.ant_sz, prop_start, ()) m0
      ⟨st.core.vals, st.core.lvl, st.core.rsns, st.core.trl, st.core.trail_end,
       st.core.confl_lit0, st.core.confl_lit1, st.scratch.ant_sz, Nat.le_refl _, hps_le,
       hbt0, Nat.le_refl _, (fun _ _ => rfl), (fun _ _ => ⟨rfl, rfl⟩),
       (fun hc0 => hmode.elim (fun h => h.2) (fun h => by omega)),
       (fun _ _ _ _ hsg => hsg), hm0⟩
  · rintro J1 ⟨tk, prop, ⟨⟩⟩ m1
      ⟨vals1, lvl1, rsns1, trl1, te1, c01, c11, asz1, hps1, hp_le, hbt1, hte_ge, htrl_pre,
       hlvl_pre, hl0_1, hseg_1, hm1⟩ ih1
    let st1 : FullState :=
      { st with
        core := { st.core with
          vals := vals1, lvl := lvl1, rsns := rsns1, trl := trl1, trail_end := te1,
          confl_lit0 := c01, confl_lit1 := c11 }
        scratch := { st.scratch with ant_sz := asz1 } }
    have hcv_st1 : st1.core.cur_vars = s0.core.cur_vars := by rw [hbt1.same_core]
    have hte1_le : te1 ≤ c.max_vars :=
      Nat.le_trans hbt1.len_ok.core_ok.trail_end_le (by rw [hcv_st1]; omega)
    c0_hsplit
    · have hp_lt : prop.toNat < te1 := by
        have h1 : prop.toNat < te1 % 2 ^ 64 := by c0_bound
        rwa [Nat.mod_eq_of_lt (by omega)] at h1
      have hp_trl : prop.toNat < st1.core.trl.length := by
        dsimp only [st1]; rw [hbt1.len_ok.core_ok.trl_len]; omega
      have hp1 : (prop + 1#64).toNat = prop.toNat + 1 := by bv_omega
      let lit := trl1[prop.toNat]'hp_trl
      let not_lit := lit ^^^ 1#32
      have hlit_get : (trl1[prop.toNat]?.getD 0#32) = lit := by
        rw [List.getElem?_eq_getElem hp_trl, Option.getD_some]
      have hlit_lt : lit.toNat < 2 * s0.core.cur_vars := by
        have := hbt1.trl_lits_lt prop.toNat hp_lt; rwa [hlit_get] at this
      have hnl_eq : not_lit.toNat = lit.toNat ^^^ 1 := s13_bb_bv32_xor1 lit
      have hnl_lt : not_lit.toNat < 2 * s0.core.cur_vars := by
        rw [hnl_eq]; exact litNeg_lt_two_mul hlit_lt
      have hwv_eq : st1.core.wvec = s0.core.wvec := by rw [hbt1.same_core]
      have hwv_len : st1.core.wvec.length = 4 * c.max_vars := hbt1.len_ok.core_ok.wvec_len
      have hnl_64 : (not_lit.setWidth 64).toNat = not_lit.toNat := by
        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
      have hnl_w0 : (not_lit.setWidth 64 <<< (1 : Nat)).toNat = 2 * not_lit.toNat := by
        rw [s13_bb_bv64_shl1_nat _ (by rw [hnl_64]; omega), hnl_64]
      have hnl_w1 : ((not_lit.setWidth 64 <<< (1 : Nat)) + 1#64).toNat =
          2 * not_lit.toNat + 1 := by
        rw [BitVec.toNat_add, hnl_w0, show (1#64).toNat = 1 from rfl,
          Nat.mod_eq_of_lt (by omega)]
      have hnl_w0_lt : (BitVec.setWidth 64 (trl1[prop.toNat]'hp_trl ^^^ 1) <<< 1).toNat <
          st1.core.wvec.length := by
        change (not_lit.setWidth 64 <<< (1 : Nat)).toNat < st1.core.wvec.length; omega
      have hnl_w1_lt : ((BitVec.setWidth 64 (trl1[prop.toNat]'hp_trl ^^^ 1) <<< 1) + 1#64).toNat <
          st1.core.wvec.length := by
        change ((not_lit.setWidth 64 <<< (1 : Nat)) + 1#64).toNat < st1.core.wvec.length; omega
      have hbd_nl := hmw.layout.bounds not_lit.toNat hnl_lt
      have hslice0 := hmw.slices not_lit.toNat hnl_lt
      let off_n := fullWatchOffCore s0.core not_lit.toNat
      let sz_n := fullWatchSizeCore s0.core not_lit.toNat
      have hend_bd : off_n + sz_n ≤ c.wcap := Nat.le_trans hbd_nl hwl_le
      have hoff_eq :
          (st1.core.wvec[(not_lit.setWidth 64 <<< (1 : Nat)).toNat]'(by omega)).toNat =
            off_n := by
        unfold off_n fullWatchOffCore
        have hg : st1.core.wvec[(not_lit.setWidth 64 <<< (1 : Nat)).toNat]'(by omega) =
            s0.core.wvec[2 * not_lit.toNat]?.getD 0#32 := by
          rw [← hwv_eq, ← hnl_w0, List.getElem?_eq_getElem (by omega), Option.getD_some]
        rw [hg]
      have hsz_eq :
          (st1.core.wvec[((not_lit.setWidth 64 <<< (1 : Nat)) + 1#64).toNat]'(by omega)).toNat =
            sz_n := by
        unfold sz_n fullWatchSizeCore
        have hg : st1.core.wvec[((not_lit.setWidth 64 <<< (1 : Nat)) + 1#64).toNat]'(by omega) =
            s0.core.wvec[2 * not_lit.toNat + 1]?.getD 0#32 := by
          rw [← hwv_eq, ← hnl_w1, List.getElem?_eq_getElem (by omega), Option.getD_some]
        rw [hg]
      have hoff_64 :
          (st1.core.wvec[(not_lit.setWidth 64 <<< (1 : Nat)).toNat]'(by omega)).setWidth 64 =
            BitVec.ofNat 64 off_n :=
        BitVec.eq_of_toNat_eq (by
          rw [BitVec.toNat_setWidth, hoff_eq, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (by omega)])
      have hsz_64 :
          (st1.core.wvec[((not_lit.setWidth 64 <<< (1 : Nat)) + 1#64).toNat]'(by
            omega)).setWidth 64 = BitVec.ofNat 64 sz_n :=
        BitVec.eq_of_toNat_eq (by
          rw [BitVec.toNat_setWidth, hsz_eq, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (by omega)])
      have hend_64 :
          ((st1.core.wvec[(not_lit.setWidth 64 <<< (1 : Nat)).toNat]'(by omega)).setWidth 64 +
           (st1.core.wvec[((not_lit.setWidth 64 <<< (1 : Nat)) + 1#64).toNat]'(by
            omega)).setWidth 64).toNat = off_n + sz_n := by
        rw [hoff_64, hsz_64, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      c0_hsteps_nogrp
      refine wp_loop_break_group (brkTs := [i64, .bool]) (lpTs := [i64])
        (fun (_q_o, confl_o, ()) m_o =>
          ∃ vals2 lvl2 rsns2 trl2 te2 c02 c12 asz2,
            prop.toNat + 1 ≤ te2 ∧
            S13BbPropStInv c F0 F_cur s0 st saved0 max_lvl prop_start.toNat R
              vals2 lvl2 rsns2 trl2 te2 c02 c12 asz2 m_o ∧
            (confl_o = true →
              c02.toNat < 2 * s0.core.cur_vars ∧ c12.toNat < 2 * s0.core.cur_vars ∧
              vals2[c02.toNat]?.getD 0#8 = 0xFF#8 ∧ vals2[c12.toNat]?.getD 0#8 = 0xFF#8 ∧
              (cnfOfClauses F_cur).EntailsClause (cnfClause [c02.toNat, c12.toNat]) ∧
              ∃ idx0, prop_start.toNat ≤ idx0 ∧ idx0 < te2 ∧
                (trl2[idx0]?.getD 0#32).toNat = c02.toNat ^^^ 1))
        (fun rem (q, ()) m2 =>
          ∃ vals2 lvl2 rsns2 trl2 te2 c02 c12 asz2,
            off_n ≤ q.toNat ∧ q.toNat ≤ off_n + sz_n ∧ rem = off_n + sz_n - q.toNat ∧
            WatchSliceOk F_cur s0.core not_lit.toNat q.toNat (off_n + sz_n - q.toNat) ∧
            te1 ≤ te2 ∧ (∀ i < te1, trl2[i]? = trl1[i]?) ∧
            S13BbPropStInv c F0 F_cur s0 st saved0 max_lvl prop_start.toNat R
              vals2 lvl2 rsns2 trl2 te2 c02 c12 asz2 m2) ?_ ?_ ?_
      · rintro _ ⟨_q_o, confl_o, ⟨⟩⟩ m_o
          ⟨vals2, lvl2, rsns2, trl2, te2, c02, c12, asz2, hp_le2,
           ⟨hbt2, hte2, htp2, hlp2, hl0_2, hsg2, hm_o⟩, hcf2⟩
        fvt_to_group
        refine wp_join_group (ts := [i64]) (fun _ m_t => m_t = m_o)
          (fun _ ⟨tk_n, ⟨⟩⟩ m_t heq => by
            subst heq; c0_hsplit
            · c0_hsteps
              exact hQ false vals2 lvl2 rsns2 trl2 te2 c02 c12 tk_n _
                (s13_bb_with_ant_sz hbt2 tk_n) hte2 htp2 hlp2
                (fun sv hs1 hs2 hc' hsg => s13_bb_probeSeg_with_confl_asz
                  (hsg2 sv hs1 hs2 hc' hsg) c02 c12 tk_n)
                (fun _ => hcf2 (by revert hc; cases confl_o <;> decide)) (by assumption)
            · c0_hsteps
              exact ih1 (tk_n, prop + 1#64, ()) m_t (by dsimp only; omega)
                ⟨vals2, lvl2, rsns2, trl2, te2, c02, c12, asz2, by omega, by omega,
                 hbt2, hte2, htp2, hlp2, hl0_2, hsg2, hm_o⟩)
          (fun Jt hJt => by c0_hsteps <;> exact hJt _ _ rfl)
      · rintro B L rem ⟨q, ⟨⟩⟩ m2 hB hL
          ⟨vals2, lvl2, rsns2, trl2, te2, c02, c12, asz2, hq_ge, hq_le, hrem, hslice_q,
           hte12, htrl12, hinv2⟩
        subst hrem
        rcases hinv2 with ⟨hbt2, hte2, htp2, hlp2, hl0_2, hsg2, hm2⟩
        let st2 : FullState :=
          { st with
            core := { st.core with
              vals := vals2, lvl := lvl2, rsns := rsns2, trl := trl2, trail_end := te2,
              confl_lit0 := c02, confl_lit1 := c12 }
            scratch := { st.scratch with ant_sz := asz2 } }
        have hcv_st2 : st2.core.cur_vars = s0.core.cur_vars := by rw [hbt2.same_core]
        have hte2_le : te2 ≤ c.max_vars :=
          Nat.le_trans hbt2.len_ok.core_ok.trail_end_le (by rw [hcv_st2]; omega)
        c0_hsplit
        · have hq_lt : q.toNat < off_n + sz_n := by
            have hwvl : st.core.wvec.length = 4 * c.max_vars := by
              have hwv : st.core.wvec = st1.core.wvec := by simp [st1]
              rw [hwv, hwv_len]
            have hnl_v : trl1[prop.toNat].toNat ^^^ 1 = not_lit.toNat := hnl_eq.symm
            have h0_mod : (2 * not_lit.toNat) % 2 ^ 64 = 2 * not_lit.toNat :=
              Nat.mod_eq_of_lt (by omega)
            have h1_mod : (2 * not_lit.toNat + 1) % 2 ^ 64 = 2 * not_lit.toNat + 1 :=
              Nat.mod_eq_of_lt (by omega)
            have h0 : st.core.wvec[2 * (trl1[prop.toNat].toNat ^^^ 1) % 2 ^ 64].toNat = off_n := by
              have hwv : st.core.wvec = st1.core.wvec := by simp [st1]
              have helem : st.core.wvec[2 * (trl1[prop.toNat].toNat ^^^ 1) % 2 ^ 64] =
                  st1.core.wvec[(not_lit.setWidth 64 <<< (1 : Nat)).toNat] := by
                rw [← Option.some_inj,
                  ← List.getElem?_eq_getElem (by rw [hwv, hwv_len]; omega),
                  ← List.getElem?_eq_getElem (by rw [hwv_len, hnl_w0]; omega), hwv]
                simp only [hnl_v, h0_mod, hnl_w0]
              rw [helem, hoff_eq]
            have h1 :
                st.core.wvec[(2 * (trl1[prop.toNat].toNat ^^^ 1) + 1) % 2 ^ 64].toNat = sz_n := by
              have hwv : st.core.wvec = st1.core.wvec := by simp [st1]
              have helem : st.core.wvec[(2 * (trl1[prop.toNat].toNat ^^^ 1) + 1) % 2 ^ 64] =
                  st1.core.wvec[((not_lit.setWidth 64 <<< (1 : Nat)) + 1#64).toNat] := by
                rw [← Option.some_inj,
                  ← List.getElem?_eq_getElem (by rw [hwv, hwv_len]; omega),
                  ← List.getElem?_eq_getElem (by rw [hwv_len, hnl_w1]; omega), hwv]
                simp only [hnl_v, h1_mod, hnl_w1]
              rw [helem, hsz_eq]
            have hc' : q.toNat <
                (st.core.wvec[2 * (trl1[prop.toNat].toNat ^^^ 1) % 2 ^ 64].toNat +
                 st.core.wvec[(2 * (trl1[prop.toNat].toNat ^^^ 1) + 1) % 2 ^ 64].toNat) %
                  2 ^ 64 := by
              simpa [hnl_v, (by omega : (2 * not_lit.toNat + 1) % 2 ^ 64 < st.core.wvec.length)]
                using hc
            rw [h0, h1] at hc'
            omega
          have hq_ws : q.toNat < st2.core.wstk.length := by
            have : st2.core.wstk.length = c.wcap := hbt2.len_ok.core_ok.wstk_len_arr; omega
          let qw := st2.core.wstk[q.toNat]'hq_ws
          have hqw_s0 : s0.core.wstk[q.toNat]? = some qw := by
            have hws2 : st2.core.wstk = s0.core.wstk := by rw [hbt2.same_core]
            rw [← hws2, List.getElem?_eq_getElem hq_ws]
          c0_hsplit
          · have hlg_f : (qw &&& 0x80000000#32) = 0#32 := by c0_bound
            obtain ⟨hrem2, _, _, _, _, hslice_2⟩ :=
              FullTransHelpers.watchSlice_inv_large hslice_q (by omega) hqw_s0 hlg_f
            c0_hsplit
            · c0_hsteps
              exact hB (q, false, ()) m2
                ⟨vals2, lvl2, rsns2, trl2, te2, c02, c12, asz2, by omega,
                 ⟨hbt2, hte2, htp2, hlp2, hl0_2, hsg2, hm2⟩, fun h => by cases h⟩
            · have hq2 : (q + 2#64).toNat = q.toNat + 2 := by bv_omega
              c0_hsteps
              exact hL (off_n + sz_n - (q.toNat + 2)) (q + 2#64, ()) m2 (by omega)
                ⟨vals2, lvl2, rsns2, trl2, te2, c02, c12, asz2, by omega, by omega, by rw [hq2],
                 by simpa [hq2, show off_n + sz_n - (q.toNat + 2) =
                   off_n + sz_n - q.toNat - 2 by omega] using hslice_2,
                 hte12, htrl12, hbt2, hte2, htp2, hlp2, hl0_2, hsg2, hm2⟩
          · have hbf : (qw &&& 0x80000000#32) ≠ 0#32 := by c0_bound
            obtain ⟨_, hot_lt, hent_bin, hslice_1⟩ :=
              FullTransHelpers.watchSlice_inv_bin hslice_q (by omega) hqw_s0 hbf
            have hq1 : (q + 1#64).toNat = q.toNat + 1 := by bv_omega
            let ot := qw &&& 0x7FFFFFFF#32
            have hot_lt' : ot.toNat < 2 * s0.core.cur_vars := hot_lt
            have hot_v : ot.toNat < vals2.length := by
              have : vals2.length = 2 * c.max_vars := hbt2.len_ok.core_ok.vals_len; omega
            have hot_not_lt : ot.toNat ^^^ 1 < 2 * s0.core.cur_vars := litNeg_lt_two_mul hot_lt'
            have hot_not_v : (ot ^^^ 1#32).toNat < (vals2.set ot.toNat 1#8).length := by
              rw [List.length_set, s13_bb_bv32_xor1]
              have : vals2.length = 2 * c.max_vars := hbt2.len_ok.core_ok.vals_len; omega
            c0_hsteps_nogrp
            refine wp_join_group (ts := [.bool])
              (fun _ m3 => ∃ vals3 lvl3 rsns3 trl3 te3 c03 c13 asz3,
                te1 ≤ te3 ∧ (∀ i < te1, trl3[i]? = trl1[i]?) ∧
                S13BbPropStInv c F0 F_cur s0 st saved0 max_lvl prop_start.toNat R
                  vals3 lvl3 rsns3 trl3 te3 c03 c13 asz3 m3)
              (fun _ ⟨_, ⟨⟩⟩ m3 ⟨vals3, lvl3, rsns3, trl3, te3, c03, c13, asz3,
                  hte13, htrl13, hinv3⟩ => by
                c0_hsteps
                exact hL (off_n + sz_n - (q.toNat + 1)) (q + 1#64, ()) m3 (by omega)
                  ⟨vals3, lvl3, rsns3, trl3, te3, c03, c13, asz3, by omega, by omega,
                   by rw [hq1], by simpa [hq1, show off_n + sz_n - (q.toNat + 1) =
                     off_n + sz_n - q.toNat - 1 by omega] using hslice_1,
                   hte13, htrl13, hinv3⟩)
              (fun Jc hJc => by
                have hot_dom := hbt2.vals_dom ot.toNat hot_lt'
                rw [List.getElem?_eq_getElem hot_v, Option.getD_some] at hot_dom
                c0_hsplit
                · c0_hsplit
                  · have hot_ff : vals2[ot.toNat]?.getD 0#8 = 0xFF#8 := by
                      rw [List.getElem?_eq_getElem hot_v, Option.getD_some]
                      exact (s13_bb_bv8_dom_slt0 hot_dom).mp hc
                    have hnl_ff : vals2[not_lit.toNat]?.getD 0#8 = 0xFF#8 := by
                      have hv := (hbt2.trl_vals_ok prop.toNat (by dsimp only [st2]; omega)).2
                      rw [htrl12 prop.toNat hp_lt, hlit_get] at hv; rwa [hnl_eq]
                    have hnl64 : (not_lit.setWidth 64).toNat = not_lit.toNat := by bv_omega
                    have hot64 : (ot.setWidth 64).toNat = ot.toNat := by bv_omega
                    c0_hsteps
                    refine hB (q + 1#64, true, ()) _
                      ⟨vals2, lvl2, rsns2, trl2, te2, not_lit.setWidth 64, ot.setWidth 64, asz2,
                       by omega, ⟨s13_bb_with_confl_asz hbt2 (not_lit.setWidth 64)
                         (ot.setWidth 64) asz2, hte2, htp2, hlp2, hl0_2,
                         fun sv hs1 hs2 hc' hsg => s13_bb_probeSeg_with_confl_asz
                           (hsg2 sv hs1 hs2 hc' hsg) _ _ _, by assumption⟩,
                       fun _ => ⟨by rw [hnl64]; exact hnl_lt, by rw [hot64]; exact hot_lt',
                         by rw [hnl64]; exact hnl_ff, by rw [hot64]; exact hot_ff,
                         by rw [hnl64, hot64]; exact hent_bin, prop.toNat, hps1, by omega,
                         by rw [htrl12 prop.toNat hp_lt, hlit_get, hnl64, hnl_eq,
                              s13_bb_xor1_xor1]⟩⟩
                  · refine wp_unroll_group fun Jn hJn => ?_
                    c0_hsplit
                    · have hot_z : vals2[ot.toNat]?.getD 0#8 = 0#8 := by
                        rw [List.getElem?_eq_getElem hot_v, Option.getD_some]
                        exact (s13_bb_bv8_sext32_eq0 _).mp hc
                      c0_hsplit
                      · have hte2_lt : te2 < c.max_vars := by
                          have h1 : te2 % 2 ^ 64 < c.max_vars % 2 ^ 64 := by c0_bound
                          rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h1
                        have hte2_trl : te2 < trl2.length := by
                          have : trl2.length = c.max_vars := hbt2.len_ok.core_ok.trl_len; omega
                        have hte2_bv : (BitVec.ofNat 64 te2).toNat = te2 := by
                          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
                        have hot64 : (ot.setWidth 64).toNat = ot.toNat :=
                          FullTransHelpers.ft_bv32_setWidth64 ot
                        have hotn64 : ((ot ^^^ 1).setWidth 64).toNat = ot.toNat ^^^ 1 := by
                          rw [FullTransHelpers.ft_bv32_setWidth64]; exact s13_bb_bv32_xor1 ot
                        have hotr64 : ((ot >>> 1).setWidth 64).toNat = ot.toNat / 2 := by
                          rw [FullTransHelpers.ft_bv32_setWidth64]
                          simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
                        have hot_v2 : (ot >>> 1).toNat < lvl2.length := by
                          have : lvl2.length = c.max_vars := hbt2.len_ok.core_ok.lvl_len
                          simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; omega
                        have hot_r2 : (ot >>> 1).toNat < rsns2.length := by
                          have : rsns2.length = c.max_vars := hbt2.len_ok.core_ok.rsns_len
                          simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; omega
                        have hte2_add : (BitVec.ofNat 64 te2 + 1).toNat = te2 + 1 := by
                          rw [BitVec.toNat_add, hte2_bv, show (1 : BitVec 64).toNat = 1 from rfl,
                            Nat.mod_eq_of_lt (by omega)]
                        have hmiss2 := s13_bb_var_unassigned hbt2 hot_lt' hot_z
                        let rsn_b := (not_lit &&& 0x7FFFFFFF#32) ||| 0x80000000#32
                        have hl0_ent :
                            ((BitVec.ofNat 64 st.core.cur_level).truncate 32).toNat = 0 →
                            (cnfOfClauses F_cur).EntailsClause (cnfClause [ot.toNat]) := by
                          intro hc0'; rw [hcl_tr] at hc0'
                          have hlv_p : (lvl2[(trl2[prop.toNat]?.getD 0#32).toNat / 2]?.getD
                              0#32).toNat = 0 := hl0_2 hc0' prop.toNat hps1 (by omega)
                          have hlit_ent :=
                            hbt2.l0_entails prop.toNat (by dsimp only [st2]; omega) hlv_p
                          rw [htrl12 prop.toNat hp_lt, hlit_get] at hlit_ent
                          exact backbone_resolve_l0 (s13_bb_entails_comm2 hent_bin)
                            (by rw [hnl_eq, s13_bb_xor1_xor1]; exact hlit_ent)
                        have hbt3 := s13_bb_push hbt2 (Nat.le_refl _) (lit := ot)
                          (rsn := rsn_b)
                          (lv_bv := (BitVec.ofNat 64 st.core.cur_level).truncate 32)
                          (cl' := st.core.cur_level) hot_lt' hot_z hte2_lt
                          (by rw [hcl_tr]; exact hbt2.cur_le_max) hbt2.cur_le_max hl0_ent
                        c0_hsteps
                        refine hJc (false, ()) _ ⟨_, _, _, _, te2 + 1, c02, c12, asz2, by omega,
                          (fun i hi => by
                            rw [List.getElem?_set_ne (by dsimp only [st2]; omega)]
                            exact htrl12 i hi),
                          hbt3, by omega,
                          (fun i hi => by
                            rw [List.getElem?_set_ne (by dsimp only [st2]; omega)]
                            exact htp2 i hi),
                          (fun i hi => by
                            have hne_v : (st.core.trl[i]?.getD 0#32).toNat / 2 ≠ ot.toNat / 2 := by
                              rw [← htp2 i hi]; exact hmiss2 i (by dsimp only [st2]; omega)
                            dsimp only
                            rw [List.getElem?_set_ne hne_v.symm, List.getElem?_set_ne hne_v.symm]
                            exact hlp2 i hi),
                          (fun hc0' i hi1 hi2 => by
                            by_cases he : i = te2
                            · subst he
                              rw [List.getElem?_set_self hte2_trl, Option.getD_some,
                                List.getElem?_set_self (by
                                  rw [hbt2.len_ok.core_ok.lvl_len]; omega), Option.getD_some,
                                hcl_tr, hc0']
                            · rw [List.getElem?_set_ne (Ne.symm he),
                                List.getElem?_set_ne (Ne.symm (hmiss2 i
                                  (by dsimp only [st2]; omega)))]
                              exact hl0_2 hc0' i hi1 (by omega)),
                          (fun sv hs1 hs2 hc' hsg =>
                            s13_bb_probeSeg_push hbt2 (hsg2 sv hs1 hs2 hc' hsg) hot_lt' hot_z
                              hte2_lt hcl_tr hnl_lt (s13_bb_entails_comm2 hent_bin)
                              (by omega : sv ≤ prop.toNat)
                              (by dsimp only [st2]; omega : prop.toNat < st2.core.trail_end)
                              (by dsimp only [st2]; rw [htrl12 prop.toNat hp_lt, hlit_get,
                                hnl_eq, s13_bb_xor1_xor1])), ?_⟩
                        refine s13_bb_fullMem_eq ?_ (by assumption)
                        dsimp only [st2, ot, qw, rsn_b, not_lit]
                        rw [FullTransHelpers.ft_bv32_setWidth64,
                          FullTransHelpers.ft_bv32_setWidth64,
                          FullTransHelpers.ft_bv32_setWidth64, hte2_bv, hte2_add]
                        simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
                        rw [show ((st.core.wstk[q.toNat]'hq_ws &&& 2147483647) ^^^ 1).toNat =
                          (st.core.wstk[q.toNat]'hq_ws &&& 2147483647).toNat ^^^ 1 from
                          s13_bb_bv32_xor1 _]; rfl
                      · c0_hsteps
                        exact hJc (false, ()) m2 ⟨vals2, lvl2, rsns2, trl2, te2, c02, c12, asz2,
                          hte12, htrl12, hbt2, hte2, htp2, hlp2, hl0_2, hsg2, hm2⟩
                    · c0_hsteps
                      exact hJc (false, ()) m2 ⟨vals2, lvl2, rsns2, trl2, te2, c02, c12, asz2,
                        hte12, htrl12, hbt2, hte2, htp2, hlp2, hl0_2, hsg2, hm2⟩
                · c0_hsteps
                  exact hJc (false, ()) m2 ⟨vals2, lvl2, rsns2, trl2, te2, c02, c12, asz2,
                    hte12, htrl12, hbt2, hte2, htp2, hlp2, hl0_2, hsg2, hm2⟩)
        · c0_hsteps
          exact hB (q, false, ()) m2
            ⟨vals2, lvl2, rsns2, trl2, te2, c02, c12, asz2, by omega,
             ⟨hbt2, hte2, htp2, hlp2, hl0_2, hsg2, hm2⟩, fun h => by cases h⟩
      · intro B L _ hL; c0_hsteps
        have hq0 : ((st.core.wvec[((trl1[prop.toNat]'hp_trl ^^^ 1).setWidth 64 <<<
            (1 : Nat)).toNat]'hnl_w0_lt).setWidth 64).toNat = off_n := by
          change ((st1.core.wvec[(not_lit.setWidth 64 <<< (1 : Nat)).toNat]'
            hnl_w0_lt).setWidth 64).toNat = off_n
          rw [hoff_64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        exact hL sz_n (_, ()) m1
          ⟨vals1, lvl1, rsns1, trl1, te1, c01, c11, asz1,
           by dsimp only; simpa only [hq0] using (Nat.le_refl off_n),
           by dsimp only; simpa only [hq0] using (Nat.le_add_right off_n sz_n),
           by dsimp only; simp only [hq0, Nat.add_sub_cancel_left],
           by dsimp only; simpa only [hq0, Nat.add_sub_cancel_left] using hslice0,
           Nat.le_refl _, (fun _ _ => rfl), hbt1, hte_ge, htrl_pre, hlvl_pre, hl0_1, hseg_1,
           hm1⟩
    · fvt_steps
      exact hQ true vals1 lvl1 rsns1 trl1 te1 c01 c11 tk _ (s13_bb_with_ant_sz hbt1 tk)
        hte_ge htrl_pre hlvl_pre (fun sv hs1 hs2 hc hsg => s13_bb_probeSeg_with_confl_asz
          (hseg_1 sv hs1 hs2 hc hsg) c01 c11 tk) (fun h => by cases h) (by assumption)

end BackbonePropS5

/-! ## 4. `full_backbone_analyze_m6_s5_wp` (`step13BackboneAnalyzeM6Spec`) -/

section BackboneAnalyzeS5

theorem full_backbone_analyze_m6_s5_wp (Γ : Env) :
    ∀ a m Q X, step13BackboneAnalyzeM6Spec a m Q X →
      Func.wp Γ FullFidelityStep13S5VivifyBackbone.full_backbone_analyze_m6_body a m Q X := by
  rintro ⟨h, c0, c1, saved, ⟨⟩⟩ m0 Q X
    ⟨c, F0, F_cur, s0, st, saved0, max_lvl, R, rfl, hsp0, hbt, hcl_pos, hres_eq, hs0_sav,
     hrsn_sav, hseg, hc0_lt, hc1_lt, hc0_ff, hc1_ff, hent_c,
     ⟨idx0, hidx0_ge, hidx0_lt, hidx0_eq⟩, hm0, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcl := hbt.len_ok.core_ok
  have hcv_st : st.core.cur_vars = s0.core.cur_vars := by rw [hbt.same_core]
  have hcv_le : s0.core.cur_vars ≤ c.max_vars := hcv_st ▸ hcl.cur_vars_le
  have hte_le : st.core.trail_end ≤ c.max_vars := Nat.le_trans hcl.trail_end_le (by omega)
  have hs0_le : saved0 ≤ st.core.trail_end := Nat.le_trans hs0_sav (Nat.le_of_lt hseg.1)
  have hs0_64 : saved0 < 2 ^ 64 := by omega
  let saved_b0 := BitVec.ofNat 64 saved0
  have hsaved_nat : saved_b0.toNat = saved0 := by
    dsimp only [saved_b0]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hs0_64]
  have hmrk0 : FullMrkZero c st := by
    have hm_eq : st.core.mrk = s0.core.mrk := by rw [hbt.same_core]
    exact fun v hv => by rw [hm_eq]; exact hsp0.2.2.1.1 v hv
  have hc0v : (c0 >>> 1#32).toNat < c.max_vars := by rw [s13_bb_bv32_lshr1]; omega
  have hc1v : (c1 >>> 1#32).toNat < c.max_vars := by rw [s13_bb_bv32_lshr1]; omega
  have hc0_lvl : (c0 >>> 1#32).toNat < st.core.lvl.length := by rw [hcl.lvl_len]; omega
  have hc1_lvl : (c1 >>> 1#32).toNat < st.core.lvl.length := by rw [hcl.lvl_len]; omega
  have hc0_64_lvl : (BitVec.setWidth 64 (c0 >>> 1#32)).toNat < st.core.lvl.length := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]; exact hc0_lvl
  have hc1_64_lvl : (BitVec.setWidth 64 (c1 >>> 1#32)).toNat < st.core.lvl.length := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]; exact hc1_lvl
  have hc0_mrk : (c0 >>> 1#32).toNat < st.core.mrk.length := by rw [hcl.mrk_len]; omega
  have hc1_mrk : (c1 >>> 1#32).toNat < st.core.mrk.length := by rw [hcl.mrk_len]; omega
  obtain ⟨idx1, hidx1_lt, hidx1_eq⟩ := hbt.vals_false_trl c1.toNat hc1_lt hc1_ff
  unfold Func.wp FullFidelityStep13S5VivifyBackbone.full_backbone_analyze_m6_body
  fvt_step; fvt_step; fvt_step; fvt_step; fvt_step; fvt_step; fvt_step; fvt_step
  · have hlv1_0 : (st.core.lvl[c1.toNat / 2]?.getD 0#32).toNat = 0 := by
      rw [List.getElem?_eq_getElem (by rw [hcl.lvl_len]; omega), Option.getD_some]
      have h1 : st.core.lvl[(c1 >>> 1#32).toNat]'hc1_lvl = 0#32 := by c0_bound
      have heq : st.core.lvl[c1.toNat / 2]'(by rw [hcl.lvl_len]; omega) =
          st.core.lvl[(c1 >>> 1#32).toNat]'hc1_lvl := by congr 1
      rw [heq, h1]; rfl
    have hc1_ent : (cnfOfClauses F_cur).EntailsClause (cnfClause [c1.toNat ^^^ 1]) := by
      have h := hbt.l0_entails idx1 hidx1_lt (by rw [hidx1_eq, fullInv_var_xor1]; exact hlv1_0)
      rwa [hidx1_eq] at h
    fvt_steps
    exact hQ (c0 ^^^ 1#32) st.core.mrk m0 hcl.mrk_len hmrk0 (fun _ =>
      ⟨by rw [s13_bb_bv32_xor1]; exact litNeg_lt_two_mul hc0_lt,
       by rw [s13_bb_bv32_xor1, s13_bb_xor1_xor1]; exact backbone_resolve_l0 hent_c hc1_ent⟩) hm0
  · have hlv1_nz : (st.core.lvl[c1.toNat / 2]?.getD 0#32).toNat ≠ 0 := by
      have h1 : st.core.lvl[(c1 >>> 1#32).toNat]'hc1_lvl ≠ 0#32 := by c0_bound
      rw [List.getElem?_eq_getElem (by rw [hcl.lvl_len]; omega), Option.getD_some]
      have heq : st.core.lvl[c1.toNat / 2]'(by rw [hcl.lvl_len]; omega) =
          st.core.lvl[(c1 >>> 1#32).toNat]'hc1_lvl := by congr 1
      rw [heq]; intro h0; apply h1; exact BitVec.eq_of_toNat_eq h0
    have hidx1_ge : saved0 ≤ idx1 :=
      Classical.byContradiction fun hlt => by
        have hlt' : idx1 < saved0 := Nat.lt_of_not_le hlt
        have htp := hbt.trl_prefix idx1 hlt'
        have hlp := (hbt.lvl_prefix idx1 hlt').1
        have h1 := hsp0.2.1.lvl_le idx1 (hbt.saved0_eq ▸ hlt')
        rw [← hlp] at h1
        rw [← htp, hbt.s0_l0] at h1
        rw [hidx1_eq, fullInv_var_xor1] at h1
        exact hlv1_nz (by omega)
    c0_hsplit
    · have hlv0_0 : (st.core.lvl[c0.toNat / 2]?.getD 0#32).toNat = 0 := by
        rw [List.getElem?_eq_getElem (by rw [hcl.lvl_len]; omega), Option.getD_some]
        have h1 : st.core.lvl[(c0 >>> 1#32).toNat]'hc0_lvl = 0#32 := by c0_bound
        have heq : st.core.lvl[c0.toNat / 2]'(by rw [hcl.lvl_len]; omega) =
            st.core.lvl[(c0 >>> 1#32).toNat]'hc0_lvl := by congr 1
        rw [heq, h1]; rfl
      have hc0_ent : (cnfOfClauses F_cur).EntailsClause (cnfClause [c0.toNat ^^^ 1]) := by
        have h := hbt.l0_entails idx0 hidx0_lt (by rw [hidx0_eq, fullInv_var_xor1]; exact hlv0_0)
        rwa [hidx0_eq] at h
      fvt_steps
      exact hQ (c1 ^^^ 1#32) st.core.mrk m0 hcl.mrk_len hmrk0 (fun _ =>
        ⟨by rw [s13_bb_bv32_xor1]; exact litNeg_lt_two_mul hc1_lt,
         by rw [s13_bb_bv32_xor1, s13_bb_xor1_xor1]
            exact backbone_resolve_l0 (s13_bb_entails_comm2 hent_c) hc0_ent⟩) hm0
    · c0_hsplit
      · have hce : c0 = c1 := by c0_bound
        subst hce; fvt_steps
        exact hQ (c0 ^^^ 1#32) st.core.mrk m0 hcl.mrk_len hmrk0 (fun _ =>
          ⟨by rw [s13_bb_bv32_xor1]; exact litNeg_lt_two_mul hc0_lt,
           by rw [s13_bb_bv32_xor1, s13_bb_xor1_xor1]; exact backbone_collapse_eq hent_c⟩) hm0
      · have hc_ne : c0 ≠ c1 := by c0_bound
        have hidx_ne : idx0 ≠ idx1 := fun he => by
          subst he
          have h1 := congrArg (· ^^^ 1) (hidx0_eq.symm.trans hidx1_eq)
          rw [s13_bb_xor1_xor1, s13_bb_xor1_xor1] at h1
          exact hc_ne (BitVec.eq_of_toNat_eq h1)
        have hv_ne : c0.toNat / 2 ≠ c1.toNat / 2 := fun he =>
          hidx_ne (hbt.trl_vars_nodup idx0 idx1 hidx0_lt hidx1_lt
            (by rw [hidx0_eq, hidx1_eq, fullInv_var_xor1, fullInv_var_xor1]; exact he))
        have hc0_mrk64 : (BitVec.setWidth 64 (c0 >>> 1)).toNat < st.core.mrk.length := by
          rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := BitVec.isLt (c0 >>> 1); omega)]
          exact hc0_mrk
        have hc1_mrk64 : (BitVec.setWidth 64 (c1 >>> 1)).toNat <
            (st.core.mrk.set (BitVec.setWidth 64 (c0 >>> 1)).toNat 1#8).length := by
          rw [List.length_set, BitVec.toNat_setWidth,
            Nat.mod_eq_of_lt (by have := BitVec.isLt (c1 >>> 1); omega)]
          exact hc1_mrk
        c0_hstraight
        refine wp_join_group (ts := [i64, i32])
          (fun (_, res, ()) m_cl => ∃ mrk_c : List (BitVec 8), mrk_c.length = c.max_vars ∧
            (∀ v < c.max_vars, mrk_c[v]?.getD 0#8 ≠ 0#8 →
              ∃ i, saved0 ≤ i ∧ i < st.core.trail_end ∧
                (st.core.trl[i]?.getD 0#32).toNat / 2 = v) ∧
            (res ≠ 0xFFFFFFFF#32 → res.toNat < 2 * s0.core.cur_vars ∧
              (cnfOfClauses F_cur).EntailsClause (cnfClause [res.toNat ^^^ 1])) ∧
            (FullMem c { st with core := { st.core with mrk := mrk_c } } ⋆ R) m_cl)
          (fun _ ⟨_, res, ⟨⟩⟩ m_cl ⟨mrk_c, hmc_len, hmc_dom, hres_ok, hm_cl⟩ => by
            have hc0_mc : (BitVec.setWidth 64 (c0 >>> 1)).toNat < mrk_c.length := by
              rw [hmc_len, BitVec.toNat_setWidth,
                Nat.mod_eq_of_lt (by have := BitVec.isLt (c0 >>> 1); omega)]
              exact hc0v
            let mrk_c1 := mrk_c.set (BitVec.setWidth 64 (c0 >>> 1)).toNat 0#8
            have hc1_mc : (BitVec.setWidth 64 (c1 >>> 1)).toNat < mrk_c1.length := by
              dsimp only [mrk_c1]
              rw [List.length_set, hmc_len, BitVec.toNat_setWidth,
                Nat.mod_eq_of_lt (by have := BitVec.isLt (c1 >>> 1); omega)]
              exact hc1v
            let mrk_c2 := mrk_c1.set (BitVec.setWidth 64 (c1 >>> 1)).toNat 0#8
            have hmc2_len : mrk_c2.length = c.max_vars := by simp [mrk_c2, mrk_c1, hmc_len]
            have hmc2_dom : ∀ v < c.max_vars, mrk_c2[v]?.getD 0#8 ≠ 0#8 →
                ∃ i, saved0 ≤ i ∧ i < st.core.trail_end ∧
                  (st.core.trl[i]?.getD 0#32).toNat / 2 = v := by
              intro v hv hnz
              dsimp only [mrk_c2, mrk_c1] at hnz
              by_cases h1 : v = (BitVec.setWidth 64 (c1 >>> 1)).toNat
              · subst h1; rw [List.getElem?_set_self hc1_mc, Option.getD_some] at hnz
                exact absurd rfl hnz
              · rw [List.getElem?_set_ne (Ne.symm h1)] at hnz
                by_cases h0 : v = (BitVec.setWidth 64 (c0 >>> 1)).toNat
                · subst h0; rw [List.getElem?_set_self hc0_mc, Option.getD_some] at hnz
                  exact absurd rfl hnz
                · rw [List.getElem?_set_ne (Ne.symm h0)] at hnz
                  exact hmc_dom v hv hnz
            c0_hsteps_nogrp
            refine wp_loop_inv (ts := [i64])
              (fun (k, ()) mk => ∃ mrk_k : List (BitVec 8), mrk_k.length = c.max_vars ∧
                saved0 ≤ k.toNat ∧ k.toNat ≤ st.core.trail_end ∧
                (∀ v < c.max_vars, mrk_k[v]?.getD 0#8 ≠ 0#8 →
                  ∃ i, k.toNat ≤ i ∧ i < st.core.trail_end ∧
                    (st.core.trl[i]?.getD 0#32).toNat / 2 = v) ∧
                (FullMem c { st with core := { st.core with mrk := mrk_k } } ⋆ R) mk)
              (fun (k, ()) _ => st.core.trail_end - k.toNat) ?_ ?_
            · intro Jk hJk; fvt_steps
              have hres_nat : st.scratch.res_sz.toNat = saved0 := by
                rw [hres_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hs0_64]
              exact hJk (st.scratch.res_sz, ()) _
                ⟨mrk_c2, hmc2_len, by rw [hres_nat]; exact Nat.le_refl _, by rw [hres_nat]; omega,
                 by simpa only [hres_nat] using hmc2_dom, by assumption⟩
            · rintro Jk ⟨k, ⟨⟩⟩ mk ⟨mrk_k, hmk_len, hk_ge, hk_le, hmk_dom, hmk⟩ ihk
              fvt_step; fvt_step; fvt_step
              · have hk_lt : k.toNat < st.core.trail_end := by
                  have h1 : k.toNat < st.core.trail_end % 2 ^ 64 := by c0_bound
                  rwa [Nat.mod_eq_of_lt (by omega)] at h1
                have hk1 : (k + 1#64).toNat = k.toNat + 1 := by bv_omega
                have hk_trl : k.toNat < st.core.trl.length := by rw [hcl.trl_len]; omega
                let zk := st.core.trl[k.toNat]'hk_trl
                have hzk_lt : zk.toNat < 2 * s0.core.cur_vars := by
                  have := hbt.trl_lits_lt k.toNat hk_lt
                  rwa [List.getElem?_eq_getElem hk_trl, Option.getD_some] at this
                have hzk_mrk : (zk >>> 1#32).toNat < mrk_k.length := by
                  rw [s13_bb_bv32_lshr1, hmk_len]; omega
                fvt_steps
                refine ihk (k + 1#64, ()) _ (by dsimp only; omega)
                  ⟨mrk_k.set (zk >>> 1#32).toNat 0#8, by simp [hmk_len], by omega, by omega,
                   fun v hv hnz => ?_, hm⟩
                have hv_ne_k : v ≠ (zk >>> 1#32).toNat := fun he => by
                  subst he; rw [List.getElem?_set_self hzk_mrk, Option.getD_some] at hnz
                  exact hnz rfl
                rw [List.getElem?_set_ne hv_ne_k.symm] at hnz
                obtain ⟨i, hi1, hi2, hieq⟩ := hmk_dom v hv hnz
                have hi_ne_k : i ≠ k.toNat := fun he => by
                  subst he; apply hv_ne_k
                  rw [s13_bb_bv32_lshr1, ← hieq, List.getElem?_eq_getElem hk_trl, Option.getD_some]
                exact ⟨i, by omega, hi2, hieq⟩
              · have hk_eq : k.toNat = st.core.trail_end := by
                  have h1 : st.core.trail_end % 2 ^ 64 ≤ k.toNat := by c0_bound
                  rw [Nat.mod_eq_of_lt (by omega)] at h1; omega
                fvt_steps
                refine hQ res mrk_k mk hmk_len
                  (fun v hv => Classical.byContradiction fun hnz => by
                    obtain ⟨i, hi1, hi2, _⟩ := hmk_dom v hv hnz; omega)
                  hres_ok hmk)
          (fun Jbr hJbr => ?_)
        refine wp_loop_inv (ts := [i64])
          (fun (t, ()) mt => ∃ mrk_t : List (BitVec 8), mrk_t.length = c.max_vars ∧
            saved0 ≤ t.toNat ∧ t.toNat ≤ st.core.trail_end ∧
            (∃ i1 i2, saved0 ≤ i1 ∧ i1 < i2 ∧ saved.toNat ≤ i2 ∧ i2 < t.toNat ∧
              (∀ v < c.max_vars, mrk_t[v]?.getD 0#8 ≠ 0#8 ↔
                v = (st.core.trl[i1]?.getD 0#32).toNat / 2 ∨
                v = (st.core.trl[i2]?.getD 0#32).toNat / 2) ∧
              (cnfOfClauses F_cur).EntailsClause
                (cnfClause [(st.core.trl[i1]?.getD 0#32).toNat ^^^ 1,
                            (st.core.trl[i2]?.getD 0#32).toNat ^^^ 1])) ∧
            (FullMem c { st with core := { st.core with mrk := mrk_t } } ⋆ R) mt)
          (fun (t, ()) _ => t.toNat) ?_ ?_
        · intro Jt hJt; fvt_steps
          let mrk_init := (st.core.mrk.set (c0 >>> 1#32).toNat 1#8).set (c1 >>> 1#32).toNat 1#8
          have hmi_len : mrk_init.length = c.max_vars := by simp [mrk_init, hcl.mrk_len]
          have hmi_iff : ∀ v < c.max_vars,
              mrk_init[v]?.getD 0#8 ≠ 0#8 ↔ v = c0.toNat / 2 ∨ v = c1.toNat / 2 := fun v hv => by
            dsimp only [mrk_init]
            by_cases h1 : v = c1.toNat / 2
            · subst h1
              rw [show (c1 >>> 1#32).toNat = c1.toNat / 2 from s13_bb_bv32_lshr1 c1,
                List.getElem?_set_self (by simp [hcl.mrk_len]; omega), Option.getD_some]
              exact ⟨fun _ => Or.inr rfl, fun _ => by decide⟩
            · rw [show (c1 >>> 1#32).toNat = c1.toNat / 2 from s13_bb_bv32_lshr1 c1,
                List.getElem?_set_ne (Ne.symm h1)]
              by_cases h0 : v = c0.toNat / 2
              · subst h0
                rw [show (c0 >>> 1#32).toNat = c0.toNat / 2 from s13_bb_bv32_lshr1 c0,
                  List.getElem?_set_self (by rw [hcl.mrk_len]; omega), Option.getD_some]
                exact ⟨fun _ => Or.inl rfl, fun _ => by decide⟩
              · rw [show (c0 >>> 1#32).toNat = c0.toNat / 2 from s13_bb_bv32_lshr1 c0,
                  List.getElem?_set_ne (Ne.symm h0), hmrk0 v hv]
                exact ⟨fun h => absurd rfl h,
                  fun h => h.elim (fun he => absurd he h0) (fun he => absurd he h1)⟩
          have hst_mi : ({ st with core := { st.core with
              mrk := (st.core.mrk.set (BitVec.setWidth 64 (c0 >>> 1)).toNat 1#8).set
                (BitVec.setWidth 64 (c1 >>> 1)).toNat 1#8 } } : FullState) =
              { st with core := { st.core with mrk := mrk_init } } := by
            dsimp only [mrk_init]
            have h0_64 : (BitVec.setWidth 64 (c0 >>> 1)).toNat = (c0 >>> 1#32).toNat := by
              have hlt := BitVec.isLt (c0 >>> 1)
              rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]; rfl
            have h1_64 : (BitVec.setWidth 64 (c1 >>> 1)).toNat = (c1 >>> 1#32).toNat := by
              have hlt := BitVec.isLt (c1 >>> 1)
              rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]; rfl
            rw [h0_64, h1_64]
          refine hJt (BitVec.ofNat 64 st.core.trail_end, ()) _
            ⟨mrk_init, hmi_len, by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega,
             by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact Nat.le_refl _, ?_,
             s13_bb_fullMem_eq hst_mi hm⟩
          rcases Nat.lt_or_gt_of_ne hidx_ne with h01 | h10
          · refine ⟨idx0, idx1, Nat.le_trans hs0_sav hidx0_ge, h01, by omega,
              by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hidx1_lt,
              fun v hv => by
                rw [hidx0_eq, hidx1_eq, fullInv_var_xor1, fullInv_var_xor1]; exact hmi_iff v hv,
              by rw [hidx0_eq, hidx1_eq, s13_bb_xor1_xor1, s13_bb_xor1_xor1]; exact hent_c⟩
          · refine ⟨idx1, idx0, hidx1_ge, h10, hidx0_ge,
              by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hidx0_lt,
              fun v hv => by
                rw [hidx0_eq, hidx1_eq, fullInv_var_xor1, fullInv_var_xor1, or_comm]
                exact hmi_iff v hv,
              by rw [hidx0_eq, hidx1_eq, s13_bb_xor1_xor1, s13_bb_xor1_xor1]
                 exact s13_bb_entails_comm2 hent_c⟩
        · rintro Jt ⟨t, ⟨⟩⟩ mt
            ⟨mrk_t, hmt_len, ht_ge, ht_le, ⟨i1, i2, hi1_ge, hi12, hi2_sav, hi2_lt, hdom, hent2⟩,
             hmt⟩ iht
          fvt_step; fvt_step
          · have ht_gt : saved0 < t.toNat := by
              have h1 : saved_b0.toNat < t.toNat := by simpa [hres_eq] using (by c0_bound : _)
              rwa [hsaved_nat] at h1
            have ht_sub : (t - 1#64).toNat = t.toNat - 1 := by bv_omega
            have ht1_trl : (t - 1#64).toNat < st.core.trl.length := by rw [hcl.trl_len]; omega
            let z := st.core.trl[(t - 1#64).toNat]'ht1_trl
            have hz_get : st.core.trl[t.toNat - 1]?.getD 0#32 = z := by
              rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; dsimp only [z]
              simp only [ht_sub]
            have hz_lt : z.toNat < 2 * s0.core.cur_vars := by
              have := hbt.trl_lits_lt (t.toNat - 1) (by omega); rwa [hz_get] at this
            have hzv_lt : (z >>> 1#32).toNat < c.max_vars := by rw [s13_bb_bv32_lshr1]; omega
            have hzv_mrk : (z >>> 1#32).toNat < mrk_t.length := by rw [hmt_len]; omega
            have hzv_rsn : (z >>> 1#32).toNat < st.core.rsns.length := by
              rw [hcl.rsns_len]; omega
            fvt_step; fvt_step; fvt_step
            · have hm_z0 : mrk_t[(z >>> 1#32).toNat]?.getD 0#8 = 0#8 := by
                rw [List.getElem?_eq_getElem hzv_mrk, Option.getD_some]
                exact (s13_bb_bv8_zext32_eq0 _).mp (by c0_bound)
              have hi2_ne : i2 ≠ t.toNat - 1 := fun he => by
                have hnz : mrk_t[(z >>> 1#32).toNat]?.getD 0#8 ≠ 0#8 :=
                  (hdom _ hzv_lt).mpr (Or.inr (by rw [s13_bb_bv32_lshr1, he, hz_get]))
                exact hnz hm_z0
              fvt_steps
              exact iht (t - 1#64, ()) mt (by dsimp only; omega)
                ⟨mrk_t, hmt_len, by omega, by omega,
                 ⟨i1, i2, hi1_ge, hi12, hi2_sav, by omega, hdom, hent2⟩, hmt⟩
            · have hm_znz : mrk_t[(z >>> 1#32).toNat]?.getD 0#8 ≠ 0#8 := fun h0 => by
                rw [List.getElem?_eq_getElem hzv_mrk, Option.getD_some] at h0
                exact (by c0_bound : (mrk_t[(z >>> 1#32).toNat]'hzv_mrk).setWidth 32 ≠ 0#32)
                  ((s13_bb_bv8_zext32_eq0 _).mpr h0)
              have hi2_eq : t.toNat - 1 = i2 := by
                rcases (hdom _ hzv_lt).mp hm_znz with h_eq1 | h_eq2
                · have := hbt.trl_vars_nodup (t.toNat - 1) i1 (by omega) (by omega)
                    (by rw [hz_get, ← s13_bb_bv32_lshr1]; exact h_eq1)
                  omega
                · exact hbt.trl_vars_nodup (t.toNat - 1) i2 (by omega) (by omega)
                    (by rw [hz_get, ← s13_bb_bv32_lshr1]; exact h_eq2)
              let mrk1 := mrk_t.set (z >>> 1#32).toNat 0#8
              have hm1_len : mrk1.length = c.max_vars := by simp [mrk1, hmt_len]
              have hv1_ne_v2 : (st.core.trl[i1]?.getD 0#32).toNat / 2 ≠
                  (st.core.trl[i2]?.getD 0#32).toNat / 2 := fun he => by
                have := hbt.trl_vars_nodup i1 i2 (by omega) (by omega) he; omega
              have hm1_iff : ∀ v < c.max_vars,
                  mrk1[v]?.getD 0#8 ≠ 0#8 ↔ v = (st.core.trl[i1]?.getD 0#32).toNat / 2 := by
                intro v hv; dsimp only [mrk1]
                by_cases he : v = (z >>> 1#32).toNat
                · subst he; rw [List.getElem?_set_self hzv_mrk, Option.getD_some]
                  exact ⟨fun h => absurd rfl h, fun h => absurd h.symm (by
                    rw [s13_bb_bv32_lshr1, ← hz_get, hi2_eq]; exact hv1_ne_v2)⟩
                · rw [List.getElem?_set_ne (Ne.symm he), hdom v hv]
                  exact ⟨fun ho => ho.elim id fun h2 => absurd
                    (by rw [h2, ← hi2_eq, hz_get, s13_bb_bv32_lshr1]) he, Or.inl⟩
              have hrsn_get : st.core.rsns[(st.core.trl[i2]?.getD 0#32).toNat / 2]?.getD
                  0xFFFFFFFF#32 = st.core.rsns[(z >>> 1#32).toNat]'hzv_rsn := by
                rw [← hi2_eq, hz_get, ← s13_bb_bv32_lshr1,
                  List.getElem?_eq_getElem hzv_rsn, Option.getD_some]
              c0_hsplit
              · c0_hsteps
                exact hJbr (t - 1#64, 0xFFFFFFFF#32, ()) _ ⟨mrk1, hm1_len,
                  (fun v hv hnz => ⟨i1, hi1_ge, by omega, ((hm1_iff v hv).mp hnz).symm⟩),
                  (fun h => absurd rfl h), hm⟩
              · have hrsn_ne_ff : st.core.rsns[(z >>> 1#32).toNat]'hzv_rsn ≠ 0xFFFFFFFF#32 := by
                  c0_bound
                c0_hsplit
                · c0_hsteps
                  exact hJbr (t - 1#64, 0xFFFFFFFF#32, ()) _ ⟨mrk1, hm1_len,
                    (fun v hv hnz => ⟨i1, hi1_ge, by omega, ((hm1_iff v hv).mp hnz).symm⟩),
                    (fun h => absurd rfl h), hm⟩
                · have hi2_ne_sav : i2 ≠ saved.toNat := fun he => by
                    rw [← hrsn_get, he] at hrsn_ne_ff; exact hrsn_ne_ff hrsn_sav
                  have hi2_gt_s : saved.toNat < i2 := by omega
                  obtain ⟨hbf_s, hnq_lt, hent_z, j, hj_ge, hj_lt, hj_eq⟩ :=
                    (hseg.2.2 i2 (by omega) (by omega)).2 hi2_gt_s
                  rw [hrsn_get] at hnq_lt hent_z hj_eq
                  let p_l := (st.core.rsns[(z >>> 1#32).toNat]'hzv_rsn &&& 0x7FFFFFFF#32) ^^^ 1#32
                  have hp_eq : p_l.toNat = (st.core.trl[j]?.getD 0#32).toNat := by
                    dsimp only [p_l]; rw [s13_bb_bv32_xor1, hj_eq]
                  have hp_lt : p_l.toNat < 2 * s0.core.cur_vars := by
                    rw [hp_eq]; exact hbt.trl_lits_lt j (by omega)
                  have hpv_lt : (p_l >>> 1#32).toNat < c.max_vars := by
                    rw [s13_bb_bv32_lshr1]; omega
                  have hpv_mrk : (p_l >>> 1#32).toNat < mrk1.length := by rw [hm1_len]; omega
                  have hent_res : (cnfOfClauses F_cur).EntailsClause
                      (cnfClause [p_l.toNat ^^^ 1, (st.core.trl[i1]?.getD 0#32).toNat ^^^ 1]) := by
                    refine backbone_resolve2 (s13_bb_entails_comm2 hent2) ?_
                    simpa [p_l, s13_bb_bv32_xor1, s13_bb_xor1_xor1] using hent_z
                  c0_hsplit
                  · have hm1_pnz : mrk1[(p_l >>> 1#32).toNat]?.getD 0#8 ≠ 0#8 := fun h0 => by
                      rw [List.getElem?_eq_getElem hpv_mrk, Option.getD_some] at h0
                      exact (by c0_bound : (mrk1[(p_l >>> 1#32).toNat]'hpv_mrk).setWidth 32 ≠ 0#32)
                        ((s13_bb_bv8_zext32_eq0 _).mpr h0)
                    have hj_eq_i1 : j = i1 := hbt.trl_vars_nodup j i1 (by omega) (by omega) (by
                      rw [← hp_eq, ← s13_bb_bv32_lshr1]; exact (hm1_iff _ hpv_lt).mp hm1_pnz)
                    have hp_eq_i1 : (st.core.trl[i1]?.getD 0#32).toNat = p_l.toNat := by
                      rw [← hj_eq_i1, hp_eq]
                    have hent_uip :
                        (cnfOfClauses F_cur).EntailsClause (cnfClause [p_l.toNat ^^^ 1]) :=
                      backbone_collapse_eq (by rwa [hp_eq_i1] at hent_res)
                    fvt_steps
                    exact hJbr (t - 1#64, p_l, ()) _ ⟨mrk1, hm1_len,
                      (fun v hv hnz => ⟨i1, hi1_ge, by omega, ((hm1_iff v hv).mp hnz).symm⟩),
                      (fun _ => ⟨hp_lt, hent_uip⟩), hm⟩
                  · have hm1_pz : mrk1[(p_l >>> 1#32).toNat]?.getD 0#8 = 0#8 := by
                      rw [List.getElem?_eq_getElem hpv_mrk, Option.getD_some]
                      exact (s13_bb_bv8_zext32_eq0 _).mp (by c0_bound)
                    have hj_ne_i1 : j ≠ i1 := fun he => by
                      subst he
                      have hnz := (hm1_iff _ hpv_lt).mpr (by rw [s13_bb_bv32_lshr1, hp_eq])
                      exact hnz hm1_pz
                    let mrk2 := mrk1.set (p_l >>> 1#32).toNat 1#8
                    have hm2_iff : ∀ v < c.max_vars, mrk2[v]?.getD 0#8 ≠ 0#8 ↔
                        v = (st.core.trl[j]?.getD 0#32).toNat / 2 ∨
                        v = (st.core.trl[i1]?.getD 0#32).toNat / 2 := fun v hv => by
                      dsimp only [mrk2]
                      by_cases he : v = (p_l >>> 1#32).toNat
                      · subst he; rw [List.getElem?_set_self hpv_mrk, Option.getD_some]
                        exact ⟨fun _ => Or.inl (by rw [s13_bb_bv32_lshr1, hp_eq]),
                          fun _ => by decide⟩
                      · rw [List.getElem?_set_ne (Ne.symm he), hm1_iff v hv]
                        exact ⟨Or.inr, fun ho => ho.elim
                          (fun h => absurd (by rw [s13_bb_bv32_lshr1, hp_eq]; exact h) he) id⟩
                    have hsw_z : (BitVec.setWidth 64
                        (st.core.trl[(t - 1#64).toNat]'ht1_trl >>> 1#32)).toNat =
                        (z >>> 1#32).toNat := FullTransHelpers.ft_bv32_setWidth64 _
                    have hpv_c0 : (BitVec.setWidth 64
                        ((st.core.rsns[(BitVec.setWidth 64
                          (st.core.trl[(t - 1#64).toNat]'ht1_trl >>> 1#32)).toNat]'(by
                            rw [hsw_z]; exact hzv_rsn) &&& 0x7FFFFFFF#32 ^^^ 1#32) >>>
                          1#32)).toNat < (mrk_t.set (BitVec.setWidth 64
                        (st.core.trl[(t - 1#64).toNat]'ht1_trl >>> 1#32)).toNat 0#8).length := by
                      rw [List.length_set, FullTransHelpers.ft_bv32_setWidth64]
                      change (BitVec.setWidth 64 (p_l >>> 1#32)).toNat < mrk_t.length
                      rw [FullTransHelpers.ft_bv32_setWidth64, hmt_len]; exact hpv_lt
                    c0_hsteps
                    refine iht (t - 1#64, ()) _ (by dsimp only; omega)
                      ⟨mrk2, by simp [mrk2, hm1_len], by omega, by omega, ?_,
                       s13_bb_fullMem_eq (by dsimp only [mrk2, mrk1])
                         (by assumption)⟩
                    rcases Nat.lt_or_gt_of_ne hj_ne_i1 with hji | hij
                    · exact ⟨j, i1, Nat.le_trans hs0_sav hj_ge, hji, by omega, by omega, hm2_iff,
                        by rwa [hp_eq] at hent_res⟩
                    · exact ⟨i1, j, hi1_ge, hij, hj_ge, by omega,
                        fun v hv => by rw [or_comm]; exact hm2_iff v hv,
                        s13_bb_entails_comm2 (by rwa [hp_eq] at hent_res)⟩

  end BackboneAnalyzeS5

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S5
