/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Src.Definition
public import LeanQbe.T.Examples.Kissat.Proof.Definition.WpFidExtract0
public import LeanQbe.T.Examples.Kissat.Proof.Kitten.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Backtrack.Spec

/-!
# Fid `full_bve_certify_unit_fid` Shared Helpers & Phase 1 (`Proof.Definition.WpFidCert0`)

Shared memory framing, semantic entailment helpers, `tmk` clear loop, unit-commit tail,
and Phase 1 literal/variable collection (`@L225` + `@L853`) for `full_bve_certify_unit_fid_wp`.
Zero legacy `Full*` imports; zero `@[expose]` on theorems/lemmas/sections.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Definition

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Definition.Spec
open LeanQbe.T.Examples.Kissat.Proof.Kitten
open LeanQbe.T.Examples.Kissat.Proof.Kitten.Spec

open scoped FullArenaTactics FidK6cTactics

public section

/-! ## 1. `FidCertGu`, Framing, Trail-Nonfull, & `i8` Sign Helpers -/

abbrev FidCertGu (s : FullState) (gu : List (BitVec 32)) : FullState :=
  { s with scratch := { s.scratch with glue_used := gu } }

@[expose] def fidCertAddClauseOuter (c : FullCfg) (s : FullState) : Mem 64 → Prop :=
  dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
  FullCoreByteArrs c s.core ⋆
  (array (t := i32) c.pFlags s.core.flags ⋆ array (t := i32) c.pLevel s.core.lvl ⋆
   array (t := i32) c.pReason s.core.rsns ⋆ array (t := i32) c.pTrail s.core.trl ⋆
   array (t := i32) c.pTrailPos s.core.trail_pos ⋆
   array (t := i32) c.pMinClr s.core.min_clr) ⋆
  FullCoreU32B c s.core ⋆ FullCoreDynArrs c s.core ⋆
  (FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆ FullScrWksArrs c s.scratch ⋆
   (array64 c.pScore s.scratch.score ⋆ array64 c.pSimSig s.scratch.sim_sig ⋆
    array (t := i32) c.pLastLearned s.scratch.last_learned) ⋆
   (array (t := i32) c.pDelayed s.scratch.delayed ⋆
    array (t := i32) c.pRedRefs s.scratch.red_refs ⋆
    array (t := i32) c.pExtendStk s.scratch.extend_stk)) ⋆ c.pad

theorem fid_cert_add_clause_split {c : FullCfg} {s : FullState}
    {tmp wsort tmk gu scr : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem c (FidP6Work (FidCertGu s gu) tmp wsort tmk scr) ⋆ R) m) :
    let sw := FidP6Work (FidCertGu s gu) tmp wsort tmk scr
    (array64 (c.hdr + 32) (hdrTailWords c sw) ⋆
      array (t := i32) c.pScratchBuf scr ⋆ array (t := i32) c.pGlueUsed gu ⋆
      array (t := i32) c.pTmp tmp ⋆ (fidCertAddClauseOuter c sw ⋆ R)) m := by
  intro sw
  have heq :
      (FullMem c sw ⋆ R) =
        (array64 (c.hdr + 32) (hdrTailWords c sw) ⋆
          array (t := i32) c.pScratchBuf scr ⋆ array (t := i32) c.pGlueUsed gu ⋆
          array (t := i32) c.pTmp tmp ⋆ (fidCertAddClauseOuter c sw ⋆ R)) := by
    unfold FullMem FullCoreArrays FullCoreU32A FullScratchArrays FullScrMetaArrs
      FullScrDynArrs fidCertAddClauseOuter
    dsimp only [sw, FidP6Work, FidCertGu]
    ac_rfl
  exact heq ▸ hm

theorem fid_cert_add_clause_join {c : FullCfg} {s : FullState}
    {tmp wsort tmk gu gu' scr scr' : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (array64 (c.hdr + 32) (hdrTailWords c (FidP6Work (FidCertGu s gu) tmp wsort tmk scr)) ⋆
      array (t := i32) c.pScratchBuf scr' ⋆ array (t := i32) c.pGlueUsed gu' ⋆
      array (t := i32) c.pTmp tmp ⋆
      (fidCertAddClauseOuter c (FidP6Work (FidCertGu s gu) tmp wsort tmk scr) ⋆ R)) m) :
    (FullMem c (FidP6Work (FidCertGu s gu') tmp wsort tmk scr') ⋆ R) m := by
  let sw0 := FidP6Work (FidCertGu s gu) tmp wsort tmk scr
  let sw1 := FidP6Work (FidCertGu s gu') tmp wsort tmk scr'
  have hhdr : hdrTailWords c sw1 = hdrTailWords c sw0 := rfl
  have hout : fidCertAddClauseOuter c sw1 = fidCertAddClauseOuter c sw0 := by
    unfold fidCertAddClauseOuter FullCoreByteArrs FullCoreU32B FullCoreDynArrs
      FullScrByteArrs FullScrU32A FullScrWksArrs
    rfl
  have heq :
      (FullMem c sw1 ⋆ R) =
        (array64 (c.hdr + 32) (hdrTailWords c sw1) ⋆
          array (t := i32) c.pScratchBuf scr' ⋆ array (t := i32) c.pGlueUsed gu' ⋆
          array (t := i32) c.pTmp tmp ⋆ (fidCertAddClauseOuter c sw1 ⋆ R)) := by
    unfold FullMem FullCoreArrays FullCoreU32A FullScratchArrays FullScrMetaArrs
      FullScrDynArrs fidCertAddClauseOuter
    dsimp only [sw1, FidP6Work, FidCertGu]
    ac_rfl
  rw [heq, hhdr, hout]
  exact hm

theorem fid_cert_denseInvW_gu_only {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hi : FullDenseInvW c F0 F_cur s) {gu : List (BitVec 32)}
    (hgu : gu.length = 64) : FullDenseInvW c F0 F_cur (FidCertGu s gu) :=
  ⟨⟨hi.1.core_ok, { hi.1.scratch_ok with glue_used_len := hgu }⟩,
   hi.2.1, hi.2.2.1, hi.2.2.2.1, hi.2.2.2.2.1, hi.2.2.2.2.2.1, hi.2.2.2.2.2.2⟩

theorem fid_cert_denseInvW_gu {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hi : FullDenseInvW c F0 F_cur s)
    {tmp wsort tmk gu scr : List (BitVec 32)}
    (ht : tmp.length = c.max_vars) (hw : wsort.length = 2 * c.max_vars)
    (htm : tmk.length = 2 * c.max_vars) (hgu : gu.length = 64)
    (hscr : scr.length = c.scratch_cap) :
    FullDenseInvW c F0 F_cur (FidP6Work (FidCertGu s gu) tmp wsort tmk scr) :=
  fid_k6c_fullDenseInvW_work (fid_cert_denseInvW_gu_only hi hgu) ht hw htm hscr

theorem fid_cert_work_gu_lengthsOk {c : FullCfg} {s : FullState}
    (hl : s.LengthsOk c) {tmp wsort tmk gu scr : List (BitVec 32)}
    (ht : tmp.length = c.max_vars) (hw : wsort.length = 2 * c.max_vars)
    (htm : tmk.length = 2 * c.max_vars) (hgu : gu.length = 64)
    (hscr : scr.length = c.scratch_cap) :
    (FidP6Work (FidCertGu s gu) tmp wsort tmk scr).LengthsOk c :=
  ⟨{ hl.core_ok with tmp_len_arr := ht },
   { hl.scratch_ok with
     wsort_len := hw, tarjan_mark_len := htm, glue_used_len := hgu, scratch_buf_len := hscr }⟩

theorem fid_cert_bv8_slt_iff {v : BitVec 8} (h : v = 0#8 ∨ v = 1#8 ∨ v = 255#8) :
    BitVec.slt (BitVec.signExtend 32 v) (BitVec.signExtend 32 (BitVec.truncate 8 0#32)) = true ↔
      v = 255#8 := by
  rcases h with rfl | rfl | rfl <;> decide

theorem fid_cert_bv8_sgt_iff {v : BitVec 8} (h : v = 0#8 ∨ v = 1#8 ∨ v = 255#8) :
    BitVec.slt (BitVec.signExtend 32 (BitVec.truncate 8 0#32)) (BitVec.signExtend 32 v) = true ↔
      v = 1#8 := by
  rcases h with rfl | rfl | rfl <;> decide

theorem fid_cert_bv8_eq0_iff {v : BitVec 8} (h : v = 0#8 ∨ v = 1#8 ∨ v = 255#8) :
    BitVec.signExtend 32 v = BitVec.signExtend 32 (BitVec.truncate 8 0#32) ↔ v = 0#8 := by
  rcases h with rfl | rfl | rfl <;> decide

private theorem nat_inj_range_le : ∀ (n k : Nat) (f : Nat → Nat),
    (∀ i < k, f i < n) → (∀ i j, i < k → j < k → f i = f j → i = j) → k ≤ n
  | 0, k, f, hlt, _ => by
    cases k with
    | zero => exact Nat.zero_le _
    | succ k' => exact absurd (hlt 0 (Nat.zero_lt_succ _)) (Nat.not_lt_zero _)
  | n + 1, k, f, hlt, hinj => by
    by_cases hsub : ∀ i < k, f i < n
    · exact Nat.le_trans (nat_inj_range_le n k f hsub hinj) (Nat.le_succ _)
    · have hex : ∃ p < k, f p = n := by
        suffices ∀ m, m ≤ k → (∀ i < m, f i < n) ∨ ∃ p < m, f p = n by
          rcases this k (Nat.le_refl _) with hall | hex
          · exact absurd hall hsub
          · exact hex
        intro m; induction m with
        | zero => intro _; exact Or.inl fun _ h0 => absurd h0 (Nat.not_lt_zero _)
        | succ m' ih =>
          intro hm
          rcases ih (Nat.le_trans (Nat.le_succ _) hm) with hlt' | ⟨p, hp, hfp⟩
          · by_cases hm_eq : f m' = n
            · exact Or.inr ⟨m', Nat.lt_succ_self _, hm_eq⟩
            · refine Or.inl fun i hi => ?_
              rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | hi_eq
              · exact hlt' i hi'
              · have := hlt m' (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hm)
                rw [hi_eq]; omega
          · exact Or.inr ⟨p, Nat.lt_succ_of_lt hp, hfp⟩
      rcases hex with ⟨p, hp, hfp⟩
      cases k with
      | zero => exact Nat.zero_le _
      | succ k' =>
        let g : Nat → Nat := fun i => if i = p then f k' else f i
        have hg_lt : ∀ i < k', g i < n := by
          intro i hi
          dsimp only [g]
          split <;> rename_i hpi
          · have hne : f k' ≠ f p := fun h => by
              have := hinj k' p (Nat.lt_succ_self _) hp h; omega
            have := hlt k' (Nat.lt_succ_self _); omega
          · have hne : f i ≠ f p := fun h => by
              have := hinj i p (Nat.lt_succ_of_lt hi) hp h; omega
            have := hlt i (Nat.lt_succ_of_lt hi); omega
        have hg_inj : ∀ i j, i < k' → j < k' → g i = g j → i = j := by
          intro i j hi hj heq
          dsimp only [g] at heq
          split at heq <;> split at heq
          · simp_all
          · have := hinj k' j (Nat.lt_succ_self _) (Nat.lt_succ_of_lt hj) heq; omega
          · have := hinj i k' (Nat.lt_succ_of_lt hi) (Nat.lt_succ_self _) heq; omega
          · exact hinj i j (Nat.lt_succ_of_lt hi) (Nat.lt_succ_of_lt hj) heq
        exact Nat.succ_le_succ (nat_inj_range_le n k' g hg_lt hg_inj)

theorem fid_xor_one_eq (n : Nat) : n ^^^ 1 = if n % 2 = 0 then n + 1 else n - 1 := by
  have hmod : n % 2 = 0 ∨ n % 2 = 1 := Nat.mod_two_eq_zero_or_one n
  apply Nat.eq_of_testBit_eq; intro k; cases k with
  | zero =>
    rw [Nat.testBit_xor, Nat.testBit_one_zero]
    rcases hmod with h0 | h1
    · simp [h0, show (n + 1) % 2 = 1 by omega, Nat.testBit_zero]
    · simp [h1, show (n - 1) % 2 = 0 by omega, Nat.testBit_zero]
  | succ k' =>
    have hp : 1 < 2 ^ (k' + 1) := by
      rw [Nat.pow_succ]; have := Nat.one_le_pow k' 2 (by omega); omega
    have h1k : Nat.testBit 1 (k' + 1) = false := by
      simp [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hp]
    rw [Nat.testBit_xor, h1k, Bool.xor_false]
    rcases hmod with h0 | h1
    · simp only [h0, ↓reduceIte, Nat.testBit, Nat.shiftRight_eq_div_pow]
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ k') 2, ← Nat.div_div_eq_div_mul,
        ← Nat.div_div_eq_div_mul, show (n + 1) / 2 = n / 2 by omega]
    · simp only [show ¬(n % 2 = 0) by omega, ↓reduceIte, Nat.testBit, Nat.shiftRight_eq_div_pow]
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ k') 2, ← Nat.div_div_eq_div_mul,
        ← Nat.div_div_eq_div_mul, show (n - 1) / 2 = n / 2 by omega]

theorem fid_cert_trail_lt_of_unassigned {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hinv : FullDenseInvW c F0 F_cur s)
    {l : Nat} (hl : l < 2 * s.core.cur_vars)
    (hz : s.core.vals[l]?.getD 0#8 = 0#8) :
    s.core.trail_end < c.max_vars := by
  have hle : s.core.trail_end ≤ s.core.cur_vars := hinv.1.core_ok.trail_end_le
  have hcv : s.core.cur_vars ≤ c.max_vars := hinv.1.core_ok.cur_vars_le
  by_cases hge : s.core.trail_end < c.max_vars
  · exact hge
  · exfalso
    have heq : s.core.trail_end = s.core.cur_vars := by omega
    let f : Nat → Nat := fun i => (s.core.trl[i]?.getD 0#32).toNat / 2
    have hmiss : ∀ i < s.core.trail_end, f i ≠ l / 2 := by
      intro i hi hfeq
      have hilt := hinv.2.1.trail_lits_lt i hi
      have hcases : (s.core.trl[i]?.getD 0#32).toNat = l ∨
          (s.core.trl[i]?.getD 0#32).toNat = l ^^^ 1 := by
        rw [fid_xor_one_eq]; dsimp only [f] at hfeq; split <;> omega
      rcases hcases with htr | htr
      · have h1 := (hinv.2.1.vals_true_iff l hl).mpr ⟨i, hi, htr⟩
        rw [h1] at hz; cases hz
      · have h255 := (hinv.2.1.vals_false_iff l hl).mpr ⟨i, hi, htr⟩
        rw [h255] at hz; cases hz
    let g : Nat → Nat := fun i => if f i < l / 2 then f i else f i - 1
    have hg_lt : ∀ i < s.core.trail_end, g i < s.core.cur_vars - 1 := by
      intro i hi
      have hlt := hinv.2.1.trail_lits_lt i hi
      have hne := hmiss i hi
      dsimp only [g, f] at *; split <;> omega
    have hg_inj : ∀ i j, i < s.core.trail_end → j < s.core.trail_end → g i = g j → i = j := by
      intro i j hi hj heqg
      have hne_i := hmiss i hi; have hne_j := hmiss j hj
      dsimp only [g] at heqg
      split at heqg <;> split at heqg
      · exact hinv.2.1.trail_vars_nodup i j hi hj heqg
      · exfalso; omega
      · exfalso; omega
      · exact hinv.2.1.trail_vars_nodup i j hi hj (by dsimp only [f] at *; omega)
    have hle_c := nat_inj_range_le (s.core.cur_vars - 1) s.core.trail_end g hg_lt hg_inj
    omega

/-! ## 2. Semantic Entailment & Kitten Valuation Bridge -/

theorem fid_cert_entails_resolve_bin {F : CNF Nat} {u ot : Nat}
    (h1 : F.EntailsClause (cnfClause [u, ot]))
    (h2 : F.EntailsClause (cnfClause [ot ^^^ 1])) :
    F.EntailsClause (cnfClause [u]) := by
  rw [CNF.entails_clause_def] at h1 h2 ⊢
  intro α hsat
  have hc1 := (clause_sat_cnfClause_iff α [u, ot]).mp (h1 α hsat)
  have hneg := (sat_cnfClause_litNeg_iff α ot).mp (h2 α hsat)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc1
  rcases hc1 with ⟨x, rfl | rfl, hxs⟩
  · exact (sat_cnfClause_singleton α x).mpr hxs
  · exact absurd ((sat_cnfClause_singleton α x).mpr hxs) hneg

@[expose] def fidCertP (F_cur : List (List Nat)) (wsort : List (BitVec 32))
    (nv unit : Nat) : (Nat → Bool) → Prop :=
  fun β => ∃ α : Nat → Bool,
    (cnfOfClauses F_cur).Sat α ∧
    (unit % 2 = 0 → α (unit / 2) = false) ∧
    (unit % 2 = 1 → α (unit / 2) = true) ∧
    ∀ kv, kv < nv → β kv = α (wsort[kv]?.getD 0#32).toNat

@[expose] def FidCertLitMap (nv : Nat) (wsort : List (BitVec 32)) (kl ol : Nat) : Prop :=
  kl / 2 < nv ∧ (wsort[kl / 2]?.getD 0#32).toNat = ol / 2 ∧ kl % 2 = ol % 2

theorem fid_cert_litMap_build {nv cur_vars : Nat} {wsort tmk : List (BitVec 32)}
    (hreg : FidK6cTmkReg nv cur_vars wsort tmk) (hnv : nv ≤ cur_vars)
    (hcv : 2 * cur_vars < 2 ^ 30) {l : BitVec 32} (hl : l.toNat < 2 * cur_vars)
    {tv : BitVec 32} (hnz : tv ≠ 0#32) (hle : tv.toNat ≤ nv)
    (htv : tmk[l.toNat / 2]?.getD 0#32 = tv) :
    let idx := tv - 1#32
    let kl := (idx <<< 1) ||| (l &&& 1#32)
    kl.toNat < 2 * nv ∧ FidCertLitMap nv wsort kl.toNat l.toNat := by
  have hv_lt : l.toNat / 2 < cur_vars := by omega
  have htnz : tmk[l.toNat / 2]?.getD 0#32 ≠ 0#32 := by rw [htv]; exact hnz
  rcases hreg.2.2 (l.toNat / 2) hv_lt htnz with ⟨i, hi, hws, hti⟩
  have hti' : tv.toNat = i + 1 := by rw [← htv]; exact hti
  have htv_bd : tv.toNat ≤ cur_vars := Nat.le_trans hle hnv
  have hidx : (tv - 1#32).toNat = i := by bv_omega
  have hand : (l &&& 1#32).toNat = l.toNat % 2 := by
    rw [BitVec.toNat_and, show (1#32 : BitVec 32).toNat = 1 from rfl, Nat.and_one_is_mod]
  have hkl : (((tv - 1#32) <<< 1) ||| (l &&& 1#32)).toNat = 2 * i + l.toNat % 2 := by
    have hsh : ((tv - 1#32) <<< 1).toNat = 2 * i := by bv_omega
    rw [BitVec.toNat_or, hsh, hand]
    apply Nat.eq_of_testBit_eq; intro b
    cases b with
    | zero =>
      rw [Nat.testBit_or, Nat.testBit_zero, Nat.testBit_zero, Nat.testBit_zero]
      have : (2 * i + l.toNat % 2) % 2 = l.toNat % 2 := by omega
      rw [this]; cases (Nat.mod_two_eq_zero_or_one l.toNat) with
      | inl h => simp [h]
      | inr h => simp [h]
    | succ j =>
      rw [Nat.testBit_or, Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ]
      have h1 : (l.toNat % 2) / 2 = 0 := by omega
      have h2 : (2 * i + l.toNat % 2) / 2 = i := by omega
      rw [h1, Nat.zero_testBit, Bool.or_false, h2, Nat.mul_div_right _ (by omega)]
  refine ⟨by rw [hkl]; omega, ⟨by rw [hkl]; omega, ?_, by rw [hkl]; omega⟩⟩
  rw [hkl, show (2 * i + l.toNat % 2) / 2 = i by omega]; exact hws

theorem fid_cert_semEntails_bin {F_cur : List (List Nat)}
    {wsort : List (BitVec 32)} {nv : Nat} {unit kl ot : Nat}
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [unit, ot]))
    (hmap : FidCertLitMap nv wsort kl ot) :
    SemEntails (fidCertP F_cur wsort nv unit) [kl] := by
  intro β ⟨α, hsat, hu0, hu1, hβ⟩
  have hc := (clause_sat_cnfClause_iff α [unit, ot]).mp
    (CNF.entails_clause_def.mp hent α hsat)
  have hu_false : ¬ CNF.Clause.Sat α (cnfClause [unit]) := by
    rw [sat_cnfClause_singleton]; dsimp only [litVar, litSign]
    cases hm : (unit % 2 == 1)
    · have hm0 : unit % 2 = 0 := by
        have : ¬ (unit % 2 = 1) := by intro h; simp [h] at hm
        omega
      simp [hu0 hm0]
    · simp [hu1 (Nat.beq_eq.mp hm)]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with ⟨x, rfl | rfl, hxs⟩
  · exact absurd ((sat_cnfClause_singleton α x).mpr hxs) hu_false
  · rw [sat_cnfClause_singleton]; dsimp only [litVar, litSign] at hxs ⊢
    have hβ' := hβ (kl / 2) hmap.1
    rw [hmap.2.1] at hβ'
    rw [hβ', show (kl % 2 == 1) = (x % 2 == 1) by simp [hmap.2.2]]
    exact hxs

theorem fid_cert_semEntails_large {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hinv : FullDenseInvW c F0 F_cur s)
    {wsort tmp : List (BitVec 32)} {nv unit sz r : Nat}
    (hr : r ∈ fullArenaClauseRefs s) (hgarb : fullArenaClauseGarb s r = false)
    (hsz : sz ≤ tmp.length)
    (hcov : ∀ q < fullArenaClauseSize s r,
      let ol := (s.core.arena[r + 3 + q]?.getD 0#32).toNat
      ol = unit ∨ s.core.vals[ol]?.getD 0#8 = 255#8 ∨
      ∃ j < sz, FidCertLitMap nv wsort (tmp[j]?.getD 0#32).toNat ol) :
    SemEntails (fidCertP F_cur wsort nv unit) ((tmp.take sz).map BitVec.toNat) := by
  intro β ⟨α, hsat, hu0, hu1, hβ⟩
  have hwf := hinv.2.1.arena.refs_wf r hr
  have hal_le := hinv.1.core_ok.arena_len_le
  have hlt_a := hinv.1.core_ok.arena_len_arr
  have hbd : r + 3 + fullArenaClauseSizeCore s.core r ≤ s.core.arena.length := by
    have := hwf.2.2.1; have := hwf.2.2.2.1; omega
  have hlt := hinv.2.1.arena.lits_lt r hr hgarb
  have hc := CNF.entails_clause_def.mp (hinv.2.1.arena.entails r hr hgarb) α hsat
  rcases (clause_sat_cnfClause_iff α _).mp hc with ⟨ol, hol_mem, hol_sat⟩
  rcases (mem_fullArenaClauseLitsCore_iff hbd).mp hol_mem with ⟨q, hq_sz, hget⟩
  have hq_lt : r + 3 + q < s.core.arena.length := by omega
  have hget' : s.core.arena[r + 3 + q]?.getD 0#32 = s.core.arena[r + 3 + q]'hq_lt := by
    rw [List.getElem?_eq_getElem hq_lt, Option.getD_some]
  have hol_eq : ol = (s.core.arena[r + 3 + q]?.getD 0#32).toNat := by rw [hget', hget]
  have hol_lt_cv : ol < 2 * s.core.cur_vars := hlt ol hol_mem
  rcases hcov q hq_sz with h_eq | h_255 | ⟨j, hj, hmap⟩
  · exfalso
    rw [← hol_eq] at h_eq; rw [h_eq] at hol_sat
    dsimp only [litVar, litSign] at hol_sat
    cases hm : (unit % 2 == 1)
    · have hm0 : unit % 2 = 0 := by
        have : ¬ (unit % 2 = 1) := by intro h; simp [h] at hm
        omega
      simp [hm, hu0 hm0] at hol_sat
    · simp [hm, hu1 (Nat.beq_eq.mp hm)] at hol_sat
  · exfalso
    rw [← hol_eq] at h_255
    have hf := CNF.entails_clause_def.mp
      (m6_lvl0_false_entails hinv.2.1 hinv.2.2.2.2.2.1 hol_lt_cv h_255) α hsat
    have hneg := (sat_cnfClause_litNeg_iff α ol).mp hf
    exact hneg ((sat_cnfClause_singleton α ol).mpr hol_sat)
  · rw [← hol_eq] at hmap
    refine (clause_sat_cnfClause_iff β _).mpr ⟨(tmp[j]?.getD 0#32).toNat, ?_, ?_⟩
    · have hj_t : j < (tmp.take sz).length := by rw [List.length_take_of_le hsz]; exact hj
      have hj_tmp : j < tmp.length := Nat.lt_of_lt_of_le hj hsz
      rw [List.getElem?_eq_getElem hj_tmp, Option.getD_some]
      refine List.mem_map.mpr ⟨tmp[j], List.mem_iff_getElem.mpr ⟨j, hj_t, ?_⟩, rfl⟩
      simp [List.getElem_take]
    · dsimp only [litVar, litSign] at hol_sat ⊢
      have hβ' := hβ ((tmp[j]?.getD 0#32).toNat / 2) hmap.1
      rw [hmap.2.1] at hβ'
      rw [hβ', show ((tmp[j]?.getD 0#32).toNat % 2 == 1) = (ol % 2 == 1) by simp [hmap.2.2]]
      exact hol_sat

theorem fid_cert_P_unsat_entails_unit {F_cur : List (List Nat)} {wsort : List (BitVec 32)}
    {nv unit : Nat} (hunsat : ∀ β, ¬ fidCertP F_cur wsort nv unit β) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause [unit]) := by
  rw [CNF.entails_clause_def]; intro α hsat
  by_cases hsu : α (litVar unit) = !litSign unit
  · exact (sat_cnfClause_singleton α unit).mpr hsu
  · exfalso
    dsimp only [litVar, litSign] at hsu
    have hu0 : unit % 2 = 0 → α (unit / 2) = false := fun h => by
      have hn : (unit % 2 == 1) = false := by simp [h]
      rw [hn] at hsu; exact Bool.eq_false_iff.mpr hsu
    have hu1 : unit % 2 = 1 → α (unit / 2) = true := fun h => by
      have hn : (unit % 2 == 1) = true := by simp [h]
      rw [hn] at hsu; cases hb : α (unit / 2) <;> simp_all
    exact hunsat (fun kv => α (wsort[kv]?.getD 0#32).toNat)
      ⟨α, hsat, hu0, hu1, fun _ _ => rfl⟩

/-! ## 3. Shared `tmk` Clear & Unit Commit Sub-Phases -/

@[expose] def fidCertTmkClearExpr (c : FullCfg) (nv : BitVec 32)
    (K_after : Expr Val Cont [Ty.bool]) : Expr Val Cont [Ty.bool] :=
  Expr.group (fun L : Tup Cont [[i32]] =>
    Blocks.cons (fun p : Tup Val [i32] =>
      Expr.let_ (Op.mk (OpCode.cmp .ult i32 .bool rfl) (Arg.var p.fst, Arg.var nv, ()))
        fun p_1 =>
      Expr.jnz (Arg.var p_1.fst)
        (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p.fst, ())) fun p_2 =>
         Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_2.fst, Arg.imm 4, ())) fun p_3 =>
         Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pWsort, Arg.var p_3.fst, ())) fun p_4 =>
         Expr.load i32 (Arg.var p_4.fst) fun wv =>
         Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var wv, ())) fun p_5 =>
         Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_5.fst, Arg.imm 4, ())) fun p_6 =>
         Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pTarjanMark, Arg.var p_6.fst, ()))
           fun p_7 =>
         Expr.store (t := i32) (Arg.imm 0) (Arg.var p_7.fst)
           (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var p.fst, Arg.imm 1, ())) fun p_8 =>
            Expr.jump L.fst (Arg.var p_8.fst, ())))
        K_after)
      Blocks.nil)
    fun L => Expr.jump L.fst (Arg.imm 0, ())

theorem fid_cert_tmk_clear_wp {Γ : Env} {Q : Post [Ty.bool]} {X : XPost}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64}
    {tmp wsort tmk gu scr : List (BitVec 32)} {nv : BitVec 32}
    {K_after : Expr Val Cont [Ty.bool]}
    (hinv : FullDenseInvW c F0 F_cur s)
    (hws : wsort.length = 2 * c.max_vars) (htm : tmk.length = 2 * c.max_vars)
    (hcv : nv.toNat ≤ s.core.cur_vars)
    (htreg : FidK6cTmkReg nv.toNat s.core.cur_vars wsort tmk)
    (hm : (FullMem c (FidP6Work (FidCertGu s gu) tmp wsort tmk scr) ⋆ R) m)
    (hK : ∀ tmk' : List (BitVec 32), ∀ m' : Mem 64,
      tmk'.length = 2 * c.max_vars →
      (∀ v, v < s.core.cur_vars → tmk'[v]?.getD 0#32 = 0#32) →
      (FullMem c (FidP6Work (FidCertGu s gu) tmp wsort tmk' scr) ⋆ R) m' →
      wp Γ Q X K_after m') :
    wp Γ Q X (fidCertTmkClearExpr c nv K_after) m := by
  have hcv_le : s.core.cur_vars ≤ c.max_vars := hinv.1.core_ok.cur_vars_le
  have hcv32 : nv.toNat < 2 ^ 31 := by
    have := c.hmaxv; simp only [dimacsBound] at this; omega
  refine wp_loop_group (ts := [i32])
    (fun rem (p : Tup Val [i32]) m1 => ∃ tmk1 : List (BitVec 32),
      p.fst.toNat ≤ nv.toNat ∧ rem = nv.toNat - p.fst.toNat ∧
      tmk1.length = 2 * c.max_vars ∧
      FidK6cTmkClearInv p.fst.toNat nv.toNat s.core.cur_vars wsort tmk1 ∧
      (FullMem c (FidP6Work (FidCertGu s gu) tmp wsort tmk1 scr) ⋆ R) m1)
    ?_ ?_
  · intro J n ⟨k, ⟨⟩⟩ m1 hcont ⟨tmk1, hk_le, hn, htm1, hcinv, hm1⟩
    dsimp only [Blocks.get, Member.here]
    c0_hsteps_nogrp
    · have hk_lt : k.toNat < nv.toNat := by bv_omega
      have hw_lt : (BitVec.setWidth 64 k).toNat < wsort.length := by
        rw [fid_zext32_toNat]; omega
      have hk_idx : (BitVec.setWidth 64 k).toNat = k.toNat := fid_zext32_toNat k
      have hw_info := hcinv.2.1 k.toNat (Nat.le_refl _) hk_lt
      have hw_v : (wsort[(BitVec.setWidth 64 k).toNat]).toNat < s.core.cur_vars := by
        have hwi := hw_info.1
        rw [List.getElem?_eq_getElem (i := k.toNat) (by omega), Option.getD_some] at hwi
        simpa [hk_idx] using hwi
      have htm_lt : (BitVec.setWidth 64 wsort[(BitVec.setWidth 64 k).toNat]).toNat <
          tmk1.length := by
        rw [fid_zext32_toNat]; omega
      have hk1 : (k + 1#32).toNat = k.toNat + 1 := fid_k6c_add1_toNat hk_lt (by omega)
      c0_hsteps
      have hcinv' : FidK6cTmkClearInv (k + 1#32).toNat nv.toNat s.core.cur_vars wsort
          (tmk1.set (BitVec.setWidth 64 wsort[(BitVec.setWidth 64 k).toNat]).toNat 0#32) := by
        have hwk_eq : (BitVec.setWidth 64 wsort[(BitVec.setWidth 64 k).toNat]).toNat =
            wsort[k.toNat].toNat := by
          rw [fid_zext32_toNat]; congr 2
        rw [hk1, hwk_eq]
        exact fid_k6c_tmkClear_step hcinv hk_lt (by omega) (by omega)
      exact hcont (nv.toNat - (k + 1#32).toNat) (k + 1#32, ()) _
        (by dsimp only at *; rw [hk1, hn]; omega)
        ⟨_, by dsimp only; rw [hk1]; omega, rfl, by simp [htm1], hcinv', hm⟩
    · have hk_eq : k.toNat = nv.toNat := by bv_omega
      exact hK tmk1 m1 htm1 (fid_k6c_tmkClear_done (hk_eq ▸ hcinv)) hm1
  · intro J hJ; c0_hsteps
    exact hJ nv.toNat _ _ ⟨tmk, Nat.zero_le _, rfl, htm, fid_k6c_tmkClear_init htreg, hm⟩

@[expose] def fidCertUnitCommitExpr (c : FullCfg) (unit : BitVec 32) :
    Expr Val Cont [Ty.bool] :=
  Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var unit, ())) fun p_1 =>
  Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pVals, Arg.var p_1.fst, ())) fun p_2 =>
  Expr.load i8 (Arg.var p_2.fst) fun uv =>
  Expr.group (fun _ : Tup Cont [[]] =>
    Blocks.cons (fun _ : Tup Val [] => Expr.ret (Arg.imm (t := Ty.bool) true, ())) Blocks.nil)
  fun Js_38 =>
  Expr.let_ (Op.mk (OpCode.trunc 32 8) (Arg.imm (t := i32) 0, ())) fun p_3 =>
  Expr.let_ (Op.mk (OpCode.sext 8 32) (Arg.var uv, ())) fun p_4 =>
  Expr.let_ (Op.mk (OpCode.sext 8 32) (Arg.var p_3.fst, ())) fun p_5 =>
  Expr.let_ (Op.mk (OpCode.cmp .slt i32 .bool rfl) (Arg.var p_4.fst, Arg.var p_5.fst, ()))
    fun p_6 =>
  Expr.jnz (Arg.var p_6.fst)
    (Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.hdr, Arg.imm 1024, ())) fun p_7 =>
     Expr.store (t := i64) (Arg.imm 1) (Arg.var p_7.fst) (Expr.jump Js_38.fst ()))
    (Expr.group (fun _ : Tup Cont [[]] =>
       Blocks.cons (fun _ : Tup Val [] => Expr.jump Js_38.fst ()) Blocks.nil)
     fun Js_242 =>
     Expr.let_ (Op.mk (OpCode.trunc 32 8) (Arg.imm (t := i32) 0, ())) fun p_7 =>
     Expr.let_ (Op.mk (OpCode.sext 8 32) (Arg.var uv, ())) fun p_8 =>
     Expr.let_ (Op.mk (OpCode.sext 8 32) (Arg.var p_7.fst, ())) fun p_9 =>
     Expr.let_ (Op.mk (OpCode.cmp .eq i32 .bool rfl) (Arg.var p_8.fst, Arg.var p_9.fst, ()))
       fun p_10 =>
     Expr.jnz (Arg.var p_10.fst)
       (Expr.call (as := [i64, i32, i32, i32]) (bs := []) "full_assign_lvl"
         (Arg.var c.hdr, Arg.var unit, Arg.imm 4294967295, Arg.imm 0, ())
         (fun _ => Expr.jump Js_242.fst ()))
       (Expr.jump Js_242.fst ()))

theorem fid_cert_unit_commit_wp {Γ : Env} {Q : Post [Ty.bool]} {X : XPost}
    (hAssign : Γ.Has "full_assign_lvl" fullAssignLvlSpec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s0 s_clr : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {unit : BitVec 32}
    (hinv : FullDenseInvW c F0 F_cur s_clr) (htmk : TmkZero s_clr)
    (hunit : unit.toNat < 2 * s_clr.core.cur_vars)
    (hcv_eq : s_clr.core.cur_vars = s0.core.cur_vars)
    (har_eq : s_clr.core.arena = s0.core.arena)
    (halen_eq : s_clr.core.arena_len = s0.core.arena_len)
    (hfuel : s_clr.core.fuel.toNat ≤ s0.core.fuel.toNat)
    (hpre : ∀ i, i < 4192 → s_clr.scratch.scratch_buf[i]? = s0.scratch.scratch_buf[i]?)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [unit.toNat]))
    (hm : (FullMem c s_clr ⋆ R) m)
    (hQ : ∀ (ok : Bool) (s' : FullState) (m' : Mem 64),
      FullDenseInvW c F0 F_cur s' → TmkZero s' →
      s'.core.cur_vars = s0.core.cur_vars → s'.core.arena = s0.core.arena →
      s'.core.arena_len = s0.core.arena_len → s'.core.fuel.toNat ≤ s0.core.fuel.toNat →
      (∀ i, i < 4192 → s'.scratch.scratch_buf[i]? = s0.scratch.scratch_buf[i]?) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    wp Γ Q X (fidCertUnitCommitExpr c unit) m := by
  have hu_vals : (BitVec.setWidth 64 unit).toNat < s_clr.core.vals.length := by
    have := hinv.1.core_ok.vals_len
    have := hinv.1.core_ok.cur_vars_le
    rw [fid_zext32_toNat]; omega
  have huv_get : s_clr.core.vals[(BitVec.setWidth 64 unit).toNat] =
      s_clr.core.vals[unit.toNat]?.getD 0#8 := by
    have hget := List.getElem?_eq_getElem (l := s_clr.core.vals) (i := unit.toNat)
      (by have := hinv.1.core_ok.vals_len; have := hinv.1.core_ok.cur_vars_le; omega)
    have hz : (BitVec.setWidth 64 unit).toNat = unit.toNat := fid_zext32_toNat unit
    simp only [hz, hget, Option.getD_some]
  have hdom : s_clr.core.vals[(BitVec.setWidth 64 unit).toNat] = 0#8 ∨
      s_clr.core.vals[(BitVec.setWidth 64 unit).toNat] = 1#8 ∨
      s_clr.core.vals[(BitVec.setWidth 64 unit).toNat] = 255#8 := by
    rw [huv_get]; exact hinv.2.1.vals_domain unit.toNat hunit
  dsimp only [fidCertUnitCommitExpr]
  c0_hsteps_nogrp
  apply wp_unroll_group; intro Js_38 hJs_38
  have hJ38 : ∀ s' m',
      FullDenseInvW c F0 F_cur s' → TmkZero s' →
      s'.core.cur_vars = s0.core.cur_vars → s'.core.arena = s0.core.arena →
      s'.core.arena_len = s0.core.arena_len → s'.core.fuel.toNat ≤ s0.core.fuel.toNat →
      (∀ i, i < 4192 → s'.scratch.scratch_buf[i]? = s0.scratch.scratch_buf[i]?) →
      (FullMem c s' ⋆ R) m' → Js_38 () m' := by
    intro s' m' hi ht hcv har hal hfl hpr hm'
    apply hJs_38; try dsimp only [Blocks.get, Member.here]
    c0_hsteps
    exact hQ true s' m' hi ht hcv har hal hfl hpr hm'
  clear hJs_38
  c0_hsteps_nogrp
  · have hv255 : s_clr.core.vals[(BitVec.setWidth 64 unit).toNat] = 255#8 :=
      (fid_cert_bv8_slt_iff hdom).mp hc
    have hvals255 : s_clr.core.vals[unit.toNat]?.getD 0#8 = 255#8 := by
      rw [← huv_get, hv255]
    have hunsat : (cnfOfClauses F_cur).Unsat :=
      m6_lvl0_unit_contra_unsat hinv.2.1 hinv.2.2.2.2.2.1 hunit hvals255 hent
    c0_hsteps
    refine hJ38 _ _ (m6_denseInvW_set_inconsistent hinv s_clr.core.confl_type
      s_clr.core.confl_lit0 s_clr.core.confl_lit1 s_clr.core.confl_ref hunsat)
      htmk hcv_eq har_eq halen_eq hfuel hpre ‹_›
  · apply wp_unroll_group; intro Js_242 hJs_242
    have hJ242 : ∀ s' m',
        FullDenseInvW c F0 F_cur s' → TmkZero s' →
        s'.core.cur_vars = s0.core.cur_vars → s'.core.arena = s0.core.arena →
        s'.core.arena_len = s0.core.arena_len → s'.core.fuel.toNat ≤ s0.core.fuel.toNat →
        (∀ i, i < 4192 → s'.scratch.scratch_buf[i]? = s0.scratch.scratch_buf[i]?) →
        (FullMem c s' ⋆ R) m' → Js_242 () m' := by
      intro s' m' hi ht hcv har hal hfl hpr hm'
      apply hJs_242; try dsimp only [Blocks.get, Member.here]
      c0_hsteps; exact hJ38 s' m' hi ht hcv har hal hfl hpr hm'
    clear hJs_242
    c0_hsteps_nogrp
    · have hv0 : s_clr.core.vals[(BitVec.setWidth 64 unit).toNat] = 0#8 :=
        (fid_cert_bv8_eq0_iff hdom).mp ‹_›
      have hvals0 : s_clr.core.vals[unit.toNat]?.getD 0#8 = 0#8 := by rw [← huv_get, hv0]
      have hte : s_clr.core.trail_end < c.max_vars :=
        fid_cert_trail_lt_of_unassigned hinv hunit hvals0
      apply wp_call_of_spec; apply hAssign
      refine ⟨c, s_clr, R, rfl, hinv.1, hm, ?_⟩
      have hcond : ¬ (s_clr.core.cur_vars ≤ unit.toNat / 2 ∨
          c.max_vars ≤ s_clr.core.trail_end ∨ s_clr.core.vals[unit.toNat]?.getD 0#8 ≠ 0#8) :=
        not_or.mpr ⟨not_le.mpr (by omega),
          not_or.mpr ⟨not_le.mpr hte, fun hne => hne hvals0⟩⟩
      dsimp only
      split
      · exact absurd ‹_› hcond
      intro flags' unass' phases' m' hfl hph hm'
      have hap := assignLvl0_preserves_denseInvW hinv hfl hph hunit hvals0 hent
        (unassigned' := unass') (unflushed' := s_clr.core.unflushed + 1#64)
      dsimp only at hap
      c0_hsteps
      exact hJ242 _ m' hap.1 htmk hcv_eq har_eq halen_eq hfuel hpre hm'
    · exact hJ242 s_clr m hinv htmk hcv_eq har_eq halen_eq hfuel hpre hm

/-! ## 4. Phase 1 Large Clause Loop (`@L853`) & Outer Scan Loop (`@L225`) -/

@[expose] def fidCertPhase1LargeExpr (c : FullCfg) (mv_s unit _v24 v227 : BitVec 32)
    (v228 : Bool) (w sz _v229 : BitVec 32)
    (L653 : Cont [i32, Ty.bool, Ty.bool, i32, i32]) : Expr Val Cont [Ty.bool] :=
  Expr.group (fun L853 : Tup Cont [[i32, i32, i32]] =>
    Blocks.cons (fun pl : Tup Val [i32, i32, i32] =>
      let v855 := pl.fst; let v856 := pl.snd.fst; let v857 := pl.snd.snd.fst
      Expr.let_ (Op.mk (OpCode.cmp .ult i32 .bool rfl) (Arg.var v857, Arg.var sz, ())) fun p_1 =>
      Expr.jnz (Arg.var p_1.fst)
        (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var w, ())) fun p_2 =>
         Expr.let_ (Op.mk (OpCode.add i64) (Arg.var p_2.fst, Arg.imm 3, ())) fun p_3 =>
         Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var v857, ())) fun p_4 =>
         Expr.let_ (Op.mk (OpCode.add i64) (Arg.var p_3.fst, Arg.var p_4.fst, ())) fun p_5 =>
         Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_5.fst, Arg.imm 4, ())) fun p_6 =>
         Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pArena, Arg.var p_6.fst, ())) fun p_7 =>
         Expr.load i32 (Arg.var p_7.fst) fun lit_k =>
         Expr.group (fun _ : Tup Cont [[i32, Ty.bool, Ty.bool, i32]] =>
           Blocks.cons (fun pl2 : Tup Val [i32, Ty.bool, Ty.bool, i32] =>
             Expr.let_ (Op.mk (OpCode.add i32) (Arg.var v857, Arg.imm 1, ())) fun k1 =>
             Expr.jump L853.fst (Arg.var pl2.fst, Arg.var pl2.snd.snd.snd.fst, Arg.var k1.fst, ()))
           Blocks.nil)
         fun Js_866 =>
         Expr.let_ (Op.mk (OpCode.cmp .ne i32 .bool rfl) (Arg.var lit_k, Arg.var unit, ()))
           fun p_8 =>
         Expr.jnz (Arg.var p_8.fst)
           (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var lit_k, ())) fun p_9 =>
            Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pVals, Arg.var p_9.fst, ())) fun p_10 =>
            Expr.load i8 (Arg.var p_10.fst) fun kv =>
            Expr.let_ (Op.mk (OpCode.trunc 32 8) (Arg.imm (t := i32) 0, ())) fun p_11 =>
            Expr.let_ (Op.mk (OpCode.sext 8 32) (Arg.var kv, ())) fun p_12 =>
            Expr.let_ (Op.mk (OpCode.sext 8 32) (Arg.var p_11.fst, ())) fun p_13 =>
            Expr.let_ (Op.mk (OpCode.cmp .sgt i32 .bool rfl)
              (Arg.var p_12.fst, Arg.var p_13.fst, ())) fun p_14 =>
            Expr.jnz (Arg.var p_14.fst)
              (Expr.jump L653 (Arg.var v855, Arg.imm v228, Arg.imm true,
                Arg.var v856, Arg.var v857, ()))
              (Expr.group (fun _ : Tup Cont [[i32, Ty.bool, i32]] =>
                 Blocks.cons (fun pl3 : Tup Val [i32, Ty.bool, i32] =>
                   Expr.jump Js_866.fst (Arg.var pl3.fst, Arg.var pl3.snd.fst,
                     Arg.imm (t := Ty.bool) false, Arg.var pl3.snd.snd.fst, ()))
                 Blocks.nil)
               fun Js_1074 =>
               Expr.let_ (Op.mk (OpCode.trunc 32 8) (Arg.imm (t := i32) 0, ())) fun p_15 =>
               Expr.let_ (Op.mk (OpCode.sext 8 32) (Arg.var kv, ())) fun p_16 =>
               Expr.let_ (Op.mk (OpCode.sext 8 32) (Arg.var p_15.fst, ())) fun p_17 =>
               Expr.let_ (Op.mk (OpCode.cmp .eq i32 .bool rfl)
                 (Arg.var p_16.fst, Arg.var p_17.fst, ())) fun p_18 =>
               Expr.jnz (Arg.var p_18.fst)
                 (Expr.let_ (Op.mk (OpCode.lshr i32) (Arg.var lit_k, Arg.imm 1, ())) fun lv =>
                  Expr.group (fun _ : Tup Cont [[i32, Ty.bool]] =>
                    Blocks.cons (fun pl4 : Tup Val [i32, Ty.bool] =>
                      Expr.let_ (Op.mk (OpCode.add i32) (Arg.var v856, Arg.imm 1, ())) fun u1 =>
                      Expr.jump Js_1074.fst
                        (Arg.var pl4.fst, Arg.var pl4.snd.fst, Arg.var u1.fst, ()))
                    Blocks.nil)
                  fun Js_1279 =>
                  Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var lv.fst, ())) fun pt1 =>
                  Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var pt1.fst, Arg.imm 4, ())) fun pt2 =>
                  Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pTarjanMark, Arg.var pt2.fst, ()))
                    fun pt3 =>
                  Expr.load i32 (Arg.var pt3.fst) fun tmkv =>
                  Expr.let_ (Op.mk (OpCode.cmp .eq i32 .bool rfl) (Arg.var tmkv, Arg.imm 0, ()))
                    fun p_19 =>
                  Expr.jnz (Arg.var p_19.fst)
                    (Expr.let_ (Op.mk (OpCode.cmp .uge i32 .bool rfl)
                       (Arg.var v855, Arg.var mv_s, ())) fun p_20 =>
                     Expr.jnz (Arg.var p_20.fst)
                       (Expr.jump L653 (Arg.var v855, Arg.imm true, Arg.imm false,
                         Arg.var v856, Arg.var v857, ()))
                       (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var v855, ())) fun pn1 =>
                        Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.hdr, Arg.imm 776, ()))
                          fun pn2 =>
                        Expr.load i64 (Arg.var pn2.fst) fun lcv =>
                        Expr.let_ (Op.mk (OpCode.cmp .uge i64 .bool rfl)
                          (Arg.var pn1.fst, Arg.var lcv, ())) fun pn3 =>
                        Expr.jnz (Arg.var pn3.fst)
                          (Expr.jump L653 (Arg.var v855, Arg.imm true, Arg.imm false,
                            Arg.var v856, Arg.var v857, ()))
                          (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var v855, ())) fun pw1 =>
                           Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var pw1.fst, Arg.imm 4, ()))
                             fun pw2 =>
                           Expr.let_ (Op.mk (OpCode.add i64)
                               (Arg.var c.pWsort, Arg.var pw2.fst, ()))
                             fun pw3 =>
                           Expr.store (t := i32) (Arg.var lv.fst) (Arg.var pw3.fst)
                             (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var v855, Arg.imm 1, ()))
                                fun nv1 =>
                              Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var lv.fst, ())) fun pm1 =>
                              Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var pm1.fst, Arg.imm 4, ()))
                                fun pm2 =>
                              Expr.let_ (Op.mk (OpCode.add i64)
                                (Arg.var c.pTarjanMark, Arg.var pm2.fst, ())) fun pm3 =>
                              Expr.store (t := i32) (Arg.var nv1.fst) (Arg.var pm3.fst)
                                (Expr.jump Js_1279.fst (Arg.var nv1.fst, Arg.imm v228, ()))))))
                    (Expr.jump Js_1279.fst (Arg.var v855, Arg.imm v228, ())))
                 (Expr.jump Js_1074.fst (Arg.var v855, Arg.imm v228, Arg.var v856, ()))))
           (Expr.jump Js_866.fst
             (Arg.var v855, Arg.imm v228, Arg.imm false, Arg.var v856, ())))
        (Expr.jump L653
          (Arg.var v855, Arg.imm v228, Arg.imm false, Arg.var v856, Arg.var v857, ())))
      Blocks.nil)
    fun L853 => Expr.jump L853.fst (Arg.var v227, Arg.imm 0, Arg.imm 0, ())

theorem fid_cert_phase1_large_wp {Γ : Env} {Q : Post [Ty.bool]} {X : XPost}
    {L653 : Cont [i32, Ty.bool, Ty.bool, i32, i32]}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s0 : FullState}
    {R : Mem 64 → Prop} {m : Mem 64}
    {tmp wsort tmk scr : List (BitVec 32)} {mv_s unit v24 nv_in : BitVec 32}
    {v228 : Bool} {w sz v229 : BitVec 32}
    (hinv : FullDenseInvW c F0 F_cur s0) (hv228 : v228 = false)
    (htp : tmp.length = c.max_vars) (hws : wsort.length = 2 * c.max_vars)
    (htm : tmk.length = 2 * c.max_vars) (_hscr : scr.length = c.scratch_cap)
    (hnv_mv : nv_in.toNat ≤ mv_s.toNat) (hnv_cv : nv_in.toNat ≤ s0.core.cur_vars)
    (hr : w.toNat ∈ fullArenaClauseRefs s0) (hgarb : fullArenaClauseGarb s0 w.toNat = false)
    (hsz : sz.toNat = fullArenaClauseSize s0 w.toNat)
    (htreg : FidK6cTmkReg nv_in.toNat s0.core.cur_vars wsort tmk)
    (hm : (FullMem c (FidP6Work s0 tmp wsort tmk scr) ⋆ R) m)
    (hL653 : ∀ (nv' u' k' : BitVec 32) (ab' sat' : Bool) (wsort' tmk' : List (BitVec 32))
      (m' : Mem 64),
      wsort'.length = 2 * c.max_vars → tmk'.length = 2 * c.max_vars →
      nv'.toNat ≤ mv_s.toNat → nv'.toNat ≤ s0.core.cur_vars →
      FidK6cTmkReg nv'.toNat s0.core.cur_vars wsort' tmk' →
      (ab' = false → sat' = false → u'.toNat = 0 →
        ∀ q < sz.toNat,
          let ol := (s0.core.arena[w.toNat + 3 + q]?.getD 0#32).toNat
          ol = unit.toNat ∨ s0.core.vals[ol]?.getD 0#8 = 255#8) →
      (FullMem c (FidP6Work s0 tmp wsort' tmk' scr) ⋆ R) m' →
      L653 (nv', ab', sat', u', k', ()) m') :
    wp Γ Q X (fidCertPhase1LargeExpr c mv_s unit v24 nv_in v228 w sz v229 L653) m := by
  subst hv228
  have hwf := hinv.2.1.arena.refs_wf w.toNat hr
  have hlits_lt := hinv.2.1.arena.lits_lt w.toNat hr hgarb
  have hal_le : s0.core.arena_len ≤ c.arena_cap := hinv.1.core_ok.arena_len_le
  have har_len : s0.core.arena.length = c.arena_cap := hinv.1.core_ok.arena_len_arr
  have har_lt : c.arena_cap < 2 * dimacsBound := c.harena
  have hw_rf := hwf.1
  have hw_sz := hwf.2.2.1
  have hw_nx := hwf.2.2.2.1
  have hsz_bd : sz.toNat ≤ c.arena_cap := by
    rw [hsz]; dsimp only [fullArenaClauseSize, fullArenaClauseSizeCore] at hw_sz ⊢; omega
  have hsz_end : w.toNat + 3 + sz.toNat ≤ s0.core.arena.length := by
    rw [hsz]; dsimp only [fullArenaClauseSize] at *; omega
  have hmax_lt : c.max_vars < 2 * dimacsBound := c.hmaxv
  have hcv_le : s0.core.cur_vars ≤ c.max_vars := hinv.1.core_ok.cur_vars_le
  have hw_lt28 : w.toNat < 2 ^ 30 := by
    dsimp only [fullArenaClauseSize, fullArenaClauseSizeCore] at hw_sz
    unfold dimacsBound at har_lt; omega
  refine wp_loop_group (ts := [i32, i32, i32])
    (fun rem pl m1 => ∃ wsort1 tmk1 : List (BitVec 32),
      let nv1 := pl.fst; let u1 := pl.snd.fst; let k1 := pl.snd.snd.fst
      k1.toNat ≤ sz.toNat ∧ u1.toNat ≤ k1.toNat ∧ rem = sz.toNat - k1.toNat ∧
      nv1.toNat ≤ mv_s.toNat ∧ nv1.toNat ≤ s0.core.cur_vars ∧
      wsort1.length = 2 * c.max_vars ∧ tmk1.length = 2 * c.max_vars ∧
      FidK6cTmkReg nv1.toNat s0.core.cur_vars wsort1 tmk1 ∧
      (u1.toNat = 0 → ∀ q < k1.toNat,
        let ol := (s0.core.arena[w.toNat + 3 + q]?.getD 0#32).toNat
        ol = unit.toNat ∨ s0.core.vals[ol]?.getD 0#8 = 255#8) ∧
      (FullMem c (FidP6Work s0 tmp wsort1 tmk1 scr) ⋆ R) m1)
    ?_ ?_
  · intro J n ⟨nv1, u1, k1, ⟨⟩⟩ m1 hcont
      ⟨wsort1, tmk1, hk_le, hu_le, hn, h1, h2, hws1, htm1, hreg1, hu0, hm1⟩
    dsimp only at hk_le hu_le hn h1 h2 hreg1 hm1
    dsimp only [Blocks.get, Member.here]
    c0_hsteps_nogrp
    · have hk_lt : k1.toNat < sz.toNat := by bv_omega
      have hk1_toNat : (k1 + 1#32).toNat = k1.toNat + 1 :=
        fid_k6c_add1_toNat hk_lt (by unfold dimacsBound at har_lt; omega)
      have ha_idx : (BitVec.setWidth 64 w + 3#64 + BitVec.setWidth 64 k1).toNat =
          w.toNat + 3 + k1.toNat := by
        rw [BitVec.toNat_add, BitVec.toNat_add, fid_zext32_toNat, fid_zext32_toNat]
        have : (3#64 : BitVec 64).toNat = 3 := rfl
        rw [this]; unfold dimacsBound at har_lt
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      have ha_mod : (w.toNat + BitVec.toNat (3 : BitVec 64) + k1.toNat) % 2 ^ 64 =
          (BitVec.setWidth 64 w + 3#64 + BitVec.setWidth 64 k1).toNat := by
        rw [ha_idx, show (BitVec.toNat (3 : BitVec 64)) = 3 from rfl]
        unfold dimacsBound at har_lt; rw [Nat.mod_eq_of_lt (by omega)]
      have ha_lt : (BitVec.setWidth 64 w + 3#64 + BitVec.setWidth 64 k1).toNat <
          s0.core.arena.length := by
        rw [ha_idx]; omega
      have hdrop_len : sz.toNat ≤ (s0.core.arena.drop (w.toNat + 3)).length := by
        rw [List.length_drop]; omega
      have hsz_core : sz.toNat = fullArenaClauseSizeCore s0.core w.toNat := hsz
      let lit_k := s0.core.arena[(BitVec.setWidth 64 w + 3#64 + BitVec.setWidth 64 k1).toNat]
      have hlit_mem : lit_k.toNat ∈ fullArenaClauseLits s0 w.toNat := by
        dsimp only [fullArenaClauseLits, fullArenaClauseLitsCore]
        refine List.mem_map.mpr ⟨lit_k, List.mem_iff_getElem.mpr ⟨k1.toNat, ?_, ?_⟩, rfl⟩
        · rw [List.length_take_of_le (by rw [← hsz_core]; exact hdrop_len), ← hsz_core]; exact hk_lt
        · simp [List.getElem_take, List.getElem_drop, lit_k, ha_idx]
      have hlit_lt : lit_k.toNat < 2 * s0.core.cur_vars := hlits_lt lit_k.toNat hlit_mem
      have hlit_get : s0.core.arena[w.toNat + 3 + k1.toNat]?.getD 0#32 = lit_k := by
        dsimp only [lit_k]
        rw [List.getElem?_eq_getElem (by rw [← ha_idx]; exact ha_lt), Option.getD_some]
        congr 1; exact ha_idx.symm
      c0_hsteps_nogrp
      apply wp_unroll_group; intro Js_866 hJs_866
      have hJ866 : ∀ (nv' u' : BitVec 32) (wsort' tmk' : List (BitVec 32)) (m' : Mem 64),
          wsort'.length = 2 * c.max_vars → tmk'.length = 2 * c.max_vars →
          nv'.toNat ≤ mv_s.toNat → nv'.toNat ≤ s0.core.cur_vars → u'.toNat ≤ k1.toNat + 1 →
          FidK6cTmkReg nv'.toNat s0.core.cur_vars wsort' tmk' →
          (u'.toNat = 0 → ∀ q < k1.toNat + 1,
            let ol := (s0.core.arena[w.toNat + 3 + q]?.getD 0#32).toNat
            ol = unit.toNat ∨ s0.core.vals[ol]?.getD 0#8 = 255#8) →
          (FullMem c (FidP6Work s0 tmp wsort' tmk' scr) ⋆ R) m' →
          ∀ (ab' : Bool), Js_866 (nv', false, ab', u', ()) m' := by
        intro nv' u' wsort' tmk' m' hw' ht' hn1 hn2 hu' hr' hu0' hm' ab'
        apply hJs_866; try dsimp only [Blocks.get, Member.here]
        c0_hsteps
        exact hcont (sz.toNat - (k1 + 1#32).toNat) (nv', u', k1 + 1#32, ()) m'
          (by dsimp only at *; rw [hk1_toNat, hn]; omega)
          ⟨wsort', tmk', by dsimp only; rw [hk1_toNat]; omega,
           by dsimp only; rw [hk1_toNat]; omega, rfl,
           hn1, hn2, hw', ht', hr', by simpa [hk1_toNat] using hu0', hm'⟩
      clear hJs_866
      c0_hsteps_nogrp
      · have hlit_ne := hc
        have hvals_lt : (BitVec.setWidth 64 lit_k).toNat < s0.core.vals.length := by
          rw [fid_zext32_toNat]; have := hinv.1.core_ok.vals_len; omega
        have hval_get : s0.core.vals[(BitVec.setWidth 64 lit_k).toNat] =
            s0.core.vals[lit_k.toNat]?.getD 0#8 := by
          have hget := List.getElem?_eq_getElem (l := s0.core.vals) (i := lit_k.toNat)
            (by have := hinv.1.core_ok.vals_len; omega)
          simp only [fid_zext32_toNat, hget, Option.getD_some]
        have hdom : s0.core.vals[(BitVec.setWidth 64 lit_k).toNat] = 0#8 ∨
            s0.core.vals[(BitVec.setWidth 64 lit_k).toNat] = 1#8 ∨
            s0.core.vals[(BitVec.setWidth 64 lit_k).toNat] = 255#8 := by
          rw [hval_get]; exact hinv.2.1.vals_domain lit_k.toNat hlit_lt
        c0_hsteps_nogrp
        · exact hL653 nv1 u1 k1 false true wsort1 tmk1 m1 hws1 htm1 h1 h2 hreg1
            (fun _ hs _ _ _ => False.elim (Bool.false_ne_true hs.symm)) hm1
        · have hkv_ngt := hc
          apply wp_unroll_group; intro Js_1074 hJs_1074
          have hJ1074 : ∀ (nv' u' : BitVec 32) (wsort' tmk' : List (BitVec 32)) (m' : Mem 64),
              wsort'.length = 2 * c.max_vars → tmk'.length = 2 * c.max_vars →
              nv'.toNat ≤ mv_s.toNat → nv'.toNat ≤ s0.core.cur_vars →
              u'.toNat ≤ k1.toNat + 1 →
              FidK6cTmkReg nv'.toNat s0.core.cur_vars wsort' tmk' →
              (u'.toNat = 0 → ∀ q < k1.toNat + 1,
                let ol := (s0.core.arena[w.toNat + 3 + q]?.getD 0#32).toNat
                ol = unit.toNat ∨ s0.core.vals[ol]?.getD 0#8 = 255#8) →
              (FullMem c (FidP6Work s0 tmp wsort' tmk' scr) ⋆ R) m' →
              Js_1074 (nv', false, u', ()) m' := by
            intro nv' u' wsort' tmk' m' hw' ht' hn1 hn2 hu' hr' hu0' hm'
            apply hJs_1074; try dsimp only [Blocks.get, Member.here]
            c0_hsteps; exact hJ866 nv' u' wsort' tmk' m' hw' ht' hn1 hn2 hu' hr' hu0' hm' false
          clear hJs_1074
          c0_hsteps_nogrp
          · have hu1_toNat : (u1 + 1#32).toNat = u1.toNat + 1 :=
              fid_k6c_add1_toNat (by omega : u1.toNat < sz.toNat)
                (by unfold dimacsBound at har_lt; omega)
            have hlv : (lit_k >>> 1).toNat = lit_k.toNat / 2 := by bv_omega
            have hlv_cv : (lit_k >>> 1).toNat < s0.core.cur_vars := by rw [hlv]; omega
            have htmk_lt : (BitVec.setWidth 64 (lit_k >>> 1)).toNat < tmk1.length := by
              rw [fid_zext32_toNat]; omega
            apply wp_unroll_group; intro Js_1279 hJs_1279
            have hJ1279 : ∀ (nv' : BitVec 32) (wsort' tmk' : List (BitVec 32)) (m' : Mem 64),
                wsort'.length = 2 * c.max_vars → tmk'.length = 2 * c.max_vars →
                nv'.toNat ≤ mv_s.toNat → nv'.toNat ≤ s0.core.cur_vars →
                FidK6cTmkReg nv'.toNat s0.core.cur_vars wsort' tmk' →
                (FullMem c (FidP6Work s0 tmp wsort' tmk' scr) ⋆ R) m' →
                Js_1279 (nv', false, ()) m' := by
              intro nv' wsort' tmk' m' hw' ht' hn1 hn2 hr' hm'
              apply hJs_1279; try dsimp only [Blocks.get, Member.here]
              c0_hsteps
              refine hJ1074 nv' (u1 + 1#32) wsort' tmk' m' hw' ht' hn1 hn2
                (by rw [hu1_toNat]; omega) hr' (fun hz => by rw [hu1_toNat] at hz; omega) hm'
            clear hJs_1279
            c0_hsteps_nogrp
            · exact hL653 nv1 u1 k1 true false wsort1 tmk1 m1 hws1 htm1 h1 h2 hreg1
                (fun ha _ _ _ _ => False.elim (Bool.false_ne_true ha.symm)) hm1
            · exact hL653 nv1 u1 k1 true false wsort1 tmk1 m1 hws1 htm1 h1 h2 hreg1
                (fun ha _ _ _ _ => False.elim (Bool.false_ne_true ha.symm)) hm1
            · rename_i htmk_raw hmv_ok
              have hcv_c := hc
              have hnv1_lt_mv : nv1.toNat < mv_s.toNat := by bv_omega
              have hnv1_lt_cv : nv1.toNat < s0.core.cur_vars := by
                unfold dimacsBound at hmax_lt; omega
              have hnv_toNat1 : (nv1 + 1#32).toNat = nv1.toNat + 1 :=
                fid_k6c_add1_toNat hnv1_lt_cv (by unfold dimacsBound at hmax_lt; omega)
              have hw1_lt : (BitVec.setWidth 64 nv1).toNat < wsort1.length := by
                rw [fid_zext32_toNat]; omega
              have hm1_lt : (BitVec.setWidth 64 (lit_k >>> 1)).toNat < tmk1.length := by
                rw [fid_zext32_toNat]; omega
              have htmk_z : tmk1[lit_k.toNat / 2]?.getD 0#32 = 0#32 := by
                have hlit_c0 : s0.core.arena[(w.toNat + BitVec.toNat (3 : BitVec 64) +
                    k1.toNat) % 2 ^ 64] = lit_k := by
                  dsimp only [lit_k]; congr 1
                simp only [hlit_c0] at htmk_raw
                rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                exact htmk_raw
              c0_hsteps
              have hstep := fid_k6c_tmkReg_step hreg1 (by omega : nv1.toNat < 2 * s0.core.cur_vars)
                hlv_cv htmk_z (Or.inr (by omega)) (by omega)
                (by unfold dimacsBound at hmax_lt; omega)
              have hbv1 : BitVec.ofNat 32 (lit_k >>> 1).toNat = lit_k >>> 1 := by
                apply BitVec.eq_of_toNat_eq
                rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (BitVec.isLt _)]
              have hbv2 : BitVec.ofNat 32 (nv1.toNat + 1) = nv1 + 1#32 := by
                apply BitVec.eq_of_toNat_eq
                rw [BitVec.toNat_ofNat,
                  Nat.mod_eq_of_lt (by unfold dimacsBound at hmax_lt; omega), hnv_toNat1]
              have hreg' : FidK6cTmkReg (nv1 + 1#32).toNat s0.core.cur_vars
                  (wsort1.set (BitVec.setWidth 64 nv1).toNat (lit_k >>> 1))
                  (tmk1.set (BitVec.setWidth 64 (lit_k >>> 1)).toNat (nv1 + 1#32)) := by
                rw [hnv_toNat1, fid_zext32_toNat, fid_zext32_toNat]
                rw [hbv1, hbv2] at hstep
                exact hstep
              exact hJ1279 (nv1 + 1#32) _ _ _ (by simp [hws1]) (by simp [htm1])
                (by rw [hnv_toNat1]; omega) (by rw [hnv_toNat1]; omega) hreg' ‹_›
            · exact hJ1279 nv1 wsort1 tmk1 m1 hws1 htm1 h1 h2 hreg1 hm1
          · have hkv_nz := hc
            have hlit_c0 : s0.core.arena[(w.toNat + BitVec.toNat (3 : BitVec 64) +
                k1.toNat) % 2 ^ 64] = lit_k := by
              dsimp only [lit_k]; congr 1
            simp only [hlit_c0] at hkv_ngt hkv_nz
            have hv_n0 : s0.core.vals[(BitVec.setWidth 64 lit_k).toNat] ≠ 0#8 := fun h => by
              simp only [fid_zext32_toNat] at h
              simp [h] at hkv_nz
            have hv_n1 : s0.core.vals[(BitVec.setWidth 64 lit_k).toNat] ≠ 1#8 := fun h => by
              have hs := (fid_cert_bv8_sgt_iff hdom).mpr h
              simp only [fid_zext32_toNat] at hs
              exact absurd (hs.symm.trans hkv_ngt) Bool.false_ne_true.symm
            have hv_255 : s0.core.vals[(BitVec.setWidth 64 lit_k).toNat] = 255#8 := by
              rcases hdom with h0 | h1v | h255
              · exact absurd h0 hv_n0
              · exact absurd h1v hv_n1
              · exact h255
            have hvals255 : s0.core.vals[lit_k.toNat]?.getD 0#8 = 255#8 := by
              rw [← hval_get, hv_255]
            refine hJ1074 nv1 u1 wsort1 tmk1 m1 hws1 htm1 h1 h2 (by omega) hreg1 ?_ hm1
            intro hu1_z q hq
            rcases Nat.lt_succ_iff_lt_or_eq.mp hq with hq' | rfl
            · exact hu0 hu1_z q hq'
            · exact Or.inr (by rw [hlit_get, hvals255])
      · have hlit_eq_raw := hc
        have hlit_eq : lit_k = unit := by
          have hlit_c0 : s0.core.arena[(w.toNat + BitVec.toNat (3 : BitVec 64) +
              k1.toNat) % 2 ^ 64] = lit_k := by
            dsimp only [lit_k]; congr 1
          rw [hlit_c0] at hlit_eq_raw
          bv_omega
        refine hJ866 nv1 u1 wsort1 tmk1 m1 hws1 htm1 h1 h2 (by omega) hreg1 ?_ hm1 false
        intro hu1_z q hq
        rcases Nat.lt_succ_iff_lt_or_eq.mp hq with hq' | rfl
        · exact hu0 hu1_z q hq'
        · exact Or.inl (by rw [hlit_get, hlit_eq])
    · have hk_eq : k1.toNat = sz.toNat := by bv_omega
      exact hL653 nv1 u1 k1 false false wsort1 tmk1 m1 hws1 htm1 h1 h2 hreg1
        (fun _ _ _ q hq => hu0 ‹_› q (by rw [hk_eq]; exact hq)) hm1
  · intro J hJ; c0_hsteps
    exact hJ sz.toNat _ _ ⟨wsort, tmk, Nat.zero_le _, Nat.zero_le _, rfl, hnv_mv, hnv_cv,
      hws, htm, htreg, fun _ _ hq => absurd hq (Nat.not_lt_zero _), hm⟩

@[expose] def fidCertPhase1Expr (c : FullCfg)
    (mv_s unit side_off side_cnt side_mask v24 : BitVec 32)
    (L25 : Cont [i32, Ty.bool, Ty.bool, i32]) : Expr Val Cont [Ty.bool] :=
  Expr.group (fun L225 : Tup Cont [[i32, Ty.bool, i32]] =>
    Blocks.cons (fun pl : Tup Val [i32, Ty.bool, i32] =>
      let v227 := pl.fst; let v228 := pl.snd.fst; let v229 := pl.snd.snd.fst
      Expr.let_ (Op.mk (OpCode.cmp .ult i32 .bool rfl) (Arg.var v229, Arg.var side_cnt, ()))
        fun p_1 =>
      Expr.jnz (Arg.var p_1.fst)
        (Expr.jnz (Arg.imm (t := Ty.bool) false)
          (Expr.jump L25 (Arg.var v227, Arg.imm false, Arg.var v228, Arg.var v229, ()))
          (Expr.jnz (Arg.var v228)
            (Expr.jump L25 (Arg.var v227, Arg.imm false, Arg.var v228, Arg.var v229, ()))
            (Expr.group (fun _ : Tup Cont [[i32, Ty.bool, Ty.bool]] =>
               Blocks.cons (fun pl1 : Tup Val [i32, Ty.bool, Ty.bool] =>
                 Expr.let_ (Op.mk (OpCode.add i32) (Arg.var v229, Arg.imm 1, ())) fun j1 =>
                 Expr.jump L225.fst (Arg.var pl1.fst, Arg.var pl1.snd.snd.fst, Arg.var j1.fst, ()))
               Blocks.nil)
             fun Js_231 =>
             Expr.let_ (Op.mk (OpCode.lshr i32) (Arg.var v229, Arg.imm 5, ())) fun p_2 =>
             Expr.let_ (Op.mk (OpCode.add i32) (Arg.var side_mask, Arg.var p_2.fst, ())) fun p_3 =>
             Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p_3.fst, ())) fun p_4 =>
             Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_4.fst, Arg.imm 4, ())) fun p_5 =>
             Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p_5.fst, ()))
               fun p_6 =>
             Expr.load i32 (Arg.var p_6.fst) fun ld =>
             Expr.let_ (Op.mk (OpCode.and i32) (Arg.var v229, Arg.imm 31, ())) fun p_7 =>
             Expr.let_ (Op.mk (OpCode.lshr i32) (Arg.var ld, Arg.var p_7.fst, ())) fun p_8 =>
             Expr.let_ (Op.mk (OpCode.and i32) (Arg.var p_8.fst, Arg.imm 1, ())) fun p_9 =>
             Expr.let_ (Op.mk (OpCode.cmp .ne i32 .bool rfl) (Arg.var p_9.fst, Arg.imm 0, ()))
               fun p_10 =>
             Expr.jnz (Arg.var p_10.fst)
               (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var side_off, Arg.var v229, ())) fun p_11 =>
                Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p_11.fst, ())) fun p_12 =>
                Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_12.fst, Arg.imm 4, ())) fun p_13 =>
                Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p_13.fst, ()))
                  fun p_14 =>
                Expr.load i32 (Arg.var p_14.fst) fun w =>
                Expr.group (fun _ : Tup Cont [[i32, Ty.bool, Ty.bool]] =>
                  Blocks.cons (fun pl2 : Tup Val [i32, Ty.bool, Ty.bool] =>
                    Expr.jump Js_231.fst
                      (Arg.var pl2.fst, Arg.var pl2.snd.fst, Arg.var pl2.snd.snd.fst, ()))
                  Blocks.nil)
                fun Js_446 =>
                Expr.let_ (Op.mk (OpCode.and i32) (Arg.var w, Arg.imm 2147483648, ())) fun p_15 =>
                Expr.let_ (Op.mk (OpCode.cmp .ne i32 .bool rfl)
                  (Arg.var p_15.fst, Arg.imm 0, ())) fun p_16 =>
                Expr.jnz (Arg.var p_16.fst)
                  (Expr.let_ (Op.mk (OpCode.and i32) (Arg.var w, Arg.imm 2147483647, ())) fun bl =>
                   Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var bl.fst, ())) fun p_17 =>
                   Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pVals, Arg.var p_17.fst, ()))
                     fun p_18 =>
                   Expr.load i8 (Arg.var p_18.fst) fun bv =>
                   Expr.let_ (Op.mk (OpCode.trunc 32 8) (Arg.imm (t := i32) 0, ())) fun p_19 =>
                   Expr.let_ (Op.mk (OpCode.sext 8 32) (Arg.var bv, ())) fun p_20 =>
                   Expr.let_ (Op.mk (OpCode.sext 8 32) (Arg.var p_19.fst, ())) fun p_21 =>
                   Expr.let_ (Op.mk (OpCode.cmp .slt i32 .bool rfl)
                     (Arg.var p_20.fst, Arg.var p_21.fst, ())) fun p_22 =>
                   Expr.jnz (Arg.var p_22.fst)
                     (Expr.jump L25 (Arg.var v227, Arg.imm true, Arg.var v228, Arg.var v229, ()))
                     (Expr.group (fun _ : Tup Cont [[i32, Ty.bool]] =>
                        Blocks.cons (fun pl3 : Tup Val [i32, Ty.bool] =>
                          Expr.jump Js_446.fst
                            (Arg.var pl3.fst, Arg.imm false, Arg.var pl3.snd.fst, ()))
                        Blocks.nil)
                      fun Js_656 =>
                      Expr.let_ (Op.mk (OpCode.trunc 32 8) (Arg.imm (t := i32) 0, ())) fun p_23 =>
                      Expr.let_ (Op.mk (OpCode.sext 8 32) (Arg.var bv, ())) fun p_24 =>
                      Expr.let_ (Op.mk (OpCode.sext 8 32) (Arg.var p_23.fst, ())) fun p_25 =>
                      Expr.let_ (Op.mk (OpCode.cmp .eq i32 .bool rfl)
                        (Arg.var p_24.fst, Arg.var p_25.fst, ())) fun p_26 =>
                      Expr.jnz (Arg.var p_26.fst)
                        (Expr.let_ (Op.mk (OpCode.lshr i32) (Arg.var bl.fst, Arg.imm 1, ()))
                           fun lv =>
                         Expr.group (fun _ : Tup Cont [[i32, Ty.bool]] =>
                           Blocks.cons (fun pl4 : Tup Val [i32, Ty.bool] =>
                             Expr.jump Js_656.fst (Arg.var pl4.fst, Arg.var pl4.snd.fst, ()))
                           Blocks.nil)
                         fun Js_861 =>
                         Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var lv.fst, ())) fun pt1 =>
                         Expr.let_ (Op.mk (OpCode.mul i64)
                           (Arg.var pt1.fst, Arg.imm 4, ())) fun pt2 =>
                         Expr.let_ (Op.mk (OpCode.add i64)
                           (Arg.var c.pTarjanMark, Arg.var pt2.fst, ())) fun pt3 =>
                         Expr.load i32 (Arg.var pt3.fst) fun tmkv =>
                         Expr.let_ (Op.mk (OpCode.cmp .eq i32 .bool rfl)
                           (Arg.var tmkv, Arg.imm 0, ())) fun p_27 =>
                         Expr.jnz (Arg.var p_27.fst)
                           (Expr.let_ (Op.mk (OpCode.cmp .uge i32 .bool rfl)
                              (Arg.var v227, Arg.var mv_s, ())) fun p_28 =>
                            Expr.jnz (Arg.var p_28.fst)
                              (Expr.jump L25 (Arg.var v227, Arg.imm false,
                                Arg.imm true, Arg.var v229, ()))
                              (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var v227, ())) fun pn1 =>
                               Expr.let_ (Op.mk (OpCode.add i64)
                                 (Arg.var c.hdr, Arg.imm 776, ())) fun pn2 =>
                               Expr.load i64 (Arg.var pn2.fst) fun lcv =>
                               Expr.let_ (Op.mk (OpCode.cmp .uge i64 .bool rfl)
                                 (Arg.var pn1.fst, Arg.var lcv, ())) fun pn3 =>
                               Expr.jnz (Arg.var pn3.fst)
                                 (Expr.jump L25 (Arg.var v227, Arg.imm false,
                                   Arg.imm true, Arg.var v229, ()))
                                 (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var v227, ()))
                                    fun pw1 =>
                                  Expr.let_ (Op.mk (OpCode.mul i64)
                                    (Arg.var pw1.fst, Arg.imm 4, ())) fun pw2 =>
                                  Expr.let_ (Op.mk (OpCode.add i64)
                                    (Arg.var c.pWsort, Arg.var pw2.fst, ())) fun pw3 =>
                                  Expr.store (t := i32) (Arg.var lv.fst) (Arg.var pw3.fst)
                                    (Expr.let_ (Op.mk (OpCode.add i32)
                                       (Arg.var v227, Arg.imm 1, ())) fun nv1 =>
                                     Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var lv.fst, ()))
                                       fun pm1 =>
                                     Expr.let_ (Op.mk (OpCode.mul i64)
                                       (Arg.var pm1.fst, Arg.imm 4, ())) fun pm2 =>
                                     Expr.let_ (Op.mk (OpCode.add i64)
                                       (Arg.var c.pTarjanMark, Arg.var pm2.fst, ())) fun pm3 =>
                                     Expr.store (t := i32) (Arg.var nv1.fst) (Arg.var pm3.fst)
                                       (Expr.jump Js_861.fst
                                         (Arg.var nv1.fst, Arg.var v228, ()))))))
                           (Expr.jump Js_861.fst (Arg.var v227, Arg.var v228, ())))
                        (Expr.jump Js_656.fst (Arg.var v227, Arg.var v228, ()))))
                  (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var w, ())) fun p_17 =>
                   Expr.let_ (Op.mk (OpCode.add i64) (Arg.var p_17.fst, Arg.imm 2, ())) fun p_18 =>
                   Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_18.fst, Arg.imm 4, ())) fun p_19 =>
                   Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pArena, Arg.var p_19.fst, ()))
                     fun p_20 =>
                   Expr.load i32 (Arg.var p_20.fst) fun sz =>
                   Expr.group (fun _ : Tup Cont [[i32, Ty.bool, Ty.bool, i32, i32]] =>
                     Blocks.cons (fun p653 : Tup Val [i32, Ty.bool, Ty.bool, i32, i32] =>
                       Expr.jnz (Arg.var p653.snd.fst)
                         (Expr.jump L25 (Arg.var p653.fst, Arg.imm false,
                           Arg.var p653.snd.fst, Arg.var v229, ()))
                         (Expr.group (fun _ : Tup Cont [[Ty.bool, Ty.bool]] =>
                            Blocks.cons (fun p660 : Tup Val [Ty.bool, Ty.bool] =>
                              Expr.jump Js_446.fst
                                (Arg.var p653.fst, Arg.var p660.fst, Arg.var p660.snd.fst, ()))
                            Blocks.nil)
                          fun Js_660 =>
                          Expr.jnz (Arg.var p653.snd.snd.fst)
                            (Expr.jump Js_660.fst (Arg.imm false, Arg.var p653.snd.fst, ()))
                            (Expr.let_ (Op.mk (OpCode.cmp .eq i32 .bool rfl)
                               (Arg.var p653.snd.snd.snd.fst, Arg.imm 0, ())) fun p_21 =>
                             Expr.jnz (Arg.var p_21.fst)
                               (Expr.jump L25 (Arg.var p653.fst, Arg.imm true,
                                 Arg.var p653.snd.fst, Arg.var v229, ()))
                               (Expr.let_ (Op.mk (OpCode.cmp .ugt i32 .bool rfl)
                                  (Arg.var p653.snd.snd.snd.fst, Arg.var v24, ())) fun p_22 =>
                                Expr.jnz (Arg.var p_22.fst)
                                  (Expr.jump L25 (Arg.var p653.fst, Arg.imm false,
                                    Arg.imm true, Arg.var v229, ()))
                                  (Expr.jump Js_660.fst
                                    (Arg.imm false, Arg.var p653.snd.fst, ()))))))
                     Blocks.nil)
                   fun L653 =>
                   fidCertPhase1LargeExpr c mv_s unit v24 v227 v228 w sz v229 L653.fst))
               (Expr.jump Js_231.fst (Arg.var v227, Arg.imm false, Arg.var v228, ())))))
        (Expr.jump L25 (Arg.var v227, Arg.imm false, Arg.var v228, Arg.var v229, ())))
      Blocks.nil)
    fun L225 => Expr.jump L225.fst (Arg.imm 0, Arg.imm false, Arg.imm 0, ())

theorem fid_cert_phase1_wp {Γ : Env} {Q : Post [Ty.bool]} {X : XPost}
    {L25 : Cont [i32, Ty.bool, Ty.bool, i32]}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s0 : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {mv_s unit side_off side_cnt side_mask v24 : BitVec 32}
    (hinv : FullDenseInvW c F0 F_cur s0)
    (hscr : s0.scratch.scratch_buf.length = c.scratch_cap)
    (h16k : 16384 ≤ c.scratch_cap) (hunit : unit.toNat < 2 * s0.core.cur_vars)
    (hcnt : side_cnt.toNat ≤ 2001) (hoff : side_off.toNat + side_cnt.toNat ≤ 4002)
    (hmask : side_mask = 4002#32 ∨ side_mask = 4066#32)
    (hent : ∀ i < side_cnt.toNat,
      FullBveEntryOkW F_cur s0 unit.toNat (s0.scratch.scratch_buf[side_off.toNat + i]?.getD 0#32))
    (htmk0 : TmkZero s0)
    (hm : (FullMem c s0 ⋆ R) m)
    (hL25 : ∀ (nv' j' : BitVec 32) (ok' ab' : Bool) (tmp' wsort' tmk' : List (BitVec 32))
      (m' : Mem 64),
      tmp'.length = c.max_vars → wsort'.length = 2 * c.max_vars →
      tmk'.length = 2 * c.max_vars →
      nv'.toNat ≤ mv_s.toNat → nv'.toNat ≤ s0.core.cur_vars →
      FidK6cTmkReg nv'.toNat s0.core.cur_vars wsort' tmk' →
      (ok' = true → (cnfOfClauses F_cur).EntailsClause (cnfClause [unit.toNat])) →
      (FullMem c (FidP6Work s0 tmp' wsort' tmk' s0.scratch.scratch_buf) ⋆ R) m' →
      L25 (nv', ok', ab', j', ()) m') :
    wp Γ Q X (fidCertPhase1Expr c mv_s unit side_off side_cnt side_mask v24 L25) m := by
  have hmax_lt : c.max_vars < 2 * dimacsBound := c.hmaxv
  have hcv_le : s0.core.cur_vars ≤ c.max_vars := hinv.1.core_ok.cur_vars_le
  have har_lt : c.arena_cap < 2 * dimacsBound := c.harena
  have hal_le : s0.core.arena_len ≤ c.arena_cap := hinv.1.core_ok.arena_len_le
  have har_len : s0.core.arena.length = c.arena_cap := hinv.1.core_ok.arena_len_arr
  have htp0 := hinv.1.core_ok.tmp_len_arr
  have hws0 := hinv.1.scratch_ok.wsort_len
  have htm0 := hinv.1.scratch_ok.tarjan_mark_len
  refine wp_loop_group (ts := [i32, Ty.bool, i32])
    (fun rem pl m1 => ∃ wsort1 tmk1 : List (BitVec 32),
      let nv1 := pl.fst; let ab1 := pl.snd.fst; let j1 := pl.snd.snd.fst
      j1.toNat ≤ side_cnt.toNat ∧ rem = side_cnt.toNat - j1.toNat ∧
      nv1.toNat ≤ mv_s.toNat ∧ nv1.toNat ≤ s0.core.cur_vars ∧
      wsort1.length = 2 * c.max_vars ∧ tmk1.length = 2 * c.max_vars ∧
      FidK6cTmkReg nv1.toNat s0.core.cur_vars wsort1 tmk1 ∧
      (FullMem c (FidP6Work s0 s0.core.tmp wsort1 tmk1 s0.scratch.scratch_buf) ⋆ R) m1)
    ?_ ?_
  · intro J n ⟨nv1, ab1, j1, ⟨⟩⟩ m1 hcont
      ⟨wsort1, tmk1, hj_le, hn, h1, h2, hws1, htm1, hreg1, hm1⟩
    dsimp only at hj_le hn h1 h2 hreg1 hm1
    dsimp only [Blocks.get, Member.here]
    c0_hsteps_nogrp
    · exact hL25 nv1 j1 false ab1 s0.core.tmp wsort1 tmk1 m1
        htp0 hws1 htm1 h1 h2 hreg1 (fun h => absurd h Bool.false_ne_true) hm1
    · have h_not_v228 := hc
      have hj_lt : j1.toNat < side_cnt.toNat := by bv_omega
      have hj1 : (j1 + 1#32).toNat = j1.toNat + 1 := fid_k6c_add1_toNat hj_lt (by omega)
      apply wp_unroll_group; intro Js_231 hJs_231
      have hJ231 : ∀ (nv' : BitVec 32) (ab' : Bool) (wsort' tmk' : List (BitVec 32))
          (m' : Mem 64),
          wsort'.length = 2 * c.max_vars → tmk'.length = 2 * c.max_vars →
          nv'.toNat ≤ mv_s.toNat → nv'.toNat ≤ s0.core.cur_vars →
          FidK6cTmkReg nv'.toNat s0.core.cur_vars wsort' tmk' →
          (FullMem c (FidP6Work s0 s0.core.tmp wsort' tmk' s0.scratch.scratch_buf) ⋆ R) m' →
          ∀ fl', Js_231 (nv', fl', ab', ()) m' := by
        intro nv' ab' wsort' tmk' m' hw' ht' hn1 hn2 hr' hm' fl'
        apply hJs_231; try dsimp only [Blocks.get, Member.here]
        c0_hsteps
        exact hcont (side_cnt.toNat - (j1 + 1#32).toNat) (nv', ab', j1 + 1#32, ()) m'
          (by dsimp only at *; rw [hj1, hn]; omega)
          ⟨wsort', tmk', by dsimp only; rw [hj1]; omega, rfl,
           hn1, hn2, hw', ht', hr', hm'⟩
      clear hJs_231
      have hm_idx := fid_k6c_mask_widx hmask (by omega : j1.toNat < 2001)
      have hscr_m : (BitVec.setWidth 64 (side_mask + (j1 >>> 5))).toNat <
          s0.scratch.scratch_buf.length := by
        rw [fid_zext32_toNat]; omega
      c0_hsteps_nogrp
      · have hoff_idx : (BitVec.setWidth 64 (side_off + j1)).toNat =
            side_off.toNat + j1.toNat := by
          rw [fid_zext32_toNat, BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
        have hscr_o : (BitVec.setWidth 64 (side_off + j1)).toNat <
            s0.scratch.scratch_buf.length := by
          rw [hoff_idx]; omega
        c0_hsteps_nogrp
        apply wp_unroll_group; intro Js_446 hJs_446
        have hJ446 : ∀ (nv' : BitVec 32) (ab' : Bool) (wsort' tmk' : List (BitVec 32))
            (m' : Mem 64),
            wsort'.length = 2 * c.max_vars → tmk'.length = 2 * c.max_vars →
            nv'.toNat ≤ mv_s.toNat → nv'.toNat ≤ s0.core.cur_vars →
            FidK6cTmkReg nv'.toNat s0.core.cur_vars wsort' tmk' →
            (FullMem c (FidP6Work s0 s0.core.tmp wsort' tmk' s0.scratch.scratch_buf) ⋆ R) m' →
            ∀ fl', Js_446 (nv', fl', ab', ()) m' := by
          intro nv' ab' wsort' tmk' m' hw' ht' hn1 hn2 hr' hm' fl'
          apply hJs_446; try dsimp only [Blocks.get, Member.here]
          c0_hsteps; exact hJ231 nv' ab' wsort' tmk' m' hw' ht' hn1 hn2 hr' hm' fl'
        clear hJs_446
        let w := s0.scratch.scratch_buf[(BitVec.setWidth 64 (side_off + j1)).toNat]
        have hw_c0 : s0.scratch.scratch_buf[(side_off.toNat + BitVec.toNat j1) % 4294967296] =
            w := by
          dsimp only [w]; congr 1
        have hw_eq : s0.scratch.scratch_buf[side_off.toNat + j1.toNat]?.getD 0#32 = w := by
          dsimp only [w]
          rw [← hoff_idx, List.getElem?_eq_getElem hscr_o, Option.getD_some]
        have hent_w := hent j1.toNat hj_lt
        rw [hw_eq] at hent_w
        have hab_false : ab1 = false := by
          cases ab1 with
          | false => rfl
          | true => exact absurd h_not_v228 Bool.noConfusion
        c0_hsteps_nogrp
        · have hw_bin := hc
          rw [hw_c0] at hw_bin
          dsimp only [FullBveEntryOkW] at hent_w
          rw [ite_eq_left (by simpa using hw_bin)] at hent_w
          have hbl_lt : (w &&& 2147483647#32).toNat < 2 * s0.core.cur_vars := hent_w.1
          let bl := w &&& 2147483647#32
          have hbl_lt' : bl.toNat < 2 * s0.core.cur_vars := hbl_lt
          have hvals_lt : (BitVec.setWidth 64 bl).toNat < s0.core.vals.length := by
            rw [fid_zext32_toNat]; have := hinv.1.core_ok.vals_len; omega
          have hval_get : s0.core.vals[(BitVec.setWidth 64 bl).toNat] =
              s0.core.vals[bl.toNat]?.getD 0#8 := by
            have hget := List.getElem?_eq_getElem (l := s0.core.vals) (i := bl.toNat)
              (by have := hinv.1.core_ok.vals_len; omega)
            simp only [fid_zext32_toNat, hget, Option.getD_some]
          have hdom : s0.core.vals[(BitVec.setWidth 64 bl).toNat] = 0#8 ∨
              s0.core.vals[(BitVec.setWidth 64 bl).toNat] = 1#8 ∨
              s0.core.vals[(BitVec.setWidth 64 bl).toNat] = 255#8 := by
            rw [hval_get]; exact hinv.2.1.vals_domain bl.toNat hent_w.1
          c0_hsteps_nogrp
          · have hw_slt := hc
            have hv255 : s0.core.vals[(BitVec.setWidth 64 bl).toNat] = 255#8 :=
              (fid_cert_bv8_slt_iff hdom).mp hw_slt
            have hvals255 : s0.core.vals[bl.toNat]?.getD 0#8 = 255#8 := by
              rw [← hval_get, hv255]
            have hbot := m6_lvl0_false_entails hinv.2.1 hinv.2.2.2.2.2.1 hent_w.1 hvals255
            have he_u := fid_cert_entails_resolve_bin hent_w.2 hbot
            exact hL25 nv1 j1 true ab1 s0.core.tmp wsort1 tmk1 m1
              htp0 hws1 htm1 h1 h2 hreg1 (fun _ => he_u) hm1
          · apply wp_unroll_group; intro Js_656 hJs_656
            have hJ656 : ∀ (nv' : BitVec 32) (ab' : Bool) (wsort' tmk' : List (BitVec 32))
                (m' : Mem 64),
                wsort'.length = 2 * c.max_vars → tmk'.length = 2 * c.max_vars →
                nv'.toNat ≤ mv_s.toNat → nv'.toNat ≤ s0.core.cur_vars →
                FidK6cTmkReg nv'.toNat s0.core.cur_vars wsort' tmk' →
                (FullMem c (FidP6Work s0 s0.core.tmp wsort' tmk' s0.scratch.scratch_buf) ⋆ R)
                  m' →
                Js_656 (nv', ab', ()) m' := by
              intro nv' ab' wsort' tmk' m' hw' ht' hn1 hn2 hr' hm'
              apply hJs_656; try dsimp only [Blocks.get, Member.here]
              c0_hsteps; exact hJ446 nv' ab' wsort' tmk' m' hw' ht' hn1 hn2 hr' hm' false
            clear hJs_656
            c0_hsteps_nogrp
            · have hlv : (bl >>> 1).toNat = bl.toNat / 2 := by bv_omega
              have hlv_cv : (bl >>> 1).toNat < s0.core.cur_vars := by rw [hlv]; omega
              have htmk_lt : (BitVec.setWidth 64 (bl >>> 1)).toNat < tmk1.length := by
                rw [fid_zext32_toNat]; omega
              apply wp_unroll_group; intro Js_861 hJs_861
              have hJ861 : ∀ (nv' : BitVec 32) (ab' : Bool) (wsort' tmk' : List (BitVec 32))
                  (m' : Mem 64),
                  wsort'.length = 2 * c.max_vars → tmk'.length = 2 * c.max_vars →
                  nv'.toNat ≤ mv_s.toNat → nv'.toNat ≤ s0.core.cur_vars →
                  FidK6cTmkReg nv'.toNat s0.core.cur_vars wsort' tmk' →
                  (FullMem c (FidP6Work s0 s0.core.tmp wsort' tmk' s0.scratch.scratch_buf) ⋆ R)
                    m' →
                  Js_861 (nv', ab', ()) m' := by
                intro nv' ab' wsort' tmk' m' hw' ht' hn1 hn2 hr' hm'
                apply hJs_861; try dsimp only [Blocks.get, Member.here]
                c0_hsteps; exact hJ656 nv' ab' wsort' tmk' m' hw' ht' hn1 hn2 hr' hm'
              clear hJs_861
              c0_hsteps_nogrp
              · exact hL25 nv1 j1 false true s0.core.tmp wsort1 tmk1 m1
                  htp0 hws1 htm1 h1 h2 hreg1 (fun h => absurd h Bool.false_ne_true) hm1
              · exact hL25 nv1 j1 false true s0.core.tmp wsort1 tmk1 m1
                  htp0 hws1 htm1 h1 h2 hreg1 (fun h => absurd h Bool.false_ne_true) hm1
              · have hcv_c := hc
                have hnv1_lt_mv : nv1.toNat < mv_s.toNat := by bv_omega
                have hnv1_lt_cv : nv1.toNat < s0.core.cur_vars := by
                  unfold dimacsBound at hmax_lt; omega
                have hnv_toNat1 : (nv1 + 1#32).toNat = nv1.toNat + 1 :=
                  fid_k6c_add1_toNat hnv1_lt_cv (by unfold dimacsBound at hmax_lt; omega)
                have hw1_lt : (BitVec.setWidth 64 nv1).toNat < wsort1.length := by
                  rw [fid_zext32_toNat]; omega
                have hm1_lt : (BitVec.setWidth 64 (bl >>> 1)).toNat < tmk1.length := by
                  rw [fid_zext32_toNat]; omega
                have htmk_z : tmk1[bl.toNat / 2]?.getD 0#32 = 0#32 := by
                  have htmk_raw : tmk1[(BitVec.setWidth 64 (bl >>> 1)).toNat] = 0#32 := by
                    assumption
                  have hidx : (BitVec.setWidth 64 (bl >>> 1)).toNat = bl.toNat / 2 := by
                    rw [fid_zext32_toNat]; exact hlv
                  have heq : tmk1[bl.toNat / 2]'(by omega) =
                      tmk1[(BitVec.setWidth 64 (bl >>> 1)).toNat] := by congr 1
                  rw [List.getElem?_eq_getElem (by omega), Option.getD_some, heq]
                  exact htmk_raw
                c0_hsteps
                have hstep := fid_k6c_tmkReg_step hreg1
                  (by omega : nv1.toNat < 2 * s0.core.cur_vars)
                  hlv_cv htmk_z (Or.inr (by omega)) (by omega)
                  (by unfold dimacsBound at hmax_lt; omega)
                have hbv1 : BitVec.ofNat 32 (bl >>> 1).toNat = bl >>> 1 := by
                  apply BitVec.eq_of_toNat_eq
                  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (BitVec.isLt _)]
                have hbv2 : BitVec.ofNat 32 (nv1.toNat + 1) = nv1 + 1#32 := by
                  apply BitVec.eq_of_toNat_eq
                  rw [BitVec.toNat_ofNat,
                    Nat.mod_eq_of_lt (by unfold dimacsBound at hmax_lt; omega), hnv_toNat1]
                have hreg' : FidK6cTmkReg (nv1 + 1#32).toNat s0.core.cur_vars
                    (wsort1.set (BitVec.setWidth 64 nv1).toNat (bl >>> 1))
                    (tmk1.set (BitVec.setWidth 64 (bl >>> 1)).toNat (nv1 + 1#32)) := by
                  rw [hnv_toNat1, fid_zext32_toNat, fid_zext32_toNat]
                  rw [hbv1, hbv2] at hstep
                  exact hstep
                exact hJ861 (nv1 + 1#32) ab1 _ _ _ (by simp [hws1]) (by simp [htm1])
                  (by rw [hnv_toNat1]; omega) (by rw [hnv_toNat1]; omega) hreg' ‹_›
              · exact hJ861 nv1 ab1 wsort1 tmk1 m1 hws1 htm1 h1 h2 hreg1 hm1
            · exact hJ656 nv1 ab1 wsort1 tmk1 m1 hws1 htm1 h1 h2 hreg1 hm1
        · have hw_nbin := hc
          rw [hw_c0] at hw_nbin
          dsimp only [FullBveEntryOkW] at hent_w
          rw [ite_eq_right (by simpa using hw_nbin)] at hent_w
          have hwf := hinv.2.1.arena.refs_wf w.toNat hent_w.1
          have har_idx : (BitVec.setWidth 64 w + 2#64).toNat = w.toNat + 2 := by
            rw [BitVec.toNat_add, fid_zext32_toNat, show (2#64 : BitVec 64).toNat = 2 from rfl]
            unfold dimacsBound at har_lt; rw [Nat.mod_eq_of_lt (by omega)]
          have har2_lt : (BitVec.setWidth 64 w + 2#64).toNat < s0.core.arena.length := by
            rw [har_idx]; omega
          c0_hsteps_nogrp
          apply wp_unroll_group; intro L653 hL653_raw
          have hL653 : ∀ (nv' u' k' : BitVec 32) (ab' sat' : Bool)
              (wsort' tmk' : List (BitVec 32)) (m' : Mem 64),
              wsort'.length = 2 * c.max_vars → tmk'.length = 2 * c.max_vars →
              nv'.toNat ≤ mv_s.toNat → nv'.toNat ≤ s0.core.cur_vars →
              FidK6cTmkReg nv'.toNat s0.core.cur_vars wsort' tmk' →
              (ab' = false → sat' = false → u'.toNat = 0 →
                ∀ q < (s0.core.arena[(BitVec.setWidth 64 w + 2#64).toNat]).toNat,
                  let ol := (s0.core.arena[w.toNat + 3 + q]?.getD 0#32).toNat
                  ol = unit.toNat ∨ s0.core.vals[ol]?.getD 0#8 = 255#8) →
              (FullMem c (FidP6Work s0 s0.core.tmp wsort' tmk' s0.scratch.scratch_buf) ⋆ R) m' →
              L653 (nv', ab', sat', u', k', ()) m' := by
            intro nv' u' k' ab' sat' wsort' tmk' m' hw' ht' hn1 hn2 hr' huall hm'
            apply hL653_raw; try dsimp only [Blocks.get, Member.here]
            c0_hsteps_nogrp
            · exact hL25 nv' j1 false ab' s0.core.tmp wsort' tmk' m' htp0 hw' ht' hn1 hn2 hr'
                (fun h => absurd h Bool.false_ne_true) hm'
            · have hab_f := hc
              apply wp_unroll_group; intro Js_660 hJs_660
              have hJ660 : ∀ (fl' ab' : Bool) (wsort' tmk' : List (BitVec 32)) (m' : Mem 64),
                  wsort'.length = 2 * c.max_vars → tmk'.length = 2 * c.max_vars →
                  nv'.toNat ≤ mv_s.toNat → nv'.toNat ≤ s0.core.cur_vars →
                  FidK6cTmkReg nv'.toNat s0.core.cur_vars wsort' tmk' →
                  (FullMem c (FidP6Work s0 s0.core.tmp wsort' tmk' s0.scratch.scratch_buf) ⋆ R)
                    m' →
                  Js_660 (fl', ab', ()) m' := by
                intro fl'' ab'' wsort'' tmk'' m'' hw'' ht'' hn1'' hn2'' hr'' hm''
                apply hJs_660; try dsimp only [Blocks.get, Member.here]
                c0_hsteps
                exact hJ446 nv' ab'' wsort'' tmk'' m'' hw'' ht'' hn1'' hn2'' hr'' hm'' fl''
              clear hJs_660
              c0_hsteps_nogrp
              · exact hJ660 false ab' wsort' tmk' m' hw' ht' hn1 hn2 hr' hm'
              · have hu_eq0 := hc
                have hsat_f' : sat' = false := by assumption
                have hu_z : u'.toNat = 0 := by simpa using congrArg BitVec.toNat hu_eq0
                have hcov := huall hab_f hsat_f' hu_z
                have har2_lt' : w.toNat + 2 < s0.core.arena.length := by
                  rw [← har_idx]; exact har2_lt
                have har_sz : s0.core.arena[(BitVec.setWidth 64 w + 2#64).toNat] =
                    s0.core.arena[w.toNat + 2]?.getD 0#32 := by
                  rw [List.getElem?_eq_getElem har2_lt', Option.getD_some]
                  congr 1
                have hwf_end : w.toNat + 3 + fullArenaClauseSize s0 w.toNat ≤
                    s0.core.arena.length := by
                  dsimp only [fullArenaClauseSize]
                  have := hwf.2.2.1; have := hwf.2.2.2.1; omega
                have hcl_ent : (cnfOfClauses F_cur).EntailsClause (cnfClause [unit.toNat]) := by
                  refine m6_lvl0_clause_unit_entails hinv.2.1 hinv.2.2.2.2.2.1
                    hent_w.1 hent_w.2 ?_
                  intro ol hol
                  dsimp only [fullArenaClauseLits, fullArenaClauseLitsCore] at hol
                  rcases List.mem_map.mp hol with ⟨obv, hobv, rfl⟩
                  have hdrop_len : (s0.core.arena.drop (w.toNat + 3)).length ≥
                      fullArenaClauseSize s0 w.toNat := by
                    rw [List.length_drop]; omega
                  rcases List.mem_iff_getElem.mp hobv with ⟨q, hq_lt, hq_eq⟩
                  have hq_sz : q < fullArenaClauseSize s0 w.toNat := by
                    rw [List.length_take_of_le hdrop_len] at hq_lt; exact hq_lt
                  have hget : obv = s0.core.arena[w.toNat + 3 + q]?.getD 0#32 := by
                    have h1 : (List.take (fullArenaClauseSize s0 w.toNat)
                        (s0.core.arena.drop (w.toNat + 3)))[q] =
                        s0.core.arena[w.toNat + 3 + q]'(by omega) := by
                      simp [List.getElem_take, List.getElem_drop]
                    rw [← hq_eq, h1, List.getElem?_eq_getElem (by omega), Option.getD_some]
                  rw [hget]; apply hcov q
                  rw [har_sz]; exact hq_sz
                exact hL25 nv' j1 true ab' s0.core.tmp wsort' tmk' m'
                  htp0 hw' ht' hn1 hn2 hr' (fun _ => hcl_ent) hm'
              · exact hL25 nv' j1 false true s0.core.tmp wsort' tmk' m' htp0 hw' ht' hn1 hn2
                  hr' (fun h => absurd h Bool.false_ne_true) hm'
              · exact hJ660 false ab' wsort' tmk' m' hw' ht' hn1 hn2 hr' hm'
          clear hL653_raw
          exact fid_cert_phase1_large_wp hinv hab_false htp0 hws1 htm1 hscr h1 h2
            hent_w.1 hent_w.2 (by
              dsimp only [fullArenaClauseSize, fullArenaClauseSizeCore]
              rw [← har_idx, List.getElem?_eq_getElem har2_lt]; rfl)
            hreg1 hm1 hL653
      · exact hJ231 nv1 ab1 wsort1 tmk1 m1 hws1 htm1 h1 h2 hreg1 hm1 false
    · exact hL25 nv1 j1 false ab1 s0.core.tmp wsort1 tmk1 m1
        htp0 hws1 htm1 h1 h2 hreg1 (fun h => absurd h Bool.false_ne_true) hm1
  · intro J hJ; c0_hsteps
    exact hJ side_cnt.toNat _ _ ⟨s0.scratch.wsort, s0.scratch.tarjan_mark, Nat.zero_le _, rfl,
      Nat.zero_le _, Nat.zero_le _, hws0, htm0, fid_k6c_tmkReg_init s0.core.cur_vars _ _ htmk0,
      hm⟩

end

end LeanQbe.T.Examples.Kissat.Proof.Definition
