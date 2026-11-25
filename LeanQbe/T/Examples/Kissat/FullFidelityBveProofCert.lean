module

public import LeanQbe.T.Examples.Kissat.FullFidelityBve
public import LeanQbe.T.Examples.Kissat.FullFidelityBveProof0
public import LeanQbe.T.Examples.Kissat.FullM6SweepProofSpec
public import LeanQbe.T.Examples.Kissat.FullM8CoreParityProofBve0
import all LeanQbe.T.Examples.Kissat.FullFidelityBveProof0
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullFidelityBveTactics
import LeanQbe.T.Examples.Kissat.FullM6SweepProofDenseProp

/-!
# Kissat Full-Fidelity BVE Certification Proofs (`FullFidelityBveProofCert`)

Proves WP specifications for:
- `full_bve_certify_unit_fid_body` (`fidBveCertifyUnitSpec`)
- `full_bve_def_k6_fid_body` (`m8BveGatesSpec`)
- `full_bve_gates_fid_body` (`m8BveGatesSpec`, no XOR)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityBve

open LeanQbe.T LeanQbe.T.ProofUtil Kraken.Bedrock2.Test
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open LeanQbe.T.Examples.Kissat.FullFastBveBudgets
open LeanQbe.T.Examples.Kissat.FullM4Sweep
open LeanQbe.T.Examples.Kissat.FullM6Sweep
open LeanQbe.T.Examples.Kissat.FullM8CoreParity
open Std.Sat

/-! ### Private Propositional, BitVec, and Pigeonhole Helpers -/

private theorem cert_zext64_toNat (x : BitVec 32) :
    (BitVec.zeroExtend 64 x).toNat = x.toNat := by
  rw [show BitVec.zeroExtend 64 x = BitVec.setWidth 64 x from rfl, BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (by have := x.isLt; omega)

private theorem cert_trunc32_toNat (x : BitVec 64) :
    (BitVec.truncate 32 x).toNat = x.toNat % 2 ^ 32 := by
  rw [show BitVec.truncate 32 x = BitVec.setWidth 32 x from rfl, BitVec.toNat_setWidth]

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
    · simp only [h, ↓reduceIte]
      have hd : l / 2 = (l + 1) / 2 := by omega
      simp [Nat.testBit_succ, hd]
    · simp only [h, ↓reduceIte]
      have hd : l / 2 = (l - 1) / 2 := by omega
      simp [Nat.testBit_succ, hd]

private theorem cert_bv32_shl1_and1 (v : BitVec 32) :
    (v <<< 1) &&& 1#32 = 0#32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  cases i with
  | zero => simp
  | succ k => simp

private theorem cert_bv32_shl1_or1_and1 (v : BitVec 32) :
    ((v <<< 1) ||| 1#32) &&& 1#32 = 1#32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  cases i with
  | zero => simp
  | succ k => simp

private theorem cert_bv32_shl1_or1_xor1 (v : BitVec 32) :
    ((v <<< 1) ||| 1#32) ^^^ 1#32 = v <<< 1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  cases i with
  | zero => simp
  | succ k => simp

private theorem cert_bv32_shl1_xor1 (v : BitVec 32) :
    (v <<< 1) ^^^ 1#32 = (v <<< 1) ||| 1#32 := by
  have h := cert_bv32_shl1_or1_xor1 v
  calc
    (v <<< 1) ^^^ 1#32 = (((v <<< 1) ||| 1#32) ^^^ 1#32) ^^^ 1#32 := by rw [h]
    _ = (v <<< 1) ||| 1#32 := by simp [BitVec.xor_assoc]

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

private theorem cert_trail_end_lt_of_val0 {c : FullCfg} {F0 : Std.Sat.CNF Nat}
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
    rw [mem_cnfClause_iff] at hm
    simp only [List.mem_singleton] at hm
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

private theorem cert_clause_sat_iff_mem (lits : List Nat) (α : Nat → Bool) :
    (cnfClause lits).Sat α ↔ ∃ q ∈ lits, (cnfClause [q]).Sat α := by
  rw [CNF.Clause.sat_iff_exists_mem_eq]
  constructor
  · rintro ⟨⟨v, p⟩, hm, heq⟩
    rw [mem_cnfClause_iff] at hm
    refine ⟨litOfLiteral (v, p), hm, ?_⟩
    rw [cert_clause_unit_sat_iff]
    cases p
    · have hd : mkLit v false / 2 = v := by
        simp only [mkLit, Bool.false_eq_true, ↓reduceIte]; omega
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

private theorem cert_clause_sat_xor_neg (l : Nat) (α : Nat → Bool) :
    (cnfClause [l ^^^ 1]).Sat α ↔ ¬ (cnfClause [l]).Sat α := by
  rw [cert_clause_unit_sat_iff, cert_clause_unit_sat_iff, cert_nat_xor1 l]
  by_cases hm : l % 2 = 0
  · have hd : (l + 1) / 2 = l / 2 := by omega
    have hne : (l + 1) % 2 ≠ 0 := by omega
    simp [hm, hd, hne]
  · have hd : (l - 1) / 2 = l / 2 := by omega
    have he0 : (l - 1) % 2 = 0 := by omega
    simp [hm, hd, he0]

private theorem cert_lvl0_false_entails {c : FullCfg} {F0 : Std.Sat.CNF Nat}
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

private theorem cert_entails_resolve_unit {F_cur : List (List Nat)} {u ot : Nat}
    (h1 : (cnfOfClauses F_cur).EntailsClause (cnfClause [u, ot]))
    (h2 : (cnfOfClauses F_cur).EntailsClause (cnfClause [ot ^^^ 1])) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause [u]) := by
  refine entails_of_mem_or_false h1 fun q hq => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · exact Or.inl (by simp)
  · exact Or.inr (by simpa [litNeg] using h2)

private theorem cert_lvl0_clause_unit_entails {F_cur : List (List Nat)} {lits : List Nat}
    {u : Nat} (h1 : (cnfOfClauses F_cur).EntailsClause (cnfClause lits))
    (h2 : ∀ q ∈ lits, q ≠ u → (cnfOfClauses F_cur).EntailsClause (cnfClause [q ^^^ 1])) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause [u]) := by
  refine entails_of_mem_or_false h1 fun q hq => ?_
  by_cases hqu : q = u
  · subst hqu; exact Or.inl (by simp)
  · exact Or.inr (by simpa [litNeg] using h2 q hq hqu)

private theorem cert_lvl0_unit_contra_unsat {F_cur : List (List Nat)} {u : Nat}
    (h1 : (cnfOfClauses F_cur).EntailsClause (cnfClause [u]))
    (h2 : (cnfOfClauses F_cur).EntailsClause (cnfClause [u ^^^ 1])) :
    (cnfOfClauses F_cur).Unsat := by
  refine unsat_of_entails_nil (entails_of_mem_or_false h1 fun q hq => ?_)
  simp only [List.mem_singleton] at hq; subst hq
  exact Or.inr (by simpa [litNeg] using h2)

private theorem cert_denseInvW_set_inconsistent {c : FullCfg} {F0 : Std.Sat.CNF Nat}
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

private theorem cert_i8_slt_zero_eq_255 (v : BitVec 8)
    (hdom : v = 0#8 ∨ v = 1#8 ∨ v = 255#8)
    (hslt : (BitVec.signExtend 32 v).slt (BitVec.signExtend 32 (BitVec.truncate 8 0#32)) = true) :
    v = 255#8 := by
  rcases hdom with rfl | rfl | rfl <;> revert hslt <;> decide

private theorem cert_i8_eq_zero_of_eq (v : BitVec 8)
    (heq : (BitVec.signExtend 32 v == BitVec.signExtend 32 (BitVec.truncate 8 0#32)) = true) :
    v = 0#8 := by
  revert v heq; decide

private theorem cert_i8_dom_255_of_not_sgt_not_eq (v : BitVec 8)
    (hdom : v = 0#8 ∨ v = 1#8 ∨ v = 255#8)
    (hns : (BitVec.signExtend 32 (BitVec.truncate 8 0#32)).slt (BitVec.signExtend 32 v) = false)
    (hne : (BitVec.signExtend 32 v == BitVec.signExtend 32 (BitVec.truncate 8 0#32)) = false) :
    v = 255#8 := by
  rcases hdom with rfl | rfl | rfl
  · exfalso; revert hne; decide
  · exfalso; revert hns; decide
  · rfl

private theorem cert_i8_slt0_eq_255 (v : BitVec 8)
    (hdom : v = 0#8 ∨ v = 1#8 ∨ v = 255#8)
    (hslt : v.slt 0#8 = true) :
    v = 255#8 := by
  rcases hdom with rfl | rfl | rfl <;> revert hslt <;> decide

private theorem cert_i8_dom_255_bv8 (v : BitVec 8)
    (hdom : v = 0#8 ∨ v = 1#8 ∨ v = 255#8)
    (hns : (0#8 : BitVec 8).slt v = false)
    (hne : v ≠ 0#8) :
    v = 255#8 := by
  rcases hdom with rfl | rfl | rfl
  · exact absurd rfl hne
  · exfalso; revert hns; decide
  · rfl

/-! ### Memory Framing and Local K6 Model-Set Helpers -/

private theorem cert_focus_addCl_tmp {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (Full.FullMem c s ⋆ R) m) :
    (array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆
      array (t := i32) c.pScratchBuf s.scratch.scratch_buf ⋆ array (t := i32) c.pTmp s.core.tmp ⋆
      (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
        FullCoreByteArrs c s.core ⋆
        (array (t := i32) c.pFlags s.core.flags ⋆ array (t := i32) c.pLevel s.core.lvl ⋆
         array (t := i32) c.pReason s.core.rsns ⋆ array (t := i32) c.pTrail s.core.trl ⋆
         array (t := i32) c.pTrailPos s.core.trail_pos ⋆
         array (t := i32) c.pMinClr s.core.min_clr) ⋆
        FullCoreU32B c s.core ⋆ FullCoreDynArrs c s.core ⋆ FullScrByteArrs c s.scratch ⋆
        FullScrU32A c s.scratch ⋆ FullScrWksArrs c s.scratch ⋆ FullScrMetaArrs c s.scratch ⋆
        (array (t := i32) c.pDelayed s.scratch.delayed ⋆
         array (t := i32) c.pRedRefs s.scratch.red_refs ⋆
         array (t := i32) c.pExtendStk s.scratch.extend_stk) ⋆ c.pad ⋆ R)) m := by
  rw [Full.FullMem] at hm
  dsimp [FullCoreArrays, FullCoreU32A, FullScratchArrays, FullScrDynArrs] at hm; exact sep_ac hm

private theorem cert_unfocus_addCl_tmp {c : FullCfg} {s : FullState}
    {scr' : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (array64 (c.hdr + 32)
        (Full.hdrTailWords c { s with scratch := { s.scratch with scratch_buf := scr' } }) ⋆
      array (t := i32) c.pScratchBuf scr' ⋆ array (t := i32) c.pTmp s.core.tmp ⋆
      (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
        FullCoreByteArrs c s.core ⋆
        (array (t := i32) c.pFlags s.core.flags ⋆ array (t := i32) c.pLevel s.core.lvl ⋆
         array (t := i32) c.pReason s.core.rsns ⋆ array (t := i32) c.pTrail s.core.trl ⋆
         array (t := i32) c.pTrailPos s.core.trail_pos ⋆
         array (t := i32) c.pMinClr s.core.min_clr) ⋆
        FullCoreU32B c s.core ⋆ FullCoreDynArrs c s.core ⋆ FullScrByteArrs c s.scratch ⋆
        FullScrU32A c s.scratch ⋆ FullScrWksArrs c s.scratch ⋆ FullScrMetaArrs c s.scratch ⋆
        (array (t := i32) c.pDelayed s.scratch.delayed ⋆
         array (t := i32) c.pRedRefs s.scratch.red_refs ⋆
         array (t := i32) c.pExtendStk s.scratch.extend_stk) ⋆ c.pad ⋆ R)) m) :
    (Full.FullMem c { s with scratch := { s.scratch with scratch_buf := scr' } } ⋆ R) m := by
  rw [Full.FullMem]
  dsimp [FullCoreArrays, FullCoreU32A, FullScratchArrays, FullScrDynArrs]; exact sep_ac hm

private def certModelSet (F_cur : List (List Nat)) (exp : List (BitVec 32))
    (nv unit : Nat) (β : Nat → Bool) : Prop :=
  ∃ α : Nat → Bool, (cnfOfClauses F_cur).Sat α ∧
    ¬ (cnfClause [unit]).Sat α ∧
    ∀ i < nv, β i = α (exp[i]?.getD 0#32).toNat

private theorem cert_modelSet_unsat_entails {F_cur : List (List Nat)}
    {exp : List (BitVec 32)} {nv unit : Nat}
    (hunsat : ∀ β : Nat → Bool, ¬ certModelSet F_cur exp nv unit β) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause [unit]) := by
  rw [CNF.entails_clause_def]
  intro α hsat
  exact Classical.byContradiction fun hnsat =>
    hunsat (fun i => α (exp[i]?.getD 0#32).toNat) ⟨α, hsat, hnsat, fun _ _ => rfl⟩

private theorem cert_entails_in_modelSet {F_cur : List (List Nat)} {lits : List Nat}
    {unit : Nat} (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause lits))
    {α : Nat → Bool} (hsat : (cnfOfClauses F_cur).Sat α)
    (hnu : ¬ (cnfClause [unit]).Sat α) :
    ∃ q ∈ lits, q ≠ unit ∧ (cnfClause [q]).Sat α := by
  rw [CNF.entails_clause_def] at hent
  rcases (cert_clause_sat_iff_mem lits α).mp (hent α hsat) with ⟨q, hq, hqs⟩
  refine ⟨q, hq, ?_, hqs⟩
  rintro rfl
  exact hnu hqs

private theorem cert_mapped_lit_sat {α β : Nat → Bool} {exp : List (BitVec 32)}
    {nv loc q : Nat} (hloc1 : 1 ≤ loc) (hloc2 : loc ≤ nv)
    (hexp : (exp[loc - 1]?.getD 0#32).toNat = q / 2)
    (hmap : ∀ i < nv, β i = α (exp[i]?.getD 0#32).toNat)
    {ml : Nat} (hml_div : ml / 2 = loc - 1) (hml_mod : ml % 2 = q % 2)
    (hqs : (cnfClause [q]).Sat α) :
    (cnfClause [ml]).Sat β := by
  rw [cert_clause_unit_sat_iff] at hqs ⊢
  rw [hml_div, hml_mod, hmap (loc - 1) (by omega), hexp]
  exact hqs

private def certExportOk (cur_vars nv : Nat) (tmk exp : List (BitVec 32)) : Prop :=
  (∀ u < cur_vars, tmk[u]?.getD 0#32 ≠ 0#32 →
    1 ≤ (tmk[u]?.getD 0#32).toNat ∧ (tmk[u]?.getD 0#32).toNat ≤ nv ∧
    (exp[(tmk[u]?.getD 0#32).toNat - 1]?.getD 0#32).toNat = u) ∧
  (∀ j < nv, (exp[j]?.getD 0#32).toNat < cur_vars ∧
    (tmk[(exp[j]?.getD 0#32).toNat]?.getD 0#32).toNat = j + 1)

private theorem cert_export_zero {cur_vars : Nat} {tmk exp : List (BitVec 32)}
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

private def certUndoInv (cur_vars nv : Nat) (exp tmk : List (BitVec 32)) : Nat → Prop
  | j => ∀ u < cur_vars, tmk[u]?.getD 0#32 ≠ 0#32 →
      ∃ k, j ≤ k ∧ k < nv ∧ (exp[k]?.getD 0#32).toNat = u

private theorem cert_undo_init {cur_vars nv : Nat} {tmk exp : List (BitVec 32)}
    (hok : certExportOk cur_vars nv tmk exp) :
    certUndoInv cur_vars nv exp tmk 0 := by
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
    rcases hinv u hu hnz with ⟨k, hle, hlt, _⟩
    omega

/-! ### `full_bve_gates_fid_wp` -/

theorem full_bve_gates_fid_wp (Γ : Env)
    (hEquiv : ∀ a m Q X, m8BveFindEquivSpec a m Q X →
      Γ "full_bve_find_equiv_m8" [i64, i32, i32] [.bool] a m Q X)
    (hAnd : ∀ a m Q X, m8BveFindAndSpec a m Q X →
      Γ "full_bve_find_and_m8" [i64, i32, i32, i32] [.bool] a m Q X)
    (hIte : ∀ a m Q X, m8BveFindIteSpec a m Q X →
      Γ "full_bve_find_ite_m8" [i64, i32, i32, i32] [.bool] a m Q X)
    (hDefK6 : ∀ a m Q X, m8BveGatesSpec a m Q X →
      Γ "full_bve_def_k6_fid" [i64, i32, i32, i32] [] a m Q X) :
    ∀ a m Q X, m8BveGatesSpec a m Q X → Func.wp Γ full_bve_gates_fid_body a m Q X := by
  rintro ⟨h, v, np, nn, ⟨⟩⟩ m Q X hspec
  rcases m8BveGatesSpec_elim hspec with
    ⟨c, F0, F_cur, s, R, rfl, hinv, htmk, hcap, hv, hnp, hnn, henp, henn, hm, hQ⟩
  unfold full_bve_gates_fid_body Func.wp; c0_hsteps_nogrp
  refine wp_while_state1 (fun st : BitVec 32 × List (BitVec 32) => st.1)
    (fun st => 130 - st.1.toNat)
    (fun (i, scr) m' => i.toNat ≤ 130 ∧ scr.length = c.scratch_cap ∧
      (∀ idx < c.scratch_cap, (idx < 4002 ∨ 4002 + i.toNat ≤ idx) →
        scr[idx]? = s.scratch.scratch_buf[idx]?) ∧
      (Full.FullMem c { s with scratch := { s.scratch with scratch_buf := scr } } ⋆ R) m')
    (fun J hJ => by
      c0_hsteps
      exact hJ (0#32, s.scratch.scratch_buf) m
        ⟨Nat.zero_le _, hinv.1.scratch_ok.scratch_buf_len, fun _ _ _ => rfl, hm⟩)
    (fun J (i, scr) m' ⟨hi, hlen, hpres, hm'⟩ ih => ?_)
  · c0_hsplit
    · have hi' : i.toNat < 130 := by c0_bound
      have hidx_eq : (4002#32 + i).toNat = 4002 + i.toNat := by simp [BitVec.toNat_add]; omega
      have hidx_lt : (BitVec.zeroExtend 64 (4002#32 + i)).toNat < scr.length := by
        rw [cert_zext64_toNat, hidx_eq]; omega
      c0_hsteps
      have hlt_mu : 130 - (i + 1#32).toNat < 130 - i.toNat := by simp [BitVec.toNat_add]; omega
      have hhi1 : (i + 1#32).toNat ≤ 130 := by simp [BitVec.toNat_add]; omega
      let scr' := scr.set (BitVec.zeroExtend 64 (4002#32 + i)).toNat 0#32
      have hlt64 : 4002 + i.toNat < 2 ^ 64 := by omega
      have hscr'_eq : scr' = scr.set (4002 + i.toNat) 0#32 := by
        simp [scr', hidx_eq, Nat.mod_eq_of_lt hlt64]
      refine ih (i + 1#32, scr') _ hlt_mu
        ⟨hhi1, by simpa [scr'] using hlen, fun idx hidx hcond => by
          have hi1 : (i + 1#32).toNat = i.toNat + 1 := by simp [BitVec.toNat_add]; omega
          rw [hi1] at hcond; rw [hscr'_eq, List.getElem?_set_ne (by omega)]
          exact hpres idx hidx (by omega), by assumption⟩
    · have hi130 : i.toNat = 130 := by c0_bound
      let s1 : FullState := { s with scratch := { s.scratch with scratch_buf := scr } }
      have hinv1 : FullDenseInvW c F0 F_cur s1 :=
        m8_fullDenseInvW_def hinv hinv.1.core_ok.tmp_len_arr hinv.1.scratch_ok.wsort_len
          hinv.1.scratch_ok.tarjan_mark_len hlen
      have htmk1 : TmkZero s1 := htmk
      have henp1 : ∀ idx < np.toNat, FullBveEntryOkW F_cur s1 (2 * v.toNat) (scr[idx]?.getD 0#32) :=
        fun idx hidx => by
          rw [hpres idx (by omega) (Or.inl (by omega))]
          exact m8_bveEntry_congr_core (henp idx hidx) rfl rfl rfl
      have henn1 : ∀ idx < nn.toNat,
          FullBveEntryOkW F_cur s1 (2 * v.toNat + 1) (scr[2001 + idx]?.getD 0#32) :=
        fun idx hidx => by
          rw [hpres (2001 + idx) (by omega) (Or.inl (by omega))]
          exact m8_bveEntry_congr_core (henn idx hidx) rfl rfl rfl
      have hret0 : ∀ {s' : FullState} {m'' : Mem 64}, FullDenseInvW c F0 F_cur s' → TmkZero s' →
          s'.core.cur_vars = s.core.cur_vars → s'.core.arena = s.core.arena →
          s'.core.arena_len = s.core.arena_len → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
          (∀ k < np.toNat, s'.scratch.scratch_buf[k]? = scr[k]?) →
          (∀ k < nn.toNat, s'.scratch.scratch_buf[2001 + k]? = scr[2001 + k]?) →
          (Full.FullMem c s' ⋆ R) m'' → Q () m'' := fun hi' ht' hcv' har' hal' hfl' hp' hn' hm'' =>
        hQ _ _ hi' ht' hcv' har' hal' hfl'
          (fun k hk => by rw [hp' k hk]; exact hpres k (by omega) (Or.inl (by omega)))
          (fun k hk => by rw [hn' k hk]; exact hpres (2001 + k) (by omega) (Or.inl (by omega))) hm''
      c0_hsteps
      · exact hret0 hinv1 htmk1 rfl rfl rfl (Nat.le_refl _) (fun _ _ => rfl) (fun _ _ => rfl) hm'
      · exact hret0 hinv1 htmk1 rfl rfl rfl (Nat.le_refl _) (fun _ _ => rfl) (fun _ _ => rfl) hm'
      · fid_call hEquiv; dsimp only [Arg.val]
        refine m8BveFindEquivSpec_intro rfl hinv1 hcap hnp hnn
          (fun idx hidx hbit => by
            have he := henp1 idx hidx; unfold FullBveEntryOkW at he; rw [ite_eq_left hbit] at he
            exact he.1)
          (fun idx hidx hbit => by
            have he := henn1 idx hidx; unfold FullBveEntryOkW at he; rw [ite_eq_left hbit] at he
            exact he.1) hm' ?_
        intro _ lmEq scrEq mEq; dsimp only; intro hinvEq _ hpresEq hmEq
        let sEq : FullState :=
          { s1 with core := { s1.core with lit_mark := lmEq }
                    scratch := { s1.scratch with scratch_buf := scrEq } }
        have hpres_lt4002_Eq : ∀ k < 4002, scrEq[k]? = scr[k]? :=
          fun k hk => hpresEq k (by omega) (Or.inl hk)
        c0_hsteps
        · exact hret0 hinvEq htmk1 rfl rfl rfl (Nat.le_refl _)
            (fun k hk => hpres_lt4002_Eq k (by omega))
            (fun k hk => hpres_lt4002_Eq (2001 + k) (by omega)) hmEq
        · fid_call hAnd; dsimp only [vals, Arg.val]
          have hlit_p : (v <<< 1) &&& 1#32 = 0#32 := cert_bv32_shl1_and1 v
          have hneg_p : ¬ ((v <<< 1) &&& 1#32 ≠ 0#32) := fun h => h hlit_p
          have hb_lt : 2 * v.toNat + 1 < 2 ^ 32 := by
            have := hinv.1.core_ok.cur_vars_le; have h2 := c.hmaxv
            unfold LeanQbe.T.Examples.LratBytes.dimacsBound at h2; omega
          have hlit_toNat : (v <<< 1).toNat = 2 * v.toNat := m8_bv32_shl1_toNat (by omega)
          have hxor_toNat : ((v <<< 1) ^^^ 1#32).toNat = 2 * v.toNat + 1 := by
            rw [cert_bv32_shl1_xor1]; exact m8_bv32_shl1_or1_toNat hb_lt
          refine m8BveFindAndSpec_intro rfl hinvEq hcap hnp hnn
            (fun idx hidx => by
              dsimp only [Arg.val] at hidx ⊢
              simp only [hneg_p, ↓reduceIte, Nat.zero_add, hlit_toNat,
                hpres_lt4002_Eq idx (by omega)]
              exact m8_bveEntry_congr_core (henp1 idx hidx) rfl rfl rfl)
            (fun idx hidx => by
              dsimp only [Arg.val] at hidx ⊢
              simp only [hneg_p, ↓reduceIte, hxor_toNat, hpres_lt4002_Eq (2001 + idx) (by omega)]
              exact m8_bveEntry_congr_core (henn1 idx hidx) rfl rfl rfl) hmEq ?_
          intro _ lmA1 scrA1 mA1; dsimp only; intro hinvA1 _ hpresA1 hmA1
          let sA1 : FullState :=
            { sEq with core := { sEq.core with lit_mark := lmA1 }
                       scratch := { sEq.scratch with scratch_buf := scrA1 } }
          have hpres_lt4002_A1 : ∀ k < 4002, scrA1[k]? = scr[k]? := fun k hk => by
            rw [hpresA1 k (by omega) (Or.inl hk)]; exact hpres_lt4002_Eq k hk
          c0_hsteps
          · exact hret0 hinvA1 htmk1 rfl rfl rfl (Nat.le_refl _)
              (fun k hk => hpres_lt4002_A1 k (by omega))
              (fun k hk => hpres_lt4002_A1 (2001 + k) (by omega)) hmA1
          · fid_call hAnd; dsimp only [vals, Arg.val]
            have hlit_n : ((v <<< 1) ||| 1#32) &&& 1#32 = 1#32 := cert_bv32_shl1_or1_and1 v
            have hlit2_toNat : ((v <<< 1) ||| 1#32).toNat = 2 * v.toNat + 1 :=
              m8_bv32_shl1_or1_toNat hb_lt
            have hxor2_toNat : (((v <<< 1) ||| 1#32) ^^^ 1#32).toNat = 2 * v.toNat := by
              rw [cert_bv32_shl1_or1_xor1]; exact m8_bv32_shl1_toNat (by omega)
            have hshl_eq : (v <<< OfNat.ofNat 1 ||| 1 : BitVec 32) = ((v <<< 1) ||| 1#32) := rfl
            refine m8BveFindAndSpec_intro rfl hinvA1 hcap hnn hnp
              (fun idx hidx => by
                dsimp only [Arg.val] at hidx ⊢
                have hif : (if (v <<< OfNat.ofNat 1 ||| 1 : BitVec 32) &&& BitVec.ofNat 32 1 ≠
                    BitVec.ofNat 32 0 then 2001 else 0) = 2001 := by rw [hshl_eq]; simp [hlit_n]
                rw [hif, hshl_eq, hlit2_toNat, hpres_lt4002_A1 (2001 + idx) (by omega)]
                exact m8_bveEntry_congr_core (henn1 idx hidx) rfl rfl rfl)
              (fun idx hidx => by
                dsimp only [Arg.val] at hidx ⊢
                have hif : (if (v <<< OfNat.ofNat 1 ||| 1 : BitVec 32) &&& BitVec.ofNat 32 1 ≠
                    BitVec.ofNat 32 0 then 0 else 2001) = 0 := by rw [hshl_eq]; simp [hlit_n]
                rw [hif, Nat.zero_add, hshl_eq, hxor2_toNat, hpres_lt4002_A1 idx (by omega)]
                exact m8_bveEntry_congr_core (henp1 idx hidx) rfl rfl rfl) hmA1 ?_
            intro _ lmA2 scrA2 mA2; dsimp only; intro hinvA2 _ hpresA2 hmA2
            let sA2 : FullState :=
              { sA1 with core := { sA1.core with lit_mark := lmA2 }
                         scratch := { sA1.scratch with scratch_buf := scrA2 } }
            have hpres_lt4002_A2 : ∀ k < 4002, scrA2[k]? = scr[k]? := fun k hk => by
              rw [hpresA2 k (by omega) (Or.inl hk)]; exact hpres_lt4002_A1 k hk
            c0_hsteps
            · exact hret0 hinvA2 htmk1 rfl rfl rfl (Nat.le_refl _)
                (fun k hk => hpres_lt4002_A2 k (by omega))
                (fun k hk => hpres_lt4002_A2 (2001 + k) (by omega)) hmA2
            · fid_call hIte; dsimp only [vals, Arg.val]
              refine m8BveFindIteSpec_intro rfl hinvA2 hcap hv hnp hnn
                (fun idx hidx => by
                  dsimp only [Arg.val] at hidx ⊢; rw [hpres_lt4002_A2 idx (by omega)]
                  exact m8_bveEntry_congr_core (henp1 idx hidx) rfl rfl rfl)
                (fun idx hidx => by
                  dsimp only [Arg.val] at hidx ⊢; rw [hpres_lt4002_A2 (2001 + idx) (by omega)]
                  exact m8_bveEntry_congr_core (henn1 idx hidx) rfl rfl rfl) hmA2 ?_
              intro _ scrIte mIte; dsimp only; intro hlenIte hpresIte hmIte
              let sIte : FullState :=
                { sA2 with scratch := { sA2.scratch with scratch_buf := scrIte } }
              have hinvIte : FullDenseInvW c F0 F_cur sIte :=
                m8_fullDenseInvW_def hinvA2 hinvA2.1.core_ok.tmp_len_arr
                  hinvA2.1.scratch_ok.wsort_len hinvA2.1.scratch_ok.tarjan_mark_len hlenIte
              have hpres_lt4002_Ite : ∀ k < 4002, scrIte[k]? = scr[k]? := fun k hk => by
                rw [hpresIte k (by omega) (Or.inl hk)]; exact hpres_lt4002_A2 k hk
              c0_hsteps
              · exact hret0 hinvIte htmk1 rfl rfl rfl (Nat.le_refl _)
                  (fun k hk => hpres_lt4002_Ite k (by omega))
                  (fun k hk => hpres_lt4002_Ite (2001 + k) (by omega)) hmIte
              · fid_call hDefK6; dsimp only [vals, Arg.val]
                refine m8BveGatesSpec_intro rfl hinvIte htmk1 hcap hv hnp hnn
                  (fun idx hidx => by
                    rw [hpres_lt4002_Ite idx (by omega)]
                    exact m8_bveEntry_congr_core (henp1 idx hidx) rfl rfl rfl)
                  (fun idx hidx => by
                    rw [hpres_lt4002_Ite (2001 + idx) (by omega)]
                    exact m8_bveEntry_congr_core (henn1 idx hidx) rfl rfl rfl) hmIte ?_
                intro sF mF hiF htF hcvF harF halF hflF hpF hnF hmF; c0_hsteps
                exact hret0 hiF htF hcvF harF halF hflF
                  (fun k hk => by rw [hpF k hk, hpres_lt4002_Ite k (by omega)])
                  (fun k hk => by rw [hnF k hk, hpres_lt4002_Ite (2001 + k) (by omega)]) hmF

/-! ### `full_bve_def_k6_fid_wp` -/

theorem full_bve_def_k6_fid_wp (Γ : Env)
    (hMv : ∀ a m Q X, fidBveK6MvSpec a m Q X → Γ "full_bve_k6_mv_fid" [i64] [i64] a m Q X)
    (hExtSolve : ∀ a m Q X, fidK6ExtractSolveSpec a m Q X →
      Γ "full_k6_extract_and_solve_fid" [i64, i32, i32, i32, .bool, i32] [.bool] a m Q X)
    (hCertUnit : ∀ a m Q X, fidBveCertifyUnitSpec a m Q X →
      Γ "full_bve_certify_unit_fid" [i64, i32, i32, i32, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, m8BveGatesSpec a m Q X → Func.wp Γ full_bve_def_k6_fid_body a m Q X := by
  rintro ⟨h, v, np, nn, ⟨⟩⟩ m Q X hspec
  rcases m8BveGatesSpec_elim hspec with
    ⟨c, F0, F_cur, s, R, rfl, hinv, htmk, hcap, hv, hnp, hnn, henp, henn, hm, hQ⟩
  unfold full_bve_def_k6_fid_body Func.wp; c0_hsteps
  fid_call hMv; unfold fidBveK6MvSpec; dsimp only; c0_hsteps
  · exact hQ s m hinv htmk rfl rfl rfl (Nat.le_refl _) (fun _ _ => rfl) (fun _ _ => rfl) hm
  · exact hQ s m hinv htmk rfl rfl rfl (Nat.le_refl _) (fun _ _ => rfl) (fun _ _ => rfl) hm
  · exact hQ s m hinv htmk rfl rfl rfl (Nat.le_refl _) (fun _ _ => rfl) (fun _ _ => rfl) hm
  · exact hQ s m hinv htmk rfl rfl rfl (Nat.le_refl _) (fun _ _ => rfl) (fun _ _ => rfl) hm
  · fid_call hExtSolve
    refine fidK6ExtractSolveSpec_intro rfl hinv htmk hcap hv hnp hnn henp henn hm ?_
    intro _ s1 m1 hinv1 htmk1 hcv1 har1 hal1 hfl1 hpres1 _ hm1
    have henp1 : ∀ idx < np.toNat,
        FullBveEntryOkW F_cur s1 (2 * v.toNat) (s1.scratch.scratch_buf[idx]?.getD 0#32) :=
      fun idx hidx => by
        rw [hpres1 idx (by omega)]; exact m8_bveEntry_congr_core (henp idx hidx) hcv1 har1 hal1
    have henn1 : ∀ idx < nn.toNat, FullBveEntryOkW F_cur s1 (2 * v.toNat + 1)
          (s1.scratch.scratch_buf[2001 + idx]?.getD 0#32) := fun idx hidx => by
      rw [hpres1 (2001 + idx) (by omega)]
      exact m8_bveEntry_congr_core (henn idx hidx) hcv1 har1 hal1
    c0_hsteps
    · fid_call hExtSolve
      refine fidK6ExtractSolveSpec_intro rfl hinv1 htmk1 hcap (by rw [hcv1]; exact hv)
        hnp hnn henp1 henn1 hm1 ?_
      intro _ s2 m2 hinv2 htmk2 hcv2 har2 hal2 hfl2 hpres2 _ hm2
      let scr2 := s2.scratch.scratch_buf
      have hlen2 : scr2.length = c.scratch_cap := hinv2.1.scratch_ok.scratch_buf_len
      have hpres02 : ∀ idx < 4002, scr2[idx]? = s.scratch.scratch_buf[idx]? := fun idx hidx => by
        rw [show scr2[idx]? = s1.scratch.scratch_buf[idx]? from hpres2 idx hidx]
        exact hpres1 idx hidx
      have henp2 : ∀ idx < np.toNat,
          FullBveEntryOkW F_cur s2 (2 * v.toNat) (scr2[idx]?.getD 0#32) := fun idx hidx => by
        rw [hpres02 idx (by omega)]
        exact m8_bveEntry_congr_core (henp idx hidx) (hcv2.trans hcv1) (har2.trans har1)
          (hal2.trans hal1)
      have henn2 : ∀ idx < nn.toNat,
          FullBveEntryOkW F_cur s2 (2 * v.toNat + 1) (scr2[2001 + idx]?.getD 0#32) :=
        fun idx hidx => by
          rw [hpres02 (2001 + idx) (by omega)]
          exact m8_bveEntry_congr_core (henn idx hidx) (hcv2.trans hcv1) (har2.trans har1)
            (hal2.trans hal1)
      c0_hsteps_nogrp
      · refine wp_while_state (fun st : Bool × Bool × BitVec 32 => (st.1, st.2.1, st.2.2, ()))
          (fun st => 64 - st.2.2.toNat) (fun _ m' => m' = m2)
          (fun J hJ => by c0_hsteps; exact hJ (false, false, 0#32) m2 rfl)
          (fun J (hp, hn, k) m' hm_eq ih => ?_)
        rw [hm_eq]; c0_hsteps_nogrp
        · refine wp_join_state1 (fun b : Bool => b) (fun _ m' => m' = m2)
            (fun J1 b m' hm_eq => by
              rw [hm_eq]; c0_hsteps_nogrp
              refine wp_join_state1 (fun b2 : Bool => b2) (fun _ m' => m' = m2)
                (fun J2 b2 m' hm_eq => by
                  rw [hm_eq]; c0_hsteps; have hk : k.toNat < 64 := by c0_bound
                  exact ih (b, b2, k + 1#32) m2 (by simp [BitVec.toNat_add]; omega) rfl)
                (fun J2 hJ2 => by
                  have hk : k.toNat < 64 := by c0_bound
                  have h4066 : (4066#32 + k).toNat = 4066 + k.toNat := by
                    simp [BitVec.toNat_add]; omega
                  have hlt : (BitVec.zeroExtend 64 (4066#32 + k)).toNat < scr2.length := by
                    rw [cert_zext64_toNat, h4066]; omega
                  c0_hsteps
                  · exact hJ2 true m2 rfl
                  · exact hJ2 hn m2 rfl))
            (fun J1 hJ1 => by
              have hk : k.toNat < 64 := by c0_bound
              have h4002 : (4002#32 + k).toNat = 4002 + k.toNat := by
                simp [BitVec.toNat_add]; omega
              have hlt : (BitVec.zeroExtend 64 (4002#32 + k)).toNat < scr2.length := by
                rw [cert_zext64_toNat, h4002]; omega
              c0_hsteps
              · exact hJ1 true m2 rfl
              · exact hJ1 hp m2 rfl)
        · have hret2 : Q () m2 := hQ s2 m2 hinv2 htmk2 (hcv2.trans hcv1) (har2.trans har1)
            (hal2.trans hal1) (Nat.le_trans hfl2 hfl1) (fun idx hidx => hpres02 idx (by omega))
            (fun idx hidx => hpres02 (2001 + idx) (by omega)) hm2
          have hpostCert : ∀ {s3 : FullState} {m3 : Mem 64}, FullDenseInvW c F0 F_cur s3 →
              TmkZero s3 → s3.core.cur_vars = s2.core.cur_vars → s3.core.arena = s2.core.arena →
              s3.core.arena_len = s2.core.arena_len → s3.core.fuel.toNat ≤ s2.core.fuel.toNat →
              (∀ i < 4192, s3.scratch.scratch_buf[i]? = s2.scratch.scratch_buf[i]?) →
              (Full.FullMem c s3 ⋆ R) m3 → Q () m3 := fun hi3 ht3 hcv3 har3 hal3 hfl3 hp3 hm3 =>
            hQ _ _ hi3 ht3 (hcv3.trans (hcv2.trans hcv1)) (har3.trans (har2.trans har1))
              (hal3.trans (hal2.trans hal1)) (Nat.le_trans hfl3 (Nat.le_trans hfl2 hfl1))
              (fun idx hidx => by rw [hp3 idx (by omega)]; exact hpres02 idx (by omega))
              (fun idx hidx => by
                rw [hp3 (2001 + idx) (by omega)]; exact hpres02 (2001 + idx) (by omega)) hm3
          have hb_lt : 2 * v.toNat + 1 < 2 ^ 32 := by
            have h1 := hinv2.1.core_ok.cur_vars_le; have h2 := c.hmaxv
            unfold LeanQbe.T.Examples.LratBytes.dimacsBound at h2; omega
          c0_hsteps_nogrp
          refine wp_join0 (fun m' => Q () m') (fun J m' hQm => by c0_hsteps; exact hQm)
            (fun Jret hJret => by
              c0_hsteps_nogrp
              refine wp_join0 (fun m' => Q () m' ∧ (hp = true → m' = m2))
                (fun J1 m' ⟨hQm, hmeq⟩ => by
                  c0_hsteps
                  · exact hJret m' hQm
                  · have hme : m' = m2 := hmeq (by c0_bound); subst hme
                    fid_call hCertUnit; dsimp only [vals, Arg.val]
                    refine fidBveCertifyUnitSpec_intro rfl hinv2 htmk2 hcap ?_ hnp (by simp; omega)
                      (Or.inl rfl) (fun i hi => by
                        simp only [show (0 : BitVec 32).toNat = 0 from rfl, Nat.zero_add]
                        rw [show (v <<< OfNat.ofNat 1 : BitVec 32) = (v <<< 1) from rfl,
                          m8_bv32_shl1_toNat (by omega)]
                        exact henp2 i hi) hm2 ?_
                    · rw [show (v <<< OfNat.ofNat 1 : BitVec 32) = (v <<< 1) from rfl,
                        m8_bv32_shl1_toNat (by omega)]; omega
                    · intro _ s3 m3 hi3 ht3 hcv3 har3 hal3 hfl3 hp3 hm3; c0_hsteps
                      exact hJret m3 (hpostCert hi3 ht3 hcv3 har3 hal3 hfl3 hp3 hm3)
                  · exact hJret m' hQm)
                (fun Jpos hJpos => by
                  c0_hsteps
                  · exact hJpos m2 ⟨hret2, fun _ => rfl⟩
                  · fid_call hCertUnit; dsimp only [vals, Arg.val]
                    refine fidBveCertifyUnitSpec_intro rfl hinv2 htmk2 hcap ?_ hnn (by simp; omega)
                      (Or.inr rfl) (fun i hi => by
                        simp only [show (2001 : BitVec 32).toNat = 2001 from rfl]
                        rw [show (v <<< OfNat.ofNat 1 ||| 1 : BitVec 32) = ((v <<< 1) ||| 1#32)
                          from rfl, m8_bv32_shl1_or1_toNat hb_lt]
                        exact henn2 i hi) hm2 ?_
                    · rw [show (v <<< OfNat.ofNat 1 ||| 1 : BitVec 32) = ((v <<< 1) ||| 1#32)
                        from rfl, m8_bv32_shl1_or1_toNat hb_lt]; omega
                    · intro _ s3 m3 hi3 ht3 hcv3 har3 hal3 hfl3 hp3 hm3; c0_hsteps
                      exact hJret m3 (hpostCert hi3 ht3 hcv3 har3 hal3 hfl3 hp3 hm3)
                  · exact hJpos m2 ⟨hret2, fun _ => rfl⟩))
      · have hlt4130 : (BitVec.zeroExtend 64 4130#32).toNat < scr2.length := by
          rw [show (BitVec.zeroExtend 64 4130#32).toNat = 4130 from rfl]; omega
        have hlt4131 : (BitVec.zeroExtend 64 4131#32).toNat < scr2.length := by
          rw [show (BitVec.zeroExtend 64 4131#32).toNat = 4131 from rfl]; omega
        c0_hsteps
        let scr3 := (scr2.set (BitVec.zeroExtend 64 4130#32).toNat 0#32).set
          (BitVec.zeroExtend 64 4131#32).toNat 0#32
        have hscr3_eq : scr3 = (scr2.set 4130 0#32).set 4131 0#32 := by simp [scr3]
        have hlen3 : scr3.length = c.scratch_cap := by simp [hscr3_eq, hlen2]
        have hinv3 : FullDenseInvW c F0 F_cur
            { s2 with scratch := { s2.scratch with scratch_buf := scr3 } } :=
          m8_fullDenseInvW_def hinv2 hinv2.1.core_ok.tmp_len_arr
            hinv2.1.scratch_ok.wsort_len hinv2.1.scratch_ok.tarjan_mark_len hlen3
        have hpres03 : ∀ idx < 4002, scr3[idx]? = s.scratch.scratch_buf[idx]? := fun idx hidx => by
          rw [hscr3_eq, List.getElem?_set_ne (by omega : 4131 ≠ idx),
            List.getElem?_set_ne (by omega : 4130 ≠ idx)]
          exact hpres02 idx hidx
        exact hQ _ _ hinv3 htmk2 (hcv2.trans hcv1) (har2.trans har1) (hal2.trans hal1)
          (Nat.le_trans hfl2 hfl1) (fun idx hidx => hpres03 idx (by omega))
          (fun idx hidx => hpres03 (2001 + idx) (by omega)) (by assumption)
    · exact hQ s1 m1 hinv1 htmk1 hcv1 har1 hal1 hfl1 (fun idx hidx => hpres1 idx (by omega))
        (fun idx hidx => hpres1 (2001 + idx) (by omega)) hm1

/-! ### `full_bve_certify_unit_fid_wp` -/

def certMkState (s : FullState) (tmp exp tmk scr : List (BitVec 32)) : FullState :=
  { core := { s.core with tmp := tmp }
    scratch := { s.scratch with wsort := exp, tarjan_mark := tmk, scratch_buf := scr } }

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
end CertMkTactics

open scoped CertMkTactics
open CertMkTactics

private theorem cert_shr1_toNat (x : BitVec 32) : (x >>> 1#32).toNat = x.toNat / 2 := by
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
private theorem cert_shr5_toNat (x : BitVec 32) : (x >>> 5#32).toNat = x.toNat / 32 := by
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
private theorem cert_getElemD {α : Type} {xs : List α} {i : Nat} (hi : i < xs.length) (d : α) :
    xs[i]?.getD d = xs[i] := by rw [List.getElem?_eq_getElem hi, Option.getD_some]

private abbrev certL1Inv (c : FullCfg) (s : FullState) (R : Mem 64 → Prop) (mv_nat : Nat)
    (nv : BitVec 32) (tmk exp : List (BitVec 32)) (m_n : Mem 64) : Prop :=
  nv.toNat ≤ mv_nat ∧ nv.toNat ≤ s.core.cur_vars ∧ tmk.length = 2 * c.max_vars ∧
  exp.length = 2 * c.max_vars ∧ certExportOk s.core.cur_vars nv.toNat tmk exp ∧
  (Full.FullMem c (certMkState s s.core.tmp exp tmk s.scratch.scratch_buf) ⋆ R) m_n

private abbrev certL2Inv (c : FullCfg) (s : FullState) (R : Mem 64 → Prop) (L : K6Layout)
    (P : (Nat → Bool) → Prop) (nv : BitVec 32) (exp tmk : List (BitVec 32)) (ok2 : Bool)
    (tmp' scr' : List (BitVec 32)) (m' : Mem 64) : Prop :=
  tmp'.length = c.max_vars ∧ scr'.length = c.scratch_cap ∧
  (∀ i < 4192, scr'[i]? = s.scratch.scratch_buf[i]?) ∧
  (ok2 = true → K6Inv L P (k6StateOfScratch L scr') ∧ K6TrailSynced (k6StateOfScratch L scr') ∧
    (k6StateOfScratch L scr').lvl = 0#32 ∧ (k6StateOfScratch L scr').nv = nv ∧
    k6AssumpLitsS L scr' = []) ∧
  (Full.FullMem c (certMkState s tmp' exp tmk scr') ⋆ R) m'

private def certUndoTmkExpr (pExp pTmk : BitVec 64) (nv : BitVec 32)
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

private theorem cert_undo_tmk_wp (Γ : Env) (Q : Post [.bool]) (X : XPost)
    (c : FullCfg) (F0 : Std.Sat.CNF Nat) (F_cur : List (List Nat))
    (s s_base : FullState) (R : Mem 64 → Prop) (tmp exp tmk scr : List (BitVec 32))
    (nv : BitVec 32) (m0 : Mem 64) (k : Expr Val Cont [.bool]) (_hinv : FullDenseInvW c F0 F_cur s)
    (hdw : FullDenseInvW c F0 F_cur (certMkState s_base tmp exp tmk scr))
    (hnv_cv : nv.toNat ≤ s.core.cur_vars) (hs_cv : s_base.core.cur_vars = s.core.cur_vars)
    (hcv_le : s.core.cur_vars ≤ c.max_vars) (_hmaxv32 : c.max_vars < 2 ^ 32)
    (htmp_len : tmp.length = c.max_vars) (hexp_len : exp.length = 2 * c.max_vars)
    (htmk_len : tmk.length = 2 * c.max_vars) (hscr_len : scr.length = c.scratch_cap)
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
      unfold certMkState; exact m8_fullDenseInvW_def hdw htmp_len hexp_len htmk'_len hscr_len
    exact hk tmk' m' htmk'_len htmkF hinvF hm'

private def certFinishUnitExpr (pHdr pVals : BitVec 64) (unit : BitVec 32) :
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

private theorem cert_finish_unit_wp (Γ : Env) (Q : Post [.bool]) (X : XPost)
    (hAssign : ∀ a m Q X, Full.fullAssignLvlSpec a m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] a m Q X)
    (c : FullCfg) (F0 : Std.Sat.CNF Nat) (F_cur : List (List Nat))
    (s_cur : FullState) (R : Mem 64 → Prop) (unit : BitVec 32) (m_cur : Mem 64)
    (hinv_cur : FullDenseInvW c F0 F_cur s_cur) (htmk_cur : TmkZero s_cur)
    (hunit : unit.toNat < 2 * s_cur.core.cur_vars)
    (hentU : (cnfOfClauses F_cur).EntailsClause (cnfClause [unit.toNat]))
    (hm_cur : (Full.FullMem c s_cur ⋆ R) m_cur)
    (hQ_ok : ∀ (s' : FullState) (m' : Mem 64), FullDenseInvW c F0 F_cur s' → TmkZero s' →
      s'.core.cur_vars = s_cur.core.cur_vars → s'.core.arena = s_cur.core.arena →
      s'.core.arena_len = s_cur.core.arena_len → s'.core.fuel = s_cur.core.fuel →
      s'.scratch.scratch_buf = s_cur.scratch.scratch_buf →
      (Full.FullMem c s' ⋆ R) m' → Q (true, ()) m') :
    wp Γ Q X (certFinishUnitExpr c.hdr c.pVals unit) m_cur := by
  have hunit_len : (BitVec.zeroExtend 64 unit).toNat < s_cur.core.vals.length := by
    have hvl := hinv_cur.1.core_ok.vals_len; have hcv := hinv_cur.1.core_ok.cur_vars_le
    rw [cert_zext64_toNat]; omega
  unfold certFinishUnitExpr; c0_hsteps_nogrp
  refine wp_join_state (α := FullState) (fun _ => ())
    (fun s3 m3 => FullDenseInvW c F0 F_cur s3 ∧ TmkZero s3 ∧
      s3.core.cur_vars = s_cur.core.cur_vars ∧ s3.core.arena = s_cur.core.arena ∧
      s3.core.arena_len = s_cur.core.arena_len ∧ s3.core.fuel = s_cur.core.fuel ∧
      s3.scratch.scratch_buf = s_cur.scratch.scratch_buf ∧ (Full.FullMem c s3 ⋆ R) m3)
    (fun J_u s3 m3 ⟨hinv3, htmk3, hcv3, har3, hal3, hfl3, hscr3, hm3⟩ => by
      c0_hsteps; exact hQ_ok s3 m3 hinv3 htmk3 hcv3 har3 hal3 hfl3 hscr3 hm3)
    (fun J_u hJu => by
      c0_hsteps_nogrp
      · have hu' : unit.toNat < s_cur.core.vals.length := by rwa [cert_zext64_toNat] at hunit_len
        have hvu255 : s_cur.core.vals[unit.toNat]?.getD 0#8 = 255#8 := by
          have hdom := hinv_cur.2.1.vals_domain unit.toNat hunit
          rw [List.getElem?_eq_getElem hu'] at hdom ⊢
          first | exact cert_i8_slt0_eq_255 _ hdom hc | exact cert_i8_slt_zero_eq_255 _ hdom hc
        have hinv3 := cert_denseInvW_set_inconsistent hinv_cur (cert_lvl0_unit_contra_unsat hentU
          (cert_lvl0_false_entails hinv_cur.2.1 hinv_cur.2.2.2.2.2.1 hunit hvu255))
        c0_hsteps; exact hJu { s_cur with core := { s_cur.core with inconsistent := 1#64 } } _
          ⟨hinv3, htmk_cur, rfl, rfl, rfl, rfl, rfl, by assumption⟩
      · c0_hsteps_nogrp
        refine wp_join_state (α := FullState) (fun _ => ())
          (fun s3 m3 => FullDenseInvW c F0 F_cur s3 ∧ TmkZero s3 ∧
            s3.core.cur_vars = s_cur.core.cur_vars ∧ s3.core.arena = s_cur.core.arena ∧
            s3.core.arena_len = s_cur.core.arena_len ∧ s3.core.fuel = s_cur.core.fuel ∧
            s3.scratch.scratch_buf = s_cur.scratch.scratch_buf ∧ (Full.FullMem c s3 ⋆ R) m3)
          (fun J_u2 s3 m3 hst3 => by c0_hsteps; exact hJu s3 m3 hst3)
          (fun J_u2 hJu2 => by
            c0_hsteps
            · have hu' : unit.toNat < s_cur.core.vals.length := by
                rwa [cert_zext64_toNat] at hunit_len
              have hvu0 : s_cur.core.vals[unit.toNat]?.getD 0#8 = 0#8 := by
                rw [List.getElem?_eq_getElem hu']; exact hc
              have htr_lt : s_cur.core.trail_end < c.max_vars :=
                Nat.lt_of_lt_of_le (cert_trail_end_lt_of_val0 hinv_cur.2.1
                  hinv_cur.1.core_ok.trail_end_le hunit hvu0) hinv_cur.1.core_ok.cur_vars_le
              fid_call hAssign; dsimp only [vals, Arg.val]
              refine ⟨c, s_cur, R, rfl, hinv_cur.1, hm_cur, ?_⟩
              have hno : ¬ (s_cur.core.cur_vars ≤ unit.toNat / 2 ∨
                  c.max_vars ≤ s_cur.core.trail_end ∨
                  s_cur.core.vals[unit.toNat]?.getD 0#8 ≠ 0#8) := by
                rw [hvu0]; simp only [ne_self_iff_false, or_false]; omega
              rw [ite_eq_right (fun h => absurd h hno)]; dsimp only
              intro flags' unass' phases' m3 hfl hlph hm3
              simp only [show ((0 : BitVec 32) = 0#32) = True from eq_true rfl, ↓reduceIte] at hm3 ⊢
              have hp_dens := @assignLvl0_preserves_denseInvW c F0 F_cur s_cur hinv_cur
                unit flags' unass' (s_cur.core.unflushed + 1#64) phases' hfl hlph hunit hvu0 hentU
              c0_hsteps; exact hJu2 _ m3 ⟨hp_dens.1, htmk_cur, rfl, rfl, rfl, rfl, rfl, hm3⟩
            · exact hJu2 s_cur m_cur ⟨hinv_cur, htmk_cur, rfl, rfl, rfl, rfl, rfl, hm_cur⟩))

private def certPostLoop2Expr (pHdr pVals : BitVec 64) (unit : BitVec 32)
    (ok2 : Bool) : Expr Val Cont [.bool] :=
  Expr.jnz (Arg.var ok2)
    (Expr.let_ ⟨OpCode.zext 32 64, (Arg.imm 1000000, ())⟩ fun p1 =>
     Expr.call (as := [i64, i64]) (bs := [i64]) "full_k6_solve"
       (Arg.var pHdr, Arg.var p1.fst, ()) fun p2 =>
     Expr.let_ ⟨OpCode.cmp CmpOp.ne i64 Ty.bool rfl, (Arg.var p2.fst, Arg.imm 20, ())⟩ fun p3 =>
     Expr.jnz (Arg.var p3.fst) (Expr.ret (Arg.imm false, ())) (certFinishUnitExpr pHdr pVals unit))
    (Expr.ret (Arg.imm false, ()))

private def certLoop2LargeExpr (Js : Cont [.bool, .bool, i32, i32])
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

private theorem cert_list_getElem_eq {α : Type} {xs ys : List α} {i j : Nat}
    (hxy : xs = ys) (hij : i = j) (hi : i < xs.length) (_hj : j < ys.length) :
    xs[i] = ys[j] := by subst hxy; subst hij; rfl

private theorem cert_packed_lit_toNat (loc l : BitVec 32)
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

private theorem cert_loop2_large_wp (Γ : Env) (Q : Post [.bool]) (X : XPost)
    (Js : Cont [.bool, .bool, i32, i32]) (c : FullCfg) (F0 : Std.Sat.CNF Nat)
    (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop)
    (tmp' exp tmk scr' : List (BitVec 32)) (w lsz unit nv max_csz : BitVec 32) (ok2 : Bool)
    (P : (Nat → Bool) → Prop) (m' : Mem 64)
    (hP : P = certModelSet F_cur exp nv.toNat unit.toNat) (hok2_t : ok2 = true)
    (hinv : FullDenseInvW c F0 F_cur s) (htmp'_len : tmp'.length = c.max_vars)
    (_hexp_len : exp.length = 2 * c.max_vars) (htmk_len : tmk.length = 2 * c.max_vars)
    (_hscr'_len : scr'.length = c.scratch_cap) (_hcur_pos : 0 < s.core.cur_vars)
    (hmaxv_pos : 0 < c.max_vars) (hnv_mv : nv.toNat ≤ k6MaxV c.scratch_cap)
    (hmv_le : k6MaxV c.scratch_cap ≤ 8192) (hnv_cv : nv.toNat ≤ s.core.cur_vars)
    (hmcsz_pos : 0 < max_csz.toNat) (hmcsz_le : max_csz.toNat ≤ c.max_vars)
    (_hmcsz_lt : max_csz.toNat < 2 ^ 32) (hok : certExportOk s.core.cur_vars nv.toNat tmk exp)
    (hwref : w.toNat ∈ fullArenaClauseRefs s)
    (hwgarb : fullArenaClauseGarbCore s.core w.toNat = false)
    (hlsz_eq : lsz.toNat = fullArenaClauseSizeCore s.core w.toNat)
    (hlsz_bound : w.toNat + 3 + lsz.toNat ≤ s.core.arena.length) (hlsz_lt_29 : lsz.toNat < 2 ^ 29)
    (hm' : (Full.FullMem c (certMkState s tmp' exp tmk scr') ⋆ R) m')
    (hB3 : ∀ bst : Bool × Bool × BitVec 32 × BitVec 32 × List (BitVec 32) × Mem 64,
      ∀ m2_in : Mem 64,
      (match bst with
       | (ok2_l, sat2, csz2, _, tmp2, m_n) => m2_in = m_n ∧ tmp2.length = c.max_vars ∧
         (ok2_l = true → sat2 = false → csz2.toNat ≤ max_csz.toNat ∧
           (∀ j < csz2.toNat, (tmp2[j]?.getD 0#32).toNat < 2 * nv.toNat) ∧
           SemEntails P (List.map BitVec.toNat (List.take csz2.toNat tmp2))) ∧
         (Full.FullMem c (certMkState s tmp2 exp tmk scr') ⋆ R) m_n) →
      Js (match bst with | (ok2_l, sat2, csz2, k2, _, _) => (ok2_l, sat2, csz2, k2, ())) m2_in) :
    wp Γ Q X (certLoop2LargeExpr Js c.pArena c.pVals c.pTarjanMark c.pTmp w lsz unit nv max_csz ok2)
      m' := by
  subst hP; subst hok2_t
  let clits := fullArenaClauseLits s w.toNat
  have hcl_ent := hinv.2.1.arena.entails w.toNat hwref hwgarb
  have hcl_lt := hinv.2.1.arena.lits_lt w.toNat hwref hwgarb
  have hcl_len : clits.length = lsz.toNat := by
    simp [clits, fullArenaClauseLitsCore, hlsz_eq]; omega
  have hcv_le := hinv.1.core_ok.cur_vars_le; have hvals_len := hinv.1.core_ok.vals_len
  unfold certLoop2LargeExpr
  refine wp_while_state (fun st : BitVec 32 × BitVec 32 × List (BitVec 32) => (st.1, st.2.1, ()))
    (fun (_, k, _) => lsz.toNat - k.toNat)
    (fun (csz2, k, tmp2) m2_in => k.toNat ≤ lsz.toNat ∧ csz2.toNat ≤ max_csz.toNat ∧
      tmp2.length = c.max_vars ∧ (∀ j < csz2.toNat, (tmp2[j]?.getD 0#32).toNat < 2 * nv.toNat) ∧
      (∀ β, certModelSet F_cur exp nv.toNat unit.toNat β →
        ∀ α, (cnfOfClauses F_cur).Sat α → ¬ (cnfClause [unit.toNat]).Sat α →
        (∀ i < nv.toNat, β i = α (exp[i]?.getD 0#32).toNat) →
        (∃ p < k.toNat, (cnfClause [clits[p]?.getD 0]).Sat α) →
        ∃ j < csz2.toNat, (cnfClause [(tmp2[j]?.getD 0#32).toNat]).Sat β) ∧
      (Full.FullMem c (certMkState s tmp2 exp tmk scr') ⋆ R) m2_in)
    (fun L3 hL3 => by
      c0_hsteps; exact hL3 (0#32, 0#32, tmp') m' ⟨Nat.zero_le _, Nat.zero_le _, htmp'_len,
        fun _ hj => absurd hj (Nat.not_lt_zero _),
        fun _ _ _ _ _ _ ⟨_, hp, _⟩ => absurd hp (Nat.not_lt_zero _), hm'⟩)
    (fun L3 (csz2, k, tmp2) m2_in ⟨hk_le, hcsz_le, htmp2_len, hlts, hsat_ih, hm2_mem⟩ ih => ?_)
  c0_hsplit
  · have hk_lt : k.toNat < lsz.toNat := by c0_bound
    have hw32 : w.toNat < 2 ^ 32 := w.isLt; have hk32 : k.toNat < 2 ^ 32 := k.isLt
    have har_idx_eq : (BitVec.zeroExtend 64 w + 3#64 + BitVec.zeroExtend 64 k).toNat =
        w.toNat + 3 + k.toNat := by
      rw [BitVec.toNat_add, BitVec.toNat_add, cert_zext64_toNat, cert_zext64_toNat,
        show (3#64 : BitVec 64).toNat = 3 from rfl, Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)]
    have har_idx_lt : (BitVec.zeroExtend 64 w + 3#64 + BitVec.zeroExtend 64 k).toNat <
        s.core.arena.length := by rw [har_idx_eq]; omega
    let q := s.core.arena[w.toNat + 3 + k.toNat]
    have har_eq2 : (certMkState s tmp2 exp tmk scr').core.arena[(BitVec.zeroExtend 64 w + 3#64 +
        BitVec.zeroExtend 64 k).toNat] = q :=
      cert_list_getElem_eq (certMkState_arena ..) har_idx_eq
        (by rw [certMkState_arena]; exact har_idx_lt) (by omega)
    have hq_cl : clits[k.toNat]? = some q.toNat := by
      have hidx_ar : w.toNat + 3 + k.toNat < s.core.arena.length := by omega
      simp [clits, fullArenaClauseLitsCore, ← hlsz_eq, hk_lt, List.getElem?_drop,
        List.getElem?_eq_getElem hidx_ar, q]
    have hq_lt : q.toNat < 2 * s.core.cur_vars := hcl_lt q.toNat (List.mem_of_getElem? hq_cl)
    have hq_len : (BitVec.zeroExtend 64 ((certMkState s tmp2 exp tmk scr').core.arena[
        (BitVec.zeroExtend 64 w + 3#64 + BitVec.zeroExtend 64 k).toNat])).toNat <
        (certMkState s tmp2 exp tmk scr').core.vals.length := by
      rw [certMkState_vals, har_eq2, cert_zext64_toNat]; exact Nat.lt_of_lt_of_le hq_lt (by omega)
    have hidx_mod : (w.toNat + BitVec.toNat (3#64) + k.toNat) % 2 ^ 64 =
        w.toNat + 3 + k.toNat := by
      rw [show BitVec.toNat (3#64) = 3 from rfl, Nat.mod_eq_of_lt (by omega)]
    have har_mod_lt : (w.toNat + BitVec.toNat (3#64) + k.toNat) % 2 ^ 64 <
        s.core.arena.length := by rw [hidx_mod]; omega
    let q_mod := s.core.arena[(w.toNat + BitVec.toNat (3#64) + k.toNat) % 2 ^ 64]'har_mod_lt
    have hq_ar_eq : q_mod = q := cert_list_getElem_eq rfl hidx_mod har_mod_lt (by omega)
    have hu_eq := cert_shr1_toNat q
    have hq_mod_div : q_mod.toNat / 2 < tmk.length := by rw [hq_ar_eq]; omega
    have hq_mod_lt : q_mod.toNat < s.core.vals.length := by rw [hq_ar_eq]; omega
    have hu_lt_tmk : (BitVec.zeroExtend 64 ((certMkState s tmp2 exp tmk scr').core.arena[
        (BitVec.zeroExtend 64 w + 3#64 + BitVec.zeroExtend 64 k).toNat] >>> 1#32)).toNat <
        tmk.length := by rw [har_eq2, cert_zext64_toNat, hu_eq]; omega
    have hFail3 : Js (false, false, csz2, k, ()) m2_in :=
      hB3 (false, false, csz2, k, tmp2, m2_in) m2_in
        ⟨rfl, htmp2_len, fun hc => absurd hc (by decide), hm2_mem⟩
    have hStepKeep : (∀ α, (cnfOfClauses F_cur).Sat α → ¬ (cnfClause [unit.toNat]).Sat α →
          ¬ (cnfClause [q.toNat]).Sat α) → L3 (csz2, k + 1#32, ()) m2_in := fun hq_false =>
      ih (csz2, k + 1#32, tmp2) m2_in (by simp [BitVec.toNat_add]; omega)
        ⟨by simp [BitVec.toNat_add]; omega, hcsz_le, htmp2_len, hlts,
         fun β hPβ α hsat hnu hmap ⟨p, hp, hps⟩ => by
           have hk1 : (k + 1#32).toNat = k.toNat + 1 := by simp [BitVec.toNat_add]; omega
           rw [hk1] at hp; by_cases hpk : p = k.toNat
           · subst hpk; rw [show clits[k.toNat]?.getD 0 = q.toNat by simp [hq_cl]] at hps
             exact absurd hps (hq_false α hsat hnu)
           · exact hsat_ih β hPβ α hsat hnu hmap ⟨p, by omega, hps⟩, hm2_mem⟩
    c0_hsteps
    · exact hB3 (true, true, csz2, k, tmp2, m2_in) m2_in
        ⟨rfl, htmp2_len, fun _ hc => absurd hc (by decide), hm2_mem⟩
    · exact hFail3
    · exact hFail3
    · exact hFail3
    · have hcsz_lt : csz2.toNat < max_csz.toNat := by c0_bound
      have hcsz_tmp_lt : (BitVec.zeroExtend 64 csz2).toNat < tmp2.length := by
        rw [cert_zext64_toNat]; omega
      have hloc_ar : tmk[q_mod.toNat / 2]'hq_mod_div = tmk[q.toNat / 2] :=
        cert_list_getElem_eq rfl (by rw [hq_ar_eq]) hq_mod_div (by omega)
      have hloc_nz : tmk[q.toNat / 2] ≠ 0#32 := by rw [← hloc_ar]; dsimp only [q_mod]; c0_bound
      have hloc_le : tmk[q.toNat / 2].toNat ≤ nv.toNat := by
        rw [← hloc_ar]; dsimp only [q_mod]; c0_bound
      have hget_loc := cert_getElemD (by omega : q.toNat / 2 < tmk.length) 0#32
      have hok_q := hok.1 (q.toNat / 2) (by omega) (by rwa [hget_loc])
      have hloc1 : 1 ≤ tmk[q.toNat / 2].toNat := by rw [← hget_loc]; exact hok_q.1
      let loc := tmk[(q >>> 1#32).toNat]
      have hloc_eq : loc = tmk[q.toNat / 2] :=
        cert_list_getElem_eq rfl hu_eq (by rw [hu_eq]; omega) (by omega)
      let ml := ((loc - 1#32) <<< 1#32) ||| (q &&& 1#32)
      let tmp2' := tmp2.set (BitVec.zeroExtend 64 csz2).toNat ml
      have htmp2'_eq : tmp2' = tmp2.set csz2.toNat ml := by
        dsimp only [tmp2']; rw [cert_zext64_toNat]
      have hml_toNat : ml.toNat = 2 * (loc.toNat - 1) + q.toNat % 2 :=
        cert_packed_lit_toNat loc q (by rw [hloc_eq]; exact hloc1) (by rw [hloc_eq]; omega)
      have hml_lt : ml.toNat < 2 * nv.toNat := by rw [hml_toNat, hloc_eq]; omega
      refine ih (csz2 + 1#32, k + 1#32, tmp2') _ (by simp [BitVec.toNat_add]; omega)
        ⟨by simp [BitVec.toNat_add]; omega, by simp [BitVec.toNat_add]; omega,
         by rw [htmp2'_eq, List.length_set]; exact htmp2_len,
         fun j hj => by
           have hcsz1 : (csz2 + 1#32).toNat = csz2.toNat + 1 := by simp [BitVec.toNat_add]; omega
           rw [hcsz1] at hj; rw [htmp2'_eq]
           by_cases hjc : j = csz2.toNat
           · subst hjc
             rw [List.getElem?_set_self
               (by rw [← cert_zext64_toNat csz2]; exact hcsz_tmp_lt), Option.getD_some]
             exact hml_lt
           · rw [List.getElem?_set_ne (Ne.symm hjc)]; exact hlts j (by omega),
         fun β hPβ α hsat hnu hmap ⟨p, hp, hps⟩ => by
           have hk1 : (k + 1#32).toNat = k.toNat + 1 := by simp [BitVec.toNat_add]; omega
           rw [hk1] at hp
           by_cases hpk : p = k.toNat
           · subst hpk
             have hpeq : clits[k.toNat]?.getD 0 = q.toNat := by rw [hq_cl, Option.getD_some]
             rw [hpeq] at hps
             have hexp_loc : (exp[loc.toNat - 1]?.getD 0#32).toNat = q.toNat / 2 := by
               rw [← show tmk[q.toNat / 2]?.getD 0#32 = loc from hloc_eq ▸ hget_loc]
               exact hok_q.2.2
             refine ⟨csz2.toNat, by simp [BitVec.toNat_add]; omega, ?_⟩
             rw [htmp2'_eq, List.getElem?_set_self (by omega), Option.getD_some]
             exact cert_mapped_lit_sat (hloc_eq ▸ hloc1) (hloc_eq ▸ hloc_le)
               hexp_loc hmap (by rw [hml_toNat]; omega) (by rw [hml_toNat]; omega) hps
           · rcases hsat_ih β hPβ α hsat hnu hmap ⟨p, by omega, hps⟩ with ⟨j, hj, hjs⟩
             refine ⟨j, by simp [BitVec.toNat_add]; omega, ?_⟩
             rw [htmp2'_eq, List.getElem?_set_ne (by omega : csz2.toNat ≠ j)]; exact hjs,
         by
           have har_sw : (certMkState s tmp2 exp tmk scr').core.arena[(BitVec.setWidth 64 w + 3 +
               BitVec.setWidth 64 k).toNat] = q := har_eq2
           have htm_ar : (certMkState s tmp2 exp tmk scr').scratch.tarjan_mark[(BitVec.setWidth 64
               ((certMkState s tmp2 exp tmk scr').core.arena[(BitVec.setWidth 64 w + 3 +
                 BitVec.setWidth 64 k).toNat] >>> OfNat.ofNat 1)).toNat] = loc :=
             cert_list_getElem_eq (certMkState_tmk s tmp2 exp tmk scr')
               (by rw [har_sw, cert_zext64_toNat]; rfl)
               (by rw [certMkState_tmk]; exact hu_lt_tmk) (by rw [hu_eq]; omega)
           have hm0 := hm; simp only [htm_ar] at hm0; rw [har_sw] at hm0; exact hm0⟩
    · have hvq255 : s.core.vals[q.toNat]?.getD 0#8 = 255#8 := by
        have hvs_eq : s.core.vals[q_mod.toNat]'hq_mod_lt = s.core.vals[q.toNat] :=
          cert_list_getElem_eq rfl (by rw [hq_ar_eq]) hq_mod_lt (by omega)
        have hns : (0#8 : BitVec 8).slt s.core.vals[q.toNat] = false := by
          rw [← hvs_eq]; dsimp only [q_mod]; c0_bound
        have hne : s.core.vals[q.toNat] ≠ 0#8 := by rw [← hvs_eq]; dsimp only [q_mod]; c0_bound
        have hdom := hinv.2.1.vals_domain q.toNat hq_lt
        rw [List.getElem?_eq_getElem (by omega : q.toNat < s.core.vals.length)] at hdom ⊢
        exact cert_i8_dom_255_bv8 _ hdom hns hne
      have hneg_q := cert_lvl0_false_entails hinv.2.1 hinv.2.2.2.2.2.1 hq_lt hvq255
      exact hStepKeep fun α hsat _ hqs => by
        rw [CNF.entails_clause_def] at hneg_q; have hcx := hneg_q α hsat
        rw [cert_clause_sat_xor_neg] at hcx; exact hcx hqs
    · have hqu : q.toNat = unit.toNat := by
        have hqeq : q_mod = unit := by dsimp only [q_mod]; c0_bound
        rw [hq_ar_eq] at hqeq; exact congrArg BitVec.toNat hqeq
      exact hStepKeep fun _ _ hnu hqs => hnu (hqu ▸ hqs)
  · have hk_eq : k.toNat = lsz.toNat := by c0_bound
    refine hB3 (true, false, csz2, k, tmp2, m2_in) m2_in
      ⟨rfl, htmp2_len, fun _ _ => ⟨hcsz_le, hlts, ?_⟩, hm2_mem⟩
    intro β ⟨α, hsat, hnu, hmap⟩
    rcases cert_entails_in_modelSet hcl_ent hsat hnu with ⟨q, hqm, _, hqs⟩
    rcases List.mem_iff_getElem.mp hqm with ⟨p, hplen, hpeq⟩
    rcases hsat_ih β ⟨α, hsat, hnu, hmap⟩ α hsat hnu hmap
      ⟨p, by rw [hk_eq, ← hcl_len]; exact hplen, by rw [cert_getElemD hplen, hpeq]; exact hqs⟩
      with ⟨j, hj, hjs⟩
    rw [cert_clause_sat_iff_mem]
    exact ⟨(tmp2[j]?.getD 0#32).toNat, List.mem_map.mpr ⟨tmp2[j]?.getD 0#32,
      List.mem_take_iff_getElem.mpr ⟨j, by rw [htmp2_len]; omega,
        (cert_getElemD (by omega : j < tmp2.length) 0#32).symm⟩, rfl⟩, hjs⟩

private theorem cert_export_add_bv {cur_vars max_vars : Nat} {nv u : BitVec 32}
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

private def certLoop1LargeExpr (Js : Cont [i32, .bool, .bool, i32, i32])
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

private def certLoop1Expr (Js : Cont [i32, .bool, .bool, i32])
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
      (Expr.jump Js
        (Arg.var p11.fst, Arg.imm false, Arg.var p11.snd.fst, Arg.var p11.snd.snd.fst, ())))
    Blocks.nil) fun Js1 => Expr.jump Js1.fst (Arg.imm 0, Arg.imm false, Arg.imm 0, ())

private theorem cert_loop1_large_wp (Γ : Env) (Q : Post [.bool]) (X : XPost)
    (Js : Cont [i32, .bool, .bool, i32, i32]) (c : FullCfg) (F0 : Std.Sat.CNF Nat)
    (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop) (exp tmk : List (BitVec 32))
    (w lsz unit nv mv : BitVec 32) (ab : Bool) (m' : Mem 64)
    (hinv : FullDenseInvW c F0 F_cur s) (hexp_len : exp.length = 2 * c.max_vars)
    (htmk_len : tmk.length = 2 * c.max_vars) (hmaxv_lt : c.max_vars < 2 ^ 32)
    (hnv_mv : nv.toNat ≤ mv.toNat) (hnv_cv : nv.toNat ≤ s.core.cur_vars)
    (hok : certExportOk s.core.cur_vars nv.toNat tmk exp) (hwref : w.toNat ∈ fullArenaClauseRefs s)
    (hwgarb : fullArenaClauseGarbCore s.core w.toNat = false)
    (hlsz_eq : lsz.toNat = fullArenaClauseSizeCore s.core w.toNat)
    (hlsz_bound : w.toNat + 3 + lsz.toNat ≤ s.core.arena.length) (hlsz_lt_29 : lsz.toNat < 2 ^ 29)
    (hm' : (Full.FullMem c (certMkState s s.core.tmp exp tmk s.scratch.scratch_buf) ⋆ R) m')
    (hB3 : ∀ bst : BitVec 32 × Bool × Bool × BitVec 32 × BitVec 32 ×
        List (BitVec 32) × List (BitVec 32) × Mem 64, ∀ m_in : Mem 64,
      (match bst with
       | (nv', ab', sat', csz', _, tmk', exp', m_n) => m_in = m_n ∧ nv'.toNat ≤ mv.toNat ∧
         nv'.toNat ≤ s.core.cur_vars ∧ tmk'.length = 2 * c.max_vars ∧ exp'.length = 2 * c.max_vars ∧
         certExportOk s.core.cur_vars nv'.toNat tmk' exp' ∧
         (ab' = false → sat' = false → csz' = 0#32 →
           (cnfOfClauses F_cur).EntailsClause (cnfClause [unit.toNat])) ∧
         (Full.FullMem c (certMkState s s.core.tmp exp' tmk' s.scratch.scratch_buf) ⋆ R) m_n) →
      Js (match bst with | (nv', ab', sat', csz', k', _, _, _) => (nv', ab', sat', csz', k', ()))
        m_in) :
    wp Γ Q X (certLoop1LargeExpr Js c.hdr c.pArena c.pVals c.pTarjanMark c.pWsort
      w lsz unit nv mv ab) m' := by
  let clits := fullArenaClauseLits s w.toNat
  have hcl_ent := hinv.2.1.arena.entails w.toNat hwref hwgarb
  have hcl_lt := hinv.2.1.arena.lits_lt w.toNat hwref hwgarb
  have hcl_len : clits.length = lsz.toNat := by
    simp [clits, fullArenaClauseLitsCore, hlsz_eq]; omega
  have hcv_le := hinv.1.core_ok.cur_vars_le; have hvals_len := hinv.1.core_ok.vals_len
  unfold certLoop1LargeExpr
  refine wp_while_state (fun st : BitVec 32 × BitVec 32 × BitVec 32 ×
      List (BitVec 32) × List (BitVec 32) => (st.1, st.2.1, st.2.2.1, ()))
    (fun (_, _, k', _, _) => lsz.toNat - k'.toNat)
    (fun (nv', csz', k', tmk', exp') m_in => k'.toNat ≤ lsz.toNat ∧ csz'.toNat ≤ k'.toNat ∧
      nv'.toNat ≤ mv.toNat ∧ nv'.toNat ≤ s.core.cur_vars ∧ tmk'.length = 2 * c.max_vars ∧
      exp'.length = 2 * c.max_vars ∧ certExportOk s.core.cur_vars nv'.toNat tmk' exp' ∧
      (csz' = 0#32 → ∀ p < k'.toNat, let ql := clits[p]?.getD 0; ql ≠ unit.toNat →
        (cnfOfClauses F_cur).EntailsClause (cnfClause [ql ^^^ 1])) ∧
      (Full.FullMem c (certMkState s s.core.tmp exp' tmk' s.scratch.scratch_buf) ⋆ R) m_in)
    (fun L3 hL3 => by
      c0_hsteps; exact hL3 (nv, 0#32, 0#32, tmk, exp) m' ⟨Nat.zero_le _, Nat.zero_le _, hnv_mv,
        hnv_cv, htmk_len, hexp_len, hok, fun _ _ hp => absurd hp (Nat.not_lt_zero _), hm'⟩)
    (fun L3 (nv', csz', k', tmk', exp') m_in
      ⟨hk_le, hcsz_le, hnv'_mv, hnv'_cv, htmk'_len, hexp'_len, hok', hzero', hm_in⟩ ih => ?_)
  c0_hsplit
  · have hk_lt : k'.toNat < lsz.toNat := by c0_bound
    have hw32 : w.toNat < 2 ^ 32 := w.isLt; have hk32 : k'.toNat < 2 ^ 32 := k'.isLt
    have har_idx_eq : (BitVec.zeroExtend 64 w + 3#64 + BitVec.zeroExtend 64 k').toNat =
        w.toNat + 3 + k'.toNat := by
      rw [BitVec.toNat_add, BitVec.toNat_add, cert_zext64_toNat, cert_zext64_toNat,
        show (3#64 : BitVec 64).toNat = 3 from rfl, Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)]
    have har_idx_lt : (BitVec.zeroExtend 64 w + 3#64 + BitVec.zeroExtend 64 k').toNat <
        (certMkState s s.core.tmp exp' tmk' s.scratch.scratch_buf).core.arena.length := by
      rw [certMkState_arena, har_idx_eq]; omega
    let q := s.core.arena[w.toNat + 3 + k'.toNat]
    have har_eq2 : (certMkState s s.core.tmp exp' tmk' s.scratch.scratch_buf).core.arena[
        (BitVec.zeroExtend 64 w + 3#64 + BitVec.zeroExtend 64 k').toNat] = q :=
      cert_list_getElem_eq (certMkState_arena s s.core.tmp exp' tmk' s.scratch.scratch_buf)
        har_idx_eq (by rw [certMkState_arena]; exact har_idx_eq ▸ by omega) (by omega)
    have hq_cl : clits[k'.toNat]? = some q.toNat := by
      have hi : w.toNat + 3 + k'.toNat < s.core.arena.length := by omega
      simp [clits, fullArenaClauseLitsCore, ← hlsz_eq, hk_lt, List.getElem?_drop,
        List.getElem?_eq_getElem hi, q]
    have hq_lt : q.toNat < 2 * s.core.cur_vars := hcl_lt q.toNat (List.mem_of_getElem? hq_cl)
    have hq_len : (BitVec.zeroExtend 64 ((certMkState s s.core.tmp exp' tmk'
        s.scratch.scratch_buf).core.arena[(BitVec.zeroExtend 64 w + 3#64 +
          BitVec.zeroExtend 64 k').toNat])).toNat <
        (certMkState s s.core.tmp exp' tmk' s.scratch.scratch_buf).core.vals.length := by
      rw [certMkState_vals, har_eq2, cert_zext64_toNat]; exact Nat.lt_of_lt_of_le hq_lt (by omega)
    have hidx_mod : (w.toNat + BitVec.toNat (3#64) + k'.toNat) % 2 ^ 64 =
        w.toNat + 3 + k'.toNat := by
      rw [show BitVec.toNat (3#64) = 3 from rfl, Nat.mod_eq_of_lt (by omega)]
    have har_mod_lt : (w.toNat + BitVec.toNat (3#64) + k'.toNat) % 2 ^ 64 <
        s.core.arena.length := by rw [hidx_mod]; omega
    let q_mod := s.core.arena[(w.toNat + BitVec.toNat (3#64) + k'.toNat) % 2 ^ 64]'har_mod_lt
    have hq_ar_eq : q_mod = q := cert_list_getElem_eq rfl hidx_mod har_mod_lt (by omega)
    have hu_eq := cert_shr1_toNat q
    have hq_mod_lt : q_mod.toNat < s.core.vals.length := by rw [hq_ar_eq]; omega
    c0_hsteps
    · exact hB3 (nv', ab, true, csz', k', tmk', exp', m_in) m_in
        ⟨rfl, hnv'_mv, hnv'_cv, htmk'_len, hexp'_len, hok',
         fun _ hs _ => absurd hs (by decide), hm_in⟩
    · have hu_lt_cv : q.toNat / 2 < s.core.cur_vars := by omega
      have hu_lt_tmk : (BitVec.zeroExtend 64 ((certMkState s s.core.tmp exp' tmk'
          s.scratch.scratch_buf).core.arena[(BitVec.zeroExtend 64 w + 3#64 +
            BitVec.zeroExtend 64 k').toNat] >>> 1#32)).toNat < tmk'.length := by
        rw [har_eq2, cert_zext64_toNat, hu_eq]; omega
      have hcsz_add : (csz' + 1#32).toNat = csz'.toNat + 1 := by simp [BitVec.toNat_add]; omega
      have hcsz_nz : csz' + 1#32 ≠ 0#32 := fun heq => by
        have ht := congrArg BitVec.toNat heq; rw [hcsz_add] at ht; simp at ht
      c0_hsteps
      · exact hB3 (nv', true, false, csz', k', tmk', exp', m_in) m_in
          ⟨rfl, hnv'_mv, hnv'_cv, htmk'_len, hexp'_len, hok',
           fun ha _ _ => absurd ha (by decide), hm_in⟩
      · exact hB3 (nv', true, false, csz', k', tmk', exp', m_in) m_in
          ⟨rfl, hnv'_mv, hnv'_cv, htmk'_len, hexp'_len, hok',
           fun ha _ _ => absurd ha (by decide), hm_in⟩
      · have hnv_lt_mv : nv'.toNat < mv.toNat := by c0_bound
        have hnv_lt_cv : nv'.toNat < s.core.cur_vars := by
          change ¬s.core.cur_vars % 2 ^ 64 ≤ nv'.toNat at hc
          rw [Nat.mod_eq_of_lt (by omega)] at hc; omega
        have hnv_lt_exp : (BitVec.zeroExtend 64 nv').toNat < exp'.length := by
          rw [cert_zext64_toNat]; omega
        have ht0 : tmk'[q.toNat / 2]?.getD 0#32 = 0#32 := by
          have heq0 : tmk'[q_mod.toNat / 2] = 0#32 := by dsimp only [q_mod]; c0_bound
          have hta : tmk'[q_mod.toNat / 2] = tmk'[q.toNat / 2] :=
            cert_list_getElem_eq rfl (by rw [hq_ar_eq]) (by rw [hq_ar_eq]; omega) (by omega)
          rw [hta] at heq0; rw [cert_getElemD (by omega : q.toNat / 2 < tmk'.length)]; exact heq0
        c0_hsteps
        let exp'' := exp'.set (BitVec.zeroExtend 64 nv').toNat (q >>> 1#32)
        let tmk'' := tmk'.set (BitVec.zeroExtend 64 (q >>> 1#32)).toNat (nv' + 1#32)
        have hexp''_eq : exp'' = exp'.set nv'.toNat (q >>> 1#32) := by
          dsimp only [exp'']; rw [cert_zext64_toNat]
        have htmk''_eq : tmk'' = tmk'.set (q.toNat / 2) (nv' + 1#32) := by
          dsimp only [tmk'']; rw [cert_zext64_toNat, hu_eq]
        have hnv1_lt : nv'.toNat + 1 < 2 ^ 32 := by omega
        have hok'' : certExportOk s.core.cur_vars (nv' + 1#32).toNat tmk'' exp'' :=
          cert_export_add_bv hok' hu_lt_cv ht0 hnv_lt_exp
            (by rw [cert_zext64_toNat, hu_eq]; omega) hcv_le hmaxv_lt hnv_lt_cv
        have hsh : q >>> (1 : Nat) = q >>> 1#32 := rfl
        have hnvz : (BitVec.setWidth 64 nv').toNat = nv'.toNat := cert_zext64_toNat nv'
        have hqz : (BitVec.setWidth 64 (q >>> 1#32)).toNat = q.toNat / 2 := by
          rw [cert_zext64_toNat, hu_eq]
        have hm_upd : (Full.FullMem c (certMkState s s.core.tmp exp'' tmk''
            s.scratch.scratch_buf) ⋆ R) m := by
          rw [hexp''_eq, htmk''_eq]; have hm0 := hm; erw [har_eq2, hnvz, hsh, hqz] at hm0; exact hm0
        exact ih (nv' + 1#32, csz' + 1#32, k' + 1#32, tmk'', exp'') m
          (by simp [BitVec.toNat_add]; omega)
          ⟨by simp [BitVec.toNat_add]; omega, by simp [BitVec.toNat_add]; omega,
           by simp [BitVec.toNat_add]; omega, by simp [BitVec.toNat_add]; omega,
           by simp [htmk''_eq, htmk'_len], by simp [hexp''_eq, hexp'_len], hok'',
           fun h => absurd h hcsz_nz, hm_upd⟩
      · exact ih (nv', csz' + 1#32, k' + 1#32, tmk', exp') m_in (by simp [BitVec.toNat_add]; omega)
          ⟨by simp [BitVec.toNat_add]; omega, by simp [BitVec.toNat_add]; omega, hnv'_mv, hnv'_cv,
           htmk'_len, hexp'_len, hok', fun h => absurd h hcsz_nz, hm_in⟩
    · have hvq255 : s.core.vals[q.toNat]?.getD 0#8 = 255#8 := by
        have hvs_eq : s.core.vals[q_mod.toNat]'hq_mod_lt = s.core.vals[q.toNat] :=
          cert_list_getElem_eq rfl (by rw [hq_ar_eq]) hq_mod_lt (by omega)
        have hns : (0#8 : BitVec 8).slt s.core.vals[q.toNat] = false := by
          rw [← hvs_eq]; dsimp only [q_mod]; c0_bound
        have hne : s.core.vals[q.toNat] ≠ 0#8 := by rw [← hvs_eq]; dsimp only [q_mod]; c0_bound
        have hdom := hinv.2.1.vals_domain q.toNat hq_lt
        rw [List.getElem?_eq_getElem (by omega : q.toNat < s.core.vals.length)] at hdom ⊢
        exact cert_i8_dom_255_bv8 _ hdom hns hne
      have hneg_q := cert_lvl0_false_entails hinv.2.1 hinv.2.2.2.2.2.1 hq_lt hvq255
      exact ih (nv', csz', k' + 1#32, tmk', exp') m_in (by simp [BitVec.toNat_add]; omega)
        ⟨by simp [BitVec.toNat_add]; omega, by simp [BitVec.toNat_add]; omega, hnv'_mv, hnv'_cv,
         htmk'_len, hexp'_len, hok', fun h0 p hp => by
           have hk1 : (k' + 1#32).toNat = k'.toNat + 1 := by simp [BitVec.toNat_add]; omega
           rw [hk1] at hp; by_cases hpk : p = k'.toNat
           · subst hpk; dsimp only; intro _
             rw [show clits[k'.toNat]?.getD 0 = q.toNat by simp [hq_cl]]; exact hneg_q
           · exact hzero' h0 p (by omega), hm_in⟩
    · have hqu : q.toNat = unit.toNat := by rw [← hq_ar_eq]; exact congrArg BitVec.toNat hc
      exact ih (nv', csz', k' + 1#32, tmk', exp') m_in (by simp [BitVec.toNat_add]; omega)
        ⟨by simp [BitVec.toNat_add]; omega, by simp [BitVec.toNat_add]; omega, hnv'_mv, hnv'_cv,
         htmk'_len, hexp'_len, hok', fun h0 p hp => by
           have hk1 : (k' + 1#32).toNat = k'.toNat + 1 := by simp [BitVec.toNat_add]; omega
           rw [hk1] at hp; by_cases hpk : p = k'.toNat
           · subst hpk; dsimp only; rw [show clits[k'.toNat]?.getD 0 = q.toNat by simp [hq_cl], hqu]
             intro hne; exact absurd rfl hne
           · exact hzero' h0 p (by omega), hm_in⟩
  · have hk_eq : k'.toNat = lsz.toNat := by c0_bound
    refine hB3 (nv', ab, false, csz', k', tmk', exp', m_in) m_in
      ⟨rfl, hnv'_mv, hnv'_cv, htmk'_len, hexp'_len, hok', fun _ _ hc0 => by
         refine cert_lvl0_clause_unit_entails hcl_ent fun r hr hrnu => ?_
         rcases List.mem_iff_getElem.mp hr with ⟨p, hplen, hpeq⟩
         have h1 := hzero' hc0 p (by rw [hk_eq, ← hcl_len]; exact hplen)
         rw [cert_getElemD hplen, hpeq] at h1; exact h1 hrnu, hm_in⟩

private theorem cert_loop1_wp (Γ : Env) (Q : Post [.bool]) (X : XPost)
    (Js : Cont [i32, .bool, .bool, i32]) (c : FullCfg) (F0 : Std.Sat.CNF Nat)
    (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop)
    (unit side_off side_cnt side_mask mv_sw max_csz : BitVec 32) (m : Mem 64)
    (hmv_toNat : mv_sw.toNat = k6MaxV c.scratch_cap) (hinv : FullDenseInvW c F0 F_cur s)
    (htmk : TmkZero s) (hcap : 16384 ≤ c.scratch_cap) (hmaxv_lt : c.max_vars < 2 ^ 32)
    (hcnt : side_cnt.toNat ≤ 2001) (hoff_cnt : side_off.toNat + side_cnt.toNat ≤ 4002)
    (hmask : side_mask = 4002#32 ∨ side_mask = 4066#32)
    (hent : ∀ i < side_cnt.toNat,
      FullBveEntryOkW F_cur s unit.toNat (s.scratch.scratch_buf[side_off.toNat + i]?.getD 0#32))
    (hm : (Full.FullMem c s ⋆ R) m)
    (hB : ∀ bst : BitVec 32 × Bool × Bool × BitVec 32 × List (BitVec 32) × List (BitVec 32),
      ∀ m'' : Mem 64,
      (match bst with
       | (nv, de, _ab, _, tmk, exp) => certL1Inv c s R (k6MaxV c.scratch_cap) nv tmk exp m'' ∧
         (de = true → (cnfOfClauses F_cur).EntailsClause (cnfClause [unit.toNat]))) →
      Js (match bst with | (nv, de, ab, idx, _, _) => (nv, de, ab, idx, ())) m'') :
    wp Γ Q X (certLoop1Expr Js c.hdr c.pScratchBuf c.pArena c.pVals c.pTarjanMark c.pWsort
      unit side_off side_cnt side_mask mv_sw max_csz) m := by
  let mv_nat := k6MaxV c.scratch_cap
  have hmv_le : mv_nat ≤ 8192 := by
    by_cases hlt : c.scratch_cap < k6MinScr
    · have : mv_nat = 0 := by simp [mv_nat, k6MaxV, hlt]
      omega
    · exact (k6MaxV_bounds (Nat.not_lt.mp hlt)).2.1
  have hbuf_len := hinv.1.scratch_ok.scratch_buf_len; have hcv_le := hinv.1.core_ok.cur_vars_le
  have har_le := hinv.1.core_ok.arena_len_le; have har_arr := hinv.1.core_ok.arena_len_arr
  have har_cap := c.harena; unfold LeanQbe.T.Examples.LratBytes.dimacsBound at har_cap
  unfold certLoop1Expr
  refine wp_while_state
    (α := BitVec 32 × Bool × BitVec 32 × List (BitVec 32) × List (BitVec 32))
    (fun (nv, ab, idx, _, _) => (nv, ab, idx, ()))
    (fun (_, _, idx, _, _) => side_cnt.toNat - idx.toNat)
    (fun (nv, _ab, idx, tmk, exp) m' =>
      idx.toNat ≤ side_cnt.toNat ∧ certL1Inv c s R mv_nat nv tmk exp m')
    (fun L1 hL1 => by
      c0_hsteps; exact hL1 (0#32, false, 0#32, s.scratch.tarjan_mark, s.scratch.wsort) m
        ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, hinv.1.scratch_ok.tarjan_mark_len,
         hinv.1.scratch_ok.wsort_len, cert_export_zero htmk, hm⟩)
    (fun L1 ⟨nv, ab, idx, tmk, exp⟩ m'
      ⟨hidx_le, hnv_mv, hnv_cv, htmk_len, hexp_len, hok, hm'⟩ ih => ?_)
  c0_hsplit
  · have hidx_lt : idx.toNat < side_cnt.toNat := by c0_bound
    c0_hsteps_nogrp
    · exact hB (nv, false, ab, idx, tmk, exp) m'
        ⟨⟨hnv_mv, hnv_cv, htmk_len, hexp_len, hok, hm'⟩, fun h => absurd h (by decide)⟩
    · refine wp_join_state (ts := [i32, .bool, .bool])
        (α := BitVec 32 × Bool × List (BitVec 32) × List (BitVec 32) × Mem 64)
        (fun (nv', ab', _, _, _) => (nv', false, ab', ()))
        (fun (nv', _ab', tmk', exp', m_n) m_in =>
          m_in = m_n ∧ certL1Inv c s R mv_nat nv' tmk' exp' m_n) ?_ ?_
      · rintro J_next ⟨nv', ab', tmk', exp', m_n⟩ m_in ⟨hm_eq, hrest⟩
        rw [hm_eq]; c0_hsteps; exact ih (nv', ab', idx + 1#32, tmk', exp') m_n
          (by simp [BitVec.toNat_add]; omega) ⟨by simp [BitVec.toNat_add]; omega, hrest⟩
      · intro J_next hJnext
        have hmask_idx_lt : (BitVec.zeroExtend 64 (side_mask + (idx >>> 5#32))).toNat <
            s.scratch.scratch_buf.length := by
          have hshr := cert_shr5_toNat idx
          have hm_lt : side_mask.toNat ≤ 4066 := by rcases hmask with rfl | rfl <;> decide
          rw [cert_zext64_toNat, BitVec.toNat_add, hshr]; omega
        c0_hsteps_nogrp
        · have hw_idx_eq : (side_off + idx).toNat = side_off.toNat + idx.toNat := by
            simp [BitVec.toNat_add]; omega
          have hw_idx_lt : (BitVec.zeroExtend 64 (side_off + idx)).toNat <
              s.scratch.scratch_buf.length := by rw [cert_zext64_toNat, hw_idx_eq]; omega
          have hw_idx_lt' : (side_off + idx).toNat < s.scratch.scratch_buf.length := by
            rw [← cert_zext64_toNat]; exact hw_idx_lt
          have hwe : FullBveEntryOkW F_cur s unit.toNat
              (s.scratch.scratch_buf[(side_off + idx).toNat]'hw_idx_lt') := by
            rw [← cert_getElemD hw_idx_lt' 0#32, hw_idx_eq]; exact hent idx.toNat hidx_lt
          c0_hsteps_nogrp
          refine wp_join_state (ts := [i32, .bool, .bool])
            (α := BitVec 32 × Bool × List (BitVec 32) × List (BitVec 32) × Mem 64)
            (fun (nv', ab', _, _, _) => (nv', false, ab', ()))
            (fun (nv', _ab', tmk', exp', m_n) m_in =>
              m_in = m_n ∧ certL1Inv c s R mv_nat nv' tmk' exp' m_n) ?_ ?_
          · rintro J_m ⟨nv', ab', tmk', exp', m_n⟩ m_in ⟨hm_eq, hrest⟩
            rw [hm_eq]; c0_hsteps; exact hJnext (nv', ab', tmk', exp', m_n) m_n ⟨rfl, hrest⟩
          · intro J_m hJm; c0_hsteps_nogrp
            · let w := s.scratch.scratch_buf[(side_off + idx).toNat]'hw_idx_lt'
              have hbit : w &&& 2147483648#32 ≠ 0#32 := by c0_bound
              dsimp only [FullBveEntryOkW] at hwe
              rw [ite_eq_left hbit] at hwe; rcases hwe with ⟨hot_lt, hot_ent⟩
              let ot := w &&& 2147483647#32
              have hot_lt' : ot.toNat < 2 * s.core.cur_vars := hot_lt
              have hscr_ot_eq : (certMkState s s.core.tmp exp tmk
                  s.scratch.scratch_buf).scratch.scratch_buf[
                  (BitVec.zeroExtend 64 (side_off + idx)).toNat] = w :=
                cert_list_getElem_eq (certMkState_buf s s.core.tmp exp tmk s.scratch.scratch_buf)
                  (cert_zext64_toNat _) (by rw [certMkState_buf]; exact hw_idx_lt) hw_idx_lt'
              have hot_len : (BitVec.zeroExtend 64 ((certMkState s s.core.tmp exp tmk
                  s.scratch.scratch_buf).scratch.scratch_buf[(BitVec.zeroExtend 64
                    (side_off + idx)).toNat] &&& 2147483647#32)).toNat <
                  (certMkState s s.core.tmp exp tmk s.scratch.scratch_buf).core.vals.length := by
                have := hinv.1.core_ok.vals_len
                rw [certMkState_vals, hscr_ot_eq, cert_zext64_toNat]
                change ot.toNat < s.core.vals.length; omega
              c0_hsteps_nogrp
              · have hu' : ot.toNat < s.core.vals.length := by
                  have := hinv.1.core_ok.vals_len; omega
                have hvo255 : s.core.vals[ot.toNat]?.getD 0#8 = 255#8 := by
                  have hslt : s.core.vals[ot.toNat].slt 0#8 = true := by
                    dsimp only [ot, w]; c0_bound
                  have hdom := hinv.2.1.vals_domain ot.toNat hot_lt
                  rw [List.getElem?_eq_getElem hu'] at hdom ⊢
                  exact cert_i8_slt0_eq_255 _ hdom hslt
                have hneg := cert_lvl0_false_entails hinv.2.1 hinv.2.2.2.2.2.1 hot_lt hvo255
                exact hB (nv, true, ab, idx, tmk, exp) m'
                  ⟨⟨hnv_mv, hnv_cv, htmk_len, hexp_len, hok, hm'⟩,
                   fun _ => cert_entails_resolve_unit hot_ent hneg⟩
              · have hu_eq := cert_shr1_toNat ot
                have hu_lt_cv : ot.toNat / 2 < s.core.cur_vars := by omega
                have hu_lt_tmk : (BitVec.zeroExtend 64 (ot >>> 1#32)).toNat < tmk.length := by
                  rw [cert_zext64_toNat, hu_eq]; omega
                have hu_lt_tmk_mk : (BitVec.zeroExtend 64 (((certMkState s s.core.tmp exp tmk
                    s.scratch.scratch_buf).scratch.scratch_buf[(BitVec.zeroExtend 64
                      (side_off + idx)).toNat] &&& 2147483647#32) >>> 1#32)).toNat <
                    (certMkState s s.core.tmp exp tmk
                      s.scratch.scratch_buf).scratch.tarjan_mark.length := by
                  rw [certMkState_tmk, hscr_ot_eq]; exact hu_lt_tmk
                c0_hsteps_nogrp
                refine wp_join_state (ts := [i32, .bool])
                  (α := BitVec 32 × Bool × List (BitVec 32) × List (BitVec 32) × Mem 64)
                  (fun (nv', ab', _, _, _) => (nv', ab', ()))
                  (fun (nv', _ab', tmk', exp', m_n) m_in =>
                    m_in = m_n ∧ certL1Inv c s R mv_nat nv' tmk' exp' m_n) ?_ ?_
                · rintro J_b ⟨nv', ab', tmk', exp', m_n⟩ m_in ⟨hm_eq, hrest⟩
                  rw [hm_eq]; c0_hsteps; exact hJm (nv', ab', tmk', exp', m_n) m_n ⟨rfl, hrest⟩
                · intro J_b hJb; c0_hsteps
                  · exact hB (nv, false, true, idx, tmk, exp) m'
                      ⟨⟨hnv_mv, hnv_cv, htmk_len, hexp_len, hok, hm'⟩,
                       fun h => absurd h (by decide)⟩
                  · exact hB (nv, false, true, idx, tmk, exp) m'
                      ⟨⟨hnv_mv, hnv_cv, htmk_len, hexp_len, hok, hm'⟩,
                       fun h => absurd h (by decide)⟩
                  · have hnv_lt_mv : nv.toNat < mv_nat := by c0_bound
                    have hnv_lt_cv : nv.toNat < s.core.cur_vars := by
                      change ¬s.core.cur_vars % 2 ^ 64 ≤ nv.toNat at hc
                      rw [Nat.mod_eq_of_lt (by omega)] at hc; omega
                    have hnv_lt_exp : (BitVec.zeroExtend 64 nv).toNat < exp.length := by
                      rw [cert_zext64_toNat]; omega
                    have ht0 : tmk[ot.toNat / 2]?.getD 0#32 = 0#32 := by
                      have heq0 : tmk[ot.toNat / 2] = 0#32 := by dsimp only [ot, w]; c0_bound
                      rw [cert_getElemD (by omega : ot.toNat / 2 < tmk.length)]; exact heq0
                    c0_hsteps
                    let exp' := exp.set (BitVec.zeroExtend 64 nv).toNat (ot >>> 1#32)
                    let tmk' := tmk.set (BitVec.zeroExtend 64 (ot >>> 1#32)).toNat (nv + 1#32)
                    have hexp'_eq : exp' = exp.set nv.toNat (ot >>> 1#32) := by
                      dsimp only [exp']; rw [cert_zext64_toNat]
                    have htmk'_eq : tmk' = tmk.set (ot.toNat / 2) (nv + 1#32) := by
                      dsimp only [tmk']; rw [cert_zext64_toNat, hu_eq]
                    have hnv1_lt : nv.toNat + 1 < 2 ^ 32 := by omega
                    have hok' := cert_export_add_bv hok hu_lt_cv ht0 hnv_lt_exp
                      (by rw [cert_zext64_toNat, hu_eq]; omega) hcv_le hmaxv_lt hnv_lt_cv
                    have hnv1_eq : (nv + 1#32).toNat = nv.toNat + 1 := by
                      simp [BitVec.toNat_add, Nat.mod_eq_of_lt hnv1_lt]
                    have hsh : (w &&& 2147483647#32) >>> (1 : Nat) = ot >>> 1#32 := rfl
                    have hnvz : (BitVec.setWidth 64 nv).toNat = nv.toNat := cert_zext64_toNat nv
                    have hotz : (BitVec.setWidth 64 (ot >>> 1#32)).toNat = ot.toNat / 2 := by
                      rw [cert_zext64_toNat, hu_eq]
                    have hm_upd : (Full.FullMem c (certMkState s s.core.tmp exp' tmk'
                        s.scratch.scratch_buf) ⋆ R) m := by
                      rw [hexp'_eq, htmk'_eq]; have hm0 := hm
                      erw [hscr_ot_eq, hnvz, hsh, hotz] at hm0; exact hm0
                    exact hJb (nv + 1#32, ab, tmk', exp', m) m
                      ⟨rfl, by rw [hnv1_eq]; omega, by rw [hnv1_eq]; omega,
                       by simp [htmk'_eq, htmk_len], by simp [hexp'_eq, hexp_len], hok', hm_upd⟩
                  · exact hJb (nv, ab, tmk, exp, m') m'
                      ⟨rfl, hnv_mv, hnv_cv, htmk_len, hexp_len, hok, hm'⟩
                  · exact hJb (nv, ab, tmk, exp, m') m'
                      ⟨rfl, hnv_mv, hnv_cv, htmk_len, hexp_len, hok, hm'⟩
            · let w := s.scratch.scratch_buf[(side_off + idx).toNat]'hw_idx_lt'
              have h1 : w &&& 2147483648#32 = 0#32 := by dsimp only [w]; c0_bound
              dsimp only [FullBveEntryOkW] at hwe
              rw [ite_eq_right (fun h => absurd h1 h)] at hwe; rcases hwe with ⟨hwref, hwgarb⟩
              have href_wf := hinv.2.1.arena.refs_wf w.toNat hwref
              have hw3 := href_wf.1; have hn1 := href_wf.2.2.1; have hn2 := href_wf.2.2.2.1
              have h2 : w.toNat < 2 ^ 32 := w.isLt
              have hw_idx_eq : (BitVec.zeroExtend 64 w + 2#64).toNat = w.toNat + 2 := by
                rw [BitVec.toNat_add, cert_zext64_toNat,
                  show (2#64 : BitVec 64).toNat = 2 from rfl, Nat.mod_eq_of_lt (by omega)]
              have hw_len : (BitVec.zeroExtend 64 w + 2#64).toNat < s.core.arena.length := by
                rw [hw_idx_eq]; omega
              c0_hsteps_nogrp
              have hwa2 : w.toNat + 2 < s.core.arena.length := by omega
              let lsz := s.core.arena[w.toNat + 2]'hwa2
              have hlsz_eq : lsz.toNat = fullArenaClauseSizeCore s.core w.toNat := by
                simp [lsz, fullArenaClauseSizeCore, List.getElem?_eq_getElem hwa2]
              have hlsz_bound : w.toNat + 3 + lsz.toNat ≤ s.core.arena.length := by
                rw [hlsz_eq]; omega
              have hlsz_lt_29 : lsz.toNat < 2 ^ 29 := by omega
              refine wp_join_state (ts := [i32, .bool, .bool, i32, i32])
                (α := BitVec 32 × Bool × Bool × BitVec 32 × BitVec 32 ×
                  List (BitVec 32) × List (BitVec 32) × Mem 64)
                (fun (nv', ab', sat', csz', k', _, _, _) => (nv', ab', sat', csz', k', ()))
                (fun (nv', ab', sat', csz', _, tmk', exp', m_n) m_in => m_in = m_n ∧
                  certL1Inv c s R mv_nat nv' tmk' exp' m_n ∧
                  (ab' = false → sat' = false → csz' = 0#32 →
                    (cnfOfClauses F_cur).EntailsClause (cnfClause [unit.toNat]))) ?_ ?_
              · rintro B3 ⟨nv', ab', sat', csz', _, tmk', exp', m_n⟩ m_in ⟨hm_eq, hrest, hent'⟩
                rw [hm_eq]; c0_hsteps
                · exact hB (nv', false, ab', idx, tmk', exp') m_n
                    ⟨hrest, fun h => absurd h (by decide)⟩
                · exact hJm (nv', ab', tmk', exp', m_n) m_n ⟨rfl, hrest⟩
                · exact hB (nv', true, ab', idx, tmk', exp') m_n
                    ⟨hrest, fun _ => hent' (by c0_bound) (by c0_bound) (by c0_bound)⟩
                · exact hB (nv', false, true, idx, tmk', exp') m_n
                    ⟨hrest, fun h => absurd h (by decide)⟩
                · exact hJm (nv', ab', tmk', exp', m_n) m_n ⟨rfl, hrest⟩
              · intro Js4 hB3
                have hgw : (certMkState s s.core.tmp exp tmk
                    s.scratch.scratch_buf).scratch.scratch_buf[
                    (BitVec.setWidth 64 (side_off + idx)).toNat] = w :=
                  cert_list_getElem_eq (certMkState_buf ..) (cert_zext64_toNat _)
                    (by rw [certMkState_buf]; exact hw_idx_lt) hw_idx_lt'
                have hgl : (certMkState s s.core.tmp exp tmk
                    s.scratch.scratch_buf).core.arena[(BitVec.setWidth 64
                      ((certMkState s s.core.tmp exp tmk
                        s.scratch.scratch_buf).scratch.scratch_buf[(BitVec.setWidth 64
                          (side_off + idx)).toNat]) + 2).toNat] = lsz :=
                  cert_list_getElem_eq (certMkState_arena ..) (by erw [hgw, hw_idx_eq])
                    (by rw [certMkState_arena]; erw [hgw, hw_idx_eq]; omega) hwa2
                dsimp -zeta only; erw [hgl, hgw]
                exact cert_loop1_large_wp Γ Q X Js4 c F0 F_cur s R exp tmk w lsz
                  unit nv mv_sw ab m' hinv hexp_len htmk_len hmaxv_lt
                  (by rw [hmv_toNat]; exact hnv_mv) hnv_cv hok hwref hwgarb hlsz_eq
                  hlsz_bound hlsz_lt_29 hm'
                  (fun bst m_in ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ =>
                    hB3 bst m_in
                      ⟨h1, ⟨by rw [hmv_toNat] at h2; exact h2, h3, h4, h5, h6, h8⟩, h7⟩)
        · exact hJnext (nv, ab, tmk, exp, m') m'
            ⟨rfl, hnv_mv, hnv_cv, htmk_len, hexp_len, hok, hm'⟩
  · exact hB (nv, false, ab, idx, tmk, exp) m'
      ⟨⟨hnv_mv, hnv_cv, htmk_len, hexp_len, hok, hm'⟩, fun h => absurd h (by decide)⟩

theorem full_bve_certify_unit_fid_wp (Γ : Env)
    (hMaxV : ∀ a m Q X, FullM6Sweep.m6MaxVSpec a m Q X → Γ "full_m6_max_v" [i64] [i64] a m Q X)
    (hInit : ∀ a m Q X, FullM6Sweep.k6InitSpec a m Q X → Γ "full_k6_init" [i64, i32] [] a m Q X)
    (hAdd : ∀ a m Q X, FullM6Sweep.k6AddClauseSpec a m Q X →
      Γ "full_k6_add_clause" [i64, i64, i32] [.bool] a m Q X)
    (hSolve : ∀ a m Q X, FullM6Sweep.k6SolveSpec a m Q X →
      Γ "full_k6_solve" [i64, i64] [i64] a m Q X)
    (hAssign : ∀ a m Q X, Full.fullAssignLvlSpec a m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] a m Q X) :
    ∀ a m Q X, fidBveCertifyUnitSpec a m Q X →
      Func.wp Γ full_bve_certify_unit_fid_body a m Q X := by
  rintro ⟨h, _v, unit, side_off, side_cnt, side_mask, ⟨⟩⟩ m Q X hspec
  rcases fidBveCertifyUnitSpec_elim hspec with
    ⟨c, F0, F_cur, s, R, rfl, hinv, htmk, hcap, hunit, hcnt, hoff_cnt, hmask, hent, hm, hQ⟩
  unfold full_bve_certify_unit_fid_body Func.wp
  have hcur_pos : 0 < s.core.cur_vars := by omega
  have hmaxv_pos : 0 < c.max_vars := Nat.lt_of_lt_of_le hcur_pos hinv.1.core_ok.cur_vars_le
  have hmaxv_lt : c.max_vars < 2 ^ 32 := by
    have := c.hmaxv; unfold LeanQbe.T.Examples.LratBytes.dimacsBound at this; omega
  have hcap_lt : c.scratch_cap < 2 ^ 64 := by
    have := c.hscr; unfold LeanQbe.T.Examples.LratBytes.dimacsBound at this; omega
  have harena_lt : c.arena_cap < 2 * 2 ^ 28 := by
    have := c.harena; unfold LeanQbe.T.Examples.LratBytes.dimacsBound at this; exact this
  c0_hsteps; fid_call hMaxV; dsimp only [m6MaxVSpec]
  let mv_nat := k6MaxV c.scratch_cap; let mv_sw : BitVec 32 := BitVec.ofNat 32 mv_nat
  have hmv_le : mv_nat ≤ 8192 := by
    by_cases hlt : c.scratch_cap < k6MinScr
    · have : mv_nat = 0 := by simp [mv_nat, k6MaxV, hlt]
      omega
    · exact (k6MaxV_bounds (Nat.not_lt.mp hlt)).2.1
  have hmv64 : BitVec.setWidth 32 (BitVec.ofNat 64 (k6MaxV c.scratch_cap)) = mv_sw := by
    apply BitVec.eq_of_toNat_eq; simp [mv_sw, mv_nat, Nat.mod_eq_of_lt (by omega : mv_nat < 2 ^ 32)]
  have hmv_toNat : mv_sw.toNat = mv_nat := Nat.mod_eq_of_lt (by omega : mv_nat < 2 ^ 32)
  dsimp only [vals, Arg.val]
  rw [show (BitVec.ofNat 64 c.scratch_cap).toNat = c.scratch_cap from Nat.mod_eq_of_lt hcap_lt]
  c0_hsteps_nogrp; rw [hmv64]
  refine wp_join_state1 (fun x : BitVec 32 => x)
    (fun x m' => x.toNat = min c.max_vars 65535 ∧ m' = m)
    (fun J_mcsz max_csz m' ⟨hmcsz, hm_eq⟩ => ?_)
    (fun J_mcsz hJm => by
      c0_hsteps
      · have hlt65 : c.max_vars < 65535 := by c0_bound
        exact hJm (BitVec.truncate 32 (BitVec.ofNat 64 c.max_vars)) m
          ⟨by simp [Nat.mod_eq_of_lt hmaxv_lt]; omega, rfl⟩
      · have hge65 : 65535 ≤ c.max_vars := by c0_bound
        exact hJm 65535#32 m ⟨by simp; omega, rfl⟩)
  rw [hm_eq]; have hmcsz_pos : 0 < max_csz.toNat := by omega
  have hmcsz_le : max_csz.toNat ≤ c.max_vars := by omega
  have hdens_mk : ∀ {tmp exp tmk scr}, tmp.length = c.max_vars → exp.length = 2 * c.max_vars →
      tmk.length = 2 * c.max_vars → scr.length = c.scratch_cap →
      FullDenseInvW c F0 F_cur (certMkState s tmp exp tmk scr) :=
    fun h1 h2 h3 h4 => m8_fullDenseInvW_def hinv h1 h2 h3 h4
  c0_hsteps_nogrp
  refine wp_join_state
    (α := BitVec 32 × Bool × Bool × BitVec 32 × List (BitVec 32) × List (BitVec 32))
    (fun (nv, de, ab, idx, _, _) => (nv, de, ab, idx, ()))
    (fun (nv, de, _ab, _, tmk, exp) m' => certL1Inv c s R mv_nat nv tmk exp m' ∧
      (de = true → (cnfOfClauses F_cur).EntailsClause (cnfClause [unit.toNat]))) ?_ ?_
  · rintro B ⟨nv, de, _ab, idx, tmk, exp⟩ m1
      ⟨⟨hnv_mv, hnv_cv, htmk_len, hexp_len, hok, hm1⟩, hde_ent⟩
    let s1 := certMkState s s.core.tmp exp tmk s.scratch.scratch_buf
    have htmp0 := hinv.1.core_ok.tmp_len_arr; have hbuf0 := hinv.1.scratch_ok.scratch_buf_len
    have hinv1 := hdens_mk htmp0 hexp_len htmk_len hbuf0; c0_hsteps_nogrp
    · have hde_t : de = true := by c0_bound
      refine cert_undo_tmk_wp Γ Q X c F0 F_cur s s R s.core.tmp exp tmk s.scratch.scratch_buf
        nv m1 (certFinishUnitExpr c.hdr c.pVals unit) hinv hinv1 hnv_cv rfl
        hinv.1.core_ok.cur_vars_le hmaxv_lt htmp0 hexp_len htmk_len hbuf0 hok hm1 ?_
      intro tmk' m2 _ htmk2 hinv2 hm2
      refine cert_finish_unit_wp Γ Q X hAssign c F0 F_cur
        (certMkState s s.core.tmp exp tmk' s.scratch.scratch_buf) R unit m2 hinv2 htmk2 hunit
        (hde_ent hde_t) hm2 ?_
      intro s3 m3 hinv3 htmk3 hcv3 har3 hal3 hfl3 hscr3 hm3
      exact hQ true s3 m3 hinv3 htmk3 hcv3 har3 hal3 (hfl3 ▸ Nat.le_refl _)
        (fun i _ => by rw [hscr3, certMkState_buf]) hm3
    · c0_hsteps_nogrp
      refine wp_join0 (fun m' => m' = m1) (fun J_ab m_ab hm_eq => by
          rw [hm_eq]; c0_hsteps_nogrp
          refine cert_undo_tmk_wp Γ Q X c F0 F_cur s s R s.core.tmp exp tmk s.scratch.scratch_buf
            nv m1 (Expr.ret (Arg.imm false, ())) hinv hinv1 hnv_cv rfl hinv.1.core_ok.cur_vars_le
            hmaxv_lt htmp0 hexp_len htmk_len hbuf0 hok hm1 ?_
          intro tmk' m' _ htmkF hinvF hm'; c0_hsteps
          exact hQ false (certMkState s s.core.tmp exp tmk' s.scratch.scratch_buf) m' hinvF htmkF
            rfl rfl rfl (Nat.le_refl _) (fun _ _ => by rw [certMkState_buf]) hm')
        (fun J_ab hJab => by
          c0_hsplit; · exact hJab m1 rfl
          c0_hsplit; · exact hJab m1 rfl
          c0_hsplit; · exact hJab m1 rfl
          c0_hsplit; · exact hJab m1 rfl
          · have hnv_nz : nv ≠ 0#32 := by c0_bound
            have hbase_ge : 4192 ≤ 1280 + 2 * mv_nat := by
              have h1 : ¬ ((1280#32 + (mv_sw <<< 1)).ult 4192#32 = true) := by c0_bound
              have hshl : (mv_sw <<< 1).toNat = 2 * mv_nat := by
                have : (mv_sw <<< 1).toNat = (mv_nat * 2) % 2 ^ 32 := by
                  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, hmv_toNat]
                omega
              have hadd : (1280#32 + (mv_sw <<< 1)).toNat = 1280 + 2 * mv_nat := by
                simp [BitVec.toNat_add, hshl]; omega
              rw [show (1280#32 + (mv_sw <<< 1)).ult 4192#32 =
                decide ((1280#32 + (mv_sw <<< 1)).toNat < 4192) from rfl,
                hadd, decide_eq_true_eq] at h1; omega
            have hmv_nz : mv_nat ≠ 0 := by omega
            have hcap_k6 : k6MinScr ≤ c.scratch_cap := Classical.byContradiction fun hlt =>
              hmv_nz (by simp [mv_nat, k6MaxV, Nat.lt_of_not_le hlt])
            fid_call hInit; dsimp only [vals, Arg.val]; refine ⟨c, s1, R, rfl, hinv1.1, hm1, ?_⟩
            have hcond_false :
                ¬ (c.scratch_cap < k6MinScr ∨ k6MaxV c.scratch_cap < nv.toNat) := by omega
            simp only [hcond_false, ↓reduceIte]
            intro L scr2 m2 hLscr hLmax hlen2 hpres2 hk6inv2 hts2 hknv hnc hlvl hp tr un hin hna
              hst hoc hneq hm2
            have hLbase : 4192 ≤ L.k6Base := by rw [K6Layout.k6Base, hLmax]; exact hbase_ge
            have hpres_4192_2 : ∀ i < 4192, scr2[i]? = s.scratch.scratch_buf[i]? :=
              fun i hi => hpres2 i (by omega)
            let P := certModelSet F_cur exp nv.toNat unit.toNat
            have hna_empty2 : k6AssumpLitsS L scr2 = [] := by
              simp [k6AssumpLitsS, k6AssumpLits, hna]
            c0_hsteps_nogrp
            refine wp_while_break_state
              (β := BitVec 32 × Bool × List (BitVec 32) × List (BitVec 32))
              (fun (idx2, ok, _, _) => (idx2, ok, ()))
              (fun (_idx2, ok2, tmp', scr') m' => certL2Inv c s R L P nv exp tmk ok2 tmp' scr' m')
              (α := BitVec 32 × Bool × List (BitVec 32) × List (BitVec 32))
              (fun (idx2, ok2, _, _) => (idx2, ok2, ()))
              (fun (idx2, _, _, _) => side_cnt.toNat - idx2.toNat)
              (fun (idx2, ok2, tmp', scr') m' => idx2.toNat ≤ side_cnt.toNat ∧
                certL2Inv c s R L P nv exp tmk ok2 tmp' scr' m') ?_ ?_ ?_
            · rintro B ⟨idx2, ok2, tmp3, scr3⟩ m3 ⟨htmp3_len, hscr3_len, hpres3, hk6_3, hm3⟩
              c0_hsteps_nogrp
              refine cert_undo_tmk_wp Γ Q X c F0 F_cur s s R tmp3 exp tmk scr3 nv m3
                (certPostLoop2Expr c.hdr c.pVals unit ok2) hinv
                (hdens_mk htmp3_len hexp_len htmk_len hscr3_len) hnv_cv rfl
                hinv.1.core_ok.cur_vars_le hmaxv_lt htmp3_len hexp_len htmk_len hscr3_len hok hm3 ?_
              intro tmk' m4 htmk'_len htmk4 hinv4 hm4; unfold certPostLoop2Expr; c0_hsteps
              · have hok2_t : ok2 = true := by c0_bound
                rcases hk6_3 hok2_t with ⟨hk6inv3, _, _, _, hna3⟩
                fid_call hSolve; dsimp only [Arg.val]
                refine ⟨c, certMkState s tmp3 exp tmk' scr3, P, L, R, rfl, hinv4.1, hLscr, hLmax,
                  hk6inv3, hm4, ?_⟩
                intro r fl' scr5 m5; dsimp only
                intro hlen5 hfl5 hpres5 hk6inv5 hts5 hnv5 hna5 has5 hneq5 hr huns5 hm5
                let s5 := { certMkState s tmp3 exp tmk' scr3 with
                  core := { (certMkState s tmp3 exp tmk' scr3).core with fuel := fl' }
                  scratch := { (certMkState s tmp3 exp tmk' scr3).scratch with
                    scratch_buf := scr5 } }
                have hinv5 : FullDenseInvW c F0 F_cur s5 :=
                  m8_fullDenseInvW_def (m8_fullDenseInvW_fuel hinv4 fl')
                    htmp3_len hexp_len htmk'_len hlen5.scratch_ok.scratch_buf_len
                have htmk5 : TmkZero s5 := htmk4
                have hpres_4192_5 : ∀ i < 4192, scr5[i]? = s.scratch.scratch_buf[i]? :=
                  fun i hi => by rw [hpres5 i (by omega)]; exact hpres3 i hi
                c0_hsteps
                · exact hQ false s5 m5 hinv5 htmk5 rfl rfl rfl hfl5
                    (fun i hi => by simp [s5, hpres_4192_5 i hi]) hm5
                · have hreq20 : r = 20#64 := by c0_bound
                  have hna_nil : k6AssumpLitsS L scr5 = [] := by
                    rw [has5, certMkState_buf s tmp3 exp tmk' scr3, hna3]
                  have hP_unsat : ∀ β : Nat → Bool, ¬ P β := fun β hPβ => by
                    have hns := huns5 hreq20 β hPβ; rw [hna_nil] at hns
                    exact hns (by simp [unitsCnf, CNF.sat_empty])
                  refine cert_finish_unit_wp Γ Q X hAssign c F0 F_cur s5 R unit m5 hinv5 htmk5
                    hunit (cert_modelSet_unsat_entails hP_unsat) hm5 ?_
                  intro s6 m6 hinv6 htmk6 hcv6 har6 hal6 hfl6 hscr6 hm6
                  exact hQ true s6 m6 hinv6 htmk6 hcv6 har6 hal6 (hfl6 ▸ hfl5)
                    (fun i hi => by rw [hscr6]; exact hpres_4192_5 i hi) hm6
              · exact hQ false (certMkState s tmp3 exp tmk' scr3) m4 hinv4 htmk4 rfl rfl rfl
                  (Nat.le_refl _) (fun i hi => by rw [certMkState_buf]; exact hpres3 i hi) hm4
            · rintro B L2 ⟨idx2, ok2, tmp', scr'⟩ m' hB hL2
                ⟨hidx_le, htmp'_len, hscr'_len, hpres', hk6', hm'⟩
              have hFail : ∀ {tmp_f scr_f mf}, tmp_f.length = c.max_vars →
                  scr_f.length = c.scratch_cap →
                  (∀ i < 4192, scr_f[i]? = s.scratch.scratch_buf[i]?) →
                  (Full.FullMem c (certMkState s tmp_f exp tmk scr_f) ⋆ R) mf →
                  B (idx2, false, ()) mf := fun {tmp_f scr_f mf} h1 h2 h3 hm_f =>
                hB (idx2, false, tmp_f, scr_f) mf ⟨h1, h2, h3, fun h => absurd h (by decide), hm_f⟩
              let s' := certMkState s tmp' exp tmk scr'; c0_hsteps_nogrp
              · have hidx_lt : idx2.toNat < side_cnt.toNat := by c0_bound
                have hok2_t : ok2 = true := by c0_bound
                rcases hk6' hok2_t with ⟨hk6inv', hts', hlvl', hknv', hna'⟩
                refine wp_join_state (ts := [.bool])
                    (α := Bool × List (BitVec 32) × List (BitVec 32) × Mem 64)
                    (fun (ok_n, _, _, _) => (ok_n, ()))
                    (fun (ok_n, tmp_n, scr_n, m_n) m_in =>
                      m_in = m_n ∧ certL2Inv c s R L P nv exp tmk ok_n tmp_n scr_n m_n)
                    (fun J_ok (ok_n, tmp_n, scr_n, m_n) m_in ⟨hm_eq, hrest⟩ => by
                      rw [hm_eq]; c0_hsteps; exact hL2 (idx2 + 1#32, ok_n, tmp_n, scr_n) m_n
                        (by simp [BitVec.toNat_add]; omega)
                        ⟨by simp [BitVec.toNat_add]; omega, hrest⟩)
                    (fun J_ok hJok => by
                      have hmask_idx_lt :
                          (BitVec.zeroExtend 64 (side_mask + (idx2 >>> 5#32))).toNat <
                          scr'.length := by
                        have hshr := cert_shr5_toNat idx2
                        have hm_lt : side_mask.toNat ≤ 4066 := by
                          rcases hmask with rfl | rfl <;> decide
                        rw [cert_zext64_toNat, BitVec.toNat_add, hshr]; omega
                      c0_hsteps_nogrp
                      · have hw_idx_eq : (side_off + idx2).toNat = side_off.toNat + idx2.toNat := by
                          simp [BitVec.toNat_add]; omega
                        have hw_idx_lt :
                            (BitVec.zeroExtend 64 (side_off + idx2)).toNat < scr'.length := by
                          rw [cert_zext64_toNat, hw_idx_eq]; omega
                        have hw_eq : scr'[(side_off + idx2).toNat]?.getD 0#32 =
                            s.scratch.scratch_buf[side_off.toNat + idx2.toNat]?.getD 0#32 := by
                          rw [hw_idx_eq, hpres' (side_off.toNat + idx2.toNat) (by omega)]
                        have hwe :
                            FullBveEntryOkW F_cur s unit.toNat scr'[(side_off + idx2).toNat] := by
                          rw [← cert_getElemD (by rw [← cert_zext64_toNat]; exact hw_idx_lt) 0#32,
                            hw_eq]
                          exact hent idx2.toNat hidx_lt
                        c0_hsteps_nogrp
                        refine wp_join_state (ts := [.bool])
                          (α := Bool × List (BitVec 32) × List (BitVec 32) × Mem 64)
                          (fun (ok_n, _, _, _) => (ok_n, ()))
                          (fun (ok_n, tmp_n, scr_n, m_n) m_in =>
                            m_in = m_n ∧ certL2Inv c s R L P nv exp tmk ok_n tmp_n scr_n m_n)
                          (fun J_m (ok_n, tmp_n, scr_n, m_n) m_in ⟨hm_eq, hrest⟩ => by
                            rw [hm_eq]; c0_hsteps
                            exact hJok (ok_n, tmp_n, scr_n, m_n) m_n ⟨rfl, hrest⟩)
                          (fun J_m hJm => by
                            c0_hsteps
                            · let w := scr'[(side_off + idx2).toNat]
                              have hbit : w &&& 2147483648#32 ≠ 0#32 := by c0_bound
                              dsimp only [FullBveEntryOkW] at hwe
                              have hbit' :
                                  scr'[(side_off + idx2).toNat] &&& 2147483648#32 ≠ 0#32 := hbit
                              rw [ite_eq_left hbit'] at hwe; rcases hwe with ⟨hot_lt, hot_ent⟩
                              let ot := w &&& 2147483647#32
                              have hot_lt' : ot.toNat < 2 * s.core.cur_vars := hot_lt
                              have hcv_le := hinv.1.core_ok.cur_vars_le
                              have hv_len : s'.core.vals.length = 2 * c.max_vars :=
                                hinv.1.core_ok.vals_len
                              have hot_len :
                                  (BitVec.zeroExtend 64 ot).toNat < s'.core.vals.length := by
                                rw [cert_zext64_toNat]; omega
                              c0_hsteps_nogrp
                              · have hu_eq := cert_shr1_toNat ot
                                have hu_lt_cv : (ot >>> 1#32).toNat < s.core.cur_vars := by
                                  rw [hu_eq]; omega
                                have hu_lt_tmk :
                                    (BitVec.zeroExtend 64 (ot >>> 1#32)).toNat < tmk.length := by
                                  rw [cert_zext64_toNat]; omega
                                c0_hsteps
                                · exact hFail htmp'_len hscr'_len hpres' hm'
                                · exact hFail htmp'_len hscr'_len hpres' hm'
                                · have hloc_nz : tmk[ot.toNat / 2] ≠ 0#32 := by c0_bound
                                  have hloc_le : tmk[ot.toNat / 2].toNat ≤ nv.toNat := by
                                    have hid : (scr'[(BitVec.toNat side_off + idx2.toNat) % 2 ^ 32]
                                        &&& 2147483647).toNat / 2 = ot.toNat / 2 := by
                                      have hsc := cert_list_getElem_eq rfl
                                        (BitVec.toNat_add side_off idx2).symm
                                        (by rw [hscr'_len]; omega) (by rw [hscr'_len]; omega)
                                      dsimp only [ot, w]; rw [hsc]; rfl
                                    have htm := cert_list_getElem_eq rfl hid
                                      (by rw [htmk_len, hid]; omega)
                                      (by omega : ot.toNat / 2 < tmk.length)
                                    exact Nat.le_of_not_lt fun h => hc (by rwa [htm])
                                  have hget_loc :=
                                    cert_getElemD (by omega : ot.toNat / 2 < tmk.length) 0#32
                                  have hok_u := hok.1 (ot.toNat / 2) (by omega) (by rwa [hget_loc])
                                  have hloc1 : 1 ≤ tmk[ot.toNat / 2].toNat := by
                                    rw [← hget_loc]; exact hok_u.1
                                  have h0_lt_tmp :
                                      (BitVec.zeroExtend 64 0#32).toNat < tmp'.length := by
                                    rw [cert_zext64_toNat, htmp'_len]; exact hmaxv_pos
                                  c0_hsteps
                                  let loc := tmk[(ot >>> 1#32).toNat]
                                  have hloc_eq : loc = tmk[ot.toNat / 2] :=
                                    cert_list_getElem_eq rfl hu_eq (by rw [hu_eq]; omega) (by omega)
                                  let lit0 := ((loc - 1#32) <<< 1#32) ||| (ot &&& 1#32)
                                  let tmp'' := tmp'.set (BitVec.zeroExtend 64 0#32).toNat lit0
                                  have htmp''_eq : tmp'' = tmp'.set 0 lit0 := by simp [tmp'']
                                  have htmp''_len : tmp''.length = c.max_vars := by
                                    simp [htmp''_eq, htmp'_len]
                                  have hlit0_toNat : lit0.toNat =
                                      2 * (loc.toNat - 1) + ot.toNat % 2 :=
                                    cert_packed_lit_toNat loc ot (hloc_eq ▸ hloc1)
                                      (hloc_eq ▸ by omega)
                                  have hlit0_lt : lit0.toNat < 2 * nv.toNat := by
                                    rw [hlit0_toNat, hloc_eq]; omega
                                  have hm0 := hm; dsimp -zeta only at hm0
                                  have hw_buf :
                                      (certMkState s tmp' exp tmk scr').scratch.scratch_buf[
                                        (BitVec.setWidth 64 (side_off + idx2)).toNat] = w :=
                                    cert_list_getElem_eq (certMkState_buf s tmp' exp tmk scr')
                                      (cert_zext64_toNat _)
                                      (by rw [certMkState_buf]; exact hw_idx_lt) (by omega)
                                  have htm_ot :
                                      (certMkState s tmp' exp tmk scr').scratch.tarjan_mark[
                                        (BitVec.setWidth 64 (((certMkState s tmp' exp tmk
                                          scr').scratch.scratch_buf[(BitVec.setWidth 64
                                            (side_off + idx2)).toNat] &&& 2147483647) >>>
                                          OfNat.ofNat 1)).toNat] = loc :=
                                    cert_list_getElem_eq (certMkState_tmk s tmp' exp tmk scr')
                                      (by rw [hw_buf, cert_zext64_toNat]; rfl)
                                      (by rw [certMkState_tmk, hw_buf, cert_zext64_toNat]
                                          rw [cert_zext64_toNat] at hu_lt_tmk; exact hu_lt_tmk)
                                      (by rw [hu_eq]; omega)
                                  erw [htm_ot, hw_buf] at hm0
                                  have hm_foc := cert_focus_addCl_tmp hm0
                                  have h1n : (1 : BitVec 32).toNat = 1 := rfl
                                  fid_call hAdd; dsimp only [vals, Arg.val]
                                  refine ⟨c, certMkState s tmp'' exp tmk scr', P, L, scr', tmp'', _,
                                    rfl, ?_, rfl, hLscr, hLmax, hk6inv', hts', hlvl',
                                    (by rw [h1n]; omega), (by rw [h1n]; decide), ?_, ?_, hm_foc, ?_⟩
                                  · exact (hdens_mk htmp''_len hexp_len htmk_len hscr'_len).1
                                  · intro idx0 hidx0
                                    have hi0 : idx0 = 0 := by rw [h1n] at hidx0; omega
                                    subst hi0
                                    rw [htmp''_eq, List.getElem?_set_self
                                      (by rw [htmp'_len]; exact hmaxv_pos), Option.getD_some,
                                      hknv']
                                    exact hlit0_lt
                                  · intro β ⟨α, hsat, hnu, hmap⟩
                                    rcases cert_entails_in_modelSet hot_ent hsat hnu with
                                      ⟨q, hqm, _, hqs⟩
                                    simp only [List.mem_cons, List.not_mem_nil, or_false] at hqm
                                    rcases hqm with rfl | rfl
                                    · exact absurd hqs hnu
                                    · have htake : List.take 1 tmp'' = [lit0] := by
                                        rw [htmp''_eq]; cases tmp' with
                                        | nil =>
                                          rw [← htmp'_len] at hmaxv_pos
                                          exact absurd hmaxv_pos (Nat.not_lt_zero _)
                                        | cons _ _ => rfl
                                      rw [h1n, htake]; simp only [List.map_cons, List.map_nil]
                                      have hexp_loc : (exp[loc.toNat - 1]?.getD 0#32).toNat =
                                          ot.toNat / 2 := by
                                        rw [← show tmk[ot.toNat / 2]?.getD 0#32 = loc from
                                          hloc_eq ▸ hget_loc]; exact hok_u.2.2
                                      exact cert_mapped_lit_sat (hloc_eq ▸ hloc1)
                                        (hloc_eq ▸ hloc_le) hexp_loc hmap
                                        (by rw [hlit0_toNat]; omega)
                                        (by rw [hlit0_toNat]; omega) hqs
                                  · dsimp only
                                    intro _ scr_a m_a hlen_a hpres_a hk6_a hts_a hlvl_a hnv_a _
                                      has_a _ _ _ hm_a
                                    have hm_unf := cert_unfocus_addCl_tmp hm_a
                                    have hpres_4192_a : ∀ i < 4192,
                                        scr_a[i]? = s.scratch.scratch_buf[i]? :=
                                      fun i hi => by rw [hpres_a i (by omega)]; exact hpres' i hi
                                    have hna_nil_a : k6AssumpLitsS L scr_a = [] := by
                                      rw [has_a, hna']
                                    c0_hsteps
                                    · have hgoal : J_m (true, ()) m_a := hJm (true, tmp'', scr_a,
                                        m_a) m_a ⟨rfl, htmp''_len, hlen_a, hpres_4192_a, fun _ =>
                                          ⟨hk6_a, hts_a, hlvl_a, by rw [hnv_a, hknv'], hna_nil_a⟩,
                                          hm_unf⟩
                                      rwa [hok2_t]
                                    · exact hFail htmp''_len hlen_a hpres_4192_a hm_unf
                              · have hgoal : J_m (true, ()) m' := hJm (true, tmp', scr', m') m'
                                  ⟨rfl, htmp'_len, hscr'_len, hpres',
                                   fun _ => ⟨hk6inv', hts', hlvl', hknv', hna'⟩, hm'⟩
                                rwa [hok2_t]
                            · let w := scr'[(side_off + idx2).toNat]
                              have hnb : w &&& 2147483648#32 = 0#32 := by dsimp only [w]; c0_bound
                              dsimp only [FullBveEntryOkW] at hwe
                              have hnb' : scr'[(side_off + idx2).toNat] &&& 2147483648#32 = 0#32 :=
                                hnb
                              rw [ite_eq_right (fun h => absurd hnb' h)] at hwe
                              rcases hwe with ⟨hwref, hwgarb⟩
                              have href_wf := hinv.2.1.arena.refs_wf w.toNat hwref
                              have har_le := hinv.1.core_ok.arena_len_le
                              have har_arr := hinv.1.core_ok.arena_len_arr
                              have hw3 := href_wf.1; have hn1 := href_wf.2.2.1
                              have hn2 := href_wf.2.2.2.1
                              have hw_idx_eq :
                                  (BitVec.zeroExtend 64 w + 2#64).toNat = w.toNat + 2 := by
                                have h2 : w.toNat < 2 ^ 32 := w.isLt
                                rw [BitVec.toNat_add, cert_zext64_toNat,
                                  show (2#64 : BitVec 64).toNat = 2 from rfl,
                                  Nat.mod_eq_of_lt (by omega)]
                              have hw_len :
                                  (BitVec.zeroExtend 64 w + 2#64).toNat < s'.core.arena.length := by
                                rw [hw_idx_eq]; dsimp only [s']; rw [certMkState_arena]; omega
                              c0_hsteps_nogrp
                              have hwa2 : w.toNat + 2 < s'.core.arena.length := by
                                dsimp only [s']; rw [certMkState_arena]; omega
                              let lsz := s'.core.arena[w.toNat + 2]'hwa2
                              have hlsz_eq :
                                  lsz.toNat = fullArenaClauseSizeCore s.core w.toNat := by
                                have hwa_s : w.toNat + 2 < s.core.arena.length := by omega
                                have hlsz_s : lsz = s.core.arena[w.toNat + 2] :=
                                  cert_list_getElem_eq
                                    (by dsimp only [s']; exact certMkState_arena ..)
                                    rfl hwa2 hwa_s
                                rw [hlsz_s]
                                simp [fullArenaClauseSizeCore, List.getElem?_eq_getElem hwa_s]
                              have hlsz_bound : w.toNat + 3 + lsz.toNat ≤ s.core.arena.length := by
                                rw [hlsz_eq]; omega
                              have hlsz_lt_29 : lsz.toNat < 2 ^ 29 := by omega
                              refine wp_join_state (ts := [.bool, .bool, i32, i32])
                                (α :=
                                  Bool × Bool × BitVec 32 × BitVec 32 × List (BitVec 32) × Mem 64)
                                (fun (ok2_l, sat2, csz2, k2, _, _) => (ok2_l, sat2, csz2, k2, ()))
                                (fun (ok2_l, sat2, csz2, _, tmp2, m_n) m2_in => m2_in = m_n ∧
                                  tmp2.length = c.max_vars ∧
                                  (ok2_l = true → sat2 = false → csz2.toNat ≤ max_csz.toNat ∧
                                    (∀ j < csz2.toNat, (tmp2[j]?.getD 0#32).toNat < 2 * nv.toNat) ∧
                                    SemEntails P
                                      (List.map BitVec.toNat (List.take csz2.toNat tmp2))) ∧
                                  (Full.FullMem c (certMkState s tmp2 exp tmk scr') ⋆ R) m_n)
                                (fun J_l (ok2_l, sat2, csz2, _, tmp2, m_n) m2_in
                                    ⟨hm2_eq, htmp2_len, hsem2, hm2_mem⟩ => by
                                  subst m2_in; c0_hsteps
                                  · have hok2_lt : ok2_l = true := by c0_bound
                                    have hgoal : J_m (true, ()) m_n :=
                                      hJm (true, tmp2, scr', m_n) m_n
                                        ⟨rfl, htmp2_len, hscr'_len, hpres',
                                         fun _ => ⟨hk6inv', hts', hlvl', hknv', hna'⟩, hm2_mem⟩
                                    rwa [hok2_lt]
                                  · have hok2_lt : ok2_l = true := by c0_bound
                                    have hsat2_f : sat2 = false := by c0_bound
                                    have hmcsz_65535 : max_csz.toNat ≤ 65535 := by omega
                                    rcases hsem2 hok2_lt hsat2_f with ⟨hcsz_le, hlts, hsem⟩
                                    have hm_foc := cert_focus_addCl_tmp hm2_mem; fid_call hAdd
                                    dsimp only [vals, Arg.val]
                                    refine ⟨c, certMkState s tmp2 exp tmk scr', P, L, scr', tmp2,
                                      _, rfl, ?_, rfl, hLscr, hLmax, hk6inv', hts', hlvl',
                                      (by omega), (by omega),
                                      (fun j hj => by simpa [hknv'] using hlts j hj),
                                      hsem, hm_foc, ?_⟩
                                    · exact (hdens_mk htmp2_len hexp_len htmk_len hscr'_len).1
                                    · dsimp only
                                      intro _ scr_a m_a hlen_a hpres_a hk6_a hts_a hlvl_a hnv_a _
                                        has_a _ _ _ hm_a
                                      have hm_unf := cert_unfocus_addCl_tmp hm_a
                                      have hpres_4192_a : ∀ i < 4192,
                                          scr_a[i]? = s.scratch.scratch_buf[i]? :=
                                        fun i hi => by rw [hpres_a i (by omega)]; exact hpres' i hi
                                      have hna_nil_a : k6AssumpLitsS L scr_a = [] := by
                                        rw [has_a, hna']
                                      c0_hsplit
                                      · c0_hsteps
                                        have hgoal : J_m (true, ()) m_a :=
                                          hJm (true, tmp2, scr_a, m_a) m_a
                                            ⟨rfl, htmp2_len, hlen_a, hpres_4192_a, fun _ =>
                                              ⟨hk6_a, hts_a, hlvl_a, by rw [hnv_a, hknv'],
                                               hna_nil_a⟩, hm_unf⟩
                                        rwa [hok2_lt]
                                      · c0_hsteps; exact hFail htmp2_len hlen_a hpres_4192_a hm_unf
                                  · have hok2_lf : ok2_l = false := by
                                      cases ok2_l with
                                      | false => rfl
                                      | true => exact absurd hc (by decide)
                                    simpa [hok2_lf] using hFail htmp2_len hscr'_len hpres' hm2_mem)
                                (fun Js hB3 => by
                                  have hgoal_w :
                                      (certMkState s tmp' exp tmk scr').scratch.scratch_buf[
                                        (BitVec.setWidth 64 (side_off + idx2)).toNat] = w :=
                                    cert_list_getElem_eq (certMkState_buf ..) (cert_zext64_toNat _)
                                      (by rw [certMkState_buf]; exact hw_idx_lt) (by omega)
                                  have hgoal_lsz : (certMkState s tmp' exp tmk scr').core.arena[
                                      (BitVec.setWidth 64 ((certMkState s tmp' exp tmk
                                        scr').scratch.scratch_buf[(BitVec.setWidth 64
                                          (side_off + idx2)).toNat]) + 2).toNat] = lsz :=
                                    cert_list_getElem_eq (certMkState_arena ..)
                                      (by erw [hgoal_w, hw_idx_eq])
                                      (by rw [certMkState_arena]; erw [hgoal_w, hw_idx_eq]; omega)
                                      hwa2
                                  dsimp -zeta only; erw [hgoal_lsz, hgoal_w]
                                  exact cert_loop2_large_wp Γ Q X Js c F0 F_cur s R tmp' exp tmk
                                    scr' w lsz unit nv max_csz ok2 P m' rfl hok2_t hinv htmp'_len
                                    hexp_len htmk_len hscr'_len hcur_pos hmaxv_pos hnv_mv hmv_le
                                    hnv_cv hmcsz_pos hmcsz_le (by omega) hok hwref hwgarb hlsz_eq
                                    hlsz_bound hlsz_lt_29 hm' hB3))
                      · have hgoal : J_ok (true, ()) m' := hJok (true, tmp', scr', m') m'
                          ⟨rfl, htmp'_len, hscr'_len, hpres',
                           fun _ => ⟨hk6inv', hts', hlvl', hknv', hna'⟩, hm'⟩
                        rwa [hok2_t])
              · exact hB (idx2, ok2, tmp', scr') m' ⟨htmp'_len, hscr'_len, hpres', hk6', hm'⟩
              · exact hB (idx2, ok2, tmp', scr') m' ⟨htmp'_len, hscr'_len, hpres', hk6', hm'⟩
            · rintro B L2 hB hL2; c0_hsteps
              exact hL2 (0#32, true, s.core.tmp, scr2) m2
                ⟨Nat.zero_le _, hinv.1.core_ok.tmp_len_arr, hlen2.scratch_ok.scratch_buf_len,
                 hpres_4192_2, fun _ => ⟨hk6inv2 P, hts2, hlvl, hknv, hna_empty2⟩, hm2⟩)
  · intro Js hB
    exact cert_loop1_wp Γ Q X Js c F0 F_cur s R unit side_off side_cnt side_mask mv_sw max_csz m
      hmv_toNat hinv htmk hcap hmaxv_lt hcnt hoff_cnt hmask hent hm hB

end LeanQbe.T.Examples.Kissat.FullFidelityBve
