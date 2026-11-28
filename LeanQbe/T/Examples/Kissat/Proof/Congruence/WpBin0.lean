/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Arena.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Clause.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Congruence.Inv
public import LeanQbe.T.Examples.Kissat.Proof.Watch.Spec
public import LeanQbe.T.Examples.Kissat.Src.Congruence

/-!
# Canonical WP Proofs for Congruence Binary / Unit Extraction (`#11–#13`)

Proves `Func.wp` against flat `CanonicalEnv` for:
- `11. full_cong_count_bins` (`Spec.fullCongCountBinsSpec`)
- `12. full_cong_eb_match` (`Spec.fullCongEbMatchSpec`)
- `13. full_cong_extract_binaries` (`Spec.fullCongExtractBinariesSpec`)
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Congruence

open Std Std.Sat
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Congruence
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Congruence.Spec
open Kraken.Bedrock2.Test

open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Proof.Congruence.CongTactics

local macro "cong_split" : tactic =>
  `(tactic| (
    c0_hsteps_nogrp
    repeat (
      refine LeanQbe.T.wp_unroll_group fun _ _ => ?_
      c0_hsteps_nogrp)
    c0_hsplit))

public section

/-! ## 12. `full_cong_eb_match_wp` (`Spec.fullCongEbMatchSpec`) -/

/-- Canonical `Func.wp` proof for `full_cong_eb_match`. -/
theorem full_cong_eb_match_wp (Γ : Env)
    (hHasBin : Γ.Has "full_has_bin" fullHasBinSpec) :
    ∀ args m Q X, Spec.fullCongEbMatchSpec args m Q X →
      Func.wp Γ full_cong_eb_match_body args m Q X := by
  rintro ⟨h, x, l, k, ⟨⟩⟩ m0 Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hx_lt, hm0, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv_le := hlen.core_ok.cur_vars_le
  have hws1_len := hlen.scratch_ok.work_stk1_len
  have hx_ws1 : (x.setWidth 64).toNat < s.scratch.work_stk1.length := by
    rw [bv_zext32_toNat]; omega
  unfold Func.wp full_cong_eb_match_body
  cong_split
  · c0_hsteps!
    exact hQ false (fun h => by cases h)
  · clear hc; c0_hsteps_nogrp
    refine LeanQbe.T.wp_join_group (ts := [.bool])
      (fun (ok, ()) mo => mo = m0 ∧
        (ok = true →
          (cnfOfClauses F_cur).EntailsClause (cnfClause [x.toNat ^^^ 1, l.toNat]) ∨
          (cnfOfClauses F_cur).EntailsClause (cnfClause [x.toNat ^^^ 1, k.toNat]))) ?_ ?_
    · rintro _ ⟨ok, ⟨⟩⟩ mo ⟨rfl, hok⟩
      c0_hsteps!; exact hQ ok hok
    · intro J hJ
      c0_hsteps!; c0_call hHasBin
      refine ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hm0, fun ok1 hok1 => ?_⟩
      cong_split
      · c0_hsteps!
        refine hJ (true, ()) m0 ⟨rfl, fun _ => Or.inl ?_⟩
        have h := (hok1 hc).2.2.2.2
        rwa [show (x ^^^ (1 : BitVec 32)).toNat = x.toNat ^^^ 1 from bv32_xor1_eq_litNeg x] at h
      · clear hc; c0_hsteps!; c0_call hHasBin
        refine ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hm0, fun ok2 hok2 => ?_⟩
        cong_split
        · c0_hsteps!
          refine hJ (true, ()) m0 ⟨rfl, fun _ => Or.inr ?_⟩
          have h := (hok2 hc).2.2.2.2
          rwa [show (x ^^^ (1 : BitVec 32)).toNat = x.toNat ^^^ 1 from bv32_xor1_eq_litNeg x] at h
        · c0_hsteps!; exact hJ (false, ()) m0 ⟨rfl, fun h => by cases h⟩

/-! ## 11. `full_cong_count_bins_wp` (`Spec.fullCongCountBinsSpec`) -/

private theorem cb_shl1_lt {x : Nat} (hx : x < 2 ^ 63) :
    ((BitVec.ofNat 64 x <<< (1 : Nat)).toNat = 2 * x) ∧
    ((BitVec.ofNat 64 x <<< (1 : Nat) + 1#64).toNat = 2 * x + 1) := by
  have h1 : (BitVec.ofNat 64 x <<< (1 : Nat)).toNat = 2 * x := by
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
      Nat.mod_eq_of_lt (by omega : x < 2 ^ 64), Nat.mul_comm]
    simp [Nat.mod_eq_of_lt (by omega : 2 * x < 2 ^ 64)]
  have h2 : (BitVec.ofNat 64 x <<< (1 : Nat) + 1#64).toNat = 2 * x + 1 := by
    rw [BitVec.toNat_add, h1, show (1#64 : BitVec 64).toNat = 1 from rfl]
    exact Nat.mod_eq_of_lt (by omega)
  exact ⟨h1, h2⟩

/-- Canonical `Func.wp` proof for `full_cong_count_bins`. -/
theorem full_cong_count_bins_wp (Γ : Env) :
    ∀ args m Q X, Spec.fullCongCountBinsSpec args m Q X →
      Func.wp Γ full_cong_count_bins_body args m Q X := by
  rintro ⟨h, ⟨⟩⟩ m0 Q X ⟨c, s, R, rfl, hlen, hwbd, hm0, hQ⟩
  have hmx := c.hmaxv; have hwc := c.hwcap; unfold dimacsBound at hmx hwc
  have hcv_le := hlen.core_ok.cur_vars_le
  have hws1_len := hlen.scratch_ok.work_stk1_len
  have hwvec_len := hlen.core_ok.wvec_len
  have hwstk_len := hlen.core_ok.wstk_len_arr
  unfold Func.wp full_cong_count_bins_body
  c0_hsteps_nogrp
  refine LeanQbe.T.wp_loop_inv (ts := [i64])
    (fun (i, ()) mi => ∃ ws1 : List (BitVec 32),
      i.toNat ≤ 2 * s.core.cur_vars ∧ ws1.length = 2 * c.max_vars ∧
      (FullMem c { s with scratch := { s.scratch with work_stk1 := ws1 } } ⋆ R) mi)
    (fun (i, ()) _ => 2 * s.core.cur_vars - i.toNat)
    (fun Ji hJi => by
      c0_hsteps!; exact hJi (0#64, ()) m0 ⟨s.scratch.work_stk1, Nat.zero_le _, hws1_len, hm0⟩)
    (fun Ji (i, ()) mi ⟨ws1, hi_le, hws1l, hmi⟩ ihi => ?_)
  have hm_eq :
      (BitVec.ofNat 64 s.core.cur_vars <<< (1 : BitVec 64)).toNat = 2 * s.core.cur_vars := by
    have h := (cb_shl1_lt (x := s.core.cur_vars) (by omega)).1
    exact h
  c0_hsplit
  · have hi_lt : i.toNat < 2 * s.core.cur_vars := by
      have := hc
      change i.toNat < (BitVec.ofNat 64 s.core.cur_vars <<< (1 : BitVec 64)).toNat at this
      omega
    have hi_ws1 : i.toNat < ws1.length := by omega
    have hi1 : (i + 1#64).toNat = i.toNat + 1 := by bv_omega
    c0_hsteps!
    exact ihi (i + 1#64, ()) m (by dsimp only; omega)
      ⟨ws1.set i.toNat 0#32, by omega, by simp [hws1l], hm⟩
  · clear hc; c0_hsteps_nogrp
    refine LeanQbe.T.wp_loop_inv (ts := [i64])
      (fun (l, ()) ml => ∃ ws1_l : List (BitVec 32),
        l.toNat ≤ 2 * s.core.cur_vars ∧ ws1_l.length = 2 * c.max_vars ∧
        (FullMem c { s with scratch := { s.scratch with work_stk1 := ws1_l } } ⋆ R) ml)
      (fun (l, ()) _ => 2 * s.core.cur_vars - l.toNat)
      (fun Jl hJl => by
        c0_hsteps!; exact hJl (0#64, ()) mi ⟨ws1, Nat.zero_le _, hws1l, hmi⟩)
      (fun Jl (l, ()) ml ⟨ws1_l, hl_le, hws1ll, hml⟩ ihl => ?_)
    c0_hsplit
    · have hl_lt : l.toNat < 2 * s.core.cur_vars := by
        have := hc
        change l.toNat < (BitVec.ofNat 64 s.core.cur_vars <<< (1 : BitVec 64)).toNat at this
        omega
      have hl1 : (l + (1 : BitVec 64)).toNat = l.toNat + 1 := by bv_omega
      have hlv : BitVec.ofNat 64 l.toNat = l := BitVec.eq_of_toNat_eq (by simp)
      have hl_shl_nat : (l <<< (1 : BitVec 64)).toNat = 2 * l.toNat := by
        conv => lhs; rw [← hlv]
        exact (cb_shl1_lt (x := l.toNat) (by omega)).1
      have hl_shl1_nat : (l <<< (1 : BitVec 64) + (1 : BitVec 64)).toNat = 2 * l.toNat + 1 := by
        change (l <<< (1 : BitVec 64) + 1#64).toNat = 2 * l.toNat + 1
        conv => lhs; rw [← hlv]
        exact (cb_shl1_lt (x := l.toNat) (by omega)).2
      have hwbd_l := hwbd l.toNat hl_lt
      have hw0_lt : (l <<< (1 : BitVec 64)).toNat < s.core.wvec.length := by omega
      have hw1_lt : (l <<< (1 : BitVec 64) + (1 : BitVec 64)).toNat < s.core.wvec.length := by
        omega
      let off := (s.core.wvec[(l <<< (1 : BitVec 64)).toNat]'hw0_lt).setWidth 64
      let wsz :=
        (s.core.wvec[(l <<< (1 : BitVec 64) + (1 : BitVec 64)).toNat]'hw1_lt).setWidth 64
      have hoff_eq : off.toNat = fullWatchOffCore s.core l.toNat := by
        dsimp only [off]; unfold fullWatchOffCore
        rw [bv_zext32_toNat, list_getElem_congr hl_shl_nat hw0_lt (by omega),
          List.getElem?_eq_getElem (by omega), Option.getD_some]
      have hwsz_eq : wsz.toNat = fullWatchSizeCore s.core l.toNat := by
        dsimp only [wsz]; unfold fullWatchSizeCore
        rw [bv_zext32_toNat, list_getElem_congr hl_shl1_nat hw1_lt (by omega),
          List.getElem?_eq_getElem (by omega), Option.getD_some]
      have hend_eq : (off + wsz).toNat = off.toNat + wsz.toNat := by bv_omega
      have hl_xor_lt : (l ^^^ (1 : BitVec 64)).toNat < ws1_l.length := by
        have hlt32 : (l ^^^ (1 : BitVec 64)).toNat < 2 ^ 32 := by
          rw [BitVec.toNat_xor]
          exact Nat.xor_lt_two_pow (by omega) (by decide)
        have h1 : (l ^^^ (1 : BitVec 64)).toNat =
            (BitVec.setWidth 32 (l ^^^ (1 : BitVec 64))).toNat := by
          rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt hlt32]
        have hset : BitVec.setWidth 32 (l ^^^ (1 : BitVec 64)) =
            BitVec.setWidth 32 l ^^^ (1 : BitVec 32) := BitVec.setWidth_xor
        have hln : (BitVec.setWidth 32 l ^^^ (1 : BitVec 32)).toNat =
            litNeg (BitVec.setWidth 32 l).toNat := bv32_xor1_eq_litNeg (BitVec.setWidth 32 l)
        have hll : (BitVec.setWidth 32 l).toNat = l.toNat := by
          rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
        have hlt_neg := litNeg_lt_two_mul hl_lt
        rw [h1, hset, hln, hll]
        exact Nat.lt_of_lt_of_le hlt_neg (by omega)
      clear hc; c0_hsteps_nogrp
      refine LeanQbe.T.wp_loop_inv (ts := [i64, i32])
        (fun (p, _cnt, ()) mp =>
          off.toNat ≤ p.toNat ∧ p.toNat ≤ (off + wsz).toNat + 1 ∧
          (FullMem c { s with scratch := { s.scratch with work_stk1 := ws1_l } } ⋆ R) mp)
        (fun (p, _cnt, ()) _ => (off + wsz).toNat + 1 - p.toNat)
        (fun Jp hJp => by
          c0_hsteps!; exact hJp (off, 0#32, ()) ml ⟨Nat.le_refl _, by omega, hml⟩)
        (fun Jp (p, cnt, ()) mp ⟨hp_lo, hp_hi, hmp⟩ ihp => ?_)
      c0_hsplit
      · have hlt2l : 2 * l.toNat < 2 ^ 64 := by omega
        have hlt2l1 : 2 * l.toNat + 1 < 2 ^ 64 := by omega
        have hm0 : (2 * l.toNat) % 2 ^ 64 = 2 * l.toNat := Nat.mod_eq_of_lt hlt2l
        have hm1 : (2 * l.toNat + 1) % 2 ^ 64 = 2 * l.toNat + 1 :=
          Nat.mod_eq_of_lt hlt2l1
        have hp_lt : p.toNat < (off + wsz).toNat := by
          dsimp only [off, wsz]
          rw [BitVec.toNat_add, bv_zext32_toNat, bv_zext32_toNat,
            list_getElem_congr hl_shl_nat hw0_lt (by omega),
            list_getElem_congr hl_shl1_nat hw1_lt (by omega)]
          simpa [hm0, hm1] using hc
        have hp_w : p.toNat < s.core.wstk.length := by omega
        have hp1 : (p + (1 : BitVec 64)).toNat = p.toNat + 1 := by bv_omega
        have hp2 : (p + (2 : BitVec 64)).toNat = p.toNat + 2 := by bv_omega
        clear hc; cong_split
        · c0_hsteps!
          exact ihp (p + (1 : BitVec 64), cnt + (1 : BitVec 32), ()) mp (by dsimp only; omega)
            ⟨by omega, by omega, hmp⟩
        · c0_hsteps!
          exact ihp (p + (2 : BitVec 64), cnt, ()) mp (by dsimp only; omega)
            ⟨by omega, by omega, hmp⟩
      · c0_hsteps!
        exact ihl (l + (1 : BitVec 64), ()) m (by dsimp only; omega)
          ⟨ws1_l.set (l ^^^ (1 : BitVec 64)).toNat cnt, by omega, by simp [hws1ll], hm⟩
    · c0_hsteps!; exact hQ ws1_l ml hws1ll hml

/-! ## 13. `full_cong_extract_binaries_wp` (`Spec.fullCongExtractBinariesSpec`) -/

private theorem eb_resolve_pair {F : Std.Sat.CNF Nat} {x y z : Nat}
    (h3 : F.EntailsClause (cnfClause [x, y, z]))
    (h2 : F.EntailsClause (cnfClause [z ^^^ 1, x]) ∨
          F.EntailsClause (cnfClause [z ^^^ 1, y])) :
    F.EntailsClause (cnfClause [x, y]) := by
  refine entails_of_eval_mem fun α hα => ?_
  have hs3 : clauseEvalVal α [x, y, z] = true :=
    (LeanQbe.T.Examples.Kissat.Ref.clauseEvalVal_iff α [x, y, z]).mpr
      (Std.Sat.CNF.entails_clause_def.mp h3 α hα)
  have hmem3 : evalLitVal α x = true ∨ evalLitVal α y = true ∨ evalLitVal α z = true := by
    simpa [LeanQbe.T.Examples.Kissat.Ref.clauseEvalVal] using hs3
  rcases hmem3 with hx | hy | hz
  · exact ⟨x, by simp, hx⟩
  · exact ⟨y, by simp, hy⟩
  · have hzf : evalLitVal α (z ^^^ 1) = false := by
      change evalLitVal α (litNeg z) = false
      rw [LeanQbe.T.Examples.Kissat.Ref.evalLitVal_litNeg, hz]; rfl
    rcases h2 with hzx | hzy
    · have hsx : clauseEvalVal α [z ^^^ 1, x] = true :=
        (LeanQbe.T.Examples.Kissat.Ref.clauseEvalVal_iff α [z ^^^ 1, x]).mpr
          (Std.Sat.CNF.entails_clause_def.mp hzx α hα)
      have hx : evalLitVal α x = true := by
        simpa [LeanQbe.T.Examples.Kissat.Ref.clauseEvalVal, hzf] using hsx
      exact ⟨x, by simp, hx⟩
    · have hsy : clauseEvalVal α [z ^^^ 1, y] = true :=
        (LeanQbe.T.Examples.Kissat.Ref.clauseEvalVal_iff α [z ^^^ 1, y]).mpr
          (Std.Sat.CNF.entails_clause_def.mp hzy α hα)
      have hy : evalLitVal α y = true := by
        simpa [LeanQbe.T.Examples.Kissat.Ref.clauseEvalVal, hzf] using hsy
      exact ⟨y, by simp, hy⟩

private theorem eb_entails3_rot1 {F : Std.Sat.CNF Nat} {x y z : Nat}
    (h3 : F.EntailsClause (cnfClause [x, y, z])) :
    F.EntailsClause (cnfClause [y, z, x]) :=
  entails_perm_clause (fun _ hl => by
    simp at hl ⊢; rcases hl with rfl | rfl | rfl <;> simp) h3

private theorem eb_entails3_swap23 {F : Std.Sat.CNF Nat} {x y z : Nat}
    (h3 : F.EntailsClause (cnfClause [x, y, z])) :
    F.EntailsClause (cnfClause [x, z, y]) :=
  entails_perm_clause (fun _ hl => by
    simp at hl ⊢; rcases hl with rfl | rfl | rfl <;> simp) h3

private theorem eb_clause3_lits {c : Spec.FullCfg} {F0 : Std.Sat.CNF Nat}
    {F_cur : List (List Nat)} {s : Spec.FullState} {cr : Nat}
    (hinv : Spec.FullDenseInvW c F0 F_cur s)
    (hcr : cr ∈ Spec.fullArenaClauseRefs s)
    (hhdr : (s.core.arena[cr]?.getD 0#32 &&& (524288#32 ||| 4194304#32)) = 0#32)
    (hsz3 : s.core.arena[cr + 2]?.getD 0#32 = 3#32) :
    cr + 6 ≤ s.core.arena.length ∧
    ∀ (hbd : cr + 6 ≤ s.core.arena.length),
      let l0 := s.core.arena[cr + 3]'(by omega)
      let l1 := s.core.arena[cr + 4]'(by omega)
      let l2 := s.core.arena[cr + 5]'(by omega)
      l0.toNat < 2 * s.core.cur_vars ∧
      l1.toNat < 2 * s.core.cur_vars ∧
      l2.toNat < 2 * s.core.cur_vars ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause [l0.toNat, l1.toNat, l2.toNat]) := by
  have hwf := hinv.2.1.arena.refs_wf cr hcr
  have hsz_nat : Spec.fullArenaClauseSizeCore s.core cr = 3 := by
    unfold Spec.fullArenaClauseSizeCore; rw [hsz3]; rfl
  have hle_len := hinv.1.core_ok.arena_len_le
  have har_len := hinv.1.core_ok.arena_len_arr
  have hbd : cr + 6 ≤ s.core.arena.length := by omega
  refine ⟨hbd, fun hbd' => ?_⟩
  have hgarb : Spec.fullArenaClauseGarb s cr = false := by
    have h48 : s.core.arena[cr]?.getD 0#32 &&& 4718592#32 = 0#32 := hhdr
    change (s.core.arena[cr]?.getD 0#32 &&& 524288#32 != 0#32) = false
    exact garb_false_of_and_480000 h48
  have hlits := arena_clause3_lits hsz_nat hbd'
  have hlt := hinv.2.1.arena.lits_lt cr hcr hgarb
  have hent := hinv.2.1.arena.entails cr hcr hgarb
  change (cnfOfClauses F_cur).EntailsClause
    (cnfClause (Spec.fullArenaClauseLitsCore s.core cr)) at hent
  rw [hlits] at hent
  refine ⟨hlt _ ?_, hlt _ ?_, hlt _ ?_, hent⟩
  · change _ ∈ Spec.fullArenaClauseLitsCore s.core cr; rw [hlits]; simp
  · change _ ∈ Spec.fullArenaClauseLitsCore s.core cr; rw [hlits]; simp
  · change _ ∈ Spec.fullArenaClauseLitsCore s.core cr; rw [hlits]; simp

private theorem eb_addBin_dense {c : Spec.FullCfg} {F0 : Std.Sat.CNF Nat}
    {F_cur : List (List Nat)} {s s' : Spec.FullState}
    (hinv : Spec.FullDenseInvW c F0 F_cur s)
    (hl' : Spec.FullState.LengthsOk c s')
    (hw' : Spec.FullWitnessInv c F0 F_cur s'.core)
    (hcl : s'.core.cur_level = s.core.cur_level)
    (hmrk : s'.core.mrk = s.core.mrk)
    (hlm : s'.core.lit_mark = s.core.lit_mark)
    (har : s'.core.arena = s.core.arena)
    (harl : s'.core.arena_len = s.core.arena_len)
    (hll : s'.scratch.last_learned = s.scratch.last_learned)
    (hel : s'.scratch.extend_len = s.scratch.extend_len)
    (hdm : s'.core.dense_mode = s.core.dense_mode) :
    Spec.FullDenseInvW c F0 F_cur s' :=
  ⟨hl', hw', fullAddUnitSpec_fullDenseInvW hinv.2.2.1 hinv.2.2.2.1 hinv.2.2.2.2.1
    hinv.2.2.2.2.2.2 (hcl.trans hinv.2.2.2.2.2.1) hmrk hlm har harl hll hel hdm⟩

private theorem eb_oom_dense {c : Spec.FullCfg} {F0 : Std.Sat.CNF Nat}
    {F_cur : List (List Nat)} {s : Spec.FullState}
    (hinv : Spec.FullDenseInvW c F0 F_cur s) :
    Spec.FullDenseInvW c F0 F_cur
      { core := { s.core with oom := 0#64 }
        scratch := { s.scratch with ant_sz := 1#64 } } := by
  have h1 : Spec.FullDenseInvW c F0 F_cur
      { core := { s.core with oom := 0#64 }, scratch := s.scratch } :=
    eb_addBin_dense hinv ⟨{ hinv.1.core_ok with }, hinv.1.scratch_ok⟩
      (fullWitnessInv_with_oom hinv.2.1 0#64) rfl rfl rfl rfl rfl rfl rfl rfl
  exact fullDenseInvW_with_antsz_ressz h1 1#64 s.scratch.res_sz

/-- Canonical `Func.wp` proof for `full_cong_extract_binaries`. -/
theorem full_cong_extract_binaries_wp (Γ : Env)
    (hCountBins : Γ.Has "full_cong_count_bins" Spec.fullCongCountBinsSpec)
    (hNext : Γ.Has "full_arena_next" fullArenaNextSpec)
    (hEb : Γ.Has "full_cong_eb_match" Spec.fullCongEbMatchSpec)
    (hHasBin : Γ.Has "full_has_bin" fullHasBinSpec)
    (hAddBin : Γ.Has "full_add_bin" fullAddBinSpec) :
    ∀ a m Q X, Spec.fullCongExtractBinariesSpec a m Q X →
      Func.wp Γ full_cong_extract_binaries_body a m Q X := by
  rintro ⟨h, tick_lim, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hinv, hm, hQ⟩
  c0_hsteps!; c0_hsplit
  · c0_hsteps!
    exact hQ 20#64 s m hinv rfl rfl (Or.inr rfl)
      (fun _ => unsat_of_inconsistent_w hinv.2.1 hc) hm
  · clear hc
    refine wp_call_of_spec _ _ (hCountBins _ _ _ _ ⟨c, s, R, rfl, hinv.1,
      fullWatchBounds_of_dense hinv, hm, fun ws1' m1 hws1l hm1 => ?_⟩)
    have hinv1 := fullDenseInvW_with_ws1 hinv hws1l
    let s1 : Spec.FullState := { core := s.core, scratch := { s.scratch with work_stk1 := ws1' } }
    have har32 : c.arena_cap < 4294967296 := by
      have := c.harena; unfold LeanQbe.T.Examples.Kissat.Ref.dimacsBound at this; omega
    have har_len32 : s.core.arena_len < 4294967296 := by
      have := hinv.1.core_ok.arena_len_le; omega
    have har_b64 : (BitVec.ofNat 64 s.core.arena_len).toNat = s.core.arena_len :=
      bv64_ofNat_toNat_lt (by omega)
    c0_hsteps_nogrp
    let J_exit : Tup Val [i64, i64] → Mem 64 → Prop := fun _ me =>
      ∃ se, Spec.FullDenseInvW c F0 F_cur se ∧ se.core.cur_vars = s.core.cur_vars ∧
        se.core.fuel = s.core.fuel ∧ (Spec.FullMem c se ⋆ R) me
    refine LeanQbe.T.wp_join_group (ts := [i64, i64]) J_exit ?_ ?_
    · rintro J_ex ⟨_cr, _tk, ⟨⟩⟩ me ⟨se, hse, hcv, hfu, hme⟩
      c0_hsteps_nogrp
      refine LeanQbe.T.wp_join_group (ts := [i64]) (fun (r, ()) mf =>
        ∃ se', Spec.FullDenseInvW c F0 F_cur se' ∧ se'.core.cur_vars = s.core.cur_vars ∧
          se'.core.fuel = s.core.fuel ∧ (r = 1#64 ∨ r = 20#64) ∧
          (r = 20#64 → F0.Unsat) ∧ (Spec.FullMem c se' ⋆ R) mf) ?_ ?_
      · rintro J_ret ⟨r, ⟨⟩⟩ mf ⟨se', hse', hcv', hfu', hr, huns, hmf⟩
        c0_hsteps!; exact hQ r se' mf hse' hcv' hfu' hr huns hmf
      · intro J_ret hJret; c0_hsteps!; c0_hsplit
        · c0_hsteps!; exact hJret (20#64, ()) me
            ⟨se, hse, hcv, hfu, Or.inr rfl, fun _ => unsat_of_inconsistent_w hse.2.1 hc, hme⟩
        · c0_hsteps!; exact hJret (1#64, ()) me
            ⟨se, hse, hcv, hfu, Or.inl rfl, fun h => absurd h (by decide), hme⟩
    · intro J_ex hJex
      let I_lp : Tup Val [i64, i64] → Mem 64 → Prop := fun (cr, _tk, ⟨⟩) ml =>
        ∃ sl, Spec.FullDenseInvW c F0 F_cur sl ∧ sl.core.cur_vars = s.core.cur_vars ∧
          sl.core.fuel = s.core.fuel ∧ sl.core.arena = s.core.arena ∧
          sl.core.arena_len = s.core.arena_len ∧ cr.toNat ≤ sl.core.arena_len ∧
          (cr.toNat = sl.core.arena_len ∨ cr.toNat ∈ Spec.fullArenaClauseRefs sl) ∧
          (Spec.FullMem c sl ⋆ R) ml
      refine LeanQbe.T.wp_loop_inv I_lp (fun (cr, _, ⟨⟩) _ => s.core.arena_len - cr.toNat) ?_ ?_
      · intro J_lp hJlp; c0_hsteps!
        refine hJlp (0#64, 0#64, ()) m1 ⟨s1, hinv1, rfl, rfl, rfl, rfl, Nat.zero_le _, ?_, hm1⟩
        by_cases hz : 0 < s.core.arena_len
        · exact Or.inr (fullArenaClauseRefs_zero_mem hinv1.2.1 hz)
        · exact Or.inl (by change (0#64).toNat = s.core.arena_len; simp; omega)
      · rintro J_lp ⟨cr, ticks, ⟨⟩⟩ ml
          ⟨sl, hsl, hcv, hfu, har_eq, harl_eq, hcr_le, hcr_ref, hml⟩ ih
        c0_hsteps_nogrp
        · have hcr_lt : cr.toNat < sl.core.arena_len := by omega
          have hcr_mem : cr.toNat ∈ Spec.fullArenaClauseRefs sl := by
            rcases hcr_ref with h | h; · omega
            · exact h
          have hwf := hsl.2.1.arena.refs_wf cr.toNat hcr_mem
          have hc0 : cr.toNat < sl.core.arena.length := by
            have := hsl.1.core_ok.arena_len_le; have := hsl.1.core_ok.arena_len_arr; omega
          have hcr2_nat : (cr + 2#64).toNat = cr.toNat + 2 := by bv_omega
          have hc2 : (cr + 2#64).toNat < sl.core.arena.length := by
            have := hsl.1.core_ok.arena_len_le; have := hsl.1.core_ok.arena_len_arr; omega
          clear hc; c0_hsteps_nogrp
          refine wp_call_of_spec _ _ (hNext _ _ _ _ ⟨c, sl, R, rfl, hsl.1, hml, ?_⟩)
          have hcr_w32 : (cr.setWidth 32).toNat = cr.toNat := by
            change cr.toNat % 4294967296 = cr.toNat
            exact Nat.mod_eq_of_lt (by omega)
          let ncr := BitVec.ofNat 32 (Spec.fullArenaNextOff sl.core.arena sl.core.arena_len
            (cr.setWidth 32).toNat)
          have hnxt_bnd := Spec.fullArenaNextOff_bounds (ar := sl.core.arena)
            (alen := sl.core.arena_len) (cref := cr.toNat) hwf.1
          have hncr64_nat : (ncr.setWidth 64).toNat =
              Spec.fullArenaNextOff sl.core.arena sl.core.arena_len cr.toNat := by
            dsimp only [ncr]; rw [bv_zext32_toNat, hcr_w32]
            exact bv32_ofNat_toNat_lt (by omega)
          have hdec : sl.core.arena_len - (ncr.setWidth 64).toNat <
              sl.core.arena_len - cr.toNat := by rw [hncr64_nat]; omega
          have hncr_ref := fullArenaClauseRefs_next_or_end hsl.2.1 hcr_mem
          c0_hsteps_nogrp
          let J_nxt : Tup Val [i64] → Mem 64 → Prop := fun (_ntk, ⟨⟩) mn =>
            ∃ sn, Spec.FullDenseInvW c F0 F_cur sn ∧ sn.core.cur_vars = s.core.cur_vars ∧
              sn.core.fuel = s.core.fuel ∧ sn.core.arena = s.core.arena ∧
              sn.core.arena_len = s.core.arena_len ∧ (Spec.FullMem c sn ⋆ R) mn
          refine LeanQbe.T.wp_join_group (ts := [i64]) J_nxt ?_ ?_
          · rintro J_nxt_c ⟨ntk, ⟨⟩⟩ mn ⟨sn, hsn, hsncv, hsnfu, hsnar, hsnarl, hmn⟩
            c0_hsteps!
            have hncr_ref' : (ncr.setWidth 64).toNat = sn.core.arena_len ∨
                (ncr.setWidth 64).toNat ∈ Spec.fullArenaClauseRefs sn := by
              rw [hncr64_nat, hsnarl, ← harl_eq]
              change _ = sl.core.arena_len ∨
                Spec.fullArenaNextOff sl.core.arena sl.core.arena_len cr.toNat ∈
                  Spec.fullArenaScanRefs sn.core.arena sn.core.arena_len 0 sn.core.arena_len
              rw [hsnar, ← har_eq, hsnarl, ← harl_eq]; exact hncr_ref
            exact ih (ncr.setWidth 64, ntk, ()) mn (by dsimp only; rw [← harl_eq]; exact hdec)
              ⟨sn, hsn, hsncv, hsnfu, hsnar, hsnarl,
                by rw [hncr64_nat, hsnarl, ← harl_eq]; exact hnxt_bnd.2, hncr_ref', hmn⟩
          · intro J2 hJ2; c0_hsteps_nogrp
            · have hhdr0 : (sl.core.arena[cr.toNat]?.getD 0#32 &&& (524288#32 ||| 4194304#32)) =
                  0#32 := by rw [List.getElem?_eq_getElem hc0, Option.getD_some]; assumption
              have hsz3 : sl.core.arena[cr.toNat + 2]?.getD 0#32 = 3#32 := by
                rw [← hcr2_nat, List.getElem?_eq_getElem hc2, Option.getD_some]
                simpa using hc
              have ⟨hcr6, hcl3⟩ := eb_clause3_lits hsl hcr_mem hhdr0 hsz3
              have ⟨hl0_lt, hl1_lt, hl2_lt, hent3⟩ := hcl3 hcr6
              have hc3 : (cr + 3#64).toNat < sl.core.arena.length := by bv_omega
              have hc4 : (cr + 4#64).toNat < sl.core.arena.length := by bv_omega
              have hc5 : (cr + 5#64).toNat < sl.core.arena.length := by bv_omega
              clear hc; c0_hsteps_nogrp
              let l0 := sl.core.arena[(cr + 3#64).toNat]'hc3
              let l1 := sl.core.arena[(cr + 4#64).toNat]'hc4
              let l2 := sl.core.arena[(cr + 5#64).toNat]'hc5
              have hl0_eq : l0 = sl.core.arena[cr.toNat + 3]'(by omega) := by
                dsimp only [l0]; congr 1; bv_omega
              have hl1_eq : l1 = sl.core.arena[cr.toNat + 4]'(by omega) := by
                dsimp only [l1]; congr 1; bv_omega
              have hl2_eq : l2 = sl.core.arena[cr.toNat + 5]'(by omega) := by
                dsimp only [l2]; congr 1; bv_omega
              simp only [← hl0_eq] at hl0_lt hent3
              simp only [← hl1_eq] at hl1_lt hent3
              simp only [← hl2_eq] at hl2_lt hent3
              have hv0 : (l0.setWidth 64).toNat < sl.core.vals.length := by
                rw [bv_zext32_toNat]; have := hsl.1.core_ok.vals_len
                have := hsl.1.core_ok.cur_vars_le; omega
              have hv1 : (l1.setWidth 64).toNat < sl.core.vals.length := by
                rw [bv_zext32_toNat]; have := hsl.1.core_ok.vals_len
                have := hsl.1.core_ok.cur_vars_le; omega
              have hv2 : (l2.setWidth 64).toNat < sl.core.vals.length := by
                rw [bv_zext32_toNat]; have := hsl.1.core_ok.vals_len
                have := hsl.1.core_ok.cur_vars_le; omega
              dsimp only [l0, l1, l2] at hv0 hv1 hv2
              refine LeanQbe.T.wp_join_group (ts := [i64]) J_nxt ?_ ?_
              · rintro _ ⟨ntk, ⟨⟩⟩ mn hmn
                c0_hsteps!; exact hJ2 (ntk, ()) mn hmn
              · intro J3 hJ3; c0_hsteps_nogrp
                · clear hc
                  let J_add : Tup Val [i32, i32, .bool] → Mem 64 → Prop :=
                    fun (ba, bb, found, ⟨⟩) ma =>
                      ma = ml ∧ (found = true →
                        ba.toNat < 2 * sl.core.cur_vars ∧
                        bb.toNat < 2 * sl.core.cur_vars ∧
                        (cnfOfClauses F_cur).EntailsClause (cnfClause [ba.toNat, bb.toNat]))
                  refine LeanQbe.T.wp_join_group (ts := [i32, i32, .bool]) J_add ?_ ?_
                  · rintro _ ⟨ba, bb, found, ⟨⟩⟩ ma ⟨hma_eq, hfound⟩; subst ma
                    refine LeanQbe.T.wp_join_group (ts := [i64]) J_nxt ?_ ?_
                    · rintro _ ⟨ntk, ⟨⟩⟩ mn hmn
                      c0_hsteps!; exact hJ3 (ntk, ()) mn hmn
                    · intro J5 hJ5; c0_hsteps_nogrp
                      · have ⟨hba, hbb, hbin_ent⟩ := hfound hc
                        clear hc
                        refine wp_call_of_spec _ _ (hHasBin _ _ _ _
                          ⟨c, F0, F_cur, sl, R, rfl, hsl.1, hsl.2.1, hml, fun ok hok => ?_⟩)
                        c0_hsteps_nogrp
                        · exact hJ5 (ticks + 1#64, ()) ml ⟨sl, hsl, hcv, hfu, har_eq, harl_eq, hml⟩
                        · clear hc
                          refine wp_call_of_spec _ _ (hAddBin _ _ _ _
                            ⟨c, F0, F_cur, sl, R, rfl, hsl.1, hsl.2.1, hsl.2.2.2.2.2.1,
                              fun _ _ => hbin_ent, hml, fun r vals' flags' lvl' rsns' trl' tp'
                              te' unass' unfl' wvec' wstk' wlen' wu' nb' oom' inc' phases'
                              wsort' m2 hl2 hw2 hr h20 hoom hm2 => ?_⟩)
                          let s2 : Spec.FullState := {
                            core := { sl.core with
                              vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                              trl := trl', trail_pos := tp', trail_end := te',
                              unassigned := unass', unflushed := unfl', wvec := wvec',
                              wstk := wstk', wlen := wlen', wusable := wu',
                              num_binary := nb', oom := oom', inconsistent := inc' }
                            scratch := { sl.scratch with phases := phases', wsort := wsort' } }
                          have hinv2 := eb_addBin_dense hsl hl2 hw2 rfl rfl rfl rfl rfl rfl rfl rfl
                          c0_hsteps_nogrp
                          · have hr20 : r = 20#64 := by assumption
                            exact hQ 20#64 s2 m2 hinv2 hcv hfu (Or.inr rfl)
                              (fun _ => (h20 hr20).1) hm2
                          · exact hJex (cr, ticks + 1#64 + 2#64, ()) _
                              ⟨_, eb_oom_dense hinv2, hcv, hfu, ‹_›⟩
                          · exact hJ5 (ticks + 1#64 + 2#64, ()) m2
                              ⟨s2, hinv2, hcv, hfu, har_eq, harl_eq, hm2⟩
                      · exact hJ5 (ticks + 1#64, ()) ml ⟨sl, hsl, hcv, hfu, har_eq, harl_eq, hml⟩
                  · intro Jadd hJadd
                    dsimp only [l0, l1, l2] at hl0_lt hl1_lt hl2_lt hent3
                    refine wp_call_of_spec _ _ (hEb _ _ _ _ ⟨c, F0, F_cur, sl, R, rfl,
                      hsl.1, hsl.2.1, hl0_lt, hml, fun ok1 hok1 => ?_⟩)
                    c0_hsteps_nogrp
                    · refine hJadd (l1, l2, true, ()) ml ⟨rfl, fun _ => ⟨hl1_lt, hl2_lt, ?_⟩⟩
                      exact eb_resolve_pair (eb_entails3_rot1 hent3) (hok1 hc)
                    · clear hc
                      refine LeanQbe.T.wp_join_group (ts := [i32, i32, .bool]) J_add ?_ ?_
                      · rintro _ ⟨ba, bb, found, ⟨⟩⟩ ma hma
                        c0_hsteps!; exact hJadd (ba, bb, found, ()) ma hma
                      · intro Jadd2 hJadd2
                        refine wp_call_of_spec _ _ (hEb _ _ _ _ ⟨c, F0, F_cur, sl, R, rfl,
                          hsl.1, hsl.2.1, hl1_lt, hml, fun ok2 hok2 => ?_⟩)
                        c0_hsteps_nogrp
                        · refine hJadd2 (l0, l2, true, ()) ml ⟨rfl, fun _ => ⟨hl0_lt, hl2_lt, ?_⟩⟩
                          exact eb_resolve_pair (eb_entails3_swap23 hent3) (hok2 hc)
                        · clear hc
                          refine LeanQbe.T.wp_join_group (ts := [i32, i32, .bool]) J_add ?_ ?_
                          · rintro _ ⟨ba, bb, found, ⟨⟩⟩ ma hma
                            c0_hsteps!; exact hJadd2 (ba, bb, found, ()) ma hma
                          · intro Jadd3 hJadd3
                            refine wp_call_of_spec _ _ (hEb _ _ _ _ ⟨c, F0, F_cur, sl, R, rfl,
                              hsl.1, hsl.2.1, hl2_lt, hml, fun ok3 hok3 => ?_⟩)
                            c0_hsteps_nogrp
                            · refine hJadd3 (l0, l1, true, ()) ml
                                ⟨rfl, fun _ => ⟨hl0_lt, hl1_lt, ?_⟩⟩
                              exact eb_resolve_pair hent3 (hok3 hc)
                            · exact hJadd3 (0#32, 0#32, false, ()) ml
                                ⟨rfl, fun hf => Bool.noConfusion hf⟩
                · exact hJ3 (ticks + 1#64, ()) ml ⟨sl, hsl, hcv, hfu, har_eq, harl_eq, hml⟩
                · exact hJ3 (ticks + 1#64, ()) ml ⟨sl, hsl, hcv, hfu, har_eq, harl_eq, hml⟩
                · exact hJ3 (ticks + 1#64, ()) ml ⟨sl, hsl, hcv, hfu, har_eq, harl_eq, hml⟩
            · exact hJ2 (ticks + 1#64, ()) ml ⟨sl, hsl, hcv, hfu, har_eq, harl_eq, hml⟩
            · exact hJ2 (ticks + 1#64, ()) ml ⟨sl, hsl, hcv, hfu, har_eq, harl_eq, hml⟩
        · exact hJex (cr, ticks, ()) ml ⟨sl, hsl, hcv, hfu, hml⟩
        · exact hJex (cr, ticks, ()) ml ⟨sl, hsl, hcv, hfu, hml⟩

end

end LeanQbe.T.Examples.Kissat.Proof.Congruence
