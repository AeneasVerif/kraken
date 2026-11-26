/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep10
public import LeanQbe.T.Examples.Kissat.FullM6CongSubstProof0
import LeanQbe.T.Examples.Kissat.FullCongLemmas1
import LeanQbe.T.Examples.Kissat.FullCongLemmas2
import LeanQbe.T.Examples.Kissat.FullM6CongSubstProof2a
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb

/-!
# Kissat Fidelity Step 10 Proofs — Congruence Clause Lookup (`FullFidelityStep10ProofCong`)

UNSAT-only parametric `(Γ : Env)` `Func.wp` proof (`public section`, `0` `@[expose]` on
theorems/lemmas, `0` `import all`, `std3`, `XPost`-polymorphic) for:
- `full_cong_has_clause_k_step10_wp` (`FullM6CongSubst.m6CongHasClauseKSpec`): tracks
  `matched_cnt` across marked unassigned literals and requires `ok && matched_cnt >= k` so
  all-root-falsified clauses cannot vacuously match (`[P2]` audit defect).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep10

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullCongHelpers
open LeanQbe.T.Examples.Kissat.FullM6CongSubst
open scoped LeanQbe.T.Examples.Kissat.FullM3CongBva.M3HeadTactics
open scoped LeanQbe.T.Examples.Kissat.FullM6CongSubst.M6HeadTactics
open scoped FullArenaTactics Full.FullCongTactics
open Kraken.Bedrock2.Test

section CongStep10Helpers

private theorem s10_slice_pop_step {F_cur : List (List Nat)} {k : FullCoreState} {a p rem : Nat}
    (hslice : if k.dense_mode = 0#64 then WatchSliceOk F_cur k a p rem
      else DenseWatchSliceOk F_cur k a p rem) (hpos : 0 < rem) :
    ∃ w0 : BitVec 32, k.wstk[p]? = some w0 ∧
      ((w0 &&& 0x80000000#32) ≠ 0#32 ∧
        (cnfOfClauses F_cur).EntailsClause (cnfClause [a, (w0 &&& 0x7FFFFFFF#32).toNat]) ∧
        (if k.dense_mode = 0#64 then WatchSliceOk F_cur k a (p + 1) (rem - 1)
         else DenseWatchSliceOk F_cur k a (p + 1) (rem - 1)) ∨
       (w0 &&& 0x80000000#32) = 0#32 ∧ 2 ≤ rem ∧
        ∃ cr : BitVec 32, k.wstk[p + 1]? = some cr ∧ cr.toNat ∈ fullArenaClauseRefsCore k ∧
        (if k.dense_mode = 0#64 then WatchSliceOk F_cur k a (p + 2) (rem - 2)
         else DenseWatchSliceOk F_cur k a (p + 2) (rem - 2))) := by
  by_cases hdm : k.dense_mode = 0#64 <;> simp only [hdm, ↓reduceIte] at hslice ⊢
  · cases hslice with
    | empty => omega
    | bin hp hf _ _ hent hrest => exact ⟨_, hp, Or.inl ⟨hf, hent, hrest⟩⟩
    | large hp hp1 hf _ href hrest => exact ⟨_, hp, Or.inr ⟨hf, by omega, _, hp1, href, hrest⟩⟩
  · cases hslice with
    | empty => omega
    | bin hp hf _ _ hent hrest => exact ⟨_, hp, Or.inl ⟨hf, hent, hrest⟩⟩
    | occ hp hp1 hf _ _ href hrest => exact ⟨_, hp, Or.inr ⟨hf, by omega, _, hp1, href, hrest⟩⟩

private theorem s10_bin_subsumes_unass {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hw : FullWitnessInv c F0 F_cur s.core) (hcl0 : s.core.cur_level = 0)
    {a b : Nat} {unass : List Nat} (hb_lt : b < 2 * s.core.cur_vars)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [a, b]))
    (ha_in : a ∈ unass) (hb_cov : s.core.vals[b]?.getD 0#8 = 0xFF#8 ∨ b ∈ unass) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause unass) := by
  refine entails_of_eval_mem fun α hα => ?_
  have hs := (clauseEvalVal_iff α _).mpr ((CNF.entails_clause_def.mp hent) α hα)
  rw [clauseEvalVal] at hs
  simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true] at hs
  rcases hs with ha_t | hb_t
  · exact ⟨a, ha_in, ha_t⟩
  · rcases hb_cov with hff | hb_in
    · exfalso
      obtain ⟨i, hi, heq⟩ := (hw.vals_false_iff b hb_lt).mp hff
      have hlvl0 : (s.core.lvl[(s.core.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by
        have := hw.lvl_le i hi; omega
      have hunit := hw.level0_sound i hi hlvl0; rw [heq] at hunit
      have hsu := (CNF.entails_clause_def.mp hunit) α hα
      rw [← clauseEvalVal_iff, clauseEvalVal] at hsu
      simp only [List.any_cons, List.any_nil, Bool.or_false,
        show b ^^^ 1 = litNeg b from rfl, evalLitVal_litNeg, hb_t] at hsu
      cases hsu
    · exact ⟨b, hb_in, hb_t⟩

private theorem s10_c0_load_full_tmp0 {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (FullMem c s ⋆ R) m) (h0 : 0 < s.core.tmp.length) :
    loadVal m i32 c.pTmp = some (s.core.tmp[0]'h0) := by
  simpa using FullArenaTactics.load_full_tmp (i := 0) h0 hm

private theorem s10_c0_load_full_tmp0_add {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (FullMem c s ⋆ R) m) (h0 : 0 < s.core.tmp.length) :
    loadVal m i32 (c.pTmp + 0#64) = some (s.core.tmp[0]'h0) := by
  simpa using FullArenaTactics.c0_load_full_tmp (i := 0#64) (by simpa using h0) hm

end CongStep10Helpers

attribute [local c0_load] s10_c0_load_full_tmp0 s10_c0_load_full_tmp0_add

/-- Parametric `Func.wp` proof for `fidStep10CongHasClauseKFn` (`full_cong_has_clause_k`,
requiring `ok && matched_cnt >= k`) against `FullM6CongSubst.m6CongHasClauseKSpec`. -/
theorem full_cong_has_clause_k_step10_wp (Γ : Env) :
    ∀ args m Q X, m6CongHasClauseKSpec args m Q X →
      Func.wp Γ fidStep10CongHasClauseKFn.body args m Q X := by
  rintro ⟨h, k, ⟨⟩⟩ m0 Q X
    ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hmk, hnd, hcl0, hk3, hk5, hkcv, htmp_lt, htmp_dis, hm0, hQ⟩
  have hmx := c.hmaxv; have hwc := c.hwcap; have hac := c.harena
  unfold dimacsBound at hmx hwc hac
  have hcl := hlen.core_ok; have hsl := hlen.scratch_ok
  have hcv_le := hcl.cur_vars_le; have htmpl := hcl.tmp_len_arr; have hlml := hcl.lit_mark_len
  have hwvl := hcl.wvec_len; have hwsl := hcl.wstk_len_arr; have hwle := hcl.wlen_le
  have harl := hcl.arena_len_arr; have hale := hcl.arena_len_le; have hvl := hcl.vals_len
  have h0_tmp : 0 < s.core.tmp.length := by omega
  let min_l0 := s.core.tmp[0]'h0_tmp
  have hmin0_lt : min_l0.toNat < 2 * s.core.cur_vars := by
    have := htmp_lt 0 (by omega)
    rwa [List.getElem?_eq_getElem h0_tmp, Option.getD_some] at this
  have hshl0_1 : (min_l0.setWidth 64 <<< (1 : Nat) + 1#64).toNat = 2 * min_l0.toNat + 1 := by
    rw [BitVec.toNat_add, FullCongHelpers.bv64_shl1_toNat, bv_zext32_toNat]
    show (2 * min_l0.toNat % 2 ^ 64 + 1) % 2 ^ 64 = 2 * min_l0.toNat + 1; omega
  have hmin0_wvec : (min_l0.setWidth 64 <<< (1 : Nat) + 1#64).toNat < s.core.wvec.length := by
    omega
  have hmin0_wvec_se :
      (min_l0.setWidth 64 <<< ((1#32 : BitVec 32).signExtend 64).toNat + 1#64).toNat <
        s.core.wvec.length := hmin0_wvec
  have hmin0_wvec_bv :
      (min_l0.setWidth 64 <<< ((1#32 : BitVec 32).signExtend 64) + 1#64).toNat <
        s.core.wvec.length := hmin0_wvec
  let unassLits := (List.range k.toNat).map fun idx => (s.core.tmp[idx]?.getD 0#32).toNat
  have hmin0_in : min_l0.toNat ∈ unassLits := by
    refine List.mem_map.mpr ⟨0, List.mem_range.mpr (by omega), ?_⟩
    rw [List.getElem?_eq_getElem h0_tmp, Option.getD_some]
  have hnl_eq : (BitVec.ofNat 64 s.core.cur_vars <<< (1 : Nat)).toNat = 2 * s.core.cur_vars := by
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.shiftLeft_eq, Nat.pow_one, Nat.mul_comm, Nat.mod_eq_of_lt (by omega)]
  unfold fidStep10CongHasClauseKFn; dsimp only; fc_split_fast
  · exfalso
    have : k.toNat < 3 := by simp only [BitVec.ult, decide_eq_true_eq] at hc; exact hc
    omega
  clear hc; fc_split_fast
  · exfalso
    have : 5 < k.toNat := by simp only [BitVec.ult, decide_eq_true_eq] at hc; exact hc
    omega
  clear hc; fc_split_fast
  · exfalso
    have : s.core.cur_vars < k.toNat := by
      simp only [BitVec.ult, decide_eq_true_eq] at hc; bv_omega
    omega
  · clear hc; fc_steps
    refine wp_loop_inv (ts := [i32, i32, i32])
      (fun (min_l, _min_d, i, ()) mi => ∃ lm' : List (BitVec 8),
        lm'.length = 2 * c.max_vars ∧ i.toNat ≤ k.toNat ∧ min_l.toNat < 2 * s.core.cur_vars ∧
        min_l.toNat ∈ unassLits ∧
        (∀ l < 2 * c.max_vars, lm'[l]?.getD 0#8 = 0#8 ∨ l ∈ unassLits) ∧
        (FullMem c { s with core := { s.core with lit_mark := lm' } } ⋆ R) mi)
      (fun (_, _, i, ()) _ => k.toNat - i.toNat)
      (fun J1 hJ1 => by
        fc_let; refine hJ1 (min_l0, _, 0#32, ()) m0
          ⟨s.core.lit_mark, hlml, Nat.zero_le _, hmin0_lt, hmin0_in,
           fun l hl => Or.inl (hmk.2 l hl), hm0⟩)
      (fun J1 (min_l, min_d, i, ()) mi ⟨lm', hlml', hi_le, hmin_lt, hmin_in, hlm_inv, hmi⟩
        ih1 => ?_)
    let si : FullState := { s with core := { s.core with lit_mark := lm' } }
    fc_split_fast
    · have hi_lt : i.toNat < k.toNat := by
        simp only [BitVec.ult, decide_eq_true_eq] at hc; exact hc
      have hi1_n : (i + 1#32).toNat = i.toNat + 1 := by bv_omega
      have hi_tmp : (i.setWidth 64).toNat < si.core.tmp.length := by
        rw [bv_zext32_toNat]; change i.toNat < s.core.tmp.length; omega
      let tl := si.core.tmp[(i.setWidth 64).toNat]'hi_tmp
      have htl_eq : tl = s.core.tmp[i.toNat]?.getD 0#32 := by
        dsimp only [tl, si]; rw [List.getElem?_eq_getElem (by omega : i.toNat < s.core.tmp.length),
          Option.getD_some]; exact list_getElem_congr (bv_zext32_toNat i) _ _
      have htl_lt : tl.toNat < 2 * s.core.cur_vars := by rw [htl_eq]; exact htmp_lt i.toNat hi_lt
      have htl_in : tl.toNat ∈ unassLits := by
        rw [htl_eq]; exact List.mem_map.mpr ⟨i.toNat, List.mem_range.mpr hi_lt, rfl⟩
      have htl_lm : (tl.setWidth 64).toNat < si.core.lit_mark.length := by
        rw [bv_zext32_toNat]; change tl.toNat < lm'.length; omega
      have htl_wv : (tl.setWidth 64 <<< (1 : Nat) + 1#64).toNat < si.core.wvec.length := by
        rw [BitVec.toNat_add, FullCongHelpers.bv64_shl1_toNat, bv_zext32_toNat]
        change (2 * tl.toNat % 2 ^ 64 + 1) % 2 ^ 64 < s.core.wvec.length; omega
      have htl_wv_se :
          (tl.setWidth 64 <<< ((1#32 : BitVec 32).signExtend 64).toNat + 1#64).toNat <
            si.core.wvec.length := htl_wv
      have htl_wv_bv :
          (tl.setWidth 64 <<< ((1#32 : BitVec 32).signExtend 64) + 1#64).toNat <
            si.core.wvec.length := htl_wv
      fc_to_group
      let lm'' := lm'.set (tl.setWidth 64).toNat ((i + 1#32).setWidth 8)
      have hlm''_len : lm''.length = 2 * c.max_vars := by simp [lm'', hlml']
      have hlm''_inv : ∀ l < 2 * c.max_vars, lm''[l]?.getD 0#8 = 0#8 ∨ l ∈ unassLits := by
        intro l hl; dsimp only [lm'']
        by_cases hltl : l = (tl.setWidth 64).toNat
        · right; rw [hltl, bv_zext32_toNat]; exact htl_in
        · rw [List.getElem?_set_ne (Ne.symm hltl)]; exact hlm_inv l hl
      have hmi' : (FullMem c { s with core := { s.core with lit_mark := lm'' } } ⋆ R) m := hm
      refine wp_join_group (ts := [i32, i32])
        (fun (min_l', _min_d', ()) m' =>
          m' = m ∧ min_l'.toNat < 2 * s.core.cur_vars ∧ min_l'.toNat ∈ unassLits) ?_ ?_
      · rintro _ ⟨min_l', min_d', ⟨⟩⟩ m' ⟨hm', hml'_lt, hml'_in⟩
        subst m'; fc_let
        exact ih1 (min_l', min_d', i + 1#32, ()) m (by dsimp only; omega)
          ⟨lm'', hlm''_len, by omega, hml'_lt, hml'_in, hlm''_inv, hmi'⟩
      · intro Jd hJd; fc_steps
        · exact hJd (tl, _, ()) m ⟨rfl, htl_lt, htl_in⟩
        · exact hJd (min_l, min_d, ()) m ⟨rfl, hmin_lt, hmin_in⟩
    · clear hc
      have hw_bd := hw.watches.bounds min_l.toNat hmin_lt
      have hshl_m : (min_l.setWidth 64 <<< (1 : Nat)).toNat = 2 * min_l.toNat := by
        rw [FullCongHelpers.bv64_shl1_toNat, bv_zext32_toNat]; omega
      have hshl1_m : (min_l.setWidth 64 <<< (1 : Nat) + 1#64).toNat = 2 * min_l.toNat + 1 := by
        rw [BitVec.toNat_add, hshl_m]
        show (2 * min_l.toNat + 1) % 2 ^ 64 = 2 * min_l.toNat + 1; omega
      have hslice0 : if s.core.dense_mode = 0#64 then
            WatchSliceOk F_cur s.core min_l.toNat (fullWatchOffCore s.core min_l.toNat)
              (fullWatchSizeCore s.core min_l.toNat)
          else DenseWatchSliceOk F_cur s.core min_l.toNat (fullWatchOffCore s.core min_l.toNat)
              (fullWatchSizeCore s.core min_l.toNat) := by
        have hwat := hw.watches; unfold ModeWatchesInv at hwat
        by_cases hdm : s.core.dense_mode = 0#64 <;> simp only [hdm, ↓reduceIte] at hwat ⊢
        · exact hwat.slices min_l.toNat hmin_lt
        · exact hwat.slices min_l.toNat hmin_lt
      have hml_wv0 : (min_l.setWidth 64 <<< (1 : Nat)).toNat < si.core.wvec.length := by
        change _ < s.core.wvec.length; omega
      have hml_wv1 : (min_l.setWidth 64 <<< (1 : Nat) + 1#64).toNat < si.core.wvec.length := by
        change _ < s.core.wvec.length; omega
      fc_to_group
      generalize hoff_v :
        (si.core.wvec[(min_l.setWidth 64 <<< (1 : Nat)).toNat]'hml_wv0).setWidth 64 = off
      generalize hwsz_v :
        (si.core.wvec[(min_l.setWidth 64 <<< (1 : Nat) + 1#64).toNat]'hml_wv1).setWidth 64 = wsz
      have hoff_n : off.toNat = fullWatchOffCore s.core min_l.toNat := by
        rw [← hoff_v, bv_zext32_toNat]; unfold fullWatchOffCore
        rw [List.getElem?_eq_getElem (by omega : 2 * min_l.toNat < s.core.wvec.length),
          Option.getD_some]
        exact congrArg BitVec.toNat (list_getElem_congr hshl_m (by omega) (by omega))
      have hwsz_n : wsz.toNat = fullWatchSizeCore s.core min_l.toNat := by
        rw [← hwsz_v, bv_zext32_toNat]; unfold fullWatchSizeCore
        rw [List.getElem?_eq_getElem (by omega : 2 * min_l.toNat + 1 < s.core.wvec.length),
          Option.getD_some]
        exact congrArg BitVec.toNat (list_getElem_congr hshl1_m (by omega) (by omega))
      have hend_n : (off + wsz).toNat = off.toNat + wsz.toNat := by bv_omega
      refine wp_loop_break_group (brkTs := [.bool, i64]) (lpTs := [i64])
        (fun (res, _, ()) mb => mb = mi ∧
          (res = true → (cnfOfClauses F_cur).EntailsClause (cnfClause unassLits)))
        (fun rem (p, ()) mp =>
          mp = mi ∧ p.toNat ≤ (off + wsz).toNat ∧ rem = (off + wsz).toNat - p.toNat ∧
          (if s.core.dense_mode = 0#64 then
             WatchSliceOk F_cur s.core min_l.toNat p.toNat ((off + wsz).toNat - p.toNat)
           else DenseWatchSliceOk F_cur s.core min_l.toNat p.toNat ((off + wsz).toNat - p.toNat)))
        ?_ ?_ ?_
      · rintro _ ⟨res, _, ⟨⟩⟩ mb ⟨hmb, hres⟩
        rw [hmb]; fc_steps
        refine wp_loop_inv
          (fun (i3, ()) mc => ∃ lm3 : List (BitVec 8),
            lm3.length = 2 * c.max_vars ∧ i3.toNat ≤ k.toNat ∧
            (∀ l < 2 * c.max_vars, lm3[l]?.getD 0#8 = 0#8 ∨
              ∃ idx, i3.toNat ≤ idx ∧ idx < k.toNat ∧
                (s.core.tmp[idx]?.getD 0#32).toNat = l) ∧
            (FullMem c { s with core := { s.core with lit_mark := lm3 } } ⋆ R) mc)
          (fun (i3, ()) _ => k.toNat - i3.toNat)
          (fun J3 hJ3 => by
            fc_let; refine hJ3 (0#32, ()) mi ⟨lm', hlml', Nat.zero_le _, fun l hl => ?_, hmi⟩
            rcases hlm_inv l hl with h0 | hmem
            · exact Or.inl h0
            · obtain ⟨idx, hrng, heq⟩ := List.mem_map.mp hmem
              exact Or.inr ⟨idx, Nat.zero_le _, List.mem_range.mp hrng, heq⟩)
          (fun J3 (i3, ()) mc ⟨lm3, hlml3, hi3_le, hlm3_inv, hmc⟩ ih3 => ?_)
        fc_split_fast
        · have hi3_lt : i3.toNat < k.toNat := by
            simp only [BitVec.ult, decide_eq_true_eq] at hc; exact hc
          have hi3_1 : (i3 + 1#32).toNat = i3.toNat + 1 := by bv_omega
          have hi3_tmp : (i3.setWidth 64).toNat < s.core.tmp.length := by
            rw [bv_zext32_toNat]; omega
          let tl := s.core.tmp[(i3.setWidth 64).toNat]'hi3_tmp
          have htl_eq : tl = s.core.tmp[i3.toNat]?.getD 0#32 := by
            dsimp only [tl]; rw [List.getElem?_eq_getElem (by omega : i3.toNat < s.core.tmp.length),
              Option.getD_some]; exact list_getElem_congr (bv_zext32_toNat i3) _ _
          have htl_lt : tl.toNat < 2 * s.core.cur_vars := by
            rw [htl_eq]; exact htmp_lt i3.toNat hi3_lt
          have htl_lm : (tl.setWidth 64).toNat < lm3.length := by rw [bv_zext32_toNat]; omega
          fc_steps
          let lm3' := lm3.set (tl.setWidth 64).toNat 0#8
          have hlm3'_inv : ∀ l < 2 * c.max_vars, lm3'[l]?.getD 0#8 = 0#8 ∨
              ∃ idx, (i3 + 1#32).toNat ≤ idx ∧ idx < k.toNat ∧
                (s.core.tmp[idx]?.getD 0#32).toNat = l := by
            intro l hl; dsimp only [lm3']
            by_cases hltl : l = (tl.setWidth 64).toNat
            · left; rw [hltl, List.getElem?_set_self htl_lm, Option.getD_some]
            · rw [List.getElem?_set_ne (Ne.symm hltl)]
              rcases hlm3_inv l hl with h0 | ⟨idx, h1, h2, h3⟩
              · exact Or.inl h0
              · right; refine ⟨idx, ?_, h2, h3⟩
                have hne : idx ≠ i3.toNat := fun he => by
                  subst he; apply hltl; rw [bv_zext32_toNat, htl_eq, h3]
                omega
          exact ih3 (i3 + 1#32, ()) m (by dsimp only; omega)
            ⟨lm3', by simp [lm3', hlml3], by omega, hlm3'_inv, hm⟩
        · have hi3_eq : i3.toNat = k.toNat := by
            simp only [BitVec.ult, decide_eq_false_iff_not] at hc; omega
          have hclear : FullLitMarksClear c { s with core := { s.core with lit_mark := lm3 } } :=
            ⟨hmk.1, fun l hl => by
              rcases hlm3_inv l hl with h0 | ⟨idx, h1, h2, _⟩
              · exact h0
              · omega⟩
          fc_steps
          exact hQ res { s with core := { s.core with lit_mark := lm3 } } mc
            ⟨{ hcl with lit_mark_len := hlml3 }, hsl⟩ rfl rfl hclear hres hmc
      · rintro B L rem ⟨p, ⟨⟩⟩ mp hB hL ⟨hmp, hp_le, rfl, hslice⟩
        rw [hmp]; fc_split_fast
        · have hp_lt : p.toNat < (off + wsz).toNat := by
            simp only [BitVec.ult, decide_eq_true_eq] at hc; bv_omega
          have hp_w : p.toNat < s.core.wstk.length := by omega
          obtain ⟨w0, hw0_get, hcase⟩ := s10_slice_pop_step hslice (by omega)
          have hw0_eq : s.core.wstk[p.toNat]'hp_w = w0 := by
            rw [List.getElem?_eq_getElem hp_w] at hw0_get; exact Option.some.inj hw0_get
          have hp1_n : (p + 1#64).toNat = p.toNat + 1 := by bv_omega
          fc_split_fast
          · rcases hcase with ⟨_, hent_bin, hrest⟩ | ⟨hf0, _⟩
            · have hcont1 : L (p + 1#64, ()) mi :=
                hL ((off + wsz).toNat - (p + 1#64).toNat) (p + 1#64, ()) mi (by omega)
                  ⟨rfl, by omega, rfl, by simpa [hp1_n, Nat.sub_sub] using hrest⟩
              let ot := w0 &&& 0x7FFFFFFF#32
              fc_split_fast
              · have hot_lt : ot.toNat < 2 * s.core.cur_vars := by
                  simp only [BitVec.ult, decide_eq_true_eq] at hc
                  rw [hw0_eq, bv_zext32_toNat, hnl_eq] at hc; exact hc
                have hot_v : (ot.setWidth 64).toNat < si.core.vals.length := by
                  rw [bv_zext32_toNat]; change ot.toNat < s.core.vals.length; omega
                have hot_v_w :
                    ((s.core.wstk[p.toNat]'hp_w &&& 0x7FFFFFFF#32).setWidth 64).toNat <
                      si.core.vals.length := by rw [hw0_eq]; exact hot_v
                have hot_v' : ot.toNat < s.core.vals.length := by
                  rw [bv_zext32_toNat] at hot_v; exact hot_v
                have hot_lm : (ot.setWidth 64).toNat < si.core.lit_mark.length := by
                  rw [bv_zext32_toNat]; change ot.toNat < lm'.length; omega
                have hot_lm_w :
                    ((s.core.wstk[p.toNat]'hp_w &&& 0x7FFFFFFF#32).setWidth 64).toNat <
                      si.core.lit_mark.length := by rw [hw0_eq]; exact hot_lm
                have hdom_ot : s.core.vals[ot.toNat]'hot_v' = 0#8 ∨
                    s.core.vals[ot.toNat]'hot_v' = 1#8 ∨
                    s.core.vals[ot.toNat]'hot_v' = 0xFF#8 := by
                  have h := hw.vals_domain ot.toNat hot_lt
                  rwa [List.getElem?_eq_getElem hot_v', Option.getD_some] at h
                clear hc; fc_split_fast
                · have hov_ff : s.core.vals[ot.toNat]?.getD 0#8 = 0xFF#8 := by
                    rw [List.getElem?_eq_getElem hot_v', Option.getD_some]
                    have hidx :
                        ((s.core.wstk[p.toNat]'hp_w &&& 2147483647).setWidth 64).toNat =
                          ot.toNat := by rw [hw0_eq, bv_zext32_toNat]; rfl
                    rw [list_getElem_congr hidx _ hot_v'] at hc
                    rcases hdom_ot with hv | hv | hv
                    · exfalso; rw [hv] at hc; cases hc
                    · exfalso; rw [hv] at hc; cases hc
                    · exact hv
                  fc_steps
                  exact hB (true, p + 1#64, ()) mi ⟨rfl, fun _ =>
                    s10_bin_subsumes_unass hw hcl0 hot_lt hent_bin hmin_in (Or.inl hov_ff)⟩
                · clear hc; fc_split_fast
                  · clear hc; fc_split_fast
                    · have hot_in : ot.toNat ∈ unassLits := by
                        have hne0 : lm'[ot.toNat]?.getD 0#8 ≠ 0#8 := by
                          intro h0
                          have hidx :
                              ((s.core.wstk[p.toNat]'hp_w &&& 2147483647).setWidth 64).toNat =
                                ot.toNat := by rw [hw0_eq, bv_zext32_toNat]; rfl
                          rw [List.getElem?_eq_getElem (by omega : ot.toNat < lm'.length),
                            Option.getD_some] at h0
                          change (BitVec.setWidth 32 (lm'[_]'_) != 0#32) = true at hc
                          rw [list_getElem_congr hidx _ (by omega), h0] at hc; cases hc
                        exact (hlm_inv ot.toNat (by omega)).resolve_left hne0
                      fc_steps
                      exact hB (true, p + 1#64, ()) mi ⟨rfl, fun _ =>
                        s10_bin_subsumes_unass hw hcl0 hot_lt hent_bin hmin_in (Or.inr hot_in)⟩
                    · fc_steps; exact hcont1
                  · fc_steps; exact hcont1
              · fc_steps; exact hcont1
            · exfalso; rw [hw0_eq] at hc
              rw [show (w0 &&& 2147483648 : BitVec 32) = w0 &&& 2147483648#32 from rfl, hf0] at hc
              revert hc; decide
          · rcases hcase with ⟨hf1, _⟩ | ⟨_, hrem2, cr, hcr_get, hcr_ref, hrest2⟩
            · exfalso; rw [hw0_eq] at hc; exact hf1 (by grind)
            · have hp1_n' : (p + 1).toNat = p.toNat + 1 := hp1_n
              have hp1_w : (p + 1).toNat < s.core.wstk.length := by omega
              have hcr_eq : s.core.wstk[(p + 1).toNat]'hp1_w = cr := by
                rw [list_getElem_congr hp1_n' hp1_w (by omega)]
                rw [List.getElem?_eq_getElem (by omega)] at hcr_get
                exact Option.some.inj hcr_get
              have hcr_wf := hw.arena.refs_wf cr.toNat hcr_ref
              have hp2_n : (p + 1#64 + 1#64).toNat = p.toNat + 2 := by bv_omega
              have hcont2 : L (p + 1 + 1, ()) mi :=
                hL ((off + wsz).toNat - (p + 1#64 + 1#64).toNat) (p + 1#64 + 1#64, ()) mi
                  (by omega) ⟨rfl, by omega, rfl, by simpa [hp2_n, Nat.sub_sub] using hrest2⟩
              fc_split_fast
              · exfalso; simp only [BitVec.ule, decide_eq_true_eq] at hc; bv_omega
              · clear hc
                have hcr_arr : cr.toNat < s.core.arena.length := by omega
                have hcr2_arr : cr.toNat + 2 < s.core.arena.length := by omega
                have hcr_z : ((s.core.wstk[(p + 1).toNat]'hp1_w).setWidth 64).toNat <
                    s.core.arena.length := by rw [hcr_eq, bv_zext32_toNat]; exact hcr_arr
                have hcr2_n : ((s.core.wstk[(p + 1).toNat]'hp1_w).setWidth 64 + 2).toNat =
                    cr.toNat + 2 := by
                  rw [hcr_eq, BitVec.toNat_add, bv_zext32_toNat,
                    show (2 : BitVec 64).toNat = 2 from rfl]
                  exact Nat.mod_eq_of_lt (by omega)
                have hcr2_w : ((s.core.wstk[(p + 1).toNat]'hp1_w).setWidth 64 + 2).toNat <
                    s.core.arena.length := by rw [hcr2_n]; omega
                fc_split_fast
                · fc_steps; exact hcont2
                · have hng_red :
                      (s.core.arena[((s.core.wstk[(p + 1).toNat]'hp1_w).setWidth
                        64).toNat]'hcr_z &&& 0x00480000#32) = 0#32 := by simpa using hc
                  clear hc
                  have hng : fullArenaClauseGarb s cr.toNat = false := by
                    unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
                    rw [List.getElem?_eq_getElem hcr_arr, Option.getD_some]
                    exact garb_false_of_and_480000
                      (by rwa [list_getElem_congr (by rw [hcr_eq, bv_zext32_toNat]) hcr_z hcr_arr]
                        at hng_red)
                  let sz_bv := s.core.arena[cr.toNat + 2]'(by omega)
                  have hsz_eq : sz_bv.toNat = fullArenaClauseSizeCore s.core cr.toNat := by
                    unfold fullArenaClauseSizeCore
                    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                  have hsz_cv : sz_bv.toNat ≤ s.core.cur_vars := by
                    rw [hsz_eq]; exact fullArenaClauseSize_le_cur_vars hlen hw hnd hcr_ref hng
                  have hbd_ar : cr.toNat + 3 + sz_bv.toNat ≤ s.core.arena.length := by omega
                  fc_to_group
                  refine wp_loop_break_group (brkTs := [.bool, i32, i32]) (lpTs := [i32, i32])
                    (fun (ok, _mc, _, ()) mb2 => mb2 = mi ∧
                      (ok = true → ∀ q < sz_bv.toNat,
                        let cl := (s.core.arena[cr.toNat + 3 + q]?.getD 0#32).toNat
                        s.core.vals[cl]?.getD 0#8 = 0xFF#8 ∨ cl ∈ unassLits))
                    (fun rem2 (_mc, j, ()) mj => mj = mi ∧ j.toNat ≤ sz_bv.toNat ∧
                      rem2 = sz_bv.toNat - j.toNat ∧
                      ∀ q < j.toNat,
                        let cl := (s.core.arena[cr.toNat + 3 + q]?.getD 0#32).toNat
                        s.core.vals[cl]?.getD 0#8 = 0xFF#8 ∨ cl ∈ unassLits)
                    ?_ ?_ ?_
                  · rintro _ ⟨ok, mc, _, ⟨⟩⟩ mb2 ⟨hmb2, hok⟩
                    rw [hmb2]; fc_split_fast
                    · have hok_t : ok = true := hc
                      clear hc; fc_split_fast
                      · have hcov : ∀ l ∈ fullArenaClauseLits s cr.toNat,
                              s.core.vals[l]?.getD 0#8 = 0xFF#8 ∨ l ∈ unassLits := fun l hl => by
                          obtain ⟨q, hq, hql⟩ :=
                            (mem_fullArenaClauseLitsCore_iff (hsz_eq ▸ hbd_ar)).mp hl
                          rw [← hsz_eq] at hq
                          have h := hok hok_t q hq; dsimp only at h
                          rw [List.getElem?_eq_getElem (by omega :
                            cr.toNat + 3 + q < s.core.arena.length), Option.getD_some, hql] at h
                          exact h
                        fc_steps
                        exact hB (true, p + 1 + 1, ()) mi
                          ⟨rfl, fun _ => unassigned_clause_entails hw hcl0 hcr_ref hng hcov⟩
                      · fc_steps; exact hcont2
                    · fc_steps; exact hcont2
                  · rintro B2 L2 rem2 ⟨mc, j, ⟨⟩⟩ mj hB2 hL2 ⟨hmj, hj_le, rfl, hcov_j⟩
                    rw [hmj]; fc_split_fast
                    · have hj_lt : j.toNat < sz_bv.toNat := by
                        rw [list_getElem_congr hcr2_n hcr2_w hcr2_arr] at hc
                        simp only [BitVec.ult, decide_eq_true_eq] at hc; exact hc
                      have hj1_n : (j + 1#32).toNat = j.toNat + 1 := by bv_omega
                      have hcr3j_n : ((s.core.wstk[(p + 1).toNat]'hp1_w).setWidth 64 + 3 +
                          j.setWidth 64).toNat = cr.toNat + 3 + j.toNat := by
                        have h3 : (cr.toNat + 3) % 2 ^ 64 = cr.toNat + 3 :=
                          Nat.mod_eq_of_lt (by omega)
                        rw [hcr_eq, BitVec.toNat_add, BitVec.toNat_add, bv_zext32_toNat,
                          bv_zext32_toNat, show (3 : BitVec 64).toNat = 3 from rfl, h3,
                          Nat.mod_eq_of_lt (by omega)]
                      have hcr3j_w : ((s.core.wstk[(p + 1).toNat]'hp1_w).setWidth 64 + 3 +
                          j.setWidth 64).toNat < s.core.arena.length := by rw [hcr3j_n]; omega
                      let cl := s.core.arena[cr.toNat + 3 + j.toNat]'(by omega)
                      have hcl_get : cl = s.core.arena[cr.toNat + 3 + j.toNat]?.getD 0#32 := by
                        rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                      have hcl_mem : cl.toNat ∈ fullArenaClauseLits s cr.toNat := by
                        rw [mem_fullArenaClauseLitsCore_iff (hsz_eq ▸ hbd_ar)]
                        exact ⟨j.toNat, by rw [← hsz_eq]; exact hj_lt, rfl⟩
                      have hcl_lt : cl.toNat < 2 * s.core.cur_vars :=
                        hw.arena.lits_lt cr.toNat hcr_ref hng cl.toNat hcl_mem
                      have hcl_eq : s.core.arena[((s.core.wstk[(p + 1).toNat]'hp1_w).setWidth 64 +
                          3 + j.setWidth 64).toNat]'hcr3j_w = cl :=
                        list_getElem_congr hcr3j_n hcr3j_w (by omega)
                      have hcl_v : (cl.setWidth 64).toNat < si.core.vals.length := by
                        rw [bv_zext32_toNat]; change cl.toNat < s.core.vals.length; omega
                      have hcl_lm : (cl.setWidth 64).toNat < si.core.lit_mark.length := by
                        rw [bv_zext32_toNat]; change cl.toNat < lm'.length; omega
                      fc_split_fast
                      · fc_steps; exact hB2 (false, mc, j, ()) mi ⟨rfl, fun h => by cases h⟩
                      · have hne1_cl : s.core.vals[cl.toNat]?.getD 0#8 ≠ 1#8 := by
                          intro h1
                          have hdom : s.core.vals[cl.toNat]'(by omega) = 1#8 := by
                            rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at h1
                            exact h1
                          have hidx : ((s.core.arena[((s.core.wstk[(p + 1).toNat]'hp1_w).setWidth
                              64 + 3 + j.setWidth 64).toNat]'hcr3j_w).setWidth 64).toNat =
                              cl.toNat := by rw [hcl_eq, bv_zext32_toNat]
                          change (0#32).slt
                            (BitVec.signExtend 32 (s.core.vals[_]'_)) = false at hc
                          rw [list_getElem_congr hidx _ (by omega), hdom] at hc; cases hc
                        clear hc; fc_to_group
                        refine wp_join_group (ts := [.bool, i32])
                          (fun (_ok', _mc', ()) mj' => mj' = mi ∧
                            (s.core.vals[cl.toNat]?.getD 0#8 = 0xFF#8 ∨ cl.toNat ∈ unassLits))
                          ?_ ?_
                        · rintro _ ⟨_ok', mc', ⟨⟩⟩ mj' ⟨hmj', hcl_cov⟩
                          rw [hmj']; fc_steps
                          refine hL2 (sz_bv.toNat - (j + 1#32).toNat) (mc', j + 1#32, ()) mi
                            (by omega) ⟨rfl, by omega, rfl, fun q hq => ?_⟩
                          rw [hj1_n] at hq
                          by_cases hqj : q = j.toNat
                          · subst hqj; rw [← congrArg BitVec.toNat hcl_get]; exact hcl_cov
                          · exact hcov_j q (by omega)
                        · intro Js hJs; fc_split_fast
                          · clear hc; fc_split_fast
                            · fc_steps
                              exact hB2 (false, mc, j, ()) mi ⟨rfl, fun h => by cases h⟩
                            · have hcl_in : cl.toNat ∈ unassLits := by
                                have hne0 : lm'[cl.toNat]?.getD 0#8 ≠ 0#8 := by
                                  intro h0
                                  have hidx : ((s.core.arena[((s.core.wstk[(p + 1).toNat]'
                                      hp1_w).setWidth 64 + 3 + j.setWidth 64).toNat]'
                                      hcr3j_w).setWidth 64).toNat = cl.toNat := by
                                    rw [hcl_eq, bv_zext32_toNat]
                                  change (BitVec.setWidth 32 (lm'[_]'_) == 0#32) = false at hc
                                  rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at h0
                                  rw [list_getElem_congr hidx _ (by omega), h0] at hc; cases hc
                                exact (hlm_inv cl.toNat (by omega)).resolve_left hne0
                              fc_steps; exact hJs (true, mc + 1#32, ()) mi ⟨rfl, Or.inr hcl_in⟩
                          · have hval_ff : s.core.vals[cl.toNat]?.getD 0#8 = 0xFF#8 := by
                              have hne0 : s.core.vals[cl.toNat]?.getD 0#8 ≠ 0#8 := by
                                intro h0
                                have hidx : ((s.core.arena[((s.core.wstk[(p + 1).toNat]'
                                    hp1_w).setWidth 64 + 3 + j.setWidth 64).toNat]'
                                    hcr3j_w).setWidth 64).toNat = cl.toNat := by
                                  rw [hcl_eq, bv_zext32_toNat]
                                change (BitVec.signExtend 32 (s.core.vals[_]'_) == 0#32) =
                                  false at hc
                                rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at h0
                                rw [list_getElem_congr hidx _ (by omega), h0] at hc; cases hc
                              rcases hw.vals_domain cl.toNat hcl_lt with hv | hv | hv
                              · exact absurd hv hne0
                              · exact absurd hv hne1_cl
                              · exact hv
                            fc_steps; exact hJs (true, mc, ()) mi ⟨rfl, Or.inl hval_ff⟩
                    · have hj_ge : sz_bv.toNat ≤ j.toNat := by
                        rw [list_getElem_congr hcr2_n hcr2_w hcr2_arr] at hc
                        simp only [BitVec.ult, decide_eq_false_iff_not] at hc
                        exact Nat.le_of_not_lt hc
                      have hj_eq : j.toNat = sz_bv.toNat := by omega
                      rw [hj_eq] at hcov_j; fc_steps
                      exact hB2 (true, mc, j, ()) mi ⟨rfl, fun _ => hcov_j⟩
                  · intro _ L2 _ hL2; fc_steps
                    exact hL2 (sz_bv.toNat - 0) (0#32, 0#32, ()) mi
                      ⟨rfl, Nat.zero_le _, rfl, fun _ h => by simp at h⟩
        · fc_steps; exact hB (false, p, ()) mi ⟨rfl, fun h => by cases h⟩
      · intro _ L _ hL; fc_steps
        refine hL ((off + wsz).toNat - off.toNat) (off, ()) mi ⟨rfl, by omega, rfl, ?_⟩
        simpa [hend_n, hoff_n, hwsz_n] using hslice0

end LeanQbe.T.Examples.Kissat.FullFidelityStep10

end
