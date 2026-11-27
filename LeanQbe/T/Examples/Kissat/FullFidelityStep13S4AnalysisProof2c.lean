/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S4Analysis
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S4AnalysisProof2b
public import LeanQbe.T.Examples.Kissat.FullM8CoreParityProofMin2
import LeanQbe.T.Examples.Kissat.FullMinLemmas3
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Fidelity Step 13 S4-B Proof 2c (`full_shrink_blk_bool_m8` Main Theorem)

UNSAT-only, callee-parametric `Func.wp` proof (`public section`, `0` `@[expose]` on theorems,
`0` `import all`, `XPost`-polymorphic) for Step-13 `fidStep13S4ShrinkBlkBoolM8Fn`
(`full_shrink_blk_bool_m8`, with `L6a` hoisted `u64 alen = h->arena_len;`) against
`FullM8CoreParity.m8ShrinkBlkBoolSpec`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S4

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full hiding
  FullMinMarkInv fullMinMarkCore fullMinMarkState fullMinMarkSpec
  fullMinLitSpec fullShrinkLowerSpec fullShrinkBlkSpec fullMinShrinkSpec
open LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open LeanQbe.T.Examples.Kissat.Full.FullMinSpecs
open LeanQbe.T.Examples.Kissat.FullM8CoreParity
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Full.FullMinTactics
open Kraken.Bedrock2.Test

private theorem is_wp_let {Γ rs Q X ts} {op : Op Val ts} {k : Tup Val ts → Expr Val Cont rs}
    {m : Mem 64} (h : wp Γ Q X (.let_ op k) m) : wp Γ Q X (.let_ op k) m := h
local macro "s13_lets" : tactic => `(tactic| repeat (apply is_wp_let; c0_hstep))
local macro "s13_ld" h:term : tactic =>
  `(tactic| (s13_lets; rw [LeanQbe.T.wp]; refine ⟨_, $h, ?_⟩))

private theorem s13_shrink_init_step {c : FullCfg} {F0 : CNF Nat} {F_cur0 : List (List Nat)}
    {s : FullState} {beg end_b max_tr k_bv slen_bv : Val i64} {keep0 : List Nat}
    {mrk1 : List (BitVec 8)} {sstk1 : List (BitVec 32)} {v : BitVec 32}
    (hcore : FullOtfsCoreInv c F0 s) (hw0 : FullOtfsWitnessInv c F0 F_cur0 s.core)
    (hbk1 : beg.toNat ≤ k_bv.toNat) (hult : k_bv.toNat < end_b.toNat)
    (hend_cv : end_b.toNat ≤ s.core.cur_vars) (hsl_eq : slen_bv.toNat = k_bv.toNat - beg.toNat)
    (hblk_lt : ∀ j, beg.toNat ≤ j → j < end_b.toNat →
      (s.core.tmp[j]?.getD 0#32).toNat / 2 < s.core.cur_vars)
    (hv_nat : v.toNat = (s.core.tmp[k_bv.toNat]?.getD 0#32).toNat / 2)
    (hv_lt' : v.toNat < s.core.cur_vars)
    (hb1 : S13ShrinkBaseInv c s mrk1 s.core.min_clr sstk1 s.scratch.wsort s.core.min_clr_len
      s.core.min_clr_full slen_bv.toNat keep0)
    (hblk_k : S13ShrinkBlk8 s mrk1 beg.toNat k_bv.toNat)
    (hsstk_k : S13ShrinkStk8 mrk1 sstk1 slen_bv.toNat)
    (h8_k : ∀ w < s.core.cur_vars, (mrk1[w]?.getD 0#8 &&& 8#8) ≠ 0#8 →
      ∃ j, beg.toNat ≤ j ∧ j < k_bv.toNat ∧ (s.core.tmp[j]?.getD 0#32).toNat / 2 = w)
    (hcnt_k : trailCount8 s.core.trl mrk1 (min (max_tr.toNat + 1) s.core.trail_end) ≤
      slen_bv.toNat) :
    let mrk2 := mrk1.set v.toNat (mrk1[v.toNat]?.getD 0#8 ||| 8#8)
    let sstk2 := sstk1.set slen_bv.toNat v
    S13ShrinkBaseInv c s mrk2 s.core.min_clr sstk2 s.scratch.wsort s.core.min_clr_len
      s.core.min_clr_full (slen_bv.toNat + 1) keep0 ∧
    S13ShrinkBlk8 s mrk2 beg.toNat (k_bv.toNat + 1) ∧
    S13ShrinkStk8 mrk2 sstk2 (slen_bv.toNat + 1) ∧
    (∀ w < s.core.cur_vars, (mrk2[w]?.getD 0#8 &&& 8#8) ≠ 0#8 →
      ∃ j, beg.toNat ≤ j ∧ j < k_bv.toNat + 1 ∧ (s.core.tmp[j]?.getD 0#32).toNat / 2 = w) ∧
    trailCount8 s.core.trl mrk2 (min (max_tr.toNat + 1) s.core.trail_end) ≤ slen_bv.toNat + 1 := by
  have hcv := hcore.1.core_ok.cur_vars_le
  have hmrk_len := hb1.mrk_len; have hsstk_len := hb1.sstk_len
  dsimp only
  have hmin2 := fullMinMarkInv_set_bit8
    (s13ShrinkBaseInv_core hcore hb1 (ticks := s.scratch.search_ticks)) hb1.min_inv hv_lt'
  change FullMinMarkInv (m8BlkState s s.core.tmp
    (mrk1.set v.toNat (mrk1[v.toNat]?.getD 0#8 ||| 8#8)) s.core.min_clr sstk1 s.scratch.wsort
    s.core.min_clr_len s.core.min_clr_full s.scratch.search_ticks).core keep0 at hmin2
  obtain ⟨hab2, hmono2, hmono8⟩ := s13Shrink_set_bit8_monos hcv hmrk_len hv_lt'
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨by simp [hmrk_len], hb1.mclr_len, hb1.mcl_le, by simp [hsstk_len],
      hb1.wsort_len, by omega, fun w hw => (hab2 w hw).trans (hb1.mrk_above w hw),
      ⟨hmin2.mrk_dom, hmin2.clr_cov, hmin2.rem_sound⟩,
      fun w hw h2 => hmono2 w hw (hb1.mono2 w hw h2), fun w hw h8w => ?_, fun j hj => ?_⟩
    · by_cases hwe : w = v.toNat
      · subst w; exact ⟨slen_bv.toNat, by omega, by
          rw [List.getElem?_set_self (by omega), Option.getD_some]⟩
      · rw [List.getElem?_set_ne (Ne.symm hwe)] at h8w
        obtain ⟨j, hj, hje⟩ := hb1.bit8_sstk w hw h8w
        exact ⟨j, by omega, by rwa [List.getElem?_set_ne (by omega)]⟩
    · by_cases hjs : j = slen_bv.toNat
      · subst j; rw [List.getElem?_set_self (by omega), Option.getD_some]; exact hv_lt'
      · rw [List.getElem?_set_ne (Ne.symm hjs)]; exact hb1.sstk_lt j (by omega)
  · intro j hj1 hj2; by_cases hjk : j = k_bv.toNat
    · subst j; rw [← hv_nat]
      rw [List.getElem?_set_self (by omega), Option.getD_some]; exact bv8_and8_of_or8 _
    · exact hmono8 _ (hblk_lt j hj1 (by omega)) (hblk_k j hj1 (by omega))
  · intro j hj; by_cases hjs : j = slen_bv.toNat
    · subst j; rw [List.getElem?_set_self (by omega), Option.getD_some]
      rw [List.getElem?_set_self (by omega), Option.getD_some]
      exact bv8_and8_of_or8 _
    · rw [List.getElem?_set_ne (Ne.symm hjs)]
      exact hmono8 _ (hb1.sstk_lt j (by omega)) (hsstk_k j (by omega))
  · intro w hw h8w; by_cases hwe : w = v.toNat
    · subst w; exact ⟨k_bv.toNat, hbk1, by omega, hv_nat.symm⟩
    · rw [List.getElem?_set_ne (Ne.symm hwe)] at h8w
      obtain ⟨j, hj1, hj2, hjv⟩ := h8_k w hw h8w; exact ⟨j, hj1, by omega, hjv⟩
  · have htl := trailCount8_set_bit8_le (trl := s.core.trl) (mrk := mrk1)
      (fun i j hi hj heq => hw0.trail_vars_nodup i j (by omega) (by omega) heq)
      v.toNat (min (max_tr.toNat + 1) s.core.trail_end) (Nat.min_le_right _ _)
    omega

private theorem s13_shrink_hin_cnt {c : FullCfg} {F0 : CNF Nat} {F_cur0 : List (List Nat)}
    {s : FullState} {mrk_c : List (BitVec 8)} {open_c t_c t_in : Val i64} {uip_in : Val i32}
    (hw0 : FullOtfsWitnessInv c F0 F_cur0 s.core)
    (hcnt_c : trailCount8 s.core.trl mrk_c (min (t_c.toNat + 1) s.core.trail_end) ≤ open_c.toNat)
    (ht_te : t_in.toNat < s.core.trail_end) (ht_tc : t_in.toNat ≤ t_c.toNat)
    (huip_eq : uip_in = s.core.trl[t_in.toNat]?.getD 0#32)
    (huip_8 : (mrk_c[uip_in.toNat / 2]?.getD 0#8 &&& 8#8) ≠ 0#8)
    (hgap : ∀ j, t_in.toNat < j → j < s.core.trail_end → j ≤ t_c.toNat →
      (mrk_c[(s.core.trl[j]?.getD 0#32).toNat / 2]?.getD 0#8 &&& 8#8) = 0#8) :
    (s.core.trl[t_in.toNat]?.getD 0#32).toNat = uip_in.toNat ∧
    uip_in.toNat < 2 * s.core.cur_vars ∧
    trailCount8 s.core.trl mrk_c t_in.toNat ≤ open_c.toNat - 1 := by
  have huip_eq' : (s.core.trl[t_in.toNat]?.getD 0#32).toNat = uip_in.toNat :=
    congrArg BitVec.toNat huip_eq.symm
  have htc_gap := trailCount8_eq_of_zero_range (trl := s.core.trl) (mrk := mrk_c)
    (by omega : t_in.toNat + 1 ≤ min (t_c.toNat + 1) s.core.trail_end)
    (fun j hj1 hj2 => hgap j (by omega) (by omega) (by omega))
  have htc_nz := trailCount8_step_nz (trl := s.core.trl) (mrk := mrk_c)
    (n := t_in.toNat) (by rwa [huip_eq'])
  exact ⟨huip_eq', by rw [← huip_eq']; exact hw0.trail_lits_lt _ ht_te, by omega⟩

private theorem s13_shrink_blk_bool_specs_wp (Γ : Env)
    (hSl : ∀ args m Q X, m8ShrinkLowerSpec args m Q X →
      Γ "full_shrink_lower_m8" [i64, i32, i32] [.bool] args m Q X)
    (hMm : ∀ args m Q X, fullMinMarkSpec args m Q X →
      Γ "full_min_mark" [i64, i32, i8] [] args m Q X)
    {c : FullCfg} {F0 : CNF Nat} {s : FullState} {beg end_b max_tr : Val i64} {blvl : Val i32}
    {keepLen : Nat} {R : Mem 64 → Prop} {Q : Post [.bool]} {X : XPost}
    (hcore : FullOtfsCoreInv c F0 s)
    (hmin0 : FullMinMarkInv s.core
      (((s.core.tmp.take keepLen).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat))
    (hno8_0 : ∀ v < s.core.cur_vars, (s.core.mrk[v]?.getD 0#8 &&& 8#8) = 0#8)
    (hbeg1 : 1 ≤ beg.toNat) (hbeg_end : beg.toNat < end_b.toNat) (hend_kl : end_b.toNat ≤ keepLen)
    (hkl_cv : keepLen ≤ s.core.cur_vars) (_hblvl_pos : 0 < blvl.toNat)
    (hblvl_lt : blvl.toNat < s.core.cur_level)
    (hblk_spec : ∀ k, beg.toNat ≤ k → k < end_b.toNat →
      let l := (s.core.tmp[k]?.getD 0#32).toNat
      l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
      (s.core.lvl[l / 2]?.getD 0#32).toNat = blvl.toNat ∧
      (s.core.trail_pos[l / 2]?.getD 0#32).toNat ≤ max_tr.toNat)
    (hkeep_spec : ∀ k < keepLen, s.core.tmp[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
      let l := (s.core.tmp[k]?.getD 0#32).toNat
      l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
      (s.core.mrk[l / 2]?.getD 0#8 &&& 2#8) ≠ 0#8)
    {m : Mem 64} (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ (ok : Bool) tmp' mrk' mclr' sstk' wsort' mcl' mcf' ticks' m',
      let s' := m8BlkState s tmp' mrk' mclr' sstk' wsort' mcl' mcf' ticks'
      FullOtfsCoreInv c F0 s' →
      FullMinMarkInv s'.core
        (((tmp'.take keepLen).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat) →
      (∀ v, s.core.cur_vars ≤ v → mrk'[v]? = s.core.mrk[v]?) →
      (∀ v < s.core.cur_vars, (mrk'[v]?.getD 0#8 &&& 8#8) = 0#8) →
      (∀ v < s.core.cur_vars,
        (s.core.mrk[v]?.getD 0#8 &&& 2#8) ≠ 0#8 → (mrk'[v]?.getD 0#8 &&& 2#8) ≠ 0#8) →
      (ok = false → tmp' = s.core.tmp) →
      (∀ k < keepLen, (k < beg.toNat ∨ end_b.toNat ≤ k) → tmp'[k]? = s.core.tmp[k]?) →
      (∀ k, beg.toNat ≤ k → k < end_b.toNat → tmp'[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
        (s.core.lvl[(tmp'[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = blvl.toNat) →
      ((((s.core.tmp.take keepLen).filter (· ≠ 0xFFFFFFFF#32)).map
          fun x => x.toNat / 2).Nodup →
        (∀ k < keepLen, (k < beg.toNat ∨ end_b.toNat ≤ k) →
          s.core.tmp[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
          (s.core.lvl[(s.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≠ blvl.toNat) →
        (((tmp'.take keepLen).filter (· ≠ 0xFFFFFFFF#32)).map
          fun x => x.toNat / 2).Nodup) →
      (∀ F_cur, FullOtfsWitnessInv c F0 F_cur s.core →
        (cnfOfClauses F_cur).EntailsClause (cnfClause
          (((s.core.tmp.take keepLen).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat)) →
        FullOtfsWitnessInv c F0 F_cur s'.core ∧
        (cnfOfClauses F_cur).EntailsClause (cnfClause
          (((tmp'.take keepLen).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat))) →
      (∀ k < keepLen, tmp'[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
        let l := (tmp'[k]?.getD 0#32).toNat
        l < 2 * s.core.cur_vars ∧ s'.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
        (mrk'[l / 2]?.getD 0#8 &&& 2#8) ≠ 0#8) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    Func.wp Γ fidStep13S4ShrinkBlkBoolM8Fn.body (c.hdr, beg, end_b, blvl, max_tr, ()) m Q X := by
  unfold Func.wp fidStep13S4ShrinkBlkBoolM8Fn full_shrink_blk_bool_m8_body
  dsimp only; c0_hstraight
  obtain ⟨_, hw0⟩ := hcore.2
  have hlen0 := hcore.1.core_ok; have hcv := hlen0.cur_vars_le
  have hmx := c.hmaxv; have har := c.harena; unfold dimacsBound at hmx har
  let keep0 := ((s.core.tmp.take keepLen).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat
  have hblk_lt : ∀ j, beg.toNat ≤ j → j < end_b.toNat →
      (s.core.tmp[j]?.getD 0#32).toNat / 2 < s.core.cur_vars := fun j hj1 hj2 => by
    have := (hblk_spec j hj1 hj2).1; omega
  have h0v : (0#64 : BitVec 64).toNat = 0 := rfl
  refine wp_loop_group (ts := [i64, i64]) (fun n (slen_bv, k_bv, ()) m1 =>
      ∃ (mrk1 : List (BitVec 8)) (sstk1 : List (BitVec 32)),
        n = end_b.toNat - k_bv.toNat ∧ beg.toNat ≤ k_bv.toNat ∧ k_bv.toNat ≤ end_b.toNat ∧
        slen_bv.toNat = k_bv.toNat - beg.toNat ∧
        S13ShrinkBaseInv c s mrk1 s.core.min_clr sstk1 s.scratch.wsort s.core.min_clr_len
          s.core.min_clr_full slen_bv.toNat keep0 ∧
        S13ShrinkBlk8 s mrk1 beg.toNat k_bv.toNat ∧ S13ShrinkStk8 mrk1 sstk1 slen_bv.toNat ∧
        (∀ w < s.core.cur_vars, (mrk1[w]?.getD 0#8 &&& 8#8) ≠ 0#8 →
          ∃ j, beg.toNat ≤ j ∧ j < k_bv.toNat ∧ (s.core.tmp[j]?.getD 0#32).toNat / 2 = w) ∧
        trailCount8 s.core.trl mrk1 (min (max_tr.toNat + 1) s.core.trail_end) ≤ slen_bv.toNat ∧
        (FullMem c (m8BlkState s s.core.tmp mrk1 s.core.min_clr sstk1 s.scratch.wsort
          s.core.min_clr_len s.core.min_clr_full s.scratch.search_ticks) ⋆ R) m1)
    ?_ (fun J1 hJ1 => by
      s13_lets
      have htc0 := trailCount8_zero_of_all_zero (trl := s.core.trl) (mrk := s.core.mrk)
        (lim := s.core.trail_end) (fun i hi => by have := hw0.trail_lits_lt i hi; omega) hno8_0
        (min (max_tr.toNat + 1) s.core.trail_end) (Nat.min_le_right _ _)
      exact hJ1 (end_b.toNat - beg.toNat) (0#64, beg, ()) m
        ⟨s.core.mrk, s.scratch.shrink_stk, rfl, le_refl _, le_of_lt hbeg_end,
          by simp only [h0v]; omega,
          ⟨hlen0.mrk_len, hlen0.min_clr_len_arr, hlen0.min_clr_len_le,
            hcore.1.scratch_ok.shrink_stk_len, hcore.1.scratch_ok.wsort_len,
            by simp only [h0v]; omega, fun _ _ => rfl, hmin0, fun _ _ h => h,
            fun w hw h8 => absurd (hno8_0 w hw) h8, fun _ h => by simp only [h0v] at h; omega⟩,
          fun _ h1 h2 => by omega, fun _ h => by simp only [h0v] at h; omega,
          fun w hw h8 => absurd (hno8_0 w hw) h8, by simp only [h0v]; exact le_of_eq htc0, hm⟩)
  rintro J1 n ⟨slen_bv, k_bv, ⟨⟩⟩ m1 hJ1
    ⟨mrk1, sstk1, rfl, hbk1, hke1, hsl_eq, hb1, hblk_k, hsstk_k, h8_k, hcnt_k, hm1⟩
  rw [Blocks.get_here]; s13_lets; ml_jnz; refine ⟨fun hult => ?_, ?_⟩
  · c0_cond hult
    let st1 := m8BlkState s s.core.tmp mrk1 s.core.min_clr sstk1 s.scratch.wsort
      s.core.min_clr_len s.core.min_clr_full s.scratch.search_ticks
    have hmrk_len := hb1.mrk_len; have hsstk_len := hb1.sstk_len
    have hk_tmp : k_bv.toNat < s.core.tmp.length := by rw [hlen0.tmp_len_arr]; omega
    have hv_lt := hblk_lt k_bv.toNat hbk1 hult
    s13_ld c0_load_full_tmp (s := st1) (i := k_bv)
      (by dsimp only [st1, m8BlkState, m8ShrinkBlkBoolState]; rw [hlen0.tmp_len_arr]; omega) hm1
    let lit := s.core.tmp[k_bv.toNat]'hk_tmp; let v := lit >>> 1
    have hv_nat : v.toNat = (s.core.tmp[k_bv.toNat]?.getD 0#32).toNat / 2 := by
      dsimp only [v, lit]; rw [List.getElem?_eq_getElem hk_tmp, Option.getD_some, bv32_lshr_1]
    have hv_lt' : v.toNat < s.core.cur_vars := by rw [hv_nat]; exact hv_lt
    have hv64 : (v.setWidth 64).toNat = v.toNat := bv_c0_zext32_64 v
    s13_ld c0_load_full_mrk (s := st1) (i := v.setWidth 64)
      (by dsimp only [st1, m8BlkState, m8ShrinkBlkBoolState]; rw [hmrk_len, hv64]; omega) hm1
    s13_lets; rw [wp]
    have hv_mrk_st1 : (v.setWidth 64).toNat < st1.core.mrk.length := by
      dsimp only [st1, m8BlkState, m8ShrinkBlkBoolState]; rw [hmrk_len, hv64]; omega
    let v_or : BitVec 8 := BitVec.setWidth 8
      (BitVec.setWidth 32 (st1.core.mrk[(v.setWidth 64).toNat]'hv_mrk_st1) ||| BitVec.ofNat 32 8)
    obtain ⟨hst1, hm_s⟩ := c0_store_full_mrk (s := st1) (i := v.setWidth 64) v_or hv_mrk_st1 hm1
    refine ⟨hst1, ?_⟩
    let mrk2 := mrk1.set v.toNat (mrk1[v.toNat]?.getD 0#8 ||| 8#8)
    have hm_mrk1 : (s.core.tmp[k_bv.toNat]'hk_tmp).toNat / 2 < mrk1.length := by
      have : v.toNat < mrk1.length := by rw [hmrk_len]; omega
      dsimp only [v, lit] at this; rwa [bv32_lshr_1] at this
    have hor8 : ∀ b : BitVec 8,
        BitVec.setWidth 8 (BitVec.setWidth 32 b ||| BitVec.ofNat 32 8) = b ||| 8#8 := by decide
    have hm_s1' : (FullMem c (m8BlkState s s.core.tmp mrk2 s.core.min_clr sstk1
        s.scratch.wsort s.core.min_clr_len s.core.min_clr_full s.scratch.search_ticks) ⋆ R)
        (storeMem m1 i8 (c.pMark + v.setWidth 64) v_or) := by
      dsimp only [st1, m8BlkState, m8ShrinkBlkBoolState, mrk2, v_or, v, lit] at hm_s ⊢
      simp only [bv_c0_zext32_64, bv32_lshr_1, hor8] at hm_s ⊢
      rw [List.getElem?_eq_getElem hm_mrk1, Option.getD_some]; exact hm_s
    s13_lets; rw [wp]
    obtain ⟨hst2, hm_s2⟩ := c0_store_full_shrink_stk (s := m8BlkState s s.core.tmp mrk2
        s.core.min_clr sstk1 s.scratch.wsort s.core.min_clr_len s.core.min_clr_full
        s.scratch.search_ticks) (i := slen_bv) v
      (by dsimp only [m8BlkState, m8ShrinkBlkBoolState]; rw [hsstk_len]; omega) hm_s1'
    refine ⟨hst2, ?_⟩
    s13_lets; let sstk2 := sstk1.set slen_bv.toNat v
    obtain ⟨hb2, hblk2, hsstk2, h8_2, hcnt2⟩ := s13_shrink_init_step hcore hw0 hbk1 hult
      (Nat.le_trans hend_kl hkl_cv) hsl_eq hblk_lt hv_nat hv_lt' hb1 hblk_k hsstk_k h8_k hcnt_k
    have hsl1 : (slen_bv + 1).toNat = slen_bv.toNat + 1 := min_bv64_add1 (by omega)
    have hk1 : (k_bv + 1).toNat = k_bv.toNat + 1 := min_bv64_add1 (by omega)
    exact hJ1 (end_b.toNat - (k_bv + 1).toNat) (slen_bv + 1, k_bv + 1, ()) _ (by omega)
      ⟨mrk2, sstk2, rfl, by omega, by omega, by rw [hsl1, hk1]; omega, by rw [hsl1]; exact hb2,
        by rw [hk1]; exact hblk2, by rw [hsl1]; exact hsstk2, by rw [hk1]; exact h8_2,
        by rw [hsl1]; exact hcnt2,
        by dsimp only [m8BlkState, m8ShrinkBlkBoolState, sstk2] at hm_s2 ⊢; exact hm_s2⟩
  intro hdone; c0_cond hdone
  have hk_end : k_bv = end_b := BitVec.eq_of_toNat_eq (by omega); subst k_bv
  refine wp_join_group (ts := [i64, i64, .bool, i32, i64])
    (S13ShrinkAfterInv c s blvl beg.toNat end_b.toNat keep0 R)
    (fun _ xs m_a ha => by
      rw [Blocks.get_here]
      exact s13_shrink_blk_bool_after_wp hMm hcore hbeg_end hend_kl hkl_cv
        (fun k hk1 hk2 => (hblk_spec k hk1 hk2).2.2.1) hkeep_spec hQ ha) ?_
  rintro J_am hJ_am
  refine wp_loop_group (ts := [i64, i64, .bool, i32, i64])
    (S13ShrinkMainInv c s blvl beg.toNat end_b.toNat keep0 R) ?_ (fun Jm hJm => by
      s13_lets
      have hsub : (end_b - beg).toNat = end_b.toNat - beg.toNat := min_bv64_sub (le_of_lt hbeg_end)
      refine hJm (if (false : Bool) = true then 0 else min max_tr.toNat s.core.trail_end + 1)
        (end_b - beg, slen_bv, false, 0xFFFFFFFF#32, max_tr, ()) m1
        ⟨mrk1, s.core.min_clr, sstk1, s.scratch.wsort, s.core.min_clr_len,
          s.core.min_clr_full, s.scratch.search_ticks, rfl, hb1, hblk_k, hsstk_k, hm1, fun _ =>
            ⟨by omega, by omega, fun w hw h8 => ?_, by omega⟩⟩
      obtain ⟨j, hj1, hj2, hjv⟩ := h8_k w hw h8
      obtain ⟨hl_lt, hval_j, hlvl_j, htp_j⟩ := hblk_spec j hj1 hj2
      obtain ⟨idx, hidx_te, hidx_eq⟩ := (hw0.vals_false_iff _ hl_lt).mp hval_j
      have hv_idx : (s.core.trl[idx]?.getD 0#32).toNat / 2 = w := by
        rw [hidx_eq, ← hjv]; exact litVar_litNeg _
      have htp_eq : (s.core.trail_pos[w]?.getD 0#32).toNat = idx := by
        rw [← hv_idx]; exact hw0.trail_pos_inv idx hidx_te
      refine ⟨by rw [← hjv]; exact hlvl_j, idx, hidx_te, hv_idx, Or.inl ?_⟩
      rw [hjv] at htp_j; omega)
  rintro Jm n ⟨open_c, slen_c, failed_c, uip_c, t_c, ⟨⟩⟩ m_c hJm
    ⟨mrk_c, mclr_c, sstk_c, wsort_c, mcl_c, mcf_c, ticks_c, rfl, hb_c, hblk_c, hsstk_c, hm_c, hok⟩
  clear hQ hmin0 hno8_0 hkeep_spec hblk_spec hm max_tr m hJ1 hb1 hsstk_k hcnt_k hm1
  clear hbk1 hke1 hsl_eq hblk_k h8_k hdone J1 slen_bv m1 mrk1 sstk1
  rw [Blocks.get_here]; s13_lets; ml_jnz; refine ⟨fun hfail => ?_, ?_⟩
  · s13_lets; exact hJ_am _ _ ⟨mrk_c, mclr_c, sstk_c, wsort_c, mcl_c, mcf_c, ticks_c,
      hb_c, hsstk_c, hm_c, fun h => by cases hfail.symm.trans h⟩
  intro hnfail; obtain ⟨hop_pos, hop_le, h8_c, hcnt_c⟩ := hok hnfail
  let st_c := m8BlkState s s.core.tmp mrk_c mclr_c sstk_c wsort_c mcl_c mcf_c ticks_c
  let InnerOutInv : Tup Val [.bool, i32, i64] → Mem 64 → Prop :=
    fun (failed_in, uip_in, t_in, ()) m_in =>
      m_in = m_c ∧ (failed_in = false →
        t_in.toNat < s.core.trail_end ∧ t_in.toNat ≤ t_c.toNat ∧
        uip_in = s.core.trl[t_in.toNat]?.getD 0#32 ∧
        (mrk_c[uip_in.toNat / 2]?.getD 0#8 &&& 8#8) ≠ 0#8 ∧
        ∀ j, t_in.toNat < j → j < s.core.trail_end → j ≤ t_c.toNat →
          (mrk_c[(s.core.trl[j]?.getD 0#32).toNat / 2]?.getD 0#8 &&& 8#8) = 0#8)
  refine wp_join_group (ts := [.bool, i32, i64]) InnerOutInv ?_ (fun J_in hJ_in => by
    refine wp_loop_group (ts := [i64]) (fun n_in (t_cur, ()) m_l =>
        m_l = m_c ∧ n_in = t_cur.toNat + 1 ∧ t_cur.toNat ≤ t_c.toNat ∧
        ∀ j, t_cur.toNat < j → j < s.core.trail_end → j ≤ t_c.toNat →
          (mrk_c[(s.core.trl[j]?.getD 0#32).toNat / 2]?.getD 0#8 &&& 8#8) = 0#8)
      ?_ (fun J_l hJ_l => by
        s13_lets; exact hJ_l (t_c.toNat + 1) (t_c, ()) m_c
          ⟨rfl, rfl, le_refl _, fun _ h1 _ h3 => by omega⟩)
    rintro J_l n_in ⟨t_cur, ⟨⟩⟩ m_l hJ_l ⟨hm_l_eq, rfl, htc_le, hgap⟩
    subst m_l; rw [Blocks.get_here, wp]; refine ⟨fun _ => ?_, fun hc => by cases hc⟩
    s13_ld load_full_trail_end (s := st_c) hm_c; s13_lets; ml_jnz
    refine ⟨fun _ => hJ_in (true, uip_c, t_cur, ()) m_c ⟨rfl, fun h => by cases h⟩, ?_⟩
    intro hlt_te; c0_cond hlt_te
    have ht_te : t_cur.toNat < s.core.trail_end := by
      dsimp only [st_c, m8BlkState, m8ShrinkBlkBoolState] at hlt_te; bv_omega
    have ht_trl : t_cur.toNat < st_c.core.trl.length := by
      dsimp only [st_c, m8BlkState, m8ShrinkBlkBoolState]
      rw [hlen0.trl_len]; have := hlen0.trail_end_le; omega
    s13_ld c0_load_full_trl (s := st_c) (i := t_cur) ht_trl hm_c
    let lit := st_c.core.trl[t_cur.toNat]'ht_trl
    have hlit_lt : lit.toNat < 2 * s.core.cur_vars := by
      have := hw0.trail_lits_lt t_cur.toNat ht_te
      rwa [List.getElem?_eq_getElem ht_trl, Option.getD_some] at this
    have hlv_mrk : ((lit >>> 1).setWidth 64).toNat < st_c.core.mrk.length := by
      dsimp only [st_c, m8BlkState, m8ShrinkBlkBoolState]
      rw [hb_c.mrk_len, bv_c0_zext32_64, bv32_lshr_1]; omega
    s13_ld c0_load_full_mrk (s := st_c) (i := (lit >>> 1).setWidth 64) hlv_mrk hm_c
    s13_lets; ml_jnz; refine ⟨fun hhit => ?_, fun hmiss => ?_⟩
    · have h8_hit : (mrk_c[lit.toNat / 2]?.getD 0#8 &&& 8#8) ≠ 0#8 := by
        have h8b : ∀ b : BitVec 8,
            (BitVec.setWidth 32 b &&& BitVec.ofNat 32 8 != BitVec.ofNat 32 0) = true →
            (b &&& 8#8) ≠ 0#8 := by decide
        have h8 := h8b _ (by exact hhit)
        rw [List.getElem?_eq_getElem (by rw [hb_c.mrk_len]; omega), Option.getD_some]
        exact (by simpa only [st_c, m8BlkState, m8ShrinkBlkBoolState, bv_c0_zext32_64,
          bv32_lshr_1] using h8)
      exact hJ_in (failed_c, lit, t_cur, ()) m_c ⟨rfl, fun _ =>
        ⟨ht_te, htc_le, by rw [List.getElem?_eq_getElem ht_trl, Option.getD_some], h8_hit, hgap⟩⟩
    · have h8_miss : (mrk_c[(s.core.trl[t_cur.toNat]?.getD 0#32).toNat / 2]?.getD 0#8 &&& 8#8) =
          0#8 := by
        have h8b0 : ∀ b : BitVec 8,
            (BitVec.setWidth 32 b &&& BitVec.ofNat 32 8 != BitVec.ofNat 32 0) = false →
            (b &&& 8#8) = 0#8 := by decide
        have h8 := h8b0 _ (by exact hmiss)
        have hlt_tr : (s.core.trl[t_cur.toNat]'ht_trl).toNat = lit.toNat := rfl
        rw [List.getElem?_eq_getElem ht_trl, Option.getD_some, hlt_tr,
          List.getElem?_eq_getElem (by rw [hb_c.mrk_len]; omega), Option.getD_some]
        exact (by simpa only [st_c, m8BlkState, m8ShrinkBlkBoolState, bv_c0_zext32_64,
          bv32_lshr_1] using h8)
      s13_lets; ml_jnz
      refine ⟨fun _ => hJ_in (true, uip_c, t_cur, ()) m_c ⟨rfl, fun h => by cases h⟩, ?_⟩
      intro ht_ne0; c0_cond ht_ne0
      have ht_pos : 1 ≤ t_cur.toNat := bv64_pos_of_ne0 ht_ne0
      have htm1 : (t_cur - 1).toNat = t_cur.toNat - 1 := min_bv64_sub1 ht_pos
      s13_lets
      refine hJ_l ((t_cur - 1).toNat + 1) (t_cur - 1, ()) m_c (by omega)
        ⟨rfl, rfl, by omega, fun j hj1 hj2 hj3 => ?_⟩
      by_cases hje : j = t_cur.toNat
      · subst j; exact h8_miss
      · exact hgap j (by omega) hj2 hj3)
  rintro J_in ⟨failed_in, uip_in, t_in, ⟨⟩⟩ m_in ⟨hm_in_eq, hin⟩
  subst m_in; rw [Blocks.get_here]
  refine wp_join_group (ts := []) (fun () m_e => m_e = m_c) ?_ ?_
  · rintro J_ex ⟨⟩ m_e hm_e_eq; subst m_e; rw [Blocks.get_here]
    refine wp_join_group (ts := [.bool])
      (fun (f_out, ()) m_f => m_f = m_c ∧ (f_out = false → failed_in = false ∧ open_c = 1#64)) ?_
      (fun J_ef hJ_ef => by
        s13_lets; ml_jnz
        refine ⟨fun _ => hJ_ef (true, ()) m_c ⟨rfl, fun h => by cases h⟩, fun hop1 => ?_⟩
        c0_cond hop1; exact hJ_ef (failed_in, ()) m_c ⟨rfl, fun hf => ⟨hf, hop1⟩⟩)
    rintro J_ef ⟨f_out, ⟨⟩⟩ m_f ⟨hm_f_eq, hf_out⟩
    subst m_f; rw [Blocks.get_here]; s13_lets; apply hJ_am
    refine ⟨mrk_c, mclr_c, sstk_c, wsort_c, mcl_c, mcf_c, ticks_c,
      hb_c, hsstk_c, hm_c, fun hf_f _ => ?_⟩
    obtain ⟨hnfi, hop1⟩ := hf_out hf_f
    obtain ⟨ht_te, ht_tc, huip_eq, huip_in_8, hzero_gap⟩ := hin hnfi
    obtain ⟨huip_in_eq', huip_in_lt, hcnt_in⟩ :=
      s13_shrink_hin_cnt hw0 hcnt_c ht_te ht_tc huip_eq huip_in_8 hzero_gap
    have hop1' : open_c.toNat = 1 := by rw [hop1]; rfl
    have hcnt0 : trailCount8 s.core.trl mrk_c t_in.toNat = 0 := by omega
    refine ⟨t_in.toNat, ht_te, huip_in_eq', huip_in_8, (h8_c _ (by omega) huip_in_8).1, hblk_c,
      fun w hw hw8 => ?_⟩
    obtain ⟨_, idx, hidx_te, hidx_v, hdisj⟩ := h8_c w hw hw8
    by_cases heq : idx = t_in.toNat
    · subst heq; left; rw [← hidx_v, huip_in_eq']; rfl
    · by_cases hlt : idx < t_in.toNat
      · exfalso; have hz := trailCount8_eq_zero_mem hcnt0 hlt; rw [hidx_v] at hz; exact hw8 hz
      · rcases hdisj with htc | hres
        · exfalso; have hz := hzero_gap idx (by omega) hidx_te htc; rw [hidx_v] at hz; exact hw8 hz
        · exact Or.inr ⟨idx, hidx_te, by omega, hidx_v, hres⟩
  rintro J_ex hJ_ex
  ml_jnz; refine ⟨fun _ => hJ_ex () m_c rfl, ?_⟩; intro hnfi
  s13_lets; ml_jnz; refine ⟨fun _ => hJ_ex () m_c rfl, ?_⟩; intro hop_ne1
  s13_lets; ml_jnz; refine ⟨fun _ => hJ_ex () m_c rfl, ?_⟩; intro ht_ne0
  dsimp only at hnfi
  obtain ⟨ht_te, ht_tc, huip_eq, huip_in_8, hzero_gap⟩ := hin hnfi
  obtain ⟨huip_in_eq', huip_in_lt, hcnt_in⟩ :=
    s13_shrink_hin_cnt hw0 hcnt_c ht_te ht_tc huip_eq huip_in_8 hzero_gap
  clear hin; subst failed_in
  have hop_ge2 : 2 ≤ open_c.toNat := by
    by_cases h1 : open_c = 1#64; · simp [h1] at hop_ne1
    have hne : open_c.toNat ≠ 1 := fun h => h1 (BitVec.eq_of_toNat_eq (by rw [h]; rfl)); omega
  c0_cond ht_ne0; have ht_pos : 1 ≤ t_in.toNat := bv64_pos_of_ne0 ht_ne0
  let t_next := t_in - 1; have ht_next : t_next.toNat = t_in.toNat - 1 := min_bv64_sub1 ht_pos
  have hcnt_pre : trailCount8 s.core.trl mrk_c (min (t_next.toNat + 1) s.core.trail_end) ≤
      open_c.toNat - 1 := by
    rwa [show min (t_next.toNat + 1) s.core.trail_end = t_in.toNat by omega]
  have h8_pre : S13ShrinkAll8 s blvl mrk_c t_next.toNat t_in.toNat := by
    intro w hw hw8; obtain ⟨hl, idx, hidx_te, hidx_v, hdisj⟩ := h8_c w hw hw8
    refine ⟨hl, idx, hidx_te, hidx_v, ?_⟩
    rcases hdisj with hle | hres
    · by_cases heq : idx = t_in.toNat; · exact Or.inr (Or.inr heq)
      by_cases hlt : idx < t_in.toNat; · exact Or.inl (by omega)
      exfalso; have hz := hzero_gap idx (by omega) hidx_te hle; rw [hidx_v] at hz; exact hw8 hz
    · exact Or.inr (Or.inl hres)
  have huip_v_rsn : ((uip_in >>> 1).setWidth 64).toNat < st_c.core.rsns.length := by
    dsimp only [st_c, m8BlkState, m8ShrinkBlkBoolState]
    rw [hlen0.rsns_len, bv_c0_zext32_64, bv32_lshr_1]; omega
  s13_ld c0_load_full_rsns (s := st_c) (i := (uip_in >>> 1).setWidth 64) huip_v_rsn hm_c
  let rsn := st_c.core.rsns[(uip_in >>> 1).setWidth 64 |>.toNat]'huip_v_rsn
  have hrs_idx : ((uip_in >>> 1).setWidth 64).toNat =
      (s.core.trl[t_in.toNat]?.getD 0#32).toNat / 2 := by
    rw [bv_c0_zext32_64, bv32_lshr_1, huip_in_eq']
  have hrsn_eq : rsn = s.core.rsns[(s.core.trl[t_in.toNat]?.getD 0#32).toNat / 2]?.getD
      0xFFFFFFFF#32 := by
    dsimp only [rsn, st_c, m8BlkState, m8ShrinkBlkBoolState]
    rw [List.getElem?_eq_getElem (by rw [hlen0.rsns_len]; omega), Option.getD_some]; congr 1
  s13_lets; ml_jnz; refine ⟨fun _ => ?_, ?_⟩
  · s13_lets; exact hJ_am _ _ ⟨mrk_c, mclr_c, sstk_c, wsort_c, mcl_c, mcf_c, ticks_c,
      hb_c, hsstk_c, hm_c, fun h => by cases h⟩
  intro hrsn_ne; c0_cond hrsn_ne; s13_lets
  have hrsn_ne' : s.core.rsns[(s.core.trl[t_in.toNat]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 ≠
      0xFFFFFFFF#32 := by
    rw [getElem?_getD_of_getElem 0xFFFFFFFF#32 (rfl : s.core.rsns = st_c.core.rsns)
      (congrArg (· / 2) huip_in_eq')]; exact hrsn_ne
  have ht_in_lvl : (s.core.lvl[(s.core.trl[t_in.toNat]?.getD 0#32).toNat / 2]?.getD 0#32).toNat <
      s.core.cur_level := by
    rw [huip_in_eq', (h8_c _ (by omega) huip_in_8).1]; exact hblvl_lt
  have hrs := hw0.reason_inv_below t_in.toNat ht_te ht_in_lvl hrsn_ne'
  let is_bin_b := (rsn &&& 0x80000000#32 != 0#32)
  let CszJoin : Tup Val [.bool, i32] → Mem 64 → Prop := fun (f_sz, csz_bv, ()) m_sz =>
    ∃ ticks_sz : BitVec 64,
      f_sz = false ∧
      csz_bv.toNat = (if is_bin_b = true then 1 else fullArenaClauseSizeCore s.core rsn.toNat) ∧
      (is_bin_b = false → rsn.toNat ∈ fullArenaClauseRefsCore s.core ∧
        fullArenaClauseGarbCore s.core rsn.toNat = false ∧
        rsn.toNat + 3 + csz_bv.toNat ≤ s.core.arena.length) ∧
      (FullMem c (m8BlkState s s.core.tmp mrk_c mclr_c sstk_c wsort_c mcl_c mcf_c ticks_sz) ⋆
        R) m_sz
  refine wp_join_group (ts := [.bool, i32]) CszJoin ?_ (fun J_sz hJ_sz => by
    ml_jnz; refine ⟨fun hbt => ?_, ?_⟩
    · change is_bin_b = true at hbt
      exact hJ_sz (false, 1#32, ()) m_c
        ⟨ticks_c, rfl, by simp only [hbt, ↓reduceIte]; rfl,
          (fun h => absurd (hbt.symm.trans h) (by decide)), hm_c⟩
    intro hbf; change is_bin_b = false at hbf
    have hbin_f : ¬ (rsn &&& 0x80000000#32) ≠ 0#32 := by
      dsimp only [is_bin_b] at hbf; intro h; simp [h] at hbf
    rw [← hrsn_eq] at hrs; simp only [eq_false hbin_f, ↓reduceIte] at hrs
    have hwf := hw0.arena.refs_wf _ hrs.1
    s13_lets; ml_jnz
    refine ⟨fun har1 => by
      exfalso; have := bv64_lt_zext32_add3 (by have := hlen0.arena_len_le; omega) rsn har1
      have := hwf.1; omega, fun _ => ?_⟩
    have har2 : (rsn.setWidth 64 + 2).toNat < st_c.core.arena.length := by
      dsimp only [st_c, m8BlkState, m8ShrinkBlkBoolState]; rw [bv64_zext32_add2]
      have := hwf.1; have := hlen0.arena_len_le; have := hlen0.arena_len_arr; omega
    s13_ld c0_load_full_arena (s := st_c) (i := rsn.setWidth 64 + 2) har2 hm_c
    let csz := st_c.core.arena[(rsn.setWidth 64 + 2).toNat]'har2
    have hcsz_e : csz.toNat = fullArenaClauseSizeCore s.core rsn.toNat := by
      have hopt : st_c.core.arena[(rsn.setWidth 64 + 2).toNat]? = s.core.arena[rsn.toNat + 2]? := by
        dsimp only [st_c, m8BlkState, m8ShrinkBlkBoolState]; rw [bv64_zext32_add2]
      rw [List.getElem?_eq_getElem har2] at hopt
      exact congrArg (fun o => (o.getD 0#32).toNat) hopt
    s13_lets; ml_jnz; refine ⟨fun hsz3 => by
      exfalso; rw [BitVec.ult, decide_eq_true_eq] at hsz3
      have h3 : (3 : BitVec 32).toNat = 3 := rfl
      rw [h3, hcsz_e] at hsz3; have := hwf.2.1; omega, fun _ => ?_⟩
    s13_lets; ml_jnz
    refine ⟨fun har_oob => by
      exfalso
      have h1 := bv64_lt_zext32_add3_add (by have := hlen0.arena_len_le; omega) rsn csz har_oob
      have := hwf.2.2.1; have := hwf.2.2.2.1; rw [hcsz_e] at h1; omega, fun _ => ?_⟩
    s13_ld load_full_search_ticks (s := st_c) hm_c
    s13_lets; rw [wp]
    obtain ⟨hst_tk, hm_tk⟩ := store_full_search_ticks (s := st_c) (ticks_c + 1#64) hm_c
    refine ⟨hst_tk, ?_⟩
    exact hJ_sz (false, csz, ()) _ ⟨ticks_c + 1#64, rfl,
      by simp only [hbf, Bool.false_eq_true, ↓reduceIte]; exact hcsz_e,
      fun _ => ⟨hrs.1, hrs.2.1, by
        rw [hcsz_e]; have := hwf.2.2.1; have := hwf.2.2.2.1
        have := hlen0.arena_len_le; have := hlen0.arena_len_arr; omega⟩, hm_tk⟩)
  rintro J_sz ⟨f_sz, csz_bv, ⟨⟩⟩ m_sz ⟨ticks_sz, hf_sz, hcsz_eq, hbig_ok, hm_sz⟩
  rw [Blocks.get_here]
  exact s13_shrink_blk_cl_wp hSl hcore hw0 hblvl_lt (Nat.le_trans hend_kl hkl_cv) hblk_lt ht_te
    ht_tc ht_pos ht_next huip_in_eq' ht_in_lvl hrsn_eq hrsn_ne' rfl hf_sz hcsz_eq hbig_ok hop_ge2
    hop_le hb_c hblk_c hsstk_c h8_pre hcnt_pre hm_sz (fun n' ys m' hlt hinv =>
      hJm n' ys m'
        (by dsimp only at hnfail; simp only [hnfail, Bool.false_eq_true, ↓reduceIte]; exact hlt)
        hinv)

/-- Step-13 `Func.wp` proof for `fidStep13S4ShrinkBlkBoolM8Fn` (`full_shrink_blk_bool_m8`, with
`L6a` hoisted `alen = h->arena_len`) against `FullM8CoreParity.m8ShrinkBlkBoolSpec`. -/
theorem full_shrink_blk_bool_m8_step13_wp (Γ : Env)
    (hSl : ∀ args m Q X, m8ShrinkLowerSpec args m Q X →
      Γ "full_shrink_lower_m8" [i64, i32, i32] [.bool] args m Q X)
    (hMm : ∀ args m Q X, Full.fullMinMarkSpec args m Q X →
      Γ "full_min_mark" [i64, i32, i8] [] args m Q X) :
    ∀ args m Q X, m8ShrinkBlkBoolSpec args m Q X →
      Func.wp Γ fidStep13S4ShrinkBlkBoolM8Fn.body args m Q X := by
  rintro ⟨h, beg, end_b, blvl, max_tr, ⟨⟩⟩ m Q X hsp
  obtain ⟨c, F0, s, keepLen, R, rfl, hcore, hmin0, hno8_0, hbeg1, hbeg_end, hend_kl, hkl_cv,
    hblvl_pos, hblvl_lt, hblk_spec, hkeep_spec, hm, hQ⟩ := m8ShrinkBlkBoolSpec_elim hsp
  exact s13_shrink_blk_bool_specs_wp Γ hSl
    (fun _ _ _ _ hm' => hMm _ _ _ _ (m8_fullMinMarkSpec_of_specs hm'))
    hcore (m8_toSpecsMinInv hmin0) hno8_0
    hbeg1 hbeg_end hend_kl hkl_cv hblvl_pos hblvl_lt hblk_spec hkeep_spec hm
    fun ok tmp' mrk' mclr' sstk' wsort' mcl' mcf' ticks' m'
        hc' hmin' hab' h8' hm2' hfl hoth hlvl hnd hEnt hrem hm' =>
      hQ ok tmp' mrk' mclr' sstk' wsort' mcl' mcf' ticks' m'
        hc' (m8_toFullMinInv hmin') hab' h8' hm2' hfl hoth hlvl hnd hEnt hrem hm'

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S4

end
