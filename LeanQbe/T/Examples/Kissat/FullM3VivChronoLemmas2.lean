module

public import LeanQbe.T.Examples.Kissat.FullM3VivChrono
public import LeanQbe.T.Examples.Kissat.FullSpec
public import LeanQbe.T.Examples.Kissat.FullAnalyzeLemmas5
public import LeanQbe.T.Logic.C0HeadStep
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat M3a `Func.wp` Proofs — Part 2 (`full_analyze_rsn` + `promote.c` Glue Promotion)

Proves `Func.wp` UNSAT soundness (`XPost := False`, `0` SAT proofs) for
`FullM3VivChrono.full_analyze_rsn` against canonical `Full.fullAnalyzeRsnSpec`:
- Binary reasons dispatch to `full_analyze_lit` unchanged.
- Redundant large reasons recompute distinct-level glue bounded by `min(glue - 1, tier2, 32)` via
  read-only scans of `arena` and `level`, promote `ar[rsn]` preserving `PH_GARB` (bit 19) and
  `PH_SHRK` (bit 23), bump `glue_used` + usage bits, and analyze all clause literals.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM3VivChrono

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open Kraken.Bedrock2.Test

section AnalyzeRsnProof

open FullAnalyzeTactics FullAnalyzeHelpers
open scoped FullArenaTactics FullAnalyzeTactics

local elab "c0_hsteps_np" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { pruneJnz := false } 10000

local elab "c0_hsteps_nogrp_np" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { unrollGroup := false, pruneJnz := false } 10000

private theorem m3_anaMarksCov_to_anaWorkInv {c : FullCfg} {s : FullState}
    (h : FullAnaMarksCov c s) : FullAnalyzeSpecs.AnaWorkInv c s :=
  ⟨h.1, h.2.1, h.2.2.1, fun v hv hnz =>
    let ⟨k, hk, hkv⟩ := h.2.2.2 v hv hnz
    ⟨hkv ▸ (h.2.2.1 k hk).1, k, hk, hkv⟩⟩

private theorem m3_anaWorkInv_to_anaMarksCov {c : FullCfg} {s : FullState}
    (h : FullAnalyzeSpecs.AnaWorkInv c s) : FullAnaMarksCov c s :=
  ⟨h.1, h.2.1, h.2.2.1, fun v hv hnz => (h.2.2.2 v hv hnz).2⟩

private theorem m3_canonCut_to_anaCut {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {k : FullCoreState} (h : FullWitnessCutInv c F0 F_cur cut k) :
    FullAnalyzeSpecs.FullWitnessCutInv c F0 F_cur cut k :=
  ⟨h.ext_sound, h.inconsistent_sound, h.arena, h.watches, h.cur_level_le, h.trail_lits_lt,
    h.trail_vars_nodup, h.vals_domain, h.vals_true_iff, h.vals_false_iff, h.lvl_le, h.dec_earliest,
    h.levels_inhabited, h.level0_sound, h.trail_pos_inv, h.level0_rsn_none, h.frame_trail_lt,
    h.frame_trail_mono, h.frame_trail_before_lt, h.frame_dec_lt,
    fun idx hi hcond hne =>
      hcond.elim (fun hc => h.reason_inv_cut idx hc hne)
        (fun hlt => h.reason_inv_below idx hi hlt hne),
    fun idx hi hcond hne hlg =>
      hcond.elim (fun hc => h.reason_lit_mem_cut idx hc hne hlg)
        (fun hlt => h.reason_lit_mem_below idx hi hlt hne hlg)⟩

private theorem m3_anaCut_to_canonCut {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {k : FullCoreState} (h : FullAnalyzeSpecs.FullWitnessCutInv c F0 F_cur cut k)
    (hcut : cut ≤ k.trail_end) : FullWitnessCutInv c F0 F_cur cut k :=
  ⟨⟨h.ext_sound, h.inconsistent_sound, h.arena, h.watches, h.cur_level_le, h.trail_lits_lt,
    h.trail_vars_nodup, h.vals_domain, h.vals_true_iff, h.vals_false_iff, h.lvl_le, h.dec_earliest,
    h.levels_inhabited, h.level0_sound, h.trail_pos_inv, h.level0_rsn_none, h.frame_trail_lt,
    h.frame_trail_mono, h.frame_trail_before_lt, h.frame_dec_lt,
    fun idx hi hlt hne => h.reason_inv idx hi (Or.inr hlt) hne,
    fun idx hi hlt hne hlg => h.reason_lit_mem idx hi (Or.inr hlt) hne hlg⟩,
    hcut,
    fun idx hc hne => h.reason_inv idx (Nat.lt_of_lt_of_le hc hcut) (Or.inl hc) hne,
    fun idx hc hne hlg => h.reason_lit_mem idx (Nat.lt_of_lt_of_le hc hcut) (Or.inl hc) hne hlg⟩

private theorem m3_fullMem_arena_gu_eq {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} {ar1 ar2 gu1 gu2 : List (BitVec 32)} (ha : ar1 = ar2) (hg : gu1 = gu2)
    (hm : (FullMem c ⟨{ s.core with arena := ar1 },
      { s.scratch with glue_used := gu1 }⟩ ⋆ R) m) :
    (FullMem c ⟨{ s.core with arena := ar2 },
      { s.scratch with glue_used := gu2 }⟩ ⋆ R) m := by
  subst ha hg; exact hm

private theorem m3_bv64_ite_iff {P Q : Prop} [Decidable P] [Decidable Q] (h : P ↔ Q) :
    (if P then (1#64 : BitVec 64) else 0#64) = BitVec.ofNat 64 (if Q then 1 else 0) := by
  by_cases hp : P
  · have hq : Q := h.mp hp; simp [hp, hq]
  · have hnq : ¬Q := mt h.mpr hp; simp [hp, hnq]

private theorem m3_res_step_of_lit {s_mrk mrk1 mrk2 : List (BitVec 8)} {mv v : Nat}
    {r0 r1 r2 : BitVec 64}
    (hmp0 : ∀ w < mv, s_mrk[w]?.getD 0#8 ≠ 0#8 → mrk1[w]?.getD 0#8 = s_mrk[w]?.getD 0#8)
    (hmp1 : ∀ w < mv, mrk1[w]?.getD 0#8 ≠ 0#8 → mrk2[w]?.getD 0#8 = mrk1[w]?.getD 0#8)
    (hnew1 : ∀ w < mv, mrk1[w]?.getD 0#8 = 0#8 → mrk2[w]?.getD 0#8 ≠ 0#8 → v = w)
    (hr1 : r1 = r0 + BitVec.ofNat 64 ((List.range mv).filter fun w =>
      decide (s_mrk[w]?.getD 0#8 = 0#8) && decide (mrk1[w]?.getD 0#8 ≠ 0#8)).length)
    (hr2 : r2 = r1 + if v < mv ∧ mrk1[v]?.getD 0#8 = 0#8 ∧ mrk2[v]?.getD 0#8 ≠ 0#8
      then 1#64 else 0#64) : r2 = r0 + BitVec.ofNat 64 ((List.range mv).filter fun w =>
      decide (s_mrk[w]?.getD 0#8 = 0#8) && decide (mrk2[w]?.getD 0#8 ≠ 0#8)).length := by
  let c1 := ((List.range mv).filter fun w =>
    decide (s_mrk[w]?.getD 0#8 = 0#8) && decide (mrk1[w]?.getD 0#8 ≠ 0#8)).length
  have hf := filter_step_of_lit (fun _ => true) (tc0 := 0) (tc1 := c1)
    (tc2 := c1 + if v < mv ∧ mrk1[v]?.getD 0#8 = 0#8 ∧ mrk2[v]?.getD 0#8 ≠ 0#8 ∧
      (true : Bool) = true then 1 else 0) hmp0 hmp1 hnew1 (Nat.zero_le _) (by simp [c1]) rfl
  simp only [Nat.sub_zero, Bool.and_true, and_true] at hf
  rw [hr2, hr1, BitVec.add_assoc]; congr 1; dsimp only [c1] at hf; rw [← hf]
  split <;> simp [BitVec.ofNat_add]

private abbrev M3CanonRsnPre (c : FullCfg) (s : FullState) (rsn_lits : List Nat)
    (skip_var : BitVec 32) (mrk' : List (BitVec 8)) (tmp' : List (BitVec 32))
    (tc' tl' : Nat) (res' : BitVec 64) : Prop :=
  (∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 ≠ 0#8 →
    mrk'[v]?.getD 0#8 = s.core.mrk[v]?.getD 0#8) ∧
  (∀ k < s.core.tmp_len, tmp'[k]? = s.core.tmp[k]?) ∧
  (∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 = 0#8 → mrk'[v]?.getD 0#8 ≠ 0#8 →
    ∃ l ∈ rsn_lits, l / 2 = v ∧ v < s.core.cur_vars ∧ v ≠ skip_var.toNat ∧
      0 < (s.core.lvl[v]?.getD 0#32).toNat ∧ (s.core.lvl[v]?.getD 0#32).toNat ≤ s.core.cur_level) ∧
  (∀ j, s.core.tmp_len ≤ j → j < tl' → let l := (tmp'[j]?.getD 0#32).toNat
    l ∈ rsn_lits ∧ l < 2 * s.core.cur_vars ∧ l / 2 ≠ skip_var.toNat ∧
    s.core.mrk[l / 2]?.getD 0#8 = 0#8 ∧ 0 < (s.core.lvl[l / 2]?.getD 0#32).toNat ∧
    (s.core.lvl[l / 2]?.getD 0#32).toNat < s.core.cur_level ∧ mrk'[l / 2]?.getD 0#8 ≠ 0#8) ∧
  (∀ j1 j2, s.core.tmp_len ≤ j1 → j1 < j2 → j2 < tl' →
    (tmp'[j1]?.getD 0#32).toNat / 2 ≠ (tmp'[j2]?.getD 0#32).toNat / 2) ∧
  (tc' - s.core.tmp_cnt = ((List.range s.core.cur_vars).filter fun w =>
    decide (s.core.mrk[w]?.getD 0#8 = 0#8) && decide (mrk'[w]?.getD 0#8 ≠ 0#8) &&
    decide ((s.core.lvl[w]?.getD 0#32).toNat = s.core.cur_level)).length) ∧
  (res' = s.scratch.res_sz + BitVec.ofNat 64 ((List.range s.core.cur_vars).filter fun w =>
    decide (s.core.mrk[w]?.getD 0#8 = 0#8) && decide (mrk'[w]?.getD 0#8 ≠ 0#8)).length)

private theorem m3_canon_rsn_step {c : FullCfg} {s : FullState} {l_bv skip_var : BitVec 32}
    {rsn_lits : List Nat} {mrk' mrk2 : List (BitVec 8)} {tmp' tmp2 : List (BitVec 32)}
    {tc' tl' tc2 tl2 : Nat} {res' res2 : BitVec 64}
    (hcv_le : s.core.cur_vars ≤ c.max_vars) (htl_ge : s.core.tmp_len ≤ tl')
    (htl2_ge : tl' ≤ tl2) (htl2_inc : tl2 ≤ tl' + 1)
    (htc_ge : s.core.tmp_cnt ≤ tc') (hl_mem : l_bv.toNat ∈ rsn_lits)
    (hpre : M3CanonRsnPre c s rsn_lits skip_var mrk' tmp' tc' tl' res')
    (hmp2 : ∀ v < c.max_vars, mrk'[v]?.getD 0#8 ≠ 0#8 →
      mrk2[v]?.getD 0#8 = mrk'[v]?.getD 0#8) (htp2 : ∀ k < tl', tmp2[k]? = tmp'[k]?)
    (hnm2 : ∀ v < c.max_vars, mrk'[v]?.getD 0#8 = 0#8 → mrk2[v]?.getD 0#8 ≠ 0#8 →
      l_bv.toNat / 2 = v ∧ v < s.core.cur_vars ∧ v ≠ skip_var.toNat ∧
      0 < (s.core.lvl[v]?.getD 0#32).toNat ∧ (s.core.lvl[v]?.getD 0#32).toNat ≤ s.core.cur_level)
    (hnt2 : ∀ j, tl' ≤ j → j < tl2 → (tmp2[j]?.getD 0#32).toNat = l_bv.toNat ∧
      l_bv.toNat / 2 < s.core.cur_vars ∧ l_bv.toNat / 2 ≠ skip_var.toNat ∧
      mrk'[l_bv.toNat / 2]?.getD 0#8 = 0#8 ∧ 0 < (s.core.lvl[l_bv.toNat / 2]?.getD 0#32).toNat ∧
      (s.core.lvl[l_bv.toNat / 2]?.getD 0#32).toNat < s.core.cur_level ∧
      mrk2[l_bv.toNat / 2]?.getD 0#8 ≠ 0#8)
    (hres2 : res2 = res' + if l_bv.toNat / 2 < s.core.cur_vars ∧
      mrk'[l_bv.toNat / 2]?.getD 0#8 = 0#8 ∧ mrk2[l_bv.toNat / 2]?.getD 0#8 ≠ 0#8
      then 1#64 else 0#64)
    (htc2_eq : tc2 = tc' + if l_bv.toNat / 2 < s.core.cur_vars ∧
      mrk'[l_bv.toNat / 2]?.getD 0#8 = 0#8 ∧ mrk2[l_bv.toNat / 2]?.getD 0#8 ≠ 0#8 ∧
      (s.core.lvl[l_bv.toNat / 2]?.getD 0#32).toNat = s.core.cur_level then 1 else 0) :
    M3CanonRsnPre c s rsn_lits skip_var mrk2 tmp2 tc2 tl2 res2 := by
  obtain ⟨hmp, htp, hnm, hnt, hnd, hcnt, hres_l⟩ := hpre
  refine ⟨fun v hv hnz => by have h1 := hmp v hv hnz; rw [hmp2 v hv (by rwa [h1]), h1],
    fun k hk => by rw [htp2 k (by omega), htp k hk], fun v hv hs0 hmnz => ?_,
    fun j hj1 hj2 => ?_, fun j1 j2 hj1 hj12 hj2 => ?_, ?_, ?_⟩
  · by_cases hm1 : mrk'[v]?.getD 0#8 = 0#8
    · obtain ⟨rfl, hlt, hne', hpos, hle⟩ := hnm2 v hv hm1 hmnz
      exact ⟨l_bv.toNat, hl_mem, rfl, hlt, hne', hpos, hle⟩
    · exact hnm v hv hs0 hm1
  · by_cases hjold : j < tl'
    · rw [htp2 j hjold]; obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hnt j hj1 hjold
      exact ⟨h1, h2, h3, h4, h5, h6, by rw [hmp2 _ (by omega) h7]; exact h7⟩
    · obtain ⟨heq, hlt, hne', hm1_0, hpos, hcl, _⟩ := hnt2 j (by omega) hj2
      have hs0 : s.core.mrk[l_bv.toNat / 2]?.getD 0#8 = 0#8 :=
        Classical.byContradiction fun hnz => by
          rw [hmp _ (by omega) hnz] at hm1_0; exact hnz hm1_0
      exact ⟨by rwa [heq], by omega, by omega, by rwa [heq], by rwa [heq], by rwa [heq],
        by rwa [heq]⟩
  · by_cases hj2_old : j2 < tl'
    · rw [htp2 j1 (by omega), htp2 j2 hj2_old]; exact hnd j1 j2 hj1 hj12 hj2_old
    · have hj1_old : j1 < tl' := by omega
      rw [htp2 j1 hj1_old]; have h1 := (hnt j1 hj1 hj1_old).2.2.2.2.2.2
      obtain ⟨heq, _, _, hm1_0, _⟩ := hnt2 j2 (by omega) hj2
      rw [heq]; intro heq_v; rw [← heq_v] at hm1_0; exact absurd hm1_0 h1
  · exact filter_step_of_lit
      (fun w => decide ((s.core.lvl[w]?.getD 0#32).toNat = s.core.cur_level))
      (mv := s.core.cur_vars) (tc0 := s.core.tmp_cnt) (tc1 := tc') (v := l_bv.toNat / 2)
      (fun w hw => hmp w (by omega)) (fun w hw => hmp2 w (by omega))
      (fun w hw h0 hnz => (hnm2 w (by omega) h0 hnz).1) htc_ge hcnt
      (by simpa only [decide_eq_true_eq] using htc2_eq)
  · exact m3_res_step_of_lit (mv := s.core.cur_vars) (v := l_bv.toNat / 2)
      (fun w hw => hmp w (by omega)) (fun w hw => hmp2 w (by omega))
      (fun w hw h0 hnz => (hnm2 w (by omega) h0 hnz).1) hres_l hres2

private abbrev m3CanonRsnState (s : FullState) (mrk' : List (BitVec 8))
    (tmp' ws1' arena' gu' : List (BitVec 32)) (mcl' tc' tl' : Nat) (ant' res' : BitVec 64) :
    FullState :=
  { s with core := { s.core with mrk := mrk', tmp := tmp', tmp_cnt := tc', tmp_len := tl',
                                 min_clr_len := mcl', arena := arena' }
           scratch := { s.scratch with work_stk1 := ws1', glue_used := gu',
                                       ant_sz := ant', res_sz := res' } }

private theorem maskGlue_bit :
    ∀ i : Fin 32, (0x0007FFFF#32)[i.val] = decide (i.val < 19) := by decide

private theorem maskNGlue_bit :
    ∀ i : Fin 32, (~~~0x0007FFFF#32)[i.val] = decide (19 ≤ i.val) := by decide

private theorem mask19_bit_rsn :
    ∀ i : Fin 32, (0x00080000#32)[i.val] = decide (i.val = 19) := by decide

private theorem mask23_bit_rsn :
    ∀ i : Fin 32, (0x00800000#32)[i.val] = decide (i.val = 23) := by decide

private theorem bv32_bit_false_of_lt {ng : BitVec 32} (hng : ng.toNat < 2 ^ 19)
    {i : Nat} (hi19 : 19 ≤ i) (hi32 : i < 32) : ng[i] = false := by
  rw [BitVec.getElem_eq_testBit_toNat]
  exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hng (Nat.pow_le_pow_right (by decide) hi19))

private theorem bv32_setGlue_garb (hdr ng : BitVec 32) (hng : ng.toNat < 2 ^ 19) :
    (((hdr &&& ~~~0x0007FFFF#32) ||| ng) &&& 0x00080000#32) = (hdr &&& 0x00080000#32) := by
  ext i hi
  simp only [BitVec.getElem_and, BitVec.getElem_or, maskNGlue_bit ⟨i, hi⟩,
    mask19_bit_rsn ⟨i, hi⟩]
  by_cases h19 : i = 19
  · subst h19
    have hb : ng[19] = false := bv32_bit_false_of_lt hng (Nat.le_refl 19) (by omega)
    simp [hb]
  · simp [h19]

private theorem bv32_setGlue_shrk (hdr ng : BitVec 32) (hng : ng.toNat < 2 ^ 19) :
    (((hdr &&& ~~~0x0007FFFF#32) ||| ng) &&& 0x00800000#32) = (hdr &&& 0x00800000#32) := by
  ext i hi
  simp only [BitVec.getElem_and, BitVec.getElem_or, maskNGlue_bit ⟨i, hi⟩,
    mask23_bit_rsn ⟨i, hi⟩]
  by_cases h23 : i = 23
  · subst h23
    have hb : ng[23] = false := bv32_bit_false_of_lt hng (by decide) (by omega)
    simp [hb]
  · simp [h23]

private theorem arenaSetGlue_preserves_fullWitnessCut {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {cut : Nat} {k : FullCoreState} (hlen : k.LengthsOk c)
    (hw : FullAnalyzeSpecs.FullWitnessCutInv c F0 F_cur cut k)
    {cref : Nat} (hcref : cref ∈ fullArenaClauseRefsCore k) (ng : BitVec 32)
    (hng : ng.toNat < 2 ^ 19) :
    let hdr := fullArenaHdrCore k cref
    let k' : FullCoreState :=
      { k with arena := k.arena.set cref ((hdr &&& ~~~0x0007FFFF#32) ||| ng) }
    FullAnalyzeSpecs.FullWitnessCutInv c F0 F_cur cut k' ∧
    fullArenaClauseRefsCore k' = fullArenaClauseRefsCore k ∧
    (∀ r ∈ fullArenaClauseRefsCore k,
      fullArenaClauseSizeCore k' r = fullArenaClauseSizeCore k r ∧
      fullArenaClauseGarbCore k' r = fullArenaClauseGarbCore k r ∧
      fullArenaClauseLitsCore k' r = fullArenaClauseLitsCore k r) :=
  hdrBitsUpdate_preserves_fullWitnessCut hlen hw hcref
    (fun x => (x &&& ~~~0x0007FFFF#32) ||| ng)
    k.arena_garbage k.num_irred k.num_redundant
    (bv32_setGlue_garb _ ng hng) (bv32_setGlue_shrk _ ng hng)

theorem m3_analyze_rsn_wp (Γ : Env)
    (hLit : ∀ a m Q X, fullAnalyzeLitSpec a m Q X →
      Γ "full_analyze_lit" [i64, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, fullAnalyzeRsnSpec a m Q X → Func.wp Γ full_analyze_rsn_body a m Q X := by
  rintro ⟨h, rsn, skip_var, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, cut, s, R, rfl, hlen, hw, hcov, htl_cv, htc_fit, hrsn_ref, hm, hQ⟩
  have hmax32 := fullInv_max_vars_lt32 c; have hcv_le := hlen.core_ok.cur_vars_le
  have har_len := hlen.core_ok.arena_len_arr; have har_le := hlen.core_ok.arena_len_le
  have hgu_len := hlen.scratch_ok.glue_used_len
  have hcur32 : s.core.cur_level < 2 ^ 32 := by
    have := hw.cur_level_le; have := hlen.core_ok.trail_end_le; omega
  have hret_false_same : Q (false, ()) m :=
    hQ false s.core.mrk s.core.tmp s.core.tmp_cnt s.core.tmp_len s.core.min_clr_len s.core.arena
      s.scratch m hlen hw hcov ⟨rfl, rfl⟩ rfl (Nat.le_refl _) htl_cv (Nat.le_refl _) rfl
      (fun _ _ => ⟨rfl, rfl, rfl⟩) (fun _ _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ h0 h => absurd h0 h) (fun _ h1 h2 => by omega) (fun _ _ _ h1 h2 => by omega)
      (by rw [Nat.sub_self, eq_comm, List.length_eq_zero_iff, List.filter_eq_nil_iff]
          intro _ _; simp)
      (by rw [List.filter_eq_nil_iff.mpr (fun _ _ => by simp)]; simp) (fun hc => by cases hc) hm
  fa_unmdata; c0_step; c0_step
  · exact hret_false_same
  · c0_step
    · have hne : rsn ≠ 0xFFFFFFFF#32 := ‹_›; have hbin : (rsn &&& 0x80000000#32) ≠ 0#32 := ‹_›
      c0_hsteps_np
      refine wp_call_of_spec _ _ (hLit (c.hdr, rsn &&& 0x7FFFFFFF#32, skip_var, ()) _ _ _
        ⟨c, s, R, rfl, hlen, hcur32, htl_cv, by omega, hcov, hm, ?_⟩)
      intro ok mrk' tmp' tc' tl' mcl' ws1' ant' res' m' _ hlen' hcov' htl_ge _ htl_le htc_ge
        hant_eq hres_eq htc_eq hmpres htpres hnewm hnewt hok hm'
      c0_hsteps_np
      have hw' : FullWitnessCutInv c F0 F_cur cut
          (m3CanonRsnState s mrk' tmp' ws1' s.core.arena s.scratch.glue_used
            mcl' tc' tl' ant' res').core :=
        m3_anaCut_to_canonCut (same_core_fullWitnessCut (m3_canonCut_to_anaCut hw)
          hlen'.core_ok.mrk_len hlen'.core_ok.tmp_len_arr hlen'.core_ok.min_clr_len_le htl_le
          (tc' := tc')) hw.cut_le
      have htc_f := filter_step_of_lit
        (fun w => decide ((s.core.lvl[w]?.getD 0#32).toNat = s.core.cur_level))
        (mv := s.core.cur_vars) (tc0 := s.core.tmp_cnt) (tc1 := s.core.tmp_cnt)
        (v := (rsn &&& 0x7FFFFFFF#32).toNat / 2) (fun _ _ _ => rfl)
        (fun w hw_lt => hmpres w (by omega)) (fun w hw_lt h0 hnz => (hnewm w (by omega) h0 hnz).1)
        (Nat.le_refl _) (by rw [Nat.sub_self, List.filter_eq_nil_iff.mpr (fun _ _ => by simp)]; rfl)
        (by simpa only [decide_eq_true_eq] using htc_eq)
      have hres_f := m3_res_step_of_lit (mv := s.core.cur_vars)
        (v := (rsn &&& 0x7FFFFFFF#32).toNat / 2) (r0 := s.scratch.res_sz)
        (r1 := s.scratch.res_sz) (fun _ _ _ => rfl) (fun w hw_lt => hmpres w (by omega))
        (fun w hw_lt h0 hnz => (hnewm w (by omega) h0 hnz).1)
        (by rw [List.filter_eq_nil_iff.mpr (fun _ _ => by simp)]; simp) hres_eq
      refine hQ ok mrk' tmp' tc' tl' mcl' s.core.arena
        { s.scratch with work_stk1 := ws1', ant_sz := ant', res_sz := res' } m'
        hlen' hw' hcov' ⟨rfl, rfl⟩ rfl htl_ge htl_le htc_ge rfl (fun _ _ => ⟨rfl, rfl, rfl⟩)
        hmpres htpres ?_ ?_ (fun _ _ _ h1 h2 => by omega) htc_f hres_f ?_ hm'
      · intro v hv h0 hnz; obtain ⟨rfl, hlt, hne', hpos, hle⟩ := hnewm v hv h0 hnz
        exact ⟨(rsn &&& 0x7FFFFFFF#32).toNat, (mem_fullRsnLits_bin hne hbin).mpr rfl,
          rfl, hlt, hne', hpos, hle⟩
      · intro j hj1 hj2; obtain ⟨heq, _, _, h0, hpos, hcl, hmk⟩ := hnewt j hj1 hj2
        exact ⟨(mem_fullRsnLits_bin hne hbin).mpr heq, by omega, by omega, by rwa [heq],
          by rwa [heq], by rwa [heq], by rwa [heq]⟩
      · intro hok'; obtain ⟨hvlt, hrest⟩ := hok hok'
        refine ⟨hne, ?_, fun l hl => ?_⟩
        · rw [hant_eq, fullRsnLits, ite_eq_right (fun h => hne h), ite_eq_left hbin,
            List.countP_cons, List.countP_nil, Nat.zero_add]
          exact congrArg (s.scratch.ant_sz + ·)
            (m3_bv64_ite_iff (by simp only [decide_eq_true_eq]))
        · simp only [fullRsnLits, ite_eq_right (fun h => hne h), ite_eq_left hbin,
            List.mem_singleton] at hl
          subst hl; refine ⟨hvlt, fun hne' => ?_⟩
          obtain ⟨hm1, h0r⟩ := hrest hne'; refine ⟨hm1, fun h0 => ?_⟩
          obtain ⟨hle, _, hlow⟩ := h0r h0
          exact ⟨hle, fun hpos hlt => let ⟨_, htget⟩ := hlow hpos hlt
            ⟨s.core.tmp_len, Nat.le_refl _, by omega, by rw [htget]; rfl⟩⟩
    · have hne : rsn ≠ 0xFFFFFFFF#32 := ‹_›; have hlarge : (rsn &&& 0x80000000#32) = 0#32 := ‹_›
      have href : rsn.toNat ∈ fullArenaClauseRefs s := hrsn_ref hne hlarge
      obtain ⟨hbd3, hsz3, hbd, hbd_le, _⟩ := hw.arena.refs_wf rsn.toNat href
      have hsz_get : (s.core.arena[rsn.toNat + 2]'(by omega)).toNat =
          fullArenaClauseSize s rsn.toNat := by
        unfold fullArenaClauseSize fullArenaClauseSizeCore
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      have hhdr_get : s.core.arena[rsn.toNat]'(by omega) = s.core.arena[rsn.toNat]?.getD 0#32 := by
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      fa_unmdata; (try c0_let_simp)
      c0_step; c0_step; c0_step; all_goals (try exact hret_false_same)
      c0_step; c0_step; c0_step; all_goals (try exact hret_false_same)
      c0_step; c0_step; all_goals (try exact hret_false_same)
      refine wp_join_group (ts := [i32]) (fun (_hdr_r, ()) m1 => ∃ arena1 gu1,
          let s1 : FullState := { s with core := { s.core with arena := arena1 }
                                         scratch := { s.scratch with glue_used := gu1 } }
          FullWitnessCutInv c F0 F_cur cut s1.core ∧ s1.LengthsOk c ∧
          fullArenaClauseRefs s1 = fullArenaClauseRefs s ∧
          (∀ r ∈ fullArenaClauseRefs s, fullArenaClauseSize s1 r = fullArenaClauseSize s r ∧
            fullArenaClauseGarb s1 r = fullArenaClauseGarb s r ∧
            fullArenaClauseLits s1 r = fullArenaClauseLits s r) ∧
          (∀ k < fullArenaClauseSize s rsn.toNat,
            arena1[rsn.toNat + 3 + k]? = s.core.arena[rsn.toNat + 3 + k]?) ∧
          (FullMem c s1 ⋆ R) m1) ?_ ?_
      · rintro _ ⟨_hdr_r, ⟨⟩⟩ m1 ⟨arena1, gu1, hw1, hlen1, hrefs1, hcl1, har1_eq, hm1⟩
        c0_hsteps_nogrp
        let s1 : FullState := { s with core := { s.core with arena := arena1 }
                                       scratch := { s.scratch with glue_used := gu1 } }
        have har1_len : arena1.length = c.arena_cap := hlen1.core_ok.arena_len_arr
        have har1_le : s.core.arena_len ≤ c.arena_cap := hlen1.core_ok.arena_len_le
        let sz : Nat := fullArenaClauseSize s rsn.toNat
        let antPred : Nat → Bool := fun l =>
          decide (l / 2 < s.core.cur_vars ∧ 0 < (s.core.lvl[l / 2]?.getD 0#32).toNat ∧
            (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ s.core.cur_level)
        let LoopInv : Nat → List (BitVec 8) → List (BitVec 32) → List (BitVec 32) →
            Nat → Nat → Nat → BitVec 64 → BitVec 64 → Prop :=
          fun i mrk' tmp' ws1' mcl' tc' tl' ant' res' =>
            i ≤ sz ∧ mrk'.length = c.max_vars ∧ tmp'.length = c.max_vars ∧
            ws1'.length = 2 * c.max_vars ∧ mcl' ≤ c.max_vars ∧
            s.core.tmp_len ≤ tl' ∧ tl' ≤ s.core.cur_vars ∧ s.core.tmp_cnt ≤ tc' ∧
            FullAnaMarksCov c (m3CanonRsnState s1 mrk' tmp' ws1' arena1 gu1
              mcl' tc' tl' ant' res') ∧
            M3CanonRsnPre c s (fullArenaClauseLits s rsn.toNat) skip_var mrk' tmp' tc' tl' res' ∧
            (∀ w < s.core.cur_vars, s.core.mrk[w]?.getD 0#8 = 0#8 → mrk'[w]?.getD 0#8 ≠ 0#8 →
              (s.core.lvl[w]?.getD 0#32).toNat < s.core.cur_level →
              ∃ j, s.core.tmp_len ≤ j ∧ j < tl' ∧ (tmp'[j]?.getD 0#32).toNat / 2 = w) ∧
            ant' = s.scratch.ant_sz +
              BitVec.ofNat 64 (((fullArenaClauseLits s rsn.toNat).take i).countP antPred) ∧
            ∀ k < i, let l := (s.core.arena[rsn.toNat + 3 + k]?.getD 0#32).toNat
              l / 2 < s.core.cur_vars ∧ (l / 2 ≠ skip_var.toNat →
                (0 < (s.core.lvl[l / 2]?.getD 0#32).toNat → mrk'[l / 2]?.getD 0#8 ≠ 0#8) ∧
                (s.core.mrk[l / 2]?.getD 0#8 = 0#8 →
                  (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ s.core.cur_level ∧
                  (0 < (s.core.lvl[l / 2]?.getD 0#32).toNat →
                    (s.core.lvl[l / 2]?.getD 0#32).toNat < s.core.cur_level →
                    ∃ j, s.core.tmp_len ≤ j ∧ j < tl' ∧
                      (tmp'[j]?.getD 0#32).toNat / 2 = l / 2)))
        refine wp_loop_group (fun r (iv, ()) ml => ∃ i mrk' tmp' ws1' mcl' tc' tl' ant' res',
          r = sz - i ∧ iv = BitVec.ofNat 32 i ∧ LoopInv i mrk' tmp' ws1' mcl' tc' tl' ant' res' ∧
          (FullMem c (m3CanonRsnState s mrk' tmp' ws1' arena1 gu1 mcl' tc' tl' ant' res') ⋆ R) ml)
          ?_ ?_
        · rintro L r ⟨iv, ⟨⟩⟩ ml ih ⟨i, mrk', tmp', ws1', mcl', tc', tl', ant', res', rfl, rfl,
            ⟨hile, hml_l, htl_l, hws_l, hmcl_le, htl_ge, htl_le, htc_ge, hcov', hpre,
              hnewlow, hant_l, hdone⟩, hml⟩
          have ⟨hmpres, htpres, hnewm, hnewt, hnd_t, hcnt, hres_l⟩ := hpre
          have hsz_mod : (rsn.toNat + (2#64).toNat) % 2 ^ 64 = rsn.toNat + 2 := by
            change (rsn.toNat + 2) % 2 ^ 64 = rsn.toNat + 2; omega
          have hidx_eq : s.core.arena[(rsn.toNat + (2#64).toNat) % 2 ^ 64]'(by omega) =
              s.core.arena[rsn.toNat + 2]'(by omega) := by simp only [hsz_mod]
          rw [Blocks.get_here]; c0_hsplit
          · have hi32 : i < 2 ^ 32 := by omega
            have hilt : i < sz := by
              have hlt_bv : i % 2 ^ 32 <
                  (s.core.arena[(rsn.toNat + (2#64).toNat) % 2 ^ 64]'(by omega)).toNat := ‹_›
              rw [Nat.mod_eq_of_lt hi32, hidx_eq, hsz_get] at hlt_bv; exact hlt_bv
            have hidx_l : ((rsn.setWidth 64 + 3) + (BitVec.ofNat 32 i).setWidth 64).toNat =
                rsn.toNat + 3 + i := by simp only [bv_c0, BitVec.reduceToNat]; omega
            have hilt_core : i < fullArenaClauseSizeCore s.core rsn.toNat := hilt
            have hidx_lt : (rsn.setWidth 64 + 3 + (BitVec.ofNat 32 i).setWidth 64).toNat <
                arena1.length := by rw [hidx_l, har1_len]; omega
            c0_hsteps_np
            have htc_le_cv : tc' - s.core.tmp_cnt ≤ s.core.cur_vars := by
              rw [hcnt]; exact Nat.le_trans (List.length_filter_le _ _) (by simp)
            let st := m3CanonRsnState s1 mrk' tmp' ws1' arena1 gu1 mcl' tc' tl' ant' res'
            have hst_len : st.LengthsOk c :=
              ⟨{ hlen1.core_ok with
                  mrk_len := hml_l, tmp_len_arr := htl_l
                  tmp_len_le := (by dsimp [st]; omega), min_clr_len_le := hmcl_le },
               { hlen1.scratch_ok with work_stk1_len := hws_l }⟩
            let l_bv : BitVec 32 := arena1[rsn.toNat + 3 + i]'(by omega)
            have hl_eq : l_bv = s.core.arena[rsn.toNat + 3 + i]'(by omega) := by
              have h1 : arena1[rsn.toNat + 3 + i]? = some l_bv :=
                List.getElem?_eq_getElem (by omega)
              rw [har1_eq i hilt, List.getElem?_eq_getElem (by omega)] at h1
              exact (Option.some.inj h1).symm
            have hl_get : (s.core.arena[rsn.toNat + 3 + i]?.getD 0#32).toNat = l_bv.toNat := by
              rw [List.getElem?_eq_getElem (by omega), Option.getD_some, ← hl_eq]
            have hl_mem : l_bv.toNat ∈ fullArenaClauseLits s rsn.toNat :=
              (mem_fullArenaClauseLitsCore_iff (by omega)).mpr ⟨i, hilt, by rw [← hl_eq]⟩
            rw [getElem_eq_of_idx (hi := hidx_lt) (hj := by omega) hidx_l]
            refine wp_call_of_spec _ _ (hLit (c.hdr, l_bv, skip_var, ()) _ _ _
              ⟨c, st, R, rfl, hst_len, hcur32, htl_le, by dsimp [st]; omega, hcov', hml, ?_⟩)
            intro ok2 mrk2 tmp2 tc2 tl2 mcl2 ws2 ant2 res2 m2 _ hlen2 hcov2 htl2_ge htl2_inc
              htl2_le htc2_ge hant2 hres2 htc2_eq hmpres2 htpres2 hnewm2 hnewt2 hok2 hm2
            dsimp only [st, s1] at *
            have hpre2 := m3_canon_rsn_step hcv_le htl_ge htl2_ge htl2_inc htc_ge hl_mem hpre
              hmpres2 htpres2 hnewm2 hnewt2 hres2 htc2_eq
            cases ok2 with
            | false =>
              wp_unfold; obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hpre2
              exact hQ false mrk2 tmp2 tc2 tl2 mcl2 arena1
                { s.scratch with work_stk1 := ws2, glue_used := gu1,
                                 ant_sz := ant2, res_sz := res2 } m2
                hlen2
                (m3_anaCut_to_canonCut (same_core_fullWitnessCut (m3_canonCut_to_anaCut hw1)
                  hlen2.core_ok.mrk_len hlen2.core_ok.tmp_len_arr hlen2.core_ok.min_clr_len_le
                  htl2_le (tc' := tc2)) hw1.cut_le)
                hcov2 ⟨rfl, rfl⟩ rfl (by omega) htl2_le (by omega) hrefs1 hcl1 h1 h2
                (fun v hv hs0 hmnz => let ⟨l, hl, hr⟩ := h3 v hv hs0 hmnz
                  ⟨l, (mem_fullRsnLits_large hne hlarge).mpr hl, hr⟩)
                (fun j hj1 hj2 => let ⟨ha, hr⟩ := h4 j hj1 hj2
                  ⟨(mem_fullRsnLits_large hne hlarge).mpr ha, hr⟩)
                h5 h6 h7 (fun hc => by cases hc) hm2
            | true =>
              wp_unfold; obtain ⟨hvlt, hrest⟩ := hok2 rfl
              have htake1 : (fullArenaClauseLits s rsn.toNat).take (i + 1) =
                  (fullArenaClauseLits s rsn.toNat).take i ++ [l_bv.toNat] := by
                have hlen_l : (fullArenaClauseLits s rsn.toNat).length = sz := by
                  simp [fullArenaClauseLits, fullArenaClauseLitsCore, sz,
                    fullArenaClauseSize]; omega
                rw [List.take_add_one, List.getElem?_eq_getElem (by omega), Option.toList_some]
                congr 2; unfold fullArenaClauseLits fullArenaClauseLitsCore
                simp [List.getElem_map, List.getElem_take, List.getElem_drop, ← hl_eq]
              have hant2_eq : ant2 = s.scratch.ant_sz + BitVec.ofNat 64
                  (((fullArenaClauseLits s rsn.toNat).take (i + 1)).countP antPred) := by
                rw [hant2, hant_l, htake1, List.countP_append, List.countP_cons, List.countP_nil,
                  Nat.zero_add, BitVec.add_assoc, BitVec.ofNat_add]
                exact congrArg (s.scratch.ant_sz + ·) (congrArg _
                  (m3_bv64_ite_iff (by simp only [antPred, decide_eq_true_eq])))
              rw [show BitVec.ofNat 32 i + 1 = BitVec.ofNat 32 (i + 1) from
                BitVec.eq_of_toNat_eq (by
                  have h1n : (1 : BitVec 32).toNat = 1 := rfl
                  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, h1n,
                    Nat.mod_eq_of_lt (show i < 2 ^ 32 by omega),
                    Nat.mod_eq_of_lt (show i + 1 < 2 ^ 32 by omega)])]
              refine ih (sz - (i + 1)) _ _ (by omega)
                ⟨i + 1, mrk2, tmp2, ws2, mcl2, tc2, tl2, ant2, res2, rfl, rfl,
                  ⟨by omega, hlen2.core_ok.mrk_len, hlen2.core_ok.tmp_len_arr,
                    hlen2.scratch_ok.work_stk1_len, hlen2.core_ok.min_clr_len_le,
                    by omega, htl2_le, by omega, hcov2, hpre2, ?_, hant2_eq, ?_⟩, hm2⟩
              · intro w hw_lt hs0 hmnz2 hltcl
                by_cases hm1_w : mrk'[w]?.getD 0#8 = 0#8
                · obtain ⟨rfl, _, hne', hpos, _⟩ := hnewm2 w (by omega) hm1_w hmnz2
                  obtain ⟨_, htget⟩ := ((hrest hne').2 hm1_w).2.2 hpos hltcl
                  exact ⟨tl', htl_ge, by omega, by rw [htget]; rfl⟩
                · obtain ⟨j, hj1, hj2, hjeq⟩ := hnewlow w hw_lt hs0 hm1_w hltcl
                  exact ⟨j, hj1, by omega, by rw [htpres2 j hj2]; exact hjeq⟩
              · intro k hk; by_cases hki : k = i
                · subst hki; dsimp only; rw [hl_get]; refine ⟨hvlt, fun hne' => ?_⟩
                  obtain ⟨hpos_m, hm1_r⟩ := hrest hne'; refine ⟨hpos_m, fun hs0 => ?_⟩
                  by_cases hm1_w : mrk'[l_bv.toNat / 2]?.getD 0#8 = 0#8
                  · obtain ⟨hle, _, hlow⟩ := hm1_r hm1_w
                    exact ⟨hle, fun hpos hltcl => let ⟨_, htget⟩ := hlow hpos hltcl
                      ⟨tl', htl_ge, by omega, by rw [htget]; rfl⟩⟩
                  · obtain ⟨_, _, _, _, _, _, hle⟩ := hnewm _ (by omega) hs0 hm1_w
                    exact ⟨hle, fun _ hltcl =>
                      let ⟨j, hj1, hj2, hjeq⟩ := hnewlow _ hvlt hs0 hm1_w hltcl
                      ⟨j, hj1, by omega, by rw [htpres2 j hj2]; exact hjeq⟩⟩
                · obtain ⟨hkv, hkrest⟩ := hdone k (by omega)
                  refine ⟨hkv, fun hne' => ?_⟩; obtain ⟨h1, h2⟩ := hkrest hne'
                  refine ⟨fun hp => by rw [hmpres2 _ (by omega) (h1 hp)]; exact h1 hp, ?_⟩
                  intro hs0
                  obtain ⟨hle, hlow⟩ := h2 hs0
                  exact ⟨hle, fun hpos hltcl => let ⟨j, hj1, hj2, hjeq⟩ := hlow hpos hltcl
                    ⟨j, hj1, by omega, by rw [htpres2 j hj2]; exact hjeq⟩⟩
          · c0_hsteps_nogrp
            have hi32 : i < 2 ^ 32 := by omega
            have hieq : i = sz := by
              have hge_bv : ¬ i % 2 ^ 32 <
                  (s.core.arena[(rsn.toNat + (2#64).toNat) % 2 ^ 64]'(by omega)).toNat := ‹_›
              rw [Nat.mod_eq_of_lt hi32, hidx_eq, hsz_get] at hge_bv; omega
            refine hQ true mrk' tmp' tc' tl' mcl' arena1
              { s.scratch with work_stk1 := ws1', glue_used := gu1,
                               ant_sz := ant', res_sz := res' } ml
              ⟨{ hlen1.core_ok with
                  mrk_len := hml_l, tmp_len_arr := htl_l
                  tmp_len_le := (by dsimp; omega), min_clr_len_le := hmcl_le },
               { hlen1.scratch_ok with work_stk1_len := hws_l }⟩
              (m3_anaCut_to_canonCut (same_core_fullWitnessCut (m3_canonCut_to_anaCut hw1)
                hml_l htl_l hmcl_le htl_le (tc' := tc')) hw1.cut_le)
              hcov' ⟨rfl, rfl⟩ rfl htl_ge htl_le htc_ge hrefs1 hcl1 hmpres htpres
              (fun v hv hs0 hmnz => let ⟨l, hl, hr⟩ := hnewm v hv hs0 hmnz
                ⟨l, (mem_fullRsnLits_large hne hlarge).mpr hl, hr⟩)
              (fun j hj1 hj2 => let ⟨h1, hr⟩ := hnewt j hj1 hj2
                ⟨(mem_fullRsnLits_large hne hlarge).mpr h1, hr⟩)
              hnd_t hcnt hres_l (fun _ => ⟨hne, ?_, fun l hl => by
                simp only [fullRsnLits, hne, hlarge, ↓reduceIte] at hl
                obtain ⟨k, hk, hget⟩ := (mem_fullArenaClauseLitsCore_iff (by omega)).mp hl
                have hkget : (s.core.arena[rsn.toNat + 3 + k]?.getD 0#32).toNat = l := by
                  rw [List.getElem?_eq_getElem (by omega), Option.getD_some, hget]
                have hd := hdone k (by rw [hieq]; exact hk); rwa [hkget] at hd⟩) hml
            · have hlen_l : (fullArenaClauseLits s rsn.toNat).length = sz := by
                simp only [fullArenaClauseLits, fullArenaClauseLitsCore, sz, fullArenaClauseSize,
                  List.length_map, List.length_take, List.length_drop]; have := har_len; omega
              rw [hant_l, hieq, List.take_of_length_le (Nat.le_of_eq hlen_l)]
              simp [fullRsnLits, hne, hlarge, antPred]
        · intro L hL; c0_hsteps_nogrp
          refine hL sz _ m1 ⟨0, s.core.mrk, s.core.tmp, s.scratch.work_stk1, s.core.min_clr_len,
            s.core.tmp_cnt, s.core.tmp_len, s.scratch.ant_sz, s.scratch.res_sz, by omega, rfl,
            ⟨Nat.zero_le _, hlen1.core_ok.mrk_len, hlen1.core_ok.tmp_len_arr,
              hlen1.scratch_ok.work_stk1_len, hlen1.core_ok.min_clr_len_le, Nat.le_refl _,
              htl_cv, Nat.le_refl _, hcov, ⟨fun _ _ _ => rfl, fun _ _ => rfl,
                fun _ _ h0 hnz => absurd h0 hnz, fun _ h1 h2 => by omega,
                fun _ _ _ h1 h2 => by omega,
                by rw [Nat.sub_self, eq_comm, List.length_eq_zero_iff, List.filter_eq_nil_iff]
                   intro _ _; simp,
                by rw [List.filter_eq_nil_iff.mpr (fun _ _ => by simp)]; simp⟩,
              fun _ _ h0 hnz _ => absurd h0 hnz, (by simp), fun _ hk => by omega⟩, hm1⟩
      · intro Jred hJred
        clear hLit hQ htl_cv htc_fit hcov hrsn_ref hret_false_same skip_var
        c0_let_simp; c0_step
        · refine wp_join_group (ts := [i32, i64])
            (fun (hdr0, glue0, ()) m0 => ∃ arena0,
              let s0 : FullState := { s with core := { s.core with arena := arena0 } }
              FullWitnessCutInv c F0 F_cur cut s0.core ∧ s0.LengthsOk c ∧
              fullArenaClauseRefs s0 = fullArenaClauseRefs s ∧
              (∀ r ∈ fullArenaClauseRefs s, fullArenaClauseSize s0 r = fullArenaClauseSize s r ∧
                fullArenaClauseGarb s0 r = fullArenaClauseGarb s r ∧
                fullArenaClauseLits s0 r = fullArenaClauseLits s r) ∧
              (∀ k < fullArenaClauseSize s rsn.toNat,
                arena0[rsn.toNat + 3 + k]? = s.core.arena[rsn.toNat + 3 + k]?) ∧
              fullArenaHdrCore s0.core rsn.toNat = hdr0 ∧
              (FullMem c s0 ⋆ R) m0) ?_ ?_
          · rintro _ ⟨hdr0, glue0, ⟨⟩⟩ m0 ⟨arena0, hw0, hlen0, hrefs0, hcl0, har0_eq, hhdr0, hm0⟩
            let s0 : FullState := { s with core := { s.core with arena := arena0 } }
            have har0_len : arena0.length = c.arena_cap := hlen0.core_ok.arena_len_arr
            have href0 : rsn.toNat ∈ fullArenaClauseRefs s0 := by rw [hrefs0]; exact href
            dsimp only [s0] at hm0
            c0_hsteps_nogrp
            refine wp_join_group (ts := [i64])
              (fun (gi, ()) m_gi => gi.toNat < 64 ∧ (FullMem c s0 ⋆ R) m_gi) ?_ ?_
            · rintro _ ⟨gi, ⟨⟩⟩ m_gi ⟨hgi_lt, hm_gi⟩; c0_let_simp
              refine wp_join_group (ts := []) (fun () m_gu => ∃ gu1, gu1.length = 64 ∧
                (FullMem c ⟨s0.core, { s.scratch with glue_used := gu1 }⟩ ⋆ R) m_gu) ?_ ?_
              · rintro _ ⟨⟩ m_gu ⟨gu1, hgu1, hm_gu⟩; clear hm_gi
                let s_gu : FullState := ⟨s0.core, { s.scratch with glue_used := gu1 }⟩
                change (FullMem c s_gu ⋆ R) m_gu at hm_gu; c0_let_simp
                refine wp_join_group (ts := [i32])
                  (fun (new_u, ()) m_nu => (FullMem c s_gu ⋆ R) m_nu) ?_ ?_
                · rintro _ ⟨new_u, ⟨⟩⟩ m_nu hm_nu; clear hm_gu
                  dsimp only [s_gu, s0] at hm_nu
                  c0_hsteps
                  · obtain ⟨hw', hr', hcl'⟩ := arenaBumpUsage_preserves_fullWitnessCut hlen0.core_ok
                      (m3_canonCut_to_anaCut hw0) href0 new_u
                    have har_u_eq : arena0.set (rsn.setWidth 64).toNat
                        ((hdr0 &&& 134217727#32) ||| (new_u <<< (27 : BitVec 32))) =
                        arena0.set rsn.toNat ((fullArenaHdrCore s0.core rsn.toNat &&&
                          0x07FFFFFF#32) ||| (new_u <<< 27)) := by
                      rw [bv_c0_zext32_64, hhdr0]; rfl
                    let arena_u := arena0.set rsn.toNat
                      ((fullArenaHdrCore s0.core rsn.toNat &&& 0x07FFFFFF#32) ||| (new_u <<< 27))
                    refine hJred (hdr0, ()) _ ⟨arena_u, gu1, m3_anaCut_to_canonCut hw' hw0.cut_le,
                      ⟨{ hlen0.core_ok with arena_len_arr := by simp [arena_u, har0_len] },
                       { hlen0.scratch_ok with glue_used_len := hgu1 }⟩,
                      hr'.trans hrefs0,
                      fun r hr =>
                        let ⟨s_a, g_a, l_a⟩ :=
                          hcl' r (by change r ∈ fullArenaClauseRefs s0; rw [hrefs0]; exact hr)
                        let ⟨s_b, g_b, l_b⟩ := hcl0 r hr
                        ⟨s_a.trans s_b, g_a.trans g_b, l_a.trans l_b⟩,
                      fun k hk => (List.getElem?_set_ne (by omega)).trans (har0_eq k hk), ?_⟩
                    refine m3_fullMem_arena_gu_eq har_u_eq rfl ?_
                    assumption
                  · exact hJred (hdr0, ()) _ ⟨arena0, gu1, hw0,
                      ⟨hlen0.core_ok, { hlen0.scratch_ok with glue_used_len := hgu1 }⟩,
                      hrefs0, hcl0, har0_eq, hm_nu⟩
                · intro Jnu hJnu; c0_hsteps_np <;> exact hJnu _ _ hm_gu
              · intro Jgu hJgu; dsimp only [s0] at hm_gi; c0_hsteps_np
                · exact hJgu () _ ⟨s.scratch.glue_used.set gi.toNat
                    (s.scratch.glue_used[gi.toNat]'(by omega) + 1), by simp [hgu_len],
                    by assumption⟩
                · exact hJgu () _ ⟨s.scratch.glue_used, hgu_len, hm_gi⟩
            · intro Jgi hJgi; c0_hsteps_np
              · exact hJgi _ _ ⟨by decide, hm0⟩
              · refine hJgi _ _ ⟨?_, hm0⟩
                rw [show (63 : BitVec 64).toNat = 63 from rfl] at hc; omega
          · intro Jpromo hJpromo
            have hJpromo_same : ∀ hdr0 glue0 m0, fullArenaHdrCore s.core rsn.toNat = hdr0 →
                (FullMem c s ⋆ R) m0 → Jpromo (hdr0, glue0, ()) m0 :=
              fun hdr0 glue0 m0 hh hm0 =>
                hJpromo (hdr0, glue0, ()) m0 ⟨s.core.arena, hw, hlen, rfl,
                  fun _ _ => ⟨rfl, rfl, rfl⟩, fun _ _ => rfl, hh,
                  by change (FullMem c s ⋆ R) m0; exact hm0⟩
            c0_hsplit
            · c0_hsplit
              · c0_hsteps_nogrp
                refine wp_join_group (ts := [i64])
                  (fun (_lim0, ()) ml1 => (FullMem c s ⋆ R) ml1) ?_ ?_
                · rintro _ ⟨lim0, ⟨⟩⟩ ml1 hm1
                  c0_hsteps_nogrp
                  refine wp_join_group (ts := [i64])
                    (fun (lim, ()) ml2 => lim.toNat ≤ 32 ∧ (FullMem c s ⋆ R) ml2) ?_ ?_
                  · rintro _ ⟨lim, ⟨⟩⟩ ml2 ⟨hlim_le, hm2⟩
                    have hlvl_ge_cv : s.core.cur_vars ≤ s.core.lvl.length := by
                      rw [hlen.core_ok.lvl_len]; exact hcv_le
                    c0_hsteps_nogrp
                    refine wp_loop_inv (ts := [i64, i64, .bool])
                      (fun (ng, lo, more, ()) mo =>
                        ng.toNat ≤ 33 ∧ (more = true → ng.toNat ≤ lim.toNat + 1) ∧
                        (FullMem c s ⋆ R) mo)
                      (fun (ng, _lo, more, ()) _ =>
                        2 * (33 - ng.toNat) + (if more then 1 else 0)) ?_ ?_
                    · intro Jout hJout; fa_fast_steps
                      exact hJout (0#64, 0#64, true, ()) ml2
                        ⟨by decide, fun _ => Nat.zero_le _, hm2⟩
                    · intro Jout (ng, lo, more, ⟨⟩) mo ⟨hng_le, hng_lim, hmo⟩ ih_out
                      cases more with
                      | false =>
                        fa_fast_steps <;> try contradiction
                        · have hng_lt : ng.toNat < 2 ^ 19 := by omega
                          have hng32_lt : (ng.setWidth 32).toNat < 2 ^ 19 := by
                            rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]; exact hng_lt
                          obtain ⟨hw0, hr0, hcl0⟩ := arenaSetGlue_preserves_fullWitnessCut
                            hlen.core_ok (m3_canonCut_to_anaCut hw) href (ng.setWidth 32) hng32_lt
                          have hhdr_eq : s.core.arena.set (rsn.setWidth 64).toNat
                              (((s.core.arena[rsn.toNat]'(by omega)) &&& ~~~0x0007FFFF#32) |||
                                ng.setWidth 32) =
                              s.core.arena.set rsn.toNat ((fullArenaHdrCore s.core rsn.toNat &&&
                                ~~~0x0007FFFF#32) ||| ng.setWidth 32) := by
                            rw [bv_c0_zext32_64, hhdr_get]; rfl
                          let hdr_p :=
                            ((s.core.arena[rsn.toNat]'(by omega)) &&& ~~~0x0007FFFF#32) |||
                            ng.setWidth 32
                          let arena_p := s.core.arena.set rsn.toNat
                            ((fullArenaHdrCore s.core rsn.toNat &&& ~~~0x0007FFFF#32) |||
                              ng.setWidth 32)
                          have hhdr_self : fullArenaHdrCore
                              ({ s.core with arena := arena_p } : FullCoreState) rsn.toNat =
                              hdr_p := by
                            unfold fullArenaHdrCore; dsimp only [arena_p, hdr_p]
                            rw [List.getElem?_set_self (by omega), Option.getD_some]
                            exact congrArg (· ||| ng.setWidth 32)
                              (congrArg (· &&& ~~~0x0007FFFF#32) hhdr_get.symm)
                          refine hJpromo (hdr_p, ng, ()) _
                            ⟨arena_p, m3_anaCut_to_canonCut hw0 hw.cut_le,
                             ⟨{ hlen.core_ok with arena_len_arr := by simp [arena_p, har_len] },
                              hlen.scratch_ok⟩,
                             hr0, hcl0, fun k _ => List.getElem?_set_ne (by omega), hhdr_self, ?_⟩
                          dsimp only [arena_p]; rw [← hhdr_eq]; assumption
                        · exact hJpromo_same _ _ mo hhdr_get.symm hmo
                        · exact hJpromo_same _ _ mo hhdr_get.symm hmo
                      | true =>
                        dsimp only
                        refine wp_unroll_group fun Jex hJex => ?_
                        c0_hsteps_nogrp <;> try (first | contradiction | exact absurd rfl ‹_›)
                        · have hng_le_lim : ng.toNat ≤ lim.toNat := by omega
                          refine wp_loop_inv (ts := [i64, i32])
                            (fun (best, k, ()) mk => k.toNat ≤ fullArenaClauseSize s rsn.toNat ∧
                              (FullMem c s ⋆ R) mk)
                            (fun (_best, k, ()) _ =>
                              fullArenaClauseSize s rsn.toNat - k.toNat) ?_ ?_
                          · intro Jin hJin; c0_hsteps_np
                            exact hJin (0xFFFFFFFFFFFFFFFF#64, 0#32, ()) mo ⟨Nat.zero_le _, hmo⟩
                          · intro Jin (best, k, ⟨⟩) mk ⟨hk_le, hmk⟩ ih_in
                            have hsz_mod : (rsn.toNat + (2#64).toNat) % 2 ^ 64 = rsn.toNat + 2 := by
                              change (rsn.toNat + 2) % 2 ^ 64 = rsn.toNat + 2; omega
                            have hidx_eq :
                                s.core.arena[(rsn.toNat + (2#64).toNat) % 2 ^ 64]'(by omega) =
                                s.core.arena[rsn.toNat + 2]'(by omega) := by simp only [hsz_mod]
                            c0_hsplit
                            · have hk_lt : k.toNat < fullArenaClauseSize s rsn.toNat := by
                                have h1 : k.toNat < (s.core.arena[(rsn.toNat +
                                    (2#64).toNat) % 2 ^ 64]'(by omega)).toNat := ‹_›
                                rwa [hidx_eq, hsz_get] at h1
                              have hk_core : k.toNat < fullArenaClauseSizeCore s.core rsn.toNat :=
                                hk_lt
                              have hk_idx : ((rsn.setWidth 64 + 3#64) + k.setWidth 64).toNat =
                                  rsn.toNat + 3 + k.toNat := by
                                simp only [bv_c0]; omega
                              have hk_lt_ar : ((rsn.setWidth 64 + 3#64) + k.setWidth 64).toNat <
                                  s.core.arena.length := by rw [hk_idx, har_len]; omega
                              have hkp1 : (k + 1#32).toNat = k.toNat + 1 := by
                                rw [BitVec.toNat_add, BitVec.toNat_ofNat,
                                  Nat.mod_eq_of_lt (by omega : 1 < 2 ^ 32)]
                                exact Nat.mod_eq_of_lt (by have := BitVec.isLt k; omega)
                              c0_hsteps_nogrp_np
                              refine wp_join_group (ts := [i64])
                                (fun (_best', ()) mb => (FullMem c s ⋆ R) mb) ?_ ?_
                              · rintro _ ⟨best', ⟨⟩⟩ mb hmb
                                c0_hsteps_np
                                exact ih_in (best', k + 1#32, ()) mb
                                  (by dsimp only; rw [hkp1]; omega)
                                  ⟨by rw [hkp1]; omega, hmb⟩
                              · intro Jbest hJbest; c0_hsteps_np <;> exact hJbest _ mk hmk
                            · have hk_eq : k.toNat = fullArenaClauseSize s rsn.toNat := by
                                have hge : ¬ k.toNat < (s.core.arena[(rsn.toNat +
                                    (2#64).toNat) % 2 ^ 64]'(by omega)).toNat := ‹_›
                                rw [hidx_eq, hsz_get] at hge; omega
                              c0_hsteps_np
                              · have hdec : 2 * (33 - ng.toNat) + 0 <
                                    2 * (33 - ng.toNat) + 1 := by omega
                                exact ih_out (ng, lo, false, ()) mk hdec
                                  ⟨hng_le, (fun hf => False.elim (Bool.noConfusion hf)), hmk⟩
                              · have hngp1 : (ng + 1#64).toNat = ng.toNat + 1 := by
                                  rw [BitVec.toNat_add, BitVec.toNat_ofNat,
                                    Nat.mod_eq_of_lt (by omega : 1 < 2 ^ 64)]
                                  exact Nat.mod_eq_of_lt (by omega)
                                have hdec : 2 * (33 - (ng + 1#64).toNat) + 1 <
                                    2 * (33 - ng.toNat) + 1 := by
                                  rw [hngp1]; omega
                                exact ih_out (ng + 1#64, _ , true, ()) mk hdec
                                  ⟨by rw [hngp1]; omega, fun _ => by rw [hngp1]; omega, hmk⟩
                        · c0_hsteps <;> try (first | contradiction | exact absurd rfl ‹_›)
                          exact hJpromo_same _ _ mo hhdr_get.symm hmo
                  · intro Jlim2 hJlim2
                    c0_hsplit
                    · c0_hsteps_np; exact hJlim2 (32#64, ()) ml1 ⟨by decide, hm1⟩
                    · c0_hsteps_np
                      refine hJlim2 (lim0, ()) ml1 ⟨?_, hm1⟩
                      rw [show (32 : BitVec 64).toNat = 32 from rfl] at hc; omega
                · intro Jlim hJlim
                  c0_hsplit
                  · c0_hsteps_np; exact hJlim _ m hm
                  · c0_hsteps_np; exact hJlim _ m hm
              · c0_hsteps_np
                exact hJpromo_same _ _ m hhdr_get.symm hm
            · c0_hsteps_np
              exact hJpromo_same _ _ m hhdr_get.symm hm
        · c0_hsteps_np
          simp only [bv_c0_zext32_64]
          exact hJred (s.core.arena[rsn.toNat]'(by omega), ()) _
            ⟨s.core.arena, s.scratch.glue_used, hw, hlen, rfl,
             fun _ _ => ⟨rfl, rfl, rfl⟩, fun _ _ => rfl, hm⟩

end AnalyzeRsnProof

end LeanQbe.T.Examples.Kissat.FullM3VivChrono
