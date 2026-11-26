/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep11
public import LeanQbe.T.Examples.Kissat.FullM6HdrProof0
public import LeanQbe.T.Examples.Kissat.FullM6OrchProof0
public import LeanQbe.T.Examples.Kissat.FullM6ProofUtil
import LeanQbe.T.Examples.Kissat.FullAnalyzeLemmas1
import LeanQbe.T.Examples.Kissat.FullAnalyzeLemmas2
import LeanQbe.T.Examples.Kissat.FullDeduce1UipLemmas1
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullSpec
import LeanQbe.T.Examples.Kissat.FullSpec1
import LeanQbe.T.Examples.Kissat.FullSpec2
import LeanQbe.T.Examples.Kissat.FullSpec3
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.WPLemmas
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Fidelity Step 11 PR 1: `full_analyze_rsn_m6_hdr` Proof (`FullFidelityStep11ProofRsn`)

UNSAT-only `Func.wp` proof (`public section`, `0` `@[expose]` on theorems/lemmas, `0` `import all`,
`std3`, `XPost`-polymorphic) for Step-11 `fidStep11AnalyzeRsnM6HdrFn` (`full_analyze_rsn_m6_hdr`,
guarding `m6_hdr_record_used` with `if (h->probing == 0ULL)` per `S11-2`) against
`FullM6Orch.m6AnalyzeRsnHdrSpec`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep11

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open Kraken.Bedrock2.Test
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM6ProofUtil
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics

section AnalyzeRsnStep11Helpers

private theorem s11_bv64_ite_iff {P Q : Prop} [Decidable P] [Decidable Q] (h : P ↔ Q) :
    (if P then (1#64 : BitVec 64) else 0#64) = BitVec.ofNat 64 (if Q then 1 else 0) := by
  by_cases hp : P
  · simp [hp, h.mp hp]
  · simp [hp, mt h.mpr hp]

private theorem s11_bv32_glue_bit (x g mask : BitVec 32) {b : Nat} (h19 : 19 ≤ b)
    (hmask_hi : (0xFFF80000#32 &&& mask) = mask)
    (hmask_eq : mask.toNat = 2 ^ b) (hg : g.toNat < 2 ^ 19) :
    (((x &&& 0xFFF80000#32) ||| g) &&& mask) = (x &&& mask) := by
  have hg_zero : (g &&& mask) = 0#32 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, BitVec.toNat_ofNat]
    apply Nat.eq_of_testBit_eq; intro k
    rw [Nat.testBit_and, Nat.zero_mod, Nat.zero_testBit, hmask_eq, Nat.testBit_two_pow]
    by_cases hkb : b = k
    · subst k
      have hdiv : g.toNat / 2 ^ b = 0 :=
        Nat.div_eq_of_lt (lt_of_lt_of_le hg (Nat.pow_le_pow_right (by decide) h19))
      simp [Nat.testBit, Nat.shiftRight_eq_div_pow, hdiv]
    · simp [hkb]
  rw [BitVec.and_or_distrib_right, hg_zero, BitVec.or_zero, BitVec.and_assoc, hmask_hi]

private theorem s11_filter_zero {α : Type} {p : α → Bool} {xs : List α}
    (h : ∀ x ∈ xs, p x = false) : (xs.filter p).length = 0 := by
  rw [List.filter_eq_nil_iff.mpr (fun x hx => by simp [h x hx])]; rfl

private theorem s11_res_step_of_lit {s_mrk mrk1 mrk2 : List (BitVec 8)} {mv v : Nat}
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
  have hf := FullAnalyzeHelpers.filter_step_of_lit (fun _ => true) (tc0 := 0) (tc1 := c1)
    (tc2 := c1 + if v < mv ∧ mrk1[v]?.getD 0#8 = 0#8 ∧ mrk2[v]?.getD 0#8 ≠ 0#8 ∧
      (true : Bool) = true then 1 else 0) hmp0 hmp1 hnew1 (Nat.zero_le _) (by simp [c1]) rfl
  simp only [Nat.sub_zero, Bool.and_true, and_true] at hf
  rw [hr2, hr1, BitVec.add_assoc]; congr 1; dsimp only [c1] at hf; rw [← hf]
  split <;> simp [BitVec.ofNat_add]

private abbrev S11RsnStepPre (s : FullState) (rsn_lits : List Nat) (skip_var : BitVec 32)
    (mrk' : List (BitVec 8)) (tmp' : List (BitVec 32)) (tc' tl' : Nat) (res' : BitVec 64) : Prop :=
  (∀ w < s.core.cur_vars, s.core.mrk[w]?.getD 0#8 ≠ 0#8 →
    mrk'[w]?.getD 0#8 = s.core.mrk[w]?.getD 0#8) ∧
  (∀ k < s.core.tmp_len, tmp'[k]? = s.core.tmp[k]?) ∧
  (∀ w < s.core.cur_vars, s.core.mrk[w]?.getD 0#8 = 0#8 → mrk'[w]?.getD 0#8 ≠ 0#8 →
    ∃ l ∈ rsn_lits, l / 2 = w ∧ w ≠ skip_var.toNat ∧
      0 < (s.core.lvl[w]?.getD 0#32).toNat ∧ (s.core.lvl[w]?.getD 0#32).toNat ≤ s.core.cur_level) ∧
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

private theorem s11_rsn_comb_step {s : FullState} {l_bv skip_var : BitVec 32}
    {rsn_lits : List Nat} {mrk' mrk2 : List (BitVec 8)} {tmp' tmp2 : List (BitVec 32)}
    {tc' tl' tc2 tl2 : Nat} {res' res2 : BitVec 64}
    (htl_ge : s.core.tmp_len ≤ tl') (htl2_ge : tl' ≤ tl2) (htl2_inc : tl2 ≤ tl' + 1)
    (htc_ge : s.core.tmp_cnt ≤ tc') (hl_mem : l_bv.toNat ∈ rsn_lits)
    (hpre : S11RsnStepPre s rsn_lits skip_var mrk' tmp' tc' tl' res')
    (hmp2 : ∀ w < s.core.cur_vars, mrk'[w]?.getD 0#8 ≠ 0#8 →
      mrk2[w]?.getD 0#8 = mrk'[w]?.getD 0#8) (htp2 : ∀ k < tl', tmp2[k]? = tmp'[k]?)
    (hnm2 : ∀ w < s.core.cur_vars, mrk'[w]?.getD 0#8 = 0#8 → mrk2[w]?.getD 0#8 ≠ 0#8 →
      l_bv.toNat / 2 = w ∧ w ≠ skip_var.toNat ∧ 0 < (s.core.lvl[w]?.getD 0#32).toNat ∧
      (s.core.lvl[w]?.getD 0#32).toNat ≤ s.core.cur_level)
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
    S11RsnStepPre s rsn_lits skip_var mrk2 tmp2 tc2 tl2 res2 := by
  obtain ⟨hmp, htp, hnm, hnt, hnd, hcnt, hres_l⟩ := hpre
  refine ⟨fun w hw hnz => by have h1 := hmp w hw hnz; rw [hmp2 w hw (by rwa [h1]), h1],
    fun k hk => by rw [htp2 k (by omega), htp k hk], fun w hw hs0 hmnz => ?_, fun j hj1 hj2 => ?_,
    fun j1 j2 hj1 hj12 hj2 => ?_, ?_, ?_⟩
  · by_cases hm1 : mrk'[w]?.getD 0#8 = 0#8
    · obtain ⟨rfl, hne', hpos, hle⟩ := hnm2 w hw hm1 hmnz
      exact ⟨l_bv.toNat, hl_mem, rfl, hne', hpos, hle⟩
    · exact hnm w hw hs0 hm1
  · by_cases hjold : j < tl'
    · rw [htp2 j hjold]; obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hnt j hj1 hjold
      exact ⟨h1, h2, h3, h4, h5, h6, by rw [hmp2 _ (by omega) h7]; exact h7⟩
    · obtain ⟨heq, hlt, hne', hm1_0, hpos, hcl, _⟩ := hnt2 j (by omega) hj2
      have hs0 : s.core.mrk[l_bv.toNat / 2]?.getD 0#8 = 0#8 :=
        Classical.byContradiction fun hnz => by rw [hmp _ hlt hnz] at hm1_0; exact hnz hm1_0
      exact ⟨by rwa [heq], by omega, by omega, by rwa [heq], by rwa [heq], by rwa [heq],
        by rwa [heq]⟩
  · by_cases hj2_old : j2 < tl'
    · rw [htp2 j1 (by omega), htp2 j2 hj2_old]; exact hnd j1 j2 hj1 hj12 hj2_old
    · have hj1_old : j1 < tl' := by omega
      rw [htp2 j1 hj1_old]; have h1 := (hnt j1 hj1 hj1_old).2.2.2.2.2.2
      obtain ⟨heq, _, _, hm1_0, _⟩ := hnt2 j2 (by omega) hj2
      rw [heq]; intro heq_v; rw [← heq_v] at hm1_0; exact absurd hm1_0 h1
  · exact FullAnalyzeHelpers.filter_step_of_lit
      (fun w => decide ((s.core.lvl[w]?.getD 0#32).toNat = s.core.cur_level))
      (mv := s.core.cur_vars) (tc0 := s.core.tmp_cnt) (tc1 := tc') (v := l_bv.toNat / 2)
      hmp hmp2 (fun w hw h0 hnz => (hnm2 w hw h0 hnz).1) htc_ge hcnt
      (by simpa only [decide_eq_true_eq] using htc2_eq)
  · exact s11_res_step_of_lit (mv := s.core.cur_vars) (v := l_bv.toNat / 2) hmp hmp2
      (fun w hw h0 hnz => (hnm2 w hw h0 hnz).1) hres_l hres2

private theorem s11_hdrBitsUpdate_cut {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {cut : Nat} {k : FullCoreState} (hlen : k.LengthsOk c)
    (hw : FullWitnessCutInv c F0 F_cur cut k)
    {cref : Nat} (hcref : cref ∈ fullArenaClauseRefsCore k)
    (f : BitVec 32 → BitVec 32) (ag' ni' nr' : BitVec 64)
    (hgarb : (f (fullArenaHdrCore k cref) &&& 0x00080000#32) =
      (fullArenaHdrCore k cref &&& 0x00080000#32))
    (hshrk : (f (fullArenaHdrCore k cref) &&& 0x00800000#32) =
      (fullArenaHdrCore k cref &&& 0x00800000#32)) :
    let hdr' := f (fullArenaHdrCore k cref)
    let k' : FullCoreState :=
      { k with arena := k.arena.set cref hdr', arena_garbage := ag',
               num_irred := ni', num_redundant := nr' }
    FullWitnessCutInv c F0 F_cur cut k' ∧
    fullArenaClauseRefsCore k' = fullArenaClauseRefsCore k ∧
    (∀ r ∈ fullArenaClauseRefsCore k,
      fullArenaClauseSizeCore k' r = fullArenaClauseSizeCore k r ∧
      fullArenaClauseGarbCore k' r = fullArenaClauseGarbCore k r ∧
      fullArenaClauseLitsCore k' r = fullArenaClauseLitsCore k r) := by
  have hwA : FullAnalyzeSpecs.FullWitnessCutInv c F0 F_cur cut k :=
    { ext_sound := hw.ext_sound, inconsistent_sound := hw.inconsistent_sound,
      arena := hw.arena, watches := hw.watches, cur_level_le := hw.cur_level_le,
      trail_lits_lt := hw.trail_lits_lt, trail_vars_nodup := hw.trail_vars_nodup,
      vals_domain := hw.vals_domain, vals_true_iff := hw.vals_true_iff,
      vals_false_iff := hw.vals_false_iff, lvl_le := hw.lvl_le, dec_earliest := hw.dec_earliest,
      levels_inhabited := hw.levels_inhabited, level0_sound := hw.level0_sound,
      trail_pos_inv := hw.trail_pos_inv, level0_rsn_none := hw.level0_rsn_none,
      frame_trail_lt := hw.frame_trail_lt, frame_trail_mono := hw.frame_trail_mono,
      frame_trail_before_lt := hw.frame_trail_before_lt, frame_dec_lt := hw.frame_dec_lt,
      reason_inv := fun idx hte hcond hne => hcond.elim (hw.reason_inv_cut idx · hne)
        (hw.reason_inv_below idx hte · hne),
      reason_lit_mem := fun idx hte hcond hne hlg => hcond.elim
        (hw.reason_lit_mem_cut idx · hne hlg) (hw.reason_lit_mem_below idx hte · hne hlg) }
  obtain ⟨hw', hrefs', hper'⟩ := FullAnalyzeHelpers.hdrBitsUpdate_preserves_fullWitnessCut
    hlen hwA hcref f ag' ni' nr' hgarb hshrk
  exact ⟨
    { ext_sound := hw'.ext_sound, inconsistent_sound := hw'.inconsistent_sound,
      arena := hw'.arena, watches := hw'.watches, cur_level_le := hw'.cur_level_le,
      trail_lits_lt := hw'.trail_lits_lt, trail_vars_nodup := hw'.trail_vars_nodup,
      vals_domain := hw'.vals_domain, vals_true_iff := hw'.vals_true_iff,
      vals_false_iff := hw'.vals_false_iff, lvl_le := hw'.lvl_le, dec_earliest := hw'.dec_earliest,
      levels_inhabited := hw'.levels_inhabited, level0_sound := hw'.level0_sound,
      trail_pos_inv := hw'.trail_pos_inv, level0_rsn_none := hw'.level0_rsn_none,
      frame_trail_lt := hw'.frame_trail_lt, frame_trail_mono := hw'.frame_trail_mono,
      frame_trail_before_lt := hw'.frame_trail_before_lt, frame_dec_lt := hw'.frame_dec_lt,
      reason_inv_below := fun idx hte hlt hne => hw'.reason_inv idx hte (Or.inr hlt) hne,
      reason_lit_mem_below := fun idx hte hlt hne hlg =>
        hw'.reason_lit_mem idx hte (Or.inr hlt) hne hlg,
      cut_le := hw.cut_le,
      reason_inv_cut := fun idx hcut hne =>
        hw'.reason_inv idx (Nat.lt_of_lt_of_le hcut hw.cut_le) (Or.inl hcut) hne,
      reason_lit_mem_cut := fun idx hcut hne hlg => hw'.reason_lit_mem idx
        (Nat.lt_of_lt_of_le hcut hw.cut_le) (Or.inl hcut) hne hlg }, hrefs', hper'⟩

private theorem s11_rsn_lit_loop {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {cut : Nat} {ext ext1 : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {arena1 : List (BitVec 32)} {sc1 : FullScratch} {m1 : Mem 64}
    {Q : Post [.bool]} {X : XPost} {rsn skip_var : Val i32} {pArena : Val i64} {sz_bv : Val i32}
    (hpArena : pArena = c.pArena)
    (hLit : ∀ a m Q X, Full.fullAnalyzeLitSpec a m Q X →
      Γ "full_analyze_lit" [i64, i32, i32] [.bool] a m Q X)
    (hext1 : M6HdrExtOk ext1) (hwb1 : M6HdrExtInitOk ext → M6ExtW2bPres ext ext1)
    (hlen : s.LengthsOk c) (hwork : FullAnaMarksCov c s) (htl_cv : s.core.tmp_len ≤ s.core.cur_vars)
    (htc_fit : s.core.tmp_cnt + s.core.cur_vars + 1 < 2 ^ 64)
    (hcv_le : s.core.cur_vars ≤ c.max_vars) (hcur32 : s.core.cur_level < 2 ^ 32)
    (hne : rsn ≠ 0xFFFFFFFF#32) (hlarge : (rsn &&& 0x80000000#32) = 0#32)
    (hbd : rsn.toNat + 3 + fullArenaClauseSizeCore s.core rsn.toNat ≤
      fullArenaNextOff s.core.arena s.core.arena_len rsn.toNat)
    (hbd_le : fullArenaNextOff s.core.arena s.core.arena_len rsn.toNat ≤ s.core.arena_len)
    (hsz_idx : (rsn.setWidth 64 + 2#64).toNat = rsn.toNat + 2)
    (hsz_lt : (rsn.setWidth 64 + 2#64).toNat < s.core.arena.length)
    (hsz_bv : sz_bv = s.core.arena[(rsn.setWidth 64 + 2#64).toNat]'hsz_lt)
    (hw1 : FullWitnessCutInv c F0 F_cur cut
      ({ s with core := { s.core with arena := arena1 }, scratch := sc1 } : FullState).core)
    (hlen1 : ({ s with core := { s.core with arena := arena1 }, scratch := sc1 } :
      FullState).LengthsOk c)
    (hexp1 : FullExtScratchPres s
      { s with core := { s.core with arena := arena1 }, scratch := sc1 })
    (hws1 : sc1.work_stk1 = s.scratch.work_stk1) (hws2 : sc1.work_stk2 = s.scratch.work_stk2)
    (hant1 : sc1.ant_sz = s.scratch.ant_sz) (hres1 : sc1.res_sz = s.scratch.res_sz)
    (hrefs1 : fullArenaClauseRefs
      { s with core := { s.core with arena := arena1 }, scratch := sc1 } = fullArenaClauseRefs s)
    (hcl1 : ∀ r ∈ fullArenaClauseRefs s,
      fullArenaClauseSize { s with core := { s.core with arena := arena1 }, scratch := sc1 } r =
        fullArenaClauseSize s r ∧
      fullArenaClauseGarb { s with core := { s.core with arena := arena1 }, scratch := sc1 } r =
        fullArenaClauseGarb s r ∧
      fullArenaClauseLits { s with core := { s.core with arena := arena1 }, scratch := sc1 } r =
        fullArenaClauseLits s r)
    (har1_eq : ∀ k < fullArenaClauseSize s rsn.toNat,
      arena1[rsn.toNat + 3 + k]? = s.core.arena[rsn.toNat + 3 + k]?)
    (hm1 : (FullMem c { s with core := { s.core with arena := arena1 }, scratch := sc1 } ⋆
      (m6ExtMem (m6ExtAddr c.hdr) ext1 ⋆ R)) m1)
    (hQ : ∀ (ok : Bool) (mrk' : List (BitVec 8)) (tmp' : List (BitVec 32))
        (tc' tl' mcl' : Nat) (arena' : List (BitVec 32)) (sc' : FullScratch)
        (ext' : List (BitVec 64)) (m' : Mem 64),
      let s' : FullState :=
        { core := { s.core with mrk := mrk', tmp := tmp', tmp_cnt := tc', tmp_len := tl',
                                min_clr_len := mcl', arena := arena' },
          scratch := sc' }
      M6HdrExtOk ext' → (M6HdrExtInitOk ext → M6ExtW2bPres ext ext') →
      s'.LengthsOk c → FullWitnessCutInv c F0 F_cur cut s'.core →
      FullAnaMarksCov c s' → FullExtScratchPres s s' → sc'.work_stk2 = s.scratch.work_stk2 →
      s.core.tmp_len ≤ tl' → tl' ≤ s.core.cur_vars → s.core.tmp_cnt ≤ tc' →
      fullArenaClauseRefs s' = fullArenaClauseRefs s →
      (∀ r ∈ fullArenaClauseRefs s, fullArenaClauseSize s' r = fullArenaClauseSize s r ∧
        fullArenaClauseGarb s' r = fullArenaClauseGarb s r ∧
        fullArenaClauseLits s' r = fullArenaClauseLits s r) →
      (∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 ≠ 0#8 →
        mrk'[v]?.getD 0#8 = s.core.mrk[v]?.getD 0#8) →
      (∀ k < s.core.tmp_len, tmp'[k]? = s.core.tmp[k]?) →
      (∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 = 0#8 → mrk'[v]?.getD 0#8 ≠ 0#8 →
        ∃ l ∈ fullRsnLits s rsn, l / 2 = v ∧ v < s.core.cur_vars ∧ v ≠ skip_var.toNat ∧
          0 < (s.core.lvl[v]?.getD 0#32).toNat ∧
          (s.core.lvl[v]?.getD 0#32).toNat ≤ s.core.cur_level) →
      (∀ j, s.core.tmp_len ≤ j → j < tl' → let l := (tmp'[j]?.getD 0#32).toNat
        l ∈ fullRsnLits s rsn ∧ l < 2 * s.core.cur_vars ∧ l / 2 ≠ skip_var.toNat ∧
        s.core.mrk[l / 2]?.getD 0#8 = 0#8 ∧ 0 < (s.core.lvl[l / 2]?.getD 0#32).toNat ∧
        (s.core.lvl[l / 2]?.getD 0#32).toNat < s.core.cur_level ∧ mrk'[l / 2]?.getD 0#8 ≠ 0#8) →
      (∀ j1 j2, s.core.tmp_len ≤ j1 → j1 < j2 → j2 < tl' →
        (tmp'[j1]?.getD 0#32).toNat / 2 ≠ (tmp'[j2]?.getD 0#32).toNat / 2) →
      tc' - s.core.tmp_cnt = ((List.range s.core.cur_vars).filter fun w =>
        decide (s.core.mrk[w]?.getD 0#8 = 0#8) && decide (mrk'[w]?.getD 0#8 ≠ 0#8) &&
        decide ((s.core.lvl[w]?.getD 0#32).toNat = s.core.cur_level)).length →
      sc'.res_sz = s.scratch.res_sz + BitVec.ofNat 64 ((List.range s.core.cur_vars).filter fun w =>
        decide (s.core.mrk[w]?.getD 0#8 = 0#8) && decide (mrk'[w]?.getD 0#8 ≠ 0#8)).length →
      (ok = true → rsn ≠ 0xFFFFFFFF#32 ∧
        sc'.ant_sz = s.scratch.ant_sz + BitVec.ofNat 64 ((fullRsnLits s rsn).countP fun l =>
          decide (l / 2 < s.core.cur_vars ∧ 0 < (s.core.lvl[l / 2]?.getD 0#32).toNat ∧
            (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ s.core.cur_level)) ∧
        ∀ l ∈ fullRsnLits s rsn, l / 2 < s.core.cur_vars ∧ (l / 2 ≠ skip_var.toNat →
          (0 < (s.core.lvl[l / 2]?.getD 0#32).toNat → mrk'[l / 2]?.getD 0#8 ≠ 0#8) ∧
          (s.core.mrk[l / 2]?.getD 0#8 = 0#8 →
            (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ s.core.cur_level ∧
            (0 < (s.core.lvl[l / 2]?.getD 0#32).toNat →
              (s.core.lvl[l / 2]?.getD 0#32).toNat < s.core.cur_level →
              ∃ j, s.core.tmp_len ≤ j ∧ j < tl' ∧ (tmp'[j]?.getD 0#32).toNat / 2 = l / 2)))) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (ok, ()) m') :
    wp Γ Q X (Expr.group (sig := [[i32]])
      (fun Js => Blocks.cons (fun p_24 =>
        Expr.let_
          { sig := [i32, i32], code := OpCode.cmp CmpOp.ult i32 Ty.bool rfl,
            args := (Arg.var p_24.fst, Arg.var sz_bv, ()) } fun p_25 =>
          Expr.jnz (Arg.var p_25.fst)
            (Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var rsn, ()) }
                fun p_26 =>
              Expr.let_
                { sig := [i64, i64], code := OpCode.add i64,
                  args := (Arg.var p_26.fst, Arg.imm 3, ()) } fun p_27 =>
                Expr.let_
                  { sig := [i32], code := OpCode.zext 32 64,
                    args := (Arg.var p_24.fst, ()) } fun p_28 =>
                  Expr.let_
                    { sig := [i64, i64], code := OpCode.add i64,
                      args := (Arg.var p_27.fst, Arg.var p_28.fst, ()) } fun p_29 =>
                    Expr.let_
                      { sig := [i64, i64], code := OpCode.mul i64,
                        args := (Arg.var p_29.fst, Arg.imm 4, ()) } fun p_30 =>
                      Expr.let_
                        { sig := [i64, i64], code := OpCode.add i64,
                          args := (Arg.var pArena, Arg.var p_30.fst, ()) } fun p_31 =>
                        Expr.load i32 (Arg.var p_31.fst) fun ld =>
                          Expr.call (as := [i64, i32, i32]) (bs := [.bool]) "full_analyze_lit"
                              (Arg.var c.hdr, Arg.var ld, Arg.var skip_var, ()) fun p =>
                            Expr.jnz (Arg.var p.fst)
                              (Expr.let_
                                { sig := [i32, i32], code := OpCode.add i32,
                                  args := (Arg.var p_24.fst, Arg.imm 1, ()) } fun p =>
                                Expr.jump Js.fst (Arg.var p.fst, ()))
                              (Expr.ret (Arg.imm false, ())))
            (Expr.ret (Arg.imm true, ()))) Blocks.nil)
      (fun Js => Expr.jump Js.fst (Arg.imm 0, ()))) m1 := by
  subst hpArena hsz_bv
  let s1 : FullState := { s with core := { s.core with arena := arena1 }, scratch := sc1 }
  have har1_len := hlen1.core_ok.arena_len_arr; have har_len := hlen.core_ok.arena_len_arr
  have har_le := hlen.core_ok.arena_len_le
  let sz : Nat := fullArenaClauseSize s rsn.toNat
  have hsz_at : s.core.arena[(rsn.setWidth 64 + 2#64).toNat]'hsz_lt =
      s.core.arena[rsn.toNat + 2]'(by omega) := FullAnalyzeTactics.getElem_eq_of_idx hsz_idx
  have hsz_val : (s.core.arena[(rsn.setWidth 64 + 2#64).toNat]'hsz_lt).toNat = sz := by
    rw [hsz_at]; unfold sz fullArenaClauseSize fullArenaClauseSizeCore
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
  let antPred : Nat → Bool := fun l => decide (l / 2 < s.core.cur_vars ∧
    0 < (s.core.lvl[l / 2]?.getD 0#32).toNat ∧
    (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ s.core.cur_level)
  refine wp_loop_inv (fun (iv, ()) ml => ∃ i mrk' tmp' mcl' tc' tl' ant' res' ws1',
    i ≤ sz ∧ iv = BitVec.ofNat 32 i ∧
    mrk'.length = c.max_vars ∧ tmp'.length = c.max_vars ∧ ws1'.length = 2 * c.max_vars ∧
    mcl' ≤ c.max_vars ∧ s.core.tmp_len ≤ tl' ∧ tl' ≤ s.core.cur_vars ∧ s.core.tmp_cnt ≤ tc' ∧
    FullAnalyzeSpecs.AnaWorkInv c { s1 with
      core := { s1.core with
        mrk := mrk', tmp := tmp', tmp_cnt := tc', tmp_len := tl', min_clr_len := mcl' },
      scratch := { sc1 with work_stk1 := ws1', ant_sz := ant', res_sz := res' } } ∧
    S11RsnStepPre s (fullArenaClauseLits s rsn.toNat) skip_var mrk' tmp' tc' tl' res' ∧
    (∀ w < s.core.cur_vars, s.core.mrk[w]?.getD 0#8 = 0#8 → mrk'[w]?.getD 0#8 ≠ 0#8 →
      (s.core.lvl[w]?.getD 0#32).toNat < s.core.cur_level →
      ∃ j, s.core.tmp_len ≤ j ∧ j < tl' ∧ (tmp'[j]?.getD 0#32).toNat / 2 = w) ∧
    ant' = s.scratch.ant_sz +
      BitVec.ofNat 64 (((fullArenaClauseLits s rsn.toNat).take i).countP antPred) ∧
    (∀ k < i, let l := (s.core.arena[rsn.toNat + 3 + k]?.getD 0#32).toNat
      l / 2 < s.core.cur_vars ∧ (l / 2 ≠ skip_var.toNat →
        (0 < (s.core.lvl[l / 2]?.getD 0#32).toNat → mrk'[l / 2]?.getD 0#8 ≠ 0#8) ∧
        (s.core.mrk[l / 2]?.getD 0#8 = 0#8 → (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ s.core.cur_level
          ∧ (0 < (s.core.lvl[l / 2]?.getD 0#32).toNat →
            (s.core.lvl[l / 2]?.getD 0#32).toNat < s.core.cur_level →
            ∃ j, s.core.tmp_len ≤ j ∧ j < tl' ∧ (tmp'[j]?.getD 0#32).toNat / 2 = l / 2)))) ∧
    (FullMem c { s1 with
      core := { s1.core with
        mrk := mrk', tmp := tmp', tmp_cnt := tc', tmp_len := tl', min_clr_len := mcl' },
      scratch := { sc1 with work_stk1 := ws1', ant_sz := ant', res_sz := res' } } ⋆
      (m6ExtMem (m6ExtAddr c.hdr) ext1 ⋆ R)) ml)
    (fun (iv, ()) _ => sz - iv.toNat)
    (fun L hL => by
      c0_hsteps_nogrp
      have hwks : FullAnalyzeSpecs.AnaWorkInv c s1 := by
        obtain ⟨h1, h2, h3, h4⟩ := hwork
        refine ⟨h1, by simpa only [s1, hws1] using h2, by simpa only [s1, hws1] using h3,
          fun v hv hnz => let ⟨k, hk, heq⟩ := h4 v hv hnz
            ⟨heq ▸ (h3 k hk).1, k, hk, by simpa only [s1, hws1] using heq⟩⟩
      refine hL (0#32, ()) m1 ⟨0, s.core.mrk, s.core.tmp, s.core.min_clr_len, s.core.tmp_cnt,
        s.core.tmp_len, s.scratch.ant_sz, s.scratch.res_sz, s.scratch.work_stk1,
        Nat.zero_le _, rfl, hlen1.core_ok.mrk_len, hlen1.core_ok.tmp_len_arr,
        hlen.scratch_ok.work_stk1_len, hlen1.core_ok.min_clr_len_le, Nat.le_refl _, htl_cv,
        Nat.le_refl _, (by simpa only [s1, ← hant1, ← hres1, ← hws1] using hwks),
        ⟨fun _ _ _ => rfl, fun _ _ => rfl, fun _ _ h0 hnz => absurd h0 hnz,
          fun _ h1 h2 => by omega, fun _ _ _ h1 h2 => by omega,
          by rw [Nat.sub_self, s11_filter_zero]; intro _ _; simp,
          by rw [s11_filter_zero (fun _ _ => by simp)]; simp⟩,
        fun _ _ h0 hnz _ => absurd h0 hnz, by simp, fun _ hk => by omega, ?_⟩
      simpa only [s1, ← hant1, ← hres1, ← hws1] using hm1)
    (fun L (iv, ()) ml ⟨i, mrk', tmp', mcl', tc', tl', ant', res', ws1', hile, hiv_eq,
        hml_l, htl_l, hws_l, hmcl_le, htl_ge, htl_le, htc_ge, hwk', hpre, hnewlow, hant_l,
        hdone, hml⟩ hL => ?_)
  · subst hiv_eq
    have ⟨hmpres, htpres, hnewm, hnewt, hnd_t, hcnt, hres_l⟩ := hpre
    have hi32 : i < 2 ^ 32 := by omega
    have hi_mod : (BitVec.ofNat 32 i).toNat = i := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi32]
    c0_hsteps_nogrp
    · have hilt : i < sz := by
        have hlt_bv : (BitVec.ofNat 32 i).toNat < (s.core.arena[(rsn.setWidth 64 + 2#64).toNat]'(
            by rw [hsz_idx]; omega)).toNat := BitVec.lt_def.mp (by assumption)
        rw [hi_mod, hsz_val] at hlt_bv; exact hlt_bv
      have hidx_l : (rsn.setWidth 64 + 3 + (BitVec.ofNat 32 i).setWidth 64).toNat =
          rsn.toNat + 3 + i := by
        rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_setWidth]
        simp [Nat.mod_eq_of_lt (by omega : rsn.toNat < 2 ^ 64),
          Nat.mod_eq_of_lt (by omega : i < 2 ^ 32)]
        omega
      have hsz_core : sz = fullArenaClauseSizeCore s.core rsn.toNat := rfl
      have hidx_lt : (rsn.setWidth 64 + 3 + (BitVec.ofNat 32 i).setWidth 64).toNat <
          arena1.length := by rw [hidx_l, har1_len]; rw [hsz_core] at hilt; omega
      have htc_le_mv : tc' - s.core.tmp_cnt ≤ s.core.cur_vars := by
        rw [hcnt]; exact Nat.le_trans (List.length_filter_le _ _) (by simp)
      let st : FullState := { s1 with
        core := { s1.core with
          mrk := mrk', tmp := tmp', tmp_cnt := tc', tmp_len := tl', min_clr_len := mcl' },
        scratch := { sc1 with work_stk1 := ws1', ant_sz := ant', res_sz := res' } }
      have hst_len : st.LengthsOk c := ⟨{ hlen1.core_ok with
          mrk_len := hml_l, tmp_len_arr := htl_l,
          tmp_len_le := (by dsimp [st]; omega), min_clr_len_le := hmcl_le },
        { hlen1.scratch_ok with work_stk1_len := hws_l }⟩
      let l_bv : BitVec 32 := arena1[rsn.toNat + 3 + i]'(by omega)
      have hl_eq : l_bv = s.core.arena[rsn.toNat + 3 + i]'(by omega) := by
        have h1 : arena1[rsn.toNat + 3 + i]? = some l_bv := List.getElem?_eq_getElem (by omega)
        rw [har1_eq i hilt, List.getElem?_eq_getElem (by omega)] at h1
        exact (Option.some.inj h1).symm
      have hl_get : (s.core.arena[rsn.toNat + 3 + i]?.getD 0#32).toNat = l_bv.toNat := by
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some, ← hl_eq]
      have hl_mem : l_bv.toNat ∈ fullArenaClauseLits s rsn.toNat :=
        (mem_fullArenaClauseLitsCore_iff (by omega)).mpr ⟨i, hilt, by rw [← hl_eq]⟩
      c0_hsteps_nogrp; dsimp only [st, s1]
      rw [FullAnalyzeTactics.getElem_eq_of_idx (hi := hidx_lt) (hj := by omega) hidx_l]
      c0_call hLit
      refine ⟨c, st, m6ExtMem (m6ExtAddr c.hdr) ext1 ⋆ R, rfl, hst_len, hcur32, htl_le,
        by dsimp [st]; omega,
        ⟨hwk'.1, hwk'.2.1, hwk'.2.2.1, fun v hv hnz => (hwk'.2.2.2 v hv hnz).2⟩, hml,
        fun ok2 mrk2 tmp2 tc2 tl2 mcl2 ws2 ant2 res2 m2 hlen2 hwk2 htl2_ge htl2_inc htl2_le
          htc2_ge hant2 hres2 htc2_eq hmpres2 htpres2 hnewm2 hnewt2 hok2 hm2 => ?_⟩
      dsimp only [st] at *
      have hwk2_ana : FullAnalyzeSpecs.AnaWorkInv c { s1 with
          core := { s1.core with
            mrk := mrk2, tmp := tmp2, tmp_cnt := tc2, tmp_len := tl2, min_clr_len := mcl2 },
          scratch := { sc1 with work_stk1 := ws2, ant_sz := ant2, res_sz := res2 } } :=
        ⟨hwk2.1, hwk2.2.1, hwk2.2.2.1, fun v hv hnz => let ⟨k, hk, heq⟩ := hwk2.2.2.2 v hv hnz
          ⟨heq ▸ (hwk2.2.2.1 k hk).1, k, hk, heq⟩⟩
      have hpre2 := s11_rsn_comb_step htl_ge htl2_ge htl2_inc htc_ge hl_mem hpre
        (fun w hw => hmpres2 w (Nat.lt_of_lt_of_le hw hcv_le)) htpres2 (fun w hw h0 hnz =>
          let h := hnewm2 w (Nat.lt_of_lt_of_le hw hcv_le) h0 hnz; ⟨h.1, h.2.2.1, h.2.2.2⟩)
        hnewt2 hres2 htc2_eq
      cases ok2 with
      | false =>
        c0_hsteps_nogrp; obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hpre2
        have h1c : ∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 ≠ 0#8 →
            mrk2[v]?.getD 0#8 = s.core.mrk[v]?.getD 0#8 := fun v hv hnz =>
          h1 v (let ⟨k, hk, heq⟩ := hwork.2.2.2 v hv hnz; heq ▸ (hwork.2.2.1 k hk).1) hnz
        have h3c : ∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 = 0#8 → mrk2[v]?.getD 0#8 ≠ 0#8 →
            ∃ l ∈ fullRsnLits s rsn, l / 2 = v ∧ v < s.core.cur_vars ∧ v ≠ skip_var.toNat ∧
              0 < (s.core.lvl[v]?.getD 0#32).toNat ∧
              (s.core.lvl[v]?.getD 0#32).toNat ≤ s.core.cur_level := fun v hv h0 hnz =>
          let hvlt := (hwk2_ana.2.2.2 v hv hnz).1; let ⟨l, hl, hr⟩ := h3 v hvlt h0 hnz
          ⟨l, (FullAnalyzeHelpers.mem_fullRsnLits_large hne hlarge).mpr hl, hr.1, hvlt, hr.2⟩
        exact hQ false mrk2 tmp2 tc2 tl2 mcl2 arena1
          { sc1 with work_stk1 := ws2, ant_sz := ant2, res_sz := res2 } ext1 m2
          hext1 hwb1 hlen2
          { hw1 with
            arena := { hw1.arena with len_ok := hw1.arena.len_ok },
            watches := hw1.watches.with_wstk rfl rfl rfl rfl rfl fun _ hr => hr }
          hwk2 hexp1 hws2 (Nat.le_trans htl_ge htl2_ge) htl2_le (Nat.le_trans htc_ge htc2_ge)
          hrefs1 hcl1 h1c h2 h3c (fun j hj1 hj2 => let ⟨ha, hr⟩ := h4 j hj1 hj2
            ⟨(FullAnalyzeHelpers.mem_fullRsnLits_large hne hlarge).mpr ha, hr⟩)
          h5 h6 h7 (fun hc => by cases hc) (fullM6HdrMem_unfocus hm2)
      | true =>
        c0_hsteps_nogrp
        · obtain ⟨hvlt, hrest⟩ := hok2 rfl
          have htake1 : (fullArenaClauseLits s rsn.toNat).take (i + 1) =
              (fullArenaClauseLits s rsn.toNat).take i ++ [l_bv.toNat] := by
            have hlen_l : (fullArenaClauseLits s rsn.toNat).length = sz := by
              simp [fullArenaClauseLits, fullArenaClauseLitsCore, sz, fullArenaClauseSize]; omega
            rw [List.take_add_one, List.getElem?_eq_getElem (by omega), Option.toList_some]
            congr 2; unfold fullArenaClauseLits fullArenaClauseLitsCore
            simp [List.getElem_map, List.getElem_take, List.getElem_drop, ← hl_eq]
          have hant2_eq : ant2 = s.scratch.ant_sz + BitVec.ofNat 64
              (((fullArenaClauseLits s rsn.toNat).take (i + 1)).countP antPred) := by
            rw [hant2, hant_l, htake1, List.countP_append, List.countP_cons, List.countP_nil,
              Nat.zero_add, BitVec.add_assoc, BitVec.ofNat_add]
            exact congrArg (s.scratch.ant_sz + ·) (congrArg _
              (s11_bv64_ite_iff (by simp only [antPred, decide_eq_true_eq]; rfl)))
          rw [show BitVec.ofNat 32 i + 1 = BitVec.ofNat 32 (i + 1) from
            BitVec.eq_of_toNat_eq (by simp [BitVec.toNat_add, hi_mod])]
          refine hL (BitVec.ofNat 32 (i + 1), ()) m2
            (by rw [bv32_ofNat_toNat (by omega), hi_mod]; omega)
            ⟨i + 1, mrk2, tmp2, mcl2, tc2, tl2, ant2, res2, ws2, by omega, rfl,
              hlen2.core_ok.mrk_len, hlen2.core_ok.tmp_len_arr, hlen2.scratch_ok.work_stk1_len,
              hlen2.core_ok.min_clr_len_le, by omega, htl2_le, by omega, hwk2_ana, hpre2, ?_,
              hant2_eq, ?_, hm2⟩
          · intro w hw_lt hs0 hmnz2 hltcl
            by_cases hm1_w : mrk'[w]?.getD 0#8 = 0#8
            · obtain ⟨rfl, _, hne', hpos, _⟩ :=
                hnewm2 w (Nat.lt_of_lt_of_le hw_lt hcv_le) hm1_w hmnz2
              obtain ⟨_, htget⟩ := ((hrest hne').2 hm1_w).2.2 hpos hltcl
              exact ⟨tl', htl_ge, by omega, by rw [htget]; rfl⟩
            · obtain ⟨j, hj1, hj2, hjeq⟩ := hnewlow w hw_lt hs0 hm1_w hltcl
              exact ⟨j, hj1, by omega, by rw [htpres2 j hj2]; exact hjeq⟩
          · intro k hk; by_cases hki : k = i
            · subst hki; rw [hl_get]; refine ⟨hvlt, fun hne' => ?_⟩
              obtain ⟨hpos_m, hm1_r⟩ := hrest hne'; refine ⟨hpos_m, fun hs0 => ?_⟩
              by_cases hm1_w : mrk'[l_bv.toNat / 2]?.getD 0#8 = 0#8
              · obtain ⟨hle, _, hlow⟩ := hm1_r hm1_w
                exact ⟨hle, fun hpos hltcl => let ⟨_, htget⟩ := hlow hpos hltcl
                  ⟨tl', htl_ge, by omega, by rw [htget]; rfl⟩⟩
              · obtain ⟨_, _, _, _, _, hle⟩ := hnewm _ hvlt hs0 hm1_w
                exact ⟨hle, fun _ hltcl =>
                  let ⟨j, hj1, hj2, hjeq⟩ := hnewlow _ hvlt hs0 hm1_w hltcl
                  ⟨j, hj1, by omega, by rw [htpres2 j hj2]; exact hjeq⟩⟩
            · obtain ⟨hkv, hkrest⟩ := hdone k (by omega)
              refine ⟨hkv, fun hne' => ?_⟩; obtain ⟨h1, h2⟩ := hkrest hne'
              refine ⟨fun hp => by
                rw [hmpres2 _ (Nat.lt_of_lt_of_le hkv hcv_le) (h1 hp)]; exact h1 hp, fun hs0 => ?_⟩
              obtain ⟨hle, hlow⟩ := h2 hs0
              exact ⟨hle, fun hpos hltcl => let ⟨j, hj1, hj2, hjeq⟩ := hlow hpos hltcl
                ⟨j, hj1, by omega, by rw [htpres2 j hj2]; exact hjeq⟩⟩
        · exact False.elim (Bool.noConfusion (by assumption : true = false))
    · c0_hsteps_nogrp
      have hieq : i = sz := by
        have hnot : ¬ BitVec.ofNat 32 i <
            s.core.arena[(rsn.setWidth 64 + 2#64).toNat]'(by rw [hsz_idx]; omega) := by assumption
        have hge_bv : ¬ (BitVec.ofNat 32 i).toNat <
            (s.core.arena[(rsn.setWidth 64 + 2#64).toNat]'(by rw [hsz_idx]; omega)).toNat :=
          fun h => hnot (BitVec.lt_def.mpr h)
        rw [hi_mod, hsz_val] at hge_bv; omega
      have h1c : ∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 ≠ 0#8 →
          mrk'[v]?.getD 0#8 = s.core.mrk[v]?.getD 0#8 := fun v hv hnz =>
        hmpres v (let ⟨k, hk, heq⟩ := hwork.2.2.2 v hv hnz; heq ▸ (hwork.2.2.1 k hk).1) hnz
      have h3c : ∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 = 0#8 → mrk'[v]?.getD 0#8 ≠ 0#8 →
          ∃ l ∈ fullRsnLits s rsn, l / 2 = v ∧ v < s.core.cur_vars ∧ v ≠ skip_var.toNat ∧
            0 < (s.core.lvl[v]?.getD 0#32).toNat ∧
            (s.core.lvl[v]?.getD 0#32).toNat ≤ s.core.cur_level := fun v hv h0 hnz =>
        let hvlt := (hwk'.2.2.2 v hv hnz).1; let ⟨l, hl, hr⟩ := hnewm v hvlt h0 hnz
        ⟨l, (FullAnalyzeHelpers.mem_fullRsnLits_large hne hlarge).mpr hl, hr.1, hvlt, hr.2⟩
      refine hQ true mrk' tmp' tc' tl' mcl' arena1
        { sc1 with work_stk1 := ws1', ant_sz := ant', res_sz := res' } ext1 ml hext1 hwb1
        ⟨{ hlen1.core_ok with
            mrk_len := hml_l, tmp_len_arr := htl_l,
            tmp_len_le := (by dsimp; omega), min_clr_len_le := hmcl_le },
         { hlen1.scratch_ok with work_stk1_len := hws_l }⟩
        { hw1 with
          arena := { hw1.arena with len_ok := hw1.arena.len_ok },
          watches := hw1.watches.with_wstk rfl rfl rfl rfl rfl fun _ hr => hr }
        ⟨hwk'.1, hwk'.2.1, hwk'.2.2.1, fun v hv hnz => (hwk'.2.2.2 v hv hnz).2⟩
        hexp1 hws2 htl_ge htl_le htc_ge hrefs1 hcl1 h1c htpres h3c
        (fun j hj1 hj2 => let ⟨ha, hr⟩ := hnewt j hj1 hj2
          ⟨(FullAnalyzeHelpers.mem_fullRsnLits_large hne hlarge).mpr ha, hr⟩)
        hnd_t hcnt hres_l (fun _ => ?_) (fullM6HdrMem_unfocus hml)
      refine ⟨hne, ?_, fun l hl => ?_⟩
      · have hlen_l : (fullArenaClauseLits s rsn.toNat).length = sz := by
          simp only [fullArenaClauseLits, fullArenaClauseLitsCore, sz, fullArenaClauseSize,
            List.length_map, List.length_take, List.length_drop]; omega
        rw [hant_l, hieq, List.take_of_length_le (Nat.le_of_eq hlen_l)]
        simp [fullRsnLits, hne, hlarge, antPred]
      · simp only [fullRsnLits, hne, hlarge, ↓reduceIte] at hl
        obtain ⟨k, hk, hget⟩ := (mem_fullArenaClauseLitsCore_iff (by omega)).mp hl
        have hkget : (s.core.arena[rsn.toNat + 3 + k]?.getD 0#32).toNat = l := by
          rw [List.getElem?_eq_getElem (by omega), Option.getD_some, hget]
        have hd := hdone k (by rw [hieq]; exact hk); rwa [hkget] at hd

private def s11GlueStepExpr {ret : List Ty} (pLvl cv64 var64 lo best : Val i64) (k : Val i32)
    (Li : Cont [i64, i32]) : Expr Val Cont ret :=
  Expr.group (sig := [[i64]]) (fun _Js => Blocks.cons (fun p =>
      Expr.let_ { sig := [i32, i32], code := OpCode.add i32, args := (Arg.var k, Arg.imm 1, ()) }
        fun p_38 => Expr.jump Li (Arg.var p.fst, Arg.var p_38.fst, ())) Blocks.nil)
    fun Js => Expr.let_
      { sig := [i64, i64], code := OpCode.cmp CmpOp.ult i64 Ty.bool rfl,
        args := (Arg.var var64, Arg.var cv64, ()) } fun p_38 =>
    Expr.jnz (Arg.var p_38.fst)
      (Expr.let_
        { sig := [i64, i64], code := OpCode.mul i64, args := (Arg.var var64, Arg.imm 4, ()) }
          fun p =>
      Expr.let_
        { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var pLvl, Arg.var p.fst, ()) }
          fun p =>
      Expr.load i32 (Arg.var p.fst) fun ld =>
      Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var ld, ()) } fun p =>
      Expr.group (sig := [[i64]])
        (fun _Js => Blocks.cons (fun p => Expr.jump Js.fst (Arg.var p.fst, ())) Blocks.nil)
        fun Js => Expr.let_
          { sig := [i64, i64], code := OpCode.cmp CmpOp.uge i64 Ty.bool rfl,
            args := (Arg.var p.fst, Arg.var lo, ()) } fun p_39 =>
        Expr.jnz (Arg.var p_39.fst)
          (Expr.let_
            { sig := [i64, i64], code := OpCode.cmp CmpOp.ult i64 Ty.bool rfl,
              args := (Arg.var p.fst, Arg.var best, ()) } fun p_40 =>
          Expr.jnz (Arg.var p_40.fst) (Expr.jump Js.fst (Arg.var p.fst, ()))
            (Expr.jump Js.fst (Arg.var best, ())))
          (Expr.jump Js.fst (Arg.var best, ())))
      (Expr.jump Js.fst (Arg.var best, ()))

private theorem s11_rsn_glue_step {Γ : Env} {c : FullCfg} {ext : List (BitVec 64)}
    {s : FullState} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [.bool]} {X : XPost}
    {k : Val i32} {var64 pLvl cv64 lo best : Val i64} {Li : Cont [i64, i32]}
    (hpLvl : pLvl = c.pLevel) (hcv64 : cv64 = BitVec.ofNat 64 s.core.cur_vars)
    (hlen : s.LengthsOk c) (hmf : (FullMem c s ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R)) m)
    (hLi : ∀ best' : Val i64, Li (best', k + 1#32, ()) m) :
    wp Γ Q X (s11GlueStepExpr pLvl cv64 var64 lo best k Li) m := by
  subst hpLvl hcv64; unfold s11GlueStepExpr
  refine wp_join_group (ts := [i64]) (fun _ ml => ml = m) ?_ ?_
  · rintro _ ⟨best', ⟨⟩⟩ ml hml; cases hml; c0_hsteps_nogrp; exact hLi best'
  · intro Jb hJb; c0_hsteps_nogrp
    · have hkv_lt : var64.toNat < s.core.lvl.length := by
        have hcv_le := hlen.core_ok.cur_vars_le; have hmax := fullInv_max_vars_lt32 c
        have hlt : var64.toNat < s.core.cur_vars % 2 ^ 64 := by assumption
        rw [Nat.mod_eq_of_lt (by omega)] at hlt; rw [hlen.core_ok.lvl_len]; omega
      c0_hsteps_nogrp
      refine wp_join_group (ts := [i64]) (fun _ ml => ml = m)
        (fun _ ⟨best', ⟨⟩⟩ ml hml => by cases hml; exact hJb _ m rfl)
        (fun Jb2 hJb2 => by c0_hsteps_nogrp <;> exact hJb2 _ m rfl)
    · exact hJb _ m rfl

private def S11GluePred (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (cut : Nat)
    (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop) (rsn : Val i32)
    (p : Tup Val [i32, i64]) (m0 : Mem 64) : Prop :=
  ∃ arena0,
    let s0 : FullState := { s with core := { s.core with arena := arena0 } }
    arena0[rsn.toNat]? = some p.1 ∧ FullWitnessCutInv c F0 F_cur cut s0.core ∧
    s0.LengthsOk c ∧ fullArenaClauseRefs s0 = fullArenaClauseRefs s ∧
    (∀ r ∈ fullArenaClauseRefs s, fullArenaClauseSize s0 r = fullArenaClauseSize s r ∧
      fullArenaClauseGarb s0 r = fullArenaClauseGarb s r ∧
      fullArenaClauseLits s0 r = fullArenaClauseLits s r) ∧
    (∀ k < fullArenaClauseSize s rsn.toNat,
      arena0[rsn.toNat + 3 + k]? = s.core.arena[rsn.toNat + 3 + k]?) ∧
    (FullMem c s0 ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R)) m0

private theorem s11_rsn_glue_lo {Γ : Env} {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {ext : List (BitVec 64)} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post [.bool]} {X : XPost} {rsn ld_2 sz_bv : Val i32}
    {pArena pLvl cv64 glue lim : Val i64} {Jg : Cont [i32, i64]}
    (hpArena : pArena = c.pArena) (hpLvl : pLvl = c.pLevel)
    (hcv64 : cv64 = BitVec.ofNat 64 s.core.cur_vars)
    (hlen : s.LengthsOk c) (hw : FullWitnessCutInv c F0 F_cur cut s.core)
    (href : rsn.toNat ∈ fullArenaClauseRefs s) (hrsn_lt : rsn.toNat < s.core.arena.length)
    (hrsn_z_lt : (rsn.setWidth 64).toNat < s.core.arena.length)
    (hsz_lt : rsn.toNat + 2 < s.core.arena.length)
    (hsz_idx : (rsn.setWidth 64 + 2#64).toNat = rsn.toNat + 2)
    (hld2 : ld_2 = s.core.arena[(rsn.setWidth 64).toNat]'hrsn_z_lt)
    (hglue : glue = (ld_2 &&& 524287#32).setWidth 64)
    (hsz_bv : sz_bv = s.core.arena[(rsn.setWidth 64 + 2#64).toNat]'(by rw [hsz_idx]; exact hsz_lt))
    (hsz_get : (s.core.arena[rsn.toNat + 2]'hsz_lt).toNat = fullArenaClauseSize s rsn.toNat)
    (hrsn_get : s.core.arena[rsn.toNat]? = some ld_2)
    (hmf : (FullMem c s ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R)) m) (hlim : lim.toNat < 2 ^ 19)
    (hJg : ∀ (xs : Tup Val [i32, i64]) (m0 : Mem 64),
      S11GluePred c F0 F_cur cut ext s R rsn xs m0 → Jg xs m0) :
    wp Γ Q X (Expr.group (sig := [[i64, i64, .bool]]) (fun Js_3 => Blocks.cons (fun p_33 =>
      Expr.group (sig := [[]]) (fun _Js_4 => Blocks.cons (fun _p_34 =>
        Expr.group (sig := [[i32, i64]])
          (fun _Js_5 => Blocks.cons (fun p => Expr.jump Jg (Arg.var p.fst, Arg.var p.snd.fst, ()))
            Blocks.nil)
          fun Js => Expr.jnz (Arg.var p_33.snd.snd.fst)
            (Expr.jump Js.fst (Arg.var ld_2, Arg.var glue, ()))
            (Expr.let_
              { sig := [i64, i64], code := OpCode.cmp CmpOp.ugt i64 Ty.bool rfl,
                args := (Arg.var p_33.fst, Arg.imm 0, ()) } fun p_35 =>
            Expr.jnz (Arg.var p_35.fst)
              (Expr.let_
                { sig := [i64, i64], code := OpCode.cmp CmpOp.ult i64 Ty.bool rfl,
                  args := (Arg.var p_33.fst, Arg.var glue, ()) } fun p_36 =>
              Expr.jnz (Arg.var p_36.fst)
                (Expr.let_ { sig := [i32], code := OpCode.not i32, args := (Arg.imm 524287, ()) }
                  fun p_37 =>
                Expr.let_
                  { sig := [i32, i32], code := OpCode.and i32,
                    args := (Arg.var ld_2, Arg.var p_37.fst, ()) } fun p_38 =>
                Expr.let_
                  { sig := [i64], code := OpCode.trunc 64 32,
                    args := (Arg.var p_33.fst, ()) } fun p_39 =>
                Expr.let_
                  { sig := [i32, i32], code := OpCode.or i32,
                    args := (Arg.var p_38.fst, Arg.var p_39.fst, ()) } fun p_40 =>
                Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var rsn, ()) }
                  fun p =>
                Expr.let_
                  { sig := [i64, i64], code := OpCode.mul i64,
                    args := (Arg.var p.fst, Arg.imm 4, ()) } fun p =>
                Expr.let_
                  { sig := [i64, i64], code := OpCode.add i64,
                    args := (Arg.var pArena, Arg.var p.fst, ()) } fun p =>
                Expr.store (t := i32) (Arg.var p_40.fst) (Arg.var p.fst)
                  (Expr.jump Js.fst (Arg.var p_40.fst, Arg.var p_33.fst, ())))
                (Expr.jump Js.fst (Arg.var ld_2, Arg.var glue, ())))
              (Expr.jump Js.fst (Arg.var ld_2, Arg.var glue, ())))) Blocks.nil)
        fun Js => Expr.jnz (Arg.var p_33.snd.snd.fst)
          (Expr.let_
            { sig := [i64, i64], code := OpCode.cmp CmpOp.ule i64 Ty.bool rfl,
              args := (Arg.var p_33.fst, Arg.var lim, ()) } fun p_34 =>
          Expr.jnz (Arg.var p_34.fst)
            (Expr.group (sig := [[i64, i32]]) (fun Li => Blocks.cons (fun p_35 =>
              Expr.let_
                { sig := [i32, i32], code := OpCode.cmp CmpOp.ult i32 Ty.bool rfl,
                  args := (Arg.var p_35.snd.fst, Arg.var sz_bv, ()) } fun p_36 =>
              Expr.jnz (Arg.var p_36.fst)
                (Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var rsn, ()) }
                  fun p_r =>
                Expr.let_
                  { sig := [i64, i64], code := OpCode.add i64,
                    args := (Arg.var p_r.fst, Arg.imm 3, ()) } fun p =>
                Expr.let_
                  { sig := [i32], code := OpCode.zext 32 64,
                    args := (Arg.var p_35.snd.fst, ()) } fun p_37 =>
                Expr.let_
                  { sig := [i64, i64], code := OpCode.add i64,
                    args := (Arg.var p.fst, Arg.var p_37.fst, ()) } fun p =>
                Expr.let_
                  { sig := [i64, i64], code := OpCode.mul i64,
                    args := (Arg.var p.fst, Arg.imm 4, ()) } fun p =>
                Expr.let_
                  { sig := [i64, i64], code := OpCode.add i64,
                    args := (Arg.var pArena, Arg.var p.fst, ()) } fun p =>
                Expr.load i32 (Arg.var p.fst) fun ld =>
                Expr.let_
                  { sig := [i32, i32], code := OpCode.lshr i32,
                    args := (Arg.var ld, Arg.imm 1, ()) } fun p =>
                Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var p.fst, ()) }
                  fun p =>
                    s11GlueStepExpr pLvl cv64 p.fst p_33.snd.fst p_35.fst p_35.snd.fst Li.fst)
                (Expr.group (sig := [[i64, i64, .bool]]) (fun _Js => Blocks.cons (fun p =>
                  Expr.jump Js_3.fst (Arg.var p.fst, Arg.var p.snd.fst, Arg.var p.snd.snd.fst, ()))
                  Blocks.nil) fun Js => Expr.let_
                  { sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64 Ty.bool rfl,
                    args := (Arg.var p_35.fst, Arg.imm 0xFFFFFFFFFFFFFFFF, ()) } fun p =>
                Expr.jnz (Arg.var p.fst)
                  (Expr.jump Js.fst (Arg.var p_33.fst, Arg.var p_33.snd.fst, Arg.imm false, ()))
                  (Expr.let_
                    { sig := [i64, i64], code := OpCode.add i64,
                      args := (Arg.var p_33.fst, Arg.imm 1, ()) } fun p =>
                  Expr.let_
                    { sig := [i64, i64], code := OpCode.add i64,
                      args := (Arg.var p_35.fst, Arg.imm 1, ()) } fun p_37 => Expr.jump Js.fst
                    (Arg.var p.fst, Arg.var p_37.fst, Arg.var p_33.snd.snd.fst, ()))))
              Blocks.nil) fun Li => Expr.jump Li.fst (Arg.imm 0xFFFFFFFFFFFFFFFF, Arg.imm 0, ()))
            (Expr.jump Js.fst ()))
          (Expr.jump Js.fst ())) Blocks.nil)
      fun Lo => Expr.jump Lo.fst (Arg.imm 0, Arg.imm 0, Arg.imm true, ())) m := by
  obtain ⟨_, _, hbd, hbd_le, _⟩ := hw.arena.refs_wf rsn.toNat href
  have har_len := hlen.core_ok.arena_len_arr; have har_le := hlen.core_ok.arena_len_le
  have hhdr_get : s.core.arena[rsn.toNat]'hrsn_lt = fullArenaHdrCore s.core rsn.toNat := by
    unfold fullArenaHdrCore; rw [List.getElem?_eq_getElem hrsn_lt, Option.getD_some]
  subst hpArena hpLvl hcv64 hld2 hglue hsz_bv
  have hg_lt : (fullArenaHdrCore s.core rsn.toNat &&& 0x7FFFF#32).toNat < 2 ^ 19 :=
    Nat.lt_of_le_of_lt (bv32_and_le_right _ _) (by decide)
  have hgl_z : ((fullArenaHdrCore s.core rsn.toNat &&& 0x7FFFF#32).setWidth 64).toNat =
      (fullArenaHdrCore s.core rsn.toNat &&& 0x7FFFF#32).toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans hg_lt (by decide))]
  have hhdr' : s.core.arena[(rsn.setWidth 64).toNat]'hrsn_z_lt =
      fullArenaHdrCore s.core rsn.toNat := by simpa only [bv_c0_zext32_64] using hhdr_get
  refine wp_loop_inv (fun (ng, lo, more, ()) ml => ml = m ∧ ng.toNat ≤ lim.toNat + 1)
    (fun (ng, _, more, ()) _ => (if more then 1 else 0) + (lim.toNat + 1 - ng.toNat))
    (fun Lo hLo => by c0_hsteps_nogrp; exact hLo (0#64, 0#64, true, ()) m ⟨rfl, Nat.zero_le _⟩)
    (fun Lo (ng, lo, more, ()) ml ⟨hml, hng_le⟩ hLo => ?_)
  cases hml
  refine wp_join_group (ts := []) (fun (_ : Tup Val []) m_ex => m_ex = m) ?_ ?_
  · rintro _ _ m_ex hm_ex; cases hm_ex; c0_hsteps_nogrp
    refine wp_join_group (ts := [i32, i64]) (S11GluePred c F0 F_cur cut ext s R rsn)
        (fun _ xs m0 h => hJg xs m0 h) ?_
    · intro Jg2 hJg2; c0_hsteps_nogrp
      all_goals try exact hJg2 (_, _, ()) m ⟨s.core.arena, hrsn_get, hw, hlen, rfl,
        fun _ _ => ⟨rfl, rfl, rfl⟩, fun _ _ => rfl, hmf⟩
      · have hng_c : ng.toNat < ((s.core.arena[(rsn.setWidth 64).toNat]'hrsn_z_lt &&&
            524287#32).setWidth 64).toNat := BitVec.lt_def.mp (by assumption)
        have hng_lt_g : (ng.setWidth 32).toNat < 2 ^ 19 := by
          rw [hhdr', hgl_z] at hng_c; rw [BitVec.toNat_setWidth]; omega
        have hup := s11_hdrBitsUpdate_cut hlen.core_ok hw href
          (fun x => (x &&& 0xFFF80000#32) ||| ng.setWidth 32)
          s.core.arena_garbage s.core.num_irred s.core.num_redundant
          (s11_bv32_glue_bit (b := 19) _ _ _ (by decide) (by decide) (by decide) hng_lt_g)
          (s11_bv32_glue_bit (b := 23) _ _ _ (by decide) (by decide) (by decide) hng_lt_g)
        let arena0 := s.core.arena.set rsn.toNat
          ((fullArenaHdrCore s.core rsn.toNat &&& 0xFFF80000#32) ||| ng.setWidth 32)
        have hm0' : (FullMem c { s with core := { s.core with arena := arena0 } } ⋆
            (m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R)) m := by
          have hm_rw : s.core.arena.set (rsn.setWidth 64).toNat
              ((s.core.arena[(rsn.setWidth 64).toNat]'hrsn_z_lt &&& 4294443008#32) |||
                ng.setWidth 32) = arena0 := by
            dsimp only [arena0]; rw [hhdr', bv_c0_zext32_64]
          rw [← hm_rw]; exact hm
        have hset : arena0[rsn.toNat]? = some
            ((s.core.arena[(rsn.setWidth 64).toNat]'hrsn_z_lt &&& ~~~524287#32) |||
              ng.setWidth 32) := by
          dsimp only [arena0]; rw [hhdr']; exact List.getElem?_set_self hrsn_lt
        exact hJg2 (_, ng, ()) _ ⟨arena0, hset, hup.1,
          ⟨{ hlen.core_ok with arena_len_arr := by simp [arena0, har_len] }, hlen.scratch_ok⟩,
          hup.2.1, hup.2.2, fun k _ => List.getElem?_set_ne (by omega), hm0'⟩
  · intro Jex hJex; c0_hsteps_nogrp
    · have hng_le' : ng.toNat ≤ lim.toNat := by bv_omega
      let sz : Nat := fullArenaClauseSize s rsn.toNat
      refine wp_loop_inv (fun (best, k, ()) ml => ml = m ∧ k.toNat ≤ sz)
        (fun (_, k, ()) _ => sz - k.toNat)
        (fun Li hLi => by
          c0_hsteps_nogrp; exact hLi (0xFFFFFFFFFFFFFFFF#64, 0#32, ()) m ⟨rfl, by simp⟩)
        (fun Li (best, k, ()) ml ⟨hkl, hkle⟩ hLi => ?_)
      · cases hkl; c0_hsteps_nogrp
        · have hk_lt : k.toNat < sz := by
            have h : k.toNat < (s.core.arena[(rsn.setWidth 64 + 2#64).toNat]'(by
                rw [hsz_idx]; exact hsz_lt)).toNat := BitVec.lt_def.mp ‹_›
            rwa [FullAnalyzeTactics.getElem_eq_of_idx hsz_idx, hsz_get] at h
          have hk1 : (k + 1#32).toNat = k.toNat + 1 := by bv_omega
          have har_k_lt : (rsn.setWidth 64 + 3#64 + k.setWidth 64).toNat < s.core.arena.length := by
            have h3 : (rsn.setWidth 64 + 3#64).toNat = rsn.toNat + 3 := by bv_omega
            rw [BitVec.toNat_add, h3, BitVec.toNat_setWidth,
              Nat.mod_eq_of_lt (by omega : k.toNat < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]
            have hk_lt_core : k.toNat < fullArenaClauseSizeCore s.core rsn.toNat := hk_lt; omega
          c0_hsteps_nogrp
          exact s11_rsn_glue_step rfl rfl hlen hmf fun best' =>
            hLi (best', k + 1#32, ()) m (by dsimp only; rw [hk1]; omega) ⟨rfl, by rw [hk1]; omega⟩
        · refine wp_join_group (ts := [i64, i64, .bool]) (fun (p : Tup Val [i64, i64, .bool]) ml =>
              ml = m ∧ p.1.toNat ≤ lim.toNat + 1 ∧
              (if p.2.2.1 then 1 else 0) + (lim.toNat + 1 - p.1.toNat) <
                (if more then 1 else 0) + (lim.toNat + 1 - ng.toNat)) ?_ ?_
          · rintro _ ⟨ng', lo', more', ⟨⟩⟩ ml ⟨hml, hle', hlt'⟩
            cases hml; c0_hsteps_nogrp; exact hLo (ng', lo', more', ()) m hlt' ⟨rfl, hle'⟩
          · intro Jm hJm; c0_hsteps_nogrp
            · have hm_eq : more = true := by assumption
              subst hm_eq; exact hJm (ng, lo, false, ()) m ⟨rfl, hng_le, by simp⟩
            · have hm_eq : more = true := by assumption
              subst hm_eq; have hng1 : (ng + 1#64).toNat = ng.toNat + 1 := by bv_omega
              exact hJm (ng + 1#64, best + 1#64, true, ()) m
                ⟨rfl, by rw [hng1]; omega, by simp [hng1]; omega⟩
    all_goals exact hJex () m rfl

end AnalyzeRsnStep11Helpers

/-- Parametric `Func.wp` proof for `fidStep11AnalyzeRsnM6HdrFn` (`full_analyze_rsn_m6_hdr`,
guarding `m6_hdr_record_used` with `h->probing == 0ULL`) against
`FullM6Orch.m6AnalyzeRsnHdrSpec`. -/
theorem full_analyze_rsn_m6_hdr_step11_wp (Γ : Env)
    (hLit : ∀ a m Q X, Full.fullAnalyzeLitSpec a m Q X →
      Γ "full_analyze_lit" [i64, i32, i32] [.bool] a m Q X)
    (hRec : ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
      Γ "m6_hdr_record_used" [i64, i64] [] a m Q X) :
    ∀ a m Q X, FullM6Orch.m6AnalyzeRsnHdrSpec a m Q X →
      Func.wp Γ fidStep11AnalyzeRsnM6HdrFn.body a m Q X := by
  rintro ⟨h, rsn, skip_var, ⟨⟩⟩ m Q X hspec
  obtain ⟨c, F0, F_cur, cut, ext, s, R, rfl, hcfg, hext, hlen, hw, hwork, htl_cv, htc_fit,
      hrsn_ref, hm, hQ⟩ := FullM6Orch.m6AnalyzeRsnHdrSpec_elim hspec
  have hmax32 := fullInv_max_vars_lt32 c; have hcv_le := hlen.core_ok.cur_vars_le
  have har_len := hlen.core_ok.arena_len_arr; have har_le := hlen.core_ok.arena_len_le
  have hcur32 : s.core.cur_level < 2 ^ 32 := by
    have := hw.cur_level_le; have := hlen.core_ok.trail_end_le; omega
  have hret_false_same : Q (false, ()) m :=
    hQ false s.core.mrk s.core.tmp s.core.tmp_cnt s.core.tmp_len s.core.min_clr_len s.core.arena
      s.scratch ext m hext (fun _ => M6ExtW2bPres.refl ext) hlen hw hwork ⟨rfl, rfl⟩ rfl
      (Nat.le_refl _) htl_cv (Nat.le_refl _) rfl (fun _ _ => ⟨rfl, rfl, rfl⟩)
      (fun _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ h0 h => absurd h0 h)
      (fun _ h1 h2 => by omega) (fun _ _ _ h1 h2 => by omega)
      (by rw [Nat.sub_self, s11_filter_zero]; intro _ _; simp)
      (by rw [s11_filter_zero (fun _ _ => by simp)]; simp) (fun hc => by cases hc) hm
  unfold Func.wp fidStep11AnalyzeRsnM6HdrFn full_analyze_rsn_m6_hdr_body; dsimp only
  c0_hsteps_nogrp
  · exact hret_false_same
  · have hne : rsn ≠ 0xFFFFFFFF#32 := by assumption
    have hbin : (rsn &&& 0x80000000#32) ≠ 0#32 := by assumption
    refine wp_m6Hdr_focus_frame hm fun hmf => ?_
    c0_hsteps_nogrp; c0_call hLit
    refine ⟨c, s, m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R, rfl, hlen, hcur32, htl_cv, by omega,
      hwork, hmf, fun ok mrk' tmp' tc' tl' mcl' ws1' ant' res' m' hlen' hwork' htl_ge
        htl_le1 htl_cv' htc_ge hant' hres' htc_eq hmpres htpres hnewm hnewt hok hm' => ?_⟩
    c0_hsteps_nogrp
    have hsame_c : FullWitnessCutInv c F0 F_cur cut
        { s.core with mrk := mrk', tmp := tmp', tmp_cnt := tc', tmp_len := tl',
                      min_clr_len := mcl' } :=
      { hw with arena := { hw.arena with len_ok := hw.arena.len_ok }
                watches := hw.watches.with_wstk rfl rfl rfl rfl rfl fun _ hr => hr }
    have htc_f := FullAnalyzeHelpers.filter_step_of_lit
      (fun w => decide ((s.core.lvl[w]?.getD 0#32).toNat = s.core.cur_level))
      (mv := s.core.cur_vars) (tc0 := s.core.tmp_cnt) (tc1 := s.core.tmp_cnt) (tc2 := tc')
      (v := (rsn &&& 0x7FFFFFFF#32).toNat / 2) (fun _ _ _ => rfl)
      (fun w hw => hmpres w (Nat.lt_of_lt_of_le hw hcv_le))
      (fun w hw_lt h0 hnz => (hnewm w (Nat.lt_of_lt_of_le hw_lt hcv_le) h0 hnz).1)
      (Nat.le_refl _) (by rw [Nat.sub_self, s11_filter_zero]; intro _ _; simp)
      (by
        rw [htc_eq]; congr 1
        exact ite_congr
          (propext (by simp only [BitVec.ofNat_eq_ofNat, decide_eq_true_eq]))
          (fun _ => rfl) (fun _ => rfl))
    have hres_f := s11_res_step_of_lit (mv := s.core.cur_vars)
      (v := (rsn &&& 0x7FFFFFFF#32).toNat / 2) (r0 := s.scratch.res_sz)
      (r1 := s.scratch.res_sz) (fun _ _ _ => rfl)
      (fun w hw => hmpres w (Nat.lt_of_lt_of_le hw hcv_le))
      (fun w hw_lt h0 hnz => (hnewm w (Nat.lt_of_lt_of_le hw_lt hcv_le) h0 hnz).1)
      (by rw [s11_filter_zero (fun _ _ => by simp)]; simp) hres'
    have hmp_cv : ∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 ≠ 0#8 →
        mrk'[v]?.getD 0#8 = s.core.mrk[v]?.getD 0#8 := fun v hv hnz => hmpres v hv hnz
    have hnewm_cv : ∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 = 0#8 → mrk'[v]?.getD 0#8 ≠ 0#8 →
        ∃ l ∈ fullRsnLits s rsn, l / 2 = v ∧ v < s.core.cur_vars ∧ v ≠ skip_var.toNat ∧
          0 < (s.core.lvl[v]?.getD 0#32).toNat ∧
          (s.core.lvl[v]?.getD 0#32).toNat ≤ s.core.cur_level := fun v hv h0 hnz => by
      obtain ⟨i, hi, heqv⟩ := hwork'.2.2.2 v hv hnz; have hvlt := (hwork'.2.2.1 i hi).1
      dsimp only at hvlt heqv; rw [heqv] at hvlt
      obtain ⟨rfl, _, hne', hpos, hle⟩ := hnewm v hv h0 hnz
      exact ⟨(rsn &&& 0x7FFFFFFF#32).toNat,
        (FullAnalyzeHelpers.mem_fullRsnLits_bin hne hbin).mpr rfl, rfl, hvlt, hne', hpos, hle⟩
    refine hQ ok mrk' tmp' tc' tl' mcl' s.core.arena _ ext m' hext
      (fun _ => M6ExtW2bPres.refl ext) hlen' hsame_c hwork' ⟨rfl, rfl⟩ rfl htl_ge htl_cv'
      htc_ge rfl (fun _ _ => ⟨rfl, rfl, rfl⟩) hmp_cv htpres hnewm_cv ?_
      (fun _ _ _ h1 h2 => by omega) htc_f hres_f ?_ (fullM6HdrMem_unfocus hm')
    · intro j hj1 hj2; obtain ⟨heq, _, _, h0, hpos, hcl, hmk⟩ := hnewt j hj1 hj2
      exact ⟨(FullAnalyzeHelpers.mem_fullRsnLits_bin hne hbin).mpr heq, by omega, by omega,
        by rwa [heq], by rwa [heq], by rwa [heq], by rwa [heq]⟩
    · intro hok'; obtain ⟨hvlt, hrest⟩ := hok hok'; refine ⟨hne, ?_, fun l hl => ?_⟩
      · rw [hant', fullRsnLits, ite_eq_right (fun h => hne h), ite_eq_left hbin, List.countP_cons,
          List.countP_nil, Nat.zero_add]
        exact congrArg (s.scratch.ant_sz + ·)
          (s11_bv64_ite_iff (by simp only [decide_eq_true_eq]; rfl))
      · simp only [fullRsnLits, ite_eq_right (fun h => hne h), ite_eq_left hbin,
          List.mem_singleton] at hl; subst hl
        refine ⟨hvlt, fun hne' => ?_⟩
        obtain ⟨hm1, h0r⟩ := hrest hne'; refine ⟨hm1, fun h0 => ?_⟩
        obtain ⟨hle, _, hlow⟩ := h0r h0
        exact ⟨hle, fun hpos hlt => let ⟨_, htget⟩ := hlow hpos hlt
          ⟨s.core.tmp_len, Nat.le_refl _, by omega, by rw [htget]; rfl⟩⟩
  · have hne : rsn ≠ 0xFFFFFFFF#32 := by assumption
    have hlarge : (rsn &&& 0x80000000#32) = 0#32 := by assumption
    have href : rsn.toNat ∈ fullArenaClauseRefs s := hrsn_ref hne hlarge
    obtain ⟨hbd3, hsz3, hbd, hbd_le, _⟩ := hw.arena.refs_wf rsn.toNat href
    have hrsn_lt : rsn.toNat < s.core.arena.length := by omega
    have hsz_idx : (rsn.setWidth 64 + 2#64).toNat = rsn.toNat + 2 := by
      have hlt32 : rsn.toNat < 2 ^ 32 := rsn.isLt
      have hsw : (rsn.setWidth 64).toNat = rsn.toNat := by
        rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by omega)
      rw [BitVec.toNat_add, hsw, show (2#64).toNat = 2 from rfl, Nat.mod_eq_of_lt (by omega)]
    have hsz_get : (s.core.arena[rsn.toNat + 2]'(by omega)).toNat =
        fullArenaClauseSize s rsn.toNat := by
      unfold fullArenaClauseSize fullArenaClauseSizeCore
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    have hhdr_get : s.core.arena[rsn.toNat]'hrsn_lt =
        fullArenaHdrCore s.core rsn.toNat := by
      unfold fullArenaHdrCore; rw [List.getElem?_eq_getElem hrsn_lt, Option.getD_some]
    refine wp_m6Hdr_focus_frame hm fun hmf => ?_
    c0_hsteps_nogrp; all_goals try exact hret_false_same
    c0_hsteps_nogrp; all_goals try exact hret_false_same
    c0_hsteps_nogrp; all_goals try exact hret_false_same
    refine wp_join_group (ts := [i32]) (fun (_ : Tup Val [i32]) m1 =>
        ∃ (arena1 : List (BitVec 32)) (sc1 : FullScratch) (ext1 : List (BitVec 64)),
        let s1 : FullState := { s with core := { s.core with arena := arena1 }, scratch := sc1 }
        M6HdrExtOk ext1 ∧ (M6HdrExtInitOk ext → M6ExtW2bPres ext ext1) ∧
        FullWitnessCutInv c F0 F_cur cut s1.core ∧ s1.LengthsOk c ∧
        FullExtScratchPres s s1 ∧ sc1.work_stk1 = s.scratch.work_stk1 ∧
        sc1.work_stk2 = s.scratch.work_stk2 ∧ sc1.ant_sz = s.scratch.ant_sz ∧
        sc1.res_sz = s.scratch.res_sz ∧ fullArenaClauseRefs s1 = fullArenaClauseRefs s ∧
        (∀ r ∈ fullArenaClauseRefs s, fullArenaClauseSize s1 r = fullArenaClauseSize s r ∧
          fullArenaClauseGarb s1 r = fullArenaClauseGarb s r ∧
          fullArenaClauseLits s1 r = fullArenaClauseLits s r) ∧
        (∀ k < fullArenaClauseSize s rsn.toNat,
          arena1[rsn.toNat + 3 + k]? = s.core.arena[rsn.toNat + 3 + k]?) ∧
        (FullMem c s1 ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext1 ⋆ R)) m1) ?_ ?_
    · rintro _ ⟨_hdr, ⟨⟩⟩ m1 ⟨arena1, sc1, ext1, hext1, hwb1, hw1, hlen1, hexp1, hws1, hws2,
        hant1, hres1, hrefs1, hcl1, har1_eq, hm1⟩
      have hsz_lt_len : (rsn.setWidth 64 + 2#64).toNat < s.core.arena.length := by
        have := hlen.core_ok.arena_len_le; rw [hsz_idx]; omega
      c0_hsteps_nogrp
      exact s11_rsn_lit_loop rfl hLit hext1 hwb1 hlen hwork htl_cv htc_fit hcv_le
        hcur32 hne hlarge hbd hbd_le hsz_idx hsz_lt_len rfl hw1 hlen1
        hexp1 hws1 hws2 hant1 hres1 hrefs1 hcl1 har1_eq hm1 hQ
    · intro Jred hJred
      c0_hsteps_nogrp
      · refine wp_join_group (ts := [i32, i64]) (S11GluePred c F0 F_cur cut ext s R rsn) ?_ ?_
        · rintro _ ⟨hdr1, glue1, ⟨⟩⟩ m0 ⟨arena0, hget0, hw0, hlen0, hrefs0, hcl0,
            har0_eq, hm0⟩
          have har0_len : arena0.length = c.arena_cap := hlen0.core_ok.arena_len_arr
          let s0 : FullState := { s with core := { s.core with arena := arena0 } }
          c0_hsteps_nogrp
          refine wp_join_group (ts := []) (fun (_ : Tup Val []) m1 =>
              ∃ (ext1 : List (BitVec 64)) (s1 : FullState),
                s1.core = s0.core ∧ s1.LengthsOk c ∧ M6HdrScratchPres s0 s1 ∧
                M6HdrExtOk ext1 ∧ (M6HdrExtInitOk ext → M6ExtW2bPres ext ext1) ∧
                (FullMem c s1 ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext1 ⋆ R)) m1) ?_ ?_
          · rintro _ ⟨⟩ m1 ⟨ext1, s1, hc1, hl1, hms1, hext1, hwb1, hm1f⟩
            have har1_len : s1.core.arena.length = c.arena_cap := hl1.core_ok.arena_len_arr
            c0_hsteps_nogrp
            refine wp_join_group (ts := []) (fun (_ : Tup Val []) m2 =>
                ∃ arena2 : List (BitVec 32),
                let s2 : FullState :=
                  { core := { s.core with arena := arena2 }, scratch := s1.scratch }
                FullWitnessCutInv c F0 F_cur cut s2.core ∧ s2.core.LengthsOk c ∧
                fullArenaClauseRefs s2 = fullArenaClauseRefs s ∧
                (∀ r ∈ fullArenaClauseRefs s, fullArenaClauseSize s2 r = fullArenaClauseSize s r ∧
                  fullArenaClauseGarb s2 r = fullArenaClauseGarb s r ∧
                  fullArenaClauseLits s2 r = fullArenaClauseLits s r) ∧
                (∀ k < fullArenaClauseSize s rsn.toNat,
                  arena2[rsn.toNat + 3 + k]? = s.core.arena[rsn.toNat + 3 + k]?) ∧
                (FullMem c s2 ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext1 ⋆ R)) m2) ?_ ?_
            · rintro _ ⟨⟩ m2 ⟨arena2, hw2, hlen2, hrefs2, hcl2, har2_eq, hm2⟩
              exact hJred (_, ()) m2 ⟨arena2, s1.scratch, ext1, hext1, hwb1,
                hw2, ⟨hlen2, hl1.scratch_ok⟩, hms1.extPres, hms1.ws1, hms1.ws2,
                hms1.ant_sz, hms1.res_sz, hrefs2, hcl2, har2_eq, hm2⟩
            · intro Ju hJu
              have hrsn_cap : rsn.toNat < c.arena_cap := by rw [← har_len]; omega
              dsimp only [s0] at hw0 hlen0 hrefs0 hcl0 hc1
              suffices hdone : ∀ (ar2 : List (BitVec 32)) (m2 : Mem 64),
                  (ar2 = s1.core.arena ∨
                    ar2 = s1.core.arena.set (rsn.setWidth 64).toNat
                      ((hdr1 &&& 134217727#32) ||| 4160749568#32)) →
                  (FullMem c { s1 with core := { s1.core with arena := ar2 } } ⋆
                    (m6ExtMem (m6ExtAddr c.hdr) ext1 ⋆ R)) m2 →
                  Ju () m2 by
                clear hJu hLit hRec hQ hwork hw htl_cv htc_fit hrsn_ref hret_false_same
                  hm hm0 hmf hms1 hwb1 hext1 hl1 hw0 hlen0 hrefs0 hcl0 har0_eq hget0 hc1
                  s0 har0_len arena0
                c0_hsteps_nogrp
                · exact hdone _ _ (Or.inr rfl) (by assumption)
                · exact hdone s1.core.arena m1 (Or.inl rfl) hm1f
              rintro ar2 m2 (rfl | rfl) hm2
              · have hs1_eq : { core := { s.core with arena := arena0 }, scratch := s1.scratch } =
                    s1 := by cases s1; dsimp only at hc1; rw [hc1]
                exact hJu () m2
                  ⟨arena0, hw0, hlen0.core_ok, hrefs0, hcl0, har0_eq, by rwa [hs1_eq]⟩
              · have hrsn1_lt : rsn.toNat < arena0.length := by rw [har0_len]; omega
                have href0c : rsn.toNat ∈ fullArenaClauseRefsCore
                    { s.core with arena := arena0 } := by
                  change rsn.toNat ∈ fullArenaClauseRefs
                    { s with core := { s.core with arena := arena0 } }
                  rw [hrefs0]; exact href
                have hbum := s11_hdrBitsUpdate_cut hlen0.core_ok hw0 href0c
                  (fun x => (x &&& 0x07FFFFFF#32) ||| (31#32 <<< 27))
                  s.core.arena_garbage s.core.num_irred s.core.num_redundant
                  (FullAnalyzeTactics.bv32_mask_usage_garb _ 31#32)
                  (FullAnalyzeTactics.bv32_mask_usage_shrk _ 31#32)
                have hhdr0_eq : hdr1 =
                    fullArenaHdrCore { s.core with arena := arena0 } rsn.toNat := by
                  unfold fullArenaHdrCore; rw [List.getElem?_eq_getElem hrsn1_lt] at hget0
                  rw [List.getElem?_eq_getElem hrsn1_lt, Option.getD_some]
                  exact (Option.some.inj hget0).symm
                let arena2 := arena0.set rsn.toNat ((fullArenaHdrCore
                  { s.core with arena := arena0 } rsn.toNat &&& 0x07FFFFFF#32) ||| (31#32 <<< 27))
                have har_u_eq : s1.core.arena.set (rsn.setWidth 64).toNat
                    ((hdr1 &&& 134217727#32) ||| 4160749568#32) = arena2 := by
                  rw [hc1, bv_c0_zext32_64, hhdr0_eq]; rfl
                refine hJu () _ ⟨arena2, hbum.1, { hlen0.core_ok with
                    arena_len_arr := (by dsimp only [arena2]; rw [List.length_set, har0_len]) },
                  hbum.2.1.trans hrefs0, fun r hr => ?_, fun k hk => ?_, ?_⟩
                · have hr0 :
                      r ∈ fullArenaClauseRefsCore { s.core with arena := arena0 } := by
                    change r ∈ fullArenaClauseRefs
                      { s with core := { s.core with arena := arena0 } }
                    rwa [hrefs0]
                  obtain ⟨a, b, d⟩ := hbum.2.2 r hr0
                  exact ⟨a.trans (hcl0 r hr).1, b.trans (hcl0 r hr).2.1, d.trans (hcl0 r hr).2.2⟩
                · rw [List.getElem?_set_ne (by omega)]; exact har0_eq k hk
                · have hs2_eq :
                      ({ core := { s.core with arena := arena2 },
                         scratch := s1.scratch } : FullState) =
                      { s1 with
                        core :=
                          { s1.core with
                            arena := s1.core.arena.set (rsn.setWidth 64).toNat
                              ((hdr1 &&& 134217727#32) ||| 4160749568#32) } } := by
                    rw [har_u_eq]; cases s1; dsimp only at hc1 ⊢; rw [hc1]
                  rw [hs2_eq]; exact hm2
          · intro Jpr hJpr
            c0_hsteps_nogrp
            · refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => hRec _ _ _ _ h) hcfg hext hlen0
                (fullM6HdrMem_unfocus hm0) fun _ ext1 s1 m1 hc1 hl1 hms1 hext1 hwb1 hm1 => ?_
              refine wp_m6Hdr_focus_frame hm1 fun hm1f => ?_
              exact hJpr () m1 ⟨ext1, s1, hc1, hl1, hms1, hext1, (fun h0 => (hwb1 h0).2), hm1f⟩
            · exact hJpr () m0 ⟨ext, s0, rfl, hlen0, M6HdrScratchPres.refl s0, hext,
                fun _ => M6ExtW2bPres.refl ext, hm0⟩
        · intro Jg hJg
          clear hLit hRec hQ hwork htl_cv htc_fit hrsn_ref hret_false_same hm hcfg hext hmax32
            hcv_le hcur32 hne hlarge
          have hrsn_get : s.core.arena[rsn.toNat]? = some (s.core.arena[(rsn.setWidth 64).toNat]'
              (by rw [bv_c0_zext32_64]; exact hrsn_lt)) := by
            simp only [bv_c0_zext32_64]; exact List.getElem?_eq_getElem hrsn_lt
          have hg_lt : (fullArenaHdrCore s.core rsn.toNat &&& 0x7FFFF#32).toNat < 2 ^ 19 :=
            Nat.lt_of_le_of_lt (bv32_and_le_right _ _) (by decide)
          c0_hsteps_nogrp
          · have hgl_z : ((fullArenaHdrCore s.core rsn.toNat &&& 0x7FFFF#32).setWidth 64).toNat =
                (fullArenaHdrCore s.core rsn.toNat &&& 0x7FFFF#32).toNat := by
              rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans hg_lt (by decide))]
            have hrsn_z_lt : (rsn.setWidth 64).toNat < s.core.arena.length := by
              rw [bv_c0_zext32_64]; exact hrsn_lt
            have hhdr_z : s.core.arena[(rsn.setWidth 64).toNat]'hrsn_z_lt =
                fullArenaHdrCore s.core rsn.toNat := by
              rw [FullAnalyzeTactics.getElem_eq_of_idx (hj := hrsn_lt) (bv_c0_zext32_64 rsn),
                hhdr_get]
            have hgt1 : 1 < (fullArenaHdrCore s.core rsn.toNat &&& 0x7FFFF#32).toNat := by
              simpa only [hhdr_get] using
                (by assumption : 1 < (s.core.arena[rsn.toNat] &&& 524287#32).toNat)
            have hle1 : (1#64 : BitVec 64) ≤
                (fullArenaHdrCore s.core rsn.toNat &&& 0x7FFFF#32).setWidth 64 := by
              refine BitVec.le_def.mpr ?_
              rw [hgl_z]; have h1n : (1#64 : BitVec 64).toNat = 1 := rfl; omega
            have hlim : (((s.core.arena[(rsn.setWidth 64).toNat]'hrsn_z_lt &&&
                524287#32).setWidth 64) - 1#64).toNat < 2 ^ 19 := by
              rw [hhdr_z, BitVec.toNat_sub_of_le hle1, hgl_z]
              have h1n : (1#64 : BitVec 64).toNat = 1 := rfl; omega
            exact s11_rsn_glue_lo rfl rfl rfl hlen hw href hrsn_lt hrsn_z_lt
              (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_trans hbd3 (har_len ▸ har_le)))
              hsz_idx rfl rfl rfl hsz_get hrsn_get hmf hlim hJg
          · exact hJg (_, _, ()) m ⟨s.core.arena, hrsn_get, hw, hlen, rfl,
              fun _ _ => ⟨rfl, rfl, rfl⟩, fun _ _ => rfl, hmf⟩
      · exact hJred (_, ()) m ⟨s.core.arena, s.scratch, ext, hext,
          fun _ => M6ExtW2bPres.refl ext, hw, hlen, fullExtScratchPres_refl s,
          rfl, rfl, rfl, rfl, rfl, fun _ _ => ⟨rfl, rfl, rfl⟩, fun _ _ => rfl, hmf⟩

end LeanQbe.T.Examples.Kissat.FullFidelityStep11

end
