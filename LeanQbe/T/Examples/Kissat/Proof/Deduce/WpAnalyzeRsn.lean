/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Deduce.Spec
public import LeanQbe.T.Examples.Kissat.Src.Deduce
public import LeanQbe.T.Logic.CanonicalEnv
import LeanQbe.T.Examples.Kissat.Proof.Deduce.WpCommon
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts1
import LeanQbe.T.Examples.Kissat.Proof.Spec.Header
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
import LeanQbe.T.Examples.Kissat.Proof.Spec.WitnessInv
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation
meta import LeanQbe.T.Logic.C0HeadStep

/-!
# Parametric WP Proof for `full_analyze_rsn_m6_hdr` (`Proof.Deduce.WpAnalyzeRsn`)

Proves `full_analyze_rsn_m6_hdr_wp` against `Proof.Deduce.Spec.s13AnalyzeRsnHdrSpec`
(`public section`, `0` legacy `Full*` imports, `0` `import all`, `0` `@[expose]` on
theorems/lemmas/sections).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Deduce

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Deduce
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Deduce.Spec
open Kraken.Bedrock2.Test

open scoped FullArenaTactics DeduceTactics

/-! ## 1. Pure Helpers for `full_analyze_rsn_m6_hdr` -/

private theorem rsn_bv32_glue_bit (x g mask : BitVec 32) {b : Nat} (h19 : 19 ≤ b)
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

private theorem rsn_bv32_or_bit31_ne0 (x : BitVec 32) :
    ((x ||| 0x80000000#32) &&& 0x80000000#32) ≠ 0#32 := by
  intro h
  have h31 := congrArg (fun v : BitVec 32 => v.getLsbD 31) h
  simp at h31

private theorem rsn_bv32_or_and_clear {x : BitVec 32} (hx : x.toNat < 2 ^ 31) :
    ((x ||| 0x80000000#32) &&& 0x7FFFFFFF#32) = x := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_or]
  by_cases h31 : k = 31
  · subst h31
    have hmsb : x.getLsbD 31 = false := by
      rw [BitVec.getLsbD_eq_getElem (by omega), BitVec.getElem_eq_testBit_toNat,
        Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hx]; rfl
    rw [hmsb]; rfl
  · have hk31 : k < 31 := by omega
    have h0 : (0x80000000#32 : BitVec 32).getLsbD k = false := by
      rw [show (0x80000000#32 : BitVec 32) = BitVec.ofNat 32 (2 ^ 31) from rfl,
        BitVec.getLsbD_ofNat, Nat.testBit_two_pow]
      simp [Ne.symm h31]
    have h1 : (0x7FFFFFFF#32 : BitVec 32).getLsbD k = true := by
      rw [show (0x7FFFFFFF#32 : BitVec 32) = BitVec.ofNat 32 (2 ^ 31 - 1) from rfl,
        BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one]
      simp [hk, hk31]
    rw [h0, h1, Bool.or_false, Bool.and_true]

private theorem rsn_nodup_length_le_of_subset {α : Type} [DecidableEq α] :
    ∀ (xs ys : List α), xs.Nodup → (∀ x ∈ xs, x ∈ ys) → xs.length ≤ ys.length
  | [], _, _, _ => Nat.zero_le _
  | a :: tl, ys, hnd, hsub => by
    rw [List.nodup_cons] at hnd
    have ha : a ∈ ys := hsub a (List.mem_cons_self ..)
    have hsub' : ∀ x ∈ tl, x ∈ ys.erase a := fun x hx =>
      (List.mem_erase_of_ne (fun h => hnd.1 (by rwa [← h]))).mpr
        (hsub x (List.mem_cons_of_mem _ hx))
    have ih := rsn_nodup_length_le_of_subset tl (ys.erase a) hnd.2 hsub'
    have hlen := List.length_erase_of_mem ha
    have hpos : 0 < ys.length := List.length_pos_of_mem ha
    simp only [List.length_cons]; omega

private theorem rsn_take_set_eq_take {α : Type} {xs : List α} {n : Nat} (v : α)
    (hn : n < xs.length) : (xs.set n v).take (n + 1) = xs.take n ++ [v] := by
  apply List.ext_getElem
  · simp [List.length_take, List.length_set, Nat.min_eq_left (Nat.le_of_lt hn),
      Nat.min_eq_left (Nat.succ_le_of_lt hn)]
  · intro i h1 h2
    simp only [List.length_take, List.length_set, Nat.min_eq_left (Nat.succ_le_of_lt hn)] at h1
    rw [List.getElem_take]
    by_cases hin : i < n
    · rw [List.getElem_set_ne (by omega), List.getElem_append_left
        (by simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hn)]; omega), List.getElem_take]
    · have hie : i = n := by omega
      subst hie
      rw [List.getElem_set_self,
        List.getElem_append_right (by simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hn)])]
      simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hn)]

private theorem rsn_witness_set_minClr {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {cut : Nat} {k : FullCoreState} (mclr' : List (BitVec 32))
    (hw : FullWitnessCutInv c F0 F_cur cut k) :
    FullWitnessCutInv c F0 F_cur cut { k with min_clr := mclr' } :=
  ⟨{ hw.toFullOtfsWitnessInv with
      arena := { hw.arena with len_ok := hw.arena.len_ok }
      watches := hw.watches.with_wstk rfl rfl rfl rfl rfl fun _ hr => hr },
    hw.cut_le, hw.reason_inv_cut, hw.reason_lit_mem_cut⟩

private theorem rsn_mem_fullRsnLits_bin {s : FullState} {rsn : BitVec 32} {l : Nat}
    (hne : rsn ≠ 0xFFFFFFFF#32) (hbin : (rsn &&& 0x80000000#32) ≠ 0#32) :
    l ∈ fullRsnLits s rsn ↔ l = (rsn &&& 0x7FFFFFFF#32).toNat := by
  simp [fullRsnLits, hne, hbin]

private theorem rsn_mem_fullRsnLits_large {s : FullState} {rsn : BitVec 32} {l : Nat}
    (hne : rsn ≠ 0xFFFFFFFF#32) (hlarge : (rsn &&& 0x80000000#32) = 0#32) :
    l ∈ fullRsnLits s rsn ↔ l ∈ fullArenaClauseLits s rsn.toNat := by
  simp [fullRsnLits, hne, hlarge]

private abbrev RsnStepPre (s : FullState) (rsn_lits : List Nat) (skip_var : BitVec 32)
    (mrk' : List (BitVec 8)) (tmp' : List (BitVec 32)) (tc' tl' : Nat)
    (res' : BitVec 64) : Prop :=
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

private theorem rsn_comb_step {s : FullState} {l_bv skip_var : BitVec 32}
    {rsn_lits : List Nat} {mrk' mrk2 : List (BitVec 8)} {tmp' tmp2 : List (BitVec 32)}
    {tc' tl' tc2 tl2 : Nat} {res' res2 : BitVec 64}
    (htl_ge : s.core.tmp_len ≤ tl') (htl2_ge : tl' ≤ tl2) (htl2_inc : tl2 ≤ tl' + 1)
    (htc_ge : s.core.tmp_cnt ≤ tc') (hl_mem : l_bv.toNat ∈ rsn_lits)
    (hpre : RsnStepPre s rsn_lits skip_var mrk' tmp' tc' tl' res')
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
    RsnStepPre s rsn_lits skip_var mrk2 tmp2 tc2 tl2 res2 := by
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
  · exact filter_step_of_lit
      (fun w => decide ((s.core.lvl[w]?.getD 0#32).toNat = s.core.cur_level))
      (mv := s.core.cur_vars) (tc0 := s.core.tmp_cnt) (tc1 := tc') (v := l_bv.toNat / 2)
      hmp hmp2 (fun w hw h0 hnz => (hnm2 w hw h0 hnz).1) htc_ge hcnt
      (by simpa only [decide_eq_true_eq] using htc2_eq)
  · exact res_step_of_lit (mv := s.core.cur_vars) (v := l_bv.toNat / 2) hmp hmp2
      (fun w hw h0 hnz => (hnm2 w hw h0 hnz).1) hres_l hres2

/-! ## 2. Large-Reason Literal Loop Helper (`rsn_lit_loop`) -/

private theorem rsn_lit_loop {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {cut : Nat} {ext ext1 : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {arena1 mclr1 : List (BitVec 32)} {sc1 : FullScratch} {m1 : Mem 64}
    {Q : Post [.bool]} {X : XPost} {rsn skip_var : Val i32} {pArena : Val i64} {sz_bv : Val i32}
    (hpArena : pArena = c.pArena)
    (hLit : Γ.Has "full_analyze_lit" Spec.fullAnalyzeLitSpec)
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
      ({ s with core := { s.core with arena := arena1, min_clr := mclr1 },
                scratch := sc1 } : FullState).core)
    (hlen1 : ({ s with core := { s.core with arena := arena1, min_clr := mclr1 },
                       scratch := sc1 } : FullState).LengthsOk c)
    (hexp1 : FullExtScratchPres s
      { s with core := { s.core with arena := arena1, min_clr := mclr1 }, scratch := sc1 })
    (hws1 : sc1.work_stk1 = s.scratch.work_stk1) (hws2 : sc1.work_stk2 = s.scratch.work_stk2)
    (hant1 : sc1.ant_sz = s.scratch.ant_sz) (hres1 : sc1.res_sz = s.scratch.res_sz)
    (hrefs1 : fullArenaClauseRefs
      { s with core := { s.core with arena := arena1, min_clr := mclr1 }, scratch := sc1 } =
        fullArenaClauseRefs s)
    (hcl1 : ∀ r ∈ fullArenaClauseRefs s,
      fullArenaClauseSize
          { s with core := { s.core with arena := arena1, min_clr := mclr1 }, scratch := sc1 } r =
        fullArenaClauseSize s r ∧
      fullArenaClauseGarb
          { s with core := { s.core with arena := arena1, min_clr := mclr1 }, scratch := sc1 } r =
        fullArenaClauseGarb s r ∧
      fullArenaClauseLits
          { s with core := { s.core with arena := arena1, min_clr := mclr1 }, scratch := sc1 } r =
        fullArenaClauseLits s r)
    (har1_eq : ∀ k < fullArenaClauseSize s rsn.toNat,
      arena1[rsn.toNat + 3 + k]? = s.core.arena[rsn.toNat + 3 + k]?)
    (hm1 : (FullMem c { s with core := { s.core with arena := arena1, min_clr := mclr1 },
                               scratch := sc1 } ⋆
      (m6ExtMem (m6ExtAddr c.hdr) ext1 ⋆ R)) m1)
    (hQ : ∀ (ok : Bool) (mrk' : List (BitVec 8)) (tmp' mclr' : List (BitVec 32))
        (tc' tl' mcl' : Nat) (arena' : List (BitVec 32)) (sc' : FullScratch)
        (ext' : List (BitVec 64)) (m' : Mem 64),
      let s' : FullState :=
        { core := { s.core with mrk := mrk', tmp := tmp', min_clr := mclr',
                                tmp_cnt := tc', tmp_len := tl',
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
  let s1 : FullState :=
    { s with core := { s.core with arena := arena1, min_clr := mclr1 }, scratch := sc1 }
  have har1_len := hlen1.core_ok.arena_len_arr; have har_len := hlen.core_ok.arena_len_arr
  have har_le := hlen.core_ok.arena_len_le
  let sz : Nat := fullArenaClauseSize s rsn.toNat
  have hsz_at : s.core.arena[(rsn.setWidth 64 + 2#64).toNat]'hsz_lt =
      s.core.arena[rsn.toNat + 2]'(by omega) := getElem_eq_of_idx hsz_idx
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
    FullAnaMarksCov c { s1 with
      core := { s1.core with
        mrk := mrk', tmp := tmp', tmp_cnt := tc', tmp_len := tl', min_clr_len := mcl' },
      scratch := { sc1 with work_stk1 := ws1', ant_sz := ant', res_sz := res' } } ∧
    RsnStepPre s (fullArenaClauseLits s rsn.toNat) skip_var mrk' tmp' tc' tl' res' ∧
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
      have hwks : FullAnaMarksCov c s1 := by
        obtain ⟨h1, h2, h3, h4⟩ := hwork
        exact ⟨h1, by simpa only [s1, hws1] using h2,
          by simpa only [s1, hws1] using h3,
          fun v hv hnz => let ⟨k, hk, heq⟩ := h4 v hv hnz
            ⟨k, hk, by simpa only [s1, hws1] using heq⟩⟩
      refine hL (0#32, ()) m1 ⟨0, s.core.mrk, s.core.tmp, s.core.min_clr_len, s.core.tmp_cnt,
        s.core.tmp_len, s.scratch.ant_sz, s.scratch.res_sz, s.scratch.work_stk1,
        Nat.zero_le _, rfl, hlen1.core_ok.mrk_len, hlen1.core_ok.tmp_len_arr,
        hlen.scratch_ok.work_stk1_len, hlen1.core_ok.min_clr_len_le, Nat.le_refl _, htl_cv,
        Nat.le_refl _, (by simpa only [s1, ← hant1, ← hres1, ← hws1] using hwks),
        ⟨fun _ _ _ => rfl, fun _ _ => rfl, fun _ _ h0 hnz => absurd h0 hnz,
          fun _ h1 h2 => by omega, fun _ _ _ h1 h2 => by omega,
          by rw [Nat.sub_self, filter_length_eq_zero_of_false]; intro _ _; simp,
          by rw [filter_length_eq_zero_of_false (fun _ _ => by simp)]; simp⟩,
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
          Nat.mod_eq_of_lt (by omega : i < 2 ^ 32)]; omega
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
      rw [getElem_eq_of_idx (hi := hidx_lt) (hj := by omega) hidx_l]
      c0_call hLit
      refine ⟨c, st, m6ExtMem (m6ExtAddr c.hdr) ext1 ⋆ R, rfl, hst_len, hcur32, htl_le,
        by dsimp [st]; omega, hwk', hml,
        fun ok2 mrk2 tmp2 tc2 tl2 mcl2 ws2 ant2 res2 m2 hlen2 hwk2 htl2_ge htl2_inc htl2_le
          htc2_ge hant2 hres2 htc2_eq hmpres2 htpres2 hnewm2 hnewt2 hok2 hm2 => ?_⟩
      dsimp only [st] at *
      have hpre2 := rsn_comb_step htl_ge htl2_ge htl2_inc htc_ge hl_mem hpre
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
          let ⟨k, hk, heq⟩ := hwk2.2.2.2 v hv hnz
          let hvlt := heq ▸ (hwk2.2.2.1 k hk).1
          let ⟨l, hl, hr⟩ := h3 v hvlt h0 hnz
          ⟨l, (rsn_mem_fullRsnLits_large hne hlarge).mpr hl, hr.1, hvlt, hr.2⟩
        exact hQ false mrk2 tmp2 mclr1 tc2 tl2 mcl2 arena1
          { sc1 with work_stk1 := ws2, ant_sz := ant2, res_sz := res2 } ext1 m2
          hext1 hwb1 hlen2
          ⟨{ hw1.toFullOtfsWitnessInv with
              arena := { hw1.arena with len_ok := hw1.arena.len_ok }
              watches := hw1.watches.with_wstk rfl rfl rfl rfl rfl fun _ hr => hr },
            hw1.cut_le, hw1.reason_inv_cut, hw1.reason_lit_mem_cut⟩
          hwk2 hexp1 hws2 (Nat.le_trans htl_ge htl2_ge) htl2_le (Nat.le_trans htc_ge htc2_ge)
          hrefs1 hcl1 h1c h2 h3c (fun j hj1 hj2 => let ⟨ha, hr⟩ := h4 j hj1 hj2
            ⟨(rsn_mem_fullRsnLits_large hne hlarge).mpr ha, hr⟩)
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
              (bv64_ite_iff (by simp only [antPred, decide_eq_true_eq]; rfl)))
          rw [show BitVec.ofNat 32 i + 1 = BitVec.ofNat 32 (i + 1) from
            BitVec.eq_of_toNat_eq (by simp [BitVec.toNat_add, hi_mod])]
          refine hL (BitVec.ofNat 32 (i + 1), ()) m2
            (by rw [bv32_ofNat_toNat (by omega), hi_mod]; omega)
            ⟨i + 1, mrk2, tmp2, mcl2, tc2, tl2, ant2, res2, ws2, by omega, rfl,
              hlen2.core_ok.mrk_len, hlen2.core_ok.tmp_len_arr, hlen2.scratch_ok.work_stk1_len,
              hlen2.core_ok.min_clr_len_le, by omega, htl2_le, by omega, hwk2, hpre2, ?_,
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
        let ⟨k, hk, heq⟩ := hwk'.2.2.2 v hv hnz
        let hvlt := heq ▸ (hwk'.2.2.1 k hk).1
        let ⟨l, hl, hr⟩ := hnewm v hvlt h0 hnz
        ⟨l, (rsn_mem_fullRsnLits_large hne hlarge).mpr hl, hr.1, hvlt, hr.2⟩
      refine hQ true mrk' tmp' mclr1 tc' tl' mcl' arena1
        { sc1 with work_stk1 := ws1', ant_sz := ant', res_sz := res' } ext1 ml hext1 hwb1
        ⟨{ hlen1.core_ok with
            mrk_len := hml_l, tmp_len_arr := htl_l,
            tmp_len_le := (by dsimp; omega), min_clr_len_le := hmcl_le },
         { hlen1.scratch_ok with work_stk1_len := hws_l }⟩
        ⟨{ hw1.toFullOtfsWitnessInv with
            arena := { hw1.arena with len_ok := hw1.arena.len_ok }
            watches := hw1.watches.with_wstk rfl rfl rfl rfl rfl fun _ hr => hr },
          hw1.cut_le, hw1.reason_inv_cut, hw1.reason_lit_mem_cut⟩
        hwk' hexp1 hws2 htl_ge htl_le htc_ge hrefs1 hcl1 h1c htpres h3c
        (fun j hj1 hj2 => let ⟨ha, hr⟩ := hnewt j hj1 hj2
          ⟨(rsn_mem_fullRsnLits_large hne hlarge).mpr ha, hr⟩)
        hnd_t hcnt hres_l ?_ (fullM6HdrMem_unfocus hml)
      intro _; refine ⟨hne, ?_, fun l hl => ?_⟩
      · rw [hant_l, hieq]
        have htake_all : (fullArenaClauseLits s rsn.toNat).take sz =
            fullArenaClauseLits s rsn.toNat := List.take_of_length_le (by
          simp [fullArenaClauseLits, fullArenaClauseLitsCore, sz, fullArenaClauseSize]; omega)
        rw [htake_all]; congr 1
        unfold fullRsnLits; rw [ite_eq_right (fun h => hne h), ite_eq_right (fun h => h hlarge)]
      · have hl_ar : l ∈ fullArenaClauseLits s rsn.toNat :=
          (rsn_mem_fullRsnLits_large hne hlarge).mp hl
        obtain ⟨k, hk, hl_eq⟩ := (mem_fullArenaClauseLitsCore_iff (by omega)).mp hl_ar
        have hlk : (s.core.arena[rsn.toNat + 3 + k]?.getD 0#32).toNat = l := by
          rw [List.getElem?_eq_getElem (by omega), Option.getD_some, ← hl_eq]
        simpa only [hlk] using hdone k (hieq ▸ hk)

/-! ## 3. O(sz) `frame_trail` Bit-31 Glue Recomputation Helper (`rsn_glue_recompute_wp`) -/

private abbrev RsnGluePred (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (cut : Nat)
    (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop) (rsn : BitVec 32)
    (xs : Tup Val [i32, i64]) (m0 : Mem 64) : Prop :=
  ∃ (arena0 mclr0 : List (BitVec 32)),
    let s0 : FullState := { s with core := { s.core with arena := arena0, min_clr := mclr0 } }
    arena0[rsn.toNat]? = some xs.fst ∧ FullWitnessCutInv c F0 F_cur cut s0.core ∧ s0.LengthsOk c ∧
    fullArenaClauseRefs s0 = fullArenaClauseRefs s ∧
    (∀ r ∈ fullArenaClauseRefs s, fullArenaClauseSize s0 r = fullArenaClauseSize s r ∧
      fullArenaClauseGarb s0 r = fullArenaClauseGarb s r ∧
      fullArenaClauseLits s0 r = fullArenaClauseLits s r) ∧
    (∀ k < fullArenaClauseSize s rsn.toNat,
      arena0[rsn.toNat + 3 + k]? = s.core.arena[rsn.toNat + 3 + k]?) ∧
    (FullMem c s0 ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R)) m0

private def rgDummyVal : (t : Ty) → Val t
  | .bits w => 0#w | .bool => false | .float f => BitVec.zero f.width
  | .pair a b => (rgDummyVal a, rgDummyVal b)
private def rgDummyTup : (ts : List Ty) → Tup Val ts
  | [] => () | t :: ts => (rgDummyVal t, rgDummyTup ts)
private def rgSkip {rs : List Ty} : Nat → Expr Val Cont rs → Expr Val Cont rs
  | 0, e => e | k + 1, .let_ (ts := ts) _ f => rgSkip k (f (rgDummyTup ts))
  | k + 1, .load t _ f => rgSkip k (f (rgDummyVal t)) | _, e => e
private def rgSkipLets {rs : List Ty} : Nat → Expr Val Cont rs → Expr Val Cont rs
  | 0, e => e | k + 1, .let_ (ts := ts) _ f => rgSkipLets k (f (rgDummyTup ts)) | _, e => e
private def rgLoad64 {rs : List Ty} (v : Val i64) : Expr Val Cont rs → Expr Val Cont rs
  | .load (.bits 64) _ f => f v | _ => .hlt
private def rgLoad32 {rs : List Ty} (v : Val i32) : Expr Val Cont rs → Expr Val Cont rs
  | .load (.bits 32) _ f => f v | _ => .hlt
private def rgLet64 {rs : List Ty} (v : Val i64) : Expr Val Cont rs → Expr Val Cont rs
  | .let_ (ts := [.bits 64]) _ f => f (v, ()) | _ => .hlt
private def rgThen {rs : List Ty} : Expr Val Cont rs → Expr Val Cont rs
  | .jnz _ t _ => t | _ => .hlt
private def rgElse {rs : List Ty} : Expr Val Cont rs → Expr Val Cont rs
  | .jnz _ _ e => e | _ => .hlt
private def rgGrp1Body {rs : List Ty} : Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 32]]) _ b => b (fun _ _ => False, ()) | _ => .hlt
private def rgGrp2Enter {rs : List Ty} (Jg : Cont [i32, i64]) :
    Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 32, .bits 64]]) _ b => b (Jg, ()) | _ => .hlt

private def rsnGlueExpr (h ar glue : Val i64) (rsn skip_var hdr sz : Val i32)
    (Jg : Cont [i32, i64]) : Expr Val Cont [.bool] :=
  full_analyze_rsn_m6_hdr_body Val Cont (h, rsn, skip_var, ())
    |> (fun e => rgElse (rgSkip 8 e))
    |> (fun e => rgElse (rgSkip 8 e))
    |> (fun e => rgLoad64 ar (rgSkipLets 8 e))
    |> (fun e => rgElse (rgSkip 8 e))
    |> (fun e => rgLoad32 hdr (rgSkipLets 8 e))
    |> (fun e => rgLoad32 sz (rgSkipLets 8 e))
    |> (fun e => rgElse (rgSkip 8 e))
    |> (fun e => rgElse (rgSkip 8 e))
    |> (fun e => rgThen (rgSkip 8 (rgGrp1Body (rgSkip 8 e))))
    |> (fun e => rgGrp2Enter Jg (rgLet64 glue (rgSkipLets 1 e)))

private theorem rsn_glue_recompute_wp {Γ : Env} {Q : Post [.bool]} {X : XPost}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {cut : Nat}
    {ext : List (BitVec 64)} {s : FullState} {R : Mem 64 → Prop} {rsn skip_var : BitVec 32}
    {Jg : Cont [i32, i64]} {m : Mem 64}
    (hlen : s.LengthsOk c) (hw : FullWitnessCutInv c F0 F_cur cut s.core)
    (href : rsn.toNat ∈ fullArenaClauseRefs s)
    (hsz3 : 3 ≤ fullArenaClauseSizeCore s.core rsn.toNat)
    (hbd : rsn.toNat + 3 + fullArenaClauseSizeCore s.core rsn.toNat ≤ s.core.arena_len)
    (hsz_idx : (rsn.setWidth 64 + 2#64).toNat = rsn.toNat + 2)
    (hrsn_lt : rsn.toNat < s.core.arena.length)
    (hsz_get : (s.core.arena[rsn.toNat + 2]'(by
      have := hlen.core_ok.arena_len_arr; have := hlen.core_ok.arena_len_le; omega)).toNat =
      fullArenaClauseSize s rsn.toNat)
    (hhdr_get : s.core.arena[rsn.toNat]'hrsn_lt = fullArenaHdrCore s.core rsn.toNat)
    (hmf : (FullMem c s ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R)) m)
    (hJg : ∀ xs m0, RsnGluePred c F0 F_cur cut ext s R rsn xs m0 → Jg xs m0) :
    wp Γ Q X (rsnGlueExpr c.hdr c.pArena
      ((s.core.arena[(rsn.setWidth 64).toNat]'(by rw [bv_c0_zext32_64]; exact hrsn_lt) &&&
        524287#32).setWidth 64)
      rsn skip_var
      (s.core.arena[(rsn.setWidth 64).toNat]'(by rw [bv_c0_zext32_64]; exact hrsn_lt))
      (s.core.arena[(rsn.setWidth 64 + 2#64).toNat]'(by
        have := hlen.core_ok.arena_len_arr; have := hlen.core_ok.arena_len_le
        rw [hsz_idx]; omega)) Jg) m := by
  have hmax32 := fullInv_max_vars_lt32 c; have hcv_le := hlen.core_ok.cur_vars_le
  have har_len := hlen.core_ok.arena_len_arr; have har_le := hlen.core_ok.arena_len_le
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcl_le_mv : s.core.cur_level ≤ c.max_vars :=
    Nat.le_trans hw.cur_level_le (Nat.le_trans hlen.core_ok.trail_end_le hcv_le)
  have hftrl_len := hlen.core_ok.frame_trail_len
  have hmclr_len := hlen.core_ok.min_clr_len_arr
  have hlvl_len := hlen.core_ok.lvl_len
  have hftrl_b31 : ∀ l ≤ s.core.cur_level,
      (s.core.frame_trail[l]?.getD 0#32).toNat < 2 ^ 31 := fun l hl => by
    have := hw.frame_trail_lt l hl; have := hlen.core_ok.trail_end_le; omega
  have hrsn_get : s.core.arena[rsn.toNat]? = some (s.core.arena[(rsn.setWidth 64).toNat]'
      (by rw [bv_c0_zext32_64]; exact hrsn_lt)) := by
    simp only [bv_c0_zext32_64]; exact List.getElem?_eq_getElem hrsn_lt
  have hg_lt : (fullArenaHdrCore s.core rsn.toNat &&& 0x7FFFF#32).toNat < 2 ^ 19 :=
    Nat.lt_of_le_of_lt (bv32_and_le_right _ _) (by decide)
  let lvlVals : List Nat :=
    (List.range s.core.cur_vars).map fun v => (s.core.lvl[v]?.getD 0#32).toNat
  have hlvlVals_len : lvlVals.length = s.core.cur_vars := by simp [lvlVals]
  let sz : Nat := fullArenaClauseSize s rsn.toNat
  have hsz_at : s.core.arena[(rsn.setWidth 64 + 2#64).toNat]'(by rw [hsz_idx]; omega) =
      s.core.arena[rsn.toNat + 2]'(by omega) := getElem_eq_of_idx hsz_idx
  have hrsn_z_lt : (rsn.setWidth 64).toNat < s.core.arena.length := by
    rw [bv_c0_zext32_64]; exact hrsn_lt
  have hhdr_z : s.core.arena[(rsn.setWidth 64).toNat]'hrsn_z_lt =
      fullArenaHdrCore s.core rsn.toNat := by
    rw [getElem_eq_of_idx (hj := hrsn_lt) (bv_c0_zext32_64 rsn), hhdr_get]
  conv => arg 4; whnf
  c0_hsteps_nogrp
  · let glue0 : BitVec 64 :=
      (s.core.arena[(rsn.setWidth 64).toNat]'hrsn_z_lt &&& 524287#32).setWidth 64
    have hglue0_eq : (s.core.arena[rsn.toNat]'hrsn_lt &&& 524287#32).toNat = glue0.toNat := by
      dsimp only [glue0]; rw [bv_c0_zext32_64, hhdr_z, hhdr_get]
    have hglue0_gt1 : 1 < glue0.toNat := by
      rw [← hglue0_eq, DeduceTactics.ded_bv32_mask_glue19_toNat]
      simpa only [show (1 : BitVec 64).toNat = 1 from rfl] using (by assumption : _)
    have hglue0_lt : glue0.toNat < 2 ^ 19 := by
      dsimp only [glue0]; rw [hhdr_z, BitVec.toNat_setWidth,
        Nat.mod_eq_of_lt (Nat.lt_trans hg_lt (by decide))]; exact hg_lt
    let glueInv (ng : Nat) (ftrl' mclr' : List (BitVec 32)) : Prop :=
      ng ≤ s.core.cur_vars ∧ ng ≤ glue0.toNat ∧
      ftrl'.length = c.max_vars + 1 ∧ mclr'.length = c.max_vars ∧
      (∀ j < ng, (mclr'[j]?.getD 0#32).toNat ≤ s.core.cur_level ∧
        (mclr'[j]?.getD 0#32).toNat ∈ lvlVals) ∧
      ((mclr'.take ng).map BitVec.toNat).Nodup ∧
      (∀ l ≤ s.core.cur_level,
        ftrl'[l]? = if l ∈ (mclr'.take ng).map BitVec.toNat
          then some ((s.core.frame_trail[l]?.getD 0#32) ||| 0x80000000#32)
          else s.core.frame_trail[l]?) ∧
      (∀ l, s.core.cur_level < l → ftrl'[l]? = s.core.frame_trail[l]?)
    refine wp_while_break_state
      (fun st : Nat × BitVec 32 × List (BitVec 32) × List (BitVec 32) =>
        (BitVec.ofNat 64 st.1, st.2.1, ()))
      (fun st mb => glueInv st.1 st.2.2.1 st.2.2.2 ∧
        (FullMem c { s with core := { s.core with
          frame_trail := st.2.2.1, min_clr := st.2.2.2 } } ⋆
          (m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R)) mb)
      (fun st : Nat × BitVec 32 × List (BitVec 32) × List (BitVec 32) =>
        (BitVec.ofNat 64 st.1, st.2.1, ()))
      (fun st => sz - st.2.1.toNat)
      (fun st ml => st.2.1.toNat ≤ sz ∧ st.1 < glue0.toNat ∧ glueInv st.1 st.2.2.1 st.2.2.2 ∧
        (FullMem c { s with core := { s.core with
          frame_trail := st.2.2.1, min_clr := st.2.2.2 } } ⋆
          (m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R)) ml) ?_ ?_ ?_
    · rintro _ ⟨ng, _kf, ftrl1, mclr1⟩ m1 ⟨hgi1, hm1⟩
      obtain ⟨hng_cv, hng_gl, hftrl1_l, hmclr1_l, hmclr1_b, hnd1, hftrl1_le, hftrl1_gt⟩ := hgi1
      have hng_lt64 : ng < 2 ^ 64 := by omega
      c0_hsteps_nogrp
      refine wp_while_state1 (t := i64) (α := Nat × List (BitVec 32))
        (proj := fun st => BitVec.ofNat 64 st.1) (μ := fun st => ng - st.1)
        (Inv := fun st mu => st.1 ≤ ng ∧ st.2.length = c.max_vars + 1 ∧
          (∀ l ≤ s.core.cur_level,
            st.2[l]? = if l ∈ ((mclr1.take ng).drop st.1).map BitVec.toNat
              then some ((s.core.frame_trail[l]?.getD 0#32) ||| 0x80000000#32)
              else s.core.frame_trail[l]?) ∧
          (∀ l, s.core.cur_level < l → st.2[l]? = s.core.frame_trail[l]?) ∧
          (FullMem c { s with core := { s.core with
            frame_trail := st.2, min_clr := mclr1 } } ⋆
            (m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R)) mu)
        (fun Ju hJu => by
          c0_hsteps; exact hJu (0, ftrl1) m1
            ⟨Nat.zero_le _, hftrl1_l, by simpa using hftrl1_le, hftrl1_gt, hm1⟩)
        (fun Ju ⟨ui, ftrlU⟩ mu ⟨hui_le, hfu_l, hfu_le, hfu_gt, hmu⟩ ihu => ?_)
      dsimp only at hui_le hfu_l hfu_le hfu_gt hmu ihu; rw [Blocks.get_here]; dsimp only
      c0_hsteps_nogrp
      · have hui_lt : ui < ng := by
          have h1 : ui % 2 ^ 64 < ng % 2 ^ 64 := by
            simpa only [BitVec.toNat_ofNat] using (by assumption : _)
          rwa [Nat.mod_eq_of_lt (by omega : ui < 2 ^ 64), Nat.mod_eq_of_lt hng_lt64] at h1
        have hui_mc : (BitVec.ofNat 64 ui).toNat < mclr1.length := by
          rw [bv64_ofNat_toNat (by omega), hmclr1_l]; omega
        let ml := mclr1[(BitVec.ofNat 64 ui).toNat]'hui_mc
        have hml_eq : ml = mclr1[ui]'(by rw [hmclr1_l]; omega) :=
          getElem_eq_of_idx (bv64_ofNat_toNat (by omega))
        have hml_le : ml.toNat ≤ s.core.cur_level := by
          have h1 := (hmclr1_b ui hui_lt).1
          rwa [List.getElem?_eq_getElem (by rw [hmclr1_l]; omega), Option.getD_some, ← hml_eq] at h1
        have hml_f : (ml.setWidth 64).toNat < ftrlU.length := by
          rw [bv_c0_zext32_64, hfu_l]; omega
        have hml_orig : ftrlU[ml.toNat]'(by rw [hfu_l]; omega) =
            (s.core.frame_trail[ml.toNat]?.getD 0#32) ||| 0x80000000#32 := by
          have hmem : ml.toNat ∈ ((mclr1.take ng).drop ui).map BitVec.toNat := by
            rw [List.mem_map]; refine ⟨ml, ?_, rfl⟩
            rw [List.mem_iff_getElem]; refine ⟨0, by simp [hmclr1_l]; omega, ?_⟩
            simp [hml_eq]
          have hget := hfu_le ml.toNat hml_le
          rw [ite_eq_left hmem, List.getElem?_eq_getElem (by rw [hfu_l]; omega)] at hget
          exact Option.some.inj hget
        have hclr_val : (ftrlU[(ml.setWidth 64).toNat]'hml_f &&& 0x7FFFFFFF#32) =
            s.core.frame_trail[ml.toNat]?.getD 0#32 := by
          rw [getElem_eq_of_idx (hj := by rw [hfu_l]; omega)
            (bv_c0_zext32_64 ml), hml_orig]
          exact rsn_bv32_or_and_clear (hftrl_b31 ml.toNat hml_le)
        have hml_notin : ml.toNat ∉ ((mclr1.take ng).drop (ui + 1)).map BitVec.toNat := by
          intro hmem
          have hnd_drop : (((mclr1.take ng).drop ui).map BitVec.toNat).Nodup := by
            rw [List.map_drop]; exact List.Pairwise.drop hnd1
          have hcons : ((mclr1.take ng).drop ui).map BitVec.toNat =
              ml.toNat :: ((mclr1.take ng).drop (ui + 1)).map BitVec.toNat := by
            have hlt_t : ui < (mclr1.take ng).length := by simp [hmclr1_l]; omega
            rw [List.drop_eq_getElem_cons hlt_t, List.map_cons, List.getElem_take, ← hml_eq]
          rw [hcons, List.nodup_cons] at hnd_drop
          exact hnd_drop.1 hmem
        c0_hsteps
        let ftrlU' := ftrlU.set ml.toNat (s.core.frame_trail[ml.toNat]?.getD 0#32)
        have hui1_bv : BitVec.ofNat 64 ui + 1#64 = BitVec.ofNat 64 (ui + 1) := by
          apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
        rw [show (1 : BitVec 64) = 1#64 from rfl, hui1_bv]
        refine ihu (ui + 1, ftrlU') _ (by dsimp only; omega)
          ⟨by omega, by simp [ftrlU', hfu_l], fun l hl => ?_, fun l hl => ?_, ?_⟩
        · dsimp only [ftrlU']
          by_cases hlm : l = ml.toNat
          · subst hlm; rw [List.getElem?_set_self (by rw [hfu_l]; omega), ite_eq_right hml_notin,
              List.getElem?_eq_getElem (by rw [hftrl_len]; omega), Option.getD_some]
          · rw [List.getElem?_set_ne (Ne.symm hlm), hfu_le l hl]
            have hlt_t : ui < (mclr1.take ng).length := by simp [hmclr1_l]; omega
            have hcons : ((mclr1.take ng).drop ui).map BitVec.toNat =
                ml.toNat :: ((mclr1.take ng).drop (ui + 1)).map BitVec.toNat := by
              rw [List.drop_eq_getElem_cons hlt_t, List.map_cons, List.getElem_take, ← hml_eq]
            simp only [hcons, List.mem_cons, hlm, false_or]
        · dsimp only [ftrlU']; rw [List.getElem?_set_ne (by omega)]; exact hfu_gt l hl
        · have hfu_eq : ftrlU.set (ml.setWidth 64).toNat
              (ftrlU[(ml.setWidth 64).toNat]'hml_f &&& 0x7FFFFFFF#32) = ftrlU' := by
            rw [hclr_val, bv_c0_zext32_64]
          simpa only [ftrlU', ← hfu_eq,
            show (2147483647 : BitVec 32) = 0x7FFFFFFF#32 from rfl] using hm
      · have hui_eq : ui = ng := by
          have h1 : ¬ ui % 2 ^ 64 < ng % 2 ^ 64 := by
            simpa only [BitVec.toNat_ofNat] using (by assumption : _)
          rw [Nat.mod_eq_of_lt (by omega : ui < 2 ^ 64), Nat.mod_eq_of_lt hng_lt64] at h1
          omega
        have hftrl_restored : ftrlU = s.core.frame_trail := by
          apply List.ext_getElem?; intro l
          by_cases hl : l ≤ s.core.cur_level
          · rw [hfu_le l hl, hui_eq]
            have hempty : (mclr1.take ng).drop ng = [] :=
              List.drop_eq_nil_of_le (by simp [hmclr1_l]; omega)
            rw [hempty]; rfl
          · exact hfu_gt l (by omega)
        rw [hftrl_restored] at hmu
        have hlen_m1 : ({ s with core := { s.core with min_clr := mclr1 } } :
            FullState).LengthsOk c :=
          ⟨{ hlen.core_ok with min_clr_len_arr := hmclr1_l }, hlen.scratch_ok⟩
        have hw_m1 := rsn_witness_set_minClr mclr1 hw
        refine wp_unroll_group fun _ _ => ?_
        c0_hsteps_nogrp
        · have hng_lt19 : ng < 2 ^ 19 := Nat.lt_of_le_of_lt hng_gl hglue0_lt
          have hng_bv32 : ((BitVec.ofNat 64 ng).setWidth 32).toNat < 2 ^ 19 := by
            rw [BitVec.toNat_setWidth, bv64_ofNat_toNat hng_lt64,
              Nat.mod_eq_of_lt (by omega)]; exact hng_lt19
          have hup := hdrBitsUpdate_preserves_fullWitnessCut hlen_m1.core_ok hw_m1 href
            (fun x => (x &&& 0xFFF80000#32) ||| (BitVec.ofNat 64 ng).setWidth 32)
            s.core.arena_garbage s.core.num_irred s.core.num_redundant
            (rsn_bv32_glue_bit _ _ 0x00080000#32 (b := 19) (by omega) rfl rfl hng_bv32)
            (rsn_bv32_glue_bit _ _ 0x00800000#32 (b := 23) (by omega) rfl rfl hng_bv32)
          let hdr' := (fullArenaHdrCore s.core rsn.toNat &&& 0xFFF80000#32) |||
            (BitVec.ofNat 64 ng).setWidth 32
          let arena0 := s.core.arena.set rsn.toNat hdr'
          have har_eq : s.core.arena.set (rsn.setWidth 64).toNat
              ((s.core.arena[(rsn.setWidth 64).toNat]'hrsn_z_lt &&& ~~~(524287 : BitVec 32)) |||
                (BitVec.ofNat 64 ng).setWidth 32) = arena0 := by
            rw [hhdr_z, bv_c0_zext32_64]; rfl
          have hset : arena0[rsn.toNat]? = some ((s.core.arena[(rsn.setWidth 64).toNat]'
              hrsn_z_lt &&& ~~~(524287 : BitVec 32)) |||
              (BitVec.ofNat 64 ng).setWidth 32) := by
            dsimp only [arena0, hdr']; rw [List.getElem?_set_self hrsn_lt, hhdr_z]; rfl
          exact hJg (_, BitVec.ofNat 64 ng, ()) _
            ⟨arena0, mclr1, hset, hup.1,
             ⟨{ hlen_m1.core_ok with arena_len_arr := by simp [arena0, har_len] }, hlen.scratch_ok⟩,
             hup.2.1, hup.2.2, fun k _ => List.getElem?_set_ne (by omega),
             by simpa only [← har_eq] using hm⟩
        all_goals exact hJg (_, _, ()) mu ⟨s.core.arena, mclr1, hrsn_get, hw_m1, hlen_m1, rfl,
          fun _ _ => ⟨rfl, rfl, rfl⟩, fun _ _ => rfl, hmu⟩
    · rintro B L ⟨ng, k, ftrlK, mclrK⟩ ml hB hL ⟨hk_le, hng_lt_gl, hgiK, hml⟩
      obtain ⟨hng_cv, hng_gl, hftrlK_l, hmclrK_l, hmclrK_b, hndK, hftrlK_le, hftrlK_gt⟩ := hgiK
      have hng_lt64 : ng < 2 ^ 64 := by omega
      dsimp only at hk_le hng_lt_gl hB hL hml
      c0_hsteps_nogrp
      · have hk_lt : k.toNat < sz := by
          have h1 : k.toNat < (s.core.arena[(rsn.setWidth 64 + 2#64).toNat]'(
              by rw [hsz_idx]; omega)).toNat := BitVec.lt_def.mp ‹_›
          rwa [hsz_at, hsz_get] at h1
        have hk1 : (k + 1#32).toNat = k.toNat + 1 := by bv_omega
        have har_k_lt : (rsn.setWidth 64 + 3 + k.setWidth 64).toNat < s.core.arena.length := by
          have h3 : (rsn.setWidth 64 + 3).toNat = rsn.toNat + 3 := by bv_omega
          rw [BitVec.toNat_add, h3, BitVec.toNat_setWidth,
            Nat.mod_eq_of_lt (by omega : k.toNat < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]
          have hk_c : k.toNat < fullArenaClauseSizeCore s.core rsn.toNat := hk_lt; omega
        c0_hsteps_nogrp
        refine wp_join_group (ts := [i64])
          (fun (ng', ()) mn => ∃ ftrl' mclr',
            ng' = BitVec.ofNat 64 ng'.toNat ∧ ng'.toNat < glue0.toNat ∧
            glueInv ng'.toNat ftrl' mclr' ∧
            (FullMem c { s with core := { s.core with
              frame_trail := ftrl', min_clr := mclr' } } ⋆
              (m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R)) mn)
          (fun _ (ng', ()) mn ⟨ftrl', mclr', hng'_eq, hng'_lt, hgi', hmn⟩ => by
            rw [Blocks.get_here]; dsimp only; c0_hsteps
            have hstep := hL (ng'.toNat, k + 1#32, ftrl', mclr') mn
              (by dsimp only; rw [hk1]; omega) ⟨by rw [hk1]; omega, hng'_lt, hgi', hmn⟩
            simpa only [← hng'_eq, show (1 : BitVec 32) = 1#32 from rfl] using hstep)
          (fun Jstep hJstep => ?_)
        have hJsame : Jstep (BitVec.ofNat 64 ng, ()) ml :=
          hJstep (BitVec.ofNat 64 ng, ()) ml
            ⟨ftrlK, mclrK, by rw [bv64_ofNat_toNat hng_lt64],
             by rw [bv64_ofNat_toNat hng_lt64]; exact hng_lt_gl,
             by rw [bv64_ofNat_toNat hng_lt64]
                exact ⟨hng_cv, hng_gl, hftrlK_l, hmclrK_l, hmclrK_b, hndK, hftrlK_le, hftrlK_gt⟩,
             hml⟩
        c0_hsteps_nogrp
        · let kv_bv := (s.core.arena[(rsn.setWidth 64 + 3 +
              k.setWidth 64).toNat]'har_k_lt >>> (1 : BitVec 32)).setWidth 64
          have hidx_eq : (rsn.setWidth 64 + 3 + k.setWidth 64).toNat =
              (rsn.toNat + (3 : BitVec 64).toNat + k.toNat) % 2 ^ 64 := by bv_omega
          have hkv_eq : kv_bv.toNat =
              (s.core.arena[(rsn.toNat + (3 : BitVec 64).toNat + k.toNat) % 2 ^ 64]'(
                hidx_eq ▸ har_k_lt)).toNat / 2 := by
            dsimp only [kv_bv]; rw [bv_c0_zext32_64,
              show ∀ x : BitVec 32, (x >>> (1 : BitVec 32)).toNat = x.toNat / 2 from
                fun x => bv32_lshr_1 x,
              getElem_eq_of_idx (hj := hidx_eq ▸ har_k_lt) hidx_eq]
          have hkv_lt : kv_bv.toNat < s.core.cur_vars := by
            rw [hkv_eq]
            have h1 : (s.core.arena[(rsn.toNat + (3 : BitVec 64).toNat + k.toNat) % 2 ^ 64]'(
                hidx_eq ▸ har_k_lt)).toNat / 2 < s.core.cur_vars % 2 ^ 64 := by assumption
            rwa [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)] at h1
          have hkv_lvl : kv_bv.toNat < s.core.lvl.length := by rw [hlvl_len]; omega
          let kl_bv := (s.core.lvl[kv_bv.toNat]'hkv_lvl).setWidth 64
          have hkl_nat : kl_bv.toNat = (s.core.lvl[kv_bv.toNat]'hkv_lvl).toNat := bv_c0_zext32_64 _
          have hkl_eq : kl_bv.toNat =
              (s.core.lvl[(s.core.arena[(rsn.toNat + (3 : BitVec 64).toNat + k.toNat) % 2 ^ 64]'(
                hidx_eq ▸ har_k_lt)).toNat / 2]'(hkv_eq ▸ hkv_lvl)).toNat := by
            rw [hkl_nat, getElem_eq_of_idx (hj := hkv_eq ▸ hkv_lvl) hkv_eq]
          c0_hsteps_nogrp
          refine wp_unroll_group fun _ _ => ?_
          c0_hsteps_nogrp
          · have hkl_le : kl_bv.toNat ≤ s.core.cur_level := by
              rw [hkl_eq]
              have h1 : (s.core.lvl[(s.core.arena[(rsn.toNat + (3 : BitVec 64).toNat + k.toNat) %
                  2 ^ 64]'(hidx_eq ▸ har_k_lt)).toNat / 2]'(hkv_eq ▸ hkv_lvl)).toNat ≤
                  s.core.cur_level % 2 ^ 64 := by assumption
              rwa [Nat.mod_eq_of_lt (by omega : s.core.cur_level < 2 ^ 64)] at h1
            have hkl_f : kl_bv.toNat < ftrlK.length := by rw [hftrlK_l]; omega
            c0_hsteps_nogrp
            · have hkl_notin : kl_bv.toNat ∉ (mclrK.take ng).map BitVec.toNat := by
                intro hmem
                have hget := hftrlK_le kl_bv.toNat hkl_le
                rw [ite_eq_left hmem, List.getElem?_eq_getElem hkl_f] at hget
                have hval := Option.some.inj hget
                have hzero : (ftrlK[kl_bv.toNat]'hkl_f &&& 0x80000000#32) = 0#32 := by
                  rw [getElem_eq_of_idx (hj := hkl_eq ▸ hkl_f) hkl_eq]
                  simpa only [show (2147483648 : BitVec 32) = 0x80000000#32 from rfl,
                    show (0 : BitVec 32) = 0#32 from rfl] using (by assumption : _)
                rw [hval] at hzero
                exact rsn_bv32_or_bit31_ne0 _ hzero
              have hkl_in_vals : kl_bv.toNat ∈ lvlVals := by
                rw [List.mem_map]; refine ⟨kv_bv.toNat, List.mem_range.mpr hkv_lt, ?_⟩
                rw [List.getElem?_eq_getElem hkv_lvl, Option.getD_some, hkl_nat]
              have hng_lt_cv : ng < s.core.cur_vars := by
                have hnd_new : (kl_bv.toNat :: (mclrK.take ng).map BitVec.toNat).Nodup :=
                  List.nodup_cons.mpr ⟨hkl_notin, hndK⟩
                have hsub_new : ∀ x ∈ kl_bv.toNat :: (mclrK.take ng).map BitVec.toNat,
                    x ∈ lvlVals := fun x hx => by
                  rcases List.mem_cons.mp hx with rfl | hxm
                  · exact hkl_in_vals
                  · rw [List.mem_map] at hxm; obtain ⟨w, hw, rfl⟩ := hxm
                    rw [List.mem_iff_getElem] at hw; obtain ⟨j, hj, rfl⟩ := hw
                    simp only [List.length_take, hmclrK_l] at hj
                    have h1 := (hmclrK_b j (by omega)).2
                    rw [List.getElem_take]
                    rwa [List.getElem?_eq_getElem (by rw [hmclrK_l]; omega), Option.getD_some] at h1
                have hle := rsn_nodup_length_le_of_subset _ lvlVals hnd_new hsub_new
                simp only [List.length_cons, List.length_map, List.length_take, hmclrK_l,
                  hlvlVals_len] at hle
                omega
              have hng_mc : (BitVec.ofNat 64 ng).toNat < mclrK.length := by
                rw [bv64_ofNat_toNat hng_lt64, hmclrK_l]; omega
              have hkl_orig : ftrlK[kl_bv.toNat]'hkl_f =
                  s.core.frame_trail[kl_bv.toNat]?.getD 0#32 := by
                have hget := hftrlK_le kl_bv.toNat hkl_le
                rw [ite_eq_right hkl_notin, List.getElem?_eq_getElem hkl_f,
                  List.getElem?_eq_getElem (by rw [hftrl_len]; omega)] at hget
                rw [List.getElem?_eq_getElem (by rw [hftrl_len]; omega), Option.getD_some]
                exact Option.some.inj hget
              have hng1_bv : (BitVec.ofNat 64 ng + 1#64).toNat = ng + 1 := by
                rw [BitVec.toNat_add, bv64_ofNat_toNat hng_lt64,
                  show (1#64 : BitVec 64).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
              let ftrlK' := ftrlK.set kl_bv.toNat ((ftrlK[kl_bv.toNat]'hkl_f) ||| 0x80000000#32)
              let mclrK' := mclrK.set ng (kl_bv.setWidth 32)
              have hkl32 : (kl_bv.setWidth 32).toNat = kl_bv.toNat := by
                rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
              have htake' : (mclrK'.take (ng + 1)).map BitVec.toNat =
                  (mclrK.take ng).map BitVec.toNat ++ [kl_bv.toNat] := by
                dsimp only [mclrK']
                rw [rsn_take_set_eq_take _ (by rw [hmclrK_l]; omega), List.map_append,
                  List.map_singleton, hkl32]
              have hgi_step : ng + 1 ≤ glue0.toNat → glueInv (ng + 1) ftrlK' mclrK' := fun hle_gl =>
                ⟨by omega, hle_gl, by simp [ftrlK', hftrlK_l], by simp [mclrK', hmclrK_l],
                 fun j hj => by
                  dsimp only [mclrK']
                  rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hlt | rfl
                  · rw [List.getElem?_set_ne (by omega)]; exact hmclrK_b j hlt
                  · rw [List.getElem?_set_self (by rw [hmclrK_l]; omega), Option.getD_some, hkl32]
                    exact ⟨hkl_le, hkl_in_vals⟩,
                 by rw [htake', List.nodup_append]
                    exact ⟨hndK, by simp, fun a ha b hb => by
                      simp only [List.mem_singleton] at hb; subst hb
                      exact fun heq => hkl_notin (heq ▸ ha)⟩,
                 fun l hl => by
                  dsimp only [ftrlK']; rw [htake']
                  by_cases hlk : l = kl_bv.toNat
                  · subst hlk; rw [List.getElem?_set_self hkl_f, hkl_orig, ite_eq_left (by simp)]
                  · rw [List.getElem?_set_ne (Ne.symm hlk), hftrlK_le l hl]; simp [hlk],
                 fun l hl => by
                  dsimp only [ftrlK']; rw [List.getElem?_set_ne (by omega)]; exact hftrlK_gt l hl⟩
              have hsh32 : ∀ x : BitVec 32, x >>> (1 : BitVec 32) = x >>> (1 : Nat) := fun _ => rfl
              c0_hsteps_nogrp
              · have hng1_eq : ng + 1 = glue0.toNat := by
                  have h1 : (s.core.arena[rsn.toNat]'hrsn_lt &&& 524287#32).toNat ≤
                      (ng + (1 : BitVec 64).toNat) % 2 ^ 64 := by
                    rw [DeduceTactics.ded_bv32_mask_glue19_toNat]; assumption
                  rw [hglue0_eq, show (1 : BitVec 64).toNat = 1 from rfl,
                    Nat.mod_eq_of_lt (by omega)] at h1; omega
                c0_hsteps
                rw [show BitVec.ofNat 64 ng + 1 = BitVec.ofNat 64 (ng + 1) from
                  BitVec.eq_of_toNat_eq (by
                    rw [show (1 : BitVec 64) = 1#64 from rfl, hng1_bv, bv64_ofNat_toNat
                      (by omega)])]
                exact hB (ng + 1, k, ftrlK', mclrK') _ ⟨hgi_step (by omega), by
                  have hm_eq : mclrK.set (BitVec.ofNat 64 ng).toNat (kl_bv.setWidth 32) = mclrK' :=
                    by rw [bv64_ofNat_toNat hng_lt64]
                  simpa only [ftrlK', kl_bv, kv_bv, hsh32, ← hm_eq,
                    show (2147483648 : BitVec 32) = 0x80000000#32 from rfl] using hm⟩
              · have hng1_lt : ng + 1 < glue0.toNat := by
                  have h1 : ¬ (s.core.arena[rsn.toNat]'hrsn_lt &&& 524287#32).toNat ≤
                      (ng + (1 : BitVec 64).toNat) % 2 ^ 64 := by
                    rw [DeduceTactics.ded_bv32_mask_glue19_toNat]; assumption
                  rw [hglue0_eq, show (1 : BitVec 64).toNat = 1 from rfl,
                    Nat.mod_eq_of_lt (by omega)] at h1; omega
                c0_hsteps
                refine hJstep (BitVec.ofNat 64 ng + 1#64, ()) _ ⟨ftrlK', mclrK',
                  BitVec.eq_of_toNat_eq (by rw [hng1_bv, bv64_ofNat_toNat (by omega)]),
                  hng1_bv ▸ hng1_lt, hng1_bv ▸ hgi_step (by omega), ?_⟩
                have hm_eq : mclrK.set (BitVec.ofNat 64 ng).toNat (kl_bv.setWidth 32) = mclrK' :=
                  by rw [bv64_ofNat_toNat hng_lt64]
                simpa only [ftrlK', kl_bv, kv_bv, hsh32, ← hm_eq,
                  show (2147483648 : BitVec 32) = 0x80000000#32 from rfl] using hm
            · exact hJsame
          · exact hJsame
        · exact hJsame
      · exact hB (ng, k, ftrlK, mclrK) ml
          ⟨⟨hng_cv, hng_gl, hftrlK_l, hmclrK_l, hmclrK_b, hndK, hftrlK_le, hftrlK_gt⟩, hml⟩
    · intro B L _ hL; c0_hsteps
      exact hL (0, 0#32, s.core.frame_trail, s.core.min_clr) m
        ⟨Nat.zero_le _, by omega, ⟨Nat.zero_le _, Nat.zero_le _, hftrl_len, hmclr_len,
          fun _ h => by omega, by simp, fun _ _ => by simp, fun _ _ => rfl⟩, hmf⟩
  · exact hJg (_, _, ()) m ⟨s.core.arena, s.core.min_clr, hrsn_get, hw, hlen, rfl,
      fun _ _ => ⟨rfl, rfl, rfl⟩, fun _ _ => rfl, hmf⟩

/-! ## 4. `full_analyze_rsn_m6_hdr_wp` (`Spec.s13AnalyzeRsnHdrSpec`) -/

/-- Canonical `Func.wp` proof for `full_analyze_rsn_m6_hdr` (`Spec.s13AnalyzeRsnHdrSpec`). -/
theorem full_analyze_rsn_m6_hdr_wp (Γ : Env)
    (hLit : Γ.Has "full_analyze_lit" Spec.fullAnalyzeLitSpec)
    (hRec : Γ.Has "m6_hdr_record_used" (m6HdrW2aSpec [i64] [])) :
    ∀ a m Q X, Spec.s13AnalyzeRsnHdrSpec a m Q X →
      Func.wp Γ full_analyze_rsn_m6_hdr_body a m Q X := by
  rintro ⟨h, rsn, skip_var, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, cut, ext, s, R, rfl, hcfg, hext, hlen, hw, hwork, htl_cv, htc_fit,
      hrsn_ref, hm, hQ⟩
  have hmax32 := fullInv_max_vars_lt32 c; have hcv_le := hlen.core_ok.cur_vars_le
  have har_len := hlen.core_ok.arena_len_arr; have har_le := hlen.core_ok.arena_len_le
  have hcur32 : s.core.cur_level < 2 ^ 32 := by
    have := hw.cur_level_le; have := hlen.core_ok.trail_end_le; omega
  have hret_false_same : Q (false, ()) m := hQ false s.core.mrk s.core.tmp s.core.min_clr
    s.core.tmp_cnt s.core.tmp_len s.core.min_clr_len s.core.arena s.scratch ext m hext
    (fun _ => M6ExtW2bPres.refl ext) hlen hw hwork ⟨rfl, rfl⟩ rfl (Nat.le_refl _) htl_cv
    (Nat.le_refl _) rfl (fun _ _ => ⟨rfl, rfl, rfl⟩) (fun _ _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ h0 h => absurd h0 h) (fun _ h1 h2 => by omega) (fun _ _ _ h1 h2 => by omega)
    (by rw [Nat.sub_self, filter_length_eq_zero_of_false]; intro _ _; simp)
    (by rw [filter_length_eq_zero_of_false (fun _ _ => by simp)]; simp) (fun hc => by cases hc) hm
  unfold Func.wp full_analyze_rsn_m6_hdr_body; dsimp only
  c0_hsteps_nogrp; · exact hret_false_same
  · have hne : rsn ≠ 0xFFFFFFFF#32 := by assumption
    have hbin : (rsn &&& 0x80000000#32) ≠ 0#32 := by assumption
    refine wp_m6Hdr_focus_frame hm fun hmf => ?_; c0_hsteps_nogrp; c0_call hLit
    refine ⟨c, s, m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R, rfl, hlen, hcur32, htl_cv, by omega,
      hwork, hmf, fun ok mrk' tmp' tc' tl' mcl' ws1' ant' res' m' hlen' hwork' htl_ge htl_le1
        htl_cv' htc_ge hant' hres' htc_eq hmpres htpres hnewm hnewt hok hm' => ?_⟩
    c0_hsteps_nogrp
    have hsame_c : FullWitnessCutInv c F0 F_cur cut { s.core with
        mrk := mrk', tmp := tmp', tmp_cnt := tc', tmp_len := tl', min_clr_len := mcl' } :=
      ⟨{ hw.toFullOtfsWitnessInv with
          arena := { hw.arena with len_ok := hw.arena.len_ok }
          watches := hw.watches.with_wstk rfl rfl rfl rfl rfl fun _ hr => hr },
        hw.cut_le, hw.reason_inv_cut, hw.reason_lit_mem_cut⟩
    have htc_f := filter_step_of_lit
      (fun w => decide ((s.core.lvl[w]?.getD 0#32).toNat = s.core.cur_level))
      (mv := s.core.cur_vars) (tc0 := s.core.tmp_cnt) (tc1 := s.core.tmp_cnt) (tc2 := tc')
      (v := (rsn &&& 0x7FFFFFFF#32).toNat / 2) (fun _ _ _ => rfl)
      (fun w hw => hmpres w (Nat.lt_of_lt_of_le hw hcv_le))
      (fun w hw_lt h0 hnz => (hnewm w (Nat.lt_of_lt_of_le hw_lt hcv_le) h0 hnz).1)
      (Nat.le_refl _) (by rw [Nat.sub_self, filter_length_eq_zero_of_false]; intro _ _; simp)
      (by rw [htc_eq]; congr 1; exact ite_congr (propext (by simp only [BitVec.ofNat_eq_ofNat,
        decide_eq_true_eq])) (fun _ => rfl) (fun _ => rfl))
    have hres_f := res_step_of_lit (mv := s.core.cur_vars)
      (v := (rsn &&& 0x7FFFFFFF#32).toNat / 2) (r0 := s.scratch.res_sz) (r1 := s.scratch.res_sz)
      (fun _ _ _ => rfl) (fun w hw => hmpres w (Nat.lt_of_lt_of_le hw hcv_le))
      (fun w hw_lt h0 hnz => (hnewm w (Nat.lt_of_lt_of_le hw_lt hcv_le) h0 hnz).1)
      (by rw [filter_length_eq_zero_of_false (fun _ _ => by simp)]; simp) hres'
    refine hQ ok mrk' tmp' s.core.min_clr tc' tl' mcl' s.core.arena _ ext m' hext
      (fun _ => M6ExtW2bPres.refl ext) hlen' hsame_c hwork' ⟨rfl, rfl⟩ rfl htl_ge htl_cv'
      htc_ge rfl (fun _ _ => ⟨rfl, rfl, rfl⟩) hmpres htpres (fun v hv h0 hnz => by
        obtain ⟨i, hi, heqv⟩ := hwork'.2.2.2 v hv hnz; have hvlt := (hwork'.2.2.1 i hi).1
        dsimp only at hvlt heqv; rw [heqv] at hvlt
        obtain ⟨rfl, _, hne', hpos, hle⟩ := hnewm v hv h0 hnz
        exact ⟨(rsn &&& 0x7FFFFFFF#32).toNat, (rsn_mem_fullRsnLits_bin hne hbin).mpr
          rfl, rfl, hvlt, hne', hpos, hle⟩) ?_ (fun _ _ _ h1 h2 => by omega) htc_f hres_f ?_
      (fullM6HdrMem_unfocus hm')
    · intro j hj1 hj2; obtain ⟨heq, _, _, h0, hpos, hcl, hmk⟩ := hnewt j hj1 hj2
      exact ⟨(rsn_mem_fullRsnLits_bin hne hbin).mpr heq, by omega, by omega,
        by rwa [heq], by rwa [heq], by rwa [heq], by rwa [heq]⟩
    · intro hok'; obtain ⟨hvlt, hrest⟩ := hok hok'; refine ⟨hne, ?_, fun l hl => ?_⟩
      · rw [hant', fullRsnLits, ite_eq_right (fun h => hne h), ite_eq_left hbin, List.countP_cons,
          List.countP_nil, Nat.zero_add]
        exact congrArg (s.scratch.ant_sz + ·)
          (bv64_ite_iff (by simp only [decide_eq_true_eq]; rfl))
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
      have hsw : (rsn.setWidth 64).toNat = rsn.toNat := by rw [BitVec.toNat_setWidth]; omega
      rw [BitVec.toNat_add, hsw, show (2#64).toNat = 2 from rfl, Nat.mod_eq_of_lt (by omega)]
    have hsz_get : (s.core.arena[rsn.toNat + 2]'(by omega)).toNat =
        fullArenaClauseSize s rsn.toNat := by
      unfold fullArenaClauseSize fullArenaClauseSizeCore
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    have hhdr_get : s.core.arena[rsn.toNat]'hrsn_lt = fullArenaHdrCore s.core rsn.toNat := by
      unfold fullArenaHdrCore; simp [List.getElem?_eq_getElem hrsn_lt]
    refine wp_m6Hdr_focus_frame hm fun hmf => ?_
    c0_hsteps_nogrp; all_goals try exact hret_false_same
    c0_hsteps_nogrp; all_goals try exact hret_false_same
    c0_hsteps_nogrp; all_goals try exact hret_false_same
    refine wp_join_group (ts := [i32]) (fun (_ : Tup Val [i32]) m1 =>
        ∃ (arena1 mclr1 : List (BitVec 32)) (sc1 : FullScratch) (ext1 : List (BitVec 64)),
        let s1 : FullState :=
          { s with core := { s.core with arena := arena1, min_clr := mclr1 }, scratch := sc1 }
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
    · rintro _ ⟨_hdr, ⟨⟩⟩ m1 ⟨arena1, mclr1, sc1, ext1, hext1, hwb1, hw1, hlen1, hexp1, hws1, hws2,
        hant1, hres1, hrefs1, hcl1, har1_eq, hm1⟩
      have hsz_lt_len : (rsn.setWidth 64 + 2#64).toNat < s.core.arena.length := by
        have := hlen.core_ok.arena_len_le; rw [hsz_idx]; omega
      c0_hsteps_nogrp
      exact rsn_lit_loop rfl hLit hext1 hwb1 hlen hwork htl_cv htc_fit hcv_le hcur32 hne
        hlarge hbd hbd_le hsz_idx hsz_lt_len rfl hw1 hlen1 hexp1 hws1 hws2 hant1 hres1 hrefs1 hcl1
        har1_eq hm1 hQ
    · intro Jred hJred; c0_hsteps_nogrp
      · refine wp_join_group (ts := [i32, i64]) (RsnGluePred c F0 F_cur cut ext s R rsn) ?_ ?_
        · rintro _ ⟨hdr1, glue1, ⟨⟩⟩ m0 ⟨arena0, mclr0, hget0, hw0, hlen0, hrefs0, hcl0,
            har0_eq, hm0⟩
          have har0_len : arena0.length = c.arena_cap := hlen0.core_ok.arena_len_arr
          let s0 : FullState := { s with core := { s.core with arena := arena0, min_clr := mclr0 } }
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
                  { core := { s.core with arena := arena2, min_clr := mclr0 },
                    scratch := s1.scratch }
                FullWitnessCutInv c F0 F_cur cut s2.core ∧ s2.core.LengthsOk c ∧
                fullArenaClauseRefs s2 = fullArenaClauseRefs s ∧
                (∀ r ∈ fullArenaClauseRefs s, fullArenaClauseSize s2 r = fullArenaClauseSize s r ∧
                  fullArenaClauseGarb s2 r = fullArenaClauseGarb s r ∧
                  fullArenaClauseLits s2 r = fullArenaClauseLits s r) ∧
                (∀ k < fullArenaClauseSize s rsn.toNat,
                  arena2[rsn.toNat + 3 + k]? = s.core.arena[rsn.toNat + 3 + k]?) ∧
                (FullMem c s2 ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext1 ⋆ R)) m2) ?_ ?_
            · rintro _ ⟨⟩ m2 ⟨arena2, hw2, hlen2, hrefs2, hcl2, har2_eq, hm2⟩
              exact hJred (_, ()) m2 ⟨arena2, mclr0, s1.scratch, ext1, hext1, hwb1,
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
                    (m6ExtMem (m6ExtAddr c.hdr) ext1 ⋆ R)) m2 → Ju () m2 by
                clear hJu hLit hRec hQ hwork hw htl_cv htc_fit hrsn_ref hret_false_same hm hm0 hmf
                  hms1 hwb1 hext1 hl1 hw0 hlen0 hrefs0 hcl0 har0_eq
                  hget0 hc1 s0 har0_len arena0 mclr0
                c0_hsteps_nogrp
                · exact hdone _ _ (Or.inr rfl) (by assumption)
                · exact hdone s1.core.arena m1 (Or.inl rfl) hm1f
              rintro ar2 m2 (rfl | rfl) hm2
              · have hs1_eq : { core := { s.core with arena := arena0, min_clr := mclr0 },
                                scratch := s1.scratch } = s1 := by
                  cases s1; dsimp only at hc1; rw [hc1]
                exact hJu () m2
                  ⟨arena0, hw0, hlen0.core_ok, hrefs0, hcl0, har0_eq, by rwa [hs1_eq]⟩
              · have hrsn1_lt : rsn.toNat < arena0.length := by rw [har0_len]; omega
                have hbum := hdrBitsUpdate_preserves_fullWitnessCut hlen0.core_ok hw0
                  (hrefs0 ▸ (href : rsn.toNat ∈ fullArenaClauseRefs s))
                  (fun x => (x &&& 0x07FFFFFF#32) ||| (31#32 <<< 27)) s.core.arena_garbage
                  s.core.num_irred s.core.num_redundant (bv32_mask_usage_garb _ 31#32)
                  (bv32_mask_usage_shrk _ 31#32)
                have hhdr0_eq : hdr1 = fullArenaHdrCore
                    { s.core with arena := arena0, min_clr := mclr0 } rsn.toNat := by
                  unfold fullArenaHdrCore; rw [List.getElem?_eq_getElem hrsn1_lt] at hget0
                  rw [List.getElem?_eq_getElem hrsn1_lt, Option.getD_some]
                  exact (Option.some.inj hget0).symm
                let arena2 := arena0.set rsn.toNat ((fullArenaHdrCore
                  { s.core with arena := arena0, min_clr := mclr0 } rsn.toNat &&&
                    0x07FFFFFF#32) ||| (31#32 <<< 27))
                refine hJu () _ ⟨arena2, hbum.1, { hlen0.core_ok with
                    arena_len_arr := (by dsimp only [arena2]; rw [List.length_set, har0_len]) },
                  hbum.2.1.trans hrefs0, ?_, ?_, ?_⟩
                · intro r hr; have hr0 : r ∈ fullArenaClauseRefs _ := hrefs0 ▸ hr
                  obtain ⟨a, b, d⟩ := hbum.2.2 r hr0
                  exact ⟨a.trans (hcl0 r hr).1, b.trans (hcl0 r hr).2.1, d.trans (hcl0 r hr).2.2⟩
                · intro k hk; rw [List.getElem?_set_ne (by omega)]; exact har0_eq k hk
                · let arena3 := s1.core.arena.set (rsn.setWidth 64).toNat
                    ((hdr1 &&& 134217727#32) ||| 4160749568#32)
                  have har3_eq : arena3 = arena2 := by
                    dsimp only [arena3]; rw [hc1, bv_c0_zext32_64, hhdr0_eq]; rfl
                  have hs2_eq : FullState.mk { s.core with arena := arena2, min_clr := mclr0 }
                      s1.scratch = { s1 with core := { s1.core with arena := arena3 } } := by
                    rw [har3_eq]; cases s1; dsimp only at hc1 ⊢; rw [hc1]
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
          exact rsn_glue_recompute_wp (skip_var := skip_var) hlen hw href hsz3
            (Nat.le_trans hbd hbd_le) hsz_idx hrsn_lt hsz_get hhdr_get hmf hJg
      · exact hJred (_, ()) m ⟨s.core.arena, s.core.min_clr, s.scratch, ext, hext,
          fun _ => M6ExtW2bPres.refl ext, hw, hlen, fullExtScratchPres_refl s,
          rfl, rfl, rfl, rfl, rfl, fun _ _ => ⟨rfl, rfl, rfl⟩, fun _ _ => rfl, hmf⟩

end LeanQbe.T.Examples.Kissat.Proof.Deduce
