/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S4EVSIDSReorderProof0
public import LeanQbe.T.Examples.Kissat.FullM6OrchAdaptersProof1
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Fidelity Step 13 S4-A Proofs: `full_bump_analyzed_mode_fid` & `full_restore_bump_ana`

UNSAT-only, callee-parametric `Func.wp` proofs (`public section`, `0` `@[expose]` on theorems,
`0` `import all`, `XPost`-polymorphic) for:
1. `full_bump_analyzed_mode_fid` (`s13BumpAnalyzedModeSpecP M6ExtW2bPres`)
2. `full_restore_bump_ana_mode_fid` (`s13RestoreBumpAnaModeSpecP M6ExtW2bPres`)

Specs allow length-preserving `s.core.repr'` (`repr'.length = 2 * c.max_vars`) from `PERF-R3`
`full_sort_ana_qs_m6`, and relax the `allow_reasons = false` precondition so both `FullAnaMarksCov`
callers and post-Option-1B `FullMrkZero` callers compose seamlessly.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S4

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6ProofUtil
open LeanQbe.T.Examples.Kissat.FullM6MinShrink
open LeanQbe.T.Examples.Kissat.FullM6OrchAdapters
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.FullM6Hdr.M6HdrTactics
open Kraken.Bedrock2.Test

/-! ## 1. Step-13 Specifications (`s13BumpAnalyzedModeSpecP`, `s13RestoreBumpAnaModeSpecP`) -/

/-- Precondition on analyzed vars for `full_bump_analyzed_mode_fid(h, allow_reasons)`:
when `allow_reasons = true`, full `FullAnaMarksCov c s` is required; when `allow_reasons = false`,
only `min_clr_len ≤ cur_vars` and valid variable bounds in `work_stk1[0..min_clr_len)` hold. -/
def S13BumpPre (allow_reasons : Bool) (c : FullCfg) (s : FullState) : Prop :=
  if allow_reasons then FullAnaMarksCov c s
  else s.core.min_clr_len ≤ s.core.cur_vars ∧
    ∀ k < s.core.min_clr_len, (s.scratch.work_stk1[k]?.getD 0#32).toNat < s.core.cur_vars

theorem s13BumpPre_of_cov (allow_reasons : Bool) {c : FullCfg} {s : FullState}
    (hcov : FullAnaMarksCov c s) : S13BumpPre allow_reasons c s := by
  unfold S13BumpPre
  cases allow_reasons
  · exact ⟨hcov.1, fun k hk => (hcov.2.2.1 k hk).1⟩
  · exact hcov

theorem s13BumpPre_false_of {c : FullCfg} {s : FullState}
    (hmcl : s.core.min_clr_len ≤ s.core.cur_vars)
    (hlt : ∀ k < s.core.min_clr_len, (s.scratch.work_stk1[k]?.getD 0#32).toNat < s.core.cur_vars) :
    S13BumpPre false c s := by
  unfold S13BumpPre; exact ⟨hmcl, hlt⟩

/-- Step-13 `full_bump_analyzed_mode_fid(h, allow_reasons)` specification over `FullM6HdrMem`,
allowing length-preserving `s.core.repr'` from `PERF-R3` `full_sort_ana_qs_m6`. -/
def s13BumpAnalyzedModeSpecP (Pext : List (BitVec 64) → List (BitVec 64) → Prop) :
    Spec [i64, .bool] [] := fun (h, allow_reasons, ()) m Q _ =>
  ∃ (c : FullCfg) (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ s.LengthsOk c ∧
    S13BumpPre allow_reasons c s ∧ (FullM6HdrMem c ext s ⋆ R) m ∧
    ∀ mrk' mcl' repr' sc' ext' m',
      let s' : FullState :=
        { s with
          core := { s.core with mrk := mrk', min_clr_len := mcl', repr := repr' }
          scratch := sc' }
      s'.LengthsOk c →
      (FullAnaMarksCov c s → FullAnaMarksCov c s') →
      (allow_reasons = false → mrk' = s.core.mrk ∧ mcl' = s.core.min_clr_len ∧ ext' = ext) →
      (allow_reasons = false →
        ∀ k < mcl', (sc'.work_stk1[k]?.getD 0#32).toNat < s.core.cur_vars) →
      FullExtScratchPres s s' → sc'.work_stk2 = s.scratch.work_stk2 →
      M6HdrExtOk ext' → (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ Pext ext ext') →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q () m'

theorem s13BumpAnalyzedModeSpecP_monoX
    {Pext : List (BitVec 64) → List (BitVec 64) → Prop}
    {xs : Tup Val [i64, .bool]} {m : Mem 64} {Q : Post []} {X X' : XPost}
    (h : s13BumpAnalyzedModeSpecP Pext xs m Q X) :
    s13BumpAnalyzedModeSpecP Pext xs m Q X' := by
  rcases xs with ⟨_, _, ⟨⟩⟩; exact h

theorem s13BumpAnalyzedModeSpecP_of
    {Pext : List (BitVec 64) → List (BitVec 64) → Prop}
    {c : FullCfg} {ext : List (BitVec 64)} {s : FullState} {allow_reasons : Bool}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post []} {X : XPost}
    (hcfg : FullM6HdrCfgOk c) (hext : M6HdrExtOk ext) (hlen : s.LengthsOk c)
    (hpre : S13BumpPre allow_reasons c s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hQ : ∀ mrk' mcl' repr' sc' ext' m',
      let s' : FullState :=
        { s with
          core := { s.core with mrk := mrk', min_clr_len := mcl', repr := repr' }
          scratch := sc' }
      s'.LengthsOk c →
      (FullAnaMarksCov c s → FullAnaMarksCov c s') →
      (allow_reasons = false → mrk' = s.core.mrk ∧ mcl' = s.core.min_clr_len ∧ ext' = ext) →
      (allow_reasons = false →
        ∀ k < mcl', (sc'.work_stk1[k]?.getD 0#32).toNat < s.core.cur_vars) →
      FullExtScratchPres s s' → sc'.work_stk2 = s.scratch.work_stk2 →
      M6HdrExtOk ext' → (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ Pext ext ext') →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q () m') :
    s13BumpAnalyzedModeSpecP Pext (c.hdr, allow_reasons, ()) m Q X :=
  ⟨c, ext, s, R, rfl, hcfg, hext, hlen, hpre, hm, hQ⟩

theorem s13BumpAnalyzedModeSpecP_elim
    {Pext : List (BitVec 64) → List (BitVec 64) → Prop}
    {h : BitVec 64} {allow_reasons : Bool} {m : Mem 64} {Q : Post []} {X : XPost}
    (hs : s13BumpAnalyzedModeSpecP Pext (h, allow_reasons, ()) m Q X) :
    ∃ (c : FullCfg) (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ s.LengthsOk c ∧
      S13BumpPre allow_reasons c s ∧ (FullM6HdrMem c ext s ⋆ R) m ∧
      ∀ mrk' mcl' repr' sc' ext' m',
        let s' : FullState :=
          { s with
            core := { s.core with mrk := mrk', min_clr_len := mcl', repr := repr' }
            scratch := sc' }
        s'.LengthsOk c →
        (FullAnaMarksCov c s → FullAnaMarksCov c s') →
        (allow_reasons = false → mrk' = s.core.mrk ∧ mcl' = s.core.min_clr_len ∧ ext' = ext) →
        (allow_reasons = false →
          ∀ k < mcl', (sc'.work_stk1[k]?.getD 0#32).toNat < s.core.cur_vars) →
        FullExtScratchPres s s' → sc'.work_stk2 = s.scratch.work_stk2 →
        M6HdrExtOk ext' → (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ Pext ext ext') →
        (FullM6HdrMem c ext' s' ⋆ R) m' → Q () m' :=
  hs

/-- Step-13 `full_restore_bump_ana_mode_fid(h, allow_reasons)` specification over `FullM6HdrMem`,
allowing length-preserving `s.core.repr'` from `PERF-R3` `full_sort_ana_qs_m6`. -/
def s13RestoreBumpAnaModeSpecP (Pext : List (BitVec 64) → List (BitVec 64) → Prop) :
    Spec [i64, .bool] [] := fun (h, _allow_reasons, ()) m Q _ =>
  ∃ (c : FullCfg) (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ s.LengthsOk c ∧
    (∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 = 0#8) ∧
    (FullM6HdrMem c ext s ⋆ R) m ∧
    ∀ mrk' mcl' repr' sc' ext' m',
      let s' : FullState :=
        { core := { s.core with mrk := mrk', min_clr_len := mcl', repr := repr' }
          scratch := sc' }
      s'.LengthsOk c → (∀ v < c.max_vars, mrk'[v]?.getD 0#8 = 0#8) →
      (s.core.probing = 0#64 → mcl' = 0) →
      (s.core.probing ≠ 0#64 → mcl' = s.core.min_clr_len) →
      FullExtScratchPres s s' → sc'.work_stk2 = s.scratch.work_stk2 →
      M6HdrExtOk ext' → (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ Pext ext ext') →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q () m'

theorem s13RestoreBumpAnaModeSpecP_monoX
    {Pext : List (BitVec 64) → List (BitVec 64) → Prop}
    {xs : Tup Val [i64, .bool]} {m : Mem 64} {Q : Post []} {X X' : XPost}
    (h : s13RestoreBumpAnaModeSpecP Pext xs m Q X) :
    s13RestoreBumpAnaModeSpecP Pext xs m Q X' := by
  rcases xs with ⟨_, _, ⟨⟩⟩; exact h

theorem s13RestoreBumpAnaModeSpecP_of
    {Pext : List (BitVec 64) → List (BitVec 64) → Prop}
    {c : FullCfg} {ext : List (BitVec 64)} {s : FullState} {allow_reasons : Bool}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post []} {X : XPost}
    (hcfg : FullM6HdrCfgOk c) (hext : M6HdrExtOk ext) (hlen : s.LengthsOk c)
    (hmrk0 : ∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 = 0#8)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hQ : ∀ mrk' mcl' repr' sc' ext' m',
      let s' : FullState :=
        { core := { s.core with mrk := mrk', min_clr_len := mcl', repr := repr' }
          scratch := sc' }
      s'.LengthsOk c → (∀ v < c.max_vars, mrk'[v]?.getD 0#8 = 0#8) →
      (s.core.probing = 0#64 → mcl' = 0) →
      (s.core.probing ≠ 0#64 → mcl' = s.core.min_clr_len) →
      FullExtScratchPres s s' → sc'.work_stk2 = s.scratch.work_stk2 →
      M6HdrExtOk ext' → (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ Pext ext ext') →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q () m') :
    s13RestoreBumpAnaModeSpecP Pext (c.hdr, allow_reasons, ()) m Q X :=
  ⟨c, ext, s, R, rfl, hcfg, hext, hlen, hmrk0, hm, hQ⟩

theorem s13RestoreBumpAnaModeSpecP_elim
    {Pext : List (BitVec 64) → List (BitVec 64) → Prop}
    {h : BitVec 64} {allow_reasons : Bool} {m : Mem 64} {Q : Post []} {X : XPost}
    (hs : s13RestoreBumpAnaModeSpecP Pext (h, allow_reasons, ()) m Q X) :
    ∃ (c : FullCfg) (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ s.LengthsOk c ∧
      (∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 = 0#8) ∧
      (FullM6HdrMem c ext s ⋆ R) m ∧
      ∀ mrk' mcl' repr' sc' ext' m',
        let s' : FullState :=
          { core := { s.core with mrk := mrk', min_clr_len := mcl', repr := repr' }
            scratch := sc' }
        s'.LengthsOk c → (∀ v < c.max_vars, mrk'[v]?.getD 0#8 = 0#8) →
        (s.core.probing = 0#64 → mcl' = 0) →
        (s.core.probing ≠ 0#64 → mcl' = s.core.min_clr_len) →
        FullExtScratchPres s s' → sc'.work_stk2 = s.scratch.work_stk2 →
        M6HdrExtOk ext' → (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ Pext ext ext') →
        (FullM6HdrMem c ext' s' ⋆ R) m' → Q () m' :=
  hs

/-! ## 2. Private Helpers for `full_bump_analyzed_mode_fid` & `full_restore_bump_ana_mode_fid` -/

section BumpHelpers

attribute [local bv_c0] Bool.true_eq_false Bool.false_eq_true

private theorem s13b_bv32_lshr1 (x : BitVec 32) : (x >>> 1#32).toNat = x.toNat / 2 :=
  fl_bv32_lshr1 x

private theorem s13b_bv32_setWidth64 (x : BitVec 32) : (x.setWidth 64).toNat = x.toNat :=
  fl_bv32_setWidth64 x

private theorem s13b_sext32_64_1 : BitVec.signExtend 64 (1#32 : BitVec 32) = 1#64 := rfl

private theorem s13b_bv32_lshr_nat1 (x : BitVec 32) : (x >>> 1).toNat = x.toNat / 2 :=
  fl_bv32_lshr1 x

attribute [local bv_c0] s13b_bv32_lshr1 s13b_bv32_setWidth64 s13b_sext32_64_1 s13b_bv32_lshr_nat1

private theorem s13b_getElem_congr_list {α : Type} {xs ys : List α} (hl : xs = ys)
    {i j : Nat} (hi : i = j) {hix : i < xs.length} {hjy : j < ys.length} :
    xs[i]'hix = ys[j]'hjy := by
  subst hl hi; rfl

private theorem s13b_bv8_zext32_eq0_iff {x : BitVec 8} :
    BitVec.setWidth 32 x = 0#32 ↔ x = 0#8 := by
  constructor
  · intro h
    have ht := congrArg BitVec.toNat h
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega : x.toNat < 2 ^ 32),
      show (0#32 : BitVec 32).toNat = 0 from rfl] at ht
    exact BitVec.eq_of_toNat_eq ht
  · rintro rfl; rfl

private theorem s13b_nodup_of_getElem_ne {α : Type} :
    ∀ (xs : List α),
      (∀ i j (hi : i < xs.length) (hj : j < xs.length), i < j → xs[i] ≠ xs[j]) → xs.Nodup
  | [], _ => List.nodup_nil
  | _ :: _, h => by
    rw [List.nodup_cons]
    refine ⟨fun hx => ?_, s13b_nodup_of_getElem_ne _ fun i j hi hj hij =>
      h (i + 1) (j + 1) (Nat.succ_lt_succ hi) (Nat.succ_lt_succ hj) (Nat.succ_lt_succ hij)⟩
    obtain ⟨k, hk, hget⟩ := List.mem_iff_getElem.mp hx
    exact h 0 (k + 1) (Nat.zero_lt_succ _) (Nat.succ_lt_succ hk) (Nat.zero_lt_succ _) hget.symm

private theorem s13b_nodup_map_take_append {xs : List (BitVec 32)} {n : Nat} {v : BitVec 32}
    (hn : n < xs.length) (hnd : ((xs.take n).map BitVec.toNat).Nodup)
    (hmiss : ∀ k < n, (xs[k]?.getD 0#32).toNat ≠ v.toNat) :
    (((xs.set n v).take (n + 1)).map BitVec.toNat).Nodup := by
  refine s13b_nodup_of_getElem_ne _ fun i j hi hj hij => ?_
  simp only [List.length_map, List.length_take, List.length_set] at hi hj
  simp only [List.getElem_map, List.getElem_take]
  have hi_n : i < n := by omega
  rw [List.getElem_set_ne (by omega)]
  by_cases hj_n : j = n
  · subst hj_n; rw [List.getElem_set_self (by rw [List.length_set]; exact hn)]
    have hm := hmiss i hi_n
    rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at hm
  · rw [List.getElem_set_ne (by omega)]
    have hi_t : i < ((xs.take n).map BitVec.toNat).length := by
      simp only [List.length_map, List.length_take]; omega
    have hj_t : j < ((xs.take n).map BitVec.toNat).length := by
      simp only [List.length_map, List.length_take]; omega
    intro heq
    have hne := List.pairwise_iff_getElem.mp hnd i j hi_t hj_t hij
    simp only [List.getElem_map, List.getElem_take] at hne
    exact hne heq

private theorem s13b_nodup_take_pred {xs : List (BitVec 32)} {n : Nat}
    (hpos : 0 < n) (hnd : ((xs.take n).map BitVec.toNat).Nodup) :
    ((xs.take (n - 1)).map BitVec.toNat).Nodup := by
  refine s13b_nodup_of_getElem_ne _ fun i j hi hj hij => ?_
  simp only [List.length_map, List.length_take] at hi hj
  have hi_t : i < ((xs.take n).map BitVec.toNat).length := by
    simp only [List.length_map, List.length_take]; omega
  have hj_t : j < ((xs.take n).map BitVec.toNat).length := by
    simp only [List.length_map, List.length_take]; omega
  have hne := List.pairwise_iff_getElem.mp hnd i j hi_t hj_t hij
  simpa only [List.getElem_map, List.getElem_take] using hne

private abbrev bumpSt2 (s : FullState) (sc : FullScratch) (mrk : List (BitVec 8)) (mcl : Nat) :
    FullState :=
  { s with core := { s.core with mrk := mrk, min_clr_len := mcl }, scratch := sc }

private abbrev mkBumpState (s : FullState) (sc0 : FullScratch) (mrk : List (BitVec 8)) (mcl : Nat)
    (ws1 : List (BitVec 32)) (tk : BitVec 64) : FullState :=
  { s with
    core := { s.core with mrk := mrk, min_clr_len := mcl }
    scratch := { sc0 with work_stk1 := ws1, search_ticks := tk } }

private abbrev mkBumpStateR (s : FullState) (sc : FullScratch) (mrk : List (BitVec 8)) (mcl : Nat)
    (repr : List (BitVec 32)) : FullState :=
  { s with
    core := { s.core with mrk := mrk, min_clr_len := mcl, repr := repr }
    scratch := sc }

private theorem mkBumpState_lengths {c : FullCfg} {s : FullState} {sc0 : FullScratch}
    (hlen : ({ s with scratch := sc0 } : FullState).LengthsOk c)
    {mrk : List (BitVec 8)} {mcl : Nat} {ws1 : List (BitVec 32)} {tk : BitVec 64}
    (hmrk : mrk.length = c.max_vars) (hws1 : ws1.length = 2 * c.max_vars)
    (hmcl : mcl ≤ c.max_vars) :
    (mkBumpState s sc0 mrk mcl ws1 tk).LengthsOk c :=
  ⟨{ hlen.core_ok with mrk_len := hmrk, min_clr_len_le := hmcl },
   { hlen.scratch_ok with work_stk1_len := hws1 }⟩

private theorem s13b_cov_of_fields {c : FullCfg} {s s' : FullState}
    (hcov : FullAnaMarksCov c s) (hcv : s'.core.cur_vars = s.core.cur_vars)
    (hmcl : s'.core.min_clr_len = s.core.min_clr_len) (hmrk : s'.core.mrk = s.core.mrk)
    (hws1 : s'.scratch.work_stk1 = s.scratch.work_stk1) :
    FullAnaMarksCov c s' := by
  unfold FullAnaMarksCov at hcov ⊢
  rw [hcv, hmcl, hmrk, hws1]; exact hcov

private theorem s13b_perm_marksCov {c : FullCfg} {s : FullState}
    {repr' ws1' wsort' sbuf' : List (BitVec 32)}
    (hcv : s.core.cur_vars ≤ c.max_vars)
    (hws1 : s.scratch.work_stk1.length = 2 * c.max_vars) (hws' : ws1'.length = 2 * c.max_vars)
    (hcov : FullAnaMarksCov c s)
    (hperm : (ws1'.take s.core.min_clr_len).Perm (s.scratch.work_stk1.take s.core.min_clr_len)) :
    FullAnaMarksCov c
      { core := { s.core with repr := repr' }
        scratch := { s.scratch with
          work_stk1 := ws1', wsort := wsort', scratch_buf := sbuf' } } := by
  obtain ⟨hcnt_cv, hnd, hfwd, hbak⟩ := hcov
  have hcnt_ws1 : s.core.min_clr_len ≤ s.scratch.work_stk1.length := by rw [hws1]; omega
  have hcnt_ws' : s.core.min_clr_len ≤ ws1'.length := by rw [hws']; omega
  refine ⟨hcnt_cv, (hperm.map BitVec.toNat).nodup_iff.mpr hnd, fun k hk => ?_,
    fun v hv hnz => ?_⟩
  · dsimp only at hk ⊢
    have hmem : ws1'[k]'(by omega) ∈ s.scratch.work_stk1.take s.core.min_clr_len := by
      rw [← hperm.mem_iff]
      have hk_t : k < (ws1'.take s.core.min_clr_len).length := by rw [List.length_take]; omega
      simpa [List.getElem_take] using List.getElem_mem hk_t
    obtain ⟨j, hj, hjeq⟩ := List.mem_iff_getElem.mp hmem
    rw [List.length_take] at hj
    have hj_lt : j < s.core.min_clr_len := Nat.lt_of_lt_of_le hj (Nat.min_le_left _ _)
    rw [List.getElem_take] at hjeq
    have hcov_j := hfwd j hj_lt
    rw [List.getElem?_eq_getElem (by omega : k < ws1'.length), Option.getD_some, ← hjeq]
    rwa [List.getElem?_eq_getElem (by omega : j < s.scratch.work_stk1.length),
      Option.getD_some] at hcov_j
  · dsimp only at hnz ⊢
    obtain ⟨j, hj, hjeq⟩ := hbak v hv hnz
    have hmem : s.scratch.work_stk1[j]'(by omega) ∈ ws1'.take s.core.min_clr_len := by
      rw [hperm.mem_iff]
      have hj_t : j < (s.scratch.work_stk1.take s.core.min_clr_len).length := by
        rw [List.length_take]; omega
      simpa [List.getElem_take] using List.getElem_mem hj_t
    obtain ⟨i, hi, hieq⟩ := List.mem_iff_getElem.mp hmem
    rw [List.length_take] at hi
    have hi_lt : i < s.core.min_clr_len := Nat.lt_of_lt_of_le hi (Nat.min_le_left _ _)
    rw [List.getElem_take] at hieq
    refine ⟨i, hi_lt, ?_⟩
    rw [List.getElem?_eq_getElem (by omega : i < ws1'.length), Option.getD_some, hieq]
    rwa [List.getElem?_eq_getElem (by omega : j < s.scratch.work_stk1.length),
      Option.getD_some] at hjeq

theorem s13b_push_marksCov_gen {c : FullCfg} {s : FullState}
    {mrk : List (BitVec 8)} {mcl : Nat} {ws1 : List (BitVec 32)} {ov : BitVec 32}
    (hmrk : mrk.length = c.max_vars) (hws1 : ws1.length = 2 * c.max_vars)
    (hcv : s.core.cur_vars ≤ c.max_vars)
    (hcov : FullAnaMarksCov c
      { s with core := { s.core with mrk := mrk, min_clr_len := mcl },
               scratch := { s.scratch with work_stk1 := ws1 } })
    (hov_cv : ov.toNat < s.core.cur_vars) (hmcl_cv : mcl < s.core.cur_vars)
    (hmrk0 : mrk[ov.toNat]?.getD 0#8 = 0#8) :
    FullAnaMarksCov c
      { s with core := { s.core with mrk := mrk.set ov.toNat 1#8, min_clr_len := mcl + 1 },
               scratch := { s.scratch with work_stk1 := ws1.set mcl ov } } := by
  obtain ⟨hmcl_cv0, hnd, hfwd, hbak⟩ := hcov
  dsimp only at hnd hfwd hbak
  have hmcl_ws : mcl < ws1.length := by rw [hws1]; omega
  refine ⟨hmcl_cv, s13b_nodup_map_take_append hmcl_ws hnd (fun k hk heq => ?_),
    fun k hk => ?_, fun v hv hnz => ?_⟩
  · exact (hfwd k hk).2 (by simpa [heq] using hmrk0)
  · dsimp only at hk ⊢
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hlt | rfl
    · have hk_cov := hfwd k hlt
      have hne : (ws1[k]?.getD 0#32).toNat ≠ ov.toNat := fun heq => by
        rw [heq] at hk_cov; exact hk_cov.2 hmrk0
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne hne.symm]
      exact hk_cov
    · rw [List.getElem?_set_self hmcl_ws, Option.getD_some,
        List.getElem?_set_self (by rw [hmrk]; omega), Option.getD_some]
      exact ⟨hov_cv, by decide⟩
  · dsimp only at hnz ⊢
    by_cases hveq : v = ov.toNat
    · refine ⟨mcl, Nat.lt_succ_self _, ?_⟩
      subst hveq; rw [List.getElem?_set_self hmcl_ws, Option.getD_some]
    · rw [List.getElem?_set_ne (Ne.symm hveq)] at hnz
      obtain ⟨i, hi, hieq⟩ := hbak v hv hnz
      refine ⟨i, Nat.lt_succ_of_lt hi, ?_⟩
      rwa [List.getElem?_set_ne (by omega)]

private theorem bump_push_marksCov {c : FullCfg} {s : FullState} {sc0 : FullScratch}
    {mrk : List (BitVec 8)} {mcl : Nat} {ws1 : List (BitVec 32)} {tk : BitVec 64}
    {ov : BitVec 32}
    (hmrk : mrk.length = c.max_vars) (hws1 : ws1.length = 2 * c.max_vars)
    (hcv : s.core.cur_vars ≤ c.max_vars)
    (hcov : FullAnaMarksCov c (mkBumpState s sc0 mrk mcl ws1 tk))
    (hov_cv : ov.toNat < s.core.cur_vars) (hmcl_cv : mcl < s.core.cur_vars)
    (hmrk0 : mrk[ov.toNat]?.getD 0#8 = 0#8) :
    FullAnaMarksCov c
      (mkBumpState s sc0 (mrk.set ov.toNat 1#8) (mcl + 1) (ws1.set mcl ov) tk) :=
  s13b_push_marksCov_gen (s := { s with scratch := { sc0 with search_ticks := tk } })
    hmrk hws1 hcv hcov hov_cv hmcl_cv hmrk0

private theorem bump_pop_marksCov {c : FullCfg} {s : FullState} {sc0 : FullScratch}
    {mrk : List (BitVec 8)} {mcl : Nat} {ws1 : List (BitVec 32)} {tk : BitVec 64}
    (hmrk : mrk.length = c.max_vars) (hws1 : ws1.length = 2 * c.max_vars)
    (hcv : s.core.cur_vars ≤ c.max_vars)
    (hcov : FullAnaMarksCov c (mkBumpState s sc0 mrk mcl ws1 tk)) (hpos : 0 < mcl) :
    let hmcl_ws : mcl - 1 < ws1.length := by
      have hm1 := hcov.1; dsimp only [mkBumpState] at hm1; rw [hws1]; omega
    let rv := ws1[mcl - 1]'hmcl_ws
    FullAnaMarksCov c (mkBumpState s sc0 (mrk.set rv.toNat 0#8) (mcl - 1) ws1 tk) := by
  intro hmcl_ws rv
  obtain ⟨hmcl_cv0, hnd, hfwd, hbak⟩ := hcov
  dsimp only [mkBumpState] at hmcl_cv0 hnd hfwd hbak
  have hrv_lt : rv.toNat < s.core.cur_vars := by
    have := (hfwd (mcl - 1) (by omega)).1
    simpa [rv, List.getElem?_eq_getElem hmcl_ws] using this
  dsimp only [FullAnaMarksCov, mkBumpState]
  refine ⟨by omega, s13b_nodup_take_pred hpos hnd, fun k hk => ?_, fun v hv hnz => ?_⟩
  · have hk_cov := hfwd k (by omega)
    have hne : (ws1[k]?.getD 0#32).toNat ≠ rv.toNat := by
      have hk_t : k < ((ws1.take mcl).map BitVec.toNat).length := by
        simp only [List.length_map, List.length_take]; omega
      have hr_t : mcl - 1 < ((ws1.take mcl).map BitVec.toNat).length := by
        simp only [List.length_map, List.length_take]; omega
      have hdiff := List.pairwise_iff_getElem.mp hnd k (mcl - 1) hk_t hr_t (by omega)
      simp only [List.getElem_map, List.getElem_take] at hdiff
      rw [List.getElem?_eq_getElem (by omega : k < ws1.length), Option.getD_some]
      exact hdiff
    rw [List.getElem?_set_ne hne.symm]; exact hk_cov
  · have hvne : v ≠ rv.toNat := fun hveq => by
      subst hveq
      rw [List.getElem?_set_self (by rw [hmrk]; omega), Option.getD_some] at hnz
      exact hnz rfl
    rw [List.getElem?_set_ne hvne.symm] at hnz
    obtain ⟨i, hi, hieq⟩ := hbak v hv hnz
    rcases Nat.lt_or_eq_of_le (Nat.le_pred_of_lt hi) with hlt | rfl
    · exact ⟨i, hlt, hieq⟩
    · exfalso; apply hvne; rw [← hieq]
      simp [rv, List.getElem?_eq_getElem hmcl_ws]

private theorem bump_zero_marksCov {c : FullCfg} {s : FullState} {ws1 : List (BitVec 32)}
    (hmrk0 : ∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 = 0#8) :
    FullAnaMarksCov c (mkBumpState s s.scratch s.core.mrk 0 ws1 s.scratch.search_ticks) :=
  ⟨Nat.zero_le _, by simp, fun _ hk => by dsimp only [mkBumpState] at hk; omega,
    fun v hv hnz => absurd (hmrk0 v hv) hnz⟩

end BumpHelpers

local macro "m6h_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

local macro "c0_hcall " h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

private abbrev BumpSt := List (BitVec 8) × Nat × List (BitVec 32) × BitVec 64

private abbrev bumpAllowInv (c : FullCfg) (s : FullState) (sc0 : FullScratch)
    (R_hdr : Mem 64 → Prop) (st : BumpSt) (m : Mem 64) : Prop :=
  st.1.length = c.max_vars ∧ st.2.2.1.length = 2 * c.max_vars ∧
  FullAnaMarksCov c (mkBumpState s sc0 st.1 st.2.1 st.2.2.1 st.2.2.2) ∧
  (FullMem c (mkBumpState s sc0 st.1 st.2.1 st.2.2.1 st.2.2.2) ⋆ R_hdr) m

private abbrev bumpPostInv (c : FullCfg) (s : FullState) (ext : List (BitVec 64))
    (R : Mem 64 → Prop) (m : Mem 64) : Prop :=
  ∃ (ext1 : List (BitVec 64)) (sc : FullScratch) (mrk : List (BitVec 8)) (mcl : Nat),
    M6HdrExtOk ext1 ∧ (M6HdrExtInitOk ext → M6HdrExtInitOk ext1 ∧ M6ExtW2bPres ext ext1) ∧
    (bumpSt2 s sc mrk mcl).LengthsOk c ∧ FullAnaMarksCov c (bumpSt2 s sc mrk mcl) ∧
    FullExtScratchPres s (bumpSt2 s sc mrk mcl) ∧ sc.work_stk2 = s.scratch.work_stk2 ∧
    (FullMem c (bumpSt2 s sc mrk mcl) ⋆ (array64 (c.hdr - 2304) ext1 ⋆ R)) m

private theorem bumpPostInv_of_w2a {c : FullCfg} {s : FullState} {sc0 : FullScratch}
    {ext ext1 ext2 : List (BitVec 64)} {R : Mem 64 → Prop}
    {mrk : List (BitVec 8)} {mcl : Nat} {ws : List (BitVec 32)} {tk : BitVec 64}
    {s' : FullState} {m' : Mem 64}
    (hpre0 : FullExtScratchPres s { s with scratch := sc0 })
    (hws20 : sc0.work_stk2 = s.scratch.work_stk2)
    (hinit1 : M6HdrExtInitOk ext → M6HdrExtInitOk ext1 ∧ M6ExtW2bPres ext ext1)
    (hcov : FullAnaMarksCov c (mkBumpState s sc0 mrk mcl ws tk))
    (hcore' : s'.core = (mkBumpState s sc0 mrk mcl ws tk).core) (hlen' : s'.LengthsOk c)
    (hsc' : M6HdrScratchPres (mkBumpState s sc0 mrk mcl ws tk) s')
    (hext2 : M6HdrExtOk ext2)
    (hw2 : M6HdrExtInitOk ext1 → M6HdrExtInitOk ext2 ∧ M6ExtW2bPres ext1 ext2)
    (hm' : (FullMem c s' ⋆ (array64 (c.hdr - 2304) ext2 ⋆ R)) m') :
    bumpPostInv c s ext R m' := by
  obtain ⟨core', sc'⟩ := s'
  dsimp only at hcore'; subst hcore'
  refine ⟨ext2, sc', mrk, mcl, hext2, fun hi =>
    ⟨(hw2 (hinit1 hi).1).1, (hinit1 hi).2.trans (hw2 (hinit1 hi).1).2⟩, hlen',
    s13b_cov_of_fields hcov rfl rfl rfl hsc'.ws1,
    ⟨hsc'.extPres.1.trans hpre0.1, hsc'.extPres.2.trans hpre0.2⟩, hsc'.ws2.trans hws20, hm'⟩

/-! ## 3. `full_bump_analyzed_mode_fid` (`s13BumpAnalyzedModeSpecP M6ExtW2bPres`) -/

/-- `allow_reasons = false` branch of `full_bump_analyzed_mode_fid`. -/
private theorem s13_bump_analyzed_mode_false_wp (Γ : Env)
    (hSortAna : ∀ a m Q X, s13SortAnaQsSpec a m Q X →
      Γ "full_sort_ana_qs_m6" [i64, i64] [] a m Q X)
    (hBumpVar : ∀ a m Q X, Full.fullBumpVarSpec a m Q X →
      Γ "full_bump_var" [i64, i32] [] a m Q X)
    (hQueueMtf : ∀ a m Q X, Full.fullQueueMtfSpec a m Q X →
      Γ "full_queue_mtf" [i64, i32] [] a m Q X)
    (hBumpDecay : ∀ a m Q X, Full.fullBumpDecaySpec a m Q X →
      Γ "full_bump_decay" [i64] [] a m Q X)
    {c : FullCfg} {ext : List (BitVec 64)} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post []} {X : XPost}
    (hext : M6HdrExtOk ext) (hlen : s.LengthsOk c) (hpre : S13BumpPre false c s)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hQ : ∀ mrk' mcl' repr' sc' ext' m',
      let s' : FullState :=
        { s with
          core := { s.core with mrk := mrk', min_clr_len := mcl', repr := repr' }
          scratch := sc' }
      s'.LengthsOk c → (FullAnaMarksCov c s → FullAnaMarksCov c s') →
      (false = false → mrk' = s.core.mrk ∧ mcl' = s.core.min_clr_len ∧ ext' = ext) →
      (false = false → ∀ k < mcl', (sc'.work_stk1[k]?.getD 0#32).toNat < s.core.cur_vars) →
      FullExtScratchPres s s' → sc'.work_stk2 = s.scratch.work_stk2 →
      M6HdrExtOk ext' → (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext ext') →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q () m') :
    Func.wp Γ full_bump_analyzed_mode_fid_body (c.hdr, false, ()) m Q X := by
  have hmaxv := c.hmaxv; unfold LratBytes.dimacsBound at hmaxv
  have hco := hlen.core_ok; have hso := hlen.scratch_ok
  have hcv_le := hco.cur_vars_le
  obtain ⟨hmcl_cv, hlt_ws0⟩ : s.core.min_clr_len ≤ s.core.cur_vars ∧
      ∀ k < s.core.min_clr_len, (s.scratch.work_stk1[k]?.getD 0#32).toNat < s.core.cur_vars := hpre
  unfold Func.wp full_bump_analyzed_mode_fid_body
  rw [fullM6HdrMem_iff] at hm
  c0_hsteps_nogrp
  · exact hQ s.core.mrk s.core.min_clr_len s.core.repr s.scratch ext m hlen id
      (fun _ => ⟨rfl, rfl, rfl⟩) (fun _ => hlt_ws0) ⟨rfl, rfl⟩ rfl hext
      (fun hi => ⟨hi, M6ExtW2bPres.refl ext⟩) ((fullM6HdrMem_iff ..).mpr hm)
  · let R_hdr : Mem 64 → Prop := array64 (c.hdr - 2304) ext ⋆ R
    let cnt := s.core.min_clr_len
    refine wp_join_group (ts := []) (fun () m2 => m2 = m)
      (fun _ () m2 hm2 => ?_) (fun Jallow hJallow => by c0_hsteps; exact hJallow () m rfl)
    rcases hm2.symm with rfl; rw [Blocks.get_here]; dsimp only
    c0_hsteps_nogrp
    refine wp_join_group (ts := []) (fun () mf => Q () mf)
      (fun _ () mf hf => by rw [Blocks.get_here]; c0_hsteps <;> exact hf)
      (fun Jfin hJfin => ?_)
    c0_hsteps_nogrp
    · -- `stable == 0`: sort via `s13SortAnaQsSpec`, then `full_queue_mtf` loop
      refine wp_join_group (ts := [])
        (fun () m3 => ∃ (repr3 : List (BitVec 32)) (sc3 : FullScratch),
          let s3 : FullState := mkBumpStateR s sc3 s.core.mrk cnt repr3
          s3.LengthsOk c ∧ (FullAnaMarksCov c s → FullAnaMarksCov c s3) ∧
          (∀ k < cnt, (sc3.work_stk1[k]?.getD 0#32).toNat < s.core.cur_vars) ∧
          FullExtScratchPres s s3 ∧ sc3.work_stk2 = s.scratch.work_stk2 ∧
          (FullMem c s3 ⋆ R_hdr) m3)
        (fun _ () m3 ⟨repr3, sc3, hlen3, hcov3, hlt3, hpre3, hws23, hm3⟩ => ?_)
        (fun Jsrt hJsrt => ?_)
      · let s3 : FullState := mkBumpStateR s sc3 s.core.mrk cnt repr3
        c0_hsteps_nogrp
        refine wp_while_state1 (t := i64) (α := Nat × FullScratch)
          (proj := fun st => BitVec.ofNat 64 st.1) (μ := fun st => cnt - st.1)
          (Inv := fun st mk => st.1 ≤ cnt ∧
            let sk : FullState := { s3 with scratch := st.2 }
            sk.LengthsOk c ∧ FullExtScratchPres s3 sk ∧
            st.2.work_stk1 = sc3.work_stk1 ∧ st.2.work_stk2 = sc3.work_stk2 ∧
            (FullMem c sk ⋆ R_hdr) mk)
          (fun Jk hJk => by
            c0_hsteps; exact hJk (0, sc3) m3 ⟨Nat.zero_le _, hlen3, ⟨rfl, rfl⟩, rfl, rfl, hm3⟩)
          (fun Jk (k, sck) mk ⟨hk_le, hlenk, hprek, hws1k, hws2k, hmk⟩ ihk => ?_)
        dsimp only at hk_le hlenk hprek hws1k hws2k hmk ihk
        rw [Blocks.get_here]; dsimp only
        let sk : FullState := { s3 with scratch := sck }
        c0_hsteps_nogrp
        · have hk_lt : k < cnt := by
            have hlt : k % 2 ^ 64 < cnt % 2 ^ 64 := by
              simpa [BitVec.toNat_ofNat] using (by assumption : _)
            rwa [Nat.mod_eq_of_lt (by omega : k < 2 ^ 64),
              Nat.mod_eq_of_lt (by omega : cnt < 2 ^ 64)] at hlt
          have hk_ws1 : k < sck.work_stk1.length := by
            rw [hlenk.scratch_ok.work_stk1_len]; omega
          let bv := sck.work_stk1[(BitVec.ofNat 64 k).toNat]'
            (by rw [bv64_ofNat_toNat (by omega)]; exact hk_ws1)
          have hbv_lt_cv : bv.toNat < s.core.cur_vars := by
            have h1 := hlt3 k hk_lt
            have hbv_eq : bv = sc3.work_stk1[k]'(by rw [hlen3.scratch_ok.work_stk1_len]; omega) :=
              s13b_getElem_congr_list hws1k (bv64_ofNat_toNat (by omega))
            rw [List.getElem?_eq_getElem (by rw [hlen3.scratch_ok.work_stk1_len]; omega),
              Option.getD_some] at h1
            simpa [hbv_eq] using h1
          have hk1_bv : BitVec.ofNat 64 k + 1 = BitVec.ofNat 64 (k + 1) :=
            BitVec.eq_of_toNat_eq (by
              rw [show (1 : BitVec 64) = 1#64 from rfl,
                fl_bv64_add1_toNat (by rw [bv64_ofNat_toNat (by omega)]; omega),
                bv64_ofNat_toNat (by omega), bv64_ofNat_toNat (by omega)])
          have hbv_fl : (bv.setWidth 64).toNat < sk.core.flags.length := by
            rw [s13b_bv32_setWidth64, hlenk.core_ok.flags_len]; omega
          c0_hsteps_nogrp
          refine wp_join_state0 (α := FullScratch)
            (Inv := fun sc' m' =>
              let sk' : FullState := { s3 with scratch := sc' }
              sk'.LengthsOk c ∧ FullExtScratchPres s3 sk' ∧
              sc'.work_stk1 = sc3.work_stk1 ∧ sc'.work_stk2 = sc3.work_stk2 ∧
              (FullMem c sk' ⋆ R_hdr) m')
            (fun _ sc' m' ⟨hl', hp', hw1', hw2', hm'⟩ => by
              rw [Blocks.get_here]; c0_hsteps; rw [hk1_bv]
              exact ihk (k + 1, sc') m' (by dsimp only; omega)
                ⟨by omega, hl', hp', hw1', hw2', hm'⟩)
            (fun Jstep hJstep => ?_)
          c0_hsteps_nogrp
          · c0_hcall hQueueMtf
            refine ⟨c, sk, R_hdr, rfl, hlenk, hmk, fun () sk1 mk1 hc1 hs1 hp1 hm1 => ?_⟩
            dsimp only [Full.fullSafetySlice_mem, Full.fullSafetySlice_coreProj,
              Full.fullSafetySlice_safe] at hc1 hs1 hm1
            have hcs1 : sk1.core = sk.core := @Full.fullCoreState_agrees_with_scratch c sk sk1 hc1
            have hsk1_eq : sk1 = { s3 with scratch := sk1.scratch } := by
              cases sk1; simp only [sk] at hcs1; congr 1
            rw [hsk1_eq] at hs1 hm1; c0_hsteps
            exact hJstep sk1.scratch mk1 ⟨hs1, ⟨hp1.1.1.trans hprek.1, hp1.1.2.trans hprek.2⟩,
              hp1.2.1.trans hws1k, hp1.2.2.1.trans hws2k, hm1⟩
          · exact hJstep sck mk ⟨hlenk, hprek, hws1k, hws2k, hmk⟩
          · exact hJstep sck mk ⟨hlenk, hprek, hws1k, hws2k, hmk⟩
        · c0_hsteps
          exact hJfin () mk (hQ s.core.mrk cnt repr3 sck ext mk hlenk
            (fun hc => s13b_cov_of_fields (hcov3 hc) rfl rfl rfl hws1k)
            (fun _ => ⟨rfl, rfl, rfl⟩) (fun _ k hk => by rw [hws1k]; exact hlt3 k hk)
            ⟨hprek.1.trans hpre3.1, hprek.2.trans hpre3.2⟩ (hws2k.trans hws23) hext
            (fun hi => ⟨hi, M6ExtW2bPres.refl ext⟩) ((fullM6HdrMem_iff ..).mpr hmk))
      · c0_hsteps_nogrp
        · have hcnt64 : (BitVec.ofNat 64 s.core.min_clr_len).toNat = s.core.min_clr_len :=
            bv64_ofNat_toNat (by omega)
          c0_hcall hSortAna
          refine s13SortAnaQsSpec_of hlen (by simp only [Arg.val_var, hcnt64]; exact hmcl_cv)
            (fun k hk => hlt_ws0 k (by simp only [Arg.val_var, hcnt64] at hk; exact hk))
            hm fun ws3 repr3 wsort3 sbuf3 m3 hws3 hrepr3 hwsort3 hsbuf3 hperm _ hlt3 hm3 => ?_
          simp only [Arg.val_var, hcnt64] at hperm hlt3
          let sc3 : FullScratch :=
            { s.scratch with work_stk1 := ws3, wsort := wsort3, scratch_buf := sbuf3 }
          c0_hsteps
          exact hJsrt () m3 ⟨repr3, sc3,
            ⟨{ hco with repr_len := hrepr3 },
             { hso with work_stk1_len := hws3, wsort_len := hwsort3, scratch_buf_len := hsbuf3 }⟩,
            fun hc => s13b_perm_marksCov hcv_le hso.work_stk1_len hws3 hc hperm,
            hlt3, ⟨rfl, rfl⟩, rfl, hm3⟩
    · -- `stable != 0`: `full_bump_var` loop + `full_bump_decay`
      c0_hsteps_nogrp
      refine wp_while_state1 (t := i64) (α := Nat × FullScratch)
        (proj := fun st => BitVec.ofNat 64 st.1) (μ := fun st => cnt - st.1)
        (Inv := fun st mk => st.1 ≤ cnt ∧
          let sk : FullState := { s with scratch := st.2 }
          sk.LengthsOk c ∧ FullExtScratchPres s sk ∧
          st.2.work_stk1 = s.scratch.work_stk1 ∧ st.2.work_stk2 = s.scratch.work_stk2 ∧
          (FullMem c sk ⋆ R_hdr) mk)
        (fun Jk hJk => by
          c0_hsteps; exact hJk (0, s.scratch) m ⟨Nat.zero_le _, hlen, ⟨rfl, rfl⟩, rfl, rfl, hm⟩)
        (fun Jk (k, sck) mk ⟨hk_le, hlenk, hprek, hws1k, hws2k, hmk⟩ ihk => ?_)
      dsimp only at hk_le hlenk hprek hws1k hws2k hmk ihk
      rw [Blocks.get_here]; dsimp only
      let sk : FullState := { s with scratch := sck }
      c0_hsteps_nogrp
      · have hk_lt : k < cnt := by
          have hlt : k % 2 ^ 64 < cnt % 2 ^ 64 := by
            simpa [BitVec.toNat_ofNat] using (by assumption : _)
          rwa [Nat.mod_eq_of_lt (by omega : k < 2 ^ 64),
            Nat.mod_eq_of_lt (by omega : cnt < 2 ^ 64)] at hlt
        have hk_ws1 : k < sck.work_stk1.length := by rw [hlenk.scratch_ok.work_stk1_len]; omega
        let bv := sck.work_stk1[(BitVec.ofNat 64 k).toNat]'
          (by rw [bv64_ofNat_toNat (by omega)]; exact hk_ws1)
        have hbv_lt_cv : bv.toNat < s.core.cur_vars := by
          have h1 := hlt_ws0 k hk_lt
          have hbv_eq : bv = s.scratch.work_stk1[k]'(by rw [hso.work_stk1_len]; omega) :=
            s13b_getElem_congr_list hws1k (bv64_ofNat_toNat (by omega))
          rw [List.getElem?_eq_getElem (by rw [hso.work_stk1_len]; omega), Option.getD_some] at h1
          simpa [hbv_eq] using h1
        have hk1_bv : BitVec.ofNat 64 k + 1 = BitVec.ofNat 64 (k + 1) :=
          BitVec.eq_of_toNat_eq (by
            rw [show (1 : BitVec 64) = 1#64 from rfl,
              fl_bv64_add1_toNat (by rw [bv64_ofNat_toNat (by omega)]; omega),
              bv64_ofNat_toNat (by omega), bv64_ofNat_toNat (by omega)])
        have hbv_fl : (bv.setWidth 64).toNat < sk.core.flags.length := by
          rw [s13b_bv32_setWidth64, hlenk.core_ok.flags_len]; omega
        c0_hsteps_nogrp
        refine wp_join_state0 (α := FullScratch)
          (Inv := fun sc' m' =>
            let sk' : FullState := { s with scratch := sc' }
            sk'.LengthsOk c ∧ FullExtScratchPres s sk' ∧
            sc'.work_stk1 = s.scratch.work_stk1 ∧ sc'.work_stk2 = s.scratch.work_stk2 ∧
            (FullMem c sk' ⋆ R_hdr) m')
          (fun _ sc' m' ⟨hl', hp', hw1', hw2', hm'⟩ => by
            rw [Blocks.get_here]; c0_hsteps; rw [hk1_bv]
            exact ihk (k + 1, sc') m' (by dsimp only; omega) ⟨by omega, hl', hp', hw1', hw2', hm'⟩)
          (fun Jstep hJstep => ?_)
        c0_hsteps_nogrp
        · c0_hcall hBumpVar
          refine ⟨c, sk, R_hdr, rfl, hlenk, hmk, fun () sk1 mk1 hc1 hs1 hp1 hm1 => ?_⟩
          dsimp only [Full.fullSafetySlice_mem, Full.fullSafetySlice_coreProj,
            Full.fullSafetySlice_safe] at hc1 hs1 hm1
          have hcs1 : sk1.core = sk.core := @Full.fullCoreState_agrees_with_scratch c sk sk1 hc1
          have hsk1_eq : sk1 = { s with scratch := sk1.scratch } := by
            cases sk1; simp only [sk] at hcs1; congr 1
          rw [hsk1_eq] at hs1 hm1; c0_hsteps
          exact hJstep sk1.scratch mk1 ⟨hs1, ⟨hp1.1.1.trans hprek.1, hp1.1.2.trans hprek.2⟩,
            hp1.2.1.trans hws1k, hp1.2.2.1.trans hws2k, hm1⟩
        · exact hJstep sck mk ⟨hlenk, hprek, hws1k, hws2k, hmk⟩
        · exact hJstep sck mk ⟨hlenk, hprek, hws1k, hws2k, hmk⟩
      · c0_hsteps_nogrp
        c0_hcall hBumpDecay
        refine ⟨c, sk, R_hdr, rfl, hlenk, hmk, fun () sk' m' hcore' hsafe' hpres' hm' => ?_⟩
        dsimp only [Full.fullSafetySlice_mem, Full.fullSafetySlice_coreProj,
          Full.fullSafetySlice_safe] at hcore' hsafe' hm'
        have hcs' : sk'.core = sk.core := @Full.fullCoreState_agrees_with_scratch c sk sk' hcore'
        have hsf_eq : sk' = { s with scratch := sk'.scratch } := by
          cases sk'; simp only [sk] at hcs'; congr 1
        rw [hsf_eq] at hsafe' hm'; c0_hsteps
        exact hJfin () m' (hQ s.core.mrk cnt s.core.repr sk'.scratch ext m' hsafe'
          (fun hc => s13b_cov_of_fields hc rfl rfl rfl (hpres'.2.1.trans hws1k))
          (fun _ => ⟨rfl, rfl, rfl⟩)
          (fun _ k hk => by rw [hpres'.2.1.trans hws1k]; exact hlt_ws0 k hk)
          ⟨hpres'.1.1.trans hprek.1, hpres'.1.2.trans hprek.2⟩ (hpres'.2.2.1.trans hws2k) hext
          (fun hi => ⟨hi, M6ExtW2bPres.refl ext⟩) ((fullM6HdrMem_iff ..).mpr hm'))

/-- `allow_reasons = true` branch of `full_bump_analyzed_mode_fid` (split into clean `wp_join_group`
phases: reason scan/rollback producer + `stable` bump consumer). -/
private theorem s13b_k_lt_of_mod {k m : Nat} (hk : k < 2 ^ 64) (hm : m < 2 ^ 64)
    (hlt : k % 2 ^ 64 < m % 2 ^ 64) : k < m := by
  rwa [Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt hm] at hlt

private theorem s13b_ofNat64_add1 {k : Nat} (hk : k + 1 < 2 ^ 64) :
    BitVec.ofNat 64 k + 1 = BitVec.ofNat 64 (k + 1) :=
  BitVec.eq_of_toNat_eq (by
    rw [show (1 : BitVec 64) = 1#64 from rfl,
      fl_bv64_add1_toNat (by rw [bv64_ofNat_toNat (by omega)]; omega),
      bv64_ofNat_toNat (by omega), bv64_ofNat_toNat hk])

private theorem s13b_ofNat64_add1_toNat {k : Nat} (hk : k + 1 < 2 ^ 64) :
    (BitVec.ofNat 64 k + 1).toNat = k + 1 := by
  rw [s13b_ofNat64_add1 hk, bv64_ofNat_toNat hk]

private theorem s13b_bv32_mod64 (b : BitVec 32) : b.toNat % 18446744073709551616 = b.toNat :=
  Nat.mod_eq_of_lt (Nat.lt_trans b.isLt (by decide))

private theorem s13b_ana_bv_lt {c : FullCfg} {s : FullState} {k : Nat}
    (hcov : FullAnaMarksCov c s) (hk_lt : k < s.core.min_clr_len)
    (hk_ws : k < s.scratch.work_stk1.length) (hk64 : k < 2 ^ 64) :
    (s.scratch.work_stk1[(BitVec.ofNat 64 k).toNat]'(by
      rw [bv64_ofNat_toNat hk64]; exact hk_ws)).toNat < s.core.cur_vars := by
  have hck := (hcov.2.2.1 k hk_lt).1
  rw [List.getElem?_eq_getElem hk_ws, Option.getD_some] at hck
  have heq : s.scratch.work_stk1[(BitVec.ofNat 64 k).toNat]'(by
      rw [bv64_ofNat_toNat hk64]; exact hk_ws) = s.scratch.work_stk1[k]'hk_ws :=
    s13b_getElem_congr_list rfl (bv64_ofNat_toNat hk64)
  rw [heq]; exact hck

private theorem s13b_state_eq_scratch {c : FullCfg} {s3 sk1 : FullState} {sck : FullScratch}
    (hc1 : PreservesCoreSlice (Full.fullSafetySlice c).coreProj
      ({ s3 with scratch := sck } : FullState) sk1) :
    sk1 = { s3 with scratch := sk1.scratch } := by
  have hcs1 : sk1.core = ({ s3 with scratch := sck } : FullState).core :=
    @Full.fullCoreState_agrees_with_scratch c { s3 with scratch := sck } sk1 hc1
  cases sk1; simp only at hcs1; congr 1

private theorem s13b_safety_step {c : FullCfg} (s3 : FullState) {sk sk1 : FullState}
    {sck : FullScratch} {R_hdr : Mem 64 → Prop} {mk1 : Mem 64}
    (hs3 : sk = { s3 with scratch := sck })
    (hc1 : PreservesCoreSlice (Full.fullSafetySlice c).coreProj sk sk1)
    (hs1 : (Full.fullSafetySlice c).safe sk1)
    (hm1 : ((Full.fullSafetySlice c).mem sk1 ⋆ R_hdr) mk1) :
    ({ s3 with scratch := sk1.scratch } : FullState).LengthsOk c ∧
      (FullMem c { s3 with scratch := sk1.scratch } ⋆ R_hdr) mk1 := by
  subst hs3
  have hsk1 := s13b_state_eq_scratch hc1
  dsimp only [Full.fullSafetySlice_mem, Full.fullSafetySlice_safe] at hs1 hm1
  rw [hsk1] at hs1 hm1
  exact ⟨hs1, hm1⟩

private theorem s13b_delay_w2a_step {Γ : Env} {Q : Post []} {X : XPost}
    {c : FullCfg} {ext ext1 : List (BitVec 64)} {s : FullState} {sc0 : FullScratch}
    {R : Mem 64 → Prop} {mrk_a : List (BitVec 8)} {mcl_a : Nat}
    {ws_a : List (BitVec 32)} {tk_a : BitVec 64} {hm_a : Mem 64}
    {J24 : Cont []} (fn : String)
    (hDelay : ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X → Γ fn [i64, i64] [] a m Q X)
    (hcfg : FullM6HdrCfgOk c) (hext1 : M6HdrExtOk ext1)
    (hlen0 : ({ s with scratch := sc0 } : FullState).LengthsOk c)
    (hpre0 : FullExtScratchPres s { s with scratch := sc0 })
    (hws20 : sc0.work_stk2 = s.scratch.work_stk2)
    (hinit_pres : M6HdrExtInitOk ext → M6HdrExtInitOk ext1 ∧ M6ExtW2bPres ext ext1)
    (hmrk_a : mrk_a.length = c.max_vars) (hws_a : ws_a.length = 2 * c.max_vars)
    (hcov_a : FullAnaMarksCov c (mkBumpState s sc0 mrk_a mcl_a ws_a tk_a))
    (hmr : (FullMem c (mkBumpState s sc0 mrk_a mcl_a ws_a tk_a) ⋆
      (array64 (c.hdr - 2304) ext1 ⋆ R)) hm_a)
    (hJrb : ∀ m', bumpPostInv c s ext R m' → J24 () m') :
    wp Γ Q X (.call fn (as := [i64, i64]) (bs := [])
      (.var c.hdr, .imm 0, ()) fun _ => .jump J24 ()) hm_a := by
  have hcv_le : s.core.cur_vars ≤ c.max_vars := hlen0.core_ok.cur_vars_le
  have hlen_a := mkBumpState_lengths (mcl := mcl_a) (tk := tk_a) hlen0 hmrk_a hws_a
    (by have := hcov_a.1; dsimp only [mkBumpState] at this; omega)
  m6h_call hDelay
  refine m6HdrW2aSpec_of rfl hcfg hext1 hlen_a ((fullM6HdrMem_iff ..).mpr hmr)
    fun () ext2 s' m' hcore' hlen' hsc' hext2 hw2 hm' => ?_
  rw [fullM6HdrMem_iff] at hm'; c0_hsteps
  exact hJrb m' (bumpPostInv_of_w2a hpre0 hws20 hinit_pres hcov_a hcore' hlen' hsc' hext2 hw2 hm')

private def s13BumpRollbackExpr {V : Ty → Type} {C : List Ty → Type}
    (h pMrk pAna cv saved lim : V i64) (Jpost : C []) : Expr V C [] :=
  let op64 (c : OpCode [i64, i64] [i64]) (a b : Arg V i64) := Op.mk c (a, b, ())
  .group (sig := [[]]) (fun _ => .cons (fun _ => .jump Jpost ()) .nil)
    fun J24 =>
      .let_ (op64 (.add i64) (.var h) (.imm 272)) fun p1 =>
      .load i64 (.var p1.fst) fun mcl =>
      .let_ (Op.mk (.cmp .ugt i64 .bool rfl) (.var mcl, .var lim, ())) fun p2 =>
      .jnz (.var p2.fst)
        (.group (sig := [[]]) (fun J28 => .cons (fun _ =>
          .let_ (op64 (.add i64) (.var h) (.imm 272)) fun p3 =>
          .load i64 (.var p3.fst) fun mcl2 =>
          .let_ (Op.mk (.cmp .ugt i64 .bool rfl) (.var mcl2, .var saved, ())) fun p4 =>
          .jnz (.var p4.fst)
            (.let_ (op64 (.add i64) (.var h) (.imm 272)) fun p5 =>
             .load i64 (.var p5.fst) fun mcl3 =>
             .let_ (op64 (.sub i64) (.var mcl3) (.imm 1)) fun m1 =>
             .let_ (op64 (.add i64) (.var h) (.imm 272)) fun p6 =>
             .store (.var m1.fst) (.var p6.fst)
               (.let_ (op64 (.add i64) (.var h) (.imm 272)) fun p7 =>
                .load i64 (.var p7.fst) fun mcl4 =>
                .let_ (op64 (.mul i64) (.var mcl4) (.imm 4)) fun p8 =>
                .let_ (op64 (.add i64) (.var pAna) (.var p8.fst)) fun p9 =>
                .load i32 (.var p9.fst) fun rv =>
                .group (sig := [[]]) (fun _ => .cons (fun _ => .jump J28.fst ()) .nil)
                  fun J32 =>
                    .let_ (Op.mk (.zext 32 64) (.var rv, ())) fun p10 =>
                    .let_ (Op.mk (.cmp .ult i64 .bool rfl) (.var p10.fst, .var cv, ()))
                      fun p11 =>
                    .jnz (.var p11.fst)
                      (.let_ (Op.mk (.zext 32 64) (.var rv, ())) fun p12 =>
                       .let_ (op64 (.add i64) (.var pMrk) (.var p12.fst)) fun p13 =>
                       .let_ (Op.mk (.trunc 32 8) (.imm 0, ())) fun p14 =>
                       .store (.var p14.fst) (.var p13.fst) (.jump J32.fst ()))
                      (.jump J32.fst ())))
            (.call "m6_hdr_bump_delay" (as := [i64, i64]) (bs := []) (.var h, .imm 0, ())
              fun _ => .jump J24.fst ())) .nil)
          fun J28 => .jump J28.fst ())
        (.call "m6_hdr_reduce_delay" (as := [i64, i64]) (bs := []) (.var h, .imm 0, ())
          fun _ => .jump J24.fst ())

private theorem s13_bump_rollback_wp {Γ : Env} {Q : Post []} {X : XPost}
    (hBumpDelay : ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
      Γ "m6_hdr_bump_delay" [i64, i64] [] a m Q X)
    (hReduceDelay : ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
      Γ "m6_hdr_reduce_delay" [i64, i64] [] a m Q X)
    {c : FullCfg} {ext ext1 : List (BitVec 64)} {s : FullState} {sc0 : FullScratch}
    {R : Mem 64 → Prop} {saved : Nat} {lim : BitVec 64} {st_a : BumpSt} {mr : Mem 64}
    {Jpost : Cont []}
    (hcfg : FullM6HdrCfgOk c) (hext1 : M6HdrExtOk ext1)
    (hlen0 : ({ s with scratch := sc0 } : FullState).LengthsOk c)
    (hpre0 : FullExtScratchPres s { s with scratch := sc0 })
    (hws20 : sc0.work_stk2 = s.scratch.work_stk2)
    (hinit_pres : M6HdrExtInitOk ext → M6HdrExtInitOk ext1 ∧ M6ExtW2bPres ext ext1)
    (hsaved64 : saved < 2 ^ 64)
    (hinv_a : bumpAllowInv c s sc0 (array64 (c.hdr - 2304) ext1 ⋆ R) st_a mr)
    (hJpost : ∀ m', bumpPostInv c s ext R m' → Jpost () m') :
    wp Γ Q X (s13BumpRollbackExpr c.hdr c.pMark c.pWorkStk1 (BitVec.ofNat 64 s.core.cur_vars)
      (BitVec.ofNat 64 saved) lim Jpost) mr := by
  rcases st_a with ⟨mrk_a, mcl_a, ws_a, tk_a⟩
  rcases hinv_a with ⟨hmrk_a, hws_a, hcov_a, hmr⟩
  dsimp only at hmrk_a hws_a hcov_a hmr
  have hmaxv := c.hmaxv; unfold LratBytes.dimacsBound at hmaxv
  have hcv_le : s.core.cur_vars ≤ c.max_vars := hlen0.core_ok.cur_vars_le
  have hcv_lt64 : s.core.cur_vars < 2 ^ 64 := by omega
  let R_hdr : Mem 64 → Prop := array64 (c.hdr - 2304) ext1 ⋆ R
  dsimp only [s13BumpRollbackExpr]
  refine wp_join_group (ts := []) (fun _ m' => bumpPostInv c s ext R m')
    (fun _ _ m' hp => by rw [Blocks.get_here]; c0_hsteps; exact hJpost m' hp)
    (fun Jrb hJrb => ?_)
  c0_hsteps_nogrp
  · refine wp_while_state0 (α := BumpSt) (μ := fun st => st.2.1)
      (Inv := fun st mr' => bumpAllowInv c s sc0 R_hdr st mr')
      (fun Jr hJr => by
        c0_hsteps; exact hJr (mrk_a, mcl_a, ws_a, tk_a) mr ⟨hmrk_a, hws_a, hcov_a, hmr⟩)
      (fun Jr (mrk_r, mcl_r, ws_r, tk_r) mr' ⟨hmrk_r, hws_r, hcov_r, hmr'⟩ ihr => ?_)
    dsimp only at hmrk_r hws_r hcov_r hmr' ihr; rw [Blocks.get_here]; dsimp only
    let sr := mkBumpState s sc0 mrk_r mcl_r ws_r tk_r
    have hmcl_r_cv : mcl_r ≤ s.core.cur_vars := hcov_r.1
    c0_hsteps_nogrp
    · have hmcl_r_pos : 0 < mcl_r := Nat.lt_of_le_of_lt (Nat.zero_le _)
        (s13b_k_lt_of_mod (k := saved) (m := mcl_r) hsaved64 (by omega) (by assumption))
      have hmcl_m1_bv : (BitVec.ofNat 64 mcl_r - 1#64).toNat = mcl_r - 1 := by
        rw [fl_bv64_sub1_toNat (by rw [bv64_ofNat_toNat (by omega)]; omega),
          bv64_ofNat_toNat (by omega)]
      have hmcl_ws :
          (BitVec.ofNat 64 mcl_r - 1#64).toNat < sr.scratch.work_stk1.length := by
        rw [hmcl_m1_bv, hws_r]; omega
      let rv := sr.scratch.work_stk1[(BitVec.ofNat 64 mcl_r - 1#64).toNat]'hmcl_ws
      have hmcl_ws' : mcl_r - 1 < ws_r.length := by rw [hws_r]; omega
      have hrv_eq : rv = ws_r[mcl_r - 1]'hmcl_ws' := s13b_getElem_congr_list rfl hmcl_m1_bv
      have hrv_lt : rv.toNat < s.core.cur_vars := by
        have h1 := (hcov_r.2.2.1 (mcl_r - 1) (by dsimp only [mkBumpState]; omega)).1
        dsimp only [sr, mkBumpState] at h1
        rw [List.getElem?_eq_getElem hmcl_ws', Option.getD_some] at h1
        simpa [hrv_eq] using h1
      have hrv_mrk : (rv.setWidth 64).toNat < mrk_r.length := by
        rw [s13b_bv32_setWidth64, hmrk_r]; omega
      refine wp_join_state0 (α := BumpSt)
        (Inv := fun st mr'' => st.2.1 < mcl_r ∧ bumpAllowInv c s sc0 R_hdr st mr'')
        (fun _ st mr'' ⟨hm_lt, hinv⟩ => by
          rw [Blocks.get_here]; c0_hsteps; exact ihr st mr'' hm_lt hinv)
        (fun Js2 hJs2 => ?_)
      c0_hsteps_nogrp
      · have hcov_pop := bump_pop_marksCov hmrk_r hws_r hcv_le hcov_r hmcl_r_pos; c0_hsteps
        exact hJs2 (mrk_r.set rv.toNat 0#8, mcl_r - 1, ws_r, tk_r) _
          ⟨by dsimp only; omega, by rw [List.length_set, hmrk_r], hws_r,
            by simpa [hrv_eq] using hcov_pop, by
            simpa [sr, mkBumpState, rv, hmcl_m1_bv, s13b_bv32_setWidth64, s13b_bv32_mod64,
              show BitVec.ofNat 8 0 = 0#8 from rfl,
              Nat.mod_eq_of_lt (by omega : mcl_r - 1 < 2 ^ 64)] using hm⟩
      · exfalso
        have hge_idx : (2 ^ 64 - BitVec.toNat (1 : BitVec 64) + mcl_r) % 2 ^ 64 % 2 ^ 64 =
            mcl_r - 1 := by simp only [show BitVec.toNat (1 : BitVec 64) = 1 from rfl]; omega
        have hrv_hc : ws_r[(2 ^ 64 - BitVec.toNat (1 : BitVec 64) + mcl_r) % 2 ^ 64 % 2 ^ 64]'(
            by rw [hge_idx]; exact hmcl_ws') = rv :=
          (s13b_getElem_congr_list rfl hge_idx).trans hrv_eq.symm
        have hge := hc; rw [hrv_hc, Nat.mod_eq_of_lt hcv_lt64] at hge; omega
    · exact s13b_delay_w2a_step "m6_hdr_bump_delay" hBumpDelay hcfg hext1 hlen0
        hpre0 hws20 hinit_pres hmrk_r hws_r hcov_r hmr' (hJrb ())
  · exact s13b_delay_w2a_step "m6_hdr_reduce_delay" hReduceDelay hcfg hext1 hlen0
      hpre0 hws20 hinit_pres hmrk_a hws_a hcov_a hmr (hJrb ())

private theorem s13b_bv32_lt_of_mod {x : BitVec 32} {n : Nat} (hn : n < 2 ^ 64)
    (h : x.toNat < n % 2 ^ 64) : x.toNat < n := by
  rwa [Nat.mod_eq_of_lt hn] at h

private theorem s13b_mrk_zero {mrk : List (BitVec 8)} {ov : BitVec 32} {cv : Nat}
    (hlen : mrk.length = cv) (hcov : ov.toNat < cv)
    (h : (mrk[ov.toNat]'(by omega)).setWidth 32 = 0#32) :
    mrk[ov.toNat]?.getD 0#8 = 0#8 := by
  rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
  exact s13b_bv8_zext32_eq0_iff.mp h

private theorem s13_bump_analyzed_mode_true_wp (Γ : Env)
    (hDelaying : ∀ a m Q X, m6HdrW2aSpec [i64] [.bool] a m Q X →
      Γ "m6_hdr_delaying" [i64, i64] [.bool] a m Q X)
    (hDrAllow : ∀ a m Q X, m6HdrDrAllowSpec a m Q X →
      Γ "m6_hdr_dr_allow" [i64] [.bool] a m Q X)
    (hBumpDelay : ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
      Γ "m6_hdr_bump_delay" [i64, i64] [] a m Q X)
    (hReduceDelay : ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
      Γ "m6_hdr_reduce_delay" [i64, i64] [] a m Q X)
    (hSortAna : ∀ a m Q X, s13SortAnaQsSpec a m Q X →
      Γ "full_sort_ana_qs_m6" [i64, i64] [] a m Q X)
    (hBumpVar : ∀ a m Q X, Full.fullBumpVarSpec a m Q X →
      Γ "full_bump_var" [i64, i32] [] a m Q X)
    (hQueueMtf : ∀ a m Q X, Full.fullQueueMtfSpec a m Q X →
      Γ "full_queue_mtf" [i64, i32] [] a m Q X)
    (hBumpDecay : ∀ a m Q X, Full.fullBumpDecaySpec a m Q X →
      Γ "full_bump_decay" [i64] [] a m Q X)
    {c : FullCfg} {ext : List (BitVec 64)} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post []} {X : XPost}
    (hcfg : FullM6HdrCfgOk c) (hext : M6HdrExtOk ext) (hlen : s.LengthsOk c)
    (hcov : FullAnaMarksCov c s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hQ : ∀ mrk' mcl' repr' sc' ext' m',
      let s' : FullState :=
        { s with
          core := { s.core with mrk := mrk', min_clr_len := mcl', repr := repr' }
          scratch := sc' }
      s'.LengthsOk c → (FullAnaMarksCov c s → FullAnaMarksCov c s') →
      (true = false → mrk' = s.core.mrk ∧ mcl' = s.core.min_clr_len ∧ ext' = ext) →
      (true = false → ∀ k < mcl', (sc'.work_stk1[k]?.getD 0#32).toNat < s.core.cur_vars) →
      FullExtScratchPres s s' → sc'.work_stk2 = s.scratch.work_stk2 →
      M6HdrExtOk ext' → (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext ext') →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q () m') :
    Func.wp Γ full_bump_analyzed_mode_fid_body (c.hdr, true, ()) m Q X := by
  have hmaxv := c.hmaxv; unfold LratBytes.dimacsBound at hmaxv
  have hco := hlen.core_ok; have hcv_le := hco.cur_vars_le; have hmrk0_len := hco.mrk_len
  unfold Func.wp full_bump_analyzed_mode_fid_body; rw [fullM6HdrMem_iff] at hm
  c0_hsteps_nogrp
  · exact hQ s.core.mrk s.core.min_clr_len s.core.repr s.scratch ext m hlen id
      (fun h => by cases h) (fun h => by cases h) ⟨rfl, rfl⟩ rfl hext
      (fun hi => ⟨hi, M6ExtW2bPres.refl ext⟩) ((fullM6HdrMem_iff ..).mpr hm)
  · let saved : Nat := s.core.min_clr_len
    have hsaved_le : saved ≤ s.core.cur_vars := hcov.1
    have hcv_lt64 : s.core.cur_vars < 2 ^ 64 := by omega
    refine wp_join_group (ts := []) (fun () m2 => bumpPostInv c s ext R m2)
      (fun _ () m2 ⟨ext1, sc2, mrk2, mcl2, hext1, hinit1, hlen2, hcov2, hpre2, hws22, hm2⟩ => ?_)
      (fun Jallow hJallow => ?_)
    · let R_hdr : Mem 64 → Prop := array64 (c.hdr - 2304) ext1 ⋆ R
      have hmcl2_cv : mcl2 ≤ s.core.cur_vars := hcov2.1
      have hws2 : sc2.work_stk1.length = 2 * c.max_vars := hlen2.scratch_ok.work_stk1_len
      c0_hsteps_nogrp
      refine wp_join_group (ts := []) (fun () mf => Q () mf)
        (fun _ () mf hf => by rw [Blocks.get_here]; c0_hsteps <;> exact hf) (fun Jfin hJfin => ?_)
      c0_hsteps_nogrp
      · refine wp_join_group (ts := [])
          (fun () m3 => ∃ (repr3 : List (BitVec 32)) (sc3 : FullScratch),
            let s3 := mkBumpStateR s sc3 mrk2 mcl2 repr3
            s3.LengthsOk c ∧ FullAnaMarksCov c s3 ∧ FullExtScratchPres s s3 ∧
            sc3.work_stk2 = s.scratch.work_stk2 ∧ (FullMem c s3 ⋆ R_hdr) m3)
          (fun _ () m3 ⟨repr3, sc3, hlen3, hcov3, hpre3, hws23, hm3⟩ => ?_) (fun Jsrt hJsrt => ?_)
        · let s3 := mkBumpStateR s sc3 mrk2 mcl2 repr3
          c0_hsteps_nogrp
          refine wp_while_state1 (t := i64) (α := Nat × FullScratch)
            (proj := fun st => BitVec.ofNat 64 st.1) (μ := fun st => mcl2 - st.1)
            (Inv := fun st mk => st.1 ≤ mcl2 ∧ let sk := { s3 with scratch := st.2 }
              sk.LengthsOk c ∧ FullAnaMarksCov c sk ∧ FullExtScratchPres s3 sk ∧
              st.2.work_stk1 = sc3.work_stk1 ∧ st.2.work_stk2 = sc3.work_stk2 ∧
              (FullMem c sk ⋆ R_hdr) mk)
            (fun Jk hJk => by
              c0_hsteps
              exact hJk (0, sc3) m3 ⟨Nat.zero_le _, hlen3, hcov3, ⟨rfl, rfl⟩, rfl, rfl, hm3⟩)
            (fun Jk (k, sck) mk ⟨hk_le, hlenk, hcovk, hprek, hws1k, hws2k, hmk⟩ ihk => ?_)
          dsimp only at hk_le hlenk hcovk hprek hws1k hws2k hmk ihk
          rw [Blocks.get_here]; dsimp only
          let sk : FullState := { s3 with scratch := sck }
          c0_hsteps_nogrp
          · have hk_lt : k < mcl2 := s13b_k_lt_of_mod (by omega) (by omega)
              (by simpa [BitVec.toNat_ofNat] using (by assumption : _))
            have hk_ws1 : k < sck.work_stk1.length := by rw [hlenk.scratch_ok.work_stk1_len]; omega
            have hbv_lt_cv := s13b_ana_bv_lt (s := sk) hcovk hk_lt hk_ws1 (by omega)
            dsimp only [sk, s3, mkBumpStateR] at hbv_lt_cv
            have hbv_fl : ((sck.work_stk1[(BitVec.ofNat 64 k).toNat]'(by
                rw [bv64_ofNat_toNat (by omega)]; exact hk_ws1)).setWidth 64).toNat <
                sk.core.flags.length := by
              rw [s13b_bv32_setWidth64, hlenk.core_ok.flags_len]; omega
            c0_hsteps_nogrp
            refine wp_join_state0 (α := FullScratch)
              (Inv := fun sc' m' => let sk' := { s3 with scratch := sc' }
                sk'.LengthsOk c ∧ FullAnaMarksCov c sk' ∧ FullExtScratchPres s3 sk' ∧
                sc'.work_stk1 = sc3.work_stk1 ∧ sc'.work_stk2 = sc3.work_stk2 ∧
                (FullMem c sk' ⋆ R_hdr) m')
              (fun _ sc' m' ⟨hl', hc', hp', hw1', hw2', hm'⟩ => by
                rw [Blocks.get_here]; c0_hsteps; rw [s13b_ofNat64_add1 (by omega)]
                exact ihk (k + 1, sc') m' (by dsimp only; omega)
                  ⟨by omega, hl', hc', hp', hw1', hw2', hm'⟩)
              (fun Jstep hJstep => ?_)
            c0_hsteps_nogrp
            · c0_hcall hQueueMtf
              refine ⟨c, sk, R_hdr, rfl, hlenk, hmk, fun () sk1 mk1 hc1 hs1 hp1 hm1 => ?_⟩
              obtain ⟨hs1', hm1'⟩ := s13b_safety_step s3 rfl hc1 hs1 hm1; c0_hsteps
              exact hJstep sk1.scratch mk1 ⟨hs1', s13b_cov_of_fields hcovk rfl rfl rfl hp1.2.1,
                ⟨hp1.1.1.trans hprek.1, hp1.1.2.trans hprek.2⟩,
                hp1.2.1.trans hws1k, hp1.2.2.1.trans hws2k, hm1'⟩
            · exact hJstep sck mk ⟨hlenk, hcovk, hprek, hws1k, hws2k, hmk⟩
          · c0_hsteps
            exact hJfin () mk (hQ mrk2 mcl2 repr3 sck ext1 mk hlenk (fun _ => hcovk)
              (fun h => by cases h) (fun h => by cases h)
              ⟨hprek.1.trans hpre3.1, hprek.2.trans hpre3.2⟩ (hws2k.trans hws23) hext1 hinit1
              ((fullM6HdrMem_iff ..).mpr hmk))
        · c0_hsteps_nogrp
          · c0_hcall hSortAna
            refine s13SortAnaQsSpec_of hlen2
              (by simpa [bumpSt2, bv64_ofNat_toNat (by omega : mcl2 < 2 ^ 64)] using hmcl2_cv)
              (fun k hk => by
                simp only [Arg.val_var, bv64_ofNat_toNat (show mcl2 < 2 ^ 64 by omega)] at hk
                exact (hcov2.2.2.1 k hk).1)
              hm2 fun ws3 repr3 wsort3 sbuf3 m3 hws3 hrepr3 hwsort3 hsbuf3 hperm _ _ hm3 => ?_
            simp only [Arg.val_var, bv64_ofNat_toNat (show mcl2 < 2 ^ 64 by omega)] at hperm
            c0_hsteps
            exact hJsrt () m3 ⟨repr3,
              { sc2 with work_stk1 := ws3, wsort := wsort3, scratch_buf := sbuf3 },
              ⟨{ hlen2.core_ok with repr_len := hrepr3 },
               { hlen2.scratch_ok with
                 work_stk1_len := hws3, wsort_len := hwsort3, scratch_buf_len := hsbuf3 }⟩,
              s13b_perm_marksCov (s := bumpSt2 s sc2 mrk2 mcl2) hcv_le hws2 hws3 hcov2 hperm,
              hpre2, hws22, hm3⟩
      · let s3 := bumpSt2 s sc2 mrk2 mcl2
        c0_hsteps_nogrp
        refine wp_while_state1 (t := i64) (α := Nat × FullScratch)
          (proj := fun st => BitVec.ofNat 64 st.1) (μ := fun st => mcl2 - st.1)
          (Inv := fun st mk => st.1 ≤ mcl2 ∧ let sk := { s3 with scratch := st.2 }
            sk.LengthsOk c ∧ FullAnaMarksCov c sk ∧ FullExtScratchPres s3 sk ∧
            st.2.work_stk1 = sc2.work_stk1 ∧ st.2.work_stk2 = sc2.work_stk2 ∧
            (FullMem c sk ⋆ R_hdr) mk)
          (fun Jk hJk => by
            c0_hsteps
            exact hJk (0, sc2) m2 ⟨Nat.zero_le _, hlen2, hcov2, ⟨rfl, rfl⟩, rfl, rfl, hm2⟩)
          (fun Jk (k, sck) mk ⟨hk_le, hlenk, hcovk, hprek, hws1k, hws2k, hmk⟩ ihk => ?_)
        dsimp only at hk_le hlenk hcovk hprek hws1k hws2k hmk ihk
        rw [Blocks.get_here]; dsimp only
        let sk : FullState := { s3 with scratch := sck }
        c0_hsteps_nogrp
        · have hk_lt : k < mcl2 := s13b_k_lt_of_mod (by omega) (by omega)
            (by simpa [BitVec.toNat_ofNat] using (by assumption : _))
          have hk_ws1 : k < sck.work_stk1.length := by rw [hlenk.scratch_ok.work_stk1_len]; omega
          have hbv_lt_cv := s13b_ana_bv_lt (s := sk) hcovk hk_lt hk_ws1 (by omega)
          dsimp only [sk, s3, bumpSt2] at hbv_lt_cv
          have hbv_fl : ((sck.work_stk1[(BitVec.ofNat 64 k).toNat]'(by
              rw [bv64_ofNat_toNat (by omega)]; exact hk_ws1)).setWidth 64).toNat <
              sk.core.flags.length := by
            rw [s13b_bv32_setWidth64, hlenk.core_ok.flags_len]; omega
          c0_hsteps_nogrp
          refine wp_join_state0 (α := FullScratch)
            (Inv := fun sc' m' => let sk' := { s3 with scratch := sc' }
              sk'.LengthsOk c ∧ FullAnaMarksCov c sk' ∧ FullExtScratchPres s3 sk' ∧
              sc'.work_stk1 = sc2.work_stk1 ∧ sc'.work_stk2 = sc2.work_stk2 ∧
              (FullMem c sk' ⋆ R_hdr) m')
            (fun _ sc' m' ⟨hl', hc', hp', hw1', hw2', hm'⟩ => by
              rw [Blocks.get_here]; c0_hsteps; rw [s13b_ofNat64_add1 (by omega)]
              exact ihk (k + 1, sc') m' (by dsimp only; omega)
                ⟨by omega, hl', hc', hp', hw1', hw2', hm'⟩)
            (fun Jstep hJstep => ?_)
          c0_hsteps_nogrp
          · c0_hcall hBumpVar
            refine ⟨c, sk, R_hdr, rfl, hlenk, hmk, fun () sk1 mk1 hc1 hs1 hp1 hm1 => ?_⟩
            obtain ⟨hs1', hm1'⟩ := s13b_safety_step s3 rfl hc1 hs1 hm1; c0_hsteps
            exact hJstep sk1.scratch mk1 ⟨hs1', s13b_cov_of_fields hcovk rfl rfl rfl hp1.2.1,
              ⟨hp1.1.1.trans hprek.1, hp1.1.2.trans hprek.2⟩,
              hp1.2.1.trans hws1k, hp1.2.2.1.trans hws2k, hm1'⟩
          · exact hJstep sck mk ⟨hlenk, hcovk, hprek, hws1k, hws2k, hmk⟩
        · c0_hsteps_nogrp; c0_hcall hBumpDecay
          refine ⟨c, sk, R_hdr, rfl, hlenk, hmk, fun () sk' m' hcore' hsafe' hpres' hm' => ?_⟩
          obtain ⟨hsafe'', hm''⟩ := s13b_safety_step s3 rfl hcore' hsafe' hm'; c0_hsteps
          exact hJfin () m' (hQ mrk2 mcl2 s.core.repr sk'.scratch ext1 m' hsafe''
            (fun _ => s13b_cov_of_fields hcovk rfl rfl rfl hpres'.2.1) (fun h => by cases h)
            (fun h => by cases h)
            ⟨hpres'.1.1.trans (hprek.1.trans hpre2.1), hpres'.1.2.trans (hprek.2.trans hpre2.2)⟩
            (hpres'.2.2.1.trans (hws2k.trans hws22)) hext1 hinit1 ((fullM6HdrMem_iff ..).mpr hm''))
    · c0_hsteps_nogrp
      · m6h_call hDelaying
        refine m6HdrW2aSpec_of rfl hcfg hext hlen ((fullM6HdrMem_iff ..).mpr hm)
          fun ⟨dl, ⟨⟩⟩ ext0 s0 m0 hcore0 hlen0 hsc0 hext0 hw0 hm0 => ?_
        obtain ⟨sc0, rfl⟩ : ∃ sc0 : FullScratch, s0 = { s with scratch := sc0 } := by
          obtain ⟨core0, sc0⟩ := s0; dsimp only at hcore0; subst hcore0; exact ⟨sc0, rfl⟩
        have hcov0 : FullAnaMarksCov c { s with scratch := sc0 } :=
          s13b_cov_of_fields hcov rfl rfl rfl hsc0.ws1
        have hpre0 : FullExtScratchPres s { s with scratch := sc0 } := hsc0.extPres
        have hws20 := hsc0.ws2; have hws10_len := hlen0.scratch_ok.work_stk1_len
        rw [fullM6HdrMem_iff] at hm0; c0_hsteps_nogrp
        · exact hJallow () m0
            ⟨ext0, sc0, s.core.mrk, saved, hext0, hw0, hlen0, hcov0, hpre0, hws20, hm0⟩
        m6h_call hDrAllow
        refine m6HdrDrAllowSpec_of hcfg hext0 hlen0 ((fullM6HdrMem_iff ..).mpr hm0)
          fun allow ext1 m1 hinit1 hext_eq hm1 => ?_
        have hext1 : M6HdrExtOk ext1 := hinit1.toOk
        have hinit_pres : M6HdrExtInitOk ext → M6HdrExtInitOk ext1 ∧ M6ExtW2bPres ext ext1 :=
          fun hi => ⟨hinit1, by rw [hext_eq (hw0 hi).1]; exact (hw0 hi).2⟩
        rw [fullM6HdrMem_iff] at hm1
        let R_hdr : Mem 64 → Prop := array64 (c.hdr - 2304) ext1 ⋆ R
        c0_hsteps_nogrp
        · refine wp_join_state1 (t := i64) (α := Nat) (proj := BitVec.ofNat 64)
            (Inv := fun tlen mt => tlen ≤ s.core.cur_vars ∧ mt = m1)
            (fun Jt tlen mt ⟨htlen_le, hmt⟩ => ?_) (fun Jt hJt => ?_)
          · rcases hmt with rfl; rw [Blocks.get_here]; dsimp only; c0_hsteps_nogrp
            refine wp_while_state1 (t := i64) (α := Nat × BumpSt)
              (proj := fun st => BitVec.ofNat 64 st.1) (μ := fun st => tlen - st.1)
              (Inv := fun st mi => st.1 ≤ tlen ∧ bumpAllowInv c s sc0 R_hdr st.2 mi)
              (fun Ji hJi => by
                c0_hsteps; exact hJi (0, s.core.mrk, saved, sc0.work_stk1, sc0.search_ticks) mt
                  ⟨Nat.zero_le _, hmrk0_len, hws10_len, hcov0, hm1⟩)
              (fun Ji (i, mrk_i, mcl_i, ws_i, tk_i) mi
                  ⟨hi_le, hmrk_i, hws_i, hcov_i, hmi⟩ ihi => ?_)
            dsimp only at hi_le hmrk_i hws_i hcov_i hmi ihi; rw [Blocks.get_here]; dsimp only
            let si := mkBumpState s sc0 mrk_i mcl_i ws_i tk_i
            refine wp_join_group (ts := [])
              (fun () mr => ∃ st_a : BumpSt, bumpAllowInv c s sc0 R_hdr st_a mr)
              (fun _ () mr ⟨st_a, hinv_a⟩ => by
                rw [Blocks.get_here]
                exact s13_bump_rollback_wp hBumpDelay hReduceDelay hcfg hext1 hlen0
                  hpre0 hws20 hinit_pres (by omega) hinv_a (fun m' hp => hJallow () m' hp))
              (fun Jafter hJafter => ?_)
            c0_hsteps_nogrp
            · have hi_lt : i < tlen := s13b_k_lt_of_mod (by omega) (by omega)
                (by simpa [BitVec.toNat_ofNat] using (by assumption : _))
              have hi_tmp_bv : (BitVec.ofNat 64 i).toNat < si.core.tmp.length := by
                rw [bv64_ofNat_toNat (by omega), show si.core.tmp = s.core.tmp from rfl,
                  hco.tmp_len_arr]; omega
              let uv32 := (si.core.tmp[(BitVec.ofNat 64 i).toNat]'hi_tmp_bv) >>> 1#32
              c0_hsteps_nogrp
              refine wp_join_state1 (t := i32) (α := BitVec 32) (proj := fun x => x)
                (Inv := fun _ mr => mr = mi) (fun Jr rsn mr hmr => ?_) (fun Jr hJr => ?_)
              · rw [hmr] at *; clear mr hmr; rw [Blocks.get_here]; dsimp only; c0_hsteps_nogrp
                refine wp_join_state0 (α := BumpSt)
                  (Inv := fun st' mi' => bumpAllowInv c s sc0 R_hdr st' mi')
                  (fun _ st' mi' hst' => by
                    rw [Blocks.get_here]; c0_hsteps; rw [s13b_ofNat64_add1 (by omega)]
                    exact ihi (i + 1, st') mi' (by dsimp only; omega) ⟨by omega, hst'⟩)
                  (fun Jstep hJstep => ?_)
                refine wp_join_group (ts := []) (fun () m' => m' = mi)
                  (fun Jelse () m' hm' => ?_) (fun Jelse hJelse => ?_)
                · rw [hm'] at *; clear m' hm'; rw [Blocks.get_here]; dsimp only
                  refine wp_join_state0 (α := BumpSt)
                    (Inv := fun st' mi' => bumpAllowInv c s sc0 R_hdr st' mi')
                    (fun _ st' mi' hst' => by
                      rw [Blocks.get_here]; c0_hsteps; exact hJstep st' mi' hst')
                    (fun Js hJs => ?_)
                  have hal_le := hco.arena_len_le; have har_len := hco.arena_len_arr
                  have har_cap := c.harena; unfold LratBytes.dimacsBound at har_cap
                  c0_hsteps_nogrp
                  · have hrsn_3 : rsn.toNat + 3 ≤ s.core.arena_len := by
                      have hge : (rsn.toNat + 3) % 2 ^ 64 ≤ s.core.arena_len % 2 ^ 64 := by
                        simpa [show BitVec.toNat (3 : BitVec 64) = 3 from rfl] using hc
                      rw [Nat.mod_eq_of_lt (by omega),
                        Nat.mod_eq_of_lt (by have := rsn.isLt; omega)] at hge; omega
                    have hrsn2 : (rsn.setWidth 64 + 2#64).toNat < s.core.arena.length := by bv_omega
                    have hrsn2_eq : (rsn.setWidth 64 + 2#64).toNat = (rsn.toNat + 2) % 2 ^ 64 :=
                      by bv_omega
                    let sz := s.core.arena[(rsn.setWidth 64 + 2#64).toNat]'hrsn2
                    c0_hsteps_nogrp
                    refine wp_join_state0 (α := BumpSt)
                      (Inv := fun st' mj' => bumpAllowInv c s sc0 R_hdr st' mj')
                      (fun _ st' mj' hst' => by
                        rw [Blocks.get_here]; c0_hsteps; exact hJs st' mj' hst')
                      (fun Jsz hJsz => ?_)
                    c0_hsteps_nogrp
                    · have hsz_ar : rsn.toNat + 3 + sz.toNat ≤ s.core.arena_len := by
                        have hge : (rsn.toNat + 3 + sz.toNat) % 2 ^ 64 ≤
                            s.core.arena_len % 2 ^ 64 := by
                          dsimp only [sz]; simpa [hrsn2_eq,
                            show BitVec.toNat (3 : BitVec 64) = 3 from rfl,
                            show BitVec.toNat (2 : BitVec 64) = 2 from rfl] using hc
                        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt
                          (by have := rsn.isLt; have := sz.isLt; omega)] at hge; omega
                      refine wp_while_state1 (t := i32) (α := BitVec 32 × BumpSt)
                        (proj := fun st => st.1) (μ := fun st => sz.toNat - st.1.toNat)
                        (Inv := fun st mj =>
                          st.1.toNat ≤ sz.toNat ∧ bumpAllowInv c s sc0 R_hdr st.2 mj)
                        (fun Jj hJj => by
                          c0_hsteps; exact hJj (0#32, mrk_i, mcl_i, ws_i, tk_i + 1) _
                            ⟨Nat.zero_le _, hmrk_i, hws_i, hcov_i, hm⟩)
                        (fun Jj (j, mrk_j, mcl_j, ws_j, tk_j) mj
                            ⟨hj_le, hmrk_j, hws_j, hcov_j, hmj⟩ ihj => ?_)
                      dsimp only at hj_le hmrk_j hws_j hcov_j hmj ihj
                      rw [Blocks.get_here]; dsimp only
                      let sj := mkBumpState s sc0 mrk_j mcl_j ws_j tk_j
                      c0_hsteps_nogrp
                      · have hj_lt : j.toNat < sz.toNat := by
                          have hj_hc : j.toNat < (s.core.arena[(rsn.toNat +
                              BitVec.toNat (2 : BitVec 64)) % 2 ^ 64]'(by
                                rw [show BitVec.toNat (2 : BitVec 64) = 2 from rfl, ← hrsn2_eq]
                                exact hrsn2)).toNat := by assumption
                          simpa [sz, hrsn2_eq,
                            show BitVec.toNat (2 : BitVec 64) = 2 from rfl] using hj_hc
                        have har_j : (rsn.setWidth 64 + 3#64 + j.setWidth 64).toNat <
                            sj.core.arena.length := by dsimp only [sj, mkBumpState]; bv_omega
                        let ov := (sj.core.arena[(rsn.setWidth 64 + 3#64 + j.setWidth 64).toNat]'
                          har_j) >>> (1 : Nat)
                        have hj1_bv := fl_bv32_add1_toNat
                          (by have := sz.isLt; omega : j.toNat + 1 < 2 ^ 32)
                        c0_hsteps_nogrp
                        refine wp_join_state0 (α := BumpSt)
                          (Inv := fun st' mj' => bumpAllowInv c s sc0 R_hdr st' mj')
                          (fun _ st' mj' hst' => by
                            rw [Blocks.get_here]; c0_hsteps
                            exact ihj (j + 1#32, st') mj' (by dsimp only; rw [hj1_bv]; omega)
                              ⟨by rw [hj1_bv]; omega, hst'⟩)
                          (fun Jjs hJjs => ?_)
                        c0_hsplit
                        · have hov_cv := s13b_bv32_lt_of_mod (x := ov) (n := s.core.cur_vars)
                            hcv_lt64 (by simpa [ov] using (by assumption : _))
                          have hov_lvl : (ov.setWidth 64).toNat < s.core.lvl.length := by
                            rw [s13b_bv32_setWidth64, hco.lvl_len]; omega
                          have hov_mrk : (ov.setWidth 64).toNat < mrk_j.length := by
                            rw [s13b_bv32_setWidth64, hmrk_j]; omega
                          have hstay :=
                            hJjs (mrk_j, mcl_j, ws_j, tk_j) mj ⟨hmrk_j, hws_j, hcov_j, hmj⟩
                          c0_hsplit
                          · c0_hsplit
                            · have hmrk_hc := hc; c0_hsplit
                              · have hmcl_cv : mcl_j < s.core.cur_vars := s13b_k_lt_of_mod
                                  (by have := hcov_j.1; dsimp [mkBumpState] at this; omega)
                                  hcv_lt64 (by assumption)
                                have hmrk_z := s13b_mrk_zero hmrk_j
                                  (by omega : ov.toNat < c.max_vars)
                                  (by simpa [ov, sj, mkBumpState, BitVec.toNat_ushiftRight,
                                    s13b_bv32_mod64, Nat.shiftRight_eq_div_pow,
                                    show BitVec.ofNat 32 0 = 0#32 from rfl] using hmrk_hc)
                                have hcov' := bump_push_marksCov hmrk_j hws_j hcv_le hcov_j
                                  hov_cv hmcl_cv hmrk_z
                                c0_hsteps
                                exact hJjs
                                  (mrk_j.set ov.toNat 1#8, mcl_j + 1, ws_j.set mcl_j ov, tk_j) _
                                  ⟨by rw [List.length_set, hmrk_j], by rw [List.length_set, hws_j],
                                    hcov', by
                                    simpa [sj, mkBumpState, ov,
                                      s13b_ofNat64_add1_toNat (k := mcl_j) (by omega),
                                      s13b_bv32_mod64, BitVec.toNat_ushiftRight,
                                      bv64_ofNat_toNat (by omega : mcl_j < 2 ^ 64),
                                      Nat.mod_eq_of_lt (by omega : mcl_j + 1 < 2 ^ 64),
                                      show BitVec.ofNat 8 1 = 1#8 from rfl] using hm⟩
                              all_goals (c0_hsteps; exact hstay)
                            all_goals (c0_hsteps; exact hstay)
                          all_goals (c0_hsteps; exact hstay)
                        all_goals (
                          c0_hsteps; exact hJjs (mrk_j, mcl_j, ws_j, tk_j) mj
                            ⟨hmrk_j, hws_j, hcov_j, hmj⟩)
                      all_goals (
                        c0_hsteps; exact hJsz (mrk_j, mcl_j, ws_j, tk_j) mj
                          ⟨hmrk_j, hws_j, hcov_j, hmj⟩)
                    all_goals (
                      c0_hsteps; exact hJsz (mrk_i, mcl_i, ws_i, tk_i) mi
                        ⟨hmrk_i, hws_i, hcov_i, hmi⟩)
                  all_goals (
                    c0_hsteps; exact hJs (mrk_i, mcl_i, ws_i, tk_i) mi
                      ⟨hmrk_i, hws_i, hcov_i, hmi⟩)
                · c0_hsteps_nogrp
                  · refine wp_join_state0 (α := BumpSt)
                      (Inv := fun st' mi' => bumpAllowInv c s sc0 R_hdr st' mi')
                      (fun _ st' mi' hst' => by
                        rw [Blocks.get_here]; c0_hsteps; exact hJstep st' mi' hst')
                      (fun Jbin hJbin => ?_)
                    let ov : BitVec 32 := (rsn &&& 0x7FFFFFFF#32) >>> (1 : Nat)
                    have hstay := hJbin (mrk_i, mcl_i, ws_i, tk_i) mi ⟨hmrk_i, hws_i, hcov_i, hmi⟩
                    c0_hsplit
                    · have hov_cv := s13b_bv32_lt_of_mod (x := ov) (n := s.core.cur_vars) hcv_lt64
                        (by simpa [ov, BitVec.toNat_ushiftRight, BitVec.toNat_and] using
                          (by assumption : _))
                      have hov_lvl : (ov.setWidth 64).toNat < s.core.lvl.length := by
                        rw [s13b_bv32_setWidth64, hco.lvl_len]; omega
                      have hov_mrk : (ov.setWidth 64).toNat < mrk_i.length := by
                        rw [s13b_bv32_setWidth64, hmrk_i]; omega
                      c0_hsplit
                      · c0_hsplit
                        · have hmrk_hc := hc; c0_hsplit
                          · have hmcl_cv : mcl_i < s.core.cur_vars := s13b_k_lt_of_mod
                              (by have := hcov_i.1; dsimp [mkBumpState] at this; omega)
                              hcv_lt64 (by assumption)
                            have hmrk_z := s13b_mrk_zero hmrk_i (by omega : ov.toNat < c.max_vars)
                              (by simpa [ov, BitVec.toNat_ushiftRight, BitVec.toNat_and,
                                s13b_bv32_mod64, Nat.shiftRight_eq_div_pow,
                                show BitVec.ofNat 32 0 = 0#32 from rfl] using hmrk_hc)
                            have hcov' := bump_push_marksCov hmrk_i hws_i hcv_le hcov_i
                              hov_cv hmcl_cv hmrk_z
                            c0_hsteps
                            exact hJbin (mrk_i.set ov.toNat 1#8, mcl_i + 1, ws_i.set mcl_i ov, tk_i)
                              _ ⟨by rw [List.length_set, hmrk_i], by rw [List.length_set, hws_i],
                                hcov', by
                                simpa [mkBumpState, ov,
                                  s13b_ofNat64_add1_toNat (k := mcl_i) (by omega),
                                  s13b_bv32_mod64, BitVec.toNat_ushiftRight, BitVec.toNat_and,
                                  bv64_ofNat_toNat (by omega : mcl_i < 2 ^ 64),
                                  Nat.mod_eq_of_lt (by omega : mcl_i + 1 < 2 ^ 64),
                                  show BitVec.ofNat 8 1 = 1#8 from rfl] using hm⟩
                          all_goals (c0_hsteps; exact hstay)
                        all_goals (c0_hsteps; exact hstay)
                      all_goals (c0_hsteps; exact hstay)
                    all_goals (c0_hsteps; exact hstay)
                  all_goals (c0_hsteps; exact hJelse () mi rfl)
              · c0_hsteps_nogrp
                · have huv_lt := s13b_bv32_lt_of_mod (x := uv32) (n := s.core.cur_vars) hcv_lt64
                    (by simpa [uv32, si, mkBumpState, s13b_bv32_setWidth64] using
                      (by assumption : _))
                  have huv_cv : (uv32.setWidth 64).toNat < si.core.rsns.length := by
                    rw [s13b_bv32_setWidth64, hco.rsns_len]; omega
                  c0_hsteps; exact hJr _ mi rfl
                · c0_hsteps; exact hJr _ mi rfl
            all_goals (
              exact hJafter () mi ⟨(mrk_i, mcl_i, ws_i, tk_i), hmrk_i, hws_i, hcov_i, hmi⟩)
          · c0_hsteps
            · exact hJt s.core.cur_vars m1 ⟨Nat.le_refl _, rfl⟩
            · have htlen_le : s.core.tmp_len ≤ s.core.cur_vars := by
                have htl_le := hco.tmp_len_le
                have hle : ¬ s.core.cur_vars % 2 ^ 64 < s.core.tmp_len % 2 ^ 64 := by assumption
                rw [Nat.mod_eq_of_lt hcv_lt64, Nat.mod_eq_of_lt (by omega)] at hle; omega
              exact hJt s.core.tmp_len m1 ⟨htlen_le, rfl⟩
        · exact hJallow () m1
            ⟨ext1, sc0, s.core.mrk, saved, hext1, hinit_pres, hlen0, hcov0, hpre0, hws20, hm1⟩
      · exfalso; cases hc

/-- Step-13 `full_bump_analyzed_mode_fid` satisfies `s13BumpAnalyzedModeSpecP M6ExtW2bPres`. -/
theorem full_bump_analyzed_mode_fid_step13_wp (Γ : Env)
    (hDelaying : ∀ a m Q X, m6HdrW2aSpec [i64] [.bool] a m Q X →
      Γ "m6_hdr_delaying" [i64, i64] [.bool] a m Q X)
    (hDrAllow : ∀ a m Q X, m6HdrDrAllowSpec a m Q X →
      Γ "m6_hdr_dr_allow" [i64] [.bool] a m Q X)
    (hBumpDelay : ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
      Γ "m6_hdr_bump_delay" [i64, i64] [] a m Q X)
    (hReduceDelay : ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
      Γ "m6_hdr_reduce_delay" [i64, i64] [] a m Q X)
    (hSortAna : ∀ a m Q X, s13SortAnaQsSpec a m Q X →
      Γ "full_sort_ana_qs_m6" [i64, i64] [] a m Q X)
    (hBumpVar : ∀ a m Q X, Full.fullBumpVarSpec a m Q X →
      Γ "full_bump_var" [i64, i32] [] a m Q X)
    (hQueueMtf : ∀ a m Q X, Full.fullQueueMtfSpec a m Q X →
      Γ "full_queue_mtf" [i64, i32] [] a m Q X)
    (hBumpDecay : ∀ a m Q X, Full.fullBumpDecaySpec a m Q X →
      Γ "full_bump_decay" [i64] [] a m Q X) :
    ∀ a m Q X, s13BumpAnalyzedModeSpecP M6ExtW2bPres a m Q X →
      Func.wp Γ full_bump_analyzed_mode_fid_body a m Q X := by
  rintro ⟨h, allow, ⟨⟩⟩ m Q X hs
  obtain ⟨c, ext, s, R, rfl, hcfg, hext, hlen, hpre, hm, hQ⟩ := s13BumpAnalyzedModeSpecP_elim hs
  cases allow
  · exact s13_bump_analyzed_mode_false_wp Γ hSortAna hBumpVar hQueueMtf hBumpDecay
      hext hlen hpre hm hQ
  · exact s13_bump_analyzed_mode_true_wp Γ hDelaying hDrAllow hBumpDelay hReduceDelay
      hSortAna hBumpVar hQueueMtf hBumpDecay hcfg hext hlen hpre hm hQ

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S4
