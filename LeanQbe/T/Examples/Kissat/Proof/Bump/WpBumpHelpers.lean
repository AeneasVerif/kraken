/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Bump.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Bump.Helpers
import LeanQbe.T.Examples.Kissat.Proof.Lib.ContractLemmas
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Header
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts1
public import LeanQbe.T.Examples.Kissat.Proof.Tiers.Spec
public import LeanQbe.T.Examples.Kissat.Src.Bump
public import LeanQbe.T.Logic.CanonicalEnv
public import LeanQbe.T.Logic.C0Agrees
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
meta import LeanQbe.T.Logic.C0Step
meta import LeanQbe.T.Logic.C0HeadStep

/-!
# Helpers for `full_bump_analyzed_mode_fid` Canonical WP Proof

Pure `FullAnaMarksCov` push/pop/sort preservation lemmas, `BumpCoreShape` /
`FullBumpInv` state invariants, and `FullMem` + `m6ExtMem` call wrappers for
`m6_hdr_*`, `full_sort_ana_qs_m6`, `full_queue_mtf`, `full_bump_var`, and
`full_bump_decay`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Bump

open LeanQbe.T
open LeanQbe.T.C0Agrees
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Tiers.Spec
open LeanQbe.T.Examples.Kissat.Proof.Bump.Spec

public section

/-! ## 1. Core Shape and List Prefix Helpers -/

@[expose] def BumpCoreShape (c0 c1 : FullCoreState) : Prop :=
  c1 = { c0 with min_clr_len := c1.min_clr_len, mrk := c1.mrk, repr := c1.repr }

structure FullBumpInv (allow : Bool) (c : FullCfg)
    (ext0 : List (BitVec 64)) (s0 : FullState)
    (ext1 : List (BitVec 64)) (s1 : FullState) : Prop where
  len : s1.LengthsOk c
  shape : BumpCoreShape s0.core s1.core
  ext_ok : M6HdrExtOk ext1
  init_pres : M6HdrExtInitOk ext0 → M6HdrExtInitOk ext1 ∧ M6ExtW2bPres ext0 ext1
  ext_scr : FullExtScratchPres s0 s1
  ws2 : s1.scratch.work_stk2 = s0.scratch.work_stk2
  cov_pres : FullAnaMarksCov c s0 → FullAnaMarksCov c s1
  mcl_le : s1.core.min_clr_len ≤ s0.core.cur_vars
  cov_k : ∀ k < s1.core.min_clr_len,
    (s1.scratch.work_stk1[k]?.getD 0#32).toNat < s0.core.cur_vars
  false_pres : allow = false →
    s1.core.mrk = s0.core.mrk ∧ s1.core.min_clr_len = s0.core.min_clr_len ∧ ext1 = ext0

theorem bumpCoreShape_refl (c0 : FullCoreState) : BumpCoreShape c0 c0 := rfl

theorem bumpCoreShape_trans {c0 c1 c2 : FullCoreState}
    (h1 : BumpCoreShape c0 c1) (h2 : BumpCoreShape c1 c2) : BumpCoreShape c0 c2 := by
  rw [h2, h1]; rfl

theorem bumpCoreShape_of_eq {c0 c1 c2 : FullCoreState}
    (h1 : BumpCoreShape c0 c1) (heq : c2 = c1) : BumpCoreShape c0 c2 := by
  rw [heq]; exact h1

theorem bumpCoreShape_set_mrk_mcl {c0 c1 : FullCoreState}
    (h : BumpCoreShape c0 c1) (mrk' : List (BitVec 8)) (mcl' : Nat) :
    BumpCoreShape c0 { c1 with mrk := mrk', min_clr_len := mcl' } := by
  rw [h]; rfl

theorem bumpCoreShape_set_mcl_mrk {c0 c1 : FullCoreState}
    (h : BumpCoreShape c0 c1) (mcl' : Nat) (mrk' : List (BitVec 8)) :
    BumpCoreShape c0 { c1 with min_clr_len := mcl', mrk := mrk' } := by
  rw [h]; rfl

theorem bumpCoreShape_set_repr {c0 c1 : FullCoreState}
    (h : BumpCoreShape c0 c1) (repr' : List (BitVec 32)) :
    BumpCoreShape c0 { c1 with repr := repr' } := by
  rw [h]; rfl

theorem list_take_succ_elem {α : Type _} (xs : List α) {n : Nat} (hn : n < xs.length) :
    xs.take (n + 1) = xs.take n ++ [xs[n]'hn] := by
  apply List.ext_getElem?
  intro k
  have hmin : min n xs.length = n := Nat.min_eq_left (Nat.le_of_lt hn)
  rw [List.getElem?_take]
  split
  · by_cases hkn : k < n
    · rw [List.getElem?_append_left (by simp [List.length_take, hmin]; exact hkn),
        List.getElem?_take]
      split
      · rfl
      · omega
    · have hke : k = n := by omega
      subst hke
      rw [List.getElem?_append_right (by simp [List.length_take, hmin]),
        List.length_take, hmin, Nat.sub_self]
      simp [List.getElem?_eq_getElem hn]
  · rw [List.getElem?_append_right (by simp [List.length_take, hmin]; omega),
      List.length_take, hmin, List.getElem?_eq_none (by simp; omega)]

theorem list_take_succ_set {α : Type _} (xs : List α) {n : Nat} (hn : n < xs.length) (v : α) :
    (xs.set n v).take (n + 1) = xs.take n ++ [v] := by
  have hn' : n < (xs.set n v).length := by simp [hn]
  rw [list_take_succ_elem (xs.set n v) hn', List.getElem_set_self]
  congr 1
  apply List.ext_getElem?
  intro k
  simp only [List.getElem?_take]
  by_cases hkn : k < n
  · simp [hkn, List.getElem?_set_ne (by omega : n ≠ k)]
  · simp [hkn]

theorem mem_map_take_iff {n : Nat} {xs : List (BitVec 32)} (hn : n ≤ xs.length) {v : Nat} :
    v ∈ (xs.take n).map BitVec.toNat ↔
      ∃ k < n, (xs[k]?.getD 0#32).toNat = v := by
  rw [List.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [List.mem_iff_getElem] at hx
    obtain ⟨k, hk, hkx⟩ := hx
    rw [List.length_take, Nat.min_eq_left hn] at hk
    have hkx' : xs[k]'(by omega) = x := by
      simpa [List.getElem_take] using hkx
    refine ⟨k, hk, ?_⟩
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some, hkx']
  · rintro ⟨k, hkn, hkv⟩
    refine ⟨xs[k]'(by omega), ?_, ?_⟩
    · rw [List.mem_iff_getElem]
      refine ⟨k, by rw [List.length_take, Nat.min_eq_left hn]; exact hkn, ?_⟩
      simp [List.getElem_take]
    · have h1 := hkv
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at h1
      exact h1

/-! ## 2. `FullAnaMarksCov` Push, Pop, and Sort Preservation -/

theorem fullAnaMarksCov_push {c : FullCfg} {s : FullState} {ov : BitVec 32}
    (hlen : s.LengthsOk c) (hcov : FullAnaMarksCov c s)
    (hov_lt : ov.toNat < s.core.cur_vars)
    (hmrk0 : s.core.mrk[ov.toNat]? = some 0#8)
    (hmcl_lt : s.core.min_clr_len < s.core.cur_vars) :
    let s' : FullState :=
      { s with
        core := { s.core with
          mrk := s.core.mrk.set ov.toNat 1#8
          min_clr_len := s.core.min_clr_len + 1 }
        scratch := { s.scratch with
          work_stk1 := s.scratch.work_stk1.set s.core.min_clr_len ov } }
    s'.LengthsOk c ∧ FullAnaMarksCov c s' := by
  have hok := hlen.core_ok
  have hsok := hlen.scratch_ok
  have hcv_le := hok.cur_vars_le
  have hna_len := hsok.work_stk1_len
  have hmrk_len := hok.mrk_len
  have hn_na : s.core.min_clr_len < s.scratch.work_stk1.length := by rw [hna_len]; omega
  have hov_mrk : ov.toNat < s.core.mrk.length := by rw [hmrk_len]; omega
  have hlen' :
      FullState.LengthsOk c
        { s with
          core := { s.core with
            mrk := s.core.mrk.set ov.toNat 1#8
            min_clr_len := s.core.min_clr_len + 1 }
          scratch := { s.scratch with
            work_stk1 := s.scratch.work_stk1.set s.core.min_clr_len ov } } :=
    ⟨{ hok with mrk_len := by simp [hmrk_len], min_clr_len_le := by dsimp only; omega },
     { hsok with work_stk1_len := by simp [hna_len] }⟩
  refine ⟨hlen', by dsimp only; omega, ?_, ?_, ?_⟩
  · dsimp only
    rw [list_take_succ_set s.scratch.work_stk1 hn_na ov, List.map_append, List.nodup_append]
    refine ⟨hcov.2.1, List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩, fun x hx y hy hxy => ?_⟩
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hy
    subst hy; rw [hxy] at hx
    rw [mem_map_take_iff (Nat.le_of_lt hn_na)] at hx
    obtain ⟨k, hkn, hkv⟩ := hx
    have hk_mrk := (hcov.2.2.1 k hkn).2
    rw [hkv, hmrk0, Option.getD_some] at hk_mrk
    exact hk_mrk rfl
  · intro k hk
    dsimp only at hk ⊢
    by_cases hkn : k < s.core.min_clr_len
    · have hk_orig := hcov.2.2.1 k hkn
      have hws_eq : (s.scratch.work_stk1.set s.core.min_clr_len ov)[k]? =
          s.scratch.work_stk1[k]? := List.getElem?_set_ne (by omega)
      rw [hws_eq]
      refine ⟨hk_orig.1, ?_⟩
      have hne : (s.scratch.work_stk1[k]?.getD 0#32).toNat ≠ ov.toNat := by
        intro heq
        have hk2 := hk_orig.2
        rw [heq, hmrk0, Option.getD_some] at hk2
        exact hk2 rfl
      rw [List.getElem?_set_ne hne.symm]
      exact hk_orig.2
    · have hke : k = s.core.min_clr_len := by omega
      subst hke
      rw [List.getElem?_set_self hn_na, Option.getD_some,
        List.getElem?_set_self hov_mrk, Option.getD_some]
      exact ⟨hov_lt, by decide⟩
  · intro v hv hmrk'
    dsimp only at hmrk' ⊢
    by_cases hveq : v = ov.toNat
    · refine ⟨s.core.min_clr_len, by omega, ?_⟩
      rw [List.getElem?_set_self hn_na, Option.getD_some, hveq]
    · rw [List.getElem?_set_ne (Ne.symm hveq)] at hmrk'
      obtain ⟨i, hi, hiv⟩ := hcov.2.2.2 v hv hmrk'
      refine ⟨i, by omega, ?_⟩
      rw [List.getElem?_set_ne (by omega)]
      exact hiv

theorem fullAnaMarksCov_pop {c : FullCfg} {s : FullState}
    (hlen : s.LengthsOk c) (hcov : FullAnaMarksCov c s) (hgt : 0 < s.core.min_clr_len) :
    let n1 := s.core.min_clr_len - 1
    let hn1_na : n1 < s.scratch.work_stk1.length := by
      have := hlen.scratch_ok.work_stk1_len
      have := hcov.1
      have := hlen.core_ok.cur_vars_le
      omega
    let rv := s.scratch.work_stk1[n1]'hn1_na
    let s' : FullState :=
      { s with core := { s.core with min_clr_len := n1, mrk := s.core.mrk.set rv.toNat 0#8 } }
    rv.toNat < s.core.cur_vars ∧ s'.LengthsOk c ∧ FullAnaMarksCov c s' := by
  have hok := hlen.core_ok
  have hsok := hlen.scratch_ok
  have hcv_le := hok.cur_vars_le
  have hna_len := hsok.work_stk1_len
  have hmrk_len := hok.mrk_len
  have hmcl_le := hcov.1
  let n1 := s.core.min_clr_len - 1
  have hn1_lt : n1 < s.core.min_clr_len := by omega
  have hn1_na : n1 < s.scratch.work_stk1.length := by rw [hna_len]; omega
  let rv := s.scratch.work_stk1[n1]'hn1_na
  have hrv_lt : rv.toNat < s.core.cur_vars := by
    have h1 := (hcov.2.2.1 n1 hn1_lt).1
    simpa [rv, List.getElem?_eq_getElem hn1_na, Option.getD_some] using h1
  have hsucc_eq : n1 + 1 = s.core.min_clr_len := by omega
  have htake_eq : (s.scratch.work_stk1.take s.core.min_clr_len).map BitVec.toNat =
      (s.scratch.work_stk1.take n1).map BitVec.toNat ++ [rv.toNat] := by
    rw [← hsucc_eq, list_take_succ_elem s.scratch.work_stk1 hn1_na, List.map_append]
    rfl
  have hnodup_split := hcov.2.1
  rw [htake_eq, List.nodup_append] at hnodup_split
  have hmcl_n1_le : n1 ≤ c.max_vars := by omega
  have hlen' :
      FullState.LengthsOk c
        { s with
          core := { s.core with min_clr_len := n1, mrk := s.core.mrk.set rv.toNat 0#8 } } :=
    ⟨{ hok with mrk_len := by simp [hmrk_len], min_clr_len_le := hmcl_n1_le }, hsok⟩
  refine ⟨hrv_lt, hlen', by dsimp only; omega, hnodup_split.1, ?_, ?_⟩
  · intro k hk
    dsimp only at hk ⊢
    have hk_orig := hcov.2.2.1 k (by omega)
    refine ⟨hk_orig.1, ?_⟩
    have hne : (s.scratch.work_stk1[k]?.getD 0#32).toNat ≠ rv.toNat := by
      intro heq
      have hmem : (s.scratch.work_stk1[k]?.getD 0#32).toNat ∈
          (s.scratch.work_stk1.take n1).map BitVec.toNat := by
        rw [mem_map_take_iff (by omega)]
        exact ⟨k, hk, rfl⟩
      exact hnodup_split.2.2 _ hmem rv.toNat (by simp) heq
    rw [List.getElem?_set_ne hne.symm]
    exact hk_orig.2
  · intro v hv hmrk'
    dsimp only at hmrk' ⊢
    by_cases hveq : v = rv.toNat
    · exfalso
      have hrv_mrk : rv.toNat < s.core.mrk.length := by rw [hmrk_len]; omega
      rw [hveq, List.getElem?_set_self hrv_mrk, Option.getD_some] at hmrk'
      exact hmrk' rfl
    · rw [List.getElem?_set_ne (Ne.symm hveq)] at hmrk'
      obtain ⟨i, hi, hiv⟩ := hcov.2.2.2 v hv hmrk'
      refine ⟨i, ?_, hiv⟩
      have hine : i ≠ n1 := by
        intro hie; subst hie
        rw [List.getElem?_eq_getElem hn1_na, Option.getD_some] at hiv
        exact hveq hiv.symm
      omega

theorem fullAnaMarksCov_sort {c : FullCfg} {s : FullState}
    {ws1' repr' : List (BitVec 32)} {wsort' sbuf' : List (BitVec 32)}
    (hlen : s.LengthsOk c) (hcov : FullAnaMarksCov c s)
    (hws1 : ws1'.length = 2 * c.max_vars)
    (hpm : (ws1'.take s.core.min_clr_len).Perm
      (s.scratch.work_stk1.take s.core.min_clr_len))
    (hcov' : ∀ k < s.core.min_clr_len, (ws1'[k]?.getD 0#32).toNat < s.core.cur_vars) :
    FullAnaMarksCov c { s with
      core := { s.core with repr := repr' }
      scratch := { s.scratch with
        work_stk1 := ws1', wsort := wsort', scratch_buf := sbuf' } } := by
  have hok := hlen.core_ok
  have hsok := hlen.scratch_ok
  have hcv_le := hok.cur_vars_le
  have hna_len := hsok.work_stk1_len
  have h1 := hcov.1
  have hmcl_le : s.core.min_clr_len ≤ 2 * c.max_vars := by omega
  have hpm_map : ((ws1'.take s.core.min_clr_len).map BitVec.toNat).Perm
      ((s.scratch.work_stk1.take s.core.min_clr_len).map BitVec.toNat) :=
    hpm.map BitVec.toNat
  refine ⟨hcov.1, hpm_map.nodup_iff.mpr hcov.2.1, ?_, ?_⟩
  · intro k hk
    refine ⟨hcov' k hk, ?_⟩
    have hmem : (ws1'[k]?.getD 0#32).toNat ∈
        (s.scratch.work_stk1.take s.core.min_clr_len).map BitVec.toNat := by
      rw [← hpm_map.mem_iff, mem_map_take_iff (by omega)]
      exact ⟨k, hk, rfl⟩
    rw [mem_map_take_iff (by omega)] at hmem
    obtain ⟨j, hj, hjv⟩ := hmem
    rw [← hjv]
    exact (hcov.2.2.1 j hj).2
  · intro v hv hmrk
    obtain ⟨i, hi, hiv⟩ := hcov.2.2.2 v hv hmrk
    have hmem : v ∈ (ws1'.take s.core.min_clr_len).map BitVec.toNat := by
      rw [hpm_map.mem_iff, mem_map_take_iff (by omega)]
      exact ⟨i, hi, hiv⟩
    rw [mem_map_take_iff (by omega)] at hmem
    exact hmem

/-! ## 3. `FullBumpInv` Transitions and `FullM6HdrMem` Call Wrappers -/

theorem fullBumpInv_init {allow : Bool} {c : FullCfg} {ext : List (BitVec 64)} {s : FullState}
    (hlen : s.LengthsOk c) (hext : M6HdrExtOk ext) (hpre : FullBumpPre allow c s) :
    FullBumpInv allow c ext s ext s := by
  have hmcl_le : s.core.min_clr_len ≤ s.core.cur_vars := by
    cases allow
    · exact hpre.1
    · exact hpre.1
  have hcov_k : ∀ k < s.core.min_clr_len,
      (s.scratch.work_stk1[k]?.getD 0#32).toNat < s.core.cur_vars := by
    cases allow
    · exact hpre.2
    · exact fun k hk => (hpre.2.2.1 k hk).1
  exact ⟨hlen, rfl, hext, fun hi => ⟨hi, M6ExtW2bPres.refl ext⟩, ⟨rfl, rfl⟩, rfl,
    fun h => h, hmcl_le, hcov_k, fun _ => ⟨rfl, rfl, rfl⟩⟩

theorem fullBumpInv_inc_ticks {c : FullCfg} {ext0 ext1 : List (BitVec 64)} {s0 s1 : FullState}
    (inv : FullBumpInv true c ext0 s0 ext1 s1) (dt : BitVec 64) :
    let s2 : FullState := { s1 with scratch := { s1.scratch with search_ticks := dt } }
    FullBumpInv true c ext0 s0 ext1 s2 :=
  ⟨⟨inv.len.core_ok, by cases inv.len.scratch_ok; constructor <;> assumption⟩,
    inv.shape, inv.ext_ok, inv.init_pres, inv.ext_scr, inv.ws2, inv.cov_pres,
    inv.mcl_le, inv.cov_k, fun h => Bool.noConfusion h⟩

theorem fullBumpInv_push {c : FullCfg} {ext0 ext1 : List (BitVec 64)} {s0 s1 : FullState}
    {ov : BitVec 32} (inv : FullBumpInv true c ext0 s0 ext1 s1)
    (hcov0 : FullAnaMarksCov c s0)
    (hov_lt : ov.toNat < s0.core.cur_vars)
    (hmrk0 : s1.core.mrk[ov.toNat]? = some 0#8)
    (hmcl_lt : s1.core.min_clr_len < s0.core.cur_vars) :
    let s2 : FullState :=
      { s1 with
        core := { s1.core with
          mrk := s1.core.mrk.set ov.toNat 1#8
          min_clr_len := s1.core.min_clr_len + 1 }
        scratch := { s1.scratch with
          work_stk1 := s1.scratch.work_stk1.set s1.core.min_clr_len ov } }
    FullBumpInv true c ext0 s0 ext1 s2 := by
  have hcv_eq : s1.core.cur_vars = s0.core.cur_vars := by rw [inv.shape]
  have ⟨hlen2, hcov2⟩ := fullAnaMarksCov_push inv.len (inv.cov_pres hcov0)
    (by omega) hmrk0 (by omega)
  exact ⟨hlen2, bumpCoreShape_set_mrk_mcl inv.shape _ _, inv.ext_ok, inv.init_pres,
    inv.ext_scr, inv.ws2, fun _ => hcov2, by dsimp only; omega,
    fun k hk => by rw [← hcv_eq]; exact (hcov2.2.2.1 k hk).1, fun h => Bool.noConfusion h⟩

theorem fullBumpInv_pop {c : FullCfg} {ext0 ext1 : List (BitVec 64)} {s0 s1 : FullState}
    (inv : FullBumpInv true c ext0 s0 ext1 s1) (hcov0 : FullAnaMarksCov c s0)
    (hgt : 0 < s1.core.min_clr_len) :
    let n1 := s1.core.min_clr_len - 1
    let hn1_na : n1 < s1.scratch.work_stk1.length := by
      have := inv.len.scratch_ok.work_stk1_len
      have := inv.mcl_le
      have := inv.len.core_ok.cur_vars_le
      have hcv_eq : s1.core.cur_vars = s0.core.cur_vars := by rw [inv.shape]
      omega
    let rv := s1.scratch.work_stk1[n1]'hn1_na
    let s2 : FullState :=
      { s1 with core := { s1.core with min_clr_len := n1, mrk := s1.core.mrk.set rv.toNat 0#8 } }
    rv.toNat < s0.core.cur_vars ∧ FullBumpInv true c ext0 s0 ext1 s2 := by
  have hcv_eq : s1.core.cur_vars = s0.core.cur_vars := by rw [inv.shape]
  obtain ⟨hrv, hlen2, hcov2⟩ := fullAnaMarksCov_pop inv.len (inv.cov_pres hcov0) hgt
  refine ⟨by rw [← hcv_eq]; exact hrv,
    hlen2, bumpCoreShape_set_mcl_mrk inv.shape _ _, inv.ext_ok, inv.init_pres,
    inv.ext_scr, inv.ws2, fun _ => hcov2, by dsimp only; have := inv.mcl_le; omega,
    fun k hk => by rw [← hcv_eq]; exact (hcov2.2.2.1 k hk).1, fun h => Bool.noConfusion h⟩

theorem fullBumpInv_sort {allow : Bool} {c : FullCfg} {ext0 ext1 : List (BitVec 64)}
    {s0 s1 : FullState} {ws1' repr' wsort' sbuf' : List (BitVec 32)}
    (inv : FullBumpInv allow c ext0 s0 ext1 s1)
    (hws1 : ws1'.length = 2 * c.max_vars) (hrep : repr'.length = 2 * c.max_vars)
    (hwso : wsort'.length = 2 * c.max_vars) (hsbu : sbuf'.length = c.scratch_cap)
    (hpm : (ws1'.take s1.core.min_clr_len).Perm
      (s1.scratch.work_stk1.take s1.core.min_clr_len))
    (hcov' : ∀ k < s1.core.min_clr_len, (ws1'[k]?.getD 0#32).toNat < s1.core.cur_vars) :
    let s2 : FullState :=
      { s1 with
        core := { s1.core with repr := repr' }
        scratch := { s1.scratch with
          work_stk1 := ws1', wsort := wsort', scratch_buf := sbuf' } }
    FullBumpInv allow c ext0 s0 ext1 s2 := by
  have hok := inv.len.core_ok
  have hsok := inv.len.scratch_ok
  have hcv_eq : s1.core.cur_vars = s0.core.cur_vars := by rw [inv.shape]
  have hlen2 :
      FullState.LengthsOk c
        { s1 with
          core := { s1.core with repr := repr' }
          scratch := { s1.scratch with
            work_stk1 := ws1', wsort := wsort', scratch_buf := sbuf' } } :=
    ⟨{ hok with repr_len := hrep },
     { hsok with work_stk1_len := hws1, wsort_len := hwso, scratch_buf_len := hsbu }⟩
  refine ⟨hlen2, bumpCoreShape_set_repr inv.shape repr', inv.ext_ok, inv.init_pres,
    inv.ext_scr, inv.ws2, ?_, inv.mcl_le, ?_, inv.false_pres⟩
  · intro hcov0
    exact fullAnaMarksCov_sort inv.len (inv.cov_pres hcov0) hws1 hpm hcov'
  · intro k hk
    rw [← hcv_eq]
    exact hcov' k hk

theorem fullBumpInv_of_safety {allow : Bool} {c : FullCfg} {ext0 ext1 : List (BitVec 64)}
    {s0 s1 s2 : FullState} (inv : FullBumpInv allow c ext0 s0 ext1 s1)
    (hcore : s2.core = s1.core) (hlen2 : s2.LengthsOk c) (hpres : FullProbeScratchPres s1 s2) :
    FullBumpInv allow c ext0 s0 ext1 s2 := by
  have hcov2 : FullAnaMarksCov c s0 → FullAnaMarksCov c s2 := by
    intro h0
    have h1 := inv.cov_pres h0
    rcases h1 with ⟨h1a, h1b, h1c, h1d⟩
    refine ⟨by rw [hcore]; exact h1a, ?_, ?_, ?_⟩
    · rw [hcore, hpres.2.1]; exact h1b
    · intro k hk; rw [hcore] at hk; rw [hcore, hpres.2.1]; exact h1c k hk
    · intro v hv hm; rw [hcore] at hm ⊢; rw [hpres.2.1]; exact h1d v hv hm
  refine ⟨hlen2, bumpCoreShape_of_eq inv.shape hcore, inv.ext_ok, inv.init_pres,
    ⟨hpres.1.1.trans inv.ext_scr.1, hpres.1.2.trans inv.ext_scr.2⟩,
    hpres.2.2.1.trans inv.ws2, hcov2, ?_, ?_, ?_⟩
  · rw [hcore]; exact inv.mcl_le
  · intro k hk; rw [hcore] at hk; rw [hpres.2.1]; exact inv.cov_k k hk
  · intro hf; rw [hcore]; exact inv.false_pres hf

theorem fullBumpInv_of_m6h {c : FullCfg} {ext0 ext1 ext2 : List (BitVec 64)}
    {s0 s1 s2 : FullState} (inv : FullBumpInv true c ext0 s0 ext1 s1)
    (hcore : s2.core = s1.core) (hlen2 : s2.LengthsOk c)
    (hpres : M6HdrScratchPres s1 s2) (hext2 : M6HdrExtOk ext2)
    (hinit2 : M6HdrExtInitOk ext1 → M6HdrExtInitOk ext2 ∧ M6ExtW2bPres ext1 ext2) :
    FullBumpInv true c ext0 s0 ext2 s2 := by
  have hext := M6HdrScratchPres.extPres hpres
  have hws1 := M6HdrScratchPres.ws1 hpres
  have hws2 := M6HdrScratchPres.ws2 hpres
  have hcov2 : FullAnaMarksCov c s0 → FullAnaMarksCov c s2 := by
    intro h0
    have h1 := inv.cov_pres h0
    rcases h1 with ⟨h1a, h1b, h1c, h1d⟩
    refine ⟨by rw [hcore]; exact h1a, ?_, ?_, ?_⟩
    · rw [hcore, hws1]; exact h1b
    · intro k hk; rw [hcore] at hk; rw [hcore, hws1]; exact h1c k hk
    · intro v hv hm; rw [hcore] at hm ⊢; rw [hws1]; exact h1d v hv hm
  exact ⟨hlen2, bumpCoreShape_of_eq inv.shape hcore, hext2,
    fun h0 => let ⟨h1, hw1⟩ := inv.init_pres h0; let ⟨h2, hw2⟩ := hinit2 h1; ⟨h2, hw1.trans hw2⟩,
    ⟨hext.1.trans inv.ext_scr.1, hext.2.trans inv.ext_scr.2⟩,
    hws2.trans inv.ws2, hcov2, by rw [hcore]; exact inv.mcl_le,
    fun k hk => by rw [hcore] at hk; rw [hws1]; exact inv.cov_k k hk,
    fun h => Bool.noConfusion h⟩

theorem fullBumpInv_finish {allow : Bool} {Q : Post []} {c : FullCfg} {ext0 ext1 : List (BitVec 64)}
    {s0 s1 : FullState} {R : Mem 64 → Prop} {m1 : Mem 64}
    (inv : FullBumpInv allow c ext0 s0 ext1 s1)
    (hm1 : (FullMem c s1 ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext1 ⋆ R)) m1)
    (hQ : ∀ (mrk' : List (BitVec 8)) (mcl' : Nat) (repr' : List (BitVec 32))
        (sc' : FullScratch) (ext' : List (BitVec 64)) (m' : Mem 64),
      let s' : FullState :=
        { core := { s0.core with min_clr_len := mcl', mrk := mrk', repr := repr' }
          scratch := sc' }
      s'.LengthsOk c → (FullAnaMarksCov c s0 → FullAnaMarksCov c s') →
      (allow = false → mrk' = s0.core.mrk ∧ mcl' = s0.core.min_clr_len ∧ ext' = ext0) →
      (allow = false → ∀ k < mcl', (sc'.work_stk1[k]?.getD 0#32).toNat < s0.core.cur_vars) →
      FullExtScratchPres s0 s' → sc'.work_stk2 = s0.scratch.work_stk2 →
      M6HdrExtOk ext' → (M6HdrExtInitOk ext0 → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext0 ext') →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q () m') :
    Q () m1 := by
  let c_rec : FullCoreState :=
    { s0.core with min_clr_len := s1.core.min_clr_len, mrk := s1.core.mrk, repr := s1.core.repr }
  let s_rec : FullState := { core := c_rec, scratch := s1.scratch }
  have hs_eq : s_rec = s1 := by
    cases s1; dsimp only [s_rec, c_rec] at *; rw [← inv.shape]
  have hm_m6 : (FullM6HdrMem c ext1 s_rec ⋆ R) m1 := by
    rw [hs_eq]; exact fullM6HdrMem_unfocus_full hm1
  exact hQ s1.core.mrk s1.core.min_clr_len s1.core.repr s1.scratch ext1 m1
    (hs_eq ▸ inv.len) (fun h0 => hs_eq ▸ inv.cov_pres h0) inv.false_pres
    (fun _ k hk => inv.cov_k k hk) (hs_eq ▸ inv.ext_scr) inv.ws2 inv.ext_ok inv.init_pres hm_m6

theorem bump_call_w2a {Γ : Env} {Q : Post []} {X : XPost} {f : Sym}
    {extraArgs rs : List Ty} {args : Tup (Arg Val) (i64 :: extraArgs)}
    {k : Tup Val rs → Expr Val Cont []}
    {c : FullCfg} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hFn : Γ.Has f (m6HdrW2aSpec extraArgs rs))
    (harg : (vals args).fst = c.hdr) (hcfg : FullM6HdrCfgOk c)
    (hext : M6HdrExtOk ext) (hlen : s.LengthsOk c)
    (hm : (FullMem c s ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R)) m)
    (hK : ∀ r ext' s' m', s'.core = s.core → s'.LengthsOk c →
      M6HdrScratchPres s s' → M6HdrExtOk ext' →
      (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext ext') →
      (FullMem c s' ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext' ⋆ R)) m' →
      wp Γ Q X (k r) m') :
    wp Γ Q X (Expr.call f args k) m := by
  c0_call hFn
  exact m6HdrW2aSpec_of harg hcfg hext hlen (fullM6HdrMem_unfocus_full hm)
    fun r ext' s' m' hc' hl' hp' he' hi' hm' =>
      hK r ext' s' m' hc' hl' hp' he' hi' (fullM6HdrMem_focus_full hm')

theorem bump_call_dr_allow {Γ : Env} {Q : Post []} {X : XPost}
    {harg_v : Arg Val i64} {k : Tup Val [.bool] → Expr Val Cont []}
    {c : FullCfg} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hFn : Γ.Has "m6_hdr_dr_allow" m6HdrDrAllowSpec)
    (harg : harg_v.val = c.hdr) (hcfg : FullM6HdrCfgOk c)
    (hext : M6HdrExtOk ext) (hlen : s.LengthsOk c)
    (hm : (FullMem c s ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R)) m)
    (hK : ∀ r ext' m', M6HdrExtInitOk ext' →
      (M6HdrExtInitOk ext → ext' = ext) →
      (FullMem c s ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext' ⋆ R)) m' →
      wp Γ Q X (k (r, PUnit.unit)) m') :
    wp Γ Q X (Expr.call "m6_hdr_dr_allow" (as := [i64]) (harg_v, PUnit.unit) k) m := by
  c0_call hFn
  rw [harg]
  exact m6HdrDrAllowSpec_of hcfg hext hlen (fullM6HdrMem_unfocus_full hm)
    fun r ext' m' hi' heq' hm' =>
      hK r ext' m' hi' heq' (fullM6HdrMem_focus_full hm')

private theorem fullProbeScratchPres_of_scratchModifies {mod : List ScratchField}
    {s s' : FullState} (h : ScratchModifies mod s s')
    (h0 : .last_learned ∉ mod) (h1 : .extend_len ∉ mod) (h2 : .work_stk1 ∉ mod)
    (h3 : .work_stk2 ∉ mod) (h4 : .tarjan_mark ∉ mod) (h5 : .scratch_buf ∉ mod)
    (h6 : .ant_sz ∉ mod) (h7 : .res_sz ∉ mod) (h8 : .sim_sig ∉ mod) :
    FullProbeScratchPres s s' :=
  ⟨⟨ScratchModifies.get_of_not_mem h h0, ScratchModifies.get_of_not_mem h h1⟩,
   ScratchModifies.get_of_not_mem h h2, ScratchModifies.get_of_not_mem h h3,
   ScratchModifies.get_of_not_mem h h4, ScratchModifies.get_of_not_mem h h5,
   ScratchModifies.get_of_not_mem h h6, ScratchModifies.get_of_not_mem h h7,
   ScratchModifies.get_of_not_mem h h8⟩

theorem bump_call_full_var {Γ : Env} {Q : Post []} {X : XPost} {f : Sym}
    {sp : Spec [i64, i32] []} {mod : List ScratchField}
    {harg_v : Arg Val i64} {bvarg : Arg Val i32} {k : Tup Val [] → Expr Val Cont []}
    {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hsp : sp = FullContract.toSpec (W := Unit)
      { pre := fun _ _ _ () => True
        post := fun _ s _ () _ s' => CorePres s s' ∧ ScratchModifies mod s s' })
    (hFn : Γ.Has f sp)
    (h0 : .last_learned ∉ mod) (h1 : .extend_len ∉ mod) (h2 : .work_stk1 ∉ mod)
    (h3 : .work_stk2 ∉ mod) (h4 : .tarjan_mark ∉ mod) (h5 : .scratch_buf ∉ mod)
    (h6 : .ant_sz ∉ mod) (h7 : .res_sz ∉ mod) (h8 : .sim_sig ∉ mod)
    (harg : harg_v.val = c.hdr)
    (hlen : s.LengthsOk c) (hm : (FullMem c s ⋆ R) m)
    (hK : ∀ s' m', s'.core = s.core → s'.LengthsOk c → FullProbeScratchPres s s' →
      (FullMem c s' ⋆ R) m' → wp Γ Q X (k PUnit.unit) m') :
    wp Γ Q X
      (Expr.call f (as := [i64, i32]) (harg_v, bvarg, PUnit.unit) k) m := by
  c0_call hFn
  rw [harg, hsp]
  refine FullContract.intro (w := ()) hlen trivial hm ?_
  intro _ s' m' hlen' ⟨hcore', hmod'⟩ hm'
  exact hK s' m' hcore' hlen'
    (fullProbeScratchPres_of_scratchModifies hmod' h0 h1 h2 h3 h4 h5 h6 h7 h8) hm'

theorem bump_call_full_void {Γ : Env} {Q : Post []} {X : XPost} {f : Sym}
    {sp : Spec [i64] []} {mod : List ScratchField}
    {harg_v : Arg Val i64} {k : Tup Val [] → Expr Val Cont []}
    {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hsp : sp = FullContract.toSpec (W := Unit)
      { pre := fun _ _ _ () => True
        post := fun _ s _ () _ s' => CorePres s s' ∧ ScratchModifies mod s s' })
    (hFn : Γ.Has f sp)
    (h0 : .last_learned ∉ mod) (h1 : .extend_len ∉ mod) (h2 : .work_stk1 ∉ mod)
    (h3 : .work_stk2 ∉ mod) (h4 : .tarjan_mark ∉ mod) (h5 : .scratch_buf ∉ mod)
    (h6 : .ant_sz ∉ mod) (h7 : .res_sz ∉ mod) (h8 : .sim_sig ∉ mod)
    (harg : harg_v.val = c.hdr)
    (hlen : s.LengthsOk c) (hm : (FullMem c s ⋆ R) m)
    (hK : ∀ s' m', s'.core = s.core → s'.LengthsOk c → FullProbeScratchPres s s' →
      (FullMem c s' ⋆ R) m' → wp Γ Q X (k PUnit.unit) m') :
    wp Γ Q X (Expr.call f (as := [i64]) (harg_v, PUnit.unit) k) m := by
  c0_call hFn
  rw [harg, hsp]
  refine FullContract.intro (w := ()) hlen trivial hm ?_
  intro _ s' m' hlen' ⟨hcore', hmod'⟩ hm'
  exact hK s' m' hcore' hlen'
    (fullProbeScratchPres_of_scratchModifies hmod' h0 h1 h2 h3 h4 h5 h6 h7 h8) hm'

theorem bump_call_sort_ana {Γ : Env} {Q : Post []} {X : XPost}
    {harg_v narg : Arg Val i64} {k : Tup Val [] → Expr Val Cont []}
    {c : FullCfg} {s : FullState} {n : Val i64} {R : Mem 64 → Prop} {m : Mem 64}
    (hFn : Γ.Has "full_sort_ana_qs_m6" sortAnaQsSpec)
    (harg : harg_v.val = c.hdr) (hnarg : narg.val = n)
    (hlen : s.LengthsOk c) (hn_cv : n.toNat ≤ s.core.cur_vars)
    (hcov0 : ∀ k < n.toNat, (s.scratch.work_stk1[k]?.getD 0#32).toNat < s.core.cur_vars)
    (hm : (FullMem c s ⋆ R) m)
    (hK : ∀ ws1' repr' wsort' sbuf' m',
      ws1'.length = 2 * c.max_vars → repr'.length = 2 * c.max_vars →
      wsort'.length = 2 * c.max_vars → sbuf'.length = c.scratch_cap →
      (ws1'.take n.toNat).Perm (s.scratch.work_stk1.take n.toNat) →
      (∀ k, n.toNat ≤ k → ws1'[k]? = s.scratch.work_stk1[k]?) →
      (∀ k < n.toNat, (ws1'[k]?.getD 0#32).toNat < s.core.cur_vars) →
      (FullMem c { s with
        core := { s.core with repr := repr' }
        scratch := { s.scratch with
          work_stk1 := ws1', wsort := wsort', scratch_buf := sbuf' } } ⋆ R) m' →
      wp Γ Q X (k PUnit.unit) m') :
    wp Γ Q X
      (Expr.call "full_sort_ana_qs_m6" (as := [i64, i64]) (harg_v, narg, PUnit.unit) k) m := by
  c0_call hFn
  rw [harg, hnarg]
  dsimp only [sortAnaQsSpec]
  refine FullContract.intro (w := ()) hlen ⟨hn_cv, hcov0⟩ hm ?_
  intro _ s' m' hlen' ⟨hagr, hpm, htl, hcv'⟩ hm'
  have hcore_eq : s'.core = { s.core with repr := s'.core.repr } := by
    have h := congrArg (fun st => st.core) hagr
    cases hco : s.core; cases hco' : s'.core
    dsimp only [AgreesExcept, sortAnaQsMask] at h
    rw [hco, hco'] at h; cases h; rfl
  have hscr_eq : s'.scratch = { s.scratch with
      work_stk1 := s'.scratch.work_stk1, wsort := s'.scratch.wsort,
      scratch_buf := s'.scratch.scratch_buf } := by
    have h := congrArg (fun st => st.scratch) hagr
    cases hsc : s.scratch; cases hsc' : s'.scratch
    dsimp only [AgreesExcept, sortAnaQsMask] at h
    rw [hsc, hsc'] at h; cases h; rfl
  have hs'_eq : s' = { s with
      core := { s.core with repr := s'.core.repr }
      scratch := { s.scratch with
        work_stk1 := s'.scratch.work_stk1, wsort := s'.scratch.wsort,
        scratch_buf := s'.scratch.scratch_buf } } := by
    rcases s with ⟨cs, scs⟩; rcases s' with ⟨cs', scs'⟩
    dsimp only at hcore_eq hscr_eq ⊢; rw [hcore_eq, hscr_eq]
  rw [hs'_eq] at hm'
  exact hK s'.scratch.work_stk1 s'.core.repr s'.scratch.wsort s'.scratch.scratch_buf m'
    hlen'.scratch_ok.work_stk1_len hlen'.core_ok.repr_len hlen'.scratch_ok.wsort_len
    hlen'.scratch_ok.scratch_buf_len hpm htl hcv' hm'

end

end LeanQbe.T.Examples.Kissat.Proof.Bump
