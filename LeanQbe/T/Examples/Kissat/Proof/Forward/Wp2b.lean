/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Src.Forward
public import LeanQbe.T.Examples.Kissat.Proof.Forward.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Forward.Lemmas
import LeanQbe.T.Examples.Kissat.Proof.Forward.Wp1c
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation
meta import LeanQbe.T.Logic.C0Step
meta import LeanQbe.T.Logic.C0HeadStep

/-!
# Forward WP Proofs Part 2b (`Proof.Forward.Wp2b`)

`full_fwd_collect_sort_m7_wp` (`fullFwdCollectSortM7Spec`).

Zero legacy imports (`Full*`, `PatchModule`, `Solver`), `0` `@[expose]` on theorems/lemmas,
every file `<= 1,500`L, every decl `<= 450`L, every line `<= 100` cols.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Forward

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Forward
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Forward.Spec
open Kraken.Bedrock2.Test

open scoped FullArenaTactics

local macro "fwd_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

/-! ## 1. Collect/Sort Pure & Separation Helpers -/

private def CollectCandInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s0 sp : FullState) (R : Mem 64 → Prop) (x : BitVec 64 × FullState) (mj : Mem 64) : Prop :=
  FullDenseInvW c F0 F_cur x.2 ∧ x.2.core.cur_vars = s0.core.cur_vars ∧
  x.2.core.arena_len = s0.core.arena_len ∧ x.2.core.fuel = s0.core.fuel ∧
  x.2.core.oom = s0.core.oom ∧ x.2.core.inconsistent = s0.core.inconsistent ∧
  x.2.scratch.tarjan_mark = s0.scratch.tarjan_mark ∧
  fullArenaClauseRefs x.2 = fullArenaClauseRefs sp ∧
  x.1.toNat ≤ c.red_cap / 2 ∧
  (∀ i < x.1.toNat, (x.2.scratch.red_refs[i]?.getD 0#32).toNat ∈ fullArenaClauseRefs x.2) ∧
  (FullMem c x.2 ⋆ R) mj

private theorem fwd_collect_k_lit_bounds {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {sc : FullState} {p : BitVec 64} {k sz_p : BitVec 32} (harc : c.arena_cap < 2 * 2 ^ 28)
    (_hmx : c.max_vars < 2 * 2 ^ 28) (hdwc : FullDenseInvW c F0 F_cur sc)
    (hp_ref_c : p.toNat ∈ fullArenaClauseRefs sc) (hngc : fullArenaClauseGarb sc p.toNat = false)
    (hszc : fullArenaClauseSize sc p.toNat = sz_p.toNat) (hk_lt : k.toNat < sz_p.toNat) :
    have hwf_c := hdwc.2.1.arena.refs_wf p.toNat hp_ref_c
    have hszc' : sz_p.toNat = fullArenaClauseSizeCore sc.core p.toNat := hszc.symm
    have hal := hdwc.1.core_ok.arena_len_le
    have hpi : (p + 3#64 + k.setWidth 64).toNat < sc.core.arena.length := by
      rw [hdwc.1.core_ok.arena_len_arr]; c0_bound
    (sc.core.arena[(p + 3#64 + k.setWidth 64).toNat]'hpi).toNat < 2 * sc.core.cur_vars ∧
    ((sc.core.arena[(p + 3#64 + k.setWidth 64).toNat]'hpi).setWidth 64).toNat <
      sc.core.vals.length := by
  intro hwf_c hszc' hal hpi
  have hmem : (sc.core.arena[(p + 3#64 + k.setWidth 64).toNat]'hpi).toNat ∈
      fullArenaClauseLitsCore sc.core p.toNat := by
    rw [mem_fullArenaClauseLitsCore_iff (by rw [hdwc.1.core_ok.arena_len_arr]; omega)]
    exact ⟨k.toNat, by unfold fullArenaClauseSize at hszc; rw [hszc]; exact hk_lt,
      congrArg BitVec.toNat (fwd_getElem_congr (by c0_bound) _ _)⟩
  have hlt := hdwc.2.1.arena.lits_lt p.toNat hp_ref_c hngc _ hmem
  refine ⟨hlt, ?_⟩
  rw [hdwc.1.core_ok.vals_len]; have := hdwc.1.core_ok.cur_vars_le; c0_bound

private theorem fwd_collect_push_rr {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 sp sc : FullState} {p ncand : BitVec 64}
    (hdwc : FullDenseInvW c F0 F_cur sc) (hp_ref_c : p.toNat ∈ fullArenaClauseRefs sc)
    (hcvc : sc.core.cur_vars = s0.core.cur_vars) (halc : sc.core.arena_len = s0.core.arena_len)
    (hflc : sc.core.fuel = s0.core.fuel) (hoomc : sc.core.oom = s0.core.oom)
    (hincc : sc.core.inconsistent = s0.core.inconsistent)
    (htmkc : sc.scratch.tarjan_mark = s0.scratch.tarjan_mark)
    (hrrc : sc.scratch.red_refs = sp.scratch.red_refs)
    (hrefsc : fullArenaClauseRefs sc = fullArenaClauseRefs sp)
    (hrr_ok : ∀ i < ncand.toNat, (sp.scratch.red_refs[i]?.getD 0#32).toNat ∈ fullArenaClauseRefs sp)
    (hnc_lt : ncand.toNat < c.red_cap / 2) (hnc_rr : ncand.toNat < sc.scratch.red_refs.length)
    (hnc1 : (ncand + 1#64).toNat = ncand.toNat + 1) (hp32 : (p.setWidth 32).toNat = p.toNat)
    {mj : Mem 64} {R : Mem 64 → Prop}
    (hm : (FullMem c { sc with scratch := { sc.scratch with
        red_refs := sc.scratch.red_refs.set ncand.toNat (p.setWidth 32) } } ⋆ R) mj) :
    let sr : FullState := { sc with scratch := { sc.scratch with
      red_refs := sc.scratch.red_refs.set ncand.toNat (p.setWidth 32) } }
    CollectCandInv c F0 F_cur s0 sp R (ncand + 1#64, sr) mj := by
  intro sr
  have hdwr : FullDenseInvW c F0 F_cur sr :=
    fwd_denseInvW_with_scratch hdwc
      { hdwc.1.scratch_ok with red_refs_len := by simp [hdwc.1.scratch_ok.red_refs_len] }
      rfl rfl
  refine ⟨hdwr, hcvc, halc, hflc, hoomc, hincc, htmkc, hrefsc, by dsimp only; omega, ?_, hm⟩
  intro i hi; dsimp only [sr] at hi ⊢
  rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp (hnc1 ▸ hi)) with h | h
  · rw [List.getElem?_set_ne (by omega), hrrc]
    change _ ∈ fullArenaClauseRefs sc; rw [hrefsc]; exact hrr_ok i h
  · subst h; rw [List.getElem?_set_self hnc_rr, Option.getD_some, hp32]; exact hp_ref_c

private theorem fwd_collect_hist_refs {sp : FullState} {rr2 : List (BitVec 32)}
    {half_b i : BitVec 64} {half ncand : Nat}
    (hhi_idx : (half_b + i).toNat = half + i.toNat) (hhi_rr : (half_b + i).toNat < rr2.length)
    (hi_lt : i.toNat < ncand) (hi_rr : i.toNat < rr2.length)
    (hi1 : (i + 1#64).toNat = i.toNat + 1)
    (hrr_ok : ∀ k < ncand, (sp.scratch.red_refs[k]?.getD 0#32).toNat ∈ fullArenaClauseRefs sp)
    (hlo2 : ∀ k < ncand, rr2[k]? = sp.scratch.red_refs[k]?)
    (hhi2 : ∀ k < i.toNat, (rr2[half + k]?.getD 0#32).toNat ∈ fullArenaClauseRefs sp)
    (hnc_le : ncand ≤ half) :
    let rr3 := rr2.set (half_b + i).toNat (rr2[i.toNat]'hi_rr)
    (rr2[i.toNat]'hi_rr).toNat ∈ fullArenaClauseRefs sp ∧
    (∀ k < ncand, rr3[k]? = sp.scratch.red_refs[k]?) ∧
    (∀ k < (i + 1#64).toNat, (rr3[half + k]?.getD 0#32).toNat ∈ fullArenaClauseRefs sp) := by
  intro rr3
  have hcr_ref : (rr2[i.toNat]'hi_rr).toNat ∈ fullArenaClauseRefs sp := by
    have h0 := hrr_ok i.toNat hi_lt
    rwa [← hlo2 i.toNat hi_lt, List.getElem?_eq_getElem hi_rr, Option.getD_some] at h0
  refine ⟨hcr_ref, fun k hk => by
    dsimp only [rr3]; rw [List.getElem?_set_ne (by rw [hhi_idx]; omega)]; exact hlo2 k hk,
    fun k hk => by
    dsimp only [rr3]
    rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp (hi1 ▸ hk)) with h | h
    · rw [List.getElem?_set_ne (by rw [hhi_idx]; omega)]; exact hhi2 k h
    · subst h; rw [← hhi_idx, List.getElem?_set_self hhi_rr, Option.getD_some]; exact hcr_ref⟩

private theorem fwd_collect_scatter_refs {sp : FullState} {rr4 : List (BitVec 32)}
    {scr4 : List (BitVec 32)} {i : BitVec 64} {hi_rr : i.toNat < rr4.length}
    {hcr2_ar : ((rr4[i.toNat]'hi_rr).setWidth 64 + 2#64).toNat < sp.core.arena.length}
    {hsz_sc : ((sp.core.arena[((rr4[i.toNat]'hi_rr).setWidth 64 + 2#64).toNat]'hcr2_ar).setWidth
      64).toNat < scr4.length}
    {ncand : Nat} {half_cap : Nat}
    (hcr_ref : (rr4[i.toNat]'hi_rr).toNat ∈ fullArenaClauseRefs sp)
    (hpos_lt : (scr4[((sp.core.arena[((rr4[i.toNat]'hi_rr).setWidth 64 + 2#64).toNat]'
      hcr2_ar).setWidth 64).toNat]'hsz_sc).toNat < ncand)
    (hhalf_eq : (BitVec.ofNat 64 half_cap >>> (1 : Nat)).toNat = half_cap / 2)
    (hrc : half_cap < 2 * 2 ^ 28) (hrr4 : rr4.length = half_cap)
    (hlo4 : ∀ k < ncand, rr4[k]? = sp.scratch.red_refs[k]?)
    (hhi4 : ∀ k < ncand, (rr4[half_cap / 2 + k]?.getD 0#32).toNat ∈ fullArenaClauseRefs sp)
    (hnc_le : ncand ≤ half_cap / 2) :
    let pos32 := scr4[((sp.core.arena[((rr4[i.toNat]'hi_rr).setWidth 64 + 2#64).toNat]'
      hcr2_ar).setWidth 64).toNat]'hsz_sc
    ∀ (p1 : i.toNat < rr4.length)
      (p2 : ((rr4[i.toNat]'p1).setWidth 64 + (2 : BitVec 64)).toNat < sp.core.arena.length)
      (p3 : ((sp.core.arena[((rr4[i.toNat]'p1).setWidth 64 + (2 : BitVec 64)).toNat]'p2).setWidth
        64).toNat < scr4.length),
    let idx := (BitVec.ofNat 64 half_cap >>> (1 : Nat) +
      (scr4[((sp.core.arena[((rr4[i.toNat]'p1).setWidth 64 + (2 : BitVec 64)).toNat]'p2).setWidth
        64).toNat]'p3).setWidth 64).toNat
    let rr' := rr4.set idx (rr4[i.toNat]'p1)
    idx = half_cap / 2 + pos32.toNat ∧
    (∀ k < ncand, rr'[k]? = sp.scratch.red_refs[k]?) ∧
    (∀ k < ncand, (rr'[half_cap / 2 + k]?.getD 0#32).toNat ∈ fullArenaClauseRefs sp) := by
  intro pos32 p1 p2 p3 idx rr'
  have hpos_idx : idx = half_cap / 2 + pos32.toNat := by
    dsimp only [idx, pos32]
    rw [BitVec.toNat_add, hhalf_eq, fwd_zext32_toNat, Nat.mod_eq_of_lt (by omega)]
    rfl
  refine ⟨hpos_idx, fun k hk => by
    dsimp only [rr']; rw [hpos_idx, List.getElem?_set_ne (by omega)]; exact hlo4 k hk,
    fun k hk => by
    dsimp only [rr']; rw [hpos_idx]
    by_cases hke : half_cap / 2 + k = half_cap / 2 + pos32.toNat
    · rw [hke, List.getElem?_set_self (by omega), Option.getD_some]; exact hcr_ref
    · rw [List.getElem?_set_ne (by omega)]; exact hhi4 k hk⟩

private theorem fwd_collect_copy_refs {half_cap : Nat} {sp : FullState}
    {rr5 : List (BitVec 32)} {i : BitVec 64}
    (hi_rr : i.toNat < rr5.length)
    (hhi_rr : (BitVec.ofNat 64 half_cap >>> (1 : Nat) + i).toNat < rr5.length)
    {ncand : Nat} (hi_lt : i.toNat < ncand) (hi1 : (i + 1#64).toNat = i.toNat + 1)
    (hlo5 : ∀ k < i.toNat, (rr5[k]?.getD 0#32).toNat ∈ fullArenaClauseRefs sp)
    (hhi5 : ∀ k < ncand, (rr5[half_cap / 2 + k]?.getD 0#32).toNat ∈ fullArenaClauseRefs sp)
    (hhi_idx : (BitVec.ofNat 64 half_cap >>> (1 : Nat) + i).toNat = half_cap / 2 + i.toNat)
    (hnc_le : ncand ≤ half_cap / 2) :
    let rr' := rr5.set i.toNat (rr5[(BitVec.ofNat 64 half_cap >>> (1 : Nat) + i).toNat]'hhi_rr)
    (∀ k < (i + 1#64).toNat, (rr'[k]?.getD 0#32).toNat ∈ fullArenaClauseRefs sp) ∧
    (∀ k < ncand, (rr'[half_cap / 2 + k]?.getD 0#32).toNat ∈ fullArenaClauseRefs sp) := by
  intro rr'
  have hval_ref : (rr5[(BitVec.ofNat 64 half_cap >>> (1 : Nat) + i).toNat]'hhi_rr).toNat ∈
      fullArenaClauseRefs sp := by
    have h0 := hhi5 i.toNat hi_lt
    rwa [← hhi_idx, List.getElem?_eq_getElem hhi_rr, Option.getD_some] at h0
  refine ⟨fun k hk => by
    dsimp only [rr']
    rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp (hi1 ▸ hk)) with h | h
    · rw [List.getElem?_set_ne (by omega)]; exact hlo5 k h
    · subst h; rw [List.getElem?_set_self hi_rr, Option.getD_some]; exact hval_ref,
    fun k hk => by dsimp only [rr']; rw [List.getElem?_set_ne (by omega)]; exact hhi5 k hk⟩

private abbrev CollectHdrInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s0 sp : FullState) (p : BitVec 64) (sz_p : BitVec 32) (R : Mem 64 → Prop)
    (x : BitVec 32 × FullState) (mc : Mem 64) : Prop :=
  FullDenseInvW c F0 F_cur x.2 ∧ x.2.core.cur_vars = s0.core.cur_vars ∧
  x.2.core.arena_len = s0.core.arena_len ∧ x.2.core.fuel = s0.core.fuel ∧
  x.2.core.oom = s0.core.oom ∧ x.2.core.inconsistent = s0.core.inconsistent ∧
  x.2.scratch.tarjan_mark = s0.scratch.tarjan_mark ∧
  x.2.scratch.red_refs = sp.scratch.red_refs ∧
  fullArenaClauseRefs x.2 = fullArenaClauseRefs sp ∧
  fullArenaClauseSize x.2 p.toNat = sz_p.toNat ∧
  fullArenaClauseGarb x.2 p.toNat = false ∧
  x.1 = fullArenaHdr x.2 p.toNat ∧ (FullMem c x.2 ⋆ R) mc

private abbrev CollectScatterInv (c : FullCfg) (sp : FullState) (R : Mem 64 → Prop)
    (ncand : BitVec 64) (scr4 rr4 : List (BitVec 32)) (m4 : Mem 64) : Prop :=
  scr4.length = c.scratch_cap ∧ rr4.length = c.red_cap ∧
  (∀ k < ncand.toNat, rr4[k]? = sp.scratch.red_refs[k]?) ∧
  (∀ k < ncand.toNat, (rr4[c.red_cap / 2 + k]?.getD 0#32).toNat ∈ fullArenaClauseRefs sp) ∧
  (FullMem c { sp with scratch := { sp.scratch with scratch_buf := scr4, red_refs := rr4 } } ⋆
    R) m4

private theorem fwd_collect_mark_garb_cand {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 sp sc : FullState} {p ncand : BitVec 64} {hdr_c sz_p : BitVec 32} {R : Mem 64 → Prop}
    {m' : Mem 64} (hdwc : FullDenseInvW c F0 F_cur sc)
    (hp_ref_c : p.toNat ∈ fullArenaClauseRefs sc) (hp_arc : p.toNat < sc.core.arena.length)
    (hhc : hdr_c = fullArenaHdr sc p.toNat) (hcvc : sc.core.cur_vars = s0.core.cur_vars)
    (halc : sc.core.arena_len = s0.core.arena_len) (hflc : sc.core.fuel = s0.core.fuel)
    (hoomc : sc.core.oom = s0.core.oom) (hincc : sc.core.inconsistent = s0.core.inconsistent)
    (htmkc : sc.scratch.tarjan_mark = s0.scratch.tarjan_mark)
    (hrrc : sc.scratch.red_refs = sp.scratch.red_refs)
    (hrefsc : fullArenaClauseRefs sc = fullArenaClauseRefs sp)
    (hnc_le : ncand.toNat ≤ c.red_cap / 2)
    (hrr_ok : ∀ i < ncand.toNat,
      (sp.scratch.red_refs[i]?.getD 0#32).toNat ∈ fullArenaClauseRefs sp)
    (hm : (FullMem c { sc with core := { sc.core with
        arena := sc.core.arena.set p.toNat (hdr_c ||| 0x00080000#32),
        arena_garbage := sc.core.arena_garbage + 3#64 + sz_p.setWidth 64 } } ⋆ R) m') :
    CollectCandInv c F0 F_cur s0 sp R (ncand, { sc with core := { sc.core with
      arena := sc.core.arena.set p.toNat (hdr_c ||| 0x00080000#32),
      arena_garbage := sc.core.arena_garbage + 3#64 + sz_p.setWidth 64 } }) m' := by
  let ag' := sc.core.arena_garbage + 3#64 + sz_p.setWidth 64
  let ar' := sc.core.arena.set p.toNat (hdr_c ||| 0x00080000#32)
  have hmg := fwd_denseInvW_markGarb hdwc hp_ref_c (arena' := ar') (ag' := ag')
    (by simp [ar', hdwc.1.core_ok.arena_len_arr])
    (Or.inl (by dsimp only [ar']; rw [hhc]; exact List.getElem?_set_self hp_arc))
    (fun i hne _ => by dsimp only [ar']; exact List.getElem?_set_ne hne.symm)
  exact ⟨hmg.1, hcvc, halc, hflc, hoomc, hincc, htmkc, hmg.2.trans hrefsc, hnc_le,
    fun i hi => by dsimp; rw [hrrc, hmg.2, hrefsc]; exact hrr_ok i hi, hm⟩

private theorem fwd_collect_keep_cand {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 sp sc : FullState} {ncand : BitVec 64} {R : Mem 64 → Prop} {mc : Mem 64}
    (hdwc : FullDenseInvW c F0 F_cur sc) (hcvc : sc.core.cur_vars = s0.core.cur_vars)
    (halc : sc.core.arena_len = s0.core.arena_len) (hflc : sc.core.fuel = s0.core.fuel)
    (hoomc : sc.core.oom = s0.core.oom) (hincc : sc.core.inconsistent = s0.core.inconsistent)
    (htmkc : sc.scratch.tarjan_mark = s0.scratch.tarjan_mark)
    (hrrc : sc.scratch.red_refs = sp.scratch.red_refs)
    (hrefsc : fullArenaClauseRefs sc = fullArenaClauseRefs sp)
    (hnc_le : ncand.toNat ≤ c.red_cap / 2)
    (hrr_ok : ∀ i < ncand.toNat,
      (sp.scratch.red_refs[i]?.getD 0#32).toNat ∈ fullArenaClauseRefs sp)
    (hmc : (FullMem c sc ⋆ R) mc) :
    CollectCandInv c F0 F_cur s0 sp R (ncand, sc) mc :=
  ⟨hdwc, hcvc, halc, hflc, hoomc, hincc, htmkc, hrefsc, hnc_le,
    fun i hi => by rw [hrrc, hrefsc]; exact hrr_ok i hi, hmc⟩

private theorem fwd_collect_clear_bit24_hdr {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 sp : FullState} {p : BitVec 64} {hdr_p sz_p : BitVec 32} {R : Mem 64 → Prop}
    {m' : Mem 64} (hdwp : FullDenseInvW c F0 F_cur sp) (hp_ref : p.toNat ∈ fullArenaClauseRefs sp)
    (hp_ar : p.toNat < sp.core.arena.length) (hhdr_eq : hdr_p = fullArenaHdr sp p.toNat)
    (hsz_eq : sz_p.toNat = fullArenaClauseSizeCore sp.core p.toNat)
    (hng : fullArenaClauseGarb sp p.toNat = false)
    (hcvp : sp.core.cur_vars = s0.core.cur_vars) (halp : sp.core.arena_len = s0.core.arena_len)
    (hflp : sp.core.fuel = s0.core.fuel) (hoomp : sp.core.oom = s0.core.oom)
    (hincp : sp.core.inconsistent = s0.core.inconsistent)
    (htmkp : sp.scratch.tarjan_mark = s0.scratch.tarjan_mark)
    (hm : (FullMem c { sp with core := { sp.core with
      arena := sp.core.arena.set p.toNat (hdr_p &&& ~~~0x01000000#32) } } ⋆ R) m') :
    CollectHdrInv c F0 F_cur s0 sp p sz_p R
      (hdr_p &&& ~~~0x01000000#32,
        { sp with core := { sp.core with
          arena := sp.core.arena.set p.toNat (hdr_p &&& ~~~0x01000000#32) } }) m' := by
  let v' := hdr_p &&& ~~~0x01000000#32
  have hcb := fwd_bit24_clear_pres hdr_p
  have hset := fwd_denseInvW_set_hdr_bit24 hdwp hp_ref (v' := v')
    (by rw [← hhdr_eq]; exact hcb.1) (by rw [← hhdr_eq]; exact hcb.2)
  have hper := hset.2.2 p.toNat hp_ref
  have hhc : v' = fullArenaHdr { sp with core := { sp.core with
      arena := sp.core.arena.set p.toNat v' } } p.toNat := by
    unfold fullArenaHdr fullArenaHdrCore; dsimp only
    rw [List.getElem?_set_self hp_ar, Option.getD_some]
  exact ⟨hset.1, hcvp, halp, hflp, hoomp, hincp, htmkp, rfl, hset.2.1,
    hper.1.trans hsz_eq.symm, hper.2.1.trans hng, hhc, hm⟩

/-! ## 2. `full_fwd_collect_sort_m7_wp` -/

/-- Parametric `Func.wp` proof for `full_fwd_collect_sort_m7`. -/
theorem full_fwd_collect_sort_m7_wp (Γ : Env)
    (hArenaNext : Γ.Has "full_arena_next" fullArenaNextSpec) :
    ∀ a m Q X, fullFwdCollectSortM7Spec a m Q X →
      Func.wp Γ full_fwd_collect_sort_m7_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m0 Q X hspec
  obtain ⟨c, F0, F_cur, s0, R, rfl, hdw0, hm0, hQ⟩ := fullFwdCollectSortM7Spec_elim hspec
  have hmx := c.hmaxv; have harc := c.harena; have hrc := c.hred; have hsc := c.hscr
  unfold dimacsBound at hmx harc hrc hsc
  have hhalf_eq : (BitVec.ofNat 64 c.red_cap >>> (1 : Nat)).toNat = c.red_cap / 2 := by
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.shiftRight_eq_div_pow]
  unfold Func.wp full_fwd_collect_sort_m7_body
  c0_hsteps_nogrp
  -- Phase 1: scan arena, clear `PH_SUBSUME`, mark root-SAT `PH_GARB`, collect candidates
  refine wp_loop_group (ts := [i64, i64])
    (fun rem (ncand, p, ()) mp => ∃ sp : FullState,
      p.toNat ≤ sp.core.arena_len ∧ rem = sp.core.arena_len - p.toNat ∧
      (p.toNat = sp.core.arena_len ∨ p.toNat ∈ fullArenaClauseRefs sp) ∧
      FullDenseInvW c F0 F_cur sp ∧ sp.core.cur_vars = s0.core.cur_vars ∧
      sp.core.arena_len = s0.core.arena_len ∧ sp.core.fuel = s0.core.fuel ∧
      sp.core.oom = s0.core.oom ∧ sp.core.inconsistent = s0.core.inconsistent ∧
      sp.scratch.tarjan_mark = s0.scratch.tarjan_mark ∧ ncand.toNat ≤ c.red_cap / 2 ∧
      (∀ i < ncand.toNat, (sp.scratch.red_refs[i]?.getD 0#32).toNat ∈ fullArenaClauseRefs sp) ∧
      (FullMem c sp ⋆ R) mp) ?_ ?_
  · rintro L rem ⟨ncand, p, ⟨⟩⟩ mp hL
      ⟨sp, hp_le, rfl, hp_mem, hdwp, hcvp, halp, hflp, hoomp, hincp, htmkp, hnc_le, hrr_ok, hmp⟩
    have hal_le := hdwp.1.core_ok.arena_len_le
    c0_hsplit
    · have hp_lt : p.toNat < sp.core.arena_len := by
        rw [Nat.mod_eq_of_lt (by omega)] at hc; exact hc
      have hp_ref : p.toNat ∈ fullArenaClauseRefs sp := hp_mem.resolve_left (by omega)
      have hwf_p := hdwp.2.1.arena.refs_wf p.toNat hp_ref
      have hp_ar : p.toNat < sp.core.arena.length := by rw [hdwp.1.core_ok.arena_len_arr]; omega
      have hp2_ar : (p + 2#64).toNat < sp.core.arena.length := by
        rw [hdwp.1.core_ok.arena_len_arr]; c0_bound
      have hp32 : (p.setWidth 32).toNat = p.toNat := by
        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
      let hdr_p := sp.core.arena[p.toNat]'hp_ar
      let sz_p := sp.core.arena[(p + 2#64).toNat]'hp2_ar
      have hsz_eq : sz_p.toNat = fullArenaClauseSizeCore sp.core p.toNat := by
        unfold sz_p fullArenaClauseSizeCore
        rw [List.getElem?_eq_getElem (by rw [hdwp.1.core_ok.arena_len_arr]; omega),
          Option.getD_some]
        exact congrArg BitVec.toNat (fwd_getElem_congr (by c0_bound) _ _)
      c0_hsteps_nogrp; fwd_call hArenaNext
      refine ⟨c, sp, R, rfl, hdwp.1, hmp, ?_⟩
      have hnb := fullArenaNextOff_bounds (ar := sp.core.arena) (alen := sp.core.arena_len)
        (cref := p.toNat) hwf_p.1
      have hnp_mem := fwd_arenaClauseRefs_next_mem hdwp.2.1.arena hp_ref
      let np := (BitVec.ofNat 32 (fullArenaNextOff sp.core.arena sp.core.arena_len
        (p.setWidth 32).toNat)).setWidth 64
      have hnp_toNat : np.toNat = fullArenaNextOff sp.core.arena sp.core.arena_len p.toNat := by
        dsimp only [np]; rw [hp32, fwd_zext32_toNat, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega)]
      c0_hsteps_nogrp
      refine wp_join_state (ts := [i64, i32]) (α := BitVec 64 × BitVec 32 × FullState)
        (fun x => (x.1, x.2.1, ()))
        (fun x mj => CollectCandInv c F0 F_cur s0 sp R (x.1, x.2.2) mj)
        (fun _ ⟨ncj, _hdj, sj⟩ mj ⟨hdwj, hcvj, halj, hflj, hoomj, hincj, htmkj, hrefsj, hncj,
            hrrj, hmj⟩ => by
          c0_hsteps!
          exact hL (sj.core.arena_len - np.toNat) (ncj, np, ()) mj
            (by rw [hnp_toNat, halj, ← halp]; omega)
            ⟨sj, by rw [hnp_toNat, halj, ← halp]; omega, rfl,
             by rw [hnp_toNat, halj, ← halp, hrefsj]; exact hnp_mem,
             hdwj, hcvj, halj, hflj, hoomj, hincj, htmkj, hncj, hrrj, hmj⟩)
        (fun Jp hJp => by
          c0_hsplit
          · have hng : fullArenaClauseGarb sp p.toNat = false := by
              unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
              rw [List.getElem?_eq_getElem hp_ar, Option.getD_some,
                fwd_and_garb_zero_of_mask hc]; rfl
            c0_hsplit
            · have hsz3 : 3 ≤ sz_p.toNat := hc
              c0_hsteps_nogrp
              refine wp_join_state (ts := [i32]) (α := BitVec 32 × FullState) (fun x => (x.1, ()))
                (CollectHdrInv c F0 F_cur s0 sp p sz_p R)
                (fun _ ⟨hdr_c, sc⟩ mc ⟨hdwc, hcvc, halc, hflc, hoomc, hincc, htmkc, hrrc, hrefsc,
                    hszc, hngc, hhc, hmc⟩ => by
                  dsimp only at hrrc hszc hngc hhc
                  have hp_ref_c : p.toNat ∈ fullArenaClauseRefs sc := hrefsc.symm ▸ hp_ref
                  have hwf_c := hdwc.2.1.arena.refs_wf p.toNat hp_ref_c
                  have hp_arc : p.toNat < sc.core.arena.length := by
                    rw [hdwc.1.core_ok.arena_len_arr]; omega
                  c0_hsteps_nogrp
                  refine wp_loop_break_group (brkTs := [.bool, i32, i32]) (lpTs := [i32, i32])
                    (fun _ ms => ms = mc)
                    (fun rem_k (_, k, ()) mk => k.toNat ≤ sz_p.toNat ∧
                      rem_k = sz_p.toNat - k.toNat ∧ mk = mc)
                    ?_ ?_ ?_
                  · rintro _ ⟨sat_b, _, _, ⟨⟩⟩ ms hms; subst ms
                    c0_hsteps_nogrp
                    refine wp_join_state (ts := [i64]) (α := BitVec 64 × FullState)
                      (fun x => (x.1, ()))
                      (fun x mj => CollectCandInv c F0 F_cur s0 sp R x mj)
                      (fun _ ⟨nc', sr⟩ mr h => by c0_hsteps!; exact hJp (nc', hdr_c, sr) mr h)
                      (fun J40 hJ40 => by
                        c0_hsplit
                        · c0_hsteps!
                          exact hJ40 (ncand, _) _ (fwd_collect_mark_garb_cand hdwc hp_ref_c hp_arc
                            hhc hcvc halc hflc hoomc hincc htmkc hrrc hrefsc hnc_le hrr_ok hm)
                        · c0_hsteps_nogrp
                          refine wp_join_state (ts := [i64]) (α := BitVec 64 × FullState)
                            (fun x => (x.1, ()))
                            (fun x mj => CollectCandInv c F0 F_cur s0 sp R x mj)
                            (fun _ ⟨nc', sr⟩ mr h => by c0_hsteps!; exact hJ40 (nc', sr) mr h)
                            (fun J41 hJ41 => by
                              have hkeep := fwd_collect_keep_cand hdwc hcvc halc hflc hoomc hincc
                                htmkc hrrc hrefsc hnc_le hrr_ok hmc
                              c0_hsplit
                              · c0_hsplit
                                · c0_hsplit
                                  · have hnc_lt : ncand.toNat < c.red_cap / 2 := by
                                      rw [← hhalf_eq]; exact hc
                                    have hnc_rr : ncand.toNat < sc.scratch.red_refs.length := by
                                      rw [hdwc.1.scratch_ok.red_refs_len]; omega
                                    have hnc1 : (ncand + 1#64).toNat = ncand.toNat + 1 := by
                                      c0_bound
                                    c0_hsteps!
                                    exact hJ41 (ncand + 1#64, _) _ (fwd_collect_push_rr hdwc
                                      hp_ref_c hcvc halc hflc hoomc hincc htmkc hrrc hrefsc
                                      hrr_ok hnc_lt hnc_rr hnc1 hp32 hm)
                                  · c0_hsteps!; exact hJ41 (ncand, sc) mc hkeep
                                · c0_hsteps!; exact hJ41 (ncand, sc) mc hkeep
                              · c0_hsteps!; exact hJ41 (ncand, sc) mc hkeep))
                  · rintro Bk Lk rem_k ⟨scnt_k, k, ⟨⟩⟩ mk hBk hLk ⟨hk_le, rfl, hmk_eq⟩
                    subst hmk_eq; c0_hsplit
                    · have hk_lt : k.toNat < sz_p.toNat := hc
                      obtain ⟨hcl_lt, hcl_v⟩ :=
                        fwd_collect_k_lit_bounds harc hmx hdwc hp_ref_c hngc hszc hk_lt
                      have hpi_ar : (p + 3#64 + k.setWidth 64).toNat < sc.core.arena.length := by
                        rw [hdwc.1.core_ok.arena_len_arr]; have := hdwc.1.core_ok.arena_len_le
                        c0_bound
                      have hk1 : (k + 1#32).toNat = k.toNat + 1 := by c0_bound
                      c0_hsplit
                      · c0_hsteps!; exact hBk (true, scnt_k, k, ()) mk rfl
                      · c0_hsteps_nogrp
                        refine wp_join_state_pure (ts := [i32]) (α := BitVec 32) (fun x => (x, ()))
                          (fun _ => True)
                          (fun _ sc' _ => by
                            c0_hsteps!
                            exact hLk (sz_p.toNat - (k + 1#32).toNat) (sc', k + 1#32, ()) mk
                              (by omega) ⟨by omega, rfl, rfl⟩)
                          (fun Js hJs => by
                            c0_hsplit
                            · have hfl_i :
                                  (((sc.core.arena[(p + 3#64 + k.setWidth 64).toNat]'hpi_ar) >>>
                                    (1 : Nat)).setWidth 64).toNat < sc.core.flags.length := by
                                rw [hdwc.1.core_ok.flags_len]; have := hdwc.1.core_ok.cur_vars_le
                                c0_bound
                              c0_hsplit
                              · c0_hsteps!; exact hJs (scnt_k + 1#32) trivial
                              · c0_hsteps!; exact hJs scnt_k trivial
                            · c0_hsteps!; exact hJs scnt_k trivial)
                    · c0_hsteps!; exact hBk (false, scnt_k, k, ()) mk rfl
                  · intro _ Lk _ hLk; c0_hsteps!
                    exact hLk sz_p.toNat (0#32, 0#32, ()) mc ⟨Nat.zero_le _, by simp, rfl⟩)
                (fun Jc hJc => by
                  have hhdr_eq : hdr_p = fullArenaHdr sp p.toNat := by
                    unfold hdr_p fullArenaHdr fullArenaHdrCore
                    rw [List.getElem?_eq_getElem hp_ar, Option.getD_some]
                  c0_hsplit
                  · c0_hsteps!
                    exact hJc (_, _) _ (fwd_collect_clear_bit24_hdr hdwp hp_ref hp_ar hhdr_eq hsz_eq
                      hng hcvp halp hflp hoomp hincp htmkp hm)
                  · c0_hsteps!
                    exact hJc (hdr_p, sp) mp ⟨hdwp, hcvp, halp, hflp, hoomp, hincp, htmkp, rfl,
                      rfl, hsz_eq.symm, hng, hhdr_eq, hmp⟩)
            · c0_hsteps!
              exact hJp (ncand, hdr_p, sp) mp ⟨hdwp, hcvp, halp, hflp, hoomp, hincp, htmkp, rfl,
                hnc_le, hrr_ok, hmp⟩
          · c0_hsteps!
            exact hJp (ncand, hdr_p, sp) mp ⟨hdwp, hcvp, halp, hflp, hoomp, hincp, htmkp, rfl,
              hnc_le, hrr_ok, hmp⟩)
    · -- Phase 2: ascending-length bucket sort if `ncand > 1 && scratch_cap >= 1008`
      c0_hsteps_nogrp
      refine wp_join_state (ts := []) (α := FullState) (fun _ => ())
        (fun sf mf => FullDenseInvW c F0 F_cur sf ∧ sf.core.cur_vars = s0.core.cur_vars ∧
          sf.core.arena_len = s0.core.arena_len ∧ sf.core.fuel = s0.core.fuel ∧
          sf.core.oom = s0.core.oom ∧ sf.core.inconsistent = s0.core.inconsistent ∧
          sf.scratch.tarjan_mark = s0.scratch.tarjan_mark ∧
          (∀ k < ncand.toNat, (sf.scratch.red_refs[k]?.getD 0#32).toNat ∈ fullArenaClauseRefs sf) ∧
          (FullMem c sf ⋆ R) mf)
        (fun _ sf mf ⟨hdwf, hcvf, half, hflf, hoomf, hincf, htmkf, hrrf, hmf⟩ => by
          c0_hsteps!; exact hQ ncand sf mf hdwf hcvf half hflf hoomf hincf htmkf hnc_le hrrf hmf)
        (fun Jf hJf => by
          c0_hsplit
          · c0_hsplit
            · have hsc_ge : 1008 ≤ c.scratch_cap := by
                rw [Nat.mod_eq_of_lt (by omega)] at hc; exact hc
              c0_hsteps_nogrp
              refine wp_loop_group (ts := [i64])
                (fun rem1 (b, ()) m1 => ∃ scr1 : List (BitVec 32),
                  scr1.length = c.scratch_cap ∧ b.toNat ≤ 1001 ∧ rem1 = 1001 - b.toNat ∧
                  (FullMem c { sp with scratch := { sp.scratch with scratch_buf := scr1 } } ⋆ R) m1)
                ?_ ?_
              · rintro L1 rem1 ⟨b, ⟨⟩⟩ m1 hL1 ⟨scr1, hsc1, hb_le, rfl, hm1⟩
                c0_hsplit
                · have hb_lt : b.toNat ≤ 1000 := hc
                  have hb_sc : b.toNat < scr1.length := by omega
                  have hb1 : (b + 1#64).toNat = b.toNat + 1 := by c0_bound
                  c0_hsteps!
                  exact hL1 (1001 - (b + 1#64).toNat) (b + 1#64, ()) _ (by omega)
                    ⟨scr1.set b.toNat 0#32, by simp [hsc1], by omega, rfl, hm⟩
                · c0_hsteps_nogrp
                  refine wp_loop_group (ts := [i64])
                    (fun rem2 (i, ()) m2 => ∃ scr2 rr2 : List (BitVec 32),
                      scr2.length = c.scratch_cap ∧ rr2.length = c.red_cap ∧
                      i.toNat ≤ ncand.toNat ∧ rem2 = ncand.toNat - i.toNat ∧
                      (∀ k < ncand.toNat, rr2[k]? = sp.scratch.red_refs[k]?) ∧
                      (∀ k < i.toNat,
                        (rr2[c.red_cap / 2 + k]?.getD 0#32).toNat ∈ fullArenaClauseRefs sp) ∧
                      (FullMem c { sp with scratch :=
                        { sp.scratch with scratch_buf := scr2, red_refs := rr2 } } ⋆ R) m2)
                    ?_ ?_
                  · rintro L2 rem2 ⟨i, ⟨⟩⟩ m2 hL2
                      ⟨scr2, rr2, hsc2, hrr2, hi_le, rfl, hlo2, hhi2, hm2⟩
                    c0_hsplit
                    · have hi_lt : i.toNat < ncand.toNat := hc
                      have hi_rr : i.toNat < rr2.length := by omega
                      have hhi_idx : (BitVec.ofNat 64 c.red_cap >>> (1 : Nat) + i).toNat =
                          c.red_cap / 2 + i.toNat := by
                        rw [BitVec.toNat_add, hhalf_eq, Nat.mod_eq_of_lt (by omega)]
                      have hhi_rr : (BitVec.ofNat 64 c.red_cap >>> (1 : Nat) + i).toNat <
                          rr2.length := by omega
                      have hi1 : (i + 1#64).toNat = i.toNat + 1 := by c0_bound
                      obtain ⟨hcr_ref, hlo3, hhi3⟩ := fwd_collect_hist_refs hhi_idx hhi_rr hi_lt
                        hi_rr hi1 hrr_ok hlo2 hhi2 hnc_le
                      have hcr_wf := hdwp.2.1.arena.refs_wf _ hcr_ref
                      have hcr2_ar : ((rr2[i.toNat]'hi_rr).setWidth 64 + 2#64).toNat <
                          sp.core.arena.length := by rw [hdwp.1.core_ok.arena_len_arr]; c0_bound
                      c0_hsteps_nogrp
                      refine wp_join_state (ts := []) (α := List (BitVec 32)) (fun _ => ())
                        (fun scr2' m2' => scr2'.length = c.scratch_cap ∧
                          (FullMem c { sp with scratch :=
                            { sp.scratch with
                              scratch_buf := scr2',
                              red_refs := rr2.set
                                (BitVec.ofNat 64 c.red_cap >>> (1 : Nat) + i).toNat
                                (rr2[i.toNat]'hi_rr) } } ⋆ R) m2')
                        (fun _ scr2' m2' ⟨hsc2', hm2'⟩ => by
                          c0_hsteps!
                          exact hL2 (ncand.toNat - (i + 1#64).toNat) (i + 1#64, ()) m2' (by omega)
                            ⟨scr2', _, hsc2', by simp [hrr2], by omega, rfl, hlo3, hhi3, hm2'⟩)
                        (fun J2 hJ2 => by
                          c0_hsplit
                          · have hsz_val : sp.core.arena[((rr2[i.toNat]'hi_rr).setWidth 64 +
                                2#64).toNat]'hcr2_ar =
                                sp.core.arena[(rr2[i.toNat].toNat + 2) % 2 ^ 64]'(by
                                  rw [hdwp.1.core_ok.arena_len_arr]; simp; omega) :=
                              fwd_getElem_congr (by c0_bound) _ _
                            have hsz_le1000 : (sp.core.arena[(rr2[i.toNat].toNat + 2) % 2 ^ 64]'(by
                                rw [hdwp.1.core_ok.arena_len_arr]; simp; omega)).toNat ≤ 1000 := by
                              simpa using hc
                            have hsz_sc : ((sp.core.arena[((rr2[i.toNat]'hi_rr).setWidth 64 +
                                2#64).toNat]'hcr2_ar).setWidth 64).toNat < scr2.length := by
                              rw [hsz_val, fwd_zext32_toNat]; omega
                            c0_hsteps!; exact hJ2 _ _ ⟨by simp [hsc2], hm⟩
                          · c0_hsteps!; exact hJ2 scr2 _ ⟨hsc2, hm⟩)
                    · c0_hsteps_nogrp
                      refine wp_loop_group (ts := [i64, i32])
                        (fun rem3 (b, _, ()) m3 => ∃ scr3 : List (BitVec 32),
                          scr3.length = c.scratch_cap ∧ b.toNat ≤ 1001 ∧ rem3 = 1001 - b.toNat ∧
                          (FullMem c { sp with scratch :=
                            { sp.scratch with scratch_buf := scr3, red_refs := rr2 } } ⋆ R) m3)
                        ?_ ?_
                      · rintro L3 rem3 ⟨b, sum_b, ⟨⟩⟩ m3 hL3 ⟨scr3, hsc3, hb_le, rfl, hm3⟩
                        c0_hsplit
                        · have hb_lt : b.toNat ≤ 1000 := hc
                          have hb_sc : b.toNat < scr3.length := by omega
                          have hb1 : (b + 1#64).toNat = b.toNat + 1 := by c0_bound
                          c0_hsteps!
                          exact hL3 (1001 - (b + 1#64).toNat) (b + 1#64, _, ()) _ (by omega)
                            ⟨scr3.set b.toNat sum_b, by simp [hsc3], by omega, rfl, hm⟩
                        · c0_hsteps_nogrp
                          refine wp_loop_group (ts := [i64])
                            (fun rem4 (i, ()) m4 => ∃ scr4 rr4 : List (BitVec 32),
                              i.toNat ≤ ncand.toNat ∧ rem4 = ncand.toNat - i.toNat ∧
                              CollectScatterInv c sp R ncand scr4 rr4 m4)
                            ?_ ?_
                          · rintro L4 rem4 ⟨i, ⟨⟩⟩ m4 hL4
                              ⟨scr4, rr4, hi_le, rfl, hsc4, hrr4, hlo4, hhi4, hm4⟩
                            c0_hsplit
                            · have hi_lt : i.toNat < ncand.toNat := hc
                              have hi_rr : i.toNat < rr4.length := by omega
                              have hcr_ref : (rr4[i.toNat]'hi_rr).toNat ∈
                                  fullArenaClauseRefs sp := by
                                have h0 := hrr_ok i.toNat hi_lt
                                rwa [← hlo4 i.toNat hi_lt, List.getElem?_eq_getElem hi_rr,
                                  Option.getD_some] at h0
                              have hcr_wf := hdwp.2.1.arena.refs_wf _ hcr_ref
                              have hcr2_ar : ((rr4[i.toNat]'hi_rr).setWidth 64 + 2#64).toNat <
                                  sp.core.arena.length := by
                                rw [hdwp.1.core_ok.arena_len_arr]; c0_bound
                              have hi1 : (i + 1#64).toNat = i.toNat + 1 := by c0_bound
                              c0_hsteps_nogrp
                              refine wp_join_state (ts := [])
                                (α := List (BitVec 32) × List (BitVec 32)) (fun _ => ())
                                (fun p4 m4' => CollectScatterInv c sp R ncand p4.1 p4.2 m4')
                                (fun _ ⟨scr4', rr4'⟩ m4' ⟨hsc4', hrr4', hlo4', hhi4', hm4'⟩ => by
                                  c0_hsteps!
                                  exact hL4 (ncand.toNat - (i + 1#64).toNat) (i + 1#64, ()) m4'
                                    (by omega) ⟨scr4', rr4', by omega, rfl, hsc4', hrr4', hlo4',
                                      hhi4', hm4'⟩)
                                (fun J4 hJ4 => by
                                  c0_hsplit
                                  · have hsz_val : sp.core.arena[((rr4[i.toNat]'hi_rr).setWidth 64 +
                                        2#64).toNat]'hcr2_ar =
                                        sp.core.arena[(rr4[i.toNat].toNat + 2) % 2 ^ 64]'(by
                                          rw [hdwp.1.core_ok.arena_len_arr]; simp; omega) :=
                                      fwd_getElem_congr (by c0_bound) _ _
                                    have hsz_le1000 :
                                        (sp.core.arena[(rr4[i.toNat].toNat + 2) % 2 ^ 64]'(by
                                          rw [hdwp.1.core_ok.arena_len_arr]; simp; omega)).toNat ≤
                                          1000 := by simpa using hc
                                    have hsz_sc : ((sp.core.arena[((rr4[i.toNat]'hi_rr).setWidth
                                        64 + 2#64).toNat]'hcr2_ar).setWidth 64).toNat <
                                        scr4.length := by
                                      rw [hsz_val, fwd_zext32_toNat]; omega
                                    c0_hsteps_nogrp
                                    refine wp_join0 (P := fun mj =>
                                        ∃ scr4' rr4' : List (BitVec 32),
                                          CollectScatterInv c sp R ncand scr4' rr4' mj)
                                      (fun _ mj ⟨scr4', rr4', h1, h2, h3, h4, hm'⟩ => by
                                        c0_hsteps!
                                        exact hJ4 (scr4', rr4') mj ⟨h1, h2, h3, h4, hm'⟩)
                                      (fun J54 hJ54 => by
                                        c0_hsplit
                                        · have hpos_lt : (scr4[((sp.core.arena[((rr4[i.toNat]'
                                              hi_rr).setWidth 64 + 2#64).toNat]'hcr2_ar).setWidth
                                              64).toNat]'hsz_sc).toNat < ncand.toNat := by
                                            simpa only [hsz_val, fwd_zext32_toNat,
                                              show (2 : BitVec 64).toNat = 2 from rfl] using hc
                                          have hsc_step := fwd_collect_scatter_refs hcr_ref hpos_lt
                                            hhalf_eq hrc hrr4 hlo4 hhi4 hnc_le
                                          have hpos_rr : (BitVec.ofNat 64 c.red_cap >>> (1 : Nat) +
                                              (scr4[((sp.core.arena[((rr4[i.toNat]'hi_rr).setWidth
                                                64 + 2#64).toNat]'hcr2_ar).setWidth 64).toNat]'
                                                hsz_sc).setWidth 64).toNat < rr4.length := by
                                            rw [BitVec.toNat_add, hhalf_eq, fwd_zext32_toNat,
                                              Nat.mod_eq_of_lt (by omega)]; omega
                                          c0_hsteps!; dsimp only at hm
                                          exact hJ54 _ ⟨_, _, by simp [hsc4], by simp [hrr4],
                                            (hsc_step _ _ _).2.1, (hsc_step _ _ _).2.2, hm⟩
                                        · c0_hsteps!
                                          exact hJ54 m4 ⟨scr4, rr4, hsc4, hrr4, hlo4, hhi4, hm4⟩)
                                  · c0_hsteps!
                                    exact hJ4 (scr4, rr4) m4 ⟨hsc4, hrr4, hlo4, hhi4, hm4⟩)
                            · c0_hsteps_nogrp
                              refine wp_loop_group (ts := [i64])
                                (fun rem5 (i, ()) m5 => ∃ rr5 : List (BitVec 32),
                                  rr5.length = c.red_cap ∧ i.toNat ≤ ncand.toNat ∧
                                  rem5 = ncand.toNat - i.toNat ∧
                                  (∀ k < i.toNat,
                                    (rr5[k]?.getD 0#32).toNat ∈ fullArenaClauseRefs sp) ∧
                                  (∀ k < ncand.toNat,
                                    (rr5[c.red_cap / 2 + k]?.getD 0#32).toNat ∈
                                      fullArenaClauseRefs sp) ∧
                                  (FullMem c { sp with scratch := { sp.scratch with
                                    scratch_buf := scr4, red_refs := rr5 } } ⋆ R) m5)
                                ?_ ?_
                              · rintro L5 rem5 ⟨i, ⟨⟩⟩ m5 hL5
                                  ⟨rr5, hrr5, hi_le, rfl, hlo5, hhi5, hm5⟩
                                c0_hsplit
                                · have hi_lt : i.toNat < ncand.toNat := hc
                                  have hi_rr : i.toNat < rr5.length := by omega
                                  have hhi_idx : (BitVec.ofNat 64 c.red_cap >>> (1 : Nat) +
                                      i).toNat = c.red_cap / 2 + i.toNat := by
                                    rw [BitVec.toNat_add, hhalf_eq, Nat.mod_eq_of_lt (by omega)]
                                  have hhi_rr : (BitVec.ofNat 64 c.red_cap >>> (1 : Nat) +
                                      i).toNat < rr5.length := by omega
                                  have hi1 : (i + 1#64).toNat = i.toNat + 1 := by c0_bound
                                  obtain ⟨hlo5', hhi5'⟩ := fwd_collect_copy_refs hi_rr hhi_rr hi_lt
                                    hi1 hlo5 hhi5 hhi_idx hnc_le
                                  c0_hsteps!
                                  exact hL5 (ncand.toNat - (i + 1#64).toNat) (i + 1#64, ()) _
                                    (by omega) ⟨_, by simp [hrr5], by omega, rfl, hlo5', hhi5', hm⟩
                                · have hi_eq : i.toNat = ncand.toNat := by omega
                                  c0_hsteps!
                                  let sfin : FullState := { sp with scratch :=
                                    { sp.scratch with scratch_buf := scr4, red_refs := rr5 } }
                                  have hdwf : FullDenseInvW c F0 F_cur sfin :=
                                    fwd_denseInvW_with_scratch hdwp
                                      { hdwp.1.scratch_ok with
                                        scratch_buf_len := hsc4, red_refs_len := hrr5 } rfl rfl
                                  exact hJf sfin m5 ⟨hdwf, hcvp, halp, hflp, hoomp, hincp, htmkp,
                                    fun k hk => hlo5 k (by omega), hm5⟩
                              · intro L5 hL5; c0_hsteps!
                                exact hL5 ncand.toNat (0#64, ()) m4
                                  ⟨rr4, hrr4, Nat.zero_le _, by simp, fun _ h => by simp at h,
                                   hhi4, hm4⟩
                          · intro L4 hL4; c0_hsteps!
                            exact hL4 ncand.toNat (0#64, ()) m3
                              ⟨scr3, rr2, Nat.zero_le _, by simp, hsc3, hrr2, hlo2,
                               fun k hk => hhi2 k (by omega), hm3⟩
                      · intro L3 hL3; c0_hsteps!
                        exact hL3 1001 (0#64, 0#32, ()) m2
                          ⟨scr2, hsc2, Nat.zero_le _, by simp, hm2⟩
                  · intro L2 hL2; c0_hsteps!
                    exact hL2 ncand.toNat (0#64, ()) m1
                      ⟨scr1, sp.scratch.red_refs, hsc1, hdwp.1.scratch_ok.red_refs_len,
                       Nat.zero_le _, by simp, fun _ _ => rfl, fun _ h => by simp at h, hm1⟩
              · intro L1 hL1; c0_hsteps!
                exact hL1 1001 (0#64, ()) mp
                  ⟨sp.scratch.scratch_buf, hdwp.1.scratch_ok.scratch_buf_len, Nat.zero_le _,
                   by simp, hmp⟩
            · c0_hsteps!; exact hJf sp mp ⟨hdwp, hcvp, halp, hflp, hoomp, hincp, htmkp, hrr_ok, hmp⟩
          · c0_hsteps!; exact hJf sp mp ⟨hdwp, hcvp, halp, hflp, hoomp, hincp, htmkp, hrr_ok, hmp⟩)
  · intro L hL; c0_hsteps!
    exact hL s0.core.arena_len (0#64, 0#64, ()) m0
      ⟨s0, Nat.zero_le _, by simp, by
        by_cases hz : s0.core.arena_len = 0
        · exact Or.inl hz.symm
        · exact Or.inr (fwd_zero_mem_arenaRefs hdw0.2.1.arena (Nat.pos_of_ne_zero hz)),
       hdw0, rfl, rfl, rfl, rfl, rfl, rfl, Nat.zero_le _, fun _ h => by simp at h, hm0⟩

end LeanQbe.T.Examples.Kissat.Proof.Forward
