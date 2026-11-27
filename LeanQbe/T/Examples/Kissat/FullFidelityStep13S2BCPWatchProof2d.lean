/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S2BCPWatchProof2c
public meta import Lean.Elab.Tactic
public meta import LeanQbe.T.Logic.C0Step

/-!
# Kissat Fidelity Step 13 Shard S2-A Headline BCP Proofs (`FullFidelityStep13S2BCPWatchProof2d`)

Plain `public section` (`0` `@[expose]`, `0` `import all`, `<= 100` cols, every theorem `<= 350`L):
1. `s13_outer_sz0_step` & `s13_outer_init_inv`: shared outer-loop invariant init / 0-watch step
   (reused by both `full_propagate_ignore{_hot}_step13_wp` and
   `full_propagate_beyond_m7_step13_wp`).
2. `full_propagate_ignore_hot_step13_wp` & `full_propagate_ignore_step13_wp`: main WP proofs
   (`step13PropagateIgnoreM6Spec`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S2

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0HeadStep LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.FastCore
open LeanQbe.T.Examples.Kissat.FullM5Otfs
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6BcpS15
open LeanQbe.T.Examples.Kissat.FullM7BcpHot
open LeanQbe.T.Examples.Kissat.FullFidelityBcp
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullAnalyzeHelpers
open LeanQbe.T.Examples.Kissat.Full.FullPropDecSpecs hiding
  fullWatchPushSpec fullPropLitSpec fullPropagateIgnoreSpec fullPropagateSpec
  FullTrailExt FullArenaPermEq
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics

attribute [local irreducible] fastPropMem

local macro "s13_hsteps" : tactic =>
  `(tactic| ((try (first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)); c0_hsteps))

local macro "s13_hsteps_nogrp" : tactic =>
  `(tactic| ((try (first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)); c0_hsteps_nogrp))

local macro "s13_hsplit" : tactic =>
  `(tactic| ((try (first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)); c0_hsplit))

private theorem s13_perm_refl (k : FullCoreState) : FullArenaPermEq k k :=
  ⟨rfl, rfl, fun _ _ => ⟨rfl, rfl, List.Perm.refl _⟩⟩

private theorem s13_trail_refl (k : FullCoreState) : FullTrailExt k k :=
  ⟨Nat.le_refl _, fun _ _ => rfl, fun _ _ => rfl⟩

theorem s13_outer_sz0_step {isBeyond : Bool} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {ext0 ext1 : List (BitVec 64)} {s sem : FullState}
    {prop_v tend_v fuel_v unass_v unfl_v : BitVec 64}
    (hext1 : M6HdrExtOk ext1)
    (hw2b1 : M6HdrExtInitOk ext0 → M6HdrExtInitOk ext1 ∧ M6ExtW2bPres ext0 ext1)
    (hlen_o : sem.LengthsOk c) (hw_o : FullWitnessInv c F0 F_cur sem.core)
    (htr_o : FullTrailExt s.core sem.core) (hperm_o : FullArenaPermEq s.core sem.core)
    (hag_o : AgreesExcept fidCoreMask s.core sem.core)
    (_hprop_eq : sem.core.propagated = prop_v.toNat) (htend_eq : sem.core.trail_end = tend_v.toNat)
    (hfuel_eq : sem.core.fuel = fuel_v) (hunass_eq : sem.core.unassigned = unass_v)
    (hunfl_eq : sem.core.unflushed = unfl_v) (hoom_o : sem.core.oom = 0#64)
    (hct_o : isBeyond = false → sem.core.confl_type = s.core.confl_type)
    (hbcf_o : isBeyond = true → S13ConflEq s.core sem.core)
    (hdm_o : sem.core.dense_mode = 0#64) (hcv_o : sem.core.cur_vars = s.core.cur_vars)
    (hcl_o : sem.core.cur_level = s.core.cur_level) (hprob_o : sem.core.probing = s.core.probing)
    (halen_o : sem.core.arena_len = s.core.arena_len) (hsc_o : S13Scr s sem)
    (hd0_sem : c.delayed_cap = 0 → sem.scratch.delayed = s.scratch.delayed)
    (hfl_rem_dec : (sem.core.fuel - 1#64).toNat < sem.core.fuel.toNat)
    (hfuel_le : sem.core.fuel.toNat ≤ s.core.fuel.toNat)
    (hp1_prop : (prop_v + 1#64).toNat = prop_v.toNat + 1)
    (hp_lt_o : prop_v.toNat < tend_v.toNat) (hpr_ge : s.core.propagated ≤ prop_v.toNat)
    {te_mem : Nat} (htem_le : te_mem ≤ sem.core.trail_end) (hpr_tem : s.core.propagated ≤ te_mem)
    {R : Mem 64 → Prop} {ml : Mem 64} {ticks1 : BitVec 64}
    (hml : (FullM6HdrMem c ext1 (fastPropMem { s with core := { s.core with trail_end := te_mem } }
      { sem with core := { sem.core with propagated := s.core.propagated, fuel := s.core.fuel } }) ⋆
      R) ml) :
    S13OuterInv isBeyond c F0 F_cur ext0 s R (sem.core.fuel - 1#64).toNat
      (prop_v + 1#64) tend_v (fuel_v - 1#64) unass_v unfl_v ticks1 ml := by
  let sem_n : FullState :=
    { sem with core :=
      { sem.core with propagated := prop_v.toNat + 1, fuel := sem.core.fuel - 1#64 } }
  have hlen_n : sem_n.LengthsOk c :=
    ⟨{ hlen_o.core_ok with propagated_le := by rw [htend_eq]; exact hp_lt_o }, hlen_o.scratch_ok⟩
  have hw_n : FullWitnessInv c F0 F_cur sem_n.core := by
    have hnw := fullWitnessInv_nw_congr hlen_n.core_ok.cur_vars_le
      (fullWitnessInv_to_nw hlen_o.core_ok.cur_vars_le hw_o)
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    have hwat_n : WatchesInv F_cur sem_n.core := by
      have hw_sp : ModeWatchesInv F_cur sem_n.core :=
        hw_o.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr)
      simpa only [ModeWatchesInv, sem_n, hdm_o, ↓reduceIte] using hw_sp
    exact fullWitnessInv_of_nw hnw hdm_o hwat_n
  exact s13OuterInv_mk ⟨ext1, sem_n, te_mem, rfl, hext1, hw2b1, hlen_n, hw_n,
    ⟨htr_o.1, htr_o.2.1, htr_o.2.2⟩, hperm_o,
    hag_o.update (fun k => { k with propagated := prop_v.toNat + 1, fuel := sem.core.fuel - 1#64 }),
    by simp [sem_n, hp1_prop], htend_eq, by simp [sem_n, hfuel_eq], hunass_eq, hunfl_eq, hoom_o,
    fun hb => by simp [sem_n, hct_o hb], fun hb => by simp [sem_n]; exact hbcf_o hb,
    hdm_o, hcv_o, hcl_o, hprob_o, halen_o,
    Nat.le_trans (Nat.le_of_lt hfl_rem_dec) hfuel_le,
    fun _ => Nat.lt_of_lt_of_le hfl_rem_dec hfuel_le, by rw [hp1_prop]; omega,
    htem_le, hpr_tem, hsc_o, hd0_sem, hml⟩

theorem s13_outer_init_inv {isBeyond : Bool} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {ext0 : List (BitVec 64)} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} (hlen0 : s.LengthsOk c) (hext0 : M6HdrExtOk ext0)
    (hw0 : FullWitnessInv c F0 F_cur s.core) (hdense0 : s.core.dense_mode = 0#64)
    (hoom0 : s.core.oom = 0#64) (hpr0_lt64 : s.core.propagated < 2 ^ 64)
    (hte0_lt64 : s.core.trail_end < 2 ^ 64)
    (hm0 : (FullM6HdrMem c ext0 s ⋆ R) m) :
    S13OuterInv isBeyond c F0 F_cur ext0 s R s.core.fuel.toNat
      (BitVec.ofNat 64 s.core.propagated) (BitVec.ofNat 64 s.core.trail_end) s.core.fuel
      s.core.unassigned s.core.unflushed 0#64 m :=
  s13OuterInv_mk ⟨ext0, s, s.core.trail_end, rfl, hext0, fun h => ⟨h, .refl _⟩, hlen0, hw0,
    s13_trail_refl s.core, s13_perm_refl s.core,
    .refl _ _, (m7_bv64_ofNat_toNat_lt hpr0_lt64).symm, (m7_bv64_ofNat_toNat_lt hte0_lt64).symm,
    rfl, rfl, rfl, hoom0, fun _ => rfl, fun _ => ⟨rfl, rfl, rfl, rfl⟩, hdense0, rfl, rfl, rfl, rfl,
    Nat.le_refl _,
    fun hlt => absurd (m7_bv64_ofNat_toNat_lt hpr0_lt64 ▸ hlt) (Nat.lt_irrefl _),
    by rw [m7_bv64_ofNat_toNat_lt hpr0_lt64]; exact Nat.le_refl _,
    Nat.le_refl _, hlen0.core_ok.propagated_le, rfl, fun _ => rfl,
    by simpa only [fastPropMem_self] using hm0⟩

/-- Shared post-overflow join continuation (`cases ovf_p`) inside `wp_loop_break_group` for both
`full_propagate_ignore{_hot}` (`isBeyond = false`) and `full_propagate_beyond_m7`
(`isBeyond = true`). -/
theorem s13_ovf_post_join_case {Γ : Env} {isBeyond : Bool} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s s_disk s_base sem sem_o sem_p : FullState}
    {not_lit : BitVec 32} {ign_v nl64 off_o p_o end_o te_p un_p uf_p tk_p p_p q_p di_p
      brk_p : BitVec 64}
    {ovf_p : Bool} {ovf_rw_p ovf_oth_p ovf_cr_p : BitVec 32} {ovf_ri_p : BitVec 64}
    {dlen_p : Nat} {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost} {mbp : Mem 64}
    {Bo Lo : Cont [i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, Ty.bool]}
    (hOvf : ∀ args m Q X, FullM7BcpHot.fullPropLitOvfHotSpec args m Q X →
      Γ "full_prop_lit_ovf_hot" [i64, i32, i32, i32] [.bool] args m Q X)
    (hFlush : ∀ args m Q X, fidPropFlushDelSpec args m Q X →
      Γ "full_prop_flush_del_fid" [i64, i64] [.bool] args m Q X)
    (hBo : ∀ xs mb,
      (∃ (sem_b : FullState) (dlen_b : Nat),
        PropLitInv c F0 F_cur
          { s_base with scratch := { s_base.scratch with delayed := sem_b.scratch.delayed } }
          sem_b not_lit.toNat xs.2.2.2.2.1.toNat xs.2.2.2.2.2.2.1.toNat
          xs.2.2.2.2.2.1.toNat xs.2.2.2.2.2.2.2.1.toNat ∧
        xs.2.2.2.2.2.2.2.2.1.toNat = 3 * dlen_b ∧ dlen_b ≤ c.delayed_cap ∧
        DelayedWatchesOk s_base.core sem_b.scratch.delayed dlen_b not_lit.toNat ∧
        (c.delayed_cap = 0 → sem_b.scratch.delayed = s.scratch.delayed) ∧
        xs.1.toNat = sem_b.core.trail_end ∧ xs.2.1 = sem_b.core.unassigned ∧
        xs.2.2.1 = sem_b.core.unflushed ∧
        (xs.2.2.2.2.2.2.2.2.2.1 = 0#64 → sem_b.core.oom = 0#64 ∧
          (isBeyond = false → sem_b.core.confl_type = s.core.confl_type) ∧
          xs.2.2.2.2.2.1 = xs.2.2.2.2.2.2.2.1) ∧
        (isBeyond = true → S13ConflEq s.core sem_b.core) ∧
        (xs.2.2.2.2.2.2.2.2.2.1 = 1#64 → isBeyond = false ∧
          PropLitConfl F_cur ign_v sem_b.core ∧ sem_b.core.oom = 0#64) ∧
        (if isBeyond then (xs.2.2.2.2.2.2.2.2.2.1 = 0#64 ∨ xs.2.2.2.2.2.2.2.2.2.1 = 2#64)
         else (xs.2.2.2.2.2.2.2.2.2.1 = 0#64 ∨ xs.2.2.2.2.2.2.2.2.2.1 = 1#64 ∨
           xs.2.2.2.2.2.2.2.2.2.1 = 2#64)) ∧
        (FullMem c (fastPropMem s_disk sem_b) ⋆ R) mb) →
      Bo xs mb)
    (hLo : ∀ rem xs m,
      rem < (end_o.toNat - p_o.toNat) + 1 →
      (∃ (sem_o' : FullState) (dlen_o' : Nat),
        rem = (xs.2.2.2.2.2.2.2.1.toNat - xs.2.2.2.2.2.1.toNat) +
          (if xs.2.2.2.2.2.2.2.2.2.2.1 then 1 else 0) ∧
        PropLitInv c F0 F_cur
          { s_base with scratch := { s_base.scratch with delayed := sem_o'.scratch.delayed } }
          sem_o' not_lit.toNat xs.2.2.2.2.1.toNat xs.2.2.2.2.2.2.1.toNat
          xs.2.2.2.2.2.1.toNat xs.2.2.2.2.2.2.2.1.toNat ∧
        xs.2.2.2.2.2.2.2.2.1.toNat = 3 * dlen_o' ∧ dlen_o' ≤ c.delayed_cap ∧
        DelayedWatchesOk s_base.core sem_o'.scratch.delayed dlen_o' not_lit.toNat ∧
        (c.delayed_cap = 0 → sem_o'.scratch.delayed = s.scratch.delayed) ∧
        xs.1.toNat = sem_o'.core.trail_end ∧ xs.2.1 = sem_o'.core.unassigned ∧
        xs.2.2.1 = sem_o'.core.unflushed ∧
        (isBeyond = true → S13ConflEq s.core sem_o'.core) ∧
        (xs.2.2.2.2.2.2.2.2.2.2.1 = true → xs.2.2.2.2.2.2.2.2.2.1 = 0#64 ∧
          sem_o'.core.oom = 0#64 ∧
          (isBeyond = false → sem_o'.core.confl_type = s.core.confl_type)) ∧
        (xs.2.2.2.2.2.2.2.2.2.2.1 = false →
          (xs.2.2.2.2.2.2.2.2.2.1 = 0#64 → sem_o'.core.oom = 0#64 ∧
            (isBeyond = false → sem_o'.core.confl_type = s.core.confl_type) ∧
            xs.2.2.2.2.2.1 = xs.2.2.2.2.2.2.2.1) ∧
          (xs.2.2.2.2.2.2.2.2.2.1 = 1#64 → isBeyond = false ∧
            PropLitConfl F_cur ign_v sem_o'.core ∧ sem_o'.core.oom = 0#64) ∧
          (if isBeyond then (xs.2.2.2.2.2.2.2.2.2.1 = 0#64 ∨ xs.2.2.2.2.2.2.2.2.2.1 = 1#64)
           else (xs.2.2.2.2.2.2.2.2.2.1 = 0#64 ∨ xs.2.2.2.2.2.2.2.2.2.1 = 1#64))) ∧
        (FullMem c (fastPropMem s_disk sem_o') ⋆ R) m) →
      Lo xs m)
    (hs_base : s_base = { sem with core := { sem.core with
      propagated := s.core.propagated, fuel := s.core.fuel } })
    (hs_disk : ∃ te_mem, s_disk = { s with core := { s.core with trail_end := te_mem } } ∧
      te_mem ≤ sem.core.trail_end ∧ s.core.propagated ≤ te_mem)
    (hlen0 : s.LengthsOk c) (hlen_o : sem.LengthsOk c)
    (hcv_o : sem.core.cur_vars = s.core.cur_vars)
    (hnot_lt : not_lit.toNat < 2 * sem.core.cur_vars)
    (hnl64 : nl64 = not_lit.setWidth 64 <<< (1 : Nat))
    (hnl64_idx : nl64.toNat = 2 * not_lit.toNat)
    (hct_o2 : isBeyond = false → sem_o.core.confl_type = s.core.confl_type)
    (hbcf_o2 : isBeyond = true → S13ConflEq s.core sem_o.core)
    (hpi_p : PropLitInv c F0 F_cur
      { s_base with scratch := { s_base.scratch with delayed := sem_p.scratch.delayed } }
      sem_p not_lit.toNat off_o.toNat q_p.toNat p_p.toNat end_o.toNat)
    (hdi_p : di_p.toNat = 3 * dlen_p) (hdl_p : dlen_p ≤ c.delayed_cap)
    (hdok_p : DelayedWatchesOk s_base.core sem_p.scratch.delayed dlen_p not_lit.toNat)
    (hd0_p : c.delayed_cap = 0 → sem_p.scratch.delayed = s.scratch.delayed)
    (hp_ge : p_o.toNat ≤ p_p.toNat)
    (hte_p : te_p.toNat = sem_p.core.trail_end)
    (hun_p : un_p = sem_p.core.unassigned) (huf_p : uf_p = sem_p.core.unflushed)
    (hoom_p : sem_p.core.oom = 0#64)
    (hnoov : ovf_p = false →
      (brk_p = 0#64 → p_p = end_o ∧ S13ConflEq sem_o.core sem_p.core) ∧
      (brk_p = 1#64 → isBeyond = false ∧ PropLitConfl F_cur ign_v sem_p.core) ∧
      (brk_p = 0#64 ∨ brk_p = 1#64))
    (hov_yes : ovf_p = true → brk_p = 0#64 ∧ S13ConflEq sem_o.core sem_p.core ∧
      2 ≤ p_p.toNat - off_o.toNat ∧ q_p.toNat + 2 ≤ p_p.toNat ∧
      end_o.toNat - p_p.toNat < end_o.toNat - p_o.toNat ∧
      ovf_cr_p.toNat < 0x80000000 ∧ ovf_cr_p.toNat ∈ fullArenaClauseRefsCore sem_p.core ∧
      ovf_cr_p.toNat + 3 + fullArenaClauseSizeCore sem_p.core ovf_cr_p.toNat ≤
        sem_p.core.arena_len ∧
      ovf_oth_p.toNat < 2 * sem_p.core.cur_vars ∧ ovf_rw_p.toNat < 2 * sem_p.core.cur_vars ∧
      ovf_rw_p.toNat ≠ not_lit.toNat ∧ 2 ≤ ovf_ri_p.toNat ∧
      ovf_ri_p.toNat < fullArenaClauseSizeCore sem_p.core ovf_cr_p.toNat ∧
      ∃ l0' l1', (l0' = not_lit ∨ l1' = not_lit) ∧ ovf_oth_p = l0' ^^^ l1' ^^^ not_lit ∧
        sem_p.core.arena[ovf_cr_p.toNat + 3]? = some l0' ∧
        sem_p.core.arena[ovf_cr_p.toNat + 4]? = some l1' ∧
        sem_p.core.arena[ovf_cr_p.toNat + 3 + ovf_ri_p.toNat]? = some ovf_rw_p)
    (hmbp : (FullMem c (fastPropMem s_disk sem_p) ⋆ R) mbp) :
    wp Γ Q X (fidPostLpOvfExpr c nl64 not_lit off_o end_o Bo Lo
      te_p un_p uf_p tk_p p_p q_p di_p brk_p ovf_p ovf_rw_p ovf_oth_p ovf_cr_p ovf_ri_p)
      mbp := by
  obtain ⟨te_mem, hsd_eq, htem_le, hpr_tem⟩ := hs_disk
  have hsd_len : s_disk.LengthsOk c := hsd_eq ▸ ⟨{ hlen0.core_ok with
    trail_end_le := Nat.le_trans htem_le (hcv_o ▸ hlen_o.core_ok.trail_end_le)
    propagated_le := hpr_tem }, hlen0.scratch_ok⟩
  have hsd_cv : s_disk.core.cur_vars = s_base.core.cur_vars := by
    rw [hsd_eq, hs_base]; exact hcv_o.symm
  have hsd_pr : s_disk.core.propagated = s_base.core.propagated := by rw [hsd_eq, hs_base]
  cases ovf_p
  · have ⟨hbrk0_fn, hbrk1_fn, hbrk_disj⟩ := hnoov rfl
    unfold fidPostLpOvfExpr
    refine wp_unroll_group fun _Js0 _hJs0 => ?_
    s13_hsteps
    exact hLo (end_o.toNat - p_p.toNat)
      (te_p, un_p, uf_p, tk_p, off_o, p_p, q_p, end_o, di_p, brk_p, false, ()) mbp
      (by have := hpi_p.sw.p_le_end; omega)
      ⟨sem_p, dlen_p, rfl, hpi_p, hdi_p, hdl_p, hdok_p, hd0_p, hte_p, hun_p, huf_p,
        (fun hb => s13ConflEq_trans ((hbrk0_fn (hbrk_disj.resolve_right
          (fun h1 => Bool.noConfusion ((hbrk1_fn h1).1.symm.trans hb)))).2) (hbcf_o2 hb)),
        fun h => Bool.noConfusion h,
        fun _ => ⟨fun h0 => ⟨hoom_p, fun hb => (hbrk0_fn h0).2.1.trans (hct_o2 hb),
            (hbrk0_fn h0).1⟩,
          fun h1 => let ⟨hb, hc⟩ := hbrk1_fn h1; ⟨hb, hc, hoom_p⟩,
          (by cases isBeyond <;> exact hbrk_disj)⟩,
        hmbp⟩
  · have hov_y := hov_yes rfl
    exact s13_post_lp_ovf_wp (isBeyond := false) hOvf hFlush
      (fun xs mb ⟨sem_b, dlen_b, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, hcf_b, h12⟩ =>
        hBo xs mb ⟨sem_b, dlen_b, h1, h2, h3, h4, h5, h6, h7, h8,
          fun h0 => let ⟨ha, hb, hc⟩ := h9 h0; ⟨ha, fun his => hb.1.trans (hct_o2 his), hc⟩,
          fun hb => s13ConflEq_trans hcf_b (hbcf_o2 hb),
          fun h1 => absurd h1 h10,
          (by cases isBeyond with
            | true => simp only [↓reduceIte]; rcases h11 with h | h <;> simp [h]
            | false => simp only [Bool.false_eq_true, ↓reduceIte]
                       rcases h11 with h | h <;> simp [h]),
          h12⟩)
      (fun n' xs m hlt ⟨sem_o', dlen_o', hn, ha, hb, hc, hd, he, hf, hg, hh, hi, hj, hk⟩ =>
        hLo n' xs m (by
          simp only [↓reduceIte] at hlt
          have hlt_pp := hov_y.2.2.2.2.1
          omega)
          ⟨sem_o', dlen_o', hn, ha, hb, hc, hd, he, hf, hg, hh,
            (fun hb' => by
              by_cases hov' : xs.2.2.2.2.2.2.2.2.2.2.1 = true
              · exact s13ConflEq_trans (hi hov').2.2 (hbcf_o2 hb')
              · have hovf' : xs.2.2.2.2.2.2.2.2.2.2.1 = false := Bool.eq_false_iff.mpr hov'
                have ⟨ha', _, hc'⟩ := hj hovf'
                exact s13ConflEq_trans (ha' hc').2.1 (hbcf_o2 hb')),
            fun ht => let ⟨ha', hb', hc'⟩ := hi ht;
              ⟨ha', hb', fun his => hc'.1.trans (hct_o2 his)⟩,
            fun hf' => let ⟨ha', hb', hc'⟩ := hj hf'; ⟨fun h0 => let ⟨x, y, z⟩ := ha' h0
              ⟨x, fun his => y.1.trans (hct_o2 his), z⟩, fun h1 => absurd h1 hb',
              by cases isBeyond <;> simp [hc']⟩, hk⟩)
      c.harena c.hwcap hsd_len hsd_cv hsd_pr
      (by
        have hcvp : sem_p.core.cur_vars = sem.core.cur_vars := by
          rw [hpi_p.cur_vars_eq, show ({ s_base with scratch :=
            { s_base.scratch with delayed := sem_p.scratch.delayed } } : FullState).core.cur_vars =
            s_base.core.cur_vars from rfl, hs_base]
        exact hcvp ▸ hnot_lt)
      hnl64 hnl64_idx rfl
      hpi_p hdi_p hdl_p hdok_p hd0_p hte_p hun_p huf_p hoom_p
      (fun h => by cases h)
      (fun _ =>
        let ⟨a1, a2, a3, a4, _, a5, a6, a7, a8, a9, a10, a11, a12, l0', l1', hl, hoth, h3, h4,
          hri⟩ := hov_y
        ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, ⟨l0', l1', hl, hoth, h3, h4⟩, hri⟩)
      hmbp

/-- Shared `wvec[nl64]` slice-entry `hLo` constructor for the non-empty watch list branch
(`sz != 0`). -/
theorem s13_outer_sz_nz_lo_pack {isBeyond : Bool} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s s_disk s_base sem sem_d : FullState}
    {prop_v tend_v unass_v unfl_v ticks1 : BitVec 64} {lit not_lit : BitVec 32}
    {ign_v : BitVec 64} {R : Mem 64 → Prop} {ml : Mem 64}
    {Lo : Cont [i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, Ty.bool]}
    (hLo : ∀ rem xs m,
      (∃ (sem_o : FullState) (dlen_o : Nat),
        rem = (xs.2.2.2.2.2.2.2.1.toNat - xs.2.2.2.2.2.1.toNat) +
          (if xs.2.2.2.2.2.2.2.2.2.2.1 then 1 else 0) ∧
        PropLitInv c F0 F_cur
          { s_base with scratch := { s_base.scratch with delayed := sem_o.scratch.delayed } }
          sem_o not_lit.toNat xs.2.2.2.2.1.toNat xs.2.2.2.2.2.2.1.toNat
          xs.2.2.2.2.2.1.toNat xs.2.2.2.2.2.2.2.1.toNat ∧
        xs.2.2.2.2.2.2.2.2.1.toNat = 3 * dlen_o ∧ dlen_o ≤ c.delayed_cap ∧
        DelayedWatchesOk s_base.core sem_o.scratch.delayed dlen_o not_lit.toNat ∧
        (c.delayed_cap = 0 → sem_o.scratch.delayed = s.scratch.delayed) ∧
        xs.1.toNat = sem_o.core.trail_end ∧ xs.2.1 = sem_o.core.unassigned ∧
        xs.2.2.1 = sem_o.core.unflushed ∧
        (isBeyond = true → S13ConflEq s.core sem_o.core) ∧
        (xs.2.2.2.2.2.2.2.2.2.2.1 = true → xs.2.2.2.2.2.2.2.2.2.1 = 0#64 ∧
          sem_o.core.oom = 0#64 ∧
          (isBeyond = false → sem_o.core.confl_type = s.core.confl_type)) ∧
        (xs.2.2.2.2.2.2.2.2.2.2.1 = false →
          (xs.2.2.2.2.2.2.2.2.2.1 = 0#64 → sem_o.core.oom = 0#64 ∧
            (isBeyond = false → sem_o.core.confl_type = s.core.confl_type) ∧
            xs.2.2.2.2.2.1 = xs.2.2.2.2.2.2.2.1) ∧
          (xs.2.2.2.2.2.2.2.2.2.1 = 1#64 → isBeyond = false ∧
            PropLitConfl F_cur ign_v sem_o.core ∧ sem_o.core.oom = 0#64) ∧
          (xs.2.2.2.2.2.2.2.2.2.1 = 0#64 ∨ xs.2.2.2.2.2.2.2.2.2.1 = 1#64)) ∧
        (FullMem c (fastPropMem s_disk sem_o) ⋆ R) m) →
      Lo xs m)
    (hs_base : s_base = { sem with core := { sem.core with
      propagated := s.core.propagated, fuel := s.core.fuel } })
    (hd0_sem : c.delayed_cap = 0 → sem.scratch.delayed = s.scratch.delayed)
    (htend_eq : sem.core.trail_end = tend_v.toNat)
    (hunass_eq : sem.core.unassigned = unass_v) (hunfl_eq : sem.core.unflushed = unfl_v)
    (hoom_o : sem.core.oom = 0#64)
    (hct_o : isBeyond = false → sem.core.confl_type = s.core.confl_type)
    (hbcf_o : isBeyond = true → S13ConflEq s.core sem.core)
    (htrl_d : (fastPropMem s_disk sem_d).core.trl = sem.core.trl)
    (hp_sem_lt_trl : prop_v.toNat < sem.core.trl.length)
    (hlit_trl : sem.core.trl[prop_v.toNat]'hp_sem_lt_trl = lit)
    (hnot_eq : not_lit = lit ^^^ 1#32)
    (hnl64_idx : (not_lit.setWidth 64 <<< (1 : Nat)).toNat = 2 * not_lit.toNat)
    (hnl64_1_idx : ((not_lit.setWidth 64 <<< (1 : Nat)) + 1#64).toNat = 2 * not_lit.toNat + 1)
    (hnl64_lt_wv0 : (not_lit.setWidth 64 <<< (1 : Nat)).toNat < sem.core.wvec.length)
    (hnl64_1_lt_wv0 : ((not_lit.setWidth 64 <<< (1 : Nat)) + 1#64).toNat < sem.core.wvec.length)
    (hoff0_nat : ((sem.core.wvec[(not_lit.setWidth 64 <<< (1 : Nat)).toNat]'
      hnl64_lt_wv0).setWidth 64).toNat = fullWatchOffCore s_base.core not_lit.toNat)
    (hsz0_nat : ((sem.core.wvec[((not_lit.setWidth 64 <<< (1 : Nat)) +
      1#64).toNat]'hnl64_1_lt_wv0).setWidth 64).toNat = fullWatchSizeCore s_base.core not_lit.toNat)
    (hend0_lt64 : fullWatchOffCore s_base.core not_lit.toNat +
      fullWatchSizeCore s_base.core not_lit.toNat < 2 ^ 64)
    (hpi0 : PropLitInv c F0 F_cur s_base s_base not_lit.toNat
      (fullWatchOffCore s_base.core not_lit.toNat) (fullWatchOffCore s_base.core not_lit.toNat)
      (fullWatchOffCore s_base.core not_lit.toNat)
      (fullWatchOffCore s_base.core not_lit.toNat + fullWatchSizeCore s_base.core not_lit.toNat))
    {pf1 pf2 pf3 pf4} (hm_base : (FullMem c (fastPropMem s_disk s_base) ⋆ R) ml) :
    let off_v := (sem.core.wvec[(BitVec.setWidth 64
      ((fastPropMem s_disk sem_d).core.trl[prop_v.toNat]'pf1 ^^^ 1#32) <<< 1).toNat]'pf2).setWidth
      64
    let sz_v := (sem.core.wvec[((BitVec.setWidth 64
      ((fastPropMem s_disk sem_d).core.trl[prop_v.toNat]'pf3 ^^^ 1#32) <<< 1) +
      1#64).toNat]'pf4).setWidth 64
    Lo (tend_v, unass_v, unfl_v, ticks1, off_v, off_v, off_v, off_v + sz_v, 0#64, 0#64, true,
      ()) ml := by
  have hof0_eq : (BitVec.ofNat 64 (fullWatchOffCore s_base.core not_lit.toNat)).toNat =
      fullWatchOffCore s_base.core not_lit.toNat :=
    m7_bv64_ofNat_toNat_lt (Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hend0_lt64)
  have hsz0_eq : (BitVec.ofNat 64 (fullWatchSizeCore s_base.core not_lit.toNat)).toNat =
      fullWatchSizeCore s_base.core not_lit.toNat :=
    m7_bv64_ofNat_toNat_lt (Nat.lt_of_le_of_lt (Nat.le_add_left _ _) hend0_lt64)
  have hadd0_eq : (BitVec.ofNat 64 (fullWatchOffCore s_base.core not_lit.toNat) +
      BitVec.ofNat 64 (fullWatchSizeCore s_base.core not_lit.toNat)).toNat =
      fullWatchOffCore s_base.core not_lit.toNat + fullWatchSizeCore s_base.core not_lit.toNat := by
    rw [BitVec.toNat_add, hof0_eq, hsz0_eq, Nat.mod_eq_of_lt hend0_lt64]
  have hoff_trl : (sem.core.wvec[(BitVec.setWidth 64
      ((fastPropMem s_disk sem_d).core.trl[prop_v.toNat]'pf1 ^^^ 1#32) <<< 1).toNat]'pf2).setWidth
      64 = BitVec.ofNat 64 (fullWatchOffCore s_base.core not_lit.toNat) := by
    have h1 : (fastPropMem s_disk sem_d).core.trl[prop_v.toNat]'pf1 = lit := by
      simpa only [htrl_d] using (fc_getElem_eq_of_idx rfl _ hp_sem_lt_trl).trans hlit_trl
    have hidx := m7_shl1_eq_of_trl rfl pf1 pf1 h1
    have hget : (sem.core.wvec[(BitVec.setWidth 64
        ((fastPropMem s_disk sem_d).core.trl[prop_v.toNat]'pf1 ^^^ 1#32) <<< 1).toNat]'pf2
        ).setWidth 64 =
        (sem.core.wvec[(not_lit.setWidth 64 <<< (1 : Nat)).toNat]'hnl64_lt_wv0).setWidth 64 := by
      congr 1; exact fc_getElem_eq_of_idx (hidx.trans (hnot_eq ▸ hnl64_idx.symm)) pf2 hnl64_lt_wv0
    rw [hget]; apply BitVec.eq_of_toNat_eq; rw [hoff0_nat, hof0_eq]
  have hsz_trl : (sem.core.wvec[((BitVec.setWidth 64
      ((fastPropMem s_disk sem_d).core.trl[prop_v.toNat]'pf3 ^^^ 1#32) <<< 1) +
      1#64).toNat]'pf4).setWidth 64 =
      BitVec.ofNat 64 (fullWatchSizeCore s_base.core not_lit.toNat) := by
    have h1 : (fastPropMem s_disk sem_d).core.trl[prop_v.toNat]'pf3 = lit := by
      simpa only [htrl_d] using (fc_getElem_eq_of_idx rfl _ hp_sem_lt_trl).trans hlit_trl
    have hidx := m7_shl1_add1_eq_of_trl rfl pf3 pf3 h1
    have hget : (sem.core.wvec[((BitVec.setWidth 64
        ((fastPropMem s_disk sem_d).core.trl[prop_v.toNat]'pf3 ^^^ 1#32) <<< 1) +
        1#64).toNat]'pf4).setWidth 64 =
        (sem.core.wvec[((not_lit.setWidth 64 <<< (1 : Nat)) +
          1#64).toNat]'hnl64_1_lt_wv0).setWidth 64 := by
      congr 1
      exact fc_getElem_eq_of_idx (hidx.trans (hnot_eq ▸ hnl64_1_idx.symm)) pf4 hnl64_1_lt_wv0
    rw [hget]; apply BitVec.eq_of_toNat_eq; rw [hsz0_nat, hsz0_eq]
  refine hLo (fullWatchSizeCore s_base.core not_lit.toNat + 1) _ ml
    ⟨s_base, 0, ?_, ?_, rfl, Nat.zero_le _, fun _ h => absurd h (Nat.not_lt_zero _),
      by rw [hs_base]; exact hd0_sem, by rw [hs_base]; exact htend_eq.symm,
      by rw [hs_base]; exact hunass_eq.symm, by rw [hs_base]; exact hunfl_eq.symm,
      (fun hb => by rw [hs_base]; exact hbcf_o hb),
      fun _ => ⟨rfl, by rw [hs_base]; exact hoom_o, fun hb => by rw [hs_base]; exact hct_o hb⟩,
      fun h => by simp at h, hm_base⟩
  · dsimp only; rw [hoff_trl, hsz_trl, hadd0_eq, hof0_eq]; simp only [↓reduceIte]
    exact congrArg (· + 1) (Nat.add_sub_cancel_left _ _).symm
  · dsimp only; rw [hoff_trl, hsz_trl, hof0_eq, hadd0_eq]; exact hpi0

/-- Shared `not_lit` + `s_base` + `PropLitInv.init` + `nl_lvl` facts for both `propagate_ignore`
and `propagate_beyond`. -/
theorem s13_sz_nz_init_facts {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s sem s_base s_disk sem_d : FullState} {prop_v : BitVec 64} {lit not_lit : BitVec 32}
    (hwc : c.wcap < 2 * dimacsBound) (hlen_o : sem.LengthsOk c)
    (hw_o : FullWitnessInv c F0 F_cur sem.core) (hcv_o : sem.core.cur_vars = s.core.cur_vars)
    (hdm_o : sem.core.dense_mode = 0#64) (hprop_eq : sem.core.propagated = prop_v.toNat)
    (hp_lt_sem : sem.core.propagated < sem.core.trail_end)
    (hpr_ge : s.core.propagated ≤ prop_v.toNat)
    (hs_base : s_base = { sem with core := { sem.core with
      propagated := s.core.propagated, fuel := s.core.fuel } })
    (hnot_lt : not_lit.toNat < 2 * sem.core.cur_vars)
    (hnot_f0 : sem.core.vals[not_lit.toNat]?.getD 0#8 = 0xFF#8)
    (hnl64_idx : (not_lit.setWidth 64 <<< (1 : Nat)).toNat = 2 * not_lit.toNat)
    (hnl64_1_idx : ((not_lit.setWidth 64 <<< (1 : Nat)) + 1#64).toNat = 2 * not_lit.toNat + 1)
    {hnl64_lt_wv0 : (not_lit.setWidth 64 <<< (1 : Nat)).toNat < sem.core.wvec.length}
    {hnl64_1_lt_wv0 : ((not_lit.setWidth 64 <<< (1 : Nat)) + 1#64).toNat < sem.core.wvec.length}
    {hp_lt_trl : prop_v.toNat < (fastPropMem s_disk sem_d).core.trl.length}
    (htrl_d : (fastPropMem s_disk sem_d).core.trl = sem.core.trl)
    (hlvl_d : (fastPropMem s_disk sem_d).core.lvl = sem.core.lvl)
    (hp_sem_lt_trl : prop_v.toNat < sem.core.trl.length)
    (hlit_trl : sem.core.trl[prop_v.toNat]'hp_sem_lt_trl = lit)
    (hnot_eq : not_lit = lit ^^^ 1#32)
    (hsz_ne : (sem.core.wvec[((not_lit.setWidth 64 <<< (1 : Nat)) +
      1#64).toNat]'hnl64_1_lt_wv0).setWidth 64 ≠ 0#64) :
    ((sem.core.wvec[(not_lit.setWidth 64 <<< (1 : Nat)).toNat]'hnl64_lt_wv0).setWidth 64).toNat =
      fullWatchOffCore s_base.core not_lit.toNat ∧
    ((sem.core.wvec[((not_lit.setWidth 64 <<< (1 : Nat)) +
      1#64).toNat]'hnl64_1_lt_wv0).setWidth 64).toNat =
      fullWatchSizeCore s_base.core not_lit.toNat ∧
    fullWatchOffCore s_base.core not_lit.toNat +
      fullWatchSizeCore s_base.core not_lit.toNat < 2 ^ 64 ∧
    PropLitInv c F0 F_cur s_base s_base not_lit.toNat
      (fullWatchOffCore s_base.core not_lit.toNat) (fullWatchOffCore s_base.core not_lit.toNat)
      (fullWatchOffCore s_base.core not_lit.toNat)
      (fullWatchOffCore s_base.core not_lit.toNat + fullWatchSizeCore s_base.core not_lit.toNat) ∧
    (∃ hl_idx : (((((fastPropMem s_disk sem_d).core.trl[prop_v.toNat]'hp_lt_trl ^^^ 1#32) >>>
        1#32).setWidth 64)).toNat < (fastPropMem s_disk sem_d).core.lvl.length,
      ∀ k : FullCoreState, FullPropDecSpecs.FullTrailExt s_base.core k →
        k.lvl[not_lit.toNat / 2]?.getD 0#32 =
          (fastPropMem s_disk sem_d).core.lvl[(((((fastPropMem
            s_disk sem_d).core.trl[prop_v.toNat]'hp_lt_trl ^^^ 1#32) >>>
            1#32).setWidth 64)).toNat]'hl_idx) := by
  subst hs_base
  have hbase_len : FullState.LengthsOk c
      { sem with core := { sem.core with propagated := s.core.propagated, fuel := s.core.fuel } } :=
    ⟨{ hlen_o.core_ok with
      propagated_le := Nat.le_trans hpr_ge (hprop_eq ▸ hlen_o.core_ok.propagated_le) },
      hlen_o.scratch_ok⟩
  have hbase_nw : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c ({ sem with core :=
      { sem.core with propagated := s.core.propagated, fuel := s.core.fuel } }).core) :=
    fullWitnessInv_nw_congr hlen_o.core_ok.cur_vars_le
      (fullWitnessInv_to_nw hlen_o.core_ok.cur_vars_le hw_o) rfl rfl rfl rfl rfl rfl rfl
      rfl rfl rfl rfl rfl rfl
  have hwat_base : WatchesInv F_cur
      ({ sem with core := { sem.core with
        propagated := s.core.propagated, fuel := s.core.fuel } }).core := by
    have hw_sp : ModeWatchesInv F_cur { sem.core with
        propagated := s.core.propagated, fuel := s.core.fuel } :=
      hw_o.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr)
    simpa only [ModeWatchesInv, hdm_o, ↓reduceIte] using hw_sp
  have hoff0_nat : ((sem.core.wvec[(not_lit.setWidth 64 <<< (1 : Nat)).toNat]'
      hnl64_lt_wv0).setWidth 64).toNat = fullWatchOffCore ({ sem with core := { sem.core with
        propagated := s.core.propagated, fuel := s.core.fuel } }).core not_lit.toNat := by
    unfold fullWatchOffCore; rw [bv_c0_zext32_64]
    exact congrArg BitVec.toNat (fc_getElem_eq_getD_of_idx hnl64_idx _)
  have hsz0_nat : ((sem.core.wvec[((not_lit.setWidth 64 <<< (1 : Nat)) +
      1#64).toNat]'hnl64_1_lt_wv0).setWidth 64).toNat =
      fullWatchSizeCore ({ sem with core := { sem.core with
        propagated := s.core.propagated, fuel := s.core.fuel } }).core not_lit.toNat := by
    unfold fullWatchSizeCore; rw [bv_c0_zext32_64]
    exact congrArg BitVec.toNat (fc_getElem_eq_getD_of_idx hnl64_1_idx _)
  have hsz0_pos : 0 < fullWatchSizeCore ({ sem with core := { sem.core with
      propagated := s.core.propagated, fuel := s.core.fuel } }).core not_lit.toNat := by
    rw [← hsz0_nat]; by_cases h0 : ((sem.core.wvec[((not_lit.setWidth 64 <<<
      (1 : Nat)) + 1#64).toNat]'hnl64_1_lt_wv0).setWidth 64).toNat = 0
    · exact absurd (BitVec.eq_of_toNat_eq h0) hsz_ne
    · omega
  have hpi0 : PropLitInv c F0 F_cur
      { sem with core := { sem.core with propagated := s.core.propagated, fuel := s.core.fuel } }
      { sem with core := { sem.core with propagated := s.core.propagated, fuel := s.core.fuel } }
      not_lit.toNat
      (fullWatchOffCore ({ sem with core := { sem.core with
        propagated := s.core.propagated, fuel := s.core.fuel } }).core not_lit.toNat)
      (fullWatchOffCore ({ sem with core := { sem.core with
        propagated := s.core.propagated, fuel := s.core.fuel } }).core not_lit.toNat)
      (fullWatchOffCore ({ sem with core := { sem.core with
        propagated := s.core.propagated, fuel := s.core.fuel } }).core not_lit.toNat)
      (fullWatchOffCore ({ sem with core := { sem.core with
        propagated := s.core.propagated, fuel := s.core.fuel } }).core not_lit.toNat +
        fullWatchSizeCore ({ sem with core := { sem.core with
          propagated := s.core.propagated, fuel := s.core.fuel } }).core not_lit.toNat) :=
    { len := hbase_len, nw := hbase_nw
      sw := SplitWatchesInv.init (by dsimp only; exact hnot_lt) hwat_base hsz0_pos
      ag := .refl _ _, tr := .refl _, perm := .refl _, sc_eq := rfl
      not_f := by dsimp only; exact hnot_f0 }
  have hend0_lt64 : fullWatchOffCore ({ sem with core := { sem.core with
        propagated := s.core.propagated, fuel := s.core.fuel } }).core not_lit.toNat +
      fullWatchSizeCore ({ sem with core := { sem.core with
        propagated := s.core.propagated, fuel := s.core.fuel } }).core not_lit.toNat < 2 ^ 64 := by
    have := hpi0.end_lt_wcap (by dsimp only; exact hnot_lt)
    exact Nat.lt_of_le_of_lt (Nat.le_trans this.1 this.2) (Nat.lt_trans hwc (by decide))
  have htrl_eq : (fastPropMem s_disk sem_d).core.trl[prop_v.toNat]'hp_lt_trl = lit := by
    simpa only [htrl_d] using (fc_getElem_eq_of_idx rfl _ hp_sem_lt_trl).trans hlit_trl
  have hnl_div : (((((fastPropMem s_disk sem_d).core.trl[prop_v.toNat]'hp_lt_trl ^^^ 1#32) >>>
      1#32).setWidth 64)).toNat = not_lit.toNat / 2 := by
    rw [htrl_eq, ← hnot_eq, bv_c0_zext32_64]
    simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hnl_idx_lt : (((((fastPropMem s_disk sem_d).core.trl[prop_v.toNat]'hp_lt_trl ^^^ 1#32) >>>
      1#32).setWidth 64)).toNat < (fastPropMem s_disk sem_d).core.lvl.length := by
    rw [hlvl_d, hlen_o.core_ok.lvl_len, hnl_div]; have := hlen_o.core_ok.cur_vars_le; omega
  refine ⟨hoff0_nat, hsz0_nat, hend0_lt64, hpi0, hnl_idx_lt, fun k htr => ?_⟩
  have hnot_div2 : not_lit.toNat / 2 = (({ sem with core := { sem.core with
      propagated := s.core.propagated, fuel := s.core.fuel } }).core.trl[prop_v.toNat]?.getD
      0#32).toNat / 2 := by
    have hlt_eq : ({ sem with core := { sem.core with
        propagated := s.core.propagated, fuel := s.core.fuel } }).core.trl[prop_v.toNat]?.getD
        0#32 = lit := by
      dsimp only
      rw [List.getElem?_eq_getElem hp_sem_lt_trl, Option.getD_some, hlit_trl]
    rw [hlt_eq, hnot_eq, BitVec.toNat_xor]
    simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, fc_nat_xor_one]
    split <;> omega
  have hlp := htr.lvl_pres prop_v.toNat (by dsimp only; rw [← hprop_eq]; exact hp_lt_sem)
  rw [← hnot_div2] at hlp; rw [hlp]
  have hsb_lt : not_lit.toNat / 2 < ({ sem with core := { sem.core with
      propagated := s.core.propagated, fuel := s.core.fuel } }).core.lvl.length := by
    dsimp only; rw [hlen_o.core_ok.lvl_len]; have := hlen_o.core_ok.cur_vars_le; omega
  have hget : some (({ sem with core := { sem.core with
      propagated := s.core.propagated, fuel := s.core.fuel } }).core.lvl[not_lit.toNat / 2]'
      hsb_lt) =
      some ((fastPropMem s_disk sem_d).core.lvl[(((((fastPropMem
        s_disk sem_d).core.trl[prop_v.toNat]'hp_lt_trl ^^^ 1#32) >>>
        1#32).setWidth 64)).toNat]'hnl_idx_lt) := by
    rw [← List.getElem?_eq_getElem hsb_lt, ← List.getElem?_eq_getElem hnl_idx_lt, hlvl_d, hnl_div]
  rw [List.getElem?_eq_getElem hsb_lt, Option.getD_some]
  exact Option.some.inj hget

theorem full_propagate_ignore_hot_step13_wp (Γ : Env)
    (hWm4Get : ∀ args m Q X, step13Wm4GetSpec args m Q X →
      Γ "m6_wm4_get" [i64] [i64] args m Q X)
    (hAddTicks : ∀ args m Q X, step13AddTicksSpec args m Q X →
      Γ "m6_hdr_add_ticks" [i64, i64] [] args m Q X)
    (hOvf : ∀ args m Q X, FullM7BcpHot.fullPropLitOvfHotSpec args m Q X →
      Γ "full_prop_lit_ovf_hot" [i64, i32, i32, i32] [.bool] args m Q X)
    (hFlush : ∀ args m Q X, fidPropFlushDelSpec args m Q X →
      Γ "full_prop_flush_del_fid" [i64, i64] [.bool] args m Q X) :
    ∀ args m Q X, step13PropagateIgnoreM6Spec args m Q X →
      Func.wp Γ full_propagate_ignore_hot_body args m Q X := by
  rintro ⟨h, ignore_ref, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, ext0, s, R, rfl, hcfg, hext0, hlen0, hw0,
    hdense0, hm0, hQ⟩
  have hQ' : S13HQ false c F0 F_cur ext0 s ignore_ref R Q := fun r ext' v' f' l' rs' tr' tp' te'
      pr' un' uf' wv' ar' ws' wl' wu' fl' ct' cr' c0' c1' om' sc' m' hx hw2 hl hwf htr hpm hpr hrr
      hdl hnp hd0 hfl hr hbcf hr0 hr1 h2 hno hm =>
    hQ r ext' v' f' l' rs' tr' tp' te' pr' un' uf' wv' ar' ws' wl' wu' fl' ct' cr' c0' c1' om' sc'
      m' hx hw2 hl hwf htr hpm hpr hrr hdl hnp hd0 hfl hr
      (fun h0 => let x := hr0 h0; ⟨x.1, x.2.1 rfl, x.2.2⟩) (hr1 rfl) h2 hno hm
  have hmaxv := c.hmaxv; have har := c.harena; have hwc := c.hwcap; have hdelc := c.hdel
  unfold dimacsBound at hmaxv har hwc hdelc
  have hcv0 := hlen0.core_ok.cur_vars_le
  have hcv_lt64 : s.core.cur_vars < 2 ^ 64 :=
    Nat.lt_of_le_of_lt hcv0 (Nat.lt_trans hmaxv (by decide))
  have h2cv_lt64 : 2 * s.core.cur_vars < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.mul_le_mul_left 2 hcv0)
    (Nat.lt_trans (Nat.mul_lt_mul_of_pos_left hmaxv (by decide)) (by decide))
  have hte0_lt64 : s.core.trail_end < 2 ^ 64 :=
    Nat.lt_of_le_of_lt hlen0.core_ok.trail_end_le hcv_lt64
  have hpr0_lt64 : s.core.propagated < 2 ^ 64 :=
    Nat.lt_of_le_of_lt hlen0.core_ok.propagated_le hte0_lt64
  have hclv_lt32 : s.core.cur_level < 2 ^ 32 := by
    have := hw0.cur_level_le; have := hlen0.core_ok.trail_end_le; omega
  have hclv_lt64 : s.core.cur_level < 2 ^ 64 := Nat.lt_trans hclv_lt32 (by decide)
  have hdelc_lt64 : c.delayed_cap < 2 ^ 64 := Nat.lt_trans hdelc (by decide)
  have hdlim_toNat : (BitVec.ofNat 64 c.delayed_cap * 3#64).toNat = 3 * c.delayed_cap := by
    rw [BitVec.toNat_mul, m7_bv64_ofNat_toNat_lt hdelc_lt64,
      show (3#64 : BitVec 64).toNat = 3 from rfl, Nat.mod_eq_of_lt (by omega)]; omega
  unfold Func.wp full_propagate_ignore_hot_body
  have _hm0_f := fullM6HdrMem_focus_full hm0
  s13_hsplit
  · have hge : s.core.trail_end ≤ s.core.propagated := by
      have hh : s.core.trail_end % 2 ^ 64 ≤ s.core.propagated % 2 ^ 64 := hc
      rwa [Nat.mod_eq_of_lt hte0_lt64, Nat.mod_eq_of_lt hpr0_lt64] at hh
    have hpe := Nat.le_antisymm hlen0.core_ok.propagated_le hge
    exact s13_exit_hQ hQ' hext0 (fun h => ⟨h, .refl _⟩) (.refl _ _) (s13_probePres_of_S13Scr rfl)
      rfl rfl (fun _ => rfl) hlen0 hw0 (s13_trail_refl s.core) (s13_perm_refl s.core) (fun _ => rfl)
      (Nat.le_refl _) (Or.inl rfl) (fun h => absurd h (by decide))
      (fun _ => ⟨hpe, fun _ => rfl, fun h => h, fun hlt => absurd hlt (by omega)⟩)
      (fun _ h => absurd h (by decide)) (fun h => absurd h (by decide)) (fun _ => ⟨rfl, rfl, rfl⟩)
      hm0
  · have hpr_lt : s.core.propagated < s.core.trail_end := by
      have hh : ¬ s.core.trail_end % 2 ^ 64 ≤ s.core.propagated % 2 ^ 64 := hc
      rwa [Nat.mod_eq_of_lt hte0_lt64, Nat.mod_eq_of_lt hpr0_lt64, Nat.not_le] at hh
    s13_hsplit
    · exact s13_exit_hQ hQ' hext0 (fun h => ⟨h, .refl _⟩) (.refl _ _)
        (s13_probePres_of_S13Scr rfl) rfl rfl (fun _ => rfl) hlen0 hw0
        (s13_trail_refl s.core) (s13_perm_refl s.core) (fun _ => rfl) (Nat.le_refl _)
        (Or.inr (Or.inr rfl)) (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
        (fun _ h => absurd h (by decide)) (fun _ => Or.inl hc)
        (fun h => absurd h (Nat.ne_of_lt hpr_lt)) hm0
    · have hoom0 : s.core.oom = 0#64 := hc
      clear _hm0_f; have _hm0_f := fullM6HdrMem_focus_full hm0
      s13_hsteps_nogrp
      refine wp_call_of_spec _ _ (hWm4Get _ _ _ _ ?_)
      refine ⟨c, ext0, s, R, rfl, hcfg, hext0, hlen0, hm0, fun wm4 hm_wm4 => ?_⟩
      clear _hm0_f; have _hm_wm4_f := fullM6HdrMem_focus_full hm_wm4
      s13_hsteps_nogrp
      refine wp_loop_group
        (fun rem (prop_v, tend_v, fuel_v, unass_v, unfl_v, ticks_v, ()) ml =>
          S13OuterInv false c F0 F_cur ext0 s R rem prop_v tend_v fuel_v unass_v unfl_v ticks_v
            ml) ?_ ?_
      · rintro J rem ⟨prop_v, tend_v, fuel_v, unass_v, unfl_v, ticks_v, ⟨⟩⟩ ml ih hinv_o
        obtain ⟨ext1, sem, te_mem, rfl, hext1, hw2b1, hlen_o, hw_o, htr_o, hperm_o, hag_o, hprop_eq,
            htend_eq, hfuel_eq, hunass_eq, hunfl_eq, hoom_o, hct_o, hbcf_o, hdm_o, hcv_o, hcl_o,
            hprob_o, halen_o, hfuel_le, hfuel_lt, hpr_ge, htem_le, hpr_tem, hsc_o, hd0_sem, hml⟩ :=
          s13OuterInv_elim hinv_o
        let s_disk : FullState := { s with core := { s.core with trail_end := te_mem } }
        let sem_d : FullState := { sem with core :=
          { sem.core with propagated := s.core.propagated, fuel := s.core.fuel } }
        have hsd_len : s_disk.LengthsOk c := ⟨{ hlen0.core_ok with
          trail_end_le := Nat.le_trans htem_le (hcv_o ▸ hlen_o.core_ok.trail_end_le)
          propagated_le := hpr_tem }, hlen0.scratch_ok⟩
        have hsemd_len : sem_d.LengthsOk c := ⟨{ hlen_o.core_ok with
          propagated_le := Nat.le_trans hpr_ge (hprop_eq ▸ hlen_o.core_ok.propagated_le) },
          hlen_o.scratch_ok⟩
        have hmem_len := fastPropMem_lengthsOk hsd_len hsemd_len (by simp [s_disk, sem_d, hcv_o])
          rfl rfl
        have hte_lt64 : sem.core.trail_end < 2 ^ 64 :=
          Nat.lt_of_le_of_lt hlen_o.core_ok.trail_end_le (hcv_o ▸ hcv_lt64)
        have hpr_o_lt64 : sem.core.propagated < 2 ^ 64 :=
          Nat.lt_of_le_of_lt hlen_o.core_ok.propagated_le hte_lt64
        have _hml_f := fullM6HdrMem_focus_full hml
        s13_hsplit
        · have hp_lt_o : prop_v.toNat < tend_v.toNat := hc
          have hp_lt_sem : sem.core.propagated < sem.core.trail_end := by
            rw [hprop_eq, htend_eq]; exact hp_lt_o
          s13_hsplit
          · have hfl0 : sem.core.fuel = 0#64 := hfuel_eq.trans hc
            clear ih; s13_hsteps_nogrp; (try dsimp only)
            exact s13_outer_flush_ret (sem := { sem with scratch :=
                { sem.scratch with search_ticks := s.scratch.search_ticks } })
              hAddTicks hQ' hcfg hext1 hw2b1 ⟨hlen_o.core_ok,
                { hlen_o.scratch_ok with phases_len := hlen_o.scratch_ok.phases_len }⟩
              hw_o htr_o hperm_o hag_o (by dsimp only; rw [hsc_o]) hd0_sem hprop_eq htend_eq hfl0
              hunass_eq hunfl_eq hfuel_le hpr_lt (Or.inr (Or.inr rfl)) hbcf_o
              (fun h => absurd h (by decide)) (fun _ => by decide) (fun _ => Or.inr hfl0)
              (fullM6HdrMem_unfocus_full (by simpa only [fastPropMem, s_disk, sem_d, hprop_eq,
                htend_eq, hunass_eq, hunfl_eq, hfl0, BitVec.ofNat_eq_ofNat] using hm))
          · have hfl_ne : sem.core.fuel ≠ 0#64 := fun h => hc (hfuel_eq ▸ h)
            have hfl_pos : 0 < sem.core.fuel.toNat := by
              by_cases h0 : sem.core.fuel.toNat = 0
              · exact absurd (BitVec.eq_of_toNat_eq h0) hfl_ne
              · omega
            have hfl_dec : (sem.core.fuel - 1#64).toNat = sem.core.fuel.toNat - 1 :=
              m7_bv64_sub_toNat (by simp; omega)
            have hfl_rem_dec : (sem.core.fuel - 1#64).toNat < sem.core.fuel.toNat := by omega
            have hp_lt_trl : prop_v.toNat < (fastPropMem s_disk sem_d).core.trl.length := by
              rw [fastPropMem_trl, hlen_o.core_ok.trl_len]
              have := hlen_o.core_ok.trail_end_le; have := hcv_o; omega
            let lit := (fastPropMem s_disk sem_d).core.trl[prop_v.toNat]'hp_lt_trl
            have hlit_eq : lit = sem.core.trl[sem.core.propagated]'(by
                rw [hlen_o.core_ok.trl_len]; have := hlen_o.core_ok.trail_end_le
                have := hcv_o; omega) := by
              simp only [lit, fc_getElem_trl]; exact (fc_getElem_eq_of_idx hprop_eq _ _).symm
            have hlit_lt : lit.toNat < 2 * sem.core.cur_vars := by
              have := hw_o.trail_lits_lt sem.core.propagated hp_lt_sem
              have hlt_trl : sem.core.propagated < sem.core.trl.length := by
                rw [hlen_o.core_ok.trl_len]; have := hlen_o.core_ok.trail_end_le
                have := hcv_o; omega
              rwa [List.getElem?_eq_getElem hlt_trl, Option.getD_some, ← hlit_eq] at this
            let not_lit := lit ^^^ 1#32
            have hnot_lt : not_lit.toNat < 2 * sem.core.cur_vars := by
              dsimp only [not_lit]; rw [BitVec.toNat_xor]
              simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
              rw [fc_nat_xor_one]; split <;> omega
            have hnot_f0 : sem.core.vals[not_lit.toNat]?.getD 0#8 = 0xFF#8 := by
              have hlt_trl : sem.core.propagated < sem.core.trl.length := by
                rw [hlen_o.core_ok.trl_len]; have := hlen_o.core_ok.trail_end_le
                have := hcv_o; omega
              refine (hw_o.vals_false_iff not_lit.toNat hnot_lt).mpr
                ⟨sem.core.propagated, hp_lt_sem, ?_⟩
              rw [List.getElem?_eq_getElem hlt_trl, Option.getD_some, ← hlit_eq]
              dsimp only [not_lit]; rw [BitVec.toNat_xor]
              simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
              rcases Nat.mod_two_eq_zero_or_one lit.toNat with h | h
              · have h2 : (lit.toNat + 1) % 2 = 1 := by omega
                simp only [fc_nat_xor_one, h, ↓reduceIte, h2, Nat.one_ne_zero]; omega
              · have h2 : (lit.toNat - 1) % 2 = 0 := by omega
                simp only [fc_nat_xor_one, h, Nat.one_ne_zero, ↓reduceIte, h2]; omega
            have hnl64_idx : (not_lit.setWidth 64 <<< (1 : Nat)).toNat = 2 * not_lit.toNat :=
              m7_bv64_shl1_u32_nat not_lit
            have hnl64_1_idx : ((not_lit.setWidth 64 <<< (1 : Nat)) + 1#64).toNat =
                2 * not_lit.toNat + 1 := m7_bv64_shl1_add1_nat not_lit
            have hwv_o_len := hlen_o.core_ok.wvec_len
            have hp1_prop : (prop_v + 1#64).toNat = prop_v.toNat + 1 :=
              m7_bv64_add1_toNat (by omega)
            have hnl64_lt_wv0 :
                (not_lit.setWidth 64 <<< (1 : Nat)).toNat < sem.core.wvec.length := by
              rw [hwv_o_len, hnl64_idx]; have := hlen_o.core_ok.cur_vars_le; omega
            have hnl64_1_lt_wv0 : ((not_lit.setWidth 64 <<< (1 : Nat)) + 1#64).toNat <
                sem.core.wvec.length := by
              rw [hwv_o_len, hnl64_1_idx]; have := hlen_o.core_ok.cur_vars_le; omega
            have hnl64_lt_wv : (not_lit.setWidth 64 <<< (1 : Nat)).toNat <
                (fastPropMem s_disk sem_d).core.wvec.length := by
              rw [fastPropMem_wvec]; exact hnl64_lt_wv0
            have hnl64_1_lt_wv : ((not_lit.setWidth 64 <<< (1 : Nat)) + 1#64).toNat <
                (fastPropMem s_disk sem_d).core.wvec.length := by
              rw [fastPropMem_wvec]; exact hnl64_1_lt_wv0
            have hp_sem_lt_trl : prop_v.toNat < sem.core.trl.length := by
              rw [hlen_o.core_ok.trl_len]; have := hlen_o.core_ok.trail_end_le
              have := hcv_o; omega
            have hsz_hc_idx : ((not_lit.setWidth 64 <<< (1 : Nat)) + 1#64).toNat =
                (2 * ((sem.core.trl[prop_v.toNat]'hp_sem_lt_trl).toNat ^^^ 1) + 1) % 2 ^ 64 := by
              have hlit_trl : sem.core.trl[prop_v.toNat]'hp_sem_lt_trl = lit := by
                simp only [lit, fc_getElem_trl, sem_d]
              have hnot_toNat : not_lit.toNat = lit.toNat ^^^ 1 := by
                dsimp only [not_lit]; rw [BitVec.toNat_xor]
                simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
              rw [hnl64_1_idx, hlit_trl, ← hnot_toNat,
                Nat.mod_eq_of_lt (by have := hlen_o.core_ok.cur_vars_le; omega)]
            s13_hsplit
            · s13_hsteps
              exact ih _ _ ml hfl_rem_dec (s13_outer_sz0_step hext1 hw2b1 hlen_o hw_o htr_o hperm_o
                hag_o hprop_eq htend_eq hfuel_eq hunass_eq hunfl_eq hoom_o hct_o hbcf_o hdm_o hcv_o
                hcl_o hprob_o halen_o hsc_o hd0_sem hfl_rem_dec hfuel_le hp1_prop hp_lt_o hpr_ge
                htem_le hpr_tem hml)
            · have hsz_ne : (sem.core.wvec[((not_lit.setWidth 64 <<< (1 : Nat)) +
                  1#64).toNat]'hnl64_1_lt_wv0).setWidth 64 ≠ 0#64 := by
                have hc' := hc; simp only [fastPropMem_wvec, fastPropMem_trl] at hc'
                rw [fc_getElem_eq_of_idx hsz_hc_idx hnl64_1_lt_wv0
                  (by rw [← hsz_hc_idx]; exact hnl64_1_lt_wv0)]; exact hc'
              let s_base : FullState := { sem with core :=
                { sem.core with propagated := s.core.propagated, fuel := s.core.fuel } }
              have hlit_trl : sem.core.trl[prop_v.toNat]'hp_sem_lt_trl = lit := by
                simp only [lit, fc_getElem_trl, sem_d]
              obtain ⟨hoff0_nat, hsz0_nat, hend0_lt64, hpi0, hnl_idx_lt, hnl_sbase⟩ :=
                s13_sz_nz_init_facts hwc hlen_o hw_o hcv_o hdm_o hprop_eq hp_lt_sem hpr_ge rfl
                  hnot_lt hnot_f0 hnl64_idx hnl64_1_idx (fastPropMem_trl s_disk sem_d)
                  (fastPropMem_lvl s_disk sem_d) hp_sem_lt_trl hlit_trl rfl hsz_ne
              s13_hsteps_nogrp
              have hm_base := fullM6HdrMem_focus_full hml
              refine wp_loop_break_group
                (fun (te_b, un_b, uf_b, tk_b, off_b, p_b, q_b, end_b, di_b, brk_b, _ovf_b, ())
                    mb =>
                  ∃ (sem_b : FullState) (dlen_b : Nat),
                    PropLitInv c F0 F_cur
                      { s_base with scratch :=
                        { s_base.scratch with delayed := sem_b.scratch.delayed } }
                      sem_b not_lit.toNat off_b.toNat q_b.toNat p_b.toNat end_b.toNat ∧
                    di_b.toNat = 3 * dlen_b ∧ dlen_b ≤ c.delayed_cap ∧
                    DelayedWatchesOk s_base.core sem_b.scratch.delayed dlen_b not_lit.toNat ∧
                    (c.delayed_cap = 0 → sem_b.scratch.delayed = s.scratch.delayed) ∧
                    te_b.toNat = sem_b.core.trail_end ∧ un_b = sem_b.core.unassigned ∧
                    uf_b = sem_b.core.unflushed ∧
                    (brk_b = 0#64 → sem_b.core.oom = 0#64 ∧
                      sem_b.core.confl_type = s.core.confl_type ∧ p_b = end_b) ∧
                    (brk_b = 1#64 → PropLitConfl F_cur ignore_ref sem_b.core ∧
                      sem_b.core.oom = 0#64) ∧
                    (brk_b = 0#64 ∨ brk_b = 1#64 ∨ brk_b = 2#64) ∧
                    (FullMem c (fastPropMem s_disk sem_b) ⋆
                      (m6ExtMem (m6ExtAddr c.hdr) ext1 ⋆ R)) mb)
                (fun rem_o (te_o, un_o, uf_o, tk_o, off_o, p_o, q_o, end_o, di_o, brk_o, ovf_o,
                    ()) mo =>
                  ∃ (sem_o : FullState) (dlen_o : Nat),
                    rem_o = (end_o.toNat - p_o.toNat) + (if ovf_o then 1 else 0) ∧
                    PropLitInv c F0 F_cur
                      { s_base with scratch :=
                        { s_base.scratch with delayed := sem_o.scratch.delayed } }
                      sem_o not_lit.toNat off_o.toNat q_o.toNat p_o.toNat end_o.toNat ∧
                    di_o.toNat = 3 * dlen_o ∧ dlen_o ≤ c.delayed_cap ∧
                    DelayedWatchesOk s_base.core sem_o.scratch.delayed dlen_o not_lit.toNat ∧
                    (c.delayed_cap = 0 → sem_o.scratch.delayed = s.scratch.delayed) ∧
                    te_o.toNat = sem_o.core.trail_end ∧ un_o = sem_o.core.unassigned ∧
                    uf_o = sem_o.core.unflushed ∧
                    (ovf_o = true → brk_o = 0#64 ∧ sem_o.core.oom = 0#64 ∧
                      sem_o.core.confl_type = s.core.confl_type) ∧
                    (ovf_o = false →
                      (brk_o = 0#64 → sem_o.core.oom = 0#64 ∧
                        sem_o.core.confl_type = s.core.confl_type ∧ p_o = end_o) ∧
                      (brk_o = 1#64 → PropLitConfl F_cur ignore_ref sem_o.core ∧
                        sem_o.core.oom = 0#64) ∧
                      (brk_o = 0#64 ∨ brk_o = 1#64)) ∧
                    (FullMem c (fastPropMem s_disk sem_o) ⋆
                      (m6ExtMem (m6ExtAddr c.hdr) ext1 ⋆ R)) mo) ?_ ?_ ?_
              · rintro _ ⟨te_b, un_b, uf_b, tk_b, off_b, p_b, q_b, end_b, di_b, brk_b, ovf_b, ⟨⟩⟩
                    mb ⟨sem_b, dlen_b, hpi_b, hdi_b, hdl_b, hdok_b, hd0_b, hte_b, hun_b, huf_b,
                    hbr0, hbr1, hbr_cases, hmb⟩
                exact s13_compact_post_wp hFlush hAddTicks hQ'
                  (fun sem_next te_mc mc0 hlen_n hw_n htr_n hperm_n hag_n hpr_n hfl_n hte_n hun_n
                    huf_n hoom_n hct_n hbcf_n hdm_n hcv_n hcl_n hprob_n halen_n hfl_sem_lt hfl_s_lt
                    hfl_le hpr_ge_n htemc_le hpr_temc hsc_n hd0_n hm_mc =>
                    ih sem_next.core.fuel.toNat (prop_v + 1#64, te_b, fuel_v - 1#64, un_b, uf_b,
                      tk_b, ()) mc0 hfl_sem_lt (s13OuterInv_mk ⟨ext1, sem_next, te_mc, rfl, hext1,
                        hw2b1, hlen_n, hw_n, htr_n, hperm_n, hag_n, hpr_n, hte_n,
                        by rw [hfl_n]; rfl, hun_n, huf_n, hoom_n, hct_n, hbcf_n, hdm_n, hcv_n,
                        hcl_n, hprob_n, halen_n, hfl_le, fun _ => hfl_s_lt, hpr_n ▸ hpr_ge_n,
                        htemc_le, hpr_temc, hsc_n, hd0_n, hm_mc⟩))
                  hcfg hext1 hw2b1 c.hwcap c.hmaxv hlen0 hpr_lt rfl (by rw [hfuel_eq]; rfl)
                  ⟨te_mem, rfl, htem_le, hpr_tem⟩ htr_o hperm_o hag_o hcv_o hcl_o hprob_o halen_o
                  hsc_o hfl_rem_dec hfuel_le hp1_prop (htend_eq ▸ hp_lt_o) hpr_ge rfl hnot_lt
                  hdm_o hpi_b hdi_b hdl_b hdok_b hd0_b hte_b hun_b huf_b
                  (fun h => let x := hbr0 h; ⟨x.1, fun _ => x.2.1⟩)
                  (fun h => absurd h (by decide)) (fun h => ⟨rfl, hbr1 h⟩)
                  hbr_cases hmb
              · rintro Bo Lo rem_o ⟨te_o, un_o, uf_o, tk_o, off_o, p_o, q_o, end_o, di_o, brk_o,
                    ovf_o, ⟨⟩⟩ mo hBo ih_o ⟨sem_o, dlen_o, rfl, hpi_o, hdi_o, hdl_o, hdok_o,
                    hd0_o, hte_o, hun_o, huf_o, hov_t, hov_f, hmo⟩
                s13_hsplit
                · have hov_t_eq : ovf_o = true := hc
                  have ⟨hbr0_o, hoom_o2, hct_o2⟩ := hov_t hov_t_eq
                  clear hov_t hov_f hc; s13_hsteps_nogrp
                  refine wp_join_group
                    (fun (te_p, un_p, uf_p, tk_p, p_p, q_p, di_p, brk_p, ovf_p,
                        ovf_rw_p, ovf_oth_p, ovf_cr_p, ovf_ri_p, ()) mbp =>
                      ∃ (sem_p : FullState) (dlen_p : Nat),
                        PropLitInv c F0 F_cur
                          { s_base with scratch :=
                            { s_base.scratch with delayed := sem_p.scratch.delayed } }
                          sem_p not_lit.toNat off_o.toNat q_p.toNat p_p.toNat end_o.toNat ∧
                        di_p.toNat = 3 * dlen_p ∧ dlen_p ≤ c.delayed_cap ∧
                        DelayedWatchesOk s_base.core sem_p.scratch.delayed dlen_p not_lit.toNat ∧
                        (c.delayed_cap = 0 → sem_p.scratch.delayed = s.scratch.delayed) ∧
                        p_o.toNat ≤ p_p.toNat ∧ sem_o.core.trail_end ≤ sem_p.core.trail_end ∧
                        te_p.toNat = sem_p.core.trail_end ∧ un_p = sem_p.core.unassigned ∧
                        uf_p = sem_p.core.unflushed ∧ sem_p.core.oom = 0#64 ∧
                        (ovf_p = false →
                          (brk_p = 0#64 → p_p = end_o ∧
                            S13ConflEq sem_o.core sem_p.core) ∧
                          (brk_p = 1#64 → PropLitConfl F_cur ignore_ref sem_p.core) ∧
                          (brk_p = 0#64 ∨ brk_p = 1#64)) ∧
                        (ovf_p = true → brk_p = 0#64 ∧
                          S13ConflEq sem_o.core sem_p.core ∧
                          2 ≤ p_p.toNat - off_o.toNat ∧ q_p.toNat + 2 ≤ p_p.toNat ∧
                          end_o.toNat - p_p.toNat < end_o.toNat - p_o.toNat ∧
                          ovf_cr_p.toNat < 0x80000000 ∧
                          ovf_cr_p.toNat ∈ fullArenaClauseRefsCore sem_p.core ∧
                          ovf_cr_p.toNat + 3 +
                            fullArenaClauseSizeCore sem_p.core ovf_cr_p.toNat ≤
                            sem_p.core.arena_len ∧
                          ovf_oth_p.toNat < 2 * sem_p.core.cur_vars ∧
                          ovf_rw_p.toNat < 2 * sem_p.core.cur_vars ∧
                          ovf_rw_p.toNat ≠ not_lit.toNat ∧ 2 ≤ ovf_ri_p.toNat ∧
                          ovf_ri_p.toNat < fullArenaClauseSizeCore sem_p.core ovf_cr_p.toNat ∧
                          ∃ l0' l1', (l0' = not_lit ∨ l1' = not_lit) ∧
                            ovf_oth_p = l0' ^^^ l1' ^^^ not_lit ∧
                            sem_p.core.arena[ovf_cr_p.toNat + 3]? = some l0' ∧
                            sem_p.core.arena[ovf_cr_p.toNat + 4]? = some l1' ∧
                            sem_p.core.arena[ovf_cr_p.toNat + 3 + ovf_ri_p.toNat]? =
                              some ovf_rw_p) ∧
                        (FullMem c (fastPropMem s_disk sem_p) ⋆
                          (m6ExtMem (m6ExtAddr c.hdr) ext1 ⋆ R)) mbp) ?_ ?_
                  · rintro _ ⟨te_p, un_p, uf_p, tk_p, p_p, q_p, di_p, brk_p, ovf_p,
                        ovf_rw_p, ovf_oth_p, ovf_cr_p, ovf_ri_p, ⟨⟩⟩ mbp
                      ⟨sem_p, dlen_p, hpi_p, hdi_p, hdl_p, hdok_p, hd0_p, hp_ge_o, _,
                        hte_p, hun_p, huf_p, hoom_p, hnoov, hov_yes, hmbp⟩
                    exact s13_ovf_post_join_case hOvf hFlush
                      (fun xs mb ⟨sem_b, dlen_b, h1, h2, h3, h4, h5, h6, h7, h8, h9, _, h10, h11,
                          h12⟩ =>
                        hBo xs mb ⟨sem_b, dlen_b, h1, h2, h3, h4, h5, h6, h7, h8,
                          fun h0 => let ⟨ha, hb, hc'⟩ := h9 h0; ⟨ha, hb rfl, hc'⟩,
                          fun h1 => (h10 h1).2, h11, h12⟩)
                      (fun n' xs m hlt ⟨sem_o', dlen_o', hn, ha, hb, hc', hd, he, hf, hg, hh, _,
                          hi, hj, hk⟩ =>
                        ih_o n' xs m (by simpa only [hov_t_eq, ↓reduceIte] using hlt)
                          ⟨sem_o', dlen_o', hn, ha, hb, hc', hd, he, hf, hg, hh,
                            fun ht => let ⟨ha', hb', hc''⟩ := hi ht; ⟨ha', hb', hc'' rfl⟩,
                            fun hf' => let ⟨ha', hb', hc''⟩ := hj hf'
                              ⟨fun h0 => let ⟨x, y, z⟩ := ha' h0; ⟨x, y rfl, z⟩,
                               fun h1 => (hb' h1).2, hc''⟩, hk⟩)
                      rfl ⟨te_mem, rfl, htem_le, hpr_tem⟩ hlen0 hlen_o hcv_o hnot_lt rfl hnl64_idx
                      (fun _ => hct_o2) (fun h => absurd h (by decide)) hpi_p hdi_p hdl_p hdok_p
                      hd0_p hp_ge_o hte_p hun_p huf_p hoom_p
                      (fun hf => let ⟨h0, h1, h2⟩ := hnoov hf
                        ⟨fun hx => ⟨(h0 hx).1, (h0 hx).2⟩,
                         fun h => ⟨rfl, h1 h⟩, h2⟩)
                      (fun ht => let ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13⟩ :=
                          hov_yes ht
                        ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13⟩)
                      hmbp
                  · intro J_ovf hJ_ovf
                    have hnot_o : not_lit.toNat < 2 * sem_o.core.cur_vars := by
                      rw [hpi_o.cur_vars_eq]; exact hnot_lt
                    have hcl32_o : sem_o.core.cur_level < 2 ^ 32 := by
                      rw [hpi_o.ag.get FullCoreState.cur_level]; dsimp only [s_base]
                      rw [hcl_o]; exact hclv_lt32
                    refine s13_lp_loop_wp (isBeyond := false) (ignore_ref := .var ignore_ref)
                      c.hmaxv c.harena c.hwcap
                      rfl hpi_o hnot_o ?_ ?_
                      hcl32_o hte_o hun_o huf_o hoom_o2 hbr0_o hnl_sbase hdi_o hdl_o hdlim_toNat
                      hdok_o (fun h0 => (hd0_o h0).trans (hd0_sem h0).symm) hmo ?_
                    · rw [hpi_o.cur_vars_eq]; dsimp only [s_base]; rw [hcv_o]
                      simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]
                      rw [Nat.mod_eq_of_lt hcv_lt64, show (OfNat.ofNat 1 : Nat) = 1 from rfl,
                        Nat.shiftLeft_eq, Nat.pow_one, Nat.mul_comm s.core.cur_vars 2,
                        Nat.mod_eq_of_lt h2cv_lt64]
                    · rw [hpi_o.ag.get FullCoreState.cur_level]; dsimp only [s_base]; rw [hcl_o]
                      apply BitVec.eq_of_toNat_eq
                      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat,
                        Nat.mod_eq_of_lt hclv_lt32, Nat.mod_eq_of_lt hclv_lt64]
                    · intro sem' te' un' uf' tk' p' q' di' brk' ovf' ovf_rw' ovf_oth' ovf_cr'
                        ovf_ri' dlen' m' hpi' hdi' hdl' hdok' hd0' hp' hte_ge' hte' hun' huf' hoom'
                        hno' hyes' hm'
                      s13_hsteps
                      exact hJ_ovf _ m' ⟨sem', dlen', hpi', hdi', hdl', hdok',
                        fun h0 => (hd0' h0).trans (hd0_sem h0), hp', hte_ge', hte', hun', huf',
                        hoom', (fun hf => let ⟨h0, h1, h2⟩ := hno' hf
                          ⟨fun hx => ⟨(h0 hx).1, (h0 hx).2⟩, fun hb => (h1 hb).2, h2⟩),
                        (fun h => let ⟨a1, a2, a3, a4, a5, a6, a7, _, a8⟩ := hyes' h
                          ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩), hm'⟩
                · have hov_f_eq : ovf_o = false := by revert hc; cases ovf_o <;> simp
                  have ⟨h0, h1, hcs⟩ := hov_f hov_f_eq
                  exact hBo _ mo ⟨sem_o, dlen_o, hpi_o, hdi_o, hdl_o, hdok_o, hd0_o, hte_o, hun_o,
                    huf_o, h0, h1, hcs.elim Or.inl (fun h => Or.inr (Or.inl h)), hmo⟩
              · intro Bo Lo hBo hLo
                s13_hsteps
                simp only [fastPropMem_wvec]
                refine s13_outer_sz_nz_lo_pack (isBeyond := false) (ign_v := ignore_ref)
                  (s_disk := s_disk) (sem_d := sem_d)
                  (fun rem xs m ⟨sem_o', dlen_o', a, b, c1, d, e, f, g, h1, i, _, ht, hf, hm'⟩ =>
                    hLo rem xs m ⟨sem_o', dlen_o', a, b, c1, d, e, f, g, h1, i,
                      (fun htrue => let ⟨x, y, z⟩ := ht htrue; ⟨x, y, z rfl⟩),
                      (fun hfalse => let ⟨h0, h1', hor⟩ := hf hfalse
                        ⟨fun hh0 => let ⟨x, y, z⟩ := h0 hh0; ⟨x, y rfl, z⟩,
                         fun hh1 => (h1' hh1).2, hor⟩),
                      hm'⟩)
                  rfl hd0_sem htend_eq hunass_eq hunfl_eq hoom_o hct_o
                  (fun h => absurd h (by decide))
                  (fastPropMem_trl s_disk sem_d)
                  hp_sem_lt_trl hlit_trl rfl hnl64_idx hnl64_1_idx hnl64_lt_wv0 hnl64_1_lt_wv0
                  hoff0_nat hsz0_nat hend0_lt64 hpi0 hm_base
        · have hpe_o : sem.core.propagated = sem.core.trail_end := by
            have hh : tend_v.toNat ≤ prop_v.toNat := Nat.le_of_not_lt hc
            rw [← htend_eq, ← hprop_eq] at hh; exact Nat.le_antisymm hlen_o.core_ok.propagated_le hh
          have hprop_gt : s.core.propagated < prop_v.toNat := by
            rw [← hprop_eq, hpe_o]; exact Nat.lt_of_lt_of_le hpr_lt htr_o.1
          have hfuel_dec := hfuel_lt hprop_gt
          clear ih; s13_hsteps_nogrp; (try dsimp only)
          exact s13_outer_flush_ret
            (sem := { sem with scratch := { sem.scratch with
              search_ticks := s.scratch.search_ticks } })
            hAddTicks hQ' hcfg hext1 hw2b1
            ⟨hlen_o.core_ok,
              { hlen_o.scratch_ok with phases_len := hlen_o.scratch_ok.phases_len }⟩
            hw_o htr_o hperm_o
            hag_o (by dsimp only; rw [hsc_o]) hd0_sem hprop_eq htend_eq hfuel_eq hunass_eq hunfl_eq
            hfuel_le hpr_lt (Or.inl rfl) hbcf_o
            (fun _ => ⟨hprop_eq ▸ htend_eq ▸ hpe_o, hct_o, fun _ => hoom_o, fun _ => hfuel_dec⟩)
            (fun _ => by decide) (fun h => absurd h (by decide))
            (fullM6HdrMem_unfocus_full (by simpa only [fastPropMem, s_disk, sem_d, hprop_eq,
              htend_eq, hunass_eq, hunfl_eq, hfuel_eq] using hm))
      · intro J hJ; s13_hsteps
        exact hJ s.core.fuel.toNat (BitVec.ofNat 64 s.core.propagated,
            BitVec.ofNat 64 s.core.trail_end, s.core.fuel, s.core.unassigned, s.core.unflushed,
            0#64, ()) m
          (s13_outer_init_inv hlen0 hext0 hw0 hdense0 hoom0 hpr0_lt64 hte0_lt64 hm_wm4)

theorem s13_ovf_loop_wp {Γ : Env} {isBeyond rec_ph bigbig : Bool} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {ext0 ext1 : List (BitVec 64)}
    {s sem s_base s_disk : FullState}
    {cur_lvl32 not_lit nl_lvl : BitVec 32}
    {ignore_ref : Arg Val i64} {ign_v : BitVec 64}
    {prop_v tend_v fuel_v fuel1 unass_v unfl_v ticks1 nl64 two_cv dlim off0 end0 : BitVec 64}
    {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost} {ml : Mem 64}
    {J_out : Cont [i64, i64, i64, i64, i64, i64]}
    (hOvf : ∀ args m Q X, FullM7BcpHot.fullPropLitOvfHotSpec args m Q X →
      Γ "full_prop_lit_ovf_hot" [i64, i32, i32, i32] [.bool] args m Q X)
    (hFlush : ∀ args m Q X, fidPropFlushDelSpec args m Q X →
      Γ "full_prop_flush_del_fid" [i64, i64] [.bool] args m Q X)
    (hAddTicks : ∀ args m Q X, step13AddTicksSpec args m Q X →
      Γ "m6_hdr_add_ticks" [i64, i64] [] args m Q X)
    (hQ : S13HQ isBeyond c F0 F_cur ext0 s ign_v R Q)
    (hJ_out : ∀ rem_n (xs_n : Tup (Arg Val) [i64, i64, i64, i64, i64, i64]) mc0,
      rem_n < sem.core.fuel.toNat →
      S13OuterInv isBeyond c F0 F_cur ext0 s R rem_n xs_n.1.val xs_n.2.1.val xs_n.2.2.1.val
        xs_n.2.2.2.1.val xs_n.2.2.2.2.1.val xs_n.2.2.2.2.2.1.val mc0 →
      wp Γ Q X (Expr.jump J_out xs_n) mc0)
    (hcfg : FullM6HdrCfgOk c) (hext1 : M6HdrExtOk ext1)
    (hw2b1 : M6HdrExtInitOk ext0 → M6HdrExtInitOk ext1 ∧ M6ExtW2bPres ext0 ext1)
    (hlen0 : s.LengthsOk c) (hpr_lt : s.core.propagated < s.core.trail_end)
    (hs_base : s_base = { sem with core := { sem.core with
      propagated := s.core.propagated, fuel := s.core.fuel } })
    (hfuel_eq : sem.core.fuel = fuel_v) (hfuel1 : fuel1 = fuel_v - 1#64)
    (hprop_eq : sem.core.propagated = prop_v.toNat) (htend_eq : sem.core.trail_end = tend_v.toNat)
    (hunass_eq : sem.core.unassigned = unass_v) (hunfl_eq : sem.core.unflushed = unfl_v)
    (hs_disk : ∃ te_mem, s_disk = { s with core := { s.core with trail_end := te_mem } } ∧
      te_mem ≤ sem.core.trail_end ∧ s.core.propagated ≤ te_mem)
    (hlen_o : sem.LengthsOk c) (hw_o : FullWitnessInv c F0 F_cur sem.core)
    (htr_o : FullTrailExt s.core sem.core) (hperm_o : FullArenaPermEq s.core sem.core)
    (hag_o : AgreesExcept fidCoreMask s.core sem.core)
    (hoom_o : sem.core.oom = 0#64)
    (hct_o : isBeyond = false → sem.core.confl_type = s.core.confl_type)
    (hbcf_o : isBeyond = true → S13ConflEq s.core sem.core)
    (hdm_o : sem.core.dense_mode = 0#64)
    (hcv_o : sem.core.cur_vars = s.core.cur_vars) (hcl_o : sem.core.cur_level = s.core.cur_level)
    (hprob_o : sem.core.probing = s.core.probing) (halen_o : sem.core.arena_len = s.core.arena_len)
    (hsc_o : S13Scr s sem) (hd0_sem : c.delayed_cap = 0 → sem.scratch.delayed = s.scratch.delayed)
    (hfl_rem_dec : (sem.core.fuel - 1#64).toNat < sem.core.fuel.toNat)
    (hfuel_le : sem.core.fuel.toNat ≤ s.core.fuel.toNat)
    (hp1_prop : (prop_v + 1#64).toNat = prop_v.toNat + 1)
    (hp_lt_o : prop_v.toNat < tend_v.toNat) (hpr_ge : s.core.propagated ≤ prop_v.toNat)
    (hign_val : ignore_ref.val = ign_v)
    (hnot_lt : not_lit.toNat < 2 * sem.core.cur_vars)
    (htwo_cv : two_cv.toNat = 2 * sem.core.cur_vars)
    (hcur_lvl : cur_lvl32 = BitVec.ofNat 32 sem.core.cur_level)
    (hcl32 : sem.core.cur_level < 2 ^ 32)
    (hnl64 : nl64 = not_lit.setWidth 64 <<< (1 : Nat)) (hnl64_idx : nl64.toNat = 2 * not_lit.toNat)
    (hnl_sbase : ∀ k : FullCoreState, FullPropDecSpecs.FullTrailExt s_base.core k →
      k.lvl[not_lit.toNat / 2]?.getD 0#32 = nl_lvl)
    (hdlim : dlim.toNat = 3 * c.delayed_cap)
    (hoff0 : off0.toNat = fullWatchOffCore s_base.core not_lit.toNat)
    (hend0 : end0 = off0 + BitVec.ofNat 64 (fullWatchSizeCore s_base.core not_lit.toNat))
    (hend0_nat : end0.toNat =
      fullWatchOffCore s_base.core not_lit.toNat + fullWatchSizeCore s_base.core not_lit.toNat)
    (hpi0 : PropLitInv c F0 F_cur s_base s_base not_lit.toNat off0.toNat off0.toNat off0.toNat
      end0.toNat)
    (hm : (FullMem c (fastPropMem s_disk s_base) ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext1 ⋆ R)) ml) :
    wp Γ Q X (s13OvfLoopExpr c isBeyond J_out dlim ignore_ref two_cv cur_lvl32 not_lit nl_lvl
      rec_ph bigbig nl64 prop_v fuel1 tend_v unass_v unfl_v ticks1 off0 end0) ml := by
  let _ := hprop_eq; let _ := hw_o; let _ := hend0
  have hsd_len : s_disk.LengthsOk c := by
    obtain ⟨te_mem, hs_d, htm, hpt⟩ := hs_disk
    subst hs_d; exact ⟨{ hlen0.core_ok with
      trail_end_le := Nat.le_trans htm (hcv_o ▸ hlen_o.core_ok.trail_end_le),
      propagated_le := hpt }, hlen0.scratch_ok⟩
  have hdense_b : s_base.core.dense_mode = 0#64 := by rw [hs_base]; exact hdm_o
  unfold s13OvfLoopExpr
  refine wp_loop_break_group
    (fun (te_b, un_b, uf_b, tk_b, off_b, p_b, q_b, end_b, di_b, brk_b, _ovf_b, ()) mb =>
      ∃ (sem_b : FullState) (dlen_b : Nat),
        PropLitInv c F0 F_cur
          { s_base with scratch := { s_base.scratch with delayed := sem_b.scratch.delayed } }
          sem_b not_lit.toNat off_b.toNat q_b.toNat p_b.toNat end_b.toNat ∧
        di_b.toNat = 3 * dlen_b ∧ dlen_b ≤ c.delayed_cap ∧
        DelayedWatchesOk s_base.core sem_b.scratch.delayed dlen_b not_lit.toNat ∧
        (c.delayed_cap = 0 → sem_b.scratch.delayed = s.scratch.delayed) ∧
        te_b.toNat = sem_b.core.trail_end ∧ un_b = sem_b.core.unassigned ∧
        uf_b = sem_b.core.unflushed ∧
        (brk_b = 0#64 → sem_b.core.oom = 0#64 ∧
          (isBeyond = false → sem_b.core.confl_type = s.core.confl_type) ∧ p_b = end_b) ∧
        (isBeyond = true → S13ConflEq s.core sem_b.core) ∧
        (brk_b = 1#64 → isBeyond = false ∧ PropLitConfl F_cur ign_v sem_b.core ∧
          sem_b.core.oom = 0#64) ∧
        (if isBeyond then (brk_b = 0#64 ∨ brk_b = 2#64)
         else (brk_b = 0#64 ∨ brk_b = 1#64 ∨ brk_b = 2#64)) ∧
        (FullMem c (fastPropMem s_disk sem_b) ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext1 ⋆ R)) mb)
    (fun rem_o o mo =>
      ∃ te_o un_o uf_o tk_o off_o p_o q_o end_o di_o brk_o ovf_o,
        o = s13LoTup isBeyond (te_o, un_o, uf_o, tk_o, off_o, p_o, q_o, end_o, di_o, brk_o,
          ovf_o, ()) ∧
        (isBeyond = true → brk_o = 0#64) ∧
        ∃ (sem_o : FullState) (dlen_o : Nat),
          rem_o = (end_o.toNat - p_o.toNat) + (if ovf_o then 1 else 0) ∧
          PropLitInv c F0 F_cur
            { s_base with scratch := { s_base.scratch with delayed := sem_o.scratch.delayed } }
            sem_o not_lit.toNat off_o.toNat q_o.toNat p_o.toNat end_o.toNat ∧
          di_o.toNat = 3 * dlen_o ∧ dlen_o ≤ c.delayed_cap ∧
          DelayedWatchesOk s_base.core sem_o.scratch.delayed dlen_o not_lit.toNat ∧
          (c.delayed_cap = 0 → sem_o.scratch.delayed = s.scratch.delayed) ∧
          te_o.toNat = sem_o.core.trail_end ∧ un_o = sem_o.core.unassigned ∧
          uf_o = sem_o.core.unflushed ∧
          (isBeyond = true → S13ConflEq s.core sem_o.core) ∧
          (ovf_o = true → brk_o = 0#64 ∧ sem_o.core.oom = 0#64 ∧
            (isBeyond = false → sem_o.core.confl_type = s.core.confl_type)) ∧
          (ovf_o = false →
            (brk_o = 0#64 → sem_o.core.oom = 0#64 ∧
              (isBeyond = false → sem_o.core.confl_type = s.core.confl_type) ∧ p_o = end_o) ∧
            (brk_o = 1#64 → isBeyond = false ∧ PropLitConfl F_cur ign_v sem_o.core ∧
              sem_o.core.oom = 0#64) ∧
            (brk_o = 0#64 ∨ brk_o = 1#64)) ∧
          (FullMem c (fastPropMem s_disk sem_o) ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext1 ⋆ R)) mo)
    ?_ ?_ ?_
  · rintro _ ⟨te_b, un_b, uf_b, tk_b, off_b, p_b, q_b, end_b, di_b, brk_b, ovf_b, ⟨⟩⟩ mb
      ⟨sem_b, dlen_b, hpi_b, hdi_b, hdl_b, hdok_b, hd0_b, hte_b, hun_b, huf_b, hbr0, hbr_cf,
        hbr1, hbr_cases, hmb⟩
    exact s13_compact_post_wp hFlush hAddTicks hQ
      (fun sem_next te_mc mc0 hlen_n hw_n htr_n hperm_n hag_n hpr_n hfl_n hte_n hun_n huf_n
        hoom_n hct_n hbcf_n hdm_n hcv_n hcl_n hprob_n halen_n hfl_sem_lt hfl_s_lt hfl_le hpr_ge_n
        htemc_le hpr_temc hsc_n hd0_n hm_mc =>
        hJ_out sem_next.core.fuel.toNat (Arg.var (prop_v + 1#64), Arg.var te_b, Arg.var fuel1,
          Arg.var un_b, Arg.var uf_b, Arg.var tk_b, ()) mc0
          hfl_sem_lt (s13OuterInv_mk ⟨ext1, sem_next, te_mc, rfl, hext1, hw2b1, hlen_n, hw_n,
            htr_n, hperm_n, hag_n, hpr_n, hte_n, hfl_n, hun_n, huf_n, hoom_n, fun hb => hct_n hb,
            hbcf_n, hdm_n, hcv_n, hcl_n, hprob_n, halen_n, hfl_le, fun _ => hfl_s_lt,
            hpr_n ▸ hpr_ge_n, htemc_le, hpr_temc, hsc_n, hd0_n, hm_mc⟩))
      hcfg hext1 hw2b1 c.hwcap c.hmaxv hlen0 hpr_lt hs_base (hfuel_eq.symm ▸ hfuel1) hs_disk htr_o
      hperm_o hag_o hcv_o hcl_o hprob_o halen_o hsc_o hfl_rem_dec hfuel_le hp1_prop
      (htend_eq ▸ hp_lt_o) hpr_ge hnl64 hnot_lt hdense_b hpi_b hdi_b hdl_b hdok_b hd0_b hte_b
      hun_b huf_b (fun h => let x := hbr0 h; ⟨x.1, x.2.1⟩) hbr_cf hbr1 hbr_cases hmb
  · rintro Bo Lo rem_o o mo hBo ih_o ⟨te_o, un_o, uf_o, tk_o, off_o, p_o, q_o, end_o, di_o,
      brk_o, ovf_o, rfl, hbrk_ib, sem_o, dlen_o, rfl, hpi_o, hdi_o, hdl_o, hdok_o, hd0_o,
      hte_o, hun_o, huf_o, hbcf_o2, hov_t, hov_f, hmo⟩
    have hih' : ∀ rem xs m, rem < (end_o.toNat - p_o.toNat) + (if ovf_o then 1 else 0) →
        (∃ (sem_o' : FullState) (dlen_o' : Nat),
          (isBeyond = true → xs.2.2.2.2.2.2.2.2.2.1 = 0#64) ∧
          rem = (xs.2.2.2.2.2.2.2.1.toNat - xs.2.2.2.2.2.1.toNat) +
            (if xs.2.2.2.2.2.2.2.2.2.2.1 then 1 else 0) ∧
          PropLitInv c F0 F_cur
            { s_base with scratch := { s_base.scratch with delayed := sem_o'.scratch.delayed } }
            sem_o' not_lit.toNat xs.2.2.2.2.1.toNat xs.2.2.2.2.2.2.1.toNat
            xs.2.2.2.2.2.1.toNat xs.2.2.2.2.2.2.2.1.toNat ∧
          xs.2.2.2.2.2.2.2.2.1.toNat = 3 * dlen_o' ∧ dlen_o' ≤ c.delayed_cap ∧
          DelayedWatchesOk s_base.core sem_o'.scratch.delayed dlen_o' not_lit.toNat ∧
          (c.delayed_cap = 0 → sem_o'.scratch.delayed = s.scratch.delayed) ∧
          xs.1.toNat = sem_o'.core.trail_end ∧ xs.2.1 = sem_o'.core.unassigned ∧
          xs.2.2.1 = sem_o'.core.unflushed ∧
          (isBeyond = true → S13ConflEq s.core sem_o'.core) ∧
          (xs.2.2.2.2.2.2.2.2.2.2.1 = true → xs.2.2.2.2.2.2.2.2.2.1 = 0#64 ∧
            sem_o'.core.oom = 0#64 ∧
            (isBeyond = false → sem_o'.core.confl_type = s.core.confl_type)) ∧
          (xs.2.2.2.2.2.2.2.2.2.2.1 = false →
            (xs.2.2.2.2.2.2.2.2.2.1 = 0#64 → sem_o'.core.oom = 0#64 ∧
              (isBeyond = false → sem_o'.core.confl_type = s.core.confl_type) ∧
              xs.2.2.2.2.2.1 = xs.2.2.2.2.2.2.2.1) ∧
            (xs.2.2.2.2.2.2.2.2.2.1 = 1#64 → isBeyond = false ∧
              PropLitConfl F_cur ign_v sem_o'.core ∧ sem_o'.core.oom = 0#64) ∧
            (xs.2.2.2.2.2.2.2.2.2.1 = 0#64 ∨ xs.2.2.2.2.2.2.2.2.2.1 = 1#64)) ∧
          (FullMem c (fastPropMem s_disk sem_o') ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext1 ⋆ R)) m) →
        Lo (s13LoTup isBeyond xs) m := fun rem xs m hlt ⟨sem_o', dlen_o', hbr_ib, rest⟩ =>
      ih_o rem (s13LoTup isBeyond xs) m hlt ⟨xs.1, xs.2.1, xs.2.2.1, xs.2.2.2.1, xs.2.2.2.2.1,
        xs.2.2.2.2.2.1, xs.2.2.2.2.2.2.1, xs.2.2.2.2.2.2.2.1, xs.2.2.2.2.2.2.2.2.1,
        xs.2.2.2.2.2.2.2.2.2.1, xs.2.2.2.2.2.2.2.2.2.2.1, rfl, hbr_ib, sem_o', dlen_o', rest⟩
    cases isBeyond
    · exact s13_ovf_loop_body_wp hOvf hFlush hcfg hlen0 hs_base hs_disk hlen_o hcv_o hd0_sem
        hign_val hnot_lt htwo_cv hcl32 hcur_lvl hnl64 hnl64_idx hnl_sbase hdlim hBo hih'
        hbrk_ib hpi_o hdi_o hdl_o hdok_o hd0_o hte_o hun_o huf_o hbcf_o2 hov_t hov_f hmo
    · obtain rfl := hbrk_ib rfl
      exact s13_ovf_loop_body_wp hOvf hFlush hcfg hlen0 hs_base hs_disk hlen_o hcv_o hd0_sem
        hign_val hnot_lt htwo_cv hcl32 hcur_lvl hnl64 hnl64_idx hnl_sbase hdlim hBo hih'
        hbrk_ib hpi_o hdi_o hdl_o hdok_o hd0_o hte_o hun_o huf_o hbcf_o2 hov_t hov_f hmo
  · intro Bo Lo hBo hLo
    cases isBeyond <;>
    · s13_hsteps
      refine hLo (fullWatchSizeCore s_base.core not_lit.toNat + 1) _ ml
        ⟨tend_v, unass_v, unfl_v, ticks1, off0, off0, off0, end0, 0#64, 0#64, true, rfl,
          fun _ => rfl, s_base, 0,
          by simp only [↓reduceIte, hend0_nat, hoff0, Nat.add_sub_cancel_left],
          hpi0, rfl, Nat.zero_le _, fun _ h => absurd h (Nat.not_lt_zero _),
          by rw [hs_base]; exact hd0_sem, by rw [hs_base]; exact htend_eq.symm,
          by rw [hs_base]; exact hunass_eq.symm, by rw [hs_base]; exact hunfl_eq.symm,
          (fun hb => by rw [hs_base]; exact hbcf_o hb),
          fun _ => ⟨rfl, by rw [hs_base]; exact hoom_o, fun hb => by rw [hs_base]; exact hct_o hb⟩,
          fun h => absurd h (by decide), hm⟩

/-- Parametric Step-13 WP proof for `full_propagate_ignore_body`
(`= full_propagate_ignore_hot_body`). -/
theorem full_propagate_ignore_step13_wp (Γ : Env)
    (hWm4Get : ∀ args m Q X, step13Wm4GetSpec args m Q X →
      Γ "m6_wm4_get" [i64] [i64] args m Q X)
    (hAddTicks : ∀ args m Q X, step13AddTicksSpec args m Q X →
      Γ "m6_hdr_add_ticks" [i64, i64] [] args m Q X)
    (hOvf : ∀ args m Q X, FullM7BcpHot.fullPropLitOvfHotSpec args m Q X →
      Γ "full_prop_lit_ovf_hot" [i64, i32, i32, i32] [.bool] args m Q X)
    (hFlush : ∀ args m Q X, fidPropFlushDelSpec args m Q X →
      Γ "full_prop_flush_del_fid" [i64, i64] [.bool] args m Q X) :
    ∀ args m Q X, step13PropagateIgnoreM6Spec args m Q X →
      Func.wp Γ full_propagate_ignore_body args m Q X := by
  rw [full_propagate_ignore_body_eq_hot]
  exact full_propagate_ignore_hot_step13_wp Γ hWm4Get hAddTicks hOvf hFlush

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S2

end