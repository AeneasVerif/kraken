/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM8SweepV2
public import LeanQbe.T.Examples.Kissat.FullM8FidV12Proof
public import LeanQbe.T.Examples.Kissat.FullM8SweepV2VarProof
public import LeanQbe.T.Examples.Kissat.FullM6SweepProofDriver
import all LeanQbe.T.Examples.Kissat.FullM7FidelityAssembly
import all LeanQbe.T.Examples.Kissat.FullM7FidelityAssemblyProof0
import all LeanQbe.T.Examples.Kissat.FullM7FidelityAssemblyProof
import all LeanQbe.T.Examples.Kissat.FullM8FidV12
import all LeanQbe.T.Examples.Kissat.FullM8FidV12Proof
import all LeanQbe.T.Examples.Kissat.FullM8SweepV2
import all LeanQbe.T.Examples.Kissat.FullM6SweepProofSpec
import all LeanQbe.T.Examples.Kissat.FullM6Orch
import all LeanQbe.T.Examples.Kissat.FullM6CompactFlush
import LeanQbe.T.Examples.Kissat.FullM6CompactFlushProof1
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb

/-!
# Kissat M8 Tier B Revived Sweep (`V12 + V3t2`) — `ModuleOk` & Soundness (`FullM8SweepV2Proof`)

Packages the closed environment `m8FidV123t2Env` and proves `449/449` `ModuleOk`
(`m8FidV123t2_moduleOk`), top-level `kissat_solve_bytes` soundness (`m8FidV123t2_solve_bytes_sound`,
`m8FidV123t2_solve_bytes_host_sound`), and concrete deterministic UNSAT non-vacuity
(`m8FidV123t2_unsat_nv`) for `FullM8SweepV2.m8FidV123t2Module` (`V12` + revived `V3t2` sweep).

Zero edits to any existing `FullM4*`–`FullM7*`, `FullM8FidV12*`, `Opt`, `Rega`, `Spill`, or cert
modules (`std3` axioms only).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM8SweepV2

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open Kraken.Bedrock2.Test
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM4Sweep
open LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM6CompactFlush
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM6Sweep
open LeanQbe.T.Examples.Kissat.FullM7
open LeanQbe.T.Examples.Kissat.FullM7Fidelity
open LeanQbe.T.Examples.Kissat.FullM7Proof
open LeanQbe.T.Examples.Kissat.FullM7Splice
open LeanQbe.T.Examples.Kissat.FullM8FidV12
open scoped Full.FullArenaTactics

/-! ## 1. `36`-Row Revived-Sweep Table & Closed `M8FidV123t2Env` -/

/-- Name excluded from `m8FidV12Env` forwarding so `"full_extend_push2"` uses stronger
`FullM6Sweep.m6ExtendPush2Spec` (preserving `tarjan_reach` and `work_stk1` for `full_m6_els_fold`).
-/
def m8SwExclNames : List Sym := ["full_extend_push2"]

/-- Exact `36`-row specification slice for the revived `FullM8SweepV2` helpers (`0..35`),
identical in order and contracts to `m6SweepSpecTable.take 36`. -/
def m8SweepEnvRows : List SpecEntry := FullM6Sweep.m6SweepSpecTable.take 36

/-- Closed environment extending `m8FidV12Env` with strengthened `m6ExtendPush2Spec` and the
`36` revived sweep helpers (`m8SweepEnvRows`). -/
inductive M8FidV123t2Env (Γ : Env) : Env where
  | base {f as bs xs m Q X} :
      f ∉ m8SwExclNames → Γ f as bs xs m Q X → M8FidV123t2Env Γ f as bs xs m Q X
  | extPush2 {a m Q X} :
      m6ExtendPush2Spec a m Q X →
      M8FidV123t2Env Γ "full_extend_push2" [i64, i32, i32] [.bool] a m Q X
  | sweep {f as bs xs m Q X} :
      Env.ofTable m8SweepEnvRows f as bs xs m Q X →
      M8FidV123t2Env Γ f as bs xs m Q X

/-- Canonical closed `Env` for `m8FidV123t2Module` (`449` fns, `0` hooks, zero cert churn). -/
def m8FidV123t2Env : Env := M8FidV123t2Env m8FidV12Env

theorem m8SweepEnvRows_nodup : (m8SweepEnvRows.map SpecEntry.name).Nodup := by
  decide

theorem m8SweepEnvRows_noExit : ∀ e ∈ m8SweepEnvRows, e.noExit = true := by
  intro e he
  exact List.all_eq_true.mp (by t_kernel_rfl : m8SweepEnvRows.all (·.noExit) = true) e he

private theorem m8Sw_ofTable_name_mem {nm : Sym} {as bs : List Ty} {xs : Tup Val as}
    {m : Mem 64} {Q : Post bs} {X : XPost} :
    ∀ {tbl : List SpecEntry},
    Env.ofTable tbl nm as bs xs m Q X → nm ∈ tbl.map SpecEntry.name
  | [], h => False.elim h
  | e :: _, h => by
    by_cases hnm : e.name = nm
    · rw [← hnm]; exact List.mem_cons_self
    · rw [Env.ofTable_cons_ne hnm] at h
      exact List.mem_cons_of_mem _ (m8Sw_ofTable_name_mem h)

private theorem m8Sw_ofTable_sig_elim {tbl : List SpecEntry}
    (hnd : (tbl.map SpecEntry.name).Nodup) {e : SpecEntry} (he : e ∈ tbl)
    {as bs : List Ty} {xs : Tup Val as} {m : Mem 64} {Q : Post bs} {X : XPost}
    (h : Env.ofTable tbl e.name as bs xs m Q X) :
    ∃ (has : e.as = as) (hrs : e.rs = bs), e.cast has hrs xs m Q X := by
  induction tbl with
  | nil => nomatch he
  | cons hd tl ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    rcases List.mem_cons.mp he with rfl | htl
    · dsimp only [Env.ofTable] at h
      rcases h with ⟨⟨_, has, hrs⟩, hcast⟩ | ⟨_, htl'⟩
      · exact ⟨has, hrs, hcast⟩
      · exact absurd (m8Sw_ofTable_name_mem htl') (by simpa [List.mem_map] using hnd.1)
    · have hne : hd.name ≠ e.name := fun hEq => hnd.1 ⟨e, htl, hEq.symm⟩
      rw [Env.ofTable_cons_ne hne] at h
      exact ih hnd.2 htl h

private def m8SwNamesLit : List String :=
  [ "full_m6_max_v", "full_k6_add_ticks", "full_k6_init", "full_k6_watch", "full_k6_assign"
  , "full_k6_add_clause", "full_k6_mtf", "full_k6_backtrack", "full_k6_propagate"
  , "full_k6_ana_clause", "full_k6_analyze", "full_k6_solve", "full_k6_flip"
  , "full_k512_add_live_m6", "full_m6_dense_prop_lit", "full_m6_dense_prop"
  , "full_m6_sweep_cone", "full_m6_sweep_refine_sig", "full_m6_sweep_rand_phases"
  , "full_m6_sweep_solve", "full_m6_sweep_flip_round", "full_m6_sweep_sim"
  , "full_m6_sweep_rearm", "full_m6_sweep_build_pht", "full_m6_extract_pht"
  , "full_m6_refine_partition", "full_m6_sweep_units", "full_m6_sweep_classes"
  , "full_m6_els_ar", "full_m6_els_lit", "full_m6_els_fold", "full_m6_dense_els"
  , "full_m6_sweep_var", "full_m6_cand_sift", "full_m6_collect_cands", "full_m6_sweep_vars" ]

private theorem m8SweepEnvRows_names_eq :
    m8SweepEnvRows.map SpecEntry.name = m8SwNamesLit := by
  rfl

private def m8MfExtraNamesLit : List String :=
  [ "m6_hdr_init", "m6_ext_ensure_init", "full_prop_lit_ovf_hot", "full_prop_chrono_hot"
  , "full_has_bin", "full_min_mark", "full_ana_sift_m6", "full_sort_ana_qs_m6"
  , "full_sort_tmp_sift_m7", "full_sort_tmp_heap_m7", "full_sort_tmp"
  , "full_min_lit_dfs_m6", "full_shrink_lower_m6", "full_shrink_blk_bool_m6"
  , "full_walk_cb_inv_m7", "full_walk_init_table_m7", "full_walk_effort_m7"
  , "full_walk_init_vals_m7", "full_walk_collect_m7", "full_walk_build_occ_m7"
  , "full_walk_break_m7", "full_walk_pick_m7", "full_walk_flip_m7", "full_walk_save_min_m7"
  , "full_warmup_m7", "full_add_bin_m6"
  , "full_viv_unreason_m6", "full_viv_watch_rank_m6", "full_viv_best_watch_m6"
  , "full_viv_simplify_m6", "full_viv_commit_m6", "full_viv_mark_garb_m6"
  , "full_viv_subsumes_bin_m6", "full_viv_subsumes_cl_m6", "full_viv_deduce_m6"
  , "full_viv_best_implied_m6", "full_viv_reestablish_m6", "full_viv_inst_check_m6"
  , "full_viv_inst_m6", "full_viv_finish_m6", "full_viv_sort_counts_m6"
  , "full_viv_has_l0_m6", "full_viv_l0_simp_m6", "full_viv_reuse_prefix_m6"
  , "full_viv_clause_m6", "full_viv_tier_match_m6", "full_viv_collect_m6"
  , "full_viv_count_m6", "full_viv_keys_m6", "full_viv_sort_sched_m6"
  , "full_viv_clear_tier_m6"
  , "full_vivify_tier_m6_hdr", "full_compact_needed", "full_walk_m7"
  , "full_bump_analyzed_m6_hdr", "full_walk_warmup_m7", "full_walk"
  , "full_bva_match_large_fid", "full_reorder_sift_fid", "m6_hdr_decide_fid" ]

private theorem m8MfExtra_names_eq :
    mfExtraRows.map SpecEntry.name = m8MfExtraNamesLit := by
  rfl

private theorem m8Sw_disj_v12Fns :
    m8SwNamesLit.all
      (fun nm => !((m8FidV12Module.fns.map Fn.name).any (· == nm))) = true := by
  t_kernel_rfl

private theorem m8Sw_disj_m7Base :
    m8SwNamesLit.all
      (fun nm => !((m7Fns.map Fn.name).any (· == nm))) = true := by
  t_kernel_rfl

private theorem m8Sw_disj_extra :
    m8SwNamesLit.all
      (fun nm => !(m8MfExtraNamesLit.any (· == nm))) = true := by
  decide

private theorem m8Sw_not_mem_v12 {g : Fn} (hg : g ∈ m8FidV12Module.fns) :
    g.name ∉ m8SweepEnvRows.map SpecEntry.name := by
  rw [m8SweepEnvRows_names_eq]
  intro hm
  have h1 := List.all_eq_true.mp m8Sw_disj_v12Fns g.name hm
  simp only [Bool.not_eq_true', List.any_eq_false, List.mem_map, beq_iff_eq] at h1
  exact h1 g.name ⟨g, hg, rfl⟩ rfl

private theorem m8Sw_not_in_v12Env {nm : Sym} {as bs : List Ty} {xs : Tup Val as}
    {m : Mem 64} {Q : Post bs} {X : XPost} (hmem : nm ∈ m8SwNamesLit)
    (hv12 : m8FidV12Env nm as bs xs m Q X) : False := by
  cases hv12 with
  | base hm7 =>
    cases hm7 with
    | base _ hb =>
      have hnm_m7 : nm ∈ m7FidBaseTable.map SpecEntry.name := m8Sw_ofTable_name_mem hb
      have hsig := congrArg (List.map Prod.fst) m7FidBaseTable_sigs
      simp only [List.map_map, Function.comp_def, Fn.sig] at hsig
      change nm ∈ m7FidBaseTable.map SpecEntry.name at hnm_m7
      rw [hsig] at hnm_m7
      have h1 := List.all_eq_true.mp m8Sw_disj_m7Base nm hmem
      simp only [Bool.not_eq_true', List.any_eq_false, List.mem_map, beq_iff_eq] at h1
      rcases List.mem_map.mp hnm_m7 with ⟨fn, hfn, hfn_eq⟩
      exact h1 nm ⟨fn, hfn, hfn_eq⟩ rfl
    | extra he =>
      have hnm_ex : nm ∈ mfExtraRows.map SpecEntry.name := m8Sw_ofTable_name_mem he
      rw [m8MfExtra_names_eq] at hnm_ex
      have h1 := List.all_eq_true.mp m8Sw_disj_extra nm hmem
      simp only [Bool.not_eq_true', List.any_eq_false, beq_iff_eq] at h1
      exact h1 nm hnm_ex rfl
  | enqVar _ => simp [m8SwNamesLit] at hmem
  | evalGate _ => simp [m8SwNamesLit] at hmem
  | worklist _ => simp [m8SwNamesLit] at hmem

private theorem m8Sw_solve_bytes_elim {xs : Tup Val [i64, i64, i64, i64, i64]}
    {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hs : m7FidSolveBytesSpec xs m Q X) :
    m8FidV123t2Env "kissat_solve_bytes" [i64, i64, i64, i64, i64] [i64] xs m Q X :=
  .base (by decide) (.base (m7FidelityEnv_solve_bytes hs))

/-! ## 2. Callee Helpers & `m8_extend_push2_m6_wp` -/

private theorem m8Sw_row (i : Nat) (nm : Sym) (as bs : List Ty) (sp : Spec as bs)
    (hi : m8SweepEnvRows[i]? = some ⟨nm, as, bs, sp, true⟩ := by rfl)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False) := by
      exact fun _ _ _ _ h => h) :
    M6EnvSpec m8FidV123t2Env nm sp := fun xs m Q X hs =>
  .sweep (Env.ofTable_of_mem (List.mem_of_getElem? hi) m8SweepEnvRows_nodup (hno xs m Q X hs))

private theorem m8Sw_base_row {f : Sym} {as bs : List Ty} {sp : Spec as bs}
    (hne_mf : f ∉ mfExclNames) (hne_sw : f ∉ m8SwExclNames)
    (hmem : (⟨f, as, bs, sp, true⟩ : SpecEntry) ∈ m7FidBaseTable)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False) := by
      exact fun _ _ _ _ h => h) :
    M6EnvSpec m8FidV123t2Env f sp := fun xs m Q X hs =>
  .base hne_sw (.base (.base hne_mf (m7FidBase_row_mem hmem hno xs m Q X hs)))

private theorem m8FidV12Env_elim_extPush2 {as bs : List Ty} {xs : Tup Val as} {m : Mem 64}
    {Q : Post bs} {X : XPost}
    (h : m8FidV12Env "full_extend_push2" as bs xs m Q X) :
    m7FidelityEnv "full_extend_push2" as bs xs m Q X := by
  generalize hnm : ("full_extend_push2" : Sym) = nm at h
  cases h with
  | base hb => exact hb
  | enqVar _ => exact absurd hnm (by decide)
  | evalGate _ => exact absurd hnm (by decide)
  | worklist _ => exact absurd hnm (by decide)

private theorem m8Sw_v12_to_v123t2 :
    ∀ f as bs xs m Q X,
      m8FidV12Env f as bs xs m Q X → m8FidV123t2Env f as bs xs m Q X := by
  intro f as bs xs m Q X h
  by_cases hf : f = "full_extend_push2"
  · subst hf
    have hm7 := m8FidV12Env_elim_extPush2 h
    generalize hnm : ("full_extend_push2" : Sym) = nm at hm7
    cases hm7 with
    | base _ hb =>
      subst hnm
      have hc2 := m7Part2Callees_of_sub m7FidBase_part2_mem
      obtain ⟨has, hrs, heff⟩ := m8Sw_ofTable_sig_elim m7FidBaseTable_nodup hc2.extendPush2 hb
      dsimp only at has hrs
      cases has; cases hrs
      rcases heff with ⟨c, s, R, hpre, hlen, hm, hQ⟩
      exact .extPush2 ⟨c, s, R, hpre, hlen, hm,
        fun r s' m' hcore hlen' ⟨h1, h2, h3, h4, _, _⟩ hm' =>
          hQ r s' m' hcore hlen' ⟨h1, h2, h3, h4⟩ hm'⟩
    | extra he =>
      exact False.elim (absurd (hnm ▸ m8Sw_ofTable_name_mem he)
        (by rw [m8MfExtra_names_eq]; decide))
  · exact .base (by simpa [m8SwExclNames] using hf) h

private theorem m8_extend_push2_m6_wp (Γ : Env) :
    ∀ a m Q X, m6ExtendPush2Spec a m Q X →
      Func.wp Γ full_extend_push2_m6cf_body a m Q X := by
  rintro ⟨h, blk_lit, other, ⟨⟩⟩ m Q X ⟨c, s, R, ⟨rfl, hel⟩, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice_mem, fullSafetySlice_coreProj, fullSafetySlice_safe] at hlen hm hQ
  have hcap : c.extend_cap < dimacsBound := c.hext
  have hmx : c.max_vars < 2 * dimacsBound := c.hmaxv
  unfold dimacsBound at hcap hmx
  have hcv_le := hlen.core_ok.cur_vars_le
  have hv_len := hlen.core_ok.vals_len
  have hl_len := hlen.core_ok.lvl_len
  have hesl := hlen.scratch_ok.extend_stk_len
  have hnlits : ((BitVec.ofNat 64 s.core.cur_vars) <<< (1 : Nat)).toNat = 2 * s.core.cur_vars := by
    have h1 : (BitVec.ofNat 64 s.core.cur_vars).toNat = s.core.cur_vars := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [BitVec.toNat_shiftLeft, h1, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]
    omega
  unfold Func.wp full_extend_push2_m6cf_body
  c0_hsteps_nogrp
  refine wp_join_state_pure (ts := [.bool]) (α := Bool) (fun b => (b, ())) (fun _ => True) ?_ ?_
  · intro _ skip_ot _
    c0_hsteps_nogrp
    refine wp_join_state_pure (ts := [i64]) (α := BitVec 64) (fun x => (x, ()))
      (fun need => need = (if skip_ot then 1#64 else 2#64)) ?_ ?_
    · intro _ need hneed
      have hneed_nat : need.toNat = if skip_ot then 1 else 2 := by
        rw [hneed]; cases skip_ot <;> rfl
      have hneed_pos : 1 ≤ need.toNat := by rw [hneed_nat]; cases skip_ot <;> decide
      c0_hsplit
      · c0_hsteps; exact hQ (false, ()) s m rfl hlen ⟨rfl, hel, rfl, rfl, rfl, rfl⟩ hm
      · c0_hsplit
        · c0_hsteps; exact hQ (false, ()) s m rfl hlen ⟨rfl, hel, rfl, rfl, rfl, rfl⟩ hm
        · have hsub_eq : (BitVec.ofNat 64 c.extend_cap -
              BitVec.ofNat 64 s.scratch.extend_len).toNat =
              c.extend_cap - s.scratch.extend_len := by bv_omega
          have hfit : s.scratch.extend_len + need.toNat ≤ c.extend_cap := by
            have hle : need.toNat ≤ (BitVec.ofNat 64 c.extend_cap -
                BitVec.ofNat 64 s.scratch.extend_len).toNat := by c0_bound
            rw [hsub_eq] at hle; omega
          have hi0 : (BitVec.ofNat 64 s.scratch.extend_len).toNat <
              s.scratch.extend_stk.length := by
            rw [hesl, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
          c0_hsteps_nogrp
          refine wp_join_state0 (α := List (BitVec 32))
            (fun ext1 m1 => ext1.length = c.extend_cap ∧
              (FullMem c { s with scratch := { s.scratch with extend_stk := ext1 } } ⋆ R) m1)
            ?_ ?_
          · rintro _ ext1 m1 ⟨hext1, hm1⟩
            have hadd_eq : (BitVec.ofNat 64 s.scratch.extend_len + need).toNat =
                s.scratch.extend_len + need.toNat := by
              rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
                Nat.mod_eq_of_lt (by omega)]
            c0_hsteps
            let s' : FullState :=
              { s with scratch := { s.scratch with
                extend_stk := ext1,
                extend_len := (BitVec.ofNat 64 s.scratch.extend_len + need).toNat } }
            exact hQ (true, ()) s' _ rfl
              (hlen.with_scratch { hlen.scratch_ok with extend_stk_len := hext1 })
              ⟨rfl, by dsimp only [s']; rw [hadd_eq]; exact hfit, rfl, rfl, rfl, rfl⟩
              (m6cf_fullMem_cast hm rfl)
          · intro Jw hJw
            c0_hsplit
            · c0_hsteps
              exact hJw _ _ ⟨by simp [hesl], hm⟩
            · have hsf : skip_ot = false := by cases skip_ot <;> simp_all
              have hneed2 : need.toNat = 2 := by rw [hneed_nat, hsf]; rfl
              have h0_el : (BitVec.ofNat 64 s.scratch.extend_len).toNat =
                  s.scratch.extend_len := by
                rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
              have hi1 : (BitVec.ofNat 64 s.scratch.extend_len + 1#64).toNat <
                  (s.scratch.extend_stk.set (BitVec.ofNat 64 s.scratch.extend_len).toNat
                    ((blk_lit &&& 0x7FFFFFFF#32) ||| 0x80000000#32)).length := by
                rw [List.length_set, hesl, BitVec.toNat_add, h0_el,
                  show (1#64 : BitVec 64).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
                omega
              c0_hsteps
              exact hJw _ _ ⟨by simp [hesl], hm⟩
    · intro Jn hJn
      c0_hsplit <;> (c0_hsteps; exact hJn _ (by simp_all))
  · intro Js hJs
    c0_hsplit
    · have hot_lt : (other &&& 0x7FFFFFFF#32).toNat < 2 * s.core.cur_vars := by
        have h1 : ((other &&& 0x7FFFFFFF#32).setWidth 64).toNat <
            ((BitVec.ofNat 64 s.core.cur_vars) <<< (1 : Nat)).toNat := by c0_bound
        rw [zext_toNat _ (by decide), hnlits] at h1; exact h1
      have hot_v : ((other &&& 0x7FFFFFFF#32).setWidth 64).toNat < s.core.vals.length := by
        rw [zext_toNat _ (by decide), hv_len]; omega
      have hot_l : (((other &&& 0x7FFFFFFF#32) >>> 1#32).setWidth 64).toNat <
          s.core.lvl.length := by
        rw [zext_toNat _ (by decide)]
        change ((other &&& 0x7FFFFFFF#32) >>> (1 : Nat)).toNat < s.core.lvl.length
        rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_one]
        omega
      c0_hsteps <;> exact hJs _ trivial
    · c0_hsteps; exact hJs false trivial

/-! ## 3. `36` Revived-Sweep Helpers + `m8_sweep_dense_m6` Certification & `ModuleOk` -/

private theorem m8SweepV2Helpers_eq :
    m8SweepV2Helpers =
      [ ⟨"full_m6_max_v", [i64], [i64], FullM6Sweep.full_m6_max_v_body⟩
      , ⟨"full_k6_add_ticks", [i64, i64], [], FullM6Sweep.full_k6_add_ticks_body⟩
      , ⟨"full_k6_init", [i64, i32], [], FullM6Sweep.full_k6_init_body⟩
      , ⟨"full_k6_watch", [i64, i32, i32, i32], [], FullM6Sweep.full_k6_watch_body⟩
      , ⟨"full_k6_assign", [i64, i32, i32], [], FullM6Sweep.full_k6_assign_body⟩
      , ⟨"full_k6_add_clause", [i64, i64, i32], [.bool], full_k6_add_clause_body⟩
      , ⟨"full_k6_mtf", [i64, i32], [], FullM6Sweep.full_k6_mtf_body⟩
      , ⟨"full_k6_backtrack", [i64, i32], [], FullM6Sweep.full_k6_backtrack_body⟩
      , ⟨"full_k6_propagate", [i64], [i32], full_k6_propagate_body⟩
      , ⟨"full_k6_ana_clause", [i64, i32, i32], [], FullM6Sweep.full_k6_ana_clause_body⟩
      , ⟨"full_k6_analyze", [i64, i32], [.bool], FullM6Sweep.full_k6_analyze_body⟩
      , ⟨"full_k6_solve", [i64, i64], [i64], FullM6Sweep.full_k6_solve_body⟩
      , ⟨"full_k6_flip", [i64, i32], [.bool], full_k6_flip_body⟩
      , ⟨"full_k512_add_live_m6", [i64, i32, i32], [], FullM6Sweep.full_k512_add_live_m6_body⟩
      , ⟨"full_m6_dense_prop_lit", [i64, i32], [.bool], FullM6Sweep.full_m6_dense_prop_lit_body⟩
      , ⟨"full_m6_dense_prop", [i64], [.bool], FullM6Sweep.full_m6_dense_prop_body⟩
      , ⟨"full_m6_sweep_cone", [i64, i32], [i64], full_m6_sweep_cone_body⟩
      , ⟨"full_m6_sweep_refine_sig", [i64, i32, i32], [], FullM6Sweep.full_m6_sweep_refine_sig_body⟩
      , ⟨"full_m6_sweep_rand_phases", [i64, i32], [], full_m6_sweep_rand_phases_body⟩
      , ⟨"full_m6_sweep_solve", [i64, i32, i64], [i64], FullM6Sweep.full_m6_sweep_solve_body⟩
      , ⟨"full_m6_sweep_flip_round", [i64, i32], [i32], full_m6_sweep_flip_round_body⟩
      , ⟨"full_m6_sweep_sim", [i64, i32, i64], [i32], full_m6_sweep_sim_body⟩
      , ⟨"full_m6_sweep_rearm", [i64, i32], [], FullM6Sweep.full_m6_sweep_rearm_body⟩
      , ⟨"full_m6_sweep_build_pht", [i64, i32, i64], [], FullM6Sweep.full_m6_sweep_build_pht_body⟩
      , ⟨"full_m6_extract_pht", [i64, i32, i64], [i32], FullM6Sweep.full_m6_extract_pht_body⟩
      , ⟨"full_m6_refine_partition", [i64, i32, i32], [i32],
          FullM6Sweep.full_m6_refine_partition_body⟩
      , ⟨"full_m6_sweep_units", [i64, i32, i32, i64], [i64], FullM6Sweep.full_m6_sweep_units_body⟩
      , ⟨"full_m6_sweep_classes", [i64, i32, i32, i64], [i64],
          FullM6Sweep.full_m6_sweep_classes_body⟩
      , ⟨"full_m6_els_ar", [i64, i32, i32], [.bool], FullM6Sweep.full_m6_els_ar_body⟩
      , ⟨"full_m6_els_lit", [i64, i32, i32], [.bool], FullM6Sweep.full_m6_els_lit_body⟩
      , ⟨"full_m6_els_fold", [i64, i32], [.bool], FullM6Sweep.full_m6_els_fold_body⟩
      , ⟨"full_m6_dense_els", [i64, i32], [.bool], FullM6Sweep.full_m6_dense_els_body⟩
      , ⟨"full_m6_sweep_var", [i64, i32, i64], [i64], FullM6Sweep.full_m6_sweep_var_body⟩
      , ⟨"full_m6_cand_sift", [i64, i64, i32, i32], [], FullM6Sweep.full_m6_cand_sift_body⟩
      , ⟨"full_m6_collect_cands", [i64], [i32], full_m6_collect_cands_body⟩
      , ⟨"full_m6_sweep_vars", [i64, i64, i64], [i64], full_m6_sweep_vars_body⟩ ] := by
  t_kernel_rfl

private theorem m8SweepV2Helpers_tableImpl :
    TableImpl m8FidV123t2Env m8SweepV2Helpers m8SweepEnvRows := by
  have hc1 := m7Part1Callees_of_sub m7FidBase_part1_mem
  have hc2 := m7Part2Callees_of_sub m7FidBase_part2_mem
  have hAssignLvl : M6EnvSpec m8FidV123t2Env "full_assign_lvl" fullAssignLvlSpec :=
    m8Sw_base_row (by decide) (by decide) hc1.assignLvl
  have hWatchPush : M6EnvSpec m8FidV123t2Env "full_watch_push" fullWatchPushSpec :=
    m8Sw_base_row (by decide) (by decide) (m7FidBase_pfx_mem _ m7FidOrchPfxRows_specs.watchPush)
  have hSetInact : M6EnvSpec m8FidV123t2Env "full_set_inactive" fullSetInactiveSpec :=
    m8Sw_base_row (by decide) (by decide) hc2.setInactive
  have hAddUnit : M6EnvSpec m8FidV123t2Env "full_add_unit" fullAddUnitSpec :=
    m8Sw_base_row (by decide) (by decide) hc2.addUnit
  have hAddBin : M6EnvSpec m8FidV123t2Env "full_add_bin" fullAddBinSpec :=
    m8Sw_base_row (by decide) (by decide) hc2.addBin
  have hExtPush2 : M6EnvSpec m8FidV123t2Env "full_extend_push2" m6ExtendPush2Spec :=
    fun _ _ _ _ hs => .extPush2 hs
  have r0 := m8Sw_row 0 "full_m6_max_v" [i64] [i64] m6MaxVSpec
  have r1 := m8Sw_row 1 "full_k6_add_ticks" [i64, i64] [] k6AddTicksSpec
  have r2 := m8Sw_row 2 "full_k6_init" [i64, i32] [] k6InitSpec
  have r3 := m8Sw_row 3 "full_k6_watch" [i64, i32, i32, i32] [] k6WatchSpec
  have r4 := m8Sw_row 4 "full_k6_assign" [i64, i32, i32] [] k6AssignSpec
  have r5 := m8Sw_row 5 "full_k6_add_clause" [i64, i64, i32] [.bool] k6AddClauseSpec
  have r6 := m8Sw_row 6 "full_k6_mtf" [i64, i32] [] k6MtfSpec
  have r7 := m8Sw_row 7 "full_k6_backtrack" [i64, i32] [] k6BacktrackSpec
  have r8 := m8Sw_row 8 "full_k6_propagate" [i64] [i32] k6PropagateSpec
  have r9 := m8Sw_row 9 "full_k6_ana_clause" [i64, i32, i32] [] k6AnaClauseSpec
  have r10 := m8Sw_row 10 "full_k6_analyze" [i64, i32] [.bool] k6AnalyzeSpec
  have r11 := m8Sw_row 11 "full_k6_solve" [i64, i64] [i64] k6SolveSpec
  have r12 := m8Sw_row 12 "full_k6_flip" [i64, i32] [.bool] k6FlipSpec
  have r13 := m8Sw_row 13 "full_k512_add_live_m6" [i64, i32, i32] [] k6AddLiveSpec
  have r14 := m8Sw_row 14 "full_m6_dense_prop_lit" [i64, i32] [.bool] m6DensePropLitSpec
  have r15 := m8Sw_row 15 "full_m6_dense_prop" [i64] [.bool] m6DensePropSpec
  have r16 := m8Sw_row 16 "full_m6_sweep_cone" [i64, i32] [i64] m6SweepConeSpec
  have r17 := m8Sw_row 17 "full_m6_sweep_refine_sig" [i64, i32, i32] [] m6SweepRefineSigSpec
  have r18 := m8Sw_row 18 "full_m6_sweep_rand_phases" [i64, i32] [] m6SweepRandPhasesSpec
  have r19 := m8Sw_row 19 "full_m6_sweep_solve" [i64, i32, i64] [i64] m6SweepSolveSpec
  have r20 := m8Sw_row 20 "full_m6_sweep_flip_round" [i64, i32] [i32] m6SweepFlipRoundSpec
  have r21 := m8Sw_row 21 "full_m6_sweep_sim" [i64, i32, i64] [i32] m6SweepSimSpec
  have r22 := m8Sw_row 22 "full_m6_sweep_rearm" [i64, i32] [] m6SweepRearmSpec
  have r23 := m8Sw_row 23 "full_m6_sweep_build_pht" [i64, i32, i64] [] m6SweepBuildPhtSpec
  have r24 := m8Sw_row 24 "full_m6_extract_pht" [i64, i32, i64] [i32] m6ExtractPhtSpec
  have r25 := m8Sw_row 25 "full_m6_refine_partition" [i64, i32, i32] [i32] m6RefinePartitionSpec
  have r26 := m8Sw_row 26 "full_m6_sweep_units" [i64, i32, i32, i64] [i64] m6SweepUnitsSpec
  have r27 := m8Sw_row 27 "full_m6_sweep_classes" [i64, i32, i32, i64] [i64] m6SweepClassesSpec
  have r28 := m8Sw_row 28 "full_m6_els_ar" [i64, i32, i32] [.bool] m6ElsArSpec
  have r29 := m8Sw_row 29 "full_m6_els_lit" [i64, i32, i32] [.bool] m6ElsLitSpec
  have r30 := m8Sw_row 30 "full_m6_els_fold" [i64, i32] [.bool] m6ElsFoldSpec
  have r31 := m8Sw_row 31 "full_m6_dense_els" [i64, i32] [.bool] m6DenseElsSpec
  have r32 := m8Sw_row 32 "full_m6_sweep_var" [i64, i32, i64] [i64] m6SweepVarSpec
  have r33 := m8Sw_row 33 "full_m6_cand_sift" [i64, i64, i32, i32] [] m6CandSiftSpec
  have r34 := m8Sw_row 34 "full_m6_collect_cands" [i64] [i32] m6CollectCandsSpec
  rw [m8SweepV2Helpers_eq]
  have hrows : m8SweepEnvRows =
      [ ⟨"full_m6_max_v", [i64], [i64], m6MaxVSpec, true⟩
      , ⟨"full_k6_add_ticks", [i64, i64], [], k6AddTicksSpec, true⟩
      , ⟨"full_k6_init", [i64, i32], [], k6InitSpec, true⟩
      , ⟨"full_k6_watch", [i64, i32, i32, i32], [], k6WatchSpec, true⟩
      , ⟨"full_k6_assign", [i64, i32, i32], [], k6AssignSpec, true⟩
      , ⟨"full_k6_add_clause", [i64, i64, i32], [.bool], k6AddClauseSpec, true⟩
      , ⟨"full_k6_mtf", [i64, i32], [], k6MtfSpec, true⟩
      , ⟨"full_k6_backtrack", [i64, i32], [], k6BacktrackSpec, true⟩
      , ⟨"full_k6_propagate", [i64], [i32], k6PropagateSpec, true⟩
      , ⟨"full_k6_ana_clause", [i64, i32, i32], [], k6AnaClauseSpec, true⟩
      , ⟨"full_k6_analyze", [i64, i32], [.bool], k6AnalyzeSpec, true⟩
      , ⟨"full_k6_solve", [i64, i64], [i64], k6SolveSpec, true⟩
      , ⟨"full_k6_flip", [i64, i32], [.bool], k6FlipSpec, true⟩
      , ⟨"full_k512_add_live_m6", [i64, i32, i32], [], k6AddLiveSpec, true⟩
      , ⟨"full_m6_dense_prop_lit", [i64, i32], [.bool], m6DensePropLitSpec, true⟩
      , ⟨"full_m6_dense_prop", [i64], [.bool], m6DensePropSpec, true⟩
      , ⟨"full_m6_sweep_cone", [i64, i32], [i64], m6SweepConeSpec, true⟩
      , ⟨"full_m6_sweep_refine_sig", [i64, i32, i32], [], m6SweepRefineSigSpec, true⟩
      , ⟨"full_m6_sweep_rand_phases", [i64, i32], [], m6SweepRandPhasesSpec, true⟩
      , ⟨"full_m6_sweep_solve", [i64, i32, i64], [i64], m6SweepSolveSpec, true⟩
      , ⟨"full_m6_sweep_flip_round", [i64, i32], [i32], m6SweepFlipRoundSpec, true⟩
      , ⟨"full_m6_sweep_sim", [i64, i32, i64], [i32], m6SweepSimSpec, true⟩
      , ⟨"full_m6_sweep_rearm", [i64, i32], [], m6SweepRearmSpec, true⟩
      , ⟨"full_m6_sweep_build_pht", [i64, i32, i64], [], m6SweepBuildPhtSpec, true⟩
      , ⟨"full_m6_extract_pht", [i64, i32, i64], [i32], m6ExtractPhtSpec, true⟩
      , ⟨"full_m6_refine_partition", [i64, i32, i32], [i32], m6RefinePartitionSpec, true⟩
      , ⟨"full_m6_sweep_units", [i64, i32, i32, i64], [i64], m6SweepUnitsSpec, true⟩
      , ⟨"full_m6_sweep_classes", [i64, i32, i32, i64], [i64], m6SweepClassesSpec, true⟩
      , ⟨"full_m6_els_ar", [i64, i32, i32], [.bool], m6ElsArSpec, true⟩
      , ⟨"full_m6_els_lit", [i64, i32, i32], [.bool], m6ElsLitSpec, true⟩
      , ⟨"full_m6_els_fold", [i64, i32], [.bool], m6ElsFoldSpec, true⟩
      , ⟨"full_m6_dense_els", [i64, i32], [.bool], m6DenseElsSpec, true⟩
      , ⟨"full_m6_sweep_var", [i64, i32, i64], [i64], m6SweepVarSpec, true⟩
      , ⟨"full_m6_cand_sift", [i64, i64, i32, i32], [], m6CandSiftSpec, true⟩
      , ⟨"full_m6_collect_cands", [i64], [i32], m6CollectCandsSpec, true⟩
      , ⟨"full_m6_sweep_vars", [i64, i64, i64], [i64], m6SweepVarsSpec, true⟩ ] := rfl
  rw [hrows]
  exact
    ⟨ SpecEntry.Impl.of (full_m6_max_v_wp m8FidV123t2Env)
    , SpecEntry.Impl.of (full_k6_add_ticks_wp m8FidV123t2Env)
    , SpecEntry.Impl.of (full_k6_init_wp m8FidV123t2Env r0)
    , SpecEntry.Impl.of (full_k6_watch_wp m8FidV123t2Env)
    , SpecEntry.Impl.of (full_k6_assign_wp m8FidV123t2Env)
    , SpecEntry.Impl.of (m8_k6_add_clause_wp m8FidV123t2Env r0 r1 r4 r3)
    , SpecEntry.Impl.of (full_k6_mtf_wp m8FidV123t2Env)
    , SpecEntry.Impl.of (full_k6_backtrack_wp m8FidV123t2Env)
    , SpecEntry.Impl.of (m8_k6_propagate_wp m8FidV123t2Env r1 r4)
    , SpecEntry.Impl.of (full_k6_ana_clause_wp m8FidV123t2Env)
    , SpecEntry.Impl.of (full_k6_analyze_wp m8FidV123t2Env r9 r7 r6 r3 r4)
    , SpecEntry.Impl.of (full_k6_solve_wp m8FidV123t2Env r0 r7 r4 r8 r10)
    , SpecEntry.Impl.of (m8_k6_flip_wp m8FidV123t2Env r0 r1)
    , SpecEntry.Impl.of (full_k512_add_live_m6_wp m8FidV123t2Env r0 r7 r4 r3 r8)
    , SpecEntry.Impl.of (full_m6_dense_prop_lit_wp m8FidV123t2Env hAssignLvl)
    , SpecEntry.Impl.of (full_m6_dense_prop_wp m8FidV123t2Env r14)
    , SpecEntry.Impl.of (m8_sweep_cone_wp m8FidV123t2Env r0 r2 r5)
    , SpecEntry.Impl.of (full_m6_sweep_refine_sig_wp m8FidV123t2Env r0)
    , SpecEntry.Impl.of (m8_sweep_rand_phases_wp m8FidV123t2Env r0)
    , SpecEntry.Impl.of (full_m6_sweep_solve_wp m8FidV123t2Env r18 r11)
    , SpecEntry.Impl.of (m8_sweep_flip_round_wp m8FidV123t2Env r0 r12)
    , SpecEntry.Impl.of (m8_sweep_sim_wp m8FidV123t2Env r0 r19 r17 r20)
    , SpecEntry.Impl.of (full_m6_sweep_rearm_wp m8FidV123t2Env)
    , SpecEntry.Impl.of (full_m6_sweep_build_pht_wp m8FidV123t2Env r0)
    , SpecEntry.Impl.of (full_m6_extract_pht_wp m8FidV123t2Env r0)
    , SpecEntry.Impl.of (full_m6_refine_partition_wp m8FidV123t2Env r0)
    , SpecEntry.Impl.of (full_m6_sweep_units_wp m8FidV123t2Env r0 r12 r17 r19 hAddUnit r13 r22)
    , SpecEntry.Impl.of (full_m6_sweep_classes_wp m8FidV123t2Env r0 r23 r24 r12 r17 r25 r19 r13
        r22)
    , SpecEntry.Impl.of (full_m6_els_ar_wp m8FidV123t2Env hWatchPush hAddUnit hAddBin)
    , SpecEntry.Impl.of (full_m6_els_lit_wp m8FidV123t2Env hAddUnit hAddBin r28)
    , SpecEntry.Impl.of (full_m6_els_fold_wp m8FidV123t2Env hAddUnit hExtPush2 hSetInact)
    , SpecEntry.Impl.of (full_m6_dense_els_wp m8FidV123t2Env r30 r29 r15)
    , SpecEntry.Impl.of (full_m6_sweep_var_wp m8FidV123t2Env r0 r16 r21 r26 r27 r31)
    , SpecEntry.Impl.of (full_m6_cand_sift_wp m8FidV123t2Env)
    , SpecEntry.Impl.of (m8_collect_cands_wp m8FidV123t2Env r33)
    , SpecEntry.Impl.of (m8_sweep_vars_wp m8FidV123t2Env r0 r15 r34 r32 r33), trivial ⟩

private theorem m8FidV12Env_elim_gen {f : Sym} {as bs : List Ty} {xs : Tup Val as}
    {m : Mem 64} {Q : Post bs} {X : XPost}
    (hne1 : f ≠ "full_cong_enq_var") (hne2 : f ≠ "full_cong_eval_gate")
    (hne3 : f ≠ "full_cong_worklist") (h : m8FidV12Env f as bs xs m Q X) :
    m7FidelityEnv f as bs xs m Q X := by
  cases h with
  | base hb => exact hb
  | enqVar _ => exact absurd rfl hne1
  | evalGate _ => exact absurd rfl hne2
  | worklist _ => exact absurd rfl hne3

private theorem m8Sw_elim_base_gen {f : Sym} {as bs : List Ty} {xs : Tup Val as}
    {m : Mem 64} {Q : Post bs} {X : XPost}
    (hne : f ≠ "full_extend_push2") (hnsw : f ∉ m8SweepEnvRows.map SpecEntry.name)
    (h : m8FidV123t2Env f as bs xs m Q X) :
    m8FidV12Env f as bs xs m Q X := by
  cases h with
  | base _ hb => exact hb
  | extPush2 _ => exact absurd rfl hne
  | sweep hsw => exact False.elim (hnsw (m8Sw_ofTable_name_mem hsw))

private theorem m8Sw_elim_sweep_gen {f : Sym} {as bs : List Ty} {xs : Tup Val as}
    {m : Mem 64} {Q : Post bs} {X : XPost}
    (hmem : f ∈ m8SwNamesLit) (h : m8FidV123t2Env f as bs xs m Q X) :
    Env.ofTable m8SweepEnvRows f as bs xs m Q X := by
  cases h with
  | base _ hv12 => exact False.elim (m8Sw_not_in_v12Env hmem hv12)
  | extPush2 _ => exact False.elim (by simp [m8SwNamesLit] at hmem)
  | sweep hsw => exact hsw

private theorem m8Sw_mem_wp_of_tableImpl :
    ∀ {fs : List Fn} {rs : List SpecEntry},
      TableImpl m8FidV123t2Env fs rs →
      (∀ e ∈ rs, e ∈ m8SweepEnvRows) →
      ∀ f ∈ fs, ∀ xs m Q X,
        m8FidV123t2Env f.name f.as f.rs xs m Q X → Func.wp m8FidV123t2Env f.body xs m Q X
  | [], [], _, _, _, hf => nomatch hf
  | [], _ :: _, _, _, _, hf => nomatch hf
  | _ :: _, [], ht, _, _, _ => False.elim ht
  | f :: _, r :: _, ⟨h1, h2⟩, hsub, g, hg => by
    intro xs m Q X hs
    rcases List.mem_cons.mp hg with rfl | htl
    · obtain ⟨⟨hnme, has, hrs⟩, himpl⟩ := h1
      have hr_mem : r ∈ m8SweepEnvRows := hsub r List.mem_cons_self
      have he_mem : g.name ∈ m8SwNamesLit := by
        rw [← hnme, ← m8SweepEnvRows_names_eq]
        exact List.mem_map.mpr ⟨r, hr_mem, rfl⟩
      have hof := m8Sw_elim_sweep_gen he_mem hs
      have hof' : Env.ofTable m8SweepEnvRows r.name g.as g.rs xs m Q X := by
        rw [hnme]; exact hof
      obtain ⟨_, _, heff⟩ := m8Sw_ofTable_sig_elim m8SweepEnvRows_nodup hr_mem hof'
      exact himpl xs m Q X heff
    · exact m8Sw_mem_wp_of_tableImpl h2 (fun e he => hsub e (List.mem_cons_of_mem _ he)) g htl
        xs m Q X hs

private theorem m8Sw_elim_extPush2 {xs m Q X}
    (hs : m8FidV123t2Env "full_extend_push2" [i64, i32, i32] [.bool] xs m Q X) :
    m6ExtendPush2Spec xs m Q X := by
  cases hs with
  | base hne _ => exact absurd (by decide : "full_extend_push2" ∈ m8SwExclNames) hne
  | extPush2 hex => exact hex
  | sweep hsw =>
    exact False.elim (absurd (m8Sw_ofTable_name_mem hsw) (by rw [m8SweepEnvRows_names_eq]; decide))

private theorem m8Sw_elim_sweepDense {xs m Q X}
    (hs : m8FidV123t2Env "full_sweep_dense_m6" [i64, i64, i64] [i64] xs m Q X) :
    m4SweepDenseSpec xs m Q (fun _ _ _ _ => False) := by
  have hv12 := m8Sw_elim_base_gen (by decide) (by rw [m8SweepEnvRows_names_eq]; decide) hs
  have hm7 := m8FidV12Env_elim_gen (by decide) (by decide) (by decide) hv12
  cases hm7 with
  | base _ hb =>
    have hr_mem : (⟨"full_sweep_dense_m6", [i64, i64, i64], [i64],
        FullDefSweep.fullSweepDenseSpec, true⟩ : SpecEntry) ∈ m7FidBaseTable :=
      m7FidBase_pfx_mem _ (List.mem_of_getElem? (i := 15) (by t_kernel_rfl))
    exact (m8Sw_ofTable_sig_elim m7FidBaseTable_nodup hr_mem hb).2.2
  | extra he =>
    exact False.elim (absurd (m8Sw_ofTable_name_mem he) (by rw [m8MfExtra_names_eq]; decide))

private theorem mf_patchModule_moduleOk {Γ Γ' : Env} {M : LeanQbe.T.Module}
    (hM : ModuleOk Γ M) {repls : List Fn} {befores : List (Sym × List Fn)}
    (hchk : ({ M with fns := mfPatchFns repls befores M.fns } :
      LeanQbe.T.Module).checkAcyclic = true)
    (hrWf : ∀ r ∈ repls, r.Wf)
    (hiWf : ∀ p ∈ befores, ∀ h ∈ p.2, h.Wf)
    (hCallee : ∀ f as bs xs m Q X, Γ f as bs xs m Q X → Γ' f as bs xs m Q X)
    (hFnWp : ∀ g ∈ M.fns, repls.find? (fun x => x.name == g.name) = none →
      (∀ xs m Q X, Γ' g.name g.as g.rs xs m Q X → Func.wp Γ' g.body xs m Q X) ∨
      (∀ xs m Q X, Γ' g.name g.as g.rs xs m Q X → Γ g.name g.as g.rs xs m Q X))
    (hrWp : ∀ r ∈ repls, ∀ xs m Q X,
      Γ' r.name r.as r.rs xs m Q X → Func.wp Γ' r.body xs m Q X)
    (hiWp : ∀ p ∈ befores, ∀ h ∈ p.2, ∀ xs m Q X,
      Γ' h.name h.as h.rs xs m Q X → Func.wp Γ' h.body xs m Q X) :
    ModuleOk Γ' { M with fns := mfPatchFns repls befores M.fns } := by
  have hwfOrig : ∀ f ∈ M.fns, f.Wf := fun f hf => by
    obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hf
    exact (hM.fnsOk pre f post hsplit).1
  refine LeanQbe.T.Module.moduleOk_of_checkAcyclic hchk
    (mfPatchFns_wf hwfOrig hrWf hiWf) ?_
  intro fn hmem
  rcases List.mem_flatMap.mp hmem with ⟨g, hg, hmem_g⟩
  rcases List.mem_append.mp hmem_g with h_ins | h_rep
  · rcases mem_mfPatchInsAt h_ins with ⟨hs, hm, hfn_hs⟩
    exact hiWp (g.name, hs) hm fn hfn_hs
  · rcases List.mem_singleton.mp h_rep with rfl
    cases h : repls.find? (fun x => x.name == g.name) with
    | some r =>
      intro xs m Q X hspec
      exact hrWp r (List.mem_of_find?_eq_some h) xs m Q X hspec
    | none =>
      intro xs m Q X hspec
      rcases hFnWp g hg h with hNew | hPull
      · exact hNew xs m Q X hspec
      · obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hg
        have ⟨hwfG, hcallsG, hwpG⟩ := hM.fnsOk pre g post hsplit
        exact wp_env_agree_of_callsOk
          (hwfG Val (fun _ => Unit) Cont (fun _ => Unit) xs (Tup.units g.as))
          hcallsG (fun f as bs _ => hCallee f as bs) m
          (hwpG xs m Q X (hPull xs m Q X hspec))

/-- Closed `449/449` `ModuleOk` for `FullM8SweepV2.m8FidV123t2Module` (`V12 + V3t2`, `0` hooks). -/
theorem m8FidV123t2_moduleOk : ModuleOk m8FidV123t2Env m8FidV123t2Module := by
  have hMod : m8FidV123t2Module =
      { m8FidV12Module with fns := mfPatchFns m8SweepV2Repls m8FidV123t2Befores m8FidV12Fns } := by
    dsimp only [m8FidV123t2Module]; rw [m8FidV123t2Fns_eq_patch]
  have hAcy : ({ m8FidV12Module with
      fns := mfPatchFns m8SweepV2Repls m8FidV123t2Befores m8FidV12Fns } :
      LeanQbe.T.Module).checkAcyclic = true := hMod ▸ m8FidV123t2_acyclic
  rw [hMod]
  refine mf_patchModule_moduleOk m8FidV12_moduleOk hAcy m8SweepV2Repls_wf
    ?_ m8Sw_v12_to_v123t2 ?_ ?_ ?_
  · intro p hp h hh
    rcases List.mem_singleton.mp hp with rfl
    exact m8SweepV2Helpers_wf h hh
  · intro g hg _hnone
    by_cases hg_ext : g.name = "full_extend_push2"
    · refine Or.inl ?_
      have hg_eq := list_nodup_name_eq Fn.name m8FidV12Fns_names_nodup hg
        (List.mem_of_getElem? (i := 172) (by t_kernel_rfl) :
          m6cfExtendPush2Fn ∈ m8FidV12Module.fns) hg_ext
      subst hg_eq
      exact fun xs m Q X hs =>
        m8_extend_push2_m6_wp m8FidV123t2Env xs m Q X (m8Sw_elim_extPush2 hs)
    · exact Or.inr fun xs m Q X hs => m8Sw_elim_base_gen hg_ext (m8Sw_not_mem_v12 hg) hs
  · intro r hr xs m Q X hs
    rcases List.mem_singleton.mp hr with rfl
    exact m8_sweep_dense_m6_wp m8FidV123t2Env
      (m8Sw_row 0 "full_m6_max_v" [i64] [i64] m6MaxVSpec)
      (m8Sw_row 35 "full_m6_sweep_vars" [i64, i64, i64] [i64] m6SweepVarsSpec)
      xs m Q X (m8Sw_elim_sweepDense hs)
  · intro p hp h hh xs m Q X hs
    rcases List.mem_singleton.mp hp with rfl
    exact m8Sw_mem_wp_of_tableImpl m8SweepV2Helpers_tableImpl (fun _ he => he) h hh xs m Q X hs

/-! ## 4. Top-Level `kissat_solve_bytes` Soundness & Concrete UNSAT Non-Vacuity -/

/-- `kissat_solve_bytes` is in `m8FidV123t2Module.fns`. -/
theorem m8FidV123t2_solveBytes_mem : m6oSolveBytesFn ∈ m8FidV123t2Module.fns := by
  change m6oSolveBytesFn ∈ m8FidV123t2Fns
  rw [m8FidV123t2Fns_eq_patch]
  exact mfPatchFns_mem_of_ne m8FidV12_solveBytes_mem
    (fun r hr => by
      rcases List.mem_singleton.mp hr with rfl
      decide)

/-- Top-level `kissat_solve_bytes` soundness theorem on `FullM8SweepV2.m8FidV123t2Module`. -/
theorem m8FidV123t2_solve_bytes_sound
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp m8FidV123t2Env FullM6Orch.kissat_solve_bytes_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
          (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
          (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
      (fun _ _ _ _ => False) := by
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem m8FidV123t2_solveBytes_mem
  have hfn := (m8FidV123t2_moduleOk.fnsOk pre m6oSolveBytesFn post hsplit).2.2
  have hsb : m6oSolveBytesFn =
      ⟨"kissat_solve_bytes", [i64, i64, i64, i64, i64], [i64],
        FullM6Orch.kissat_solve_bytes_body⟩ := rfl
  rw [hsb] at hfn
  refine hfn (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ())
    m _ _ (m8Sw_solve_bytes_elim (m7FidSolveBytesSpec_intro hcfit hwfit hm ?_))
  intro r m' hdom h20 _ hm'
  exact ⟨hdom, h20, hm'⟩

/-- Host-framed machine-memory lift for `kissat_solve_bytes` on `m8FidV123t2Module`. -/
theorem m8FidV123t2_solve_bytes_host_sound
    {cnf_ptr work_ptr : BitVec 64} {cnfBytes : List UInt8} {wlen : Nat}
    {R F_host : Mem 64 → Prop} {r : BitVec 64} {m' st_dmem : Mem 64}
    (hpost :
      (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
      (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m')
    (hhost : (Eq m' ⋆ F_host) st_dmem) :
    (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
    (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
    (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R ⋆ F_host) st_dmem :=
  m7Fidelity_solve_bytes_host_sound hpost hhost

/-- Concrete deterministic UNSAT non-vacuity (`r = 20#64`) for `kissat_solve_bytes` on
`nvM6UnsatInitMem` (`m8FidV123t2Module`). -/
theorem m8FidV123t2_unsat_nv :
    Func.wp m8FidV123t2Env FullM6Orch.kissat_solve_bytes_body
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
        nvM6UnsatWorkPtr, BitVec.ofNat 64 nvM6WorkLen, 16#64, ())
      nvM6UnsatInitMem
      (fun rs m' =>
        match rs with
        | (r, ()) =>
          r = 20#64 ∧ nvM6UnsatCnf.Unsat ∧
          (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen) m')
      (fun _ _ _ _ => False) := by
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem m8FidV123t2_solveBytes_mem
  have hfn := (m8FidV123t2_moduleOk.fnsOk pre m6oSolveBytesFn post hsplit).2.2
  have hsb : m6oSolveBytesFn =
      ⟨"kissat_solve_bytes", [i64, i64, i64, i64, i64], [i64],
        FullM6Orch.kissat_solve_bytes_body⟩ := rfl
  rw [hsb] at hfn
  have hm0 :
      (bytes nvM6CnfPtr nvM6UnsatBytes ⋆ region nvM6UnsatWorkPtr nvM6WorkLen ⋆ emp)
        nvM6UnsatInitMem := by
    rw [Std.ExtHashMap.sep_emp]
    exact nvM6UnsatInitMem_sep
  refine hfn (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
      nvM6UnsatWorkPtr, BitVec.ofNat 64 nvM6WorkLen, 16#64, ()) nvM6UnsatInitMem _ _
    (m8Sw_solve_bytes_elim
      (m7FidSolveBytesSpec_intro (by decide) (by decide) hm0 fun r m' _ _ htr hm' => ?_))
  have hr20 := htr 1 2 9 (by decide) (by decide) (by decide) nvM6_unsat_bound (by decide)
    nvM6Unsat_header nvM6Unsat_unitTrace
  exact ⟨hr20, nvM6UnsatCnf_unsat, by rwa [Std.ExtHashMap.sep_emp] at hm'⟩

end LeanQbe.T.Examples.Kissat.FullM8SweepV2
