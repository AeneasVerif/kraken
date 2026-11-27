/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S1BVEFwdSub
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S1Spec
public import LeanQbe.T.Examples.Kissat.FullM7BveGatesProof0
public import LeanQbe.T.Examples.Kissat.FullM6BveFwdProof2
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullBvaFwdSpec
import LeanQbe.T.Examples.Kissat.FullDenseWatchLemmas1
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Fidelity Step 13 Shard S1-B Proofs — Part 0 (`has_*_cands`, `bve_var_key`,
`fwd_scan_lit`, `fwd_connect_subsumer`)

Parametric `(Γ : Env)` proofs (`public section`, `0` `@[expose]`, `0` `import all`,
`<= 100` cols, `< 1,400` LOC, every theorem `<= 420` lines):
1. `full_has_factor_cands_fid_s13_wp` (`step13HasFactorCandsSpec`)
2. `full_has_elim_cands_fid_s13_wp` (`step13HasElimCandsSpec`)
3. `full_bve_var_key_m7_s13_wp` (`step13BveVarKeySpec`)
4. `full_fwd_scan_lit_m7_s13_wp` (`step13FwdScanLitSpec`)
5. `full_fwd_connect_subsumer_m7_s13_wp` (`step13FwdConnectSubsumerSpec`)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S1

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullBvaFwdHelpers
open LeanQbe.T.Examples.Kissat.Full.FullDenseWatchHelpers
open LeanQbe.T.Examples.Kissat.FullFastBveBudgets
open LeanQbe.T.Examples.Kissat.FullM6Sweep
open LeanQbe.T.Examples.Kissat.FullM6BveFwd
open LeanQbe.T.Examples.Kissat.FullM7BveGates
open Kraken.Bedrock2.Test

open scoped FullArenaTactics

local macro "s13b_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

/-! ## 1. `full_has_factor_cands_fid` & `full_has_elim_cands_fid` -/

private theorem s13_cands_pred_wp {Γ : Env} {e : Expr Val Cont [.bool]}
    {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [.bool]} {X : XPost}
    (hBody : e = full_has_factor_cands_fid_body Val Cont (c.hdr, ()) ∨
      e = full_has_elim_cands_fid_body Val Cont (c.hdr, ()))
    (hlen : s.LengthsOk c) (hm : (FullMem c s ⋆ R) m) (hQ : ∀ r : Bool, Q (r, ()) m) :
    wp Γ Q X e m := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv_le := hlen.core_ok.cur_vars_le
  rcases hBody with rfl | rfl
  · unfold full_has_factor_cands_fid_body; c0_hsteps_nogrp
    refine wp_loop_group (ts := [i64])
      (fun rem (v, ()) mv => mv = m ∧ v.toNat ≤ s.core.cur_vars ∧ rem = s.core.cur_vars - v.toNat)
      ?_ (fun _ hL => by
        c0_hsteps!; exact hL s.core.cur_vars (0#64, ()) m ⟨rfl, Nat.zero_le _, rfl⟩)
    rintro L rem ⟨v, ⟨⟩⟩ mv hL ⟨rfl, hv_le, rfl⟩
    c0_hsplit
    · have hv_lt : v.toNat < s.core.cur_vars := by
        rw [Nat.mod_eq_of_lt (by omega)] at hc; exact hc
      have hv_fl : v.toNat < s.core.flags.length := by rw [hlen.core_ok.flags_len]; omega
      have hv_vals : (v <<< (1 : Nat)).toNat < s.core.vals.length := by
        rw [hlen.core_ok.vals_len]; c0_bound
      have hv1 : (v + 1#64).toNat = v.toNat + 1 := by c0_bound
      c0_hsteps_nogrp
      refine wp_join0 (fun mj => mj = mv)
        (fun _ mj hmj => by
          rcases hmj.symm with rfl; c0_hsteps!
          exact hL (s.core.cur_vars - (v + 1#64).toNat) (v + 1#64, ()) mv (by omega)
            ⟨rfl, by omega, rfl⟩)
        (fun Jx hJx => by
          c0_hsplit
          · c0_hsplit
            · c0_hsplit
              · c0_hsteps!; exact hQ true
              · c0_hsteps!; exact hJx mv rfl
            · c0_hsteps!; exact hJx mv rfl
          · c0_hsteps!; exact hJx mv rfl)
    · c0_hsteps!; exact hQ false
  · unfold full_has_elim_cands_fid_body; c0_hsteps_nogrp
    refine wp_loop_group (ts := [i64])
      (fun rem (v, ()) mv => mv = m ∧ v.toNat ≤ s.core.cur_vars ∧ rem = s.core.cur_vars - v.toNat)
      ?_ (fun _ hL => by
        c0_hsteps!; exact hL s.core.cur_vars (0#64, ()) m ⟨rfl, Nat.zero_le _, rfl⟩)
    rintro L rem ⟨v, ⟨⟩⟩ mv hL ⟨rfl, hv_le, rfl⟩
    c0_hsplit
    · have hv_lt : v.toNat < s.core.cur_vars := by
        rw [Nat.mod_eq_of_lt (by omega)] at hc; exact hc
      have hv_fl : v.toNat < s.core.flags.length := by rw [hlen.core_ok.flags_len]; omega
      have hv_vals : (v <<< (1 : Nat)).toNat < s.core.vals.length := by
        rw [hlen.core_ok.vals_len]; c0_bound
      have hv1 : (v + 1#64).toNat = v.toNat + 1 := by c0_bound
      c0_hsteps_nogrp
      refine wp_join0 (fun mj => mj = mv)
        (fun _ mj hmj => by
          rcases hmj.symm with rfl; c0_hsteps!
          exact hL (s.core.cur_vars - (v + 1#64).toNat) (v + 1#64, ()) mv (by omega)
            ⟨rfl, by omega, rfl⟩)
        (fun Jx hJx => by
          c0_hsplit
          · c0_hsplit
            · c0_hsplit
              · c0_hsteps!; exact hQ true
              · c0_hsteps!; exact hJx mv rfl
            · c0_hsteps!; exact hJx mv rfl
          · c0_hsteps!; exact hJx mv rfl)
    · c0_hsteps!; exact hQ false

/-- Certifies `step13HasFactorCandsSpec` for Step-13 `full_has_factor_cands_fid`. -/
theorem full_has_factor_cands_fid_s13_wp (Γ : Env) :
    ∀ a m Q X, step13HasFactorCandsSpec a m Q X →
      Func.wp Γ full_has_factor_cands_fid_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  exact s13_cands_pred_wp (Or.inl rfl) hlen hm hQ

/-- Certifies `step13HasElimCandsSpec` for Step-13 `full_has_elim_cands_fid`. -/
theorem full_has_elim_cands_fid_s13_wp (Γ : Env) :
    ∀ a m Q X, step13HasElimCandsSpec a m Q X →
      Func.wp Γ full_has_elim_cands_fid_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  exact s13_cands_pred_wp (Or.inr rfl) hlen hm hQ

/-! ## 2. `full_bve_var_key_m7` -/

/-- Certifies `step13BveVarKeySpec` for Step-13 `full_bve_var_key_m7`. -/
theorem full_bve_var_key_m7_s13_wp (Γ : Env)
    (hOcc : M6EnvSpec Γ "full_dense_occ_cnt_fid" step13DenseOccCntSpec)
    (hFtoU : M6EnvSpec Γ "f64u_to_u64" f64uPure1Spec) :
    ∀ a m Q X, step13BveVarKeySpec a m Q X →
      Func.wp Γ full_bve_var_key_m7_body a m Q X := by
  rintro ⟨h, v, ⟨⟩⟩ m0 Q X ⟨c, s, R, rfl, hlen, hlay, hm0, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv_le := hlen.core_ok.cur_vars_le
  unfold Func.wp full_bve_var_key_m7_body
  c0_hsplit
  · c0_hsteps!; exact hQ 0#64
  · have hv_lt : v.toNat < s.core.cur_vars := by
      rw [Nat.mod_eq_of_lt (by omega)] at hc; omega
    have hv_sc : (v.setWidth 64).toNat < s.scratch.score.length := by
      rw [hlen.scratch_ok.score_len, m6_zext32_toNat]; omega
    have hv_qs : (v.setWidth 64).toNat < s.scratch.q_stamp.length := by
      rw [hlen.scratch_ok.q_stamp_len, m6_zext32_toNat]; omega
    have hv2_lt : (v <<< (1 : Nat)).toNat < 2 * s.core.cur_vars := by c0_bound
    have hv2o_lt : ((v <<< (1 : Nat)) ||| 1#32).toNat < 2 * s.core.cur_vars := by
      have h1 : ((v <<< (1 : Nat)) ||| 1#32).toNat = 2 * v.toNat + 1 := by
        rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, show (1#32 : BitVec 32).toNat = 1 from rfl,
          Nat.shiftLeft_eq, Nat.pow_one, Nat.mod_eq_of_lt (by omega)]
        apply Nat.eq_of_testBit_eq; intro k
        cases k with
        | zero => simp [Nat.testBit_zero, Nat.add_comm]
        | succ k =>
          rw [Nat.testBit_or, Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ,
            show ((1 : Nat) / 2).testBit k = false by simp,
            Bool.or_false, show (v.toNat * 2) / 2 = v.toNat by omega,
            show (2 * v.toNat + 1) / 2 = v.toNat by omega]
      omega
    c0_hsteps_nogrp
    s13b_call hOcc
    refine ⟨c, s, R, rfl, hlen, hlay, hv2_lt, hm0, fun _ => ?_⟩
    c0_hsteps_nogrp
    s13b_call hOcc
    refine ⟨c, s, R, rfl, hlen, hlay, hv2o_lt, hm0, fun _ => ?_⟩
    c0_hsteps_nogrp
    refine wp_join_state_pure (ts := [i64]) (α := BitVec 64) (fun x => (x, ())) (fun _ => True)
      (fun _ _ _ => by
        c0_hsteps_nogrp
        refine wp_join_state_pure (ts := [i64]) (α := BitVec 64) (fun x => (x, ())) (fun _ => True)
          (fun _ _ _ => by
            c0_hsteps_nogrp
            refine wp_join_state_pure (ts := [i64]) (α := BitVec 64) (fun x => (x, ()))
              (fun _ => True)
              (fun _ _ _ => by
                c0_hsteps_nogrp
                refine wp_join_state_pure (ts := [i64]) (α := BitVec 64) (fun x => (x, ()))
                  (fun _ => True)
                  (fun _ _ _ => by c0_hsteps!; exact hQ _)
                  (fun Jr hJr => by c0_hsplit <;> (c0_hsteps!; exact hJr _ trivial)))
              (fun Jr hJr => by
                c0_hsplit
                · c0_hsteps_nogrp; s13b_call hFtoU; intro rel
                  c0_hsteps_nogrp
                  refine wp_join_state_pure (ts := [i64]) (α := BitVec 64) (fun x => (x, ()))
                    (fun _ => True) (fun _ _ _ => by c0_hsteps!; exact hJr _ trivial)
                    (fun Jx hJx => by c0_hsplit <;> (c0_hsteps!; exact hJx _ trivial))
                · c0_hsteps!; exact hJr _ trivial))
          (fun Jn hJn => by c0_hsplit <;> (c0_hsteps!; exact hJn _ trivial)))
      (fun Jp hJp => by c0_hsplit <;> (c0_hsteps!; exact hJp _ trivial))

/-! ## 3. `full_fwd_scan_lit_m7` (`full_dense_occ_cnt_fid`) -/

private theorem s13_lit_compl_conflict {α : Nat → Bool} {l : Nat}
    (h1 : α (litVar l) = !litSign l) (h2 : α (litVar (l ^^^ 1)) = !litSign (l ^^^ 1)) :
    False := by
  simp only [litVar, litSign] at h1 h2
  rw [fullInv_var_xor1 l, m6_xor1_mod2 l] at h2
  rcases Nat.mod_two_eq_zero_or_one l with hm | hm <;> cases h : α (l / 2) <;> simp_all

private theorem s13_selfsub_bin {F : CNF Nat} {C : List Nat} {scan_lit ot : Nat}
    (hC : F.EntailsClause (cnfClause C)) (hbin : F.EntailsClause (cnfClause [scan_lit, ot]))
    (hscan : scan_lit ∈ C) (hne : ot ^^^ 1 ≠ scan_lit) :
    F.EntailsClause (cnfClause (C.filter (· != (ot ^^^ 1)))) := by
  rw [CNF.entails_clause_def] at hC hbin ⊢; intro α hα
  have hb := (clause_sat_cnfClause_iff α _).mp (hbin α hα)
  have hc := (clause_sat_cnfClause_iff α _).mp (hC α hα)
  rw [clause_sat_cnfClause_iff]; obtain ⟨lb, hlb, hsb⟩ := hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hlb
  rcases hlb with hlb | hlb
  · rw [hlb] at hsb; exact ⟨scan_lit, List.mem_filter.mpr ⟨hscan, bne_iff_ne.mpr hne.symm⟩, hsb⟩
  · obtain ⟨lc, hlc, hsc⟩ := hc
    refine ⟨lc, List.mem_filter.mpr ⟨hlc, bne_iff_ne.mpr fun heq => ?_⟩, hsc⟩
    rw [heq] at hsc; rw [hlb] at hsb; exact s13_lit_compl_conflict hsb hsc

private theorem s13_selfsub_clause {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (hl0 : k.cur_level = 0)
    {C D : List Nat} {drop : Nat} (hC : (cnfOfClauses F_cur).EntailsClause (cnfClause C))
    (hD : (cnfOfClauses F_cur).EntailsClause (cnfClause D))
    (hD_lt : ∀ l ∈ D, l < 2 * k.cur_vars) (hD_nd : (D.map (· / 2)).Nodup)
    (hneg_mem : drop ^^^ 1 ∈ D)
    (hD_ok : ∀ l ∈ D, l ∈ C ∨ k.vals[l]?.getD 0#8 = 0xFF#8 ∨ l = drop ^^^ 1) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause (C.filter (· != drop))) := by
  have hdrop_not_D : drop ∉ D := by
    intro hmem; obtain ⟨i, hi, heq1⟩ := List.mem_iff_getElem.mp hmem
    obtain ⟨j, hj, heq2⟩ := List.mem_iff_getElem.mp hneg_mem
    have hij : i ≠ j := fun h => by
      subst h; rw [heq1] at heq2
      have hmod := m6_xor1_mod2 drop; have := congrArg (· % 2) heq2; omega
    have hdiv : (D.map (· / 2))[i]'(by simp [hi]) = (D.map (· / 2))[j]'(by simp [hj]) := by
      simp only [List.getElem_map, heq1, heq2, fullInv_var_xor1]
    exact hij (by
      rcases Nat.lt_trichotomy i j with hlt | rfl | hgt
      · exact False.elim ((List.pairwise_iff_getElem.mp hD_nd) i j (by simp [hi]) (by simp [hj])
          hlt hdiv)
      · rfl
      · exact False.elim ((List.pairwise_iff_getElem.mp hD_nd) j i (by simp [hj]) (by simp [hi])
          hgt hdiv.symm))
  rw [CNF.entails_clause_def] at hC hD ⊢; intro α hα
  have hd := (clause_sat_cnfClause_iff α _).mp (hD α hα)
  have hc := (clause_sat_cnfClause_iff α _).mp (hC α hα)
  rw [clause_sat_cnfClause_iff]; obtain ⟨ld, hld, hsd⟩ := hd
  rcases hD_ok ld hld with hmemC | hfalse | hcompl
  · exact ⟨ld, List.mem_filter.mpr ⟨hmemC, bne_iff_ne.mpr (fun heq => hdrop_not_D (heq ▸ hld))⟩,
      hsd⟩
  · exfalso
    have hneg := m6_vals_neg_entails hw hl0 (hD_lt ld hld) hfalse
    have hsn := (clause_sat_cnfClause_iff α _).mp ((CNF.entails_clause_def.mp hneg) α hα)
    obtain ⟨l', hl', hs'⟩ := hsn; rw [List.mem_singleton] at hl'; rw [hl'] at hs'
    exact s13_lit_compl_conflict hsd hs'
  · obtain ⟨lc, hlc, hsc⟩ := hc
    refine ⟨lc, List.mem_filter.mpr ⟨hlc, bne_iff_ne.mpr fun heq => ?_⟩, hsc⟩
    rw [heq] at hsc; rw [hcompl] at hsd; exact s13_lit_compl_conflict hsc hsd

private theorem s13_scan_lm_mem {c : FullCfg} {s0 : FullState} {cref : BitVec 32}
    (hlen0 : s0.LengthsOk c) (hcv : s0.core.cur_vars ≤ c.max_vars)
    (hlm_iff : ∀ x < 2 * s0.core.cur_vars,
      s0.core.lit_mark[x]?.getD 0#8 ≠ 0#8 ↔ x ∈ fullArenaClauseLits s0 cref.toNat)
    {x : BitVec 32} (hx_lt : x.toNat < 2 * s0.core.cur_vars) {idx : Nat}
    (heq : idx = x.toNat) (hb : idx < s0.core.lit_mark.length)
    (hnz : BitVec.setWidth 32 (s0.core.lit_mark[idx]'hb) ≠ 0#32) :
    x.toNat ∈ fullArenaClauseLits s0 cref.toNat := by
  apply (hlm_iff x.toNat hx_lt).mp
  have hlt_l : x.toNat < s0.core.lit_mark.length := by rw [hlen0.core_ok.lit_mark_len]; omega
  rw [List.getElem?_eq_getElem hlt_l, Option.getD_some]; intro heq0; apply hnz
  rw [m6_getElem_congr heq hb hlt_l, heq0]; rfl

private theorem s13_scan_vals_ff {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 : FullState} (hlen0 : s0.LengthsOk c) (hw0 : FullWitnessInv c F0 F_cur s0.core)
    {dl : BitVec 32} (hdl_lt : dl.toNat < 2 * s0.core.cur_vars) {idx : Nat}
    (heq : idx = dl.toNat) (hb : idx < s0.core.vals.length)
    (hneg : ¬ ((0#32).sle ((s0.core.vals[idx]'hb).signExtend 32) = true)) :
    s0.core.vals[dl.toNat]?.getD 0#8 = 0xFF#8 := by
  have hcv := hlen0.core_ok.cur_vars_le
  have hlt_v : dl.toNat < s0.core.vals.length := by rw [hlen0.core_ok.vals_len]; omega
  have hdom := hw0.vals_domain dl.toNat hdl_lt
  rw [List.getElem?_eq_getElem hlt_v, Option.getD_some] at hdom ⊢
  rcases hdom with h0 | h1 | hff
  · exfalso; apply hneg; rw [m6_getElem_congr heq hb hlt_v, h0]; decide
  · exfalso; apply hneg; rw [m6_getElem_congr heq hb hlt_v, h1]; decide
  · exact hff

/-- Certifies `step13FwdScanLitSpec` for Step-13 `full_fwd_scan_lit_m7`. -/
theorem full_fwd_scan_lit_m7_s13_wp (Γ : Env)
    (hOcc : M6EnvSpec Γ "full_dense_occ_cnt_fid" step13DenseOccCntSpec) :
    ∀ a m Q X, step13FwdScanLitSpec a m Q X →
      Func.wp Γ full_fwd_scan_lit_m7_body a m Q X := by
  rintro ⟨h, cref, sz, scan_lit, check_bins, ⟨⟩⟩ m0 Q X
    ⟨c, F0, F_cur, s0, R, rfl, hlen0, hw0, hl0, hdm0, hnd0, href0, hng0, hsz0, hscan_lt,
      hcb_mem, hlm_iff, hm0, hQ⟩
  have hmx := c.hmaxv; have hwc := c.hwcap; have harc := c.harena
  unfold dimacsBound at hmx hwc harc
  have hcv_le := hlen0.core_ok.cur_vars_le; have hwlen_le := hlen0.core_ok.wlen_le
  have hdw0 : DenseWatchesInv F_cur s0.core := by
    have := hw0.watches; unfold ModeWatchesInv at this; rwa [ite_eq_right hdm0] at this
  have hbd := hdw0.layout.bounds scan_lit.toNat hscan_lt
  have hlv0 : (scan_lit.setWidth 64 <<< (1 : Nat)).toNat < s0.core.wvec.length := by
    rw [hlen0.core_ok.wvec_len]; c0_bound
  have hlv1 : (scan_lit.setWidth 64 <<< (1 : Nat) + 1#64).toNat < s0.core.wvec.length := by
    rw [hlen0.core_ok.wvec_len]; c0_bound
  unfold Func.wp full_fwd_scan_lit_m7_body
  c0_hsteps_nogrp
  · c0_hsteps!; exact hQ 0xFFFFFFFF#32 (Or.inl rfl)
  · c0_hsteps_nogrp
    s13b_call hOcc
    refine ⟨c, s0, R, rfl, hlen0, hdw0.layout, hscan_lt, hm0, fun _ => ?_⟩
    c0_hsplit
    · c0_hsteps!; exact hQ 0xFFFFFFFF#32 (Or.inl rfl)
    · let off_s := (s0.core.wvec[(scan_lit.setWidth 64 <<< (1 : Nat)).toNat]'hlv0).setWidth 64
      let sz_s := (s0.core.wvec[(scan_lit.setWidth 64 <<< (1 : Nat) + 1#64).toNat]'hlv1).setWidth 64
      let end_s := off_s + sz_s
      have hoff_eq : off_s.toNat = fullWatchOffCore s0.core scan_lit.toNat := by
        unfold off_s fullWatchOffCore
        rw [List.getElem?_eq_getElem (by rw [hlen0.core_ok.wvec_len]; omega), Option.getD_some,
          m6_zext32_toNat]
        exact congrArg BitVec.toNat (m6_getElem_congr (by c0_bound) _ _)
      have hsz_s_eq : sz_s.toNat = fullWatchSizeCore s0.core scan_lit.toNat := by
        unfold sz_s fullWatchSizeCore
        rw [List.getElem?_eq_getElem (by rw [hlen0.core_ok.wvec_len]; omega), Option.getD_some,
          m6_zext32_toNat]
        exact congrArg BitVec.toNat (m6_getElem_congr (by c0_bound) _ _)
      have hend_eq : end_s.toNat = off_s.toNat + sz_s.toNat := by
        dsimp only [end_s]; rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
      have hsum_c0 :
          ((s0.core.wvec[2 * scan_lit.toNat % 2 ^ 64]'(by
              rw [hlen0.core_ok.wvec_len]; omega)).toNat +
            (s0.core.wvec[(2 * scan_lit.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
              rw [hlen0.core_ok.wvec_len]; simp; omega)).toNat) % 2 ^ 64 = end_s.toNat := by
        have h1 : (s0.core.wvec[2 * scan_lit.toNat % 2 ^ 64]'(by
            rw [hlen0.core_ok.wvec_len]; omega)).toNat = off_s.toNat := by
          rw [hoff_eq]; unfold fullWatchOffCore
          rw [List.getElem?_eq_getElem (by rw [hlen0.core_ok.wvec_len]; omega), Option.getD_some]
          exact congrArg BitVec.toNat (m6_getElem_congr (by omega) _ _)
        have h2 : (s0.core.wvec[(2 * scan_lit.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
            rw [hlen0.core_ok.wvec_len]; simp; omega)).toNat = sz_s.toNat := by
          rw [hsz_s_eq]; unfold fullWatchSizeCore
          rw [List.getElem?_eq_getElem (by rw [hlen0.core_ok.wvec_len]; omega), Option.getD_some]
          exact congrArg BitVec.toNat (m6_getElem_congr (by simp; omega) _ _)
        rw [h1, h2, Nat.mod_eq_of_lt (by omega), hend_eq]
      have hent_C := hw0.arena.entails cref.toNat href0 hng0
      c0_hsteps_nogrp
      refine wp_loop_break_group (brkTs := [i64]) (lpTs := [i64])
        (fun _ mb => mb = m0)
        (fun rem (p, ()) mp =>
          mp = m0 ∧ p.toNat ≤ end_s.toNat ∧ rem = end_s.toNat - p.toNat ∧
          DenseWatchSliceOk F_cur s0.core scan_lit.toNat p.toNat rem)
        ?_ ?_ ?_
      · rintro _ ⟨_, ⟨⟩⟩ mb hmb; subst mb; c0_hsteps!; exact hQ 0xFFFFFFFF#32 (Or.inl rfl)
      · rintro B L rem ⟨p, ⟨⟩⟩ mp hB hL ⟨rfl, hp_le, hrem, hslice⟩
        c0_hsplit
        {
        have hp_lt : p.toNat < end_s.toNat := by rw [hsum_c0] at hc; exact hc
        have hpw : p.toNat < s0.core.wstk.length := by rw [hlen0.core_ok.wstk_len_arr]; omega
        have hp1_nat : (p + 1#64).toNat = p.toNat + 1 := by c0_bound
        cases hslice with
        | empty => omega
        | @bin _ rem1 w0 hwp hflag _ hot_lt hent_bin hrest =>
          have hw0_eq : s0.core.wstk[p.toNat]'hpw = w0 := by
            rw [List.getElem?_eq_getElem hpw] at hwp; exact Option.some.inj hwp
          let ot := w0 &&& 0x7FFFFFFF#32
          have hot_lt' : ot.toNat < 2 * s0.core.cur_vars := hot_lt
          have hot_lm : (ot.setWidth 64).toNat < s0.core.lit_mark.length := by
            rw [hlen0.core_ok.lit_mark_len, m6_zext32_toNat]; omega
          have hotn_lt : (ot ^^^ 1#32).toNat < 2 * s0.core.cur_vars := by
            change ot.toNat ^^^ 1 < 2 * s0.core.cur_vars; have := fullInv_var_xor1 ot.toNat; omega
          have hotn_lm : ((ot ^^^ 1#32).setWidth 64).toNat < s0.core.lit_mark.length := by
            rw [hlen0.core_ok.lit_mark_len, m6_zext32_toNat]; omega
          have hot_lm_c0 : (BitVec.setWidth 64 (s0.core.wstk[p.toNat] &&& 0x7FFFFFFF#32)).toNat <
              s0.core.lit_mark.length := by rw [hw0_eq]; exact hot_lm
          have hotn_lm_c0 : (BitVec.setWidth 64 ((s0.core.wstk[p.toNat] &&&
              0x7FFFFFFF#32) ^^^ 1#32)).toNat < s0.core.lit_mark.length := by
            rw [hw0_eq]; exact hotn_lm
          c0_hsplit
          · refine wp_join0 (P := fun mj => mj = mp)
              (fun _ mj hmj => by
                rcases hmj.symm with rfl; c0_hsteps!
                exact hL rem1 (p + 1#64, ()) mp (by omega)
                  ⟨rfl, by omega, by omega, by rw [hp1_nat]; exact hrest⟩)
              (fun J44 hJ44 => by
                c0_hsplit
                · have hcb_t : check_bins = true := by simpa using hc
                  c0_hsplit
                  · c0_hsteps!; exact hQ 0xFFFFFFFE#32 (Or.inr (Or.inl rfl))
                  · have hot_c0 : (s0.core.wstk[p.toNat]'hpw &&& 0x7FFFFFFF#32) = ot := by
                      dsimp only [ot]; rw [hw0_eq]
                    have hne_c0 : (s0.core.wstk[p.toNat]'hpw &&& 0x7FFFFFFF#32 ^^^ 1#32) =
                        ot ^^^ 1#32 := by rw [hot_c0]
                    c0_hsplit
                    · have hne_scan : (ot ^^^ 1#32).toNat ≠ scan_lit.toNat := fun h =>
                        hc (hne_c0.symm ▸ BitVec.eq_of_toNat_eq h)
                      c0_hsplit
                      · have hmem_drop : (ot ^^^ 1#32).toNat ∈
                            fullArenaClauseLits s0 cref.toNat := by
                          apply (hlm_iff _ hotn_lt).mp
                          have hlt_l : (ot ^^^ 1#32).toNat < s0.core.lit_mark.length := by
                            rw [hlen0.core_ok.lit_mark_len]; omega
                          rw [List.getElem?_eq_getElem hlt_l, Option.getD_some]
                          intro heq0; apply hc
                          have hlm_eq : s0.core.lit_mark[(s0.core.wstk[p.toNat]'hpw &&&
                              0x7FFFFFFF#32).toNat ^^^ 1]'(by
                                rw [hw0_eq]; change (ot ^^^ 1#32).toNat < _; omega) =
                              s0.core.lit_mark[(ot ^^^ 1#32).toNat]'hlt_l :=
                            m6_getElem_congr (congrArg BitVec.toNat hne_c0) _ _
                          have h0 : BitVec.setWidth 32
                              (s0.core.lit_mark[(s0.core.wstk[p.toNat]'hpw &&&
                                0x7FFFFFFF#32).toNat ^^^ 1]'(by
                                  rw [hw0_eq]; change (ot ^^^ 1#32).toNat < _; omega)) = 0#32 := by
                            rw [hlm_eq, heq0]; rfl
                          exact h0
                        c0_hsteps!
                        exact hne_c0.symm ▸ hQ (ot ^^^ 1#32) (Or.inr (Or.inr ⟨hmem_drop,
                          s13_selfsub_bin hent_C hent_bin (hcb_mem hcb_t) hne_scan⟩))
                      · c0_hsteps!; exact hJ44 mp rfl
                    · c0_hsteps!; exact hJ44 mp rfl
                · c0_hsteps!; exact hJ44 mp rfl)
          · rw [hw0_eq] at hc; exact absurd hc hflag
        | @occ _ rem2 w0 cr hwp hwp1 hflag _ _ href_cr hrest =>
          have hw0_eq : s0.core.wstk[p.toNat]'hpw = w0 := by
            rw [List.getElem?_eq_getElem hpw] at hwp; exact Option.some.inj hwp
          have hp1_w : (p + 1#64).toNat < s0.core.wstk.length := by
            rw [hlen0.core_ok.wstk_len_arr]; omega
          have hp1_c0 : (p.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 = p.toNat + 1 := by
            simp; omega
          have hcr_eq : s0.core.wstk[(p.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
              rw [hlen0.core_ok.wstk_len_arr]; omega) = cr := by
            rw [List.getElem?_eq_getElem (by rw [hlen0.core_ok.wstk_len_arr]; omega)] at hwp1
            exact (m6_getElem_congr hp1_c0 _ _).trans (Option.some.inj hwp1)
          have hp2_nat : (p + 1#64 + 1#64).toNat = p.toNat + 2 := by c0_bound
          have hrest' : DenseWatchSliceOk F_cur s0.core scan_lit.toNat
              (p + 1#64 + 1#64).toNat rem2 := by rw [hp2_nat]; exact hrest
          have hwf_cr := hw0.arena.refs_wf cr.toNat href_cr
          have hal_le := hlen0.core_ok.arena_len_le
          have har_len_cr : cr.toNat < s0.core.arena.length := by
            rw [hlen0.core_ok.arena_len_arr]; omega
          have hcr_ar : (cr.setWidth 64).toNat < s0.core.arena.length := by
            rw [hlen0.core_ok.arena_len_arr, m6_zext32_toNat]; omega
          c0_hsplit
          · rw [hw0_eq] at hc; exact absurd hflag hc
          · c0_hsplit
            · rw [hsum_c0] at hc; simp at hc; omega
            · c0_hsplit
              · c0_hsteps!; exact hL rem2 (p + 1#64 + 1#64, ()) mp (by omega)
                  ⟨rfl, by omega, by omega, hrest'⟩
              · c0_hsplit
                · c0_hsteps!; exact hL rem2 (p + 1#64 + 1#64, ()) mp (by omega)
                    ⟨rfl, by omega, by omega, hrest'⟩
                · simp only [hcr_eq] at hc ⊢
                  have hng_cr : fullArenaClauseGarb s0 cr.toNat = false := by
                    unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
                    rw [List.getElem?_eq_getElem har_len_cr, Option.getD_some]
                    have h0 : (s0.core.arena[cr.toNat]'har_len_cr &&& 0x00080000#32) = 0#32 := by
                      have hsub : (0x00080000#32 : BitVec 32) &&&
                          ((524288 : BitVec 32) ||| (4194304 : BitVec 32)) =
                          0x00080000#32 := by decide
                      have h0r : (0 : BitVec 32) &&& 0x00080000#32 = 0#32 := rfl
                      have hc' := congrArg (· &&& 0x00080000#32) hc
                      rw [BitVec.and_assoc, BitVec.and_comm _ 0x00080000#32, hsub, h0r] at hc'
                      exact hc'
                    rw [h0]; rfl
                  have hcr2_ar : (cr.setWidth 64 + 2#64).toNat < s0.core.arena.length := by
                    rw [hlen0.core_ok.arena_len_arr]; c0_bound
                  have hcr_p1' : s0.core.wstk[(p + (1 : BitVec 64)).toNat]'(by
                      rw [hlen0.core_ok.wstk_len_arr, BitVec.toNat_add,
                        show ((1 : BitVec 64)).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
                      omega) = cr := by
                    have h1 : (p + (1 : BitVec 64)).toNat =
                        (p.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 := BitVec.toNat_add _ _
                    exact (m6_getElem_congr h1 _ _).trans hcr_eq
                  have hdsz_bd : (BitVec.setWidth 64 (s0.core.wstk[(p + (1 : BitVec 64)).toNat]'(by
                      rw [hlen0.core_ok.wstk_len_arr, BitVec.toNat_add,
                        show ((1 : BitVec 64)).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
                      omega)) + (2 : BitVec 64)).toNat < s0.core.arena.length := by
                    rw [hcr_p1']; simpa [show ((2 : BitVec 64)) = 2#64 from rfl] using hcr2_ar
                  let dsz := s0.core.arena[(cr.setWidth 64 + 2#64).toNat]'hcr2_ar
                  have hdsz_eq : dsz.toNat = fullArenaClauseSizeCore s0.core cr.toNat := by
                    unfold dsz fullArenaClauseSizeCore
                    rw [List.getElem?_eq_getElem (by rw [hlen0.core_ok.arena_len_arr]; omega),
                      Option.getD_some]
                    exact congrArg BitVec.toNat (m6_getElem_congr (by c0_bound) _ _)
                  have hdsz_idx : (s0.core.wstk[(p.toNat + BitVec.toNat (1 : BitVec 64)) %
                      2 ^ 64].toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64 =
                      (cr.setWidth 64 + 2#64).toNat := by rw [hcr_eq]; c0_bound
                  have hdsz_eq' : s0.core.arena[(s0.core.wstk[(p.toNat +
                      BitVec.toNat (1 : BitVec 64)) % 2 ^ 64].toNat +
                      BitVec.toNat (2 : BitVec 64)) % 2 ^ 64] = dsz :=
                    m6_getElem_congr hdsz_idx _ _
                  c0_hsplit
                  · c0_hsteps!; exact hL rem2 (p + 1#64 + 1#64, ()) mp (by omega)
                      ⟨rfl, by omega, by omega, hrest'⟩
                  · c0_hsteps_nogrp
                    refine wp_loop_break_group (brkTs := [i32, i32, i32]) (lpTs := [i32, i32])
                      (fun (miss_b, cand_b, j_b, ()) ms => ms = mp ∧
                        (miss_b = 0#32 → j_b = dsz ∧ (cand_b ≠ 0xFFFFFFFF#32 →
                          cand_b.toNat ∈ fullArenaClauseLits s0 cref.toNat ∧
                          cand_b.toNat ^^^ 1 ∈ fullArenaClauseLits s0 cr.toNat ∧
                          ∀ t < dsz.toNat,
                            let dl := (s0.core.arena[cr.toNat + 3 + t]?.getD 0#32).toNat
                            dl ∈ fullArenaClauseLits s0 cref.toNat ∨
                            s0.core.vals[dl]?.getD 0#8 = 0xFF#8 ∨ dl = cand_b.toNat ^^^ 1)))
                      (fun rem_j (cand_j, j, ()) mj => mj = mp ∧
                        j.toNat ≤ dsz.toNat ∧ rem_j = dsz.toNat - j.toNat ∧
                        (cand_j = 0xFFFFFFFF#32 → ∀ t < j.toNat,
                          let dl := (s0.core.arena[cr.toNat + 3 + t]?.getD 0#32).toNat
                          dl ∈ fullArenaClauseLits s0 cref.toNat ∨
                          s0.core.vals[dl]?.getD 0#8 = 0xFF#8) ∧
                        (cand_j ≠ 0xFFFFFFFF#32 →
                          cand_j.toNat ∈ fullArenaClauseLits s0 cref.toNat ∧
                          cand_j.toNat ^^^ 1 ∈ fullArenaClauseLits s0 cr.toNat ∧
                          ∀ t < j.toNat,
                            let dl := (s0.core.arena[cr.toNat + 3 + t]?.getD 0#32).toNat
                            dl ∈ fullArenaClauseLits s0 cref.toNat ∨
                            s0.core.vals[dl]?.getD 0#8 = 0xFF#8 ∨ dl = cand_j.toNat ^^^ 1))
                      ?_ ?_ ?_
                    · rintro _ ⟨miss_b, cand_b, j_b, ⟨⟩⟩ ms ⟨hm_s, hpost⟩
                      rcases hm_s.symm with rfl; c0_hsplit
                      · obtain ⟨_, hcand⟩ := hpost hc; c0_hsplit
                        · c0_hsteps!; exact hQ 0xFFFFFFFE#32 (Or.inr (Or.inl rfl))
                        · obtain ⟨hmemC, hnegD, hallD⟩ := hcand hc
                          have hD_ok : ∀ l ∈ fullArenaClauseLits s0 cr.toNat,
                              l ∈ fullArenaClauseLits s0 cref.toNat ∨
                              s0.core.vals[l]?.getD 0#8 = 0xFF#8 ∨ l = cand_b.toNat ^^^ 1 := by
                            intro l hl; change l ∈ fullArenaClauseLitsCore s0.core cr.toNat at hl
                            rw [mem_fullArenaClauseLitsCore_iff
                              (by rw [hlen0.core_ok.arena_len_arr]; omega)] at hl
                            obtain ⟨t, ht, rfl⟩ := hl
                            have hlt_t : cr.toNat + 3 + t < s0.core.arena.length := by
                              rw [hlen0.core_ok.arena_len_arr]; omega
                            simpa [List.getElem?_eq_getElem hlt_t] using hallD t (by omega)
                          c0_hsteps!
                          exact hQ cand_b (Or.inr (Or.inr ⟨hmemC, s13_selfsub_clause hw0 hl0
                            hent_C (hw0.arena.entails cr.toNat href_cr hng_cr)
                            (hw0.arena.lits_lt cr.toNat href_cr hng_cr)
                            (hnd0 cr.toNat href_cr hng_cr) hnegD hD_ok⟩))
                      · c0_hsteps!; exact hL rem2 (p + 1#64 + 1#64, ()) mp (by omega)
                          ⟨rfl, by omega, by omega, hrest'⟩
                    · rintro Bj Lj rem_j ⟨cand_j, j, ⟨⟩⟩ mj hBj hLj
                        ⟨rfl, hj_le, rfl, hc_none, hc_some⟩
                      c0_hsplit
                      {
                      have hj_lt : j.toNat < dsz.toNat := by rw [hdsz_eq'] at hc; exact hc
                      have hcrj : (cr.setWidth 64 + 3#64 + j.setWidth 64).toNat <
                          s0.core.arena.length := by
                        rw [hlen0.core_ok.arena_len_arr]; c0_bound
                      let dl := s0.core.arena[(cr.setWidth 64 + 3#64 + j.setWidth 64).toNat]'hcrj
                      have hdl_eq : s0.core.arena[cr.toNat + 3 + j.toNat]?.getD 0#32 = dl := by
                        have hal := hlen0.core_ok.arena_len_arr
                        rw [List.getElem?_eq_getElem (by rw [hal]; omega), Option.getD_some]
                        exact m6_getElem_congr (by c0_bound) _ _
                      have hdl_memD : dl.toNat ∈ fullArenaClauseLits s0 cr.toNat := by
                        change dl.toNat ∈ fullArenaClauseLitsCore s0.core cr.toNat
                        rw [mem_fullArenaClauseLitsCore_iff
                          (by rw [hlen0.core_ok.arena_len_arr]; omega)]
                        exact ⟨j.toNat, by omega,
                          congrArg BitVec.toNat (m6_getElem_congr (by c0_bound) _ _)⟩
                      have hdl_lt := hw0.arena.lits_lt cr.toNat href_cr hng_cr _ hdl_memD
                      have hdln_lt : (dl ^^^ 1#32).toNat < 2 * s0.core.cur_vars := by
                        change dl.toNat ^^^ 1 < 2 * s0.core.cur_vars
                        have := fullInv_var_xor1 dl.toNat; omega
                      have hdl_idx : (s0.core.wstk[(p.toNat + BitVec.toNat (1 : BitVec 64)) %
                          2 ^ 64].toNat + BitVec.toNat (3 : BitVec 64) + j.toNat) % 2 ^ 64 =
                          (cr.setWidth 64 + 3#64 + j.setWidth 64).toNat := by rw [hcr_eq]; c0_bound
                      have hdl_c0_eq' : s0.core.arena[(s0.core.wstk[(p.toNat +
                          BitVec.toNat (1 : BitVec 64)) % 2 ^ 64].toNat +
                          BitVec.toNat (3 : BitVec 64) + j.toNat) % 2 ^ 64]'(by
                            rw [hdl_idx]; exact hcrj) = dl :=
                        m6_getElem_congr hdl_idx _ _
                      have hj1 : (j + 1#32).toNat = j.toNat + 1 := by c0_bound
                      rw [hcr_p1']
                      have hdl_c0_cr :
                          s0.core.arena[(cr.toNat + BitVec.toNat (3 : BitVec 64) +
                            j.toNat) % 2 ^ 64]'(by
                              rw [show (cr.toNat + BitVec.toNat (3 : BitVec 64) + j.toNat) %
                                2 ^ 64 = (cr.setWidth 64 + 3#64 + j.setWidth 64).toNat by c0_bound]
                              exact hcrj) = dl :=
                        m6_getElem_congr (by c0_bound) _ _
                      have hdl_c0_lm : (BitVec.setWidth 64
                          (s0.core.arena[(BitVec.setWidth 64 cr + 3#64 +
                            j.setWidth 64).toNat]'hcrj)).toNat <
                          s0.core.lit_mark.length := by
                        rw [hlen0.core_ok.lit_mark_len, m6_zext32_toNat]
                        change dl.toNat < 2 * c.max_vars; omega
                      have hdl_c0_v : (BitVec.setWidth 64
                          (s0.core.arena[(BitVec.setWidth 64 cr + 3#64 +
                            j.setWidth 64).toNat]'hcrj)).toNat <
                          s0.core.vals.length := by
                        rw [hlen0.core_ok.vals_len, m6_zext32_toNat]
                        change dl.toNat < 2 * c.max_vars; omega
                      have hdln_c0_lm : (BitVec.setWidth 64
                          ((s0.core.arena[(BitVec.setWidth 64 cr + 3#64 +
                            j.setWidth 64).toNat]'hcrj) ^^^ 1#32)).toNat <
                          s0.core.lit_mark.length := by
                        rw [hlen0.core_ok.lit_mark_len, m6_zext32_toNat]
                        change (dl ^^^ 1#32).toNat < 2 * c.max_vars; omega
                      c0_hsteps_nogrp
                      refine wp_join_state_pure (ts := [i32, i32]) (α := BitVec 32 × BitVec 32)
                        (fun x => (x.1, x.2, ()))
                        (fun x => (x.2 = 0xFFFFFFFF#32 → ∀ t < j.toNat + 1,
                            let dl := (s0.core.arena[cr.toNat + 3 + t]?.getD 0#32).toNat
                            dl ∈ fullArenaClauseLits s0 cref.toNat ∨
                            s0.core.vals[dl]?.getD 0#8 = 0xFF#8) ∧
                          (x.2 ≠ 0xFFFFFFFF#32 → x.2.toNat ∈ fullArenaClauseLits s0 cref.toNat ∧
                            x.2.toNat ^^^ 1 ∈ fullArenaClauseLits s0 cr.toNat ∧ ∀ t < j.toNat + 1,
                            let dl := (s0.core.arena[cr.toNat + 3 + t]?.getD 0#32).toNat
                            dl ∈ fullArenaClauseLits s0 cref.toNat ∨
                            s0.core.vals[dl]?.getD 0#8 = 0xFF#8 ∨ dl = x.2.toNat ^^^ 1))
                        (fun _ ⟨_, cand_n⟩ ⟨hc_n, hc_s⟩ => by
                          c0_hsteps!
                          exact hLj (dsz.toNat - (j + 1#32).toNat) (cand_n, j + 1#32, ()) mj
                            (by omega) ⟨rfl, by omega, rfl, by rw [hj1]; exact hc_n,
                              by rw [hj1]; exact hc_s⟩)
                        (fun J75 hJ75 => by
                          have hstep_keep : (dl.toNat ∈ fullArenaClauseLits s0 cref.toNat ∨
                              s0.core.vals[dl.toNat]?.getD 0#8 = 0xFF#8) →
                              J75 (0#32, cand_j, ()) mj :=
                            fun hok => hJ75 (0#32, cand_j)
                              ⟨fun hcn t ht => by
                                 rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp ht) with h | h
                                 · exact hc_none hcn t h
                                 · subst h; rw [hdl_eq]; exact hok,
                               fun hcs => by
                                 obtain ⟨hmC, hnD, hall⟩ := hc_some hcs
                                 refine ⟨hmC, hnD, fun t ht => ?_⟩
                                 rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp ht) with h | h
                                 · exact hall t h
                                 · subst h; rw [hdl_eq]; exact hok.imp id (fun hf => Or.inl hf)⟩
                          c0_hsplit
                          · c0_hsplit
                            · c0_hsplit
                              · have hlm_dln_nz := hc
                                c0_hsplit
                                · have hcn : cand_j = 0xFFFFFFFF#32 := hc
                                  have hne_ff : (dl ^^^ 1#32) ≠ 0xFFFFFFFF#32 := fun h => by
                                    have : (dl ^^^ 1#32).toNat = 4294967295 :=
                                      congrArg BitVec.toNat h
                                    omega
                                  have hmem_dln : (dl ^^^ 1#32).toNat ∈
                                      fullArenaClauseLits s0 cref.toNat :=
                                    s13_scan_lm_mem hlen0 hcv_le hlm_iff hdln_lt
                                      (by rw [congrArg BitVec.toNat hdl_c0_cr, BitVec.toNat_xor,
                                        show (1#32).toNat = 1 from rfl])
                                      _ hlm_dln_nz
                                  have hneg_eq : (dl ^^^ 1#32).toNat ^^^ 1 = dl.toNat := by
                                    change (dl.toNat ^^^ 1) ^^^ 1 = dl.toNat
                                    exact litNeg_litNeg dl.toNat
                                  c0_hsteps!
                                  exact hJ75 (0#32, dl ^^^ 1#32) ⟨fun h => absurd h hne_ff, fun _ =>
                                    ⟨hmem_dln, by rw [hneg_eq]; exact hdl_memD, fun t ht => by
                                      rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp ht) with h | h
                                      · exact (hc_none hcn t h).imp id (fun hf => Or.inl hf)
                                      · subst h; rw [hdl_eq]; exact Or.inr (Or.inr (by
                                          change dl.toNat = (dl ^^^ 1#32).toNat ^^^ 1
                                          exact hneg_eq.symm))⟩⟩
                                · c0_hsteps!
                                  exact hBj (1#32, cand_j, j, ()) mj ⟨rfl, fun h => by cases h⟩
                              · c0_hsteps!
                                exact hBj (1#32, cand_j, j, ()) mj ⟨rfl, fun h => by cases h⟩
                            · c0_hsteps!
                              exact hstep_keep (Or.inr (s13_scan_vals_ff hlen0 hw0 hdl_lt
                                (congrArg BitVec.toNat hdl_c0_cr) _ (by rw [hc]; decide)))
                          · c0_hsteps!
                            exact hstep_keep (Or.inl (s13_scan_lm_mem hlen0 hcv_le hlm_iff hdl_lt
                              (congrArg BitVec.toNat hdl_c0_cr) _ hc))) }
                      {
                        rw [hdsz_eq'] at hc
                        have hj_eq : j = dsz := BitVec.eq_of_toNat_eq (by omega)
                        c0_hsteps!; exact hBj (0#32, cand_j, j, ()) mj
                          ⟨rfl, fun _ => ⟨hj_eq, by subst hj_eq; exact hc_some⟩⟩ }
                    · intro _ Lj _ hLj; c0_hsteps!
                      exact hLj dsz.toNat (0xFFFFFFFF#32, 0#32, ()) mp
                        ⟨rfl, Nat.zero_le _, by simp, fun _ _ ht => by simp at ht,
                         fun h => absurd rfl h⟩ }
        · c0_hsteps!; exact hB (_, ()) mp rfl
      · intro _ L _ hL; c0_hsteps!
        exact hL sz_s.toNat (off_s, ()) m0 ⟨rfl, by omega, by omega, by
          rw [hoff_eq, hsz_s_eq]; exact hdw0.slices scan_lit.toNat hscan_lt⟩

/-! ## 4. `full_fwd_connect_subsumer_m7` (`full_dense_occ_cnt_fid`) -/

private theorem s13_sz_and_mask_eq {sz : BitVec 32} (hlt : sz.toNat < 2 ^ 31) :
    (sz &&& 0x7FFFFFFF#32) = sz := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (0x7FFFFFFF#32 : BitVec 32).toNat = 2 ^ 31 - 1 by decide]
  exact Nat.and_two_pow_sub_one_eq_mod sz.toNat 31 |>.trans (Nat.mod_eq_of_lt hlt)

private theorem s13_sz_and_mask_no_bin {sz : BitVec 32} :
    ((sz &&& 0x7FFFFFFF#32) &&& 0x80000000#32) = 0#32 := by
  ext i _; simp only [BitVec.getElem_and, BitVec.getElem_zero]
  have h0 : ((0x7FFFFFFF#32 &&& 0x80000000#32) : BitVec 32)[i] = false := by
    have : (0x7FFFFFFF#32 &&& 0x80000000#32) = 0#32 := by decide
    rw [this]; simp
  simp only [BitVec.getElem_and] at h0; rw [Bool.and_assoc, h0, Bool.and_false]

private theorem s13_bv32_ne_sent_of_lt {x : BitVec 32} (hlt : x.toNat < 2 ^ 31) :
    x ≠ 0xFFFFFFFF#32 := fun h => by have := congrArg BitVec.toNat h; simp at this; omega

private theorem s13_and_garb_zero_of_mask {hdr : BitVec 32}
    (h : (hdr &&& (0x00080000#32 ||| 0x00400000#32)) = 0#32) :
    (hdr &&& 0x00080000#32) = 0#32 := by
  have hmask : ((0x00080000#32 ||| 0x00400000#32) &&& 0x00080000#32) = 0x00080000#32 := by decide
  calc hdr &&& 0x00080000#32
      = hdr &&& ((0x00080000#32 ||| 0x00400000#32) &&& 0x00080000#32) := by rw [hmask]
    _ = (hdr &&& (0x00080000#32 ||| 0x00400000#32)) &&& 0x00080000#32 := by rw [BitVec.and_assoc]
    _ = 0#32 := by rw [h, BitVec.zero_and]

/-- Certifies `step13FwdConnectSubsumerSpec` for Step-13 `full_fwd_connect_subsumer_m7`. -/
theorem full_fwd_connect_subsumer_m7_s13_wp (Γ : Env)
    (hOcc : M6EnvSpec Γ "full_dense_occ_cnt_fid" step13DenseOccCntSpec)
    (hWatchPush : M6EnvSpec Γ "full_watch_push" fullWatchPushSpec) :
    ∀ a m Q X, step13FwdConnectSubsumerSpec a m Q X →
      Func.wp Γ full_fwd_connect_subsumer_m7_body a m Q X := by
  rintro ⟨h, cref, ⟨⟩⟩ m0 Q X ⟨c, F0, F_cur, s0, R, rfl, hdw0, href, hm0, hQ⟩
  have hmx := c.hmaxv; have harc := c.harena; unfold dimacsBound at hmx harc
  have hwf := hdw0.2.1.arena.refs_wf cref.toNat href
  have hal_le := hdw0.1.core_ok.arena_len_le
  have hlay0 : WatchStackLayout s0.core := (m6_denseWatchesInv_of_w hdw0).layout
  have hcr_ar : (cref.setWidth 64).toNat < s0.core.arena.length := by
    rw [hdw0.1.core_ok.arena_len_arr, m6_zext32_toNat]; omega
  have hcr2_ar : (cref.setWidth 64 + 2#64).toNat < s0.core.arena.length := by
    rw [hdw0.1.core_ok.arena_len_arr]; c0_bound
  let hdr := s0.core.arena[(cref.setWidth 64).toNat]'hcr_ar
  let sz := s0.core.arena[(cref.setWidth 64 + 2#64).toNat]'hcr2_ar
  have hsz_eq : sz.toNat = fullArenaClauseSizeCore s0.core cref.toNat := by
    unfold sz fullArenaClauseSizeCore
    rw [List.getElem?_eq_getElem (by rw [hdw0.1.core_ok.arena_len_arr]; omega), Option.getD_some]
    exact congrArg BitVec.toNat (m6_getElem_congr (by c0_bound) _ _)
  unfold Func.wp full_fwd_connect_subsumer_m7_body
  c0_hsplit
  · c0_hsteps!; exact hQ s0 m0 hdw0 rfl rfl rfl rfl rfl rfl rfl hm0
  · have hng : fullArenaClauseGarb s0 cref.toNat = false := by
      unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
      rw [List.getElem?_eq_getElem (by rw [hdw0.1.core_ok.arena_len_arr]; omega), Option.getD_some]
      have hget : s0.core.arena[cref.toNat]'(by rw [hdw0.1.core_ok.arena_len_arr]; omega) = hdr :=
        m6_getElem_congr (m6_zext32_toNat cref).symm _ _
      rw [hget]; rw [hget] at hc; rw [s13_and_garb_zero_of_mask hc]; rfl
    c0_hsplit
    · c0_hsteps!; exact hQ s0 m0 hdw0 rfl rfl rfl rfl rfl rfl rfl hm0
    · have hsz3 : 3 ≤ sz.toNat := by omega
      have hcr3_ar : (cref.setWidth 64 + 3#64).toNat < s0.core.arena.length := by
        rw [hdw0.1.core_ok.arena_len_arr]; c0_bound
      have hl0_lt : (s0.core.arena[(cref.setWidth 64 + 3#64).toNat]'hcr3_ar).toNat <
          2 * s0.core.cur_vars := by
        have hmem : (s0.core.arena[(cref.setWidth 64 + 3#64).toNat]'hcr3_ar).toNat ∈
            fullArenaClauseLitsCore s0.core cref.toNat := by
          rw [mem_fullArenaClauseLitsCore_iff (by rw [hdw0.1.core_ok.arena_len_arr]; omega)]
          exact ⟨0, by omega, congrArg BitVec.toNat (m6_getElem_congr (by c0_bound) _ _)⟩
        exact hdw0.2.1.arena.lits_lt cref.toNat href hng _ hmem
      c0_hsteps_nogrp
      refine wp_loop_group (ts := [i32, i32, i32])
        (fun rem1 (best_l, best_d, i, ()) m1 =>
          m1 = m0 ∧ i.toNat ≤ sz.toNat ∧ rem1 = sz.toNat - i.toNat ∧
          best_l.toNat < 2 * s0.core.cur_vars)
        ?_ ?_
      · rintro L1 rem1 ⟨best_l, best_d, i, ⟨⟩⟩ m1 hL1 ⟨rfl, hi_le, rfl, hbl_lt⟩
        c0_hsplit
        · have hi_lt : i.toNat < sz.toNat := hc
          have hcri : (cref.setWidth 64 + 3#64 + i.setWidth 64).toNat < s0.core.arena.length := by
            rw [hdw0.1.core_ok.arena_len_arr]; c0_bound
          let l := s0.core.arena[(cref.setWidth 64 + 3#64 + i.setWidth 64).toNat]'hcri
          have hl_lt : l.toNat < 2 * s0.core.cur_vars := by
            have hmem : l.toNat ∈ fullArenaClauseLitsCore s0.core cref.toNat := by
              rw [mem_fullArenaClauseLitsCore_iff (by rw [hdw0.1.core_ok.arena_len_arr]; omega)]
              exact ⟨i.toNat, by omega, congrArg BitVec.toNat (m6_getElem_congr (by c0_bound) _ _)⟩
            exact hdw0.2.1.arena.lits_lt cref.toNat href hng _ hmem
          have hfl_idx : ((l >>> (1 : Nat)).setWidth 64).toNat < s0.core.flags.length := by
            rw [hdw0.1.core_ok.flags_len]; have := hdw0.1.core_ok.cur_vars_le; c0_bound
          have hi1 : (i + 1#32).toNat = i.toNat + 1 := by c0_bound
          c0_hsteps_nogrp
          refine wp_join_state_pure (ts := [i32, i32]) (α := BitVec 32 × BitVec 32)
            (fun p => (p.1, p.2, ())) (fun p => p.1.toNat < 2 * s0.core.cur_vars)
            (fun _ p hp => by
              c0_hsteps!; exact hL1 (sz.toNat - (i + 1#32).toNat) (p.1, p.2, i + 1#32, ()) m1
                (by omega) ⟨rfl, by omega, rfl, hp⟩)
            (fun J1 hJ1 => by
              c0_hsplit
              · c0_hsteps_nogrp; s13b_call hOcc
                refine ⟨c, s0, R, rfl, hdw0.1, hlay0, hl_lt, hm0, fun _ => ?_⟩
                c0_hsteps!
                · exact hJ1 (l, _) hl_lt
                · exact hJ1 (best_l, best_d) hbl_lt
              · c0_hsteps!; exact hJ1 (best_l, best_d) hbl_lt)
        · c0_hsteps_nogrp
          refine wp_join_state_pure (ts := [i32, i32, i32])
            (α := BitVec 32 × BitVec 32 × BitVec 32) (fun p => (p.1, p.2.1, p.2.2, ()))
            (fun p => p.1.toNat < 2 * s0.core.cur_vars) ?_ ?_
          rotate_left
          · intro J2 hJ2
            c0_hsplit
            · c0_hsteps_nogrp; s13b_call hOcc
              refine ⟨c, s0, R, rfl, hdw0.1, hlay0, hbl_lt, hm0, fun _ => ?_⟩
              c0_hsteps_nogrp
              refine wp_loop_group (ts := [i32, i32, i32])
                (fun rem2 (bl2, bd2, i2, ()) m2 =>
                  m2 = m1 ∧ i2.toNat ≤ sz.toNat ∧ rem2 = sz.toNat - i2.toNat ∧
                  bl2.toNat < 2 * s0.core.cur_vars)
                ?_ ?_
              · rintro L2 rem2 ⟨bl2, bd2, i2, ⟨⟩⟩ m2 hL2 ⟨rfl, hi2_le, rfl, hbl2⟩
                c0_hsplit
                · have hi2_lt : i2.toNat < sz.toNat := hc
                  have hcri2 : (cref.setWidth 64 + 3#64 + i2.setWidth 64).toNat <
                      s0.core.arena.length := by rw [hdw0.1.core_ok.arena_len_arr]; c0_bound
                  have hl2_lt : (s0.core.arena[(cref.setWidth 64 + 3#64 + i2.setWidth 64).toNat]'
                      hcri2).toNat < 2 * s0.core.cur_vars := by
                    have hmem : (s0.core.arena[(cref.setWidth 64 + 3#64 + i2.setWidth 64).toNat]'
                        hcri2).toNat ∈ fullArenaClauseLitsCore s0.core cref.toNat := by
                      rw [mem_fullArenaClauseLitsCore_iff
                        (by rw [hdw0.1.core_ok.arena_len_arr]; omega)]
                      exact ⟨i2.toNat, by omega,
                        congrArg BitVec.toNat (m6_getElem_congr (by c0_bound) _ _)⟩
                    exact hdw0.2.1.arena.lits_lt cref.toNat href hng _ hmem
                  have hi21 : (i2 + 1#32).toNat = i2.toNat + 1 := by c0_bound
                  c0_hsteps_nogrp; s13b_call hOcc
                  refine ⟨c, s0, R, rfl, hdw0.1, hlay0, hl2_lt, hm0, fun _ => ?_⟩
                  c0_hsteps_nogrp
                  refine wp_join_state_pure (ts := [i32, i32]) (α := BitVec 32 × BitVec 32)
                    (fun p => (p.1, p.2, ())) (fun p => p.1.toNat < 2 * s0.core.cur_vars) ?_ ?_
                  rotate_left
                  · intro J2b hJ2b
                    c0_hsteps!
                    · exact hJ2b (s0.core.arena[(cref.setWidth 64 + 3#64 +
                        i2.setWidth 64).toNat]'hcri2, _) hl2_lt
                    · exact hJ2b (bl2, bd2) hbl2
                  · rintro _ p hp; c0_hsteps!
                    exact hL2 (sz.toNat - (i2 + 1#32).toNat) (p.1, p.2, i2 + 1#32, ()) m2
                      (by omega) ⟨rfl, by omega, rfl, hp⟩
                · c0_hsteps!; exact hJ2 (bl2, bd2, i2) hbl2
              · intro L2 hL2
                c0_hsteps!; exact hL2 (sz.toNat - 1) (best_l, _, 1#32, ()) m1
                  ⟨rfl, by have : (1#32).toNat = 1 := rfl; omega, by simp, hbl_lt⟩
            · c0_hsteps!; exact hJ2 (best_l, best_d, i) hbl_lt
          · rintro _ ⟨bl, bd, _⟩ hbl
            c0_hsteps_nogrp
            refine wp_join0 (P := fun mj => ∃ sj : FullState,
                FullDenseInvW c F0 F_cur sj ∧ sj.core.cur_vars = s0.core.cur_vars ∧
                sj.core.arena = s0.core.arena ∧ sj.core.arena_len = s0.core.arena_len ∧
                sj.core.fuel = s0.core.fuel ∧ sj.core.inconsistent = s0.core.inconsistent ∧
                sj.scratch.tarjan_mark = s0.scratch.tarjan_mark ∧
                sj.scratch.red_refs = s0.scratch.red_refs ∧ (FullMem c sj ⋆ R) mj) ?_ ?_
            rotate_left
            · intro J35 hJ35
              c0_hsplit
              · c0_hsteps_nogrp
                refine wp_join0 (P := fun mj => ∃ sj : FullState,
                    FullDenseInvW c F0 F_cur sj ∧ sj.core.cur_vars = s0.core.cur_vars ∧
                    sj.core.arena = s0.core.arena ∧ sj.core.arena_len = s0.core.arena_len ∧
                    sj.core.fuel = s0.core.fuel ∧ sj.core.inconsistent = s0.core.inconsistent ∧
                    sj.scratch.tarjan_mark = s0.scratch.tarjan_mark ∧
                    sj.scratch.red_refs = s0.scratch.red_refs ∧ (FullMem c sj ⋆ R) mj) ?_ ?_
                rotate_left
                · intro J37 hJ37
                  have hsz_lt31 : sz.toNat < 2 ^ 31 := by omega
                  have hsz_mask : (sz &&& 0x7FFFFFFF#32) = sz := s13_sz_and_mask_eq hsz_lt31
                  c0_hsteps_nogrp; s13b_call hWatchPush
                  refine ⟨c, s0, R, rfl, hdw0.1, hlay0, fun h => by simp at h, fun _ => by
                      dsimp only; have hcr_lt : cref.toNat < 2 ^ 31 := by have := hwf.1; omega
                      refine ⟨?_, s13_bv32_ne_sent_of_lt hcr_lt⟩
                      rw [show (s0.core.arena[(cref.setWidth 64 + 2).toNat]'hcr2_ar &&&
                          2147483647 : BitVec 32) = sz &&& 0x7FFFFFFF#32 from rfl, hsz_mask]
                      exact s13_bv32_ne_sent_of_lt hsz_lt31,
                    hm0, ?_⟩
                  intro ok wvec' wstk' wlen' wu' wsort' m2
                  dsimp only
                  intro hlen2 hlay2 hoth2 hokt hokf hm2
                  let s2 : FullState :=
                    { s0 with
                      core := { s0.core with
                        wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' }
                      scratch := { s0.scratch with wsort := wsort' } }
                  have hdw2 : FullDenseInvW c F0 F_cur s2 :=
                    m6_fullDenseInvW_of_watchPush_occ hdw0 hlen2 hlay2 s13_sz_and_mask_no_bin
                      (by rw [hsz_mask]; omega) (by omega) href hoth2
                      (fun ht => by
                        obtain ⟨h1, _, h3, h4, h5, h6⟩ := hokt ht
                        exact ⟨h1, h3, h4, h5, h6 rfl⟩) (fun hf => (hokf hf).1)
                  c0_hsplit
                  · c0_hsteps!; exact hJ37 m2 ⟨s2, hdw2, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hm2⟩
                  · c0_hsteps!
                    exact hJ37 m ⟨{ s2 with core := { s2.core with oom := 1#64 } },
                      m6_fullDenseInvW_with_oom hdw2 1#64, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hm⟩
                · intro _ mj h; c0_hsteps!; exact hJ35 mj h
              · c0_hsteps!; exact hJ35 m1 ⟨s0, hdw0, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hm0⟩
            · intro _ mj ⟨sj, hdwj, hcvj, harj, halj, hflj, hincj, htmkj, hrrj, hmj⟩
              c0_hsteps!; exact hQ sj mj hdwj hcvj harj halj hflj hincj htmkj hrrj hmj
      · intro L1 hL1; c0_hsteps!
        exact hL1 sz.toNat (s0.core.arena[(cref.setWidth 64 + 3#64).toNat]'hcr3_ar,
          0xFFFFFFFF#32, 0#32, ()) m0 ⟨rfl, Nat.zero_le _, by simp, hl0_lt⟩

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S1
