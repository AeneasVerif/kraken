/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Transitive.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Transitive.UnrollInv
public import LeanQbe.T.Examples.Kissat.Proof.Transitive.WpLitHelpers
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics1
public import LeanQbe.T.Examples.Kissat.Src.Transitive

/-!
# Soundness Proof for `full_trans_lit_m6` (`Proof.Transitive.WpLit`)

Proves `full_trans_lit_m6_wp` (`Src.Transitive.full_trans_lit_m6_body`) against
canonical `Spec.fullTransLitM6Spec`, with pure step/bound helpers factored above
the main WP theorem.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Transitive

open Std.Sat
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Transitive.Spec
open LeanQbe.T.Examples.Kissat.Src.Transitive
open Kraken.Bedrock2.Test
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics

private theorem tr_lit_init_bounds {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {src : BitVec 32} (hw0 : FullWitnessInv c F0 F_cur s.core)
    (hlen : s.LengthsOk c) (hdm : s.core.dense_mode = 0#64)
    (hsrc_lt : src.toNat < 2 * s.core.cur_vars)
    (hsz_nz : (BitVec.setWidth 64 (s.core.wvec[2 * src.toNat + 1]'(by
      have := hlen.core_ok.cur_vars_le; have := hlen.core_ok.wvec_len; omega)) == 0#64) = false) :
    let off := fullWatchOffCore s.core src.toNat
    let sz := fullWatchSizeCore s.core src.toNat
    let off64 := BitVec.setWidth 64 (s.core.wvec[(BitVec.setWidth 64 src <<< (1 : Nat)).toNat]'(by
      have := hlen.core_ok.cur_vars_le; have := hlen.core_ok.wvec_len
      have : (BitVec.setWidth 64 src <<< (1 : Nat)).toNat = 2 * src.toNat := by bv_omega
      omega))
    let sz64 := BitVec.setWidth 64 (s.core.wvec[2 * src.toNat + 1]'(by
      have := hlen.core_ok.cur_vars_le; have := hlen.core_ok.wvec_len; omega))
    0 < sz ∧ off + sz ≤ s.core.wlen ∧ off64.toNat = off ∧ sz64.toNat = sz ∧
    (off64 + sz64).toNat = off + sz := by
  have hwm : WatchesInv F_cur s.core := by
    have hm := hw0.watches; unfold ModeWatchesInv at hm; simp only [hdm, ↓reduceIte] at hm; exact hm
  have hbnd := hwm.layout.bounds src.toNat hsrc_lt
  have hwl := hlen.core_ok.wlen_le
  have hwc := c.hwcap; unfold dimacsBound at hwc
  have hcv := hlen.core_ok.cur_vars_le; have hwvl := hlen.core_ok.wvec_len
  have hshl : (BitVec.setWidth 64 src <<< (1 : Nat)).toNat = 2 * src.toNat := by bv_omega
  have hoff_eq : (BitVec.setWidth 64 (s.core.wvec[(BitVec.setWidth 64 src <<< (1 : Nat)).toNat]'(by
      rw [hshl]; omega))).toNat = fullWatchOffCore s.core src.toNat := by
    rw [tr_bv32_setWidth64]
    simp only [fullWatchOffCore, hshl,
      List.getElem?_eq_getElem (by omega : 2 * src.toNat < s.core.wvec.length), Option.getD_some]
  have hsz_eq : (BitVec.setWidth 64 (s.core.wvec[2 * src.toNat + 1]'(by omega))).toNat =
      fullWatchSizeCore s.core src.toNat := by
    rw [tr_bv32_setWidth64]
    simp only [fullWatchSizeCore,
      List.getElem?_eq_getElem (by omega : 2 * src.toNat + 1 < s.core.wvec.length),
      Option.getD_some]
  have hsz_pos : 0 < fullWatchSizeCore s.core src.toNat := by
    rw [← hsz_eq]
    by_cases h0 : BitVec.setWidth 64 (s.core.wvec[2 * src.toNat + 1]'(by omega)) = 0#64
    · rw [h0] at hsz_nz; contradiction
    · exact Nat.pos_of_ne_zero (fun h => h0 (BitVec.eq_of_toNat_eq h))
  exact ⟨hsz_pos, hbnd, hoff_eq, hsz_eq, by bv_omega⟩

private theorem tr_lit_unroll_step_eq {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st_pre st_r : FullState} {src saved : Nat} (hw0 : FullWitnessInv c F0 F_cur s0.core)
    (hpre_vals : st_pre.core.vals = s0.core.vals)
    (hpre_cv : st_pre.core.cur_vars = s0.core.cur_vars) (hlen_pre : st_pre.LengthsOk c)
    (hu : TransUnrollInv c F0 F_cur s0 st_pre src saved st_r) (hgt : saved < st_r.core.trail_end) :
    let idx := (BitVec.ofNat 64 (BitVec.ofNat 64 st_r.core.trail_end - 1#64).toNat).toNat
    ∃ hidx : idx < st_r.core.trl.length,
      let ul := st_r.core.trl[idx]'hidx
      (BitVec.setWidth 64 ul).toNat < st_r.core.vals.length ∧
      (BitVec.setWidth 64 (ul ^^^ 1#32)).toNat < st_r.core.vals.length ∧
      (BitVec.ofNat 64 st_r.core.trail_end - 1#64).toNat = st_r.core.trail_end - 1 ∧
      TransUnrollInv c F0 F_cur s0 st_pre src saved
        { st_r with core := { st_r.core with
          vals := (st_r.core.vals.set (BitVec.setWidth 64 ul).toNat 0#8).set
            (BitVec.setWidth 64 (ul ^^^ 1#32)).toNat 0#8,
          trail_end := (BitVec.ofNat 64 st_r.core.trail_end - 1#64).toNat } } :=
  tr_unroll_c0_aux hw0 hpre_vals hpre_cv hlen_pre hu hgt (tr_bnds hu.len_ok.core_ok).2.2.2

private theorem tr_lit_del_side_and_tomb_eq {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st_pre st_u : FullState} {src off p end_v red dst : Nat}
    {w0 : BitVec 32} {wvec' wstk' : List (BitVec 32)} {wu' : BitVec 64}
    (hp_lt : p < end_v) (hp_wc : p < c.wcap)
    (hs_lt : src < 2 * st_u.core.cur_vars) (hd_lt : dst < 2 * st_u.core.cur_vars)
    (hd_ne : dst ≠ src)
    (hpre_eq : st_u.core.wstk = st_pre.core.wstk ∧ st_u.core.cur_vars = st_pre.core.cur_vars)
    (hget : st_pre.core.wstk[p]? = some w0) (hfl : (w0 &&& 0x80000000#32) ≠ 0#32)
    (hst_u_to : TransOuterInv c F0 F_cur s0 src off p end_v red st_u)
    (hl' : ({ st_u with core := { st_u.core with wvec := wvec', wstk := wstk', wusable := wu' } } :
      FullState).LengthsOk c)
    (hws : fullWatchOff { st_u with core :=
        { st_u.core with wvec := wvec', wstk := wstk', wusable := wu' } } dst =
        fullWatchOff st_u dst ∧
      fullWatchSize { st_u with core :=
        { st_u.core with wvec := wvec', wstk := wstk', wusable := wu' } } dst ≤
        fullWatchSize st_u dst)
    (hows : ∀ l < 2 * st_u.core.cur_vars, l ≠ dst →
      fullWatchOff { st_u with core :=
        { st_u.core with wvec := wvec', wstk := wstk', wusable := wu' } } l =
        fullWatchOff st_u l ∧
      fullWatchSize { st_u with core :=
        { st_u.core with wvec := wvec', wstk := wstk', wusable := wu' } } l =
        fullWatchSize st_u l)
    (hout : ∀ i < c.wcap, (i < fullWatchOff st_u dst ∨
      fullWatchOff st_u dst + fullWatchSize st_u dst ≤ i) → wstk'[i]? = st_u.core.wstk[i]?)
    (hsl : WatchSliceOk F_cur st_u.core dst (fullWatchOff st_u dst) (fullWatchSize st_u dst) →
      WatchSliceOk F_cur { st_u.core with wvec := wvec', wstk := wstk', wusable := wu' } dst
        (fullWatchOff { st_u with core :=
          { st_u.core with wvec := wvec', wstk := wstk', wusable := wu' } } dst)
        (fullWatchSize { st_u with core :=
          { st_u.core with wvec := wvec', wstk := wstk', wusable := wu' } } dst)) :
    TransOuterInv c F0 F_cur s0 src off (p + 1) end_v (red + 1)
      { st_u with
        core := { st_u.core with wvec := wvec', wstk := wstk'.set p 0xFFFFFFFF#32, wusable := wu' },
        scratch := { st_u.scratch with trans_cnt := st_u.scratch.trans_cnt + 1#64 } } :=
  hst_u_to.del_side_and_tomb hp_lt hp_wc hs_lt hd_lt hd_ne (by rw [hpre_eq.1]; exact hget) hfl
    rfl hl' hws hows hout hsl

private theorem tr_lit_hend_hc {s : FullState} {src : Val i32}
    (hb : 2 * src.toNat + 1 < 2 ^ 64)
    (hw0_b : (BitVec.setWidth 64 src <<< (1 : Nat)).toNat < s.core.wvec.length)
    (hwv_b : 2 * src.toNat + 1 < s.core.wvec.length)
    (hshl_eq : (BitVec.setWidth 64 src <<< (1 : Nat)).toNat = 2 * src.toNat)
    (hoff_nat :
      (BitVec.setWidth 64 (s.core.wvec[(BitVec.setWidth 64 src <<< (1 : Nat)).toNat]'hw0_b)).toNat =
        fullWatchOffCore s.core src.toNat)
    (hsz_nat : (BitVec.setWidth 64 (s.core.wvec[2 * src.toNat + 1]'hwv_b)).toNat =
      fullWatchSizeCore s.core src.toNat) :
    (s.core.wvec[(2 * src.toNat) % 2 ^ 64]'(by
      have hm0 : (2 * src.toNat) % 2 ^ 64 = (BitVec.setWidth 64 src <<< (1 : Nat)).toNat := by
        rw [hshl_eq, Nat.mod_eq_of_lt (by omega)]
      rw [hm0]; exact hw0_b)).toNat +
    (s.core.wvec[(2 * src.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
      have hm1 : (2 * src.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 = 2 * src.toNat + 1 := by
        rw [show BitVec.toNat (1 : BitVec 64) = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
      rw [hm1]; exact hwv_b)).toNat =
      fullWatchOffCore s.core src.toNat + fullWatchSizeCore s.core src.toNat := by
  have hm0 : (2 * src.toNat) % 2 ^ 64 = (BitVec.setWidth 64 src <<< (1 : Nat)).toNat := by
    rw [hshl_eq, Nat.mod_eq_of_lt (by omega)]
  have hm1 : (2 * src.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 = 2 * src.toNat + 1 := by
    rw [show BitVec.toNat (1 : BitVec 64) = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
  simp only [hm0, hm1]
  have h0 : (s.core.wvec[(BitVec.setWidth 64 src <<< (1 : Nat)).toNat]'hw0_b).toNat =
      fullWatchOffCore s.core src.toNat := by
    have h0' := hoff_nat
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt
      (Nat.lt_trans (BitVec.isLt (s.core.wvec[_]'hw0_b)) (by decide))] at h0'
    exact h0'
  have h1 : (s.core.wvec[2 * src.toNat + 1]'hwv_b).toNat =
      fullWatchSizeCore s.core src.toNat := by
    have h1' := hsz_nat
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt
      (Nat.lt_trans (BitVec.isLt (s.core.wvec[2 * src.toNat + 1]'hwv_b)) (by decide))] at h1'
    exact h1'
  rw [h0, h1]

/-- `full_trans_lit_m6` satisfies canonical `Spec.fullTransLitM6Spec`. -/
theorem full_trans_lit_m6_wp (Γ : Env)
    (hDel : Γ.Has "full_delete_bin_side" fullDeleteBinSideSpec)
    (hAu : Γ.Has "full_add_unit" fullAddUnitSpec) :
    ∀ a m Q X, fullTransLitM6Spec a m Q X →
      Func.wp Γ full_trans_lit_m6_body a m Q X := by
  rintro ⟨h, src, stop_early, ⟨⟩⟩ m0 Q X ⟨c, F0, s, R, rfl, hsp, hcl0, hsrc_lt, hm0, hQ⟩
  obtain ⟨hcore, hmrk, hnodup, hext, hdense0⟩ := id hsp
  have hlen0 := hcore.lengths; rcases hcore.witness with ⟨F_cur, hw0⟩
  have hmv := c.hmv; have hmaxv := c.hmaxv; have hwc := c.hwcap
  unfold dimacsBound at hmv hmaxv hwc
  have hcv0 := hlen0.core_ok.cur_vars_le
  have hbnds := tr_bnds hlen0.core_ok
  have hsrc_vlen : src.toNat < s.core.vals.length := tr_vals_lt hlen0.core_ok hsrc_lt
  have hshl_eq : (BitVec.setWidth 64 src <<< (1 : Nat)).toNat = 2 * src.toNat := by bv_omega
  have hw0_b : (BitVec.setWidth 64 src <<< (1 : Nat)).toNat < s.core.wvec.length := by
    rw [hshl_eq, hlen0.core_ok.wvec_len]; omega
  have hwv_b : 2 * src.toNat + 1 < s.core.wvec.length := by
    rw [hlen0.core_ok.wvec_len]; omega
  unfold Func.wp full_trans_lit_m6_body
  c0_hsteps_nogrp
  · exact hQ true s m0 ⟨hcore, hmrk, hnodup, hext, hdense0⟩ hcl0 rfl rfl rfl
      (fun h => by cases h) hm0
  · exact hQ true s m0 ⟨hcore, hmrk, hnodup, hext, hdense0⟩ hcl0 rfl rfl rfl
      (fun h => by cases h) hm0
  ·
      have hsz_nz :
          (BitVec.setWidth 64 (s.core.wvec[2 * src.toNat + 1]'hwv_b) == 0#64) = false := by
        rw [beq_eq_false_iff_ne]
        intro h0
        have hm : (2 * src.toNat + 1) % 2 ^ 64 = 2 * src.toNat + 1 := Nat.mod_eq_of_lt (by omega)
        exact hc (by simpa [hm] using h0)
      obtain ⟨hsz_pos, hend_le_wlen, hoff_nat, hsz_nat, hend_nat⟩ :=
        tr_lit_init_bounds hw0 hlen0 hdense0 hsrc_lt hsz_nz
      let off := fullWatchOffCore s.core src.toNat
      let sz := fullWatchSizeCore s.core src.toNat
      let end_v := off + sz
      let not_src := src ^^^ 1#32
      have hnot_src_lt : not_src.toNat < 2 * s.core.cur_vars := by
        rw [show not_src = src ^^^ 1#32 from rfl, tr_bv32_xor1]
        exact litNeg_lt_two_mul hsrc_lt
      refine wp_loop_break_group (brkTs := [.bool, i64, i64]) (lpTs := [.bool, i64, i64])
        (BrkPost := fun (failed, red_v, p, ()) mb => ∃ red st,
          red_v = BitVec.ofNat 64 red ∧ red ≤ end_v - off ∧
          TransOuterInv c F0 F_cur s src.toNat off p.toNat end_v red st ∧
          st.scratch.work_stk1 = s.scratch.work_stk1 ∧
          (failed = true → (cnfOfClauses F_cur).EntailsClause (cnfClause [src.toNat])) ∧
          (FullMem c st ⋆ R) mb)
        (Inv := fun rem (failed, red_v, p, ()) ml => ∃ red st,
          red_v = BitVec.ofNat 64 red ∧ rem = end_v - p.toNat ∧
          TransOuterInv c F0 F_cur s src.toNat off p.toNat end_v red st ∧
          st.scratch.work_stk1 = s.scratch.work_stk1 ∧
          (failed = true → (cnfOfClauses F_cur).EntailsClause (cnfClause [src.toNat])) ∧
          (FullMem c st ⋆ R) ml)
        ?_ ?_ ?_
      · rintro _ ⟨failed, red_v, p_fin, ⟨⟩⟩ mb
          ⟨red, st_c, rfl, hred_le, hto_c, hws1_c, hfail_c, hmb⟩
        have hshl1 : (BitVec.setWidth 64 src <<< (1 : Nat) + (1 : BitVec 64)).toNat =
            2 * src.toNat + 1 := by
          rw [BitVec.toNat_add, tr_bv64_shl1 (by rw [tr_bv32_setWidth64]; omega),
            tr_bv32_setWidth64, show (1 : BitVec 64).toNat = 1 from rfl,
            Nat.mod_eq_of_lt (by omega)]
        have hweq : s.core.wvec[(BitVec.setWidth 64 src <<< (1 : Nat) + (1 : BitVec 64)).toNat]'(by
              rw [hshl1]; exact hwv_b) = s.core.wvec[2 * src.toNat + 1] := by
          simp only [hshl1]
        have hend_shl := hend_nat
        rw [← hweq] at hend_shl
        refine tr_lit_post_wp Γ hAu hsp hw0 hcl0 hsrc_lt rfl rfl rfl hend_le_wlen
          hoff_nat hend_shl hred_le hto_c hws1_c hfail_c hmb hQ
      · rintro B L rem ⟨failed, red_v, p, ⟨⟩⟩ ml hB hL
          ⟨red, st_l, rfl, hrem, hto_l, hws1_l, hfail_l, hml⟩
        have hb_l := hto_l.base
        have hpe_bnd : end_v ≤ c.wcap :=
          Nat.le_trans hb_l.end_le_wlen hb_l.len_ok.core_ok.wlen_le
        have hp_le := hto_l.p_le_end; have hred_le := hto_l.red_le
        have hred_end : red ≤ end_v - off := Nat.le_trans hred_le (by omega)
        c0_hsplit
        · have hp_lt : p.toNat < end_v := by
            have hend_eq := tr_lit_hend_hc (by have := src.isLt; omega) hw0_b hwv_b hshl_eq
              hoff_nat hsz_nat
            change _ = end_v at hend_eq
            have h_ed : end_v < 2 ^ 64 := by omega
            have hcw := hc
            rw [hend_eq, Nat.mod_eq_of_lt h_ed] at hcw
            exact hcw
          c0_hsplit
          · have hf_t : failed = true := by c0_bound
            c0_hsteps; exact hB _ ml ⟨red, st_l, rfl, hred_end, hto_l, hws1_l, hf_t ▸ hfail_l, hml⟩
          · have hf_f : failed = false := by assumption
            subst hf_f
            c0_hsplit
            · have hp_wlen : p.toNat < st_l.core.wstk.length := by
                rw [hb_l.len_ok.core_ok.wstk_len_arr]; omega
              let w0 := st_l.core.wstk[p.toNat]'hp_wlen
              have hw0_get : st_l.core.wstk[p.toNat]? = some w0 := List.getElem?_eq_getElem hp_wlen
              c0_hsplit
              · have hfl0 : (w0 &&& 0x80000000#32) = 0#32 := by c0_bound
                obtain ⟨_, hto_lg⟩ := hto_l.skip_large hp_lt hw0_get hfl0
                c0_hsplit
                · c0_hsteps; exact hB _ ml ⟨red, st_l, rfl, hred_end, hto_l, hws1_l,
                    (fun h => by cases h), hml⟩
                · have hp2_bv : (p + 2).toNat = p.toNat + 2 := tr_bv64_add2 (by omega)
                  c0_hsteps
                  exact hL (end_v - (p.toNat + 2)) _ ml (by omega)
                    ⟨red, st_l, rfl, by rw [hp2_bv], by rw [hp2_bv]; exact hto_lg, hws1_l,
                      (fun h => by cases h), hml⟩
              · have hfl_nz : (w0 &&& 0x80000000#32) ≠ 0#32 := by c0_bound
                obtain ⟨hne_tomb, hdst_lt_c, _, hto_sk⟩ := hto_l.skip_bin hp_lt hw0_get hfl_nz
                have hdst_lt : (w0 &&& 0x7FFFFFFF#32).toNat < 2 * st_l.core.cur_vars := hdst_lt_c
                let dst := w0 &&& 0x7FFFFFFF#32
                have hdst_vlen : dst.toNat < st_l.core.vals.length :=
                  tr_vals_lt hb_l.len_ok.core_ok hdst_lt
                have hp1_bv : (p + 1#64).toNat = p.toNat + 1 := tr_bv64_add1 (by omega)
                c0_hstraight
                refine wp_join_group (ts := []) (fun () mc => mc = ml) ?_ ?_
                · rintro _ ⟨⟩ mc rfl
                  c0_hsteps
                  exact hL (end_v - (p.toNat + 1)) (false, BitVec.ofNat 64 red, p + 1#64, ()) mc
                    (by omega)
                    ⟨red, st_l, rfl, by rw [hp1_bv], by rw [hp1_bv]; exact hto_sk, hws1_l,
                      (fun h => by cases h), hml⟩
                ·
                    intro Jc hJc
                    c0_hsplit
                    · c0_hsteps; exact hJc () ml rfl
                    · c0_hsplit
                      · c0_hsteps; exact hJc () ml rfl
                      · have hsrc_lt_dst : src.toNat < dst.toNat := by
                          dsimp only [dst, w0]
                          rw [show (2147483647#32 : BitVec 32) = 2147483647 from rfl]; omega
                        c0_hsteps_nogrp
                        c0_hsplit
                        · c0_hsteps; exact hJc () ml rfl
                        · have hdst0_sxt :
                              (st_l.core.vals[dst.toNat]'hdst_vlen).signExtend 32 = 0#32 := by
                            dsimp only [dst, w0]; bv_omega
                          have hticks0_lt : st_l.scratch.ant_sz ≠ 0#64 := by c0_bound
                          have hcv_l : st_l.core.cur_vars = s.core.cur_vars := hb_l.core_pres.1
                          have hsrc_vlen_l : src.toNat < st_l.core.vals.length :=
                            tr_vals_lt hb_l.len_ok.core_ok (hcv_l.symm ▸ hsrc_lt)
                          have hnot_vlen_l : not_src.toNat < st_l.core.vals.length :=
                            tr_vals_lt hb_l.len_ok.core_ok (hcv_l.symm ▸ hnot_src_lt)
                          let saved := st_l.core.trail_end
                          have hsrc0_l : st_l.core.vals[src.toNat]?.getD 0#8 = 0#8 := by
                            rw [hb_l.core_pres.2.2.2.2.2.2.2.2.2.2.1]
                            have hg : s.core.vals[src.toNat]?.getD 0#8 =
                                s.core.vals[src.toNat]'hsrc_vlen := by
                              simp [List.getElem?_eq_getElem hsrc_vlen]
                            rw [hg]
                            exact tr_vals_zero_of_domain (hg ▸ hw0.vals_domain src.toNat hsrc_lt)
                              rfl (by assumption)
                          obtain ⟨hsaved_lt, hu_init, hsaved_lt_te⟩ :=
                            TransUnrollInv.init hw0 hb_l.len_ok hb_l.core_pres.2.2.2.2.2.2.2.2.2.2.1
                              hb_l.core_pres.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hb_l.core_pres.1
                              (hb_l.core_pres.1 ▸ hsrc_lt) hsrc0_l
                          have hsaved_trl : saved < st_l.core.trl.length := by
                            rw [hb_l.len_ok.core_ok.trl_len]
                            have := hb_l.len_ok.core_ok.cur_vars_le; omega
                          have hsaved_u64 : st_l.core.trail_end + 1 < 2 ^ 64 := by
                            have := hsaved_lt; have := hb_l.len_ok.core_ok.cur_vars_le; omega
                          have hsaved1_eq : (BitVec.ofNat 64 saved + 1#64).toNat = saved + 1 := by
                            change (BitVec.ofNat 64 st_l.core.trail_end + 1#64).toNat =
                              st_l.core.trail_end + 1
                            rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
                            omega
                          c0_hsteps_nogrp
                          refine wp_loop_inv (ts := [.bool, i64, i64, .bool])
                            (fun (fail_b, ticks_b, qhead_b, hit_b, ()) m_b => ∃ st_b,
                              TransUnrollInv c F0 F_cur s st_l src.toNat saved st_b ∧
                              saved ≤ qhead_b.toNat ∧ qhead_b.toNat ≤ st_b.core.trail_end ∧
                              saved < st_b.core.trail_end ∧
                              st_b.scratch.work_stk1 = s.scratch.work_stk1 ∧
                              (fail_b = true →
                                (cnfOfClauses F_cur).EntailsClause (cnfClause [src.toNat])) ∧
                              (FullMem c st_b ⋆ R) m_b)
                            (fun (_, _, qhead_b, _, ()) _ => st_l.core.cur_vars - qhead_b.toNat)
                            ?_ ?_
                          · intro Jbfs hJbfs
                            c0_hsteps
                            have h1_64 : (1 : BitVec 64) = 1#64 := rfl
                            have h1_32 : (1 : BitVec 32) = 1#32 := rfl
                            have hte_bv0 : (BitVec.ofNat 64 st_l.core.trail_end).toNat =
                                st_l.core.trail_end := by
                              have := hsaved_lt; have := hb_l.len_ok.core_ok.cur_vars_le; bv_omega
                            have hv1 : BitVec.ofNat (OfNat.ofNat 8) (OfNat.ofNat 1) =
                                (1#8 : BitVec 8) := rfl
                            have h_neg1 : BitVec.setWidth 8 (-1 : BitVec 32) = 255#8 := rfl
                            have h_neg1_s : BitVec.setWidth 8 (-1#32 : BitVec 32) = 255#8 := rfl
                            have h_neg1_64 : BitVec.setWidth 8 (-1 : BitVec 64) = 255#8 := rfl
                            have hsrc_xor_lt : src.toNat ^^^ 1 < 2 * c.max_vars := by
                              have := litNeg_lt_two_mul hsrc_lt; omega
                            have hxsrc_eq : src ^^^ 1#32 = BitVec.ofNat 32 (src.toNat ^^^ 1) := by
                              apply BitVec.eq_of_toNat_eq
                              rw [tr_bv32_xor1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
                            have hsw_x : (BitVec.setWidth 64
                                (BitVec.ofNat 32 (src.toNat ^^^ 1))).toNat = src.toNat ^^^ 1 := by
                              rw [tr_bv32_setWidth64, BitVec.toNat_ofNat,
                                Nat.mod_eq_of_lt (by omega)]
                            have hsaved1_raw :
                                (BitVec.ofNat 64 st_l.core.trail_end + 1#64).toNat =
                                st_l.core.trail_end + 1 := hsaved1_eq
                            refine hJbfs (false, st_l.scratch.ant_sz - 1#64, BitVec.ofNat 64 saved,
                              false, ()) m ⟨_, hu_init, ?_, ?_,
                              hsaved_lt_te, hws1_l, (fun h => by cases h), (by
                                simpa only [h1_64, h1_32, hsaved1_raw, hte_bv0, hv1,
                                  h_neg1, h_neg1_s, h_neg1_64, hxsrc_eq, hsw_x,
                                  show (BitVec.setWidth 64 src).toNat = src.toNat from
                                    tr_bv32_setWidth64 src] using hm)⟩
                            · rw [show (BitVec.ofNat 64 saved).toNat = saved by
                                have := (tr_bnds hb_l.len_ok.core_ok).2.2.2; bv_omega]
                              exact Nat.le_refl _
                            · rw [show (BitVec.ofNat 64 saved).toNat = saved by
                                have := (tr_bnds hb_l.len_ok.core_ok).2.2.2; bv_omega]
                              exact Nat.le_of_lt hsaved_lt_te
                          · rintro Jbfs ⟨fail_b, ticks_b, qhead_b, hit_b, ⟨⟩⟩ m_b
                              ⟨st_b, hu_b, hqh_ge, hqh_le, hte_gt, hws1_b, hfail_b, hm_b⟩ ih_bfs
                            c0_hsteps_nogrp
                            refine wp_join_group (ts := []) (fun () mj => (FullMem c st_b ⋆ R) mj)
                              ?_ ?_
                            ·
                                rintro _ ⟨⟩ mj hm_j
                                let st_post_pre : FullState :=
                                  { st_l with scratch := { st_l.scratch with ant_sz := ticks_b } }
                                let st_post_b : FullState :=
                                  { st_b with scratch := { st_b.scratch with ant_sz := ticks_b } }
                                have hto_post := tr_outer_with_ant_sz ticks_b hto_l
                                have hu_post := tr_unroll_with_ant_sz ticks_b hu_b
                                c0_hsteps_nogrp
                                refine wp_loop_group (ts := [])
                                  (fun n () mu => ∃ st_u, n = st_u.core.trail_end - saved ∧
                                    TransUnrollInv c F0 F_cur s st_post_pre src.toNat saved st_u ∧
                                    st_u.scratch.work_stk1 = s.scratch.work_stk1 ∧
                                    (FullMem c st_u ⋆ R) mu)
                                  ?_ (fun Ju hJu => by
                                    c0_hsteps
                                    exact hJu (st_post_b.core.trail_end - saved) () m
                                      ⟨st_post_b, rfl, hu_post, hws1_b, hm⟩)
                                rintro Ju n ⟨⟩ mu ihu ⟨st_u, rfl, hu_u, hws1_u, hm_u⟩
                                c0_hsplit
                                · have hgt_u : saved < st_u.core.trail_end := by c0_bound
                                  obtain ⟨hidx_len, hul_v, huln_v, hte1_eq, hu_u'⟩ :=
                                    tr_lit_unroll_step_eq hw0
                                      hto_post.base.core_pres.2.2.2.2.2.2.2.2.2.2.1
                                      hto_post.base.core_pres.1 hto_post.base.len_ok hu_u hgt_u
                                  have huln_v' :
                                      (BitVec.setWidth 64 (st_u.core.trl[(BitVec.ofNat 64
                                        (BitVec.ofNat 64 st_u.core.trail_end -
                                          1#64).toNat).toNat]'hidx_len ^^^ 1#32)).toNat <
                                        (st_u.core.vals.set (BitVec.setWidth 64
                                          (st_u.core.trl[(BitVec.ofNat 64
                                            (BitVec.ofNat 64 st_u.core.trail_end -
                                              1#64).toNat).toNat]'hidx_len)).toNat 0#8).length :=
                                    by rw [List.length_set]; exact huln_v
                                  have h1_64 : (1 : BitVec 64) = 1#64 := rfl
                                  have h1_32 : (1 : BitVec 32) = 1#32 := rfl
                                  have h0_8 : BitVec.ofNat (OfNat.ofNat 8) (OfNat.ofNat 0) =
                                      (0#8 : BitVec 8) := rfl
                                  c0_hsteps
                                  exact ihu (st_u.core.trail_end - 1 - saved) () m (by omega)
                                    ⟨_, by simp [hte1_eq], hu_u', hws1_u, by
                                      dsimp only
                                      simpa only [h1_64, h1_32, h0_8] using hm⟩
                                · have hte_eq_u : st_u.core.trail_end = saved := by
                                    have := hu_u.saved_le_te
                                    have hte_lt := (tr_bnds hu_u.len_ok.core_ok).2.2.2
                                    have hno : ¬ saved < st_u.core.trail_end := by intro h; c0_bound
                                    omega
                                  have hto_u := hu_u.done hto_post hte_eq_u
                                  c0_hsteps_nogrp
                                  refine wp_join_group (ts := [i64])
                                    (fun (red'_v, ()) m_out => ∃ red' st_out,
                                      red'_v = BitVec.ofNat 64 red' ∧
                                      TransOuterInv c F0 F_cur s src.toNat off (p.toNat + 1) end_v
                                        red' st_out ∧
                                      st_out.scratch.work_stk1 = s.scratch.work_stk1 ∧
                                      (FullMem c st_out ⋆ R) m_out)
                                    ?_ ?_
                                  · rintro _ ⟨red'_v, ⟨⟩⟩ m_out
                                        ⟨red', st_out, rfl, hto_out, hws1_out, hm_out⟩
                                    have h1_64 : (1 : BitVec 64) = 1#64 := rfl
                                    c0_hsteps
                                    exact hL (end_v - (p.toNat + 1)) _ m_out (by omega)
                                      ⟨red', st_out, rfl, by rw [h1_64, hp1_bv],
                                        by rw [h1_64, hp1_bv]; exact hto_out,
                                        hws1_out, hfail_b, hm_out⟩
                                  · intro Jr hJr
                                    c0_hsplit
                                    · have hst_u_core : st_u.core.wstk = st_post_pre.core.wstk ∧
                                          st_u.core.cur_vars = st_post_pre.core.cur_vars := by
                                        rw [hu_u.same_core]; exact ⟨rfl, rfl⟩
                                      have hsrc_u : src.toNat < 2 * st_u.core.cur_vars := by
                                        rw [hst_u_core.2]; exact hb_l.core_pres.1 ▸ hsrc_lt
                                      have hdst_u : dst.toNat < 2 * st_u.core.cur_vars := by
                                        rw [hst_u_core.2]; exact hdst_lt
                                      refine wp_call_of_spec _ _ (hDel (c.hdr, dst, src, ()) _ _ _
                                        ⟨c, st_u, R, rfl, hto_u.base.len_ok,
                                         fun h => hto_u.base.other_bounds dst.toNat h
                                           (Nat.ne_of_lt hsrc_lt_dst).symm,
                                         hm_u, ?_⟩)
                                      intro wvec' wstk' wu' m_del
                                      dsimp only
                                      intro hlen_del hself_del hows_del hout_del hws_del
                                        _ _ _ hm_del
                                      have hp_wlen_del : p.toNat < wstk'.length := by
                                        rw [hlen_del.core_ok.wstk_len_arr]; omega
                                      c0_hsteps
                                      have hto_red := tr_lit_del_side_and_tomb_eq hp_lt (by omega)
                                        hsrc_u hdst_u (Nat.ne_of_lt hsrc_lt_dst).symm hst_u_core
                                        hw0_get hfl_nz hto_u hlen_del (hself_del hdst_u) hows_del
                                        (fun i hi hdisj => hout_del i hi (fun _ => hdisj))
                                        (hws_del F_cur)
                                      refine hJr _ m ⟨red + 1, _, ?_, hto_red, hws1_u, ?_⟩
                                      · bv_omega
                                      · simpa only [show (4294967295 : BitVec 32) = 0xFFFFFFFF#32
                                            from rfl, show (1 : BitVec 64) = 1#64 from rfl] using hm
                                    · c0_hsteps
                                      have hto_u1 : TransOuterInv c F0 F_cur s src.toNat off
                                          (p.toNat + 1) end_v red st_u :=
                                        (hto_u.skip_bin hp_lt (by
                                          rw [hu_u.same_core]; exact hw0_get) hfl_nz).2.2.2
                                      exact hJr _ mu ⟨red, st_u, rfl, hto_u1, hws1_u, hm_u⟩
                            · intro Jex hJex
                              refine tr_lit_bfs_wp Γ hw0 hcl0 hsrc_lt hto_l hws1_l ?_ hu_b hqh_ge
                                hqh_le hte_gt hws1_b hfail_b hm_b hJex
                                (fun fb tb qhb hb m hlt h =>
                                  ih_bfs (fb, tb, qhb, hb, ()) m hlt h)
                              have hcv64 : (BitVec.ofNat 64 s.core.cur_vars).toNat =
                                  s.core.cur_vars := by
                                rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
                              rw [tr_bv64_shl1 (by rw [hcv64]; omega), hcv64]
            · c0_hsteps
              exact hB _ ml ⟨red, st_l, rfl, hred_end, hto_l, hws1_l, (fun h => by cases h), hml⟩
        · c0_hsteps
          exact hB _ ml ⟨red, st_l, rfl, hred_end, hto_l, hws1_l, hfail_l, hml⟩
      · rintro _ _ _ hL0
        c0_hsteps
        exact hL0 (end_v - off) _ m0
          ⟨0, s, rfl, by rw [hoff_nat],
           by rw [hoff_nat]; exact TransOuterInv.init hlen0 hw0 hdense0 hcl0 hsrc_lt hsz_pos,
           rfl, (fun h => by cases h), hm0⟩
