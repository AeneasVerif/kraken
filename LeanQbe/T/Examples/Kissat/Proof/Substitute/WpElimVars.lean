/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Substitute.Spec
public import LeanQbe.T.Examples.Kissat.Src.Substitute
import LeanQbe.T.Examples.Kissat.Proof.Substitute.Helpers
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb

/-!
# WP Proof for `full_subst_elim_vars` (`Proof.Substitute.WpElimVars`)

Proves `full_subst_elim_vars_wp` parametrically over `Γ : Env` against
`Spec.fullSubstElimVarsM6Spec`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Substitute

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Substitute
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Substitute.Spec
open scoped Proof.Spec.FullArenaTactics SubstArenaTactics
open Kraken.Bedrock2.Test

private theorem two_mul_xor_one (n : Nat) : (2 * n) ^^^ 1 = 2 * n + 1 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor]
  cases i with
  | zero =>
    simp only [Nat.testBit_zero, show 2 * n % 2 = 0 by omega, show (1 : Nat) % 2 = 1 from rfl,
      show (2 * n + 1) % 2 = 1 by omega]
    decide
  | succ k =>
    simp only [Nat.testBit_succ]
    rw [show (1 : Nat) / 2 = 0 from rfl, show (2 * n + 1) / 2 = 2 * n / 2 by omega]
    simp

public section

/-- `full_subst_elim_vars` satisfies canonical `Spec.fullSubstElimVarsM6Spec`
parametrically in `Γ`. -/
theorem full_subst_elim_vars_wp (Γ : Env)
    (hAddUnit : Γ.Has "full_add_unit" fullAddUnitSpec)
    (hProp : Γ.Has "full_propagate" Proof.PropSearch.Spec.propagateM6Spec)
    (hExtPush2 : Γ.Has "full_extend_push2" fullExtendPush2Spec)
    (hSetInact : Γ.Has "full_set_inactive" Proof.Internal.Spec.fullSetInactiveSpec) :
    ∀ args m Q X, Spec.fullSubstElimVarsM6Spec args m Q X →
      Func.wp Γ full_subst_elim_vars_body args m Q X := by
  rintro ⟨h, ucnt, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, ext0, s0, R, rfl, hinv0, hl0, hrepr0, huc_le, hus0, hm0, hQ⟩
  have _hx := c.hmaxv; unfold dimacsBound at _hx
  unfold Func.wp full_subst_elim_vars_body
  have hsp0 := hinv0.sparseW
  have hm0_f := fullM6HdrMem_focus_full hm0
  c0_hsteps_nogrp
  refine wp_loop_inv (ts := [i64])
    (fun (k, ()) ml => ∃ st : FullState,
      FullSparseInvW c F0 F_cur st ∧ st.core.cur_level = 0 ∧
      st.core.cur_vars = s0.core.cur_vars ∧ st.core.fuel.toNat ≤ s0.core.fuel.toNat ∧
      FullReprEquiv F_cur st ∧ k.toNat ≤ ucnt.toNat ∧
      st.scratch.shrink_stk = s0.scratch.shrink_stk ∧
      (FullMem c st ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext0 ⋆ R)) ml)
    (fun (k, ()) _ => ucnt.toNat - k.toNat)
    ?_ ?_
  · exact fun J1 hJ1 => hJ1 (0#64, ()) m
      ⟨s0, hsp0, hl0, rfl, Nat.le_refl _, hrepr0, Nat.zero_le _, rfl, hm0_f⟩
  rintro J1 ⟨k, ⟨⟩⟩ ml ⟨st, hsp, hl, hcv, hfl, hrepr, hk_le, hss, hml⟩ ih1
  have hk_max : k.toNat ≤ c.max_vars := Nat.le_trans hk_le huc_le
  have hstk_len_eq : st.scratch.shrink_stk.length = c.max_vars := hsp.1.scratch_ok.shrink_stk_len
  c0_hsteps_nogrp
  c0_hsplit
  · have hk_lt : k.toNat < ucnt.toNat := hc
    have hk1 : (k + 1#64).toNat = k.toNat + 1 := bv64_add1_toNat (by omega)
    have hstk_len : k.toNat < st.scratch.shrink_stk.length := by rw [hstk_len_eq]; omega
    c0_hsteps_nogrp
    c0_hcall hAddUnit
    refine ⟨c, F0, F_cur, st, _, rfl, hsp.1, hsp.2.1, fun _hlt => ?_, hml, ?_⟩
    · have hget : st.scratch.shrink_stk[k.toNat]?.getD 0#32 =
          st.scratch.shrink_stk[k.toNat]'hstk_len := by
        rw [List.getElem?_eq_getElem hstk_len, Option.getD_some]
      rw [← hget, hss]; exact (hus0 k.toNat hk_lt).2
    intro ok1 vals1 fl1 lvl1 rsns1 trl1 tp1 te1 prop1 cl1 unass1 unfl1 inc1
      ph1 ta1 ba1 pt1 pb1 hp1 ps1 hl1 qsi1 qss1 m1 _ hlen1 hw1 hcl1 _ hfail1 hm1_f
    let st1 : FullState :=
      { core := { st.core with
          vals := vals1, flags := fl1, lvl := lvl1, rsns := rsns1, trl := trl1,
          trail_pos := tp1, trail_end := te1, propagated := prop1, cur_level := cl1,
          unassigned := unass1, unflushed := unfl1, inconsistent := inc1 }
        scratch := { st.scratch with
          phases := ph1, target_assigned := ta1, best_assigned := ba1,
          phases_target := pt1, phases_best := pb1, heap := hp1, pos := ps1,
          heap_len := hl1, q_search_idx := qsi1, q_search_stamp := qss1 } }
    have hsp1 := fullSparseInvW_afterAddUnit hsp hlen1 hw1
    c0_hsteps_nogrp
    c0_hsplit
    · exact ih1 (k + 1#64, ()) m1 (by dsimp only; rw [hk1]; omega)
        ⟨st1, hsp1, hcl1, hcv, hfl, hrepr, by rw [hk1]; omega, hss, hm1_f⟩
    · exact hQ false ext0 st1 m1 (FullM6HdrInvW.mk_inv hinv0.cfgOk hinv0.extOk hsp1) hcl1 hcv hfl
        hrepr
        (fun _ => by
          have hlt_lit :
              (st.scratch.shrink_stk[k.toNat]'hstk_len).toNat < 2 * st.core.cur_vars := by
            have := (hus0 k.toNat hk_lt).1
            rw [← hcv, ← hss, List.getElem?_eq_getElem hstk_len, Option.getD_some] at this
            exact this
          exact (hfail1 (by cases ok1 <;> first | rfl | exact absurd hc (by decide))).elim
            (fun hle => absurd hlt_lit (by omega)) (·.1))
        (fullM6HdrMem_unfocus_full hm1_f)
  · c0_hcall hProp
    refine ⟨c, F0, F_cur, ext0, st, R, rfl, hinv0.cfgOk, hinv0.extOk, hsp.1, hsp.2.1,
      hsp.2.2.2.2.2, fullM6HdrMem_unfocus_full hml, ?_⟩
    intro pr ext1 vals1 fl1 lvl1 rsns1 trl1 tp1 te1 prop1 unass1 unfl1 wvec1 arena1 wstk1
      wlen1 wu1 fuel1 ctype1 cref1 c01 c11 oom1 sc1 m1 _ hext1 _ hlen1 hw1 _ _ hperm1 hsc1
      _ _ _ _ hfl1 _ _ hpr1 _ _ hm1
    let st1 : FullState :=
      { core := { st.core with
          vals := vals1, flags := fl1, lvl := lvl1, rsns := rsns1, trl := trl1,
          trail_pos := tp1, trail_end := te1, propagated := prop1, unassigned := unass1,
          unflushed := unfl1, wvec := wvec1, arena := arena1, wstk := wstk1,
          wlen := wlen1, wusable := wu1, fuel := fuel1, confl_type := ctype1,
          confl_ref := cref1, confl_lit0 := c01, confl_lit1 := c11, oom := oom1 }
        scratch := sc1 }
    have hsp1 := fullSparseInvW_of_bcp hsp hlen1 hw1 hperm1 hsc1
    have hfl1' : st1.core.fuel.toNat ≤ s0.core.fuel.toNat := Nat.le_trans hfl1 hfl
    have hrepr1 : FullReprEquiv F_cur st1 := hrepr
    have hm1_f := fullM6HdrMem_focus_full hm1
    c0_hsteps_nogrp
    · exact hQ false ext1 st1 m1 (FullM6HdrInvW.mk_inv hinv0.cfgOk hext1 hsp1) hl hcv hfl1' hrepr1
        (fun _ => level0_unsat_of_conflict_okW hw1 hl (hpr1 hc).2.2)
        (fullM6HdrMem_unfocus_full hm1_f)
    · exact hQ false ext1 st1 m1 (FullM6HdrInvW.mk_inv hinv0.cfgOk hext1 hsp1) hl hcv hfl1'
        hrepr1 (fun _ => hw1.ext_sound.2 (hw1.inconsistent_sound hc))
        (fullM6HdrMem_unfocus_full hm1_f)
    · c0_hsteps_nogrp
      refine wp_loop_inv (ts := [i64])
        (fun (v, ()) mv => ∃ stv : FullState,
          FullSparseInvW c F0 F_cur stv ∧ stv.core.cur_level = 0 ∧
          stv.core.cur_vars = s0.core.cur_vars ∧ stv.core.fuel.toNat ≤ s0.core.fuel.toNat ∧
          FullReprEquiv F_cur stv ∧ v.toNat ≤ stv.core.cur_vars ∧
          stv.core.repr.length = 2 * c.max_vars ∧
          (FullMem c stv ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext1 ⋆ R)) mv)
        (fun (v, ()) _ => st1.core.cur_vars - v.toNat)
        ?_ ?_
      · exact fun J2 hJ2 => hJ2 (0#64, ()) m1
          ⟨st1, hsp1, hl, hcv, hfl1', hrepr1, Nat.zero_le _, hsp1.1.core_ok.repr_len, hm1_f⟩
      rintro J2 ⟨v, ⟨⟩⟩ mv ⟨stv, hspv, hlv, hcvv, hflv, hreprv, hv_le, hrlenv, hmv⟩ ih2
      have hcv_max : stv.core.cur_vars ≤ c.max_vars := hspv.1.core_ok.cur_vars_le
      c0_hsteps_nogrp
      c0_hsplit
      · have hv_lt : v.toNat < stv.core.cur_vars := by
          rw [hcvv, ← hcv]
          exact Nat.lt_of_lt_of_le (by assumption) (Nat.mod_le _ _)
        have hv1 : (v + 1#64).toNat = v.toNat + 1 := bv64_add1_toNat (by omega)
        have hcv_meas : stv.core.cur_vars = st1.core.cur_vars := hcvv.trans hcv.symm
        have h2v : (v <<< 1#64).toNat = 2 * v.toNat := by
          simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
        have hr_lt : 2 * v.toNat < stv.core.repr.length := by rw [hrlenv]; omega
        have hr1_lt : 2 * v.toNat + 1 < stv.core.repr.length := by rw [hrlenv]; omega
        have hf_lt : v.toNat < stv.core.flags.length := by
          rw [hspv.1.core_ok.flags_len]; omega
        c0_hsteps
        · c0_hcall hExtPush2
          refine ⟨c, stv, _, ⟨rfl, hspv.2.2.2.2.1.2⟩, hspv.1, hmv,
            fun _ st_p1 mp1 hpresp1 hlenp1 hp1 hm_p1 => ?_⟩
          have hsp_p1 := fullSparseInvW_afterExtPush2 hspv hlenp1 hpresp1 hp1.1 hp1.2.1
          c0_hsteps_nogrp
          c0_hcall hExtPush2
          refine ⟨c, st_p1, _, ⟨rfl, hsp_p1.2.2.2.2.1.2⟩, hsp_p1.1, hm_p1,
            fun _ st_p2 mp2 hpresp2 hlenp2 hp2 hm_p2 => ?_⟩
          have hsp_p2 := fullSparseInvW_afterExtPush2 hsp_p1 hlenp2 hpresp2 hp2.1 hp2.2.1
          have hcore_p2 : st_p2.core = stv.core :=
            (fullCoreState_agrees_with_scratch hpresp2).trans
              (fullCoreState_agrees_with_scratch hpresp1)
          have hcv_p2 : st_p2.core.cur_vars = stv.core.cur_vars :=
            congrArg FullCoreState.cur_vars hcore_p2
          c0_hsteps_nogrp
          c0_hcall hSetInact
          have htrunc_v : (v.setWidth 32).toNat = v.toNat := by simp; omega
          refine ⟨c, st_p2, _, rfl, hsp_p2.1, hm_p2, ?_⟩
          simp only [show ¬st_p2.core.cur_vars ≤ (v.setWidth 32).toNat by
            rw [htrunc_v, hcv_p2]; omega, ↓reduceIte]
          intro fl_s unass_s sc_s m_s hlen_s hpr_s hm_s
          let st_s : FullState :=
            { core := { st_p2.core with flags := fl_s, unassigned := unass_s }
              scratch := sc_s }
          have hsp_s := fullSparseInvW_setInact hsp_p2 hlen_s hpr_s
          have hrepr_p2 : FullReprEquiv F_cur st_p2 := by
            intro l hl
            have := hreprv l (by rw [← hcv_p2]; exact hl)
            change (st_p2.core.repr[l]?.getD 0#32).toNat < 2 * st_p2.core.cur_vars ∧ _
            rw [hcore_p2]; exact this
          have hrep_s : FullReprEquiv F_cur st_s := hrepr_p2
          c0_hsteps
          let st_f : FullState :=
            { st_s with scratch := { st_s.scratch with
                subst_cnt := st_s.scratch.subst_cnt + 1#64 } }
          have hsp_f : FullSparseInvW c F0 F_cur st_f :=
            ⟨⟨hsp_s.1.core_ok, { hsp_s.1.scratch_ok with }⟩, hsp_s.2⟩
          exact ih2 (v + 1#64, ()) _ (by dsimp only; rw [hv1]; omega)
            ⟨st_f, hsp_f,
              by dsimp only [st_f, st_s]; rw [hcore_p2]; exact hlv,
              by dsimp only [st_f, st_s]; rw [hcore_p2]; exact hcvv,
              by dsimp only [st_f, st_s]; rw [hcore_p2]; exact hflv,
              hrep_s, by dsimp only [st_f, st_s]; rw [hcore_p2, hv1]; omega,
              hsp_f.1.core_ok.repr_len, by assumption⟩
        · have hrlen2 : 2 * stv.core.cur_vars ≤ stv.core.repr.length := by rw [hrlenv]; omega
          have hrepr_r := fullReprEquiv_reset_pair hreprv hrlen2 hv_lt (by omega)
          have hsp_r := fullSparseInvW_repr_set2 hspv hrlenv.symm hv_lt
          have hval0 : BitVec.setWidth 32 (v <<< 1#64) = BitVec.ofNat 32 (2 * v.toNat) := by
            apply BitVec.eq_of_toNat_eq
            rw [BitVec.toNat_setWidth, h2v, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          have hidx0 :
              (BitVec.setWidth 64 (BitVec.setWidth 32 (v <<< 1#64))).toNat = 2 * v.toNat := by
            rw [BitVec.toNat_setWidth, hval0, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
              Nat.mod_eq_of_lt (by omega)]
          have hval1 : BitVec.setWidth 32 (v <<< 1#64) ^^^ 1#32 =
              BitVec.ofNat 32 (2 * v.toNat + 1) := by
            apply BitVec.eq_of_toNat_eq
            simp only [BitVec.toNat_xor, hval0, BitVec.toNat_ofNat,
              Nat.mod_eq_of_lt (by omega : 2 * v.toNat < 2 ^ 32),
              Nat.mod_eq_of_lt (by omega : 1 < 2 ^ 32),
              Nat.mod_eq_of_lt (by omega : 2 * v.toNat + 1 < 2 ^ 32),
              two_mul_xor_one]
          have h2v_xor :
              (BitVec.setWidth 64 (BitVec.setWidth 32 (v <<< 1#64) ^^^ 1#32)).toNat =
                2 * v.toNat + 1 := by
            rw [BitVec.toNat_setWidth, hval1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
              Nat.mod_eq_of_lt (by omega)]
          have h2v_xor' :
              (BitVec.setWidth 64 (BitVec.setWidth 32 (v <<< OfNat.ofNat 1) ^^^ 1)).toNat =
                2 * v.toNat + 1 := h2v_xor
          have hrep_set_len :
              (stv.core.repr.set
                (BitVec.setWidth 64 (BitVec.setWidth 32 (v <<< OfNat.ofNat 1))).toNat
                (BitVec.setWidth 32 (v <<< OfNat.ofNat 1))).length =
                stv.core.repr.length := List.length_set
          c0_hsteps
          refine ih2 (v + 1#64, ()) _ (by dsimp only; rw [hv1]; omega)
            ⟨_, hsp_r, hlv, hcvv, hflv, hrepr_r, by dsimp only; rw [hv1]; omega,
              hsp_r.1.core_ok.repr_len, ?_⟩
          dsimp only at hm
          have hset32 : BitVec.setWidth 32 (v <<< (1 : Nat)) =
              BitVec.ofNat 32 (2 * BitVec.toNat v) := by
            apply BitVec.eq_of_toNat_eq
            rw [BitVec.toNat_setWidth, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
            simp [Nat.mod_eq_of_lt (by omega : BitVec.toNat v * 2 ^ 1 < 2 ^ 64),
              Nat.mod_eq_of_lt (by omega : BitVec.toNat v * 2 ^ 1 < 2 ^ 32)]
            omega
          rw [hset32, ← hval0, hidx0, show (1 : BitVec 32) = 1#32 from rfl, h2v_xor, hval1,
            hval0] at hm
          exact hm
        · c0_hsteps
          exact ih2 (v + 1#64, ()) mv (by dsimp only; rw [hv1]; omega)
            ⟨stv, hspv, hlv, hcvv, hflv, hreprv, by rw [hv1]; omega, hrlenv, hmv⟩
        · c0_hsteps
          exact ih2 (v + 1#64, ()) mv (by dsimp only; rw [hv1]; omega)
            ⟨stv, hspv, hlv, hcvv, hflv, hreprv, by rw [hv1]; omega, hrlenv, hmv⟩
      · c0_hsteps_nogrp
        exact hQ true ext1 stv mv (FullM6HdrInvW.mk_inv hinv0.cfgOk hext1 hspv) hlv hcvv hflv
          hreprv (fun h => by cases h) (fullM6HdrMem_unfocus_full hmv)

end

end LeanQbe.T.Examples.Kissat.Proof.Substitute
