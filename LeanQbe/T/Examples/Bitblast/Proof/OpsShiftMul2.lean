/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Bitblast.Src.OpsShiftMul
public import LeanQbe.T.Examples.Bitblast.Proof.OpsShiftMulSpecs
public import LeanQbe.T.Examples.Bitblast.Proof.OpsShiftMul2Helpers
public import LeanQbe.T.Examples.Bitblast.Proof.OpsShiftMul2Stages
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.ProofKit
import LeanQbe.T.Logic.MemLemmas

/-!
# Canonical WP Proofs for `bv_blast_mul` & `bv_blast_clz` (`Bitblast.Proof.OpsShiftMul2`)

Proves canonical `Func.wp` contracts for the remaining `2` of `12` functions in
`Src/OpsShiftMul.lean`: `bv_blast_clz_wp` (`3` extern callees) and `bv_blast_mul_wp`
(`5` extern callees), using the factored invariants and stage lemmas from
`OpsShiftMul2Helpers` and `OpsShiftMul2Stages`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Bitblast.Proof

open Std.Tactic.BVDecide
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofKit
open LeanQbe.T.ProofUtil
open Std.ExtHashMap
open LeanQbe.T.Examples.Bitblast.Ref
open LeanQbe.T.Examples.Bitblast.Src.OpsShiftMul

/-! ## 1. Pure `clzAux = BitVec.clz` & Frame Helpers -/

private theorem clzAux_of_msb {w : Nat} (va : BitVec w) (k m : Nat) (hk : k ≤ w)
    (hm : m < k) (hmt : va.getLsbD m = true)
    (hhi : ∀ j, m < j → j < k → va.getLsbD j = false) :
    clzAux va k = BitVec.ofNat w (w - 1 - m) := by
  induction k with
  | zero => omega
  | succ k ih =>
    rw [clzAux_succ]
    by_cases hmk : m = k
    · subst hmk; rw [hmt]; rfl
    · have hkf : va.getLsbD k = false := hhi k (by omega) (Nat.lt_succ_self k)
      rw [hkf]
      exact ih (by omega) (by omega) (fun j h1 h2 => hhi j h1 (by omega))

private theorem clzAux_eq_clz {w : Nat} (va : BitVec w) : clzAux va w = va.clz := by
  by_cases hw0 : w = 0
  · subst hw0; exact Subsingleton.elim _ _
  have hlt2 : w < 2 ^ w := Nat.lt_two_pow_self
  by_cases hz : va = 0#w
  · subst hz
    have h0 : ∀ k, k ≤ w → clzAux (0#w) k = BitVec.ofNat w w := by
      intro k hk
      induction k with
      | zero => rfl
      | succ k ih => rw [clzAux_succ, BitVec.getLsbD_zero]; exact ih (by omega)
    apply BitVec.eq_of_toNat_eq
    rw [h0 w (Nat.le_refl _), BitVec.toNat_ofNat, BitVec.toNat_clz,
      ite_eq_left (show (0#w : BitVec w) = 0 from rfl), Nat.mod_eq_of_lt hlt2]
  · have hpos : va.toNat ≠ 0 := fun h => hz (BitVec.eq_of_toNat_eq (by simp [h]))
    let m := va.toNat.log2
    have hm_le : 2 ^ m ≤ va.toNat := Nat.log2_self_le hpos
    have hm_lt : va.toNat < 2 ^ (m + 1) := Nat.lt_log2_self
    have hm_w : m < w := (Nat.log2_lt hpos).mpr (by have := va.isLt; omega)
    have hmt : va.getLsbD m = true := by
      rw [BitVec.getLsbD_eq_getElem hm_w, BitVec.getElem_eq_testBit_toNat,
        Nat.testBit_eq_decide_div_mod_eq]
      have hd_pos : 0 < va.toNat / 2 ^ m := Nat.div_pos hm_le (Nat.two_pow_pos m)
      have hd_lt : va.toNat / 2 ^ m < 2 :=
        (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos m)).mpr (by rw [← Nat.pow_succ']; exact hm_lt)
      have : va.toNat / 2 ^ m = 1 := by omega
      simp [this]
    have hhi : ∀ j, m < j → j < w → va.getLsbD j = false := by
      intro j hmj hjw
      rw [BitVec.getLsbD_eq_getElem hjw, BitVec.getElem_eq_testBit_toNat,
        Nat.testBit_eq_decide_div_mod_eq]
      have hpow : 2 ^ (m + 1) ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) (by omega)
      have hdiv : va.toNat / 2 ^ j = 0 := Nat.div_eq_of_lt (by omega)
      simp [hdiv]
    apply BitVec.eq_of_toNat_eq
    rw [clzAux_of_msb va w m (Nat.le_refl w) hm_w hmt hhi, BitVec.toNat_ofNat,
      BitVec.toNat_clz, ite_eq_right (show va ≠ 0 from hz), Nat.mod_eq_of_lt (by omega)]
    omega

/-! ## 3. Canonical WP Theorems (`bv_blast_clz` & `bv_blast_mul`) -/

public section

/-- Canonical `Func.wp` contract for `bv_blast_clz(h, a_off, w)`. -/
theorem bv_blast_clz_wp (Γ : Env)
    (hSliceOk : Γ.Has "bv_slice_ok" smBvSliceOkSpec)
    (hAlloc : Γ.Has "bv_lits_alloc" bvLitsAllocSpec)
    (hIte : Γ.Has "bv_aig_ite" bvAigIteSpec)
    (xs : Tup Val [i64, i32, i32]) (m : Mem 64)
    (Q : Post [i32]) (X : XPost)
    (hpre : bvBlastClzSpec xs m Q X) :
    Func.wp Γ bv_blast_clz_body xs m Q X := by
  rcases xs with ⟨h, aOff, w, ⟨⟩⟩
  rcases hpre with ⟨hdr0, g0, aw0, ht0, lp0, R, haig0, hcap0, hwfa_imp, hm0, hQ⟩
  dsimp only [Func.wp]
  rw [bv_blast_clz_split_eq]
  dsimp only [m2Cmp, m2Bin, m2Add64, m2Zext, m2LoadLit, m2AddrLit, m2LoadOom]
  refine wp_join_state (α := PUnit) (fun _ => ())
    (fun _ mB => (hdr0.oom ≠ 0#32 ∨ sliceOkBool hdr0 aOff w = false) ∧ mB = m) ?_ ?_
  · intro _ _ mB ⟨hbad, hmB⟩
    subst hmB; c0_hsteps
    exact clz_bad_close haig0 hbad (sep_ac hm) hQ
  · intro _ hJ_bad
    c0_hstraight; c0_hsplit
    · exact hJ_bad () m ⟨Or.inl (by c0_bv_omega [hc]), rfl⟩
    · have hoom0 : hdr0.oom = 0#32 := by c0_bv_omega [hc]
      clear hc
      c0_hcall hSliceOk
      refine ⟨hdr0, array64 hdr0.aig_ptr aw0 ⋆ array (t := i32) hdr0.ht_ptr ht0 ⋆
        array (t := i32) hdr0.lits_ptr lp0 ⋆ R, sep_ac hm0, ?_⟩
      c0_hstraight; c0_hsplit
      · have hsla : sliceOkBool hdr0 aOff w = true := by
          cases hb : sliceOkBool hdr0 aOff w <;> simp_all
        clear hc
        have hwfa0 := hwfa_imp hoom0 hsla
        have hlen0_cap : hdr0.lits_len.toNat ≤ hdr0.lits_cap.toNat := by
          unfold sliceOkBool at hsla; simp only [decide_eq_true_eq] at hsla; exact hsla.1
        have ha_hi : aOff.toNat + w.toNat ≤ hdr0.lits_len.toNat := by
          unfold sliceOkBool at hsla; simp only [decide_eq_true_eq] at hsla; omega
        c0_hcall hAlloc
        refine ⟨hdr0, array64 hdr0.aig_ptr aw0 ⋆ array (t := i32) hdr0.ht_ptr ht0 ⋆
          array (t := i32) hdr0.lits_ptr lp0 ⋆ R, sep_ac hm0, ?_⟩
        by_cases hfit1 : w.toNat ≤ hdr0.lits_cap.toNat - hdr0.lits_len.toNat
        · rw [ite_eq_left ⟨hoom0, hlen0_cap, hfit1⟩]
          intro mA hmA
          c0_hstraight; c0_hsplit
          · exact absurd hoom0 (by c0_bv_omega [hc])
          · clear hc
            have hl1_eq : (hdr0.lits_len + w).toNat = hdr0.lits_len.toNat + w.toNat := by
              rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by have := hdr0.lits_cap.isLt; omega)]
            c0_hstraight; c0_hsplit
            · have hw0 : w = 0#32 := by c0_bv_omega [hc]
              clear hc
              have hw_n : w.toNat = 0 := by rw [hw0]; rfl
              c0_hsteps
              exact clz_ok_close hoom0 hsla
                (mul2_opsFrame_with_lits_len (Modifies.refl _ hdr0) (hdr0.lits_len + w))
                (mul2_aig_le_self g0)
                (mul2_aigInv_with_lits_len haig0 (hdr0.lits_len + w)) rfl
                (by dsimp only; rw [hl1_eq]; omega) (by dsimp only; rw [hl1_eq]; omega)
                hcap0 (by omega) (fun _ _ => rfl) hoom0 rfl (fun _ hk => by omega)
                (fun _ _ _ => BitVec.eq_of_getLsbD_eq fun i hi => by omega)
                (sep_ac hmA) hQ
            · have hw_pos : 0 < w.toNat := by c0_bv_omega [hc]
              clear hc
              c0_hsteps
              rw [show ({ hdr0 with lits_len := hdr0.lits_len + w } : BVHdrState).lits_ptr =
                hdr0.lits_ptr from rfl]
              refine wp_while_state (α := Nat × List (BitVec 32))
                (fun (j, _) => (BitVec.ofNat 32 j, ())) (fun (j, _) => w.toNat - j)
                (fun st mJ => ClzInitInv w hdr0 { hdr0 with lits_len := hdr0.lits_len + w }
                  g0 aw0 ht0 lp0 R st mJ h) ?_ ?_
              · intro J_i hJ_i; c0_hsteps
                exact hJ_i (0, lp0) mA
                  ⟨Nat.zero_le _, rfl, fun _ _ => rfl, fun _ hk => by omega,
                    fun _ _ hk => by omega, sep_ac hmA⟩
              · intro J_i ⟨j, lpJ⟩ mJ hinvJ ih_i
                have hj_w := hinvJ.1
                have hj32 : (BitVec.ofNat 32 j).toNat = j := by
                  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := w.isLt; omega)]
                c0_hstraight; c0_hsplit
                · have hj_lt : j < w.toNat := by
                    have h1 : BitVec.ofNat 32 j < w := hc
                    rw [BitVec.lt_def, hj32] at h1; exact h1
                  clear hc
                  rcases hinvJ with ⟨_, hlpJ_len, hpreJ, hwf_prevJ, hev_prevJ, hmJ⟩
                  refine wp_join_state (α := BitVec 32) (fun c => (c, ()))
                    (fun c mCb =>
                      c = (if BitVec.ofNat 32 j < 32#32 then
                        w >>> BitVec.ofNat 32 j &&& 1#32 else 0#32) ∧ mCb = mJ) ?_ ?_
                  · intro _ wb mCb ⟨hwb, hmCb⟩; subst hwb hmCb
                    have houtj_sw : ((hdr0.lits_len + BitVec.ofNat 32 j).setWidth 64).toNat =
                        hdr0.lits_len.toNat + j := by
                      rw [mul2_setWidth64_toNat, BitVec.toNat_add, hj32,
                        Nat.mod_eq_of_lt (by have := hdr0.lits_cap.isLt; omega)]
                    c0_hsteps
                    rw [houtj_sw] at hm
                    have hstep := clz_init_step_ok hlpJ_len hpreJ hwf_prevJ hev_prevJ hj_lt hj32
                      (by rw [hlpJ_len, hcap0]; omega) rfl
                    rw [mul2_bv32_succ_add (by have := w.isLt; omega)]
                    exact ih_i (j + 1, _) _ (by dsimp only; omega)
                      ⟨by omega, hstep.1, hstep.2.1, hstep.2.2.1, hstep.2.2.2, sep_ac hm⟩
                  · intro J_cb hJ_cb; c0_hstraight; c0_hsplit
                    · have hj32_lt : BitVec.ofNat 32 j < 32#32 := hc
                      clear hc; c0_hsteps
                      have hmod : (BitVec.ofNat 32 j).toNat % 32 = (BitVec.ofNat 32 j).toNat :=
                        Nat.mod_eq_of_lt (BitVec.lt_def.mp hj32_lt)
                      exact hJ_cb _ mJ ⟨by rw [ite_eq_left hj32_lt, hmod]; rfl, rfl⟩
                    · have hj32_ge : ¬ BitVec.ofNat 32 j < 32#32 := hc
                      clear hc; c0_hsteps
                      exact hJ_cb 0#32 mJ ⟨by rw [ite_eq_right hj32_ge], rfl⟩
                · have hj_eq : j = w.toNat := by
                    have h1 : ¬ BitVec.ofNat 32 j < w := hc
                    rw [BitVec.lt_def, hj32] at h1; omega
                  clear hc; subst j
                  rcases hinvJ with ⟨_, hlpJ_len, hpreJ, hwf_prevJ, hev_prevJ, hmJ⟩
                  refine wp_while_state
                    (α := BitVec 32 × Nat × BVHdrState × Aig × List (BitVec 64) ×
                      List (BitVec 32) × List (BitVec 32))
                    (fun (jd, curr, _) => (jd, BitVec.ofNat 32 curr, ()))
                    (fun (_, curr, _) => w.toNat - curr)
                    (fun (_, curr, st) mC =>
                      ClzOuterInv aOff w hdr0 g0 lp0 R (curr, st) mC h) ?_ ?_
                  · intro J_c hJ_c; c0_hsteps
                    refine hJ_c (BitVec.ofNat 32 w.toNat, 0,
                        { hdr0 with lits_len := hdr0.lits_len + w }, g0, aw0, ht0, lpJ) mJ
                      ⟨Nat.zero_le _,
                        mul2_opsFrame_with_lits_len (Modifies.refl _ hdr0)
                          (hdr0.lits_len + w),
                        mul2_aig_le_self g0,
                        mul2_aigInv_with_lits_len haig0 (hdr0.lits_len + w), hoom0, rfl,
                        hlpJ_len, hpreJ, fun k hk => hwf_prevJ k hk, fun ρ va _ => ?_, sep_ac hmJ⟩
                    apply BitVec.eq_of_getLsbD_eq
                    intro i hi
                    rw [evalPoolSlice_getLsbD hi, hev_prevJ ρ i hi, clzAux_zero]
                  · intro J_c ⟨jd, curr, hdrC, gC, awC, htC, lpC⟩ mC hinvC ih_c
                    have hcurr_w := hinvC.1
                    have hcurr32 : (BitVec.ofNat 32 curr).toNat = curr := by
                      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := w.isLt; omega)]
                    c0_hstraight; c0_hsplit
                    · have hcurr_lt : curr < w.toNat := by
                        have h1 : BitVec.ofNat 32 curr < w := hc
                        rw [BitVec.lt_def, hcurr32] at h1; exact h1
                      clear hc
                      rcases hinvC with ⟨_, hfrC, hextC, haigC, hoomC, hlenC, hlpC_len, hpreC,
                        hwfC, hevC, hmC⟩
                      have hac_sw :
                          ((aOff + BitVec.ofNat 32 curr).setWidth 64).toNat =
                            aOff.toNat + curr := by
                        rw [mul2_setWidth64_toNat, BitVec.toNat_add, hcurr32,
                          Nat.mod_eq_of_lt (by have := hdr0.lits_cap.isLt; omega)]
                      have hxc_ag :
                          lpC[((aOff + BitVec.ofNat 32 curr).setWidth 64).toNat]'(by
                            rw [hac_sw, hlpC_len, hcap0]; omega) =
                          lp0.getD (aOff.toNat + curr) 0#32 := by
                        rw [← mul2_getD_eq_getElem lpC (by rw [hac_sw, hlpC_len, hcap0]; omega),
                          hac_sw]
                        exact hpreC _ (by omega)
                      c0_hstraight
                      refine wp_join_state (α := BitVec 32) (fun jn => (jn, ()))
                        (fun _ mN => ∃ hdrN gN awN htN lpN,
                          ClzOuterInv aOff w hdr0 g0 lp0 R (curr + 1, hdrN, gN, awN, htN, lpN) mN
                            h) ?_ ?_
                      · intro _ jn mN ⟨hdrN, gN, awN, htN, lpN, hinvN⟩
                        c0_hsteps
                        rw [mul2_bv32_succ_add (by have := w.isLt; omega)]
                        exact ih_c (jn, curr + 1, hdrN, gN, awN, htN, lpN) mN (by dsimp only; omega)
                          hinvN
                      · intro J_next hJ_next; c0_hstraight; c0_hsplit
                        · have hxc_ne :
                              lpC[((aOff + BitVec.ofNat 32 curr).setWidth 64).toNat]'(by
                                rw [hac_sw, hlpC_len, hcap0]; omega) ≠ 0#32 := by
                            c0_bv_omega [hc]
                          clear hc
                          exact clz_inner_wp hIte hcap0 hfit1 hl1_eq hcurr_lt hcurr32 ha_hi hwfa0
                            ⟨hcurr_w, hfrC, hextC, haigC, hoomC, hlenC, hlpC_len, hpreC, hwfC,
                              hevC, hmC⟩
                            hxc_ag (fun jn mN hinvN => hJ_next jn mN hinvN) hQ
                        · have hxc0 : lp0.getD (aOff.toNat + curr) 0#32 = 0#32 := by
                            rw [← hxc_ag]; c0_bv_omega [hc]
                          clear hc
                          exact hJ_next jd mC ⟨hdrC, gC, awC, htC, lpC, by
                            refine ⟨by omega, hfrC, hextC, haigC, hoomC, hlenC, hlpC_len, hpreC,
                              hwfC, ?_, hmC⟩
                            have hxc0' : lpC.getD (aOff.toNat + curr) 0#32 = 0#32 := by
                              rw [hpreC _ (by omega)]; exact hxc0
                            exact clz_skip_step_ok hxc0' hpreC ha_hi (by rw [hcap0]; omega)
                              hcurr_lt hevC⟩
                    · have hcurr_eq : curr = w.toNat := by
                        have h1 : ¬ BitVec.ofNat 32 curr < w := hc
                        rw [BitVec.lt_def, hcurr32] at h1; omega
                      clear hc; subst curr
                      rcases hinvC with ⟨_, hfrC, hextC, haigC, hoomC, hlenC, hlpC_len, hpreC,
                        hwfC, hevC, hmC⟩
                      c0_hsteps
                      rw [← hfrC.lits_ptr] at hmC
                      exact clz_ok_close hoom0 hsla hfrC hextC haigC hlpC_len
                        (by rw [hlenC, hl1_eq]; omega)
                        (by rw [hlenC, hl1_eq, hfrC.lits_cap]; omega)
                        hcap0 (by omega) hpreC hoomC hlenC hwfC
                        (fun ρ va hva => by rw [hevC ρ va hva, clzAux_eq_clz va])
                        (sep_ac hmC) hQ
        · rw [ite_eq_right (fun ⟨_, _, h3⟩ => hfit1 h3)]
          dsimp only
          rw [ite_eq_right (show ¬ hdr0.oom ≠ 0#32 from fun h => h hoom0)]
          intro mA hmA
          c0_hstraight; c0_hsplit
          · have hoom_ne : (1#32 : BitVec 32) ≠ 0#32 := by decide
            clear hc; c0_hsteps
            exact clz_oom_close (ops_lits_pure_guard_oom hdr0).2.2.2
              (mul2_aig_le_self g0) (mul2_aigInv_with_oom haig0 1#32) rfl (Nat.le_refl _)
              hlen0_cap (fun _ _ => rfl) hoom_ne (sep_ac hmA) hQ
          · exact absurd (show (1#32 : BitVec 32) = 0#32 from by c0_bv_omega [hc]) (by decide)
      · exact hJ_bad () m ⟨Or.inr (by cases hb : sliceOkBool hdr0 aOff w <;> simp_all), rfl⟩

/-- Canonical `Func.wp` contract for `bv_blast_mul(h, a_off, b_off, w)`. -/
theorem bv_blast_mul_wp (Γ : Env)
    (hSliceOk : Γ.Has "bv_slice_ok" smBvSliceOkSpec)
    (hAlloc : Γ.Has "bv_lits_alloc" bvLitsAllocSpec)
    (hAnd : Γ.Has "bv_mk_and" bvMkAndSpec)
    (hMark : Γ.Has "bv_lits_mark" bvLitsMarkSpec)
    (hRel : Γ.Has "bv_lits_release" bvLitsReleaseSpec)
    (hAdd : Γ.Has "bv_blast_add" smBvBlastAddSpec)
    (hIte : Γ.Has "bv_aig_ite" bvAigIteSpec)
    (xs : Tup Val [i64, i32, i32, i32]) (m : Mem 64)
    (Q : Post [i32]) (X : XPost)
    (hpre : bvBlastMulSpec xs m Q X) :
    Func.wp Γ bv_blast_mul_body xs m Q X := by
  rcases xs with ⟨h, aOff, bOff, w, ⟨⟩⟩
  rcases hpre with ⟨hdr0, g0, aw0, ht0, lp0, R, haig0, hcap0, _, hwf_imp, hm0, hQ⟩
  dsimp only [Func.wp]
  rw [bv_blast_mul_split_eq]
  dsimp only [m2Cmp, m2Bin, m2Add64, m2Zext, m2LoadLit, m2AddrLit, m2LoadOom]
  refine wp_join_state (α := PUnit) (fun _ => ())
    (fun _ mB =>
      (hdr0.oom ≠ 0#32 ∨ sliceOkBool hdr0 aOff w = false ∨ sliceOkBool hdr0 bOff w = false) ∧
      mB = m) ?_ ?_
  · intro _ _ mB ⟨hbad, hmB⟩
    subst hmB; c0_hsteps
    exact mul_bad_close haig0 hbad (sep_ac hm) hQ
  · intro _ hJ_bad
    c0_hstraight; c0_hsplit
    · exact hJ_bad () m ⟨Or.inl (by c0_bv_omega [hc]), rfl⟩
    · have hoom0 : hdr0.oom = 0#32 := by c0_bv_omega [hc]
      clear hc
      c0_hcall hSliceOk
      refine ⟨hdr0, array64 hdr0.aig_ptr aw0 ⋆ array (t := i32) hdr0.ht_ptr ht0 ⋆
        array (t := i32) hdr0.lits_ptr lp0 ⋆ R, sep_ac hm0, ?_⟩
      c0_hstraight; c0_hsplit
      · have hsla : sliceOkBool hdr0 aOff w = true := by
          cases hb : sliceOkBool hdr0 aOff w <;> simp_all
        clear hc
        c0_hcall hSliceOk
        refine ⟨hdr0, array64 hdr0.aig_ptr aw0 ⋆ array (t := i32) hdr0.ht_ptr ht0 ⋆
          array (t := i32) hdr0.lits_ptr lp0 ⋆ R, sep_ac hm0, ?_⟩
        c0_hstraight; c0_hsplit
        · have hslb : sliceOkBool hdr0 bOff w = true := by
            cases hb : sliceOkBool hdr0 bOff w <;> simp_all
          clear hc
          obtain ⟨hwfa0, hwfb0⟩ := hwf_imp hoom0 rfl hsla hslb
          have hlen0_cap : hdr0.lits_len.toNat ≤ hdr0.lits_cap.toNat := by
            unfold sliceOkBool at hsla; simp only [decide_eq_true_eq] at hsla; exact hsla.1
          have ha_hi : aOff.toNat + w.toNat ≤ hdr0.lits_len.toNat := by
            unfold sliceOkBool at hsla; simp only [decide_eq_true_eq] at hsla; omega
          have hb_hi : bOff.toNat + w.toNat ≤ hdr0.lits_len.toNat := by
            unfold sliceOkBool at hslb; simp only [decide_eq_true_eq] at hslb; omega
          c0_hcall hAlloc
          refine ⟨hdr0, array64 hdr0.aig_ptr aw0 ⋆ array (t := i32) hdr0.ht_ptr ht0 ⋆
            array (t := i32) hdr0.lits_ptr lp0 ⋆ R, sep_ac hm0, ?_⟩
          by_cases hfit1 : w.toNat ≤ hdr0.lits_cap.toNat - hdr0.lits_len.toNat
          · rw [ite_eq_left ⟨hoom0, hlen0_cap, hfit1⟩]
            intro mA hmA
            c0_hstraight; c0_hsplit
            · exact absurd hoom0 (by c0_bv_omega [hc])
            · clear hc
              have hl1_eq : (hdr0.lits_len + w).toNat = hdr0.lits_len.toNat + w.toNat := by
                rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by have := hdr0.lits_cap.isLt; omega)]
              c0_hstraight; c0_hsplit
              · have hw0 : w = 0#32 := by c0_bv_omega [hc]
                clear hc
                have hw_n : w.toNat = 0 := by rw [hw0]; rfl
                c0_hsteps
                exact mul_ok_close hoom0 hsla hslb
                  (mul2_opsFrame_with_lits_len (Modifies.refl _ hdr0) (hdr0.lits_len + w))
                  (mul2_aig_le_self g0)
                  (mul2_aigInv_with_lits_len haig0 (hdr0.lits_len + w)) rfl
                  (by dsimp only; rw [hl1_eq]; omega) (by dsimp only; rw [hl1_eq]; omega)
                  hcap0 (by omega) (fun _ _ => rfl) hoom0 rfl (fun _ hk => by omega)
                  (fun _ _ _ _ _ => BitVec.eq_of_getLsbD_eq fun i hi => by omega)
                  (sep_ac hmA) hQ
              · have hw_pos : 0 < w.toNat := by c0_bv_omega [hc]
                clear hc
                have hb0_sw : (bOff.setWidth 64).toNat = bOff.toNat :=
                  mul2_setWidth64_toNat bOff
                have hb0_ag :
                    lp0[(bOff.setWidth 64).toNat]'(by rw [hb0_sw, hcap0]; omega) =
                    lp0.getD bOff.toNat 0#32 := by
                  rw [← mul2_getD_eq_getElem lp0 (by rw [hb0_sw, hcap0]; omega), hb0_sw]
                c0_hsteps
                refine wp_while_state
                  (α := Nat × BVHdrState × Aig × List (BitVec 64) × List (BitVec 32) ×
                    List (BitVec 32))
                  (fun (j, _) => (BitVec.ofNat 32 j, ())) (fun (j, _) => w.toNat - j)
                  (fun st mJ =>
                    MulInitInv aOff bOff w hdr0 g0 lp0 R
                      lp0[(bOff.setWidth 64).toNat] st mJ h) ?_ ?_
                · intro J_i hJ_i; c0_hsteps
                  exact hJ_i (0, { hdr0 with lits_len := hdr0.lits_len + w }, g0, aw0, ht0, lp0)
                    mA
                    ⟨Nat.zero_le _,
                      mul2_opsFrame_with_lits_len (Modifies.refl _ hdr0)
                        (hdr0.lits_len + w),
                      mul2_aig_le_self g0,
                      mul2_aigInv_with_lits_len haig0 (hdr0.lits_len + w), hoom0, rfl, rfl,
                      fun _ _ => rfl, by rw [hb0_ag]; exact hwfb0 0 hw_pos,
                      fun _ hk => by omega, fun _ _ _ _ hk => by omega, sep_ac hmA⟩
                · intro J_i ⟨j, hdrJ, gJ, awJ, htJ, lpJ⟩ mJ hinvJ ih_i
                  have hj_w := hinvJ.1
                  have hj32 : (BitVec.ofNat 32 j).toNat = j := by
                    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := w.isLt; omega)]
                  c0_hstraight; c0_hsplit
                  · have hj_lt : j < w.toNat := by
                      have h1 : BitVec.ofNat 32 j < w := hc
                      rw [BitVec.lt_def, hj32] at h1; exact h1
                    clear hc
                    rcases hinvJ with ⟨_, hfrJ, hextJ, haigJ, hoomJ, hlenJ, hlpJ_len, hpreJ,
                      hwf_y0J, hwf_prevJ, hev_prevJ, hmJ⟩
                    have houtj_sw : ((hdr0.lits_len + BitVec.ofNat 32 j).setWidth 64).toNat =
                        hdr0.lits_len.toNat + j := by
                      rw [mul2_setWidth64_toNat, BitVec.toNat_add, hj32,
                        Nat.mod_eq_of_lt (by have := hdr0.lits_cap.isLt; omega)]
                    have haj_sw : ((aOff + BitVec.ofNat 32 j).setWidth 64).toNat =
                        aOff.toNat + j := by
                      rw [mul2_setWidth64_toNat, BitVec.toNat_add, hj32,
                        Nat.mod_eq_of_lt (by have := hdr0.lits_cap.isLt; omega)]
                    have haj_ag :
                        lpJ[((aOff + BitVec.ofNat 32 j).setWidth 64).toNat]'(by
                          rw [haj_sw, hlpJ_len, hcap0]; omega) =
                        lp0.getD (aOff.toNat + j) 0#32 := by
                      rw [← mul2_getD_eq_getElem lpJ (by rw [haj_sw, hlpJ_len, hcap0]; omega),
                        haj_sw]
                      exact hpreJ _ (by omega)
                    have hwf_aj :
                        ((lp0.getD (aOff.toNat + j) 0#32) >>> 1).toNat <
                          gJ.A + 1 + gJ.nodes.size := by
                      have hsz : g0.A + 1 + g0.nodes.size ≤ gJ.A + 1 + gJ.nodes.size := by
                        have := hextJ.1; have := hextJ.2.1; omega
                      exact Nat.lt_of_lt_of_le (hwfa0 j hj_lt) hsz
                    c0_hstraight; c0_hcall hAnd
                    refine ⟨hdrJ, gJ, awJ, htJ, array (t := i32) hdr0.lits_ptr lpJ ⋆ R, haigJ,
                      fun _ => ⟨by rw [haigJ.aig_len_eq]; exact hwf_y0J,
                        by rw [haj_ag, haigJ.aig_len_eq]; exact hwf_aj⟩,
                      sep_ac hmJ,
                      fun ret hdrN gN awN htN mN hfrN hextN _ haigN hoomN _ hevN hmN => ?_⟩
                    have hfr0N := hfrJ.trans hfrN.mono
                    have hext0N := Aig.extends_trans hextJ hextN
                    have hlenN : hdrN.lits_len = hdr0.lits_len + w := hfrN.lits_len.trans hlenJ
                    rw [← hfrJ.lits_ptr] at hmN
                    have hmN' := ops_aig_frame_unfocus hfrN.mono hmN
                    rw [hfr0N.lits_ptr] at hmN'
                    c0_hstraight; rw [houtj_sw] at hm; c0_hsplit
                    · have hoom_ne : hdrN.oom ≠ 0#32 := by c0_bv_omega [hc]
                      clear hc; c0_hsteps; rw [← hfr0N.lits_ptr] at hm
                      exact mul_oom_close (lp' := lpJ.set (hdr0.lits_len.toNat + j) ret)
                        hfr0N hext0N haigN (by simp [hlpJ_len])
                        (by rw [hlenN, hl1_eq]; omega)
                        (by rw [hlenN, hl1_eq, hfr0N.lits_cap]; omega)
                        (fun q hq => by
                          rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne (by omega),
                            ← List.getD_eq_getElem?_getD]
                          exact hpreJ q hq)
                        hoom_ne (sep_ac hm) hQ
                    · have hoomN0 : hdrN.oom = 0#32 := by c0_bv_omega [hc]
                      clear hc; c0_hsteps
                      obtain ⟨hret_bd, hret_ev⟩ := hevN hoomN0
                      rw [haigN.aig_len_eq] at hret_bd
                      have hstep := mul_and_step_ok hlpJ_len hpreJ hwf_y0J hwfa0 hwfb0 hb0_ag
                        hwf_prevJ hev_prevJ hj_lt (by rw [hlpJ_len, hcap0]; omega) hextN hextJ
                        (by rw [hcap0]; omega) (by rw [hcap0]; omega) hret_bd
                        (fun ρ => by rw [hret_ev ρ]; dsimp only; rw [haj_ag]) rfl
                      rw [mul2_bv32_succ_add (by have := w.isLt; omega)]
                      exact ih_i (j + 1, hdrN, gN, awN, htN, _) _ (by dsimp only; omega)
                        ⟨by omega, hfr0N, hext0N, haigN, hoomN0, hlenN, hstep.1, hstep.2.1,
                          hstep.2.2.1, hstep.2.2.2.1, hstep.2.2.2.2, sep_ac hm⟩
                  · have hj_eq : j = w.toNat := by
                      have h1 : ¬ BitVec.ofNat 32 j < w := hc
                      rw [BitVec.lt_def, hj32] at h1; omega
                    clear hc; subst j
                    obtain ⟨hwf_outJ, hev_outJ⟩ := mulInitInv_to_eval (y0 := 0#64) hinvJ
                    rcases hinvJ with ⟨_, hfrJ, hextJ, haigJ, hoomJ, hlenJ, hlpJ_len, hpreJ,
                      _, _, _, hmJ⟩
                    c0_hstraight; c0_hsplit
                    · have hw1 : w = 1#32 := by c0_bv_omega [hc]
                      clear hc
                      have hw1_n : w.toNat = 1 := by rw [hw1]; rfl
                      c0_hsteps
                      rw [← hfrJ.lits_ptr] at hmJ
                      exact mul_ok_close hoom0 hsla hslb hfrJ hextJ haigJ hlpJ_len
                        (by rw [hlenJ, hl1_eq]; omega)
                        (by rw [hlenJ, hl1_eq, hfrJ.lits_cap]; omega)
                        hcap0 (by omega) hpreJ hoomJ hlenJ hwf_outJ
                        (fun ρ va vb hva hvb => by
                          apply BitVec.eq_of_getLsbD_eq
                          intro i hi
                          have hi0 : i = 0 := by omega
                          subst hi0
                          rw [hev_outJ ρ va vb hva hvb, mulRec_zero_getLsbD va vb (by omega),
                            BitVec.getLsbD_eq_getElem (by omega),
                            BitVec.getLsbD_eq_getElem (by omega),
                            BitVec.getLsbD_eq_getElem (by omega),
                            BitVec.getElem_eq_testBit_toNat, BitVec.getElem_eq_testBit_toNat,
                            BitVec.getElem_eq_testBit_toNat, BitVec.toNat_mul]
                          have hpow : 2 ^ w.toNat = 2 := by rw [hw1_n]
                          have ha : va.toNat = 0 ∨ va.toNat = 1 := by
                            have hlt : va.toNat < 2 := by rw [← hpow]; exact va.isLt
                            omega
                          have hb : vb.toNat = 0 ∨ vb.toNat = 1 := by
                            have hlt : vb.toNat < 2 := by rw [← hpow]; exact vb.isLt
                            omega
                          rcases ha with ha0 | ha1 <;> rcases hb with hb0 | hb1 <;> simp [*])
                        (sep_ac hmJ) hQ
                    · have hw_gt1 : 1 < w.toNat := by c0_bv_omega [hc]
                      clear hc
                      c0_hcall hMark
                      refine ⟨hdrJ, array64 hdrJ.aig_ptr awJ ⋆ array (t := i32) hdrJ.ht_ptr htJ ⋆
                        array (t := i32) hdr0.lits_ptr lpJ ⋆ R, sep_ac hmJ, ?_⟩
                      c0_hcall hAlloc
                      refine ⟨hdrJ, array64 hdrJ.aig_ptr awJ ⋆ array (t := i32) hdrJ.ht_ptr htJ ⋆
                        array (t := i32) hdr0.lits_ptr lpJ ⋆ R, sep_ac hmJ, ?_⟩
                      by_cases hfit2 : w.toNat ≤ hdrJ.lits_cap.toNat - hdrJ.lits_len.toNat
                      · have hfit2' : w.toNat ≤ hdr0.lits_cap.toNat - (hdr0.lits_len + w).toNat :=
                          by rwa [hlenJ, hfrJ.lits_cap] at hfit2
                        have hlenJ_cap : hdrJ.lits_len.toNat ≤ hdrJ.lits_cap.toNat := by
                          rw [hlenJ, hl1_eq, hfrJ.lits_cap]; omega
                        rw [ite_eq_left ⟨hoomJ, hlenJ_cap, hfit2⟩]
                        intro mA hmA
                        c0_hstraight; c0_hsplit
                        · exact absurd hoomJ (by c0_bv_omega [hc])
                        · clear hc
                          have hl2_eq :
                              (hdr0.lits_len + w + w).toNat =
                                hdr0.lits_len.toNat + w.toNat + w.toNat := by
                            rw [BitVec.toNat_add, hl1_eq,
                              Nat.mod_eq_of_lt (by have := hdr0.lits_cap.isLt; omega)]
                          rw [hlenJ] at hmA ⊢
                          exact mul_loop_wp
                            (hdrS0 := { hdrJ with lits_len := hdr0.lits_len + w + w })
                            hMark hRel hAdd hIte hoom0 hsla hslb hcap0 hfit1 hfit2' hl1_eq hl2_eq
                            hw_gt1 ha_hi hb_hi hwfa0 hwfb0
                            ⟨by omega, by omega,
                              mul2_opsFrame_with_lits_len hfrJ (hdr0.lits_len + w + w), hextJ,
                              mul2_aigInv_with_lits_len haigJ (hdr0.lits_len + w + w), hoomJ, rfl,
                              hlpJ_len, hpreJ, hwf_outJ, hev_outJ, sep_ac hmA⟩
                            hQ
                      · rw [ite_eq_right (fun ⟨_, _, h3⟩ => hfit2 h3)]
                        dsimp only
                        rw [ite_eq_right (show ¬ hdrJ.oom ≠ 0#32 from fun h => h hoomJ)]
                        intro mA hmA
                        c0_hstraight; c0_hsplit
                        · have hoom_ne : (1#32 : BitVec 32) ≠ 0#32 := by decide
                          clear hc
                          c0_hcall hRel
                          refine ⟨{ hdrJ with oom := 1#32 },
                            array64 hdrJ.aig_ptr awJ ⋆ array (t := i32) hdrJ.ht_ptr htJ ⋆
                            array (t := i32) hdr0.lits_ptr lpJ ⋆ R, sep_ac hmA, fun mO hmO => ?_⟩
                          rw [ite_eq_left (Nat.le_refl _), ← hfrJ.lits_ptr] at hmO
                          c0_hsteps
                          exact mul_oom_close
                            (mul2_opsFrame_with_lits_len
                              (hfrJ.trans (ops_lits_pure_guard_oom hdrJ).2.2.2) hdrJ.lits_len)
                            hextJ
                            (mul2_aigInv_with_lits_len (mul2_aigInv_with_oom haigJ 1#32) _)
                            hlpJ_len (by rw [hlenJ, hl1_eq]; omega)
                            (by rw [hlenJ, hl1_eq, hfrJ.lits_cap]; omega)
                            hpreJ hoom_ne (sep_ac hmO) hQ
                        · exact absurd (show (1#32 : BitVec 32) = 0#32 from by c0_bv_omega [hc])
                            (by decide)
          · rw [ite_eq_right (fun ⟨_, _, h3⟩ => hfit1 h3)]
            dsimp only
            rw [ite_eq_right (show ¬ hdr0.oom ≠ 0#32 from fun h => h hoom0)]
            intro mA hmA
            c0_hstraight; c0_hsplit
            · have hoom_ne : (1#32 : BitVec 32) ≠ 0#32 := by decide
              clear hc; c0_hsteps
              exact mul_oom_close (ops_lits_pure_guard_oom hdr0).2.2.2
                (mul2_aig_le_self g0) (mul2_aigInv_with_oom haig0 1#32) rfl (Nat.le_refl _)
                hlen0_cap (fun _ _ => rfl) hoom_ne (sep_ac hmA) hQ
            · exact absurd (show (1#32 : BitVec 32) = 0#32 from by c0_bv_omega [hc]) (by decide)
        · exact hJ_bad () m
            ⟨Or.inr (Or.inr (by cases hb : sliceOkBool hdr0 bOff w <;> simp_all)), rfl⟩
      · exact hJ_bad () m
          ⟨Or.inr (Or.inl (by cases hb : sliceOkBool hdr0 aOff w <;> simp_all)), rfl⟩

end

end LeanQbe.T.Examples.Bitblast.Proof
