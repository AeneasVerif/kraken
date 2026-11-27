/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Bitblast.Proof.OpsShiftMulSpecs
import LeanQbe.T.Examples.Bitblast.Proof.OpsShiftMul1Helpers
import LeanQbe.T.Examples.Bitblast.Proof.OpsShiftMul1Stages
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.ProofKit
import LeanQbe.T.Logic.MemLemmas

/-!
# Functional Correctness for `bv_blast_shift_var`, `bv_blast_shl`, `bv_blast_ushr`, `bv_blast_ashr`

Canonical `Func.wp` theorems (`<= 200` lines each) for the `4` variable-shift operators of
`OpsShiftMul`, polymorphic in `Γ` via `Env.Has` and in exit continuation `X` (`Spec.XFree`).
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

/-! ## 1. Canonical `Func.wp` Theorems (`OpsShiftMul1`) -/

public section

theorem bv_blast_shift_var_wp (Γ : Env)
    (hSlice : Γ.Has "bv_slice_ok" smBvSliceOkSpec) (hAlloc : Γ.Has "bv_lits_alloc" bvLitsAllocSpec)
    (hMark : Γ.Has "bv_lits_mark" bvLitsMarkSpec) (hRel : Γ.Has "bv_lits_release" bvLitsReleaseSpec)
    (hCopy : Γ.Has "bv_copy_lits" bvCopyLitsSpec) (hOr : Γ.Has "bv_aig_or" bvAigOrSpec)
    (hIte : Γ.Has "bv_aig_ite" bvAigIteSpec) :
    ∀ xs m Q X, bvBlastShiftVarSpec xs m Q X → Func.wp Γ bv_blast_shift_var_body xs m Q X := by
  rintro ⟨h, aOff, w, bOff, nw, op, ⟨⟩⟩ m0 Q X
    ⟨hdr0, g0, aw0, ht0, lp0, R, haig0, hcap0, _hreq, hwf0, hm0, hQ⟩
  change wp Γ Q X (bv_blast_shift_var_body (V := Val) (L := Cont) (h, aOff, w, bOff, nw, op, ())) m0
  rw [bv_blast_shift_var_split_eq]
  dsimp only [svCmp, svLoadOom, svAdd64]
  let opOk : Bool := decide (op = 19#32 ∨ op = 20#32 ∨ op = 21#32)
  c0_hstraight
  refine wp_join0 (fun m1 => m1 = m0 ∧ opOk = true) ?_ ?_
  · intro _ m1 ⟨hm1, hop_t⟩; rw [hm1] at *
    have hop_disj : op = 19#32 ∨ op = 20#32 ∨ op = 21#32 := by simpa [opOk] using hop_t
    c0_hstraight
    refine wp_join0 (fun mb => mb = m0 ∧
      (hdr0.oom ≠ 0#32 ∨ sliceOkBool hdr0 aOff w = false ∨ sliceOkBool hdr0 bOff nw = false)) ?_ ?_
    · intro _ mb ⟨hmb, hbad⟩; rw [hmb] at *; c0_hsteps
      exact shiftVar_bad_close haig0
        (by rcases hbad with h1 | h1 | h1
            · exact Or.inl h1
            · exact Or.inr (Or.inr (Or.inl h1))
            · exact Or.inr (Or.inr (Or.inr h1)))
        (sep_ac hm) hQ
    · intro J_bad hJ_bad
      c0_hstraight; c0_hsplit
      · exact hJ_bad m0 ⟨rfl, Or.inl (by c0_bv_omega [hc])⟩
      have hoom0 : hdr0.oom = 0#32 := by c0_bv_omega [hc]
      clear hc; c0_hstraight
      c0_hcall hSlice; refine ⟨hdr0, array64 hdr0.aig_ptr aw0 ⋆
        array (t := i32) hdr0.ht_ptr ht0 ⋆ array (t := i32) hdr0.lits_ptr lp0 ⋆ R,
        sep_ac hm0, ?_⟩
      c0_hsplit
      · have hsla : sliceOkBool hdr0 aOff w = true := by
          cases hok : sliceOkBool hdr0 aOff w <;> simp_all
        clear hc; c0_hstraight
        c0_hcall hSlice; refine ⟨hdr0, array64 hdr0.aig_ptr aw0 ⋆
          array (t := i32) hdr0.ht_ptr ht0 ⋆ array (t := i32) hdr0.lits_ptr lp0 ⋆ R,
          sep_ac hm0, ?_⟩
        c0_hsplit
        · have hslb : sliceOkBool hdr0 bOff nw = true := by
            cases hok : sliceOkBool hdr0 bOff nw <;> simp_all
          clear hc hJ_bad
          have ⟨hwfa0, hwfb0⟩ := hwf0 hoom0 hop_t hsla hslb
          have hsla' := hsla; rw [sliceOkBool_true_iff] at hsla'
          have hslb' := hslb; rw [sliceOkBool_true_iff] at hslb'
          c0_hstraight
          c0_hcall hAlloc; refine ⟨hdr0, array64 hdr0.aig_ptr aw0 ⋆
            array (t := i32) hdr0.ht_ptr ht0 ⋆ array (t := i32) hdr0.lits_ptr lp0 ⋆ R,
            sep_ac hm0, ?_⟩
          by_cases hfit1 : w.toNat ≤ hdr0.lits_cap.toNat - hdr0.lits_len.toNat
          · rw [ite_eq_left (⟨hoom0, hsla'.1, hfit1⟩ :
                hdr0.oom = 0#32 ∧ hdr0.lits_len.toNat ≤ hdr0.lits_cap.toNat ∧
                w.toNat ≤ hdr0.lits_cap.toNat - hdr0.lits_len.toNat)]
            intro m1 hm1
            have hfr1 := ops_lits_alloc_ok_frame hdr0 w
            have haig1 := shift1_aigInv_with_lits_len haig0 (hdr0.lits_len + w)
            have hl1_eq : (hdr0.lits_len + w).toNat = hdr0.lits_len.toNat + w.toNat := by
              rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by have := hdr0.lits_cap.isLt; omega)]
            c0_hstraight; c0_hsplit
            · exfalso; exact hc hoom0
            · clear hc; c0_hstraight; c0_hsplit
              · have hw0 : w = 0#32 := by c0_bv_omega [hc]
                clear hc; c0_hsteps
                exact shiftVar_ok_close hoom0 hop_t hsla hslb hfr1 (shift1_aig_le_self g0) haig1
                  rfl (by dsimp only; rw [hl1_eq]; omega) (by dsimp only; rw [hl1_eq]; omega) hcap0
                  (by rw [hw0]; simp [hsla'.1]) (fun _ _ => rfl) hoom0 rfl
                  (fun j hj => by rw [hw0] at hj; cases hj)
                  (fun _ _ _ _ _ => BitVec.eq_of_getLsbD_eq fun _ hi => by rw [hw0] at hi; cases hi)
                  (sep_ac hm1) hQ
              · have hw_pos : 0 < w.toNat := by c0_bv_omega [hc]
                clear hc; c0_hstraight
                c0_hcall hCopy
                refine ⟨{ hdr0 with lits_len := hdr0.lits_len + w }, lp0,
                  array64 hdr0.aig_ptr aw0 ⋆ array (t := i32) hdr0.ht_ptr ht0 ⋆ R,
                  by rw [hcap0]; exact hdr0.lits_cap.isLt, by rw [hcap0]; omega,
                  by rw [hcap0]; omega, Or.inr (by omega), sep_ac hm1,
                  fun lp1 m2 hlp1_len hout1 hin1 hm2 => ?_⟩
                c0_hstraight; c0_hsplit
                · have hnw0 : nw = 0#32 := by c0_bv_omega [hc]
                  clear hc; c0_hsteps
                  refine shiftVar_ok_close hoom0 hop_t hsla hslb hfr1 (shift1_aig_le_self g0) haig1
                    hlp1_len (by dsimp only; rw [hl1_eq]; omega)
                    (by dsimp only; rw [hl1_eq]; omega) hcap0 (by omega)
                    (fun q hq => hout1 q (Or.inl hq)) hoom0 rfl
                    (SliceLitsWf.of_agree hin1 hwfa0)
                    (fun ρ va vb hva _ => by
                      have hev : evalPoolSlice g0 ρ lp1 hdr0.lits_len.toNat w.toNat = va := by
                        rw [evalPoolSlice_of_agree hin1]
                        exact evalPoolSlice_eq_of_sliceDenotes (by rw [hcap0]; omega) hva
                      rw [hev]
                      have hnw0_n : nw.toNat = 0 := by rw [hnw0]; decide
                      exact (bvShiftCur_zero op va vb).symm.trans
                        (bvShiftCur_eq_sem_of_no_hi va vb (Nat.zero_le _)
                          (anyOrBool_le _ (by omega))))
                    (sep_ac hm2) hQ
                · have hnw_pos : 0 < nw.toNat := by c0_bv_omega [hc]
                  clear hc
                  have hwfc1 : SliceLitsWf g0 lp1 hdr0.lits_len.toNat w.toNat :=
                    SliceLitsWf.of_agree hin1 hwfa0
                  have hev1 : ∀ (ρ : Nat → Bool) (va : BitVec w.toNat) (vb : BitVec nw.toNat),
                      SliceDenotes g0 ρ (litsSlice lp0 aOff.toNat w.toNat) va →
                      SliceDenotes g0 ρ (litsSlice lp0 bOff.toNat nw.toNat) vb →
                      evalPoolSlice g0 ρ lp1 hdr0.lits_len.toNat w.toNat = bvShiftCur op va vb 0 :=
                    fun ρ va vb hva _ => by
                      rw [evalPoolSlice_of_agree hin1,
                        evalPoolSlice_eq_of_sliceDenotes (by rw [hcap0]; omega) hva,
                        bvShiftCur_zero]
                  c0_hstraight
                  refine wp_join_state (α := Nat × BVHdrState × Aig × List (BitVec 64) ×
                      List (BitVec 32) × List (BitVec 32))
                    (fun st => (BitVec.ofNat 32 st.1, ()))
                    (fun st mS => ShiftStageInv aOff w bOff nw op hdr0 g0 lp0 R st mS h) ?_ ?_
                  · intro _ ⟨p0, hdrS, gS, awS, htS, lpS⟩ mS hstS
                    c0_hstraight
                    exact shiftVar_tail_wp hOr hIte hoom0 hop_t hop_disj hsla hslb hcap0 hfit1
                      hl1_eq hw_pos (by omega) hwfb0 hstS hQ
                  · intro J_fin hJ_fin
                    c0_hstraight; c0_hsplit
                    · have _hw_gt1 : 1 < w.toNat := by c0_bv_omega [hc]
                      clear hc
                      exact shiftVar_phase2_wp hAlloc hMark hRel hCopy hIte hoom0 hop_t hop_disj
                        hsla hslb hcap0 hfit1 hl1_eq hw_pos hnw_pos (by omega) hfr1 haig1 hlp1_len
                        hout1 hwfc1 hev1 hwfb0 (sep_ac hm2) hJ_fin hQ
                    · have hw1 : w.toNat = 1 := by c0_bv_omega [hc]
                      clear hc; c0_hsteps
                      exact hJ_fin (0, { hdr0 with lits_len := hdr0.lits_len + w },
                        g0, aw0, ht0, lp1) m2 ⟨Nat.zero_le _, by decide,
                        fun _ => by rw [hw1, Nat.pow_zero]; exact Nat.le_refl _,
                        hfr1, shift1_aig_le_self g0, haig1, hoom0, rfl, hlp1_len,
                        fun q hq => hout1 q (Or.inl hq), hwfc1, hev1, sep_ac hm2⟩
          · have hcond1 : ¬ (hdr0.oom = 0#32 ∧ hdr0.lits_len.toNat ≤ hdr0.lits_cap.toNat ∧
                w.toNat ≤ hdr0.lits_cap.toNat - hdr0.lits_len.toNat) := fun h => hfit1 h.2.2
            rw [ite_eq_right hcond1]; dsimp only; rw [ite_eq_right (fun h => h hoom0)]
            intro m1 hm1
            c0_hstraight; c0_hsplit
            · clear hc; c0_hsteps
              exact shiftVar_oom_close (ops_lits_pure_guard_oom hdr0).2.2.2
                (shift1_aig_le_self g0) (shift1_aigInv_with_oom haig0 1#32) rfl (Nat.le_refl _)
                hsla'.1 (fun _ _ => rfl) (show (1#32 : BitVec 32) ≠ 0#32 from by decide)
                (sep_ac hm1) hQ
            · exfalso; cases hc
        · exact hJ_bad m0 ⟨rfl, Or.inr (Or.inr
            (by cases hok : sliceOkBool hdr0 bOff nw <;> simp_all))⟩
      · exact hJ_bad m0 ⟨rfl, Or.inr (Or.inl
          (by cases hok : sliceOkBool hdr0 aOff w <;> simp_all))⟩
  · intro J_badOp hJ_badOp
    c0_hstraight; c0_hsplit
    · c0_hstraight; c0_hsplit
      · c0_hstraight; c0_hsplit
        · c0_hsteps
          refine shiftVar_bad_close haig0 (Or.inr (Or.inl ?_)) (sep_ac hm) hQ
          simp only [decide_eq_false_iff_not, not_or]
          exact ⟨by c0_bv_omega [hc], by c0_bv_omega [hc_1], by c0_bv_omega [hc_2]⟩
        · exact hJ_badOp m0 ⟨rfl, by simp [opOk, (by c0_bv_omega [hc] : op = 21#32)]⟩
      · exact hJ_badOp m0 ⟨rfl, by simp [opOk, (by c0_bv_omega [hc] : op = 20#32)]⟩
    · exact hJ_badOp m0 ⟨rfl, by simp [opOk, (by c0_bv_omega [hc] : op = 19#32)]⟩

theorem bv_blast_shl_wp (Γ : Env) (hSV : Γ.Has "bv_blast_shift_var" bvBlastShiftVarSpec) :
    ∀ xs m Q X, bvBlastShlSpec xs m Q X → Func.wp Γ bv_blast_shl_body xs m Q X := by
  rintro ⟨h, aOff, w, bOff, nw, ⟨⟩⟩ m0 Q X
    ⟨hdr0, g0, aw0, ht0, lp0, R, haig0, hcap0, _hreq, hwf0, hm0, hQ⟩
  c0_hstraight; c0_hcall hSV
  refine ⟨hdr0, g0, aw0, ht0, lp0, R, haig0, hcap0, (fun hf => absurd hf Bool.false_ne_true),
    fun hoom _ ha hb => hwf0 hoom rfl ha hb, hm0, fun ret hdr' g' aw' ht' lp' m' hfr hext haig'
      hlp hl1 hl2 hpre hfail hoom hr hm' => ?_⟩
  c0_hsteps
  exact shiftVar_wrap_close (by decide) (fun _ _ => by simp [bvShiftSem]) hfr hext haig' hlp hl1
    hl2 hpre hfail hoom hr hm' hQ

theorem bv_blast_ushr_wp (Γ : Env) (hSV : Γ.Has "bv_blast_shift_var" bvBlastShiftVarSpec) :
    ∀ xs m Q X, bvBlastUshrSpec xs m Q X → Func.wp Γ bv_blast_ushr_body xs m Q X := by
  rintro ⟨h, aOff, w, bOff, nw, ⟨⟩⟩ m0 Q X
    ⟨hdr0, g0, aw0, ht0, lp0, R, haig0, hcap0, _hreq, hwf0, hm0, hQ⟩
  c0_hstraight; c0_hcall hSV
  refine ⟨hdr0, g0, aw0, ht0, lp0, R, haig0, hcap0, (fun hf => absurd hf Bool.false_ne_true),
    fun hoom _ ha hb => hwf0 hoom rfl ha hb, hm0, fun ret hdr' g' aw' ht' lp' m' hfr hext haig'
      hlp hl1 hl2 hpre hfail hoom hr hm' => ?_⟩
  c0_hsteps
  exact shiftVar_wrap_close (by decide) (fun _ _ => by simp [bvShiftSem]) hfr hext haig' hlp hl1
    hl2 hpre hfail hoom hr hm' hQ

theorem bv_blast_ashr_wp (Γ : Env) (hSV : Γ.Has "bv_blast_shift_var" bvBlastShiftVarSpec) :
    ∀ xs m Q X, bvBlastAshrSpec xs m Q X → Func.wp Γ bv_blast_ashr_body xs m Q X := by
  rintro ⟨h, aOff, w, bOff, nw, ⟨⟩⟩ m0 Q X
    ⟨hdr0, g0, aw0, ht0, lp0, R, haig0, hcap0, _hreq, hwf0, hm0, hQ⟩
  c0_hstraight; c0_hcall hSV
  refine ⟨hdr0, g0, aw0, ht0, lp0, R, haig0, hcap0, (fun hf => absurd hf Bool.false_ne_true),
    fun hoom _ ha hb => hwf0 hoom rfl ha hb, hm0, fun ret hdr' g' aw' ht' lp' m' hfr hext haig'
      hlp hl1 hl2 hpre hfail hoom hr hm' => ?_⟩
  c0_hsteps
  exact shiftVar_wrap_close (by decide) (fun _ _ => by simp [bvShiftSem]) hfr hext haig' hlp hl1
    hl2 hpre hfail hoom hr hm' hQ

end

end LeanQbe.T.Examples.Bitblast.Proof
