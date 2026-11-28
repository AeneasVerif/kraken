/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Congruence.Inv
public import LeanQbe.T.Examples.Kissat.Proof.Clause.Spec
public import LeanQbe.T.Examples.Kissat.Src.Congruence

/-!
# Congruence Core WP Proofs (`find`, `merge`, `mark_trail`, `unit_fold`, `equiv_fold`)

Canonical `Func.wp` proofs for functions #1–#5 of `Src.Congruence`:
1. `full_cong_find` (`Spec.fullCongFindSpec`)
2. `full_cong_merge` (`Spec.fullCongMergeSpec`)
3. `full_cong_mark_trail` (`Spec.fullCongMarkTrailSpec`)
4. `full_cong_unit_fold` (`Spec.fullCongUnitFoldSpec`)
5. `full_cong_equiv_fold` (`Spec.fullCongEquivFoldSpec`)
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Congruence

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Congruence
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Clause.Spec
open LeanQbe.T.Examples.Kissat.Proof.Congruence.Spec
open Kraken.Bedrock2.Test

open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Proof.Congruence.CongTactics

local macro "cong_split" : tactic =>
  `(tactic| (
    c0_hsteps_nogrp
    repeat (
      refine LeanQbe.T.wp_unroll_group fun _ _ => ?_
      c0_hsteps_nogrp)
    c0_hsplit))

public section

/-! ## 1. `full_cong_find_wp` (`Spec.fullCongFindSpec`) -/

private theorem congRoot_step {repr : List (BitVec 32)} {f x : Nat}
    (hne : (repr[x]?.getD 0#32).toNat ≠ x) :
    congRoot repr (f + 1) x = congRoot repr f (repr[x]?.getD 0#32).toNat := by
  simp [congRoot, hne]

private theorem congRoot_set_gt {repr : List (BitVec 32)} {nlits p r : Nat}
    (hwf : FullCongReprWf nlits repr) :
    ∀ {f x : Nat}, x < nlits → x < p →
      congRoot (repr.set p (BitVec.ofNat 32 r)) f x = congRoot repr f x := by
  intro f; induction f with
  | zero => intro _ _ _; rfl
  | succ f ih =>
    intro x hx hxp
    have hgt : (repr.set p (BitVec.ofNat 32 r))[x]?.getD 0#32 = repr[x]?.getD 0#32 := by
      rw [List.getElem?_set_ne (by omega)]
    simp only [congRoot, hgt]
    split
    · rfl
    · have hle := hwf.2 x hx
      exact ih (by omega) (by omega)

/-- Canonical `Func.wp` proof for `full_cong_find`. -/
theorem full_cong_find_wp (Γ : Env) :
    ∀ args m Q X, Spec.fullCongFindSpec args m Q X →
      Func.wp Γ full_cong_find_body args m Q X := by
  rintro ⟨repr_p, l, ⟨⟩⟩ m0 Q X ⟨F_cur, nlits, repr0, R, hinv0, hl_lt, hm0, hQ⟩
  unfold Func.wp full_cong_find_body
  have hlen0 : nlits ≤ repr0.length := hinv0.1.1
  let root := congRoot repr0 (nlits + 1) l.toNat
  c0_hsteps_nogrp
  refine wp_loop_inv (ts := [i32])
    (fun (r, ()) mr => mr = m0 ∧ r.toNat < nlits ∧
      congRoot repr0 (r.toNat + 1) r.toNat = root ∧
      LitEquiv (cnfOfClauses F_cur) l.toNat r.toNat)
    (fun (r, ()) _ => r.toNat)
    (fun J hJ => by
      c0_hsteps!
      have hrt : congRoot repr0 (l.toNat + 1) l.toNat = root :=
        congRoot_fuel_ge hinv0.1 hl_lt (by omega) (by omega)
      exact hJ (l, ()) m0 ⟨rfl, hl_lt, hrt, LitEquiv.refl _ _⟩)
    (fun J (r, ()) mr ⟨hmr, hr_lt, hrt_r, heqv_r⟩ ihr => by
      subst mr
      have hr_arr : (r.setWidth 64).toNat < repr0.length := by rw [bv_zext32_toNat]; omega
      c0_hsplit
      · have hp_ne : repr0[r.toNat]?.getD 0#32 ≠ r := by
          rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; exact hc
        let nxt := repr0[r.toNat]'(by omega)
        have hnxt_eq : nxt = repr0[r.toNat]?.getD 0#32 := by
          rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
        have hnxt_le := hinv0.1.2 r.toNat hr_lt
        have hnxt_ne : nxt.toNat ≠ r.toNat := fun he => hp_ne (by
          rw [← hnxt_eq]; exact BitVec.eq_of_toNat_eq he)
        have hnxt_lt : nxt.toNat < r.toNat := by rw [← hnxt_eq] at hnxt_le; omega
        have hrt_n : congRoot repr0 (nxt.toNat + 1) nxt.toNat = root := by
          have h1 := congRoot_step (repr := repr0) (f := r.toNat)
            (fun h => hnxt_ne (hnxt_eq ▸ h))
          rw [hrt_r, ← hnxt_eq] at h1
          exact (congRoot_fuel_ge hinv0.1 (by omega) (by omega) (by omega)).trans h1.symm
        have heqv_n : LitEquiv (cnfOfClauses F_cur) l.toNat nxt.toNat :=
          heqv_r.trans (by rw [hnxt_eq]; exact hinv0.2 r.toNat hr_lt)
        c0_hsteps!
        exact ihr (nxt, ()) m0 (by dsimp only; omega) ⟨rfl, by omega, hrt_n, heqv_n⟩
      · have hfix : (repr0[r.toNat]?.getD 0#32).toNat = r.toNat := by
          rw [List.getElem?_eq_getElem (by omega), Option.getD_some, hc]
        have hr_eq_root : r.toNat = root := by rw [← hrt_r, congRoot_eq_of_fixed hfix]
        have hr_le_l : r.toNat ≤ l.toNat := by rw [hr_eq_root]; exact congRoot_le hinv0.1 hl_lt
        c0_hsteps!
        refine wp_loop_inv (ts := [i32])
          (fun (p, ()) mp => ∃ repr_k : List (BitVec 32),
            repr_k.length = repr0.length ∧ p.toNat < nlits ∧
            FullCongReprInv F_cur nlits repr_k ∧
            (repr_k[r.toNat]?.getD 0#32).toNat = r.toNat ∧
            congRoot repr_k (nlits + 1) p.toNat = r.toNat ∧
            (array (t := i32) repr_p repr_k ⋆ R) mp)
          (fun (p, ()) _ => p.toNat)
          (fun J2 hJ2 => by
            c0_hsteps!
            exact hJ2 (l, ()) m0 ⟨repr0, rfl, hl_lt, hinv0, hfix, hr_eq_root ▸ rfl, hm0⟩)
          (fun J2 (p, ()) mp ⟨repr_k, hlen_k, hp_lt, hinv_k, hfix_r, hrt_p, hmp⟩ ih2 => by
            clear hc; c0_hsplit
            · have hp_ne_r : p.toNat ≠ r.toNat := fun he => hc (by
                have hget : repr_k[p.toNat]'(by omega) = repr_k[r.toNat]?.getD 0#32 := by
                  rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; simp [he]
                rw [hget]; exact BitVec.eq_of_toNat_eq hfix_r)
              have hp_arr : (p.setWidth 64).toNat < repr_k.length := by
                rw [bv_zext32_toNat]; omega
              let nxt := repr_k[(p.setWidth 64).toNat]'hp_arr
              have hnxt_eq : nxt = repr_k[p.toNat]?.getD 0#32 := by
                dsimp only [nxt]
                rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                exact list_getElem_congr (bv_zext32_toNat p) hp_arr (by omega)
              have hnxt_ne_p : nxt.toNat ≠ p.toNat := fun he => by
                have hfix_p : (repr_k[p.toNat]?.getD 0#32).toNat = p.toNat := by
                  rw [← hnxt_eq, he]
                rw [congRoot_eq_of_fixed hfix_p] at hrt_p
                exact hp_ne_r hrt_p
              have hnxt_le := hinv_k.1.2 p.toNat hp_lt
              have hnxt_lt : nxt.toNat < p.toNat := by rw [← hnxt_eq] at hnxt_le; omega
              c0_hsteps!
              let repr_k' := repr_k.set p.toNat r
              have hmp' : (array (t := i32) repr_p repr_k' ⋆ R) m := by
                dsimp only [repr_k']; rwa [bv_zext32_toNat] at hm
              have hinv_k' : FullCongReprInv F_cur nlits repr_k' := by
                refine ⟨⟨by simp [repr_k', hlen_k, hlen0], fun x hx => ?_⟩, fun x hx => ?_⟩
                · by_cases hxp : x = p.toNat
                  · subst hxp; rw [List.getElem?_set_self (by omega), Option.getD_some]
                    rw [← hrt_p]; exact congRoot_le hinv_k.1 hp_lt
                  · rw [List.getElem?_set_ne (Ne.symm hxp)]; exact hinv_k.1.2 x hx
                · by_cases hxp : x = p.toNat
                  · subst hxp; rw [List.getElem?_set_self (by omega), Option.getD_some]
                    exact (congRoot_litEquiv hinv_k hp_lt).trans (by
                      rw [hrt_p]; exact LitEquiv.refl _ _)
                  · rw [List.getElem?_set_ne (Ne.symm hxp)]; exact hinv_k.2 x hx
              have hfix_r' : (repr_k'[r.toNat]?.getD 0#32).toNat = r.toNat := by
                dsimp only [repr_k']; rw [List.getElem?_set_ne hp_ne_r]; exact hfix_r
              have hrt_n' : congRoot repr_k' (nlits + 1) nxt.toNat = r.toNat := by
                have hr_eq_of : BitVec.ofNat 32 r.toNat = r :=
                  BitVec.eq_of_toNat_eq (bv32_ofNat_toNat_lt r.isLt)
                rw [show repr_k' = repr_k.set p.toNat (BitVec.ofNat 32 r.toNat) from by
                  simp [repr_k', hr_eq_of]]
                rw [congRoot_set_gt hinv_k.1 (by omega) hnxt_lt]
                have hst := congRoot_step (repr := repr_k) (f := nlits)
                  (fun h => hnxt_ne_p (hnxt_eq ▸ h))
                rw [hrt_p, ← hnxt_eq] at hst
                exact (congRoot_fuel_ge hinv_k.1 (by omega) (by omega) (by omega)).trans hst.symm
              exact ih2 (nxt, ()) m (by dsimp only; omega)
                ⟨repr_k', by simp [repr_k', hlen_k], by omega, hinv_k', hfix_r', hrt_n', hmp'⟩
            · c0_hsteps!
              exact hQ r repr_k mp hlen_k hinv_k hr_le_l hr_lt heqv_r hmp))

/-! ## 2. `full_cong_merge_wp` (`Spec.fullCongMergeSpec`) -/

/-- Canonical `Func.wp` proof for `full_cong_merge`. -/
theorem full_cong_merge_wp (Γ : Env)
    (hFind : Γ.Has "full_cong_find" Spec.fullCongFindSpec)
    (hAddBin : Γ.Has "full_add_bin" fullAddBinSpec) :
    ∀ args m Q X, Spec.fullCongMergeSpec args m Q X →
      Func.wp Γ full_cong_merge_body args m Q X := by
  rintro ⟨h, a, b, ⟨⟩⟩ m0 Q X
    ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hmk, hnd, hext, hcl0, hdm, hrepr, ha, hb, heqv, hm0, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx; have hcv_le := hlen.core_ok.cur_vars_le
  have hrl := hlen.core_ok.repr_len
  unfold Func.wp full_cong_merge_body
  c0_hsteps!; c0_call hFind
  refine ⟨F_cur, 2 * s.core.cur_vars, s.core.repr, ArrayField.repr.rest c s ⋆ R, hrepr, ha,
    focus_full_repr hm0, fun ra repr1 m1 hrl1 hrepr1 _ hra_lt ha_ra hm1 => ?_⟩
  let s1 : FullState := { s with core := { s.core with repr := repr1 } }
  have hlen1 : s1.LengthsOk c := ⟨{ hlen.core_ok with repr_len := by simp [s1, hrl1, hrl] },
    hlen.scratch_ok⟩
  have hw1 : FullWitnessInv c F0 F_cur s1.core := fullWitnessInv_with_repr hw repr1
  have hm1' : (FullMem c s1 ⋆ R) m1 := unfocus_full_repr hm1
  c0_hsteps!; c0_call hFind
  refine ⟨F_cur, 2 * s.core.cur_vars, repr1, ArrayField.repr.rest c s1 ⋆ R, hrepr1, hb,
    focus_full_repr hm1', fun rb repr2 m2 hrl2 hrepr2 _ hrb_lt hb_rb hm2 => ?_⟩
  let s2 : FullState := { s1 with core := { s1.core with repr := repr2 } }
  have hlen2 : s2.LengthsOk c := ⟨{ hlen1.core_ok with repr_len := by simp [s2, hrl2, hrl1, hrl] },
    hlen.scratch_ok⟩
  have hw2 : FullWitnessInv c F0 F_cur s2.core := fullWitnessInv_with_repr hw1 repr2
  have hm2' : (FullMem c s2 ⋆ R) m2 := unfocus_full_repr hm2
  have hrab_eqv : LitEquiv (cnfOfClauses F_cur) ra.toNat rb.toNat :=
    ha_ra.symm.trans (heqv.trans hb_rb)
  c0_hsplit
  · c0_hsteps!
    exact hQ false s2 m2 hlen2 hw2 hmk hnd hext hcl0 hdm rfl rfl rfl rfl rfl rfl hrepr2 hm2'
  · have hne_eq := hc; clear hc; c0_hsplit
    · have heq_neg : ra = rb ^^^ 1#32 := by grind
      have hunsat : (cnfOfClauses F_cur).Unsat := by
        have hneg : LitEquiv (cnfOfClauses F_cur) rb.toNat (litNeg rb.toNat) := by
          rw [← bv32_xor1_eq_litNeg rb, ← heq_neg]; exact hrab_eqv.symm
        exact unsat_of_litEquiv_neg hneg
      c0_hsteps!
      let s3 : FullState := { s2 with core := { s2.core with inconsistent := 1#64 } }
      have hlen3 : s3.LengthsOk c := ⟨{ hlen2.core_ok with vals_len := hlen2.core_ok.vals_len },
        hlen2.scratch_ok⟩
      have hw3 : FullWitnessInv c F0 F_cur s3.core :=
        fullWitnessInv_with_inconsistent hw2 1#64 (fun _ => hunsat)
      exact hQ true s3 m hlen3 hw3 hmk hnd hext hcl0 hdm rfl rfl rfl rfl rfl rfl hrepr2 hm
    · have hne_neg := hc; clear hc; c0_hsteps_nogrp
      refine wp_join_group (ts := [i32, i32])
        (fun (ra', rb', ()) mj =>
          mj = m2 ∧ ra'.toNat < rb'.toNat ∧ rb'.toNat < 2 * s.core.cur_vars ∧
          ra' ≠ rb' ^^^ 1#32 ∧ LitEquiv (cnfOfClauses F_cur) ra'.toNat rb'.toNat)
        ?_ ?_
      · rintro _ ⟨ra', rb', ⟨⟩⟩ mj ⟨rfl, hlt_ab, hrb'_lt, hne_n', heqv'⟩
        have hra'_lt : ra'.toNat < 2 * s.core.cur_vars := by omega
        have hdiv := bv32_lt_and_ne_xor1_div_lt hlt_ab hne_n'
        have hnrb_lt : (rb' ^^^ 1#32).toNat < 2 * s.core.cur_vars := by
          rw [bv32_xor1_eq_litNeg]; exact bv32_xor1_lt_even hrb'_lt
        have hnra_lt : (ra' ^^^ 1#32).toNat < 2 * s.core.cur_vars := by
          rw [bv32_xor1_eq_litNeg]; exact bv32_xor1_lt_even hra'_lt
        have hrb_arr : rb'.toNat < s2.core.repr.length := by
          have := hlen2.core_ok.repr_len; omega
        have hnrb_arr : (rb' ^^^ 1#32).toNat < s2.core.repr.length := by
          have := hlen2.core_ok.repr_len; omega
        have hrb_z : (rb'.setWidth 64).toNat < s2.core.repr.length := by
          rw [bv_zext32_toNat]; exact hrb_arr
        have hnrb_z : ((rb' ^^^ 1).setWidth 64).toNat <
            (s2.core.repr.set (rb'.setWidth 64).toNat ra').length := by
          rw [List.length_set, bv_zext32_toNat]; exact hnrb_arr
        c0_hsteps!
        let repr3 := (repr2.set rb'.toNat ra').set (rb' ^^^ 1#32).toNat (ra' ^^^ 1#32)
        let s3 : FullState := { s2 with core := { s2.core with repr := repr3 } }
        have hlen3 : s3.LengthsOk c :=
          ⟨{ hlen2.core_ok with repr_len := by simpa [s3, repr3] using hlen2.core_ok.repr_len },
           hlen2.scratch_ok⟩
        have hw3 : FullWitnessInv c F0 F_cur s3.core := fullWitnessInv_with_repr hw2 repr3
        have hrepr3 : FullCongReprInv F_cur (2 * s.core.cur_vars) repr3 := by
          have hlen3_r : repr3.length = repr2.length := by simp [repr3]
          refine ⟨⟨by omega, fun x hx => ?_⟩, fun x hx => ?_⟩
          · by_cases hx1 : x = (rb' ^^^ 1#32).toNat
            · subst hx1; dsimp only [repr3]
              rw [List.getElem?_set_self (by simpa using hnrb_arr), Option.getD_some]; omega
            · dsimp only [repr3]; rw [List.getElem?_set_ne (Ne.symm hx1)]
              by_cases hx2 : x = rb'.toNat
              · subst hx2; rw [List.getElem?_set_self hrb_arr, Option.getD_some]; omega
              · rw [List.getElem?_set_ne (Ne.symm hx2)]; exact hrepr2.1.2 x hx
          · by_cases hx1 : x = (rb' ^^^ 1#32).toNat
            · subst hx1; dsimp only [repr3]
              rw [List.getElem?_set_self (by simpa using hnrb_arr), Option.getD_some,
                bv32_xor1_eq_litNeg, bv32_xor1_eq_litNeg]
              exact heqv'.symm.neg
            · dsimp only [repr3]; rw [List.getElem?_set_ne (Ne.symm hx1)]
              by_cases hx2 : x = rb'.toNat
              · subst hx2; rw [List.getElem?_set_self hrb_arr, Option.getD_some]; exact heqv'.symm
              · rw [List.getElem?_set_ne (Ne.symm hx2)]; exact hrepr2.2 x hx
        have hm3 : (FullMem c s3 ⋆ R) m := by
          rw [bv_zext32_toNat, bv_zext32_toNat] at hm; exact hm
        c0_call hAddBin
        refine ⟨c, F0, F_cur, s3, R, rfl, hlen3, hw3, hcl0,
          fun _ _ => by rw [bv32_xor1_litNeg]; exact heqv'.1, hm3, ?_⟩
        intro r1 vals1 flags1 lvl1 rsns1 trl1 tp1 te1 unass1 unfl1 wvec1 wstk1 wlen1 wu1 nb1
          oom1 inc1 ph1 ws1 m4 s4 hlen4 hw4 _ hr1_20 _ hm4
        have hmk4 : FullLitMarksClear c s4 := fullLitMarksClear_of_eq hmk rfl rfl
        have hnd4 : FullArenaVarsNodup s4 := fullArenaVarsNodup_of_eq hnd rfl rfl
        have hext4 : FullExtScratchOk c s4 := fullExtScratchOk_of_eq hext rfl rfl rfl rfl
        c0_hsplit
        · have hunsat4 : (cnfOfClauses F_cur).Unsat := hw4.inconsistent_sound (hr1_20 hc).2
          c0_hsteps!
          let s5 : FullState := { s4 with core := { s4.core with inconsistent := 1#64 } }
          have hlen5 : s5.LengthsOk c := ⟨{ hlen4.core_ok with vals_len := hlen4.core_ok.vals_len },
            hlen4.scratch_ok⟩
          have hw5 : FullWitnessInv c F0 F_cur s5.core :=
            fullWitnessInv_with_inconsistent hw4 1#64 (fun _ => hunsat4)
          exact hQ true s5 m hlen5 hw5 hmk4 hnd4 hext4 hcl0 hdm rfl rfl rfl rfl rfl rfl hrepr3 hm
        · clear hc; c0_hsteps_nogrp
          refine wp_join_group (ts := [])
            (fun () mj => ∃ s5 : FullState,
              s5.LengthsOk c ∧ FullWitnessInv c F0 F_cur s5.core ∧
              FullLitMarksClear c s5 ∧ FullArenaVarsNodup s5 ∧ FullExtScratchOk c s5 ∧
              s5.core.cur_level = 0 ∧ s5.core.dense_mode ≠ 0#64 ∧
              s5.core.cur_vars = s.core.cur_vars ∧ s5.core.fuel = s.core.fuel ∧
              s5.core.arena = s.core.arena ∧ s5.core.arena_len = s.core.arena_len ∧
              s5.core.tmp = s.core.tmp ∧ s5.scratch.scratch_buf = s.scratch.scratch_buf ∧
              FullCongReprInv F_cur (2 * s5.core.cur_vars) s5.core.repr ∧
              (FullMem c s5 ⋆ R) mj)
            ?_ ?_
          · rintro _ ⟨⟩ mj
              ⟨s5, hlen5, hw5, hmk5, hnd5, hext5, hcl5, hdm5, hcv5, hfl5, har5, hal5, htmp5,
               hscr5, hrepr5, hmj⟩
            c0_hsteps!
            let s6 : FullState :=
              { s5 with scratch := { s5.scratch with cong_cnt := s5.scratch.cong_cnt + 1#64 } }
            have hlen6 : s6.LengthsOk c := ⟨hlen5.core_ok,
              { hlen5.scratch_ok with walk_vals_len := hlen5.scratch_ok.walk_vals_len }⟩
            exact hQ true s6 m hlen6 hw5 hmk5 hnd5 hext5 hcl5 hdm5 hcv5 hfl5 har5 hal5 htmp5 hscr5
              hrepr5 hm
          · intro Jst hJst; c0_hsplit
            · c0_hsteps!
              let s5 : FullState := { s4 with
                core := { s4.core with oom := 0#64 },
                scratch := { s4.scratch with ant_sz := 1#64 } }
              have hlen5 : s5.LengthsOk c :=
                ⟨{ hlen4.core_ok with vals_len := hlen4.core_ok.vals_len },
                 { hlen4.scratch_ok with walk_vals_len := hlen4.scratch_ok.walk_vals_len }⟩
              have hw5 := fullWitnessInv_with_oom hw4 0#64
              exact hJst () m ⟨s5, hlen5, hw5, hmk4, hnd4, hext4, hcl0, hdm, rfl, rfl, rfl, rfl,
                rfl, rfl, hrepr3, hm⟩
            · clear hc; c0_hsteps!; c0_call hAddBin
              refine ⟨c, F0, F_cur, s4, R, rfl, hlen4, hw4, hcl0,
                fun _ _ => by rw [bv32_xor1_litNeg]; exact heqv'.2, hm4, ?_⟩
              intro r2 vals2 flags2 lvl2 rsns2 trl2 tp2 te2 unass2 unfl2 wvec2 wstk2 wlen2 wu2 nb2
                oom2 inc2 ph2 ws2 m5 s5 hlen5 hw5 _ hr2_20 _ hm5
              have hmk5 : FullLitMarksClear c s5 := fullLitMarksClear_of_eq hmk4 rfl rfl
              have hnd5 : FullArenaVarsNodup s5 := fullArenaVarsNodup_of_eq hnd4 rfl rfl
              have hext5 : FullExtScratchOk c s5 := fullExtScratchOk_of_eq hext4 rfl rfl rfl rfl
              c0_hsplit
              · have hunsat5 : (cnfOfClauses F_cur).Unsat := hw5.inconsistent_sound (hr2_20 hc).2
                c0_hsteps!
                let s6 : FullState := { s5 with core := { s5.core with inconsistent := 1#64 } }
                have hlen6 : s6.LengthsOk c :=
                  ⟨{ hlen5.core_ok with vals_len := hlen5.core_ok.vals_len }, hlen5.scratch_ok⟩
                have hw6 : FullWitnessInv c F0 F_cur s6.core :=
                  fullWitnessInv_with_inconsistent hw5 1#64 (fun _ => hunsat5)
                exact hQ true s6 m hlen6 hw6 hmk5 hnd5 hext5 hcl0 hdm rfl rfl rfl rfl rfl rfl
                  hrepr3 hm
              · clear hc; cong_split
                · c0_hsteps!
                  let s6 : FullState := { s5 with
                    core := { s5.core with oom := 0#64 },
                    scratch := { s5.scratch with ant_sz := 1#64 } }
                  have hlen6 : s6.LengthsOk c :=
                    ⟨{ hlen5.core_ok with vals_len := hlen5.core_ok.vals_len },
                     { hlen5.scratch_ok with walk_vals_len := hlen5.scratch_ok.walk_vals_len }⟩
                  have hw6 := fullWitnessInv_with_oom hw5 0#64
                  exact hJst () m ⟨s6, hlen6, hw6, hmk5, hnd5, hext5, hcl0, hdm, rfl, rfl, rfl, rfl,
                    rfl, rfl, hrepr3, hm⟩
                · c0_hsteps!
                  exact hJst () m5 ⟨s5, hlen5, hw5, hmk5, hnd5, hext5, hcl0, hdm, rfl, rfl, rfl,
                    rfl, rfl, rfl, hrepr3, hm5⟩
      · intro J hJ; c0_hsteps!
        · exact hJ (rb, ra, ()) m2 ⟨rfl, by c0_bound, hra_lt, bv32_xor1_symm hne_neg, hrab_eqv.symm⟩
        · have hne_n : ra.toNat ≠ rb.toNat := fun h => hne_eq (BitVec.eq_of_toNat_eq h)
          exact hJ (ra, rb, ()) m2 ⟨rfl, by c0_bound, hrb_lt, hne_neg, hrab_eqv⟩

/-! ## 3. `full_cong_mark_trail_wp` (`Spec.fullCongMarkTrailSpec`) -/

/-- Canonical `Func.wp` proof for `full_cong_mark_trail`. -/
theorem full_cong_mark_trail_wp (Γ : Env)
    (hFind : Γ.Has "full_cong_find" Spec.fullCongFindSpec) :
    ∀ args m Q X, Spec.fullCongMarkTrailSpec args m Q X →
      Func.wp Γ full_cong_mark_trail_body args m Q X := by
  rintro ⟨h, prev_te, ep, ⟨⟩⟩ m0 Q X ⟨c, F_cur, s, R, rfl, hlen, hrepr0, hm0, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv_le := hlen.core_ok.cur_vars_le
  have hte_le := hlen.core_ok.trail_end_le
  have htrll := hlen.core_ok.trl_len
  have hrl0 := hlen.core_ok.repr_len
  have htmkl0 := hlen.scratch_ok.tarjan_mark_len
  unfold Func.wp full_cong_mark_trail_body
  c0_hsteps_nogrp
  refine wp_loop_inv (ts := [i64])
    (fun (i, ()) mi => ∃ repr_i tmk_i : List (BitVec 32),
      let si : FullState :=
        { s with
          core := { s.core with repr := repr_i },
          scratch := { s.scratch with tarjan_mark := tmk_i } }
      repr_i.length = 2 * c.max_vars ∧ tmk_i.length = 2 * c.max_vars ∧
      FullCongReprInv F_cur (2 * s.core.cur_vars) repr_i ∧
      (FullMem c si ⋆ R) mi)
    (fun (i, ()) _ => s.core.trail_end - i.toNat)
    (fun J hJ => by
      c0_hsteps!
      exact hJ (prev_te, ()) m0 ⟨s.core.repr, s.scratch.tarjan_mark, hrl0, htmkl0, hrepr0, hm0⟩)
    (fun J (i, ()) mi ⟨repr_i, tmk_i, hrli, htmkli, hrepri, hmi⟩ ih => by
      let si : FullState :=
        { s with
          core := { s.core with repr := repr_i },
          scratch := { s.scratch with tarjan_mark := tmk_i } }
      c0_hsplit
      · have hi_lt : i.toNat < s.core.trail_end := by have := hc; omega
        have hi_trl : i.toNat < si.core.trl.length := by dsimp [si]; omega
        let lit := si.core.trl[i.toNat]'hi_trl
        have hi1 : (i + 1#64).toNat = i.toNat + 1 := by bv_omega
        have h_shr1 (x : BitVec 32) : (BitVec.setWidth 64 (x >>> 1#32)).toNat =
            x.toNat / 2 := by
          simp [Nat.shiftRight_eq_div_pow]; omega
        clear hc; cong_split
        · have hlv_lt : lit.toNat / 2 < s.core.cur_vars := by
            have := hc; dsimp only [lit, si] at *; omega
          have hlit_lt : lit.toNat < 2 * s.core.cur_vars := by omega
          have hlv_arr :
              (BitVec.setWidth 64 (si.core.trl[i.toNat]'hi_trl >>> 1#32)).toNat <
                si.scratch.tarjan_mark.length := by
            rw [h_shr1]; dsimp [si]; omega
          c0_hsteps!
          let tmk_1 := tmk_i.set (lit.toNat / 2) ep
          let si1 : FullState :=
            { s with
              core := { s.core with repr := repr_i },
              scratch := { s.scratch with tarjan_mark := tmk_1 } }
          have htmkl1 : tmk_1.length = 2 * c.max_vars := by simp [tmk_1, htmkli]
          have hmod64 (x : BitVec 32) : x.toNat % 2 ^ 64 = x.toNat :=
            Nat.mod_eq_of_lt (Nat.lt_trans (BitVec.isLt x) (by decide))
          have hm1 : (FullMem c si1 ⋆ R) m := by
            dsimp only [si1, tmk_1]
            let idx_trl := (s.core.trl[i.toNat]'hi_trl).toNat / 2
            change (FullMem c {
                core := { s.core with repr := repr_i },
                scratch := { s.scratch with tarjan_mark := tmk_i.set idx_trl ep } } ⋆ R) m
            simpa [Nat.shiftRight_eq_div_pow, hmod64] using hm
          c0_call hFind
          refine ⟨F_cur, 2 * s.core.cur_vars, repr_i, ArrayField.repr.rest c si1 ⋆ R,
            hrepri, hlit_lt, focus_full_repr hm1,
            fun r repr' m2 hrli' hrepri' _ hr_lt _ hm2 => ?_⟩
          let si2 : FullState :=
            { s with
              core := { s.core with repr := repr' },
              scratch := { s.scratch with tarjan_mark := tmk_1 } }
          have hm2' : (FullMem c si2 ⋆ R) m2 := unfocus_full_repr hm2
          have hrv_arr : (BitVec.setWidth 64 (r >>> 1#32)).toNat <
              si2.scratch.tarjan_mark.length := by
            rw [h_shr1]; dsimp [si2]; have := hlen.core_ok.cur_vars_le; omega
          have hrv_lt : r.toNat / 2 < s.core.cur_vars := by omega
          clear hc; cong_split
          c0_hsteps!
          let tmk_2 := tmk_1.set (r.toNat / 2) ep
          have hm3 : (FullMem c { s with
              core := { s.core with repr := repr' },
              scratch := { s.scratch with tarjan_mark := tmk_2 } } ⋆ R) m := by
            dsimp only [tmk_2]
            simpa [Nat.shiftRight_eq_div_pow, hmod64] using hm
          exact ih (i + 1#64, ()) m (by dsimp only; omega)
            ⟨repr', tmk_2, by omega, by simp [tmk_2, htmkl1], hrepri', hm3⟩
        · c0_hsteps!
          exact ih (i + 1#64, ()) mi (by dsimp only; omega)
            ⟨repr_i, tmk_i, hrli, htmkli, hrepri, hmi⟩
      · c0_hsteps!
        exact hQ repr_i tmk_i mi
          ⟨{ hlen.core_ok with repr_len := hrli },
            { hlen.scratch_ok with tarjan_mark_len := htmkli }⟩
          hrepri hmi)

/-! ## 4. `full_cong_unit_fold_wp` (`Spec.fullCongUnitFoldSpec`) -/

/-- Canonical `Func.wp` proof for `full_cong_unit_fold`. -/
theorem full_cong_unit_fold_wp (Γ : Env)
    (hAddUnit : Γ.Has "full_add_unit" fullAddUnitSpec)
    (hMark : Γ.Has "full_cong_mark_trail" Spec.fullCongMarkTrailSpec) :
    ∀ args m Q X, Spec.fullCongUnitFoldSpec args m Q X →
      Func.wp Γ full_cong_unit_fold_body args m Q X := by
  rintro ⟨h, lit, next_ep, ⟨⟩⟩ m0 Q X
    ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hmk, hnd, hext, hcl0, hdm, hrepr, hlit_lt, hent, hm0, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv_le := hlen.core_ok.cur_vars_le
  have hvl := hlen.core_ok.vals_len
  have hlit_vals : (lit.setWidth 64).toNat < s.core.vals.length := by
    rw [bv_zext32_toNat]; omega
  unfold Func.wp full_cong_unit_fold_body
  c0_hsplit
  · c0_hsteps!
    exact hQ 0#64 s m0 hlen hw hmk hnd hext hcl0 hdm rfl rfl rfl rfl rfl rfl hrepr
      (Or.inl rfl) (fun h => by cases h) hm0
  · clear hc; c0_hsteps!; c0_call hAddUnit
    refine ⟨c, F0, F_cur, s, R, rfl, hlen, hw, fun _ => hent, hm0, ?_⟩
    intro ok3 vals3 flags3 lvl3 rsns3 trl3 tp3 te3 prop3 cl3 unass3 unfl3 inc3
      ph3 ta3 ba3 pt3 pb3 hp3 ps3 hl3 qsi3 qss3 m3 s3 hlen3 hw3 hcl3 hu_ok _ hm3
    obtain ⟨hmk3, hnd3, hext3, _, hdm3⟩ := fullAddUnitSpec_fullDenseInvW (s' := s3)
      hmk hnd hext hdm hcl3 rfl rfl rfl rfl rfl rfl rfl
    c0_hsplit
    · clear hc; c0_hsteps!
      let s3c : FullState :=
        { s3 with scratch := { s3.scratch with cong_cnt := s3.scratch.cong_cnt + 1#64 } }
      have hlen3c : s3c.LengthsOk c := ⟨hlen3.core_ok, { hlen3.scratch_ok with }⟩
      have hext3c : FullExtScratchOk c s3c := fullExtScratchOk_of_eq hext3 rfl rfl rfl rfl
      c0_call hMark
      refine ⟨c, F_cur, s3c, R, rfl, hlen3c, hrepr, hm, fun repr4 tmk4 m4 hlen4 hrepr4 hm4 => ?_⟩
      let s4 : FullState :=
        { s3c with core := { s3c.core with repr := repr4 },
                   scratch := { s3c.scratch with tarjan_mark := tmk4 } }
      have hw4 : FullWitnessInv c F0 F_cur s4.core := fullWitnessInv_with_repr hw3 repr4
      cong_split
      · have huns4 : F0.Unsat :=
          unsat_of_inconsistent_w hw4 (show s4.core.inconsistent ≠ 0#64 from hc)
        c0_hsteps!
        exact hQ 2#64 s4 m4 hlen4 hw4 (fullLitMarksClear_of_eq hmk3 rfl rfl)
          (fullArenaVarsNodup_of_eq hnd3 rfl rfl) (fullExtScratchOk_of_eq hext3c rfl rfl rfl rfl)
          hcl3 hdm3 rfl rfl rfl rfl rfl rfl hrepr4 (Or.inr (Or.inr rfl))
          (fun _ => ⟨hc, huns4⟩) hm4
      · c0_hsteps!
        exact hQ 1#64 s4 m4 hlen4 hw4 (fullLitMarksClear_of_eq hmk3 rfl rfl)
          (fullArenaVarsNodup_of_eq hnd3 rfl rfl) (fullExtScratchOk_of_eq hext3c rfl rfl rfl rfl)
          hcl3 hdm3 rfl rfl rfl rfl rfl rfl hrepr4 (Or.inr (Or.inl rfl))
          (fun h => by cases h) hm4
    · obtain ⟨huns3, hinc3⟩ := hu_ok hlit_lt hc
      clear hc; c0_hsteps!; c0_call hMark
      refine ⟨c, F_cur, s3, R, rfl, hlen3, hrepr, hm3, fun repr4 tmk4 m4 hlen4 hrepr4 hm4 => ?_⟩
      let s4 : FullState :=
        { s3 with core := { s3.core with repr := repr4 },
                  scratch := { s3.scratch with tarjan_mark := tmk4 } }
      c0_hsteps!
      exact hQ 2#64 s4 m4 hlen4 (fullWitnessInv_with_repr hw3 repr4)
        (fullLitMarksClear_of_eq hmk3 rfl rfl) (fullArenaVarsNodup_of_eq hnd3 rfl rfl)
        (fullExtScratchOk_of_eq hext3 rfl rfl rfl rfl) hcl3 hdm3 rfl rfl rfl rfl rfl rfl hrepr4
        (Or.inr (Or.inr rfl)) (fun _ => ⟨hinc3, huns3⟩) hm4

/-! ## 5. `full_cong_equiv_fold_wp` (`Spec.fullCongEquivFoldSpec`) -/

private theorem ef_evalLitVal_litNeg (α : Nat → Bool) (l : Nat) :
    evalLitVal α (litNeg l) = !evalLitVal α l := by
  have h1 : ∀ k, (1 : Nat).testBit (k + 1) = false := fun k => by
    simp only [Nat.testBit, Nat.shiftRight_eq_div_pow]
    have hp : 2 ≤ 2 ^ (k + 1) :=
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by decide) (by omega)
    simp [Nat.div_eq_of_lt (by omega : 1 < 2 ^ (k + 1))]
  have hdiv : (l ^^^ 1) / 2 = l / 2 := by
    apply Nat.eq_of_testBit_eq; intro k
    rw [Nat.testBit_div_two, Nat.testBit_div_two, Nat.testBit_xor, h1, Bool.xor_false]
  have hmod : (l ^^^ 1) % 2 = 1 - l % 2 := by
    have h0 : (l ^^^ 1).testBit 0 = !l.testBit 0 := by
      rw [Nat.testBit_xor, show Nat.testBit 1 0 = true from rfl, Bool.xor_true]
    simp only [Nat.testBit_zero] at h0
    rcases Nat.mod_two_eq_zero_or_one l with hm | hm <;>
      rcases Nat.mod_two_eq_zero_or_one (l ^^^ 1) with hn | hn <;> simp_all
  unfold evalLitVal litNeg litVar litSign; rw [hdiv, hmod]
  cases α (l / 2) <;> rcases Nat.mod_two_eq_zero_or_one l with hm | hm <;> simp [hm]

private theorem ef_litEquiv_eval {f : CNF Nat} {a b : Nat}
    (heqv : LitEquiv f a b) {α : Nat → Bool} (hα : f.Sat α) :
    evalLitVal α a = evalLitVal α b := by
  have hc1 := (CNF.entails_clause_def.mp heqv.1) α hα
  have hc2 := (CNF.entails_clause_def.mp heqv.2) α hα
  rw [← clauseEvalVal_iff] at hc1 hc2
  unfold clauseEvalVal at hc1 hc2
  rw [List.any_eq_true] at hc1 hc2
  obtain ⟨x, hx, hxt⟩ := hc1
  obtain ⟨y, hy, hyt⟩ := hc2
  have hx' : x = litNeg a ∨ x = b := by simpa using hx
  have hy' : y = a ∨ y = litNeg b := by simpa using hy
  rcases hx' with hxa | hxb <;> rcases hy' with hya | hyb
  · rw [hxa, ef_evalLitVal_litNeg] at hxt; rw [hya] at hyt
    cases ha : evalLitVal α a <;> simp_all
  · rw [hxa, ef_evalLitVal_litNeg] at hxt; rw [hyb, ef_evalLitVal_litNeg] at hyt
    cases ha : evalLitVal α a <;> cases hb : evalLitVal α b <;> simp_all
  · rw [hxb] at hxt; rw [hya] at hyt
    cases ha : evalLitVal α a <;> cases hb : evalLitVal α b <;> simp_all
  · rw [hxb] at hxt; rw [hyb, ef_evalLitVal_litNeg] at hyt
    cases hb : evalLitVal α b <;> simp_all

private theorem ef_litEquiv_of_eval {f : CNF Nat} {a b : Nat}
    (h : ∀ α : Nat → Bool, f.Sat α → evalLitVal α a = evalLitVal α b) :
    LitEquiv f a b := by
  constructor <;> rw [CNF.entails_clause_def] <;> intro α hα <;>
    rw [← clauseEvalVal_iff] <;> unfold clauseEvalVal <;> rw [List.any_eq_true]
  · cases hb : evalLitVal α b
    · exact ⟨litNeg a, by simp, by rw [ef_evalLitVal_litNeg, h α hα, hb]; rfl⟩
    · exact ⟨b, by simp, hb⟩
  · cases ha : evalLitVal α a
    · exact ⟨litNeg b, by simp, by rw [ef_evalLitVal_litNeg, ← h α hα, ha]; rfl⟩
    · exact ⟨a, by simp, ha⟩

private theorem ef_litEquiv_chain {f : CNF Nat} {a b c d : Nat}
    (ha : LitEquiv f a c) (hab : LitEquiv f a b) (hb : LitEquiv f b d) :
    LitEquiv f c d :=
  ef_litEquiv_of_eval fun α hα => by
    rw [← ef_litEquiv_eval ha hα, ef_litEquiv_eval hab hα, ef_litEquiv_eval hb hα]

private theorem ef_unit_entails {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (hcl : k.cur_level = 0)
    {r other : BitVec 32} (hr_lt : r.toNat < 2 * k.cur_vars)
    (heqv : LitEquiv (cnfOfClauses F_cur) r.toNat other.toNat)
    (hne0 : k.vals[r.toNat]?.getD 0#8 ≠ 0#8) :
    let ul := if (0#32 : BitVec 32).slt (BitVec.signExtend 32 (k.vals[r.toNat]?.getD 0#8))
      then other else other ^^^ 1#32
    (cnfOfClauses F_cur).EntailsClause (cnfClause [ul.toNat]) := by
  intro ul
  have hv_dom := hw.vals_domain r.toNat hr_lt
  rcases hv_dom with h0 | h1 | hff
  · exact absurd h0 hne0
  · have hpos : (0#32 : BitVec 32).slt ((1#8 : BitVec 8).signExtend 32) = true := by decide
    have hul : ul = other := by dsimp only [ul]; rw [h1, hpos]; rfl
    rw [hul, CNF.entails_clause_def]; intro α hα
    have hvals := (CNF.entails_clause_def.mp (vals1_entails hw hcl hr_lt h1)) α hα
    rw [← clauseEvalVal_iff] at hvals ⊢
    unfold clauseEvalVal at hvals ⊢
    rw [List.any_eq_true] at hvals ⊢
    obtain ⟨x, hx, hxt⟩ := hvals
    have hx' : x = r.toNat := by simpa using hx
    subst hx'
    exact ⟨other.toNat, by simp, by rwa [← ef_litEquiv_eval heqv hα]⟩
  · have hneg : (0#32 : BitVec 32).slt ((0xFF#8 : BitVec 8).signExtend 32) = false := by decide
    have hul : ul = other ^^^ 1#32 := by dsimp only [ul]; rw [hff, hneg]; rfl
    rw [hul, bv32_xor1_eq_litNeg, CNF.entails_clause_def]; intro α hα
    have hvals := (CNF.entails_clause_def.mp (valsff_entails_neg hw hcl hr_lt hff)) α hα
    rw [← clauseEvalVal_iff] at hvals ⊢
    unfold clauseEvalVal at hvals ⊢
    rw [List.any_eq_true] at hvals ⊢
    obtain ⟨x, hx, hxt⟩ := hvals
    have hx' : x = litNeg r.toNat := by simpa using hx
    subst hx'
    rw [ef_evalLitVal_litNeg] at hxt
    exact ⟨litNeg other.toNat, by simp, by
      rw [ef_evalLitVal_litNeg, ← ef_litEquiv_eval heqv hα]; exact hxt⟩

private abbrev EfRetInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s0 s : FullState) : Prop :=
  s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
  FullLitMarksClear c s ∧ FullArenaVarsNodup s ∧ FullExtScratchOk c s ∧
  s.core.cur_level = 0 ∧ s.core.dense_mode ≠ 0#64 ∧
  s.core.cur_vars = s0.core.cur_vars ∧ s.core.fuel = s0.core.fuel ∧
  s.core.arena = s0.core.arena ∧ s.core.arena_len = s0.core.arena_len ∧
  s.core.tmp = s0.core.tmp ∧ s.scratch.scratch_buf = s0.scratch.scratch_buf ∧
  FullCongReprInv F_cur (2 * s.core.cur_vars) s.core.repr

private theorem ef_ret_inv_of_add_unit {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 s s' : FullState} (hinv : EfRetInv c F0 F_cur s0 s) (hlen' : s'.LengthsOk c)
    (hw' : FullWitnessInv c F0 F_cur s'.core) (hcl' : s'.core.cur_level = 0)
    (hcv' : s'.core.cur_vars = s.core.cur_vars) (hfl' : s'.core.fuel = s.core.fuel)
    (hmrk' : s'.core.mrk = s.core.mrk) (hlm' : s'.core.lit_mark = s.core.lit_mark)
    (har' : s'.core.arena = s.core.arena) (hal' : s'.core.arena_len = s.core.arena_len)
    (htmp' : s'.core.tmp = s.core.tmp) (hrepr' : s'.core.repr = s.core.repr)
    (hdm' : s'.core.dense_mode = s.core.dense_mode)
    (hll' : s'.scratch.last_learned = s.scratch.last_learned)
    (hext' : s'.scratch.extend_len = s.scratch.extend_len)
    (hsb' : s'.scratch.scratch_buf = s.scratch.scratch_buf) :
    EfRetInv c F0 F_cur s0 s' := by
  obtain ⟨_, _, hmk, hnd, hext, _, hdm, hcv, hfl, har, hal, htmp, hsb, hrepr⟩ := hinv
  obtain ⟨hmk', hnd', hext', _, hdm'⟩ := fullAddUnitSpec_fullDenseInvW
    hmk hnd hext hdm hcl' hmrk' hlm' har' hal' hll' hext' hdm'
  exact ⟨hlen', hw', hmk', hnd', hext', hcl', hdm', hcv'.trans hcv, hfl'.trans hfl,
    har'.trans har, hal'.trans hal, htmp'.trans htmp, hsb'.trans hsb,
    by rw [hcv', hrepr']; exact hrepr⟩

private theorem ef_ret_inv_with_cong_cnt {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 s : FullState} (hinv : EfRetInv c F0 F_cur s0 s) (cnt : BitVec 64) :
    EfRetInv c F0 F_cur s0 { s with scratch := { s.scratch with cong_cnt := cnt } } := by
  obtain ⟨hlen, hw, hmk, hnd, hext, hcl, hdm, hcv, hfl, har, hal, htmp, hsb, hrepr⟩ := hinv
  exact ⟨⟨hlen.core_ok, { hlen.scratch_ok with }⟩, hw, fullLitMarksClear_of_eq hmk rfl rfl,
    fullArenaVarsNodup_of_eq hnd rfl rfl, fullExtScratchOk_of_eq hext rfl rfl rfl rfl,
    hcl, hdm, hcv, hfl, har, hal, htmp, hsb, hrepr⟩

private theorem ef_ret_inv_with_tmk {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 s : FullState} (hinv : EfRetInv c F0 F_cur s0 s) {tmk' : List (BitVec 32)}
    (htl : tmk'.length = 2 * c.max_vars) :
    EfRetInv c F0 F_cur s0 { s with scratch := { s.scratch with tarjan_mark := tmk' } } := by
  obtain ⟨hlen, hw, hmk, hnd, hext, hcl, hdm, hcv, hfl, har, hal, htmp, hsb, hrepr⟩ := hinv
  exact ⟨⟨hlen.core_ok, { hlen.scratch_ok with tarjan_mark_len := htl }⟩, hw,
    fullLitMarksClear_of_eq hmk rfl rfl, fullArenaVarsNodup_of_eq hnd rfl rfl,
    fullExtScratchOk_of_eq hext rfl rfl rfl rfl, hcl, hdm, hcv, hfl, har, hal, htmp, hsb, hrepr⟩

private theorem ef_ret_inv_with_repr_tmk {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 s : FullState} (hinv : EfRetInv c F0 F_cur s0 s) {repr' tmk' : List (BitVec 32)}
    (hrc_len : repr'.length = 2 * c.max_vars)
    (htl : tmk'.length = 2 * c.max_vars)
    (hrepr' : FullCongReprInv F_cur (2 * s.core.cur_vars) repr') :
    EfRetInv c F0 F_cur s0
      { core := { s.core with repr := repr' }
        scratch := { s.scratch with tarjan_mark := tmk' } } := by
  obtain ⟨hlen, hw, hmk, hnd, hext, hcl, hdm, hcv, hfl, har, hal, htmp, hsb, _⟩ := hinv
  exact ⟨⟨{ hlen.core_ok with repr_len := hrc_len },
    { hlen.scratch_ok with tarjan_mark_len := htl }⟩,
    fullWitnessInv_with_repr hw repr', fullLitMarksClear_of_eq hmk rfl rfl,
    fullArenaVarsNodup_of_eq hnd rfl rfl, fullExtScratchOk_of_eq hext rfl rfl rfl rfl,
    hcl, hdm, hcv, hfl, har, hal, htmp, hsb, hrepr'⟩

private theorem ef_shl_zext_idx (x : BitVec 32) :
    (BitVec.setWidth 64 (x >>> (1 : BitVec 32))).toNat = x.toNat / 2 := by
  simp [Nat.shiftRight_eq_div_pow]; omega

/-- Canonical `Func.wp` proof for `full_cong_equiv_fold`. -/
theorem full_cong_equiv_fold_wp (Γ : Env)
    (hFind : Γ.Has "full_cong_find" Spec.fullCongFindSpec)
    (hMerge : Γ.Has "full_cong_merge" Spec.fullCongMergeSpec)
    (hAddUnit : Γ.Has "full_add_unit" fullAddUnitSpec)
    (hMark : Γ.Has "full_cong_mark_trail" Spec.fullCongMarkTrailSpec) :
    ∀ args m Q X, Spec.fullCongEquivFoldSpec args m Q X →
      Func.wp Γ full_cong_equiv_fold_body args m Q X := by
  rintro ⟨h, a, b, next_ep, ⟨⟩⟩ m0 Q X
    ⟨c, F0, F_cur, s, R, rfl, hlen0, hw0, hmk0, hnd0, hext0, hcl0, hdm0, hrepr0,
      ha_lt, hb_lt, heqv_ab, hm0, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv_le := hlen0.core_ok.cur_vars_le
  have hvals_len := hlen0.core_ok.vals_len
  unfold Func.wp full_cong_equiv_fold_body
  c0_hsteps!
  c0_call hFind
  refine ⟨F_cur, 2 * s.core.cur_vars, s.core.repr, ArrayField.repr.rest c s ⋆ R,
    hrepr0, ha_lt, focus_full_repr hm0,
    fun ra repr1 m1 hrl1 hrepr1 hle_ra hra_lt heqv_a hm1 => ?_⟩
  let s1 : FullState := { s with core := { s.core with repr := repr1 } }
  have hm1' : (FullMem c s1 ⋆ R) m1 := unfocus_full_repr hm1
  have hlen1 : s1.LengthsOk c :=
    ⟨{ hlen0.core_ok with repr_len := hrl1.trans hlen0.core_ok.repr_len }, hlen0.scratch_ok⟩
  c0_call hFind
  refine ⟨F_cur, 2 * s1.core.cur_vars, s1.core.repr, ArrayField.repr.rest c s1 ⋆ R,
    hrepr1, hb_lt, focus_full_repr hm1',
    fun rb repr2 m2 hrl2 hrepr2 hle_rb hrb_lt heqv_b hm2 => ?_⟩
  let s2 : FullState := { s with core := { s.core with repr := repr2 } }
  have hm2' : (FullMem c s2 ⋆ R) m2 := unfocus_full_repr hm2
  have hlen2 : s2.LengthsOk c :=
    ⟨{ hlen0.core_ok with repr_len := hrl2.trans (hrl1.trans hlen0.core_ok.repr_len) },
      hlen0.scratch_ok⟩
  have hw2 : FullWitnessInv c F0 F_cur s2.core := fullWitnessInv_with_repr hw0 repr2
  have hinv2 : EfRetInv c F0 F_cur s s2 :=
    ⟨hlen2, hw2, fullLitMarksClear_of_eq hmk0 rfl rfl, fullArenaVarsNodup_of_eq hnd0 rfl rfl,
      fullExtScratchOk_of_eq hext0 rfl rfl rfl rfl, hcl0, hdm0, rfl, rfl, rfl, rfl, rfl, rfl,
      hrepr2⟩
  have heqv_rarb : LitEquiv (cnfOfClauses F_cur) ra.toNat rb.toNat :=
    ef_litEquiv_chain heqv_a heqv_ab heqv_b
  have heqv_rbra : LitEquiv (cnfOfClauses F_cur) rb.toNat ra.toNat :=
    ef_litEquiv_of_eval fun α hα => (ef_litEquiv_eval heqv_rarb hα).symm
  have hra_vals : (ra.setWidth 64).toNat < s2.core.vals.length := by
    rw [bv_zext32_toNat]; change ra.toNat < s.core.vals.length; omega
  have hrb_vals : (rb.setWidth 64).toNat < s2.core.vals.length := by
    rw [bv_zext32_toNat]; change rb.toNat < s.core.vals.length; omega
  c0_hsteps_nogrp
  refine LeanQbe.T.wp_join_group (ts := [.bool])
    (fun (_ch, ()) mc => ∃ sc : FullState,
      EfRetInv c F0 F_cur s sc ∧ (FullMem c sc ⋆ R) mc) ?_ ?_
  · rintro _ ⟨ch0, ⟨⟩⟩ mc ⟨sc, hinv_c, hmc⟩
    c0_hsteps_nogrp
    refine LeanQbe.T.wp_join_group (ts := [.bool])
      (fun (_ch, ()) md => ∃ sd : FullState,
        EfRetInv c F0 F_cur s sd ∧ (FullMem c sd ⋆ R) md) ?_ ?_
    · rintro _ ⟨ch1, ⟨⟩⟩ md ⟨sd, hinv_d, hmd⟩
      c0_hsteps_nogrp
      refine LeanQbe.T.wp_join_group (ts := [])
        (fun () me => ∃ se : FullState,
          EfRetInv c F0 F_cur s se ∧ (FullMem c se ⋆ R) me) ?_ ?_
      · rintro _ ⟨⟩ me ⟨se, hinv_e, hme⟩
        obtain ⟨hlene, hwe, hmke, hnde, hexte, hcle, hdme, hcve, hfle, hare, hale, htmpe, hsbe,
          hrepre⟩ := hinv_e
        cong_split
        · have huns : F0.Unsat := unsat_of_inconsistent_w hwe hc
          c0_hsteps!
          exact hQ 2#64 se me hlene hwe hmke hnde hexte hcle hdme hcve hfle hare hale htmpe hsbe
            hrepre (Or.inr (Or.inr rfl)) (fun _ => huns) hme
        · clear hc; cong_split
          · c0_hsteps!
            exact hQ 1#64 se me hlene hwe hmke hnde hexte hcle hdme hcve hfle hare hale htmpe hsbe
              hrepre (Or.inr (Or.inl rfl)) (fun h => by cases h) hme
          · c0_hsteps!
            exact hQ 0#64 se me hlene hwe hmke hnde hexte hcle hdme hcve hfle hare hale htmpe hsbe
              hrepre (Or.inl rfl) (fun h => by cases h) hme
      · intro Jt hJt
        have ⟨hlend, _, _, _, _, _, _, _, _, _, _, _, _, hreprd⟩ := hinv_d
        cong_split
        · clear hc; c0_hsteps!; c0_call hMark
          refine ⟨c, F_cur, sd, R, rfl, hlend, hreprd, hmd,
            fun repr' tmk' m' hlen' hrepr' hm' => ?_⟩
          let se : FullState :=
            { core := { sd.core with repr := repr' }
              scratch := { sd.scratch with tarjan_mark := tmk' } }
          c0_hsteps!
          exact hJt () m' ⟨se,
            ef_ret_inv_with_repr_tmk hinv_d hlen'.core_ok.repr_len hlen'.scratch_ok.tarjan_mark_len
              hrepr', hm'⟩
        · c0_hsteps!; exact hJt () md ⟨sd, hinv_d, hmd⟩
    · intro Jm hJm
      obtain ⟨hlenc, hwc, hmkc, hndc, hextc, hclc, hdmc, hcvc, hflc, harc, halc, htmpc, hsbc,
        hreprc⟩ := hinv_c
      c0_hsteps!; c0_call hMerge
      refine ⟨c, F0, F_cur, sc, R, rfl, hlenc, hwc, hmkc, hndc, hextc, hclc, hdmc, hreprc,
        by omega, by omega, heqv_rarb, hmc,
        fun ch_m sm mm hlenm hwm hmkm hndm hextm hclm hdmm hcvm hflm harm halm htmpm hsbm
          hreprm hmm => ?_⟩
      have hinvm : EfRetInv c F0 F_cur s sm :=
        ⟨hlenm, hwm, hmkm, hndm, hextm, hclm, hdmm, hcvm.trans hcvc, hflm.trans hflc,
          harc ▸ harm, halc ▸ halm, htmpc ▸ htmpm, hsbc ▸ hsbm, hreprm⟩
      have htmk_rb :
          (BitVec.setWidth 64 (rb >>> (1 : BitVec 32))).toNat < sm.scratch.tarjan_mark.length := by
        rw [ef_shl_zext_idx]; have := hlenm.scratch_ok.tarjan_mark_len; omega
      have htmk_ra :
          (BitVec.setWidth 64 (ra >>> (1 : BitVec 32))).toNat < sm.scratch.tarjan_mark.length := by
        rw [ef_shl_zext_idx]; have := hlenm.scratch_ok.tarjan_mark_len; omega
      have htmk_b :
          (BitVec.setWidth 64 (b >>> (1 : BitVec 32))).toNat < sm.scratch.tarjan_mark.length := by
        rw [ef_shl_zext_idx]; have := hlenm.scratch_ok.tarjan_mark_len; omega
      have htmk_a :
          (BitVec.setWidth 64 (a >>> (1 : BitVec 32))).toNat < sm.scratch.tarjan_mark.length := by
        rw [ef_shl_zext_idx]; have := hlenm.scratch_ok.tarjan_mark_len; omega
      have htmk_ab :
          (BitVec.setWidth 64 (b >>> (1 : BitVec 32))).toNat <
            (sm.scratch.tarjan_mark.set
              (BitVec.setWidth 64 (a >>> (1 : BitVec 32))).toNat next_ep).length := by
        simp only [List.length_set, hlenm.scratch_ok.tarjan_mark_len]
        rw [ef_shl_zext_idx]; omega
      have htmk_abra :
          (BitVec.setWidth 64 (ra >>> (1 : BitVec 32))).toNat <
            ((sm.scratch.tarjan_mark.set
              (BitVec.setWidth 64 (a >>> (1 : BitVec 32))).toNat next_ep).set
                (BitVec.setWidth 64 (b >>> (1 : BitVec 32))).toNat next_ep).length := by
        simp only [List.length_set, hlenm.scratch_ok.tarjan_mark_len]
        rw [ef_shl_zext_idx]; omega
      have htmk_abrarb :
          (BitVec.setWidth 64 (rb >>> (1 : BitVec 32))).toNat <
            (((sm.scratch.tarjan_mark.set
              (BitVec.setWidth 64 (a >>> (1 : BitVec 32))).toNat next_ep).set
                (BitVec.setWidth 64 (b >>> (1 : BitVec 32))).toNat next_ep).set
                  (BitVec.setWidth 64 (ra >>> (1 : BitVec 32))).toNat next_ep).length := by
        simp only [List.length_set, hlenm.scratch_ok.tarjan_mark_len]
        rw [ef_shl_zext_idx]; omega
      cong_split
      · clear hc
        have htl_final :
            ((((sm.scratch.tarjan_mark.set
              (BitVec.setWidth 64 (a >>> (1 : BitVec 32))).toNat next_ep).set
                (BitVec.setWidth 64 (b >>> (1 : BitVec 32))).toNat next_ep).set
                  (BitVec.setWidth 64 (ra >>> (1 : BitVec 32))).toNat next_ep).set
                    (BitVec.setWidth 64 (rb >>> (1 : BitVec 32))).toNat next_ep).length =
              2 * c.max_vars := by
          simp only [List.length_set, hlenm.scratch_ok.tarjan_mark_len]
        c0_hsteps!
        exact hJm (true, ()) m ⟨_, ef_ret_inv_with_tmk hinvm htl_final, hm⟩
      · c0_hsteps!; exact hJm (ch0, ()) mm ⟨sm, hinvm, hmm⟩
  · intro Jc hJc
    c0_hsplit
    · have hva_ne0 : s2.core.vals[ra.toNat]?.getD 0#8 ≠ 0#8 := by
        intro h0; revert hc
        have hr_g : s2.core.vals[ra.toNat]'(by change ra.toNat < s.core.vals.length; omega) =
            0#8 := by
          rw [List.getElem?_eq_getElem (by change ra.toNat < s.core.vals.length; omega),
            Option.getD_some] at h0
          exact h0
        try rw [list_getElem_congr (bv_zext32_toNat ra) hra_vals _]
        rw [hr_g]; decide
      c0_hsteps_nogrp
      refine LeanQbe.T.wp_join_group (ts := [i32])
        (fun (ul, ()) mu => mu = m2 ∧ ul.toNat < 2 * s2.core.cur_vars ∧
          (cnfOfClauses F_cur).EntailsClause (cnfClause [ul.toNat])) ?_ ?_
      · rintro _ ⟨ul, ⟨⟩⟩ mu ⟨hmu, hul_lt, hent_ul⟩
        subst mu
        have hul_vals : (ul.setWidth 64).toNat < s2.core.vals.length := by
          rw [bv_zext32_toNat]; change ul.toNat < s.core.vals.length; omega
        cong_split
        · clear hc; c0_hsteps!; c0_call hAddUnit
          refine ⟨c, F0, F_cur, s2, R, rfl, hlen2, hw2, fun _ => hent_ul, hm2', ?_⟩
          intro ok3 _ _ _ _ _ _ _ _ _ _ _ inc3 _ _ _ _ _ _ _ _ _ _ m3 s3 hlen3 hw3 hcl3 hu_ok _ hm3
          have hinv3 := ef_ret_inv_of_add_unit hinv2 hlen3 hw3 hcl3 rfl rfl rfl rfl rfl rfl rfl rfl
            rfl rfl rfl rfl
          cong_split
          · clear hc; c0_hsteps!
            exact hJc (true, ()) m ⟨_, ef_ret_inv_with_cong_cnt hinv3 _, hm⟩
          · obtain ⟨huns3, _⟩ := hu_ok hul_lt hc
            clear hc; c0_hsteps!; c0_call hMark
            refine ⟨c, F_cur, s3, R, rfl, hlen3, hrepr2, hm3,
              fun repr4 tmk4 m4 hlen4 hrepr4 hm4 => ?_⟩
            let s4 : FullState :=
              { core := { s3.core with repr := repr4 }
                scratch := { s3.scratch with tarjan_mark := tmk4 } }
            have hinv4 := ef_ret_inv_with_repr_tmk hinv3 hlen4.core_ok.repr_len
              hlen4.scratch_ok.tarjan_mark_len hrepr4
            c0_hsteps!
            exact hQ 2#64 s4 m4 hlen4 hinv4.2.1 hinv4.2.2.1 hinv4.2.2.2.1 hinv4.2.2.2.2.1
              hinv4.2.2.2.2.2.1 hinv4.2.2.2.2.2.2.1 hinv4.2.2.2.2.2.2.2.1 hinv4.2.2.2.2.2.2.2.2.1
              hinv4.2.2.2.2.2.2.2.2.2.1 hinv4.2.2.2.2.2.2.2.2.2.2.1 hinv4.2.2.2.2.2.2.2.2.2.2.2.1
              hinv4.2.2.2.2.2.2.2.2.2.2.2.2.1 hinv4.2.2.2.2.2.2.2.2.2.2.2.2.2 (Or.inr (Or.inr rfl))
              (fun _ => huns3) hm4
        · c0_hsteps!; exact hJc (false, ()) m2 ⟨s2, hinv2, hm2'⟩
      · intro Ju hJu
        have hent := ef_unit_entails hw2 hcl0 hra_lt heqv_rarb hva_ne0
        cong_split
        · have hlt : rb.toNat < 2 * s2.core.cur_vars := hrb_lt
          have hpos : (0#32 : BitVec 32).slt
              (BitVec.signExtend 32 (s2.core.vals[ra.toNat]?.getD 0#8)) = true := by
            rw [List.getElem?_eq_getElem (by change ra.toNat < s.core.vals.length; omega),
              Option.getD_some]
            try rw [list_getElem_congr (bv_zext32_toNat ra) hra_vals _] at hc
            simpa using hc
          c0_hsteps!; exact hJu (rb, ()) m2 ⟨rfl, hlt, by simpa [hpos] using hent⟩
        · have hlt : (rb ^^^ 1#32).toNat < 2 * s2.core.cur_vars := by
            rw [bv32_xor1_eq_litNeg]; exact litNeg_lt_two_mul hrb_lt
          have hneg : (0#32 : BitVec 32).slt
              (BitVec.signExtend 32 (s2.core.vals[ra.toNat]?.getD 0#8)) = false := by
            rw [List.getElem?_eq_getElem (by change ra.toNat < s.core.vals.length; omega),
              Option.getD_some]
            try rw [list_getElem_congr (bv_zext32_toNat ra) hra_vals _] at hc
            simpa using hc
          c0_hsteps!; exact hJu (rb ^^^ 1#32, ()) m2 ⟨rfl, hlt, by simpa [hneg] using hent⟩
    · clear hc; c0_hsteps_nogrp
      refine LeanQbe.T.wp_unroll_group fun _ _ => ?_
      c0_hsplit
      · have hvb_ne0 : s2.core.vals[rb.toNat]?.getD 0#8 ≠ 0#8 := by
          intro h0; revert hc
          have hr_g : s2.core.vals[rb.toNat]'(by change rb.toNat < s.core.vals.length; omega) =
              0#8 := by
            rw [List.getElem?_eq_getElem (by change rb.toNat < s.core.vals.length; omega),
              Option.getD_some] at h0
            exact h0
          try rw [list_getElem_congr (bv_zext32_toNat rb) hrb_vals _]
          rw [hr_g]; decide
        c0_hsteps_nogrp
        refine LeanQbe.T.wp_join_group (ts := [i32])
          (fun (ul, ()) mu => mu = m2 ∧ ul.toNat < 2 * s2.core.cur_vars ∧
            (cnfOfClauses F_cur).EntailsClause (cnfClause [ul.toNat])) ?_ ?_
        · rintro _ ⟨ul, ⟨⟩⟩ mu ⟨hmu, hul_lt, hent_ul⟩
          subst mu
          have hul_vals : (ul.setWidth 64).toNat < s2.core.vals.length := by
            rw [bv_zext32_toNat]; change ul.toNat < s.core.vals.length; omega
          cong_split
          · clear hc; c0_hsteps!; c0_call hAddUnit
            refine ⟨c, F0, F_cur, s2, R, rfl, hlen2, hw2, fun _ => hent_ul, hm2', ?_⟩
            intro ok3 _ _ _ _ _ _ _ _ _ _ _ inc3 _ _ _ _ _ _ _ _ _ _ m3 s3 hlen3 hw3 hcl3 hu_ok _
              hm3
            have hinv3 := ef_ret_inv_of_add_unit hinv2 hlen3 hw3 hcl3 rfl rfl rfl rfl rfl rfl rfl
              rfl rfl rfl rfl rfl
            cong_split
            · clear hc; c0_hsteps!
              exact hJc (true, ()) m ⟨_, ef_ret_inv_with_cong_cnt hinv3 _, hm⟩
            · obtain ⟨huns3, _⟩ := hu_ok hul_lt hc
              clear hc; c0_hsteps!; c0_call hMark
              refine ⟨c, F_cur, s3, R, rfl, hlen3, hrepr2, hm3,
                fun repr4 tmk4 m4 hlen4 hrepr4 hm4 => ?_⟩
              let s4 : FullState :=
                { core := { s3.core with repr := repr4 }
                  scratch := { s3.scratch with tarjan_mark := tmk4 } }
              have hinv4 := ef_ret_inv_with_repr_tmk hinv3 hlen4.core_ok.repr_len
                hlen4.scratch_ok.tarjan_mark_len hrepr4
              c0_hsteps!
              exact hQ 2#64 s4 m4 hlen4 hinv4.2.1 hinv4.2.2.1 hinv4.2.2.2.1 hinv4.2.2.2.2.1
                hinv4.2.2.2.2.2.1 hinv4.2.2.2.2.2.2.1 hinv4.2.2.2.2.2.2.2.1
                hinv4.2.2.2.2.2.2.2.2.1 hinv4.2.2.2.2.2.2.2.2.2.1 hinv4.2.2.2.2.2.2.2.2.2.2.1
                hinv4.2.2.2.2.2.2.2.2.2.2.2.1 hinv4.2.2.2.2.2.2.2.2.2.2.2.2.1
                hinv4.2.2.2.2.2.2.2.2.2.2.2.2.2 (Or.inr (Or.inr rfl)) (fun _ => huns3) hm4
          · c0_hsteps!; exact hJc (false, ()) m2 ⟨s2, hinv2, hm2'⟩
        · intro Ju hJu
          have hent := ef_unit_entails hw2 hcl0 hrb_lt heqv_rbra hvb_ne0
          cong_split
          · have hlt : ra.toNat < 2 * s2.core.cur_vars := hra_lt
            have hpos : (0#32 : BitVec 32).slt
                (BitVec.signExtend 32 (s2.core.vals[rb.toNat]?.getD 0#8)) = true := by
              rw [List.getElem?_eq_getElem (by change rb.toNat < s.core.vals.length; omega),
                Option.getD_some]
              try rw [list_getElem_congr (bv_zext32_toNat rb) hrb_vals _] at hc
              simpa using hc
            c0_hsteps!; exact hJu (ra, ()) m2 ⟨rfl, hlt, by simpa [hpos] using hent⟩
          · have hlt : (ra ^^^ 1#32).toNat < 2 * s2.core.cur_vars := by
              rw [bv32_xor1_eq_litNeg]; exact litNeg_lt_two_mul hra_lt
            have hneg : (0#32 : BitVec 32).slt
                (BitVec.signExtend 32 (s2.core.vals[rb.toNat]?.getD 0#8)) = false := by
              rw [List.getElem?_eq_getElem (by change rb.toNat < s.core.vals.length; omega),
                Option.getD_some]
              try rw [list_getElem_congr (bv_zext32_toNat rb) hrb_vals _] at hc
              simpa using hc
            c0_hsteps!; exact hJu (ra ^^^ 1#32, ()) m2 ⟨rfl, hlt, by simpa [hneg] using hent⟩
      · c0_hsteps!; exact hJc (false, ()) m2 ⟨s2, hinv2, hm2'⟩

end

end LeanQbe.T.Examples.Kissat.Proof.Congruence
