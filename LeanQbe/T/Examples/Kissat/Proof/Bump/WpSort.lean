/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Src.Bump
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena
public import LeanQbe.T.Examples.Kissat.Proof.Bump.Spec
import LeanQbe.T.Examples.Kissat.Proof.Lib.ContractLemmas
public import LeanQbe.T.Examples.Kissat.Proof.Bump.WpSortHelpers
public import LeanQbe.T.Examples.Kissat.Proof.Bump.WpSortRadix
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
import LeanQbe.T.Examples.Kissat.Proof.Spec.MemBridges
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
meta import LeanQbe.T.Logic.C0Step
meta import LeanQbe.T.Logic.C0HeadStep

/-!
# WP Proofs for `full_ana_sift_m6` and `full_sort_ana_qs_m6` (`Proof.Bump.WpSort`)

Canonical `Func.wp` proofs for the two analysis-array sorting functions in `Src.Bump.fns`:
- `full_ana_sift_m6_wp`
- `full_sort_ana_qs_m6_wp` (delegating to `sort_ana_ins_wp`, `sort_ana_radix_wp`, and
  `sort_ana_heap_wp`).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Bump

open Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Src.Bump
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Spec.FullKissatMath
open LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open LeanQbe.T.Examples.Kissat.Proof.Bump.Spec
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open Kraken.Bedrock2.Test

public section

/-! ## 1. WP Proof of `full_ana_sift_m6` -/

theorem full_ana_sift_m6_wp (Γ : Env) :
    ∀ a m Q X, anaSiftSpec a m Q X →
      Func.wp Γ full_ana_sift_m6_body a m Q X := by
  rintro ⟨qs_ptr, ana_ptr, cv, start, n, ⟨⟩⟩ m Q X hs
  obtain ⟨⟨qs, ana⟩, R, ⟨hcv_qs, hst_n, hn_ana, hn62, hcov⟩, hm, hQ⟩ := FnContract.elim hs
  unfold Func.wp full_ana_sift_m6_body
  c0_hsteps_nogrp
  refine wp_join_group (fun (_, ()) m_b => Q () m_b)
    (fun _ _ m_b hm_b => by c0_hsteps_nogrp; exact hm_b)
    (fun J_brk hJ_brk => ?_)
  refine wp_loop_inv
    (fun (root, ()) m1 => ∃ ana1 : List (BitVec 32),
      ana1.length = ana.length ∧ root.toNat ≤ n.toNat ∧
      (ana1.take n.toNat).Perm (ana.take n.toNat) ∧
      (∀ k, n.toNat ≤ k → ana1[k]? = ana[k]?) ∧
      (∀ k < n.toNat, (ana1[k]?.getD 0#32).toNat < cv.toNat) ∧
      (array (t := i32) qs_ptr qs ⋆ array (t := i32) ana_ptr ana1 ⋆ R) m1)
    (fun (root, ()) _ => n.toNat - root.toNat)
    (fun J1 hJ1 => by
      c0_hsteps_nogrp
      exact hJ1 (start, ()) m ⟨ana, rfl, hst_n, List.Perm.refl _, fun _ _ => rfl, hcov, hm⟩)
    (fun J1 (root, ()) m1 ⟨ana1, hlen1, hrt_le, hpm1, htail1, hcov1, hm1⟩ ih1 => ?_)
  rw [Blocks.get_here]
  have hsh_lt : (root <<< (1 : Nat)).toNat = 2 * root.toNat := by
    have h2 : 2 * root.toNat < 2 ^ 64 := by omega
    simpa using bv64_shl1_toNat h2
  have hch_lt : ((root <<< (1 : Nat)) + 1#64).toNat = 2 * root.toNat + 1 := by
    rw [BitVec.toNat_add, hsh_lt]
    simp [Nat.mod_eq_of_lt (by omega : 2 * root.toNat + 1 < 2 ^ 64)]
  c0_hsteps_nogrp
  · exact hJ_brk _ m1 (hQ () ana1 m1 ⟨hlen1, hpm1, htail1, hcov1⟩ hm1)
  · have hch_n : 2 * root.toNat + 1 < n.toNat := by
      have h1 : ((root <<< (1 : Nat)) + 1#64).toNat < n.toNat := by c0_bound
      rwa [hch_lt] at h1
    have hrt_n : root.toNat < n.toNat := by omega
    have hch_ana1 : ((root <<< (1 : Nat)) + 1#64).toNat < ana1.length := by omega
    c0_hsteps_nogrp
    let ch0 := (root <<< (1 : Nat)) + 1#64
    refine wp_join_group (ts := [i32]) (fun (_, ()) m2 => m1 = m2) ?_ ?_
    · intro _ ⟨qc0, ⟨⟩⟩ m2 hm2
      rw [Blocks.get_here]
      rcases hm2 with rfl
      c0_hsteps_nogrp
      refine wp_join_group (ts := [i64, i32])
        (fun (ch', _qc', ()) m3 => m1 = m3 ∧ ch'.toNat < n.toNat ∧ root.toNat < ch'.toNat)
        ?_ ?_
      · intro _ ⟨ch', qc', ⟨⟩⟩ m3 ⟨hm3, hch'_n, hrt_ch'⟩
        rw [Blocks.get_here]
        rcases hm3 with rfl
        have hrt_ana1 : root.toNat < ana1.length := by omega
        c0_hsteps_nogrp
        refine wp_join_group (ts := [i32]) (fun (_, ()) m4 => m1 = m4) ?_ ?_
        · intro _ ⟨qr, ⟨⟩⟩ m4 hm4
          rw [Blocks.get_here]
          rcases hm4 with rfl
          c0_hsteps_nogrp
          · exact hJ_brk _ m1 (hQ () ana1 m1 ⟨hlen1, hpm1, htail1, hcov1⟩ hm1)
          · have hch'_ana1 : ch'.toNat < ana1.length := by omega
            c0_hsteps_nogrp
            let ar := ana1[root.toNat]'hrt_ana1
            let ana2 := listSwap ana1 root.toNat ch'.toNat hrt_ana1 hch'_ana1
            have hana2_len : ana2.length = ana.length := by rw [listSwap_length, hlen1]
            have hpm2 : (ana2.take n.toNat).Perm (ana.take n.toNat) :=
              (list_take_set_perm_swap ana1 hrt_n hch'_n (by omega)).trans hpm1
            have htail2 : ∀ k, n.toNat ≤ k → ana2[k]? = ana[k]? := by
              intro k hk
              rw [listSwap_getElem_ge ana1 root.toNat ch'.toNat k hrt_ana1 hch'_ana1
                (by omega) (by omega)]
              exact htail1 k hk
            have hcov2 := listSwap_cov hrt_n hch'_n (by omega) hcov1
            refine ih1 (ch', ()) _ (by dsimp only; omega)
              ⟨ana2, hana2_len, by omega, hpm2, htail2, hcov2, ?_⟩
            rw [sep_comm (array (t := i32) qs_ptr qs), sep_assoc, ← sep_emp R]
            assumption
        · intro Jqr hJqr
          let ar := ana1[root.toNat]'hrt_ana1
          have har_cv : ar.toNat < cv.toNat := by
            have h1 := hcov1 root.toNat hrt_n
            rwa [List.getElem?_eq_getElem hrt_ana1, Option.getD_some] at h1
          have har_qs : (BitVec.setWidth 64 ar).toNat < qs.length := by
            rw [zext_toNat _ (by decide)]; omega
          c0_hsteps_nogrp
          · exact hJqr _ m1 rfl
          · exact hJqr _ m1 rfl
      · intro Jch hJch
        c0_hsteps_nogrp
        · have hch0_nat : ch0.toNat = 2 * root.toNat + 1 := hch_lt
          have hch1_n : (ch0 + 1#64).toNat < n.toNat := by
            rw [BitVec.toNat_add, hch0_nat, show (1#64 : BitVec 64).toNat = 1 from rfl]
            assumption
          have hch1_ana1 : (ch0 + 1#64).toNat < ana1.length := by omega
          c0_hsteps_nogrp
          refine wp_join_group (ts := [i32]) (fun (_, ()) m3 => m1 = m3) ?_ ?_
          · intro _ ⟨qc1, ⟨⟩⟩ m3 hm3
            rw [Blocks.get_here]
            rcases hm3 with rfl
            c0_hsteps_nogrp
            refine wp_join_group (ts := [i64, i32])
              (fun (ch', _qc', ()) m4 => m1 = m4 ∧ ch'.toNat < n.toNat ∧ root.toNat < ch'.toNat)
              ?_ ?_
            · intro _ ⟨ch', qc', ⟨⟩⟩ m4 ⟨hm4, h1, h2⟩
              rw [Blocks.get_here]
              c0_hsteps_nogrp
              exact hJch (ch', qc', ()) m4 ⟨hm4, h1, h2⟩
            · intro Jcmp hJcmp
              have hch0_nat : ch0.toNat = 2 * root.toNat + 1 := hch_lt
              have hch0_p1 : (ch0 + 1#64).toNat = 2 * root.toNat + 2 := by
                rw [BitVec.toNat_add, hch0_nat, show (1#64 : BitVec 64).toNat = 1 from rfl,
                  Nat.mod_eq_of_lt (by omega : 2 * root.toNat + 2 < 2 ^ 64)]
              c0_hsteps_nogrp
              · exact hJcmp (ch0 + 1#64, qc1, ()) m1 ⟨rfl, hch1_n, by omega⟩
              · exact hJcmp (ch0, qc0, ()) m1 ⟨rfl, by omega, by omega⟩
          · intro Jqc1 hJqc1
            let ac1 := ana1[(ch0 + 1#64).toNat]'hch1_ana1
            have hac1_cv : ac1.toNat < cv.toNat := by
              have h1 := hcov1 (ch0 + 1#64).toNat hch1_n
              rwa [List.getElem?_eq_getElem hch1_ana1, Option.getD_some] at h1
            have hac1_qs : (BitVec.setWidth 64 ac1).toNat < qs.length := by
              rw [zext_toNat _ (by decide)]; omega
            c0_hsteps_nogrp
            · exact hJqc1 _ m1 rfl
            · exact hJqc1 _ m1 rfl
        · exact hJch (ch0, qc0, ()) m1
            ⟨rfl, by rw [show ch0.toNat = 2 * root.toNat + 1 from hch_lt]; exact hch_n,
              by rw [show ch0.toNat = 2 * root.toNat + 1 from hch_lt]; omega⟩
    · intro Jqc0 hJqc0
      let ac0 := ana1[ch0.toNat]'hch_ana1
      have hac0_cv : ac0.toNat < cv.toNat := by
        have h1 := hcov1 ch0.toNat
          (by rw [show ch0.toNat = 2 * root.toNat + 1 from hch_lt]; exact hch_n)
        rwa [List.getElem?_eq_getElem hch_ana1, Option.getD_some] at h1
      have hac0_qs : (BitVec.setWidth 64 ac0).toNat < qs.length := by
        rw [zext_toNat _ (by decide)]; omega
      c0_hsteps_nogrp
      · exact hJqc0 _ m1 rfl
      · exact hJqc0 _ m1 rfl
  · simp_all

/-! ## 2. Heapsort & Insertion-Sort Branches -/

private theorem sort_ana_heap_wp {Γ : Env} {Q : Post []} {X : XPost} {c : FullCfg}
    {s : FullState} {n : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64}
    (hSift : Γ.Has "full_ana_sift_m6" anaSiftSpec)
    (hlen : s.LengthsOk c) (hn_cv : n.toNat ≤ s.core.cur_vars)
    (hn_gt1 : ¬ n.toNat ≤ 1)
    (hcov0 : ∀ k < n.toNat, (s.scratch.work_stk1[k]?.getD 0#32).toNat < s.core.cur_vars)
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ ws1' repr' wsort' sbuf' m',
      ws1'.length = 2 * c.max_vars → repr'.length = 2 * c.max_vars →
      wsort'.length = 2 * c.max_vars → sbuf'.length = c.scratch_cap →
      (ws1'.take n.toNat).Perm (s.scratch.work_stk1.take n.toNat) →
      (∀ k, n.toNat ≤ k → ws1'[k]? = s.scratch.work_stk1[k]?) →
      (∀ k < n.toNat, (ws1'[k]?.getD 0#32).toNat < s.core.cur_vars) →
      (FullMem c { s with core := { s.core with repr := repr' }
                          scratch := { s.scratch with
                            work_stk1 := ws1', wsort := wsort', scratch_buf := sbuf' } } ⋆ R)
        m' → Q () m') :
    let cv := BitVec.ofNat 64 s.core.cur_vars
    wp Γ Q X
      (.group (sig := [[i64]]) (fun Js => .cons (fun p =>
        .let_ { sig := [i64, i64], code := .cmp .ugt i64 .bool (by decide),
                args := (.var p.fst, .imm 0, ()) } fun p_1 =>
        .jnz (.var p_1.fst)
          (.let_ { sig := [i64, i64], code := .sub i64, args := (.var p.fst, .imm 1, ()) } fun p =>
           .call (V := Val) (as := [i64, i64, i64, i64, i64]) "full_ana_sift_m6"
             (.var (c.pQStamp : Val i64), .var (c.pWorkStk1 : Val i64),
               .var cv, .var p.fst, .var n, ())
             (fun (_ : Tup Val []) => .jump Js.fst (.var p.fst, ())))
          (.let_ { sig := [i64, i64], code := .sub i64, args := (.var n, .imm 1, ()) } fun p =>
           .group (sig := [[i64]]) (fun Js => .cons (fun p =>
             .let_ { sig := [i64, i64], code := .cmp .ugt i64 .bool (by decide),
                     args := (.var p.fst, .imm 0, ()) } fun p_2 =>
             .jnz (.var p_2.fst)
               (.let_ { sig := [i32], code := .sext 32 64, args := (.imm 0, ()) } fun p_3 =>
                .let_ { sig := [i64, i64], code := .mul i64,
                        args := (.var p_3.fst, .imm 4, ()) } fun p_4 =>
                .let_ { sig := [i64, i64], code := .add i64,
                        args := (.var c.pWorkStk1, .var p_4.fst, ()) } fun p_5 =>
                .load i32 (.var p_5.fst) fun ld =>
                .let_ { sig := [i32], code := .sext 32 64, args := (.imm 0, ()) } fun p_6 =>
                .let_ { sig := [i64, i64], code := .mul i64,
                        args := (.var p_6.fst, .imm 4, ()) } fun p_7 =>
                .let_ { sig := [i64, i64], code := .add i64,
                        args := (.var c.pWorkStk1, .var p_7.fst, ()) } fun p_8 =>
                .let_ { sig := [i64, i64], code := .mul i64,
                        args := (.var p.fst, .imm 4, ()) } fun p_9 =>
                .let_ { sig := [i64, i64], code := .add i64,
                        args := (.var c.pWorkStk1, .var p_9.fst, ()) } fun p_10 =>
                .load i32 (.var p_10.fst) fun ld_1 =>
                .store (.var ld_1) (.var p_8.fst)
                (.let_ { sig := [i64, i64], code := .mul i64,
                         args := (.var p.fst, .imm 4, ()) } fun p_11 =>
                 .let_ { sig := [i64, i64], code := .add i64,
                         args := (.var c.pWorkStk1, .var p_11.fst, ()) } fun p_12 =>
                 .store (.var ld) (.var p_12.fst)
                 (.call (V := Val) (as := [i64, i64, i64, i64, i64]) "full_ana_sift_m6"
                   (.var (c.pQStamp : Val i64), .var (c.pWorkStk1 : Val i64),
                     .var cv, .imm 0, .var p.fst, ())
                   (fun (_ : Tup Val []) =>
                    .let_ { sig := [i64, i64], code := .sub i64,
                            args := (.var p.fst, .imm 1, ()) } fun p =>
                    .jump Js.fst (.var p.fst, ())))))
               (.ret ())) .nil)
             fun Js => .jump Js.fst (.var p.fst, ()))) .nil)
        fun Js => .jump Js.fst (.var (n >>> (1 : BitVec 64)), ())) m := by
  obtain hok := hlen.core_ok
  obtain hsok := hlen.scratch_ok
  have hmaxv : c.max_vars < 2 * Ref.dimacsBound := c.hmaxv
  unfold Ref.dimacsBound at hmaxv
  have hcv_le := hok.cur_vars_le
  have hcv_lt64 : s.core.cur_vars < 2 ^ 64 := by omega
  have hcv_eq : (BitVec.ofNat 64 s.core.cur_vars).toNat = s.core.cur_vars :=
    bv64_ofNat_toNat hcv_lt64
  have hna_len : s.scratch.work_stk1.length = 2 * c.max_vars := hsok.work_stk1_len
  have hqs_len : s.scratch.q_stamp.length = c.max_vars := hsok.q_stamp_len
  have hrp_len : s.core.repr.length = 2 * c.max_vars := hok.repr_len
  have hws_len : s.scratch.wsort.length = 2 * c.max_vars := hsok.wsort_len
  have hsb_len : s.scratch.scratch_buf.length = c.scratch_cap := hsok.scratch_buf_len
  let ana0 := s.scratch.work_stk1
  refine wp_loop_inv
    (fun (start, ()) m1 => ∃ ana1 : List (BitVec 32),
      ana1.length = 2 * c.max_vars ∧ start.toNat ≤ n.toNat ∧
      (ana1.take n.toNat).Perm (ana0.take n.toNat) ∧
      (∀ k, n.toNat ≤ k → ana1[k]? = ana0[k]?) ∧
      (∀ k < n.toNat, (ana1[k]?.getD 0#32).toNat < s.core.cur_vars) ∧
      (FullMem c { s with scratch := { s.scratch with work_stk1 := ana1 } } ⋆ R) m1)
    (fun (start, ()) _ => start.toNat)
    (fun Jb hJb => by
      c0_hsteps_nogrp
      have hshr_eq : (n >>> (1 : BitVec 64)).toNat = n.toNat >>> (1 : BitVec 64).toNat :=
        BitVec.toNat_ushiftRight n (1 : BitVec 64).toNat
      have hshr : (n >>> (1 : BitVec 64)).toNat ≤ n.toNat :=
        hshr_eq ▸ Nat.shiftRight_le _ _
      exact hJb (n >>> (1 : BitVec 64), ()) m
        ⟨ana0, hna_len, hshr, List.Perm.refl _, fun _ _ => rfl, hcov0, hm⟩)
    (fun Jb (start, ()) m1 ⟨ana1, hana1, hst_le, hpm1, htl1, hcov1, hm1⟩ ihb => ?_)
  rw [Blocks.get_here]
  c0_hsteps_nogrp
  · have hst_pos : 0 < start.toNat := by c0_bound
    have hsm1 : (start - 1).toNat = start.toNat - 1 := by bv_omega
    have hm1' := hm1
    rw [fullMem_focus_qs_ws1_upd] at hm1'
    c0_call hSift
    refine FnContract.intro (s.scratch.q_stamp, ana1) (SiftTail c s R)
      ⟨by rw [hcv_eq, hqs_len]; exact hcv_le, by omega, by rw [hana1]; omega,
       by omega, by rwa [hcv_eq]⟩ hm1' ?_
    rintro ⟨⟩ ana2 m2 ⟨hlen2, hpm2, htl2, hcov2⟩ hm2'
    rw [hcv_eq] at hcov2
    have hm2 : (FullMem c { s with scratch := { s.scratch with work_stk1 := ana2 } } ⋆ R) m2 := by
      rw [fullMem_focus_qs_ws1_upd]; exact hm2'
    c0_hsteps_nogrp
    exact ihb (start - 1, ()) m2 (by dsimp only; omega)
      ⟨ana2, by rw [hlen2, hana1], by omega, hpm2.trans hpm1,
        fun k hk => (htl2 k hk).trans (htl1 k hk), hcov2, hm2⟩
  · have hnm1 : (n - 1#64).toNat = n.toNat - 1 := by bv_omega
    c0_hsteps_nogrp
    refine wp_loop_inv
      (fun (endv, ()) m2 => ∃ ana2 : List (BitVec 32),
        ana2.length = 2 * c.max_vars ∧ endv.toNat < n.toNat ∧
        (ana2.take n.toNat).Perm (ana0.take n.toNat) ∧
        (∀ k, n.toNat ≤ k → ana2[k]? = ana0[k]?) ∧
        (∀ k < n.toNat, (ana2[k]?.getD 0#32).toNat < s.core.cur_vars) ∧
        (FullMem c { s with scratch := { s.scratch with work_stk1 := ana2 } } ⋆ R) m2)
      (fun (endv, ()) _ => endv.toNat)
      (fun Je hJe => by
        c0_hsteps_nogrp
        exact hJe (n - 1#64, ()) m1 ⟨ana1, hana1, by rw [hnm1]; omega, hpm1, htl1, hcov1, hm1⟩)
      (fun Je (endv, ()) m2 ⟨ana2, hana2, he_lt, hpm2, htl2, hcov2, hm2⟩ ihe => ?_)
    rw [Blocks.get_here]
    c0_hsteps_nogrp
    · have he_pos : 0 < endv.toNat := by c0_bound
      have hem1 : (endv - 1#64).toNat = endv.toNat - 1 := by bv_omega
      have h0_ana2 : 0 < ana2.length := by rw [hana2]; omega
      have he_ana2 : endv.toNat < ana2.length := by rw [hana2]; omega
      rw [fullMem_focus_qs_ws1_upd] at hm2
      c0_hsteps_nogrp
      let ana2' := listSwap ana2 0 endv.toNat h0_ana2 he_ana2
      have hana2'_len : ana2'.length = 2 * c.max_vars := by rw [listSwap_length, hana2]
      have hpm2' : (ana2'.take n.toNat).Perm (ana0.take n.toNat) :=
        (list_take_set_perm_swap ana2 (by omega) he_lt (by omega)).trans hpm2
      have htl2' : ∀ k, n.toNat ≤ k → ana2'[k]? = ana0[k]? := by
        intro k hk
        rw [listSwap_getElem_ge ana2 0 endv.toNat k h0_ana2 he_ana2 (by omega) (by omega)]
        exact htl2 k hk
      have hcov2' := listSwap_cov (by omega : 0 < n.toNat) he_lt (by omega) hcov2
      c0_call hSift
      refine FnContract.intro (s.scratch.q_stamp, ana2') (SiftTail c s R)
        ⟨by rw [hcv_eq, hqs_len]; exact hcv_le, by simp, by rw [hana2'_len]; omega,
         by omega, fun k hk => by rw [hcv_eq]; exact hcov2' k (by omega)⟩ ?_ ?_
      · simp only [sep_emp] at hm ⊢
        have hmem_eq :
            (array (t := i32) c.pWorkStk1 ana2' ⋆
              (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆ SiftTail c s R)) =
            (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
              array (t := i32) c.pWorkStk1 ana2' ⋆ SiftTail c s R) := by ac_rfl
        exact hmem_eq ▸ hm
      · rintro ⟨⟩ ana3 m3 ⟨hlen3, hpm3, htl3, hcov3⟩ hm3'
        rw [hcv_eq] at hcov3
        have hm3 :
            (FullMem c { s with scratch := { s.scratch with work_stk1 := ana3 } } ⋆ R) m3 := by
          rw [fullMem_focus_qs_ws1_upd]; exact hm3'
        have hpm_n : (ana3.take n.toNat).Perm (ana2'.take n.toNat) :=
          list_perm_take_split ana2' ana3 (by omega : endv.toNat ≤ n.toNat) hpm3 htl3
        have hcov3' : ∀ k < n.toNat, (ana3[k]?.getD 0#32).toNat < s.core.cur_vars := by
          intro k hk
          by_cases hke : k < endv.toNat
          · exact hcov3 k hke
          · have h1 := hcov2' k hk; rwa [← htl3 k (by omega)] at h1
        c0_hsteps_nogrp
        exact ihe (endv - 1#64, ()) m3 (by dsimp only; rw [hem1]; omega)
          ⟨ana3, by rw [hlen3, hana2'_len], by rw [hem1]; omega, hpm_n.trans hpm2',
            fun k hk => (htl3 k (by omega)).trans (htl2' k hk), hcov3', hm3⟩
    · exact hQ ana2 s.core.repr s.scratch.wsort s.scratch.scratch_buf m2
        hana2 hrp_len hws_len hsb_len hpm2 htl2 hcov2 hm2

private theorem sort_ana_ins_wp {Γ : Env} {Q : Post []} {X : XPost} {c : FullCfg}
    {s : FullState} {n : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64}
    (hlen : s.LengthsOk c) (hn_cv : n.toNat ≤ s.core.cur_vars)
    (hn_gt1 : 1 < n.toNat) (hn_lt32 : n.toNat < 32)
    (hcov0 : ∀ k < n.toNat, (s.scratch.work_stk1[k]?.getD 0#32).toNat < s.core.cur_vars)
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ ws1' repr' wsort' sbuf' m',
      ws1'.length = 2 * c.max_vars → repr'.length = 2 * c.max_vars →
      wsort'.length = 2 * c.max_vars → sbuf'.length = c.scratch_cap →
      (ws1'.take n.toNat).Perm (s.scratch.work_stk1.take n.toNat) →
      (∀ k, n.toNat ≤ k → ws1'[k]? = s.scratch.work_stk1[k]?) →
      (∀ k < n.toNat, (ws1'[k]?.getD 0#32).toNat < s.core.cur_vars) →
      (FullMem c { s with core := { s.core with repr := repr' }
                          scratch := { s.scratch with
                            work_stk1 := ws1', wsort := wsort', scratch_buf := sbuf' } } ⋆ R)
        m' → Q () m') :
    Func.wp Γ full_sort_ana_qs_m6_body (c.hdr, n, ()) m Q X := by
  obtain hok := hlen.core_ok
  obtain hsok := hlen.scratch_ok
  have hmaxv : c.max_vars < 2 * Ref.dimacsBound := c.hmaxv
  unfold Ref.dimacsBound at hmaxv
  have hcv_le := hok.cur_vars_le
  have hna_len : s.scratch.work_stk1.length = 2 * c.max_vars := hsok.work_stk1_len
  have hrp_len : s.core.repr.length = 2 * c.max_vars := hok.repr_len
  have hws_len : s.scratch.wsort.length = 2 * c.max_vars := hsok.wsort_len
  have hsb_len : s.scratch.scratch_buf.length = c.scratch_cap := hsok.scratch_buf_len
  have hn_gt1_bv : ¬ (n ≤ 1#64) := by c0_bound
  have hn_le_cv : ¬ ((BitVec.ofNat 64 s.core.cur_vars) < n) := by c0_bound
  have hn_lt32_bv : n < 32#64 := by c0_bound
  unfold Func.wp full_sort_ana_qs_m6_body
  dsimp only
  c0_hsteps_nogrp
  let ana0 := s.scratch.work_stk1
  let rk0 := packPairs64 s.core.repr
  have hrk0_len : rk0.length = c.max_vars := by
    dsimp [rk0]; rw [packPairs64_length, hrp_len]; omega
  have hm_ins := hm
  rw [fullMem_focus_ins c s R hlen] at hm_ins
  refine sort_ana_pack_wp hlen hn_cv hrk0_len hcov0 hm_ins fun rk1 m1 hrk1 hpk1 hm1 => ?_
  refine wp_loop_inv
    (fun (i, ()) m2 => ∃ rk2 : List (BitVec 64),
      rk2.length = c.max_vars ∧ 1 ≤ i.toNat ∧ i.toNat ≤ n.toNat ∧
      (rk2.take n.toNat).Perm (rk1.take n.toNat) ∧
      (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
        array (t := i32) c.pWorkStk1 ana0 ⋆ array64 c.pRepr rk2 ⋆ InsTail c s R) m2)
    (fun (i, ()) _ => n.toNat - i.toNat)
    (fun Ji hJi => by
      c0_hsteps_nogrp
      have h1eq : (1#64 : BitVec 64).toNat = 1 := rfl
      exact hJi (1#64, ()) m1
        ⟨rk1, hrk1, by rw [h1eq]; exact Nat.le_refl _, by rw [h1eq]; omega,
          List.Perm.refl _, hm1⟩)
    (fun Ji (i, ()) m2 ⟨rk2, hrk2, hi1, hi_le2, hpm2, hm2⟩ ihi => ?_)
  rw [Blocks.get_here]
  c0_hsteps_nogrp
  · have hi_lt2 : i.toNat < n.toNat := by c0_bound
    have hi_rk2 : i.toNat < rk2.length := by rw [hrk2]; omega
    have hip1 : (i + 1#64).toNat = i.toNat + 1 := by bv_omega
    let x := rk2[i.toNat]'hi_rk2
    c0_hsteps_nogrp
    refine wp_loop_inv
      (fun (j, ()) m3 => ∃ rk3 : List (BitVec 64),
        rk3.length = c.max_vars ∧ j.toNat ≤ i.toNat ∧
        ((rk3.set j.toNat x).take n.toNat).Perm (rk2.take n.toNat) ∧
        (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
          array (t := i32) c.pWorkStk1 ana0 ⋆ array64 c.pRepr rk3 ⋆ InsTail c s R) m3)
      (fun (j, ()) _ => j.toNat)
      (fun Jj hJj => by
        c0_hsteps_nogrp
        have hself : rk2.set i.toNat x = rk2 := List.set_getElem_self hi_rk2
        exact hJj (i, ()) m2 ⟨rk2, hrk2, Nat.le_refl _, by rw [hself], hm2⟩)
      (fun Jj (j, ()) m3 ⟨rk3, hrk3, hj_le, hpm3, hm3⟩ ihj => ?_)
    rw [Blocks.get_here]
    refine wp_join_group
      (fun (_ : Tup Val []) m4 => ∃ rk4 : List (BitVec 64), rk4.length = c.max_vars ∧
        ((rk4.set j.toNat x).take n.toNat).Perm (rk2.take n.toNat) ∧
        (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
          array (t := i32) c.pWorkStk1 ana0 ⋆ array64 c.pRepr rk4 ⋆ InsTail c s R) m4)
      ?_ ?_
    · intro _ _ m4 ⟨rk4, hrk4, hpm4, hm4⟩
      rw [Blocks.get_here]
      have hj_rk4 : j.toNat < rk4.length := by rw [hrk4]; omega
      c0_hsteps_nogrp
      refine ihi (i + 1#64, ()) _ (by dsimp only; omega)
        ⟨rk4.set j.toNat x, by simp [hrk4], by rw [hip1]; omega, by rw [hip1]; omega,
          hpm4.trans hpm2, ?_⟩
      have hmem_eq :
          (array64 c.pRepr (rk4.set j.toNat x) ⋆
            (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
              (array (t := i32) c.pWorkStk1 ana0 ⋆ (InsTail c s R ⋆ emp)))) =
          (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
            array (t := i32) c.pWorkStk1 ana0 ⋆
            array64 c.pRepr (rk4.set j.toNat x) ⋆ InsTail c s R) := by
        rw [sep_emp (InsTail c s R)]; ac_rfl
      exact hmem_eq ▸ hm
    · intro Jtail hJtail
      c0_hsteps_nogrp
      · have hj_pos : 0 < j.toNat := by c0_bound
        have hj1 : (j - 1#64).toNat = j.toNat - 1 := by bv_omega
        have hjm1_rk3 : (j - 1#64).toNat < rk3.length := by rw [hrk3, hj1]; omega
        have hj_rk3 : j.toNat < rk3.length := by rw [hrk3]; omega
        c0_hsteps_nogrp
        · have hval_eq : rk3[j.toNat - 1]'(by rw [hrk3]; omega) =
              rk3[(j - 1#64).toNat]'hjm1_rk3 := by congr 1; exact hj1.symm
          let rk3' := rk3.set j.toNat (rk3[j.toNat - 1]'(by rw [hrk3]; omega))
          have hrk3' : rk3'.length = c.max_vars := by simp [rk3', hrk3]
          have hsw := ins_step_swap_eq rk3 hj_pos hj_rk3 x
          have hpm_step : ((rk3'.set (j - 1#64).toNat x).take n.toNat).Perm
              (rk2.take n.toNat) := by
            rw [hj1]; dsimp only [rk3']; rw [hsw]
            exact (list_take_set_perm_swap (rk3.set j.toNat x)
              (by omega) (by omega) (by simp [hrk3]; omega)).trans hpm3
          refine ihj (j - 1#64, ()) _ (by dsimp only; rw [hj1]; omega)
            ⟨rk3', hrk3', by rw [hj1]; omega, hpm_step, ?_⟩
          have hmem_eq :
              (array64 c.pRepr (rk3.set j.toNat (rk3[(j - 1#64).toNat]'hjm1_rk3)) ⋆
                (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
                  (array (t := i32) c.pWorkStk1 ana0 ⋆ (InsTail c s R ⋆ emp)))) =
              (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
                array (t := i32) c.pWorkStk1 ana0 ⋆
                array64 c.pRepr rk3' ⋆ InsTail c s R) := by
            dsimp only [rk3']; rw [hval_eq, sep_emp (InsTail c s R)]; ac_rfl
          exact hmem_eq ▸ hm
      all_goals exact hJtail () m3 ⟨rk3, hrk3, hpm3, hm3⟩
  · have hm2_cp : (array (t := i32) c.pWorkStk1 ana0 ⋆ array64 c.pRepr rk2 ⋆
        (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆ InsTail c s R)) m2 := by
      have heq : (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
          array (t := i32) c.pWorkStk1 ana0 ⋆ array64 c.pRepr rk2 ⋆ InsTail c s R) =
        (array (t := i32) c.pWorkStk1 ana0 ⋆ array64 c.pRepr rk2 ⋆
          (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆ InsTail c s R)) := by ac_rfl
      exact heq ▸ hm2
    refine sort_ana_copy_wp hlen hn_cv hrk2 hm2_cp fun ana3 m3 hana3 hcp3 htl3 hm3 => ?_
    have hm3_un : (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
        array (t := i32) c.pWorkStk1 ana3 ⋆ array64 c.pRepr rk2 ⋆ InsTail c s R) m3 := by
      have heq : (array (t := i32) c.pWorkStk1 ana3 ⋆ array64 c.pRepr rk2 ⋆
          (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆ InsTail c s R)) =
        (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
          array (t := i32) c.pWorkStk1 ana3 ⋆ array64 c.pRepr rk2 ⋆ InsTail c s R) := by ac_rfl
      exact heq ▸ hm3
    obtain ⟨hpm_end, hcov_end⟩ := ana_copy_perm_cov ana0 ana3 rk1 rk2
      (by dsimp [ana0]; omega) (by rw [hana3, hna_len]) (by rw [hrk1]; omega)
      (by rw [hrk2, hrk1]) hpk1 hpm2 hcp3 hcov0
    have hm_fin := hm3_un
    rw [fullMem_unfocus_ins c s R hrk2] at hm_fin
    exact hQ ana3 (unpackPairs32 rk2) s.scratch.wsort s.scratch.scratch_buf m3
      hana3 (by rw [unpackPairs32_length, hrk2]) hws_len hsb_len
      hpm_end htl3 hcov_end hm_fin

/-! ## 3. Main `full_sort_ana_qs_m6_wp` Proof -/

theorem full_sort_ana_qs_m6_wp (Γ : Env)
    (hSift : Γ.Has "full_ana_sift_m6" anaSiftSpec) :
    ∀ a m Q X, sortAnaQsSpec a m Q X →
      Func.wp Γ full_sort_ana_qs_m6_body a m Q X := by
  rintro ⟨h, n, ⟨⟩⟩ m Q X hs
  obtain ⟨c, s, ⟨⟩, R, rfl, hlen, ⟨hn_cv, hcov0⟩, hm, hQ0⟩ := FullContract.elim hs
  let hQ : ∀ ws1' repr' wsort' sbuf' m',
      ws1'.length = 2 * c.max_vars → repr'.length = 2 * c.max_vars →
      wsort'.length = 2 * c.max_vars → sbuf'.length = c.scratch_cap →
      (ws1'.take n.toNat).Perm (s.scratch.work_stk1.take n.toNat) →
      (∀ k, n.toNat ≤ k → ws1'[k]? = s.scratch.work_stk1[k]?) →
      (∀ k < n.toNat, (ws1'[k]?.getD 0#32).toNat < s.core.cur_vars) →
      (FullMem c { s with core := { s.core with repr := repr' }
                          scratch := { s.scratch with
                            work_stk1 := ws1', wsort := wsort', scratch_buf := sbuf' } } ⋆ R)
        m' → Q () m' :=
    fun ws1' repr' wsort' sbuf' m' hws1 hrep hwso hsbu hpm htl hcv hm' =>
      hQ0 ()
        { core := { s.core with repr := repr' }
          scratch := { s.scratch with
            work_stk1 := ws1', wsort := wsort', scratch_buf := sbuf' } }
        m'
        ⟨{ hlen.core_ok with repr_len := hrep },
         { hlen.scratch_ok with
           work_stk1_len := hws1, wsort_len := hwso, scratch_buf_len := hsbu }⟩
        ⟨rfl, hpm, htl, hcv⟩ hm'
  by_cases hn1 : n.toNat ≤ 1
  · obtain hok := hlen.core_ok
    obtain hsok := hlen.scratch_ok
    have hmaxv : c.max_vars < 2 * Ref.dimacsBound := c.hmaxv
    unfold Ref.dimacsBound at hmaxv
    unfold Func.wp full_sort_ana_qs_m6_body
    dsimp only
    c0_hsteps_nogrp
    exact hQ s.scratch.work_stk1 s.core.repr s.scratch.wsort s.scratch.scratch_buf m
      hsok.work_stk1_len hok.repr_len hsok.wsort_len hsok.scratch_buf_len
      (List.Perm.refl _) (fun _ _ => rfl) hcov0 hm
  · by_cases hn32 : n.toNat < 32
    · exact sort_ana_ins_wp hlen hn_cv (by omega) hn32 hcov0 hm hQ
    · by_cases hcap : 512 ≤ c.scratch_cap
      · exact sort_ana_radix_wp hlen hn_cv (by omega) hcap hcov0 hm hQ
      · obtain hok := hlen.core_ok
        obtain hsok := hlen.scratch_ok
        have hmaxv : c.max_vars < 2 * Ref.dimacsBound := c.hmaxv
        have hscr_bd : c.scratch_cap < Ref.dimacsBound := c.hscr
        unfold Ref.dimacsBound at hmaxv hscr_bd
        have hcv_le := hok.cur_vars_le
        have hn_gt1_bv : ¬ (n ≤ 1#64) := by c0_bound
        have hn_le_cv : ¬ ((BitVec.ofNat 64 s.core.cur_vars) < n) := by c0_bound
        have hn_nlt32 : ¬ (n < 32#64) := by c0_bound
        have hcap_lt : ¬ (512#64 ≤ BitVec.ofNat 64 c.scratch_cap) := by
          change ¬ (512 ≤ (BitVec.ofNat 64 c.scratch_cap).toNat)
          rw [bv64_ofNat_toNat (by omega)]; exact hcap
        unfold Func.wp full_sort_ana_qs_m6_body
        dsimp only
        c0_hsteps_nogrp
        exact sort_ana_heap_wp hSift hlen hn_cv hn1 hcov0 hm hQ

end

end LeanQbe.T.Examples.Kissat.Proof.Bump
