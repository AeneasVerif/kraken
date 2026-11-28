/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Float64.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Walk.Helpers
public import LeanQbe.T.Examples.Kissat.Proof.Walk.Spec
public import LeanQbe.T.Examples.Kissat.Src.Walk

import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb

/-!
# Walk WP Proofs — Part 0 (`Proof.Walk.Wp0`)

Proves canonical WP correctness for the `5` leaf WalkSAT helpers in `Src.Walk`:
1. `full_walk_cb_inv_m7_wp` (`fullWalkCbInvM7Spec`)
2. `full_walk_effort_m7_wp` (`fullWalkEffortM7Spec`)
3. `full_walk_init_vals_m7_wp` (`fullWalkInitValsM7Spec`)
4. `full_walk_break_m7_wp` (`fullWalkBreakM7Spec`)
5. `full_walk_save_min_m7_wp` (`fullWalkSaveMinM7Spec`)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Walk

open Kraken.Bedrock2.Test
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Float64.Spec
open LeanQbe.T.Examples.Kissat.Proof.Walk.Spec
open LeanQbe.T.Examples.Kissat.Src.Walk

open scoped FullArenaTactics
open scoped WalkMemTactics

private theorem bv64_shl1_or1_lt {v : BitVec 64} (h : 2 * v.toNat + 1 < 2 ^ 64) :
    ((v <<< (1 : Nat)) ||| 1#64).toNat = 2 * v.toNat + 1 := by
  rw [BitVec.toNat_or, bv64_shl1_toNat_lt (by omega)]
  have h1 : (1#64 : BitVec 64).toNat = 1 := rfl
  rw [h1]
  apply Nat.eq_of_testBit_eq; intro k
  cases k with
  | zero => simp
  | succ k =>
    rw [Nat.testBit_or, Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ]
    simp [show (2 * v.toNat) / 2 = v.toNat by omega,
      show (2 * v.toNat + 1) / 2 = v.toNat by omega]

private theorem bv64_shr2_add1_lt {cv : BitVec 64} {mx : Nat} (hcv : cv.toNat ≤ mx)
    (hcv_pos : 0 < cv.toNat) (hmx : mx < 2 * dimacsBound) :
    ((cv >>> (2 : Nat)) + 1#64).toNat ≤ mx := by
  have hshr : (cv >>> (2 : Nat)).toNat = cv.toNat / 4 := by
    rw [BitVec.toNat_ushiftRight]; simp [Nat.shiftRight_eq_div_pow]
  unfold dimacsBound at hmx
  have hlt : (cv >>> (2 : Nat)).toNat + 1 < 2 ^ 64 := by omega
  rw [BitVec.toNat_add, show (1#64 : BitVec 64).toNat = 1 from rfl, Nat.mod_eq_of_lt hlt, hshr]
  omega

private theorem bv64_cb_join_chain {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    (hSub : Γ.Has "f64u_sub" f64uPure2Spec)
    (hMul : Γ.Has "f64u_mul" f64uPure2Spec)
    (hDiv : Γ.Has "f64u_div" f64uPure2Spec)
    (hAdd : Γ.Has "f64u_add" f64uPure2Spec)
    (sz : BitVec 64) (Jcb : Cont [i64])
    (hJcb : ∀ xs m1, m = m1 → Jcb xs m1) :
    wp Γ Q X
      (.group (sig := [[i64, i64, i64, i64]])
        (fun _ => Blocks.cons (fun (x0, x1, y0, y1, ()) =>
          .call (as := [i64, i64]) (bs := [i64]) "f64u_sub"
            (Arg.var x1, Arg.var x0, ()) fun (dx, ()) =>
          .call (as := [i64, i64]) (bs := [i64]) "f64u_sub"
            (Arg.var y1, Arg.var y0, ()) fun (dy, ()) =>
          .call (as := [i64, i64]) (bs := [i64]) "f64u_sub"
            (Arg.var sz, Arg.var x0, ()) fun (ds, ()) =>
          .call (as := [i64, i64]) (bs := [i64]) "f64u_mul"
            (Arg.var dy, Arg.var ds, ()) fun (num, ()) =>
          .call (as := [i64, i64]) (bs := [i64]) "f64u_div"
            (Arg.var num, Arg.var dx, ()) fun (q, ()) =>
          .call (as := [i64, i64]) (bs := [i64]) "f64u_add"
            (Arg.var q, Arg.var y0, ()) fun (cb, ()) =>
          .jump Jcb (Arg.var cb, ())) .nil)
        fun (Js, ()) =>
        .let_ (Op.mk (.cmp .ule i64 .bool rfl) (Arg.var sz, Arg.imm 4613937818241073152, ()))
          fun (p2, ()) =>
        .jnz (Arg.var p2)
          (.jump Js (Arg.imm 0, Arg.imm 4613937818241073152, Arg.imm 4611686018427387904,
            Arg.imm 4612811918334230528, ()))
          (.group (sig := [[i64, i64, i64, i64]])
            (fun _ => Blocks.cons (fun (a, b, c0, d, ()) =>
              .jump Js (Arg.var a, Arg.var b, Arg.var c0, Arg.var d, ())) .nil)
            fun (Js1, ()) =>
            .let_ (Op.mk (.cmp .ule i64 .bool rfl)
                (Arg.var sz, Arg.imm 4616189618054758400, ())) fun (p3, ()) =>
            .jnz (Arg.var p3)
              (.jump Js1 (Arg.imm 4613937818241073152, Arg.imm 4616189618054758400,
                Arg.imm 4612811918334230528, Arg.imm 4613600048269020365, ()))
              (.group (sig := [[i64, i64, i64, i64]])
                (fun _ => Blocks.cons (fun (a, b, c0, d, ()) =>
                  .jump Js1 (Arg.var a, Arg.var b, Arg.var c0, Arg.var d, ())) .nil)
                fun (Js2, ()) =>
                .let_ (Op.mk (.cmp .ule i64 .bool rfl)
                    (Arg.var sz, Arg.imm 4617315517961601024, ())) fun (p4, ()) =>
                .jnz (Arg.var p4)
                  (.jump Js2 (Arg.imm 4616189618054758400, Arg.imm 4617315517961601024,
                    Arg.imm 4613600048269020365, Arg.imm 4615514078110652826, ()))
                  (.group (sig := [[i64, i64, i64, i64]])
                    (fun _ => Blocks.cons (fun (a, b, c0, d, ()) =>
                      .jump Js2 (Arg.var a, Arg.var b, Arg.var c0, Arg.var d, ())) .nil)
                    fun (Js3, ()) =>
                    .let_ (Op.mk (.cmp .ule i64 .bool rfl)
                        (Arg.var sz, Arg.imm 4618441417868443648, ())) fun (p5, ()) =>
                    .jnz (Arg.var p5)
                      (.jump Js3 (Arg.imm 4617315517961601024, Arg.imm 4618441417868443648,
                        Arg.imm 4615514078110652826, Arg.imm 4617428107952285286, ()))
                      (.jump Js3 (Arg.imm 4618441417868443648, Arg.imm 4619567317775286272,
                        Arg.imm 4617428107952285286, Arg.imm 4620017677738023322, ())))))) m := by
  refine wp_join_group (ts := [i64, i64, i64, i64]) (fun _ m1 => m = m1) ?_ ?_
  · rintro _ ⟨x0, x1, y0, y1, ⟨⟩⟩ _ rfl
    rw [Blocks.get_here]; c0_hsteps_nogrp
    refine wp_call_of_spec _ _ (hSub _ _ _ _ fun _ => ?_); c0_hsteps_nogrp
    refine wp_call_of_spec _ _ (hSub _ _ _ _ fun _ => ?_); c0_hsteps_nogrp
    refine wp_call_of_spec _ _ (hSub _ _ _ _ fun _ => ?_); c0_hsteps_nogrp
    refine wp_call_of_spec _ _ (hMul _ _ _ _ fun _ => ?_); c0_hsteps_nogrp
    refine wp_call_of_spec _ _ (hDiv _ _ _ _ fun _ => ?_); c0_hsteps_nogrp
    refine wp_call_of_spec _ _ (hAdd _ _ _ _ fun _ => ?_); c0_hsteps
    exact hJcb _ _ rfl
  · intro J0 hJ0; c0_hsteps_nogrp
    · exact hJ0 _ _ rfl
    · refine wp_join_group (ts := [i64, i64, i64, i64]) (fun _ m1 => m = m1) ?_ ?_
      · rintro _ _ _ rfl; rw [Blocks.get_here]; c0_hsteps; exact hJ0 _ _ rfl
      · intro J1 hJ1; c0_hsteps_nogrp
        · exact hJ1 _ _ rfl
        · refine wp_join_group (ts := [i64, i64, i64, i64]) (fun _ m1 => m = m1) ?_ ?_
          · rintro _ _ _ rfl; rw [Blocks.get_here]; c0_hsteps; exact hJ1 _ _ rfl
          · intro J2 hJ2; c0_hsteps_nogrp
            · exact hJ2 _ _ rfl
            · refine wp_join_group (ts := [i64, i64, i64, i64]) (fun _ m1 => m = m1) ?_ ?_
              · rintro _ _ _ rfl; rw [Blocks.get_here]; c0_hsteps; exact hJ2 _ _ rfl
              · intro J3 hJ3; c0_hsteps_nogrp <;> exact hJ3 _ _ rfl

/-! ## 1. `full_walk_cb_inv_m7` -/

theorem full_walk_cb_inv_m7_wp (Γ : Env)
    (hAdd : Γ.Has "f64u_add" f64uPure2Spec)
    (hSub : Γ.Has "f64u_sub" f64uPure2Spec)
    (hMul : Γ.Has "f64u_mul" f64uPure2Spec)
    (hDiv : Γ.Has "f64u_div" f64uPure2Spec)
    (hFrom : Γ.Has "f64u_from_u64" f64uPure1Spec) :
    ∀ a m Q X, fullWalkCbInvM7Spec a m Q X → Func.wp Γ full_walk_cb_inv_m7_body a m Q X := by
  rintro ⟨h, ncl, tot_lits, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hlen hm hQ
  have hscr := c.hscr; unfold dimacsBound at hscr
  unfold Func.wp full_walk_cb_inv_m7_body
  c0_hsteps_nogrp
  · exact hQ (0#64, ()) s m rfl hlen ⟨⟨rfl, rfl⟩, fun hc => absurd rfl hc⟩ hm
  · exact hQ (0#64, ()) s m rfl hlen ⟨⟨rfl, rfl⟩, fun hc => absurd rfl hc⟩ hm
  · have h2208 : 2208 ≤ c.scratch_cap := by
      have hc1 : ¬ (c.scratch_cap < 2208) := by
        intro hlt
        have hc2 : (BitVec.ofNat 64 c.scratch_cap).toNat < (2208#64 : BitVec 64).toNat := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hlt
        c0_bound
      omega
    refine wp_join_group (ts := [i64]) (fun _ m1 => m = m1) ?_ ?_
    · rintro Jcb ⟨cb, ⟨⟩⟩ _ rfl
      rw [Blocks.get_here]; c0_hsteps_nogrp
      refine wp_call_of_spec _ _ (hDiv _ _ _ _ fun base => ?_)
      refine wp_loop_safety_slice (fullSafetySlice c) s R (fun _ => True) trivial
        (fun st (next, epsilon, i, ()) => FullExtScratchPres s st ∧ i.toNat ≤ 1080)
        (fun (_next, _epsilon, i, ()) => 1080 - i.toNat)
        ?_ ?_
      · intro Jl hJl; c0_hsteps
        exact hJl s (0x3FF0000000000000#64, 0x3FF0000000000000#64, 0#64, ()) m
          hm rfl hlen ⟨⟨rfl, rfl⟩, by simp⟩
      · rintro Jl st ⟨next, epsilon, i, ⟨⟩⟩ ml hcorel hlenl _ ⟨hextl, hil⟩ hml hJl
        rw [Blocks.get_here]; dsimp only [fullSafetySlice] at hcorel hlenl hml
        have hsb := hlenl.scratch_ok.scratch_buf_len
        refine wp_join_group (ts := []) (fun _ m1 => ml = m1) ?_ ?_
        · rintro Jx ⟨⟩ _ rfl
          rw [Blocks.get_here]
          have h2161 : (1080#64 * 8#64 : BitVec 64).toNat / 4 + 1 <
              st.scratch.scratch_buf.length := by
            rw [hsb]; have : (1080#64 * 8#64 : BitVec 64).toNat = 8640 := by decide
            omega
          have h2163 : (1081#64 * 8#64 : BitVec 64).toNat / 4 + 1 <
              st.scratch.scratch_buf.length := by
            rw [hsb]; have : (1081#64 * 8#64 : BitVec 64).toNat = 8648 := by decide
            omega
          have h2165 : (1082#64 * 8#64 : BitVec 64).toNat / 4 + 1 <
              st.scratch.scratch_buf.length := by
            rw [hsb]; have : (1082#64 * 8#64 : BitVec 64).toNat = 8656 := by decide
            omega
          c0_hsteps
          refine hQ (i, ()) _ _ ?_ ?_ ?_ hm
          · exact hcorel
          · exact ⟨hlenl.core_ok, { hlenl.scratch_ok with scratch_buf_len := by simp [hsb] }⟩
          · refine ⟨⟨hextl.1, hextl.2⟩, fun _ => ?_⟩
            exact walkTblExpsOk_cb_tbl rfl (by decide) (by decide) (by decide)
              (by rw [hsb]; omega) (by rw [pack64_lo_hi]; exact hil)
        · intro Jx hJx; c0_hsteps_nogrp
          · c0_hsteps_nogrp
            · have hi_lt : i.toNat < 1080 := by c0_bound
              have hi_arr : 2 * i.toNat + 1 < st.scratch.scratch_buf.length := by
                rw [hsb]; omega
              c0_hsteps_nogrp
              refine wp_call_of_spec _ _ (hMul _ _ _ _ fun next' => ?_)
              c0_hsteps
              dsimp only [fullSafetySlice] at hJl
              refine hJl _ (next', next, i + 1#64, ()) _ hm ?_ rfl ?_ ?_
              · dsimp only; have h1 : (i + 1#64).toNat = i.toNat + 1 := by bv_omega
                rw [h1]; omega
              · exact ⟨hlenl.core_ok, { hlenl.scratch_ok with scratch_buf_len := by simp [hsb] }⟩
              · exact ⟨⟨hextl.1, hextl.2⟩, by
                  have h1 : (i + 1#64).toNat = i.toNat + 1 := by bv_omega
                  rw [h1]; omega⟩
          · exact hJx () ml rfl
          · exact hJx () ml rfl
    · intro Jcb hJcb; c0_hsteps_nogrp
      · refine wp_call_of_spec _ _ (hFrom _ _ _ _ fun _ftot => ?_); c0_hsteps_nogrp
        refine wp_call_of_spec _ _ (hFrom _ _ _ _ fun _fncl => ?_); c0_hsteps_nogrp
        refine wp_call_of_spec _ _ (hDiv _ _ _ _ fun sz => ?_); c0_hsteps_nogrp
        exact bv64_cb_join_chain hSub hMul hDiv hAdd sz Jcb hJcb
      · exact hJcb _ _ rfl

/-! ## 2. `full_walk_effort_m7` -/

theorem full_walk_effort_m7_wp (Γ : Env) :
    ∀ a m Q X, fullWalkEffortM7Spec a m Q X → Func.wp Γ full_walk_effort_m7_body a m Q X := by
  rintro ⟨h, mf, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hlen hm hQ
  unfold Func.wp full_walk_effort_m7_body
  c0_hsteps_nogrp
  refine wp_join_group (ts := [i64]) (fun _ m1 => m = m1) ?_ ?_
  · rintro Jdt ⟨dt, ⟨⟩⟩ _ rfl
    rw [Blocks.get_here]; c0_hsteps_nogrp
    refine wp_join_group (ts := [i64]) (fun _ m1 => m = m1) ?_ ?_
    · rintro Jdt2 ⟨dt2, ⟨⟩⟩ _ rfl
      rw [Blocks.get_here]; c0_hsteps
      exact hQ _ s m rfl hlen rfl hm
    · intro Jdt2 hJdt2; c0_hsteps_nogrp <;> exact hJdt2 _ _ rfl
  · intro Jdt hJdt; c0_hsteps_nogrp <;> exact hJdt _ _ rfl

/-! ## 3. `full_walk_init_vals_m7` -/

theorem full_walk_init_vals_m7_wp (Γ : Env) :
    ∀ a m Q X, fullWalkInitValsM7Spec a m Q X →
      Func.wp Γ full_walk_init_vals_m7_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hlen hm hQ
  unfold Func.wp full_walk_init_vals_m7_body
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  c0_hsteps_nogrp
  refine wp_join_group (ts := [i64])
    (fun (cv, ()) m0 => m = m0 ∧ cv.toNat ≤ c.max_vars) ?_ ?_
  · rintro Jcv ⟨cv, ⟨⟩⟩ _ ⟨rfl, hcv_le⟩
    rw [Blocks.get_here]; c0_hsteps_nogrp
    refine wp_loop_safety_slice (ts := [i64]) (fullSafetySlice c) s R (fun _ => True) trivial
      (fun st (v, ()) => FullExtScratchPres s st ∧ v.toNat ≤ cv.toNat)
      (fun (v, ()) => cv.toNat - v.toNat) ?_ ?_
    · intro Jv hJv; c0_hsteps
      exact hJv s (0#64, ()) m hm rfl hlen ⟨⟨rfl, rfl⟩, by simp⟩
    · rintro Jv st ⟨v, ⟨⟩⟩ ml hcorev hlenv _ ⟨hextv, hvle⟩ hml hJv
      rw [Blocks.get_here]; dsimp only [fullSafetySlice] at hcorev hlenv hml
      have hv_len := hlenv.core_ok.vals_len
      have hfl_len := hlenv.core_ok.flags_len
      have hph_len := hlenv.scratch_ok.phases_len
      have hpt_len := hlenv.scratch_ok.phases_target_len
      have hwv_len := hlenv.scratch_ok.walk_vals_len
      have hwb_len := hlenv.scratch_ok.walk_best_len
      c0_hsteps_nogrp
      · have hv_lt : v.toNat < cv.toNat := by c0_bound
        have hv2_lt : (v <<< (1 : Nat)).toNat < st.core.vals.length := by
          rw [hv_len, bv64_shl1_toNat_lt (by omega)]; omega
        c0_hsteps_nogrp
        refine wp_join_safety_slice (ts := [i8]) (fullSafetySlice c) st R
          (fun _ => True) trivial (fun st1 _ => st1 = st) ?_ ?_
        · rintro Jp st1 ⟨p, ⟨⟩⟩ m1 _ hlen1 _ heq hm1
          subst st1; rw [Blocks.get_here]; dsimp only [fullSafetySlice] at hlen1 hm1
          have hv2w_lt : (v <<< (1 : Nat)).toNat < st.scratch.walk_vals.length := by
            rw [hwv_len, bv64_shl1_toNat_lt (by omega)]; omega
          c0_hsteps_nogrp
          let st' : FullState :=
            { st with scratch := { st.scratch with
              walk_vals := st.scratch.walk_vals.set (v <<< (1 : Nat)).toNat p } }
          have hst'_wv : st'.scratch.walk_vals.length = 2 * c.max_vars := by simp [st', hwv_len]
          have hst'_wb : st'.scratch.walk_best.length = c.max_vars := by simp [st', hwb_len]
          have hst'_len : FullState.LengthsOk c st' :=
            ⟨hlen1.core_ok, { hlen1.scratch_ok with walk_vals_len := hst'_wv }⟩
          refine wp_join_safety_slice (ts := [i32]) (fullSafetySlice c) st' R
            (fun _ => True) trivial (fun st2 _ => st2 = st') ?_ ?_
          · rintro Jn st2 ⟨nv, ⟨⟩⟩ m2 _ hlen2 _ heq2 hm2
            subst st2; rw [Blocks.get_here]; dsimp only [fullSafetySlice] at hlen2 hm2
            have hv2o_lt : ((v <<< (1 : Nat)) ||| 1#64).toNat < st'.scratch.walk_vals.length := by
              rw [hst'_wv, bv64_shl1_or1_lt (by omega)]; omega
            have hwb_lt : v.toNat < st'.scratch.walk_best.length := by rw [hst'_wb]; omega
            c0_hsteps
            dsimp only [fullSafetySlice] at hJv
            refine hJv _ (v + 1#64, ()) _ hm ?_ ?_ ?_ ?_
            · dsimp only; have h1 : (v + 1#64).toNat = v.toNat + 1 := by bv_omega
              rw [h1]; omega
            · rfl
            · exact ⟨hlen2.core_ok, { hlen2.scratch_ok with
                walk_vals_len := by simp [hst'_wv]
                walk_best_len := by simp [hst'_wb] }⟩
            · have h1 : (v + 1#64).toNat = v.toNat + 1 := by bv_omega
              exact ⟨hextv, by rw [h1]; omega⟩
          · intro Jn hJn
            c0_hsteps_nogrp <;> exact hJn st' (_, ()) m hm rfl hst'_len rfl
        · intro Jp hJp; c0_hsteps_nogrp
          · exact hJp st (_, ()) _ hml rfl hlenv rfl
          · have hvf : v.toNat < st.core.flags.length := by rw [hfl_len]; omega
            have hvph : v.toNat < st.scratch.phases.length := by rw [hph_len]; omega
            have hvpt : v.toNat < st.scratch.phases_target.length := by rw [hpt_len]; omega
            c0_hsteps_nogrp
            refine wp_join_group (ts := [i8]) (fun _ m1 => ml = m1) ?_ ?_
            · rintro Jfl ⟨p2, ⟨⟩⟩ _ rfl; rw [Blocks.get_here]
              exact hJp st (p2, ()) ml hml rfl hlenv rfl
            · intro Jfl hJfl; c0_hsteps_nogrp
              · refine wp_join_group (ts := [i8]) (fun _ m1 => ml = m1) ?_ ?_
                · rintro Jpt ⟨p3, ⟨⟩⟩ _ rfl; rw [Blocks.get_here]
                  refine wp_join_group (ts := [i8]) (fun _ m1 => ml = m1) ?_ ?_
                  · rintro Jnz ⟨p4, ⟨⟩⟩ _ rfl; rw [Blocks.get_here]
                    exact hJfl (p4, ()) ml rfl
                  · intro Jnz hJnz; c0_hsteps_nogrp <;> exact hJnz _ ml rfl
                · intro Jpt hJpt; c0_hsteps_nogrp <;> exact hJpt _ ml rfl
              · exact hJfl (1#8, ()) ml rfl
      · have h2cv : (cv <<< (1 : Nat)).toNat = 2 * cv.toNat := bv64_shl1_toNat_lt (by omega)
        refine wp_loop_safety_slice (ts := [i64]) (fullSafetySlice c) st R (fun _ => True) trivial
          (fun st1 (l, ()) => FullExtScratchPres s st1 ∧ l.toNat ≤ 2 * cv.toNat)
          (fun (l, ()) => 2 * cv.toNat - l.toNat) ?_ ?_
        · intro Jl hJl; c0_hsteps
          exact hJl st (0#64, ()) ml hml rfl hlenv ⟨hextv, by simp⟩
        · rintro Jl st1 ⟨l, ⟨⟩⟩ m1 hcore1 hlen1 _ ⟨hext1, hle1⟩ hm1 hJl
          rw [Blocks.get_here]; dsimp only [fullSafetySlice] at hcore1 hlen1 hm1 hJl
          have htrc1 := hlen1.scratch_ok.tarjan_reach_len
          c0_hsteps_nogrp
          · have hl_lt : l.toNat < 2 * cv.toNat := by
              have hc : l.toNat < (cv <<< (1 : Nat)).toNat := by c0_bound
              omega
            have hl_trc : l.toNat < st1.scratch.tarjan_reach.length := by rw [htrc1]; omega
            c0_hsteps
            refine hJl _ (l + 1#64, ()) _ hm ?_ ?_ ?_ ?_
            · dsimp only; have h1 : (l + 1#64).toNat = l.toNat + 1 := by bv_omega
              rw [h1]; omega
            · rfl
            · exact ⟨hlen1.core_ok, { hlen1.scratch_ok with tarjan_reach_len := by simp [htrc1] }⟩
            · have h1 : (l + 1#64).toNat = l.toNat + 1 := by bv_omega
              exact ⟨hext1, by rw [h1]; omega⟩
          · exact hQ () st1 m1 (hcorev.trans hcore1) hlen1 hext1 hm1
  · intro Jcv hJcv; c0_hsteps_nogrp
    · exact hJcv (_, ()) m ⟨rfl, by
        have hlt : c.max_vars < 2 ^ 64 := by omega
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]; exact Nat.le_refl _⟩
    · exact hJcv (_, ()) m ⟨rfl, by c0_bound⟩

/-! ## 4. `full_walk_break_m7` -/

theorem full_walk_break_m7_wp (Γ : Env) :
    ∀ a m Q X, fullWalkBreakM7Spec a m Q X → Func.wp Γ full_walk_break_m7_body a m Q X := by
  rintro ⟨h, not_lit, ncl, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hlen hm hQ
  have hmaxv := c.hmaxv; have hscr := c.hscr; unfold dimacsBound at hmaxv hscr
  have hcv := hlen.core_ok.cur_vars_le
  have htmk := hlen.scratch_ok.tarjan_mark_len
  have htrc := hlen.scratch_ok.tarjan_reach_len
  have hsb := hlen.scratch_ok.scratch_buf_len
  unfold Func.wp full_walk_break_m7_body
  c0_hsteps_nogrp
  · exact hQ (0#32, ()) s m rfl hlen rfl hm
  · exact hQ (0#32, ()) s m rfl hlen rfl hm
  · exact hQ (0#32, ()) s m rfl hlen rfl hm
  · exact hQ (0#32, ()) s m rfl hlen rfl hm
  · exact hQ (0#32, ()) s m rfl hlen rfl hm
  · have hnl_lt : not_lit.toNat < 2 * c.max_vars := by
      have hcv_lt : s.core.cur_vars < 2 ^ 64 := by omega
      have hshl : (BitVec.ofNat 64 s.core.cur_vars <<< (1 : Nat)).toNat = 2 * s.core.cur_vars := by
        rw [bv64_shl1_toNat_lt (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcv_lt]; omega),
          BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcv_lt]
      have hc1 : not_lit.toNat < 2 * s.core.cur_vars := by
        rw [← hshl, ← bv32_lit_toNat_mod64]
        have hc2 : ¬ (BitVec.ofNat 64 s.core.cur_vars <<< (1 : Nat)).toNat ≤
            (not_lit.setWidth 64).toNat := by c0_bound
        omega
      omega
    have hncl_le : ncl.toNat ≤ c.scratch_cap := by c0_bound
    have h5ncl_le : 2200 + 5 * ncl.toNat ≤ c.scratch_cap := by
      have hbd : (2200#64 + 5#64 * ncl).toNat = 2200 + 5 * ncl.toNat := by bv_omega
      have hc1 : ¬ (BitVec.ofNat 64 c.scratch_cap).toNat <
          (2200#64 + 5#64 * ncl).toNat := by c0_bound
      rw [hbd, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hc1; omega
    have hocc_eq : (2200#64 + 5#64 * ncl).toNat = 2200 + 5 * ncl.toNat := by bv_omega
    have hsub1_eq : (BitVec.ofNat 64 c.scratch_cap - (2200#64 + 5#64 * ncl)).toNat =
        c.scratch_cap - (2200 + 5 * ncl.toNat) := by
      have hcap_lt : c.scratch_cap < 2 ^ 64 := by omega
      rw [BitVec.toNat_sub, hocc_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcap_lt]
      have hsub_add : 2 ^ 64 - (2200 + 5 * ncl.toNat) + c.scratch_cap =
          2 ^ 64 + (c.scratch_cap - (2200 + 5 * ncl.toNat)) := by omega
      rw [hsub_add, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    have hoff_le : (s.scratch.tarjan_mark[not_lit.toNat]'(by omega)).toNat ≤
        c.scratch_cap - (2200 + 5 * ncl.toNat) := by
      have hc1 : ¬ (BitVec.ofNat 64 c.scratch_cap - (2200#64 + 5#64 * ncl)).toNat <
          (s.scratch.tarjan_mark[not_lit.toNat]'(by omega)).toNat := by
        have := bv32_lit_toNat_mod64 (s.scratch.tarjan_mark[not_lit.toNat]'(by omega))
        c0_bound
      rw [hsub1_eq] at hc1; exact Nat.le_of_not_lt hc1
    refine wp_join_group (ts := [i64]) (fun (len, ()) m0 => m = m0 ∧
        len.toNat ≤ c.scratch_cap - (2200 + 5 * ncl.toNat) -
          (s.scratch.tarjan_mark[not_lit.toNat]'(by omega)).toNat) ?_ ?_
    · rintro Jlen ⟨len, ⟨⟩⟩ _ ⟨rfl, hlen_bd⟩
      rw [Blocks.get_here]
      refine wp_loop_safety_slice (fullSafetySlice c) s R (fun _ => True) trivial
        (fun st (k, brk, ()) => st = s ∧ k.toNat ≤ len.toNat)
        (fun (k, _brk, ()) => len.toNat - k.toNat) ?_ ?_
      · intro Jk hJk; c0_hsteps
        exact hJk s (0#64, 0#32, ()) m hm rfl hlen ⟨rfl, by simp⟩
      · rintro Jk st ⟨k, brk, ⟨⟩⟩ mk hcorek hlenk _ ⟨hst, hk_le⟩ hmk hJk
        subst st; rw [Blocks.get_here]; dsimp only [fullSafetySlice] at hcorek hlenk hmk
        c0_hsteps_nogrp
        · have hk_lt : k.toNat < len.toNat := by c0_bound
          have htmk_lt : not_lit.toNat < s.scratch.tarjan_mark.length := by omega
          have hz_tm := bv32_lit_toNat_mod64 (s.scratch.tarjan_mark[not_lit.toNat]'htmk_lt)
          have hocc_bv : (2200#64 + 5#64 * ncl +
              (s.scratch.tarjan_mark[not_lit.toNat]'htmk_lt).setWidth 64 + k).toNat =
              2200 + 5 * ncl.toNat +
                (s.scratch.tarjan_mark[not_lit.toNat]'htmk_lt).toNat + k.toNat := by
            bv_omega
          have hocc_lt : (2200#64 + 5#64 * ncl +
              (s.scratch.tarjan_mark[not_lit.toNat]'htmk_lt).setWidth 64 + k).toNat <
              s.scratch.scratch_buf.length := by
            rw [hsb, hocc_bv]; omega
          c0_hsteps_nogrp
          refine wp_join_safety_slice (ts := [i32]) (fullSafetySlice c) s R
            (fun _ => True) trivial (fun st1 _ => st1 = s) ?_ ?_
          · rintro Jb st1 ⟨brk1, ⟨⟩⟩ m1 _ _ _ heq1 hm1
            subst st1; rw [Blocks.get_here]; c0_hsteps
            have hk1 : (k + 1#64).toNat = k.toNat + 1 := by bv_omega
            exact hJk s (k + 1#64, brk1, ()) m1 hm1 (by dsimp only; rw [hk1]; omega)
              rfl hlen ⟨rfl, by rw [hk1]; omega⟩
          · intro Jb hJb; c0_hsteps_nogrp
            · let cidx : BitVec 32 := s.scratch.scratch_buf[(2200#64 + 5#64 * ncl +
                (s.scratch.tarjan_mark[not_lit.toNat]'htmk_lt).setWidth 64 +
                k).toNat]'hocc_lt
              have hc_lt : cidx.toNat < ncl.toNat := by
                have hmod : (BitVec.toNat (2200 : BitVec 64) +
                    BitVec.toNat (5 : BitVec 64) * ncl.toNat +
                    (s.scratch.tarjan_mark[not_lit.toNat]'htmk_lt).toNat + k.toNat) % 2 ^ 64 =
                    (2200#64 + 5#64 * ncl +
                      (s.scratch.tarjan_mark[not_lit.toNat]'htmk_lt).setWidth 64 + k).toNat := by
                  rw [hocc_bv]
                  change (2200 + 5 * ncl.toNat +
                      (s.scratch.tarjan_mark[not_lit.toNat]'htmk_lt).toNat + k.toNat) % 2 ^ 64 = _
                  exact Nat.mod_eq_of_lt (by omega)
                dsimp only [cidx]; simp only [hmod] at hc; exact hc
              have hsat_lt : (2200#64 + (ncl <<< (1 : Nat)) + cidx.setWidth 64).toNat <
                  s.scratch.scratch_buf.length := by
                have hz := bv32_lit_toNat_mod64 cidx
                have hshl1 : (ncl <<< (1 : Nat)).toNat = 2 * ncl.toNat :=
                  bv64_shl1_toNat_lt (by omega)
                have hbv : (2200#64 + (ncl <<< (1 : Nat)) + cidx.setWidth 64).toNat =
                    2200 + 2 * ncl.toNat + cidx.toNat := by
                  bv_omega
                rw [hsb, hbv]; omega
              c0_hsteps_nogrp <;> exact hJb s (_, ()) mk hmk rfl hlenk rfl
            · exact hJb s (_, ()) mk hmk rfl hlenk rfl
        · exact hQ (brk, ()) s mk rfl hlen rfl hmk
    · intro Jlen hJlen; c0_hsteps_nogrp
      · refine hJlen _ _ ⟨rfl, ?_⟩
        have hz_nl := bv32_lit_toNat_mod64 not_lit
        have hz_tm := bv32_lit_toNat_mod64 (s.scratch.tarjan_mark[not_lit.toNat]'(by omega))
        simp only [hz_nl]
        bv_omega
      · refine hJlen _ _ ⟨rfl, ?_⟩
        have hz_nl := bv32_lit_toNat_mod64 not_lit
        have hz_tm := bv32_lit_toNat_mod64 (s.scratch.tarjan_mark[not_lit.toNat]'(by omega))
        have hz := bv32_lit_toNat_mod64 (s.scratch.tarjan_reach[not_lit.toNat]'(by omega))
        simp only [hz_nl] at *
        bv_omega

/-! ## 5. `full_walk_save_min_m7` -/

theorem full_walk_save_min_m7_wp (Γ : Env) :
    ∀ a m Q X, fullWalkSaveMinM7Spec a m Q X →
      Func.wp Γ full_walk_save_min_m7_body a m Q X := by
  rintro ⟨h, best_pos, trail_ok, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hlen hm hQ
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  unfold Func.wp full_walk_save_min_m7_body
  c0_hsteps_nogrp
  · exact hQ () s m rfl hlen ⟨rfl, rfl⟩ hm
  · exact hQ () s m rfl hlen ⟨rfl, rfl⟩ hm
  · have hcv_pos : 0 < s.core.cur_vars := by
      have hcv_lt : s.core.cur_vars < 2 ^ 64 := by
        have := hlen.core_ok.cur_vars_le; omega
      have hne : BitVec.ofNat 64 s.core.cur_vars ≠ 0#64 := by c0_bound
      exact Nat.pos_of_ne_zero fun h0 => hne (by simp [h0])
    have hcv_le : s.core.cur_vars ≤ c.max_vars := by
      have := hlen.core_ok.cur_vars_le; exact this
    have hlim_le : ((BitVec.ofNat 64 s.core.cur_vars >>> (2 : Nat)) + 1#64).toNat ≤
        c.max_vars := by
      have hcv_lt : s.core.cur_vars < 2 ^ 64 := by
        have := hlen.core_ok.cur_vars_le; omega
      refine bv64_shr2_add1_lt ?_ ?_ c.hmaxv
      · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcv_lt]; exact hcv_le
      · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcv_lt]; exact hcv_pos
    refine wp_join_safety_slice (ts := []) (fullSafetySlice c) s R (fun _ => True) trivial
      (fun st _ => FullExtScratchPres s st) ?_ ?_
    · rintro Jf st ⟨⟩ mf hcoref hlenf _ hextf hmf
      rw [Blocks.get_here]; dsimp only [fullSafetySlice] at hcoref hlenf hmf
      refine wp_loop_safety_slice (fullSafetySlice c) st R (fun _ => True) trivial
        (fun st1 (v, ()) => FullExtScratchPres s st1 ∧ v.toNat ≤ s.core.cur_vars)
        (fun (v, ()) => s.core.cur_vars - v.toNat) ?_ ?_
      · intro Jv hJv; c0_hsteps
        exact hJv st (0#64, ()) mf hmf rfl hlenf ⟨hextf, by simp⟩
      · rintro Jv st1 ⟨v, ⟨⟩⟩ m1 hcore1 hlen1 _ ⟨hext1, hvle⟩ hm1 hJv
        rw [Blocks.get_here]; dsimp only [fullSafetySlice] at hcore1 hlen1 hm1 hJv
        have hv_len := hlen1.core_ok.vals_len
        have hfl_len := hlen1.core_ok.flags_len
        have hwb_len := hlen1.scratch_ok.walk_best_len
        have hph_len := hlen1.scratch_ok.phases_len
        c0_hsteps_nogrp
        · have hv_lt : v.toNat < s.core.cur_vars := by c0_bound
          have hv2_lt : (v <<< (1 : Nat)).toNat < st1.core.vals.length := by
            rw [hv_len, bv64_shl1_toNat_lt (by omega)]; omega
          refine wp_join_safety_slice (ts := []) (fullSafetySlice c) st1 R
            (fun _ => True) trivial (fun st2 _ => FullExtScratchPres s st2) ?_ ?_
          · rintro Js st2 ⟨⟩ m2 hcore2 hlen2 _ hext2 hm2
            rw [Blocks.get_here]; dsimp only [fullSafetySlice] at hcore2 hlen2 hm2
            c0_hsteps; exact hJv st2 (v + 1#64, ()) m2 hm2 (by
              dsimp only; have h1 : (v + 1#64).toNat = v.toNat + 1 := by bv_omega
              rw [h1]; omega)
              hcore2 hlen2 ⟨hext2, by
                have h1 : (v + 1#64).toNat = v.toNat + 1 := by bv_omega
                rw [h1]; omega⟩
          · intro Js hJs; c0_hsteps_nogrp
            · have hwb_lt : v.toNat < st1.scratch.walk_best.length := by rw [hwb_len]; omega
              c0_hsteps_nogrp
              refine wp_join_safety_slice (ts := []) (fullSafetySlice c) st1 R
                (fun _ => True) trivial (fun st2 _ => FullExtScratchPres s st2) ?_ ?_
              · rintro Jp st2 ⟨⟩ m2 hcore2 hlen2 _ hext2 hm2
                rw [Blocks.get_here]; exact hJs st2 () m2 hm2 hcore2 hlen2 hext2
              · intro Jp hJp; c0_hsteps_nogrp
                · have hph_lt : v.toNat < st1.scratch.phases.length := by
                    rw [hph_len]; omega
                  c0_hsteps
                  dsimp only [fullSafetySlice] at hJp
                  refine hJp _ () _ hm ?_ ?_ ?_
                  · rfl
                  · exact ⟨hlen1.core_ok, { hlen1.scratch_ok with
                      phases_len := by simp [hph_len] }⟩
                  · exact hext1
                · exact hJp st1 () m1 hm1 rfl hlen1 hext1
            · exact hJs st1 () m1 hm1 rfl hlen1 hext1
            · exact hJs st1 () m1 hm1 rfl hlen1 hext1
        · exact hQ () st1 m1 (hcoref.trans hcore1) hlen1 hext1 hm1
    · intro Jf hJf; c0_hsteps_nogrp
      · refine wp_join_group (ts := [i64])
          (fun (lim, ()) m0 => m = m0 ∧ lim.toNat ≤ c.max_vars) ?_ ?_
        · rintro Jlim ⟨lim, ⟨⟩⟩ _ ⟨rfl, hlim_le⟩
          rw [Blocks.get_here]
          refine wp_loop_safety_slice (fullSafetySlice c) s R (fun _ => True) trivial
            (fun st1 (k, ()) => FullExtScratchPres s st1 ∧ k.toNat ≤ lim.toNat)
            (fun (k, ()) => lim.toNat - k.toNat) ?_ ?_
          · intro Jk hJk; c0_hsteps
            exact hJk s (0#64, ()) m hm rfl hlen ⟨⟨rfl, rfl⟩, by simp⟩
          · rintro Jk st1 ⟨k, ⟨⟩⟩ m1 hcore1 hlen1 _ ⟨hext1, hk_le⟩ hm1 hJk
            rw [Blocks.get_here]; dsimp only [fullSafetySlice] at hcore1 hlen1 hm1
            have hws_len := hlen1.scratch_ok.wsort_len
            have hwb_len := hlen1.scratch_ok.walk_best_len
            c0_hsteps_nogrp
            · have hk_lt : k.toNat < lim.toNat := by c0_bound
              have hk_ws : k.toNat < st1.scratch.wsort.length := by rw [hws_len]; omega
              refine wp_join_safety_slice (ts := []) (fullSafetySlice c) st1 R
                (fun _ => True) trivial (fun st2 _ => FullExtScratchPres s st2) ?_ ?_
              · rintro Jb st2 ⟨⟩ m2 hcore2 hlen2 _ hext2 hm2
                rw [Blocks.get_here]; dsimp only [fullSafetySlice] at hcore2 hlen2 hm2
                c0_hsteps; exact hJk st2 (k + 1#64, ()) m2 hm2 (by
                  dsimp only; have h1 : (k + 1#64).toNat = k.toNat + 1 := by bv_omega
                  rw [h1]; omega) hcore2 hlen2 ⟨hext2, by
                    have h1 : (k + 1#64).toNat = k.toNat + 1 := by bv_omega
                    rw [h1]; omega⟩
              · intro Jb hJb; c0_hsteps_nogrp
                · have hbv_lt : (st1.scratch.wsort[k.toNat]'hk_ws).toNat <
                      st1.scratch.walk_best.length := by
                    have hcv_lt : s.core.cur_vars < 2 ^ 64 := by omega
                    have hz := bv32_lit_toNat_mod64 (st1.scratch.wsort[k.toNat]'hk_ws)
                    have hc : ((st1.scratch.wsort[k.toNat]'hk_ws).setWidth 64).toNat <
                        (BitVec.ofNat 64 s.core.cur_vars).toNat := by c0_bound
                    rw [hz, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcv_lt] at hc
                    rw [hwb_len]; omega
                  c0_hsteps_nogrp
                  refine wp_join_safety_slice (ts := [i32]) (fullSafetySlice c) st1 R
                    (fun _ => True) trivial (fun st2 _ => FullExtScratchPres s st2) ?_ ?_
                  · rintro Jnv st2 ⟨nv, ⟨⟩⟩ m2 hcore2 hlen2 _ hext2 hm2
                    rw [Blocks.get_here]; dsimp only [fullSafetySlice] at hcore2 hlen2 hm2
                    have hwb2 := hlen2.scratch_ok.walk_best_len
                    c0_hsteps
                    dsimp only [fullSafetySlice] at hJb
                    refine hJb _ () _ hm ?_ ?_ ?_
                    · exact hcore2
                    · exact ⟨hlen2.core_ok, { hlen2.scratch_ok with
                        walk_best_len := by simp [hwb2] }⟩
                    · exact hext2
                  · intro Jnv hJnv
                    c0_hsteps_nogrp <;> exact hJnv st1 (_, ()) m1 hm1 rfl hlen1 hext1
                · exact hJb st1 () m1 hm1 rfl hlen1 hext1
            · exact hJf st1 () m1 hm1 hcore1 hlen1 hext1
        · intro Jlim hJlim; c0_hsteps_nogrp
          · exact hJlim _ _ ⟨rfl, hlim_le⟩
          · exact hJlim _ _ ⟨rfl, by
              have hcv_lt : s.core.cur_vars < 2 ^ 64 := by
                have := hlen.core_ok.cur_vars_le; omega
              have hshr : (BitVec.ofNat 64 s.core.cur_vars >>> (2 : Nat)).toNat + 1 < 2 ^ 64 := by
                rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcv_lt]
                simp [Nat.shiftRight_eq_div_pow]; omega
              have hbp : best_pos.toNat ≤
                  ((BitVec.ofNat 64 s.core.cur_vars >>> (2 : Nat)).toNat + 1) % 2 ^ 64 :=
                Nat.le_of_not_lt ‹¬ _ < best_pos.toNat›
              rw [Nat.mod_eq_of_lt hshr] at hbp
              rw [BitVec.toNat_add, show (1#64 : BitVec 64).toNat = 1 from rfl,
                Nat.mod_eq_of_lt hshr] at hlim_le
              exact Nat.le_trans hbp hlim_le⟩
      · exact hJf s () m hm rfl hlen ⟨rfl, rfl⟩
      · exact hJf s () m hm rfl hlen ⟨rfl, rfl⟩

end LeanQbe.T.Examples.Kissat.Proof.Walk
