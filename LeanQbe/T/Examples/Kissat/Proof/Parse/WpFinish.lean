/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Parse.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics1
public import LeanQbe.T.Examples.Kissat.Src.Parse

/-!
# Soundness Proof for `full_tumble_finish_fid` (`Proof.Parse.WpFinish`)

Proves `full_tumble_finish_fid_wp` (`Src.Parse.full_tumble_finish_fid_body`) against
canonical `Spec.fullTumbleFinishFidSpec`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Parse

open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Parse.Spec
open LeanQbe.T.Examples.Kissat.Src.Parse
open Kraken.Bedrock2.Test
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics

/-- `full_tumble_finish_fid` satisfies canonical `Spec.fullTumbleFinishFidSpec`. -/
theorem full_tumble_finish_fid_wp (Γ : Env) :
    ∀ a m Q X, fullTumbleFinishFidSpec a m Q X →
      Func.wp Γ full_tumble_finish_fid_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m0 Q X ⟨c, s, R, rfl, hlen, hcl0, hm0, hQ⟩
  have hmv := c.hmv; have hext := c.hext; have hbva := c.hbva
  unfold dimacsBound at hmv hext
  have hfll := hlen.core_ok.frame_dec_len
  have hesl := hlen.scratch_ok.extend_stk_len
  unfold Func.wp full_tumble_finish_fid_body
  c0_hsteps_nogrp
  · have hno : ¬ c.mv < c.extend_cap := by c0_bound
    exact hQ s.core.frame_dec s.scratch.extend_stk s.scratch.extend_len m0
      hlen (fun h => absurd h hno) (fun _ => rfl) hm0
  have htum : c.mv < c.extend_cap := by c0_bound
  c0_hsteps_nogrp
  refine wp_loop_inv (ts := [i64])
    (fun (e, ()) m1 => ∃ fd1 ext1 : List (BitVec 32),
      e.toNat ≤ c.mv ∧ fd1.length = c.max_vars + 1 ∧ ext1.length = c.extend_cap ∧
      (FullMem c { core := { s.core with frame_dec := fd1 }
                   scratch := { s.scratch with extend_stk := ext1 } } ⋆ R) m1)
    (fun (e, ()) _ => c.mv - e.toNat)
    (fun J hJ => by
      c0_hsteps
      exact hJ (0#64, ()) m0
        ⟨s.core.frame_dec, s.scratch.extend_stk, Nat.zero_le _, hfll, hesl, hm0⟩)
    (fun J ⟨e, ⟨⟩⟩ m1 ⟨fd1, ext1, he_le, hfdl1, hesl1, hm1⟩ ih => ?_)
  c0_hsplit
  · have he_lt : e.toNat < c.mv := by c0_bound
    have he_fd : e.toNat < fd1.length := by omega
    have he1_eq : (e + 1#64).toNat = e.toNat + 1 := by bv_omega
    have he1_ext_nat : e.toNat + 1 < ext1.length := by omega
    have he1_ext : (e + 1#64).toNat < ext1.length := by rw [he1_eq]; exact he1_ext_nat
    c0_hsteps_nogrp
    refine wp_join_group (ts := [i32]) (fun _ m2 => m2 = m1) ?_
      (fun Jv hJv => by
        c0_hsplit
        · c0_hsteps; exact hJv _ m1 rfl
        · c0_hsteps; exact hJv _ m1 rfl)
    rintro _ ⟨ev_val, ⟨⟩⟩ m2 rfl
    have he_fd2 : e.toNat <
        ({ core := { s.core with frame_dec := fd1 }
           scratch := { s.scratch with extend_stk := ext1.set (e + 1#64).toNat ev_val } } :
          FullState).core.frame_dec.length := by dsimp only; exact he_fd
    c0_hsteps
    refine ih (e + 1#64, ()) _ (by dsimp only; omega)
      ⟨fd1.set e.toNat 0xFFFFFFFF#32, ext1.set (e.toNat + 1) ev_val,
       by rw [he1_eq]; omega, by simp [hfdl1], by simp [hesl1], ?_⟩
    rw [← he1_eq]; assumption
  · have h0_ext : (0 : Nat) < ext1.length := by omega
    have hmv1_eq : (BitVec.ofNat 64 c.mv + 1#64).toNat = c.mv + 1 := by bv_omega
    let v0 : BitVec 32 :=
      2147483648#32 ||| 536870912#32 ||| BitVec.setWidth 32 (BitVec.ofNat 64 c.mv)
    c0_hsteps
    refine hQ fd1 (ext1.set 0 v0) (c.mv + 1) _ ?_ (fun _ => rfl) (fun h => absurd htum h) ?_
    · exact ⟨{ hlen.core_ok with frame_dec_len := hfdl1 },
        { hlen.scratch_ok with extend_stk_len := by simp [hesl1] }⟩
    · rw [← hmv1_eq]; assumption

end LeanQbe.T.Examples.Kissat.Proof.Parse
