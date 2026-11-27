/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Bitblast.Proof.ValidateNode
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.ProofKit

/-!
# Program Validator WP Proof (`Bitblast.Proof.Validate`)

Proves `bv_validate_wp` (`Γ`-parametric `Func.wp` soundness for `bv_validate`),
composing `bv_read_u32_wp`, `bv_count_atoms_wp`, and `bv_validate_node_wp` into
`validBVP1_parse` / `BVProg.parse progBytes = some prog`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Bitblast.Proof

open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofKit
open LeanQbe.T.Examples.Bitblast.Src
open LeanQbe.T.Examples.Bitblast.Src.Validate
open LeanQbe.T.Examples.Bitblast.Ref.BVProg

private theorem bv64_and3_eq_zero (x : BitVec 64) :
    (x &&& 3#64).toNat = 0 ↔ x.toNat % 4 = 0 := by
  have h1 : (x &&& 3#64).toNat = x.toNat &&& 3 := by simp [BitVec.toNat_and]
  have h2 : x.toNat &&& 3 = x.toNat % 4 := by
    simpa using Nat.and_two_pow_sub_one_eq_mod x.toNat 2
  rw [h1, h2]

private theorem val_ult_sub_max_toNat (progPtr progLen : BitVec 64)
    (h : ((18446744073709551615 - progPtr).ult progLen) = false) :
    progPtr.toNat + progLen.toNat < 2 ^ 64 := by
  have hp := progPtr.isLt; have hl := progLen.isLt
  have hsub : (18446744073709551615 - progPtr).toNat = 2 ^ 64 - 1 - progPtr.toNat := by
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by
      rw [show (18446744073709551615 : BitVec 64).toNat = 2 ^ 64 - 1 by simp]; omega)),
      show (18446744073709551615 : BitVec 64).toNat = 2 ^ 64 - 1 by simp]
  simp only [BitVec.ult, decide_eq_false_iff_not, Nat.not_lt, hsub] at h
  omega

private theorem val_ult_sub_max_contra (progPtr progLen : BitVec 64)
    (h : ((18446744073709551615 - progPtr).ult progLen) = true)
    (hlt : progPtr.toNat + progLen.toNat < 2 ^ 64) : False := by
  have hp := progPtr.isLt
  have hsub : (18446744073709551615 - progPtr).toNat = 2 ^ 64 - 1 - progPtr.toNat := by
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by
      rw [show (18446744073709551615 : BitVec 64).toNat = 2 ^ 64 - 1 by simp]; omega)),
      show (18446744073709551615 : BitVec 64).toNat = 2 ^ 64 - 1 by simp]
  simp only [BitVec.ult, decide_eq_true_eq, hsub] at h
  omega

private theorem val_nodesOff_eq (nv nc : Nat) (hnv : nv < 2 ^ 32) (hnc : nc < 2 ^ 32) :
    (8 + ((BitVec.ofNat 32 nv).setWidth 64 <<< (1 : Nat)) +
      (BitVec.ofNat 32 nc).setWidth 64).toNat = nodesOff nv nc := by
  unfold nodesOff
  have h1 : ((BitVec.ofNat 32 nv).setWidth 64).toNat = nv := by
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnv,
      Nat.mod_eq_of_lt (by omega)]
  have h2 : ((BitVec.ofNat 32 nc).setWidth 64).toNat = nc := by
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnc,
      Nat.mod_eq_of_lt (by omega)]
  have hsh : ((BitVec.ofNat 32 nv).setWidth 64 <<< (1 : Nat)).toNat = 2 * nv := by
    rw [BitVec.toNat_shiftLeft, h1, Nat.shiftLeft_eq]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have h8 : (8 : BitVec 64).toNat = 8 := rfl
  rw [BitVec.toNat_add, BitVec.toNat_add, h8, hsh, h2,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

private theorem val_rootOff_eq (nv nc rt : Nat)
    (hnv : nv < 2 ^ 32) (hnc : nc < 2 ^ 32) (hrt : rt < 2 ^ 32) :
    ((8 + ((BitVec.ofNat 32 nv).setWidth 64 <<< (1 : Nat)) +
        (BitVec.ofNat 32 nc).setWidth 64) +
      (BitVec.ofNat 32 rt).setWidth 64 * 5).toNat = nodesOff nv nc + 5 * rt := by
  have hnw := val_nodesOff_eq nv nc hnv hnc
  have h3 : ((BitVec.ofNat 32 rt).setWidth 64).toNat = rt := by
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hrt,
      Nat.mod_eq_of_lt (by omega)]
  have h5 : (5 : BitVec 64).toNat = 5 := rfl
  have hm : ((BitVec.ofNat 32 rt).setWidth 64 * 5).toNat = 5 * rt := by
    rw [BitVec.toNat_mul, h3, h5, Nat.mod_eq_of_lt (by omega)]
    omega
  rw [BitVec.toNat_add, hnw, hm, Nat.mod_eq_of_lt (by unfold nodesOff; omega)]

public section

theorem bv_validate_wp (Γ : Env)
    (hRead : ∀ xs m Q X, bvReadU32Spec xs m Q X →
      Γ "bv_read_u32" [i64, i64] [i32] xs m Q X)
    (hCount : ∀ xs m Q X, bvCountAtomsSpec xs m Q X →
      Γ "bv_count_atoms" [i64, i32] [i64] xs m Q X)
    (hNode : ∀ xs m Q X, bvValidateNodeSpec xs m Q X →
      Γ "bv_validate_node" [i64, i64, i32, i32, i32] [.bool] xs m Q X) :
    ∀ xs m Q X, bvValidateSpec xs m Q X → Func.wp Γ bv_validate_body xs m Q X := by
  rintro ⟨progPtr, progLen, ⟨⟩⟩ m Q X ⟨progBytes, R, hplen, hm, hQ⟩
  c0_hstraight
  c0_hsplit
  · c0_hstraight; exact hQ false (by simp [hc])
  · have hpptr : progPtr ≠ 0#64 := hc; clear hc
    c0_hstraight
    c0_hsplit
    · c0_hstraight
      exact hQ false ⟨fun h => absurd h Bool.false_ne_true,
        fun ⟨_, _, hv⟩ => by have hge := hv.len_ge; c0_bv_omega [hplen, hge]⟩
    · have hlen32 : 32 ≤ progBytes.length := by c0_bv_omega [hplen, hc]
      clear hc
      c0_hstraight
      c0_hsplit
      · c0_hstraight
        exact hQ false ⟨fun h => absurd h Bool.false_ne_true,
          fun ⟨_, _, hv⟩ => False.elim (hc (BitVec.eq_of_toNat_eq
            ((bv64_and3_eq_zero progLen).mpr (by have := hv.len_mod4; omega))))⟩
      · have hand0 : (progLen &&& 3#64).toNat = 0 := congrArg BitVec.toNat hc
        clear hc
        c0_hstraight
        refine head_wp_jnz rfl (fun hc => ?_) (fun hc => ?_)
        · dsimp only [Arg.val, Prod.fst] at hc
          c0_hstraight
          exact hQ false ⟨fun h => absurd h Bool.false_ne_true,
            fun ⟨_, hfit, _⟩ =>
              False.elim (val_ult_sub_max_contra progPtr progLen hc (by omega))⟩
        · dsimp only [Arg.val, Prod.fst] at hc
          have hfit_len : progPtr.toNat + progLen.toNat < 2 ^ 64 :=
            val_ult_sub_max_toNat progPtr progLen hc
          clear hc
          c0_hstraight
          have hfit : progPtr.toNat + progBytes.length < 2 ^ 64 := by omega
          c0_call hRead; refine ⟨progBytes, R, hfit, by c0_bv_omega [hlen32], hm, ?_⟩
          c0_hstraight
          c0_call hRead; refine ⟨progBytes, R, hfit, by c0_bv_omega [hlen32], hm, ?_⟩
          c0_hstraight
          c0_hsplit
          · c0_hstraight
            exact hQ false ⟨fun h => absurd h Bool.false_ne_true,
              fun ⟨_, _, hv⟩ => False.elim (hc (by rw [hv.magic_eq]; rfl))⟩
          · have hmagic : u32At progBytes 0 = bvMagic := by
              have h0 := u32At_lt progBytes 0; unfold u32Bound at h0
              have hc' := congrArg BitVec.toNat hc
              rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h0,
                show (827348546 : BitVec 32).toNat = 827348546 from rfl] at hc'
              exact hc'
            clear hc
            c0_hstraight
            c0_hsplit
            · c0_hstraight
              exact hQ false ⟨fun h => absurd h Bool.false_ne_true,
                fun ⟨_, _, hv⟩ => False.elim (hc (by
                  rw [show (1 : BitVec 64).toNat = 1 from rfl, hv.ver_eq]; rfl))⟩
            · have hver : u32At progBytes 1 = bvVersion := by
                have h1 := u32At_lt progBytes 1; unfold u32Bound at h1
                rw [show (1 : BitVec 64).toNat = 1 from rfl] at hc
                have hc' := congrArg BitVec.toNat hc
                rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1,
                  show (1 : BitVec 32).toNat = 1 from rfl] at hc'
                exact hc'
              clear hc
              c0_hstraight
              c0_call hRead; refine ⟨progBytes, R, hfit, by c0_bv_omega [hlen32], hm, ?_⟩
              c0_hstraight
              c0_call hRead; refine ⟨progBytes, R, hfit, by c0_bv_omega [hlen32], hm, ?_⟩
              c0_hstraight
              c0_call hRead; refine ⟨progBytes, R, hfit, by c0_bv_omega [hlen32], hm, ?_⟩
              c0_hstraight
              c0_call hRead; refine ⟨progBytes, R, hfit, by c0_bv_omega [hlen32], hm, ?_⟩
              c0_hstraight
              c0_hsplit
              · c0_hstraight
                exact hQ false ⟨fun h => absurd h Bool.false_ne_true,
                  fun ⟨_, _, hv⟩ => False.elim (by
                    have hnp := hv.nodes_pos
                    have h3 := u32At_lt progBytes 3; unfold u32Bound at h3
                    have hc' := congrArg BitVec.toNat hc
                    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h3,
                      show (0 : BitVec 32).toNat = 0 from rfl] at hc'
                    omega)⟩
              · have hnn_pos : 0 < u32At progBytes 3 := by
                  have h3 := u32At_lt progBytes 3; unfold u32Bound at h3
                  have hne : (BitVec.ofNat 32 (u32At progBytes 3)).toNat ≠ 0 :=
                    fun h => hc (BitVec.eq_of_toNat_eq (by simpa using h))
                  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h3] at hne
                  omega
                clear hc
                c0_hstraight
                c0_hsplit
                · c0_hstraight
                  exact hQ false ⟨fun h => absurd h Bool.false_ne_true,
                    fun ⟨_, _, hv⟩ => False.elim (by
                      have hrl := hv.root_lt
                      have h3 := u32At_lt progBytes 3; have h5 := u32At_lt progBytes 5
                      unfold u32Bound at h3 h5
                      rw [show (5 : BitVec 64).toNat = 5 from rfl] at hc
                      c0_bv_omega [h3, h5, hrl, hc])⟩
                · rw [show (5 : BitVec 64).toNat = 5 from rfl] at hc
                  have hrt_lt : u32At progBytes 5 < u32At progBytes 3 := by
                    have h3 := u32At_lt progBytes 3; have h5 := u32At_lt progBytes 5
                    unfold u32Bound at h3 h5
                    c0_bv_omega [h3, h5, hc]
                  clear hc
                  have hnv_lt := u32At_lt progBytes 2
                  have hnn_lt := u32At_lt progBytes 3
                  have hnc_lt := u32At_lt progBytes 4
                  unfold u32Bound at hnv_lt hnn_lt hnc_lt
                  have htot_lt : 4 * (8 + 2 * u32At progBytes 2 + u32At progBytes 4 +
                      5 * u32At progBytes 3) < 2 ^ 64 := by omega
                  c0_hstraight
                  c0_hsplit
                  · c0_hstraight
                    exact hQ false ⟨fun h => absurd h Bool.false_ne_true,
                      fun ⟨_, _, hv⟩ => by
                        have htl := hv.total_len
                        c0_bv_omega [hplen, htl, htot_lt, hc]⟩
                  · have htot : 4 * (8 + 2 * u32At progBytes 2 + u32At progBytes 4 +
                        5 * u32At progBytes 3) = progBytes.length := by
                      c0_bv_omega [hplen, htot_lt, hc]
                    clear hc
                    c0_call hCount
                    refine ⟨progBytes, R, hfit, by simp [BitVec.toNat_ofNat]; omega, hm, ?_⟩
                    c0_hsteps_nogrp
                    · exact hQ false ⟨fun h => absurd h Bool.false_ne_true,
                        fun ⟨_, _, hv⟩ => by
                          have hao := hv.atoms_ok
                          have hca := countAtoms_lt progBytes (u32At progBytes 2)
                          try unfold bvDimacsBound at hao
                          try unfold bvDimacsBound at hca
                          c0_bv_omega [hao, hca, hc]⟩
                    · have hatoms : countAtoms progBytes (u32At progBytes 2) ≠ 0 := by
                        have hca := countAtoms_lt progBytes (u32At progBytes 2)
                        try unfold bvDimacsBound at hca
                        c0_bv_omega [hca, hc]
                      clear hc
                      have hmod4 : progBytes.length % 4 = 0 := by
                        have := (bv64_and3_eq_zero progLen).mp hand0; omega
                      have hnw := val_nodesOff_eq (u32At progBytes 2) (u32At progBytes 4)
                        hnv_lt hnc_lt
                      have hro_eq := val_rootOff_eq (u32At progBytes 2) (u32At progBytes 4)
                        (u32At progBytes 5) hnv_lt hnc_lt (by omega)
                      refine wp_while_state (α := Nat)
                        (fun i => (BitVec.ofNat 32 i, ()))
                        (fun i => u32At progBytes 3 - i)
                        (fun i ml => ml = m ∧ i ≤ u32At progBytes 3 ∧
                          ∀ k < i, validNodeAt progBytes
                            (u32At progBytes 2) (u32At progBytes 4) k = true)
                        ?_ ?_
                      · intro J hJ
                        c0_hsteps
                        exact hJ 0 m ⟨rfl, Nat.zero_le _, fun _ h => by omega⟩
                      · intro J i ml ⟨hml, hi_le, hi_ok⟩ ih
                        subst hml
                        c0_hstraight
                        refine head_wp_jnz rfl (fun hc => ?_) (fun hc => ?_)
                        · dsimp only [Arg.val, Prod.fst] at hc
                          have hi_lt : i < u32At progBytes 3 := by
                            have hi_32 : (BitVec.ofNat 32 i).toNat = i := by
                              rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : i < 2 ^ 32)]
                            have hult : (BitVec.ofNat 32 i).ult
                                (BitVec.ofNat 32 (u32At progBytes 3)) = true := hc
                            rw [BitVec.ult, decide_eq_true_eq, hi_32, BitVec.toNat_ofNat,
                              Nat.mod_eq_of_lt hnn_lt] at hult
                            exact hult
                          clear hc
                          c0_hstraight
                          c0_call hNode
                          refine ⟨progBytes, R, hfit, ?_, ?_, hm, ?_⟩
                          · rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnv_lt,
                              Nat.mod_eq_of_lt hnc_lt]
                            exact hnw
                          · rw [hnw]; unfold nodesOff
                            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : i < 2 ^ 32)]
                            omega
                          · c0_hstraight
                            refine head_wp_jnz rfl (fun hc => ?_) (fun hc => ?_)
                            · dsimp only [Arg.val, Prod.fst] at hc
                              c0_hstraight
                              rw [show (BitVec.ofNat 32 i + 1 : BitVec 32) =
                                  BitVec.ofNat 32 (i + 1) from
                                BitVec.eq_of_toNat_eq (by simp [BitVec.toNat_add])]
                              exact ih (i + 1) ml (by omega) ⟨rfl, hi_lt, fun k hk => by
                                by_cases hki : k = i
                                · subst hki
                                  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
                                    Nat.mod_eq_of_lt hnv_lt, Nat.mod_eq_of_lt hnc_lt,
                                    Nat.mod_eq_of_lt (by omega : k < 2 ^ 32)] at hc
                                  exact hc
                                · exact hi_ok k (by omega)⟩
                            · dsimp only [Arg.val, Prod.fst] at hc
                              c0_hstraight
                              exact hQ false ⟨fun h => absurd h Bool.false_ne_true,
                                fun ⟨_, _, hv⟩ => False.elim (by
                                  have hok := hv.nodes_ok i hi_lt
                                  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
                                    Nat.mod_eq_of_lt hnv_lt, Nat.mod_eq_of_lt hnc_lt,
                                    Nat.mod_eq_of_lt (by omega : i < 2 ^ 32), hok] at hc
                                  cases hc)⟩
                        · dsimp only [Arg.val, Prod.fst] at hc
                          have hi_eq : i = u32At progBytes 3 := by
                            have hi_32 : (BitVec.ofNat 32 i).toNat = i := by
                              rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : i < 2 ^ 32)]
                            have hult : (BitVec.ofNat 32 i).ult
                                (BitVec.ofNat 32 (u32At progBytes 3)) = false := hc
                            rw [BitVec.ult, decide_eq_false_iff_not, Nat.not_lt, hi_32,
                              BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnn_lt] at hult
                            omega
                          clear hc
                          subst hi_eq
                          c0_hstraight
                          c0_call hRead
                          refine ⟨progBytes, R, hfit, ?_, hm, ?_⟩
                          · rw [hro_eq]; unfold nodesOff; omega
                          c0_hstraight
                          rw [hro_eq]
                          refine hQ _ ⟨fun h => ?_, fun ⟨_, _, hv⟩ => ?_⟩
                          · refine ⟨hpptr, hfit, ⟨hlen32, hmod4, hmagic, hver, hnn_pos, hrt_lt,
                              htot, hatoms, hi_ok, ?_⟩⟩
                            · unfold opEq
                              have hro := u32At_lt progBytes
                                (nodesOff (u32At progBytes 2) (u32At progBytes 4) +
                                  5 * u32At progBytes 5)
                              unfold u32Bound at hro
                              rw [BitVec.ule, decide_eq_true_eq, BitVec.toNat_ofNat,
                                Nat.mod_eq_of_lt hro,
                                show (22 : BitVec 32).toNat = 22 from rfl] at h
                              exact h
                          · have hrb := hv.root_bool
                            unfold opEq at hrb
                            have hro := u32At_lt progBytes
                              (nodesOff (u32At progBytes 2) (u32At progBytes 4) +
                                5 * u32At progBytes 5)
                            unfold u32Bound at hro
                            rw [BitVec.ule, decide_eq_true_eq, BitVec.toNat_ofNat,
                              Nat.mod_eq_of_lt hro,
                              show (22 : BitVec 32).toNat = 22 from rfl]
                            exact hrb

end

end LeanQbe.T.Examples.Bitblast.Proof
