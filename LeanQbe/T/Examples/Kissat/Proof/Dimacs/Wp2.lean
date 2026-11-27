/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Dimacs.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Spec.MemBridges
public import LeanQbe.T.Examples.Kissat.Src.Dimacs
public import LeanQbe.T.Logic.C0Step
public import LeanQbe.T.Logic.C0HeadStep

/-!
# Soundness Proof for `kissat_check_model` (`Proof.Dimacs.Wp2`)

Proves parametric `(Γ : Env)` `Func.wp` soundness for `kissat_check_model` against canonical
`Spec.SatNv.kissatCheckModelExactSpec`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Dimacs

open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Src.Dimacs
open Kraken.Bedrock2.Test

open Std.ExtHashMap

private theorem sep_mid_to_front {P Q R : Mem 64 → Prop} {m : Mem 64}
    (h : (P ⋆ Q ⋆ R) m) : (Q ⋆ (P ⋆ R)) m := by
  rw [sep_comm P Q, sep_assoc] at h
  exact h

private theorem sep_front_to_mid {P Q R : Mem 64 → Prop} {m : Mem 64}
    (h : (Q ⋆ (P ⋆ R)) m) : (P ⋆ Q ⋆ R) m := by
  rw [← sep_assoc, sep_comm Q P] at h
  exact h

private theorem wp_load_d_mv {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {cnf_ptr : BitVec 64} {d mv nc cur val : Val i64} {bs : List UInt8} {R : Mem 64 → Prop}
    {k : Val i64 → Expr Val Cont rs}
    (hm : (bytes cnf_ptr bs ⋆ dimacsState d mv nc cur val ⋆ R) m)
    (hk : wp Γ Q X (k mv) m) :
    wp Γ Q X (.load i64 (Arg.var d) k) m := by
  refine wp_load_of ?_ hk
  simpa only [Arg.val_var] using load_dimacs_mv (sep_mid_to_front hm)

private theorem wp_load_d_nc {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {cnf_ptr : BitVec 64} {d mv nc cur val : Val i64} {bs : List UInt8} {R : Mem 64 → Prop}
    {k : Val i64 → Expr Val Cont rs}
    (hm : (bytes cnf_ptr bs ⋆ dimacsState d mv nc cur val ⋆ R) m)
    (hk : wp Γ Q X (k nc) m) :
    wp Γ Q X (.load i64 (Arg.var (d + 8)) k) m := by
  refine wp_load_of ?_ hk
  simpa only [Arg.val_var] using load_dimacs_nc (sep_mid_to_front hm)

private theorem wp_load_d_cur {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {cnf_ptr : BitVec 64} {d mv nc cur val : Val i64} {bs : List UInt8} {R : Mem 64 → Prop}
    {k : Val i64 → Expr Val Cont rs}
    (hm : (bytes cnf_ptr bs ⋆ dimacsState d mv nc cur val ⋆ R) m)
    (hk : wp Γ Q X (k cur) m) :
    wp Γ Q X (.load i64 (Arg.var (d + 16)) k) m := by
  refine wp_load_of ?_ hk
  simpa only [Arg.val_var] using load_dimacs_cur (sep_mid_to_front hm)

private theorem wp_load_d_val {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {cnf_ptr : BitVec 64} {d mv nc cur val : Val i64} {bs : List UInt8} {R : Mem 64 → Prop}
    {k : Val i64 → Expr Val Cont rs}
    (hm : (bytes cnf_ptr bs ⋆ dimacsState d mv nc cur val ⋆ R) m)
    (hk : wp Γ Q X (k val) m) :
    wp Γ Q X (.load i64 (Arg.var (d + 24)) k) m := by
  refine wp_load_of ?_ hk
  simpa only [Arg.val_var] using load_dimacs_val (sep_mid_to_front hm)

private theorem wp_store_d_cur {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {cnf_ptr : BitVec 64} {d mv nc cur val cur' : Val i64} {bs : List UInt8} {R : Mem 64 → Prop}
    {k : Expr Val Cont rs}
    (hm : (bytes cnf_ptr bs ⋆ dimacsState d mv nc cur val ⋆ R) m)
    (hk : ∀ m', (bytes cnf_ptr bs ⋆ dimacsState d mv nc cur' val ⋆ R) m' → wp Γ Q X k m') :
    wp Γ Q X (.store (Arg.var cur') (Arg.var (d + 16)) k) m := by
  refine wp_store_sep ?_ fun m' hm' => hk m' (sep_front_to_mid hm')
  simpa only [Arg.val_var] using store_dimacs_cur cur' (sep_mid_to_front hm)

private theorem wp_load_vals_byte {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {cnf_ptr vals_ptr p : BitVec 64} {d mv nc cur val : Val i64}
    {cnfBytes valsBytes : List UInt8} {idx : Nat} {R : Mem 64 → Prop}
    {k : Val i8 → Expr Val Cont rs}
    (hp : p = vals_ptr + BitVec.ofNat 64 idx) (hi : idx < valsBytes.length)
    (hlen : valsBytes.length ≤ 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ dimacsState d mv nc cur val ⋆
      (bytes vals_ptr valsBytes ⋆ R)) m)
    (hk : wp Γ Q X (k (BitVec.ofNat 8 valsBytes[idx].toNat)) m) :
    wp Γ Q X (.load i8 (Arg.var p) k) m := by
  subst hp
  have hm' : (bytes vals_ptr valsBytes ⋆
      (R ⋆ (bytes cnf_ptr cnfBytes ⋆ dimacsState d mv nc cur val))) m := by
    rw [sep_comm (bytes cnf_ptr cnfBytes ⋆ dimacsState d mv nc cur val) _, sep_assoc] at hm
    exact hm
  exact wp_load_of (load_bytes_at hi hlen hm') hk

private theorem bv_lit_var_addr {l : Nat} (hl : l < 2 * dimacsBound) {o1 o2 : Nat}
    (ho1 : o1 = 1) (ho2 : o2 = 1) :
    ((BitVec.ofNat 64 l >>> o1) <<< o2) =
      BitVec.ofNat 64 (2 * litVar l) := by
  subst ho1 ho2
  have hbnd : dimacsBound = 2 ^ 28 := rfl
  unfold litVar
  apply BitVec.eq_of_toNat_eq
  have hshr : (BitVec.ofNat 64 l >>> (1 : Nat)).toNat = l / 2 := by
    simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    omega
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, hshr]
  omega

private theorem checkClausesVals_succ (mv : Nat) (valsBytes : List UInt8) (n : Nat)
    (bs : List UInt8) :
    checkClausesVals mv valsBytes (n + 1) bs =
      match checkClauseValsAux (bs.length + 1) mv valsBytes false bs with
      | none => false
      | some (sat, rest) => sat && checkClausesVals mv valsBytes n rest := by
  rw [checkClausesVals]
  cases checkClauseValsAux (bs.length + 1) mv valsBytes false bs with
  | none => rfl
  | some p => rcases p with ⟨_ | _, _⟩ <;> rfl

private theorem bv_lit_sign_zero_iff {l : Nat} (hl : l < 2 * dimacsBound) :
    ((BitVec.ofNat 64 l &&& 1#64) = 0#64) ↔ litSign l = false := by
  have hbnd : dimacsBound = 2 ^ 28 := rfl
  unfold litSign
  have hm1 : (BitVec.ofNat 64 l &&& 1#64).toNat = l % 2 := by
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.and_one_is_mod]
    simp [Nat.mod_eq_of_lt (by omega : l < 2 ^ 64)]
  constructor
  · intro h
    have ht := congrArg BitVec.toNat h
    rw [hm1] at ht; simp [ht]
  · intro h
    apply BitVec.eq_of_toNat_eq
    rw [hm1]; simp at h; simp [h]

private theorem evalLitVals_pos_eq {valsBytes : List UInt8} {l : Nat}
    (hs : litSign l = false) (hi : 2 * litVar l < valsBytes.length) :
    evalLitVals valsBytes l =
      (0#32).slt ((BitVec.ofNat 8 valsBytes[2 * litVar l].toNat).signExtend 32) := by
  simp only [evalLitVals, hs, Bool.false_eq_true, ↓reduceIte, i8_sext32_sgt_zero,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  rfl

private theorem evalLitVals_neg_eq {valsBytes : List UInt8} {l : Nat}
    (hs : litSign l = true) (hi : 2 * litVar l < valsBytes.length) :
    evalLitVals valsBytes l =
      ((BitVec.ofNat 8 valsBytes[2 * litVar l].toNat).signExtend 32).slt 0#32 := by
  simp only [evalLitVals, hs, ↓reduceIte, i8_sext32_slt_zero,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  rfl

private theorem cnf_ptr_eq_end_iff {cnf_ptr : BitVec 64} {j n : Nat}
    (hbound : cnf_ptr.toNat + n < 2 ^ 64) (hj : j ≤ n) :
    cnf_ptr + BitVec.ofNat 64 j = cnf_ptr + BitVec.ofNat 64 n ↔ j = n := by
  constructor
  · intro h
    have ht := congrArg BitVec.toNat h
    rw [bv_add_ofNat_toNat (by omega), bv_add_ofNat_toNat hbound] at ht
    omega
  · intro h; subst h; rfl

/-- Soundness proof for `kissat_check_model`. -/
theorem kissat_check_model_wp (Γ : Env)
    (hHdr : Γ.Has "kissat_parse_header" Spec.kissatParseHeaderSpec)
    (hLit : Γ.Has "kissat_next_lit" Spec.kissatNextLitSpec)
    (hSkip : Γ.Has "kissat_skip_ws_comments" Spec.kissatSkipWsCommentsSpec) :
    ∀ a m Q X, kissatCheckModelExactSpec a m Q X →
      Func.wp Γ kissat_check_model_body a m Q X := by
  rintro ⟨cnf_ptr, cend, d, vals_ptr, mv_max_v, ⟨⟩⟩ m Q X
    ⟨mv0, nc0, cur0, val0, cnfBytes, valsBytes, mv_max, R,
     rfl, rfl, hbound, hmv_max64, hvals_ge, hvals_64, hm, hQ⟩
  unfold Func.wp kissat_check_model_body
  c0_hsteps_nogrp
  c0_call hHdr
  refine ⟨mv0, nc0, cur0, val0, cnfBytes, bytes vals_ptr valsBytes ⋆ R, rfl, hbound,
    by rw [← sep_assoc]; exact hm, ?_⟩
  cases hph : parseHeader cnfBytes with
  | none =>
    simp only [runKissatCheckModel, hph] at hQ
    intro mv' nc' cur' val' m' hm'
    dsimp only
    c0_hsteps
    · exact absurd (by assumption : false = true) (by decide)
    · exact hQ 0#64 mv' nc' cur' val' m' rfl (by rw [sep_assoc]; exact hm')
  | some p =>
    rcases p with ⟨mv, nc, rest0⟩
    simp only [runKissatCheckModel, hph] at hQ
    intro i0 m0 hmv_bnd hnc_bnd hi0_le hdrop0 hm0
    dsimp only
    have hm0_w : (bytes cnf_ptr cnfBytes ⋆ dimacsState d (BitVec.ofNat 64 mv) (BitVec.ofNat 64 nc)
        (cnf_ptr + BitVec.ofNat 64 i0) (BitVec.ofNat 64 nc) ⋆
        bytes vals_ptr valsBytes ⋆ R) m0 := by
      rw [sep_assoc]
      exact hm0
    c0_hsteps_nogrp
    · refine wp_load_d_mv hm0 ?_
      c0_hsteps_nogrp
      · have hgt : mv > mv_max := by
          have hc : BitVec.ofNat 64 mv_max < BitVec.ofNat 64 mv := by c0_bound
          rw [BitVec.lt_def, bv64_ofNat_toNat hmv_max64,
            bv64_ofNat_toNat (by unfold dimacsBound at *; omega)] at hc
          exact hc
        simp only [hgt, ↓reduceIte] at hQ
        c0_hsteps
        exact hQ 0#64 (BitVec.ofNat 64 mv) (BitVec.ofNat 64 nc) (cnf_ptr + BitVec.ofNat 64 i0)
          (BitVec.ofNat 64 nc) m0 rfl hm0_w
      · have hle : mv ≤ mv_max := by
          have hc : ¬ BitVec.ofNat 64 mv_max < BitVec.ofNat 64 mv := by c0_bound
          rw [BitVec.lt_def, bv64_ofNat_toNat hmv_max64,
            bv64_ofNat_toNat (by unfold dimacsBound at *; omega)] at hc
          omega
        simp only [Nat.not_lt.mpr hle, ↓reduceIte] at hQ
        have hmv64 : mv < 2 ^ 64 := by unfold dimacsBound at *; omega
        have hnc64 : nc < 2 ^ 64 := by unfold dimacsBound at *; omega
        c0_hsteps
        refine wp_loop_group
          (fun (n : Nat) (args : Tup Val [i64]) (mL : Mem 64) =>
            ∃ ci k val', ci ≤ nc ∧ n = nc - ci ∧ args.1 = BitVec.ofNat 64 ci ∧
              k ≤ cnfBytes.length ∧
              (bytes cnf_ptr cnfBytes ⋆
                dimacsState d (BitVec.ofNat 64 mv) (BitVec.ofNat 64 nc)
                  (cnf_ptr + BitVec.ofNat 64 k) val' ⋆
                bytes vals_ptr valsBytes ⋆ R) mL ∧
              checkClausesVals mv valsBytes (nc - ci) (cnfBytes.drop k) =
                checkClausesVals mv valsBytes nc rest0)
          (fun J n (ci_bv, ()) mL hLoop
              ⟨ci, k, val', hci_le, hn_eq, hci_bv, hk_le, hmL, hchk⟩ => ?_)
          (fun J hLoop => ?_)
        · dsimp only at hci_bv; subst hci_bv
          have hmL_w : (bytes cnf_ptr cnfBytes ⋆ dimacsState d (BitVec.ofNat 64 mv)
              (BitVec.ofNat 64 nc) (cnf_ptr + BitVec.ofNat 64 k) val' ⋆
              (bytes vals_ptr valsBytes ⋆ R)) mL := by
            rw [sep_assoc] at hmL
            exact hmL
          rw [Blocks.get_here]; dsimp only
          c0_hsteps_nogrp
          refine wp_load_d_nc hmL_w ?_
          c0_hsteps_nogrp
          · have hci_lt : ci < nc := by
              have hc : BitVec.ofNat 64 ci < BitVec.ofNat 64 nc := by c0_bound
              rw [BitVec.lt_def, bv64_ofNat_toNat (by omega), bv64_ofNat_toNat hnc64] at hc
              exact hc
            have hrem_pos : ∃ r, nc - ci = r + 1 := ⟨nc - ci - 1, by omega⟩
            rcases hrem_pos with ⟨cl_rem, hrem⟩
            rw [hrem] at hchk
            c0_hsteps
            refine wp_loop_group
              (fun (m_n : Nat) (sargs : Tup Val [.bool]) (mC : Mem 64) =>
                ∃ pos valc sat, pos ≤ cnfBytes.length ∧ m_n = cnfBytes.length - pos ∧
                  sargs.1 = sat ∧
                  (bytes cnf_ptr cnfBytes ⋆
                    dimacsState d (BitVec.ofNat 64 mv) (BitVec.ofNat 64 nc)
                      (cnf_ptr + BitVec.ofNat 64 pos) valc ⋆
                    bytes vals_ptr valsBytes ⋆ R) mC ∧
                  match checkClauseValsAux (cnfBytes.length - pos + 1) mv valsBytes sat
                      (cnfBytes.drop pos) with
                  | none => checkClauseValsAux ((cnfBytes.drop k).length + 1) mv valsBytes false
                      (cnfBytes.drop k) = none
                  | some (sat', rest') =>
                    checkClauseValsAux ((cnfBytes.drop k).length + 1) mv valsBytes false
                      (cnfBytes.drop k) = some (sat', rest'))
              (fun Jc m_n (sat_bv, ()) mC hLc
                  ⟨pos, valc, sat, hpos_le, hmn_eq, hsat_eq, hmC, hcc⟩ => ?_)
              (fun Jc hLc => ?_)
            · dsimp only at hsat_eq; subst sat_bv
              rw [Blocks.get_here]; dsimp only
              c0_hsteps_nogrp
              · c0_call hLit
                refine ⟨cnf_ptr, BitVec.ofNat 64 nc, valc, mv, cnfBytes, pos,
                  bytes vals_ptr valsBytes ⋆ R, rfl, hbound, hmv64, hpos_le,
                  by rw [← sep_assoc]; exact hmC, ?_⟩
                have hc_step : checkClauseValsAux (cnfBytes.length - pos + 1) mv valsBytes sat
                    (cnfBytes.drop pos) =
                    match nextLitPure mv (cnfBytes.drop pos) with
                    | .err => none
                    | .endClause rest' => some (sat, rest')
                    | .lit l rest' => checkClauseValsAux (cnfBytes.length - pos) mv valsBytes
                        (sat || evalLitVals valsBytes l) rest' := rfl
                cases hnl : nextLitPure mv (cnfBytes.drop pos) with
                | err =>
                  rw [hnl] at hc_step; rw [hc_step] at hcc; simp at hcc
                  rw [checkClausesVals_succ, List.length_drop, hcc] at hchk
                  simp at hchk; rw [hchk] at hQ; simp at hQ
                  intro cur' val' m' hm'
                  c0_hsteps
                  exact hQ 0#64 (BitVec.ofNat 64 mv) (BitVec.ofNat 64 nc) cur' val' m' rfl
                    (by simpa only [sep_assoc] using hm')
                | endClause rest' =>
                  rw [hnl] at hc_step; rw [hc_step] at hcc; dsimp only at hcc
                  intro j m' hpos_j hj_le hdrop_j hm'
                  c0_hsteps_nogrp
                  · have hsat_t : sat = true := by assumption
                    subst hsat_t
                    rw [checkClausesVals_succ, hcc] at hchk; dsimp only at hchk
                    rw [← hdrop_j] at hchk
                    have hci_next : BitVec.ofNat 64 ci + (1 : BitVec 64) =
                        BitVec.ofNat 64 (ci + 1) := by
                      apply BitVec.eq_of_toNat_eq
                      simp [Nat.mod_eq_of_lt (by omega : ci + 1 < 2 ^ 64)]
                    c0_hsteps
                    rw [hci_next]
                    exact hLoop (nc - (ci + 1)) (BitVec.ofNat 64 (ci + 1), ()) m' (by omega)
                      ⟨ci + 1, j, 0#64, by omega, rfl, rfl, hj_le,
                        (by simpa only [sep_assoc] using hm'), by
                        rw [show nc - (ci + 1) = cl_rem by omega]; exact hchk⟩
                  · have hsat_f : sat = false := by assumption
                    subst hsat_f
                    rw [checkClausesVals_succ, hcc] at hchk
                    simp at hchk; rw [hchk] at hQ; simp at hQ
                    c0_hsteps
                    exact hQ 0#64 (BitVec.ofNat 64 mv) (BitVec.ofNat 64 nc)
                      (cnf_ptr + BitVec.ofNat 64 j) 0#64 m' rfl
                      (by simpa only [sep_assoc] using hm')
                | lit l rest' =>
                  rw [hnl] at hc_step; dsimp only at hc_step
                  intro j m' hl_2mv hl_bnd hpos_j hj_le hdrop_j hm'
                  have hvar_idx : 2 * litVar l < valsBytes.length := by
                    unfold litVar; omega
                  c0_hsteps_nogrp
                  refine wp_load_d_val hm' ?_
                  c0_hsteps_nogrp
                  dsimp only
                  rw [bv_lit_var_addr hl_bnd (by rfl) (by rfl)]
                  refine wp_load_vals_byte rfl hvar_idx hvals_64 hm' ?_
                  have hirr : checkClauseValsAux (cnfBytes.length - j + 1) mv valsBytes
                      (sat || evalLitVals valsBytes l) (cnfBytes.drop j) =
                      checkClauseValsAux (cnfBytes.length - pos) mv valsBytes
                        (sat || evalLitVals valsBytes l) rest' := by
                    rw [← hdrop_j]
                    exact checkClauseValsAux_fuel_irrel (by simp) (by simp; omega)
                  rw [hirr.symm] at hc_step
                  rw [hc_step] at hcc
                  by_cases hsign : litSign l = false
                  · have hs0 : (BitVec.ofNat 64 l &&& (1 : BitVec 64)) = 0 :=
                      (bv_lit_sign_zero_iff hl_bnd).mpr hsign
                    rw [evalLitVals_pos_eq hsign hvar_idx] at hcc
                    c0_hsteps
                    all_goals try exact absurd (by assumption : (BitVec.ofNat 64 l &&& 1) ≠ 0) hs0
                    · have hpos_b : (0#32).slt
                          ((BitVec.ofNat 8 valsBytes[2 * litVar l].toNat).signExtend 32) =
                          true := by
                        assumption
                      rw [hpos_b, Bool.or_true] at hcc
                      exact hLc (cnfBytes.length - j) (true, ()) m' (by omega)
                        ⟨j, BitVec.ofNat 64 l, true, hj_le, rfl, rfl,
                          (by simpa only [sep_assoc] using hm'), hcc⟩
                    · have hnp : (0#32).slt
                          ((BitVec.ofNat 8 valsBytes[2 * litVar l].toNat).signExtend 32) =
                          false := by
                        assumption
                      rw [hnp, Bool.or_false] at hcc
                      exact hLc (cnfBytes.length - j) (sat, ()) m' (by omega)
                        ⟨j, BitVec.ofNat 64 l, sat, hj_le, rfl, rfl,
                          (by simpa only [sep_assoc] using hm'), hcc⟩
                  · have hs_t : litSign l = true := Bool.eq_true_of_ne_false hsign
                    have hns0 : (BitVec.ofNat 64 l &&& (1 : BitVec 64)) ≠ 0 :=
                      fun h => absurd ((bv_lit_sign_zero_iff hl_bnd).mp h) (by rw [hs_t]; decide)
                    rw [evalLitVals_neg_eq hs_t hvar_idx] at hcc
                    c0_hsteps
                    all_goals try exact absurd (by assumption : (BitVec.ofNat 64 l &&& 1) = 0) hns0
                    · have hneg_b :
                          ((BitVec.ofNat 8 valsBytes[2 * litVar l].toNat).signExtend 32).slt
                          0#32 = true := by assumption
                      rw [hneg_b, Bool.or_true] at hcc
                      exact hLc (cnfBytes.length - j) (true, ()) m' (by omega)
                        ⟨j, BitVec.ofNat 64 l, true, hj_le, rfl, rfl,
                          (by simpa only [sep_assoc] using hm'), hcc⟩
                    · have hnn : ((BitVec.ofNat 8 valsBytes[2 * litVar l].toNat).signExtend 32).slt
                          0#32 = false := by assumption
                      rw [hnn, Bool.or_false] at hcc
                      exact hLc (cnfBytes.length - j) (sat, ()) m' (by omega)
                        ⟨j, BitVec.ofNat 64 l, sat, hj_le, rfl, rfl,
                          (by simpa only [sep_assoc] using hm'), hcc⟩
              all_goals exact absurd (by assumption : true = false) (by decide)
            · c0_hsteps
              refine hLc (cnfBytes.length - k) (false, ()) mL
                ⟨k, val', false, hk_le, rfl, rfl, hmL, ?_⟩
              have hirr := checkClauseValsAux_fuel_irrel (f1 := cnfBytes.length - k + 1)
                (f2 := (cnfBytes.drop k).length + 1) (mv := mv) (valsBytes := valsBytes)
                (sat := false) (bs := cnfBytes.drop k) (by simp) (by simp)
              rw [hirr]
              cases checkClauseValsAux ((cnfBytes.drop k).length + 1) mv valsBytes false
                  (cnfBytes.drop k) <;> rfl
          · have hci_eq : ci = nc := by
              have hc : ¬ BitVec.ofNat 64 ci < BitVec.ofNat 64 nc := by c0_bound
              rw [BitVec.lt_def, bv64_ofNat_toNat (by omega), bv64_ofNat_toNat hnc64] at hc
              omega
            subst hci_eq
            simp only [Nat.sub_self, checkClausesVals] at hchk
            try c0_hstraight
            refine wp_load_d_cur hmL_w ?_
            c0_hsteps_nogrp
            c0_call hSkip
            refine ⟨cnf_ptr, cnfBytes, k,
              dimacsState d (BitVec.ofNat 64 mv) (BitVec.ofNat 64 ci)
                (cnf_ptr + BitVec.ofNat 64 k) val' ⋆ bytes vals_ptr valsBytes ⋆ R,
              rfl, rfl, hbound, hk_le, by simpa only [sep_assoc] using hmL,
              fun j hk_j hj_le hdrop_j => ?_⟩
            try c0_hstraight
            refine wp_store_d_cur hmL_w fun m'' hm'' => ?_
            dsimp only at hm''
            rw [← hdrop_j] at hchk
            refine wp_load_d_cur hm'' ?_
            c0_hsteps_nogrp
            · have hj_ne : j ≠ cnfBytes.length := fun h =>
                (by assumption :
                    cnf_ptr + BitVec.ofNat 64 j ≠ cnf_ptr + BitVec.ofNat 64 cnfBytes.length)
                  ((cnf_ptr_eq_end_iff hbound hj_le).mpr h)
              have hne_emp : (cnfBytes.drop j).isEmpty = false := by
                cases hd : cnfBytes.drop j with
                | nil => exact absurd (List.drop_eq_nil_iff.mp hd |> fun h => by omega) hj_ne
                | cons _ _ => rfl
              rw [hne_emp] at hchk
              exact hQ 0#64 (BitVec.ofNat 64 mv) (BitVec.ofNat 64 ci)
                (cnf_ptr + BitVec.ofNat 64 j) val' m''
                (by simp [← hchk]) (by simpa only [sep_assoc] using hm'')
            · have hj_eq : j = cnfBytes.length :=
                (cnf_ptr_eq_end_iff hbound hj_le).mp (by assumption)
              subst hj_eq
              have hemp : (cnfBytes.drop cnfBytes.length).isEmpty = true := by
                rw [List.drop_length]; rfl
              rw [hemp] at hchk
              exact hQ 1#64 (BitVec.ofNat 64 mv) (BitVec.ofNat 64 ci)
                (cnf_ptr + BitVec.ofNat 64 cnfBytes.length) val' m''
                (by simp [← hchk]) (by simpa only [sep_assoc] using hm'')
        · c0_hsteps
          refine hLoop nc (0#64, ()) m0
            ⟨0, i0, BitVec.ofNat 64 nc, Nat.zero_le _, rfl, rfl, hi0_le, hm0_w,
              by rw [Nat.sub_zero, hdrop0]⟩
    · exact absurd (by assumption : true = false) (by decide)

end LeanQbe.T.Examples.Kissat.Proof.Dimacs