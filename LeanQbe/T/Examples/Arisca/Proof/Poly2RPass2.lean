/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Arisca.Proof.Poly2RBase
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ProofKit
import LeanQbe.T.Logic.MemLemmas
import Kraken.Separation

/-!
# ARiSCA `ar_build_R` Pass 2 Expansion WP (`Arisca.Proof.Poly2RPass2`)

Proves `buildR_pass2_wp` (split into `buildR_pass2_J_wp`, `buildR_pass2_S_wp`, and
`buildR_pass2_wp` to keep every declaration well under the P0-5 limit), discharging the bounds
checks, `fv_b` constant-1 initialization, and the `i < cnt` / `countF` / `S < 2^f` /
`j ≤ mlen` subset-expansion loop of `ar_build_R` from `buildRPass2EntryExpr` into
`buildRPass2AfterExpr`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Arisca.Proof

open Std
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofKit
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Arisca
open LeanQbe.T.Examples.Arisca.Src
open LeanQbe.T.Examples.Arisca.Src.Poly

public section

private theorem nat_xor1_mod2 (x : Nat) :
    (x ^^^ 1) % 2 = if x % 2 = 0 then 1 else 0 := by
  have hb := Nat.testBit_xor x 1 0
  simp only [Nat.testBit, Nat.shiftRight_zero, Nat.and_one_is_mod] at hb
  have hm2 : x % 2 = 0 ∨ x % 2 = 1 := by omega
  have hm2' : (x ^^^ 1) % 2 = 0 ∨ (x ^^^ 1) % 2 = 1 := by omega
  rcases hm2 with h0 | h1 <;> rcases hm2' with g0 | g1 <;> simp_all

private theorem list_getLast?_some_eq {α : Type} (xs : List α) (d : α) (hx : 0 < xs.length) :
    xs.getLast? = some (xs.getD (xs.length - 1) d) := by
  have hne : xs ≠ [] := by intro h; subst h; simp at hx
  rw [List.getLast?_eq_some_getLast hne, getD_eq_getElem xs d (by omega),
    List.getLast_eq_getElem]

private theorem neg_polyEvalRange {nOut : Nat} (σ : Nat → Bool)
    (pool tm : List (BitVec 32)) (tl th : List (BitVec 64)) (off n : Nat) :
    -polyEvalRange nOut σ pool tm tl th off n =
      (List.range n).foldl
        (fun acc k => acc + -termEval nOut σ pool tm tl th (off + k)) 0#nOut := by
  induction n with
  | zero => simp [polyEvalRange]
  | succ n ih =>
    rw [polyEvalRange_succ, List.range_succ, List.foldl_append, List.foldl_cons,
      List.foldl_nil, BitVec.neg_add, ih, ← BitVec.sub_eq_add_neg]

private theorem expandSum_signed_eq {nOut bd : Nat} (σ : Nat → Bool)
    (flippedArr : List (BitVec 8)) (pool tm : List (BitVec 32)) (tl th : List (BitVec 64))
    (idx : Nat) (fv_b : Bool)
    (hσ : ∀ w < bd, σ (2 * w + 1) = !(σ (2 * w)))
    (hxs : ∀ x ∈ symListAt pool (tm.getD idx 0#32).toNat, x / 2 < bd) :
    expandSum nOut σ flippedArr (coeff128 nOut (tl.getD idx 0#64) (th.getD idx 0#64)) []
        (if fv_b then 1 else 0) (symListAt pool (tm.getD idx 0#32).toNat) =
      (if fv_b then -termEval nOut σ pool tm tl th idx
       else termEval nOut σ pool tm tl th idx) := by
  rw [expandSum_eq nOut bd σ flippedArr _ [] (if fv_b then 1 else 0) _ hσ hxs]
  simp only [monoValL_nil, Bool.true_and, termEval]
  cases hmv : monoValL σ (symListAt pool (tm.getD idx 0#32).toNat) <;> cases fv_b <;>
    simp [bv]

private theorem ruleBt8_mono (flippedArr : List (BitVec 8)) (rsPool rsM : List (BitVec 32))
    (off a b : Nat) (h : a ≤ b) :
    ruleBt8 flippedArr rsPool rsM off a ≤ ruleBt8 flippedArr rsPool rsM off b := by
  induction h with
  | refl => exact le_refl _
  | step _ ih => rw [ruleBt8_succ]; exact Nat.le_trans ih (Nat.le_add_right _ _)

private theorem ruleBw8_mono (flippedArr : List (BitVec 8)) (rsPool rsM : List (BitVec 32))
    (off a b : Nat) (h : a ≤ b) :
    ruleBw8 flippedArr rsPool rsM off a ≤ ruleBw8 flippedArr rsPool rsM off b := by
  induction h with
  | refl => exact le_refl _
  | step _ ih => rw [ruleBw8_succ]; exact Nat.le_trans ih (Nat.le_add_right _ _)

private theorem buildR_pass2_J_wp (Γ : T.Env)
    {Ji : Cont [.bits 32, .bits 64, .bits 32]} {Js : Cont [.bits 64, .bits 32, .bits 32, .bits 64]}
    {cx : BitVec 64} {v off cnt : BitVec 32} {fv_b any : Bool} {bt bw : BitVec 64}
    {iC : BitVec 32} {rpC : BitVec 64} {nC mOffBv mlenBv : BitVec 32} {cl ch : BitVec 64}
    {fF jF : BitVec 32} {rpS : BitVec 64} {nS_cur jU : BitVec 32} {S : BitVec 64}
    {s : ArCtxState} {ruleOff ruleN rsM : List (BitVec 32)} {rsL rsH : List (BitVec 64)}
    {rsPool : List (BitVec 32)} {flippedArr : List (BitVec 8)}
    {rmLen rpoolLen : Nat} {rmS rm2 : List (BitVec 32)} {rlS rhS rl2 rh2 : List (BitVec 64)}
    {rpoolS : List (BitVec 32)} {R : Mem 64 → Prop} {mS : Mem 64}
    {Q : Post [.bool]} {X : XPost}
    (hnn_bd : s.n_nets.toNat ≤ 0x3FFFFFFF) (hfl_len : s.n_nets.toNat ≤ flippedArr.length)
    (hmlen_eq : mlenBv = rsPool.getD mOffBv.toNat 0#32)
    (hmlen_32 : mlenBv.toNat + 1 < 2 ^ 32)
    (hmlen_end : mOffBv.toNat + mlenBv.toNat + 1 ≤ rsPool.length)
    (hxs_bd : ∀ x ∈ symListAt rsPool mOffBv.toNat, x / 2 < s.n_nets.toNat)
    (hf_max : flipCount flippedArr (symListAt rsPool mOffBv.toNat) ≤ arRMaxF)
    (hrpS_len : rpS.toNat + mlenBv.toNat + 1 ≤ rpoolS.length)
    (_hrpS_32 : rpS.toNat + mlenBv.toNat + 1 < 2 ^ 32)
    (hmS : (arCtxMem cx s ⋆ array (t := i32) s.rm rmS ⋆ array64 s.rl rlS ⋆
      array64 s.rh rhS ⋆ array (t := i32) s.rpool rpoolS ⋆
      buildRPass2Ro s ruleOff ruleN rsM rsL rsH rsPool flippedArr rmLen rpoolLen
        rm2 rl2 rh2 R) mS)
    (hAfterJ : ∀ (jJ kJ fiJ parJ : BitVec 32) (rpoolJ : List (BitVec 32)) (mJ : Mem 64),
      jJ.toNat = mlenBv.toNat + 1 →
      rpoolJ.length = rpoolS.length →
      kJ.toNat = ((symListAt rsPool mOffBv.toNat).foldl
        (expandStep flippedArr S.toNat) ([], 0, 0)).1.length + 1 →
      ((symListAt rsPool mOffBv.toNat).foldl
        (expandStep flippedArr S.toNat) ([], 0, 0)).1.length ≤ mlenBv.toNat →
      parJ.toNat = ((symListAt rsPool mOffBv.toNat).foldl
        (expandStep flippedArr S.toNat) ([], 0, 0)).2.2 % 2 →
      (∀ idx < rpS.toNat, rpoolJ.getD idx 0#32 = rpoolS.getD idx 0#32) →
      (∀ p < ((symListAt rsPool mOffBv.toNat).foldl
          (expandStep flippedArr S.toNat) ([], 0, 0)).1.length,
        (rpoolJ.getD (rpS.toNat + 1 + p) 0#32).toNat =
          ((symListAt rsPool mOffBv.toNat).foldl
            (expandStep flippedArr S.toNat) ([], 0, 0)).1.getD p 0) →
      (arCtxMem cx s ⋆ array (t := i32) s.rm rmS ⋆ array64 s.rl rlS ⋆ array64 s.rh rhS ⋆
        array (t := i32) s.rpool rpoolJ ⋆
        buildRPass2Ro s ruleOff ruleN rsM rsL rsH rsPool flippedArr rmLen rpoolLen
          rm2 rl2 rh2 R) mJ →
      wp Γ Q X (buildRPass2JAfterExpr Ji Js cx s.rs_pool
        (s.rs_pool + BitVec.setWidth 64 mOffBv * 4)
        (1#64 <<< ((fF.setWidth 64).toNat % 64)) s.rpool (s.rpool + rpS * 4) v off cnt fv_b any
        bt bw iC rpC nC mOffBv mlenBv cl ch fF jF rpS nS_cur jU S jJ kJ fiJ parJ) mJ) :
    wp Γ Q X (buildRPass2JExpr Ji Js cx s.rs_pool (s.rs_pool + BitVec.setWidth 64 mOffBv * 4)
      (1#64 <<< ((fF.setWidth 64).toNat % 64)) s.rpool (s.rpool + rpS * 4) v off cnt fv_b any
      bt bw iC rpC nC mOffBv mlenBv cl ch fF jF rpS nS_cur jU S) mS := by
  let Rro := buildRPass2Ro s ruleOff ruleN rsM rsL rsH rsPool flippedArr rmLen rpoolLen
    rm2 rl2 rh2 R
  obtain ⟨rrP, hrrP⟩ := buildRPass2Ro_rsPool (s := s) (ruleOff := ruleOff) (ruleN := ruleN)
    (rsM := rsM) (rsL := rsL) (rsH := rsH) (rsPool := rsPool) (flippedArr := flippedArr)
    (rmLen := rmLen) (rpoolLen := rpoolLen) (rm2 := rm2) (rl2 := rl2) (rh2 := rh2) (R := R)
  obtain ⟨rrFl, hrrFl⟩ := buildRPass2Ro_flipped (s := s) (ruleOff := ruleOff) (ruleN := ruleN)
    (rsM := rsM) (rsL := rsL) (rsH := rsH) (rsPool := rsPool) (flippedArr := flippedArr)
    (rmLen := rmLen) (rpoolLen := rpoolLen) (rm2 := rm2) (rl2 := rl2) (rh2 := rh2) (R := R)
  dsimp only [buildRPass2JExpr, buildRPass2SBranches, buildRPass2SExpr, buildRPass2P2Exit,
    buildRPass2EntryExpr]
  refine wp_loop_group (fun remJ ⟨jJ, kJ, fiJ, parJ, ⟨⟩⟩ mJ =>
      ∃ rpoolJ : List (BitVec 32),
        let st := (symListAt rsPool mOffBv.toNat |>.take (jJ.toNat - 1)).foldl
          (expandStep flippedArr S.toNat) ([], 0, 0)
        1 ≤ jJ.toNat ∧ jJ.toNat ≤ mlenBv.toNat + 1 ∧
        remJ = mlenBv.toNat + 1 - jJ.toNat ∧
        rpoolJ.length = rpoolS.length ∧
        kJ.toNat = st.1.length + 1 ∧
        st.1.length ≤ jJ.toNat - 1 ∧
        fiJ.toNat = st.2.1 ∧
        st.2.1 ≤ flipCount flippedArr ((symListAt rsPool mOffBv.toNat).take (jJ.toNat - 1)) ∧
        parJ.toNat = st.2.2 % 2 ∧
        (∀ idx < rpS.toNat, rpoolJ.getD idx 0#32 = rpoolS.getD idx 0#32) ∧
        (∀ p < st.1.length, (rpoolJ.getD (rpS.toNat + 1 + p) 0#32).toNat = st.1.getD p 0) ∧
        (arCtxMem cx s ⋆ array (t := i32) s.rm rmS ⋆ array64 s.rl rlS ⋆ array64 s.rh rhS ⋆
          array (t := i32) s.rpool rpoolJ ⋆ Rro) mJ)
    ?_ ?_
  · rintro Jj remJ ⟨jJ, kJ, fiJ, parJ, ⟨⟩⟩ mJ hrecJ
      ⟨rpoolJ, hjJ1, hjJle, hremJ, hrpoolJ, hkJ, haccJ_le, hfiJ, hfiJ_bd,
        hparJ, hprefJ, haccJ_eq, hmJ⟩
    c0_hsteps_nogrp
    · have hjJ_le_m : jJ.toNat ≤ mlenBv.toNat := hc
      clear hc
      have hmJ_lt : mOffBv.toNat + jJ.toNat < rsPool.length := by omega
      have hxj_eq : (rsPool[mOffBv.toNat + jJ.toNat]'hmJ_lt).toNat =
          (rsPool.getD (mOffBv.toNat + jJ.toNat) 0#32).toNat :=
        congrArg BitVec.toNat (getD_eq_getElem rsPool 0#32 hmJ_lt).symm
      have htake_j : (symListAt rsPool mOffBv.toNat).take jJ.toNat =
          (symListAt rsPool mOffBv.toNat).take (jJ.toNat - 1) ++
            [(rsPool[mOffBv.toNat + jJ.toNat]'hmJ_lt).toNat] := by
        rw [hxj_eq]; exact symListAt_take_succ hjJ1 (by rw [← hmlen_eq]; exact hjJ_le_m)
      have hxj_mem : (rsPool[mOffBv.toNat + jJ.toNat]'hmJ_lt).toNat ∈
          symListAt rsPool mOffBv.toNat := by
        simp only [symListAt, ← hmlen_eq, List.mem_map, List.mem_range]
        refine ⟨jJ.toNat - 1, by omega, ?_⟩
        rw [show mOffBv.toNat + 1 + (jJ.toNat - 1) = mOffBv.toNat + jJ.toNat by omega, ← hxj_eq]
      have hxj_half : (rsPool[mOffBv.toNat + jJ.toNat]'hmJ_lt).toNat / 2 < flippedArr.length :=
        Nat.lt_of_lt_of_le (hxs_bd _ hxj_mem) hfl_len
      refine wp_load_arr32_add (base := s.rs_pool) (off64 := BitVec.setWidth 64 mOffBv)
        (idx := jJ) (xs := rsPool)
        (R := arCtxMem cx s ⋆ array (t := i32) s.rm rmS ⋆ array64 s.rl rlS ⋆
          array64 s.rh rhS ⋆ array (t := i32) s.rpool rpoolJ ⋆ rrP)
        (by rfl) (by rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]; exact hmJ_lt)
        (sep_cast (by simpa only [Rro, hrrP] using hmJ) (by ac_rfl)) ?_
      c0_hsteps_nogrp
      let xJ := rsPool[(BitVec.setWidth 64 mOffBv).toNat + jJ.toNat]'(by
        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]; exact hmJ_lt)
      have hxJ_eq : xJ = rsPool[mOffBv.toNat + jJ.toNat]'hmJ_lt := by
        dsimp only [xJ]; simp [BitVec.toNat_setWidth]
      have hxJ_half : (xJ >>> 1#32).toNat < flippedArr.length := by
        rw [bv32_shr1_toNat, hxJ_eq]; exact hxj_half
      let stPrev := (symListAt rsPool mOffBv.toNat |>.take (jJ.toNat - 1)).foldl
        (expandStep flippedArr S.toNat) ([], 0, 0)
      have htake_fc : flipCount flippedArr ((symListAt rsPool mOffBv.toNat).take jJ.toNat) =
          flipCount flippedArr ((symListAt rsPool mOffBv.toNat).take (jJ.toNat - 1)) +
            (if flipCond flippedArr xJ.toNat then 1 else 0) := by
        rw [htake_j, flipCount_append, flipCount_cons, flipCount_nil, ← hxJ_eq]; simp
      have hjJ1_nat : (jJ + 1#32).toNat = jJ.toNat + 1 := by
        rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl,
          Nat.mod_eq_of_lt (by omega : jJ.toNat + 1 < 2 ^ 32)]
      have hfc_pref : flipCount flippedArr
          ((symListAt rsPool mOffBv.toNat).take (jJ.toNat - 1)) ≤
          flipCount flippedArr (symListAt rsPool mOffBv.toNat) := by
        conv =>
          rhs
          rw [← List.take_append_drop (jJ.toNat - 1) (symListAt rsPool mOffBv.toNat)]
        rw [flipCount_append]
        omega
      have hfiJ_64 : fiJ.toNat < 64 := by
        have : arRMaxF = 24 := rfl; omega
      refine wp_join_group (fun ⟨jP, fiP, parP, xP, ⟨⟩⟩ mP =>
          mP = mJ ∧
          let stNext := expandStep flippedArr S.toNat stPrev xJ.toNat
          jP = jJ ∧ fiP.toNat = stNext.2.1 ∧
          stNext.2.1 ≤ flipCount flippedArr ((symListAt rsPool mOffBv.toNat).take jJ.toNat) ∧
          parP.toNat = stNext.2.2 % 2 ∧
          dedupPush stPrev.1 xP.toNat = stNext.1 ∧
          (kJ.toNat > 1 → (rpoolJ.getD (rpS.toNat + (kJ - 1#32).toNat) 0#32).toNat =
            stPrev.1.getD (stPrev.1.length - 1) 0))
        ?_ ?_
      · rintro Jp ⟨jP, fiP, parP, xP, ⟨⟩⟩ mP
          ⟨hmP, hjP, hfiP, hfiP_bd, hparP, hdedup, hlastK⟩
        cases hmP; cases hjP
        let stNext := (symListAt rsPool mOffBv.toNat |>.take jJ.toNat).foldl
          (expandStep flippedArr S.toNat) ([], 0, 0)
        have hstNext_eq : expandStep flippedArr S.toNat stPrev xJ.toNat = stNext := by
          dsimp only [stNext, stPrev]
          rw [htake_j, List.foldl_append, List.foldl_cons, List.foldl_nil, hxJ_eq]
        rw [hstNext_eq] at hfiP hfiP_bd hparP hdedup
        have hstep_len : stNext.1.length ≤ jJ.toNat := by
          dsimp only [stNext]
          have h1 := expandFold_len_le flippedArr S.toNat
            ((symListAt rsPool mOffBv.toNat).take jJ.toNat) [] 0 0
          simp only [List.length_nil, Nat.zero_add, List.length_take] at h1; omega
        c0_hsteps_nogrp
        refine wp_join_group (fun (_ : Tup Val []) mK =>
            mK = mJ ∧ ¬ (1 < kJ.toNat ∧ stPrev.1.getLast? = some xP.toNat))
          ?_ ?_
        · rintro Jk _ mK ⟨hmK, hnotdup⟩
          cases hmK
          have hps := pass2_dedup_slice_ok (rpool := rpoolJ) (rp := rpS.toNat)
            (mlen := mlenBv.toNat) (acc := stPrev.1) (x := xP)
            (by omega) (by dsimp only [stPrev]; omega) haccJ_eq
          have hnotlast : ¬ stPrev.1.getLast? = some xP.toNat := by
            intro h
            by_cases hk1 : 1 < kJ.toNat
            · exact hnotdup ⟨hk1, h⟩
            · have hlen0 : stPrev.1.length = 0 := by dsimp only [stPrev]; omega
              rw [List.length_eq_zero_iff.mp hlen0] at h
              simp at h
          dsimp only at hps
          rw [ite_eq_right hnotlast, hdedup] at hps
          have hidx_store : rpS.toNat + kJ.toNat < rpoolJ.length := by omega
          have hkk1 : (kJ + 1#32).toNat = kJ.toNat + 1 := by
            rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl,
              Nat.mod_eq_of_lt (by omega : kJ.toNat + 1 < 2 ^ 32)]
          have hk64 : (kJ.setWidth 64).toNat = kJ.toNat := by
            rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
          c0_hsteps_nogrp
          have hmJ' : (arCtxMem cx s ⋆ array (t := i32) s.rm rmS ⋆ array64 s.rl rlS ⋆
              array64 s.rh rhS ⋆
              array (t := i32) s.rpool (rpoolJ.set (rpS.toNat + kJ.toNat) xP) ⋆ Rro) m := by
            rw [← hk64]; exact sep_cast hm (by ac_rfl)
          refine hrecJ (mlenBv.toNat + 1 - (jJ + 1#32).toNat)
            (jJ + 1#32, kJ + 1#32, fiP, parP, ⟨⟩) _ (by omega) ?_
          refine ⟨rpoolJ.set (rpS.toNat + kJ.toNat) xP, by omega, by omega, rfl,
            by simp [hrpoolJ], ?_, ?_, ?_, ?_, ?_, ?_, ?_, hmJ'⟩
          · rw [hjJ1_nat, Nat.add_sub_cancel]; refine hkk1.trans ?_
            change kJ.toNat + 1 = stNext.1.length + 1
            rw [hkJ, ← hdedup]
            simp only [dedupPush, ite_eq_right hnotlast, List.length_append, List.length_singleton]
            dsimp only [stPrev]
          · rw [hjJ1_nat, Nat.add_sub_cancel]; exact hstep_len
          · rw [hjJ1_nat, Nat.add_sub_cancel]; exact hfiP
          · rw [hjJ1_nat, Nat.add_sub_cancel]; exact hfiP_bd
          · rw [hjJ1_nat, Nat.add_sub_cancel]; exact hparP
          · intro idx hidx
            rw [← hprefJ idx hidx, getD_set_eq rpoolJ 0#32 xP hidx_store, ite_eq_right (by omega)]
          · rw [hjJ1_nat, Nat.add_sub_cancel]
            intro p hp
            rw [hkJ, show rpS.toNat + ((List.foldl (expandStep flippedArr S.toNat) ([], 0, 0)
              (List.take (jJ.toNat - 1) (symListAt rsPool mOffBv.toNat))).1.length + 1) =
              rpS.toNat + 1 + stPrev.1.length from by dsimp only [stPrev]; omega]
            exact hps.2.2.2 p hp
        · intro Jk hJk
          c0_hsteps_nogrp
          · have hk_gt1 : 1 < kJ.toNat := by assumption
            have h132 : (1#32 : BitVec 32).toNat = 1 := rfl
            have hk1_lt : rpS.toNat + (kJ - 1#32).toNat < rpoolJ.length := by
              rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by omega))]; omega
            have hlast_eq : (rpoolJ[rpS.toNat + (kJ - 1#32).toNat]'hk1_lt).toNat =
                stPrev.1.getD (stPrev.1.length - 1) 0 := by
              rw [← getD_eq_getElem rpoolJ 0#32 hk1_lt]; exact hlastK hk_gt1
            have hidx_k1 : (2 ^ 32 - BitVec.toNat (1 : BitVec 32) + kJ.toNat) % 2 ^ 32 =
                (kJ - 1#32).toNat := by
              rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by rw [h132]; omega))]
              change (2 ^ 32 - 1 + kJ.toNat) % 2 ^ 32 = kJ.toNat - 1
              omega
            have hc' : rpoolJ.getD (rpS.toNat + (kJ - 1#32).toNat) 0#32 = xP := by
              rw [← hidx_k1, getD_eq_getElem rpoolJ 0#32 (by rw [hidx_k1]; exact hk1_lt)]
              exact hc
            have hlen_pos : 0 < stPrev.1.length := by
              dsimp only [stPrev] at hkJ ⊢; omega
            have hdup : stPrev.1.getLast? = some xP.toNat := by
              rw [list_getLast?_some_eq stPrev.1 0 hlen_pos, ← hlast_eq,
                ← getD_eq_getElem rpoolJ 0#32 hk1_lt]
              exact congrArg some (congrArg BitVec.toNat hc')
            have hps := pass2_dedup_slice_ok (rpool := rpoolJ) (rp := rpS.toNat)
              (mlen := mlenBv.toNat) (acc := stPrev.1) (x := xP)
              (by omega) (by dsimp only [stPrev]; omega) haccJ_eq
            dsimp only at hps
            rw [ite_eq_left hdup, hdedup] at hps
            refine hrecJ (mlenBv.toNat + 1 - (jJ + 1#32).toNat)
              (jJ + 1#32, kJ, fiP, parP, ⟨⟩) mJ (by omega) ?_
            refine ⟨rpoolJ, by omega, by omega, rfl, hrpoolJ, ?_, ?_, ?_, ?_, ?_, hprefJ, ?_, hmJ⟩
            · rw [hjJ1_nat, Nat.add_sub_cancel]
              rw [← hdedup, dedupPush, ite_eq_left hdup]
              dsimp only [stPrev] at hkJ ⊢; exact hkJ
            · rw [hjJ1_nat, Nat.add_sub_cancel]; exact hstep_len
            · rw [hjJ1_nat, Nat.add_sub_cancel]; exact hfiP
            · rw [hjJ1_nat, Nat.add_sub_cancel]; exact hfiP_bd
            · rw [hjJ1_nat, Nat.add_sub_cancel]; exact hparP
            · rw [hjJ1_nat, Nat.add_sub_cancel]; exact hps.2.2.2
          · have hk_gt1 : 1 < kJ.toNat := by assumption
            have h132 : (1#32 : BitVec 32).toNat = 1 := rfl
            have hk1_lt : rpS.toNat + (kJ - 1#32).toNat < rpoolJ.length := by
              rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by omega))]; omega
            have hlast_eq : (rpoolJ[rpS.toNat + (kJ - 1#32).toNat]'hk1_lt).toNat =
                stPrev.1.getD (stPrev.1.length - 1) 0 := by
              rw [← getD_eq_getElem rpoolJ 0#32 hk1_lt]; exact hlastK hk_gt1
            have hidx_k1 : (2 ^ 32 - BitVec.toNat (1 : BitVec 32) + kJ.toNat) % 2 ^ 32 =
                (kJ - 1#32).toNat := by
              rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by rw [h132]; omega))]
              change (2 ^ 32 - 1 + kJ.toNat) % 2 ^ 32 = kJ.toNat - 1
              omega
            have hlen_pos : 0 < stPrev.1.length := by
              dsimp only [stPrev] at hkJ ⊢; omega
            refine hJk _ _ ⟨rfl, fun ⟨_, hgl⟩ => ?_⟩
            rw [list_getLast?_some_eq stPrev.1 0 hlen_pos, ← hlast_eq,
              ← getD_eq_getElem rpoolJ 0#32 hk1_lt] at hgl
            have hneg_getD : ¬ rpoolJ.getD (rpS.toNat + (kJ - 1#32).toNat) 0#32 = xP := by
              rw [← hidx_k1, getD_eq_getElem rpoolJ 0#32 (by rw [hidx_k1]; exact hk1_lt)]
              assumption
            exact hneg_getD (BitVec.eq_of_toNat_eq (Option.some.inj hgl))
          · have hnotlt : ¬ 1 < kJ.toNat := fun h =>
              (by assumption : ¬ (1#32 < kJ)) (BitVec.lt_def.mpr h)
            exact hJk _ _ ⟨rfl, fun ⟨hk_gt1, _⟩ => hnotlt hk_gt1⟩
      · intro Jp hJp
        c0_hsteps_nogrp
        · refine wp_load_arr8_idx (base := s.flipped) (i := xJ >>> 1#32) (xs := flippedArr)
            (R := arCtxMem cx s ⋆ array (t := i32) s.rm rmS ⋆ array64 s.rl rlS ⋆
              array64 s.rh rhS ⋆ array (t := i32) s.rpool rpoolJ ⋆ rrFl)
            ?_ hxJ_half (sep_cast (by simpa only [Rro, hrrFl] using hmJ) (by ac_rfl)) ?_
          · rfl
          c0_hsteps_nogrp
          · have hfl_cond : flipCond flippedArr xJ.toNat = true := by
              simp only [flipCond, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq]
              refine ⟨(bv32_and1_eq_zero_iff xJ).mp (by assumption), ?_⟩
              rw [getD_eq_getElem flippedArr 0#8 (by rw [← bv32_shr1_toNat xJ]; exact hxJ_half)]
              have hne : ¬ BitVec.setWidth 32
                  (flippedArr[xJ.toNat / 2 ^ (1 % 2 ^ 32)]'(by
                    simp; rw [← bv32_shr1_toNat xJ]; exact hxJ_half)) = BitVec.ofNat 32 0 := by
                assumption
              intro hz; apply hne; simp [hz]
            have hfiJ1_nat : (fiJ + 1#32).toNat = fiJ.toNat + 1 := by
              rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl,
                Nat.mod_eq_of_lt (by omega : fiJ.toNat + 1 < 2 ^ 32)]
            have hbit0 : (S.toNat / 2 ^ stPrev.2.1) % 2 = 0 := by
              have hzero : BitVec.setWidth 32 ((S >>> (fiJ.toNat % 64)) &&& 1#64) = 0#32 := by
                assumption
              have h1 := congrArg BitVec.toNat hzero
              rw [BitVec.toNat_setWidth, bv_c0_toNat_and_one_64, bv_c0_toNat_ushiftRight_nat,
                Nat.mod_eq_of_lt hfiJ_64] at h1
              dsimp only [stPrev]; rw [← hfiJ]; simpa using h1
            refine hrecJ (mlenBv.toNat + 1 - (jJ + 1#32).toNat)
              (jJ + 1#32, kJ, fiJ + 1#32, parJ, ⟨⟩) mJ (by omega) ?_
            have hstep : expandStep flippedArr S.toNat stPrev xJ.toNat =
                (stPrev.1, stPrev.2.1 + 1, stPrev.2.2) := by
              simp [expandStep, hfl_cond, hbit0]
            refine ⟨rpoolJ, by omega, by omega, rfl, hrpoolJ, ?_, ?_, ?_, ?_, ?_, hprefJ, ?_, hmJ⟩
            · rw [hjJ1_nat, Nat.add_sub_cancel, htake_j, List.foldl_append,
                List.foldl_cons, List.foldl_nil]
              change kJ.toNat = (expandStep _ _ stPrev xJ.toNat).1.length + 1
              rw [hstep]; exact hkJ
            · rw [hjJ1_nat, Nat.add_sub_cancel, htake_j, List.foldl_append,
                List.foldl_cons, List.foldl_nil]
              change (expandStep _ _ stPrev xJ.toNat).1.length ≤ jJ.toNat
              rw [hstep]; dsimp only [stPrev]; omega
            · rw [hjJ1_nat, Nat.add_sub_cancel, htake_j, List.foldl_append,
                List.foldl_cons, List.foldl_nil]
              change (fiJ + 1#32).toNat = (expandStep _ _ stPrev xJ.toNat).2.1
              rw [hstep, hfiJ1_nat, hfiJ]
            · rw [hjJ1_nat, Nat.add_sub_cancel, htake_j, List.foldl_append,
                List.foldl_cons, List.foldl_nil, ← hxJ_eq, hstep]
              dsimp only [stPrev] at hfiJ_bd ⊢
              rw [hxJ_eq, ← htake_j, htake_fc, hfl_cond]
              simp only [↓reduceIte]; exact Nat.succ_le_succ hfiJ_bd
            · rw [hjJ1_nat, Nat.add_sub_cancel, htake_j, List.foldl_append,
                List.foldl_cons, List.foldl_nil]
              change parJ.toNat = (expandStep _ _ stPrev xJ.toNat).2.2 % 2
              rw [hstep]; exact hparJ
            · rw [hjJ1_nat, Nat.add_sub_cancel, htake_j, List.foldl_append,
                List.foldl_cons, List.foldl_nil, ← hxJ_eq]
              change ∀ p < (expandStep _ _ stPrev xJ.toNat).1.length, _
              rw [hstep]; exact haccJ_eq
          · have hfl_cond : flipCond flippedArr xJ.toNat = true := by
              simp only [flipCond, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq]
              refine ⟨(bv32_and1_eq_zero_iff xJ).mp (by assumption), ?_⟩
              rw [getD_eq_getElem flippedArr 0#8 (by rw [← bv32_shr1_toNat xJ]; exact hxJ_half)]
              have hne : ¬ BitVec.setWidth 32
                  (flippedArr[xJ.toNat / 2 ^ (1 % 2 ^ 32)]'(by
                    simp; rw [← bv32_shr1_toNat xJ]; exact hxJ_half)) = BitVec.ofNat 32 0 := by
                assumption
              intro hz; apply hne; simp [hz]
            have hfiJ1_nat : (fiJ + 1#32).toNat = fiJ.toNat + 1 := by
              rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl,
                Nat.mod_eq_of_lt (by omega : fiJ.toNat + 1 < 2 ^ 32)]
            have hbit1 : (S.toNat / 2 ^ stPrev.2.1) % 2 ≠ 0 := by
              have hnz : ¬ BitVec.setWidth 32 ((S >>> (fiJ.toNat % 64)) &&& 1#64) = 0#32 := by
                assumption
              intro h0; apply hnz; apply BitVec.eq_of_toNat_eq
              rw [BitVec.toNat_setWidth, bv_c0_toNat_and_one_64, bv_c0_toNat_ushiftRight_nat,
                Nat.mod_eq_of_lt hfiJ_64]
              dsimp only [stPrev] at h0; rw [← hfiJ] at h0; simp [h0]
            have hxJ1_nat : (xJ + 1#32).toNat = xJ.toNat + 1 := by
              have hmod2 : xJ.toNat % 2 = 0 :=
                (bv32_and1_eq_zero_iff xJ).mp (by assumption)
              have hbd32 : xJ.toNat / 2 < 0x3FFFFFFF := by
                rw [hxJ_eq]; exact Nat.lt_of_lt_of_le (hxs_bd _ hxj_mem) hnn_bd
              rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl,
                Nat.mod_eq_of_lt (by omega : xJ.toNat + 1 < 2 ^ 32)]
            have hpar1_nat : (parJ ^^^ 1#32).toNat = (stPrev.2.2 ^^^ 1) % 2 := by
              rw [BitVec.toNat_xor, show (1#32 : BitVec 32).toNat = 1 from rfl, hparJ,
                nat_xor1_mod2]
              have hmod1 : stPrev.2.2 % 2 = 0 ∨ stPrev.2.2 % 2 = 1 := by omega
              dsimp only [stPrev] at hmod1
              rcases hmod1 with hp | hp
              · rw [hp]; rfl
              · rw [hp]; rfl
            c0_hsteps_nogrp
            have h132 : (1#32 : BitVec 32).toNat = 1 := rfl
            refine hJp _ _ ⟨rfl, rfl,
              hfiJ1_nat.trans (by simp [expandStep, hfl_cond, hbit1, stPrev, hfiJ]),
              ?_, ?_, ?_, ?_⟩
            · simp [expandStep, hfl_cond, hbit1, htake_fc]
              dsimp only [stPrev] at hfiJ_bd ⊢; omega
            · simp [expandStep, hfl_cond, hbit1, hpar1_nat]
            · change dedupPush stPrev.1 (xJ + 1#32).toNat =
                (expandStep flippedArr S.toNat stPrev xJ.toNat).1
              simp [expandStep, hfl_cond, hbit1, hxJ1_nat]
            · intro hk1
              have hk_sub : (kJ - 1#32).toNat = kJ.toNat - 1 := by
                rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by rw [h132]; omega)), h132]
              rw [hk_sub, hkJ, Nat.add_sub_cancel]
              have hlen_pos : 0 < stPrev.1.length := by
                dsimp only [stPrev] at hkJ ⊢; omega
              rw [show rpS.toNat + stPrev.1.length = rpS.toNat + 1 + (stPrev.1.length - 1) by omega]
              exact haccJ_eq (stPrev.1.length - 1)
                (by dsimp only [stPrev] at hlen_pos; exact Nat.sub_lt hlen_pos Nat.one_pos)
          · have hfl_cond : flipCond flippedArr xJ.toNat = false := by
              simp only [flipCond, Bool.and_eq_false_iff, bne_eq_false_iff_eq]
              right
              rw [getD_eq_getElem flippedArr 0#8 (by rw [← bv32_shr1_toNat xJ]; exact hxJ_half)]
              apply BitVec.eq_of_toNat_eq
              have ht := congrArg BitVec.toNat
                (by assumption : BitVec.setWidth 32
                  (flippedArr[xJ.toNat / 2 ^ (1 % 2 ^ 32)]'(by
                    simp; rw [← bv32_shr1_toNat xJ]; exact hxJ_half)) = BitVec.ofNat 32 0)
              rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt
                (Nat.lt_of_lt_of_le (BitVec.isLt _) (by decide))] at ht
              simpa using ht
            c0_hsteps_nogrp
            have h132 : (1#32 : BitVec 32).toNat = 1 := rfl
            refine hJp _ _ ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
            · simp [expandStep, hfl_cond, stPrev, hfiJ]
            · simp [expandStep, hfl_cond, htake_fc]
              dsimp only [stPrev] at hfiJ_bd ⊢; omega
            · simp [expandStep, hfl_cond, stPrev, hparJ]
            · simp only [expandStep, hfl_cond, stPrev]; dsimp only [xJ]; simp
            · intro hk1
              have hk_sub : (kJ - 1#32).toNat = kJ.toNat - 1 := by
                rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by rw [h132]; omega)), h132]
              rw [hk_sub, hkJ, Nat.add_sub_cancel]
              have hlen_pos : 0 < stPrev.1.length := by
                dsimp only [stPrev] at hkJ ⊢; omega
              rw [show rpS.toNat + stPrev.1.length = rpS.toNat + 1 + (stPrev.1.length - 1) by omega]
              exact haccJ_eq (stPrev.1.length - 1)
                (by dsimp only [stPrev] at hlen_pos; exact Nat.sub_lt hlen_pos Nat.one_pos)
        · have hfl_cond : flipCond flippedArr xJ.toNat = false := by
            simp only [flipCond, Bool.and_eq_false_iff, beq_eq_false_iff_ne]
            left; intro hmod
            have hne : ¬ (rsPool[mOffBv.toNat + jJ.toNat]'hmJ_lt) &&& 1#32 = 0#32 := by assumption
            exact hne (by rw [← hxJ_eq]; exact (bv32_and1_eq_zero_iff xJ).mpr hmod)
          c0_hsteps_nogrp
          have h132 : (1#32 : BitVec 32).toNat = 1 := rfl
          refine hJp _ _ ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
          · simp [expandStep, hfl_cond, stPrev, hfiJ]
          · simp [expandStep, hfl_cond, htake_fc]
            dsimp only [stPrev] at hfiJ_bd ⊢; omega
          · simp [expandStep, hfl_cond, stPrev, hparJ]
          · simp only [expandStep, hfl_cond, stPrev]; dsimp only [xJ]; simp
          · intro hk1
            have hk_sub : (kJ - 1#32).toNat = kJ.toNat - 1 := by
              rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by rw [h132]; omega)), h132]
            rw [hk_sub, hkJ, Nat.add_sub_cancel]
            have hlen_pos : 0 < stPrev.1.length := by
              dsimp only [stPrev] at hkJ ⊢; omega
            rw [show rpS.toNat + stPrev.1.length = rpS.toNat + 1 + (stPrev.1.length - 1) by omega]
            exact haccJ_eq (stPrev.1.length - 1)
              (by dsimp only [stPrev] at hlen_pos; exact Nat.sub_lt hlen_pos Nat.one_pos)
    · have hjJ_eq : jJ.toNat = mlenBv.toNat + 1 := by
        have := BitVec.not_le.mp hc; omega
      have htake_all : (symListAt rsPool mOffBv.toNat).take (jJ.toNat - 1) =
          symListAt rsPool mOffBv.toNat := by
        rw [hjJ_eq, Nat.add_sub_cancel]
        apply List.take_of_length_le
        simp only [symListAt, ← hmlen_eq, List.length_map, List.length_range, le_refl]
      let stEnd := (symListAt rsPool mOffBv.toNat).foldl
        (expandStep flippedArr S.toNat) ([], 0, 0)
      have hstEnd_len : stEnd.1.length ≤ mlenBv.toNat := by
        dsimp only [stEnd]; rw [← htake_all]; exact Nat.le_trans haccJ_le (by omega)
      exact hAfterJ jJ kJ fiJ parJ rpoolJ mJ hjJ_eq hrpoolJ
        (by rw [htake_all] at hkJ; exact hkJ) hstEnd_len
        (by rw [htake_all] at hparJ; exact hparJ) hprefJ
        (fun p hp => by rw [← htake_all] at hp ⊢; exact haccJ_eq p hp)
        hmJ
  · intro J hJ; c0_hsteps_nogrp
    have h132 : (1#32 : BitVec 32).toNat = 1 := rfl
    exact hJ mlenBv.toNat (1#32, 1#32, 0#32, 0#32, ⟨⟩) mS
      ⟨rpoolS, by omega, by omega, by omega, rfl, rfl, by simp, rfl, by simp, rfl,
        fun _ _ => rfl, fun _ hp => by simp at hp, hmS⟩

private theorem buildR_pass2_S_wp (Γ : T.Env)
    {Ji : Cont [.bits 32, .bits 64, .bits 32]}
    (hCneg : ∀ xs m Q X, arCnegSpec xs m Q X → Γ "ar_cneg" [i64, i64, i64] [i64, i64] xs m Q X)
    {cx : BitVec 64} {v off cnt : BitVec 32} {fv_b any : Bool} {bt bw : BitVec 64}
    {iC : BitVec 32} {rpC : BitVec 64} {nC mOffBv mlenBv : BitVec 32} {cl ch : BitVec 64}
    {fF jF : BitVec 32} {s : ArCtxState} {ruleOff ruleN rsM : List (BitVec 32)}
    {rsL rsH : List (BitVec 64)} {rsPool : List (BitVec 32)} {flippedArr : List (BitVec 8)}
    {rm rmC rm2 : List (BitVec 32)} {rl rh rlC rhC rl2 rh2 : List (BitVec 64)}
    {rpool rpoolC : List (BitVec 32)} {R : Mem 64 → Prop} {mC : Mem 64}
    {Q : Post [.bool]} {X : XPost}
    (hnn_bd : s.n_nets.toNat ≤ 0x3FFFFFFF) (hfl_len : s.n_nets.toNat ≤ flippedArr.length)
    (hMasks : MasksOk s.modW s.mlo s.mhi)
    (hrmC : rmC.length = rm.length) (hrlC : rlC.length = rl.length)
    (hrhC : rhC.length = rh.length) (hrpoolC : rpoolC.length = rpool.length)
    (hrm_len : s.rcap.toNat ≤ rm.length) (hrl_len : s.rcap.toNat ≤ rl.length)
    (hrh_len : s.rcap.toNat ≤ rh.length) (hrpool_len : s.rpcap.toNat ≤ rpool.length)
    (hrpcap_32 : s.rpcap.toNat < 2 ^ 32)
    (hmlen_eq : mlenBv = rsPool.getD mOffBv.toNat 0#32)
    (hmlen_32 : mlenBv.toNat + 1 < 2 ^ 32)
    (hmlen_end : mOffBv.toNat + mlenBv.toNat + 1 ≤ rsPool.length)
    (hxs_bd : ∀ x ∈ symListAt rsPool mOffBv.toNat, x / 2 < s.n_nets.toNat)
    (hxsSorted : MonoSorted rsPool mOffBv.toNat)
    (hfF_eq : fF.toNat = flipCount flippedArr (symListAt rsPool mOffBv.toNat))
    (hf_max : flipCount flippedArr (symListAt rsPool mOffBv.toNat) ≤ arRMaxF)
    (hnC_bd : nC.toNat + 2 ^ flipCount flippedArr (symListAt rsPool mOffBv.toNat) ≤ s.rcap.toNat)
    (hrpC_bd : rpC.toNat + 2 ^ flipCount flippedArr (symListAt rsPool mOffBv.toNat) *
      (mlenBv.toNat + 1) ≤ s.rpcap.toNat)
    (hSlC : ∀ r < nC.toNat, MonoSliceOk rpoolC (rmC.getD r 0#32).toNat rpC.toNat ∧
      (rpoolC.getD (rmC.getD r 0#32).toNat 0#32).toNat + 1 < 2 ^ 32)
    (hSortedC : ∀ r < nC.toNat, MonoSorted rpoolC (rmC.getD r 0#32).toNat)
    (hWC : monoTotalWords rpoolC rmC nC.toNat = rpC.toNat)
    (hSbC : SymsBound rpoolC rmC nC.toNat s.n_nets.toNat)
    (hmC : (arCtxMem cx s ⋆ array (t := i32) s.rm rmC ⋆ array64 s.rl rlC ⋆
      array64 s.rh rhC ⋆ array (t := i32) s.rpool rpoolC ⋆
      buildRPass2Ro s ruleOff ruleN rsM rsL rsH rsPool flippedArr rm.length rpool.length
        rm2 rl2 rh2 R) mC)
    (hAfterS : ∀ (Js : Cont [.bits 64, .bits 32, .bits 32, .bits 64])
        (rpS : BitVec 64) (nS_cur jU : BitVec 32) (S : BitVec 64)
        (rmS : List (BitVec 32)) (rlS rhS : List (BitVec 64)) (rpoolS : List (BitVec 32))
        (mS : Mem 64),
      S.toNat = 2 ^ flipCount flippedArr (symListAt rsPool mOffBv.toNat) →
      rmS.length = rm.length → rlS.length = rl.length →
      rhS.length = rh.length → rpoolS.length = rpool.length →
      nS_cur.toNat = nC.toNat + 2 ^ flipCount flippedArr (symListAt rsPool mOffBv.toNat) →
      rpS.toNat ≤ rpC.toNat +
        2 ^ flipCount flippedArr (symListAt rsPool mOffBv.toNat) * (mlenBv.toNat + 1) →
      (∀ r < nS_cur.toNat, MonoSliceOk rpoolS (rmS.getD r 0#32).toNat rpS.toNat ∧
        (rpoolS.getD (rmS.getD r 0#32).toNat 0#32).toNat + 1 < 2 ^ 32) →
      (∀ r < nS_cur.toNat, MonoSorted rpoolS (rmS.getD r 0#32).toNat) →
      monoTotalWords rpoolS rmS nS_cur.toNat = rpS.toNat →
      SymsBound rpoolS rmS nS_cur.toNat s.n_nets.toNat →
      (∀ σ : Nat → Bool, (∀ w < s.n_nets.toNat, σ (2 * w + 1) = !(σ (2 * w))) →
        polyEval s.modW σ rpoolS rmS rlS rhS nS_cur.toNat =
          polyEval s.modW σ rpoolC rmC rlC rhC nC.toNat +
            expandSum s.modW σ flippedArr (coeff128 s.modW cl ch) []
              (if fv_b then 1 else 0) (symListAt rsPool mOffBv.toNat)) →
      (arCtxMem cx s ⋆ array (t := i32) s.rm rmS ⋆ array64 s.rl rlS ⋆ array64 s.rh rhS ⋆
        array (t := i32) s.rpool rpoolS ⋆
        buildRPass2Ro s ruleOff ruleN rsM rsL rsH rsPool flippedArr rm.length rpool.length
          rm2 rl2 rh2 R) mS →
      wp Γ Q X (buildRPass2SBranches Ji Js cx s.rs_pool
        (s.rs_pool + BitVec.setWidth 64 mOffBv * 4)
        (1#64 <<< ((fF.setWidth 64).toNat % 64)) v off cnt fv_b any bt bw iC rpC nC mOffBv mlenBv
        cl ch fF jF rpS nS_cur jU S).2 mS) :
    wp Γ Q X (buildRPass2SExpr Ji cx s.rs_pool (s.rs_pool + BitVec.setWidth 64 mOffBv * 4)
      (1#64 <<< ((fF.setWidth 64).toNat % 64)) v off cnt fv_b any bt bw iC rpC nC mOffBv mlenBv
      cl ch fF jF) mC := by
  let Rro := buildRPass2Ro s ruleOff ruleN rsM rsL rsH rsPool flippedArr rm.length rpool.length
    rm2 rl2 rh2 R
  let f_tgt := flipCount flippedArr (symListAt rsPool mOffBv.toNat)
  let nSBv : BitVec 64 := 1#64 <<< ((fF.setWidth 64).toNat % 64)
  have hnS_nat : nSBv.toNat = 2 ^ f_tgt := by
    have hf_lt : fF.toNat < 64 := by rw [hfF_eq]; exact Nat.lt_of_le_of_lt hf_max (by decide)
    have hff64 : fF.toNat < 2 ^ 64 := Nat.lt_trans hf_lt (by decide)
    have hf64 : (fF.setWidth 64).toNat % 64 = fF.toNat := by
      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt hff64, Nat.mod_eq_of_lt hf_lt]
    dsimp only [nSBv]
    rw [hf64, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
      show (1#64 : BitVec 64).toNat = 1 from rfl, Nat.one_mul,
      Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hf_lt), hfF_eq]
  dsimp only [buildRPass2SExpr, buildRPass2P2Exit, buildRPass2EntryExpr]
  refine wp_loop_group (fun remS ⟨rpS, nS_cur, _jU, S, ⟨⟩⟩ mS =>
      ∃ (rmS : List (BitVec 32)) (rlS rhS : List (BitVec 64)) (rpoolS : List (BitVec 32)),
        S.toNat ≤ nSBv.toNat ∧ remS = nSBv.toNat - S.toNat ∧
        rmS.length = rm.length ∧ rlS.length = rl.length ∧ rhS.length = rh.length ∧
        rpoolS.length = rpool.length ∧
        nS_cur.toNat = nC.toNat + S.toNat ∧
        rpS.toNat ≤ rpC.toNat + S.toNat * (mlenBv.toNat + 1) ∧
        (∀ r < nS_cur.toNat, MonoSliceOk rpoolS (rmS.getD r 0#32).toNat rpS.toNat ∧
          (rpoolS.getD (rmS.getD r 0#32).toNat 0#32).toNat + 1 < 2 ^ 32) ∧
        (∀ r < nS_cur.toNat, MonoSorted rpoolS (rmS.getD r 0#32).toNat) ∧
        monoTotalWords rpoolS rmS nS_cur.toNat = rpS.toNat ∧
        SymsBound rpoolS rmS nS_cur.toNat s.n_nets.toNat ∧
        (∀ σ : Nat → Bool, (∀ w < s.n_nets.toNat, σ (2 * w + 1) = !(σ (2 * w))) →
          polyEval s.modW σ rpoolS rmS rlS rhS nS_cur.toNat =
            polyEval s.modW σ rpoolC rmC rlC rhC nC.toNat +
              (List.range S.toNat).foldl (fun acc kS =>
                acc + expandTermEval s.modW σ flippedArr
                  (coeff128 s.modW cl ch) kS [] 0 (if fv_b then 1 else 0)
                  (symListAt rsPool mOffBv.toNat)) 0#(s.modW)) ∧
        (arCtxMem cx s ⋆ array (t := i32) s.rm rmS ⋆ array64 s.rl rlS ⋆
          array64 s.rh rhS ⋆ array (t := i32) s.rpool rpoolS ⋆ Rro) mS)
    ?_ ?_
  · rintro Js remS ⟨rpS, nS_cur, jU, S, ⟨⟩⟩ mS hrecS
      ⟨rmS, rlS, rhS, rpoolS, hS_le, hremS, hrmS, hrlS, hrhS, hrpoolS, hnS_cur,
        hrpS_bd, hSlS, hSortedS, hWS, hSbS, hEvS, hmS⟩
    c0_hsteps_nogrp
    · have hS_pow : S.toNat < 2 ^ f_tgt := by
        have hf_lt : fF.toNat < 64 := by rw [hfF_eq]; exact Nat.lt_of_le_of_lt hf_max (by decide)
        have hpow_lt : 2 ^ fF.toNat < 2 ^ 64 := Nat.pow_lt_pow_right (by decide : 1 < 2) hf_lt
        dsimp only [f_tgt]
        rw [← hfF_eq]
        simpa [Nat.mod_eq_of_lt hf_lt, Nat.mod_eq_of_lt hpow_lt] using hc
      have hS_lt : S.toNat < nSBv.toNat := by rw [hnS_nat]; exact hS_pow
      have hS1_mul : (S.toNat + 1) * (mlenBv.toNat + 1) ≤ 2 ^ f_tgt * (mlenBv.toNat + 1) :=
        Nat.mul_le_mul_right _ (by omega)
      dsimp only [f_tgt] at hS_pow hS1_mul
      have hrpS_end_bd : rpS.toNat + (mlenBv.toNat + 1) ≤ s.rpcap.toNat := by
        have hmul_s : rpS.toNat + (mlenBv.toNat + 1) ≤
            rpC.toNat + S.toNat * (mlenBv.toNat + 1) + (mlenBv.toNat + 1) := by omega
        rw [Nat.add_assoc, ← Nat.succ_mul, Nat.succ_eq_add_one] at hmul_s; omega
      have hrpS_len : rpS.toNat + mlenBv.toNat + 1 ≤ rpoolS.length := by omega
      have hrpS_32 : rpS.toNat + mlenBv.toNat + 1 < 2 ^ 32 := by omega
      have hnS_lt_rcap : nS_cur.toNat < s.rcap.toNat := by omega
      have hnS_rm : nS_cur.toNat < rmS.length := by omega
      have hnS_rl : nS_cur.toNat < rlS.length := by omega
      have hnS_rh : nS_cur.toNat < rhS.length := by omega
      refine buildR_pass2_J_wp Γ (Ji := Ji) (Js := Js) (v := v) (off := off) (cnt := cnt)
        (fv_b := fv_b) (any := any) (bt := bt) (bw := bw) (iC := iC) (rpC := rpC) (nC := nC)
        (cl := cl) (ch := ch) (fF := fF) (jF := jF) (nS_cur := nS_cur) (jU := jU) (S := S)
        hnn_bd hfl_len hmlen_eq hmlen_32 hmlen_end hxs_bd hf_max hrpS_len hrpS_32 hmS ?_
      intro jJ kJ fiJ parJ rpoolJ mJ hjJ_eq hrpoolJ hkJ hstEnd_len hparJ hprefJ haccJ_eq hmJ
      let stEnd := (symListAt rsPool mOffBv.toNat).foldl
        (expandStep flippedArr S.toNat) ([], 0, 0)
      have hstEnd_32 : stEnd.1.length < 2 ^ 32 := Nat.lt_of_le_of_lt hstEnd_len (by omega)
      have hk1_sub : kJ - 1#32 = BitVec.ofNat 32 stEnd.1.length := by
        have h132 : (1#32 : BitVec 32).toNat = 1 := rfl
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by rw [h132]; omega)), h132,
          BitVec.toNat_ofNat, Nat.mod_eq_of_lt hstEnd_32, hkJ]
        dsimp only [stEnd]; omega
      have hrpS_lt : rpS.toNat < rpoolJ.length := by omega
      dsimp only [buildRPass2JAfterExpr, buildRPass2JExpr, buildRPass2SBranches,
        buildRPass2SExpr, buildRPass2P2Exit, buildRPass2EntryExpr]
      c0_hsteps_nogrp
      let rpool1 := rpoolJ.set rpS.toNat (kJ - 1#32)
      refine wp_join_group (fun ⟨fvu, ⟨⟩⟩ mFvu =>
          mFvu = m ∧ fvu = if fv_b then 1#32 else 0#32) ?_ ?_
      · rintro Jfv ⟨fvu, ⟨⟩⟩ mFvu ⟨hmFvu, hfvu⟩
        cases hmFvu; cases hfvu
        c0_hsteps_nogrp
        refine wp_join_group (fun ⟨lFin, hFin, ⟨⟩⟩ mFin =>
            mFin = m ∧ coeff128 s.modW lFin hFin =
              if (stEnd.2.2 ^^^ (if fv_b then 1 else 0)) % 2 = 1 then
                -coeff128 s.modW cl ch
              else coeff128 s.modW cl ch)
          ?_ ?_
        · rintro Jlh ⟨lFin, hFin, ⟨⟩⟩ mFin ⟨hmFin, hCoeff⟩
          cases hmFin
          c0_hsteps_nogrp
          have hnS64 : (nS_cur.setWidth 64).toNat = nS_cur.toNat := by
            rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt
              (lt_trans nS_cur.isLt (by decide : 2 ^ 32 < 2 ^ 64))]
          have hm3 : (arCtxMem cx s ⋆
              array (t := i32) s.rm (rmS.set nS_cur.toNat (rpS.setWidth 32)) ⋆
              array64 s.rl (rlS.set nS_cur.toNat lFin) ⋆
              array64 s.rh (rhS.set nS_cur.toNat hFin) ⋆
              array (t := i32) s.rpool rpool1 ⋆ Rro) m := by
            have hzero : rpS.toNat + (0#64).toNat = rpS.toNat := rfl
            have hm0 := hm; rw [hzero, hnS64] at hm0
            dsimp only [rpool1, Rro]
            simpa only [ExtHashMap.sep_emp] using sep_cast hm0 (by ac_rfl)
          have hrpS_setW : rpS.setWidth 32 = BitVec.ofNat 32 rpS.toNat := by
            apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_setWidth]
          have hdone := pass2_S_done_inv (nOut := s.modW) (bd := s.n_nets.toNat)
            flippedArr (rsPool := rsPool) (mOff := mOffBv.toNat) (mlen := mlenBv.toNat)
            (S := S.toNat) (fv_b := fv_b) (rpool0 := rpoolJ) (rpool1 := rpool1) (rmS := rmS)
            (rlS := rlS) (rhS := rhS) (rpS := rpS.toNat) (nS := nS_cur.toNat)
            (cl := cl) (ch := ch) (lFin := lFin) (hFin := hFin)
            hxs_bd hxsSorted (congrArg BitVec.toNat hmlen_eq) (by rw [hrpoolJ]; exact hrpS_len)
            hrpS_32 hnS_rm hnS_rl hnS_rh
            (fun r hr => by
              obtain ⟨h1, h2⟩ := hSlS r hr
              have hrp_r := hprefJ _ h1.1
              exact ⟨⟨h1.1, by rw [hrp_r]; exact h1.2⟩, by rw [hrp_r]; exact h2⟩)
            (fun r hr => monoSorted_congr (by
              have h1 := (hSlS r hr).1
              have h12 := h1.2
              simp only [symListAt, hprefJ _ h1.1]
              exact List.map_congr_left fun p hp => by
                have hplt := List.mem_range.mp hp
                rw [hprefJ _ (by omega)]) (hSortedS r hr))
            (by
              rw [← hWS]
              exact monoTotalWords_congr_prefix (fun r hr => (hSlS r hr).1) hprefJ
                (fun _ _ => rfl))
            (SymsBound.congr_prefix hSbS (fun r hr => (hSlS r hr).1) hprefJ (fun _ _ => rfl))
            hstEnd_len haccJ_eq (by dsimp only [rpool1]; rw [hk1_sub]) hCoeff
          rw [← hrpS_setW] at hdone
          have hpe_eqS : ∀ σ, (∀ w < s.n_nets.toNat, σ (2 * w + 1) = !(σ (2 * w))) →
              polyEval s.modW σ rpoolJ rmS rlS rhS nS_cur.toNat =
                polyEval s.modW σ rpoolS rmS rlS rhS nS_cur.toNat :=
            fun σ _ => polyEval_congr_prefix s.modW σ (fun r hr => (hSlS r hr).1)
              hprefJ (fun _ _ => ⟨rfl, rfl, rfl⟩)
          have hkJ_bd : kJ.toNat ≤ mlenBv.toNat + 1 := by omega
          have hrp_next : (rpS + kJ.setWidth 64).toNat = rpS.toNat + stEnd.1.length + 1 := by
            have hk64 : (kJ.setWidth 64).toNat = kJ.toNat := by
              rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
            rw [BitVec.toNat_add, hk64, Nat.mod_eq_of_lt (by omega)]
            dsimp only [stEnd] at hkJ ⊢; omega
          have hn_next : (nS_cur + 1#32).toNat = nS_cur.toNat + 1 := by
            rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl,
              Nat.mod_eq_of_lt (by omega : nS_cur.toNat + 1 < 2 ^ 32)]
          have hS_next : (S + 1#64).toNat = S.toNat + 1 := by
            rw [BitVec.toNat_add, show (1#64 : BitVec 64).toNat = 1 from rfl,
              Nat.mod_eq_of_lt (by omega : S.toNat + 1 < 2 ^ 64)]
          refine hrecS (nSBv.toNat - (S + 1#64).toNat)
            (rpS + kJ.setWidth 64, nS_cur + 1#32, jJ, S + 1#64, ⟨⟩) m
            (by rw [hS_next]; omega) ?_
          refine ⟨rmS.set nS_cur.toNat (rpS.setWidth 32), rlS.set nS_cur.toNat lFin,
            rhS.set nS_cur.toNat hFin, rpool1, by rw [hS_next]; omega, by rw [hS_next],
            by simp [hrmS], by simp [hrlS], by simp [hrhS],
            by rw [hdone.1, hrpoolJ, hrpoolS], by rw [hn_next, hnS_cur, hS_next]; omega,
            by rw [hrp_next, hS_next, Nat.succ_mul]; dsimp only [stEnd]; omega,
            ?_, ?_, ?_, ?_, ?_, sep_cast hm3 (by ac_rfl)⟩
          · rw [hn_next, hrp_next]; exact hdone.2.2.1
          · rw [hn_next]; exact hdone.2.2.2.1
          · rw [hn_next, hrp_next]; exact hdone.2.2.2.2.1
          · rw [hn_next]; exact hdone.2.2.2.2.2.1
          · intro σ hσ
            rw [hn_next, hS_next, hdone.2.2.2.2.2.2 σ, hpe_eqS σ hσ, hEvS σ hσ,
              List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, BitVec.add_assoc]
        · intro Jlh hJlh
          c0_hsteps_nogrp
          · have hpar_ne : (parJ.toNat ^^^ (if fv_b then 1 else 0)) % 2 = 1 := by
              have h1 : (parJ ^^^ (if fv_b then 1#32 else 0#32)).toNat ≠ 0 := by
                intro hz
                exact ‹¬ (parJ ^^^ if fv_b = true then 1#32 else 0#32) = 0#32›
                  (BitVec.eq_of_toNat_eq hz)
              rw [BitVec.toNat_xor] at h1
              have hlt2 : (if fv_b then 1#32 else 0#32).toNat = (if fv_b then 1 else 0) := by
                cases fv_b <;> rfl
              rw [hlt2] at h1
              have hpar_cases : parJ.toNat = 0 ∨ parJ.toNat = 1 := by
                rw [hparJ]; have := Nat.mod_lt stEnd.2.2 (by decide : 0 < 2); omega
              cases fv_b <;> rcases hpar_cases with hp | hp <;> simp [hp] at h1 ⊢ <;> decide
            have hpar_cond : (stEnd.2.2 ^^^ (if fv_b then 1 else 0)) % 2 = 1 := by
              dsimp only [stEnd]
              cases fv_b
              · simp at hpar_ne ⊢; omega
              · simp only [↓reduceIte, nat_xor1_mod2]; simp only [← hparJ]
                simp at hpar_ne ⊢; omega
            c0_hsteps_nogrp
            have hmJ'' : (arCtxMem cx s ⋆ array (t := i32) s.rm rmS ⋆ array64 s.rl rlS ⋆
                array64 s.rh rhS ⋆ array (t := i32) s.rpool rpool1 ⋆ Rro) m := by
              have hzero : rpS.toNat + (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 0)).toNat =
                  rpS.toNat := by
                rw [BitVec.toNat_ofNat, Nat.zero_mod, Nat.add_zero]
              have hm0 := hm; rw [hzero] at hm0
              dsimp only [rpool1, Rro]
              simpa only [ExtHashMap.sep_emp] using sep_cast hm0 (by ac_rfl)
            refine head_wp_call ?_ (hCneg (cx, cl, ch, ⟨⟩) m _ _
              ⟨s, array (t := i32) s.rm rmS ⋆ array64 s.rl rlS ⋆ array64 s.rh rhS ⋆
                array (t := i32) s.rpool rpool1 ⋆ Rro,
                hMasks, sep_cast hmJ'' (by ac_rfl), fun lo hi hcoeff => ?_⟩)
            · rfl
            · c0_hsteps_nogrp; exact hJlh _ _ ⟨rfl, by simp [hpar_cond, hcoeff]⟩
          · have hpar_eq : (parJ.toNat ^^^ (if fv_b then 1 else 0)) % 2 ≠ 1 := by
              have h0 := congrArg BitVec.toNat
                ‹(parJ ^^^ if fv_b = true then 1#32 else 0#32) = 0#32›
              rw [BitVec.toNat_xor] at h0
              have hlt2 : (if fv_b then 1#32 else 0#32).toNat = (if fv_b then 1 else 0) := by
                cases fv_b <;> rfl
              rw [hlt2] at h0
              have hpar_cases : parJ.toNat = 0 ∨ parJ.toNat = 1 := by
                rw [hparJ]; have := Nat.mod_lt stEnd.2.2 (by decide : 0 < 2); omega
              cases fv_b <;> rcases hpar_cases with hp | hp <;> simp [hp] at h0 ⊢ <;> decide
            have hpar_cond : (stEnd.2.2 ^^^ (if fv_b then 1 else 0)) % 2 ≠ 1 := by
              dsimp only [stEnd]
              cases fv_b
              · simp at hpar_eq ⊢; omega
              · simp only [↓reduceIte, nat_xor1_mod2]; simp only [← hparJ]
                simp at hpar_eq ⊢; omega
            c0_hsteps_nogrp; exact hJlh _ _ ⟨rfl, by simp [hpar_cond]⟩
      · intro Jfv hJfv
        c0_hsteps_nogrp
        · have ht : fv_b = true := by assumption
          exact hJfv _ _ ⟨rfl, by simp [ht]⟩
        · have hf : fv_b = false := by assumption
          exact hJfv _ _ ⟨rfl, by simp [hf]⟩
    · have hS_eq : S.toNat = 2 ^ f_tgt := by
        have hf_lt : fF.toNat < 64 := by rw [hfF_eq]; exact Nat.lt_of_le_of_lt hf_max (by decide)
        have hpow_lt : 2 ^ fF.toNat < 2 ^ 64 := Nat.pow_lt_pow_right (by decide : 1 < 2) hf_lt
        have hge : 2 ^ f_tgt ≤ S.toNat := by
          dsimp only [f_tgt]; rw [← hfF_eq]
          simpa [Nat.mod_eq_of_lt hf_lt, Nat.mod_eq_of_lt hpow_lt] using hc
        have : S.toNat ≤ 2 ^ f_tgt := by rw [← hnS_nat]; exact hS_le
        omega
      exact hAfterS Js rpS nS_cur jU S rmS rlS rhS rpoolS mS hS_eq hrmS hrlS hrhS hrpoolS
        (by rw [hnS_cur, hS_eq]) (by rw [← hS_eq]; exact hrpS_bd) hSlS hSortedS hWS hSbS
        (fun σ hσ => by rw [hEvS σ hσ, hS_eq]; rfl) hmS
  · intro J hJ; c0_hsteps_nogrp
    exact hJ nSBv.toNat (rpC, nC, jF, 0#64, ⟨⟩) mC
      ⟨rmC, rlC, rhC, rpoolC, Nat.zero_le _, rfl, hrmC, hrlC, hrhC, hrpoolC, by simp,
        by simp, hSlC, hSortedC, hWC, hSbC, fun σ _ => by simp, hmC⟩

/-- Pass 2 (`bounds checks`, `fv_b` init, `i < cnt` expansion loops) WP for `ar_build_R`. -/
theorem buildR_pass2_wp (Γ : T.Env)
    (hCneg : ∀ xs m Q X, arCnegSpec xs m Q X → Γ "ar_cneg" [i64, i64, i64] [i64, i64] xs m Q X)
    {cx : BitVec 64} {v off cnt : BitVec 32} {fv_b any : Bool} {bt bw : BitVec 64}
    {s : ArCtxState} {ruleOff ruleN rsM : List (BitVec 32)} {rsL rsH : List (BitVec 64)}
    {rsPool : List (BitVec 32)} {flippedArr : List (BitVec 8)}
    {rm : List (BitVec 32)} {rl rh : List (BitVec 64)}
    {rm2 : List (BitVec 32)} {rl2 rh2 : List (BitVec 64)} {rpool : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [.bool]} {X : XPost}
    (_hv_lt : v.toNat < s.n_nets.toNat)
    (hnn_bd : s.n_nets.toNat ≤ 0x3FFFFFFF) (hfl_len : s.n_nets.toNat ≤ flippedArr.length)
    (_hqcap_lo : 16 ≤ s.qcap.toNat) (_hqcap_hi : s.qcap.toNat + 16 < 2 ^ 32)
    (hrcap_le : s.rcap.toNat ≤ s.qcap.toNat) (hrpcap_32 : s.rpcap.toNat < 2 ^ 32)
    (_hrsp_32 : s.rs_pcap.toNat < 2 ^ 32)
    (hrm_len : s.rcap.toNat ≤ rm.length) (hrl_len : s.rcap.toNat ≤ rl.length)
    (hrh_len : s.rcap.toNat ≤ rh.length) (hrpool_len : s.rpcap.toNat ≤ rpool.length)
    (hMasks : MasksOk s.modW s.mlo s.mhi)
    (hoff_cnt : off.toNat + cnt.toNat ≤ s.rs_n.toNat)
    (hrs_n_le : s.rs_n.toNat ≤ s.rs_cap.toNat) (hrs_cap_le : s.rs_cap.toNat ≤ rsM.length)
    (hrsL_len : s.rs_cap.toNat ≤ rsL.length) (hrsH_len : s.rs_cap.toNat ≤ rsH.length)
    (hrsPool_len : s.rs_pcap.toNat ≤ rsPool.length) (hrs_ptop : s.rs_ptop.toNat ≤ s.rs_pcap.toNat)
    (hRsSl : ∀ i < s.rs_n.toNat, MonoSliceOk rsPool (rsM.getD i 0#32).toNat s.rs_ptop.toNat ∧
      (rsPool.getD (rsM.getD i 0#32).toNat 0#32).toNat + 1 < 2 ^ 32)
    (hRsSorted : RulesSorted rsPool rsM s.rs_n.toNat)
    (hRsSyms : SymsBound rsPool rsM s.rs_n.toNat s.n_nets.toNat)
    (hMaxF : ∀ i < cnt.toNat,
      flipCount flippedArr (symListAt rsPool (rsM.getD (off.toNat + i) 0#32).toNat) ≤ arRMaxF)
    (hBt : bt.toNat = (if fv_b then 1 else 0) + ruleBt8 flippedArr rsPool rsM off.toNat cnt.toNat)
    (hBw : bw.toNat = (if fv_b then 1 else 0) + ruleBw8 flippedArr rsPool rsM off.toNat cnt.toNat)
    (hm : (arCtxMem cx s ⋆ array (t := i32) s.rule_off ruleOff ⋆ array (t := i32) s.rule_n ruleN ⋆
      array (t := i8) s.flipped flippedArr ⋆ rsMem s rsM rsL rsH rsPool ⋆
      rMem s rm rl rh rm2 rl2 rh2 rpool ⋆ R) m)
    (hFalse : Q (false, ⟨⟩) m)
    (hAfter : ∀ (nFinal : BitVec 32) (rm' : List (BitVec 32)) (rl' rh' : List (BitVec 64))
        (rpool' : List (BitVec 32)) (m' : Mem 64),
      nFinal.toNat = bt.toNat → nFinal.toNat ≤ s.rcap.toNat → nFinal.toNat ≤ s.qcap.toNat →
      rm'.length = rm.length → rl'.length = rl.length → rh'.length = rh.length →
      rpool'.length = rpool.length →
      (∀ r < nFinal.toNat, MonoSliceOk rpool' (rm'.getD r 0#32).toNat rpool'.length ∧
        (rpool'.getD (rm'.getD r 0#32).toNat 0#32).toNat + 1 < 2 ^ 32) →
      (∀ r < nFinal.toNat, MonoSorted rpool' (rm'.getD r 0#32).toNat) →
      monoTotalWords rpool' rm' nFinal.toNat ≤ s.rpcap.toNat →
      SymsBound rpool' rm' nFinal.toNat s.n_nets.toNat →
      (∀ σ : Nat → Bool, (∀ w < s.n_nets.toNat, σ (2 * w + 1) = !(σ (2 * w))) →
        polyEval s.modW σ rpool' rm' rl' rh' nFinal.toNat =
          (if fv_b then (1#(s.modW) : BitVec s.modW) else 0#(s.modW)) +
            (if fv_b then -polyEvalRange s.modW σ rsPool rsM rsL rsH off.toNat cnt.toNat
             else polyEvalRange s.modW σ rsPool rsM rsL rsH off.toNat cnt.toNat)) →
      (arCtxMem cx s ⋆ array (t := i32) s.rule_off ruleOff ⋆ array (t := i32) s.rule_n ruleN ⋆
        array (t := i8) s.flipped flippedArr ⋆ rsMem s rsM rsL rsH rsPool ⋆
        rMem s rm' rl' rh' rm2 rl2 rh2 rpool' ⋆ R) m' →
      wp Γ Q X (buildRPass2AfterExpr cx s.ix s.ix2 v off cnt fv_b any bt bw nFinal) m') :
    wp Γ Q X (buildRPass2EntryExpr cx v off cnt fv_b any bt bw) m := by
  dsimp only [buildRPass2EntryExpr]
  rw [buildR_pass2_pack] at hm
  let Rro := buildRPass2Ro s ruleOff ruleN rsM rsL rsH rsPool flippedArr rm.length rpool.length
    rm2 rl2 rh2 R
  have hm0 : (arCtxMem cx s ⋆ array (t := i32) s.rm rm ⋆ array64 s.rl rl ⋆ array64 s.rh rh ⋆
      array (t := i32) s.rpool rpool ⋆ Rro) m := hm
  c0_hsteps_nogrp
  · exact hFalse
  · exact hFalse
  · have hbt_rcap : bt.toNat ≤ s.rcap.toNat := by c0_bv_omega
    have hbt_qcap : bt.toNat ≤ s.qcap.toNat := by omega
    have hbw_rpcap : bw.toNat ≤ s.rpcap.toNat := by c0_bv_omega
    refine wp_join_group (fun ⟨rp0, n0, ⟨⟩⟩ m1 =>
        ∃ (rm0 : List (BitVec 32)) (rl0 rh0 : List (BitVec 64)) (rpool0 : List (BitVec 32)),
          rm0.length = rm.length ∧ rl0.length = rl.length ∧ rh0.length = rh.length ∧
          rpool0.length = rpool.length ∧
          rp0.toNat = (if fv_b then 1 else 0) ∧ n0.toNat = (if fv_b then 1 else 0) ∧
          (∀ r < n0.toNat, MonoSliceOk rpool0 (rm0.getD r 0#32).toNat rp0.toNat ∧
            (rpool0.getD (rm0.getD r 0#32).toNat 0#32).toNat + 1 < 2 ^ 32) ∧
          (∀ r < n0.toNat, MonoSorted rpool0 (rm0.getD r 0#32).toNat) ∧
          monoTotalWords rpool0 rm0 n0.toNat = rp0.toNat ∧
          SymsBound rpool0 rm0 n0.toNat s.n_nets.toNat ∧
          (∀ σ : Nat → Bool,
            polyEval s.modW σ rpool0 rm0 rl0 rh0 n0.toNat =
              if fv_b then (1#(s.modW) : BitVec s.modW) else 0#(s.modW)) ∧
          (arCtxMem cx s ⋆ array (t := i32) s.rm rm0 ⋆ array64 s.rl rl0 ⋆
            array64 s.rh rh0 ⋆ array (t := i32) s.rpool rpool0 ⋆ Rro) m1)
      ?_ ?_
    · rintro Jp2 ⟨rp0, n0, ⟨⟩⟩ m1
        ⟨rm0, rl0, rh0, rpool0, hrm0, hrl0, hrh0, hrpool0, hrp0, hn0, hSl0, hSorted0, hW0,
          hSb0, hEv0, hm1⟩
      refine wp_loop_group (fun rem ⟨iC, rpC, nC, ⟨⟩⟩ mC =>
          ∃ (rmC : List (BitVec 32)) (rlC rhC : List (BitVec 64)) (rpoolC : List (BitVec 32)),
            iC.toNat ≤ cnt.toNat ∧ rem = cnt.toNat - iC.toNat ∧
            rmC.length = rm.length ∧ rlC.length = rl.length ∧ rhC.length = rh.length ∧
            rpoolC.length = rpool.length ∧
            nC.toNat = (if fv_b then 1 else 0) + ruleBt8 flippedArr rsPool rsM off.toNat iC.toNat ∧
            rpC.toNat ≤ (if fv_b then 1 else 0) + ruleBw8 flippedArr rsPool rsM off.toNat iC.toNat ∧
            (∀ r < nC.toNat, MonoSliceOk rpoolC (rmC.getD r 0#32).toNat rpC.toNat ∧
              (rpoolC.getD (rmC.getD r 0#32).toNat 0#32).toNat + 1 < 2 ^ 32) ∧
            (∀ r < nC.toNat, MonoSorted rpoolC (rmC.getD r 0#32).toNat) ∧
            monoTotalWords rpoolC rmC nC.toNat = rpC.toNat ∧
            SymsBound rpoolC rmC nC.toNat s.n_nets.toNat ∧
            (∀ σ : Nat → Bool, (∀ w < s.n_nets.toNat, σ (2 * w + 1) = !(σ (2 * w))) →
              polyEval s.modW σ rpoolC rmC rlC rhC nC.toNat =
                (if fv_b then (1#(s.modW) : BitVec s.modW) else 0#(s.modW)) +
                  (if fv_b then -polyEvalRange s.modW σ rsPool rsM rsL rsH off.toNat iC.toNat
                   else polyEvalRange s.modW σ rsPool rsM rsL rsH off.toNat iC.toNat)) ∧
            (arCtxMem cx s ⋆ array (t := i32) s.rm rmC ⋆ array64 s.rl rlC ⋆
              array64 s.rh rhC ⋆ array (t := i32) s.rpool rpoolC ⋆ Rro) mC)
        ?_ ?_
      · rintro Ji rem ⟨iC, rpC, nC, ⟨⟩⟩ mC hrec
          ⟨rmC, rlC, rhC, rpoolC, hi_le, hrem, hrmC, hrlC, hrhC, hrpoolC, hnC, hrpC, hSlC,
            hSortedC, hWC, hSbC, hEvC, hmC⟩
        have hbt_pref := ruleBt8_mono flippedArr rsPool rsM off.toNat iC.toNat cnt.toNat hi_le
        have hbw_pref := ruleBw8_mono flippedArr rsPool rsM off.toNat iC.toNat cnt.toNat hi_le
        c0_hsteps_nogrp
        · have hi_lt : iC.toNat < cnt.toNat := hc
          have hidx_rs : (off + iC).toNat = off.toNat + iC.toNat := by
            rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega : off.toNat + iC.toNat < 2 ^ 32)]
          have hidx_lt_rsM : (off + iC).toNat < rsM.length := by omega
          have hidx_lt_rsL : (off + iC).toNat < rsL.length := by omega
          have hidx_lt_rsH : (off + iC).toNat < rsH.length := by omega
          have hidx_lt_rsn : off.toNat + iC.toNat < s.rs_n.toNat := by omega
          obtain ⟨rrM, hrrM⟩ := buildRPass2Ro_rsM (s := s) (ruleOff := ruleOff) (ruleN := ruleN)
            (rsM := rsM) (rsL := rsL) (rsH := rsH) (rsPool := rsPool) (flippedArr := flippedArr)
            (rmLen := rm.length) (rpoolLen := rpool.length) (rm2 := rm2) (rl2 := rl2) (rh2 := rh2)
            (R := R)
          obtain ⟨rrP, hrrP⟩ := buildRPass2Ro_rsPool (s := s) (ruleOff := ruleOff)
            (ruleN := ruleN) (rsM := rsM) (rsL := rsL) (rsH := rsH) (rsPool := rsPool)
            (flippedArr := flippedArr) (rmLen := rm.length) (rpoolLen := rpool.length)
            (rm2 := rm2) (rl2 := rl2) (rh2 := rh2) (R := R)
          obtain ⟨rrL, hrrL⟩ := buildRPass2Ro_rsL (s := s) (ruleOff := ruleOff) (ruleN := ruleN)
            (rsM := rsM) (rsL := rsL) (rsH := rsH) (rsPool := rsPool) (flippedArr := flippedArr)
            (rmLen := rm.length) (rpoolLen := rpool.length) (rm2 := rm2) (rl2 := rl2) (rh2 := rh2)
            (R := R)
          obtain ⟨rrH, hrrH⟩ := buildRPass2Ro_rsH (s := s) (ruleOff := ruleOff) (ruleN := ruleN)
            (rsM := rsM) (rsL := rsL) (rsH := rsH) (rsPool := rsPool) (flippedArr := flippedArr)
            (rmLen := rm.length) (rpoolLen := rpool.length) (rm2 := rm2) (rl2 := rl2) (rh2 := rh2)
            (R := R)
          obtain ⟨rrFl, hrrFl⟩ := buildRPass2Ro_flipped (s := s) (ruleOff := ruleOff)
            (ruleN := ruleN) (rsM := rsM) (rsL := rsL) (rsH := rsH) (rsPool := rsPool)
            (flippedArr := flippedArr) (rmLen := rm.length) (rpoolLen := rpool.length)
            (rm2 := rm2) (rl2 := rl2) (rh2 := rh2) (R := R)
          let mOffBv := rsM.getD (off.toNat + iC.toNat) 0#32
          have hmOff_sl := hRsSl (off.toNat + iC.toNat) hidx_lt_rsn
          dsimp only [MonoSliceOk] at hmOff_sl
          have hmOff_lt_pool : mOffBv.toNat < rsPool.length := by
            have h1 := hmOff_sl.1.1; dsimp only [mOffBv]; omega
          let mlenBv := rsPool.getD mOffBv.toNat 0#32
          have hmlen_eq : mlenBv = rsPool.getD mOffBv.toNat 0#32 := rfl
          have hmOff_32 : mlenBv.toNat + 1 < 2 ^ 32 := hmOff_sl.2
          have hmlen_end : mOffBv.toNat + mlenBv.toNat + 1 ≤ rsPool.length := by
            have h2 := hmOff_sl.1.2; dsimp only [mOffBv, mlenBv]; omega
          have hxs_bd : ∀ x ∈ symListAt rsPool mOffBv.toNat, x / 2 < s.n_nets.toNat :=
            hRsSyms (off.toNat + iC.toNat) hidx_lt_rsn
          let f_tgt := flipCount flippedArr (symListAt rsPool mOffBv.toNat)
          have hf_max : f_tgt ≤ arRMaxF := hMaxF iC.toNat hi_lt
          have hbt_step : (if fv_b then 1 else 0) +
              ruleBt8 flippedArr rsPool rsM off.toNat iC.toNat + 2 ^ f_tgt =
              (if fv_b then 1 else 0) + ruleBt8 flippedArr rsPool rsM off.toNat (iC.toNat + 1) := by
            rw [ruleBt8_succ]; dsimp only [f_tgt, mOffBv]; omega
          have hbt_step_le := ruleBt8_mono flippedArr rsPool rsM off.toNat (iC.toNat + 1) cnt.toNat
            (by omega)
          have hbw_step : (if fv_b then 1 else 0) +
              ruleBw8 flippedArr rsPool rsM off.toNat iC.toNat + 2 ^ f_tgt * (mlenBv.toNat + 1) =
              (if fv_b then 1 else 0) + ruleBw8 flippedArr rsPool rsM off.toNat (iC.toNat + 1) := by
            rw [ruleBw8_succ]; dsimp only [f_tgt, mlenBv, mOffBv]; omega
          have hbw_step_le := ruleBw8_mono flippedArr rsPool rsM off.toNat (iC.toNat + 1) cnt.toNat
            (by omega)
          have hmOff_elem : rsM[0 + (off + iC).toNat]'(by simpa using hidx_lt_rsM) = mOffBv := by
            rw [← getD_eq_getElem rsM 0#32 (by simpa using hidx_lt_rsM), Nat.zero_add, hidx_rs]
          have hmlen_elem : rsPool[0 + mOffBv.toNat]'(by simpa using hmOff_lt_pool) = mlenBv := by
            rw [← getD_eq_getElem rsPool 0#32 (by simpa using hmOff_lt_pool), Nat.zero_add]
          focus
            refine wp_load_arr32_idx (off := 0) (i := off + iC) (base := s.rs_m) (xs := rsM)
              (R := arCtxMem cx s ⋆ array (t := i32) s.rm rmC ⋆ array64 s.rl rlC ⋆
                array64 s.rh rhC ⋆ array (t := i32) s.rpool rpoolC ⋆ rrM)
              (by simp) (by simpa using hidx_lt_rsM)
              (sep_cast (by simpa only [Rro, hrrM] using hmC) (by ac_rfl)) ?_
            rw [hmOff_elem]
            c0_hsteps_nogrp
            refine wp_load_arr32_idx (off := 0) (i := mOffBv) (base := s.rs_pool) (xs := rsPool)
              (R := arCtxMem cx s ⋆ array (t := i32) s.rm rmC ⋆ array64 s.rl rlC ⋆
                array64 s.rh rhC ⋆ array (t := i32) s.rpool rpoolC ⋆ rrP)
              (by simp) (by simpa using hmOff_lt_pool)
              (sep_cast (by simpa only [Rro, hrrP] using hmC) (by ac_rfl)) ?_
            rw [hmlen_elem]
            c0_hsteps_nogrp
            refine wp_load_arr64_idx (i := off + iC) (base := s.rs_l) (xs := rsL)
              (R := arCtxMem cx s ⋆ array (t := i32) s.rm rmC ⋆ array64 s.rl rlC ⋆
                array64 s.rh rhC ⋆ array (t := i32) s.rpool rpoolC ⋆ rrL)
              rfl hidx_lt_rsL (sep_cast (by simpa only [Rro, hrrL] using hmC) (by ac_rfl)) ?_
            c0_hsteps_nogrp
            refine wp_load_arr64_idx (i := off + iC) (base := s.rs_h) (xs := rsH)
              (R := arCtxMem cx s ⋆ array (t := i32) s.rm rmC ⋆ array64 s.rl rlC ⋆
                array64 s.rh rhC ⋆ array (t := i32) s.rpool rpoolC ⋆ rrH)
              rfl hidx_lt_rsH (sep_cast (by simpa only [Rro, hrrH] using hmC) (by ac_rfl)) ?_
            c0_hsteps_nogrp
            let cl := rsL[(off + iC).toNat]'hidx_lt_rsL
            let ch := rsH[(off + iC).toNat]'hidx_lt_rsH
            refine wp_loop_group (fun remF ⟨fF, jF, ⟨⟩⟩ mF =>
                mF = mC ∧ 1 ≤ jF.toNat ∧ jF.toNat ≤ mlenBv.toNat + 1 ∧
                remF = mlenBv.toNat + 1 - jF.toNat ∧
                fF.toNat =
                  flipCount flippedArr ((symListAt rsPool mOffBv.toNat).take (jF.toNat - 1)))
              ?_ ?_
            · rintro Jf remF ⟨fF, jF, ⟨⟩⟩ mF hrecF ⟨hmF, hjF1, hjFle, hremF, hfF⟩
              cases hmF
              have hfF_le : fF.toNat ≤ jF.toNat - 1 := by
                rw [hfF]; exact Nat.le_trans (flipCount_le_length _ _) (by simp [Nat.min_le_left])
              c0_hsteps_nogrp
              · have hjF_le_m : jF.toNat ≤ mlenBv.toNat := hc
                have hmF_lt : mOffBv.toNat + jF.toNat < rsPool.length := by omega
                have hxj_eq : (rsPool[mOffBv.toNat + jF.toNat]'hmF_lt).toNat =
                    (rsPool.getD (mOffBv.toNat + jF.toNat) 0#32).toNat :=
                  congrArg BitVec.toNat (getD_eq_getElem rsPool 0#32 hmF_lt).symm
                have htake_j : (symListAt rsPool mOffBv.toNat).take jF.toNat =
                    (symListAt rsPool mOffBv.toNat).take (jF.toNat - 1) ++
                      [(rsPool[mOffBv.toNat + jF.toNat]'hmF_lt).toNat] := by
                  rw [hxj_eq]; exact symListAt_take_succ hjF1 (by rw [← hmlen_eq]; exact hjF_le_m)
                have hxj_mem : (rsPool[mOffBv.toNat + jF.toNat]'hmF_lt).toNat ∈
                    symListAt rsPool mOffBv.toNat := by
                  simp only [symListAt, ← hmlen_eq, List.mem_map, List.mem_range]
                  refine ⟨jF.toNat - 1, by omega, ?_⟩
                  rw [show mOffBv.toNat + 1 + (jF.toNat - 1) = mOffBv.toNat + jF.toNat by omega,
                    ← hxj_eq]
                have hxj_half : (rsPool[mOffBv.toNat + jF.toNat]'hmF_lt).toNat / 2 <
                    flippedArr.length :=
                  Nat.lt_of_lt_of_le (hxs_bd _ hxj_mem) hfl_len
                refine wp_load_arr32_add (base := s.rs_pool) (off64 := BitVec.setWidth 64 mOffBv)
                  (idx := jF) (xs := rsPool)
                  (R := arCtxMem cx s ⋆ array (t := i32) s.rm rmC ⋆ array64 s.rl rlC ⋆
                    array64 s.rh rhC ⋆ array (t := i32) s.rpool rpoolC ⋆ rrP)
                  rfl (by rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]; exact hmF_lt)
                  (sep_cast (by simpa only [Rro, hrrP] using hmC) (by ac_rfl)) ?_
                c0_hsteps_nogrp
                let xF := rsPool[(BitVec.setWidth 64 mOffBv).toNat + jF.toNat]'(by
                  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]; exact hmF_lt)
                have hxF_eq : xF = rsPool[mOffBv.toNat + jF.toNat]'hmF_lt := by
                  dsimp only [xF]; simp [BitVec.toNat_setWidth]
                have hxF_half : (xF >>> 1#32).toNat < flippedArr.length := by
                  rw [bv32_shr1_toNat, hxF_eq]; exact hxj_half
                have hjF1_nat : (jF + 1#32).toNat = jF.toNat + 1 := by
                  rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl,
                    Nat.mod_eq_of_lt (by omega : jF.toNat + 1 < 2 ^ 32)]
                refine wp_join_group (fun ⟨fF', ⟨⟩⟩ mF' =>
                    mF' = mC ∧ fF'.toNat = flipCount flippedArr
                      ((symListAt rsPool mOffBv.toNat).take jF.toNat))
                  ?_ ?_
                · rintro Jfc ⟨fF', ⟨⟩⟩ mF' ⟨hmF', hfF'⟩
                  cases hmF'
                  c0_hsteps_nogrp
                  exact hrecF (mlenBv.toNat + 1 - (jF + 1#32).toNat) (fF', jF + 1#32, ⟨⟩) mC
                    (by omega) ⟨rfl, by omega, by omega, rfl, by
                      rw [hjF1_nat, Nat.add_sub_cancel]; exact hfF'⟩
                · intro Jfc hJfc
                  c0_hsteps_nogrp
                  · refine wp_load_arr8_idx (base := s.flipped) (i := xF >>> 1#32)
                      (xs := flippedArr)
                      (R := arCtxMem cx s ⋆ array (t := i32) s.rm rmC ⋆ array64 s.rl rlC ⋆
                        array64 s.rh rhC ⋆ array (t := i32) s.rpool rpoolC ⋆ rrFl)
                      ?_ hxF_half
                      (sep_cast (by simpa only [Rro, hrrFl] using hmC) (by ac_rfl)) ?_
                    · rfl
                    c0_hsteps_nogrp
                    · have hfl_cond : flipCond flippedArr xF.toNat = true := by
                        simp only [flipCond, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq]
                        refine ⟨(bv32_and1_eq_zero_iff xF).mp (by assumption), ?_⟩
                        rw [getD_eq_getElem flippedArr 0#8
                          (by rw [← bv32_shr1_toNat xF]; exact hxF_half)]
                        have hne : ¬ BitVec.setWidth 32
                            (flippedArr[xF.toNat / 2 ^ (1 % 2 ^ 32)]'(by
                              simp; rw [← bv32_shr1_toNat xF]; exact hxF_half)) =
                            BitVec.ofNat 32 0 := by assumption
                        intro hz; apply hne; simp [hz]
                      have hfF_add1 : (fF + 1#32).toNat = fF.toNat + 1 := by
                        rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl,
                          Nat.mod_eq_of_lt (by omega : fF.toNat + 1 < 2 ^ 32)]
                      c0_hsteps_nogrp
                      refine hJfc _ _ ⟨rfl, ?_⟩
                      rw [show (fF + 1 : BitVec 32).toNat = fF.toNat + 1 from hfF_add1,
                        htake_j, flipCount_append, flipCount_cons, flipCount_nil,
                        ← hxF_eq, hfl_cond, hfF]; rfl
                    · have hfl_cond : flipCond flippedArr xF.toNat = false := by
                        simp only [flipCond, Bool.and_eq_false_iff, bne_eq_false_iff_eq]
                        right
                        rw [getD_eq_getElem flippedArr 0#8
                          (by rw [← bv32_shr1_toNat xF]; exact hxF_half)]
                        have heq0 : BitVec.setWidth 32
                            (flippedArr[xF.toNat / 2 ^ (1 % 2 ^ 32)]'(by
                              simp; rw [← bv32_shr1_toNat xF]; exact hxF_half)) =
                            BitVec.ofNat 32 0 := by assumption
                        apply BitVec.eq_of_toNat_eq
                        have ht := congrArg BitVec.toNat heq0
                        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt
                          (Nat.lt_of_lt_of_le (BitVec.isLt _) (by decide))] at ht
                        simpa using ht
                      c0_hsteps_nogrp
                      refine hJfc _ _ ⟨rfl, ?_⟩
                      rw [htake_j, flipCount_append, flipCount_cons, flipCount_nil, ← hxF_eq,
                        hfl_cond, hfF]; simp
                  · have hfl_cond : flipCond flippedArr xF.toNat = false := by
                      simp only [flipCond, Bool.and_eq_false_iff, beq_eq_false_iff_ne]
                      left; intro hmod
                      exact ‹¬ xF &&& 1#32 = 0#32› ((bv32_and1_eq_zero_iff xF).mpr hmod)
                    c0_hsteps_nogrp
                    refine hJfc _ _ ⟨rfl, ?_⟩
                    rw [htake_j, flipCount_append, flipCount_cons, flipCount_nil, ← hxF_eq,
                      hfl_cond, hfF]; simp
              · have hjF_eq : jF.toNat = mlenBv.toNat + 1 := by
                  have := BitVec.not_le.mp hc; omega
                have htake_all : (symListAt rsPool mOffBv.toNat).take (jF.toNat - 1) =
                    symListAt rsPool mOffBv.toNat := by
                  rw [hjF_eq, Nat.add_sub_cancel]
                  apply List.take_of_length_le
                  simp only [symListAt, ← hmlen_eq, List.length_map, List.length_range, le_refl]
                have hfF_eq : fF.toNat = f_tgt := by rw [hfF, htake_all]
                have hnC_bd' : nC.toNat + 2 ^ f_tgt ≤ s.rcap.toNat := by
                  have hbt' := hbt_step; have hbt'' := hbt_step_le; dsimp only [f_tgt] at hbt' ⊢
                  omega
                have hrpC_bd' : rpC.toNat + 2 ^ f_tgt * (mlenBv.toNat + 1) ≤ s.rpcap.toNat := by
                  have hbw' := hbw_step; have hbw'' := hbw_step_le; dsimp only [f_tgt] at hbw' ⊢
                  omega
                c0_hsteps_nogrp
                refine buildR_pass2_S_wp Γ (Ji := Ji) hCneg (v := v) (off := off) (cnt := cnt)
                  (fv_b := fv_b) (any := any) (bt := bt) (bw := bw) (iC := iC) (rpC := rpC)
                  (nC := nC) (cl := cl) (ch := ch) (fF := fF) (jF := jF) hnn_bd hfl_len hMasks
                  hrmC hrlC hrhC hrpoolC hrm_len hrl_len hrh_len hrpool_len hrpcap_32 hmlen_eq
                  hmOff_32 hmlen_end hxs_bd (hRsSorted (off.toNat + iC.toNat) hidx_lt_rsn)
                  hfF_eq hf_max hnC_bd' hrpC_bd' hSlC hSortedC hWC hSbC hmC ?_
                intro Js rpS nS_cur jU S rmS rlS rhS rpoolS mS hS_eq hrmS hrlS hrhS hrpoolS
                  hnS_cur hrpS_bd hSlS hSortedS hWS hSbS hEvS hmS
                have hcl_eq : cl = rsL.getD (off.toNat + iC.toNat) 0#64 := by
                  dsimp only [cl]; rw [← getD_eq_getElem rsL 0#64 hidx_lt_rsL, hidx_rs]
                have hch_eq : ch = rsH.getD (off.toNat + iC.toNat) 0#64 := by
                  dsimp only [ch]; rw [← getD_eq_getElem rsH 0#64 hidx_lt_rsH, hidx_rs]
                have hi1_nat : (iC + 1#32).toNat = iC.toNat + 1 := by
                  rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl,
                    Nat.mod_eq_of_lt (by omega : iC.toNat + 1 < 2 ^ 32)]
                dsimp only [buildRPass2SBranches, buildRPass2SExpr, buildRPass2P2Exit,
                  buildRPass2EntryExpr]
                c0_hsteps_nogrp
                refine hrec (cnt.toNat - (iC + 1#32).toNat) (iC + 1#32, rpS, nS_cur, ⟨⟩)
                  mS (by omega) ?_
                refine ⟨rmS, rlS, rhS, rpoolS, by omega, by rw [hi1_nat], hrmS, hrlS, hrhS,
                  hrpoolS, by rw [hnS_cur, hnC, hi1_nat, ← hbt_step],
                  by dsimp only [f_tgt] at *; rw [hi1_nat, ← hbw_step]; omega,
                  hSlS, hSortedS, hWS, hSbS, ?_, hmS⟩
                intro σ hσ
                rw [hEvS σ hσ, hcl_eq, hch_eq,
                  expandSum_signed_eq σ flippedArr rsPool rsM rsL rsH
                    (off.toNat + iC.toNat) fv_b hσ (hRsSyms _ hidx_lt_rsn),
                  hEvC σ hσ, hi1_nat, BitVec.add_assoc]
                congr 1
                cases fv_b
                · simp [polyEvalRange_succ]
                · simp only [↓reduceIte, neg_polyEvalRange, List.range_succ,
                    List.foldl_append, List.foldl_cons, List.foldl_nil]
            · intro J hJ; c0_hsteps_nogrp
              exact hJ mlenBv.toNat (0#32, 1#32, ⟨⟩) mC
                ⟨rfl, by decide, Nat.le_add_left 1 _, rfl, by simp [flipCount]⟩
        · have hi_eq : iC.toNat = cnt.toNat := by
            have := BitVec.not_lt.mp hc; omega
          have hnC_eq : nC.toNat = bt.toNat := by rw [hnC, hi_eq, hBt]
          have hrpC_rpcap : rpC.toNat ≤ s.rpcap.toNat := by omega
          have hmC' : (arCtxMem cx s ⋆ array (t := i32) s.rule_off ruleOff ⋆
              array (t := i32) s.rule_n ruleN ⋆ array (t := i8) s.flipped flippedArr ⋆
              rsMem s rsM rsL rsH rsPool ⋆ rMem s rmC rlC rhC rm2 rl2 rh2 rpoolC ⋆ R) mC := by
            have hmC0 := hmC; dsimp only [Rro] at hmC0
            rw [← hrmC, ← hrpoolC] at hmC0; rw [← buildR_pass2_pack] at hmC0
            exact sep_cast hmC0 (by ac_rfl)
          exact hAfter nC rmC rlC rhC rpoolC mC hnC_eq (by omega) (by omega)
            hrmC hrlC hrhC hrpoolC
            (fun r hr => by
              obtain ⟨h1, h2⟩ := hSlC r hr; dsimp only [MonoSliceOk] at h1 ⊢
              exact ⟨⟨by omega, by omega⟩, h2⟩)
            hSortedC (by rw [hWC]; omega) hSbC (by rw [← hi_eq]; exact hEvC) hmC'
      · intro J hJ; c0_hsteps_nogrp
        exact hJ cnt.toNat (0#32, rp0, n0, ⟨⟩) m1
          ⟨rm0, rl0, rh0, rpool0, Nat.zero_le _, rfl, hrm0, hrl0, hrh0, hrpool0,
            by simp [hn0, ruleBt8], by simp [hrp0, ruleBw8], hSl0, hSorted0, hW0, hSb0,
            fun σ _ => by simp [hEv0 σ, polyEvalRange], hm1⟩
    · intro Jp2 hJp2
      by_cases hfv : fv_b
      · have hfv_eq : fv_b = true := by simp [hfv]
        subst hfv_eq
        dsimp only
        refine head_wp_jnz (vc := true) rfl (fun _ => ?_) (fun h => by cases h)
        have hbt1 : 1 ≤ bt.toNat := by rw [hBt]; simp
        have hbw1 : 1 ≤ bw.toNat := by rw [hBw]; simp
        have hrp_lt0 : 0 < rpool.length := Nat.lt_of_lt_of_le hbw1 (by omega)
        have hrm_lt0 : 0 < rm.length := Nat.lt_of_lt_of_le hbt1 (by omega)
        have hrl_lt0 : 0 < rl.length := Nat.lt_of_lt_of_le hbt1 (by omega)
        have hrh_lt0 : 0 < rh.length := Nat.lt_of_lt_of_le hbt1 (by omega)
        c0_hsteps_nogrp
        have hzero : (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 0)).toNat = 0 := rfl
        have hm1 : (arCtxMem cx s ⋆ array (t := i32) s.rm (rm.set 0 0#32) ⋆
            array64 s.rl (rl.set 0 (1#64 &&& s.mlo)) ⋆ array64 s.rh (rh.set 0 0#64) ⋆
            array (t := i32) s.rpool (rpool.set 0 0#32) ⋆ Rro) m := by
          have hm0' := hm; rw [hzero] at hm0'; exact sep_cast hm0' (by ac_rfl)
        have h132 : BitVec.toNat (1 : BitVec 32) = 1 := rfl
        have h164 : BitVec.toNat (1 : BitVec 64) = 1 := rfl
        refine hJp2 _ _ ⟨rm.set 0 0#32, rl.set 0 (1#64 &&& s.mlo), rh.set 0 0#64, rpool.set 0 0#32,
          by simp, by simp, by simp, by simp, rfl, rfl, fun r hr => ?_, fun r hr => ?_, ?_,
          fun r hr => ?_, fun σ => ?_, hm1⟩
        · rw [h132] at hr
          have hr0 : r = 0 := by omega
          subst hr0
          have hrm0' : ((rm.set 0 0#32).getD 0 0#32).toNat = 0 := by
            rw [getD_set_eq rm 0#32 0#32 hrm_lt0, ite_eq_left rfl]; rfl
          have hrp0' : ((rpool.set 0 0#32).getD 0 0#32).toNat = 0 := by
            rw [getD_set_eq rpool 0#32 0#32 hrp_lt0, ite_eq_left rfl]; rfl
          rw [hrm0', hrp0', h164]; exact ⟨⟨by omega, by omega⟩, by omega⟩
        · rw [h132] at hr
          have hr0 : r = 0 := by omega
          subst hr0
          rw [getD_set_eq rm 0#32 0#32 hrm_lt0, ite_eq_left rfl,
            show (0#32 : BitVec 32).toNat = 0 from rfl]
          exact monoSorted_of_le1 (by
            rw [getD_set_eq rpool 0#32 0#32 hrp_lt0, ite_eq_left rfl]; simp)
        · rw [h132, h164, monoTotalWords_succ, monoTotalWords_zero, Nat.zero_add,
            getD_set_eq rm 0#32 0#32 hrm_lt0, ite_eq_left rfl,
            show (0#32 : BitVec 32).toNat = 0 from rfl,
            getD_set_eq rpool 0#32 0#32 hrp_lt0, ite_eq_left rfl]; rfl
        · rw [h132] at hr
          have hr0 : r = 0 := by omega
          subst hr0
          rw [getD_set_eq rm 0#32 0#32 hrm_lt0, ite_eq_left rfl,
            show (0#32 : BitVec 32).toNat = 0 from rfl,
            symListAt_set_zero rpool 0#32 hrp_lt0,
            show (0#32 : BitVec 32).toNat = 0 from rfl, List.range_zero, List.map_nil]
          exact fun _ hx => by cases hx
        · rw [h132, polyEval_succ, polyEval_zero, BitVec.zero_add]
          simp only [termEval, getD_set_eq rm 0#32 0#32 hrm_lt0,
            show (0#32 : BitVec 32).toNat = 0 from rfl, symListAt_set_zero rpool 0#32 hrp_lt0,
            List.range_zero, List.map_nil, monoValL_nil, ↓reduceIte,
            getD_set_eq rl 0#64 _ hrl_lt0, getD_set_eq rh 0#64 _ hrh_lt0,
            bv64_one_and_mlo hMasks]
          exact coeff128_one s.modW
      · have hfv_eq : fv_b = false := Bool.eq_false_iff.mpr hfv
        subst hfv_eq
        dsimp only
        refine head_wp_jnz (vc := false) ?_ (fun h => by cases h) (fun _ => ?_)
        · rfl
        c0_hsteps_nogrp
        exact hJp2 _ _ ⟨rm, rl, rh, rpool, rfl, rfl, rfl, rfl, rfl, rfl,
          fun _ hr => by simp at hr, fun _ hr => by simp at hr, rfl,
          fun _ hr => by simp at hr, fun _ => rfl, hm0⟩

end

end LeanQbe.T.Examples.Arisca.Proof
