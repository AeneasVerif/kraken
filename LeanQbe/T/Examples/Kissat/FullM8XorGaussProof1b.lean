/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM8XorGaussProof0
public import LeanQbe.T.Examples.Kissat.FullM8XorGaussProof1a
import LeanQbe.T.Examples.Kissat.FullAssignAddLemmas1
import LeanQbe.T.Examples.Kissat.FullLearnAnaLemmas1
import LeanQbe.T.Examples.Kissat.FullM6ProofUtil
import LeanQbe.T.Examples.Kissat.FullM4VivBceProof1
import LeanQbe.T.Examples.Kissat.FullM6Transport1
public meta import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.C0Agrees
public meta import Lean.Elab.Tactic
public meta import LeanQbe.T.Logic.C0Step

/-!
# Kissat M8 XOR / $\mathbb{F}_2$ Gauss-Jordan — Extraction & Chain Merge (`FullM8XorGaussProof1b`)

`Func.wp` proofs for `full_xor_collect_arena`, `full_xor_collect_bins`, and `full_xor_chain_merge`.
-/

set_option autoImplicit false

local elab "c0_hstraight" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { unrollGroup := false, splitJnz := false } 2000

local elab "c0_hstraight!" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { unrollGroup := false, splitJnz := false, strictMem := true } 2000

public section

namespace LeanQbe.T.Examples.Kissat.FullM8XorGauss

open Std Std.Sat Std.ExtHashMap LeanQbe.T.C0Step
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open Kraken.Bedrock2.Test

open scoped FullArenaTactics FullAssignAddTactics
open FullAssignAddTactics LeanQbe.T.Examples.Kissat.FullM6ProofUtil
open LeanQbe.T.Examples.Kissat.Full.FullDenseWatchHelpers

@[expose] def fullXorCollectArenaSpec : Spec [i64, i64] [i64] := fun (h, ht_cap, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧
    FullSparseInvW c F0 F_cur s ∧
    s.core.cur_level = 0 ∧
    (ht_cap ≠ 0#64 → 7 * ht_cap.toNat ≤ c.scratch_cap ∧ ht_cap.toNat < 2 ^ 30) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (res : BitVec 64) (s' : FullState) (m' : Mem 64),
      FullSparseInvW c F0 F_cur s' →
      s'.core.cur_vars = s.core.cur_vars →
      s'.core.cur_level = s.core.cur_level →
      s'.core.fuel = s.core.fuel →
      FullExtScratchPres s s' →
      (res = 0xFFFFFFFFFFFFFFFF#64 → F0.Unsat ∧ s'.core.inconsistent ≠ 0#64) →
      (res ≠ 0xFFFFFFFFFFFFFFFF#64 →
        res.toNat ≤ c.scratch_cap ∧ s'.core.inconsistent = s.core.inconsistent ∧
        XorEqPoolOk (cnfOfClauses F_cur) s'.core.cur_vars s'.scratch.scratch_buf res.toNat 0) →
      (FullMem c s' ⋆ R) m' → Q (res, ()) m'

private theorem collect_arena_slot_append_ok {F : CNF Nat} {cv ht_cap : Nat}
    {scr scr1 : List (BitVec 32)} {i eq_end sk : Nat}
    {seen v0 v1 v2 v3 v4 hdr : BitVec 32} {rhs_b : Bool}
    (hi : i < ht_cap)
    (heq_le : eq_end ≤ i * 7)
    (hcap : 7 * ht_cap ≤ scr.length)
    (hlen : scr1.length = scr.length)
    (hsk3 : 3 ≤ sk) (hsk5 : sk ≤ 5)
    (hpool : XorEqPoolOk F cv scr eq_end 0)
    (hht : ∀ s_idx, i ≤ s_idx → s_idx < ht_cap →
      let sb := s_idx * 7
      let sk_s := (scr[sb]?.getD 0#32).toNat
      sk_s = 0 ∨ (3 ≤ sk_s ∧ sk_s ≤ 5 ∧
        let vs := (List.range sk_s).map fun k => (scr[sb + 2 + k]?.getD 0#32).toNat
        List.Pairwise (· < ·) vs ∧ (∀ v ∈ vs, v < cv) ∧
        let sn := scr[sb + 1]?.getD 0#32
        ∀ mv < 2 ^ sk_s, sn.getLsbD mv = true → F.EntailsClause (cnfClause (xorMaskClause vs mv))))
    (hsk_eq : (scr[i * 7]?.getD 0#32).toNat = sk)
    (hsn_eq : scr[i * 7 + 1]? = some seen)
    (hv0_eq : scr[i * 7 + 2]? = some v0)
    (hv1_eq : scr[i * 7 + 3]? = some v1)
    (hv2_eq : scr[i * 7 + 4]? = some v2)
    (hv3_eq : scr[i * 7 + 5]? = some v3)
    (hv4_eq : scr[i * 7 + 6]? = some v4)
    (hrhs_eq : ((hdr >>> 31#32) != 0#32) = rhs_b)
    (hmask : seen &&& parityMask sk (!rhs_b) = parityMask sk (!rhs_b))
    (hst : ((hdr >>> 16#32) &&& 0x7FFF#32).toNat = sk)
    (hcl : (hdr &&& 0xFFFF#32).toNat = sk)
    (hpre : ∀ j < eq_end, scr1[j]? = scr[j]?)
    (hsuf : ∀ j, eq_end + 1 + sk ≤ j → scr1[j]? = scr[j]?)
    (hwhdr : scr1[eq_end]? = some hdr)
    (hw0 : scr1[eq_end + 1]? = some v0)
    (hw1 : scr1[eq_end + 2]? = some v1)
    (hw2 : scr1[eq_end + 3]? = some v2)
    (hw3 : 4 ≤ sk → scr1[eq_end + 4]? = some v3)
    (hw4 : 5 ≤ sk → scr1[eq_end + 5]? = some v4) :
    XorEqPoolOk F cv scr1 (eq_end + 1 + sk) 0 ∧
      ∀ s_idx, i + 1 ≤ s_idx → s_idx < ht_cap →
        let sb := s_idx * 7
        let sk_s := (scr1[sb]?.getD 0#32).toNat
        sk_s = 0 ∨ (3 ≤ sk_s ∧ sk_s ≤ 5 ∧
          let vs := (List.range sk_s).map fun k => (scr1[sb + 2 + k]?.getD 0#32).toNat
          List.Pairwise (· < ·) vs ∧ (∀ v ∈ vs, v < cv) ∧
          let sn := scr1[sb + 1]?.getD 0#32
          ∀ mv < 2 ^ sk_s, sn.getLsbD mv = true →
            F.EntailsClause (cnfClause (xorMaskClause vs mv))) := by
  have hslot := hht i (Nat.le_refl _) hi
  dsimp only at hslot
  rw [hsk_eq] at hslot
  rcases hslot with h0 | ⟨_, _, hss, hlt, hent⟩
  · omega
  · have hsn' : scr[i * 7 + 1]?.getD 0#32 = seen := by simp [hsn_eq]
    rw [hsn'] at hent
    let vs := (List.range sk).map fun k => (scr[i * 7 + 2 + k]?.getD 0#32).toNat
    have hvs_len : vs.length = sk := by simp [vs]
    have hsnd : XorVarsSound F vs ((hdr >>> 31#32) != 0#32) := by
      have hpm := xorVarsSound_of_parityMask (F := F) (vs := vs) (seen := seen)
        (p := !rhs_b)
        (by rw [hvs_len]; exact hsk3) (by rw [hvs_len]; exact hsk5)
        (by rw [hvs_len]; exact hmask) (by rw [hvs_len]; exact hent)
      rw [hrhs_eq]; simpa using hpm
    have hvs_new : (List.range sk).map (fun k => (scr1[eq_end + 1 + k]?.getD 0#32).toNat) = vs := by
      refine List.map_congr_left fun k hk => ?_
      have hkm : k < sk := List.mem_range.mp hk
      have hcases : k = 0 ∨ k = 1 ∨ k = 2 ∨ (k = 3 ∧ 4 ≤ sk) ∨ (k = 4 ∧ 5 ≤ sk) := by omega
      rcases hcases with rfl | rfl | rfl | ⟨rfl, hk4⟩ | ⟨rfl, hk5⟩
      · simp [hw0, hv0_eq]
      · simp [hw1, hv1_eq]
      · simp [hw2, hv2_eq]
      · simp [hw3 hk4, hv3_eq]
      · simp [hw4 hk5, hv4_eq]
    have hpool1 : XorEqPoolOk F cv scr1 eq_end 0 :=
      xorEqPoolOk_congr hpool fun j _ hj => hpre j hj
    have hpool2 : XorEqPoolOk F cv scr1 (eq_end + 1 + sk) 0 := by
      refine xorEqPoolOk_append hpool1 (by omega) hwhdr hst hcl (by omega) ?_ ?_ ?_
      · rw [hvs_new]; exact hss
      · rw [hvs_new]; exact hlt
      · rw [hvs_new]; exact hsnd
    refine ⟨hpool2, fun s_idx hs1 hs2 => ?_⟩
    have horig := hht s_idx (by omega) hs2
    dsimp only at horig ⊢
    have h0 : scr1[s_idx * 7]? = scr[s_idx * 7]? := hsuf _ (by omega)
    have h1 : scr1[s_idx * 7 + 1]? = scr[s_idx * 7 + 1]? := hsuf _ (by omega)
    have h2 : ∀ k, scr1[s_idx * 7 + 2 + k]? = scr[s_idx * 7 + 2 + k]? := fun k =>
      hsuf _ (by omega)
    simp only [h0, h1, h2]
    exact horig

private theorem pack_hdr_drain_fields (sk32 : BitVec 32) (rhs : BitVec 64)
    (hsk3 : 3 ≤ sk32.toNat) (hsk5 : sk32.toNat ≤ 5) (hrhs : rhs = 0#64 ∨ rhs = 1#64) :
    let hdr := (sk32 ||| (sk32 <<< (16#32 &&& 31#32))) ||| ((rhs.setWidth 32) <<< (31#32 &&& 31#32))
    ((hdr >>> 16#32) &&& 0x7FFF#32).toNat = sk32.toNat ∧
    (hdr &&& 0xFFFF#32).toNat = sk32.toNat ∧
    ((hdr >>> 31#32) != 0#32) = decide (rhs = 1#64) := by
  rcases hrhs with rfl | rfl
  · have : ∀ k : BitVec 32, 3 ≤ k.toNat → k.toNat ≤ 5 →
        let hdr := (k ||| (k <<< (16#32 &&& 31#32))) ||| ((0#64).setWidth 32 <<< (31#32 &&& 31#32))
        ((hdr >>> 16#32) &&& 0x7FFF#32).toNat = k.toNat ∧
        (hdr &&& 0xFFFF#32).toNat = k.toNat ∧ ((hdr >>> 31#32) != 0#32) = false := by
      intro k hk3 hk5
      have hk_cases : k = 3#32 ∨ k = 4#32 ∨ k = 5#32 := by bv_omega
      rcases hk_cases with rfl | rfl | rfl <;> decide
    simpa using this sk32 hsk3 hsk5
  · have : ∀ k : BitVec 32, 3 ≤ k.toNat → k.toNat ≤ 5 →
        let hdr := (k ||| (k <<< (16#32 &&& 31#32))) ||| ((1#64).setWidth 32 <<< (31#32 &&& 31#32))
        ((hdr >>> 16#32) &&& 0x7FFF#32).toNat = k.toNat ∧
        (hdr &&& 0xFFFF#32).toNat = k.toNat ∧ ((hdr >>> 31#32) != 0#32) = true := by
      intro k hk3 hk5
      have hk_cases : k = 3#32 ∨ k = 4#32 ∨ k = 5#32 := by bv_omega
      rcases hk_cases with rfl | rfl | rfl <;> decide
    simpa using this sk32 hsk3 hsk5

private theorem collect_arena_tmp_step {tmp : List (BitVec 32)} {cnt cv : Nat} {li : BitVec 32}
    {lits : List Nat} {vals : List (BitVec 8)} {i : Nat}
    (hcnt_lt : cnt < tmp.length)
    (hli_lt : li.toNat < 2 * cv)
    (htmp_lt : ∀ k < cnt, (tmp[k]?.getD 0#32).toNat < 2 * cv)
    (hsub : ∀ l ∈ lits.take i,
      l ∈ (tmp.take cnt).map BitVec.toNat ∨ (l < 2 * cv ∧ vals[l]?.getD 0#8 = 255#8))
    (hstep : ∀ l ∈ lits.take (i + 1), l ∈ lits.take i ∨ l = li.toNat) :
    let tmp_new := tmp.set cnt li
    (∀ k < cnt + 1, (tmp_new[k]?.getD 0#32).toNat < 2 * cv) ∧
    (∀ l ∈ lits.take (i + 1),
      l ∈ (tmp_new.take (cnt + 1)).map BitVec.toNat ∨
      (l < 2 * cv ∧ vals[l]?.getD 0#8 = 255#8)) := by
  intro tmp_new
  refine ⟨fun k hk => ?_, fun l hl => ?_⟩
  · rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hk) with hk_old | rfl
    · dsimp only [tmp_new]
      rw [List.getElem?_set_ne (by omega)]
      exact htmp_lt k hk_old
    · dsimp only [tmp_new]
      rw [List.getElem?_set_self hcnt_lt, Option.getD_some]
      exact hli_lt
  · have htk : tmp_new.take (cnt + 1) = tmp.take cnt ++ [li] := list_take_succ_set hcnt_lt
    rcases hstep l hl with h_old | rfl
    · rcases hsub l h_old with hin | hfal
      · left; rw [htk, List.map_append]; exact List.mem_append_left _ hin
      · right; exact hfal
    · left; rw [htk, List.map_append]; exact List.mem_append_right _ (by simp)

private theorem liftCmp_eq_i32_true {a b : BitVec 32}
    (h : liftCmp (fun {_} => CmpOp.eq.evalBits) CmpOp.eq.evalBool i32 a b = true) :
    a = b := by
  simpa [liftCmp, CmpOp.evalBits] using h

private theorem liftCmp_eq_i32_false {a b : BitVec 32}
    (h : liftCmp (fun {_} => CmpOp.eq.evalBits) CmpOp.eq.evalBool i32 a b = false) :
    a ≠ b := by
  simpa [liftCmp, CmpOp.evalBits] using h

private theorem collect_arena_write4_ok {scr2 : List (BitVec 32)} {eq_end : BitVec 64}
    {hdr v0 v1 v2 v3 : BitVec 32}
    (hw1 : (eq_end + 1#64).toNat = eq_end.toNat + 1)
    (hw2 : (eq_end + 2#64).toNat = eq_end.toNat + 2)
    (hw3 : (eq_end + 3#64).toNat = eq_end.toNat + 3)
    (hw4 : (eq_end + 4#64).toNat = eq_end.toNat + 4)
    (hbd : eq_end.toNat + 4 < scr2.length) :
    let scr_a := (((scr2.set eq_end.toNat hdr).set (eq_end + 1#64).toNat v0).set
      (eq_end + 2#64).toNat v1).set (eq_end + 3#64).toNat v2
    let scr6 := scr_a.set (eq_end + 4#64).toNat v3
    scr6.length = scr2.length ∧
    (∀ k < eq_end.toNat, scr6[k]? = scr2[k]?) ∧
    scr6[eq_end.toNat]? = some hdr ∧
    scr6[eq_end.toNat + 1]? = some v0 ∧
    scr6[eq_end.toNat + 2]? = some v1 ∧
    scr6[eq_end.toNat + 3]? = some v2 ∧
    scr6[eq_end.toNat + 4]? = some v3 ∧
    (∀ k, eq_end.toNat + 5 ≤ k → scr6[k]? = scr2[k]?) := by
  intro scr_a scr6
  have h0 : eq_end.toNat < scr2.length := by omega
  have h1 : eq_end.toNat + 1 < scr2.length := by omega
  have h2 : eq_end.toNat + 2 < scr2.length := by omega
  have h3 : eq_end.toNat + 3 < scr2.length := by omega
  refine ⟨by simp [scr6, scr_a], fun k hk => ?_, ?_, ?_, ?_, ?_, ?_, fun k hk => ?_⟩
  · simp only [scr6, scr_a, hw4, hw3, hw2, hw1,
      List.getElem?_set_ne (by omega : eq_end.toNat + 4 ≠ k),
      List.getElem?_set_ne (by omega : eq_end.toNat + 3 ≠ k),
      List.getElem?_set_ne (by omega : eq_end.toNat + 2 ≠ k),
      List.getElem?_set_ne (by omega : eq_end.toNat + 1 ≠ k),
      List.getElem?_set_ne (by omega : eq_end.toNat ≠ k)]
  · simp only [scr6, scr_a, hw4, hw3, hw2, hw1,
      List.getElem?_set_ne (by omega : eq_end.toNat + 4 ≠ eq_end.toNat),
      List.getElem?_set_ne (by omega : eq_end.toNat + 3 ≠ eq_end.toNat),
      List.getElem?_set_ne (by omega : eq_end.toNat + 2 ≠ eq_end.toNat),
      List.getElem?_set_ne (by omega : eq_end.toNat + 1 ≠ eq_end.toNat),
      List.getElem?_set_self h0]
  · simp only [scr6, scr_a, hw4, hw3, hw2, hw1,
      List.getElem?_set_ne (by omega : eq_end.toNat + 4 ≠ eq_end.toNat + 1),
      List.getElem?_set_ne (by omega : eq_end.toNat + 3 ≠ eq_end.toNat + 1),
      List.getElem?_set_ne (by omega : eq_end.toNat + 2 ≠ eq_end.toNat + 1)]
    exact List.getElem?_set_self (by simp [h1])
  · simp only [scr6, scr_a, hw4, hw3, hw2, hw1,
      List.getElem?_set_ne (by omega : eq_end.toNat + 4 ≠ eq_end.toNat + 2),
      List.getElem?_set_ne (by omega : eq_end.toNat + 3 ≠ eq_end.toNat + 2)]
    exact List.getElem?_set_self (by simp [h2])
  · simp only [scr6, scr_a, hw4, hw3, hw2, hw1,
      List.getElem?_set_ne (by omega : eq_end.toNat + 4 ≠ eq_end.toNat + 3)]
    exact List.getElem?_set_self (by simp [h3])
  · simp only [scr6, scr_a, hw4]
    exact List.getElem?_set_self (by simp [hbd])
  · simp only [scr6, scr_a, hw4, hw3, hw2, hw1,
      List.getElem?_set_ne (by omega : eq_end.toNat + 4 ≠ k),
      List.getElem?_set_ne (by omega : eq_end.toNat + 3 ≠ k),
      List.getElem?_set_ne (by omega : eq_end.toNat + 2 ≠ k),
      List.getElem?_set_ne (by omega : eq_end.toNat + 1 ≠ k),
      List.getElem?_set_ne (by omega : eq_end.toNat ≠ k)]

private theorem collect_arena_write3_ok {scr2 : List (BitVec 32)} {eq_end : BitVec 64}
    {hdr v0 v1 v2 : BitVec 32}
    (hw1 : (eq_end + 1#64).toNat = eq_end.toNat + 1)
    (hw2 : (eq_end + 2#64).toNat = eq_end.toNat + 2)
    (hw3 : (eq_end + 3#64).toNat = eq_end.toNat + 3)
    (hbd : eq_end.toNat + 3 < scr2.length) :
    let scr_a := (((scr2.set eq_end.toNat hdr).set (eq_end + 1#64).toNat v0).set
      (eq_end + 2#64).toNat v1).set (eq_end + 3#64).toNat v2
    scr_a.length = scr2.length ∧
    (∀ k < eq_end.toNat, scr_a[k]? = scr2[k]?) ∧
    scr_a[eq_end.toNat]? = some hdr ∧
    scr_a[eq_end.toNat + 1]? = some v0 ∧
    scr_a[eq_end.toNat + 2]? = some v1 ∧
    scr_a[eq_end.toNat + 3]? = some v2 ∧
    (∀ k, eq_end.toNat + 4 ≤ k → scr_a[k]? = scr2[k]?) := by
  intro scr_a
  have h0 : eq_end.toNat < scr2.length := by omega
  have h1 : eq_end.toNat + 1 < scr2.length := by omega
  have h2 : eq_end.toNat + 2 < scr2.length := by omega
  refine ⟨by simp [scr_a], fun k hk => ?_, ?_, ?_, ?_, ?_, fun k hk => ?_⟩
  · simp only [scr_a, hw3, hw2, hw1,
      List.getElem?_set_ne (by omega : eq_end.toNat + 3 ≠ k),
      List.getElem?_set_ne (by omega : eq_end.toNat + 2 ≠ k),
      List.getElem?_set_ne (by omega : eq_end.toNat + 1 ≠ k),
      List.getElem?_set_ne (by omega : eq_end.toNat ≠ k)]
  · simp only [scr_a, hw3, hw2, hw1,
      List.getElem?_set_ne (by omega : eq_end.toNat + 3 ≠ eq_end.toNat),
      List.getElem?_set_ne (by omega : eq_end.toNat + 2 ≠ eq_end.toNat),
      List.getElem?_set_ne (by omega : eq_end.toNat + 1 ≠ eq_end.toNat),
      List.getElem?_set_self h0]
  · simp only [scr_a, hw3, hw2, hw1,
      List.getElem?_set_ne (by omega : eq_end.toNat + 3 ≠ eq_end.toNat + 1),
      List.getElem?_set_ne (by omega : eq_end.toNat + 2 ≠ eq_end.toNat + 1)]
    exact List.getElem?_set_self (by simp [h1])
  · simp only [scr_a, hw3, hw2, hw1,
      List.getElem?_set_ne (by omega : eq_end.toNat + 3 ≠ eq_end.toNat + 2)]
    exact List.getElem?_set_self (by simp [h2])
  · simp only [scr_a, hw3]
    exact List.getElem?_set_self (by simp [hbd])
  · simp only [scr_a, hw3, hw2, hw1,
      List.getElem?_set_ne (by omega : eq_end.toNat + 3 ≠ k),
      List.getElem?_set_ne (by omega : eq_end.toNat + 2 ≠ k),
      List.getElem?_set_ne (by omega : eq_end.toNat + 1 ≠ k),
      List.getElem?_set_ne (by omega : eq_end.toNat ≠ k)]

theorem full_xor_collect_arena_wp (Γ : Env) :
    (∀ a m Q X, fullArenaNextSpec a m Q X →
      Γ "full_arena_next" [i64, i32] [i32] a m Q X) →
    (∀ a m Q X, fullXorSort5Spec a m Q X →
      Γ "full_xor_sort5" [i64, i32, i32] [.bool] a m Q X) →
    (∀ a m Q X, fullXorParityMaskSpec a m Q X →
      Γ "full_xor_parity_mask" [i32, .bool] [i32] a m Q X) →
    (∀ a m Q X, fullXorHtInsertSpec a m Q X →
      Γ "full_xor_ht_insert" [i64, i64, i64, i64, i32] [i64] a m Q X) →
    ∀ a m Q X, fullXorCollectArenaSpec a m Q X →
      Func.wp Γ full_xor_collect_arena_body a m Q X := by
  intro hAnxt hSort hPm hHt (h, ht_cap, ()) m Q X
    ⟨c, F0, F_cur, s, R, hc_eq, hs, hl0, hcap, hm, hQ⟩
  subst hc_eq
  unfold full_xor_collect_arena_body Func.wp; dsimp only
  c0_hsplit
  · have h0 : ht_cap = 0#64 := by bv_omega
    subst h0
    refine hQ 0#64 s m hs rfl rfl rfl ⟨rfl, rfl⟩
      (fun hn => by simp at hn) (fun _ => ⟨Nat.zero_le _, rfl, .done⟩) hm
  · have hnz : ht_cap ≠ 0#64 := by bv_omega
    obtain ⟨h7cap, hcap30⟩ := hcap hnz
    have hscr_len : s.scratch.scratch_buf.length = c.scratch_cap := hs.1.2.scratch_buf_len
    have hscr32 : s.scratch.scratch_buf.length < 2 ^ 32 := by
      have := c.hscr; have := dimacsBound_val; rw [hscr_len]; omega
    c0_hstraight
    have hm_f : (array (t := i32) c.pScratchBuf s.scratch.scratch_buf ⋆
        (FullScrBufRest c s ⋆ R)) m := focus_full_scr_buf hm
    let J0 : Tup Val [i64] → Mem 64 → Prop := fun (i, ()) m0 =>
      ∃ scr0 : List (BitVec 32),
        i.toNat ≤ ht_cap.toNat ∧ scr0.length = c.scratch_cap ∧
        (∀ j < i.toNat, scr0[j * 7]? = some 0#32) ∧
        (array (t := i32) c.pScratchBuf scr0 ⋆ (FullScrBufRest c s ⋆ R)) m0
    refine wp_loop_inv J0 (fun (i, ()) _ => ht_cap.toNat - i.toNat) (fun _ h => by
      c0_hstraight
      exact h (0#64, ()) m ⟨s.scratch.scratch_buf, Nat.zero_le _, hscr_len,
        fun _ hj => absurd hj (Nat.not_lt_zero _), hm_f⟩) ?_
    rintro J0_step ⟨i, _⟩ m0 ⟨scr0, hi_le, hlen0, hzero0, hm0⟩ hJ0_ih
    c0_hsplit
    · have hi_bd : i.toNat < ht_cap.toNat := by bv_omega
      have hidx_nat : (i * 7#64).toNat = i.toNat * 7 := by bv_omega
      have hidx_lt : (i * 7#64).toNat < scr0.length := by rw [hlen0, hidx_nat]; omega
      c0_hstraight
      refine hJ0_ih _ _ (by dsimp only; bv_omega) ⟨scr0.set (i * 7#64).toNat 0#32,
        by bv_omega, by simp [hlen0], fun j hj => ?_, hm⟩
      · have hj' : j < i.toNat + 1 := by bv_omega
        rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hj') with hj_old | rfl
        · rw [List.getElem?_set_ne (by rw [hidx_nat]; omega)]
          exact hzero0 j hj_old
        · rw [hidx_nat, List.getElem?_set_self (by rw [← hidx_nat]; exact hidx_lt)]
    · have hi_eq : i.toNat = ht_cap.toNat := by bv_omega
      have hht0 : XorHtInv (cnfOfClauses F_cur) s.core.cur_vars ht_cap.toNat scr0 := by
        intro s_idx hs_lt
        exact Or.inl (by simp [hzero0 s_idx (by rw [hi_eq]; exact hs_lt)])
      have hm1_full :
          (FullMem c { s with scratch := { s.scratch with scratch_buf := scr0 } } ⋆ R) m0 :=
        unfocus_full_scr_buf hm0
      let s0 : FullState := { s with scratch := { s.scratch with scratch_buf := scr0 } }
      have hs0 : FullSparseInvW c F0 F_cur s0 :=
        fullSparseInvW_upd_scratch_buf hs (by rw [hlen0, hscr_len])
      have hcv32 : s0.core.cur_vars < 2 ^ 32 := by
        have := hs0.1.1.cur_vars_le; have := c.hmaxv; have := dimacsBound_val; omega
      have h_alen32 : s0.core.arena_len < 2 ^ 32 := by
        have := hs0.1.1.arena_len_le; have := c.harena; have := dimacsBound_val; omega
      let Jdrain : Tup Val [i64, i64] → Mem 64 → Prop := fun (_r, _used, ()) m1 =>
        ∃ s1 : FullState,
          FullSparseInvW c F0 F_cur s1 ∧
          s1.core.cur_vars = s.core.cur_vars ∧
          s1.core.cur_level = 0 ∧
          s1.core.fuel = s.core.fuel ∧
          s1.core.inconsistent = s.core.inconsistent ∧
          FullExtScratchPres s s1 ∧
          XorHtInv (cnfOfClauses F_cur) s1.core.cur_vars ht_cap.toNat s1.scratch.scratch_buf ∧
          (FullMem c s1 ⋆ R) m1
      refine wp_join_group Jdrain ?_ ?_
      · rintro Jd ⟨_r0, _u0, _⟩ m1 ⟨s1, hs1, hcv1, hl1, hfuel1, hinc1, hext1, hht1, hm1⟩
        let J9 : Tup Val [i64, i64] → Mem 64 → Prop := fun (j, eq_end, ()) m2 =>
          ∃ scr2 : List (BitVec 32),
            j.toNat ≤ ht_cap.toNat ∧ eq_end.toNat ≤ j.toNat * 7 ∧
            scr2.length = c.scratch_cap ∧
            XorEqPoolOk (cnfOfClauses F_cur) s1.core.cur_vars scr2 eq_end.toNat 0 ∧
            (∀ s_idx, j.toNat ≤ s_idx → s_idx < ht_cap.toNat →
              let sb := s_idx * 7
              let sk_s := (scr2[sb]?.getD 0#32).toNat
              sk_s = 0 ∨ (3 ≤ sk_s ∧ sk_s ≤ 5 ∧
                let vs := (List.range sk_s).map fun k => (scr2[sb + 2 + k]?.getD 0#32).toNat
                List.Pairwise (· < ·) vs ∧ (∀ v ∈ vs, v < s1.core.cur_vars) ∧
                let sn := scr2[sb + 1]?.getD 0#32
                ∀ mv < 2 ^ sk_s, sn.getLsbD mv = true →
                  (cnfOfClauses F_cur).EntailsClause (cnfClause (xorMaskClause vs mv)))) ∧
            (array (t := i32) c.pScratchBuf scr2 ⋆ (FullScrBufRest c s1 ⋆ R)) m2
        have hscr1_len : s1.scratch.scratch_buf.length = c.scratch_cap := hs1.1.2.scratch_buf_len
        have hm1_f := focus_full_scr_buf hm1
        refine wp_loop_inv J9 (fun (j, _eq, ()) _ => ht_cap.toNat - j.toNat)
          (fun _ h => by
            c0_hstraight
            exact h (0#64, 0#64, ()) m1 ⟨s1.scratch.scratch_buf, Nat.zero_le _, Nat.zero_le _,
              hscr1_len, .done, fun s_idx _ hs_lt => hht1 s_idx hs_lt, hm1_f⟩) ?_
        rintro J9_step ⟨j, eq_end, _⟩ m2 ⟨scr2, hj_le, heq_le, hlen2, hpool2, hht2, hm2⟩ hJ9_ih
        c0_hsplit
        · have hj_bd : j.toNat < ht_cap.toNat := by bv_omega
          have hsb0_nat : (j * 7#64).toNat = j.toNat * 7 := by bv_omega
          have hsb0_lt : (j * 7#64).toNat < scr2.length := by rw [hlen2, hsb0_nat]; omega
          c0_hstraight
          let sk32 := scr2[(j * 7#64).toNat]
          let J10 : Tup Val [i64] → Mem 64 → Prop := fun (eq_next, ()) m3 =>
            ∃ scr3 : List (BitVec 32),
              eq_next.toNat ≤ (j.toNat + 1) * 7 ∧ scr3.length = c.scratch_cap ∧
              XorEqPoolOk (cnfOfClauses F_cur) s1.core.cur_vars scr3 eq_next.toNat 0 ∧
              (∀ s_idx, j.toNat + 1 ≤ s_idx → s_idx < ht_cap.toNat →
                let sb := s_idx * 7
                let sk_s := (scr3[sb]?.getD 0#32).toNat
                sk_s = 0 ∨ (3 ≤ sk_s ∧ sk_s ≤ 5 ∧
                  let vs := (List.range sk_s).map fun k => (scr3[sb + 2 + k]?.getD 0#32).toNat
                  List.Pairwise (· < ·) vs ∧ (∀ v ∈ vs, v < s1.core.cur_vars) ∧
                  let sn := scr3[sb + 1]?.getD 0#32
                  ∀ mv < 2 ^ sk_s, sn.getLsbD mv = true →
                    (cnfOfClauses F_cur).EntailsClause (cnfClause (xorMaskClause vs mv)))) ∧
              (array (t := i32) c.pScratchBuf scr3 ⋆ (FullScrBufRest c s1 ⋆ R)) m3
          refine wp_join_group J10 ?_ ?_
          · rintro J10_s ⟨eq_next, _⟩ m3 ⟨scr3, heq3_le, hlen3, hpool3, hht3, hm3⟩
            c0_hstraight
            have hj_succ : (j + 1#64).toNat = j.toNat + 1 := by bv_omega
            exact hJ9_ih (j + 1#64, eq_next, ()) m3 (by dsimp only; bv_omega)
              ⟨scr3, by rw [hj_succ]; omega, by rw [hj_succ]; exact heq3_le, hlen3,
                hpool3, by simpa [hj_succ] using hht3, hm3⟩
          · intro _ hJ10
            c0_hsplit
            · c0_hsplit
              · have hsb0_idx : j.toNat * (7 % 2 ^ 64) % 2 ^ 64 = (j * 7#64).toNat := by bv_omega
                have hsk3 : 3 ≤ sk32.toNat := by
                  have h3 : 3 ≤ (scr2[j.toNat * (7 % 2 ^ 64) % 2 ^ 64]'(by
                    rw [hsb0_idx]; exact hsb0_lt)).toNat := by bv_omega
                  dsimp only [sk32]
                  rw [← list_getElem_congr hsb0_idx]
                  exact h3
                have hsk5 : sk32.toNat ≤ 5 := by
                  have h5 : (scr2[j.toNat * (7 % 2 ^ 64) % 2 ^ 64]'(by
                    rw [hsb0_idx]; exact hsb0_lt)).toNat ≤ 5 := by bv_omega
                  dsimp only [sk32]
                  rw [← list_getElem_congr hsb0_idx]
                  exact h5
                have hsb1_nat : ((j * 7#64) + 1#64).toNat = j.toNat * 7 + 1 := by bv_omega
                have hsb1_lt : ((j * 7#64) + 1#64).toNat < scr2.length := by
                  rw [hlen2, hsb1_nat]; omega
                c0_hstraight
                let seen := scr2[((j * 7#64) + 1#64).toNat]
                apply wp_call_of_spec
                refine hPm _ _ _ _ ?_
                dsimp only
                apply wp_call_of_spec
                refine hPm _ _ _ _ ?_
                dsimp only
                let mask0 := parityMask sk32.toNat false
                let mask1 := parityMask sk32.toNat true
                have hsk_c0 : scr2[j.toNat * (7 % 2 ^ 64) % 2 ^ 64]'(by
                    rw [hsb0_idx]; exact hsb0_lt) = sk32 :=
                  list_getElem_congr hsb0_idx _ _
                have hsb1_idx : (j.toNat * (7 % 2 ^ 64) % 2 ^ 64 + 1 % 2 ^ 64) % 2 ^ 64 =
                    ((j * 7#64) + 1#64).toNat := by bv_omega
                have hseen_c0 :
                    scr2[(j.toNat * (7 % 2 ^ 64) % 2 ^ 64 + 1 % 2 ^ 64) % 2 ^ 64]'(by
                      rw [hsb1_idx]; exact hsb1_lt) = seen :=
                  list_getElem_congr hsb1_idx _ _
                have hseen_mod :
                    scr2[(j.toNat * 7 + 1) % 2 ^ 64]'(by
                      rw [Nat.mod_eq_of_lt (by omega), ← hsb1_nat]; exact hsb1_lt) = seen :=
                  list_getElem_congr (by rw [hsb1_nat, Nat.mod_eq_of_lt (by omega)]) _ _
                let b0 : Bool := decide ((seen &&& mask0) = mask0)
                let b1 : Bool := decide ((seen &&& mask1) = mask1)
                have hslot := hht2 j.toNat (Nat.le_refl _) hj_bd
                dsimp only at hslot
                have hsb0_lt' : j.toNat * 7 < scr2.length := by rw [← hsb0_nat]; exact hsb0_lt
                have hsk_eq : (scr2[j.toNat * 7]?.getD 0#32).toNat = sk32.toNat := by
                  simp [sk32, hsb0_nat, List.getElem?_eq_getElem hsb0_lt']
                rw [hsk_eq] at hslot
                rcases hslot with hbad0 | ⟨_, _, hvs_ss, hvs_lt, hent⟩
                · omega
                · let vs := (List.range sk32.toNat).map fun k =>
                    (scr2[j.toNat * 7 + 2 + k]?.getD 0#32).toNat
                  have hvs_len : vs.length = sk32.toNat := by simp [vs]
                  have hsb1_lt' : j.toNat * 7 + 1 < scr2.length := by rw [← hsb1_nat]; exact hsb1_lt
                  have hsn_eq : scr2[j.toNat * 7 + 1]?.getD 0#32 = seen := by
                    simp [seen, hsb1_nat, List.getElem?_eq_getElem hsb1_lt']
                  rw [hsn_eq] at hent
                  let JL11 : Unit → Mem 64 → Prop := fun _ m3 =>
                    m3 = m2 ∧ (b0 = false ∨ b1 = false)
                  refine wp_join0 (JL11 ()) ?_ ?_
                  · rintro JL11_s m3 ⟨hm3_eq, hnot_both⟩
                    rw [hm3_eq]
                    c0_hstraight
                    let JL12 : Tup Val [i64] → Mem 64 → Prop := fun (eq_next, ()) m5 =>
                      ∃ scr5 : List (BitVec 32),
                        eq_next.toNat ≤ (j.toNat + 1) * 7 ∧ scr5.length = c.scratch_cap ∧
                        XorEqPoolOk (cnfOfClauses F_cur) s1.core.cur_vars scr5 eq_next.toNat 0 ∧
                        (∀ s_idx, j.toNat + 1 ≤ s_idx → s_idx < ht_cap.toNat →
                          let sb := s_idx * 7
                          let sk_s := (scr5[sb]?.getD 0#32).toNat
                          sk_s = 0 ∨ (3 ≤ sk_s ∧ sk_s ≤ 5 ∧
                            let vs := (List.range sk_s).map fun k =>
                              (scr5[sb + 2 + k]?.getD 0#32).toNat
                            List.Pairwise (· < ·) vs ∧ (∀ v ∈ vs, v < s1.core.cur_vars) ∧
                            let sn := scr5[sb + 1]?.getD 0#32
                            ∀ mv < 2 ^ sk_s, sn.getLsbD mv = true →
                              (cnfOfClauses F_cur).EntailsClause
                                (cnfClause (xorMaskClause vs mv)))) ∧
                        (array (t := i32) c.pScratchBuf scr5 ⋆ (FullScrBufRest c s1 ⋆ R)) m5
                    refine wp_join_group JL12 ?_ ?_
                    · rintro JL12_s ⟨eq_next, _⟩ m5 ⟨scr5, heq5, hlen5, hpool5, hht5, hm5⟩
                      c0_hstraight
                      exact hJ10 (eq_next, ()) m5 ⟨scr5, heq5, hlen5, hpool5, hht5, hm5⟩
                    · intro _ hJ12
                      let JL13 : Unit → Mem 64 → Prop := fun _ m4 =>
                        m4 = m2 ∧ (b0 = true ∨ b1 = true)
                      refine wp_join0 (JL13 ()) ?_ ?_
                      · rintro JL13_s m4 ⟨hm4_eq, hor⟩
                        rw [hm4_eq]
                        c0_hstraight
                        let JL14 : Tup Val [i32] → Mem 64 → Prop := fun (rhs, ()) m5 =>
                          m5 = m2 ∧ (rhs = 0#32 ∨ rhs = 1#32) ∧
                          seen &&& parityMask sk32.toNat (if rhs = 1#32 then false else true) =
                            parityMask sk32.toNat (if rhs = 1#32 then false else true)
                        refine wp_join_group JL14 ?_ ?_
                        · rintro JL14_s ⟨rhs, _⟩ m5 ⟨hm5_eq, hrhs, hmask_rhs⟩
                          rw [hm5_eq]
                          have hsb2_nat : ((j * 7#64) + 2#64).toNat = j.toNat * 7 + 2 := by bv_omega
                          have hsb3_nat : ((j * 7#64) + 3#64).toNat = j.toNat * 7 + 3 := by bv_omega
                          have hsb4_nat : ((j * 7#64) + 4#64).toNat = j.toNat * 7 + 4 := by bv_omega
                          have hsb5_nat : ((j * 7#64) + 5#64).toNat = j.toNat * 7 + 5 := by bv_omega
                          have hsb6_nat : ((j * 7#64) + 6#64).toNat = j.toNat * 7 + 6 := by bv_omega
                          have hsb2_lt : ((j * 7#64) + 2#64).toNat < scr2.length := by
                            rw [hlen2, hsb2_nat]; omega
                          have hsb3_lt : ((j * 7#64) + 3#64).toNat < scr2.length := by
                            rw [hlen2, hsb3_nat]; omega
                          have hsb4_lt : ((j * 7#64) + 4#64).toNat < scr2.length := by
                            rw [hlen2, hsb4_nat]; omega
                          have hsb5_lt : ((j * 7#64) + 5#64).toNat < scr2.length := by
                            rw [hlen2, hsb5_nat]; omega
                          have hsb6_lt : ((j * 7#64) + 6#64).toNat < scr2.length := by
                            rw [hlen2, hsb6_nat]; omega
                          have hw0_lt : eq_end.toNat < scr2.length := by rw [hlen2]; omega
                          have hw1_nat : (eq_end + 1#64).toNat = eq_end.toNat + 1 := by bv_omega
                          have hw2_nat : (eq_end + 2#64).toNat = eq_end.toNat + 2 := by bv_omega
                          have hw3_nat : (eq_end + 3#64).toNat = eq_end.toNat + 3 := by bv_omega
                          have hw4_nat : (eq_end + 4#64).toNat = eq_end.toNat + 4 := by bv_omega
                          have hw5_nat : (eq_end + 5#64).toNat = eq_end.toNat + 5 := by bv_omega
                          have hw1_lt : (eq_end + 1#64).toNat < scr2.length := by
                            rw [hlen2, hw1_nat]; omega
                          have hw2_lt : (eq_end + 2#64).toNat < scr2.length := by
                            rw [hlen2, hw2_nat]; omega
                          have hw3_lt : (eq_end + 3#64).toNat < scr2.length := by
                            rw [hlen2, hw3_nat]; omega
                          c0_hstraight
                          let v0 := scr2[((j * 7#64) + 2#64).toNat]
                          let v1 := scr2[((j * 7#64) + 3#64).toNat]
                          let v2 := scr2[((j * 7#64) + 4#64).toNat]
                          let v3 := scr2[((j * 7#64) + 5#64).toNat]
                          let v4 := scr2[((j * 7#64) + 6#64).toNat]
                          let hdr := (sk32 ||| (sk32 <<< (16#32 &&& 31#32))) |||
                            (rhs <<< (31#32 &&& 31#32))
                          let scr_a := (((scr2.set eq_end.toNat hdr).set
                            (eq_end + 1#64).toNat v0).set (eq_end + 2#64).toNat v1).set
                            (eq_end + 3#64).toNat v2
                          have hlena : scr_a.length = scr2.length := by simp [scr_a]
                          have hw4_lt : (eq_end + 4#64).toNat < scr_a.length := by
                            rw [hlena, hlen2, hw4_nat]; omega
                          let JL15 : Mem 64 → Prop := fun m6 =>
                            ∃ scr6 : List (BitVec 32),
                              scr6.length = scr2.length ∧
                              (∀ k < eq_end.toNat, scr6[k]? = scr2[k]?) ∧
                              scr6[eq_end.toNat]? = some hdr ∧
                              scr6[eq_end.toNat + 1]? = some v0 ∧
                              scr6[eq_end.toNat + 2]? = some v1 ∧
                              scr6[eq_end.toNat + 3]? = some v2 ∧
                              (4 ≤ sk32.toNat → scr6[eq_end.toNat + 4]? = some v3) ∧
                              (∀ k, eq_end.toNat + 5 ≤ k → scr6[k]? = scr2[k]?) ∧
                              (4 ≤ sk32.toNat → ∀ k, eq_end.toNat + 5 ≤ k → scr6[k]? = scr2[k]?) ∧
                              (sk32.toNat = 3 → ∀ k, eq_end.toNat + 4 ≤ k → scr6[k]? = scr2[k]?) ∧
                              (array (t := i32) c.pScratchBuf scr6 ⋆ (FullScrBufRest c s1 ⋆ R)) m6
                          refine wp_join0 JL15 ?_ ?_
                          · rintro JL15_s m6 ⟨scr6, hlen6, hpre6, hhdr6, hw0_6, hw1_6, hw2_6, hw3_6,
                                hsuf5, _, hsuf3, hm6⟩
                            let JL16 : Mem 64 → Prop := fun m7 =>
                              ∃ scr7 : List (BitVec 32),
                                scr7.length = scr2.length ∧
                                (∀ k < eq_end.toNat, scr7[k]? = scr2[k]?) ∧
                                scr7[eq_end.toNat]? = some hdr ∧
                                scr7[eq_end.toNat + 1]? = some v0 ∧
                                scr7[eq_end.toNat + 2]? = some v1 ∧
                                scr7[eq_end.toNat + 3]? = some v2 ∧
                                (4 ≤ sk32.toNat → scr7[eq_end.toNat + 4]? = some v3) ∧
                                (5 ≤ sk32.toNat → scr7[eq_end.toNat + 5]? = some v4) ∧
                                (∀ k, eq_end.toNat + 1 + sk32.toNat ≤ k → scr7[k]? = scr2[k]?) ∧
                                (array (t := i32) c.pScratchBuf scr7 ⋆ (FullScrBufRest c s1 ⋆ R)) m7
                            refine wp_join0 JL16 ?_ ?_
                            · rintro JL16_s m7 ⟨scr7, hlen7, hpre7, hhdr7, hw0_7, hw1_7, hw2_7,
                                  hw3_7, hw4_7, hsuf7, hm7⟩
                              c0_hstraight
                              have hpk := pack_hdr_drain_fields sk32 (rhs.setWidth 64) hsk3 hsk5
                                (by rcases hrhs with rfl | rfl <;> simp)
                              obtain ⟨hst_p, hcl_p, hrhs_p⟩ := hpk
                              have hhdr_fix : (sk32 ||| (sk32 <<< (16#32 &&& 31#32))) |||
                                  ((rhs.setWidth 64).setWidth 32 <<< (31#32 &&& 31#32)) = hdr := by
                                rcases hrhs with rfl | rfl <;> rfl
                              rw [hhdr_fix] at hst_p hcl_p hrhs_p
                              have hmask_p : seen &&&
                                  parityMask sk32.toNat (!decide (rhs.setWidth 64 = 1#64)) =
                                  parityMask sk32.toNat (!decide (rhs.setWidth 64 = 1#64)) := by
                                rcases hrhs with rfl | rfl <;> simpa using hmask_rhs
                              have hslot_ok := collect_arena_slot_append_ok hj_bd heq_le
                                (by rw [hlen2]; exact h7cap) hlen7 hsk3 hsk5 hpool2
                                (fun s_idx h1 h2 => hht2 s_idx h1 h2) hsk_eq
                                (by simp [seen, hsb1_nat])
                                (by simp [v0, hsb2_nat])
                                (by simp [v1, hsb3_nat])
                                (by simp [v2, hsb4_nat])
                                (by simp [v3, hsb5_nat])
                                (by simp [v4, hsb6_nat])
                                hrhs_p hmask_p hst_p hcl_p hpre7 hsuf7
                                hhdr7 hw0_7 hw1_7 hw2_7 hw3_7 hw4_7
                              have heq_next_nat : (eq_end + 1#64 + sk32.setWidth 64).toNat =
                                  eq_end.toNat + 1 + sk32.toNat := by
                                have : eq_end.toNat + 1 + sk32.toNat ≤ c.scratch_cap := by omega
                                have := c.hscr; have := dimacsBound_val; bv_omega
                              exact hJ12 (eq_end + 1#64 + sk32.setWidth 64, ()) m7
                                ⟨scr7, by rw [heq_next_nat]; omega,
                                  by rw [hlen7, hlen2], by rw [heq_next_nat]; exact hslot_ok.1,
                                  by simpa using hslot_ok.2, hm7⟩
                            · intro _ hJ16
                              c0_hsplit
                              · have hsk5' : 5 ≤ sk32.toNat := by
                                  have h5 : 5 ≤ (scr2[j.toNat * (7 % 2 ^ 64) % 2 ^ 64]'(by
                                    rw [hsb0_idx]; exact hsb0_lt)).toNat := by bv_omega
                                  dsimp only [sk32]; rw [← list_getElem_congr hsb0_idx]; exact h5
                                have hw5_lt : (eq_end + 5#64).toNat < scr6.length := by
                                  rw [hlen6, hlen2, hw5_nat]; omega
                                c0_hstraight
                                refine hJ16 _ ⟨scr6.set (eq_end + 5#64).toNat v4,
                                  by simp [hlen6], fun k hk => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hm⟩
                                · rw [List.getElem?_set_ne (by omega)]; exact hpre6 k hk
                                · rw [List.getElem?_set_ne (by omega)]; exact hhdr6
                                · rw [List.getElem?_set_ne (by omega)]; exact hw0_6
                                · rw [List.getElem?_set_ne (by omega)]; exact hw1_6
                                · rw [List.getElem?_set_ne (by omega)]; exact hw2_6
                                · intro hk4; rw [List.getElem?_set_ne (by omega)]; exact hw3_6 hk4
                                · intro _
                                  rw [hw5_nat]
                                  exact List.getElem?_set_self (by rw [← hw5_nat]; exact hw5_lt)
                                · intro k hk
                                  rw [List.getElem?_set_ne (by omega)]
                                  exact hsuf5 k (by omega)
                              · have hle4 : sk32.toNat ≤ 4 := by
                                  have h4 : (scr2[j.toNat * (7 % 2 ^ 64) % 2 ^ 64]'(by
                                    rw [hsb0_idx]; exact hsb0_lt)).toNat ≤ 4 := by bv_omega
                                  dsimp only [sk32]; rw [← list_getElem_congr hsb0_idx]; exact h4
                                c0_hstraight
                                refine hJ16 _ ⟨scr6, hlen6, hpre6, hhdr6, hw0_6, hw1_6, hw2_6,
                                  hw3_6, fun hk => absurd hk (by omega), fun k hk => ?_, hm6⟩
                                rcases Nat.eq_or_lt_of_le hsk3 with h3 | h4
                                · exact hsuf3 h3.symm k (by omega)
                                · exact hsuf5 k (by omega)
                          · intro _ hJ15
                            c0_hsplit
                            · have hsk4' : 4 ≤ sk32.toNat := by
                                have h4 : 4 ≤ (scr2[j.toNat * (7 % 2 ^ 64) % 2 ^ 64]'(by
                                  rw [hsb0_idx]; exact hsb0_lt)).toNat := by bv_omega
                                dsimp only [sk32]; rw [← list_getElem_congr hsb0_idx]; exact h4
                              c0_hstraight
                              obtain ⟨hl, hp, hh, h0, h1, h2, h3, hsuf⟩ :=
                                collect_arena_write4_ok (hdr := hdr) (v0 := v0) (v1 := v1)
                                  (v2 := v2) (v3 := v3) hw1_nat hw2_nat hw3_nat hw4_nat
                                  (by rw [hlen2]; omega)
                              exact hJ15 _ ⟨scr_a.set (eq_end + 4#64).toNat v3, hl, hp, hh,
                                h0, h1, h2, fun _ => h3, hsuf, fun _ => hsuf,
                                fun h3e => absurd h3e (by omega), hm⟩
                            · have hsk3_eq : sk32.toNat = 3 := by
                                have hle3 : (scr2[j.toNat * (7 % 2 ^ 64) % 2 ^ 64]'(by
                                  rw [hsb0_idx]; exact hsb0_lt)).toNat ≤ 3 := by bv_omega
                                have hle3' : sk32.toNat ≤ 3 := by
                                  dsimp only [sk32]; rw [← list_getElem_congr hsb0_idx]; exact hle3
                                omega
                              c0_hstraight
                              obtain ⟨hl, hp, hh, h0, h1, h2, hsuf⟩ :=
                                collect_arena_write3_ok (hdr := hdr) (v0 := v0) (v1 := v1)
                                  (v2 := v2) hw1_nat hw2_nat hw3_nat (by rw [hlen2]; omega)
                              exact hJ15 _ ⟨scr_a, hl, hp, hh, h0, h1, h2,
                                fun h4 => absurd h4 (by omega), fun k hk => hsuf k (by omega),
                                fun h4 => absurd h4 (by omega), fun _ => hsuf, hm⟩
                        · intro _ hJ14
                          c0_hsplit
                          · have hm0_eq : seen &&& mask0 = mask0 := by
                              have h1 := liftCmp_eq_i32_true hc
                              simpa [lift2, mask0, hsk_c0, hseen_mod] using h1
                            have hb0t : b0 = true := by simp [b0, mask0, hm0_eq]
                            exact hJ14 (1#32, ()) m2
                              ⟨rfl, Or.inr rfl, by simpa [b0, mask0] using hb0t⟩
                          · have hb0f : b0 = false := by
                              have hne : seen &&& mask0 ≠ mask0 := by
                                have h1 := liftCmp_eq_i32_false hc
                                simpa [lift2, mask0, hsk_c0, hseen_mod] using h1
                              simp [b0, mask0, hne]
                            have hb1t : b1 = true := by
                              rcases hor with h | h
                              · exfalso; rw [hb0f] at h; cases h
                              · exact h
                            exact hJ14 (0#32, ()) m2
                              ⟨rfl, Or.inl rfl, by simpa [b1, mask1] using hb1t⟩
                      · intro _ hJ13
                        c0_hsplit
                        · have hm0_eq : seen &&& mask0 = mask0 := by
                            have h1 := liftCmp_eq_i32_true hc
                            simpa [lift2, mask0, hsk_c0, hseen_mod] using h1
                          exact hJ13 m2 ⟨rfl, Or.inl (by simp [b0, mask0, hm0_eq])⟩
                        · clear hc
                          c0_hsplit
                          · have hm1_eq : seen &&& mask1 = mask1 := by
                              have h1 := liftCmp_eq_i32_true hc
                              simpa [lift2, mask1, hsk_c0, hseen_mod] using h1
                            exact hJ13 m2 ⟨rfl, Or.inr (by simp [b1, mask1, hm1_eq])⟩
                          · c0_hstraight
                            exact hJ12 (eq_end, ()) m2 ⟨scr2, by omega, hlen2, hpool2,
                              fun s_idx hs_ge hs_lt => hht2 s_idx (by omega) hs_lt, hm2⟩
                  · intro J11 hJ11
                    c0_hsplit
                    · have hm0_eq : seen &&& mask0 = mask0 := by
                        have h1 := liftCmp_eq_i32_true hc
                        simpa [lift2, mask0, hsk_c0, hseen_mod] using h1
                      clear hc
                      c0_hsplit
                      · have hm1_eq : seen &&& mask1 = mask1 := by
                          have h1 := liftCmp_eq_i32_true hc
                          simpa [lift2, mask1, hsk_c0, hseen_mod] using h1
                        have hxs_t : XorVarsSound (cnfOfClauses F_cur) vs true := by
                          have := xorVarsSound_of_parityMask (F := cnfOfClauses F_cur)
                            (vs := vs) (seen := seen) (p := false)
                            (by rw [hvs_len]; exact hsk3) (by rw [hvs_len]; exact hsk5)
                            (by rw [hvs_len]; exact hm0_eq) (by rw [hvs_len]; exact hent)
                          simpa using this
                        have hxs_f : XorVarsSound (cnfOfClauses F_cur) vs false := by
                          have := xorVarsSound_of_parityMask (F := cnfOfClauses F_cur)
                            (vs := vs) (seen := seen) (p := true)
                            (by rw [hvs_len]; exact hsk3) (by rw [hvs_len]; exact hsk5)
                            (by rw [hvs_len]; exact hm1_eq) (by rw [hvs_len]; exact hent)
                          simpa using this
                        have hc_unsat : (cnfOfClauses F_cur).Unsat :=
                          xorVarsSound_both_unsat hxs_f hxs_t
                        have hF0_unsat : F0.Unsat :=
                          unsat_of_sparseW_inconsistent hs1 hc_unsat
                        have hm2_full :
                            (FullMem c
                              { s1 with scratch := { s1.scratch with scratch_buf := scr2 } } ⋆
                                R) m2 :=
                          unfocus_full_scr_buf hm2
                        let s2 : FullState :=
                          { s1 with scratch := { s1.scratch with scratch_buf := scr2 } }
                        have hs2 : FullSparseInvW c F0 F_cur s2 :=
                          fullSparseInvW_upd_scratch_buf hs1 (by rw [hlen2, hscr1_len])
                        c0_hstraight
                        let s3 : FullState :=
                          { s2 with core := { s2.core with inconsistent := 1#64 } }
                        have hs3 : FullSparseInvW c F0 F_cur s3 :=
                          fullSparseInvW_upd_inc hs2 1#64 (fun _ => hc_unsat)
                        exact hQ 0xFFFFFFFFFFFFFFFF#64 s3 _ hs3 hcv1 (hl1.trans hl0.symm) hfuel1
                          hext1 (fun _ => ⟨hF0_unsat, by simp [s3]⟩)
                          (fun hn => by simp at hn) hm
                      · have hb1f : b1 = false := by
                          have hne : seen &&& mask1 ≠ mask1 := by
                            have h1 := liftCmp_eq_i32_false hc
                            simpa [lift2, mask1, hsk_c0, hseen_mod] using h1
                          simp [b1, mask1, hne]
                        exact hJ11 m2 ⟨rfl, Or.inr hb1f⟩
                    · have hb0f : b0 = false := by
                        have hne : seen &&& mask0 ≠ mask0 := by
                          have h1 := liftCmp_eq_i32_false hc
                          simpa [lift2, mask0, hsk_c0, hseen_mod] using h1
                        simp [b0, mask0, hne]
                      exact hJ11 m2 ⟨rfl, Or.inl hb0f⟩
              · c0_hstraight
                exact hJ10 (eq_end, ()) m2 ⟨scr2, by omega, hlen2, hpool2,
                  fun s_idx hs_ge hs_lt => hht2 s_idx (by omega) hs_lt, hm2⟩
            · c0_hstraight
              exact hJ10 (eq_end, ()) m2 ⟨scr2, by omega, hlen2, hpool2,
                fun s_idx hs_ge hs_lt => hht2 s_idx (by omega) hs_lt, hm2⟩
        · c0_hstraight
          have hm2_full : (FullMem c
              { s1 with scratch := { s1.scratch with scratch_buf := scr2 } } ⋆ R) m2 :=
            unfocus_full_scr_buf hm2
          let s2 : FullState := { s1 with scratch := { s1.scratch with scratch_buf := scr2 } }
          have hs2 : FullSparseInvW c F0 F_cur s2 :=
            fullSparseInvW_upd_scratch_buf hs1 (by rw [hlen2, hscr1_len])
          refine hQ eq_end s2 m2 hs2 hcv1 (hl1.trans hl0.symm) hfuel1 hext1
            (fun heq => by
              exfalso; rw [heq] at heq_le; have := c.hscr; have := dimacsBound_val; bv_omega)
            (fun _ => ⟨by omega, hinc1, hpool2⟩) hm2_full
      · intro _ hJdrain
        have hr0_mem : 0 = s0.core.arena_len ∨ 0 ∈ fullArenaClauseRefs s0 :=
          fullArena_start_mem hs0.2.1.arena
        let J2 : Tup Val [i64, i64] → Mem 64 → Prop := fun (r, used, ()) m1 =>
          ∃ s1 : FullState,
            FullSparseInvW c F0 F_cur s1 ∧
            s1.core.cur_vars = s.core.cur_vars ∧
            s1.core.cur_level = 0 ∧
            s1.core.fuel = s.core.fuel ∧
            s1.core.inconsistent = s.core.inconsistent ∧
            s1.core.arena = s.core.arena ∧
            s1.core.arena_len = s.core.arena_len ∧
            s1.core.vals = s.core.vals ∧
            FullExtScratchPres s s1 ∧
            XorHtInv (cnfOfClauses F_cur) s1.core.cur_vars ht_cap.toNat s1.scratch.scratch_buf ∧
            (r.toNat = s1.core.arena_len ∨ r.toNat ∈ fullArenaClauseRefs s1) ∧
            (FullMem c s1 ⋆ R) m1
        refine wp_loop_inv J2 (fun (r, _u, ()) _ => s.core.arena_len - r.toNat)
          (fun _ h => by
            c0_hstraight
            exact h (0#64, 0#64, ()) m0 ⟨s0, hs0, rfl, hl0, rfl, rfl, rfl, rfl, rfl, ⟨rfl, rfl⟩,
              hht0, by simpa [s0] using hr0_mem, hm1_full⟩) ?_
        rintro J2_step ⟨r, used, _⟩ m1 ⟨s1, hs1, hcv1, hl1, hfuel1, hinc1, har1, hal1, hvals1,
            hext1, hht1, hr_mem, hm1⟩ hJ2_ih
        have hr_le : r.toNat ≤ s1.core.arena_len := by
          rcases hr_mem with heq | hmem
          · exact Nat.le_of_eq heq
          · have := (hs1.2.1.arena.refs_wf r.toNat hmem).1; omega
        c0_hsplit
        · have hr_bd : r.toNat < s1.core.arena_len := by bv_omega
          have hr_ref : r.toNat ∈ fullArenaClauseRefs s1 := by
            rcases hr_mem with h | h
            · omega
            · exact h
          c0_hsplit
          · exact hJdrain (r, used, ()) m1 ⟨s1, hs1, hcv1, hl1, hfuel1, hinc1, hext1, hht1, hm1⟩
          · have hal_bd : s1.core.arena_len < 2 ^ 32 := by
              have := hs1.1.1.arena_len_le; have := c.harena; have := dimacsBound_val; omega
            have hal0_bd : s.core.arena_len < 2 ^ 32 := by rw [← hal1]; exact hal_bd
            have hr_lt_ar : r.toNat < s1.core.arena.length := by
              have := hs1.1.1.arena_len_le; have := hs1.1.1.arena_len_arr; omega
            have hr3_le : r.toNat + 3 ≤ s1.core.arena_len := by
              have := hal0_bd; have := hal1; bv_omega
            have hr2_nat : (r + 2#64).toNat = r.toNat + 2 := by bv_omega
            have hr2_lt_ar : (r + 2#64).toNat < s1.core.arena.length := by
              have := hs1.1.1.arena_len_le; have := hs1.1.1.arena_len_arr; omega
            have hrz_eq : (r.setWidth 32).toNat = r.toNat := by
              rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
            c0_hstraight
            apply wp_call_of_spec
            refine hAnxt _ _ _ _ ⟨c, s1, R, rfl, hs1.1, hm1, ?_⟩
            dsimp only
            simp only [Arg.val]
            rw [hrz_eq]
            c0_hstraight
            let next32 := BitVec.ofNat 32
              (Full.fullArenaNextOff s1.core.arena s1.core.arena_len r.toNat)
            have hnext_nat : (next32.setWidth 64).toNat =
                fullArenaNextOff s1.core.arena s1.core.arena_len r.toNat := by
              have hle_next := (hs1.2.1.arena.refs_wf r.toNat hr_ref).2.2.2.1
              rw [bv_zext32_toNat]
              dsimp only [next32]
              rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
            have hnext_mem : (next32.setWidth 64).toNat = s1.core.arena_len ∨
                (next32.setWidth 64).toNat ∈ fullArenaClauseRefs s1 := by
              rw [hnext_nat]
              exact fullArenaClauseRefs_next hs1.2.1.arena hr_ref
            let JL3 : Tup Val [i64] → Mem 64 → Prop := fun (used', ()) m3 =>
              ∃ s3 : FullState,
                FullSparseInvW c F0 F_cur s3 ∧
                s3.core.cur_vars = s.core.cur_vars ∧
                s3.core.cur_level = 0 ∧
                s3.core.fuel = s.core.fuel ∧
                s3.core.inconsistent = s.core.inconsistent ∧
                s3.core.arena = s.core.arena ∧
                s3.core.arena_len = s.core.arena_len ∧
                s3.core.vals = s.core.vals ∧
                FullExtScratchPres s s3 ∧
                XorHtInv (cnfOfClauses F_cur) s3.core.cur_vars ht_cap.toNat s3.scratch.scratch_buf ∧
                (FullMem c s3 ⋆ R) m3
            refine wp_join_group JL3 ?_ ?_
            · rintro JL3_s ⟨used', _⟩ m3 ⟨s3, hs3, hcv3, hl3, hfuel3, hinc3, har3, hal3, hv3,
                  hext3, hht3, hm3⟩
              c0_hsplit
              · exact hJdrain (r, used', ()) m3 ⟨s3, hs3, hcv3, hl3, hfuel3, hinc3,
                  hext3, hht3, hm3⟩
              · have hmem3 : (next32.setWidth 64).toNat = s3.core.arena_len ∨
                    (next32.setWidth 64).toNat ∈ fullArenaClauseRefs s3 := by
                  have hrefs : fullArenaClauseRefs s3 = fullArenaClauseRefs s1 := by
                    unfold fullArenaClauseRefs fullArenaClauseRefsCore
                    rw [har3, hal3, har1, hal1]
                  rw [hal3, ← hal1, hrefs]; exact hnext_mem
                have hdec : s.core.arena_len - (next32.setWidth 64).toNat <
                    s.core.arena_len - r.toNat := by
                  have : r.toNat < (next32.setWidth 64).toNat := by bv_omega
                  omega
                exact hJ2_ih (next32.setWidth 64, used', ()) m3 hdec
                  ⟨s3, hs3, hcv3, hl3, hfuel3, hinc3, har3, hal3, hv3, hext3, hht3, hmem3, hm3⟩
            · intro hCont3 hJ3
              let hdr_ar := s1.core.arena[r.toNat]
              let sz_ar := s1.core.arena[(r + 2#64).toNat]
              c0_hsplit
              · c0_hsplit
                · c0_hsplit
                  · c0_hsplit
                    · have hgarb_f : fullArenaClauseGarb s1 r.toNat = false := by
                        unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
                        have hg : hdr_ar &&& 524288#32 = 0#32 := by
                          dsimp only [hdr_ar]; bv_omega
                        simp [hr_lt_ar]
                        exact hg
                      have hsz_eq : fullArenaClauseSizeCore s1.core r.toNat = sz_ar.toNat := by
                        unfold fullArenaClauseSizeCore
                        rw [List.getElem?_eq_getElem (by rw [← hr2_nat]; exact hr2_lt_ar)]
                        simp [sz_ar, hr2_nat]
                      have hent_r : (cnfOfClauses F_cur).EntailsClause
                          (cnfClause (fullArenaClauseLits s1 r.toNat)) :=
                        hs1.2.1.arena.entails r.toNat hr_ref hgarb_f
                      have hlits_lt : ∀ l ∈ fullArenaClauseLits s1 r.toNat,
                          l < 2 * s1.core.cur_vars :=
                        hs1.2.1.arena.lits_lt r.toNat hr_ref hgarb_f
                      have hsz_le_rem : r.toNat + 3 + sz_ar.toNat ≤ s1.core.arena_len := by
                        dsimp only [sz_ar]; bv_omega
                      have hlits_len : (fullArenaClauseLits s1 r.toNat).length = sz_ar.toNat := by
                        unfold fullArenaClauseLits fullArenaClauseLitsCore
                        rw [hsz_eq, List.length_map, List.length_take, List.length_drop]
                        have := hs1.1.1.arena_len_le; have := hs1.1.1.arena_len_arr
                        omega
                      let JL4 : Tup Val [i32, Ty.bool, i32] → Mem 64 → Prop :=
                          fun (cnt, sat_b, _i, ()) m4 =>
                        ∃ s4 : FullState,
                          FullSparseInvW c F0 F_cur s4 ∧
                          s4.core.cur_vars = s.core.cur_vars ∧
                          s4.core.cur_level = 0 ∧
                          s4.core.fuel = s.core.fuel ∧
                          s4.core.inconsistent = s.core.inconsistent ∧
                          s4.core.arena = s.core.arena ∧
                          s4.core.arena_len = s.core.arena_len ∧
                          s4.core.vals = s.core.vals ∧
                          s4.scratch.scratch_buf = s1.scratch.scratch_buf ∧
                          FullExtScratchPres s s4 ∧
                          (sat_b = false → cnt.toNat ≤ 5 →
                            cnt.toNat ≤ s4.core.cur_vars ∧
                            (∀ k < cnt.toNat,
                              (s4.core.tmp[k]?.getD 0#32).toNat < 2 * s4.core.cur_vars) ∧
                            (cnfOfClauses F_cur).EntailsClause
                              (cnfClause ((s4.core.tmp.take cnt.toNat).map BitVec.toNat))) ∧
                          (FullMem c s4 ⋆ R) m4
                      refine wp_join_group JL4 ?_ ?_
                      · rintro JL4_s ⟨cnt, sat_b, _i, _⟩ m4 ⟨s4, hs4, hcv4, hl4, hf4, hi4, ha4,
                            hl4a, hv4, hscr4, he4, hcls4, hm4⟩
                        have hht4 : XorHtInv (cnfOfClauses F_cur) s4.core.cur_vars ht_cap.toNat
                            s4.scratch.scratch_buf := by
                          rw [hscr4, hcv4, ← hcv1]; exact hht1
                        c0_hstraight
                        let JL7 : Tup Val [i64] → Mem 64 → Prop := fun (used', ()) m7 =>
                          ∃ s7 : FullState,
                            FullSparseInvW c F0 F_cur s7 ∧
                            s7.core.cur_vars = s.core.cur_vars ∧
                            s7.core.cur_level = 0 ∧
                            s7.core.fuel = s.core.fuel ∧
                            s7.core.inconsistent = s.core.inconsistent ∧
                            s7.core.arena = s.core.arena ∧
                            s7.core.arena_len = s.core.arena_len ∧
                            s7.core.vals = s.core.vals ∧
                            FullExtScratchPres s s7 ∧
                            XorHtInv (cnfOfClauses F_cur) s7.core.cur_vars ht_cap.toNat
                              s7.scratch.scratch_buf ∧
                            (FullMem c s7 ⋆ R) m7
                        refine wp_join_group JL7 ?_ ?_
                        · rintro JL7_s ⟨used', _⟩ m7 ⟨s7, hs7, hcv7, hl7, hf7, hi7, ha7, hl7a, hv7,
                              he7, hht7, hm7⟩
                          c0_hstraight
                          exact hJ3 (used', ()) m7 ⟨s7, hs7, hcv7, hl7, hf7, hi7, ha7, hl7a, hv7,
                            he7, hht7, hm7⟩
                        · intro _ hJ7
                          c0_hsplit
                          · c0_hstraight
                            exact hJ7 (used, ()) m4 ⟨s4, hs4, hcv4, hl4, hf4, hi4, ha4, hl4a, hv4,
                              he4, hht4, hm4⟩
                          · have hbad0 : sat_b = false := by bv_omega
                            c0_hsplit
                            · c0_hsplit
                              · have hcnt_bd : cnt.toNat ≤ 5 := by bv_omega
                                have hcnt3 : 3 ≤ cnt.toNat := by bv_omega
                                obtain ⟨hcnt_cv, hlt_tmp, hent_tmp⟩ := hcls4 hbad0 hcnt_bd
                                have hm4_f := focus_full_tmp_scr hm4
                                have htmp_len4 : s4.core.tmp.length = c.max_vars :=
                                  hs4.1.1.tmp_len_arr
                                have htmp31 : s4.core.tmp.length < 2 ^ 31 := by
                                  have := c.hmaxv; have := dimacsBound_val; rw [htmp_len4]; omega
                                have hcv32_eq :
                                    ((BitVec.ofNat 64 s4.core.cur_vars).setWidth 32).toNat =
                                      s4.core.cur_vars := by
                                  have := hs4.1.1.cur_vars_le; have := c.hmaxv
                                  have := dimacsBound_val
                                  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
                                  omega
                                have hcv31 :
                                    ((BitVec.ofNat 64 s4.core.cur_vars).setWidth 32).toNat <
                                      2 ^ 31 := by
                                  have := hs4.1.1.cur_vars_le; have := c.hmaxv
                                  have := dimacsBound_val; omega
                                let JL8 : Tup Val [i64] → Mem 64 → Prop := fun (used', ()) m8 =>
                                  ∃ s8 : FullState,
                                    FullSparseInvW c F0 F_cur s8 ∧
                                    s8.core.cur_vars = s.core.cur_vars ∧
                                    s8.core.cur_level = 0 ∧
                                    s8.core.fuel = s.core.fuel ∧
                                    s8.core.inconsistent = s.core.inconsistent ∧
                                    s8.core.arena = s.core.arena ∧
                                    s8.core.arena_len = s.core.arena_len ∧
                                    s8.core.vals = s.core.vals ∧
                                    FullExtScratchPres s s8 ∧
                                    XorHtInv (cnfOfClauses F_cur) s8.core.cur_vars ht_cap.toNat
                                      s8.scratch.scratch_buf ∧
                                    (FullMem c s8 ⋆ R) m8
                                refine wp_join_group JL8 ?_ ?_
                                · rintro JL8_s ⟨used', _⟩ m8 ⟨s8, hs8, hcv8, hl8, hf8, hi8, ha8,
                                      hl8a, hv8, he8, hht8, hm8⟩
                                  c0_hstraight
                                  exact hJ7 (used', ()) m8 ⟨s8, hs8, hcv8, hl8, hf8, hi8, ha8,
                                    hl8a, hv8, he8, hht8, hm8⟩
                                · intro hCont8 hJ8
                                  c0_hstraight
                                  apply wp_call_of_spec
                                  dsimp only [vals, Arg.val]
                                  refine hSort _ _ _ _ ⟨s4.core.tmp,
                                    array (t := i32) c.pScratchBuf s4.scratch.scratch_buf ⋆
                                      (FullTmpScrRest c s4 ⋆ R),
                                    by rw [htmp_len4]; have := hs4.1.1.cur_vars_le; omega,
                                    htmp31, by rw [← hcv4]; exact hcv31, hm4_f,
                                    fun ok_s tmp' m5 hlen5 hperm5 hpre5 hok5 hm5 => ?_⟩
                                  dsimp only
                                  c0_hsplit
                                  · have hok_true : ok_s = true := by
                                      cases ok_s <;> simp_all
                                    obtain ⟨hvars_lt', hss'⟩ := hok5 hok_true
                                    have hm5' :
                                        (array (t := i32) c.pScratchBuf s4.scratch.scratch_buf ⋆
                                         array (t := i32) c.pTmp tmp' ⋆
                                         (FullTmpScrRest c s4 ⋆ R)) m5 := by
                                      ecancel
                                    have hent5' : (cnfOfClauses F_cur).EntailsClause
                                        (cnfClause ((tmp'.take cnt.toNat).map BitVec.toNat)) :=
                                      entailsClause_perm (hperm5.symm.map BitVec.toNat) hent_tmp
                                    have htmp32 : tmp'.length < 2 ^ 32 := by omega
                                    have hscr4_len :
                                        s4.scratch.scratch_buf.length = c.scratch_cap :=
                                      hs4.1.2.scratch_buf_len
                                    have hscr4_32 : s4.scratch.scratch_buf.length < 2 ^ 32 := by
                                      rw [hscr4_len]; have := c.hscr; have := dimacsBound_val; omega
                                    apply wp_call_of_spec
                                    dsimp only [vals, Arg.val]
                                    refine hHt _ _ _ _ ⟨cnfOfClauses F_cur, s4.core.cur_vars,
                                      s4.scratch.scratch_buf, tmp', FullTmpScrRest c s4 ⋆ R,
                                      by rw [hscr4_len]; exact h7cap, hscr4_32,
                                      by rw [hlen5, htmp_len4]; have := hs4.1.1.cur_vars_le; omega,
                                      htmp32, ⟨hcnt3, hcnt_bd⟩,
                                      by rw [← hcv4, hcv32_eq] at hvars_lt'; exact hvars_lt',
                                      hss', hent5', hht4, hm5',
                                      fun used' scr' m6 hlen6 _ hht6 hm6 => ?_⟩
                                    dsimp only
                                    c0_hstraight
                                    have hm6_ts : (array (t := i32) c.pTmp tmp' ⋆
                                        (array (t := i32) c.pScratchBuf scr' ⋆
                                          (FullTmpScrRest c s4 ⋆ R))) m6 := by ecancel
                                    have hm6_full := unfocus_full_tmp_scr hm6_ts
                                    let s6 : FullState :=
                                      { s4 with
                                        core := { s4.core with tmp := tmp' }
                                        scratch := { s4.scratch with scratch_buf := scr' } }
                                    have hs6 : FullSparseInvW c F0 F_cur s6 :=
                                      fullSparseInvW_upd_scratch_buf
                                        (fullSparseInvW_upd_tmp hs4 hlen5) hlen6
                                    exact hJ8 (used', ()) m6 ⟨s6, hs6, hcv4, hl4, hf4, hi4, ha4,
                                      hl4a, hv4, ⟨he4.1, he4.2⟩, hht6, hm6_full⟩
                                  · c0_hstraight
                                    have hm5_full := unfocus_full_tmp_scr hm5
                                    let s5 : FullState :=
                                      { s4 with core := { s4.core with tmp := tmp' } }
                                    have hs5 : FullSparseInvW c F0 F_cur s5 :=
                                      fullSparseInvW_upd_tmp hs4 hlen5
                                    exact hJ8 (used, ()) m5 ⟨s5, hs5, hcv4, hl4, hf4, hi4, ha4,
                                      hl4a, hv4, ⟨he4.1, he4.2⟩, hht4, hm5_full⟩
                              · c0_hstraight
                                exact hJ7 (used, ()) m4 ⟨s4, hs4, hcv4, hl4, hf4, hi4, ha4,
                                  hl4a, hv4, he4, hht4, hm4⟩
                            · c0_hstraight
                              exact hJ7 (used, ()) m4 ⟨s4, hs4, hcv4, hl4, hf4, hi4, ha4, hl4a, hv4,
                                he4, hht4, hm4⟩
                      · intro _ hJ4
                        clear hAnxt hSort hPm hHt hJdrain hJ2_ih hJ3 hht1 hht0 hr0_mem hm_f
                          hm1_full hs0 hcap hnz h7cap hcap30 hscr_len hscr32 hcv32 h_alen32
                          hr_le hr_bd hr_ref hr3_le hr2_nat hrz_eq
                          hnext_nat hnext_mem hgarb_f hsz_eq
                        let JL5 : Tup Val [i32, i32] → Mem 64 → Prop := fun (cnt, i, ()) m5 =>
                          ∃ s5 : FullState,
                            FullSparseInvW c F0 F_cur s5 ∧
                            s5.core.cur_vars = s.core.cur_vars ∧
                            s5.core.cur_level = 0 ∧
                            s5.core.fuel = s.core.fuel ∧
                            s5.core.inconsistent = s.core.inconsistent ∧
                            s5.core.arena = s.core.arena ∧
                            s5.core.arena_len = s.core.arena_len ∧
                            s5.core.vals = s.core.vals ∧
                            s5.scratch.scratch_buf = s1.scratch.scratch_buf ∧
                            FullExtScratchPres s s5 ∧
                            cnt.toNat ≤ 5 ∧
                            cnt.toNat ≤ s5.core.cur_vars ∧
                            i.toNat ≤ sz_ar.toNat ∧
                            (∀ k < cnt.toNat,
                              (s5.core.tmp[k]?.getD 0#32).toNat < 2 * s5.core.cur_vars) ∧
                            (∀ l ∈ (fullArenaClauseLits s1 r.toNat).take i.toNat,
                              l ∈ (s5.core.tmp.take cnt.toNat).map BitVec.toNat ∨
                              (l < 2 * s5.core.cur_vars ∧ s5.core.vals[l]?.getD 0#8 = 255#8)) ∧
                            (FullMem c s5 ⋆ R) m5
                        refine wp_loop_inv JL5 (fun (_cnt, i, ()) _ => sz_ar.toNat - i.toNat)
                          (fun _ h => by
                            c0_hstraight
                            exact h (0#32, 0#32, ()) m1 ⟨s1, hs1, hcv1, hl1, hfuel1, hinc1, har1,
                              hal1, hvals1, rfl, hext1, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _,
                              fun _ hk => absurd hk (Nat.not_lt_zero _), by simp, hm1⟩) ?_
                        rintro JL5_s ⟨cnt, i, _⟩ m5 ⟨s5, hs5, hcv5, hl5, hf5, hi5, ha5, hl5a, hv5,
                            hscr5, he5, hcnt5, hcnt_cv5, hi_le5, htmp_lt5, hsub5, hm5⟩ hJ5_ih
                        c0_hsplit
                        · have hi_bd : i.toNat < sz_ar.toNat := by dsimp only [sz_ar]; bv_omega
                          have hidx_nat : (r + 3#64 + i.setWidth 64).toNat =
                              r.toNat + 3 + i.toNat := by
                            have := hsz_le_rem; have := hal_bd; have := hi_bd; bv_omega
                          have hidx_lt : (r + 3#64 + i.setWidth 64).toNat <
                              s5.core.arena.length := by
                            rw [hidx_nat]; have := hs5.1.1.arena_len_arr
                            have := hs5.1.1.arena_len_le; omega
                          c0_hstraight
                          let li := s5.core.arena[(r + 3#64 + i.setWidth 64).toNat]
                          have har_eq : s5.core.arena = s1.core.arena := ha5.trans har1.symm
                          have hli_eq_s1 : ∀ h_s1,
                              li = s1.core.arena[r.toNat + 3 + i.toNat]'h_s1 := by
                            intro h_s1
                            have h1 : s5.core.arena[(r + 3#64 + i.setWidth 64).toNat]'hidx_lt =
                                s5.core.arena[r.toNat + 3 + i.toNat]'(by rw [har_eq]; exact h_s1) :=
                              list_getElem_congr hidx_nat _ _
                            dsimp only [li]; rw [h1]; congr 1
                          have hli_mem : li.toNat ∈ fullArenaClauseLits s1 r.toNat := by
                            have hl_eq : li.toNat = (fullArenaClauseLits s1 r.toNat)[i.toNat]'(by
                                rw [hlits_len]; exact hi_bd) := by
                              unfold fullArenaClauseLits fullArenaClauseLitsCore
                              simp only [List.getElem_map, List.getElem_take, List.getElem_drop]
                              exact congrArg BitVec.toNat (hli_eq_s1 _)
                            rw [hl_eq]; exact List.getElem_mem _
                          have hli_lt : li.toNat < 2 * s5.core.cur_vars := by
                            rw [hcv5, ← hcv1]; exact hlits_lt li.toNat hli_mem
                          have hli_vals_lt : (li.setWidth 64).toNat < s5.core.vals.length := by
                            rw [bv_zext32_toNat, hs5.1.1.vals_len]
                            have := hs5.1.1.cur_vars_le; omega
                          c0_hsplit
                          · exfalso
                            have hge2 : 2 * s5.core.cur_vars ≤ li.toNat := by
                              have h1 : 2 * s.core.cur_vars ≤
                                  (s5.core.arena[(r.toNat + BitVec.toNat (3 : BitVec 64) +
                                    i.toNat) % 2 ^ 64]'(by
                                    rw [show BitVec.toNat (3 : BitVec 64) = 3 from rfl,
                                      Nat.mod_eq_of_lt (by omega), ← hidx_nat]
                                    exact hidx_lt)).toNat := by
                                have := hs5.1.1.cur_vars_le; have := c.hmaxv
                                have := dimacsBound_val; rw [← hcv5] at *; bv_omega
                              have hli_mod : (r.toNat + BitVec.toNat (3 : BitVec 64) +
                                  i.toNat) % 2 ^ 64 = (r + 3#64 + i.setWidth 64).toNat := by
                                rw [show BitVec.toNat (3 : BitVec 64) = 3 from rfl, hidx_nat,
                                  Nat.mod_eq_of_lt (by omega)]
                              rw [hcv5]
                              dsimp only [li]
                              rw [← list_getElem_congr hli_mod]
                              exact h1
                            omega
                          · clear hc
                            c0_hstraight
                            let bval := s5.core.vals[(li.setWidth 64).toNat]
                            have hdom := hs5.2.1.vals_domain li.toNat hli_lt
                            have hb_eq : s5.core.vals[li.toNat]?.getD 0#8 = bval := by
                              dsimp only [bval]
                              rw [List.getElem?_eq_getElem (by
                                rw [← bv_zext32_toNat li]; exact hli_vals_lt), Option.getD_some]
                              exact list_getElem_congr (bv_zext32_toNat li).symm _ _
                            rw [hb_eq] at hdom
                            have hli_mod_eq :
                                (r.toNat + BitVec.toNat (3 : BitVec 64) + i.toNat) % 2 ^ 64 =
                                (r + 3#64 + i.setWidth 64).toNat := by
                              rw [show BitVec.toNat (3 : BitVec 64) = 3 from rfl, hidx_nat,
                                Nat.mod_eq_of_lt (by omega)]
                            have hb_c0_val : ∀ h1 h2,
                                s5.core.vals[(s5.core.arena[(r.toNat +
                                  BitVec.toNat (3 : BitVec 64) + i.toNat) % 2 ^ 64]'h1).toNat]'h2 =
                                bval := by
                              intro h1 h2; dsimp only [bval, li]; congr 1
                              rw [bv_zext32_toNat]; congr 1; apply list_getElem_congr hli_mod_eq
                            have htake_step : ∀ l,
                                l ∈ (fullArenaClauseLits s1 r.toNat).take (i.toNat + 1) →
                                l ∈ (fullArenaClauseLits s1 r.toNat).take i.toNat ∨
                                  l = li.toNat := by
                              intro l hl_mem
                              have htk := list_take_succ_of_lt (by rw [hlits_len]; exact hi_bd :
                                i.toNat < (fullArenaClauseLits s1 r.toNat).length)
                              rw [htk, List.mem_append, List.mem_singleton] at hl_mem
                              rcases hl_mem with h1 | h2
                              · exact Or.inl h1
                              · right
                                rw [h2]
                                unfold fullArenaClauseLits fullArenaClauseLitsCore
                                simp only [List.getElem_map, List.getElem_take, List.getElem_drop]
                                exact (congrArg BitVec.toNat (hli_eq_s1 _)).symm
                            let JL6 : Tup Val [i32] → Mem 64 → Prop := fun (cnt', ()) m6 =>
                              ∃ s6 : FullState,
                                FullSparseInvW c F0 F_cur s6 ∧
                                s6.core.cur_vars = s.core.cur_vars ∧
                                s6.core.cur_level = 0 ∧
                                s6.core.fuel = s.core.fuel ∧
                                s6.core.inconsistent = s.core.inconsistent ∧
                                s6.core.arena = s.core.arena ∧
                                s6.core.arena_len = s.core.arena_len ∧
                                s6.core.vals = s.core.vals ∧
                                s6.scratch.scratch_buf = s1.scratch.scratch_buf ∧
                                FullExtScratchPres s s6 ∧
                                cnt'.toNat ≤ 5 ∧
                                cnt'.toNat ≤ s6.core.cur_vars ∧
                                (∀ k < cnt'.toNat,
                                  (s6.core.tmp[k]?.getD 0#32).toNat < 2 * s6.core.cur_vars) ∧
                                (∀ l ∈ (fullArenaClauseLits s1 r.toNat).take (i.toNat + 1),
                                  l ∈ (s6.core.tmp.take cnt'.toNat).map BitVec.toNat ∨
                                  (l < 2 * s6.core.cur_vars ∧
                                    s6.core.vals[l]?.getD 0#8 = 255#8)) ∧
                                (FullMem c s6 ⋆ R) m6
                            c0_hsplit
                            · c0_hstraight
                              exact hJ4 (cnt, true, i, ()) m5 ⟨s5, hs5, hcv5, hl5, hf5, hi5,
                                ha5, hl5a, hv5, hscr5, he5,
                                fun hb1 => absurd hb1 (by decide), hm5⟩
                            · have hnot1 : bval ≠ 1#8 := by
                                intro hb1
                                apply hc
                                rw [hb_c0_val _ _, hb1]
                                decide
                              clear hc
                              refine wp_join_group JL6 ?_ ?_
                              · rintro JL6_s ⟨cnt', _⟩ m6 ⟨s6, hs6, hcv6, hl6, hf6, hi6, ha6,
                                    hl6a, hv6, hscr6, he6, hcnt6, hcnt_cv6, htmp_lt6, hsub6,
                                    hm6⟩
                                c0_hstraight
                                have hi_succ : (i + 1#32).toNat = i.toNat + 1 := by bv_omega
                                refine hJ5_ih (cnt', i + 1#32, ()) m6
                                  (by dsimp only; rw [hi_succ]; omega)
                                  ⟨s6, hs6, hcv6, hl6, hf6, hi6, ha6, hl6a, hv6, hscr6, he6,
                                    hcnt6, hcnt_cv6, by rw [hi_succ]; omega, htmp_lt6,
                                    by rw [hi_succ]; exact hsub6, hm6⟩
                              · intro J6 hJ6
                                c0_hsplit
                                · clear hc
                                  c0_hsplit
                                  · c0_hsplit
                                    · have hcnt_lt5 : cnt.toNat < 5 := by bv_omega
                                      have hcnt_lt_cv : cnt.toNat < s5.core.cur_vars := by
                                        rw [hcv5]; bv_omega
                                      have hcnt_lt_tmp : cnt.toNat < s5.core.tmp.length := by
                                        rw [hs5.1.1.tmp_len_arr]
                                        have := hs5.1.1.cur_vars_le; omega
                                      have hcnt_z_eq : (cnt.setWidth 64).toNat = cnt.toNat :=
                                        bv_zext32_toNat cnt
                                      c0_hstraight
                                      rw [hcnt_z_eq] at hm
                                      let tmp_new := s5.core.tmp.set cnt.toNat li
                                      let s5' : FullState :=
                                        { s5 with core := { s5.core with tmp := tmp_new } }
                                      have hs5' : FullSparseInvW c F0 F_cur s5' :=
                                        fullSparseInvW_upd_tmp hs5 (by simp [tmp_new])
                                      have hcnt_s : (cnt + 1#32).toNat = cnt.toNat + 1 := by
                                        bv_omega
                                      obtain ⟨hlt5', hsub5'⟩ := collect_arena_tmp_step
                                        hcnt_lt_tmp hli_lt htmp_lt5 hsub5 htake_step
                                      exact hJ6 (cnt + 1#32, ()) _
                                        ⟨s5', hs5', hcv5, hl5, hf5, hi5, ha5, hl5a, hv5, hscr5,
                                          he5, by rw [hcnt_s]; omega,
                                          by rw [hcnt_s]; dsimp only [s5']; omega,
                                          by rw [hcnt_s]; exact hlt5',
                                          by rw [hcnt_s]; exact hsub5', hm⟩
                                    · c0_hstraight
                                      exact hJ4 (6#32, false, i, ()) m5 ⟨s5, hs5, hcv5, hl5, hf5,
                                        hi5, ha5, hl5a, hv5, hscr5, he5,
                                        fun _ h6 => absurd h6 (by decide), hm5⟩
                                  · c0_hstraight
                                    exact hJ4 (6#32, false, i, ()) m5 ⟨s5, hs5, hcv5, hl5, hf5,
                                      hi5, ha5, hl5a, hv5, hscr5, he5,
                                      fun _ h6 => absurd h6 (by decide), hm5⟩
                                · have hnot0 : bval ≠ 0#8 := by
                                    intro hb0
                                    apply hc
                                    rw [hb_c0_val _ _, hb0]
                                    decide
                                  have hv255 : bval = 255#8 := by
                                    rcases hdom with h0 | h1 | h255
                                    · exact absurd h0 hnot0
                                    · exact absurd h1 hnot1
                                    · exact h255
                                  c0_hstraight
                                  refine hJ6 (cnt, ()) m5 ⟨s5, hs5, hcv5, hl5, hf5, hi5, ha5,
                                    hl5a, hv5, hscr5, he5, hcnt5, hcnt_cv5, htmp_lt5,
                                    fun l hl_m => ?_, hm5⟩
                                  rcases htake_step l hl_m with h_old | rfl
                                  · exact hsub5 l h_old
                                  · right; exact ⟨hli_lt, by simpa [hb_eq] using hv255⟩
                        · have hi_eq : i.toNat = sz_ar.toNat := by
                            have hr2_mod : (r.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64 =
                                (r + 2#64).toNat := by
                              have := hal_bd; have := hsz_le_rem; bv_omega
                            have hsz_c0 :
                                s1.core.arena[(r.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64]'(by
                                  rw [hr2_mod]; exact hr2_lt_ar) = sz_ar :=
                              list_getElem_congr hr2_mod _ _
                            rw [hsz_c0] at hc; omega
                          c0_hstraight
                          refine hJ4 (cnt, false, i, ()) m5 ⟨s5, hs5, hcv5, hl5, hf5, hi5, ha5,
                            hl5a, hv5, hscr5, he5, fun _ _ => ?_, hm5⟩
                          refine ⟨hcnt_cv5, htmp_lt5, ?_⟩
                          apply fullWitnessInv_vals_falsified_entails hs5.2.1 hl5 hent_r
                          intro l hl_m
                          have hmem' := hsub5 l (by
                            rw [hi_eq, List.take_of_length_le
                              (by rw [hlits_len]; exact Nat.le_refl _)]
                            exact hl_m)
                          rcases hmem' with hin | ⟨hl_lt5, hv_eq5⟩
                          · exact Or.inl hin
                          · exact Or.inr ⟨hl_lt5, hv_eq5⟩
                    · c0_hstraight
                      exact hJ3 (used, ()) m1 ⟨s1, hs1, hcv1, hl1, hfuel1, hinc1, har1,
                        hal1, hvals1, hext1, hht1, hm1⟩
                  · c0_hstraight
                    exact hJ3 (used, ()) m1 ⟨s1, hs1, hcv1, hl1, hfuel1, hinc1, har1,
                      hal1, hvals1, hext1, hht1, hm1⟩
                · c0_hstraight
                  exact hJ3 (used, ()) m1 ⟨s1, hs1, hcv1, hl1, hfuel1, hinc1, har1,
                    hal1, hvals1, hext1, hht1, hm1⟩
              · c0_hstraight
                exact hJ3 (used, ()) m1 ⟨s1, hs1, hcv1, hl1, hfuel1, hinc1, har1,
                  hal1, hvals1, hext1, hht1, hm1⟩
        · c0_hstraight
          exact hJdrain (r, used, ()) m1 ⟨s1, hs1, hcv1, hl1, hfuel1, hinc1, hext1, hht1, hm1⟩

/-! ## 2. Binary XOR Pair Collection (`full_xor_collect_bins`) -/

@[expose] def fullXorCollectBinsSpec : Spec [i64, i64] [i64] := fun (h, eq_end, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧
    FullSparseInvW c F0 F_cur s ∧
    eq_end.toNat ≤ c.scratch_cap ∧
    XorEqPoolOk (cnfOfClauses F_cur) s.core.cur_vars s.scratch.scratch_buf eq_end.toNat 0 ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (eq_end' : BitVec 64) (scr' : List (BitVec 32)) (m' : Mem 64),
      let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
      scr'.length = s.scratch.scratch_buf.length →
      eq_end'.toNat ≤ c.scratch_cap →
      XorEqPoolOk (cnfOfClauses F_cur) s.core.cur_vars scr' eq_end'.toNat 0 →
      (FullMem c s' ⋆ R) m' → Q (eq_end', ()) m'

private theorem bv32_xor1_toNat (x : BitVec 32) : (x ^^^ 1#32).toNat = litNeg x.toNat := by
  rw [BitVec.toNat_xor]; rfl

private theorem collect_bins_pack_hdr (ot : BitVec 32) :
    let rhs_bit := (ot &&& 1#32) ^^^ 1#32
    let hdr := (2#32 ||| (2#32 <<< (16#32 &&& 31#32))) ||| (rhs_bit <<< (31#32 &&& 31#32))
    ((hdr >>> 16#32) &&& 0x7FFF#32).toNat = 2 ∧
    (hdr &&& 0xFFFF#32).toNat = 2 ∧
    ((hdr >>> 31#32) != 0#32) = (ot.toNat % 2 == 0) := by
  have hm := bv32_and_one_toNat ot
  have hmod : ot.toNat % 2 = 0 ∨ ot.toNat % 2 = 1 := by omega
  rcases hmod with h0 | h1
  · have ha : ot &&& 1#32 = 0#32 := BitVec.eq_of_toNat_eq (by rw [hm, h0]; rfl)
    dsimp only; rw [ha, h0]; decide
  · have ha : ot &&& 1#32 = 1#32 := BitVec.eq_of_toNat_eq (by rw [hm, h1]; rfl)
    dsimp only; rw [ha, h1]; decide

private theorem collect_bins_append_ok {F : CNF Nat} {cv : Nat} {scr : List (BitVec 32)}
    {eq_end v ov : BitVec 64} {lit ot : BitVec 32}
    (hpool : XorEqPoolOk F cv scr eq_end.toNat 0)
    (heq_bd : eq_end.toNat + 3 ≤ scr.length)
    (hscr32 : scr.length < 2 ^ 32)
    (hv_lt : v.toNat < ov.toNat) (hov_lt : ov.toNat < cv) (hcv32 : cv < 2 ^ 31)
    (hlit : lit.toNat = 2 * v.toNat) (hov : ov.toNat = ot.toNat / 2)
    (h1 : F.EntailsClause (cnfClause [lit.toNat, ot.toNat]))
    (h2 : F.EntailsClause (cnfClause [(lit ^^^ 1#32).toNat, (ot ^^^ 1#32).toNat])) :
    let rhs_bit := (ot &&& 1#32) ^^^ 1#32
    let hdr := (2#32 ||| (2#32 <<< (16#32 &&& 31#32))) ||| (rhs_bit <<< (31#32 &&& 31#32))
    let scr' := ((scr.set eq_end.toNat hdr).set (eq_end + 1#64).toNat (v.setWidth 32)).set
      (eq_end + 2#64).toNat (ov.setWidth 32)
    scr'.length = scr.length ∧
    XorEqPoolOk F cv scr' (eq_end.toNat + 3) 0 := by
  intro rhs_bit hdr scr'
  have hw1 : (eq_end + 1#64).toNat = eq_end.toNat + 1 := by bv_omega
  have hw2 : (eq_end + 2#64).toNat = eq_end.toNat + 2 := by bv_omega
  have hlen : scr'.length = scr.length := by simp [scr']
  have hpre : ∀ i, 0 ≤ i → i < eq_end.toNat → scr'[i]? = scr[i]? := by
    intro i _ hi
    simp only [scr', hw1, hw2,
      List.getElem?_set_ne (by omega : eq_end.toNat + 2 ≠ i),
      List.getElem?_set_ne (by omega : eq_end.toNat + 1 ≠ i),
      List.getElem?_set_ne (by omega : eq_end.toNat ≠ i)]
  have hhdr : scr'[eq_end.toNat]? = some hdr := by
    simp only [scr', hw1, hw2,
      List.getElem?_set_ne (by omega : eq_end.toNat + 2 ≠ eq_end.toNat),
      List.getElem?_set_ne (by omega : eq_end.toNat + 1 ≠ eq_end.toNat)]
    exact List.getElem?_set_self (by omega)
  have hv_w : scr'[eq_end.toNat + 1]? = some (v.setWidth 32) := by
    simp only [scr', hw1, hw2,
      List.getElem?_set_ne (by omega : eq_end.toNat + 2 ≠ eq_end.toNat + 1)]
    exact List.getElem?_set_self (by simp; omega)
  have hov_w : scr'[eq_end.toNat + 2]? = some (ov.setWidth 32) := by
    simp only [scr', hw2]
    exact List.getElem?_set_self (by simp; omega)
  have hvs_eq :
      (List.range 2).map (fun i => (scr'[eq_end.toNat + 1 + i]?.getD 0#32).toNat) =
        [v.toNat, ov.toNat] := by
    simp only [List.range_succ, List.range_zero, List.map_nil, List.map_cons,
      List.nil_append, List.cons_append, Nat.add_zero]
    rw [hv_w, hov_w]
    simp only [Option.getD_some, bv64_toNat_setWidth32_lt (by omega : v.toNat < 2 ^ 32),
      bv64_toNat_setWidth32_lt (by omega : ov.toNat < 2 ^ 32)]
  obtain ⟨hst, hcl, hrhs⟩ := collect_bins_pack_hdr ot
  have hbin := xorVarsSound_of_binPair h1 (by
    rw [bv32_xor1_toNat, bv32_xor1_toNat] at h2; exact h2)
  have hlit_var : litVar lit.toNat = v.toNat := by unfold litVar; rw [hlit]; omega
  have hot_var : litVar ot.toNat = ov.toNat := by unfold litVar; exact hov.symm
  have hlit_sign : litSign lit.toNat = false := by unfold litSign; rw [hlit]; simp
  have hbeq_sign : (litSign lit.toNat == litSign ot.toNat) = (ot.toNat % 2 == 0) := by
    rw [hlit_sign]; unfold litSign
    rcases (by omega : ot.toNat % 2 = 0 ∨ ot.toNat % 2 = 1) with h0 | h1
    · simp [h0]
    · simp [h1]
  rw [hlit_var, hot_var, hbeq_sign] at hbin
  have hpool1 := xorEqPoolOk_congr hpool hpre
  refine ⟨hlen, xorEqPoolOk_append hpool1 (by omega) hhdr hst hcl (by omega) ?_ ?_ ?_⟩
  · rw [hvs_eq]; exact List.pairwise_cons.mpr ⟨fun x hx => by
      simp at hx; subst hx; exact hv_lt, List.pairwise_singleton _ _⟩
  · rw [hvs_eq]; intro x hx; simp at hx; rcases hx with rfl | rfl <;> omega
  · rw [hvs_eq, hrhs]; exact hbin

theorem full_xor_collect_bins_wp (Γ : Env) :
    (∀ a m Q X, fullHasBinSpec a m Q X →
      Γ "full_has_bin" [i64, i32, i32] [.bool] a m Q X) →
    ∀ a m Q X, fullXorCollectBinsSpec a m Q X →
      Func.wp Γ full_xor_collect_bins_body a m Q X := by
  intro hHasBin (h, eq0, ()) m0 Q X ⟨c, F0, F_cur, s, R, hc_eq, hs, heq0_le, hpool0, hm0, hQ⟩
  subst hc_eq
  unfold full_xor_collect_bins_body Func.wp; dsimp only
  have hscr_len : s.scratch.scratch_buf.length = c.scratch_cap := hs.1.2.scratch_buf_len
  have hscr32 : c.scratch_cap < 2 ^ 32 := by have := c.hscr; have := dimacsBound_val; omega
  have hcv31 : s.core.cur_vars < 2 ^ 31 := by
    have := hs.1.1.cur_vars_le; have := c.hmaxv; have := dimacsBound_val; omega
  have hwlen32 : s.core.wlen < 2 ^ 32 := by
    have := hs.1.1.wlen_le; have := c.hwcap; have := dimacsBound_val; omega
  have hwatches : WatchesInv F_cur s.core := by
    have hm := hs.2.1.watches
    unfold ModeWatchesInv at hm
    simp only [hs.2.2.2.2.2, ↓reduceIte] at hm
    exact hm
  c0_hstraight
  let Jv : Tup Val [i64, i64] → Mem 64 → Prop := fun (eq_c, v, ()) m1 =>
    ∃ scr1 : List (BitVec 32),
      v.toNat ≤ s.core.cur_vars ∧
      eq_c.toNat ≤ c.scratch_cap ∧
      scr1.length = c.scratch_cap ∧
      XorEqPoolOk (cnfOfClauses F_cur) s.core.cur_vars scr1 eq_c.toNat 0 ∧
      (FullMem c { s with scratch := { s.scratch with scratch_buf := scr1 } } ⋆ R) m1
  refine wp_loop_inv Jv (fun (_eq, v, ()) _ => s.core.cur_vars - v.toNat)
    (fun _ h => by
      c0_hstraight
      exact h (eq0, 0#64, ()) m0 ⟨s.scratch.scratch_buf, Nat.zero_le _, heq0_le,
        hscr_len, hpool0, hm0⟩) ?_
  rintro Jv_s ⟨eq_c, v, _⟩ m1 ⟨scr1, hv_le, heq1_le, hlen1, hpool1, hm1⟩ hJv_ih
  c0_hsplit
  · have hv_lt : v.toNat < s.core.cur_vars := by bv_omega
    have hlit_nat : ((v <<< 1#64).setWidth 32).toNat = 2 * v.toNat := by
      change ((v <<< (1 : Nat)).setWidth 32).toNat = 2 * v.toNat; bv_omega
    let lit32 : BitVec 32 := (v <<< 1#64).setWidth 32
    have hlit_lt_vals : (lit32.setWidth 64).toNat < s.core.vals.length := by
      rw [bv_zext32_toNat, hlit_nat, hs.1.1.vals_len]; have := hs.1.1.cur_vars_le; omega
    let Jv_next : Tup Val [i64] → Mem 64 → Prop := fun (eq_n, ()) m2 =>
      ∃ scr2 : List (BitVec 32),
        eq_n.toNat ≤ c.scratch_cap ∧ scr2.length = c.scratch_cap ∧
        XorEqPoolOk (cnfOfClauses F_cur) s.core.cur_vars scr2 eq_n.toNat 0 ∧
        (FullMem c { s with scratch := { s.scratch with scratch_buf := scr2 } } ⋆ R) m2
    c0_hstraight
    refine wp_join_group Jv_next ?_ ?_
    · rintro _ ⟨eq_n, _⟩ m2 ⟨scr2, heq2_le, hlen2, hpool2, hm2⟩
      c0_hstraight
      exact hJv_ih (eq_n, v + 1#64, ()) m2 (by dsimp only; bv_omega)
        ⟨scr2, by bv_omega, heq2_le, hlen2, hpool2, hm2⟩
    · intro _ hJv_next
      c0_hsplit
      · have hlit64 : (lit32.setWidth 64).toNat = lit32.toNat := bv_zext32_toNat lit32
        have h2lit0 : (2#64 * lit32.setWidth 64).toNat = 2 * lit32.toNat := by
          have := hlit_nat; bv_omega
        have h2lit1 : (2#64 * lit32.setWidth 64 + 1#64).toNat = 2 * lit32.toNat + 1 := by
          have := hlit_nat; bv_omega
        have hwv0_lt : (2#64 * lit32.setWidth 64).toNat < s.core.wvec.length := by
          rw [h2lit0, hlit_nat, hs.1.1.wvec_len]; have := hs.1.1.cur_vars_le; omega
        have hwv1_lt : (2#64 * lit32.setWidth 64 + 1#64).toNat < s.core.wvec.length := by
          rw [h2lit1, hlit_nat, hs.1.1.wvec_len]; have := hs.1.1.cur_vars_le; omega
        c0_hstraight
        have hwv0_eq' : (2 * BitVec.setWidth 64 (BitVec.setWidth 32 (v <<< OfNat.ofNat 1))).toNat =
            2 * lit32.toNat := h2lit0
        have hwv1_eq' :
            (2 * BitVec.setWidth 64 (BitVec.setWidth 32 (v <<< OfNat.ofNat 1)) + 1).toNat =
            2 * lit32.toNat + 1 := h2lit1
        let w_off : BitVec 64 :=
          (s.core.wvec[(2 * BitVec.setWidth 64 (BitVec.setWidth 32 (v <<< OfNat.ofNat 1))).toNat]'
            hwv0_lt).setWidth 64
        let w_sz : BitVec 64 :=
          (s.core.wvec[(2 * BitVec.setWidth 64
            (BitVec.setWidth 32 (v <<< OfNat.ofNat 1)) + 1).toNat]'hwv1_lt).setWidth 64
        have hwoff_eq : w_off.toNat = fullWatchOffCore s.core lit32.toNat := by
          dsimp only [w_off, fullWatchOffCore]
          rw [bv_zext32_toNat, List.getElem?_eq_getElem (by rw [← h2lit0]; exact hwv0_lt),
            Option.getD_some]
          exact congrArg BitVec.toNat (list_getElem_congr hwv0_eq' _ _)
        have hwsz_eq : w_sz.toNat = fullWatchSizeCore s.core lit32.toNat := by
          dsimp only [w_sz, fullWatchSizeCore]
          rw [bv_zext32_toNat, List.getElem?_eq_getElem (by rw [← h2lit1]; exact hwv1_lt),
            Option.getD_some]
          exact congrArg BitVec.toNat (list_getElem_congr hwv1_eq' _ _)
        have hwoff_c0_idx :
            2 % 2 ^ 64 * (v.toNat * 2 ^ OfNat.ofNat 1 % 2 ^ 64 % 2 ^ 32) % 2 ^ 64 =
            (2 * BitVec.setWidth 64 (BitVec.setWidth 32 (v <<< OfNat.ofNat 1))).toNat := by
          rw [hwv0_eq', hlit_nat]
          change 2 % 2 ^ 64 * (v.toNat * 2 % 2 ^ 64 % 2 ^ 32) % 2 ^ 64 = 2 * (2 * v.toNat)
          omega
        have hwoff_c0 :
            (s.core.wvec[2 % 2 ^ 64 *
              (v.toNat * 2 ^ OfNat.ofNat 1 % 2 ^ 64 % 2 ^ 32) % 2 ^ 64]'(by
              rw [hwoff_c0_idx]; exact hwv0_lt)).toNat = w_off.toNat := by
          dsimp only [w_off]; rw [bv_zext32_toNat]
          exact congrArg BitVec.toNat (list_getElem_congr hwoff_c0_idx _ _)
        have hwsz_c0_idx :
            (2 % 2 ^ 64 * (v.toNat * 2 ^ OfNat.ofNat 1 % 2 ^ 64 % 2 ^ 32) + 1) % 2 ^ 64 =
            (2 * BitVec.setWidth 64 (BitVec.setWidth 32 (v <<< OfNat.ofNat 1)) + 1).toNat := by
          rw [hwv1_eq', hlit_nat]
          change (2 % 2 ^ 64 * (v.toNat * 2 % 2 ^ 64 % 2 ^ 32) + 1) % 2 ^ 64 =
            2 * (2 * v.toNat) + 1
          omega
        have hwsz_c0 :
            (s.core.wvec[(2 % 2 ^ 64 *
              (v.toNat * 2 ^ OfNat.ofNat 1 % 2 ^ 64 % 2 ^ 32) + 1) % 2 ^ 64]'(by
              rw [hwsz_c0_idx]; exact hwv1_lt)).toNat = w_sz.toNat := by
          dsimp only [w_sz]; rw [bv_zext32_toNat]
          exact congrArg BitVec.toNat (list_getElem_congr hwsz_c0_idx _ _)
        have hslice0 : WatchSliceOk F_cur s.core lit32.toNat w_off.toNat w_sz.toNat := by
          rw [hwoff_eq, hwsz_eq]
          exact hwatches.slices lit32.toNat (by rw [hlit_nat]; omega)
        have hwb0 : w_off.toNat + w_sz.toNat ≤ s.core.wlen := by
          rw [hwoff_eq, hwsz_eq]
          exact hwatches.layout.bounds lit32.toNat (by rw [hlit_nat]; omega)
        let Jwi_exit : Tup Val [i64] → Mem 64 → Prop := fun (eq_e, ()) m2 =>
          ∃ scr2 : List (BitVec 32),
            eq_e.toNat ≤ c.scratch_cap ∧ scr2.length = c.scratch_cap ∧
            XorEqPoolOk (cnfOfClauses F_cur) s.core.cur_vars scr2 eq_e.toNat 0 ∧
            (FullMem c { s with scratch := { s.scratch with scratch_buf := scr2 } } ⋆ R) m2
        refine wp_join_group Jwi_exit ?_ ?_
        · rintro _ ⟨eq_e, _⟩ m2 ⟨scr2, heq2_le, hlen2, hpool2, hm2⟩
          exact hJv_next (eq_e, ()) m2 ⟨scr2, heq2_le, hlen2, hpool2, hm2⟩
        · intro _ hJwi_exit
          c0_hsplit
          · let Jwi_brk : Tup Val [i64, i64] → Mem 64 → Prop := fun (eq_e, _wi, ()) m2 =>
              ∃ scr2 : List (BitVec 32),
                eq_e.toNat ≤ c.scratch_cap ∧ scr2.length = c.scratch_cap ∧
                XorEqPoolOk (cnfOfClauses F_cur) s.core.cur_vars scr2 eq_e.toNat 0 ∧
                (FullMem c { s with scratch := { s.scratch with scratch_buf := scr2 } } ⋆ R) m2
            refine wp_join_group Jwi_brk ?_ ?_
            · rintro _ ⟨eq_e, _wi, _⟩ m2 ⟨scr2, heq2_le, hlen2, hpool2, hm2⟩
              exact hJwi_exit (eq_e, ()) m2 ⟨scr2, heq2_le, hlen2, hpool2, hm2⟩
            · intro _ hJwi_brk
              let Jwi : Tup Val [i64, i64] → Mem 64 → Prop := fun (eq_w, wi, ()) m2 =>
                ∃ scr2 : List (BitVec 32),
                  wi.toNat ≤ w_sz.toNat ∧
                  eq_w.toNat ≤ c.scratch_cap ∧ scr2.length = c.scratch_cap ∧
                  WatchSliceOk F_cur s.core lit32.toNat (w_off.toNat + wi.toNat)
                    (w_sz.toNat - wi.toNat) ∧
                  XorEqPoolOk (cnfOfClauses F_cur) s.core.cur_vars scr2 eq_w.toNat 0 ∧
                  (FullMem c { s with scratch := { s.scratch with scratch_buf := scr2 } } ⋆ R) m2
              refine wp_loop_inv Jwi (fun (_eq, wi, ()) _ => w_sz.toNat - wi.toNat)
                (fun _ h => by
                  c0_hstraight
                  exact h (eq_c, 0#64, ()) m1 ⟨scr1, Nat.zero_le _, heq1_le, hlen1,
                    by simpa using hslice0, hpool1, hm1⟩) ?_
              rintro _ ⟨eq_w, wi, _⟩ m2
                ⟨scr2, hwi_le, heqw_le, hlen2, hslice, hpool2, hm2⟩ hJwi_ih
              c0_hsplit
              · have hwi_lt : wi.toNat < w_sz.toNat := by
                  rw [← hwsz_c0]; bv_omega
                have hidx_nat : (w_off + wi).toNat = w_off.toNat + wi.toNat := by bv_omega
                have hidx_lt : (w_off + wi).toNat < s.core.wstk.length := by
                  rw [hidx_nat, hs.1.1.wstk_len_arr]; have := hs.1.1.wlen_le; omega
                dsimp only
                c0_hstraight
                let entry := s.core.wstk[(w_off + wi).toNat]'hidx_lt
                have hentry_c0_idx :
                    ((s.core.wvec[2 % 2 ^ 64 *
                      (v.toNat * 2 ^ OfNat.ofNat 1 % 2 ^ 64 % 2 ^ 32) % 2 ^ 64]'(by
                      rw [hwoff_c0_idx]; exact hwv0_lt)).toNat + wi.toNat) % 2 ^ 64 =
                    (w_off + wi).toNat := by
                  rw [hwoff_c0, hidx_nat]; omega
                have hentry_c0 :
                    s.core.wstk[((s.core.wvec[2 % 2 ^ 64 *
                      (v.toNat * 2 ^ OfNat.ofNat 1 % 2 ^ 64 % 2 ^ 32) % 2 ^ 64]'(by
                      rw [hwoff_c0_idx]; exact hwv0_lt)).toNat + wi.toNat) % 2 ^ 64]'(by
                      rw [hentry_c0_idx]; exact hidx_lt) = entry :=
                  list_getElem_congr hentry_c0_idx _ _
                have hentry_opt : s.core.wstk[w_off.toNat + wi.toNat]? = some entry := by
                  dsimp only [entry]
                  rw [List.getElem?_eq_getElem (by rw [← hidx_nat]; exact hidx_lt)]
                  exact congrArg some (list_getElem_congr hidx_nat _ _).symm
                let Jwi_step : Tup Val [i64, i64] → Mem 64 → Prop := fun (eq_s, wi_s, ()) m3 =>
                  ∃ scr3 : List (BitVec 32),
                    wi.toNat < wi_s.toNat ∧ wi_s.toNat ≤ w_sz.toNat ∧
                    eq_s.toNat ≤ c.scratch_cap ∧ scr3.length = c.scratch_cap ∧
                    WatchSliceOk F_cur s.core lit32.toNat (w_off.toNat + wi_s.toNat)
                      (w_sz.toNat - wi_s.toNat) ∧
                    XorEqPoolOk (cnfOfClauses F_cur) s.core.cur_vars scr3 eq_s.toNat 0 ∧
                    (FullMem c { s with scratch := { s.scratch with scratch_buf := scr3 } } ⋆
                      R) m3
                refine wp_join_group Jwi_step ?_ ?_
                · rintro _ ⟨eq_s, wi_s, _⟩ m3
                    ⟨scr3, hinc, hle_s, heqs_le, hlen3, hslice3, hpool3, hm3⟩
                  exact hJwi_ih (eq_s, wi_s, ()) m3 (by dsimp only; omega)
                    ⟨scr3, hle_s, heqs_le, hlen3, hslice3, hpool3, hm3⟩
                · intro _ hJwi_step
                  generalize hrem : w_sz.toNat - wi.toNat = rem at hslice
                  cases hslice with
                  | empty => omega
                  | @bin _ rem' w0 hw0_eq hmsb hne_ff hot_lt hent_bin hrest =>
                    have hw0_is : entry = w0 := by
                      rw [hentry_opt] at hw0_eq; exact Option.some.inj hw0_eq
                    c0_hsplit
                    · let Jbin : Tup Val [i64] → Mem 64 → Prop := fun (eq_b, ()) m3 =>
                        ∃ scr3 : List (BitVec 32),
                          eq_b.toNat ≤ c.scratch_cap ∧ scr3.length = c.scratch_cap ∧
                          XorEqPoolOk (cnfOfClauses F_cur) s.core.cur_vars scr3 eq_b.toNat 0 ∧
                          (FullMem c { s with scratch := { s.scratch with scratch_buf := scr3 } } ⋆
                            R) m3
                      refine wp_join_group Jbin ?_ ?_
                      · rintro _ ⟨eq_b, _⟩ m3 ⟨scr3, heqb_le, hlen3, hpool3, hm3⟩
                        c0_hstraight
                        have hwi1_nat : (wi + 1#64).toNat = wi.toNat + 1 := by bv_omega
                        refine hJwi_step (eq_b, wi + 1#64, ()) m3
                          ⟨scr3, by omega, by omega, heqb_le, hlen3, ?_, hpool3, hm3⟩
                        have hp1 : w_off.toNat + (wi + 1#64).toNat = w_off.toNat + wi.toNat + 1 :=
                          by omega
                        have hr1 : w_sz.toNat - (wi + 1#64).toNat = rem' := by omega
                        rw [hp1, hr1]; exact hrest
                      · intro _ hJbin
                        c0_hsplit
                        · c0_hstraight
                          refine wp_join_group Jbin (fun _ xs m h => hJbin xs m h) ?_
                          intro _ hJbin1
                          let ot : BitVec 32 := entry &&& 0x7FFFFFFF#32
                          let ov : BitVec 64 := (ot >>> 1#32).setWidth 64
                          have hot_eq : ot = w0 &&& 0x7FFFFFFF#32 := by simp [ot, hw0_is]
                          have hot_lt_cv : ot.toNat < 2 * s.core.cur_vars := by
                            rw [hot_eq]; exact hot_lt
                          have hov_nat : ov.toNat = ot.toNat / 2 := by
                            dsimp only [ov]; rw [bv_zext32_toNat]; exact bv32_shr1_nat ot
                          c0_hsplit
                          · have hv_lt_ov : v.toNat < ov.toNat := by
                              have h1 : (2 ^ OfNat.ofNat 1 : Nat) = 2 := rfl
                              have h2 : ov.toNat =
                                  (entry.toNat &&& 2147483647 % 2 ^ 32) / 2 ^ OfNat.ofNat 1 := by
                                rw [hov_nat, h1]; dsimp only [ot]; rw [BitVec.toNat_and]; rfl
                              rw [h2, ← hentry_c0]; bv_omega
                            c0_hsplit
                            · have hov_lt_cv : ov.toNat < s.core.cur_vars := by bv_omega
                              have hot_vals_lt : (ot.setWidth 64).toNat < s.core.vals.length := by
                                rw [bv_zext32_toNat, hs.1.1.vals_len]
                                have := hs.1.1.cur_vars_le; omega
                              c0_hstraight
                              c0_hsplit
                              · refine wp_join_group Jbin (fun _ xs m h => hJbin1 xs m h) ?_
                                intro _ hJbin2
                                let s2 : FullState :=
                                  { s with scratch := { s.scratch with scratch_buf := scr2 } }
                                have hs2 : FullSparseInvW c F0 F_cur s2 :=
                                  fullSparseInvW_upd_scratch_buf hs (by rw [hlen2, hscr_len])
                                c0_hstraight
                                apply wp_call_of_spec
                                dsimp only [vals, Arg.val]
                                refine hHasBin _ _ _ _
                                  ⟨c, F0, F_cur, s2, R, rfl, hs2.1, hs2.2.1, hm2, fun ok hok => ?_⟩
                                dsimp only
                                c0_hsplit
                                · have hok_t : ok = true := by cases ok <;> simp_all
                                  obtain ⟨_, _, _, _, hent2⟩ := hok hok_t
                                  refine wp_join_group Jbin (fun _ xs m h => hJbin2 xs m h) ?_
                                  intro _ hJbin3
                                  c0_hsplit
                                  · have heq3_le : eq_w.toNat + 3 ≤ c.scratch_cap := by bv_omega
                                    have hm2_f := focus_full_scr_buf hm2
                                    have h0_lt : eq_w.toNat < scr2.length := by rw [hlen2]; omega
                                    have h1_nat : (eq_w + 1#64).toNat = eq_w.toNat + 1 := by
                                      bv_omega
                                    have h2_nat : (eq_w + 2#64).toNat = eq_w.toNat + 2 := by
                                      bv_omega
                                    have h1_lt : (eq_w + 1#64).toNat < scr2.length := by
                                      rw [hlen2, h1_nat]; omega
                                    have h2_lt : (eq_w + 2#64).toNat < scr2.length := by
                                      rw [hlen2, h2_nat]; omega
                                    c0_hstraight
                                    have happ := collect_bins_append_ok hpool2
                                      (by rw [hlen2]; exact heq3_le) (by rw [hlen2]; exact hscr32)
                                      hv_lt_ov hov_lt_cv hcv31 hlit_nat hov_nat
                                      (by rw [hot_eq]; exact hent_bin) hent2
                                    dsimp only at happ
                                    let scr3 := ((scr2.set eq_w.toNat
                                      ((2#32 ||| (2#32 <<< (16#32 &&& 31#32))) |||
                                        (((ot &&& 1#32) ^^^ 1#32) <<< (31#32 &&& 31#32)))).set
                                      (eq_w + 1#64).toNat (v.setWidth 32)).set
                                      (eq_w + 2#64).toNat (ov.setWidth 32)
                                    have hm3_full := unfocus_full_scr_buf hm
                                    change (FullMem c { s with scratch :=
                                      { s.scratch with scratch_buf := scr3 } } ⋆ R) _ at hm3_full
                                    have heq3_nat : (eq_w + 3#64).toNat = eq_w.toNat + 3 := by
                                      bv_omega
                                    exact hJbin3 (eq_w + 3#64, ()) _
                                      ⟨scr3, by rw [heq3_nat]; exact heq3_le,
                                       by rw [happ.1, hlen2],
                                       by rw [heq3_nat]; exact happ.2, hm3_full⟩
                                  · exact hJbin3 (eq_w, ()) m2 ⟨scr2, heqw_le, hlen2, hpool2, hm2⟩
                                · exact hJbin2 (eq_w, ()) m2 ⟨scr2, heqw_le, hlen2, hpool2, hm2⟩
                              · exact hJbin1 (eq_w, ()) m2 ⟨scr2, heqw_le, hlen2, hpool2, hm2⟩
                            · exact hJbin1 (eq_w, ()) m2 ⟨scr2, heqw_le, hlen2, hpool2, hm2⟩
                          · exact hJbin1 (eq_w, ()) m2 ⟨scr2, heqw_le, hlen2, hpool2, hm2⟩
                        · exfalso
                          exact hne_ff (by rw [← hw0_is, ← hentry_c0]; bv_omega)
                    · exfalso
                      have hz : (w0 &&& 0x80000000#32) = 0#32 := by
                        rw [← hw0_is, ← hentry_c0]; bv_omega
                      exact hmsb hz
                  | @large _ rem' w0 _ hw0_eq _ hmsb _ _ hrest =>
                    have hw0_is : entry = w0 := by
                      rw [hentry_opt] at hw0_eq; exact Option.some.inj hw0_eq
                    c0_hsplit
                    · exfalso
                      have hnz : (w0 &&& 0x80000000#32) ≠ 0#32 := by
                        rw [← hw0_is, ← hentry_c0]; bv_omega
                      exact hnz hmsb
                    · c0_hsplit
                      · exfalso; rw [← hwsz_c0] at hrem; bv_omega
                      · c0_hstraight
                        have hwi2_nat : (wi + 2#64).toNat = wi.toNat + 2 := by bv_omega
                        refine hJwi_step (eq_w, wi + 2#64, ()) m2
                          ⟨scr2, by omega, by omega, heqw_le, hlen2, ?_, hpool2, hm2⟩
                        have hp2 : w_off.toNat + (wi + 2#64).toNat = w_off.toNat + wi.toNat + 2 :=
                          by omega
                        have hr2 : w_sz.toNat - (wi + 2#64).toNat = rem' := by omega
                        rw [hp2, hr2]; exact hrest
              · exact hJwi_brk (eq_w, wi, ()) m2 ⟨scr2, heqw_le, hlen2, hpool2, hm2⟩
          · exact hJwi_exit (eq_c, ()) m1 ⟨scr1, heq1_le, hlen1, hpool1, hm1⟩
      · exact hJv_next (eq_c, ()) m1 ⟨scr1, heq1_le, hlen1, hpool1, hm1⟩
  · c0_hstraight
    exact hQ eq_c scr1 m1 (by rw [hlen1, hscr_len]) heq1_le hpool1 hm1

/-! ## 3. Multi-Round Variable-Elimination Chain Merge (`full_xor_chain_merge`) -/

@[expose] def fullXorChainMergeSpec : Spec [i64, i64] [i64] := fun (h, eq_end, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧
    FullSparseInvW c F0 F_cur s ∧
    eq_end.toNat ≤ c.scratch_cap ∧
    XorEqPoolOk (cnfOfClauses F_cur) s.core.cur_vars s.scratch.scratch_buf eq_end.toNat 0 ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (res : BitVec 64) (s' : FullState) (m' : Mem 64),
      FullSparseInvW c F0 F_cur s' →
      s'.core.cur_vars = s.core.cur_vars →
      s'.core.cur_level = s.core.cur_level →
      s'.core.fuel = s.core.fuel →
      FullExtScratchPres s s' →
      (res = 0xFFFFFFFFFFFFFFFF#64 → F0.Unsat ∧ s'.core.inconsistent ≠ 0#64) →
      (res ≠ 0xFFFFFFFFFFFFFFFF#64 →
        res.toNat ≤ c.scratch_cap ∧ s'.core.inconsistent = s.core.inconsistent ∧
        XorEqPoolOk (cnfOfClauses F_cur) s'.core.cur_vars s'.scratch.scratch_buf res.toNat 0) →
      (FullMem c s' ⋆ R) m' → Q (res, ()) m'

private def ChainOccInv (scr : List (BitVec 32)) (eq_end cv bound : Nat)
    (occ eq1 eq2 : List (BitVec 32)) : Prop :=
  ∀ u < cv,
    (occ[u]?.getD 0#32).toNat ≤ bound ∧
    (1 ≤ (occ[u]?.getD 0#32).toNat →
      (eq1[u]?.getD 0#32).toNat < eq_end ∧
      (eq1[u]?.getD 0#32).toNat ∈ poolStarts scr eq_end 0 eq_end) ∧
    (2 ≤ (occ[u]?.getD 0#32).toNat →
      (eq2[u]?.getD 0#32).toNat < eq_end ∧
      (eq2[u]?.getD 0#32).toNat ∈ poolStarts scr eq_end 0 eq_end)

private theorem poolStarts_mono_fuel {scr : List (BitVec 32)} {eq_end : Nat} :
    ∀ {f0 f1 p q : Nat}, f0 ≤ f1 → q ∈ poolStarts scr eq_end p f0 →
      q ∈ poolStarts scr eq_end p f1
  | 0, _, _, _, _, hq => nomatch hq
  | f0 + 1, f1, p, q, hf, hq => by
    cases f1 with
    | zero => omega
    | succ f1 =>
      unfold poolStarts at hq ⊢
      split at hq
      · rename_i hp
        simp only [hp, ↓reduceIte, List.mem_cons] at hq ⊢
        rcases hq with rfl | hr
        · exact Or.inl rfl
        · exact Or.inr (poolStarts_mono_fuel (by omega) hr)
      · exact nomatch hq

private theorem fullSparseInvW_upd_chain {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hs : FullSparseInvW c F0 F_cur s)
    {scr' ws1' ws2' tr' : List (BitVec 32)}
    (h1 : scr'.length = s.scratch.scratch_buf.length)
    (h2 : ws1'.length = s.scratch.work_stk1.length)
    (h3 : ws2'.length = s.scratch.work_stk2.length)
    (h4 : tr'.length = s.scratch.tarjan_reach.length) :
    FullSparseInvW c F0 F_cur { s with scratch :=
      { s.scratch with
        scratch_buf := scr', work_stk1 := ws1',
        work_stk2 := ws2', tarjan_reach := tr' } } :=
  fullSparseInvW_upd_tarjan_reach
    (fullSparseInvW_upd_work_stk2
      (fullSparseInvW_upd_work_stk1 (fullSparseInvW_upd_scratch_buf hs h1) h2) h3) h4

private theorem chain_occ_step {scr : List (BitVec 32)} {eq_end cv bound x_nat : Nat}
    {occ eq1 eq2 : List (BitVec 32)} {p32 c_occ : BitVec 32}
    (hinv : ChainOccInv scr eq_end cv bound occ eq1 eq2)
    (hbd_lt : bound + 1 < 2 ^ 32)
    (hx_lt : x_nat < cv) (hx_occ : x_nat < occ.length)
    (hx_eq1 : x_nat < eq1.length) (hx_eq2 : x_nat < eq2.length)
    (hc_eq : occ[x_nat]?.getD 0#32 = c_occ)
    (hp_lt : p32.toNat < eq_end)
    (hp_mem : p32.toNat ∈ poolStarts scr eq_end 0 eq_end) :
    let eq1' := if c_occ = 0#32 then eq1.set x_nat p32 else eq1
    let eq2' := if c_occ = 0#32 then eq2 else if c_occ = 1#32 then eq2.set x_nat p32 else eq2
    let occ' := occ.set x_nat (c_occ + 1#32)
    ChainOccInv scr eq_end cv (bound + 1) occ' eq1' eq2' := by
  intro eq1' eq2' occ' u hu
  have hu_old := hinv u hu
  by_cases hux : u = x_nat
  · subst hux
    have hocc_u : occ'[u]?.getD 0#32 = c_occ + 1#32 := by
      simp [occ', List.getElem?_set_self hx_occ]
    have hc_le : c_occ.toNat ≤ bound := by rw [← hc_eq]; exact hu_old.1
    have hc1_nat : (c_occ + 1#32).toNat = c_occ.toNat + 1 := by bv_omega
    rw [hocc_u, hc1_nat]
    refine ⟨by omega, fun _ => ?_, fun h2 => ?_⟩
    · by_cases hc0 : c_occ = 0#32
      · simp [eq1', hc0, List.getElem?_set_self hx_eq1, hp_lt, hp_mem]
      · simp only [eq1', hc0, ↓reduceIte]
        exact hu_old.2.1 (by rw [hc_eq]; bv_omega)
    · by_cases hc0 : c_occ = 0#32
      · subst hc0; simp at h2
      · by_cases hc1 : c_occ = 1#32
        · simp [eq2', hc1, List.getElem?_set_self hx_eq2, hp_lt, hp_mem]
        · simp only [eq2', hc0, hc1, ↓reduceIte]
          exact hu_old.2.2 (by rw [hc_eq]; bv_omega)
  · have hocc_u : occ'[u]? = occ[u]? := List.getElem?_set_ne (Ne.symm hux)
    have heq1_u : eq1'[u]? = eq1[u]? := by
      dsimp only [eq1']; split
      · exact List.getElem?_set_ne (Ne.symm hux)
      · rfl
    have heq2_u : eq2'[u]? = eq2[u]? := by
      dsimp only [eq2']; split
      · rfl
      · split
        · exact List.getElem?_set_ne (Ne.symm hux)
        · rfl
    rw [hocc_u, heq1_u, heq2_u]
    exact ⟨by omega, hu_old.2.1, hu_old.2.2⟩

theorem full_xor_chain_merge_wp (Γ : Env) :
    (∀ a m Q X, fullXorMergeTwoSpec a m Q X →
      Γ "full_xor_merge_two" [i64, i64, i64, i64] [i64] a m Q X) →
    (∀ a m Q X, fullXorCompactPoolSpec a m Q X →
      Γ "full_xor_compact_pool" [i64, i64] [i64] a m Q X) →
    ∀ a m Q X, fullXorChainMergeSpec a m Q X →
      Func.wp Γ full_xor_chain_merge_body a m Q X := by
  intro hMerge hCompact (h, eq0, ()) m0 Q X
    ⟨c, F0, F_cur, s, R, hc_eq, hs, heq0_le, hpool0, hm0, hQ⟩
  subst hc_eq
  unfold full_xor_chain_merge_body Func.wp; dsimp only
  have hscr_len : s.scratch.scratch_buf.length = c.scratch_cap := hs.1.2.scratch_buf_len
  have hws1_len : s.scratch.work_stk1.length = 2 * c.max_vars := hs.1.2.work_stk1_len
  have hws2_len : s.scratch.work_stk2.length = 2 * c.max_vars := hs.1.2.work_stk2_len
  have htr_len : s.scratch.tarjan_reach.length = 2 * c.max_vars := hs.1.2.tarjan_reach_len
  have hscr32 : c.scratch_cap < 2 ^ 32 := by have := c.hscr; have := dimacsBound_val; omega
  have hcv_le_mv : s.core.cur_vars ≤ c.max_vars := hs.1.1.cur_vars_le
  have hcv31 : s.core.cur_vars < 2 ^ 31 := by have := c.hmaxv; have := dimacsBound_val; omega
  c0_hstraight
  have hm0_f := focus_full_chain hm0
  let Jret : Tup Val [i64, i64] → Mem 64 → Prop := fun (eq_f, _rnd, ()) mf =>
    ∃ scr_f ws1_f ws2_f tr_f,
      eq_f.toNat ≤ c.scratch_cap ∧
      scr_f.length = c.scratch_cap ∧ ws1_f.length = 2 * c.max_vars ∧
      ws2_f.length = 2 * c.max_vars ∧ tr_f.length = 2 * c.max_vars ∧
      XorEqPoolOk (cnfOfClauses F_cur) s.core.cur_vars scr_f eq_f.toNat 0 ∧
      (array (t := i32) c.pScratchBuf scr_f ⋆
       array (t := i32) c.pWorkStk1 ws1_f ⋆
       array (t := i32) c.pWorkStk2 ws2_f ⋆
       array (t := i32) c.pTarjanReach tr_f ⋆
       (FullChainRest c s ⋆ R)) mf
  refine wp_join_group Jret ?_ ?_
  · rintro _ ⟨eq_f, _rnd, _⟩ mf ⟨scr_f, ws1_f, ws2_f, tr_f, heqf_le, hl_s, hl_1, hl_2, hl_t,
        hpool_f, hm_f⟩
    c0_hstraight
    have hm_full := unfocus_full_chain hm_f
    let s' : FullState := { s with scratch :=
      { s.scratch with
        scratch_buf := scr_f, work_stk1 := ws1_f,
        work_stk2 := ws2_f, tarjan_reach := tr_f } }
    have hs' : FullSparseInvW c F0 F_cur s' :=
      fullSparseInvW_upd_chain hs (by rw [hl_s, hscr_len]) (by rw [hl_1, hws1_len])
        (by rw [hl_2, hws2_len]) (by rw [hl_t, htr_len])
    refine hQ eq_f s' mf hs' rfl rfl rfl ⟨rfl, rfl⟩
      (fun hff => by exfalso; rw [hff] at heqf_le; bv_omega)
      (fun _ => ⟨heqf_le, rfl, hpool_f⟩) hm_full
  · intro _ hJret
    let Jrnd : Tup Val [i64, i64] → Mem 64 → Prop := fun (eq_r, rnd, ()) m1 =>
      ∃ scr1 ws1 ws2 tr1,
        rnd.toNat ≤ 16 ∧ eq_r.toNat ≤ c.scratch_cap ∧
        scr1.length = c.scratch_cap ∧ ws1.length = 2 * c.max_vars ∧
        ws2.length = 2 * c.max_vars ∧ tr1.length = 2 * c.max_vars ∧
        XorEqPoolOk (cnfOfClauses F_cur) s.core.cur_vars scr1 eq_r.toNat 0 ∧
        (array (t := i32) c.pScratchBuf scr1 ⋆
         array (t := i32) c.pWorkStk1 ws1 ⋆
         array (t := i32) c.pWorkStk2 ws2 ⋆
         array (t := i32) c.pTarjanReach tr1 ⋆
         (FullChainRest c s ⋆ R)) m1
    refine wp_loop_inv Jrnd (fun (_eq, rnd, ()) _ => 16 - rnd.toNat)
      (fun _ h => by
        c0_hstraight
        exact h (eq0, 0#64, ()) m0 ⟨s.scratch.scratch_buf, s.scratch.work_stk1,
          s.scratch.work_stk2, s.scratch.tarjan_reach, Nat.zero_le _, heq0_le,
          hscr_len, hws1_len, hws2_len, htr_len, hpool0, hm0_f⟩) ?_
    rintro _ ⟨eq_r, rnd, _⟩ m1 ⟨scr1, ws1, ws2, tr1, hrnd_le, heqr_le, hl_s1, hl_11, hl_21,
        hl_t1, hpool1, hm1⟩ hJrnd_ih
    c0_hsplit
    · have hrnd_lt : rnd.toNat < 16 := by bv_omega
      let Jinit : Tup Val [i64] → Mem 64 → Prop := fun (v, ()) m2 =>
        ∃ ws1_i ws2_i tr_i,
          v.toNat ≤ s.core.cur_vars ∧
          ws1_i.length = 2 * c.max_vars ∧ ws2_i.length = 2 * c.max_vars ∧
          tr_i.length = 2 * c.max_vars ∧
          (∀ u < v.toNat, ws1_i[u]? = some 0#32) ∧
          (array (t := i32) c.pScratchBuf scr1 ⋆
           array (t := i32) c.pWorkStk1 ws1_i ⋆
           array (t := i32) c.pWorkStk2 ws2_i ⋆
           array (t := i32) c.pTarjanReach tr_i ⋆
           (FullChainRest c s ⋆ R)) m2
      refine wp_loop_inv Jinit (fun (v, ()) _ => s.core.cur_vars - v.toNat)
        (fun _ h => by
          c0_hstraight
          exact h (0#64, ()) m1 ⟨ws1, ws2, tr1, Nat.zero_le _, hl_11, hl_21, hl_t1,
            fun _ hu => absurd hu (Nat.not_lt_zero _), hm1⟩) ?_
      rintro _ ⟨v, _⟩ m2 ⟨ws1_i, ws2_i, tr_i, hv_le, hli1, hli2, hlit, hzero, hm2⟩ hJinit_ih
      c0_hsplit
      · have hv_lt : v.toNat < s.core.cur_vars := by bv_omega
        have hv1 : v.toNat < ws1_i.length := by omega
        have hv2 : v.toNat < ws2_i.length := by omega
        have hvt : v.toNat < tr_i.length := by omega
        c0_hstraight
        refine hJinit_ih (v + 1#64, ()) _ (by dsimp only; bv_omega)
          ⟨ws1_i.set v.toNat 0#32, ws2_i.set v.toNat 0xFFFFFFFF#32, tr_i.set v.toNat 0xFFFFFFFF#32,
           by bv_omega, by simp [hli1], by simp [hli2], by simp [hlit], fun u hu => ?_, ?_⟩
        · have hu' : u < v.toNat + 1 := by bv_omega
          rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hu') with hlt | rfl
          · rw [List.getElem?_set_ne (by omega)]; exact hzero u hlt
          · exact List.getElem?_set_self hv1
        · rw [Std.ExtHashMap.sep_emp] at hm
          change (array (t := i32) c.pTarjanReach (tr_i.set v.toNat 0xFFFFFFFF#32) ⋆
            (array (t := i32) c.pWorkStk2 (ws2_i.set v.toNat 0xFFFFFFFF#32) ⋆
              (array (t := i32) c.pWorkStk1 (ws1_i.set v.toNat 0#32) ⋆
                (array (t := i32) c.pScratchBuf scr1 ⋆ (FullChainRest c s ⋆ R))))) m at hm
          ecancel
      · have hv_eq : v.toNat = s.core.cur_vars := by bv_omega
        have hocc0 : ChainOccInv scr1 eq_r.toNat s.core.cur_vars 0 ws1_i ws2_i tr_i := by
          intro u hu
          have hz := hzero u (by rw [hv_eq]; exact hu)
          simp [hz]
        let Jscan_exit : Tup Val [i64] → Mem 64 → Prop := fun (_p, ()) m3 =>
          ∃ occ_s eq1_s eq2_s,
            occ_s.length = 2 * c.max_vars ∧ eq1_s.length = 2 * c.max_vars ∧
            eq2_s.length = 2 * c.max_vars ∧
            ChainOccInv scr1 eq_r.toNat s.core.cur_vars eq_r.toNat occ_s eq1_s eq2_s ∧
            (array (t := i32) c.pScratchBuf scr1 ⋆
             array (t := i32) c.pWorkStk1 occ_s ⋆
             array (t := i32) c.pWorkStk2 eq1_s ⋆
             array (t := i32) c.pTarjanReach eq2_s ⋆
             (FullChainRest c s ⋆ R)) m3
        refine wp_join_group Jscan_exit ?_ ?_
        · rintro _ ⟨_p_end, _⟩ m3 ⟨occ_s, eq1_s, eq2_s, hl_o, hl_e1, hl_e2, hocc_s, hm3⟩
          let Jmrg : Tup Val [i64, i64, i64] → Mem 64 → Prop :=
            fun (eq_m, vm, merges, ()) m4 =>
              ∃ scr_m : List (BitVec 32),
                vm.toNat ≤ s.core.cur_vars ∧
                eq_r.toNat ≤ eq_m.toNat ∧ eq_m.toNat ≤ c.scratch_cap ∧
                scr_m.length = c.scratch_cap ∧
                XorEqPoolOk (cnfOfClauses F_cur) s.core.cur_vars scr_m eq_m.toNat 0 ∧
                (∀ idx < eq_r.toNat,
                  (((scr_m[idx]?.getD 0#32) >>> 16#32) &&& 0x7FFF#32) =
                  (((scr1[idx]?.getD 0#32) >>> 16#32) &&& 0x7FFF#32)) ∧
                (array (t := i32) c.pScratchBuf scr_m ⋆
                 array (t := i32) c.pWorkStk1 occ_s ⋆
                 array (t := i32) c.pWorkStk2 eq1_s ⋆
                 array (t := i32) c.pTarjanReach eq2_s ⋆
                 (FullChainRest c s ⋆ R)) m4
          refine wp_loop_inv Jmrg (fun (_, vm, _, ()) _ => s.core.cur_vars - vm.toNat)
            (fun _ h => by
              c0_hstraight
              exact h (eq_r, 0#64, 0#64, ()) m3 ⟨scr1, Nat.zero_le _, Nat.le_refl _, heqr_le,
                hl_s1, hpool1, fun _ _ => rfl, hm3⟩) ?_
          rintro _ ⟨eq_m, vm, merges, _⟩ m4 ⟨scr_m, hvm_le, heqr_m, heqm_cap, hls_m, hpool_m,
              hstride_m, hm4⟩ hJmrg_ih
          c0_hsplit
          · have hvm_lt : vm.toNat < s.core.cur_vars := by bv_omega
            have hvm_o : vm.toNat < occ_s.length := by omega
            have hvm_e1 : vm.toNat < eq1_s.length := by omega
            have hvm_e2 : vm.toNat < eq2_s.length := by omega
            let Jmrg_next : Tup Val [i64, i64] → Mem 64 → Prop :=
              fun (eq_n, merges_n, ()) m5 =>
                ∃ scr_n : List (BitVec 32),
                  eq_r.toNat ≤ eq_n.toNat ∧ eq_n.toNat ≤ c.scratch_cap ∧
                  scr_n.length = c.scratch_cap ∧
                  XorEqPoolOk (cnfOfClauses F_cur) s.core.cur_vars scr_n eq_n.toNat 0 ∧
                  (∀ idx < eq_r.toNat,
                    (((scr_n[idx]?.getD 0#32) >>> 16#32) &&& 0x7FFF#32) =
                    (((scr1[idx]?.getD 0#32) >>> 16#32) &&& 0x7FFF#32)) ∧
                  (array (t := i32) c.pScratchBuf scr_n ⋆
                   array (t := i32) c.pWorkStk1 occ_s ⋆
                   array (t := i32) c.pWorkStk2 eq1_s ⋆
                   array (t := i32) c.pTarjanReach eq2_s ⋆
                   (FullChainRest c s ⋆ R)) m5
            c0_hstraight
            refine wp_join_group Jmrg_next ?_ ?_
            · rintro _ ⟨eq_n, merges_n, _⟩ m5 ⟨scr_n, heqr_n, heqn_cap, hls_n, hpool_n,
                  hstride_n, hm5⟩
              c0_hstraight
              exact hJmrg_ih (eq_n, vm + 1#64, merges_n, ()) m5 (by dsimp only; bv_omega)
                ⟨scr_n, by bv_omega, heqr_n, heqn_cap, hls_n, hpool_n, hstride_n, hm5⟩
            · intro _ hJmrg_next
              c0_hsplit
              · have hocc_eq2 : (occ_s[vm.toNat]?.getD 0#32).toNat = 2 := by
                  rw [List.getElem?_eq_getElem hvm_o, Option.getD_some]; bv_omega
                obtain ⟨_, h1_ok, h2_ok⟩ := hocc_s vm.toNat hvm_lt
                obtain ⟨hp1_lt0, hp1_mem0⟩ := h1_ok (by omega)
                obtain ⟨hp2_lt0, hp2_mem0⟩ := h2_ok (by omega)
                c0_hstraight
                refine wp_join_group Jmrg_next (fun _ xs m h => hJmrg_next xs m h) ?_
                intro _ hJmrg1
                let p1 : BitVec 64 := (eq1_s[vm.toNat]'hvm_e1).setWidth 64
                let p2 : BitVec 64 := (eq2_s[vm.toNat]'hvm_e2).setWidth 64
                have hp1_nat : p1.toNat = (eq1_s[vm.toNat]?.getD 0#32).toNat := by
                  dsimp only [p1]; rw [bv_zext32_toNat, List.getElem?_eq_getElem hvm_e1]; rfl
                have hp2_nat : p2.toNat = (eq2_s[vm.toNat]?.getD 0#32).toNat := by
                  dsimp only [p2]; rw [bv_zext32_toNat, List.getElem?_eq_getElem hvm_e2]; rfl
                c0_hsplit
                · c0_hsplit
                  · c0_hsplit
                    · have hp1_ne_p2 : p1 ≠ p2 := by dsimp only [p1, p2]; bv_omega
                      have hp1_lt_m : p1.toNat < eq_m.toNat := by rw [hp1_nat]; omega
                      have hp2_lt_m : p2.toNat < eq_m.toNat := by rw [hp2_nat]; omega
                      have hp1_bd : p1.toNat < scr_m.length := by omega
                      have hp2_bd : p2.toNat < scr_m.length := by omega
                      c0_hstraight
                      refine wp_join_group Jmrg_next (fun _ xs m h => hJmrg1 xs m h) ?_
                      intro _ hJmrg2
                      let h1 := scr_m[(eq1_s[vm.toNat]'hvm_e1).toNat]'(by
                        have := bv_zext32_toNat (eq1_s[vm.toNat]'hvm_e1); exact hp1_bd)
                      let h2 := scr_m[(eq2_s[vm.toNat]'hvm_e2).toNat]'(by
                        have := bv_zext32_toNat (eq2_s[vm.toNat]'hvm_e2); exact hp2_bd)
                      have hh1_opt : scr_m[p1.toNat]?.getD 0#32 = h1 := by
                        have hpeq : p1.toNat = (eq1_s[vm.toNat]'hvm_e1).toNat :=
                          bv_zext32_toNat _
                        rw [hpeq, List.getElem?_eq_getElem (by rw [← hpeq]; exact hp1_bd)]; rfl
                      have hh2_opt : scr_m[p2.toNat]?.getD 0#32 = h2 := by
                        have hpeq : p2.toNat = (eq2_s[vm.toNat]'hvm_e2).toNat :=
                          bv_zext32_toNat _
                        rw [hpeq, List.getElem?_eq_getElem (by rw [← hpeq]; exact hp2_bd)]; rfl
                      have hl1_and : (h1 &&& 0xFFFF#32).toNat =
                          h1.toNat &&& (65535 % 2 ^ 32) := BitVec.toNat_and h1 0xFFFF#32
                      have hl2_and : (h2 &&& 0xFFFF#32).toNat =
                          h2.toNat &&& (65535 % 2 ^ 32) := BitVec.toNat_and h2 0xFFFF#32
                      have hl1_lt16 : (h1 &&& 0xFFFF#32).toNat < 2 ^ 16 := by
                        rw [BitVec.toNat_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
                      have hl2_lt16 : (h2 &&& 0xFFFF#32).toNat < 2 ^ 16 := by
                        rw [BitVec.toNat_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
                      c0_hsplit
                      · have hl1_pos : 0 < (h1 &&& 0xFFFF#32).toNat := by
                          rw [hl1_and]; dsimp only [h1]; bv_omega
                        clear hc; c0_hsplit
                        · have hl2_pos : 0 < (h2 &&& 0xFFFF#32).toNat := by
                            rw [hl2_and]; dsimp only [h2]; bv_omega
                          clear hc; c0_hsplit
                          · clear hc; c0_hsplit
                            · clear hc; c0_hsplit
                              · clear hc; c0_hsplit
                                · clear hc; c0_hsplit
                                  · have hl12_le : (h1 &&& 0xFFFF#32).toNat +
                                        (h2 &&& 0xFFFF#32).toNat ≤ 512 := by
                                      rw [hl1_and] at hl1_lt16 ⊢
                                      rw [hl2_and] at hl2_lt16 ⊢
                                      dsimp only [h1, h2] at hl1_lt16 hl2_lt16 ⊢; bv_omega
                                    clear hc
                                    refine wp_join_group Jmrg_next
                                      (fun _ xs m h => hJmrg2 xs m h) ?_
                                    intro _ hJmrg3
                                    c0_hsplit
                                    · have hcap_ok : eq_m.toNat + 1 +
                                          (h1 &&& 0xFFFF#32).toNat +
                                          (h2 &&& 0xFFFF#32).toNat ≤ c.scratch_cap := by
                                        rw [hl1_and] at hl1_lt16 ⊢
                                        rw [hl2_and] at hl2_lt16 ⊢
                                        dsimp only [h1, h2] at hl1_lt16 hl2_lt16 ⊢; bv_omega
                                      have hp1_mem_m := poolStarts_extend (p := p1.toNat) heqr_m
                                        (by rw [hp1_nat]; exact hp1_lt0) hstride_m hpool1
                                        (by rw [hp1_nat]; exact hp1_mem0)
                                      have hp2_mem_m := poolStarts_extend (p := p2.toNat) heqr_m
                                        (by rw [hp2_nat]; exact hp2_lt0) hstride_m hpool1
                                        (by rw [hp2_nat]; exact hp2_mem0)
                                      c0_hstraight
                                      apply wp_call_of_spec
                                      dsimp only [vals, Arg.val]
                                      refine hMerge _ _ _ _
                                        ⟨cnfOfClauses F_cur, s.core.cur_vars, eq_m.toNat,
                                         eq_r.toNat, eq_r.toNat, scr_m,
                                         array (t := i32) c.pWorkStk1 occ_s ⋆
                                           array (t := i32) c.pWorkStk2 eq1_s ⋆
                                           array (t := i32) c.pTarjanReach eq2_s ⋆
                                           (FullChainRest c s ⋆ R),
                                         hp1_lt_m, hp2_lt_m, hp1_ne_p2, rfl, hp1_mem_m, hp2_mem_m,
                                         by rw [hh1_opt]; exact hl1_pos,
                                         by rw [hh2_opt]; exact hl2_pos,
                                         by rw [hh1_opt, hh2_opt]; exact hl12_le,
                                         by rw [hh1_opt, hh2_opt, hls_m]; exact hcap_ok,
                                         by rw [hls_m]; exact hscr32,
                                         hpool_m, by ecancel,
                                         fun next_dst scr_n m5 hlen_n hff hok hm5 => ?_⟩
                                      dsimp only
                                      c0_hsplit
                                      · have hunsat_cur := hff (by bv_omega)
                                        have hF0_unsat :=
                                          unsat_of_sparseW_inconsistent hs hunsat_cur
                                        have hm5_full := unfocus_full_chain (by ecancel)
                                        let s_m : FullState := { s with scratch :=
                                          { s.scratch with
                                            scratch_buf := scr_n, work_stk1 := occ_s,
                                            work_stk2 := eq1_s, tarjan_reach := eq2_s } }
                                        have hs_m : FullSparseInvW c F0 F_cur s_m :=
                                          fullSparseInvW_upd_chain hs
                                            (by rw [hlen_n, hls_m, hscr_len])
                                            (by rw [hl_o, hws1_len])
                                            (by rw [hl_e1, hws2_len]) (by rw [hl_e2, htr_len])
                                        c0_hstraight
                                        let s_f : FullState :=
                                          { s_m with core :=
                                            { s_m.core with inconsistent := 1#64 } }
                                        have hs_f : FullSparseInvW c F0 F_cur s_f :=
                                          fullSparseInvW_upd_inc hs_m 1#64 (fun _ => hunsat_cur)
                                        exact hQ 0xFFFFFFFFFFFFFFFF#64 s_f _ hs_f rfl rfl rfl
                                          ⟨rfl, rfl⟩ (fun _ => ⟨hF0_unsat, by simp [s_f]⟩)
                                          (fun hn => by simp at hn)
                                          (by rw [Std.ExtHashMap.sep_emp] at hm; exact hm)
                                      · obtain ⟨hge_m, hle_m, hpool_n, _, hstr_n, _⟩ :=
                                          hok (by bv_omega)
                                        rw [hh1_opt, hh2_opt] at hle_m
                                        c0_hstraight
                                        refine hJmrg3 (next_dst, merges + 1#64, ()) m5
                                          ⟨scr_n, by omega, by omega, by rw [hlen_n, hls_m],
                                           hpool_n, fun idx hidx => ?_, by ecancel⟩
                                        rw [hstr_n idx (by omega), hstride_m idx hidx]
                                    · exact hJmrg3 (eq_m, merges, ()) m4
                                        ⟨scr_m, heqr_m, heqm_cap, hls_m, hpool_m, hstride_m, hm4⟩
                                  · exact hJmrg2 (eq_m, merges, ()) m4
                                      ⟨scr_m, heqr_m, heqm_cap, hls_m, hpool_m, hstride_m, hm4⟩
                                · exact hJmrg2 (eq_m, merges, ()) m4
                                    ⟨scr_m, heqr_m, heqm_cap, hls_m, hpool_m, hstride_m, hm4⟩
                              · exact hJmrg2 (eq_m, merges, ()) m4
                                  ⟨scr_m, heqr_m, heqm_cap, hls_m, hpool_m, hstride_m, hm4⟩
                            · exact hJmrg2 (eq_m, merges, ()) m4
                                ⟨scr_m, heqr_m, heqm_cap, hls_m, hpool_m, hstride_m, hm4⟩
                          · exact hJmrg2 (eq_m, merges, ()) m4
                              ⟨scr_m, heqr_m, heqm_cap, hls_m, hpool_m, hstride_m, hm4⟩
                        · exact hJmrg2 (eq_m, merges, ()) m4
                            ⟨scr_m, heqr_m, heqm_cap, hls_m, hpool_m, hstride_m, hm4⟩
                      · exact hJmrg2 (eq_m, merges, ()) m4
                          ⟨scr_m, heqr_m, heqm_cap, hls_m, hpool_m, hstride_m, hm4⟩
                    · exact hJmrg1 (eq_m, merges, ()) m4
                        ⟨scr_m, heqr_m, heqm_cap, hls_m, hpool_m, hstride_m, hm4⟩
                  · exact hJmrg1 (eq_m, merges, ()) m4
                      ⟨scr_m, heqr_m, heqm_cap, hls_m, hpool_m, hstride_m, hm4⟩
                · exact hJmrg1 (eq_m, merges, ()) m4
                    ⟨scr_m, heqr_m, heqm_cap, hls_m, hpool_m, hstride_m, hm4⟩
              · exact hJmrg_next (eq_m, merges, ()) m4
                  ⟨scr_m, heqr_m, heqm_cap, hls_m, hpool_m, hstride_m, hm4⟩
          · c0_hstraight
            apply wp_call_of_spec
            dsimp only [vals, Arg.val]
            refine hCompact _ _ _ _
              ⟨cnfOfClauses F_cur, s.core.cur_vars, scr_m,
               array (t := i32) c.pWorkStk1 occ_s ⋆
                 array (t := i32) c.pWorkStk2 eq1_s ⋆
                 array (t := i32) c.pTarjanReach eq2_s ⋆
                 (FullChainRest c s ⋆ R),
               by rw [hls_m]; exact heqm_cap, by rw [hls_m]; exact hscr32, hpool_m, by ecancel,
               fun eq_c scr_c m5 hlen_c heqc_le hpool_c _ hm5 => ?_⟩
            dsimp only
            c0_hsplit
            · exact hJret (eq_c, rnd, ()) m5 ⟨scr_c, occ_s, eq1_s, eq2_s, by omega,
                by rw [hlen_c, hls_m], hl_o, hl_e1, hl_e2, hpool_c, by ecancel⟩
            · c0_hstraight
              exact hJrnd_ih (eq_c, rnd + 1#64, ()) m5 (by dsimp only; bv_omega)
                ⟨scr_c, occ_s, eq1_s, eq2_s, by bv_omega, by omega,
                 by rw [hlen_c, hls_m], hl_o, hl_e1, hl_e2, hpool_c, by ecancel⟩
        · intro _ hJscan_exit
          let Jscan : Tup Val [i64] → Mem 64 → Prop := fun (p, ()) m3 =>
            ∃ occ_p eq1_p eq2_p,
              p.toNat ≤ eq_r.toNat ∧
              occ_p.length = 2 * c.max_vars ∧ eq1_p.length = 2 * c.max_vars ∧
              eq2_p.length = 2 * c.max_vars ∧
              XorEqPoolOk (cnfOfClauses F_cur) s.core.cur_vars scr1 eq_r.toNat p.toNat ∧
              (∀ q, q ∈ poolStarts scr1 eq_r.toNat p.toNat (eq_r.toNat - p.toNat) →
                q ∈ poolStarts scr1 eq_r.toNat 0 eq_r.toNat) ∧
              ChainOccInv scr1 eq_r.toNat s.core.cur_vars p.toNat occ_p eq1_p eq2_p ∧
              (array (t := i32) c.pScratchBuf scr1 ⋆
               array (t := i32) c.pWorkStk1 occ_p ⋆
               array (t := i32) c.pWorkStk2 eq1_p ⋆
               array (t := i32) c.pTarjanReach eq2_p ⋆
               (FullChainRest c s ⋆ R)) m3
          refine wp_loop_inv Jscan (fun (p, ()) _ => eq_r.toNat - p.toNat)
            (fun _ h => by
              c0_hstraight
              exact h (0#64, ()) m2 ⟨ws1_i, ws2_i, tr_i, Nat.zero_le _, hli1, hli2, hlit,
                hpool1, fun _ hq => hq, hocc0, hm2⟩) ?_
          rintro _ ⟨p, _⟩ m3 ⟨occ_p, eq1_p, eq2_p, hp_le, hlo_p, hle1_p, hle2_p, hpool_p,
              hstarts_p, hocc_p, hm3⟩ hJscan_ih
          c0_hsplit
          · have hp_lt : p.toNat < eq_r.toNat := by bv_omega
            generalize hp_eq : p.toNat = p_nat at hpool_p
            cases hpool_p with
            | done => rw [hp_eq] at hp_lt; omega
            | @step _ hdr stride clen _ hhdr hst hcl hbd hbody hrest =>
              rw [← hp_eq] at hhdr hbd hbody hrest
              have hp_scr : p.toNat < scr1.length := by omega
              have hget_hdr : scr1[p.toNat]'hp_scr = hdr := by
                have := hhdr; rw [List.getElem?_eq_getElem hp_scr] at this
                exact Option.some.inj this
              have hp_mem : p.toNat ∈ poolStarts scr1 eq_r.toNat 0 eq_r.toNat := by
                apply hstarts_p
                have hsub : eq_r.toNat - p.toNat = (eq_r.toNat - p.toNat - 1) + 1 := by omega
                rw [hsub, poolStarts_step_iff hp_lt]; exact Or.inl rfl
              have hnext_starts : ∀ q, q ∈ poolStarts scr1 eq_r.toNat (p.toNat + 1 + stride)
                  (eq_r.toNat - (p.toNat + 1 + stride)) →
                  q ∈ poolStarts scr1 eq_r.toNat 0 eq_r.toNat := by
                intro q hq
                apply hstarts_p
                have hsub : eq_r.toNat - p.toNat = (eq_r.toNat - p.toNat - 1) + 1 := by omega
                rw [hsub, poolStarts_step_iff hp_lt]
                have hst_c : (((scr1[p.toNat]?.getD 0#32) >>> 16#32) &&& 0x7FFF#32).toNat =
                    stride := by simp [hhdr, hst]
                rw [hst_c]
                exact Or.inr ⟨poolStarts_ge hq, poolStarts_mono_fuel (by omega) hq⟩
              c0_hstraight
              rw [hget_hdr]
              have hst_c0 :
                  ((hdr >>> OfNat.ofNat 16 &&& (32767 : BitVec 32)).setWidth 64).toNat =
                    stride := by
                change (((hdr >>> 16#32) &&& 0x7FFF#32).setWidth 64).toNat = stride
                rw [bv_zext32_toNat, ← hst]
              have hcl_c0 :
                  ((hdr &&& (65535 : BitVec 32)).setWidth 64).toNat = clen := by
                change ((hdr &&& 0xFFFF#32).setWidth 64).toNat = clen
                rw [bv_zext32_toNat, ← hcl]
              have hst_nat_c0 :
                  (hdr.toNat / 2 ^ OfNat.ofNat 16 &&& BitVec.toNat (32767 : BitVec 32)) =
                    stride := by
                have := hst_c0
                rwa [bv_zext32_toNat, BitVec.toNat_and, BitVec.toNat_ushiftRight,
                  Nat.shiftRight_eq_div_pow] at this
              have hst_nat_c0' : (hdr.toNat / 2 ^ OfNat.ofNat 16 &&& 32767 % 2 ^ 32) = stride :=
                hst_nat_c0
              have hcl_nat_c0 : (hdr.toNat &&& 65535 % 2 ^ 32) = clen := by
                have := hcl_c0
                rwa [bv_zext32_toNat, BitVec.toNat_and] at this
              c0_hsplit
              · exfalso
                have := hst_nat_c0; have := hst_nat_c0'; bv_omega
              · let Jp_next : Mem 64 → Prop := fun m4 =>
                  ∃ occ_n eq1_n eq2_n,
                    occ_n.length = 2 * c.max_vars ∧ eq1_n.length = 2 * c.max_vars ∧
                    eq2_n.length = 2 * c.max_vars ∧
                    ChainOccInv scr1 eq_r.toNat s.core.cur_vars (p.toNat + 1 + stride)
                      occ_n eq1_n eq2_n ∧
                    (array (t := i32) c.pScratchBuf scr1 ⋆
                     array (t := i32) c.pWorkStk1 occ_n ⋆
                     array (t := i32) c.pWorkStk2 eq1_n ⋆
                     array (t := i32) c.pTarjanReach eq2_n ⋆
                     (FullChainRest c s ⋆ R)) m4
                refine wp_join0 Jp_next ?_ ?_
                · rintro _ m4 ⟨occ_n, eq1_n, eq2_n, hlo_n, hle1_n, hle2_n, hocc_n, hm4⟩
                  c0_hstraight
                  have hp_next_nat :
                      (p + (1 : BitVec 64) +
                        BitVec.setWidth 64 (hdr >>> OfNat.ofNat 16 &&& (32767 : BitVec 32))).toNat =
                        p.toNat + 1 + stride := by
                    have := hst_nat_c0'; bv_omega
                  refine hJscan_ih _ m4 (by dsimp only; rw [hp_next_nat]; omega)
                    ⟨occ_n, eq1_n, eq2_n, by rw [hp_next_nat]; omega, hlo_n, hle1_n, hle2_n,
                     by rw [hp_next_nat]; exact hrest,
                     by rw [hp_next_nat]; exact hnext_starts,
                     by rw [hp_next_nat]; exact hocc_n, hm4⟩
                · intro _ hJp_next
                  c0_hsplit
                  · c0_hsplit
                    · have hcl_le_st : clen ≤ stride := by
                        have := hst_nat_c0; have := hcl_nat_c0; bv_omega
                      let Ji : Tup Val [i64] → Mem 64 → Prop := fun (i, ()) m4 =>
                        ∃ occ_i eq1_i eq2_i,
                          i.toNat ≤ clen ∧
                          occ_i.length = 2 * c.max_vars ∧ eq1_i.length = 2 * c.max_vars ∧
                          eq2_i.length = 2 * c.max_vars ∧
                          ChainOccInv scr1 eq_r.toNat s.core.cur_vars (p.toNat + i.toNat)
                            occ_i eq1_i eq2_i ∧
                          (array (t := i32) c.pScratchBuf scr1 ⋆
                           array (t := i32) c.pWorkStk1 occ_i ⋆
                           array (t := i32) c.pWorkStk2 eq1_i ⋆
                           array (t := i32) c.pTarjanReach eq2_i ⋆
                           (FullChainRest c s ⋆ R)) m4
                      refine wp_loop_inv Ji (fun (i, ()) _ => clen - i.toNat)
                        (fun _ h => by
                          c0_hstraight
                          exact h (0#64, ()) m3 ⟨occ_p, eq1_p, eq2_p, Nat.zero_le _, hlo_p,
                            hle1_p, hle2_p, by simpa using hocc_p, hm3⟩) ?_
                      rintro _ ⟨i, _⟩ m4 ⟨occ_i, eq1_i, eq2_i, hi_le, hlo_i, hle1_i, hle2_i,
                          hocc_i, hm4⟩ hJi_ih
                      c0_hsplit
                      · have hi_lt : i.toNat < clen := by have := hcl_nat_c0; bv_omega
                        have hpi_nat : (p + (1 : BitVec 64) + i).toNat = p.toNat + 1 + i.toNat := by
                          bv_omega
                        have hpi_mod : (p.toNat + 1 + i.toNat) % 2 ^ 64 = p.toNat + 1 + i.toNat :=
                          by omega
                        have hpi_lt : (p.toNat + 1 + i.toNat) % 2 ^ 64 < scr1.length := by
                          rw [hpi_mod]; omega
                        c0_hstraight
                        let x32 := scr1[(p.toNat + 1 + i.toNat) % 2 ^ 64]'hpi_lt
                        let Ji_next : Mem 64 → Prop := fun m5 =>
                          ∃ occ_n eq1_n eq2_n,
                            occ_n.length = 2 * c.max_vars ∧ eq1_n.length = 2 * c.max_vars ∧
                            eq2_n.length = 2 * c.max_vars ∧
                            ChainOccInv scr1 eq_r.toNat s.core.cur_vars (p.toNat + i.toNat + 1)
                              occ_n eq1_n eq2_n ∧
                            (array (t := i32) c.pScratchBuf scr1 ⋆
                             array (t := i32) c.pWorkStk1 occ_n ⋆
                             array (t := i32) c.pWorkStk2 eq1_n ⋆
                             array (t := i32) c.pTarjanReach eq2_n ⋆
                             (FullChainRest c s ⋆ R)) m5
                        refine wp_join0 Ji_next ?_ ?_
                        · rintro _ m5 ⟨occ_n, eq1_n, eq2_n, hlo_n, hle1_n, hle2_n, hocc_n, hm5⟩
                          c0_hstraight
                          have hi1 : (i + 1#64).toNat = i.toNat + 1 := by bv_omega
                          refine hJi_ih (i + 1#64, ()) m5 (by dsimp only; omega)
                            ⟨occ_n, eq1_n, eq2_n, by omega, hlo_n, hle1_n, hle2_n,
                             by rw [hi1, ← Nat.add_assoc]; exact hocc_n, hm5⟩
                        · intro _ hJi_next
                          c0_hsplit
                          · have hx_lt : x32.toNat < s.core.cur_vars := by
                              dsimp only [x32]; bv_omega
                            have hx_o : x32.toNat < occ_i.length := by omega
                            have hx_e1 : x32.toNat < eq1_i.length := by omega
                            have hx_e2 : x32.toNat < eq2_i.length := by omega
                            have hx_o64 : (x32.setWidth 64).toNat < occ_i.length := by
                              rw [bv_zext32_toNat]; exact hx_o
                            have hx_e1_64 : (x32.setWidth 64).toNat < eq1_i.length := by
                              rw [bv_zext32_toNat]; exact hx_e1
                            have hx_e2_64 : (x32.setWidth 64).toNat < eq2_i.length := by
                              rw [bv_zext32_toNat]; exact hx_e2
                            c0_hstraight
                            let c_occ := occ_i[x32.toNat]'hx_o
                            have hc_eq : occ_i[x32.toNat]?.getD 0#32 = c_occ := by
                              simp [c_occ, List.getElem?_eq_getElem hx_o]
                            have hx32_c0 :
                                (BitVec.setWidth 64
                                  (scr1[(p + (1 : BitVec 64) + i).toNat]'(by
                                    rw [hpi_nat]; omega))).toNat = x32.toNat := by
                              rw [bv_zext32_toNat]
                              exact congrArg BitVec.toNat
                                (list_getElem_congr (by rw [hpi_nat, hpi_mod]) _ _)
                            have hp32_nat : (p.setWidth 32).toNat = p.toNat :=
                              bv64_toNat_setWidth32_lt (by omega)
                            have hstep := chain_occ_step hocc_i (by omega) hx_lt
                              hx_o hx_e1 hx_e2
                              hc_eq (by rw [hp32_nat]; exact hp_lt)
                              (by rw [hp32_nat]; exact hp_mem)
                            dsimp only at hstep
                            let Jocc : Mem 64 → Prop := fun m5 =>
                              (array (t := i32) c.pScratchBuf scr1 ⋆
                               array (t := i32) c.pWorkStk1 occ_i ⋆
                               array (t := i32) c.pWorkStk2
                                 (if c_occ = 0#32 then eq1_i.set x32.toNat (p.setWidth 32)
                                  else eq1_i) ⋆
                               array (t := i32) c.pTarjanReach
                                 (if c_occ = 0#32 then eq2_i
                                  else if c_occ = 1#32 then eq2_i.set x32.toNat (p.setWidth 32)
                                  else eq2_i) ⋆
                               (FullChainRest c s ⋆ R)) m5
                            refine wp_join0 Jocc ?_ ?_
                            · rintro _ m5 hm5
                              dsimp only [Jocc] at hm5
                              c0_hstraight
                              refine hJi_next _ ⟨occ_i.set x32.toNat (c_occ + 1#32), _, _,
                                by simp [hlo_i], by split <;> simp [hle1_i],
                                by split; exact hle2_i; split <;> simp [hle2_i],
                                hstep, ?_⟩
                              have hocc_set_eq :
                                  occ_i.set
                                    (BitVec.setWidth 64
                                      (scr1[(p + (1 : BitVec 64) + i).toNat]'(by
                                        rw [hpi_nat]; omega))).toNat
                                    (occ_i[(BitVec.setWidth 64
                                      (scr1[(p + (1 : BitVec 64) + i).toNat]'(by
                                        rw [hpi_nat]; omega))).toNat]'(by
                                          rw [hx32_c0]; exact hx_o) + 1) =
                                  occ_i.set x32.toNat (c_occ + 1#32) := by
                                have hval :
                                    occ_i[(BitVec.setWidth 64
                                      (scr1[(p + (1 : BitVec 64) + i).toNat]'(by
                                        rw [hpi_nat]; omega))).toNat]'(by
                                          rw [hx32_c0]; exact hx_o) + (1 : BitVec 32) =
                                    c_occ + 1#32 := by
                                  rw [list_getElem_congr hx32_c0 _ _]; rfl
                                rw [hval, hx32_c0]
                              rw [Std.ExtHashMap.sep_emp, hocc_set_eq] at hm
                              rw [← Std.ExtHashMap.sep_assoc,
                                Std.ExtHashMap.sep_comm (array (t := i32) c.pWorkStk1 _),
                                ← Std.ExtHashMap.sep_assoc, ← Std.ExtHashMap.sep_assoc] at hm
                              exact hm
                            · intro _ hJocc
                              c0_hsplit
                              · have hc0 : c_occ = 0#32 := by dsimp only [c_occ, x32]; bv_omega
                                c0_hstraight
                                refine hJocc _ ?_
                                dsimp only [Jocc]; simp only [hc0, ↓reduceIte]
                                rw [Std.ExtHashMap.sep_emp, hx32_c0] at hm
                                ecancel
                              · have hc0 : c_occ ≠ 0#32 := by dsimp only [c_occ, x32]; bv_omega
                                refine wp_join0 Jocc (fun _ m h => hJocc m h) ?_
                                intro _ hJocc1
                                c0_hsplit
                                · have hc1 : c_occ = 1#32 := by dsimp only [c_occ, x32]; bv_omega
                                  c0_hstraight
                                  refine hJocc1 _ ?_
                                  dsimp only [Jocc]
                                  simp only [hc0, ↓reduceIte]
                                  simp only [hc1, ↓reduceIte]
                                  rw [Std.ExtHashMap.sep_emp, hx32_c0] at hm
                                  ecancel
                                · have hc1 : c_occ ≠ 1#32 := by dsimp only [c_occ, x32]; bv_omega
                                  refine hJocc1 m4 ?_
                                  dsimp only [Jocc]
                                  simp only [hc0, ↓reduceIte]
                                  simp only [hc1, ↓reduceIte]
                                  exact hm4
                          · exact hJi_next m4 ⟨occ_i, eq1_i, eq2_i, hlo_i, hle1_i, hle2_i,
                              fun u hu => let h := hocc_i u hu; ⟨by omega, h.2.1, h.2.2⟩, hm4⟩
                      · exact hJp_next m4 ⟨occ_i, eq1_i, eq2_i, hlo_i, hle1_i, hle2_i,
                          fun u hu => let h := hocc_i u hu; ⟨by omega, h.2.1, h.2.2⟩, hm4⟩
                    · exact hJp_next m3 ⟨occ_p, eq1_p, eq2_p, hlo_p, hle1_p, hle2_p,
                        fun u hu => let h := hocc_p u hu; ⟨by omega, h.2.1, h.2.2⟩, hm3⟩
                  · exact hJp_next m3 ⟨occ_p, eq1_p, eq2_p, hlo_p, hle1_p, hle2_p,
                      fun u hu => let h := hocc_p u hu; ⟨by omega, h.2.1, h.2.2⟩, hm3⟩
          · exact hJscan_exit (p, ()) m3 ⟨occ_p, eq1_p, eq2_p, hlo_p, hle1_p, hle2_p,
              fun u hu => let h := hocc_p u hu; ⟨by omega, h.2.1, h.2.2⟩, hm3⟩
    · exact hJret (eq_r, rnd, ()) m1 ⟨scr1, ws1, ws2, tr1, heqr_le, hl_s1, hl_11, hl_21, hl_t1,
        hpool1, hm1⟩

end LeanQbe.T.Examples.Kissat.FullM8XorGauss
