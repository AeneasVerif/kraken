/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Collect.Spec
import LeanQbe.T.Examples.Kissat.Proof.Collect.Tactics
import LeanQbe.T.Examples.Kissat.Proof.Collect.HelpersMoveSweep
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.ControlComb

/-!
# Pure Helpers for End-of-Collection Move-Redundant Proofs (`Proof.Collect.HelpersMoveEnd`)

Pure chain, literal-scan, and postcondition-lifting lemmas shared by `WpMoveRed1`
and `WpMoveRed2`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Collect

open Classical
open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Collect.Spec

public section

theorem bv64_add3_zext_toNat (sz : BitVec 32) :
    ((3 : BitVec 64) + sz.setWidth 64).toNat = 3 + sz.toNat := by
  have hlt := sz.isLt
  have h3 : (3 : BitVec 64).toNat = 3 := rfl
  rw [BitVec.toNat_add, zext_toNat sz (by decide), h3, Nat.mod_eq_of_lt (by omega)]

theorem bv8_sgt_zero_iff (b : BitVec 8)
    (hb : b = 0#8 ∨ b = 1#8 ∨ b = 255#8) :
    (BitVec.slt (BitVec.signExtend 32 (BitVec.setWidth 8 0#32))
      (BitVec.signExtend 32 b)) ↔ b = 1#8 := by
  rcases hb with rfl | rfl | rfl <;> decide

theorem lit_ushiftRight_one (lit : BitVec 32) :
    (lit >>> 1#32).toNat = lit.toNat / 2 := by
  change (lit >>> 1).toNat = lit.toNat / 2
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_one]

theorem lit_div2_lt {lit : BitVec 32} {cv : Nat}
    (hlt : (lit >>> 1#32).toNat < cv) : lit.toNat < 2 * cv := by
  rw [lit_ushiftRight_one] at hlt
  omega

theorem moveRangeChain_congr_out {ar1 ar2 : List (BitVec 32)} {lo hi rw : Nat}
    (heq : ∀ i, lo ≤ i → i < hi → ar2[i]? = ar1[i]?)
    (hmv : MoveRangeChain ar1 lo hi rw) :
    MoveRangeChain ar2 lo hi rw := by
  induction hmv with
  | empty => exact MoveRangeChain.empty
  | @step p hi rw hp1 hp2 hp3 hp4 _ ih =>
    have hp0 : ar2[p]?.getD 0#32 = ar1[p]?.getD 0#32 := by
      rw [heq p (Nat.le_refl _) (by omega)]
    have hp2' : ar2[p + 2]?.getD 0#32 = ar1[p + 2]?.getD 0#32 := by
      rw [heq (p + 2) (by omega) (by omega)]
    rw [← hp0, ← hp2']
    exact MoveRangeChain.step hp1 (by rw [hp0]; exact hp2) (by rw [hp2']; exact hp3)
      (by rw [hp2']; exact hp4)
      (by rw [hp2']; exact ih (fun i hi1 hi2 => heq i (by omega) hi2))

theorem refInChain_congr_out {ar1 ar2 : List (BitVec 32)} {lo hi r : Nat}
    (heq : ∀ i, lo ≤ i → i < hi → ar2[i]? = ar1[i]?)
    (hrc : RefInChain ar1 lo hi r) :
    RefInChain ar2 lo hi r := by
  induction hrc with
  | @head p hi hp1 hp2 hp3 hp4 =>
    have hp0 : ar2[p]?.getD 0#32 = ar1[p]?.getD 0#32 := by
      rw [heq p (Nat.le_refl _) (by omega)]
    have hp2' : ar2[p + 2]?.getD 0#32 = ar1[p + 2]?.getD 0#32 := by
      rw [heq (p + 2) (by omega) (by omega)]
    exact RefInChain.head hp1 (by rw [hp0]; exact hp2) (by rw [hp2']; exact hp3)
      (by rw [hp2']; exact hp4)
  | @tail p hi r hp1 hp2 hp3 hp4 _ ih =>
    have hp0 : ar2[p]?.getD 0#32 = ar1[p]?.getD 0#32 := by
      rw [heq p (Nat.le_refl _) (by omega)]
    have hp2' : ar2[p + 2]?.getD 0#32 = ar1[p + 2]?.getD 0#32 := by
      rw [heq (p + 2) (by omega) (by omega)]
    exact RefInChain.tail hp1 (by rw [hp0]; exact hp2) (by rw [hp2']; exact hp3)
      (by rw [hp2']; exact hp4)
      (by rw [hp2']; exact ih (fun i hi1 hi2 => heq i (by omega) hi2))

theorem refInChain_bounds {ar : List (BitVec 32)} {lo hi r : Nat}
    (hrc : RefInChain ar lo hi r) : lo ≤ r ∧ r < hi := by
  induction hrc with
  | @head p hi hp1 _ _ _ => exact ⟨Nat.le_refl _, by omega⟩
  | @tail p hi r hp1 _ _ _ _ ih => exact ⟨by omega, ih.2⟩

theorem refInChain_single {ar : List (BitVec 32)} {p hi r : Nat}
    (hsz : hi = p + 3 + (ar[p + 2]?.getD 0#32).toNat)
    (hrc : RefInChain ar p hi r) : r = p := by
  cases hrc with
  | head => rfl
  | tail _ _ _ _ hrest =>
    have hb := refInChain_bounds hrest
    omega

theorem moveRangeChain_empty_rw {ar : List (BitVec 32)} {p rw : Nat}
    (hmv : MoveRangeChain ar p p rw) : rw = 0 := by
  cases hmv with
  | empty => rfl
  | step hp1 => omega

theorem moveRangeChain_uncons {ar : List (BitVec 32)} {lo hi rw : Nat}
    (hmv : MoveRangeChain ar lo hi rw) (hlt : lo < hi) :
    ∃ rw', (ar[lo]?.getD 0#32 &&& 0x00880000#32) = 0#32 ∧
      3 ≤ (ar[lo + 2]?.getD 0#32).toNat ∧
      lo + 3 + (ar[lo + 2]?.getD 0#32).toNat ≤ hi ∧
      (if (ar[lo]?.getD 0#32 &&& 0x00400000#32) ≠ 0#32 then
        3 + (ar[lo + 2]?.getD 0#32).toNat else 0) + rw' = rw ∧
      MoveRangeChain ar (lo + 3 + (ar[lo + 2]?.getD 0#32).toNat) hi rw' := by
  cases hmv with
  | empty => exact absurd hlt (Nat.lt_irrefl _)
  | step _ hc hsz hfit hrest => exact ⟨_, hc, hsz, hfit, rfl, hrest⟩

theorem moveRangeChain_snoc_rw {ar : List (BitVec 32)} {a p p' rw rw' : Nat}
    (hmv : MoveRangeChain ar a p rw) (h3 : p + 3 ≤ p')
    (hc : (ar[p]?.getD 0#32 &&& 0x00880000#32) = 0#32)
    (hsz : 3 ≤ (ar[p + 2]?.getD 0#32).toNat)
    (hp' : p + 3 + (ar[p + 2]?.getD 0#32).toNat = p')
    (hrw' : rw + (if (ar[p]?.getD 0#32 &&& 0x00400000#32) ≠ 0#32 then
      3 + (ar[p + 2]?.getD 0#32).toNat else 0) = rw') :
    MoveRangeChain ar a p' rw' := by
  subst hrw'
  exact moveRangeChain_snoc hmv h3 hc hsz hp'

theorem moveRangeChain_rw_le {ar : List (BitVec 32)} {lo hi rw : Nat}
    (hmv : MoveRangeChain ar lo hi rw) : rw ≤ hi - lo := by
  induction hmv with
  | empty => omega
  | @step p hi rw hp1 _ _ hp4 _ ih =>
    by_cases h : (ar[p]?.getD 0#32 &&& 0x00400000#32) ≠ 0#32
    · rw [ite_eq_left h]; omega
    · rw [ite_eq_right h]; omega

theorem bv32_clear_0020_props {w : BitVec 32} (hclean : (w &&& 0x00880000#32) = 0#32) :
    ((w &&& ~~~0x00200000#32) &&& 0x00880000#32) = 0#32 ∧
    ((w &&& ~~~0x00200000#32) &&& 0x00400000#32) = (w &&& 0x00400000#32) ∧
    ((w &&& ~~~0x00200000#32) &&& 0x00200000#32) = 0#32 := by
  refine ⟨?_, ?_, ?_⟩
  · have h1 : (w &&& ~~~0x00200000#32) &&& 0x00880000#32 =
        (w &&& 0x00880000#32) &&& ~~~0x00200000#32 := by
      rw [BitVec.and_assoc, BitVec.and_comm (~~~0x00200000#32) 0x00880000#32, ← BitVec.and_assoc]
    rw [h1, hclean]; decide
  · have h1 : (w &&& ~~~0x00200000#32) &&& 0x00400000#32 =
        w &&& (~~~0x00200000#32 &&& 0x00400000#32) := BitVec.and_assoc _ _ _
    have h2 : (~~~0x00200000#32 &&& 0x00400000#32) = 0x00400000#32 := by decide
    rw [h1, h2]
  · have h1 : (w &&& ~~~0x00200000#32) &&& 0x00200000#32 =
        w &&& (~~~0x00200000#32 &&& 0x00200000#32) := BitVec.and_assoc _ _ _
    have h2 : (~~~0x00200000#32 &&& 0x00200000#32) = 0#32 := by decide
    rw [h1, h2, BitVec.and_zero]

theorem moveRangeChain_head_of_lt {ar : List (BitVec 32)} {lo hi rw : Nat}
    (hmv : MoveRangeChain ar lo hi rw) (hlt : lo < hi) : RefInChain ar lo hi lo := by
  cases hmv with
  | empty => exact absurd hlt (Nat.lt_irrefl _)
  | step hp1 hp2 hp3 hp4 => exact RefInChain.head hp1 hp2 hp3 hp4

theorem refInChain_in_prefix_or_curr {ar : List (BitVec 32)}
    {fr r dst rw1 r0 : Nat}
    (hmv_pre : MoveRangeChain ar fr r rw1)
    (hnext : ar[r]?.getD 0#32 &&& 0x00880000#32 = 0#32)
    (hsz3 : 3 ≤ (ar[r + 2]?.getD 0#32).toNat)
    (_hr_dst : r + 3 + (ar[r + 2]?.getD 0#32).toNat ≤ dst)
    (hrc : RefInChain ar fr dst r0)
    (hr0_lt : r0 < r + 3 + (ar[r + 2]?.getD 0#32).toNat) :
    RefInChain ar fr r r0 ∨ r0 = r := by
  have hmv_pre' : MoveRangeChain ar fr (r + 3 + (ar[r + 2]?.getD 0#32).toNat)
      (rw1 + if (ar[r]?.getD 0#32 &&& 0x00400000#32) ≠ 0#32 then
        3 + (ar[r + 2]?.getD 0#32).toNat else 0) :=
    moveRangeChain_snoc hmv_pre (by omega) hnext hsz3 rfl
  rcases refInChain_split hmv_pre' hrc with hin | hout
  · rcases refInChain_split hmv_pre hin with hin_r | hsingle
    · exact Or.inl hin_r
    · exact Or.inr (refInChain_single rfl hsingle)
  · have hb := refInChain_bounds hout
    omega

theorem noHitBefore_none_live {arPre : List (BitVec 32)} {vals : List (BitVec 8)}
    {rsns : List (BitVec 32)} {cv fr dst r sz : Nat}
    (hsz : (arPre[r + 2]?.getD 0#32).toNat = sz)
    (hno : ∀ k < sz, (arPre[r + 3 + k]?.getD 0#32).toNat / 2 < cv →
      vals[(arPre[r + 3 + k]?.getD 0#32).toNat]?.getD 0#8 = 1#8 →
      (rsns[(arPre[r + 3 + k]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat ≠ r) :
    ∀ v < cv, MoveLiveRsn arPre vals rsns fr dst v →
      (rsns[v]?.getD 0xFFFFFFFF#32).toNat ≠ r := by
  intro v hv hml hrs
  obtain ⟨j, hj, hlit, hval⟩ := hml.2.2.2.2
  rw [hrs] at hj hlit hval
  rw [hsz] at hj
  have hne := hno j hj (by rw [hlit]; exact hv) hval
  rw [hlit, hrs] at hne
  exact hne rfl

theorem litScan_hit_moveLiveRsn {arPre : List (BitVec 32)} {vals : List (BitVec 8)}
    {rsns : List (BitVec 32)} {fr r dst rwPre j : Nat}
    {hdr sz lit v32 : BitVec 32}
    (hmv_pre : MoveRangeChain arPre fr r rwPre)
    (hhdr : arPre[r]? = some hdr)
    (hsz : arPre[r + 2]? = some sz)
    (hclean : (hdr &&& 0x00880000#32) = 0#32)
    (hfl_ne : (hdr &&& 0x00200000#32) ≠ 0#32)
    (hsz3 : 3 ≤ sz.toNat)
    (hfit : r + 3 + sz.toNat ≤ dst)
    (hfr_r : fr ≤ r)
    (hr_dst : r < dst)
    (hj_lt : j < sz.toNat)
    (hlit_ar : arPre[r + 3 + j]? = some lit)
    (hv_nat : v32.toNat = lit.toNat / 2)
    (hb_1 : vals[lit.toNat]? = some 1#8)
    (hrs_r : (rsns[v32.toNat]?.getD 0xFFFFFFFF#32).toNat = r) :
    MoveLiveRsn arPre vals rsns fr dst v32.toNat := by
  have hclean_r : (arPre[r]?.getD 0#32 &&& 0x00880000#32) = 0#32 := by
    rw [hhdr, Option.getD_some]; exact hclean
  have hsz_r : 3 ≤ (arPre[r + 2]?.getD 0#32).toNat := by
    rw [hsz, Option.getD_some]; exact hsz3
  have hfit_r : r + 3 + (arPre[r + 2]?.getD 0#32).toNat ≤ dst := by
    rw [hsz, Option.getD_some]; exact hfit
  have hrc : RefInChain arPre fr dst r :=
    refInChain_append_left hfit_r
      (refInChain_append_right hmv_pre (RefInChain.head (by omega) hclean_r hsz_r (le_refl _)))
  refine ⟨by rw [hrs_r]; exact hfr_r, by rw [hrs_r]; exact hr_dst,
    by rw [hrs_r]; exact hrc, by rw [hrs_r, hhdr, Option.getD_some]; exact hfl_ne,
    j, by rw [hrs_r, hsz, Option.getD_some]; exact hj_lt,
    by rw [hrs_r, hlit_ar, Option.getD_some]; exact hv_nat.symm,
    by rw [hrs_r, hlit_ar, Option.getD_some, hb_1, Option.getD_some]⟩

theorem end_buf_exit_to_pass2_pre {c : FullCfg} {s : FullState}
    {arPre arCurr bufCurr rsnsCurr : List (BitVec 32)}
    {first_red dst mid blen : BitVec 64} {bufPtr : Val i64}
    {bufLen : Nat} {R : Mem 64 → Prop} {m' : Mem 64}
    (hfr_mid : first_red.toNat ≤ mid.toNat)
    (hdst_cap : dst.toNat ≤ c.arena_cap)
    (hbuf_bd : bufLen < 2 * dimacsBound)
    (hmid_blen : mid.toNat + blen.toNat = dst.toNat)
    (hblen_buf : blen.toNat ≤ bufLen)
    (har_len : arCurr.length = dst.toNat)
    (hbuf_len : bufCurr.length = bufLen)
    (hrsns_len : rsnsCurr.length = c.max_vars)
    (hmv_buf : MoveRangeChain bufCurr 0 blen.toNat blen.toNat)
    (hbuf_blk : ∀ rp, RefInChain bufCurr 0 blen.toNat rp →
      (bufCurr[rp]?.getD 0#32 &&& 0x00400000#32) ≠ 0#32 ∧
      ∃ src_c, RefInChain arPre first_red.toNat dst.toNat src_c ∧
        (arPre[src_c]?.getD 0#32 &&& 0x00400000#32) ≠ 0#32 ∧
        (arPre[src_c + 2]?.getD 0#32).toNat = (bufCurr[rp + 2]?.getD 0#32).toNat ∧
        (∀ j < (bufCurr[rp + 2]?.getD 0#32).toNat,
          bufCurr[rp + 3 + j]? = arPre[src_c + 3 + j]?) ∧
        ((bufCurr[rp]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 →
          (bufCurr[rp + 1]?.getD 0#32).toNat < s.core.cur_vars ∧
          s.core.rsns[(bufCurr[rp + 1]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32 =
            BitVec.ofNat 32 src_c ∧
          MoveLiveRsn arPre s.core.vals s.core.rsns first_red.toNat dst.toNat
            (bufCurr[rp + 1]?.getD 0#32).toNat))
    (hrsn_map : ∀ v < s.core.cur_vars,
      let r0 := s.core.rsns[v]?.getD 0xFFFFFFFF#32
      if MoveLiveRsn arPre s.core.vals s.core.rsns first_red.toNat dst.toNat v ∧
          r0.toNat < dst.toNat ∧
          (arPre[r0.toNat]?.getD 0#32 &&& 0x00400000#32) = 0#32
      then let r' := (rsnsCurr[v]?.getD 0xFFFFFFFF#32).toNat
        first_red.toNat ≤ r' ∧ r' < mid.toNat ∧ r' < 0x80000000 ∧
        RefInChain arCurr first_red.toNat mid.toNat r' ∧
        (arCurr[r' + 2]?.getD 0#32).toNat = (arPre[r0.toNat + 2]?.getD 0#32).toNat ∧
        ∀ j < (arPre[r0.toNat + 2]?.getD 0#32).toNat,
          arCurr[r' + 3 + j]? = arPre[r0.toNat + 3 + j]?
      else rsnsCurr[v]?.getD 0xFFFFFFFF#32 = r0)
    (hbuf_rsns : ∀ v < s.core.cur_vars,
      let r0 := s.core.rsns[v]?.getD 0xFFFFFFFF#32
      MoveLiveRsn arPre s.core.vals s.core.rsns first_red.toNat dst.toNat v →
      r0.toNat < dst.toNat →
      (arPre[r0.toNat]?.getD 0#32 &&& 0x00400000#32) ≠ 0#32 →
      ∃ rp, RefInChain bufCurr 0 blen.toNat rp ∧
        (bufCurr[rp]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 ∧
        bufCurr[rp + 1]?.getD 0#32 = BitVec.ofNat 32 v ∧
        (∀ rp2, RefInChain bufCurr 0 blen.toNat rp2 →
          (bufCurr[rp2]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 →
          bufCurr[rp2 + 1]?.getD 0#32 = BitVec.ofNat 32 v → rp2 = rp))
    (hm' : (array (t := i32) c.pArena arCurr ⋆ array (t := i32) bufPtr bufCurr ⋆
      FullMemArenaOut c { s with core := { s.core with rsns := rsnsCurr } } ⋆ R) m') :
    first_red.toNat ≤ mid.toNat ∧
    dst.toNat ≤ c.arena_cap ∧
    blen.toNat ≤ bufCurr.length ∧
    bufCurr.length < 2 * dimacsBound ∧
    MoveRangeChain bufCurr 0 blen.toNat blen.toNat ∧
    (∀ rp, RefInChain bufCurr 0 blen.toNat rp →
      (bufCurr[rp]?.getD 0#32 &&& 0x00400000#32) ≠ 0#32 ∧
      ∃ src_c, RefInChain arPre first_red.toNat dst.toNat src_c ∧
        (arPre[src_c]?.getD 0#32 &&& 0x00400000#32) ≠ 0#32 ∧
        (arPre[src_c + 2]?.getD 0#32).toNat = (bufCurr[rp + 2]?.getD 0#32).toNat ∧
        (∀ j < (bufCurr[rp + 2]?.getD 0#32).toNat,
          bufCurr[rp + 3 + j]? = arPre[src_c + 3 + j]?) ∧
        ((bufCurr[rp]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 →
          (bufCurr[rp + 1]?.getD 0#32).toNat < s.core.cur_vars ∧
          s.core.rsns[(bufCurr[rp + 1]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32 =
            BitVec.ofNat 32 src_c ∧
          MoveLiveRsn arPre s.core.vals s.core.rsns first_red.toNat dst.toNat
            (bufCurr[rp + 1]?.getD 0#32).toNat)) ∧
    MovePass2Inv c s arPre arCurr bufCurr rsnsCurr first_red dst bufPtr
      mid.toNat blen.toNat R (0#64, ()) m' := by
  have h0_64 : (0#64).toNat = 0 := rfl
  refine ⟨hfr_mid, hdst_cap, by omega, by omega, hmv_buf, hbuf_blk,
    Nat.zero_le _, hmid_blen, arCurr, rsnsCurr, har_len, hrsns_len, fun _ _ => rfl,
    by rw [h0_64, Nat.add_zero]; exact MoveRangeChain.empty,
    fun hbl_pos => ?_,
    fun r hr => by have hb := refInChain_bounds hr; rw [h0_64] at hb; omega,
    fun v hv => ?_, hm'⟩
  · rw [h0_64] at hbl_pos ⊢
    exact moveRangeChain_head_of_lt hmv_buf hbl_pos
  · dsimp only
    by_cases hcond : MoveLiveRsn arPre s.core.vals s.core.rsns first_red.toNat dst.toNat v ∧
        (arPre[(s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat]?.getD 0#32 &&& 0x00400000#32) ≠ 0#32
    · rw [ite_eq_left hcond]
      have hr0_lt : (s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat < dst.toNat := hcond.1.2.1
      obtain ⟨rp, hrp, hrp_fl, hrp_v, hrp_uniq⟩ := hbuf_rsns v hv hcond.1 hr0_lt hcond.2
      refine ⟨rp, hrp, hrp_fl, hrp_v, hrp_uniq, ?_⟩
      rw [h0_64, ite_eq_right (Nat.not_lt_zero _)]
      have h1 := hrsn_map v hv
      dsimp only at h1
      rw [ite_eq_right (fun h => hcond.2 h.2.2)] at h1
      exact h1
    · rw [ite_eq_right hcond]

theorem end_buf_exit_to_pass2_post {c : FullCfg} {s : FullState}
    {arPre arCurr bufCurr rsnsCurr arOut rsnsOut : List (BitVec 32)}
    {first_red dst mid blen : BitVec 64}
    (hfr_mid : first_red.toNat ≤ mid.toNat)
    (hdst_cap : dst.toNat ≤ c.arena_cap)
    (hmid_blen : mid.toNat + blen.toNat = dst.toNat)
    (hpre_curr : ∀ i < first_red.toNat, arCurr[i]? = arPre[i]?)
    (hmv_irred : MoveRangeChain arCurr first_red.toNat mid.toNat 0)
    (_hmv_buf : MoveRangeChain bufCurr 0 blen.toNat blen.toNat)
    (hirred_blk : ∀ ir, RefInChain arCurr first_red.toNat mid.toNat ir →
      (arCurr[ir]?.getD 0#32 &&& 0x00200000#32) = 0#32 ∧
      ∃ src, RefInChain arPre first_red.toNat dst.toNat src ∧
        (arPre[src]?.getD 0#32 &&& 0x00400000#32) = 0#32 ∧
        (arPre[src + 2]?.getD 0#32).toNat = (arCurr[ir + 2]?.getD 0#32).toNat ∧
        ∀ j < (arPre[src + 2]?.getD 0#32).toNat, arCurr[ir + 3 + j]? = arPre[src + 3 + j]?)
    (hbuf_blk : ∀ rp, RefInChain bufCurr 0 blen.toNat rp →
      (bufCurr[rp]?.getD 0#32 &&& 0x00400000#32) ≠ 0#32 ∧
      ∃ src_c, RefInChain arPre first_red.toNat dst.toNat src_c ∧
        (arPre[src_c]?.getD 0#32 &&& 0x00400000#32) ≠ 0#32 ∧
        (arPre[src_c + 2]?.getD 0#32).toNat = (bufCurr[rp + 2]?.getD 0#32).toNat ∧
        (∀ j < (bufCurr[rp + 2]?.getD 0#32).toNat,
          bufCurr[rp + 3 + j]? = arPre[src_c + 3 + j]?) ∧
        ((bufCurr[rp]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 →
          (bufCurr[rp + 1]?.getD 0#32).toNat < s.core.cur_vars ∧
          s.core.rsns[(bufCurr[rp + 1]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32 =
            BitVec.ofNat 32 src_c ∧
          MoveLiveRsn arPre s.core.vals s.core.rsns first_red.toNat dst.toNat
            (bufCurr[rp + 1]?.getD 0#32).toNat))
    (hrsn_map : ∀ v < s.core.cur_vars,
      let r0 := s.core.rsns[v]?.getD 0xFFFFFFFF#32
      if MoveLiveRsn arPre s.core.vals s.core.rsns first_red.toNat dst.toNat v ∧
          r0.toNat < dst.toNat ∧
          (arPre[r0.toNat]?.getD 0#32 &&& 0x00400000#32) = 0#32
      then let r' := (rsnsCurr[v]?.getD 0xFFFFFFFF#32).toNat
        first_red.toNat ≤ r' ∧ r' < mid.toNat ∧ r' < 0x80000000 ∧
        RefInChain arCurr first_red.toNat mid.toNat r' ∧
        (arCurr[r' + 2]?.getD 0#32).toNat = (arPre[r0.toNat + 2]?.getD 0#32).toNat ∧
        ∀ j < (arPre[r0.toNat + 2]?.getD 0#32).toNat,
          arCurr[r' + 3 + j]? = arPre[r0.toNat + 3 + j]?
      else rsnsCurr[v]?.getD 0xFFFFFFFF#32 = r0)
    (hp2_pre : ∀ i < mid.toNat, arOut[i]? = arCurr[i]?)
    (hp2_mv : MoveRangeChain arOut mid.toNat (mid.toNat + blen.toNat) blen.toNat)
    (hp2_blk : ∀ r, RefInChain arOut mid.toNat (mid.toNat + blen.toNat) r →
      (arOut[r]?.getD 0#32 &&& 0x00200000#32) = 0#32 ∧
      arOut[r + 1]? = some 2#32 ∧
      ∃ rp, RefInChain bufCurr 0 blen.toNat rp ∧ r = mid.toNat + rp ∧
        (bufCurr[rp + 2]?.getD 0#32).toNat = (arOut[r + 2]?.getD 0#32).toNat ∧
        ∀ j < (arOut[r + 2]?.getD 0#32).toNat, arOut[r + 3 + j]? = bufCurr[rp + 3 + j]?)
    (hp2_rsn : ∀ v < s.core.cur_vars,
      let r0 := s.core.rsns[v]?.getD 0xFFFFFFFF#32
      if MoveLiveRsn arPre s.core.vals s.core.rsns first_red.toNat dst.toNat v ∧
          (arPre[r0.toNat]?.getD 0#32 &&& 0x00400000#32) ≠ 0#32
      then ∃ rp, RefInChain bufCurr 0 blen.toNat rp ∧
          (bufCurr[rp]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 ∧
          bufCurr[rp + 1]?.getD 0#32 = BitVec.ofNat 32 v ∧
          (∀ rp2, RefInChain bufCurr 0 blen.toNat rp2 →
            (bufCurr[rp2]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 →
            bufCurr[rp2 + 1]?.getD 0#32 = BitVec.ofNat 32 v → rp2 = rp) ∧
          let r' := (rsnsOut[v]?.getD 0xFFFFFFFF#32).toNat
          r' = mid.toNat + rp ∧ r' < dst.toNat ∧ r' < 0x80000000 ∧
          RefInChain arOut mid.toNat (mid.toNat + blen.toNat) r' ∧
          (arOut[r' + 2]?.getD 0#32).toNat = (bufCurr[rp + 2]?.getD 0#32).toNat ∧
          ∀ j < (bufCurr[rp + 2]?.getD 0#32).toNat, arOut[r' + 3 + j]? = bufCurr[rp + 3 + j]?
      else rsnsOut[v]?.getD 0xFFFFFFFF#32 = rsnsCurr[v]?.getD 0xFFFFFFFF#32) :
    (∀ i < first_red.toNat, arOut[i]? = arPre[i]?) ∧
    MoveRangeChain arOut first_red.toNat mid.toNat 0 ∧
    MoveRangeChain arOut mid.toNat dst.toNat (dst.toNat - mid.toNat) ∧
    (∀ r, RefInChain arOut first_red.toNat mid.toNat r ∨ RefInChain arOut mid.toNat dst.toNat r →
      (arOut[r]?.getD 0#32 &&& 0x00200000#32) = 0#32 ∧
      (mid.toNat ≤ r → arOut[r + 1]? = some 2#32) ∧
      ∃ src, RefInChain arPre first_red.toNat dst.toNat src ∧
        (arPre[src + 2]?.getD 0#32).toNat = (arOut[r + 2]?.getD 0#32).toNat ∧
        ∀ j < (arOut[r + 2]?.getD 0#32).toNat, arOut[r + 3 + j]? = arPre[src + 3 + j]?) ∧
    (∀ v < s.core.cur_vars,
      let r0 := s.core.rsns[v]?.getD 0xFFFFFFFF#32
      if first_red.toNat ≤ r0.toNat ∧ r0.toNat < dst.toNat ∧
          RefInChain arPre first_red.toNat dst.toNat r0.toNat ∧
          (arPre[r0.toNat]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 ∧
          ∃ j, j < (arPre[r0.toNat + 2]?.getD 0#32).toNat ∧
            let lit := (arPre[r0.toNat + 3 + j]?.getD 0#32).toNat
            lit / 2 = v ∧ s.core.vals[lit]?.getD 0#8 = 1#8
      then let r' := (rsnsOut[v]?.getD 0xFFFFFFFF#32).toNat
        first_red.toNat ≤ r' ∧ r' < dst.toNat ∧ r' < 0x80000000 ∧
        (RefInChain arOut first_red.toNat mid.toNat r' ∨
          RefInChain arOut mid.toNat dst.toNat r') ∧
        (arOut[r' + 2]?.getD 0#32).toNat = (arPre[r0.toNat + 2]?.getD 0#32).toNat ∧
        ∀ j < (arPre[r0.toNat + 2]?.getD 0#32).toNat,
          arOut[r' + 3 + j]? = arPre[r0.toNat + 3 + j]?
      else rsnsOut[v]?.getD 0xFFFFFFFF#32 = r0) := by
  have hmv_irred_out : MoveRangeChain arOut first_red.toNat mid.toNat 0 :=
    moveRangeChain_congr_out (fun i _ hi => hp2_pre i hi) hmv_irred
  have hmv_red_out : MoveRangeChain arOut mid.toNat dst.toNat (dst.toNat - mid.toNat) := by
    have hbl_eq : blen.toNat = dst.toNat - mid.toNat := by omega
    rwa [hmid_blen, hbl_eq] at hp2_mv
  refine ⟨fun i hi => by rw [hp2_pre i (by omega)]; exact hpre_curr i hi,
    hmv_irred_out, hmv_red_out, fun r hr => ?_, fun v hv => ?_⟩
  · rcases hr with hr_irred | hr_red
    · have hr_b := refInChain_bounds hr_irred
      have hr_old : RefInChain arCurr first_red.toNat mid.toNat r :=
        refInChain_congr_out (fun i _ hi => (hp2_pre i hi).symm) hr_irred
      have hr_fit := (refInChain_of_moveRangeChain hmv_irred hr_old).2.2.2
      obtain ⟨h0, src, hsrc, _, hsz_s, hcp_s⟩ := hirred_blk r hr_old
      have heq2 : arOut[r + 2]? = arCurr[r + 2]? := hp2_pre (r + 2) (by omega)
      refine ⟨by rw [hp2_pre r hr_b.2]; exact h0, fun hle => by omega,
        src, hsrc, by rw [heq2, ← hsz_s], fun j hj => ?_⟩
      rw [heq2, ← hsz_s] at hj
      rw [hp2_pre (r + 3 + j) (by omega)]; exact hcp_s j hj
    · rw [← hmid_blen] at hr_red
      obtain ⟨h0, h2, rp, hrp, rfl, hsz_rp, hcp_rp⟩ := hp2_blk r hr_red
      obtain ⟨_, src_c, hsrc_c, _, hsz_sc, hcp_sc, _⟩ := hbuf_blk rp hrp
      refine ⟨h0, fun _ => h2, src_c, hsrc_c, by rw [hsz_sc, hsz_rp], fun j hj => ?_⟩
      rw [hcp_rp j hj, hcp_sc j (by rw [hsz_rp]; exact hj)]
  · dsimp only
    by_cases hlive : MoveLiveRsn arPre s.core.vals s.core.rsns first_red.toNat dst.toNat v
    · have hlive_u := hlive; unfold MoveLiveRsn at hlive_u
      rw [ite_eq_left hlive_u]
      have hr0_lt : (s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat < dst.toNat := hlive.2.1
      by_cases hred : (arPre[(s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat]?.getD 0#32 &&&
          0x00400000#32) ≠ 0#32
      · have h1 := hp2_rsn v hv
        dsimp only at h1
        rw [ite_eq_left ⟨hlive, hred⟩] at h1
        obtain ⟨rp, hrp, hrp_fl, hrp_v, _, r'_eq, hr'_dst, hr'_31, hr'_rc, hsz_r, hcp_r⟩ := h1
        obtain ⟨_, src_c, hsrc_c, _, hsz_sc, hcp_sc, hlive_rp⟩ := hbuf_blk rp hrp
        have hrs_src : s.core.rsns[v]?.getD 0xFFFFFFFF#32 = BitVec.ofNat 32 src_c := by
          have h1 := (hlive_rp hrp_fl).2.1
          have hv_eq : (bufCurr[rp + 1]?.getD 0#32).toNat = v := by
            rw [hrp_v, bv32_ofNat_toNat (by omega)]
          rwa [hv_eq] at h1
        have hdb : dimacsBound = 2 ^ 28 := rfl
        have hcap := c.harena
        have hsc_lt : src_c < dst.toNat := (refInChain_bounds hsrc_c).2
        have hr0_eq_src : (s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat = src_c := by
          have := congrArg BitVec.toNat hrs_src
          rw [this]; exact bv32_ofNat_toNat (by omega)
        refine ⟨by omega, hr'_dst, hr'_31, Or.inr (by rwa [hmid_blen] at hr'_rc),
          by rw [hsz_r, ← hsz_sc, hr0_eq_src], fun j hj => ?_⟩
        rw [hr0_eq_src] at hj
        rw [hcp_r j (by rw [← hsz_sc]; exact hj), hcp_sc j (by rw [← hsz_sc]; exact hj),
          hr0_eq_src]
      · have hirred : (arPre[(s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat]?.getD 0#32 &&&
            0x00400000#32) = 0#32 := Classical.byContradiction fun hne => hred hne
        have hp2 := hp2_rsn v hv
        dsimp only at hp2
        rw [ite_eq_right (fun h => hred h.2)] at hp2
        have h1 := hrsn_map v hv
        dsimp only at h1
        rw [ite_eq_left ⟨hlive, hr0_lt, hirred⟩] at h1
        obtain ⟨ha, hb, hc, hd, he, hf⟩ := h1
        have h1' : (rsnsOut[v]?.getD 0xFFFFFFFF#32).toNat =
            (rsnsCurr[v]?.getD 0xFFFFFFFF#32).toNat := by
          rw [hp2]
        rw [← h1'] at ha hb hc hd he hf
        have hfit_r' := (refInChain_of_moveRangeChain hmv_irred hd).2.2.2
        refine ⟨ha, by omega, hc,
          Or.inl (refInChain_congr_out (fun i _ hi => hp2_pre i hi) hd),
          by rw [hp2_pre _ (by omega)]; exact he, fun j hj => ?_⟩
        rw [hp2_pre _ (by omega)]; exact hf j hj
    · have hlive_u : ¬ (first_red.toNat ≤ (s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat ∧
          (s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat < dst.toNat ∧
          RefInChain arPre first_red.toNat dst.toNat
            (s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat ∧
          (arPre[(s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat]?.getD 0#32 &&& 0x00200000#32) ≠
            0#32 ∧
          ∃ j, j < (arPre[(s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat + 2]?.getD 0#32).toNat ∧
            (arPre[(s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat + 3 + j]?.getD 0#32).toNat / 2 =
              v ∧
            s.core.vals[(arPre[(s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat + 3 + j]?.getD
              0#32).toNat]?.getD 0#8 = 1#8) := fun h => hlive h
      rw [ite_eq_right hlive_u]
      have hp2 := hp2_rsn v hv
      dsimp only at hp2
      rw [ite_eq_right (fun h => hlive h.1)] at hp2
      have h1 := hrsn_map v hv
      dsimp only at h1
      rw [ite_eq_right (fun h => hlive h.1)] at h1
      rw [hp2, h1]

theorem end_buf_post_to_end_post {c : FullCfg} {s : FullState}
    {arPre arOut arTail rsns' : List (BitVec 32)}
    {first_red dst : BitVec 64} {mid rw0 : Nat}
    (hfr_dst : first_red.toNat < dst.toNat)
    (hdst_cap : dst.toNat ≤ c.arena_cap)
    (harPre_def : arPre = s.core.arena.take dst.toNat)
    (harTail_len : arTail.length = c.arena_cap - dst.toNat)
    (harOut_len : arOut.length = dst.toNat)
    (hmid_dst : mid ≤ dst.toNat)
    (hpre_out : ∀ i < first_red.toNat, arOut[i]? = arPre[i]?)
    (hmv_irred : MoveRangeChain arOut first_red.toNat mid 0)
    (hmv_red : MoveRangeChain arOut mid dst.toNat (dst.toNat - mid))
    (hblk : ∀ r, RefInChain arOut first_red.toNat mid r ∨ RefInChain arOut mid dst.toNat r →
      (arOut[r]?.getD 0#32 &&& 0x00200000#32) = 0#32 ∧
      (mid ≤ r → arOut[r + 1]? = some 2#32) ∧
      ∃ src, RefInChain arPre first_red.toNat dst.toNat src ∧
        (arPre[src + 2]?.getD 0#32).toNat = (arOut[r + 2]?.getD 0#32).toNat ∧
        ∀ j < (arOut[r + 2]?.getD 0#32).toNat, arOut[r + 3 + j]? = arPre[src + 3 + j]?)
    (hrsn : ∀ v < s.core.cur_vars,
      let r0 := s.core.rsns[v]?.getD 0xFFFFFFFF#32
      if first_red.toNat ≤ r0.toNat ∧ r0.toNat < dst.toNat ∧
          RefInChain arPre first_red.toNat dst.toNat r0.toNat ∧
          (arPre[r0.toNat]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 ∧
          ∃ j, j < (arPre[r0.toNat + 2]?.getD 0#32).toNat ∧
            let lit := (arPre[r0.toNat + 3 + j]?.getD 0#32).toNat
            lit / 2 = v ∧ s.core.vals[lit]?.getD 0#8 = 1#8
      then let r' := (rsns'[v]?.getD 0xFFFFFFFF#32).toNat
        first_red.toNat ≤ r' ∧ r' < dst.toNat ∧ r' < 0x80000000 ∧
        (RefInChain arOut first_red.toNat mid r' ∨ RefInChain arOut mid dst.toNat r') ∧
        (arOut[r' + 2]?.getD 0#32).toNat = (arPre[r0.toNat + 2]?.getD 0#32).toNat ∧
        ∀ j < (arPre[r0.toNat + 2]?.getD 0#32).toNat,
          arOut[r' + 3 + j]? = arPre[r0.toNat + 3 + j]?
      else rsns'[v]?.getD 0xFFFFFFFF#32 = r0)
    (hmv_orig : MoveRangeChain s.core.arena first_red.toNat dst.toNat rw0) :
    let ar' := arOut ++ arTail
    ar'.length = c.arena_cap ∧
    (∀ i < first_red.toNat, ar'[i]? = s.core.arena[i]?) ∧
    MoveRangeChain ar' first_red.toNat dst.toNat (dst.toNat - mid) ∧
    (∀ r, RefInChain ar' first_red.toNat dst.toNat r →
      (ar'[r]?.getD 0#32 &&& 0x00200000#32) = 0#32 ∧
      ∃ src, RefInChain s.core.arena first_red.toNat dst.toNat src ∧
        (ar'[r + 2]?.getD 0#32).toNat = (s.core.arena[src + 2]?.getD 0#32).toNat ∧
        ∀ j < (s.core.arena[src + 2]?.getD 0#32).toNat,
          ar'[r + 3 + j]? = s.core.arena[src + 3 + j]?) ∧
    (∀ v < s.core.cur_vars,
      let r0 := s.core.rsns[v]?.getD 0xFFFFFFFF#32
      if first_red.toNat ≤ r0.toNat ∧ r0.toNat < dst.toNat ∧
          RefInChain s.core.arena first_red.toNat dst.toNat r0.toNat ∧
          (s.core.arena[r0.toNat]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 ∧
          ∃ j, j < (s.core.arena[r0.toNat + 2]?.getD 0#32).toNat ∧
            let lit := (s.core.arena[r0.toNat + 3 + j]?.getD 0#32).toNat
            lit / 2 = v ∧ s.core.vals[lit]?.getD 0#8 = 1#8
      then let r' := (rsns'[v]?.getD 0xFFFFFFFF#32).toNat
        first_red.toNat ≤ r' ∧ r' < dst.toNat ∧ r' < 0x80000000 ∧
        RefInChain ar' first_red.toNat dst.toNat r' ∧
        (ar'[r' + 2]?.getD 0#32).toNat = (s.core.arena[r0.toNat + 2]?.getD 0#32).toNat ∧
        ∀ j < (s.core.arena[r0.toNat + 2]?.getD 0#32).toNat,
          ar'[r' + 3 + j]? = s.core.arena[r0.toNat + 3 + j]?
      else rsns'[v]?.getD 0xFFFFFFFF#32 = r0) := by
  intro ar'
  have har_eq : ∀ i, i < dst.toNat → ar'[i]? = arOut[i]? := fun i hi =>
    List.getElem?_append_left (by omega)
  have hpre_eq : ∀ i, i < dst.toNat → arPre[i]? = s.core.arena[i]? := fun i hi => by
    rw [harPre_def, List.getElem?_take_of_lt hi]
  have hmv_pre_orig : MoveRangeChain arPre first_red.toNat dst.toNat rw0 :=
    moveRangeChain_congr_out (lo := first_red.toNat) (fun i _ hi => hpre_eq i hi) hmv_orig
  have hmv_irred' : MoveRangeChain ar' first_red.toNat mid 0 :=
    moveRangeChain_congr_out (fun i _ hi => har_eq i (by omega)) hmv_irred
  have hmv_red' : MoveRangeChain ar' mid dst.toNat (dst.toNat - mid) :=
    moveRangeChain_congr_out (fun i _ hi => har_eq i hi) hmv_red
  have hmv_full : MoveRangeChain ar' first_red.toNat dst.toNat (dst.toNat - mid) := by
    simpa only [Nat.zero_add] using moveRangeChain_append hmv_irred' hmv_red'
  refine ⟨by rw [List.length_append, harOut_len, harTail_len]; omega,
    fun i hi => by rw [har_eq i (by omega), hpre_out i hi, hpre_eq i (by omega)],
    hmv_full, fun r hr => ?_, fun v hv => ?_⟩
  · have hr_fit := (refInChain_of_moveRangeChain hmv_full hr).2.2.2
    have hr_b := refInChain_bounds hr
    have hsplit : RefInChain arOut first_red.toNat mid r ∨
        RefInChain arOut mid dst.toNat r := by
      rcases refInChain_split hmv_irred' hr with h1 | h2
      · exact Or.inl (refInChain_congr_out (fun i _ hi => (har_eq i (by omega)).symm) h1)
      · exact Or.inr (refInChain_congr_out (fun i _ hi => (har_eq i hi).symm) h2)
    obtain ⟨h0, _, src, hsrc, hsz_s, hcp_s⟩ := hblk r hsplit
    have hsrc_fit := (refInChain_of_moveRangeChain hmv_pre_orig hsrc).2.2.2
    have har_r2 := har_eq (r + 2) (by omega)
    have hpre_s2 := hpre_eq (src + 2) (by omega)
    have hfit_out : r + 3 + (arOut[r + 2]?.getD 0#32).toNat ≤ dst.toNat := by
      rw [← har_r2]; exact hr_fit
    refine ⟨by rw [har_eq r hr_b.2]; exact h0, src,
      refInChain_congr_out (fun i _ hi => (hpre_eq i hi).symm) hsrc, ?_, fun j hj => ?_⟩
    · rw [har_r2, ← hsz_s, hpre_s2]
    · have hj' : j < (arOut[r + 2]?.getD 0#32).toNat := by
        rw [← hsz_s, hpre_s2]; exact hj
      rw [har_eq (r + 3 + j) (by omega), ← hpre_eq (src + 3 + j) (by omega)]
      exact hcp_s j hj'
  · dsimp only
    have h1 := hrsn v hv
    dsimp only at h1
    by_cases hcond : first_red.toNat ≤ (s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat ∧
        (s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat < dst.toNat ∧
        RefInChain s.core.arena first_red.toNat dst.toNat
          (s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat ∧
        (s.core.arena[(s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat]?.getD 0#32 &&&
          0x00200000#32) ≠ 0#32 ∧
        ∃ j, j < (s.core.arena[(s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat + 2]?.getD
            0#32).toNat ∧
          let lit := (s.core.arena[(s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat + 3 + j]?.getD
            0#32).toNat
          lit / 2 = v ∧ s.core.vals[lit]?.getD 0#8 = 1#8
    · have hr0_fit := (refInChain_of_moveRangeChain hmv_orig hcond.2.2.1).2.2.2
      have hcond_pre : first_red.toNat ≤ (s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat ∧
          (s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat < dst.toNat ∧
          RefInChain arPre first_red.toNat dst.toNat
            (s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat ∧
          (arPre[(s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat]?.getD 0#32 &&&
            0x00200000#32) ≠ 0#32 ∧
          ∃ j, j < (arPre[(s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat + 2]?.getD 0#32).toNat ∧
            let lit := (arPre[(s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat + 3 + j]?.getD
              0#32).toNat
            lit / 2 = v ∧ s.core.vals[lit]?.getD 0#8 = 1#8 := by
        refine ⟨hcond.1, hcond.2.1,
          refInChain_congr_out (fun i _ hi => hpre_eq i hi) hcond.2.2.1,
          by rw [hpre_eq _ hcond.2.1]; exact hcond.2.2.2.1, ?_⟩
        obtain ⟨j, hj, hlit, hval⟩ := hcond.2.2.2.2
        exact ⟨j, by rw [hpre_eq _ (by omega)]; exact hj,
          by rw [hpre_eq _ (by omega)]; exact hlit, by rw [hpre_eq _ (by omega)]; exact hval⟩
      rw [ite_eq_left hcond]
      rw [ite_eq_left hcond_pre] at h1
      obtain ⟨ha, hb, hc, hd, he, hf⟩ := h1
      have hd' : RefInChain ar' first_red.toNat dst.toNat
          (rsns'[v]?.getD 0xFFFFFFFF#32).toNat := by
        rcases hd with hd1 | hd2
        · exact refInChain_append_left hmid_dst
            (refInChain_congr_out (fun i _ hi => har_eq i (by omega)) hd1)
        · exact refInChain_append_right hmv_irred'
            (refInChain_congr_out (fun i _ hi => har_eq i hi) hd2)
      have hr'_fit := (refInChain_of_moveRangeChain hmv_full hd').2.2.2
      have har_r2 := har_eq ((rsns'[v]?.getD 0xFFFFFFFF#32).toNat + 2) (by omega)
      have hpre_r02 := hpre_eq ((s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat + 2) (by omega)
      have hfit_out : (rsns'[v]?.getD 0xFFFFFFFF#32).toNat + 3 +
          (arOut[(rsns'[v]?.getD 0xFFFFFFFF#32).toNat + 2]?.getD 0#32).toNat ≤ dst.toNat := by
        rw [← har_r2]; exact hr'_fit
      refine ⟨ha, hb, hc, hd', by rw [har_r2, he, hpre_r02], fun j hj => ?_⟩
      have hj_pre : j < (arPre[(s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat + 2]?.getD
          0#32).toNat := by
        rw [hpre_r02]; exact hj
      have hj_out : j < (arOut[(rsns'[v]?.getD 0xFFFFFFFF#32).toNat + 2]?.getD
          0#32).toNat := by
        rw [he]; exact hj_pre
      rw [har_eq _ (by omega), ← hpre_eq _ (by omega)]
      exact hf j hj_pre
    · have hcond_npre : ¬ (first_red.toNat ≤ (s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat ∧
          (s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat < dst.toNat ∧
          RefInChain arPre first_red.toNat dst.toNat
            (s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat ∧
          (arPre[(s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat]?.getD 0#32 &&&
            0x00200000#32) ≠ 0#32 ∧
          ∃ j, j < (arPre[(s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat + 2]?.getD 0#32).toNat ∧
            let lit := (arPre[(s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat + 3 + j]?.getD
              0#32).toNat
            lit / 2 = v ∧ s.core.vals[lit]?.getD 0#8 = 1#8) := by
        intro hp
        apply hcond
        have hr0_fit := (refInChain_of_moveRangeChain hmv_pre_orig hp.2.2.1).2.2.2
        refine ⟨hp.1, hp.2.1,
          refInChain_congr_out (fun i _ hi => (hpre_eq i hi).symm) hp.2.2.1,
          by rw [← hpre_eq _ hp.2.1]; exact hp.2.2.2.1, ?_⟩
        obtain ⟨j, hj, hlit, hval⟩ := hp.2.2.2.2
        exact ⟨j, by rw [← hpre_eq _ (by omega)]; exact hj,
          by rw [← hpre_eq _ (by omega)]; exact hlit,
          by rw [← hpre_eq _ (by omega)]; exact hval⟩
      rw [ite_eq_right hcond]
      rw [ite_eq_right hcond_npre] at h1
      exact h1

theorem sep_right5_swap23 {A B C D E : Mem 64 → Prop} :
    (A ⋆ (B ⋆ (C ⋆ (D ⋆ E)))) = (A ⋆ (C ⋆ (B ⋆ (D ⋆ E)))) := by
  rw [sep_comm_l B]

theorem sep_right5_swap34 {A B C D E : Mem 64 → Prop} :
    (A ⋆ (B ⋆ (C ⋆ (D ⋆ E)))) = (A ⋆ (B ⋆ (D ⋆ (C ⋆ E)))) := by
  rw [sep_comm_l C]

theorem sep_right5_swap24 {A B C D E : Mem 64 → Prop} :
    (A ⋆ (B ⋆ (C ⋆ (D ⋆ E)))) = (A ⋆ (C ⋆ (D ⋆ (B ⋆ E)))) := by
  rw [sep_comm_l B, sep_comm_l B]

theorem sep_right5_rot4_2 {A B C D E : Mem 64 → Prop} :
    (A ⋆ (B ⋆ (C ⋆ (D ⋆ E)))) = (A ⋆ (D ⋆ (B ⋆ (C ⋆ E)))) := by
  rw [sep_comm_l C, sep_comm_l B]

abbrev LitNotHitRsn (arPre rsns : List (BitVec 32)) (vals : List (BitVec 8))
    (cv rIdx idx : Nat) : Prop :=
  (arPre[idx]?.getD 0#32).toNat / 2 < cv →
    vals[(arPre[idx]?.getD 0#32).toNat]?.getD 0#8 = 1#8 →
    (rsns[(arPre[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat ≠ rIdx

theorem litNotHit_of_ge {arPre rsns : List (BitVec 32)} {vals : List (BitVec 8)}
    {cv rIdx idx : Nat} {lit v32 : BitVec 32}
    (hlit : arPre[idx]? = some lit) (hv_nat : v32.toNat = lit.toNat / 2)
    (hv_ge : ¬ v32.toNat < cv) : LitNotHitRsn arPre rsns vals cv rIdx idx := by
  intro hlt _
  rw [hlit, Option.getD_some, ← hv_nat] at hlt
  exact False.elim (hv_ge hlt)

theorem litNotHit_of_val_ne {arPre rsns : List (BitVec 32)} {vals : List (BitVec 8)}
    {cv rIdx idx : Nat} {lit : BitVec 32} {bval : BitVec 8}
    (hlit : arPre[idx]? = some lit) (hbval : vals[lit.toNat]? = some bval)
    (htri : bval = 0#8 ∨ bval = 1#8 ∨ bval = 255#8)
    (hnot_pos : ¬ BitVec.slt (BitVec.signExtend 32 (BitVec.setWidth 8 0#32))
      (BitVec.signExtend 32 bval)) : LitNotHitRsn arPre rsns vals cv rIdx idx := by
  intro _ hval1
  rw [hlit, Option.getD_some, hbval, Option.getD_some] at hval1
  exact False.elim (hnot_pos ((bv8_sgt_zero_iff bval htri).mpr hval1))

theorem litNotHit_of_rsn_ne {arPre rsns : List (BitVec 32)} {vals : List (BitVec 8)}
    {cv idx : Nat} {r : BitVec 64} {lit v32 r0 : BitVec 32}
    (hlit : arPre[idx]? = some lit) (hv_nat : v32.toNat = lit.toNat / 2)
    (hr0 : rsns[v32.toNat]? = some r0) (hne : r0.setWidth 64 ≠ r) :
    LitNotHitRsn arPre rsns vals cv r.toNat idx := by
  intro _ _ hrs_eq
  rw [hlit, Option.getD_some, ← hv_nat, hr0, Option.getD_some] at hrs_eq
  exact hne (by apply BitVec.eq_of_toNat_eq; rw [zext_toNat r0 (by decide)]; exact hrs_eq)

theorem end_buf_red_copy_step {arPre bufCurr bufC : List (BitVec 32)}
    {bufLen blen r j bj : Nat} {v : BitVec 32}
    (hbuf_len : bufC.length = bufLen) (hbj_eq : bj = blen + j) (hbj_lt : bj < bufC.length)
    (hv_eq : arPre[r + j]? = some v)
    (hpre : ∀ k < blen, bufC[k]? = bufCurr[k]?)
    (hcp : ∀ k < j, bufC[blen + k]? = arPre[r + k]?) :
    (bufC.set bj v).length = bufLen ∧
    (∀ k < blen, (bufC.set bj v)[k]? = bufCurr[k]?) ∧
    (∀ k < j + 1, (bufC.set bj v)[blen + k]? = arPre[r + k]?) := by
  refine ⟨by simp [hbuf_len], fun k hk => by rw [List.getElem?_set_ne (by omega)]; exact hpre k hk,
    fun k hk => ?_⟩
  subst hbj_eq
  by_cases hkj : k = j
  · subst hkj; rw [List.getElem?_set_self hbj_lt, hv_eq]
  · rw [List.getElem?_set_ne (by omega)]
    exact hcp k (Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hk) hkj)

theorem end_buf_irred_copy_step {arCurr arPre arC : List (BitVec 32)}
    {dstLen mid r sz3 j mj : Nat} {v : BitVec 32}
    (har_len : arC.length = dstLen) (hmj_eq : mj = mid + j) (hmj_lt : mj < arC.length)
    (hrs_lt : mj < r + sz3) (hv_eq : arPre[r + j]? = some v)
    (hpre : ∀ i < mid, arC[i]? = arCurr[i]?)
    (hsuf : ∀ i, r + sz3 ≤ i → i < dstLen → arC[i]? = arCurr[i]?)
    (hmr : ∀ i, mid + j ≤ i → i < r + sz3 → i < dstLen → arC[i]? = arPre[i]?)
    (hcp : ∀ k < j, arC[mid + k]? = arPre[r + k]?) :
    (arC.set mj v).length = dstLen ∧
    (∀ i < mid, (arC.set mj v)[i]? = arCurr[i]?) ∧
    (∀ i, r + sz3 ≤ i → i < dstLen → (arC.set mj v)[i]? = arCurr[i]?) ∧
    (∀ i, mid + (j + 1) ≤ i → i < r + sz3 → i < dstLen → (arC.set mj v)[i]? = arPre[i]?) ∧
    (∀ k < j + 1, (arC.set mj v)[mid + k]? = arPre[r + k]?) := by
  subst hmj_eq
  refine ⟨by simp [har_len],
    fun i hi => by rw [List.getElem?_set_ne (by omega)]; exact hpre i hi,
    fun i hi1 hi2 => by rw [List.getElem?_set_ne (by omega)]; exact hsuf i hi1 hi2,
    fun i hi1 hi2 hi3 => by rw [List.getElem?_set_ne (by omega)]; exact hmr i (by omega) hi2 hi3,
    fun k hk => ?_⟩
  by_cases hkj : k = j
  · subst hkj; rw [List.getElem?_set_self hmj_lt, hv_eq]
  · rw [List.getElem?_set_ne (by omega)]
    exact hcp k (Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hk) hkj)

theorem end_buf_red_clr_hdr {arPre bufCurr bufF : List (BitVec 32)}
    {s : FullState} {bufLen blen r sz3 fr dst : Nat} {hdr : BitVec 32}
    (hbf_len : bufF.length = bufLen) (hbl_lt : blen < bufF.length)
    (hclean : (hdr &&& 0x00880000#32) = 0#32) (hred : (hdr &&& 0x00400000#32) ≠ 0#32)
    (hbf_pre : ∀ k < blen, bufF[k]? = bufCurr[k]?)
    (hbf_tail : ∀ k, 2 ≤ k → k < sz3 → bufF[blen + k]? = arPre[r + k]?)
    (hno_live : ∀ v < s.core.cur_vars, MoveLiveRsn arPre s.core.vals s.core.rsns fr dst v →
      (s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat ≠ r) :
    let buf' := bufF.set blen (hdr &&& ~~~0x00200000#32)
    buf'.length = bufLen ∧
    (∀ k < blen, buf'[k]? = bufCurr[k]?) ∧
    (∀ k, 2 ≤ k → k < sz3 → buf'[blen + k]? = arPre[r + k]?) ∧
    (buf'[blen]?.getD 0#32 &&& 0x00880000#32) = 0#32 ∧
    (buf'[blen]?.getD 0#32 &&& 0x00400000#32) ≠ 0#32 ∧
    ((buf'[blen]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 →
      ∃ v, v < s.core.cur_vars ∧ buf'[blen + 1]? = some (BitVec.ofNat 32 v) ∧
        s.core.rsns[v]?.getD 0xFFFFFFFF#32 = BitVec.ofNat 32 r ∧
        MoveLiveRsn arPre s.core.vals s.core.rsns fr dst v) ∧
    ((buf'[blen]?.getD 0#32 &&& 0x00200000#32) = 0#32 →
      ∀ v < s.core.cur_vars, MoveLiveRsn arPre s.core.vals s.core.rsns fr dst v →
        (s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat ≠ r) := by
  have hcl := bv32_clear_0020_props hclean
  refine ⟨by simp [hbf_len],
    fun k hk => by rw [List.getElem?_set_ne (by omega)]; exact hbf_pre k hk,
    fun k hk1 hk2 => by rw [List.getElem?_set_ne (by omega)]; exact hbf_tail k hk1 hk2,
    by rw [List.getElem?_set_self hbl_lt, Option.getD_some]; exact hcl.1,
    by rw [List.getElem?_set_self hbl_lt, Option.getD_some, hcl.2.1]; exact hred,
    fun hne => by
      rw [List.getElem?_set_self hbl_lt, Option.getD_some] at hne
      exact absurd hcl.2.2 hne,
    fun _ => hno_live⟩

end

end LeanQbe.T.Examples.Kissat.Proof.Collect
