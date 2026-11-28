/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Src.Collect
public import LeanQbe.T.Examples.Kissat.Proof.Collect.Spec
import LeanQbe.T.Examples.Kissat.Proof.Spec.MemBridges
import LeanQbe.T.Examples.Kissat.Proof.Collect.Tactics
import LeanQbe.T.Examples.Kissat.Proof.Collect.HelpersMoveSweep
import LeanQbe.T.Examples.Kissat.Proof.Collect.HelpersMoveEnd
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.ControlComb
meta import LeanQbe.T.Logic.C0Step
meta import LeanQbe.T.Logic.C0HeadStep

/-!
# End-of-Collection Buffer-Based Move-Redundant WP (`Proof.Collect.WpMoveRed1`)

Canonical `Func.wp` proof for `full_move_red_end_buf_m6` from `Src.Collect`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Collect

open Classical
open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Collect
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Collect.Spec
open scoped FullArenaTactics M6Tactics2a

public section

private theorem val_pair_of_div2 {vals : List (BitVec 8)} {lit v : Nat}
    (hdiv : lit / 2 = v) (hval : vals[lit]?.getD 0#8 = 1#8) :
    vals[2 * v]?.getD 0#8 = 1#8 ∨ vals[2 * v + 1]?.getD 0#8 = 1#8 := by
  have hm : lit = 2 * v ∨ lit = 2 * v + 1 := by omega
  rcases hm with hm | hm
  · left; rw [← hm]; exact hval
  · right; rw [← hm]; exact hval

private def EndBufInv (c : FullCfg) (s : FullState) (arPre : List (BitVec 32))
    (first_red dst bufPtr : Val i64) (bufLen redWords : Nat) (R : Mem 64 → Prop) :
    Tup Val [i64, i64, i64] → Mem 64 → Prop
  | (r, mid, blen, ()), m =>
    mid.toNat + blen.toNat = r.toNat ∧
    first_red.toNat ≤ mid.toNat ∧
    r.toNat ≤ dst.toNat ∧
    blen.toNat ≤ redWords ∧
    ∃ arCurr bufCurr rsnsCurr : List (BitVec 32),
      arCurr.length = dst.toNat ∧
      bufCurr.length = bufLen ∧
      rsnsCurr.length = c.max_vars ∧
      (∀ i < first_red.toNat, arCurr[i]? = arPre[i]?) ∧
      (∀ i, r.toNat ≤ i → i < dst.toNat → arCurr[i]? = arPre[i]?) ∧
      MoveRangeChain arPre first_red.toNat r.toNat blen.toNat ∧
      MoveRangeChain arPre r.toNat dst.toNat (redWords - blen.toNat) ∧
      MoveRangeChain arCurr first_red.toNat mid.toNat 0 ∧
      MoveRangeChain bufCurr 0 blen.toNat blen.toNat ∧
      (∀ ir, RefInChain arCurr first_red.toNat mid.toNat ir →
        (arCurr[ir]?.getD 0#32 &&& 0x00200000#32) = 0#32 ∧
        ∃ src, RefInChain arPre first_red.toNat r.toNat src ∧
          (arPre[src]?.getD 0#32 &&& 0x00400000#32) = 0#32 ∧
          (arPre[src + 2]?.getD 0#32).toNat = (arCurr[ir + 2]?.getD 0#32).toNat ∧
          ∀ j < (arPre[src + 2]?.getD 0#32).toNat, arCurr[ir + 3 + j]? = arPre[src + 3 + j]?) ∧
      (∀ rp, RefInChain bufCurr 0 blen.toNat rp →
        (bufCurr[rp]?.getD 0#32 &&& 0x00400000#32) ≠ 0#32 ∧
        ∃ src_c, RefInChain arPre first_red.toNat r.toNat src_c ∧
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
      (∀ v < s.core.cur_vars,
        let r0 := s.core.rsns[v]?.getD 0xFFFFFFFF#32
        if MoveLiveRsn arPre s.core.vals s.core.rsns first_red.toNat dst.toNat v ∧
            r0.toNat < r.toNat ∧
            (arPre[r0.toNat]?.getD 0#32 &&& 0x00400000#32) = 0#32
        then let r' := (rsnsCurr[v]?.getD 0xFFFFFFFF#32).toNat
          first_red.toNat ≤ r' ∧ r' < mid.toNat ∧ r' < 0x80000000 ∧
          RefInChain arCurr first_red.toNat mid.toNat r' ∧
          (arCurr[r' + 2]?.getD 0#32).toNat = (arPre[r0.toNat + 2]?.getD 0#32).toNat ∧
          ∀ j < (arPre[r0.toNat + 2]?.getD 0#32).toNat,
            arCurr[r' + 3 + j]? = arPre[r0.toNat + 3 + j]?
        else rsnsCurr[v]?.getD 0xFFFFFFFF#32 = r0) ∧
      (∀ v < s.core.cur_vars,
        let r0 := s.core.rsns[v]?.getD 0xFFFFFFFF#32
        MoveLiveRsn arPre s.core.vals s.core.rsns first_red.toNat dst.toNat v →
        r0.toNat < r.toNat →
        (arPre[r0.toNat]?.getD 0#32 &&& 0x00400000#32) ≠ 0#32 →
        ∃ rp, RefInChain bufCurr 0 blen.toNat rp ∧
          (bufCurr[rp]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 ∧
          bufCurr[rp + 1]?.getD 0#32 = BitVec.ofNat 32 v ∧
          (∀ rp2, RefInChain bufCurr 0 blen.toNat rp2 →
            (bufCurr[rp2]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 →
            bufCurr[rp2 + 1]?.getD 0#32 = BitVec.ofNat 32 v → rp2 = rp)) ∧
      (array (t := i32) c.pArena arCurr ⋆ array (t := i32) bufPtr bufCurr ⋆
        FullMemArenaOut c { s with core := { s.core with rsns := rsnsCurr } } ⋆ R) m

private theorem end_buf_red_step_inv {c : FullCfg} {s : FullState}
    {arPre arCurr bufCurr buf' rsnsCurr : List (BitVec 32)}
    {first_red r mid dst blen : BitVec 64} {bufPtr : Val i64}
    {bufLen redWords rwRem : Nat} {R : Mem 64 → Prop} {m' : Mem 64}
    (huniq : MoveRedRsnUnique arPre s.core.vals s.core.rsns s.core.cur_vars
      first_red.toNat dst.toNat)
    (hcv_le : s.core.cur_vars ≤ c.max_vars)
    (hdst_cap : dst.toNat ≤ c.arena_cap)
    (_hrw_buf : redWords ≤ bufLen)
    (hmid_blen : mid.toNat + blen.toNat = r.toNat)
    (hfr_mid : first_red.toNat ≤ mid.toNat)
    (_hblen_le : blen.toNat ≤ redWords)
    (har_len : arCurr.length = dst.toNat)
    (_hbuf_len : bufCurr.length = bufLen)
    (hrsns_len : rsnsCurr.length = c.max_vars)
    (hpre : ∀ i < first_red.toNat, arCurr[i]? = arPre[i]?)
    (hsuf : ∀ i, r.toNat ≤ i → i < dst.toNat → arCurr[i]? = arPre[i]?)
    (hmv_pre : MoveRangeChain arPre first_red.toNat r.toNat blen.toNat)
    (hmv_irred : MoveRangeChain arCurr first_red.toNat mid.toNat 0)
    (hmv_buf : MoveRangeChain bufCurr 0 blen.toNat blen.toNat)
    (hirred_blk : ∀ ir, RefInChain arCurr first_red.toNat mid.toNat ir →
      (arCurr[ir]?.getD 0#32 &&& 0x00200000#32) = 0#32 ∧
      ∃ src, RefInChain arPre first_red.toNat r.toNat src ∧
        (arPre[src]?.getD 0#32 &&& 0x00400000#32) = 0#32 ∧
        (arPre[src + 2]?.getD 0#32).toNat = (arCurr[ir + 2]?.getD 0#32).toNat ∧
        ∀ j < (arPre[src + 2]?.getD 0#32).toNat, arCurr[ir + 3 + j]? = arPre[src + 3 + j]?)
    (hbuf_blk : ∀ rp, RefInChain bufCurr 0 blen.toNat rp →
      (bufCurr[rp]?.getD 0#32 &&& 0x00400000#32) ≠ 0#32 ∧
      ∃ src_c, RefInChain arPre first_red.toNat r.toNat src_c ∧
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
          r0.toNat < r.toNat ∧
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
      r0.toNat < r.toNat →
      (arPre[r0.toNat]?.getD 0#32 &&& 0x00400000#32) ≠ 0#32 →
      ∃ rp, RefInChain bufCurr 0 blen.toNat rp ∧
        (bufCurr[rp]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 ∧
        bufCurr[rp + 1]?.getD 0#32 = BitVec.ofNat 32 v ∧
        (∀ rp2, RefInChain bufCurr 0 blen.toNat rp2 →
          (bufCurr[rp2]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 →
          bufCurr[rp2 + 1]?.getD 0#32 = BitVec.ofNat 32 v → rp2 = rp))
    {hdr sz : BitVec 32}
    (hhdr : arPre[r.toNat]? = some hdr)
    (hsz : arPre[r.toNat + 2]? = some sz)
    (hclean : (hdr &&& 0x00880000#32) = 0#32)
    (hred : (hdr &&& 0x00400000#32) ≠ 0#32)
    (hsz3 : 3 ≤ sz.toNat)
    (hfit : r.toNat + 3 + sz.toNat ≤ dst.toNat)
    (hmv_rem' : MoveRangeChain arPre (r.toNat + (3 + sz.toNat)) dst.toNat rwRem)
    (hrw_eq : blen.toNat + (3 + sz.toNat) + rwRem = redWords)
    (hbuf'_len : buf'.length = bufLen)
    (hbuf'_pre : ∀ k < blen.toNat, buf'[k]? = bufCurr[k]?)
    (hbuf'_tail : ∀ k, 2 ≤ k → k < 3 + sz.toNat →
      buf'[blen.toNat + k]? = arPre[r.toNat + k]?)
    (hbuf'_hdr_clean : (buf'[blen.toNat]?.getD 0#32 &&& 0x00880000#32) = 0#32)
    (hbuf'_hdr_red : (buf'[blen.toNat]?.getD 0#32 &&& 0x00400000#32) ≠ 0#32)
    (hbuf'_live : (buf'[blen.toNat]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 →
      ∃ v, v < s.core.cur_vars ∧
        buf'[blen.toNat + 1]? = some (BitVec.ofNat 32 v) ∧
        s.core.rsns[v]?.getD 0xFFFFFFFF#32 = BitVec.ofNat 32 r.toNat ∧
        MoveLiveRsn arPre s.core.vals s.core.rsns first_red.toNat dst.toNat v)
    (hbuf'_none : (buf'[blen.toNat]?.getD 0#32 &&& 0x00200000#32) = 0#32 →
      ∀ v < s.core.cur_vars,
        MoveLiveRsn arPre s.core.vals s.core.rsns first_red.toNat dst.toNat v →
        (s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat ≠ r.toNat)
    (hm' : (array (t := i32) c.pArena arCurr ⋆ array (t := i32) bufPtr buf' ⋆
      FullMemArenaOut c { s with core := { s.core with rsns := rsnsCurr } } ⋆ R) m') :
    EndBufInv c s arPre first_red dst bufPtr bufLen redWords R
      ⟨r + (3 + sz.setWidth 64), mid, blen + (3 + sz.setWidth 64), ()⟩ m' := by
  have hdb : dimacsBound = 2 ^ 28 := rfl
  have har_cap : c.arena_cap < 2 * dimacsBound := c.harena
  have hmax : c.max_vars < 2 * dimacsBound := c.hmaxv
  have hclen_eq : (3 + sz.setWidth 64).toNat = 3 + sz.toNat := bv64_add3_zext_toNat sz
  have hr_eq : (r + (3 + sz.setWidth 64)).toNat = r.toNat + 3 + sz.toNat := by
    rw [BitVec.toNat_add, hclen_eq, Nat.mod_eq_of_lt (by omega), Nat.add_assoc]
  have hblen_eq : (blen + (3 + sz.setWidth 64)).toNat = blen.toNat + 3 + sz.toNat := by
    rw [BitVec.toNat_add, hclen_eq, Nat.mod_eq_of_lt (by omega), Nat.add_assoc]
  have hhdr_d : arPre[r.toNat]?.getD 0#32 = hdr := by rw [hhdr, Option.getD_some]
  have hsz_d : (arPre[r.toNat + 2]?.getD 0#32).toNat = sz.toNat := by
    rw [hsz, Option.getD_some]
  have hclean_r : (arPre[r.toNat]?.getD 0#32 &&& 0x00880000#32) = 0#32 := by
    rw [hhdr_d]; exact hclean
  have hred_r : (arPre[r.toNat]?.getD 0#32 &&& 0x00400000#32) ≠ 0#32 := by
    rw [hhdr_d]; exact hred
  have hmv_pre' : MoveRangeChain arPre first_red.toNat (r.toNat + 3 + sz.toNat)
      (blen.toNat + 3 + sz.toNat) :=
    moveRangeChain_snoc_rw hmv_pre (by omega) hclean_r
      (by rw [hsz_d]; exact hsz3) (by rw [hsz_d])
      (by rw [hhdr_d, hsz_d, ite_eq_left hred]; omega)
  have hbuf'_pre_m := moveRangeChain_congr_out
    (fun i _ hi => hbuf'_pre i hi) hmv_buf
  have hbuf'_2 : buf'[blen.toNat + 2]? = some sz := by
    rw [hbuf'_tail 2 (by omega) (by omega), hsz]
  have hbuf'_sz : (buf'[blen.toNat + 2]?.getD 0#32).toNat = sz.toNat := by
    rw [hbuf'_2, Option.getD_some]
  have hmv_buf' : MoveRangeChain buf' 0 (blen.toNat + 3 + sz.toNat)
      (blen.toNat + 3 + sz.toNat) :=
    moveRangeChain_snoc_rw hbuf'_pre_m (by omega) hbuf'_hdr_clean
      (by rw [hbuf'_sz]; exact hsz3) (by rw [hbuf'_sz])
      (by rw [hbuf'_sz, ite_eq_left hbuf'_hdr_red]; omega)
  refine ⟨by rw [hr_eq, hblen_eq]; omega, hfr_mid, by rw [hr_eq]; omega,
    by rw [hblen_eq]; omega, arCurr, buf', rsnsCurr, har_len, hbuf'_len, hrsns_len, hpre,
    fun i hi1 hi2 => hsuf i (by rw [hr_eq] at hi1; omega) hi2,
    by rw [hr_eq, hblen_eq]; exact hmv_pre', ?_, hmv_irred,
    by rw [hblen_eq]; exact hmv_buf', fun ir hir => ?_, fun rp hrp => ?_,
    fun v hv => ?_, fun v hv hlive hr0_lt hr0_red => ?_, hm'⟩
  · rw [hr_eq, hblen_eq]
    have hrem_eq : redWords - (blen.toNat + 3 + sz.toNat) = rwRem := by omega
    rw [hrem_eq]; simpa only [Nat.add_assoc] using hmv_rem'
  · obtain ⟨h0, src, hsrc, hni, hsz_s, hcp_s⟩ := hirred_blk ir hir
    exact ⟨h0, src, refInChain_append_left (by rw [hr_eq]; omega) hsrc, hni, hsz_s, hcp_s⟩
  · rw [hblen_eq] at hrp
    rw [hr_eq]
    rcases refInChain_split hbuf'_pre_m hrp with hrp_pre | hrp_new
    · have hrp_b := refInChain_bounds hrp_pre
      have hrp_old : RefInChain bufCurr 0 blen.toNat rp :=
        refInChain_congr_out (fun i _ hi => (hbuf'_pre i hi).symm) hrp_pre
      obtain ⟨hr1, src_c, hsrc, hsrc_red, hsrc_sz, hsrc_lits, hsrc_live⟩ :=
        hbuf_blk rp hrp_old
      have hfit_rp := (refInChain_of_moveRangeChain hmv_buf hrp_old).2.2.2
      have heq_rp0 : buf'[rp]? = bufCurr[rp]? := hbuf'_pre rp hrp_b.2
      have heq_rp1 : buf'[rp + 1]? = bufCurr[rp + 1]? :=
        hbuf'_pre (rp + 1) (by omega)
      have heq_rp2 : buf'[rp + 2]? = bufCurr[rp + 2]? :=
        hbuf'_pre (rp + 2) (by omega)
      refine ⟨by rw [heq_rp0]; exact hr1, src_c,
        refInChain_append_left (by omega) hsrc, hsrc_red,
        by rw [heq_rp2]; exact hsrc_sz, fun j hj => ?_, fun hlive_rp => ?_⟩
      · rw [heq_rp2] at hj
        rw [hbuf'_pre (rp + 3 + j) (by omega)]; exact hsrc_lits j hj
      · rw [heq_rp0] at hlive_rp
        rw [heq_rp1]
        exact hsrc_live hlive_rp
    · have hrp_eq : rp = blen.toNat := refInChain_single (by rw [hbuf'_sz]) hrp_new
      subst hrp_eq
      refine ⟨hbuf'_hdr_red, r.toNat, ?_, hred_r, by rw [hsz_d, hbuf'_sz],
        fun j hj => ?_, fun hlive_rp => ?_⟩
      · exact refInChain_append_right hmv_pre
          (RefInChain.head (by omega) hclean_r (by rw [hsz_d]; exact hsz3)
            (by rw [hsz_d]; omega))
      · rw [hbuf'_sz] at hj
        simp only [Nat.add_assoc]
        exact hbuf'_tail (3 + j) (by omega) (by omega)
      · obtain ⟨v, hv, hv1, hrs, hml⟩ := hbuf'_live hlive_rp
        have hv1_d : buf'[blen.toNat + 1]?.getD 0#32 = BitVec.ofNat 32 v := by
          rw [hv1, Option.getD_some]
        rw [hv1_d, bv32_ofNat_toNat (by omega)]
        exact ⟨hv, hrs, hml⟩
  · dsimp only
    rw [hr_eq]
    by_cases hcond : MoveLiveRsn arPre s.core.vals s.core.rsns first_red.toNat dst.toNat v ∧
        (s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat < r.toNat + 3 + sz.toNat ∧
        (arPre[(s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat]?.getD 0#32 &&& 0x00400000#32) = 0#32
    · have hr0_lt_r : (s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat < r.toNat := by
        rcases refInChain_in_prefix_or_curr hmv_pre hclean_r (by rw [hsz_d]; exact hsz3)
          (by rw [hsz_d]; omega) hcond.1.2.2.1 (by rw [hsz_d]; exact hcond.2.1) with h1 | h2
        · exact (refInChain_bounds h1).2
        · exfalso; rw [h2] at hcond; exact hred_r hcond.2.2
      have h1 := hrsn_map v hv
      dsimp only at h1
      rw [ite_eq_left ⟨hcond.1, hr0_lt_r, hcond.2.2⟩] at h1
      rw [ite_eq_left hcond]; exact h1
    · have hcond_old : ¬ (MoveLiveRsn arPre s.core.vals s.core.rsns first_red.toNat dst.toNat v ∧
          (s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat < r.toNat ∧
          (arPre[(s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat]?.getD 0#32 &&& 0x00400000#32) =
            0#32) :=
        fun h => hcond ⟨h.1, by omega, h.2.2⟩
      have h1 := hrsn_map v hv
      dsimp only at h1
      rw [ite_eq_right hcond_old] at h1
      rw [ite_eq_right hcond]; exact h1
  · rw [hr_eq, hblen_eq] at *
    rcases refInChain_in_prefix_or_curr hmv_pre hclean_r (by rw [hsz_d]; exact hsz3)
        (by rw [hsz_d]; omega) hlive.2.2.1 (by rw [hsz_d]; exact hr0_lt) with h_in_pre | h_eq_r
    · have hr0_lt_r : (s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat < r.toNat :=
        (refInChain_bounds h_in_pre).2
      obtain ⟨rp, hrp, hrp_fl, hrp_v, hrp_uniq⟩ := hbuf_rsns v hv hlive hr0_lt_r hr0_red
      have hrp_fit := (refInChain_of_moveRangeChain hmv_buf hrp).2.2.2
      have hrp_in : RefInChain buf' 0 blen.toNat rp :=
        refInChain_congr_out (fun i _ hi => hbuf'_pre i hi) hrp
      refine ⟨rp, refInChain_append_left (by omega) hrp_in,
        by rw [hbuf'_pre rp (by omega)]; exact hrp_fl,
        by rw [hbuf'_pre (rp + 1) (by omega)]; exact hrp_v, fun rp2 hrp2 hfl2 hv2 => ?_⟩
      rcases refInChain_split hbuf'_pre_m hrp2 with hrp2_pre | hrp2_new
      · have hrp2_old := refInChain_congr_out (fun i _ hi => (hbuf'_pre i hi).symm) hrp2_pre
        have hrp2_b := refInChain_bounds hrp2_pre
        have hrp2_fit := (refInChain_of_moveRangeChain hmv_buf hrp2_old).2.2.2
        exact hrp_uniq rp2 hrp2_old
          (by rw [← hbuf'_pre rp2 hrp2_b.2]; exact hfl2)
          (by rw [← hbuf'_pre (rp2 + 1) (by omega)]; exact hv2)
      · have hrp2_eq : rp2 = blen.toNat :=
          refInChain_single (by rw [hbuf'_sz]) hrp2_new
        subst hrp2_eq
        exfalso
        obtain ⟨v2, hv2_lt, hv2_1, hrs_v2, _⟩ := hbuf'_live hfl2
        rw [hv2_1, Option.getD_some] at hv2
        have hv_eq : v2 = v := by
          have := congrArg BitVec.toNat hv2
          rw [bv32_ofNat_toNat (by omega), bv32_ofNat_toNat (by omega)] at this
          exact this
        rw [hv_eq] at hrs_v2
        have hrs_nat := congrArg BitVec.toNat hrs_v2
        rw [bv32_ofNat_toNat (by omega)] at hrs_nat
        omega
    · have hfl_blen : (buf'[blen.toNat]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 := by
        intro hzero
        exact hbuf'_none hzero v hv hlive h_eq_r
      obtain ⟨v1, hv1, hv1_1, hrs_v1, hml_v1⟩ := hbuf'_live hfl_blen
      have hv_eq : v1 = v := by
        rcases hml_v1.2.2.2.2 with ⟨j1, _, hlit1, hval1⟩
        rcases hlive.2.2.2.2 with ⟨j2, _, hlit2, hval2⟩
        have hpair1 := val_pair_of_div2 hlit1 hval1
        have hpair2 := val_pair_of_div2 hlit2 hval2
        have hrs1_n : (s.core.rsns[v1]?.getD 0xFFFFFFFF#32).toNat = r.toNat := by
          rw [hrs_v1, bv32_ofNat_toNat (by omega)]
        exact huniq r.toNat (Nat.le_trans hfr_mid (by omega)) (by omega) v1 v hv1 hv hpair1 hpair2
          hrs1_n h_eq_r
      subst hv_eq
      refine ⟨blen.toNat, refInChain_append_right hbuf'_pre_m
          (RefInChain.head (by omega) hbuf'_hdr_clean
            (by rw [hbuf'_sz]; exact hsz3) (by rw [hbuf'_sz]; omega)),
        hfl_blen, by rw [hv1_1, Option.getD_some], fun rp2 hrp2 hfl2 hv2 => ?_⟩
      rcases refInChain_split hbuf'_pre_m hrp2 with hrp2_pre | hrp2_new
      · exfalso
        have hrp2_b := refInChain_bounds hrp2_pre
        have hrp2_old := refInChain_congr_out (fun i _ hi => (hbuf'_pre i hi).symm) hrp2_pre
        obtain ⟨_, src2, hsrc2, _, _, _, hlive2⟩ := hbuf_blk rp2 hrp2_old
        have hsrc2_b := refInChain_bounds hsrc2
        have hrp2_fit := (refInChain_of_moveRangeChain hmv_buf hrp2_old).2.2.2
        have hfl2' : (bufCurr[rp2]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 := by
          rw [← hbuf'_pre rp2 hrp2_b.2]; exact hfl2
        obtain ⟨_, hrs2, _⟩ := hlive2 hfl2'
        have hv2_eq : (bufCurr[rp2 + 1]?.getD 0#32).toNat = v1 := by
          rw [← hbuf'_pre (rp2 + 1) (by omega), hv2, bv32_ofNat_toNat (by omega)]
        rw [hv2_eq] at hrs2
        have hrs2_n := congrArg BitVec.toNat hrs2
        rw [bv32_ofNat_toNat (by omega)] at hrs2_n
        omega
      · exact refInChain_single (by rw [hbuf'_sz]) hrp2_new

private theorem end_buf_irred_step_inv {c : FullCfg} {s : FullState}
    {arPre arCurr ar' bufCurr rsnsCurr rsns' : List (BitVec 32)}
    {first_red r mid dst blen : BitVec 64} {bufPtr : Val i64}
    {bufLen redWords rwRem : Nat} {R : Mem 64 → Prop} {m' : Mem 64}
    (huniq : MoveRedRsnUnique arPre s.core.vals s.core.rsns s.core.cur_vars
      first_red.toNat dst.toNat)
    (hcv_le : s.core.cur_vars ≤ c.max_vars)
    (hdst_cap : dst.toNat ≤ c.arena_cap)
    (hmid_blen : mid.toNat + blen.toNat = r.toNat)
    (hfr_mid : first_red.toNat ≤ mid.toNat)
    (hblen_le : blen.toNat ≤ redWords)
    (har_len : arCurr.length = dst.toNat)
    (hbuf_len : bufCurr.length = bufLen)
    (hrsns_len : rsnsCurr.length = c.max_vars)
    (hpre : ∀ i < first_red.toNat, arCurr[i]? = arPre[i]?)
    (hsuf : ∀ i, r.toNat ≤ i → i < dst.toNat → arCurr[i]? = arPre[i]?)
    (hmv_pre : MoveRangeChain arPre first_red.toNat r.toNat blen.toNat)
    (hmv_irred : MoveRangeChain arCurr first_red.toNat mid.toNat 0)
    (hmv_buf : MoveRangeChain bufCurr 0 blen.toNat blen.toNat)
    (hirred_blk : ∀ ir, RefInChain arCurr first_red.toNat mid.toNat ir →
      (arCurr[ir]?.getD 0#32 &&& 0x00200000#32) = 0#32 ∧
      ∃ src, RefInChain arPre first_red.toNat r.toNat src ∧
        (arPre[src]?.getD 0#32 &&& 0x00400000#32) = 0#32 ∧
        (arPre[src + 2]?.getD 0#32).toNat = (arCurr[ir + 2]?.getD 0#32).toNat ∧
        ∀ j < (arPre[src + 2]?.getD 0#32).toNat, arCurr[ir + 3 + j]? = arPre[src + 3 + j]?)
    (hbuf_blk : ∀ rp, RefInChain bufCurr 0 blen.toNat rp →
      (bufCurr[rp]?.getD 0#32 &&& 0x00400000#32) ≠ 0#32 ∧
      ∃ src_c, RefInChain arPre first_red.toNat r.toNat src_c ∧
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
          r0.toNat < r.toNat ∧
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
      r0.toNat < r.toNat →
      (arPre[r0.toNat]?.getD 0#32 &&& 0x00400000#32) ≠ 0#32 →
      ∃ rp, RefInChain bufCurr 0 blen.toNat rp ∧
        (bufCurr[rp]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 ∧
        bufCurr[rp + 1]?.getD 0#32 = BitVec.ofNat 32 v ∧
        (∀ rp2, RefInChain bufCurr 0 blen.toNat rp2 →
          (bufCurr[rp2]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 →
          bufCurr[rp2 + 1]?.getD 0#32 = BitVec.ofNat 32 v → rp2 = rp))
    {hdr sz : BitVec 32}
    (hhdr : arPre[r.toNat]? = some hdr)
    (hsz : arPre[r.toNat + 2]? = some sz)
    (hclean : (hdr &&& 0x00880000#32) = 0#32)
    (hirred : (hdr &&& 0x00400000#32) = 0#32)
    (hsz3 : 3 ≤ sz.toNat)
    (hfit : r.toNat + 3 + sz.toNat ≤ dst.toNat)
    (hmv_rem' : MoveRangeChain arPre (r.toNat + (3 + sz.toNat)) dst.toNat rwRem)
    (hrw_eq : blen.toNat + rwRem = redWords)
    (har'_len : ar'.length = dst.toNat)
    (har'_pre : ∀ i < mid.toNat, ar'[i]? = arCurr[i]?)
    (har'_suf : ∀ i, r.toNat + (3 + sz.toNat) ≤ i → i < dst.toNat → ar'[i]? = arCurr[i]?)
    (har'_0 : ar'[mid.toNat]? = some (hdr &&& ~~~0x00200000#32))
    (har'_tail : ∀ k, 1 ≤ k → k < 3 + sz.toNat → ar'[mid.toNat + k]? = arPre[r.toNat + k]?)
    (hrsns'_len : rsns'.length = c.max_vars)
    (hrsns'_ok : (∃ v, v < s.core.cur_vars ∧
        s.core.rsns[v]?.getD 0xFFFFFFFF#32 = BitVec.ofNat 32 r.toNat ∧
        MoveLiveRsn arPre s.core.vals s.core.rsns first_red.toNat dst.toNat v ∧
        rsns' = rsnsCurr.set v (BitVec.ofNat 32 mid.toNat)) ∨
      (rsns' = rsnsCurr ∧ ∀ v < s.core.cur_vars,
        MoveLiveRsn arPre s.core.vals s.core.rsns first_red.toNat dst.toNat v →
        (s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat = r.toNat → mid.toNat = r.toNat))
    (hm' : (array (t := i32) c.pArena ar' ⋆ array (t := i32) bufPtr bufCurr ⋆
      FullMemArenaOut c { s with core := { s.core with rsns := rsns' } } ⋆ R) m') :
    EndBufInv c s arPre first_red dst bufPtr bufLen redWords R
      ⟨r + (3 + sz.setWidth 64), mid + (3 + sz.setWidth 64), blen, ()⟩ m' := by
  have hdb : dimacsBound = 2 ^ 28 := rfl
  have har_cap : c.arena_cap < 2 * dimacsBound := c.harena
  have hmax : c.max_vars < 2 * dimacsBound := c.hmaxv
  have hclen_eq : (3 + sz.setWidth 64).toNat = 3 + sz.toNat := bv64_add3_zext_toNat sz
  have hr_eq : (r + (3 + sz.setWidth 64)).toNat = r.toNat + 3 + sz.toNat := by
    rw [BitVec.toNat_add, hclen_eq, Nat.mod_eq_of_lt (by omega), Nat.add_assoc]
  have hmid_eq : (mid + (3 + sz.setWidth 64)).toNat = mid.toNat + 3 + sz.toNat := by
    rw [BitVec.toNat_add, hclen_eq, Nat.mod_eq_of_lt (by omega), Nat.add_assoc]
  have hhdr_d : arPre[r.toNat]?.getD 0#32 = hdr := by rw [hhdr, Option.getD_some]
  have hsz_d : (arPre[r.toNat + 2]?.getD 0#32).toNat = sz.toNat := by
    rw [hsz, Option.getD_some]
  have hclean_r : (arPre[r.toNat]?.getD 0#32 &&& 0x00880000#32) = 0#32 := by
    rw [hhdr_d]; exact hclean
  have hirred_r : (arPre[r.toNat]?.getD 0#32 &&& 0x00400000#32) = 0#32 := by
    rw [hhdr_d]; exact hirred
  have hmv_pre' : MoveRangeChain arPre first_red.toNat (r.toNat + 3 + sz.toNat) blen.toNat :=
    moveRangeChain_snoc_rw hmv_pre (by omega) hclean_r
      (by rw [hsz_d]; exact hsz3) (by rw [hsz_d])
      (by rw [ite_eq_right (fun h => h hirred_r), Nat.add_zero])
  have hcl_mid := bv32_clear_0020_props hclean
  have har'_0_d : ar'[mid.toNat]?.getD 0#32 = hdr &&& ~~~0x00200000#32 := by
    rw [har'_0, Option.getD_some]
  have har'_2 : ar'[mid.toNat + 2]? = some sz := by
    rw [har'_tail 2 (by omega) (by omega), hsz]
  have har'_sz : (ar'[mid.toNat + 2]?.getD 0#32).toNat = sz.toNat := by
    rw [har'_2, Option.getD_some]
  have har'_pre_m := moveRangeChain_congr_out
    (fun i _ hi => har'_pre i hi) hmv_irred
  have hmid_clean : (ar'[mid.toNat]?.getD 0#32 &&& 0x00880000#32) = 0#32 := by
    rw [har'_0_d]; exact hcl_mid.1
  have hmid_irred : (ar'[mid.toNat]?.getD 0#32 &&& 0x00400000#32) = 0#32 := by
    rw [har'_0_d, hcl_mid.2.1]; exact hirred
  have hmv_irred' : MoveRangeChain ar' first_red.toNat (mid.toNat + 3 + sz.toNat) 0 :=
    moveRangeChain_snoc_rw har'_pre_m (by omega) hmid_clean
      (by rw [har'_sz]; exact hsz3) (by rw [har'_sz])
      (by rw [ite_eq_right (fun h => h hmid_irred), Nat.add_zero])
  refine ⟨by rw [hr_eq, hmid_eq]; omega, by rw [hmid_eq]; omega, by rw [hr_eq]; omega,
    hblen_le, ar', bufCurr, rsns', har'_len, hbuf_len, hrsns'_len,
    fun i hi => by rw [har'_pre i (by omega)]; exact hpre i hi,
    fun i hi1 hi2 => by
      rw [hr_eq] at hi1; rw [har'_suf i (by omega) hi2]; exact hsuf i (by omega) hi2,
    by rw [hr_eq]; exact hmv_pre',
    by rw [hr_eq]; rw [show redWords - blen.toNat = rwRem by omega]
       simpa only [Nat.add_assoc] using hmv_rem',
    by rw [hmid_eq]; exact hmv_irred', hmv_buf, fun ir hir => ?_, fun rp hrp => ?_,
    fun v hv => ?_, fun v hv hlive hr0_lt hr0_red => ?_, hm'⟩
  · rw [hmid_eq] at hir
    rw [hr_eq]
    rcases refInChain_split har'_pre_m hir with hir_pre | hir_new
    · have hir_b := refInChain_bounds hir_pre
      have hir_old := refInChain_congr_out (fun i _ hi => (har'_pre i hi).symm) hir_pre
      have hir_fit := (refInChain_of_moveRangeChain hmv_irred hir_old).2.2.2
      obtain ⟨h0, src, hsrc, hni, hsz_s, hcp_s⟩ := hirred_blk ir hir_old
      refine ⟨by rw [har'_pre ir hir_b.2]; exact h0, src,
        refInChain_append_left (by omega) hsrc, hni, ?_, fun j hj => ?_⟩
      · rw [har'_pre (ir + 2) (by omega)]; exact hsz_s
      · rw [hsz_s] at hj
        rw [har'_pre (ir + 3 + j) (by omega)]
        exact hcp_s j (by rw [hsz_s]; exact hj)
    · have hir_eq : ir = mid.toNat := refInChain_single (by rw [har'_sz]) hir_new
      subst hir_eq
      refine ⟨by rw [har'_0_d]; exact hcl_mid.2.2, r.toNat,
        refInChain_append_right hmv_pre
          (RefInChain.head (by omega) hclean_r (by rw [hsz_d]; exact hsz3)
            (by rw [hsz_d]; omega)),
        hirred_r, by rw [hsz_d, har'_sz], fun j hj => ?_⟩
      rw [hsz_d] at hj
      simp only [Nat.add_assoc]
      exact har'_tail (3 + j) (by omega) (by omega)
  · obtain ⟨h0, src_c, hsrc, hred_c, hsz_c, hcp_c, hlive_c⟩ := hbuf_blk rp hrp
    exact ⟨h0, src_c, refInChain_append_left (by rw [hr_eq]; omega) hsrc,
      hred_c, hsz_c, hcp_c, hlive_c⟩
  · dsimp only
    rw [hr_eq, hmid_eq]
    by_cases hcond : MoveLiveRsn arPre s.core.vals s.core.rsns first_red.toNat dst.toNat v ∧
        (s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat < r.toNat + 3 + sz.toNat ∧
        (arPre[(s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat]?.getD 0#32 &&& 0x00400000#32) = 0#32
    · rw [ite_eq_left hcond]
      rcases refInChain_in_prefix_or_curr hmv_pre hclean_r (by rw [hsz_d]; exact hsz3)
          (by rw [hsz_d]; omega) hcond.1.2.2.1 (by rw [hsz_d]; exact hcond.2.1)
        with h_in_pre | h_eq_r
      · have hr0_lt_r : (s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat < r.toNat :=
          (refInChain_bounds h_in_pre).2
        have h1 := hrsn_map v hv
        dsimp only at h1
        rw [ite_eq_left ⟨hcond.1, hr0_lt_r, hcond.2.2⟩] at h1
        have hrs_v_eq : rsns'[v]? = rsnsCurr[v]? := by
          rcases hrsns'_ok with ⟨v1, hv1, hrs1, _, rfl⟩ | ⟨rfl, _⟩
          · have hne : v1 ≠ v := by
              intro hEq; subst hEq
              have hn := congrArg BitVec.toNat hrs1
              rw [bv32_ofNat_toNat (by omega)] at hn
              omega
            exact List.getElem?_set_ne hne
          · rfl
        have h1' : (rsns'[v]?.getD 0xFFFFFFFF#32).toNat =
            (rsnsCurr[v]?.getD 0xFFFFFFFF#32).toNat := by
          rw [hrs_v_eq]
        obtain ⟨ha, hb, hc, hd, he, hf⟩ := h1
        rw [← h1'] at ha hb hc hd he hf
        have hfit_r' := (refInChain_of_moveRangeChain hmv_irred hd).2.2.2
        have heq2 : ar'[(rsns'[v]?.getD 0xFFFFFFFF#32).toNat + 2]? =
            arCurr[(rsns'[v]?.getD 0xFFFFFFFF#32).toNat + 2]? :=
          har'_pre _ (by omega)
        refine ⟨ha, by omega, hc,
          refInChain_append_left (by omega) (refInChain_congr_out
            (fun i _ hi => har'_pre i hi) hd),
          by rw [heq2]; exact he, fun j hj => ?_⟩
        rw [har'_pre _ (by omega)]
        exact hf j hj
      · have hr0_mid : (s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat = r.toNat := h_eq_r
        have hrs_eq_mid : rsns'[v]?.getD 0xFFFFFFFF#32 = BitVec.ofNat 32 mid.toNat := by
          rcases hrsns'_ok with ⟨v1, hv1, hrs1, hml1, rfl⟩ | ⟨rfl, hall⟩
          · have hv_eq : v1 = v := by
              rcases hml1.2.2.2.2 with ⟨j1, _, hlit1, hval1⟩
              rcases hcond.1.2.2.2.2 with ⟨j2, _, hlit2, hval2⟩
              have hp1 := val_pair_of_div2 hlit1 hval1
              have hp2 := val_pair_of_div2 hlit2 hval2
              have hrs1_n : (s.core.rsns[v1]?.getD 0xFFFFFFFF#32).toNat = r.toNat := by
                rw [hrs1, bv32_ofNat_toNat (by omega)]
              exact huniq r.toNat (Nat.le_trans hfr_mid (by omega)) (by omega) v1 v hv1 hv
                hp1 hp2 hrs1_n hr0_mid
            subst hv_eq
            rw [List.getElem?_set_self (by rw [hrsns_len]; omega), Option.getD_some]
          · have hmr := hall v hv hcond.1 hr0_mid
            have h1 := hrsn_map v hv
            dsimp only at h1
            have hne : ¬ (s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat < r.toNat := by omega
            rw [ite_eq_right (fun h => hne h.2.1)] at h1
            rw [h1]
            apply BitVec.eq_of_toNat_eq
            rw [bv32_ofNat_toNat (by omega), hr0_mid, hmr]
        have hr'_nat : (rsns'[v]?.getD 0xFFFFFFFF#32).toNat = mid.toNat := by
          rw [hrs_eq_mid, bv32_ofNat_toNat (by omega)]
        rw [hr'_nat]
        refine ⟨hfr_mid, by omega, by omega,
          refInChain_append_right har'_pre_m
            (RefInChain.head (by omega) hmid_clean (by rw [har'_sz]; exact hsz3)
              (by rw [har'_sz]; omega)),
          by rw [har'_sz, hr0_mid, hsz_d], fun j hj => ?_⟩
        rw [hr0_mid, hsz_d] at hj
        rw [hr0_mid]; simp only [Nat.add_assoc]
        exact har'_tail (3 + j) (by omega) (by omega)
    · rw [ite_eq_right hcond]
      have hcond_old : ¬ (MoveLiveRsn arPre s.core.vals s.core.rsns first_red.toNat dst.toNat v ∧
          (s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat < r.toNat ∧
          (arPre[(s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat]?.getD 0#32 &&& 0x00400000#32) =
            0#32) :=
        fun h => hcond ⟨h.1, by omega, h.2.2⟩
      have h1 := hrsn_map v hv
      dsimp only at h1
      rw [ite_eq_right hcond_old] at h1
      have hrs_v_eq : rsns'[v]? = rsnsCurr[v]? := by
        rcases hrsns'_ok with ⟨v1, hv1, hrs1, hml1, rfl⟩ | ⟨rfl, _⟩
        · have hne : v1 ≠ v := by
            intro hEq; subst hEq
            have hn : (s.core.rsns[v1]?.getD 0xFFFFFFFF#32).toNat = r.toNat := by
              rw [hrs1, bv32_ofNat_toNat (by omega)]
            exact hcond ⟨hml1, by omega, by rw [hn]; exact hirred_r⟩
          exact List.getElem?_set_ne hne
        · rfl
      rw [hrs_v_eq]; exact h1
  · rw [hr_eq] at hr0_lt
    have hr0_lt_r : (s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat < r.toNat := by
      rcases refInChain_in_prefix_or_curr hmv_pre hclean_r (by rw [hsz_d]; exact hsz3)
          (by rw [hsz_d]; omega) hlive.2.2.1 (by rw [hsz_d]; exact hr0_lt) with h1 | h2
      · exact (refInChain_bounds h1).2
      · exfalso; rw [h2] at hr0_red; exact hr0_red hirred_r
    exact hbuf_rsns v hv hlive hr0_lt_r hr0_red

private def RedCopyInv (c : FullCfg) (s : FullState)
    (arPre arCurr bufCurr rsnsCurr : List (BitVec 32)) (r blen : BitVec 64)
    (bufPtr : Val i64) (bufLen sz3 : Nat) (R : Mem 64 → Prop) :
    Tup Val [i64] → Mem 64 → Prop
  | (j, ()), mC => j.toNat ≤ sz3 ∧ ∃ bufC : List (BitVec 32), bufC.length = bufLen ∧
    (∀ k < blen.toNat, bufC[k]? = bufCurr[k]?) ∧
    (∀ k < j.toNat, bufC[blen.toNat + k]? = arPre[r.toNat + k]?) ∧
    (array (t := i32) c.pArena arCurr ⋆ array (t := i32) bufPtr bufC ⋆
      FullMemArenaOut c { s with core := { s.core with rsns := rsnsCurr } } ⋆ R) mC

private def RedHdrPost (c : FullCfg) (s : FullState)
    (arPre arCurr bufCurr rsnsCurr : List (BitVec 32)) (first_red r dst blen : BitVec 64)
    (bufPtr : Val i64) (bufLen sz3 : Nat) (R : Mem 64 → Prop) : Mem 64 → Prop := fun mNext =>
  ∃ buf' : List (BitVec 32), buf'.length = bufLen ∧
    (∀ k < blen.toNat, buf'[k]? = bufCurr[k]?) ∧
    (∀ k, 2 ≤ k → k < sz3 → buf'[blen.toNat + k]? = arPre[r.toNat + k]?) ∧
    (buf'[blen.toNat]?.getD 0#32 &&& 0x00880000#32) = 0#32 ∧
    (buf'[blen.toNat]?.getD 0#32 &&& 0x00400000#32) ≠ 0#32 ∧
    ((buf'[blen.toNat]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 → ∃ v, v < s.core.cur_vars ∧
      buf'[blen.toNat + 1]? = some (BitVec.ofNat 32 v) ∧
      s.core.rsns[v]?.getD 0xFFFFFFFF#32 = BitVec.ofNat 32 r.toNat ∧
      MoveLiveRsn arPre s.core.vals s.core.rsns first_red.toNat dst.toNat v) ∧
    ((buf'[blen.toNat]?.getD 0#32 &&& 0x00200000#32) = 0#32 → ∀ v < s.core.cur_vars,
      MoveLiveRsn arPre s.core.vals s.core.rsns first_red.toNat dst.toNat v →
      (s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat ≠ r.toNat) ∧
    (array (t := i32) c.pArena arCurr ⋆ array (t := i32) bufPtr buf' ⋆
      FullMemArenaOut c { s with core := { s.core with rsns := rsnsCurr } } ⋆ R) mNext

private def RedScanPost (c : FullCfg) (s : FullState)
    (arPre arCurr bufCurr rsnsCurr : List (BitVec 32)) (first_red r dst blen : BitVec 64)
    (bufPtr : Val i64) (bufLen sz3 : Nat) (hdr : BitVec 32) (R : Mem 64 → Prop) :
    Tup Val [i32, Ty.bool] → Mem 64 → Prop
  | (_, found, ()), mF => ∃ bufF : List (BitVec 32), bufF.length = bufLen ∧
    (∀ k < blen.toNat, bufF[k]? = bufCurr[k]?) ∧ bufF[blen.toNat]? = some hdr ∧
    (∀ k, 2 ≤ k → k < sz3 → bufF[blen.toNat + k]? = arPre[r.toNat + k]?) ∧
    (found = true → ∃ v, v < s.core.cur_vars ∧
      bufF[blen.toNat + 1]? = some (BitVec.ofNat 32 v) ∧
      s.core.rsns[v]?.getD 0xFFFFFFFF#32 = BitVec.ofNat 32 r.toNat ∧
      MoveLiveRsn arPre s.core.vals s.core.rsns first_red.toNat dst.toNat v) ∧
    (found = false → (∀ k, 1 ≤ k → k < sz3 → bufF[blen.toNat + k]? = arPre[r.toNat + k]?) ∧
      ∀ v < s.core.cur_vars,
        MoveLiveRsn arPre s.core.vals s.core.rsns first_red.toNat dst.toNat v →
        (s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat ≠ r.toNat) ∧
    (array (t := i32) c.pArena arCurr ⋆ array (t := i32) bufPtr bufF ⋆
      FullMemArenaOut c { s with core := { s.core with rsns := rsnsCurr } } ⋆ R) mF

private def ScanLoopInv (s : FullState) (arPre : List (BitVec 32)) (r : BitVec 64)
    (sz : Nat) (mBase : Mem 64) : Tup Val [i32] → Mem 64 → Prop
  | (j, ()), mS => mS = mBase ∧ j.toNat ≤ sz ∧
    ∀ k < j.toNat, LitNotHitRsn arPre s.core.rsns s.core.vals s.core.cur_vars r.toNat
      (r.toNat + 3 + k)

private def IrredCopyInv (c : FullCfg) (s : FullState)
    (arPre arCurr bufCurr rsnsCurr : List (BitVec 32)) (r mid dst : BitVec 64)
    (bufPtr : Val i64) (sz3 : Nat) (R : Mem 64 → Prop) : Tup Val [i64] → Mem 64 → Prop
  | (j, ()), mC => j.toNat ≤ sz3 ∧ ∃ arC : List (BitVec 32), arC.length = dst.toNat ∧
    (∀ i < mid.toNat, arC[i]? = arCurr[i]?) ∧
    (∀ i, r.toNat + sz3 ≤ i → i < dst.toNat → arC[i]? = arCurr[i]?) ∧
    (∀ i, r.toNat + j.toNat ≤ i → i < r.toNat + sz3 → i < dst.toNat →
      arC[i]? = arPre[i]?) ∧
    (∀ k < j.toNat, arC[mid.toNat + k]? = arPre[r.toNat + k]?) ∧
    (array (t := i32) c.pArena arC ⋆ array (t := i32) bufPtr bufCurr ⋆
      FullMemArenaOut c { s with core := { s.core with rsns := rsnsCurr } } ⋆ R) mC

private def IrredRsnPost (c : FullCfg) (s : FullState)
    (arPre arC bufCurr rsnsCurr : List (BitVec 32)) (first_red r mid dst : BitVec 64)
    (bufPtr : Val i64) (R : Mem 64 → Prop) : Mem 64 → Prop := fun mNext =>
  ∃ rsns' : List (BitVec 32), rsns'.length = c.max_vars ∧
    ((∃ v, v < s.core.cur_vars ∧ s.core.rsns[v]?.getD 0xFFFFFFFF#32 = BitVec.ofNat 32 r.toNat ∧
        MoveLiveRsn arPre s.core.vals s.core.rsns first_red.toNat dst.toNat v ∧
        rsns' = rsnsCurr.set v (BitVec.ofNat 32 mid.toNat)) ∨
      (rsns' = rsnsCurr ∧ ∀ v < s.core.cur_vars,
        MoveLiveRsn arPre s.core.vals s.core.rsns first_red.toNat dst.toNat v →
        (s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat = r.toNat → mid.toNat = r.toNat)) ∧
    (array (t := i32) c.pArena arC ⋆ array (t := i32) bufPtr bufCurr ⋆
      FullMemArenaOut c { s with core := { s.core with rsns := rsns' } } ⋆ R) mNext

private def IrredPost (c : FullCfg) (s : FullState)
    (arPre arCurr bufCurr rsnsCurr : List (BitVec 32)) (first_red r mid dst : BitVec 64)
    (bufPtr : Val i64) (sz3 : Nat) (hdr : BitVec 32) (R : Mem 64 → Prop) : Mem 64 → Prop :=
  fun mI => ∃ (ar' rsns' : List (BitVec 32)), ar'.length = dst.toNat ∧
    (∀ i < mid.toNat, ar'[i]? = arCurr[i]?) ∧
    (∀ i, r.toNat + sz3 ≤ i → i < dst.toNat → ar'[i]? = arCurr[i]?) ∧
    ar'[mid.toNat]? = some hdr ∧
    (∀ k, 1 ≤ k → k < sz3 → ar'[mid.toNat + k]? = arPre[r.toNat + k]?) ∧
    rsns'.length = c.max_vars ∧
    ((∃ v, v < s.core.cur_vars ∧ s.core.rsns[v]?.getD 0xFFFFFFFF#32 = BitVec.ofNat 32 r.toNat ∧
        MoveLiveRsn arPre s.core.vals s.core.rsns first_red.toNat dst.toNat v ∧
        rsns' = rsnsCurr.set v (BitVec.ofNat 32 mid.toNat)) ∨
      (rsns' = rsnsCurr ∧ ∀ v < s.core.cur_vars,
        MoveLiveRsn arPre s.core.vals s.core.rsns first_red.toNat dst.toNat v →
        (s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat = r.toNat → mid.toNat = r.toNat)) ∧
    (array (t := i32) c.pArena ar' ⋆ array (t := i32) bufPtr bufCurr ⋆
      FullMemArenaOut c { s with core := { s.core with rsns := rsns' } } ⋆ R) mI

private theorem end_buf_red_clr_post {c : FullCfg} {s : FullState}
    {arPre arCurr bufCurr bufIn rsnsCurr : List (BitVec 32)}
    {first_red r dst blen : BitVec 64} {bufPtr : Val i64} {bufLen sz3 : Nat}
    {hdr : BitVec 32} {R : Mem 64 → Prop} {m : Mem 64}
    (hbf_len : bufIn.length = bufLen) (hbf_lt : blen.toNat < bufIn.length)
    (hclean : (hdr &&& 0x00880000#32) = 0#32) (hred : (hdr &&& 0x00400000#32) ≠ 0#32)
    (hbf_pre : ∀ k < blen.toNat, bufIn[k]? = bufCurr[k]?)
    (hbf_tail : ∀ k, 2 ≤ k → k < sz3 → bufIn[blen.toNat + k]? = arPre[r.toNat + k]?)
    (hnone : ∀ v < s.core.cur_vars,
      MoveLiveRsn arPre s.core.vals s.core.rsns first_red.toNat dst.toNat v →
      (s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat ≠ r.toNat)
    (hmF' : (array (t := i32) c.pArena arCurr ⋆
      array (t := i32) bufPtr (bufIn.set blen.toNat (hdr &&& ~~~0x00200000#32)) ⋆
      FullMemArenaOut c { s with core := { s.core with rsns := rsnsCurr } } ⋆ R) m) :
    RedHdrPost c s arPre arCurr bufCurr rsnsCurr first_red r dst blen bufPtr bufLen sz3 R m := by
  obtain ⟨hp1, hp2, hp3, hp4, hp5, hp6, hp7⟩ :=
    end_buf_red_clr_hdr hbf_len hbf_lt hclean hred hbf_pre hbf_tail hnone
  exact ⟨_, hp1, hp2, hp3, hp4, hp5, hp6, hp7, hmF'⟩

private theorem end_buf_red_hit_buf {c : FullCfg} {s : FullState}
    {arPre arCurr bufCurr bufC rsnsCurr : List (BitVec 32)}
    {first_red r dst blen : BitVec 64} {bufPtr : Val i64} {bufLen : Nat}
    {hdr sz lit v32 r0 j : BitVec 32} {R : Mem 64 → Prop} {m : Mem 64}
    (hblen_le : blen.toNat + (3 + sz.toNat) ≤ bufLen) (hsz3 : 3 ≤ sz.toNat)
    (hfit : r.toNat + 3 + sz.toNat ≤ dst.toNat) (hfr_r : first_red.toNat ≤ r.toNat)
    (hr_lt : r.toNat < dst.toNat) (hr_32 : r.toNat < 2 ^ 32)
    (hhdr_ar : arPre[r.toNat]? = some hdr) (hsz_ar : arPre[r.toNat + 2]? = some sz)
    (hclean : (hdr &&& 0x00880000#32) = 0#32)
    (hfl_ne : (hdr &&& 0x00200000#32) ≠ 0#32) (hj_lt : j.toNat < sz.toNat)
    (hlit_ar : arPre[r.toNat + 3 + j.toNat]? = some lit)
    (hv_nat : v32.toNat = lit.toNat / 2) (hv_lt : v32.toNat < s.core.cur_vars)
    (hb_1 : s.core.vals[lit.toNat]? = some 1#8)
    (hr0_eq : s.core.rsns[v32.toNat]? = some r0) (hrs_r_n : r0.toNat = r.toNat)
    (hmv_pre : MoveRangeChain arPre first_red.toNat r.toNat blen.toNat)
    (hbufC_len : bufC.length = bufLen)
    (hbufC_pre : ∀ k < blen.toNat, bufC[k]? = bufCurr[k]?)
    (hbufC_hdr : bufC[blen.toNat]? = some hdr)
    (hbufC_cp : ∀ k < 3 + sz.toNat, bufC[blen.toNat + k]? = arPre[r.toNat + k]?)
    (hmF : (array (t := i32) c.pArena arCurr ⋆
      array (t := i32) bufPtr (bufC.set (blen.toNat + 1) v32) ⋆
      FullMemArenaOut c { s with core := { s.core with rsns := rsnsCurr } } ⋆ R) m) :
    RedScanPost c s arPre arCurr bufCurr rsnsCurr first_red r dst blen bufPtr bufLen
      (3 + sz.toNat) hdr R ⟨j, true, ()⟩ m := by
  let bufF := bufC.set (blen.toNat + 1) v32
  have hml := litScan_hit_moveLiveRsn hmv_pre hhdr_ar hsz_ar hclean hfl_ne hsz3 hfit hfr_r
    hr_lt hj_lt hlit_ar hv_nat hb_1 (by rw [hr0_eq, Option.getD_some]; exact hrs_r_n)
  exact ⟨bufF, by simp [bufF, hbufC_len],
    fun k hk => by dsimp [bufF]; rw [List.getElem?_set_ne (by omega)]; exact hbufC_pre k hk,
    by dsimp [bufF]; rw [List.getElem?_set_ne (by omega)]; exact hbufC_hdr,
    fun k _ hk2 => by dsimp [bufF]; rw [List.getElem?_set_ne (by omega)]; exact hbufC_cp k hk2,
    fun _ => ⟨v32.toNat, hv_lt,
      by dsimp [bufF]; rw [List.getElem?_set_self (by rw [hbufC_len]; omega)]
         exact congrArg some (BitVec.eq_of_toNat_eq (bv32_ofNat_toNat v32.isLt)).symm,
      by rw [hr0_eq, Option.getD_some]; apply BitVec.eq_of_toNat_eq
         rw [hrs_r_n, bv32_ofNat_toNat hr_32], hml⟩,
    fun h01 => absurd h01 (by decide), hmF⟩

private theorem scanLoopInv_succ {s : FullState} {arPre : List (BitVec 32)}
    {r : BitVec 64} {sz : Nat} {mJ : Mem 64} {j : BitVec 32}
    (hj_lt : j.toNat < sz) (hj1_eq : (j + 1#32).toNat = j.toNat + 1)
    (hno_k : ∀ k < j.toNat, LitNotHitRsn arPre s.core.rsns s.core.vals s.core.cur_vars r.toNat
      (r.toNat + 3 + k))
    (hmiss : LitNotHitRsn arPre s.core.rsns s.core.vals s.core.cur_vars r.toNat
      (r.toNat + 3 + j.toNat)) :
    ScanLoopInv s arPre r sz mJ ⟨j + 1#32, ()⟩ mJ :=
  ⟨rfl, by rw [hj1_eq]; omega, fun k hk => by
    by_cases hkj : k = j.toNat
    · subst hkj; exact hmiss
    · exact hno_k k (by rw [hj1_eq] at hk; omega)⟩

private theorem end_buf_irred_hit_rsn {c : FullCfg} {s : FullState}
    {arPre arC bufCurr rsnsCurr : List (BitVec 32)}
    {first_red r mid dst : BitVec 64} {bufPtr : Val i64} {rw : Nat}
    {hdr sz lit v32 r0 j2 : BitVec 32} {R : Mem 64 → Prop} {m : Mem 64}
    (hmv_pre : MoveRangeChain arPre first_red.toNat r.toNat rw)
    (hhdr_ar : arPre[r.toNat]? = some hdr) (hsz_ar : arPre[r.toNat + 2]? = some sz)
    (hclean : (hdr &&& 0x00880000#32) = 0#32)
    (hfl_ne : (hdr &&& 0x00200000#32) ≠ 0#32)
    (hsz3 : 3 ≤ sz.toNat) (hfit : r.toNat + 3 + sz.toNat ≤ dst.toNat)
    (hfr_r : first_red.toNat ≤ r.toNat) (hr_lt : r.toNat < dst.toNat)
    (hr_32 : r.toNat < 2 ^ 32) (hj_lt2 : j2.toNat < sz.toNat)
    (hlit_ar : arPre[r.toNat + 3 + j2.toNat]? = some lit)
    (hv_nat : v32.toNat = lit.toNat / 2) (hv_lt : v32.toNat < s.core.cur_vars)
    (hb_1 : s.core.vals[lit.toNat]? = some 1#8)
    (hr0_eq : s.core.rsns[v32.toNat]? = some r0) (hrs_r_n : r0.toNat = r.toNat)
    (hrsns_len : rsnsCurr.length = c.max_vars)
    (hm_rsn : (FullMemArenaOut c { s with core :=
        { s.core with rsns := rsnsCurr.set v32.toNat (BitVec.ofNat 32 mid.toNat) } } ⋆
      (array (t := i32) c.pArena arC ⋆ (array (t := i32) bufPtr bufCurr ⋆ (R ⋆ emp)))) m) :
    IrredRsnPost c s arPre arC bufCurr rsnsCurr first_red r mid dst bufPtr R m := by
  let rsns' := rsnsCurr.set v32.toNat (BitVec.ofNat 32 mid.toNat)
  have hm_rsn' : (array (t := i32) c.pArena arC ⋆ array (t := i32) bufPtr bufCurr ⋆
      FullMemArenaOut c { s with core := { s.core with rsns := rsns' } } ⋆ R) m := by
    simp only [sep_emp, sep_assoc] at hm_rsn ⊢
    rw [sep_comm_l (FullMemArenaOut c _) (array (t := i32) c.pArena arC),
      sep_comm_l (FullMemArenaOut c _) (array (t := i32) bufPtr bufCurr)] at hm_rsn
    exact hm_rsn
  have hml := litScan_hit_moveLiveRsn hmv_pre hhdr_ar hsz_ar hclean hfl_ne hsz3 hfit hfr_r
    hr_lt hj_lt2 hlit_ar hv_nat hb_1 (by rw [hr0_eq, Option.getD_some]; exact hrs_r_n)
  exact ⟨rsns', by simp [rsns', hrsns_len], Or.inl ⟨v32.toNat, hv_lt,
    by rw [hr0_eq, Option.getD_some]; apply BitVec.eq_of_toNat_eq
       rw [hrs_r_n, bv32_ofNat_toNat hr_32], hml, rfl⟩, hm_rsn'⟩

private theorem end_buf_irred_id_post {c : FullCfg} {s : FullState}
    {arPre arCurr bufCurr rsnsCurr : List (BitVec 32)}
    {first_red r mid dst : BitVec 64} {bufPtr : Val i64} {sz : BitVec 32}
    {hdr : BitVec 32} {R : Mem 64 → Prop} {m : Mem 64}
    (har_len : arCurr.length = dst.toNat) (hrsns_len : rsnsCurr.length = c.max_vars)
    (hr_lt : r.toNat < dst.toNat) (hfit : r.toNat + 3 + sz.toNat ≤ dst.toNat)
    (hmid_n : mid.toNat = r.toNat) (hhdr_ar : arPre[r.toNat]? = some hdr)
    (hsuf : ∀ i, r.toNat ≤ i → i < dst.toNat → arCurr[i]? = arPre[i]?)
    (hm : (array (t := i32) c.pArena arCurr ⋆ array (t := i32) bufPtr bufCurr ⋆
      FullMemArenaOut c { s with core := { s.core with rsns := rsnsCurr } } ⋆ R) m) :
    IrredPost c s arPre arCurr bufCurr rsnsCurr first_red r mid dst bufPtr (3 + sz.toNat) hdr
      R m :=
  ⟨arCurr, rsnsCurr, har_len, fun _ _ => rfl, fun _ _ _ => rfl,
    by rw [hmid_n, hsuf r.toNat (Nat.le_refl _) hr_lt]; exact hhdr_ar,
    fun k _ hk2 => by rw [hmid_n]; exact hsuf (r.toNat + k) (by omega) (by omega),
    hrsns_len, Or.inr ⟨rfl, fun _ _ _ _ => hmid_n⟩, hm⟩

private theorem end_buf_irred_ar_set {arCurr arPre ar' : List (BitVec 32)}
    {mid r dst : BitVec 64} {sz hdr : BitVec 32}
    (har'_len : ar'.length = dst.toNat) (hmid_lt : mid.toNat < ar'.length)
    (hmid_le : mid.toNat < r.toNat + (3 + sz.toNat))
    (har'_pre : ∀ i < mid.toNat, ar'[i]? = arCurr[i]?)
    (har'_suf : ∀ i, r.toNat + (3 + sz.toNat) ≤ i → i < dst.toNat → ar'[i]? = arCurr[i]?)
    (har'_tail : ∀ k, 1 ≤ k → k < 3 + sz.toNat → ar'[mid.toNat + k]? = arPre[r.toNat + k]?) :
    let ar'' := ar'.set mid.toNat (hdr &&& ~~~0x00200000#32)
    ar''.length = dst.toNat ∧
      (∀ i < mid.toNat, ar''[i]? = arCurr[i]?) ∧
      (∀ i, r.toNat + (3 + sz.toNat) ≤ i → i < dst.toNat → ar''[i]? = arCurr[i]?) ∧
      ar''[mid.toNat]? = some (hdr &&& ~~~0x00200000#32) ∧
      (∀ k, 1 ≤ k → k < 3 + sz.toNat → ar''[mid.toNat + k]? = arPre[r.toNat + k]?) := by
  intro ar''
  refine ⟨by simp [ar'', har'_len],
    fun i hi => by dsimp [ar'']; rw [List.getElem?_set_ne (by omega)]; exact har'_pre i hi,
    fun i a b => by dsimp [ar'']; rw [List.getElem?_set_ne (by omega)]; exact har'_suf i a b,
    by dsimp [ar'']; rw [List.getElem?_set_self hmid_lt],
    fun k a b => by dsimp [ar'']; rw [List.getElem?_set_ne (by omega)]; exact har'_tail k a b⟩

private theorem end_buf_rsn_hit_curr_hc {c : FullCfg} {s : FullState}
    {arPre arCurr rsnsCurr : List (BitVec 32)} {first_red r mid dst : BitVec 64}
    {lit : BitVec 32} (hv_lt : (lit >>> 1#32).toNat < s.core.cur_vars)
    (hrs_len : s.core.rsns.length = c.max_vars)
    (hrsns_len : rsnsCurr.length = c.max_vars) (hcv_le : s.core.cur_vars ≤ c.max_vars)
    (hmid_le : mid.toNat ≤ r.toNat)
    (hc : (rsnsCurr[lit.toNat / 2]'(by
      rw [hrsns_len, ← lit_ushiftRight_one lit]; omega)).setWidth 64 = r)
    (hrsn_map : ∀ v < s.core.cur_vars,
      let r0 := s.core.rsns[v]?.getD 0xFFFFFFFF#32
      if MoveLiveRsn arPre s.core.vals s.core.rsns first_red.toNat dst.toNat v ∧
          r0.toNat < r.toNat ∧ (arPre[r0.toNat]?.getD 0#32 &&& 0x00400000#32) = 0#32
      then let r' := (rsnsCurr[v]?.getD 0xFFFFFFFF#32).toNat
        first_red.toNat ≤ r' ∧ r' < mid.toNat ∧ r' < 0x80000000 ∧
        RefInChain arCurr first_red.toNat mid.toNat r' ∧
        (arCurr[r' + 2]?.getD 0#32).toNat = (arPre[r0.toNat + 2]?.getD 0#32).toNat ∧
        ∀ j < (arPre[r0.toNat + 2]?.getD 0#32).toNat,
          arCurr[r' + 3 + j]? = arPre[r0.toNat + 3 + j]?
      else rsnsCurr[v]?.getD 0xFFFFFFFF#32 = r0) :
    ∃ r0s, s.core.rsns[(lit >>> 1#32).toNat]? = some r0s ∧ r0s.toNat = r.toNat := by
  have hlt_c : lit.toNat / 2 < rsnsCurr.length := by
    rw [hrsns_len, ← lit_ushiftRight_one lit]; omega
  let r0c := rsnsCurr[lit.toNat / 2]'hlt_c
  have hr0c_eq : rsnsCurr[lit.toNat / 2]? = some r0c := List.getElem?_eq_getElem hlt_c
  have hrs_r_n : r0c.toNat = r.toNat := by
    have h1 := congrArg BitVec.toNat hc
    rwa [zext_toNat (n := 64) r0c (by decide)] at h1
  have hm_v := hrsn_map (lit >>> 1#32).toNat hv_lt
  rw [lit_ushiftRight_one] at hm_v; dsimp only at hm_v; split at hm_v
  · exact absurd (by rw [hr0c_eq, Option.getD_some, hrs_r_n] at hm_v; exact hm_v.2.1) (by omega)
  · have hrs_lt : lit.toNat / 2 < s.core.rsns.length := by
      rw [hrs_len, ← lit_ushiftRight_one lit]; omega
    refine ⟨s.core.rsns[lit.toNat / 2]'hrs_lt, by
      rw [lit_ushiftRight_one]; exact List.getElem?_eq_getElem hrs_lt, ?_⟩
    have h1 : rsnsCurr[lit.toNat / 2]?.getD 0xFFFFFFFF#32 =
        s.core.rsns[lit.toNat / 2]?.getD 0xFFFFFFFF#32 := hm_v
    rw [hr0c_eq, List.getElem?_eq_getElem hrs_lt, Option.getD_some, Option.getD_some] at h1
    rw [← h1]; exact hrs_r_n

private theorem end_buf_rsn_miss_curr_hc {c : FullCfg} {s : FullState}
    {arPre arCurr rsnsCurr : List (BitVec 32)} {first_red r mid dst : BitVec 64}
    {j3 : Nat} {lit : BitVec 32} (hlit_ar : arPre[j3]? = some lit)
    (hv_lt : (lit >>> 1#32).toNat < s.core.cur_vars)
    (hcv_le : s.core.cur_vars ≤ c.max_vars) (hrs_len : s.core.rsns.length = c.max_vars)
    (hrsns_len : rsnsCurr.length = c.max_vars)
    (hc : (rsnsCurr[lit.toNat / 2]'(by
      rw [hrsns_len, ← lit_ushiftRight_one lit]; omega)).setWidth 64 ≠ r)
    (hrsn_map : ∀ v < s.core.cur_vars,
      let r0 := s.core.rsns[v]?.getD 0xFFFFFFFF#32
      if MoveLiveRsn arPre s.core.vals s.core.rsns first_red.toNat dst.toNat v ∧
          r0.toNat < r.toNat ∧ (arPre[r0.toNat]?.getD 0#32 &&& 0x00400000#32) = 0#32
      then let r' := (rsnsCurr[v]?.getD 0xFFFFFFFF#32).toNat
        first_red.toNat ≤ r' ∧ r' < mid.toNat ∧ r' < 0x80000000 ∧
        RefInChain arCurr first_red.toNat mid.toNat r' ∧
        (arCurr[r' + 2]?.getD 0#32).toNat = (arPre[r0.toNat + 2]?.getD 0#32).toNat ∧
        ∀ j < (arPre[r0.toNat + 2]?.getD 0#32).toNat,
          arCurr[r' + 3 + j]? = arPre[r0.toNat + 3 + j]?
      else rsnsCurr[v]?.getD 0xFFFFFFFF#32 = r0) :
    LitNotHitRsn arPre s.core.rsns s.core.vals s.core.cur_vars r.toNat j3 := by
  have hlt_c : lit.toNat / 2 < rsnsCurr.length := by
    rw [hrsns_len, ← lit_ushiftRight_one lit]; omega
  let r0c := rsnsCurr[lit.toNat / 2]'hlt_c
  have hr0c_eq : rsnsCurr[lit.toNat / 2]? = some r0c := List.getElem?_eq_getElem hlt_c
  have hrs_lt : lit.toNat / 2 < s.core.rsns.length := by
    rw [hrs_len, ← lit_ushiftRight_one lit]; omega
  let r0 := s.core.rsns[lit.toNat / 2]'hrs_lt
  have hr0_eq : s.core.rsns[(lit >>> 1#32).toNat]? = some r0 := by
    rw [lit_ushiftRight_one]; exact List.getElem?_eq_getElem hrs_lt
  refine litNotHit_of_rsn_ne hlit_ar (lit_ushiftRight_one lit) hr0_eq (fun heq => hc ?_)
  have hr0_r : r0.toNat = r.toNat := by
    have h1 := congrArg BitVec.toNat heq; rwa [zext_toNat (n := 64) r0 (by decide)] at h1
  have hm_v := hrsn_map (lit >>> 1#32).toNat hv_lt
  rw [lit_ushiftRight_one] at hm_v; dsimp only at hm_v
  rw [ite_eq_right (fun h => by
    have h1 : (s.core.rsns[lit.toNat / 2]?.getD 0xFFFFFFFF#32).toNat < r.toNat := h.2.1
    rw [List.getElem?_eq_getElem hrs_lt, Option.getD_some, hr0_r] at h1
    exact Nat.lt_irrefl _ h1)] at hm_v
  have hrc : r0c = r0 := by
    simpa only [hr0c_eq, List.getElem?_eq_getElem hrs_lt, Option.getD_some] using hm_v
  change r0c.setWidth 64 = r; rw [hrc]; exact heq

private theorem end_buf_red_found_true {c : FullCfg} {s : FullState}
    {arPre arCurr bufCurr rsnsCurr : List (BitVec 32)} {first_red r dst blen : BitVec 64}
    {bufPtr : Val i64} {bufLen sz3 : Nat} {hdr : BitVec 32} {R : Mem 64 → Prop} {mF : Mem 64}
    (hclean : (hdr &&& 0x00880000#32) = 0#32) (hred : (hdr &&& 0x00400000#32) ≠ 0#32)
    (hfl_ne : (hdr &&& 0x00200000#32) ≠ 0#32) {bufF : List (BitVec 32)}
    (hbf_len : bufF.length = bufLen) (hbf_pre : ∀ k < blen.toNat, bufF[k]? = bufCurr[k]?)
    (hbf_hdr : bufF[blen.toNat]? = some hdr)
    (hbf_tail : ∀ k, 2 ≤ k → k < sz3 → bufF[blen.toNat + k]? = arPre[r.toNat + k]?)
    (hit : ∃ v, v < s.core.cur_vars ∧ bufF[blen.toNat + 1]? = some (BitVec.ofNat 32 v) ∧
      s.core.rsns[v]?.getD 0xFFFFFFFF#32 = BitVec.ofNat 32 r.toNat ∧
      MoveLiveRsn arPre s.core.vals s.core.rsns first_red.toNat dst.toNat v)
    (hmF : (array (t := i32) c.pArena arCurr ⋆ array (t := i32) bufPtr bufF ⋆
      FullMemArenaOut c { s with core := { s.core with rsns := rsnsCurr } } ⋆ R) mF) :
    RedHdrPost c s arPre arCurr bufCurr rsnsCurr first_red r dst blen bufPtr bufLen sz3 R mF :=
  let ⟨v, hv, hbv1, hrs_v, hml_v⟩ := hit
  ⟨bufF, hbf_len, hbf_pre, hbf_tail, by rwa [hbf_hdr, Option.getD_some],
    by rwa [hbf_hdr, Option.getD_some], fun _ => ⟨v, hv, hbv1, hrs_v, hml_v⟩,
    fun hz => absurd (by rwa [hbf_hdr, Option.getD_some] at hz) hfl_ne, hmF⟩

private theorem end_buf_red_none_scan {c : FullCfg} {s : FullState}
    {arPre arCurr bufCurr bufC rsnsCurr : List (BitVec 32)} {first_red r dst blen : BitVec 64}
    {bufPtr : Val i64} {bufLen : Nat} {hdr sz j : BitVec 32} {R : Mem 64 → Prop} {mJ : Mem 64}
    (hj_eq : j.toNat = sz.toNat) (hsz_ar : arPre[r.toNat + 2]? = some sz)
    (hno_k : ∀ k < j.toNat, LitNotHitRsn arPre s.core.rsns s.core.vals s.core.cur_vars r.toNat
      (r.toNat + 3 + k))
    (hbufC_len : bufC.length = bufLen) (hbufC_pre : ∀ k < blen.toNat, bufC[k]? = bufCurr[k]?)
    (hbufC_hdr : bufC[blen.toNat]? = some hdr)
    (hbufC_cp : ∀ k < 3 + sz.toNat, bufC[blen.toNat + k]? = arPre[r.toNat + k]?)
    (hmJ : (array (t := i32) c.pArena arCurr ⋆ array (t := i32) bufPtr bufC ⋆
      FullMemArenaOut c { s with core := { s.core with rsns := rsnsCurr } } ⋆ R) mJ) :
    RedScanPost c s arPre arCurr bufCurr rsnsCurr first_red r dst blen bufPtr bufLen
      (3 + sz.toNat) hdr R ⟨j, false, ()⟩ mJ := by
  rw [hj_eq] at hno_k
  exact ⟨bufC, hbufC_len, hbufC_pre, hbufC_hdr, fun k _ hk2 => hbufC_cp k hk2,
    fun h10 => absurd h10 (by decide), fun _ => ⟨fun k _ hk2 => hbufC_cp k hk2,
      noHitBefore_none_live (by rw [hsz_ar, Option.getD_some]) hno_k⟩, hmJ⟩

private theorem end_buf_irred_none_scan {c : FullCfg} {s : FullState}
    {arPre arC bufCurr rsnsCurr : List (BitVec 32)} {first_red r mid dst : BitVec 64}
    {bufPtr : Val i64} {sz j2 : BitVec 32} {R : Mem 64 → Prop} {mJ : Mem 64}
    (hj_eq : j2.toNat = sz.toNat) (hsz_ar : arPre[r.toNat + 2]? = some sz)
    (hno_k : ∀ k < j2.toNat, LitNotHitRsn arPre s.core.rsns s.core.vals s.core.cur_vars r.toNat
      (r.toNat + 3 + k))
    (hrsns_len : rsnsCurr.length = c.max_vars)
    (hmJ : (array (t := i32) c.pArena arC ⋆ array (t := i32) bufPtr bufCurr ⋆
      FullMemArenaOut c { s with core := { s.core with rsns := rsnsCurr } } ⋆ R) mJ) :
    IrredRsnPost c s arPre arC bufCurr rsnsCurr first_red r mid dst bufPtr R mJ := by
  rw [hj_eq] at hno_k
  exact ⟨rsnsCurr, hrsns_len, Or.inr ⟨rfl, fun v hv hml hrs_n =>
    absurd hrs_n (noHitBefore_none_live (by rw [hsz_ar, Option.getD_some]) hno_k v hv hml)⟩, hmJ⟩

private theorem end_buf_irred_copy_step_r {arC arCurr arPre : List (BitVec 32)}
    {mid r dst j sz3 : Nat} {val : BitVec 32}
    (harC_len : arC.length = dst) (hmj_lt : mid + j < arC.length) (hmid_lt : mid < r)
    (hj_lt : j < sz3) (harj_val : arPre[r + j]? = some val)
    (harC_pre : ∀ i < mid, arC[i]? = arCurr[i]?)
    (harC_suf : ∀ i, r + sz3 ≤ i → i < dst → arC[i]? = arCurr[i]?)
    (harC_rem : ∀ i, r + j ≤ i → i < r + sz3 → i < dst → arC[i]? = arPre[i]?)
    (harC_cp : ∀ k < j, arC[mid + k]? = arPre[r + k]?) :
    let arC' := arC.set (mid + j) val
    arC'.length = dst ∧ (∀ i < mid, arC'[i]? = arCurr[i]?) ∧
      (∀ i, r + sz3 ≤ i → i < dst → arC'[i]? = arCurr[i]?) ∧
      (∀ i, r + (j + 1) ≤ i → i < r + sz3 → i < dst → arC'[i]? = arPre[i]?) ∧
      (∀ k < j + 1, arC'[mid + k]? = arPre[r + k]?) := by
  intro arC'
  refine ⟨by simp [arC', harC_len],
    fun i hi => by dsimp [arC']; rw [List.getElem?_set_ne (by omega)]; exact harC_pre i hi,
    fun i a b => by dsimp [arC']; rw [List.getElem?_set_ne (by omega)]; exact harC_suf i a b,
    fun i a b hc => by dsimp [arC']; rw [List.getElem?_set_ne (by omega)]
                       exact harC_rem i (by omega) b hc,
    fun k hk => by
      dsimp [arC']; by_cases hkj : k = j
      · subst hkj; rw [List.getElem?_set_self hmj_lt, harj_val]
      · rw [List.getElem?_set_ne (by omega)]; exact harC_cp k (by omega)⟩

private theorem end_buf_val_eq_one {c : FullCfg} {s : FullState} {lit : BitVec 32}
    (hvals_len : s.core.vals.length = 2 * c.max_vars) (hcv_le : s.core.cur_vars ≤ c.max_vars)
    (hlt : lit.toNat < 2 * s.core.cur_vars)
    (hvals_tri : ∀ i < 2 * s.core.cur_vars,
      s.core.vals[i]?.getD 0#8 = 0#8 ∨ s.core.vals[i]?.getD 0#8 = 1#8 ∨
      s.core.vals[i]?.getD 0#8 = 255#8)
    (hsgt : (0#32).slt (BitVec.signExtend 32 (s.core.vals[lit.toNat]'(by omega))) = true) :
    s.core.vals[lit.toNat]? = some 1#8 := by
  have hl : lit.toNat < s.core.vals.length := by omega
  have heq := List.getElem?_eq_getElem hl; have htri := hvals_tri lit.toNat hlt
  rw [heq, Option.getD_some] at htri; rw [heq, (bv8_sgt_zero_iff _ htri).mp hsgt]

private theorem end_buf_val_litNotHit {c : FullCfg} {s : FullState} {arPre : List (BitVec 32)}
    {r : BitVec 64} {j3 : Nat} {lit : BitVec 32}
    (hlit_ar : arPre[j3]? = some lit) (hvals_len : s.core.vals.length = 2 * c.max_vars)
    (hcv_le : s.core.cur_vars ≤ c.max_vars) (hlt : lit.toNat < 2 * s.core.cur_vars)
    (hvals_tri : ∀ i < 2 * s.core.cur_vars,
      s.core.vals[i]?.getD 0#8 = 0#8 ∨ s.core.vals[i]?.getD 0#8 = 1#8 ∨
      s.core.vals[i]?.getD 0#8 = 255#8)
    (hsle : (0#32).slt (BitVec.signExtend 32 (s.core.vals[lit.toNat]'(by omega))) = false) :
    LitNotHitRsn arPre s.core.rsns s.core.vals s.core.cur_vars r.toNat j3 := by
  have hl : lit.toNat < s.core.vals.length := by omega
  have heq := List.getElem?_eq_getElem hl; have htri := hvals_tri lit.toNat hlt
  rw [heq, Option.getD_some] at htri
  exact litNotHit_of_val_ne hlit_ar heq htri (fun h1 => by
    change (0#32).slt _ = true at h1; rw [hsle] at h1; exact Bool.false_ne_true h1)

private theorem end_buf_red_clr_zero {c : FullCfg} {s : FullState}
    {arPre arCurr bufCurr bufC rsnsCurr : List (BitVec 32)}
    {first_red r dst blen : BitVec 64} {bufPtr : Val i64} {bufLen sz3 : Nat}
    {hdr : BitVec 32} {R : Mem 64 → Prop} {m : Mem 64}
    (hbufC_len : bufC.length = bufLen) (hbl_lt : blen.toNat < bufC.length)
    (hclean : (hdr &&& 0x00880000#32) = 0#32) (hred : (hdr &&& 0x00400000#32) ≠ 0#32)
    (hfl_eq : (hdr &&& 0x00200000#32) = 0#32) (hhdr_ar : arPre[r.toNat]? = some hdr)
    (hbufC_hdr : bufC[blen.toNat]? = some hdr)
    (hbufC_pre : ∀ k < blen.toNat, bufC[k]? = bufCurr[k]?)
    (hbufC_tail : ∀ k, 2 ≤ k → k < sz3 → bufC[blen.toNat + k]? = arPre[r.toNat + k]?)
    (hmJ : (array (t := i32) c.pArena arCurr ⋆ array (t := i32) bufPtr bufC ⋆
      FullMemArenaOut c { s with core := { s.core with rsns := rsnsCurr } } ⋆ R) m) :
    RedHdrPost c s arPre arCurr bufCurr rsnsCurr first_red r dst blen bufPtr bufLen sz3 R m := by
  have h1 : hdr = (hdr &&& 0x00200000#32) ||| (hdr &&& ~~~0x00200000#32) := by
    rw [← BitVec.and_or_distrib_left, show (0x00200000#32 ||| ~~~0x00200000#32) =
      BitVec.allOnes 32 from by decide, BitVec.and_allOnes]
  rw [hfl_eq, BitVec.zero_or] at h1
  have hset : bufC.set blen.toNat (hdr &&& ~~~0x00200000#32) = bufC := by
    apply List.ext_getElem?; intro i; by_cases hi : i = blen.toNat
    · subst hi; rw [List.getElem?_set_self hbl_lt, hbufC_hdr, ← h1]
    · rw [List.getElem?_set_ne (Ne.symm hi)]
  have hmF' : (array (t := i32) c.pArena arCurr ⋆
      array (t := i32) bufPtr (bufC.set blen.toNat (hdr &&& ~~~0x00200000#32)) ⋆
      FullMemArenaOut c { s with core := { s.core with rsns := rsnsCurr } } ⋆ R) m := by
    rwa [hset]
  exact end_buf_red_clr_post hbufC_len hbl_lt hclean hred hbufC_pre hbufC_tail
    (fun v _ hml hrs => by
      have h2 := hml.2.2.2.1; rw [hrs, hhdr_ar, Option.getD_some] at h2; exact h2 hfl_eq) hmF'

private theorem end_buf_fred_val {mid dst fred' : BitVec 64}
    (hfred : fred' = if mid.toNat < dst.toNat then mid else 0xFFFFFFFF#64) :
    fred' = if mid.toNat < dst.toNat then BitVec.ofNat 64 mid.toNat else 0xFFFFFFFF#64 := by
  by_cases hlt : mid.toNat < dst.toNat
  · simp only [hfred, ite_eq_left hlt]
    exact (BitVec.eq_of_toNat_eq (bv64_ofNat_toNat mid.isLt)).symm
  · simp only [hfred, ite_eq_right hlt]

theorem full_move_red_end_buf_m6_wp (Γ : Env)
    (hPass2 : ∀ a m Q X, fullMoveRedPass2Spec a m Q X →
      Γ "full_move_red_pass2_m6" [i64, i64, i64, i64, i64] [] a m Q X) :
    ∀ a m Q X, fullMoveRedEndBufSpec a m Q X →
      Func.wp Γ full_move_red_end_buf_m6_body a m Q X := by
  rintro ⟨h, first_red, dst, bufPtr, ⟨⟩⟩ m Q X
    ⟨c, s, arPre, buf, redWords, R, rfl, hlen, hfr_dst, hdst_cap, harPre_len, hrw_buf,
      hbuf_bd, hmv_arPre, hvals_tri, huniq, hm, hQ⟩
  have hdb : dimacsBound = 2 ^ 28 := rfl
  have har_cap : c.arena_cap < 2 * dimacsBound := c.harena
  have hmax : c.max_vars < 2 * dimacsBound := c.hmaxv
  have hcv_le : s.core.cur_vars ≤ c.max_vars := hlen.core_ok.cur_vars_le
  have hrs_len : s.core.rsns.length = c.max_vars := hlen.core_ok.rsns_len
  have hvals_len : s.core.vals.length = 2 * c.max_vars := hlen.core_ok.vals_len
  have h0_64 : (0#64).toNat = 0 := rfl; have h1_64 : (1#64).toNat = 1 := rfl
  have h2_64 : (2#64).toNat = 2 := rfl; have h3_64 : (3#64).toNat = 3 := rfl
  have h1_32 : (1#32).toNat = 1 := rfl
  have h0_32 : BitVec.ofNat (OfNat.ofNat 32) (OfNat.ofNat 0) = 0#32 := rfl
  have hcv_mod : s.core.cur_vars % 2 ^ 64 = s.core.cur_vars := Nat.mod_eq_of_lt (by omega)
  c0_hsteps_nogrp
  refine wp_loop_inv (ts := [i64, i64, i64])
    (EndBufInv c s arPre first_red dst bufPtr buf.length redWords R)
    (fun ⟨r, _, _, ⟨⟩⟩ _ => dst.toNat - r.toNat) (fun JL hLoop => ?_) ?_
  · c0_hsteps; refine hLoop ⟨first_red, first_red, 0#64, ⟨⟩⟩ m ⟨by rw [h0_64, Nat.add_zero],
      Nat.le_refl _, hfr_dst, by rw [h0_64]; exact Nat.zero_le _, arPre, buf, s.core.rsns,
      harPre_len, rfl, hrs_len, fun _ _ => rfl, fun _ _ _ => rfl,
      by rw [h0_64]; exact MoveRangeChain.empty, by rw [h0_64, Nat.sub_zero]; exact hmv_arPre,
      MoveRangeChain.empty, by rw [h0_64]; exact MoveRangeChain.empty,
      fun _ h => absurd (refInChain_bounds h).2 (Nat.not_lt_of_ge (refInChain_bounds h).1),
      fun _ h => absurd (refInChain_bounds h).2 (by rw [h0_64]; exact Nat.not_lt_zero _),
      fun v hv => ?_, fun _ _ hlive _ _ => absurd hlive.1 (by omega), hm⟩
    dsimp only; rw [ite_eq_right (fun h => by have := h.1.1; omega)]
  · rintro JL ⟨r, mid, blen, ⟨⟩⟩ mL ⟨hmid_blen, hfr_mid, hr_dst, hblen_le,
      arCurr, bufCurr, rsnsCurr, har_len, hbuf_len, hrsns_len, hpre, hsuf,
      hmv_pre, hmv_rem, hmv_irred, hmv_buf, hirred_blk, hbuf_blk, hrsn_map, hbuf_rsns, hmL⟩ hLoop
    c0_hsplit
    · have hr_lt : r.toNat < dst.toNat := hc
      obtain ⟨rwRem, hclean_r, hsz3_r, hfit_r, hrw_step, hmv_rem'⟩ :=
        moveRangeChain_uncons hmv_rem hr_lt
      have hr2_eq : (r + 2#64).toNat = r.toNat + 2 := by
        rw [BitVec.toNat_add, h2_64, Nat.mod_eq_of_lt (by omega)]
      let hdr := arCurr[r.toNat]'(by rw [har_len]; omega)
      let sz := arCurr[(r + 2#64).toNat]'(by rw [har_len, hr2_eq]; omega)
      have hhdr_ar : arPre[r.toNat]? = some hdr := by
        dsimp [hdr]; rw [← hsuf r.toNat (Nat.le_refl _) hr_lt]
        exact List.getElem?_eq_getElem (by rw [har_len]; omega)
      have hsz_ar : arPre[r.toNat + 2]? = some sz := by
        have h1 : arCurr[(r + 2#64).toNat]? = some sz :=
          List.getElem?_eq_getElem (by rw [har_len, hr2_eq]; omega)
        rw [hr2_eq, hsuf (r.toNat + 2) (by omega) (by omega)] at h1; exact h1
      have hclean : (hdr &&& 0x00880000#32) = 0#32 := by rwa [hhdr_ar, Option.getD_some] at hclean_r
      have hsz3 : 3 ≤ sz.toNat := by rwa [hsz_ar, Option.getD_some] at hsz3_r
      have hfit : r.toNat + 3 + sz.toNat ≤ dst.toNat := by rwa [hsz_ar, Option.getD_some] at hfit_r
      have hclen_eq : (3 + sz.setWidth 64).toNat = 3 + sz.toNat := bv64_add3_zext_toNat sz
      have hr_next_eq : (r + (3 + sz.setWidth 64)).toNat = r.toNat + 3 + sz.toNat := by
        rw [BitVec.toNat_add, hclen_eq, Nat.mod_eq_of_lt (by omega), Nat.add_assoc]
      c0_hsteps_nogrp
      refine wp_join_group (ts := [i64, i64]) (fun ⟨mid', blen', ⟨⟩⟩ mNext =>
        EndBufInv c s arPre first_red dst bufPtr buf.length redWords R
          ⟨r + (3 + sz.setWidth 64), mid', blen', ()⟩ mNext) ?_ ?_
      · rintro _ ⟨mid', blen', ⟨⟩⟩ mNext hinv; c0_hsteps
        exact hLoop ⟨r + (3 + sz.setWidth 64), mid', blen', ()⟩ mNext
          (by dsimp only; rw [hr_next_eq]; omega) hinv
      · intro Js_next hJs_next; c0_hsplit
        · have hred : (hdr &&& 0x00400000#32) ≠ 0#32 := hc
          have hrw_eq : blen.toNat + (3 + sz.toNat) + rwRem = redWords := by
            rw [hhdr_ar, hsz_ar, Option.getD_some, Option.getD_some, ite_eq_left hred] at hrw_step
            omega
          c0_hsteps_nogrp
          refine wp_loop_inv (ts := [i64])
            (RedCopyInv c s arPre arCurr bufCurr rsnsCurr r blen bufPtr buf.length (3 + sz.toNat) R)
            (fun ⟨j, ⟨⟩⟩ _ => (3 + sz.setWidth 64).toNat - j.toNat)
            (fun Jc hCopy => by c0_hsteps; exact hCopy ⟨0#64, ⟨⟩⟩ mL ⟨Nat.zero_le _, bufCurr,
              hbuf_len, fun _ _ => rfl, fun _ hk => absurd hk (Nat.not_lt_zero _), hmL⟩)
            (fun Jc ⟨j, ⟨⟩⟩ mJ ⟨hj_le, bufC, hbufC_len, hbufC_pre, hbufC_cp, hmJ⟩ hCopy => ?_)
          c0_hsplit
          · have hj_lt : j.toNat < (3 + sz.setWidth 64).toNat := hc
            have hbj_eq : (blen + j).toNat = blen.toNat + j.toNat := by
              rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
            have hrj_eq : (r + j).toNat = r.toNat + j.toNat := by
              rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
            have hj1_eq : (j + 1#64).toNat = j.toNat + 1 := by
              rw [BitVec.toNat_add, h1_64, Nat.mod_eq_of_lt (by omega)]
            have hbj_lt : (blen + j).toNat < bufC.length := by rw [hbj_eq, hbufC_len]; omega
            have hrj_lt : (r + j).toNat < arCurr.length := by rw [hrj_eq, har_len]; omega
            c0_hsteps
            have hm_cp : (array (t := i32) c.pArena arCurr ⋆ array (t := i32) bufPtr
                (bufC.set (blen + j).toNat (arCurr[(r + j).toNat]'hrj_lt)) ⋆
                FullMemArenaOut c { s with core := { s.core with rsns := rsnsCurr } } ⋆ R) m := by
              simp only [sep_emp, sep_assoc] at hm ⊢
              rwa [sep_comm_l (array (t := i32) bufPtr _) (array (t := i32) c.pArena _)] at hm
            have hv_eq : arPre[r.toNat + j.toNat]? = some (arCurr[(r + j).toNat]'hrj_lt) := by
              rw [← hsuf (r.toNat + j.toNat) (by omega) (by omega), ← hrj_eq]
              exact List.getElem?_eq_getElem hrj_lt
            obtain ⟨hl1, hp1, hc1⟩ :=
              end_buf_red_copy_step hbufC_len hbj_eq hbj_lt hv_eq hbufC_pre hbufC_cp
            exact hCopy ⟨j + 1#64, ⟨⟩⟩ m (by dsimp only; rw [hj1_eq]; omega)
              ⟨by rw [hj1_eq]; omega, _, hl1, hp1, by simpa only [hj1_eq] using hc1, hm_cp⟩
          · have hj_eq : j.toNat = 3 + sz.toNat := by
              have h1 : ¬ j.toNat < (3 + sz.setWidth 64).toNat := hc; rw [hclen_eq] at h1; omega
            rw [hj_eq] at hbufC_cp; c0_hsteps_nogrp
            refine wp_join_group (ts := []) (fun _ mNext => RedHdrPost c s arPre arCurr bufCurr
              rsnsCurr first_red r dst blen bufPtr buf.length (3 + sz.toNat) R mNext) ?_ ?_
            · rintro _ ⟨⟩ mNext ⟨buf', hbl, hbpre, hbtail, hbcl, hbred, hblive, hbnone, hmN⟩
              c0_hsteps
              exact hJs_next ⟨mid, blen + (3 + sz.setWidth 64), ⟨⟩⟩ mNext
                (end_buf_red_step_inv huniq hcv_le hdst_cap hrw_buf hmid_blen hfr_mid hblen_le
                  har_len hbuf_len hrsns_len hpre hsuf hmv_pre hmv_irred hmv_buf hirred_blk
                  hbuf_blk hrsn_map hbuf_rsns hhdr_ar hsz_ar hclean hred hsz3 hfit
                  (by rw [hsz_ar, Option.getD_some] at hmv_rem'
                      simpa only [Nat.add_assoc] using hmv_rem')
                  hrw_eq hbl hbpre hbtail hbcl hbred hblive hbnone hmN)
            · intro Js_r hJs_r
              have hbl_lt : blen.toNat < bufC.length := by rw [hbufC_len]; omega
              have hbufC_hdr : bufC[blen.toNat]? = some hdr := by
                have h0 := hbufC_cp 0 (by omega); simp only [Nat.add_zero] at h0; rw [h0, hhdr_ar]
              c0_hsplit
              · have hfl_ne : (hdr &&& 0x00200000#32) ≠ 0#32 := hc
                c0_hsteps_nogrp
                refine wp_join_group (ts := [i32, Ty.bool])
                  (RedScanPost c s arPre arCurr bufCurr rsnsCurr first_red r dst blen bufPtr
                    buf.length (3 + sz.toNat) hdr R) ?_ ?_
                · rintro _ ⟨_, found, ⟨⟩⟩ mF
                    ⟨bufF, hbf_len, hbf_pre, hbf_hdr, hbf_tail, hbf_t, hbf_f, hmF⟩
                  c0_hsteps
                  · exact hJs_r () mF (end_buf_red_found_true hclean hred hfl_ne hbf_len hbf_pre
                      hbf_hdr hbf_tail (hbf_t hc) hmF)
                  · have hbf_lt : blen.toNat < bufF.length := by rw [hbf_len]; omega
                    have hmF' : (array (t := i32) c.pArena arCurr ⋆ array (t := i32) bufPtr
                        (bufF.set blen.toNat (hdr &&& ~~~0x00200000#32)) ⋆
                        FullMemArenaOut c { s with core := { s.core with rsns := rsnsCurr } } ⋆
                        R) m := by
                      simp only [sep_emp, sep_assoc] at hm ⊢
                      rwa [sep_comm_l (array (t := i32) bufPtr _)
                        (array (t := i32) c.pArena _)] at hm
                    exact hJs_r () m (end_buf_red_clr_post hbf_len hbf_lt hclean hred hbf_pre
                      hbf_tail (hbf_f hc).2 hmF')
                · intro Js_scan hJs_scan; c0_hsteps_nogrp
                  refine wp_loop_inv (ts := [i32]) (ScanLoopInv s arPre r sz.toNat mJ)
                    (fun ⟨j, ⟨⟩⟩ _ => sz.toNat - j.toNat) ?_ ?_
                  · intro Jsc hSc; c0_hsteps; exact hSc ⟨0#32, ⟨⟩⟩ mJ
                      ⟨rfl, Nat.zero_le _, fun _ hk => absurd hk (Nat.not_lt_zero _)⟩
                  rintro Jsc ⟨j, ⟨⟩⟩ mS ⟨hmS, hj_le, hno_k⟩ hSc
                  subst mS; c0_hsplit
                  · have hj_lt : j.toNat < sz.toNat := hc
                    have hj1_eq : (j + 1#32).toNat = j.toNat + 1 := by
                      rw [BitVec.toNat_add, h1_32, Nat.mod_eq_of_lt (by omega)]
                    have hrj3_eq : (r + 3#64 + j.setWidth 64).toNat = r.toNat + 3 + j.toNat := by
                      rw [BitVec.toNat_add, BitVec.toNat_add, h3_64,
                        zext_toNat (n := 64) j (by decide), Nat.mod_eq_of_lt (by omega),
                        Nat.mod_eq_of_lt (by omega)]
                    have hrj_mod :
                        (r.toNat + 3 + j.toNat) % 2 ^ 64 = r.toNat + 3 + j.toNat :=
                      Nat.mod_eq_of_lt (by omega)
                    have hrj3_lt : (r + 3#64 + j.setWidth 64).toNat < arCurr.length := by
                      rw [har_len, hrj3_eq]; omega
                    let lit := arCurr[(r + 3#64 + j.setWidth 64).toNat]'hrj3_lt
                    have hlit_ar : arPre[r.toNat + 3 + j.toNat]? = some lit := by
                      dsimp [lit]; rw [← hsuf (r.toNat + 3 + j.toNat) (by omega) (by omega),
                        ← hrj3_eq]; exact List.getElem?_eq_getElem hrj3_lt
                    let v32 := lit >>> 1#32
                    have hv_nat : v32.toNat = lit.toNat / 2 := lit_ushiftRight_one lit
                    c0_hsteps_nogrp
                    refine wp_join_group (ts := []) (fun ⟨⟩ mNext => mNext = mJ ∧
                      LitNotHitRsn arPre s.core.rsns s.core.vals s.core.cur_vars r.toNat
                        (r.toNat + 3 + j.toNat)) ?_ ?_
                    · rintro _ ⟨⟩ mN ⟨hmN, hmiss⟩; subst mN; c0_hsteps
                      exact hSc ⟨j + 1#32, ⟨⟩⟩ mJ (by dsimp only; rw [hj1_eq]; omega)
                        (scanLoopInv_succ hj_lt hj1_eq hno_k hmiss)
                    · intro Js_nxt hJs_nxt; c0_hsplit
                      · have hv_lt : v32.toNat < s.core.cur_vars := by
                          rw [hv_nat]; simpa [lit, h3_64, hrj_mod, hcv_mod] using hc
                        have hlit_lt : lit.toNat < 2 * s.core.cur_vars := lit_div2_lt hv_lt
                        c0_hsplit
                        · have hb_1 : s.core.vals[lit.toNat]? = some 1#8 :=
                            end_buf_val_eq_one hvals_len hcv_le hlit_lt hvals_tri
                              (by simpa [lit, h3_64, hrj_mod, h0_32] using hc)
                          have hrs_lt_c : (v32.setWidth 64).toNat < rsnsCurr.length := by
                            rw [zext_toNat (n := 64) v32 (by decide), hrsns_len]; omega
                          c0_hsteps_nogrp; c0_hsplit
                          · obtain ⟨r0s, hr0s_eq, hr0s_n⟩ := end_buf_rsn_hit_curr_hc hv_lt
                              hrs_len hrsns_len hcv_le (by omega)
                              (by simpa [lit, h3_64, hrj_mod] using hc) hrsn_map
                            have hbl1_eq : (blen + 1).toNat = blen.toNat + 1 := by
                              rw [BitVec.toNat_add, show (1 : BitVec 64).toNat = 1 from rfl,
                                Nat.mod_eq_of_lt (by omega)]
                            c0_hsteps
                            have hmF : (array (t := i32) c.pArena arCurr ⋆
                                array (t := i32) bufPtr (bufC.set (blen.toNat + 1) v32) ⋆
                                FullMemArenaOut c { s with core :=
                                  { s.core with rsns := rsnsCurr } } ⋆ R) m := by
                              simp only [sep_emp, sep_assoc] at hm ⊢; rw [← hbl1_eq]
                              rwa [sep_comm_l (array (t := i32) bufPtr _)
                                (array (t := i32) c.pArena _)] at hm
                            exact hJs_scan ⟨j, true, ⟨⟩⟩ m (end_buf_red_hit_buf (by omega) hsz3
                              hfit (Nat.le_trans hfr_mid (by omega)) hr_lt (by omega) hhdr_ar
                              hsz_ar hclean hfl_ne hj_lt hlit_ar hv_nat hv_lt hb_1 hr0s_eq hr0s_n
                              hmv_pre hbufC_len hbufC_pre hbufC_hdr hbufC_cp hmF)
                          · c0_hsteps; exact hJs_nxt () mJ ⟨rfl, end_buf_rsn_miss_curr_hc
                              hlit_ar hv_lt hcv_le hrs_len hrsns_len
                              (by simpa [lit, h3_64, hrj_mod] using hc) hrsn_map⟩
                        · c0_hsteps; exact hJs_nxt () mJ ⟨rfl, end_buf_val_litNotHit hlit_ar
                            hvals_len hcv_le hlit_lt hvals_tri
                            (by simpa [lit, h3_64, hrj_mod, h0_32] using hc)⟩
                      · have hv_ge : ¬ v32.toNat < s.core.cur_vars := by
                          rw [hv_nat]; simpa [lit, h3_64, hrj_mod, hcv_mod] using hc
                        c0_hsteps
                        exact hJs_nxt () mJ ⟨rfl, litNotHit_of_ge hlit_ar hv_nat hv_ge⟩
                  · have hj_eq : j.toNat = sz.toNat := by
                      have h1 : ¬ j.toNat < sz.toNat := by dsimp only [sz]; exact hc
                      omega
                    c0_hsteps; exact hJs_scan ⟨j, false, ⟨⟩⟩ mJ (end_buf_red_none_scan
                      hj_eq hsz_ar hno_k hbufC_len hbufC_pre hbufC_hdr hbufC_cp hmJ)
              · have hfl_eq : (hdr &&& 0x00200000#32) = 0#32 := hc
                c0_hsteps; exact hJs_r () mJ (end_buf_red_clr_zero hbufC_len hbl_lt hclean hred
                  hfl_eq hhdr_ar hbufC_hdr hbufC_pre (fun k _ hk2 => hbufC_cp k hk2) hmJ)
        · have hirred : (hdr &&& 0x00400000#32) = 0#32 := hc
          have hrw_eq : blen.toNat + rwRem = redWords := by
            rw [hhdr_ar, Option.getD_some, ite_eq_right (fun h => h hirred), Nat.zero_add]
              at hrw_step; omega
          c0_hsteps_nogrp
          refine wp_join_group (ts := []) (fun _ mI => IrredPost c s arPre arCurr bufCurr rsnsCurr
            first_red r mid dst bufPtr (3 + sz.toNat) hdr R mI) ?_ ?_
          · rintro _ ⟨⟩ mI ⟨ar', rsns', har'_len, har'_pre, har'_suf, _, har'_tail,
              hrsns'_len, hrsns'_ok, hmI⟩
            have hmid_lt : mid.toNat < ar'.length := by rw [har'_len]; omega
            c0_hsteps; let ar'' := ar'.set mid.toNat (hdr &&& ~~~0x00200000#32)
            have hm'' : (array (t := i32) c.pArena ar'' ⋆ array (t := i32) bufPtr bufCurr ⋆
                FullMemArenaOut c { s with core := { s.core with rsns := rsns' } } ⋆ R) m := by
              simp only [sep_emp, ← sep_assoc] at hm ⊢; exact hm
            obtain ⟨ha1, ha2, ha3, ha4, ha5⟩ := end_buf_irred_ar_set (hdr := hdr) har'_len hmid_lt
              (by omega) har'_pre har'_suf har'_tail
            exact hJs_next ⟨mid + (3 + sz.setWidth 64), blen, ⟨⟩⟩ m
              (end_buf_irred_step_inv huniq hcv_le hdst_cap hmid_blen hfr_mid hblen_le har_len
                hbuf_len hrsns_len hpre hsuf hmv_pre hmv_irred hmv_buf hirred_blk hbuf_blk hrsn_map
                hbuf_rsns hhdr_ar hsz_ar hclean hirred hsz3 hfit
                (by rw [hsz_ar, Option.getD_some] at hmv_rem'
                    simpa only [Nat.add_assoc] using hmv_rem')
                hrw_eq ha1 ha2 ha3 ha4 ha5 hrsns'_len hrsns'_ok hm'')
          · intro Js_i hJs_i; c0_hsplit
            · have hmid_lt_r : mid.toNat < r.toNat := by
                have hne_n : mid.toNat ≠ r.toNat := fun h => hc (BitVec.eq_of_toNat_eq h); omega
              c0_hsteps_nogrp
              refine wp_loop_inv (ts := [i64])
                (IrredCopyInv c s arPre arCurr bufCurr rsnsCurr r mid dst bufPtr (3 + sz.toNat) R)
                (fun ⟨j, ⟨⟩⟩ _ => (3 + sz.setWidth 64).toNat - j.toNat) ?_ ?_
              · intro Jc hCopy; c0_hsteps; exact hCopy ⟨0#64, ⟨⟩⟩ mL ⟨Nat.zero_le _, arCurr,
                  har_len, fun _ _ => rfl, fun _ _ _ => rfl, fun i hi _ hi3 => hsuf i (by omega)
                    hi3, fun _ hk => absurd hk (Nat.not_lt_zero _), hmL⟩
              · rintro Jc ⟨j, ⟨⟩⟩ mJ ⟨hj_le, arC, harC_len, harC_pre, harC_suf,
                  harC_rem, harC_cp, hmJ⟩ hCopy
                c0_hsplit
                · have hj_lt : j.toNat < (3 + sz.setWidth 64).toNat := hc
                  rw [hclen_eq] at hj_lt
                  have hmj_eq : (mid + j).toNat = mid.toNat + j.toNat := by
                    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
                  have hrj_eq : (r + j).toNat = r.toNat + j.toNat := by
                    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
                  have hj1_eq : (j + 1#64).toNat = j.toNat + 1 := by
                    rw [BitVec.toNat_add, h1_64, Nat.mod_eq_of_lt (by omega)]
                  have hmj_lt : (mid + j).toNat < arC.length := by rw [hmj_eq, harC_len]; omega
                  have hrj_lt : (r + j).toNat < arC.length := by rw [hrj_eq, harC_len]; omega
                  c0_hsteps; let arC' := arC.set (mid + j).toNat (arC[(r + j).toNat]'hrj_lt)
                  have hm_cp : (array (t := i32) c.pArena arC' ⋆ array (t := i32) bufPtr bufCurr ⋆
                      FullMemArenaOut c { s with core := { s.core with rsns := rsnsCurr } } ⋆ R)
                      m := by simp only [sep_emp, ← sep_assoc] at hm ⊢; exact hm
                  have harj_val :
                      arPre[r.toNat + j.toNat]? = some (arC[(r + j).toNat]'hrj_lt) := by
                    rw [← harC_rem (r.toNat + j.toNat) (Nat.le_refl _) (by omega) (by omega),
                      ← hrj_eq]; exact List.getElem?_eq_getElem hrj_lt
                  obtain ⟨hl1, hp1, hs1, hmr1, hcp1⟩ := end_buf_irred_copy_step_r harC_len
                    (by rw [← hmj_eq]; exact hmj_lt) hmid_lt_r hj_lt harj_val
                    harC_pre harC_suf harC_rem harC_cp
                  exact hCopy ⟨j + 1#64, ⟨⟩⟩ m (by dsimp only; rw [hclen_eq, hj1_eq]; omega)
                    ⟨by rw [hj1_eq]; omega, arC.set (mid.toNat + j.toNat) _,
                      by simpa only [hmj_eq] using hl1, by simpa only [hmj_eq] using hp1,
                      by simpa only [hmj_eq] using hs1,
                      by simpa only [hmj_eq, hj1_eq] using hmr1,
                      by simpa only [hmj_eq, hj1_eq] using hcp1,
                      by simpa only [arC', hmj_eq] using hm_cp⟩
                · have hj_eq : j.toNat = 3 + sz.toNat := by
                    have h1 : ¬ j.toNat < (3 + sz.setWidth 64).toNat := hc
                    rw [hclen_eq] at h1; omega
                  rw [hj_eq] at harC_cp
                  have harC_hdr : arC[mid.toNat]? = some hdr := by
                    have h0 := harC_cp 0 (by omega)
                    simp only [Nat.add_zero] at h0; rw [h0, hhdr_ar]
                  c0_hsteps_nogrp
                  refine wp_join_group (ts := []) (fun _ mNext => IrredRsnPost c s arPre arC
                    bufCurr rsnsCurr first_red r mid dst bufPtr R mNext) ?_ ?_
                  · rintro _ ⟨⟩ mNext ⟨rsns', hrsns'_len, hrsns'_ok, hmN⟩; c0_hsteps
                    exact hJs_i () mNext ⟨arC, rsns', harC_len, harC_pre, harC_suf, harC_hdr,
                      fun k _ hk2 => harC_cp k hk2, hrsns'_len, hrsns'_ok, hmN⟩
                  · intro Js_r hJs_r; c0_hsplit
                    · have hfl_ne : (hdr &&& 0x00200000#32) ≠ 0#32 := hc
                      c0_hsteps_nogrp
                      refine wp_join_group (ts := [i32]) (fun _ mR => IrredRsnPost c s arPre arC
                        bufCurr rsnsCurr first_red r mid dst bufPtr R mR) ?_ ?_
                      · rintro _ ⟨_, ⟨⟩⟩ mR ⟨rsns', hrsns'_len, hrsns'_ok, hmR⟩; c0_hsteps
                        exact hJs_r () mR ⟨rsns', hrsns'_len, hrsns'_ok, hmR⟩
                      · intro Js_scan hJs_scan; c0_hsteps_nogrp
                        refine wp_loop_inv (ts := [i32]) (ScanLoopInv s arPre r sz.toNat mJ)
                          (fun ⟨j2, ⟨⟩⟩ _ => sz.toNat - j2.toNat) ?_ ?_
                        · intro Jsc hSc; c0_hsteps; exact hSc ⟨0#32, ⟨⟩⟩ mJ
                            ⟨rfl, Nat.zero_le _, fun _ hk => absurd hk (Nat.not_lt_zero _)⟩
                        · rintro Jsc ⟨j2, ⟨⟩⟩ mS ⟨hmS, hj_le2, hno_k⟩ hSc
                          subst mS; c0_hsplit
                          · have hj_lt2 : j2.toNat < sz.toNat := hc
                            have hj1_eq2 : (j2 + 1#32).toNat = j2.toNat + 1 := by
                              rw [BitVec.toNat_add, h1_32, Nat.mod_eq_of_lt (by omega)]
                            have hmj3_eq : (mid + 3#64 + j2.setWidth 64).toNat =
                                mid.toNat + 3 + j2.toNat := by
                              rw [BitVec.toNat_add, BitVec.toNat_add, h3_64,
                                zext_toNat (n := 64) j2 (by decide),
                                Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
                            have hmj_mod :
                                (mid.toNat + 3 + j2.toNat) % 2 ^ 64 = mid.toNat + 3 + j2.toNat :=
                              Nat.mod_eq_of_lt (by omega)
                            have hmj3_lt : (mid + 3#64 + j2.setWidth 64).toNat < arC.length := by
                              rw [harC_len, hmj3_eq]; omega
                            let lit := arC[(mid + 3#64 + j2.setWidth 64).toNat]'hmj3_lt
                            have hlit_ar : arPre[r.toNat + 3 + j2.toNat]? = some lit := by
                              dsimp [lit]; rw [Nat.add_assoc (r.toNat),
                                ← harC_cp (3 + j2.toNat) (by omega), ← Nat.add_assoc (mid.toNat),
                                ← hmj3_eq]
                              exact List.getElem?_eq_getElem hmj3_lt
                            let v32 := lit >>> 1#32
                            have hv_nat : v32.toNat = lit.toNat / 2 := lit_ushiftRight_one lit
                            c0_hsteps_nogrp
                            refine wp_join_group (ts := []) (fun ⟨⟩ mNext => mNext = mJ ∧
                              LitNotHitRsn arPre s.core.rsns s.core.vals s.core.cur_vars r.toNat
                                (r.toNat + 3 + j2.toNat)) ?_ ?_
                            · rintro _ ⟨⟩ mN ⟨hmN, hmiss⟩; subst mN; c0_hsteps
                              exact hSc ⟨j2 + 1#32, ⟨⟩⟩ mJ (by dsimp only; rw [hj1_eq2]; omega)
                                (scanLoopInv_succ hj_lt2 hj1_eq2 hno_k hmiss)
                            · intro Js_nxt hJs_nxt; c0_hsplit
                              · have hv_lt : v32.toNat < s.core.cur_vars := by
                                  rw [hv_nat]; simpa [lit, h3_64, hmj_mod, hcv_mod] using hc
                                have hlit_lt : lit.toNat < 2 * s.core.cur_vars := lit_div2_lt hv_lt
                                c0_hsplit
                                · have hb_1 : s.core.vals[lit.toNat]? = some 1#8 :=
                                    end_buf_val_eq_one hvals_len hcv_le hlit_lt hvals_tri
                                      (by simpa [lit, h3_64, hmj_mod, h0_32] using hc)
                                  have hrs_lt_c : (v32.setWidth 64).toNat < rsnsCurr.length := by
                                    rw [zext_toNat (n := 64) v32 (by decide), hrsns_len]; omega
                                  c0_hsteps_nogrp; c0_hsplit
                                  · obtain ⟨r0s, hr0s_eq, hr0s_n⟩ := end_buf_rsn_hit_curr_hc hv_lt
                                      hrs_len hrsns_len hcv_le (by omega)
                                      (by simpa [lit, h3_64, hmj_mod] using hc) hrsn_map
                                    have hidx : (v32.setWidth 64).toNat = v32.toNat :=
                                      zext_toNat (n := 64) v32 (by decide)
                                    have hvs_lt : ((arC[(mid + 3#64 +
                                        j2.setWidth 64).toNat]'hmj3_lt >>> 1#32).setWidth
                                        64).toNat < rsnsCurr.length := by
                                      change (v32.setWidth 64).toNat < rsnsCurr.length
                                      rw [hidx, hrsns_len]; omega
                                    c0_hsteps
                                    let rsns' := rsnsCurr.set v32.toNat (BitVec.ofNat 32 mid.toNat)
                                    have hm_rsn : (FullMemArenaOut c { s with core :=
                                        { s.core with rsns := rsns' } } ⋆
                                        (array (t := i32) c.pArena arC ⋆ (array (t := i32)
                                          bufPtr bufCurr ⋆ (R ⋆ emp)))) m := by
                                      dsimp [rsns']; rw [← hidx]; exact hm
                                    exact hJs_scan ⟨j2, ()⟩ m (end_buf_irred_hit_rsn hmv_pre hhdr_ar
                                      hsz_ar hclean hfl_ne hsz3 hfit
                                      (Nat.le_trans hfr_mid (by omega)) hr_lt (by omega) hj_lt2
                                      hlit_ar hv_nat hv_lt hb_1 hr0s_eq hr0s_n hrsns_len hm_rsn)
                                  · c0_hsteps; exact hJs_nxt () mJ ⟨rfl, end_buf_rsn_miss_curr_hc
                                      hlit_ar hv_lt hcv_le hrs_len hrsns_len
                                      (by simpa [lit, h3_64, hmj_mod] using hc) hrsn_map⟩
                                · c0_hsteps; exact hJs_nxt () mJ ⟨rfl, end_buf_val_litNotHit hlit_ar
                                    hvals_len hcv_le hlit_lt hvals_tri
                                    (by simpa [lit, h3_64, hmj_mod, h0_32] using hc)⟩
                              · have hv_ge : ¬ v32.toNat < s.core.cur_vars := by
                                  rw [hv_nat]; simpa [lit, h3_64, hmj_mod, hcv_mod] using hc
                                c0_hsteps; exact hJs_nxt () mJ ⟨rfl, litNotHit_of_ge hlit_ar
                                  hv_nat hv_ge⟩
                          · have hj_eq2 : j2.toNat = sz.toNat := by
                              have h1 : ¬ j2.toNat < sz.toNat := by dsimp only [sz]; exact hc
                              omega
                            c0_hsteps; exact hJs_scan ⟨j2, ()⟩ mJ (end_buf_irred_none_scan hj_eq2
                              hsz_ar hno_k hrsns_len hmJ)
                    · have hfl_eq : (hdr &&& 0x00200000#32) = 0#32 := hc
                      c0_hsteps
                      exact hJs_r () mJ ⟨rsnsCurr, hrsns_len, Or.inr ⟨rfl, fun v hv hml hrs_n =>
                        absurd hfl_eq (by have h1 := hml.2.2.2.1
                                          rw [hrs_n, hhdr_ar, Option.getD_some] at h1; exact h1)⟩,
                        hmJ⟩
            · have hmid_eq : mid = r := hc
              have hmid_n : mid.toNat = r.toNat := congrArg BitVec.toNat hmid_eq; c0_hsteps
              exact hJs_i () mL (end_buf_irred_id_post har_len hrsns_len hr_lt hfit hmid_n
                hhdr_ar hsuf hmL)
    · have hr_eq : r.toNat = dst.toNat := by have := hc; omega
      rw [hr_eq] at hmid_blen hmv_rem hirred_blk hbuf_blk hrsn_map hbuf_rsns
      have hrw_rem : redWords - blen.toNat = 0 := moveRangeChain_empty_rw hmv_rem
      c0_hsteps_nogrp; c0_call hPass2
      obtain ⟨hp2_1, hp2_2, hp2_3, hp2_4, hp2_5, hp2_6, hp2_7⟩ := end_buf_exit_to_pass2_pre
        hfr_mid hdst_cap hbuf_bd hmid_blen (by omega) har_len hbuf_len hrsns_len hmv_buf
        hbuf_blk hrsn_map hbuf_rsns hmL
      refine ⟨c, s, arPre, arCurr, bufCurr, rsnsCurr, first_red, R, rfl, hlen, hp2_1, hp2_2,
        hp2_3, hp2_4, hp2_5, hp2_6, hp2_7,
        fun arOut rsnsOut fred' m' harOut hrsnsOut hp2_pre hp2_mv hp2_blk hp2_rsn hfred hm' => ?_⟩
      obtain ⟨hp1, hp2, hp3, hp4, hp5⟩ := end_buf_exit_to_pass2_post hfr_mid hdst_cap hmid_blen
        hpre hmv_irred hmv_buf hirred_blk hbuf_blk hrsn_map hp2_pre hp2_mv hp2_blk hp2_rsn
      exact hQ arOut bufCurr rsnsOut fred' mid.toNat m' harOut (by omega) hrsnsOut hfr_mid
        (by omega) hp1 hp2 hp3 hp4 hp5 (end_buf_fred_val hfred) hm'

end

end LeanQbe.T.Examples.Kissat.Proof.Collect
