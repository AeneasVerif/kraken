/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Src.Collect
public import LeanQbe.T.Examples.Kissat.Proof.Collect.Spec
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
import LeanQbe.T.Examples.Kissat.Proof.Spec.WitnessInv
import LeanQbe.T.Examples.Kissat.Proof.Collect.Tactics
import LeanQbe.T.Examples.Kissat.Proof.Collect.HelpersMoveSweep
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.ControlComb
meta import LeanQbe.T.Logic.C0Step
meta import LeanQbe.T.Logic.C0HeadStep

/-!
# MoveRed Pass 2 WP Proof (`Proof.Collect.WpMoveRed0`)

Canonical `Func.wp` proof for `full_move_red_pass2_m6` from `Src.Collect`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Collect

open Std Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Collect
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Collect.Spec
open scoped LeanQbe.T.Examples.Kissat.Proof.Collect.M6Tactics2a

/-! ## 1. Pure Helpers for Pass 2 -/

private abbrev pass2RsnsState (s : FullState) (rsns : List (BitVec 32)) : FullState :=
  { s with core := { s.core with rsns := rsns } }

private theorem refInChain_next_of_range {ar : List (BitVec 32)} {p hi rw r : Nat}
    (hmv : MoveRangeChain ar p hi rw) (hrc : RefInChain ar p hi r)
    (hlt : r + 3 + (ar[r + 2]?.getD 0#32).toNat < hi) :
    RefInChain ar p hi (r + 3 + (ar[r + 2]?.getD 0#32).toNat) := by
  induction hmv with
  | empty => exact absurd hrc.bounds (by omega)
  | @step p hi rw h3 hfl hsz hfit htl ih =>
    cases hrc with
    | head =>
      cases htl with
      | empty => omega
      | step h3' hfl' hsz' hfit' _ => exact .tail h3 hfl hsz hfit (.head h3' hfl' hsz' hfit')
    | tail _ _ _ _ hrc' => exact .tail h3 hfl hsz hfit (ih hrc' hlt)

private theorem refInChain_disjoint {ar : List (BitVec 32)} {p hi r1 r2 : Nat}
    (h1 : RefInChain ar p hi r1) (h2 : RefInChain ar p hi r2) (hlt : r1 < r2) :
    r1 + 3 + (ar[r1 + 2]?.getD 0#32).toNat ≤ r2 := by
  induction h1 with
  | head _ _ _ _ =>
    cases h2 with
    | head => omega
    | tail _ _ _ _ h2' => exact h2'.bounds.1
  | tail _ _ _ _ h1' ih =>
    cases h2 with
    | head => have := h1'.bounds; omega
    | tail _ _ _ _ h2' => exact ih h2' hlt

private theorem pass2_hdr_clear_clean {hdr : BitVec 32}
    (hfl : (hdr &&& 0x00880000#32) = 0#32) :
    ((hdr &&& ~~~0x00200000#32) &&& 0x00880000#32) = 0#32 := by
  rw [BitVec.and_assoc,
    show (~~~0x00200000#32 &&& 0x00880000#32) = 0x00880000#32 from rfl, hfl]

private theorem pass2_hdr_clear_not_rsn (hdr : BitVec 32) :
    ((hdr &&& ~~~0x00200000#32) &&& 0x00200000#32) = 0#32 := by
  rw [BitVec.and_assoc,
    show (~~~0x00200000#32 &&& 0x00200000#32) = 0#32 from rfl, BitVec.and_zero]

private theorem pass2_hdr_clear_red {hdr : BitVec 32}
    (hred : (hdr &&& 0x00400000#32) ≠ 0#32) :
    ((hdr &&& ~~~0x00200000#32) &&& 0x00400000#32) ≠ 0#32 := by
  rwa [BitVec.and_assoc,
    show (~~~0x00200000#32 &&& 0x00400000#32) = 0x00400000#32 from rfl]

private def Pass2CopyInv (c : FullCfg) (s : FullState) (ar buf rsns : List (BitVec 32))
    (rpos dst bufPtr dest clen : BitVec 64) (R : Mem 64 → Prop)
    (p : Tup Val [i64]) (mJ : Mem 64) : Prop :=
  let (j, ()) := p
  j.toNat ≤ clen.toNat ∧
  ∃ arL : List (BitVec 32), arL.length = dst.toNat ∧
    (∀ k < dest.toNat, arL[k]? = ar[k]?) ∧
    (∀ k < j.toNat, arL[dest.toNat + k]? = buf[rpos.toNat + k]?) ∧
    (array (t := i32) c.pArena arL ⋆ array (t := i32) bufPtr buf ⋆
      FullMemArenaOut c (pass2RsnsState s rsns) ⋆ R) mJ

open Classical in
private theorem pass2_step_inv {c : FullCfg} {s : FullState}
    {arOrig ar1 buf rsns1 ar rsns rsns' arL : List (BitVec 32)}
    {first_red dst bufPtr : BitVec 64} {mid rlen : Nat} {R : Mem 64 → Prop}
    {rpos : BitVec 64} {hdr sz : BitVec 32} {m' : Mem 64}
    (hcv_le : s.core.cur_vars ≤ c.max_vars)
    (hmv_buf : MoveRangeChain buf 0 rlen rlen)
    (hbuf_refs : ∀ rp, RefInChain buf 0 rlen rp →
      let sz0 := (buf[rp + 2]?.getD 0#32).toNat
      (buf[rp]?.getD 0#32 &&& 0x00400000#32) ≠ 0#32 ∧
      ∃ src_c, RefInChain arOrig first_red.toNat dst.toNat src_c ∧
        (arOrig[src_c]?.getD 0#32 &&& 0x00400000#32) ≠ 0#32 ∧
        (arOrig[src_c + 2]?.getD 0#32).toNat = sz0 ∧
        (∀ j < sz0, buf[rp + 3 + j]? = arOrig[src_c + 3 + j]?) ∧
        ((buf[rp]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 →
          (buf[rp + 1]?.getD 0#32).toNat < s.core.cur_vars ∧
          s.core.rsns[(buf[rp + 1]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32 =
            BitVec.ofNat 32 src_c ∧
          MoveLiveRsn arOrig s.core.vals s.core.rsns first_red.toNat dst.toNat
            (buf[rp + 1]?.getD 0#32).toNat))
    (hrpos_lt : rpos.toNat < rlen) (hmid_dst : mid + rlen = dst.toNat)
    (hdst_cap : dst.toNat ≤ c.arena_cap)
    (hpre : ∀ i < mid, ar[i]? = ar1[i]?)
    (hmv : MoveRangeChain ar mid (mid + rpos.toNat) rpos.toNat)
    (hrc : RefInChain buf 0 rlen rpos.toNat)
    (hblk : ∀ r, RefInChain ar mid (mid + rpos.toNat) r →
      let sz0 := (ar[r + 2]?.getD 0#32).toNat
      (ar[r]?.getD 0#32 &&& 0x00200000#32) = 0#32 ∧ ar[r + 1]? = some 2#32 ∧
      ∃ rp, RefInChain buf 0 rlen rp ∧ r = mid + rp ∧
        (buf[rp + 2]?.getD 0#32).toNat = sz0 ∧
        ∀ j < sz0, ar[r + 3 + j]? = buf[rp + 3 + j]?)
    (hrsn : ∀ v < s.core.cur_vars,
      let r0 := s.core.rsns[v]?.getD 0xFFFFFFFF#32
      if MoveLiveRsn arOrig s.core.vals s.core.rsns first_red.toNat dst.toNat v ∧
          (arOrig[r0.toNat]?.getD 0#32 &&& 0x00400000#32) ≠ 0#32
      then ∃ rp, RefInChain buf 0 rlen rp ∧
          (buf[rp]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 ∧
          buf[rp + 1]?.getD 0#32 = BitVec.ofNat 32 v ∧
          (∀ rp2, RefInChain buf 0 rlen rp2 →
            (buf[rp2]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 →
            buf[rp2 + 1]?.getD 0#32 = BitVec.ofNat 32 v → rp2 = rp) ∧
          if rp < rpos.toNat then
            let r' := (rsns[v]?.getD 0xFFFFFFFF#32).toNat
            r' = mid + rp ∧ r' < dst.toNat ∧ r' < 0x80000000 ∧
            RefInChain ar mid (mid + rpos.toNat) r' ∧
            (ar[r' + 2]?.getD 0#32).toNat = (buf[rp + 2]?.getD 0#32).toNat ∧
            ∀ j < (buf[rp + 2]?.getD 0#32).toNat, ar[r' + 3 + j]? = buf[rp + 3 + j]?
          else rsns[v]?.getD 0xFFFFFFFF#32 = r0
      else rsns[v]?.getD 0xFFFFFFFF#32 = rsns1[v]?.getD 0xFFFFFFFF#32)
    (hhdr : buf[rpos.toNat]? = some hdr) (hsz : buf[rpos.toNat + 2]? = some sz)
    (harL : arL.length = dst.toNat) (hrsns : rsns.length = c.max_vars)
    (harL_pre : ∀ k < mid + rpos.toNat, arL[k]? = ar[k]?)
    (harL_cp : ∀ k < 3 + sz.toNat, arL[mid + rpos.toNat + k]? = buf[rpos.toNat + k]?)
    (hrsns'_len : rsns'.length = c.max_vars)
    (hrsns'_ok :
      ((hdr &&& 0x00200000#32) ≠ 0#32 → ∃ v32, buf[rpos.toNat + 1]? = some v32 ∧
        v32.toNat < s.core.cur_vars ∧
        rsns' = rsns.set v32.toNat (BitVec.ofNat 32 (mid + rpos.toNat))) ∧
      ((hdr &&& 0x00200000#32) = 0#32 → rsns' = rsns))
    (hm' : (array (t := i32) c.pArena
        ((arL.set (mid + rpos.toNat) (hdr &&& ~~~0x00200000#32)).set
          (mid + rpos.toNat + 1) 2#32) ⋆
        array (t := i32) bufPtr buf ⋆
        FullMemArenaOut c (pass2RsnsState s rsns') ⋆ R) m') :
    MovePass2Inv c s arOrig ar1 buf rsns1 first_red dst bufPtr mid rlen R
      (rpos + (3 + sz.setWidth 64), ()) m' := by
  have har_cap := c.harena; have hmax := c.hmaxv
  unfold dimacsBound at har_cap hmax
  have hch := refInChain_of_moveRangeChain hmv_buf hrc
  have hsz_buf : (buf[rpos.toNat + 2]?.getD 0#32).toNat = sz.toNat := by
    rw [hsz, Option.getD_some]
  have hsz3 : 3 ≤ sz.toNat := hsz_buf ▸ hch.2.2.1
  have hfit : rpos.toNat + 3 + sz.toNat ≤ rlen := hsz_buf ▸ hch.2.2.2
  have hfl_hdr : (hdr &&& 0x00880000#32) = 0#32 := by simpa [hhdr] using hch.2.1
  have hred_hdr : (hdr &&& 0x00400000#32) ≠ 0#32 := by
    simpa [hhdr] using (hbuf_refs rpos.toNat hrc).1
  have hrpos1_eq : (rpos + (3 + sz.setWidth 64)).toNat = rpos.toNat + 3 + sz.toNat := by
    have hz : (sz.setWidth 64).toNat = sz.toNat := zext_toNat sz (by decide)
    rw [BitVec.toNat_add, BitVec.toNat_add, show (3 : BitVec 64).toNat = 3 from rfl, hz,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.add_assoc]
  let dest := mid + rpos.toNat
  let ar1' := arL.set dest (hdr &&& ~~~0x00200000#32)
  let ar' := ar1'.set (dest + 1) 2#32
  have har'_len : ar'.length = dst.toNat := by
    dsimp [ar', ar1']
    rw [List.length_set, List.length_set, harL]
  have hpre' : ∀ i < dest, ar'[i]? = ar[i]? := fun i hi => by
    dsimp [ar', ar1', dest]
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
    exact harL_pre i hi
  have har'_0 : ar'[dest]? = some (hdr &&& ~~~0x00200000#32) := by
    dsimp [ar', ar1', dest]
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega)]
  have har'_1 : ar'[dest + 1]? = some 2#32 := by
    dsimp [ar', ar1', dest]
    rw [List.getElem?_set_self (by rw [List.length_set, harL]; omega)]
  have har'_tail : ∀ k, 2 ≤ k → k < 3 + sz.toNat → ar'[dest + k]? = buf[rpos.toNat + k]? :=
    fun k hk1 hk2 => by
      dsimp [ar', ar1', dest]
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
      exact harL_cp k hk2
  have har'_2 : ar'[dest + 2]? = some sz := by
    rw [har'_tail 2 (by omega) (by omega), hsz]
  have hfl' : (ar'[dest]?.getD 0#32 &&& 0x00880000#32) = 0#32 := by
    rw [har'_0, Option.getD_some]; exact pass2_hdr_clear_clean hfl_hdr
  have hred' : (ar'[dest]?.getD 0#32 &&& 0x00400000#32) ≠ 0#32 := by
    rw [har'_0, Option.getD_some]; exact pass2_hdr_clear_red hred_hdr
  have hsz' : 3 ≤ (ar'[dest + 2]?.getD 0#32).toNat := by
    rw [har'_2, Option.getD_some]; exact hsz3
  have hmv_pre : MoveRangeChain ar' mid dest rpos.toNat := hmv.congr fun i _ hi2 => hpre' i hi2
  have hmv' : MoveRangeChain ar' mid (mid + (rpos.toNat + 3 + sz.toNat))
      (rpos.toNat + 3 + sz.toNat) := by
    have hsn := moveRangeChain_snoc hmv_pre (p' := mid + (rpos.toNat + 3 + sz.toNat))
      (by dsimp [dest]; omega) hfl' hsz' (by rw [har'_2, Option.getD_some]; dsimp [dest]; omega)
    rw [ite_eq_left hred', har'_2, Option.getD_some] at hsn
    simpa [Nat.add_assoc] using hsn
  have hrc'_dest : RefInChain ar' mid (mid + (rpos.toNat + 3 + sz.toNat)) dest :=
    refInChain_append_right hmv_pre
      (.head (by dsimp [dest]; omega) hfl' hsz'
        (by rw [har'_2, Option.getD_some]; dsimp [dest]; omega))
  refine ⟨by omega, hmid_dst, ar', rsns', har'_len, hrsns'_len,
    fun i hi => (hpre' i (by dsimp [dest]; omega)).trans (hpre i hi),
    by rw [hrpos1_eq]; exact hmv', fun hlt => ?_, fun r hr => ?_, fun v hv => ?_, hm'⟩
  · rw [hrpos1_eq] at hlt ⊢
    simpa only [hsz_buf] using refInChain_next_of_range hmv_buf hrc (by omega)
  · rw [hrpos1_eq] at hr
    rcases refInChain_split hmv_pre hr with hr_prev | hr_new
    · have hr_ar := hr_prev.congr fun i _ hi2 => (hpre' i hi2).symm
      have hb_ar := hr_ar.bounds
      obtain ⟨hf, h1, rp, hrp, heq, hszp, hcp⟩ := hblk r hr_ar
      have hsz_eq : (ar'[r + 2]?.getD 0#32).toNat = (ar[r + 2]?.getD 0#32).toNat := by
        rw [hpre' (r + 2) (by omega)]
      refine ⟨by rw [hpre' r (by omega)]; exact hf,
        by rw [hpre' (r + 1) (by omega)]; exact h1, rp, hrp, heq,
        by rw [hsz_eq]; exact hszp,
        fun j hj => by
          rw [hsz_eq] at hj
          rw [hpre' (r + 3 + j) (by omega)]
          exact hcp j hj⟩
    · cases hr_new with
      | head =>
        refine ⟨by rw [har'_0, Option.getD_some]; exact pass2_hdr_clear_not_rsn hdr,
          har'_1, rpos.toNat, hrc, rfl, by rw [hsz, har'_2],
          fun j hj => by
            rw [har'_2, Option.getD_some] at hj
            simpa only [Nat.add_assoc] using har'_tail (3 + j) (by omega) (by omega)⟩
      | tail _ _ _ _ hr_tl =>
        exfalso; have := hr_tl.bounds; rw [har'_2, Option.getD_some] at this; omega
  · dsimp only
    have hprev := hrsn v hv
    by_cases hcond : MoveLiveRsn arOrig s.core.vals s.core.rsns first_red.toNat dst.toNat v ∧
        (arOrig[(s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat]?.getD 0#32 &&& 0x00400000#32) ≠ 0#32
    · rw [ite_eq_left hcond] at hprev ⊢
      obtain ⟨rp, hrp, hrp_fl, hrp_v, huniq, hrest⟩ := hprev
      refine ⟨rp, hrp, hrp_fl, hrp_v, huniq, ?_⟩
      by_cases hlt_old : rp < rpos.toNat
      · have hlt_new : rp < (rpos + (3 + sz.setWidth 64)).toNat := by omega
        rw [ite_eq_left hlt_old] at hrest; rw [ite_eq_left hlt_new]
        obtain ⟨hr', hlt_dst, hlt_31, hrc_old, hsz_old, hcp_old⟩ := hrest
        have hrsns_keep : rsns'[v]?.getD 0xFFFFFFFF#32 = rsns[v]?.getD 0xFFFFFFFF#32 := by
          by_cases hfl0 : (hdr &&& 0x00200000#32) = 0#32
          · rw [hrsns'_ok.2 hfl0]
          · obtain ⟨v32, hv32, _, hrs_set⟩ := hrsns'_ok.1 hfl0
            have hne : v32.toNat ≠ v := fun he => by
              have hv_eq : buf[rpos.toNat + 1]?.getD 0#32 = BitVec.ofNat 32 v := by
                rw [hv32, Option.getD_some, ← he]
                apply BitVec.eq_of_toNat_eq; exact (bv32_ofNat_toNat v32.isLt).symm
              have := huniq rpos.toNat hrc (by simpa [hhdr] using hfl0) hv_eq
              omega
            rw [hrs_set, List.getElem?_set_ne hne]
        have hkeep_nat : (rsns'[v]?.getD 0xFFFFFFFF#32).toNat =
            (rsns[v]?.getD 0xFFFFFFFF#32).toNat := congrArg BitVec.toNat hrsns_keep
        have hrc_ar : RefInChain ar mid (mid + rpos.toNat) (mid + rp) := by
          simpa [hr'] using hrc_old
        have hcb := hrc_ar.bounds
        have hsz_match : (ar'[mid + rp + 2]?.getD 0#32).toNat =
            (buf[rp + 2]?.getD 0#32).toNat := by
          rw [hpre' (mid + rp + 2) (by dsimp [dest]; omega)]
          simpa [hr'] using hsz_old
        have hrc_ar' : RefInChain ar' mid (mid + (rpos + (3 + sz.setWidth 64)).toNat)
            (mid + rp) :=
          refInChain_append_left (by rw [hrpos1_eq]; omega)
            (hrc_ar.congr fun i _ hi2 => hpre' i hi2)
        refine ⟨by rw [hkeep_nat]; exact hr', by rw [hkeep_nat]; exact hlt_dst,
          by rw [hkeep_nat]; exact hlt_31, by rw [hkeep_nat, hr']; exact hrc_ar',
          by rw [hkeep_nat, hr']; exact hsz_match,
          fun j hj => by
            rw [hkeep_nat, hr']
            rw [hr'] at hsz_old hcp_old
            rw [hpre' (mid + rp + 3 + j) (by rw [hsz_old] at hcb; dsimp [dest]; omega)]
            exact hcp_old j hj⟩
      · by_cases heq : rp = rpos.toNat
        · subst heq
          have hlt_new : rpos.toNat < (rpos + (3 + sz.setWidth 64)).toNat := by omega
          rw [ite_eq_left hlt_new]
          have hfl_ne : (hdr &&& 0x00200000#32) ≠ 0#32 := by simpa [hhdr] using hrp_fl
          obtain ⟨v32, hv32, hv32_lt, hrs_set⟩ := hrsns'_ok.1 hfl_ne
          have hv_eq : v32.toNat = v := by
            rw [hv32, Option.getD_some] at hrp_v
            have h1 := congrArg BitVec.toNat hrp_v
            rwa [bv32_ofNat_toNat (by omega)] at h1
          have hrs_self : (rsns'[v]?.getD 0xFFFFFFFF#32).toNat = dest := by
            rw [hrs_set, ← hv_eq, List.getElem?_set_self (by omega), Option.getD_some,
              bv32_ofNat_toNat (by omega)]
          refine ⟨hrs_self, by rw [hrs_self]; dsimp [dest]; omega,
            by rw [hrs_self]; dsimp [dest]; omega,
            by rw [hrs_self, hrpos1_eq]; exact hrc'_dest,
            by rw [hrs_self, har'_2, hsz],
            fun j hj => by
              rw [hrs_self]
              rw [hsz, Option.getD_some] at hj
              simpa only [Nat.add_assoc] using har'_tail (3 + j) (by omega) (by omega)⟩
        · have hdisj := refInChain_disjoint hrc hrp (by omega)
          rw [hsz_buf] at hdisj
          have hge_new : ¬ (rp < (rpos + (3 + sz.setWidth 64)).toNat) := by omega
          rw [ite_eq_right hge_new]
          rw [ite_eq_right hlt_old] at hrest
          by_cases hfl0 : (hdr &&& 0x00200000#32) = 0#32
          · rw [hrsns'_ok.2 hfl0]; exact hrest
          · obtain ⟨v32, hv32, _, hrs_set⟩ := hrsns'_ok.1 hfl0
            have hne : v32.toNat ≠ v := fun he => by
              have hv_eq : buf[rpos.toNat + 1]?.getD 0#32 = BitVec.ofNat 32 v := by
                rw [hv32, Option.getD_some, ← he]
                apply BitVec.eq_of_toNat_eq; exact (bv32_ofNat_toNat v32.isLt).symm
              have := huniq rpos.toNat hrc (by simpa [hhdr] using hfl0) hv_eq
              omega
            rw [hrs_set, List.getElem?_set_ne hne]
            exact hrest
    · rw [ite_eq_right hcond] at hprev ⊢
      by_cases hfl0 : (hdr &&& 0x00200000#32) = 0#32
      · rw [hrsns'_ok.2 hfl0]; exact hprev
      · obtain ⟨v32, hv32, _, hrs_set⟩ := hrsns'_ok.1 hfl0
        obtain ⟨_, src_c, hrc_src, hred_src, _, _, hlive_fn⟩ := hbuf_refs rpos.toNat hrc
        obtain ⟨_, hrs32, hlive32⟩ := hlive_fn (by simpa [hhdr] using hfl0)
        rw [hv32, Option.getD_some] at hrs32 hlive32
        have hsrc_lt := hrc_src.bounds
        have hrs_nat : (s.core.rsns[v32.toNat]?.getD 0xFFFFFFFF#32).toNat = src_c := by
          rw [hrs32, bv32_ofNat_toNat (by omega)]
        have hne : v32.toNat ≠ v := fun he => hcond (by
          rw [← he, hrs_nat]; exact ⟨hlive32, hred_src⟩)
        rw [hrs_set, List.getElem?_set_ne hne]
        exact hprev

/-! ## 2. `full_move_red_pass2_m6_wp` -/

public section

open Classical in
theorem full_move_red_pass2_m6_wp (Γ : Env) :
    ∀ a m Q X, fullMoveRedPass2Spec a m Q X →
      Func.wp Γ full_move_red_pass2_m6_body a m Q X := by
  rintro ⟨h, mid, rlen, dst, bufPtr, ⟨⟩⟩ m Q X
    ⟨c, s, arOrig, ar1, buf, rsns1, first_red, R, rfl, hlen, hfr_mid, hdst_cap, hrlen_buf,
     hbuf_bd, hmv_buf, hbuf_refs, hinv0, hQ⟩
  have hdb : dimacsBound = 2 ^ 28 := rfl
  have har_cap := c.harena; have hmax := c.hmaxv
  have hcv_le := hlen.core_ok.cur_vars_le; have hrs_len := hlen.core_ok.rsns_len
  have h1_64 : (1 : BitVec 64).toNat = 1 := rfl
  have h2_64 : (2 : BitVec 64).toNat = 2 := rfl
  have h3_64 : (3 : BitVec 64).toNat = 3 := rfl
  obtain ⟨hrpos0, hmid_dst0, ar0, rsns0, har0, hrsns0, hpre0, hmv0, hnxt0, hblk0, hrsn0, hm0⟩ :=
    hinv0
  unfold Func.wp full_move_red_pass2_m6_body
  c0_hsteps_nogrp
  refine wp_loop_inv (ts := [i64])
    (MovePass2Inv c s arOrig ar1 buf rsns1 first_red dst bufPtr mid.toNat rlen.toNat R)
    (fun ⟨rpos, ⟨⟩⟩ _ => rlen.toNat - rpos.toNat) (fun JL hLoop => ?_) ?_
  · c0_hsteps
    exact hLoop ⟨0#64, ⟨⟩⟩ m ⟨hrpos0, hmid_dst0, ar0, rsns0, har0, hrsns0, hpre0, hmv0, hnxt0,
      hblk0, hrsn0, hm0⟩
  · rintro JL ⟨rpos, ⟨⟩⟩ mL
      ⟨hrpos, hmid_dst, ar, rsns, har, hrsns, hpre, hmv, hnxt, hblk, hrsn, hmL⟩ hLoop
    c0_hsplit
    · have hrpos_lt : rpos.toNat < rlen.toNat := hc
      have hrc := hnxt hrpos_lt
      have hch := refInChain_of_moveRangeChain hmv_buf hrc
      have hr0_lt : rpos.toNat < buf.length := by omega
      have hr1_eq : (rpos + 1).toNat = rpos.toNat + 1 := by
        rw [BitVec.toNat_add, h1_64, Nat.mod_eq_of_lt (by omega)]
      have hr2_eq : (rpos + 2).toNat = rpos.toNat + 2 := by
        rw [BitVec.toNat_add, h2_64, Nat.mod_eq_of_lt (by omega)]
      have hr1_lt : (rpos + 1).toNat < buf.length := by rw [hr1_eq]; omega
      have hr2_lt : (rpos + 2).toNat < buf.length := by rw [hr2_eq]; omega
      let hdr := buf[rpos.toNat]'hr0_lt
      let sz := buf[(rpos + 2).toNat]'hr2_lt
      have hsz_val : buf[rpos.toNat + 2]? = some sz := by
        rw [← hr2_eq]; exact List.getElem?_eq_getElem hr2_lt
      have hsz3 : 3 ≤ sz.toNat := by
        have h1 := hch.2.2.1; rw [hsz_val, Option.getD_some] at h1; exact h1
      have hfit : rpos.toNat + 3 + sz.toNat ≤ rlen.toNat := by
        have h1 := hch.2.2.2; rw [hsz_val, Option.getD_some] at h1; exact h1
      have hclen_eq : (3 + sz.setWidth 64).toNat = 3 + sz.toNat := by
        rw [BitVec.toNat_add, h3_64, zext_toNat sz (by decide), Nat.mod_eq_of_lt (by omega)]
      have hdest_eq : (mid + rpos).toNat = mid.toNat + rpos.toNat := by
        rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
      c0_hsteps_nogrp
      refine wp_loop_inv (ts := [i64])
        (Pass2CopyInv c s ar buf rsns rpos dst bufPtr (mid + rpos) (3 + sz.setWidth 64) R)
        (fun ⟨j, ⟨⟩⟩ _ => (3 + sz.setWidth 64).toNat - j.toNat) (fun Jc hCopy => ?_) ?_
      · c0_hsteps
        exact hCopy ⟨0#64, ⟨⟩⟩ mL ⟨Nat.zero_le _, ar, har, fun _ _ => rfl,
          fun _ hk => absurd hk (Nat.not_lt_zero _), hmL⟩
      · rintro Jc ⟨j, ⟨⟩⟩ mJ ⟨hj_le, arL, harL, harL_pre, harL_cp, hmJ⟩ hCopy
        c0_hsplit
        · have hj_lt : j.toNat < (3 + sz.setWidth 64).toNat := hc
          have hdj_eq : (mid + rpos + j).toNat = (mid + rpos).toNat + j.toNat := by
            rw [BitVec.toNat_add, hdest_eq, Nat.mod_eq_of_lt (by omega)]
          have hrj_eq : (rpos + j).toNat = rpos.toNat + j.toNat := by
            rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
          have hdj_lt : (mid + rpos + j).toNat < arL.length := by rw [hdj_eq, harL]; omega
          have hrj_lt : (rpos + j).toNat < buf.length := by rw [hrj_eq]; omega
          have hj1_eq : (j + 1).toNat = j.toNat + 1 := by
            rw [BitVec.toNat_add, h1_64, Nat.mod_eq_of_lt (by omega)]
          c0_hsteps
          have hm_step : (array (t := i32) c.pArena
              (arL.set (mid + rpos + j).toNat (buf[(rpos + j).toNat]'hrj_lt)) ⋆
              (array (t := i32) bufPtr buf ⋆
                (FullMemArenaOut c (pass2RsnsState s rsns) ⋆ (R ⋆ emp)))) m :=
            by assumption
          simp only [sep_emp, ← sep_assoc] at hm_step
          refine hCopy ⟨j + 1, ⟨⟩⟩ m (by simp; omega)
            ⟨by rw [hj1_eq]; omega,
              arL.set (mid + rpos + j).toNat (buf[(rpos + j).toNat]'hrj_lt),
              by simp [harL], fun k hk => ?_, fun k hk => ?_, hm_step⟩
          · rw [List.getElem?_set_ne (by rw [hdj_eq]; omega)]
            exact harL_pre k hk
          · rw [hj1_eq] at hk
            by_cases hkj : k = j.toNat
            · subst hkj
              rw [hdj_eq, List.getElem?_set_self (by rw [← hdj_eq]; exact hdj_lt),
                ← hrj_eq, List.getElem?_eq_getElem hrj_lt]
            · rw [List.getElem?_set_ne (by rw [hdj_eq]; omega)]
              exact harL_cp k (Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hk) hkj)
        · have hr2_mod : (rpos.toNat + 2) % 2 ^ 64 = rpos.toNat + 2 := Nat.mod_eq_of_lt (by omega)
          have hsz_at : buf[rpos.toNat + 2]'(by omega) = sz :=
            Option.some.inj ((List.getElem?_eq_getElem (by omega)).symm.trans hsz_val)
          simp only [h3_64, h2_64, hr2_mod, hsz_at,
            Nat.mod_eq_of_lt (by omega : 3 + sz.toNat < 2 ^ 64)] at hc
          rw [hclen_eq] at hj_le
          have hj_eq : j.toNat = 3 + sz.toNat := by omega
          rw [hj_eq] at harL_cp
          rw [hdest_eq] at harL_pre harL_cp
          have hdest_lt : (mid + rpos).toNat < arL.length := by rw [hdest_eq, harL]; omega
          have hdest1_eq : (mid + rpos + 1).toNat = (mid + rpos).toNat + 1 := by
            rw [BitVec.toNat_add, h1_64, hdest_eq, Nat.mod_eq_of_lt (by omega)]
          have hdest1_lt : (mid + rpos + 1).toNat <
              (arL.set (mid + rpos).toNat (hdr &&& ~~~0x00200000#32)).length := by
            rw [List.length_set, hdest1_eq, hdest_eq, harL]; omega
          c0_hsteps_nogrp
          refine wp_join_group (ts := []) (fun () mR => ∃ rsns' : List (BitVec 32),
            rsns'.length = c.max_vars ∧
            (((hdr &&& 0x00200000#32) ≠ 0#32 → ∃ v32, buf[rpos.toNat + 1]? = some v32 ∧
              v32.toNat < s.core.cur_vars ∧
              rsns' = rsns.set v32.toNat (BitVec.ofNat 32 (mid.toNat + rpos.toNat))) ∧
             ((hdr &&& 0x00200000#32) = 0#32 → rsns' = rsns)) ∧
            (array (t := i32) c.pArena arL ⋆ array (t := i32) bufPtr buf ⋆
              FullMemArenaOut c (pass2RsnsState s rsns') ⋆ R) mR) ?_ ?_
          · rintro _ ⟨⟩ mR ⟨rsns', hrsns', hrs_ok, hmR⟩
            c0_hsteps
            have hnxt_eq : (rpos + (3 + sz.setWidth 64)).toNat = rpos.toNat + 3 + sz.toNat := by
              rw [BitVec.toNat_add, hclen_eq, Nat.mod_eq_of_lt (by omega), Nat.add_assoc]
            have h1 : (array (t := i32) c.pArena
                  ((arL.set (mid + rpos).toNat (hdr &&& ~~~0x00200000#32)).set
                    (mid + rpos + 1).toNat 2#32) ⋆
                (array (t := i32) bufPtr buf ⋆
                  (FullMemArenaOut c (pass2RsnsState s rsns') ⋆ (R ⋆ emp)))) m :=
              by assumption
            simp only [sep_emp, ← sep_assoc, hdest_eq, hdest1_eq] at h1
            exact hLoop ⟨rpos + (3 + sz.setWidth 64), ⟨⟩⟩ m (by simp; omega)
              (pass2_step_inv hcv_le hmv_buf hbuf_refs hrpos_lt hmid_dst hdst_cap hpre hmv hrc
                hblk hrsn (List.getElem?_eq_getElem hr0_lt) hsz_val
                harL hrsns harL_pre harL_cp hrsns' hrs_ok h1)
          · intro Js hJs
            c0_hsplit
            · have hfl_ne : (hdr &&& 0x00200000#32) ≠ 0#32 := hc
              obtain ⟨_, src_c, _, _, _, _, hlive_fn⟩ := hbuf_refs rpos.toNat hrc
              have hlive := hlive_fn (by
                simpa [hdr, List.getElem?_eq_getElem hr0_lt, Option.getD_some] using hfl_ne)
              let v32 := buf[(rpos + 1).toNat]'hr1_lt
              have hv32_val : buf[rpos.toNat + 1]? = some v32 := by
                rw [← hr1_eq]; exact List.getElem?_eq_getElem hr1_lt
              have hv32_lt : v32.toNat < s.core.cur_vars := by
                have h1 := hlive.1; rw [hv32_val, Option.getD_some] at h1; exact h1
              have hv32_r : (v32.setWidth 64).toNat < rsns.length := by
                rw [zext_toNat v32 (by decide), hrsns]; omega
              c0_hsteps
              · have hm_out : (FullMemArenaOut c (pass2RsnsState s
                      (rsns.set (v32.setWidth 64).toNat ((mid + rpos).truncate 32))) ⋆
                    (array (t := i32) c.pArena arL ⋆
                      (array (t := i32) bufPtr buf ⋆
                        (R ⋆ emp)))) m := by assumption
                simp only [sep_emp] at hm_out
                rw [sep_comm_l (FullMemArenaOut c _) (array (t := i32) c.pArena arL),
                  sep_comm_l (FullMemArenaOut c _) (array (t := i32) bufPtr buf)] at hm_out
                simp only [← sep_assoc] at hm_out
                refine hJs () m ⟨rsns.set (v32.setWidth 64).toNat ((mid + rpos).truncate 32),
                  by simp [hrsns], ⟨fun _ => ⟨v32, hv32_val, hv32_lt, ?_⟩,
                    fun h0 => absurd h0 hfl_ne⟩,
                  hm_out⟩
                have hidx : (v32.setWidth 64).toNat = v32.toNat := zext_toNat v32 (by decide)
                have hval : (mid + rpos).truncate 32 =
                    BitVec.ofNat 32 (mid.toNat + rpos.toNat) := by
                  apply BitVec.eq_of_toNat_eq
                  rw [BitVec.toNat_setWidth, hdest_eq, bv32_ofNat_toNat (by omega),
                    Nat.mod_eq_of_lt (by omega)]
                rw [hidx, hval]
              · exfalso
                rw [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64),
                  Nat.mod_eq_of_lt (Nat.lt_trans (BitVec.isLt _) (by decide))] at hc
                exact absurd hv32_lt hc
            · have hfl_eq : (hdr &&& 0x00200000#32) = 0#32 := hc
              c0_hsteps
              exact hJs () mJ ⟨rsns, hrsns, ⟨fun h => absurd hfl_eq h, fun _ => rfl⟩, hmJ⟩
    · have hrpos_eq : rpos.toNat = rlen.toNat := by have := hc; omega
      rw [hrpos_eq] at hmv hblk hrsn
      have hrsn' : ∀ v < s.core.cur_vars,
          let r0 := s.core.rsns[v]?.getD 0xFFFFFFFF#32
          if MoveLiveRsn arOrig s.core.vals s.core.rsns first_red.toNat dst.toNat v ∧
              (arOrig[r0.toNat]?.getD 0#32 &&& 0x00400000#32) ≠ 0#32
          then ∃ rp, RefInChain buf 0 rlen.toNat rp ∧
              (buf[rp]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 ∧
              buf[rp + 1]?.getD 0#32 = BitVec.ofNat 32 v ∧
              (∀ rp2, RefInChain buf 0 rlen.toNat rp2 →
                (buf[rp2]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 →
                buf[rp2 + 1]?.getD 0#32 = BitVec.ofNat 32 v → rp2 = rp) ∧
              let r' := (rsns[v]?.getD 0xFFFFFFFF#32).toNat
              r' = mid.toNat + rp ∧ r' < dst.toNat ∧ r' < 0x80000000 ∧
              RefInChain ar mid.toNat (mid.toNat + rlen.toNat) r' ∧
              (ar[r' + 2]?.getD 0#32).toNat = (buf[rp + 2]?.getD 0#32).toNat ∧
              ∀ j < (buf[rp + 2]?.getD 0#32).toNat, ar[r' + 3 + j]? = buf[rp + 3 + j]?
          else rsns[v]?.getD 0xFFFFFFFF#32 = rsns1[v]?.getD 0xFFFFFFFF#32 := fun v hv => by
        have h1 := hrsn v hv
        dsimp only at h1 ⊢
        by_cases hcond : MoveLiveRsn arOrig s.core.vals s.core.rsns first_red.toNat dst.toNat v ∧
            (arOrig[(s.core.rsns[v]?.getD 0xFFFFFFFF#32).toNat]?.getD 0#32 &&&
              0x00400000#32) ≠ 0#32
        · rw [ite_eq_left hcond] at h1 ⊢
          obtain ⟨rp, hrp, hfl, hv', hu, hres⟩ := h1
          have hrp_lt : rp < rlen.toNat := (refInChain_of_moveRangeChain hmv_buf hrp).1
          rw [ite_eq_left hrp_lt] at hres
          exact ⟨rp, hrp, hfl, hv', hu, hres⟩
        · rw [ite_eq_right hcond] at h1 ⊢; exact h1
      c0_hsteps_nogrp
      refine wp_join_group (ts := [i64]) (fun ⟨fred', ⟨⟩⟩ m' =>
        m' = mL ∧ fred' = if mid.toNat < dst.toNat then mid else 0xFFFFFFFF#64) ?_ ?_
      · rintro _ ⟨fred', ⟨⟩⟩ _ ⟨rfl, rfl⟩
        c0_hsteps
        have hm_out : (FullMemArenaOut c { (pass2RsnsState s rsns) with core :=
              { (pass2RsnsState s rsns).core with first_reducible :=
                if mid.toNat < dst.toNat then mid else 0xFFFFFFFF#64 } } ⋆
            (array (t := i32) c.pArena ar ⋆ (array (t := i32) bufPtr buf ⋆ (R ⋆ emp)))) m :=
          by assumption
        simp only [sep_emp] at hm_out
        rw [sep_comm_l (FullMemArenaOut c _) (array (t := i32) c.pArena ar),
          sep_comm_l (FullMemArenaOut c _) (array (t := i32) bufPtr buf)] at hm_out
        simp only [← sep_assoc] at hm_out
        exact hQ ar rsns _ m har hrsns hpre hmv hblk hrsn' rfl hm_out
      · intro _ hJf
        c0_hsteps_nogrp; c0_hsplit
        · c0_hsteps; exact hJf ⟨mid, ⟨⟩⟩ mL ⟨rfl, (ite_eq_left hc).symm⟩
        · c0_hsteps; exact hJf ⟨0xFFFFFFFF#64, ⟨⟩⟩ mL ⟨rfl, (ite_eq_right hc).symm⟩

end

end LeanQbe.T.Examples.Kissat.Proof.Collect
