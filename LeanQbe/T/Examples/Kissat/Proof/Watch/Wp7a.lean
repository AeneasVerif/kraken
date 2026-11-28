/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Watch.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Watch.Helpers
public import LeanQbe.T.Examples.Kissat.Src.Watch

import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts3
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics1
import LeanQbe.T.Examples.Kissat.Proof.Spec.MemBridges
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb

/-! # Watch WP Proofs Part 7a: `full_sort_bin_watches_fid` and `full_prioritize_binaries_m6`

Proves `Func.wp` for:
* `full_sort_bin_watches_fid` (`Watch.Spec.fullSortBinWatchesSpec`)
* `full_prioritize_binaries_m6` (`Watch.Spec.fullPrioritizeBinariesM6Spec`)
using `CanonicalEnv` (`Γ.Sat Spec.specs`). -/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Watch

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.C0Step
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Watch
open LeanQbe.T.Examples.Kissat.Proof.Spec
open Kraken.Bedrock2.Test
open scoped FullArenaTactics

public section

private theorem watchSliceOk_append {F_cur : List (List Nat)} {k : FullCoreState}
    {lit p n1 n2 : Nat}
    (h1 : WatchSliceOk F_cur k lit p n1) (h2 : WatchSliceOk F_cur k lit (p + n1) n2) :
    WatchSliceOk F_cur k lit p (n1 + n2) := by
  induction h1 with
  | empty => simpa using h2
  | @bin p rem w0 hp hflag hne hlt hent _ ih =>
    have h2' : WatchSliceOk F_cur k lit (p + 1 + rem) n2 := by
      simpa [Nat.add_assoc, Nat.add_comm 1 rem] using h2
    simpa [Nat.add_assoc, Nat.add_comm 1 n2] using
      WatchSliceOk.bin hp hflag hne hlt hent (ih h2')
  | @large p rem w0 cref hp hp1 hflag hlt href _ ih =>
    have h2' : WatchSliceOk F_cur k lit (p + 2 + rem) n2 := by
      simpa [Nat.add_assoc, Nat.add_comm 2 rem] using h2
    simpa [Nat.add_assoc, Nat.add_comm 2 n2] using
      WatchSliceOk.large hp hp1 hflag hlt href (ih h2')

private theorem watchSliceOk_snoc_bin {F_cur : List (List Nat)} {k : FullCoreState}
    {lit p n : Nat} {w0 : BitVec 32} (h1 : WatchSliceOk F_cur k lit p n)
    (hp : k.wstk[p + n]? = some w0) (hflag : (w0 &&& 0x80000000#32) ≠ 0#32)
    (hne : w0 ≠ 0xFFFFFFFF#32) (hlt : (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k.cur_vars)
    (hent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause [lit, (w0 &&& 0x7FFFFFFF#32).toNat])) :
    WatchSliceOk F_cur k lit p (n + 1) :=
  watchSliceOk_append h1 (WatchSliceOk.bin hp hflag hne hlt hent .empty)

private def LargeWatchBufOk (k : FullCoreState) (scr : List (BitVec 32)) (ln : Nat) : Prop :=
  ln % 2 = 0 ∧
  ∀ i, 2 * i + 1 < ln →
    ∃ w0 cr, scr[2 * i]? = some w0 ∧ scr[2 * i + 1]? = some cr ∧
      (w0 &&& 0x80000000#32) = 0#32 ∧ cr.toNat < 0x80000000 ∧
      cr.toNat ∈ fullArenaClauseRefsCore k

private theorem largeWatchBuf_to_slice {F_cur : List (List Nat)} {k : FullCoreState}
    {lit q ln : Nat} {scr : List (BitVec 32)} (hbuf : LargeWatchBufOk k scr ln)
    (hcopy : ∀ j < ln, k.wstk[q + j]? = scr[j]?) :
    WatchSliceOk F_cur k lit q ln := by
  suffices h : ∀ m q0 off, off + 2 * m = ln →
      (∀ j < 2 * m, k.wstk[q0 + j]? = scr[off + j]?) →
      (∀ i, off ≤ 2 * i → 2 * i + 1 < ln →
        ∃ w0 cr, scr[2 * i]? = some w0 ∧ scr[2 * i + 1]? = some cr ∧
          (w0 &&& 0x80000000#32) = 0#32 ∧ cr.toNat < 0x80000000 ∧
          cr.toNat ∈ fullArenaClauseRefsCore k) →
      off % 2 = 0 → WatchSliceOk F_cur k lit q0 (2 * m) by
    have hln : ln = 2 * (ln / 2) := by have := hbuf.1; omega
    rw [hln]
    exact h (ln / 2) q 0 (by omega) (fun j hj => by simpa using hcopy j (by omega))
      (fun i _ hi => hbuf.2 i hi) rfl
  intro m; induction m with
  | zero => intro _ _ _ _ _ _; exact .empty
  | succ m ih =>
    intro q0 off hoff hcp hall heven
    have hi : 2 * (off / 2) = off := by omega
    obtain ⟨w0, cr, hw0, hcr, hfl, hlt, href⟩ := hall (off / 2) (by omega) (by omega)
    rw [hi] at hw0 hcr
    have hq0 : k.wstk[q0]? = some w0 := by
      have := hcp 0 (by omega); simpa [hw0] using this
    have hq1 : k.wstk[q0 + 1]? = some cr := by
      have := hcp 1 (by omega); simpa [hcr] using this
    have htail := ih (q0 + 2) (off + 2) (by omega)
      (fun j hj => by
        have := hcp (j + 2) (by omega)
        simpa [Nat.add_assoc, Nat.add_comm 2 j] using this)
      (fun i hi1 hi2 => hall i (by omega) hi2) (by omega)
    simpa [Nat.mul_succ] using WatchSliceOk.large hq0 hq1 hfl hlt href htail

private theorem prio_largeBuf_snoc {k : FullCoreState} {scr : List (BitVec 32)} {ln : Nat}
    {w0 cr : BitVec 32} (hbuf : LargeWatchBufOk k scr ln) (hln_lt : ln + 1 < scr.length)
    (hfl : (w0 &&& 0x80000000#32) = 0#32) (hlt : cr.toNat < 0x80000000)
    (href : cr.toNat ∈ fullArenaClauseRefsCore k) :
    LargeWatchBufOk k ((scr.set ln w0).set (ln + 1) cr) (ln + 2) := by
  refine ⟨by have := hbuf.1; omega, fun i hi => ?_⟩
  by_cases hie : 2 * i = ln
  · refine ⟨w0, cr, ?_, ?_, hfl, hlt, href⟩
    · rw [hie, List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega)]
    · rw [hie, List.getElem?_set_self (by simp; omega)]
  · have hlt2 : 2 * i + 1 < ln := by have := hbuf.1; omega
    obtain ⟨w', cr', hw', hcr', hfl', hlt', href'⟩ := hbuf.2 i hlt2
    refine ⟨w', cr', ?_, ?_, hfl', hlt', href'⟩
    · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]; exact hw'
    · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]; exact hcr'

private theorem prio_replace_slice_sparse {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hsp : FullSparseInvW c F0 F_cur s) {l : Nat}
    (hl : l < 2 * s.core.cur_vars) {wstk' scr' : List (BitVec 32)}
    (hwl : wstk'.length = c.wcap) (hscl : scr'.length = c.scratch_cap)
    (hout : ∀ idx, (idx < fullWatchOff s l ∨ fullWatchOff s l + fullWatchSize s l ≤ idx) →
      wstk'[idx]? = s.core.wstk[idx]?)
    (hslice : WatchSliceOk F_cur { s.core with wstk := wstk' } l
      (fullWatchOff s l) (fullWatchSize s l)) :
    FullSparseInvW c F0 F_cur
      { s with core := { s.core with wstk := wstk' }
               scratch := { s.scratch with scratch_buf := scr' } } := by
  let s' : FullState :=
    { s with core := { s.core with wstk := wstk' }
             scratch := { s.scratch with scratch_buf := scr' } }
  have hw := hsp.2.1; have hdm := hsp.2.2.2.2.2
  have hmw := hw.watches; rw [modeWatchesInv_eq_watches hdm] at hmw
  have hlay := hmw.layout
  have hdm' : s'.core.dense_mode = 0#64 := hdm
  have hwat' : ModeWatchesInv F_cur s'.core := by
    rw [modeWatchesInv_eq_watches hdm']
    refine WatchesInv.of_slices hlay.bounds hlay.pos_off hlay.disjoint fun l2 hl2 => ?_
    by_cases heq : l2 = l
    · subst heq; exact hslice
    · refine (hmw.slices l2 hl2).mono (k := s.core) (k' := s'.core)
        (by rw [CNF.entails_def]; exact fun _ h => h)
        (Nat.le_refl _) (fun _ hr => hr) fun idx hi1 hi2 => ?_
      dsimp only [s']; unfold fullWatchOff fullWatchSize at hout
      have hoff2 : fullWatchOffCore s'.core l2 = fullWatchOffCore s.core l2 := rfl
      have hsz2 : fullWatchSizeCore s'.core l2 = fullWatchSizeCore s.core l2 := rfl
      rw [hoff2] at hi1 hi2; rw [hsz2] at hi2
      by_cases hsz0 : fullWatchSizeCore s.core l = 0
      · exact hout idx (by omega)
      · have hpos2 : 0 < fullWatchSizeCore s.core l2 := by omega
        have hdisj := hlay.disjoint l l2 hl hl2 (Ne.symm heq) (by omega) hpos2
        rcases hdisj with h1 | h2
        · exact hout idx (Or.inr (by omega))
        · exact hout idx (Or.inl (by omega))
  exact ⟨⟨{ hsp.1.core_ok with wstk_len_arr := hwl },
          { hsp.1.scratch_ok with scratch_buf_len := hscl }⟩,
    { hw with arena := { hw.arena with len_ok := hw.arena.len_ok }, watches := hwat' },
    hsp.2.2.1, hsp.2.2.2.1, hsp.2.2.2.2.1, hdm⟩

private def PrioPartInv (c : FullCfg) (F_cur : List (List Nat)) (s0 : FullState)
    (wstk_l : List (BitVec 32)) (l off sz : Nat) (st : Nat × Nat × Nat × List (BitVec 32) ×
      List (BitVec 32)) : Prop :=
  let (p, q, ln, wstk_p, scr_p) := st
  off ≤ q ∧ q ≤ p ∧ p ≤ off + sz ∧ (q - off) + ln = p - off ∧
  wstk_p.length = c.wcap ∧ scr_p.length = c.scratch_cap ∧
  (∀ idx, (idx < off ∨ p ≤ idx) → wstk_p[idx]? = wstk_l[idx]?) ∧
  WatchSliceOk F_cur { s0.core with wstk := wstk_p } l off (q - off) ∧
  WatchSliceOk F_cur { s0.core with wstk := wstk_p } l p (off + sz - p) ∧
  LargeWatchBufOk s0.core scr_p ln

private theorem prio_part_step_bin {c : FullCfg} {F_cur : List (List Nat)} {s0 : FullState}
    {wstk_l : List (BitVec 32)} {l off sz p q ln : Nat}
    {wstk_p scr_p : List (BitVec 32)}
    (hinv : PrioPartInv c F_cur s0 wstk_l l off sz (p, q, ln, wstk_p, scr_p))
    (hlt : p < off + sz) (hw_lt : p < wstk_p.length)
    (hbin : (wstk_p[p]'hw_lt &&& 0x80000000#32) ≠ 0#32) :
    PrioPartInv c F_cur s0 wstk_l l off sz
      (p + 1, q + 1, ln, wstk_p.set q (wstk_p[p]'hw_lt), scr_p) := by
  rcases hinv with ⟨hq_ge, hq_le, hp_le, hsum, hwpl, hspl, hout, hbin_p, hrem_p, hbuf_p⟩
  have hw0_at : wstk_p[p]? = some (wstk_p[p]'hw_lt) := List.getElem?_eq_getElem hw_lt
  generalize hrem_eq : off + sz - p = rem_n at hrem_p
  cases hrem_p with
  | empty => omega
  | @large _ _ w0' _ hw0' _ hfl' _ _ _ =>
    exact absurd (Option.some.inj (hw0_at.symm.trans hw0') ▸ hfl') hbin
  | @bin _ rem1 w0' hw0' _ hne_ff hlt_ot hent_ot htail =>
    have hw0_eq : wstk_p[p]'hw_lt = w0' := Option.some.inj (hw0_at.symm.trans hw0')
    let wstk_n := wstk_p.set q (wstk_p[p]'hw_lt)
    have hq_lt : q < wstk_p.length := by omega
    refine ⟨by omega, by omega, by omega, by omega, by simp [hwpl], hspl,
      fun idx hidx => ?_, ?_, ?_, hbuf_p⟩
    · rw [List.getElem?_set_ne (by
        rcases hidx with h1 | h2
        · omega
        · omega)]
      exact hout idx (by
        rcases hidx with h1 | h2
        · exact Or.inl (by omega)
        · exact Or.inr (by omega))
    · have hpref := hbin_p.mono (k := { s0.core with wstk := wstk_p })
        (k' := { s0.core with wstk := wstk_n })
        (by rw [CNF.entails_def]; exact fun _ h => h) (Nat.le_refl _) (fun _ hr => hr)
        fun idx hi1 hi2 => List.getElem?_set_ne (by omega)
      have hsn := watchSliceOk_snoc_bin hpref (by
        rw [show off + (q - off) = q by omega]
        dsimp only [wstk_n]
        rw [List.getElem?_set_self hq_lt, hw0_eq])
        (hw0_eq ▸ hbin) hne_ff hlt_ot hent_ot
      simpa [show q - off + 1 = q + 1 - off by omega] using hsn
    · have heq_r : rem1 = off + sz - (p + 1) := by omega
      rw [← heq_r]
      exact htail.mono (k := { s0.core with wstk := wstk_p })
        (k' := { s0.core with wstk := wstk_n })
        (by rw [CNF.entails_def]; exact fun _ h => h) (Nat.le_refl _) (fun _ hr => hr)
        fun idx hi1 _ => List.getElem?_set_ne (by omega)

private theorem prio_part_step_large {c : FullCfg} {F_cur : List (List Nat)} {s0 : FullState}
    {wstk_l : List (BitVec 32)} {l off sz p q ln : Nat}
    {wstk_p scr_p : List (BitVec 32)}
    (hinv : PrioPartInv c F_cur s0 wstk_l l off sz (p, q, ln, wstk_p, scr_p))
    (hend_le : off + sz ≤ c.wcap) (hlt : p < off + sz) (hsz_le : sz ≤ c.scratch_cap)
    (hlg : (wstk_p[p]'(by have := hinv.2.2.2.2.1; omega) &&& 0x80000000#32) = 0#32) :
    ∃ (hp1_w : p + 1 < wstk_p.length),
      p + 1 < off + sz ∧ ln + 1 < scr_p.length ∧
      PrioPartInv c F_cur s0 wstk_l l off sz
        (p + 2, q, ln + 2, wstk_p,
          (scr_p.set ln (wstk_p[p]'(by have := hinv.2.2.2.2.1; omega))).set (ln + 1)
            (wstk_p[p + 1]'hp1_w)) := by
  rcases hinv with ⟨hq_ge, hq_le, hp_le, hsum, hwpl, hspl, hout, hbin_p, hrem_p, hbuf_p⟩
  have hw_lt : p < wstk_p.length := by omega
  have hw0_at : wstk_p[p]? = some (wstk_p[p]'hw_lt) := List.getElem?_eq_getElem hw_lt
  generalize hrem_eq : off + sz - p = rem_n at hrem_p
  cases hrem_p with
  | empty => omega
  | @bin _ _ w0' hw0' hfl' =>
    exact absurd (Option.some.inj (hw0_at.symm.trans hw0') ▸ hlg) hfl'
  | @large _ rem2 w0' cr' hw0' hcr' _ hlt_cr href_cr htail =>
    have hp1_lt : p + 1 < off + sz := by omega
    have hp1_w : p + 1 < wstk_p.length := by omega
    have hln1_scr : ln + 1 < scr_p.length := by omega
    have hw0_eq : wstk_p[p]'hw_lt = w0' := Option.some.inj (hw0_at.symm.trans hw0')
    have hcr_eq : wstk_p[p + 1]'hp1_w = cr' := by
      change wstk_p[p + 1]? = some cr' at hcr'
      rw [List.getElem?_eq_getElem hp1_w] at hcr'; exact Option.some.inj hcr'
    refine ⟨hp1_w, hp1_lt, hln1_scr, hq_ge, by omega, by omega, by omega, hwpl, by simp [hspl],
      fun idx hidx => hout idx (by
        rcases hidx with h1 | h2
        · exact Or.inl h1
        · exact Or.inr (by omega)),
      hbin_p, ?_, ?_⟩
    · have heq_r : rem2 = off + sz - (p + 2) := by omega
      rwa [← heq_r]
    · rw [hw0_eq, hcr_eq]; exact prio_largeBuf_snoc hbuf_p hln1_scr (hw0_eq ▸ hlg) hlt_cr href_cr

private theorem prio_part_large_bad {F_cur : List (List Nat)} {s0 : FullState}
    {wstk_l wstk_p scr_p : List (BitVec 32)} {c : FullCfg} {l off sz p q ln : Nat}
    (hinv : PrioPartInv c F_cur s0 wstk_l l off sz (p, q, ln, wstk_p, scr_p))
    (hend_le : off + sz ≤ c.wcap) (hlt : p < off + sz)
    (hlg : (wstk_p[p]'(by have := hinv.2.2.2.2.1; omega) &&& 0x80000000#32) = 0#32)
    (hge : off + sz ≤ p + 1) : False := by
  have hrem_p := hinv.2.2.2.2.2.2.2.2.1
  have hwpl := hinv.2.2.2.2.1
  have hw_lt : p < wstk_p.length := by omega
  have hw0_at : wstk_p[p]? = some (wstk_p[p]'hw_lt) := List.getElem?_eq_getElem hw_lt
  generalize hrem_eq : off + sz - p = rem_n at hrem_p
  cases hrem_p with
  | empty => omega
  | @bin _ _ w0' hw0' hfl' => exact hfl' (Option.some.inj (hw0_at.symm.trans hw0') ▸ hlg)
  | @large => omega

theorem full_sort_bin_watches_fid_wp (Γ : Env) (_hΓ : Γ.Sat Spec.specs)
    (a : Tup Val [i64]) (m : Mem 64) (Q : Post []) (X : XPost) :
    Spec.fullSortBinWatchesSpec a m Q X → Func.wp Γ full_sort_bin_watches_fid_body a m Q X := by
  rcases a with ⟨h, ⟨⟩⟩
  rintro ⟨c, F0, F_cur, s, R, rfl, hsp, hm, hQ⟩
  unfold Func.wp full_sort_bin_watches_fid_body
  c0_hsteps
  have hmw := hsp.2.1.watches
  rw [modeWatchesInv_eq_watches hsp.2.2.2.2.2] at hmw
  exact hQ s.core.wstk m hsp.1.core_ok.wstk_len_arr hsp hmw hm

theorem full_prioritize_binaries_m6_wp (Γ : Env) (_hΓ : Γ.Sat Spec.specs)
    (a : Tup Val [i64]) (m : Mem 64) (Q : Post [.bool]) (X : XPost) :
    Spec.fullPrioritizeBinariesM6Spec a m Q X →
      Func.wp Γ full_prioritize_binaries_m6_body a m Q X := by
  rcases a with ⟨h, ⟨⟩⟩
  rintro ⟨c, F0, F_cur, s0, R, rfl, hsp0, hm0, hQ⟩
  have hcl0 := hsp0.1.core_ok
  have hmx := c.hmaxv; have hwc := c.hwcap; have hsc := c.hscr
  unfold dimacsBound at hmx hwc hsc
  have hcv_le := hcl0.cur_vars_le; have hwv_len := hcl0.wvec_len
  have h1_64 : (1 : BitVec 64).toNat = 1 := rfl
  have hcv_lt64 : s0.core.cur_vars < 2 ^ 64 := by omega
  have h2cv_lt64 : 2 * s0.core.cur_vars < 2 ^ 64 := by omega
  have hnlits : (BitVec.ofNat 64 s0.core.cur_vars <<< 1).toNat = 2 * s0.core.cur_vars := by
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcv_lt64,
      Nat.shiftLeft_eq, Nat.pow_one, Nat.mul_comm, Nat.mod_eq_of_lt h2cv_lt64]
  unfold Func.wp full_prioritize_binaries_m6_body
  c0_hstraight
  let InvOuter : Bool × Nat × List (BitVec 32) × List (BitVec 32) → Mem 64 → Prop :=
    fun st ml =>
      st.2.1 ≤ 2 * s0.core.cur_vars ∧
      let sl : FullState :=
        { s0 with core := { s0.core with wstk := st.2.2.1 }
                  scratch := { s0.scratch with scratch_buf := st.2.2.2 } }
      FullSparseInvW c F0 F_cur sl ∧ (FullMem c sl ⋆ R) ml
  apply wp_while_state (fun st => (st.1, BitVec.ofNat 64 st.2.1, ()))
    (fun st => 2 * s0.core.cur_vars - st.2.1) InvOuter
  · intro J hJ
    c0_hsteps
    exact hJ (true, 0, s0.core.wstk, s0.scratch.scratch_buf) m
      ⟨Nat.zero_le _, hsp0, hm0⟩
  · rintro J ⟨all_p, l_v, wstk_l, scr_l⟩ ml ⟨hl_le, hsp_l, hm_l⟩ ih
    dsimp only at hl_le hsp_l hm_l ⊢
    let sl : FullState :=
      { s0 with core := { s0.core with wstk := wstk_l }
                scratch := { s0.scratch with scratch_buf := scr_l } }
    change FullSparseInvW c F0 F_cur sl at hsp_l
    change (FullMem c sl ⋆ R) ml at hm_l
    have hl_bv : (BitVec.ofNat 64 l_v).toNat = l_v := Nat.mod_eq_of_lt (by omega)
    c0_hsplit
    · have hl_lt : l_v < 2 * s0.core.cur_vars := by
        simp only [Nat.mod_eq_of_lt (show l_v < 2 ^ 64 by omega),
          Nat.mod_eq_of_lt hcv_lt64, Nat.mod_eq_of_lt h2cv_lt64] at hc
        exact hc
      have hl_w0 : (BitVec.ofNat 64 l_v <<< 1).toNat = 2 * l_v := by
        rw [BitVec.toNat_shiftLeft, hl_bv, Nat.shiftLeft_eq, Nat.pow_one,
          Nat.mod_eq_of_lt (by omega), Nat.mul_comm]
      have hl_w1 : (BitVec.ofNat 64 l_v <<< 1 + 1).toNat = 2 * l_v + 1 := by
        rw [BitVec.toNat_add, hl_w0, h1_64, Nat.mod_eq_of_lt (by omega)]
      have hw0_lt : (BitVec.ofNat 64 l_v <<< 1).toNat < s0.core.wvec.length := by omega
      have hw1_lt : (BitVec.ofNat 64 l_v <<< 1 + 1).toNat < s0.core.wvec.length := by omega
      have hdm := hsp_l.2.2.2.2.2
      have hmw := hsp_l.2.1.watches; rw [modeWatchesInv_eq_watches hdm] at hmw
      have hbd := hmw.layout.bounds l_v hl_lt
      have hwl_le := hsp_l.1.core_ok.wlen_le
      have hwpl := hsp_l.1.core_ok.wstk_len_arr
      have hspl := hsp_l.1.scratch_ok.scratch_buf_len
      have h2l0 : 2 * l_v < s0.core.wvec.length := by omega
      have h2l1 : 2 * l_v + 1 < s0.core.wvec.length := by omega
      let off_n := fullWatchOff s0 l_v
      let sz_n := fullWatchSize s0 l_v
      have hoff_eq : (s0.core.wvec[(BitVec.ofNat 64 l_v <<< 1).toNat]'hw0_lt).toNat = off_n := by
        rw [list_getElem_congr hw0_lt hl_w0]
        unfold off_n fullWatchOff fullWatchOffCore
        rw [List.getElem?_eq_getElem h2l0, Option.getD_some]
      have hsz_eq : (s0.core.wvec[(BitVec.ofNat 64 l_v <<< 1 + 1).toNat]'hw1_lt).toNat = sz_n := by
        rw [list_getElem_congr hw1_lt hl_w1]
        unfold sz_n fullWatchSize fullWatchSizeCore
        rw [List.getElem?_eq_getElem h2l1, Option.getD_some]
      have hslice_l : WatchSliceOk F_cur sl.core l_v off_n sz_n := hmw.slices l_v hl_lt
      have hend_n : off_n + sz_n ≤ c.wcap := Nat.le_trans hbd hwl_le
      have hl1_bv : BitVec.ofNat 64 l_v + 1 = BitVec.ofNat 64 (l_v + 1) :=
        bv64_ofNat_add1 (by omega)
      c0_hstraight
      let InvJo : Bool × List (BitVec 32) × List (BitVec 32) → Mem 64 → Prop :=
        fun st mj =>
          let sn : FullState :=
            { s0 with core := { s0.core with wstk := st.2.1 }
                      scratch := { s0.scratch with scratch_buf := st.2.2 } }
          FullSparseInvW c F0 F_cur sn ∧ (FullMem c sn ⋆ R) mj
      apply wp_join_state (fun st => (st.1, ())) InvJo
      · intro _ ⟨ap_n, wstk_n, scr_n⟩ mj ⟨hsp_n, hm_n⟩
        dsimp only at hsp_n hm_n ⊢
        c0_hsteps
        rw [hl1_bv]
        exact ih (ap_n, l_v + 1, wstk_n, scr_n) mj
          (Nat.sub_lt_sub_left hl_lt (Nat.lt_succ_self l_v)) ⟨hl_lt, hsp_n, hm_n⟩
      · intro Jo hJo
        have hoff_64 : (BitVec.setWidth 64
            (s0.core.wvec[(BitVec.ofNat 64 l_v <<< 1).toNat]'hw0_lt)).toNat = off_n := by
          rw [BitVec.toNat_setWidth, hoff_eq, Nat.mod_eq_of_lt (by omega)]
        have hsz_64 : (BitVec.setWidth 64
            (s0.core.wvec[(BitVec.ofNat 64 l_v <<< 1 + 1).toNat]'hw1_lt)).toNat = sz_n := by
          rw [BitVec.toNat_setWidth, hsz_eq, Nat.mod_eq_of_lt (by omega)]
        have hend_64 : (BitVec.setWidth 64
              (s0.core.wvec[(BitVec.ofNat 64 l_v <<< 1).toNat]'hw0_lt) +
            BitVec.setWidth 64
              (s0.core.wvec[(BitVec.ofNat 64 l_v <<< 1 + 1).toNat]'hw1_lt)).toNat =
            off_n + sz_n := by
          rw [BitVec.toNat_add, hoff_64, hsz_64, Nat.mod_eq_of_lt (by omega)]
        have h_idx0_eq : 2 * (l_v % 2 ^ 64) % 2 ^ 64 = 2 * l_v := by
          rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        have h_wvec_l0 :
            sl.core.wvec[2 * (l_v % 2 ^ 64) % 2 ^ 64]'(by rw [h_idx0_eq]; exact h2l0) =
              s0.core.wvec[2 * l_v]'h2l0 :=
          list_getElem_congr _ h_idx0_eq
        have hoff_wv : (s0.core.wvec[2 * l_v]'h2l0).toNat = off_n := by
          unfold off_n fullWatchOff fullWatchOffCore
          rw [List.getElem?_eq_getElem h2l0, Option.getD_some]
        have h_idx1_eq : (2 * (l_v % 2 ^ 64) + (1 : BitVec 64).toNat) % 2 ^ 64 =
            2 * l_v + 1 := by
          rw [Nat.mod_eq_of_lt (by omega), h1_64, Nat.mod_eq_of_lt (by omega)]
        have h_wvec_l1 :
            sl.core.wvec[(2 * (l_v % 2 ^ 64) + (1 : BitVec 64).toNat) % 2 ^ 64]'(by
              rw [h_idx1_eq]; exact h2l1) = s0.core.wvec[2 * l_v + 1]'h2l1 :=
          list_getElem_congr _ h_idx1_eq
        have hsz_wv : (s0.core.wvec[2 * l_v + 1]'h2l1).toNat = sz_n := by
          unfold sz_n fullWatchSize fullWatchSizeCore
          rw [List.getElem?_eq_getElem h2l1, Option.getD_some]
        have h_end_raw :
            ((sl.core.wvec[2 * (l_v % 2 ^ 64) % 2 ^ 64]'(by rw [h_idx0_eq]; exact h2l0)).toNat +
              (sl.core.wvec[(2 * (l_v % 2 ^ 64) + (1 : BitVec 64).toNat) % 2 ^ 64]'(by
                rw [h_idx1_eq]; exact h2l1)).toNat) % 2 ^ 64 = off_n + sz_n := by
          rw [h_wvec_l0, h_wvec_l1, hoff_wv, hsz_wv, Nat.mod_eq_of_lt (by omega)]
        have hsc_lt64 : c.scratch_cap < 2 ^ 64 := by omega
        c0_hsplit
        · apply wp_join_state (fun st : Bool × List (BitVec 32) × List (BitVec 32) =>
              (st.1, ())) InvJo
          · intro _ ⟨ap_s, wstk_s, scr_s⟩ ms ⟨hsp_s, hm_s⟩
            c0_hsteps
            exact hJo (ap_s, wstk_s, scr_s) ms ⟨hsp_s, hm_s⟩
          · intro Js hJs
            c0_hsplit
            · c0_hsteps
              exact hJs (false, wstk_l, scr_l) ml ⟨hsp_l, hm_l⟩
            · have hsz_le_cap : sz_n ≤ c.scratch_cap := by
                simp only [Nat.mod_eq_of_lt hsc_lt64] at hc
                rw [h_wvec_l1, hsz_wv] at hc
                omega
              c0_hstraight
              let InvP : Nat × Nat × Nat × List (BitVec 32) × List (BitVec 32) →
                  Mem 64 → Prop := fun st mp =>
                PrioPartInv c F_cur s0 wstk_l l_v off_n sz_n st ∧
                (FullMem c { s0 with core := { s0.core with wstk := st.2.2.2.1 }
                                     scratch := { s0.scratch with scratch_buf := st.2.2.2.2 } } ⋆
                  R) mp
              apply wp_while_state
                (fun st => (BitVec.ofNat 64 st.1, BitVec.ofNat 64 st.2.1,
                  BitVec.ofNat 64 st.2.2.1, ()))
                (fun st => off_n + sz_n - st.1) InvP
              · intro Jp hJp
                c0_hsteps
                have hof_bv : BitVec.setWidth 64
                    (s0.core.wvec[(BitVec.ofNat 64 l_v <<< 1).toNat]'hw0_lt) =
                    BitVec.ofNat 64 off_n :=
                  BitVec.eq_of_toNat_eq
                    (by rw [hoff_64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])
                rw [hof_bv]
                exact hJp (off_n, off_n, 0, wstk_l, scr_l) ml
                  ⟨⟨Nat.le_refl _, Nat.le_refl _, by omega, by simp, hwpl, hspl, fun _ _ => rfl,
                    by rw [Nat.sub_self]; exact .empty,
                    by rw [show off_n + sz_n - off_n = sz_n by omega]; exact hslice_l,
                    ⟨rfl, fun _ hi => by simp at hi⟩⟩, hm_l⟩
              · rintro Jp ⟨p_v, q_v, ln_v, wstk_p, scr_p⟩ mp ⟨hinv_p, hm_p⟩ ihp
                clear hm_l hm0
                dsimp only at hinv_p hm_p ⊢
                rcases hinv_p with ⟨hq_ge, hq_le, hp_le, hsum, hwpl_p, hspl_p, hout_p,
                  hbin_p, hrem_p, hbuf_p⟩
                have hp_bv : (BitVec.ofNat 64 p_v).toNat = p_v := Nat.mod_eq_of_lt (by omega)
                have hq_bv : (BitVec.ofNat 64 q_v).toNat = q_v := Nat.mod_eq_of_lt (by omega)
                have hln_bv : (BitVec.ofNat 64 ln_v).toNat = ln_v := Nat.mod_eq_of_lt (by omega)
                c0_hsplit
                · have hp_lt : p_v < off_n + sz_n := by
                    rw [h_end_raw, Nat.mod_eq_of_lt (show p_v < 2 ^ 64 by omega)] at hc
                    exact hc
                  have hp_w : p_v < wstk_p.length := by omega
                  have hq_w : q_v < wstk_p.length := by omega
                  have hp1_bv : BitVec.ofNat 64 p_v + 1 = BitVec.ofNat 64 (p_v + 1) :=
                    BitVec.eq_of_toNat_eq (by
                      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, h1_64]
                      omega)
                  have hq1_bv : BitVec.ofNat 64 q_v + 1 = BitVec.ofNat 64 (q_v + 1) :=
                    BitVec.eq_of_toNat_eq (by
                      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, h1_64]
                      omega)
                  c0_hstraight
                  let InvJa : Nat × Nat × Nat × List (BitVec 32) × List (BitVec 32) →
                      Mem 64 → Prop := fun st ma =>
                    p_v < st.1 ∧ PrioPartInv c F_cur s0 wstk_l l_v off_n sz_n st ∧
                    (FullMem c { s0 with
                      core := { s0.core with wstk := st.2.2.2.1 }
                      scratch := { s0.scratch with scratch_buf := st.2.2.2.2 } } ⋆ R) ma
                  apply wp_join_state
                    (fun st => (BitVec.ofNat 64 st.1, BitVec.ofNat 64 st.2.1,
                      BitVec.ofNat 64 st.2.2.1, ())) InvJa
                  · rintro _ ⟨pa, qa, lna, wstk_a, scr_a⟩ ma ⟨hgt_a, hinv_a, hm_a⟩
                    c0_hsteps
                    exact ihp (pa, qa, lna, wstk_a, scr_a) ma (by omega) ⟨hinv_a, hm_a⟩
                  · intro Ja hJa
                    c0_hsplit
                    · have hbin : (wstk_p[p_v]'hp_w &&& 0x80000000#32) ≠ 0#32 := by
                        simp only [Nat.mod_eq_of_lt (show p_v < 2 ^ 64 by omega)] at hc
                        exact hc
                      c0_hsteps
                      rw [hp1_bv, hq1_bv]
                      have hm_next := ‹(FullMem c _ ⋆ R) _›
                      simp only [hp_bv, hq_bv] at hm_next
                      exact hJa (p_v + 1, q_v + 1, ln_v,
                        wstk_p.set q_v (wstk_p[p_v]'hp_w), scr_p) _
                        ⟨by omega, prio_part_step_bin ⟨hq_ge, hq_le, hp_le, hsum, hwpl_p,
                          hspl_p, hout_p, hbin_p, hrem_p, hbuf_p⟩ hp_lt hp_w hbin, hm_next⟩
                    · have hlg : (wstk_p[p_v]'hp_w &&& 0x80000000#32) = 0#32 := by
                        simp only [Nat.mod_eq_of_lt (show p_v < 2 ^ 64 by omega)] at hc
                        exact hc
                      c0_hstraight
                      let InvJb : Nat × Nat × List (BitVec 32) → Mem 64 → Prop := fun st mb =>
                        p_v < st.1 ∧ PrioPartInv c F_cur s0 wstk_l l_v off_n sz_n
                          (st.1, q_v, st.2.1, wstk_p, st.2.2) ∧
                        (FullMem c { s0 with
                          core := { s0.core with wstk := wstk_p }
                          scratch := { s0.scratch with scratch_buf := st.2.2 } } ⋆ R) mb
                      apply wp_join_state
                        (fun st => (BitVec.ofNat 64 st.1, BitVec.ofNat 64 st.2.1, ())) InvJb
                      · rintro _ ⟨pb, lnb, scr_b⟩ mb ⟨hgt_b, hinv_b, hm_b⟩
                        c0_hsteps
                        exact hJa (pb, q_v, lnb, wstk_p, scr_b) mb ⟨hgt_b, hinv_b, hm_b⟩
                      · intro Jb hJb
                        c0_hsplit
                        · have hstep := prio_part_step_large ⟨hq_ge, hq_le, hp_le, hsum, hwpl_p,
                            hspl_p, hout_p, hbin_p, hrem_p, hbuf_p⟩ hend_n hp_lt hsz_le_cap hlg
                          have hp1_w : p_v + 1 < wstk_p.length := hstep.1
                          have hln0_s : ln_v < scr_p.length := by omega
                          have hln1_s : ln_v + 1 < scr_p.length := hstep.2.2.1
                          have hp2_bv : BitVec.ofNat 64 p_v + 1 + 1 = BitVec.ofNat 64 (p_v + 2) :=
                            BitVec.eq_of_toNat_eq (by
                              simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow,
                                h1_64]; omega)
                          have hln2_bv : BitVec.ofNat 64 ln_v + 2 = BitVec.ofNat 64 (ln_v + 2) := by
                            have h2_64 : (2 : BitVec 64).toNat = 2 := rfl
                            exact BitVec.eq_of_toNat_eq (by
                              simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow,
                                h2_64]
                              omega)
                          have hp1_n : (BitVec.ofNat 64 p_v + 1).toNat = p_v + 1 := by
                            rw [hp1_bv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
                          have hln1_n : (BitVec.ofNat 64 ln_v + 1).toNat = ln_v + 1 := by
                            rw [BitVec.toNat_add, hln_bv, h1_64, Nat.mod_eq_of_lt (by omega)]
                          c0_hsteps
                          rw [hp2_bv, hln2_bv]
                          have hm_next := ‹(FullMem c _ ⋆ R) _›
                          simp only [hp_bv, hp1_n, hln_bv, hln1_n] at hm_next
                          exact hJb (p_v + 2, ln_v + 2,
                            (scr_p.set ln_v (wstk_p[p_v]'hp_w)).set (ln_v + 1)
                              (wstk_p[p_v + 1]'hp1_w))
                            _ ⟨by omega, hstep.2.2.2, hm_next⟩
                        · exfalso
                          have hge : off_n + sz_n ≤ p_v + 1 := by
                            rw [h_end_raw, h1_64,
                              Nat.mod_eq_of_lt (show p_v + 1 < 2 ^ 64 by omega)] at hc
                            omega
                          exact prio_part_large_bad ⟨hq_ge, hq_le, hp_le, hsum, hwpl_p, hspl_p,
                            hout_p, hbin_p, hrem_p, hbuf_p⟩ hend_n hp_lt hlg hge
                · have hp_eq : p_v = off_n + sz_n := by
                    rw [h_end_raw, Nat.mod_eq_of_lt (show p_v < 2 ^ 64 by omega)] at hc
                    omega
                  let InvC : Nat × List (BitVec 32) → Mem 64 → Prop := fun st mk =>
                    st.1 ≤ ln_v ∧ st.2.length = c.wcap ∧
                    (∀ idx, (idx < off_n ∨ off_n + sz_n ≤ idx) → st.2[idx]? = wstk_l[idx]?) ∧
                    (∀ idx, off_n ≤ idx → idx < q_v → st.2[idx]? = wstk_p[idx]?) ∧
                    (∀ j < st.1, st.2[q_v + j]? = scr_p[j]?) ∧
                    (FullMem c { s0 with core := { s0.core with wstk := st.2 }
                                         scratch := { s0.scratch with scratch_buf := scr_p } } ⋆
                      R) mk
                  apply wp_while_state (fun st => (BitVec.ofNat 64 st.1, ()))
                    (fun st => ln_v - st.1) InvC
                  · intro Jk hJk
                    c0_hsteps
                    exact hJk (0, wstk_p) mp ⟨Nat.zero_le _, hwpl_p, hp_eq ▸ hout_p,
                      fun _ _ _ => rfl, fun _ hj => by simp at hj, hm_p⟩
                  · rintro Jk ⟨k_v, wstk_k⟩ mk ⟨hk_le, hwkl, hout_k, hpref_k, hcp_k, hm_k⟩ ihk
                    clear hm_p
                    dsimp only at hk_le hwkl hout_k hpref_k hcp_k hm_k ⊢
                    have hk_bv : (BitVec.ofNat 64 k_v).toNat = k_v := Nat.mod_eq_of_lt (by omega)
                    c0_hsplit
                    · have hk_lt : k_v < ln_v := by
                        simp only [Nat.mod_eq_of_lt (show k_v < 2 ^ 64 by omega),
                          Nat.mod_eq_of_lt (show ln_v < 2 ^ 64 by omega)] at hc
                        exact hc
                      have hk_scr : k_v < scr_p.length := by omega
                      have hqk_w : q_v + k_v < wstk_k.length := by omega
                      have hk1_bv : BitVec.ofNat 64 k_v + 1 = BitVec.ofNat 64 (k_v + 1) :=
                        BitVec.eq_of_toNat_eq (by
                          simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, h1_64]
                          omega)
                      have hqk_n : (BitVec.ofNat 64 q_v + BitVec.ofNat 64 k_v).toNat =
                          q_v + k_v := by
                        rw [BitVec.toNat_add, hq_bv, hk_bv, Nat.mod_eq_of_lt (by omega)]
                      c0_hsteps
                      rw [hk1_bv]
                      have hm_next := ‹(FullMem c _ ⋆ R) _›
                      simp only [hk_bv, hqk_n] at hm_next
                      let wstk_n := wstk_k.set (q_v + k_v) (scr_p[k_v]'hk_scr)
                      refine ihk (k_v + 1, wstk_n) _ (by omega)
                        ⟨by omega, by simp [wstk_n, hwkl],
                          fun idx hidx => by
                            dsimp only [wstk_n]
                            rw [List.getElem?_set_ne (by rcases hidx with h1 | h2 <;> omega)]
                            exact hout_k idx hidx,
                          fun idx hi1 hi2 => by
                            dsimp only [wstk_n]
                            rw [List.getElem?_set_ne (by omega)]; exact hpref_k idx hi1 hi2,
                          fun j hj => by
                            dsimp only [wstk_n]
                            by_cases hje : j = k_v
                            · subst hje
                              rw [List.getElem?_set_self hqk_w, List.getElem?_eq_getElem hk_scr]
                            · rw [List.getElem?_set_ne (by omega)]; exact hcp_k j (by omega),
                          hm_next⟩
                    · have hk_eq : k_v = ln_v := by
                        simp only [Nat.mod_eq_of_lt (show k_v < 2 ^ 64 by omega),
                          Nat.mod_eq_of_lt (show ln_v < 2 ^ 64 by omega)] at hc
                        omega
                      c0_hsteps
                      have hq_add : off_n + (q_v - off_n) = q_v := by omega
                      have hsz_add : (q_v - off_n) + ln_v = sz_n := by omega
                      have hbin_k : WatchSliceOk F_cur { s0.core with wstk := wstk_k } l_v
                          off_n (q_v - off_n) :=
                        hbin_p.mono (k := { s0.core with wstk := wstk_p })
                          (k' := { s0.core with wstk := wstk_k })
                          (by rw [CNF.entails_def]; exact fun _ h => h) (Nat.le_refl _)
                          (fun _ hr => hr) fun idx hi1 hi2 => hpref_k idx hi1 (by omega)
                      have hlg_k : WatchSliceOk F_cur { s0.core with wstk := wstk_k } l_v
                          q_v ln_v :=
                        largeWatchBuf_to_slice (k := { s0.core with wstk := wstk_k })
                          (by simpa [LargeWatchBufOk, fullArenaClauseRefsCore] using hbuf_p)
                          (fun j hj => hcp_k j (by omega))
                      have hwa := watchSliceOk_append hbin_k (by rwa [hq_add])
                      rw [hsz_add] at hwa
                      exact hJs (all_p, wstk_k, scr_p) mk
                        ⟨prio_replace_slice_sparse hsp_l hl_lt hwkl hspl_p hout_k hwa, hm_k⟩
        · c0_hsteps
          exact hJo (all_p, wstk_l, scr_l) ml ⟨hsp_l, hm_l⟩
    · c0_hsteps
      exact hQ all_p wstk_l scr_l ml hsp_l hm_l

end

end LeanQbe.T.Examples.Kissat.Proof.Watch
