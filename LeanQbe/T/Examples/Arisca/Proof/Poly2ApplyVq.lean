/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Arisca.Proof.Poly2ApplyPhases
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ProofKit
import LeanQbe.T.Logic.MemLemmas
import Kraken.Separation

/-!
# ARiSCA `ar_apply` Loop 3 WP Phase (`Arisca.Proof.Poly2ApplyVq`)

Proves `apply_vq_loop_wp` (Loop 3: `r < nR` partner-conflict table populating `vq_off`,
`vq_skip`, and `vq`), landing cleanly at `applyAfterLoop3Expr`.
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

private theorem vqRowPreOk_step {nNets sym : Nat}
    {partnerArr curRp curRm vqOffL vqL vqN : List (BitVec 32)}
    {vqSkipL : List (BitVec 8)} {Valid : (Nat → Bool) → Prop}
    {r : BitVec 32} {q qNext : BitVec 64} {sk : BitVec 32} {mrOff : BitVec 32}
    (hmr_eq : mrOff.toNat = (curRm.getD r.toNat 0#32).toNat)
    (hr_vqoff : r.toNat < vqOffL.length) (hr_skip : r.toNat < vqSkipL.length)
    (hq_qn : q.toNat ≤ qNext.toNat) (hq32 : (q.setWidth 32 : BitVec 32).toNat = q.toNat)
    (hsk_cases : sk = 1#32 ∨ sk = 0#32)
    (hsk_van : sk = 1#32 → ∀ σ, Valid σ → monoValL σ (symListAt curRp mrOff.toNat) = false)
    (hvq_pre : ∀ p < q.toNat, vqN.getD p 0#32 = vqL.getD p 0#32)
    (hvq_new : sk = 0#32 → ∀ p, q.toNat ≤ p → p < qNext.toNat →
      ∃ w ∈ symListAt curRp mrOff.toNat,
        w % 2 = 0 ∧ w / 2 < nNets ∧
        partnerArr.getD (w / 2) 0#32 ≠ cNone32 ∧
        (vqN.getD p 0#32).toNat = 2 * (partnerArr.getD (w / 2) 0#32).toNat ∧
        (vqN.getD p 0#32).toNat ≠ sym)
    (hPre : ∀ idx < r.toNat, VqRowPreOk nNets sym partnerArr curRp curRm
      vqOffL vqL vqSkipL Valid r.toNat idx q.toNat) :
    ∀ idx < r.toNat + 1, VqRowPreOk nNets sym partnerArr curRp curRm
      (vqOffL.set r.toNat (q.setWidth 32)) vqN (vqSkipL.set r.toNat (sk.setWidth 8))
      Valid (r.toNat + 1) idx qNext.toNat := by
  intro idx hidx
  by_cases hidx_r : idx = r.toNat
  · subst hidx_r
    constructor
    · intro hnz
      rw [getD_set_eq vqSkipL 0#8 (sk.setWidth 8) hr_skip, ite_eq_left rfl] at hnz
      have hsk1 : sk = 1#32 := by
        rcases hsk_cases with h1 | h0
        · exact h1
        · exfalso; apply hnz; rw [h0]; rfl
      rw [← hmr_eq]; exact hsk_van hsk1
    · intro hz
      rw [getD_set_eq vqSkipL 0#8 (sk.setWidth 8) hr_skip, ite_eq_left rfl] at hz
      have hsk0 : sk = 0#32 := by
        rcases hsk_cases with h1 | h0
        · exfalso; rw [h1] at hz; simp at hz
        · exact h0
      simp only [↓reduceIte]
      rw [getD_set_eq vqOffL 0#32 (q.setWidth 32) hr_vqoff, ite_eq_left rfl, hq32]
      refine ⟨hq_qn, le_refl _, fun p hp1 hp2 => ?_⟩
      rw [← hmr_eq]; exact hvq_new hsk0 p hp1 hp2
  · have hprev := hPre idx (by omega)
    constructor
    · intro hnz
      rw [getD_set_eq vqSkipL 0#8 (sk.setWidth 8) hr_skip,
        ite_eq_right (by omega)] at hnz
      exact hprev.1 hnz
    · intro hz
      rw [getD_set_eq vqSkipL 0#8 (sk.setWidth 8) hr_skip,
        ite_eq_right (by omega)] at hz
      have hpr := hprev.2 hz
      dsimp only at hpr ⊢
      rw [getD_set_eq vqOffL 0#32 (q.setWidth 32) hr_vqoff, ite_eq_right (by omega)]
      by_cases hlast : idx + 1 = r.toNat
      · have hne : ¬ (idx + 1 = r.toNat + 1) := by omega
        simp only [hlast, ↓reduceIte] at hpr
        simp only [hne, ↓reduceIte]
        rw [getD_set_eq vqOffL 0#32 (q.setWidth 32) hr_vqoff, ite_eq_left hlast, hq32]
        refine ⟨hpr.1, hq_qn, fun p hp1 hp2 => ?_⟩
        obtain ⟨w, hw1, hw2, hw3, hw4, hw5, hw6⟩ := hpr.2.2 p hp1 hp2
        rw [hvq_pre p (lt_of_lt_of_le hp2 hpr.2.1)]
        exact ⟨w, hw1, hw2, hw3, hw4, hw5, hw6⟩
      · have hne : ¬ (idx + 1 = r.toNat + 1) := by omega
        simp only [hlast, ↓reduceIte] at hpr
        simp only [hne, ↓reduceIte]
        rw [getD_set_eq vqOffL 0#32 (q.setWidth 32) hr_vqoff, ite_eq_right hlast]
        refine ⟨hpr.1, le_trans hpr.2.1 hq_qn, fun p hp1 hp2 => ?_⟩
        obtain ⟨w, hw1, hw2, hw3, hw4, hw5, hw6⟩ := hpr.2.2 p hp1 hp2
        rw [hvq_pre p (lt_of_lt_of_le hp2 hpr.2.1)]
        exact ⟨w, hw1, hw2, hw3, hw4, hw5, hw6⟩

private def vqKInv (cx : BitVec 64) (sym : BitVec 32) (s : ArCtxState)
    (partnerArr curRm curRp vqOffL' vqL : List (BitVec 32)) (vqSkipL' : List (BitVec 8))
    (vqLen qNat mrOffNat : Nat) (Rtq : Mem 64 → Prop)
    (qk : BitVec 64) (m : Mem 64) : Prop :=
  ∃ vqI : List (BitVec 32),
    vqI.length = vqLen ∧ qNat ≤ qk.toNat ∧ qk.toNat ≤ s.pcap.toNat ∧
    (∀ p < qNat, vqI.getD p 0#32 = vqL.getD p 0#32) ∧
    (∀ p, qNat ≤ p → p < qk.toNat →
      ∃ w ∈ symListAt curRp mrOffNat,
        w % 2 = 0 ∧ w / 2 < s.n_nets.toNat ∧
        partnerArr.getD (w / 2) 0#32 ≠ cNone32 ∧
        (vqI.getD p 0#32).toNat = 2 * (partnerArr.getD (w / 2) 0#32).toNat ∧
        (vqI.getD p 0#32).toNat ≠ sym.toNat) ∧
    (arCtxMem cx s ⋆ array (t := i32) s.partner partnerArr ⋆
      array (t := i32) s.cur_rm curRm ⋆ array (t := i32) s.cur_rp curRp ⋆
      array (t := i32) s.vq_off vqOffL' ⋆ array (t := i32) s.vq vqI ⋆
      array (t := i8) s.vq_skip vqSkipL' ⋆ Rtq) m

private theorem vq_k_step_inv {cx : BitVec 64} {sym : BitVec 32} {s : ArCtxState}
    {partnerArr curRm curRp vqOffL' vqL vqI : List (BitVec 32)} {vqSkipL' : List (BitVec 8)}
    {vqLen qNat mrOffNat : Nat} {Rtq : Mem 64 → Prop} {Valid : (Nat → Bool) → Prop}
    {qk : BitVec 64} {x pBv : BitVec 32} {mSt : Mem 64}
    (hNonEmpty : ∃ σ₀, Valid σ₀) (hPart : ∀ σ, Valid σ → PartnerRep σ s.n_nets.toNat partnerArr)
    (hnn32 : 2 * s.n_nets.toNat < 2 ^ 32)
    (hvqI_len : vqI.length = vqLen) (hqk_vq : qk.toNat < vqI.length)
    (hqk_lt : qk.toNat < s.pcap.toNat) (hq_qk : qNat ≤ qk.toNat)
    (hx_mem : x.toNat ∈ symListAt curRp mrOffNat) (hx_even : x.toNat % 2 = 0)
    (hv_lt : (x >>> 1#32).toNat < s.n_nets.toNat) (hv_eq : (x >>> 1#32).toNat = x.toNat / 2)
    (hp_eq : pBv = partnerArr.getD (x.toNat / 2) 0#32)
    (hp_ne : pBv ≠ cNone32) (hp_sym : 2#32 * pBv ≠ sym)
    (hvqI_pre : ∀ p < qNat, vqI.getD p 0#32 = vqL.getD p 0#32)
    (hvqI_new : ∀ p, qNat ≤ p → p < qk.toNat →
      ∃ w ∈ symListAt curRp mrOffNat,
        w % 2 = 0 ∧ w / 2 < s.n_nets.toNat ∧ partnerArr.getD (w / 2) 0#32 ≠ cNone32 ∧
        (vqI.getD p 0#32).toNat = 2 * (partnerArr.getD (w / 2) 0#32).toNat ∧
        (vqI.getD p 0#32).toNat ≠ sym.toNat)
    (hmSt : (array (t := i32) s.vq (vqI.set qk.toNat (2#32 * pBv)) ⋆
      (arCtxMem cx s ⋆ array (t := i32) s.partner partnerArr ⋆
        array (t := i32) s.cur_rm curRm ⋆ array (t := i32) s.cur_rp curRp ⋆
        array (t := i32) s.vq_off vqOffL' ⋆ array (t := i8) s.vq_skip vqSkipL' ⋆ Rtq)) mSt) :
    vqKInv cx sym s partnerArr curRm curRp vqOffL' vqL vqSkipL' vqLen qNat mrOffNat Rtq
      (qk + 1#64) mSt := by
  obtain ⟨σ₀, hV₀⟩ := hNonEmpty
  have hp_lt_nets : pBv.toNat < s.n_nets.toNat := by
    have hpr := (hPart σ₀ hV₀).2 (x.toNat / 2) (by omega) (by rw [← hp_eq]; exact hp_ne)
    rw [← hp_eq] at hpr; exact hpr.1
  have h2p_eq : (2#32 * pBv).toNat = 2 * pBv.toNat := by
    rw [BitVec.toNat_mul, show (2#32 : BitVec 32).toNat = 2 from rfl,
      Nat.mod_eq_of_lt (by omega : 2 * pBv.toNat < 2 ^ 32)]
  have hqkp1 : (qk + 1#64).toNat = qk.toNat + 1 := by
    rw [BitVec.toNat_add, show (1#64 : BitVec 64).toNat = 1 from rfl,
      Nat.mod_eq_of_lt (by omega : qk.toNat + 1 < 2 ^ 64)]
  refine ⟨vqI.set qk.toNat (2#32 * pBv), by simp [hvqI_len],
    by rw [hqkp1]; omega, by rw [hqkp1]; omega, ?_, ?_, sep_cast hmSt (by ac_rfl)⟩
  · intro p hp
    rw [getD_set_eq vqI 0#32 (2#32 * pBv) hqk_vq, ite_eq_right (by omega)]
    exact hvqI_pre p hp
  · intro p hp1 hp2
    rw [hqkp1] at hp2
    by_cases hpqk : p = qk.toNat
    · subst hpqk
      rw [getD_set_eq vqI 0#32 (2#32 * pBv) hqk_vq, ite_eq_left rfl, h2p_eq]
      refine ⟨x.toNat, hx_mem, hx_even, by omega, by rw [← hp_eq]; exact hp_ne, by rw [hp_eq], ?_⟩
      intro heq; apply hp_sym; apply BitVec.eq_of_toNat_eq; rw [h2p_eq]; exact heq
    · rw [getD_set_eq vqI 0#32 (2#32 * pBv) hqk_vq, ite_eq_right hpqk]
      exact hvqI_new p hp1 (by omega)

private theorem apply_vq_tq_focus {cx : BitVec 64} (s : ArCtxState)
    (tm0 tm1 : List (BitVec 32)) (ts0 tl0 th0 ts1 tl1 th1 : List (BitVec 64))
    (pool0 pool1 qm : List (BitVec 32)) (qs ql qh : List (BitVec 64))
    (ix ix2 bx vqOff vq : List (BitVec 32)) (vqSkip : List (BitVec 8))
    (curRm : List (BitVec 32)) (curRl curRh : List (BitVec 64)) (curRp : List (BitVec 32))
    (partnerArr : List (BitVec 32)) (R : Mem 64 → Prop) {m0 : Mem 64}
    (hpc : s.pc.toNat < 2) (htc : s.tc.toNat < 2)
    (hm0 : (arCtxMem cx s ⋆ array (t := i32) s.partner partnerArr ⋆
      array (t := i32) s.cur_rm curRm ⋆ array64 s.cur_rl curRl ⋆ array64 s.cur_rh curRh ⋆
      array (t := i32) s.cur_rp curRp ⋆
      tMem s tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0 pool1 ⋆
      qMem s qm qs ql qh ix ix2 bx vqOff vq vqSkip ⋆ R) m0) :
    ∃ Rtq : Mem 64 → Prop,
      (arCtxMem cx s ⋆ array (t := i32) s.partner partnerArr ⋆ array (t := i32) s.cur_rm curRm ⋆
        array (t := i32) s.cur_rp curRp ⋆ array (t := i32) s.vq_off vqOff ⋆
        array (t := i32) s.vq vq ⋆ array (t := i8) s.vq_skip vqSkip ⋆ Rtq) m0 ∧
      (∀ (vqOff' vq' : List (BitVec 32)) (vqSkip' : List (BitVec 8)) (m' : Mem 64),
        vqOff'.length = vqOff.length → vq'.length = vq.length → vqSkip'.length = vqSkip.length →
        (arCtxMem cx s ⋆ array (t := i32) s.partner partnerArr ⋆ array (t := i32) s.cur_rm curRm ⋆
          array (t := i32) s.cur_rp curRp ⋆ array (t := i32) s.vq_off vqOff' ⋆
          array (t := i32) s.vq vq' ⋆ array (t := i8) s.vq_skip vqSkip' ⋆ Rtq) m' →
        (arCtxMem cx s ⋆ array (t := i32) s.partner partnerArr ⋆ array (t := i32) s.cur_rm curRm ⋆
          array64 s.cur_rl curRl ⋆ array64 s.cur_rh curRh ⋆ array (t := i32) s.cur_rp curRp ⋆
          tMem s tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0 pool1 ⋆
          qMem s qm qs ql qh ix ix2 bx vqOff' vq' vqSkip' ⋆ R) m') := by
  obtain ⟨rest, hFoc0, hRe⟩ := tqMem_apply_focus s tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0 pool1
    qm qs ql qh ix ix2 bx vqOff vq vqSkip hpc htc
  let srcPool := if s.pc.toNat = 0 then pool0 else pool1
  let srcTm := if s.tc.toNat = 0 then tm0 else tm1
  let srcTs := if s.tc.toNat = 0 then ts0 else ts1
  let srcTl := if s.tc.toNat = 0 then tl0 else tl1
  let srcTh := if s.tc.toNat = 0 then th0 else th1
  have hp_id0 : (if s.pc.toNat = 0 then srcPool else pool0) = pool0 := by
    dsimp only [srcPool]; rcases bv32_lt2_cases hpc with h | h <;> simp [h]
  have hp_id1 : (if s.pc.toNat = 0 then pool1 else srcPool) = pool1 := by
    dsimp only [srcPool]; rcases bv32_lt2_cases hpc with h | h <;> simp [h]
  let Rtq : Mem 64 → Prop := array64 s.cur_rl curRl ⋆ array64 s.cur_rh curRh ⋆
    array (t := i32) (s.pool.getD s.pc.toNat 0#64) srcPool ⋆
    array (t := i32) (s.tm.getD s.tc.toNat 0#64) srcTm ⋆
    array64 (s.ts.getD s.tc.toNat 0#64) srcTs ⋆ array64 (s.tl.getD s.tc.toNat 0#64) srcTl ⋆
    array64 (s.th.getD s.tc.toNat 0#64) srcTh ⋆ array (t := i32) s.qm qm ⋆
    array64 s.qs qs ⋆ array64 s.ql ql ⋆ array64 s.qh qh ⋆ array (t := i32) s.bx bx ⋆ rest ⋆ R
  refine ⟨Rtq, ?_, ?_⟩
  · have hm0_tq : ((tMem s tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0 pool1 ⋆
        qMem s qm qs ql qh ix ix2 bx vqOff vq vqSkip) ⋆
        (arCtxMem cx s ⋆ array (t := i32) s.partner partnerArr ⋆
          array (t := i32) s.cur_rm curRm ⋆ array64 s.cur_rl curRl ⋆
          array64 s.cur_rh curRh ⋆ array (t := i32) s.cur_rp curRp ⋆ R)) m0 :=
      sep_cast hm0 (by ac_rfl)
    rw [hFoc0] at hm0_tq
    dsimp only [Rtq]; exact sep_cast hm0_tq (by ac_rfl)
  · intro vqOff' vq' vqSkip' m' hl1 hl2 hl3 hm'
    have hEq := hRe s srcPool qm qs ql qh bx vqOff' vq' vqSkip' rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl hl1 hl2 hl3
    rw [hp_id0, hp_id1] at hEq
    have hm1 : (arCtxMem cx s ⋆ array (t := i32) s.partner partnerArr ⋆
        array (t := i32) s.cur_rm curRm ⋆ array64 s.cur_rl curRl ⋆
        array64 s.cur_rh curRh ⋆ array (t := i32) s.cur_rp curRp ⋆
        (tMem s tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0 pool1 ⋆
          qMem s qm qs ql qh ix ix2 bx vqOff' vq' vqSkip') ⋆ R) m' := by
      rw [hEq]; refine sep_cast hm' ?_; dsimp only [Rtq]; ac_rfl
    exact sep_cast hm1 (by ac_rfl)

private theorem arCtxMem_lengthsOk {cx : BitVec 64} {s : ArCtxState} {R : Mem 64 → Prop}
    {m : Mem 64} (hm : (arCtxMem cx s ⋆ R) m) : ArCtxLengthsOk s := by
  unfold arCtxMem at hm
  exact (sep_pure_l (φ := ArCtxLengthsOk s) (P := (arCtxTree cx s).eval) (R := R)).mp hm |>.1

/-- Loop 3 (`r < nR`) of `ar_apply`: builds vanishing-row flags `vq_skip` and partner conflict
arrays `vq_off`/`vq`, finalizing `vq_off[nR] := q`. -/
theorem apply_vq_loop_wp (Γ : T.Env)
    (hMvan : ∀ xs m Q X, arMvanishSpec xs m Q X → Γ "ar_mvanish" [i64, i64] [.bool] xs m Q X)
    {cx : BitVec 64} {sym : BitVec 32} {s : ArCtxState}
    {tm0 tm1 : List (BitVec 32)} {ts0 tl0 th0 ts1 tl1 th1 : List (BitVec 64)}
    {pool0 pool1 qm : List (BitVec 32)} {qs ql qh : List (BitVec 64)}
    {ix ix2 bx vqOff vq : List (BitVec 32)} {vqSkip : List (BitVec 8)}
    {curRm : List (BitVec 32)} {curRl curRh : List (BitVec 64)} {curRp : List (BitVec 32)}
    {partnerArr : List (BitVec 32)} {Valid : (Nat → Bool) → Prop} {R : Mem 64 → Prop}
    {nb : BitVec 32} {slB slR : BitVec 64} {m0 : Mem 64}
    {Q : Post [.bool]} {X : XPost}
    (hpc : s.pc.toNat < 2) (htc : s.tc.toNat < 2)
    (hcurNr_qcap : s.cur_nr.toNat ≤ s.qcap.toNat) (hqcap32 : s.qcap.toNat + 16 < 2 ^ 32)
    (hpcap32 : s.pcap.toNat < 2 ^ 32) (hnn32 : 2 * s.n_nets.toNat < 2 ^ 32)
    (hcurNr_rm : s.cur_nr.toNat ≤ curRm.length)
    (hvqOff_len : s.qcap.toNat + 1 ≤ vqOff.length) (hvq_len : s.pcap.toNat ≤ vq.length)
    (hvqSkip_len : s.qcap.toNat ≤ vqSkip.length)
    (hcurSl : ∀ r < s.cur_nr.toNat, MonoSliceOk curRp (curRm.getD r 0#32).toNat curRp.length)
    (hcurMr32 : ∀ r < s.cur_nr.toNat,
      (curRp.getD (curRm.getD r 0#32).toNat 0#32).toNat + 1 < 2 ^ 32)
    (hNonEmpty : ∃ σ₀, Valid σ₀)
    (hPart : ∀ σ, Valid σ → PartnerRep σ s.n_nets.toNat partnerArr)
    (hm0 : (arCtxMem cx s ⋆ array (t := i32) s.partner partnerArr ⋆
      array (t := i32) s.cur_rm curRm ⋆ array64 s.cur_rl curRl ⋆ array64 s.cur_rh curRh ⋆
      array (t := i32) s.cur_rp curRp ⋆
      tMem s tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0 pool1 ⋆
      qMem s qm qs ql qh ix ix2 bx vqOff vq vqSkip ⋆ R) m0)
    (hFail : ∀ (vqOff' vq' : List (BitVec 32)) (vqSkip' : List (BitVec 8)) (m' : Mem 64),
      vqOff'.length = vqOff.length → vq'.length = vq.length → vqSkip'.length = vqSkip.length →
      (arCtxMem cx s ⋆ array (t := i32) s.partner partnerArr ⋆
        array (t := i32) s.cur_rm curRm ⋆ array64 s.cur_rl curRl ⋆
        array64 s.cur_rh curRh ⋆ array (t := i32) s.cur_rp curRp ⋆
        tMem s tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0 pool1 ⋆
        qMem s qm qs ql qh ix ix2 bx vqOff' vq' vqSkip' ⋆ R) m' →
      Q (false, ⟨⟩) m')
    (hDone : ∀ (vqOff' vq' : List (BitVec 32)) (vqSkip' : List (BitVec 8)) (qFin : Nat)
        (m' : Mem 64),
      vqOff'.length = vqOff.length → vq'.length = vq.length → vqSkip'.length = vqSkip.length →
      qFin ≤ s.pcap.toNat →
      (∀ r < s.cur_nr.toNat,
        VqRowOk s.n_nets.toNat sym.toNat partnerArr curRp curRm vqOff' vq' vqSkip' Valid r qFin) →
      (arCtxMem cx s ⋆ array (t := i32) s.partner partnerArr ⋆
        array (t := i32) s.cur_rm curRm ⋆ array64 s.cur_rl curRl ⋆
        array64 s.cur_rh curRh ⋆ array (t := i32) s.cur_rp curRp ⋆
        tMem s tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0 pool1 ⋆
        qMem s qm qs ql qh ix ix2 bx vqOff' vq' vqSkip' ⋆ R) m' →
      wp Γ Q X (applyLoop4Expr cx sym s.cur_rm s.cur_rl s.cur_rh s.cur_rp s.cur_nr s.tn
        s.bx nb slB slR (s.pool.getD s.pc.toNat 0#64) (s.tm.getD s.tc.toNat 0#64)
        (s.tl.getD s.tc.toNat 0#64) (s.th.getD s.tc.toNat 0#64) s.ptop) m') :
    wp Γ Q X (applyLoop3Expr cx sym s.cur_rm s.cur_rl s.cur_rh s.cur_rp s.cur_nr s.tn
      s.bx nb slB slR) m0 := by
  dsimp only [applyLoop3Expr, applyAfterLoop2Expr, applyLoop2Expr, applyLoop1ExitExpr,
    applyLoop1Expr]
  have hl_ok : ArCtxLengthsOk s := arCtxMem_lengthsOk (sep_cast hm0 (by
    change (arCtxMem cx s ⋆ array (t := i32) s.partner partnerArr ⋆
      array (t := i32) s.cur_rm curRm ⋆ array64 s.cur_rl curRl ⋆ array64 s.cur_rh curRh ⋆
      array (t := i32) s.cur_rp curRp ⋆ tMem s tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0 pool1 ⋆
      qMem s qm qs ql qh ix ix2 bx vqOff vq vqSkip ⋆ R) =
      (arCtxMem cx s ⋆ (array (t := i32) s.partner partnerArr ⋆
        array (t := i32) s.cur_rm curRm ⋆ array64 s.cur_rl curRl ⋆ array64 s.cur_rh curRh ⋆
        array (t := i32) s.cur_rp curRp ⋆ tMem s tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0 pool1 ⋆
        qMem s qm qs ql qh ix ix2 bx vqOff vq vqSkip ⋆ R)); ac_rfl))
  obtain ⟨Rtq, hm0', mkFull⟩ := apply_vq_tq_focus s tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0 pool1
    qm qs ql qh ix ix2 bx vqOff vq vqSkip curRm curRl curRh curRp partnerArr R hpc htc hm0
  have hpart_len : s.n_nets.toNat ≤ partnerArr.length := by
    obtain ⟨σ₀, hV₀⟩ := hNonEmpty; exact (hPart σ₀ hV₀).1
  refine wp_loop_group (fun rem ⟨r, q, ⟨⟩⟩ mL =>
      ∃ (vqOffL vqL : List (BitVec 32)) (vqSkipL : List (BitVec 8)),
        vqOffL.length = vqOff.length ∧ vqL.length = vq.length ∧ vqSkipL.length = vqSkip.length ∧
        r.toNat ≤ s.cur_nr.toNat ∧ rem = s.cur_nr.toNat - r.toNat ∧ q.toNat ≤ s.pcap.toNat ∧
        (∀ idx < r.toNat, VqRowPreOk s.n_nets.toNat sym.toNat partnerArr curRp curRm
          vqOffL vqL vqSkipL Valid r.toNat idx q.toNat) ∧
        (arCtxMem cx s ⋆ array (t := i32) s.partner partnerArr ⋆ array (t := i32) s.cur_rm curRm ⋆
          array (t := i32) s.cur_rp curRp ⋆ array (t := i32) s.vq_off vqOffL ⋆
          array (t := i32) s.vq vqL ⋆ array (t := i8) s.vq_skip vqSkipL ⋆ Rtq) mL)
    ?_ ?_
  · rintro J rem ⟨r, q, ⟨⟩⟩ mL hrec ⟨vqOffL, vqL, vqSkipL, hl1, hl2, hl3, hr_le, hrem, hq_cap,
        hPre, hmL⟩
    c0_hsteps_nogrp
    · have hr_lt : r.toNat < s.cur_nr.toNat := hc
      have hrm_lt : r.toNat < curRm.length := by omega
      have hr_sw : (BitVec.setWidth 64 r : BitVec 64).toNat = r.toNat := by
        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans r.isLt (by decide))]
      let mrOff := curRm[(BitVec.setWidth 64 r : BitVec 64).toNat]'(by rw [hr_sw]; exact hrm_lt)
      have hmr_eq : mrOff.toNat = (curRm.getD r.toNat 0#32).toNat := by
        dsimp only [mrOff]; simp only [hr_sw]; rw [getD_eq_getElem curRm 0#32 hrm_lt]
      have hmr_sl := hcurSl r.toNat hr_lt
      have hmr_32 := hcurMr32 r.toNat hr_lt
      rw [← hmr_eq] at hmr_sl hmr_32
      have hr_vqoff : r.toNat < vqOffL.length := by omega
      have hq32_eq : (q.setWidth 32 : BitVec 32).toNat = q.toNat := by
        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega : q.toNat < 2 ^ 32)]
      let vqOffL' := vqOffL.set r.toNat (q.setWidth 32)
      have hl1' : vqOffL'.length = vqOff.length := by simp [vqOffL', hl1]
      have hmO' : (arCtxMem cx s ⋆ array (t := i32) s.partner partnerArr ⋆
          array (t := i32) s.cur_rm curRm ⋆ array (t := i32) s.cur_rp curRp ⋆
          array (t := i32) s.vq_off vqOffL' ⋆ array (t := i32) s.vq vqL ⋆
          array (t := i8) s.vq_skip vqSkipL ⋆ Rtq) m := by
        dsimp only [vqOffL']; rw [← hr_sw]; exact sep_cast hm (by ac_rfl)
      refine wp_join_group (fun ⟨sk, ⟨⟩⟩ mS =>
          (sk = 1#32 ∨ sk = 0#32) ∧
          (sk = 1#32 → ∀ σ, Valid σ → monoValL σ (symListAt curRp mrOff.toNat) = false) ∧
          (arCtxMem cx s ⋆ array (t := i32) s.partner partnerArr ⋆
            array (t := i32) s.cur_rm curRm ⋆ array (t := i32) s.cur_rp curRp ⋆
            array (t := i32) s.vq_off vqOffL' ⋆ array (t := i32) s.vq vqL ⋆
            array (t := i8) s.vq_skip vqSkipL ⋆ Rtq) mS)
        ?_ ?_
      · rintro Js ⟨sk, ⟨⟩⟩ mS ⟨hsk_cases, hsk_van, hmS⟩
        c0_hsteps_nogrp
        have hr_skip : r.toNat < vqSkipL.length := by omega
        let vqSkipL' := vqSkipL.set r.toNat (sk.setWidth 8)
        have hl3' : vqSkipL'.length = vqSkip.length := by simp [vqSkipL', hl3]
        let mSk' := m
        have hmSk' : (arCtxMem cx s ⋆ array (t := i32) s.partner partnerArr ⋆
            array (t := i32) s.cur_rm curRm ⋆ array (t := i32) s.cur_rp curRp ⋆
            array (t := i32) s.vq_off vqOffL' ⋆ array (t := i32) s.vq vqL ⋆
            array (t := i8) s.vq_skip vqSkipL' ⋆ Rtq) mSk' := by
          dsimp only [vqSkipL', mSk']; rw [← hr_sw]; exact sep_cast hm (by ac_rfl)
        refine wp_join_group (fun ⟨qNext, ⟨⟩⟩ mN =>
            ∃ vqN : List (BitVec 32),
              vqN.length = vq.length ∧ q.toNat ≤ qNext.toNat ∧ qNext.toNat ≤ s.pcap.toNat ∧
              (∀ p < q.toNat, vqN.getD p 0#32 = vqL.getD p 0#32) ∧
              (sk = 0#32 → ∀ p, q.toNat ≤ p → p < qNext.toNat →
                ∃ w ∈ symListAt curRp mrOff.toNat,
                  w % 2 = 0 ∧ w / 2 < s.n_nets.toNat ∧
                  partnerArr.getD (w / 2) 0#32 ≠ cNone32 ∧
                  (vqN.getD p 0#32).toNat = 2 * (partnerArr.getD (w / 2) 0#32).toNat ∧
                  (vqN.getD p 0#32).toNat ≠ sym.toNat) ∧
              (arCtxMem cx s ⋆ array (t := i32) s.partner partnerArr ⋆
                array (t := i32) s.cur_rm curRm ⋆ array (t := i32) s.cur_rp curRp ⋆
                array (t := i32) s.vq_off vqOffL' ⋆ array (t := i32) s.vq vqN ⋆
                array (t := i8) s.vq_skip vqSkipL' ⋆ Rtq) mN)
          ?_ ?_
        · rintro Jn ⟨qNext, ⟨⟩⟩ mN ⟨vqN, hvqN_len, hq_qn, hqn_cap, hvq_pre, hvq_new, hmN⟩
          c0_hsteps_nogrp
          have hrp1 : (r + 1#32).toNat = r.toNat + 1 := by
            rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl,
              Nat.mod_eq_of_lt (by omega : r.toNat + 1 < 2 ^ 32)]
          refine hrec (s.cur_nr.toNat - (r + 1#32).toNat) (r + 1#32, qNext, ⟨⟩) mN
            (by omega) ⟨vqOffL', vqN, vqSkipL', hl1', hvqN_len, hl3', by rw [hrp1]; omega,
              rfl, hqn_cap, ?_, hmN⟩
          rw [hrp1]
          exact vqRowPreOk_step hmr_eq hr_vqoff hr_skip hq_qn hq32_eq hsk_cases hsk_van
            hvq_pre hvq_new hPre
        · intro Jn hJn
          c0_hsteps_nogrp
          · have hsk0 : sk = 0#32 := by
              rcases hsk_cases with rfl | rfl
              · exact absurd hc (by decide)
              · rfl
            have hm_mlen : (array (t := i32) s.cur_rp curRp ⋆
                (arCtxMem cx s ⋆ array (t := i32) s.partner partnerArr ⋆
                  array (t := i32) s.cur_rm curRm ⋆ array (t := i32) s.vq_off vqOffL' ⋆
                  array (t := i32) s.vq vqL ⋆ array (t := i8) s.vq_skip vqSkipL' ⋆ Rtq))
                mSk' := sep_cast hmSk' (by ac_rfl)
            have ha_mr : s.cur_rp + BitVec.setWidth 64 mrOff * 4#64 =
                s.cur_rp + BitVec.ofNat 64 (4 * mrOff.toNat) := by
              apply congrArg (s.cur_rp + ·)
              apply BitVec.eq_of_toNat_eq
              have hlt : mrOff.toNat < 2 ^ 32 := mrOff.isLt
              rw [BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
                Nat.mod_eq_of_lt (by omega : mrOff.toNat < 2 ^ 64),
                Nat.mod_eq_of_lt (by decide : 4 < 2 ^ 64),
                Nat.mod_eq_of_lt (by omega : mrOff.toNat * 4 < 2 ^ 64),
                Nat.mod_eq_of_lt (by omega : 4 * mrOff.toNat < 2 ^ 64), Nat.mul_comm]
            refine wp_load_arr32_0 (base := s.cur_rp) (xs := curRp) (off := mrOff.toNat)
              ?_ hmr_sl.1 hm_mlen ?_
            · simp only [Arg.val]; exact congrArg (· + 0#64 * 4#64) ha_mr
            c0_hsteps_nogrp
            let mlen := curRp[mrOff.toNat]'hmr_sl.1
            have hmlen_eq : mlen.toNat = (curRp.getD mrOff.toNat 0#32).toNat := by
              dsimp only [mlen]
              exact (congrArg BitVec.toNat (getD_eq_getElem curRp 0#32 hmr_sl.1)).symm
            have hmlen_32 : mlen.toNat + 1 < 2 ^ 32 := by rw [hmlen_eq]; exact hmr_32
            have hmlen_len : mrOff.toNat + 1 + mlen.toNat ≤ curRp.length := by
              rw [hmlen_eq]; exact hmr_sl.2
            let KInv := vqKInv cx sym s partnerArr curRm curRp vqOffL' vqL vqSkipL'
              vq.length q.toNat mrOff.toNat Rtq
            refine wp_loop_group (fun remI ⟨qk, k, ⟨⟩⟩ mI =>
                1 ≤ k.toNat ∧ k.toNat ≤ mlen.toNat + 1 ∧ remI = mlen.toNat + 1 - k.toNat ∧
                KInv qk mI)
              ?_ ?_
            · rintro Ji remI ⟨qk, k, ⟨⟩⟩ mI hrecI ⟨hk_ge1, hk_le1, hremI, vqI, hvqI_len,
                  hq_qk, hqk_cap, hvqI_pre, hvqI_new, hmI⟩
              c0_hsteps_nogrp
              · have hk_le : k.toNat ≤ mlen.toNat := by c0_bv_omega
                clear hc
                have hxk_lt : mrOff.toNat + k.toNat < curRp.length := by omega
                have hm_xk : (array (t := i32) s.cur_rp curRp ⋆
                    (arCtxMem cx s ⋆ array (t := i32) s.partner partnerArr ⋆
                      array (t := i32) s.cur_rm curRm ⋆ array (t := i32) s.vq_off vqOffL' ⋆
                      array (t := i32) s.vq vqI ⋆ array (t := i8) s.vq_skip vqSkipL' ⋆ Rtq))
                    mI := sep_cast hmI (by ac_rfl)
                refine wp_load_arr32_idx (base := s.cur_rp) (off := mrOff.toNat) (xs := curRp)
                  (i := k) ?_ hxk_lt hm_xk ?_
                · simp only [Arg.val]; exact congrArg (· + BitVec.setWidth 64 k * 4#64) ha_mr
                c0_hsteps_nogrp
                let x := curRp[mrOff.toNat + k.toNat]'hxk_lt
                have hx_mem : x.toNat ∈ symListAt curRp mrOff.toNat := by
                  rw [mem_symListAt_iff]
                  refine ⟨k.toNat, hk_ge1, by rw [← hmlen_eq]; exact hk_le, ?_⟩
                  dsimp only [x]
                  rw [getD_eq_getElem curRp 0#32 hxk_lt]
                refine wp_join_group (fun ⟨qk', ⟨⟩⟩ mI' => KInv qk' mI') ?_ ?_
                · rintro Jk' ⟨qk', ⟨⟩⟩ mI' hK
                  c0_hsteps_nogrp
                  have hkp1 : (k + 1#32).toNat = k.toNat + 1 := by
                    rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl,
                      Nat.mod_eq_of_lt (by omega : k.toNat + 1 < 2 ^ 32)]
                  exact hrecI (mlen.toNat + 1 - (k + 1#32).toNat) (qk', k + 1#32, ⟨⟩) mI'
                    (by omega) ⟨by rw [hkp1]; omega, by rw [hkp1]; omega, rfl, hK⟩
                · intro Jk' hJk'
                  c0_hsplit_nobound
                  · have hx0 : (x &&& 1#32) = 0#32 := by c0_bv_omega
                    have hx_even : x.toNat % 2 = 0 := by
                      have h := congrArg BitVec.toNat hx0
                      rw [BitVec.toNat_and] at h
                      simpa [Nat.and_one_is_mod] using h
                    clear hc; c0_hsteps_nogrp
                    refine wp_join_group (fun ⟨qk', ⟨⟩⟩ mI' => KInv qk' mI') ?_ ?_
                    · rintro Jv ⟨qk', ⟨⟩⟩ mI' hK; c0_hsteps_nogrp; exact hJk' (qk', ⟨⟩) mI' hK
                    · intro Jv hJv
                      c0_hstep_np; c0_hstep_np; c0_hstep_np
                      refine head_wp_jnz rfl (fun hc => ?_) (fun hc => ?_)
                      · have hv_lt : (x >>> 1#32).toNat < s.n_nets.toNat := of_decide_eq_true hc
                        clear hc
                        have hv_eq : (x >>> 1#32).toNat = x.toNat / 2 := by
                          change (x >>> 1).toNat = x.toNat / 2
                          rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_one]
                        have hv_arr : (x >>> 1#32).toNat < partnerArr.length := by omega
                        c0_hsteps_nogrp_nobound
                        let pBv := partnerArr[(x >>> 1#32).toNat]'hv_arr
                        have hp_eq : pBv = partnerArr.getD (x.toNat / 2) 0#32 := by
                          dsimp only [pBv]
                          rw [← hv_eq, getD_eq_getElem partnerArr 0#32 hv_arr]
                        refine wp_join_group (fun ⟨qk', ⟨⟩⟩ mI' => KInv qk' mI') ?_ ?_
                        · rintro Jp ⟨qk', ⟨⟩⟩ mI' hK; c0_hstep_np; exact hJv (qk', ⟨⟩) mI' hK
                        · intro Jp hJp
                          c0_hstep_np
                          refine head_wp_jnz rfl (fun hc => ?_) (fun hc => ?_)
                          · have hp_ne : pBv ≠ cNone32 := by
                              dsimp only [Arg.val] at hc; exact bne_iff_ne.mp hc
                            clear hc; c0_hstep_np; c0_hstep_np
                            refine head_wp_jnz rfl (fun hc => ?_) (fun hc => ?_)
                            · have hp_sym : 2#32 * pBv ≠ sym := by
                                dsimp only [Arg.val] at hc; exact bne_iff_ne.mp hc
                              clear hc; c0_hstep_np; c0_hstep_np; c0_hstep_np
                              refine head_wp_jnz rfl (fun hc => ?_) (fun hc => ?_)
                              · c0_hstep_np
                                exact hFail vqOffL' vqI vqSkipL' _ hl1' hvqI_len hl3'
                                  (mkFull vqOffL' vqI vqSkipL' _ hl1' hvqI_len hl3' hmI)
                              · have hqk_lt : qk.toNat < s.pcap.toNat := by
                                  have hnot : ¬ s.pcap.toNat ≤ qk.toNat := of_decide_eq_false hc
                                  omega
                                clear hc
                                c0_hstep_np; c0_hstep_np; c0_hstep_np; c0_hstep_np; c0_hstep_np
                                have hqk_vq : qk.toNat < vqI.length := by omega
                                have hm_vq0 : (array (t := i32) s.vq vqI ⋆
                                    (arCtxMem cx s ⋆ array (t := i32) s.partner partnerArr ⋆
                                      array (t := i32) s.cur_rm curRm ⋆
                                      array (t := i32) s.cur_rp curRp ⋆
                                      array (t := i32) s.vq_off vqOffL' ⋆
                                      array (t := i8) s.vq_skip vqSkipL' ⋆ Rtq)) mI :=
                                  sep_cast hmI (by ac_rfl)
                                refine wp_store_arr32_abs (base := s.vq) (xs := vqI) (idx := qk)
                                  (val := 2#32 * pBv) (by rfl) (by rfl) hqk_vq hm_vq0
                                  fun mSt hmSt => ?_
                                c0_hstep_np; c0_hstep_np
                                exact hJp (qk + 1#64, ⟨⟩) mSt (vq_k_step_inv hNonEmpty hPart hnn32
                                  hvqI_len hqk_vq hqk_lt hq_qk hx_mem hx_even hv_lt hv_eq hp_eq
                                  hp_ne hp_sym hvqI_pre hvqI_new hmSt)
                            · refine head_wp_jump rfl rfl (hJp (qk, ⟨⟩) mI ⟨vqI, hvqI_len, hq_qk,
                                hqk_cap, hvqI_pre, hvqI_new, hmI⟩)
                          · refine head_wp_jump rfl rfl (hJp (qk, ⟨⟩) mI ⟨vqI, hvqI_len, hq_qk,
                              hqk_cap, hvqI_pre, hvqI_new, hmI⟩)
                      · refine head_wp_jump rfl rfl (hJv (qk, ⟨⟩) mI ⟨vqI, hvqI_len, hq_qk,
                          hqk_cap, hvqI_pre, hvqI_new, hmI⟩)
                  · refine head_wp_jump rfl rfl (hJk' (qk, ⟨⟩) mI ⟨vqI, hvqI_len, hq_qk, hqk_cap,
                      hvqI_pre, hvqI_new, hmI⟩)
              · have hk_gt : mlen.toNat < k.toNat := by dsimp only [mlen]; omega
                clear hc
                exact hJn (qk, ⟨⟩) mI ⟨vqI, hvqI_len, hq_qk, hqk_cap, hvqI_pre,
                  fun _ p hp1 hp2 => hvqI_new p hp1 hp2, hmI⟩
            · intro Ji hJi
              refine head_wp_jump rfl rfl ?_
              have h1_32 : (1#32 : BitVec 32).toNat = 1 := rfl
              exact hJi mlen.toNat (q, 1#32, ⟨⟩) mSk' ⟨le_refl _,
                (by rw [h1_32]; omega), (by rw [h1_32, Nat.add_sub_cancel]),
                vqL, hl2, le_refl _, hq_cap, fun _ _ => rfl, fun p hp1 hp2 => by omega, hmSk'⟩
          · have hsk1 : sk = 1#32 := by
              rcases hsk_cases with rfl | rfl
              · rfl
              · exact absurd hc (by decide)
            clear hc; c0_hsteps_nogrp_nobound
            exact hJn (q, ⟨⟩) mSk' ⟨vqL, hl2, le_refl _, hq_cap, fun _ _ => rfl,
              fun h0 => absurd hsk1 (by rw [h0]; decide), hmSk'⟩
      · intro Js hJs
        c0_hsteps_nogrp_nobound
        have hmrPtr : (s.cur_rp + BitVec.setWidth 64 mrOff * 4#64) =
            s.cur_rp + BitVec.ofNat 64 (4 * mrOff.toNat) := by
          apply congrArg (s.cur_rp + ·); apply BitVec.eq_of_toNat_eq
          have hlt : mrOff.toNat < 2 ^ 32 := mrOff.isLt
          rw [BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (by omega : mrOff.toNat < 2 ^ 64),
            Nat.mod_eq_of_lt (by decide : 4 < 2 ^ 64),
            Nat.mod_eq_of_lt (by omega : mrOff.toNat * 4 < 2 ^ 64),
            Nat.mod_eq_of_lt (by omega : 4 * mrOff.toNat < 2 ^ 64), Nat.mul_comm]
        have hm_van : (arCtxMem cx s ⋆ array (t := i32) s.partner partnerArr ⋆
            array (t := i32) s.cur_rp curRp ⋆
            (array (t := i32) s.cur_rm curRm ⋆ array (t := i32) s.vq_off vqOffL' ⋆
              array (t := i32) s.vq vqL ⋆ array (t := i8) s.vq_skip vqSkipL ⋆ Rtq)) m :=
          sep_cast hmO' (by ac_rfl)
        refine wp_call_of_spec _ _ (arMvanish_forall_of_spec Γ hMvan hmrPtr hmr_sl hmr_32
          (by omega) hNonEmpty hPart hm_van fun ok hok => ?_)
        c0_hsplit_nobound
        · c0_hsteps_nogrp
          exact hJs (1#32, ⟨⟩) m ⟨Or.inl rfl, fun _ => hok hc, hmO'⟩
        · c0_hsteps_nogrp
          exact hJs (0#32, ⟨⟩) m ⟨Or.inr rfl, (fun h => by cases h), hmO'⟩
    · have hr_eq : r.toNat = s.cur_nr.toNat := by
        have hnot : ¬ r.toNat < s.cur_nr.toNat := by c0_bv_omega
        omega
      clear hc; c0_hsteps_nogrp
      have hnr_vqoff : s.cur_nr.toNat < vqOffL.length := by omega
      have hnr_sw : (BitVec.setWidth 64 s.cur_nr : BitVec 64).toNat = s.cur_nr.toNat := by
        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans s.cur_nr.isLt (by decide))]
      have hq32_fin : q.setWidth 32 = BitVec.ofNat 32 q.toNat := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega : q.toNat < 2 ^ 32)]
      let vqOffFin := vqOffL.set s.cur_nr.toNat (q.setWidth 32)
      have hl1_fin : vqOffFin.length = vqOff.length := by simp [vqOffFin, hl1]
      have hmFin : (arCtxMem cx s ⋆ array (t := i32) s.partner partnerArr ⋆
          array (t := i32) s.cur_rm curRm ⋆ array (t := i32) s.cur_rp curRp ⋆
          array (t := i32) s.vq_off vqOffFin ⋆ array (t := i32) s.vq vqL ⋆
          array (t := i8) s.vq_skip vqSkipL ⋆ Rtq) m := by
        dsimp only [vqOffFin]; rw [← hnr_sw]; exact sep_cast hm (by ac_rfl)
      have hmFin' := mkFull vqOffFin vqL vqSkipL m hl1_fin hl2 hl3 hmFin
      obtain rfl : r = s.cur_nr := BitVec.eq_of_toNat_eq hr_eq
      change wp Γ Q X (applyLoop4Expr cx sym s.cur_rm s.cur_rl s.cur_rh s.cur_rp s.cur_nr
        s.tn s.bx nb slB slR (s.pool[s.pc.toNat]'(by rw [hl_ok.pool]; exact hpc))
        (s.tm[s.tc.toNat]'(by rw [hl_ok.tm]; exact htc))
        (s.tl[s.tc.toNat]'(by rw [hl_ok.tl]; exact htc))
        (s.th[s.tc.toNat]'(by rw [hl_ok.th]; exact htc)) s.ptop) m
      rw [← getD_eq_getElem s.pool 0#64 (by rw [hl_ok.pool]; exact hpc),
        ← getD_eq_getElem s.tm 0#64 (by rw [hl_ok.tm]; exact htc),
        ← getD_eq_getElem s.tl 0#64 (by rw [hl_ok.tl]; exact htc),
        ← getD_eq_getElem s.th 0#64 (by rw [hl_ok.th]; exact htc)]
      refine hDone vqOffFin vqL vqSkipL q.toNat m hl1_fin hl2 hl3 hq_cap ?_ hmFin'
      intro idx hidx
      rw [show vqOffFin = vqOffL.set s.cur_nr.toNat (BitVec.ofNat 32 q.toNat) by
        dsimp only [vqOffFin]; rw [hq32_fin]]
      exact vqRowPreOk_to_ok (hr_eq ▸ hPre idx (by omega)) hidx hnr_vqoff (by omega)
  · intro J hJ
    c0_hsteps_nogrp
    exact hJ s.cur_nr.toNat (0#32, 0#64, ⟨⟩) m0 ⟨vqOff, vq, vqSkip, rfl, rfl, rfl,
      Nat.zero_le _, by rw [show (0#32 : BitVec 32).toNat = 0 from rfl]; omega,
      Nat.zero_le _, fun _ h => absurd h (Nat.not_lt_zero _), hm0'⟩

end

end LeanQbe.T.Examples.Arisca.Proof
