/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Float64.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Heap.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Lib.ContractLemmas
public import LeanQbe.T.Examples.Kissat.Proof.Limits.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Restart.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts3
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Header
public import LeanQbe.T.Examples.Kissat.Src.Restart
public import LeanQbe.T.Logic.CanonicalEnv
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics1
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Canonical WP Proofs for `Kissat.Src.Restart` — Part 1 (`full_switch_mode_m7`)

Proves `full_switch_mode_m7_wp` (`Spec.fullSwitchModeM7Spec`) against `Src.Restart`
(`0` legacy imports, `0` `@[expose]` on theorems/lemmas/sections).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Restart

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Float64.Spec
open LeanQbe.T.Examples.Kissat.Proof.Limits.Spec
open LeanQbe.T.Examples.Kissat.Src.Restart
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.M6HdrTactics

local macro "rs_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

private theorem rs_add1 {x : BitVec 64} (hx : x.toNat + 1 < 2 ^ 64) :
    (x + 1#64).toNat = x.toNat + 1 := by
  rw [BitVec.toNat_add, show (1#64 : BitVec 64).toNat = 1 from rfl, Nat.mod_eq_of_lt hx]

private theorem rs_zext32 (x : BitVec 32) : (x.setWidth 64).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans x.isLt (by decide))]

private theorem rs_ext_trans {s1 s2 s3 : FullState}
    (h12 : FullExtScratchPres s1 s2) (h23 : FullExtScratchPres s2 s3) :
    FullExtScratchPres s1 s3 :=
  ⟨h23.1.trans h12.1, h23.2.trans h12.2⟩

private theorem rs_m7_set64_len {c : FullCfg} {s : FullState} (hlen : s.LengthsOk c)
    (idx : Nat) (val : BitVec 64) :
    ({ s with scratch := { s.scratch with
      glue_used := if idx < 63 then m7Set64List s.scratch.glue_used idx val
                   else s.scratch.glue_used } } : FullState).LengthsOk c := by
  refine ⟨hlen.core_ok, { hlen.scratch_ok with glue_used_len := ?_ }⟩
  split
  · rw [m7Set64List_length]; exact hlen.scratch_ok.glue_used_len
  · exact hlen.scratch_ok.glue_used_len

private theorem rs_call_get64 {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {args : Tup (Arg Val) [i64, i64]} {k : Tup Val [i64] → Expr Val Cont rs}
    (hGet : Γ.Has "full_m7_get64" m7Get64Spec)
    {c : FullCfg} {idx : BitVec 64} {s : FullState} {R : Mem 64 → Prop}
    (hargs : vals args = (c.hdr, idx, ())) (hlen : s.LengthsOk c) (hm : (FullMem c s ⋆ R) m)
    (hk : ∀ v : BitVec 64, wp Γ Q X (k (v, ())) m) :
    wp Γ Q X (.call "full_m7_get64" args k) m := by
  refine wp_call_of_spec args k ?_
  rw [hargs]
  exact hGet _ _ _ _ ⟨c, s, R, rfl, hlen, hm, hk _⟩

private theorem rs_call_set64 {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {args : Tup (Arg Val) [i64, i64, i64]} {k : Tup Val [] → Expr Val Cont rs}
    (hSet : Γ.Has "full_m7_set64" m7Set64Spec)
    {c : FullCfg} {idx val : BitVec 64} {s : FullState} {R : Mem 64 → Prop}
    (hargs : vals args = (c.hdr, idx, val, ()))
    (hlen : s.LengthsOk c) (hm : (FullMem c s ⋆ R) m)
    (hk : ∀ s' m', s'.core = s.core → s'.LengthsOk c →
      FullExtScratchPres s s' → (FullMem c s' ⋆ R) m' → wp Γ Q X (k ()) m') :
    wp Γ Q X (.call "full_m7_set64" args k) m := by
  refine wp_call_of_spec args k ?_
  rw [hargs]
  refine hSet _ _ _ _ ⟨c, s, R, rfl, hlen, hm, fun m' hm' => ?_⟩
  let s' : FullState := { s with scratch := { s.scratch with
    glue_used := if idx.toNat < 63 then m7Set64List s.scratch.glue_used idx.toNat val
                 else s.scratch.glue_used } }
  exact hk s' m' rfl (rs_m7_set64_len hlen idx.toNat val) ⟨rfl, rfl⟩ hm'

/-- Soundness proof for `full_switch_mode_m7` against `Spec.switchModeSpec`. -/
theorem full_switch_mode_m7_wp (Γ : Env)
    (hWm4Get : Γ.Has "m6_wm4_get" (m6HdrW2aSpec [] [i64]))
    (hWm4Set : Γ.Has "m6_wm4_set" (m6HdrW2aSpec [i64] []))
    (hHeapUp : Γ.Has "full_heap_up" fullHeapUpSpec)
    (hHeapDown : Γ.Has "full_heap_down" fullHeapDownSpec)
    (hHeapPush : Γ.Has "full_heap_push" fullHeapPushSpec)
    (hNlog : Γ.Has "f64u_nlogpown" f64uPure2Spec)
    (hTo : Γ.Has "f64u_to_u64" f64uPure1Spec)
    (hEmaSwap : Γ.Has "full_ema_swap_m7" step13EmaSwapSpec)
    (hDrInit : Γ.Has "m6_hdr_dr_init" m6HdrDrMutSpec)
    (hIlog : Γ.Has "full_ilog10" fullIlog10Spec)
    (hGet64 : Γ.Has "full_m7_get64" m7Get64Spec)
    (hSet64 : Γ.Has "full_m7_set64" m7Set64Spec)
    (hLog : Γ.Has "f64u_log10_u64" f64uPure1Spec)
    (hMul : Γ.Has "f64u_mul" f64uPure2Spec) :
    ∀ a m Q X, Spec.switchModeSpec a m Q X →
      Func.wp Γ full_switch_mode_m7_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hs
  unfold Spec.switchModeSpec at hs
  obtain ⟨c, ext, s, ⟨⟩, R, rfl, hcfg, hext, hlen, _, hm, hQ⟩ := M6HdrContract.elim hs
  have hmax := c.hmaxv; unfold dimacsBound at hmax
  have hcv_le := hlen.core_ok.cur_vars_le
  rw [fullM6HdrMem_iff] at hm
  dsimp only [Func.wp, full_switch_mode_m7_body]
  refine wp_join_group (ts := [i64, i64])
    (fun _ mJ => ∃ extJ sJ, sJ.core = s.core ∧ sJ.LengthsOk c ∧
      FullExtScratchPres s sJ ∧ M6HdrExtOk extJ ∧
      (FullMem c sJ ⋆ (array64 (c.hdr - 2304) extJ ⋆ R)) mJ)
    (fun _ ⟨om, nm, ⟨⟩⟩ mJ ⟨extJ, sJ, hcoreJ, hlenJ, hpsJ, hextJ, hmJ⟩ => ?_)
    (fun Js hJs => ?_)
  · -- Shared tail after mode switch
    c0_hsteps_nogrp
    let sJ1 : FullState := { sJ with scratch := { sJ.scratch with
      switched := sJ.scratch.switched + 1#64, mode_count := sJ.scratch.mode_count + 1#64 } }
    have hlenJ1 : sJ1.LengthsOk c := ⟨hlenJ.core_ok, { hlenJ.scratch_ok with }⟩
    rs_call hEmaSwap
    refine ⟨c, sJ1, array64 (c.hdr - 2304) extJ ⋆ R, rfl, hlenJ1, ‹_›, ?_⟩
    rintro ⟨⟩ sSw mSw hcoreSw hlenSw ⟨hpsSw, _, _⟩ hmSw
    dsimp only [PreservesCoreSlice, fullSafetySlice] at hcoreSw hlenSw hmSw
    have hcoreSw0 : sSw.core = s.core := hcoreSw.trans hcoreJ
    have hpsSw0 : FullExtScratchPres s sSw := rs_ext_trans hpsJ hpsSw
    c0_hsteps_nogrp; rs_call hDrInit
    refine m6HdrDrMutSpec_of hcfg hextJ hlenSw ((fullM6HdrMem_iff ..).mpr hmSw)
      fun extD mD hinitD _ hmD => ?_
    have hlD : extD.length = 288 := hinitD.toOk.len
    have h1_lt : 1 < extD.length := by rw [hlD]; decide
    rw [fullM6HdrMem_iff] at hmD
    c0_hsteps_nogrp
    refine wp_join_group (ts := [i64])
      (fun (mbit, ()) mD1 => (∃ extD1 : List (BitVec 64), extD1.length = 288 ∧
        (FullMem c sSw ⋆ (array64 (c.hdr - 2304) extD1 ⋆ R)) mD1) ∧
        (mbit = 0#64 ∨ mbit = 1#64))
      (fun _ ⟨mbit, ⟨⟩⟩ mD1 ⟨⟨extD1, hlD1, hmD1⟩, hmbit⟩ => ?_)
      (fun Jm hJm => by
        c0_hsteps
        · exact hJm (1#64, ()) _ ⟨⟨_, by rw [List.length_set, hlD], hm⟩, Or.inr rfl⟩
        · exact hJm (0#64, ()) _ ⟨⟨_, by rw [List.length_set, hlD], hm⟩, Or.inl rfl⟩)
    have hidx2_eq : ((2 : BitVec 64) + mbit).toNat = 2 + mbit.toNat := by
      rcases hmbit with rfl | rfl <;> decide
    have hidx2_lt : ((2 : BitVec 64) + mbit).toNat < extD1.length := by
      rw [hlD1, hidx2_eq]; rcases hmbit with rfl | rfl <;> decide
    c0_hsteps_nogrp
    have ⟨extD2, hlD2, hmD2⟩ : ∃ extD2 : List (BitVec 64), extD2.length = 288 ∧
        (FullMem c sSw ⋆ (array64 (c.hdr - 2304) extD2 ⋆ R)) m :=
      ⟨_, by rw [List.length_set, hlD1], hm⟩
    have hextD2 : M6HdrExtOk extD2 := hlD2
    clear hm
    c0_hstep; c0_hsplit
    · -- Focused mode post-switch: restart_limit + randec update
      c0_hsteps_nogrp
      refine wp_join_group (ts := [i64])
        (fun _ mR => (FullMem c sSw ⋆ (array64 (c.hdr - 2304) extD2 ⋆ R)) mR)
        (fun _ ⟨d, ⟨⟩⟩ mR hmR => ?_)
        (fun Jd hJd => ?_)
      rotate_left
      · c0_hsplit; rotate_left; · c0_hsteps; exact hJd (1#64, ()) _ ‹_›
        refine wp_join_group (ts := [i64])
          (fun _ mA => (FullMem c sSw ⋆ (array64 (c.hdr - 2304) extD2 ⋆ R)) mA)
          (fun _ ⟨rc, ⟨⟩⟩ mA hmA => by
            c0_hsteps_nogrp; rs_call hIlog; intro d10 _ _; c0_hsteps_nogrp
            refine wp_join_group (ts := [i64])
              (fun _ mB => (FullMem c sSw ⋆ (array64 (c.hdr - 2304) extD2 ⋆ R)) mB)
              (fun _ ⟨d', ⟨⟩⟩ mB hmB => by c0_hsteps; exact hJd (d', ()) mB hmB)
              (fun J2 hJ2 => by c0_hsteps <;> exact hJ2 (_, ()) mA hmA))
          (fun J1 hJ1 => by c0_hsteps <;> exact hJ1 (_, ()) _ ‹_›)
      c0_hsteps_nogrp
      let sR0 : FullState := { sSw with scratch := { sSw.scratch with
        restart_limit := sSw.scratch.conflicts + d } }
      have hlenR0 : sR0.LengthsOk c := ⟨hlenSw.core_ok, { hlenSw.scratch_ok with }⟩
      refine rs_call_get64 hGet64 rfl hlenR0 ‹_› fun rem0 => ?_; c0_hsteps_nogrp
      refine rs_call_get64 hGet64 rfl hlenR0 ‹_› fun lc0 => ?_; c0_hsteps_nogrp
      refine wp_join_group (ts := [i64])
        (fun (rem1, ()) m1 => ∃ s1, s1.core = s.core ∧ s1.LengthsOk c ∧
          FullExtScratchPres s s1 ∧
          (FullMem c s1 ⋆ (array64 (c.hdr - 2304) extD2 ⋆ R)) m1)
        (fun _ ⟨rem1, ⟨⟩⟩ m1 ⟨s1, hcore1, hlen1, hps1, hm1⟩ => ?_)
        (fun Jc hJc => ?_)
      rotate_left
      · c0_hsplit; rotate_left
        · c0_hsteps; exact hJc (rem0, ()) _ ⟨sR0, hcoreSw0, hlenR0, hpsSw0, ‹_›⟩
        c0_hsteps_nogrp; refine wp_join_group (ts := [i64])
          (fun _ mA => (FullMem c sR0 ⋆ (array64 (c.hdr - 2304) extD2 ⋆ R)) mA)
          (fun _ ⟨rem', ⟨⟩⟩ mA hmA => by
            c0_hsteps_nogrp
            refine rs_call_set64 hSet64 rfl hlenR0 hmA fun sA mA hca hla hpsa hma => ?_
            c0_hsteps
            exact hJc (rem', ()) mA ⟨sA, hca.trans hcoreSw0, hla, rs_ext_trans hpsSw0 hpsa, hma⟩)
          (fun Jsub hJsub => by c0_hsteps <;> exact hJsub (_, ()) _ ‹_›)
      c0_hsteps_nogrp
      refine rs_call_set64 hSet64 rfl hlen1 hm1 fun s2 m2 hcore2 hlen2 hps2 hm2 => ?_
      have hcore20 : s2.core = s.core := hcore2.trans hcore1
      have hps20 : FullExtScratchPres s s2 := rs_ext_trans hps1 hps2
      c0_hsteps_nogrp; c0_hstep; c0_hsplit
      · refine rs_call_get64 hGet64 rfl hlen2 hm2 fun seq0 => ?_; c0_hsteps_nogrp
        refine rs_call_set64 hSet64 rfl hlen2 hm2 fun s3 m3 hcore3 hlen3 hps3 hm3 => ?_
        c0_hsteps_nogrp
        refine wp_join_group (ts := [i64]) (fun _ m4 => m3 = m4)
          (fun _ ⟨qarg, ⟨⟩⟩ m4 hm4 => by
            rcases hm4 with rfl; c0_hsteps_nogrp
            rs_call hLog; intro _; c0_hsteps_nogrp; rs_call hMul; intro _; c0_hsteps_nogrp
            rs_call hTo; intro _; c0_hsteps_nogrp
            refine wp_join_group (ts := [i64]) (fun _ m5 => m3 = m5)
              (fun _ ⟨rlen, ⟨⟩⟩ m5 hm5 => by
                rcases hm5 with rfl; c0_hsteps_nogrp
                rs_call hMul; intro _; c0_hsteps_nogrp; rs_call hTo; intro _; c0_hsteps_nogrp
                refine rs_call_set64 hSet64 rfl hlen3 hm3 fun s4 m4 hcore4 hlen4 hps4 hm4 => ?_
                c0_hsteps_nogrp
                refine rs_call_set64 hSet64 rfl hlen4 hm4 fun s5 m5 hcore5 hlen5 hps5 hm5 => ?_
                c0_hsteps
                exact hQ () extD2 s5 m5 hextD2 trivial hlen5
                  ⟨hcore5.trans (hcore4.trans (hcore3.trans hcore20)),
                   rs_ext_trans hps20 (rs_ext_trans hps3 (rs_ext_trans hps4 hps5))⟩
                  ((fullM6HdrMem_iff ..).mpr hm5))
              (fun Jr hJr => by c0_hsteps <;> exact hJr (_, ()) m3 rfl))
          (fun Jq hJq => by c0_hsteps <;> exact hJq (_, ()) m3 rfl)
      · c0_hsteps; exact hQ () extD2 s2 m2 hextD2 trivial hlen2 ⟨hcore20, hps20⟩
          ((fullM6HdrMem_iff ..).mpr hm2)
    · c0_hsteps; exact hQ () extD2 sSw _ hextD2 trivial hlenSw ⟨hcoreSw0, hpsSw0⟩
        ((fullM6HdrMem_iff ..).mpr ‹_›)
  · -- Pre-join: Focused -> Stable vs Stable -> Focused
    c0_hsplit
    · -- `h->stable == 0` (Focused -> Stable)
      c0_hsplit
      · c0_hsteps; exact hQ () ext s m hext trivial hlen ⟨rfl, rfl, rfl⟩
          ((fullM6HdrMem_iff ..).mpr hm)
      c0_hsteps_nogrp
      let s1 : FullState := { s with scratch := { s.scratch with stable := 1#64 } }
      refine wp_join_group (ts := [i64])
        (fun _ m1 => (FullMem c s1 ⋆ (array64 (c.hdr - 2304) ext ⋆ R)) m1)
        (fun _ ⟨dticks, ⟨⟩⟩ m1 hm1 => ?_)
        (fun Jd hJd => by c0_hsteps <;> exact hJd (_, ()) _ ‹_›)
      c0_hsteps_nogrp
      let s2 : FullState := { s1 with scratch := { s1.scratch with
        mode_tick_lim := s1.scratch.search_ticks + dticks,
        mode_saved_ticks := s1.scratch.search_ticks } }
      refine wp_join_group (ts := [i64])
        (fun _ m2 => (FullMem c s2 ⋆ (array64 (c.hdr - 2304) ext ⋆ R)) m2)
        (fun _ ⟨rp, ⟨⟩⟩ m2 hm2 => ?_)
        (fun Jr hJr => by
          c0_hsplit; · c0_hsplit <;> (c0_hsteps; exact hJr (_, ()) _ ‹_›)
          · c0_hsteps; exact hJr (_, ()) _ ‹_›)
      c0_hsteps_nogrp
      let s3 : FullState := { s2 with scratch := { s2.scratch with
        rel_wait := rp, rel_u := 1#64, rel_v := 1#64, rel_trigger := 0#64 } }
      have hlen3 : s3.LengthsOk c := ⟨hlen.core_ok, { hlen.scratch_ok with }⟩
      rs_call hWm4Get
      refine m6HdrW2aSpec_of rfl hcfg hext hlen3 ((fullM6HdrMem_iff ..).mpr ‹_›)
        fun ⟨wm4, ⟨⟩⟩ ext1 s4 m4 hcore4 hlen4 hm4p hext1 _ hm4 => ?_
      rw [fullM6HdrMem_iff] at hm4
      have hps4 : FullExtScratchPres s s4 := hm4p.probePres.1
      c0_hsteps_nogrp
      refine wp_join_group (ts := [i64])
        (fun _ m5 => ∃ ext5 s5, s5.core = s.core ∧ s5.LengthsOk c ∧
          FullExtScratchPres s s5 ∧ M6HdrExtOk ext5 ∧
          (FullMem c s5 ⋆ (array64 (c.hdr - 2304) ext5 ⋆ R)) m5)
        (fun _ ⟨_, ⟨⟩⟩ m5 ⟨ext5, s5, hcore5, hlen5, hps5, hext5, hm5⟩ => ?_)
        (fun Jw hJw => ?_)
      · -- Push active vars onto heap (`v < cv`)
        refine wp_loop_group (ts := [i64])
          (fun fn ⟨v, ⟨⟩⟩ mV => v.toNat ≤ s.core.cur_vars ∧ fn = s.core.cur_vars - v.toNat ∧
            ∃ sV, sV.core = s.core ∧ sV.LengthsOk c ∧ FullExtScratchPres s sV ∧
              (FullMem c sV ⋆ (array64 (c.hdr - 2304) ext5 ⋆ R)) mV) ?_ ?_
        · intro JV fn ⟨v, ⟨⟩⟩ mV hJV ⟨hv_le, hfn, sV, hcoreV, hlenV, hpsV, hmV⟩
          c0_hsplit
          · have hv_lt : v.toNat < s.core.cur_vars := by
              rw [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)] at hc; exact hc
            have hv1 : (v + 1).toNat = v.toNat + 1 := rs_add1 (by omega)
            have hv_fl : v.toNat < sV.core.flags.length := by
              rw [hcoreV, hlen.core_ok.flags_len]; omega
            c0_hsteps_nogrp
            refine wp_join_group (ts := [])
              (fun _ mN => ∃ sN, sN.core = s.core ∧ sN.LengthsOk c ∧
                FullExtScratchPres s sN ∧
                (FullMem c sN ⋆ (array64 (c.hdr - 2304) ext5 ⋆ R)) mN)
              (fun _ ⟨⟩ mN ⟨sN, hcoreN, hlenN, hpsN, hmN⟩ => by
                c0_hsteps; exact hJV (s.core.cur_vars - (v.toNat + 1)) _ mN (by omega)
                  ⟨by rw [hv1]; omega, by rw [hv1], sN, hcoreN, hlenN, hpsN, hmN⟩)
              (fun Jn hJn => by
                c0_hsplit
                · c0_hsteps_nogrp
                  refine wp_call_of_spec _ _ (hHeapPush _ _ _ _
                    ⟨c, sV, array64 (c.hdr - 2304) ext5 ⋆ R, rfl, hlenV, hmV, ?_⟩)
                  rintro ⟨⟩ sN mN hcoreN hlenN hpostN hmN
                  dsimp only [PreservesCoreSlice, fullSafetySlice] at hcoreN hlenN hmN
                  c0_hsteps
                  exact hJn () mN ⟨sN, hcoreN.trans hcoreV, hlenN,
                    rs_ext_trans hpsV hpostN.1, hmN⟩
                · c0_hsteps; exact hJn () mV ⟨sV, hcoreV, hlenV, hpsV, hmV⟩)
          · c0_hsteps; exact hJs (0#64, 1#64, ()) mV ⟨ext5, sV, hcoreV, hlenV, hpsV, hext5, hmV⟩
        · intro JV hJV; c0_hsteps
          exact hJV s.core.cur_vars (0#64, ()) m5
            ⟨Nat.zero_le _, by simp, s5, hcore5, hlen5, hps5, hm5⟩
      · -- `if (wm4 & 1 == 0)` init heap vs remove inactive vars
        c0_hsplit
        · refine wp_loop_group (ts := [i64])
            (fun fn ⟨v, ⟨⟩⟩ mV => v.toNat ≤ s.core.cur_vars ∧ fn = s.core.cur_vars - v.toNat ∧
              ∃ sV, sV.core = s.core ∧ sV.LengthsOk c ∧ FullExtScratchPres s sV ∧
                (FullMem c sV ⋆ (array64 (c.hdr - 2304) ext1 ⋆ R)) mV) ?_ ?_
          · intro JV fn ⟨v, ⟨⟩⟩ mV hJV ⟨hv_le, hfn, sV, hcoreV, hlenV, hpsV, hmV⟩
            c0_hsplit
            · have hv_lt : v.toNat < s.core.cur_vars := by
                rw [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)] at hc; exact hc
              have hv1 : (v + 1).toNat = v.toNat + 1 := rs_add1 (by omega)
              have hv_ps : v.toNat < sV.scratch.pos.length := by
                rw [hlenV.scratch_ok.pos_len]; omega
              c0_hsteps
              let sV' : FullState := { sV with scratch := { sV.scratch with
                pos := sV.scratch.pos.set v.toNat 0xFFFFFFFF#32 } }
              have hlenV' : sV'.LengthsOk c := ⟨hlenV.core_ok,
                { hlenV.scratch_ok with pos_len := by simp [sV', hlenV.scratch_ok.pos_len] }⟩
              exact hJV (s.core.cur_vars - (v.toNat + 1)) _ _ (by omega)
                ⟨by rw [hv1]; omega, by rw [hv1], sV', hcoreV, hlenV', hpsV, ‹_›⟩
            · c0_hsteps_nogrp
              let sZ : FullState := { sV with scratch := { sV.scratch with heap_len := 0 } }
              have hlenZ : sZ.LengthsOk c := ⟨hlenV.core_ok, { hlenV.scratch_ok with }⟩
              rs_call hWm4Set
              refine m6HdrW2aSpec_of rfl hcfg hext1 hlenZ ((fullM6HdrMem_iff ..).mpr ‹_›)
                fun ⟨⟩ ext2 sZ2 mZ2 hcoreZ2 hlenZ2 hmZ2p hext2 _ hmZ2 => ?_
              rw [fullM6HdrMem_iff] at hmZ2; c0_hsteps
              exact hJw (_, ()) mZ2 ⟨ext2, sZ2, hcoreZ2.trans hcoreV, hlenZ2,
                rs_ext_trans hpsV hmZ2p.probePres.1, hext2, hmZ2⟩
          · intro JV hJV; c0_hsteps
            exact hJV s.core.cur_vars (0#64, ()) m4
              ⟨Nat.zero_le _, by simp, s4, hcore4, hlen4, hps4, hm4⟩
        · -- Remove inactive vars from heap
          refine wp_loop_group (ts := [i64])
            (fun fn ⟨v, ⟨⟩⟩ mV => v.toNat ≤ s.core.cur_vars ∧ fn = s.core.cur_vars - v.toNat ∧
              ∃ sV, sV.core = s.core ∧ sV.LengthsOk c ∧ FullExtScratchPres s sV ∧
                (FullMem c sV ⋆ (array64 (c.hdr - 2304) ext1 ⋆ R)) mV) ?_ ?_
          · intro JV fn ⟨v, ⟨⟩⟩ mV hJV ⟨hv_le, hfn, sV, hcoreV, hlenV, hpsV, hmV⟩
            c0_hsplit
            · have hv_lt : v.toNat < s.core.cur_vars := by
                rw [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)] at hc; exact hc
              have hv1 : (v + 1).toNat = v.toNat + 1 := rs_add1 (by omega)
              have hv_fl : v.toNat < sV.core.flags.length := by
                rw [hcoreV, hlen.core_ok.flags_len]; omega
              have hv_ps : v.toNat < sV.scratch.pos.length := by
                rw [hlenV.scratch_ok.pos_len]; omega
              c0_hsteps_nogrp
              refine wp_join_group (ts := [])
                (fun _ mN => ∃ sN, sN.core = s.core ∧ sN.LengthsOk c ∧
                  FullExtScratchPres s sN ∧
                  (FullMem c sN ⋆ (array64 (c.hdr - 2304) ext1 ⋆ R)) mN)
                (fun _ ⟨⟩ mN ⟨sN, hcoreN, hlenN, hpsN, hmN⟩ => by
                  c0_hsteps; exact hJV (s.core.cur_vars - (v.toNat + 1)) _ mN (by omega)
                    ⟨by rw [hv1]; omega, by rw [hv1], sN, hcoreN, hlenN, hpsN, hmN⟩)
                (fun Jn hJn => by
                  c0_hsplit; rotate_left
                  · c0_hsteps; exact hJn () mV ⟨sV, hcoreV, hlenV, hpsV, hmV⟩
                  c0_hsteps_nogrp
                  refine wp_join_group (ts := [])
                    (fun _ mN => ∃ sN, sN.core = s.core ∧ sN.LengthsOk c ∧
                      FullExtScratchPres s sN ∧
                      (FullMem c sN ⋆ (array64 (c.hdr - 2304) ext1 ⋆ R)) mN)
                    (fun _ ⟨⟩ mN h => by c0_hsteps; exact hJn () mN h)
                    (fun Je hJe => by
                      refine wp_join_group (ts := [])
                        (fun _ mE => (FullMem c sV ⋆ (array64 (c.hdr - 2304) ext1 ⋆ R)) mE)
                        (fun _ ⟨⟩ mE hmE => by
                          c0_hsteps
                          let sN : FullState := { sV with scratch := { sV.scratch with
                            pos := sV.scratch.pos.set v.toNat 0xFFFFFFFF#32 } }
                          exact hJe () _ ⟨sN, hcoreV, ⟨hlenV.core_ok, { hlenV.scratch_ok with
                            pos_len := by simp [sN, hlenV.scratch_ok.pos_len] }⟩, hpsV, ‹_›⟩)
                        (fun Jelse hJelse => by
                          c0_hsplit; rotate_left; · c0_hsteps; exact hJelse () mV hmV
                          have hn_pos : 0 < (BitVec.ofNat 64 sV.scratch.heap_len).toNat := by
                            simpa using hc
                          c0_hsplit; rotate_left; · c0_hsteps; exact hJelse () mV hmV
                          have hn_le : (BitVec.ofNat 64 sV.scratch.heap_len).toNat ≤
                              s.core.cur_vars := by
                            rw [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)] at hc
                            simpa using hc
                          c0_hsplit; rotate_left; · c0_hsteps; exact hJelse () mV hmV
                          have hp_lt : (sV.scratch.pos[v.toNat]'hv_ps).toNat <
                              (BitVec.ofNat 64 sV.scratch.heap_len).toNat := hc
                          have hp_hp : ((sV.scratch.pos[v.toNat]'hv_ps).setWidth 64).toNat <
                              sV.scratch.heap.length := by
                            rw [rs_zext32, hlenV.scratch_ok.heap_len_arr]; omega
                          c0_hsplit; rotate_left; · c0_hsteps; exact hJelse () mV hmV
                          have hn1_eq : (BitVec.ofNat 64 sV.scratch.heap_len - 1#64).toNat =
                              (BitVec.ofNat 64 sV.scratch.heap_len).toNat - 1 := by bv_omega
                          have hn1_hp : (BitVec.ofNat 64 sV.scratch.heap_len - 1#64).toNat <
                              sV.scratch.heap.length := by
                            rw [hn1_eq, hlenV.scratch_ok.heap_len_arr]; omega
                          c0_hsteps_nogrp
                          let last_v := sV.scratch.heap[(BitVec.ofNat 64 sV.scratch.heap_len -
                            1#64).toNat]'hn1_hp
                          let sV1 : FullState := { sV with scratch := { sV.scratch with
                            heap_len := (BitVec.ofNat 64 sV.scratch.heap_len - 1#64).toNat } }
                          refine wp_join_group (ts := [])
                            (fun _ mA => ∃ sA, sA.core = s.core ∧ sA.LengthsOk c ∧
                              FullExtScratchPres s sA ∧
                              (FullMem c sA ⋆ (array64 (c.hdr - 2304) ext1 ⋆ R)) mA)
                            (fun _ ⟨⟩ mA ⟨sA, hcoreA, hlenA, hpsA, hmA⟩ => by
                              c0_hstep; c0_hsplit; rotate_left
                              · c0_hsteps; exact hJe () mA ⟨sA, hcoreA, hlenA, hpsA, hmA⟩
                              have hv_psA : v.toNat < sA.scratch.pos.length := by
                                rw [hlenA.scratch_ok.pos_len]; omega
                              c0_hsteps_nogrp; c0_hstep
                              let sA1 : FullState := { sA with scratch := { sA.scratch with
                                pos := sA.scratch.pos.set v.toNat 0xFFFFFFFF#32 } }
                              have hlenA1 : sA1.LengthsOk c := ⟨hlenA.core_ok,
                                { hlenA.scratch_ok with
                                  pos_len := by simp [sA1, hlenA.scratch_ok.pos_len] }⟩
                              c0_hsplit; rotate_left
                              · c0_hsteps; exact hJe () _ ⟨sA1, hcoreA, hlenA1, hpsA, ‹_›⟩
                              have hlast_lt : (last_v.setWidth 64).toNat < s.core.cur_vars := by
                                rw [rs_zext32]; dsimp only [last_v]
                                rw [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)] at hc
                                simpa only [hn1_eq, BitVec.toNat_ofNat,
                                  show (1 : BitVec 64).toNat = 1 from rfl,
                                  show (2 ^ 64 - 1 + sV.scratch.heap_len) % 2 ^ 64 =
                                    sV.scratch.heap_len % 2 ^ 64 - 1 by omega] using hc
                              have hp_hpA : ((sV.scratch.pos[v.toNat]'hv_ps).setWidth 64).toNat <
                                  sA1.scratch.heap.length := by
                                rw [rs_zext32, hlenA1.scratch_ok.heap_len_arr]; omega
                              have hlast_psA : (last_v.setWidth 64).toNat <
                                  sA1.scratch.pos.length := by
                                rw [hlenA1.scratch_ok.pos_len]; omega
                              c0_hsteps_nogrp
                              let sA2 : FullState := { sA1 with scratch := { sA1.scratch with
                                heap := sA1.scratch.heap.set
                                  ((sV.scratch.pos[v.toNat]'hv_ps).setWidth 64).toNat last_v,
                                pos := sA1.scratch.pos.set (last_v.setWidth 64).toNat
                                  (sV.scratch.pos[v.toNat]'hv_ps) } }
                              have hlenA2 : sA2.LengthsOk c := ⟨hlenA1.core_ok,
                                { hlenA1.scratch_ok with
                                  heap_len_arr := by simp [sA2, hlenA1.scratch_ok.heap_len_arr]
                                  pos_len := by simp [sA2, hlenA1.scratch_ok.pos_len] }⟩
                              refine wp_call_of_spec _ _ (hHeapUp _ _ _ _
                                ⟨c, sA2, array64 (c.hdr - 2304) ext1 ⋆ R, rfl, hlenA2, ‹_›, ?_⟩)
                              rintro ⟨⟩ sU mU hcoreU hlenU ⟨hpsU, _⟩ hmU; c0_hsteps_nogrp
                              refine wp_call_of_spec _ _ (hHeapDown _ _ _ _
                                ⟨c, sU, array64 (c.hdr - 2304) ext1 ⋆ R, rfl, hlenU, hmU, ?_⟩)
                              rintro ⟨⟩ sD mD hcoreD hlenD ⟨_, hpsD⟩ hmD; c0_hsteps
                              exact hJe () mD ⟨sD, Eq.trans hcoreD (Eq.trans hcoreU hcoreA), hlenD,
                                rs_ext_trans hpsA (rs_ext_trans hpsU.1 hpsD.1), hmD⟩)
                            (fun Jla hJla => by
                              c0_hsplit
                              · have hlast_lt : (last_v.setWidth 64).toNat < s.core.cur_vars := by
                                  rw [rs_zext32]; dsimp only [last_v]
                                  rw [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)] at hc
                                  simpa only [hn1_eq, BitVec.toNat_ofNat,
                                    show (1 : BitVec 64).toNat = 1 from rfl,
                                    show (2 ^ 64 - 1 + sV.scratch.heap_len) % 2 ^ 64 =
                                      sV.scratch.heap_len % 2 ^ 64 - 1 by omega] using hc
                                have hlast_ps : (last_v.setWidth 64).toNat <
                                    sV1.scratch.pos.length := by
                                  rw [hlenV.scratch_ok.pos_len]; omega
                                c0_hsteps
                                let sA : FullState := { sV1 with scratch := { sV1.scratch with
                                  pos := sV1.scratch.pos.set (last_v.setWidth 64).toNat
                                    0xFFFFFFFF#32 } }
                                exact hJla () _ ⟨sA, hcoreV, ⟨hlenV.core_ok,
                                  { hlenV.scratch_ok with
                                    pos_len := by
                                      rw [List.length_set]; exact hlenV.scratch_ok.pos_len }⟩,
                                  hpsV, ‹_›⟩
                              · c0_hsteps; exact hJla () _ ⟨sV1, hcoreV,
                                  ⟨hlenV.core_ok, { hlenV.scratch_ok with }⟩, hpsV, ‹_›⟩))))
            · c0_hsteps; exact hJw (_, ()) mV ⟨ext1, sV, hcoreV, hlenV, hpsV, hext1, hmV⟩
          · intro JV hJV; c0_hsteps
            exact hJV s.core.cur_vars (0#64, ()) m4
              ⟨Nat.zero_le _, by simp, s4, hcore4, hlen4, hps4, hm4⟩
    · -- `h->stable != 0` (Stable -> Focused)
      c0_hsplit
      · c0_hsteps; exact hQ () ext s m hext trivial hlen ⟨rfl, rfl, rfl⟩
          ((fullM6HdrMem_iff ..).mpr hm)
      c0_hsteps_nogrp
      let s1 : FullState := { s with scratch := { s.scratch with stable := 0#64 } }
      rs_call hNlog; intro _; c0_hsteps_nogrp
      rs_call hTo; intro rTo; c0_hsteps_nogrp
      let s2 : FullState := { s1 with scratch := { s1.scratch with
        mode_confl_lim := s1.scratch.conflicts + 1000#64 * rTo,
        mode_saved_ticks := s1.scratch.search_ticks, q_search_idx := s1.scratch.q_last } }
      refine wp_join_group (ts := [])
        (fun _ m3 => ∃ qss : BitVec 64,
          (FullMem c { s2 with scratch := { s2.scratch with q_search_stamp := qss } } ⋆
            (array64 (c.hdr - 2304) ext ⋆ R)) m3)
        (fun _ ⟨⟩ m3 ⟨qss, hm3⟩ => by
          let s3 : FullState := { s2 with scratch := { s2.scratch with q_search_stamp := qss } }
          c0_hsteps; exact hJs (1#64, 0#64, ()) m3 ⟨ext, s3, rfl,
            ⟨hlen.core_ok, { hlen.scratch_ok with }⟩, ⟨rfl, rfl⟩, hext, hm3⟩)
        (fun Jq hJq => by
          c0_hsplit
          · have hql_lt : s.scratch.q_last.toNat < s.core.cur_vars := by
              rw [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)] at hc; exact hc
            have hql_qs : s.scratch.q_last.toNat < s.scratch.q_stamp.length := by
              rw [hlen.scratch_ok.q_stamp_len]; omega
            c0_hsteps; exact hJq () _ ⟨_, ‹_›⟩
          · c0_hsteps; exact hJq () _ ⟨s2.scratch.q_search_stamp, ‹_›⟩)

end LeanQbe.T.Examples.Kissat.Proof.Restart
