/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Backtrack.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Decide.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Float64.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Lib.ContractLemmas
public import LeanQbe.T.Examples.Kissat.Proof.Restart.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts3
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Header
public import LeanQbe.T.Examples.Kissat.Src.Restart
public import LeanQbe.T.Logic.CanonicalEnv
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics1
import LeanQbe.T.Examples.Kissat.Proof.Spec.WitnessInv1
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Canonical WP Proofs for `Kissat.Src.Restart` — Part 0 (`full_restart_due`, `full_restart`)

Proves `full_restart_due_wp` (`fullRestartDueSpec`) and `full_restart_wp` (`fullRestartSpec`)
against `Src.Restart` (`0` legacy imports, `0` `@[expose]` on theorems/lemmas/sections).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Restart

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Decide.Spec
open LeanQbe.T.Examples.Kissat.Proof.Float64.Spec
open LeanQbe.T.Examples.Kissat.Src.Restart
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics

local macro "rs_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

private theorem bv64_add1_toNat {x : BitVec 64} (hx : x.toNat + 1 < 2 ^ 64) :
    (x + 1#64).toNat = x.toNat + 1 := by
  rw [BitVec.toNat_add, show (1#64 : BitVec 64).toNat = 1 from rfl, Nat.mod_eq_of_lt hx]

private theorem extPres_trans {s1 s2 s3 : FullState}
    (h12 : FullExtScratchPres s1 s2) (h23 : FullExtScratchPres s2 s3) :
    FullExtScratchPres s1 s3 :=
  ⟨h23.1.trans h12.1, h23.2.trans h12.2⟩

/-- Soundness proof for `full_restart_due` against `restartDueSpec`. -/
theorem full_restart_due_wp (Γ : Env)
    (hSub : Γ.Has "f64u_sub" f64uPure2Spec)
    (hMul : Γ.Has "f64u_mul" f64uPure2Spec)
    (hLog : Γ.Has "f64u_log10_u64" f64uPure1Spec)
    (hTo : Γ.Has "f64u_to_u64" f64uPure1Spec) :
    ∀ a m Q X, Spec.restartDueSpec a m Q X →
      Func.wp Γ full_restart_due_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hs
  unfold Spec.restartDueSpec at hs
  obtain ⟨c, s, ⟨⟩, R, rfl, hlen, _, hm, hQ⟩ := FullContract.elim hs
  have hret0 : Q (0#64, ()) m := hQ (0#64, ()) s m hlen ⟨rfl, Or.inl rfl, rfl, rfl⟩ hm
  dsimp only [Func.wp, full_restart_due_body]
  c0_hsteps_nogrp
  · exact hret0
  · exact hret0
  · let s1 : FullState := { s with scratch := { s.scratch with rel_trigger := 0#64 } }
    exact hQ (1#64, ()) s1 _ ⟨hlen.core_ok, { hlen.scratch_ok with }⟩
      ⟨rfl, Or.inr rfl, rfl, rfl⟩ ‹_›
  · exact hret0
  · refine wp_join_group (ts := [Ty.bool]) (fun _ m1 => m = m1)
      (fun _ ⟨fire, ⟨⟩⟩ m1 hm1 => ?_)
      (fun J hJ => by
        refine wp_join_group (ts := []) (fun _ mE => m = mE)
          (fun _ ⟨⟩ mE hmE => by
            rcases hmE with rfl
            refine wp_join_group (ts := [i64]) (fun _ mB => m = mB)
              (fun _ ⟨fdiv, ⟨⟩⟩ mB hmB => by
                rcases hmB with rfl
                refine wp_join_group (ts := [i64]) (fun _ mC => m = mC)
                  (fun _ ⟨sdiv, ⟨⟩⟩ mC hmC => by
                    rcases hmC with rfl
                    c0_hsteps_nogrp
                    · exact hret0
                    · exact hret0
                    · rs_call hMul; intro _; c0_hsteps_nogrp; rs_call hMul; intro _
                      c0_hsteps_nogrp; rs_call hMul; intro _; c0_hsteps
                      exact hJ (_, ()) m rfl)
                  (fun J2 hJ2 => by
                    c0_hsplit; · c0_hsteps; exact hJ2 (_, ()) m rfl
                    · c0_hsteps_nogrp; rs_call hSub; intro _; c0_hsteps
                      exact hJ2 (_, ()) m rfl))
              (fun J1 hJ1 => by
                c0_hsplit; · c0_hsteps; exact hJ1 (_, ()) m rfl
                · c0_hsteps_nogrp; rs_call hSub; intro _; c0_hsteps; exact hJ1 (_, ()) m rfl))
          (fun JE hJE => by
            c0_hsplit
            · c0_hsplit
              · c0_hsteps_nogrp; rs_call hMul; intro _; c0_hsteps; exact hJ (_, ()) m rfl
              · c0_hsteps; exact hJE () m rfl
            · c0_hsteps; exact hJE () m rfl))
    rcases hm1 with rfl
    c0_hsplit
    · refine wp_join_group (ts := [i64]) (fun _ m2 => m = m2)
        (fun _ ⟨rst, ⟨⟩⟩ m2 hm2 => by
          rcases hm2 with rfl
          c0_hsteps_nogrp; rs_call hLog; intro _
          c0_hsteps_nogrp; rs_call hTo; intro _
          c0_hsteps_nogrp
          refine wp_join_group (ts := [i64]) (fun _ m3 => m = m3)
            (fun _ ⟨d, ⟨⟩⟩ m3 hm3 => by
              rcases hm3 with rfl; c0_hsteps
              let s1 : FullState := { s with scratch := { s.scratch with
                restart_limit := s.scratch.conflicts + d } }
              exact hQ (1#64, ()) s1 _ ⟨hlen.core_ok, { hlen.scratch_ok with }⟩
                ⟨rfl, Or.inr rfl, rfl, rfl⟩ ‹_›)
            (fun Jd hJd => by c0_hsteps <;> exact hJd (_, ()) m rfl))
        (fun Jr hJr => by c0_hsteps <;> exact hJr (_, ()) m rfl)
    · c0_hsteps; exact hret0

/-- Soundness proof for `full_restart` against `restartSpec`. -/
theorem full_restart_wp (Γ : Env)
    (hRandec : Γ.Has "full_randec_var_lvl_fid" fullRandecVarLvlSpec)
    (hNDV : Γ.Has "full_next_dec_var" fullNextDecVarSpec)
    (hBT : Γ.Has "full_backtrack" fullBacktrackSpec) :
    ∀ a m Q X, Spec.restartSpec a m Q X →
      Func.wp Γ full_restart_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hs
  unfold Spec.restartSpec at hs
  obtain ⟨c, s, F0, R, rfl, hlen, hinv, hm, hQ⟩ := FullContract.elim hs
  have hmax := c.hmaxv; unfold dimacsBound at hmax
  obtain ⟨F_cur, hw0⟩ := hinv.witness
  have hcl_le : s.core.cur_level ≤ c.max_vars :=
    Nat.le_trans hw0.cur_level_le
      (Nat.le_trans hlen.core_ok.trail_end_le hlen.core_ok.cur_vars_le)
  dsimp only [Func.wp, full_restart_body]
  c0_hsteps_nogrp
  let s1 : FullState := { s with scratch := { s.scratch with
    restarts := s.scratch.restarts + 1#64 } }
  have hlen1 : s1.LengthsOk c := ⟨hlen.core_ok, { hlen.scratch_ok with }⟩
  refine wp_call_of_spec _ _ (hRandec _ _ _ _ ⟨c, s1, R, rfl, hlen1, ‹_›, ?_⟩)
  rintro ⟨nv0, ⟨⟩⟩ s2 m2 hcore2 hlen2 ⟨hpres2, _⟩ hm2
  dsimp only [PreservesCoreSlice, fullSafetySlice] at hcore2 hlen2 hm2
  refine wp_join_group (ts := [i64])
    (fun (_nv, ()) m3 => ∃ s3, s3.core = s.core ∧ s3.LengthsOk c ∧
      FullExtScratchPres s s3 ∧ (FullMem c s3 ⋆ R) m3)
    (fun _ ⟨nv, ⟨⟩⟩ m3 ⟨s3, hcore3, hlen3, hpres3, hm3⟩ => ?_)
    (fun Jnv hJnv => by
      c0_hsplit
      · c0_hsteps_nogrp
        refine wp_call_of_spec _ _ (hNDV _ _ _ _ ⟨c, s2, R, rfl, hlen2, hm2, ?_⟩)
        rintro ⟨nv1, ⟨⟩⟩ s3 m3 hcore3 hlen3 ⟨hpres3, _⟩ hm3
        dsimp only [PreservesCoreSlice, fullSafetySlice] at hcore3 hlen3 hm3
        c0_hsteps
        exact hJnv (nv1, ()) m3 ⟨s3, hcore3.trans hcore2, hlen3,
          extPres_trans hpres2 hpres3, hm3⟩
      · c0_hsteps; exact hJnv (nv0, ()) m2 ⟨s2, hcore2, hlen2, hpres2, hm2⟩)
  have hcv3_le : s3.core.cur_vars ≤ c.max_vars := hlen3.core_ok.cur_vars_le
  refine wp_join_group (ts := [i64])
    (fun (reuse, ()) m4 => m3 = m4 ∧ reuse.toNat ≤ s3.core.cur_level)
    (fun _ ⟨reuse, ⟨⟩⟩ m4 ⟨hm4, hreuse⟩ => ?_)
    (fun Jre hJre => ?_)
  · rcases hm4 with rfl
    have hcl3_lt : s3.core.cur_level < 2 ^ 64 := by rw [hcore3]; omega
    have htv : reuse.toNat < s3.core.cur_level → reuse.toNat < c.max_vars := by
      intro hlt; rw [hcore3] at hlt; omega
    c0_hsteps_nogrp
    refine wp_call_of_spec _ _
      (hBT _ _ _ _ ⟨c, s3, R, rfl, hlen3, hcl3_lt, htv,
        by rw [hcore3]; exact hw0.trail_lits_lt, hm3, ?_⟩)
    intro vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' mB sB hsB _ _ hclB hpresB
      _ _ _ hw1 _ hmB
    have hsB_eq : sB = FullState.mk
        { s.core with
          vals := vals', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
          trail_end := te', propagated := prop', cur_level := cl', unassigned := unass' }
        sc' := by
      dsimp only [sB]; rw [hcore3]
    have hinvB : FullCoreInv c F0 sB :=
      ⟨hsB, F_cur, hw1 F0 F_cur (by rw [hcore3]; exact hw0) hreuse⟩
    c0_hsteps
    refine hQ () sB mB hsB ⟨congrArg FullState.core hsB_eq, hinvB,
      by change cl' ≤ s.core.cur_level; rw [hclB, hcore3]; exact Nat.min_le_left _ _,
      extPres_trans hpres3 hpresB.1⟩ hmB
  · c0_hsplit; rotate_left; · c0_hsteps; exact hJre (0#64, ()) m3 ⟨rfl, Nat.zero_le _⟩
    have hnv_lt : nv.toNat < s3.core.cur_vars := by
      rw [Nat.mod_eq_of_lt (by omega : s3.core.cur_vars < 2 ^ 64)] at hc; exact hc
    c0_hsplit; rotate_left; · c0_hsteps; exact hJre (0#64, ()) m3 ⟨rfl, Nat.zero_le _⟩
    c0_hsteps_nogrp
    refine wp_join_group (ts := [i64])
      (fun (r, ()) mS => m3 = mS ∧ r.toNat ≤ s3.core.cur_level)
      (fun _ ⟨r, ⟨⟩⟩ mS h => by c0_hsteps; exact hJre (r, ()) mS h)
      (fun Jst hJst => by
        c0_hsplit
        · have hnv_sc : nv.toNat < s3.scratch.score.length := by
            rw [hlen3.scratch_ok.score_len]; omega
          c0_hsteps_nogrp
          refine wp_join_group (ts := [i64])
            (fun (r, ()) mB => m3 = mB ∧ r.toNat ≤ s3.core.cur_level)
            (fun _ ⟨r, ⟨⟩⟩ mB h => by c0_hsteps; exact hJst (r, ()) mB h)
            (fun Jbrk hJbrk => by
              refine wp_loop_group (ts := [i64])
                (fun fn ⟨reuse, ⟨⟩⟩ mL => m3 = mL ∧ reuse.toNat ≤ s3.core.cur_level ∧
                  fn = s3.core.cur_level - reuse.toNat) ?_ ?_
              · intro JL fn ⟨reuse, ⟨⟩⟩ mL hJL ⟨hmL, hre_le, hfn⟩
                rcases hmL with rfl
                c0_hsplit; rotate_left; · c0_hsteps; exact hJbrk (reuse, ()) m3 ⟨rfl, hre_le⟩
                have hre_lt : reuse.toNat < s3.core.cur_level := by
                  rw [Nat.mod_eq_of_lt (by rw [hcore3]; omega : s3.core.cur_level < 2 ^ 64)] at hc
                  exact hc
                have hre1 : (reuse + 1).toNat = reuse.toNat + 1 :=
                  bv64_add1_toNat (by rw [hcore3] at hre_lt; omega)
                have hre1_fd : (reuse + 1).toNat < s3.core.frame_dec.length := by
                  rw [hlen3.core_ok.frame_dec_len, hre1]; rw [hcore3] at hre_lt; omega
                c0_hsteps_nogrp
                c0_hsplit; · c0_hsteps; exact hJbrk (reuse, ()) m3 ⟨rfl, hre_le⟩
                have hdv_lt :
                    ((s3.core.frame_dec[(reuse + 1).toNat]'hre1_fd >>> 1#32).setWidth 64).toNat <
                    s3.scratch.score.length := by
                  rw [hlen3.scratch_ok.score_len]
                  have h1 : ¬ s3.core.cur_vars % 2 ^ 64 ≤
                      ((s3.core.frame_dec[(reuse + 1).toNat]'hre1_fd >>> 1#32).setWidth 64).toNat
                      := hc
                  rw [Nat.mod_eq_of_lt (by omega : s3.core.cur_vars < 2 ^ 64)] at h1; omega
                c0_hsplit; · c0_hsteps; exact hJbrk (reuse, ()) m3 ⟨rfl, hre_le⟩
                · c0_hsteps; exact hJL (s3.core.cur_level - (reuse.toNat + 1)) _ m3 (by omega)
                    ⟨rfl, by rw [hre1]; omega, by rw [hre1]⟩
              · intro JL hJL; c0_hsteps
                exact hJL s3.core.cur_level (0#64, ()) m3 ⟨rfl, Nat.zero_le _, by simp⟩)
        · have hnv_qs : nv.toNat < s3.scratch.q_stamp.length := by
            rw [hlen3.scratch_ok.q_stamp_len]; omega
          c0_hsteps_nogrp
          refine wp_join_group (ts := [i64])
            (fun (r, ()) mB => m3 = mB ∧ r.toNat ≤ s3.core.cur_level)
            (fun _ ⟨r, ⟨⟩⟩ mB h => by c0_hsteps; exact hJst (r, ()) mB h)
            (fun Jbrk hJbrk => by
              refine wp_loop_group (ts := [i64])
                (fun fn ⟨reuse, ⟨⟩⟩ mL => m3 = mL ∧ reuse.toNat ≤ s3.core.cur_level ∧
                  fn = s3.core.cur_level - reuse.toNat) ?_ ?_
              · intro JL fn ⟨reuse, ⟨⟩⟩ mL hJL ⟨hmL, hre_le, hfn⟩
                rcases hmL with rfl
                c0_hsplit; rotate_left; · c0_hsteps; exact hJbrk (reuse, ()) m3 ⟨rfl, hre_le⟩
                have hre_lt : reuse.toNat < s3.core.cur_level := by
                  rw [Nat.mod_eq_of_lt (by rw [hcore3]; omega : s3.core.cur_level < 2 ^ 64)] at hc
                  exact hc
                have hre1 : (reuse + 1).toNat = reuse.toNat + 1 :=
                  bv64_add1_toNat (by rw [hcore3] at hre_lt; omega)
                have hre1_fd : (reuse + 1).toNat < s3.core.frame_dec.length := by
                  rw [hlen3.core_ok.frame_dec_len, hre1]; rw [hcore3] at hre_lt; omega
                c0_hsteps_nogrp
                c0_hsplit; · c0_hsteps; exact hJbrk (reuse, ()) m3 ⟨rfl, hre_le⟩
                have hdv_lt :
                    ((s3.core.frame_dec[(reuse + 1).toNat]'hre1_fd >>> 1#32).setWidth 64).toNat <
                    s3.scratch.q_stamp.length := by
                  rw [hlen3.scratch_ok.q_stamp_len]
                  have h1 : ¬ s3.core.cur_vars % 2 ^ 64 ≤
                      ((s3.core.frame_dec[(reuse + 1).toNat]'hre1_fd >>> 1#32).setWidth 64).toNat
                      := hc
                  rw [Nat.mod_eq_of_lt (by omega : s3.core.cur_vars < 2 ^ 64)] at h1; omega
                c0_hsplit; · c0_hsteps; exact hJbrk (reuse, ()) m3 ⟨rfl, hre_le⟩
                · c0_hsteps; exact hJL (s3.core.cur_level - (reuse.toNat + 1)) _ m3 (by omega)
                    ⟨rfl, by rw [hre1]; omega, by rw [hre1]⟩
              · intro JL hJL; c0_hsteps
                exact hJL s3.core.cur_level (0#64, ()) m3 ⟨rfl, Nat.zero_le _, by simp⟩))

end LeanQbe.T.Examples.Kissat.Proof.Restart
