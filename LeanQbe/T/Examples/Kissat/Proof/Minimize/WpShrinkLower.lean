/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Minimize.Spec
public import LeanQbe.T.Examples.Kissat.Src.Minimize
public import LeanQbe.T.Logic.CanonicalEnv
import LeanQbe.T.Examples.Kissat.Proof.Minimize.MinTactics
import LeanQbe.T.Examples.Kissat.Proof.Minimize.WpMinDfsHelpers
import LeanQbe.T.Examples.Kissat.Proof.Lib.ContractLemmas
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
import LeanQbe.T.Logic.C0Grind
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.ControlComb

/-!
# `full_shrink_lower_m8` WP Proof for `Kissat.Src.Minimize`

Proves `Func.wp Γ full_shrink_lower_m8_body ...` against canonical `Spec.fullShrinkLowerSpec`,
consuming `Γ.Has "full_min_mark" Spec.fullMinMarkSpec` and
`Γ.Has "full_min_lit_dfs_m8" Spec.fullMinLitDfsSpec`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Minimize

open Std Std.Sat
open LeanQbe.T LeanQbe.T.C0Grind LeanQbe.T.C0HeadStep LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open LeanQbe.T.Examples.Kissat.Src.Minimize
open FullMinTactics
open scoped FullArenaTactics FullMinTactics
open Kraken.Bedrock2.Test

private theorem full_shrink_lower_mark_step {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    {ov : BitVec 32} {tag : BitVec 8} {d : M8DfsScratch}
    (_hcore : FullOtfsCoreInv c F0 s) (hov_lt : ov.toNat < s.core.cur_vars)
    (hlen_d : (d.st s).LengthsOk c) (hno8_d : ((d.st s).core.mrk[ov.toNat]?.getD 0#8 &&& 8#8) = 0#8)
    (hab_d : ∀ v, s.core.cur_vars ≤ v → d.mrk[v]? = s.core.mrk[v]?)
    (hmono_d : ∀ v < s.core.cur_vars,
      (s.core.mrk[v]?.getD 0#8 &&& 2#8) ≠ 0#8 → (d.mrk[v]?.getD 0#8 &&& 2#8) ≠ 0#8)
    (hbit8_d : ∀ v < s.core.cur_vars,
      (d.mrk[v]?.getD 0#8 &&& 8#8) = (s.core.mrk[v]?.getD 0#8 &&& 8#8))
    (htag : tag = 2#8 ∨ tag = 4#8)
    {R : Mem 64 → Prop} {m_f : Mem 64}
    (hm_f : (FullMem c (fullMinMarkStepState (d.st s) ov.toNat tag) ⋆ R) m_f) :
    let st_f := fullMinMarkStepState (d.st s) ov.toNat tag
    let d_f : M8DfsScratch := { d with
      mrk := st_f.core.mrk
      min_clr := st_f.core.min_clr
      mcl := st_f.core.min_clr_len
      mcf := st_f.core.min_clr_full }
    d_f.st s = st_f ∧
    (d_f.st s).LengthsOk c ∧
    (∀ v, s.core.cur_vars ≤ v → d_f.mrk[v]? = s.core.mrk[v]?) ∧
    (∀ v < s.core.cur_vars,
      (s.core.mrk[v]?.getD 0#8 &&& 2#8) ≠ 0#8 → (d_f.mrk[v]?.getD 0#8 &&& 2#8) ≠ 0#8) ∧
    (∀ v < s.core.cur_vars,
      (d_f.mrk[v]?.getD 0#8 &&& 8#8) = (s.core.mrk[v]?.getD 0#8 &&& 8#8)) ∧
    (FullMem c (d_f.st s) ⋆ R) m_f := by
  have hstep := m8MinLit_state_step (s := s) (mrk1 := d.mrk) (wsort1 := d.wsort)
    (mclr1 := d.min_clr) (mcl1 := d.mcl) (mcf1 := d.mcf) (ticks1 := d.ticks) ov.toNat tag
  have hbm_f := fullMinMarkStepState_bit8_mono2 hlen_d hov_lt htag hno8_d
  have hlen_f := fullMinMarkStepState_lengths hlen_d ov.toNat tag
  refine ⟨hstep.symm, hstep.symm ▸ hlen_f,
    fun v hv => (fullMinMarkStepState_mrk_above (s := d.st s) hov_lt tag v hv).trans (hab_d v hv),
    fun w hw h2w => hbm_f.2 w hw (hmono_d w hw h2w),
    fun w hw => (hbm_f.1 w hw).trans (hbit8_d w hw),
    hstep.symm ▸ hm_f⟩

public section

theorem full_shrink_lower_m8_wp (Γ : Env)
    (hMm : Γ.Has "full_min_mark" Spec.minMarkSpec)
    (hDfs : Γ.Has "full_min_lit_dfs_m8" Spec.minLitDfsSpec) :
    ∀ args m Q X, Spec.shrinkLowerSpec args m Q X →
      Func.wp Γ full_shrink_lower_m8_body args m Q X := by
  rintro ⟨h, ot, ov, ⟨⟩⟩ m Q X hsp
  obtain ⟨c, s, ⟨F0, keepSet⟩, R, rfl, _, ⟨hov, hcore, hmin, hot, hval, hlvl, hno8⟩, hm, hQ⟩ :=
    FullContract.elim hsp
  have hlen0 := hcore.1.core_ok
  have hcv := hlen0.cur_vars_le
  have hov_lt : ov.toNat < s.core.cur_vars := by omega
  have hov_mrk : (ov.setWidth 64).toNat < s.core.mrk.length := by
    rw [hlen0.mrk_len, bv_c0_zext32_64]; omega
  have hno8_ov : (s.core.mrk[ov.toNat]?.getD 0#8 &&& 8#8) = 0#8 :=
    hno8 ov.toNat hov_lt (by rw [hov]; exact Nat.le_refl _)
  unfold Func.wp full_shrink_lower_m8_body; dsimp only [full_shrink_lower_m8_body]
  c0_hsteps_nogrp; c0_hsplit
  · have h2_nz : (s.core.mrk[ov.toNat]?.getD 0#8 &&& 2#8) ≠ 0#8 := by
      rw [List.getElem?_eq_getElem (by rw [hlen0.mrk_len]; omega), Option.getD_some]
      c0_bv_bit_grind
    c0_hsteps!
    exact hQ (true, ()) s m hcore.1
      ⟨⟨rfl, fun _ _ => rfl, fun _ _ h => h, fun _ _ => rfl, hmin⟩, fun _ => h2_nz⟩ hm
  · let FailPost : Tup Val [] → Mem 64 → Prop := fun () m_d =>
      ∃ d : M8DfsScratch,
        let st_d := d.st s
        st_d.LengthsOk c ∧
        (∀ v, s.core.cur_vars ≤ v → d.mrk[v]? = s.core.mrk[v]?) ∧
        (∀ v < s.core.cur_vars,
          (s.core.mrk[v]?.getD 0#8 &&& 2#8) ≠ 0#8 → (d.mrk[v]?.getD 0#8 &&& 2#8) ≠ 0#8) ∧
        (∀ v < s.core.cur_vars,
          (d.mrk[v]?.getD 0#8 &&& 8#8) = (s.core.mrk[v]?.getD 0#8 &&& 8#8)) ∧
        FullMinMarkInv st_d.core keepSet ∧
        (FullMem c st_d ⋆ R) m_d
    refine wp_join_group (ts := []) FailPost ?_ ?_
    · rintro _ ⟨⟩ m_d ⟨d, hlen_d, hab_d, hmono_d, hbit8_d, hmin_d, hm_d⟩
      rw [Blocks.get_here]
      have hsc_d : FullOtfsCoreInv c F0 (d.st s) :=
        m8FullOtfsCoreInv_with_state hcore hlen_d.core_ok.mrk_len hlen_d.scratch_ok.wsort_len
          hlen_d.core_ok.min_clr_len_arr hlen_d.core_ok.min_clr_len_le
      have hno8_d : ((d.st s).core.mrk[ov.toNat]?.getD 0#8 &&& 8#8) = 0#8 := by
        dsimp only [M8DfsScratch.st, m8MinLitDfsState]; rwa [hbit8_d ov.toNat hov_lt]
      c0_hsteps!; apply wp_call_of_spec; apply hMm
      refine fullMinMarkSpec_step hlen_d hm_d ov hov_lt 4#8 fun m_f hm_f => ?_
      obtain ⟨hst_eq, hlen_f, hab_f, hmono_f, hbit8_f, hm_f'⟩ :=
        full_shrink_lower_mark_step hcore hov_lt hlen_d hno8_d hab_d hmono_d hbit8_d
          (Or.inr rfl) hm_f
      have hmin_f : FullMinMarkInv (fullMinMarkStepState (d.st s) ov.toNat 4#8).core keepSet :=
        fullMinMarkInv_step_poison hsc_d hmin_d hov_lt hno8_d
      c0_hsteps!
      exact hQ (false, ()) _ m_f (hst_eq ▸ hlen_f)
        ⟨⟨hst_eq ▸ rfl, hab_f, hmono_f, hbit8_f, hst_eq ▸ hmin_f⟩, fun hc => by cases hc⟩
        (hst_eq ▸ hm_f')
    · rintro Jfail hJfail
      c0_hsteps_nogrp; c0_hsplit
      · exact hJfail () m ⟨M8DfsScratch.ofState s, hcore.1, (fun _ _ => rfl),
          (fun _ _ h => h), (fun _ _ => rfl), hmin, hm⟩
      · c0_hsteps!; apply wp_call_of_spec; apply hDfs
        dsimp only [Spec.minLitDfsSpec]
        refine FullContract.intro (w := (F0, keepSet)) hcore.1 ⟨hcore, hmin, hot, hval,
          by simpa only [vals, Arg.val, hov] using hlvl,
          fun v hv hlv => hno8 v hv (by simpa only [vals, Arg.val, hov] using hlv)⟩ hm ?_
        rintro ⟨ok_d, ⟨⟩⟩ st_d m_d hlen_d ⟨⟨hframe_d, hab_d, hmono_d, hbit8_d, hmin_d⟩, hok_d⟩ hm_d
        have hst_d_eq := minLitDfsMask_eq hframe_d
        let d : M8DfsScratch := ⟨st_d.core.mrk, st_d.scratch.wsort, st_d.core.min_clr,
          st_d.core.min_clr_len, st_d.core.min_clr_full, st_d.scratch.search_ticks⟩
        have hdst : d.st s = st_d := hst_d_eq.symm
        rw [← hdst] at hlen_d hab_d hmono_d hbit8_d hmin_d hok_d hm_d
        c0_hsplit
        · have hok_true : ok_d = true := by c0_grind
          have hno8_d : ((d.st s).core.mrk[ov.toNat]?.getD 0#8 &&& 8#8) = 0#8 := by
            dsimp only [M8DfsScratch.st, m8MinLitDfsState]; rwa [hbit8_d ov.toNat hov_lt]
          c0_hsteps!; apply wp_call_of_spec; apply hMm
          refine fullMinMarkSpec_step hlen_d hm_d ov hov_lt 2#8 fun m_f hm_f => ?_
          obtain ⟨hst_eq, hlen_f, hab_f, hmono_f, hbit8_f, hm_f'⟩ :=
            full_shrink_lower_mark_step hcore hov_lt hlen_d hno8_d hab_d hmono_d hbit8_d
              (Or.inl rfl) hm_f
          have hmin_f :
              FullMinMarkInv (fullMinMarkStepState (d.st s) ov.toNat 2#8).core keepSet := by
            dsimp only [fullMinMarkStepState, fullMinMarkStepCore]; split
            · exact hmin_d
            · dsimp only [vals, Arg.val] at hok_d; rw [← hov] at hok_d
              exact (hok_d hok_true).2
          have h2_ov : ((fullMinMarkStepState (d.st s) ov.toNat 2#8).core.mrk[ov.toNat]?.getD
              0#8 &&& 2#8) ≠ 0#8 := by
            dsimp only [fullMinMarkStepState, fullMinMarkStepCore]; split
            · rename_i hc; exact hc.resolve_left (Nat.not_le.mpr hov_lt)
            · dsimp only [fullMinMarkCore]
              rw [List.getElem?_set_self (by rw [hlen_d.core_ok.mrk_len]; omega), Option.getD_some]
              exact bv8_and2_of_or2 _
          c0_hsteps!
          exact hQ (true, ()) _ m_f (hst_eq ▸ hlen_f)
            ⟨⟨hst_eq ▸ rfl, hab_f, hmono_f, hbit8_f, hst_eq ▸ hmin_f⟩, fun _ => hst_eq ▸ h2_ov⟩
            (hst_eq ▸ hm_f')
        · exact hJfail () m_d ⟨d, hlen_d, hab_d, hmono_d, hbit8_d, hmin_d, hm_d⟩

end

end LeanQbe.T.Examples.Kissat.Proof.Minimize
