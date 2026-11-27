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
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open LeanQbe.T.Examples.Kissat.Src.Minimize
open FullMinTactics
open scoped FullArenaTactics FullMinTactics
open Kraken.Bedrock2.Test

public section

theorem full_shrink_lower_m8_wp (Γ : Env)
    (hMm : Γ.Has "full_min_mark" Spec.fullMinMarkSpec)
    (hDfs : Γ.Has "full_min_lit_dfs_m8" Spec.fullMinLitDfsSpec) :
    ∀ args m Q X, Spec.fullShrinkLowerSpec args m Q X →
      Func.wp Γ full_shrink_lower_m8_body args m Q X := by
  rintro ⟨h, ot, ov, ⟨⟩⟩ m Q X hsp
  obtain ⟨c, F0, s, keepSet, R, rfl, hcore, hmin, hov, hot, hval, hlvl, hno8, hm, hQ⟩ :=
    Spec.fullShrinkLowerSpec_elim hsp
  have hlen0 := hcore.1.core_ok
  have hcv := hlen0.cur_vars_le
  have hov_lt : ov.toNat < s.core.cur_vars := by omega
  have hov_mrk : (ov.setWidth 64).toNat < s.core.mrk.length := by
    rw [hlen0.mrk_len, bv_c0_zext32_64]; omega
  have hno8_ov : (s.core.mrk[ov.toNat]?.getD 0#8 &&& 8#8) = 0#8 :=
    hno8 ov.toNat hov_lt (Nat.le_refl _)
  unfold Func.wp full_shrink_lower_m8_body; dsimp only [full_shrink_lower_m8_body]
  ml_ld load_full_mark_ptr hm
  ml_ld c0_load_full_mrk (i := ov.setWidth 64) hov_mrk hm
  ml_lets; ml_jnz; refine ⟨fun h2 => ?_, fun hn2 => ?_⟩
  · have h2_nz : (s.core.mrk[ov.toNat]?.getD 0#8 &&& 2#8) ≠ 0#8 := by
      have hb := bv8_c0_bit_ne0 h2
      rw [List.getElem?_eq_getElem (by rw [hlen0.mrk_len]; omega), Option.getD_some]
      simpa only [bv_c0_zext32_64, show BitVec.setWidth 8 (2 : BitVec 32) = 2#8 from rfl] using hb
    ml_lets; rw [wp]
    exact hQ true s.core.mrk s.scratch.wsort s.core.min_clr s.core.min_clr_len
      s.core.min_clr_full s.scratch.search_ticks m hcore.1 (fun _ _ => rfl) (fun _ _ h => h)
      (fun _ _ => rfl) hmin (fun _ => h2_nz) hm
  · let FailPost : Tup Val [] → Mem 64 → Prop := fun () m_d =>
      ∃ mrk_d wsort_d mclr_d mcl_d mcf_d ticks_d,
        let st_d := Spec.m8MinLitDfsState s mrk_d wsort_d mclr_d mcl_d mcf_d ticks_d
        st_d.LengthsOk c ∧
        (∀ v, s.core.cur_vars ≤ v → mrk_d[v]? = s.core.mrk[v]?) ∧
        (∀ v < s.core.cur_vars,
          (s.core.mrk[v]?.getD 0#8 &&& 2#8) ≠ 0#8 → (mrk_d[v]?.getD 0#8 &&& 2#8) ≠ 0#8) ∧
        (∀ v < s.core.cur_vars,
          (mrk_d[v]?.getD 0#8 &&& 8#8) = (s.core.mrk[v]?.getD 0#8 &&& 8#8)) ∧
        FullMinMarkInv st_d.core keepSet ∧
        (FullMem c st_d ⋆ R) m_d
    refine wp_join_group (ts := []) FailPost ?_ ?_
    · rintro _ ⟨⟩ m_d ⟨mrk_d, wsort_d, mclr_d, mcl_d, mcf_d, ticks_d,
          hlen_d, hab_d, hmono_d, hbit8_d, hmin_d, hm_d⟩
      rw [Blocks.get_here]
      let st_d := Spec.m8MinLitDfsState s mrk_d wsort_d mclr_d mcl_d mcf_d ticks_d
      have hsc_d : FullOtfsCoreInv c F0 st_d :=
        m8FullOtfsCoreInv_with_state hcore hlen_d.core_ok.mrk_len hlen_d.scratch_ok.wsort_len
          hlen_d.core_ok.min_clr_len_arr hlen_d.core_ok.min_clr_len_le
      have hno8_d : (st_d.core.mrk[ov.toNat]?.getD 0#8 &&& 8#8) = 0#8 := by
        dsimp only [st_d, Spec.m8MinLitDfsState]
        rw [hbit8_d ov.toNat hov_lt]; exact hno8_ov
      ml_lets; apply wp_call_of_spec; apply hMm
      refine fullMinMarkSpec_step hlen_d hm_d ov hov_lt 4#8 fun m_f hm_f => ?_
      have hstep := m8MinLit_state_step (s := s) (mrk1 := mrk_d) (wsort1 := wsort_d)
        (mclr1 := mclr_d) (mcl1 := mcl_d) (mcf1 := mcf_d) (ticks1 := ticks_d) ov.toNat 4#8
      let st_f := fullMinMarkStepState st_d ov.toNat 4#8
      have hm_f' : (FullMem c (Spec.m8MinLitDfsState s st_f.core.mrk wsort_d st_f.core.min_clr
          st_f.core.min_clr_len st_f.core.min_clr_full ticks_d) ⋆ R) m_f := by
        rw [← hstep]; exact hm_f
      have hlen_f : (Spec.m8MinLitDfsState s st_f.core.mrk wsort_d st_f.core.min_clr
          st_f.core.min_clr_len st_f.core.min_clr_full ticks_d).LengthsOk c := by
        rw [← hstep]; exact fullMinMarkStepState_lengths hlen_d ov.toNat 4#8
      have hab_f : ∀ v, s.core.cur_vars ≤ v → st_f.core.mrk[v]? = s.core.mrk[v]? :=
        fun v hv =>
          (fullMinMarkStepState_mrk_above (s := st_d) hov_lt 4#8 v hv).trans (hab_d v hv)
      have hbm_f := fullMinMarkStepState_bit8_mono2 hlen_d hov_lt (Or.inr rfl) hno8_d
      have hmin_f : FullMinMarkInv (Spec.m8MinLitDfsState s st_f.core.mrk wsort_d st_f.core.min_clr
          st_f.core.min_clr_len st_f.core.min_clr_full ticks_d).core keepSet := by
        rw [← hstep]; exact fullMinMarkInv_step_poison hsc_d hmin_d hov_lt hno8_d
      ml_lets; rw [wp]
      exact hQ false st_f.core.mrk wsort_d st_f.core.min_clr st_f.core.min_clr_len
        st_f.core.min_clr_full ticks_d m_f hlen_f hab_f
        (fun w hw h2w => hbm_f.2 w hw (hmono_d w hw h2w))
        (fun w hw => (hbm_f.1 w hw).trans (hbit8_d w hw))
        hmin_f (fun hc => by cases hc) hm_f'
    · rintro Jfail hJfail
      ml_ld c0_load_full_mrk (i := ov.setWidth 64) hov_mrk hm
      ml_lets; ml_jnz; refine ⟨fun _ => ?_, fun _ => ?_⟩
      · exact hJfail () m ⟨s.core.mrk, s.scratch.wsort, s.core.min_clr, s.core.min_clr_len,
          s.core.min_clr_full, s.scratch.search_ticks, hcore.1, (fun _ _ => rfl),
          (fun _ _ h => h), (fun _ _ => rfl), hmin, hm⟩
      · ml_lets; apply wp_call_of_spec; apply hDfs
        refine Spec.fullMinLitDfsSpec_of hcore hmin hot hval
          (by simpa only [Arg.val, hov] using hlvl)
          (fun v hv hlv => hno8 v hv (by simpa only [Arg.val, hov] using hlv)) hm ?_
        intro ok_d mrk_d wsort_d mclr_d mcl_d mcf_d ticks_d m_d st_d
          hlen_d hab_d hmono_d hbit8_d hmin_d hok_d hm_d
        ml_jnz; refine ⟨fun hok_t => ?_, fun hok_f => ?_⟩
        · have hok_true : ok_d = true := by
            cases ok_d with | true => rfl | false => cases hok_t
          let st_d := Spec.m8MinLitDfsState s mrk_d wsort_d mclr_d mcl_d mcf_d ticks_d
          have hno8_d : (st_d.core.mrk[ov.toNat]?.getD 0#8 &&& 8#8) = 0#8 := by
            dsimp only [st_d, Spec.m8MinLitDfsState]
            rw [hbit8_d ov.toNat hov_lt]; exact hno8_ov
          ml_lets; apply wp_call_of_spec; apply hMm
          refine fullMinMarkSpec_step hlen_d hm_d ov hov_lt 2#8 fun m_f hm_f => ?_
          have hstep := m8MinLit_state_step (s := s) (mrk1 := mrk_d) (wsort1 := wsort_d)
            (mclr1 := mclr_d) (mcl1 := mcl_d) (mcf1 := mcf_d) (ticks1 := ticks_d) ov.toNat 2#8
          let st_f := fullMinMarkStepState st_d ov.toNat 2#8
          have hm_f' : (FullMem c (Spec.m8MinLitDfsState s st_f.core.mrk wsort_d st_f.core.min_clr
              st_f.core.min_clr_len st_f.core.min_clr_full ticks_d) ⋆ R) m_f := by
            rw [← hstep]; exact hm_f
          have hlen_f : (Spec.m8MinLitDfsState s st_f.core.mrk wsort_d st_f.core.min_clr
              st_f.core.min_clr_len st_f.core.min_clr_full ticks_d).LengthsOk c := by
            rw [← hstep]; exact fullMinMarkStepState_lengths hlen_d ov.toNat 2#8
          have hab_f : ∀ v, s.core.cur_vars ≤ v → st_f.core.mrk[v]? = s.core.mrk[v]? :=
            fun v hv =>
              (fullMinMarkStepState_mrk_above (s := st_d) hov_lt 2#8 v hv).trans (hab_d v hv)
          have hbm_f := fullMinMarkStepState_bit8_mono2 hlen_d hov_lt (Or.inl rfl) hno8_d
          have hmin_f : FullMinMarkInv
              (Spec.m8MinLitDfsState s st_f.core.mrk wsort_d st_f.core.min_clr
              st_f.core.min_clr_len st_f.core.min_clr_full ticks_d).core keepSet := by
            rw [← hstep]
            dsimp only [st_f, fullMinMarkStepState, fullMinMarkStepCore]
            split
            · exact hmin_d
            · dsimp only [Arg.val] at hok_d
              rw [← hov] at hok_d
              exact (hok_d hok_true).2
          have h2_ov : (st_f.core.mrk[ov.toNat]?.getD 0#8 &&& 2#8) ≠ 0#8 := by
            dsimp only [st_f, fullMinMarkStepState, fullMinMarkStepCore]
            split
            · rename_i hc
              exact hc.resolve_left (Nat.not_le.mpr hov_lt)
            · dsimp only [fullMinMarkCore]
              rw [List.getElem?_set_self (by rw [hlen_d.core_ok.mrk_len]; omega), Option.getD_some]
              exact bv8_and2_of_or2 _
          ml_lets; rw [wp]
          exact hQ true st_f.core.mrk wsort_d st_f.core.min_clr st_f.core.min_clr_len
            st_f.core.min_clr_full ticks_d m_f hlen_f hab_f
            (fun w hw h2w => hbm_f.2 w hw (hmono_d w hw h2w))
            (fun w hw => (hbm_f.1 w hw).trans (hbit8_d w hw))
            hmin_f (fun _ => h2_ov) hm_f'
        · exact hJfail () m_d ⟨mrk_d, wsort_d, mclr_d, mcl_d, mcf_d, ticks_d,
            hlen_d, hab_d, hmono_d, hbit8_d, hmin_d, hm_d⟩

end

end LeanQbe.T.Examples.Kissat.Proof.Minimize
