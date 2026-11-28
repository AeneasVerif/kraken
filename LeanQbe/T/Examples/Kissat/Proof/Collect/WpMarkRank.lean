/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Src.Collect
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts1
public import LeanQbe.T.Examples.Kissat.Proof.Collect.Spec
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts
import LeanQbe.T.Examples.Kissat.Proof.Spec.MemBridges
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
import LeanQbe.T.Examples.Kissat.Proof.Spec.WitnessInv
import LeanQbe.T.Examples.Kissat.Proof.Collect.Tactics
import LeanQbe.T.Examples.Kissat.Proof.Collect.HelpersWatch
import LeanQbe.T.Examples.Kissat.Proof.Collect.HelpersArena
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.ControlComb
meta import LeanQbe.T.Logic.C0Step
meta import LeanQbe.T.Logic.C0HeadStep

/-!
# Reason Marking & Literal Rank WP Proofs (`Proof.Collect.WpMarkRank`)

Canonical `Func.wp` proofs for `full_mark_reasons_m6`, `full_mark_reasons`, and
`full_lit_rank_m6` from `Src.Collect`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Collect

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Collect
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Spec.FullKissatMath
open LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open LeanQbe.T.Examples.Kissat.Proof.Collect.Spec
open Kraken.Bedrock2.Test
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Proof.Collect.M6Tactics1

public section

private theorem collect_fwd0 {Q : Post []} : (fun (_ : Tup Val []) m' => Q () m') = Q :=
  funext fun r => by cases r; rfl

theorem full_lit_rank_m6_wp (Γ : Env) :
    ∀ a m Q X, fullLitRankSpec a m Q X → Func.wp Γ full_lit_rank_m6_body a m Q X := by
  rintro ⟨vals_ptr, lvl_ptr, l, ⟨⟩⟩ m Q X ⟨vals, lvl, R, hl_v, hl_l, hm, hQ⟩
  have hsh : (l >>> 1#32).toNat = l.toNat / 2 := bv32_shr1_toNat l
  have hsh_l : (l >>> 1#32).toNat < lvl.length := by rw [hsh]; exact hl_l
  m6_steps <;> exact hQ _

theorem full_mark_reasons_m6_wp (Γ : Env) :
    ∀ a m Q X, fullMarkReasonsSpec a m Q X → Func.wp Γ full_mark_reasons_m6_body a m Q X := by
  rintro ⟨h, set_flag, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hm, hQ⟩
  have hte_le := hlen.core_ok.trail_end_le
  have hcv_le := hlen.core_ok.cur_vars_le
  have hmax_lt : c.max_vars < 2 * dimacsBound := c.hmaxv
  have hcap_lt : c.arena_cap < 2 * dimacsBound := c.harena
  unfold dimacsBound at hmax_lt hcap_lt
  have hal_le := hlen.core_ok.arena_len_le
  have htrl_len := hlen.core_ok.trl_len
  have hlvl_len := hlen.core_ok.lvl_len
  have hrsns_len := hlen.core_ok.rsns_len
  have hft_len := hlen.core_ok.frame_trail_len
  m6_to_jnz
  refine wp_jnz_of (fun hc => ?_) (fun hc => ?_)
  · have hcl0 : s.core.cur_level = 0 := by
      rw [Arg.val_var, beq_iff_eq] at hc
      have h0 := congrArg BitVec.toNat hc
      have hcl_lt : s.core.cur_level < 2 ^ 64 := by have := hw.cur_level_le; omega
      simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcl_lt] using h0
    fr_steps
    refine hQ s.core.arena m hlen rfl (fun _ _ => ⟨rfl, rfl, rfl⟩) (fun _ idx hidx => ?_) hw hm
    dsimp only; intro hl_pos _
    exact absurd hl_pos (by
      change ¬ 0 < (s.core.lvl[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
      exact Nat.not_lt_of_le (hcl0 ▸ hw.lvl_le idx hidx))
  · have hcl_pos : 0 < s.core.cur_level := by
      rw [Arg.val_var, beq_eq_false_iff_ne] at hc
      rcases Nat.eq_zero_or_pos s.core.cur_level with h0 | hpos
      · exact absurd (by simp [h0]) hc
      · exact hpos
    have hft1_lt : 1 < s.core.frame_trail.length := by
      have := hw.cur_level_le; rw [hft_len]; omega
    have hft1_le_te : (s.core.frame_trail[1]?.getD 0#32).toNat ≤ s.core.trail_end :=
      hw.frame_trail_lt 1 (by omega)
    have hpre_lv0 : ∀ idx < (s.core.frame_trail[1]?.getD 0#32).toNat,
        0 < (s.core.lvl[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat → False :=
      fun idx hidx hl => by
        have := hw.frame_trail_before_lt 1 (by omega) hcl_pos idx hidx; omega
    m6_steps
    refine wp_load_of (by
      simpa [Arg.val_var] using FullArenaTactics.load_full_frame_trail (i := 1) hft1_lt hm) ?_
    m6_steps
    refine wp_loop_inv (ts := [i64])
      (fun (i, ()) mL =>
        i.toNat ≤ s.core.trail_end ∧
        ∃ arL : List (BitVec 32), arL.length = c.arena_cap ∧
          let sL : FullState := { s with core := { s.core with arena := arL } }
          FullWitnessInv c F0 F_cur sL.core ∧
          fullArenaClauseRefs sL = fullArenaClauseRefs s ∧
          (∀ r ∈ fullArenaClauseRefs s,
            fullArenaClauseSize sL r = fullArenaClauseSize s r ∧
            fullArenaClauseGarb sL r = fullArenaClauseGarb s r ∧
            fullArenaClauseLits sL r = fullArenaClauseLits s r) ∧
          (set_flag = true → ∀ idx < i.toNat,
            let v := (s.core.trl[idx]?.getD 0#32).toNat / 2
            let rsn := s.core.rsns[v]?.getD 0xFFFFFFFF#32
            0 < (s.core.lvl[v]?.getD 0#32).toNat →
            (rsn &&& 0x80000000#32) = 0#32 →
            (fullArenaHdr sL rsn.toNat &&& 0x00200000#32) ≠ 0#32) ∧
          (FullMem c sL ⋆ R) mL)
      (fun (i, ()) _ => s.core.trail_end - i.toNat) (fun J hLoop => ?_) ?_
    · refine hLoop ((s.core.frame_trail[1]'hft1_lt).setWidth 64, ()) m ?_
      have hstart_eq : ((s.core.frame_trail[1]'hft1_lt).setWidth 64).toNat =
          (s.core.frame_trail[1]?.getD 0#32).toNat := by
        rw [List.getElem?_eq_getElem hft1_lt, Option.getD_some,
          bv32_zext64_toNat]
      dsimp only; rw [hstart_eq]
      exact ⟨hft1_le_te, s.core.arena, hlen.core_ok.arena_len_arr, hw, rfl,
        fun _ _ => ⟨rfl, rfl, rfl⟩, fun _ idx hidx hl => absurd hl (hpre_lv0 idx hidx), hm⟩
    · rintro J ⟨i, ⟨⟩⟩ mL ⟨hi_le, arL, harL, hwL, hrefsL, hclL, hmkL, hmL⟩ hLoop
      let sL : FullState := { s with core := { s.core with arena := arL } }
      have hlenL : sL.LengthsOk c := ⟨{ hlen.core_ok with arena_len_arr := harL }, hlen.scratch_ok⟩
      have hdone : i.toNat = s.core.trail_end → Q () mL := fun heq =>
        hQ arL mL hlenL hrefsL hclL (fun hsf idx hidx => hmkL hsf idx (heq ▸ hidx)) hwL hmL
      m6_split
      · have hi_lt : i.toNat < s.core.trail_end := by c0_bound
        have hi_trl : i.toNat < sL.core.trl.length := by dsimp [sL]; rw [htrl_len]; omega
        have hlit_lt : (s.core.trl[i.toNat]'(by omega)).toNat < 2 * s.core.cur_vars := by
          have := hw.trail_lits_lt i.toNat hi_lt
          rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at this
        have hv_lt : (s.core.trl[i.toNat]'(by omega)).toNat / 2 < s.core.cur_vars := by omega
        have hv_lvl : (s.core.trl[i.toNat]'(by omega)).toNat / 2 < s.core.lvl.length := by omega
        have hv_rsn : (s.core.trl[i.toNat]'(by omega)).toNat / 2 < s.core.rsns.length := by omega
        have hi_next : (i + 1#64).toNat = i.toNat + 1 := bv64_add1_lt (by omega)
        let vNat : Nat := (s.core.trl[i.toNat]'(by omega)).toNat / 2
        let r32 : BitVec 32 := s.core.rsns[vNat]'hv_rsn
        have hr32_eq : s.core.rsns[(s.core.trl[i.toNat]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32
            = r32 := by
          simp [List.getElem?_eq_getElem (by omega : i.toNat < s.core.trl.length),
            List.getElem?_eq_getElem hv_rsn, r32, vNat]
        m6_to_group
        refine wp_join_group (fun () mJ =>
          ∃ ar' : List (BitVec 32), ar'.length = c.arena_cap ∧
            let s' : FullState := { s with core := { s.core with arena := ar' } }
            FullWitnessInv c F0 F_cur s'.core ∧
            fullArenaClauseRefs s' = fullArenaClauseRefs s ∧
            (∀ r ∈ fullArenaClauseRefs s,
              fullArenaClauseSize s' r = fullArenaClauseSize s r ∧
              fullArenaClauseGarb s' r = fullArenaClauseGarb s r ∧
              fullArenaClauseLits s' r = fullArenaClauseLits s r) ∧
            (set_flag = true → ∀ idx < i.toNat + 1,
              let v := (s.core.trl[idx]?.getD 0#32).toNat / 2
              let rsn := s.core.rsns[v]?.getD 0xFFFFFFFF#32
              0 < (s.core.lvl[v]?.getD 0#32).toNat →
              (rsn &&& 0x80000000#32) = 0#32 →
              (fullArenaHdr s' rsn.toNat &&& 0x00200000#32) ≠ 0#32) ∧
            (FullMem c s' ⋆ R) mJ) ?_ ?_
        · rintro _ ⟨⟩ mJ ⟨ar', har', hw', hrefs', hcl', hmk', hmJ⟩
          fr_steps
          exact hLoop (i + 1#64, ()) mJ (by dsimp only; rw [hi_next]; omega)
            ⟨by rw [hi_next]; omega, ar', har', hw', hrefs', hcl',
             by simpa [hi_next] using hmk', hmJ⟩
        · intro Jj hJj
          have hmem_of_lt : r32.toNat < 0x80000000 →
              r32.toNat ∈ fullArenaClauseRefsCore sL.core := by
            intro hr_lt
            have hr_ne : r32 ≠ 0xFFFFFFFF#32 := fun h => by
              have := congrArg BitVec.toNat h; simp at this; omega
            have hr_lg : (r32 &&& 0x80000000#32) = 0#32 := (bv32_lt_highbit_iff r32).mp hr_lt
            have hri := hwL.reason_inv i.toNat hi_lt (by simpa [sL, hr32_eq] using hr_ne)
            have h1 : sL.core.rsns[(sL.core.trl[i.toNat]?.getD 0#32).toNat / 2]?.getD
                0xFFFFFFFF#32 = r32 := hr32_eq
            rw [h1, ite_eq_right (fun h => h hr_lg)] at hri; exact hri.1
          fr_steps
          · rename_i hv_lt_cv hlvl_pos hr_lt8 hr_le3
            have hr_lt : r32.toNat < 0x80000000 := by
              change (s.core.rsns[vNat]'hv_rsn).toNat < 0x80000000
              simpa [vNat, show (2147483648 : BitVec 32).toNat = 0x80000000 from rfl] using hr_lt8
            have hmem := hmem_of_lt hr_lt
            have hr_al : r32.toNat < arL.length := by
              have := (hwL.arena.refs_wf _ hmem).1; dsimp [sL] at this; omega
            have hbits := bv32_bit21_or_pres (arL[r32.toNat]'hr_al)
            have hhdr_eq : fullArenaHdrCore sL.core r32.toNat = arL[r32.toNat]'hr_al := by
              unfold fullArenaHdrCore; dsimp [sL]
              rw [List.getElem?_eq_getElem hr_al, Option.getD_some]
            obtain ⟨hrefs', hcl', hw'⟩ :=
              setHdrKeepGarbShrk_preserves_witness hlenL.core_ok hwL hmem
              (v := (arL[r32.toNat]'hr_al) ||| 0x00200000#32)
              (by rw [hhdr_eq]; exact hbits.1) (by rw [hhdr_eq]; exact hbits.2.1)
            refine hJj () _ ⟨arL.set r32.toNat ((arL[r32.toNat]'hr_al) ||| 0x00200000#32),
              by simp [harL], hw', hrefs'.trans hrefsL, fun r hr => ?_, fun _ idx hidx => ?_, hm⟩
            · have hrL : r ∈ fullArenaClauseRefsCore sL.core := by
                change r ∈ fullArenaClauseRefs sL; rw [hrefsL]; exact hr
              have h1 := hcl' r hrL; have h2 := hclL r hr
              exact ⟨h1.1.trans h2.1, h1.2.1.trans h2.2.1, h1.2.2.trans h2.2.2⟩
            · dsimp only; intro hlpos hrlg
              by_cases hidx_eq : idx = i.toNat
              · subst hidx_eq; rw [hr32_eq]
                unfold fullArenaHdr fullArenaHdrCore; dsimp only
                rw [List.getElem?_set_self hr_al, Option.getD_some]; exact hbits.2.2
              · have hprev := hmkL hc idx (by omega) hlpos hrlg
                let rsn_i :=
                  s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32
                by_cases hre : rsn_i.toNat = r32.toNat
                · unfold fullArenaHdr fullArenaHdrCore; dsimp only
                  rw [show (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
                      0xFFFFFFFF#32).toNat = r32.toNat from hre,
                    List.getElem?_set_self hr_al, Option.getD_some]
                  exact hbits.2.2
                · unfold fullArenaHdr fullArenaHdrCore at hprev ⊢; dsimp only at hprev ⊢
                  rw [List.getElem?_set_ne (Ne.symm hre)]; exact hprev
          · rename_i hv_lt_cv hlvl_pos hr_lt8 hr_le3
            have hr_lt : r32.toNat < 0x80000000 := by
              change (s.core.rsns[vNat]'hv_rsn).toNat < 0x80000000
              simpa [vNat, show (2147483648 : BitVec 32).toNat = 0x80000000 from rfl] using hr_lt8
            have hmem := hmem_of_lt hr_lt
            have hr_al : r32.toNat < arL.length := by
              have := (hwL.arena.refs_wf _ hmem).1; dsimp [sL] at this; omega
            have hbits := bv32_bit21_clear_pres (arL[r32.toNat]'hr_al)
            have hhdr_eq : fullArenaHdrCore sL.core r32.toNat = arL[r32.toNat]'hr_al := by
              unfold fullArenaHdrCore; dsimp [sL]
              rw [List.getElem?_eq_getElem hr_al, Option.getD_some]
            obtain ⟨hrefs', hcl', hw'⟩ :=
              setHdrKeepGarbShrk_preserves_witness hlenL.core_ok hwL hmem
              (v := (arL[r32.toNat]'hr_al) &&& ~~~0x00200000#32)
              (by rw [hhdr_eq]; exact hbits.1) (by rw [hhdr_eq]; exact hbits.2)
            refine hJj () _ ⟨arL.set r32.toNat ((arL[r32.toNat]'hr_al) &&& ~~~0x00200000#32),
              by simp [harL], hw', hrefs'.trans hrefsL, fun r hr => ?_,
              fun h => by simp [h] at hc, hm⟩
            have hrL : r ∈ fullArenaClauseRefsCore sL.core := by
              change r ∈ fullArenaClauseRefs sL; rw [hrefsL]; exact hr
            have h1 := hcl' r hrL; have h2 := hclL r hr
            exact ⟨h1.1.trans h2.1, h1.2.1.trans h2.2.1, h1.2.2.trans h2.2.2⟩
          · rename_i hv_lt_cv hlvl_pos hr_lt8
            have hr_lt : r32.toNat < 0x80000000 := by
              change (s.core.rsns[vNat]'hv_rsn).toNat < 0x80000000
              simpa [vNat, show (2147483648 : BitVec 32).toNat = 0x80000000 from rfl] using hr_lt8
            have hmem := hmem_of_lt hr_lt
            have hwf3 := (hwL.arena.refs_wf _ hmem).1; dsimp [sL] at hwf3
            have hnot3 : ¬ (r32.toNat + 3) % 2 ^ 64 ≤ s.core.arena_len % 2 ^ 64 := by
              simpa [r32, vNat, show (3 : BitVec 64).toNat = 3 from rfl] using hc
            omega
          · rename_i hv_lt_cv hlvl_pos
            refine hJj () mL ⟨arL, harL, hwL, hrefsL, hclL, fun hsf idx hidx => ?_, hmL⟩
            by_cases hidx_eq : idx = i.toNat
            · subst hidx_eq; dsimp only; intro _ hrlg; rw [hr32_eq] at hrlg
              have hlt := (bv32_lt_highbit_iff r32).mpr hrlg
              have hge : ¬ r32.toNat < 0x80000000 := by
                simpa [r32, vNat, show (2147483648 : BitVec 32).toNat = 0x80000000 from rfl]
                  using hc
              exact False.elim (hge hlt)
            · exact hmkL hsf idx (by omega)
          · rename_i hv_lt_cv
            refine hJj () mL ⟨arL, harL, hwL, hrefsL, hclL, fun hsf idx hidx => ?_, hmL⟩
            by_cases hidx_eq : idx = i.toNat
            · subst hidx_eq; dsimp only; intro hlpos _
              have h1 : (s.core.lvl[(s.core.trl[i.toNat]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
                  = (s.core.lvl[vNat]'hv_lvl).toNat := by
                simp [List.getElem?_eq_getElem (by omega : i.toNat < s.core.trl.length),
                  List.getElem?_eq_getElem hv_lvl, vNat]
              have hnot : ¬ (0 < (s.core.lvl[vNat]'hv_lvl).toNat) := by
                simpa [vNat, show (0 : BitVec 32).toNat = 0 from rfl] using hc
              rw [h1] at hlpos; exact False.elim (hnot hlpos)
            · exact hmkL hsf idx (by omega)
      · fr_steps; exact hdone (by c0_bound)

theorem full_mark_reasons_wp (Γ : Env)
    (hSub : ∀ a m Q X, fullMarkReasonsSpec a m Q X →
      Γ "full_mark_reasons_m6" [i64, .bool] [] a m Q X) :
    ∀ a m Q X, fullMarkReasonsSpec a m Q X → Func.wp Γ full_mark_reasons_body a m Q X := by
  intro ⟨_, _, ⟨⟩⟩ _ _ _ hs; unfold Func.wp full_mark_reasons_body
  c0_hsteps; c0_call hSub; rwa [collect_fwd0]

end

end LeanQbe.T.Examples.Kissat.Proof.Collect
