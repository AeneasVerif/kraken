module

public import LeanQbe.T.Examples.Kissat.FullM4VivBceProof1

/-!
# Kissat M4f BCE `Func.wp` Proofs, Closed `ModuleOk`, & Concrete `Mem 64` UNSAT Non-Vacuity

Completes the standalone Kissat M4f verification suite (`FullM4VivBce.lean`, `FullM4VivBceProof0`,
`FullM4VivBceProof1`, `FullM4VivBceProof`, `0` edits to existing files, `0` custom axioms,
`XPost := False`, `0` SAT model proofs):

1. **Dual-polarity Blocked Clause Elimination (`l` and `nl`)**:
   - `full_bce_side_m4_wp`, `full_bce_pair_m4_wp`, `full_bce_var_m4_wp`, `full_bce_m4_wp`
     (preserves `FullSparseInv`, `cur_level = 0`, UNSAT-sound `20#64 → F0.Unsat`).
2. **Closed `31`-row `m4VivBceSpecTable`**, `m4VivBceEnv`, and
   `m4VivBce_moduleOk : ModuleOk m4VivBceEnv m4VivBceModule` covering all `16` M4f functions
   (with `full_vivify_m4` certified to canonical `FullFastBveBudgets.fullVivifyFastSpec`).
3. **Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`)** for all `16` M4f functions on a
   concrete `2588`-byte heap (`nvM4SparseMem` / `nvM4DenseMem`) with UNSAT formula `{(x0), (¬x0)}`
   and live 3-literal arena clause `[x0, x1, x2]`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM4VivBce

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open Kraken.Bedrock2.Test

/-! ## 1. Dual-polarity BCE M4f `Func.wp` proofs (`4` functions) -/

section BceM4Proofs

open FullBveVarTactics FullBveVarHelpers FullVivTopTactics
open scoped FullArenaTactics FullBveVarTactics FullVivTopTactics

theorem full_bce_side_m4_wp (Γ : Env)
    (hTryBce : ∀ a m Q X, Full.fullBveTryBceSpec a m Q X →
      Γ "full_bve_try_bce" [i64, i32, i32, i32, i32] [.bool] a m Q X)
    (hExtPush2 : ∀ a m Q X, Full.fullExtendPush2Spec a m Q X →
      Γ "full_extend_push2" [i64, i32, i32] [.bool] a m Q X)
    (hExtPushCl : ∀ a m Q X, Full.fullExtendPushClSpec a m Q X →
      Γ "full_extend_push_cl" [i64, i32, i32] [.bool] a m Q X)
    (hDelBin : ∀ a m Q X, Full.fullDeleteBinarySpec a m Q X →
      Γ "full_delete_binary" [i64, i32, i32] [] a m Q X) :
    ∀ a m Q X, fullBceSideM4Spec a m Q X → Func.wp Γ full_bce_side_m4_body a m Q X := by
  rintro ⟨h, blk_lit, cand_off, cand_n, opp_off, opp_n, ⟨⟩⟩ m0 Q X
    ⟨c, F0, F_cur, s, R, rfl, hinv0, hblk_lt, hc_cap, ho_cap, hdisj, hcand0, hopp0, hm0, hQ⟩
  have hsc := c.hscr; have harc := c.harena; unfold dimacsBound at hsc harc
  unfold Func.wp full_bce_side_m4_body
  fvt_steps
  refine wp_loop_inv (ts := [i32, i32])
    (fun (i, rem, ()) ml => ∃ sl : FullState,
      FullDenseInvW c F0 F_cur sl ∧ sl.core.cur_vars = s.core.cur_vars ∧
      sl.core.fuel = s.core.fuel ∧ rem.toNat ≤ i.toNat ∧ i.toNat ≤ cand_n.toNat ∧
      (∀ k < rem.toNat,
        FullBceCandOk c sl (sl.scratch.scratch_buf[cand_off.toNat + k]?.getD 0#32)) ∧
      (∀ k, i.toNat ≤ k → k < cand_n.toNat →
        sl.scratch.scratch_buf[cand_off.toNat + k]? =
          s.scratch.scratch_buf[cand_off.toNat + k]?) ∧
      (∀ j < opp_n.toNat,
        sl.scratch.scratch_buf[opp_off.toNat + j]? =
          s.scratch.scratch_buf[opp_off.toNat + j]?) ∧
      (∀ w, FullBceCandOk c s w → FullBceCandOk c sl w) ∧
      (∀ w, FullBveBceWeakOk c s w → FullBveBceWeakOk c sl w) ∧
      (FullMem c sl ⋆ R) ml)
    (fun (i, _, _) _ => cand_n.toNat - i.toNat) ?_ ?_
  · intro J hJ; fvt_steps
    exact hJ (0#32, 0#32, ()) m0 ⟨s, hinv0, rfl, rfl, Nat.le_refl _, Nat.zero_le _,
      fun _ hk => by simp at hk, fun _ _ _ => rfl, fun _ _ => rfl, fun _ hw => hw,
      fun _ hw => hw, hm0⟩
  · intro J ⟨i, rem, ⟨⟩⟩ ml ⟨sl, hinvl, hcvl, hfll, hrem_le, hi_le, hrem_ok, htail_eq,
      hopp_eq, hmono_c, hmono_w, hml⟩ ih
    fvt_steps
    · have hi_lt : i.toNat < cand_n.toNat := by c0_bound
      have hscrl := hinvl.1.scratch_ok.scratch_buf_len
      have hci_nat : (cand_off.setWidth 64 + i.setWidth 64).toNat =
          cand_off.toNat + i.toNat := by bv_omega
      have hci_lt : (cand_off.setWidth 64 + i.setWidth 64).toNat <
          sl.scratch.scratch_buf.length := by omega
      let w := sl.scratch.scratch_buf[(cand_off.setWidth 64 + i.setWidth 64).toNat]'hci_lt
      have hw_eq : w = s.scratch.scratch_buf[cand_off.toNat + i.toNat]?.getD 0#32 := by
        have h1 := htail_eq i.toNat (Nat.le_refl _) hi_lt
        rw [List.getElem?_eq_getElem (by omega : cand_off.toNat + i.toNat <
          sl.scratch.scratch_buf.length)] at h1
        rw [← h1, Option.getD_some]
        exact Option.some.inj (by
          rw [← List.getElem?_eq_getElem hci_lt, hci_nat, List.getElem?_eq_getElem (by omega)])
      have hw_cand : FullBceCandOk c sl w := hmono_c w (hw_eq ▸ hcand0 i.toNat hi_lt)
      fvt_to_group
      -- Join `deleted : Bool` after `if (full_bve_try_bce(...))`
      refine wp_join_group (ts := [.bool])
        (fun (deleted, ()) md => ∃ sd : FullState,
          FullDenseInvW c F0 F_cur sd ∧ sd.core.cur_vars = s.core.cur_vars ∧
          sd.core.fuel = s.core.fuel ∧
          sd.scratch.scratch_buf = sl.scratch.scratch_buf ∧
          (∀ w', FullBceCandOk c sl w' → FullBceCandOk c sd w') ∧
          (∀ w', FullBveBceWeakOk c sl w' → FullBveBceWeakOk c sd w') ∧
          (FullMem c sd ⋆ R) md) ?_ ?_
      · -- After `deleted` join: compact if `!deleted`, advance `i + 1`
        rintro _ ⟨deleted, ⟨⟩⟩ md ⟨sd, hinvd, hcvd, hfld, hscrd, hstep_c, hstep_w, hmd⟩
        have hi1 : (i + 1#32).toNat = i.toNat + 1 := by bv_omega
        have hrem_ok_d : ∀ k < rem.toNat,
            FullBceCandOk c sd (sd.scratch.scratch_buf[cand_off.toNat + k]?.getD 0#32) := by
          intro k hk; rw [hscrd]; exact hstep_c _ (hrem_ok k hk)
        have htail_d : ∀ k, i.toNat + 1 ≤ k → k < cand_n.toNat →
            sd.scratch.scratch_buf[cand_off.toNat + k]? =
              s.scratch.scratch_buf[cand_off.toNat + k]? := fun k hk1 hk2 => by
          rw [hscrd]; exact htail_eq k (by omega) hk2
        have hopp_d : ∀ j < opp_n.toNat,
            sd.scratch.scratch_buf[opp_off.toNat + j]? =
              s.scratch.scratch_buf[opp_off.toNat + j]? := fun j hj => by
          rw [hscrd]; exact hopp_eq j hj
        have hmonod_c : ∀ w', FullBceCandOk c s w' → FullBceCandOk c sd w' :=
          fun w' hw => hstep_c w' (hmono_c w' hw)
        have hmonod_w : ∀ w', FullBveBceWeakOk c s w' → FullBveBceWeakOk c sd w' :=
          fun w' hw => hstep_w w' (hmono_w w' hw)
        fvt_steps
        · -- `deleted = true`: keep `rem` unchanged
          exact ih (i + 1#32, rem, ()) md (by dsimp only; omega)
            ⟨sd, hinvd, hcvd, hfld, by omega, by omega, hrem_ok_d,
              fun k hk1 hk2 => htail_d k (by omega) hk2, hopp_d, hmonod_c, hmonod_w, hmd⟩
        · -- `deleted = false` (`!deleted`): write `scr[cand_off + rem] = w; rem = rem + 1`
          have hcr_nat : (cand_off.setWidth 64 + rem.setWidth 64).toNat =
              cand_off.toNat + rem.toNat := by bv_omega
          have hcr_lt : (cand_off.setWidth 64 + rem.setWidth 64).toNat <
              sd.scratch.scratch_buf.length := by
            rw [hinvd.1.scratch_ok.scratch_buf_len]; omega
          have hrem1 : (rem + 1#32).toNat = rem.toNat + 1 := by bv_omega
          fvt_steps
          let scr' := sd.scratch.scratch_buf.set (cand_off.toNat + rem.toNat) w
          let sd' : FullState := { sd with scratch := { sd.scratch with scratch_buf := scr' } }
          have hinvd' : FullDenseInvW c F0 F_cur sd' :=
            FullBveVarHelpers.FullDenseInvW.with_scratch_buf hinvd
              (by simp [scr', hinvd.1.scratch_ok.scratch_buf_len])
          refine ih (i + 1#32, rem + 1#32, ()) _ (by dsimp only; omega)
            ⟨sd', hinvd', hcvd, hfld, by omega, by omega, fun k hk => ?_, fun k hk1 hk2 => ?_,
              fun j hj => ?_, fun w' hw => FullBceCandOk.with_same_arena rfl rfl (hmonod_c w' hw),
              fun w' hw => FullBveBceWeakOk.with_same_arena rfl rfl (hmonod_w w' hw),
              by simpa only [sd', scr', hcr_nat] using hm⟩
          · rw [hrem1] at hk
            rcases (by omega : k < rem.toNat ∨ k = rem.toNat) with hkr | rfl
            · have hne : cand_off.toNat + rem.toNat ≠ cand_off.toNat + k := by omega
              change FullBceCandOk c sd' (scr'[cand_off.toNat + k]?.getD 0#32)
              rw [show scr'[cand_off.toNat + k]? = sd.scratch.scratch_buf[cand_off.toNat + k]?
                from List.getElem?_set_ne hne]
              exact FullBceCandOk.with_same_arena rfl rfl (hrem_ok_d k hkr)
            · change FullBceCandOk c sd' (scr'[cand_off.toNat + rem.toNat]?.getD 0#32)
              rw [show scr'[cand_off.toNat + rem.toNat]? = some w from
                List.getElem?_set_self (by rw [hinvd.1.scratch_ok.scratch_buf_len]; omega),
                Option.getD_some]
              exact FullBceCandOk.with_same_arena rfl rfl (hstep_c w hw_cand)
          · have hne : cand_off.toNat + rem.toNat ≠ cand_off.toNat + k := by omega
            change scr'[cand_off.toNat + k]? = s.scratch.scratch_buf[cand_off.toNat + k]?
            rw [List.getElem?_set_ne hne]; exact htail_d k (by omega) hk2
          · have hne : cand_off.toNat + rem.toNat ≠ opp_off.toNat + j := by
              rcases hdisj with h1 | h2 <;> omega
            change scr'[opp_off.toNat + j]? = s.scratch.scratch_buf[opp_off.toNat + j]?
            rw [List.getElem?_set_ne hne]; exact hopp_d j hj
      · -- `if (full_bve_try_bce(h, blk_lit, w, opp_off, opp_n))` entry
        intro Jd hJd
        c0_call hTryBce
        refine ⟨c, F0, F_cur, sl, R, rfl, hinvl, by rw [hcvl]; exact hblk_lt,
          hw_cand.1, hw_cand.2, ho_cap,
          fun j hj => by rw [hopp_eq j hj]; exact hmono_w _ (hopp0 j hj), hml,
          fun blk lm' tmp' m_tb hinv_tb hm_tb => ?_⟩
        let stb : FullState := { sl with core := { sl.core with lit_mark := lm', tmp := tmp' } }
        have htb_c : ∀ w', FullBceCandOk c sl w' → FullBceCandOk c stb w' :=
          fun _ h => FullBceCandOk.with_same_arena rfl rfl h
        have htb_w : ∀ w', FullBveBceWeakOk c sl w' → FullBveBceWeakOk c stb w' :=
          fun _ h => FullBveBceWeakOk.with_same_arena rfl rfl h
        fvt_to_group
        · -- `blk = true`: binary vs arena branch
          fvt_steps
          · -- Binary branch `(w & PW_BIN_FLAG) != 0`
            c0_call hExtPush2
            refine ⟨c, stb, R, ⟨rfl, hinv_tb.2.2.2.2.1.2⟩, hinv_tb.1, hm_tb,
              fun ⟨okp, ⟨⟩⟩ se2 m_e2 hcore_e2 hlen_e2 ⟨hll_e2, hext_e2, hscr_e2⟩ hm_e2 => ?_⟩
            have heq_e2 : se2.core = stb.core := fullCoreState_agrees_with_scratch hcore_e2
            have hinv_e2 : FullDenseInvW c F0 F_cur se2 :=
              denseInvW_of_extPush hinv_tb hlen_e2 hcore_e2 hll_e2 hext_e2
            have he2_c : ∀ w', FullBceCandOk c sl w' → FullBceCandOk c se2 w' :=
              fun _ h => FullBceCandOk.with_same_arena (congrArg FullCoreState.arena heq_e2)
                (congrArg FullCoreState.arena_len heq_e2) (htb_c _ h)
            have he2_w : ∀ w', FullBveBceWeakOk c sl w' → FullBveBceWeakOk c se2 w' :=
              fun _ h => FullBveBceWeakOk.with_same_arena (congrArg FullCoreState.arena heq_e2)
                (congrArg FullCoreState.arena_len heq_e2) (htb_w _ h)
            fvt_steps
            · c0_call hDelBin
              refine ⟨c, se2, R, rfl, hinv_e2.1, hinv_e2.2.1.watches.layout, hm_e2,
                fun wvec' wstk' wu' nb' m_db hlen_db _ hwat_fn hm_db => ?_⟩
              let sdb : FullState :=
                { se2 with core := { se2.core with wvec := wvec', wstk := wstk',
                                                   wusable := wu', num_binary := nb' } }
              have hinv_db : FullDenseInvW c F0 F_cur sdb :=
                FullDenseInvW.of_deleteBinary hinv_e2 hlen_db (hwat_fn F_cur hinv_e2.2.1.watches)
              fvt_steps
              let sbce : FullState :=
                { sdb with scratch := { sdb.scratch with bce_cnt := sdb.scratch.bce_cnt + 1#64 } }
              exact hJd (true, ()) _ ⟨sbce, FullDenseInvW.with_bce_cnt hinv_db _,
                (congrArg FullCoreState.cur_vars heq_e2).trans hcvl,
                (congrArg FullCoreState.fuel heq_e2).trans hfll, hscr_e2,
                fun _ h => FullBceCandOk.with_same_arena rfl rfl (he2_c _ h),
                fun _ h => FullBveBceWeakOk.with_same_arena rfl rfl (he2_w _ h), by assumption⟩
            · exact hJd (false, ()) m_e2 ⟨se2, hinv_e2,
                (congrArg FullCoreState.cur_vars heq_e2).trans hcvl,
                (congrArg FullCoreState.fuel heq_e2).trans hfll,
                hscr_e2, he2_c, he2_w, hm_e2⟩
          · -- Arena clause branch `(w & PW_BIN_FLAG) == 0`
            have hnb_w : (w &&& 0x80000000#32) = 0#32 := by c0_bound
            have hw_cand_tb := htb_c w hw_cand
            have hw_weak_tb := hw_cand_tb.1
            unfold FullBveBceWeakOk at hw_weak_tb
            simp only [hnb_w, ne_eq, not_true_eq_false, ↓reduceIte] at hw_weak_tb
            have hw_nat : (w.setWidth 64).toNat = w.toNat := bv32_setWidth64_toNat w
            have hw_ar_lt : (w.setWidth 64).toNat < stb.core.arena.length := by
              have hlen_tb : stb.core.arena.length = c.arena_cap := hinv_tb.1.core_ok.arena_len_arr
              have hal_tb : stb.core.arena_len ≤ c.arena_cap := hinv_tb.1.core_ok.arena_len_le
              omega
            fvt_steps
            · -- Already `PH_GARB`: `deleted = true`
              exact hJd (true, ()) m_tb ⟨stb, hinv_tb, hcvl, hfll, rfl, htb_c, htb_w, hm_tb⟩
            · -- Not yet `PH_GARB`: `full_extend_push_cl` then mark `PH_GARB`
              c0_call hExtPushCl
              refine ⟨c, stb, R, ⟨rfl, hinv_tb.2.2.2.2.1.2⟩, hinv_tb.1, hm_tb,
                fun ⟨okp, ⟨⟩⟩ se2 m_e2 hcore_e2 hlen_e2 ⟨hll_e2, hext_e2, hscr_e2⟩ hm_e2 => ?_⟩
              have hm_e2' : (FullMem c se2 ⋆ R) m_e2 := hm_e2
              clear hm_e2
              have heq_e2 : se2.core = stb.core := fullCoreState_agrees_with_scratch hcore_e2
              have hinv_e2 : FullDenseInvW c F0 F_cur se2 :=
                denseInvW_of_extPush hinv_tb hlen_e2 hcore_e2 hll_e2 hext_e2
              have he2_c : ∀ w', FullBceCandOk c sl w' → FullBceCandOk c se2 w' :=
                fun _ h => FullBceCandOk.with_same_arena (congrArg FullCoreState.arena heq_e2)
                  (congrArg FullCoreState.arena_len heq_e2) (htb_c _ h)
              have he2_w : ∀ w', FullBveBceWeakOk c sl w' → FullBveBceWeakOk c se2 w' :=
                fun _ h => FullBveBceWeakOk.with_same_arena (congrArg FullCoreState.arena heq_e2)
                  (congrArg FullCoreState.arena_len heq_e2) (htb_w _ h)
              fvt_steps
              · have hw_ref_e2 : w.toNat ∈ fullArenaClauseRefs se2 := by
                  unfold fullArenaClauseRefs fullArenaClauseRefsCore
                  rw [heq_e2]; exact hw_weak_tb.1
                have hw_ar_e2 : (w.setWidth 64).toNat < se2.core.arena.length := by
                  rw [heq_e2]; exact hw_ar_lt
                have hw_p2_e2 : ((w.setWidth 64) + 2).toNat < se2.core.arena.length := by
                  have hsz_e2 : 3 ≤ fullArenaClauseSize se2 w.toNat :=
                    (hinv_e2.2.1.arena.refs_wf w.toNat hw_ref_e2).2.1
                  have hwf_e2 := hinv_e2.2.1.arena.refs_wf w.toNat hw_ref_e2
                  have := hinv_e2.1.core_ok.arena_len_arr; have := hinv_e2.1.core_ok.arena_len_le
                  bv_omega
                have hhdr_eq : se2.core.arena[(w.setWidth 64).toNat]'hw_ar_e2 =
                    fullArenaHdr se2 w.toNat := by
                  unfold fullArenaHdr fullArenaHdrCore
                  rw [← hw_nat, List.getElem?_eq_getElem hw_ar_e2, Option.getD_some]
                have har_eq :
                    se2.core.arena.set (w.setWidth 64).toNat
                      (se2.core.arena[(w.setWidth 64).toNat]'hw_ar_e2 ||| 524288) =
                    se2.core.arena.set w.toNat (fullArenaHdr se2 w.toNat ||| 0x00080000#32) := by
                  rw [hhdr_eq, hw_nat]; rfl
                fvt_steps
                let ar_mg := se2.core.arena.set w.toNat
                  (fullArenaHdr se2 w.toNat ||| 0x00080000#32)
                have hm_mg : (FullMem c { se2 with core := { se2.core with arena := ar_mg } } ⋆ R)
                    m := by
                  dsimp only [ar_mg]; rw [← har_eq]; exact hm
                clear hm
                have har_mg_lt : ((w.setWidth 64) + 2).toNat < ar_mg.length := by
                  rw [show ar_mg.length = se2.core.arena.length by simp [ar_mg]]; exact hw_p2_e2
                fvt_steps
                let ag_mg := se2.core.arena_garbage + 3#64 +
                  (ar_mg[((w.setWidth 64) + 2).toNat]'har_mg_lt).setWidth 64
                let smg : FullState :=
                  { se2 with
                    core := { se2.core with arena := ar_mg, arena_garbage := ag_mg }
                    scratch := { se2.scratch with bce_cnt := se2.scratch.bce_cnt + 1#64 } }
                have hinv_mg : FullDenseInvW c F0 F_cur smg :=
                  FullDenseInvW.with_bce_cnt
                    (FullDenseInvW.of_markGarb_zero hinv_e2 hw_ref_e2 ag_mg) _
                have hmg_c : ∀ w', FullBceCandOk c sl w' → FullBceCandOk c smg w' := fun w' hw =>
                  FullBceCandOk.with_same_arena rfl rfl
                    (FullBceCandOk.of_markGarb hinv_e2.1 hinv_e2.2.1 hw_ref_e2 ag_mg
                      (he2_c w' hw))
                have hmg_w : ∀ w', FullBveBceWeakOk c sl w' → FullBveBceWeakOk c smg w' :=
                  fun w' hw => FullBveBceWeakOk.with_same_arena rfl rfl
                    (FullBveBceWeakOk.of_markGarb hinv_e2.1 hinv_e2.2.1 hw_ref_e2 ag_mg
                      (he2_w w' hw))
                exact hJd (true, ()) _ ⟨smg, hinv_mg,
                  (congrArg FullCoreState.cur_vars heq_e2).trans hcvl,
                  (congrArg FullCoreState.fuel heq_e2).trans hfll, hscr_e2,
                  hmg_c, hmg_w, hm⟩
              · exact hJd (false, ()) m_e2 ⟨se2, hinv_e2,
                  (congrArg FullCoreState.cur_vars heq_e2).trans hcvl,
                  (congrArg FullCoreState.fuel heq_e2).trans hfll,
                  hscr_e2, he2_c, he2_w, hm_e2'⟩
        · -- `blk = false`
          exact hJd (false, ()) m_tb ⟨stb, hinv_tb, hcvl, hfll, rfl, htb_c, htb_w, hm_tb⟩
    · exact hQ rem sl ml hinvl hcvl hfll (by omega) hrem_ok hopp_eq hmono_c hml

theorem full_bce_pair_m4_wp (Γ : Env)
    (hSide : ∀ a m Q X, fullBceSideM4Spec a m Q X →
      Γ "full_bce_side_m4" [i64, i32, i32, i32, i32, i32] [i32] a m Q X) :
    ∀ a m Q X, fullBcePairM4Spec a m Q X → Func.wp Γ full_bce_pair_m4_body a m Q X := by
  rintro ⟨h, v, np, nn, ⟨⟩⟩ m0 Q X ⟨c, F0, F_cur, s, R, rfl, hinv0, hcap, hv_lt, hnp, hnn,
    hp_ok, hn_ok, hm0, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv := hinv0.1.core_ok.cur_vars_le
  have hpl_nat : (v <<< 1).toNat = 2 * v.toNat := by bv_omega
  have hnl_nat : ((v <<< 1) ||| 1).toNat = 2 * v.toNat + 1 := bv32_or1_even_toNat hpl_nat
  have h64_nat : (64 : BitVec 32).toNat = 64 := rfl
  unfold Func.wp full_bce_pair_m4_body
  fvt_steps
  c0_call hSide
  refine ⟨c, F0, F_cur, s, R, rfl, hinv0, by rw [hpl_nat]; omega,
    by simp; omega, by rw [h64_nat]; omega,
    Or.inl (by simp; omega),
    fun i hi => by simpa using hp_ok i hi,
    fun j hj => by rw [h64_nat]; exact (hn_ok j hj).toWeak,
    hm0, fun rem_p s1 m1 hinv1 hcv1 hfl1 hrem_le hp1 hn_eq1 hmono1 hm1 => ?_⟩
  fvt_steps
  c0_call hSide
  refine ⟨c, F0, F_cur, s1, R, rfl, hinv1, by rw [hnl_nat, hcv1]; omega,
    by rw [h64_nat]; omega,
    by simp; omega,
    Or.inr (by simp; omega),
    fun j hj => by
      rw [h64_nat] at hn_eq1 ⊢
      rw [hn_eq1 j hj]; exact hmono1 _ (hn_ok j hj),
    fun k hk => by simpa using (hp1 k hk).toWeak,
    hm1, fun _ s2 m2 hinv2 hcv2 hfl2 _ _ _ _ hm2 =>
      hQ s2 m2 hinv2 (hcv2.trans hcv1) (hfl2.trans hfl1) hm2⟩

theorem full_bce_var_m4_wp (Γ : Env)
    (hCollect : ∀ a m Q X, Full.fullBveCollectSpec a m Q X →
      Γ "full_bve_collect" [i64, i32, i64, i32] [i32] a m Q X)
    (hPair : ∀ a m Q X, fullBcePairM4Spec a m Q X →
      Γ "full_bce_pair_m4" [i64, i32, i32, i32] [] a m Q X) :
    ∀ a m Q X, fullBceVarM4Spec a m Q X → Func.wp Γ full_bce_var_m4_body a m Q X := by
  rintro ⟨h, v, ⟨⟩⟩ m0 Q X ⟨c, F0, F_cur, s, R, rfl, hinv0, hv_lt, hm0, hQ⟩
  have hmx := c.hmaxv; have hsc := c.hscr; unfold dimacsBound at hmx hsc
  have hcv := hinv0.1.core_ok.cur_vars_le
  unfold Func.wp full_bce_var_m4_body
  fvt_to_group
  · fvt_steps; exact hQ s m0 hinv0 rfl rfl hm0
  · have hcap128 : 128 ≤ c.scratch_cap := by
      have hc0 : ¬ c.scratch_cap % 2 ^ 64 < 128 := by c0_bound
      rw [Nat.mod_eq_of_lt (by omega)] at hc0; omega
    have hpl_nat : (v <<< 1).toNat = 2 * v.toNat := by bv_omega
    have hnl_nat : ((v <<< 1) ||| 1).toNat = 2 * v.toNat + 1 := bv32_or1_even_toNat hpl_nat
    have h64_nat : (64 : BitVec 32).toNat = 64 := rfl
    fvt_steps
    c0_call hCollect
    refine ⟨c, F0, F_cur, s, 0, R, rfl, hinv0, by rw [hpl_nat]; omega, by simp,
      by rw [h64_nat]; omega, hm0,
      fun np scr1 m1 hlen1 hpres1 hnp_ok hm1 => ?_⟩
    let s1 : FullState := { s with scratch := { s.scratch with scratch_buf := scr1 } }
    have hinv1 : FullDenseInvW c F0 F_cur s1 := FullDenseInvW.with_scratch_buf hinv0 hlen1
    fvt_steps
    c0_call hCollect
    refine ⟨c, F0, F_cur, s1, 64, R, rfl, hinv1, by dsimp only [s1]; rw [hnl_nat]; omega,
      (by show c.pScratchBuf + 256#64 = c.pScratchBuf + BitVec.ofNat 64 (4 * 64); rfl),
      by rw [h64_nat]; omega, hm1,
      fun nn scr2 m2 hlen2 hpres2 hnn_ok hm2 => ?_⟩
    let s2 : FullState := { s1 with scratch := { s1.scratch with scratch_buf := scr2 } }
    have hinv2 : FullDenseInvW c F0 F_cur s2 := FullDenseInvW.with_scratch_buf hinv1 hlen2
    fvt_steps
    · exact hQ s2 m2 hinv2 rfl rfl hm2
    · exact hQ s2 m2 hinv2 rfl rfl hm2
    · have hnp_ne : np ≠ 0xFFFFFFFF#32 := by c0_bound
      have hnn_ne : nn ≠ 0xFFFFFFFF#32 := by c0_bound
      obtain ⟨hnp_le, hnp_ent⟩ := hnp_ok.resolve_left hnp_ne
      obtain ⟨hnn_le, hnn_ent⟩ := hnn_ok.resolve_left hnn_ne
      have hnp64 : np.toNat ≤ 64 := by
        simpa [show (64#32 : BitVec 32).toNat = 64 from rfl] using hnp_le
      have hnn64 : nn.toNat ≤ 64 := by
        simpa [show (64#32 : BitVec 32).toNat = 64 from rfl] using hnn_le
      c0_call hPair
      refine ⟨c, F0, F_cur, s2, R, rfl, hinv2, hcap128, hv_lt, hnp64, hnn64,
        fun i hi => by
          have heq : scr2[i]? = scr1[i]? := hpres2 i (by omega) (Or.inl (by omega))
          change FullBceCandOk c s2 (scr2[i]?.getD 0#32)
          rw [heq]
          exact FullBceCandOk.with_same_arena rfl rfl
            (FullBceCandOk.of_entry hinv1 (by simpa using hnp_ent i hi)),
        fun j hj => FullBceCandOk.of_entry hinv2 (hnn_ent j hj),
        hm2, fun s3 m3 hinv3 hcv3 hfl3 hm3 => hQ s3 m3 hinv3 hcv3 hfl3 hm3⟩

private theorem m4_sparseInvW_of_prop_del {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hsp : FullSparseInvW c F0 F_cur s)
    {vals' : List (BitVec 8)} {flags' lvl' rsns' trl' tp' : List (BitVec 32)}
    {te' prop' : Nat} {unass' unfl' : BitVec 64} {wvec' arena' wstk' : List (BitVec 32)}
    {wlen' : Nat} {wu' fuel' ctype' cref' c0' c1' oom' ticks' : BitVec 64}
    {wsort' : List (BitVec 32)} {phases' : List (BitVec 8)} {delayed' : List (BitVec 32)}
    (hlen' : ({ s with
      core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                            trl := trl', trail_pos := tp', trail_end := te', propagated := prop',
                            unassigned := unass', unflushed := unfl', wvec := wvec',
                            arena := arena', wstk := wstk', wlen := wlen', wusable := wu',
                            fuel := fuel', confl_type := ctype', confl_ref := cref',
                            confl_lit0 := c0', confl_lit1 := c1', oom := oom' }
      scratch := { s.scratch with search_ticks := ticks', wsort := wsort',
                                  phases := phases', delayed := delayed' } } :
      FullState).LengthsOk c)
    (hw' : FullWitnessInv c F0 F_cur
      { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
                    trail_pos := tp', trail_end := te', propagated := prop',
                    unassigned := unass', unflushed := unfl', wvec := wvec', arena := arena',
                    wstk := wstk', wlen := wlen', wusable := wu', fuel := fuel',
                    confl_type := ctype', confl_ref := cref', confl_lit0 := c0',
                    confl_lit1 := c1', oom := oom' })
    (hperm : FullArenaPermEq s.core
      { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
                    trail_pos := tp', trail_end := te', propagated := prop',
                    unassigned := unass', unflushed := unfl', wvec := wvec', arena := arena',
                    wstk := wstk', wlen := wlen', wusable := wu', fuel := fuel',
                    confl_type := ctype', confl_ref := cref', confl_lit0 := c0',
                    confl_lit1 := c1', oom := oom' }) :
    FullSparseInvW c F0 F_cur
      { s with
        core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                              trl := trl', trail_pos := tp', trail_end := te', propagated := prop',
                              unassigned := unass', unflushed := unfl', wvec := wvec',
                              arena := arena', wstk := wstk', wlen := wlen', wusable := wu',
                              fuel := fuel', confl_type := ctype', confl_ref := cref',
                              confl_lit0 := c0', confl_lit1 := c1', oom := oom' }
        scratch := { s.scratch with
          search_ticks := ticks', wsort := wsort', phases := phases', delayed := delayed' } } := by
  let s0' : FullState :=
    { s with
      core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                            trl := trl', trail_pos := tp', trail_end := te',
                            propagated := prop', unassigned := unass', unflushed := unfl',
                            wvec := wvec', arena := arena', wstk := wstk', wlen := wlen',
                            wusable := wu', fuel := fuel', confl_type := ctype',
                            confl_ref := cref', confl_lit0 := c0', confl_lit1 := c1',
                            oom := oom' }
      scratch := { s.scratch with search_ticks := ticks', wsort := wsort', phases := phases' } }
  have h0_len : s0'.LengthsOk c :=
    ⟨hlen'.core_ok,
      { hlen'.scratch_ok with delayed_len_arr := hsp.1.scratch_ok.delayed_len_arr }⟩
  have h0 := m4_sparseInvW_of_prop_canon hsp h0_len hw' hperm
  exact ⟨hlen', hw', h0.2.2.1, h0.2.2.2.1, h0.2.2.2.2.1, h0.2.2.2.2.2⟩

theorem full_bce_m4_del_wp (Γ : Env)
    (hEnterDense : ∀ a m Q X, Full.fullEnterDenseSpec a m Q X →
      Γ "full_enter_dense" [i64] [.bool] a m Q X)
    (hBceVar : ∀ a m Q X, fullBceVarM4Spec a m Q X →
      Γ "full_bce_var_m4" [i64, i32] [] a m Q X)
    (hRebuild : ∀ a m Q X, Full.fullRebuildWatchesSpec a m Q X →
      Γ "full_rebuild_watches" [i64] [i64] a m Q X)
    (hProp : ∀ a m Q X, Full.fullPropagateDelSpec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X) :
    ∀ a m Q X, fullBceM4Spec a m Q X → Func.wp Γ full_bce_m4_body a m Q X := by
  rintro ⟨h, budget, ⟨⟩⟩ m0 Q X ⟨c, F0, s, R, rfl, hsp0, hcl0, hm0, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  unfold Func.wp full_bce_m4_body
  fvt_to_group
  · fvt_steps
    exact hQ 1#64 s m0 hsp0 hcl0 (Nat.le_refl _) (Or.inl rfl) (fun h => by cases h) hm0
  · fvt_steps
    exact hQ 1#64 s m0 hsp0 hcl0 (Nat.le_refl _) (Or.inl rfl) (fun h => by cases h) hm0
  · fvt_steps
    c0_call hEnterDense
    refine ⟨c, F0, s, R, rfl, hsp0, hm0, fun ok s1 m1 hcl1 hfl1 hok_t hok_f hm1 => ?_⟩
    fvt_to_group
    · -- `ok = true`: dense-mode dual-polarity BCE scan over active unassigned vars
      have hdn1 : FullDenseInv c F0 s1 := hok_t (by c0_bound)
      obtain ⟨F_cur1, hdw1⟩ := fullDenseInv_exists_witness hdn1
      have hcv1_le : s1.core.cur_vars ≤ c.max_vars := hdw1.1.core_ok.cur_vars_le
      fvt_steps
      refine wp_loop_inv (ts := [i64, i64])
        (fun (v, done, ()) ml => ∃ sl : FullState,
          FullDenseInvW c F0 F_cur1 sl ∧ sl.core.cur_vars = s1.core.cur_vars ∧
          sl.core.fuel.toNat ≤ s.core.fuel.toNat ∧ v.toNat ≤ s1.core.cur_vars ∧
          (FullMem c sl ⋆ R) ml)
        (fun (v, _, _) _ => s1.core.cur_vars - v.toNat) ?_ ?_
      · intro J hJ; fvt_steps
        exact hJ (0#64, 0#64, ()) m1 ⟨s1, hdw1, rfl, by rw [hfl1]; exact Nat.le_refl _,
          Nat.zero_le _, hm1⟩
      · intro J ⟨v, done, ⟨⟩⟩ ml ⟨sl, hinvl, hcvl, hfll, hv_le, hml⟩ ih
        have hv_lt_cv_of : v.toNat < (BitVec.ofNat 64 s1.core.cur_vars).toNat →
            v.toNat < s1.core.cur_vars := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact id
        fvt_to_group
        refine wp_join_group (ts := [])
          (fun () m_ex => ∃ s_ex : FullState,
            FullDenseInvW c F0 F_cur1 s_ex ∧ s_ex.core.fuel.toNat ≤ s.core.fuel.toNat ∧
            (FullMem c s_ex ⋆ R) m_ex) ?_ ?_
        · -- Post-loop exit: rebuild watches -> propagate
          rintro _ ⟨⟩ m_ex ⟨s_ex, hinv_ex, hfl_ex, hm_ex⟩
          c0_call hRebuild
          refine ⟨c, F0, s_ex, R, rfl, hinv_ex.toDense, hm_ex,
            fun rr s3 m3 hsp3 hcl3 hfl3 _ h20_3 hm3 => ?_⟩
          fvt_steps
          · exact hQ 20#64 s3 m3 hsp3 hcl3 (Nat.le_trans hfl3 hfl_ex) (Or.inr rfl)
              (fun _ => h20_3 (by c0_bound)) hm3
          · exact hQ 20#64 s3 m3 hsp3 hcl3 (Nat.le_trans hfl3 hfl_ex) (Or.inr rfl)
              (fun _ => m4_unsat_of_inconsistent hsp3 (by c0_bound)) hm3
          · obtain ⟨F_cur3, hsw3⟩ := hsp3.exists_witness
            c0_call hProp
            refine ⟨c, F0, F_cur3, s3, R, rfl, hsw3.1, hsw3.2.1, hsw3.2.2.2.2.2, hm3,
              fun pr vals_p flags_p lvl_p rsns_p trl_p tp_p te_p prop_p unass_p unfl_p
                wvec_p arena_p wstk_p wlen_p wu_p fuel_p ctype_p cref_p c0_p c1_p oom_p
                ticks_p wsort_p phases_p delayed_p m_p hlen_p hw_p _ hperm_p hfl_p _ _ hpr1 _ _
                hm_p => ?_⟩
            let s4 : FullState :=
              { s3 with
                core := { s3.core with
                  vals := vals_p, flags := flags_p, lvl := lvl_p, rsns := rsns_p,
                  trl := trl_p, trail_pos := tp_p, trail_end := te_p, propagated := prop_p,
                  unassigned := unass_p, unflushed := unfl_p, wvec := wvec_p,
                  arena := arena_p, wstk := wstk_p, wlen := wlen_p, wusable := wu_p,
                  fuel := fuel_p, confl_type := ctype_p, confl_ref := cref_p,
                  confl_lit0 := c0_p, confl_lit1 := c1_p, oom := oom_p }
                scratch := { s3.scratch with
                  search_ticks := ticks_p, wsort := wsort_p,
                  phases := phases_p, delayed := delayed_p } }
            have hsw4 : FullSparseInvW c F0 F_cur3 s4 :=
              m4_sparseInvW_of_prop_del hsw3 hlen_p hw_p hperm_p
            have hfl4 : s4.core.fuel.toNat ≤ s.core.fuel.toNat :=
              Nat.le_trans hfl_p (Nat.le_trans hfl3 hfl_ex)
            fvt_steps
            all_goals first
              | exact hQ 1#64 s4 m_p hsw4.toSparse hcl3 hfl4 (Or.inl rfl)
                  (fun h => by cases h) hm_p
              | exact hQ 20#64 s4 m_p hsw4.toSparse hcl3 hfl4 (Or.inr rfl)
                  (fun _ => FullVivTopSpecs.level0_unsat_of_conflict_okW hw_p hcl3
                    (hpr1 (by c0_bound)).2.2) hm_p
        · -- Loop condition & body
          intro Jex hJex
          fvt_to_group
          · have hv_lt : v.toNat < s1.core.cur_vars := hv_lt_cv_of (by c0_bound)
            have hv_fl : v.toNat < sl.core.flags.length := by
              rw [hinvl.1.core_ok.flags_len]; omega
            have hv2_lt : (v <<< (BitVec.toNat (1 : BitVec 64) % 64)).toNat <
                sl.core.vals.length := by
              rw [show BitVec.toNat (1 : BitVec 64) % 64 = 1 from rfl, BitVec.toNat_shiftLeft,
                Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega), hinvl.1.core_ok.vals_len]
              omega
            have hv1 : (v + 1#64).toNat = v.toNat + 1 := by bv_omega
            refine wp_join_group (ts := [i64])
              (fun (done', ()) mj => ∃ sj : FullState,
                FullDenseInvW c F0 F_cur1 sj ∧ sj.core.cur_vars = s1.core.cur_vars ∧
                sj.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c sj ⋆ R) mj) ?_ ?_
            · rintro _ ⟨done', ⟨⟩⟩ mj ⟨sj, hinvj, hcvj, hflj, hmj⟩
              fvt_steps
              exact ih (v + 1#64, done', ()) mj (by dsimp only; omega)
                ⟨sj, hinvj, hcvj, hflj, by omega, hmj⟩
            · intro Jv hJv
              fvt_steps
              · c0_call hBceVar
                refine ⟨c, F0, F_cur1, sl, R, rfl, hinvl,
                  by rw [bv64_toNat_setWidth32_lt (by omega), hcvl]; exact hv_lt, hml,
                  fun sv mv hinvv hcvv hflv hmv =>
                    hJv (done + 1#64, ()) mv ⟨sv, hinvv, hcvv.trans hcvl,
                      by rw [hflv]; exact hfll, hmv⟩⟩
              · exact hJv (done, ()) ml ⟨sl, hinvl, hcvl, hfll, hml⟩
              · exact hJv (done, ()) ml ⟨sl, hinvl, hcvl, hfll, hml⟩
          all_goals exact hJex () ml ⟨sl, hinvl, hfll, hml⟩
    · -- `ok = false`: check `inconsistent != 0`
      have hsp1 : FullSparseInv c F0 s1 := hok_f (by c0_bound)
      fvt_steps
      · exact hQ 20#64 s1 m1 hsp1 hcl1 (by rw [hfl1]; exact Nat.le_refl _) (Or.inr rfl)
          (fun _ => m4_unsat_of_inconsistent hsp1 (by c0_bound)) hm1
      · exact hQ 1#64 s1 m1 hsp1 hcl1 (by rw [hfl1]; exact Nat.le_refl _) (Or.inl rfl)
          (fun h => by cases h) hm1

theorem full_bce_m4_wp (Γ : Env)
    (hEnterDense : ∀ a m Q X, Full.fullEnterDenseSpec a m Q X →
      Γ "full_enter_dense" [i64] [.bool] a m Q X)
    (hBceVar : ∀ a m Q X, fullBceVarM4Spec a m Q X →
      Γ "full_bce_var_m4" [i64, i32] [] a m Q X)
    (hRebuild : ∀ a m Q X, Full.fullRebuildWatchesSpec a m Q X →
      Γ "full_rebuild_watches" [i64] [i64] a m Q X)
    (hProp : ∀ a m Q X, Full.fullPropagateSpec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X) :
    ∀ a m Q X, fullBceM4Spec a m Q X → Func.wp Γ full_bce_m4_body a m Q X :=
  full_bce_m4_del_wp Γ hEnterDense hBceVar hRebuild
    (fun a m Q X h => hProp a m Q X (Full.fullPropagateSpec_of_del h))

end BceM4Proofs

/-! ## 2. Closed `31`-Row `m4VivBceSpecTable`, `m4VivBceEnv`, & `ModuleOk` -/

section ModuleOkSection

/-- Closed `31`-row specification table (`16` M4f functions + `15` canonical externs, all `noExit`).
`full_vivify_m4` carries canonical `FullFastBveBudgets.fullVivifyFastSpec`; `full_viv_simplify` and
`full_viv_commit` carry the `red_refs`-preserving specs proved in `FullM4VivBceProof0`. -/
def m4VivBceSpecTable : List SpecEntry :=
  [ ⟨"full_viv_sort_noccs_m4", [i64, i32], [], fullVivSortNoccsM4Spec, true⟩
  , ⟨"full_viv_has_l0_m4", [i64, i32, i32], [.bool], fullVivHasL0M4Spec, true⟩
  , ⟨"full_viv_l0_simp_m4", [i64, i32, i32], [i64], fullVivL0SimpM4Spec, true⟩
  , ⟨"full_viv_reuse_prefix_m4", [i64, i32, i32], [], fullVivReusePrefixM4Spec, true⟩
  , ⟨"full_viv_finish_m4", [i64, i32, i32, .bool, i32, .bool], [i64], fullVivFinishM4Spec, true⟩
  , ⟨"full_viv_clause_m4", [i64, i32], [i64], fullVivClauseM4Spec, true⟩
  , ⟨"full_viv_sort_sched_m4", [i64, i64], [], fullVivSortSchedM4Spec, true⟩
  , ⟨"full_viv_tier_match_m4", [i64, i32, i64], [.bool], fullVivTierMatchM4Spec, true⟩
  , ⟨"full_viv_collect_m4", [i64, i64], [i64], fullVivCollectM4Spec, true⟩
  , ⟨"full_viv_keys_m4", [i64, i64], [], fullVivKeysM4Spec, true⟩
  , ⟨"full_viv_clear_tier_m4", [i64, i64], [], fullVivClearTierM4Spec, true⟩
  , ⟨"full_vivify_m4", [i64, i64, i64], [i64], FullFastBveBudgets.fullVivifyFastSpec, true⟩
  , ⟨"full_bce_side_m4", [i64, i32, i32, i32, i32, i32], [i32], fullBceSideM4Spec, true⟩
  , ⟨"full_bce_pair_m4", [i64, i32, i32, i32], [], fullBcePairM4Spec, true⟩
  , ⟨"full_bce_var_m4", [i64, i32], [], fullBceVarM4Spec, true⟩
  , ⟨"full_bce_m4", [i64, i64], [i64], fullBceM4Spec, true⟩
  , ⟨"full_arena_next", [i64, i32], [i32], fullArenaNextSpec, true⟩
  , ⟨"full_assign", [i64, i32, i32], [], fullAssignSpec, true⟩
  , ⟨"full_backtrack", [i64, i64], [], fullBacktrackSpec, true⟩
  , ⟨"full_propagate_ignore", [i64, i64], [i64], fullPropagateIgnoreSpec, true⟩
  , ⟨"full_propagate", [i64], [i64], fullPropagateSpec, true⟩
  , ⟨"full_viv_simplify", [i64, i32], [i64], fullVivSimplifyM4Spec, true⟩
  , ⟨"full_viv_deduce", [i64, i32, i32, i64], [i32], fullVivDeduceSpec, true⟩
  , ⟨"full_viv_commit", [i64, i32, i64, i32, .bool], [i64], fullVivCommitM4Spec, true⟩
  , ⟨"full_enter_dense", [i64], [.bool], fullEnterDenseSpec, true⟩
  , ⟨"full_rebuild_watches", [i64], [i64], fullRebuildWatchesSpec, true⟩
  , ⟨"full_bve_collect", [i64, i32, i64, i32], [i32], fullBveCollectSpec, true⟩
  , ⟨"full_bve_try_bce", [i64, i32, i32, i32, i32], [.bool], fullBveTryBceSpec, true⟩
  , ⟨"full_extend_push2", [i64, i32, i32], [.bool], fullExtendPush2Spec, true⟩
  , ⟨"full_extend_push_cl", [i64, i32, i32], [.bool], fullExtendPushClSpec, true⟩
  , ⟨"full_delete_binary", [i64, i32, i32], [], fullDeleteBinarySpec, true⟩ ]

theorem m4VivBceSpecTable_nodup : (m4VivBceSpecTable.map SpecEntry.name).Nodup := by
  decide

theorem m4VivBceSpecTable_noExit : ∀ e ∈ m4VivBceSpecTable, e.noExit = true := by
  intro e he
  have hall : m4VivBceSpecTable.all (fun x => x.noExit) = true := by t_kernel_rfl
  exact List.all_eq_true.mp hall e he

/-- Closed environment for `m4VivBceModule` (`16` M4f functions + `15` canonical externs). -/
def m4VivBceEnv : Env := Env.ofTable m4VivBceSpecTable

theorem m4VivBceEnv_noExit :
    ∀ f as bs xs m Q X X', m4VivBceEnv f as bs xs m Q X → m4VivBceEnv f as bs xs m Q X' :=
  Env.ofTable_noExit m4VivBceSpecTable_noExit

private theorem m4VivBceEnv_row {nm : String} {as bs : List Ty} {sp : Spec as bs}
    (hmem : (⟨nm, as, bs, sp, true⟩ : SpecEntry) ∈ m4VivBceSpecTable)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False)) :
    ∀ xs m Q X, sp xs m Q X → m4VivBceEnv nm as bs xs m Q X :=
  fun xs m Q X hs =>
    Env.ofTable_of_mem (e := ⟨nm, as, bs, sp, true⟩) hmem m4VivBceSpecTable_nodup (hno xs m Q X hs)

theorem m4_viv_sort_noccs_impl :
    SpecEntry.Impl m4VivBceEnv
      ⟨"full_viv_sort_noccs_m4", [i64, i32], [], full_viv_sort_noccs_m4_body⟩
      ⟨"full_viv_sort_noccs_m4", [i64, i32], [], fullVivSortNoccsM4Spec, true⟩ :=
  SpecEntry.Impl.of (full_viv_sort_noccs_m4_wp m4VivBceEnv)

theorem m4_viv_has_l0_impl :
    SpecEntry.Impl m4VivBceEnv
      ⟨"full_viv_has_l0_m4", [i64, i32, i32], [.bool], full_viv_has_l0_m4_body⟩
      ⟨"full_viv_has_l0_m4", [i64, i32, i32], [.bool], fullVivHasL0M4Spec, true⟩ :=
  SpecEntry.Impl.of (full_viv_has_l0_m4_wp m4VivBceEnv)

theorem m4_viv_l0_simp_impl :
    SpecEntry.Impl m4VivBceEnv
      ⟨"full_viv_l0_simp_m4", [i64, i32, i32], [i64], full_viv_l0_simp_m4_body⟩
      ⟨"full_viv_l0_simp_m4", [i64, i32, i32], [i64], fullVivL0SimpM4Spec, true⟩ :=
  SpecEntry.Impl.of (full_viv_l0_simp_m4_wp m4VivBceEnv
    (m4VivBceEnv_row (by simp [m4VivBceSpecTable]) (fun _ _ _ _ h => h))
    (m4VivBceEnv_row (by simp [m4VivBceSpecTable]) (fun _ _ _ _ h => h))
    (m4VivBceEnv_row (by simp [m4VivBceSpecTable]) (fun _ _ _ _ h => h)))

theorem m4_viv_reuse_prefix_impl :
    SpecEntry.Impl m4VivBceEnv
      ⟨"full_viv_reuse_prefix_m4", [i64, i32, i32], [], full_viv_reuse_prefix_m4_body⟩
      ⟨"full_viv_reuse_prefix_m4", [i64, i32, i32], [], fullVivReusePrefixM4Spec, true⟩ :=
  SpecEntry.Impl.of (full_viv_reuse_prefix_m4_wp m4VivBceEnv
    (m4VivBceEnv_row (by simp [m4VivBceSpecTable]) (fun _ _ _ _ h => h)))

theorem m4_viv_finish_impl :
    SpecEntry.Impl m4VivBceEnv
      ⟨"full_viv_finish_m4", [i64, i32, i32, .bool, i32, .bool], [i64], full_viv_finish_m4_body⟩
      ⟨"full_viv_finish_m4", [i64, i32, i32, .bool, i32, .bool], [i64],
        fullVivFinishM4Spec, true⟩ :=
  SpecEntry.Impl.of (full_viv_finish_m4_wp m4VivBceEnv
    (m4VivBceEnv_row (by simp [m4VivBceSpecTable]) (fun _ _ _ _ h => h))
    (m4VivBceEnv_row (by simp [m4VivBceSpecTable]) (fun _ _ _ _ h => h))
    (m4VivBceEnv_row (by simp [m4VivBceSpecTable]) (fun _ _ _ _ h => h)))

theorem m4_viv_clause_impl :
    SpecEntry.Impl m4VivBceEnv
      ⟨"full_viv_clause_m4", [i64, i32], [i64], full_viv_clause_m4_body⟩
      ⟨"full_viv_clause_m4", [i64, i32], [i64], fullVivClauseM4Spec, true⟩ :=
  SpecEntry.Impl.of (full_viv_clause_m4_wp m4VivBceEnv
    (m4VivBceEnv_row (by simp [m4VivBceSpecTable]) (fun _ _ _ _ h => h))
    (m4VivBceEnv_row (by simp [m4VivBceSpecTable]) (fun _ _ _ _ h => h))
    (m4VivBceEnv_row (by simp [m4VivBceSpecTable]) (fun _ _ _ _ h => h))
    (m4VivBceEnv_row (by simp [m4VivBceSpecTable]) (fun _ _ _ _ h => h))
    (m4VivBceEnv_row (by simp [m4VivBceSpecTable]) (fun _ _ _ _ h => h))
    (m4VivBceEnv_row (by simp [m4VivBceSpecTable]) (fun _ _ _ _ h => h))
    (m4VivBceEnv_row (by simp [m4VivBceSpecTable]) (fun _ _ _ _ h => h)))

theorem m4_viv_sort_sched_impl :
    SpecEntry.Impl m4VivBceEnv
      ⟨"full_viv_sort_sched_m4", [i64, i64], [], full_viv_sort_sched_m4_body⟩
      ⟨"full_viv_sort_sched_m4", [i64, i64], [], fullVivSortSchedM4Spec, true⟩ :=
  SpecEntry.Impl.of (full_viv_sort_sched_m4_wp m4VivBceEnv)

theorem m4_viv_tier_match_impl :
    SpecEntry.Impl m4VivBceEnv
      ⟨"full_viv_tier_match_m4", [i64, i32, i64], [.bool], full_viv_tier_match_m4_body⟩
      ⟨"full_viv_tier_match_m4", [i64, i32, i64], [.bool], fullVivTierMatchM4Spec, true⟩ :=
  SpecEntry.Impl.of (full_viv_tier_match_m4_wp m4VivBceEnv)

theorem m4_viv_collect_impl :
    SpecEntry.Impl m4VivBceEnv
      ⟨"full_viv_collect_m4", [i64, i64], [i64], full_viv_collect_m4_body⟩
      ⟨"full_viv_collect_m4", [i64, i64], [i64], fullVivCollectM4Spec, true⟩ :=
  SpecEntry.Impl.of (full_viv_collect_m4_wp m4VivBceEnv
    (m4VivBceEnv_row (by simp [m4VivBceSpecTable]) (fun _ _ _ _ h => h))
    (m4VivBceEnv_row (by simp [m4VivBceSpecTable]) (fun _ _ _ _ h => h)))

theorem m4_viv_keys_impl :
    SpecEntry.Impl m4VivBceEnv
      ⟨"full_viv_keys_m4", [i64, i64], [], full_viv_keys_m4_body⟩
      ⟨"full_viv_keys_m4", [i64, i64], [], fullVivKeysM4Spec, true⟩ :=
  SpecEntry.Impl.of (full_viv_keys_m4_wp m4VivBceEnv)

theorem m4_viv_clear_tier_impl :
    SpecEntry.Impl m4VivBceEnv
      ⟨"full_viv_clear_tier_m4", [i64, i64], [], full_viv_clear_tier_m4_body⟩
      ⟨"full_viv_clear_tier_m4", [i64, i64], [], fullVivClearTierM4Spec, true⟩ :=
  SpecEntry.Impl.of (full_viv_clear_tier_m4_wp m4VivBceEnv
    (m4VivBceEnv_row (by simp [m4VivBceSpecTable]) (fun _ _ _ _ h => h))
    (m4VivBceEnv_row (by simp [m4VivBceSpecTable]) (fun _ _ _ _ h => h)))

theorem m4_vivify_impl :
    SpecEntry.Impl m4VivBceEnv
      ⟨"full_vivify_m4", [i64, i64, i64], [i64], full_vivify_m4_body⟩
      ⟨"full_vivify_m4", [i64, i64, i64], [i64], FullFastBveBudgets.fullVivifyFastSpec, true⟩ :=
  SpecEntry.Impl.of (full_vivify_m4_wp m4VivBceEnv
    (m4VivBceEnv_row (by simp [m4VivBceSpecTable]) (fun _ _ _ _ h => h))
    (m4VivBceEnv_row (by simp [m4VivBceSpecTable]) (fun _ _ _ _ h => h))
    (m4VivBceEnv_row (by simp [m4VivBceSpecTable]) (fun _ _ _ _ h => h))
    (m4VivBceEnv_row (by simp [m4VivBceSpecTable]) (fun _ _ _ _ h => h))
    (m4VivBceEnv_row (by simp [m4VivBceSpecTable]) (fun _ _ _ _ h => h))
    (m4VivBceEnv_row (by simp [m4VivBceSpecTable]) (fun _ _ _ _ h => h))
    (m4VivBceEnv_row (by simp [m4VivBceSpecTable]) (fun _ _ _ _ h => h)))

theorem m4_bce_side_impl :
    SpecEntry.Impl m4VivBceEnv
      ⟨"full_bce_side_m4", [i64, i32, i32, i32, i32, i32], [i32], full_bce_side_m4_body⟩
      ⟨"full_bce_side_m4", [i64, i32, i32, i32, i32, i32], [i32], fullBceSideM4Spec, true⟩ :=
  SpecEntry.Impl.of (full_bce_side_m4_wp m4VivBceEnv
    (m4VivBceEnv_row (by simp [m4VivBceSpecTable]) (fun _ _ _ _ h => h))
    (m4VivBceEnv_row (by simp [m4VivBceSpecTable]) (fun _ _ _ _ h => h))
    (m4VivBceEnv_row (by simp [m4VivBceSpecTable]) (fun _ _ _ _ h => h))
    (m4VivBceEnv_row (by simp [m4VivBceSpecTable]) (fun _ _ _ _ h => h)))

theorem m4_bce_pair_impl :
    SpecEntry.Impl m4VivBceEnv
      ⟨"full_bce_pair_m4", [i64, i32, i32, i32], [], full_bce_pair_m4_body⟩
      ⟨"full_bce_pair_m4", [i64, i32, i32, i32], [], fullBcePairM4Spec, true⟩ :=
  SpecEntry.Impl.of (full_bce_pair_m4_wp m4VivBceEnv
    (m4VivBceEnv_row (by simp [m4VivBceSpecTable]) (fun _ _ _ _ h => h)))

theorem m4_bce_var_impl :
    SpecEntry.Impl m4VivBceEnv
      ⟨"full_bce_var_m4", [i64, i32], [], full_bce_var_m4_body⟩
      ⟨"full_bce_var_m4", [i64, i32], [], fullBceVarM4Spec, true⟩ :=
  SpecEntry.Impl.of (full_bce_var_m4_wp m4VivBceEnv
    (m4VivBceEnv_row (by simp [m4VivBceSpecTable]) (fun _ _ _ _ h => h))
    (m4VivBceEnv_row (by simp [m4VivBceSpecTable]) (fun _ _ _ _ h => h)))

theorem m4_bce_impl :
    SpecEntry.Impl m4VivBceEnv
      ⟨"full_bce_m4", [i64, i64], [i64], full_bce_m4_body⟩
      ⟨"full_bce_m4", [i64, i64], [i64], fullBceM4Spec, true⟩ :=
  SpecEntry.Impl.of (full_bce_m4_wp m4VivBceEnv
    (m4VivBceEnv_row (by simp [m4VivBceSpecTable]) (fun _ _ _ _ h => h))
    (m4VivBceEnv_row (by simp [m4VivBceSpecTable]) (fun _ _ _ _ h => h))
    (m4VivBceEnv_row (by simp [m4VivBceSpecTable]) (fun _ _ _ _ h => h))
    (m4VivBceEnv_row (by simp [m4VivBceSpecTable]) (fun _ _ _ _ h => h)))

theorem m4VivBce_allFns_wf : AllFns Fn.Wf m4VivBceModule.fns :=
  ⟨full_viv_sort_noccs_m4_wf, full_viv_has_l0_m4_wf, full_viv_l0_simp_m4_wf,
    full_viv_reuse_prefix_m4_wf, full_viv_finish_m4_wf, full_viv_clause_m4_wf,
    full_viv_sort_sched_m4_wf, full_viv_tier_match_m4_wf, full_viv_collect_m4_wf,
    full_viv_keys_m4_wf, full_viv_clear_tier_m4_wf, full_vivify_m4_wf, full_bce_side_m4_wf,
    full_bce_pair_m4_wf, full_bce_var_m4_wf, full_bce_m4_wf, trivial⟩

theorem m4VivBce_tableImpl : TableImpl m4VivBceEnv m4VivBceModule.fns m4VivBceSpecTable :=
  ⟨m4_viv_sort_noccs_impl, m4_viv_has_l0_impl, m4_viv_l0_simp_impl, m4_viv_reuse_prefix_impl,
    m4_viv_finish_impl, m4_viv_clause_impl, m4_viv_sort_sched_impl, m4_viv_tier_match_impl,
    m4_viv_collect_impl, m4_viv_keys_impl, m4_viv_clear_tier_impl, m4_vivify_impl,
    m4_bce_side_impl, m4_bce_pair_impl, m4_bce_var_impl, m4_bce_impl, trivial⟩

/-- Headline `ModuleOk` certifying all `16` M4f functions in `m4VivBceModule`. -/
theorem m4VivBce_moduleOk : ModuleOk m4VivBceEnv m4VivBceModule :=
  Env.ofTable_moduleOk m4VivBce_acyclic m4VivBce_allFns_wf m4VivBce_tableImpl

end ModuleOkSection

/-! ## 3. Concrete `Mem 64` UNSAT Non-Vacuity for All `16` Functions (`XPost := False`) -/

section ConcreteNonVacuity

/-- Minimal UNSAT formula `{(x0), (¬x0)}` over variables `{0, 1, 2}`. -/
def nvM4F0 : CNF Nat := cnfOfClauses [[0], [1]]

theorem nvM4F0_unsat : nvM4F0.Unsat := by
  rw [CNF.unsat_iff_not_sat]; intro α hα
  have h0 : (cnfClause [0]).Sat α :=
    (CNF.sat_iff_all_mem_sat.mp hα) _ (CNF.Internal.mem_iff.mpr (by simp [nvM4F0, cnfOfClauses]))
  have h1 : (cnfClause [1]).Sat α :=
    (CNF.sat_iff_all_mem_sat.mp hα) _ (CNF.Internal.mem_iff.mpr (by simp [nvM4F0, cnfOfClauses]))
  rw [CNF.Clause.sat_iff_exists_mem_eq] at h0 h1
  obtain ⟨⟨v0, p0⟩, hm0, he0⟩ := h0; obtain ⟨⟨v1, p1⟩, hm1, he1⟩ := h1
  rw [mem_cnfClause_iff] at hm0 hm1; simp only [List.mem_singleton] at hm0 hm1
  cases p0 <;> cases p1 <;> simp [litOfLiteral, mkLit] at hm0 hm1
  · have hv0 : v0 = 0 := by omega
    have hv1 : v1 = 0 := by omega
    subst hv0 hv1; dsimp only at he0 he1; rw [he0] at he1; cases he1
  · omega

/-- Concrete `FullCfg` (`hdr = 0x1000#64`, `avail = 2588`, `max_vars = 3`, `arena_cap = 6`,
`wcap = 1`, `scratch_cap = 128`, `slack = 0`). -/
def nvM4Cfg : FullCfg where
  hdr := 0x1000#64
  avail := 2588
  mv := 3
  max_vars := 3
  bva_cap := 0
  nc := 2
  arena_cap := 6
  wcap := 1
  delayed_cap := 0
  red_cap := 0
  extend_cap := 0
  scratch_cap := 128
  hbva := rfl
  hmv := by decide
  hmaxv := by decide
  hnc := by decide
  harena := by decide
  hwcap := by decide
  hdel := by decide
  hred := by decide
  hext := by decide
  hscr := by decide
  havail_fit := by decide
  hsize := by decide

def nvM4Scratch : FullScratch where
  heap_len := 0
  scinc := 0#64
  rel_period := 0#64
  rel_limit := 0#64
  rel_wait := 0#64
  rel_u := 0#64
  rel_v := 0#64
  rel_trigger := 0#64
  conflicts := 0#64
  learned_lits := 0#64
  min_removed := 0#64
  delayed_len := 0
  stable := 0#64
  switched := 0#64
  mode_count := 0#64
  mode_confl_lim := 0#64
  mode_tick_lim := 0#64
  mode_saved_ticks := 0#64
  search_ticks := 0#64
  q_first := 0#64
  q_last := 0#64
  q_search_idx := 0#64
  q_search_stamp := 0#64
  q_cur_stamp := 0#64
  target_assigned := 0#64
  best_assigned := 0#64
  rephase_limit := 0#64
  rephased := 0#64
  reduce_limit := 0#64
  reductions := 0#64
  tier1 := 2#64
  tier2 := 6#64
  restarts := 0#64
  restart_limit := 0#64
  ema_fast_biased := 0#64
  ema_fast_exp := 0#64
  ema_slow_biased := 0#64
  ema_slow_exp := 0#64
  extend_len := 0
  rng_state := 1#64
  chrono_levels := 0#64
  otfs_cnt := 0#64
  eager_sub_cnt := 0#64
  probe_limit := 0#64
  probings := 0#64
  elim_limit := 0#64
  eliminations := 0#64
  elim_bound := 0#64
  iterating := 0#64
  hbr_cnt := 0#64
  trans_cnt := 0#64
  viv_cnt := 0#64
  subst_cnt := 0#64
  cong_cnt := 0#64
  sweep_cnt := 0#64
  bve_cnt := 0#64
  bce_cnt := 0#64
  bva_cnt := 0#64
  walk_cnt_stat := 0#64
  fwd_sub_cnt := 0#64
  fwd_str_cnt := 0#64
  ant_sz := 0#64
  res_sz := 0#64
  walk_vals := List.replicate 6 0#8
  phases := List.replicate 3 0#8
  phases_target := List.replicate 3 0#8
  phases_best := List.replicate 3 0#8
  walk_best := List.replicate 3 0#8
  heap := List.replicate 3 0#32
  pos := List.replicate 3 0#32
  shrink_stk := List.replicate 3 0#32
  q_prev := List.replicate 3 0#32
  q_next := List.replicate 3 0#32
  q_stamp := List.replicate 3 0#32
  wsort := List.replicate 6 0#32
  work_stk1 := List.replicate 6 0#32
  work_stk2 := List.replicate 6 0#32
  tarjan_mark := List.replicate 6 0#32
  tarjan_reach := List.replicate 6 0#32
  score := List.replicate 3 0#64
  sim_sig := List.replicate 3 0#64
  glue_used := List.replicate 64 0#32
  last_learned := List.replicate 16 0xFFFFFFFF#32
  delayed := []
  red_refs := []
  extend_stk := []
  scratch_buf := List.replicate 128 0#32

/-- Concrete sparse-mode UNSAT state with 1 live 3-literal arena clause `[x0, x1, x2]` at `cref = 0`
and cleared `last_learned[0..15] = 0xFFFFFFFFu`. -/
def nvM4SparseState : FullState where
  core :=
    { d_cur := 0#64, d_val := 0#64, cur_vars := 3, unassigned := 3#64
      arena_len := 6, wlen := 1, wusable := 0#64, arena_garbage := 0#64
      first_reducible := 0#64, num_irred := 1#64, num_redundant := 0#64, num_binary := 0#64
      unflushed := 0#64, probing := 0#64, trail_end := 0, propagated := 0
      cur_level := 0, fuel := 100#64, confl_ref := 0xFFFFFFFF#64, confl_type := 0#64
      confl_lit0 := 0#64, confl_lit1 := 0#64, tmp_cnt := 0, tmp_len := 0
      min_clr_len := 0, min_clr_full := 0#64, oom := 0#64, dense_mode := 0#64
      inconsistent := 0#64
      vals := List.replicate 6 0#8
      lit_mark := List.replicate 6 0#8
      mrk := List.replicate 3 0#8
      flags := List.replicate 3 1#32
      lvl := List.replicate 3 0#32
      rsns := List.replicate 3 0xFFFFFFFF#32
      trl := List.replicate 3 0#32
      trail_pos := List.replicate 3 0#32
      tmp := [0#32, 2#32, 4#32]
      min_clr := List.replicate 3 0#32
      frame_trail := List.replicate 4 0#32
      frame_dec := List.replicate 4 0#32
      wvec := List.replicate 12 0#32
      repr := List.replicate 6 0#32
      min_stk := List.replicate 8 0#32
      arena := [0#32, 0#32, 3#32, 0#32, 2#32, 4#32]
      wstk := [0#32] }
  scratch := nvM4Scratch

/-- Concrete dense-mode UNSAT state (`dense_mode = 1#64`) sharing all tables with `nvM4SparseState`.
-/
def nvM4DenseState : FullState :=
  { nvM4SparseState with core := { nvM4SparseState.core with dense_mode := 1#64 } }

def nvM4BlockHdr (s : FullState) : List UInt8 :=
  bytes64 [3#64, 2#64, 0#64, 0#64] ++ bytes64 (Full.hdrTailWords nvM4Cfg s)

def nvM4BlockBytes : List UInt8 :=
  (bytesOf (t := i8) nvM4SparseState.core.vals ++ List.replicate 2 0) ++
  (bytesOf (t := i8) nvM4SparseState.scratch.walk_vals ++ List.replicate 2 0) ++
  (bytesOf (t := i8) nvM4SparseState.core.lit_mark ++ List.replicate 2 0) ++
  (bytesOf (t := i8) nvM4SparseState.core.mrk ++ List.replicate 5 0) ++
  (bytesOf (t := i8) nvM4SparseState.scratch.phases ++ List.replicate 5 0) ++
  (bytesOf (t := i8) nvM4SparseState.scratch.phases_target ++ List.replicate 5 0) ++
  (bytesOf (t := i8) nvM4SparseState.scratch.phases_best ++ List.replicate 5 0) ++
  (bytesOf (t := i8) nvM4SparseState.scratch.walk_best ++ List.replicate 5 0)

def nvM4BlockU32A : List UInt8 :=
  (bytesOf (t := i32) nvM4SparseState.core.flags ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvM4SparseState.core.lvl ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvM4SparseState.core.rsns ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvM4SparseState.core.trl ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvM4SparseState.core.trail_pos ++ List.replicate 4 0)

def nvM4BlockU32B : List UInt8 :=
  (bytesOf (t := i32) nvM4SparseState.core.tmp ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvM4SparseState.scratch.heap ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvM4SparseState.scratch.pos ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvM4SparseState.core.min_clr ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvM4SparseState.scratch.shrink_stk ++ List.replicate 4 0)

def nvM4BlockU32C : List UInt8 :=
  (bytesOf (t := i32) nvM4SparseState.scratch.q_prev ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvM4SparseState.scratch.q_next ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvM4SparseState.scratch.q_stamp ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvM4SparseState.core.frame_trail ++ List.replicate 0 0) ++
  (bytesOf (t := i32) nvM4SparseState.core.frame_dec ++ List.replicate 0 0)

def nvM4BlockWvec : List UInt8 :=
  bytesOf (t := i32) nvM4SparseState.core.wvec ++
  bytesOf (t := i32) nvM4SparseState.core.repr ++
  bytesOf (t := i32) nvM4SparseState.scratch.wsort ++
  bytesOf (t := i32) nvM4SparseState.scratch.work_stk1 ++
  bytesOf (t := i32) nvM4SparseState.scratch.work_stk2 ++
  bytesOf (t := i32) nvM4SparseState.scratch.tarjan_mark ++
  bytesOf (t := i32) nvM4SparseState.scratch.tarjan_reach ++
  bytes64 nvM4SparseState.scratch.score ++
  bytes64 nvM4SparseState.scratch.sim_sig

def nvM4BlockTail : List UInt8 :=
  bytesOf (t := i32) nvM4SparseState.core.min_stk ++
  bytesOf (t := i32) nvM4SparseState.scratch.glue_used ++
  bytesOf (t := i32) nvM4SparseState.scratch.last_learned ++
  bytesOf (t := i32) nvM4SparseState.core.arena ++
  bytesOf (t := i32) nvM4SparseState.core.wstk ++
  bytesOf (t := i32) nvM4SparseState.scratch.delayed ++
  bytesOf (t := i32) nvM4SparseState.scratch.red_refs ++
  bytesOf (t := i32) nvM4SparseState.scratch.extend_stk ++
  bytesOf (t := i32) nvM4SparseState.scratch.scratch_buf ++
  List.replicate 0 0

def nvM4BytesOf (s : FullState) : List UInt8 :=
  nvM4BlockHdr s ++ nvM4BlockBytes ++ nvM4BlockU32A ++ nvM4BlockU32B ++
  nvM4BlockU32C ++ nvM4BlockWvec ++ nvM4BlockTail

/-- Concrete `2588`-byte sparse-mode `Mem 64` heap mapped at `nvM4Cfg.hdr` (`0x1000#64`). -/
def nvM4SparseMem : Mem 64 := (nvM4BytesOf nvM4SparseState).At nvM4Cfg.hdr

/-- Concrete `2588`-byte dense-mode `Mem 64` heap mapped at `nvM4Cfg.hdr` (`0x1000#64`). -/
def nvM4DenseMem : Mem 64 := (nvM4BytesOf nvM4DenseState).At nvM4Cfg.hdr

private theorem m4_nv_sep_append {P Q : Mem 64 → Prop} {a b : BitVec 64} {bs1 bs2 : List UInt8}
    (hb : b = a + BitVec.ofNat 64 bs1.length) (hlen : bs1.length + bs2.length ≤ 2 ^ 64)
    (h1 : P (bs1.At a)) (h2 : Q (bs2.At b)) : (P ⋆ Q) ((bs1 ++ bs2).At a) := by
  have heq := congrFun (Mem.At_append_sep bs1 bs2 a hlen) ((bs1 ++ bs2).At a)
  rw [← hb] at heq
  exact sep_mono2 (fun _ h => h ▸ h1) (fun _ h => h ▸ h2) _ (heq.mp rfl)

private theorem m4_nv_arr_pad_p {t : Ty} {a : BitVec 64} {xs : List (Val t)} (n pad : Nat)
    (hn : t.bytes * xs.length = n) (hbd : n + pad ≤ 2 ^ 64) :
    (bytesOf xs ++ List.replicate pad 0).length = n + pad ∧
    (array (t := t) a xs ⋆ region (a + BitVec.ofNat 64 n) pad)
      ((bytesOf xs ++ List.replicate pad 0).At a) :=
  ⟨by rw [List.length_append, bytesOf_length, List.length_replicate, hn],
    m4_nv_sep_append (by rw [bytesOf_length, hn])
      (by rw [bytesOf_length, List.length_replicate]; omega)
      (array_bytes a xs (by omega)) ⟨List.replicate pad 0, List.length_replicate, rfl⟩⟩

private theorem m4_nv_arr_p {t : Ty} {a : BitVec 64} {xs : List (Val t)} (n : Nat)
    (hn : t.bytes * xs.length = n) (hbd : n ≤ 2 ^ 64) :
    (bytesOf xs).length = n ∧ array (t := t) a xs ((bytesOf xs).At a) :=
  ⟨by rw [bytesOf_length, hn], array_bytes a xs (by omega)⟩

private theorem m4_nv_arr64_p {a : BitVec 64} {xs : List (BitVec 64)} (n : Nat)
    (hn : 8 * xs.length = n) (hbd : n ≤ 2 ^ 64) :
    (bytes64 xs).length = n ∧ array64 a xs ((bytes64 xs).At a) :=
  ⟨by rw [bytes64_length, hn], array64_bytes a xs (by omega)⟩

private theorem m4_nv_join {P Q : Mem 64 → Prop} {a b : BitVec 64} {bs1 bs2 : List UInt8}
    {n1 n2 : Nat} (h1 : bs1.length = n1 ∧ P (bs1.At a))
    (h2 : bs2.length = n2 ∧ Q (bs2.At b))
    (hb : b = a + BitVec.ofNat 64 n1) (hbd : n1 + n2 ≤ 2 ^ 64) :
    (bs1 ++ bs2).length = n1 + n2 ∧ (P ⋆ Q) ((bs1 ++ bs2).At a) :=
  ⟨by rw [List.length_append, h1.1, h2.1], m4_nv_sep_append (h1.1 ▸ hb) (by omega) h1.2 h2.2⟩

private theorem m4_nv_reorg {P Q : Mem 64 → Prop} {bs : List UInt8} {a : BitVec 64} {n : Nat}
    (h : bs.length = n ∧ P (bs.At a)) (himp : ∀ m, P m → Q m) : bs.length = n ∧ Q (bs.At a) :=
  ⟨h.1, himp _ h.2⟩

private theorem m4_nv_zip4 {A1 B1 A2 B2 A3 B3 A4 B4 : Mem 64 → Prop} {m : Mem 64}
    (h : ((((A1 ⋆ B1) ⋆ (A2 ⋆ B2)) ⋆ (A3 ⋆ B3)) ⋆ (A4 ⋆ B4)) m) :
    (((A1 ⋆ A3 ⋆ A4) ⋆ A2) ⋆ (B1 ⋆ B2 ⋆ B3 ⋆ B4)) m := sep_ac h

private theorem m4_nv_zip4_tail {C A2 P1 A5 B5 A6 B6 A7 B7 A8 B8 : Mem 64 → Prop} {m : Mem 64}
    (h : ((((((C ⋆ A2) ⋆ P1) ⋆ (A5 ⋆ B5)) ⋆ (A6 ⋆ B6)) ⋆ (A7 ⋆ B7)) ⋆ (A8 ⋆ B8)) m) :
    (C ⋆ (A2 ⋆ A5 ⋆ A6 ⋆ A7 ⋆ A8) ⋆ (P1 ⋆ B5 ⋆ B6 ⋆ B7 ⋆ B8)) m := sep_ac h

private theorem nvM4Mem_of_mode (dm : BitVec 64) :
    let s : FullState :=
      { nvM4SparseState with core := { nvM4SparseState.core with dense_mode := dm } }
    FullMem nvM4Cfg s ((nvM4BytesOf s).At nvM4Cfg.hdr) := by
  intro s
  let c := nvM4Cfg
  have hvb : valsBytes c.max_vars - 2 * c.max_vars = 2 := by decide
  have hmb : markBytes c.max_vars - c.max_vars = 5 := by decide
  have hu4 : u32FullBytes c.max_vars - 4 * c.max_vars = 4 := by decide
  have hu8 : u32FullBytes c.max_vars - 4 * (c.max_vars + 1) = 0 := by decide
  have hmv3 : BitVec.ofNat 64 c.max_vars = 3#64 := rfl
  have hmv6 : BitVec.ofNat 64 (2 * c.max_vars) = 6#64 := rfl
  have hmv12 : BitVec.ofNat 64 (4 * c.max_vars) = 12#64 := rfl
  have hmv16 : BitVec.ofNat 64 (4 * (c.max_vars + 1)) = 16#64 := rfl
  have hHdr : (nvM4BlockHdr s).length = 1152 ∧
      (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc)
        s.core.d_cur s.core.d_val ⋆ array64 (c.hdr + 32) (Full.hdrTailWords c s))
        ((nvM4BlockHdr s).At c.hdr) :=
    m4_nv_join
      (m4_nv_arr64_p (a := c.hdr) (xs := [3#64, 2#64, 0#64, 0#64]) 32 rfl (by decide))
      (m4_nv_arr64_p (a := c.hdr + 32) (xs := Full.hdrTailWords c s) 1120
        (by rw [Full.hdrTailWords_length]) (by decide))
      (by decide) (by decide)
  have hBytes : nvM4BlockBytes.length = 64 ∧
      (FullCoreByteArrs c s.core ⋆ FullScrByteArrs c s.scratch ⋆ c.padBytes)
        (nvM4BlockBytes.At c.pVals) := by
    have h1 := m4_nv_arr_pad_p (t := i8) (a := c.pVals) (xs := s.core.vals) 6 2 rfl (by decide)
    have h2 := m4_nv_arr_pad_p (t := i8) (a := c.pWalkVals) (xs := s.scratch.walk_vals) 6 2 rfl
      (by decide)
    have h3 := m4_nv_arr_pad_p (t := i8) (a := c.pLitMark) (xs := s.core.lit_mark) 6 2 rfl
      (by decide)
    have h4 := m4_nv_arr_pad_p (t := i8) (a := c.pMark) (xs := s.core.mrk) 3 5 rfl (by decide)
    have h5 := m4_nv_arr_pad_p (t := i8) (a := c.pPhases) (xs := s.scratch.phases) 3 5 rfl
      (by decide)
    have h6 := m4_nv_arr_pad_p (t := i8) (a := c.pPhasesTarget) (xs := s.scratch.phases_target) 3 5
      rfl (by decide)
    have h7 := m4_nv_arr_pad_p (t := i8) (a := c.pPhasesBest) (xs := s.scratch.phases_best) 3 5 rfl
      (by decide)
    have h8 := m4_nv_arr_pad_p (t := i8) (a := c.pWalkBest) (xs := s.scratch.walk_best) 3 5 rfl
      (by decide)
    let pB1 : Mem 64 → Prop :=
      region (c.pVals + 6#64) 2 ⋆ region (c.pWalkVals + 6#64) 2 ⋆
      region (c.pLitMark + 6#64) 2 ⋆ region (c.pMark + 3#64) 5
    have h12 := m4_nv_join h1 h2 (by decide) (by decide)
    have h123 := m4_nv_join h12 h3 (by decide) (by decide)
    have h1234 := m4_nv_reorg (m4_nv_join h123 h4 (by decide) (by decide))
      (Q := (FullCoreByteArrs c s.core ⋆ array (t := i8) c.pWalkVals s.scratch.walk_vals) ⋆ pB1)
      fun _ hm => m4_nv_zip4 hm
    have h12345 := m4_nv_join h1234 h5 (by decide) (by decide)
    have h123456 := m4_nv_join h12345 h6 (by decide) (by decide)
    have h1234567 := m4_nv_join h123456 h7 (by decide) (by decide)
    have hall := m4_nv_join h1234567 h8 (by decide) (by decide)
    exact m4_nv_reorg hall fun _ hm => by
      have hfin := m4_nv_zip4_tail hm
      unfold FullScrByteArrs FullCfg.padBytes
      rw [hvb, hmb, hmv6, hmv3]; simpa only [pB1, sep_assoc] using hfin
  have hU32A : nvM4BlockU32A.length = 80 ∧
      ((array (t := i32) c.pFlags s.core.flags ⋆ array (t := i32) c.pLevel s.core.lvl ⋆
        array (t := i32) c.pReason s.core.rsns ⋆ array (t := i32) c.pTrail s.core.trl ⋆
        array (t := i32) c.pTrailPos s.core.trail_pos) ⋆ c.padU32A)
        (nvM4BlockU32A.At c.pFlags) := by
    have h1 := m4_nv_arr_pad_p (t := i32) (a := c.pFlags) (xs := s.core.flags) 12 4 rfl (by decide)
    have h2 := m4_nv_arr_pad_p (t := i32) (a := c.pLevel) (xs := s.core.lvl) 12 4 rfl (by decide)
    have h3 := m4_nv_arr_pad_p (t := i32) (a := c.pReason) (xs := s.core.rsns) 12 4 rfl (by decide)
    have h4 := m4_nv_arr_pad_p (t := i32) (a := c.pTrail) (xs := s.core.trl) 12 4 rfl (by decide)
    have h5 := m4_nv_arr_pad_p (t := i32) (a := c.pTrailPos) (xs := s.core.trail_pos) 12 4 rfl
      (by decide)
    have h12 := m4_nv_join h1 h2 (by decide) (by decide)
    have h123 := m4_nv_join h12 h3 (by decide) (by decide)
    have h1234 := m4_nv_join h123 h4 (by decide) (by decide)
    exact m4_nv_reorg (m4_nv_join h1234 h5 (by decide) (by decide)) fun _ hm => by
      unfold FullCfg.padU32A; rw [hu4, hmv12]; exact sep_ac hm
  have hU32B : nvM4BlockU32B.length = 80 ∧
      ((array (t := i32) c.pTmp s.core.tmp ⋆ array (t := i32) c.pMinClr s.core.min_clr) ⋆
        (array (t := i32) c.pHeap s.scratch.heap ⋆ array (t := i32) c.pPos s.scratch.pos ⋆
         array (t := i32) c.pShrinkStk s.scratch.shrink_stk) ⋆ c.padU32B)
        (nvM4BlockU32B.At c.pTmp) := by
    have h1 := m4_nv_arr_pad_p (t := i32) (a := c.pTmp) (xs := s.core.tmp) 12 4 rfl (by decide)
    have h2 := m4_nv_arr_pad_p (t := i32) (a := c.pHeap) (xs := s.scratch.heap) 12 4 rfl (by decide)
    have h3 := m4_nv_arr_pad_p (t := i32) (a := c.pPos) (xs := s.scratch.pos) 12 4 rfl (by decide)
    have h4 := m4_nv_arr_pad_p (t := i32) (a := c.pMinClr) (xs := s.core.min_clr) 12 4 rfl
      (by decide)
    have h5 := m4_nv_arr_pad_p (t := i32) (a := c.pShrinkStk) (xs := s.scratch.shrink_stk) 12 4 rfl
      (by decide)
    have h12 := m4_nv_join h1 h2 (by decide) (by decide)
    have h123 := m4_nv_join h12 h3 (by decide) (by decide)
    have h1234 := m4_nv_join h123 h4 (by decide) (by decide)
    exact m4_nv_reorg (m4_nv_join h1234 h5 (by decide) (by decide)) fun _ hm => by
      unfold FullCfg.padU32B; rw [hu4, hmv12]; exact sep_ac hm
  have hU32C : nvM4BlockU32C.length = 80 ∧
      ((array (t := i32) c.pQPrev s.scratch.q_prev ⋆
        array (t := i32) c.pQNext s.scratch.q_next ⋆
        array (t := i32) c.pQStamp s.scratch.q_stamp) ⋆
        (array (t := i32) c.pFrameTrail s.core.frame_trail ⋆
         array (t := i32) c.pFrameDec s.core.frame_dec) ⋆ c.padU32C)
        (nvM4BlockU32C.At c.pQPrev) := by
    have h1 := m4_nv_arr_pad_p (t := i32) (a := c.pQPrev) (xs := s.scratch.q_prev) 12 4 rfl
      (by decide)
    have h2 := m4_nv_arr_pad_p (t := i32) (a := c.pQNext) (xs := s.scratch.q_next) 12 4 rfl
      (by decide)
    have h3 := m4_nv_arr_pad_p (t := i32) (a := c.pQStamp) (xs := s.scratch.q_stamp) 12 4 rfl
      (by decide)
    have h4 := m4_nv_arr_pad_p (t := i32) (a := c.pFrameTrail) (xs := s.core.frame_trail) 16 0 rfl
      (by decide)
    have h5 := m4_nv_arr_pad_p (t := i32) (a := c.pFrameDec) (xs := s.core.frame_dec) 16 0 rfl
      (by decide)
    have h12 := m4_nv_join h1 h2 (by decide) (by decide)
    have h123 := m4_nv_join h12 h3 (by decide) (by decide)
    have h1234 := m4_nv_join h123 h4 (by decide) (by decide)
    exact m4_nv_reorg (m4_nv_join h1234 h5 (by decide) (by decide)) fun _ hm => by
      unfold FullCfg.padU32C; rw [hu4, hu8, hmv12, hmv16]; exact sep_ac hm
  have hWvec : nvM4BlockWvec.length = 240 ∧
      ((array (t := i32) c.pWvec s.core.wvec ⋆ array (t := i32) c.pRepr s.core.repr) ⋆
        FullScrWksArrs c s.scratch ⋆
        (array64 c.pScore s.scratch.score ⋆ array64 c.pSimSig s.scratch.sim_sig))
        (nvM4BlockWvec.At c.pWvec) := by
    have h1 := m4_nv_arr_p (t := i32) (a := c.pWvec) (xs := s.core.wvec) 48 rfl (by decide)
    have h2 := m4_nv_arr_p (t := i32) (a := c.pRepr) (xs := s.core.repr) 24 rfl (by decide)
    have h3 := m4_nv_arr_p (t := i32) (a := c.pWsort) (xs := s.scratch.wsort) 24 rfl (by decide)
    have h4 := m4_nv_arr_p (t := i32) (a := c.pWorkStk1) (xs := s.scratch.work_stk1) 24 rfl
      (by decide)
    have h5 := m4_nv_arr_p (t := i32) (a := c.pWorkStk2) (xs := s.scratch.work_stk2) 24 rfl
      (by decide)
    have h6 := m4_nv_arr_p (t := i32) (a := c.pTarjanMark) (xs := s.scratch.tarjan_mark) 24 rfl
      (by decide)
    have h7 := m4_nv_arr_p (t := i32) (a := c.pTarjanReach) (xs := s.scratch.tarjan_reach) 24 rfl
      (by decide)
    have h8 := m4_nv_arr64_p (a := c.pScore) (xs := s.scratch.score) 24 rfl (by decide)
    have h9 := m4_nv_arr64_p (a := c.pSimSig) (xs := s.scratch.sim_sig) 24 rfl (by decide)
    have h12 := m4_nv_join h1 h2 (by decide) (by decide)
    have h123 := m4_nv_join h12 h3 (by decide) (by decide)
    have h1234 := m4_nv_join h123 h4 (by decide) (by decide)
    have h12345 := m4_nv_join h1234 h5 (by decide) (by decide)
    have h123456 := m4_nv_join h12345 h6 (by decide) (by decide)
    have h1234567 := m4_nv_join h123456 h7 (by decide) (by decide)
    have h12345678 := m4_nv_join h1234567 h8 (by decide) (by decide)
    exact m4_nv_reorg (m4_nv_join h12345678 h9 (by decide) (by decide)) fun _ hm => by
      unfold FullScrWksArrs; exact sep_ac hm
  have hTail : nvM4BlockTail.length = 892 ∧
      (array (t := i32) c.pMinStk s.core.min_stk ⋆
        (array (t := i32) c.pGlueUsed s.scratch.glue_used ⋆
         array (t := i32) c.pLastLearned s.scratch.last_learned) ⋆
        FullCoreDynArrs c s.core ⋆ FullScrDynArrs c s.scratch ⋆ region c.pSlack c.slack)
        (nvM4BlockTail.At c.pMinStk) := by
    have h1 := m4_nv_arr_p (t := i32) (a := c.pMinStk) (xs := s.core.min_stk) 32 rfl (by decide)
    have h2 := m4_nv_arr_p (t := i32) (a := c.pGlueUsed) (xs := s.scratch.glue_used) 256 rfl
      (by decide)
    have h3 := m4_nv_arr_p (t := i32) (a := c.pLastLearned) (xs := s.scratch.last_learned) 64 rfl
      (by decide)
    have h4 := m4_nv_arr_p (t := i32) (a := c.pArena) (xs := s.core.arena) 24 rfl (by decide)
    have h5 := m4_nv_arr_p (t := i32) (a := c.pWstk) (xs := s.core.wstk) 4 rfl (by decide)
    have h6 := m4_nv_arr_p (t := i32) (a := c.pDelayed) (xs := s.scratch.delayed) 0 rfl (by decide)
    have h7 := m4_nv_arr_p (t := i32) (a := c.pRedRefs) (xs := s.scratch.red_refs) 0 rfl (by decide)
    have h8 := m4_nv_arr_p (t := i32) (a := c.pExtendStk) (xs := s.scratch.extend_stk) 0 rfl
      (by decide)
    have h9 := m4_nv_arr_p (t := i32) (a := c.pScratchBuf) (xs := s.scratch.scratch_buf) 512 rfl
      (by decide)
    have h10 : (List.replicate 0 (0 : UInt8)).length = 0 ∧
        region c.pSlack c.slack ((List.replicate 0 0).At c.pSlack) :=
      ⟨rfl, ⟨List.replicate 0 0, by decide, rfl⟩⟩
    have h12 := m4_nv_join h1 h2 (by decide) (by decide)
    have h123 := m4_nv_join h12 h3 (by decide) (by decide)
    have h1234 := m4_nv_join h123 h4 (by decide) (by decide)
    have h12345 := m4_nv_join h1234 h5 (by decide) (by decide)
    have h123456 := m4_nv_join h12345 h6 (by decide) (by decide)
    have h1234567 := m4_nv_join h123456 h7 (by decide) (by decide)
    have h12345678 := m4_nv_join h1234567 h8 (by decide) (by decide)
    have h123456789 := m4_nv_join h12345678 h9 (by decide) (by decide)
    exact m4_nv_reorg (m4_nv_join h123456789 h10 (by decide) (by decide)) fun _ hm => by
      unfold FullCoreDynArrs FullScrDynArrs; exact sep_ac hm
  have h01 := m4_nv_join hHdr hBytes (by decide) (by decide)
  have h02 := m4_nv_join h01 hU32A (by decide) (by decide)
  have h03 := m4_nv_join h02 hU32B (by decide) (by decide)
  have h04 := m4_nv_join h03 hU32C (by decide) (by decide)
  have h05 := m4_nv_join h04 hWvec (by decide) (by decide)
  exact (m4_nv_reorg (m4_nv_join h05 hTail (by decide) (by decide)) fun _ hm => by
    unfold FullMem FullCoreArrays FullCoreU32A FullCoreU32B FullScratchArrays FullScrU32A
      FullScrMetaArrs FullCfg.pad
    exact sep_ac hm).2

theorem nvM4SparseMem_ok : FullMem nvM4Cfg nvM4SparseState nvM4SparseMem :=
  nvM4Mem_of_mode 0#64

theorem nvM4DenseMem_ok : FullMem nvM4Cfg nvM4DenseState nvM4DenseMem :=
  nvM4Mem_of_mode 1#64

private theorem nvM4_entails_024 :
    (cnfOfClauses [[0], [1]]).EntailsClause (cnfClause [0, 2, 4]) := by
  rw [CNF.entails_clause_def]; intro α hα
  have h0 : (cnfClause [0]).Sat α :=
    (CNF.sat_iff_all_mem_sat.mp hα) _ (CNF.Internal.mem_iff.mpr (by simp [cnfOfClauses]))
  rw [CNF.Clause.sat_iff_exists_mem_eq] at h0 ⊢
  obtain ⟨lit, hm, heq⟩ := h0
  refine ⟨lit, ?_, heq⟩
  rw [mem_cnfClause_iff] at hm ⊢; simp only [List.mem_cons, List.not_mem_nil, or_false] at hm ⊢
  exact Or.inl hm

private theorem nvM4_lengths (dm : BitVec 64) :
    ({ nvM4SparseState with core := { nvM4SparseState.core with dense_mode := dm } } :
      FullState).LengthsOk nvM4Cfg :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.zero_le _, Nat.zero_le _,
    Nat.zero_le _, Nat.zero_le _⟩,
   ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

private theorem nvM4_witness (b : Bool) :
    let dm : BitVec 64 := if b then 1#64 else 0#64
    FullWitnessInv nvM4Cfg nvM4F0 [[0], [1]]
      { nvM4SparseState.core with dense_mode := dm } := by
  cases b
  all_goals
    intro dm
    let k : FullCoreState := { nvM4SparseState.core with dense_mode := dm }
    have hrefs : fullArenaClauseRefsCore k = [0] := by
      unfold fullArenaClauseRefsCore; dsimp only [k, dm]; decide
    have hwat : ModeWatchesInv [[0], [1]] k := by
      unfold ModeWatchesInv
      first
        | (rw [ite_eq_left_of_eq_true _ _ (eq_true (by decide))]
           refine WatchesInv.of_slices (fun l hl => ?_) (fun l hl hp => ?_)
             (fun l1 _ h1 _ _ hp => ?_) (fun l hl => ?_)
           · dsimp only [k, dm, nvM4SparseState] at hl
             rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 ∨ l = 4 ∨ l = 5) with
               rfl | rfl | rfl | rfl | rfl | rfl <;> decide
           · dsimp only [k, dm, nvM4SparseState] at hl
             rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 ∨ l = 4 ∨ l = 5) with
               rfl | rfl | rfl | rfl | rfl | rfl <;>
               simp [fullWatchSizeCore, k, nvM4SparseState] at hp
           · dsimp only [k, dm, nvM4SparseState] at h1
             rcases (by omega : l1 = 0 ∨ l1 = 1 ∨ l1 = 2 ∨ l1 = 3 ∨ l1 = 4 ∨ l1 = 5) with
               rfl | rfl | rfl | rfl | rfl | rfl <;>
               simp [fullWatchSizeCore, k, nvM4SparseState] at hp
           · dsimp only [k, dm, nvM4SparseState] at hl
             rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 ∨ l = 4 ∨ l = 5) with
               rfl | rfl | rfl | rfl | rfl | rfl <;> exact WatchSliceOk.empty)
        | (rw [ite_eq_right_of_eq_false _ _ (eq_false (by decide))]
           refine DenseWatchesInv.of_slices (fun l hl => ?_) (fun l hl hp => ?_)
             (fun l1 _ h1 _ _ hp => ?_) (fun l hl => ?_)
           · dsimp only [k, dm, nvM4SparseState] at hl
             rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 ∨ l = 4 ∨ l = 5) with
               rfl | rfl | rfl | rfl | rfl | rfl <;> decide
           · dsimp only [k, dm, nvM4SparseState] at hl
             rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 ∨ l = 4 ∨ l = 5) with
               rfl | rfl | rfl | rfl | rfl | rfl <;>
               simp [fullWatchSizeCore, k, nvM4SparseState] at hp
           · dsimp only [k, dm, nvM4SparseState] at h1
             rcases (by omega : l1 = 0 ∨ l1 = 1 ∨ l1 = 2 ∨ l1 = 3 ∨ l1 = 4 ∨ l1 = 5) with
               rfl | rfl | rfl | rfl | rfl | rfl <;>
               simp [fullWatchSizeCore, k, nvM4SparseState] at hp
           · dsimp only [k, dm, nvM4SparseState] at hl
             rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 ∨ l = 4 ∨ l = 5) with
               rfl | rfl | rfl | rfl | rfl | rfl <;> exact DenseWatchSliceOk.empty)
    exact
      { ext_sound := ⟨(varsBoundedBool_iff 3 [[0], [1]]).mp rfl, id⟩
        inconsistent_sound := fun h => absurd rfl h
        arena := ⟨Or.inr (by decide),
          fun r hr => by
            rw [hrefs, List.mem_singleton] at hr; subst hr
            exact ⟨by decide, by decide, by decide, by decide,
              Or.inl (by dsimp only [k, dm]; decide)⟩,
          fun r hr hsh => by
            rw [hrefs, List.mem_singleton] at hr; subst hr
            exact absurd (by dsimp only [k, dm]; decide) hsh,
          fun r hr _ l hl => by
            rw [hrefs, List.mem_singleton] at hr; subst hr
            have hlits : fullArenaClauseLitsCore k 0 = [0, 2, 4] := rfl
            rw [hlits] at hl; simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
            rcases hl with rfl | rfl | rfl <;> decide,
          fun r hr _ => by
            rw [hrefs, List.mem_singleton] at hr; subst hr
            have hlits : fullArenaClauseLitsCore k 0 = [0, 2, 4] := rfl
            rw [hlits]; exact nvM4_entails_024⟩
        watches := hwat
        cur_level_le := Nat.le_refl 0
        trail_lits_lt := fun _ hi => by cases hi
        trail_vars_nodup := fun _ _ hi => by cases hi
        vals_domain := fun l hl => by
          dsimp only [nvM4SparseState] at hl
          rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 ∨ l = 4 ∨ l = 5) with
            rfl | rfl | rfl | rfl | rfl | rfl <;> exact Or.inl rfl
        vals_true_iff := fun l hl => by
          dsimp only [nvM4SparseState] at hl
          rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 ∨ l = 4 ∨ l = 5) with
            rfl | rfl | rfl | rfl | rfl | rfl <;>
            exact ⟨(fun h => by cases h), (fun ⟨_, hi, _⟩ => by cases hi)⟩
        vals_false_iff := fun l hl => by
          dsimp only [nvM4SparseState] at hl
          rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 ∨ l = 4 ∨ l = 5) with
            rfl | rfl | rfl | rfl | rfl | rfl <;>
            exact ⟨(fun h => by cases h), (fun ⟨_, hi, _⟩ => by cases hi)⟩
        lvl_le := fun _ hi => by cases hi
        dec_earliest := fun _ _ hi => by cases hi
        levels_inhabited := fun _ h1 h2 => by dsimp only [nvM4SparseState] at h2; omega
        level0_sound := fun _ hi => by cases hi
        trail_pos_inv := fun _ hi => by cases hi
        level0_rsn_none := fun _ hi => by cases hi
        frame_trail_lt := fun L hL => by
          dsimp only [nvM4SparseState] at hL; obtain rfl : L = 0 := by omega
          exact Nat.le_refl 0
        frame_trail_mono := fun L1 L2 hL12 hL2 => by
          dsimp only [nvM4SparseState] at hL2
          obtain rfl : L2 = 0 := by omega
          obtain rfl : L1 = 0 := by omega
          exact Nat.le_refl _
        frame_trail_before_lt := fun _ h1 h2 => by dsimp only [nvM4SparseState] at h2; omega
        frame_dec_lt := fun _ h1 h2 => by dsimp only [nvM4SparseState] at h2; omega
        reason_inv := fun _ hi => by cases hi
        reason_lit_mem := fun _ hi => by cases hi }

private theorem nvM4_marks (dm : BitVec 64) :
    FullLitMarksClear nvM4Cfg
      { nvM4SparseState with core := { nvM4SparseState.core with dense_mode := dm } } := by
  refine ⟨fun v hv => ?_, fun l hl => ?_⟩
  · dsimp only [nvM4Cfg] at hv
    rcases (by omega : v = 0 ∨ v = 1 ∨ v = 2) with rfl | rfl | rfl <;> rfl
  · dsimp only [nvM4Cfg] at hl
    rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 ∨ l = 4 ∨ l = 5) with
      rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

private theorem nvM4_nodup (b : Bool) :
    let dm : BitVec 64 := if b then 1#64 else 0#64
    FullArenaVarsNodup
      { nvM4SparseState with core := { nvM4SparseState.core with dense_mode := dm } } := by
  cases b
  all_goals
    intro dm r hr _
    have hrefs : fullArenaClauseRefs
        { nvM4SparseState with core := { nvM4SparseState.core with dense_mode := dm } } = [0] := by
      unfold fullArenaClauseRefs fullArenaClauseRefsCore; dsimp only [dm]; decide
    rw [hrefs, List.mem_singleton] at hr; subst hr; dsimp only [dm]; decide

private theorem nvM4_ext (dm : BitVec 64) :
    FullExtScratchOk nvM4Cfg
      { nvM4SparseState with core := { nvM4SparseState.core with dense_mode := dm } } :=
  ⟨FullLastLearnedWf.of_cleared fun i hi => by
    simp only [nvM4SparseState, nvM4Scratch, List.getElem?_replicate, show i < 16 by omega,
      ↓reduceIte, Option.getD_some], Nat.le_refl 0⟩

theorem nvM4Sparse_invW : FullSparseInvW nvM4Cfg nvM4F0 [[0], [1]] nvM4SparseState :=
  ⟨nvM4_lengths 0#64, nvM4_witness false, nvM4_marks 0#64,
    nvM4_nodup false, nvM4_ext 0#64, rfl⟩

theorem nvM4Dense_invW : FullDenseInvW nvM4Cfg nvM4F0 [[0], [1]] nvM4DenseState :=
  ⟨nvM4_lengths 1#64, nvM4_witness true, nvM4_marks 1#64,
    nvM4_nodup true, nvM4_ext 1#64, rfl, by decide⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_viv_sort_noccs_m4`. -/
theorem nv_m4_viv_sort_noccs :
    Func.wp m4VivBceEnv full_viv_sort_noccs_m4_body (nvM4Cfg.hdr, 3#32, ()) nvM4SparseMem
      (fun () m' => ∃ tmp',
        tmp'.length = 3 ∧ (tmp'.take 3).Perm (nvM4SparseState.core.tmp.take 3) ∧
        nvM4F0.Unsat ∧
        FullMem nvM4Cfg
          { nvM4SparseState with core := { nvM4SparseState.core with tmp := tmp' } } m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvM4Cfg nvM4SparseState ⋆ emp) nvM4SparseMem := by
    rw [sep_emp]; exact nvM4SparseMem_ok
  exact m4_viv_sort_noccs_impl.2 _ _ _ _
    ⟨nvM4Cfg, nvM4SparseState, emp, rfl, nvM4_lengths 0#64, by decide,
      (fun k hk => by
        rw [show (3#32 : BitVec 32).toNat = 3 from rfl] at hk
        rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl <;> decide),
      hm, fun tmp' m' hlen hperm _ hm' => by
        rw [sep_emp] at hm'; exact ⟨tmp', hlen, hperm, nvM4F0_unsat, hm'⟩⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_viv_has_l0_m4`. -/
theorem nv_m4_viv_has_l0 :
    Func.wp m4VivBceEnv full_viv_has_l0_m4_body (nvM4Cfg.hdr, 0#32, 3#32, ()) nvM4SparseMem
      (fun (_r, ()) m' => nvM4F0.Unsat ∧ FullMem nvM4Cfg nvM4SparseState m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvM4Cfg nvM4SparseState ⋆ emp) nvM4SparseMem := by
    rw [sep_emp]; exact nvM4SparseMem_ok
  exact m4_viv_has_l0_impl.2 _ _ _ _
    ⟨nvM4Cfg, nvM4F0, [[0], [1]], nvM4SparseState, emp, rfl, nvM4Sparse_invW,
      List.mem_singleton.mpr rfl, rfl, rfl, hm, fun _ => ⟨nvM4F0_unsat, nvM4SparseMem_ok⟩⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_viv_l0_simp_m4`. -/
theorem nv_m4_viv_l0_simp :
    Func.wp m4VivBceEnv full_viv_l0_simp_m4_body (nvM4Cfg.hdr, 0#32, 3#32, ()) nvM4SparseMem
      (fun (r, ()) m' => ∃ s',
        FullSparseInvW nvM4Cfg nvM4F0 [[0], [1]] s' ∧
        (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) ∧ nvM4F0.Unsat ∧ FullMem nvM4Cfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvM4Cfg nvM4SparseState ⋆ emp) nvM4SparseMem := by
    rw [sep_emp]; exact nvM4SparseMem_ok
  exact m4_viv_l0_simp_impl.2 _ _ _ _
    ⟨nvM4Cfg, nvM4F0, [[0], [1]], nvM4SparseState, emp, rfl, nvM4Sparse_invW,
      List.mem_singleton.mpr rfl, rfl, rfl, hm,
      fun r s' m' hsp _ _ _ _ hr _ _ hm' => by
        rw [sep_emp] at hm'; exact ⟨s', hsp, hr, nvM4F0_unsat, hm'⟩⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_viv_reuse_prefix_m4`. -/
theorem nv_m4_viv_reuse_prefix :
    Func.wp m4VivBceEnv full_viv_reuse_prefix_m4_body (nvM4Cfg.hdr, 0#32, 3#32, ()) nvM4SparseMem
      (fun () m' => ∃ s',
        FullSparseInvW nvM4Cfg nvM4F0 [[0], [1]] s' ∧
        s'.core.tmp = nvM4SparseState.core.tmp ∧
        nvM4F0.Unsat ∧ FullMem nvM4Cfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvM4Cfg nvM4SparseState ⋆ emp) nvM4SparseMem := by
    rw [sep_emp]; exact nvM4SparseMem_ok
  exact m4_viv_reuse_prefix_impl.2 _ _ _ _
    ⟨nvM4Cfg, nvM4F0, [[0], [1]], nvM4SparseState, emp, rfl, nvM4Sparse_invW, by decide,
      (fun k hk => by
        rw [show (3#32 : BitVec 32).toNat = 3 from rfl] at hk
        rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl <;> decide),
      hm, fun s' m' hsp _ _ _ _ _ htmp _ hm' => by
        rw [sep_emp] at hm'; exact ⟨s', hsp, htmp, nvM4F0_unsat, hm'⟩⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_viv_finish_m4`. -/
theorem nv_m4_viv_finish :
    Func.wp m4VivBceEnv full_viv_finish_m4_body
      (nvM4Cfg.hdr, 0#32, 3#32, false, 0xFFFFFFFF#32, false, ()) nvM4SparseMem
      (fun (r, ()) m' => ∃ s',
        FullSparseInvW nvM4Cfg nvM4F0 [[0], [1]] s' ∧
        (r = 1#64 ∨ r = 2#64 ∨ r = 20#64) ∧ nvM4F0.Unsat ∧ FullMem nvM4Cfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvM4Cfg nvM4SparseState ⋆ emp) nvM4SparseMem := by
    rw [sep_emp]; exact nvM4SparseMem_ok
  exact m4_viv_finish_impl.2 _ _ _ _
    ⟨nvM4Cfg, nvM4F0, [[0], [1]], nvM4SparseState, emp, rfl, nvM4Sparse_invW, by decide,
      List.mem_singleton.mpr rfl, rfl, rfl, (fun h => by cases h), (fun _ h => absurd rfl h),
      (fun _ _ h => by cases h), hm,
      fun r s' m' hsp _ _ _ _ hr _ hm' => by
        rw [sep_emp] at hm'; exact ⟨s', hsp, hr, nvM4F0_unsat, hm'⟩⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_viv_clause_m4`. -/
theorem nv_m4_viv_clause :
    Func.wp m4VivBceEnv full_viv_clause_m4_body (nvM4Cfg.hdr, 0#32, ()) nvM4SparseMem
      (fun (r, ()) m' => ∃ s',
        FullSparseInvW nvM4Cfg nvM4F0 [[0], [1]] s' ∧
        (r = 1#64 ∨ r = 2#64 ∨ r = 20#64) ∧ nvM4F0.Unsat ∧ FullMem nvM4Cfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvM4Cfg nvM4SparseState ⋆ emp) nvM4SparseMem := by
    rw [sep_emp]; exact nvM4SparseMem_ok
  exact m4_viv_clause_impl.2 _ _ _ _
    ⟨nvM4Cfg, nvM4F0, [[0], [1]], nvM4SparseState, emp, rfl, nvM4Sparse_invW,
      List.mem_singleton.mpr rfl, hm,
      fun r s' m' hsp _ _ _ _ hr _ hm' => by
        rw [sep_emp] at hm'; exact ⟨s', hsp, hr, nvM4F0_unsat, hm'⟩⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_viv_sort_sched_m4`. -/
theorem nv_m4_viv_sort_sched :
    Func.wp m4VivBceEnv full_viv_sort_sched_m4_body (nvM4Cfg.hdr, 0#64, ()) nvM4SparseMem
      (fun () m' => ∃ rr',
        rr'.length = 0 ∧ nvM4F0.Unsat ∧
        FullMem nvM4Cfg
          { nvM4SparseState with scratch := { nvM4SparseState.scratch with red_refs := rr' } } m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvM4Cfg nvM4SparseState ⋆ emp) nvM4SparseMem := by
    rw [sep_emp]; exact nvM4SparseMem_ok
  exact m4_viv_sort_sched_impl.2 _ _ _ _
    ⟨nvM4Cfg, nvM4SparseState, emp, rfl, nvM4_lengths 0#64, by decide,
      fun _ hk => by simp at hk, hm, fun rr' m' hlen _ hm' => by
        rw [sep_emp] at hm'; exact ⟨rr', hlen, nvM4F0_unsat, hm'⟩⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_viv_tier_match_m4`. -/
theorem nv_m4_viv_tier_match :
    Func.wp m4VivBceEnv full_viv_tier_match_m4_body (nvM4Cfg.hdr, 0#32, 0#64, ()) nvM4SparseMem
      (fun (_r, ()) m' => nvM4F0.Unsat ∧ FullMem nvM4Cfg nvM4SparseState m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvM4Cfg nvM4SparseState ⋆ emp) nvM4SparseMem := by
    rw [sep_emp]; exact nvM4SparseMem_ok
  exact m4_viv_tier_match_impl.2 _ _ _ _
    ⟨nvM4Cfg, nvM4SparseState, emp, rfl, hm, fun _ => ⟨nvM4F0_unsat, nvM4SparseMem_ok⟩⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_viv_collect_m4`. -/
theorem nv_m4_viv_collect :
    Func.wp m4VivBceEnv full_viv_collect_m4_body (nvM4Cfg.hdr, 0#64, ()) nvM4SparseMem
      (fun (bn, ()) m' => ∃ tr' rr',
        bn = 0#64 ∧ tr'.length = 6 ∧ rr'.length = 0 ∧ nvM4F0.Unsat ∧
        FullMem nvM4Cfg
          { nvM4SparseState with
            scratch := { nvM4SparseState.scratch with tarjan_reach := tr', red_refs := rr' } } m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvM4Cfg nvM4SparseState ⋆ emp) nvM4SparseMem := by
    rw [sep_emp]; exact nvM4SparseMem_ok
  exact m4_viv_collect_impl.2 _ _ _ _
    ⟨nvM4Cfg, nvM4F0, nvM4SparseState, emp, rfl, nvM4Sparse_invW.toSparse, hm,
      fun bn tr' rr' m' h3bn htr hrr _ hm' => by
        rw [sep_emp] at hm'
        have hbn0 : bn = 0#64 := BitVec.eq_of_toNat_eq (by
          dsimp only [nvM4Cfg] at h3bn
          rw [show (0#64 : BitVec 64).toNat = 0 from rfl]; omega)
        exact ⟨tr', rr', hbn0, htr, hrr, nvM4F0_unsat, hm'⟩⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_viv_keys_m4`. -/
theorem nv_m4_viv_keys :
    Func.wp m4VivBceEnv full_viv_keys_m4_body (nvM4Cfg.hdr, 0#64, ()) nvM4SparseMem
      (fun () m' => ∃ rr',
        rr'.length = 0 ∧ nvM4F0.Unsat ∧
        FullMem nvM4Cfg
          { nvM4SparseState with scratch := { nvM4SparseState.scratch with red_refs := rr' } } m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvM4Cfg nvM4SparseState ⋆ emp) nvM4SparseMem := by
    rw [sep_emp]; exact nvM4SparseMem_ok
  exact m4_viv_keys_impl.2 _ _ _ _
    ⟨nvM4Cfg, nvM4F0, nvM4SparseState, emp, rfl, nvM4Sparse_invW.toSparse, by decide,
      fun _ hk => by simp at hk, hm, fun rr' m' hlen _ hm' => by
        rw [sep_emp] at hm'; exact ⟨rr', hlen, nvM4F0_unsat, hm'⟩⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_viv_clear_tier_m4`. -/
theorem nv_m4_viv_clear_tier :
    Func.wp m4VivBceEnv full_viv_clear_tier_m4_body (nvM4Cfg.hdr, 0#64, ()) nvM4SparseMem
      (fun () m' => ∃ s',
        FullSparseInv nvM4Cfg nvM4F0 s' ∧ s'.core.cur_level = 0 ∧ nvM4F0.Unsat ∧
        FullMem nvM4Cfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvM4Cfg nvM4SparseState ⋆ emp) nvM4SparseMem := by
    rw [sep_emp]; exact nvM4SparseMem_ok
  exact m4_viv_clear_tier_impl.2 _ _ _ _
    ⟨nvM4Cfg, nvM4F0, nvM4SparseState, emp, rfl, nvM4Sparse_invW.toSparse, rfl, hm,
      fun s' m' hsp hcl0 _ hm' => by rw [sep_emp] at hm'; exact ⟨s', hsp, hcl0, nvM4F0_unsat, hm'⟩⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_vivify_m4`. -/
theorem nv_m4_vivify :
    Func.wp m4VivBceEnv full_vivify_m4_body (nvM4Cfg.hdr, 0#64, 10#64, ()) nvM4SparseMem
      (fun (r, ()) m' => ∃ s',
        FullSparseInv nvM4Cfg nvM4F0 s' ∧ s'.core.cur_level = 0 ∧ s'.core.probing = 0#64 ∧
        (r = 1#64 ∨ r = 20#64) ∧ nvM4F0.Unsat ∧ FullMem nvM4Cfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvM4Cfg nvM4SparseState ⋆ emp) nvM4SparseMem := by
    rw [sep_emp]; exact nvM4SparseMem_ok
  exact m4_vivify_impl.2 _ _ _ _
    ⟨nvM4Cfg, nvM4F0, nvM4SparseState, emp, rfl, nvM4Sparse_invW.toSparse, hm,
      fun r s' m' hsp _ _ hnz _ hr _ hm' => by
        obtain ⟨hcl0, hpr0⟩ := hnz (by decide)
        rw [sep_emp] at hm'; exact ⟨s', hsp, hcl0, hpr0, hr, nvM4F0_unsat, hm'⟩⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_bce_side_m4`. -/
theorem nv_m4_bce_side :
    Func.wp m4VivBceEnv full_bce_side_m4_body (nvM4Cfg.hdr, 1#32, 64#32, 0#32, 0#32, 0#32, ())
      nvM4DenseMem
      (fun (rem, ()) m' => ∃ s',
        FullDenseInvW nvM4Cfg nvM4F0 [[0], [1]] s' ∧ rem = 0#32 ∧ nvM4F0.Unsat ∧
        FullMem nvM4Cfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvM4Cfg nvM4DenseState ⋆ emp) nvM4DenseMem := by
    rw [sep_emp]; exact nvM4DenseMem_ok
  exact m4_bce_side_impl.2 _ _ _ _
    ⟨nvM4Cfg, nvM4F0, [[0], [1]], nvM4DenseState, emp, rfl, nvM4Dense_invW, by decide,
      by decide, by decide, Or.inr (by decide), (fun _ hi => by cases hi),
      (fun _ hj => by cases hj), hm, fun rem s' m' hdn _ _ hrem _ _ _ hm' => by
        rw [sep_emp] at hm'
        have hrem0 : rem = 0#32 := BitVec.eq_of_toNat_eq (Nat.le_zero.mp hrem)
        exact ⟨s', hdn, hrem0, nvM4F0_unsat, hm'⟩⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_bce_pair_m4`. -/
theorem nv_m4_bce_pair :
    Func.wp m4VivBceEnv full_bce_pair_m4_body (nvM4Cfg.hdr, 0#32, 0#32, 0#32, ()) nvM4DenseMem
      (fun () m' => ∃ s',
        FullDenseInvW nvM4Cfg nvM4F0 [[0], [1]] s' ∧ nvM4F0.Unsat ∧ FullMem nvM4Cfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvM4Cfg nvM4DenseState ⋆ emp) nvM4DenseMem := by
    rw [sep_emp]; exact nvM4DenseMem_ok
  exact m4_bce_pair_impl.2 _ _ _ _
    ⟨nvM4Cfg, nvM4F0, [[0], [1]], nvM4DenseState, emp, rfl, nvM4Dense_invW, by decide, by decide,
      by decide, by decide, (fun _ hi => by cases hi), (fun _ hj => by cases hj), hm,
      fun s' m' hdn _ _ hm' => by rw [sep_emp] at hm'; exact ⟨s', hdn, nvM4F0_unsat, hm'⟩⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_bce_var_m4`. -/
theorem nv_m4_bce_var :
    Func.wp m4VivBceEnv full_bce_var_m4_body (nvM4Cfg.hdr, 0#32, ()) nvM4DenseMem
      (fun () m' => ∃ s',
        FullDenseInvW nvM4Cfg nvM4F0 [[0], [1]] s' ∧ nvM4F0.Unsat ∧ FullMem nvM4Cfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvM4Cfg nvM4DenseState ⋆ emp) nvM4DenseMem := by
    rw [sep_emp]; exact nvM4DenseMem_ok
  exact m4_bce_var_impl.2 _ _ _ _
    ⟨nvM4Cfg, nvM4F0, [[0], [1]], nvM4DenseState, emp, rfl, nvM4Dense_invW, by decide, hm,
      fun s' m' hdn _ _ hm' => by rw [sep_emp] at hm'; exact ⟨s', hdn, nvM4F0_unsat, hm'⟩⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_bce_m4`. -/
theorem nv_m4_bce :
    Func.wp m4VivBceEnv full_bce_m4_body (nvM4Cfg.hdr, 10#64, ()) nvM4SparseMem
      (fun (r, ()) m' => ∃ s',
        FullSparseInv nvM4Cfg nvM4F0 s' ∧ s'.core.cur_level = 0 ∧
        (r = 1#64 ∨ r = 20#64) ∧ nvM4F0.Unsat ∧ FullMem nvM4Cfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvM4Cfg nvM4SparseState ⋆ emp) nvM4SparseMem := by
    rw [sep_emp]; exact nvM4SparseMem_ok
  exact m4_bce_impl.2 _ _ _ _
    ⟨nvM4Cfg, nvM4F0, nvM4SparseState, emp, rfl, nvM4Sparse_invW.toSparse, rfl, hm,
      fun r s' m' hsp hcl0 _ hr _ hm' => by
        rw [sep_emp] at hm'; exact ⟨s', hsp, hcl0, hr, nvM4F0_unsat, hm'⟩⟩

end ConcreteNonVacuity

end LeanQbe.T.Examples.Kissat.FullM4VivBce
