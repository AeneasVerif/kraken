module

public import LeanQbe.T.Examples.Kissat.FullProbeTransLemmas4

/-!
# Kissat `D-Full` Probe Propagation & HBR Flush Proofs (`Stage 4`, Part 5)

Exports the parametric `(Γ : Env)` `Func.wp` proofs for `Full3.lean` #11–13:
1. `full_probe_prop_lit_ext_wp` / `full_probe_prop_lit_wp`
2. `full_probe_prop_ext_wp` / `full_probe_prop_wp`
3. `full_probe_flush_hbr_wp`
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test
open FullProbeTransSpecs FullProbeTransHelpers
open scoped FullArenaTactics FullProbeTransTactics

section LocalHelpers

private theorem pt_vals_ne_ff_of_sgt_or_zero {vals : List (BitVec 8)} {i : Nat}
    (hi : i < vals.length) (hv : vals[i]?.getD 0#8 = 0xFF#8) :
    ((vals[i]'hi).signExtend 32).slt 0#32 = true := by
  rw [List.getElem?_eq_getElem hi, Option.getD_some] at hv; rw [hv]; decide

private theorem entails_bin_swap {F : CNF Nat} {a b : Nat}
    (h : F.EntailsClause (cnfClause [a, b])) : F.EntailsClause (cnfClause [b, a]) := by
  rw [CNF.entails_clause_def] at h ⊢
  intro α hα
  obtain ⟨l, hl, hsat⟩ := (clause_sat_cnfClause_iff α _).mp (h α hα)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  exact (clause_sat_cnfClause_iff α _).mpr ⟨l, by simp [hl.symm], hsat⟩

private theorem pt_vals_eq_1_of_sgt' {vals : List (BitVec 8)} {i : Nat} (hi : i < vals.length)
    (hdom : vals[i]?.getD 0#8 = 0#8 ∨ vals[i]?.getD 0#8 = 1#8 ∨ vals[i]?.getD 0#8 = 0xFF#8)
    (hsgt : (0#32).slt ((vals[i]'hi).signExtend 32) = true) : vals[i]?.getD 0#8 = 1#8 := by
  rw [List.getElem?_eq_getElem hi, Option.getD_some] at hdom ⊢; exact (i8_vals_sgt0 hdom).mp hsgt

private theorem bv32_mask7f_toNat_eq {x : BitVec 32} (hx : x.toNat < 2 ^ 31) :
    (x &&& 0x7FFFFFFF#32).toNat = x.toNat :=
  bv32_mask7f_toNat_lt (by omega)

end LocalHelpers

/-! ## 1. `full_probe_prop_lit_ext_wp` & `full_probe_prop_lit_wp` -/

theorem full_probe_prop_lit_ext_wp (Γ : Env)
    (hFindRepl : ∀ args m Q X, fullFindReplSpec args m Q X →
      Γ "full_find_repl" [i64, i64] [i64] args m Q X)
    (hWatchPush : ∀ args m Q X, fullWatchPushSpec args m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] args m Q X)
    (hHbrDom : ∀ args m Q X, fullHbrDomSpec args m Q X →
      Γ "full_hbr_dom" [i64, i32, i32] [i32] args m Q X)
    (hAssignLvl : ∀ args m Q X, fullAssignLvlSpec args m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] args m Q X) :
    ∀ args m Q X, fullProbePropLitExtSpec args m Q X →
      Func.wp Γ full_probe_prop_lit_body args m Q X := by
  rintro ⟨h_arg, lit, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hlen0, hw0, hmrk0, hnd0, hext0, hdm0, hcl10, hoom0, hhbr0, hm0, hQ⟩
  have hcl0 := hlen0.core_ok
  have hmv := c.hmaxv; unfold dimacsBound at hmv
  have hcv_le := hcl0.cur_vars_le
  have hnl_eq : (BitVec.ofNat 64 s.core.cur_vars <<<
      ((1#32 : BitVec 32).signExtend 64).toNat).toNat = 2 * s.core.cur_vars := by
    rw [show ((1#32 : BitVec 32).signExtend 64).toNat = 1 from rfl,
      bv64_shl1_toNat (by rw [bv64_ofNat_toNat (by omega)]; omega),
      bv64_ofNat_toNat (by omega)]
  pt_steps_nogrp
  · exact hQ true s m hlen0 hw0 hmrk0 hnd0 hext0 hdm0 hcl10 rfl rfl rfl rfl
      (fullTrailRsnsExt_refl s.core) hhbr0 (fun hf => by cases hf) (fun _ => hoom0) hm0
  · have hnot_lt : (lit ^^^ 1#32).toNat < 2 * s.core.cur_vars := by
      pt_clear_big
      simp only [BitVec.toNat_xor, show (1#32).toNat = 1 from rfl] at *
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hc
      omega
    have hnot_vlt : (lit ^^^ 1#32).toNat < s.core.vals.length := by rw [hcl0.vals_len]; omega
    have hnot_v64 : ((lit ^^^ 1#32).setWidth 64).toNat < s.core.vals.length := by
      rw [bv_c0_zext32_64]; exact hnot_vlt
    pt_steps_nogrp
    · exact hQ true s m hlen0 hw0 hmrk0 hnd0 hext0 hdm0 hcl10 rfl rfl rfl rfl
        (fullTrailRsnsExt_refl s.core) hhbr0 (fun hf => by cases hf) (fun _ => hoom0) hm0
    · have hnot_false : s.core.vals[(lit ^^^ 1#32).toNat]?.getD 0#8 = 0xFF#8 := by
        apply pt_vals_eq_ff_of_nsge hnot_vlt (hw0.vals_domain _ hnot_lt)
        rw [Bool.not_eq_true]; pt_clear_big; exact hc
      have hnot_shl : ((lit ^^^ 1#32).setWidth 64 <<<
          ((1#32 : BitVec 32).signExtend 64).toNat).toNat = 2 * (lit ^^^ 1#32).toNat := by
        rw [show ((1#32 : BitVec 32).signExtend 64).toNat = 1 from rfl,
          bv64_shl1_toNat (by rw [bv_c0_zext32_64]; omega), bv_c0_zext32_64]
      have hwvec_i0 : ((lit ^^^ 1#32).setWidth 64 <<<
          ((1#32 : BitVec 32).signExtend 64).toNat).toNat < s.core.wvec.length := by
        rw [hcl0.wvec_len, hnot_shl]; omega
      have hwvec_i1 : (((lit ^^^ 1#32).setWidth 64 <<<
          ((1#32 : BitVec 32).signExtend 64).toNat) + 1#64).toNat < s.core.wvec.length := by
        rw [hcl0.wvec_len, bv64_add1_toNat (by rw [hnot_shl]; omega), hnot_shl]; omega
      pt_steps_nogrp
      · exact hQ true s m hlen0 hw0 hmrk0 hnd0 hext0 hdm0 hcl10 rfl rfl rfl rfl
          (fullTrailRsnsExt_refl s.core) hhbr0 (fun hf => by cases hf) (fun _ => hoom0) hm0
      · have hsz_pos : 0 < fullWatchSizeCore s.core (lit ^^^ 1#32).toNat := by
          unfold fullWatchSizeCore
          have hidx_eq : 2 * (lit ^^^ 1#32).toNat + 1 = (2 * (lit.toNat ^^^ 1) + 1) % 2 ^ 64 := by
            rw [show (lit ^^^ 1#32).toNat = lit.toNat ^^^ 1 from rfl, Nat.mod_eq_of_lt (by omega)]
          have hw_lt : 2 * (lit ^^^ 1#32).toNat + 1 < s.core.wvec.length := by
            rw [hcl0.wvec_len]; omega
          have heq_w : s.core.wvec[2 * (lit ^^^ 1#32).toNat + 1]'hw_lt =
              s.core.wvec[(2 * (lit.toNat ^^^ 1) + 1) % 2 ^ 64]'(by
                rw [← hidx_eq]; exact hw_lt) := by congr 1
          have hne : (s.core.wvec[2 * (lit ^^^ 1#32).toNat + 1]'hw_lt).setWidth 64 ≠ 0#64 := by
            rw [heq_w]; pt_clear_big; exact hc
          have hto : ((s.core.wvec[2 * (lit ^^^ 1#32).toNat + 1]'hw_lt).setWidth 64).toNat ≠
              0 := fun h0 => hne (BitVec.eq_of_toNat_eq (by simpa using h0))
          rw [bv_c0_zext32_64] at hto
          rw [List.getElem?_eq_getElem hw_lt, Option.getD_some]
          exact Nat.pos_of_ne_zero hto
        have hwat0 : WatchesInv F_cur s.core := by
          have hw_w := hw0.watches; simp only [ModeWatchesInv, hdm0, ↓reduceIte] at hw_w
          exact hw_w
        have hsplit0 := FullSplitWatchesInv.init hnot_lt hwat0 hsz_pos
        have h_off_eq : (s.core.wvec[((lit ^^^ 1#32).setWidth 64 <<<
            ((1#32 : BitVec 32).signExtend 64).toNat).toNat]'hwvec_i0).setWidth 64 =
            BitVec.ofNat 64 (fullWatchOffCore s.core (lit ^^^ 1#32).toNat) := by
          apply BitVec.eq_of_toNat_eq; unfold fullWatchOffCore
          rw [bv_c0_zext32_64, bv64_ofNat_toNat (Nat.lt_trans (BitVec.isLt _) (by decide)),
            ← hnot_shl, List.getElem?_eq_getElem hwvec_i0, Option.getD_some]
        have h_sz_eq : (s.core.wvec[(((lit ^^^ 1#32).setWidth 64 <<<
            ((1#32 : BitVec 32).signExtend 64).toNat) + 1#64).toNat]'hwvec_i1).setWidth 64 =
            BitVec.ofNat 64 (fullWatchSizeCore s.core (lit ^^^ 1#32).toNat) := by
          apply BitVec.eq_of_toNat_eq; unfold fullWatchSizeCore
          have hwv1_eq : (((lit ^^^ 1#32).setWidth 64 <<<
              ((1#32 : BitVec 32).signExtend 64).toNat) + 1#64).toNat =
              2 * (lit ^^^ 1#32).toNat + 1 := by
            rw [bv64_add1_toNat (by rw [hnot_shl]; omega), hnot_shl]
          rw [bv_c0_zext32_64, bv64_ofNat_toNat (Nat.lt_trans (BitVec.isLt _) (by decide)),
            ← hwv1_eq, List.getElem?_eq_getElem hwvec_i1, Option.getD_some]
        refine wp_join_group (propLitTailInv c F0 F_cur s R (lit ^^^ 1#32))
          (fun _ (off_v, p_v, q_v, end_v, confl_v, ()) ml htail =>
            propLitTail_wp hnot_lt hQ rfl rfl rfl rfl htail)
          (fun Jtail hJtail => ?_)
        pt_steps_nogrp
        refine wp_loop_inv
          (propLitMainInv c F0 F_cur s R (lit ^^^ 1#32))
          (fun (_off, p_v, _q, end_v, ()) _ => end_v.toNat - p_v.toNat)
          (fun Jloop hJloop => ?_)
          (fun Jloop (off_v, p_v, q_v, end_v, ()) ml hmain hJloop => ?_)
        · pt_steps_nogrp
          have hwcap := c.hwcap; unfold dimacsBound at hwcap
          have hbd0 := hwat0.layout.bounds _ hnot_lt
          have hwl0 := hcl0.wlen_le
          have hend0 : (BitVec.ofNat 64 (fullWatchOffCore s.core (lit ^^^ 1#32).toNat) +
              BitVec.ofNat 64 (fullWatchSizeCore s.core (lit ^^^ 1#32).toNat)).toNat =
              fullWatchOffCore s.core (lit ^^^ 1#32).toNat +
              fullWatchSizeCore s.core (lit ^^^ 1#32).toNat := by
            rw [BitVec.toNat_add, bv64_ofNat_toNat (by omega), bv64_ofNat_toNat (by omega),
              Nat.mod_eq_of_lt (by omega)]
          have h_off_c0 : (s.core.wvec[((lit ^^^ 1).setWidth 64 <<< 1).toNat]'
              (by simpa only [show ((1#32 : BitVec 32).signExtend 64).toNat = 1 from rfl,
                show ((1 : BitVec 32).signExtend 64).toNat = 1 from rfl,
                show (1#32 : BitVec 32) = 1 from rfl] using hwvec_i0)).setWidth 64 =
              BitVec.ofNat 64 (fullWatchOffCore s.core (lit ^^^ 1#32).toNat) := by
            simpa only [show ((1#32 : BitVec 32).signExtend 64).toNat = 1 from rfl,
              show ((1 : BitVec 32).signExtend 64).toNat = 1 from rfl,
              show (1#32 : BitVec 32) = 1 from rfl] using h_off_eq
          have h_sz_c0 : (s.core.wvec[((lit ^^^ 1).setWidth 64 <<< 1 + 1).toNat]'
              (by simpa only [show ((1#32 : BitVec 32).signExtend 64).toNat = 1 from rfl,
                show ((1 : BitVec 32).signExtend 64).toNat = 1 from rfl,
                show (1#32 : BitVec 32) = 1 from rfl,
                show (1#64 : BitVec 64) = 1 from rfl] using hwvec_i1)).setWidth 64 =
              BitVec.ofNat 64 (fullWatchSizeCore s.core (lit ^^^ 1#32).toNat) := by
            simpa only [show ((1#32 : BitVec 32).signExtend 64).toNat = 1 from rfl,
              show ((1 : BitVec 32).signExtend 64).toNat = 1 from rfl,
              show (1#32 : BitVec 32) = 1 from rfl,
              show (1#64 : BitVec 64) = 1 from rfl] using h_sz_eq
          rw [h_off_c0, h_sz_c0]
          have hoff0_lt : fullWatchOffCore s.core (lit ^^^ 1#32).toNat < 2 ^ 64 :=
            Nat.lt_trans (BitVec.isLt _) (by decide)
          exact hJloop (BitVec.ofNat 64 (fullWatchOffCore s.core (lit ^^^ 1#32).toNat),
            BitVec.ofNat 64 (fullWatchOffCore s.core (lit ^^^ 1#32).toNat),
            BitVec.ofNat 64 (fullWatchOffCore s.core (lit ^^^ 1#32).toNat),
            BitVec.ofNat 64 (fullWatchOffCore s.core (lit ^^^ 1#32).toNat) +
              BitVec.ofNat 64 (fullWatchSizeCore s.core (lit ^^^ 1#32).toNat), ())
            m ⟨s, hlen0, fullWitnessInv_to_nw hcl0 hw0, hmrk0, hnd0, hext0, hdm0, hcl10, rfl, rfl,
              rfl, rfl, fullTrailRsnsExt_refl s.core, hhbr0, by
                simpa only [bv64_ofNat_toNat hoff0_lt, hend0] using hsplit0,
              hnot_false, hoom0, hm0⟩
        · rcases hmain with ⟨st, hlen, hw_nw, hmrk, hnd, hext, hdm, hcl1, hcv, hfu, hlm, hws1, htr,
            hhbr, hsplit, hnf, hoom, hml⟩
          have hcl := hlen.core_ok
          have hnot_lt' : (lit ^^^ 1#32).toNat < 2 * st.core.cur_vars := hcv ▸ hnot_lt
          have hwcap := c.hwcap; unfold dimacsBound at hwcap
          have hbd_st := hsplit.layout.bounds _ hnot_lt'
          rw [hsplit.off_eq, hsplit.sz_eq] at hbd_st
          have hwl_st := hcl.wlen_le; have hwa_st := hcl.wstk_len_arr
          have hqp := hsplit.q_ge; have hqp_le := hsplit.q_le_p; have hpe := hsplit.p_le_end
          pt_steps_nogrp
          · have hp_lt : p_v.toNat < end_v.toNat := by pt_bound
            have hp_wa : p_v.toNat < st.core.wstk.length := by omega
            have hp1_64 : p_v.toNat + 1 < 2 ^ 64 := by omega
            have hp1_eq : (p_v + 1#64).toNat = p_v.toNat + 1 := bv64_add1_toNat hp1_64
            let w0_v := st.core.wstk[p_v.toNat]'hp_wa
            have hw0_get : st.core.wstk[p_v.toNat]? = some w0_v :=
              List.getElem?_eq_getElem hp_wa
            pt_steps_nogrp
            · have hflag_b : (w0_v &&& 0x80000000#32) ≠ 0#32 := by pt_clear_big; exact hc
              obtain ⟨hw0_ne, hot_lt, hent_b, hrem'⟩ :=
                watchSlice_inv_bin hsplit.rem_slice (by omega) hw0_get hflag_b
              have hq_wa : q_v.toNat < st.core.wstk.length := by omega
              have hp1_rev : p_v.toNat + 1 = (p_v + 1#64).toNat := hp1_eq.symm
              have hrem_p1 : end_v.toNat - (p_v.toNat + 1) = end_v.toNat - p_v.toNat - 1 := by omega
              have hrem_p1' : WatchSliceOk F_cur st.core (lit ^^^ 1#32).toNat (p_v.toNat + 1)
                  (end_v.toNat - (p_v.toNat + 1)) := by
                simpa only [hrem_p1] using hrem'
              have hsw_pre : FullSplitWatchesInv F_cur st.core (lit ^^^ 1#32).toNat off_v.toNat
                  q_v.toNat (p_v.toNat + 1) end_v.toNat :=
                { hsplit with q_le_p := by omega, p_le_end := by omega, rem_slice := hrem_p1' }
              have hsw_wb := FullSplitWatchesInv.write_bin (c := c) (p := p_v.toNat) (w0 := w0_v)
                hsw_pre hnot_lt' hqp_le hq_wa hflag_b hot_lt hent_b (by rw [hcv]; exact hcv_le)
              let st_wb : FullState :=
                { st with core := { st.core with wstk := st.core.wstk.set q_v.toNat w0_v } }
              have hlen_wb : st_wb.LengthsOk c :=
                ⟨{ hcl with wstk_len_arr := by simp [st_wb, hwa_st] }, hlen.scratch_ok⟩
              have hw_wb := fullWitnessInv_nw_upd_watches (s := st) (s' := st_wb) hw_nw
                hlen_wb.core_ok rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
              have hnd_wb := fullArenaVarsNodup_of_arena_eq hnd rfl rfl
              have hext_wb : FullExtScratchOk c st_wb :=
                ⟨fullLastLearnedWf_of_refs_eq hext.1 rfl rfl, hext.2⟩
              have htr_wb := fullTrailRsnsExt_trans htr (fullTrailRsnsExt_congr rfl rfl rfl rfl)
              have hhbr_wb := fullHbrBufOkW_congr hhbr rfl rfl
              have hq1_64 : q_v.toNat + 1 < 2 ^ 64 := by omega
              have hq1_eq : (q_v + 1#64).toNat = q_v.toNat + 1 := bv64_add1_toNat hq1_64
              have hsw_wb' : FullSplitWatchesInv F_cur st_wb.core (lit ^^^ 1#32).toNat
                  off_v.toNat (q_v + 1#64).toNat (p_v + 1#64).toNat end_v.toNat := by
                simpa only [st_wb, hq1_eq, hp1_eq] using hsw_wb
              pt_steps_nogrp
              · exact hJloop (off_v, p_v + 1#64, q_v + 1#64, end_v, ()) m
                  (by dsimp only; rw [hp1_eq]; omega)
                  ⟨st_wb, hlen_wb, hw_wb, hmrk, hnd_wb, hext_wb, hdm, hcl1, hcv, hfu, hlm, hws1,
                    htr_wb, hhbr_wb, hsw_wb', hnf, hoom, hm⟩
              · have hot_vlt : (w0_v &&& 2147483647#32).toNat < st_wb.core.vals.length := by
                  rw [hlen_wb.core_ok.vals_len]
                  have hle_wb := hlen_wb.core_ok.cur_vars_le
                  exact Nat.lt_of_lt_of_le hot_lt (by omega)
                have hot_v64 : ((w0_v &&& 2147483647#32).setWidth 64).toNat <
                    st_wb.core.vals.length := by rw [bv_c0_zext32_64]; exact hot_vlt
                pt_steps_nogrp
                · exact hJloop (off_v, p_v + 1#64, q_v + 1#64, end_v, ()) m
                    (by dsimp only; rw [hp1_eq]; omega)
                    ⟨st_wb, hlen_wb, hw_wb, hmrk, hnd_wb, hext_wb, hdm, hcl1, hcv, hfu, hlm,
                      hws1, htr_wb, hhbr_wb, hsw_wb', hnf, hoom, hm⟩
                · have hot_ff : st_wb.core.vals[(w0_v &&& 2147483647#32).toNat]?.getD 0#8 =
                      0xFF#8 := by
                    apply pt_vals_eq_ff_of_slt hot_vlt (hw_wb.vals_domain _ hot_lt)
                    pt_clear_big; exact hc
                  let st_c : FullState := { st_wb with core := { st_wb.core with
                    confl_type := 1#64, confl_lit0 := (lit ^^^ 1#32).setWidth 64,
                    confl_lit1 := (w0_v &&& 2147483647#32).setWidth 64 } }
                  have hlen_c : st_c.LengthsOk c :=
                    ⟨{ hlen_wb.core_ok with }, hlen_wb.scratch_ok⟩
                  have hw_c := fullWitnessInv_nw_upd_watches (s := st_wb) (s' := st_c) hw_wb
                    hlen_c.core_ok rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
                  have hconfl_ok : FullConflictOkW F_cur st_c := by
                    refine Or.inl ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
                    · dsimp [st_c]; rw [bv_c0_zext32_64]; exact hnot_lt'
                    · dsimp [st_c]; rw [bv_c0_zext32_64]; exact hot_lt
                    · dsimp [st_c]; rw [bv_c0_zext32_64]; exact hnf
                    · dsimp [st_c]; rw [bv_c0_zext32_64]; exact hot_ff
                    · dsimp [st_c]; rw [bv_c0_zext32_64]; exact hent_b
                  pt_steps_nogrp
                  exact hJtail (off_v, p_v + 1#64, q_v + 1#64, end_v, true, ()) m
                    ⟨st_c, hlen_c, hw_c, hmrk, fullArenaVarsNodup_of_arena_eq hnd_wb rfl rfl,
                      ⟨fullLastLearnedWf_of_refs_eq hext_wb.1 rfl rfl, hext_wb.2⟩,
                      hdm, hcl1, hcv, hfu, hlm, hws1,
                      fullTrailRsnsExt_trans htr_wb (fullTrailRsnsExt_congr rfl rfl rfl rfl),
                      fullHbrBufOkW_congr hhbr_wb rfl rfl,
                      hsw_wb'.with_nonwatch (k' := st_c.core) rfl rfl rfl rfl fun _ h => h,
                      fun _ => Or.inr hconfl_ok, (fun hf => by cases hf), hm⟩
                · have hot_0 : st_wb.core.vals[(w0_v &&& 2147483647#32).toNat]?.getD 0#8 =
                      0#8 := by
                    apply pt_vals_eq_0_of_flags hot_vlt (hw_wb.vals_domain _ hot_lt)
                    · rw [Bool.not_eq_true]; dsimp only [st_wb, w0_v]; pt_clear_big; assumption
                    · rw [Bool.not_eq_true]; dsimp only [st_wb, w0_v]; pt_clear_big; assumption
                  c0_call hAssignLvl
                  refine ⟨c, st_wb, R, rfl, hlen_wb, hm, ?_⟩
                  have hcur_wb : st_wb.core.cur_vars ≤ c.max_vars := hlen_wb.core_ok.cur_vars_le
                  have hte_wb : st_wb.core.trail_end < st_wb.core.cur_vars :=
                    hw_wb.trail_end_lt_of_unassigned hot_lt hot_0
                  have hno_wb : ¬ (st_wb.core.cur_vars ≤ (w0_v &&& 2147483647#32).toNat / 2 ∨
                      c.max_vars ≤ st_wb.core.trail_end ∨
                      st_wb.core.vals[(w0_v &&& 2147483647#32).toNat]?.getD 0#8 ≠ 0#8) := by
                    intro hbad
                    rcases hbad with h1 | h2 | h3
                    · have hlt2 : (w0_v &&& 2147483647#32).toNat < 2 * st_wb.core.cur_vars :=
                        hot_lt
                      omega
                    · omega
                    · exact h3 hot_0
                  rw [ite_eq_right ?hno]
                  case hno => exact hno_wb
                  dsimp only
                  intro flags' unass' phases' m_a hfll hph hm_a
                  have hnot_31 : (lit ^^^ 1#32).toNat < 0x7FFFFFFF := by omega
                  obtain ⟨hbs_msb, hbs_ne, hbs_lit⟩ := bv32_set_bin_watch_spec hnot_31
                  obtain ⟨kf, hkf, hkeq⟩ := (hw_wb.vals_false_iff _ hnot_lt').mp hnf
                  have hklvl := hw_wb.lvl_le kf hkf
                  dsimp only [withEmptyModeWatches] at hklvl
                  have hkv_eq : (st_wb.core.trl[kf]?.getD 0#32).toNat / 2 =
                      (lit ^^^ 1#32).toNat / 2 := by rw [hkeq]; exact fullInv_var_xor1 _
                  rw [hkv_eq, hcl1] at hklvl
                  have hu := unitAssignLvl_preserves_witness hlen_wb hw_wb
                    (other := w0_v &&& 2147483647#32)
                    (rsn := ((lit ^^^ 1#32) &&& 2147483647#32) ||| 2147483648#32)
                    (alvl := 1#32) (not_lit := (lit ^^^ 1#32).toNat)
                    (flags' := flags') (phases' := phases') (unass' := unass')
                    (unfl' := st_wb.core.unflushed) hot_lt hfll hph hot_0 hnot_lt' hnf
                    (by decide) (by rw [hcl1]; decide) hbs_ne (by
                      rw [ite_eq_left hbs_msb, hbs_lit]
                      refine ⟨hnot_lt', entails_bin_swap hent_b, kf, hkf, hkeq,
                        by simpa using hklvl⟩)
                    (fun hc_msb => absurd hc_msb hbs_msb)
                  dsimp only at hu hm_a
                  let st_a : FullState :=
                    { st_wb with
                      core := { st_wb.core with
                        vals := (st_wb.core.vals.set (w0_v &&& 2147483647#32).toNat 1#8).set
                          ((w0_v &&& 2147483647#32).toNat ^^^ 1) 0xFF#8
                        flags := flags'
                        lvl := st_wb.core.lvl.set ((w0_v &&& 2147483647#32).toNat / 2) 1#32
                        rsns := st_wb.core.rsns.set ((w0_v &&& 2147483647#32).toNat / 2)
                          (((lit ^^^ 1#32) &&& 2147483647#32) ||| 2147483648#32)
                        trl := st_wb.core.trl.set st_wb.core.trail_end (w0_v &&& 2147483647#32)
                        trail_pos := st_wb.core.trail_pos.set
                          ((w0_v &&& 2147483647#32).toNat / 2)
                          (BitVec.ofNat 32 st_wb.core.trail_end)
                        trail_end := st_wb.core.trail_end + 1, unassigned := unass' }
                      scratch := { st_wb.scratch with phases := phases' } }
                  have hlen_a : st_a.LengthsOk c :=
                    ⟨{ hlen_wb.core_ok with
                      vals_len := by simp [st_a, hlen_wb.core_ok.vals_len],
                      flags_len := by simp [st_a, hfll],
                      lvl_len := by simp [st_a, hlen_wb.core_ok.lvl_len],
                      rsns_len := by simp [st_a, hlen_wb.core_ok.rsns_len],
                      trl_len := by simp [st_a, hlen_wb.core_ok.trl_len],
                      trail_pos_len := by simp [st_a, hlen_wb.core_ok.trail_pos_len],
                      trail_end_le := by simp [st_a]; omega,
                      propagated_le := by
                        simp [st_a]; have := hlen_wb.core_ok.propagated_le; omega },
                      { hlen_wb.scratch_ok with phases_len := by simp [st_a, hph] }⟩
                  have htr_ja := fullTrailRsnsExt_trans
                    (fullTrailRsnsExt_congr (k1 := st_wb.core)
                      (k2 := (withEmptyModeWatches c st_wb).core) rfl rfl rfl rfl)
                    (fullTrailRsnsExt_trans
                      (fullTrailRsnsExt_of_assign_lvl
                        (rsn := ((lit ^^^ 1#32) &&& 2147483647#32) ||| 2147483648#32)
                        (alvl := 1#32) (flags' := flags') (unass' := unass')
                        (unfl' := st_wb.core.unflushed) hw_wb hot_lt hot_0)
                      (fullTrailRsnsExt_congr (k2 := st_a.core) rfl rfl rfl rfl))
                  have htr_a := fullTrailRsnsExt_trans htr_wb htr_ja
                  refine hJloop (off_v, p_v + 1#64, q_v + 1#64, end_v, ()) m_a
                    (by dsimp only; rw [hp1_eq]; omega)
                    ⟨st_a, hlen_a, hu.1, fun w hw => hmrk w hw,
                      fullArenaVarsNodup_of_arena_eq hnd_wb rfl rfl,
                      ⟨fullLastLearnedWf_of_refs_eq hext_wb.1 rfl rfl, hext_wb.2⟩,
                      hdm, hcl1, hcv, hfu, hlm, hws1, htr_a,
                      fullHbrBufOkW_congr hhbr_wb rfl rfl,
                      hsw_wb'.with_nonwatch (k' := st_a.core) rfl rfl rfl rfl fun _ h => h,
                      hu.2, hoom, hm_a⟩
            · have hflag_l : (w0_v &&& 0x80000000#32) = 0#32 := by
                change (st.core.wstk[p_v.toNat]'hp_wa &&& 2147483648#32) = 0#32
                assumption
              obtain ⟨hrem2, _cr_v, _hcr_get, _hcr_lt, _hcr_ref, _hrem'⟩ :=
                watchSlice_inv_large hsplit.rem_slice (by omega) hw0_get hflag_l
              exfalso
              have hc' : end_v.toNat ≤ (p_v.toNat + 1) % 2 ^ 64 := hc
              rw [Nat.mod_eq_of_lt hp1_64] at hc'
              omega
            · have hflag_l : (w0_v &&& 0x80000000#32) = 0#32 := by pt_clear_big; assumption
              obtain ⟨hrem2, cr_v, hcr_get, hcr_lt, hcr_ref, hrem'⟩ :=
                watchSlice_inv_large hsplit.rem_slice (by omega) hw0_get hflag_l
              have hp1_wa : (p_v + 1#64).toNat < st.core.wstk.length := by omega
              focus
                have hcr_at : st.core.wstk[(p_v + 1#64).toNat]'hp1_wa = cr_v := Option.some_inj.mp
                  (by rw [← List.getElem?_eq_getElem hp1_wa, hp1_eq]; exact hcr_get)
                have hp2_64 : p_v.toNat + 2 < 2 ^ 64 := by omega
                have hp2_eq : (p_v + 2#64).toNat = p_v.toNat + 2 := by bv_omega
                have hsplit_prev : FullSplitWatchesInv F_cur st.core (lit ^^^ 1#32).toNat
                    off_v.toNat q_v.toNat (p_v.toNat + 2) end_v.toNat :=
                  hsplit.advance_rem (by omega) (by omega)
                    (by simpa only [show end_v.toNat - (p_v.toNat + 2) =
                      end_v.toNat - p_v.toNat - 2 by omega] using hrem')
                have hsplit_p2 : FullSplitWatchesInv F_cur st.core (lit ^^^ 1#32).toNat
                    off_v.toNat q_v.toNat (p_v + 2#64).toNat end_v.toNat := by
                  simpa only [← hp2_eq] using hsplit_prev
                have hwf_cr := hw_nw.arena.refs_wf cr_v.toNat hcr_ref
                have hcr_sz3 : 3 ≤ fullArenaClauseSize st cr_v.toNat := hwf_cr.2.1
                have hcr_bd : cr_v.toNat + 3 + fullArenaClauseSize st cr_v.toNat ≤
                    st.core.arena_len := Nat.le_trans hwf_cr.2.2.1 hwf_cr.2.2.2.1
                have hcr_arr : cr_v.toNat + 3 + fullArenaClauseSize st cr_v.toNat ≤
                    st.core.arena.length := by
                  have := hcl.arena_len_arr; have := hcl.arena_len_le; omega
                have ha_lt := c.harena; unfold dimacsBound at ha_lt
                have hcr64 : (cr_v.setWidth 64).toNat = cr_v.toNat := bv_c0_zext32_64 _
                have hcr_lt' : cr_v.toNat < st.core.arena.length := by omega
                have hcr2_lt : cr_v.toNat + 2 < st.core.arena.length := by omega
                have hcr3_lt : cr_v.toNat + 3 < st.core.arena.length := by omega
                have hcr4_lt : cr_v.toNat + 4 < st.core.arena.length := by omega
                have har_len : st.core.arena.length = c.arena_cap := hcl.arena_len_arr
                have har_64 : st.core.arena_len < 2 ^ 64 := by have := hcl.arena_len_le; omega
                have hp2_sum : p_v + 1 + 1 = p_v + 2#64 := by bv_omega
                have hcr_mod : st.core.wstk[(p_v.toNat + 1) % 2 ^ 64]'(by
                    rw [Nat.mod_eq_of_lt hp1_64, ← hp1_eq]; exact hp1_wa) = cr_v :=
                  Option.some_inj.mp (by
                    rw [← List.getElem?_eq_getElem, Nat.mod_eq_of_lt hp1_64]; exact hcr_get)
                have hsz_mod : (st.core.arena[(cr_v.toNat + 2) % 2 ^ 64]'(by
                    rw [Nat.mod_eq_of_lt (by omega : cr_v.toNat + 2 < 2 ^ 64)]
                    exact hcr2_lt)).toNat = fullArenaClauseSize st cr_v.toNat := by
                  have hidx2 : (cr_v.toNat + 2) % 2 ^ 64 = cr_v.toNat + 2 :=
                    Nat.mod_eq_of_lt (by omega)
                  have heq : st.core.arena[(cr_v.toNat + 2) % 2 ^ 64]'(by
                      rw [hidx2]; exact hcr2_lt) = st.core.arena[cr_v.toNat + 2]'hcr2_lt :=
                    Option.some_inj.mp (by
                      rw [← List.getElem?_eq_getElem, hidx2, ← List.getElem?_eq_getElem hcr2_lt])
                  rw [heq]; unfold fullArenaClauseSize fullArenaClauseSizeCore
                  rw [List.getElem?_eq_getElem hcr2_lt, Option.getD_some]
                pt_steps_nogrp
                refine wp_join_group (fun _ mj => ml = mj) ?_ ?_
                · intro Js_2 _ mj heq; subst heq
                  pt_steps_nogrp
                  · exfalso
                    have h2 : cr_v.toNat + 3 < 2 ^ 64 := by omega
                    rw [hcr_mod, Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt har_64] at hc
                    omega
                  · rw [hp2_sum]
                    exact hJloop (off_v, p_v + 2#64, q_v, end_v, ()) ml
                      (by dsimp only; rw [hp2_eq]; omega)
                      ⟨st, hlen, hw_nw, hmrk, hnd, hext, hdm, hcl1, hcv, hfu, hlm, hws1, htr,
                        hhbr, hsplit_p2, hnf, hoom, hml⟩
                  · exfalso; simp only [hcr_mod, hsz_mod] at hc; omega
                  · exfalso
                    simp only [hcr_mod, hsz_mod] at hc
                    have h2 : cr_v.toNat + 3 + fullArenaClauseSize st cr_v.toNat < 2 ^ 64 := by
                      omega
                    rw [Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt har_64] at hc; omega
                  · have hcr_ng : fullArenaClauseGarb st cr_v.toNat = false := by
                      unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
                      rw [List.getElem?_eq_getElem hcr_lt', Option.getD_some]
                      have hidx : cr_v.toNat =
                          st.core.wstk[(p_v.toNat + 1) % 2 ^ 64].toNat :=
                        congrArg BitVec.toNat hcr_mod.symm
                      have heq_w : st.core.arena[cr_v.toNat]'hcr_lt' =
                          st.core.arena[st.core.wstk[(p_v.toNat + 1) % 2 ^ 64].toNat]'(by
                            rw [← hidx]; exact hcr_lt') := by
                        congr 1
                      have heq0 : (st.core.arena[cr_v.toNat]'hcr_lt' &&& 0x00080000#32) =
                          0#32 := by
                        rw [heq_w]
                        change (_ &&& 524288#32) = 0#32
                        assumption
                      change ((_ &&& (BitVec.ofNat 32 524288)) != 0#32) = false
                      simp [heq0]
                    have hp1_c0 : st.core.wstk[(p_v + 1 : BitVec 64).toNat]'hp1_wa = cr_v := hcr_at
                    have hcr3_v : (cr_v.setWidth 64 + (3 : BitVec 64)).toNat = cr_v.toNat + 3 := by
                      rw [BitVec.toNat_add, hcr64, show (3 : BitVec 64).toNat = 3 from rfl,
                        Nat.mod_eq_of_lt (by omega)]
                    have hcr4_v : (cr_v.setWidth 64 + (4 : BitVec 64)).toNat = cr_v.toNat + 4 := by
                      rw [BitVec.toNat_add, hcr64, show (4 : BitVec 64).toNat = 4 from rfl,
                        Nat.mod_eq_of_lt (by omega)]
                    simp only [hp1_c0]
                    pt_steps_nogrp
                    try simp only [hcr3_v, hcr4_v]
                    let l0_v := st.core.arena[cr_v.toNat + 3]'hcr3_lt
                    let l1_v := st.core.arena[cr_v.toNat + 4]'hcr4_lt
                    refine wp_join_group
                      (fun (lv, ()) mj => ∃ st_x : FullState,
                        st_x.LengthsOk c ∧
                        FullWitnessInv c F0 F_cur (withEmptyModeWatches c st_x).core ∧
                        FullMrkZero c st_x ∧ FullArenaVarsNodup st_x ∧ FullExtScratchOk c st_x ∧
                        st_x.core.dense_mode = 0#64 ∧ st_x.core.cur_level = 1 ∧
                        st_x.core.cur_vars = s.core.cur_vars ∧ st_x.core.fuel = s.core.fuel ∧
                        st_x.core.lit_mark = s.core.lit_mark ∧
                        st_x.scratch.work_stk1 = s.scratch.work_stk1 ∧
                        FullTrailRsnsExt s.core st_x.core ∧
                        FullHbrBufOkW F_cur st_x st_x.core.tmp_cnt ∧
                        FullSplitWatchesInv F_cur st_x.core (lit ^^^ 1#32).toNat off_v.toNat
                          q_v.toNat (p_v + 2#64).toNat end_v.toNat ∧
                        st_x.core.vals[(lit ^^^ 1#32).toNat]?.getD 0#8 = 0xFF#8 ∧
                        st_x.core.oom = 0#64 ∧ cr_v.toNat ∈ fullArenaClauseRefs st_x ∧
                        fullArenaClauseGarb st_x cr_v.toNat = false ∧
                        3 ≤ fullArenaClauseSize st_x cr_v.toNat ∧
                        cr_v.toNat + 3 + fullArenaClauseSize st_x cr_v.toNat ≤
                          st_x.core.arena_len ∧
                        cr_v.toNat + 3 + fullArenaClauseSize st_x cr_v.toNat ≤
                          st_x.core.arena.length ∧
                        (st_x.core.arena[cr_v.toNat + 3]?.getD 0#32).toNat = lv.toNat ∧
                        (st_x.core.arena[cr_v.toNat + 4]?.getD 0#32).toNat =
                          (lit ^^^ 1#32).toNat ∧
                        (FullMem c st_x ⋆ R) mj)
                      (fun _ (lv, ()) mj ⟨st_x, hx_len, hx_nw, hx_mrk, hx_nd, hx_ext, hx_dm,
                        hx_cl1, hx_cv, hx_fu, hx_lm, hx_ws1, hx_tr, hx_hbr, hx_sw, hx_nf,
                        hx_oom, hx_ref, hx_ng, hx_sz, hx_bd, hx_arr, hx_l0, hx_not, hm_x⟩ => by
                        rw [hp2_sum]
                        exact propLitLarge_wp (not_lit := lit ^^^ 1#32) (p_prev := p_v)
                          hFindRepl hWatchPush hHbrDom hAssignLvl hnot_lt hJtail
                          (fun off_r p_r q_r end_r m' hm' hdec =>
                            hJloop (off_r, p_r, q_r, end_r, ()) m'
                              (by dsimp only; rw [hdec, hp2_eq]; omega) hm')
                          rfl rfl rfl rfl rfl rfl rfl hp2_eq hx_len hx_nw hx_mrk hx_nd
                          hx_ext hx_dm hx_cl1 hx_cv hx_fu hx_lm hx_ws1 hx_tr hx_hbr hx_sw
                          hqp_le hx_nf hx_oom hflag_l hcr_lt hx_ref hx_ng hx_sz hx_bd hx_arr
                          (by
                            rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at hx_l0)
                          (by
                            rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at hx_not)
                          hm_x)
                      (fun Js_3 hJs3 => ?_)
                    pt_steps_nogrp
                    · have hl0_eq : l0_v = lit ^^^ 1#32 := by pt_clear_big; exact hc
                      have hsw_l := arena_swapLits_keep_inv hlen hw_nw hnd hext hcr_ref
                        (k1 := 0) (k2 := 1) (by omega) (by omega)
                      dsimp only at hsw_l
                      let ar_x := (st.core.arena.set (cr_v.toNat + 3) l1_v).set
                        (cr_v.toNat + 4) (lit ^^^ 1#32)
                      have har_x_eq : (st.core.arena.set (cr_v.toNat + 3 + 0) l1_v).set
                          (cr_v.toNat + 3 + 1) l0_v = ar_x := by
                        simp only [hl0_eq]; rfl
                      rw [har_x_eq] at hsw_l
                      let st_x : FullState := { st with core := { st.core with arena := ar_x } }
                      obtain ⟨hx_len, hx_nw, hx_nd, hx_ext, hx_ref, hper_x⟩ :=
                        (hsw_l : st_x.LengthsOk c ∧
                          FullWitnessInv c F0 F_cur (withEmptyModeWatches c st_x).core ∧
                          FullArenaVarsNodup st_x ∧ FullExtScratchOk c st_x ∧
                          fullArenaClauseRefs st_x = fullArenaClauseRefs st ∧
                          ∀ r0 ∈ fullArenaClauseRefs st,
                            fullArenaClauseSize st_x r0 = fullArenaClauseSize st r0 ∧
                            fullArenaClauseGarb st_x r0 = fullArenaClauseGarb st r0 ∧
                            (fullArenaClauseLits st_x r0).Perm (fullArenaClauseLits st r0))
                      have hsz_x : fullArenaClauseSize st_x cr_v.toNat =
                          fullArenaClauseSize st cr_v.toNat := (hper_x _ hcr_ref).1
                      have hng_x : fullArenaClauseGarb st_x cr_v.toNat = false :=
                        (hper_x _ hcr_ref).2.1.trans hcr_ng
                      have harr_x : cr_v.toNat + 3 + fullArenaClauseSize st_x cr_v.toNat ≤
                          st_x.core.arena.length := by
                        simpa only [st_x, ar_x, hsz_x, List.length_set] using hcr_arr
                      have hx_l3 : (st_x.core.arena[cr_v.toNat + 3]?.getD 0#32).toNat =
                          l1_v.toNat := by
                        dsimp only [st_x, ar_x]
                        rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega),
                          Option.getD_some]
                      have hx_l4 : (st_x.core.arena[cr_v.toNat + 4]?.getD 0#32).toNat =
                          (lit ^^^ 1#32).toNat := by
                        dsimp only [st_x, ar_x]
                        rw [List.getElem?_set_self (by simp only [List.length_set]; omega),
                          Option.getD_some]
                      have hm_x : (FullMem c st_x ⋆ R) m := by
                        dsimp only [st_x, ar_x]
                        simp only [hcr3_v, hcr4_v] at hm
                        exact hm
                      exact hJs3 (l1_v, ()) m
                        ⟨st_x, hx_len, hx_nw, hmrk, hx_nd, hx_ext, hdm, hcl1, hcv, hfu, hlm,
                          hws1, fullTrailRsnsExt_trans htr (fullTrailRsnsExt_congr rfl rfl rfl
                          rfl), fullHbrBufOkW_congr hhbr rfl rfl,
                          hsplit_p2.with_nonwatch (k' := st_x.core) rfl rfl rfl rfl fun r0 hr0 =>
                            by change r0 ∈ fullArenaClauseRefs st_x; rw [hx_ref]; exact hr0,
                          hnf, hoom, hx_ref ▸ hcr_ref, hng_x, hsz_x ▸ hcr_sz3,
                          by simpa only [st_x, hsz_x] using hcr_bd, harr_x, hx_l3, hx_l4, hm_x⟩
                    · rw [hp2_sum]
                      exact hJloop (off_v, p_v + 2#64, q_v, end_v, ()) ml
                        (by dsimp only; rw [hp2_eq]; omega)
                        ⟨st, hlen, hw_nw, hmrk, hnd, hext, hdm, hcl1, hcv, hfu, hlm, hws1, htr,
                          hhbr, hsplit_p2, hnf, hoom, hml⟩
                    · have hl1_eq : l1_v = lit ^^^ 1#32 := by
                        pt_clear_big; first | exact hc | exact not_ne_iff.mp hc
                      exact hJs3 (l0_v, ()) ml
                        ⟨st, hlen, hw_nw, hmrk, hnd, hext, hdm, hcl1, hcv, hfu, hlm, hws1, htr,
                          hhbr, hsplit_p2, hnf, hoom, hcr_ref, hcr_ng, hcr_sz3, hcr_bd, hcr_arr,
                          by rw [List.getElem?_eq_getElem hcr3_lt, Option.getD_some],
                          by
                            rw [List.getElem?_eq_getElem hcr4_lt, Option.getD_some]
                            exact congrArg BitVec.toNat hl1_eq,
                          hml⟩
                · intro Js_2 hJs2
                  pt_steps_nogrp
                  · have hblk_lt : (w0_v &&& 0x7FFFFFFF#32).toNat < 2 * st.core.cur_vars := by
                      have hcv64 : s.core.cur_vars < 2 ^ 64 := by
                        have := hcl0.cur_vars_le; omega
                      have h2cv64 : 2 * s.core.cur_vars < 2 ^ 64 := by omega
                      pt_clear_big
                      rw [Nat.mod_eq_of_lt hcv64, Nat.mod_eq_of_lt h2cv64] at hc
                      rw [hcv]; exact hc
                    have hblk_vlt : (w0_v &&& 0x7FFFFFFF#32).toNat < st.core.vals.length := by
                      rw [hcl.vals_len]; have := hcl.cur_vars_le; omega
                    have hblk_v64 : ((w0_v &&& 0x7FFFFFFF#32).setWidth 64).toNat <
                        st.core.vals.length := by rw [bv_c0_zext32_64]; exact hblk_vlt
                    have hq_wa : q_v.toNat < st.core.wstk.length := by omega
                    have hq1_wa : q_v.toNat + 1 < st.core.wstk.length := by omega
                    have hq1_64 : q_v.toNat + 1 < 2 ^ 64 := by omega
                    have hq2_64 : q_v.toNat + 2 < 2 ^ 64 := by omega
                    have hq1_eq : (q_v + 1#64).toNat = q_v.toNat + 1 := bv64_add1_toNat hq1_64
                    have hq1_c0 : (q_v + 1 : BitVec 64).toNat = q_v.toNat + 1 := hq1_eq
                    have hp1_c0 : st.core.wstk[(p_v + 1 : BitVec 64).toNat]'hp1_wa = cr_v := hcr_at
                    have hq2_eq : (q_v + 2#64).toNat = q_v.toNat + 2 := by bv_omega
                    have hq2_c0 : (q_v + 2 : BitVec 64) = q_v + 2#64 := rfl
                    pt_steps_nogrp
                    · have hsw_wl := hsplit_prev.write_large (w0 := w0_v) (cref := cr_v) hnot_lt'
                        hqp_le hq_wa hq1_wa hflag_l hcr_lt hcr_ref
                      let st_wl : FullState := { st with core := { st.core with
                        wstk := (st.core.wstk.set q_v.toNat w0_v).set (q_v.toNat + 1) cr_v } }
                      have hlen_wl : st_wl.LengthsOk c :=
                        ⟨{ hcl with wstk_len_arr := by simp [st_wl, hwa_st] }, hlen.scratch_ok⟩
                      have hw_wl := fullWitnessInv_nw_upd_watches (s := st) (s' := st_wl) hw_nw
                        hlen_wl.core_ok rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
                      have hsw_wl' : FullSplitWatchesInv F_cur st_wl.core (lit ^^^ 1#32).toNat
                          off_v.toNat (q_v + 2#64).toNat (p_v + 2#64).toNat end_v.toNat := by
                        simpa only [st_wl, hq2_eq, hp2_eq] using hsw_wl
                      have hm_wl : (FullMem c st_wl ⋆ R) m := by
                        dsimp only [st_wl]; rw [hq1_c0, hp1_c0] at hm; exact hm
                      rw [hp2_sum, hq2_c0]
                      exact hJloop (off_v, p_v + 2#64, q_v + 2#64, end_v, ()) m
                        (by dsimp only; rw [hp2_eq]; omega)
                        ⟨st_wl, hlen_wl, hw_wl, hmrk, fullArenaVarsNodup_of_arena_eq hnd rfl rfl,
                          ⟨fullLastLearnedWf_of_refs_eq hext.1 rfl rfl, hext.2⟩,
                          hdm, hcl1, hcv, hfu, hlm, hws1,
                          fullTrailRsnsExt_trans htr (fullTrailRsnsExt_congr rfl rfl rfl rfl),
                          fullHbrBufOkW_congr hhbr rfl rfl, hsw_wl', hnf, hoom, hm_wl⟩
                    · exact hJs2 () ml rfl
                  · exact hJs2 () ml rfl
          · have hp_eq : p_v = end_v := BitVec.eq_of_toNat_eq (by pt_bound)
            exact hJtail (off_v, p_v, q_v, end_v, false, ()) ml
              ⟨st, hlen, hw_nw, hmrk, hnd, hext, hdm, hcl1, hcv, hfu, hlm, hws1, htr, hhbr,
                hsplit, (fun hf => by cases hf), fun _ => ⟨hoom, hp_eq⟩, hml⟩

theorem full_probe_prop_lit_wp (Γ : Env)
    (hFindRepl : ∀ args m Q X, fullFindReplSpec args m Q X →
      Γ "full_find_repl" [i64, i64] [i64] args m Q X)
    (hWatchPush : ∀ args m Q X, fullWatchPushSpec args m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] args m Q X)
    (hHbrDom : ∀ args m Q X, fullHbrDomSpec args m Q X →
      Γ "full_hbr_dom" [i64, i32, i32] [i32] args m Q X)
    (hAssignLvl : ∀ args m Q X, fullAssignLvlSpec args m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] args m Q X) :
    ∀ args m Q X, fullProbePropLitSpec args m Q X →
      Func.wp Γ full_probe_prop_lit_body args m Q X := by
  rintro args m Q X ⟨c, F0, F_cur, s, R, hh, hlen, hw, hmrk, hnd, hext, hdm, hcl1, hoom, hhbr, hm,
    hQ⟩
  apply full_probe_prop_lit_ext_wp Γ hFindRepl hWatchPush hHbrDom hAssignLvl args m Q X
  refine ⟨c, F0, F_cur, s, R, hh, hlen, hw, hmrk, hnd, hext, hdm, hcl1, hoom, hhbr, hm, ?_⟩
  intro ok s' m' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 hm'
  exact hQ ok s' m' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12.1.1 h13 h14 h15 hm'

/-! ## 2. `full_probe_prop_ext_wp` & `full_probe_prop_wp` -/

private def fullProbePropPostSpec (Ext : FullCoreState → FullCoreState → Prop) :
    Spec [i64, i32] [.bool] := fun (h, _lit, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧ FullMrkZero c s ∧
    FullArenaVarsNodup s ∧ FullExtScratchOk c s ∧ s.core.dense_mode = 0#64 ∧
    s.core.cur_level = 1 ∧ s.core.oom = 0#64 ∧ FullHbrBufOkW F_cur s s.core.tmp_cnt ∧
    (FullMem c s ⋆ R) m ∧ ∀ (ok : Bool) s' m',
      s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core → FullMrkZero c s' →
      FullArenaVarsNodup s' → FullExtScratchOk c s' → s'.core.dense_mode = 0#64 →
      s'.core.cur_level = 1 → s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
      s'.core.lit_mark = s.core.lit_mark → s'.scratch.work_stk1 = s.scratch.work_stk1 →
      Ext s.core s'.core → FullHbrBufOkW F_cur s' s'.core.tmp_cnt →
      (ok = false → s'.core.oom ≠ 0#64 ∨ FullConflictOkW F_cur s') →
      (ok = true → s'.core.oom = 0#64) → (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

private theorem full_probe_prop_aux (Γ : Env) (Ext : FullCoreState → FullCoreState → Prop)
    (hrefl : ∀ k, Ext k k) (htrans : ∀ k1 k2 k3, Ext k1 k2 → Ext k2 k3 → Ext k1 k3)
    (hcongr : ∀ k1 k2, k2.trail_end = k1.trail_end → k2.trl = k1.trl → k2.lvl = k1.lvl →
      k2.rsns = k1.rsns → Ext k1 k2)
    (hPropLit : ∀ args m Q X, fullProbePropPostSpec Ext args m Q X →
      Γ "full_probe_prop_lit" [i64, i32] [.bool] args m Q X) :
    ∀ args m Q X,
      (fun (h, ()) m Q _ =>
        ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
            (R : Mem 64 → Prop),
          h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
          FullMrkZero c s ∧ FullArenaVarsNodup s ∧ FullExtScratchOk c s ∧
          s.core.dense_mode = 0#64 ∧ s.core.cur_level = 1 ∧
          FullHbrBufOkW F_cur s s.core.tmp_cnt ∧ (FullMem c s ⋆ R) m ∧
          ∀ r s' m', s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core → FullMrkZero c s' →
            FullArenaVarsNodup s' → FullExtScratchOk c s' → s'.core.dense_mode = 0#64 →
            s'.core.cur_level = 1 → s'.core.cur_vars = s.core.cur_vars →
            s'.core.fuel.toNat ≤ s.core.fuel.toNat → s'.core.lit_mark = s.core.lit_mark →
            s'.scratch.work_stk1 = s.scratch.work_stk1 → Ext s.core s'.core →
            FullHbrBufOkW F_cur s' s'.core.tmp_cnt → (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) →
            (r = 1#64 → FullConflictOkW F_cur s') →
            (r = 0#64 → s'.core.propagated = s'.core.trail_end) →
            (FullMem c s' ⋆ R) m' → Q (r, ()) m') args m Q X →
      Func.wp Γ full_probe_prop_body args m Q X := by
  rintro ⟨h_arg, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, heq_h, hlen0, hw0, hmrk0, hnd0, hext0, hdm0, hcl10, hhbr0, hm0, hQ⟩
  subst heq_h
  have hmv := c.hmaxv; unfold dimacsBound at hmv
  pt_steps_nogrp
  let propLoopInv : Nat → Tup Val [] → Mem 64 → Prop := fun rem () ml => ∃ st : FullState,
    rem = st.core.fuel.toNat ∧ st.LengthsOk c ∧ FullWitnessInv c F0 F_cur st.core ∧
    FullMrkZero c st ∧ FullArenaVarsNodup st ∧ FullExtScratchOk c st ∧
    st.core.dense_mode = 0#64 ∧ st.core.cur_level = 1 ∧ st.core.cur_vars = s.core.cur_vars ∧
    st.core.fuel.toNat ≤ s.core.fuel.toNat ∧ st.core.lit_mark = s.core.lit_mark ∧
    st.scratch.work_stk1 = s.scratch.work_stk1 ∧ Ext s.core st.core ∧
    FullHbrBufOkW F_cur st st.core.tmp_cnt ∧ (FullMem c st ⋆ R) ml
  refine wp_loop_group propLoopInv ?_ ?_
  · rintro Js rem ⟨⟩ ml ih ⟨st, rfl, hlen, hw, hmrk, hnd, hext, hdm, hcl1, hcv, hfu, hlm, hws1,
      htr, hhbr, hml⟩
    have hcl := hlen.core_ok
    have hcv_le := hcl.cur_vars_le; have hte_le := hcl.trail_end_le
    have hpr_le := hcl.propagated_le; have htl := hcl.trl_len
    have hte_64 : st.core.trail_end < 2 ^ 64 := by omega
    have hpr_64 : st.core.propagated < 2 ^ 64 := by omega
    pt_steps_nogrp
    · exact hQ 2#64 st ml hlen hw hmrk hnd hext hdm hcl1 hcv hfu hlm hws1 htr hhbr
        (Or.inr (Or.inr rfl)) (fun h1 => by cases h1) (fun h0 => by cases h0) hml
    · exact hQ 2#64 st ml hlen hw hmrk hnd hext hdm hcl1 hcv hfu hlm hws1 htr hhbr
        (Or.inr (Or.inr rfl)) (fun h1 => by cases h1) (fun h0 => by cases h0) hml
    · have hpr_lt : st.core.propagated < st.core.trail_end := by pt_bound
      have hoom0 : st.core.oom = 0#64 := by pt_clear_big; assumption
      have hfuel_ne0 : st.core.fuel ≠ 0#64 := by pt_clear_big; exact hc
      have hfuel_sub : (st.core.fuel - 1#64).toNat = st.core.fuel.toNat - 1 :=
        bv64_sub1_toNat hfuel_ne0
      have hfuel_pos : 0 < st.core.fuel.toNat := Nat.pos_of_ne_zero fun h0 =>
        hfuel_ne0 (BitVec.eq_of_toNat_eq (by simpa using h0))
      have hpr1 : (BitVec.ofNat 64 st.core.propagated + 1#64).toNat =
          st.core.propagated + 1 := by
        rw [bv64_add1_toNat (by rw [bv64_ofNat_toNat (by omega)]; omega),
          bv64_ofNat_toNat (by omega)]
      let st1 : FullState := { st with core := { st.core with
        fuel := st.core.fuel - 1#64, propagated := st.core.propagated + 1 } }
      have hlen1 : st1.LengthsOk c :=
        ⟨{ hcl with propagated_le := by dsimp [st1]; omega }, hlen.scratch_ok⟩
      have hw1 : FullWitnessInv c F0 F_cur st1.core :=
        fullWitnessInv_congr_ctrl hw hlen1.core_ok rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
          rfl rfl rfl rfl rfl rfl
      have htr1 : Ext s.core st1.core :=
        htrans _ _ _ htr (hcongr st.core st1.core rfl rfl rfl rfl)
      have hfuel_lt : st.core.fuel.toNat < 2 ^ 64 := st.core.fuel.isLt
      have hfu1 : st1.core.fuel.toNat < st.core.fuel.toNat := by dsimp [st1]; omega
      have hpr_lt' : st.core.propagated < st.core.trl.length := by omega
      pt_steps_nogrp
      have hm1 : (FullMem c st1 ⋆ R) m := by
        dsimp only [st1]; rw [show (1 : BitVec 64) = 1#64 from rfl, hpr1] at hm; exact hm
      c0_call hPropLit
      refine ⟨c, F0, F_cur, st1, R, rfl, hlen1, hw1, hmrk,
        fullArenaVarsNodup_of_arena_eq hnd rfl rfl,
        ⟨fullLastLearnedWf_of_refs_eq hext.1 rfl rfl, hext.2⟩,
        hdm, hcl1, hoom0, fullHbrBufOkW_congr hhbr rfl rfl, hm1, ?_⟩
      dsimp only
      intro ok s' m' hs'_len hs'_w hs'_mrk hs'_nd hs'_ext hs'_dm hs'_cl1 hs'_cv hs'_fu hs'_lm
        hs'_ws1 hs'_tr hs'_hbr hs'_f hs'_t hm'
      have htr' := htrans _ _ _ htr1 hs'_tr
      have hcv' : s'.core.cur_vars = s.core.cur_vars := hs'_cv.trans hcv
      have hfu' : s'.core.fuel.toNat ≤ s.core.fuel.toNat := by rw [hs'_fu]; omega
      have hlm' : s'.core.lit_mark = s.core.lit_mark := hs'_lm.trans hlm
      have hws1' : s'.scratch.work_stk1 = s.scratch.work_stk1 := hs'_ws1.trans hws1
      pt_steps_nogrp
      · exact ih s'.core.fuel.toNat () m' (by rw [hs'_fu]; exact hfu1)
          ⟨s', rfl, hs'_len, hs'_w, hs'_mrk, hs'_nd, hs'_ext, hs'_dm, hs'_cl1, hcv', hfu',
            hlm', hws1', htr', hs'_hbr, hm'⟩
      · have hok_f : ok = false := by pt_clear_big; cases ok <;> simp_all
        refine wp_join_group
          (fun (rv, ()) mj => (rv = 1#64 ∨ rv = 2#64) ∧
            (rv = 1#64 → FullConflictOkW F_cur s') ∧ mj = m')
          (fun _ (rv, ()) mj ⟨hrd, hcf, hmeq⟩ => by
            subst hmeq; pt_steps_nogrp
            exact hQ rv s' mj hs'_len hs'_w hs'_mrk hs'_nd hs'_ext hs'_dm hs'_cl1 hcv' hfu'
              hlm' hws1' htr' hs'_hbr (by rcases hrd with rfl | rfl <;> simp)
              hcf (fun h0 => by rcases hrd with rfl | rfl <;> cases h0) hm')
          (fun Js2 hJs2 => by
            pt_steps_nogrp
            · exact hJs2 (2#64, ()) m' ⟨Or.inr rfl, (fun h1 => by cases h1), rfl⟩
            · have hoom_s' : s'.core.oom = 0#64 := by pt_clear_big; exact hc
              have hcf := (hs'_f hok_f).resolve_left (fun h => h hoom_s')
              exact hJs2 (1#64, ()) m' ⟨Or.inl rfl, fun _ => hcf, rfl⟩)
    · have hpr_eq : st.core.propagated = st.core.trail_end := by
        simp only [bv_c0, Nat.mod_eq_of_lt hte_64, Nat.mod_eq_of_lt hpr_64] at hc; omega
      exact hQ 0#64 st ml hlen hw hmrk hnd hext hdm hcl1 hcv hfu hlm hws1 htr hhbr
        (Or.inl rfl) (fun h1 => by cases h1) (fun _ => hpr_eq) hml
  · intro Js hJs; pt_steps_nogrp
    exact hJs s.core.fuel.toNat () m ⟨s, rfl, hlen0, hw0, hmrk0, hnd0, hext0, hdm0, hcl10, rfl,
      Nat.le_refl _, rfl, rfl, hrefl s.core, hhbr0, hm0⟩

theorem full_probe_prop_ext_wp (Γ : Env)
    (hPropLit : ∀ args m Q X, fullProbePropLitExtSpec args m Q X →
      Γ "full_probe_prop_lit" [i64, i32] [.bool] args m Q X) :
    ∀ args m Q X, fullProbePropExtSpec args m Q X →
      Func.wp Γ full_probe_prop_body args m Q X :=
  full_probe_prop_aux Γ FullTrailRsnsExt fullTrailRsnsExt_refl
    (fun _ _ _ h1 h2 => fullTrailRsnsExt_trans h1 h2)
    (fun _ _ h1 h2 h3 h4 => fullTrailRsnsExt_congr h1 h2 h3 h4)
    (fun args m Q X h => hPropLit args m Q X h)

theorem full_probe_prop_wp (Γ : Env)
    (hPropLit : ∀ args m Q X, fullProbePropLitSpec args m Q X →
      Γ "full_probe_prop_lit" [i64, i32] [.bool] args m Q X) :
    ∀ args m Q X, fullProbePropSpec args m Q X →
      Func.wp Γ full_probe_prop_body args m Q X := by
  rintro args m Q X ⟨c, F0, F_cur, s, R, hh, hlen, hw, hmrk, hnd, hext, hdm, hcl1, hhbr, hm, hQ⟩
  refine full_probe_prop_aux Γ (fun _ _ => True) (fun _ => trivial) (fun _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ _ => trivial) ?_ args m Q X
    ⟨c, F0, F_cur, s, R, hh, hlen, hw, hmrk, hnd, hext, hdm, hcl1, hhbr, hm,
      fun r s' m' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 _ h12 h13 h14 h15 hm' =>
        hQ r s' m' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 hm'⟩
  rintro a m' Q' X' ⟨c', F0', Fc', st, R', h', hl', hw', hm', hn', he', hd', hc', ho', hb',
    hmm, hQ'⟩
  apply hPropLit a m' Q' X'
  refine ⟨c', F0', Fc', st, R', h', hl', hw', hm', hn', he', hd', hc', ho', hb', hmm,
    fun ok st' m'' x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 _ x13 x14 x15 hm'' =>
      hQ' ok st' m'' x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 trivial x13 x14 x15 hm''⟩

/-! ## 3. `full_probe_flush_hbr_wp` -/

theorem full_probe_flush_hbr_wp (Γ : Env)
    (hAddBin : ∀ args m Q X, fullAddBinSpec args m Q X →
      Γ "full_add_bin" [i64, i32, i32] [i64] args m Q X)
    (hProp : ∀ args m Q X, fullPropagateSpec args m Q X →
      Γ "full_propagate" [i64] [i64] args m Q X) :
    ∀ args m Q X, fullProbeFlushHbrSpec args m Q X →
      Func.wp Γ full_probe_flush_hbr_body args m Q X := by
  rintro ⟨h_arg, hbr_n, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hlen0, hw0, hmrk0, hnd0, hext0, hdm0, hcl0, hhbr0, hm0, hQ⟩
  have hmv := c.hmaxv; unfold dimacsBound at hmv
  have hcv_le := hlen0.core_ok.cur_vars_le
  have hbr_le_mv : hbr_n.toNat ≤ c.max_vars := Nat.le_trans hhbr0.1 hcv_le
  pt_steps_nogrp
  let flushLoopInv : Tup Val [i64] → Mem 64 → Prop := fun (i_v, ()) ml =>
    i_v.toNat ≤ hbr_n.toNat ∧ ∃ st : FullState,
      st.LengthsOk c ∧ FullWitnessInv c F0 F_cur st.core ∧ FullMrkZero c st ∧
      FullArenaVarsNodup st ∧ FullExtScratchOk c st ∧ st.core.dense_mode = 0#64 ∧
      st.core.cur_level = 0 ∧ st.core.cur_vars = s.core.cur_vars ∧
      st.core.fuel.toNat ≤ s.core.fuel.toNat ∧ st.core.lit_mark = s.core.lit_mark ∧
      st.scratch.work_stk1 = s.scratch.work_stk1 ∧ FullHbrBufOkW F_cur st hbr_n.toNat ∧
      (FullMem c st ⋆ R) ml
  let flushMeas : Tup Val [i64] → Mem 64 → Nat := fun (i_v, ()) _ => hbr_n.toNat - i_v.toNat
  refine wp_loop_inv flushLoopInv flushMeas (fun Js hJs => ?_)
    (fun Js (i_v, ()) ml ⟨hi_le, st, hlen, hw, hmrk, hnd, hext, hdm, hcl, hcv, hfu, hlm, hws1,
      hhbr, hml⟩ hJs => ?_)
  · pt_steps_nogrp
    exact hJs (0#64, ()) m ⟨Nat.zero_le _, s, hlen0, hw0, hmrk0, hnd0, hext0, hdm0, hcl0, rfl,
      Nat.le_refl _, rfl, rfl, hhbr0, hm0⟩
  · have hws2_len := hlen.scratch_ok.work_stk2_len
    pt_steps_nogrp
    · have hi_lt : i_v.toNat < hbr_n.toNat := by pt_bound
      have hi2_lt : 2 * i_v.toNat + 1 < 2 * c.max_vars := by omega
      have hi_shl : (i_v <<< 1).toNat = 2 * i_v.toNat := by
        rw [show (1 : Nat) = (1#64).toNat from rfl]; exact bv64_shl1_toNat (by omega)
      have hi_shl1 : (i_v <<< 1 + 1).toNat = 2 * i_v.toNat + 1 := by
        rw [show (1 : BitVec 64) = 1#64 from rfl, bv64_add1_toNat (by rw [hi_shl]; omega), hi_shl]
      have hi_shl_w : (i_v <<< 1).toNat < st.scratch.work_stk2.length := by
        rw [hws2_len, hi_shl]; exact Nat.lt_of_succ_lt hi2_lt
      have hi_shl1_w : (i_v <<< 1 + 1).toNat < st.scratch.work_stk2.length := by
        rw [hws2_len, hi_shl1]; exact hi2_lt
      obtain ⟨ha_lt, hb_lt, hent_ab⟩ := hhbr.2 i_v.toNat hi_lt
      have ha_eq : (st.scratch.work_stk2[(i_v <<< 1).toNat]'hi_shl_w).toNat =
          (st.scratch.work_stk2[2 * i_v.toNat]?.getD 0#32).toNat := by
        have hg : some (st.scratch.work_stk2[(i_v <<< 1).toNat]'hi_shl_w) =
            some (st.scratch.work_stk2[2 * i_v.toNat]'(by rw [hws2_len]; omega)) := by
          rw [← List.getElem?_eq_getElem hi_shl_w, hi_shl,
            List.getElem?_eq_getElem (by rw [hws2_len]; omega)]
        rw [Option.some_inj.mp hg, List.getElem?_eq_getElem (by omega), Option.getD_some]
      have hb_eq : (st.scratch.work_stk2[(i_v <<< 1 + 1).toNat]'hi_shl1_w).toNat =
          (st.scratch.work_stk2[2 * i_v.toNat + 1]?.getD 0#32).toNat := by
        have hg : some (st.scratch.work_stk2[(i_v <<< 1 + 1).toNat]'hi_shl1_w) =
            some (st.scratch.work_stk2[2 * i_v.toNat + 1]'(by rw [hws2_len]; omega)) := by
          rw [← List.getElem?_eq_getElem hi_shl1_w, hi_shl1,
            List.getElem?_eq_getElem (by rw [hws2_len]; omega)]
        rw [Option.some_inj.mp hg, List.getElem?_eq_getElem (by omega), Option.getD_some]
      pt_steps_nogrp
      c0_call hAddBin
      refine ⟨c, F0, F_cur, st, R, rfl, hlen, hw, hcl, fun _ _ => by
          simpa only [ha_eq, hb_eq] using hent_ab, hml, ?_⟩
      dsimp only
      intro ar vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec' wstk' wlen' wu' nb' oom'
        inc' phases' wsort' ma hlen_a hw_a har_dom har20 har2 hma
      let st_a : FullState :=
        { st with
          core := { st.core with
            vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
            trail_pos := tp', trail_end := te', unassigned := unass', unflushed := unfl',
            wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu', num_binary := nb',
            oom := oom', inconsistent := inc' }
          scratch := { st.scratch with phases := phases', wsort := wsort' } }
      have hnd_a := fullArenaVarsNodup_of_arena_eq hnd rfl rfl
      have hext_a : FullExtScratchOk c st_a :=
        ⟨fullLastLearnedWf_of_refs_eq hext.1 rfl rfl, hext.2⟩
      have hhbr_a := fullHbrBufOkW_congr hhbr (s' := st_a) rfl rfl
      pt_steps_nogrp
      · have har_eq20 : ar = 20#64 := by pt_clear_big; exact hc
        exact hQ 20#64 st_a ma hlen_a hw_a hmrk hnd_a hext_a hdm hcl hcv hfu hlm hws1
          (Or.inr (Or.inr rfl)) (fun _ => (har20 har_eq20).1) hma
      · refine wp_join_group
          (fun () mj => ∃ st_j : FullState,
            st_j.LengthsOk c ∧ FullWitnessInv c F0 F_cur st_j.core ∧ FullMrkZero c st_j ∧
            FullArenaVarsNodup st_j ∧ FullExtScratchOk c st_j ∧ st_j.core.dense_mode = 0#64 ∧
            st_j.core.cur_level = 0 ∧ st_j.core.cur_vars = s.core.cur_vars ∧
            st_j.core.fuel.toNat ≤ s.core.fuel.toNat ∧ st_j.core.lit_mark = s.core.lit_mark ∧
            st_j.scratch.work_stk1 = s.scratch.work_stk1 ∧ FullHbrBufOkW F_cur st_j hbr_n.toNat ∧
            (FullMem c st_j ⋆ R) mj)
          (fun _ () mj ⟨st_j, hj_len, hj_w, hj_mrk, hj_nd, hj_ext, hj_dm, hj_cl, hj_cv, hj_fu,
            hj_lm, hj_ws1, hj_hbr, hm_j⟩ => by
            pt_steps_nogrp
            · exact hQ 2#64 st_j mj hj_len hj_w hj_mrk hj_nd hj_ext hj_dm hj_cl hj_cv hj_fu hj_lm
                hj_ws1 (Or.inr (Or.inl rfl)) (fun h20 => by cases h20) hm_j
            · have hi1_eq : (i_v + 1#64).toNat = i_v.toNat + 1 := bv64_add1_toNat (by omega)
              exact hJs (i_v + 1#64, ()) mj (by dsimp only [flushMeas]; rw [hi1_eq]; omega)
                ⟨by rw [hi1_eq]; omega, st_j, hj_len, hj_w, hj_mrk, hj_nd, hj_ext, hj_dm, hj_cl,
                  hj_cv, hj_fu, hj_lm, hj_ws1, hj_hbr, hm_j⟩)
          (fun Js1 hJs1 => by
            pt_steps_nogrp
            · let st_h : FullState :=
                { st_a with scratch := { st_a.scratch with hbr_cnt := st_a.scratch.hbr_cnt + 1 } }
              have hlen_h : st_h.LengthsOk c := ⟨hlen_a.core_ok, { hlen_a.scratch_ok with }⟩
              have hw_h := fullWitnessInv_congr_ctrl hw_a hlen_h.core_ok rfl rfl rfl rfl rfl rfl rfl
                rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
              exact hJs1 () m ⟨st_h, hlen_h, hw_h, hmrk,
                fullArenaVarsNodup_of_arena_eq hnd_a rfl rfl,
                ⟨fullLastLearnedWf_of_refs_eq hext_a.1 rfl rfl, hext_a.2⟩, hdm, hcl, hcv, hfu,
                hlm, hws1, fullHbrBufOkW_congr hhbr_a rfl rfl,
                by simpa only [st_h, show (1 : BitVec 64) = 1#64 from rfl] using hm⟩
            · exact hJs1 () ma ⟨st_a, hlen_a, hw_a, hmrk, hnd_a, hext_a, hdm, hcl, hcv, hfu, hlm,
                hws1, hhbr_a, hma⟩)
    · c0_call hProp
      refine ⟨c, F0, F_cur, st, R, rfl, hlen, hw, hdm, hml, ?_⟩
      dsimp only
      intro pr vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen'
        wu' fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' mp hlen_p hw_p htr_p hperm_p
        hfu_p _ _ hp1 _ _ hmp
      let st_p : FullState :=
        { st with
          core := { st.core with
            vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
            trail_pos := tp', trail_end := te', propagated := prop', unassigned := unass',
            unflushed := unfl', wvec := wvec', arena := arena', wstk := wstk', wlen := wlen',
            wusable := wu', fuel := fuel', confl_type := ctype', confl_ref := cref',
            confl_lit0 := c0', confl_lit1 := c1', oom := oom' }
          scratch := { st.scratch with
            search_ticks := ticks', wsort := wsort', phases := phases' } }
      have hnd_p : FullArenaVarsNodup st_p := fullArenaVarsNodup_of_permEq hnd hperm_p
      have hext_p : FullExtScratchOk c st_p :=
        ⟨fullLastLearnedWf_of_refs_eq hext.1 rfl hperm_p.2.1, hext.2⟩
      have hfu_ps : st_p.core.fuel.toNat ≤ s.core.fuel.toNat := by
        dsimp [st_p]; exact Nat.le_trans hfu_p hfu
      pt_steps_nogrp
      · have hp_eq1 : pr = 1#64 := by pt_clear_big; exact hc
        have hcf := (hp1 hp_eq1).2.2
        have hcl_p : st_p.core.cur_level = 0 := hcl
        have hunsat : F0.Unsat := level0_unsat_of_conflict_okW (s := st_p) hw_p hcl_p hcf
        exact hQ 20#64 st_p mp hlen_p hw_p hmrk hnd_p hext_p hdm hcl hcv hfu_ps hlm hws1
          (Or.inr (Or.inr rfl)) (fun _ => hunsat) hmp
      · exact hQ 1#64 st_p mp hlen_p hw_p hmrk hnd_p hext_p hdm hcl hcv hfu_ps hlm hws1
          (Or.inl rfl) (fun h20 => by cases h20) hmp

end LeanQbe.T.Examples.Kissat.Full