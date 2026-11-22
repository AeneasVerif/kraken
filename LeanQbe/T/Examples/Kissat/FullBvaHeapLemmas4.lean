module

public import LeanQbe.T.Examples.Kissat.FullBvaHeapCommitSpec
import LeanQbe.T.Logic.ControlComb
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Full` 3-Hop BVA — Matrix Commit Top Driver (`Part 4`)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullBvaHeap

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.C0Step LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Full
open Kraken.Bedrock2.Test
open FullBvaHeapTactics FullBvaHeapHelpers FullBvaHeapScanHelpers
open scoped FullArenaTactics FullBvaHeapTactics

theorem full_bva_commit_wp_of (Γ : Env)
    (hDefrag : ∀ args m Q X, Full.fullWstackDefragSpec args m Q X →
      Γ "full_wstack_defrag" [i64] [] args m Q X)
    (hInitFresh : ∀ args m Q X, fullInitFreshVarHeapSpec args m Q X →
      Γ "full_init_fresh_var" [i64, i32] [] args m Q X)
    (hAddBin : ∀ args m Q X, Full.fullAddBinSpec args m Q X →
      Γ "full_add_bin" [i64, i32, i32] [i64] args m Q X)
    (hAllocCl : ∀ args m Q X, Full.fullAllocClSpec args m Q X →
      Γ "full_alloc_cl" [i64, i32, i32, .bool] [i64] args m Q X)
    (hWPush : ∀ args m Q X, Full.fullWatchPushSpec args m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] args m Q X)
    (hDelBin : ∀ args m Q X, Full.fullDeleteBinarySpec args m Q X →
      Γ "full_delete_binary" [i64, i32, i32] [] args m Q X)
    (hUnwatch : ∀ args m Q X, Full.fullUnwatchLargeSpec args m Q X →
      Γ "full_unwatch_large" [i64, i32, i32] [] args m Q X)
    (hDelLoop : ∀ {Q : Post [.bool]} {X : XPost}, CommitDelLoopWp Γ Q X hDelBin hUnwatch)
    (hLargeTop : ∀ {Q : Post [.bool]} {X : XPost}, CommitLargeTopWp Γ Q X hAllocCl hWPush)
    (hTail : ∀ {Q : Post [.bool]} {X : XPost}, CommitTailWp Γ Q X hAddBin) :
    ∀ args m Q X, fullBvaCommitSpec args m Q X →
      Func.wp Γ full_bva_commit_body args m Q X := by
  rintro ⟨h, best_k, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hinv, hbk1, hbk16, hmat, hm, hQ⟩
  have hmx := c.hmaxv; have hwcap := c.hwcap; have har_b := c.harena; have hscr_b := c.hscr
  unfold dimacsBound at hmx hwcap har_b hscr_b
  have hcl := hinv.1.core_ok; have hsc := hinv.1.scratch_ok
  have hcv_le := hcl.cur_vars_le; have hsb_len := hsc.scratch_buf_len
  have hscr2304 := hmat.1
  have hbk_row := hmat.2.2.2 best_k.toNat (by omega)
  obtain ⟨hfbk_lt, hmn_lo, hmn_hi, hbk_entries⟩ := hbk_row
  have h16bk : ((16 : BitVec 32) + best_k).toNat = 16 + best_k.toNat := by c0_bound
  let mn_bv := s.scratch.scratch_buf[16 + best_k.toNat]'(by omega)
  have hmn_getD : (s.scratch.scratch_buf[16 + best_k.toNat]?.getD 0#32).toNat = mn_bv.toNat := by
    dsimp only [mn_bv]; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
  rw [hmn_getD] at hmn_lo hmn_hi hbk_entries
  have hmn_eq : s.scratch.scratch_buf[(BitVec.setWidth 64 (16 + best_k)).toNat]'(by
      rw [bv64_setWidth_32, h16bk]; omega) = mn_bv := by
    dsimp only [mn_bv]; simp only [bv64_setWidth_32, h16bk]
  c0_hsteps_nogrp
  · exact hQ false s m hinv.toDense (Nat.le_refl _) rfl rfl rfl hm
  · exact hQ false s m hinv.toDense (Nat.le_refl _) rfl rfl rfl hm
  · -- Passed `cur_vars < max_vars` and `arena_cap - arena_len >= need_ar`
    have hcv_lt : s.core.cur_vars < c.max_vars := by c0_bound
    -- Join point `Jdef` after optional `full_wstack_defrag`
    refine wp_join_state0 (α := FullState)
      (fun sd md =>
        (FullMem c sd ⋆ R) md ∧ FullDenseInvW c F0 F_cur sd ∧
        sd.core.cur_vars = s.core.cur_vars ∧ sd.core.fuel = s.core.fuel ∧
        sd.core.arena = s.core.arena ∧ sd.core.arena_len = s.core.arena_len ∧
        sd.scratch.scratch_buf = s.scratch.scratch_buf ∧
        sd.scratch.tarjan_mark = s.scratch.tarjan_mark ∧
        sd.scratch.tarjan_reach = s.scratch.tarjan_reach)
      (fun _ sd md ⟨hmd, hinvd, hcvd, hfueld, hard, hald, hsbd, htmd, htrd⟩ => ?_)
      (fun Jdef hJdef => ?_)
    · -- Main commit path: introduce fresh variable `fv = sd.core.cur_vars`
      have hcld := hinvd.1.core_ok; have hscd := hinvd.1.scratch_ok
      let old_cv := s.core.cur_vars
      have hfv_nat : (BitVec.setWidth 32 (BitVec.ofNat 64 sd.core.cur_vars)).toNat = old_cv := by
        rw [hcvd]; c0_bound
      have hcv1_nat : (BitVec.ofNat 64 sd.core.cur_vars + 1).toNat = old_cv + 1 := by
        change (BitVec.ofNat 64 sd.core.cur_vars + 1#64).toNat = _; rw [hcvd]; c0_bound
      c0_hsteps
      -- Call `full_init_fresh_var(h, fv)` on state with `cur_vars = old_cv + 1`
      let sd_inc : FullState :=
        { sd with core := { sd.core with cur_vars := old_cv + 1 } }
      have hmd_inc : (FullMem c sd_inc ⋆ R) m := by
        dsimp only [sd_inc]; rw [hcv1_nat] at hm; exact hm
      c0_call hInitFresh
      refine ⟨c, sd_inc, R, rfl,
        ⟨{ hcld with
             cur_vars_ge := by have := hcld.cur_vars_ge; dsimp only [sd_inc, old_cv]; omega,
             cur_vars_le := by dsimp only [sd_inc, old_cv]; omega,
             trail_end_le := by have := hcld.trail_end_le; dsimp only [sd_inc, old_cv]; omega },
         hscd⟩,
        by dsimp only [sd_inc, old_cv]; rw [hfv_nat]; omega, hmd_inc,
        fun vals' mrk' fl' lvl' rsns' wvec' unass' sc' m1 hlen1 hext1 hsb1 hws1 htm1 htr1 hss1
          hv0 hv1 hv_oth hm0 hm_oth hl0 hl_oth hr0 hr_oth hw0 hw_oth hm1 => ?_⟩
      -- Construct `F_next = bvaExtendGen old_cv L Qs F_cur`
      let dm := best_k.toNat + 1
      let L : List Nat := (List.range dm).map fun t => (s.scratch.scratch_buf[t]?.getD 0#32).toNat
      let resAt (idx : Nat) : List Nat :=
        if h : idx < mn_bv.toNat then Classical.choose (hbk_entries idx h) else []
      let Qs : List (List Nat) := (List.range mn_bv.toNat).map resAt
      have hL_lt : ∀ f ∈ L, f < 2 * old_cv := by
        intro f hf; obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hf
        rw [List.mem_range] at ht; exact (hmat.2.2.2 t (by omega)).1
      have hQ_lt : ∀ C ∈ Qs, ∀ l ∈ C, l < 2 * old_cv := by
        intro C hC l hl; obtain ⟨idx, hidx, rfl⟩ := List.mem_map.mp hC
        rw [List.mem_range] at hidx; dsimp only [resAt] at hl; rw [dite_eq_left hidx] at hl
        exact (Classical.choose_spec (hbk_entries idx hidx)).1 l hl
      have hprod : ∀ f ∈ L, ∀ C ∈ Qs, (cnfOfClauses F_cur).EntailsClause (cnfClause (f :: C)) := by
        intro f hf C hC
        obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hf; rw [List.mem_range] at ht
        obtain ⟨idx, hidx, rfl⟩ := List.mem_map.mp hC; rw [List.mem_range] at hidx
        dsimp only [resAt]; rw [dite_eq_left hidx]
        exact (Classical.choose_spec (hbk_entries idx hidx)).2.2.2.1 t (by omega)
      let F_next := bvaExtendGen old_cv L Qs F_cur
      let s1 : FullState :=
        { sd_inc with
          core := { sd_inc.core with vals := vals', mrk := mrk', flags := fl', lvl := lvl',
                                     rsns := rsns', wvec := wvec', unassigned := unass' }
          scratch := sc' }
      have hcore1 : s1.core =
          { sd.core with cur_vars := sd.core.cur_vars + 1, vals := vals', mrk := mrk',
                         flags := fl', lvl := lvl', rsns := rsns', wvec := wvec',
                         unassigned := unass' } := by
        dsimp only [s1, sd_inc, old_cv]; rw [hcvd]
      have ⟨hw1, hd1⟩ := fullDenseInv_add_fresh_var_gen (s := sd) (s' := s1)
        hinvd.1 hinvd.2.1 hinvd.2.2.1 hinvd.2.2.2.1 hinvd.2.2.2.2.1 hinvd.2.2.2.2.2.1
        hinvd.2.2.2.2.2.2 (by rw [hcvd]; exact hcv_lt)
        (by rw [hcvd]; exact hL_lt) (by rw [hcvd]; exact hQ_lt) hprod
        hlen1 hcore1
        (by rw [hfv_nat] at hv0; rwa [hcvd])
        (by rw [hfv_nat] at hv1; rwa [hcvd])
        (by intro l hl hne; exact hv_oth l hl (by rw [hfv_nat]; dsimp only [old_cv]; rwa [← hcvd]))
        (by rw [hfv_nat] at hm0; rwa [hcvd])
        (by intro v hv hne; exact hm_oth v hv (by rw [hfv_nat]; dsimp only [old_cv]; rwa [← hcvd]))
        (by intro v hv hne; exact hl_oth v hv (by rw [hfv_nat]; dsimp only [old_cv]; rwa [← hcvd]))
        (by intro v hv hne; exact hr_oth v hv (by rw [hfv_nat]; dsimp only [old_cv]; rwa [← hcvd]))
        (by intro k hk; rw [hfv_nat] at hw0; rw [hcvd]; exact hw0 k hk)
        (by intro i hi hne; exact hw_oth i hi (by rw [hfv_nat]; dsimp only [old_cv]; rwa [← hcvd]))
        hext1.1 hext1.2
      have hinv1 : FullDenseInvW c F0 F_next s1 :=
        ⟨hlen1, by rwa [hcvd] at hw1, hd1.2.1, hd1.2.2.1, hd1.2.2.2.1, hd1.2.2.2.2.1,
          hd1.2.2.2.2.2⟩
      have hpos_ent : ∀ f ∈ L, (cnfOfClauses F_next).EntailsClause (cnfClause [2 * old_cv, f]) :=
        fun _ hf => bvaExtendGen_entails_pos hf
      have hneg_ent : ∀ R ∈ Qs,
          (cnfOfClauses F_next).EntailsClause (cnfClause ((2 * old_cv + 1) :: R)) :=
        fun _ hR => bvaExtendGen_entails_neg hR
      -- Zero `s1[fv]`, `s2[fv]`, `cnt[fv << 1]`, `cnt[(fv << 1) | 1]`
      let fv_bv := BitVec.setWidth 32 (BitVec.ofNat 64 sd.core.cur_vars)
      have hfv_repr : 2 * (BitVec.setWidth 64 fv_bv).toNat + 1 < sd.core.repr.length := by
        rw [bv64_setWidth_32, hfv_nat, hcld.repr_len]; omega
      have hfv_sig : (BitVec.setWidth 64 fv_bv).toNat < sc'.sim_sig.length := by
        rw [bv64_setWidth_32, hfv_nat, hlen1.scratch_ok.sim_sig_len]; omega
      have hfv2_ws : (BitVec.setWidth 64 (fv_bv <<< (1 : Nat))).toNat < sc'.wsort.length := by
        rw [bv64_setWidth_32, bv32_shl1_nat, hfv_nat, Nat.mod_eq_of_lt (by omega),
          hlen1.scratch_ok.wsort_len]; omega
      have hfv21_ws : (BitVec.setWidth 64 ((fv_bv <<< (1 : Nat)) ||| 1#32)).toNat <
          sc'.wsort.length := by
        rw [bv64_setWidth_32, bv32_shl1_or1 (by rw [hfv_nat]; omega), hfv_nat,
          hlen1.scratch_ok.wsort_len]; omega
      have hfresh_nat : (fv_bv <<< (1 : Nat)).toNat = 2 * old_cv := by
        rw [bv32_shl1_nat, hfv_nat, Nat.mod_eq_of_lt (by omega)]
      have hfresh1_nat : ((fv_bv <<< (1 : Nat)) ^^^ 1#32).toNat = 2 * old_cv + 1 := by
        rw [bv32_shl1_xor1 (by rw [hfv_nat]; omega), hfv_nat]
      have hfresh1_bv : ((BitVec.setWidth 32 (BitVec.ofNat 64 sd.core.cur_vars) <<<
          (1 : BitVec 32)) ^^^ (1 : BitVec 32)).toNat = 2 * old_cv + 1 := by
        have hev : (fv_bv <<< (1 : BitVec 32)) = fv_bv <<< (1 : Nat) := by
          apply BitVec.eq_of_toNat_eq; rw [bv32_shl1_bv, bv32_shl1_nat]
        change ((fv_bv <<< (1 : BitVec 32)) ^^^ 1#32).toNat = _
        rw [hev]; exact hfresh1_nat
      c0_hsteps_nogrp
      -- Main `m < mn` loop: create new clause for `c_top`, then delete column `s = best_k .. 0`
      refine wp_loop_inv
        (fun (mi, ()) mm => ∃ stm : FullState,
          mi.toNat ≤ mn_bv.toNat ∧ FullDenseInvW c F0 F_next stm ∧
          stm.core.cur_vars = old_cv + 1 ∧ stm.core.fuel = s.core.fuel ∧
          stm.scratch.scratch_buf = s.scratch.scratch_buf ∧
          stm.scratch.tarjan_mark = s.scratch.tarjan_mark ∧
          stm.scratch.tarjan_reach = s.scratch.tarjan_reach ∧
          ArenaMono s.core stm.core ∧ (FullMem c stm ⋆ R) mm)
        (fun (mi, _) _ => mn_bv.toNat - mi.toNat)
        (fun Jm hJm => by
          c0_hsteps
          let st0 : FullState :=
            { core := { sd.core with
                cur_vars := old_cv + 1, vals := vals', mrk := mrk', flags := fl', lvl := lvl',
                rsns := rsns', wvec := wvec', unassigned := unass',
                repr := repr64Set sd.core.repr (BitVec.setWidth 64 fv_bv).toNat 0 }
              scratch := { sc' with
                sim_sig := sc'.sim_sig.set (BitVec.setWidth 64 fv_bv).toNat 0
                wsort := (sc'.wsort.set (BitVec.setWidth 64
                  (fv_bv <<< (OfNat.ofNat 1 : BitVec 32))).toNat 0).set
                  (BitVec.setWidth 64
                    (fv_bv <<< (OfNat.ofNat 1 : BitVec 32) ||| 1#32)).toNat 0 } }
          have hinv2 : FullDenseInvW c F0 F_next st0 :=
            fullDenseInv_with_core_aux (tc' := sd.core.tmp_cnt) (tl' := sd.core.tmp_len)
              hinv1 (by rw [repr64Set_length, hcld.repr_len]) hcld.min_clr_len_arr hcld.tmp_len_arr
              hlen1.core_ok.flags_len hcld.tmp_len_le
              { hlen1.scratch_ok with
                sim_sig_len := by simp [hlen1.scratch_ok.sim_sig_len]
                wsort_len := by simp [hlen1.scratch_ok.wsort_len] } rfl rfl
          refine hJm (0#32, ()) _ ⟨st0, Nat.zero_le _, hinv2, rfl, hfueld, hsb1.trans hsbd,
            htm1.trans htmd, htr1.trans htrd, ?_, hm⟩
          intro r hr
          change r ∈ fullArenaClauseRefsCore { sd.core with arena := sd.core.arena } ∧ _
          have h1 : fullArenaClauseRefsCore { sd.core with arena := sd.core.arena } =
              fullArenaClauseRefsCore s.core := by
            unfold fullArenaClauseRefsCore; rw [hard, hald]
          refine ⟨by rw [h1]; exact hr, ?_, ?_⟩
          · unfold fullArenaClauseSizeCore; rw [hard]
          · unfold fullArenaClauseLitsCore fullArenaClauseSizeCore; rw [hard])
        (fun Jm (mi, ()) mm ⟨stm, hmi_le, hinvm, hcvm, hfuelm, hsbm, htmm, htrm, hmono, hmm⟩
            ihm => ?_)
      have hclm := hinvm.1.core_ok; have hscm := hinvm.1.scratch_ok
      c0_hsteps
      · -- Body of `while (mi < mn)`
        have h16bk_mod : (BitVec.toNat (16 : BitVec 32) + best_k.toNat) % 2 ^ 32 =
            16 + best_k.toNat := by
          rw [show BitVec.toNat (16 : BitVec 32) = 16 from rfl]; omega
        have hmi_lt : mi.toNat < mn_bv.toNat := by
          have h1 : mi.toNat < (s.scratch.scratch_buf[(BitVec.toNat (16 : BitVec 32) +
              best_k.toNat) % 2 ^ 32]'(by rw [h16bk_mod]; omega)).toNat := by assumption
          simpa only [mn_bv, h16bk_mod] using h1
        have hmi1 : (mi + 1#32).toNat = mi.toNat + 1 := by c0_bound
        have hctop_idx : (64 + best_k * 64 + mi).toNat =
            64 + best_k.toNat * 64 + mi.toNat := by
          change (64#32 + best_k * 64#32 + mi).toNat = _; c0_bound
        have hctop_sb : (BitVec.setWidth 64 (64 + best_k * 64 + mi)).toNat <
            stm.scratch.scratch_buf.length := by
          rw [bv64_setWidth_32, hctop_idx, hscm.scratch_buf_len]; omega
        let c_top := s.scratch.scratch_buf[64 + best_k.toNat * 64 + mi.toNat]'(by omega)
        have hctop_eq : stm.scratch.scratch_buf[(BitVec.setWidth 64
            (64 + best_k * 64 + mi)).toNat]'hctop_sb = c_top := by
          dsimp only [c_top]; simp only [hsbm, bv64_setWidth_32, hctop_idx]
        have hctop_mod_n : (64 + best_k.toNat * 64 + mi.toNat) % 2 ^ 32 =
            64 + best_k.toNat * 64 + mi.toNat := Nat.mod_eq_of_lt (by omega)
        have hctop_mod : stm.scratch.scratch_buf[(BitVec.toNat (64 : BitVec 32) +
            best_k.toNat * BitVec.toNat (64 : BitVec 32) + mi.toNat) % 2 ^ 32]'(by
            rw [show BitVec.toNat (64 : BitVec 32) = 64 from rfl, hctop_mod_n,
              hscm.scratch_buf_len]; omega) = c_top := by
          dsimp only [c_top]
          simp only [hsbm, show BitVec.toNat (64 : BitVec 32) = 64 from rfl, hctop_mod_n]
        have hres_spec := Classical.choose_spec (hbk_entries mi.toNat hmi_lt)
        let resm := resAt mi.toNat
        have hresm_eq : resm = Classical.choose (hbk_entries mi.toNat hmi_lt) := by
          dsimp only [resm, resAt]; rw [dite_eq_left hmi_lt]
        have hresm_in_Qs : resm ∈ Qs :=
          List.mem_map.mpr ⟨mi.toNat, List.mem_range.mpr hmi_lt, rfl⟩
        have hresm_ent : (cnfOfClauses F_next).EntailsClause
            (cnfClause ((2 * old_cv + 1) :: resm)) := hneg_ent resm hresm_in_Qs
        obtain ⟨hresm_lt, hresm_nd, hctop_ok, _, _⟩ := hres_spec
        rw [← hresm_eq] at hresm_lt hresm_nd hctop_ok
        have hctop_getD : s.scratch.scratch_buf[64 + best_k.toNat * 64 + mi.toNat]?.getD 0#32 =
            c_top := by
          dsimp only [c_top]; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
        rw [hctop_getD] at hctop_ok
        c0_hsteps_nogrp
        -- Join point `Jtop` after `if (c_top & BIN)` -> countdown deletion `s = best_k .. 0`
        refine wp_join_state0 (α := FullState)
          (fun st1 m1 =>
            (FullMem c st1 ⋆ R) m1 ∧ FullDenseInvW c F0 F_next st1 ∧
            st1.core.cur_vars = old_cv + 1 ∧ st1.core.fuel = s.core.fuel ∧
            st1.scratch.scratch_buf = s.scratch.scratch_buf ∧
            st1.scratch.tarjan_mark = s.scratch.tarjan_mark ∧
            st1.scratch.tarjan_reach = s.scratch.tarjan_reach ∧ ArenaMono s.core st1.core)
          (fun _ st1 m1 ⟨hm1, hinv1, hcv1, hfuel1, hsb1, htm1, htr1, hmono1⟩ => ?_)
          (fun Jtop hJtop => ?_)
        · -- Countdown deletion loop `s = best_k .. 0` (delegated to `commit_del_loop_wp`)
          have hdel := hDelLoop (Q := Q) (X := X)
            (F_next := F_next) (Jm := Jm)
            hinv hbk1 hbk16 hmat (by rw [hmn_getD]; exact hmi_lt)
            hm1 hinv1 hcv1 hfuel1 hsb1 htm1 htr1 hmono1
            (fun st2 m2 hinv2 hcv2 hfuel2 hsb2 htm2 htr2 hmono2 hm2 =>
              ihm (mi + 1#32, ()) m2 (by dsimp only; rw [hmi1]; omega)
                ⟨st2, by rw [hmi1]; omega, hinv2, hcv2, hfuel2, hsb2, htm2, htr2, hmono2, hm2⟩)
          dsimp only [commitDelLoopExpr, eSteps, eStep, eLoad64, eGrp0_0, eGrp0_1, eThen, eElse,
            full_bva_commit_body] at hdel
          exact hdel
        · -- Branch `c_top` binary vs large
          c0_hsplit
          · -- Binary `c_top`: `full_add_bin(h, fresh ^ 1, c_top & 0x7FFFFFFF)`
            c0_hsteps
            have hbin_ct : (c_top &&& 0x80000000#32) ≠ 0#32 := by
              simpa only [← hctop_mod] using (by assumption : _)
            unfold BvaRowEntryOk at hctop_ok; rw [ite_eq_left hbin_ct] at hctop_ok
            obtain ⟨_, hres_q, _⟩ := hctop_ok
            c0_call hAddBin
            refine ⟨c, F0, F_next, stm, R, rfl, hinvm.1, hinvm.2.1, hinvm.2.2.2.2.2.1,
              fun _ _ => ?_, hmm,
              fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 hlen1' hw1' _ _ _ hm1' => ?_⟩
            · rw [hctop_eq]; rw [hres_q] at hresm_ent
              have hfx : (BitVec.setWidth 32 (BitVec.ofNat 64 sd.core.cur_vars) <<<
                  (OfNat.ofNat 1 : Nat) ^^^ (1 : BitVec 32)).toNat = 2 * old_cv + 1 :=
                hfresh1_nat
              simpa only [hfx, show (2147483647 : BitVec 32) = 0x7FFFFFFF#32 from rfl]
                using hresm_ent
            · exact hJtop _ m1 ⟨hm1', fullDenseInvW_of_addBin hinvm hlen1' hw1', hcvm, hfuelm,
                hsbm, htmm, htrm, hmono⟩
          · -- Large `c_top` (delegated to `commit_large_top_wp`)
            have hbin_ct : (c_top &&& 0x80000000#32) = 0#32 := by
              simpa only [← hctop_mod] using (by assumption : _)
            unfold BvaRowEntryOk at hctop_ok; rw [ite_eq_right (fun h' => h' hbin_ct)] at hctop_ok
            obtain ⟨hct_ref0, hct_ng0, hct_sz3, hct_sz5, hfbk_mem, hres_perm_f, _⟩ := hctop_ok
            have hlt := hLargeTop (Q := Q) (X := X)
              (F_next := F_next) (c_top := stm.scratch.scratch_buf[(BitVec.setWidth 64
                (64 + best_k * 64 + mi)).toNat]'hctop_sb)
              (fresh := fv_bv <<< (OfNat.ofNat 1 : BitVec 32)) (Jtop := Jtop)
              hinv hbk16 hscr2304 hfresh1_bv hresm_lt hresm_nd hresm_ent
              (by rwa [hctop_eq]) (by rwa [hctop_eq]) (by rwa [hctop_eq]) (by rwa [hctop_eq])
              (by rwa [hctop_eq]) (by rwa [hctop_eq])
              hmm hinvm hcvm hfuelm hsbm htmm htrm hmono
              (fun st1 m1 hm1 hinv1 hcv1 hfuel1 hsb1 htm1 htr1 hmono1 =>
                hJtop st1 m1 ⟨hm1, hinv1, hcv1, hfuel1, hsb1, htm1, htr1, hmono1⟩)
            dsimp only [commitLargeTopExpr, eSteps, eStep, eLet32, eLoad64, eLoad32, eGrp0_0,
              eGrp0_1, eGrpBody_0, eThen, eElse, full_bva_commit_body] at hlt
            exact hlt
      · -- Exit `mi < mn` loop (delegated to `commit_tail_wp`)
        have htail := hTail (Q := Q) (X := X)
          (F_next := F_next) (dm_bv := best_k + 1#32)
          (fresh := fv_bv <<< (OfNat.ofNat 1 : Nat))
          hbk16 hscr2304 (by simp only [bv_c0]; omega) hfresh_nat
          (fun t ht => hL_lt _ (List.mem_map.mpr ⟨t, List.mem_range.mpr ht, rfl⟩))
          (fun t ht => hpos_ent _ (List.mem_map.mpr ⟨t, List.mem_range.mpr ht, rfl⟩))
          hinvm hcvm hfuelm hsbm htmm htrm hmm hQ
        dsimp only [commitTailExpr, eSteps, eStep, eLet32, eLoad64, eGrp0_0, eGrp0_1, eElse,
          full_bva_commit_body] at htail
        exact htail
    · -- Defrag branch `if (h->wcap - h->wlen < need_w)`
      c0_hsteps_nogrp
      · -- `wcap - wlen < need_w`: try `full_wstack_defrag`, recheck, maybe zero `cnt` & ret false
        refine wp_join_state0 (α := FullState)
          (fun sd md =>
            (FullMem c sd ⋆ R) md ∧ FullDenseInvW c F0 F_cur sd ∧
            sd.core.cur_vars = s.core.cur_vars ∧ sd.core.fuel = s.core.fuel ∧
            sd.core.arena = s.core.arena ∧ sd.core.arena_len = s.core.arena_len ∧
            sd.scratch.scratch_buf = s.scratch.scratch_buf ∧
            sd.scratch.tarjan_mark = s.scratch.tarjan_mark ∧
            sd.scratch.tarjan_reach = s.scratch.tarjan_reach)
          (fun _ sd md ⟨hmd, hinvd, hcvd, hfueld, hard, hald, hsbd, htmd, htrd⟩ => ?_)
          (fun Jd1 hJd1 => ?_)
        · c0_hsplit
          · -- Still not enough watch space: zero `cnt[0..2*cur_vars)` and return `false`
            c0_hsteps_nogrp
            have h2cv : (BitVec.ofNat 64 sd.core.cur_vars <<< (1 : Nat)).toNat =
                2 * s.core.cur_vars := by rw [hcvd]; simp only [bv_c0]; omega
            refine wp_loop_inv
              (fun (zi, ()) mzi => ∃ wsz : List (BitVec 32),
                zi.toNat ≤ 2 * s.core.cur_vars ∧ wsz.length = 2 * c.max_vars ∧
                (FullMem c { sd with scratch := { sd.scratch with wsort := wsz } } ⋆ R) mzi)
              (fun (zi, _) _ => 2 * s.core.cur_vars - zi.toNat)
              (fun Jz hJz => by
                c0_hfast; exact hJz (0#64, ()) md ⟨sd.scratch.wsort, Nat.zero_le _,
                  hinvd.1.scratch_ok.wsort_len, hmd⟩)
              (fun Jz (zi, ()) mzi ⟨wsz, hzi_le, hwsz_l, hmzi⟩ ihz => ?_)
            c0_hsplit
            · have hzi_lt : zi.toNat < 2 * s.core.cur_vars := by
                have h1 : zi.toNat < (BitVec.ofNat 64 sd.core.cur_vars <<< (1 : Nat)).toNat :=
                  by assumption
                rwa [h2cv] at h1
              have hzi1 : (zi + 1#64).toNat = zi.toNat + 1 := by simp only [bv_c0]; omega
              c0_hfast
              exact ihz (zi + 1#64, ()) m (by dsimp only; rw [hzi1]; omega)
                ⟨_, by rw [hzi1]; omega, by simp [hwsz_l], hm⟩
            · c0_hfast
              exact hQ false _ mzi (fullDenseInvW_set_wsort hinvd hwsz_l).toDense
                (by dsimp only; omega) hfueld htmd htrd hmzi
          · c0_hfast; exact hJdef sd md ⟨hmd, hinvd, hcvd, hfueld, hard, hald, hsbd, htmd, htrd⟩
        · c0_hsplit
          · c0_hsteps
            c0_call hDefrag
            refine ⟨c, s, R, rfl, hinv.1, hinv.2.1.watches.layout, hm,
              fun wvec' wstk' wlen' wsort' md hlen' hlay' _ hsl' hmd =>
                hJd1 _ md ⟨hmd, fullDenseInvW_of_defrag hinv hlen' hlay' hsl',
                  rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
          · c0_hfast; exact hJd1 s m ⟨hm, hinv, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · c0_hfast; exact hJdef s m ⟨hm, hinv, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end LeanQbe.T.Examples.Kissat.FullBvaHeap
