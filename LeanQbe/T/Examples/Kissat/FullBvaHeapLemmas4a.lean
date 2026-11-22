module

public import LeanQbe.T.Examples.Kissat.FullBvaHeapCommitSpec
import LeanQbe.T.Logic.ControlComb
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Full` 3-Hop BVA — Matrix Commit Large-Clause Sub-Proof (`Part 4a`)
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

theorem commit_large_top_wp {Γ : Env} {Q : Post [.bool]} {X : XPost}
    (hAllocCl : ∀ args m Q X, Full.fullAllocClSpec args m Q X →
      Γ "full_alloc_cl" [i64, i32, i32, .bool] [i64] args m Q X)
    (hWPush : ∀ args m Q X, Full.fullWatchPushSpec args m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] args m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur F_next : List (List Nat)} {s stm : FullState}
    {R : Mem 64 → Prop} {best_k c_top fresh : Val i32} {Jtop : Cont []} {mm : Mem 64}
    {resm : List Nat}
    (hinv : FullDenseInvW c F0 F_cur s)
    (hbk16 : best_k.toNat < 16) (hscr2304 : 2304 ≤ c.scratch_cap)
    (hfresh1 : (fresh ^^^ 1#32).toNat = 2 * s.core.cur_vars + 1)
    (hresm_lt : ∀ x ∈ resm, x < 2 * s.core.cur_vars)
    (hresm_nd : (resm.map (· / 2)).Nodup)
    (hresm_ent : (cnfOfClauses F_next).EntailsClause
      (cnfClause ((2 * s.core.cur_vars + 1) :: resm)))
    (hct_ref0 : c_top.toNat ∈ fullArenaClauseRefsCore s.core)
    (hct_ng0 : fullArenaClauseGarbCore s.core c_top.toNat = false)
    (hct_sz3 : 3 ≤ fullArenaClauseSizeCore s.core c_top.toNat)
    (hct_sz5 : fullArenaClauseSizeCore s.core c_top.toNat ≤ 5)
    (hfbk_mem : (s.scratch.scratch_buf[best_k.toNat]?.getD 0#32).toNat ∈
      fullArenaClauseLitsCore s.core c_top.toNat)
    (hres_perm_f : resm.Perm ((fullArenaClauseLitsCore s.core c_top.toNat).filter
      (· != (s.scratch.scratch_buf[best_k.toNat]?.getD 0#32).toNat)))
    (hmm : (FullMem c stm ⋆ R) mm) (hinvm : FullDenseInvW c F0 F_next stm)
    (hcvm : stm.core.cur_vars = s.core.cur_vars + 1) (hfuelm : stm.core.fuel = s.core.fuel)
    (hsbm : stm.scratch.scratch_buf = s.scratch.scratch_buf)
    (htmm : stm.scratch.tarjan_mark = s.scratch.tarjan_mark)
    (htrm : stm.scratch.tarjan_reach = s.scratch.tarjan_reach)
    (hmono : ArenaMono s.core stm.core)
    (hDone : ∀ st1 m1,
      (FullMem c st1 ⋆ R) m1 → FullDenseInvW c F0 F_next st1 →
      st1.core.cur_vars = s.core.cur_vars + 1 → st1.core.fuel = s.core.fuel →
      st1.scratch.scratch_buf = s.scratch.scratch_buf →
      st1.scratch.tarjan_mark = s.scratch.tarjan_mark →
      st1.scratch.tarjan_reach = s.scratch.tarjan_reach →
      ArenaMono s.core st1.core → Jtop () m1) :
    wp Γ Q X (commitLargeTopExpr c.hdr c.pArena c.pScratchBuf c.pFlags c.pTmp
      best_k c_top fresh Jtop) mm := by
  have hmx := c.hmaxv; have har_b := c.harena; have hscr_b := c.hscr
  unfold dimacsBound at hmx har_b hscr_b
  have hcl := hinv.1.core_ok; have hsc := hinv.1.scratch_ok
  have hclm := hinvm.1.core_ok; have hscm := hinvm.1.scratch_ok
  have hcv_le := hclm.cur_vars_le; have hsb_len := hsc.scratch_buf_len
  let old_cv := s.core.cur_vars
  obtain ⟨hct_refm, hct_szm, hct_litsm⟩ := hmono c_top.toNat hct_ref0
  have hct_wfm := hinvm.2.1.arena.refs_wf c_top.toNat hct_refm
  have hct_sz_eq : (stm.core.arena[c_top.toNat + 2]'(by
      have := hclm.arena_len_le; have := hclm.arena_len_arr; omega)).toNat =
      fullArenaClauseSizeCore s.core c_top.toNat := by
    rw [← hct_szm]; unfold fullArenaClauseSizeCore
    rw [List.getElem?_eq_getElem (by
      have := hclm.arena_len_le; have := hclm.arena_len_arr; omega), Option.getD_some]
  let csz_bv := stm.core.arena[c_top.toNat + 2]'(by
    have := hclm.arena_len_le; have := hclm.arena_len_arr; omega)
  have hcsz_s : csz_bv.toNat = fullArenaClauseSizeCore s.core c_top.toNat := hct_sz_eq
  let C_lits := fullArenaClauseLitsCore s.core c_top.toNat
  have hC_len : C_lits.length = csz_bv.toNat := by
    rw [hcsz_s]; exact FullBvaFwdHelpers.fullArenaClauseLitsCore_length (by
      have := (hinv.2.1.arena.refs_wf c_top.toNat hct_ref0).2.2.1
      have := (hinv.2.1.arena.refs_wf c_top.toNat hct_ref0).2.2.2.1
      have := hcl.arena_len_le; have := hcl.arena_len_arr; omega)
  have hC_nd_vars : (C_lits.map (· / 2)).Nodup :=
    hinv.2.2.2.1 c_top.toNat hct_ref0 hct_ng0
  have hC_nd : C_lits.Nodup := nodup_of_map_div2 hC_nd_vars
  have hC_len_le_cv : csz_bv.toNat ≤ old_cv := by
    rw [← hC_len, ← List.length_map (· / 2)]
    exact nodup_lt_length_le hC_nd_vars fun v hv => by
      obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hv
      have := hinv.2.1.arena.lits_lt c_top.toNat hct_ref0 hct_ng0 l hl; omega
  let flit := s.scratch.scratch_buf[best_k.toNat]'(by omega)
  have hbk_sb : (BitVec.setWidth 64 best_k).toNat < stm.scratch.scratch_buf.length := by
    rw [bv64_setWidth_32, hscm.scratch_buf_len]; omega
  have hflit_eq : stm.scratch.scratch_buf[(BitVec.setWidth 64 best_k).toNat]'hbk_sb =
      flit := by dsimp only [flit]; simp only [hsbm, bv64_setWidth_32]
  have hfbk_mem' : flit.toNat ∈ C_lits := by
    simpa only [flit, List.getElem?_eq_getElem (by omega : best_k.toNat <
      s.scratch.scratch_buf.length), Option.getD_some] using hfbk_mem
  have hfilt_len : (C_lits.filter (· != flit.toNat)).length + 1 = csz_bv.toNat := by
    rw [← hC_len]; exact filter_ne_nodup_length hC_nd hfbk_mem'
  have hct2_n : (BitVec.setWidth 64 c_top + 2).toNat = c_top.toNat + 2 := by
    change (BitVec.setWidth 64 c_top + 2#64).toNat = _; c0_bound
  have hct2_ar : (BitVec.setWidth 64 c_top + 2).toNat < stm.core.arena.length := by
    rw [hct2_n]; have := hclm.arena_len_le; have := hclm.arena_len_arr; omega
  have htmp0_lt : 0 < stm.core.tmp.length := by rw [hclm.tmp_len_arr]; omega
  dsimp only [commitLargeTopExpr, eSteps, eStep, eLet32, eLoad64, eLoad32, eGrp0_0, eGrp0_1,
    eGrpBody_0, eThen, eElse, full_bva_commit_body]
  c0_hsteps_nogrp
  -- Loop `j < csz`: filter `C_lits` into `tmp[1..tk)`
  refine wp_loop_inv
    (fun (tk, j, ()) mj => ∃ tmpj : List (BitVec 32),
      j.toNat ≤ csz_bv.toNat ∧ tmpj.length = c.max_vars ∧
      tk.toNat = 1 + ((C_lits.take j.toNat).filter (· != flit.toNat)).length ∧
      tmpj[0]? = some (fresh ^^^ 1#32) ∧
      (∀ t, 1 ≤ t → t < tk.toNat →
        (tmpj[t]?.getD 0#32).toNat =
          ((C_lits.take j.toNat).filter (· != flit.toNat))[t - 1]?.getD 0) ∧
      (FullMem c { stm with core := { stm.core with tmp := tmpj } } ⋆ R) mj)
    (fun (_, j, _) _ => csz_bv.toNat - j.toNat)
    (fun Jf hJf => by
      c0_hsteps
      exact hJf (1#32, 0#32, ()) m ⟨_, Nat.zero_le _, by simp [hclm.tmp_len_arr],
        rfl, by rw [show (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 0)).toNat = 0 from rfl,
          List.getElem?_set_self (by rw [hclm.tmp_len_arr]; omega)]; rfl,
        fun _ h1 h2 => by simp only [bv_c0] at h2; omega, hm⟩)
    (fun Jf (tk, j, ()) mj ⟨tmpj, hj_le, htmpj_l, htk_eq, htmp0, htmp_rest, hmj⟩ ihf => ?_)
  c0_hsteps
  · -- Body of filter loop
    have hj_lt : j.toNat < csz_bv.toNat := by
      have h1 : j.toNat < (stm.core.arena[(BitVec.setWidth 64 c_top + 2).toNat]'hct2_ar).toNat :=
        by assumption
      simpa only [hct2_n] using h1
    have hj1 : (j + 1#32).toNat = j.toNat + 1 := by c0_bound
    have hctj_n : (BitVec.setWidth 64 c_top + 3 + BitVec.setWidth 64 j).toNat =
        c_top.toNat + 3 + j.toNat := by
      change (BitVec.setWidth 64 c_top + 3#64 + BitVec.setWidth 64 j).toNat = _; c0_bound
    have hctj_ar : c_top.toNat + 3 + j.toNat < stm.core.arena.length := by
      have := hclm.arena_len_le; have := hclm.arena_len_arr; omega
    have hCj_eq : C_lits[j.toNat]'(by rw [hC_len]; exact hj_lt) =
        (stm.core.arena[c_top.toNat + 3 + j.toNat]'hctj_ar).toNat := by
      have h1 := FullBvaFwdHelpers.fullArenaClauseLitsCore_getElem (k := stm.core)
        (r := c_top.toNat) (j := j.toNat) (by rw [hct_szm]; omega) hctj_ar
      rw [hct_litsm, List.getElem?_eq_getElem (by rw [hC_len]; exact hj_lt)] at h1
      exact Option.some.inj h1
    have htake_succ := FullBvaFwdHelpers.take_succ_filter_eq (l := C_lits)
      (i := j.toNat) (x := flit.toNat) (by rw [hC_len]; exact hj_lt)
    have hsub_len : ((C_lits.take (j.toNat + 1)).filter (· != flit.toNat)).length ≤
        (C_lits.filter (· != flit.toNat)).length :=
      List.Sublist.length_le (List.Sublist.filter _ (List.take_sublist _ _))
    have hctj_mod : (c_top.toNat + BitVec.toNat (3 : BitVec 64) + j.toNat) % 2 ^ 64 =
        c_top.toNat + 3 + j.toNat := by
      rw [show BitVec.toNat (3 : BitVec 64) = 3 from rfl]; omega
    c0_hsteps
    · -- `l != flit`: store `tmpj[tk] = l`, `tk++`
      have hne_bv : stm.core.arena[c_top.toNat + 3 + j.toNat]'hctj_ar ≠ flit := by
        have h1 : ¬ stm.core.arena[(c_top.toNat + BitVec.toNat (3 : BitVec 64) + j.toNat) %
            2 ^ 64]'(by rw [hctj_mod]; exact hctj_ar) =
            stm.scratch.scratch_buf[best_k.toNat]'(by rw [hscm.scratch_buf_len]; omega) :=
          by assumption
        simpa only [hctj_mod, flit, hsbm] using h1
      have hne_nat : C_lits[j.toNat]'(by rw [hC_len]; exact hj_lt) ≠ flit.toNat := by
        rw [hCj_eq]; intro h; exact hne_bv (BitVec.eq_of_toNat_eq h)
      have htk_succ_eq : ((C_lits.take (j.toNat + 1)).filter (· != flit.toNat)).length =
          ((C_lits.take j.toNat).filter (· != flit.toNat)).length + 1 := by
        rw [htake_succ, ite_eq_left (bne_iff_ne.mpr hne_nat), List.length_append]; rfl
      have htk_lt_tmp : tk.toNat < tmpj.length := by omega
      have htk1 : (tk + 1#32).toNat = tk.toNat + 1 := by c0_bound
      c0_hsteps
      refine ihf (tk + 1#32, j + 1#32, ()) m (by dsimp only; rw [hj1]; omega)
        ⟨tmpj.set tk.toNat (stm.core.arena[c_top.toNat + 3 + j.toNat]'hctj_ar),
         by rw [hj1]; omega, by simp [htmpj_l], by rw [htk1, hj1, htk_succ_eq]; omega,
         by rw [List.getElem?_set_ne (by omega)]; exact htmp0, fun t ht1 ht2 => ?_, ?_⟩
      · rw [htk1] at ht2; rw [hj1, htake_succ, ite_eq_left (bne_iff_ne.mpr hne_nat)]
        by_cases hte : t = tk.toNat
        · subst hte
          rw [List.getElem?_set_self htk_lt_tmp, Option.getD_some,
            List.getElem?_append_right (by omega),
            show tk.toNat - 1 - ((C_lits.take j.toNat).filter (· != flit.toNat)).length =
              0 by omega]
          simp [hCj_eq]
        · rw [List.getElem?_set_ne (Ne.symm hte), List.getElem?_append_left (by omega)]
          exact htmp_rest t ht1 (by omega)
      · simp only [hctj_n, bv64_setWidth_32] at hm; exact hm
    · -- `l == flit`: skip
      have heq_bv : stm.core.arena[c_top.toNat + 3 + j.toNat]'hctj_ar = flit := by
        have h1 : stm.core.arena[(c_top.toNat + BitVec.toNat (3 : BitVec 64) + j.toNat) %
            2 ^ 64]'(by rw [hctj_mod]; exact hctj_ar) =
            stm.scratch.scratch_buf[best_k.toNat]'(by rw [hscm.scratch_buf_len]; omega) :=
          by assumption
        simpa only [hctj_mod, flit, hsbm] using h1
      have heq_nat : (C_lits[j.toNat]'(by rw [hC_len]; exact hj_lt) != flit.toNat) =
          false := by rw [hCj_eq, heq_bv]; simp
      have htake_eq : (C_lits.take (j.toNat + 1)).filter (· != flit.toNat) =
          (C_lits.take j.toNat).filter (· != flit.toNat) := by
        rw [htake_succ, heq_nat]; simp
      refine ihf (tk, j + 1#32, ()) mj (by dsimp only; rw [hj1]; omega)
        ⟨tmpj, by rw [hj1]; omega, htmpj_l, by rw [hj1, htake_eq]; exact htk_eq, htmp0,
         fun t ht1 ht2 => by rw [hj1, htake_eq]; exact htmp_rest t ht1 ht2, hmj⟩
  · -- Exit filter loop: `tk = csz`, call `full_alloc_cl(h, tk, 0, false)`
    have hj_eq : j.toNat = csz_bv.toNat := by
      have h1 : ¬ j.toNat < (stm.core.arena[(BitVec.setWidth 64 c_top + 2).toNat]'hct2_ar).toNat :=
        by assumption
      have h2 : ¬ j.toNat < csz_bv.toNat := by simpa only [hct2_n] using h1
      omega
    rw [hj_eq, ← hC_len, List.take_length] at htk_eq htmp_rest
    have htk_csz : tk.toNat = csz_bv.toNat := by omega
    let st_tmp : FullState := { stm with core := { stm.core with tmp := tmpj } }
    have hinv_tmp : FullDenseInvW c F0 F_next st_tmp :=
      fullDenseInvW_set_tmp hinvm htmpj_l
    c0_call hAllocCl
    refine ⟨c, st_tmp, R, rfl, hinv_tmp.1, hmj, ?_⟩
    split
    · -- OOM (`ncr == 0xFFFFFFFFULL`)
      c0_hsteps
      exact hDone st_tmp mj hmj hinv_tmp hcvm hfuelm hsbm htmm htrm hmono
    · -- Allocated `ncr = stm.core.arena_len`
      intro ar1 ma1; dsimp only
      intro hlen_a1 hhold_a1 hns_a1 hng_a1 _ hsz_a1 hma1
      have hncr_nat :
          (BitVec.ofNat 64 stm.core.arena_len).toNat = stm.core.arena_len := by
        have := hclm.arena_len_le; c0_bound
      have hncr_ne : BitVec.ofNat 64 stm.core.arena_len ≠ 0xFFFFFFFF#64 := by
        intro h; have := congrArg BitVec.toNat h; rw [hncr_nat] at this
        have : (0xFFFFFFFF#64 : BitVec 64).toNat = 4294967295 := rfl
        have := hclm.arena_len_le; omega
      c0_hsteps_nogrp
      refine wp_join_state1 (t := i32) (α := BitVec 32 × FullState) (fun p => p.1)
        (fun ⟨_, stf⟩ mf => (FullMem c stf ⋆ R) mf ∧ FullDenseInvW c F0 F_next stf ∧
          stf.core.cur_vars = old_cv + 1 ∧ stf.core.fuel = s.core.fuel ∧
          stf.scratch.scratch_buf = s.scratch.scratch_buf ∧
          stf.scratch.tarjan_mark = s.scratch.tarjan_mark ∧
          stf.scratch.tarjan_reach = s.scratch.tarjan_reach ∧ ArenaMono s.core stf.core)
        (fun _ ⟨_, stf⟩ mf ⟨hmf, hinvf, hcvf, hfuelf, hsbf, htmf, htrf, hmonof⟩ => by
          c0_hsteps; exact hDone stf mf hmf hinvf hcvf hfuelf hsbf htmf htrf hmonof)
        (fun Jif hJif => ?_)
      c0_hsplit
      · -- Copy `tmpj[0..tk)` into `ar[ncr + 3..ncr + 3 + tk)`
        let ncr0 := stm.core.arena_len
        have hncr_cap : ncr0 + 3 + tk.toNat ≤ c.arena_cap := hlen_a1.core_ok.arena_len_le
        refine wp_loop_inv
          (fun (jc, ()) mjc => ∃ arj : List (BitVec 32),
            jc.toNat ≤ tk.toNat ∧ arj.length = c.arena_cap ∧
            (∀ i < ncr0, arj[i]? = stm.core.arena[i]?) ∧
            arj[ncr0]? = ar1[ncr0]? ∧ arj[ncr0 + 2]? = ar1[ncr0 + 2]? ∧
            (∀ t < jc.toNat, arj[ncr0 + 3 + t]? = tmpj[t]?) ∧
            (FullMem c { st_tmp with core := { st_tmp.core with
              arena := arj, arena_len := ncr0 + 3 + tk.toNat } } ⋆ R) mjc)
          (fun (jc, _) _ => tk.toNat - jc.toNat)
          (fun Jcp hJcp => by
            c0_hsteps
            exact hJcp (0#32, ()) ma1 ⟨ar1, Nat.zero_le _, hlen_a1.core_ok.arena_len_arr,
              hhold_a1, rfl, rfl, fun _ h => by simp only [bv_c0] at h; omega, hma1⟩)
          (fun Jcp (jc, ()) mjc ⟨arj, hjc_le, harj_l, hhold_j, harj0, harj2, hcp_j, hmjc⟩
              ihcp => ?_)
        c0_hsteps
        · have hjc_lt : jc.toNat < tk.toNat := by c0_bound
          have hjc1 : (jc + 1#32).toNat = jc.toNat + 1 := by c0_bound
          have hncr_jc : (BitVec.ofNat 64 st_tmp.core.arena_len + 3 +
              BitVec.setWidth 64 jc).toNat = ncr0 + 3 + jc.toNat := by
            change (BitVec.ofNat 64 ncr0 + 3#64 + BitVec.setWidth 64 jc).toNat = _
            c0_bound
          have hjc_tmp : jc.toNat < tmpj.length := by omega
          c0_hsteps
          refine ihcp (jc + 1#32, ()) m (by dsimp only; rw [hjc1]; omega)
            ⟨arj.set (ncr0 + 3 + jc.toNat) (tmpj[jc.toNat]'hjc_tmp),
             by rw [hjc1]; omega, by simp [harj_l],
             fun i hi => by rw [List.getElem?_set_ne (by omega)]; exact hhold_j i hi,
             by rw [List.getElem?_set_ne (by omega)]; exact harj0,
             by rw [List.getElem?_set_ne (by omega)]; exact harj2,
             fun t ht => by
               rw [hjc1] at ht
               by_cases hte : t = jc.toNat
               · subst hte
                 rw [List.getElem?_set_self (by omega), List.getElem?_eq_getElem hjc_tmp]
               · rw [List.getElem?_set_ne (by omega)]; exact hcp_j t (by omega),
             by simp only [hncr_jc, bv64_setWidth_32] at hm; exact hm⟩
        · -- Done copying -> push watches `jw < tk`, set `FL_FACT_*`, `num_irred++`
          have hjc_eq : jc.toNat = tk.toNat := by c0_bound
          rw [hjc_eq] at hcp_j
          let st_cp : FullState :=
            { st_tmp with core := { st_tmp.core with
              arena := arj, arena_len := ncr0 + 3 + tk.toNat } }
          have hlen_cp : st_cp.LengthsOk c :=
            ⟨{ hlen_a1.core_ok with arena_len_arr := harj_l }, hlen_a1.scratch_ok⟩
          have hns_cp : (arj[ncr0]?.getD 0#32 &&& 0x00800000#32) = 0#32 := by
            rw [harj0]; exact hns_a1
          have hsz_cp : (arj[ncr0 + 2]?.getD 0#32).toNat = tk.toNat := by
            rw [harj2]; exact hsz_a1
          have hrefs_cp : fullArenaClauseRefsCore st_cp.core =
              fullArenaClauseRefsCore stm.core ++ [ncr0] :=
            fullArenaClauseRefsCore_append hinvm.2.1.arena (by omega) rfl hhold_j hns_cp hsz_cp
          have hwat_cp : ModeWatchesInv F_next st_cp.core :=
            hinvm.2.1.watches.with_wstk rfl rfl rfl rfl rfl
              (fun r hr => by rw [hrefs_cp]; exact List.mem_append_left _ hr)
          have hnew_lits_eq :
              fullArenaClauseLitsCore { stm.core with arena := arj } ncr0 =
              (2 * old_cv + 1) :: C_lits.filter (· != flit.toNat) := by
            rw [fullArenaLitsCore_eq_map (sz := tk.toNat)
              (by unfold fullArenaClauseSizeCore; exact hsz_cp) (by dsimp only; omega)]
            apply List.ext_getElem?; intro t
            cases t with
            | zero =>
              rw [List.getElem?_map, List.getElem?_range (by omega), Option.map_some,
                Nat.add_zero, hcp_j 0 (by omega), htmp0, Option.getD_some, hfresh1]
              rfl
            | succ t' =>
              by_cases ht : t' + 1 < tk.toNat
              · rw [List.getElem?_map, List.getElem?_range ht, Option.map_some,
                  hcp_j (t' + 1) ht, htmp_rest (t' + 1) (by omega) ht, Nat.add_sub_cancel,
                  List.getElem?_cons_succ,
                  List.getElem?_eq_getElem (by omega : t' <
                    (C_lits.filter (· != flit.toNat)).length),
                  Option.getD_some]
              · rw [List.getElem?_eq_none (by simp; omega),
                  List.getElem?_eq_none (by simp; omega)]
          have hnew_perm : (fullArenaClauseLitsCore { stm.core with arena := arj }
              ncr0).Perm ((2 * old_cv + 1) :: resm) := by
            rw [hnew_lits_eq]
            have hf' : resm.Perm (C_lits.filter (· != flit.toNat)) := by
              simpa only [flit, List.getElem?_eq_getElem (by omega : best_k.toNat <
                s.scratch.scratch_buf.length), Option.getD_some] using hres_perm_f
            exact List.Perm.cons _ hf'.symm
          have hnew_lt :
              ∀ l ∈ fullArenaClauseLitsCore { stm.core with arena := arj } ncr0,
              l < 2 * stm.core.cur_vars := by
            intro l hl; rw [hcvm]
            have hl' := hnew_perm.subset hl
            rcases List.mem_cons.mp hl' with rfl | hr
            · omega
            · have := hresm_lt l hr; omega
          have hnew_nd : ((fullArenaClauseLitsCore { stm.core with arena := arj }
              ncr0).map (· / 2)).Nodup := by
            have hp := hnew_perm.map (· / 2)
            refine (List.nodup_cons.mpr ⟨?_, hresm_nd⟩).perm hp.symm
            intro hmem; obtain ⟨x, hx, hdiv⟩ := List.mem_map.mp hmem
            have := hresm_lt x hx; dsimp only [old_cv] at *; omega
          have hnew_ent : (cnfOfClauses F_next).EntailsClause
              (cnfClause (fullArenaClauseLitsCore { stm.core with arena := arj } ncr0)) :=
            clause_entails_of_perm hnew_perm.symm hresm_ent
          have htmp_lt :
              ∀ t (ht : t < tk.toNat), (tmpj[t]'(by omega)).toNat < 2 * (old_cv + 1) := by
            intro t ht
            have hmem : (tmpj[t]'(by omega)).toNat ∈
                fullArenaClauseLitsCore { stm.core with arena := arj } ncr0 := by
              rw [fullArenaLitsCore_eq_map (sz := tk.toNat)
                (by unfold fullArenaClauseSizeCore; exact hsz_cp) (by dsimp only; omega)]
              refine List.mem_map.mpr ⟨t, List.mem_range.mpr ht, ?_⟩
              rw [hcp_j t ht, List.getElem?_eq_getElem (by omega), Option.getD_some]
            simpa only [hcvm] using hnew_lt _ hmem
          -- Watch-push loop `jw < tk`
          refine wp_loop_inv
            (fun (jw, ()) mjw => ∃ wvecw wstkw flw wsortw wlenw wuw,
              jw.toNat ≤ tk.toNat ∧
              let sw : FullState :=
                { st_cp with
                  core := { st_cp.core with wvec := wvecw, wstk := wstkw, wlen := wlenw,
                                            wusable := wuw, flags := flw }
                  scratch := { st_cp.scratch with wsort := wsortw } }
              sw.LengthsOk c ∧ ModeWatchesInv F_next sw.core ∧ (FullMem c sw ⋆ R) mjw)
            (fun (jw, _) _ => tk.toNat - jw.toNat)
            (fun Jw hJw => by
              c0_hsteps
              exact hJw (0#32, ()) mjc
                ⟨st_cp.core.wvec, st_cp.core.wstk, st_cp.core.flags,
                 st_cp.scratch.wsort, st_cp.core.wlen, st_cp.core.wusable, Nat.zero_le _,
                 hlen_cp, hwat_cp, hmjc⟩)
            (fun Jw (jw, ()) mjw ⟨wvecw, wstkw, flw, wsortw, wlenw, wuw, hjw_le, hlenw,
                hwatw, hmjw⟩ ihw => ?_)
          let sw : FullState :=
            { st_cp with
              core := { st_cp.core with wvec := wvecw, wstk := wstkw, wlen := wlenw,
                                        wusable := wuw, flags := flw }
              scratch := { st_cp.scratch with wsort := wsortw } }
          c0_hsteps
          · have hjw_lt : jw.toNat < tk.toNat := by c0_bound
            have hjw1 : (jw + 1#32).toNat = jw.toNat + 1 := by c0_bound
            have hjw_tmp : jw.toNat < tmpj.length := by omega
            have hjw_tmp_sw : (BitVec.setWidth 64 jw).toNat < sw.core.tmp.length := by
              rw [bv64_setWidth_32]; exact hjw_tmp
            have htk_mask : (tk &&& (2147483647 : BitVec 32)) = tk :=
              bv32_lit_mask_eq (by omega)
            have htk_ne : (tk &&& (2147483647 : BitVec 32)) ≠ 0xFFFFFFFF#32 := by
              rw [htk_mask]; intro h; have := congrArg BitVec.toNat h
              have : (0xFFFFFFFF#32 : BitVec 32).toNat = 2 ^ 32 - 1 := rfl; omega
            have hncr32_nat :
                (BitVec.setWidth 32 (BitVec.ofNat 64 ncr0)).toNat = ncr0 := by
              have := hclm.arena_len_le; c0_bound
            have hncr32_ne :
                BitVec.setWidth 32 (BitVec.ofNat 64 ncr0) ≠ 0xFFFFFFFF#32 := by
              intro h; have := congrArg BitVec.toNat h; rw [hncr32_nat] at this
              have := hclm.arena_len_le
              have : (0xFFFFFFFF#32 : BitVec 32).toNat = 2 ^ 32 - 1 := rfl; omega
            c0_hsteps
            c0_call hWPush
            refine ⟨c, sw, R, rfl, hlenw, hwatw.layout, (fun h => absurd h (by decide)),
              (fun _ => ⟨htk_ne, hncr32_ne⟩), hmjw,
              fun okw wvec' wstk' wlen' wu' wsort' mw' hlenw' hlayw' hothw hokt hokf
                  hmw' => ?_⟩
            have hwatw' : ModeWatchesInv F_next
                { sw.core with wvec := wvec', wstk := wstk', wlen := wlen',
                               wusable := wu' } := by
              refine fullWatchPush_preserves_modeWatchesInv (cnt := 2#32) hwatw hlayw'
                rfl rfl (fun _ hr => hr) (fun h => absurd h (by decide)) ?_ hothw hokt
                (fun hf => (hokf hf).1)
              intro _
              have htk_nb : (tk &&& 0x80000000#32) = 0#32 := by
                apply BitVec.eq_of_toNat_eq; change tk.toNat &&& 2147483648 = 0
                match h : tk.toNat, (by omega : tk.toNat ≤ 5) with
                | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ => rfl
                | _ + 6, hle => omega
              refine ⟨by rw [htk_mask]; exact htk_nb,
                fun _ => by rw [htk_mask]; omega,
                by rw [hncr32_nat]; have := hclm.arena_len_le; omega, ?_⟩
              change (BitVec.setWidth 32 (BitVec.ofNat 64 ncr0)).toNat ∈
                fullArenaClauseRefsCore st_cp.core
              rw [hncr32_nat, hrefs_cp]; exact List.mem_append_right _ (by simp)
            have htv_shr : (BitVec.setWidth 64 ((tmpj[(BitVec.setWidth 64 jw).toNat]'(by
                rw [bv64_setWidth_32]; exact hjw_tmp)) >>> (1 : BitVec 32))).toNat <
                flw.length := by
              rw [bv64_setWidth_32, bv32_lshr1_bv, hlenw'.core_ok.flags_len]
              simp only [bv64_setWidth_32]; have := htmp_lt jw.toNat hjw_lt; omega
            have htv_shr_n : (BitVec.setWidth 64 ((tmpj[(BitVec.setWidth 64 jw).toNat]'(by
                rw [bv64_setWidth_32]; exact hjw_tmp)) >>> (1 : Nat))).toNat <
                flw.length := by
              rw [bv64_setWidth_32, bv32_lshr1_nat, hlenw'.core_ok.flags_len]
              simp only [bv64_setWidth_32]; have := htmp_lt jw.toNat hjw_lt; omega
            c0_hsteps
            all_goals
              refine ihw (jw + 1#32, ()) m (by dsimp only; rw [hjw1]; omega)
                ⟨wvec', wstk', _, wsort', wlen', wu', by rw [hjw1]; omega, ?_, ?_, hm⟩
              · exact ⟨{ hlenw'.core_ok with flags_len := by simp [hlenw'.core_ok.flags_len] },
                  hlenw'.scratch_ok⟩
              · exact hwatw'.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr)
          · -- Exit watch-push loop -> `h->num_irred++`, invoke `hJif`
            c0_hsteps
            have hlen_fin : ({ stm with
                core := { stm.core with arena := arj, arena_len := ncr0 + 3 + tk.toNat,
                                        wvec := wvecw, wstk := wstkw, wlen := wlenw,
                                        wusable := wuw, flags := flw, tmp := tmpj,
                                        num_irred := stm.core.num_irred + 1#64 }
                scratch := { stm.scratch with wsort := wsortw } } : FullState).LengthsOk c :=
              ⟨{ hlenw.core_ok with vals_len := hlenw.core_ok.vals_len }, hlenw.scratch_ok⟩
            have hwat_fin : ModeWatchesInv F_next
                { st_tmp.core with arena := arj, arena_len := ncr0 + 3 + tk.toNat,
                                   wvec := wvecw, wstk := wstkw, wlen := wlenw,
                                   wusable := wuw, flags := flw,
                                   num_irred := stm.core.num_irred + 1#64 } :=
              hwatw.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr)
            have ⟨hinv_app, hmono_app⟩ := fullDenseInvW_of_append_clause hinv_tmp
              (by omega) hlen_fin hhold_j hns_cp hsz_cp hnew_lt hnew_nd hnew_ent hwat_fin
            exact hJif (jw, _) m ⟨hm, hinv_app, hcvm, hfuelm, hsbm, htmm, htrm,
              arenaMono_trans hmono hmono_app⟩
      · exact absurd (by assumption : BitVec.ofNat 64 stm.core.arena_len = 0xFFFFFFFF#64) hncr_ne


end LeanQbe.T.Examples.Kissat.FullBvaHeap
