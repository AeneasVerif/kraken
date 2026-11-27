/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S6aLiftsSpec
public import LeanQbe.T.Examples.Kissat.FullFidelityBvaProof2b0
public import LeanQbe.T.Examples.Kissat.FullFidelityStep7BvaSpec
import LeanQbe.T.Examples.Kissat.FullFidelityStep13S6aProof1d0
import LeanQbe.T.Examples.Kissat.FullFidelityBvaProof0

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S6a

open LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.LratBytes
open Std.Sat
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullBvaHeap.FullBvaHeapHelpers
open LeanQbe.T.Examples.Kissat.FullFidelityBva
open LeanQbe.T.Examples.Kissat.FullFidelityStep7
open scoped FullArenaTactics

private theorem s6a_bv32_add1 {x : BitVec 32} (hx : x.toNat + 1 < 2 ^ 32) :
    (x + 1#32).toNat = x.toNat + 1 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

private theorem s6a_getElem_eq_of_eq {α : Type _} {xs ys : List α} {i j : Nat}
    (hl : xs = ys) (hij : i = j) (hi : i < xs.length) (hj : j < ys.length) :
    xs[i]'hi = ys[j]'hj := by subst hl; subst hij; rfl

private theorem s6a_bva_step_scan_ok {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s stl : FullState} {R : Mem 64 → Prop} {sc bump : Nat}
    {step cur_qn best_k : BitVec 32} {ml : Mem 64}
    (hinv : StepInvBody c F0 F_cur s R sc step cur_qn best_k bump stl ml)
    (hsc_eq : sc = fidStepsCap c.scratch_cap) :
    let ro := (stl.scratch.scratch_buf[sc + (step.toNat - 1)]?.getD 0#32).toNat
    ro + cur_qn.toNat ≤ c.scratch_cap ∧
    ∀ qi < cur_qn.toNat,
      let w := stl.scratch.scratch_buf[ro + qi]?.getD 0#32
      if w &&& 0x80000000#32 ≠ 0#32 then (w &&& 0x7FFFFFFF#32).toNat < 2 * stl.core.cur_vars
      else w.toNat ∈ fullArenaClauseRefs stl ∧ fullArenaClauseGarb stl w.toNat = false := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h4sc_b, hbump_cap, hqn, hmat, _, _,
    _, _⟩ := hinv
  have hrow := hmat.2.2.2.2.2 (step.toNat - 1) (by omega)
  have hro_le := hrow.2.2.2.1
  have hqn_eq : cur_qn.toNat = (stl.scratch.scratch_buf[2 * fidStepsCap c.scratch_cap +
      (step.toNat - 1)]?.getD 0#32).toNat := hsc_eq ▸ hqn
  refine ⟨by rw [hsc_eq]; omega, fun qi hqi => ?_⟩
  rw [hsc_eq]
  obtain ⟨_, hx_bdd, _, hok, _⟩ := hrow.2.2.2.2.2 qi (hqn_eq ▸ hqi)
  unfold FidBvaRowEntryOk at hok
  split at hok
  · rename_i hbin; rw [ite_eq_left hbin]
    exact hok.1
  · rename_i hbin; rw [ite_eq_right hbin]
    rcases hok with ⟨href, hng, _⟩; exact ⟨href, hng⟩

private theorem s6a_bva_step_upd_ok {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s stl st1 st2 st3 : FullState} {R : Mem 64 → Prop} {sc bump max_new : Nat}
    {step cur_qn best_k best_lit nrow_off par_off new_qn : BitVec 32} {ml m3 : Mem 64}
    (hinv : StepInvBody c F0 F_cur s R sc step cur_qn best_k bump stl ml)
    (hsc_eq : sc = fidStepsCap c.scratch_cap)
    (hsc_pos : 0 < sc) (hsc_le : sc ≤ 256) (hstep_lt : step.toNat < sc)
    (hden1 : st1.core = stl.core ∧ st1.scratch.scratch_buf = stl.scratch.scratch_buf ∧
      st1.scratch.tarjan_mark = stl.scratch.tarjan_mark ∧
      st1.scratch.tarjan_reach = stl.scratch.tarjan_reach)
    (hden2 : FullDenseInvNoLm c F0 F_cur st2)
    (hst2_eq : st2.core.cur_vars = st1.core.cur_vars ∧ st2.core.fuel = st1.core.fuel ∧
      st2.core.arena = st1.core.arena ∧ st2.core.arena_len = st1.core.arena_len ∧
      st2.core.lit_mark = st1.core.lit_mark ∧ st2.core.mrk = st1.core.mrk ∧
      st2.scratch.tarjan_mark = st1.scratch.tarjan_mark ∧
      st2.scratch.tarjan_reach = st1.scratch.tarjan_reach ∧
      st2.scratch.scratch_buf = st1.scratch.scratch_buf)
    (hbl_lt : best_lit.toNat < 2 * st1.core.cur_vars)
    (hst3 : st3 = { st2 with scratch := { st2.scratch with
      scratch_buf := st3.scratch.scratch_buf, ant_sz := st3.scratch.ant_sz } })
    (hsb3_len : st3.scratch.scratch_buf.length = c.scratch_cap)
    (hnrow : nrow_off.toNat = bump) (hpar : par_off.toNat = bump + max_new)
    (hpar_cap : par_off.toNat + max_new ≤ c.scratch_cap)
    (hnqn_le : new_qn.toNat ≤ max_new) (hnqn2 : 2 ≤ new_qn.toNat)
    (hkeep3 : ∀ idx < c.scratch_cap,
      ¬(nrow_off.toNat ≤ idx ∧ idx < nrow_off.toNat + max_new) →
      ¬(par_off.toNat ≤ idx ∧ idx < par_off.toNat + max_new) →
      st3.scratch.scratch_buf[idx]? = stl.scratch.scratch_buf[idx]?)
    (hrows3 : ∀ nm < new_qn.toNat,
      let pi := (st3.scratch.scratch_buf[par_off.toNat + nm]?.getD 0#32).toNat
      pi < cur_qn.toNat ∧ ∃ res, (∀ x ∈ res, x < 2 * st2.core.cur_vars) ∧
        (List.map (fun x => x / 2) res).Nodup ∧
        FidBvaRowEntryOk F_cur st2 (stl.scratch.scratch_buf[step.toNat - 1]?.getD 0#32).toNat
          (stl.scratch.scratch_buf[(stl.scratch.scratch_buf[sc + (step.toNat - 1)]?.getD
            0#32).toNat + pi]?.getD 0#32) res ∧
        FidBvaRowEntryOk F_cur st2 best_lit.toNat
          (st3.scratch.scratch_buf[nrow_off.toNat + nm]?.getD 0#32) res ∧
        (∀ t < step.toNat, (cnfOfClauses F_cur).EntailsClause
          (cnfClause ((stl.scratch.scratch_buf[t]?.getD 0#32).toNat :: res))) ∧
        (cnfOfClauses F_cur).EntailsClause (cnfClause (best_lit.toNat :: res)))
    {bk' : BitVec 32} (hbk' : bk' = best_k ∨ bk' = step)
    (hm4 : (FullMem c { st3 with
      core := { st3.core with lit_mark := st3.core.lit_mark.set best_lit.toNat 1#8 }
      scratch := { st3.scratch with
        scratch_buf := (((st3.scratch.scratch_buf.set step.toNat best_lit).set
          (sc + step.toNat) nrow_off).set (2 * sc + step.toNat) new_qn).set
          (3 * sc + step.toNat) par_off } } ⋆ R) m3) :
    StepInvBody c F0 F_cur s R sc (step + 1#32) new_qn bk' (par_off.toNat + new_qn.toNat)
      { st3 with
        core := { st3.core with lit_mark := st3.core.lit_mark.set best_lit.toNat 1#8 }
        scratch := { st3.scratch with
          scratch_buf := (((st3.scratch.scratch_buf.set step.toNat best_lit).set
            (sc + step.toNat) nrow_off).set (2 * sc + step.toNat) new_qn).set
            (3 * sc + step.toNat) par_off } } m3 := by
  obtain ⟨_, hlen_l, _, _, _, _, _, hcv_l, hfu_l, har_l, hal_l, hmrk_l, htm_l, htr_l,
    hstep1, _, h4sc_b, _, hqn_l, hmat_l, hbk_l, hlm_hi, hlm_set, hlm_only⟩ := hinv
  let sb4 := (((st3.scratch.scratch_buf.set step.toNat best_lit).set
    (sc + step.toNat) nrow_off).set (2 * sc + step.toNat) new_qn).set
    (3 * sc + step.toNat) par_off
  let lm4 := st3.core.lit_mark.set best_lit.toNat 1#8
  let st4 : FullState := { st3 with
    core := { st3.core with lit_mark := lm4 }
    scratch := { st3.scratch with scratch_buf := sb4 } }
  have hmx := c.hmaxv; have hsc_c := c.hscr; unfold dimacsBound at hmx hsc_c
  have hcv2_le : st2.core.cur_vars ≤ c.max_vars := hden2.1.core_ok.cur_vars_le
  have hst3_len : st3.LengthsOk c := by
    rw [hst3]
    exact ⟨hden2.1.core_ok, { hden2.1.scratch_ok with scratch_buf_len := hsb3_len }⟩
  have hsb4_len : sb4.length = c.scratch_cap := by simp [sb4, hsb3_len]
  have hlm4_len : lm4.length = 2 * c.max_vars := by
    dsimp only [lm4]; rw [List.length_set, hst3, hden2.1.core_ok.lit_mark_len]
  have hst4_len : st4.LengthsOk c :=
    ⟨{ hst3_len.core_ok with lit_mark_len := hlm4_len },
     { hst3_len.scratch_ok with scratch_buf_len := hsb4_len }⟩
  have hw4 : FullWitnessInv c F0 F_cur st4.core := by
    dsimp only [st4]; rw [hst3]
    exact FullBvaHeap.fullWitnessInv_with_litMark hden2.2.1 lm4
  have hnd4 : FullArenaVarsNodup st4 := by
    unfold FullArenaVarsNodup; dsimp only [st4]; rw [hst3]; exact hden2.2.2.1
  have hext4 : FullExtScratchOk c st4 := by
    dsimp only [st4]; rw [hst3]
    exact FullExtScratchOk.of_pres hden2.2.2.2.1 ⟨rfl, rfl⟩ fun _ hr => hr
  have hstep1_bv : (step + 1#32).toNat = step.toNat + 1 := s6a_bv32_add1 (by omega)
  have hmat2 : FidBvaMatrixInv c F_cur st2 step.toNat bump :=
    fidBvaMatrixInv_congr (by rw [hst2_eq.1, hden1.1]) (by rw [hst2_eq.2.2.1, hden1.1])
      (by rw [hst2_eq.2.2.2.1, hden1.1]) (hst2_eq.2.2.2.2.2.2.2.2.trans hden1.2.1) hmat_l
  have hkeep3' : ∀ idx < c.scratch_cap,
      ¬(nrow_off.toNat ≤ idx ∧ idx < nrow_off.toNat + max_new) →
      ¬(par_off.toNat ≤ idx ∧ idx < par_off.toNat + max_new) →
      st3.scratch.scratch_buf[idx]? = st2.scratch.scratch_buf[idx]? := by
    intro idx hi h1 h2
    rw [hst2_eq.2.2.2.2.2.2.2.2, hden1.2.1]
    exact hkeep3 idx hi h1 h2
  have hrows3' : ∀ nm < new_qn.toNat,
      let pi := (st3.scratch.scratch_buf[par_off.toNat + nm]?.getD 0#32).toNat
      pi < (st2.scratch.scratch_buf[2 * sc + (step.toNat - 1)]?.getD 0#32).toNat ∧
        ∃ res, (∀ x ∈ res, x < 2 * st2.core.cur_vars) ∧
          (List.map (fun x => x / 2) res).Nodup ∧
          FidBvaRowEntryOk F_cur st2
            (st2.scratch.scratch_buf[step.toNat - 1]?.getD 0#32).toNat
            (st2.scratch.scratch_buf[(st2.scratch.scratch_buf[sc + (step.toNat - 1)]?.getD
              0#32).toNat + pi]?.getD 0#32) res ∧
          FidBvaRowEntryOk F_cur st2 best_lit.toNat
            (st3.scratch.scratch_buf[nrow_off.toNat + nm]?.getD 0#32) res ∧
          (∀ t < step.toNat, (cnfOfClauses F_cur).EntailsClause
            (cnfClause ((st2.scratch.scratch_buf[t]?.getD 0#32).toNat :: res))) ∧
          (cnfOfClauses F_cur).EntailsClause (cnfClause (best_lit.toNat :: res)) := by
    intro nm hnm
    have hr := hrows3 nm hnm
    rw [hst2_eq.2.2.2.2.2.2.2.2, hden1.2.1]
    refine ⟨?_, hr.2⟩
    simpa [← hsc_eq, ← hqn_l] using hr.1
  have hmat_ext := fidBvaMatrixInv_extend_step (c := c) (F_cur := F_cur) (s := st2)
    (sb' := st3.scratch.scratch_buf) (step := step.toNat) (bump := bump) (max_new := max_new)
    (sc := sc) (best_lit := best_lit) (new_qn := new_qn) (nrow_off := nrow_off)
    (par_off := par_off) hsc_eq hstep1 hstep_lt hmat2 hsb3_len (by omega) hnrow hpar hpar_cap
    hnqn_le hnqn2 hkeep3' hrows3'
  have hlm4 := fid_bva_try_lit_extend_lm (maxv := c.max_vars) (cap := c.scratch_cap)
    (sc := sc) (step := step.toNat) (bump := bump) (max_new := max_new)
    (lm := st2.core.lit_mark) (sb2 := stl.scratch.scratch_buf) (sb3 := st3.scratch.scratch_buf)
    (bl := best_lit) (new_qn := new_qn) (nrow_off := nrow_off) (par_off := par_off)
    hsc_pos hstep_lt (by rw [hst2_eq.2.2.2.2.1, hden1.1]; exact hlen_l.core_ok.lit_mark_len)
    hsb3_len (by omega) hnrow hpar h4sc_b hpar_cap hkeep3
    (by rw [hst2_eq.2.2.2.2.1, hden1.1]; exact hlm_hi)
    (by rw [hst2_eq.2.2.2.2.1, hden1.1]; exact hlm_set)
    (by rw [hst2_eq.2.2.2.2.1, hden1.1]; exact hlm_only)
  have hst3_lm : st3.core.lit_mark = st2.core.lit_mark := by rw [hst3]
  have hst4_st2 : st4.core.cur_vars = st2.core.cur_vars ∧ st4.core.fuel = st2.core.fuel ∧
      st4.core.arena = st2.core.arena ∧ st4.core.arena_len = st2.core.arena_len ∧
      st4.core.mrk = st2.core.mrk ∧ st4.core.cur_level = st2.core.cur_level ∧
      st4.core.dense_mode = st2.core.dense_mode ∧
      st4.scratch.tarjan_mark = st2.scratch.tarjan_mark ∧
      st4.scratch.tarjan_reach = st2.scratch.tarjan_reach := by
    dsimp only [st4]; rw [hst3]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hcqn4 : new_qn.toNat =
      (st4.scratch.scratch_buf[2 * sc + ((step + 1#32).toNat - 1)]?.getD 0#32).toNat := by
    change new_qn.toNat = (sb4[2 * sc + ((step + 1#32).toNat - 1)]?.getD 0#32).toNat
    rw [hstep1_bv, show step.toNat + 1 - 1 = step.toNat from by omega]
    dsimp only [sb4]
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by simp [hsb3_len]; omega),
      Option.getD_some]
  refine ⟨hm4, hst4_len, hw4, hnd4, hext4, by rw [hst4_st2.2.2.2.2.2.1]; exact hden2.2.2.2.2.1,
    by rw [hst4_st2.2.2.2.2.2.2.1]; exact hden2.2.2.2.2.2,
    by rw [hst4_st2.1, hst2_eq.1, hden1.1]; exact hcv_l,
    by rw [hst4_st2.2.1, hst2_eq.2.1, hden1.1]; exact hfu_l,
    by rw [hst4_st2.2.2.1, hst2_eq.2.2.1, hden1.1]; exact har_l,
    by rw [hst4_st2.2.2.2.1, hst2_eq.2.2.2.1, hden1.1]; exact hal_l,
    by rw [hst4_st2.2.2.2.2.1, hst2_eq.2.2.2.2.2.1, hden1.1]; exact hmrk_l,
    by rw [hst4_st2.2.2.2.2.2.2.2.1, hst2_eq.2.2.2.2.2.2.1, hden1.2.2.1]; exact htm_l,
    by rw [hst4_st2.2.2.2.2.2.2.2.2, hst2_eq.2.2.2.2.2.2.2.1, hden1.2.2.2]; exact htr_l,
    by rw [hstep1_bv]; omega, by rw [hstep1_bv]; omega, by omega, by omega,
    hcqn4, ?_, ?_, ?_, ?_, ?_⟩
  · have hmat4 : FidBvaMatrixInv c F_cur st4 (step.toNat + 1) (par_off.toNat + new_qn.toNat) :=
      @fidBvaMatrixInv_congr c F_cur
        { st2 with scratch := { st2.scratch with
          scratch_buf := (((st3.scratch.scratch_buf.set step.toNat best_lit).set
            (sc + step.toNat) nrow_off).set (2 * sc + step.toNat) new_qn).set
            (3 * sc + step.toNat) par_off } }
        st4 (step.toNat + 1) (par_off.toNat + new_qn.toNat)
        hst4_st2.1 hst4_st2.2.2.1 hst4_st2.2.2.2.1 rfl hmat_ext
    rwa [hstep1_bv]
  · rcases hbk' with rfl | rfl
    · rcases hbk_l with rfl | ⟨h1, h2⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨h1, by rw [hstep1_bv]; omega⟩
    · exact Or.inr ⟨hstep1, by rw [hstep1_bv]; omega⟩
  · dsimp only [st4]; rw [hst3_lm]; exact hlm4.1
  · rw [hstep1_bv]; dsimp only [st4]; rw [hst3_lm]; exact hlm4.2.1
  · intro l hl hnz; rw [hstep1_bv]; dsimp only [st4] at hnz
    rw [hst3_lm] at hnz; exact hlm4.2.2 l hl hnz

private theorem s6a_bva_step_iter_wp (Γ : Env)
    (hScan : ∀ a m Q X, step13BvaScanCandsSpec a m Q X →
      Γ "full_bva_scan_cands" [i64, i32, i32, i64] [i32] a m Q X)
    (hPick : ∀ a m Q X, step13BvaPickCandSpec a m Q X →
      Γ "full_bva_pick_cand" [i64, i32, i32] [i32] a m Q X)
    (hFilter : ∀ a m Q X, fidBvaFilterRowSpec a m Q X →
      Γ "full_bva_filter_row" [i64, i32, i32, i32, i32, i32] [i32] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {R : Mem 64 → Prop} {Q : Post [.bool]} {X : XPost}
    {f0_bv : BitVec 32} {init_cv init_lits lim_bv : BitVec 64} {sc bump : Nat}
    {bump_bv step cur_qn best_k : BitVec 32} {best_red : BitVec 64}
    {stl : FullState} {ml : Mem 64}
    {Jex Js : Tup Cont [[i32, i32, i32, i32, i64]]}
    (hsc_eq : sc = fidStepsCap c.scratch_cap)
    (hsc_pos : 0 < sc) (hsc_le : sc ≤ 256)
    (hf0_lt : f0_bv.toNat < 2 * s.core.cur_vars)
    (hil_le : init_lits.toNat ≤ 2 * s.core.cur_vars)
    (hbump_bv : bump_bv.toNat = bump)
    (hlay : Step7BvaLayout c stl step.toNat)
    (hinv : StepInvBody c F0 F_cur s R sc step cur_qn best_k bump stl ml)
    (hJex : ∀ bump' step' cur_qn' best_k' best_red' st_e m_e,
      Step7BvaLayout c st_e step'.toNat →
      StepExitBody c F0 F_cur s R sc step' best_k' bump' st_e m_e →
      Jex.fst (BitVec.ofNat 32 bump', step', cur_qn', best_k', best_red', ()) m_e)
    (hJs : ∀ bump' step' cur_qn' best_k' best_red' st_n m_n,
      Step7BvaLayout c st_n step'.toNat →
      StepInvBody c F0 F_cur s R sc step' cur_qn' best_k' bump' st_n m_n →
      step.toNat < sc → step'.toNat > step.toNat →
      Js.fst (BitVec.ofNat 32 bump', step', cur_qn', best_k', best_red', ()) m_n) :
    wp Γ Q X ((fidTryLitStepBlock Val Cont (BitVec.ofNat 32 sc, ()) (c.hdr, f0_bv, init_cv, ())
        c.pScratchBuf (init_lits, ()) Jex (BitVec.ofNat 64 c.scratch_cap) c.pLitMark lim_bv
        Js).get Member.here (bump_bv, step, cur_qn, best_k, best_red, ())) ml := by
  have hmx := c.hmaxv; have har_b := c.harena; have hsc_c := c.hscr
  unfold dimacsBound at hmx har_b hsc_c
  have ⟨hm_l, hlen_l, hw_l, hnodup_l, hext_l, hcl0_l, hdm_l, hcv_l, hfu_l, har_l, hal_l,
    hmrk_l, htm_l, htr_l, hstep1, hstep_sc, h4sc_b, hbump_cap, hqn_l, hmat_l, hbk_l, hlm_hi,
    hlm_set, hlm_only⟩ := hinv
  have hsb_len := hlen_l.scratch_ok.scratch_buf_len
  dsimp only [fidTryLitStepBlock, Blocks.get]
  c0_hfast
  · rename_i hstep_bv hcqn_bv
    have hstep_lt : step.toNat < sc := by
      rw [Nat.mod_eq_of_lt (by omega)] at hstep_bv
      exact hstep_bv
    have hcqn2 : 2 ≤ cur_qn.toNat := hcqn_bv
    have hro_idx : (BitVec.setWidth 64 (BitVec.ofNat 32 sc + step - 1)).toNat <
        stl.scratch.scratch_buf.length := by
      rw [hsb_len, show (1 : BitVec 32) = 1#32 from rfl,
        fid_bv64_sc_add_step_sub1 hsc_le hstep1 hstep_sc]
      omega
    c0_hfast
    obtain ⟨hro_qn_cap, hscan_rows⟩ := s6a_bva_step_scan_ok hinv hsc_eq
    have hro_nat : ∀ h, (stl.scratch.scratch_buf[(BitVec.setWidth 64
        (BitVec.ofNat 32 sc + step - 1)).toNat]'h).toNat =
        (stl.scratch.scratch_buf[sc + (step.toNat - 1)]?.getD 0#32).toNat := by
      intro h
      rw [List.getElem?_eq_getElem (by rw [hsb_len]; omega), Option.getD_some]
      exact congrArg BitVec.toNat (s6a_getElem_eq_of_eq rfl
        (by rw [show (1 : BitVec 32) = 1#32 from rfl]
            exact fid_bv64_sc_add_step_sub1 hsc_le hstep1 hstep_sc) h _)
    apply wp_call_of_spec; apply hScan _ _ _ X
    dsimp only [step13BvaScanCandsSpec, vals_nil, vals_cons, Arg.val_var]
    refine ⟨c, F0, F_cur, stl, R, rfl, hlen_l, hw_l, hnodup_l, hext_l, hcl0_l, hdm_l,
      (by omega), hlm_hi, (by rw [hro_nat _]; exact hro_qn_cap),
      (by simpa only [hro_nat] using hscan_rows), hm_l,
      fun ncntd wsort1 ws1_1 ws2_1 ant1 m1 hlen1 hnc1 hws1_ok hm1 => ?_⟩
    let st1 : FullState := { stl with scratch := { stl.scratch with
      ant_sz := ant1, wsort := wsort1, work_stk1 := ws1_1, work_stk2 := ws2_1 } }
    have hst1_den : FullDenseInvNoLm c F0 F_cur st1 :=
      ⟨hlen1, hw_l, hnodup_l, FullExtScratchOk.of_pres hext_l ⟨rfl, rfl⟩ fun _ hr => hr,
       hcl0_l, hdm_l⟩
    apply wp_call_of_spec; apply hPick _ _ _ X
    dsimp only [step13BvaPickCandSpec, vals_nil, vals_cons, Arg.val_var]
    refine ⟨c, F0, F_cur, st1, R, rfl, hst1_den, (by dsimp only [st1]; omega), hnc1,
      (fun i hi => (hws1_ok i hi).2), hm1,
      fun best_lit repr2 mclr2 tc2 tl2 wsort2 ant2 sig2 shrk2 m2 hden2 hbl_dom hm2 => ?_⟩
    let st2 : FullState := { st1 with
      core := { st1.core with tmp_cnt := tc2, tmp_len := tl2, min_clr := mclr2, repr := repr2 }
      scratch := { st1.scratch with
        ant_sz := ant2, wsort := wsort2, shrink_stk := shrk2, sim_sig := sig2 } }
    have hst2_l : st2.core.cur_vars = stl.core.cur_vars ∧ st2.core.fuel = stl.core.fuel ∧
        st2.core.arena = stl.core.arena ∧ st2.core.arena_len = stl.core.arena_len ∧
        st2.core.lit_mark = stl.core.lit_mark ∧ st2.core.mrk = stl.core.mrk ∧
        st2.scratch.tarjan_mark = stl.scratch.tarjan_mark ∧
        st2.scratch.tarjan_reach = stl.scratch.tarjan_reach ∧
        st2.scratch.scratch_buf = stl.scratch.scratch_buf :=
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    have hinv2 : StepInvBody c F0 F_cur s R sc step cur_qn best_k bump st2 m2 :=
      ⟨hm2, hden2.1, hden2.2.1, hden2.2.2.1, hden2.2.2.2.1, hden2.2.2.2.2.1,
       hden2.2.2.2.2.2, by rw [hst2_l.1]; exact hcv_l, by rw [hst2_l.2.1]; exact hfu_l,
       by rw [hst2_l.2.2.1]; exact har_l, by rw [hst2_l.2.2.2.1]; exact hal_l,
       by rw [hst2_l.2.2.2.2.2.1]; exact hmrk_l, by rw [hst2_l.2.2.2.2.2.2.1]; exact htm_l,
       by rw [hst2_l.2.2.2.2.2.2.2.1]; exact htr_l, hstep1, hstep_sc, h4sc_b, hbump_cap,
       by rw [hst2_l.2.2.2.2.2.2.2.2]; exact hqn_l,
       fidBvaMatrixInv_congr hst2_l.1 hst2_l.2.2.1 hst2_l.2.2.2.1 hst2_l.2.2.2.2.2.2.2.2 hmat_l,
       hbk_l, by rw [hst2_l.2.2.2.2.1]; exact hlm_hi,
       by rw [hst2_l.2.2.2.2.1, hst2_l.2.2.2.2.2.2.2.2]; exact hlm_set,
       by rw [hst2_l.2.2.2.2.1, hst2_l.2.2.2.2.2.2.2.2]; exact hlm_only⟩
    have hlay2 : Step7BvaLayout c st2 step.toNat :=
      Step7BvaLayout.congr hst2_l.2.2.2.2.2.2.2.2 hlay
    c0_hfast_nogrp
    · have heq_b : BitVec.ofNat 32 bump = bump_bv := BitVec.eq_of_toNat_eq
        (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hbump_bv])
      rw [← heq_b]
      exact hJex bump step cur_qn best_k best_red st2 m2 hlay2 (stepExitBody_of_inv hinv2)
    · have heq_b : BitVec.ofNat 32 bump = bump_bv := BitVec.eq_of_toNat_eq
        (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hbump_bv])
      rw [← heq_b]
      exact hJex bump step cur_qn best_k best_red st2 m2 hlay2 (stepExitBody_of_inv hinv2)
    · have hbl_ne : best_lit ≠ 0xFFFFFFFF#32 := by assumption
      have hbl_lt : best_lit.toNat < 2 * st2.core.cur_vars := by
        rcases hbl_dom with rfl | hlt
        · exact absurd rfl hbl_ne
        · exact hlt
      let max_new0 := ((BitVec.ofNat 64 c.scratch_cap - bump_bv.setWidth 64).setWidth 32) >>>
        (1 : Nat)
      have hmn0 : max_new0.toNat = (c.scratch_cap - bump) / 2 := by
        dsimp only [max_new0]
        have hb_lt : bump < 2 ^ 64 := by omega
        have hsc_lt64 : c.scratch_cap < 2 ^ 64 := by omega
        rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_one,
          BitVec.toNat_setWidth, BitVec.toNat_sub,
          BitVec.toNat_setWidth, BitVec.toNat_ofNat, hbump_bv,
          Nat.mod_eq_of_lt hb_lt, Nat.mod_eq_of_lt hsc_lt64]
        have : bump ≤ c.scratch_cap := hbump_cap
        have : c.scratch_cap - bump < 2 ^ 32 := by omega
        rw [show (2 ^ 64 - bump + c.scratch_cap) % 2 ^ 64 = c.scratch_cap - bump by omega,
          Nat.mod_eq_of_lt this]
      refine wp_join_group (ts := [i32]) (fun mn_v m_j =>
          m_j = m2 ∧ mn_v.fst.toNat = min ((c.scratch_cap - bump) / 2) cur_qn.toNat) ?_ ?_
      · intro _ mn_tup m_j ⟨hm_eq, hmn_nat⟩
        rcases mn_tup with ⟨mn_bv, _⟩
        dsimp only at hmn_nat
        subst m_j
        c0_hfast
        · have heq_b : BitVec.ofNat 32 bump = bump_bv := BitVec.eq_of_toNat_eq
            (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hbump_bv])
          rw [← heq_b]
          exact hJex bump step cur_qn best_k best_red st2 m2 hlay2 (stepExitBody_of_inv hinv2)
        · have hmn2 : 2 ≤ mn_bv.toNat := by c0_bound
          have hmn_cap : bump + 2 * mn_bv.toNat ≤ c.scratch_cap := by omega
          have hpar_nat : (bump_bv + mn_bv).toNat = bump + mn_bv.toNat := by c0_bound
          have hpar_cap : (bump_bv + mn_bv).toNat + mn_bv.toNat ≤ c.scratch_cap := by omega
          have hmn_diff : (bump_bv + mn_bv).toNat - bump_bv.toNat = mn_bv.toNat := by omega
          have hmat2 : FidBvaMatrixInv c F_cur st2 step.toNat bump :=
            fidBvaMatrixInv_congr hst2_l.1 hst2_l.2.2.1 hst2_l.2.2.2.1
              hst2_l.2.2.2.2.2.2.2.2 hmat_l
          apply wp_call_of_spec; apply hFilter _ _ _ X
          dsimp only [fidBvaFilterRowSpec, vals_nil, vals_cons, Arg.val_var]
          refine ⟨c, F0, F_cur, st2, R, step.toNat, bump, rfl, hden2.1, hden2.2.1,
            hden2.2.2.1, hden2.2.2.2.1, hden2.2.2.2.2.1, hden2.2.2.2.2.2,
            hsc_eq ▸ hsc_pos, hstep1, hsc_eq ▸ hstep_lt,
            (by dsimp only [st2, st1]; rw [hro_nat _, hsc_eq]),
            (by rw [← hsc_eq, hst2_l.2.2.2.2.2.2.2.2]; exact hqn_l), hbump_bv,
            (by omega), (by rw [hpar_nat]; omega), hbl_lt, hmat2,
            (by rw [hst2_l.2.2.2.2.1]; exact hlm_hi),
            (by rw [hst2_l.2.2.2.2.1, hst2_l.2.2.2.2.2.2.2.2]; exact hlm_set), hm2,
            fun new_qn sb3 ant3 m3 hlen3 hnqn_le hkeep3 hrows3 hm3 => ?_⟩
          rw [hmn_diff] at hnqn_le hkeep3
          simp only [hro_nat] at hrows3
          let st3 : FullState := { st2 with scratch := { st2.scratch with
            scratch_buf := sb3, ant_sz := ant3 } }
          have hsb3_len := hlen3.scratch_ok.scratch_buf_len
          c0_hfast
          · have hnqn_lt2 : new_qn.toNat < 2 := by assumption
            have hmat3 : FidBvaMatrixInv c F_cur st3 step.toNat bump := by
              have h := fidBvaMatrixInv_of_filter_pres (sb' := sb3) (max_new := mn_bv.toNat)
                (nrow_off := bump_bv) (par_off := bump_bv + mn_bv)
                hmat2 hbump_bv (by omega)
                (fun idx hi h1 h2 =>
                  (hkeep3 idx hi h1 h2).trans
                    (congrArg (fun xs => xs[idx]?) hst2_l.2.2.2.2.2.2.2.2.symm))
              exact fidBvaMatrixInv_congr (s' := st3) rfl rfl rfl rfl h
            have hlm_set3 : ∀ r < step.toNat,
                st3.core.lit_mark[(st3.scratch.scratch_buf[r]?.getD 0#32).toNat]?.getD
                  0#8 &&& 1#8 ≠ 0#8 := by
              intro r hr
              have hkr := hkeep3 r (by omega) (by rw [hbump_bv]; omega)
                (by rw [hpar_nat]; omega)
              dsimp only [st3]; rw [hkr, hst2_l.2.2.2.2.1, ← hst2_l.2.2.2.2.2.2.2.2]
              exact hlm_set r hr
            have hlm_only3 : ∀ l < 2 * c.max_vars,
                st3.core.lit_mark[l]?.getD 0#8 &&& 1#8 ≠ 0#8 →
                ∃ r < step.toNat, (st3.scratch.scratch_buf[r]?.getD 0#32).toNat = l := by
              intro l hl hnz
              rw [show st3.core.lit_mark = stl.core.lit_mark from hst2_l.2.2.2.2.1] at hnz
              obtain ⟨r, hr, heq⟩ := hlm_only l hl hnz
              refine ⟨r, hr, ?_⟩
              have hkr := hkeep3 r (by omega) (by rw [hbump_bv]; omega)
                (by rw [hpar_nat]; omega)
              dsimp only [st3]; rwa [hkr, ← hst2_l.2.2.2.2.2.2.2.2]
            have hlay3 : Step7BvaLayout c st3 step.toNat :=
              s6a_bva_step7_layout_of_pre (hsc_eq ▸ Nat.le_of_lt hstep_lt) (hsc_eq ▸ h4sc_b)
                (fun idx hi => by
                  rw [hkeep3 idx (by omega) (by rw [hbump_bv]; omega) (by rw [hpar_nat]; omega),
                    ← hst2_l.2.2.2.2.2.2.2.2]) hlay2
            have heq_b : BitVec.ofNat 32 bump = bump_bv := BitVec.eq_of_toNat_eq
              (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hbump_bv])
            rw [← heq_b]
            exact hJex bump step new_qn best_k best_red st3 m3 hlay3
              (stepExitBody_of_inv ⟨hm3, hlen3, hden2.2.1, hden2.2.2.1,
                FullExtScratchOk.of_pres hden2.2.2.2.1 ⟨rfl, rfl⟩ (fun _ hr => hr),
                hden2.2.2.2.2.1, hden2.2.2.2.2.2, hcv_l, hfu_l, har_l, hal_l, hmrk_l,
                htm_l, htr_l, hstep1, hstep_sc, h4sc_b, hbump_cap, rfl, hmat3, hbk_l,
                hlm_hi, hlm_set3, hlm_only3⟩)
          · have hnqn2 : 2 ≤ new_qn.toNat := by c0_bound
            have hs3_0 : (BitVec.setWidth 64 step).toNat <
                st3.scratch.scratch_buf.length := by
              rw [hsb3_len]; c0_bound
            have hs3_1 : (BitVec.setWidth 64 (BitVec.ofNat 32 sc + step)).toNat <
                (st3.scratch.scratch_buf.set
                  (BitVec.setWidth 64 step).toNat best_lit).length := by
              rw [List.length_set, hsb3_len]; c0_bound
            have hs3_2 : (BitVec.setWidth 64 (2#32 * BitVec.ofNat 32 sc + step)).toNat <
                ((st3.scratch.scratch_buf.set
                    (BitVec.setWidth 64 step).toNat best_lit).set
                  (BitVec.setWidth 64
                    (BitVec.ofNat 32 sc + step)).toNat bump_bv).length := by
              rw [List.length_set, List.length_set, hsb3_len]; c0_bound
            have hs3_3 : (BitVec.setWidth 64 (3#32 * BitVec.ofNat 32 sc + step)).toNat <
                (((st3.scratch.scratch_buf.set
                      (BitVec.setWidth 64 step).toNat best_lit).set
                    (BitVec.setWidth 64 (BitVec.ofNat 32 sc + step)).toNat bump_bv).set
                  (BitVec.setWidth 64
                    (2#32 * BitVec.ofNat 32 sc + step)).toNat new_qn).length := by
              rw [List.length_set, List.length_set, List.length_set, hsb3_len]; c0_bound
            have hcv2_le := hden2.1.core_ok.cur_vars_le
            have hlm_b : (BitVec.setWidth 64 best_lit).toNat <
                st3.core.lit_mark.length := by
              dsimp only [st3]; rw [hden2.1.core_ok.lit_mark_len]; c0_bound
            c0_hfast_nogrp
            have hsc32 : sc < 2 ^ 32 := by omega
            have hsc_bv : (BitVec.ofNat 32 sc).toNat = sc := by
              rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hsc32
            have hi0 : (BitVec.setWidth 64 step).toNat = step.toNat := by
              rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
            have hi1 : (BitVec.setWidth 64 (BitVec.ofNat 32 sc + step)).toNat =
                sc + step.toNat := by
              rw [BitVec.toNat_setWidth, BitVec.toNat_add, hsc_bv,
                Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
            have h2sc : 2 * sc < 2 ^ 32 := by omega
            have h2sc_s : 2 * sc + step.toNat < 2 ^ 32 := by omega
            have h2sc_s64 : 2 * sc + step.toNat < 2 ^ 64 := by omega
            have hi2 : (BitVec.setWidth 64 (2#32 * BitVec.ofNat 32 sc + step)).toNat =
                2 * sc + step.toNat := by
              have h2 : (2#32 : BitVec 32).toNat = 2 := rfl
              rw [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_mul, h2, hsc_bv,
                Nat.mod_eq_of_lt h2sc, Nat.mod_eq_of_lt h2sc_s, Nat.mod_eq_of_lt h2sc_s64]
            have h3sc : 3 * sc < 2 ^ 32 := by omega
            have h3sc_s : 3 * sc + step.toNat < 2 ^ 32 := by omega
            have h3sc_s64 : 3 * sc + step.toNat < 2 ^ 64 := by omega
            have hi3 : (BitVec.setWidth 64 (3#32 * BitVec.ofNat 32 sc + step)).toNat =
                3 * sc + step.toNat := by
              have h3 : (3#32 : BitVec 32).toNat = 3 := rfl
              rw [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_mul, h3, hsc_bv,
                Nat.mod_eq_of_lt h3sc, Nat.mod_eq_of_lt h3sc_s, Nat.mod_eq_of_lt h3sc_s64]
            have heq_sb : (((st3.scratch.scratch_buf.set
                  (BitVec.setWidth 64 step).toNat best_lit).set
                (BitVec.setWidth 64 (BitVec.ofNat 32 sc + step)).toNat bump_bv).set
                (BitVec.setWidth 64 (2#32 * BitVec.ofNat 32 sc + step)).toNat new_qn).set
                (BitVec.setWidth 64
                  (3#32 * BitVec.ofNat 32 sc + step)).toNat (bump_bv + mn_bv) =
                (((st3.scratch.scratch_buf.set step.toNat best_lit).set
                  (sc + step.toNat) bump_bv).set (2 * sc + step.toNat) new_qn).set
                  (3 * sc + step.toNat) (bump_bv + mn_bv) := by
              rw [hi0, hi1, hi2, hi3]
            have hbl64 : (BitVec.setWidth 64 best_lit).toNat = best_lit.toNat := by
              simp only [BitVec.toNat_setWidth]; omega
            have heq_lm : st3.core.lit_mark.set (BitVec.setWidth 64 best_lit).toNat
                (BitVec.setWidth 8 1#32) =
                st3.core.lit_mark.set best_lit.toNat 1#8 := by
              rw [hbl64, show (BitVec.setWidth 8 1#32) = 1#8 from rfl]
            let sb4 := (((st3.scratch.scratch_buf.set step.toNat best_lit).set
              (sc + step.toNat) bump_bv).set (2 * sc + step.toNat) new_qn).set
              (3 * sc + step.toNat) (bump_bv + mn_bv)
            let st4 : FullState := { st3 with
              core := { st3.core with lit_mark := st3.core.lit_mark.set best_lit.toNat 1#8 }
              scratch := { st3.scratch with scratch_buf := sb4 } }
            have hm4 : (FullMem c st4 ⋆ R) m := by
              dsimp only [st4, sb4]; rw [← heq_sb, ← heq_lm]; exact hm
            have hupd : ∀ bk' br', bk' = best_k ∨ bk' = step →
                Js.fst (bump_bv + mn_bv + new_qn, step + 1#32, new_qn, bk', br',
                  ()) m := by
              intro bk' br' hbk'
              have hstep_gt : (step + 1#32).toNat > step.toNat := by
                rw [s6a_bv32_add1 (by omega)]; omega
              have hbump'_eq : (bump_bv + mn_bv).toNat + new_qn.toNat =
                  ((bump_bv + mn_bv) + new_qn).toNat := by
                rw [BitVec.toNat_add (bump_bv + mn_bv) new_qn, hpar_nat,
                  Nat.mod_eq_of_lt (by omega)]
              have hinv4 := s6a_bva_step_upd_ok (st2 := st2) (max_new := mn_bv.toNat) hinv hsc_eq
                hsc_pos hsc_le hstep_lt ⟨rfl, rfl, rfl, rfl⟩ hden2 hst2_l hbl_lt rfl hsb3_len
                hbump_bv hpar_nat hpar_cap (by omega) hnqn2 hkeep3
                (fun nm hnm => hrows3 nm hnm) hbk' hm4
              have heq_bv' : BitVec.ofNat 32 ((bump_bv + mn_bv).toNat + new_qn.toNat) =
                  bump_bv + mn_bv + new_qn := BitVec.eq_of_toNat_eq
                (by rw [hbump'_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])
              have hlay4 : Step7BvaLayout c st4 (step + 1#32).toNat := by
                rw [s6a_bv32_add1 (by omega)]
                exact s6a_bva_step7_layout_extend (best_lit := best_lit)
                  hstep1 (hsc_eq ▸ hstep_lt) hmat_l
                  hlay hsb3_len hbump_bv hpar_nat hnqn_le
                  (by rw [← hsc_eq, ← hqn_l]; omega) (hsc_eq ▸ h4sc_b)
                  (fun idx hi => by
                    rw [hkeep3 idx (by omega) (by rw [hbump_bv]; omega) (by rw [hpar_nat]; omega),
                      ← hst2_l.2.2.2.2.2.2.2.2])
                  (by dsimp only [st4, sb4]; rw [← hsc_eq])
              rw [← heq_bv']
              exact hJs ((bump_bv + mn_bv).toNat + new_qn.toNat) (step + 1#32) new_qn
                bk' br' st4 m hlay4 hinv4 hstep_lt hstep_gt
            refine wp_join_group (ts := [i32, i64]) (fun bk_tup mk =>
                mk = m ∧ (bk_tup.fst = best_k ∨ bk_tup.fst = step)) ?_ ?_
            · intro _ bk_tup mk ⟨hm_eq, hbk'⟩
              rcases bk_tup with ⟨bk', br', _⟩
              dsimp only at hbk'
              subst mk
              c0_hfast; exact hupd bk' br' hbk'
            · intro Js2 hJs2
              c0_hfast
              all_goals (first
                | (have hbk_step : (step + 1 - 1 : BitVec 32) = step := BitVec.eq_of_toNat_eq (by
                    rw [BitVec.toNat_sub, BitVec.toNat_add, show (1 : BitVec 32).toNat = 1 from rfl]
                    omega)
                   rw [hbk_step]
                   exact hJs2 (step, _, ()) m ⟨rfl, by dsimp only; exact Or.inr rfl⟩)
                | exact hJs2 (best_k, best_red, ()) m ⟨rfl, by dsimp only; exact Or.inl rfl⟩)
      · intro _ hJmn
        c0_hfast
        · rw [hbump_bv, show (2 ^ 64 - bump + c.scratch_cap) % 2 ^ 64 = c.scratch_cap - bump
            by omega, Nat.mod_eq_of_lt (by omega)] at hc
          exact hJmn (cur_qn, ()) m2 ⟨rfl, by dsimp only; rw [Nat.min_eq_right (by omega)]⟩
        · rw [hbump_bv, show (2 ^ 64 - bump + c.scratch_cap) % 2 ^ 64 = c.scratch_cap - bump
            by omega, Nat.mod_eq_of_lt (by omega)] at hc
          exact hJmn (max_new0, ()) m2 ⟨rfl, by dsimp only; rw [hmn0, Nat.min_eq_left (by omega)]⟩
  · have heq_b : BitVec.ofNat 32 bump = bump_bv := BitVec.eq_of_toNat_eq
      (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hbump_bv])
    rw [← heq_b]
    exact hJex bump step cur_qn best_k best_red stl ml hlay (stepExitBody_of_inv hinv)
  · have heq_b : BitVec.ofNat 32 bump = bump_bv := BitVec.eq_of_toNat_eq
      (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hbump_bv])
    rw [← heq_b]
    exact hJex bump step cur_qn best_k best_red stl ml hlay (stepExitBody_of_inv hinv)
  · have heq_b : BitVec.ofNat 32 bump = bump_bv := BitVec.eq_of_toNat_eq
      (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hbump_bv])
    rw [← heq_b]
    exact hJex bump step cur_qn best_k best_red stl ml hlay (stepExitBody_of_inv hinv)

public theorem s6a_bva_step_loop_wp (Γ : Env)
    (hScan : ∀ a m Q X, step13BvaScanCandsSpec a m Q X →
      Γ "full_bva_scan_cands" [i64, i32, i32, i64] [i32] a m Q X)
    (hPick : ∀ a m Q X, step13BvaPickCandSpec a m Q X →
      Γ "full_bva_pick_cand" [i64, i32, i32] [i32] a m Q X)
    (hFilter : ∀ a m Q X, fidBvaFilterRowSpec a m Q X →
      Γ "full_bva_filter_row" [i64, i32, i32, i32, i32, i32] [i32] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {R : Mem 64 → Prop} {Q : Post [.bool]} {X : XPost}
    {f0_bv : BitVec 32} {init_cv init_lits lim_bv : BitVec 64} {sc : Nat}
    {m0 : Mem 64}
    {Jex : Tup Cont [[i32, i32, i32, i32, i64]]}
    {entry : Tup Cont [[i32, i32, i32, i32, i64]] → Expr Val Cont [.bool]}
    (hsc_eq : sc = fidStepsCap c.scratch_cap)
    (hsc_pos : 0 < sc) (hsc_le : sc ≤ 256)
    (hf0_lt : f0_bv.toNat < 2 * s.core.cur_vars)
    (hil_le : init_lits.toNat ≤ 2 * s.core.cur_vars)
    (hentry : ∀ J : Cont [i32, i32, i32, i32, i64],
      (∀ (bump_bv stp cqn bk : BitVec 32) (bred : BitVec 64) (m_lp : Mem 64),
        (∃ bp st_lp, bump_bv.toNat = bp ∧ Step7BvaLayout c st_lp stp.toNat ∧
          StepInvBody c F0 F_cur s R sc stp cqn bk bp st_lp m_lp) →
        J (bump_bv, stp, cqn, bk, bred, ()) m_lp) →
      wp Γ Q X (entry (J, ())) m0)
    (hJex : ∀ bump' step' cur_qn' best_k' best_red' st_e m_e,
      Step7BvaLayout c st_e step'.toNat →
      StepExitBody c F0 F_cur s R sc step' best_k' bump' st_e m_e →
      Jex.fst (BitVec.ofNat 32 bump', step', cur_qn', best_k', best_red', ()) m_e) :
    wp Γ Q X (Expr.group
      (fidTryLitStepBlock Val Cont (BitVec.ofNat 32 sc, ()) (c.hdr, f0_bv, init_cv, ())
        c.pScratchBuf (init_lits, ()) Jex (BitVec.ofNat 64 c.scratch_cap) c.pLitMark lim_bv)
      entry) m0 := by
  have hsc_c := c.hscr; unfold dimacsBound at hsc_c
  refine wp_loop_inv
    (fun (bump_bv, stp, cqn, bk, bred, _) m_lp => ∃ bp st_lp,
      bump_bv.toNat = bp ∧ Step7BvaLayout c st_lp stp.toNat ∧
      StepInvBody c F0 F_cur s R sc stp cqn bk bp st_lp m_lp)
    (fun (_, stp, _) _ => sc - stp.toNat)
    (fun J hJ => hentry J (fun bump_bv stp cqn bk bred m_lp h => hJ _ m_lp h))
    (fun Js (bump_bv, stp, cqn, bk, bred, _) m_lp ⟨bp, st_lp, hbp_bv, hlay_lp, hinv_lp⟩ ih =>
      s6a_bva_step_iter_wp Γ hScan hPick hFilter hsc_eq hsc_pos hsc_le hf0_lt hil_le hbp_bv
        hlay_lp hinv_lp hJex fun bp' stp' cqn' bk' bred' st_n m_n hlay_n hinv_n hlt_sc hgt =>
        ih (BitVec.ofNat 32 bp', stp', cqn', bk', bred', ()) m_n
          (by dsimp only; omega)
          ⟨bp', st_n, by
            have hbp_lt := hinv_n.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)], hlay_n, hinv_n⟩)

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S6a
