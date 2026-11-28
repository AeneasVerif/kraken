/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Sweep.LemmasCone
public import LeanQbe.T.Logic.ControlComb

/-!
# Cone Extraction Sub-Block WP Proofs (`Proof.Sweep.WpCone0`)

Modular WP lemmas for the shared cone-extraction subtrees inside
`Src.Sweep.full_m6_sweep_cone_body`:
1. `s13BinUnitCallExpr` / `step13_cone_bin_unit_call_wp` (unit clause push + `k[6]` check).
2. `s13RollbackLoopExpr` / `step13_cone_rollback_loop_wp` (vertex stack rollback loop).
3. `s13AddClauseBlockExpr` / `step13_cone_add_clause_block_wp` (commit `k[6]`/`mv_c` or rollback).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Sweep

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Kitten
open Kraken.Bedrock2.Test
open scoped FullArenaTactics K6MemATactics FullK6DynMem

/-! ## 1. Unit Clause Helper (`binUnitCall`) -/

private theorem s13_getElem_congr {α : Type _} {xs : List α} {i j : Nat} (heq : i = j)
    (hi : i < xs.length) (hj : j < xs.length) : xs[i]'hi = xs[j]'hj := by
  subst heq; rfl

@[expose] def s13BinUnitCallExpr (pHdr pTmp pK : Val i64)
    (aMapC aPol aNc : Arg Val i32) (aLim : Arg Val .bool)
    (k_done : Val i32 → Val .bool → Expr Val Cont [i64]) : Expr Val Cont [i64] :=
  Expr.let_ (Op.mk (.sext 32 64) (Arg.imm 0, ())) fun p0 =>
  Expr.let_ (Op.mk (.mul i64) (Arg.var p0.fst, Arg.imm 4, ())) fun p1 =>
  Expr.let_ (Op.mk (.add i64) (Arg.var pTmp, Arg.var p1.fst, ())) fun pAddr =>
  Expr.let_ (Op.mk (.shl i32) (aMapC, Arg.imm 1, ())) fun pSh =>
  Expr.let_ (Op.mk (.or i32) (Arg.var pSh.fst, aPol, ())) fun pLit =>
  Expr.store (Arg.var pLit.fst) (Arg.var pAddr.fst)
    (Expr.group (fun _ => Blocks.cons
        (fun p : Tup Val [i32, .bool] => k_done p.fst p.snd.fst) Blocks.nil) fun Js =>
      Expr.call (as := [i64, i64, i32]) (bs := [.bool]) "full_k6_add_clause"
        (Arg.var pHdr, Arg.var pTmp, Arg.imm 1, ()) fun pOk =>
      Expr.jnz (Arg.var pOk.fst)
        (Expr.let_ (Op.mk (.add i32) (aNc, Arg.imm 1, ())) fun pNc1 =>
          Expr.group (fun _ => Blocks.cons (fun pL : Tup Val [.bool] =>
            Expr.jump Js.fst (Arg.var pNc1.fst, Arg.var pL.fst, ())) Blocks.nil) fun Js2 =>
          Expr.let_ (Op.mk (.zext 32 64) (Arg.imm 6, ())) fun p6 =>
          Expr.let_ (Op.mk (.mul i64) (Arg.var p6.fst, Arg.imm 4, ())) fun p24 =>
          Expr.let_ (Op.mk (.add i64) (Arg.var pK, Arg.var p24.fst, ())) fun pK6 =>
          Expr.load i32 (Arg.var pK6.fst) fun ld =>
          Expr.let_ (Op.mk (.cmp .ne i32 .bool rfl) (Arg.var ld, Arg.imm 0, ())) fun pNe =>
          Expr.jnz (Arg.var pNe.fst)
            (Expr.jump Js2.fst (Arg.imm true, ()))
            (Expr.jump Js2.fst (aLim, ())))
        (Expr.jump Js.fst (aNc, Arg.imm true, ())))

theorem step13_cone_bin_unit_call_wp {Γ : Env}
    (hAddCl : Γ.Has "full_k6_add_clause" Kitten.Spec.step13K6AddClauseHwSpec)
    {c : FullCfg} {F_cur : List (List Nat)} {L : K6Layout}
    {s st : FullState} {pK : Val i64} {mvC cv qi_l nv nc mapC pol : BitVec 32}
    {aMapC aPol aNc : Arg Val i32} {lim : Bool} {aLim : Arg Val .bool}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    {k_done : Val i32 → Val .bool → Expr Val Cont [i64]}
    (hLscr : L.scrLen = c.scratch_cap) (hLmv : L.maxV = k6MaxV c.scratch_cap)
    (hpK : pK = L.kPtr c.pScratchBuf)
    (ham : aMapC.val = mapC) (hap : aPol.val = pol)
    (hanc : aNc.val = nc) (halim : aLim.val = lim)
    (hsb : Step13ConeBase F_cur L mvC c s cv qi_l nv.toNat nc.toNat st)
    (hlim0 : lim = false) (hnc_lt : nc.toNat < L.maxOrig)
    (hpol : pol = 0#32 ∨ pol = 1#32)
    (hmap_lt : mapC.toNat < nv.toNat)
    (hmap_cv : (st.scratch.work_stk1[mapC.toNat]?.getD 0#32).toNat = cv.toNat)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [2 * cv.toNat + pol.toNat]))
    (hm : (FullMem c st ⋆ R) m)
    (hCont : ∀ (nc' : BitVec 32) (lim' : Bool) (st' : FullState) (m' : Mem 64),
      nc'.toNat ≤ L.maxOrig → nc.toNat ≤ nc'.toNat →
      (lim' = false → nc'.toNat = nc.toNat + 1 ∧
        st'.scratch.scratch_buf.length = L.scrLen ∧
        (k6StateOfScratch L st'.scratch.scratch_buf).incons = 0#32) →
      Step13ConeBase F_cur L mvC c s cv qi_l nv.toNat nc'.toNat st' →
      (FullMem c st' ⋆ R) m' → wp Γ Q X (k_done nc' lim') m') :
    wp Γ Q X (s13BinUnitCallExpr c.hdr c.pTmp pK aMapC aPol aNc aLim k_done) m := by
  subst hpK
  have hmL := L.hmaxV; have hmvC := hsb.hcone.mvC_leMax; have hnv_mvC := hsb.hcone.nv_le_mvC
  have hnv_ge1 := hsb.hcone.nv_ge1; have hnv_cv := hsb.hcone.nv_le_cv
  have hcv_le := hsb.hlen.core_ok.cur_vars_le
  have htmp_len := hsb.hlen.core_ok.tmp_len_arr
  have h0_lt : (BitVec.signExtend 64 (0#32 : BitVec 32)).toNat < st.core.tmp.length := by
    rw [show (BitVec.signExtend 64 (0#32 : BitVec 32)).toNat = 0 from rfl, htmp_len]; omega
  have hpol_lt : pol.toNat < 2 := by rcases hpol with rfl | rfl <;> decide
  let lit32 : BitVec 32 := (mapC <<< 1#32) ||| pol
  have hlit32_to : lit32.toNat = 2 * mapC.toNat + pol.toNat := by
    dsimp only [lit32]
    change (mapC <<< (1 : Nat) ||| pol).toNat = 2 * mapC.toNat + pol.toNat
    exact m6_bv32_shl1_or_pol mapC pol (by omega) hpol_lt
  let tmp' := st.core.tmp.set 0 lit32
  let st0 : FullState := { st with core := { st.core with tmp := tmp' } }
  have hag0 : AgreesExcept step13ConeMask s st0 := s13_upd_tmp tmp' hsb.hag
  have hgu0 : S13GuOk L s nv.toNat st0 := s13GuOk_with_core_tmp hsb.hgu
  have hcone0 : FidConeInv F_cur L mvC st0 nv.toNat nc.toNat :=
    fidConeInv_tmp_irrel hsb.hcone
  obtain ⟨hst0_len, hlts0_raw, hent0_raw⟩ :=
    m6_cone_unit_tmp_prep hsb.hlen (by rw [htmp_len]; omega)
      hmap_lt (by omega) hpol_lt hlit32_to (by rw [hmap_cv]) hent
  have h1_lt : (1#32 : BitVec 32).toNat ≤ st0.core.tmp.length := by
    rw [show (1#32 : BitVec 32).toNat = 1 from rfl, hst0_len.core_ok.tmp_len_arr]; omega
  have hlts0 : ∀ j < (1#32 : BitVec 32).toNat,
      (st0.core.tmp[j]?.getD 0#32).toNat < 2 * nv.toNat := hlts0_raw
  have hent0 : (cnfOfClauses F_cur).EntailsClause (cnfClause
      ((st0.core.tmp.take (1#32 : BitVec 32).toNat).map
        (fun x => m6ConeLift st0.scratch.work_stk1 x.toNat))) := hent0_raw
  unfold s13BinUnitCallExpr
  c0_hsteps_nogrp
  refine wp_join_group (ts := [i32, .bool])
    (fun (nc', lim', ()) m' => nc'.toNat ≤ L.maxOrig ∧ nc.toNat ≤ nc'.toNat ∧
      (lim' = false → nc'.toNat = nc.toNat + 1 ∧
        ∃ st' : FullState, st'.scratch.scratch_buf.length = L.scrLen ∧
          (k6StateOfScratch L st'.scratch.scratch_buf).incons = 0#32 ∧
          Step13ConeBase F_cur L mvC c s cv qi_l nv.toNat nc'.toNat st' ∧
          (FullMem c st' ⋆ R) m') ∧
      (lim' = true → ∃ st' : FullState,
        Step13ConeBase F_cur L mvC c s cv qi_l nv.toNat nc'.toNat st' ∧
        (FullMem c st' ⋆ R) m'))
    ?_ ?_
  · rintro _ ⟨nc', lim', ⟨⟩⟩ m' ⟨hle_mo, hle_nc, hlf, hlt⟩
    cases lim'
    · obtain ⟨hnc1, st', hscr', hinc0, hsb', hm'⟩ := hlf rfl
      exact hCont nc' false st' m' hle_mo hle_nc (fun _ => ⟨hnc1, hscr', hinc0⟩) hsb' hm'
    · obtain ⟨st', hsb', hm'⟩ := hlt rfl
      exact hCont nc' true st' m' hle_mo hle_nc (fun h => absurd h (by decide)) hsb' hm'
  · intro Js hJs
    refine step13_cone_call_add_clause hAddCl (R := R) (aSz := Arg.imm 1) (sz := 1#32) rfl
      hLscr hLmv hst0_len hag0 (Nat.le_refl _) hgu0 (fun h => absurd h (Nat.lt_irrefl _)) hcone0
      hnc_lt (by decide) h1_lt hlts0 hent0 ?_ ?_
    · have htmp_eq : st.core.tmp.set
          (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 0)).toNat
          (aMapC.val <<< OfNat.ofNat 1 ||| aPol.val) = tmp' := by
        dsimp only [tmp', lit32]; rw [ham, hap]; rfl
      simpa only [st0, htmp_eq] using hm
    intro ok st1 m1 hlen1 hag1 hgu1 hgu_nv1 hcone1 _ htmk1 hws1 hm1
    have hsb1 : Step13ConeBase F_cur L mvC c s cv qi_l nv.toNat
        (if ok then nc + 1#32 else nc).toNat st1 :=
      ⟨hlen1, hag1, (by cases ok; exact hgu1; exact hgu_nv1 rfl), hcone1,
        by rw [htmk1]; exact hsb.htmk, by rw [hws1]; exact hsb.hwk⟩
    c0_hsplit
    · have hok : ok = true := ‹_›
      subst hok
      have hnc1 : (nc + 1#32).toNat = nc.toNat + 1 := by
        unfold K6Layout.maxOrig at hnc_lt; bv_omega
      have hnc1_le : (nc + 1#32).toNat ≤ L.maxOrig := by omega
      have hnc_mono : nc.toNat ≤ (nc + 1#32).toNat := by omega
      have hsb1' : Step13ConeBase F_cur L mvC c s cv qi_l nv.toNat (nc + 1#32).toNat st1 := by
        simpa only [↓reduceIte] using hsb1
      have hscr1_len := hlen1.scratch_ok.scratch_buf_len
      have h6_val := FullK6DynMem.load_m6_full_k6_hdr hLscr hscr1_len (idx := 6) (by decide) hm1
      c0_hsteps_nogrp
      refine wp_join_group (ts := [.bool])
        (fun (lim', ()) mJ => mJ = m1 ∧
          (lim' = false → (k6StateOfScratch L st1.scratch.scratch_buf).incons = 0#32))
        ?_ ?_
      · rintro _ ⟨lim', ⟨⟩⟩ mJ ⟨hmJ, hinc0⟩
        subst hmJ
        cases lim'
        · c0_hsteps!; rw [hanc]
          exact hJs (nc + 1#32, false, ()) mJ ⟨hnc1_le, hnc_mono,
            fun _ => ⟨hnc1, st1, hcone1.scr_len, hinc0 rfl, hsb1', hm1⟩,
            fun h => absurd h (by decide)⟩
        · c0_hsteps!; rw [hanc]
          exact hJs (nc + 1#32, true, ()) mJ ⟨hnc1_le, hnc_mono,
            fun h => absurd h (by decide), fun _ => ⟨st1, hsb1', hm1⟩⟩
      · intro Js2 hJs2
        c0_hsplit
        · c0_hsteps!; exact hJs2 (true, ()) m1 ⟨rfl, fun h => absurd h (by decide)⟩
        · have hinc_bv : (k6StateOfScratch L st1.scratch.scratch_buf).incons = 0#32 := by
            have hb6 : L.k6Base + 6 < st1.scratch.scratch_buf.length := by
              rw [hcone1.scr_len]; unfold K6Layout.scrLen K6Layout.k6Fixed
              have := L.hmaxV; have := L.hacap; omega
            have hz : st1.scratch.scratch_buf[L.k6Base + 6]'hb6 = 0#32 := ‹_›
            unfold k6StateOfScratch K6State.ofSlab
            simp only [List.getElem?_drop, List.getElem?_eq_getElem hb6, Option.getD_some, hz]
          c0_hsteps!
          have hJ2 := hJs2 (lim, ()) m1 ⟨rfl, fun _ => hinc_bv⟩
          simpa only [halim, hlim0] using hJ2
    · have hok : ok = false := by
        cases ok <;> first | rfl | exact absurd rfl ‹_› | contradiction
      subst hok
      have hsb1' : Step13ConeBase F_cur L mvC c s cv qi_l nv.toNat nc.toNat st1 := by
        simpa only [Bool.false_eq_true, ↓reduceIte] using hsb1
      c0_hsteps!
      have hJr := hJs (nc, true, ()) m1 ⟨by omega, le_refl _,
        fun h => absurd h (by decide), fun _ => ⟨st1, hsb1', hm1⟩⟩
      simpa only [hanc] using hJr

/-! ## 2. Vertex Rollback Loop & `add_clause` Block Helpers -/

@[expose] def s13RollbackLoopExpr (pWs pTmk : Val i64) (aSavedNv aNv : Arg Val i32)
    (k_done : Val i32 → Expr Val Cont [i64]) : Expr Val Cont [i64] :=
  Expr.group
    (fun Js => Blocks.cons
      (fun p : Tup Val [i32] =>
        Expr.let_ (Op.mk (.cmp .ugt i32 .bool rfl) (Arg.var p.fst, aSavedNv, ())) fun pc =>
        Expr.jnz (Arg.var pc.fst)
          (Expr.let_ (Op.mk (.sub i32) (Arg.var p.fst, Arg.imm 1, ())) fun pnv1 =>
           Expr.let_ (Op.mk (.zext 32 64) (Arg.var pnv1.fst, ())) fun pz1 =>
           Expr.let_ (Op.mk (.mul i64) (Arg.var pz1.fst, Arg.imm 4, ())) fun pm1 =>
           Expr.let_ (Op.mk (.add i64) (Arg.var pWs, Arg.var pm1.fst, ())) fun pws =>
           Expr.load i32 (Arg.var pws.fst) fun ld =>
           Expr.let_ (Op.mk (.zext 32 64) (Arg.var ld, ())) fun pz2 =>
           Expr.let_ (Op.mk (.mul i64) (Arg.var pz2.fst, Arg.imm 4, ())) fun pm2 =>
           Expr.let_ (Op.mk (.add i64) (Arg.var pTmk, Arg.var pm2.fst, ())) fun pt =>
           Expr.store (t := i32) (Arg.imm 0) (Arg.var pt.fst)
             (Expr.jump Js.fst (Arg.var pnv1.fst, ())))
          (k_done p.fst))
      Blocks.nil)
    fun Js => Expr.jump Js.fst (aNv, ())

theorem step13_cone_rollback_loop_wp {Γ : Env}
    {c : FullCfg} {F_cur : List (List Nat)} {L : K6Layout} {mvC : BitVec 32}
    {s st0 : FullState} {ws0 scr0 : List (BitVec 32)} {savedNv nv0 : BitVec 32}
    {aSavedNv aNv : Arg Val i32} {nc_w : Nat}
    {R : Mem 64 → Prop} {m0 : Mem 64} {Q : Post [i64]} {X : XPost}
    {k_done : Val i32 → Expr Val Cont [i64]}
    (hsav_eq : aSavedNv.val = savedNv) (hanv : aNv.val = nv0)
    (hlen0 : st0.LengthsOk c) (hag0 : AgreesExcept step13ConeMask s st0)
    (hgu0 : S13GuOk L s savedNv.toNat st0)
    (hcone0 : FidConeInv F_cur L mvC st0 nv0.toNat nc_w)
    (hsav_ge1 : 1 ≤ savedNv.toNat) (hsav_le : savedNv.toNat ≤ nv0.toNat)
    (hscr0 : st0.scratch.scratch_buf = scr0)
    (hbdd_s : K6LitsBounded savedNv.toNat (k6StateOfScratch L scr0))
    (htrl_s : ∀ l ∈ k6TrailLits (k6StateOfScratch L scr0), l < 2 * savedNv.toNat)
    (hws_sav : ∀ j < savedNv.toNat, st0.scratch.work_stk1[j]? = ws0[j]?)
    (hm0 : (FullMem c st0 ⋆ R) m0)
    (hDone : ∀ (st' : FullState) (m' : Mem 64),
      st'.LengthsOk c → AgreesExcept step13ConeMask s st' →
      S13GuOk L s savedNv.toNat st' →
      FidConeInv F_cur L mvC st' savedNv.toNat nc_w →
      st'.scratch.scratch_buf = scr0 →
      (∀ j < savedNv.toNat, st'.scratch.work_stk1[j]? = ws0[j]?) →
      (FullMem c st' ⋆ R) m' → wp Γ Q X (k_done savedNv) m') :
    wp Γ Q X
      (s13RollbackLoopExpr c.pWorkStk1 c.pTarjanMark aSavedNv aNv k_done) m0 := by
  unfold s13RollbackLoopExpr
  refine wp_loop_inv (ts := [i32])
    (fun (nv_r, ()) mr => savedNv.toNat ≤ nv_r.toNat ∧ nv_r.toNat ≤ nv0.toNat ∧
      ∃ st_r : FullState, st_r.LengthsOk c ∧ AgreesExcept step13ConeMask s st_r ∧
        S13GuOk L s savedNv.toNat st_r ∧ FidConeInv F_cur L mvC st_r nv_r.toNat nc_w ∧
        st_r.scratch.scratch_buf = scr0 ∧
        (∀ j < savedNv.toNat, st_r.scratch.work_stk1[j]? = ws0[j]?) ∧
        (FullMem c st_r ⋆ R) mr)
    (fun (nv_r, ()) _ => nv_r.toNat - savedNv.toNat) ?_ ?_
  · intro Jl hJl; c0_hsteps!; rw [hanv]
    exact hJl (nv0, ()) m0 ⟨hsav_le, le_refl _, st0, hlen0, hag0, hgu0, hcone0, hscr0, hws_sav, hm0⟩
  · rintro Jl ⟨nv_r, ⟨⟩⟩ mr
      ⟨hsav_le_r, hle_nv0, st_r, hl_r, ha_r, hgu_r, hc_r, hscr_r, hws_r, hmr⟩ ih
    clear hm0
    have hnv_pos : 1 ≤ nv_r.toNat := Nat.le_trans hsav_ge1 hsav_le_r
    have hnv_cv_r : nv_r.toNat ≤ st_r.core.cur_vars := hc_r.nv_le_cv
    have hcv_le_r : st_r.core.cur_vars ≤ c.max_vars := hl_r.core_ok.cur_vars_le
    have hidx_ws : (BitVec.setWidth 64 (nv_r - 1#32)).toNat <
        st_r.scratch.work_stk1.length := by
      have h1 : (nv_r - 1#32).toNat = nv_r.toNat - 1 := by bv_omega
      rw [bv_c0_zext32_64, hl_r.scratch_ok.work_stk1_len, h1]; omega
    have hvr_bd_c0 : (BitVec.setWidth 64
        (st_r.scratch.work_stk1[(BitVec.setWidth 64 (nv_r - 1#32)).toNat]'hidx_ws)).toNat <
        st_r.scratch.tarjan_mark.length := by
      have h1 : (nv_r - 1#32).toNat = nv_r.toNat - 1 := by bv_omega
      have hf := (hc_r.fwd (nv_r.toNat - 1) (by omega)).1
      have hidx1 : nv_r.toNat - 1 < st_r.scratch.work_stk1.length := by
        rw [hl_r.scratch_ok.work_stk1_len]; omega
      have hidx_eq : (BitVec.setWidth 64 (nv_r - 1#32)).toNat = nv_r.toNat - 1 := by
        rw [bv_c0_zext32_64, h1]
      rw [bv_c0_zext32_64, hl_r.scratch_ok.tarjan_mark_len,
        s13_getElem_congr hidx_eq hidx_ws hidx1]
      rw [List.getElem?_eq_getElem hidx1, Option.getD_some] at hf
      omega
    c0_hsteps_nogrp
    c0_hsplit
    · have hsav_lt : savedNv.toNat < nv_r.toNat := by
        have hlt : aSavedNv.val.toNat < nv_r.toNat := ‹_›
        rwa [hsav_eq] at hlt
      obtain ⟨hnv1, _, hl', ha', hgu', hc', hscr', hws'⟩ :=
        step13_cone_pop_var_ok hl_r ha_r hgu_r hc_r hsav_ge1 hsav_lt hscr_r hbdd_s htrl_s hws_r
      c0_hsteps!
      have hidx1 : (nv_r - 1#32).toNat < st_r.scratch.work_stk1.length := by
        simpa only [bv_c0_zext32_64] using hidx_ws
      have hvr_eq :
          (BitVec.setWidth 64
            (st_r.scratch.work_stk1[(BitVec.setWidth 64 (nv_r - 1)).toNat]'hidx_ws)).toNat =
          (st_r.scratch.work_stk1[(nv_r - 1#32).toNat]?.getD 0#32).toNat := by
        rw [bv_c0_zext32_64, List.getElem?_eq_getElem hidx1, Option.getD_some]
        exact congrArg BitVec.toNat (s13_getElem_congr
          (by rw [bv_c0_zext32_64]) hidx_ws hidx1)
      have h0eq : (0 : BitVec 32) = 0#32 := rfl
      refine ih (nv_r - 1#32, ()) _ (by dsimp only; rw [hnv1]; omega)
        ⟨by rw [hnv1]; omega, by rw [hnv1]; omega, _, hl', ha', hgu', hc', hscr', hws', ?_⟩
      simpa only [hvr_eq, h0eq] using hm
    · have hge : ¬ savedNv.toNat < nv_r.toNat := by
        have hnh : ¬ aSavedNv.val.toNat < nv_r.toNat := ‹_›
        rwa [hsav_eq] at hnh
      have hnv_eq : nv_r = savedNv := BitVec.eq_of_toNat_eq (by omega)
      change wp Γ Q X (k_done nv_r) mr
      rw [hnv_eq]
      exact hDone _ mr hl_r ha_r hgu_r (by rw [← hnv_eq]; exact hc_r) hscr_r hws_r hmr

@[expose] def s13AddClauseBlockExpr (pHdr pTmp pK pWs pTmk : Val i64)
    (aSz aSavedNv aNv aNc aMvC : Arg Val i32) (aLim : Arg Val .bool)
    (k_done : Val i32 → Val i32 → Val .bool → Expr Val Cont [i64]) : Expr Val Cont [i64] :=
  Expr.group
    (fun _ => Blocks.cons
      (fun p : Tup Val [i32, i32, .bool] => k_done p.fst p.snd.fst p.snd.snd.fst)
      Blocks.nil)
    fun Js =>
      Expr.call (as := [i64, i64, i32]) (bs := [.bool]) "full_k6_add_clause"
        (Arg.var pHdr, Arg.var pTmp, aSz, ()) fun pok =>
      Expr.jnz (Arg.var pok.fst)
        (Expr.let_ (Op.mk (.add i32) (aNc, Arg.imm 1, ())) fun pnc1 =>
          Expr.group
            (fun _ => Blocks.cons
              (fun pl : Tup Val [.bool] =>
                Expr.jump Js.fst (aNv, Arg.var pnc1.fst, Arg.var pl.fst, ()))
              Blocks.nil)
            fun Js2 =>
              Expr.let_ (Op.mk (.zext 32 64) (Arg.imm 6, ())) fun p6 =>
              Expr.let_ (Op.mk (.mul i64) (Arg.var p6.fst, Arg.imm 4, ())) fun p24 =>
              Expr.let_ (Op.mk (.add i64) (Arg.var pK, Arg.var p24.fst, ())) fun pk6 =>
              Expr.load i32 (Arg.var pk6.fst) fun ld =>
              Expr.let_ (Op.mk (.cmp .ne i32 .bool rfl) (Arg.var ld, Arg.imm 0, ())) fun pne =>
              Expr.jnz (Arg.var pne.fst)
                (Expr.jump Js2.fst (Arg.imm true, ()))
                (Expr.let_ (Op.mk (.cmp .uge i32 .bool rfl) (aNv, aMvC, ())) fun puge =>
                  Expr.jnz (Arg.var puge.fst)
                    (Expr.jump Js2.fst (Arg.imm true, ()))
                    (Expr.jump Js2.fst (aLim, ()))))
        (s13RollbackLoopExpr pWs pTmk aSavedNv aNv fun nvr =>
          Expr.jump Js.fst (Arg.var nvr, aNc, Arg.imm true, ()))

theorem step13_cone_add_clause_block_wp {Γ : Env}
    (hAddCl : Γ.Has "full_k6_add_clause" Kitten.Spec.step13K6AddClauseHwSpec)
    {c : FullCfg} {F_cur : List (List Nat)} {L : K6Layout} {pK : Val i64}
    {mvC cv qi_l savedNv nv nc sz : BitVec 32}
    {aSz aSavedNv aNv aNc aMvC : Arg Val i32} {lim : Bool} {aLim : Arg Val .bool}
    {s st : FullState} {ws0 scr0 : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    {k_done : Val i32 → Val i32 → Val .bool → Expr Val Cont [i64]}
    (hLscr : L.scrLen = c.scratch_cap) (hLmv : L.maxV = k6MaxV c.scratch_cap)
    (hpK : pK = L.kPtr c.pScratchBuf)
    (haSz : aSz.val = sz) (hasav : aSavedNv.val = savedNv) (hanv : aNv.val = nv)
    (hanc : aNc.val = nc) (hamvc_le : aMvC.val.toNat ≤ mvC.toNat) (halim : aLim.val = lim)
    (hsb : Step13ConeSavedBase F_cur L mvC c s cv qi_l savedNv ws0 scr0 nv.toNat nc.toNat st)
    (hqi_sav : qi_l.toNat < savedNv.toNat) (hsav_ge1 : 1 ≤ savedNv.toNat)
    (hbdd_s : K6LitsBounded savedNv.toNat (k6StateOfScratch L scr0))
    (htrl_s : ∀ l ∈ k6TrailLits (k6StateOfScratch L scr0), l < 2 * savedNv.toNat)
    (hnew_in_tmp : savedNv.toNat < nv.toNat →
      ∃ i < sz.toNat, (st.core.tmp[i]?.getD 0#32).toNat / 2 + 1 = nv.toNat)
    (hnc_lt : nc.toNat < L.maxOrig) (hsz28 : sz.toNat < 2 ^ 28)
    (hsz_tmp : sz.toNat ≤ st.core.tmp.length)
    (hlts : ∀ j < sz.toNat, (st.core.tmp[j]?.getD 0#32).toNat < 2 * nv.toNat)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause
      ((st.core.tmp.take sz.toNat).map (fun x => m6ConeLift st.scratch.work_stk1 x.toNat))))
    (hlim0 : lim = false) (hm : (FullMem c st ⋆ R) m)
    (hCont : ∀ (nv' nc' : BitVec 32) (lim' : Bool) (st' : FullState) (m' : Mem 64),
      nc'.toNat ≤ L.maxOrig → nc.toNat ≤ nc'.toNat →
      savedNv.toNat ≤ nv'.toNat → nv'.toNat ≤ mvC.toNat →
      (lim' = false → nc'.toNat = nc.toNat + 1 ∧ nv' = nv ∧ nv'.toNat < mvC.toNat ∧
        st'.scratch.scratch_buf.length = L.scrLen ∧
        (k6StateOfScratch L st'.scratch.scratch_buf).incons = 0#32) →
      Step13ConeBase F_cur L mvC c s cv qi_l nv'.toNat nc'.toNat st' →
      (FullMem c st' ⋆ R) m' → wp Γ Q X (k_done nv' nc' lim') m') :
    wp Γ Q X (s13AddClauseBlockExpr c.hdr c.pTmp pK c.pWorkStk1 c.pTarjanMark
      aSz aSavedNv aNv aNc aMvC aLim k_done) m := by
  subst hpK
  have hmL := L.hmaxV; have hmvC := hsb.hcone.mvC_leMax; have hnv_mvC := hsb.hcone.nv_le_mvC
  unfold s13AddClauseBlockExpr
  refine wp_join_group (ts := [i32, i32, .bool])
    (fun (nv', nc', lim', ()) m' => nc'.toNat ≤ L.maxOrig ∧ nc.toNat ≤ nc'.toNat ∧
      savedNv.toNat ≤ nv'.toNat ∧ nv'.toNat ≤ mvC.toNat ∧
      (lim' = false → nc'.toNat = nc.toNat + 1 ∧ nv' = nv ∧ nv'.toNat < mvC.toNat ∧
        ∃ st' : FullState, st'.scratch.scratch_buf.length = L.scrLen ∧
          (k6StateOfScratch L st'.scratch.scratch_buf).incons = 0#32 ∧
          Step13ConeBase F_cur L mvC c s cv qi_l nv'.toNat nc'.toNat st' ∧
          (FullMem c st' ⋆ R) m') ∧
      (lim' = true → ∃ st' : FullState,
        Step13ConeBase F_cur L mvC c s cv qi_l nv'.toNat nc'.toNat st' ∧
        (FullMem c st' ⋆ R) m'))
    ?_ ?_
  · rintro _ ⟨nv', nc', lim', ⟨⟩⟩ m' ⟨h1, h2, h3s, h3, hlf, hlt⟩
    cases lim'
    · obtain ⟨h4, h5, h6, st', h7, h8, hsb', hm'⟩ := hlf rfl
      exact hCont nv' nc' false st' m' h1 h2 h3s h3 (fun _ => ⟨h4, h5, h6, h7, h8⟩) hsb' hm'
    · obtain ⟨st', hsb', hm'⟩ := hlt rfl
      exact hCont nv' nc' true st' m' h1 h2 h3s h3 (fun h => absurd h (by decide)) hsb' hm'
  · intro Js hJs
    refine step13_cone_call_add_clause hAddCl haSz hLscr hLmv hsb.hlen hsb.hag hsb.hsav_le
      hsb.hgu_sav hnew_in_tmp hsb.hcone hnc_lt hsz28 hsz_tmp hlts hent hm ?_
    intro ok st1 m1 hlen1 hag1 hgu_sav1 hgu_nv1 hcone1 hscr_f htmk1 hws1 hm1
    c0_hsplit
    · have hok : ok = true := ‹_›
      subst hok
      have hnc1 : (nc + 1#32).toNat = nc.toNat + 1 := by
        unfold K6Layout.maxOrig at hnc_lt; bv_omega
      have hnc1_le : (nc + 1#32).toNat ≤ L.maxOrig := by omega
      have hnc_mono : nc.toNat ≤ (nc + 1#32).toNat := by omega
      have hcone1' : FidConeInv F_cur L mvC st1 nv.toNat (nc + 1#32).toNat := by
        simpa only [↓reduceIte] using hcone1
      have hsb1 : Step13ConeBase F_cur L mvC c s cv qi_l nv.toNat (nc + 1#32).toNat st1 :=
        ⟨hlen1, hag1, hgu_nv1 rfl, hcone1', by rw [htmk1]; exact hsb.htmk,
         by rw [hws1]; exact hsb.hwk⟩
      have hscr1_len := hlen1.scratch_ok.scratch_buf_len
      have h6_val := FullK6DynMem.load_m6_full_k6_hdr hLscr hscr1_len (idx := 6) (by decide) hm1
      c0_hsteps_nogrp
      refine wp_join_group (ts := [.bool])
        (fun (lim', ()) mJ => mJ = m1 ∧
          (lim' = false → nv.toNat < mvC.toNat ∧
            (k6StateOfScratch L st1.scratch.scratch_buf).incons = 0#32))
        ?_ ?_
      · rintro _ ⟨lim', ⟨⟩⟩ mJ ⟨hmJ, hfalse⟩
        subst hmJ
        cases lim'
        · obtain ⟨hnv_lt, hinc0⟩ := hfalse rfl
          c0_hsteps!; rw [hanv, hanc]
          exact hJs (nv, nc + 1#32, false, ()) mJ ⟨hnc1_le, hnc_mono, hsb.hsav_le, hnv_mvC,
            fun _ => ⟨hnc1, rfl, hnv_lt, st1, hcone1'.scr_len, hinc0, hsb1, hm1⟩,
            fun h => absurd h (by decide)⟩
        · c0_hsteps!; rw [hanv, hanc]
          exact hJs (nv, nc + 1#32, true, ()) mJ ⟨hnc1_le, hnc_mono, hsb.hsav_le, hnv_mvC,
            fun h => absurd h (by decide), fun _ => ⟨st1, hsb1, hm1⟩⟩
      · intro Js2 hJs2
        c0_hsplit
        · c0_hsteps!; exact hJs2 (true, ()) m1 ⟨rfl, fun h => absurd h (by decide)⟩
        · have hinc_bv : (k6StateOfScratch L st1.scratch.scratch_buf).incons = 0#32 := by
            have hb6 : L.k6Base + 6 < st1.scratch.scratch_buf.length := by
              rw [hcone1'.scr_len]; unfold K6Layout.scrLen K6Layout.k6Fixed
              have := L.hmaxV; have := L.hacap; omega
            have hz : st1.scratch.scratch_buf[L.k6Base + 6]'hb6 = 0#32 := ‹_›
            unfold k6StateOfScratch K6State.ofSlab
            simp only [List.getElem?_drop, List.getElem?_eq_getElem hb6, Option.getD_some, hz]
          c0_hsplit
          · c0_hsteps!; exact hJs2 (true, ()) m1 ⟨rfl, fun h => absurd h (by decide)⟩
          · have hnv_lt : nv.toNat < mvC.toNat := by
              have hc' : ¬ aMvC.val.toNat ≤ aNv.val.toNat := ‹_›
              rw [hanv] at hc'; omega
            c0_hsteps!
            simpa only [halim, hlim0] using
              hJs2 (aLim.val, ()) m1 ⟨rfl, fun _ => ⟨hnv_lt, hinc_bv⟩⟩
    · have hok : ok = false := by
        cases ok <;> first | rfl | exact absurd rfl ‹_› | contradiction
      subst hok
      have hcone1' : FidConeInv F_cur L mvC st1 nv.toNat nc.toNat := by
        simpa only [Bool.false_eq_true, ↓reduceIte] using hcone1
      have hscr1_eq : st1.scratch.scratch_buf = scr0 :=
        (hscr_f rfl).trans hsb.hscr
      have hws1_sav : ∀ j < savedNv.toNat, st1.scratch.work_stk1[j]? = ws0[j]? := fun j hj => by
        rw [hws1]; exact hsb.hws j hj
      refine step13_cone_rollback_loop_wp hasav hanv hlen1 hag1 hgu_sav1 hcone1'
        hsav_ge1 hsb.hsav_le hscr1_eq hbdd_s htrl_s hws1_sav hm1 ?_
      intro stR mR hlR haR hguR hcR _ hwsR hmR
      c0_hsteps!
      have hwkR : (stR.scratch.work_stk1[qi_l.toNat]?.getD 0#32).toNat = cv.toNat := by
        rw [hwsR qi_l.toNat hqi_sav, ← hsb.hws qi_l.toNat hqi_sav]; exact hsb.hwk
      have htmkR : stR.scratch.tarjan_mark[cv.toNat]?.getD 0#32 =
          BitVec.ofNat 32 (qi_l.toNat + 1) := by
        have hf := (hcR.fwd qi_l.toNat hqi_sav).2
        rwa [hwkR] at hf
      have hsbR : Step13ConeBase F_cur L mvC c s cv qi_l savedNv.toNat nc.toNat stR :=
        ⟨hlR, haR, hguR, hcR, htmkR, hwkR⟩
      have hJ_res := hJs (savedNv, nc, true, ()) mR ⟨by omega, le_refl _, le_refl _,
        Nat.le_trans hsb.hsav_le hnv_mvC, fun h => absurd h (by decide),
        fun _ => ⟨stR, hsbR, hmR⟩⟩
      simpa only [hasav, hanc] using hJ_res

end LeanQbe.T.Examples.Kissat.Proof.Sweep
