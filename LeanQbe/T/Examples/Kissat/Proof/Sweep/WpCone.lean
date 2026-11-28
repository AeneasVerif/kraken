/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Sweep.Spec
public import LeanQbe.T.Examples.Kissat.Src.Sweep
import LeanQbe.T.Examples.Kissat.Proof.Kitten.Tactics
import LeanQbe.T.Examples.Kissat.Proof.Sweep.WpCone1
import LeanQbe.T.Examples.Kissat.Proof.Sweep.WpConeBin

/-!
# Step 13 `full_m6_sweep_cone` WP Proof (`Kissat.Proof.Sweep.WpCone`)

Proves `full_m6_sweep_cone_wp` (`1/20` of `Src.Sweep.fns`) matching `Spec.fullM6SweepConeSpec`,
composing `step13_cone_bin_pass_wp` (`WpConeBin`) and `step13_cone_occ_pass_wp` (`WpCone1`).
Zero legacy imports; zero `@[expose]` on theorems, lemmas, or sections.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Sweep

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Kitten

open scoped FullArenaTactics FullK6DynMem M6SweepTactics

private theorem cone_getElem_congr {α : Type} {xs : List α} {i j : Nat}
    (h : i = j) (hi : i < xs.length) (hj : j < xs.length) : xs[i]'hi = xs[j]'hj := by
  subst h; rfl

private theorem s13_cone_call_k6_init {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (hInit : Γ.Has "full_k6_init" Kitten.Spec.step13K6InitSpec)
    {c : FullCfg} {L : K6Layout} {s : FullState} {mv : BitVec 32}
    {R : Mem 64 → Prop} {m : Mem 64} {k : Tup Val [] → Expr Val Cont rs}
    (hcap : k6MinScr ≤ c.scratch_cap) (hLscr : L.scrLen = c.scratch_cap)
    (hLmv : L.maxV = k6MaxV c.scratch_cap) (hmv_le : mv.toNat ≤ k6MaxV c.scratch_cap)
    (hlen : s.LengthsOk c)
    (hclean : K6HwmClean L (s.scratch.glue_used[33]?.getD 0#32)
      (k6StateOfScratch L s.scratch.scratch_buf))
    (hm : (FullMem c s ⋆ R) m)
    (hk : ∀ (scr0 gu0 : List (BitVec 32)) (m0 : Mem 64),
      ({ s with scratch := { s.scratch with scratch_buf := scr0, glue_used := gu0 } } :
        FullState).LengthsOk c →
      (∀ i < 64, i ≠ 33 → gu0[i]? = s.scratch.glue_used[i]?) →
      K6HwmClean L (gu0[33]?.getD 0#32) (k6StateOfScratch L scr0) →
      (∀ P, K6Inv L P (k6StateOfScratch L scr0)) → K6TrailSynced (k6StateOfScratch L scr0) →
      (k6StateOfScratch L scr0).nv = mv → (k6StateOfScratch L scr0).nc = 0#32 →
      (k6StateOfScratch L scr0).lvl = 0#32 → (k6StateOfScratch L scr0).trl_end = 0#32 →
      (k6StateOfScratch L scr0).nassump = 0#32 →
      (FullMem c { s with scratch := { s.scratch with scratch_buf := scr0, glue_used := gu0 } } ⋆
        R) m0 →
      wp Γ Q X (k ()) m0) :
    wp Γ Q X (.call (as := [i64, i32]) (bs := []) "full_k6_init"
      (Arg.var c.hdr, Arg.var mv, ()) k) m := by
  m6_call hInit
  refine ⟨c, s, R, rfl, hlen, hm, fun h => by dsimp only [Arg.val_var] at h; omega,
    fun _ _ => ⟨L, hLscr, hLmv, hclean, ?_⟩⟩
  intro scr0 gu0 m0
  dsimp only
  intro hlen0 _ hgu0 _ _ hcl0 hinv0 hsy0 hnv0 hnc0 hlvl0 _ htr0 _ _ hna0 _ _ _ hm0
  exact hk scr0 gu0 m0 hlen0 hgu0 hcl0 hinv0 hsy0 hnv0 hnc0 hlvl0 htr0 hna0 hm0

public section

theorem full_m6_sweep_cone_wp (Γ : Env)
    (hMaxV : Γ.Has "full_m6_max_v" Kitten.Spec.m6MaxVSpec)
    (hInit : Γ.Has "full_k6_init" Kitten.Spec.step13K6InitSpec)
    (hAddCl : Γ.Has "full_k6_add_clause" Kitten.Spec.step13K6AddClauseHwSpec) :
    ∀ args m Q X, Spec.fullM6SweepConeSpec args m Q X →
      Func.wp Γ Src.Sweep.full_m6_sweep_cone_body args m Q X := by
  rintro ⟨h, root_v, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hdense, hcap, hroot, htmk, ⟨L, hLscr, hLmv, hclean0⟩, hm, hQ⟩
  have hlen := hdense.1; have hw := hdense.2.1; have hnd := hdense.2.2.2.1
  have hcl0 := hdense.2.2.2.2.2.1; have hdm := hdense.2.2.2.2.2.2
  have hcv_le := hlen.core_ok.cur_vars_le
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hdwatches : DenseWatchesInv F_cur s.core := by
    have hmw := hw.watches; unfold ModeWatchesInv at hmw; rwa [ite_eq_right hdm] at hmw
  have hmL := L.hmaxV
  have hscr64 : c.scratch_cap < 2 ^ 64 := Nat.lt_trans c.hscr (by unfold dimacsBound; decide)
  let mv : BitVec 32 := (BitVec.ofNat 64 (k6MaxV c.scratch_cap)).setWidth 32
  have hmv_eq : mv = L.mv32 := by
    apply BitVec.eq_of_toNat_eq
    simp only [mv, K6PtrTactics.k6_mv32_toNat, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), hLmv]
  have hmv_nat : mv.toNat = L.maxV := by rw [hmv_eq, K6PtrTactics.k6_mv32_toNat]
  have hmo_nat : (mv * 3#32).toNat = L.maxOrig := by unfold K6Layout.maxOrig; bv_omega
  have hkptr_c0 : c.pScratchBuf + BitVec.setWidth 64
      ((1280 : BitVec 32) + (mv <<< (1 : Nat))) * 4 = L.kPtr c.pScratchBuf :=
    m6_k6Ptr_eq hLmv (by omega)
  have hqnext_c0 : L.kPtr c.pScratchBuf + BitVec.setWidth 64
      ((32 : BitVec 32) + (3 : BitVec 32) * mv) * 4 =
      L.kPtr c.pScratchBuf + BitVec.ofNat 64 (4 * L.oQNext) := by
    rw [hmv_eq]; exact K6PtrTactics.k6_ptr_qnext L (L.kPtr c.pScratchBuf)
  unfold Func.wp Src.Sweep.full_m6_sweep_cone_body
  c0_hsteps_nogrp
  refine m6_call_max_v hMaxV hscr64 ?_
  c0_hsplit
  · exfalso
    have hz : mv = 0#32 := ‹_›
    have h0 := congrArg BitVec.toNat hz; rw [hmv_nat] at h0; simp at h0; omega
  · have hgu28_lt : (BitVec.signExtend 64 (28 : BitVec 32)).toNat < s.scratch.glue_used.length := by
      rw [hlen.scratch_ok.glue_used_len]; decide
    c0_hsteps_nogrp
    refine wp_join_group (ts := [i32]) (fun (comp, ()) m1 => comp.toNat ≤ 5 ∧ m1 = m) ?_ ?_
    · rintro _ ⟨comp, ⟨⟩⟩ m1 ⟨hcomp_le, hm1⟩
      subst m1
      c0_hsteps_nogrp
      refine wp_join_group (ts := [i32])
        (fun (dlim, ()) m2 => dlim.toNat ≤ 3 ∧ m2 = m) ?_ ?_
      · rintro _ ⟨dlim, ⟨⟩⟩ m2 ⟨hdlim_le, hm2⟩
        subst m2
        c0_hsteps_nogrp
        refine wp_join_group (ts := [i32])
          (fun (mv_c, ()) m3 => mv_c.toNat ≤ mv.toNat ∧ m3 = m) ?_ ?_
        · rintro _ ⟨mv_c, ⟨⟩⟩ m3 ⟨hmvc_le, hm3⟩
          subst m3
          c0_hsteps_nogrp
          refine wp_join_group (ts := [i32])
            (fun (mc_c, ()) m4 => mc_c.toNat ≤ L.maxOrig ∧ m4 = m) ?_ ?_
          · rintro _ ⟨mc_c, ⟨⟩⟩ m4 ⟨hmcc_le, hm4⟩
            subst m4
            c0_hsteps_nogrp
            refine s13_cone_call_k6_init hInit hcap hLscr hLmv
              (by dsimp only [Prod.fst]; change mv.toNat ≤ _; omega) hlen hclean0 hm ?_
            intro scr0 gu0 m0 hlen0 hgu0 hcl0_k hinv0 hsy0 hnv0 hnc0 hlvl0 htr0 hna0 hm0
            let s0 : FullState :=
              { s with scratch := { s.scratch with scratch_buf := scr0, glue_used := gu0 } }
            have hscr0 : scr0.length = c.scratch_cap := hlen0.scratch_ok.scratch_buf_len
            let seed : BitVec 32 := (root_v ^^^ 2654435769#32) ||| 1#32
            let scr1 := scr0.set (L.k6Base + 25) seed
            have hscr1_len : scr1.length = L.scrLen := by
              simp [scr1, hscr0, hLscr]
            obtain ⟨hnv25, hnc25, hlvl25, htr25, hna25, hsy25, hinv25, hcl25⟩ :=
              s13_k6StateOfScratch_set25 L scr0 seed (hscr0.trans hLscr.symm)
            have hlen0_25 : ({ s with scratch :=
                { s.scratch with glue_used := gu0, scratch_buf := scr1 } } :
                FullState).LengthsOk c :=
              ⟨hlen0.core_ok, { hlen0.scratch_ok with scratch_buf_len := by simp [scr1, hscr0] }⟩
            obtain ⟨hlen1, hag1, hgu1, hcone1⟩ :=
              step13_cone_init_ok (F_cur := F_cur) hlen hLscr hmv_eq (by omega) hroot htmk
                hscr1_len hlen0_25 hgu0 (hcl25 _ hcl0_k) (fun P => hinv25 P (hinv0 P))
                (hsy25 hsy0) (hnv25.trans hnv0) (hnc25.trans hnc0) (hlvl25.trans hlvl0)
                (htr25.trans htr0) (hna25.trans hna0)
            have h25_store := FullK6DynMem.store_m6_full_k6_hdr (L := L) seed hLscr hscr0
              (idx := 25) (by decide) hm0
            have h0_wk0 : (BitVec.signExtend 64 (0 : BitVec 32)).toNat <
                s0.scratch.work_stk1.length := by
              rw [hlen0.scratch_ok.work_stk1_len,
                show (BitVec.signExtend 64 (0 : BitVec 32)).toNat = 0 from rfl]; omega
            have hrt_tm0 : (BitVec.setWidth 64 root_v).toNat <
                s0.scratch.tarjan_mark.length := by
              rw [hlen0.scratch_ok.tarjan_mark_len, bv_c0_zext32_64]; omega
            clear hm
            c0_hsteps_nogrp
            rw [hkptr_c0]
            c0_hsteps_nogrp
            -- Outer BFS depth loop (`Jd`)
            refine wp_loop_inv (ts := [i32, i32, i32, i32, .bool])
              (fun (nv, nc, qi, depth, _lim, ()) mo =>
                qi.toNat ≤ nv.toNat ∧ depth.toNat ≤ dlim.toNat ∧ ∃ st : FullState,
                  st.LengthsOk c ∧ AgreesExcept step13ConeMask s st ∧
                  S13GuOk L s nv.toNat st ∧ FidConeInv F_cur L mv st nv.toNat nc.toNat ∧
                  (FullMem c st ⋆ R) mo)
              (fun (_, _, _, depth, _, ()) _ => dlim.toNat - depth.toNat) ?_ ?_
            · intro _ hJd
              c0_hsteps!
              refine hJd (1#32, 0#32, 0#32, 0#32, false, ()) _
                ⟨Nat.zero_le _, Nat.zero_le _, _, hlen1, hag1, hgu1, hcone1, ?_⟩
              simpa only [s0, scr1, seed,
                show (BitVec.signExtend 64 (0 : BitVec 32)).toNat = 0 from rfl,
                bv_c0_zext32_64] using ‹_›
            · rintro _ ⟨nv, nc, qi, depth, lim, ⟨⟩⟩ mo
                ⟨hqi_le, hdep_le, st, hlen_st, hag_st, hgu_st, hcone_st, hmo⟩ hJd
              refine wp_join_group (ts := [])
                (fun () m_ex => ∃ st_e : FullState,
                  st_e.LengthsOk c ∧ AgreesExcept step13ConeMask s st_e ∧
                  S13GuOk L s nv.toNat st_e ∧ FidConeInv F_cur L mv st_e nv.toNat nc.toNat ∧
                  (FullMem c st_e ⋆ R) m_ex) ?_ ?_
              · rintro _ ⟨⟩ m_ex ⟨st_e, hlen_e, hag_e, hgu_e, hcone_e, hm_e⟩
                let ks_e := k6StateOfScratch L st_e.scratch.scratch_buf
                have hte_le : ks_e.trl_end.toNat ≤ nv.toNat :=
                  m6_trl_end_le_of_bdd hcone_e.k6_inv hcone_e.k6_trl_bdd
                have hnv_ge1 := hcone_e.nv_ge1
                have hnv_leMax : nv.toNat ≤ L.maxV :=
                  Nat.le_trans hcone_e.nv_le_mvC hcone_e.mvC_leMax
                obtain ⟨Rfr, hRfr⟩ : ∃ Rfr : Mem 64 → Prop, Rfr = (FullK6Frame c L st_e ⋆ R) :=
                  ⟨_, rfl⟩
                have hm_ka : (K6MemA L (L.kPtr c.pScratchBuf) ks_e ⋆ Rfr) m_ex := by
                  rw [fullMem_eq_k6Frame hcone_e.scr_len] at hm_e
                  rw [hRfr]
                  exact k6Mem_to_amem hcone_e.k6_inv.shapes (sep_ac hm_e)
                clear hm_e
                open scoped K6MemATactics K6PtrTactics in c0_hsteps_nogrp
                refine wp_join_group (ts := [i32])
                  (fun (un_v, ()) mu => un_v = nv - ks_e.trl_end ∧
                    (K6MemA L (L.kPtr c.pScratchBuf) (ks_e.putHdr .nv nv) ⋆ Rfr) mu) ?_ ?_
                · rintro _ ⟨un_v, ⟨⟩⟩ mu ⟨hun_eq, hmu⟩
                  subst hun_eq
                  have hnv_sub_bv : (nv - (1 : BitVec 32)).toNat = nv.toNat - 1 := by bv_omega
                  have hnv_subMax : (nv - (1 : BitVec 32)).toNat < K6MemATactics.szV L := by
                    dsimp only [K6MemATactics.szV]; rw [hnv_sub_bv]; omega
                  open scoped K6MemATactics K6PtrTactics in c0_hsteps_nogrp
                  refine wp_join_group (ts := [])
                    (fun () mf =>
                      (K6MemA L (L.kPtr c.pScratchBuf)
                        ((((((ks_e.putHdr .nv nv).putHdr .unass (nv - ks_e.trl_end)).putHdr .qlast
                          (nv - 1#32)).putHdr .qsearch (nv - 1#32)).putHdr .qstamp nv).putArr .qnext
                            (nv.toNat - 1) 4294967295#32) ⋆ Rfr) mf) ?_ ?_
                  · rintro _ ⟨⟩ mf hmf
                    c0_hsteps!
                    rw [hRfr] at hmf
                    exact step13_cone_exit_post hdense hcap hLscr hLmv hlen_e hag_e hgu_e
                      hcone_e hmf hQ
                  · intro _ hJnv
                    open scoped K6MemATactics K6PtrTactics in c0_hsplit
                    · open scoped K6MemATactics K6PtrTactics in c0_hsteps_nogrp
                      rw [hqnext_c0]
                      open scoped K6MemATactics K6PtrTactics in c0_hsteps!
                      rw [hnv_sub_bv, show (1 : BitVec 32) = 1#32 from rfl,
                        show (4294967295 : BitVec 32) = 4294967295#32 from rfl] at ‹_›
                      exact hJnv () _ ‹_›
                    · exfalso; have : nv = 0#32 := by bv_omega
                      have h0 := congrArg BitVec.toNat this; simp at h0; omega
                · intro _ hJter
                  c0_hsplit
                  · c0_hsteps!; exact hJter (nv - ks_e.trl_end, ()) _ ⟨rfl, ‹_›⟩
                  · exfalso; exact (‹¬ ks_e.trl_end.toNat ≤ nv.toNat›) hte_le
              · intro _ hJex
                c0_hsplit
                · have hqi_lt : qi.toNat < nv.toNat := ‹_›
                  c0_hsplit
                  · have hdep_lt : depth.toNat < dlim.toNat := ‹_›
                    c0_hsplit
                    · c0_hsteps!; exact hJex () mo ⟨st, hlen_st, hag_st, hgu_st, hcone_st, hmo⟩
                    · c0_hsplit
                      · have hdep1 : (depth + 1#32).toNat = depth.toNat + 1 :=
                          m6_bv32_add1 (by omega)
                        obtain ⟨layer_end, hle_def⟩ : ∃ le : BitVec 32, le = nv := ⟨_, rfl⟩
                        c0_hsteps_nogrp
                        -- Layer BFS loop (`Jll`)
                        refine wp_loop_inv (ts := [i32, i32, i32, .bool])
                          (fun (nv_l, nc_l, qi_l, _lim_l, ()) ml =>
                            qi_l.toNat ≤ layer_end.toNat ∧ layer_end.toNat ≤ nv_l.toNat ∧
                            ∃ st_l : FullState,
                              st_l.LengthsOk c ∧ AgreesExcept step13ConeMask s st_l ∧
                              S13GuOk L s nv_l.toNat st_l ∧
                              FidConeInv F_cur L mv st_l nv_l.toNat nc_l.toNat ∧
                              (FullMem c st_l ⋆ R) ml)
                          (fun (_, _, qi_l, _, ()) _ => layer_end.toNat - qi_l.toNat) ?_ ?_
                        · intro _ hJll
                          c0_hsteps!
                          exact hJll (nv, nc, qi, lim, ()) mo
                            ⟨hle_def ▸ hqi_le, hle_def ▸ le_refl _, st, hlen_st, hag_st, hgu_st,
                              hcone_st, hmo⟩
                        · rintro Jll ⟨nv_l, nc_l, qi_l, lim_l, ⟨⟩⟩ ml
                            ⟨hqi_l_le, hle_nv_l, st_l, hlen_l, hag_l, hgu_l, hcone_l, hml⟩ hJll
                          c0_hsplit
                          · have hqi_l_lt : qi_l.toNat < layer_end.toNat := hle_def ▸ ‹_›
                            c0_hsplit
                            · c0_hsteps!
                              exact hJd (nv_l, nc_l, qi_l, depth + 1#32, lim_l, ()) ml
                                (by dsimp only; omega)
                                ⟨Nat.le_trans hqi_l_le hle_nv_l, by rw [hdep1]; omega, st_l,
                                  hlen_l, hag_l, hgu_l, hcone_l, hml⟩
                            · c0_hsplit
                              · have hqi_nv : qi_l.toNat < nv_l.toNat :=
                                  Nat.lt_of_lt_of_le hqi_l_lt hle_nv_l
                                have hqi_ws : (BitVec.setWidth 64 qi_l).toNat <
                                    st_l.scratch.work_stk1.length := by
                                  rw [bv_c0_zext32_64, hlen_l.scratch_ok.work_stk1_len]
                                  have := hcone_l.nv_le_cv
                                  have := hlen_l.core_ok.cur_vars_le; omega
                                let cv : BitVec 32 :=
                                  st_l.scratch.work_stk1[(BitVec.setWidth 64 qi_l).toNat]'hqi_ws
                                have hwk_cv :
                                    (st_l.scratch.work_stk1[qi_l.toNat]?.getD 0#32).toNat =
                                    cv.toNat := by
                                  have hbd : qi_l.toNat < st_l.scratch.work_stk1.length :=
                                    bv_c0_zext32_64 qi_l ▸ hqi_ws
                                  rw [List.getElem?_eq_getElem hbd, Option.getD_some]
                                  exact congrArg BitVec.toNat
                                    (cone_getElem_congr (bv_c0_zext32_64 qi_l).symm hbd hqi_ws)
                                have hfwd_l := hcone_l.fwd qi_l.toNat hqi_nv
                                rw [hwk_cv] at hfwd_l
                                have hcv_tm : (BitVec.setWidth 64 cv).toNat <
                                    st_l.scratch.tarjan_mark.length := by
                                  rw [bv_c0_zext32_64, hlen_l.scratch_ok.tarjan_mark_len]
                                  have := hlen_l.core_ok.cur_vars_le; omega
                                let cur_tmk : BitVec 32 :=
                                  st_l.scratch.tarjan_mark[(BitVec.setWidth 64 cv).toNat]'hcv_tm
                                have htmk_cv : st_l.scratch.tarjan_mark[cv.toNat]?.getD 0#32 =
                                    BitVec.ofNat 32 (qi_l.toNat + 1) := hfwd_l.2
                                have hcur_eq : cur_tmk =
                                    st_l.scratch.tarjan_mark[cv.toNat]?.getD 0#32 := by
                                  have hbd : cv.toNat < st_l.scratch.tarjan_mark.length :=
                                    bv_c0_zext32_64 cv ▸ hcv_tm
                                  rw [List.getElem?_eq_getElem hbd, Option.getD_some]
                                  exact cone_getElem_congr (bv_c0_zext32_64 cv) hcv_tm hbd
                                have hqi1 : (qi_l + 1#32).toNat = qi_l.toNat + 1 :=
                                  m6_bv32_add1 (by
                                    have := hcone_l.nv_le_cv
                                    have := hlen_l.core_ok.cur_vars_le; omega)
                                have hb_l : Step13ConeBase F_cur L mv c s cv qi_l
                                    nv_l.toNat nc_l.toNat st_l :=
                                  ⟨hlen_l, hag_l, hgu_l, hcone_l, htmk_cv, hwk_cv⟩
                                c0_hsteps_nogrp
                                dsimp only [Prod.fst, Prod.snd]
                                refine step13_cone_bin_pass_wp
                                  (aCv := Arg.var cv) (aCurTmk := Arg.var (cur_tmk - 1#32))
                                  (aMvC := Arg.var mv) (aLimV := Arg.var mv_c)
                                  (aMaxOrig := Arg.var (mv * 3#32)) (aLayerStart := Arg.var qi)
                                  (aNv0 := Arg.var nv_l) (aNc0 := Arg.var nc_l)
                                  (aLim0 := Arg.var lim_l)
                                  (k_done := fun nv1 nc1 lim1 =>
                                    s13OccPassExpr c.hdr c.pArena c.pWvec c.pWstk c.pVals
                                      c.pFlags c.pTarjanMark c.pTmp c.pWorkStk1
                                      (L.kPtr c.pScratchBuf) (Arg.var cv) (Arg.var cur_tmk)
                                      (Arg.var mv) (Arg.var mv_c) (Arg.var (mv * 3#32))
                                      (Arg.var nv1) (Arg.var nc1) (Arg.var lim1)
                                      (fun nv2 nc2 lim2 => Expr.jump Jll
                                        (Arg.var nv2, Arg.var nc2, Arg.var (qi_l + 1#32),
                                         Arg.var lim2, ())))
                                  hAddCl hLscr hLmv rfl rfl rfl rfl
                                  rfl rfl rfl rfl rfl rfl rfl rfl hmvc_le rfl rfl rfl rfl
                                  (by dsimp only [Arg.val_var]; omega) hlen hw hcl0 hdwatches
                                  hqi_l_lt hle_nv_l (by dsimp only [Arg.val_var]; rw [hcur_eq])
                                  hb_l hml ?_
                                intro nv1 nc1 lim1 st1 m1 hle1 _ _ hb1 hm1
                                refine step13_cone_occ_pass_wp
                                  hAddCl hLscr hLmv rfl rfl rfl rfl
                                  rfl rfl rfl rfl rfl rfl rfl rfl rfl hmvc_le rfl rfl rfl rfl
                                  (by dsimp only [Arg.val_var]; omega) hlen hw hcl0 hnd hdwatches
                                  hqi_l_lt hle1 hb1 hm1 ?_
                                intro nv2 nc2 lim2 st2 m2 hle2 hb2 hm2
                                c0_hsteps!
                                exact hJll (nv2, nc2, qi_l + 1#32, lim2, ()) m2
                                  (by dsimp only; omega)
                                  ⟨by rw [hqi1]; omega, hle2, st2, hb2.hlen, hb2.hag, hb2.hgu,
                                    hb2.hcone, hm2⟩
                              · c0_hsteps!
                                exact hJd (nv_l, nc_l, qi_l, depth + 1#32, lim_l, ()) ml
                                  (by dsimp only; omega)
                                  ⟨Nat.le_trans hqi_l_le hle_nv_l, by rw [hdep1]; omega, st_l,
                                    hlen_l, hag_l, hgu_l, hcone_l, hml⟩
                          · c0_hsteps!
                            exact hJd (nv_l, nc_l, qi_l, depth + 1#32, lim_l, ()) ml
                              (by dsimp only; omega)
                              ⟨Nat.le_trans hqi_l_le hle_nv_l, by rw [hdep1]; omega, st_l,
                                hlen_l, hag_l, hgu_l, hcone_l, hml⟩
                      · c0_hsteps!; exact hJex () mo ⟨st, hlen_st, hag_st, hgu_st, hcone_st, hmo⟩
                  · c0_hsteps!; exact hJex () mo ⟨st, hlen_st, hag_st, hgu_st, hcone_st, hmo⟩
                · c0_hsteps!; exact hJex () mo ⟨st, hlen_st, hag_st, hgu_st, hcone_st, hmo⟩
          · intro _ hJ4
            c0_hsplit
            · c0_hsteps!; exact hJ4 (mv * 3#32, ()) m ⟨by omega, rfl⟩
            · c0_hsteps!
              refine hJ4 (_, ()) m ⟨?_, rfl⟩
              have hnl : ¬ (mv * 3#32).toNat <
                  ((1024 : BitVec 32) <<< (comp.toNat % 32)).toNat := by
                simpa only [mv, BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
                  BitVec.toNat_shiftLeft, Nat.shiftLeft_eq] using (‹_› : ¬ _ < _)
              omega
        · intro _ hJ3
          c0_hsplit
          · c0_hsteps!; exact hJ3 (mv, ()) m ⟨le_refl _, rfl⟩
          · c0_hsteps!
            refine hJ3 (_, ()) m ⟨?_, rfl⟩
            have hnl : ¬ mv.toNat < ((256 : BitVec 32) <<< (comp.toNat % 32)).toNat := by
              simpa only [mv, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
                BitVec.toNat_shiftLeft, Nat.shiftLeft_eq] using (‹_› : ¬ _ < _)
            omega
      · intro _ hJ2
        c0_hsplit
        · c0_hsteps!; exact hJ2 (3#32, ()) m ⟨by decide, rfl⟩
        · c0_hsteps!; exact hJ2 (2#32, ()) m ⟨by decide, rfl⟩
    · intro _ hJ1
      c0_hsplit
      · c0_hsteps!; exact hJ1 (5#32, ()) m ⟨by decide, rfl⟩
      · c0_hsteps!
        have hle : (s.scratch.glue_used[28]'(by rw [hlen.scratch_ok.glue_used_len]; decide)).toNat
            ≤ 5 := by
          have hng : ¬ (5 : Nat) < (s.scratch.glue_used[28]'(by
            rw [hlen.scratch_ok.glue_used_len]; decide)).toNat := ‹_›
          omega
        exact hJ1 (_, ()) m ⟨hle, rfl⟩

end

end LeanQbe.T.Examples.Kissat.Proof.Sweep
