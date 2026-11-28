/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Analyze.Helpers

/-!
# WP Proof for `full_restore_bump_ana_mode_fid` (`Proof.Analyze.WpRestore`)

Proves `full_restore_bump_ana_mode_fid_wp` against canonical
`Analyze.Spec.fullRestoreBumpAnaModeSpec`
(`0` legacy `Full*` imports, `0` `@[expose]` on theorems/sections, `<= 100` cols).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Analyze.WpRestore

open Std.Sat
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.C0Step LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Bump.Spec
open LeanQbe.T.Examples.Kissat.Proof.Analyze.Spec
open LeanQbe.T.Examples.Kissat.Proof.Analyze.Helpers
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.M6HdrTactics
open Kraken.Bedrock2.Test

public section

private theorem mrk_all_zero_of_cov0 {c : FullCfg} {s : FullState}
    (hcov : FullAnaMarksCov c s) (hm0 : s.core.min_clr_len = 0) :
    ∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 = 0#8 := by
  intro v hv
  by_cases h0 : s.core.mrk[v]?.getD 0#8 = 0#8
  · exact h0
  · obtain ⟨i, hi, _⟩ := hcov.2.2.2 v hv h0
    omega

private theorem cov_init_of_zero {c : FullCfg} {s : FullState}
    (hmrk0 : ∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 = 0#8)
    (hmcl0 : s.core.min_clr_len = 0) : FullAnaMarksCov c s := by
  refine ⟨by rw [hmcl0]; exact Nat.zero_le _, by simp [hmcl0], fun k hk => by omega, ?_⟩
  intro v hv hnz
  exact absurd (hmrk0 v hv) hnz

private theorem mrk_zext32_eq0 {x : BitVec 8}
    (h : BitVec.setWidth 32 x = BitVec.ofNat (OfNat.ofNat 32) (OfNat.ofNat 0)) :
    x = 0#8 := by
  have hsw := congrArg BitVec.toNat h
  have hlt : x.toNat < 2 ^ 32 := Nat.lt_trans (BitVec.isLt x) (by omega)
  have h0 : x.toNat = 0 := by simpa [BitVec.toNat_setWidth, Nat.mod_eq_of_lt hlt] using hsw
  exact BitVec.eq_of_toNat_eq (by simpa using h0)

private theorem restore_core_lengthsOk {c : FullCfg} {s0 s1 : FullState}
    (h1 : s1.LengthsOk c) (hcore : s1.core = { s0.core with mrk := s1.core.mrk })
    {mrk' : List (BitVec 8)} {mcl' : Nat} {repr' : List (BitVec 32)} {sc' : FullScratch}
    (hmrk : mrk'.length = c.max_vars) (hrepr : repr'.length = 2 * c.max_vars)
    (hmcl : mcl' ≤ c.max_vars) (hscr : sc'.LengthsOk c) :
    ({ core := { s0.core with mrk := mrk', min_clr_len := mcl', repr := repr' }
       scratch := sc' } : FullState).LengthsOk c := by
  have h1c := h1.core_ok
  rw [hcore] at h1c
  exact ⟨{ h1c with mrk_len := hmrk, min_clr_len_le := hmcl, repr_len := hrepr }, hscr⟩

private theorem restore_bump_clear_wp (Γ : Env)
    (hBump : Γ.Has "full_bump_analyzed_mode_fid" fullBumpAnalyzedModeSpec)
    (hClr : Γ.Has "full_clear_ana" Deduce.Spec.fullClearAnaSpec)
    {c : FullCfg} {ext : List (BitVec 64)} {s0 s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} {Q : Post []} {X : XPost} {ar : Bool} {J_ret : Cont []}
    (hcfg : FullM6HdrCfgOk c) (hext : M6HdrExtOk ext) (hlen : s.LengthsOk c)
    (hcov : FullAnaMarksCov c s) (hprob0 : s0.core.probing = 0#64)
    (hcore : s.core = { s0.core with mrk := s.core.mrk, min_clr_len := s.core.min_clr_len })
    (hpres0 : FullExtScratchPres s0 s) (hws2 : s.scratch.work_stk2 = s0.scratch.work_stk2)
    (hm : (FullMem c s ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R)) m)
    (hRet : ∀ mrk' mcl' repr' sc' ext' m',
      let s' : FullState :=
        { core := { s0.core with mrk := mrk', min_clr_len := mcl', repr := repr' }
          scratch := sc' }
      s'.LengthsOk c → (∀ v < c.max_vars, mrk'[v]?.getD 0#8 = 0#8) →
      (s0.core.probing = 0#64 → mcl' = 0) →
      (s0.core.probing ≠ 0#64 → mcl' = s0.core.min_clr_len) →
      FullExtScratchPres s0 s' → sc'.work_stk2 = s0.scratch.work_stk2 →
      M6HdrExtOk ext' → (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext ext') →
      (FullM6HdrMem c ext' s' ⋆ R) m' → J_ret () m') :
    wp Γ Q X
      (Expr.call (as := [i64, .bool]) (bs := []) "full_bump_analyzed_mode_fid"
        (Arg.var c.hdr, Arg.var ar, ()) fun _ =>
        Expr.call (as := [i64]) (bs := []) "full_clear_ana" (Arg.var c.hdr, ()) fun _ =>
          Expr.jump J_ret ()) m := by
  have hmHdr : (FullM6HdrMem c ext s ⋆ R) m := fullM6HdrMem_unfocus hm
  c0_call hBump
  refine fullBumpAnalyzedModeSpec_of hcfg hext hlen (fullBumpPre_of_cov ar hcov) hmHdr ?_
  intro mrk1 mcl1 repr1 sc1 ext1 m1 s1 hlen1 hcov1 _ _ hpres1 hws21 hext1 hw2b1 hm1
  have hcov1' : FullAnaMarksCov c s1 := hcov1 hcov
  c0_hsteps
  c0_call hClr
  have hm1f : (FullMem c s1 ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext1 ⋆ R)) m1 :=
    fullM6HdrMem_focus hm1
  refine ⟨c, s1, m6ExtMem (m6ExtAddr c.hdr) ext1 ⋆ R, rfl, hlen1, hm1f, ?_⟩
  intro mrk2 m2 hmrk2 _ _ hall0 hm2
  c0_hsteps
  have hmrk_all : ∀ v < c.max_vars, mrk2[v]?.getD 0#8 = 0#8 := hall0 hcov1'
  have hs1c : s1.core = { s0.core with mrk := mrk1, min_clr_len := mcl1, repr := repr1 } := by
    change { s.core with mrk := mrk1, min_clr_len := mcl1, repr := repr1 } = _
    rw [hcore]
  have hlen2 : ({ core := { s0.core with mrk := mrk2, min_clr_len := 0, repr := repr1 }
                  scratch := sc1 } : FullState).LengthsOk c := by
    have h1c := hlen1.core_ok
    rw [hs1c] at h1c
    exact ⟨{ h1c with mrk_len := hmrk2, min_clr_len_le := Nat.zero_le _ }, hlen1.scratch_ok⟩
  have hm2_eq : FullMem c { s1 with core := { s1.core with mrk := mrk2, min_clr_len := 0 } } =
      FullMem c { core := { s0.core with mrk := mrk2, min_clr_len := 0, repr := repr1 }
                  scratch := sc1 } := by
    have heq_st : ({ s1 with core := { s1.core with mrk := mrk2, min_clr_len := 0 } } :
        FullState) =
        { core := { s0.core with mrk := mrk2, min_clr_len := 0, repr := repr1 }
          scratch := sc1 } := by
      change ({ core := { s1.core with mrk := mrk2, min_clr_len := 0 }, scratch := s1.scratch } :
          FullState) = _
      rw [hs1c]
    rw [heq_st]
  rw [hm2_eq] at hm2
  exact hRet mrk2 0 repr1 sc1 ext1 m2 hlen2 hmrk_all (fun _ => rfl) (fun hn => absurd hprob0 hn)
    (fullExtScratchPres_trans hpres0 hpres1) (hws21.trans hws2) hext1 hw2b1
    (fullM6HdrMem_unfocus hm2)

private theorem restore_push_step {c : FullCfg} {s0 s1 : FullState} {mcl : Nat}
    (hlen1 : s1.LengthsOk c)
    (hcov1 : FullAnaMarksCov c { s1 with core := { s1.core with min_clr_len := mcl } })
    (hcore1 : s1.core = { s0.core with mrk := s1.core.mrk })
    (hpres1 : FullExtScratchPres s0 s1) (hws21 : s1.scratch.work_stk2 = s0.scratch.work_stk2)
    {v : Nat} (hv : v < s1.core.cur_vars) (hm0 : s1.core.mrk[v]?.getD 0#8 = 0#8) :
    let s2 : FullState :=
      { s1 with
        core := { s1.core with mrk := s1.core.mrk.set v 1#8 }
        scratch := { s1.scratch with
          work_stk1 := s1.scratch.work_stk1.set mcl (BitVec.ofNat 32 v) } }
    s2.LengthsOk c ∧
    FullAnaMarksCov c { s2 with core := { s2.core with min_clr_len := mcl + 1 } } ∧
    s2.core = { s0.core with mrk := s2.core.mrk } ∧
    FullExtScratchPres s0 s2 ∧ s2.scratch.work_stk2 = s0.scratch.work_stk2 := by
  intro s2
  let s1c : FullState := { s1 with core := { s1.core with min_clr_len := mcl } }
  have hmcl_le : mcl ≤ c.max_vars := by
    have h1 := hcov1.1; have h2 := hlen1.core_ok.cur_vars_le; exact Nat.le_trans h1 h2
  have hlen1c : s1c.LengthsOk c :=
    ⟨{ hlen1.core_ok with min_clr_len_le := hmcl_le }, hlen1.scratch_ok⟩
  have hcov2 := s13b_push_marksCov_gen hlen1c hcov1 hv hm0 (by decide : (1#8 : BitVec 8) ≠ 0#8)
  have hlen2 : s2.LengthsOk c :=
    ⟨{ hlen1.core_ok with
        mrk_len := by simp [s2, List.length_set, hlen1.core_ok.mrk_len] },
     fullScratch_lengthsOk_of_arr_len hlen1.scratch_ok rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
       rfl (by simp [s2, List.length_set, hlen1.scratch_ok.work_stk1_len]) rfl rfl rfl rfl rfl rfl
       rfl rfl rfl rfl rfl⟩
  have hcore2 : s2.core = { s0.core with mrk := s2.core.mrk } := by
    change { s1.core with mrk := s1.core.mrk.set v 1#8 } = _
    rw [hcore1]
  have hcov2' : FullAnaMarksCov c { s2 with core := { s2.core with min_clr_len := mcl + 1 } } := by
    simpa [s2, s1c] using hcov2
  exact ⟨hlen2, hcov2', hcore2, fullExtScratchPres_trans hpres1 ⟨rfl, rfl⟩, hws21⟩

theorem full_restore_bump_ana_mode_fid_wp (Γ : Env)
    (hBump : Γ.Has "full_bump_analyzed_mode_fid" fullBumpAnalyzedModeSpec)
    (hClr : Γ.Has "full_clear_ana" Deduce.Spec.fullClearAnaSpec) :
    ∀ args m Q X,
      fullRestoreBumpAnaModeSpec args m Q X →
      Func.wp Γ Src.Analyze.full_restore_bump_ana_mode_fid_body args m Q X := by
  rintro ⟨h, ar, ⟨⟩⟩ m Q X hs
  rcases fullRestoreBumpAnaModeSpec_elim hs with
    ⟨c, ext, s, R, rfl, hcfg, hext, hlen, hmrk0, hm, hQ⟩
  have hm0 := fullM6HdrMem_focus hm
  clear hm
  unfold Func.wp Src.Analyze.full_restore_bump_ana_mode_fid_body
  c0_hsteps_nogrp
  · exact hQ s.core.mrk s.core.min_clr_len s.core.repr s.scratch ext m hlen hmrk0
      (fun hp => absurd hp hc) (fun _ => rfl) (fullExtScratchPres_refl s) rfl hext
      (fun hi => ⟨hi, M6ExtW2bPres.refl ext⟩) (fullM6HdrMem_unfocus hm0)
  · have hprob0 : s.core.probing = 0#64 := hc
    clear hc
    refine wp_join_state1 (t := i64) (fun x : BitVec 64 => x)
        (fun lim m' => lim.toNat ≤ s.core.cur_vars ∧ m' = m) ?_ ?_
    · intro _J lim m' ⟨hlim, hmEq⟩
      subst hmEq
      c0_hsteps_nogrp
      let Inv : (FullState × Nat × BitVec 64) → Nat → Mem 64 → Prop := fun st ub m'' =>
        st.1.LengthsOk c ∧
        FullAnaMarksCov c { st.1 with core := { st.1.core with min_clr_len := st.2.1 } } ∧
        st.1.core = { s.core with mrk := st.1.core.mrk } ∧
        FullExtScratchPres s st.1 ∧ st.1.scratch.work_stk2 = s.scratch.work_stk2 ∧
        st.2.2.toNat ≤ ub ∧ (FullMem c st.1 ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R)) m''
      let JInv : (FullState × Nat) → Mem 64 → Prop := fun st m'' =>
        st.1.LengthsOk c ∧
        FullAnaMarksCov c { st.1 with core := { st.1.core with min_clr_len := st.2 } } ∧
        st.1.core = { s.core with mrk := st.1.core.mrk } ∧
        FullExtScratchPres s st.1 ∧ st.1.scratch.work_stk2 = s.scratch.work_stk2 ∧
        (FullMem c st.1 ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R)) m''
      refine wp_while_state (fun st : FullState × Nat × BitVec 64 =>
            (BitVec.ofNat 64 st.2.1, st.2.2, ()))
          (fun st => lim.toNat - st.2.2.toNat) (fun st m'' => Inv st lim.toNat m'') ?_ ?_
      · intro J hJ
        c0_hsteps
        let sCov0 : FullState := { s with core := { s.core with min_clr_len := 0 } }
        have hcov0 : FullAnaMarksCov c sCov0 := cov_init_of_zero hmrk0 rfl
        exact hJ (s, 0, 0#64) m' ⟨hlen, hcov0, rfl, ⟨rfl, rfl⟩, rfl, by simp, hm0⟩
      · intro J ⟨s1, mcl1, idx⟩ m1 ⟨hlen1, hcov1, hcore1, hpres1, hws21, hidx_le, hm1⟩ ih
        dsimp only at *
        c0_hsteps_nogrp
        · have hidx_lt : idx.toNat < lim.toNat := by simpa using hc
          have hcv1 : s1.core.cur_vars = s.core.cur_vars := by rw [hcore1]
          have hmrk1_len : s1.core.mrk.length = c.max_vars := hlen1.core_ok.mrk_len
          have hcv1_le : s1.core.cur_vars ≤ c.max_vars := hlen1.core_ok.cur_vars_le
          have hws1_len1 : s1.scratch.work_stk1.length = 2 * c.max_vars :=
            hlen1.scratch_ok.work_stk1_len
          have hcv0_le : s.core.cur_vars ≤ c.max_vars := by rw [← hcv1]; exact hcv1_le
          have hidx_len : idx.toNat < s1.scratch.work_stk1.length := by
            rw [hws1_len1]; omega
          clear hc
          c0_hsteps_nogrp
          refine wp_join_state1 (t := i64)
              (fun st : FullState × Nat => BitVec.ofNat 64 st.2) JInv ?_ ?_
          · intro _Jc ⟨s2, mcl2⟩ m2 ⟨hlen2, hcov2, hcore2, hpres2, hws22, hm2⟩
            dsimp only at *
            c0_hsteps
            apply ih (s2, mcl2, idx + 1#64) m2
            · exact bv64_measure_sub_lt hidx_lt
            · exact ⟨hlen2, hcov2, hcore2, hpres2, hws22,
                by rw [bv64_add1_toNat hidx_lt]; omega, hm2⟩
          · intro Jc hJc
            c0_hsteps_nogrp
            · rename_i hc1
              have hcv0_64 : s.core.cur_vars < 2 ^ 64 := by
                have := fullInv_max_vars_lt32 c; rw [← hcv1]; omega
              have hget_ws : s1.scratch.work_stk1[idx.toNat]?.getD 0#32 =
                  s1.scratch.work_stk1[idx.toNat] := by
                simp [List.getElem?_eq_getElem hidx_len]
              have hv : (s1.scratch.work_stk1[idx.toNat]?.getD 0#32).toNat < s1.core.cur_vars := by
                rw [hget_ws, hcv1, ← Nat.mod_eq_of_lt hcv0_64]; exact hc1
              have hmrk_lt : s1.scratch.work_stk1[idx.toNat].toNat < s1.core.mrk.length := by
                rw [hmrk1_len, ← hget_ws]; exact Nat.lt_of_lt_of_le hv hcv1_le
              have hm_eq : s1.core.mrk[(s1.scratch.work_stk1[idx.toNat]?.getD 0#32).toNat]?.getD
                  0#8 = 0#8 := by
                rw [hget_ws, List.getElem?_eq_getElem hmrk_lt, Option.getD_some]
                exact mrk_zext32_eq0 hc
              have hp := restore_push_step hlen1 hcov1 hcore1 hpres1 hws21 hv hm_eq
              have hmcl_lt : mcl1 < 2 * c.max_vars := by
                have h1 : mcl1 + 1 ≤ s1.core.cur_vars := hp.2.1.1
                omega
              have hmcl_ws1 : mcl1 < s1.scratch.work_stk1.length := by
                have h1 : mcl1 + 1 ≤ s1.core.cur_vars := hp.2.1.1
                rw [hws1_len1]; omega
              have hmcl64 : mcl1 < 2 ^ 64 := by
                have := fullInv_max_vars_lt32 c; omega
              c0_hsteps
              rw [show (BitVec.ofNat 64 mcl1 + 1 : BitVec 64) = BitVec.ofNat 64 (mcl1 + 1) from
                (BitVec.ofNat_add mcl1 1).symm]
              have hv_w32 : BitVec.ofNat 32 (s1.scratch.work_stk1[idx.toNat]?.getD 0#32).toNat =
                  s1.scratch.work_stk1[idx.toNat] :=
                BitVec.eq_of_toNat_eq (by
                  have hlt32 := BitVec.isLt s1.scratch.work_stk1[idx.toNat]
                  rw [hget_ws, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt32])
              have hmcl_nat : (BitVec.ofNat 64 mcl1).toNat = mcl1 := by
                simp [Nat.mod_eq_of_lt hmcl64]
              have hws_lt64 : s1.scratch.work_stk1[idx.toNat].toNat < 2 ^ 64 :=
                Nat.lt_trans (BitVec.isLt _) (by omega)
              rw [hmcl_nat, show (BitVec.setWidth 64 s1.scratch.work_stk1[idx.toNat]).toNat =
                  (s1.scratch.work_stk1[idx.toNat]?.getD 0#32).toNat from by
                  simp [hget_ws, BitVec.toNat_setWidth, Nat.mod_eq_of_lt hws_lt64],
                show (BitVec.ofNat 8 1 : BitVec 8) = 1#8 from rfl] at hm
              exact hJc (_, mcl1 + 1) _ ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2, by
                simpa only [hv_w32] using hm⟩
            · exact hJc (s1, mcl1) m1 ⟨hlen1, hcov1, hcore1, hpres1, hws21, hm1⟩
            · exact hJc (s1, mcl1) m1 ⟨hlen1, hcov1, hcore1, hpres1, hws21, hm1⟩
        · c0_hsteps_nogrp
          refine wp_join_state1 (t := i64)
              (fun st : FullState × Nat => BitVec.ofNat 64 st.2) JInv ?_ ?_
          · intro _Jp ⟨s2, mcl2⟩ m2 ⟨hlen2, hcov2, hcore2, hpres2, hws22, hm2⟩
            dsimp only at *
            have hmcl_le : mcl2 ≤ c.max_vars := by
              have h1 : mcl2 ≤ s2.core.cur_vars := hcov2.1
              have h2 : s2.core.cur_vars ≤ c.max_vars := hlen2.core_ok.cur_vars_le
              omega
            have hmcl64 : mcl2 < 2 ^ 64 := by
              have := fullInv_max_vars_lt32 c; omega
            c0_hsteps_nogrp
            refine wp_join0 (fun m'' => Q () m'') (fun _ _ hq => hq) fun J_ret hJ_ret => ?_
            c0_hsteps
            · let s2c : FullState := { s2 with core := { s2.core with min_clr_len := mcl2 } }
              have hlen2c : s2c.LengthsOk c :=
                ⟨{ hlen2.core_ok with min_clr_len_le := hmcl_le }, hlen2.scratch_ok⟩
              have hcore2c : s2c.core =
                  { s.core with mrk := s2c.core.mrk, min_clr_len := s2c.core.min_clr_len } := by
                change { s2.core with min_clr_len := mcl2 } = _
                rw [hcore2]
              exact restore_bump_clear_wp Γ hBump hClr hcfg hext hlen2c hcov2 hprob0 hcore2c
                hpres2 hws22 hm
                (fun mrk' mcl' repr' sc' ext' m' h1 h2 h3 h4 h5 h6 h7 h8 h9 =>
                  hJ_ret m' (hQ mrk' mcl' repr' sc' ext' m' h1 h2 h3 h4 h5 h6 h7 h8 h9))
            · have hmcl0 : mcl2 = 0 := by
                by_cases h0 : mcl2 = 0
                · exact h0
                · have hlt : (0#64 : BitVec 64) < BitVec.ofNat 64 mcl2 := by
                    rw [BitVec.lt_def]
                    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hmcl64]; omega
                  exact absurd hlt (by simpa using hc)
              have hmrk_all := mrk_all_zero_of_cov0 hcov2 hmcl0
              let sFin : FullState :=
                { core := { s.core with mrk := s2.core.mrk, min_clr_len := 0 }
                  scratch := s2.scratch }
              have hrepr_s : s.core.repr.length = 2 * c.max_vars := by
                have := hlen2.core_ok.repr_len; rw [hcore2] at this; exact this
              have hlen_f : sFin.LengthsOk c :=
                restore_core_lengthsOk hlen2 hcore2 hlen2.core_ok.mrk_len hrepr_s
                  (Nat.zero_le _) hlen2.scratch_ok
              rw [hmcl0] at hm
              have hcore_f : ({ s2.core with min_clr_len := 0 } : FullCoreState) =
                  { s.core with mrk := s2.core.mrk, min_clr_len := 0 } := by
                change { s2.core with min_clr_len := 0 } = _; rw [hcore2]
              have hs_f : ({ s2 with core := { s2.core with min_clr_len := 0 } } : FullState) =
                  sFin :=
                congrArg (fun fc => ({ core := fc, scratch := s2.scratch } : FullState)) hcore_f
              rw [hs_f] at hm
              exact hJ_ret m (hQ s2.core.mrk 0 s.core.repr s2.scratch ext m hlen_f hmrk_all
                (fun _ => rfl) (fun hn => absurd hprob0 hn) hpres2 hws22 hext
                (fun hi => ⟨hi, M6ExtW2bPres.refl ext⟩) (fullM6HdrMem_unfocus hm))
          · intro Jp hJp
            c0_hsteps_nogrp
            · have htl_le : s1.core.tmp_len ≤ s1.core.cur_vars := by
                have hcv1 : s1.core.cur_vars = s.core.cur_vars := by rw [hcore1]
                have htl64 : s1.core.tmp_len < 2 ^ 64 := by
                  have := fullInv_max_vars_lt32 c; have := hlen1.core_ok.tmp_len_le; omega
                have hcv64 : s.core.cur_vars < 2 ^ 64 := by
                  have := fullInv_max_vars_lt32 c; have := hlen1.core_ok.cur_vars_le
                  rw [hcv1] at this; omega
                rw [Nat.mod_eq_of_lt htl64, Nat.mod_eq_of_lt hcv64] at hc
                rw [hcv1]; exact hc
              clear hc
              refine wp_while_state (fun st : FullState × Nat × BitVec 64 =>
                    (BitVec.ofNat 64 st.2.1, st.2.2, ()))
                  (fun st => s1.core.tmp_len - st.2.2.toNat)
                  (fun st m'' => Inv st s1.core.tmp_len m'') ?_ ?_
              · intro J2 hJ2
                c0_hsteps
                exact hJ2 (s1, mcl1, 0#64) m1 ⟨hlen1, hcov1, hcore1, hpres1, hws21, by simp, hm1⟩
              · intro J2 ⟨s2, mcl2, jdx⟩ m2 ⟨hlen2, hcov2, hcore2, hpres2, hws22, hj_le, hm2⟩ ih2
                dsimp only at *
                c0_hsteps_nogrp
                · have htl2 : s2.core.tmp_len = s1.core.tmp_len := by rw [hcore2, hcore1]
                  have htl_lt64 : s1.core.tmp_len < 2 ^ 64 := by
                    have := fullInv_max_vars_lt32 c; have := hlen1.core_ok.tmp_len_le; omega
                  have hj_lt : jdx.toNat < s1.core.tmp_len := by
                    rw [Nat.mod_eq_of_lt htl_lt64] at hc; exact hc
                  have hj_len : jdx.toNat < s2.core.tmp.length := by
                    rw [hlen2.core_ok.tmp_len_arr]
                    have := hlen1.core_ok.cur_vars_le; omega
                  have hj_add1 : (jdx + 1#64).toNat = jdx.toNat + 1 := by
                    rw [BitVec.toNat_add]
                    have hj_u64 : jdx.toNat + 1 < 2 ^ 64 := by omega
                    simp [Nat.mod_eq_of_lt hj_u64]
                  have hcv2 : s2.core.cur_vars = s1.core.cur_vars := by rw [hcore2, hcore1]
                  have hcv1 : s1.core.cur_vars = s.core.cur_vars := by rw [hcore1]
                  have hcv2_le : s2.core.cur_vars ≤ c.max_vars := hlen2.core_ok.cur_vars_le
                  have hlvl2_len : s2.core.lvl.length = c.max_vars := hlen2.core_ok.lvl_len
                  have hmrk2_len : s2.core.mrk.length = c.max_vars := hlen2.core_ok.mrk_len
                  have hws1_len2 : s2.scratch.work_stk1.length = 2 * c.max_vars :=
                    hlen2.scratch_ok.work_stk1_len
                  clear hc
                  c0_hsteps_nogrp
                  refine wp_join_state1 (t := i64)
                      (fun st : FullState × Nat => BitVec.ofNat 64 st.2) JInv ?_ ?_
                  · intro _Jc2 ⟨s3, mcl3⟩ m3 ⟨hlen3, hcov3, hcore3, hpres3, hws23, hm3⟩
                    dsimp only at *
                    c0_hsteps
                    apply ih2 (s3, mcl3, jdx + 1#64) m3
                    · rw [hj_add1]; omega
                    · exact ⟨hlen3, hcov3, hcore3, hpres3, hws23, by rw [hj_add1]; omega, hm3⟩
                  · intro Jc2 hJc2
                    c0_hsteps_nogrp
                    · rename_i hc1 hc2 hc3
                      have hcv0_64 : s.core.cur_vars < 2 ^ 64 := by
                        have := fullInv_max_vars_lt32 c; rw [← hcv1, ← hcv2]; omega
                      have hget_tmp :
                          s2.core.tmp[jdx.toNat]?.getD 0#32 = s2.core.tmp[jdx.toNat] := by
                        simp [List.getElem?_eq_getElem hj_len]
                      have hshift : (s2.core.tmp[jdx.toNat] >>> 1#32).toNat =
                          s2.core.tmp[jdx.toNat].toNat / 2 := by
                        simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
                      have hv : (s2.core.tmp[jdx.toNat]?.getD 0#32 >>> 1#32).toNat <
                          s2.core.cur_vars := by
                        rw [hget_tmp, hshift, hcv2, hcv1, ← Nat.mod_eq_of_lt hcv0_64]; exact hc1
                      have hmrk_lt : s2.core.tmp[jdx.toNat].toNat / 2 < s2.core.mrk.length := by
                        rw [hmrk2_len, ← hshift, ← hget_tmp]; exact Nat.lt_of_lt_of_le hv hcv2_le
                      have hm_eq :
                          s2.core.mrk[(s2.core.tmp[jdx.toNat]?.getD 0#32 >>> 1#32).toNat]?.getD
                          0#8 = 0#8 := by
                        rw [hget_tmp, hshift, List.getElem?_eq_getElem hmrk_lt, Option.getD_some]
                        exact mrk_zext32_eq0 hc3
                      have hp := restore_push_step hlen2 hcov2 hcore2 hpres2 hws22 hv hm_eq
                      have hmcl_lt : mcl2 < 2 * c.max_vars := by
                        have h1 : mcl2 + 1 ≤ s2.core.cur_vars := hp.2.1.1
                        omega
                      have hmcl_ws1 : mcl2 < s2.scratch.work_stk1.length := by
                        have h1 : mcl2 + 1 ≤ s2.core.cur_vars := hp.2.1.1
                        rw [hws1_len2]; omega
                      have hmcl64 : mcl2 < 2 ^ 64 := by
                        have := fullInv_max_vars_lt32 c; omega
                      c0_hsteps
                      rw [show (BitVec.ofNat 64 mcl2 + 1 : BitVec 64) = BitVec.ofNat 64 (mcl2 + 1)
                        from (BitVec.ofNat_add mcl2 1).symm]
                      have hmcl_nat : (BitVec.ofNat 64 mcl2).toNat = mcl2 := by
                        simp [Nat.mod_eq_of_lt hmcl64]
                      have hv_lt64 : (s2.core.tmp[jdx.toNat] >>> OfNat.ofNat 1).toNat < 2 ^ 64 :=
                        Nat.lt_trans (BitVec.isLt _) (by omega)
                      have hv_bw : (BitVec.setWidth 64
                          (s2.core.tmp[jdx.toNat] >>> OfNat.ofNat 1)).toNat =
                          (s2.core.tmp[jdx.toNat]?.getD 0#32 >>> 1#32).toNat := by
                        rw [hget_tmp, BitVec.toNat_setWidth, Nat.mod_eq_of_lt hv_lt64]; rfl
                      have hv_w32 : BitVec.ofNat 32
                          (s2.core.tmp[jdx.toNat]?.getD 0#32 >>> 1#32).toNat =
                          (s2.core.tmp[jdx.toNat] >>> OfNat.ofNat 1) := by
                        apply BitVec.eq_of_toNat_eq
                        have h32 : (s2.core.tmp[jdx.toNat] >>> OfNat.ofNat 1).toNat < 2 ^ 32 :=
                          BitVec.isLt _
                        rw [hget_tmp, show (1#32 : BitVec 32) = OfNat.ofNat 1 from rfl,
                          BitVec.toNat_ofNat]
                        exact Nat.mod_eq_of_lt h32
                      rw [hmcl_nat, hv_bw, show (BitVec.ofNat 8 1 : BitVec 8) = 1#8 from rfl] at hm
                      exact hJc2 (_, mcl2 + 1) _ ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2,
                        by simpa only [hv_w32] using hm⟩
                    · exact hJc2 (s2, mcl2) m2 ⟨hlen2, hcov2, hcore2, hpres2, hws22, hm2⟩
                    · exact hJc2 (s2, mcl2) m2 ⟨hlen2, hcov2, hcore2, hpres2, hws22, hm2⟩
                    · exact hJc2 (s2, mcl2) m2 ⟨hlen2, hcov2, hcore2, hpres2, hws22, hm2⟩
                    · exact hJc2 (s2, mcl2) m2 ⟨hlen2, hcov2, hcore2, hpres2, hws22, hm2⟩
                · exact hJp (s2, mcl2) m2 ⟨hlen2, hcov2, hcore2, hpres2, hws22, hm2⟩
            · exact hJp (s1, mcl1) m1 ⟨hlen1, hcov1, hcore1, hpres1, hws21, hm1⟩
    · intro J hJ
      c0_hsteps
      · exact hJ (BitVec.ofNat 64 s.core.cur_vars) m ⟨by
          have hcv64 : s.core.cur_vars < 2 ^ 64 := by
            have := fullInv_max_vars_lt32 c; have := hlen.core_ok.cur_vars_le; omega
          simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcv64], rfl⟩
      · exact hJ s.scratch.res_sz m ⟨by
          have hcv64 : s.core.cur_vars < 2 ^ 64 := by
            have := fullInv_max_vars_lt32 c; have := hlen.core_ok.cur_vars_le; omega
          have hlt : ¬ s.core.cur_vars < s.scratch.res_sz.toNat := by
            simpa [Nat.mod_eq_of_lt hcv64] using hc
          omega, rfl⟩

end

end LeanQbe.T.Examples.Kissat.Proof.Analyze.WpRestore
