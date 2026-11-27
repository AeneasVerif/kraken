/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S4EVSIDSReorderProof1
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Fidelity Step 13 S4-A Proofs — `full_restore_bump_ana_mode_fid`

UNSAT-only, callee-parametric `Func.wp` proof (`public section`, `0` `@[expose]` on theorems,
`0` `import all`, `XPost`-polymorphic) for `full_restore_bump_ana_mode_fid`
(`s13RestoreBumpAnaModeSpecP M6ExtW2bPres`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S4

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6ProofUtil
open LeanQbe.T.Examples.Kissat.FullM6MinShrink
open LeanQbe.T.Examples.Kissat.FullM6OrchAdapters
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.FullM6Hdr.M6HdrTactics
open Kraken.Bedrock2.Test

section RestoreHelpers

attribute [local bv_c0] Bool.true_eq_false Bool.false_eq_true

private theorem s13r_bv32_lshr1 (x : BitVec 32) : (x >>> 1#32).toNat = x.toNat / 2 :=
  fl_bv32_lshr1 x

private theorem s13r_bv32_setWidth64 (x : BitVec 32) : (x.setWidth 64).toNat = x.toNat :=
  fl_bv32_setWidth64 x

private theorem s13r_bv32_lshr_nat1 (x : BitVec 32) : (x >>> 1).toNat = x.toNat / 2 :=
  fl_bv32_lshr1 x

attribute [local bv_c0] s13r_bv32_lshr1 s13r_bv32_setWidth64 s13r_bv32_lshr_nat1

private theorem s13r_bv8_zext32_eq0_iff {x : BitVec 8} :
    BitVec.setWidth 32 x = 0#32 ↔ x = 0#8 := by
  constructor
  · intro h
    have ht := congrArg BitVec.toNat h
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega : x.toNat < 2 ^ 32),
      show (0#32 : BitVec 32).toNat = 0 from rfl] at ht
    exact BitVec.eq_of_toNat_eq ht
  · rintro rfl; rfl

private abbrev mkRestoreState (s : FullState) (mrk : List (BitVec 8)) (mcl : Nat)
    (ws1 : List (BitVec 32)) : FullState :=
  { s with
    core := { s.core with mrk := mrk, min_clr_len := mcl }
    scratch := { s.scratch with work_stk1 := ws1 } }

private theorem mkRestoreState_lengths {c : FullCfg} {s : FullState} (hlen : s.LengthsOk c)
    {mrk : List (BitVec 8)} {mcl : Nat} {ws1 : List (BitVec 32)}
    (hmrk : mrk.length = c.max_vars) (hws1 : ws1.length = 2 * c.max_vars)
    (hmcl : mcl ≤ c.max_vars) :
    (mkRestoreState s mrk mcl ws1).LengthsOk c :=
  ⟨{ hlen.core_ok with mrk_len := hmrk, min_clr_len_le := hmcl },
   { hlen.scratch_ok with work_stk1_len := hws1 }⟩

private theorem s13r_zero_marksCov {c : FullCfg} {s : FullState} {ws1 : List (BitVec 32)}
    (hmrk0 : ∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 = 0#8) :
    FullAnaMarksCov c (mkRestoreState s s.core.mrk 0 ws1) :=
  ⟨Nat.zero_le _, by simp, fun _ hk => by dsimp only [mkRestoreState] at hk; omega,
    fun v hv hnz => absurd (hmrk0 v hv) hnz⟩

end RestoreHelpers

local macro "m6h_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

local macro "c0_hcall " h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

private abbrev RestoreSt := List (BitVec 8) × Nat × List (BitVec 32)

/-- Step-13 `full_restore_bump_ana_mode_fid` satisfies `s13RestoreBumpAnaModeSpecP M6ExtW2bPres`. -/
theorem full_restore_bump_ana_mode_fid_step13_wp (Γ : Env)
    (hBumpAna : ∀ a m Q X, s13BumpAnalyzedModeSpecP M6ExtW2bPres a m Q X →
      Γ "full_bump_analyzed_mode_fid" [i64, .bool] [] a m Q X)
    (hClearAna : ∀ a m Q X, Full.fullClearAnaSpec a m Q X →
      Γ "full_clear_ana" [i64] [] a m Q X) :
    ∀ a m Q X, s13RestoreBumpAnaModeSpecP M6ExtW2bPres a m Q X →
      Func.wp Γ full_restore_bump_ana_mode_fid_body a m Q X := by
  rintro ⟨h, allow, ⟨⟩⟩ m Q X hs
  obtain ⟨c, ext, s, R, rfl, hcfg, hext, hlen, hmrk0, hm, hQ⟩ := s13RestoreBumpAnaModeSpecP_elim hs
  have hmaxv := c.hmaxv; unfold LratBytes.dimacsBound at hmaxv
  have hco := hlen.core_ok; have hso := hlen.scratch_ok
  have hcv_le := hco.cur_vars_le; have hmrk0_len := hco.mrk_len; have hws10_len := hso.work_stk1_len
  unfold Func.wp full_restore_bump_ana_mode_fid_body
  rw [fullM6HdrMem_iff] at hm
  c0_hsteps_nogrp
  · exact hQ s.core.mrk s.core.min_clr_len s.core.repr s.scratch ext m hlen hmrk0
      (fun hp => absurd hp (by assumption)) (fun _ => rfl) ⟨rfl, rfl⟩ rfl hext
      (fun hi => ⟨hi, M6ExtW2bPres.refl ext⟩) ((fullM6HdrMem_iff ..).mpr hm)
  · have hprob0 : s.core.probing = 0#64 := by assumption
    let R_hdr : Mem 64 → Prop := array64 (c.hdr - 2304) ext ⋆ R
    have hcv_lt64 : s.core.cur_vars < 2 ^ 64 := by omega
    c0_hsteps_nogrp
    refine wp_join_state1 (t := i64) (α := Nat) (proj := BitVec.ofNat 64)
      (Inv := fun ana_n m1 => ana_n ≤ s.core.cur_vars ∧ m1 = m)
      (fun Ja ana_n m1 ⟨hana_le, hm1⟩ => ?_) (fun Ja hJa => ?_)
    · rcases hm1.symm with rfl; rw [Blocks.get_here]; dsimp only
      c0_hsteps_nogrp
      refine wp_while_state (ts := [i64, i64]) (α := Nat × Nat × RestoreSt)
        (proj := fun st => (BitVec.ofNat 64 st.2.1, BitVec.ofNat 64 st.1, ()))
        (μ := fun st => ana_n - st.1)
        (Inv := fun st mk =>
          st.2.1 ≤ st.1 ∧ st.1 ≤ ana_n ∧
          st.2.2.1.length = c.max_vars ∧ st.2.2.2.2.length = 2 * c.max_vars ∧
          FullAnaMarksCov c (mkRestoreState s st.2.2.1 st.2.1 st.2.2.2.2) ∧
          (FullMem c (mkRestoreState s st.2.2.1 s.core.min_clr_len st.2.2.2.2) ⋆ R_hdr) mk)
        (fun Jk hJk => by
          c0_hsteps
          exact hJk (0, 0, s.core.mrk, 0, s.scratch.work_stk1) m
            ⟨Nat.le_refl _, Nat.zero_le _, hmrk0_len, hws10_len, s13r_zero_marksCov hmrk0, hm⟩)
        (fun Jk (k, w, mrk_k, mcl_k, ws_k) mk ⟨hwk, hka, hmrk_k, hws_k, hcov_k, hmk⟩ ihk => ?_)
      dsimp only at hwk hka hmrk_k hws_k hcov_k hmk ihk; rw [Blocks.get_here]; dsimp only
      c0_hsteps_nogrp
      · have hk_lt : k < ana_n := by
          have hlt : k % 2 ^ 64 < ana_n % 2 ^ 64 := by
            simpa [BitVec.toNat_ofNat] using (by assumption : _)
          rwa [Nat.mod_eq_of_lt (by omega : k < 2 ^ 64),
            Nat.mod_eq_of_lt (by omega : ana_n < 2 ^ 64)] at hlt
        have hk_ws : k < ws_k.length := by rw [hws_k]; omega
        let av := ws_k[(BitVec.ofNat 64 k).toNat]'(by rw [bv64_ofNat_toNat (by omega)]; exact hk_ws)
        have hk1_bv : BitVec.ofNat 64 k + 1 = BitVec.ofNat 64 (k + 1) :=
          BitVec.eq_of_toNat_eq (by
            rw [show (1 : BitVec 64) = 1#64 from rfl,
              fl_bv64_add1_toNat (by rw [bv64_ofNat_toNat (by omega)]; omega),
              bv64_ofNat_toNat (by omega), bv64_ofNat_toNat (by omega)])
        c0_hsteps_nogrp
        refine wp_join_state (ts := [i64]) (α := Nat × RestoreSt)
          (proj := fun st => (BitVec.ofNat 64 st.1, ()))
          (Inv := fun st mk' =>
            st.1 ≤ k + 1 ∧ st.2.1.length = c.max_vars ∧ st.2.2.2.length = 2 * c.max_vars ∧
            FullAnaMarksCov c (mkRestoreState s st.2.1 st.1 st.2.2.2) ∧
            (FullMem c (mkRestoreState s st.2.1 s.core.min_clr_len st.2.2.2) ⋆ R_hdr) mk')
          (fun _ (w', mrk', mcl', ws') mk' ⟨hw', hmrk', hws', hcov', hmk'⟩ => by
            rw [Blocks.get_here]; dsimp only; c0_hsteps; rw [hk1_bv]
            exact ihk (k + 1, w', mrk', mcl', ws') mk' (by dsimp only; omega)
              ⟨hw', by omega, hmrk', hws', hcov', hmk'⟩)
          (fun Jks hJks => ?_)
        c0_hsteps_nogrp
        · have hav_cv : av.toNat < s.core.cur_vars := by dsimp only [av]; c0_bound
          have hw_cv : w < s.core.cur_vars := by omega
          have hmrk_z : mrk_k[av.toNat]?.getD 0#8 = 0#8 := by
            rw [List.getElem?_eq_getElem (by rw [hmrk_k]; omega), Option.getD_some]
            exact s13r_bv8_zext32_eq0_iff.mp (by simpa [av] using (by assumption : _))
          have hcov' := s13b_push_marksCov_gen hmrk_k hws_k hcv_le hcov_k hav_cv hw_cv hmrk_z
          have hw1_bv : (BitVec.ofNat 64 w + 1).toNat = w + 1 := by
            rw [show (1 : BitVec 64) = 1#64 from rfl,
              fl_bv64_add1_toNat (by rw [bv64_ofNat_toNat (by omega)]; omega),
              bv64_ofNat_toNat (by omega)]
          have hav_lt64 : (ws_k[k]'(by omega)).toNat < 2 ^ 64 := by
            have := (ws_k[k]'(by omega)).isLt; omega
          rw [show BitVec.ofNat 64 w + 1 = BitVec.ofNat 64 (w + 1) from
            BitVec.eq_of_toNat_eq (by rw [hw1_bv, bv64_ofNat_toNat (by omega)])]
          exact hJks (w + 1, mrk_k.set av.toNat 1#8, 0, ws_k.set w av) _
            ⟨by omega, by rw [List.length_set, hmrk_k], by rw [List.length_set, hws_k], hcov', by
              simpa [mkRestoreState, av, s13r_bv32_setWidth64,
                bv64_ofNat_toNat (by omega : w < 2 ^ 64),
                bv64_ofNat_toNat (by omega : k < 2 ^ 64),
                Nat.mod_eq_of_lt (by omega : w < 2 ^ 64),
                Nat.mod_eq_of_lt (by omega : k < 2 ^ 64),
                Nat.mod_eq_of_lt hav_lt64, show BitVec.ofNat 8 1 = 1#8 from rfl] using hm⟩
        · exact hJks (w, mrk_k, 0, ws_k) mk ⟨by omega, hmrk_k, hws_k, hcov_k, hmk⟩
        · exact hJks (w, mrk_k, 0, ws_k) mk ⟨by omega, hmrk_k, hws_k, hcov_k, hmk⟩
      · c0_hsteps_nogrp
        refine wp_join_state1 (t := i64) (α := Nat × RestoreSt)
          (proj := fun st => BitVec.ofNat 64 st.1)
          (Inv := fun st m2 =>
            st.1 ≤ s.core.cur_vars ∧ st.2.1.length = c.max_vars ∧ st.2.2.2.length = 2 * c.max_vars ∧
            FullAnaMarksCov c (mkRestoreState s st.2.1 st.1 st.2.2.2) ∧
            (FullMem c (mkRestoreState s st.2.1 s.core.min_clr_len st.2.2.2) ⋆ R_hdr) m2)
          (fun Jw (wf, mrkf, mclf, wsf) m2 ⟨hwf_le, hmrkf, hwsf, hcovf, hm2⟩ => ?_)
          (fun Jw hJw => ?_)
        · dsimp only at hwf_le hmrkf hwsf hcovf hm2; rw [Blocks.get_here]; dsimp only
          let s_pre := mkRestoreState s mrkf wf wsf
          have hlen_pre : s_pre.LengthsOk c := mkRestoreState_lengths hlen hmrkf hwsf (by omega)
          c0_hsteps_nogrp
          refine wp_join_group (ts := [])
            (fun () m_out => ∃ (mrk_o : List (BitVec 8)) (repr_o : List (BitVec 32))
              (sc_o : FullScratch) (ext_o : List (BitVec 64)),
              let s_o : FullState :=
                { core := { s.core with mrk := mrk_o, min_clr_len := 0, repr := repr_o }
                  scratch := sc_o }
              s_o.LengthsOk c ∧ (∀ v < c.max_vars, mrk_o[v]?.getD 0#8 = 0#8) ∧
              FullExtScratchPres s s_o ∧ sc_o.work_stk2 = s.scratch.work_stk2 ∧
              M6HdrExtOk ext_o ∧
              (M6HdrExtInitOk ext → M6HdrExtInitOk ext_o ∧ M6ExtW2bPres ext ext_o) ∧
              (FullM6HdrMem c ext_o s_o ⋆ R) m_out)
            (fun _ () m_out
                ⟨mrk_o, repr_o, sc_o, ext_o, hlo, hmo, hpo, hw2o, hext_o, hinit_o, hm_o⟩ => by
              rw [Blocks.get_here]; c0_hsteps
              exact hQ mrk_o 0 repr_o sc_o ext_o m_out hlo hmo (fun _ => rfl)
                (fun hp => absurd hprob0 hp) hpo hw2o hext_o hinit_o hm_o)
            (fun Jret hJret => ?_)
          c0_hsteps_nogrp
          · m6h_call hBumpAna
            refine s13BumpAnalyzedModeSpecP_of hcfg hext hlen_pre (s13BumpPre_of_cov allow hcovf)
              ((fullM6HdrMem_iff ..).mpr (by
                simpa [R_hdr, s_pre, mkRestoreState, bv64_ofNat_toNat (by omega : wf < 2 ^ 64),
                  Nat.mod_eq_of_lt (by omega : wf < 2 ^ 64)] using hm))
              fun mrk_b mcl_b repr_b sc_b ext' m_b hlen_b hcov_b _ _
                hpre_b hws2_b hext_b hinit_b hm_b => ?_
            rw [fullM6HdrMem_iff] at hm_b
            c0_hsteps_nogrp
            c0_hcall hClearAna
            let s_b : FullState :=
              { s_pre with
                core := { s_pre.core with mrk := mrk_b, min_clr_len := mcl_b, repr := repr_b }
                scratch := sc_b }
            refine ⟨c, s_b, array64 (c.hdr - 2304) ext' ⋆ R, rfl, hlen_b, hm_b,
              fun mrk' m' hmrk' _ _ hclr' hm' => ?_⟩
            have hmrk0' : ∀ v < c.max_vars, mrk'[v]?.getD 0#8 = 0#8 := hclr' (hcov_b hcovf)
            c0_hsteps
            exact hJret () m' ⟨mrk', repr_b, sc_b, ext',
              ⟨{ hlen_b.core_ok with mrk_len := hmrk', min_clr_len_le := Nat.zero_le _ },
               hlen_b.scratch_ok⟩,
              hmrk0', hpre_b, hws2_b, hext_b, hinit_b,
              (fullM6HdrMem_iff ..).mpr (by simpa [s_b, s_pre, mkRestoreState] using hm')⟩
          · have hwf0 : wf = 0 := by
              have h0 : ¬ (0 : Nat) < wf % 2 ^ 64 := hc
              rw [Nat.mod_eq_of_lt (by omega)] at h0; omega
            subst hwf0
            have hmrk0' : ∀ v < c.max_vars, mrkf[v]?.getD 0#8 = 0#8 := fun v hv => by
              if hnz : mrkf[v]?.getD 0#8 = 0#8 then exact hnz else
                exfalso; obtain ⟨i, hi, _⟩ := hcovf.2.2.2 v hv hnz
                dsimp only [mkRestoreState] at hi; omega
            have hm2' : (FullMem c (mkRestoreState s mrkf 0 wsf) ⋆ R_hdr) m := by
              simpa [mkRestoreState, show (BitVec.ofNat 64 0).toNat = 0 from rfl] using hm
            c0_hsteps
            exact hJret () m ⟨mrkf, s.core.repr, (mkRestoreState s mrkf 0 wsf).scratch, ext,
              mkRestoreState_lengths hlen hmrkf hwsf (Nat.zero_le _), hmrk0', ⟨rfl, rfl⟩, rfl,
              hext, fun hi => ⟨hi, M6ExtW2bPres.refl ext⟩, (fullM6HdrMem_iff ..).mpr hm2'⟩
        · c0_hsteps_nogrp
          · have htl_le : s.core.tmp_len ≤ s.core.cur_vars := by
              have htl64 : s.core.tmp_len < 2 ^ 64 := by have := hco.tmp_len_le; omega
              have hle : ¬ s.core.cur_vars % 2 ^ 64 < s.core.tmp_len % 2 ^ 64 := by
                simpa [mkRestoreState] using hc
              rw [Nat.mod_eq_of_lt hcv_lt64, Nat.mod_eq_of_lt htl64] at hle; omega
            refine wp_while_state (ts := [i64, i64]) (α := Nat × Nat × RestoreSt)
              (proj := fun st => (BitVec.ofNat 64 st.2.1, BitVec.ofNat 64 st.1, ()))
              (μ := fun st => s.core.tmp_len - st.1)
              (Inv := fun st mt =>
                st.1 ≤ s.core.tmp_len ∧ st.2.1 ≤ s.core.cur_vars ∧
                st.2.2.1.length = c.max_vars ∧ st.2.2.2.2.length = 2 * c.max_vars ∧
                FullAnaMarksCov c (mkRestoreState s st.2.2.1 st.2.1 st.2.2.2.2) ∧
                (FullMem c (mkRestoreState s st.2.2.1 s.core.min_clr_len st.2.2.2.2) ⋆ R_hdr) mt)
              (fun Jt hJt => by
                c0_hsteps; exact hJt (0, w, mrk_k, 0, ws_k) mk
                  ⟨Nat.zero_le _, by dsimp only; omega, hmrk_k, hws_k, hcov_k, hmk⟩)
              (fun Jt (ti, wt, mrk_t, mcl_t, ws_t) mt
                ⟨hti_le, hwt_le, hmrk_t, hws_t, hcov_t, hmt⟩ iht => ?_)
            dsimp only at hti_le hwt_le hmrk_t hws_t hcov_t hmt iht
            rw [Blocks.get_here]; dsimp only
            let st := mkRestoreState s mrk_t s.core.min_clr_len ws_t
            c0_hsteps_nogrp
            · have hti_lt : ti < s.core.tmp_len := by
                have htl64 : s.core.tmp_len < 2 ^ 64 := by omega
                have hlt : ti % 2 ^ 64 < s.core.tmp_len % 2 ^ 64 := by
                  simpa [BitVec.toNat_ofNat] using (by assumption : _)
                rwa [Nat.mod_eq_of_lt (by omega : ti < 2 ^ 64), Nat.mod_eq_of_lt htl64] at hlt
              have hti_tmp : ti < st.core.tmp.length := by
                rw [show st.core.tmp = s.core.tmp from rfl, hco.tmp_len_arr]; omega
              have hti_tmp_bv : (BitVec.ofNat 64 ti).toNat < st.core.tmp.length := by
                rw [bv64_ofNat_toNat (by omega)]; exact hti_tmp
              have hti1_bv : BitVec.ofNat 64 ti + 1 = BitVec.ofNat 64 (ti + 1) :=
                BitVec.eq_of_toNat_eq (by
                  rw [show (1 : BitVec 64) = 1#64 from rfl,
                    fl_bv64_add1_toNat (by rw [bv64_ofNat_toNat (by omega)]; omega),
                    bv64_ofNat_toNat (by omega), bv64_ofNat_toNat (by omega)])
              let tv := (st.core.tmp[(BitVec.ofNat 64 ti).toNat]'hti_tmp_bv) >>> 1#32
              c0_hsteps_nogrp
              refine wp_join_state (ts := [i64]) (α := Nat × RestoreSt)
                (proj := fun st => (BitVec.ofNat 64 st.1, ()))
                (Inv := fun st mt' =>
                  st.1 ≤ s.core.cur_vars ∧ st.2.1.length = c.max_vars ∧
                  st.2.2.2.length = 2 * c.max_vars ∧
                  FullAnaMarksCov c (mkRestoreState s st.2.1 st.1 st.2.2.2) ∧
                  (FullMem c (mkRestoreState s st.2.1 s.core.min_clr_len st.2.2.2) ⋆ R_hdr) mt')
                (fun _ (wt', mrk', mcl', ws') mt' ⟨hwt', hmrk', hws', hcov', hmt'⟩ => by
                  rw [Blocks.get_here]; dsimp only; c0_hsteps; rw [hti1_bv]
                  exact iht (ti + 1, wt', mrk', mcl', ws') mt' (by dsimp only; omega)
                    ⟨by omega, hwt', hmrk', hws', hcov', hmt'⟩)
                (fun Jts hJts => ?_)
              c0_hsteps_nogrp
              · have htv_cv : tv.toNat < s.core.cur_vars := by
                  dsimp only [tv, st, mkRestoreState]
                  simp only [bv64_ofNat_toNat (by omega : ti < 2 ^ 64),
                    Nat.mod_eq_of_lt (by omega : ti < 2 ^ 64), Nat.mod_eq_of_lt hcv_lt64] at *
                  c0_bound
                have htv_lvl : (tv.setWidth 64).toNat < st.core.lvl.length := by
                  rw [s13r_bv32_setWidth64, show st.core.lvl = s.core.lvl from rfl, hco.lvl_len]
                  omega
                have htv_mrk : (tv.setWidth 64).toNat < mrk_t.length := by
                  rw [s13r_bv32_setWidth64, hmrk_t]; omega
                c0_hsteps_nogrp
                · have hwt_cv : wt < s.core.cur_vars := by c0_bound
                  have hmrk_z : mrk_t[tv.toNat]?.getD 0#8 = 0#8 := by
                    rw [List.getElem?_eq_getElem (by rw [hmrk_t]; omega), Option.getD_some]
                    exact s13r_bv8_zext32_eq0_iff.mp (by simpa [tv] using (by assumption : _))
                  have hcov' :=
                    s13b_push_marksCov_gen hmrk_t hws_t hcv_le hcov_t htv_cv hwt_cv hmrk_z
                  have hwt1_bv : (BitVec.ofNat 64 wt + 1).toNat = wt + 1 := by
                    rw [show (1 : BitVec 64) = 1#64 from rfl,
                      fl_bv64_add1_toNat (by rw [bv64_ofNat_toNat (by omega)]; omega),
                      bv64_ofNat_toNat (by omega)]
                  have hwt_ws : (BitVec.ofNat 64 wt).toNat < ws_t.length := by
                    rw [bv64_ofNat_toNat (by omega), hws_t]; omega
                  have htmp_lt64 :
                      (s.core.tmp[ti]'(by rw [hco.tmp_len_arr]; omega)).toNat < 2 ^ 64 := by
                    have := (s.core.tmp[ti]'(by rw [hco.tmp_len_arr]; omega)).isLt; omega
                  c0_hsteps
                  rw [show BitVec.ofNat 64 wt + 1 = BitVec.ofNat 64 (wt + 1) from
                    BitVec.eq_of_toNat_eq (by rw [hwt1_bv, bv64_ofNat_toNat (by omega)])]
                  exact hJts (wt + 1, mrk_t.set tv.toNat 1#8, 0, ws_t.set wt tv) _
                    ⟨by omega, by rw [List.length_set, hmrk_t], by rw [List.length_set, hws_t],
                     hcov', by
                      simpa [st, mkRestoreState, tv, s13r_bv32_setWidth64, s13r_bv32_lshr_nat1,
                        bv64_ofNat_toNat (by omega : wt < 2 ^ 64),
                        bv64_ofNat_toNat (by omega : ti < 2 ^ 64),
                        Nat.mod_eq_of_lt (by omega : wt < 2 ^ 64),
                        Nat.mod_eq_of_lt (by omega : ti < 2 ^ 64),
                        Nat.mod_eq_of_lt htmp_lt64, show BitVec.ofNat 8 1 = 1#8 from rfl] using hm⟩
                · exact hJts (wt, mrk_t, 0, ws_t) mt ⟨hwt_le, hmrk_t, hws_t, hcov_t, hmt⟩
                · exact hJts (wt, mrk_t, 0, ws_t) mt ⟨hwt_le, hmrk_t, hws_t, hcov_t, hmt⟩
                · exact hJts (wt, mrk_t, 0, ws_t) mt ⟨hwt_le, hmrk_t, hws_t, hcov_t, hmt⟩
              · exact hJts (wt, mrk_t, 0, ws_t) mt ⟨hwt_le, hmrk_t, hws_t, hcov_t, hmt⟩
            · exact hJw (wt, mrk_t, 0, ws_t) mt ⟨hwt_le, hmrk_t, hws_t, hcov_t, hmt⟩
          · exact hJw (w, mrk_k, 0, ws_k) mk ⟨by omega, hmrk_k, hws_k, hcov_k, hmk⟩
    · c0_hsteps
      · exact hJa s.core.cur_vars m ⟨Nat.le_refl _, rfl⟩
      · have hle : s.scratch.res_sz.toNat ≤ s.core.cur_vars := by
          have hng : ¬ s.core.cur_vars % 2 ^ 64 < s.scratch.res_sz.toNat := by assumption
          rw [Nat.mod_eq_of_lt hcv_lt64] at hng; omega
        have hres_bv : BitVec.ofNat 64 s.scratch.res_sz.toNat = s.scratch.res_sz :=
          BitVec.eq_of_toNat_eq (bv64_ofNat_toNat (by omega))
        simpa [hres_bv] using hJa s.scratch.res_sz.toNat m ⟨hle, rfl⟩

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S4
