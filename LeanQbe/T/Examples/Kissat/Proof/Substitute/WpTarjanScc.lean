/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Substitute.WpTarjanScc0
public import LeanQbe.T.Examples.Kissat.Src.Substitute

/-!
# WP Proof for `full_tarjan_scc` (`Proof.Substitute.WpTarjanScc`)

Proves `full_tarjan_scc_fast_wp` and `full_tarjan_scc_wp` parametrically over `Γ : Env`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Substitute

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Substitute
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Substitute.Spec
open scoped Proof.Spec.FullArenaTactics SubstArenaTactics SubstSccTactics
open Kraken.Bedrock2.Test

public section

/-- Local upgraded `full_tarjan_scc` spec preserving `TmkZero` on exit. -/
private def fullTarjanSccFastSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInvW c F0 F_cur s ∧ s.core.cur_level = 0 ∧ (FullMem c s ⋆ R) m ∧
    ∀ r repr' tc' inc' tmk' trc' ws1' ws2' wsort' sstk' rsz' m',
      let s' : FullState :=
        { s with
          core := { s.core with repr := repr', tmp_cnt := tc', inconsistent := inc' }
          scratch := { s.scratch with tarjan_mark := tmk', tarjan_reach := trc',
                                      work_stk1 := ws1', work_stk2 := ws2', wsort := wsort',
                                      shrink_stk := sstk', res_sz := rsz' } }
      FullSparseInvW c F0 F_cur s' → r.toNat ≤ c.max_vars →
      (∀ k < r.toNat,
        (sstk'[k]?.getD 0#32).toNat < 2 * s.core.cur_vars ∧
        (cnfOfClauses F_cur).EntailsClause (cnfClause [(sstk'[k]?.getD 0#32).toNat])) →
      (inc' = 0#64 → FullReprEquiv F_cur s') →
      (∀ l < 2 * s.core.cur_vars,
        tmk'[l]?.getD 0#32 = 0#32 ∧ trc'[l]?.getD 0#32 = 0#32) →
      TmkZero s' → (FullMem c s' ⋆ R) m' → Q (r, ()) m'

private theorem fullTarjanSccFastSpec_of_canon {a m Q X}
    (h : Spec.fullTarjanSccSpec a m Q X) : fullTarjanSccFastSpec a m Q X := by
  rcases a with ⟨h_ptr, ⟨⟩⟩; rcases h with ⟨c, F0, F_cur, s, R, rfl, hsp, hcl0, hm, hQ⟩
  exact ⟨c, F0, F_cur, s, R, rfl, hsp, hcl0, hm,
    fun r repr' tc' inc' tmk' trc' ws1' ws2' wsort' sstk' rsz' m' h1 h2 h3 h4 _ _ hm' =>
      hQ r repr' tc' inc' tmk' trc' ws1' ws2' wsort' sstk' rsz' m' h1 h2 h3 h4 hm'⟩

private abbrev TarjanInitInv (c : FullCfg) (s0 : FullState) (i : Nat)
    (R : Mem 64 → Prop) (ml : Mem 64) : Prop :=
  ∃ st : FullState, AgreesExcept tarjanSccMask s0 st ∧ st.LengthsOk c ∧
    st.core.inconsistent = s0.core.inconsistent ∧ i ≤ 2 * s0.core.cur_vars ∧
    (∀ l < i, st.core.repr[l]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 ∧
      (st.scratch.tarjan_mark[l]?.getD 0#32).toNat = 0 ∧
      (st.scratch.tarjan_reach[l]?.getD 0#32).toNat = 0) ∧ (FullMem c st ⋆ R) ml

private abbrev TarjanOuterInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s0 : FullState) (reached root : Nat) (R : Mem 64 → Prop) (ml : Mem 64) : Prop :=
  ∃ st : FullState, root ≤ 2 * s0.core.cur_vars ∧ TarjanLoopBase c F_cur s0 st ∧
    (st.core.inconsistent = 0#64 → st.core.tmp_cnt = 0 ∧
      M6TarjanDfsInv c F0 F_cur s0 0 1 reached 0 st) ∧ (FullMem c st ⋆ R) ml

private abbrev TarjanFillInv (c : FullCfg) (F_cur : List (List Nat))
    (s0 stf : FullState) (idx : Nat) (R : Mem 64 → Prop) (mk : Mem 64) : Prop :=
  ∃ st4 : FullState, AgreesExcept tarjanSccMask s0 st4 ∧ st4.LengthsOk c ∧
    st4.core.inconsistent = stf.core.inconsistent ∧ st4.scratch.res_sz = stf.scratch.res_sz ∧
    st4.scratch.shrink_stk = stf.scratch.shrink_stk ∧ idx ≤ 2 * s0.core.cur_vars ∧
    FullPartialReprInv F_cur st4.core ∧
    (∀ l < idx, st4.core.repr[l]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 ∧
      st4.scratch.tarjan_mark[l]?.getD 0#32 = 0#32 ∧
      st4.scratch.tarjan_reach[l]?.getD 0#32 = 0#32) ∧ (FullMem c st4 ⋆ R) mk

private abbrev TarjanFillSetPred (c : FullCfg) (F_cur : List (List Nat))
    (s0 stf st4 st5 : FullState) (idx : Nat) (R : Mem 64 → Prop) (m4a : Mem 64) : Prop :=
  AgreesExcept tarjanSccMask s0 st5 ∧ st5.LengthsOk c ∧
  st5.core.inconsistent = stf.core.inconsistent ∧ st5.scratch.res_sz = stf.scratch.res_sz ∧
  st5.scratch.shrink_stk = stf.scratch.shrink_stk ∧
  st5.scratch.tarjan_mark = st4.scratch.tarjan_mark ∧
  st5.scratch.tarjan_reach = st4.scratch.tarjan_reach ∧ FullPartialReprInv F_cur st5.core ∧
  st5.core.repr[idx]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 ∧
  (∀ l < idx, st5.core.repr[l]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32) ∧ (FullMem c st5 ⋆ R) m4a

private abbrev TarjanDfsPred (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s0 : FullState) (root reached : Nat) (rch : BitVec 32) (dsp : BitVec 64)
    (n : Nat) (R : Mem 64 → Prop) (m3 : Mem 64) : Prop :=
  ∃ st3 : FullState, TarjanLoopBase c F_cur s0 st3 ∧
    (st3.core.inconsistent = 0#64 → n = M6TarjanDfsInv.measure c s0 st3 rch.toNat dsp.toNat ∧
      M6TarjanDfsInv c F0 F_cur s0 root (reached + 1) rch.toNat dsp.toNat st3 ∧
      (dsp.toNat = 0 → st3.core.tmp_cnt = 0)) ∧ (FullMem c st3 ⋆ R) m3

private abbrev TarjanNbPred (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s0 st3 : FullState) (root : BitVec 64) (reached rch : BitVec 32) (dsp : Nat)
    (rch' : BitVec 32) (dsp' : BitVec 64) (R : Mem 64 → Prop) (mj : Mem 64) : Prop :=
  ∃ st4 : FullState, 0 < dsp'.toNat ∧
    M6TarjanDfsInv c F0 F_cur s0 root.toNat (reached.toNat + 1) rch'.toNat dsp'.toNat st4 ∧
    M6TarjanDfsInv.measure c s0 st4 rch'.toNat dsp'.toNat <
      M6TarjanDfsInv.measure c s0 st3 rch.toNat dsp ∧ (FullMem c st4 ⋆ R) mj

private abbrev TarjanPopPred (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s0 st3 : FullState) (root reached rch dsp : Nat)
    (R : Mem 64 → Prop) (mj : Mem 64) : Prop :=
  ∃ st4 : FullState, TarjanLoopBase c F_cur s0 st4 ∧ (st4.core.inconsistent = 0#64 →
    M6TarjanDfsInv c F0 F_cur s0 root (reached + 1) rch (dsp - 1) st4 ∧
    M6TarjanDfsInv.measure c s0 st4 rch (dsp - 1) <
      M6TarjanDfsInv.measure c s0 st3 rch dsp ∧
    (dsp - 1 = 0 → st4.core.tmp_cnt = 0)) ∧ (FullMem c st4 ⋆ R) mj

private theorem tarjan_getElem_lit_eq {xs : List (BitVec 32)} {w lit : BitVec 32}
    {hi : w.toNat < xs.length} (hw : w = lit) (hlit : lit.toNat < xs.length) :
    xs[w.toNat]'hi = xs[lit.toNat]?.getD 0#32 := by
  subst hw; rw [List.getElem?_eq_getElem hlit, Option.getD_some]

private theorem tarjan_getElem_par_eq {xs : List (BitVec 32)} {w par : BitVec 32}
    {hi : w.toNat < xs.length} (hw : w = par)
    (hpar : (BitVec.setWidth 64 par).toNat < xs.length)
    (hz : (BitVec.setWidth 64 par).toNat = par.toNat) :
    xs[w.toNat]'hi = xs[(BitVec.setWidth 64 par).toNat]'hpar :=
  getElem_congr_idx hi hpar ((congrArg BitVec.toNat hw).trans hz.symm)

private theorem tarjan_wstk_hc_val {ws2 wsrt wvec wstk : List (BitVec 32)}
    {dsp : Nat} {off32 pos32 w0 : BitVec 32}
    {h0 : (2 ^ 64 - 1 + dsp) % 2 ^ 64 < ws2.length}
    {h1 : (2 * ((ws2[(2 ^ 64 - 1 + dsp) % 2 ^ 64]'h0).toNat ^^^ 1)) % 2 ^ 64 < wvec.length}
    {h2 : (2 ^ 64 - 1 + dsp) % 2 ^ 64 < wsrt.length}
    {h3 : ((wvec[(2 * ((ws2[(2 ^ 64 - 1 + dsp) % 2 ^ 64]'h0).toNat ^^^ 1)) % 2 ^ 64]'h1).toNat +
      (wsrt[(2 ^ 64 - 1 + dsp) % 2 ^ 64]'h2).toNat) % 2 ^ 64 < wstk.length}
    (hoff : wvec[(2 * ((ws2[(2 ^ 64 - 1 + dsp) % 2 ^ 64]'h0).toNat ^^^ 1)) % 2 ^ 64]'h1 = off32)
    (hpos : wsrt[(2 ^ 64 - 1 + dsp) % 2 ^ 64]'h2 = pos32)
    (hw0 : wstk[(off32.toNat + pos32.toNat) % 2 ^ 64]'(by rw [← hoff, ← hpos]; exact h3) = w0) :
    wstk[((wvec[(2 * ((ws2[(2 ^ 64 - 1 + dsp) % 2 ^ 64]'h0).toNat ^^^ 1)) % 2 ^ 64]'h1).toNat +
      (wsrt[(2 ^ 64 - 1 + dsp) % 2 ^ 64]'h2).toNat) % 2 ^ 64]'h3 = w0 := by
  have hi : ((wvec[(2 * ((ws2[(2 ^ 64 - 1 + dsp) % 2 ^ 64]'h0).toNat ^^^ 1)) %
        2 ^ 64]'h1).toNat + (wsrt[(2 ^ 64 - 1 + dsp) % 2 ^ 64]'h2).toNat) % 2 ^ 64 =
      (off32.toNat + pos32.toNat) % 2 ^ 64 := by rw [hoff, hpos]
  exact (getElem_congr_idx h3 (by rw [← hi]; exact h3) hi).trans hw0

private theorem tarjan_arr_hc_val {xs ws2 wsrt wvec wstk : List (BitVec 32)}
    (f : BitVec 32 → Nat) {dsp : Nat} {off32 pos32 w0 : BitVec 32}
    {h0 : (2 ^ 64 - 1 + dsp) % 2 ^ 64 < ws2.length}
    {h1 : (2 * ((ws2[(2 ^ 64 - 1 + dsp) % 2 ^ 64]'h0).toNat ^^^ 1)) % 2 ^ 64 < wvec.length}
    {h2 : (2 ^ 64 - 1 + dsp) % 2 ^ 64 < wsrt.length}
    {h3 : ((wvec[(2 * ((ws2[(2 ^ 64 - 1 + dsp) % 2 ^ 64]'h0).toNat ^^^ 1)) % 2 ^ 64]'h1).toNat +
      (wsrt[(2 ^ 64 - 1 + dsp) % 2 ^ 64]'h2).toNat) % 2 ^ 64 < wstk.length}
    {h4 : f (wstk[((wvec[(2 * ((ws2[(2 ^ 64 - 1 + dsp) % 2 ^ 64]'h0).toNat ^^^ 1)) %
        2 ^ 64]'h1).toNat + (wsrt[(2 ^ 64 - 1 + dsp) % 2 ^ 64]'h2).toNat) % 2 ^ 64]'h3) <
      xs.length}
    (hoff : wvec[(2 * ((ws2[(2 ^ 64 - 1 + dsp) % 2 ^ 64]'h0).toNat ^^^ 1)) % 2 ^ 64]'h1 = off32)
    (hpos : wsrt[(2 ^ 64 - 1 + dsp) % 2 ^ 64]'h2 = pos32)
    (hw0 : wstk[(off32.toNat + pos32.toNat) % 2 ^ 64]'(by rw [← hoff, ← hpos]; exact h3) = w0)
    (hf : f w0 < xs.length) :
    xs[f (wstk[((wvec[(2 * ((ws2[(2 ^ 64 - 1 + dsp) % 2 ^ 64]'h0).toNat ^^^ 1)) %
        2 ^ 64]'h1).toNat + (wsrt[(2 ^ 64 - 1 + dsp) % 2 ^ 64]'h2).toNat) % 2 ^ 64]'h3)]'h4 =
      xs[f w0]'hf :=
  getElem_congr_idx h4 hf (congrArg f (tarjan_wstk_hc_val hoff hpos hw0))

/-- `full_tarjan_scc` satisfies `fullTarjanSccFastSpec` parametrically in `Γ`. -/
private theorem full_tarjan_scc_fast_wp (Γ : Env)
    (hPop : Γ.Has "full_tarjan_pop_scc" Spec.fullTarjanPopSccSpec) :
    ∀ args m Q X, fullTarjanSccFastSpec args m Q X →
      Func.wp Γ full_tarjan_scc_body args m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s0, R, rfl, hsp0, _, hm0, hQ⟩
  have hmx := c.hmaxv; have hwc := c.hwcap; unfold dimacsBound at hmx hwc
  have hlen0 := hsp0.1; have hw0 := hsp0.2.1; have hdm0 := hsp0.2.2.2.2.2
  have hcv_le := hlen0.core_ok.cur_vars_le
  have hwat0 : WatchesInv F_cur s0.core := by
    have hmw := hw0.watches; unfold ModeWatchesInv at hmw; rwa [ite_eq_left hdm0] at hmw
  have hnl_eq := tarjan_bv64_nl_eq hcv_le hmx
  unfold Func.wp full_tarjan_scc_body; c0_hsteps_nogrp
  refine wp_loop_inv (fun (i, ()) ml => TarjanInitInv c s0 i.toNat R ml)
    (fun (i, ()) _ => 2 * s0.core.cur_vars - i.toNat) ?_ ?_
  · intro J hJ; c0_hsteps
    exact hJ (0#64, ()) m ⟨s0, AgreesExcept.refl _ _, hlen0, rfl, Nat.zero_le _,
      fun _ h => by simp at h, hm0⟩
  rintro J ⟨i, ⟨⟩⟩ ml ⟨st, hag, hlen, hinc_st, hi_le, hinit, hml⟩ hJ
  have hrp_l := hlen.core_ok.repr_len; have htmk_l := hlen.scratch_ok.tarjan_mark_len
  have htrc_l := hlen.scratch_ok.tarjan_reach_len
  c0_hsplit
  · have hi_lt := tarjan_u64_lt_2cv hcv_le hmx hc
    have hi1 : (i + 1#64).toNat = i.toNat + 1 := bv64_add1_toNat (by omega)
    c0_hsteps
    obtain ⟨hag1, hlen1, hinc1, hinit1⟩ := m6_tarjan_init_step hag hlen hinc_st hi_lt hinit
    exact hJ (i + 1#64, ()) _ (by dsimp only; omega)
      ⟨_, hag1, hlen1, hinc1, by omega, by rw [hi1]; exact hinit1, by assumption⟩
  have hi_eq := tarjan_u64_eq_2cv hcv_le hmx hi_le hc; c0_hsteps_nogrp
  refine wp_loop_inv (fun (reached, root, ()) ml =>
      TarjanOuterInv c F0 F_cur s0 reached.toNat root.toNat R ml)
    (fun (_, root, ()) _ => 2 * s0.core.cur_vars - root.toNat) ?_ ?_
  · intro J2 hJ2; c0_hsteps
    have he := m6_tarjan_empty_dfs_inv hsp0 hag hlen hinc_st (fun l hl => hinit l (by omega))
    exact hJ2 (0#32, 0#64, ()) _ ⟨_, Nat.zero_le _, he.1, he.2, by assumption⟩
  rintro J2 ⟨reached, root, ⟨⟩⟩ ml ⟨st, hrt_le, hbase, hinc_dfs, hml⟩ hJ2
  clear hm0 hJ hinit hi_le hi_eq hinc_st hrp_l htmk_l htrc_l hag hlen
  obtain ⟨hag, hlen, hrsz, hpr, hus, hinc_u⟩ := hbase
  have hfl_l := hlen.core_ok.flags_len; have htmk_l := hlen.scratch_ok.tarjan_mark_len
  have htrc_l := hlen.scratch_ok.tarjan_reach_len; have hscc_l := hlen.scratch_ok.work_stk1_len
  have hdv_l := hlen.scratch_ok.work_stk2_len; have hdp_l := hlen.scratch_ok.wsort_len
  c0_hsteps_nogrp
  refine wp_join_group (ts := [])
    (fun () mj => ∃ st' : FullState, TarjanLoopBase c F_cur s0 st' ∧ (FullMem c st' ⋆ R) mj) ?_ ?_
  · rintro _ ⟨⟩ mj ⟨stf, ⟨hagf, hlenf, hrszf, hprf, husf, hincf⟩, hmj⟩; c0_hsteps_nogrp
    refine wp_loop_inv (fun (idx, ()) mk => TarjanFillInv c F_cur s0 stf idx.toNat R mk)
      (fun (idx, ()) _ => 2 * s0.core.cur_vars - idx.toNat) ?_ ?_
    · intro J4 hJ4; c0_hsteps
      exact hJ4 (0#64, ()) mj ⟨stf, hagf, hlenf, rfl, rfl, rfl, Nat.zero_le _, hprf,
        fun _ h => by simp at h, hmj⟩
    rintro J4 ⟨idx, ⟨⟩⟩ mk ⟨st4, hag4, hlen4, hinc4, hrsz4, hsh4, hidx_le, hpr4, hfill4, hmk⟩ hJ4
    have hrp4 := hlen4.core_ok.repr_len; have hcv4 := hag4.get (·.core.cur_vars)
    have htmk4 := hlen4.scratch_ok.tarjan_mark_len; have htrc4 := hlen4.scratch_ok.tarjan_reach_len
    c0_hsplit
    · have hidx_lt := tarjan_u64_lt_2cv hcv_le hmx hc
      have hidx1 : (idx + 1#64).toNat = idx.toNat + 1 := bv64_add1_toNat (by omega)
      c0_hsteps_nogrp
      refine wp_join_group (ts := [])
        (fun () m4a => ∃ st5, TarjanFillSetPred c F_cur s0 stf st4 st5 idx.toNat R m4a) ?_ ?_
      · rintro _ ⟨⟩ m4a ⟨st5, hag5, hlen5, hinc5, hrsz5, hsh5, htmk_eq5, htrc_eq5, hpr5,
            hfill_i, hfill_prev, hm4a⟩
        have _htmk5 := hlen5.scratch_ok.tarjan_mark_len
        have _htrc5 := hlen5.scratch_ok.tarjan_reach_len; c0_hsteps
        obtain ⟨hag6, hlen6, hfill6⟩ := m6_tarjan_fill_zero_step hag5 hlen5 htmk_eq5 htrc_eq5
          hfill_i hfill_prev (fun l hl => (hfill4 l hl).2) hidx_lt
        exact hJ4 (idx + 1#64, ()) _ (by dsimp only; omega) ⟨_, hag6, hlen6, hinc5, hrsz5, hsh5,
          by omega, hpr5, by rw [hidx1]; exact hfill6, by assumption⟩
      · intro Jrep hRep; c0_hsplit
        · have hidx_rp : idx.toNat < st4.core.repr.length := by rw [hrp4]; omega
          c0_hsteps; obtain ⟨hag5, hlen5, hpr5, hfill_i, hfill_prev⟩ := m6_tarjan_fill_set_repr
            hag4 hlen4 hpr4 (fun l hl => (hfill4 l hl).1) hidx_lt (by omega)
          refine hRep () _ ⟨_, hag5, hlen5, hinc4, hrsz4, hsh4, rfl, rfl, hpr5, hfill_i,
            hfill_prev, by rw [BitVec.eq_of_toNat_eq
              (by simp : (BitVec.ofNat 64 idx.toNat).toNat = idx.toNat)]; assumption⟩
        · have hne_idx : st4.core.repr[idx.toNat]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := by
            rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; assumption
          c0_hsteps; exact hRep () mk ⟨st4, hag4, hlen4, hinc4, hrsz4, hsh4, rfl, rfl, hpr4,
            hne_idx, fun l hl => (hfill4 l hl).1, hmk⟩
    · have hidx_eq := tarjan_u64_eq_2cv hcv_le hmx hidx_le hc; c0_hsteps
      have hfin := m6_tarjan_fill_finish hsp0 hagf husf hag4 hlen4 hinc4 hrsz4 hsh4 hincf hpr4
        (fun l hl => hfill4 l (by omega))
      have heq4 := agrees_tarjanSccMask_eq hag4
      exact hQ _ _ _ _ _ _ _ _ _ _ _ _ (heq4.symm ▸ hfin.1) (by rw [hrsz4]; exact hrszf)
        hfin.2.2.1 (fun _ => heq4.symm ▸ hfin.2.1 0) hfin.2.2.2.1 (heq4.symm ▸ hfin.2.2.2.2)
        (heq4.symm ▸ hmk)
  intro Jexit hExit; c0_hsplit; rotate_left
  · c0_hsteps; exact hExit () ml ⟨st, ⟨hag, hlen, hrsz, hpr, hus, hinc_u⟩, hml⟩
  have hrt_lt := tarjan_u64_lt_2cv hcv_le hmx hc
  have hrt1 : (root + 1#64).toNat = root.toNat + 1 := bv64_add1_toNat (by omega)
  c0_hsplit; rotate_left
  · c0_hsteps; exact hExit () ml ⟨st, ⟨hag, hlen, hrsz, hpr, hus, hinc_u⟩, hml⟩
  have hst_inc0 : st.core.inconsistent = 0#64 := hc; obtain ⟨htop0, hdfs⟩ := hinc_dfs hst_inc0
  c0_hsteps_nogrp
  refine wp_join_group (ts := [i32]) (fun (rch', ()) mj => ∃ st' : FullState,
      TarjanLoopBase c F_cur s0 st' ∧ (st'.core.inconsistent = 0#64 → st'.core.tmp_cnt = 0 ∧
        M6TarjanDfsInv c F0 F_cur s0 0 1 rch'.toNat 0 st') ∧ (FullMem c st' ⋆ R) mj) ?_ ?_
  · rintro _ ⟨rch', ⟨⟩⟩ mj ⟨st', hbase', hdfs', hmj⟩
    c0_hsteps; exact hJ2 (rch', root + 1#64, ()) mj (by dsimp only; omega)
      ⟨st', by omega, hbase', hdfs', hmj⟩
  intro Jskip hSkip; c0_hsplit; rotate_left
  · c0_hsteps; exact hSkip (reached, ()) ml ⟨st, ⟨hag, hlen, hrsz, hpr, hus, hinc_u⟩, hinc_dfs, hml⟩
  have hc_tmk := hc
  have _hrt_fl : (root >>> (1 : Nat)).toNat < st.core.flags.length := by
    rw [hfl_l, tarjan_bv64_ushr1_nat]; omega
  c0_hsplit; rotate_left
  · c0_hsteps; exact hSkip (reached, ()) ml ⟨st, ⟨hag, hlen, hrsz, hpr, hus, hinc_u⟩, hinc_dfs, hml⟩
  obtain ⟨hr_lt, hr1_nat, hrt32_eq, hr32_eq, hinit_base, hinit_dfs⟩ :=
    m6_tarjan_root_init_facts hw0 hdm0 hag hlen hdfs htop0 hrt_lt hc_tmk hc
  have hpos_mv : 0 < 2 * c.max_vars := by omega
  c0_hsteps_nogrp
  refine wp_loop_group (ts := [i32, .bool, i64])
    (fun n (rch, _failb, dsp, ()) m3 =>
      TarjanDfsPred c F0 F_cur s0 root.toNat reached.toNat rch dsp n R m3) ?_ ?_
  rotate_left
  · intro J3 hJ3; c0_hsteps
    refine hJ3 _ (reached + 1#32, false, 1#64, ()) m
      ⟨_, hinit_base, fun _ => ⟨rfl, hinit_dfs, fun h => by simp at h⟩, ?_⟩
    have h0_64 : (BitVec.ofNat 64 0).toNat = 0 := rfl
    have hhm := hm; try simp only [htop0, hrt32_eq, hr32_eq, h0_64] at hhm ⊢; exact hhm
  rintro J3 n ⟨rch, failb, dsp, ⟨⟩⟩ m3 hJ3 ⟨st3, hbase3, hdfs3, hm3⟩
  clear hinc_dfs hdfs hinit_base hinit_dfs hc_tmk hr_lt hrt32_eq hr32_eq hrsz hpr hus hinc_u htop0
    hst_inc0
  c0_hsplit; rotate_left
  · have hdsp0 : dsp.toNat = 0 := by have := hc; omega
    c0_hsteps; refine hSkip (rch, ()) m3 ⟨st3, hbase3, fun hinc30 => ?_, hm3⟩
    obtain ⟨_, hd3, htop3⟩ := hdfs3 hinc30; exact ⟨htop3 hdsp0, hd3.reset_empty (htop3 hdsp0)⟩
  have hdsp_pos : 0 < dsp.toNat := by simpa using hc
  c0_hsplit; rotate_left
  · c0_hsteps; exact hSkip (rch, ()) m3 ⟨st3, hbase3, fun h => absurd h hc, hm3⟩
  have hinc30 : st3.core.inconsistent = 0#64 := hc; obtain ⟨rfl, hd3, _⟩ := hdfs3 hinc30
  obtain ⟨hag3, hlen3, hrsz3, hpr3, hus3, hinc3⟩ := hbase3
  have hcl3 := hlen3.core_ok; have hsl3 := hlen3.scratch_ok
  have hdv_l3 := hsl3.work_stk2_len; have hdp_l3 := hsl3.wsort_len
  have htmk_l3 := hsl3.tarjan_mark_len; have htrc_l3 := hsl3.tarjan_reach_len
  have hfl_l3 := hcl3.flags_len; have hwv_l3 := hcl3.wvec_len; have hws_l3 := hcl3.wstk_len_arr
  have hcv3 := hag3.get (·.core.cur_vars); have hwv3 := hag3.get (·.core.wvec)
  have hws3 := hag3.get (·.core.wstk); have hfl3 := hag3.get (·.core.flags)
  have hdsp_sub := tarjan_u64_dsp_sub1 hdsp_pos
  have hlt_stk2 : dsp.toNat - 1 < st3.scratch.work_stk2.length := by
    rw [hdv_l3]; exact Nat.lt_of_lt_of_le (Nat.sub_lt hdsp_pos (by decide))
      (Nat.le_trans hd3.dsp_le (Nat.le_trans hd3.top_le
        (Nat.le_trans hd3.reached_le (Nat.mul_le_mul_left 2 hcv_le))))
  let lit := st3.scratch.work_stk2[(dsp - 1#64).toNat]'(by rw [hdsp_sub]; exact hlt_stk2)
  have hlit_get : lit = st3.scratch.work_stk2[dsp.toNat - 1]?.getD 0#32 := by
    simp only [lit, hdsp_sub, List.getElem?_eq_getElem hlt_stk2, Option.getD_some]
  obtain ⟨hdsp_lt3, hlit_lt, hnl_lt_nat, hnl_lt, hlit_act, hnl2, hnl2_1, hsb, hz_lit, hz_lit_lt⟩ :=
    m6_tarjan_dfs_head_facts hwat0 hcv3 hlen3 hd3 hdsp_pos hlit_get
  let pos32 := st3.scratch.wsort[(dsp - 1#64).toNat]'(by rw [hdsp_sub]; omega)
  have hpos_get : pos32 = st3.scratch.wsort[dsp.toNat - 1]?.getD 0#32 := by
    have hlt : dsp.toNat - 1 < st3.scratch.wsort.length := by omega
    simp only [pos32, hdsp_sub, List.getElem?_eq_getElem hlt, Option.getD_some]
  let off32 := st3.core.wvec[(BitVec.setWidth 64 (lit ^^^ 1#32) <<< (1 : Nat)).toNat]'(
    by rw [hnl2]; omega)
  let sz32 := st3.core.wvec[((BitVec.setWidth 64 (lit ^^^ 1#32) <<< (1 : Nat)) + 1#64).toNat]'(
    by rw [hnl2_1]; omega)
  let woff := fullWatchOffCore s0.core (lit.toNat ^^^ 1)
  let wsz := fullWatchSizeCore s0.core (lit.toNat ^^^ 1)
  have hoff_get : off32.toNat = woff := m6_tarjan_wvec_off hwv3 (by rw [hnl2]; omega) hnl2
  have hsz_get : sz32.toNat = wsz := m6_tarjan_wvec_sz hwv3 (by rw [hnl2_1]; omega) hnl2_1
  have hwle0 := hlen0.core_ok.wlen_le
  have _hwv_off : (BitVec.setWidth 64 (st3.scratch.work_stk2[(dsp - 1#64).toNat]'(
      by rw [hdsp_sub]; omega) ^^^ 1#32) <<< (1 : Nat)).toNat < st3.core.wvec.length := by
    change (BitVec.setWidth 64 (lit ^^^ 1#32) <<< (1 : Nat)).toNat < _; rw [hnl2, hwv_l3]; omega
  have _hwv_sz : ((BitVec.setWidth 64 (st3.scratch.work_stk2[(dsp - 1#64).toNat]'(
      by rw [hdsp_sub]; omega) ^^^ 1#32) <<< (1 : Nat)) + 1#64).toNat <
      st3.core.wvec.length := by
    change ((BitVec.setWidth 64 (lit ^^^ 1#32) <<< (1 : Nat)) + 1#64).toNat < _
    rw [hnl2_1, hwv_l3]; omega
  have hdsp_m1 : (2 ^ 64 - 1 + dsp.toNat) % 2 ^ 64 = dsp.toNat - 1 := by omega
  have hlit_hc : st3.scratch.work_stk2[(2 ^ 64 - 1 + dsp.toNat) % 2 ^ 64]'(by omega) = lit :=
    getElem_congr_idx _ _ (by rw [hdsp_m1, ← hdsp_sub])
  have hpos_hc : st3.scratch.wsort[(2 ^ 64 - 1 + dsp.toNat) % 2 ^ 64]'(by omega) = pos32 :=
    getElem_congr_idx _ _ (by rw [hdsp_m1, ← hdsp_sub])
  have hsz_hc : st3.core.wvec[(2 * ((st3.scratch.work_stk2[(2 ^ 64 - 1 + dsp.toNat) % 2 ^ 64]'(
      by omega)).toNat ^^^ 1) + 1) % 2 ^ 64]'(by
        rw [congrArg BitVec.toNat hlit_hc, Nat.mod_eq_of_lt (by omega), hwv_l3]; omega) = sz32 :=
    getElem_congr_idx _ _
      (by rw [congrArg BitVec.toNat hlit_hc, Nat.mod_eq_of_lt (by omega), hnl2_1])
  have hoff_hc : st3.core.wvec[(2 * ((st3.scratch.work_stk2[(2 ^ 64 - 1 + dsp.toNat) % 2 ^ 64]'(
      by omega)).toNat ^^^ 1)) % 2 ^ 64]'(by
        rw [congrArg BitVec.toNat hlit_hc, Nat.mod_eq_of_lt (by omega), hwv_l3]; omega) = off32 :=
    getElem_congr_idx _ _
      (by rw [congrArg BitVec.toNat hlit_hc, Nat.mod_eq_of_lt (by omega), hnl2])
  c0_hsplit
  · have hpos_lt : pos32.toNat < wsz := by rw [hpos_hc, hsz_hc] at hc; rw [← hsz_get]; exact hc
    have hidx_eq : (BitVec.setWidth 64 off32 + BitVec.setWidth 64 pos32).toNat =
        woff + pos32.toNat := by
      rw [bv64_add_toNat (by rw [zext_toNat _ (by decide), zext_toNat _ (by decide)]; omega),
        zext_toNat _ (by decide), zext_toNat _ (by decide), hoff_get]
    have hidx_lt : (BitVec.setWidth 64 off32 + BitVec.setWidth 64 pos32).toNat <
        st3.core.wstk.length := by rw [hidx_eq]; omega
    have hidx_mod : (off32.toNat + pos32.toNat) % 2 ^ 64 = woff + pos32.toNat := by
      rw [Nat.mod_eq_of_lt (by omega), hoff_get]
    dsimp only [off32, pos32, lit] at hidx_eq
    c0_hsplit
    · have hflag0 := m6_tarjan_wstk_flag0 hws3 hidx_mod (by omega) (by rw [hidx_mod]; omega)
        (by simp only [hoff_hc, hpos_hc] at hc; exact hc)
      have hp2 : (pos32 + 2#32).toNat = pos32.toNat + 2 := bv32_add2_toNat (by omega)
      obtain ⟨hd4, hmeas4⟩ :=
        m6_tarjan_nb_slice_prep hd3 hdsp_pos hlit_get hpos_get hpos_lt hflag0 hp2
      c0_hsteps
      let st4 : FullState := { st3 with scratch := { st3.scratch with
        wsort := st3.scratch.wsort.set (dsp.toNat - 1) (pos32 + 2#32) } }
      refine hJ3 _ (rch, failb, dsp, ()) _ hmeas4
        ⟨st4, hd4.toBase, fun _ => ⟨rfl, hd4, fun h => by omega⟩, ?_⟩
      have hw : st3.scratch.wsort.set (dsp - 1#64).toNat (pos32 + 2#32) =
          st3.scratch.wsort.set (dsp.toNat - 1) (pos32 + 2#32) := by rw [hdsp_sub]
      dsimp only [st4]; simpa only [← hw]
    have hflag1 := m6_tarjan_wstk_flag1 hws3 hidx_mod (by omega) (by rw [hidx_mod]; omega)
      (by simp only [hoff_hc, hpos_hc] at hc; exact hc)
    have hp1 : (pos32 + 1#32).toNat = pos32.toNat + 1 := bv32_add1_toNat (by omega)
    obtain ⟨w0, hw0_eq, hot_lt, hbins_ot, hskip_ok_fn, hslc_b1⟩ :=
      m6_tarjan_bin_slice_prep hd3 hdsp_pos hlit_get hpos_get hpos_lt hflag1 hp1
    have hw0_get : st3.core.wstk[(BitVec.setWidth 64 off32 +
        BitVec.setWidth 64 pos32).toNat]'hidx_lt = w0 := by
      have h1 := hw0_eq; rw [← hws3, List.getElem?_eq_getElem (by omega)] at h1
      simpa only [hidx_eq, woff, off32, pos32, lit] using Option.some.inj h1
    have hw0_mod : st3.core.wstk[(off32.toNat + pos32.toNat) % 2 ^ 64]'(by
        rw [hidx_mod]; omega) = w0 := by
      have h_eq : (off32.toNat + pos32.toNat) % 2 ^ 64 =
          (BitVec.setWidth 64 off32 + BitVec.setWidth 64 pos32).toNat := by
        dsimp only [off32, pos32, lit] at hidx_eq ⊢; rw [hidx_mod, hidx_eq]
      exact (getElem_congr_idx _ hidx_lt h_eq).trans hw0_get
    let ot := w0 &&& (2147483647 : BitVec 32)
    have hot_lt' : ot.toNat < 2 * s0.core.cur_vars := hot_lt
    obtain ⟨hz_ot, hdiv_ot, hot_z_raw, hot_div_raw⟩ := m6_tarjan_ot_bounds hcv_le hot_lt
    have hot_z_lt : (BitVec.setWidth 64 (st3.core.wstk[(BitVec.setWidth 64 off32 +
        BitVec.setWidth 64 pos32).toNat]'hidx_lt &&& (2147483647 : BitVec 32))).toNat <
        2 * c.max_vars := by dsimp only [off32, pos32, lit]; rw [hw0_get]; exact hot_z_raw
    have hot_div_lt : (BitVec.setWidth 64 ((st3.core.wstk[(BitVec.setWidth 64 off32 +
        BitVec.setWidth 64 pos32).toNat]'hidx_lt &&& (2147483647 : BitVec 32)) >>>
          (BitVec.toNat 1#32 % 32))).toNat < c.max_vars := by
      dsimp only [off32, pos32, lit]; rw [hw0_get]; exact hot_div_raw
    dsimp only [off32, pos32, lit] at hot_z_lt hot_div_lt; c0_hsteps_nogrp
    refine wp_join_group (ts := [i32, i64])
      (fun (rch', dsp', ()) mj =>
        TarjanNbPred c F0 F_cur s0 st3 root reached rch dsp.toNat rch' dsp' R mj) ?_ ?_
    · rintro _ ⟨rch', dsp', ⟨⟩⟩ mj ⟨st4, hdsp4, hd4, hm4, hmj⟩
      c0_hsteps; exact hJ3 _ (rch', failb, dsp', ()) mj hm4
        ⟨st4, hd4.toBase, fun _ => ⟨rfl, hd4, fun h => by omega⟩, hmj⟩
    intro Jb hJb
    let st3a : FullState := { st3 with scratch := { st3.scratch with
      wsort := st3.scratch.wsort.set (dsp.toNat - 1) (pos32 + 1#32) } }
    have hma : (FullMem c st3a ⋆ R) m := by
      dsimp only [st3a, pos32]
      simpa only [show (1 : BitVec 64) = 1#64 from rfl,
        show (1 : BitVec 32) = 1#32 from rfl, hdsp_sub] using hm
    have hfl_a : st3a.core.flags.length = c.max_vars := hfl_l3
    have htmk_a : st3a.scratch.tarjan_mark.length = 2 * c.max_vars := htmk_l3
    have htrc_a : st3a.scratch.tarjan_reach.length = 2 * c.max_vars := htrc_l3
    have hscc_a : st3a.scratch.work_stk1.length = 2 * c.max_vars := hsl3.work_stk1_len
    have hdv_a : st3a.scratch.work_stk2.length = 2 * c.max_vars := hdv_l3
    have hdp_a : st3a.scratch.wsort.length = 2 * c.max_vars := by simp [st3a, hdp_l3]
    have _htmk_z_a : (BitVec.setWidth 64 (st3.core.wstk[(BitVec.setWidth 64 off32 +
        BitVec.setWidth 64 pos32).toNat]'hidx_lt &&& (2147483647 : BitVec 32))).toNat <
        st3a.scratch.tarjan_mark.length := by
      dsimp only [off32, pos32, lit]; rw [htmk_a]; exact hot_z_lt
    have _htrc_z_a : (BitVec.setWidth 64 (st3.core.wstk[(BitVec.setWidth 64 off32 +
        BitVec.setWidth 64 pos32).toNat]'hidx_lt &&& (2147483647 : BitVec 32))).toNat <
        st3a.scratch.tarjan_reach.length := by
      dsimp only [off32, pos32, lit]; rw [htrc_a]; exact hot_z_lt
    have htrc_ot : st3.scratch.tarjan_reach[(BitVec.setWidth 64 (st3.core.wstk[(BitVec.setWidth 64
        off32 + BitVec.setWidth 64 pos32).toNat]'hidx_lt &&& (2147483647 : BitVec 32))).toNat]'(by
          rw [htrc_l3]; dsimp only [off32, pos32, lit]; exact hot_z_lt) =
        st3.scratch.tarjan_reach[ot.toNat]'(by omega) :=
      getElem_congr_idx _ _ (by dsimp only [off32, pos32, lit]; rw [hw0_get]; exact hz_ot)
    dsimp only [off32, pos32, lit] at htrc_ot _htmk_z_a _htrc_z_a
    c0_hsplit; rotate_left
    · exfalso
      rw [tarjan_wstk_hc_val hoff_hc hpos_hc hw0_mod] at hc
      change ¬ot.toNat < 2 * (s0.core.cur_vars % 2 ^ 64) % 2 ^ 64 at hc
      omega
    c0_hsplit; rotate_left
    · have hna : ¬ activeLit s0 ot.toNat := fun hact => hact.2 (by
        rw [← hfl3, List.getElem?_eq_getElem (by omega), Option.getD_some]
        dsimp only [st3a] at hc
        rw [tarjan_arr_hc_val (fun w => (w &&& (2147483647 : BitVec 32)).toNat / 2)
          hoff_hc hpos_hc hw0_mod (by
            rw [hfl_l3]; change ot.toNat / 2 < c.max_vars; omega)] at hc
        exact hc)
      obtain ⟨hd4, hm4⟩ := hskip_ok_fn (Or.inl hna)
      c0_hsteps; exact hJb (rch, dsp, ()) _ ⟨st3a, hdsp_pos, hd4, hm4, hma⟩
    have hact_ot : activeLit s0 ot.toNat := ⟨hot_lt', by
      rw [← hfl3, List.getElem?_eq_getElem (by omega), Option.getD_some]
      dsimp only [st3a] at hc
      rw [tarjan_arr_hc_val (fun w => (w &&& (2147483647 : BitVec 32)).toNat / 2)
        hoff_hc hpos_hc hw0_mod (by
          rw [hfl_l3]; change ot.toNat / 2 < c.max_vars; omega)] at hc
      exact hc⟩
    have hot_eq : (st3.core.wstk[(BitVec.setWidth 64 off32 +
        BitVec.setWidth 64 pos32).toNat]'hidx_lt &&& (2147483647 : BitVec 32)) = ot := by
      dsimp only [off32, pos32, lit]; rw [hw0_get]
    dsimp only [off32, pos32, lit] at hot_eq
    c0_hstep; c0_hsplit
    · have htmk_ot0 : (st3.scratch.tarjan_mark[ot.toNat]?.getD 0#32).toNat = 0 := by
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
        dsimp only [st3a] at hc
        rw [tarjan_arr_hc_val (fun w => (w &&& (2147483647 : BitVec 32)).toNat)
          hoff_hc hpos_hc hw0_mod (by rw [htmk_l3]; change ot.toNat < 2 * c.max_vars; omega)] at hc
        rw [hc]; rfl
      obtain ⟨hr_lt3, htop_lt3, hdsp_lt3', hr1_3, hr32_3, hdsp1, hdisc, hm_disc⟩ :=
        m6_tarjan_disc_pure hw0 hdm0 hd3 hdsp_pos hlit_get hpos_get hp1 hlit_act hact_ot hbins_ot
          htmk_ot0 hslc_b1
      have htc_mod_a : (BitVec.ofNat 64 st3a.core.tmp_cnt).toNat = st3.core.tmp_cnt := by
        dsimp only [st3a]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      have htc1_a : (BitVec.ofNat 64 st3a.core.tmp_cnt + 1#64).toNat = st3.core.tmp_cnt + 1 :=
        (bv64_add1_toNat (by rw [htc_mod_a]; omega)).trans (by rw [htc_mod_a])
      c0_hsteps
      let st4 : FullState := { st3 with
        core := { st3.core with tmp_cnt := st3.core.tmp_cnt + 1 }
        scratch := { st3.scratch with
          wsort := (st3.scratch.wsort.set (dsp.toNat - 1) (pos32 + 1#32)).set dsp.toNat 0#32
          tarjan_mark := st3.scratch.tarjan_mark.set ot.toNat (BitVec.ofNat 32 (rch.toNat + 1))
          tarjan_reach := st3.scratch.tarjan_reach.set ot.toNat (BitVec.ofNat 32 (rch.toNat + 1))
          work_stk1 := st3.scratch.work_stk1.set st3.core.tmp_cnt ot
          work_stk2 := st3.scratch.work_stk2.set dsp.toNat ot } }
      refine hJb (rch + 1#32, dsp + 1#64, ()) _ ⟨st4, by rw [hdsp1]; omega, hdisc, hm_disc, ?_⟩
      dsimp only [st4, st3a]; rw [← show (BitVec.setWidth 64 ot).toNat = ot.toNat from hz_ot,
        ← hot_eq, ← hr32_3, ← htc1_a, ← htc_mod_a, show (BitVec.ofNat 64
          (BitVec.ofNat 64 st3a.core.tmp_cnt).toNat + 1#64).toNat =
          (BitVec.ofNat 64 st3a.core.tmp_cnt + 1#64).toNat from by rw [htc_mod_a]]; exact hm
    have htmk_pos : 1 ≤ (st3.scratch.tarjan_mark[ot.toNat]?.getD 0#32).toNat := by
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; dsimp only [st3a] at hc
      rw [tarjan_arr_hc_val (fun w => (w &&& (2147483647 : BitVec 32)).toNat)
        hoff_hc hpos_hc hw0_mod (by rw [htmk_l3]; change ot.toNat < 2 * c.max_vars; omega)] at hc
      rw [show st3.scratch.tarjan_mark[(w0 &&& (2147483647 : BitVec 32)).toNat]'(
          by rw [htmk_l3]; change ot.toNat < 2 * c.max_vars; omega) =
          st3.scratch.tarjan_mark[ot.toNat]'(by omega) from getElem_congr_idx _ _ rfl] at hc
      exact Nat.pos_of_ne_zero fun h0 => hc (BitVec.eq_of_toNat_eq (by simpa using h0))
    have _htrc_lit_a : (BitVec.setWidth 64 (st3.scratch.work_stk2[(dsp - 1#64).toNat]'(
        by rw [hdsp_sub]; exact hlt_stk2))).toNat < st3a.scratch.tarjan_reach.length := by
      change (BitVec.setWidth 64 lit).toNat < _; rw [htrc_a]; exact hz_lit_lt
    c0_hstep; c0_hsplit
    · have htrc_lt : (st3.scratch.tarjan_reach[ot.toNat]?.getD 0#32).toNat <
          (st3.scratch.tarjan_reach[lit.toNat]?.getD 0#32).toNat := by
        have h1 := hc; dsimp only [st3a] at h1
        rw [tarjan_arr_hc_val (fun w => (w &&& (2147483647 : BitVec 32)).toNat)
          hoff_hc hpos_hc hw0_mod (by rw [htrc_l3]; change ot.toNat < 2 * c.max_vars; omega),
          tarjan_getElem_lit_eq hlit_hc (by rw [htrc_l3]; omega)] at h1
        rwa [List.getElem?_eq_getElem (by rw [htrc_l3]; omega : ot.toNat < _), Option.getD_some]
      obtain ⟨hbe_inv, hbe_meas⟩ := m6_tarjan_be_pure hw0 hdm0 hd3 hdsp_pos hlit_get hpos_get hp1
        hlit_act hact_ot hbins_ot htmk_pos htrc_lt hslc_b1; c0_hsteps
      let st4 : FullState := { st3 with scratch := { st3.scratch with
        wsort := st3.scratch.wsort.set (dsp.toNat - 1) (pos32 + 1#32)
        tarjan_reach := st3.scratch.tarjan_reach.set lit.toNat
          (st3.scratch.tarjan_reach[ot.toNat]?.getD 0#32) } }
      refine hJb (rch, dsp, ()) _ ⟨st4, hdsp_pos, hbe_inv, hbe_meas, ?_⟩
      dsimp only [st4, st3a]; rw [← show (BitVec.setWidth 64 lit).toNat = lit.toNat from hz_lit,
        ← (by rw [List.getElem?_eq_getElem (by omega), Option.getD_some] :
          st3.scratch.tarjan_reach[ot.toNat]'(by omega) =
          st3.scratch.tarjan_reach[ot.toNat]?.getD 0#32), ← htrc_ot]; exact hm
    · have htrc_ge : (st3.scratch.tarjan_reach[lit.toNat]?.getD 0#32).toNat ≤
          (st3.scratch.tarjan_reach[ot.toNat]?.getD 0#32).toNat := by
        have hge := Nat.le_of_not_lt hc; dsimp only [st3a] at hge
        rw [tarjan_arr_hc_val (fun w => (w &&& (2147483647 : BitVec 32)).toNat)
          hoff_hc hpos_hc hw0_mod (by rw [htrc_l3]; change ot.toNat < 2 * c.max_vars; omega),
          tarjan_getElem_lit_eq hlit_hc (by rw [htrc_l3]; omega)] at hge
        rw [List.getElem?_eq_getElem (by rw [htrc_l3]; omega : ot.toNat < _), Option.getD_some]
        exact hge
      obtain ⟨hd4, hm4⟩ := hskip_ok_fn (Or.inr ⟨htmk_pos, htrc_ge⟩)
      c0_hsteps; exact hJb (rch, dsp, ()) _ ⟨st3a, hdsp_pos, hd4, hm4, hma⟩
  have hpos_ge : wsz ≤ (st3.scratch.wsort[dsp.toNat - 1]?.getD 0#32).toNat := by
    rw [hpos_hc, hsz_hc] at hc; rw [← hpos_get, ← hsz_get]; exact Nat.le_of_not_lt hc
  let rlit := st3.scratch.tarjan_reach[lit.toNat]'(by omega)
  have hrlit_eq : rlit = st3.scratch.tarjan_reach[lit.toNat]?.getD 0#32 := by
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
  have _htrc_lit : (BitVec.setWidth 64 (st3.scratch.work_stk2[(dsp - 1#64).toNat]'(
      by rw [hdsp_sub]; omega))).toNat < st3.scratch.tarjan_reach.length := by
    change (BitVec.setWidth 64 lit).toNat < _; rw [htrc_l3]; exact hz_lit_lt
  have _htmk_lit : (BitVec.setWidth 64 (st3.scratch.work_stk2[(dsp - 1#64).toNat]'(
      by rw [hdsp_sub]; omega))).toNat < st3.scratch.tarjan_mark.length := by
    change (BitVec.setWidth 64 lit).toNat < _; rw [htmk_l3]; exact hz_lit_lt
  c0_hsteps_nogrp
  refine wp_join_group (ts := [.bool])
    (fun (_failb', ()) mj =>
      TarjanPopPred c F0 F_cur s0 st3 root.toNat reached.toNat rch.toNat dsp.toNat R mj) ?_ ?_
  · rintro _ ⟨failb', ⟨⟩⟩ mj ⟨st4, hbase4, hd4, hmj⟩; c0_hsteps
    by_cases hinc40 : st4.core.inconsistent = 0#64
    · obtain ⟨hd4', hm4', htop4'⟩ := hd4 hinc40
      exact hJ3 _ (rch, failb', dsp - 1#64, ()) mj hm4' ⟨st4, hbase4, fun _ =>
        ⟨by rw [hdsp_sub], by rwa [hdsp_sub], fun h => htop4' (by rwa [hdsp_sub] at h)⟩, hmj⟩
    · exact hJ3 0 (rch, failb', dsp - 1#64, ()) mj (M6TarjanDfsInv.measure_pos hdsp_pos)
        ⟨st4, hbase4, fun h => absurd h hinc40, hmj⟩
  intro Jpop hPopJ; c0_hsplit
  · have hne_tmk : rlit.toNat ≠ (st3.scratch.tarjan_mark[lit.toNat]?.getD 0#32).toNat := by
      rw [tarjan_getElem_lit_eq hlit_hc (by rw [htrc_l3]; omega), ← hrlit_eq,
        tarjan_getElem_lit_eq hlit_hc (by rw [htmk_l3]; omega)] at hc
      exact fun heq => hc (BitVec.eq_of_toNat_eq heq)
    obtain ⟨hdsp_gt1, _⟩ := m6_tarjan_pop_nonroot (rlit := rlit) hw0 hdm0 hd3 hdsp_pos
      (by rw [← hlit_get]; exact hrlit_eq) (by rw [← hlit_get]; exact hpos_ge)
      (by rw [← hlit_get]; exact hne_tmk)
    obtain ⟨hpar_get, hpar_lt_cv, hz_par, hpar_trc_lt⟩ := m6_tarjan_par_facts hd3 hdsp_gt1
    have _hpar_len : (dsp - 1#64 - 1#64).toNat < st3.scratch.work_stk2.length := by
      rw [tarjan_u64_dsp_sub2 hdsp_gt1, hdv_l3]; omega
    c0_hsteps_nogrp
    refine wp_join_group (ts := []) (fun () mj =>
      TarjanPopPred c F0 F_cur s0 st3 root.toNat reached.toNat rch.toNat dsp.toNat R mj) ?_ ?_
    · rintro _ ⟨⟩ mj ⟨st4, hb4, hd4, hmj⟩; c0_hsteps
      exact hPopJ (failb, ()) mj ⟨st4, hb4, hd4, hmj⟩
    intro Jd hJd
    have hstk2_m1 : (dsp - (1 : BitVec 64)).toNat < st3.scratch.work_stk2.length := by
      rw [show (1 : BitVec 64) = 1#64 from rfl, hdsp_sub]; exact hlt_stk2
    have htrc_self : st3.scratch.tarjan_reach.set (BitVec.setWidth 64
        (st3.scratch.work_stk2[(dsp - (1 : BitVec 64)).toNat]'hstk2_m1)).toNat
        (st3.scratch.tarjan_reach[(BitVec.setWidth 64 (st3.scratch.work_stk2[(dsp -
          (1 : BitVec 64)).toNat]'hstk2_m1)).toNat]'_htrc_lit) = st3.scratch.tarjan_reach :=
      list_set_getElem_self_eq _htrc_lit
    replace hm : (FullMem c st3 ⋆ R) m := by simpa only [htrc_self] using hm
    c0_hsplit; rotate_left
    · exfalso; rw [hdsp_m1] at hc; omega
    c0_hsteps_nogrp
    refine wp_join_group (ts := []) (fun () mk =>
      TarjanPopPred c F0 F_cur s0 st3 root.toNat reached.toNat rch.toNat dsp.toNat R mk) ?_ ?_
    · rintro _ ⟨⟩ mk ⟨st4, hb4, hd4, hmk⟩; c0_hsteps; exact hJd () mk ⟨st4, hb4, hd4, hmk⟩
    have hpar_hc : st3.scratch.work_stk2[(2 ^ 64 - 1 + (2 ^ 64 - 1 + dsp.toNat)) % 2 ^ 64]'(
        by rw [tarjan_u64_dsp_sub2 hdsp_gt1] at _hpar_len; omega) =
        st3.scratch.work_stk2[(dsp - 1#64 - 1#64).toNat]'_hpar_len :=
      getElem_congr_idx _ _ (by rw [tarjan_u64_dsp_sub2 hdsp_gt1]; omega)
    intro Jr hJr; c0_hsplit
    · c0_hsteps
      rw [tarjan_getElem_lit_eq hlit_hc (by rw [htrc_l3]; omega), ← hrlit_eq,
        tarjan_getElem_par_eq hpar_hc hpar_trc_lt hz_par] at hc
      obtain ⟨_, hb4, hd4, hm4⟩ := m6_tarjan_nonroot_lt_step hw0 hdm0 hd3 hdsp_pos hlit_get
        hrlit_eq hpos_ge hne_tmk hpar_get hz_par (by rw [htrc_l3]; omega) hpar_trc_lt hc
      let st4 : FullState := { st3 with scratch := { st3.scratch with
        tarjan_reach := st3.scratch.tarjan_reach.set
          (st3.scratch.work_stk2[dsp.toNat - 2]?.getD 0#32).toNat rlit } }
      refine hJr () _ ⟨st4, hb4, fun _ => ⟨hd4, hm4, fun h => by omega⟩, ?_⟩
      dsimp only [st4]; rw [← hpar_get, ← hz_par]; exact hm
    · rw [tarjan_getElem_lit_eq hlit_hc (by rw [htrc_l3]; omega), ← hrlit_eq,
        tarjan_getElem_par_eq hpar_hc hpar_trc_lt hz_par] at hc
      obtain ⟨_, hb4, hd4, hm4⟩ := m6_tarjan_nonroot_ge_step hw0 hdm0 hd3 hdsp_pos hlit_get
        hrlit_eq hpos_ge hne_tmk hpar_get hz_par (by rw [htrc_l3]; omega) hpar_trc_lt hc
      c0_hsteps; exact hJr () _ ⟨st3, hb4, fun _ => ⟨hd4, hm4, fun h => by omega⟩, hm⟩
  have hr_eq_bv : rlit = st3.scratch.tarjan_mark[lit.toNat]?.getD 0#32 := by
    rw [tarjan_getElem_lit_eq hlit_hc (by rw [htrc_l3]; omega), ← hrlit_eq,
      tarjan_getElem_lit_eq hlit_hc (by rw [htmk_l3]; omega)] at hc
    exact hc
  obtain ⟨k0, hk0_lt, hk0_bv, hk0_uniq, hk0_zero, hk0_eqv, hmr_reach⟩ :=
    m6_tarjan_root_call_facts hw0 hdm0 hd3 hdsp_pos hcv3 hrt_lt hr1_nat hlit_get hrlit_eq
      hpos_ge hr_eq_bv
  c0_hsteps <;> refine m6_tarjan_pop_scc_call_wp hPop hw0 hinc30 hdsp_pos hrt_lt hlit_lt hd3
      hlit_get hk0_lt hk0_bv hk0_uniq hk0_zero hk0_eqv ?_ hm3 (fun b mj h => by
        dsimp only; c0_hsteps; first | exact h | exact hPopJ (b, ()) mj h)
  · exact fun h => absurd rfl h
  · exact hmr_reach

/-- `full_tarjan_scc` satisfies canonical `fullTarjanSccSpec` parametrically in `Γ`. -/
theorem full_tarjan_scc_wp (Γ : Env)
    (hPop : Γ.Has "full_tarjan_pop_scc" Spec.fullTarjanPopSccSpec) :
    ∀ args m Q X, Spec.fullTarjanSccSpec args m Q X →
      Func.wp Γ full_tarjan_scc_body args m Q X := fun _ m Q X hs =>
  full_tarjan_scc_fast_wp Γ hPop _ m Q X (fullTarjanSccFastSpec_of_canon hs)

end

end LeanQbe.T.Examples.Kissat.Proof.Substitute
