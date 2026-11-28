/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.PropSearch.Spec
public import LeanQbe.T.Examples.Kissat.Proof.PropSearch.BcpPropHelpers
public import LeanQbe.T.Examples.Kissat.Src.PropSearch
public import LeanQbe.T.Logic.CanonicalEnv
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
meta import LeanQbe.T.Logic.C0Step
meta import LeanQbe.T.Logic.C0HeadStep

/-!
# Canonical WP Proofs for `PropSearch`: Overflow & Delayed Watch Flush (`WpOvfFlush`)

Self-contained `CanonicalEnv` `Func.wp` proofs (`0` legacy `Full*` imports, `<= 1,500` LOC,
`<= 450` LOC/decl, `<= 100` cols, `0` `@[expose]` on theorems):
1. `full_prop_lit_ovf_hot_wp` (`fullPropLitOvfHotSpec`).
2. `full_prop_flush_slow_fid_wp` (`fidPropFlushSlowSpec`, factored loop step).
3. `full_prop_flush_del_fid_wp` (`fidPropFlushDelSpec`, factored loop step).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.PropSearch

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.PropSearch
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.PropSearch.Spec
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Proof.PropSearch.BcpPropTactics
open Kraken.Bedrock2.Test

@[local bv_c0] private theorem p0_bv64_0_toNat : (0 : BitVec 64).toNat = 0 := rfl
@[local bv_c0] private theorem p0_bv64_1_toNat : (1 : BitVec 64).toNat = 1 := rfl
@[local bv_c0] private theorem p0_bv64_2_toNat : (2 : BitVec 64).toNat = 2 := rfl

local macro "p0_hsplit" : tactic =>
  `(tactic| (c0_hsplit; all_goals try simp only [bv_c0, Nat.reduceMod] at hc))

/-! ## 1. `full_prop_lit_ovf_hot_wp` -/

theorem full_prop_lit_ovf_hot_wp (Γ : Env)
    (hPush : Γ.Has "full_watch_push" fullWatchPushSpec) :
    ∀ args m Q X, fullPropLitOvfHotSpec args m Q X →
      Func.wp Γ full_prop_lit_ovf_hot_body args m Q X := by
  rintro ⟨h, rw, w0, cref, ⟨⟩⟩ m Q X hsp
  unfold Func.wp full_prop_lit_ovf_hot_body
  c0_hsteps_nogrp
  exact wp_call_of_spec _ _ (hPush _ _ _ _ hsp)

/-! ## 2. Delayed Watch Flush Helpers -/

private theorem p0_bv64_ofNat {n : Nat} (hn : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

private theorem p0_getElem_idx {α : Type} {xs : List α} {i j : Nat}
    (hij : i = j) (hi : i < xs.length) (hj : j < xs.length) : xs[i]'hi = xs[j]'hj := by
  subst hij; rfl

private def p0FlushDisk (wl_d : Nat) (wu_d : BitVec 64) (st : FullState) : FullState :=
  { st with core := { st.core with wlen := wl_d, wusable := wu_d } }

private theorem p0_flush_true_preserves {F_cur : List (List Nat)} {k k' : FullCoreState}
    {skip_lit : Nat} {lit w0 cref : BitVec 32}
    (hk' : k'.cur_vars = k.cur_vars)
    (hrefs : ∀ r, r ∈ fullArenaClauseRefsCore k → r ∈ fullArenaClauseRefsCore k')
    (hlay' : WatchStackLayout k') (hlit : lit.toNat < 2 * k.cur_vars) (hne : lit.toNat ≠ skip_lit)
    (hw0_f : (w0 &&& 0x80000000#32) = 0#32) (hcr_lt : cref.toNat < 0x80000000)
    (hcr_ref : cref.toNat ∈ fullArenaClauseRefsCore k')
    (hpres_o : ∀ l < 2 * k.cur_vars, l ≠ lit.toNat →
      fullWatchSizeCore k' l = fullWatchSizeCore k l ∧
      ∀ idx < fullWatchSizeCore k l,
        k'.wstk[fullWatchOffCore k' l + idx]? = k.wstk[fullWatchOffCore k l + idx]?)
    (hpush : fullWatchSizeCore k' lit.toNat = fullWatchSizeCore k lit.toNat + 2 ∧
      (∀ idx < fullWatchSizeCore k lit.toNat,
        k'.wstk[fullWatchOffCore k' lit.toNat + idx]? =
          k.wstk[fullWatchOffCore k lit.toNat + idx]?) ∧
      k'.wstk[fullWatchOffCore k' lit.toNat + fullWatchSizeCore k lit.toNat]? = some w0 ∧
      k'.wstk[fullWatchOffCore k' lit.toNat + fullWatchSizeCore k lit.toNat + 1]? = some cref) :
    (WatchesInv F_cur k → WatchesInv F_cur k') ∧
    (skip_lit < 2 * k.cur_vars →
      ∀ off q p end_v, SplitWatchesInv F_cur k skip_lit off q p end_v →
        let off' := fullWatchOffCore k' skip_lit
        SplitWatchesInv F_cur k' skip_lit off'
          (off' + (q - off)) (off' + (p - off)) (off' + (end_v - off))) := by
  have hF : (cnfOfClauses F_cur).Entails (cnfOfClauses F_cur) := by
    rw [CNF.entails_def]; exact fun _ hx => hx
  refine ⟨fun hw => WatchesInv.mk hlay' fun l hl => ?_, fun hsk off q p end_v hsw => ?_⟩
  · have hl0 : l < 2 * k.cur_vars := hk' ▸ hl
    by_cases hlr : l = lit.toNat
    · subst hlr; rw [hpush.1]
      exact watchSlice_append_large (k := k) (k' := k') (by omega) hrefs hpush.2.1
        (hw.slices lit.toNat hl0) hpush.2.2.1 hpush.2.2.2 hw0_f hcr_lt hcr_ref
    · obtain ⟨hsz, hpre⟩ := hpres_o l hl0 hlr
      rw [hsz]
      exact watchSlice_relocate (k := k) (k' := k') hF (by omega) hrefs hpre (hw.slices l hl0)
  · have hpush' : fullWatchSizeCore k' lit.toNat = fullWatchSizeCore k lit.toNat + 2 ∧
        (∀ idx < fullWatchSizeCore k lit.toNat,
          k'.wstk[fullWatchOffCore k' lit.toNat + idx]? =
            k.wstk[fullWatchOffCore k lit.toNat + idx]?) ∧
        k'.wstk[fullWatchOffCore k' lit.toNat + fullWatchSizeCore k lit.toNat]? =
          some (BitVec.ofNat 32 w0.toNat) ∧
        k'.wstk[fullWatchOffCore k' lit.toNat + fullWatchSizeCore k lit.toNat + 1]? =
          some (BitVec.ofNat 32 cref.toNat) := by
      simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using hpush
    have hw0_f' : (BitVec.ofNat 32 w0.toNat &&& 0x80000000#32) = 0#32 := by
      simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using hw0_f
    exact SplitWatchesInv.push_nonskip (k := k) (k' := k') (lit := lit.toNat) (w0 := w0.toNat)
      (cref := cref.toNat) hk' hrefs hlit hne hsw hsk hlay' hpres_o hpush' hw0_f' hcr_lt hcr_ref

private theorem p0_flush_false_preserves {F_cur : List (List Nat)} {k k' : FullCoreState}
    {skip_lit : Nat} {lit : BitVec 32}
    (hk' : k'.cur_vars = k.cur_vars)
    (hrefs : ∀ r, r ∈ fullArenaClauseRefsCore k → r ∈ fullArenaClauseRefsCore k')
    (hlay' : WatchStackLayout k')
    (hpres_o : ∀ l < 2 * k.cur_vars, l ≠ lit.toNat →
      fullWatchSizeCore k' l = fullWatchSizeCore k l ∧
      ∀ idx < fullWatchSizeCore k l,
        k'.wstk[fullWatchOffCore k' l + idx]? = k.wstk[fullWatchOffCore k l + idx]?)
    (hpres_r : lit.toNat < 2 * k.cur_vars →
      fullWatchSizeCore k' lit.toNat = fullWatchSizeCore k lit.toNat ∧
      ∀ idx < fullWatchSizeCore k lit.toNat,
        k'.wstk[fullWatchOffCore k' lit.toNat + idx]? =
          k.wstk[fullWatchOffCore k lit.toNat + idx]?) :
    (WatchesInv F_cur k → WatchesInv F_cur k') ∧
    (skip_lit < 2 * k.cur_vars →
      ∀ off q p end_v, SplitWatchesInv F_cur k skip_lit off q p end_v →
        let off' := fullWatchOffCore k' skip_lit
        SplitWatchesInv F_cur k' skip_lit off'
          (off' + (q - off)) (off' + (p - off)) (off' + (end_v - off))) := by
  have hF : (cnfOfClauses F_cur).Entails (cnfOfClauses F_cur) := by
    rw [CNF.entails_def]; exact fun _ hx => hx
  have hslice_eq : ∀ l < 2 * k.cur_vars,
      fullWatchSizeCore k' l = fullWatchSizeCore k l ∧
      ∀ idx < fullWatchSizeCore k l,
        k'.wstk[fullWatchOffCore k' l + idx]? = k.wstk[fullWatchOffCore k l + idx]? := fun l hl =>
    if h : l = lit.toNat then h ▸ hpres_r (h ▸ hl) else hpres_o l hl h
  refine ⟨fun hw => WatchesInv.mk hlay' fun l hl => ?_, fun hsk off q p end_v hsw => ?_⟩
  · have hl0 : l < 2 * k.cur_vars := hk' ▸ hl
    obtain ⟨hsz, hpre⟩ := hslice_eq l hl0
    rw [hsz]
    exact watchSlice_relocate (k := k) (k' := k') hF (by omega) hrefs hpre (hw.slices l hl0)
  · intro off'
    obtain ⟨hsz_sk, hpre_sk⟩ := hslice_eq skip_lit hsk
    rw [hsw.off_eq, hsw.sz_eq] at hpre_sk
    have hq_ge := hsw.q_ge; have hq_le := hsw.q_le_p; have hp_le := hsw.p_le_end
    refine
      { layout := hlay', off_eq := rfl
        sz_eq := by rw [hsz_sk, hsw.sz_eq]; omega
        sz_pos := by have := hsw.sz_pos; omega
        q_ge := by omega, q_le_p := by omega, p_le_end := by omega
        other_slices := fun l hl hln => by
          have hl0 : l < 2 * k.cur_vars := hk' ▸ hl
          obtain ⟨hsz_l, hpre_l⟩ := hslice_eq l hl0; rw [hsz_l]
          exact watchSlice_relocate (k := k) (k' := k') hF (by omega) hrefs hpre_l
            (hsw.other_slices l hl0 hln)
        kept_slice := by
          rw [show off' + (q - off) - off' = q - off by omega]
          exact watchSlice_relocate (k := k) (k' := k') hF (by omega) hrefs
            (fun j hj => hpre_sk j (by omega)) hsw.kept_slice
        rem_slice := by
          rw [show off' + (end_v - off) - (off' + (p - off)) = end_v - p by omega]
          refine watchSlice_relocate (k := k) (k' := k') hF (by omega) hrefs (fun j hj => ?_)
            hsw.rem_slice
          have hj' := hpre_sk ((p - off) + j) (by omega)
          rwa [show off' + (p - off + j) = off' + (p - off) + j by omega,
            show off + (p - off + j) = p + j by omega] at hj' }

private theorem p0_slow_case1_fin {c : FullCfg} {F_cur : List (List Nat)}
    {st0 st : FullState} {skip_lit : Nat}
    {rw_v ow_v cr_v : BitVec 32} {wu_n : BitVec 64}
    {sz0 wend0 : Nat}
    (hsz0 : sz0 = fullWatchSizeCore st.core rw_v.toNat)
    (hwend0 : wend0 = fullWatchOffCore st.core rw_v.toNat + sz0)
    (hlay : WatchStackLayout st.core) (hlen : st.LengthsOk c)
    (hrw_lt : rw_v.toNat < 2 * st.core.cur_vars)
    (hrsz_pos : 0 < fullWatchSizeCore st.core rw_v.toNat)
    (hend2_le : fullWatchOffCore st.core rw_v.toNat +
      fullWatchSizeCore st.core rw_v.toNat + 2 ≤ st.core.wlen)
    (hsent0 : st.core.wstk[fullWatchOffCore st.core rw_v.toNat +
      fullWatchSizeCore st.core rw_v.toNat]? = some 0xFFFFFFFF#32)
    (hsent1 : st.core.wstk[fullWatchOffCore st.core rw_v.toNat +
      fullWatchSizeCore st.core rw_v.toNat + 1]? = some 0xFFFFFFFF#32)
    (how_f : (ow_v &&& 0x80000000#32) = 0#32) (hcr_lt_st : cr_v.toNat < 0x80000000)
    (hcr_ref_st : cr_v.toNat ∈ fullArenaClauseRefsCore st.core)
    (hrw_ne : rw_v.toNat ≠ skip_lit) (hcv_eq : st.core.cur_vars = st0.core.cur_vars)
    (hcore_eq : st.core =
      { st0.core with
          wvec := st.core.wvec, wstk := st.core.wstk,
          wlen := st.core.wlen, wusable := st.core.wusable })
    (hsc_eq : st.scratch = { st0.scratch with wsort := st.scratch.wsort })
    (hwat_pres : WatchesInv F_cur st0.core → WatchesInv F_cur st.core)
    (hsw_pres : skip_lit < 2 * st0.core.cur_vars →
      ∀ off q p end_v, SplitWatchesInv F_cur st0.core skip_lit off q p end_v →
        let off' := fullWatchOffCore st.core skip_lit
        SplitWatchesInv F_cur st.core skip_lit off'
          (off' + (q - off)) (off' + (p - off)) (off' + (end_v - off))) :
    let st_n : FullState :=
      { st with
          core :=
            { st.core with
                wstk := (st.core.wstk.set wend0 ow_v).set (wend0 + 1) cr_v
                wvec := st.core.wvec.set (2 * rw_v.toNat + 1) (BitVec.ofNat 32 (sz0 + 2))
                wusable := wu_n } }
    st_n.core =
      { st0.core with
          wvec := st_n.core.wvec, wstk := st_n.core.wstk,
          wlen := st_n.core.wlen, wusable := st_n.core.wusable } ∧
    st_n.scratch = { st0.scratch with wsort := st_n.scratch.wsort } ∧
    st_n.LengthsOk c ∧ WatchStackLayout st_n.core ∧
    (WatchesInv F_cur st0.core → WatchesInv F_cur st_n.core) ∧
    (skip_lit < 2 * st0.core.cur_vars →
      ∀ off q p end_v, SplitWatchesInv F_cur st0.core skip_lit off q p end_v →
        let off' := fullWatchOffCore st_n.core skip_lit
        SplitWatchesInv F_cur st_n.core skip_lit off'
          (off' + (q - off)) (off' + (p - off)) (off' + (end_v - off))) := by
  subst hsz0 hwend0
  obtain ⟨hlen_k0, hlay_k0, h_off_ne, hpres_o, hsz_k, hpre_k, hw0_k, hw1_k⟩ :=
    s15_append_sentinel_layout hlay hlen.core_ok hrw_lt hrsz_pos
      hsent0 hsent1 (by omega) how_f hcr_lt_st
  let st_n : FullState :=
    { st with core := { st.core with
        wstk := (st.core.wstk.set (fullWatchOffCore st.core rw_v.toNat +
          fullWatchSizeCore st.core rw_v.toNat) ow_v).set
          (fullWatchOffCore st.core rw_v.toNat + fullWatchSizeCore st.core rw_v.toNat + 1) cr_v
        wvec := st.core.wvec.set (2 * rw_v.toNat + 1)
          (BitVec.ofNat 32 (fullWatchSizeCore st.core rw_v.toNat + 2))
        wusable := wu_n } }
  have hlen_k : st_n.core.LengthsOk c :=
    ⟨hlen_k0.vals_len, hlen_k0.lit_mark_len, hlen_k0.mrk_len, hlen_k0.flags_len,
     hlen_k0.lvl_len, hlen_k0.rsns_len, hlen_k0.trl_len, hlen_k0.trail_pos_len,
     hlen_k0.tmp_len_arr, hlen_k0.min_clr_len_arr, hlen_k0.frame_trail_len,
     hlen_k0.frame_dec_len, hlen_k0.wvec_len, hlen_k0.repr_len, hlen_k0.min_stk_len,
     hlen_k0.arena_len_arr, hlen_k0.wstk_len_arr, hlen_k0.cur_vars_ge, hlen_k0.cur_vars_le,
     hlen_k0.arena_len_le, hlen_k0.wlen_le, hlen_k0.trail_end_le, hlen_k0.propagated_le,
     hlen_k0.tmp_len_le, hlen_k0.min_clr_len_le⟩
  have hlay_k : WatchStackLayout st_n.core :=
    ⟨hlay_k0.bounds, hlay_k0.pos_off, hlay_k0.disjoint, hlay_k0.no_sentinel⟩
  have hstep := s15_flush_step_preserves (_c := c) (F_cur := F_cur) (k := st.core)
    (k' := st_n.core) (lit := rw_v.toNat) (w0 := ow_v) (cref := cr_v)
    (skip_lit := skip_lit) rfl (fun _ h => h) hrw_lt hrw_ne how_f hcr_lt_st hcr_ref_st
    h_off_ne hpres_o ⟨hsz_k, hpre_k, hw0_k, hw1_k⟩ hlay_k
  refine ⟨by dsimp [st_n]; rw [hcore_eq], hsc_eq,
    ⟨hlen_k, hlen.scratch_ok⟩, hlay_k, fun hw0 => hstep.1 (hwat_pres hw0), ?_⟩
  intro hsk off q p end_v hsw0
  have hsw1 := hsw_pres hsk off q p end_v hsw0
  have hsw2 := hstep.2 (hcv_eq ▸ hsk)
    (fullWatchOffCore st.core skip_lit)
    (fullWatchOffCore st.core skip_lit + (q - off))
    (fullWatchOffCore st.core skip_lit + (p - off))
    (fullWatchOffCore st.core skip_lit + (end_v - off)) hsw1
  simpa only [Nat.add_sub_cancel_left] using hsw2

private theorem p0_slow_case2a_fin {c : FullCfg} {F_cur : List (List Nat)}
    {st0 st : FullState} {skip_lit : Nat}
    {rw_v ow_v cr_v : BitVec 32}
    (hlay : WatchStackLayout st.core) (hlen : st.LengthsOk c)
    (hrw_lt : rw_v.toNat < 2 * st.core.cur_vars) (hw_pos : 1 ≤ st.core.wlen)
    (hrsz0 : fullWatchSizeCore st.core rw_v.toNat = 0)
    (hfit2 : st.core.wlen + 2 ≤ c.wcap) (how_f : (ow_v &&& 0x80000000#32) = 0#32)
    (hcr_lt_st : cr_v.toNat < 0x80000000)
    (hcr_ref_st : cr_v.toNat ∈ fullArenaClauseRefsCore st.core)
    (hrw_ne : rw_v.toNat ≠ skip_lit) (hcv_eq : st.core.cur_vars = st0.core.cur_vars)
    (hcore_eq : st.core =
      { st0.core with
          wvec := st.core.wvec, wstk := st.core.wstk,
          wlen := st.core.wlen, wusable := st.core.wusable })
    (hsc_eq : st.scratch = { st0.scratch with wsort := st.scratch.wsort })
    (hwat_pres : WatchesInv F_cur st0.core → WatchesInv F_cur st.core)
    (hsw_pres : skip_lit < 2 * st0.core.cur_vars →
      ∀ off q p end_v, SplitWatchesInv F_cur st0.core skip_lit off q p end_v →
        let off' := fullWatchOffCore st.core skip_lit
        SplitWatchesInv F_cur st.core skip_lit off'
          (off' + (q - off)) (off' + (p - off)) (off' + (end_v - off))) :
    let st_n : FullState :=
      { st with
          core :=
            { st.core with
                wstk := (st.core.wstk.set st.core.wlen ow_v).set (st.core.wlen + 1) cr_v
                wvec := (st.core.wvec.set (2 * rw_v.toNat)
                  (BitVec.ofNat 32 st.core.wlen)).set (2 * rw_v.toNat + 1) 2#32
                wlen := st.core.wlen + 2 } }
    st_n.core =
      { st0.core with
          wvec := st_n.core.wvec, wstk := st_n.core.wstk,
          wlen := st_n.core.wlen, wusable := st_n.core.wusable } ∧
    st_n.scratch = { st0.scratch with wsort := st_n.scratch.wsort } ∧
    st_n.LengthsOk c ∧ WatchStackLayout st_n.core ∧
    (WatchesInv F_cur st0.core → WatchesInv F_cur st_n.core) ∧
    (skip_lit < 2 * st0.core.cur_vars →
      ∀ off q p end_v, SplitWatchesInv F_cur st0.core skip_lit off q p end_v →
        let off' := fullWatchOffCore st_n.core skip_lit
        SplitWatchesInv F_cur st_n.core skip_lit off'
          (off' + (q - off)) (off' + (p - off)) (off' + (end_v - off))) := by
  obtain ⟨hlen_k, hlay_k, h_off_ne, hpres_o, hsz_k, hpre_k, hw0_k, hw1_k⟩ :=
    fid_repl_empty_layout hlay hlen.core_ok hrw_lt hw_pos hrsz0 hfit2 how_f hcr_lt_st
  let st_n : FullState :=
    { st with
        core :=
          { st.core with
              wstk := (st.core.wstk.set st.core.wlen ow_v).set (st.core.wlen + 1) cr_v
              wvec := (st.core.wvec.set (2 * rw_v.toNat)
                (BitVec.ofNat 32 st.core.wlen)).set (2 * rw_v.toNat + 1) 2#32
              wlen := st.core.wlen + 2 } }
  have hstep := s15_flush_step_preserves (_c := c) (F_cur := F_cur) (k := st.core)
    (k' := st_n.core) (lit := rw_v.toNat) (w0 := ow_v) (cref := cr_v) (skip_lit := skip_lit)
    rfl (fun _ h => h) hrw_lt hrw_ne how_f hcr_lt_st hcr_ref_st h_off_ne hpres_o
    ⟨hsz_k, hpre_k, hw0_k, hw1_k⟩ hlay_k
  refine ⟨by dsimp [st_n]; rw [hcore_eq], hsc_eq,
    ⟨hlen_k, hlen.scratch_ok⟩, hlay_k, fun hw0 => hstep.1 (hwat_pres hw0), ?_⟩
  intro hsk off q p end_v hsw0
  have hsw1 := hsw_pres hsk off q p end_v hsw0
  have hsw2 := hstep.2 (hcv_eq ▸ hsk)
    (fullWatchOffCore st.core skip_lit)
    (fullWatchOffCore st.core skip_lit + (q - off))
    (fullWatchOffCore st.core skip_lit + (p - off))
    (fullWatchOffCore st.core skip_lit + (end_v - off)) hsw1
  simpa only [Nat.add_sub_cancel_left] using hsw2

private theorem p0_slow_case2b_fin {c : FullCfg} {F_cur : List (List Nat)}
    {st0 st : FullState} {skip_lit : Nat}
    {rw_v ow_v cr_v : BitVec 32} {sz0 : Nat}
    (hsz0 : sz0 = fullWatchSizeCore st.core rw_v.toNat)
    (hlay : WatchStackLayout st.core) (hlen : st.LengthsOk c)
    (hrw_lt : rw_v.toNat < 2 * st.core.cur_vars)
    (hrsz_pos : 0 < fullWatchSizeCore st.core rw_v.toNat)
    (hend_wlen : fullWatchOffCore st.core rw_v.toNat + sz0 = st.core.wlen)
    (hfit2 : st.core.wlen + 2 ≤ c.wcap) (how_f : (ow_v &&& 0x80000000#32) = 0#32)
    (hcr_lt_st : cr_v.toNat < 0x80000000)
    (hcr_ref_st : cr_v.toNat ∈ fullArenaClauseRefsCore st.core)
    (hrw_ne : rw_v.toNat ≠ skip_lit) (hcv_eq : st.core.cur_vars = st0.core.cur_vars)
    (hcore_eq : st.core =
      { st0.core with
          wvec := st.core.wvec, wstk := st.core.wstk,
          wlen := st.core.wlen, wusable := st.core.wusable })
    (hsc_eq : st.scratch = { st0.scratch with wsort := st.scratch.wsort })
    (hwat_pres : WatchesInv F_cur st0.core → WatchesInv F_cur st.core)
    (hsw_pres : skip_lit < 2 * st0.core.cur_vars →
      ∀ off q p end_v, SplitWatchesInv F_cur st0.core skip_lit off q p end_v →
        let off' := fullWatchOffCore st.core skip_lit
        SplitWatchesInv F_cur st.core skip_lit off'
          (off' + (q - off)) (off' + (p - off)) (off' + (end_v - off))) :
    let st_n : FullState :=
      { st with
          core :=
            { st.core with
                wstk := (st.core.wstk.set st.core.wlen ow_v).set (st.core.wlen + 1) cr_v
                wvec := st.core.wvec.set (2 * rw_v.toNat + 1) (BitVec.ofNat 32 (sz0 + 2))
                wlen := st.core.wlen + 2 } }
    st_n.core =
      { st0.core with
          wvec := st_n.core.wvec, wstk := st_n.core.wstk,
          wlen := st_n.core.wlen, wusable := st_n.core.wusable } ∧
    st_n.scratch = { st0.scratch with wsort := st_n.scratch.wsort } ∧
    st_n.LengthsOk c ∧ WatchStackLayout st_n.core ∧
    (WatchesInv F_cur st0.core → WatchesInv F_cur st_n.core) ∧
    (skip_lit < 2 * st0.core.cur_vars →
      ∀ off q p end_v, SplitWatchesInv F_cur st0.core skip_lit off q p end_v →
        let off' := fullWatchOffCore st_n.core skip_lit
        SplitWatchesInv F_cur st_n.core skip_lit off'
          (off' + (q - off)) (off' + (p - off)) (off' + (end_v - off))) := by
  subst hsz0
  obtain ⟨hlen_k, hlay_k, h_off_ne, hpres_o, hsz_k, hpre_k, hw0_k, hw1_k⟩ :=
    s15_append_end_layout hlay hlen.core_ok hrw_lt hrsz_pos hend_wlen hfit2 how_f hcr_lt_st
  let st_n : FullState :=
    { st with
        core :=
          { st.core with
              wstk := (st.core.wstk.set st.core.wlen ow_v).set (st.core.wlen + 1) cr_v
              wvec := st.core.wvec.set (2 * rw_v.toNat + 1)
                (BitVec.ofNat 32 (fullWatchSizeCore st.core rw_v.toNat + 2))
              wlen := st.core.wlen + 2 } }
  have hstep := s15_flush_step_preserves (_c := c) (F_cur := F_cur) (k := st.core)
    (k' := st_n.core) (lit := rw_v.toNat) (w0 := ow_v) (cref := cr_v) (skip_lit := skip_lit)
    rfl (fun _ h => h) hrw_lt hrw_ne how_f hcr_lt_st hcr_ref_st
    (by simpa only [st_n, hend_wlen] using h_off_ne)
    (by simpa only [st_n, hend_wlen] using hpres_o)
    ⟨by simpa only [st_n, hend_wlen] using hsz_k,
     by simpa only [st_n, hend_wlen] using hpre_k,
     by simpa only [st_n, hend_wlen] using hw0_k,
     by simpa only [st_n, hend_wlen] using hw1_k⟩
    (by simpa only [st_n, hend_wlen] using hlay_k)
  refine ⟨by dsimp [st_n]; rw [hcore_eq], hsc_eq,
    ⟨by simpa only [st_n, hend_wlen] using hlen_k, hlen.scratch_ok⟩,
    by simpa only [st_n, hend_wlen] using hlay_k, fun hw0 => hstep.1 (hwat_pres hw0), ?_⟩
  intro hsk off q p end_v hsw0
  have hsw1 := hsw_pres hsk off q p end_v hsw0
  have hsw2 := hstep.2 (hcv_eq ▸ hsk)
    (fullWatchOffCore st.core skip_lit)
    (fullWatchOffCore st.core skip_lit + (q - off))
    (fullWatchOffCore st.core skip_lit + (p - off))
    (fullWatchOffCore st.core skip_lit + (end_v - off)) hsw1
  simpa only [Nat.add_sub_cancel_left] using hsw2

private theorem p0_slow_delayed_entry {c : FullCfg} {st0 st : FullState}
    {j_v : BitVec 64} {idx dlen skip_lit : Nat}
    (hdelc : c.delayed_cap < dimacsBound)
    (hdel_len : st.scratch.delayed.length = 3 * c.delayed_cap)
    (hj_eq : j_v.toNat = 3 * idx) (hidx_lt : idx < dlen) (hdlen_le : dlen ≤ c.delayed_cap)
    (hdel_eq : st.scratch.delayed = st0.scratch.delayed)
    (hcv_eq : st.core.cur_vars = st0.core.cur_vars)
    (href_eq : fullArenaClauseRefsCore st.core = fullArenaClauseRefsCore st0.core)
    (hdel0 : DelayedWatchesOk st0.core st0.scratch.delayed dlen skip_lit) :
    let rw_v := st.scratch.delayed[j_v.toNat]'(by omega)
    let ow_v := st.scratch.delayed[(j_v + 1#64).toNat]'(by
      have := hdelc; unfold dimacsBound at this
      rw [BitVec.toNat_add, hj_eq, show (1#64 : BitVec 64).toNat = 1 from rfl,
        Nat.mod_eq_of_lt (by omega)]; omega)
    let cr_v := st.scratch.delayed[(j_v + 2#64).toNat]'(by
      have := hdelc; unfold dimacsBound at this
      rw [BitVec.toNat_add, hj_eq, show (2#64 : BitVec 64).toNat = 2 from rfl,
        Nat.mod_eq_of_lt (by omega)]; omega)
    3 * idx + 2 < st.scratch.delayed.length ∧
    (j_v + 1#64).toNat = 3 * idx + 1 ∧
    (j_v + 2#64).toNat = 3 * idx + 2 ∧
    (j_v + 3#64).toNat = 3 * (idx + 1) ∧
    rw_v.toNat < 2 * st.core.cur_vars ∧
    rw_v.toNat ≠ skip_lit ∧
    (ow_v &&& 0x80000000#32) = 0#32 ∧
    cr_v.toNat < 0x80000000 ∧
    cr_v.toNat ∈ fullArenaClauseRefsCore st.core ∧
    ow_v ≠ 0xFFFFFFFF#32 ∧
    cr_v ≠ 0xFFFFFFFF#32 ∧
    (rw_v.setWidth 64 <<< (1 : Nat)).toNat = 2 * rw_v.toNat ∧
    ((rw_v.setWidth 64 <<< (1 : Nat)) + 1#64).toNat = 2 * rw_v.toNat + 1 := by
  have hdelc' := hdelc; unfold dimacsBound at hdelc'
  have h3i_lt : 3 * idx + 2 < st.scratch.delayed.length := by omega
  have hj1_nat : (j_v + 1#64).toNat = 3 * idx + 1 := by
    rw [BitVec.toNat_add, hj_eq]; change (3 * idx + 1) % 2 ^ 64 = 3 * idx + 1
    exact Nat.mod_eq_of_lt (by omega)
  have hj2_nat : (j_v + 2#64).toNat = 3 * idx + 2 := by
    rw [BitVec.toNat_add, hj_eq]; change (3 * idx + 2) % 2 ^ 64 = 3 * idx + 2
    exact Nat.mod_eq_of_lt (by omega)
  have hj3_nat : (j_v + 3#64).toNat = 3 * (idx + 1) := by
    rw [BitVec.toNat_add, hj_eq]; change (3 * idx + 3) % 2 ^ 64 = 3 * (idx + 1)
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  obtain ⟨hrlit_lt, hrlit_ne, hrw0_f, hrcr_lt, hrcr_ref⟩ := hdel0 idx hidx_lt
  let rw_v := st.scratch.delayed[j_v.toNat]'(by omega)
  let ow_v := st.scratch.delayed[(j_v + 1#64).toNat]'(by rw [hj1_nat]; omega)
  let cr_v := st.scratch.delayed[(j_v + 2#64).toNat]'(by rw [hj2_nat]; omega)
  have hrlit_get : rw_v = st0.scratch.delayed[3 * idx]?.getD 0#32 := by
    dsimp only [rw_v]; rw [← hdel_eq, List.getElem?_eq_getElem (by omega), Option.getD_some]
    simp only [hj_eq]
  have hrw0_get : ow_v = st0.scratch.delayed[3 * idx + 1]?.getD 0#32 := by
    dsimp only [ow_v]; rw [← hdel_eq, List.getElem?_eq_getElem (by omega), Option.getD_some]
    simp only [hj1_nat]
  have hrcr_get : cr_v = st0.scratch.delayed[3 * idx + 2]?.getD 0#32 := by
    dsimp only [cr_v]; rw [← hdel_eq, List.getElem?_eq_getElem (by omega), Option.getD_some]
    simp only [hj2_nat]
  have hrw_lt : rw_v.toNat < 2 * st.core.cur_vars := by
    rw [hrlit_get, hcv_eq]; exact hrlit_lt
  have hrw_ne : rw_v.toNat ≠ skip_lit := by rw [hrlit_get]; exact hrlit_ne
  have how_f : (ow_v &&& 0x80000000#32) = 0#32 := by rw [hrw0_get]; exact hrw0_f
  have hcr_lt_st : cr_v.toNat < 0x80000000 := by rw [hrcr_get]; exact hrcr_lt
  have hcr_ref_st : cr_v.toNat ∈ fullArenaClauseRefsCore st.core := by
    rw [hrcr_get, href_eq]; exact hrcr_ref
  have how_ne : ow_v ≠ 0xFFFFFFFF#32 := fun heq => by
    rw [heq] at how_f; exact absurd how_f (by decide)
  have hcr_ne : cr_v ≠ 0xFFFFFFFF#32 := fun heq => by
    rw [heq] at hcr_lt_st; revert hcr_lt_st; decide
  have hrw64_nat : (rw_v.setWidth 64 <<< (1 : Nat)).toNat = 2 * rw_v.toNat := by
    rw [BitVec.toNat_shiftLeft, zext_toNat _ (by decide)]; simp [Nat.shiftLeft_eq]; omega
  have hrw64p1_nat :
      ((rw_v.setWidth 64 <<< (1 : Nat)) + 1#64).toNat = 2 * rw_v.toNat + 1 := by
    rw [BitVec.toNat_add, hrw64_nat]; change (2 * rw_v.toNat + 1) % 2 ^ 64 = _
    exact Nat.mod_eq_of_lt (by omega)
  exact ⟨h3i_lt, hj1_nat, hj2_nat, hj3_nat, hrw_lt, hrw_ne, how_f, hcr_lt_st, hcr_ref_st,
    how_ne, hcr_ne, hrw64_nat, hrw64p1_nat⟩

private theorem p0_slow_push_fin {c : FullCfg} {F_cur : List (List Nat)}
    {st0 st : FullState} {R : Mem 64 → Prop} {skip_lit : Nat} {rw_v ow_v cr_v : BitVec 32}
    {wvec' wstk' wsort' : List (BitVec 32)} {wlen' : Nat} {wu' : BitVec 64} {mp : Mem 64}
    (hcore_eq : st.core =
      { st0.core with wvec := st.core.wvec, wstk := st.core.wstk,
                      wlen := st.core.wlen, wusable := st.core.wusable })
    (hsc_eq : st.scratch = { st0.scratch with wsort := st.scratch.wsort })
    (hwat_pres : WatchesInv F_cur st0.core → WatchesInv F_cur st.core)
    (hsw_pres : skip_lit < 2 * st0.core.cur_vars →
      ∀ off q p end_v, SplitWatchesInv F_cur st0.core skip_lit off q p end_v →
        let off' := fullWatchOffCore st.core skip_lit
        SplitWatchesInv F_cur st.core skip_lit off'
          (off' + (q - off)) (off' + (p - off)) (off' + (end_v - off)))
    (hlen_p : ({ st with
        core := { st.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' }
        scratch := { st.scratch with wsort := wsort' } } : FullState).LengthsOk c)
    (hlay_p : WatchStackLayout { st.core with
        wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' })
    (hmp : (FullMem c { st with
        core := { st.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' }
        scratch := { st.scratch with wsort := wsort' } } ⋆ R) mp) :
    let st_p : FullState :=
      { st0 with
        core := { st0.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' }
        scratch := { st0.scratch with wsort := wsort' } }
    st_p.core = { st0.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' } ∧
    st_p.scratch = { st0.scratch with wsort := wsort' } ∧
    st_p.LengthsOk c ∧ WatchStackLayout st_p.core ∧
    (FullMem c st_p ⋆ R) mp ∧
    (∀ (_hrw_lt : rw_v.toNat < 2 * st.core.cur_vars) (_hrw_ne : rw_v.toNat ≠ skip_lit)
       (_how_f : (ow_v &&& 0x80000000#32) = 0#32) (_hcr_lt_st : cr_v.toNat < 0x80000000)
       (_hcr_ref_st : cr_v.toNat ∈ fullArenaClauseRefsCore st.core)
       (_hpres_o : ∀ l < 2 * st.core.cur_vars, l ≠ rw_v.toNat →
         fullWatchSize st_p l = fullWatchSize st l ∧
         ∀ idx < fullWatchSize st l,
           wstk'[fullWatchOff st_p l + idx]? = st.core.wstk[fullWatchOff st l + idx]?)
       (_hsz_p : fullWatchSize st_p rw_v.toNat = fullWatchSize st rw_v.toNat + 2)
       (_hpre_p : ∀ idx < fullWatchSize st rw_v.toNat,
         wstk'[fullWatchOff st_p rw_v.toNat + idx]? =
           st.core.wstk[fullWatchOff st rw_v.toNat + idx]?)
       (_hw0_p : wstk'[fullWatchOff st_p rw_v.toNat + fullWatchSize st rw_v.toNat]? = some ow_v)
       (_hw1_p : wstk'[fullWatchOff st_p rw_v.toNat + fullWatchSize st rw_v.toNat + 1]? =
         some cr_v),
       (WatchesInv F_cur st0.core → WatchesInv F_cur st_p.core) ∧
       (skip_lit < 2 * st0.core.cur_vars →
         ∀ off q p end_v, SplitWatchesInv F_cur st0.core skip_lit off q p end_v →
           let off' := fullWatchOffCore st_p.core skip_lit
           SplitWatchesInv F_cur st_p.core skip_lit off'
             (off' + (q - off)) (off' + (p - off)) (off' + (end_v - off)))) := by
  have hst_eq : st = { st0 with core := st.core, scratch := st.scratch } := by
    cases st; rfl
  have hst_p_eq :
      ({ st with
          core := { st.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' }
          scratch := { st.scratch with wsort := wsort' } } : FullState) =
      { st0 with
        core := { st0.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' }
        scratch := { st0.scratch with wsort := wsort' } } := by
    rw [hst_eq, hcore_eq, hsc_eq]
  have hcore_eq_p :
      ({ st.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' } :
        FullCoreState) =
      { st0.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' } := by
    rw [hcore_eq]
  rw [hst_p_eq] at hlen_p hmp
  rw [hcore_eq_p] at hlay_p
  refine ⟨rfl, rfl, hlen_p, hlay_p, hmp, ?_⟩
  intro hrw_lt hrw_ne how_f hcr_lt_st hcr_ref_st hpres_o hsz_p hpre_p hw0_p hw1_p
  have hcv_eq : st.core.cur_vars = st0.core.cur_vars := by rw [hcore_eq]
  have href_eq : fullArenaClauseRefsCore { st0.core with
      wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' } =
      fullArenaClauseRefsCore st.core := by
    unfold fullArenaClauseRefsCore; rw [hcore_eq]
  have hstep := p0_flush_true_preserves (F_cur := F_cur) (k := st.core)
    (k' := { st0.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' })
    (skip_lit := skip_lit) (lit := rw_v) (w0 := ow_v) (cref := cr_v)
    (by rw [hcore_eq]) (fun r hr => by rw [href_eq]; exact hr)
    hlay_p hrw_lt hrw_ne how_f hcr_lt_st (by rw [href_eq]; exact hcr_ref_st)
    (by simpa [hcore_eq_p, fullWatchSize, fullWatchOff] using hpres_o)
    ⟨by simpa [hcore_eq_p, fullWatchSize] using hsz_p,
     by simpa [hcore_eq_p, fullWatchSize, fullWatchOff] using hpre_p,
     by simpa [hcore_eq_p, fullWatchSize, fullWatchOff] using hw0_p,
     by simpa [hcore_eq_p, fullWatchSize, fullWatchOff] using hw1_p⟩
  refine ⟨fun hw0 => hstep.1 (hwat_pres hw0), fun hsk off q p end_v hsw0 => ?_⟩
  have hsw1 := hsw_pres hsk off q p end_v hsw0
  have hsw2 := hstep.2 (hcv_eq ▸ hsk)
    (fullWatchOffCore st.core skip_lit)
    (fullWatchOffCore st.core skip_lit + (q - off))
    (fullWatchOffCore st.core skip_lit + (p - off))
    (fullWatchOffCore st.core skip_lit + (end_v - off)) hsw1
  simpa only [Nat.add_sub_cancel_left] using hsw2

/-! ## 3. `full_prop_flush_slow_fid_wp` (`fidPropFlushSlowSpec`) -/

theorem full_prop_flush_slow_fid_wp (Γ : Env)
    (hPush : Γ.Has "full_watch_push" fullWatchPushSpec) :
    ∀ a m Q X, fidPropFlushSlowSpec a m Q X → Func.wp Γ full_prop_flush_slow_fid_body a m Q X := by
  rintro ⟨h, j0, di, ⟨⟩⟩ m0 Q X
    ⟨c, F_cur, st0, R, idx0, dlen, skip_lit, rfl, hlen0, hlay0, hj0_eq, hdi_eq, hidx0_lt,
     hdlen_le, hdel0, hm0, hQ⟩
  have hdelc : c.delayed_cap < dimacsBound := c.hdel
  have hwc : c.wcap < 2 * dimacsBound := c.hwcap
  have hmaxv : c.max_vars < 2 * dimacsBound := c.hmaxv
  unfold dimacsBound at hdelc hwc hmaxv
  have hdel_len0 := hlen0.scratch_ok.delayed_len_arr
  obtain ⟨h3i0_lt, hj0_1, hj0_2, hj0_3, hrlit0_lt, hrlit0_ne, how0_f, hcr0_lt, hcr0_ref,
    how0_ne, hcr0_ne, _, _⟩ :=
    p0_slow_delayed_entry hdelc hdel_len0 hj0_eq hidx0_lt hdlen_le rfl rfl rfl hdel0
  let rw0 := st0.scratch.delayed[j0.toNat]'(by omega)
  let ow0 := st0.scratch.delayed[(j0 + 1#64).toNat]'(by rw [hj0_1]; omega)
  let cr0 := st0.scratch.delayed[(j0 + 2#64).toNat]'(by rw [hj0_2]; omega)
  unfold Func.wp full_prop_flush_slow_fid_body
  c0_hsteps_nogrp
  refine LeanQbe.T.wp_call_of_spec _ _ (hPush _ _ _ _ ?_)
  refine ⟨c, st0, R, rfl, hlen0, hlay0, fun h => absurd h (by decide),
    fun _ => ⟨how0_ne, hcr0_ne⟩, hm0,
    fun pok0 wvec1 wstk1 wlen1 wu1 wsort1 mp0 hlen1 hlay1 hpres_o0 hpok0_t hpok0_f hmp0 => ?_⟩
  let st1 : FullState :=
    { st0 with
      core := { st0.core with wvec := wvec1, wstk := wstk1, wlen := wlen1, wusable := wu1 }
      scratch := { st0.scratch with wsort := wsort1 } }
  c0_hsteps_nogrp
  · have hpok0_eq : pok0 = true := by assumption
    have ⟨_, _, hsz1, hpre1, hw0_1, hw1_1⟩ := hpok0_t hpok0_eq
    have hstep0 := p0_flush_true_preserves (F_cur := F_cur) (k := st0.core) (k' := st1.core)
      (skip_lit := skip_lit) (lit := rw0) (w0 := ow0) (cref := cr0)
      rfl (fun _ h => h) hlay1 hrlit0_lt hrlit0_ne how0_f hcr0_lt hcr0_ref
      (by simpa [st1, fullWatchSize, fullWatchOff] using hpres_o0)
      ⟨by simpa [st1, fullWatchSize] using hsz1,
       by simpa [st1, fullWatchSize, fullWatchOff] using hpre1,
       by
         dsimp only [st1, rw0, ow0]
         exact hw0_1.trans (congrArg some (p0_getElem_idx (by rw [BitVec.toNat_add]; rfl) _ _)),
       by
         dsimp only [st1, rw0, cr0]
         exact (hw1_1 rfl).trans
           (congrArg some (p0_getElem_idx (by rw [BitVec.toNat_add]; rfl) _ _))⟩
    c0_hsteps_nogrp
    refine wp_loop_inv (ts := [i64, i64])
      (fun (j_v, wstk_v, ()) mj => ∃ (st : FullState) (idx : Nat),
        j_v.toNat = 3 * idx ∧ idx ≤ dlen ∧ wstk_v = c.pWstk ∧
        st.core = { st0.core with
          wvec := st.core.wvec, wstk := st.core.wstk,
          wlen := st.core.wlen, wusable := st.core.wusable } ∧
        st.scratch = { st0.scratch with wsort := st.scratch.wsort } ∧
        st.LengthsOk c ∧ WatchStackLayout st.core ∧
        (WatchesInv F_cur st0.core → WatchesInv F_cur st.core) ∧
        (skip_lit < 2 * st0.core.cur_vars →
          ∀ off q p end_v, SplitWatchesInv F_cur st0.core skip_lit off q p end_v →
            let off' := fullWatchOffCore st.core skip_lit
            SplitWatchesInv F_cur st.core skip_lit off'
              (off' + (q - off)) (off' + (p - off)) (off' + (end_v - off))) ∧
        (FullMem c st ⋆ R) mj)
      (fun (j_v, _, ()) _ => 3 * dlen - j_v.toNat) ?_ ?_
    · intro Jl hJl
      refine hJl (j0 + 3#64, c.pWstk, ()) mp0
        ⟨st1, idx0 + 1, hj0_3, hidx0_lt, rfl, rfl, rfl, hlen1, hlay1, hstep0.1, ?_, hmp0⟩
      intro hsk off q p end_v hsw0
      exact hstep0.2 hsk off q p end_v hsw0
    · rintro Jl ⟨j_v, wstk_v, ⟨⟩⟩ mj ⟨st, idx, hj_eq, hidx_le, hwv_p, hcore_eq, hsc_eq,
        hlen, hlay, hwat_pres, hsw_pres, hmj⟩ hJl
      subst hwv_p
      clear hstep0 hpok0_t hpok0_f hpres_o0 hm0 hmp0 hlay1 hlen1 hlay0 hlen0
      have hdel_len := hlen.scratch_ok.delayed_len_arr
      have hcv_le := hlen.core_ok.cur_vars_le
      have hwv_len := hlen.core_ok.wvec_len
      have hws_len := hlen.core_ok.wstk_len_arr
      have hwlen_le := hlen.core_ok.wlen_le
      have hcv_eq : st.core.cur_vars = st0.core.cur_vars := by rw [hcore_eq]
      have har_eq : st.core.arena = st0.core.arena := by rw [hcore_eq]
      have hal_eq : st.core.arena_len = st0.core.arena_len := by rw [hcore_eq]
      have href_eq : fullArenaClauseRefsCore st.core = fullArenaClauseRefsCore st0.core := by
        unfold fullArenaClauseRefsCore; rw [har_eq, hal_eq]
      have hdel_eq : st.scratch.delayed = st0.scratch.delayed := by rw [hsc_eq]
      dsimp only [Blocks.get_here, Blocks.get_there]
      c0_hsteps_nogrp
      · have hlt_j : j_v.toNat < di.toNat := hc
        have hidx_lt : idx < dlen := by omega
        obtain ⟨h3i_lt, hj1_nat, hj2_nat, hj3_nat, hrw_lt0, hrw_ne, how_f, hcr_lt_st,
          hcr_ref_st, how_ne, hcr_ne, hrw64_0, hrw64p1_0⟩ :=
          p0_slow_delayed_entry hdelc hdel_len hj_eq hidx_lt hdlen_le hdel_eq hcv_eq href_eq hdel0
        let rw_v := st.scratch.delayed[j_v.toNat]'(by omega)
        let ow_v := st.scratch.delayed[(j_v + 1#64).toNat]'(by rw [hj1_nat]; omega)
        let cr_v := st.scratch.delayed[(j_v + 2#64).toNat]'(by rw [hj2_nat]; omega)
        have hrw_lt : rw_v.toNat < 2 * st.core.cur_vars := hrw_lt0
        have hrw64_nat : (rw_v.setWidth 64 <<< (1 : Nat)).toNat = 2 * rw_v.toNat := hrw64_0
        have hrw64p1_nat :
            ((rw_v.setWidth 64 <<< (1 : Nat)) + 1#64).toNat = 2 * rw_v.toNat + 1 := hrw64p1_0
        have hwv_i0 : (rw_v.setWidth 64 <<< (1 : Nat)).toNat < st.core.wvec.length := by
          rw [hwv_len, hrw64_nat]; omega
        have hwv_i1 : ((rw_v.setWidth 64 <<< (1 : Nat)) + 1#64).toNat < st.core.wvec.length := by
          rw [hwv_len, hrw64p1_nat]; omega
        let roff_w := st.core.wvec[(rw_v.setWidth 64 <<< (1 : Nat)).toNat]'hwv_i0
        let rsz_w := st.core.wvec[((rw_v.setWidth 64 <<< (1 : Nat)) + 1#64).toNat]'hwv_i1
        have hroff_eq : (roff_w.setWidth 64).toNat = fullWatchOffCore st.core rw_v.toNat := by
          rw [zext_toNat _ (by decide)]; unfold fullWatchOffCore
          rw [List.getElem?_eq_getElem (by rw [hwv_len]; omega), Option.getD_some]
          exact congrArg BitVec.toNat (by dsimp only [roff_w]; exact p0_getElem_idx hrw64_nat _ _)
        have hrsz_eq : (rsz_w.setWidth 64).toNat = fullWatchSizeCore st.core rw_v.toNat := by
          rw [zext_toNat _ (by decide)]; unfold fullWatchSizeCore
          rw [List.getElem?_eq_getElem (by rw [hwv_len]; omega), Option.getD_some]
          exact congrArg BitVec.toNat
            (by dsimp only [rsz_w]; exact p0_getElem_idx hrw64p1_nat _ _)
        have hbd_rw := hlay.bounds rw_v.toNat hrw_lt
        have hrend_nat : (roff_w.setWidth 64 + rsz_w.setWidth 64).toNat =
            fullWatchOffCore st.core rw_v.toNat + fullWatchSizeCore st.core rw_v.toNat := by
          rw [BitVec.toNat_add, hroff_eq, hrsz_eq, Nat.mod_eq_of_lt (by omega)]
        have hrend1_nat : (roff_w.setWidth 64 + rsz_w.setWidth 64 + 1#64).toNat =
            fullWatchOffCore st.core rw_v.toNat + fullWatchSizeCore st.core rw_v.toNat + 1 := by
          rw [BitVec.toNat_add, hrend_nat]; change (_ + 1) % 2 ^ 64 = _
          exact Nat.mod_eq_of_lt (by omega)
        have hwl_nat : (BitVec.ofNat 64 st.core.wlen).toNat = st.core.wlen :=
          p0_bv64_ofNat (by omega)
        have hrv_w0 : st.core.wvec[2 * st.scratch.delayed[j_v.toNat].toNat % 2 ^ 64]'(by
            change 2 * rw_v.toNat % 2 ^ 64 < st.core.wvec.length
            rw [hwv_len, Nat.mod_eq_of_lt (by omega : 2 * rw_v.toNat < 2 ^ 64)]; omega) =
            roff_w := by
          dsimp only [roff_w]
          exact p0_getElem_idx
            ((Nat.mod_eq_of_lt (by omega : 2 * rw_v.toNat < 2 ^ 64)).trans hrw64_nat.symm) _ _
        have hrv_w1 : st.core.wvec[(2 * st.scratch.delayed[j_v.toNat].toNat + 1) % 2 ^ 64]'(by
            change (2 * rw_v.toNat + 1) % 2 ^ 64 < st.core.wvec.length
            rw [hwv_len, Nat.mod_eq_of_lt (by omega : 2 * rw_v.toNat + 1 < 2 ^ 64)]; omega) =
            rsz_w := by
          dsimp only [rsz_w]
          exact p0_getElem_idx
            ((Nat.mod_eq_of_lt (by omega : 2 * rw_v.toNat + 1 < 2 ^ 64)).trans hrw64p1_nat.symm)
            _ _
        have hroff_t : roff_w.toNat = fullWatchOffCore st.core rw_v.toNat := by
          rw [← hroff_eq, zext_toNat _ (by decide)]
        have hrsz_t : rsz_w.toNat = fullWatchSizeCore st.core rw_v.toNat := by
          rw [← hrsz_eq, zext_toNat _ (by decide)]
        have hmod_2rw : 2 * st.scratch.delayed[j_v.toNat].toNat % 2 ^ 64 = 2 * rw_v.toNat :=
          Nat.mod_eq_of_lt (by omega)
        have hmod_2rw1 : (2 * st.scratch.delayed[j_v.toNat].toNat + 1) % 2 ^ 64 =
            2 * rw_v.toNat + 1 := Nat.mod_eq_of_lt (by omega)
        have hmod_2rw1_rv : (2 * rw_v.toNat + 1) % 2 ^ 64 = 2 * rw_v.toNat + 1 :=
          Nat.mod_eq_of_lt (by omega)
        have hrv_w0_raw : st.core.wvec[2 * rw_v.toNat]'(by rw [hwv_len]; omega) = roff_w := by
          simpa only [hmod_2rw] using hrv_w0
        have hrv_w1_raw : st.core.wvec[2 * rw_v.toNat + 1]'(by rw [hwv_len]; omega) = rsz_w := by
          simpa only [hmod_2rw1] using hrv_w1
        c0_hsteps_nogrp
        refine wp_join_group (ts := [i64])
          (fun (wstk_n, ()) mn => ∃ (st_n : FullState),
            wstk_n = c.pWstk ∧
            st_n.core = { st0.core with
              wvec := st_n.core.wvec, wstk := st_n.core.wstk,
              wlen := st_n.core.wlen, wusable := st_n.core.wusable } ∧
            st_n.scratch = { st0.scratch with wsort := st_n.scratch.wsort } ∧
            st_n.LengthsOk c ∧ WatchStackLayout st_n.core ∧
            (WatchesInv F_cur st0.core → WatchesInv F_cur st_n.core) ∧
            (skip_lit < 2 * st0.core.cur_vars →
              ∀ off q p end_v, SplitWatchesInv F_cur st0.core skip_lit off q p end_v →
                let off' := fullWatchOffCore st_n.core skip_lit
                SplitWatchesInv F_cur st_n.core skip_lit off'
                  (off' + (q - off)) (off' + (p - off)) (off' + (end_v - off))) ∧
            (FullMem c st_n ⋆ R) mn)
          (fun _ ⟨wstk_n, ⟨⟩⟩ mn ⟨st_n, hwvn, hcn, hscn, hln, hlyn, hwn, hswn, hmn⟩ => by
            c0_hsteps
            exact hJl (j_v + 3#64, wstk_n, ()) mn (by dsimp only; rw [hj_eq, hj3_nat]; omega)
              ⟨st_n, idx + 1, hj3_nat, by omega, hwvn, hcn, hscn, hln, hlyn, hwn, hswn, hmn⟩)
          ?_
        intro Jnext hJnext
        refine wp_join_group (ts := []) (fun _ m2 => (FullMem c st ⋆ R) m2)
          (fun _ ⟨⟩ m2 hm2 => by
            dsimp only [Blocks.get_here, Blocks.get_there]
            refine wp_join_group (ts := [i64])
              (fun p mn => wp Γ Q X (.jump Jnext (.var p.1, ())) mn)
              (fun _ p mn h => by try dsimp only [Blocks.get_here, Blocks.get_there]; exact h) ?_
            intro Jnext2 hJnext2
            refine wp_join_group (ts := []) (fun _ m3 => (FullMem c st ⋆ R) m3)
              (fun _ ⟨⟩ m3 hm3 => by
                dsimp only [Blocks.get_here, Blocks.get_there]
                refine wp_join_group (ts := [i64])
                  (fun p mn => wp Γ Q X (.jump Jnext2 (.var p.1, ())) mn)
                  (fun _ p mn h => by
                    try dsimp only [Blocks.get_here, Blocks.get_there]; exact h) ?_
                intro Jnext3 hJnext3
                refine wp_join_group (ts := []) (fun _ mc => (FullMem c st ⋆ R) mc)
                  (fun _ ⟨⟩ mc hmc => by
                    dsimp only [Blocks.get_here, Blocks.get_there]
                    c0_hsteps_nogrp
                    refine LeanQbe.T.wp_call_of_spec _ _ (hPush _ _ _ _ ?_)
                    refine ⟨c, st, R, rfl, hlen, hlay, fun h => absurd h (by decide),
                      fun _ => ⟨how_ne, hcr_ne⟩, hmc,
                      fun pok wvec' wstk' wlen' wu' wsort' mp hlen_p hlay_p hpres_o
                        hpok_t hpok_f hmp => ?_⟩
                    obtain ⟨hcore_p, hsc_p, hlen_p', hlay_p', hmp', htrue_p⟩ :=
                      p0_slow_push_fin hcore_eq hsc_eq hwat_pres hsw_pres hlen_p hlay_p hmp
                    let st_p : FullState :=
                      { st0 with
                        core := { st0.core with wvec := wvec', wstk := wstk',
                                                wlen := wlen', wusable := wu' }
                        scratch := { st0.scratch with wsort := wsort' } }
                    c0_hsteps_nogrp
                    · have hpok_eq : pok = true := by assumption
                      have ⟨_, _, hsz_p, hpre_p, hw0_p, hw1_p⟩ := hpok_t hpok_eq
                      obtain ⟨hw_fin, hsw_fin⟩ := htrue_p hrw_lt hrw_ne how_f hcr_lt_st hcr_ref_st
                        hpres_o hsz_p hpre_p hw0_p (hw1_p rfl)
                      exact hJnext (c.pWstk, ()) mp
                        ⟨st_p, rfl, hcore_p, hsc_p, hlen_p', hlay_p', hw_fin, hsw_fin, hmp'⟩
                    · have hpok_eq : pok = false := by
                        cases pok with
                        | false => rfl
                        | true => exact absurd (hc : _) (by decide)
                      have hcore_p' :
                          ({ st.core with
                              wvec := wvec', wstk := wstk',
                              wlen := wlen', wusable := wu' } : FullCoreState) = st_p.core := by
                        dsimp only [st_p]; rw [hcore_eq]
                      have hstep := p0_flush_false_preserves (F_cur := F_cur) (k := st.core)
                        (k' := st_p.core) (skip_lit := skip_lit) (lit := rw_v)
                        (by rw [hcore_eq]) (fun r hr => by
                          unfold fullArenaClauseRefsCore at hr ⊢; rw [hcore_eq] at hr; exact hr)
                        hlay_p' (by
                          dsimp only [st_p, rw_v] at hcore_p' ⊢; rw [← hcore_p']
                          simpa only [fullWatchSize, fullWatchOff, Arg.val_var] using hpres_o)
                        (fun h => by
                          dsimp only [st_p, rw_v] at hcore_p' ⊢; rw [← hcore_p']
                          simpa only [fullWatchSize, fullWatchOff, Arg.val_var] using
                            (hpok_f hpok_eq).1 h)
                      refine hQ false wvec' wstk' wlen' wu' wsort' mp hlen_p' hlay_p'
                        (fun hw0 => hstep.1 (hwat_pres hw0)) ?_ hmp'
                      intro hsk off q p end_v hsw0
                      have hsw1 := hsw_pres hsk off q p end_v hsw0
                      have hsw2 := hstep.2 (hcv_eq ▸ hsk)
                        (fullWatchOffCore st.core skip_lit)
                        (fullWatchOffCore st.core skip_lit + (q - off))
                        (fullWatchOffCore st.core skip_lit + (p - off))
                        (fullWatchOffCore st.core skip_lit + (end_v - off)) hsw1
                      simpa [Nat.add_sub_cancel_left] using hsw2) ?_
                intro Jc3 hJc3
                p0_hsplit
                · have hrsz0 : fullWatchSizeCore st.core rw_v.toNat = 0 := by
                    have h := congrArg BitVec.toNat (hc : _)
                    simp only [bv_c0] at h
                    rw [← hrsz_t]; simpa only [hrv_w1] using h
                  p0_hsplit
                  · have hw_pos : 1 ≤ st.core.wlen := by
                      have h := hc
                      rw [Nat.mod_eq_of_lt (by omega : st.core.wlen < 2 ^ 64)] at h; omega
                    p0_hsplit
                    · have hfit2 : st.core.wlen + 2 ≤ c.wcap := by
                        have h := hc
                        rw [Nat.mod_eq_of_lt (by omega : st.core.wlen + 2 < 2 ^ 64),
                          Nat.mod_eq_of_lt (by omega : c.wcap < 2 ^ 64)] at h; exact h
                      have hwv_set_lt : (rw_v.setWidth 64 <<< (1 : Nat) + 1).toNat <
                          (st.core.wvec.set (rw_v.setWidth 64 <<< (1 : Nat)).toNat
                            ((BitVec.ofNat 64 st.core.wlen).setWidth 32)).length := by
                        rw [List.length_set, hwv_len, show (1 : BitVec 64) = 1#64 from rfl,
                          hrw64p1_nat]; omega
                      c0_hsteps_nogrp
                      have hmod_wl1 : (st.core.wlen + 1) % 2 ^ 64 = st.core.wlen + 1 :=
                        Nat.mod_eq_of_lt (by omega)
                      have hmod_wl2 : (st.core.wlen + 2) % 2 ^ 64 = st.core.wlen + 2 :=
                        Nat.mod_eq_of_lt (by omega)
                      have htr32 :
                          (BitVec.ofNat 64 st.core.wlen).setWidth 32 =
                            BitVec.ofNat 32 st.core.wlen := by
                        apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_ofNat]
                      obtain ⟨hcn, hscn, hln, hlyn, hwn, hswn⟩ :=
                        p0_slow_case2a_fin hlay hlen hrw_lt hw_pos hrsz0 hfit2 how_f hcr_lt_st
                          hcr_ref_st hrw_ne hcv_eq hcore_eq hsc_eq hwat_pres hsw_pres
                      exact hJnext (c.pWstk, ()) m
                        ⟨_, rfl, hcn, hscn, hln, hlyn, hwn, hswn,
                          Eq.mp (congrArg (fun x => (FullMem c x ⋆ R) m) (by
                            dsimp only [ow_v, cr_v]; congr 1; congr 1 <;>
                              (try simp only [bv_c0, p0_bv64_1_toNat, p0_bv64_2_toNat, hmod_2rw,
                                hmod_2rw1_rv, hmod_wl1, hmod_wl2, hwl_nat, htr32]) <;> rfl)) hm⟩
                    · exact hJc3 () m3 hm3
                  · exact hJc3 () m3 hm3
                · exact hJc3 () m3 hm3) ?_
            intro Jc2 hJc2
            p0_hsplit
            · have hrsz_pos : 0 < fullWatchSizeCore st.core rw_v.toNat := by
                have h := hc; simp only [hrv_w1, hrsz_t] at h; exact h
              p0_hsplit
              · have hend_wlen : fullWatchOffCore st.core rw_v.toNat +
                    fullWatchSizeCore st.core rw_v.toNat = st.core.wlen := by
                  have h := congrArg BitVec.toNat (hc : _)
                  simp only [bv_c0, hmod_2rw, hmod_2rw1] at h
                  simpa only [hrv_w0_raw, hrv_w1_raw, hroff_t, hrsz_t, hwl_nat,
                    Nat.mod_eq_of_lt (by omega :
                      fullWatchOffCore st.core rw_v.toNat +
                        fullWatchSizeCore st.core rw_v.toNat < 2 ^ 64),
                    Nat.mod_eq_of_lt (by omega : st.core.wlen < 2 ^ 64)] using h
                p0_hsplit
                · have hfit2 : st.core.wlen + 2 ≤ c.wcap := by
                    have h := hc
                    rw [Nat.mod_eq_of_lt (by omega : st.core.wlen + 2 < 2 ^ 64),
                      Nat.mod_eq_of_lt (by omega : c.wcap < 2 ^ 64)] at h; exact h
                  c0_hsteps_nogrp
                  let sz0 := fullWatchSizeCore st.core rw_v.toNat
                  have hsz_bv :
                      (rsz_w.setWidth 64 + 2).setWidth 32 = BitVec.ofNat 32 (sz0 + 2) := by
                    apply BitVec.eq_of_toNat_eq
                    rw [show (2 : BitVec 64) = 2#64 from rfl, BitVec.toNat_setWidth,
                      BitVec.toNat_add, hrsz_eq, BitVec.toNat_ofNat]
                    change ((sz0 + 2) % 2 ^ 64) % 2 ^ 32 = (sz0 + 2) % 2 ^ 32
                    rw [Nat.mod_eq_of_lt (by omega : sz0 + 2 < 2 ^ 64)]
                  have hmod_wl1 : (st.core.wlen + 1) % 2 ^ 64 = st.core.wlen + 1 :=
                    Nat.mod_eq_of_lt (by omega)
                  have hmod_wl2 : (st.core.wlen + 2) % 2 ^ 64 = st.core.wlen + 2 :=
                    Nat.mod_eq_of_lt (by omega)
                  obtain ⟨hcn, hscn, hln, hlyn, hwn, hswn⟩ :=
                    p0_slow_case2b_fin rfl hlay hlen hrw_lt hrsz_pos hend_wlen hfit2 how_f
                      hcr_lt_st hcr_ref_st hrw_ne hcv_eq hcore_eq hsc_eq hwat_pres hsw_pres
                  exact hJnext (c.pWstk, ()) m
                    ⟨_, rfl, hcn, hscn, hln, hlyn, hwn, hswn,
                      Eq.mp (congrArg (fun x => (FullMem c x ⋆ R) m) (by
                        dsimp only [sz0, ow_v, cr_v]; congr 1; congr 1 <;>
                          (try simp only [bv_c0, p0_bv64_1_toNat, p0_bv64_2_toNat, hmod_2rw,
                            hmod_2rw1_rv, hmod_wl1, hmod_wl2, hrv_w1_raw, hwl_nat, hsz_bv]) <;>
                          rfl)) hm⟩
                · exact hJc2 () m2 hm2
              · exact hJc2 () m2 hm2
            · exact hJc2 () m2 hm2) ?_
        intro Jc1 hJc1
        p0_hsplit
        · have hrsz_pos : 0 < fullWatchSizeCore st.core rw_v.toNat := by
            have h := hc; simp only [hrv_w1, hrsz_t] at h; exact h
          p0_hsplit
          · have hend2_le : fullWatchOffCore st.core rw_v.toNat +
                fullWatchSizeCore st.core rw_v.toNat + 2 ≤ st.core.wlen := by
              have h := hc
              simp only [bv_c0, hmod_2rw, hmod_2rw1, hrv_w0_raw, hrv_w1_raw,
                hroff_t, hrsz_t] at h
              rw [Nat.mod_eq_of_lt (by omega :
                  fullWatchOffCore st.core rw_v.toNat + fullWatchSizeCore st.core rw_v.toNat + 2 <
                    2 ^ 64),
                Nat.mod_eq_of_lt (by omega : st.core.wlen < 2 ^ 64)] at h; exact h
            have hws_i0 : (roff_w.setWidth 64 + rsz_w.setWidth 64).toNat < st.core.wstk.length := by
              rw [hws_len, hrend_nat]; omega
            have hws_i1 : (roff_w.setWidth 64 + rsz_w.setWidth 64 + 1).toNat <
                st.core.wstk.length := by
              rw [hws_len, show (1 : BitVec 64) = 1#64 from rfl, hrend1_nat]; omega
            p0_hsplit
            · have hsent0 : st.core.wstk[fullWatchOffCore st.core rw_v.toNat +
                  fullWatchSizeCore st.core rw_v.toNat]? = some 0xFFFFFFFF#32 := by
                rw [List.getElem?_eq_getElem (by rw [hws_len]; omega)]
                refine congrArg some (Eq.trans ?_ hc)
                congr 1; simp only [hmod_2rw, hmod_2rw1, hrv_w0_raw, hrv_w1_raw, hroff_t, hrsz_t]
                rw [Nat.mod_eq_of_lt (by omega)]
              p0_hsplit
              · have hsent1 : st.core.wstk[fullWatchOffCore st.core rw_v.toNat +
                    fullWatchSizeCore st.core rw_v.toNat + 1]? = some 0xFFFFFFFF#32 := by
                  rw [List.getElem?_eq_getElem (by rw [hws_len]; omega)]
                  refine congrArg some (Eq.trans ?_ hc)
                  congr 1; simp only [hmod_2rw, hmod_2rw1, hrv_w0_raw, hrv_w1_raw, hroff_t, hrsz_t]
                  rw [Nat.mod_eq_of_lt (by omega)]
                c0_hsteps_nogrp
                refine wp_join_group (ts := []) (fun _ mf =>
                    wp Γ Q X (.jump Jnext (Arg.var c.pWstk, ())) mf)
                  (fun _ ⟨⟩ mf hmf => by
                    dsimp only [Blocks.get_here, Blocks.get_there] at *; exact hmf) ?_
                intro Jwu hJwu
                let sz0 := fullWatchSizeCore st.core rw_v.toNat
                let wend0 := fullWatchOffCore st.core rw_v.toNat + sz0
                have hsz_bv : (rsz_w.setWidth 64 + 2).setWidth 32 =
                    BitVec.ofNat 32 (sz0 + 2) := by
                  apply BitVec.eq_of_toNat_eq
                  rw [show (2 : BitVec 64) = 2#64 from rfl, BitVec.toNat_setWidth,
                    BitVec.toNat_add, hrsz_eq, BitVec.toNat_ofNat]
                  change ((sz0 + 2) % 2 ^ 64) % 2 ^ 32 = (sz0 + 2) % 2 ^ 32
                  rw [Nat.mod_eq_of_lt (by omega : sz0 + 2 < 2 ^ 64)]
                obtain ⟨st_c1, hst_c1, hm_c1⟩ : ∃ st_c1 : FullState,
                    st_c1 = { st with core := { st.core with
                      wstk := (st.core.wstk.set wend0 ow_v).set (wend0 + 1) cr_v
                      wvec := st.core.wvec.set (2 * rw_v.toNat + 1)
                        (BitVec.ofNat 32 (sz0 + 2)) } } ∧
                    (FullMem c st_c1 ⋆ R) m :=
                  ⟨_, rfl, Eq.mp (congrArg (fun x => (FullMem c x ⋆ R) m) (by
                    dsimp only [wend0, sz0, ow_v, cr_v]; congr 1; congr 1 <;>
                      simp only [bv_c0, p0_bv64_1_toNat, p0_bv64_2_toNat, hmod_2rw,
                        hmod_2rw1_rv, hrv_w0_raw, hrv_w1_raw, hroff_t, hrsz_t, hsz_bv,
                        Nat.mod_eq_of_lt (by omega :
                          fullWatchOffCore st.core rw_v.toNat +
                            fullWatchSizeCore st.core rw_v.toNat < 2 ^ 64),
                        Nat.mod_eq_of_lt (by omega :
                          fullWatchOffCore st.core rw_v.toNat +
                            fullWatchSizeCore st.core rw_v.toNat + 1 < 2 ^ 64)] <;> rfl)) hm⟩
                clear hm
                c0_hstep; p0_hsplit
                · c0_hstep; c0_hstep; c0_hstep
                  obtain ⟨hcn, hscn, hln, hlyn, hwn, hswn⟩ :=
                    p0_slow_case1_fin rfl rfl hlay hlen hrw_lt hrsz_pos hend2_le hsent0 hsent1
                      how_f hcr_lt_st hcr_ref_st hrw_ne hcv_eq hcore_eq hsc_eq hwat_pres hsw_pres
                  exact hJwu () _ (hJnext (c.pWstk, ()) _
                    ⟨_, rfl, hcn, hscn, hln, hlyn, hwn, hswn, by subst hst_c1; exact hm⟩)
                · obtain ⟨hcn, hscn, hln, hlyn, hwn, hswn⟩ :=
                    p0_slow_case1_fin rfl rfl hlay hlen hrw_lt hrsz_pos hend2_le hsent0 hsent1
                      how_f hcr_lt_st hcr_ref_st hrw_ne hcv_eq hcore_eq hsc_eq hwat_pres hsw_pres
                  exact hJwu () _ (hJnext (c.pWstk, ()) _
                    ⟨_, rfl, hcn, hscn, hln, hlyn, hwn, hswn, by subst hst_c1; exact hm_c1⟩)
              · exact hJc1 () mj hmj
            · exact hJc1 () mj hmj
          · exact hJc1 () mj hmj
        · exact hJc1 () mj hmj
      · c0_hsteps_nogrp
        have hst_eq : st =
            { st0 with
              core := { st0.core with
                wvec := st.core.wvec, wstk := st.core.wstk,
                wlen := st.core.wlen, wusable := st.core.wusable }
              scratch := { st0.scratch with wsort := st.scratch.wsort } } := by
          cases st; cases st0; simp only [FullState.mk.injEq] at *; exact ⟨hcore_eq, hsc_eq⟩
        exact hQ true st.core.wvec st.core.wstk st.core.wlen st.core.wusable st.scratch.wsort _
          (hst_eq ▸ hlen) (hcore_eq ▸ hlay) (fun hw0 => hcore_eq ▸ hwat_pres hw0)
          (fun hsk off q p end_v hsw0 => by
            have h1 := hsw_pres hsk off q p end_v hsw0
            simpa only [← hcore_eq] using h1)
          (hst_eq ▸ hmj)
  · have hpok0_eq : pok0 = false := by
      cases pok0 with
      | false => rfl
      | true => exact absurd (hc : _) (by decide)
    have hstep0 := p0_flush_false_preserves (F_cur := F_cur) (k := st0.core) (k' := st1.core)
      (skip_lit := skip_lit) (lit := rw0) rfl (fun _ h => h) hlay1
      hpres_o0 (hpok0_f hpok0_eq).1
    c0_hsteps_nogrp
    exact hQ false wvec1 wstk1 wlen1 wu1 wsort1 mp0 hlen1 hlay1 hstep0.1 hstep0.2 hmp0

/-! ## 4. `full_prop_flush_del_fid_wp` (`fidPropFlushDelSpec`) -/

theorem full_prop_flush_del_fid_wp (Γ : Env)
    (hSlow : Γ.Has "full_prop_flush_slow_fid" fidPropFlushSlowSpec) :
    ∀ a m Q X, fidPropFlushDelSpec a m Q X → Func.wp Γ full_prop_flush_del_fid_body a m Q X := by
  rintro ⟨h, di, ⟨⟩⟩ m0 Q X hs
  obtain ⟨c, F_cur, st0, R, dlen, skip_lit, rfl, hlen0, hlay0, hdi_eq, hdlen_le, hdel0, hm0, hQ⟩ :=
    hs
  have hdelc : c.delayed_cap < dimacsBound := c.hdel
  have hwc : c.wcap < 2 * dimacsBound := c.hwcap
  have hmaxv : c.max_vars < 2 * dimacsBound := c.hmaxv
  unfold dimacsBound at hdelc hwc hmaxv
  unfold Func.wp full_prop_flush_del_fid_body
  c0_hsteps_nogrp
  refine wp_loop_inv (ts := [i64, i64, i64])
    (fun (wlen_v, wu_v, j_v, ()) mj => ∃ (st : FullState) (wl_d : Nat) (wu_d : BitVec 64)
      (idx : Nat),
      wlen_v = BitVec.ofNat 64 st.core.wlen ∧ wu_v = st.core.wusable ∧
      j_v.toNat = 3 * idx ∧ idx ≤ dlen ∧
      st.core = { st0.core with
        wvec := st.core.wvec, wstk := st.core.wstk,
        wlen := st.core.wlen, wusable := st.core.wusable } ∧
      st.scratch = { st0.scratch with wsort := st.scratch.wsort } ∧
      st.LengthsOk c ∧ WatchStackLayout st.core ∧
      (WatchesInv F_cur st0.core → WatchesInv F_cur st.core) ∧
      (skip_lit < 2 * st0.core.cur_vars →
        ∀ off q p end_v, SplitWatchesInv F_cur st0.core skip_lit off q p end_v →
          let off' := fullWatchOffCore st.core skip_lit
          SplitWatchesInv F_cur st.core skip_lit off'
            (off' + (q - off)) (off' + (p - off)) (off' + (end_v - off))) ∧
      (FullMem c (p0FlushDisk wl_d wu_d st) ⋆ R) mj)
    (fun (_, _, j_v, ()) _ => 3 * dlen - j_v.toNat) ?_ ?_
  · intro Jl hJl
    c0_hsteps
    refine hJl (BitVec.ofNat 64 st0.core.wlen, st0.core.wusable, 0#64, ()) m0
      ⟨st0, st0.core.wlen, st0.core.wusable, 0, rfl, rfl, by decide, Nat.zero_le _,
       by cases st0.core; rfl, by cases st0.scratch; rfl, hlen0, hlay0, fun h => h, ?_,
       by simpa [p0FlushDisk] using hm0⟩
    intro _ off q p end_v hsw
    have hoff := hsw.off_eq
    have hq_ge := hsw.q_ge; have hq_le := hsw.q_le_p; have hp_le := hsw.p_le_end
    have h1 : fullWatchOffCore st0.core skip_lit = off := hoff
    simpa [h1, show off + (q - off) = q by omega, show off + (p - off) = p by omega,
      show off + (end_v - off) = end_v by omega] using hsw
  · rintro Jl ⟨wlen_v, wu_v, j_v, ⟨⟩⟩ mj ⟨st, wl_d, wu_d, idx, hwlen_v, hwu_v, hj_eq, hidx_le,
      hcore_eq, hsc_eq, hlen, hlay, hwat_pres, hsw_pres, hmj⟩ hJl
    subst hwlen_v hwu_v
    have hdel_len := hlen.scratch_ok.delayed_len_arr
    have hcv_le := hlen.core_ok.cur_vars_le
    have hwv_len := hlen.core_ok.wvec_len
    have hws_len := hlen.core_ok.wstk_len_arr
    have hwlen_le := hlen.core_ok.wlen_le
    have hcv_eq : st.core.cur_vars = st0.core.cur_vars := by rw [hcore_eq]
    have har_eq : st.core.arena = st0.core.arena := by rw [hcore_eq]
    have hal_eq : st.core.arena_len = st0.core.arena_len := by rw [hcore_eq]
    have href_eq : fullArenaClauseRefsCore st.core = fullArenaClauseRefsCore st0.core := by
      unfold fullArenaClauseRefsCore; rw [har_eq, hal_eq]
    have hdel_eq : st.scratch.delayed = st0.scratch.delayed := by rw [hsc_eq]
    have hdisk_del : (p0FlushDisk wl_d wu_d st).scratch.delayed = st.scratch.delayed := rfl
    have hdisk_wv : (p0FlushDisk wl_d wu_d st).core.wvec = st.core.wvec := rfl
    have hdisk_ws : (p0FlushDisk wl_d wu_d st).core.wstk = st.core.wstk := rfl
    have hdisk_del_len : (p0FlushDisk wl_d wu_d st).scratch.delayed.length = 3 * c.delayed_cap :=
      hdel_len
    have hdisk_wv_len : (p0FlushDisk wl_d wu_d st).core.wvec.length = 4 * c.max_vars := hwv_len
    have hdisk_ws_len : (p0FlushDisk wl_d wu_d st).core.wstk.length = c.wcap := hws_len
    dsimp only [Blocks.get]
    c0_hsteps_nogrp
    · have hlt_j : j_v.toNat < di.toNat := hc
      have hidx_lt : idx < dlen := by omega
      obtain ⟨h3i_lt, hj1_nat, hj2_nat, hj3_nat, hrw_lt0, hrw_ne, how_f, hcr_lt_st,
        hcr_ref_st, _, _, hrw64_0, hrw64p1_0⟩ :=
        p0_slow_delayed_entry hdelc hdel_len hj_eq hidx_lt hdlen_le hdel_eq hcv_eq href_eq hdel0
      let rw_v := st.scratch.delayed[j_v.toNat]'(by omega)
      let ow_v := st.scratch.delayed[(j_v + 1#64).toNat]'(by rw [hj1_nat]; omega)
      let cr_v := st.scratch.delayed[(j_v + 2#64).toNat]'(by rw [hj2_nat]; omega)
      have hrw_lt : rw_v.toNat < 2 * st.core.cur_vars := hrw_lt0
      have hrw64_nat : (rw_v.setWidth 64 <<< (1 : Nat)).toNat = 2 * rw_v.toNat := hrw64_0
      have hrw64p1_nat :
          ((rw_v.setWidth 64 <<< (1 : Nat)) + 1#64).toNat = 2 * rw_v.toNat + 1 := hrw64p1_0
      have hwv_i0 : (rw_v.setWidth 64 <<< (1 : Nat)).toNat < st.core.wvec.length := by
        rw [hwv_len, hrw64_nat]; omega
      have hwv_i1 : ((rw_v.setWidth 64 <<< (1 : Nat)) + 1#64).toNat < st.core.wvec.length := by
        rw [hwv_len, hrw64p1_nat]; omega
      let roff_w := st.core.wvec[(rw_v.setWidth 64 <<< (1 : Nat)).toNat]'hwv_i0
      let rsz_w := st.core.wvec[((rw_v.setWidth 64 <<< (1 : Nat)) + 1#64).toNat]'hwv_i1
      have hroff_eq : (roff_w.setWidth 64).toNat = fullWatchOffCore st.core rw_v.toNat := by
        rw [zext_toNat _ (by decide)]; unfold fullWatchOffCore
        rw [List.getElem?_eq_getElem (by rw [hwv_len]; omega), Option.getD_some]
        exact congrArg BitVec.toNat (by dsimp only [roff_w]; exact p0_getElem_idx hrw64_nat _ _)
      have hrsz_eq : (rsz_w.setWidth 64).toNat = fullWatchSizeCore st.core rw_v.toNat := by
        rw [zext_toNat _ (by decide)]; unfold fullWatchSizeCore
        rw [List.getElem?_eq_getElem (by rw [hwv_len]; omega), Option.getD_some]
        exact congrArg BitVec.toNat (by dsimp only [rsz_w]; exact p0_getElem_idx hrw64p1_nat _ _)
      have hbd_rw := hlay.bounds rw_v.toNat hrw_lt
      have hrend_nat : (roff_w.setWidth 64 + rsz_w.setWidth 64).toNat =
          fullWatchOffCore st.core rw_v.toNat + fullWatchSizeCore st.core rw_v.toNat := by
        rw [BitVec.toNat_add, hroff_eq, hrsz_eq, Nat.mod_eq_of_lt (by omega)]
      have hrend1_nat : (roff_w.setWidth 64 + rsz_w.setWidth 64 + 1#64).toNat =
          fullWatchOffCore st.core rw_v.toNat + fullWatchSizeCore st.core rw_v.toNat + 1 := by
        rw [BitVec.toNat_add, hrend_nat]; change (_ + 1) % 2 ^ 64 = _
        exact Nat.mod_eq_of_lt (by omega)
      have hwl_nat : (BitVec.ofNat 64 st.core.wlen).toNat = st.core.wlen :=
        p0_bv64_ofNat (by omega)
      have hwl2_nat : (BitVec.ofNat 64 st.core.wlen + 2#64).toNat = st.core.wlen + 2 := by
        rw [BitVec.toNat_add, hwl_nat]; change (_ + 2) % 2 ^ 64 = _
        exact Nat.mod_eq_of_lt (by omega)
      c0_hsteps_nogrp
      refine wp_join_group (ts := [i64, i64])
        (fun (wlen_n, wu_n, ()) mn => ∃ (st_n : FullState) (wl_dn : Nat) (wu_dn : BitVec 64),
          wlen_n = BitVec.ofNat 64 st_n.core.wlen ∧ wu_n = st_n.core.wusable ∧
          st_n.core = { st0.core with
            wvec := st_n.core.wvec, wstk := st_n.core.wstk,
            wlen := st_n.core.wlen, wusable := st_n.core.wusable } ∧
          st_n.scratch = { st0.scratch with wsort := st_n.scratch.wsort } ∧
          st_n.LengthsOk c ∧ WatchStackLayout st_n.core ∧
          (WatchesInv F_cur st0.core → WatchesInv F_cur st_n.core) ∧
          (skip_lit < 2 * st0.core.cur_vars →
            ∀ off q p end_v, SplitWatchesInv F_cur st0.core skip_lit off q p end_v →
              let off' := fullWatchOffCore st_n.core skip_lit
              SplitWatchesInv F_cur st_n.core skip_lit off'
                (off' + (q - off)) (off' + (p - off)) (off' + (end_v - off))) ∧
          (FullMem c (p0FlushDisk wl_dn wu_dn st_n) ⋆ R) mn)
        (fun _ ⟨wlen_n, wu_n, ⟨⟩⟩ mn ⟨st_n, wl_dn, wu_dn, hwl_n, hwu_n, hcn, hscn, hln, hlyn,
            hwn, hswn, hmn⟩ => by
          c0_hsteps
          exact hJl (wlen_n, wu_n, j_v + 3#64, ()) mn (by dsimp only; rw [hj_eq, hj3_nat]; omega)
            ⟨st_n, wl_dn, wu_dn, idx + 1, hwl_n, hwu_n, hj3_nat, by omega, hcn, hscn, hln, hlyn,
              hwn, hswn, hmn⟩) ?_
      intro Jnext hJnext
      have hrv_w0 : (p0FlushDisk wl_d wu_d st).core.wvec[
          2 * (p0FlushDisk wl_d wu_d st).scratch.delayed[j_v.toNat].toNat % 2 ^ 64]'(by
            dsimp only [p0FlushDisk]
            change 2 * rw_v.toNat % 2 ^ 64 < st.core.wvec.length
            rw [hwv_len, Nat.mod_eq_of_lt (by omega : 2 * rw_v.toNat < 2 ^ 64)]; omega) =
          roff_w := by
        dsimp only [p0FlushDisk, roff_w]
        exact p0_getElem_idx
          ((Nat.mod_eq_of_lt (by omega : 2 * rw_v.toNat < 2 ^ 64)).trans hrw64_nat.symm) _ _
      have hrv_w1 : (p0FlushDisk wl_d wu_d st).core.wvec[
          (2 * (p0FlushDisk wl_d wu_d st).scratch.delayed[j_v.toNat].toNat + 1) % 2 ^ 64]'(by
            dsimp only [p0FlushDisk]
            change (2 * rw_v.toNat + 1) % 2 ^ 64 < st.core.wvec.length
            rw [hwv_len, Nat.mod_eq_of_lt (by omega : 2 * rw_v.toNat + 1 < 2 ^ 64)]; omega) =
          rsz_w := by
        dsimp only [p0FlushDisk, rsz_w]
        exact p0_getElem_idx
          ((Nat.mod_eq_of_lt (by omega : 2 * rw_v.toNat + 1 < 2 ^ 64)).trans hrw64p1_nat.symm) _ _
      have hrv_w0_s : st.core.wvec[2 * st.scratch.delayed[j_v.toNat].toNat % 2 ^ 64]'(by
            change 2 * rw_v.toNat % 2 ^ 64 < st.core.wvec.length
            rw [hwv_len, Nat.mod_eq_of_lt (by omega : 2 * rw_v.toNat < 2 ^ 64)]; omega) =
          roff_w := by simpa only [p0FlushDisk] using hrv_w0
      have hrv_w1_s : st.core.wvec[(2 * st.scratch.delayed[j_v.toNat].toNat + 1) % 2 ^ 64]'(by
            change (2 * rw_v.toNat + 1) % 2 ^ 64 < st.core.wvec.length
            rw [hwv_len, Nat.mod_eq_of_lt (by omega : 2 * rw_v.toNat + 1 < 2 ^ 64)]; omega) =
          rsz_w := by simpa only [p0FlushDisk] using hrv_w1
      have hroff_t : roff_w.toNat = fullWatchOffCore st.core rw_v.toNat := by
        rw [← hroff_eq, zext_toNat _ (by decide)]
      have hrsz_t : rsz_w.toNat = fullWatchSizeCore st.core rw_v.toNat := by
        rw [← hrsz_eq, zext_toNat _ (by decide)]
      have hmod_2rw : 2 * st.scratch.delayed[j_v.toNat].toNat % 2 ^ 64 = 2 * rw_v.toNat :=
        Nat.mod_eq_of_lt (by omega)
      have hmod_2rw1 : (2 * st.scratch.delayed[j_v.toNat].toNat + 1) % 2 ^ 64 =
          2 * rw_v.toNat + 1 := Nat.mod_eq_of_lt (by omega)
      have hmod_2rw1_rv : (2 * rw_v.toNat + 1) % 2 ^ 64 = 2 * rw_v.toNat + 1 :=
        Nat.mod_eq_of_lt (by omega)
      have hrv_w0_raw : st.core.wvec[2 * rw_v.toNat]'(by rw [hwv_len]; omega) = roff_w := by
        simpa only [hmod_2rw] using hrv_w0_s
      have hrv_w1_raw : st.core.wvec[2 * rw_v.toNat + 1]'(by rw [hwv_len]; omega) = rsz_w := by
        simpa only [hmod_2rw1] using hrv_w1_s
      refine wp_join_group (ts := [])
        (fun _ m2 => (FullMem c (p0FlushDisk wl_d wu_d st) ⋆ R) m2)
        (fun _ ⟨⟩ m2 hm2 => by
          dsimp only [Blocks.get_here, Blocks.get_there]
          refine wp_join_group (ts := [i64])
            (fun p mn => wp Γ Q X (.jump Jnext (.var p.1, .var st.core.wusable, ())) mn)
            (fun _ p mn h => by try dsimp only [Blocks.get_here, Blocks.get_there]; exact h) ?_
          intro Jnext2 hJnext2
          refine wp_join_group (ts := [])
            (fun _ m3 => (FullMem c (p0FlushDisk wl_d wu_d st) ⋆ R) m3)
            (fun _ ⟨⟩ m3 hm3 => by
              dsimp only [Blocks.get_here, Blocks.get_there]
              refine wp_join_group (ts := [])
                (fun _ mc => (FullMem c (p0FlushDisk wl_d wu_d st) ⋆ R) mc)
                (fun _ ⟨⟩ mc hmc => by
                  dsimp only [Blocks.get_here, Blocks.get_there]
                  c0_hsteps_nogrp
                  have hmc_sync : (FullMem c st ⋆ R) m := by
                    simpa only [p0FlushDisk, hwl_nat] using hm
                  refine LeanQbe.T.wp_call_of_spec _ _ (hSlow _ _ _ _ ?_)
                  refine ⟨c, F_cur, st, R, idx, dlen, skip_lit, rfl, hlen, hlay, hj_eq,
                    hdi_eq, hidx_lt, hdlen_le, ?_, hmc_sync,
                    fun ok wvec' wstk' wlen' wu' wsort' mp hlen_p hlay_p hwat_p hsw_p hmp => ?_⟩
                  · unfold DelayedWatchesOk at hdel0 ⊢
                    intro k hk; simpa only [hcv_eq, hdel_eq, href_eq] using hdel0 k hk
                  · let st_p : FullState :=
                      { st0 with
                        core := { st0.core with wvec := wvec', wstk := wstk',
                                                wlen := wlen', wusable := wu' }
                        scratch := { st0.scratch with wsort := wsort' } }
                    have hst_p_eq :
                        ({ st with
                            core := { st.core with wvec := wvec', wstk := wstk',
                                                   wlen := wlen', wusable := wu' }
                            scratch := { st.scratch with wsort := wsort' } } : FullState) =
                          st_p := by
                      cases st; dsimp only at hcore_eq hsc_eq; rw [hcore_eq, hsc_eq]
                    have hcore_p :
                        ({ st.core with wvec := wvec', wstk := wstk',
                                        wlen := wlen', wusable := wu' } : FullCoreState) =
                          st_p.core := by dsimp only [st_p]; rw [hcore_eq]
                    rw [hst_p_eq] at hlen_p hmp; rw [hcore_p] at hlay_p hwat_p hsw_p
                    c0_hsteps_nogrp
                    refine hQ ok wvec' wstk' wlen' wu' wsort' mp hlen_p hlay_p
                      (fun hw0 => hwat_p (hwat_pres hw0)) ?_ hmp
                    intro hsk off q p end_v hsw0
                    have hsw1 := hsw_pres hsk off q p end_v hsw0
                    have hsw2 := hsw_p (hcv_eq ▸ hsk)
                      (fullWatchOffCore st.core skip_lit)
                      (fullWatchOffCore st.core skip_lit + (q - off))
                      (fullWatchOffCore st.core skip_lit + (p - off))
                      (fullWatchOffCore st.core skip_lit + (end_v - off)) hsw1
                    simpa [Nat.add_sub_cancel_left] using hsw2) ?_
              intro Jc3 hJc3
              p0_hsplit
              · have hrsz0 : fullWatchSizeCore st.core rw_v.toNat = 0 := by
                  have h := congrArg BitVec.toNat (hc : _)
                  simp only [bv_c0, p0FlushDisk] at h
                  rw [← hrsz_t]; simpa only [hrv_w1_s] using h
                p0_hsplit
                · have hw_pos : 1 ≤ st.core.wlen := by
                    have h := hc
                    rw [Nat.mod_eq_of_lt (by omega : st.core.wlen < 2 ^ 64)] at h; omega
                  p0_hsplit
                  · have hfit2 : st.core.wlen + 2 ≤ c.wcap := by
                      have h := hc
                      rw [Nat.mod_eq_of_lt (by omega : st.core.wlen + 2 < 2 ^ 64),
                        Nat.mod_eq_of_lt (by omega : c.wcap < 2 ^ 64)] at h; exact h
                    have hwv_set_lt : (rw_v.setWidth 64 <<< (1 : Nat) + 1).toNat <
                        ((p0FlushDisk wl_d wu_d st).core.wvec.set
                          (rw_v.setWidth 64 <<< (1 : Nat)).toNat
                          ((BitVec.ofNat 64 st.core.wlen).setWidth 32)).length := by
                      rw [List.length_set, hdisk_wv_len, show (1 : BitVec 64) = 1#64 from rfl,
                        hrw64p1_nat]; omega
                    c0_hsteps_nogrp
                    have hwl_bv : BitVec.ofNat 64 st.core.wlen + 2#64 =
                        BitVec.ofNat 64 (st.core.wlen + 2) := by
                      apply BitVec.eq_of_toNat_eq; rw [hwl2_nat, p0_bv64_ofNat (by omega)]
                    have hmod_wl1 : (st.core.wlen + 1) % 2 ^ 64 = st.core.wlen + 1 :=
                      Nat.mod_eq_of_lt (by omega)
                    have htr32 :
                        (BitVec.ofNat 64 st.core.wlen).setWidth 32 =
                          BitVec.ofNat 32 st.core.wlen := by
                      apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_ofNat]
                    let st_n : FullState := { st with core := { st.core with
                      wstk := (st.core.wstk.set st.core.wlen ow_v).set (st.core.wlen + 1) cr_v
                      wvec := (st.core.wvec.set (2 * rw_v.toNat) (BitVec.ofNat 32 st.core.wlen)).set
                        (2 * rw_v.toNat + 1) 2#32
                      wlen := st.core.wlen + 2 } }
                    obtain ⟨hcn, hscn, hln, hlyn, hwn, hswn⟩ :=
                      p0_slow_case2a_fin hlay hlen hrw_lt hw_pos hrsz0 hfit2 how_f hcr_lt_st
                        hcr_ref_st hrw_ne hcv_eq hcore_eq hsc_eq hwat_pres hsw_pres
                    exact hJnext (BitVec.ofNat 64 st.core.wlen + 2#64, st.core.wusable, ()) m
                      ⟨st_n, wl_d, wu_d, hwl_bv, rfl, hcn, hscn, hln, hlyn, hwn, hswn,
                        Eq.mp (congrArg (fun x => (FullMem c x ⋆ R) m) (by
                          unfold p0FlushDisk; dsimp only [st_n, ow_v, cr_v]; congr 1; congr 1 <;>
                            (try simp only [bv_c0, p0_bv64_1_toNat, p0_bv64_2_toNat, hmod_2rw,
                              hmod_2rw1_rv, hmod_wl1, hwl_nat, htr32]) <;> rfl)) hm⟩
                  · exact hJc3 () m3 hm3
                · exact hJc3 () m3 hm3
              · exact hJc3 () m3 hm3) ?_
          intro Jc2 hJc2
          p0_hsplit
          · have hrsz_pos : 0 < fullWatchSizeCore st.core rw_v.toNat := by
              have h := hc
              simp only [bv_c0, p0FlushDisk, hmod_2rw1, hrv_w1_raw, hrsz_t] at h; exact h
            p0_hsplit
            · have hend_wlen : fullWatchOffCore st.core rw_v.toNat +
                  fullWatchSizeCore st.core rw_v.toNat = st.core.wlen := by
                have h := congrArg BitVec.toNat (hc : _)
                simp only [bv_c0, p0FlushDisk, hmod_2rw, hmod_2rw1] at h
                simpa only [hrv_w0_raw, hrv_w1_raw, hroff_t, hrsz_t, hwl_nat,
                  Nat.mod_eq_of_lt (by omega :
                    fullWatchOffCore st.core rw_v.toNat +
                      fullWatchSizeCore st.core rw_v.toNat < 2 ^ 64),
                  Nat.mod_eq_of_lt (by omega : st.core.wlen < 2 ^ 64)] using h
              p0_hsplit
              · have hfit2 : st.core.wlen + 2 ≤ c.wcap := by
                  have h := hc
                  rw [Nat.mod_eq_of_lt (by omega : st.core.wlen + 2 < 2 ^ 64),
                    Nat.mod_eq_of_lt (by omega : c.wcap < 2 ^ 64)] at h; exact h
                c0_hsteps_nogrp
                let sz0 := fullWatchSizeCore st.core rw_v.toNat
                have hwl_bv :
                    BitVec.ofNat 64 st.core.wlen + 2#64 = BitVec.ofNat 64 (st.core.wlen + 2) := by
                  apply BitVec.eq_of_toNat_eq; rw [hwl2_nat, p0_bv64_ofNat (by omega)]
                have hmod_wl1 : (st.core.wlen + 1) % 2 ^ 64 = st.core.wlen + 1 :=
                  Nat.mod_eq_of_lt (by omega)
                have hsz_bv :
                    (rsz_w.setWidth 64 + 2).setWidth 32 = BitVec.ofNat 32 (sz0 + 2) := by
                  apply BitVec.eq_of_toNat_eq
                  rw [show (2 : BitVec 64) = 2#64 from rfl, BitVec.toNat_setWidth,
                    BitVec.toNat_add, hrsz_eq, BitVec.toNat_ofNat]
                  change ((sz0 + 2) % 2 ^ 64) % 2 ^ 32 = (sz0 + 2) % 2 ^ 32
                  rw [Nat.mod_eq_of_lt (by omega : sz0 + 2 < 2 ^ 64)]
                let st_n : FullState := { st with core := { st.core with
                  wstk := (st.core.wstk.set st.core.wlen ow_v).set (st.core.wlen + 1) cr_v
                  wvec := st.core.wvec.set (2 * rw_v.toNat + 1) (BitVec.ofNat 32 (sz0 + 2))
                  wlen := st.core.wlen + 2 } }
                obtain ⟨hcn, hscn, hln, hlyn, hwn, hswn⟩ :=
                  p0_slow_case2b_fin rfl hlay hlen hrw_lt hrsz_pos hend_wlen hfit2 how_f
                    hcr_lt_st hcr_ref_st hrw_ne hcv_eq hcore_eq hsc_eq hwat_pres hsw_pres
                exact hJnext (BitVec.ofNat 64 st.core.wlen + 2#64, st.core.wusable, ()) m
                  ⟨st_n, wl_d, wu_d, hwl_bv, rfl, hcn, hscn, hln, hlyn, hwn, hswn,
                    Eq.mp (congrArg (fun x => (FullMem c x ⋆ R) m) (by
                      unfold p0FlushDisk; dsimp only [st_n, sz0, ow_v, cr_v]; congr 1; congr 1 <;>
                        (try simp only [bv_c0, p0_bv64_1_toNat, p0_bv64_2_toNat, hmod_2rw,
                          hmod_2rw1_rv, hmod_wl1, hrv_w1_raw, hwl_nat, hsz_bv]) <;> rfl)) hm⟩
              · exact hJc2 () m2 hm2
            · exact hJc2 () m2 hm2
          · exact hJc2 () m2 hm2) ?_
      intro Jc1 hJc1
      p0_hsplit
      · have hrsz_pos : 0 < fullWatchSizeCore st.core rw_v.toNat := by
          have h := hc; simp only [bv_c0, p0FlushDisk, hmod_2rw1, hrv_w1_raw, hrsz_t] at h; exact h
        p0_hsplit
        · have hend2_le : fullWatchOffCore st.core rw_v.toNat +
              fullWatchSizeCore st.core rw_v.toNat + 2 ≤ st.core.wlen := by
            have h := hc
            simp only [bv_c0, p0FlushDisk, hmod_2rw, hmod_2rw1, hrv_w0_raw, hrv_w1_raw,
              hroff_t, hrsz_t] at h
            rw [Nat.mod_eq_of_lt (by omega :
                fullWatchOffCore st.core rw_v.toNat + fullWatchSizeCore st.core rw_v.toNat + 2 <
                  2 ^ 64),
              Nat.mod_eq_of_lt (by omega : st.core.wlen < 2 ^ 64)] at h; exact h
          have hws_i0 : (roff_w.setWidth 64 + rsz_w.setWidth 64).toNat <
              (p0FlushDisk wl_d wu_d st).core.wstk.length := by
            rw [hdisk_ws_len, hrend_nat]; omega
          have hws_i1 : (roff_w.setWidth 64 + rsz_w.setWidth 64 + 1).toNat <
              (p0FlushDisk wl_d wu_d st).core.wstk.length := by
            rw [hdisk_ws_len, show (1 : BitVec 64) = 1#64 from rfl, hrend1_nat]; omega
          p0_hsplit
          · have hsent0 : st.core.wstk[fullWatchOffCore st.core rw_v.toNat +
                fullWatchSizeCore st.core rw_v.toNat]? = some 0xFFFFFFFF#32 := by
              rw [List.getElem?_eq_getElem (by rw [hws_len]; omega)]
              refine congrArg some (Eq.trans ?_ hc)
              congr 1; simp only [bv_c0, p0FlushDisk, hmod_2rw, hmod_2rw1, hrv_w0_raw,
                hrv_w1_raw, hroff_t, hrsz_t]
              rw [Nat.mod_eq_of_lt (by omega)]
            p0_hsplit
            · have hsent1 : st.core.wstk[fullWatchOffCore st.core rw_v.toNat +
                  fullWatchSizeCore st.core rw_v.toNat + 1]? = some 0xFFFFFFFF#32 := by
                rw [List.getElem?_eq_getElem (by rw [hws_len]; omega)]
                refine congrArg some (Eq.trans ?_ hc)
                congr 1; simp only [bv_c0, p0FlushDisk, hmod_2rw, hmod_2rw1, hrv_w0_raw,
                  hrv_w1_raw, hroff_t, hrsz_t]
                rw [Nat.mod_eq_of_lt (by omega)]
              let sz0 := fullWatchSizeCore st.core rw_v.toNat
              let wend0 := fullWatchOffCore st.core rw_v.toNat + sz0
              have hsz_bv :
                  (rsz_w.setWidth 64 + 2).setWidth 32 = BitVec.ofNat 32 (sz0 + 2) := by
                apply BitVec.eq_of_toNat_eq
                rw [show (2 : BitVec 64) = 2#64 from rfl, BitVec.toNat_setWidth,
                  BitVec.toNat_add, hrsz_eq, BitVec.toNat_ofNat]
                change ((sz0 + 2) % 2 ^ 64) % 2 ^ 32 = (sz0 + 2) % 2 ^ 32
                rw [Nat.mod_eq_of_lt (by omega : sz0 + 2 < 2 ^ 64)]
              have hfin : ∀ (wu_n : BitVec 64) (mn : Mem 64),
                  (FullMem c (p0FlushDisk wl_d wu_d
                    { st with core :=
                        { st.core with
                          wstk := (st.core.wstk.set wend0 ow_v).set (wend0 + 1) cr_v
                          wvec := st.core.wvec.set (2 * rw_v.toNat + 1)
                            (BitVec.ofNat 32 (sz0 + 2))
                          wusable := wu_n } }) ⋆ R) mn →
                  wp Γ Q X (Expr.jump Jnext (Arg.var (BitVec.ofNat 64 st.core.wlen),
                    Arg.var wu_n, ())) mn := by
                intro wu_n mn hmn
                let st_n : FullState := { st with core := { st.core with
                  wstk := (st.core.wstk.set wend0 ow_v).set (wend0 + 1) cr_v
                  wvec := st.core.wvec.set (2 * rw_v.toNat + 1) (BitVec.ofNat 32 (sz0 + 2))
                  wusable := wu_n } }
                obtain ⟨hcn, hscn, hln, hlyn, hwn, hswn⟩ :=
                  p0_slow_case1_fin rfl rfl hlay hlen hrw_lt hrsz_pos hend2_le hsent0 hsent1
                    how_f hcr_lt_st hcr_ref_st hrw_ne hcv_eq hcore_eq hsc_eq hwat_pres hsw_pres
                exact hJnext (BitVec.ofNat 64 st.core.wlen, wu_n, ()) mn
                  ⟨st_n, wl_d, wu_d, rfl, rfl, hcn, hscn, hln, hlyn, hwn, hswn, hmn⟩
              c0_hsteps_nogrp
              refine wp_join_group (ts := [i64]) (fun p mf =>
                  wp Γ Q X (.jump Jnext
                    (Arg.var (BitVec.ofNat 64 st.core.wlen), Arg.var p.1, ())) mf)
                (fun _ _ mf h => by
                  dsimp only [Blocks.get_here, Blocks.get_there] at *; exact h) ?_
              intro Jwu hJwu; c0_hsteps_nogrp
              · refine hfin (st.core.wusable - 2#64) m ?_
                refine Eq.mp (congrArg (fun x => (FullMem c x ⋆ R) m) ?_) hm
                unfold p0FlushDisk; dsimp only [wend0, sz0, ow_v, cr_v]; congr 1; congr 1 <;>
                  (try simp only [bv_c0, p0_bv64_1_toNat, p0_bv64_2_toNat, hmod_2rw, hmod_2rw1_rv,
                    hrv_w0_raw, hrv_w1_raw, hroff_t, hrsz_t, hsz_bv,
                    Nat.mod_eq_of_lt (by omega :
                      fullWatchOffCore st.core rw_v.toNat +
                        fullWatchSizeCore st.core rw_v.toNat < 2 ^ 64),
                    Nat.mod_eq_of_lt (by omega :
                      fullWatchOffCore st.core rw_v.toNat +
                        fullWatchSizeCore st.core rw_v.toNat + 1 < 2 ^ 64)]) <;> rfl
              · refine hfin st.core.wusable m ?_
                refine Eq.mp (congrArg (fun x => (FullMem c x ⋆ R) m) ?_) hm
                unfold p0FlushDisk; dsimp only [wend0, sz0, ow_v, cr_v]; congr 1; congr 1 <;>
                  (try simp only [bv_c0, p0_bv64_1_toNat, p0_bv64_2_toNat, hmod_2rw, hmod_2rw1_rv,
                    hrv_w0_raw, hrv_w1_raw, hroff_t, hrsz_t, hsz_bv,
                    Nat.mod_eq_of_lt (by omega :
                      fullWatchOffCore st.core rw_v.toNat +
                        fullWatchSizeCore st.core rw_v.toNat < 2 ^ 64),
                    Nat.mod_eq_of_lt (by omega :
                      fullWatchOffCore st.core rw_v.toNat +
                        fullWatchSizeCore st.core rw_v.toNat + 1 < 2 ^ 64)]) <;> rfl
            · exact hJc1 () mj hmj
          · exact hJc1 () mj hmj
        · exact hJc1 () mj hmj
      · exact hJc1 () mj hmj
    · c0_hsteps_nogrp
      have hst_eq : st =
          { st0 with
            core := { st0.core with
              wvec := st.core.wvec, wstk := st.core.wstk,
              wlen := st.core.wlen, wusable := st.core.wusable }
            scratch := { st0.scratch with wsort := st.scratch.wsort } } := by
        cases st; cases st0; simp only [FullState.mk.injEq] at *; exact ⟨hcore_eq, hsc_eq⟩
      have hwl_d_eq : (BitVec.ofNat 64 st.core.wlen).toNat = st.core.wlen :=
        p0_bv64_ofNat (by omega)
      have hm_sync : (FullMem c st ⋆ R) (by assumption : Mem 64) := by
        simpa only [p0FlushDisk, hwl_d_eq] using (by assumption : _)
      exact hQ true st.core.wvec st.core.wstk st.core.wlen st.core.wusable st.scratch.wsort _
        (hst_eq ▸ hlen) (hcore_eq ▸ hlay) (fun hw0 => hcore_eq ▸ hwat_pres hw0)
        (fun hsk off q p end_v hsw0 => by
          have h1 := hsw_pres hsk off q p end_v hsw0
          simpa only [← hcore_eq] using h1)
        (hst_eq ▸ hm_sync)

end LeanQbe.T.Examples.Kissat.Proof.PropSearch
