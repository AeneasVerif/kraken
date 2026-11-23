/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM7BcpHot
public import LeanQbe.T.Examples.Kissat.FullM6BcpS15Proof1
public import LeanQbe.T.Examples.Kissat.FullM5OtfsLemmas1
public import LeanQbe.T.Examples.Kissat.FullSpec

/-!
# Kissat M7 Hot-Path Fused BCP Proofs — Part 0 (`full_prop_lit_ovf_hot`,
  `full_prop_chrono_hot`, and Inline Watch-Push / Clause-Swap Lemmas)

Zero `import all`, plain `public section` (`0` blanket `@[expose]`).
Proves:
1. `full_prop_lit_ovf_hot_wp`: cold overflow push wrapper delegating to `full_watch_push`.
2. `full_prop_chrono_hot_wp`: chronological backjump watch repair on `[t0 .. trail_end)`.
3. `m7_repl_empty_layout`, `m7_repl_{empty,end,sentinel}_step`, `m7_tB_swap_step`,
   `m7_ovf_swap_step`: inline watch-push & `tB` / `ovf` arena-swap preservation lemmas.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM7BcpHot

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0HeadStep LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.FastCore
open LeanQbe.T.Examples.Kissat.FullM5Otfs
open LeanQbe.T.Examples.Kissat.FullM6BcpS15
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullAnalyzeHelpers
open LeanQbe.T.Examples.Kissat.Full.FullPropDecSpecs hiding
  fullWatchPushSpec fullPropLitSpec fullPropagateIgnoreSpec fullPropagateSpec
  FullTrailExt FullArenaPermEq
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics

attribute [local irreducible] fastPropMem

local macro "m7_hsteps" : tactic =>
  `(tactic| ((try (first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)); c0_hsteps))

local macro "m7_hsteps_nogrp" : tactic =>
  `(tactic| ((try (first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)); c0_hsteps_nogrp))

local macro "m7_hsplit" : tactic =>
  `(tactic| ((try (first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)); c0_hsplit))

/-! ## 1. Canonical Contracts for Cold Overflow & Chrono Repair Helpers -/

/-- Specification of `full_prop_lit_ovf_hot(h, rw, w0, cref)`. -/
@[expose] def fullPropLitOvfHotSpec : Spec [i64, i32, i32, i32] [.bool] :=
  fun (h, lit, w0, cref, ()) m Q X =>
    Full.fullWatchPushSpec (h, lit, w0, cref, 2#32, ()) m Q X

/-- Specification of `full_prop_chrono_hot(h, t0)`.
Repairs non-highest-level second watches on recently unit-propagated trail slice `[t0..trail_end)`.
Preserves `LengthsOk`, `FullWitnessInv`, and `FullArenaPermEq`, while leaving `vals`, `flags`,
`lvl`, `rsns`, `trl`, `trail_pos`, `trail_end`, `propagated`, `unassigned`, `unflushed`, `fuel`,
and `confl_*` untouched (setting `oom = 1#64` only on `ok = false`). -/
@[expose] def fullPropChronoHotSpec : Spec [i64, i64] [.bool] :=
  fun (h, t0, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (st0 : FullState)
      (R : Mem 64 → Prop),
      h = c.hdr ∧ st0.LengthsOk c ∧ FullWitnessInv c F0 F_cur st0.core ∧
      st0.core.dense_mode = 0#64 ∧ t0.toNat ≤ st0.core.trail_end ∧
      (FullMem c st0 ⋆ R) m ∧
      ∀ (ok : Bool) wvec' arena' wstk' wlen' wu' oom' wsort' m',
        let st' : FullState :=
          { core :=
              { st0.core with
                wvec := wvec', arena := arena', wstk := wstk', wlen := wlen',
                wusable := wu', oom := oom' }
            scratch := { st0.scratch with wsort := wsort' } }
        st'.LengthsOk c → FullWitnessInv c F0 F_cur st'.core →
        FullPropDecSpecs.FullArenaPermEq st0.core st'.core →
        (ok = true → oom' = st0.core.oom) →
        (ok = false → oom' = 1#64) →
        (FullMem c st' ⋆ R) m' → Q (ok, ()) m'

/-! ## 2. Proof of `full_prop_lit_ovf_hot_wp` -/

theorem full_prop_lit_ovf_hot_wp (Γ : Env)
    (hPush : ∀ args m Q X, Full.fullWatchPushSpec args m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] args m Q X) :
    ∀ args m Q X, fullPropLitOvfHotSpec args m Q X →
      Func.wp Γ full_prop_lit_ovf_hot_body args m Q X := by
  rintro ⟨h, rw, w0, cref, ⟨⟩⟩ m Q X hsp
  unfold Func.wp full_prop_lit_ovf_hot_body
  m7_hsteps_nogrp
  exact wp_call_of_spec _ _ (hPush _ _ _ _ hsp)

/-! ## 3. Shared BitVec / Chrono Helpers & Proof of `full_prop_chrono_hot_wp` -/

private theorem m7_bv32_rshift1_toNat (x : BitVec 32) :
    (BitVec.setWidth 64 (x >>> 1#32)).toNat = x.toNat / 2 := by
  have := BitVec.isLt x
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  omega

private theorem m7_bv32_add1_toNat {x : BitVec 32} (hx : x.toNat + 1 < 2 ^ 32) :
    (x + 1#32).toNat = x.toNat + 1 := by
  rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl, Nat.mod_eq_of_lt hx]

private theorem m7_bv32_zext64_add_toNat (r : BitVec 32) {k : Nat} (hk : r.toNat + k < 2 ^ 64) :
    (BitVec.setWidth 64 r + BitVec.ofNat 64 k).toNat = r.toNat + k := by
  have h1 : (BitVec.setWidth 64 r).toNat = r.toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans r.isLt (by decide))]
  have h2 : (BitVec.ofNat 64 k).toNat = k := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.toNat_add, h1, h2, Nat.mod_eq_of_lt hk]

private theorem m7_list_getElem_of_idx {α : Type} {xs : List α} {i j : Nat}
    {hi : i < xs.length} {hj : j < xs.length} (hij : i = j) :
    xs[i]'hi = xs[j]'hj := by subst hij; rfl

private theorem m7_chrono_r_facts {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {st : FullState} {t : BitVec 64} {ol r : BitVec 32}
    (hlen_t : st.LengthsOk c) (hw_t : FullWitnessInv c F0 F_cur st.core)
    (ht_lt : t.toNat < st.core.trail_end) (htrl_lt : t.toNat < st.core.trl.length)
    (hol : ol = st.core.trl[t.toNat]'htrl_lt)
    (hrsn_lt : (ol.setWidth 64 >>> 1#64).toNat < st.core.rsns.length)
    (hr : r = st.core.rsns[(ol.setWidth 64 >>> 1#64).toNat]'hrsn_lt)
    (hr_ne : r ≠ 0xFFFFFFFF#32) (hr_lg : (r &&& 0x80000000#32) = 0#32) :
    r.toNat ∈ fullArenaClauseRefsCore st.core ∧
    3 ≤ fullArenaClauseSizeCore st.core r.toNat ∧
    r.toNat + 3 + fullArenaClauseSizeCore st.core r.toNat ≤ st.core.arena.length ∧
    r.toNat < 0x80000000 ∧
    (BitVec.setWidth 64 (ol >>> 1#32)).toNat = (ol.setWidth 64 >>> 1#64).toNat ∧
    ol.toNat / 2 = (ol.setWidth 64 >>> 1#64).toNat := by
  have hi_r : (BitVec.setWidth 64 (ol >>> 1#32)).toNat = (ol.setWidth 64 >>> 1#64).toNat := by
    simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hdiv_r : ol.toNat / 2 = (ol.setWidth 64 >>> 1#64).toNat := by
    have := BitVec.isLt ol
    simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; omega
  have hrg : st.core.rsns[(st.core.trl[t.toNat]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 = r := by
    have hidx : (st.core.trl[t.toNat]?.getD 0#32).toNat / 2 =
        (ol.setWidth 64 >>> 1#64).toNat := by
      rw [List.getElem?_eq_getElem htrl_lt, Option.getD_some, ← hol]; exact hdiv_r
    rw [hidx, List.getElem?_eq_getElem hrsn_lt, Option.getD_some, ← hr]
  have href_all := hw_t.reason_inv t.toNat ht_lt (by rw [hrg]; exact hr_ne)
  rw [hrg] at href_all
  have hrb : ¬ ((r &&& 0x80000000#32) ≠ 0#32) := fun h => h hr_lg
  rw [ite_eq_right hrb] at href_all
  obtain ⟨href, _, _⟩ := href_all
  obtain ⟨_, hsz3, hfit, _, _⟩ := hw_t.arena.refs_wf r.toNat href
  have hr_lt_ar : r.toNat + 3 + fullArenaClauseSizeCore st.core r.toNat ≤ st.core.arena.length := by
    have := hlen_t.core_ok.arena_len_le
    have := hlen_t.core_ok.arena_len_arr; omega
  exact ⟨href, hsz3, hr_lt_ar, (m5_bv32_lt_highbit_iff r).mpr hr_lg, hi_r, hdiv_r⟩

private theorem m7_chrono_swap_preserves_inv {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {k0 k : FullCoreState} {cref i1 i2 : Nat}
    (hlen : k.LengthsOk c) (hw : FullWitnessInv c F0 F_cur k)
    (hdm : k.dense_mode = 0#64)
    (hperm0 : FullPropDecSpecs.FullArenaPermEq k0 k)
    (hcref : cref ∈ fullArenaClauseRefsCore k) (_hi1 : 1 ≤ i1) (_hi2 : 1 ≤ i2)
    (hi1_sz : i1 < fullArenaClauseSizeCore k cref)
    (hi2_sz : i2 < fullArenaClauseSizeCore k cref) :
    let v1 := k.arena[cref + 3 + i1]?.getD 0#32
    let v2 := k.arena[cref + 3 + i2]?.getD 0#32
    let k' : FullCoreState :=
      { k with arena := (k.arena.set (cref + 3 + i1) v2).set (cref + 3 + i2) v1 }
    k'.LengthsOk c ∧ FullWitnessInv c F0 F_cur k' ∧
    FullPropDecSpecs.FullArenaPermEq k0 k' := by
  intro v1 v2 k'
  have hnw0 : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c k) :=
    fullWitnessInv_to_nw hlen.cur_vars_le hw
  have ⟨hfit1, hfit2⟩ : cref + 3 + fullArenaClauseSizeCore k cref ≤ k.arena.length ∧
      k.arena.length = c.arena_cap := by
    have hwf := hnw0.arena.refs_wf cref hcref
    have hwe1 : (withEmptyWatchesCore c k).arena = k.arena := rfl
    have hwe2 : (withEmptyWatchesCore c k).arena_len = k.arena_len := rfl
    have hfit' : cref + 3 + fullArenaClauseSizeCore k cref ≤ k.arena_len := by
      have h1 := hwf.2.2.1; have h2 := hwf.2.2.2.1
      unfold fullArenaClauseSizeCore at h1 ⊢
      rw [hwe1, hwe2] at h1 h2; omega
    have := hlen.arena_len_le; have := hlen.arena_len_arr; omega
  have hv1 : v1 = k.arena[cref + 3 + i1]'(by omega) := by
    dsimp [v1]; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
  have hv2 : v2 = k.arena[cref + 3 + i2]'(by omega) := by
    dsimp [v2]; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
  obtain ⟨hnw', hperm'⟩ := full_swapLits_preserves_nw hlen hnw0 hcref hi1_sz hi2_sz
  have hnw_k' : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c k') := by
    simpa only [k', hv1, hv2] using hnw'
  have hperm_k' : FullPropDecSpecs.FullArenaPermEq k k' := by
    simpa only [k', hv1, hv2] using hperm'
  have hlen' : k'.LengthsOk c :=
    { hlen with arena_len_arr := by simp [k', hfit2] }
  have hwat_raw : ModeWatchesInv F_cur k' :=
    hw.watches.with_wstk rfl rfl rfl rfl rfl (fun q hq => hperm_k'.1.symm ▸ hq)
  have hwat : WatchesInv F_cur k' := by
    dsimp only [ModeWatchesInv, k'] at hwat_raw
    rwa [ite_eq_left hdm] at hwat_raw
  exact ⟨hlen', fullWitnessInv_of_nw hnw_k' hdm hwat, hperm0.trans hperm_k'⟩

private theorem m7_chrono_push_wit {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {st : FullState} {ol r nw : BitVec 32} {pok : Bool}
    {wv' ws' : List (BitVec 32)} {wl' : Nat} {wu' : BitVec 64}
    (hlen_t : st.LengthsOk c) (hw_t : FullWitnessInv c F0 F_cur st.core)
    (hdm_t : st.core.dense_mode = 0#64) (href : r.toNat ∈ fullArenaClauseRefs st)
    (hcr_lt31 : r.toNat < 0x80000000) (hnw_ltv : nw.toNat < 2 * st.core.cur_vars)
    (hlen_p : ({ st.core with wvec := wv', wstk := ws', wlen := wl', wusable := wu' }).LengthsOk c)
    (hlay_p : WatchStackLayout
      { st.core with wvec := wv', wstk := ws', wlen := wl', wusable := wu' })
    (hpres_o : ∀ l < 2 * st.core.cur_vars, l ≠ nw.toNat →
      fullWatchSizeCore { st.core with
          wvec := wv', wstk := ws', wlen := wl', wusable := wu' } l =
        fullWatchSizeCore st.core l ∧
      ∀ k < fullWatchSizeCore st.core l,
        ws'[fullWatchOffCore { st.core with
            wvec := wv', wstk := ws', wlen := wl', wusable := wu' } l + k]? =
        st.core.wstk[fullWatchOffCore st.core l + k]?)
    (hpok_t : pok = true →
      fullWatchSizeCore { st.core with
          wvec := wv', wstk := ws', wlen := wl', wusable := wu' } nw.toNat =
        fullWatchSizeCore st.core nw.toNat + 2 ∧
      (∀ k < fullWatchSizeCore st.core nw.toNat,
        ws'[fullWatchOffCore { st.core with
            wvec := wv', wstk := ws', wlen := wl', wusable := wu' } nw.toNat + k]? =
        st.core.wstk[fullWatchOffCore st.core nw.toNat + k]?) ∧
      ws'[fullWatchOffCore { st.core with
          wvec := wv', wstk := ws', wlen := wl', wusable := wu' }
        nw.toNat + fullWatchSizeCore st.core nw.toNat]? = some (ol &&& 0x7FFFFFFF#32) ∧
      ws'[fullWatchOffCore { st.core with
          wvec := wv', wstk := ws', wlen := wl', wusable := wu' }
        nw.toNat + fullWatchSizeCore st.core nw.toNat + 1]? = some r)
    (hpok_f : pok = false →
      fullWatchSizeCore { st.core with
          wvec := wv', wstk := ws', wlen := wl', wusable := wu' } nw.toNat =
        fullWatchSizeCore st.core nw.toNat ∧
      ∀ k < fullWatchSizeCore st.core nw.toNat,
        ws'[fullWatchOffCore { st.core with
            wvec := wv', wstk := ws', wlen := wl', wusable := wu' } nw.toNat + k]? =
        st.core.wstk[fullWatchOffCore st.core nw.toNat + k]?) :
    FullWitnessInv c F0 F_cur
      { st.core with wvec := wv', wstk := ws', wlen := wl', wusable := wu' } := by
  let k' : FullCoreState := { st.core with wvec := wv', wstk := ws', wlen := wl', wusable := wu' }
  have hmw : ModeWatchesInv F_cur k' := by
    cases pok with
    | false =>
      exact fa_watchPush_fail_preserves hdm_t hw_t.watches hlay_p fun l hl =>
        if hln : l = nw.toNat then by subst l; exact hpok_f rfl else hpres_o l hl hln
    | true =>
      obtain ⟨hsz, hsame, hw0, hw1⟩ := hpok_t rfl
      exact fa_watchPush_large_preserves hdm_t hw_t.watches hnw_ltv hlay_p hpres_o
        hsz hsame hw0 hw1 (bv32_mask7f_flag0 ol) hcr_lt31 href
  have hwat_p : WatchesInv F_cur k' := by
    unfold ModeWatchesInv at hmw
    simpa only [k', hdm_t, ↓reduceIte] using hmw
  have hnw_p : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c k') :=
    fullWitnessInv_nw_congr hlen_p.cur_vars_le
      (fullWitnessInv_to_nw hlen_t.core_ok.cur_vars_le hw_t)
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  exact fullWitnessInv_of_nw hnw_p hdm_t hwat_p

private structure M7ChronoLoopInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (st0 st : FullState) (t : BitVec 64) : Prop where
  len : st.LengthsOk c
  wit : FullWitnessInv c F0 F_cur st.core
  core_eq : ∃ wv' ar' ws' wl' wu',
    st.core = { st0.core with wvec := wv', arena := ar', wstk := ws', wlen := wl', wusable := wu' }
  sc_eq : ∃ wsort', st.scratch = { st0.scratch with wsort := wsort' }
  perm : FullPropDecSpecs.FullArenaPermEq st0.core st.core
  tle : t.toNat ≤ st0.core.trail_end

private theorem m7_chrono_oom_ret {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {st0 st : FullState} {R : Mem 64 → Prop} {Q : Post [.bool]} {mp : Mem 64}
    {wv_t ar_t ws_t wv' ws' wso_t wso' : List (BitVec 32)} {wl_t wl' : Nat}
    {wu_t wu' : BitVec 64}
    (hQ : ∀ (ok : Bool) wvec' arena' wstk' wlen' wu' oom' wsort' m',
      let st' : FullState :=
        { core :=
            { st0.core with
              wvec := wvec', arena := arena', wstk := wstk', wlen := wlen',
              wusable := wu', oom := oom' }
          scratch := { st0.scratch with wsort := wsort' } }
      st'.LengthsOk c → FullWitnessInv c F0 F_cur st'.core →
      FullPropDecSpecs.FullArenaPermEq st0.core st'.core →
      (ok = true → oom' = st0.core.oom) →
      (ok = false → oom' = 1#64) →
      (FullMem c st' ⋆ R) m' → Q (ok, ()) m')
    (hceq : st.core = { st0.core with
      wvec := wv_t, arena := ar_t, wstk := ws_t, wlen := wl_t, wusable := wu_t })
    (hsceq : st.scratch = { st0.scratch with wsort := wso_t })
    (hdm : st.core.dense_mode = 0#64)
    (hperm_t : FullPropDecSpecs.FullArenaPermEq st0.core st.core)
    (hlen_p : ({ st with
        core := { st.core with wvec := wv', wstk := ws', wlen := wl', wusable := wu' }
        scratch := { st.scratch with wsort := wso' } } : FullState).LengthsOk c)
    (hw_p : FullWitnessInv c F0 F_cur
      { st.core with wvec := wv', wstk := ws', wlen := wl', wusable := wu' })
    (hmp : (FullMem c
      { st with
        core := { st.core with wvec := wv', wstk := ws', wlen := wl', wusable := wu', oom := 1#64 }
        scratch := { st.scratch with wsort := wso' } } ⋆ R) mp) :
    Q (false, ()) mp := by
  let st_o : FullState :=
    { core := { st0.core with
        wvec := wv', arena := ar_t, wstk := ws', wlen := wl', wusable := wu', oom := 1#64 }
      scratch := { st0.scratch with wsort := wso' } }
  have hceq_o : st_o.core =
      { st.core with wvec := wv', wstk := ws', wlen := wl', wusable := wu', oom := 1#64 } := by
    dsimp only [st_o]; rw [hceq]
  have hsceq_o : st_o.scratch = { st.scratch with wsort := wso' } := by
    dsimp only [st_o]; rw [hsceq]
  have hlen_o : st_o.LengthsOk c :=
    ⟨by rw [hceq_o]; exact { hlen_p.core_ok with vals_len := hlen_p.core_ok.vals_len },
     by rw [hsceq_o]; exact hlen_p.scratch_ok⟩
  have hwat_mode : ModeWatchesInv F_cur st_o.core := by
    rw [hceq_o]; exact hw_p.watches.with_wstk rfl rfl rfl rfl rfl (fun _ h => h)
  have hdm_o : st_o.core.dense_mode = 0#64 := by rw [hceq_o]; exact hdm
  have hwat_o : WatchesInv F_cur st_o.core := by
    simpa only [ModeWatchesInv, hdm_o, ↓reduceIte] using hwat_mode
  have hnw_o : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c st_o.core) :=
    fullWitnessInv_nw_congr hlen_o.core_ok.cur_vars_le
      (fullWitnessInv_to_nw hlen_p.core_ok.cur_vars_le hw_p)
      (by rw [hceq_o]) (by rw [hceq_o]) (by rw [hceq_o]) (by rw [hceq_o]) (by rw [hceq_o])
      (by rw [hceq_o]) (by rw [hceq_o]) (by rw [hceq_o]) (by rw [hceq_o]) (by rw [hceq_o])
      (by rw [hceq_o]) (by rw [hceq_o]) (by rw [hceq_o])
  have hw_o : FullWitnessInv c F0 F_cur st_o.core := fullWitnessInv_of_nw hnw_o hdm_o hwat_o
  have hperm_o : FullPropDecSpecs.FullArenaPermEq st0.core st_o.core := by
    rw [hceq_o]; exact ⟨hperm_t.1, hperm_t.2⟩
  exact hQ false wv' ar_t ws' wl' wu' 1#64 wso' mp hlen_o hw_o hperm_o
    (fun hf => by cases hf) (fun _ => rfl)
    (m5_fullMem_of_eq hmp hceq_o.symm hsceq_o.symm)

theorem full_prop_chrono_hot_wp (Γ : Env)
    (hDefrag : ∀ a m Q X, Full.fullWstackDefragSpec a m Q X →
      Γ "full_wstack_defrag" [i64] [] a m Q X)
    (hUnw : ∀ a m Q X, Full.fullUnwatchLargeSpec a m Q X →
      Γ "full_unwatch_large" [i64, i32, i32] [] a m Q X)
    (hPush : ∀ a m Q X, Full.fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, fullPropChronoHotSpec a m Q X →
      Func.wp Γ full_prop_chrono_hot_body a m Q X := by
  rintro ⟨h, t0, ⟨⟩⟩ m0 Q X ⟨c, F0, F_cur, st0, R, rfl, hlen0, hw0, hdm0, ht0_le, hm0, hQ⟩
  have hret_noop : Q (true, ()) m0 :=
    hQ true st0.core.wvec st0.core.arena st0.core.wstk st0.core.wlen st0.core.wusable st0.core.oom
      st0.scratch.wsort m0 hlen0 hw0 (.refl _) (fun _ => rfl) (fun hf => by cases hf) hm0
  have hmaxv := c.hmaxv; have har := c.harena; have hwc := c.hwcap
  unfold dimacsBound at hmaxv har hwc
  have hcv_le0 := hlen0.core_ok.cur_vars_le
  have hte0_64 : st0.core.trail_end < 2 ^ 64 := by
    have := hlen0.core_ok.trail_end_le; omega
  have hal0_64 : st0.core.arena_len < 2 ^ 64 := by
    have := hlen0.core_ok.arena_len_le; omega
  have hwc_64 : c.wcap < 2 ^ 64 := by omega
  unfold Func.wp full_prop_chrono_hot_body
  m7_hsteps
  · exact hret_noop
  · refine wp_loop_inv
      (fun (t, ()) ml => ∃ st : FullState,
        M7ChronoLoopInv c F0 F_cur st0 st t ∧ (FullMem c st ⋆ R) ml)
      (fun (t, ()) _ => st0.core.trail_end - t.toNat) ?_ ?_
    · intro L hL
      exact hL (t0, ()) m0
        ⟨st0, ⟨hlen0, hw0, ⟨_, _, _, _, _, rfl⟩, ⟨_, rfl⟩, .refl _, ht0_le⟩, hm0⟩
    · rintro L ⟨t, ⟨⟩⟩ ml ⟨st, ⟨hlen_t, hw_t, ⟨wv_t, ar_t, ws_t, wl_t, wu_t, hceq_t⟩,
          ⟨wso_t, hsceq_t⟩, hperm_t, ht_le⟩, hml⟩ ih_out
      have hdm_t : st.core.dense_mode = 0#64 := by rw [hceq_t]; exact hdm0
      have hte_eq : st.core.trail_end = st0.core.trail_end := by rw [hceq_t]
      have hcv_eq : st.core.cur_vars = st0.core.cur_vars := by rw [hceq_t]
      have halen_eq : st.core.arena_len = st0.core.arena_len := by rw [hceq_t]
      have htrl_len := hlen_t.core_ok.trl_len
      have hrsn_len := hlen_t.core_ok.rsns_len
      have haren_len := hlen_t.core_ok.arena_len_arr
      have hlvl_len := hlen_t.core_ok.lvl_len
      have hwv_len := hlen_t.core_ok.wvec_len
      have hcv_le := hlen_t.core_ok.cur_vars_le
      have hte_le := hlen_t.core_ok.trail_end_le
      have hal_le := hlen_t.core_ok.arena_len_le
      m7_hsplit
      · have ht_lt : t.toNat < st.core.trail_end := by c0_bound
        have htrl_lt : t.toNat < st.core.trl.length := by rw [htrl_len]; omega
        have ht1_nat : (t + 1#64).toNat = t.toNat + 1 := by
          rw [BitVec.toNat_add, show (1#64 : BitVec 64).toNat = 1 from rfl,
            Nat.mod_eq_of_lt (by omega)]
        have htp1_le : (t + 1#64).toNat ≤ st0.core.trail_end := by rw [ht1_nat]; omega
        have hrem_dec : st0.core.trail_end - (t + 1#64).toNat < st0.core.trail_end - t.toNat := by
          rw [ht1_nat]; omega
        obtain ⟨ol, hol_def⟩ : ∃ ol, ol = st.core.trl[t.toNat]'htrl_lt := ⟨_, rfl⟩
        have hol_lt : ol.toNat < 2 * st.core.cur_vars := by
          have := hw_t.trail_lits_lt t.toNat ht_lt
          rw [List.getElem?_eq_getElem htrl_lt, Option.getD_some, ← hol_def] at this
          exact this
        have hrsn_lt : (ol.setWidth 64 >>> 1#64).toNat < st.core.rsns.length := by
          have : (ol.setWidth 64 >>> 1#64).toNat = ol.toNat / 2 := by
            simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; omega
          rw [this, hrsn_len]; omega
        m7_hsplit
        · have hol_ge : 2 * st.core.cur_vars ≤ ol.toNat := by
            have hc' : 2 * (st0.core.cur_vars % 2 ^ 64) % 2 ^ 64 ≤ ol.toNat := by
              rw [hol_def]; exact hc
            rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hc'
            rw [hcv_eq]; exact hc'
          exact absurd hol_lt (Nat.not_lt.mpr hol_ge)
        · obtain ⟨r, hr_def⟩ :
              ∃ r, r = st.core.rsns[(ol.setWidth 64 >>> 1#64).toNat]'hrsn_lt := ⟨_, rfl⟩
          m7_hsplit
          · exact ih_out (t + 1#64, ()) ml hrem_dec
              ⟨st, ⟨hlen_t, hw_t, ⟨_, _, _, _, _, hceq_t⟩, ⟨_, hsceq_t⟩, hperm_t, htp1_le⟩, hml⟩
          m7_hsplit
          · exact ih_out (t + 1#64, ()) ml hrem_dec
              ⟨st, ⟨hlen_t, hw_t, ⟨_, _, _, _, _, hceq_t⟩, ⟨_, hsceq_t⟩, hperm_t, htp1_le⟩, hml⟩
          have hr_idx : (ol.setWidth 64 >>> 1#64).toNat = st.core.trl[t.toNat].toNat / 2 := by
            have := BitVec.isLt ol
            simp [← hol_def, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; omega
          have hr_eq' : r = st.core.rsns[st.core.trl[t.toNat].toNat / 2]'(by
              rw [← hr_idx]; exact hrsn_lt) := by
            rw [hr_def]; exact m7_list_getElem_of_idx hr_idx
          have hr_ne : r ≠ 0xFFFFFFFF#32 := by rw [hr_eq']; assumption
          have hr_lg : (r &&& 0x80000000#32) = 0#32 := by rw [hr_eq']; exact hc
          obtain ⟨href, hsz3, hr_lt_ar, hcr_lt31, hi_r, hdiv_r⟩ :=
            m7_chrono_r_facts hlen_t hw_t ht_lt htrl_lt hol_def hrsn_lt hr_def hr_ne hr_lg
          have hr_alen : r.toNat < st.core.arena.length := by omega
          have hr_add2_lt : (r.setWidth 64 + 2#64).toNat < st.core.arena.length := by
            rw [m7_bv32_zext64_add_toNat r (by omega)]; omega
          have hcb_nat : (r.setWidth 64 + 3#64).toNat = r.toNat + 3 :=
            m7_bv32_zext64_add_toNat r (by omega)
          m7_hsplit
          · have hgt : st.core.arena_len < r.toNat + 3 := by
              have hc' : st0.core.arena_len % 2 ^ 64 < (r.toNat + 3) % 2 ^ 64 := by
                rw [hr_eq']; exact hc
              have := hlen_t.core_ok.arena_len_le
              rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hc'
              omega
            have hwf_r := hw_t.arena.refs_wf r.toNat href; omega
          · obtain ⟨hdr, hhdr_def⟩ : ∃ hdr, hdr = st.core.arena[r.toNat]'hr_alen := ⟨_, rfl⟩
            obtain ⟨csz, hcsz_def⟩ :
                ∃ csz, csz = st.core.arena[(r.setWidth 64 + 2#64).toNat]'hr_add2_lt := ⟨_, rfl⟩
            have hcsz_eq : csz.toNat = fullArenaClauseSizeCore st.core r.toNat := by
              unfold fullArenaClauseSizeCore
              have hr2_eq : (r.setWidth 64 + 2#64).toNat = r.toNat + 2 :=
                m7_bv32_zext64_add_toNat r (by omega)
              rw [List.getElem?_eq_getElem (by omega), Option.getD_some, hcsz_def,
                m7_list_getElem_of_idx hr2_eq]
            m7_hsplit
            · exact ih_out (t + 1#64, ()) ml hrem_dec
                ⟨st, ⟨hlen_t, hw_t, ⟨_, _, _, _, _, hceq_t⟩, ⟨_, hsceq_t⟩,
                  hperm_t, htp1_le⟩, hml⟩
            m7_hsplit
            · exact ih_out (t + 1#64, ()) ml hrem_dec
                ⟨st, ⟨hlen_t, hw_t, ⟨_, _, _, _, _, hceq_t⟩, ⟨_, hsceq_t⟩,
                  hperm_t, htp1_le⟩, hml⟩
            m7_hsplit
            · exact ih_out (t + 1#64, ()) ml hrem_dec
                ⟨st, ⟨hlen_t, hw_t, ⟨_, _, _, _, _, hceq_t⟩, ⟨_, hsceq_t⟩,
                  hperm_t, htp1_le⟩, hml⟩
            · have hcsz_ge3 : 3 ≤ csz.toNat := by rw [hcsz_eq]; exact hsz3
              have hcb_ar : r.toNat + 3 + csz.toNat ≤ st.core.arena.length := by
                rw [hcsz_eq]; exact hr_lt_ar
              have hcb0_lt : (r.setWidth 64 + 3#64).toNat < st.core.arena.length := by
                rw [hcb_nat]; omega
              have hcb1_lt :
                  ((r.setWidth 64 + 3#64) + 1#64).toNat < st.core.arena.length := by
                rw [BitVec.toNat_add, hcb_nat, show (1#64 : BitVec 64).toNat = 1 from rfl,
                  Nat.mod_eq_of_lt (by omega)]; omega
              have hcb1_nat : ((r.setWidth 64 + 3#64) + 1#64).toNat = r.toNat + 3 + 1 := by
                rw [BitVec.toNat_add, hcb_nat, show (1#64 : BitVec 64).toNat = 1 from rfl,
                  Nat.mod_eq_of_lt (by omega)]
              m7_hsplit
              · exact ih_out (t + 1#64, ()) ml hrem_dec
                  ⟨st, ⟨hlen_t, hw_t, ⟨_, _, _, _, _, hceq_t⟩, ⟨_, hsceq_t⟩,
                    hperm_t, htp1_le⟩, hml⟩
              · have hol_get : st.core.trl[t.toNat] = ol := hol_def.symm
                have hr_idx_lt : (BitVec.setWidth 64 (st.core.trl[t.toNat] >>>
                    1#32)).toNat < st.core.rsns.length := by
                  rw [hol_get, hi_r]; exact hrsn_lt
                have hr_get : st.core.rsns[(BitVec.setWidth 64 (st.core.trl[t.toNat] >>>
                    1#32)).toNat]'hr_idx_lt = r := by
                  rw [hr_def]; exact m7_list_getElem_of_idx (by rw [hol_get, hi_r])
                have hcb1_load : (BitVec.setWidth 64 st.core.rsns[(BitVec.setWidth 64
                    (st.core.trl[t.toNat] >>> 1#32)).toNat] + 3#64 + 1#64).toNat <
                    st.core.arena.length := by
                  rw [hr_get]; exact hcb1_lt
                obtain ⟨l1, hl1_def⟩ :
                    ∃ l1, l1 = st.core.arena[((r.setWidth 64 + 3#64) +
                      1#64).toNat]'hcb1_lt := ⟨_, rfl⟩
                m7_hsplit
                · exact ih_out (t + 1#64, ()) ml hrem_dec
                    ⟨st, ⟨hlen_t, hw_t, ⟨_, _, _, _, _, hceq_t⟩, ⟨_, hsceq_t⟩,
                      hperm_t, htp1_le⟩, hml⟩
                · have hcb1_raw :
                      (st.core.rsns[st.core.trl[t.toNat].toNat / 2].toNat +
                        BitVec.toNat 3#64 + BitVec.toNat 1#64) % 2 ^ 64 <
                        st.core.arena.length := by
                    rw [← hr_eq', show BitVec.toNat 3#64 = 3 from rfl,
                      show BitVec.toNat 1#64 = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
                    omega
                  have hl1_get :
                      st.core.arena[(st.core.rsns[st.core.trl[t.toNat].toNat / 2].toNat +
                        BitVec.toNat 3#64 + BitVec.toNat 1#64) % 2 ^ 64]'hcb1_raw = l1 := by
                    rw [hl1_def]; apply m7_list_getElem_of_idx
                    rw [← hr_eq', hcb1_nat, show BitVec.toNat 3#64 = 3 from rfl,
                      show BitVec.toNat 1#64 = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
                  have hl1_ltv : l1.toNat < 2 * st.core.cur_vars := by
                    have hc' : ¬ 2 * (st0.core.cur_vars % 2 ^ 64) % 2 ^ 64 ≤ l1.toNat := by
                      rw [← hl1_get]; exact hc
                    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hc'
                    rw [hcv_eq]; omega
                  have hl1_rsh :
                      (BitVec.setWidth 64 (l1 >>> 1#32)).toNat < st.core.lvl.length := by
                    rw [m7_bv32_rshift1_toNat, hlvl_len]; omega
                  have hb1_ltv : (st.core.arena[r.toNat + 3 + 1]?.getD 0#32).toNat <
                      2 * st.core.cur_vars := by
                    rw [List.getElem?_eq_getElem (by omega), Option.getD_some,
                      m7_list_getElem_of_idx (hj := hcb1_lt) hcb1_nat.symm, ← hl1_def]
                    exact hl1_ltv
                  m7_hsteps_nogrp
                  refine wp_loop_inv
                    (fun (best, bi, k, ()) mk =>
                      1 ≤ bi.toNat ∧ bi.toNat < csz.toNat ∧
                      2 ≤ k.toNat ∧ k.toNat ≤ csz.toNat ∧
                      (st.core.arena[r.toNat + 3 + bi.toNat]?.getD 0#32).toNat <
                        2 * st.core.cur_vars ∧ mk = ml)
                    (fun (_, _, k, ()) _ => csz.toNat - k.toNat) ?_ ?_
                  · intro Jin hJin
                    exact hJin (_, 1#32, 2#32, ()) ml
                      ⟨by decide, by change 1 < csz.toNat; omega, by decide,
                       by change 2 ≤ csz.toNat; omega, hb1_ltv, rfl⟩
                  · rintro Jin ⟨best, bi, k, ⟨⟩⟩ mk
                      ⟨hbi_ge, hbi_lt, hk_ge, hk_le, hbi_ltv, hmk_eq⟩ ih_in
                    subst mk
                    m7_hsplit
                    · have hk_lt : k.toNat < csz.toNat := by
                        have hidx2 :
                            (st.core.rsns[st.core.trl[t.toNat].toNat / 2].toNat +
                              BitVec.toNat 2#64) % 2 ^ 64 = (r.setWidth 64 + 2#64).toNat := by
                          rw [← hr_eq', m7_bv32_zext64_add_toNat r (by omega),
                            show BitVec.toNat 2#64 = 2 from rfl]
                          exact Nat.mod_eq_of_lt (by omega)
                        have hcsz_raw :
                            st.core.arena[(st.core.rsns[st.core.trl[t.toNat].toNat / 2].toNat +
                              BitVec.toNat 2#64) % 2 ^ 64]'(by
                                rw [hidx2]; exact hr_add2_lt) = csz := by
                          rw [hcsz_def]; exact m7_list_getElem_of_idx hidx2
                        rw [← hcsz_raw]; exact hc
                      have hk_idx : ((r.setWidth 64 + 3#64) + k.setWidth 64).toNat =
                          r.toNat + 3 + k.toNat := by
                        rw [BitVec.toNat_add, hcb_nat, BitVec.toNat_setWidth,
                          Nat.mod_eq_of_lt (Nat.lt_trans k.isLt (by decide)),
                          Nat.mod_eq_of_lt (by omega)]
                      have hcbk_lt : ((r.setWidth 64 + 3#64) + k.setWidth 64).toNat <
                          st.core.arena.length := by rw [hk_idx]; omega
                      have hkp1 : (k + 1#32).toNat = k.toNat + 1 :=
                        m7_bv32_add1_toNat (by have := BitVec.isLt csz; omega)
                      have hcbk_load :
                          ((BitVec.setWidth 64 st.core.rsns[(BitVec.setWidth 64
                              (st.core.trl[t.toNat] >>> 1#32)).toNat] + 3#64) +
                            k.setWidth 64).toNat < st.core.arena.length := by
                        rw [hr_get]; exact hcbk_lt
                      have hcbk_raw :
                          (st.core.rsns[st.core.trl[t.toNat].toNat / 2].toNat +
                            BitVec.toNat 3#64 + k.toNat) % 2 ^ 64 < st.core.arena.length := by
                        rw [← hr_eq', show BitVec.toNat 3#64 = 3 from rfl,
                          Nat.mod_eq_of_lt (by omega)]
                        omega
                      obtain ⟨ck, hck_def⟩ :
                          ∃ ck, ck = st.core.arena[((r.setWidth 64 + 3#64) +
                            k.setWidth 64).toNat]'hcbk_lt := ⟨_, rfl⟩
                      have hck_raw :
                          st.core.arena[(st.core.rsns[st.core.trl[t.toNat].toNat / 2].toNat +
                            BitVec.toNat 3#64 + k.toNat) % 2 ^ 64]'hcbk_raw = ck := by
                        rw [hck_def]; apply m7_list_getElem_of_idx
                        rw [← hr_eq', hk_idx, show BitVec.toNat 3#64 = 3 from rfl,
                          Nat.mod_eq_of_lt (by omega)]
                      m7_hsteps_nogrp
                      refine wp_join_group (ts := [i32, i32])
                        (fun (best', bi', ()) mb =>
                          1 ≤ bi'.toNat ∧ bi'.toNat < csz.toNat ∧
                          (st.core.arena[r.toNat + 3 + bi'.toNat]?.getD 0#32).toNat <
                            2 * st.core.cur_vars ∧ mb = ml) ?_ ?_
                      · rintro _ ⟨best', bi', ⟨⟩⟩ mb ⟨hbi1', hbi_lt', hbi_v', hmb_eq⟩
                        subst mb
                        m7_hsteps_nogrp
                        exact ih_in (best', bi', k + 1#32, ()) ml
                          (by dsimp only; rw [hkp1]; omega)
                          ⟨hbi1', hbi_lt', by rw [hkp1]; omega, by rw [hkp1]; omega, hbi_v', rfl⟩
                      · intro Jbest hJbest
                        m7_hsplit
                        · have hck_ltv : ck.toNat < 2 * st.core.cur_vars := by
                            have hc' : ck.toNat < 2 * (st0.core.cur_vars % 2 ^ 64) % 2 ^ 64 := by
                              rw [← hck_raw]; exact hc
                            rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hc'
                            rw [hcv_eq]; exact hc'
                          have hck_get :
                              (st.core.arena[r.toNat + 3 + k.toNat]?.getD 0#32).toNat <
                                2 * st.core.cur_vars := by
                            rw [List.getElem?_eq_getElem (by omega), Option.getD_some,
                              m7_list_getElem_of_idx (hj := hcbk_lt) hk_idx.symm, ← hck_def]
                            exact hck_ltv
                          have hck_lvl :
                              (BitVec.setWidth 64 (ck >>> 1#32)).toNat < st.core.lvl.length := by
                            rw [m7_bv32_rshift1_toNat, hlvl_len]; omega
                          m7_hsteps_nogrp
                          refine wp_join_group (ts := [i32, i32])
                            (fun (best', bi', ()) mb =>
                              1 ≤ bi'.toNat ∧ bi'.toNat < csz.toNat ∧
                              (st.core.arena[r.toNat + 3 + bi'.toNat]?.getD 0#32).toNat <
                                2 * st.core.cur_vars ∧ mb = ml) ?_ ?_
                          · rintro _ ⟨best', bi', ⟨⟩⟩ mb hpost
                            m7_hsteps_nogrp; exact hJbest (best', bi', ()) mb hpost
                          · intro Jin2 hJin2
                            m7_hsteps_nogrp
                            · exact hJin2 (_, k, ()) ml ⟨by omega, hk_lt, hck_get, rfl⟩
                            · exact hJin2 (best, bi, ()) ml ⟨hbi_ge, hbi_lt, hbi_ltv, rfl⟩
                        · exact hJbest (best, bi, ()) ml ⟨hbi_ge, hbi_lt, hbi_ltv, rfl⟩
                    · refine wp_join_group (ts := []) (fun () mb => L (t + 1#64, ()) mb) ?_ ?_
                      · rintro _ ⟨⟩ mb hmb; m7_hsteps_nogrp; exact hmb
                      · intro Js hJs
                        m7_hsplit
                        · have hbi_ge2 : 2 ≤ bi.toNat := by
                            have hne : bi ≠ 1#32 := hc
                            have : bi.toNat ≠ 1 := fun h => hne (BitVec.eq_of_toNat_eq h)
                            omega
                          have hbi_csz : bi.toNat < fullArenaClauseSizeCore st.core r.toNat := by
                            rw [← hcsz_eq]; exact hbi_lt
                          have hbi_idx : ((r.setWidth 64 + 3#64) + bi.setWidth 64).toNat =
                              r.toNat + 3 + bi.toNat := by
                            rw [BitVec.toNat_add, hcb_nat, BitVec.toNat_setWidth,
                              Nat.mod_eq_of_lt (Nat.lt_trans bi.isLt (by decide)),
                              Nat.mod_eq_of_lt (by omega)]
                          have hcbbi_lt : ((r.setWidth 64 + 3#64) + bi.setWidth 64).toNat <
                              st.core.arena.length := by rw [hbi_idx]; omega
                          have hcbbi_load :
                              ((BitVec.setWidth 64 st.core.rsns[(BitVec.setWidth 64
                                  (st.core.trl[t.toNat] >>> 1#32)).toNat] + 3#64) +
                                bi.setWidth 64).toNat < st.core.arena.length := by
                            rw [hr_get]; exact hcbbi_lt
                          obtain ⟨nw, hnw_def⟩ :
                              ∃ nw, nw = st.core.arena[((r.setWidth 64 + 3#64) +
                                bi.setWidth 64).toNat]'hcbbi_lt := ⟨_, rfl⟩
                          have hnw_ltv : nw.toNat < 2 * st.core.cur_vars := by
                            rwa [List.getElem?_eq_getElem (by omega), Option.getD_some,
                              m7_list_getElem_of_idx hbi_idx.symm, ← hnw_def] at hbi_ltv
                          have h1_idx : ((r.setWidth 64 + 3#64) + 1#64).toNat =
                              r.toNat + 3 + 1 := hcb1_nat
                          m7_hsteps_nogrp
                          refine wp_join_group (ts := [])
                            (fun () m_d => ∃ (st_d : FullState)
                              (wv_d ws_d : List (BitVec 32)) (wl_d : Nat)
                              (wu_d : BitVec 64) (wso_d : List (BitVec 32)),
                              st_d.core = { st.core with
                                wvec := wv_d, wstk := ws_d, wlen := wl_d, wusable := wu_d } ∧
                              st_d.scratch = { st.scratch with wsort := wso_d } ∧
                              st_d.LengthsOk c ∧ FullWitnessInv c F0 F_cur st_d.core ∧
                              (FullMem c st_d ⋆ R) m_d) ?_ ?_
                          · rintro _ ⟨⟩ m_d ⟨st_d, wv_d, ws_d, wl_d, wu_d, wso_d, hsd_c,
                                hsd_sc, hlen_d, hw_d, hm_d⟩
                            have href_d : r.toNat ∈ fullArenaClauseRefs st_d := by
                              change r.toNat ∈ fullArenaClauseRefsCore st_d.core
                              rw [hsd_c]; exact href
                            have hr_any : ∀ {sh : BitVec 32} {pf},
                                (BitVec.setWidth 64 sh).toNat =
                                  (ol.setWidth 64 >>> 1#64).toNat →
                                st.core.rsns[(BitVec.setWidth 64 sh).toNat]'pf = r :=
                              fun h => (m7_list_getElem_of_idx h).trans hr_def.symm
                            have hnw_any : ∀ {x : BitVec 32} {pf}, x = r →
                                st.core.arena[(BitVec.setWidth 64 x + 3 +
                                  bi.setWidth 64).toNat]'pf = nw := fun hx =>
                              (m7_list_getElem_of_idx (by rw [hx]; rfl)).trans hnw_def.symm
                            have hsh_eq : ∀ {sh : BitVec 32},
                                (sh = st.core.trl[t.toNat] >>> 1#32 ∨
                                 sh = st.core.trl[t.toNat] >>> (1 : Nat)) →
                                (BitVec.setWidth 64 sh).toNat =
                                  (ol.setWidth 64 >>> 1#64).toNat := by
                              intro sh hsh
                              rcases hsh with rfl | rfl <;>
                              · rw [hol_get]; have := BitVec.isLt ol
                                simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
                                try omega
                            have hnw_raw_eq : ∀ {sh : BitVec 32} {pf1 pf2},
                                (sh = st.core.trl[t.toNat] >>> 1#32 ∨
                                 sh = st.core.trl[t.toNat] >>> (1 : Nat)) →
                                st.core.arena[(BitVec.setWidth 64
                                  (st.core.rsns[(BitVec.setWidth 64 sh).toNat]'pf1) + 3 +
                                  bi.setWidth 64).toNat]'pf2 = nw :=
                              fun hsh => hnw_any (hr_any (hsh_eq hsh))
                            m7_hsteps_nogrp
                            c0_call hPush
                            refine ⟨c, st_d, R, rfl, hlen_d, hw_d.watches.layout,
                              fun h => absurd h (by decide),
                              fun _ => ⟨by
                                change (_ &&& 0x7FFFFFFF#32) ≠ 0xFFFFFFFF#32
                                intro h0
                                have h1 := bv32_mask7f_flag0 (st.core.trl[t.toNat])
                                rw [h0] at h1; revert h1; decide,
                                by
                                  first
                                  | rw [hr_any (hsh_eq (Or.inl rfl))]; exact hr_ne
                                  | rw [hr_any (hsh_eq (Or.inr rfl))]; exact hr_ne⟩,
                              hm_d,
                              fun pok wv_p ws_p wl_p wu_p wso_p m_p hlen_p hlay_p hpres_o
                                hpok_t hpok_f hm_p => ?_⟩
                            have hw_p : FullWitnessInv c F0 F_cur
                                { st_d.core with
                                  wvec := wv_p, wstk := ws_p, wlen := wl_p, wusable := wu_p } :=
                              m7_chrono_push_wit (ol := st.core.trl[t.toNat]) (r := r) (nw := nw)
                                hlen_d hw_d (by rw [hsd_c]; exact hdm_t) href_d
                                hcr_lt31 (by rw [hsd_c]; exact hnw_ltv)
                                hlen_p.core_ok hlay_p
                                (fun l hl hne => by
                                  have h := hpres_o l hl
                                  first
                                  | rw [hnw_raw_eq (Or.inl rfl)] at h
                                  | rw [hnw_raw_eq (Or.inr rfl)] at h
                                  exact h hne)
                                (fun ht => by
                                  have h := hpok_t ht
                                  first
                                  | rw [hnw_raw_eq (Or.inl rfl), hr_any (hsh_eq (Or.inl rfl))] at h
                                  | rw [hnw_raw_eq (Or.inr rfl), hr_any (hsh_eq (Or.inr rfl))] at h
                                  exact ⟨h.2.2.1, h.2.2.2.1,
                                    by simpa only [BitVec.ofNat_eq_ofNat] using h.2.2.2.2.1,
                                    h.2.2.2.2.2 rfl⟩)
                                (fun hf => by
                                  have h := hpok_f hf
                                  first
                                  | rw [hnw_raw_eq (Or.inl rfl)] at h
                                  | rw [hnw_raw_eq (Or.inr rfl)] at h
                                  exact h.1 (by rw [hsd_c]; exact hnw_ltv))
                            have hsd_ar : st_d.core.arena = st.core.arena := by rw [hsd_c]
                            have hsd_dm : st_d.core.dense_mode = 0#64 := by rw [hsd_c]; exact hdm_t
                            have hperm_d : FullPropDecSpecs.FullArenaPermEq st0.core st_d.core := by
                              rw [hsd_c]; exact ⟨hperm_t.1, hperm_t.2⟩
                            m7_hsplit
                            · obtain ⟨st_p, hsp_c, hsp_sc, hmp'⟩ := m5_otfs_opaque_state
                                { st_d.core with
                                  wvec := wv_p, wstk := ws_p, wlen := wl_p, wusable := wu_p }
                                { st_d.scratch with wsort := wso_p } hm_p rfl rfl
                              have hsp_base : st_p.core = { st.core with
                                  wvec := wv_p, wstk := ws_p, wlen := wl_p, wusable := wu_p } := by
                                rw [hsp_c, hsd_c]
                              have hsp_scr : st_p.scratch =
                                  { st.scratch with wsort := wso_p } := by
                                rw [hsp_sc, hsd_sc]
                              have hlen_p' : st_p.LengthsOk c :=
                                ⟨by rw [hsp_c]; exact hlen_p.core_ok,
                                 by rw [hsp_sc]; exact hlen_p.scratch_ok⟩
                              have hw_p' : FullWitnessInv c F0 F_cur st_p.core := by
                                rw [hsp_c]; exact hw_p
                              have hperm_p' :
                                  FullPropDecSpecs.FullArenaPermEq st0.core st_p.core := by
                                rw [hsp_base]; exact ⟨hperm_t.1, hperm_t.2⟩
                              have hsp_ar : st_p.core.arena = st.core.arena := by rw [hsp_base]
                              have href_p : r.toNat ∈ fullArenaClauseRefsCore st_p.core := by
                                rw [hsp_base]; exact href
                              have hbi_csz_p : bi.toNat <
                                  fullArenaClauseSizeCore st_p.core r.toNat := by
                                unfold fullArenaClauseSizeCore; rw [hsp_ar]; exact hbi_csz
                              have hst1_bd : ((r.setWidth 64 + 3#64) + 1#64).toNat <
                                  st_p.core.arena.length := by rw [hsp_ar, h1_idx]; omega
                              have hstbi_bd : ((r.setWidth 64 + 3#64) + bi.setWidth 64).toNat <
                                  (st_p.core.arena.set
                                    ((r.setWidth 64 + 3#64) + 1#64).toNat nw).length := by
                                rw [List.length_set, hsp_ar, hbi_idx]; omega
                              have hl1_sp : l1 =
                                  st_p.core.arena[r.toNat + 3 + 1]'(by rw [hsp_ar]; omega) := by
                                rw [hl1_def]; simp only [hsp_ar]
                                exact m7_list_getElem_of_idx hcb1_nat
                              have hnw_sp : nw =
                                  st_p.core.arena[r.toNat + 3 + bi.toNat]'(by
                                    rw [hsp_ar]; omega) := by
                                rw [hnw_def]; simp only [hsp_ar]
                                exact m7_list_getElem_of_idx hbi_idx
                              obtain ⟨hlen_s, hw_s, hperm_s⟩ :=
                                m7_chrono_swap_preserves_inv hlen_p'.core_ok hw_p'
                                  (by rw [hsp_base]; exact hdm_t) hperm_p' href_p
                                  (Nat.le_refl 1) (by omega)
                                  (by
                                    have hsz_eq : fullArenaClauseSizeCore st_p.core r.toNat =
                                        fullArenaClauseSizeCore st.core r.toNat := by
                                      unfold fullArenaClauseSizeCore; rw [hsp_ar]
                                    rw [hsz_eq, ← hcsz_eq]; omega)
                                  hbi_csz_p
                              let ar_s : List (BitVec 32) :=
                                (st_p.core.arena.set (r.toNat + 3 + 1) nw).set
                                  (r.toNat + 3 + bi.toNat) l1
                              have har_s_eq : (st_p.core.arena.set
                                  ((r.setWidth 64 + 3#64) + 1#64).toNat nw).set
                                  ((r.setWidth 64 + 3#64) + bi.setWidth 64).toNat l1 = ar_s := by
                                rw [h1_idx, hbi_idx]
                              have har_s_def :
                                  (st_p.core.arena.set (r.toNat + 3 + 1)
                                    (st_p.core.arena[r.toNat + 3 + bi.toNat]?.getD 0#32)).set
                                    (r.toNat + 3 + bi.toNat)
                                    (st_p.core.arena[r.toNat + 3 + 1]?.getD 0#32) = ar_s := by
                                simp only [ar_s, List.getElem?_eq_getElem
                                  (show r.toNat + 3 + 1 < st_p.core.arena.length by
                                    rw [hsp_ar]; omega),
                                  List.getElem?_eq_getElem
                                    (show r.toNat + 3 + bi.toNat < st_p.core.arena.length by
                                      rw [hsp_ar]; omega),
                                  Option.getD_some, ← hl1_sp, ← hnw_sp]
                              rw [har_s_def] at hlen_s hw_s hperm_s
                              have hlen_s' : ({ st_p with core := { st_p.core with
                                  arena := ar_s } } : FullState).LengthsOk c :=
                                ⟨hlen_s, hlen_p'.scratch_ok⟩
                              have hr_lt_nat :
                                  (BitVec.setWidth 64 (st.core.trl[t.toNat] >>> (1 : Nat))).toNat <
                                    st.core.rsns.length := by
                                have h32 : (BitVec.setWidth 64
                                    (st.core.trl[t.toNat] >>> 1#32)).toNat <
                                    st.core.rsns.length := by get_elem_tactic
                                rwa [hsh_eq (Or.inr rfl), ← hsh_eq (Or.inl rfl)]
                              have hst1_raw :
                                  (BitVec.setWidth 64 (st.core.rsns[(BitVec.setWidth 64
                                    (st.core.trl[t.toNat] >>> (1 : Nat))).toNat]'hr_lt_nat) +
                                    3 + 1).toNat < st_p.core.arena.length := by
                                rw [hr_any (hsh_eq (Or.inr rfl)),
                                  show (3 : BitVec 64) = 3#64 from rfl,
                                  show (1 : BitVec 64) = 1#64 from rfl]
                                exact hst1_bd
                              have hr_nw : st.core.arena[(BitVec.setWidth 64
                                  (st.core.rsns[(BitVec.setWidth 64
                                    (st.core.trl[t.toNat] >>> (1 : Nat))).toNat]'hr_lt_nat) +
                                  3 + bi.setWidth 64).toNat]'(by
                                    rw [hr_any (hsh_eq (Or.inr rfl)),
                                      show (3 : BitVec 64) = 3#64 from rfl, hbi_idx]
                                    omega) = nw := hnw_raw_eq (Or.inr rfl)
                              have hstbi_raw :
                                  (BitVec.setWidth 64 (st.core.rsns[(BitVec.setWidth 64
                                    (st.core.trl[t.toNat] >>> (1 : Nat))).toNat]'hr_lt_nat) +
                                    3 + bi.setWidth 64).toNat <
                                  (st_p.core.arena.set
                                    (BitVec.setWidth 64 (st.core.rsns[(BitVec.setWidth 64
                                      (st.core.trl[t.toNat] >>> (1 : Nat))).toNat]'hr_lt_nat) +
                                      3 + 1).toNat
                                    nw).length := by
                                rw [List.length_set, hr_any (hsh_eq (Or.inr rfl)),
                                  show (3 : BitVec 64) = 3#64 from rfl, hbi_idx, hsp_ar]
                                omega
                              have hstbi_raw' :
                                  (BitVec.setWidth 64 (st.core.rsns[(BitVec.setWidth 64
                                    (st.core.trl[t.toNat] >>> (1 : Nat))).toNat]'hr_lt_nat) +
                                    3 + bi.setWidth 64).toNat <
                                  (st_p.core.arena.set
                                    (BitVec.setWidth 64 (st.core.rsns[(BitVec.setWidth 64
                                      (st.core.trl[t.toNat] >>> (1 : Nat))).toNat]'hr_lt_nat) +
                                      3 + 1).toNat
                                    (st.core.arena[(BitVec.setWidth 64
                                      (st.core.rsns[(BitVec.setWidth 64
                                        (st.core.trl[t.toNat] >>> (1 : Nat))).toNat]'hr_lt_nat) +
                                      3 + bi.setWidth 64).toNat]'(by
                                        rw [hr_any (hsh_eq (Or.inr rfl)),
                                          show (3 : BitVec 64) = 3#64 from rfl, hbi_idx]
                                        omega))).length := by
                                rw [hr_nw]; exact hstbi_raw
                              m7_hsteps_nogrp
                              let st_s : FullState :=
                                { st_p with core := { st_p.core with arena := ar_s } }
                              c0_call hUnw
                              refine ⟨c, st_s, R, rfl, hlen_s', hw_s.watches.layout,
                                (by
                                  have hr_l1_any : ∀ {x : BitVec 32} {pf}, x = r →
                                      st.core.arena[(BitVec.setWidth 64 x + 3 +
                                        1).toNat]'pf = l1 := fun hx =>
                                    (show st.core.arena[(BitVec.setWidth 64 _ + 3 + 1).toNat]'_ =
                                        st.core.arena[r.toNat + 3 + 1]'(by omega) from
                                      m7_list_getElem_of_idx (by
                                        rw [hx, show (3 : BitVec 64) = 3#64 from rfl,
                                          show (1 : BitVec 64) = 1#64 from rfl, h1_idx])).trans
                                      (by
                                        have hget : st.core.arena[r.toNat + 3 + 1]? = some l1 := by
                                          rw [← hsp_ar, List.getElem?_eq_getElem, hl1_sp]
                                        simpa only [List.getElem?_eq_getElem
                                          (show r.toNat + 3 + 1 < st.core.arena.length by omega),
                                          Option.some.injEq] using hget)
                                  rw [hr_nw, hr_l1_any (hr_any (hsh_eq (Or.inr rfl))),
                                    hr_any (hsh_eq (Or.inr rfl)),
                                    show (3 : BitVec 64) = 3#64 from rfl,
                                    show (1 : BitVec 64) = 1#64 from rfl, h1_idx, hbi_idx] at hm
                                  exact hm),
                                fun wv_u ws_u wu_u m_u hlen_u hlay_u hmw_u hm_u => ?_⟩
                              have hw_s' : FullWitnessInv c F0 F_cur
                                  { st_p.core with arena := ar_s } := hw_s
                              have hperm_s' : FullPropDecSpecs.FullArenaPermEq st0.core
                                  { st_p.core with arena := ar_s } := hperm_s
                              let st_u : FullState :=
                                { st_s with core := { st_s.core with
                                  wvec := wv_u, wstk := ws_u, wusable := wu_u } }
                              have hstu_base : st_u.core = { st0.core with
                                  wvec := wv_u, arena := ar_s, wstk := ws_u, wlen := wl_p,
                                  wusable := wu_u } := by
                                dsimp only [st_u, st_s]; rw [hsp_base, hceq_t]
                              have hstu_scr : st_u.scratch =
                                  { st0.scratch with wsort := wso_p } := by
                                dsimp only [st_u, st_s]; rw [hsp_scr, hsceq_t]
                              have hlen_u' : st_u.LengthsOk c := ⟨hlen_u.core_ok, hlen_u.scratch_ok⟩
                              have hdm_u : st_u.core.dense_mode = 0#64 := by
                                rw [hstu_base]; exact hdm0
                              have hmw_u' : ModeWatchesInv F_cur st_u.core :=
                                hmw_u F_cur hw_s'.watches
                              have hwat_u : WatchesInv F_cur st_u.core := by
                                unfold ModeWatchesInv at hmw_u'
                                simpa only [hdm_u, ↓reduceIte] using hmw_u'
                              have hperm_u :
                                  FullPropDecSpecs.FullArenaPermEq st0.core st_u.core := by
                                exact hperm_s'.trans ⟨rfl, fun q _ => ⟨rfl, rfl, .refl _⟩⟩
                              have hnw_u : FullWitnessInv c F0 F_cur
                                  (withEmptyWatchesCore c st_u.core) :=
                                fullWitnessInv_nw_congr hlen_u'.core_ok.cur_vars_le
                                  (fullWitnessInv_to_nw hlen_s'.core_ok.cur_vars_le hw_s')
                                  rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
                              have hw_u : FullWitnessInv c F0 F_cur st_u.core :=
                                fullWitnessInv_of_nw hnw_u hdm_u hwat_u
                              have h2cv_u : 2 * st_u.core.cur_vars < 2 ^ 31 - 1 := by
                                have := hlen_u'.core_ok.cur_vars_le; omega
                              have hol_lt_u : ol.toNat < 2 * st_u.core.cur_vars := by
                                rw [hstu_base]; change ol.toNat < 2 * st0.core.cur_vars
                                rw [← hcv_eq]; exact hol_lt
                              have hnw_lt_u : nw.toNat < 2 * st_u.core.cur_vars := by
                                rw [hstu_base]; change nw.toNat < 2 * st0.core.cur_vars
                                rw [← hcv_eq]; exact hnw_ltv
                              have href_u : r.toNat ∈ fullArenaClauseRefsCore st_u.core := by
                                rw [hperm_u.1, ← hperm_t.1]; exact href
                              have hwv_u_len := hlen_u'.core_ok.wvec_len
                              have hshl_ol :
                                  (BitVec.setWidth 64 ol <<< 1).toNat = 2 * ol.toNat := by
                                rw [m5_bv64_shl1_nat _ (by
                                  rw [BitVec.toNat_setWidth,
                                    Nat.mod_eq_of_lt (Nat.lt_trans ol.isLt (by decide))]
                                  omega)]
                                rw [BitVec.toNat_setWidth,
                                  Nat.mod_eq_of_lt (Nat.lt_trans ol.isLt (by decide))]
                              have h2ol1 : ((BitVec.setWidth 64 ol <<< 1) + (1 : BitVec 64)).toNat =
                                  2 * ol.toNat + 1 := by
                                rw [m5_bv64_add1_nat _ (by rw [hshl_ol]; omega), hshl_ol]
                              have hm_u' : (FullMem c st_u ⋆ R) m_u := hm_u
                              clear hm_u
                              have hol_idx_u0 :
                                  (BitVec.setWidth 64 st.core.trl[t.toNat] <<< 1).toNat <
                                    st_u.core.wvec.length := by
                                rw [hol_get, hshl_ol, hwv_u_len]; omega
                              have hol_idx_u1 :
                                  ((BitVec.setWidth 64 st.core.trl[t.toNat] <<< 1) + 1).toNat <
                                    st_u.core.wvec.length := by
                                rw [hol_get, h2ol1, hwv_u_len]; omega
                              have hwv_off_raw :
                                  st_u.core.wvec[(BitVec.setWidth 64
                                    st.core.trl[t.toNat] <<< 1).toNat]'hol_idx_u0 =
                                  st_u.core.wvec[(BitVec.setWidth 64 ol <<< 1).toNat]'(by
                                    rw [hshl_ol, hwv_u_len]; omega) :=
                                m7_list_getElem_of_idx (by rw [hol_get])
                              have hwv_sz_raw :
                                  st_u.core.wvec[((BitVec.setWidth 64
                                    st.core.trl[t.toNat] <<< 1) + 1).toNat]'hol_idx_u1 =
                                  st_u.core.wvec[((BitVec.setWidth 64 ol <<< 1) +
                                    (1 : BitVec 64)).toNat]'(by rw [h2ol1, hwv_u_len]; omega) :=
                                m7_list_getElem_of_idx (by rw [hol_get])
                              m7_hsteps_nogrp
                              rw [hwv_off_raw, hwv_sz_raw, hnw_raw_eq (Or.inr rfl),
                                hr_any (hsh_eq (Or.inr rfl))]
                              refine m5_loop4_sz_wp hdm_u hmw_u' hlen_u' h2cv_u hol_lt_u hnw_lt_u
                                rfl hcr_lt31 href_u ?_ ?_ hm_u' ?_
                              · dsimp only; rw [bv_c0_zext32_64]; unfold fullWatchOffCore
                                rw [List.getElem?_eq_getElem (by rw [hwv_u_len]; omega),
                                  Option.getD_some]
                                exact congrArg BitVec.toNat (m7_list_getElem_of_idx hshl_ol)
                              · dsimp only; rw [bv_c0_zext32_64]; unfold fullWatchSizeCore
                                rw [List.getElem?_eq_getElem (by rw [hwv_u_len]; omega),
                                  Option.getD_some]
                                exact congrArg BitVec.toNat (m7_list_getElem_of_idx h2ol1)
                              · rintro _ ml_f ⟨ws_f, hm_f, hws_fl, hmw_f⟩
                                let st_f : FullState :=
                                  { st_u with core := { st_u.core with wstk := ws_f } }
                                have hlen_f : st_f.LengthsOk c :=
                                  ⟨{ hlen_u'.core_ok with wstk_len_arr := hws_fl },
                                   hlen_u'.scratch_ok⟩
                                have hdm_f : st_f.core.dense_mode = 0#64 := hdm_u
                                have hwat_f : WatchesInv F_cur st_f.core := by
                                  unfold ModeWatchesInv at hmw_f
                                  rw [ite_eq_left hdm_u] at hmw_f; exact hmw_f
                                have hnw_f : FullWitnessInv c F0 F_cur
                                    (withEmptyWatchesCore c st_f.core) :=
                                  fullWitnessInv_nw_congr hlen_f.core_ok.cur_vars_le
                                    (fullWitnessInv_to_nw hlen_u'.core_ok.cur_vars_le hw_u)
                                    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
                                have hw_f : FullWitnessInv c F0 F_cur st_f.core :=
                                  fullWitnessInv_of_nw hnw_f hdm_f hwat_f
                                have hperm_f :
                                    FullPropDecSpecs.FullArenaPermEq st0.core st_f.core :=
                                  hperm_u.trans ⟨rfl, fun q _ => ⟨rfl, rfl, .refl _⟩⟩
                                m7_hsteps_nogrp
                                exact hJs () ml_f (ih_out (t + 1#64, ()) ml_f hrem_dec
                                  ⟨st_f, ⟨hlen_f, hw_f, ⟨wv_u, ar_s, ws_f, wl_p, wu_u, by
                                      dsimp only [st_f]; rw [hstu_base]⟩,
                                    ⟨wso_p, by dsimp only [st_f]; exact hstu_scr⟩,
                                    hperm_f, htp1_le⟩, hm_f⟩)
                            · m7_hsteps_nogrp
                              exact m7_chrono_oom_ret hQ (by rw [hsd_c, hceq_t])
                                (by rw [hsd_sc, hsceq_t]) hsd_dm hperm_d
                                hlen_p hw_p (by assumption)
                          · intro J_d hJ_d
                            exact m5_wstack_ensure2_ret_false_wp hDefrag hlen_t hdm_t hw_t.watches
                              hml
                              (fun s_i wv_i ws_i wl_i wu_i wso_i ml_o hsi_c hsi_sc hlen_i
                                  hmw_i hm_o => by
                                let st_o : FullState :=
                                  { core :=
                                      { st0.core with
                                        wvec := wv_i, arena := ar_t, wstk := ws_i,
                                        wlen := wl_i, wusable := wu_i, oom := 1#64 },
                                    scratch := { st0.scratch with wsort := wso_i } }
                                have hsto_c : st_o.core = { s_i.core with oom := 1#64 } := by
                                  dsimp only [st_o]; rw [hsi_c, hceq_t]
                                have hsto_sc : st_o.scratch = s_i.scratch := by
                                  dsimp only [st_o]; rw [hsi_sc, hsceq_t]
                                have hlen_o : st_o.LengthsOk c :=
                                  ⟨by rw [hsto_c]; exact { hlen_i.core_ok with
                                        vals_len := hlen_i.core_ok.vals_len },
                                   by rw [hsto_sc]; exact hlen_i.scratch_ok⟩
                                have hdm_i : s_i.core.dense_mode = 0#64 := by
                                  rw [hsi_c]; exact hdm_t
                                have hdm_o : st_o.core.dense_mode = 0#64 := by
                                  rw [hsto_c]; exact hdm_i
                                have hmw_o : ModeWatchesInv F_cur st_o.core := by
                                  rw [hsto_c]
                                  exact hmw_i.with_wstk rfl rfl rfl rfl rfl (fun _ h => h)
                                have hwat_o : WatchesInv F_cur st_o.core := by
                                  unfold ModeWatchesInv at hmw_o
                                  simpa only [hdm_o, ↓reduceIte] using hmw_o
                                have hnw_o : FullWitnessInv c F0 F_cur
                                    (withEmptyWatchesCore c st_o.core) :=
                                  fullWitnessInv_nw_congr hlen_o.core_ok.cur_vars_le
                                    (fullWitnessInv_to_nw hcv_le hw_t)
                                    (by rw [hsto_c, hsi_c]) (by rw [hsto_c, hsi_c])
                                    (by rw [hsto_c, hsi_c]) (by rw [hsto_c, hsi_c])
                                    (by rw [hsto_c, hsi_c]) (by rw [hsto_c, hsi_c])
                                    (by rw [hsto_c, hsi_c]) (by rw [hsto_c, hsi_c])
                                    (by rw [hsto_c, hsi_c]) (by rw [hsto_c, hsi_c])
                                    (by rw [hsto_c, hsi_c]) (by rw [hsto_c, hsi_c])
                                    (by rw [hsto_c, hsi_c])
                                have hw_o := fullWitnessInv_of_nw hnw_o hdm_o hwat_o
                                have hperm_o :
                                    FullPropDecSpecs.FullArenaPermEq st0.core st_o.core := by
                                  rw [hsto_c, hsi_c]; exact ⟨hperm_t.1, hperm_t.2⟩
                                exact hQ false wv_i ar_t ws_i wl_i wu_i 1#64 wso_i ml_o
                                  hlen_o hw_o hperm_o (fun hf => by cases hf) (fun _ => rfl)
                                  (m5_fullMem_of_eq hm_o hsto_c.symm hsto_sc.symm))
                              (fun _ ml_d ⟨s_d, wv_d, ws_d, wl_d, wu_d, wso_d, hsd_c, hsd_sc,
                                  hlen_d, hmw_d, hm_d⟩ => by
                                have hdm_d : s_d.core.dense_mode = 0#64 := by
                                  rw [hsd_c]; exact hdm_t
                                have hwat_d : WatchesInv F_cur s_d.core := by
                                  unfold ModeWatchesInv at hmw_d
                                  simpa only [hdm_d, ↓reduceIte] using hmw_d
                                have hnw_d : FullWitnessInv c F0 F_cur
                                    (withEmptyWatchesCore c s_d.core) :=
                                  fullWitnessInv_nw_congr hlen_d.core_ok.cur_vars_le
                                    (fullWitnessInv_to_nw hcv_le hw_t)
                                    (by rw [hsd_c]) (by rw [hsd_c]) (by rw [hsd_c])
                                    (by rw [hsd_c]) (by rw [hsd_c]) (by rw [hsd_c])
                                    (by rw [hsd_c]) (by rw [hsd_c]) (by rw [hsd_c])
                                    (by rw [hsd_c]) (by rw [hsd_c]) (by rw [hsd_c])
                                    (by rw [hsd_c])
                                have hw_d := fullWitnessInv_of_nw hnw_d hdm_d hwat_d
                                exact hJ_d () ml_d ⟨s_d, wv_d, ws_d, wl_d, wu_d, wso_d,
                                  hsd_c, hsd_sc, hlen_d, hw_d, hm_d⟩)
                        · m7_hsteps_nogrp
                          exact hJs () ml (ih_out (t + 1#64, ()) ml hrem_dec
                            ⟨st, ⟨hlen_t, hw_t, ⟨_, _, _, _, _, hceq_t⟩, ⟨_, hsceq_t⟩,
                              hperm_t, htp1_le⟩, hml⟩)
      · m7_hsteps_nogrp
        have hlen_exit :
            ({ core :=
                { st0.core with
                  wvec := wv_t, arena := ar_t, wstk := ws_t,
                  wlen := wl_t, wusable := wu_t },
               scratch := { st0.scratch with wsort := wso_t } } : FullState).LengthsOk c :=
          ⟨by rw [← hceq_t]; exact hlen_t.core_ok,
           by rw [← hsceq_t]; exact hlen_t.scratch_ok⟩
        exact hQ true wv_t ar_t ws_t wl_t wu_t st0.core.oom wso_t ml
          hlen_exit (by rw [← hceq_t]; exact hw_t) (by rw [← hceq_t]; exact hperm_t)
          (fun _ => rfl) (fun hf => by cases hf)
          (m5_fullMem_of_eq hml hceq_t hsceq_t)

/-! ## 4. Inline Replacement Watch-Push & Clause-Swap Lemmas for M7 -/

/-- Branch 1 of inline watch push (`rsz = 0 ∧ wlen + 2 ≤ c.wcap`) preserves `WatchStackLayout`
and produces the postconditions consumed by `s15_flush_step_preserves`. -/
theorem m7_repl_empty_layout {c : FullCfg} {k : FullCoreState}
    (hlay : WatchStackLayout k) (hlen : k.LengthsOk c) {not_lit : Nat} {lit w0 cref : BitVec 32}
    (hlit : lit.toNat < 2 * k.cur_vars) (hnot : not_lit < 2 * k.cur_vars)
    (hnot_sz : 0 < fullWatchSizeCore k not_lit)
    (hrsz0 : fullWatchSizeCore k lit.toNat = 0)
    (hfit2 : k.wlen + 2 ≤ c.wcap)
    (hw0_f : (w0 &&& 0x80000000#32) = 0#32) (hcr_lt : cref.toNat < 0x80000000) :
    let wend := k.wlen
    let k' : FullCoreState :=
      { k with
        wstk := (k.wstk.set wend w0).set (wend + 1) cref
        wvec := (k.wvec.set (2 * lit.toNat) (BitVec.ofNat 32 wend)).set
          (2 * lit.toNat + 1) 2#32
        wlen := wend + 2 }
    k'.LengthsOk c ∧ WatchStackLayout k' ∧
    (∀ l, l ≠ lit.toNat → fullWatchOffCore k' l = fullWatchOffCore k l) ∧
    (∀ l < 2 * k.cur_vars, l ≠ lit.toNat →
      fullWatchSizeCore k' l = fullWatchSizeCore k l ∧
      ∀ j < fullWatchSizeCore k l,
        k'.wstk[fullWatchOffCore k' l + j]? = k.wstk[fullWatchOffCore k l + j]?) ∧
    fullWatchSizeCore k' lit.toNat = fullWatchSizeCore k lit.toNat + 2 ∧
    (∀ j < fullWatchSizeCore k lit.toNat,
      k'.wstk[fullWatchOffCore k' lit.toNat + j]? =
        k.wstk[fullWatchOffCore k lit.toNat + j]?) ∧
    k'.wstk[fullWatchOffCore k' lit.toNat + fullWatchSizeCore k lit.toNat]? = some w0 ∧
    k'.wstk[fullWatchOffCore k' lit.toNat + fullWatchSizeCore k lit.toNat + 1]? = some cref := by
  intro wend k'
  have hwc := c.hwcap; have hmaxv := c.hmaxv; unfold dimacsBound at hwc hmaxv
  have hcv := hlen.cur_vars_le; have hwv := hlen.wvec_len; have hws := hlen.wstk_len_arr
  have hw_pos : 1 ≤ k.wlen := by
    have h1 := hlay.pos_off not_lit hnot hnot_sz
    have h2 := hlay.bounds not_lit hnot
    omega
  have hwend_32 : wend < 2 ^ 32 := by dsimp [wend]; omega
  have h2l_lt : 2 * lit.toNat < k.wvec.length := by rw [hwv]; omega
  have h2l1_lt : 2 * lit.toNat + 1 < k.wvec.length := by rw [hwv]; omega
  have hw0_lt : wend < k.wstk.length := by rw [hws]; dsimp [wend]; omega
  have hw1_lt : wend + 1 < k.wstk.length := by rw [hws]; dsimp [wend]; omega
  have hoff_lit : fullWatchOffCore k' lit.toNat = wend := by
    unfold fullWatchOffCore; dsimp [k']
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_self h2l_lt, Option.getD_some,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt hwend_32]
  have hsz_lit : fullWatchSizeCore k' lit.toNat = 2 := by
    unfold fullWatchSizeCore; dsimp [k']
    rw [List.getElem?_set_self (by rw [List.length_set]; exact h2l1_lt), Option.getD_some]
    rfl
  have hoff_ne : ∀ l, l ≠ lit.toNat → fullWatchOffCore k' l = fullWatchOffCore k l := by
    intro l hne; unfold fullWatchOffCore; dsimp [k']
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
  have hsz_ne : ∀ l, l ≠ lit.toNat → fullWatchSizeCore k' l = fullWatchSizeCore k l := by
    intro l hne; unfold fullWatchSizeCore; dsimp [k']
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
  have hwstk_ne : ∀ j < wend, k'.wstk[j]? = k.wstk[j]? := by
    intro j hj; dsimp [k']
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
  have hlen' : k'.LengthsOk c :=
    { hlen with
      wstk_len_arr := by simp [k', hws]
      wvec_len := by simp [k', hwv]
      wlen_le := by dsimp [k', wend]; exact hfit2 }
  have hlay' : WatchStackLayout k' := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro l hl
      by_cases hll : l = lit.toNat
      · subst hll; rw [hoff_lit, hsz_lit]; dsimp [k']; omega
      · rw [hoff_ne l hll, hsz_ne l hll]
        exact Nat.le_trans (hlay.bounds l hl) (by dsimp [k']; omega)
    · intro l hl hpos
      by_cases hll : l = lit.toNat
      · subst hll; rw [hoff_lit]; exact hw_pos
      · rw [hoff_ne l hll]; rw [hsz_ne l hll] at hpos; exact hlay.pos_off l hl hpos
    · intro l1 l2 h1 h2 hne hp1 hp2
      by_cases hl1 : l1 = lit.toNat
      · subst hl1; have hl2 : l2 ≠ lit.toNat := hne.symm
        rw [hsz_ne l2 hl2] at hp2 ⊢
        rw [hoff_lit, hoff_ne l2 hl2]
        exact Or.inr (hlay.bounds l2 h2)
      · by_cases hl2 : l2 = lit.toNat
        · subst hl2
          rw [hsz_ne l1 hl1] at hp1 ⊢
          rw [hoff_ne l1 hl1, hoff_lit]
          exact Or.inl (hlay.bounds l1 h1)
        · rw [hsz_ne l1 hl1] at hp1 ⊢
          rw [hsz_ne l2 hl2] at hp2 ⊢
          rw [hoff_ne l1 hl1, hoff_ne l2 hl2]
          exact hlay.disjoint l1 l2 h1 h2 hne hp1 hp2
    · intro l hl idx hidx
      by_cases hll : l = lit.toNat
      · subst hll; rw [hsz_lit] at hidx; rw [hoff_lit]
        rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_of_lt_of_eq hidx rfl) with h0 | rfl
        · have hi0 : idx = 0 := by omega
          subst hi0; dsimp [k']
          rw [List.getElem?_set_ne (by omega), List.getElem?_set_self hw0_lt]
          intro heq; have h := Option.some.inj heq
          rw [h] at hw0_f; exact absurd hw0_f (by decide)
        · dsimp [k']
          rw [List.getElem?_set_self (by rw [List.length_set]; exact hw1_lt)]
          intro heq; have h := Option.some.inj heq
          rw [h] at hcr_lt; revert hcr_lt; decide
      · rw [hsz_ne l hll] at hidx; rw [hoff_ne l hll]
        have hb := hlay.bounds l hl
        rw [hwstk_ne (fullWatchOffCore k l + idx) (by omega)]
        exact hlay.no_sentinel l hl idx hidx
  refine ⟨hlen', hlay', hoff_ne, ?_, by rw [hsz_lit, hrsz0], fun j hj => by omega, ?_, ?_⟩
  · intro l hl hne
    refine ⟨hsz_ne l hne, fun j hj => ?_⟩
    rw [hoff_ne l hne]
    exact hwstk_ne _ (Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj _) (hlay.bounds l hl))
  · rw [hoff_lit, hrsz0, Nat.add_zero]
    dsimp [k']; rw [List.getElem?_set_ne (by omega), List.getElem?_set_self hw0_lt]
  · rw [hoff_lit, hrsz0, Nat.add_zero]
    dsimp [k']; rw [List.getElem?_set_self (by rw [List.length_set]; exact hw1_lt)]

/-- Replacement inline push (Branch 1: `rsz = 0 ∧ wlen + 2 ≤ wcap`) preserves `PropLitInv`. -/
theorem m7_repl_empty_step {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s _sem sem1 st3 : FullState} {not_lit other repl_f cref : BitVec 32}
    {off0_v p_v q_v end0_v : BitVec 64}
    (hpi1 : PropLitInv c F0 F_cur s sem1 not_lit.toNat
      off0_v.toNat q_v.toNat (p_v.toNat + 2) end0_v.toNat)
    (hst3_core_eq : st3.core = { sem1.core with arena := st3.core.arena })
    (hst3_sc_eq : st3.scratch = sem1.scratch)
    (hlen3 : st3.LengthsOk c)
    (hnw3 : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c st3.core))
    (hsw3 : SplitWatchesInv F_cur st3.core not_lit.toNat off0_v.toNat q_v.toNat
      (p_v.toNat + 2) end0_v.toNat)
    (hperm13 : FullPropDecSpecs.FullArenaPermEq sem1.core st3.core)
    (hcr_lt : cref.toNat < 0x80000000) (hcr_ref3 : cref.toNat ∈ fullArenaClauseRefsCore st3.core)
    (hrepl_lt3 : repl_f.toNat < 2 * st3.core.cur_vars)
    (hrepl_ne_not : repl_f.toNat ≠ not_lit.toNat)
    (hnot_st3 : not_lit.toNat < 2 * st3.core.cur_vars)
    (hrsz0 : fullWatchSizeCore st3.core repl_f.toNat = 0)
    (hfit2 : st3.core.wlen + 2 ≤ c.wcap)
    (hq_le_p : q_v.toNat ≤ p_v.toNat)
    (hp2_nat : (p_v + 1#64 + 1#64).toNat = p_v.toNat + 2) :
    let wend := st3.core.wlen
    let st4 : FullState :=
      { st3 with core :=
        { st3.core with
          wstk := (st3.core.wstk.set wend (other &&& 0x7FFFFFFF#32)).set (wend + 1) cref
          wvec := (st3.core.wvec.set (2 * repl_f.toNat) (BitVec.ofNat 32 wend)).set
            (2 * repl_f.toNat + 1) 2#32
          wlen := wend + 2 } }
    PropLitInv c F0 F_cur s st4 not_lit.toNat off0_v.toNat
      q_v.toNat (p_v + 1#64 + 1#64).toNat end0_v.toNat := by
  intro wend st4
  have hnot_sz : 0 < fullWatchSizeCore st3.core not_lit.toNat := by
    have hq_ge := hsw3.q_ge; have hp_end := hsw3.p_le_end
    rw [hsw3.sz_eq]; omega
  have hwo_st3 : fullWatchOffCore st3.core not_lit.toNat = off0_v.toNat := hsw3.off_eq
  have ⟨hlen4c, hlay4, hwo4, hpres4, hsz4, hpre4, hw0_4, hw1_4⟩ :=
    m7_repl_empty_layout hsw3.layout hlen3.core_ok hrepl_lt3 hnot_st3 hnot_sz hrsz0 hfit2
      (bv32_mask7f_flag0 other) hcr_lt
  have hsw4_raw := (s15_flush_step_preserves (k := st3.core) (k' := st4.core)
    (lit := repl_f) (w0 := other &&& 0x7FFFFFFF#32) (cref := cref) (skip_lit := not_lit.toNat)
    rfl rfl hlay4 hrepl_lt3 (bv32_mask7f_flag0 other) hcr_lt hcr_ref3 hpres4
    ⟨hsz4, hpre4, hw0_4, hw1_4⟩).2 hrepl_ne_not hnot_st3 _ _ _ _ hsw3
  have hoff4_eq : fullWatchOffCore st4.core not_lit.toNat = off0_v.toNat := by
    have h := hwo4 not_lit.toNat (Ne.symm hrepl_ne_not); simpa only [hwo_st3] using h
  have hsw4 : SplitWatchesInv F_cur st4.core not_lit.toNat off0_v.toNat q_v.toNat
      (p_v.toNat + 2) end0_v.toNat := by
    dsimp only at hsw4_raw
    have hq_ge := hsw3.q_ge; have hq_le := hsw3.q_le_p; have hp_le := hsw3.p_le_end
    rw [hoff4_eq,
      show off0_v.toNat + (q_v.toNat - off0_v.toNat) = q_v.toNat by omega,
      show off0_v.toNat + (p_v.toNat + 2 - off0_v.toNat) = p_v.toNat + 2 by omega,
      show off0_v.toNat + (end0_v.toNat - off0_v.toNat) = end0_v.toNat by omega] at hsw4_raw
    exact hsw4_raw
  have hlen4 : st4.LengthsOk c := ⟨hlen4c, hlen3.scratch_ok⟩
  have hnw4 : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c st4.core) :=
    fullWitnessInv_nw_congr hlen4.core_ok.cur_vars_le hnw3
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have hag4 : AgreesExcept propLitCoreMask s.core st4.core := by
    have hag1 := hpi1.ag.update (fun k => { k with
      arena := st3.core.arena, wstk := st4.core.wstk, wvec := st4.core.wvec, wlen := wend + 2 })
    have hcore4 : st4.core = { sem1.core with
        arena := st3.core.arena, wstk := st4.core.wstk, wvec := st4.core.wvec,
        wlen := wend + 2 } := by dsimp only [st4]; rw [hst3_core_eq]
    rw [hcore4]; exact hag1
  exact
    { len := hlen4, nw := hnw4, sw := hp2_nat.symm ▸ hsw4
      ag := hag4
      tr := hpi1.tr.congr (by dsimp only [st4]; rw [hst3_core_eq])
        (by dsimp only [st4]; rw [hst3_core_eq]) (by dsimp only [st4]; rw [hst3_core_eq])
      perm := hpi1.perm.trans hperm13
      sc_eq := by dsimp only [st4]; rw [hst3_sc_eq, hpi1.sc_eq]
      not_f := by dsimp only [st4]; rw [hst3_core_eq]; exact hpi1.not_f }

/-- Replacement inline push (Branch 2: `roff + rsz = wlen ∧ wlen + 2 ≤ wcap`). -/
theorem m7_repl_end_step {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s sem1 st3 : FullState} {not_lit other repl_f cref : BitVec 32}
    {off0_v p_v q_v end0_v rwend_v : BitVec 64}
    (hpi1 : PropLitInv c F0 F_cur s sem1 not_lit.toNat
      off0_v.toNat q_v.toNat (p_v.toNat + 2) end0_v.toNat)
    (hst3_core_eq : st3.core = { sem1.core with arena := st3.core.arena })
    (hst3_sc_eq : st3.scratch = sem1.scratch)
    (hlen3 : st3.LengthsOk c)
    (hnw3 : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c st3.core))
    (hsw3 : SplitWatchesInv F_cur st3.core not_lit.toNat off0_v.toNat q_v.toNat
      (p_v.toNat + 2) end0_v.toNat)
    (hperm13 : FullPropDecSpecs.FullArenaPermEq sem1.core st3.core)
    (hcr_lt : cref.toNat < 0x80000000) (hcr_ref3 : cref.toNat ∈ fullArenaClauseRefsCore st3.core)
    (hrepl_lt3 : repl_f.toNat < 2 * st3.core.cur_vars)
    (hrepl_ne_not : repl_f.toNat ≠ not_lit.toNat)
    (hnot_st3 : not_lit.toNat < 2 * st3.core.cur_vars)
    (hrsz_pos : 0 < fullWatchSizeCore st3.core repl_f.toNat)
    (hend_wlen : fullWatchOffCore st3.core repl_f.toNat +
      fullWatchSizeCore st3.core repl_f.toNat = st3.core.wlen)
    (hfit2 : st3.core.wlen + 2 ≤ c.wcap)
    (hrwend_nat : rwend_v.toNat =
      fullWatchOffCore st3.core repl_f.toNat + fullWatchSizeCore st3.core repl_f.toNat)
    (hp2_nat : (p_v + 1#64 + 1#64).toNat = p_v.toNat + 2) :
    let st4 : FullState :=
      { st3 with core := { st3.core with
          wstk := (st3.core.wstk.set rwend_v.toNat
            (other &&& 0x7FFFFFFF#32)).set (rwend_v.toNat + 1) cref
          wvec := st3.core.wvec.set (2 * repl_f.toNat + 1)
            (BitVec.ofNat 32 (fullWatchSizeCore st3.core repl_f.toNat + 2))
          wlen := rwend_v.toNat + 2 } }
    PropLitInv c F0 F_cur s st4 not_lit.toNat off0_v.toNat
      q_v.toNat (p_v + 1#64 + 1#64).toNat end0_v.toNat := by
  intro st4
  have hq_ge := hsw3.q_ge; have hq_le := hsw3.q_le_p; have hp_le := hsw3.p_le_end
  have hroff_pos : 0 < fullWatchOffCore st3.core repl_f.toNat :=
    hsw3.layout.pos_off repl_f.toNat hrepl_lt3 hrsz_pos
  have hwo_st3 : fullWatchOffCore st3.core not_lit.toNat = off0_v.toNat := hsw3.off_eq
  have ⟨hlen4c, hlay4, hwo4, hpres4, hsz4, hpre4, hw0_4, hw1_4⟩ :=
    s15_append_end_layout hsw3.layout hlen3.core_ok hrepl_lt3 hroff_pos hend_wlen hfit2
      (bv32_mask7f_flag0 other) hcr_lt
  have hsw4_raw := (s15_flush_step_preserves (k := st3.core) (k' := st4.core)
    (lit := repl_f) (w0 := other &&& 0x7FFFFFFF#32) (cref := cref) (skip_lit := not_lit.toNat)
    rfl rfl (by simpa [st4, hrwend_nat, hend_wlen] using hlay4) hrepl_lt3
    (bv32_mask7f_flag0 other) hcr_lt hcr_ref3
    (by simpa [st4, hrwend_nat, hend_wlen] using hpres4)
    ⟨by simpa [st4, hrwend_nat, hend_wlen] using hsz4,
     by simpa [st4, hrwend_nat, hend_wlen] using hpre4,
     by simpa [st4, hrwend_nat, hend_wlen] using hw0_4,
     by simpa [st4, hrwend_nat, hend_wlen] using hw1_4⟩).2
    hrepl_ne_not hnot_st3 _ _ _ _ hsw3
  have hoff4_eq : fullWatchOffCore st4.core not_lit.toNat = off0_v.toNat := by
    have h := hwo4 not_lit.toNat; simpa only [st4, hrwend_nat, hend_wlen, hwo_st3] using h
  have hsw4 : SplitWatchesInv F_cur st4.core not_lit.toNat off0_v.toNat q_v.toNat
      (p_v.toNat + 2) end0_v.toNat := by
    dsimp only at hsw4_raw
    rw [hoff4_eq,
      show off0_v.toNat + (q_v.toNat - off0_v.toNat) = q_v.toNat by omega,
      show off0_v.toNat + (p_v.toNat + 2 - off0_v.toNat) = p_v.toNat + 2 by omega,
      show off0_v.toNat + (end0_v.toNat - off0_v.toNat) = end0_v.toNat by omega] at hsw4_raw
    exact hsw4_raw
  have hlen4 : st4.LengthsOk c :=
    ⟨by simpa [st4, hrwend_nat, hend_wlen] using hlen4c, hlen3.scratch_ok⟩
  have hnw4 : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c st4.core) :=
    fullWitnessInv_nw_congr hlen4.core_ok.cur_vars_le hnw3
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have hag4 : AgreesExcept propLitCoreMask s.core st4.core := by
    have hag1 := hpi1.ag.update (fun k => { k with
      arena := st3.core.arena, wstk := st4.core.wstk,
      wvec := st4.core.wvec, wlen := st4.core.wlen })
    have hcore4 : st4.core = { sem1.core with
        arena := st3.core.arena, wstk := st4.core.wstk, wvec := st4.core.wvec,
        wlen := st4.core.wlen } := by dsimp only [st4]; rw [hst3_core_eq]
    rw [hcore4]; exact hag1
  exact
    { len := hlen4, nw := hnw4, sw := hp2_nat.symm ▸ hsw4
      ag := hag4
      tr := hpi1.tr.congr (by dsimp only [st4]; rw [hst3_core_eq])
        (by dsimp only [st4]; rw [hst3_core_eq]) (by dsimp only [st4]; rw [hst3_core_eq])
      perm := hpi1.perm.trans hperm13
      sc_eq := by dsimp only [st4]; rw [hst3_sc_eq, hpi1.sc_eq]
      not_f := by dsimp only [st4]; rw [hst3_core_eq]; exact hpi1.not_f }

/-- Replacement inline push (Branch 3: trailing sentinel pair `[0xFFFFFFFFu, 0xFFFFFFFFu]`). -/
theorem m7_repl_sentinel_step {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s sem1 st3 : FullState} {not_lit other repl_f cref : BitVec 32}
    {off0_v p_v q_v end0_v rwend_v wu' : BitVec 64}
    (hpi1 : PropLitInv c F0 F_cur s sem1 not_lit.toNat
      off0_v.toNat q_v.toNat (p_v.toNat + 2) end0_v.toNat)
    (hst3_core_eq : st3.core = { sem1.core with arena := st3.core.arena })
    (hst3_sc_eq : st3.scratch = sem1.scratch)
    (hlen3 : st3.LengthsOk c)
    (hnw3 : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c st3.core))
    (hsw3 : SplitWatchesInv F_cur st3.core not_lit.toNat off0_v.toNat q_v.toNat
      (p_v.toNat + 2) end0_v.toNat)
    (hperm13 : FullPropDecSpecs.FullArenaPermEq sem1.core st3.core)
    (hcr_lt : cref.toNat < 0x80000000) (hcr_ref3 : cref.toNat ∈ fullArenaClauseRefsCore st3.core)
    (hrepl_lt3 : repl_f.toNat < 2 * st3.core.cur_vars)
    (hrepl_ne_not : repl_f.toNat ≠ not_lit.toNat)
    (hnot_st3 : not_lit.toNat < 2 * st3.core.cur_vars)
    (hrsz_pos : 0 < fullWatchSizeCore st3.core repl_f.toNat)
    (hrwend2_le : fullWatchOffCore st3.core repl_f.toNat +
      fullWatchSizeCore st3.core repl_f.toNat + 2 ≤ st3.core.wlen)
    (hsent0 : st3.core.wstk[fullWatchOffCore st3.core repl_f.toNat +
      fullWatchSizeCore st3.core repl_f.toNat]? = some 0xFFFFFFFF#32)
    (hsent1 : st3.core.wstk[fullWatchOffCore st3.core repl_f.toNat +
      fullWatchSizeCore st3.core repl_f.toNat + 1]? = some 0xFFFFFFFF#32)
    (hrwend_nat : rwend_v.toNat =
      fullWatchOffCore st3.core repl_f.toNat + fullWatchSizeCore st3.core repl_f.toNat)
    (hp2_nat : (p_v + 1#64 + 1#64).toNat = p_v.toNat + 2) :
    let st4 : FullState :=
      { st3 with core := { st3.core with
          wstk := (st3.core.wstk.set rwend_v.toNat
            (other &&& 0x7FFFFFFF#32)).set (rwend_v.toNat + 1) cref
          wvec := st3.core.wvec.set (2 * repl_f.toNat + 1)
            (BitVec.ofNat 32 (fullWatchSizeCore st3.core repl_f.toNat + 2))
          wusable := wu' } }
    PropLitInv c F0 F_cur s st4 not_lit.toNat off0_v.toNat
      q_v.toNat (p_v + 1#64 + 1#64).toNat end0_v.toNat := by
  intro st4
  have hq_ge := hsw3.q_ge; have hq_le := hsw3.q_le_p; have hp_le := hsw3.p_le_end
  have hroff_pos : 0 < fullWatchOffCore st3.core repl_f.toNat :=
    hsw3.layout.pos_off repl_f.toNat hrepl_lt3 hrsz_pos
  have hwo_st3 : fullWatchOffCore st3.core not_lit.toNat = off0_v.toNat := hsw3.off_eq
  have ⟨hlen4c, hlay4, hwo4, hpres4, hsz4, hpre4, hw0_4, hw1_4⟩ :=
    s15_append_sentinel_layout (wu' := wu') hsw3.layout hlen3.core_ok
      hrepl_lt3 hroff_pos hrwend2_le hsent0 hsent1 (bv32_mask7f_flag0 other) hcr_lt
  have hsw4_raw := (s15_flush_step_preserves (k := st3.core) (k' := st4.core)
    (lit := repl_f) (w0 := other &&& 0x7FFFFFFF#32) (cref := cref) (skip_lit := not_lit.toNat)
    rfl rfl (by simpa [st4, hrwend_nat] using hlay4) hrepl_lt3 (bv32_mask7f_flag0 other)
    hcr_lt hcr_ref3 (by simpa [st4, hrwend_nat] using hpres4)
    ⟨by simpa [st4, hrwend_nat] using hsz4, by simpa [st4, hrwend_nat] using hpre4,
     by simpa [st4, hrwend_nat] using hw0_4, by simpa [st4, hrwend_nat] using hw1_4⟩).2
    hrepl_ne_not hnot_st3 _ _ _ _ hsw3
  have hoff4_eq : fullWatchOffCore st4.core not_lit.toNat = off0_v.toNat := by
    have h := hwo4 not_lit.toNat; simpa only [st4, hrwend_nat, hwo_st3] using h
  have hsw4 : SplitWatchesInv F_cur st4.core not_lit.toNat off0_v.toNat q_v.toNat
      (p_v.toNat + 2) end0_v.toNat := by
    dsimp only at hsw4_raw
    rw [hoff4_eq,
      show off0_v.toNat + (q_v.toNat - off0_v.toNat) = q_v.toNat by omega,
      show off0_v.toNat + (p_v.toNat + 2 - off0_v.toNat) = p_v.toNat + 2 by omega,
      show off0_v.toNat + (end0_v.toNat - off0_v.toNat) = end0_v.toNat by omega] at hsw4_raw
    exact hsw4_raw
  have hlen4 : st4.LengthsOk c :=
    ⟨by simpa [st4, hrwend_nat] using hlen4c, hlen3.scratch_ok⟩
  have hnw4 : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c st4.core) :=
    fullWitnessInv_nw_congr hlen4.core_ok.cur_vars_le hnw3
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have hag4 : AgreesExcept propLitCoreMask s.core st4.core := by
    have hag1 := hpi1.ag.update (fun k => { k with
      arena := st3.core.arena, wstk := st4.core.wstk, wvec := st4.core.wvec, wusable := wu' })
    have hcore4 : st4.core = { sem1.core with
        arena := st3.core.arena, wstk := st4.core.wstk, wvec := st4.core.wvec, wusable := wu' } :=
      by dsimp only [st4]; rw [hst3_core_eq]
    rw [hcore4]; exact hag1
  exact
    { len := hlen4, nw := hnw4, sw := hp2_nat.symm ▸ hsw4
      ag := hag4
      tr := hpi1.tr.congr (by dsimp only [st4]; rw [hst3_core_eq])
        (by dsimp only [st4]; rw [hst3_core_eq]) (by dsimp only [st4]; rw [hst3_core_eq])
      perm := hpi1.perm.trans hperm13
      sc_eq := by dsimp only [st4]; rw [hst3_sc_eq, hpi1.sc_eq]
      not_f := by dsimp only [st4]; rw [hst3_core_eq]; exact hpi1.not_f }

/-- `tB` watched-literal normalization: when `l0 = not_lit`, swapping `(0, 1)` puts
`[other, not_lit]` into `ar[cref + 3, cref + 4]` while preserving `PropLitInv`. -/
theorem m7_tB_swap_step {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s sem : FullState} {not_lit : BitVec 32} {cref : BitVec 32}
    {off0_v p_v q_v end0_v : BitVec 64}
    (hpi : PropLitInv c F0 F_cur s sem not_lit.toNat off0_v.toNat q_v.toNat
      (p_v.toNat + 2) end0_v.toNat)
    (hcr_ref : cref.toNat ∈ fullArenaClauseRefsCore sem.core)
    (hcsz3 : 3 ≤ fullArenaClauseSizeCore sem.core cref.toNat)
    (hfit : cref.toNat + 3 + fullArenaClauseSizeCore sem.core cref.toNat ≤ sem.core.arena_len)
    {l0 l1 : BitVec 32} (hl0 : sem.core.arena[cref.toNat + 3]? = some l0)
    (hl1 : sem.core.arena[cref.toNat + 4]? = some l1) (hl0_eq : l0 = not_lit) :
    let other := l0 ^^^ l1 ^^^ not_lit
    let sem1 : FullState :=
      { sem with core := { sem.core with
          arena := (sem.core.arena.set (cref.toNat + 3) other).set (cref.toNat + 4) not_lit } }
    other = l1 ∧
    PropLitInv c F0 F_cur s sem1 not_lit.toNat off0_v.toNat q_v.toNat
      (p_v.toNat + 2) end0_v.toNat ∧
    cref.toNat ∈ fullArenaClauseRefsCore sem1.core ∧
    fullArenaClauseSizeCore sem1.core cref.toNat = fullArenaClauseSizeCore sem.core cref.toNat ∧
    sem1.core.arena[cref.toNat + 3]? = some other ∧
    sem1.core.arena[cref.toNat + 4]? = some not_lit := by
  intro other sem1
  have hother : other = l1 := by
    dsimp only [other]; rw [hl0_eq]
    have hx : not_lit ^^^ l1 ^^^ not_lit = l1 := by
      rw [BitVec.xor_comm not_lit l1, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
    exact hx
  have haren := hpi.len.core_ok.arena_len_arr; have halen := hpi.len.core_ok.arena_len_le
  have hl0_idx : l0 = sem.core.arena[cref.toNat + 3 + 0]'(by omega) :=
    Option.some.inj (hl0.symm.trans (List.getElem?_eq_getElem (by omega)))
  have hl1_idx : l1 = sem.core.arena[cref.toNat + 3 + 1]'(by omega) :=
    Option.some.inj (hl1.symm.trans (List.getElem?_eq_getElem (by omega)))
  obtain ⟨hnw1, hperm1⟩ := full_swapLits_preserves_nw hpi.len.core_ok hpi.nw hcr_ref
    (k1 := 0) (k2 := 1) (by omega) (by omega)
  have hsem1_eq : sem1.core = { sem.core with
      arena := (sem.core.arena.set (cref.toNat + 3 + 0)
        (sem.core.arena[cref.toNat + 3 + 1]'(by omega))).set
        (cref.toNat + 3 + 1) (sem.core.arena[cref.toNat + 3 + 0]'(by omega)) } := by
    dsimp [sem1]; rw [← hl0_idx, ← hl1_idx, hl0_eq, hother]
  rw [← hsem1_eq] at hnw1 hperm1
  have hlen1 : sem1.LengthsOk c :=
    ⟨{ hpi.len.core_ok with arena_len_arr := by simp [sem1, haren] }, hpi.len.scratch_ok⟩
  have hpi1 : PropLitInv c F0 F_cur s sem1 not_lit.toNat off0_v.toNat q_v.toNat
      (p_v.toNat + 2) end0_v.toNat :=
    { len := hlen1, nw := hnw1
      sw := hpi.sw.with_nonwatch rfl rfl rfl rfl hperm1.1
      ag := hpi.ag.update (fun k => { k with arena := sem1.core.arena })
      tr := hpi.tr.congr rfl rfl rfl
      perm := hpi.perm.trans hperm1
      sc_eq := hpi.sc_eq
      not_f := hpi.not_f }
  refine ⟨hother, hpi1, hperm1.1.symm ▸ hcr_ref, (hperm1.2 cref.toNat hcr_ref).1, ?_, ?_⟩
  · dsimp [sem1]
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega)]
  · dsimp [sem1]
    rw [List.getElem?_set_self (by simp; omega)]

/-- Cold overflow path post-`full_watch_push` arena swap (`ar[obase] = ovf_other;
ar[obase + 1] = ovf_rw; ar[obase + ovf_ri] = not_lit`) preserves `PropLitInv`. -/
theorem m7_ovf_swap_step {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st_p : FullState} {not_lit other repl cref : BitVec 32} {ri : Nat}
    {off_v p2_v q_v end_v : BitVec 64}
    (hpi : PropLitInv c F0 F_cur s st_p not_lit.toNat off_v.toNat q_v.toNat p2_v.toNat end_v.toNat)
    (hcr_ref : cref.toNat ∈ fullArenaClauseRefsCore st_p.core)
    (hcsz3 : 3 ≤ fullArenaClauseSizeCore st_p.core cref.toNat)
    (hfit : cref.toNat + 3 + fullArenaClauseSizeCore st_p.core cref.toNat ≤ st_p.core.arena_len)
    (har3 : st_p.core.arena[cref.toNat + 3]? = some other)
    (har4 : st_p.core.arena[cref.toNat + 4]? = some not_lit)
    (_hri2 : 2 ≤ ri) (hri_lt : ri < fullArenaClauseSizeCore st_p.core cref.toNat)
    (hrepl : st_p.core.arena[cref.toNat + 3 + ri]? = some repl) :
    let st3 : FullState :=
      { st_p with core := { st_p.core with
          arena := ((st_p.core.arena.set (cref.toNat + 3) other).set (cref.toNat + 4) repl).set
            (cref.toNat + 3 + ri) not_lit } }
    PropLitInv c F0 F_cur s st3 not_lit.toNat off_v.toNat q_v.toNat p2_v.toNat end_v.toNat := by
  intro st3
  have haren := hpi.len.core_ok.arena_len_arr; have halen := hpi.len.core_ok.arena_len_le
  have har3_set : st_p.core.arena.set (cref.toNat + 3) other = st_p.core.arena := by
    apply List.ext_getElem (by simp)
    intro i hi1 hi2
    by_cases he : i = cref.toNat + 3
    · subst he; rw [List.getElem_set_self]
      exact Option.some.inj (har3.symm.trans (List.getElem?_eq_getElem hi2))
    · rw [List.getElem_set_ne (Ne.symm he)]
  have h1 : not_lit = st_p.core.arena[cref.toNat + 3 + 1]'(by omega) :=
    Option.some.inj (har4.symm.trans (List.getElem?_eq_getElem (by omega)))
  have hr : repl = st_p.core.arena[cref.toNat + 3 + ri]'(by omega) :=
    Option.some.inj (hrepl.symm.trans (List.getElem?_eq_getElem (by omega)))
  obtain ⟨hnw3, hperm3⟩ := full_swapLits_preserves_nw hpi.len.core_ok hpi.nw hcr_ref
    (k1 := 1) (k2 := ri) (by omega) hri_lt
  have hst3_eq : st3.core = { st_p.core with
      arena := (st_p.core.arena.set (cref.toNat + 3 + 1)
        (st_p.core.arena[cref.toNat + 3 + ri]'(by omega))).set
        (cref.toNat + 3 + ri) (st_p.core.arena[cref.toNat + 3 + 1]'(by omega)) } := by
    dsimp [st3]; rw [har3_set, ← h1, ← hr]
  rw [← hst3_eq] at hnw3 hperm3
  have hlen3 : st3.LengthsOk c :=
    ⟨{ hpi.len.core_ok with arena_len_arr := by simp [st3, haren] }, hpi.len.scratch_ok⟩
  exact
    { len := hlen3, nw := hnw3
      sw := hpi.sw.with_nonwatch rfl rfl rfl rfl hperm3.1
      ag := hpi.ag.update (fun k => { k with arena := st3.core.arena })
      tr := hpi.tr.congr rfl rfl rfl
      perm := hpi.perm.trans hperm3
      sc_eq := hpi.sc_eq
      not_f := hpi.not_f }

end LeanQbe.T.Examples.Kissat.FullM7BcpHot
