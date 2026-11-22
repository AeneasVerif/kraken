/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM5Otfs
public import LeanQbe.T.Examples.Kissat.FullM5OtfsLemmas1
public import LeanQbe.T.Examples.Kissat.FullSpec
public import LeanQbe.T.Examples.Kissat.FullPropDecLemmas2
public import LeanQbe.T.Examples.Kissat.FullFastCoreBcpLemmas
public import LeanQbe.T.Examples.Kissat.FullFastCoreLemmas
public import LeanQbe.T.Logic.C0HeadStep
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat M5 `Func.wp` Proofs — Part 2 (`full_prop_lit_chrono`, `full_prop_lit`,
  `full_propagate_ignore`)

Zero `import all LeanQbe.*`. Proves canonical `FullSpec2` contracts (`XPost := False`, UNSAT-only)
for:
1. `full_prop_lit_chrono_wp` (`Full.fullPropLitSpec`): propagates `full_prop_lit_raw`, repairs
   newly propagated trail entries `[t0 .. te)` even on non-root conflicts (`ok0 = false`),
   pre-checks watch headroom (`wcap - wlen >= 2ULL` + `full_wstack_defrag`) before mutating,
   calls `full_watch_push` then `full_unwatch_large(l1, r)` on `l1 <-> nw` swap, and updates
   `ol`'s blocker via shared `m5_loop4_sz_wp`.
2. `full_prop_lit_wp` (`Full.fullPropLitSpec`).
3. `full_propagate_ignore_wp` (`Full.fullPropagateIgnoreSpec`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM5Otfs

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0HeadStep LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full.FullAnalyzeHelpers
open Kraken.Bedrock2.Test
open LeanQbe.T.Examples.Kissat.Full hiding
  full_unwatch_large_body full_unwatch_large_wf
  full_otfs_large_body full_otfs_large_wf full_otfs_large_wp full_otfs_large_wp_weak
  full_prop_lit_body full_prop_lit_wf
  full_propagate_ignore_body full_propagate_ignore_wf
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics

/-! ## 1. Chrono-Repair Helpers & `full_prop_lit_chrono_wp` (`Full.fullPropLitSpec`) -/

section PropChronoProof

private theorem m5_bv32_rshift1_toNat (x : BitVec 32) :
    (BitVec.setWidth 64 (x >>> 1#32)).toNat = x.toNat / 2 := by
  have h1 : (x >>> 1#32).toNat < 2 ^ 32 := BitVec.isLt _
  have h2 : (x >>> 1#32).toNat = x.toNat / 2 := by
    simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega), h2]

private theorem m5_bv32_zext64_add_toNat (r : BitVec 32) {k : Nat} (hk : r.toNat + k < 2 ^ 64) :
    (r.setWidth 64 + BitVec.ofNat 64 k).toNat = r.toNat + k := by
  rw [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.le_add_right _ _) hk),
    Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega)]
  exact Nat.mod_eq_of_lt hk

private theorem m5_bv32_add1_toNat {x : BitVec 32} (hx : x.toNat + 1 < 2 ^ 32) :
    (x + 1#32).toNat = x.toNat + 1 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 1 < 2 ^ 32)]
  exact Nat.mod_eq_of_lt hx

private theorem m5_bv32_mask_lit_lt (ol : BitVec 32) :
    (ol &&& 0x7FFFFFFF#32) ≠ 0xFFFFFFFF#32 := by
  intro hff
  have h := bv32_mask7f_flag0 ol
  rw [hff] at h
  exact absurd h (by decide)

private theorem m5_bv32_bit31_zero : (0#32)[31] = false := by decide
private theorem m5_bv32_bit31_msb : (0x80000000#32)[31] = true := by decide

private theorem m5_pd_trailExt_of_canon {k1 k2 : FullCoreState}
    (h : Full.FullTrailExt k1 k2) : FullPropDecSpecs.FullTrailExt k1 k2 :=
  ⟨h.1, h.2.1, h.2.2⟩

private theorem m5_canon_trailExt_of_pd {k1 k2 : FullCoreState}
    (h : FullPropDecSpecs.FullTrailExt k1 k2) : Full.FullTrailExt k1 k2 :=
  ⟨h.te_ge, h.trl_pref, h.lvl_pres⟩

private theorem m5_canon_arenaPerm_trans {k1 k2 k3 : FullCoreState}
    (h1 : Full.FullArenaPermEq k1 k2) (h2 : Full.FullArenaPermEq k2 k3) :
    Full.FullArenaPermEq k1 k3 :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, fun r hr =>
    let ⟨s1, g1, p1⟩ := h1.2.2 r hr
    let ⟨s2, g2, p2⟩ := h2.2.2 r (h1.2.1.symm ▸ hr)
    ⟨s2.trans s1, g2.trans g1, p2.trans p1⟩⟩

private theorem m5_canon_arenaPerm_of_pd {k1 k2 : FullCoreState} (hal : k2.arena_len = k1.arena_len)
    (h : FullPropDecSpecs.FullArenaPermEq k1 k2) : Full.FullArenaPermEq k1 k2 :=
  ⟨hal, h.1, h.2⟩

private theorem m5_conflOkW_of_arenaPerm {F_cur : List (List Nat)} {st0 st : FullState}
    (hcf : Full.FullConflictOkW F_cur st0)
    (hvals : st.core.vals = st0.core.vals) (hcv : st.core.cur_vars = st0.core.cur_vars)
    (hct : st.core.confl_type = st0.core.confl_type)
    (hcr : st.core.confl_ref = st0.core.confl_ref)
    (hc0 : st.core.confl_lit0 = st0.core.confl_lit0)
    (hc1 : st.core.confl_lit1 = st0.core.confl_lit1)
    (hperm : Full.FullArenaPermEq st0.core st.core) :
    Full.FullConflictOkW F_cur st := by
  rcases hcf with ⟨ht, h0, h1, hv0, hv1, hent⟩ | ⟨ht, href, hng, hfals⟩
  · left; refine ⟨hct.trans ht, by rwa [hc0, hcv], by rwa [hc1, hcv], ?_, ?_, ?_⟩
    · rw [hvals, hc0]; exact hv0
    · rw [hvals, hc1]; exact hv1
    · rw [hc0, hc1]; exact hent
  · right
    change st0.core.confl_ref.toNat ∈ fullArenaClauseRefsCore st0.core at href
    have hprops := hperm.2.2 _ href
    refine ⟨hct.trans ht, ?_, ?_, ?_⟩
    · change st.core.confl_ref.toNat ∈ fullArenaClauseRefsCore st.core
      rw [hcr, hperm.2.1]; exact href
    · change fullArenaClauseGarbCore st.core st.core.confl_ref.toNat = false
      rw [hcr, hprops.2.1]; exact hng
    · intro l hl
      change l ∈ fullArenaClauseLitsCore st.core st.core.confl_ref.toNat at hl
      rw [hcr] at hl
      rw [hvals]
      exact hfals l (hprops.2.2.mem_iff.mp hl)

private theorem m5_prop_swap_preserves_inv {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {k0 k : FullCoreState} (hlen : k.LengthsOk c)
    (hw : FullWitnessInv c F0 F_cur k) (hdm : k.dense_mode = 0#64)
    (hperm0 : Full.FullArenaPermEq k0 k) {r bi : Nat} (href : r ∈ fullArenaClauseRefsCore k)
    (hbi_ge : 2 ≤ bi) (hbi_lt : bi < fullArenaClauseSizeCore k r) :
    have hbd : r + 3 + fullArenaClauseSizeCore k r ≤ k.arena.length := by
      have h1 := (hw.arena.refs_wf r href).2.2.1
      have h2 := (hw.arena.refs_wf r href).2.2.2.1
      have h3 := hlen.arena_len_le; have h4 := hlen.arena_len_arr; omega
    let l1 := k.arena[r + 3 + 1]'(by omega)
    let nw := k.arena[r + 3 + bi]'(by omega)
    let k' : FullCoreState :=
      { k with arena := (k.arena.set (r + 3 + 1) nw).set (r + 3 + bi) l1 }
    k'.LengthsOk c ∧ FullWitnessInv c F0 F_cur k' ∧ Full.FullArenaPermEq k0 k' := by
  intro hbd l1 nw k'
  have h3 : 3 ≤ fullArenaClauseSizeCore k r := (hw.arena.refs_wf r href).2.1
  have hnw := fullWitnessInv_to_nw hlen.cur_vars_le hw
  obtain ⟨hnw', hperm'⟩ := full_swapLits_preserves_nw hlen hnw href (k1 := 1) (k2 := bi)
    (by omega) hbi_lt
  have hlen' : k'.LengthsOk c := { hlen with arena_len_arr := by simp [k', hlen.arena_len_arr] }
  have hwat : ModeWatchesInv F_cur k' :=
    hw.watches.with_wstk (k' := k') rfl rfl rfl rfl rfl (fun q hq => hperm'.1.symm ▸ hq)
  have hwat_sp : WatchesInv F_cur k' := by
    dsimp only [ModeWatchesInv, k'] at hwat
    rwa [ite_eq_left hdm] at hwat
  exact ⟨hlen', fullWitnessInv_of_nw hnw' hdm hwat_sp,
    m5_canon_arenaPerm_trans hperm0 (m5_canon_arenaPerm_of_pd rfl hperm')⟩

private theorem m5_prop_push_wit {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
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

private structure M5PropLoopInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (st0 st : FullState) (t : BitVec 64) : Prop where
  len : st.LengthsOk c
  wit : FullWitnessInv c F0 F_cur st.core
  core_eq : ∃ wv' ar' ws' wl' wu',
    st.core = { st0.core with wvec := wv', arena := ar', wstk := ws', wlen := wl', wusable := wu' }
  sc_eq : ∃ wsort', st.scratch = { st0.scratch with wsort := wsort' }
  perm : Full.FullArenaPermEq st0.core st.core
  tle : t.toNat ≤ st0.core.trail_end

private theorem m5_prop_chrono_oom_done {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st0 st : FullState} {R : Mem 64 → Prop} {Q : Post [.bool]} {mp : Mem 64}
    {ignore_ref : BitVec 64}
    {vals0 : List (BitVec 8)} {flags0 lvl0 rsns0 trl0 tp0 : List (BitVec 32)}
    {te0 : Nat} {un0 uf0 : BitVec 64} {wv0 ar0 ws0 : List (BitVec 32)} {wl0 : Nat}
    {wu0 ct0 cr0 c00 c10 oom0 tk0 : BitVec 64} {wso0 : List (BitVec 32)} {ph0 : List (BitVec 8)}
    {wv_t ar_t ws_t : List (BitVec 32)} {wl_t : Nat} {wu_t : BitVec 64} {wso_t : List (BitVec 32)}
    {wv' ws' : List (BitVec 32)} {wl' : Nat} {wu' : BitVec 64} {wso' : List (BitVec 32)}
    (hQ : ∀ ok (vals' : List (BitVec 8))
      (flags' lvl' rsns' trl' tp' : List (BitVec 32)) (te' : Nat)
      (un' uf' : BitVec 64) (wv'' ar'' ws'' : List (BitVec 32)) (wl'' : Nat)
      (wu'' ct' cr' c0' c1' oom' tk' : BitVec 64) (wso'' : List (BitVec 32))
      (ph' : List (BitVec 8)) (m' : Mem 64),
      let s' : FullState :=
        { s with
          core :=
            { s.core with
              vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
              trail_pos := tp', trail_end := te', unassigned := un', unflushed := uf',
              wvec := wv'', arena := ar'', wstk := ws'', wlen := wl'', wusable := wu'',
              confl_type := ct', confl_ref := cr', confl_lit0 := c0', confl_lit1 := c1',
              oom := oom' }
          scratch := { s.scratch with search_ticks := tk', wsort := wso'', phases := ph' } }
      s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
      Full.FullTrailExt s.core s'.core → Full.FullArenaPermEq s.core s'.core →
      (ok = false → oom' ≠ 0#64 ∨ (FullConflictOkW F_cur s' ∧ (ct' = 2#64 → cr' ≠ ignore_ref))) →
      (ok = true → oom' = 0#64 ∧ ct' = s.core.confl_type) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m')
    (hceq0 : st0.core =
      { s.core with
        vals := vals0, flags := flags0, lvl := lvl0, rsns := rsns0, trl := trl0,
        trail_pos := tp0, trail_end := te0, unassigned := un0, unflushed := uf0, wvec := wv0,
        arena := ar0, wstk := ws0, wlen := wl0, wusable := wu0, confl_type := ct0,
        confl_ref := cr0, confl_lit0 := c00, confl_lit1 := c10, oom := oom0 })
    (hsc0 : st0.scratch = { s.scratch with search_ticks := tk0, wsort := wso0, phases := ph0 })
    (hceq_t : st.core = { st0.core with
      wvec := wv_t, arena := ar_t, wstk := ws_t, wlen := wl_t, wusable := wu_t })
    (hsceq_t : st.scratch = { st0.scratch with wsort := wso_t })
    (hdm_t : st.core.dense_mode = 0#64)
    (htr1 : Full.FullTrailExt s.core
      { s.core with
        vals := vals0, flags := flags0, lvl := lvl0, rsns := rsns0, trl := trl0,
        trail_pos := tp0, trail_end := te0, unassigned := un0, unflushed := uf0, wvec := wv0,
        arena := ar0, wstk := ws0, wlen := wl0, wusable := wu0, confl_type := ct0,
        confl_ref := cr0, confl_lit0 := c00, confl_lit1 := c10, oom := oom0 })
    (hpm1' : Full.FullArenaPermEq s.core st0.core)
    (hperm_t : Full.FullArenaPermEq st0.core st.core)
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
  let st_p : FullState :=
    { st with
      core := { st.core with wvec := wv', wstk := ws', wlen := wl', wusable := wu' }
      scratch := { st.scratch with wsort := wso' } }
  let st_o : FullState := { st_p with core := { st_p.core with oom := 1#64 } }
  have hlen_o : st_o.LengthsOk c :=
    ⟨{ hlen_p.core_ok with vals_len := hlen_p.core_ok.vals_len }, hlen_p.scratch_ok⟩
  have hwat_o_mode : ModeWatchesInv F_cur st_o.core :=
    hw_p.watches.with_wstk rfl rfl rfl rfl rfl (fun _ h => h)
  have hdm_o : st_o.core.dense_mode = 0#64 := hdm_t
  have hwat_o : WatchesInv F_cur st_o.core := by
    simpa only [ModeWatchesInv, hdm_o, ↓reduceIte] using hwat_o_mode
  have hnw_o : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c st_o.core) :=
    fullWitnessInv_nw_congr hlen_o.core_ok.cur_vars_le
      (fullWitnessInv_to_nw hlen_p.core_ok.cur_vars_le hw_p)
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have hw_o : FullWitnessInv c F0 F_cur st_o.core :=
    fullWitnessInv_of_nw hnw_o hdm_o hwat_o
  have hceq_o : st_o.core = { s.core with
      vals := vals0, flags := flags0, lvl := lvl0, rsns := rsns0,
      trl := trl0, trail_pos := tp0, trail_end := te0,
      unassigned := un0, unflushed := uf0, wvec := wv',
      arena := ar_t, wstk := ws', wlen := wl', wusable := wu',
      confl_type := ct0, confl_ref := cr0, confl_lit0 := c00,
      confl_lit1 := c10, oom := 1#64 } := by
    change { st.core with
      wvec := wv', wstk := ws', wlen := wl', wusable := wu', oom := 1#64 } = _
    rw [hceq_t, hceq0]
  have hsc_o : st_o.scratch = { s.scratch with
      search_ticks := tk0, wsort := wso', phases := ph0 } := by
    change { st.scratch with wsort := wso' } = _
    rw [hsceq_t, hsc0]
  have hpm_st : Full.FullArenaPermEq s.core st.core := m5_canon_arenaPerm_trans hpm1' hperm_t
  have hpm_o : Full.FullArenaPermEq s.core st_o.core := ⟨hpm_st.1, hpm_st.2.1, hpm_st.2.2⟩
  have htr_o : Full.FullTrailExt s.core st_o.core := by
    rw [hceq_o]
    exact ⟨htr1.1, htr1.2.1, htr1.2.2⟩
  exact hQ false vals0 flags0 lvl0 rsns0 trl0 tp0 te0 un0 uf0
    wv' ar_t ws' wl' wu' ct0 cr0 c00 c10 1#64 tk0 wso' ph0 _
    (by dsimp only [st_o, st_p]; rw [← hceq_o, ← hsc_o]; exact hlen_o)
    (by rw [← hceq_o]; exact hw_o)
    (by rw [← hceq_o]; exact htr_o)
    (by rw [← hceq_o]; exact hpm_o)
    (fun _ => Or.inl (by decide)) (fun hc => by cases hc)
    (by rw [← hceq_o, ← hsc_o]; exact hmp)

private theorem m5_prop_chrono_ret_wp {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st0 st : FullState} {R : Mem 64 → Prop} {Q : Post [.bool]} {ml : Mem 64}
    {ok0 : Bool} {ignore_ref : BitVec 64}
    {vals0 : List (BitVec 8)} {flags0 lvl0 rsns0 trl0 tp0 : List (BitVec 32)}
    {te0 : Nat} {un0 uf0 : BitVec 64} {wv0 ar0 ws0 : List (BitVec 32)} {wl0 : Nat}
    {wu0 ct0 cr0 c00 c10 oom0 tk0 : BitVec 64} {wso0 : List (BitVec 32)} {ph0 : List (BitVec 8)}
    {wv_t ar_t ws_t : List (BitVec 32)} {wl_t : Nat} {wu_t : BitVec 64} {wso_t : List (BitVec 32)}
    (hQ : ∀ ok (vals' : List (BitVec 8))
      (flags' lvl' rsns' trl' tp' : List (BitVec 32)) (te' : Nat)
      (un' uf' : BitVec 64) (wv'' ar'' ws'' : List (BitVec 32)) (wl'' : Nat)
      (wu'' ct' cr' c0' c1' oom' tk' : BitVec 64) (wso'' : List (BitVec 32))
      (ph' : List (BitVec 8)) (m' : Mem 64),
      let s' : FullState :=
        { s with
          core :=
            { s.core with
              vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
              trail_pos := tp', trail_end := te', unassigned := un', unflushed := uf',
              wvec := wv'', arena := ar'', wstk := ws'', wlen := wl'', wusable := wu'',
              confl_type := ct', confl_ref := cr', confl_lit0 := c0', confl_lit1 := c1',
              oom := oom' }
          scratch := { s.scratch with search_ticks := tk', wsort := wso'', phases := ph' } }
      s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
      Full.FullTrailExt s.core s'.core → Full.FullArenaPermEq s.core s'.core →
      (ok = false → oom' ≠ 0#64 ∨ (FullConflictOkW F_cur s' ∧ (ct' = 2#64 → cr' ≠ ignore_ref))) →
      (ok = true → oom' = 0#64 ∧ ct' = s.core.confl_type) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m')
    (hceq0 : st0.core =
      { s.core with
        vals := vals0, flags := flags0, lvl := lvl0, rsns := rsns0, trl := trl0,
        trail_pos := tp0, trail_end := te0, unassigned := un0, unflushed := uf0, wvec := wv0,
        arena := ar0, wstk := ws0, wlen := wl0, wusable := wu0, confl_type := ct0,
        confl_ref := cr0, confl_lit0 := c00, confl_lit1 := c10, oom := oom0 })
    (hsc0 : st0.scratch = { s.scratch with search_ticks := tk0, wsort := wso0, phases := ph0 })
    (hceq_t : st.core = { st0.core with
      wvec := wv_t, arena := ar_t, wstk := ws_t, wlen := wl_t, wusable := wu_t })
    (hsceq_t : st.scratch = { st0.scratch with wsort := wso_t })
    (hoom_z : oom0 = 0#64) (hct_ok : ok0 = true → ct0 = s.core.confl_type)
    (hcf_ok : ok0 = false → FullConflictOkW F_cur st0 ∧ (ct0 = 2#64 → cr0 ≠ ignore_ref))
    (htr1 : Full.FullTrailExt s.core
      { s.core with
        vals := vals0, flags := flags0, lvl := lvl0, rsns := rsns0, trl := trl0,
        trail_pos := tp0, trail_end := te0, unassigned := un0, unflushed := uf0, wvec := wv0,
        arena := ar0, wstk := ws0, wlen := wl0, wusable := wu0, confl_type := ct0,
        confl_ref := cr0, confl_lit0 := c00, confl_lit1 := c10, oom := oom0 })
    (hpm1' : Full.FullArenaPermEq s.core st0.core)
    (hperm_t : Full.FullArenaPermEq st0.core st.core)
    (hlen_t : st.LengthsOk c) (hw_t : FullWitnessInv c F0 F_cur st.core)
    (hml : (FullMem c st ⋆ R) ml) :
    Q (ok0, ()) ml := by
  have hceq_s : st.core = { s.core with
      vals := vals0, flags := flags0, lvl := lvl0, rsns := rsns0, trl := trl0,
      trail_pos := tp0, trail_end := te0, unassigned := un0, unflushed := uf0,
      wvec := wv_t, arena := ar_t, wstk := ws_t, wlen := wl_t, wusable := wu_t,
      confl_type := ct0, confl_ref := cr0, confl_lit0 := c00, confl_lit1 := c10, oom := oom0 } := by
    rw [hceq_t, hceq0]
  have hsc_s : st.scratch = { s.scratch with
      search_ticks := tk0, wsort := wso_t, phases := ph0 } := by
    rw [hsceq_t, hsc0]
  have hcf_st : ok0 = false → FullConflictOkW F_cur st ∧ (ct0 = 2#64 → cr0 ≠ ignore_ref) := by
    intro hfk
    obtain ⟨hcf0, hign0⟩ := hcf_ok hfk
    refine ⟨m5_conflOkW_of_arenaPerm hcf0 (by rw [hceq_t, hceq0]) (by rw [hceq_t, hceq0])
      (by rw [hceq_t, hceq0]) (by rw [hceq_t, hceq0]) (by rw [hceq_t, hceq0])
      (by rw [hceq_t, hceq0]) hperm_t, hign0⟩
  have hst_def : st =
      { s with
        core := { s.core with
          vals := vals0, flags := flags0, lvl := lvl0, rsns := rsns0, trl := trl0,
          trail_pos := tp0, trail_end := te0, unassigned := un0, unflushed := uf0,
          wvec := wv_t, arena := ar_t, wstk := ws_t, wlen := wl_t, wusable := wu_t,
          confl_type := ct0, confl_ref := cr0, confl_lit0 := c00, confl_lit1 := c10, oom := oom0 }
        scratch := { s.scratch with search_ticks := tk0, wsort := wso_t, phases := ph0 } } := by
    cases st; simp only [FullState.mk.injEq]; exact ⟨hceq_s, hsc_s⟩
  have htr_f : Full.FullTrailExt s.core st.core :=
    m5_canon_trailExt_of_pd ((m5_pd_trailExt_of_canon htr1).congr
      (by rw [hceq_s]) (by rw [hceq_s]) (by rw [hceq_s]))
  have hpm_f : Full.FullArenaPermEq s.core st.core := m5_canon_arenaPerm_trans hpm1' hperm_t
  rw [hst_def] at hlen_t hml
  have hcf_res : ok0 = false → oom0 ≠ 0#64 ∨ (FullConflictOkW F_cur
      { s with
        core := { s.core with
          vals := vals0, flags := flags0, lvl := lvl0, rsns := rsns0, trl := trl0,
          trail_pos := tp0, trail_end := te0, unassigned := un0, unflushed := uf0,
          wvec := wv_t, arena := ar_t, wstk := ws_t, wlen := wl_t, wusable := wu_t,
          confl_type := ct0, confl_ref := cr0, confl_lit0 := c00, confl_lit1 := c10, oom := oom0 }
        scratch := { s.scratch with search_ticks := tk0, wsort := wso_t, phases := ph0 } } ∧
      (ct0 = 2#64 → cr0 ≠ ignore_ref)) := by
    intro hfk
    obtain ⟨hcf_s, hign⟩ := hcf_st hfk
    rw [hst_def] at hcf_s
    exact Or.inr ⟨hcf_s, hign⟩
  rw [hceq_s] at hw_t htr_f hpm_f
  exact hQ ok0 vals0 flags0 lvl0 rsns0 trl0 tp0 te0 un0 uf0
    wv_t ar_t ws_t wl_t wu_t ct0 cr0 c00 c10 oom0 tk0 wso_t ph0 ml
    hlen_t hw_t htr_f hpm_f hcf_res (fun ht => ⟨hoom_z, hct_ok ht⟩) hml

private theorem m5_prop_chrono_wit_of_watches {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {st st_n : FullState} {wv_n ws_n wso_n : List (BitVec 32)}
    {wl_n : Nat} {wu_n : BitVec 64}
    (hlen : st.LengthsOk c) (hw : FullWitnessInv c F0 F_cur st.core)
    (hdm : st.core.dense_mode = 0#64)
    (hc : st_n.core = { st.core with wvec := wv_n, wstk := ws_n, wlen := wl_n, wusable := wu_n })
    (hsc : st_n.scratch = { st.scratch with wsort := wso_n })
    (hlen_n : st_n.LengthsOk c) (hmw : ModeWatchesInv F_cur st_n.core) :
    ({ st with
      core := { st.core with wvec := wv_n, wstk := ws_n, wlen := wl_n, wusable := wu_n }
      scratch := { st.scratch with wsort := wso_n } } : FullState).LengthsOk c ∧
    FullWitnessInv c F0 F_cur st_n.core ∧
    FullWitnessInv c F0 F_cur
      { st.core with wvec := wv_n, wstk := ws_n, wlen := wl_n, wusable := wu_n } := by
  have hlen_c : ({ st with
      core := { st.core with wvec := wv_n, wstk := ws_n, wlen := wl_n, wusable := wu_n }
      scratch := { st.scratch with wsort := wso_n } } : FullState).LengthsOk c :=
    ⟨by rw [← hc]; exact hlen_n.core_ok, by rw [← hsc]; exact hlen_n.scratch_ok⟩
  have hdm_n : st_n.core.dense_mode = 0#64 := by rw [hc]; exact hdm
  have hwat : WatchesInv F_cur st_n.core := by
    unfold ModeWatchesInv at hmw; simpa only [hdm_n, ↓reduceIte] using hmw
  have hnw : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c st_n.core) :=
    fullWitnessInv_nw_congr hlen_n.core_ok.cur_vars_le
      (fullWitnessInv_to_nw hlen.core_ok.cur_vars_le hw)
      (by rw [hc]) (by rw [hc]) (by rw [hc]) (by rw [hc]) (by rw [hc]) (by rw [hc])
      (by rw [hc]) (by rw [hc]) (by rw [hc]) (by rw [hc]) (by rw [hc]) (by rw [hc])
      (by rw [hc])
  have hw_n : FullWitnessInv c F0 F_cur st_n.core := fullWitnessInv_of_nw hnw hdm_n hwat
  exact ⟨hlen_c, hw_n, by simpa only [hc] using hw_n⟩

private theorem m5_prop_chrono_ret_early {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {R : Mem 64 → Prop} {Q : Post [.bool]} {ok0 : Bool}
    {ignore_ref : BitVec 64} {vals0 : List (BitVec 8)}
    {flags0 lvl0 rsns0 trl0 tp0 : List (BitVec 32)} {te0 : Nat} {un0 uf0 : BitVec 64}
    {wv0 ar0 ws0 : List (BitVec 32)} {wl0 : Nat} {wu0 ct0 cr0 c00 c10 oom0 tk0 : BitVec 64}
    {wso0 : List (BitVec 32)} {ph0 : List (BitVec 8)} {m1 : Mem 64}
    (hQ : ∀ ok (vals' : List (BitVec 8))
      (flags' lvl' rsns' trl' tp' : List (BitVec 32)) (te' : Nat)
      (un' uf' : BitVec 64) (wv'' ar'' ws'' : List (BitVec 32)) (wl'' : Nat)
      (wu'' ct' cr' c0' c1' oom' tk' : BitVec 64) (wso'' : List (BitVec 32))
      (ph' : List (BitVec 8)) (m' : Mem 64),
      let s' : FullState :=
        { s with
          core :=
            { s.core with
              vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
              trail_pos := tp', trail_end := te', unassigned := un', unflushed := uf',
              wvec := wv'', arena := ar'', wstk := ws'', wlen := wl'', wusable := wu'',
              confl_type := ct', confl_ref := cr', confl_lit0 := c0', confl_lit1 := c1',
              oom := oom' }
          scratch := { s.scratch with search_ticks := tk', wsort := wso'', phases := ph' } }
      s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
      Full.FullTrailExt s.core s'.core → Full.FullArenaPermEq s.core s'.core →
      (ok = false → oom' ≠ 0#64 ∨ (FullConflictOkW F_cur s' ∧ (ct' = 2#64 → cr' ≠ ignore_ref))) →
      (ok = true → oom' = 0#64 ∧ ct' = s.core.confl_type) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m')
    (hlen1 : ({ s with
      core :=
        { s.core with
          vals := vals0, flags := flags0, lvl := lvl0, rsns := rsns0, trl := trl0,
          trail_pos := tp0, trail_end := te0, unassigned := un0, unflushed := uf0, wvec := wv0,
          arena := ar0, wstk := ws0, wlen := wl0, wusable := wu0, confl_type := ct0,
          confl_ref := cr0, confl_lit0 := c00, confl_lit1 := c10, oom := oom0 }
      scratch := { s.scratch with search_ticks := tk0, wsort := wso0, phases := ph0 } } :
        FullState).LengthsOk c)
    (hw1 : FullWitnessInv c F0 F_cur
      { s.core with
        vals := vals0, flags := flags0, lvl := lvl0, rsns := rsns0, trl := trl0,
        trail_pos := tp0, trail_end := te0, unassigned := un0, unflushed := uf0, wvec := wv0,
        arena := ar0, wstk := ws0, wlen := wl0, wusable := wu0, confl_type := ct0,
        confl_ref := cr0, confl_lit0 := c00, confl_lit1 := c10, oom := oom0 })
    (htr1 : Full.FullTrailExt s.core
      { s.core with
        vals := vals0, flags := flags0, lvl := lvl0, rsns := rsns0, trl := trl0,
        trail_pos := tp0, trail_end := te0, unassigned := un0, unflushed := uf0, wvec := wv0,
        arena := ar0, wstk := ws0, wlen := wl0, wusable := wu0, confl_type := ct0,
        confl_ref := cr0, confl_lit0 := c00, confl_lit1 := c10, oom := oom0 })
    (hpm1 : Full.FullArenaPermEq s.core
      { s.core with
        vals := vals0, flags := flags0, lvl := lvl0, rsns := rsns0, trl := trl0,
        trail_pos := tp0, trail_end := te0, unassigned := un0, unflushed := uf0, wvec := wv0,
        arena := ar0, wstk := ws0, wlen := wl0, wusable := wu0, confl_type := ct0,
        confl_ref := cr0, confl_lit0 := c00, confl_lit1 := c10, oom := oom0 })
    (hF1 : ok0 = false → oom0 ≠ 0#64 ∨ (FullConflictOkW F_cur
      { s with
        core :=
          { s.core with
            vals := vals0, flags := flags0, lvl := lvl0, rsns := rsns0, trl := trl0,
            trail_pos := tp0, trail_end := te0, unassigned := un0, unflushed := uf0, wvec := wv0,
            arena := ar0, wstk := ws0, wlen := wl0, wusable := wu0, confl_type := ct0,
            confl_ref := cr0, confl_lit0 := c00, confl_lit1 := c10, oom := oom0 }
        scratch := { s.scratch with search_ticks := tk0, wsort := wso0, phases := ph0 } } ∧
      (ct0 = 2#64 → cr0 ≠ ignore_ref)))
    (hT1 : ok0 = true → oom0 = 0#64 ∧ ct0 = s.core.confl_type)
    (hm1 : (FullMem c
      { s with
        core :=
          { s.core with
            vals := vals0, flags := flags0, lvl := lvl0, rsns := rsns0, trl := trl0,
            trail_pos := tp0, trail_end := te0, unassigned := un0, unflushed := uf0, wvec := wv0,
            arena := ar0, wstk := ws0, wlen := wl0, wusable := wu0, confl_type := ct0,
            confl_ref := cr0, confl_lit0 := c00, confl_lit1 := c10, oom := oom0 }
        scratch := { s.scratch with search_ticks := tk0, wsort := wso0, phases := ph0 } } ⋆ R) m1)
    (hoom_z : oom0 = 0#64) :
    Q (ok0, ()) m1 :=
  hQ ok0 vals0 flags0 lvl0 rsns0 trl0 tp0 te0 un0 uf0 wv0 ar0 ws0 wl0 wu0
    ct0 cr0 c00 c10 oom0 tk0 wso0 ph0 m1 hlen1 hw1 htr1 hpm1
    (fun hf => Or.inr ((hF1 hf).resolve_left (fun h => h hoom_z)))
    (fun ht => ⟨hoom_z, (hT1 ht).2⟩) hm1

private theorem m5_prop_chrono_r_facts {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
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

private theorem m5_prop_chrono_inner_ck_facts {ar : List (BitVec 32)} {r ck k : BitVec 32}
    {cb : BitVec 64} {cur_vars lvl_len : Nat}
    (hcv_le : cur_vars ≤ lvl_len)
    (hk_idx : (cb + k.setWidth 64).toNat = r.toNat + 3 + k.toNat)
    (hk_ar : r.toNat + 3 + k.toNat < ar.length)
    (hcbk_lt : (cb + k.setWidth 64).toNat < ar.length)
    (hck_def : ck = ar[(cb + k.setWidth 64).toNat]'hcbk_lt)
    (hck_ltv : ck.toNat < 2 * cur_vars) :
    (ar[r.toNat + 3 + k.toNat]?.getD 0#32).toNat < 2 * cur_vars ∧
    (BitVec.setWidth 64 (ck >>> 1#32)).toNat < lvl_len := by
  have _ := hcv_le
  refine ⟨?_, ?_⟩
  · rw [List.getElem?_eq_getElem hk_ar, Option.getD_some,
      m5_list_getElem_of_idx (xs := ar) (hi := hk_ar) (hj := hcbk_lt) hk_idx.symm, ← hck_def]
    exact hck_ltv
  · rw [m5_bv32_rshift1_toNat]; omega

private theorem m5_prop_chrono_push_wrap {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {st st_d : FullState} {wv_d ws_d : List (BitVec 32)} {wl_d : Nat} {wu_d : BitVec 64}
    {wso_d : List (BitVec 32)} {ol nw r : BitVec 32} {R : Mem 64 → Prop} {mp : Mem 64}
    {pok : Bool} {wv_p ws_p wso_p : List (BitVec 32)} {wl_p : Nat} {wu_p : BitVec 64}
    (hlen_d : st_d.LengthsOk c) (hw_d : FullWitnessInv c F0 F_cur st_d.core)
    (hsd_c : st_d.core =
      { st.core with wvec := wv_d, wstk := ws_d, wlen := wl_d, wusable := wu_d })
    (hsd_sc : st_d.scratch = { st.scratch with wsort := wso_d })
    (hdm_t : st.core.dense_mode = 0#64) (href_d : r.toNat ∈ fullArenaClauseRefs st_d)
    (hcr_lt31 : r.toNat < 0x80000000) (hnw_ltv : nw.toNat < 2 * st.core.cur_vars)
    (hmp : (FullMem c
      { st_d with
        core := { st_d.core with wvec := wv_p, wstk := ws_p, wlen := wl_p, wusable := wu_p }
        scratch := { st_d.scratch with wsort := wso_p } } ⋆ R) mp)
    (hlen_p : ({ st_d with
        core := { st_d.core with wvec := wv_p, wstk := ws_p, wlen := wl_p, wusable := wu_p }
        scratch := { st_d.scratch with wsort := wso_p } } : FullState).LengthsOk c)
    (hlay_p : WatchStackLayout
      { st_d.core with wvec := wv_p, wstk := ws_p, wlen := wl_p, wusable := wu_p })
    (hpres_o : ∀ l < 2 * st_d.core.cur_vars, l ≠ nw.toNat →
      fullWatchSizeCore { st_d.core with
        wvec := wv_p, wstk := ws_p, wlen := wl_p, wusable := wu_p } l =
        fullWatchSizeCore st_d.core l ∧
      ∀ k < fullWatchSizeCore st_d.core l,
        ws_p[fullWatchOffCore { st_d.core with
          wvec := wv_p, wstk := ws_p, wlen := wl_p, wusable := wu_p } l + k]? =
        st_d.core.wstk[fullWatchOffCore st_d.core l + k]?)
    (hpok_t : pok = true →
      nw.toNat < 2 * st_d.core.cur_vars ∧ ((2#32 : BitVec 32).toNat = 1 ∨ (2#32).toNat = 2) ∧
      fullWatchSizeCore { st_d.core with
        wvec := wv_p, wstk := ws_p, wlen := wl_p, wusable := wu_p } nw.toNat =
        fullWatchSizeCore st_d.core nw.toNat + 2 ∧
      (∀ k < fullWatchSizeCore st_d.core nw.toNat,
        ws_p[fullWatchOffCore { st_d.core with
          wvec := wv_p, wstk := ws_p, wlen := wl_p, wusable := wu_p } nw.toNat + k]? =
        st_d.core.wstk[fullWatchOffCore st_d.core nw.toNat + k]?) ∧
      ws_p[fullWatchOffCore { st_d.core with
        wvec := wv_p, wstk := ws_p, wlen := wl_p, wusable := wu_p } nw.toNat +
        fullWatchSizeCore st_d.core nw.toNat]? = some (ol &&& 0x7FFFFFFF#32) ∧
      ((2#32 : BitVec 32).toNat = 2 →
        ws_p[fullWatchOffCore { st_d.core with
          wvec := wv_p, wstk := ws_p, wlen := wl_p, wusable := wu_p } nw.toNat +
          fullWatchSizeCore st_d.core nw.toNat + 1]? = some r))
    (hpok_f : pok = false →
      (nw.toNat < 2 * st_d.core.cur_vars →
        fullWatchSizeCore { st_d.core with
          wvec := wv_p, wstk := ws_p, wlen := wl_p, wusable := wu_p } nw.toNat =
          fullWatchSizeCore st_d.core nw.toNat ∧
        ∀ k < fullWatchSizeCore st_d.core nw.toNat,
          ws_p[fullWatchOffCore { st_d.core with
            wvec := wv_p, wstk := ws_p, wlen := wl_p, wusable := wu_p } nw.toNat + k]? =
          st_d.core.wstk[fullWatchOffCore st_d.core nw.toNat + k]?) ∧
      (2 * st_d.core.cur_vars ≤ nw.toNat ∨ ((2#32 : BitVec 32).toNat ≠ 1 ∧
        (2#32).toNat ≠ 2) ∨
        ({ st_d with
          core := { st_d.core with wvec := wv_p, wstk := ws_p, wlen := wl_p, wusable := wu_p }
          scratch := { st_d.scratch with wsort := wso_p } } : FullState) = st_d ∨ wu_p = 0#64)) :
    ∃ st_p : FullState,
      st_p.core = { st.core with wvec := wv_p, wstk := ws_p, wlen := wl_p, wusable := wu_p } ∧
      st_p.scratch = { st.scratch with wsort := wso_p } ∧
      st_p.LengthsOk c ∧ FullWitnessInv c F0 F_cur st_p.core ∧ (FullMem c st_p ⋆ R) mp := by
  have hsd_cv : st_d.core.cur_vars = st.core.cur_vars := by rw [hsd_c]
  have hsd_dm : st_d.core.dense_mode = 0#64 := by rw [hsd_c]; exact hdm_t
  let st_p : FullState :=
    { st_d with
      core := { st_d.core with wvec := wv_p, wstk := ws_p, wlen := wl_p, wusable := wu_p }
      scratch := { st_d.scratch with wsort := wso_p } }
  have hw_p : FullWitnessInv c F0 F_cur st_p.core :=
    m5_prop_push_wit hlen_d hw_d hsd_dm href_d hcr_lt31 (by rw [hsd_cv]; exact hnw_ltv)
      hlen_p.core_ok hlay_p hpres_o
      (fun ht => let h := hpok_t ht; ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2 rfl⟩)
      (fun hf => (hpok_f hf).1 (by rw [hsd_cv]; exact hnw_ltv))
  exact ⟨st_p, by dsimp only [st_p]; rw [hsd_c], by dsimp only [st_p]; rw [hsd_sc],
    hlen_p, hw_p, hmp⟩

private theorem m5_prop_chrono_post_swap {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {st0 st st_p : FullState} {wv_p ws_p wso_p : List (BitVec 32)} {wl_p : Nat} {wu_p : BitVec 64}
    {r bi nw l1 : BitVec 32} {ar_s : List (BitVec 32)} {R : Mem 64 → Prop} {ms : Mem 64}
    (hsp_c : st_p.core = { st.core with wvec := wv_p, wstk := ws_p, wlen := wl_p, wusable := wu_p })
    (hsp_sc : st_p.scratch = { st.scratch with wsort := wso_p })
    (hlen_p : st_p.LengthsOk c) (hw_p : FullWitnessInv c F0 F_cur st_p.core)
    (hdm_t : st.core.dense_mode = 0#64) (hperm_t : Full.FullArenaPermEq st0.core st.core)
    (href : r.toNat ∈ fullArenaClauseRefsCore st.core)
    (hbi_ge2 : 2 ≤ bi.toNat) (hbi_csz : bi.toNat < fullArenaClauseSizeCore st.core r.toNat)
    (hr_bd : r.toNat + 3 + fullArenaClauseSizeCore st.core r.toNat ≤ st.core.arena.length)
    (har_s : ar_s = (st_p.core.arena.set (r.toNat + 3 + 1) nw).set (r.toNat + 3 + bi.toNat) l1)
    (hnw : nw = st_p.core.arena[r.toNat + 3 + bi.toNat]'(by
      have har_p : st_p.core.arena = st.core.arena := by rw [hsp_c]
      rw [har_p]; omega))
    (hl1 : l1 = st_p.core.arena[r.toNat + 3 + 1]'(by
      have har_p : st_p.core.arena = st.core.arena := by rw [hsp_c]
      rw [har_p]; omega))
    (hm_s : (FullMem c { st_p with core := { st_p.core with arena := ar_s } } ⋆ R) ms) :
    ∃ st_s : FullState,
      st_s.core = { st_p.core with arena := ar_s } ∧
      st_s.scratch = st_p.scratch ∧
      st_s.LengthsOk c ∧ FullWitnessInv c F0 F_cur st_s.core ∧
      Full.FullArenaPermEq st0.core st_s.core ∧ (FullMem c st_s ⋆ R) ms := by
  have hsp_ar : st_p.core.arena = st.core.arena := by rw [hsp_c]
  have hbi_csz_p : bi.toNat < fullArenaClauseSizeCore st_p.core r.toNat := by
    unfold fullArenaClauseSizeCore; rw [hsp_ar]; exact hbi_csz
  have href_p : r.toNat ∈ fullArenaClauseRefsCore st_p.core := by
    simp only [fullArenaClauseRefsCore, hsp_c]; exact href
  have hsp_dm : st_p.core.dense_mode = 0#64 := by rw [hsp_c]; exact hdm_t
  have hperm_p : Full.FullArenaPermEq st0.core st_p.core :=
    ⟨by rw [hsp_c]; exact hperm_t.1,
     by simp only [fullArenaClauseRefsCore, hsp_c]; exact hperm_t.2.1,
     fun q hq => by
       simp only [fullArenaClauseSizeCore, fullArenaClauseGarbCore, fullArenaClauseLitsCore,
         fullArenaHdrCore, hsp_c]
       exact hperm_t.2.2 q hq⟩
  obtain ⟨hlen_s, hw_s, hperm_s⟩ := m5_prop_swap_preserves_inv hlen_p.core_ok hw_p hsp_dm
    hperm_p href_p hbi_ge2 hbi_csz_p
  let ar_sw : List (BitVec 32) :=
    (st_p.core.arena.set (r.toNat + 3 + 1)
      (st_p.core.arena[r.toNat + 3 + bi.toNat]'(by rw [hsp_ar]; omega))).set
      (r.toNat + 3 + bi.toNat) (st_p.core.arena[r.toNat + 3 + 1]'(by rw [hsp_ar]; omega))
  have har_s' : ar_s = ar_sw := by dsimp only [ar_sw]; rw [har_s, ← hnw, ← hl1]
  have hm_s' : (FullMem c { st_p with core := { st_p.core with arena := ar_sw } } ⋆ R) ms := by
    rwa [← har_s']
  obtain ⟨st_s, hsts_c, hsts_sc, hm_out⟩ :=
    m5_otfs_opaque_state { st_p.core with arena := ar_sw } st_p.scratch hm_s' rfl rfl
  have _ := hsp_sc
  exact ⟨st_s, by rw [hsts_c, har_s'], hsts_sc,
    ⟨by rw [hsts_c]; exact hlen_s, by rw [hsts_sc]; exact hlen_p.scratch_ok⟩,
    by rw [hsts_c]; exact hw_s, by rw [hsts_c]; exact hperm_s, hm_out⟩

private theorem m5_prop_chrono_post_unw {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {st0 st st_p st_s : FullState} {wv_p ws_p wso_p ar_s : List (BitVec 32)} {wl_p : Nat}
    {wu_p : BitVec 64} {ol nw r : BitVec 32} {R : Mem 64 → Prop}
    {wv_u ws_u : List (BitVec 32)} {wu_u : BitVec 64} {m_u : Mem 64}
    (hsp_c : st_p.core = { st.core with wvec := wv_p, wstk := ws_p, wlen := wl_p, wusable := wu_p })
    (hsp_sc : st_p.scratch = { st.scratch with wsort := wso_p })
    (hsts_c : st_s.core = { st_p.core with arena := ar_s })
    (hsts_sc : st_s.scratch = st_p.scratch)
    (hceq_t : st.core =
      { st0.core with
        wvec := st.core.wvec, arena := st.core.arena, wstk := st.core.wstk,
        wlen := st.core.wlen, wusable := st.core.wusable })
    (hsceq_t : st.scratch = { st0.scratch with wsort := st.scratch.wsort })
    (hdm_t : st.core.dense_mode = 0#64)
    (hlen_s : st_s.LengthsOk c) (hw_s : FullWitnessInv c F0 F_cur st_s.core)
    (hperm_s : Full.FullArenaPermEq st0.core st_s.core)
    (hperm_t : Full.FullArenaPermEq st0.core st.core)
    (href : r.toNat ∈ fullArenaClauseRefsCore st.core)
    (hol_lt : ol.toNat < 2 * st.core.cur_vars) (hnw_ltv : nw.toNat < 2 * st.core.cur_vars)
    (hm_u : (FullMem c { st_s with core :=
      { st_s.core with wvec := wv_u, wstk := ws_u, wusable := wu_u } } ⋆ R) m_u)
    (hlen_u : ({ st_s.core with wvec := wv_u, wstk := ws_u, wusable := wu_u }).LengthsOk c ∧
      st_s.scratch.LengthsOk c)
    (hmw_u : ModeWatchesInv F_cur { st_s.core with wvec := wv_u, wstk := ws_u, wusable := wu_u }) :
    ∃ st_u : FullState,
      st_u.core =
        { st0.core with wvec := wv_u, arena := ar_s, wstk := ws_u, wlen := wl_p, wusable := wu_u } ∧
      st_u.scratch = { st0.scratch with wsort := wso_p } ∧
      st_u.LengthsOk c ∧ FullWitnessInv c F0 F_cur st_u.core ∧
      Full.FullArenaPermEq st0.core st_u.core ∧ st_u.core.dense_mode = 0#64 ∧
      ModeWatchesInv F_cur st_u.core ∧ 2 * st_u.core.cur_vars < 2 ^ 31 - 1 ∧
      ol.toNat < 2 * st_u.core.cur_vars ∧ nw.toNat < 2 * st_u.core.cur_vars ∧
      r.toNat ∈ fullArenaClauseRefsCore st_u.core ∧
      (∀ (hb0 : (BitVec.setWidth 64 ol <<< (1 : Nat)).toNat < st_u.core.wvec.length),
        (BitVec.setWidth 64
          (st_u.core.wvec[(BitVec.setWidth 64 ol <<< (1 : Nat)).toNat]'hb0)).toNat =
          fullWatchOffCore st_u.core ol.toNat) ∧
      (∀ (hb1 : ((BitVec.setWidth 64 ol <<< (1 : Nat)) + (1 : BitVec 64)).toNat <
          st_u.core.wvec.length),
        (BitVec.setWidth 64
          (st_u.core.wvec[((BitVec.setWidth 64 ol <<< (1 : Nat)) +
            (1 : BitVec 64)).toNat]'hb1)).toNat = fullWatchSizeCore st_u.core ol.toNat) ∧
      (FullMem c st_u ⋆ R) m_u := by
  obtain ⟨st_u, hstu_c, hstu_sc, hm_u'⟩ := m5_otfs_opaque_state
    { st_s.core with wvec := wv_u, wstk := ws_u, wusable := wu_u } st_s.scratch hm_u rfl rfl
  have hlen_u' : st_u.LengthsOk c :=
    ⟨by rw [hstu_c]; exact hlen_u.1, by rw [hstu_sc]; exact hlen_u.2⟩
  have hstu_base : st_u.core =
      { st0.core with
        wvec := wv_u, arena := ar_s, wstk := ws_u, wlen := wl_p, wusable := wu_u } := by
    rw [hstu_c, hsts_c, hsp_c, hceq_t]
  have hstu_scr : st_u.scratch = { st0.scratch with wsort := wso_p } := by
    rw [hstu_sc, hsts_sc, hsp_sc, hsceq_t]
  have hperm_u : Full.FullArenaPermEq st0.core st_u.core := by
    have h1 : st_u.core.arena_len = st_s.core.arena_len := by rw [hstu_c]
    have h2 : fullArenaClauseRefsCore st_u.core = fullArenaClauseRefsCore st_s.core := by
      simp [fullArenaClauseRefsCore, hstu_c]
    have h3 : ∀ q ∈ fullArenaClauseRefsCore st_s.core,
        fullArenaClauseSizeCore st_u.core q = fullArenaClauseSizeCore st_s.core q ∧
        fullArenaClauseGarbCore st_u.core q = fullArenaClauseGarbCore st_s.core q ∧
        (fullArenaClauseLitsCore st_u.core q).Perm (fullArenaClauseLitsCore st_s.core q) :=
      fun q _ => by
        simp [fullArenaClauseSizeCore, fullArenaClauseGarbCore, fullArenaClauseLitsCore,
          fullArenaHdrCore, hstu_c]
    exact m5_canon_arenaPerm_trans hperm_s ⟨h1, h2, h3⟩
  have hdm_u : st_u.core.dense_mode = 0#64 := by rw [hstu_c, hsts_c, hsp_c]; exact hdm_t
  have hmw_u' : ModeWatchesInv F_cur st_u.core := by rw [hstu_c]; exact hmw_u
  have hwat_u : WatchesInv F_cur st_u.core := by
    unfold ModeWatchesInv at hmw_u'; simpa only [hdm_u, ↓reduceIte] using hmw_u'
  have hnw_u : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c st_u.core) :=
    fullWitnessInv_nw_congr hlen_u'.core_ok.cur_vars_le
      (fullWitnessInv_to_nw hlen_s.core_ok.cur_vars_le hw_s)
      (by rw [hstu_c]) (by rw [hstu_c]) (by rw [hstu_c]) (by rw [hstu_c]) (by rw [hstu_c])
      (by rw [hstu_c]) (by rw [hstu_c]) (by rw [hstu_c]) (by rw [hstu_c]) (by rw [hstu_c])
      (by rw [hstu_c]) (by rw [hstu_c]) (by rw [hstu_c])
  have hw_u : FullWitnessInv c F0 F_cur st_u.core := fullWitnessInv_of_nw hnw_u hdm_u hwat_u
  have hcv_u : st_u.core.cur_vars = st.core.cur_vars := by rw [hstu_c, hsts_c, hsp_c]
  have h2cv_u : 2 * st_u.core.cur_vars < 2 ^ 31 - 1 := by
    have hcv_le := hlen_u'.core_ok.cur_vars_le
    have hmv := c.hmaxv; unfold dimacsBound at hmv; omega
  have hol_lt_u : ol.toNat < 2 * st_u.core.cur_vars := by rw [hcv_u]; exact hol_lt
  have hnw_lt_u : nw.toNat < 2 * st_u.core.cur_vars := by rw [hcv_u]; exact hnw_ltv
  have href_u : r.toNat ∈ fullArenaClauseRefsCore st_u.core := by
    rw [hperm_u.2.1, ← hperm_t.2.1]; exact href
  have hwv_u_len := hlen_u'.core_ok.wvec_len
  have hshl_ol : (BitVec.setWidth 64 ol <<< (1 : Nat)).toNat = 2 * ol.toNat := by
    rw [m5_bv64_shl1_nat _ (by rw [zext_toNat ol (by decide)]; omega), zext_toNat ol (by decide)]
  have h2ol1 : ((BitVec.setWidth 64 ol <<< (1 : Nat)) + (1 : BitVec 64)).toNat =
      2 * ol.toNat + 1 := by
    rw [m5_bv64_add1_nat _ (by rw [hshl_ol]; omega), hshl_ol]
  refine ⟨st_u, hstu_base, hstu_scr, hlen_u', hw_u, hperm_u, hdm_u, hmw_u', h2cv_u, hol_lt_u,
    hnw_lt_u, href_u, ?_, ?_, hm_u'⟩
  · intro hb0; rw [zext_toNat _ (by decide)]; unfold fullWatchOffCore
    rw [List.getElem?_eq_getElem (by rw [hwv_u_len]; omega), Option.getD_some]
    exact congrArg BitVec.toNat (m5_list_getElem_of_idx hshl_ol)
  · intro hb1; rw [zext_toNat _ (by decide)]; unfold fullWatchSizeCore
    rw [List.getElem?_eq_getElem (by rw [hwv_u_len]; omega), Option.getD_some]
    exact congrArg BitVec.toNat (m5_list_getElem_of_idx h2ol1)

private theorem m5_prop_chrono_post_loop4 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {st0 st_u : FullState} {ar_s : List (BitVec 32)} {wl_p : Nat} {wu_u : BitVec 64}
    {wv_u ws_f wso_p : List (BitVec 32)} {R : Mem 64 → Prop} {ml_f : Mem 64}
    (hlen_u' : st_u.LengthsOk c) (hw_u : FullWitnessInv c F0 F_cur st_u.core)
    (hdm_u : st_u.core.dense_mode = 0#64)
    (hstu_base : st_u.core =
      { st0.core with
        wvec := wv_u, arena := ar_s, wstk := st_u.core.wstk, wlen := wl_p, wusable := wu_u })
    (hstu_scr : st_u.scratch = { st0.scratch with wsort := wso_p })
    (hperm_u : Full.FullArenaPermEq st0.core st_u.core)
    (hm_f : (FullMem c { st_u with core := { st_u.core with wstk := ws_f } } ⋆ R) ml_f)
    (hws_fl : ws_f.length = c.wcap)
    (hmw_f : ModeWatchesInv F_cur { st_u.core with wstk := ws_f }) :
    ∃ st_f : FullState,
      st_f.LengthsOk c ∧ FullWitnessInv c F0 F_cur st_f.core ∧
      st_f.core =
        { st0.core with
          wvec := wv_u, arena := ar_s, wstk := ws_f, wlen := wl_p, wusable := wu_u } ∧
      st_f.scratch = { st0.scratch with wsort := wso_p } ∧
      Full.FullArenaPermEq st0.core st_f.core ∧ (FullMem c st_f ⋆ R) ml_f := by
  obtain ⟨st_f, hstf_c, hstf_sc, hm_f'⟩ :=
    m5_otfs_opaque_state { st_u.core with wstk := ws_f } st_u.scratch hm_f rfl rfl
  have hlen_f : st_f.LengthsOk c :=
    ⟨by rw [hstf_c]; exact { hlen_u'.core_ok with wstk_len_arr := hws_fl },
     by rw [hstf_sc]; exact hlen_u'.scratch_ok⟩
  have hdm_f : st_f.core.dense_mode = 0#64 := by rw [hstf_c]; exact hdm_u
  have hmw_f' : ModeWatchesInv F_cur st_f.core := by rw [hstf_c]; exact hmw_f
  have hwat_f : WatchesInv F_cur st_f.core := by
    unfold ModeWatchesInv at hmw_f'; simpa only [hdm_f, ↓reduceIte] using hmw_f'
  have hnw_f : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c st_f.core) :=
    fullWitnessInv_nw_congr hlen_f.core_ok.cur_vars_le
      (fullWitnessInv_to_nw hlen_u'.core_ok.cur_vars_le hw_u)
      (by rw [hstf_c]) (by rw [hstf_c]) (by rw [hstf_c]) (by rw [hstf_c]) (by rw [hstf_c])
      (by rw [hstf_c]) (by rw [hstf_c]) (by rw [hstf_c]) (by rw [hstf_c]) (by rw [hstf_c])
      (by rw [hstf_c]) (by rw [hstf_c]) (by rw [hstf_c])
  have hw_f : FullWitnessInv c F0 F_cur st_f.core := fullWitnessInv_of_nw hnw_f hdm_f hwat_f
  have hperm_f : Full.FullArenaPermEq st0.core st_f.core := by
    have h1 : st_f.core.arena_len = st_u.core.arena_len := by rw [hstf_c]
    have h2 : fullArenaClauseRefsCore st_f.core = fullArenaClauseRefsCore st_u.core := by
      simp [fullArenaClauseRefsCore, hstf_c]
    have h3 : ∀ q ∈ fullArenaClauseRefsCore st_u.core,
        fullArenaClauseSizeCore st_f.core q = fullArenaClauseSizeCore st_u.core q ∧
        fullArenaClauseGarbCore st_f.core q = fullArenaClauseGarbCore st_u.core q ∧
        (fullArenaClauseLitsCore st_f.core q).Perm (fullArenaClauseLitsCore st_u.core q) :=
      fun q _ => by
        simp [fullArenaClauseSizeCore, fullArenaClauseGarbCore, fullArenaClauseLitsCore,
          fullArenaHdrCore, hstf_c]
    exact m5_canon_arenaPerm_trans hperm_u ⟨h1, h2, h3⟩
  exact ⟨st_f, hlen_f, hw_f, by rw [hstf_c, hstu_base], by rw [hstf_sc, hstu_scr], hperm_f, hm_f'⟩

private theorem m5_prop_chrono_scan_wp {Γ : Env} {c : FullCfg} {st : FullState}
    {r csz best0 : BitVec 32} {cb nlits : BitVec 64} {R : Mem 64 → Prop}
    {Q : Post [.bool]} {X : XPost} {ml : Mem 64}
    {k_after : Tup Val [i32, i32, i32] → Expr Val Cont [.bool]}
    (hlen : st.LengthsOk c)
    (_hcv64 : st.core.cur_vars < 2 ^ 64) (_h2cv : 2 * st.core.cur_vars < 2 ^ 64)
    (hnlits_val : nlits.toNat = 2 * st.core.cur_vars)
    (hr_bd : r.toNat + 3 + fullArenaClauseSizeCore st.core r.toNat ≤ st.core.arena.length)
    (hcsz_eq : csz.toNat = fullArenaClauseSizeCore st.core r.toNat)
    (hcsz_ge3 : 3 ≤ csz.toNat) (hcb : cb.toNat = r.toNat + 3)
    (hb1_ltv : (st.core.arena[r.toNat + 3 + 1]?.getD 0#32).toNat < 2 * st.core.cur_vars)
    (hml : (FullMem c st ⋆ R) ml)
    (hAfter : ∀ p : Tup Val [i32, i32, i32], 1 ≤ p.snd.fst.toNat → p.snd.fst.toNat < csz.toNat →
      (st.core.arena[r.toNat + 3 + p.snd.fst.toNat]?.getD 0#32).toNat < 2 * st.core.cur_vars →
      wp Γ Q X (k_after p) ml) :
    wp Γ Q X
      (.group (fun Js_1 => .cons (fun (p_70 : Tup Val [i32, i32, i32]) =>
        .let_ (Op.mk (.cmp .ult i32 .bool rfl) (Arg.var p_70.snd.snd.fst, Arg.var csz, ()))
          fun p_71 =>
        .jnz (Arg.var p_71.fst)
          (.let_ (Op.mk (.zext 32 64) (Arg.var p_70.snd.snd.fst, ())) fun p1 =>
           .let_ (Op.mk (.add i64) (Arg.var cb, Arg.var p1.fst, ())) fun p2 =>
           .let_ (Op.mk (.mul i64) (Arg.var p2.fst, Arg.imm 4#64, ())) fun p3 =>
           .let_ (Op.mk (.add i64) (Arg.var c.pArena, Arg.var p3.fst, ())) fun p4 =>
           .load i32 (Arg.var p4.fst) fun ld =>
           .group (fun _Js => .cons (fun (p : Tup Val [i32, i32]) =>
             .let_ (Op.mk (.add i32) (Arg.var p_70.snd.snd.fst, Arg.imm 1#32, ())) fun p_72 =>
             .jump Js_1.fst (Arg.var p.fst, Arg.var p.snd.fst, Arg.var p_72.fst, ())) .nil)
             fun Js =>
             .let_ (Op.mk (.zext 32 64) (Arg.var ld, ())) fun p5 =>
             .let_ (Op.mk (.cmp .ult i64 .bool rfl) (Arg.var p5.fst, Arg.var nlits, ())) fun p6 =>
             .jnz (Arg.var p6.fst)
               (.let_ (Op.mk (.lshr i32) (Arg.var ld, Arg.imm 1#32, ())) fun p7 =>
                .let_ (Op.mk (.zext 32 64) (Arg.var p7.fst, ())) fun p8 =>
                .let_ (Op.mk (.mul i64) (Arg.var p8.fst, Arg.imm 4#64, ())) fun p9 =>
                .let_ (Op.mk (.add i64) (Arg.var c.pLevel, Arg.var p9.fst, ())) fun p10 =>
                .load i32 (Arg.var p10.fst) fun kl =>
                .group (fun _Js_2 => .cons (fun (p : Tup Val [i32, i32]) =>
                  .jump Js.fst (Arg.var p.fst, Arg.var p.snd.fst, ())) .nil) fun Js_in =>
                  .let_ (Op.mk (.cmp .ugt i32 .bool rfl) (Arg.var kl, Arg.var p_70.fst, ()))
                    fun p11 =>
                  .jnz (Arg.var p11.fst)
                    (.jump Js_in.fst (Arg.var kl, Arg.var p_70.snd.snd.fst, ()))
                    (.jump Js_in.fst (Arg.var p_70.fst, Arg.var p_70.snd.fst, ())))
               (.jump Js.fst (Arg.var p_70.fst, Arg.var p_70.snd.fst, ())))
          (k_after p_70)) .nil)
        fun Js => .jump Js.fst (Arg.var best0, Arg.imm 1#32, Arg.imm 2#32, ())) ml := by
  have har_len := hlen.core_ok.arena_len_arr
  have _hlvl_len := hlen.core_ok.lvl_len
  have hcv_le := hlen.core_ok.cur_vars_le
  refine wp_loop_inv (ts := [i32, i32, i32])
    (fun (best, bi, k, ()) mk =>
      1 ≤ bi.toNat ∧ bi.toNat < csz.toNat ∧ 2 ≤ k.toNat ∧ k.toNat ≤ csz.toNat ∧
      (st.core.arena[r.toNat + 3 + bi.toNat]?.getD 0#32).toNat < 2 * st.core.cur_vars ∧ mk = ml)
    (fun (_best, _bi, k, ()) _ => csz.toNat - k.toNat) ?_ ?_
  · intro Jin hJin; c0_hsteps_nogrp
    exact hJin (best0, 1#32, 2#32, ()) ml
      ⟨by decide, by change 1 < csz.toNat; omega, by decide, by change 2 ≤ csz.toNat; omega,
       hb1_ltv, rfl⟩
  · intro Jin (best, bi, k, ⟨⟩) mk ⟨hbi_ge, hbi_lt, hk_ge, hk_le, hbi_ltv, hmk_eq⟩ ih_in
    subst mk
    c0_hsplit
    · have hk_lt : k.toNat < csz.toNat := by assumption
      have hk_csz : k.toNat < fullArenaClauseSizeCore st.core r.toNat := by
        rw [← hcsz_eq]; exact hk_lt
      have hk_idx : (cb + k.setWidth 64).toNat = r.toNat + 3 + k.toNat := by
        have hk32 := BitVec.isLt k
        rw [BitVec.toNat_add, hcb, BitVec.toNat_setWidth,
          Nat.mod_eq_of_lt (show k.toNat < 2 ^ 64 by omega)]
        exact Nat.mod_eq_of_lt (by omega)
      have hcbk_lt : (cb + k.setWidth 64).toNat < st.core.arena.length := by rw [hk_idx]; omega
      have hkp1 : (k + 1#32).toNat = k.toNat + 1 := m5_bv32_add1_toNat (by
        have := BitVec.isLt csz; omega)
      obtain ⟨ck, hck_def⟩ : ∃ ck : BitVec 32,
          ck = st.core.arena[(cb + k.setWidth 64).toNat]'hcbk_lt := ⟨_, rfl⟩
      c0_hsteps_nogrp
      refine wp_load_of (Full.FullArenaTactics.c0_load_full_arena (i := cb + k.setWidth 64)
        hcbk_lt hml) ?_
      rw [← hck_def]
      c0_hsteps_nogrp
      refine wp_join_group (ts := [i32, i32])
        (fun (best', bi', ()) mb =>
          1 ≤ bi'.toNat ∧ bi'.toNat < csz.toNat ∧
          (st.core.arena[r.toNat + 3 + bi'.toNat]?.getD 0#32).toNat < 2 * st.core.cur_vars ∧
          mb = ml) ?_ ?_
      · rintro _ ⟨best', bi', ⟨⟩⟩ mb ⟨hbi1', hbi_lt', hbi_v', hmb_eq⟩
        subst mb
        c0_hsteps_nogrp
        exact ih_in (best', bi', k + 1#32, ()) ml (by dsimp only; rw [hkp1]; omega)
          ⟨hbi1', hbi_lt', by rw [hkp1]; omega, by rw [hkp1]; omega, hbi_v', rfl⟩
      · intro Jbest hJbest
        c0_hsplit
        · have hck_ltv : ck.toNat < 2 * st.core.cur_vars := by
            have hlt_nl : ck.toNat < nlits.toNat := by assumption
            omega
          obtain ⟨hck_get, hck_lvl_lt⟩ := m5_prop_chrono_inner_ck_facts
            (lvl_len := st.core.lvl.length) (by rw [_hlvl_len]; exact hcv_le)
            hk_idx (by omega) hcbk_lt hck_def hck_ltv
          c0_hsteps_nogrp
          refine wp_load_of (Full.FullArenaTactics.c0_load_full_lvl
            (i := BitVec.setWidth 64 (ck >>> 1#32)) hck_lvl_lt hml) ?_
          c0_hsteps_nogrp
          refine wp_join_group (ts := [i32, i32])
            (fun (best', bi', ()) mb =>
              1 ≤ bi'.toNat ∧ bi'.toNat < csz.toNat ∧
              (st.core.arena[r.toNat + 3 + bi'.toNat]?.getD 0#32).toNat < 2 * st.core.cur_vars ∧
              mb = ml) ?_ ?_
          · rintro _ ⟨best', bi', ⟨⟩⟩ mb hpost
            c0_hsteps_nogrp; exact hJbest (best', bi', ()) mb hpost
          · intro Jin2 hJin2; c0_hsteps_nogrp
            · exact hJin2 (_, k, ()) ml ⟨by omega, hk_lt, hck_get, rfl⟩
            · exact hJin2 (best, bi, ()) ml ⟨hbi_ge, hbi_lt, hbi_ltv, rfl⟩
        · c0_hsteps_nogrp
          exact hJbest (best, bi, ()) ml ⟨hbi_ge, hbi_lt, hbi_ltv, rfl⟩
    · c0_hsteps_nogrp
      exact hAfter (best, bi, k, ()) hbi_ge hbi_lt hbi_ltv

private theorem m5_prop_chrono_post_push_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {st st_p : FullState}
    {wv_p ws_p wso_p : List (BitVec 32)} {wl_p : Nat} {wu_p : BitVec 64}
    {cb cb_arg : BitVec 64} {ol r nw l1 l1_arg bi r_arg : BitVec 32}
    {R : Mem 64 → Prop} {Q : Post [.bool]} {X : XPost} {mp : Mem 64}
    {pok : Bool} {k_after : Expr Val Cont [.bool]}
    (hUnw : ∀ a m Q X, Full.fullUnwatchLargeSpec a m Q X →
      Γ "full_unwatch_large" [i64, i32, i32] [] a m Q X)
    (hsp_c : st_p.core = { st.core with wvec := wv_p, wstk := ws_p, wlen := wl_p, wusable := wu_p })
    (hsp_sc : st_p.scratch = { st.scratch with wsort := wso_p })
    (hdm_t : st.core.dense_mode = 0#64)
    (hlen_p : st_p.LengthsOk c) (hw_p : FullWitnessInv c F0 F_cur st_p.core)
    (href : r.toNat ∈ fullArenaClauseRefsCore st.core)
    (hr_bd : r.toNat + 3 + fullArenaClauseSizeCore st.core r.toNat ≤ st.core.arena.length)
    (hbi_ge2 : 2 ≤ bi.toNat) (hbi_csz : bi.toNat < fullArenaClauseSizeCore st.core r.toNat)
    (hcb_eq : cb.toNat = r.toNat + 3) (h1_idx : (cb + 1#64).toNat = r.toNat + 3 + 1)
    (hbi_idx : (cb + bi.setWidth 64).toNat = r.toNat + 3 + bi.toNat)
    (hl1_def : l1 = st.core.arena[(cb + 1#64).toNat]'(by rw [h1_idx]; omega))
    (hnw_def : nw = st.core.arena[(cb + bi.setWidth 64).toNat]'(by rw [hbi_idx]; omega))
    (hol_lt : ol.toNat < 2 * st.core.cur_vars) (hnw_lt : nw.toNat < 2 * st.core.cur_vars)
    (hcb_arg : cb_arg = cb) (hl1_arg : l1_arg = l1) (hr_arg : r_arg = r)
    (hmp : (FullMem c st_p ⋆ R) mp)
    (hOom : ∀ {ml_o : Mem 64},
      (FullMem c { st_p with core := { st_p.core with oom := 1#64 } } ⋆ R) ml_o →
      Q (false, ()) ml_o)
    (hAfter : ∀ (st_u : FullState) (wv_u ws_u : List (BitVec 32)) (wu_u : BitVec 64)
      (ar_s : List (BitVec 32)) (m_u : Mem 64),
      st_u.core =
        { st.core with wvec := wv_u, arena := ar_s, wstk := ws_u, wlen := wl_p, wusable := wu_u } →
      st_u.scratch = { st.scratch with wsort := wso_p } →
      st_u.LengthsOk c → FullWitnessInv c F0 F_cur st_u.core →
      Full.FullArenaPermEq st.core st_u.core → st_u.core.dense_mode = 0#64 →
      ModeWatchesInv F_cur st_u.core → 2 * st_u.core.cur_vars < 2 ^ 31 - 1 →
      ol.toNat < 2 * st_u.core.cur_vars → nw.toNat < 2 * st_u.core.cur_vars →
      r.toNat ∈ fullArenaClauseRefsCore st_u.core →
      (∀ (hb0 : (BitVec.setWidth 64 ol <<< (1 : Nat)).toNat < st_u.core.wvec.length),
        (BitVec.setWidth 64
          (st_u.core.wvec[(BitVec.setWidth 64 ol <<< (1 : Nat)).toNat]'hb0)).toNat =
          fullWatchOffCore st_u.core ol.toNat) →
      (∀ (hb1 : ((BitVec.setWidth 64 ol <<< (1 : Nat)) + (1 : BitVec 64)).toNat <
          st_u.core.wvec.length),
        (BitVec.setWidth 64
          (st_u.core.wvec[((BitVec.setWidth 64 ol <<< (1 : Nat)) +
            (1 : BitVec 64)).toNat]'hb1)).toNat = fullWatchSizeCore st_u.core ol.toNat) →
      (FullMem c st_u ⋆ R) m_u → wp Γ Q X k_after m_u) :
    wp Γ Q X
      (.jnz (Arg.var pok)
        (.let_ (Op.mk (.add i64) (Arg.var cb_arg, Arg.imm 1#64, ())) fun p_80 =>
         .let_ (Op.mk (.mul i64) (Arg.var p_80.fst, Arg.imm 4#64, ())) fun p_81 =>
         .let_ (Op.mk (.add i64) (Arg.var c.pArena, Arg.var p_81.fst, ())) fun p_82 =>
         .store (t := i32) (Arg.var nw) (Arg.var p_82.fst)
           (.let_ (Op.mk (.zext 32 64) (Arg.var bi, ())) fun p_83 =>
            .let_ (Op.mk (.add i64) (Arg.var cb_arg, Arg.var p_83.fst, ())) fun p_84 =>
            .let_ (Op.mk (.mul i64) (Arg.var p_84.fst, Arg.imm 4#64, ())) fun p_85 =>
            .let_ (Op.mk (.add i64) (Arg.var c.pArena, Arg.var p_85.fst, ())) fun p_86 =>
            .store (t := i32) (Arg.var l1_arg) (Arg.var p_86.fst)
              (.call (rs := [.bool]) (as := [i64, i32, i32]) (bs := [])
                "full_unwatch_large" (Arg.var c.hdr, Arg.var l1_arg, Arg.var r_arg, ())
                fun (_ : Tup Val []) => k_after)))
        (.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 760#64, ())) fun p_o =>
         .store (t := i64) (Arg.imm 1#64) (Arg.var p_o.fst)
           (.ret (Arg.imm false, ())))) mp := by
  subst cb_arg; subst l1_arg; subst r_arg
  cases pok with
  | false =>
    refine wp_jnz_of (fun h => by cases h) fun _ => ?_
    c0_hstep
    refine wp_store_sep (Full.FullArenaTactics.store_full_oom 1#64 hmp) fun _ hm_o => ?_
    clear hmp
    c0_hstep
    exact hOom hm_o
  | true =>
    have hsp_ar : st_p.core.arena = st.core.arena := by rw [hsp_c]
    have hst1_bd : (cb + 1#64).toNat < st_p.core.arena.length := by rw [hsp_ar, h1_idx]; omega
    have hstbi_bd : (cb + bi.setWidth 64).toNat <
        (st_p.core.arena.set (cb + 1#64).toNat nw).length := by
      rw [List.length_set, hsp_ar, hbi_idx]; omega
    obtain ⟨ar_s, har_s⟩ : ∃ ar_s, ar_s =
        (st_p.core.arena.set (r.toNat + 3 + 1) nw).set (r.toNat + 3 + bi.toNat) l1 := ⟨_, rfl⟩
    have hl1_sp : l1 = st_p.core.arena[r.toNat + 3 + 1]'(by rw [hsp_ar]; omega) :=
      hl1_def ▸ m5_list_getElem_of_list_idx hsp_ar.symm h1_idx
    have hnw_sp : nw = st_p.core.arena[r.toNat + 3 + bi.toNat]'(by rw [hsp_ar]; omega) :=
      hnw_def ▸ m5_list_getElem_of_list_idx hsp_ar.symm hbi_idx
    have har_s_eq : (st_p.core.arena.set (cb + 1#64).toNat nw).set (cb + bi.setWidth 64).toNat l1 =
        ar_s := by
      rw [h1_idx, hbi_idx, har_s]
    have hperm_st : Full.FullArenaPermEq st.core st.core :=
      ⟨rfl, rfl, fun _ _ => ⟨rfl, rfl, List.Perm.refl _⟩⟩
    refine wp_jnz_of (fun _ => ?_) fun h => by cases h
    c0_hstep; c0_hstep; c0_hstep
    refine wp_store_sep
      (Full.FullArenaTactics.c0_store_full_arena (i := cb + 1#64) nw hst1_bd hmp)
      fun _ hm_s1 => ?_
    clear hmp
    c0_hstep; c0_hstep; c0_hstep; c0_hstep
    refine wp_store_sep
      (Full.FullArenaTactics.c0_store_full_arena (i := cb + BitVec.setWidth 64 bi) l1
        (by simpa using hstbi_bd) hm_s1)
      fun _ hm_s2 => ?_
    clear hm_s1
    obtain ⟨st_s, hsts_c, hsts_sc, hlen_s', hw_s', hperm_s', hm_s'⟩ :=
      m5_prop_chrono_post_swap hsp_c hsp_sc hlen_p hw_p hdm_t hperm_st href hbi_ge2 hbi_csz hr_bd
        har_s hnw_sp hl1_sp (m5_fullMem_of_eq hm_s2 (by dsimp only; rw [har_s_eq]) rfl)
    clear hm_s2
    c0_call hUnw
    refine ⟨c, st_s, R, rfl, hlen_s', hw_s'.watches.layout, hm_s',
      fun wv_u ws_u wu_u m_u hlen_u _ hmw_u hm_u => ?_⟩
    obtain ⟨st_u, hstu_base, hstu_scr, hlen_u', hw_u, hperm_u, hdm_u, hmw_u', h2cv_u, hol_lt_u,
      hnw_lt_u, href_u, hoff_f, hsz_f, hm_u'⟩ :=
      m5_prop_chrono_post_unw hsp_c hsp_sc hsts_c hsts_sc rfl rfl hdm_t hlen_s' hw_s'
        hperm_s' hperm_st href hol_lt hnw_lt hm_u ⟨hlen_u.core_ok, hlen_u.scratch_ok⟩
        (hmw_u F_cur hw_s'.watches)
    exact hAfter st_u wv_u ws_u wu_u ar_s m_u hstu_base hstu_scr hlen_u' hw_u hperm_u hdm_u
      hmw_u' h2cv_u hol_lt_u hnw_lt_u href_u hoff_f hsz_f hm_u'

private theorem m5_prop_chrono_post_unw_loop4_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {st0 st_u : FullState}
    {wv_u ws_u wso_p ar_s : List (BitVec 32)} {wl_p : Nat} {wu_u : BitVec 64}
    {ol r r_arg nw : BitVec 32} {t : BitVec 64} {wvec_arg : BitVec 64} {ol_arg : BitVec 32}
    {R : Mem 64 → Prop} {Q : Post [.bool]} {X : XPost} {m_u : Mem 64} {J_next : Cont []}
    (hwvec_arg : wvec_arg = c.pWvec) (hol_arg : ol_arg = ol) (hr_arg : r_arg = r)
    (hstu_base : st_u.core =
      { st0.core with
        wvec := wv_u, arena := ar_s, wstk := ws_u, wlen := wl_p, wusable := wu_u })
    (hstu_scr : st_u.scratch = { st0.scratch with wsort := wso_p })
    (hlen_u' : st_u.LengthsOk c) (hw_u : FullWitnessInv c F0 F_cur st_u.core)
    (hperm_u : Full.FullArenaPermEq st0.core st_u.core) (hdm_u : st_u.core.dense_mode = 0#64)
    (hmw_u' : ModeWatchesInv F_cur st_u.core) (h2cv_u : 2 * st_u.core.cur_vars < 2 ^ 31 - 1)
    (hol_lt_u : ol.toNat < 2 * st_u.core.cur_vars) (hnw_lt_u : nw.toNat < 2 * st_u.core.cur_vars)
    (hcr_lt31 : r.toNat < 0x80000000) (href_u : r.toNat ∈ fullArenaClauseRefsCore st_u.core)
    (htp1_le : (t + 1#64).toNat ≤ st0.core.trail_end)
    (hoff_f : ∀ (hb0 : (BitVec.setWidth 64 ol <<< (1 : Nat)).toNat < st_u.core.wvec.length),
      (BitVec.setWidth 64
        (st_u.core.wvec[(BitVec.setWidth 64 ol <<< (1 : Nat)).toNat]'hb0)).toNat =
        fullWatchOffCore st_u.core ol.toNat)
    (hsz_f : ∀ (hb1 : ((BitVec.setWidth 64 ol <<< (1 : Nat)) + (1 : BitVec 64)).toNat <
        st_u.core.wvec.length),
      (BitVec.setWidth 64
        (st_u.core.wvec[((BitVec.setWidth 64 ol <<< (1 : Nat)) +
          (1 : BitVec 64)).toNat]'hb1)).toNat = fullWatchSizeCore st_u.core ol.toNat)
    (hm_u' : (FullMem c st_u ⋆ R) m_u)
    (hJ_next : ∀ xs ml,
      (∃ st_n : FullState, M5PropLoopInv c F0 F_cur st0 st_n (t + 1#64) ∧
        (FullMem c st_n ⋆ R) ml) →
      J_next xs ml) :
    wp Γ Q X
      (.let_ (Op.mk (.zext 32 64) (Arg.var ol_arg, ())) fun p =>
       .let_ (Op.mk (.sext 32 64) (Arg.imm 1#32, ())) fun p_87 =>
       .let_ (Op.mk (.shl i64) (Arg.var p.fst, Arg.var p_87.fst, ())) fun p =>
       .let_ (Op.mk (.mul i64) (Arg.var p.fst, Arg.imm 4#64, ())) fun p =>
       .let_ (Op.mk (.add i64) (Arg.var wvec_arg, Arg.var p.fst, ())) fun p =>
       .load i32 (Arg.var p.fst) fun ld_20 =>
       .let_ (Op.mk (.zext 32 64) (Arg.var ld_20, ())) fun p_off =>
       .let_ (Op.mk (.zext 32 64) (Arg.var ol_arg, ())) fun p_88 =>
       .let_ (Op.mk (.sext 32 64) (Arg.imm 1#32, ())) fun p_89 =>
       .let_ (Op.mk (.shl i64) (Arg.var p_88.fst, Arg.var p_89.fst, ())) fun p_90 =>
       .let_ (Op.mk (.add i64) (Arg.var p_90.fst, Arg.imm 1#64, ())) fun p_91 =>
       .let_ (Op.mk (.mul i64) (Arg.var p_91.fst, Arg.imm 4#64, ())) fun p_92 =>
       .let_ (Op.mk (.add i64) (Arg.var wvec_arg, Arg.var p_92.fst, ())) fun p_93 =>
       .load i32 (Arg.var p_93.fst) fun ld_sz =>
       .let_ (Op.mk (.zext 32 64) (Arg.var ld_sz, ())) fun p_94 =>
       (.group (fun (_ : Tup Cont [[]]) =>
          Blocks.cons (fun (_ : Tup Val []) => Expr.jump J_next ()) Blocks.nil) fun Js =>
        .let_ (Op.mk (.cmp .uge (.bits 64) .bool rfl) (Arg.var p_94.fst, Arg.imm 2, ()))
          fun p_60 =>
        .jnz (Arg.var p_60.fst)
          (.let_ (Op.mk (.add (.bits 64)) (Arg.var p_off.fst, Arg.var p_94.fst, ())) fun p_61 =>
           .let_ (Op.mk (.add (.bits 64)) (Arg.var p_off.fst, Arg.imm 2, ())) fun p_62 =>
           .group (fun (_ : Tup Cont [[i64]]) =>
             Blocks.cons (fun (_ : Tup Val [i64]) => Expr.jump Js.fst ()) Blocks.nil) fun Js_b =>
           .group (fun (Js_1 : Tup Cont [[i64]]) =>
             Blocks.cons (fun (p_63 : Tup Val [i64]) =>
               .let_ (Op.mk (.cmp .uge (.bits 64) .bool rfl)
                 (Arg.var p_63.fst, Arg.var p_62.fst, ())) fun p_64 =>
               .jnz (Arg.var p_64.fst)
                 (.let_ (Op.mk (.sub (.bits 64)) (Arg.var p_63.fst, Arg.imm 1, ())) fun p_65 =>
                  .let_ (Op.mk (.mul (.bits 64)) (Arg.var p_65.fst, Arg.imm 4, ())) fun p_66 =>
                  .let_ (Op.mk (.add (.bits 64))
                    (Arg.var c.pWstk, Arg.var p_66.fst, ())) fun p_67 =>
                  .load i32 (Arg.var p_67.fst) fun ld_10 =>
                  .let_ (Op.mk (.cmp .eq (.bits 32) .bool rfl)
                    (Arg.var ld_10, Arg.var r_arg, ())) fun p =>
                  .jnz (Arg.var p.fst)
                    (.let_ (Op.mk (.sub (.bits 64))
                        (Arg.var p_63.fst, Arg.imm 2, ())) fun p =>
                     .let_ (Op.mk (.mul (.bits 64)) (Arg.var p.fst, Arg.imm 4, ())) fun p =>
                     .let_ (Op.mk (.add (.bits 64))
                       (Arg.var c.pWstk, Arg.var p.fst, ())) fun p =>
                     .let_ (Op.mk (.and (.bits 32))
                       (Arg.var nw, Arg.imm 2147483647, ())) fun p_68 =>
                     .store (Arg.var p_68.fst) (Arg.var p.fst)
                       (.jump Js_b.fst (Arg.var p_63.fst, ())))
                    (.let_ (Op.mk (.sub (.bits 64))
                        (Arg.var p_63.fst, Arg.imm 2, ())) fun p =>
                     .let_ (Op.mk (.lshr (.bits 32))
                       (Arg.var ld_10, Arg.imm 31, ())) fun p_68 =>
                     .let_ (Op.mk (.zext 32 64) (Arg.var p_68.fst, ())) fun p_69 =>
                     .let_ (Op.mk (.add (.bits 64))
                       (Arg.var p.fst, Arg.var p_69.fst, ())) fun p =>
                     .jump Js_1.fst (Arg.var p.fst, ())))
                 (.jump Js_b.fst (Arg.var p_63.fst, ()))) Blocks.nil)
           fun Js_l => .jump Js_l.fst (Arg.var p_61.fst, ()))
          (.jump Js.fst ()))) m_u := by
  subst wvec_arg; subst ol_arg; subst r_arg
  have hwv_u_len := hlen_u'.core_ok.wvec_len
  have hcv_le := hlen_u'.core_ok.cur_vars_le
  have hshl_ol : (BitVec.setWidth 64 ol <<< (1 : Nat)).toNat = 2 * ol.toNat := by
    rw [m5_bv64_shl1_nat _ (by rw [zext_toNat ol (by decide)]; omega), zext_toNat ol (by decide)]
  have h2ol1 : ((BitVec.setWidth 64 ol <<< (1 : Nat)) + (1 : BitVec 64)).toNat =
      2 * ol.toNat + 1 := by
    rw [m5_bv64_add1_nat _ (by rw [hshl_ol]; omega), hshl_ol]
  have hbv_shl1 : ∀ x : BitVec 64, x <<< (1 : BitVec 64) = x <<< (1 : Nat) := fun x => by
    apply BitVec.eq_of_toNat_eq; simp
  have hw_u_bd0 : (BitVec.setWidth 64 ol <<< (1 : Nat)).toNat < st_u.core.wvec.length := by
    rw [hshl_ol, hwv_u_len]; omega
  have hw_u_bd1 : ((BitVec.setWidth 64 ol <<< (1 : Nat)) + (1 : BitVec 64)).toNat <
      st_u.core.wvec.length := by
    rw [h2ol1, hwv_u_len]; omega
  have hw_u_bd0' : (BitVec.setWidth 64 ol <<< (1 : BitVec 64)).toNat <
      st_u.core.wvec.length := by
    rw [hbv_shl1]; exact hw_u_bd0
  have hw_u_bd1' : ((BitVec.setWidth 64 ol <<< (1 : BitVec 64)) + 1#64).toNat <
      st_u.core.wvec.length := by
    rw [hbv_shl1]; exact hw_u_bd1
  have hoff_u := hoff_f hw_u_bd0
  have hsz_u := hsz_f hw_u_bd1
  have hoff_u' : (BitVec.setWidth 64 (st_u.core.wvec[(BitVec.setWidth 64 ol <<<
      (1 : BitVec 64)).toNat]'hw_u_bd0')).toNat = fullWatchOffCore st_u.core ol.toNat := by
    rw [m5_list_getElem_of_idx (xs := st_u.core.wvec) (hi := hw_u_bd0') (hj := hw_u_bd0)
      (congrArg BitVec.toNat (hbv_shl1 _))]
    exact hoff_u
  have hsz_u' : (BitVec.setWidth 64 (st_u.core.wvec[((BitVec.setWidth 64 ol <<<
      (1 : BitVec 64)) + 1#64).toNat]'hw_u_bd1')).toNat = fullWatchSizeCore st_u.core ol.toNat := by
    rw [m5_list_getElem_of_idx (xs := st_u.core.wvec) (hi := hw_u_bd1') (hj := hw_u_bd1)
      (congrArg (fun x => (x + 1#64).toNat) (hbv_shl1 _))]
    exact hsz_u
  c0_hstep; c0_hstep; c0_hstep; c0_hstep; c0_hstep
  refine wp_load_of (Full.FullArenaTactics.c0_load_full_wvec hw_u_bd0' hm_u') ?_
  c0_hstep; c0_hstep; c0_hstep; c0_hstep; c0_hstep; c0_hstep; c0_hstep
  refine wp_load_of (Full.FullArenaTactics.c0_load_full_wvec hw_u_bd1' hm_u') ?_
  c0_hstep
  dsimp only
  refine m5_loop4_sz_wp hdm_u hmw_u' hlen_u' h2cv_u hol_lt_u hnw_lt_u rfl
    hcr_lt31 href_u hoff_u' hsz_u' hm_u' ?_
  rintro ⟨⟩ ml_f ⟨ws_f, hm_f, hws_fl, hmw_f⟩
  clear hm_u'
  have hstu_b : st_u.core = { st0.core with
      wvec := wv_u, arena := ar_s, wstk := st_u.core.wstk, wlen := wl_p, wusable := wu_u } := by
    have hw : ws_u = st_u.core.wstk := by rw [hstu_base]
    rw [hstu_base, hw]
  obtain ⟨st_f, hlen_f, hw_f, hstf_base, hstf_scr, hperm_f, hm_f'⟩ :=
    m5_prop_chrono_post_loop4 hlen_u' hw_u hdm_u hstu_b hstu_scr hperm_u hm_f hws_fl hmw_f
  exact hJ_next () ml_f ⟨st_f, ⟨hlen_f, hw_f,
    ⟨wv_u, ar_s, ws_f, wl_p, wu_u, hstf_base⟩,
    ⟨wso_p, hstf_scr⟩, hperm_f, htp1_le⟩, hm_f'⟩

/-- Canonical `Func.wp` proof for `FullM5Otfs.full_prop_lit_chrono` (`Full.fullPropLitSpec`). -/
theorem full_prop_lit_chrono_wp (Γ : Env)
    (hDefrag : ∀ a m Q X, Full.fullWstackDefragSpec a m Q X →
      Γ "full_wstack_defrag" [i64] [] a m Q X)
    (hUnw : ∀ a m Q X, Full.fullUnwatchLargeSpec a m Q X →
      Γ "full_unwatch_large" [i64, i32, i32] [] a m Q X)
    (hRaw : ∀ a m Q X, Full.fullPropLitSpec a m Q X →
      Γ "full_prop_lit_raw" [i64, i32, i64] [.bool] a m Q X)
    (hPush : ∀ a m Q X, Full.fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, Full.fullPropLitSpec a m Q X →
      Func.wp Γ full_prop_lit_chrono_body a m Q X := by
  rintro ⟨h, lit, ignore_ref, ⟨⟩⟩ m0 Q X ⟨c, F0, F_cur, s, R, rfl, hlen0, hw0, hdm0, hoom0, hm0, hQ⟩
  have hmax32 := fullInv_max_vars_lt32 c
  unfold Func.wp full_prop_lit_chrono_body
  c0_hsteps_nogrp
  refine wp_call_of_spec _ _ (hRaw _ _ _ _ ⟨c, F0, F_cur, s, R, rfl, hlen0, hw0, hdm0, hoom0, hm0,
    fun ok0 vals0 flags0 lvl0 rsns0 trl0 tp0 te0 un0 uf0 wv0 ar0 ws0 wl0 wu0
      ct0 cr0 c00 c10 oom0 tk0 wso0 ph0 m1 hlen1 hw1 htr1 hpm1 hF1 hT1 hm1 => ?_⟩)
  dsimp only
  clear hm0
  have hret_early (hoom_z : oom0 = 0#64) : Q (ok0, ()) m1 :=
    m5_prop_chrono_ret_early hQ hlen1 hw1 htr1 hpm1 hF1 hT1 hm1 hoom_z
  c0_hsteps_nogrp
  · have hoom_ne : oom0 ≠ 0#64 := ‹_›
    exact hQ false vals0 flags0 lvl0 rsns0 trl0 tp0 te0 un0 uf0 wv0 ar0 ws0 wl0 wu0
      ct0 cr0 c00 c10 oom0 tk0 wso0 ph0 m1 hlen1 hw1 htr1 hpm1
      (fun _ => Or.inl hoom_ne) (fun hc => by cases hc) hm1
  · exact hret_early ‹_›
  · exact hret_early ‹_›
  · have hoom_z : oom0 = 0#64 := ‹_›
    have hc_lit : ¬ 2 * (s.core.cur_vars % 2 ^ 64) % 2 ^ 64 ≤ lit.toNat := ‹_›
    have hcv_le0 : s.core.cur_vars ≤ c.max_vars := hlen0.core_ok.cur_vars_le
    have hlvl_len0 : lvl0.length = c.max_vars := hlen1.core_ok.lvl_len
    have hlit_v64 : (BitVec.setWidth 64 (lit >>> 1#32)).toNat < lvl0.length := by
      have hcv64 : s.core.cur_vars < 2 ^ 64 := by omega
      have h2cv : 2 * s.core.cur_vars < 2 ^ 64 := by omega
      rw [Nat.mod_eq_of_lt hcv64, Nat.mod_eq_of_lt h2cv] at hc_lit
      rw [m5_bv32_rshift1_toNat]; omega
    c0_hsteps_nogrp
    · exact hret_early hoom_z
    · have hct_ok : ok0 = true → ct0 = s.core.confl_type := fun ht => (hT1 ht).2
      obtain ⟨st0, hst0_eq⟩ : ∃ st0 : FullState, st0 =
          { s with
            core := { s.core with vals := vals0, flags := flags0, lvl := lvl0, rsns := rsns0,
                                  trl := trl0, trail_pos := tp0, trail_end := te0,
                                  unassigned := un0, unflushed := uf0, wvec := wv0, arena := ar0,
                                  wstk := ws0, wlen := wl0, wusable := wu0, confl_type := ct0,
                                  confl_ref := cr0, confl_lit0 := c00, confl_lit1 := c10,
                                  oom := oom0 }
            scratch := { s.scratch with search_ticks := tk0, wsort := wso0, phases := ph0 } } :=
        ⟨_, rfl⟩
      have hceq0 : st0.core =
          { s.core with vals := vals0, flags := flags0, lvl := lvl0, rsns := rsns0,
                        trl := trl0, trail_pos := tp0, trail_end := te0, unassigned := un0,
                        unflushed := uf0, wvec := wv0, arena := ar0, wstk := ws0, wlen := wl0,
                        wusable := wu0, confl_type := ct0, confl_ref := cr0, confl_lit0 := c00,
                        confl_lit1 := c10, oom := oom0 } := by rw [hst0_eq]
      have hsc0 : st0.scratch =
          { s.scratch with search_ticks := tk0, wsort := wso0, phases := ph0 } := by rw [hst0_eq]
      have hcv_eq0 : st0.core.cur_vars = s.core.cur_vars := by rw [hceq0]
      have hte_st0 : st0.core.trail_end = te0 := by rw [hceq0]
      have hoom_0 : st0.core.oom = oom0 := by rw [hceq0]
      have hdm1 : st0.core.dense_mode = 0#64 := by rw [hceq0]; exact hdm0
      have hlen1' : st0.LengthsOk c := by rw [hst0_eq]; exact hlen1
      have hw1' : FullWitnessInv c F0 F_cur st0.core := by rw [hceq0]; exact hw1
      have htr1' : Full.FullTrailExt s.core st0.core := by rw [hceq0]; exact htr1
      have hpm1' : Full.FullArenaPermEq s.core st0.core := by rw [hceq0]; exact hpm1
      have hm1' : (FullMem c st0 ⋆ R) m1 := by rw [hst0_eq]; exact hm1
      have hcf_ok : ok0 = false →
          FullConflictOkW F_cur st0 ∧ (ct0 = 2#64 → cr0 ≠ ignore_ref) := by
        intro hf; rw [hst0_eq]; exact (hF1 hf).resolve_left (fun h => h hoom_z)
      clear hst0_eq hret_early hF1 hT1 hm1 hpm1 hw1 hlen1 hcv_le0 hlvl_len0
      have har_cap64 : c.arena_cap < 2 ^ 64 := by
        have := c.harena; unfold dimacsBound at this; omega
      have hwcap_lt64 : c.wcap < 2 ^ 64 := by
        have := c.hwcap; unfold dimacsBound at this; omega
      have hte_le0 : s.core.trail_end ≤ s.core.cur_vars := hlen0.core_ok.trail_end_le
      have hte_le1 : te0 ≤ st0.core.cur_vars := by
        rw [← hte_st0]; exact hlen1'.core_ok.trail_end_le
      have hte_ge : s.core.trail_end ≤ te0 := by rw [← hte_st0]; exact htr1'.1
      have hcv_le : st0.core.cur_vars ≤ c.max_vars := hlen1'.core_ok.cur_vars_le
      have hte0_lt64 : te0 < 2 ^ 64 := by omega
      have hte_s_lt64 : s.core.trail_end < 2 ^ 64 := by omega
      have htrl_len0 : st0.core.trl.length = c.max_vars := hlen1'.core_ok.trl_len
      refine wp_loop_inv (ts := [i64])
        (fun (t, ()) ml => ∃ st : FullState, M5PropLoopInv c F0 F_cur st0 st t ∧
          (FullMem c st ⋆ R) ml)
        (fun (t, ()) _ => st0.core.trail_end - t.toNat) ?_ ?_
      · intro J hJ; c0_hsteps
        exact hJ (BitVec.ofNat 64 s.core.trail_end, ()) m1
          ⟨st0, ⟨hlen1', hw1',
            ⟨st0.core.wvec, st0.core.arena, st0.core.wstk, st0.core.wlen, st0.core.wusable, rfl⟩,
            ⟨st0.scratch.wsort, rfl⟩,
            ⟨rfl, rfl, fun _ _ => ⟨rfl, rfl, List.Perm.refl _⟩⟩,
            by rw [hte_st0, bv64_ofNat_toNat hte_s_lt64]; exact hte_ge⟩, hm1'⟩
      · intro J (t, ⟨⟩) ml ⟨st, ⟨hlen_t, hw_t, ⟨wv_t, ar_t, ws_t, wl_t, wu_t, hceq_t⟩,
          ⟨wso_t, hsceq_t⟩, hperm_t, htle⟩, hml⟩ ih
        have har_len_t : st.core.arena.length = c.arena_cap := hlen_t.core_ok.arena_len_arr
        have hlvl_len_t : st.core.lvl.length = c.max_vars := hlen_t.core_ok.lvl_len
        have hcv_le_t : st.core.cur_vars ≤ c.max_vars := hlen_t.core_ok.cur_vars_le
        have hoom_t : st.core.oom = 0#64 := by rw [hceq_t, hoom_0]; exact hoom_z
        have hdm_t : st.core.dense_mode = 0#64 := by rw [hceq_t]; exact hdm1
        have hte_eq_t : st.core.trail_end = te0 := by rw [hceq_t]; exact hte_st0
        have hcv_eq_t : st.core.cur_vars = st0.core.cur_vars := by rw [hceq_t]
        have hal_eq_t : st.core.arena_len = st0.core.arena_len := by rw [hceq_t]
        have hcv64_t : st.core.cur_vars < 2 ^ 64 := by rw [hcv_eq_t, hcv_eq0]; omega
        have h2cv_t : 2 * st.core.cur_vars < 2 ^ 64 := by rw [hcv_eq_t, hcv_eq0]; omega
        have hcv_s : st.core.cur_vars = s.core.cur_vars := hcv_eq_t.trans hcv_eq0
        c0_hsplit
        · have ht_lt : t.toNat < te0 := by
            have h1 : t.toNat < st0.core.trail_end % 2 ^ 64 := by rw [hte_st0]; assumption
            rwa [hte_st0, Nat.mod_eq_of_lt hte0_lt64] at h1
          have htp1_nat : (t + 1#64).toNat = t.toNat + 1 :=
            bv64_add1_toNat (by have := hte0_lt64; omega)
          have htp1_le : (t + 1#64).toNat ≤ st0.core.trail_end := by rw [htp1_nat, hte_st0]; omega
          have htrl_lt : t.toNat < st.core.trl.length := by rw [hceq_t, htrl_len0]; omega
          obtain ⟨ol, hol_def⟩ : ∃ ol : BitVec 32, ol = st.core.trl[t.toNat]'htrl_lt := ⟨_, rfl⟩
          have hcont : J (t + 1#64, ()) ml :=
            ih (t + 1#64, ()) ml (by dsimp only; rw [htp1_nat]; omega)
              ⟨st, ⟨hlen_t, hw_t, ⟨wv_t, ar_t, ws_t, wl_t, wu_t, hceq_t⟩, ⟨wso_t, hsceq_t⟩,
                hperm_t, htp1_le⟩, hml⟩
          c0_hsplit
          · c0_hsteps; exact hcont
          · have hol_lt : ol.toNat < 2 * st.core.cur_vars := by
              have hhc : ¬ 2 * (st0.core.cur_vars % 2 ^ 64) % 2 ^ 64 ≤
                  (st.core.trl[t.toNat]'htrl_lt).toNat := by
                rw [hcv_eq0]; assumption
              rw [← hol_def, hcv_eq0, ← hcv_s, Nat.mod_eq_of_lt hcv64_t,
                Nat.mod_eq_of_lt h2cv_t] at hhc
              omega
            have hol_v_lt : ol.toNat / 2 < st.core.cur_vars := by omega
            have hrsn_lt : (ol.setWidth 64 >>> 1#64).toNat < st.core.rsns.length := by
              have hsh : (ol.setWidth 64 >>> 1#64).toNat = ol.toNat / 2 := by
                have := BitVec.isLt ol
                simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; omega
              rw [hsh, hlen_t.core_ok.rsns_len]; omega
            obtain ⟨r, hr_def⟩ : ∃ r : BitVec 32,
                r = st.core.rsns[(ol.setWidth 64 >>> 1#64).toNat]'hrsn_lt := ⟨_, rfl⟩
            have hsh_raw : (BitVec.setWidth 64 (st.core.trl[t.toNat]'htrl_lt >>> 1#32)).toNat =
                (ol.setWidth 64 >>> 1#64).toNat := by
              rw [← hol_def]; simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
            have hdiv_raw : (st.core.trl[t.toNat]'htrl_lt).toNat / 2 =
                (ol.setWidth 64 >>> 1#64).toNat := by
              have := BitVec.isLt ol
              rw [← hol_def]; simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; omega
            have hr_c0_eq : (st.core.rsns[(BitVec.setWidth 64
                (st.core.trl[t.toNat]'htrl_lt >>> 1#32)).toNat]'(by
                  rw [hsh_raw]; exact hrsn_lt)) = r :=
              (m5_list_getElem_of_idx hsh_raw).trans hr_def.symm
            have hr_div_eq :
                st.core.rsns[(st.core.trl[t.toNat]'htrl_lt).toNat / 2]'(by
                  rw [hdiv_raw]; exact hrsn_lt) = r :=
              (m5_list_getElem_of_idx hdiv_raw).trans hr_def.symm
            c0_hsplit
            · c0_hsteps; exact hcont
            · c0_hsplit
              · c0_hsteps; exact hcont
              · have hr_ne : r ≠ 0xFFFFFFFF#32 := by rw [← hr_c0_eq]; assumption
                have hr_lg : (r &&& 0x80000000#32) = 0#32 := by rw [← hr_c0_eq]; assumption
                obtain ⟨href, hsz3, hr_lt_ar, hcr_lt31, hi_r, hdiv_r⟩ := m5_prop_chrono_r_facts
                  hlen_t hw_t (by rw [hte_eq_t]; exact ht_lt) htrl_lt hol_def hrsn_lt hr_def
                  hr_ne hr_lg
                have hr_lt32 : r.toNat < 2 ^ 32 := BitVec.isLt r
                have har_r_lt : (BitVec.setWidth 64 (st.core.rsns[(BitVec.setWidth 64
                    (st.core.trl[t.toNat]'htrl_lt >>> 1#32)).toNat]'(by
                      rw [hsh_raw]; exact hrsn_lt))).toNat < st.core.arena.length := by
                  rw [hr_c0_eq, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]; omega
                have har_r2_lt : (BitVec.setWidth 64 (st.core.rsns[(BitVec.setWidth 64
                    (st.core.trl[t.toNat]'htrl_lt >>> 1#32)).toNat]'(by
                      rw [hsh_raw]; exact hrsn_lt)) + 2#64).toNat < st.core.arena.length := by
                  rw [hr_c0_eq, m5_bv32_zext64_add_toNat r (by omega)]; omega
                have har_r3_lt : (BitVec.setWidth 64 (st.core.rsns[(BitVec.setWidth 64
                    (st.core.trl[t.toNat]'htrl_lt >>> 1#32)).toNat]'(by
                      rw [hsh_raw]; exact hrsn_lt)) + 3#64).toNat < st.core.arena.length := by
                  rw [hr_c0_eq, m5_bv32_zext64_add_toNat r (by omega)]; omega
                have har_r4_lt : (BitVec.setWidth 64 (st.core.rsns[(BitVec.setWidth 64
                    (st.core.trl[t.toNat]'htrl_lt >>> 1#32)).toNat]'(by
                      rw [hsh_raw]; exact hrsn_lt)) + 3#64 + 1#64).toNat <
                    st.core.arena.length := by
                  rw [hr_c0_eq, BitVec.add_assoc, show (3#64 + 1#64 : BitVec 64) = 4#64 by rfl,
                    m5_bv32_zext64_add_toNat r (by omega)]
                  omega
                c0_hsteps_nogrp
                all_goals try exact hcont
                have hidx2 : (r.setWidth 64 + 2#64).toNat = r.toNat + 2 :=
                  m5_bv32_zext64_add_toNat r (by omega)
                have hj2 : r.toNat + 2 < st.core.arena.length := by omega
                obtain ⟨csz, hcsz_def⟩ : ∃ csz : BitVec 32,
                    csz = st.core.arena[(r.setWidth 64 + 2#64).toNat]'(by
                      rw [hidx2]; exact hj2) := ⟨_, rfl⟩
                have hcsz_eq : csz.toNat = fullArenaClauseSizeCore st.core r.toNat := by
                  rw [hcsz_def]
                  have hget2 := m5_list_getElem_of_idx (xs := st.core.arena)
                    (hi := by rw [hidx2]; exact hj2) (hj := hj2) hidx2
                  simp only [fullArenaClauseSizeCore, List.getElem?_eq_getElem hj2,
                    Option.getD_some]
                  exact congrArg BitVec.toNat hget2
                have hcsz_ge3 : 3 ≤ csz.toNat := by rw [hcsz_eq]; exact hsz3
                have hcb_nat : (r.setWidth 64 + 3#64).toNat = r.toNat + 3 :=
                  m5_bv32_zext64_add_toNat r (by omega)
                obtain ⟨cb, hcb_def⟩ : ∃ cb : BitVec 64, cb = r.setWidth 64 + 3#64 := ⟨_, rfl⟩
                have hcb_eq : cb.toNat = r.toNat + 3 := by rw [hcb_def]; exact hcb_nat
                have hcb1_nat : (cb + 1#64).toNat = r.toNat + 3 + 1 := by
                  rw [BitVec.toNat_add, hcb_eq]; simp only [BitVec.toNat_ofNat]
                  exact Nat.mod_eq_of_lt (by omega)
                have har_cb1_eq : ((st.core.rsns[(st.core.trl[t.toNat]'htrl_lt).toNat / 2]'(by
                      rw [hdiv_raw]; exact hrsn_lt)).toNat + BitVec.toNat (3#64) +
                    BitVec.toNat (1#64)) % 2 ^ 64 = (cb + 1#64).toNat := by
                  change ((st.core.rsns[(st.core.trl[t.toNat]'htrl_lt).toNat / 2]'(by
                      rw [hdiv_raw]; exact hrsn_lt)).toNat + 3 + 1) % 2 ^ 64 = _
                  rw [hr_div_eq, hcb1_nat]; exact Nat.mod_eq_of_lt (by omega)
                have hl1_lt_v : (st.core.arena[(cb + 1#64).toNat]'(by
                    rw [hcb1_nat]; omega)).toNat < 2 * st.core.cur_vars := by
                  have hhc : ¬ 2 * (s.core.cur_vars % 2 ^ 64) % 2 ^ 64 ≤
                      (st.core.arena[((st.core.rsns[(st.core.trl[t.toNat]'htrl_lt).toNat / 2]'(
                          by rw [hdiv_raw]; exact hrsn_lt)).toNat + BitVec.toNat (3#64) +
                          BitVec.toNat (1#64)) % 2 ^ 64]'(by
                        rw [har_cb1_eq, hcb1_nat]; omega)).toNat := by
                    assumption
                  rw [m5_list_getElem_of_idx (j := (cb + 1#64).toNat)
                      (hj := by rw [hcb1_nat]; omega) har_cb1_eq,
                    ← hcv_s, Nat.mod_eq_of_lt hcv64_t, Nat.mod_eq_of_lt h2cv_t] at hhc
                  omega
                obtain ⟨l1, hl1_def⟩ : ∃ l1 : BitVec 32,
                    l1 = st.core.arena[(cb + 1#64).toNat]'(by rw [hcb1_nat]; omega) := ⟨_, rfl⟩
                have hl1_lvl_lt : (BitVec.setWidth 64 (l1 >>> 1#32)).toNat <
                    st.core.lvl.length := by
                  rw [hl1_def, hlen_t.core_ok.lvl_len, m5_bv32_rshift1_toNat]; omega
                have hb1_get :
                    (st.core.arena[r.toNat + 3 + 1]?.getD 0#32).toNat <
                    2 * st.core.cur_vars := by
                  have h1lt : r.toNat + 3 + 1 < st.core.arena.length := by omega
                  rw [List.getElem?_eq_getElem h1lt, Option.getD_some,
                    m5_list_getElem_of_idx (xs := st.core.arena) (hi := h1lt)
                      (j := (cb + 1#64).toNat) (hj := by rw [hcb1_nat]; omega) hcb1_nat.symm]
                  exact hl1_lt_v
                have hsh_nat : (BitVec.setWidth 64
                    (st.core.trl[t.toNat]'htrl_lt >>> (1 : Nat))).toNat =
                    (ol.setWidth 64 >>> 1#64).toNat := by
                  simpa only [BitVec.ushiftRight_eq', BitVec.toNat_ofNat,
                    Nat.mod_eq_of_lt (by decide : 1 < 2 ^ 32)] using hsh_raw
                have hr_nat_eq : st.core.rsns[(BitVec.setWidth 64
                    (st.core.trl[t.toNat]'htrl_lt >>> (1 : Nat))).toNat]'(by
                      rw [hsh_nat]; exact hrsn_lt) = r := by
                  simpa only [BitVec.ushiftRight_eq', BitVec.toNat_ofNat,
                    Nat.mod_eq_of_lt (by decide : 1 < 2 ^ 32)] using hr_c0_eq
                have h_rsn_r : ∀ (sh : BitVec 32)
                    (pf : (BitVec.setWidth 64 sh).toNat < st.core.rsns.length),
                    (sh = st.core.trl[t.toNat]'htrl_lt >>> 1#32 ∨
                     sh = st.core.trl[t.toNat]'htrl_lt >>> (1 : Nat)) →
                    st.core.rsns[(BitVec.setWidth 64 sh).toNat]'pf = r := by
                  rintro sh pf (rfl | rfl); exact hr_c0_eq; exact hr_nat_eq
                c0_hsteps_nogrp
                refine m5_prop_chrono_scan_wp hlen_t hcv64_t h2cv_t ?_ hr_lt_ar ?_ ?_ ?_ hb1_get
                  hml ?_
                · dsimp only
                  rw [← hcv_s, m5_bv64_shl1_nat _ (by rw [bv64_ofNat_toNat hcv64_t]; exact h2cv_t),
                    bv64_ofNat_toNat hcv64_t]
                · rw [← hcsz_eq, hcsz_def]
                  exact congrArg BitVec.toNat (m5_list_getElem_of_idx (by
                    try erw [hr_c0_eq]
                    try erw [hr_nat_eq]
                    rfl))
                · refine Nat.le_trans hcsz_ge3 (Nat.le_of_eq (congrArg BitVec.toNat ?_).symm)
                  rw [hcsz_def]
                  refine m5_list_getElem_of_idx (xs := st.core.arena)
                    (hj := by rw [hidx2]; exact hj2) ?_
                  first
                  | exact congrArg (fun x => (BitVec.setWidth 64 x + 2#64).toNat)
                      (h_rsn_r _ _ (Or.inl rfl))
                  | exact congrArg (fun x => (BitVec.setWidth 64 x + 2#64).toNat)
                      (h_rsn_r _ _ (Or.inr rfl))
                · dsimp only
                  refine Eq.trans (congrArg (fun x => (BitVec.setWidth 64 x + 3#64).toNat) ?_)
                    (by rw [← hcb_def]; exact hcb_eq)
                  first
                  | exact h_rsn_r _ _ (Or.inl rfl)
                  | exact h_rsn_r _ _ (Or.inr rfl)
                intro p_ex hbi_ge hbi_lt hbi_ltv
                let bi := p_ex.snd.fst
                have hbi_lt' : bi.toNat < csz.toNat := by
                  refine lt_of_lt_of_eq hbi_lt (congrArg BitVec.toNat ?_)
                  rw [hcsz_def]
                  refine m5_list_getElem_of_idx (xs := st.core.arena)
                    (hj := by rw [hidx2]; exact hj2) ?_
                  first
                  | exact congrArg (fun x => (BitVec.setWidth 64 x + 2#64).toNat)
                      (h_rsn_r _ _ (Or.inl rfl))
                  | exact congrArg (fun x => (BitVec.setWidth 64 x + 2#64).toNat)
                      (h_rsn_r _ _ (Or.inr rfl))
                refine wp_join_group (ts := []) (fun () ml_next => ∃ st_n : FullState,
                    M5PropLoopInv c F0 F_cur st0 st_n (t + 1#64) ∧
                    (FullMem c st_n ⋆ R) ml_next) ?_ ?_
                · rintro _ ⟨⟩ ml_next ⟨st_n, hinv_n, hm_n⟩
                  c0_hsteps
                  exact ih (t + 1#64, ()) ml_next (by dsimp only; rw [htp1_nat]; omega)
                    ⟨st_n, hinv_n, hm_n⟩
                intro J_next hJ_next
                c0_hsplit
                · have hbi_ne1 : bi ≠ 1#32 := by assumption
                  have hbi_ge2 : 2 ≤ bi.toNat := by
                    rcases Nat.eq_or_lt_of_le hbi_ge with heq | hgt
                    · exfalso; exact hbi_ne1 (BitVec.eq_of_toNat_eq heq.symm)
                    · exact hgt
                  have hbi_csz : bi.toNat < fullArenaClauseSizeCore st.core r.toNat := by
                    rw [← hcsz_eq]; exact hbi_lt'
                  have hbi_lt32 : bi.toNat < 2 ^ 32 := BitVec.isLt bi
                  have hbi_idx : (cb + bi.setWidth 64).toNat = r.toNat + 3 + bi.toNat := by
                    rw [BitVec.toNat_add, hcb_eq, BitVec.toNat_setWidth,
                      Nat.mod_eq_of_lt (show bi.toNat < 2 ^ 64 by omega)]
                    exact Nat.mod_eq_of_lt (by omega)
                  have h1_idx : (cb + 1#64).toNat = r.toNat + 3 + 1 := hcb1_nat
                  have hblt_ar : r.toNat + 3 + bi.toNat < st.core.arena.length := by omega
                  have hcb_bi_lt : (cb + bi.setWidth 64).toNat < st.core.arena.length := by
                    rw [hbi_idx]; omega
                  obtain ⟨nw, hnw_def⟩ : ∃ nw : BitVec 32,
                      nw = st.core.arena[(cb + bi.setWidth 64).toNat]'hcb_bi_lt := ⟨_, rfl⟩
                  have hnw_get : nw = st.core.arena[r.toNat + 3 + bi.toNat]?.getD 0#32 := by
                    rw [hnw_def, List.getElem?_eq_getElem hblt_ar, Option.getD_some]
                    exact m5_list_getElem_of_idx (xs := st.core.arena) (hj := hblt_ar) hbi_idx
                  have hnw_ltv : nw.toNat < 2 * st.core.cur_vars := by
                    rw [hnw_get]; exact hbi_ltv
                  have hwlen_le_t : st.core.wlen ≤ c.wcap := hlen_t.core_ok.wlen_le
                  c0_hstep; c0_hstep; c0_hstep; c0_hstep
                  refine wp_load_of (Full.FullArenaTactics.c0_load_full_arena (i := _) (by
                    try erw [hr_c0_eq]
                    try erw [hr_nat_eq]
                    erw [← hcb_def]
                    exact hcb_bi_lt) hml) ?_
                  rw [m5_list_getElem_of_idx (xs := st.core.arena) (hj := hcb_bi_lt) (by
                    try erw [hr_c0_eq]
                    try erw [hr_nat_eq]
                    erw [← hcb_def]
                    try rfl), ← hnw_def]
                  refine wp_join_group (ts := []) (fun () ml_d =>
                    ∃ (st_d : FullState) (wv_d ws_d : List (BitVec 32)) (wl_d : Nat)
                      (wu_d : BitVec 64) (wso_d : List (BitVec 32)),
                      st_d.core = { st.core with wvec := wv_d, wstk := ws_d, wlen := wl_d,
                                                 wusable := wu_d } ∧
                      st_d.scratch = { st.scratch with wsort := wso_d } ∧
                      st_d.LengthsOk c ∧ FullWitnessInv c F0 F_cur st_d.core ∧
                      (FullMem c st_d ⋆ R) ml_d) ?_ ?_
                  · rintro _ ⟨⟩ ml_d ⟨st_d, wv_d, ws_d, wl_d, wu_d, wso_d, hsd_c, hsd_sc,
                      hlen_d, hw_d, hm_d⟩
                    have href_d : r.toNat ∈ fullArenaClauseRefs st_d := by
                      change r.toNat ∈ fullArenaClauseRefsCore st_d.core
                      rwa [show fullArenaClauseRefsCore st_d.core =
                          fullArenaClauseRefsCore st.core by
                        simp [fullArenaClauseRefsCore, hsd_c]]
                    c0_call hPush
                    · refine ⟨c, st_d, R, rfl, hlen_d, hw_d.watches.layout,
                        fun h => absurd h (by decide),
                        fun _ => ⟨by
                          change (_ &&& 0x7FFFFFFF#32) ≠ 0xFFFFFFFF#32
                          exact m5_bv32_mask_lit_lt _,
                          by
                            first
                            | rw [h_rsn_r _ _ (Or.inl rfl)]; exact hr_ne
                            | rw [h_rsn_r _ _ (Or.inr rfl)]; exact hr_ne⟩, hm_d,
                        fun pok wv_p ws_p wl_p wu_p wso_p mp hlen_p hlay_p hpres_o
                          hpok_t hpok_f hmp => ?_⟩
                      clear hm_d
                      obtain ⟨st_p, hsp_c, hsp_sc, hlen_p', hw_p, hm_p'⟩ :=
                        m5_prop_chrono_push_wrap (ol := st.core.trl[t.toNat]'htrl_lt)
                          hlen_d hw_d hsd_c hsd_sc hdm_t href_d hcr_lt31
                          hnw_ltv hmp hlen_p hlay_p hpres_o (fun ht => by
                            obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hpok_t ht
                            refine ⟨h1, h2, h3, h4, h5, fun h2eq => ?_⟩
                            have hr_arg : ∀ {sh pf},
                                (sh = st.core.trl[t.toNat]'htrl_lt >>> 1#32 ∨
                                 sh = st.core.trl[t.toNat]'htrl_lt >>> (1 : Nat)) →
                                ∀ {idx : Nat},
                                ws_p[idx]? =
                                  some (st.core.rsns[(BitVec.setWidth 64 sh).toNat]'pf) →
                                ws_p[idx]? = some r := by
                              intro sh pf hsh idx hidx
                              rwa [h_rsn_r sh pf hsh] at hidx
                            first
                            | exact hr_arg (Or.inl rfl) (h6 h2eq)
                            | exact hr_arg (Or.inr rfl) (h6 h2eq)) hpok_f
                      clear hmp
                      refine m5_prop_chrono_post_push_wp hUnw hsp_c hsp_sc hdm_t
                        hlen_p' hw_p href hr_lt_ar hbi_ge2 hbi_csz hcb_eq h1_idx hbi_idx
                        hl1_def hnw_def hol_lt hnw_ltv ?_ ?_ ?_ hm_p'
                        (fun {ml_o} hm_o =>
                          m5_prop_chrono_oom_done hQ hceq0 hsc0 hceq_t hsceq_t hdm_t htr1 hpm1'
                            hperm_t
                            ⟨by rw [← hsp_c]; exact hlen_p'.core_ok,
                             by rw [← hsp_sc]; exact hlen_p'.scratch_ok⟩
                            (by simpa only [hsp_c] using hw_p)
                            (m5_fullMem_of_eq hm_o (by dsimp only; rw [hsp_c]) hsp_sc)) ?_
                      · rw [hcb_def]
                        first
                        | exact congrArg (fun x => BitVec.setWidth 64 x + 3#64)
                            (h_rsn_r _ _ (Or.inl rfl))
                        | exact congrArg (fun x => BitVec.setWidth 64 x + 3#64)
                            (h_rsn_r _ _ (Or.inr rfl))
                      · rw [hl1_def]
                        refine m5_list_getElem_of_idx ?_
                        rw [hcb_def]
                        first
                        | exact congrArg (fun x => (BitVec.setWidth 64 x + 3 + 1).toNat)
                            (h_rsn_r _ _ (Or.inl rfl))
                        | exact congrArg (fun x => (BitVec.setWidth 64 x + 3 + 1).toNat)
                            (h_rsn_r _ _ (Or.inr rfl))
                      · first | exact h_rsn_r _ _ (Or.inl rfl) | exact h_rsn_r _ _ (Or.inr rfl)
                      clear hml hm_p' hm1'
                      intro st_u wv_u ws_u wu_u ar_s m_u hstu_c hstu_sc hlen_u' hw_u hperm_su
                        hdm_u hmw_u' h2cv_u hol_lt_u hnw_lt_u href_u hoff_f hsz_f hm_u'
                      refine m5_prop_chrono_post_unw_loop4_wp rfl hol_def.symm ?_
                        (by rw [hstu_c, hceq_t]) (by rw [hstu_sc, hsceq_t]) hlen_u' hw_u
                        (m5_canon_arenaPerm_trans hperm_t hperm_su) hdm_u hmw_u' h2cv_u
                        hol_lt_u hnw_lt_u hcr_lt31 href_u htp1_le hoff_f hsz_f hm_u' hJ_next
                      first
                      | exact h_rsn_r _ _ (Or.inl rfl)
                      | exact h_rsn_r _ _ (Or.inr rfl)
                  · intro Jd hJd
                    exact m5_wstack_ensure2_ret_false_wp hDefrag hlen_t hdm_t hw_t.watches hml
                      (fun st_i wv_i ws_i wl_i wu_i wso_i ml_o hsi_c hsi_sc hlen_i
                          hmw_i hm_o => by
                        obtain ⟨hlen_ic, _, hw_ic⟩ := m5_prop_chrono_wit_of_watches hlen_t
                          hw_t hdm_t hsi_c hsi_sc hlen_i hmw_i
                        exact m5_prop_chrono_oom_done hQ hceq0 hsc0 hceq_t hsceq_t hdm_t
                          htr1 hpm1' hperm_t hlen_ic hw_ic
                          (m5_fullMem_of_eq hm_o (by dsimp only; rw [hsi_c]) hsi_sc))
                      (fun _ ml_d ⟨st_d, wv_d, ws_d, wl_d, wu_d, wso_d, hsd_c, hsd_sc,
                          hlen_d, hmw_d, hm_d⟩ => by
                        obtain ⟨_, hw_d, _⟩ := m5_prop_chrono_wit_of_watches hlen_t hw_t
                          hdm_t hsd_c hsd_sc hlen_d hmw_d
                        exact hJd () ml_d ⟨st_d, wv_d, ws_d, wl_d, wu_d, wso_d, hsd_c,
                          hsd_sc, hlen_d, hw_d, hm_d⟩)
                · c0_hsteps
                  exact hJ_next () ml ⟨st, ⟨hlen_t, hw_t,
                    ⟨wv_t, ar_t, ws_t, wl_t, wu_t, hceq_t⟩,
                    ⟨wso_t, hsceq_t⟩, hperm_t, htp1_le⟩, hml⟩
        · c0_hsteps
          exact m5_prop_chrono_ret_wp hQ hceq0 hsc0 hceq_t hsceq_t hoom_z hct_ok hcf_ok
            htr1 hpm1' hperm_t hlen_t hw_t hml

end PropChronoProof

/-! ## 2. Leaf Dispatch `full_prop_lit_wp` & Main Loop `full_propagate_ignore_wp` -/

section PropFastProof

/-- Zero-frame leaf chrono-bypass wrapper `full_prop_lit` (`Full.fullPropLitSpec`). -/
theorem full_prop_lit_wp (Γ : Env)
    (hChrono : ∀ a m Q X, Full.fullPropLitSpec a m Q X →
      Γ "full_prop_lit_chrono" [i64, i32, i64] [.bool] a m Q X)
    (hRaw : ∀ a m Q X, Full.fullPropLitSpec a m Q X →
      Γ "full_prop_lit_raw" [i64, i32, i64] [.bool] a m Q X) :
    ∀ a m Q X, Full.fullPropLitSpec a m Q X →
      Func.wp Γ full_prop_lit_body a m Q X := by
  rintro ⟨h, lit, ignore_ref, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hdm, hoom, hm, hQ⟩
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  have hcv_le := hlen.core_ok.cur_vars_le
  have hlvl_len := hlen.core_ok.lvl_len
  have hnlits_eq :
      ((BitVec.ofNat 64 s.core.cur_vars) <<< (1 : Nat)).toNat = 2 * s.core.cur_vars := by
    have h1 : (BitVec.ofNat 64 s.core.cur_vars).toNat = s.core.cur_vars := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [m5_bv64_shl1_nat _ (by omega), h1]
  have hspec_pre : Full.fullPropLitSpec (c.hdr, lit, ignore_ref, ()) m Q X :=
    ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hdm, hoom, hm, hQ⟩
  unfold Func.wp full_prop_lit_body
  c0_hsteps_nogrp
  refine wp_join_group (ts := []) (fun () m_r => m_r = m) ?_ ?_
  · rintro _ ⟨⟩ m_r rfl
    c0_hsteps
    refine wp_call_of_spec _ _ (hRaw _ _ _ _ hspec_pre)
  · intro Jr hJr
    c0_hsplit
    · have hlit_lt : lit.toNat < 2 * s.core.cur_vars := by omega
      have hvar_lt : (BitVec.setWidth 64 (lit >>> (1 : Nat))).toNat < s.core.lvl.length := by
        rw [zext_toNat _ (by decide), BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
          hlvl_len]
        omega
      c0_hsplit
      · c0_hsteps; exact wp_call_of_spec _ _ (hChrono _ _ _ _ hspec_pre)
      · c0_hsteps; exact hJr () m rfl
    · c0_hsteps; exact hJr () m rfl

/-- Hoisted chrono-bypass propagation loop `full_propagate_ignore`
(`Full.fullPropagateIgnoreSpec`). -/
theorem full_propagate_ignore_wp (Γ : Env)
    (hChrono : ∀ a m Q X, Full.fullPropLitSpec a m Q X →
      Γ "full_prop_lit_chrono" [i64, i32, i64] [.bool] a m Q X)
    (hRaw : ∀ a m Q X, Full.fullPropLitSpec a m Q X →
      Γ "full_prop_lit_raw" [i64, i32, i64] [.bool] a m Q X) :
    ∀ a m Q X, Full.fullPropagateIgnoreSpec a m Q X →
      Func.wp Γ full_propagate_ignore_body a m Q X := by
  rintro ⟨h, ignore_ref, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen0, hw0, hdense0, hm, hQ⟩
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  have hret_st : ∀ (r : BitVec 64) (st : FullState) (ml : Mem 64),
      st.LengthsOk c → FullWitnessInv c F0 F_cur st.core →
      AgreesExcept FastCore.fastPropCoreMask s.core st.core →
      Full.FullTrailExt s.core st.core → Full.FullArenaPermEq s.core st.core →
      st.core.fuel.toNat ≤ s.core.fuel.toNat →
      st.scratch = { s.scratch with
        search_ticks := st.scratch.search_ticks, wsort := st.scratch.wsort,
        phases := st.scratch.phases } →
      (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) →
      (r = 0#64 → st.core.propagated = st.core.trail_end ∧
        st.core.confl_type = s.core.confl_type ∧
        (s.core.oom = 0#64 → st.core.oom = 0#64) ∧
        (s.core.propagated < s.core.trail_end → st.core.fuel.toNat < s.core.fuel.toNat)) →
      (r = 1#64 → st.core.fuel.toNat < s.core.fuel.toNat ∧ st.core.oom = 0#64 ∧
        Full.FullConflictOkW F_cur st ∧
        (st.core.confl_type = 2#64 → st.core.confl_ref ≠ ignore_ref)) →
      (r = 2#64 → st.core.oom ≠ 0#64 ∨ st.core.fuel = 0#64) →
      (s.core.propagated = s.core.trail_end → r = 0#64 ∧ st = s) →
      (FullMem c st ⋆ R) ml → Q (r, ()) ml := by
    intro r st ml hst_l hst_w hag htr hperm hfl hsc hr hr0 hr1 hr2 hnoop hml
    have hst_eq : st =
        { core :=
            { s.core with
              vals := st.core.vals, flags := st.core.flags, lvl := st.core.lvl,
              rsns := st.core.rsns, trl := st.core.trl, trail_pos := st.core.trail_pos,
              trail_end := st.core.trail_end, propagated := st.core.propagated,
              unassigned := st.core.unassigned, unflushed := st.core.unflushed,
              wvec := st.core.wvec, arena := st.core.arena, wstk := st.core.wstk,
              wlen := st.core.wlen, wusable := st.core.wusable, fuel := st.core.fuel,
              confl_type := st.core.confl_type, confl_ref := st.core.confl_ref,
              confl_lit0 := st.core.confl_lit0, confl_lit1 := st.core.confl_lit1,
              oom := st.core.oom }
          scratch := { s.scratch with
            search_ticks := st.scratch.search_ticks, wsort := st.scratch.wsort,
            phases := st.scratch.phases } } := by
      have h1 := hag.get FullCoreState.d_cur; have h2 := hag.get FullCoreState.d_val
      have h3 := hag.get FullCoreState.cur_vars; have h4 := hag.get FullCoreState.arena_len
      have h5 := hag.get FullCoreState.arena_garbage
      have h6 := hag.get FullCoreState.first_reducible
      have h7 := hag.get FullCoreState.num_irred; have h8 := hag.get FullCoreState.num_redundant
      have h9 := hag.get FullCoreState.num_binary; have h10 := hag.get FullCoreState.probing
      have h11 := hag.get FullCoreState.cur_level; have h12 := hag.get FullCoreState.tmp_cnt
      have h13 := hag.get FullCoreState.tmp_len; have h14 := hag.get FullCoreState.min_clr_len
      have h15 := hag.get FullCoreState.min_clr_full; have h16 := hag.get FullCoreState.dense_mode
      have h17 := hag.get FullCoreState.inconsistent; have h18 := hag.get FullCoreState.lit_mark
      have h19 := hag.get FullCoreState.mrk; have h20 := hag.get FullCoreState.tmp
      have h21 := hag.get FullCoreState.min_clr; have h22 := hag.get FullCoreState.frame_trail
      have h23 := hag.get FullCoreState.frame_dec; have h24 := hag.get FullCoreState.repr
      have h25 := hag.get FullCoreState.min_stk
      cases st with | mk stc stsc =>
      cases s with | mk sc ssc =>
      dsimp only at hsc; rw [hsc]
      cases stc; cases sc; simp only at *; subst_vars; rfl
    have hst_l' := hst_l; have hst_w' := hst_w; have htr' := htr; have hperm' := hperm
    rw [hst_eq] at hst_l' hst_w' htr' hperm' hml
    refine hQ r st.core.vals st.core.flags st.core.lvl st.core.rsns st.core.trl st.core.trail_pos
      st.core.trail_end st.core.propagated st.core.unassigned st.core.unflushed st.core.wvec
      st.core.arena st.core.wstk st.core.wlen st.core.wusable st.core.fuel st.core.confl_type
      st.core.confl_ref st.core.confl_lit0 st.core.confl_lit1 st.core.oom
      st.scratch.search_ticks st.scratch.wsort st.scratch.phases ml
      hst_l' hst_w' htr' hperm' hfl hr (fun h0 => hr0 h0) ?_ (fun h2 => hr2 h2) ?_ hml
    · intro h1; have hcf := hr1 h1; rw [hst_eq] at hcf; exact hcf
    · intro hpe; obtain ⟨h0, heq⟩ := hnoop hpe; exact ⟨h0, hst_eq ▸ heq⟩
  have hpr_le0 := hlen0.core_ok.propagated_le
  have hte_le0 := hlen0.core_ok.trail_end_le
  have hcv_le0 := hlen0.core_ok.cur_vars_le
  have hpr_lt64 : s.core.propagated < 2 ^ 64 := by omega
  have hte_lt64 : s.core.trail_end < 2 ^ 64 := by omega
  have hnlits_eq :
      ((BitVec.ofNat 64 s.core.cur_vars) <<< (1 : Nat)).toNat = 2 * s.core.cur_vars := by
    have h1 : (BitVec.ofNat 64 s.core.cur_vars).toNat = s.core.cur_vars := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [m5_bv64_shl1_nat _ (by omega), h1]
  unfold Func.wp full_propagate_ignore_body
  c0_hsteps_nogrp
  · -- Pre-loop `prop >= trail_end`: return `0ULL` with state unchanged
    have hpe : s.core.propagated = s.core.trail_end := by
      have hc' : (BitVec.ofNat 64 s.core.trail_end).toNat ≤
          (BitVec.ofNat 64 s.core.propagated).toNat := by c0_bound
      rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hte_lt64,
        Nat.mod_eq_of_lt hpr_lt64] at hc'
      omega
    exact hret_st 0#64 s m hlen0 hw0 (.refl _ _)
      ⟨Nat.le_refl _, fun _ _ => rfl, fun _ _ => rfl⟩
      ⟨rfl, rfl, fun _ _ => ⟨rfl, rfl, .refl _⟩⟩
      (Nat.le_refl _) rfl (Or.inl rfl)
      (fun _ => ⟨hpe, rfl, fun h => h, fun hlt => by omega⟩)
      (by simp) (by simp) (fun _ => ⟨rfl, rfl⟩) hm
  · -- Pre-loop `prop < trail_end` and `oom != 0`: return `2ULL` with state unchanged
    have hlt0 : s.core.propagated < s.core.trail_end := by
      have hc' : ¬ (BitVec.ofNat 64 s.core.trail_end).toNat ≤
          (BitVec.ofNat 64 s.core.propagated).toNat := by c0_bound
      rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hte_lt64,
        Nat.mod_eq_of_lt hpr_lt64] at hc'
      omega
    have hoom_ne : s.core.oom ≠ 0#64 := by assumption
    exact hret_st 2#64 s m hlen0 hw0 (.refl _ _)
      ⟨Nat.le_refl _, fun _ _ => rfl, fun _ _ => rfl⟩
      ⟨rfl, rfl, fun _ _ => ⟨rfl, rfl, .refl _⟩⟩
      (Nat.le_refl _) rfl (Or.inr (Or.inr rfl))
      (by simp) (by simp) (fun _ => Or.inl hoom_ne) (fun hpe => by omega) hm
  · -- Active loop: `s.core.propagated < s.core.trail_end` and `s.core.oom = 0#64`
    have hlt0 : s.core.propagated < s.core.trail_end := by
      have hc' : ¬ (BitVec.ofNat 64 s.core.trail_end).toNat ≤
          (BitVec.ofNat 64 s.core.propagated).toNat := by c0_bound
      rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hte_lt64,
        Nat.mod_eq_of_lt hpr_lt64] at hc'
      omega
    have hoom0 : s.core.oom = 0#64 := by assumption
    refine wp_loop_group
      (fun rem (prop_v, fuel_v, ()) ml => ∃ memSt : FullState,
        rem = fuel_v.toNat ∧ memSt.LengthsOk c ∧ FullWitnessInv c F0 F_cur memSt.core ∧
        memSt.core.fuel = s.core.fuel ∧ memSt.core.propagated = prop_v.toNat ∧
        memSt.core.oom = 0#64 ∧
        AgreesExcept FastCore.fastPropCoreMask s.core memSt.core ∧
        Full.FullTrailExt s.core memSt.core ∧ Full.FullArenaPermEq s.core memSt.core ∧
        fuel_v.toNat ≤ s.core.fuel.toNat ∧
        memSt.scratch = { s.scratch with
          search_ticks := memSt.scratch.search_ticks, wsort := memSt.scratch.wsort,
          phases := memSt.scratch.phases } ∧
        memSt.core.confl_type = s.core.confl_type ∧
        (fuel_v.toNat = s.core.fuel.toNat →
          { memSt with core := { memSt.core with fuel := fuel_v } } = s) ∧
        (FullMem c memSt ⋆ R) ml) ?_ ?_
    · rintro L rem ⟨prop_v, fuel_v, ⟨⟩⟩ ml ih
        ⟨memSt, rfl, hml_l, hml_w, hmfuel, hmprop, hoom_st, hag, htr, hperm, hfuel_le, hsc,
          hct_pres, hsame, hml⟩
      have hcl := hml_l.core_ok
      have hcv_le := hcl.cur_vars_le
      have htl := hcl.trl_len; have hte_le := hcl.trail_end_le; have hpr_le := hcl.propagated_le
      have hdm_st : memSt.core.dense_mode = 0#64 :=
        (hag.get FullCoreState.dense_mode).trans hdense0
      have hcv_eq : memSt.core.cur_vars = s.core.cur_vars := hag.get FullCoreState.cur_vars
      c0_hsplit
      · -- `prop < trail_end`
        have hpr_lt : prop_v.toNat < memSt.core.trail_end := by c0_bound
        c0_hsplit
        · -- `fuel == 0`
          c0_hsteps
          let finSt : FullState :=
            { memSt with core := { memSt.core with propagated := prop_v.toNat, fuel := fuel_v } }
          exact hret_st 2#64 finSt _
            ⟨{ hcl with propagated_le := by dsimp [finSt]; omega }, hml_l.scratch_ok⟩
            (hml_w.with_fuel_prop fuel_v prop_v.toNat)
            (hag.update fun k => { k with propagated := prop_v.toNat, fuel := fuel_v })
            (FastCore.fastTrailExt_congr htr rfl rfl rfl) hperm hfuel_le hsc (Or.inr (Or.inr rfl))
            (by simp) (by simp) (fun _ => Or.inr hc) (fun hpe => by omega) (by assumption)
        · -- `fuel != 0`: pop `lit = trl[prop]`, advance `h->propagated`, dispatch chrono vs raw
          have hfuel_sub : (fuel_v - 1#64).toNat = fuel_v.toNat - 1 :=
            Full.bv64_sub1_toNat hc
          have hfuel_pos : 0 < fuel_v.toNat :=
            Nat.pos_of_ne_zero fun h0 => hc (BitVec.eq_of_toNat_eq (by simpa using h0))
          have hpr1 : (prop_v + (1 : BitVec 64)).toNat = prop_v.toNat + 1 := by c0_bound
          let memSt1 : FullState :=
            { memSt with core := { memSt.core with propagated := prop_v.toNat + 1 } }
          have hlen1 : memSt1.LengthsOk c :=
            ⟨{ hcl with propagated_le := by dsimp [memSt1]; omega }, hml_l.scratch_ok⟩
          have hw1 : FullWitnessInv c F0 F_cur memSt1.core := hml_w.with_fuel_prop _ _
          have hag1 : AgreesExcept FastCore.fastPropCoreMask s.core memSt1.core :=
            hag.update fun k => { k with propagated := memSt1.core.propagated }
          c0_hsteps_nogrp
          have hm1_mem : (FullMem c memSt1 ⋆ R) m := by
            simpa only [memSt1, show (prop_v + (1 : BitVec 64)).toNat = prop_v.toNat + 1 from hpr1]
              using hm
          refine wp_join_group (ts := [.bool])
            (fun (ok, ()) m2 => ∃ memSt2 : FullState,
              memSt2.LengthsOk c ∧ FullWitnessInv c F0 F_cur memSt2.core ∧
              memSt2.core.fuel = s.core.fuel ∧ memSt2.core.propagated = prop_v.toNat + 1 ∧
              AgreesExcept FastCore.fastPropCoreMask s.core memSt2.core ∧
              Full.FullTrailExt s.core memSt2.core ∧ Full.FullArenaPermEq s.core memSt2.core ∧
              memSt2.scratch = { s.scratch with
                search_ticks := memSt2.scratch.search_ticks, wsort := memSt2.scratch.wsort,
                phases := memSt2.scratch.phases } ∧
              (ok = false → memSt2.core.oom ≠ 0#64 ∨
                (Full.FullConflictOkW F_cur memSt2 ∧
                  (memSt2.core.confl_type = 2#64 → memSt2.core.confl_ref ≠ ignore_ref))) ∧
              (ok = true → memSt2.core.oom = 0#64 ∧ memSt2.core.confl_type = s.core.confl_type) ∧
              (FullMem c memSt2 ⋆ R) m2) ?_ ?_
          · rintro _ ⟨ok, ⟨⟩⟩ m2 ⟨memSt2, hlen2, hw2, hfuel2, hprop2, hag2, htr12, hperm12, hsc2,
              hcf, hok_t_spec, hm2⟩
            have hfl2_lt : (fuel_v - 1#64).toNat < s.core.fuel.toNat := by omega
            c0_hsteps
            · -- `ok = true`
              have hok_t : ok = true := by assumption
              obtain ⟨hoom2, hct2⟩ := hok_t_spec hok_t
              exact ih (fuel_v - 1#64).toNat (prop_v + 1#64, fuel_v - 1#64, ()) m2 (by omega)
                ⟨memSt2, rfl, hlen2, hw2, hfuel2, hprop2.trans hpr1.symm, hoom2, hag2, htr12,
                 hperm12, by omega, hsc2, hct2, fun heq => by omega, hm2⟩
            · -- `ok = false` and `oom != 0`
              let finSt2 : FullState :=
                { memSt2 with core := { memSt2.core with fuel := fuel_v - 1#64 } }
              exact hret_st 2#64 finSt2 _
                ⟨{ hlen2.core_ok with vals_len := hlen2.core_ok.vals_len }, hlen2.scratch_ok⟩
                (hw2.with_fuel_prop _ _)
                (hag2.update fun k => { k with fuel := fuel_v - 1#64 })
                (FastCore.fastTrailExt_congr htr12 rfl rfl rfl) hperm12
                (by dsimp [finSt2]; omega) hsc2 (Or.inr (Or.inr rfl))
                (by simp) (by simp) (fun _ => Or.inl hc) (fun hpe => by omega) (by assumption)
            · -- `ok = false` and `oom == 0`
              have hok_f : ok = false := by assumption
              have hoom2_0 : memSt2.core.oom = 0#64 := by assumption
              have ⟨hcf_ok, hcf_ign⟩ := (hcf hok_f).resolve_left (fun h => h hoom2_0)
              let finSt2 : FullState :=
                { memSt2 with core := { memSt2.core with fuel := fuel_v - 1#64 } }
              exact hret_st 1#64 finSt2 _
                ⟨{ hlen2.core_ok with vals_len := hlen2.core_ok.vals_len }, hlen2.scratch_ok⟩
                (hw2.with_fuel_prop _ _)
                (hag2.update fun k => { k with fuel := fuel_v - 1#64 })
                (FastCore.fastTrailExt_congr htr12 rfl rfl rfl) hperm12
                (by dsimp [finSt2]; omega) hsc2 (Or.inr (Or.inl rfl)) (by simp)
                (fun _ => ⟨by dsimp [finSt2]; exact hfl2_lt, hoom2_0,
                  by simpa only [Full.FullConflictOkW, fullArenaClauseRefs, fullArenaClauseGarb,
                       fullArenaClauseLits, fullArenaClauseRefsCore, fullArenaClauseGarbCore,
                       fullArenaClauseLitsCore, fullArenaClauseSizeCore, fullArenaHdrCore,
                       finSt2] using hcf_ok,
                  hcf_ign⟩)
                (by simp) (fun hpe => by omega) (by assumption)
          · intro Jok hJok
            have hcall_post : ∀ (lit_arg : BitVec 32),
                Full.fullPropLitSpec (c.hdr, lit_arg, ignore_ref, ()) _
                  (fun (ok, ()) m2 => Jok (ok, ()) m2) X := fun lit_arg =>
              ⟨c, F0, F_cur, memSt1, R, rfl, hlen1, hw1, hdm_st, hoom_st, hm1_mem,
                fun ok vals' flags' lvl' rsns' trl' tp' te' unas' unfl' wvec' arena' wstk' wlen' wu'
                  ctype' cref' c0' c1' oom' ticks' wsort' phases' m2 hlen2 hw2 htr2 hperm2
                  hcf hok_t_spec hm2 => by
                  let memSt2 : FullState :=
                    { core :=
                        { memSt1.core with
                          vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
                          trail_pos := tp', trail_end := te', unassigned := unas',
                          unflushed := unfl', wvec := wvec', arena := arena', wstk := wstk',
                          wlen := wlen', wusable := wu', confl_type := ctype', confl_ref := cref',
                          confl_lit0 := c0', confl_lit1 := c1', oom := oom' }
                      scratch := { memSt1.scratch with
                        search_ticks := ticks', wsort := wsort', phases := phases' } }
                  refine hJok (ok, ()) m2 ⟨memSt2, hlen2, hw2, hmfuel, rfl,
                    hag1.update (fun k => { k with
                      vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
                      trail_pos := tp', trail_end := te', unassigned := unas', unflushed := unfl',
                      wvec := wvec', arena := arena', wstk := wstk', wlen := wlen', wusable := wu',
                      confl_type := ctype', confl_ref := cref', confl_lit0 := c0',
                      confl_lit1 := c1', oom := oom' }),
                    FastCore.fastTrailExt_trans
                      (FastCore.fastTrailExt_congr htr (k2 := memSt1.core) rfl rfl rfl) htr2,
                    FastCore.fastArenaPerm_trans hperm hperm2,
                    by dsimp [memSt2, memSt1]; rw [hsc], hcf,
                    fun hok => let ⟨ho, hct⟩ := hok_t_spec hok; ⟨ho, hct.trans hct_pres⟩, hm2⟩⟩
            c0_hsteps_nogrp
            refine wp_join_group (ts := []) (fun () me => me = m) ?_ ?_
            · rintro _ ⟨⟩ me rfl
              c0_hsteps
              exact wp_call_of_spec _ _ (hRaw _ _ _ _ (hcall_post _))
            · intro Jelse hJelse
              c0_hsplit
              · c0_hsplit
                · have hlit_lt : (memSt.core.trl[prop_v.toNat]'(by omega)).toNat <
                      2 * s.core.cur_vars := by omega
                  have hvar_lt :
                      (BitVec.setWidth 64 ((memSt.core.trl[prop_v.toNat]'(by omega)) >>>
                        (1 : Nat))).toNat < memSt1.core.lvl.length := by
                    rw [zext_toNat _ (by decide), BitVec.toNat_ushiftRight,
                      Nat.shiftRight_eq_div_pow, hlen1.core_ok.lvl_len]
                    omega
                  c0_hsplit
                  · c0_hsteps; exact wp_call_of_spec _ _ (hChrono _ _ _ _ (hcall_post _))
                  · c0_hsteps; exact hJelse () _ rfl
                · c0_hsteps; exact hJelse () _ rfl
              · c0_hsteps; exact hJelse () _ rfl
      · -- Loop exit `!(prop < trail_end)`
        have hpr_eq : prop_v.toNat = memSt.core.trail_end := by c0_bound
        c0_hsteps
        let finSt : FullState :=
          { memSt with core := { memSt.core with propagated := prop_v.toNat, fuel := fuel_v } }
        exact hret_st 0#64 finSt _
          ⟨{ hcl with propagated_le := by dsimp [finSt]; omega }, hml_l.scratch_ok⟩
          (hml_w.with_fuel_prop fuel_v prop_v.toNat)
          (hag.update fun k => { k with propagated := prop_v.toNat, fuel := fuel_v })
          (FastCore.fastTrailExt_congr htr rfl rfl rfl) hperm hfuel_le hsc (Or.inl rfl)
          (fun _ => ⟨by dsimp [finSt]; exact hpr_eq, hct_pres, fun _ => hoom_st, fun _ => by
            by_cases hf : fuel_v.toNat = s.core.fuel.toNat
            · have hsame_st := hsame hf
              have : finSt = s := by
                rw [← hsame_st]; dsimp [finSt]; rw [← hmprop]
              have hpe_s : s.core.propagated = s.core.trail_end := by
                have h1 := congrArg (fun x => x.core.propagated) this
                have h2 := congrArg (fun x => x.core.trail_end) this
                dsimp [finSt] at h1 h2; omega
              omega
            · dsimp [finSt]; omega⟩)
          (by simp) (by simp) (fun hpe => by omega) (by assumption)
    · intro L hL; c0_hsteps
      exact hL s.core.fuel.toNat (BitVec.ofNat 64 s.core.propagated, s.core.fuel, ()) m
        ⟨s, rfl, hlen0, hw0, rfl, by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpr_lt64], hoom0,
         .refl _ _, ⟨Nat.le_refl _, fun _ _ => rfl, fun _ _ => rfl⟩,
         ⟨rfl, rfl, fun _ _ => ⟨rfl, rfl, .refl _⟩⟩, Nat.le_refl _, rfl, rfl,
         fun _ => by cases s with | mk sc ssc => cases sc; rfl, hm⟩

end PropFastProof

end LeanQbe.T.Examples.Kissat.FullM5Otfs
