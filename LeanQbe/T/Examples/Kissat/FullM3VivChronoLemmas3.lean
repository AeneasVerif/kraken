module

public import LeanQbe.T.Examples.Kissat.FullM3VivChrono
public import LeanQbe.T.Examples.Kissat.FullSpec
public import LeanQbe.T.Examples.Kissat.FullPropDecLemmas2
public import LeanQbe.T.Logic.C0HeadStep
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat M3a `Func.wp` Proofs — Part 3 (`full_prop_lit` Chronological `lits[1]` Swap)

Proves `Func.wp` UNSAT soundness (`XPost := False`, `0` SAT proofs) for
`FullM3VivChrono.full_prop_lit` against canonical `Full.fullPropLitSpec`:
- Calls M2 `full_prop_lit_raw` under `Full.fullPropLitSpec`, returning immediately on
  conflict/OOM or when `t0 >= te`, `lit >= 2 * cur_vars`, or `level[lit >> 1] >= cur_level`.
- Otherwise scans newly propagated trail entries `t ∈ [t0, te)`, finding the highest-level literal
  at index `bi ∈ [1, csz)` in each large reason clause (`ar[cb] == ol`), and when `bi ≠ 1` pushes
  `(ol & 0x7FFFFFFF, r)` onto `nw`'s watch list before swapping `ar[cb + 1] ↔ ar[cb + bi]`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM3VivChrono

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open Kraken.Bedrock2.Test

section PropLitProof

open scoped FullArenaTactics FullPropDecTactics

local elab "c0_hsteps_np" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { pruneJnz := false } 10000

private theorem list_getElem_idx {α : Type _} {xs : List α} {i j : Nat}
    (h : i = j) (hi : i < xs.length) (hj : j < xs.length) : xs[i]'hi = xs[j]'hj := by
  subst h; rfl

private theorem bv32_rshift1_toNat (x : BitVec 32) :
    (BitVec.setWidth 64 (x >>> 1#32)).toNat = x.toNat / 2 := by
  have h1 : (x >>> 1#32).toNat < 2 ^ 32 := BitVec.isLt _
  have h2 : (x >>> 1#32).toNat = x.toNat / 2 := by
    simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega), h2]

private theorem pd_trailExt_of_canon {k1 k2 : FullCoreState}
    (h : Full.FullTrailExt k1 k2) : FullPropDecSpecs.FullTrailExt k1 k2 :=
  ⟨h.1, h.2.1, h.2.2⟩

private theorem canon_trailExt_of_pd {k1 k2 : FullCoreState}
    (h : FullPropDecSpecs.FullTrailExt k1 k2) : Full.FullTrailExt k1 k2 :=
  ⟨h.te_ge, h.trl_pref, h.lvl_pres⟩

private theorem canon_arenaPerm_trans {k1 k2 k3 : FullCoreState}
    (h1 : Full.FullArenaPermEq k1 k2) (h2 : Full.FullArenaPermEq k2 k3) :
    Full.FullArenaPermEq k1 k3 :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, fun r hr =>
    let ⟨s1, g1, p1⟩ := h1.2.2 r hr
    let ⟨s2, g2, p2⟩ := h2.2.2 r (h1.2.1.symm ▸ hr)
    ⟨s2.trans s1, g2.trans g1, p2.trans p1⟩⟩

private theorem canon_arenaPerm_of_pd {k1 k2 : FullCoreState} (hal : k2.arena_len = k1.arena_len)
    (h : FullPropDecSpecs.FullArenaPermEq k1 k2) : Full.FullArenaPermEq k1 k2 :=
  ⟨hal, h.1, h.2⟩

private theorem watchesInv_after_push {F_cur : List (List Nat)} {s : FullState}
    {nw w0 cref : BitVec 32} {wv' ws' : List (BitVec 32)} {wl' : Nat} {wu' : BitVec 64}
    {pok : Bool}
    (hwat : WatchesInv F_cur s.core)
    (hlit : nw.toNat < 2 * s.core.cur_vars)
    (hflag : (w0 &&& 0x80000000#32) = 0#32)
    (hcr_lt : cref.toNat < 0x80000000)
    (hcr_ref : cref.toNat ∈ fullArenaClauseRefsCore s.core)
    (hlay' : WatchStackLayout
      { s.core with wvec := wv', wstk := ws', wlen := wl', wusable := wu' })
    (hpres_o : ∀ l < 2 * s.core.cur_vars, l ≠ nw.toNat →
      fullWatchSizeCore { s.core with wvec := wv', wstk := ws', wlen := wl', wusable := wu' } l =
        fullWatchSizeCore s.core l ∧
      ∀ k < fullWatchSizeCore s.core l,
        ws'[fullWatchOffCore { s.core with wvec := wv', wstk := ws', wlen := wl', wusable := wu' }
          l + k]? =
        s.core.wstk[fullWatchOffCore s.core l + k]?)
    (hpok_t : pok = true →
      fullWatchSizeCore { s.core with wvec := wv', wstk := ws', wlen := wl', wusable := wu' }
        nw.toNat = fullWatchSizeCore s.core nw.toNat + 2 ∧
      (∀ k < fullWatchSizeCore s.core nw.toNat,
        ws'[fullWatchOffCore { s.core with wvec := wv', wstk := ws', wlen := wl', wusable := wu' }
          nw.toNat + k]? =
        s.core.wstk[fullWatchOffCore s.core nw.toNat + k]?) ∧
      ws'[fullWatchOffCore { s.core with wvec := wv', wstk := ws', wlen := wl', wusable := wu' }
        nw.toNat + fullWatchSizeCore s.core nw.toNat]? = some w0 ∧
      ws'[fullWatchOffCore { s.core with wvec := wv', wstk := ws', wlen := wl', wusable := wu' }
        nw.toNat + fullWatchSizeCore s.core nw.toNat + 1]? = some cref)
    (hpok_f : pok = false →
      fullWatchSizeCore { s.core with wvec := wv', wstk := ws', wlen := wl', wusable := wu' }
        nw.toNat = fullWatchSizeCore s.core nw.toNat ∧
      ∀ k < fullWatchSizeCore s.core nw.toNat,
        ws'[fullWatchOffCore { s.core with wvec := wv', wstk := ws', wlen := wl', wusable := wu' }
          nw.toNat + k]? =
        s.core.wstk[fullWatchOffCore s.core nw.toNat + k]?) :
    WatchesInv F_cur { s.core with wvec := wv', wstk := ws', wlen := wl', wusable := wu' } := by
  let k' : FullCoreState := { s.core with wvec := wv', wstk := ws', wlen := wl', wusable := wu' }
  have hF : (cnfOfClauses F_cur).Entails (cnfOfClauses F_cur) := by
    rw [CNF.entails_def]; exact fun _ hx => hx
  have hsub : ∀ r ∈ fullArenaClauseRefsCore s.core, r ∈ fullArenaClauseRefsCore k' := fun _ h => h
  refine ⟨hlay', fun l hl => ?_⟩
  by_cases hln : l = nw.toNat
  · subst hln
    cases pok with
    | false =>
      obtain ⟨hsz, hget⟩ := hpok_f rfl
      change WatchSliceOk F_cur k' nw.toNat (fullWatchOffCore k' nw.toNat)
        (fullWatchSizeCore k' nw.toNat)
      rw [hsz]
      exact WatchSliceOk.relocate (k := s.core) (k' := k') hF (Nat.le_refl _) hsub hget
        (hwat.slices nw.toNat hlit)
    | true =>
      obtain ⟨hsz, hget, hw0, hcr⟩ := hpok_t rfl
      change WatchSliceOk F_cur k' nw.toNat (fullWatchOffCore k' nw.toNat)
        (fullWatchSizeCore k' nw.toNat)
      rw [hsz]
      exact WatchSliceOk.append_large (k := s.core) (k' := k') (Nat.le_refl _) hsub hget
        (hwat.slices nw.toNat hlit) hw0 hcr hflag hcr_lt hcr_ref
  · obtain ⟨hsz, hget⟩ := hpres_o l hl hln
    change WatchSliceOk F_cur k' l (fullWatchOffCore k' l) (fullWatchSizeCore k' l)
    rw [hsz]
    exact WatchSliceOk.relocate (k := s.core) (k' := k') hF (Nat.le_refl _) hsub hget
      (hwat.slices l hl)

private theorem bv32_mask_lit_lt (ol : BitVec 32) : (ol &&& 0x7FFFFFFF#32) ≠ 0xFFFFFFFF#32 := by
  intro hff
  have h := bv32_mask7f_flag0 ol
  rw [hff] at h
  exact absurd h (by decide)

private theorem full_prop_swap_preserves_inv {c : FullCfg} {F0 : CNF Nat}
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
    canon_arenaPerm_trans hperm0 (canon_arenaPerm_of_pd rfl hperm')⟩

private theorem bv32_bit31_zero : (0#32)[31] = false := by decide
private theorem bv32_bit31_msb : (0x80000000#32)[31] = true := by decide

private theorem bv32_zext64_add_toNat (r : BitVec 32) {k : Nat} (hk : r.toNat + k < 2 ^ 64) :
    (r.setWidth 64 + BitVec.ofNat 64 k).toNat = r.toNat + k := by
  rw [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.le_add_right _ _) hk),
    Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega)]
  exact Nat.mod_eq_of_lt hk

private theorem bv32_add1_toNat {x : BitVec 32} (hx : x.toNat + 1 < 2 ^ 32) :
    (x + 1#32).toNat = x.toNat + 1 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 1 < 2 ^ 32)]
  exact Nat.mod_eq_of_lt hx

private structure M3PropLoopInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (st0 st : FullState) (t : BitVec 64) : Prop where
  len : st.LengthsOk c
  wit : FullWitnessInv c F0 F_cur st.core
  core_eq : ∃ wv' ar' ws' wl' wu',
    st.core = { st0.core with wvec := wv', arena := ar', wstk := ws', wlen := wl', wusable := wu' }
  sc_eq : ∃ wsort', st.scratch = { st0.scratch with wsort := wsort' }
  perm : Full.FullArenaPermEq st0.core st.core
  tle : t.toNat ≤ st0.core.trail_end

private theorem m3_prop_lit_push_wit {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {st : FullState} {ol r nw : BitVec 32} {pok : Bool}
    {wv' ws' : List (BitVec 32)} {wl' : Nat} {wu' : BitVec 64} {wso' : List (BitVec 32)}
    (hlen_t : st.LengthsOk c) (hw_t : FullWitnessInv c F0 F_cur st.core)
    (hdm_t : st.core.dense_mode = 0#64) (href : r.toNat ∈ fullArenaClauseRefs st)
    (hcr_lt31 : r.toNat < 0x80000000) (hnw_ltv : nw.toNat < 2 * st.core.cur_vars)
    (hlen_p : ({ st with
        core := { st.core with wvec := wv', wstk := ws', wlen := wl', wusable := wu' }
        scratch := { st.scratch with wsort := wso' } } : FullState).LengthsOk c)
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
  have hwat_st : WatchesInv F_cur st.core := by
    have := hw_t.watches; simpa [ModeWatchesInv, hdm_t] using this
  have hwat_p := watchesInv_after_push hwat_st hnw_ltv
    (bv32_mask7f_flag0 ol) hcr_lt31 href hlay_p hpres_o hpok_t hpok_f
  have hnw_p : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c
      { st.core with wvec := wv', wstk := ws', wlen := wl', wusable := wu' }) :=
    fullWitnessInv_nw_congr hlen_p.core_ok.cur_vars_le
      (fullWitnessInv_to_nw hlen_t.core_ok.cur_vars_le hw_t)
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  exact fullWitnessInv_of_nw hnw_p hdm_t hwat_p

private theorem m3_prop_lit_oom_done {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
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
  have hpm_st : Full.FullArenaPermEq s.core st.core := canon_arenaPerm_trans hpm1' hperm_t
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

private theorem m3_prop_lit_ret_true {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st0 st : FullState} {R : Mem 64 → Prop} {Q : Post [.bool]} {ml : Mem 64}
    {ignore_ref : BitVec 64}
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
    (hoom_z : oom0 = 0#64) (hct_eq : ct0 = s.core.confl_type)
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
    Q (true, ()) ml := by
  have hceq_s : st.core = { s.core with
      vals := vals0, flags := flags0, lvl := lvl0, rsns := rsns0, trl := trl0,
      trail_pos := tp0, trail_end := te0, unassigned := un0, unflushed := uf0,
      wvec := wv_t, arena := ar_t, wstk := ws_t, wlen := wl_t, wusable := wu_t,
      confl_type := ct0, confl_ref := cr0, confl_lit0 := c00, confl_lit1 := c10, oom := oom0 } := by
    rw [hceq_t, hceq0]
  have hsc_s : st.scratch = { s.scratch with
      search_ticks := tk0, wsort := wso_t, phases := ph0 } := by
    rw [hsceq_t, hsc0]
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
    canon_trailExt_of_pd ((pd_trailExt_of_canon htr1).congr
      (by rw [hceq_s]) (by rw [hceq_s]) (by rw [hceq_s]))
  have hpm_f : Full.FullArenaPermEq s.core st.core := canon_arenaPerm_trans hpm1' hperm_t
  rw [hst_def] at hlen_t hml
  rw [hceq_s] at hw_t htr_f hpm_f
  exact hQ true vals0 flags0 lvl0 rsns0 trl0 tp0 te0 un0 uf0
    wv_t ar_t ws_t wl_t wu_t ct0 cr0 c00 c10 oom0 tk0 wso_t ph0 ml
    hlen_t hw_t htr_f hpm_f (fun hc => by cases hc) (fun _ => ⟨hoom_z, hct_eq⟩) hml

private theorem m3_prop_lit_swap_done {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {st0 st : FullState} {R : Mem 64 → Prop} {ol r nw : BitVec 32} {bi : BitVec 32}
    {t : BitVec 64} {wv_t ar_t ws_t : List (BitVec 32)} {wl_t : Nat} {wu_t : BitVec 64}
    {wso_t : List (BitVec 32)} {wv' ws' : List (BitVec 32)} {wl' : Nat} {wu' : BitVec 64}
    {wso' : List (BitVec 32)} {i1 i2 : Nat} {v1 v2 : BitVec 32} {m' : Mem 64}
    {J : Cont [i64]} {pok : Bool}
    (hlen_t : st.LengthsOk c) (hw_t : FullWitnessInv c F0 F_cur st.core)
    (hdm_t : st.core.dense_mode = 0#64) (href : r.toNat ∈ fullArenaClauseRefs st)
    (hcr_lt31 : r.toNat < 0x80000000) (hnw_ltv : nw.toNat < 2 * st.core.cur_vars)
    (hbi_ge2 : 2 ≤ bi.toNat) (hbi_csz : bi.toNat < fullArenaClauseSizeCore st.core r.toNat)
    (h1lt_ar : r.toNat + 3 + 1 < st.core.arena.length)
    (hblt_ar : r.toNat + 3 + bi.toNat < st.core.arena.length)
    (hceq_t : st.core = { st0.core with
      wvec := wv_t, arena := ar_t, wstk := ws_t, wlen := wl_t, wusable := wu_t })
    (hsceq_t : st.scratch = { st0.scratch with wsort := wso_t })
    (hperm_t : Full.FullArenaPermEq st0.core st.core)
    (htp1_le : (t + 1#64).toNat ≤ st0.core.trail_end)
    (hlen_p : ({ st with
        core := { st.core with wvec := wv', wstk := ws', wlen := wl', wusable := wu' }
        scratch := { st.scratch with wsort := wso' } } : FullState).LengthsOk c)
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
        st.core.wstk[fullWatchOffCore st.core nw.toNat + k]?)
    (hi1 : i1 = r.toNat + 3 + 1) (hi2 : i2 = r.toNat + 3 + bi.toNat)
    (hv1 : v1 = st.core.arena[r.toNat + 3 + bi.toNat]'hblt_ar)
    (hv2 : v2 = st.core.arena[r.toNat + 3 + 1]'h1lt_ar)
    (hih : (∃ st_s : FullState,
      M3PropLoopInv c F0 F_cur st0 st_s (t + 1#64) ∧ (FullMem c st_s ⋆ R) m') →
      J (t + 1#64, ()) m')
    (hm' : (FullMem c
      { st with
        core :=
          { st.core with
            wvec := wv', wstk := ws', wlen := wl', wusable := wu',
            arena := (st.core.arena.set i1 v1).set i2 v2 }
        scratch := { st.scratch with wsort := wso' } } ⋆ R) m') :
    J (t + 1#64, ()) m' := by
  have hw_p := m3_prop_lit_push_wit hlen_t hw_t hdm_t href hcr_lt31 hnw_ltv hlen_p
    hlay_p hpres_o hpok_t hpok_f
  let st_p : FullState :=
    { st with
      core := { st.core with wvec := wv', wstk := ws', wlen := wl', wusable := wu' }
      scratch := { st.scratch with wsort := wso' } }
  obtain ⟨hlen_s, hw_s, hperm_s⟩ :=
    full_prop_swap_preserves_inv hlen_p.core_ok hw_p hdm_t hperm_t href hbi_ge2 hbi_csz
  subst hi1; subst hi2; subst hv1; subst hv2
  let ar_s := (st_p.core.arena.set (r.toNat + 3 + 1)
      (st_p.core.arena[r.toNat + 3 + bi.toNat]'hblt_ar)).set
    (r.toNat + 3 + bi.toNat) (st_p.core.arena[r.toNat + 3 + 1]'h1lt_ar)
  let st_s : FullState := { st_p with core := { st_p.core with arena := ar_s } }
  exact hih ⟨st_s,
    ⟨⟨hlen_s, hlen_p.scratch_ok⟩, hw_s,
      ⟨wv', ar_s, ws', wl', wu', by dsimp only [st_s, st_p]; rw [hceq_t]⟩,
      ⟨wso', by dsimp only [st_s, st_p]; rw [hsceq_t]⟩,
      hperm_s, htp1_le⟩, hm'⟩

theorem m3_prop_lit_wp (Γ : Env)
    (hRaw : ∀ a m Q X, fullPropLitSpec a m Q X →
      Γ "full_prop_lit_raw" [i64, i32, i64] [.bool] a m Q X)
    (hPush : ∀ a m Q X, fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, fullPropLitSpec a m Q X → Func.wp Γ full_prop_lit_body a m Q X := by
  rintro ⟨h, lit, ignore_ref, ⟨⟩⟩ m0 Q X ⟨c, F0, F_cur, s, R, rfl, hlen0, hw0, hdm0, hoom0, hm0, hQ⟩
  have hmax32 := fullInv_max_vars_lt32 c
  unfold Func.wp full_prop_lit_body
  c0_hsteps
  c0_call hRaw
  refine ⟨c, F0, F_cur, s, R, rfl, hlen0, hw0, hdm0, hoom0, hm0,
    fun ok0 vals0 flags0 lvl0 rsns0 trl0 tp0 te0 un0 uf0 wv0 ar0 ws0 wl0 wu0
      ct0 cr0 c00 c10 oom0 tk0 wso0 ph0 m1 hlen1 hw1 htr1 hpm1 hF1 hT1 hm1 => ?_⟩
  cases ok0 with
  | false =>
    c0_hsteps
    exact hQ false vals0 flags0 lvl0 rsns0 trl0 tp0 te0 un0 uf0 wv0 ar0 ws0 wl0 wu0
      ct0 cr0 c00 c10 oom0 tk0 wso0 ph0 m1 hlen1 hw1 htr1 hpm1 hF1 (fun hc => by cases hc) hm1
  | true =>
    obtain ⟨hoom_z, hct_eq⟩ := hT1 rfl
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
    have hct_0 : st0.core.confl_type = ct0 := by rw [hceq0]
    have hdm1 : st0.core.dense_mode = 0#64 := by rw [hceq0]; exact hdm0
    have hlen1' : st0.LengthsOk c := by rw [hst0_eq]; exact hlen1
    have hw1' : FullWitnessInv c F0 F_cur st0.core := by rw [hceq0]; exact hw1
    have htr1' : Full.FullTrailExt s.core st0.core := by rw [hceq0]; exact htr1
    have hpm1' : Full.FullArenaPermEq s.core st0.core := by rw [hceq0]; exact hpm1
    have hm1' : (FullMem c st0 ⋆ R) m1 := by rw [hst0_eq]; exact hm1
    clear hst0_eq
    have har_cap64 : c.arena_cap < 2 ^ 64 := by
      have := c.harena; unfold dimacsBound at this; omega
    have hte_le0 : s.core.trail_end ≤ s.core.cur_vars := hlen0.core_ok.trail_end_le
    have hcv_le0 : s.core.cur_vars ≤ c.max_vars := hlen0.core_ok.cur_vars_le
    have hte_le1 : te0 ≤ st0.core.cur_vars := by
      rw [← hte_st0]; exact hlen1'.core_ok.trail_end_le
    have hte_ge : s.core.trail_end ≤ te0 := htr1.1
    have hcv_le : st0.core.cur_vars ≤ c.max_vars := hlen1'.core_ok.cur_vars_le
    have hte0_lt64 : te0 < 2 ^ 64 := by omega
    have hte_s_lt64 : s.core.trail_end < 2 ^ 64 := by omega
    have har_len0 : st0.core.arena.length = c.arena_cap := hlen1'.core_ok.arena_len_arr
    have har_le0 : st0.core.arena_len ≤ c.arena_cap := hlen1'.core_ok.arena_len_le
    have htrl_len0 : st0.core.trl.length = c.max_vars := hlen1'.core_ok.trl_len
    have hrsn_len0 : st0.core.rsns.length = c.max_vars := hlen1'.core_ok.rsns_len
    have hlvl_len0 : st0.core.lvl.length = c.max_vars := hlen1'.core_ok.lvl_len
    have hret_st0 : Q (true, ()) m1 :=
      hQ true vals0 flags0 lvl0 rsns0 trl0 tp0 te0 un0 uf0 wv0 ar0 ws0 wl0 wu0
        ct0 cr0 c00 c10 oom0 tk0 wso0 ph0 m1 hlen1 hw1 htr1 hpm1 (fun hc => by cases hc)
        (fun _ => ⟨hoom_z, hct_eq⟩) hm1
    c0_hsteps_nogrp
    all_goals try exact False.elim (Bool.noConfusion (‹true = false›))
    · exact hret_st0
    · exact hret_st0
    · exact hret_st0
    ·
        refine wp_loop_inv (ts := [i64])
          (fun (t, ()) ml => ∃ st : FullState, M3PropLoopInv c F0 F_cur st0 st t ∧
            (FullMem c st ⋆ R) ml)
          (fun (t, ()) _ => st0.core.trail_end - t.toNat) ?_ ?_
        · intro J hJ; c0_hsteps_np
          exact hJ (BitVec.ofNat 64 s.core.trail_end, ()) m1
            ⟨st0, ⟨hlen1', hw1',
              ⟨st0.core.wvec, st0.core.arena, st0.core.wstk, st0.core.wlen, st0.core.wusable,
                rfl⟩,
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
          have hct_t : st.core.confl_type = s.core.confl_type := by
            rw [hceq_t, hct_0]; exact hct_eq
          have hcv64_t : st.core.cur_vars < 2 ^ 64 := by rw [hcv_eq_t, hcv_eq0]; omega
          have h2cv_t : 2 * st.core.cur_vars < 2 ^ 64 := by rw [hcv_eq_t, hcv_eq0]; omega
          have hcv_s : st.core.cur_vars = s.core.cur_vars := hcv_eq_t.trans hcv_eq0
          c0_hsplit
          · have ht_lt : t.toNat < te0 := by
              have h1 : t.toNat < st0.core.trail_end % 2 ^ 64 := by assumption
              rwa [hte_st0, Nat.mod_eq_of_lt hte0_lt64] at h1
            have htp1_nat : (t + 1#64).toNat = t.toNat + 1 :=
              bv64_add1_toNat (by have := hte0_lt64; omega)
            have htp1_le : (t + 1#64).toNat ≤ st0.core.trail_end := by rw [htp1_nat, hte_st0]; omega
            have htrl_lt : t.toNat < st.core.trl.length := by
              rw [hceq_t, htrl_len0]; omega
            let ol : BitVec 32 := st.core.trl[t.toNat]'htrl_lt
            have hcont : J (t + 1#64, ()) ml :=
              ih (t + 1#64, ()) ml (by dsimp only; rw [htp1_nat]; omega)
                ⟨st, ⟨hlen_t, hw_t, ⟨wv_t, ar_t, ws_t, wl_t, wu_t, hceq_t⟩, ⟨wso_t, hsceq_t⟩,
                  hperm_t, htp1_le⟩, hml⟩
            c0_hsplit
            · c0_hsteps_np; exact hcont
            · have hol_lt : ol.toNat < 2 * st.core.cur_vars := by
                have hhc : ¬ 2 * (st0.core.cur_vars % 2 ^ 64) % 2 ^ 64 ≤ ol.toNat := by
                  assumption
                rw [hcv_eq0, ← hcv_s, Nat.mod_eq_of_lt hcv64_t, Nat.mod_eq_of_lt h2cv_t] at hhc
                omega
              have hol_v_lt : ol.toNat / 2 < st.core.cur_vars := by omega
              have hrsn_lt : (ol.setWidth 64 >>> 1#64).toNat < st.core.rsns.length := by
                have hsh : (ol.setWidth 64 >>> 1#64).toNat = ol.toNat / 2 := by
                  have := BitVec.isLt ol
                  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; omega
                rw [hsh, hlen_t.core_ok.rsns_len]; omega
              let r : BitVec 32 := st.core.rsns[(ol.setWidth 64 >>> 1#64).toNat]'hrsn_lt
              c0_hsplit
              · c0_hsteps; exact hcont
              · c0_hsplit
                · c0_hsteps; exact hcont
                · have hr_ne : r ≠ 0xFFFFFFFF#32 := by assumption
                  have hr_lg : (r &&& 0x80000000#32) = 0#32 := by assumption
                  have hrsn_ne : (st.core.rsns[(st.core.trl[t.toNat]?.getD 0#32).toNat / 2]?.getD
                      0xFFFFFFFF#32) ≠ 0xFFFFFFFF#32 := by
                    have hsh : (ol.setWidth 64 >>> 1#64).toNat =
                        (st.core.trl[t.toNat]?.getD 0#32).toNat / 2 := by
                      have := BitVec.isLt ol
                      simp [ol, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
                        List.getElem?_eq_getElem htrl_lt]; omega
                    have hrg : st.core.rsns[(st.core.trl[t.toNat]?.getD 0#32).toNat / 2]?.getD
                        0xFFFFFFFF#32 = r := by
                      rw [← hsh, List.getElem?_eq_getElem hrsn_lt, Option.getD_some]
                    rw [hrg]; exact hr_ne
                  have href_all := hw_t.reason_inv t.toNat (by rw [hte_eq_t]; exact ht_lt) hrsn_ne
                  have hrg' : (st.core.rsns[(st.core.trl[t.toNat]?.getD 0#32).toNat / 2]?.getD
                      0xFFFFFFFF#32) = r := by
                    have hsh : (ol.setWidth 64 >>> 1#64).toNat =
                        (st.core.trl[t.toNat]?.getD 0#32).toNat / 2 := by
                      have := BitVec.isLt ol
                      simp [ol, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
                        List.getElem?_eq_getElem htrl_lt]; omega
                    rw [← hsh, List.getElem?_eq_getElem hrsn_lt, Option.getD_some]
                  rw [hrg'] at href_all
                  have hrb : ¬ ((r &&& 0x80000000#32) ≠ 0#32) := fun h => h hr_lg
                  rw [ite_eq_right hrb] at href_all
                  obtain ⟨href, hng, _⟩ := href_all
                  obtain ⟨hr3, hsz3, hfit, _, _⟩ := hw_t.arena.refs_wf r.toNat href
                  have hr_lt_ar : r.toNat + 3 + fullArenaClauseSizeCore st.core r.toNat ≤
                      st.core.arena.length := by
                    have := hlen_t.core_ok.arena_len_le
                    have := hlen_t.core_ok.arena_len_arr; omega
                  have hi_r : (BitVec.setWidth 64
                      (st.core.trl[t.toNat]'htrl_lt >>> 1#32)).toNat =
                      (ol.setWidth 64 >>> 1#64).toNat := by
                    simp [ol, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
                  have hr_c0_eq : (st.core.rsns[(BitVec.setWidth 64
                      (st.core.trl[t.toNat]'htrl_lt >>> 1#32)).toNat]'(by
                        rw [hi_r]; exact hrsn_lt)) = r :=
                    list_getElem_idx hi_r _ hrsn_lt
                  have hdiv_r : (st.core.trl[t.toNat]'htrl_lt).toNat / 2 =
                      (ol.setWidth 64 >>> 1#64).toNat := by
                    have := BitVec.isLt ol
                    simp [ol, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
                    omega
                  have hr_div_eq :
                      st.core.rsns[(st.core.trl[t.toNat]'htrl_lt).toNat / 2]'(by
                        rw [hdiv_r]; exact hrsn_lt) = r :=
                    list_getElem_idx hdiv_r _ hrsn_lt
                  have hr_lt32 : r.toNat < 2 ^ 32 := BitVec.isLt r
                  have har_r_lt : (BitVec.setWidth 64 (st.core.rsns[(BitVec.setWidth 64
                      (st.core.trl[t.toNat]'htrl_lt >>> 1#32)).toNat]'(by
                        rw [hi_r]; exact hrsn_lt))).toNat < st.core.arena.length := by
                    rw [hr_c0_eq, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]; omega
                  have har_r2_lt : (BitVec.setWidth 64 (st.core.rsns[(BitVec.setWidth 64
                      (st.core.trl[t.toNat]'htrl_lt >>> 1#32)).toNat]'(by
                        rw [hi_r]; exact hrsn_lt)) + 2#64).toNat < st.core.arena.length := by
                    rw [hr_c0_eq, bv32_zext64_add_toNat r (by omega)]; omega
                  have har_r3_lt : (BitVec.setWidth 64 (st.core.rsns[(BitVec.setWidth 64
                      (st.core.trl[t.toNat]'htrl_lt >>> 1#32)).toNat]'(by
                        rw [hi_r]; exact hrsn_lt)) + 3#64).toNat < st.core.arena.length := by
                    rw [hr_c0_eq, bv32_zext64_add_toNat r (by omega)]; omega
                  have har_r4_lt : (BitVec.setWidth 64 (st.core.rsns[(BitVec.setWidth 64
                      (st.core.trl[t.toNat]'htrl_lt >>> 1#32)).toNat]'(by
                        rw [hi_r]; exact hrsn_lt)) + 3#64 + 1#64).toNat <
                      st.core.arena.length := by
                    rw [hr_c0_eq, BitVec.add_assoc, show (3#64 + 1#64 : BitVec 64) = 4#64 by rfl,
                      bv32_zext64_add_toNat r (by omega)]
                    omega
                  c0_hsteps_np
                  all_goals try exact hcont
                  have hidx2 : (r.setWidth 64 + 2#64).toNat = r.toNat + 2 :=
                    bv32_zext64_add_toNat r (by omega)
                  have hj2 : r.toNat + 2 < st.core.arena.length := by omega
                  have hget2 := list_getElem_idx (xs := st.core.arena) hidx2
                    (by rw [hidx2]; exact hj2) hj2
                  have hc_sz : (st.core.arena[(r.setWidth 64 + 2#64).toNat]'(by
                        rw [hidx2]; exact hj2)).toNat =
                      fullArenaClauseSizeCore st.core r.toNat := by
                    simp only [fullArenaClauseSizeCore, List.getElem?_eq_getElem hj2,
                      Option.getD_some]
                    exact congrArg BitVec.toNat hget2
                  have hcb_nat : (r.setWidth 64 + 3#64).toNat = r.toNat + 3 :=
                    bv32_zext64_add_toNat r (by omega)
                  let csz : BitVec 32 := st.core.arena[(r.setWidth 64 + 2#64).toNat]'(by
                    rw [hidx2]; exact hj2)
                  have hcsz_eq : csz.toNat = fullArenaClauseSizeCore st.core r.toNat := hc_sz
                  have hcsz_ge3 : 3 ≤ csz.toNat := by rw [hcsz_eq]; exact hsz3
                  let cb : BitVec 64 := r.setWidth 64 + 3#64
                  have hcb_eq : cb.toNat = r.toNat + 3 := hcb_nat
                  have hcb1_nat : (cb + 1#64).toNat = r.toNat + 3 + 1 := by
                    rw [BitVec.toNat_add, hcb_eq]; simp only [BitVec.toNat_ofNat]
                    exact Nat.mod_eq_of_lt (by omega)
                  have har_cb1_eq : ((st.core.rsns[(st.core.trl[t.toNat]'htrl_lt).toNat / 2]'(by
                        rw [hdiv_r]; exact hrsn_lt)).toNat + BitVec.toNat (3#64) +
                      BitVec.toNat (1#64)) % 2 ^ 64 = (cb + 1#64).toNat := by
                    change ((st.core.rsns[(st.core.trl[t.toNat]'htrl_lt).toNat / 2]'(by
                        rw [hdiv_r]; exact hrsn_lt)).toNat + 3 + 1) % 2 ^ 64 = _
                    rw [hr_div_eq, hcb1_nat]; exact Nat.mod_eq_of_lt (by omega)
                  have hl1_lt_v : (st.core.arena[(cb + 1#64).toNat]'(by
                      rw [hcb1_nat]; omega)).toNat < 2 * st.core.cur_vars := by
                    have hhc : ¬ 2 * (st0.core.cur_vars % 2 ^ 64) % 2 ^ 64 ≤
                        (st.core.arena[((st.core.rsns[(st.core.trl[t.toNat]'htrl_lt).toNat / 2]'(
                            by rw [hdiv_r]; exact hrsn_lt)).toNat + BitVec.toNat (3#64) +
                            BitVec.toNat (1#64)) % 2 ^ 64]'(by
                          rw [har_cb1_eq, hcb1_nat]; omega)).toNat := by
                      assumption
                    rw [list_getElem_idx har_cb1_eq _ (by rw [hcb1_nat]; omega), hcv_eq0, ← hcv_s,
                      Nat.mod_eq_of_lt hcv64_t, Nat.mod_eq_of_lt h2cv_t] at hhc
                    omega
                  let l1 : BitVec 32 := st.core.arena[(cb + 1#64).toNat]'(by rw [hcb1_nat]; omega)
                  have hl1_lvl_lt : (BitVec.setWidth 64 (l1 >>> 1#32)).toNat <
                      st.core.lvl.length := by
                    have : l1.toNat < 2 * st.core.cur_vars := hl1_lt_v
                    rw [hlen_t.core_ok.lvl_len, bv32_rshift1_toNat]; omega
                  c0_hsteps_np
                  refine wp_loop_inv (ts := [i32, i32, i32])
                    (fun (best, bi, k, ()) mk =>
                      1 ≤ bi.toNat ∧ bi.toNat < csz.toNat ∧ 2 ≤ k.toNat ∧ k.toNat ≤ csz.toNat ∧
                      (st.core.arena[r.toNat + 3 + bi.toNat]?.getD 0#32).toNat <
                        2 * st.core.cur_vars ∧ mk = ml)
                    (fun (_best, _bi, k, ()) _ => csz.toNat - k.toNat) ?_ ?_
                  · intro Jin hJin; c0_hsteps_np
                    have hb1_get :
                        (st.core.arena[r.toNat + 3 + (1#32).toNat]?.getD 0#32).toNat <
                        2 * st.core.cur_vars := by
                      have h1n : (1#32 : BitVec 32).toNat = 1 := rfl
                      have h1lt : r.toNat + 3 + 1 < st.core.arena.length := by omega
                      rw [h1n, List.getElem?_eq_getElem h1lt, Option.getD_some,
                        list_getElem_idx (xs := st.core.arena) hcb1_nat.symm h1lt
                          (by rw [hcb1_nat]; omega)]
                      exact hl1_lt_v
                    exact hJin (_, 1#32, 2#32, ()) ml
                      ⟨by decide, by change 1 < csz.toNat; omega, by decide,
                       by change 2 ≤ csz.toNat; omega, hb1_get, rfl⟩
                  · intro Jin (best, bi, k, ⟨⟩) mk
                      ⟨hbi_ge, hbi_lt, hk_ge, hk_le, hbi_ltv, hmk_eq⟩ ih_in
                    subst mk
                    c0_hsplit
                    · have hk_lt : k.toNat < csz.toNat := by assumption
                      have hk_lt32 : k.toNat < 2 ^ 32 := BitVec.isLt k
                      have hk_csz : k.toNat < fullArenaClauseSizeCore st.core r.toNat := by
                        rw [← hcsz_eq]; exact hk_lt
                      have hk_idx : (cb + k.setWidth 64).toNat = r.toNat + 3 + k.toNat := by
                        rw [BitVec.toNat_add, hcb_eq, BitVec.toNat_setWidth,
                          Nat.mod_eq_of_lt (show k.toNat < 2 ^ 64 by omega)]
                        exact Nat.mod_eq_of_lt (by omega)
                      have hcbk_lt : (cb + k.setWidth 64).toNat < st.core.arena.length := by
                        rw [hk_idx]; omega
                      have hkp1 : (k + 1#32).toNat = k.toNat + 1 := bv32_add1_toNat (by omega)
                      let ck : BitVec 32 := st.core.arena[(cb + k.setWidth 64).toNat]'(by
                        rw [hk_idx]; omega)
                      c0_hsteps_nogrp
                      refine wp_join_group (ts := [i32, i32])
                        (fun (best', bi', ()) mb =>
                          1 ≤ bi'.toNat ∧ bi'.toNat < csz.toNat ∧
                          (st.core.arena[r.toNat + 3 + bi'.toNat]?.getD 0#32).toNat <
                            2 * st.core.cur_vars ∧ mb = ml) ?_ ?_
                      · rintro _ ⟨best', bi', ⟨⟩⟩ mb ⟨hbi1', hbi_lt', hbi_v', hmb_eq⟩
                        subst mb
                        c0_hsteps_np
                        exact ih_in (best', bi', k + 1#32, ()) ml
                          (by dsimp only; rw [hkp1]; omega)
                          ⟨hbi1', hbi_lt', by rw [hkp1]; omega, by rw [hkp1]; omega, hbi_v', rfl⟩
                      · intro Jbest hJbest
                        c0_hsplit
                        · have hck_ltv : ck.toNat < 2 * st.core.cur_vars := by
                            have har_cbk_eq :
                                ((st.core.rsns[(st.core.trl[t.toNat]'htrl_lt).toNat / 2]'(by
                                  rw [hdiv_r]; exact hrsn_lt)).toNat + BitVec.toNat (3#64) +
                                  k.toNat) % 2 ^ 64 = (cb + k.setWidth 64).toNat := by
                              change ((st.core.rsns[(st.core.trl[t.toNat]'htrl_lt).toNat / 2]'(by
                                  rw [hdiv_r]; exact hrsn_lt)).toNat + 3 + k.toNat) % 2 ^ 64 = _
                              rw [hr_div_eq, hk_idx]; exact Nat.mod_eq_of_lt (by omega)
                            have hhc :
                                (st.core.arena[((st.core.rsns[
                                    (st.core.trl[t.toNat]'htrl_lt).toNat / 2]'(by
                                      rw [hdiv_r]; exact hrsn_lt)).toNat + BitVec.toNat (3#64) +
                                    k.toNat) % 2 ^ 64]'(by
                                  rw [har_cbk_eq]; exact hcbk_lt)).toNat <
                                2 * (st0.core.cur_vars % 2 ^ 64) % 2 ^ 64 := by
                              assumption
                            rw [list_getElem_idx har_cbk_eq _ hcbk_lt] at hhc
                            change ck.toNat < 2 * (st0.core.cur_vars % 2 ^ 64) % 2 ^ 64 at hhc
                            rw [hcv_eq0, ← hcv_s, Nat.mod_eq_of_lt hcv64_t,
                              Nat.mod_eq_of_lt h2cv_t] at hhc
                            omega
                          have hk_ar : r.toNat + 3 + k.toNat < st.core.arena.length := by omega
                          have hck_get :
                              (st.core.arena[r.toNat + 3 + k.toNat]?.getD 0#32).toNat <
                              2 * st.core.cur_vars := by
                            rw [List.getElem?_eq_getElem hk_ar, Option.getD_some,
                              list_getElem_idx (xs := st.core.arena) hk_idx.symm hk_ar hcbk_lt]
                            exact hck_ltv
                          have hck_lvl_lt : (BitVec.setWidth 64 (ck >>> 1#32)).toNat <
                              st.core.lvl.length := by
                            have : ck.toNat < 2 * st.core.cur_vars := hck_ltv
                            rw [hlen_t.core_ok.lvl_len, bv32_rshift1_toNat]; omega
                          c0_hsteps_np
                          · exact hJbest (_, k, ()) ml ⟨by omega, hk_lt, hck_get, rfl⟩
                          · exact hJbest (best, bi, ()) ml ⟨hbi_ge, hbi_lt, hbi_ltv, rfl⟩
                        · c0_hsteps_np
                          exact hJbest (best, bi, ()) ml ⟨hbi_ge, hbi_lt, hbi_ltv, rfl⟩
                    · c0_hsteps_np
                      · have hbi_ne1 : bi ≠ 1#32 := by assumption
                        have hbi_ge2 : 2 ≤ bi.toNat := by
                          rcases Nat.eq_or_lt_of_le hbi_ge with heq | hgt
                          · exfalso; exact hbi_ne1 (BitVec.eq_of_toNat_eq heq.symm)
                          · exact hgt
                        have hbi_csz : bi.toNat < fullArenaClauseSizeCore st.core r.toNat := by
                          rw [← hcsz_eq]; exact hbi_lt
                        have hbi_lt32 : bi.toNat < 2 ^ 32 := BitVec.isLt bi
                        have hbi_idx : (cb + bi.setWidth 64).toNat = r.toNat + 3 + bi.toNat := by
                          rw [BitVec.toNat_add, hcb_eq, BitVec.toNat_setWidth,
                            Nat.mod_eq_of_lt (show bi.toNat < 2 ^ 64 by omega)]
                          exact Nat.mod_eq_of_lt (by omega)
                        have h1_idx : (cb + 1#64).toNat = r.toNat + 3 + 1 := hcb1_nat
                        let nw : BitVec 32 := st.core.arena[(cb + bi.setWidth 64).toNat]'(by
                          rw [hbi_idx]; omega)
                        have h1lt_ar : r.toNat + 3 + 1 < st.core.arena.length := by omega
                        have hblt_ar : r.toNat + 3 + bi.toNat < st.core.arena.length := by omega
                        have hnw_get : nw = st.core.arena[r.toNat + 3 + bi.toNat]?.getD 0#32 := by
                          rw [List.getElem?_eq_getElem hblt_ar, Option.getD_some]
                          exact list_getElem_idx (xs := st.core.arena) hbi_idx
                            (by rw [hbi_idx]; exact hblt_ar) hblt_ar
                        have hnw_ltv : nw.toNat < 2 * st.core.cur_vars := by
                          rw [hnw_get]; exact hbi_ltv
                        have hcr_lt31 : r.toNat < 0x80000000 := by
                          have hr_and31 : (r &&& 0x80000000#32)[31] = false := by
                            rw [hr_lg]; exact bv32_bit31_zero
                          have h31 : r[31] = false := by
                            rw [BitVec.getElem_and, bv32_bit31_msb, Bool.and_true] at hr_and31
                            exact hr_and31
                          have hr31 : r.toNat.testBit 31 = false := by
                            rw [← BitVec.getElem_eq_testBit_toNat]; exact h31
                          have hr32 : r.toNat < 2 ^ 32 := BitVec.isLt r
                          by_cases hlt31 : r.toNat < 0x80000000
                          · exact hlt31
                          · have hsh1 : r.toNat >>> 31 = 1 := by
                              rw [Nat.shiftRight_eq_div_pow]; omega
                            have htr : r.toNat.testBit 31 = true := by
                              unfold Nat.testBit; rw [hsh1]; rfl
                            cases hr31.symm.trans htr
                        have hcb_bi_lt : (cb + bi.setWidth 64).toNat < st.core.arena.length := by
                          rw [hbi_idx]; omega
                        c0_hsteps_np
                        c0_call hPush
                        refine ⟨c, st, R, rfl, hlen_t, hw_t.watches.layout,
                          fun h => absurd h (by decide),
                          fun _ => ⟨bv32_mask_lit_lt ol, hr_ne⟩, hml,
                          fun pok wv' ws' wl' wu' wso' mp hlen_p hlay_p hpres_o hpok_t hpok_f
                            hmp => ?_⟩
                        cases pok with
                        | false =>
                          c0_hsteps_np
                          have hw_p : FullWitnessInv c F0 F_cur
                              { st.core with
                                wvec := wv', wstk := ws', wlen := wl', wusable := wu' } :=
                            m3_prop_lit_push_wit hlen_t hw_t hdm_t href hcr_lt31 hnw_ltv hlen_p
                              hlay_p (fun l hl hne => hpres_o l hl hne)
                              (fun ht => let h := hpok_t ht
                                ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2 rfl⟩)
                              (fun hf => (hpok_f hf).1 hnw_ltv)
                          exact m3_prop_lit_oom_done hQ hceq0 hsc0 hceq_t hsceq_t hdm_t htr1
                            hpm1' hperm_t hlen_p hw_p ‹_›
                        | true =>
                          let idx_1_r := BitVec.setWidth 64 (st.core.rsns[(BitVec.setWidth 64
                              (st.core.trl[t.toNat]'htrl_lt >>> 1#32)).toNat]'(by
                                rw [hi_r]; exact hrsn_lt)) + 3#64 + 1#64
                          let idx_bi_r := BitVec.setWidth 64 (st.core.rsns[(BitVec.setWidth 64
                              (st.core.trl[t.toNat]'htrl_lt >>> 1#32)).toNat]'(by
                                rw [hi_r]; exact hrsn_lt)) + 3#64 + bi.setWidth 64
                          have har_r_bi_lt : idx_bi_r.toNat < st.core.arena.length := by
                            dsimp only [idx_bi_r]; rw [hr_c0_eq]; exact hcb_bi_lt
                          c0_hsteps_np <;> try (first
                            | exact False.elim (Bool.noConfusion (‹true = false›))
                            | exact False.elim (Bool.noConfusion (‹false = true›)))
                          refine head_wp_store rfl rfl
                            (FullArenaTactics.c0_store_full_arena (i := idx_bi_r) _ ?_ ‹_›)
                            fun m' hm' => ?_
                          · rw [List.length_set]; exact har_r_bi_lt
                          · c0_hsteps_np
                            have hidx1_eq : idx_1_r.toNat = r.toNat + 3 + 1 := by
                              dsimp only [idx_1_r]; rw [hr_c0_eq]; exact h1_idx
                            have hidxbi_eq : idx_bi_r.toNat = r.toNat + 3 + bi.toNat := by
                              dsimp only [idx_bi_r]; rw [hr_c0_eq]; exact hbi_idx
                            have hnw' : st.core.arena[idx_bi_r.toNat]'(by omega) =
                                st.core.arena[r.toNat + 3 + bi.toNat]'hblt_ar :=
                              list_getElem_idx (xs := st.core.arena) hidxbi_eq (by omega) hblt_ar
                            have hl1' : st.core.arena[idx_1_r.toNat]'(by omega) =
                                st.core.arena[r.toNat + 3 + 1]'h1lt_ar :=
                              list_getElem_idx (xs := st.core.arena) hidx1_eq (by omega) h1lt_ar
                            exact m3_prop_lit_swap_done hlen_t hw_t hdm_t href hcr_lt31 hnw_ltv
                              hbi_ge2 hbi_csz h1lt_ar hblt_ar hceq_t hsceq_t hperm_t htp1_le
                              hlen_p hlay_p (fun l hl hne => hpres_o l hl hne)
                              (fun ht => let h := hpok_t ht
                                ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2 rfl⟩)
                              (fun hf => (hpok_f hf).1 hnw_ltv)
                              hidx1_eq hidxbi_eq hnw' hl1'
                              (ih (t + 1#64, ()) m' (by dsimp only; rw [htp1_nat]; omega)) hm'
                      · c0_hsteps_np; exact hcont
          · c0_hsteps_np
            exact m3_prop_lit_ret_true hQ hceq0 hsc0 hceq_t hsceq_t hoom_z hct_eq htr1
              hpm1' hperm_t hlen_t hw_t hml

end PropLitProof

end LeanQbe.T.Examples.Kissat.FullM3VivChrono
