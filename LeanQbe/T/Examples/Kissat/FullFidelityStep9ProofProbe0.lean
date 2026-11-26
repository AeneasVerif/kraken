/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep9
public import LeanQbe.T.Examples.Kissat.FullFidelityBcpProof0
public import LeanQbe.T.Examples.Kissat.FullFidelityStep7Proof1a
public import LeanQbe.T.Examples.Kissat.FullSpec
public import LeanQbe.T.Examples.Kissat.FullM6BcpS15Proof1
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullDenseWatchLemmas
import LeanQbe.T.Examples.Kissat.FullVivTopLemmas1
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Fidelity Step 9 Proofs — Watch Flush & Rebuild (`FullFidelityStep9ProofProbe0`)

M1-clean UNSAT-only parametric `(Γ : Env)` `Func.wp` proofs (`public section`, `0` `@[expose]`
on theorems/lemmas, `0` `import all`, `std3`, `XPost`-polymorphic) for:
1. `fidPropFlushSlowSpec` + `full_prop_flush_slow_fid_step9_wp`: cold realloc fallback split out of
   `full_prop_flush_del_fid` (`S9-P1.1`).
2. `full_prop_flush_del_fid_step9_wp` (`fidPropFlushDelSpec`): register-cached fast flush delegating
   to `full_prop_flush_slow_fid` on cold push.
3. `full_rebuild_watches_nosort_fid_step9_wp` (`Full.fullRebuildWatchesSpec`): sweep+BCP rebuild
   without binary-watch sort (`S9-P0.2`).
4. `full_rebuild_watches_step9_wp` (`Full.fullRebuildWatchesSpec`): calls `nosort` then sorts
   binary watches when `rr == 1ULL`.
-/

set_option autoImplicit false

local elab "p0_steps_np" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { pruneJnz := false } 10000

local macro "p0_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep9

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.C0Step LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM6BcpS15
open LeanQbe.T.Examples.Kissat.FullFidelityBcp
open LeanQbe.T.Examples.Kissat.FullFidelityStep7 (step7SortBinWatchesSpec)
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Full.FullVivTopTactics
open Kraken.Bedrock2.Test

@[local bv_c0] private theorem p0_bv64_0_toNat : (0 : BitVec 64).toNat = 0 := rfl
@[local bv_c0] private theorem p0_bv64_1_toNat : (1 : BitVec 64).toNat = 1 := rfl
@[local bv_c0] private theorem p0_bv64_2_toNat : (2 : BitVec 64).toNat = 2 := rfl

local macro "p0_hsplit" : tactic =>
  `(tactic| (c0_hsplit; all_goals try simp only [bv_c0, Nat.reduceMod] at hc))

/-! ## 1. `fidPropFlushSlowSpec` & `full_prop_flush_slow_fid_step9_wp` -/

/-- Specification for cold delayed-watch flush helper `full_prop_flush_slow_fid(h, j, di)`:
assumes `j = 3 * idx` with `idx < dlen` (`di = 3 * dlen`), executes at least one `full_watch_push`
and loops `j < di` while reading `h->wlen`/`h->wusable` from memory, preserving `WatchesInv`
and `SplitWatchesInv` with `off'` rebase. -/
@[expose] def fidPropFlushSlowSpec : Spec [i64, i64, i64] [.bool] :=
  fun (h, j, di, ()) m Q _ =>
    ∃ (c : FullCfg) (F_cur : List (List Nat)) (st : FullState) (R : Mem 64 → Prop)
      (idx dlen skip_lit : Nat),
      h = c.hdr ∧ st.LengthsOk c ∧ WatchStackLayout st.core ∧
      j.toNat = 3 * idx ∧ di.toNat = 3 * dlen ∧ idx < dlen ∧ dlen ≤ c.delayed_cap ∧
      DelayedWatchesOk st.core st.scratch.delayed dlen skip_lit ∧
      (FullMem c st ⋆ R) m ∧
      ∀ (ok : Bool) wvec' wstk' wlen' wu' wsort' m',
        let st' : FullState :=
          { st with
            core := { st.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' }
            scratch := { st.scratch with wsort := wsort' } }
        st'.LengthsOk c → WatchStackLayout st'.core →
        (WatchesInv F_cur st.core → WatchesInv F_cur st'.core) →
        (skip_lit < 2 * st.core.cur_vars →
          ∀ off q p end_v, SplitWatchesInv F_cur st.core skip_lit off q p end_v →
            let off' := fullWatchOffCore st'.core skip_lit
            SplitWatchesInv F_cur st'.core skip_lit off'
              (off' + (q - off)) (off' + (p - off)) (off' + (end_v - off))) →
        (FullMem c st' ⋆ R) m' → Q (ok, ()) m'

theorem fidPropFlushSlowSpec_monoX {xs : Tup Val [i64, i64, i64]} {m : Mem 64}
    {Q : Post [.bool]} {X X' : XPost} (h : fidPropFlushSlowSpec xs m Q X) :
    fidPropFlushSlowSpec xs m Q X' := h

theorem fidPropFlushSlowSpec_noExit :
    ∀ xs m Q X, fidPropFlushSlowSpec xs m Q X →
      fidPropFlushSlowSpec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => fidPropFlushSlowSpec_monoX h

section Probe0Helpers

private theorem p0_bv64_ofNat {n : Nat} (hn : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

private def p0FlushDisk (wl_d : Nat) (wu_d : BitVec 64) (st : FullState) : FullState :=
  { st with core := { st.core with wlen := wl_d, wusable := wu_d } }

private theorem p0_repl_empty_layout {c : FullCfg} {k : FullCoreState}
    (hlay : WatchStackLayout k) (hlen : k.LengthsOk c) {lit w0 cref : BitVec 32}
    (hlit : lit.toNat < 2 * k.cur_vars) (hw_pos : 1 ≤ k.wlen)
    (hrsz0 : fullWatchSizeCore k lit.toNat = 0) (hfit2 : k.wlen + 2 ≤ c.wcap)
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
  have hwend_32 : wend < 2 ^ 32 := by dsimp [wend]; omega
  have h2l_lt : 2 * lit.toNat < k.wvec.length := by rw [hwv]; omega
  have h2l1_lt : 2 * lit.toNat + 1 < k.wvec.length := by rw [hwv]; omega
  have hw0_lt : wend < k.wstk.length := by rw [hws]; exact Nat.lt_of_lt_of_le (by omega) hfit2
  have hw1_lt : wend + 1 < k.wstk.length := by rw [hws]; exact Nat.lt_of_lt_of_le (by omega) hfit2
  have hwstk_ne : ∀ idx < k.wlen, k'.wstk[idx]? = k.wstk[idx]? := fun idx hidx => by
    dsimp [k', wend]; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
  have hoff_ne : ∀ l, l ≠ lit.toNat → fullWatchOffCore k' l = fullWatchOffCore k l :=
    fun l hne => by
    unfold fullWatchOffCore; dsimp [k']
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
  have hoff_lit : fullWatchOffCore k' lit.toNat = wend := by
    unfold fullWatchOffCore; dsimp [k']
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_self h2l_lt, Option.getD_some,
      bv32_ofNat_toNat hwend_32]
  have hsz_ne : ∀ l, l ≠ lit.toNat → fullWatchSizeCore k' l = fullWatchSizeCore k l :=
    fun l hne => by
    unfold fullWatchSizeCore; dsimp [k']
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
  have hsz_lit : fullWatchSizeCore k' lit.toNat = 2 := by
    unfold fullWatchSizeCore; dsimp [k']; rw [List.getElem?_set_self (by simp; omega)]; rfl
  have hlen' : k'.LengthsOk c :=
    { hlen with wvec_len := by dsimp [k']; simp [hwv], wstk_len_arr := by dsimp [k']; simp [hws]
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
        rw [hsz_ne l2 hl2] at hp2 ⊢; rw [hoff_lit, hoff_ne l2 hl2]
        exact Or.inr (hlay.bounds l2 h2)
      · by_cases hl2 : l2 = lit.toNat
        · subst hl2; rw [hsz_ne l1 hl1] at hp1 ⊢; rw [hoff_ne l1 hl1, hoff_lit]
          exact Or.inl (hlay.bounds l1 h1)
        · rw [hsz_ne l1 hl1] at hp1 ⊢; rw [hsz_ne l2 hl2] at hp2 ⊢
          rw [hoff_ne l1 hl1, hoff_ne l2 hl2]; exact hlay.disjoint l1 l2 h1 h2 hne hp1 hp2
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

end Probe0Helpers

private theorem p0_fullWatchOff_congr_idx {l : List (BitVec 32)} {i j : Nat}
    (hij : i = j) (hi : i < l.length) : l[j]'(hij ▸ hi) = l[i]'hi := by
  subst hij; rfl

private theorem p0_slow_case1_fin {c : FullCfg} {F_cur : List (List Nat)}
    {st0 st : FullState} {R : Mem 64 → Prop} {skip_lit : Nat}
    {rw_v ow_v cr_v : BitVec 32} {wu_n : BitVec 64} {mn : Mem 64}
    {sz0 wend0 : Nat}
    (hsz0 : sz0 = fullWatchSizeCore st.core rw_v.toNat)
    (hwend0 : wend0 = fullWatchOffCore st.core rw_v.toNat + sz0)
    (hlay : WatchStackLayout st.core) (hlen : st.LengthsOk c)
    (hrw_lt : rw_v.toNat < 2 * st.core.cur_vars)
    (hoff_pos : 0 < fullWatchOffCore st.core rw_v.toNat)
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
          (off' + (q - off)) (off' + (p - off)) (off' + (end_v - off)))
    (hmn : (FullMem c
      { st with
          core :=
            { st.core with
                wstk := (st.core.wstk.set wend0 ow_v).set (wend0 + 1) cr_v
                wvec := st.core.wvec.set (2 * rw_v.toNat + 1) (BitVec.ofNat 32 (sz0 + 2))
                wusable := wu_n } } ⋆ R) mn) :
    ∃ (st_n : FullState), c.pWstk = c.pWstk ∧
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
            (off' + (q - off)) (off' + (p - off)) (off' + (end_v - off))) ∧
      (FullMem c st_n ⋆ R) mn := by
  subst hsz0 hwend0
  obtain ⟨hlen_k, hlay_k, _, hpres_o, hsz_k, hpre_k, hw0_k, hw1_k⟩ :=
    s15_append_sentinel_layout hlay hlen.core_ok (wu' := wu_n) hrw_lt hoff_pos
      hend2_le hsent0 hsent1 how_f hcr_lt_st
  let st_n : FullState :=
    { st with core := { st.core with
        wstk := (st.core.wstk.set (fullWatchOffCore st.core rw_v.toNat +
          fullWatchSizeCore st.core rw_v.toNat) ow_v).set
          (fullWatchOffCore st.core rw_v.toNat + fullWatchSizeCore st.core rw_v.toNat + 1) cr_v
        wvec := st.core.wvec.set (2 * rw_v.toNat + 1)
          (BitVec.ofNat 32 (fullWatchSizeCore st.core rw_v.toNat + 2))
        wusable := wu_n } }
  have hstep := s15_flush_step_preserves (F_cur := F_cur) (k := st.core)
    (k' := st_n.core) (lit := rw_v) (w0 := ow_v) (cref := cr_v)
    (skip_lit := skip_lit) rfl rfl hlay_k hrw_lt how_f hcr_lt_st hcr_ref_st
    hpres_o ⟨hsz_k, hpre_k, hw0_k, hw1_k⟩
  refine ⟨st_n, rfl, by dsimp [st_n]; rw [hcore_eq], hsc_eq,
    ⟨hlen_k, hlen.scratch_ok⟩, hlay_k, fun hw0 => hstep.1 (hwat_pres hw0), ?_, hmn⟩
  intro hsk off q p end_v hsw0
  have hsw1 := hsw_pres hsk off q p end_v hsw0
  have hsw2 := hstep.2 hrw_ne (hcv_eq ▸ hsk)
    (fullWatchOffCore st.core skip_lit)
    (fullWatchOffCore st.core skip_lit + (q - off))
    (fullWatchOffCore st.core skip_lit + (p - off))
    (fullWatchOffCore st.core skip_lit + (end_v - off)) hsw1
  simpa only [Nat.add_sub_cancel_left] using hsw2

private theorem p0_slow_case2a_fin {c : FullCfg} {F_cur : List (List Nat)}
    {st0 st : FullState} {R : Mem 64 → Prop} {skip_lit : Nat}
    {rw_v ow_v cr_v : BitVec 32} {m : Mem 64}
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
          (off' + (q - off)) (off' + (p - off)) (off' + (end_v - off)))
    (hm : (FullMem c
      { st with
          core :=
            { st.core with
                wstk := (st.core.wstk.set st.core.wlen ow_v).set (st.core.wlen + 1) cr_v
                wvec := (st.core.wvec.set (2 * rw_v.toNat)
                  (BitVec.ofNat 32 st.core.wlen)).set (2 * rw_v.toNat + 1) 2#32
                wlen := st.core.wlen + 2 } } ⋆ R) m) :
    ∃ (st_n : FullState), c.pWstk = c.pWstk ∧
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
            (off' + (q - off)) (off' + (p - off)) (off' + (end_v - off))) ∧
      (FullMem c st_n ⋆ R) m := by
  obtain ⟨hlen_k, hlay_k, _, hpres_o, hsz_k, hpre_k, hw0_k, hw1_k⟩ :=
    p0_repl_empty_layout hlay hlen.core_ok hrw_lt hw_pos hrsz0 hfit2 how_f hcr_lt_st
  let st_n : FullState :=
    { st with
        core :=
          { st.core with
              wstk := (st.core.wstk.set st.core.wlen ow_v).set (st.core.wlen + 1) cr_v
              wvec := (st.core.wvec.set (2 * rw_v.toNat)
                (BitVec.ofNat 32 st.core.wlen)).set (2 * rw_v.toNat + 1) 2#32
              wlen := st.core.wlen + 2 } }
  have hstep := s15_flush_step_preserves (F_cur := F_cur) (k := st.core) (k' := st_n.core)
    (lit := rw_v) (w0 := ow_v) (cref := cr_v) (skip_lit := skip_lit) rfl rfl hlay_k hrw_lt how_f
    hcr_lt_st hcr_ref_st hpres_o ⟨hsz_k, hpre_k, hw0_k, hw1_k⟩
  refine ⟨st_n, rfl, by dsimp [st_n]; rw [hcore_eq], hsc_eq,
    ⟨hlen_k, hlen.scratch_ok⟩, hlay_k, fun hw0 => hstep.1 (hwat_pres hw0), ?_, hm⟩
  intro hsk off q p end_v hsw0
  have hsw1 := hsw_pres hsk off q p end_v hsw0
  have hsw2 := hstep.2 hrw_ne (hcv_eq ▸ hsk)
    (fullWatchOffCore st.core skip_lit)
    (fullWatchOffCore st.core skip_lit + (q - off))
    (fullWatchOffCore st.core skip_lit + (p - off))
    (fullWatchOffCore st.core skip_lit + (end_v - off)) hsw1
  simpa only [Nat.add_sub_cancel_left] using hsw2

private theorem p0_slow_case2b_fin {c : FullCfg} {F_cur : List (List Nat)}
    {st0 st : FullState} {R : Mem 64 → Prop} {skip_lit : Nat}
    {rw_v ow_v cr_v : BitVec 32} {m : Mem 64} {sz0 : Nat}
    (hsz0 : sz0 = fullWatchSizeCore st.core rw_v.toNat)
    (hlay : WatchStackLayout st.core) (hlen : st.LengthsOk c)
    (hrw_lt : rw_v.toNat < 2 * st.core.cur_vars)
    (hoff_pos : 0 < fullWatchOffCore st.core rw_v.toNat)
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
          (off' + (q - off)) (off' + (p - off)) (off' + (end_v - off)))
    (hm : (FullMem c
      { st with
          core :=
            { st.core with
                wstk := (st.core.wstk.set st.core.wlen ow_v).set (st.core.wlen + 1) cr_v
                wvec := st.core.wvec.set (2 * rw_v.toNat + 1) (BitVec.ofNat 32 (sz0 + 2))
                wlen := st.core.wlen + 2 } } ⋆ R) m) :
    ∃ (st_n : FullState), c.pWstk = c.pWstk ∧
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
            (off' + (q - off)) (off' + (p - off)) (off' + (end_v - off))) ∧
      (FullMem c st_n ⋆ R) m := by
  subst hsz0
  obtain ⟨hlen_k, hlay_k, _, hpres_o, hsz_k, hpre_k, hw0_k, hw1_k⟩ :=
    s15_append_end_layout hlay hlen.core_ok hrw_lt hoff_pos hend_wlen hfit2 how_f hcr_lt_st
  let st_n : FullState :=
    { st with
        core :=
          { st.core with
              wstk := (st.core.wstk.set st.core.wlen ow_v).set (st.core.wlen + 1) cr_v
              wvec := st.core.wvec.set (2 * rw_v.toNat + 1)
                (BitVec.ofNat 32 (fullWatchSizeCore st.core rw_v.toNat + 2))
              wlen := st.core.wlen + 2 } }
  have hstep := s15_flush_step_preserves (F_cur := F_cur) (k := st.core) (k' := st_n.core)
    (lit := rw_v) (w0 := ow_v) (cref := cr_v) (skip_lit := skip_lit) rfl rfl
    (by simpa [st_n, hend_wlen] using hlay_k) hrw_lt how_f hcr_lt_st hcr_ref_st
    (by simpa [st_n, hend_wlen] using hpres_o)
    ⟨by simpa [st_n, hend_wlen] using hsz_k, by simpa [st_n, hend_wlen] using hpre_k,
     by simpa [st_n, hend_wlen] using hw0_k, by simpa [st_n, hend_wlen] using hw1_k⟩
  refine ⟨st_n, rfl, by dsimp [st_n]; rw [hcore_eq], hsc_eq,
    ⟨by simpa [st_n, hend_wlen] using hlen_k, hlen.scratch_ok⟩,
    by simpa [st_n, hend_wlen] using hlay_k, fun hw0 => hstep.1 (hwat_pres hw0), ?_, hm⟩
  intro hsk off q p end_v hsw0
  have hsw1 := hsw_pres hsk off q p end_v hsw0
  have hsw2 := hstep.2 hrw_ne (hcv_eq ▸ hsk)
    (fullWatchOffCore st.core skip_lit)
    (fullWatchOffCore st.core skip_lit + (q - off))
    (fullWatchOffCore st.core skip_lit + (p - off))
    (fullWatchOffCore st.core skip_lit + (end_v - off)) hsw1
  simpa only [Nat.add_sub_cancel_left] using hsw2

theorem full_prop_flush_slow_fid_step9_wp (Γ : Env)
    (hPush : ∀ a m Q X, Full.fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, fidPropFlushSlowSpec a m Q X → Func.wp Γ fidStep9PropFlushSlowFn.body a m Q X := by
  rintro ⟨h, j0, di, ⟨⟩⟩ m0 Q X
    ⟨c, F_cur, st0, R, idx0, dlen, skip_lit, rfl, hlen0, hlay0, hj0_eq, hdi_eq, hidx0_lt,
     hdlen_le, hdel0, hm0, hQ⟩
  have hdelc : c.delayed_cap < dimacsBound := c.hdel
  have hwc : c.wcap < 2 * dimacsBound := c.hwcap
  have hmaxv : c.max_vars < 2 * dimacsBound := c.hmaxv
  unfold dimacsBound at hdelc hwc hmaxv
  have hdel_len0 := hlen0.scratch_ok.delayed_len_arr
  have h3i0_lt : 3 * idx0 + 2 < st0.scratch.delayed.length := by omega
  have hj0_1 : (j0 + 1#64).toNat = 3 * idx0 + 1 := by
    rw [BitVec.toNat_add, hj0_eq]; change (3 * idx0 + 1) % 2 ^ 64 = 3 * idx0 + 1
    exact Nat.mod_eq_of_lt (by omega)
  have hj0_2 : (j0 + 2#64).toNat = 3 * idx0 + 2 := by
    rw [BitVec.toNat_add, hj0_eq]; change (3 * idx0 + 2) % 2 ^ 64 = 3 * idx0 + 2
    exact Nat.mod_eq_of_lt (by omega)
  have hj0_3 : (j0 + 3#64).toNat = 3 * (idx0 + 1) := by
    rw [BitVec.toNat_add, hj0_eq]; change (3 * idx0 + 3) % 2 ^ 64 = 3 * (idx0 + 1)
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  obtain ⟨hrlit0_lt, hrlit0_ne, hrw00_f, hrcr0_lt, hrcr0_ref⟩ := hdel0 idx0 hidx0_lt
  have hrlit0_get : st0.scratch.delayed[j0.toNat]'(by omega) =
      st0.scratch.delayed[3 * idx0]?.getD 0#32 := by
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; simp only [hj0_eq]
  have hrw00_get : st0.scratch.delayed[(j0 + 1#64).toNat]'(by rw [hj0_1]; omega) =
      st0.scratch.delayed[3 * idx0 + 1]?.getD 0#32 := by
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; simp only [hj0_1]
  have hrcr0_get : st0.scratch.delayed[(j0 + 2#64).toNat]'(by rw [hj0_2]; omega) =
      st0.scratch.delayed[3 * idx0 + 2]?.getD 0#32 := by
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; simp only [hj0_2]
  let rw0 := st0.scratch.delayed[j0.toNat]'(by omega)
  let ow0 := st0.scratch.delayed[(j0 + 1#64).toNat]'(by rw [hj0_1]; omega)
  let cr0 := st0.scratch.delayed[(j0 + 2#64).toNat]'(by rw [hj0_2]; omega)
  have how0_f : (ow0 &&& 0x80000000#32) = 0#32 := by dsimp only [ow0]; rw [hrw00_get]; exact hrw00_f
  have hcr0_lt : cr0.toNat < 0x80000000 := by dsimp only [cr0]; rw [hrcr0_get]; exact hrcr0_lt
  have how0_ne : ow0 ≠ 0xFFFFFFFF#32 := fun h => by
    rw [h] at how0_f; exact absurd how0_f (by decide)
  have hcr0_ne : cr0 ≠ 0xFFFFFFFF#32 := fun h => by
    rw [h] at hcr0_lt; revert hcr0_lt; decide
  unfold Func.wp fidStep9PropFlushSlowFn; dsimp only; unfold full_prop_flush_slow_fid_body
  c0_hsteps_nogrp
  refine LeanQbe.T.wp_call_of_spec _ _ (hPush _ _ _ _ ?_)
  refine ⟨c, st0, R, rfl, hlen0, hlay0, fun h => absurd h (by decide),
    fun _ => ⟨how0_ne, hcr0_ne⟩, hm0,
    fun pok0 wvec1 wstk1 wlen1 wu1 wsort1 mp0 hlen1 hlay1 hpres_o0 hpok0_t hpok0_f hmp0 => ?_⟩
  let st1 : FullState :=
    { st0 with
      core := { st0.core with wvec := wvec1, wstk := wstk1, wlen := wlen1, wusable := wu1 }
      scratch := { st0.scratch with wsort := wsort1 } }
  unfold fullWatchSize fullWatchOff at hpres_o0 hpok0_t hpok0_f
  c0_hsteps_nogrp
  · have hpok0_eq : pok0 = true := by assumption
    have ⟨_, _, hsz1, hpre1, hw0_1, hw1_1⟩ := hpok0_t hpok0_eq
    have hstep0 := s15_flush_step_preserves (F_cur := F_cur) (k := st0.core) (k' := st1.core)
      (lit := rw0) (w0 := ow0) (cref := cr0) (skip_lit := skip_lit) rfl rfl hlay1
      (by dsimp only [rw0]; rw [hrlit0_get]; exact hrlit0_lt) how0_f hcr0_lt
      (by dsimp only [cr0]; rw [hrcr0_get]; exact hrcr0_ref) hpres_o0
      ⟨hsz1, hpre1, hw0_1, hw1_1 rfl⟩
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
      exact hstep0.2 (by dsimp only [rw0]; rw [hrlit0_get]; exact hrlit0_ne) hsk off q p end_v hsw0
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
        have hrlit_get : st.scratch.delayed[j_v.toNat]'(by omega) =
            st0.scratch.delayed[3 * idx]?.getD 0#32 := by
          rw [← hdel_eq, List.getElem?_eq_getElem (by omega), Option.getD_some]; simp only [hj_eq]
        have hrw0_get : st.scratch.delayed[(j_v + 1#64).toNat]'(by rw [hj1_nat]; omega) =
            st0.scratch.delayed[3 * idx + 1]?.getD 0#32 := by
          rw [← hdel_eq, List.getElem?_eq_getElem (by omega), Option.getD_some]; simp only [hj1_nat]
        have hrcr_get : st.scratch.delayed[(j_v + 2#64).toNat]'(by rw [hj2_nat]; omega) =
            st0.scratch.delayed[3 * idx + 2]?.getD 0#32 := by
          rw [← hdel_eq, List.getElem?_eq_getElem (by omega), Option.getD_some]; simp only [hj2_nat]
        let rw_v := st.scratch.delayed[j_v.toNat]'(by omega)
        let ow_v := st.scratch.delayed[(j_v + 1#64).toNat]'(by rw [hj1_nat]; omega)
        let cr_v := st.scratch.delayed[(j_v + 2#64).toNat]'(by rw [hj2_nat]; omega)
        have hrw_lt : rw_v.toNat < 2 * st.core.cur_vars := by
          dsimp only [rw_v]; rw [hrlit_get, hcv_eq]; exact hrlit_lt
        have hrw_ne : rw_v.toNat ≠ skip_lit := by
          dsimp only [rw_v]; rw [hrlit_get]; exact hrlit_ne
        have how_f : (ow_v &&& 0x80000000#32) = 0#32 := by
          dsimp only [ow_v]; rw [hrw0_get]; exact hrw0_f
        have hcr_lt_st : cr_v.toNat < 0x80000000 := by
          dsimp only [cr_v]; rw [hrcr_get]; exact hrcr_lt
        have hcr_ref_st : cr_v.toNat ∈ fullArenaClauseRefsCore st.core := by
          dsimp only [cr_v]; rw [hrcr_get, href_eq]; exact hrcr_ref
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
        have hwv_i0 : (rw_v.setWidth 64 <<< (1 : Nat)).toNat < st.core.wvec.length := by
          rw [hwv_len, hrw64_nat]; omega
        have hwv_i1 : ((rw_v.setWidth 64 <<< (1 : Nat)) + 1#64).toNat < st.core.wvec.length := by
          rw [hwv_len, hrw64p1_nat]; omega
        let roff_w := st.core.wvec[(rw_v.setWidth 64 <<< (1 : Nat)).toNat]'hwv_i0
        let rsz_w := st.core.wvec[((rw_v.setWidth 64 <<< (1 : Nat)) + 1#64).toNat]'hwv_i1
        have hroff_eq : (roff_w.setWidth 64).toNat = fullWatchOffCore st.core rw_v.toNat := by
          rw [zext_toNat _ (by decide)]; unfold fullWatchOffCore
          rw [List.getElem?_eq_getElem (by rw [hwv_len]; omega), Option.getD_some]
          exact congrArg BitVec.toNat (by simp [roff_w, hrw64_nat])
        have hrsz_eq : (rsz_w.setWidth 64).toNat = fullWatchSizeCore st.core rw_v.toNat := by
          rw [zext_toNat _ (by decide)]; unfold fullWatchSizeCore
          rw [List.getElem?_eq_getElem (by rw [hwv_len]; omega), Option.getD_some]
          exact congrArg BitVec.toNat (by simp [rsz_w, hrw64p1_nat])
        have hbd_rw := hlay.bounds rw_v.toNat hrw_lt
        have hrend_nat : (roff_w.setWidth 64 + rsz_w.setWidth 64).toNat =
            fullWatchOffCore st.core rw_v.toNat + fullWatchSizeCore st.core rw_v.toNat := by
          rw [BitVec.toNat_add, hroff_eq, hrsz_eq, Nat.mod_eq_of_lt (by omega)]
        have hrend1_nat : (roff_w.setWidth 64 + rsz_w.setWidth 64 + 1#64).toNat =
            fullWatchOffCore st.core rw_v.toNat + fullWatchSizeCore st.core rw_v.toNat + 1 := by
          rw [BitVec.toNat_add, hrend_nat]; change (_ + 1) % 2 ^ 64 = _
          exact Nat.mod_eq_of_lt (by omega)
        have hrend2_nat : (roff_w.setWidth 64 + rsz_w.setWidth 64 + 2#64).toNat =
            fullWatchOffCore st.core rw_v.toNat + fullWatchSizeCore st.core rw_v.toNat + 2 := by
          rw [BitVec.toNat_add, hrend_nat]; change (_ + 2) % 2 ^ 64 = _
          exact Nat.mod_eq_of_lt (by omega)
        have hwl_nat : (BitVec.ofNat 64 st.core.wlen).toNat = st.core.wlen :=
          p0_bv64_ofNat (by omega)
        have hwl1_nat : (BitVec.ofNat 64 st.core.wlen + 1#64).toNat = st.core.wlen + 1 := by
          rw [BitVec.toNat_add, hwl_nat]; change (_ + 1) % 2 ^ 64 = _
          exact Nat.mod_eq_of_lt (by omega)
        have hwl2_nat : (BitVec.ofNat 64 st.core.wlen + 2#64).toNat = st.core.wlen + 2 := by
          rw [BitVec.toNat_add, hwl_nat]; change (_ + 2) % 2 ^ 64 = _
          exact Nat.mod_eq_of_lt (by omega)
        have hwc_nat : (BitVec.ofNat 64 c.wcap).toNat = c.wcap := p0_bv64_ofNat (by omega)
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
        have hrv_w0 : st.core.wvec[
            2 * st.scratch.delayed[j_v.toNat].toNat % 2 ^ 64]'(by
              change 2 * rw_v.toNat % 2 ^ 64 < st.core.wvec.length
              rw [hwv_len, Nat.mod_eq_of_lt (by omega : 2 * rw_v.toNat < 2 ^ 64)]; omega) =
            roff_w := by
          dsimp only [roff_w]; congr 1
        have hrv_w1 : st.core.wvec[
            (2 * st.scratch.delayed[j_v.toNat].toNat + 1) % 2 ^ 64]'(by
              change (2 * rw_v.toNat + 1) % 2 ^ 64 < st.core.wvec.length
              rw [hwv_len, Nat.mod_eq_of_lt (by omega : 2 * rw_v.toNat + 1 < 2 ^ 64)]; omega) =
            rsz_w := by
          dsimp only [rsz_w]; congr 1
          change (2 * rw_v.toNat + 1) % 2 ^ 64 = (rw_v.setWidth 64 <<< (1 : Nat) + 1#64).toNat
          rw [hrw64p1_nat, Nat.mod_eq_of_lt (by omega : 2 * rw_v.toNat + 1 < 2 ^ 64)]
        have hroff_t : roff_w.toNat = fullWatchOffCore st.core rw_v.toNat := by
          rw [← hroff_eq, zext_toNat _ (by decide)]
        have hrsz_t : rsz_w.toNat = fullWatchSizeCore st.core rw_v.toNat := by
          rw [← hrsz_eq, zext_toNat _ (by decide)]
        have hmod_2rw : 2 * st.scratch.delayed[j_v.toNat].toNat % 2 ^ 64 = 2 * rw_v.toNat :=
          Nat.mod_eq_of_lt (by omega)
        have hmod_2rw1 : (2 * st.scratch.delayed[j_v.toNat].toNat + 1) % 2 ^ 64 =
            2 * rw_v.toNat + 1 := Nat.mod_eq_of_lt (by omega)
        have hmod_2rw_rv : 2 * rw_v.toNat % 2 ^ 64 = 2 * rw_v.toNat := Nat.mod_eq_of_lt (by omega)
        have hmod_2rw1_rv : (2 * rw_v.toNat + 1) % 2 ^ 64 = 2 * rw_v.toNat + 1 :=
          Nat.mod_eq_of_lt (by omega)
        have hrv_w0_raw : st.core.wvec[2 * rw_v.toNat]'(by rw [hwv_len]; omega) = roff_w := by
          simpa only [hmod_2rw] using hrv_w0
        have hrv_w1_raw : st.core.wvec[2 * rw_v.toNat + 1]'(by rw [hwv_len]; omega) = rsz_w := by
          simpa only [hmod_2rw1] using hrv_w1
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
                    try dsimp only [Blocks.get_here, Blocks.get_there]
                    exact h) ?_
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
                    let st_p : FullState :=
                      { st with
                        core := { st.core with wvec := wvec', wstk := wstk',
                                               wlen := wlen', wusable := wu' }
                        scratch := { st.scratch with wsort := wsort' } }
                    have hcore_p : st_p.core = { st0.core with
                        wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' } := by
                      dsimp only [st_p]; rw [hcore_eq]
                    have hsc_p : st_p.scratch = { st0.scratch with wsort := wsort' } := by
                      dsimp only [st_p]; rw [hsc_eq]
                    have hst_p_eq : st_p =
                        { st0 with
                          core := { st0.core with wvec := wvec', wstk := wstk',
                                                  wlen := wlen', wusable := wu' }
                          scratch := { st0.scratch with wsort := wsort' } } := by
                      cases h1 : st_p; rw [h1] at hcore_p hsc_p; dsimp only at hcore_p hsc_p
                      rw [hcore_p, hsc_p]
                    unfold fullWatchSize fullWatchOff at hpres_o hpok_t hpok_f
                    c0_hsteps_nogrp
                    · have hpok_eq : pok = true := by assumption
                      have ⟨_, _, hsz_p, hpre_p, hw0_p, hw1_p⟩ := hpok_t hpok_eq
                      have hstep := s15_flush_step_preserves (F_cur := F_cur) (k := st.core)
                        (k' := st_p.core) (lit := rw_v) (w0 := ow_v) (cref := cr_v)
                        (skip_lit := skip_lit) rfl rfl hlay_p hrw_lt how_f hcr_lt_st hcr_ref_st
                        hpres_o ⟨hsz_p, hpre_p, hw0_p, hw1_p rfl⟩
                      refine hJnext (c.pWstk, ()) mp
                        ⟨st_p, rfl, hcore_p, hsc_p, hlen_p, hlay_p,
                         fun hw0 => hstep.1 (hwat_pres hw0), ?_, hmp⟩
                      intro hsk off q p end_v hsw0
                      have hsw1 := hsw_pres hsk off q p end_v hsw0
                      have hsw2 := hstep.2 hrw_ne (hcv_eq ▸ hsk)
                        (fullWatchOffCore st.core skip_lit)
                        (fullWatchOffCore st.core skip_lit + (q - off))
                        (fullWatchOffCore st.core skip_lit + (p - off))
                        (fullWatchOffCore st.core skip_lit + (end_v - off)) hsw1
                      simpa [Nat.add_sub_cancel_left] using hsw2
                    · have hpok_eq : pok = false := by
                        cases pok
                        · rfl
                        · cases (by assumption : true = false)
                      have hstep := s15_flush_step_false_preserves (F_cur := F_cur)
                        (k := st.core) (k' := st_p.core) (lit := rw_v) (skip_lit := skip_lit)
                        rfl rfl hlay_p hpres_o (hpok_f hpok_eq).1
                      refine hQ false wvec' wstk' wlen' wu' wsort' mp
                        (hst_p_eq ▸ hlen_p) (hcore_p ▸ hlay_p)
                        (fun hw0 => hcore_p ▸ hstep.1 (hwat_pres hw0)) ?_ (hst_p_eq ▸ hmp)
                      intro hsk off q p end_v hsw0
                      have hsw1 := hsw_pres hsk off q p end_v hsw0
                      have hsw2 := hstep.2 (hcv_eq ▸ hsk)
                        (fullWatchOffCore st.core skip_lit)
                        (fullWatchOffCore st.core skip_lit + (q - off))
                        (fullWatchOffCore st.core skip_lit + (p - off))
                        (fullWatchOffCore st.core skip_lit + (end_v - off)) hsw1
                      simpa [Nat.add_sub_cancel_left, ← hcore_p] using hsw2) ?_
                intro Jc3 hJc3
                p0_hsplit
                · have hrsz0 : fullWatchSizeCore st.core rw_v.toNat = 0 := by
                    have h := congrArg BitVec.toNat (hc : _)
                    simp only [bv_c0] at h
                    rw [← hrsz_t]; simpa only [hrv_w1] using h
                  p0_hsplit
                  · have hw_pos : 1 ≤ st.core.wlen := by
                      have h := hc
                      rw [Nat.mod_eq_of_lt (by omega : st.core.wlen < 2 ^ 64)] at h
                      omega
                    p0_hsplit
                    · have hfit2 : st.core.wlen + 2 ≤ c.wcap := by
                        have h := hc
                        rw [Nat.mod_eq_of_lt (by omega : st.core.wlen + 2 < 2 ^ 64),
                          Nat.mod_eq_of_lt (by omega : c.wcap < 2 ^ 64)] at h; exact h
                      have hwv_set_lt : (rw_v.setWidth 64 <<< (1 : Nat) + 1).toNat <
                          (st.core.wvec.set
                            (rw_v.setWidth 64 <<< (1 : Nat)).toNat
                            ((BitVec.ofNat 64 st.core.wlen).setWidth 32)).length := by
                        rw [List.length_set, hwv_len, show (1 : BitVec 64) = 1#64 from rfl,
                          hrw64p1_nat]; omega
                      c0_hsteps_nogrp
                      have hmod_wl1 : (st.core.wlen + 1) % 2 ^ 64 = st.core.wlen + 1 :=
                        Nat.mod_eq_of_lt (by omega)
                      have htr32 :
                          (BitVec.ofNat 64 st.core.wlen).setWidth 32 =
                            BitVec.ofNat 32 st.core.wlen := by
                        apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_ofNat]
                      exact hJnext (c.pWstk, ()) m
                        (p0_slow_case2a_fin hlay hlen hrw_lt hw_pos hrsz0 hfit2 how_f hcr_lt_st
                          hcr_ref_st hrw_ne hcv_eq hcore_eq hsc_eq hwat_pres hsw_pres
                          (Eq.mp (congrArg (fun x => (FullMem c x ⋆ R) m) (by
                            dsimp only [ow_v, cr_v]; congr 1; congr 1 <;>
                              (simp only [bv_c0, p0_bv64_1_toNat, p0_bv64_2_toNat, hmod_2rw,
                                hmod_2rw1_rv, hmod_wl1, hwl_nat, htr32] <;> rfl))) hm))
                    · exact hJc3 () m3 hm3
                  · exact hJc3 () m3 hm3
                · exact hJc3 () m3 hm3) ?_
            intro Jc2 hJc2
            p0_hsplit
            · have hrsz_pos : 0 < fullWatchSizeCore st.core rw_v.toNat := by
                have h := hc; simp only [hrv_w1, hrsz_t] at h; exact h
              have hoff_pos := hlay.pos_off rw_v.toNat hrw_lt hrsz_pos
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
                  exact hJnext (c.pWstk, ()) m
                    (p0_slow_case2b_fin rfl hlay hlen hrw_lt hoff_pos hend_wlen hfit2 how_f
                      hcr_lt_st hcr_ref_st hrw_ne hcv_eq hcore_eq hsc_eq hwat_pres hsw_pres
                      (Eq.mp (congrArg (fun x => (FullMem c x ⋆ R) m) (by
                        dsimp only [sz0, ow_v, cr_v]; congr 1; congr 1 <;>
                          (simp only [bv_c0, p0_bv64_1_toNat, p0_bv64_2_toNat, hmod_2rw,
                            hmod_2rw1_rv, hmod_wl1, hrv_w1_raw, hwl_nat, hsz_bv] <;> rfl))) hm))
                · exact hJc2 () m2 hm2
              · exact hJc2 () m2 hm2
            · exact hJc2 () m2 hm2) ?_
        intro Jc1 hJc1
        p0_hsplit
        · have hrsz_pos : 0 < fullWatchSizeCore st.core rw_v.toNat := by
            have h := hc; simp only [hrv_w1, hrsz_t] at h; exact h
          have hoff_pos := hlay.pos_off rw_v.toNat hrw_lt hrsz_pos
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
                congr 1
                simp only [hmod_2rw, hmod_2rw1, hrv_w0_raw, hrv_w1_raw, hroff_t, hrsz_t]
                rw [Nat.mod_eq_of_lt (by omega)]
              p0_hsplit
              · have hsent1 : st.core.wstk[fullWatchOffCore st.core rw_v.toNat +
                    fullWatchSizeCore st.core rw_v.toNat + 1]? = some 0xFFFFFFFF#32 := by
                  rw [List.getElem?_eq_getElem (by rw [hws_len]; omega)]
                  refine congrArg some (Eq.trans ?_ hc)
                  congr 1
                  simp only [hmod_2rw, hmod_2rw1, hrv_w0_raw, hrv_w1_raw, hroff_t, hrsz_t]
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
                c0_hstep
                p0_hsplit
                · c0_hstep; c0_hstep; c0_hstep
                  exact hJwu () _ (by
                    subst hst_c1
                    exact hJnext (c.pWstk, ()) _
                      (p0_slow_case1_fin rfl rfl hlay hlen hrw_lt hoff_pos hend2_le hsent0 hsent1
                        how_f hcr_lt_st hcr_ref_st hrw_ne hcv_eq hcore_eq hsc_eq hwat_pres hsw_pres
                        hm))
                · exact hJwu () _ (by
                    subst hst_c1
                    exact hJnext (c.pWstk, ()) _
                      (p0_slow_case1_fin rfl rfl hlay hlen hrw_lt hoff_pos hend2_le hsent0 hsent1
                        how_f hcr_lt_st hcr_ref_st hrw_ne hcv_eq hcore_eq hsc_eq hwat_pres hsw_pres
                        hm_c1))
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
      cases pok0
      · rfl
      · cases (by assumption : true = false)
    have hstep0 := s15_flush_step_false_preserves (F_cur := F_cur)
      (k := st0.core) (k' := st1.core) (lit := rw0) (skip_lit := skip_lit)
      rfl rfl hlay1 hpres_o0 (hpok0_f hpok0_eq).1
    c0_hsteps_nogrp
    exact hQ false wvec1 wstk1 wlen1 wu1 wsort1 mp0 hlen1 hlay1 hstep0.1 hstep0.2 hmp0

/-! ## 2. `full_prop_flush_del_fid_step9_wp` (`fidPropFlushDelSpec`) -/

/-- Proof of Step-9 `fidStep9PropFlushDelFn` (`full_prop_flush_del_fid`) against
`FullFidelityBcp.fidPropFlushDelSpec`, delegating cold fallback to `full_prop_flush_slow_fid`. -/
theorem full_prop_flush_del_fid_step9_wp (Γ : Env)
    (hSlow : ∀ a m Q X, fidPropFlushSlowSpec a m Q X →
      Γ "full_prop_flush_slow_fid" [i64, i64, i64] [.bool] a m Q X) :
    ∀ a m Q X, fidPropFlushDelSpec a m Q X → Func.wp Γ fidStep9PropFlushDelFn.body a m Q X := by
  rintro ⟨h, di, ⟨⟩⟩ m0 Q X hs
  obtain ⟨c, F_cur, st0, R, dlen, skip_lit, rfl, hlen0, hlay0, hdi_eq, hdlen_le, hdel0, hm0, hQ⟩ :=
    fidPropFlushDelSpec_elim hs
  have hdelc : c.delayed_cap < dimacsBound := c.hdel
  have hwc : c.wcap < 2 * dimacsBound := c.hwcap
  have hmaxv : c.max_vars < 2 * dimacsBound := c.hmaxv
  unfold dimacsBound at hdelc hwc hmaxv
  unfold Func.wp fidStep9PropFlushDelFn; dsimp only; unfold full_prop_flush_del_fid_body
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
      have hrlit_get : st.scratch.delayed[j_v.toNat]'(by omega) =
          st0.scratch.delayed[3 * idx]?.getD 0#32 := by
        rw [← hdel_eq, List.getElem?_eq_getElem (by omega), Option.getD_some]; simp only [hj_eq]
      have hrw0_get : st.scratch.delayed[(j_v + 1#64).toNat]'(by rw [hj1_nat]; omega) =
          st0.scratch.delayed[3 * idx + 1]?.getD 0#32 := by
        rw [← hdel_eq, List.getElem?_eq_getElem (by omega), Option.getD_some]; simp only [hj1_nat]
      have hrcr_get : st.scratch.delayed[(j_v + 2#64).toNat]'(by rw [hj2_nat]; omega) =
          st0.scratch.delayed[3 * idx + 2]?.getD 0#32 := by
        rw [← hdel_eq, List.getElem?_eq_getElem (by omega), Option.getD_some]; simp only [hj2_nat]
      let rw_v := st.scratch.delayed[j_v.toNat]'(by omega)
      let ow_v := st.scratch.delayed[(j_v + 1#64).toNat]'(by rw [hj1_nat]; omega)
      let cr_v := st.scratch.delayed[(j_v + 2#64).toNat]'(by rw [hj2_nat]; omega)
      have hrw_lt : rw_v.toNat < 2 * st.core.cur_vars := by
        dsimp only [rw_v]; rw [hrlit_get, hcv_eq]; exact hrlit_lt
      have hrw_ne : rw_v.toNat ≠ skip_lit := by
        dsimp only [rw_v]; rw [hrlit_get]; exact hrlit_ne
      have how_f : (ow_v &&& 0x80000000#32) = 0#32 := by
        dsimp only [ow_v]; rw [hrw0_get]; exact hrw0_f
      have hcr_lt_st : cr_v.toNat < 0x80000000 := by
        dsimp only [cr_v]; rw [hrcr_get]; exact hrcr_lt
      have hcr_ref_st : cr_v.toNat ∈ fullArenaClauseRefsCore st.core := by
        dsimp only [cr_v]; rw [hrcr_get, href_eq]; exact hrcr_ref
      have hrw64_nat : (rw_v.setWidth 64 <<< (1 : Nat)).toNat = 2 * rw_v.toNat := by
        rw [BitVec.toNat_shiftLeft, zext_toNat _ (by decide)]; simp [Nat.shiftLeft_eq]; omega
      have hrw64p1_nat : ((rw_v.setWidth 64 <<< (1 : Nat)) + 1#64).toNat = 2 * rw_v.toNat + 1 := by
        rw [BitVec.toNat_add, hrw64_nat]; change (2 * rw_v.toNat + 1) % 2 ^ 64 = _
        exact Nat.mod_eq_of_lt (by omega)
      have hwv_i0 : (rw_v.setWidth 64 <<< (1 : Nat)).toNat < st.core.wvec.length := by
        rw [hwv_len, hrw64_nat]; omega
      have hwv_i1 : ((rw_v.setWidth 64 <<< (1 : Nat)) + 1#64).toNat < st.core.wvec.length := by
        rw [hwv_len, hrw64p1_nat]; omega
      let roff_w := st.core.wvec[(rw_v.setWidth 64 <<< (1 : Nat)).toNat]'hwv_i0
      let rsz_w := st.core.wvec[((rw_v.setWidth 64 <<< (1 : Nat)) + 1#64).toNat]'hwv_i1
      have hroff_eq : (roff_w.setWidth 64).toNat = fullWatchOffCore st.core rw_v.toNat := by
        rw [zext_toNat _ (by decide)]; unfold fullWatchOffCore
        rw [List.getElem?_eq_getElem (by rw [hwv_len]; omega), Option.getD_some]
        exact congrArg BitVec.toNat (by simp [roff_w, hrw64_nat])
      have hrsz_eq : (rsz_w.setWidth 64).toNat = fullWatchSizeCore st.core rw_v.toNat := by
        rw [zext_toNat _ (by decide)]; unfold fullWatchSizeCore
        rw [List.getElem?_eq_getElem (by rw [hwv_len]; omega), Option.getD_some]
        exact congrArg BitVec.toNat (by simp [rsz_w, hrw64p1_nat])
      have hbd_rw := hlay.bounds rw_v.toNat hrw_lt
      have hrend_nat : (roff_w.setWidth 64 + rsz_w.setWidth 64).toNat =
          fullWatchOffCore st.core rw_v.toNat + fullWatchSizeCore st.core rw_v.toNat := by
        rw [BitVec.toNat_add, hroff_eq, hrsz_eq, Nat.mod_eq_of_lt (by omega)]
      have hrend1_nat : (roff_w.setWidth 64 + rsz_w.setWidth 64 + 1#64).toNat =
          fullWatchOffCore st.core rw_v.toNat + fullWatchSizeCore st.core rw_v.toNat + 1 := by
        rw [BitVec.toNat_add, hrend_nat]; change (_ + 1) % 2 ^ 64 = _
        exact Nat.mod_eq_of_lt (by omega)
      have hrend2_nat : (roff_w.setWidth 64 + rsz_w.setWidth 64 + 2#64).toNat =
          fullWatchOffCore st.core rw_v.toNat + fullWatchSizeCore st.core rw_v.toNat + 2 := by
        rw [BitVec.toNat_add, hrend_nat]; change (_ + 2) % 2 ^ 64 = _
        exact Nat.mod_eq_of_lt (by omega)
      have hwl_nat : (BitVec.ofNat 64 st.core.wlen).toNat = st.core.wlen :=
        p0_bv64_ofNat (by omega)
      have hwl1_nat : (BitVec.ofNat 64 st.core.wlen + 1#64).toNat = st.core.wlen + 1 := by
        rw [BitVec.toNat_add, hwl_nat]; change (_ + 1) % 2 ^ 64 = _
        exact Nat.mod_eq_of_lt (by omega)
      have hwl2_nat : (BitVec.ofNat 64 st.core.wlen + 2#64).toNat = st.core.wlen + 2 := by
        rw [BitVec.toNat_add, hwl_nat]; change (_ + 2) % 2 ^ 64 = _
        exact Nat.mod_eq_of_lt (by omega)
      have hwc_nat : (BitVec.ofNat 64 c.wcap).toNat = c.wcap := p0_bv64_ofNat (by omega)
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
        dsimp only [p0FlushDisk, roff_w]; congr 1
      have hrv_w1 : (p0FlushDisk wl_d wu_d st).core.wvec[
          (2 * (p0FlushDisk wl_d wu_d st).scratch.delayed[j_v.toNat].toNat + 1) % 2 ^ 64]'(by
            dsimp only [p0FlushDisk]
            change (2 * rw_v.toNat + 1) % 2 ^ 64 < st.core.wvec.length
            rw [hwv_len, Nat.mod_eq_of_lt (by omega : 2 * rw_v.toNat + 1 < 2 ^ 64)]; omega) =
          rsz_w := by
        dsimp only [p0FlushDisk, rsz_w]; congr 1
        change (2 * rw_v.toNat + 1) % 2 ^ 64 = (rw_v.setWidth 64 <<< (1 : Nat) + 1#64).toNat
        rw [hrw64p1_nat, Nat.mod_eq_of_lt (by omega : 2 * rw_v.toNat + 1 < 2 ^ 64)]
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
      have hmod_2rw_rv : 2 * rw_v.toNat % 2 ^ 64 = 2 * rw_v.toNat := Nat.mod_eq_of_lt (by omega)
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
            (fun _ p mn h => by
              try dsimp only [Blocks.get_here, Blocks.get_there]
              exact h) ?_
          intro Jnext2 hJnext2
          refine wp_join_group (ts := [])
            (fun _ m3 => (FullMem c (p0FlushDisk wl_d wu_d st) ⋆ R) m3)
            (fun _ ⟨⟩ m3 hm3 => by
              dsimp only [Blocks.get_here, Blocks.get_there]
              refine wp_join_group (ts := [])
                (fun _ mc => (FullMem c (p0FlushDisk wl_d wu_d st) ⋆ R) mc)
                (fun _ ⟨⟩ mc hmc => by
                  -- Cold fallback: sync wlen & wu, tail-call `full_prop_flush_slow_fid`
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
                      { st with
                        core := { st.core with wvec := wvec', wstk := wstk',
                                               wlen := wlen', wusable := wu' }
                        scratch := { st.scratch with wsort := wsort' } }
                    have hcore_p : st_p.core = { st0.core with
                        wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' } := by
                      dsimp only [st_p]; rw [hcore_eq]
                    have hsc_p : st_p.scratch = { st0.scratch with wsort := wsort' } := by
                      dsimp only [st_p]; rw [hsc_eq]
                    have hst_p_eq : st_p =
                        { st0 with
                          core := { st0.core with wvec := wvec', wstk := wstk',
                                                  wlen := wlen', wusable := wu' }
                          scratch := { st0.scratch with wsort := wsort' } } := by
                      cases h1 : st_p; rw [h1] at hcore_p hsc_p; dsimp only at hcore_p hsc_p
                      rw [hcore_p, hsc_p]
                    c0_hsteps_nogrp
                    refine hQ ok wvec' wstk' wlen' wu' wsort' mp (hst_p_eq ▸ hlen_p)
                      (hcore_p ▸ hlay_p) (fun hw0 => hcore_p ▸ hwat_p (hwat_pres hw0)) ?_
                      (hst_p_eq ▸ hmp)
                    intro hsk off q p end_v hsw0
                    have hsw1 := hsw_pres hsk off q p end_v hsw0
                    have hsw2 := hsw_p (hcv_eq ▸ hsk)
                      (fullWatchOffCore st.core skip_lit)
                      (fullWatchOffCore st.core skip_lit + (q - off))
                      (fullWatchOffCore st.core skip_lit + (p - off))
                      (fullWatchOffCore st.core skip_lit + (end_v - off)) hsw1
                    simpa [Nat.add_sub_cancel_left, ← hcore_p] using hsw2) ?_
              -- Case 3: rsz == 0 && wlen > 0 && wlen + 2 <= wcap
              intro Jc3 hJc3
              p0_hsplit
              · have hrsz0 : fullWatchSizeCore st.core rw_v.toNat = 0 := by
                  have h := congrArg BitVec.toNat (hc : _)
                  simp only [bv_c0, p0FlushDisk] at h
                  rw [← hrsz_t]; simpa only [hrv_w1_s] using h
                p0_hsplit
                · have hw_pos : 1 ≤ st.core.wlen := by
                    have h := hc
                    rw [Nat.mod_eq_of_lt (by omega : st.core.wlen < 2 ^ 64)] at h
                    omega
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
                    obtain ⟨hlen_k, hlay_k, _, hpres_o, hsz_k, hpre_k, hw0_k, hw1_k⟩ :=
                      p0_repl_empty_layout hlay hlen.core_ok hrw_lt hw_pos hrsz0 hfit2 how_f
                        hcr_lt_st
                    let st_n : FullState :=
                      { st with core :=
                          { st.core with
                            wstk :=
                              (st.core.wstk.set st.core.wlen ow_v).set (st.core.wlen + 1) cr_v
                            wvec := (st.core.wvec.set (2 * rw_v.toNat)
                              (BitVec.ofNat 32 st.core.wlen)).set (2 * rw_v.toNat + 1) 2#32
                            wlen := st.core.wlen + 2 } }
                    have hstep := s15_flush_step_preserves (F_cur := F_cur) (k := st.core)
                      (k' := st_n.core) (lit := rw_v) (w0 := ow_v) (cref := cr_v)
                      (skip_lit := skip_lit) rfl rfl hlay_k hrw_lt how_f hcr_lt_st hcr_ref_st
                      hpres_o ⟨hsz_k, hpre_k, hw0_k, hw1_k⟩
                    have hwl_bv :
                        BitVec.ofNat 64 st.core.wlen + 2#64 =
                          BitVec.ofNat 64 (st.core.wlen + 2) := by
                      apply BitVec.eq_of_toNat_eq; rw [hwl2_nat, p0_bv64_ofNat (by omega)]
                    have hmod_wl1 : (st.core.wlen + 1) % 2 ^ 64 = st.core.wlen + 1 :=
                      Nat.mod_eq_of_lt (by omega)
                    have htr32 :
                        (BitVec.ofNat 64 st.core.wlen).setWidth 32 =
                          BitVec.ofNat 32 st.core.wlen := by
                      apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_ofNat]
                    refine hJnext (BitVec.ofNat 64 st.core.wlen + 2#64, st.core.wusable, ()) m
                      ⟨st_n, wl_d, wu_d, hwl_bv, rfl, by dsimp [st_n]; rw [hcore_eq], hsc_eq,
                       ⟨hlen_k, hlen.scratch_ok⟩, hlay_k,
                       fun hw0 => hstep.1 (hwat_pres hw0), ?_, ?_⟩
                    · intro hsk off q p end_v hsw0
                      have hsw1 := hsw_pres hsk off q p end_v hsw0
                      have hsw2 := hstep.2 hrw_ne (hcv_eq ▸ hsk)
                        (fullWatchOffCore st.core skip_lit)
                        (fullWatchOffCore st.core skip_lit + (q - off))
                        (fullWatchOffCore st.core skip_lit + (p - off))
                        (fullWatchOffCore st.core skip_lit + (end_v - off)) hsw1
                      simpa only [Nat.add_sub_cancel_left] using hsw2
                    · refine Eq.mp (congrArg (fun x => (FullMem c x ⋆ R) m) ?_) hm
                      unfold p0FlushDisk; dsimp only [st_n, ow_v, cr_v]; congr 1; congr 1 <;>
                        (simp only [bv_c0, p0_bv64_1_toNat, p0_bv64_2_toNat, hmod_2rw,
                          hmod_2rw1_rv, hmod_wl1, hwl_nat, htr32] <;> rfl)
                  · exact hJc3 () m3 hm3
                · exact hJc3 () m3 hm3
              · exact hJc3 () m3 hm3) ?_
          -- Case 2: rsz > 0 && roff + rsz == wlen && wlen + 2 <= wcap
          intro Jc2 hJc2
          p0_hsplit
          · have hrsz_pos : 0 < fullWatchSizeCore st.core rw_v.toNat := by
              have h := hc
              simp only [bv_c0, p0FlushDisk, hmod_2rw1, hrv_w1_raw, hrsz_t] at h; exact h
            have hoff_pos := hlay.pos_off rw_v.toNat hrw_lt hrsz_pos
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
                obtain ⟨hlen_k, hlay_k, _, hpres_o, hsz_k, hpre_k, hw0_k, hw1_k⟩ :=
                  s15_append_end_layout hlay hlen.core_ok hrw_lt hoff_pos hend_wlen hfit2 how_f
                    hcr_lt_st
                let sz0 := fullWatchSizeCore st.core rw_v.toNat
                let st_n : FullState :=
                  { st with core :=
                      { st.core with
                        wstk :=
                          (st.core.wstk.set st.core.wlen ow_v).set (st.core.wlen + 1) cr_v
                        wvec :=
                          st.core.wvec.set (2 * rw_v.toNat + 1) (BitVec.ofNat 32 (sz0 + 2))
                        wlen := st.core.wlen + 2 } }
                have hstep := s15_flush_step_preserves (F_cur := F_cur) (k := st.core)
                  (k' := st_n.core) (lit := rw_v) (w0 := ow_v) (cref := cr_v)
                  (skip_lit := skip_lit) rfl rfl (by simpa [st_n, hend_wlen] using hlay_k)
                  hrw_lt how_f hcr_lt_st hcr_ref_st (by simpa [st_n, hend_wlen] using hpres_o)
                  ⟨by simpa [st_n, hend_wlen] using hsz_k,
                   by simpa [st_n, hend_wlen] using hpre_k,
                   by simpa [st_n, hend_wlen] using hw0_k,
                   by simpa [st_n, hend_wlen] using hw1_k⟩
                have hwl_bv :
                    BitVec.ofNat 64 st.core.wlen + 2#64 =
                      BitVec.ofNat 64 (st.core.wlen + 2) := by
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
                refine hJnext (BitVec.ofNat 64 st.core.wlen + 2#64, st.core.wusable, ()) m
                  ⟨st_n, wl_d, wu_d, hwl_bv, rfl, by dsimp [st_n]; rw [hcore_eq], hsc_eq,
                   ⟨by simpa [st_n, hend_wlen] using hlen_k, hlen.scratch_ok⟩,
                   by simpa [st_n, hend_wlen] using hlay_k,
                   fun hw0 => hstep.1 (hwat_pres hw0), ?_, ?_⟩
                · intro hsk off q p end_v hsw0
                  have hsw1 := hsw_pres hsk off q p end_v hsw0
                  have hsw2 := hstep.2 hrw_ne (hcv_eq ▸ hsk)
                    (fullWatchOffCore st.core skip_lit)
                    (fullWatchOffCore st.core skip_lit + (q - off))
                    (fullWatchOffCore st.core skip_lit + (p - off))
                    (fullWatchOffCore st.core skip_lit + (end_v - off)) hsw1
                  simpa only [Nat.add_sub_cancel_left] using hsw2
                · refine Eq.mp (congrArg (fun x => (FullMem c x ⋆ R) m) ?_) hm
                  unfold p0FlushDisk; dsimp only [st_n, ow_v, cr_v]; congr 1; congr 1 <;>
                    (simp only [bv_c0, p0_bv64_1_toNat, p0_bv64_2_toNat, hmod_2rw, hmod_2rw1_rv,
                      hmod_wl1, hrv_w1_raw, hwl_nat, hsz_bv] <;> rfl)
              · exact hJc2 () m2 hm2
            · exact hJc2 () m2 hm2
          · exact hJc2 () m2 hm2) ?_
      intro Jc1 hJc1
      p0_hsplit
      · have hrsz_pos : 0 < fullWatchSizeCore st.core rw_v.toNat := by
          have h := hc; simp only [bv_c0, p0FlushDisk, hmod_2rw1, hrv_w1_raw, hrsz_t] at h; exact h
        have hoff_pos := hlay.pos_off rw_v.toNat hrw_lt hrsz_pos
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
              congr 1
              simp only [bv_c0, p0FlushDisk, hmod_2rw, hmod_2rw1, hrv_w0_raw, hrv_w1_raw,
                hroff_t, hrsz_t]
              rw [Nat.mod_eq_of_lt (by omega)]
            p0_hsplit
            · have hsent1 : st.core.wstk[fullWatchOffCore st.core rw_v.toNat +
                  fullWatchSizeCore st.core rw_v.toNat + 1]? = some 0xFFFFFFFF#32 := by
                rw [List.getElem?_eq_getElem (by rw [hws_len]; omega)]
                refine congrArg some (Eq.trans ?_ hc)
                congr 1
                simp only [bv_c0, p0FlushDisk, hmod_2rw, hmod_2rw1, hrv_w0_raw, hrv_w1_raw,
                  hroff_t, hrsz_t]
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
                obtain ⟨hlen_k, hlay_k, _, hpres_o, hsz_k, hpre_k, hw0_k, hw1_k⟩ :=
                  s15_append_sentinel_layout hlay hlen.core_ok (wu' := wu_n) hrw_lt hoff_pos
                    hend2_le hsent0 hsent1 how_f hcr_lt_st
                let st_n : FullState :=
                  { st with core :=
                      { st.core with
                        wstk := (st.core.wstk.set wend0 ow_v).set (wend0 + 1) cr_v
                        wvec := st.core.wvec.set (2 * rw_v.toNat + 1)
                          (BitVec.ofNat 32 (sz0 + 2))
                        wusable := wu_n } }
                have hstep := s15_flush_step_preserves (F_cur := F_cur) (k := st.core)
                  (k' := st_n.core) (lit := rw_v) (w0 := ow_v) (cref := cr_v)
                  (skip_lit := skip_lit) rfl rfl hlay_k hrw_lt how_f hcr_lt_st hcr_ref_st
                  hpres_o ⟨hsz_k, hpre_k, hw0_k, hw1_k⟩
                refine hJnext (BitVec.ofNat 64 st.core.wlen, wu_n, ()) mn
                  ⟨st_n, wl_d, wu_d, rfl, rfl, by dsimp [st_n]; rw [hcore_eq], hsc_eq,
                   ⟨hlen_k, hlen.scratch_ok⟩, hlay_k, fun hw0 => hstep.1 (hwat_pres hw0), ?_, hmn⟩
                intro hsk off q p end_v hsw0
                have hsw1 := hsw_pres hsk off q p end_v hsw0
                have hsw2 := hstep.2 hrw_ne (hcv_eq ▸ hsk)
                  (fullWatchOffCore st.core skip_lit)
                  (fullWatchOffCore st.core skip_lit + (q - off))
                  (fullWatchOffCore st.core skip_lit + (p - off))
                  (fullWatchOffCore st.core skip_lit + (end_v - off)) hsw1
                simpa only [Nat.add_sub_cancel_left] using hsw2
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
                  simp only [bv_c0, p0_bv64_1_toNat, p0_bv64_2_toNat, hmod_2rw, hmod_2rw1_rv,
                    hrv_w0_raw, hrv_w1_raw, hroff_t, hrsz_t, hsz_bv,
                    Nat.mod_eq_of_lt (by omega :
                      fullWatchOffCore st.core rw_v.toNat +
                        fullWatchSizeCore st.core rw_v.toNat < 2 ^ 64),
                    Nat.mod_eq_of_lt (by omega :
                      fullWatchOffCore st.core rw_v.toNat +
                        fullWatchSizeCore st.core rw_v.toNat + 1 < 2 ^ 64)] <;> rfl
              · refine hfin st.core.wusable m ?_
                refine Eq.mp (congrArg (fun x => (FullMem c x ⋆ R) m) ?_) hm
                unfold p0FlushDisk; dsimp only [wend0, sz0, ow_v, cr_v]; congr 1; congr 1 <;>
                  simp only [bv_c0, p0_bv64_1_toNat, p0_bv64_2_toNat, hmod_2rw, hmod_2rw1_rv,
                    hrv_w0_raw, hrv_w1_raw, hroff_t, hrsz_t, hsz_bv,
                    Nat.mod_eq_of_lt (by omega :
                      fullWatchOffCore st.core rw_v.toNat +
                        fullWatchSizeCore st.core rw_v.toNat < 2 ^ 64),
                    Nat.mod_eq_of_lt (by omega :
                      fullWatchOffCore st.core rw_v.toNat +
                        fullWatchSizeCore st.core rw_v.toNat + 1 < 2 ^ 64)] <;> rfl
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
          simpa only [← hcore_eq] using hsw_pres hsk off q p end_v hsw0)
        (hst_eq ▸ hm_sync)

/-! ## 3. `full_rebuild_watches_nosort_fid_step9_wp` & `full_rebuild_watches_step9_wp` -/

section RebuildStep9

private def S9RebuildOk (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s s' : FullState) : Prop :=
  FullSparseInvW c F0 F_cur s' ∧ s'.core.cur_level = 0 ∧
  s'.core.fuel.toNat ≤ s.core.fuel.toNat

private theorem s9RebuildOk_sweep {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st : FullState} (hst : S9RebuildOk c F0 F_cur s st)
    {vals' : List (BitVec 8)}
    {flags' lvl' rsns' trl' tp' wvec' wstk' arena' : List (BitVec 32)}
    {te' alen' wlen' : Nat} {unass' unfl' wu' fred' ni' nr' nb' oom' : BitVec 64}
    {sc' : FullScratch} :
    let sA : FullState :=
      { st with
        core := { st.core with
          vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
          trail_pos := tp', trail_end := te', unassigned := unass', unflushed := unfl',
          wvec := wvec', wstk := wstk', arena := arena', arena_len := alen', wlen := wlen',
          wusable := wu', arena_garbage := 0#64, first_reducible := fred', num_irred := ni',
          num_redundant := nr', num_binary := nb', oom := oom' }
        scratch := sc' }
    sA.LengthsOk c → FullWitnessInv c F0 F_cur sA.core → Full.FullArenaVarsNodup sA →
    FullLastLearnedWf sA → sc'.extend_len = st.scratch.extend_len →
    S9RebuildOk c F0 F_cur s sA := by
  intro sA hlenA hwA hndA hllA hextA
  exact ⟨⟨hlenA, hwA, hst.1.2.2.1, hndA, ⟨hllA, hextA ▸ hst.1.2.2.2.2.1.2⟩, hst.1.2.2.2.2.2⟩,
    hst.2.1, hst.2.2⟩

private theorem s9RebuildOk_bcp {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s sA : FullState} (hA : S9RebuildOk c F0 F_cur s sA)
    {valsB : List (BitVec 8)}
    {flagsB lvlB rsnsB trlB tpB wvecB arenaB wstkB : List (BitVec 32)}
    {teB propB wlenB : Nat} {unassB unflB wuB fuelB ctypeB crefB c0B c1B oomB ticksB : BitVec 64}
    {wsortB delayedB : List (BitVec 32)} {phasesB : List (BitVec 8)} :
    let sB : FullState :=
      { sA with
        core := { sA.core with
          vals := valsB, flags := flagsB, lvl := lvlB, rsns := rsnsB, trl := trlB,
          trail_pos := tpB, trail_end := teB, propagated := propB, unassigned := unassB,
          unflushed := unflB, wvec := wvecB, arena := arenaB, wstk := wstkB, wlen := wlenB,
          wusable := wuB, fuel := fuelB, confl_type := ctypeB, confl_ref := crefB,
          confl_lit0 := c0B, confl_lit1 := c1B, oom := oomB }
        scratch := { sA.scratch with
          search_ticks := ticksB, wsort := wsortB, phases := phasesB, delayed := delayedB } }
    sB.LengthsOk c → FullWitnessInv c F0 F_cur sB.core →
    FullArenaPermEq sA.core sB.core → fuelB.toNat ≤ sA.core.fuel.toNat →
    S9RebuildOk c F0 F_cur s sB := by
  intro sB hlenB hwB hpermB hfuelB
  have hndB : Full.FullArenaVarsNodup sB := fun ref href hng => by
    have href0 : ref ∈ fullArenaClauseRefs sA := by
      change ref ∈ fullArenaClauseRefsCore sB.core at href
      change ref ∈ fullArenaClauseRefsCore sA.core; rwa [← hpermB.2.1]
    have hp := hpermB.2.2 ref href0
    have hgb : fullArenaClauseGarb sA ref = false := by
      change fullArenaClauseGarbCore sA.core ref = false
      change fullArenaClauseGarbCore sB.core ref = false at hng; rwa [← hp.2.1]
    exact (hp.2.2.map (· / 2)).nodup_iff.mpr (hA.1.2.2.2.1 ref href0 hgb)
  have hllB : FullLastLearnedWf sB :=
    hA.1.2.2.2.2.1.1.of_refs_subset rfl fun ref href => by
      change ref ∈ fullArenaClauseRefsCore sA.core at href
      change ref ∈ fullArenaClauseRefsCore sB.core; rwa [hpermB.2.1]
  exact ⟨⟨hlenB, hwB, hA.1.2.2.1, hndB, ⟨hllB, hA.1.2.2.2.2.1.2⟩, hA.1.2.2.2.2.2⟩,
    hA.2.1, Nat.le_trans hfuelB hA.2.2⟩

end RebuildStep9

/-- Parametric `Func.wp` proof for `fidStep9RebuildWatchesNosortFn`
(`full_rebuild_watches_nosort_fid`, rebuild without binary-watch sorting) against
`Full.fullRebuildWatchesSpec`. -/
theorem full_rebuild_watches_nosort_fid_step9_wp (Γ : Env)
    (hSweep : ∀ a m Q X, Full.fullArenaSweepSpec a m Q X →
      Γ "full_arena_sweep" [i64] [i64] a m Q X)
    (hProp : ∀ a m Q X, FullM6BcpS15.fullBcpS15Spec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X) :
    ∀ a m Q X, Full.fullRebuildWatchesSpec a m Q X →
      Func.wp Γ fidStep9RebuildWatchesNosortFn.body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m0 Q X ⟨c, F0, s, R, rfl, hdn, hm0, hQ⟩
  obtain ⟨F_cur, hdw⟩ := hdn.exists_witness
  let s0 : FullState := { s with core := { s.core with dense_mode := 0#64 } }
  have hsp0 : FullSparseInvW c F0 F_cur s0 := hdw.toSparse_clear_dense
  have hok0 : S9RebuildOk c F0 F_cur s s0 := ⟨hsp0, hdw.2.2.2.2.2.1, Nat.le_refl _⟩
  unfold Func.wp fidStep9RebuildWatchesNosortFn; dsimp only
  unfold full_rebuild_watches_nosort_fid_body
  c0_hsteps_nogrp
  refine wp_join_group (ts := [])
    (fun () m1 => ∃ st : FullState, S9RebuildOk c F0 F_cur s st ∧ (FullMem c st ⋆ R) m1)
    (fun _ () m1 ⟨st, hok, hm1⟩ => by
      c0_hsteps_nogrp
      exact hQ 1#64 _ m1 hok.1.toSparse hok.2.1 hok.2.2 (Or.inr (Or.inl rfl))
        (fun h => by cases h) hm1)
    ?_
  intro Jbrk hJbrk
  c0_hsteps_nogrp
  refine wp_loop_group (ts := [])
    (fun rem () ml => ∃ st : FullState, rem = c.max_vars - st.core.trail_end ∧
      S9RebuildOk c F0 F_cur s st ∧ (FullMem c st ⋆ R) ml) ?_ ?_
  · rintro L rem ⟨⟩ ml ih ⟨st, rfl, hok_st, hm_st⟩
    dsimp only [Blocks.get]
    refine wp_jnz_of (fun _ => ?_) (fun hc => by cases hc)
    c0_hsteps_nogrp
    p0_call hSweep
    refine ⟨c, F0, F_cur, st, R, rfl, hok_st.1.1, hok_st.1.2.1, hok_st.1.2.2.2.1,
      hok_st.1.2.2.2.2.2, fun hpos => by have := hok_st.2.1; omega, hm_st,
      fun sr vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec' wstk' arena' alen'
        wlen' wu' fred' ni' nr' nb' oom' sc' mA hlenA hsr_dom hextA _ hllA hwA hndA
        _ _ hsr1 hsr2 _ hmA => ?_⟩
    let sA : FullState :=
      { st with
        core := { st.core with
          vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
          trail_pos := tp', trail_end := te', unassigned := unass', unflushed := unfl',
          wvec := wvec', wstk := wstk', arena := arena', arena_len := alen', wlen := wlen',
          wusable := wu', arena_garbage := 0#64, first_reducible := fred', num_irred := ni',
          num_redundant := nr', num_binary := nb', oom := oom' }
        scratch := sc' }
    have hokA : S9RebuildOk c F0 F_cur s sA := s9RebuildOk_sweep hok_st hlenA hwA hndA hllA hextA
    c0_hsteps_nogrp
    · exact hQ 20#64 sA mA hokA.1.toSparse hokA.2.1 hokA.2.2 (Or.inr (Or.inr rfl))
        (fun _ => (hsr2 hc).2) hmA
    · exact hQ 0#64 sA mA hokA.1.toSparse hokA.2.1 hokA.2.2 (Or.inl rfl)
        (fun h => by cases h) hmA
    · p0_call hProp
      refine ⟨c, F0, F_cur, sA, R, rfl, hlenA, hwA, hokA.1.2.2.2.2.2, hmA,
        fun pr valsB flagsB lvlB rsnsB trlB tpB teB propB unassB unflB wvecB arenaB wstkB
          wlenB wuB fuelB ctypeB crefB c0B c1B oomB ticksB wsortB phasesB delayedB mB
          hlenB hwB htrB hpermB _ hfuelB _ _ hpr1 _ _ hmB => ?_⟩
      let sB : FullState :=
        { sA with
          core := { sA.core with
            vals := valsB, flags := flagsB, lvl := lvlB, rsns := rsnsB, trl := trlB,
            trail_pos := tpB, trail_end := teB, propagated := propB, unassigned := unassB,
            unflushed := unflB, wvec := wvecB, arena := arenaB, wstk := wstkB, wlen := wlenB,
            wusable := wuB, fuel := fuelB, confl_type := ctypeB, confl_ref := crefB,
            confl_lit0 := c0B, confl_lit1 := c1B, oom := oomB }
          scratch := { sA.scratch with
            search_ticks := ticksB, wsort := wsortB, phases := phasesB, delayed := delayedB } }
      have hokB : S9RebuildOk c F0 F_cur s sB := s9RebuildOk_bcp hokA hlenB hwB hpermB hfuelB
      c0_hsteps_nogrp
      · have hunsat : F0.Unsat :=
          FullVivTopSpecs.level0_unsat_of_conflict_okW hwB hokA.2.1 (hpr1 hc).2.2
        exact hQ 20#64 sB mB hokB.1.toSparse hokB.2.1 hokB.2.2 (Or.inr (Or.inr rfl))
          (fun _ => hunsat) hmB
      · exact hJbrk () mB ⟨sB, hokB, hmB⟩
      · have hsr_eq1 : sr = 1#64 := by
          rcases hsr_dom with rfl | rfl | rfl | rfl <;> first | rfl | contradiction
        obtain ⟨_, hte_lt⟩ := hsr1 hsr_eq1
        have hte_bd : sB.core.trail_end ≤ c.max_vars :=
          Nat.le_trans hlenB.core_ok.trail_end_le hlenB.core_ok.cur_vars_le
        have hteA : sA.core.trail_end = te' := rfl
        have hte_le : sA.core.trail_end ≤ sB.core.trail_end := htrB.1
        rw [hteA] at hte_le
        exact ih (c.max_vars - sB.core.trail_end) () mB (by omega) ⟨sB, rfl, hokB, hmB⟩
  · intro L hL; c0_hsteps_nogrp
    exact hL (c.max_vars - s0.core.trail_end) () _ ⟨s0, rfl, hok0, by assumption⟩

/-- Parametric `Func.wp` proof for `fidStep9RebuildWatchesFn` (`full_rebuild_watches`) against
`Full.fullRebuildWatchesSpec`: calls `full_rebuild_watches_nosort_fid`, sorting binary watches when
`rr == 1ULL`. -/
theorem full_rebuild_watches_step9_wp (Γ : Env)
    (hNosort : ∀ a m Q X, Full.fullRebuildWatchesSpec a m Q X →
      Γ "full_rebuild_watches_nosort_fid" [i64] [i64] a m Q X)
    (hSortBin : ∀ a m Q X, step7SortBinWatchesSpec a m Q X →
      Γ "full_sort_bin_watches_fid" [i64] [] a m Q X) :
    ∀ a m Q X, Full.fullRebuildWatchesSpec a m Q X →
      Func.wp Γ fidStep9RebuildWatchesFn.body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m0 Q X ⟨c, F0, s, R, rfl, hdn, hm0, hQ⟩
  unfold Func.wp fidStep9RebuildWatchesFn; dsimp only; unfold full_rebuild_watches_body
  c0_hsteps_nogrp
  p0_call hNosort
  refine ⟨c, F0, s, R, rfl, hdn, hm0, fun rr sr mr hspr hclr hfur hdomr hunsr hmr => ?_⟩
  c0_hsteps
  · obtain ⟨F_cur, hspW⟩ := hspr.exists_witness
    have hrr1 : rr = 1#64 := by c0_bound
    subst hrr1
    p0_call hSortBin
    refine ⟨c, F0, F_cur, sr, R, rfl, hspW, hmr, fun wstk' m2 _ hsp' _ hm2 => ?_⟩
    c0_hsteps_nogrp
    exact hQ 1#64 _ m2 hsp'.toSparse hclr hfur (Or.inr (Or.inl rfl)) (fun h => by cases h) hm2
  · exact hQ rr sr mr hspr hclr hfur hdomr hunsr hmr

end LeanQbe.T.Examples.Kissat.FullFidelityStep9

end
