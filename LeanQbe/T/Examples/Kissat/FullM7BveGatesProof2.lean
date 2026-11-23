module

public import LeanQbe.T.Examples.Kissat.FullM7BveGatesProof0
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullBvaFwdSpec
import LeanQbe.T.Examples.Kissat.FullDenseWatchLemmas1
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Wave-4E (`FullM7BveGates`) Proofs — Part 2 (`full_fwd_check_cl_m7` & `full_forward_sub_m7`)

M1-clean proof module (`public section`, `0` `@[expose]`, `0` `import all`, `private` helpers):
1. `full_fwd_check_cl_m7_wp` (`fullFwdCheckClM7Spec`) + canonical `full_fwd_check_cl_m7_wp_canon`
   (`Full.fullFwdCheckClSpec`) dispatching `full_fwd_scan_lit_m7`.
2. `full_forward_sub_m7_wp` (certifies canonical `FullFastBveBudgets.fullForwardSubFastSpec`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM7BveGates

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullBvaFwdHelpers
open LeanQbe.T.Examples.Kissat.Full.FullDenseWatchHelpers
open LeanQbe.T.Examples.Kissat.FullFastBveBudgets
open LeanQbe.T.Examples.Kissat.FullM6BveFwd
open Kraken.Bedrock2.Test

open scoped FullArenaTactics

local macro "m7_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

/-! ## 1. Clause-Shrink & Lit-Mark Helpers -/

private theorem m7_p2_lit_compl_conflict {α : Nat → Bool} {l : Nat}
    (h1 : α (litVar l) = !litSign l)
    (h2 : α (litVar (l ^^^ 1)) = !litSign (l ^^^ 1)) : False := by
  simp only [litVar, litSign] at h1 h2
  rw [fullInv_var_xor1 l, m6_xor1_mod2 l] at h2
  rcases Nat.mod_two_eq_zero_or_one l with hm | hm <;>
    cases h : α (l / 2) <;> simp_all


private theorem m7_p2_drop_false_lit {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (hl0 : k.cur_level = 0)
    {C : List Nat} {drop : Nat} (hC : (cnfOfClauses F_cur).EntailsClause (cnfClause C))
    (hlt : drop < 2 * k.cur_vars) (hff : k.vals[drop]?.getD 0#8 = 0xFF#8) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause (C.filter (· != drop))) := by
  have hneg := m6_vals_neg_entails hw hl0 hlt hff
  rw [CNF.entails_clause_def] at hC hneg ⊢
  intro α hα
  have hc := (clause_sat_cnfClause_iff α _).mp (hC α hα)
  have hn := (clause_sat_cnfClause_iff α _).mp (hneg α hα)
  obtain ⟨l', hl', hs'⟩ := hn
  rw [List.mem_singleton] at hl'; rw [hl'] at hs'
  rw [clause_sat_cnfClause_iff]
  obtain ⟨lc, hlc, hsc⟩ := hc
  refine ⟨lc, List.mem_filter.mpr ⟨hlc, bne_iff_ne.mpr fun heq => ?_⟩, hsc⟩
  rw [heq] at hsc; exact m7_p2_lit_compl_conflict hsc hs'

private theorem m7_p2_unsat_of_entails_nil {F : CNF Nat} (h : F.EntailsClause (cnfClause [])) :
    F.Unsat := by
  rw [CNF.unsat_iff_not_sat]; intro α hα
  have hs := (clause_sat_cnfClause_iff α []).mp ((CNF.entails_clause_def.mp h) α hα)
  obtain ⟨_, hm, _⟩ := hs; cases hm

private theorem m7_p2_sublist_map_nodup {xs ys : List Nat} (hsub : ys.Sublist xs)
    (hnd : (xs.map (· / 2)).Nodup) : (ys.map (· / 2)).Nodup :=
  (hsub.map (· / 2)).nodup hnd

private theorem m7_p2_zero_mem_arenaRefs3 {c : FullCfg} {F_cur : List (List Nat)}
    {k : FullCoreState} (ha : FullArenaClausesInv c F_cur k) (hpos : 0 < k.arena_len) :
    0 ∈ fullArenaClauseRefsCore k := by
  rcases ha.len_ok with hz | h3
  · omega
  · unfold fullArenaClauseRefsCore
    cases hal : k.arena_len with
    | zero => omega
    | succ n =>
      rw [fullArenaScanRefs]
      simp only [show 0 + 3 ≤ n + 1 by omega, ↓reduceIte]
      exact List.mem_cons_self

private theorem m7_p2_fullDenseInvW_with_lit_mark {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (h : FullDenseInvW c F0 F_cur s)
    {lm' : List (BitVec 8)} (hlm_len : lm'.length = 2 * c.max_vars)
    (hlm_clr : ∀ l < 2 * c.max_vars, lm'[l]?.getD 0#8 = 0#8) :
    FullDenseInvW c F0 F_cur { s with core := { s.core with lit_mark := lm' } } :=
  ⟨⟨{ h.1.core_ok with lit_mark_len := hlm_len }, h.1.scratch_ok⟩,
   { h.2.1 with
     arena := { h.2.1.arena with len_ok := h.2.1.arena.len_ok }
     watches := h.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) },
   ⟨h.2.2.1.1, hlm_clr⟩, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

private theorem m7_p2_fullDenseInvW_of_unwatch {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (h : FullDenseInvW c F0 F_cur s)
    {wvec' wstk' : List (BitVec 32)} {wu' : BitVec 64}
    (hlen' : ({ s with core :=
      { s.core with wvec := wvec', wstk := wstk', wusable := wu' } } :
      FullState).LengthsOk c)
    (hw' : ModeWatchesInv F_cur { s.core with wvec := wvec', wstk := wstk', wusable := wu' }) :
    FullDenseInvW c F0 F_cur
      { s with core := { s.core with wvec := wvec', wstk := wstk', wusable := wu' } } :=
  ⟨hlen', { h.2.1 with arena := { h.2.1.arena with len_ok := h.2.1.arena.len_ok }, watches := hw' },
   h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

private theorem m7_p2_fullDenseInvW_of_addBin {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s s' : FullState} (h : FullDenseInvW c F0 F_cur s)
    (hlen' : s'.LengthsOk c) (hw' : FullWitnessInv c F0 F_cur s'.core)
    (hmrk : s'.core.mrk = s.core.mrk) (hlm : s'.core.lit_mark = s.core.lit_mark)
    (har : s'.core.arena = s.core.arena) (hal : s'.core.arena_len = s.core.arena_len)
    (hcl : s'.core.cur_level = s.core.cur_level) (hdm : s'.core.dense_mode = s.core.dense_mode)
    (hll : s'.scratch.last_learned = s.scratch.last_learned)
    (hext : s'.scratch.extend_len = s.scratch.extend_len) :
    FullDenseInvW c F0 F_cur s' :=
  m6_fullDenseInvW_of_addUnit h hlen' hw' (hcl.trans h.2.2.2.2.2.1) hmrk hlm har hal hdm hll hext

private theorem m7_p2_fullDenseInvW_of_shrink {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (h : FullDenseInvW c F0 F_cur s)
    {cref nsz : Nat} (href : cref ∈ fullArenaClauseRefs s)
    (hnsz3 : 3 ≤ nsz) (hnsz_lt : nsz < fullArenaClauseSizeCore s.core cref)
    {arena' : List (BitVec 32)} (hal : arena'.length = c.arena_cap)
    (hhdr' : arena'[cref]? = some (if (fullArenaHdrCore s.core cref &&& 0x00800000#32) = 0#32
      then fullArenaHdrCore s.core cref ||| 0x00800000#32 else fullArenaHdrCore s.core cref))
    (hsz' : arena'[cref + 2]? = some (BitVec.ofNat 32 nsz))
    (hpad_new : (fullArenaHdrCore s.core cref &&& 0x00800000#32) = 0#32 →
      arena'[cref + 3 + fullArenaClauseSizeCore s.core cref - 1]? = some 0xFFFFFFFF#32 ∧
      ∀ i, cref + 3 + nsz ≤ i → i < cref + 3 + fullArenaClauseSizeCore s.core cref - 1 →
        arena'[i]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32)
    (hpad_old : (fullArenaHdrCore s.core cref &&& 0x00800000#32) ≠ 0#32 →
      ∀ i, cref + 3 + nsz ≤ i → i < cref + 3 + fullArenaClauseSizeCore s.core cref →
        arena'[i]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32)
    (hout : ∀ i, i < cref ∨ cref + 3 + fullArenaClauseSizeCore s.core cref ≤ i →
      arena'[i]? = s.core.arena[i]?)
    (hnew_lits_lt : ∀ l ∈ fullArenaClauseLitsCore { s.core with arena := arena' } cref,
      l < 2 * s.core.cur_vars)
    (hnew_nd : ((fullArenaClauseLitsCore { s.core with arena := arena' } cref).map (· / 2)).Nodup)
    (hnew_ent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause (fullArenaClauseLitsCore { s.core with arena := arena' } cref))) :
    let s' : FullState := { s with core := { s.core with arena := arena' } }
    FullDenseInvW c F0 F_cur s' ∧ fullArenaClauseRefs s' = fullArenaClauseRefs s := by
  intro s'
  obtain ⟨hlen_c', hrefs', hw', hoth'⟩ :=
    fullWitnessInv_shrink_at_root h.1.core_ok h.2.1 h.2.2.2.2.2.1 href hnsz3 hnsz_lt hal hhdr'
      hsz' hpad_new hpad_old hout hnew_lits_lt hnew_ent
  refine ⟨⟨⟨hlen_c', h.1.scratch_ok⟩, hw', h.2.2.1, fun r hr hng => ?_,
    ⟨fun i hi => by
      change _ = 0xFFFFFFFF#32 ∨ _ ∈ fullArenaClauseRefsCore s'.core
      rw [hrefs']; exact h.2.2.2.2.1.1 i hi, h.2.2.2.2.1.2⟩,
    h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩, hrefs'⟩
  change r ∈ fullArenaClauseRefsCore s'.core at hr; rw [hrefs'] at hr
  by_cases hrc : r = cref
  · subst hrc; exact hnew_nd
  · obtain ⟨hgb, hlits⟩ := hoth' r hr hrc
    change fullArenaClauseGarbCore s'.core r = false at hng; rw [hgb] at hng
    change ((fullArenaClauseLitsCore s'.core r).map (· / 2)).Nodup; rw [hlits]
    exact h.2.2.2.1 r hr hng


private theorem m7_p2_fwd_shrink_common {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hdw : FullDenseInvW c F0 F_cur s) {cref : BitVec 32} {hdr nsz sz : BitVec 32}
    (href : cref.toNat ∈ fullArenaClauseRefs s)
    (hsz3 : 3 ≤ nsz.toNat) (hsz_lt : nsz.toNat < sz.toNat)
    (hsz_eq : fullArenaClauseSizeCore s.core cref.toNat = sz.toNat)
    (hhdr_eq : fullArenaHdrCore s.core cref.toNat = hdr)
    (hcv_le : sz.toNat ≤ s.core.cur_vars)
    {tmp' ar_c : List (BitVec 32)} (htl' : tmp'.length = c.max_vars)
    (harc_l : ar_c.length = c.arena_cap)
    (hout_c : ∀ idx, idx < cref.toNat + 3 ∨ cref.toNat + 3 + nsz.toNat ≤ idx →
      ar_c[idx]? = s.core.arena[idx]?)
    (hcopy_c : ∀ k < nsz.toNat, ar_c[cref.toNat + 3 + k]? = tmp'[k]?)
    (hpad_orig : ∀ idx, cref.toNat + 3 + nsz.toNat ≤ idx → idx < cref.toNat + 3 + sz.toNat →
      s.core.arena[idx]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32) :
    let ar_w := (ar_c.set (cref.toNat + 2) nsz).set (cref.toNat + 1) 2#32
    ar_w.length = c.arena_cap ∧
    ar_w[cref.toNat + 2]? = some nsz ∧
    (∀ k < nsz.toNat, ar_w[cref.toNat + 3 + k]? = tmp'[k]?) ∧
    ar_w[cref.toNat]? = some hdr ∧
    (∀ idx, idx < cref.toNat ∨ cref.toNat + 3 + sz.toNat ≤ idx →
      ar_w[idx]? = s.core.arena[idx]?) ∧
    (∀ idx, cref.toNat + 3 + nsz.toNat ≤ idx → idx < cref.toNat + 3 + sz.toNat →
      ar_w[idx]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32) ∧
    fullArenaClauseLitsCore { s.core with arena := ar_w } cref.toNat =
      (tmp'.take nsz.toNat).map BitVec.toNat := by
  intro ar_w
  have hwf := hdw.2.1.arena.refs_wf cref.toNat href
  have har_len : cref.toNat < s.core.arena.length := by
    rw [hdw.1.core_ok.arena_len_arr]; have := hdw.1.core_ok.arena_len_le; omega
  have hcr2_arc : cref.toNat + 2 < ar_c.length := by
    rw [harc_l]; have := hdw.1.core_ok.arena_len_le; omega
  have hlen_w : ar_w.length = c.arena_cap := by
    dsimp only [ar_w]; rw [List.length_set, List.length_set, harc_l]
  have hsz_w : ar_w[cref.toNat + 2]? = some nsz := by
    dsimp only [ar_w]; rw [List.getElem?_set_ne (by omega), List.getElem?_set_self hcr2_arc]
  have hget_w : ∀ k < nsz.toNat, ar_w[cref.toNat + 3 + k]? = tmp'[k]? := fun k hk => by
    dsimp only [ar_w]; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
    exact hcopy_c k hk
  have hhdr_w : ar_w[cref.toNat]? = some hdr := by
    dsimp only [ar_w]
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      hout_c cref.toNat (Or.inl (by omega)), List.getElem?_eq_getElem har_len]
    unfold fullArenaHdrCore at hhdr_eq
    rw [List.getElem?_eq_getElem har_len, Option.getD_some] at hhdr_eq; rw [hhdr_eq]
  have hout_w : ∀ idx, idx < cref.toNat ∨ cref.toNat + 3 + sz.toNat ≤ idx →
      ar_w[idx]? = s.core.arena[idx]? := fun idx hidx => by
    dsimp only [ar_w]; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
    exact hout_c idx (by omega)
  have hpad_w : ∀ idx, cref.toNat + 3 + nsz.toNat ≤ idx → idx < cref.toNat + 3 + sz.toNat →
      ar_w[idx]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := fun idx hi1 hi2 => by
    dsimp only [ar_w]
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      hout_c idx (by omega)]
    exact hpad_orig idx hi1 hi2
  have hlits_w : fullArenaClauseLitsCore { s.core with arena := ar_w } cref.toNat =
      (tmp'.take nsz.toNat).map BitVec.toNat := by
    unfold fullArenaClauseLitsCore fullArenaClauseSizeCore
    rw [hsz_w, Option.getD_some]
    apply List.ext_getElem
    · simp only [List.length_map, List.length_take, List.length_drop, hlen_w, htl']
      have := hdw.1.core_ok.cur_vars_le; have := hdw.1.core_ok.arena_len_le; omega
    · intro k hk1 hk2
      simp only [List.getElem_map, List.getElem_take, List.getElem_drop]
      have hk_lt : k < nsz.toNat := by
        simp only [List.length_map, List.length_take, htl'] at hk2
        have := hdw.1.core_ok.cur_vars_le; omega
      have h1 := hget_w k hk_lt
      rw [List.getElem?_eq_getElem (by
          rw [hlen_w]; have := hdw.1.core_ok.arena_len_le; omega),
        List.getElem?_eq_getElem (by
          rw [htl']; have := hdw.1.core_ok.cur_vars_le; omega)] at h1
      exact congrArg BitVec.toNat (Option.some.inj h1)
  exact ⟨hlen_w, hsz_w, hget_w, hhdr_w, hout_w, hpad_w, hlits_w⟩

private theorem m7_p2_fwd_shrink_step {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hdw : FullDenseInvW c F0 F_cur s) {cref hdr nsz sz : BitVec 32}
    (href : cref.toNat ∈ fullArenaClauseRefs s)
    (hngt : fullArenaClauseGarb s cref.toNat = false)
    (hsz3 : 3 ≤ nsz.toNat) (hsz_lt : nsz.toNat < sz.toNat)
    (hsz_eq : fullArenaClauseSizeCore s.core cref.toNat = sz.toNat)
    (hhdr_eq : fullArenaHdrCore s.core cref.toNat = hdr)
    (hcv_le : sz.toNat ≤ s.core.cur_vars)
    {tmp' ar_c : List (BitVec 32)} (htl' : tmp'.length = c.max_vars)
    (harc_l : ar_c.length = c.arena_cap)
    (hout_c : ∀ idx, idx < cref.toNat + 3 ∨ cref.toNat + 3 + nsz.toNat ≤ idx →
      ar_c[idx]? = s.core.arena[idx]?)
    (hcopy_c : ∀ k < nsz.toNat, ar_c[cref.toNat + 3 + k]? = tmp'[k]?)
    (htmp_lt : ∀ l ∈ (tmp'.take nsz.toNat).map BitVec.toNat, l < 2 * s.core.cur_vars)
    (htmp_nd : (((tmp'.take nsz.toNat).map BitVec.toNat).map (· / 2)).Nodup)
    (htmp_ent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((tmp'.take nsz.toNat).map BitVec.toNat)))
    (hpad_orig : ∀ idx, cref.toNat + 3 + nsz.toNat ≤ idx → idx < cref.toNat + 3 + sz.toNat →
      s.core.arena[idx]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32) :
    let ar_w := (ar_c.set (cref.toNat + 2) nsz).set (cref.toNat + 1) 2#32
    let ar_fin := if (hdr &&& 0x00800000#32) = 0#32 then
      (ar_w.set (cref.toNat + 3 + sz.toNat - 1) 0xFFFFFFFF#32).set cref.toNat
        (hdr ||| 0x00800000#32) else ar_w
    let hdr_fin := if (hdr &&& 0x00800000#32) = 0#32 then hdr ||| 0x00800000#32 else hdr
    let sx : FullState := { s with core := { s.core with arena := ar_fin } }
    FullDenseInvW c F0 F_cur sx ∧
    fullArenaClauseRefs sx = fullArenaClauseRefs s ∧
    hdr_fin = fullArenaHdr sx cref.toNat ∧
    fullArenaClauseSizeCore sx.core cref.toNat = nsz.toNat ∧
    fullArenaClauseGarb sx cref.toNat = false := by
  intro ar_w ar_fin hdr_fin sx
  obtain ⟨hlen_w, hsz_w, hget_w, hhdr_w, hout_w, hpad_w, hlits_w⟩ :=
    m7_p2_fwd_shrink_common hdw href hsz3 hsz_lt hsz_eq hhdr_eq hcv_le htl' harc_l hout_c hcopy_c
      hpad_orig
  have hwf := hdw.2.1.arena.refs_wf cref.toNat href
  have hng' : (hdr &&& 0x00080000#32 != 0#32) = false := by
    change (fullArenaHdrCore s.core cref.toNat &&& 0x00080000#32 != 0#32) = false at hngt
    rwa [hhdr_eq] at hngt
  by_cases hsh0 : (hdr &&& 0x00800000#32) = 0#32
  · have hsent_ar : cref.toNat + 3 + sz.toNat - 1 < ar_w.length := by
      rw [hlen_w]; have := hdw.1.core_ok.arena_len_le; omega
    have hcr_ars : cref.toNat <
        (ar_w.set (cref.toNat + 3 + sz.toNat - 1) 0xFFFFFFFF#32).length := by
      rw [List.length_set, hlen_w]; have := hdw.1.core_ok.arena_len_le; omega
    have har_eq : ar_fin =
        (ar_w.set (cref.toNat + 3 + sz.toNat - 1) 0xFFFFFFFF#32).set cref.toNat
          (hdr ||| 0x00800000#32) := ite_eq_left hsh0
    have hhdr_eq_fin : hdr_fin = hdr ||| 0x00800000#32 := ite_eq_left hsh0
    have hlen_s : ar_fin.length = c.arena_cap := by
      rw [har_eq, List.length_set, List.length_set, hlen_w]
    have hsz_s : ar_fin[cref.toNat + 2]? = some nsz := by
      rw [har_eq, List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]; exact hsz_w
    have hhdr_s : ar_fin[cref.toNat]? = some (hdr ||| 0x00800000#32) := by
      rw [har_eq, List.getElem?_set_self hcr_ars]
    have hlits_s : fullArenaClauseLitsCore { s.core with arena := ar_fin } cref.toNat =
        (tmp'.take nsz.toNat).map BitVec.toNat := by
      rw [← hlits_w]
      dsimp only [fullArenaClauseLitsCore, fullArenaClauseSizeCore]
      rw [hsz_s, hsz_w, Option.getD_some]
      congr 1
      have hsub : ∀ j < nsz.toNat, ar_fin[cref.toNat + 3 + j]? = ar_w[cref.toNat + 3 + j]? :=
        fun j hj => by
          rw [har_eq, List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
      have hmin : min nsz.toNat (ar_fin.length - (cref.toNat + 3)) = nsz.toNat := by
        rw [hlen_s]; have := hdw.1.core_ok.arena_len_le; omega
      have hmin_w : min nsz.toNat (ar_w.length - (cref.toNat + 3)) = nsz.toNat := by
        rw [hlen_w]; have := hdw.1.core_ok.arena_len_le; omega
      apply List.ext_getElem
      · simp only [List.length_take, List.length_drop]; omega
      · intro k hk1 hk2
        simp only [List.getElem_take, List.getElem_drop]
        have hk_lt : k < nsz.toNat := by
          simp only [List.length_take, List.length_drop] at hk1; omega
        have hopt := hsub k hk_lt
        rw [List.getElem?_eq_getElem (by rw [hlen_s]; have := hdw.1.core_ok.arena_len_le; omega),
          List.getElem?_eq_getElem (by rw [hlen_w]; have := hdw.1.core_ok.arena_len_le; omega)]
          at hopt
        exact Option.some.inj hopt
    have hshr := m7_p2_fullDenseInvW_of_shrink (arena' := ar_fin) hdw href hsz3 (by omega) hlen_s
      (by rw [hhdr_eq, ite_eq_left hsh0]; exact hhdr_s)
      (by rw [BitVec.ofNat_toNat]; exact hsz_s)
      (fun _ => ⟨by
        rw [har_eq, List.getElem?_set_ne (by omega), hsz_eq, List.getElem?_set_self hsent_ar],
        fun idx hi1 hi2 => by
          rw [har_eq, List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
          exact hpad_w idx hi1 (by omega)⟩)
      (fun h => absurd hsh0 (by rw [← hhdr_eq]; exact h))
      (fun idx hidx => by
        rw [har_eq, List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
        exact hout_w idx (by omega))
      (by rw [hlits_s]; exact htmp_lt) (by rw [hlits_s]; exact htmp_nd)
      (by rw [hlits_s]; exact htmp_ent)
    have hhdr_fin : hdr_fin = fullArenaHdr sx cref.toNat := by
      unfold fullArenaHdr fullArenaHdrCore; dsimp only [sx]
      rw [hhdr_eq_fin, hhdr_s, Option.getD_some]
    have hng_fin : fullArenaClauseGarb sx cref.toNat = false := by
      unfold fullArenaClauseGarb fullArenaClauseGarbCore
      change (fullArenaHdr sx cref.toNat &&& 0x00080000#32 != 0#32) = false
      rw [← hhdr_fin, hhdr_eq_fin]
      have h0 : ((hdr ||| 0x00800000#32) &&& 0x00080000#32) = (hdr &&& 0x00080000#32) := by
        ext i hi; simp only [BitVec.getElem_and, BitVec.getElem_or]
        have hd : ((0x00800000#32 &&& 0x00080000#32) : BitVec 32)[i] = false := by
          have : (0x00800000#32 &&& 0x00080000#32) = 0#32 := by decide
          rw [this]; simp
        simp only [BitVec.getElem_and] at hd; rw [Bool.and_or_distrib_right, hd, Bool.or_false]
      rwa [h0]
    exact ⟨hshr.1, hshr.2, hhdr_fin, by unfold fullArenaClauseSizeCore; rw [hsz_s]; rfl, hng_fin⟩
  · have har_eq : ar_fin = ar_w := ite_eq_right hsh0
    have hhdr_eq_fin : hdr_fin = hdr := ite_eq_right hsh0
    have hshr := m7_p2_fullDenseInvW_of_shrink (arena' := ar_fin) hdw href hsz3 (by omega)
      (by rw [har_eq]; exact hlen_w)
      (by rw [hhdr_eq, ite_eq_right hsh0, har_eq]; exact hhdr_w)
      (by rw [BitVec.ofNat_toNat, har_eq]; exact hsz_w)
      (fun h => absurd (by rw [← hhdr_eq]; exact h) hsh0)
      (fun _ idx hi1 hi2 => by rw [har_eq]; exact hpad_w idx hi1 (by omega))
      (fun idx hidx => by rw [har_eq]; exact hout_w idx (by omega))
      (by rw [har_eq, hlits_w]; exact htmp_lt) (by rw [har_eq, hlits_w]; exact htmp_nd)
      (by rw [har_eq, hlits_w]; exact htmp_ent)
    have hhdr_fin : hdr_fin = fullArenaHdr sx cref.toNat := by
      unfold fullArenaHdr fullArenaHdrCore; dsimp only [sx]
      rw [hhdr_eq_fin, har_eq, hhdr_w, Option.getD_some]
    have hng_fin : fullArenaClauseGarb sx cref.toNat = false := by
      unfold fullArenaClauseGarb fullArenaClauseGarbCore
      change (fullArenaHdr sx cref.toNat &&& 0x00080000#32 != 0#32) = false
      rwa [← hhdr_fin, hhdr_eq_fin]
    exact ⟨hshr.1, hshr.2, hhdr_fin,
      by unfold fullArenaClauseSizeCore; dsimp only [sx]; rw [har_eq, hsz_w]; rfl, hng_fin⟩

/-! ## 3. `full_fwd_check_cl_m7` -/

private theorem m7_p2_fwd_lm_set_iff {c : FullCfg} {k : FullCoreState} {lits : List Nat}
    {lm : List (BitVec 8)} {li : BitVec 32} {i : Nat}
    (hlm : lm.length = 2 * c.max_vars) (_hcv : k.cur_vars ≤ c.max_vars)
    (_hli_lt : li.toNat < 2 * k.cur_vars) (hi_lt : i < lits.length)
    (hget : lits[i]'hi_lt = li.toNat)
    (htk : ∀ x < 2 * c.max_vars, lm[x]?.getD 0#8 ≠ 0#8 ↔ x ∈ lits.take i) :
    ∀ x < 2 * c.max_vars,
      (lm.set li.toNat 1#8)[x]?.getD 0#8 ≠ 0#8 ↔ x ∈ lits.take (i + 1) := by
  intro x hx
  rw [List.take_succ_eq_append_getElem hi_lt, hget, List.mem_append, List.mem_singleton]
  by_cases hxe : x = li.toNat
  · subst hxe; rw [List.getElem?_set_self (by omega), Option.getD_some]; simp
  · rw [List.getElem?_set_ne (Ne.symm hxe), htk x hx]; simp [hxe]

private theorem m7_p2_fwd_lm_clear_step {c : FullCfg} {lits : List Nat} {lm : List (BitVec 8)}
    {li : BitVec 32} {i : Nat} (hlm : lm.length = 2 * c.max_vars) (hi_lt : i < lits.length)
    (hget : lits[i]'hi_lt = li.toNat)
    (hrem : ∀ x < 2 * c.max_vars, lm[x]?.getD 0#8 ≠ 0#8 → x ∈ lits.drop i) :
    ∀ x < 2 * c.max_vars,
      (lm.set li.toNat 0#8)[x]?.getD 0#8 ≠ 0#8 → x ∈ lits.drop (i + 1) := by
  intro x hx hnz
  by_cases hxe : x = li.toNat
  · subst hxe
    have hlt_x : li.toNat < lm.length := by omega
    rw [List.getElem?_set_self hlt_x, Option.getD_some] at hnz
    exact absurd rfl hnz
  · rw [List.getElem?_set_ne (Ne.symm hxe)] at hnz
    have hmem := hrem x hx hnz
    rw [List.drop_eq_getElem_cons hi_lt, hget, List.mem_cons] at hmem
    exact hmem.resolve_left hxe

private theorem m7_p2_fwd_cl_lits_len {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hdw : FullDenseInvW c F0 F_cur s) {cref : Nat}
    (href : cref ∈ fullArenaClauseRefs s) {sz : Nat}
    (hsz : sz = fullArenaClauseSizeCore s.core cref) :
    (fullArenaClauseLits s cref).length = sz := by
  have hwf := hdw.2.1.arena.refs_wf cref href
  unfold fullArenaClauseLits fullArenaClauseLitsCore
  simp only [List.length_map, List.length_take, List.length_drop]
  rw [hdw.1.core_ok.arena_len_arr]; have := hdw.1.core_ok.arena_len_le; omega

private theorem m7_p2_fwd_cl_lit_at {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hdw : FullDenseInvW c F0 F_cur s) {cref : Nat}
    (href : cref ∈ fullArenaClauseRefs s) {sz i : Nat}
    (hsz : sz = fullArenaClauseSizeCore s.core cref) (hi : i < sz) :
    i < (fullArenaClauseLits s cref).length ∧
    (fullArenaClauseLits s cref)[i]'(by
      rw [m7_p2_fwd_cl_lits_len hdw href hsz]; exact hi) =
      (s.core.arena[cref + 3 + i]'(by
        have hwf := hdw.2.1.arena.refs_wf cref href
        rw [hdw.1.core_ok.arena_len_arr]; have := hdw.1.core_ok.arena_len_le; omega)).toNat := by
  have hlen := m7_p2_fwd_cl_lits_len hdw href hsz
  refine ⟨by rw [hlen]; exact hi, ?_⟩
  unfold fullArenaClauseLits fullArenaClauseLitsCore
  simp only [List.getElem_map, List.getElem_take, List.getElem_drop]


private theorem m7_p2_fwd_nsz2_garb_post {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s_b : FullState} (hdw_b : FullDenseInvW c F0 F_cur s_b) {cref sz hdr : BitVec 32}
    (href : cref.toNat ∈ fullArenaClauseRefs s_b)
    (hsz_b : fullArenaClauseSizeCore s_b.core cref.toNat = sz.toNat)
    (hhdr_b : fullArenaHdr s_b cref.toNat = hdr)
    {tmp' : List (BitVec 32)} (h0_tmp : 0 < tmp'.length) (h1_tmp : 1 < tmp'.length) :
    let ar1 := s_b.core.arena.set (cref.setWidth 64).toNat
      ((hdr ||| 0x00080000#32) ||| 0x01000000#32)
    let ar2 := ar1.set (cref.setWidth 64 + 3#64).toNat (tmp'[0]'h0_tmp)
    let ar3 := ar2.set (cref.setWidth 64 + 4#64).toNat (tmp'[1]'h1_tmp)
    let ag' := s_b.core.arena_garbage + 3#64 + sz.setWidth 64
    let smg : FullState := { s_b with core := { s_b.core with arena := ar3, arena_garbage := ag' } }
    FullDenseInvW c F0 F_cur smg ∧ fullArenaClauseRefs smg = fullArenaClauseRefs s_b := by
  intro ar1 ar2 ar3 ag' smg
  have harc := c.harena; unfold dimacsBound at harc
  have hwf := hdw_b.2.1.arena.refs_wf cref.toNat href
  have := hdw_b.1.core_ok.arena_len_le
  have har_len : cref.toNat < s_b.core.arena.length := by
    rw [hdw_b.1.core_ok.arena_len_arr]; omega
  refine m6_fullDenseInvW_markGarb hdw_b href (arena' := ar3) (ag' := ag')
    (by simp [ar3, ar2, ar1, hdw_b.1.core_ok.arena_len_arr])
    (Or.inr (by
      dsimp only [ar3, ar2, ar1]
      rw [List.getElem?_set_ne (by c0_bound), List.getElem?_set_ne (by c0_bound),
        m6_zext32_toNat, hhdr_b]
      exact List.getElem?_set_self har_len))
    (fun idx hne hout => by
      dsimp only [ar3, ar2, ar1]
      rw [List.getElem?_set_ne (by c0_bound), List.getElem?_set_ne (by c0_bound),
        m6_zext32_toNat, List.getElem?_set_ne hne.symm])

private theorem m7_p2_fwd_nsz3_sub_post {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {sf' : FullState} {ar_s : List (BitVec 32)} {cref hdr_s nsz : BitVec 32}
    (hdws : FullDenseInvW c F0 F_cur { sf' with core := { sf'.core with arena := ar_s } })
    (href_s : cref.toNat ∈ fullArenaClauseRefs
      { sf' with core := { sf'.core with arena := ar_s } })
    (hhdrs : hdr_s = fullArenaHdr { sf' with core := { sf'.core with arena := ar_s } } cref.toNat)
    (hszs : fullArenaClauseSizeCore { sf'.core with arena := ar_s } cref.toNat = nsz.toNat)
    (hngs : fullArenaClauseGarb { sf' with core := { sf'.core with arena := ar_s } } cref.toNat =
      false) :
    let v_sub := hdr_s ||| 0x01000000#32
    let s_sub : FullState :=
      { sf' with core := { sf'.core with arena := ar_s.set (cref.setWidth 64).toNat v_sub } }
    FullDenseInvW c F0 F_cur s_sub ∧
    fullArenaClauseRefs s_sub =
      fullArenaClauseRefs { sf' with core := { sf'.core with arena := ar_s } } ∧
    v_sub = fullArenaHdr s_sub cref.toNat ∧
    nsz.toNat = fullArenaClauseSizeCore s_sub.core cref.toNat ∧
    fullArenaClauseGarb s_sub cref.toNat = false := by
  intro v_sub s_sub
  have harc := c.harena; unfold dimacsBound at harc
  have hwf := hdws.2.1.arena.refs_wf cref.toNat href_s
  have := hdws.1.core_ok.arena_len_le
  have hidx_eq : (cref.setWidth 64).toNat = cref.toNat := m6_zext32_toNat cref
  have hcr_ars : cref.toNat < ar_s.length := by
    change cref.toNat < ({ sf'.core with arena := ar_s } : FullCoreState).arena.length
    rw [hdws.1.core_ok.arena_len_arr]; omega
  have hbo := m6_bit24_or_pres hdr_s
  have hset := m6_fullDenseInvW_set_hdr_bit24 hdws href_s (v' := v_sub)
    (by rw [← hhdrs]; exact hbo.1) (by rw [← hhdrs]; exact hbo.2)
  have hper := hset.2.2 cref.toNat href_s
  have hdw_sub : FullDenseInvW c F0 F_cur s_sub := by simpa only [s_sub, hidx_eq] using hset.1
  have hrefs_sub : fullArenaClauseRefs s_sub =
      fullArenaClauseRefs { sf' with core := { sf'.core with arena := ar_s } } := by
    simpa only [s_sub, hidx_eq] using hset.2.1
  have hhdr_sub : v_sub = fullArenaHdr s_sub cref.toNat := by
    unfold fullArenaHdr fullArenaHdrCore; dsimp only [s_sub]
    rw [hidx_eq, List.getElem?_set_self hcr_ars, Option.getD_some]
  have hsz_sub : fullArenaClauseSizeCore s_sub.core cref.toNat = nsz.toNat := by
    simpa only [s_sub, hidx_eq] using hper.1.trans hszs
  have hng_sub : fullArenaClauseGarb s_sub cref.toNat = false := by
    simpa only [s_sub, hidx_eq] using hper.2.1.trans hngs
  exact ⟨hdw_sub, hrefs_sub, hhdr_sub, hsz_sub.symm, hng_sub⟩

private theorem m7_p2_fwd_pad_orig {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {sf' st : FullState} (hdwt : FullDenseInvW c F0 F_cur st)
    (hdw_f' : FullDenseInvW c F0 F_cur sf') {cref nsz sz : BitVec 32}
    (href_t : cref.toNat ∈ fullArenaClauseRefs st)
    (hngt : fullArenaClauseGarb st cref.toNat = false)
    (hszt : sz.toNat = fullArenaClauseSizeCore st.core cref.toNat)
    (har : sf'.core.arena = st.core.arena) :
    ∀ idx, cref.toNat + 3 + nsz.toNat ≤ idx → idx < cref.toNat + 3 + sz.toNat →
      sf'.core.arena[idx]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := by
  intro idx hi1 hi2
  have hwf := hdwt.2.1.arena.refs_wf cref.toNat href_t
  have := hdwt.1.core_ok.arena_len_le
  have hlt_i : idx < sf'.core.arena.length := by rw [hdw_f'.1.core_ok.arena_len_arr]; omega
  have hlt_t : cref.toNat + 3 + (idx - (cref.toNat + 3)) < st.core.arena.length := by
    rw [hdwt.1.core_ok.arena_len_arr]; omega
  have hmem : (sf'.core.arena[idx]'hlt_i).toNat ∈
      fullArenaClauseLitsCore st.core cref.toNat := by
    rw [mem_fullArenaClauseLitsCore_iff (by rw [hdwt.1.core_ok.arena_len_arr]; omega)]
    refine ⟨idx - (cref.toNat + 3), by omega, ?_⟩
    have hopt : some (sf'.core.arena[idx]'hlt_i) =
        some (st.core.arena[cref.toNat + 3 + (idx - (cref.toNat + 3))]'hlt_t) := by
      rw [← List.getElem?_eq_getElem hlt_i, ← List.getElem?_eq_getElem hlt_t, har]
      exact congrArg (st.core.arena[·]?) (by omega)
    exact congrArg BitVec.toNat (Option.some.inj hopt.symm)
  have hlt2 := hdwt.2.1.arena.lits_lt cref.toNat href_t hngt _ hmem
  rw [List.getElem?_eq_getElem hlt_i, Option.getD_some]
  intro heq
  have hto : (sf'.core.arena[idx]'hlt_i).toNat = 4294967295 := congrArg BitVec.toNat heq
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have := hdwt.1.core_ok.cur_vars_le; omega

private theorem m7_p2_copy_iter {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {st : FullState} (hdwt : FullDenseInvW c F0 F_cur st)
    {cref nsz ic : BitVec 32} (href_t : cref.toNat ∈ fullArenaClauseRefs st)
    {sz : Nat} (hsz : sz = fullArenaClauseSizeCore st.core cref.toNat) (hnsz_lt : nsz.toNat < sz)
    {ar0 tmp' ar_c : List (BitVec 32)}
    (harc_l : ar_c.length = c.arena_cap) (_htl' : tmp'.length = c.max_vars)
    (hout_c : ∀ idx, idx < cref.toNat + 3 ∨ cref.toNat + 3 + ic.toNat ≤ idx →
      ar_c[idx]? = ar0[idx]?)
    (hcopy_c : ∀ k < ic.toNat, ar_c[cref.toNat + 3 + k]? = tmp'[k]?)
    (hic_lt : ic.toNat < nsz.toNat)
    (hic_tmp : (ic.setWidth 64).toNat < tmp'.length)
    (hic_ar : (cref.setWidth 64 + 3#64 + ic.setWidth 64).toNat < ar_c.length)
    (hic1 : (ic + 1#32).toNat = ic.toNat + 1) :
    let ar_c' := ar_c.set (cref.setWidth 64 + 3#64 + ic.setWidth 64).toNat
      (tmp'[(ic.setWidth 64).toNat]'hic_tmp)
    ar_c'.length = c.arena_cap ∧ (ic + 1#32).toNat ≤ nsz.toNat ∧
    (∀ idx, idx < cref.toNat + 3 ∨ cref.toNat + 3 + (ic + 1#32).toNat ≤ idx →
      ar_c'[idx]? = ar0[idx]?) ∧
    (∀ k < (ic + 1#32).toNat, ar_c'[cref.toNat + 3 + k]? = tmp'[k]?) := by
  intro ar_c'
  have hwf := hdwt.2.1.arena.refs_wf cref.toNat href_t
  have := hdwt.1.core_ok.arena_len_le
  have harc_c := c.harena; unfold dimacsBound at harc_c
  refine ⟨by simp [ar_c', harc_l], by omega, fun idx hidx => ?_, fun idx hidx => ?_⟩
  · dsimp only [ar_c']
    rw [List.getElem?_set_ne (by c0_bound)]
    exact hout_c idx (by omega)
  · dsimp only [ar_c']
    rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp (hic1 ▸ hidx)) with h | h
    · rw [List.getElem?_set_ne (by c0_bound)]
      exact hcopy_c idx h
    · subst h
      have heq_idx : cref.toNat + 3 + ic.toNat =
          (cref.setWidth 64 + 3#64 + ic.setWidth 64).toNat := by c0_bound
      rw [heq_idx, List.getElem?_set_self hic_ar,
        List.getElem?_eq_getElem (by rw [m6_zext32_toNat] at hic_tmp; exact hic_tmp)]
      exact congrArg some (m6_getElem_congr (m6_zext32_toNat ic) _ _)

private theorem m7_p2_check_cl_shrink0 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {sf' : FullState} (hdw_f' : FullDenseInvW c F0 F_cur sf')
    {cref hdr nsz sz : BitVec 32} (href_u : cref.toNat ∈ fullArenaClauseRefs sf')
    (hngt_sf' : fullArenaClauseGarb sf' cref.toNat = false)
    (hnsz3 : 3 ≤ nsz.toNat) (hnsz_lt_sz : nsz.toNat < sz.toNat)
    (hsz_sf' : fullArenaClauseSizeCore sf'.core cref.toNat = sz.toNat)
    (hhdr_sf' : fullArenaHdrCore sf'.core cref.toNat = hdr)
    (hcv_f' : sz.toNat ≤ sf'.core.cur_vars)
    {tmp' ar_c : List (BitVec 32)} (htl' : tmp'.length = c.max_vars)
    (harc_l : ar_c.length = c.arena_cap)
    (hout_c : ∀ idx, idx < cref.toNat + 3 ∨ cref.toNat + 3 + nsz.toNat ≤ idx →
      ar_c[idx]? = sf'.core.arena[idx]?)
    (hcopy_c : ∀ k < nsz.toNat, ar_c[cref.toNat + 3 + k]? = tmp'[k]?)
    (htmp_lt : ∀ l ∈ (tmp'.take nsz.toNat).map BitVec.toNat, l < 2 * sf'.core.cur_vars)
    (htmp_nd : (((tmp'.take nsz.toNat).map BitVec.toNat).map (· / 2)).Nodup)
    (htmp_ent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((tmp'.take nsz.toNat).map BitVec.toNat)))
    (hpad_orig : ∀ idx, cref.toNat + 3 + nsz.toNat ≤ idx → idx < cref.toNat + 3 + sz.toNat →
      sf'.core.arena[idx]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32)
    (hsh0 : (hdr &&& 0x00800000#32) = 0#32)
    {i2 i1 isent i0 : Nat} {v2 vfff v80 : BitVec 32}
    (hi2 : i2 = cref.toNat + 2) (hi1 : i1 = cref.toNat + 1)
    (hisent : isent = cref.toNat + 3 + sz.toNat - 1) (hi0 : i0 = cref.toNat)
    (hv2 : v2 = 2#32) (hvfff : vfff = 0xFFFFFFFF#32) (hv80 : v80 = 0x00800000#32) :
    let ar_s := (((ar_c.set i2 nsz).set i1 v2).set isent vfff).set i0 (hdr ||| v80)
    let sx : FullState := { sf' with core := { sf'.core with arena := ar_s } }
    FullDenseInvW c F0 F_cur sx ∧ fullArenaClauseRefs sx = fullArenaClauseRefs sf' ∧
    hdr ||| 0x00800000#32 = fullArenaHdr sx cref.toNat ∧
    fullArenaClauseSizeCore sx.core cref.toNat = nsz.toNat ∧
    fullArenaClauseGarb sx cref.toNat = false := by
  subst hi2 hi1 hisent hi0 hv2 hvfff hv80
  have hstep := m7_p2_fwd_shrink_step hdw_f' href_u hngt_sf' hnsz3 hnsz_lt_sz hsz_sf' hhdr_sf'
    hcv_f' htl' harc_l hout_c hcopy_c htmp_lt htmp_nd htmp_ent hpad_orig
  simp only [hsh0, ↓reduceIte] at hstep
  exact hstep

private theorem m7_p2_check_cl_shrink1 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {sf' : FullState} (hdw_f' : FullDenseInvW c F0 F_cur sf')
    {cref hdr nsz sz : BitVec 32} (href_u : cref.toNat ∈ fullArenaClauseRefs sf')
    (hngt_sf' : fullArenaClauseGarb sf' cref.toNat = false)
    (hnsz3 : 3 ≤ nsz.toNat) (hnsz_lt_sz : nsz.toNat < sz.toNat)
    (hsz_sf' : fullArenaClauseSizeCore sf'.core cref.toNat = sz.toNat)
    (hhdr_sf' : fullArenaHdrCore sf'.core cref.toNat = hdr)
    (hcv_f' : sz.toNat ≤ sf'.core.cur_vars)
    {tmp' ar_c : List (BitVec 32)} (htl' : tmp'.length = c.max_vars)
    (harc_l : ar_c.length = c.arena_cap)
    (hout_c : ∀ idx, idx < cref.toNat + 3 ∨ cref.toNat + 3 + nsz.toNat ≤ idx →
      ar_c[idx]? = sf'.core.arena[idx]?)
    (hcopy_c : ∀ k < nsz.toNat, ar_c[cref.toNat + 3 + k]? = tmp'[k]?)
    (htmp_lt : ∀ l ∈ (tmp'.take nsz.toNat).map BitVec.toNat, l < 2 * sf'.core.cur_vars)
    (htmp_nd : (((tmp'.take nsz.toNat).map BitVec.toNat).map (· / 2)).Nodup)
    (htmp_ent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((tmp'.take nsz.toNat).map BitVec.toNat)))
    (hpad_orig : ∀ idx, cref.toNat + 3 + nsz.toNat ≤ idx → idx < cref.toNat + 3 + sz.toNat →
      sf'.core.arena[idx]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32)
    (hsh1 : (hdr &&& 0x00800000#32) ≠ 0#32)
    {i2 i1 : Nat} {v2 : BitVec 32} (hi2 : i2 = cref.toNat + 2) (hi1 : i1 = cref.toNat + 1)
    (hv2 : v2 = 2#32) :
    let ar_w := (ar_c.set i2 nsz).set i1 v2
    let sx : FullState := { sf' with core := { sf'.core with arena := ar_w } }
    FullDenseInvW c F0 F_cur sx ∧ fullArenaClauseRefs sx = fullArenaClauseRefs sf' ∧
    hdr = fullArenaHdr sx cref.toNat ∧
    fullArenaClauseSizeCore sx.core cref.toNat = nsz.toNat ∧
    fullArenaClauseGarb sx cref.toNat = false := by
  subst hi2 hi1 hv2
  have hstep := m7_p2_fwd_shrink_step hdw_f' href_u hngt_sf' hnsz3 hnsz_lt_sz hsz_sf' hhdr_sf'
    hcv_f' htl' harc_l hout_c hcopy_c htmp_lt htmp_nd htmp_ent hpad_orig
  simp only [hsh1, ↓reduceIte] at hstep
  exact hstep

private theorem m7_p2_unmark_iter {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {st : FullState} (hdwt : FullDenseInvW c F0 F_cur st) {cref sz : BitVec 32}
    (href_t : cref.toNat ∈ fullArenaClauseRefs st)
    (hngt : fullArenaClauseGarb st cref.toNat = false)
    (hszt : sz.toNat = fullArenaClauseSizeCore st.core cref.toNat)
    {lm_u : List (BitVec 8)} (hlmu : lm_u.length = 2 * c.max_vars)
    {iu : BitVec 32} (hiu_lt : iu.toNat < sz.toNat)
    (hrem_lm : ∀ x < 2 * c.max_vars,
      lm_u[x]?.getD 0#8 ≠ 0#8 → x ∈ (fullArenaClauseLits st cref.toNat).drop iu.toNat) :
    ∃ hcri : (cref.setWidth 64 + 3#64 + iu.setWidth 64).toNat < st.core.arena.length,
      let li := st.core.arena[(cref.setWidth 64 + 3#64 + iu.setWidth 64).toNat]'hcri
      (li.setWidth 64).toNat < lm_u.length ∧ (iu + 1#32).toNat = iu.toNat + 1 ∧
      ∀ x < 2 * c.max_vars,
        (lm_u.set (li.setWidth 64).toNat 0#8)[x]?.getD 0#8 ≠ 0#8 →
          x ∈ (fullArenaClauseLits st cref.toNat).drop (iu + 1#32).toNat := by
  have harc := c.harena; unfold dimacsBound at harc
  have hwf := hdwt.2.1.arena.refs_wf cref.toNat href_t
  have := hdwt.1.core_ok.arena_len_le
  have hcri : (cref.setWidth 64 + 3#64 + iu.setWidth 64).toNat < st.core.arena.length := by
    rw [hdwt.1.core_ok.arena_len_arr]; c0_bound
  refine ⟨hcri, ?_⟩
  let li := st.core.arena[(cref.setWidth 64 + 3#64 + iu.setWidth 64).toNat]'hcri
  have hli_at := m7_p2_fwd_cl_lit_at hdwt href_t hszt hiu_lt
  have hli_eq : (fullArenaClauseLits st cref.toNat)[iu.toNat]'hli_at.1 = li.toNat :=
    hli_at.2.trans (congrArg BitVec.toNat (m6_getElem_congr (by c0_bound) _ _))
  have hli_lt : li.toNat < 2 * st.core.cur_vars :=
    hdwt.2.1.arena.lits_lt cref.toNat href_t hngt _ (hli_eq ▸ List.getElem_mem hli_at.1)
  have hli_lm : (li.setWidth 64).toNat < lm_u.length := by
    rw [hlmu, m6_zext32_toNat]; have := hdwt.1.core_ok.cur_vars_le; omega
  have hiu1 : (iu + 1#32).toNat = iu.toNat + 1 := by c0_bound
  refine ⟨hli_lm, hiu1, ?_⟩
  rw [m6_zext32_toNat, hiu1]
  exact m7_p2_fwd_lm_clear_step hlmu hli_at.1 hli_eq hrem_lm

/-- Parametric `Func.wp` proof for `full_fwd_check_cl_m7`. -/
theorem full_fwd_check_cl_m7_wp (Γ : Env)
    (hScanLit : ∀ a m Q X, fullFwdScanLitM7Spec a m Q X →
      Γ "full_fwd_scan_lit_m7" [i64, i32, i32, i32, .bool] [i32] a m Q X)
    (hUnwatch : ∀ a m Q X, fullUnwatchLargeSpec a m Q X →
      Γ "full_unwatch_large" [i64, i32, i32] [] a m Q X)
    (hAddUnit : ∀ a m Q X, fullAddUnitSpec a m Q X →
      Γ "full_add_unit" [i64, i32] [.bool] a m Q X)
    (hAddBin : ∀ a m Q X, fullAddBinSpec a m Q X →
      Γ "full_add_bin" [i64, i32, i32] [i64] a m Q X)
    (hFlushUnits : ∀ a m Q X, fullDenseFlushUnitsM6Spec a m Q X →
      Γ "full_dense_flush_units_m7" [i64] [.bool] a m Q X) :
    ∀ a m Q X, fullFwdCheckClM7Spec a m Q X →
      Func.wp Γ full_fwd_check_cl_m7_body a m Q X := by
  rintro ⟨h, cref, ⟨⟩⟩ m0 Q X hSpec
  obtain ⟨c, F0, F_cur, s0, R, rfl, hdw0, href0, hm0, hQ⟩ :=
    fullFwdCheckClM7Spec_elim hSpec
  have hmx := c.hmaxv; have harc := c.harena; unfold dimacsBound at hmx harc
  have hwf0 := hdw0.2.1.arena.refs_wf cref.toNat href0
  have hal0_le := hdw0.1.core_ok.arena_len_le
  have har_len0 : cref.toNat < s0.core.arena.length := by
    rw [hdw0.1.core_ok.arena_len_arr]; omega
  have hcr_ar0 : (cref.setWidth 64).toNat < s0.core.arena.length := by
    rw [hdw0.1.core_ok.arena_len_arr, m6_zext32_toNat]; omega
  have hcr2_ar0 : (cref.setWidth 64 + 2#64).toNat < s0.core.arena.length := by
    rw [hdw0.1.core_ok.arena_len_arr]; c0_bound
  let hdr0 := s0.core.arena[(cref.setWidth 64).toNat]'hcr_ar0
  let sz0 := s0.core.arena[(cref.setWidth 64 + 2#64).toNat]'hcr2_ar0
  unfold Func.wp full_fwd_check_cl_m7_body
  c0_hsplit
  · c0_hsteps!; exact hQ true s0 m0 hdw0 rfl rfl rfl rfl rfl rfl (fun h => by cases h) hm0
  · have hng0 : fullArenaClauseGarb s0 cref.toNat = false := by
      unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
      rw [List.getElem?_eq_getElem har_len0, Option.getD_some]
      have hget : s0.core.arena[cref.toNat]'har_len0 = hdr0 :=
        m6_getElem_congr (m6_zext32_toNat cref).symm _ _
      rw [hget]
      have h0 : (hdr0 &&& 0x00080000#32) = 0#32 := by
        change (hdr0 &&& (0x00080000#32 ||| 0x00400000#32)) = 0#32 at hc
        have hsub : (0x00080000#32 : BitVec 32) &&& (0x00080000#32 ||| 0x00400000#32) =
            0x00080000#32 := by decide
        have hc' := congrArg (· &&& 0x00080000#32) hc
        rw [BitVec.and_assoc, BitVec.and_comm _ 0x00080000#32, hsub, BitVec.zero_and] at hc'
        exact hc'
      rw [h0]; rfl
    c0_hsplit
    · c0_hsteps!; exact hQ true s0 m0 hdw0 rfl rfl rfl rfl rfl rfl (fun h => by cases h) hm0
    · have hsz0_eq : sz0.toNat = fullArenaClauseSizeCore s0.core cref.toNat := by
        unfold sz0 fullArenaClauseSizeCore
        rw [List.getElem?_eq_getElem (by rw [hdw0.1.core_ok.arena_len_arr]; omega),
          Option.getD_some]
        exact congrArg BitVec.toNat (m6_getElem_congr (by c0_bound) _ _)
      have hhdr0_eq : hdr0 = fullArenaHdr s0 cref.toNat := by
        unfold hdr0 fullArenaHdr fullArenaHdrCore
        rw [List.getElem?_eq_getElem har_len0, Option.getD_some]
        exact m6_getElem_congr (m6_zext32_toNat cref) _ _
      c0_hsteps_nogrp
      -- Outer multi-shrink `while (true)` loop (measure: `sz.toNat`)
      refine wp_loop_group (ts := [i32, i32])
        (fun rem (hdr, sz, ()) ms => ∃ st : FullState,
          rem = sz.toNat ∧ 3 ≤ sz.toNat ∧
          FullDenseInvW c F0 F_cur st ∧
          st.core.cur_vars = s0.core.cur_vars ∧ st.core.arena_len = s0.core.arena_len ∧
          st.core.fuel = s0.core.fuel ∧
          fullArenaClauseRefs st = fullArenaClauseRefs s0 ∧
          st.scratch.tarjan_mark = s0.scratch.tarjan_mark ∧
          st.scratch.red_refs = s0.scratch.red_refs ∧
          hdr = fullArenaHdr st cref.toNat ∧
          sz.toNat = fullArenaClauseSizeCore st.core cref.toNat ∧
          fullArenaClauseGarb st cref.toNat = false ∧
          (FullMem c st ⋆ R) ms)
        ?_ ?_
      · rintro L rem ⟨hdr, sz, ⟨⟩⟩ ms hL
          ⟨st, rfl, hsz3, hdwt, hcvt, halt, hflt, hrefst, htmkt, hrrt, hhdrt, hszt, hngt, hms⟩
        have href_t : cref.toNat ∈ fullArenaClauseRefs st := hrefst.symm ▸ href0
        have hwf_t := hdwt.2.1.arena.refs_wf cref.toNat href_t
        have hal_t := hdwt.1.core_ok.arena_len_le
        have har_len_t : cref.toNat < st.core.arena.length := by
          rw [hdwt.1.core_ok.arena_len_arr]; omega
        have hcr_art : (cref.setWidth 64).toNat < st.core.arena.length := by
          rw [hdwt.1.core_ok.arena_len_arr, m6_zext32_toNat]; omega
        have hsz_le_cv : sz.toNat ≤ st.core.cur_vars := by
          have := m6_clause_nodup_len_le hdwt href_t hngt
          change fullArenaClauseSizeCore st.core cref.toNat ≤ st.core.cur_vars at this; omega
        have hent_C := hdwt.2.1.arena.entails cref.toNat href_t hngt
        -- Step 1: scan `cref` for root-SAT or first level-0 false lit
        c0_hsplit
        · refine wp_loop_break_group (brkTs := [.bool, i32, i32]) (lpTs := [i32, i32])
            (fun (sat_b, drop_b, _, ()) m1 => m1 = ms ∧
              (sat_b = false → drop_b ≠ 0xFFFFFFFF#32 →
                drop_b.toNat < 2 * st.core.cur_vars ∧
                st.core.vals[drop_b.toNat]?.getD 0#8 = 0xFF#8))
            (fun rem_i (drop_i, i, ()) mi => mi = ms ∧
              i.toNat ≤ sz.toNat ∧ rem_i = sz.toNat - i.toNat ∧
              (drop_i ≠ 0xFFFFFFFF#32 →
                drop_i.toNat < 2 * st.core.cur_vars ∧
                st.core.vals[drop_i.toNat]?.getD 0#8 = 0xFF#8))
            ?_ ?_ ?_
          · rintro _ ⟨sat_b, drop_b, _, ⟨⟩⟩ m1 ⟨rfl, hfalse_drop⟩
            c0_hsplit
            · -- Root-SAT: mark `PH_GARB` and return `true`
              c0_hsteps!
              let ag' := st.core.arena_garbage + 3#64 + sz.setWidth 64
              let ar' := st.core.arena.set (cref.setWidth 64).toNat (hdr ||| 0x00080000#32)
              let smg : FullState :=
                { st with core := { st.core with arena := ar', arena_garbage := ag' } }
              have hmg := m6_fullDenseInvW_markGarb hdwt href_t (arena' := ar') (ag' := ag')
                (by simp [ar', hdwt.1.core_ok.arena_len_arr])
                (Or.inl (by
                  dsimp only [ar']; rw [m6_zext32_toNat, hhdrt]
                  exact List.getElem?_set_self har_len_t))
                (fun i hne _ => by
                  dsimp only [ar']; rw [m6_zext32_toNat]; exact List.getElem?_set_ne hne.symm)
              exact hQ true smg _ hmg.1 hcvt halt hflt (hmg.2.trans hrefst) htmkt hrrt
                (fun h => by cases h) hm
            · have hdrop_ent0 : drop_b ≠ 0xFFFFFFFF#32 →
                  (cnfOfClauses F_cur).EntailsClause
                    (cnfClause ((fullArenaClauseLits st cref.toNat).filter
                      (· != drop_b.toNat))) :=
                fun hne => by
                  obtain ⟨hlt_d, hff_d⟩ := hfalse_drop hc hne
                  exact m7_p2_drop_false_lit hdwt.2.1 hdwt.2.2.2.2.2.1 hent_C hlt_d hff_d
              -- Step 2: if `drop_b == 0xFFFFFFFFu`, mark `lm`, scan `l` & `l^1`, unmark `lm`
              refine wp_join_state (ts := [i32, i32, .bool])
                (α := Bool × BitVec 32 × BitVec 32 × FullState)
                (fun x => (x.2.1, x.2.2.1, x.1, ()))
                (fun x mj =>
                  x.2.2.2.core.cur_vars = st.core.cur_vars ∧
                  x.2.2.2.core.arena = st.core.arena ∧
                  x.2.2.2.core.arena_len = st.core.arena_len ∧
                  x.2.2.2.core.fuel = st.core.fuel ∧
                  x.2.2.2.scratch = st.scratch ∧
                  FullDenseInvW c F0 F_cur x.2.2.2 ∧
                  (x.1 = false → x.2.1 ≠ 0xFFFFFFFF#32 →
                    (cnfOfClauses F_cur).EntailsClause
                      (cnfClause ((fullArenaClauseLits st cref.toNat).filter
                        (· != x.2.1.toNat)))) ∧
                  (FullMem c x.2.2.2 ⋆ R) mj)
                (fun _ ⟨sub_b, drop_f, _unk, sf⟩ mj
                    ⟨hcvf, harf, half, hflf, hscrf, hdwf, hdrop_ent, hmj⟩ => by
                have hrefsf : fullArenaClauseRefs sf = fullArenaClauseRefs st := by
                  unfold fullArenaClauseRefs fullArenaClauseRefsCore; rw [harf, half]
                have href_f : cref.toNat ∈ fullArenaClauseRefs sf := hrefsf.symm ▸ href_t
                have hhdr_f : hdr = fullArenaHdr sf cref.toNat := by
                  unfold fullArenaHdr fullArenaHdrCore; rw [harf]; exact hhdrt
                have har_len_f : cref.toNat < sf.core.arena.length := by
                  rw [hdwf.1.core_ok.arena_len_arr]; omega
                have hcr_arf : (cref.setWidth 64).toNat < sf.core.arena.length := by
                  rw [hdwf.1.core_ok.arena_len_arr, m6_zext32_toNat]; omega
                c0_hsplit
                · -- Subsumed: mark `PH_GARB`, bump `fwd_sub_cnt`, return `true`
                  c0_hsteps!
                  let ag' := sf.core.arena_garbage + 3#64 + sz.setWidth 64
                  let ar' := sf.core.arena.set (cref.setWidth 64).toNat (hdr ||| 0x00080000#32)
                  let smg : FullState :=
                    { sf with
                      core := { sf.core with arena := ar', arena_garbage := ag' }
                      scratch := { sf.scratch with fwd_sub_cnt := sf.scratch.fwd_sub_cnt + 1#64 } }
                  have hmg := m6_fullDenseInvW_markGarb hdwf href_f (arena' := ar') (ag' := ag')
                    (by simp [ar', hdwf.1.core_ok.arena_len_arr])
                    (Or.inl (by
                      dsimp only [ar']; rw [m6_zext32_toNat, hhdr_f]
                      exact List.getElem?_set_self har_len_f))
                    (fun i hne _ => by
                      dsimp only [ar']; rw [m6_zext32_toNat]; exact List.getElem?_set_ne hne.symm)
                  have hdw_sub := m6_fullDenseInvW_with_scratch hmg.1
                    (sc' := smg.scratch) { hdwf.1.scratch_ok with } rfl rfl
                  exact hQ true smg _ hdw_sub (hcvf.trans hcvt) (half.trans halt) (hflf.trans hflt)
                    (hmg.2.trans (hrefsf.trans hrefst))
                    (by dsimp only [smg]; rw [hscrf]; exact htmkt)
                    (by dsimp only [smg]; rw [hscrf]; exact hrrt) (fun h => by cases h) hm
                · c0_hsplit
                  · c0_hsteps!
                    exact hQ true sf mj hdwf (hcvf.trans hcvt) (half.trans halt) (hflf.trans hflt)
                      (hrefsf.trans hrefst) (by rw [hscrf, htmkt]) (by rw [hscrf, hrrt])
                      (fun h => by cases h) hmj
                  · have hent_drop := hdrop_ent ‹sub_b = false› hc
                    c0_hsteps_nogrp
                    let sf1 : FullState :=
                      { sf with scratch := { sf.scratch with
                          fwd_str_cnt := sf.scratch.fwd_str_cnt + 1#64 } }
                    have hdwf1 : FullDenseInvW c F0 F_cur sf1 :=
                      m6_fullDenseInvW_with_scratch hdwf (sc' := sf1.scratch)
                        { hdwf.1.scratch_ok with } rfl rfl
                    m7_call hUnwatch
                    refine ⟨c, sf1, R, rfl, hdwf1.1, (m6_denseWatchesInv_of_w hdwf1).layout, hm, ?_⟩
                    intro wvec' wstk' wu' m_u su hlen_u _ hwm_u hm_u
                    have hdw_u : FullDenseInvW c F0 F_cur su :=
                      m7_p2_fullDenseInvW_of_unwatch hdwf1 hlen_u (hwm_u F_cur hdwf1.2.1.watches)
                    have href_u : cref.toNat ∈ fullArenaClauseRefs su := href_f
                    have har_len_u : cref.toNat < su.core.arena.length := har_len_f
                    have hcr_aru : (cref.setWidth 64).toNat < su.core.arena.length := hcr_arf
                    -- Filter `l != drop_f` into `tmp[0 ..< nsz)`
                    c0_hsteps_nogrp
                    refine wp_loop_group (ts := [i32, i32])
                      (fun rem_f (i, nsz, ()) mf => ∃ tmp' : List (BitVec 32),
                        let sf' : FullState := { su with core := { su.core with tmp := tmp' } }
                        tmp'.length = c.max_vars ∧
                        i.toNat ≤ sz.toNat ∧ rem_f = sz.toNat - i.toNat ∧
                        nsz.toNat ≤ i.toNat ∧
                        (tmp'.take nsz.toNat).map BitVec.toNat =
                          (((fullArenaClauseLits st cref.toNat).take i.toNat).filter
                            (· != drop_f.toNat)) ∧
                        (FullMem c sf' ⋆ R) mf)
                      ?_ ?_
                    · rintro Lf rem_f ⟨i, nsz, ⟨⟩⟩ mf hLf
                        ⟨tmp', htl', hi_le, rfl, hnsz_le, hfilt, hmf⟩
                      let sf' : FullState := { su with core := { su.core with tmp := tmp' } }
                      c0_hsplit
                      · have hi_lt : i.toNat < sz.toNat := hc
                        have hcri : (cref.setWidth 64 + 3#64 + i.setWidth 64).toNat <
                            su.core.arena.length := by
                          rw [hdw_u.1.core_ok.arena_len_arr]; c0_bound
                        let l_i := su.core.arena[(cref.setWidth 64 + 3#64 + i.setWidth 64).toNat]'
                          hcri
                        have hli_eq :
                            (fullArenaClauseLits st cref.toNat)[i.toNat]'(by
                              unfold fullArenaClauseLits fullArenaClauseLitsCore
                              simp only [List.length_take, List.length_drop, List.length_map]
                              rw [hdwt.1.core_ok.arena_len_arr]; omega) = l_i.toNat := by
                          unfold fullArenaClauseLits fullArenaClauseLitsCore
                          simp only [List.getElem_map, List.getElem_take, List.getElem_drop]
                          have hopt :
                              some (st.core.arena[cref.toNat + 3 + i.toNat]'(by
                                rw [hdwt.1.core_ok.arena_len_arr]; omega)) = some l_i := by
                            have hsu_ar : su.core.arena = st.core.arena := by
                              dsimp only [su, sf1]; exact harf
                            dsimp only [l_i]
                            rw [← List.getElem?_eq_getElem (by
                              rw [hdwt.1.core_ok.arena_len_arr]; omega),
                              ← List.getElem?_eq_getElem hcri, hsu_ar]
                            exact congrArg (st.core.arena[·]?) (by c0_bound)
                          exact congrArg BitVec.toNat (Option.some.inj hopt)
                        have htake_succ :
                            (fullArenaClauseLits st cref.toNat).take (i.toNat + 1) =
                            (fullArenaClauseLits st cref.toNat).take i.toNat ++ [l_i.toNat] := by
                          rw [List.take_succ_eq_append_getElem (by
                            unfold fullArenaClauseLits fullArenaClauseLitsCore
                            simp only [List.length_take, List.length_drop, List.length_map]
                            rw [hdwt.1.core_ok.arena_len_arr]; omega), hli_eq]
                        have hi1 : (i + 1#32).toNat = i.toNat + 1 := by c0_bound
                        c0_hsteps_nogrp
                        refine wp_join_state (ts := [i32]) (α := BitVec 32 × List (BitVec 32))
                          (fun x => (x.1, ()))
                          (fun x mj =>
                            x.2.length = c.max_vars ∧
                            x.1.toNat ≤ i.toNat + 1 ∧
                            (x.2.take x.1.toNat).map BitVec.toNat =
                              ((fullArenaClauseLits st cref.toNat).take (i.toNat + 1)).filter
                                (· != drop_f.toNat) ∧
                            (FullMem c { su with core := { su.core with tmp := x.2 } } ⋆ R) mj)
                          (fun _ ⟨nsz', tmp''⟩ mj ⟨htl'', hnsz_le', hfilt', hmj⟩ => by
                            c0_hsteps!
                            exact hLf (sz.toNat - (i + 1#32).toNat) (i + 1#32, nsz', ()) mj
                              (by omega) ⟨tmp'', htl'', by omega, rfl,
                                by rw [hi1]; exact hnsz_le', by rw [hi1]; exact hfilt', hmj⟩)
                          (fun J52 hJ52 => by
                            c0_hsplit
                            · have hnsz_tmp : (nsz.setWidth 64).toNat < tmp'.length := by
                                rw [htl', m6_zext32_toNat]
                                have := hdwt.1.core_ok.cur_vars_le; omega
                              have hnsz1 : (nsz + 1#32).toNat = nsz.toNat + 1 := by c0_bound
                              c0_hsteps!
                              let tmp'' := tmp'.set (nsz.setWidth 64).toNat l_i
                              have htake_set : (tmp''.take (nsz.toNat + 1)).map BitVec.toNat =
                                  (tmp'.take nsz.toNat).map BitVec.toNat ++ [l_i.toNat] := by
                                have hlt_m : nsz.toNat + 1 ≤ tmp''.length := by
                                  simp only [tmp'', List.length_set, htl']
                                  have := hdwt.1.core_ok.cur_vars_le; omega
                                rw [List.take_succ_eq_append_getElem hlt_m, List.map_append,
                                  List.map_singleton]
                                congr 1
                                · rw [List.take_set_of_le (by
                                    rw [m6_zext32_toNat]; exact Nat.le_refl _)]
                                · have h1 : tmp''[nsz.toNat]'(by
                                      simp only [tmp'', List.length_set, htl']
                                      have := hdwt.1.core_ok.cur_vars_le; omega) = l_i := by
                                    dsimp only [tmp'']
                                    rw [m6_getElem_congr (m6_zext32_toNat nsz).symm _
                                      (by simp only [List.length_set]; exact hnsz_tmp)]
                                    exact List.getElem_set_self
                                      (by rw [List.length_set]; exact hnsz_tmp)
                                  exact congrArg (fun x => [x.toNat]) h1
                              have hl_c0 :
                                  su.core.arena[(cref.toNat + BitVec.toNat (3 : BitVec 64) +
                                    i.toNat) % 2 ^ 64]'(by
                                      rw [hdw_u.1.core_ok.arena_len_arr]; c0_bound) = l_i :=
                                m6_getElem_congr (by c0_bound) _ _
                              rw [hl_c0] at hc
                              exact hJ52 (nsz + 1#32, tmp'') _ ⟨by simp [tmp'', htl'],
                                by rw [hnsz1]; omega, by
                                rw [hnsz1, htake_set, htake_succ, List.filter_append, hfilt]
                                have hne_n : (l_i.toNat != drop_f.toNat) = true :=
                                  bne_iff_ne.mpr fun h => hc (BitVec.eq_of_toNat_eq h)
                                simp [hne_n], hm⟩
                            · have hl_c0 :
                                  su.core.arena[(cref.toNat + BitVec.toNat (3 : BitVec 64) +
                                    i.toNat) % 2 ^ 64]'(by
                                      rw [hdw_u.1.core_ok.arena_len_arr]; c0_bound) = l_i :=
                                m6_getElem_congr (by c0_bound) _ _
                              rw [hl_c0] at hc
                              c0_hsteps!
                              exact hJ52 (nsz, tmp') mf ⟨htl', Nat.le_succ_of_le hnsz_le, by
                                rw [htake_succ, List.filter_append, hfilt]
                                have heq_n : (l_i.toNat != drop_f.toNat) = false :=
                                  bne_eq_false_iff_eq.mpr (congrArg BitVec.toNat hc)
                                simp [heq_n], hmf⟩)
                      · -- Post-filter: `tmp'[0..nsz)` equals `C.filter (· != drop_f)`
                        have hdw_f' : FullDenseInvW c F0 F_cur sf' :=
                          m6_fullDenseInvW_with_tmp hdw_u htl'
                        have hi_eq : i.toNat = sz.toNat := by omega
                        have hC_len : (fullArenaClauseLits st cref.toNat).length = sz.toNat := by
                          unfold fullArenaClauseLits fullArenaClauseLitsCore
                          simp only [List.length_map, List.length_take, List.length_drop]
                          rw [hdwt.1.core_ok.arena_len_arr]; omega
                        have htmp_eq : (tmp'.take nsz.toNat).map BitVec.toNat =
                            (fullArenaClauseLits st cref.toNat).filter (· != drop_f.toNat) := by
                          rw [hi_eq, ← hC_len, List.take_length] at hfilt; exact hfilt
                        have htmp_ent : (cnfOfClauses F_cur).EntailsClause
                            (cnfClause ((tmp'.take nsz.toNat).map BitVec.toNat)) := by
                          rw [htmp_eq]; exact hent_drop
                        have htmp_nd : (((tmp'.take nsz.toNat).map BitVec.toNat).map
                            (· / 2)).Nodup := by
                          rw [htmp_eq]
                          exact m7_p2_sublist_map_nodup (List.filter_sublist)
                            (hdwt.2.2.2.1 cref.toNat href_t hngt)
                        have htmp_lt : ∀ l ∈ (tmp'.take nsz.toNat).map BitVec.toNat,
                            l < 2 * sf'.core.cur_vars := fun l hl => by
                          rw [htmp_eq] at hl
                          have hmC := (List.mem_filter.mp hl).1
                          have hlt := hdwt.2.1.arena.lits_lt cref.toNat href_t hngt l hmC
                          dsimp only [sf', su, sf1]; rw [hcvf]; exact hlt
                        c0_hsplit
                        · -- `nsz >= sz`: no-op return `true`
                          c0_hsteps!
                          exact hQ true sf' mf hdw_f' (hcvf.trans hcvt) (half.trans halt)
                            (hflf.trans hflt) (hrefsf.trans hrefst)
                            (by dsimp only [sf', su, sf1]; rw [hscrf]; exact htmkt)
                            (by dsimp only [sf', su, sf1]; rw [hscrf]; exact hrrt)
                            (fun h => by cases h) hmf
                        · have hnsz_lt_sz : nsz.toNat < sz.toNat := by omega
                          c0_hsplit
                          · -- `nsz == 0`: empty clause entailed → UNSAT!
                            have hnsz0 : nsz.toNat = 0 := by rw [hc]; rfl
                            rw [hnsz0, List.take_zero, List.map_nil] at htmp_ent
                            have hunsat : (cnfOfClauses F_cur).Unsat :=
                              m7_p2_unsat_of_entails_nil htmp_ent
                            c0_hsteps!
                            let ag' := sf'.core.arena_garbage + 3#64 + sz.setWidth 64
                            let ar' := sf'.core.arena.set (cref.setWidth 64).toNat
                              (hdr ||| 0x00080000#32)
                            let smg : FullState :=
                              { sf' with core :=
                                { sf'.core with arena := ar', arena_garbage := ag' } }
                            have hmg := m6_fullDenseInvW_markGarb hdw_f' href_u (arena' := ar')
                              (ag' := ag') (by simp [ar', hdw_f'.1.core_ok.arena_len_arr])
                              (Or.inl (by
                                dsimp only [ar']; rw [m6_zext32_toNat, hhdr_f]
                                exact List.getElem?_set_self har_len_u))
                              (fun idx hne _ => by
                                dsimp only [ar']; rw [m6_zext32_toNat]
                                exact List.getElem?_set_ne hne.symm)
                            let sinc := { smg with core := { smg.core with inconsistent := 1#64 } }
                            exact hQ false sinc _ (m6_fullDenseInvW_set_inc hmg.1 hunsat)
                              (hcvf.trans hcvt) (half.trans halt) (hflf.trans hflt)
                              (hmg.2.trans (hrefsf.trans hrefst))
                              (by dsimp only [sinc, smg, sf', su, sf1]; rw [hscrf]; exact htmkt)
                              (by dsimp only [sinc, smg, sf', su, sf1]; rw [hscrf]; exact hrrt)
                              (fun _ => hdw_f'.2.1.ext_sound.2 hunsat) hm
                          · c0_hsplit
                            · -- `nsz == 1`: unit clause → mark `PH_GARB`, `add_unit`, `flush_units`
                              have hnsz1 : nsz.toNat = 1 := by rw [hc]; rfl
                              have h0_tmp : 0 < tmp'.length := by
                                rw [htl']; have := hdwt.1.core_ok.cur_vars_le; omega
                              have htake1 : (tmp'.take nsz.toNat).map BitVec.toNat =
                                  [(tmp'[0]'h0_tmp).toNat] := by
                                rw [hnsz1, show tmp'.take 1 = [tmp'[0]'h0_tmp] from
                                  match tmp', h0_tmp with | _ :: _, _ => rfl]
                                rfl
                              rw [htake1] at htmp_ent
                              c0_hsteps_nogrp
                              let ag' := sf'.core.arena_garbage + 3#64 + sz.setWidth 64
                              let ar' := sf'.core.arena.set (cref.setWidth 64).toNat
                                (hdr ||| 0x00080000#32)
                              let smg : FullState :=
                                { sf' with core :=
                                  { sf'.core with arena := ar', arena_garbage := ag' } }
                              have hmg := m6_fullDenseInvW_markGarb hdw_f' href_u (arena' := ar')
                                (ag' := ag') (by simp [ar', hdw_f'.1.core_ok.arena_len_arr])
                                (Or.inl (by
                                  dsimp only [ar']; rw [m6_zext32_toNat, hhdr_f]
                                  exact List.getElem?_set_self har_len_u))
                                (fun idx hne _ => by
                                  dsimp only [ar']; rw [m6_zext32_toNat]
                                  exact List.getElem?_set_ne hne.symm)
                              have ht0_lt : (tmp'[0]'h0_tmp).toNat < 2 * smg.core.cur_vars :=
                                htmp_lt _ (by rw [htake1]; exact List.mem_singleton_self _)
                              m7_call hAddUnit
                              refine ⟨c, F0, F_cur, smg, R, rfl, hmg.1.1, hmg.1.2.1,
                                fun _ => htmp_ent, hm, ?_⟩
                              intro ok vals' flags' lvl' rsns' trl' tp' te' prop' cl' unass' unfl'
                                inc' phases' ta' ba' pt' pb' hp' ps' hl' qsi' qss' m_au s_au
                                hlen_au hw_au hcl_au hfu_au _ hm_au
                              have hdw_au := m6_fullDenseInvW_of_addUnit hmg.1 hlen_au hw_au hcl_au
                                rfl rfl rfl rfl rfl rfl rfl
                              c0_hsplit
                              · c0_hsteps_nogrp
                                m7_call hFlushUnits
                                refine fullDenseFlushUnitsM6Spec_intro rfl hdw_au hm_au ?_
                                intro ok2 s2 m2 hdw2 hcv2 hal2 hfl2 hrefs2 htmk2 hrr2 _ _ _ _
                                  hf2 hm2
                                c0_hsteps!
                                exact hQ ok2 s2 m2 hdw2 (hcv2.trans (hcvf.trans hcvt))
                                  (hal2.trans (half.trans halt)) (hfl2.trans (hflf.trans hflt))
                                  (hrefs2.trans (hmg.2.trans (hrefsf.trans hrefst)))
                                  (htmk2.trans (by
                                    dsimp only [s_au, smg, sf', su, sf1]; rw [hscrf]; exact htmkt))
                                  (hrr2.trans (by
                                    dsimp only [s_au, smg, sf', su, sf1]; rw [hscrf]; exact hrrt))
                                  hf2 hm2
                              · c0_hsteps!
                                exact hQ false s_au m_au hdw_au (hcvf.trans hcvt) (half.trans halt)
                                  (hflf.trans hflt) (hmg.2.trans (hrefsf.trans hrefst))
                                  (by
                                    dsimp only [s_au, smg, sf', su, sf1]; rw [hscrf]; exact htmkt)
                                  (by dsimp only [s_au, smg, sf', su, sf1]; rw [hscrf]; exact hrrt)
                                  (fun _ => (hfu_au ht0_lt (by simpa using hc)).1) hm_au
                            · c0_hsplit
                              · -- `nsz == 2`: OOM-safe `full_add_bin`, then `PH_GARB | PH_SUBSUME`
                                have hnsz2 : nsz.toNat = 2 := by rw [hc]; rfl
                                have h0_tmp : 0 < tmp'.length := by
                                  rw [htl']; have := hdwt.1.core_ok.cur_vars_le; omega
                                have h1_tmp : 1 < tmp'.length := by
                                  rw [htl']; have := hdwt.1.core_ok.cur_vars_le; omega
                                have htake2 : (tmp'.take nsz.toNat).map BitVec.toNat =
                                    [(tmp'[0]'h0_tmp).toNat, (tmp'[1]'h1_tmp).toNat] := by
                                  rw [hnsz2, show tmp'.take 2 =
                                      [tmp'[0]'h0_tmp, tmp'[1]'h1_tmp] from
                                    match tmp', h0_tmp, h1_tmp with | _ :: _ :: _, _, _ => rfl]
                                  rfl
                                rw [htake2] at htmp_ent
                                c0_hsteps_nogrp
                                m7_call hAddBin
                                refine ⟨c, F0, F_cur, sf', R, rfl, hdw_f'.1, hdw_f'.2.1,
                                  hdw_f'.2.2.2.2.2.1, fun _ _ => htmp_ent, hmf, ?_⟩
                                intro br vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec'
                                  wstk' wlen' wu' nb' oom' inc' phases' wsort' m_b s_b
                                  hlen_b hw_b hbr_b h20_b _ hm_b
                                have hdw_b : FullDenseInvW c F0 F_cur s_b :=
                                  m7_p2_fullDenseInvW_of_addBin hdw_f' hlen_b hw_b rfl rfl rfl
                                    rfl rfl rfl rfl rfl
                                c0_hsplit
                                · c0_hsteps!
                                  exact hQ false s_b m_b hdw_b (hcvf.trans hcvt) (half.trans halt)
                                    (hflf.trans hflt) (hrefsf.trans hrefst)
                                    (by dsimp only [s_b, sf', su, sf1]; rw [hscrf]; exact htmkt)
                                    (by dsimp only [s_b, sf', su, sf1]; rw [hscrf]; exact hrrt)
                                    (fun _ => (h20_b hc).1) hm_b
                                · c0_hsplit
                                  · c0_hsteps!
                                    exact hQ true s_b m_b hdw_b (hcvf.trans hcvt) (half.trans halt)
                                      (hflf.trans hflt) (hrefsf.trans hrefst)
                                      (by dsimp only [s_b, sf', su, sf1]; rw [hscrf]; exact htmkt)
                                      (by dsimp only [s_b, sf', su, sf1]; rw [hscrf]; exact hrrt)
                                      (fun h => by cases h) hm_b
                                  · have hcr3_ar : (cref.setWidth 64 + 3#64).toNat <
                                        s_b.core.arena.length := by
                                      rw [hdw_b.1.core_ok.arena_len_arr]; c0_bound
                                    have hcr4_ar : (cref.setWidth 64 + 4#64).toNat <
                                        s_b.core.arena.length := by
                                      rw [hdw_b.1.core_ok.arena_len_arr]; c0_bound
                                    c0_hsteps_nogrp
                                    have hmg := m7_p2_fwd_nsz2_garb_post hdw_b href_u (by
                                      change fullArenaClauseSizeCore sf.core cref.toNat = sz.toNat
                                      unfold fullArenaClauseSizeCore; rw [harf]; exact hszt.symm)
                                      (by
                                        unfold fullArenaHdr fullArenaHdrCore
                                        change sf.core.arena[cref.toNat]?.getD 0#32 = hdr
                                        rw [harf]; exact hhdrt.symm) h0_tmp h1_tmp
                                    m7_call hFlushUnits
                                    refine fullDenseFlushUnitsM6Spec_intro rfl hmg.1 hm ?_
                                    intro ok2 s2 m2 hdw2 hcv2 hal2 hfl2 hrefs2 htmk2 hrr2 _ _ _ _
                                      hf2 hm2
                                    c0_hsteps!
                                    exact hQ ok2 s2 m2 hdw2 (hcv2.trans (hcvf.trans hcvt))
                                      (hal2.trans (half.trans halt)) (hfl2.trans (hflf.trans hflt))
                                      (hrefs2.trans (hmg.2.trans (hrefsf.trans hrefst)))
                                      (htmk2.trans (by
                                        dsimp only [s_b, sf', su, sf1]; rw [hscrf]
                                        exact htmkt))
                                      (hrr2.trans (by
                                        dsimp only [s_b, sf', su, sf1]; rw [hscrf]
                                        exact hrrt))
                                      hf2 hm2
                              · -- `nsz >= 3`: copy `tmp[0..nsz)` in-place, shrink, set `PH_SUBSUME`
                                have hnsz3 : 3 ≤ nsz.toNat := by
                                  have h0 : nsz.toNat ≠ 0 := fun h =>
                                    ‹nsz ≠ 0#32› (BitVec.eq_of_toNat_eq h)
                                  have h1 : nsz.toNat ≠ 1 := fun h =>
                                    ‹nsz ≠ 1#32› (BitVec.eq_of_toNat_eq h)
                                  have h2 : nsz.toNat ≠ 2 := fun h =>
                                    hc (BitVec.eq_of_toNat_eq h)
                                  omega
                                c0_hsteps_nogrp
                                refine wp_loop_group (ts := [i32])
                                  (fun rem_c (ic, ()) mc => ∃ ar_c : List (BitVec 32),
                                    let sc : FullState :=
                                      { sf' with core := { sf'.core with arena := ar_c } }
                                    ar_c.length = c.arena_cap ∧
                                    ic.toNat ≤ nsz.toNat ∧ rem_c = nsz.toNat - ic.toNat ∧
                                    (∀ idx, idx < cref.toNat + 3 ∨
                                      cref.toNat + 3 + ic.toNat ≤ idx →
                                      ar_c[idx]? = sf'.core.arena[idx]?) ∧
                                    (∀ idx < ic.toNat,
                                      ar_c[cref.toNat + 3 + idx]? = tmp'[idx]?) ∧
                                    (FullMem c sc ⋆ R) mc)
                                  ?_ ?_
                                · rintro Lc rem_c ⟨ic, ⟨⟩⟩ mc hLc
                                    ⟨ar_c, harc_l, hic_le, rfl, hout_c, hcopy_c, hmc⟩
                                  c0_hsplit
                                  · have hic_lt : ic.toNat < nsz.toNat := hc
                                    have hic_tmp : (ic.setWidth 64).toNat < tmp'.length := by
                                      rw [htl', m6_zext32_toNat]
                                      have := hdwt.1.core_ok.cur_vars_le; omega
                                    have hic_ar : (cref.setWidth 64 + 3#64 + ic.setWidth 64).toNat <
                                        ar_c.length := by rw [harc_l]; c0_bound
                                    have hic1 : (ic + 1#32).toNat = ic.toNat + 1 := by c0_bound
                                    have hcp := m7_p2_copy_iter hdwt href_t hszt hnsz_lt_sz
                                      harc_l htl' hout_c hcopy_c hic_lt hic_tmp hic_ar hic1
                                    c0_hsteps!
                                    exact hLc (nsz.toNat - (ic + 1#32).toNat) (ic + 1#32, ()) _
                                      (by omega) ⟨_, hcp.1, hcp.2.1, rfl, hcp.2.2.1, hcp.2.2.2, hm⟩
                                  · have hic_eq : ic.toNat = nsz.toNat := by omega
                                    have hcr2_arc : (cref.setWidth 64 + 2#64).toNat <
                                        ar_c.length := by rw [harc_l]; c0_bound
                                    have hcr1_arc : (cref.setWidth 64 + 1#64).toNat <
                                        ar_c.length := by rw [harc_l]; c0_bound
                                    c0_hsteps_nogrp
                                    let ar_w := (ar_c.set (cref.setWidth 64 + 2#64).toNat nsz).set
                                      (cref.setWidth 64 + 1#64).toNat 2#32
                                    -- Optional `PH_SHRK` sentinel + bit23 write
                                    refine wp_join_state (ts := [i32])
                                      (α := BitVec 32 × List (BitVec 32))
                                      (fun x => (x.1, ()))
                                      (fun x ms' =>
                                        let sx : FullState :=
                                          { sf' with core := { sf'.core with arena := x.2 } }
                                        FullDenseInvW c F0 F_cur sx ∧
                                        fullArenaClauseRefs sx = fullArenaClauseRefs sf' ∧
                                        x.1 = fullArenaHdr sx cref.toNat ∧
                                        fullArenaClauseSizeCore sx.core cref.toNat = nsz.toNat ∧
                                        fullArenaClauseGarb sx cref.toNat = false ∧
                                        (FullMem c sx ⋆ R) ms')
                                      (fun _ ⟨hdr_s, ar_s⟩ ms'
                                          ⟨hdws, hrefss, hhdrs, hszs, hngs, hms'⟩ => by
                                        have href_s : cref.toNat ∈ fullArenaClauseRefs
                                            { sf' with core := { sf'.core with arena := ar_s } } :=
                                          hrefss.symm ▸ href_u
                                        have hcr_ars : (cref.setWidth 64).toNat < ar_s.length := by
                                          rw [hdws.1.core_ok.arena_len_arr, m6_zext32_toNat]; omega
                                        c0_hsteps!
                                        obtain ⟨hdw_sub, hrefs_sub', hhdr_sub, hsz_sub, hng_sub⟩ :=
                                          m7_p2_fwd_nsz3_sub_post hdws href_s hhdrs hszs hngs
                                        let v_sub := hdr_s ||| 0x01000000#32
                                        let s_sub : FullState :=
                                          { sf' with core := { sf'.core with
                                            arena := ar_s.set (cref.setWidth 64).toNat v_sub } }
                                        exact hL nsz.toNat (v_sub, nsz, ()) _ hnsz_lt_sz
                                          ⟨s_sub, rfl, hnsz3, hdw_sub, hcvf.trans hcvt,
                                           half.trans halt, hflf.trans hflt,
                                           hrefs_sub'.trans (hrefss.trans (hrefsf.trans hrefst)),
                                           by dsimp only [s_sub, sf', su, sf1]; rw [hscrf]
                                              exact htmkt,
                                           by dsimp only [s_sub, sf', su, sf1]; rw [hscrf]
                                              exact hrrt,
                                           hhdr_sub, hsz_sub, hng_sub, hm⟩)
                                      (fun Js hJs => by
                                        have hsz_sf' :
                                            fullArenaClauseSizeCore sf'.core cref.toNat =
                                              sz.toNat := by
                                          change fullArenaClauseSizeCore sf.core cref.toNat =
                                            sz.toNat
                                          unfold fullArenaClauseSizeCore; rw [harf]; exact hszt.symm
                                        have hhdr_sf' :
                                            fullArenaHdrCore sf'.core cref.toNat = hdr :=
                                          hhdr_f.symm
                                        have hpad_orig :=
                                          m7_p2_fwd_pad_orig hdwt hdw_f' href_t hngt hszt
                                            (nsz := nsz)
                                            (by dsimp only [sf', su, sf1]; exact harf)
                                        have hcr0_eq : (cref.setWidth 64).toNat = cref.toNat :=
                                          m6_zext32_toNat cref
                                        have hcr1_eq : (cref.setWidth 64 + 1#64).toNat =
                                            cref.toNat + 1 := by c0_bound
                                        have hcr2_eq : (cref.setWidth 64 + 2#64).toNat =
                                            cref.toNat + 2 := by c0_bound
                                        have hsent_eq : (cref.setWidth 64 + 3#64 + sz.setWidth 64 -
                                            1#64).toNat = cref.toNat + 3 + sz.toNat - 1 := by
                                          c0_bound
                                        have hcr1_eq' : (cref.setWidth 64 + (1 : BitVec 64)).toNat
                                            = cref.toNat + 1 := hcr1_eq
                                        have hcr2_eq' : (cref.setWidth 64 + (2 : BitVec 64)).toNat
                                            = cref.toNat + 2 := hcr2_eq
                                        have hsent_eq' : (cref.setWidth 64 + (3 : BitVec 64) +
                                            sz.setWidth 64 - (1 : BitVec 64)).toNat =
                                            cref.toNat + 3 + sz.toNat - 1 := hsent_eq
                                        have h2_32 : (2 : BitVec 32) = 2#32 := rfl
                                        have hfff_32 : (4294967295 : BitVec 32) = 0xFFFFFFFF#32 :=
                                          rfl
                                        have h80_32 : (8388608 : BitVec 32) = 0x00800000#32 := rfl
                                        have hcv_f' : sz.toNat ≤ sf'.core.cur_vars := by
                                          change sz.toNat ≤ sf.core.cur_vars
                                          rw [hcvf]; exact hsz_le_cv
                                        have hngt_sf' :
                                            fullArenaClauseGarb sf' cref.toNat = false := by
                                          unfold fullArenaClauseGarb fullArenaClauseGarbCore
                                          rw [hhdr_sf']
                                          change (fullArenaHdr st cref.toNat &&& 0x00080000#32 !=
                                            0#32) = false at hngt
                                          rwa [← hhdrt] at hngt
                                        c0_hsplit
                                        · have hsh0 : (hdr &&& 0x00800000#32) = 0#32 := hc
                                          have hsent_ar :
                                              (cref.setWidth 64 + 3#64 + sz.setWidth 64 -
                                                1#64).toNat < ar_w.length := by
                                            rw [hsent_eq]; simp only [ar_w, List.length_set, harc_l]
                                            omega
                                          have hcr_arw :
                                              (cref.setWidth 64).toNat < ar_w.length := by
                                            simp only [ar_w, List.length_set, harc_l, hcr0_eq]
                                            omega
                                          c0_hsteps!
                                          have hstep := m7_p2_check_cl_shrink0 hdw_f' href_u
                                            hngt_sf' hnsz3 (by omega) hsz_sf' hhdr_sf' hcv_f' htl'
                                            harc_l (fun idx hidx => hout_c idx (by omega))
                                            (fun k hk => hcopy_c k (by omega)) htmp_lt htmp_nd
                                            htmp_ent hpad_orig hsh0 hcr2_eq' hcr1_eq' hsent_eq'
                                            hcr0_eq h2_32 hfff_32 h80_32
                                          exact hJs (hdr ||| 0x00800000#32, _) m
                                            ⟨hstep.1, hstep.2.1, hstep.2.2.1, hstep.2.2.2.1,
                                             hstep.2.2.2.2, hm⟩
                                        · have hsh1 : (hdr &&& 0x00800000#32) ≠ 0#32 := hc
                                          c0_hsteps!
                                          have hstep := m7_p2_check_cl_shrink1 hdw_f' href_u
                                            hngt_sf' hnsz3 (by omega) hsz_sf' hhdr_sf' hcv_f' htl'
                                            harc_l (fun idx hidx => hout_c idx (by omega))
                                            (fun k hk => hcopy_c k (by omega)) htmp_lt htmp_nd
                                            htmp_ent hpad_orig hsh1 hcr2_eq' hcr1_eq' h2_32
                                          exact hJs (hdr, _) m
                                            ⟨hstep.1, hstep.2.1, hstep.2.2.1, hstep.2.2.2.1,
                                             hstep.2.2.2.2, hm⟩)
                                · intro Lc hLc; c0_hsteps!
                                  exact hLc nsz.toNat (0#32, ()) mf
                                    ⟨sf'.core.arena, hdw_f'.1.core_ok.arena_len_arr, Nat.zero_le _,
                                     by simp, fun _ _ => rfl, fun _ h => by
                                       rw [show (0#32).toNat = 0 from rfl] at h; omega, hmf⟩
                    · intro Lf hLf; c0_hsteps!
                      exact hLf sz.toNat (0#32, 0#32, ()) m_u
                        ⟨su.core.tmp, hdw_u.1.core_ok.tmp_len_arr, Nat.zero_le _, by simp,
                         Nat.zero_le _, by simp, hm_u⟩)
                (fun Jm hJm => by
                  c0_hsplit
                  · -- `drop_b == 0xFFFFFFFFu`: mark `lm`, scan `l` and `l^1`, clear `lm`
                    have hdrop_ff : drop_b = 0xFFFFFFFF#32 := hc
                    have hcr3_t : (cref.setWidth 64 + 3#64).toNat < st.core.arena.length := by
                      rw [hdwt.1.core_ok.arena_len_arr]; c0_bound
                    have hl0_lt : (st.core.arena[(cref.setWidth 64 + 3#64).toNat]'hcr3_t).toNat <
                        2 * st.core.cur_vars := by
                      have hmem : (st.core.arena[(cref.setWidth 64 + 3#64).toNat]'hcr3_t).toNat ∈
                          fullArenaClauseLitsCore st.core cref.toNat := by
                        rw [mem_fullArenaClauseLitsCore_iff (by
                          rw [hdwt.1.core_ok.arena_len_arr]; omega)]
                        exact ⟨0, by omega,
                          congrArg BitVec.toNat (m6_getElem_congr (by c0_bound) _ _)⟩
                      exact hdwt.2.1.arena.lits_lt cref.toNat href_t hngt _ hmem
                    have hl0_wv : ((st.core.arena[(cref.setWidth 64 + 3#64).toNat]'hcr3_t).setWidth
                        64 <<< (1 : Nat) + 1#64).toNat < st.core.wvec.length := by
                      rw [hdwt.1.core_ok.wvec_len]; have := hdwt.1.core_ok.cur_vars_le; c0_bound
                    c0_hsteps_nogrp
                    -- Mark `lm[l] = 1` & find `min_l`
                    refine wp_loop_group (ts := [i32, i32, i32])
                      (fun rem_m (i, min_l, min_deg, ()) mm => ∃ lm' : List (BitVec 8),
                        let sm : FullState := { st with core := { st.core with lit_mark := lm' } }
                        lm'.length = 2 * c.max_vars ∧
                        i.toNat ≤ sz.toNat ∧ rem_m = sz.toNat - i.toNat ∧
                        min_l.toNat ∈ fullArenaClauseLits st cref.toNat ∧
                        (∀ x < 2 * c.max_vars,
                          lm'[x]?.getD 0#8 ≠ 0#8 ↔
                            x ∈ (fullArenaClauseLits st cref.toNat).take i.toNat) ∧
                        (FullMem c sm ⋆ R) mm)
                      ?_ ?_
                    · rintro Lm rem_m ⟨i, min_l, min_deg, ⟨⟩⟩ mm hLm
                        ⟨lm', hlml, hi_le, rfl, hml_mem, hlm_tk, hmm⟩
                      let sm : FullState := { st with core := { st.core with lit_mark := lm' } }
                      c0_hsplit
                      · have hi_lt : i.toNat < sz.toNat := hc
                        have hcri : (cref.setWidth 64 + 3#64 + i.setWidth 64).toNat <
                            st.core.arena.length := by
                          rw [hdwt.1.core_ok.arena_len_arr]; c0_bound
                        let li :=
                          st.core.arena[(cref.setWidth 64 + 3#64 + i.setWidth 64).toNat]'hcri
                        have hli_at := m7_p2_fwd_cl_lit_at hdwt href_t hszt hi_lt
                        have hli_eq : (fullArenaClauseLits st cref.toNat)[i.toNat]'hli_at.1 =
                            li.toNat := hli_at.2.trans (congrArg BitVec.toNat
                          (m6_getElem_congr (by c0_bound) _ _))
                        have hli_mem : li.toNat ∈ fullArenaClauseLits st cref.toNat :=
                          hli_eq ▸ List.getElem_mem hli_at.1
                        have hli_lt : li.toNat < 2 * st.core.cur_vars :=
                          hdwt.2.1.arena.lits_lt cref.toNat href_t hngt _ hli_mem
                        have hli_lm : (li.setWidth 64).toNat < lm'.length := by
                          rw [hlml, m6_zext32_toNat]; have := hdwt.1.core_ok.cur_vars_le; omega
                        have hli_wv : (li.setWidth 64 <<< (1 : Nat) + 1#64).toNat <
                            st.core.wvec.length := by
                          rw [hdwt.1.core_ok.wvec_len]; have := hdwt.1.core_ok.cur_vars_le; c0_bound
                        have hi1 : (i + 1#32).toNat = i.toNat + 1 := by c0_bound
                        have hlm_next : ∀ x < 2 * c.max_vars,
                            (lm'.set (li.setWidth 64).toNat 1#8)[x]?.getD 0#8 ≠ 0#8 ↔
                              x ∈ (fullArenaClauseLits st cref.toNat).take (i + 1#32).toNat := by
                          rw [hi1, m6_zext32_toNat]
                          exact m7_p2_fwd_lm_set_iff hlml hdwt.1.core_ok.cur_vars_le hli_lt hli_at.1
                            hli_eq hlm_tk
                        c0_hsteps_nogrp
                        refine wp_join_state (ts := [i32, i32]) (α := BitVec 32 × BitVec 32)
                          (fun x => (x.1, x.2, ()))
                          (fun x mj =>
                            x.1.toNat ∈ fullArenaClauseLits st cref.toNat ∧
                            (FullMem c { st with core := { st.core with
                              lit_mark := lm'.set (li.setWidth 64).toNat 1#8 } } ⋆ R) mj)
                          (fun _ ⟨ml', md'⟩ mj ⟨hml_m, hmj⟩ => by
                            c0_hsteps!
                            exact hLm (sz.toNat - (i + 1#32).toNat) (i + 1#32, ml', md', ()) mj
                              (by omega) ⟨lm'.set (li.setWidth 64).toNat 1#8, by simp [hlml],
                               by omega, rfl, hml_m, hlm_next, hmj⟩)
                          (fun J68 hJ68 => by
                            c0_hsplit
                            · c0_hsteps!; exact hJ68 (li, _) _ ⟨hli_mem, by assumption⟩
                            · c0_hsteps!; exact hJ68 (min_l, min_deg) _ ⟨hml_mem, by assumption⟩)
                      · -- Scan loop: call `full_fwd_scan_lit_m7` on `l` and `l ^ 1`
                        have hi_eq : i.toNat = sz.toNat := by omega
                        have hC_len : (fullArenaClauseLits st cref.toNat).length = sz.toNat :=
                          m7_p2_fwd_cl_lits_len hdwt href_t hszt
                        have hlm_full : ∀ x < 2 * c.max_vars,
                            lm'[x]?.getD 0#8 ≠ 0#8 ↔ x ∈ fullArenaClauseLits st cref.toNat := by
                          intro x hx
                          simpa only [hi_eq, ← hC_len, List.take_length] using hlm_tk x hx
                        have hlen_sm : sm.LengthsOk c :=
                          ⟨{ hdwt.1.core_ok with lit_mark_len := hlml }, hdwt.1.scratch_ok⟩
                        have hw_sm : FullWitnessInv c F0 F_cur sm.core :=
                          { hdwt.2.1 with
                            arena := { hdwt.2.1.arena with len_ok := hdwt.2.1.arena.len_ok }
                            watches :=
                              hdwt.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }
                        c0_hsteps_nogrp
                        refine wp_loop_break_group (brkTs := [i32, i32, .bool]) (lpTs := [i32])
                          (fun (drop_s, _, sub_s, ()) m_s => m_s = mm ∧
                            (sub_s = false → drop_s ≠ 0xFFFFFFFF#32 →
                              (cnfOfClauses F_cur).EntailsClause
                                (cnfClause ((fullArenaClauseLits st cref.toNat).filter
                                  (· != drop_s.toNat)))))
                          (fun rem_s (is, ()) m_s => m_s = mm ∧
                            is.toNat ≤ sz.toNat ∧ rem_s = sz.toNat - is.toNat)
                          ?_ ?_ ?_
                        · rintro _ ⟨drop_s, _, sub_s, ⟨⟩⟩ m_s ⟨rfl, hscan_post⟩
                          -- Unmark `lm` for all `i < sz`
                          c0_hsteps_nogrp
                          refine wp_loop_group (ts := [i32])
                            (fun rem_u (iu, ()) mu => ∃ lm_u : List (BitVec 8),
                              let su' : FullState :=
                                { st with core := { st.core with lit_mark := lm_u } }
                              lm_u.length = 2 * c.max_vars ∧
                              iu.toNat ≤ sz.toNat ∧ rem_u = sz.toNat - iu.toNat ∧
                              (∀ x < 2 * c.max_vars,
                                lm_u[x]?.getD 0#8 ≠ 0#8 →
                                  x ∈ (fullArenaClauseLits st cref.toNat).drop iu.toNat) ∧
                              (FullMem c su' ⋆ R) mu)
                            ?_ ?_
                          · rintro Lu rem_u ⟨iu, ⟨⟩⟩ mu hLu ⟨lm_u, hlmu, hiu_le, rfl, hrem_lm, hmu⟩
                            c0_hsplit
                            · have hiu_lt : iu.toNat < sz.toNat := hc
                              obtain ⟨hcri, hli_lm, hiu1, hlm_next⟩ :=
                                m7_p2_unmark_iter hdwt href_t hngt hszt hlmu hiu_lt hrem_lm
                              c0_hsteps!
                              exact hLu (sz.toNat - (iu + 1#32).toNat) (iu + 1#32, ()) _ (by omega)
                                ⟨_, by simp [hlmu], by omega, rfl, hlm_next, hm⟩
                            · have hiu_eq : iu.toNat = sz.toNat := by omega
                              have hlm_clr : ∀ x < 2 * c.max_vars, lm_u[x]?.getD 0#8 = 0#8 :=
                                fun x hx => Classical.byContradiction fun hnz => by
                                  have hmem := hrem_lm x hx hnz
                                  rw [hiu_eq, ← hC_len, List.drop_length] at hmem
                                  cases hmem
                              let su_clr : FullState :=
                                { st with core := { st.core with lit_mark := lm_u } }
                              have hdw_clr := m7_p2_fullDenseInvW_with_lit_mark hdwt hlmu hlm_clr
                              c0_hsteps!
                              exact hJm (sub_s, drop_s, _, su_clr) mu
                                ⟨rfl, rfl, rfl, rfl, rfl, hdw_clr, hscan_post, hmu⟩
                          · intro Lu hLu; c0_hsteps!
                            exact hLu sz.toNat (0#32, ()) _
                              ⟨lm', hlml, Nat.zero_le _, by simp,
                                fun x hx hnz => (hlm_full x hx).mp hnz, hmm⟩
                        · rintro Bs Ls rem_s ⟨is, ⟨⟩⟩ m_s hBs hLs ⟨rfl, his_le, rfl⟩
                          c0_hsplit
                          · have his_lt : is.toNat < sz.toNat := hc
                            have hcri : (cref.setWidth 64 + 3#64 + is.setWidth 64).toNat <
                                st.core.arena.length := by
                              rw [hdwt.1.core_ok.arena_len_arr]; c0_bound
                            have hli_mem : (st.core.arena[(cref.setWidth 64 + 3#64 +
                                is.setWidth 64).toNat]'hcri).toNat ∈
                                fullArenaClauseLits st cref.toNat := by
                              have hat := m7_p2_fwd_cl_lit_at hdwt href_t hszt his_lt
                              have hli_eq : (fullArenaClauseLits st cref.toNat)[is.toNat]'hat.1 =
                                  (st.core.arena[(cref.setWidth 64 + 3#64 +
                                    is.setWidth 64).toNat]'hcri).toNat :=
                                hat.2.trans (congrArg BitVec.toNat
                                  (m6_getElem_congr (by c0_bound) _ hcri))
                              rw [← hli_eq]; exact List.getElem_mem hat.1
                            have hl0_mem : (st.core.arena[(cref.setWidth 64 + 3#64).toNat]'
                                hcr3_t).toNat ∈ fullArenaClauseLits st cref.toNat := by
                              have hat := m7_p2_fwd_cl_lit_at hdwt href_t hszt (i := 0) (by omega)
                              have hl0_eq : (fullArenaClauseLits st cref.toNat)[0]'hat.1 =
                                  (st.core.arena[(cref.setWidth 64 + 3#64).toNat]'hcr3_t).toNat :=
                                hat.2.trans (congrArg BitVec.toNat
                                  (m6_getElem_congr (by c0_bound) _ hcr3_t))
                              rw [← hl0_eq]; exact List.getElem_mem hat.1
                            have his1 : (is + 1#32).toNat = is.toNat + 1 := by c0_bound
                            c0_hsplit
                            c0_hsplit
                            · -- `l = (is == 0 ? min_l : ar[cref+3+is])`, swap if `l == min_l`
                              refine wp_join_state_pure (ts := [i32]) (α := BitVec 32)
                                (fun l => (l, ()))
                                (fun l => l.toNat ∈ fullArenaClauseLits st cref.toNat)
                                (fun _ l1 hl1_mem => by
                                  refine wp_join_state_pure (ts := [i32]) (α := BitVec 32)
                                    (fun l => (l, ()))
                                    (fun l => l.toNat ∈ fullArenaClauseLits st cref.toNat)
                                    (fun _ l_use hl_mem => by
                                      have hl_lt : l_use.toNat < 2 * sm.core.cur_vars :=
                                        hdwt.2.1.arena.lits_lt cref.toNat href_t hngt _ hl_mem
                                      have hln_lt :
                                          (l_use ^^^ 1#32).toNat < 2 * sm.core.cur_vars := by
                                        change l_use.toNat ^^^ 1 < 2 * sm.core.cur_vars
                                        have := fullInv_var_xor1 l_use.toNat; omega
                                      c0_hsteps_nogrp
                                      m7_call hScanLit
                                      refine fullFwdScanLitM7Spec_intro rfl hlen_sm hw_sm
                                        hdwt.2.2.2.2.2.1 hdwt.2.2.2.2.2.2 hdwt.2.2.2.1 href_t
                                        hngt hszt hl_lt (fun _ => hl_mem)
                                        (fun x hx => hlm_full x (Nat.lt_of_lt_of_le hx
                                          (Nat.mul_le_mul_left 2 hdwt.1.core_ok.cur_vars_le)))
                                        hmm ?_
                                      intro r1 hr1
                                      c0_hsplit
                                      · c0_hsteps!
                                        exact hBs (drop_b, is, true, ()) _ ⟨rfl, by simp⟩
                                      · c0_hsplit
                                        · have hr1_ent : (cnfOfClauses F_cur).EntailsClause
                                              (cnfClause ((fullArenaClauseLits st cref.toNat).filter
                                                (· != r1.toNat))) := by
                                            rcases hr1 with h1 | h2 | ⟨_, h3⟩
                                            · exact absurd h1 hc
                                            · exact absurd h2 ‹r1 ≠ 0xFFFFFFFE#32›
                                            · exact h3
                                          c0_hsteps!
                                          exact hBs (r1, _, false, ()) _
                                            ⟨rfl, fun _ _ => hr1_ent⟩
                                        · c0_hsteps_nogrp
                                          m7_call hScanLit
                                          refine fullFwdScanLitM7Spec_intro rfl hlen_sm hw_sm
                                            hdwt.2.2.2.2.2.1 hdwt.2.2.2.2.2.2 hdwt.2.2.2.1
                                            href_t hngt hszt hln_lt
                                            (fun h => False.elim (Bool.noConfusion h))
                                            (fun x hx => hlm_full x (Nat.lt_of_lt_of_le hx
                                              (Nat.mul_le_mul_left 2 hdwt.1.core_ok.cur_vars_le)))
                                            hmm ?_
                                          intro r2 hr2
                                          c0_hsplit
                                          · c0_hsteps!
                                            exact hBs (drop_b, is, true, ()) _ ⟨rfl, by simp⟩
                                          · c0_hsplit
                                            · have hr2_ent : (cnfOfClauses F_cur).EntailsClause
                                                  (cnfClause ((fullArenaClauseLits st
                                                    cref.toNat).filter (· != r2.toNat))) := by
                                                rcases hr2 with h1 | h2 | ⟨_, h3⟩
                                                · exact absurd h1 hc
                                                · exact absurd h2 ‹r2 ≠ 0xFFFFFFFE#32›
                                                · exact h3
                                              c0_hsteps!
                                              exact hBs (r2, _, false, ()) _
                                                ⟨rfl, fun _ _ => hr2_ent⟩
                                            · c0_hsteps!
                                              exact hLs (sz.toNat - (is + 1#32).toNat)
                                                (is + 1#32, ()) _ (by omega) ⟨rfl, by omega, rfl⟩)
                                    (fun Jl2 hJl2 => by
                                      c0_hsplit
                                      · c0_hsplit
                                        · c0_hsteps!; exact hJl2 _ hl0_mem
                                        · c0_hsteps!; exact hJl2 l1 hl1_mem
                                      · c0_hsteps!; exact hJl2 l1 hl1_mem))
                                (fun Jl1 hJl1 => by
                                  c0_hsplit
                                  · c0_hsteps!; exact hJl1 min_l hml_mem
                                  · c0_hsteps!; exact hJl1 _ hli_mem)
                            · c0_hsteps!; exact absurd hdrop_ff hc
                          · c0_hsteps!
                            exact hBs (drop_b, is, false, ()) _
                              ⟨rfl, fun _ h => absurd hdrop_ff h⟩
                        · intro _ Ls _ hLs; c0_hsteps!
                          exact hLs sz.toNat (0#32, ()) _ ⟨rfl, Nat.zero_le _, by simp⟩
                    · intro Lm hLm; c0_hsteps!
                      have hl0_mem : (st.core.arena[(cref.setWidth 64 + 3#64).toNat]'
                          hcr3_t).toNat ∈ fullArenaClauseLits st cref.toNat := by
                        have hat := m7_p2_fwd_cl_lit_at hdwt href_t hszt (i := 0) (by omega)
                        have hl0_eq : (fullArenaClauseLits st cref.toNat)[0]'hat.1 =
                            (st.core.arena[(cref.setWidth 64 + 3#64).toNat]'hcr3_t).toNat :=
                          hat.2.trans (congrArg BitVec.toNat
                            (m6_getElem_congr (by c0_bound) _ hcr3_t))
                        rw [← hl0_eq]; exact List.getElem_mem hat.1
                      exact hLm sz.toNat (0#32, _, _, ()) _
                        ⟨st.core.lit_mark, hdwt.1.core_ok.lit_mark_len, Nat.zero_le _, by simp,
                         hl0_mem, fun x hx => by
                           rw [show (0#32).toNat = 0 from rfl]
                           simp only [List.take_zero, List.not_mem_nil]
                           exact ⟨fun h => h (hdwt.2.2.1.2 x hx), False.elim⟩, hms⟩
                  · c0_hsteps!
                    exact hJm (false, drop_b, _, _) _
                      ⟨rfl, rfl, rfl, rfl, rfl, hdwt, fun _ hne => hdrop_ent0 hne, hms⟩)
          · rintro Bi Li rem_i ⟨drop_i, i, ⟨⟩⟩ mi hBi hLi ⟨rfl, hi_le, rfl, hdrop_ok⟩
            c0_hsplit
            · have hi_lt : i.toNat < sz.toNat := hc
              have hcri :
                  (cref.setWidth 64 + 3#64 + i.setWidth 64).toNat < st.core.arena.length := by
                rw [hdwt.1.core_ok.arena_len_arr]; c0_bound
              let li := st.core.arena[(cref.setWidth 64 + 3#64 + i.setWidth 64).toNat]'hcri
              have hli_lt : li.toNat < 2 * st.core.cur_vars := by
                have hmem : li.toNat ∈ fullArenaClauseLitsCore st.core cref.toNat := by
                  rw [mem_fullArenaClauseLitsCore_iff (by rw [hdwt.1.core_ok.arena_len_arr]; omega)]
                  exact ⟨i.toNat, by omega,
                    congrArg BitVec.toNat (m6_getElem_congr (by c0_bound) _ _)⟩
                exact hdwt.2.1.arena.lits_lt cref.toNat href_t hngt _ hmem
              have hli_v : (li.setWidth 64).toNat < st.core.vals.length := by
                rw [hdwt.1.core_ok.vals_len, m6_zext32_toNat]; have := hdwt.1.core_ok.cur_vars_le
                omega
              have hi1 : (i + 1#32).toNat = i.toNat + 1 := by c0_bound
              c0_hsplit
              · c0_hsteps!; exact hBi (true, drop_i, i, ()) _ ⟨rfl, by simp⟩
              · refine wp_join_state_pure (ts := [i32]) (α := BitVec 32) (fun d => (d, ()))
                  (fun d => d ≠ 0xFFFFFFFF#32 →
                    d.toNat < 2 * st.core.cur_vars ∧ st.core.vals[d.toNat]?.getD 0#8 = 0xFF#8)
                  (fun _ d hd => by
                    c0_hsteps!
                    exact hLi (sz.toNat - (i + 1#32).toNat) (d, i + 1#32, ()) _ (by omega)
                      ⟨rfl, by omega, rfl, hd⟩)
                  (fun Jd hJd => by
                    c0_hsplit
                    · have hff_i : st.core.vals[li.toNat]?.getD 0#8 = 0xFF#8 := by
                        have hdom := hdwt.2.1.vals_domain li.toNat hli_lt
                        have hlt_v : li.toNat < st.core.vals.length := by
                          rw [hdwt.1.core_ok.vals_len]; have := hdwt.1.core_ok.cur_vars_le; omega
                        have hli_idx : (cref.toNat + BitVec.toNat (3 : BitVec 64) +
                            i.toNat) % 2 ^ 64 =
                            (cref.setWidth 64 + 3#64 + i.setWidth 64).toNat := by
                          have := hdwt.2.1.arena.refs_wf cref.toNat href_t
                          have := hdwt.1.core_ok.arena_len_le
                          rw [BitVec.toNat_add, BitVec.toNat_add, m6_zext32_toNat,
                            m6_zext32_toNat, show (3#64).toNat = 3 from rfl,
                            show BitVec.toNat (3 : BitVec 64) = 3 from rfl,
                            Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
                            Nat.mod_eq_of_lt (by omega)]
                        have hli_c0 : st.core.arena[(cref.toNat + BitVec.toNat (3 : BitVec 64) +
                            i.toNat) % 2 ^ 64]'(by rw [hli_idx]; exact hcri) = li :=
                          m6_getElem_congr hli_idx (by rw [hli_idx]; exact hcri) hcri
                        have hval_c0 :
                            st.core.vals[(st.core.arena[(cref.toNat +
                                BitVec.toNat (3 : BitVec 64) + i.toNat) % 2 ^ 64]'(by
                                  rw [hli_idx]; exact hcri)).toNat]'(by
                                    rw [hli_c0]; exact hlt_v) =
                              st.core.vals[li.toNat]'hlt_v :=
                          m6_getElem_congr (congrArg BitVec.toNat hli_c0) _ hlt_v
                        rw [List.getElem?_eq_getElem hlt_v, Option.getD_some] at hdom ⊢
                        exact m6_bv8_dom_neg_slt hdom (by simpa only [hval_c0] using hc)
                      c0_hsplit
                      · c0_hsteps!; exact hJd li (fun _ => ⟨hli_lt, hff_i⟩)
                      · c0_hsteps!; exact hJd drop_i hdrop_ok
                    · c0_hsteps!; exact hJd drop_i hdrop_ok)
            · c0_hsteps!; exact hBi (false, drop_i, i, ()) _ ⟨rfl, fun _ => hdrop_ok⟩
          · intro _ Li _ hLi; c0_hsteps!
            exact hLi sz.toNat (0xFFFFFFFF#32, 0#32, ()) _
              ⟨rfl, Nat.zero_le _, by simp, fun h => absurd rfl h⟩
        · exact absurd hc (by decide)
      · intro L hL; c0_hsteps!
        exact hL sz0.toNat (hdr0, sz0, ()) m0
          ⟨s0, rfl, by omega, hdw0, rfl, rfl, rfl, rfl, rfl, rfl, hhdr0_eq, hsz0_eq, hng0, hm0⟩

/-- Canonical `Full.fullFwdCheckClSpec` corollary for `full_fwd_check_cl_m7`. -/
theorem full_fwd_check_cl_m7_wp_canon (Γ : Env)
    (hScanLit : ∀ a m Q X, fullFwdScanLitM7Spec a m Q X →
      Γ "full_fwd_scan_lit_m7" [i64, i32, i32, i32, .bool] [i32] a m Q X)
    (hUnwatch : ∀ a m Q X, fullUnwatchLargeSpec a m Q X →
      Γ "full_unwatch_large" [i64, i32, i32] [] a m Q X)
    (hAddUnit : ∀ a m Q X, fullAddUnitSpec a m Q X →
      Γ "full_add_unit" [i64, i32] [.bool] a m Q X)
    (hAddBin : ∀ a m Q X, fullAddBinSpec a m Q X →
      Γ "full_add_bin" [i64, i32, i32] [i64] a m Q X)
    (hFlushUnits : ∀ a m Q X, fullDenseFlushUnitsM6Spec a m Q X →
      Γ "full_dense_flush_units_m7" [i64] [.bool] a m Q X) :
    ∀ a m Q X, Full.fullFwdCheckClSpec a m Q X →
      Func.wp Γ full_fwd_check_cl_m7_body a m Q X :=
  fun _ _ _ _ h =>
    full_fwd_check_cl_m7_wp Γ hScanLit hUnwatch hAddUnit hAddBin hFlushUnits _ _ _ _
      (fullFwdCheckClM7Spec_of_canon h)

/-! ## 4. `full_forward_sub_m7` (Canonical `FullFastBveBudgets.fullForwardSubFastSpec`) -/

/-- Parametric `Func.wp` proof for `full_forward_sub_m7`, directly certifying canonical
`FullFastBveBudgets.fullForwardSubFastSpec`. -/
theorem full_forward_sub_m7_wp (Γ : Env)
    (hDedup : ∀ a m Q X, fullFwdDedupBinsSpec a m Q X →
      Γ "full_fwd_dedup_bins" [i64] [.bool] a m Q X)
    (hFlushUnits : ∀ a m Q X, fullDenseFlushUnitsM6Spec a m Q X →
      Γ "full_dense_flush_units_m7" [i64] [.bool] a m Q X)
    (hCollectSort : ∀ a m Q X, fullFwdCollectSortM6Spec a m Q X →
      Γ "full_fwd_collect_sort_m7" [i64] [i64] a m Q X)
    (hFlushLarge : ∀ a m Q X, fullFwdFlushLargeM6Spec a m Q X →
      Γ "full_fwd_flush_large_m7" [i64] [] a m Q X)
    (hCheckCl : ∀ a m Q X, fullFwdCheckClM7Spec a m Q X →
      Γ "full_fwd_check_cl_m7" [i64, i32] [.bool] a m Q X)
    (hConnectSub : ∀ a m Q X, fullFwdConnectSubsumerM6Spec a m Q X →
      Γ "full_fwd_connect_subsumer_m7" [i64, i32] [] a m Q X)
    (hArenaNext : ∀ a m Q X, fullArenaNextSpec a m Q X →
      Γ "full_arena_next" [i64, i32] [i32] a m Q X)
    (hReconnect : ∀ a m Q X, fullFwdReconnectIrredM6Spec a m Q X →
      Γ "full_fwd_reconnect_irred_m7" [i64] [] a m Q X) :
    ∀ a m Q X, fullForwardSubFastSpec a m Q X →
      Func.wp Γ full_forward_sub_m7_body a m Q X := by
  rintro ⟨h, budget, ⟨⟩⟩ m0 Q X ⟨c, F0, s0, R, rfl, hd0, hm0, hQ⟩
  have hmx := c.hmaxv; have harc := c.harena; have hrc := c.hred
  unfold dimacsBound at hmx harc hrc
  obtain ⟨F_cur, hw0⟩ := hd0.exists_witness
  unfold Func.wp full_forward_sub_m7_body
  c0_hsplit
  · c0_hsteps!; exact hQ 1#64 s0 m0 hd0 rfl rfl (Or.inl rfl) (by simp) hm0
  · c0_hsteps_nogrp
    m7_call hDedup
    refine ⟨c, F0, F_cur, s0, R, rfl, hw0, hm0, ?_⟩
    intro ok1 s1 m1 hdw1 hcv1 hfl1 hf1 hm1
    c0_hsplit
    · c0_hsteps_nogrp
      m7_call hFlushUnits
      refine fullDenseFlushUnitsM6Spec_intro rfl hdw1 hm1 ?_
      intro ok2 s2 m2 hdw2 hcv2 _ hfl2 _ _ _ _ _ _ _ hf2 hm2
      c0_hsplit
      · c0_hsteps_nogrp
        m7_call hCollectSort
        refine fullFwdCollectSortM6Spec_intro rfl hdw2 hm2 ?_
        intro ncand s3 m3 hdw3 hcv3 hal3 hfl3 _ _ _ hnc_le hrr3 hm3
        c0_hsplit
        · c0_hsteps_nogrp
          refine wp_join_state_pure (ts := [i64]) (α := BitVec 64) (fun r => (r, ()))
            (fun r => (r = 1#64 ∨ r = 20#64) ∧ (r = 20#64 → F0.Unsat))
            (fun _ r ⟨hr_disj, hr20⟩ => by
              c0_hsteps!
              exact hQ r s3 m3 hdw3.toDense (hcv3.trans (hcv2.trans hcv1))
                (hfl3.trans (hfl2.trans hfl1)) hr_disj hr20 hm3)
            (fun J7 hJ7 => by
              c0_hsplit
              · c0_hsteps!
                exact hJ7 20#64 ⟨Or.inr rfl, fun _ =>
                  hdw3.2.1.ext_sound.2 (hdw3.2.1.inconsistent_sound hc)⟩
              · c0_hsteps!; exact hJ7 1#64 ⟨Or.inl rfl, by simp⟩)
        · c0_hsteps_nogrp
          m7_call hFlushLarge
          refine fullFwdFlushLargeM6Spec_intro rfl hdw3 hm3 ?_
          intro s4 m4 hdw4 hcv4 har4 hal4 hfl4 _ _ _ hrr4 _ _ _ _ hm4
          have hrr4_ok : ∀ k < ncand.toNat,
              (s4.scratch.red_refs[k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s4 := by
            intro k hk; rw [hrr4]
            have hrefs4 : fullArenaClauseRefs s4 = fullArenaClauseRefs s3 := by
              unfold fullArenaClauseRefs fullArenaClauseRefsCore; rw [har4, hal4]
            rw [hrefs4]; exact hrr3 k hk
          c0_hsteps_nogrp
          -- Main forward-subsumption candidate loop
          refine wp_loop_group (ts := [i64, i64])
            (fun r_lp (i, rem, ()) ml => ∃ sl : FullState,
              i.toNat ≤ ncand.toNat ∧ r_lp = ncand.toNat - i.toNat ∧
              FullDenseInvW c F0 F_cur sl ∧
              sl.core.cur_vars = s0.core.cur_vars ∧ sl.core.fuel = s0.core.fuel ∧
              fullArenaClauseRefs sl = fullArenaClauseRefs s4 ∧
              sl.scratch.red_refs = s4.scratch.red_refs ∧
              (FullMem c sl ⋆ R) ml)
            ?_ ?_
          · rintro L r_lp ⟨i, rem, ⟨⟩⟩ ml hL
              ⟨sl, hi_le, rfl, hdwl, hcvl, hfll, hrefsl, hrrl, hml⟩
            refine wp_join0 (P := fun mb => mb = ml)
              (fun _ mb hmb => by
                rcases hmb.symm with rfl
                -- Optional `FL_SUBSUME` clearing & `PH_SUBSUME` reactivation pass
                refine wp_join_state (ts := []) (α := FullState) (fun _ => ())
                  (fun sf mf =>
                    FullDenseInvW c F0 F_cur sf ∧
                    sf.core.cur_vars = s0.core.cur_vars ∧ sf.core.fuel = s0.core.fuel ∧
                    (FullMem c sf ⋆ R) mf)
                  (fun _ sf mf ⟨hdwf, hcvf, hflf, hmf⟩ => by
                    c0_hsteps_nogrp
                    c0_hsplit
                    · c0_hsteps!
                      exact hQ 20#64 sf mf hdwf.toDense hcvf hflf (Or.inr rfl)
                        (fun _ => hdwf.2.1.ext_sound.2 (hdwf.2.1.inconsistent_sound hc)) hmf
                    · c0_hsteps_nogrp
                      m7_call hFlushUnits
                      refine fullDenseFlushUnitsM6Spec_intro rfl hdwf hmf ?_
                      intro ok_f s5 m5 hdw5 hcv5 _ hfl5 _ _ _ _ _ _ _ hf5 hm5
                      c0_hsplit
                      · c0_hsteps_nogrp
                        m7_call hReconnect
                        refine fullFwdReconnectIrredM6Spec_intro rfl hdw5 hm5 ?_
                        intro s6 m6 hdw6 hcv6 _ hfl6 _ _ hm6
                        c0_hsplit
                        · c0_hsteps_nogrp
                          refine wp_join_state_pure (ts := [i64]) (α := BitVec 64)
                            (fun r => (r, ()))
                            (fun r => (r = 1#64 ∨ r = 20#64) ∧ (r = 20#64 → F0.Unsat))
                            (fun _ r ⟨hr_disj, hr20⟩ => by
                              c0_hsteps!
                              exact hQ r s6 m6 hdw6.toDense (hcv6.trans (hcv5.trans hcvf))
                                (hfl6.trans (hfl5.trans hflf)) hr_disj hr20 hm6)
                            (fun J20 hJ20 => by
                              c0_hsplit
                              · c0_hsteps!
                                exact hJ20 20#64 ⟨Or.inr rfl, fun _ =>
                                  hdw6.2.1.ext_sound.2 (hdw6.2.1.inconsistent_sound hc)⟩
                              · c0_hsteps!; exact hJ20 1#64 ⟨Or.inl rfl, by simp⟩)
                      · c0_hsteps!
                        exact hQ 20#64 s5 m5 hdw5.toDense (hcv5.trans hcvf) (hfl5.trans hflf)
                          (Or.inr rfl) (fun _ => hf5 (by simpa using hc)) hm5)
                  (fun Jc hJc => by
                    c0_hsplit
                    · c0_hsplit
                      · c0_hsplit
                        · -- Clear `FL_SUBSUME` on all `v < cv`, then scan arena for `PH_SUBSUME`
                          have hcvl_le := hdwl.1.core_ok.cur_vars_le
                          c0_hsteps_nogrp
                          refine wp_loop_group (ts := [i64])
                            (fun rem_v (v, ()) mv => ∃ fl_v : List (BitVec 32),
                              let sv : FullState :=
                                { sl with core := { sl.core with flags := fl_v } }
                              fl_v.length = c.max_vars ∧ v.toNat ≤ sl.core.cur_vars ∧
                              rem_v = sl.core.cur_vars - v.toNat ∧ (FullMem c sv ⋆ R) mv)
                            ?_ ?_
                          · rintro Lv rem_v ⟨v, ⟨⟩⟩ mv hLv ⟨fl_v, hflv, hv_le, rfl, hmv⟩
                            c0_hsplit
                            · have hv_lt : v.toNat < sl.core.cur_vars := by
                                rw [Nat.mod_eq_of_lt (by omega)] at hc; exact hc
                              have hv_fl : v.toNat < fl_v.length := by omega
                              have hv1 : (v + 1#64).toNat = v.toNat + 1 := by c0_bound
                              c0_hsteps!
                              exact hLv (sl.core.cur_vars - (v + 1#64).toNat) (v + 1#64, ()) _
                                (by omega) ⟨_, by simp [hflv], by omega, rfl, hm⟩
                            · let sv0 : FullState :=
                                { sl with core := { sl.core with flags := fl_v } }
                              have hdw_v0 : FullDenseInvW c F0 F_cur sv0 :=
                                m6_fullDenseInvW_with_flags hdwl hflv
                              c0_hsteps_nogrp
                              refine wp_loop_group (ts := [i64])
                                (fun rem_p (p, ()) mp => ∃ sp : FullState,
                                  p.toNat ≤ sp.core.arena_len ∧
                                  rem_p = sp.core.arena_len - p.toNat ∧
                                  (p.toNat = sp.core.arena_len ∨ p.toNat ∈ fullArenaClauseRefs sp) ∧
                                  FullDenseInvW c F0 F_cur sp ∧
                                  sp.core.cur_vars = s0.core.cur_vars ∧
                                  sp.core.arena_len = sl.core.arena_len ∧
                                  sp.core.fuel = s0.core.fuel ∧
                                  (FullMem c sp ⋆ R) mp)
                                ?_ ?_
                              · rintro Lp rem_p ⟨p, ⟨⟩⟩ mp hLp
                                  ⟨sp, hp_le, rfl, hp_mem, hdwp, hcvp, halp, hflp, hmp⟩
                                have hal_p := hdwp.1.core_ok.arena_len_le
                                c0_hsplit
                                · have hp_lt : p.toNat < sp.core.arena_len := by
                                    rw [Nat.mod_eq_of_lt (by omega)] at hc; exact hc
                                  have hp_ref : p.toNat ∈ fullArenaClauseRefs sp :=
                                    hp_mem.resolve_left (by omega)
                                  have hwf_p := hdwp.2.1.arena.refs_wf p.toNat hp_ref
                                  have hp_ar : p.toNat < sp.core.arena.length := by
                                    rw [hdwp.1.core_ok.arena_len_arr]; omega
                                  have hp2_ar : (p + 2#64).toNat < sp.core.arena.length := by
                                    rw [hdwp.1.core_ok.arena_len_arr]; c0_bound
                                  have hp32 : (p.setWidth 32).toNat = p.toNat := by
                                    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
                                  let hdr_p := sp.core.arena[p.toNat]'hp_ar
                                  let sz_p := sp.core.arena[(p + 2#64).toNat]'hp2_ar
                                  have hsz_p :
                                      sz_p.toNat = fullArenaClauseSizeCore sp.core p.toNat := by
                                    unfold sz_p fullArenaClauseSizeCore
                                    rw [List.getElem?_eq_getElem (by
                                      rw [hdwp.1.core_ok.arena_len_arr]; omega), Option.getD_some]
                                    exact congrArg BitVec.toNat (m6_getElem_congr (by c0_bound) _ _)
                                  c0_hsteps_nogrp
                                  m7_call hArenaNext
                                  dsimp only [vals, Arg.val]
                                  refine ⟨c, sp, R, rfl, hdwp.1, hmp, ?_⟩
                                  have hnb := fullArenaNextOff_bounds (ar := sp.core.arena)
                                    (alen := sp.core.arena_len) (cref := p.toNat) hwf_p.1
                                  have hnp_mem :=
                                    FullDenseWatchHelpers.fullArenaClauseRefs_next_mem
                                      hdwp.2.1.arena hp_ref
                                  let np := (BitVec.ofNat 32 (fullArenaNextOff sp.core.arena
                                    sp.core.arena_len (p.setWidth 32).toNat)).setWidth 64
                                  have hnp_toNat : np.toNat =
                                      fullArenaNextOff sp.core.arena sp.core.arena_len p.toNat := by
                                    dsimp only [np]; rw [hp32, m6_zext32_toNat, BitVec.toNat_ofNat,
                                      Nat.mod_eq_of_lt (by omega)]
                                  c0_hsteps_nogrp
                                  refine wp_join0 (P := fun mj => ∃ sj : FullState,
                                      FullDenseInvW c F0 F_cur sj ∧
                                      sj.core.cur_vars = s0.core.cur_vars ∧
                                      sj.core.arena_len = sl.core.arena_len ∧
                                      sj.core.fuel = s0.core.fuel ∧
                                      fullArenaClauseRefs sj = fullArenaClauseRefs sp ∧
                                      (FullMem c sj ⋆ R) mj)
                                    (fun _ mj ⟨sj, hdwj, hcvj, halj, hflj, hrefsj, hmj⟩ => by
                                      c0_hsteps!
                                      exact hLp (sj.core.arena_len - np.toNat) (np, ()) mj
                                        (by omega) ⟨sj, by omega, rfl, by
                                          rw [hnp_toNat, halj, ← halp, hrefsj]; exact hnp_mem,
                                         hdwj, hcvj, halj, hflj, hmj⟩)
                                    (fun Jp hJp => by
                                      c0_hsplit
                                      · c0_hsteps_nogrp
                                        let v' := hdr_p &&& ~~~0x01000000#32
                                        let sc : FullState :=
                                          { sp with core := { sp.core with
                                            arena := sp.core.arena.set p.toNat v' } }
                                        have hhdr_eq : hdr_p = fullArenaHdr sp p.toNat := by
                                          unfold hdr_p fullArenaHdr fullArenaHdrCore
                                          rw [List.getElem?_eq_getElem hp_ar, Option.getD_some]
                                        have hcb := m6_bit24_clear_pres hdr_p
                                        have hset := m6_fullDenseInvW_set_hdr_bit24 hdwp hp_ref
                                          (v' := v') (by rw [← hhdr_eq]; exact hcb.1)
                                          (by rw [← hhdr_eq]; exact hcb.2)
                                        refine wp_join0 (P := fun mj => ∃ sj : FullState,
                                            FullDenseInvW c F0 F_cur sj ∧
                                            sj.core.cur_vars = s0.core.cur_vars ∧
                                            sj.core.arena_len = sl.core.arena_len ∧
                                            sj.core.fuel = s0.core.fuel ∧
                                            fullArenaClauseRefs sj = fullArenaClauseRefs sp ∧
                                            (FullMem c sj ⋆ R) mj)
                                          (fun _ mj hmj => hJp mj hmj)
                                          (fun J52 hJ52 => by
                                            c0_hsplit
                                            · -- Live clause: re-arm `FL_SUBSUME | FL_ELIM_C`
                                              c0_hsteps_nogrp
                                              refine wp_loop_group (ts := [i32])
                                                (fun rem_k (k, ()) mk =>
                                                  ∃ fl_k : List (BitVec 32),
                                                    let sk : FullState :=
                                                      { sc with core := { sc.core with
                                                        flags := fl_k } }
                                                    fl_k.length = c.max_vars ∧
                                                    k.toNat ≤ sz_p.toNat ∧
                                                    rem_k = sz_p.toNat - k.toNat ∧
                                                    (FullMem c sk ⋆ R) mk)
                                                ?_ ?_
                                              · rintro Lk rem_k ⟨k, ⟨⟩⟩ mk hLk
                                                  ⟨fl_k, hflk, hk_le, rfl, hmk⟩
                                                c0_hsplit
                                                · have hk_lt : k.toNat < sz_p.toNat := hc
                                                  have hpi_ar : (p + 3#64 + k.setWidth 64).toNat <
                                                      sc.core.arena.length := by
                                                    rw [hset.1.1.core_ok.arena_len_arr]; c0_bound
                                                  have hk1 : (k + 1#32).toNat = k.toNat + 1 := by
                                                    c0_bound
                                                  c0_hsteps_nogrp
                                                  refine wp_join0 (P := fun mj => ∃ fl' : List
                                                      (BitVec 32),
                                                      fl'.length = c.max_vars ∧
                                                      (FullMem c { sc with core := { sc.core with
                                                        flags := fl' } } ⋆ R) mj)
                                                    (fun _ mj ⟨fl', hfl', hmj⟩ => by
                                                      c0_hsteps!
                                                      exact hLk (sz_p.toNat - (k + 1#32).toNat)
                                                        (k + 1#32, ()) mj (by omega)
                                                        ⟨fl', hfl', by omega, rfl, hmj⟩)
                                                    (fun J65 hJ65 => by
                                                      c0_hsplit
                                                      · have hlv_lt : ((sc.core.arena[(p + 3#64 +
                                                            k.setWidth 64).toNat]'hpi_ar >>>
                                                            (1 : Nat)).setWidth 64).toNat <
                                                            fl_k.length := by
                                                          have hpi_mod : (p + 3#64 +
                                                              k.setWidth 64).toNat =
                                                              (p.toNat + BitVec.toNat (3#64) +
                                                                k.toNat) % 2 ^ 64 := by
                                                            rw [BitVec.toNat_add, BitVec.toNat_add,
                                                              m6_zext32_toNat]
                                                            simp only [BitVec.toNat_ofNat]
                                                            c0_bound
                                                          have har_eq : sc.core.arena[(p.toNat +
                                                              BitVec.toNat (3#64) +
                                                              k.toNat) % 2 ^ 64]'(by
                                                                rw [hset.1.1.core_ok.arena_len_arr]
                                                                c0_bound) =
                                                              sc.core.arena[(p + 3#64 +
                                                                k.setWidth 64).toNat]'hpi_ar :=
                                                            m6_getElem_congr hpi_mod.symm _ _
                                                          have hcv_mod : sl.core.cur_vars % 2 ^ 64 =
                                                              sl.core.cur_vars :=
                                                            Nat.mod_eq_of_lt (by
                                                              rw [hcvl]; have :=
                                                                hset.1.1.core_ok.cur_vars_le
                                                              omega)
                                                          rw [hcv_mod] at hc
                                                          have hdiv_lt : (sc.core.arena[(p + 3#64 +
                                                              k.setWidth 64).toNat]'hpi_ar).toNat /
                                                              2 < sl.core.cur_vars := by
                                                            simpa [har_eq] using hc
                                                          have hsh1 :
                                                              ((sc.core.arena[(p + 3#64 +
                                                                    k.setWidth 64).toNat]'hpi_ar
                                                                  >>> (1 : Nat)) :
                                                                BitVec 32).toNat =
                                                              (sc.core.arena[(p + 3#64 +
                                                                  k.setWidth 64).toNat]'
                                                                  hpi_ar).toNat / 2 := by
                                                            rw [BitVec.toNat_ushiftRight,
                                                              Nat.shiftRight_eq_div_pow]
                                                          rw [hflk, m6_zext32_toNat, hsh1]
                                                          have := hset.1.1.core_ok.cur_vars_le
                                                          omega
                                                        c0_hsteps!
                                                        exact hJ65 _ ⟨_, by simp [hflk], hm⟩
                                                      · c0_hsteps!; exact hJ65 mk ⟨fl_k, hflk, hmk⟩)
                                                · c0_hsteps!
                                                  exact hJ52 mk ⟨{ sc with core := { sc.core with
                                                    flags := fl_k } },
                                                    m6_fullDenseInvW_with_flags hset.1 hflk,
                                                    hcvp, halp, hflp, hset.2.1, hmk⟩
                                              · intro Lk hLk; c0_hsteps!
                                                exact hLk sz_p.toNat (0#32, ()) m
                                                  ⟨sc.core.flags, hset.1.1.core_ok.flags_len,
                                                   Nat.zero_le _, by simp, hm⟩
                                            · refine wp_join0 (P := fun mj => ∃ sj : FullState,
                                                  FullDenseInvW c F0 F_cur sj ∧
                                                  sj.core.cur_vars = s0.core.cur_vars ∧
                                                  sj.core.arena_len = sl.core.arena_len ∧
                                                  sj.core.fuel = s0.core.fuel ∧
                                                  fullArenaClauseRefs sj = fullArenaClauseRefs sp ∧
                                                  (FullMem c sj ⋆ R) mj)
                                                (fun _ mj hmj => hJ52 mj hmj)
                                                (fun J55p hJ55p => by
                                                  c0_hsplit
                                                  · have hsz2 : 2 ≤ sz_p.toNat := hc
                                                    have hp3_ar : (p + 3#64).toNat <
                                                        sc.core.arena.length := by
                                                      rw [hset.1.1.core_ok.arena_len_arr]; c0_bound
                                                    have hp4_ar : (p + 4#64).toNat <
                                                        sc.core.arena.length := by
                                                      rw [hset.1.1.core_ok.arena_len_arr]; c0_bound
                                                    c0_hsteps_nogrp
                                                    refine wp_join_state (ts := [])
                                                      (α := List (BitVec 32)) (fun _ => ())
                                                      (fun fl1 m1 => fl1.length = c.max_vars ∧
                                                        (FullMem c { sc with core := { sc.core with
                                                          flags := fl1 } } ⋆ R) m1)
                                                      (fun _ fl1 m1 ⟨hfl1, hm1⟩ => by
                                                        c0_hsteps_nogrp
                                                        refine wp_join_state (ts := [])
                                                          (α := List (BitVec 32)) (fun _ => ())
                                                          (fun fl2 m2 => fl2.length = c.max_vars ∧
                                                            (FullMem c { sc with core :=
                                                              { sc.core with flags := fl2 } } ⋆ R)
                                                              m2)
                                                          (fun _ fl2 m2 ⟨hfl2, hm2⟩ => by
                                                            c0_hsteps!
                                                            let s_fl2 : FullState :=
                                                              { sc with core := { sc.core with
                                                                flags := fl2 } }
                                                            have hdw_fl2 :
                                                                FullDenseInvW c F0 F_cur s_fl2 :=
                                                              m6_fullDenseInvW_with_flags hset.1
                                                                hfl2
                                                            exact hJ55p m2 ⟨s_fl2, hdw_fl2,
                                                              hcvp, halp, hflp, hset.2.1, hm2⟩)
                                                          (fun J68 hJ68 => by
                                                            c0_hsplit
                                                            · have hv1_lt :
                                                                  ((sc.core.arena[(p +
                                                                    4#64).toNat]'hp4_ar >>>
                                                                    (1 : Nat)).setWidth 64).toNat <
                                                                    fl1.length := by
                                                                have hp4_mod : (p + 4#64).toNat =
                                                                    (p.toNat + BitVec.toNat 4#64) %
                                                                      2 ^ 64 := BitVec.toNat_add _ _
                                                                have hsp_len :
                                                                    sp.core.arena.length =
                                                                      c.arena_cap := by
                                                                  have h0 :=
                                                                    hset.1.1.core_ok.arena_len_arr
                                                                  simpa [sc] using h0
                                                                have hcv_mod : sl.core.cur_vars %
                                                                    2 ^ 64 = sl.core.cur_vars :=
                                                                  Nat.mod_eq_of_lt (by
                                                                    rw [hcvl]; have :=
                                                                      hset.1.1.core_ok.cur_vars_le
                                                                    omega)
                                                                rw [hcv_mod] at hc
                                                                have hne4 : p.toNat ≠
                                                                    (p.toNat + BitVec.toNat 4#64) %
                                                                      2 ^ 64 := by
                                                                  rw [← hp4_mod]; c0_bound
                                                                have hset_ne1 :
                                                                    (sp.core.arena.set p.toNat
                                                                      (sp.core.arena[p.toNat]'(by
                                                                        rw [hsp_len]; c0_bound) &&&
                                                                        ~~~(16777216 : BitVec 32)))[
                                                                        (p.toNat +
                                                                        BitVec.toNat 4#64) %
                                                                        2 ^ 64]'(by
                                                                          rw [List.length_set,
                                                                            hsp_len]
                                                                          c0_bound) =
                                                                      sp.core.arena[(p +
                                                                        4#64).toNat]'(by
                                                                          rw [hsp_len]; c0_bound) :=
                                                                  (List.getElem_set_ne hne4
                                                                    _).trans (m6_getElem_congr
                                                                      hp4_mod.symm _ _)
                                                                have hset_ne2 :
                                                                    sc.core.arena[(p +
                                                                      4#64).toNat]'hp4_ar =
                                                                      sp.core.arena[(p +
                                                                        4#64).toNat]'(by
                                                                          rw [hsp_len]; c0_bound) :=
                                                                  by
                                                                  dsimp only [sc]
                                                                  exact List.getElem_set_ne
                                                                    (by c0_bound) _
                                                                have hdiv_lt : (sc.core.arena[(p +
                                                                    4#64).toNat]'hp4_ar).toNat / 2
                                                                    < sl.core.cur_vars := by
                                                                  have hc' :
                                                                      ((sp.core.arena.set p.toNat
                                                                        (sp.core.arena[p.toNat]'(by
                                                                          rw [hsp_len]; c0_bound)
                                                                          &&& ~~~(16777216 :
                                                                            BitVec 32)))[(p.toNat +
                                                                          BitVec.toNat 4#64) %
                                                                          2 ^ 64]'(by
                                                                            rw [List.length_set,
                                                                              hsp_len]
                                                                            c0_bound)).toNat / 2 <
                                                                        sl.core.cur_vars := hc
                                                                  rw [hset_ne1] at hc'
                                                                  rw [hset_ne2]; exact hc'
                                                                have hsh1 : ((sc.core.arena[(p +
                                                                    4#64).toNat]'hp4_ar >>>
                                                                    (1 : Nat)) : BitVec 32).toNat =
                                                                    (sc.core.arena[(p +
                                                                      4#64).toNat]'hp4_ar).toNat /
                                                                      2 := by
                                                                  rw [BitVec.toNat_ushiftRight,
                                                                    Nat.shiftRight_eq_div_pow]
                                                                rw [hfl1, m6_zext32_toNat, hsh1]
                                                                have :=
                                                                  hset.1.1.core_ok.cur_vars_le
                                                                omega
                                                              c0_hsteps!
                                                              exact hJ68 _ _ ⟨by simp [hfl1], hm⟩
                                                            · c0_hsteps!
                                                              exact hJ68 fl1 m1 ⟨hfl1, hm1⟩))
                                                      (fun J67 hJ67 => by
                                                        c0_hsplit
                                                        · have hv0_lt :
                                                              ((sc.core.arena[(p + 3#64).toNat]'
                                                                hp3_ar >>> (1 : Nat)).setWidth
                                                                64).toNat < sc.core.flags.length :=
                                                            by
                                                              have hp3_mod : (p + 3#64).toNat =
                                                                  (p.toNat + BitVec.toNat 3#64) %
                                                                    2 ^ 64 := BitVec.toNat_add _ _
                                                              have hsp_len :
                                                                  sp.core.arena.length =
                                                                    c.arena_cap := by
                                                                have h0 :=
                                                                  hset.1.1.core_ok.arena_len_arr
                                                                simpa [sc] using h0
                                                              have hcv_mod : sl.core.cur_vars %
                                                                  2 ^ 64 = sl.core.cur_vars :=
                                                                Nat.mod_eq_of_lt (by
                                                                  rw [hcvl]; have :=
                                                                    hset.1.1.core_ok.cur_vars_le
                                                                  omega)
                                                              rw [hcv_mod] at hc
                                                              have hne3 : p.toNat ≠
                                                                  (p.toNat + BitVec.toNat 3#64) %
                                                                    2 ^ 64 := by
                                                                rw [← hp3_mod]; c0_bound
                                                              have hset_ne1 :
                                                                  (sp.core.arena.set p.toNat
                                                                    (sp.core.arena[p.toNat]'(by
                                                                      rw [hsp_len]; c0_bound) &&&
                                                                      ~~~(16777216 : BitVec 32)))[
                                                                      (p.toNat +
                                                                      BitVec.toNat 3#64) %
                                                                      2 ^ 64]'(by
                                                                        rw [List.length_set,
                                                                          hsp_len]
                                                                        c0_bound) =
                                                                    sp.core.arena[(p +
                                                                      3#64).toNat]'(by
                                                                        rw [hsp_len]; c0_bound) :=
                                                                (List.getElem_set_ne hne3 _).trans
                                                                  (m6_getElem_congr hp3_mod.symm _
                                                                    _)
                                                              have hset_ne2 :
                                                                  sc.core.arena[(p +
                                                                    3#64).toNat]'hp3_ar =
                                                                    sp.core.arena[(p +
                                                                      3#64).toNat]'(by
                                                                        rw [hsp_len]; c0_bound) :=
                                                                by
                                                                dsimp only [sc]
                                                                exact List.getElem_set_ne
                                                                  (by c0_bound) _
                                                              have hdiv_lt : (sc.core.arena[(p +
                                                                  3#64).toNat]'hp3_ar).toNat / 2 <
                                                                  sl.core.cur_vars := by
                                                                have hc' :
                                                                    ((sp.core.arena.set p.toNat
                                                                      (sp.core.arena[p.toNat]'(by
                                                                        rw [hsp_len]; c0_bound) &&&
                                                                        ~~~(16777216 : BitVec 32)))[
                                                                        (p.toNat +
                                                                        BitVec.toNat 3#64) %
                                                                        2 ^ 64]'(by
                                                                          rw [List.length_set,
                                                                            hsp_len]
                                                                          c0_bound)).toNat / 2 <
                                                                      sl.core.cur_vars := hc
                                                                rw [hset_ne1] at hc'
                                                                rw [hset_ne2]; exact hc'
                                                              have hsh1 : ((sc.core.arena[(p +
                                                                  3#64).toNat]'hp3_ar >>>
                                                                  (1 : Nat)) : BitVec 32).toNat =
                                                                  (sc.core.arena[(p +
                                                                    3#64).toNat]'hp3_ar).toNat /
                                                                    2 := by
                                                                rw [BitVec.toNat_ushiftRight,
                                                                  Nat.shiftRight_eq_div_pow]
                                                              rw [hset.1.1.core_ok.flags_len,
                                                                m6_zext32_toNat, hsh1]
                                                              have := hset.1.1.core_ok.cur_vars_le
                                                              omega
                                                          c0_hsteps!
                                                          exact hJ67 _ _
                                                            ⟨by simp [hset.1.1.core_ok.flags_len],
                                                             hm⟩
                                                        · c0_hsteps!
                                                          exact hJ67 sc.core.flags m
                                                            ⟨hset.1.1.core_ok.flags_len, hm⟩)
                                                  · c0_hsteps!
                                                    exact hJ55p m ⟨sc, hset.1, hcvp, halp, hflp,
                                                      hset.2.1, hm⟩))
                                      · c0_hsteps!
                                        exact hJp mp ⟨sp, hdwp, hcvp, halp, hflp, rfl, hmp⟩)
                                · c0_hsteps!; exact hJc sp mp ⟨hdwp, hcvp, hflp, hmp⟩
                              · intro Lp hLp; c0_hsteps!
                                exact hLp sv0.core.arena_len (0#64, ()) mv
                                  ⟨sv0, Nat.zero_le _, by simp, by
                                    by_cases hz : sv0.core.arena_len = 0
                                    · exact Or.inl hz.symm
                                    · exact Or.inr (m7_p2_zero_mem_arenaRefs3 hdw_v0.2.1.arena
                                        (Nat.pos_of_ne_zero hz)),
                                   hdw_v0, hcvl, rfl, hfll, hmv⟩
                          · intro Lv hLv; c0_hsteps!
                            exact hLv sl.core.cur_vars (0#64, ()) ml
                              ⟨sl.core.flags, hdwl.1.core_ok.flags_len, Nat.zero_le _, by simp, hml⟩
                        · c0_hsteps!; exact hJc sl ml ⟨hdwl, hcvl, hfll, hml⟩
                      · c0_hsteps!; exact hJc sl ml ⟨hdwl, hcvl, hfll, hml⟩
                    · c0_hsteps!; exact hJc sl ml ⟨hdwl, hcvl, hfll, hml⟩))
              (fun B hB => by
                c0_hsplit
                · have hi_lt : i.toNat < ncand.toNat := hc
                  c0_hsplit
                  · c0_hsplit
                    · c0_hsplit
                      · have hi_rr : i.toNat < sl.scratch.red_refs.length := by
                          rw [hdwl.1.scratch_ok.red_refs_len]; omega
                        have hcr_ref : (sl.scratch.red_refs[i.toNat]'hi_rr).toNat ∈
                            fullArenaClauseRefs sl := by
                          rw [hrefsl]
                          have h0 := hrr4_ok i.toNat hi_lt
                          rw [← hrrl, List.getElem?_eq_getElem hi_rr, Option.getD_some] at h0
                          exact h0
                        have hi1 : (i + 1#64).toNat = i.toNat + 1 := by c0_bound
                        c0_hsteps_nogrp
                        m7_call hCheckCl
                        refine fullFwdCheckClM7Spec_intro rfl hdwl hcr_ref hml ?_
                        intro ok_c sc mc hdwc hcvc _ hflc hrefsc _ hrrc hfc hmc
                        c0_hsplit
                        · have hcr_ref_c : (sl.scratch.red_refs[i.toNat]'hi_rr).toNat ∈
                              fullArenaClauseRefs sc := hrefsc.symm ▸ hcr_ref
                          refine wp_join0 (P := fun mj => ∃ sj : FullState,
                              FullDenseInvW c F0 F_cur sj ∧
                              sj.core.cur_vars = s0.core.cur_vars ∧ sj.core.fuel = s0.core.fuel ∧
                              fullArenaClauseRefs sj = fullArenaClauseRefs s4 ∧
                              sj.scratch.red_refs = s4.scratch.red_refs ∧
                              (FullMem c sj ⋆ R) mj)
                            (fun _ mj ⟨sj, hdwj, hcvj, hflj, hrefsj, hrrj, hmj⟩ => by
                              c0_hsteps!
                              exact hL (ncand.toNat - (i + 1#64).toNat)
                                (i + 1#64, rem - 1#64, ()) mj (by omega)
                                ⟨sj, by omega, rfl, hdwj, hcvj, hflj, hrefsj, hrrj, hmj⟩)
                            (fun Jcon hJcon => by
                              c0_hsplit
                              · c0_hsplit
                                · have hcr_ar :
                                      ((sl.scratch.red_refs[i.toNat]'hi_rr).setWidth 64).toNat <
                                        sc.core.arena.length := by
                                    have hwf_c := hdwc.2.1.arena.refs_wf _ hcr_ref_c
                                    have := hdwc.1.core_ok.arena_len_le
                                    rw [hdwc.1.core_ok.arena_len_arr, m6_zext32_toNat]; omega
                                  c0_hsplit
                                  · c0_hsteps_nogrp
                                    m7_call hConnectSub
                                    refine fullFwdConnectSubsumerM6Spec_intro rfl hdwc hcr_ref_c
                                      hmc ?_
                                    intro s_con m_con hdw_con hcv_con har_con hal_con hfl_con _ _
                                      hrr_con hm_con
                                    have hrefs_con : fullArenaClauseRefs s_con =
                                        fullArenaClauseRefs sc := by
                                      unfold fullArenaClauseRefs fullArenaClauseRefsCore
                                      rw [har_con, hal_con]
                                    c0_hsteps!
                                    exact hJcon m_con ⟨s_con, hdw_con,
                                      hcv_con.trans (hcvc.trans hcvl),
                                      hfl_con.trans (hflc.trans hfll),
                                      hrefs_con.trans (hrefsc.trans hrefsl),
                                      hrr_con.trans (hrrc.trans hrrl), hm_con⟩
                                  · c0_hsteps!
                                    exact hJcon mc ⟨sc, hdwc, hcvc.trans hcvl, hflc.trans hfll,
                                      hrefsc.trans hrefsl, hrrc.trans hrrl, hmc⟩
                                · c0_hsteps!
                                  exact hJcon mc ⟨sc, hdwc, hcvc.trans hcvl, hflc.trans hfll,
                                    hrefsc.trans hrefsl, hrrc.trans hrrl, hmc⟩
                              · c0_hsteps!
                                exact hJcon mc ⟨sc, hdwc, hcvc.trans hcvl, hflc.trans hfll,
                                  hrefsc.trans hrefsl, hrrc.trans hrrl, hmc⟩)
                        · c0_hsteps!
                          exact hQ 20#64 sc mc hdwc.toDense (hcvc.trans hcvl) (hflc.trans hfll)
                            (Or.inr rfl) (fun _ => hfc (by simpa using hc)) hmc
                      · c0_hsteps!; exact hB ml rfl
                    · c0_hsteps!; exact hB ml rfl
                  · c0_hsteps!; exact hB ml rfl
                · c0_hsteps!; exact hB ml rfl)
          · intro L hL; c0_hsteps!
            exact hL ncand.toNat (0#64, budget, ()) m4
              ⟨s4, Nat.zero_le _, by simp, hdw4,
               hcv4.trans (hcv3.trans (hcv2.trans hcv1)),
               hfl4.trans (hfl3.trans (hfl2.trans hfl1)), rfl, rfl, hm4⟩
      · c0_hsteps!
        exact hQ 20#64 s2 m2 hdw2.toDense (hcv2.trans hcv1) (hfl2.trans hfl1) (Or.inr rfl)
          (fun _ => hf2 (by simpa using hc)) hm2
    · c0_hsteps!
      exact hQ 20#64 s1 m1 hdw1.toDense hcv1 hfl1 (Or.inr rfl)
        (fun _ => hf1 (by simpa using hc)) hm1

end LeanQbe.T.Examples.Kissat.FullM7BveGates
