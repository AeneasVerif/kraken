module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S6aLiftsSpec
public import LeanQbe.T.Examples.Kissat.FullM7BveGates
public import LeanQbe.T.Examples.Kissat.FullM7BveGatesProof0
public import LeanQbe.T.Examples.Kissat.FullM6BveFwd
public import LeanQbe.T.Examples.Kissat.FullSpec
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullBvaFwdSpec
import LeanQbe.T.Examples.Kissat.FullDenseWatchLemmas1
import LeanQbe.T.Examples.Kissat.FullM6BveFwdProof1
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Wave-4F Step-13 Callee-Parametric WP Lifts — Part 3d0
(`Proof3d0` helpers for `full_fwd_check_cl_m7_step13_wp`)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S6a

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullBvaFwdHelpers
open LeanQbe.T.Examples.Kissat.Full.FullDenseWatchHelpers
open LeanQbe.T.Examples.Kissat.FullFastBveBudgets
open LeanQbe.T.Examples.Kissat.FullM6BveFwd
open LeanQbe.T.Examples.Kissat.FullM7BveGates
open Kraken.Bedrock2.Test

open scoped FullArenaTactics

local macro "m7_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

theorem step13FwdScanLitSpec_intro {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {R : Mem 64 → Prop} {h : Val i64} {cref sz scan_lit : BitVec 32}
    {check_bins : Bool} {m : Mem 64} {Q : Post [i32]} {X : XPost}
    (hh : h = c.hdr) (hlen : s.LengthsOk c)
    (hw : FullWitnessInv c F0 F_cur s.core) (hcl : s.core.cur_level = 0)
    (hdm : s.core.dense_mode ≠ 0#64) (hnd : FullArenaVarsNodup s)
    (href : cref.toNat ∈ fullArenaClauseRefs s)
    (hng : fullArenaClauseGarb s cref.toNat = false)
    (hsz : sz.toNat = fullArenaClauseSize s cref.toNat) (hlt : scan_lit.toNat < 2 * s.core.cur_vars)
    (hcb : check_bins = true → scan_lit.toNat ∈ fullArenaClauseLits s cref.toNat)
    (hlm : ∀ x < 2 * s.core.cur_vars,
      s.core.lit_mark[x]?.getD 0#8 ≠ 0#8 ↔ x ∈ fullArenaClauseLits s cref.toNat)
    (hm : (FullMem c s ⋆ R) m)
    (hpost : ∀ r : BitVec 32, r = 0xFFFFFFFF#32 ∨ r = 0xFFFFFFFE#32 ∨
      (r.toNat ∈ fullArenaClauseLits s cref.toNat ∧
        (cnfOfClauses F_cur).EntailsClause
          (cnfClause ((fullArenaClauseLits s cref.toNat).filter (· != r.toNat)))) →
      Q (r, ()) m) :
    step13FwdScanLitSpec (h, cref, sz, scan_lit, check_bins, ()) m Q X :=
  ⟨c, F0, F_cur, s, R, hh, hlen, hw, hcl, hdm, hnd, href, hng, hsz, hlt, hcb, hlm, hm, hpost⟩

theorem m7_p3_lit_compl_conflict {α : Nat → Bool} {l : Nat}
    (h1 : α (litVar l) = !litSign l)
    (h2 : α (litVar (l ^^^ 1)) = !litSign (l ^^^ 1)) : False := by
  simp only [litVar, litSign] at h1 h2
  rw [fullInv_var_xor1 l, m6_xor1_mod2 l] at h2
  rcases Nat.mod_two_eq_zero_or_one l with hm | hm <;>
    cases h : α (l / 2) <;> simp_all


theorem m7_p3_drop_false_lit {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
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
  rw [heq] at hsc; exact m7_p3_lit_compl_conflict hsc hs'

theorem m7_p3_unsat_of_entails_nil {F : CNF Nat} (h : F.EntailsClause (cnfClause [])) :
    F.Unsat := by
  rw [CNF.unsat_iff_not_sat]; intro α hα
  have hs := (clause_sat_cnfClause_iff α []).mp ((CNF.entails_clause_def.mp h) α hα)
  obtain ⟨_, hm, _⟩ := hs; cases hm

theorem m7_p3_sublist_map_nodup {xs ys : List Nat} (hsub : ys.Sublist xs)
    (hnd : (xs.map (· / 2)).Nodup) : (ys.map (· / 2)).Nodup :=
  (hsub.map (· / 2)).nodup hnd

theorem m7_p3_fullDenseInvW_with_lit_mark {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (h : FullDenseInvW c F0 F_cur s)
    {lm' : List (BitVec 8)} (hlm_len : lm'.length = 2 * c.max_vars)
    (hlm_clr : ∀ l < 2 * c.max_vars, lm'[l]?.getD 0#8 = 0#8) :
    FullDenseInvW c F0 F_cur { s with core := { s.core with lit_mark := lm' } } :=
  ⟨⟨{ h.1.core_ok with lit_mark_len := hlm_len }, h.1.scratch_ok⟩,
   { h.2.1 with
     arena := { h.2.1.arena with len_ok := h.2.1.arena.len_ok }
     watches := h.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) },
   ⟨h.2.2.1.1, hlm_clr⟩, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

theorem m7_p3_fullDenseInvW_of_unwatch {c : FullCfg} {F0 : CNF Nat}
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

theorem m7_p3_fullDenseInvW_of_addBin {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s s' : FullState} (h : FullDenseInvW c F0 F_cur s)
    (hlen' : s'.LengthsOk c) (hw' : FullWitnessInv c F0 F_cur s'.core)
    (hmrk : s'.core.mrk = s.core.mrk) (hlm : s'.core.lit_mark = s.core.lit_mark)
    (har : s'.core.arena = s.core.arena) (hal : s'.core.arena_len = s.core.arena_len)
    (hcl : s'.core.cur_level = s.core.cur_level) (hdm : s'.core.dense_mode = s.core.dense_mode)
    (hll : s'.scratch.last_learned = s.scratch.last_learned)
    (hext : s'.scratch.extend_len = s.scratch.extend_len) :
    FullDenseInvW c F0 F_cur s' :=
  m6_fullDenseInvW_of_addUnit h hlen' hw' (hcl.trans h.2.2.2.2.2.1) hmrk hlm har hal hdm hll hext

theorem m7_p3_fullDenseInvW_of_shrink {c : FullCfg} {F0 : CNF Nat}
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


theorem m7_p3_fwd_shrink_common {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
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

theorem m7_p3_fwd_shrink_step {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
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
    m7_p3_fwd_shrink_common hdw href hsz3 hsz_lt hsz_eq hhdr_eq hcv_le htl' harc_l hout_c hcopy_c
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
    have hshr := m7_p3_fullDenseInvW_of_shrink (arena' := ar_fin) hdw href hsz3 (by omega) hlen_s
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
    have hshr := m7_p3_fullDenseInvW_of_shrink (arena' := ar_fin) hdw href hsz3 (by omega)
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

theorem m7_p3_fwd_lm_set_iff {c : FullCfg} {k : FullCoreState} {lits : List Nat}
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

theorem m7_p3_fwd_lm_clear_step {c : FullCfg} {lits : List Nat} {lm : List (BitVec 8)}
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

theorem m7_p3_fwd_cl_lits_len {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hdw : FullDenseInvW c F0 F_cur s) {cref : Nat}
    (href : cref ∈ fullArenaClauseRefs s) {sz : Nat}
    (hsz : sz = fullArenaClauseSizeCore s.core cref) :
    (fullArenaClauseLits s cref).length = sz := by
  have hwf := hdw.2.1.arena.refs_wf cref href
  unfold fullArenaClauseLits fullArenaClauseLitsCore
  simp only [List.length_map, List.length_take, List.length_drop]
  rw [hdw.1.core_ok.arena_len_arr]; have := hdw.1.core_ok.arena_len_le; omega

theorem m7_p3_fwd_cl_lit_at {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hdw : FullDenseInvW c F0 F_cur s) {cref : Nat}
    (href : cref ∈ fullArenaClauseRefs s) {sz i : Nat}
    (hsz : sz = fullArenaClauseSizeCore s.core cref) (hi : i < sz) :
    i < (fullArenaClauseLits s cref).length ∧
    (fullArenaClauseLits s cref)[i]'(by
      rw [m7_p3_fwd_cl_lits_len hdw href hsz]; exact hi) =
      (s.core.arena[cref + 3 + i]'(by
        have hwf := hdw.2.1.arena.refs_wf cref href
        rw [hdw.1.core_ok.arena_len_arr]; have := hdw.1.core_ok.arena_len_le; omega)).toNat := by
  have hlen := m7_p3_fwd_cl_lits_len hdw href hsz
  refine ⟨by rw [hlen]; exact hi, ?_⟩
  have heq : (fullArenaClauseLits s cref)[i]'(by rw [hlen]; exact hi) =
      (List.map BitVec.toNat
        (List.take (fullArenaClauseSizeCore s.core cref)
          (List.drop (cref + 3) s.core.arena)))[i]'(by
        have hwf := hdw.2.1.arena.refs_wf cref href
        have := hdw.1.core_ok.arena_len_le
        have := hdw.1.core_ok.arena_len_arr
        simp [← hsz]; omega) := rfl
  rw [heq, List.getElem_map, List.getElem_take, List.getElem_drop]


theorem m7_p3_fwd_nsz2_garb_post {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
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

theorem m7_p3_fwd_nsz3_sub_post {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
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

theorem m7_p3_fwd_pad_orig {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
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

theorem m7_p3_copy_iter {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
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

theorem m7_p3_check_cl_shrink0 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
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
  have hstep := m7_p3_fwd_shrink_step hdw_f' href_u hngt_sf' hnsz3 hnsz_lt_sz hsz_sf' hhdr_sf'
    hcv_f' htl' harc_l hout_c hcopy_c htmp_lt htmp_nd htmp_ent hpad_orig
  simp only [hsh0, ↓reduceIte] at hstep
  exact hstep

theorem m7_p3_check_cl_shrink1 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
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
  have hstep := m7_p3_fwd_shrink_step hdw_f' href_u hngt_sf' hnsz3 hnsz_lt_sz hsz_sf' hhdr_sf'
    hcv_f' htl' harc_l hout_c hcopy_c htmp_lt htmp_nd htmp_ent hpad_orig
  simp only [hsh1, ↓reduceIte] at hstep
  exact hstep

theorem m7_p3_unmark_iter {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
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
  have hli_at := m7_p3_fwd_cl_lit_at hdwt href_t hszt hiu_lt
  have hli_eq : (fullArenaClauseLits st cref.toNat)[iu.toNat]'hli_at.1 = li.toNat :=
    hli_at.2.trans (congrArg BitVec.toNat (m6_getElem_congr (by c0_bound) _ _))
  have hli_lt : li.toNat < 2 * st.core.cur_vars :=
    hdwt.2.1.arena.lits_lt cref.toNat href_t hngt _ (hli_eq ▸ List.getElem_mem hli_at.1)
  have hli_lm : (li.setWidth 64).toNat < lm_u.length := by
    rw [hlmu, m6_zext32_toNat]; have := hdwt.1.core_ok.cur_vars_le; omega
  have hiu1 : (iu + 1#32).toNat = iu.toNat + 1 := by c0_bound
  refine ⟨hli_lm, hiu1, ?_⟩
  rw [m6_zext32_toNat, hiu1]
  exact m7_p3_fwd_lm_clear_step hlmu hli_at.1 hli_eq hrem_lm

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S6a
