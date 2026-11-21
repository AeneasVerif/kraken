module

public import LeanQbe.T.Examples.Kissat.FullAnalyzeLemmas1
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Full` Conflict Analysis, OTFS & Eager Subsumption Helpers (Part 2)

Provides `PH_GARB`/watch-slice helpers, `Func.wp` proofs (`full_analyze_lit_wp`,
`full_clear_ana_wp`, `full_analyze_rsn_wp`), and strictly scoped `fa_fast_steps` tactics.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.C0Step Kraken.Bedrock2.Test FullAnalyzeTactics FullAnalyzeSpecs FullAnalyzeHelpers
open scoped FullArenaTactics FullAnalyzeTactics

/-! ## 1. `PH_GARB` witness-cut & shared helpers -/

namespace FullAnalyzeHelpers

theorem bv32_or_garb_garb (x : BitVec 32) :
    ((x ||| 0x00080000#32) &&& 0x00080000#32) ≠ 0#32 := by
  intro h; have h19 := congrArg (·[19]) h; revert h19
  simp [show (0x00080000#32)[19] = true from rfl]

theorem fullArenaVarsNodup_markGarb {s : FullState} (hnd : FullArenaVarsNodup s)
    {cref : Nat} {arena' : List (BitVec 32)} {ag' : BitVec 64}
    (hrefs : fullArenaClauseRefsCore { s.core with arena := arena', arena_garbage := ag' } =
      fullArenaClauseRefsCore s.core) (hgarb_c : fullArenaClauseGarbCore
      { s.core with arena := arena', arena_garbage := ag' } cref = true)
    (hother : ∀ r ∈ fullArenaClauseRefsCore s.core, r ≠ cref →
      fullArenaClauseLitsCore { s.core with arena := arena', arena_garbage := ag' } r =
        fullArenaClauseLitsCore s.core r ∧
      fullArenaClauseGarbCore { s.core with arena := arena', arena_garbage := ag' } r =
        fullArenaClauseGarbCore s.core r) :
    FullArenaVarsNodup
      { s with core := { s.core with arena := arena', arena_garbage := ag' } } := by
  intro r hr hng
  change r ∈ fullArenaClauseRefsCore { s.core with arena := arena', arena_garbage := ag' } at hr
  rw [hrefs] at hr; by_cases hrc : r = cref
  · subst r; change fullArenaClauseGarbCore _ _ = false at hng; rw [hgarb_c] at hng; cases hng
  · obtain ⟨hlits, hgarb⟩ := hother r hr hrc
    change ((fullArenaClauseLitsCore _ r).map (· / 2)).Nodup; rw [hlits]
    exact hnd r hr (by change fullArenaClauseGarbCore s.core r = false; rw [← hgarb]; exact hng)

theorem markGarb_preserves_fullWitnessCut {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {cut cut' : Nat} {k : FullCoreState} (hlen : k.LengthsOk c)
    (hw : FullWitnessCutInv c F0 F_cur cut k) (hcut : cut' ≤ cut) {cref : Nat}
    (href : cref ∈ fullArenaClauseRefsCore k) (ag' : BitVec 64)
    (hnonact : ∀ idx < k.trail_end, (idx < cut' ∨
        (k.lvl[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat < k.cur_level) →
      let rsn := k.rsns[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32
      rsn ≠ 0xFFFFFFFF#32 → (rsn &&& 0x80000000#32) = 0#32 → rsn.toNat ≠ cref) :
    let arena' := k.arena.set cref (fullArenaHdrCore k cref ||| 0x00080000#32)
    let k' : FullCoreState := { k with arena := arena', arena_garbage := ag' }
    FullWitnessCutInv c F0 F_cur cut' k' ∧ fullArenaClauseRefsCore k' = fullArenaClauseRefsCore k ∧
    (∀ r ∈ fullArenaClauseRefsCore k, fullArenaClauseSizeCore k' r = fullArenaClauseSizeCore k r ∧
      fullArenaClauseLitsCore k' r = fullArenaClauseLitsCore k r ∧
      (r ≠ cref → fullArenaClauseGarbCore k' r = fullArenaClauseGarbCore k r)) := by
  intro arena' k'; have hmg := hw.arena.markGarb hlen href ag'
  have hrefs : fullArenaClauseRefsCore k' = fullArenaClauseRefsCore k := hmg.1
  have hdisj_props : ∀ r ∈ fullArenaClauseRefsCore k,
      fullArenaClauseSizeCore k' r = fullArenaClauseSizeCore k r ∧
      fullArenaClauseLitsCore k' r = fullArenaClauseLitsCore k r ∧
      (r ≠ cref → fullArenaClauseGarbCore k' r = fullArenaClauseGarbCore k r) := fun r hr => by
    have hrwf := hw.arena.refs_wf r hr; have hbd : r + 3 + fullArenaClauseSizeCore k r ≤
        k.arena.length := by have := hlen.arena_len_le; have := hlen.arena_len_arr; omega
    by_cases hrc : r = cref
    · subst r; have hsz : fullArenaClauseSizeCore k' cref = fullArenaClauseSizeCore k cref := by
        unfold fullArenaClauseSizeCore k'; rw [List.getElem?_set_ne (by omega)]
      exact ⟨hsz, fullArenaClauseLitsCore_eq_of_hold hbd (by simpa [k', arena'] using hbd) hsz
        fun _ _ => List.getElem?_set_ne (by omega), fun hne => absurd rfl hne⟩
    · have hdisj : r + 3 + fullArenaClauseSizeCore k r ≤ cref ∨ cref + 3 ≤ r := by
        rcases Nat.lt_or_gt_of_ne hrc with hlt | hgt
        · exact Or.inl (hw.arena.disjoint hr href hlt)
        · exact Or.inr (by have := hw.arena.disjoint href hr hgt; omega)
      have hsz : fullArenaClauseSizeCore k' r = fullArenaClauseSizeCore k r := by
        unfold fullArenaClauseSizeCore k'; rw [List.getElem?_set_ne (by omega)]
      have hgarb : fullArenaClauseGarbCore k' r = fullArenaClauseGarbCore k r := by
        unfold fullArenaClauseGarbCore fullArenaHdrCore k'; rw [List.getElem?_set_ne (Ne.symm hrc)]
      exact ⟨hsz, (fullArenaClauseLitsCore_set_outside hbd hdisj).2, fun _ => hgarb⟩
  have hcw := arenaUpdate_preserves_fullWitnessCut (hw.shrink_cut hcut) hmg.2 hrefs
    fun idx hidx hc hne hlg => by
      have hrs := hw.reason_inv idx hidx (hc.elim (fun h => Or.inl (by omega)) Or.inr) hne
      rw [ite_eq_right (fun h => absurd hlg h)] at hrs; have hp := hdisj_props _ hrs.1
      exact ⟨(hp.2.2 (hnonact idx hidx hc hne hlg)).trans hrs.2.1, hp.2.1 ▸ List.Perm.refl _⟩
  exact ⟨hcw, hrefs, hdisj_props⟩

theorem otfs_nonactive_on_trail {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {k : FullCoreState} (hw : FullWitnessCutInv c F0 F_cur cut k)
    (hlen : k.LengthsOk c) {cref uip : BitVec 32} {idx_u : Nat} (hiu_cut : idx_u < cut)
    (hiu_te : idx_u < k.trail_end) (ht_u : (k.trl[idx_u]?.getD 0#32).toNat = uip.toNat)
    (hr_u : k.rsns[uip.toNat / 2]?.getD 0xFFFFFFFF#32 = cref)
    (hlev_u : (k.lvl[uip.toNat / 2]?.getD 0#32).toNat = k.cur_level)
    (href : cref.toNat ∈ fullArenaClauseRefsCore k) : ∀ idx < k.trail_end, (idx < min cut idx_u ∨
        (k.lvl[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat < k.cur_level) →
      let rsn := k.rsns[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32
      rsn ≠ 0xFFFFFFFF#32 → (rsn &&& 0x80000000#32) = 0#32 → rsn.toNat ≠ cref.toNat := by
  have har_cap := c.harena; have hal_le := hlen.arena_len_le
  have hcref_lt : cref.toNat < 2 ^ 31 - 1 := by
    have := (hw.arena.refs_wf cref.toNat href).1; unfold dimacsBound at har_cap; omega
  have hcref_ne : cref ≠ 0xFFFFFFFF#32 := bv32_lit_neq_ff hcref_lt
  have hcref_lg : (cref &&& 0x80000000#32) = 0#32 :=
    (bv32_lit_lo31_props (by omega : cref.toNat < 2 ^ 31)).2.2
  have huip_mem : uip.toNat ∈ fullArenaClauseLitsCore k cref.toNat := by
    have hm := hw.reason_lit_mem idx_u hiu_te (Or.inl hiu_cut)
    dsimp only at hm; rw [ht_u, hr_u] at hm; exact hm hcref_ne hcref_lg
  intro idx hidx hc rsn hne hlg heq
  have hr := hw.reason_inv idx hidx (hc.elim (fun h => Or.inl (by omega)) Or.inr) hne
  rw [ite_eq_right (fun h => absurd hlg h)] at hr
  rcases hr.2.2 uip.toNat (heq ▸ huip_mem) with h_eq | ⟨m, hm, hmeq, _⟩
  · have hieq := hw.trail_vars_nodup idx idx_u hidx hiu_te (by rw [ht_u, ← h_eq])
    rcases hc with h1 | h2
    · omega
    · rw [hieq, ht_u, hlev_u] at h2; omega
  · have := hw.trail_vars_nodup m idx_u (by omega) hiu_te (by rw [hmeq, fullInv_var_xor1, ht_u])
    rcases hc with h1 | h2 <;> omega

theorem falsified_clause_nonactive {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {k : FullCoreState} (hw : FullWitnessCutInv c F0 F_cur cut k) {cref : Nat}
    (hfals : ∀ l ∈ fullArenaClauseLitsCore k cref, k.vals[l]?.getD 0#8 = 0xFF#8) :
    ∀ idx < k.trail_end,
      (idx < cut ∨ (k.lvl[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat < k.cur_level) →
      let rsn := k.rsns[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32
      rsn ≠ 0xFFFFFFFF#32 → (rsn &&& 0x80000000#32) = 0#32 → rsn.toNat ≠ cref := by
  intro idx hidx hc rsn hne hlg heq
  have hp_t := (hw.vals_true_iff _ (hw.trail_lits_lt idx hidx)).mpr ⟨idx, hidx, rfl⟩
  have hp_mem : (k.trl[idx]?.getD 0#32).toNat ∈ fullArenaClauseLitsCore k cref := by
    rw [← heq]; exact hw.reason_lit_mem idx hidx hc hne hlg
  have hp_f := hfals _ hp_mem; rw [hp_t] at hp_f; cases hp_f

theorem same_core_fullWitnessCut {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {k : FullCoreState} (hw : FullWitnessCutInv c F0 F_cur cut k)
    {mrk' : List (BitVec 8)} {tmp' : List (BitVec 32)} {mcl' tc' tl' : Nat}
    (_hm : mrk'.length = c.max_vars) (_ht : tmp'.length = c.max_vars)
    (_hmcl : mcl' ≤ c.max_vars) (_htl : tl' ≤ k.cur_vars) : FullWitnessCutInv c F0 F_cur cut
      { k with mrk := mrk', tmp := tmp', tmp_cnt := tc', tmp_len := tl', min_clr_len := mcl' } :=
  { hw with arena := { hw.arena with len_ok := hw.arena.len_ok }
            watches := hw.watches.with_wstk rfl rfl rfl rfl rfl fun _ hr => hr }

/-! ## 2. Filter-count, watch-slice helpers & `full_analyze_lit_wp` -/

private theorem filter_length_flip_one {α : Type} (p p' : α → Bool) (k : α) :
    ∀ (xs : List α), xs.Nodup → k ∈ xs → p k = false → p' k = true →
      (∀ x ∈ xs, x ≠ k → p' x = p x) → (xs.filter p').length = (xs.filter p).length + 1
  | [], _, hmem, _, _, _ => by simp at hmem
  | x :: xs, hnd, hmem, hpk, hp'k, hagree => by
    rw [List.nodup_cons] at hnd; rcases List.mem_cons.mp hmem with rfl | hmem'
    · have hfeq := List.filter_congr fun y hy =>
        hagree y (List.mem_cons_of_mem _ hy) (fun heq => hnd.1 (heq ▸ hy))
      simp [hpk, hp'k, hfeq]
    · have hx := hagree x List.mem_cons_self (fun heq => hnd.1 (heq ▸ hmem'))
      have ih := filter_length_flip_one p p' k xs hnd.2 hmem' hpk hp'k
        fun y hy => hagree y (List.mem_cons_of_mem _ hy)
      cases hp : p x <;> simp [hx, hp, ih] <;> omega

private theorem filter_length_eq_zero_of_false {α : Type} {p : α → Bool} {xs : List α}
    (h : ∀ x ∈ xs, p x = false) : (xs.filter p).length = 0 := by
  have : xs.filter p = [] := List.filter_eq_nil_iff.mpr fun x hx => by simp [h x hx]
  simp [this]

theorem filter_step_of_lit {s_mrk mrk1 mrk2 : List (BitVec 8)} (P : Nat → Bool)
    {mv tc0 tc1 tc2 v : Nat}
    (hmp0 : ∀ w < mv, s_mrk[w]?.getD 0#8 ≠ 0#8 → mrk1[w]?.getD 0#8 = s_mrk[w]?.getD 0#8)
    (hmp1 : ∀ w < mv, mrk1[w]?.getD 0#8 ≠ 0#8 → mrk2[w]?.getD 0#8 = mrk1[w]?.getD 0#8)
    (hnew1 : ∀ w < mv, mrk1[w]?.getD 0#8 = 0#8 → mrk2[w]?.getD 0#8 ≠ 0#8 → v = w)
    (htc_ge : tc0 ≤ tc1) (hcnt1 : tc1 - tc0 = ((List.range mv).filter fun w =>
      decide (s_mrk[w]?.getD 0#8 = 0#8) && decide (mrk1[w]?.getD 0#8 ≠ 0#8) && P w).length)
    (htc2 : tc2 = tc1 + if v < mv ∧ mrk1[v]?.getD 0#8 = 0#8 ∧ mrk2[v]?.getD 0#8 ≠ 0#8 ∧
      P v = true then 1 else 0) : tc2 - tc0 = ((List.range mv).filter fun w =>
      decide (s_mrk[w]?.getD 0#8 = 0#8) && decide (mrk2[w]?.getD 0#8 ≠ 0#8) && P w).length := by
  have hne_iff : ∀ w < mv, w ≠ v → (mrk2[w]?.getD 0#8 ≠ 0#8 ↔ mrk1[w]?.getD 0#8 ≠ 0#8) :=
    fun w hw hne => ⟨fun h2 h1 => hne (hnew1 w hw h1 h2).symm, fun h1 => by rwa [hmp1 w hw h1]⟩
  split at htc2
  · rename_i hC; obtain ⟨hv, hm1, hm2, hcl⟩ := hC
    have hs0 : s_mrk[v]?.getD 0#8 = 0#8 :=
      Classical.byContradiction fun hnz => absurd hm1 (by rwa [hmp0 v hv hnz])
    have hflip := filter_length_flip_one
      (fun w => decide (s_mrk[w]?.getD 0#8 = 0#8) && decide (mrk1[w]?.getD 0#8 ≠ 0#8) && P w)
      (fun w => decide (s_mrk[w]?.getD 0#8 = 0#8) && decide (mrk2[w]?.getD 0#8 ≠ 0#8) && P w)
      v (List.range mv) List.nodup_range (List.mem_range.mpr hv) (by simp [hm1])
      (by simp [hs0, hm2, hcl]) (fun w hw hne => by simp [hne_iff w (List.mem_range.mp hw) hne])
    rw [hflip, ← hcnt1]; omega
  · rename_i hC; rw [Nat.add_zero] at htc2; subst htc2; rw [hcnt1]
    congr 1; apply List.filter_congr; intro w hw; have hwlt := List.mem_range.mp hw
    by_cases hwe : w = v
    · subst w; by_cases hm1 : mrk1[v]?.getD 0#8 = 0#8
      · by_cases hcl : P v = true
        · have hm2 : mrk2[v]?.getD 0#8 = 0#8 :=
            Classical.byContradiction fun hnz => hC ⟨hwlt, hm1, hnz, hcl⟩; simp [hm1, hm2]
        · simp [hcl]
      · rw [hmp1 v hwlt hm1]
    · simp [hne_iff w hwlt hwe]

theorem fa_watchSlice_relocate {F F' : List (List Nat)} {k k' : FullCoreState}
    {lit p p' rem : Nat} (hF : (cnfOfClauses F').Entails (cnfOfClauses F))
    (hvars : k.cur_vars ≤ k'.cur_vars)
    (hsub : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k')
    (hwstk : ∀ idx < rem, k'.wstk[p' + idx]? = k.wstk[p + idx]?)
    (h : WatchSliceOk F k lit p rem) : WatchSliceOk F' k' lit p' rem := by
  induction h generalizing p' with
  | empty => exact .empty
  | @bin p rem w0 hp hflag hne hlt hent _ ih =>
    exact .bin (by simpa using (hwstk 0 (by omega)).trans hp) hflag hne (by omega)
      (CNF.entails_clause_trans hF hent) (ih (p' := p' + 1) fun idx hi => by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hwstk (idx + 1) (by omega))
  | @large p rem w0 cref hp hp1 hflag hlt href _ ih =>
    exact .large (by simpa using (hwstk 0 (by omega)).trans hp)
      (by simpa using (hwstk 1 (by omega)).trans hp1) hflag hlt (hsub _ href)
      (ih (p' := p' + 2) fun idx hi => by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hwstk (idx + 2) (by omega))

theorem fa_watchSlice_append_bin {F_cur : List (List Nat)} {k k' : FullCoreState}
    {lit p p' rem : Nat} {w0 : BitVec 32} (hvars : k.cur_vars ≤ k'.cur_vars)
    (hsub : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k')
    (hwstk : ∀ idx < rem, k'.wstk[p' + idx]? = k.wstk[p + idx]?)
    (h : WatchSliceOk F_cur k lit p rem) (hw0 : k'.wstk[p' + rem]? = some w0)
    (hflag : (w0 &&& 0x80000000#32) ≠ 0#32) (hne : w0 ≠ 0xFFFFFFFF#32)
    (hlt : (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k'.cur_vars)
    (hent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause [lit, (w0 &&& 0x7FFFFFFF#32).toNat])) :
    WatchSliceOk F_cur k' lit p' (rem + 1) := by
  induction h generalizing p' with
  | empty => exact .bin (by simpa using hw0) hflag hne hlt hent .empty
  | @bin p rem w hp hf hn hl he _ ih =>
    exact .bin (by simpa using (hwstk 0 (by omega)).trans hp) hf hn (by omega) he
      (ih (p' := p' + 1) (fun idx hi => by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hwstk (idx + 1) (by omega))
        (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hw0))
  | @large p rem w cref hp hp1 hf hl href _ ih =>
    exact .large (by simpa using (hwstk 0 (by omega)).trans hp)
      (by simpa using (hwstk 1 (by omega)).trans hp1) hf hl (hsub _ href)
      (ih (p' := p' + 2) (fun idx hi => by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hwstk (idx + 2) (by omega))
        (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hw0))

end FullAnalyzeHelpers

private def anaLitSt (s : FullState) (mrk' : List (BitVec 8)) (tmp' ws1' : List (BitVec 32))
    (mcl' tc' tl' : Nat) (ant' res' : BitVec 64) : FullState :=
  { s with core := { s.core with mrk := mrk', tmp := tmp', tmp_cnt := tc', tmp_len := tl',
                                 min_clr_len := mcl' }
           scratch := { s.scratch with work_stk1 := ws1', ant_sz := ant', res_sz := res' } }

private theorem anaWorkInv_step_lshr {c : FullCfg} {s : FullState} (hlen : s.LengthsOk c)
    (hwork : AnaWorkInv c s) (lit : BitVec 32) (hv : lit.toNat / 2 < s.core.cur_vars)
    (hm0 : s.core.mrk[lit.toNat / 2]?.getD 0#8 = 0#8) :
    s.core.min_clr_len < s.core.cur_vars ∧ AnaWorkInv c (anaLitSt s
      (s.core.mrk.set (lit.toNat / 2) 1#8) s.core.tmp (s.scratch.work_stk1.set s.core.min_clr_len
      (lit >>> 1)) (s.core.min_clr_len + 1) s.core.tmp_cnt s.core.tmp_len
      s.scratch.ant_sz s.scratch.res_sz) := by
  have hlt : lit.toNat / 2 < 2 ^ 32 := by have := lit.isLt; omega
  have hwl : BitVec.ofNat 32 (lit.toNat / 2) = lit >>> 1 :=
    BitVec.eq_of_toNat_eq (by rw [bv32_ofNat_toNat hlt]; exact (bv32_lshr_1 lit).symm)
  simpa [anaLitSt, hwl] using anaWorkInv_step hlen hwork hv hm0

private theorem lvl_lt_cur_of_le_ne {lvl : List (BitVec 32)} {v cl : Nat}
    (hv : v < lvl.length) (hcl : cl < 2 ^ 32) (hle : ¬ cl % 2 ^ 32 < (lvl[v]'hv).toNat)
    (hne : lvl[v]'hv ≠ (BitVec.ofNat 64 cl).setWidth 32) : (lvl[v]?.getD 0#32).toNat < cl := by
  rw [Nat.mod_eq_of_lt hcl] at hle; rw [List.getElem?_eq_getElem hv, Option.getD_some]
  have htr : ((BitVec.ofNat 64 cl).setWidth 32).toNat = cl := by
    rw [bv64_trunc32_ofNat hcl, bv32_ofNat_toNat hcl]
  exact Nat.lt_of_le_of_ne (Nat.not_lt.mp hle) fun h => hne (BitVec.eq_of_toNat_eq (by rw [h, htr]))

private abbrev AnaLitQ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop)
    (lit skip_var : BitVec 32) (Q : Post [.bool]) : Prop :=
  ∀ (ok : Bool) mrk' tmp' ws1' mcl' tc' tl' ant' res' m',
    let s' := anaLitSt s mrk' tmp' ws1' mcl' tc' tl' ant' res'
    s'.LengthsOk c → AnaWorkInv c s' → tl' ≤ s.core.cur_vars → s.core.tmp_len ≤ tl' →
    tl' ≤ s.core.tmp_len + 1 → s.core.tmp_cnt ≤ tc' → let v := lit.toNat / 2
    (∀ w < s.core.cur_vars, s.core.mrk[w]?.getD 0#8 ≠ 0#8 →
      mrk'[w]?.getD 0#8 = s.core.mrk[w]?.getD 0#8) →
    (∀ k < s.core.tmp_len, tmp'[k]? = s.core.tmp[k]?) →
    (∀ w < s.core.cur_vars, s.core.mrk[w]?.getD 0#8 = 0#8 → mrk'[w]?.getD 0#8 ≠ 0#8 →
      v = w ∧ w ≠ skip_var.toNat ∧ 0 < (s.core.lvl[w]?.getD 0#32).toNat ∧
      (s.core.lvl[w]?.getD 0#32).toNat ≤ s.core.cur_level) →
    (∀ j, s.core.tmp_len ≤ j → j < tl' → (tmp'[j]?.getD 0#32).toNat = lit.toNat ∧
      v < s.core.cur_vars ∧ v ≠ skip_var.toNat ∧ s.core.mrk[v]?.getD 0#8 = 0#8 ∧
      0 < (s.core.lvl[v]?.getD 0#32).toNat ∧ (s.core.lvl[v]?.getD 0#32).toNat < s.core.cur_level ∧
      mrk'[v]?.getD 0#8 ≠ 0#8) →
    ant' = s.scratch.ant_sz + (if v < s.core.cur_vars ∧ 0 < (s.core.lvl[v]?.getD 0#32).toNat ∧
      (s.core.lvl[v]?.getD 0#32).toNat ≤ s.core.cur_level then 1#64 else 0#64) →
    res' = s.scratch.res_sz + (if v < s.core.cur_vars ∧ s.core.mrk[v]?.getD 0#8 = 0#8 ∧
      mrk'[v]?.getD 0#8 ≠ 0#8 then 1#64 else 0#64) →
    tc' = s.core.tmp_cnt + (if v < s.core.cur_vars ∧ s.core.mrk[v]?.getD 0#8 = 0#8 ∧
      mrk'[v]?.getD 0#8 ≠ 0#8 ∧ (s.core.lvl[v]?.getD 0#32).toNat = s.core.cur_level then 1 else 0) →
    (ok = true → v < s.core.cur_vars ∧ (v ≠ skip_var.toNat →
      (0 < (s.core.lvl[v]?.getD 0#32).toNat → mrk'[v]?.getD 0#8 ≠ 0#8) ∧
      (s.core.mrk[v]?.getD 0#8 = 0#8 → (s.core.lvl[v]?.getD 0#32).toNat ≤ s.core.cur_level ∧
        (0 < (s.core.lvl[v]?.getD 0#32).toNat →
          (s.core.lvl[v]?.getD 0#32).toNat = s.core.cur_level → tc' = s.core.tmp_cnt + 1) ∧
        (0 < (s.core.lvl[v]?.getD 0#32).toNat → (s.core.lvl[v]?.getD 0#32).toNat <
          s.core.cur_level → tl' = s.core.tmp_len + 1 ∧ tmp'[s.core.tmp_len]? = some lit)))) →
    (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

private theorem mk_lit_ne_skip {lit skip_var : BitVec 32} (h : lit >>> 1 ≠ skip_var) :
    lit.toNat / 2 ≠ skip_var.toNat :=
  fun heq => h (BitVec.eq_of_toNat_eq (by rw [bv32_lshr_1]; exact heq))

private theorem mk_lvl_pos {lvl : List (BitVec 32)} {v : Nat} {hv : v < lvl.length}
    (hnz : lvl[v]'hv ≠ 0#32) : 0 < (lvl[v]?.getD 0#32).toNat := by
  rw [List.getElem?_eq_getElem hv, Option.getD_some]
  exact Nat.pos_of_ne_zero fun hz => hnz (BitVec.eq_of_toNat_eq hz)

private theorem mrk_getD_ne_zero {mrk : List (BitVec 8)} {v : Nat} {hv : v < mrk.length}
    (h : mrk[v]'hv ≠ 0#8) : mrk[v]?.getD 0#8 ≠ 0#8 := by
  rwa [List.getElem?_eq_getElem hv, Option.getD_some]

private theorem full_analyze_lit_mark {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} {Q : Post [.bool]} {lit skip_var : BitVec 32} (ok : Bool)
    (tmp' : List (BitVec 32)) (tc' tl' : Nat) (hlen : s.LengthsOk c) (hwork : AnaWorkInv c s)
    (hvlt : lit.toNat / 2 < s.core.cur_vars) (hvne : lit.toNat / 2 ≠ skip_var.toNat)
    (hm0 : s.core.mrk[lit.toNat / 2]?.getD 0#8 = 0#8)
    (hvl_pos : 0 < (s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat)
    (hvl_le : (s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat ≤ s.core.cur_level)
    (htmp_len : tmp'.length = c.max_vars) (htl_ge : s.core.tmp_len ≤ tl')
    (htl_inc : tl' ≤ s.core.tmp_len + 1) (htl_cv : tl' ≤ s.core.cur_vars)
    (htc_ge : s.core.tmp_cnt ≤ tc') (htpres : ∀ k < s.core.tmp_len, tmp'[k]? = s.core.tmp[k]?)
    (hnewt : ∀ j, s.core.tmp_len ≤ j → j < tl' → (tmp'[j]?.getD 0#32).toNat = lit.toNat ∧
      (s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat < s.core.cur_level)
    (htc_eq : tc' = s.core.tmp_cnt +
      if (s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat = s.core.cur_level then 1 else 0)
    (hok : ok = true → ((s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat = s.core.cur_level →
        tc' = s.core.tmp_cnt + 1) ∧ ((s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat <
        s.core.cur_level → tl' = s.core.tmp_len + 1 ∧ tmp'[s.core.tmp_len]? = some lit))
    (hm : (FullMem c (anaLitSt s (s.core.mrk.set (lit.toNat / 2) 1#8) tmp'
      (s.scratch.work_stk1.set s.core.min_clr_len (lit >>> 1)) (s.core.min_clr_len + 1)
      tc' tl' (s.scratch.ant_sz + 1#64) (s.scratch.res_sz + 1#64)) ⋆ R) m)
    (hQ : AnaLitQ c s R lit skip_var Q) : Q (ok, ()) m := by
  have hcv_le := hlen.core_ok.cur_vars_le
  have ⟨hmcl_lt, hw0⟩ := anaWorkInv_step_lshr hlen hwork lit hvlt hm0
  let mrk1 := s.core.mrk.set (lit.toNat / 2) 1#8
  let ws1 := s.scratch.work_stk1.set s.core.min_clr_len (lit >>> 1)
  have hlen' : (anaLitSt s mrk1 tmp' ws1 (s.core.min_clr_len + 1) tc' tl'
      (s.scratch.ant_sz + 1#64) (s.scratch.res_sz + 1#64)).LengthsOk c :=
    ⟨{ hlen.core_ok with
        mrk_len := (by dsimp [anaLitSt, mrk1]; rw [List.length_set, hlen.core_ok.mrk_len])
        tmp_len_arr := htmp_len
        tmp_len_le := (by dsimp [anaLitSt]; omega)
        min_clr_len_le := (by dsimp [anaLitSt]; omega) },
     { hlen.scratch_ok with
        work_stk1_len := (by
          dsimp [anaLitSt, ws1]; rw [List.length_set, hlen.scratch_ok.work_stk1_len]) }⟩
  have hm1 : mrk1[lit.toNat / 2]?.getD 0#8 ≠ 0#8 := by
    rw [List.getElem?_set_self (by rw [hlen.core_ok.mrk_len]; omega)]; decide
  refine hQ ok mrk1 tmp' ws1 (s.core.min_clr_len + 1) tc' tl' (s.scratch.ant_sz + 1#64)
    (s.scratch.res_sz + 1#64) m hlen' hw0 htl_cv htl_ge htl_inc htc_ge
    (fun _ _ hnz => by rw [List.getElem?_set_ne fun heq => hnz (by rw [← heq, hm0])]) htpres
    (fun w _ hw0 hnz' => if hwe : w = lit.toNat / 2 then by subst w; exact ⟨rfl, hvne, hvl_pos,
        hvl_le⟩ else absurd hw0 (by rwa [List.getElem?_set_ne (Ne.symm hwe)] at hnz'))
    (fun j h1 h2 => let ⟨hl, hlt⟩ := hnewt j h1 h2; ⟨hl, hvlt, hvne, hm0, hvl_pos, hlt, hm1⟩)
    (by simp [hvlt, hvl_pos, hvl_le]) (by simp [hvlt, hm0, hm1])
    (by simpa [hvlt, hm0, hm1] using htc_eq) (fun h => ⟨hvlt, fun _ => ⟨fun _ => hm1, fun _ =>
      ⟨hvl_le, fun _ hcl => (hok h).1 hcl, fun _ hlt => (hok h).2 hlt⟩⟩⟩) hm

private theorem full_analyze_lit_ret_false (lit skip_var : BitVec 32)
    {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [.bool]}
    (hlen : s.LengthsOk c) (htl_cv : s.core.tmp_len ≤ s.core.cur_vars)
    (hwork : AnaWorkInv c s) (hm : (FullMem c s ⋆ R) m) (hQ : AnaLitQ c s R lit skip_var Q)
    (hbad : ¬ (lit.toNat / 2 < s.core.cur_vars ∧
      (s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat ≤ s.core.cur_level)) : Q (false, ()) m :=
  hQ false s.core.mrk s.core.tmp s.scratch.work_stk1 s.core.min_clr_len s.core.tmp_cnt
    s.core.tmp_len s.scratch.ant_sz s.scratch.res_sz m hlen hwork htl_cv (Nat.le_refl _)
    (by omega) (Nat.le_refl _) (fun _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ h0 h => absurd h0 h)
    (fun _ h1 h2 => by omega) (by rw [ite_eq_right (fun h => hbad ⟨h.1, h.2.2⟩)]; simp)
    (by rw [ite_eq_right (fun h => h.2.2 h.2.1)]; simp)
    (by rw [ite_eq_right (fun h => h.2.2.1 h.2.1)]; simp) (fun hc => by cases hc) hm

private theorem full_analyze_lit_ret_lvl0 (lit skip_var : BitVec 32)
    {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [.bool]}
    (hlen : s.LengthsOk c) (htl_cv : s.core.tmp_len ≤ s.core.cur_vars)
    (hwork : AnaWorkInv c s) (hm : (FullMem c s ⋆ R) m) (hQ : AnaLitQ c s R lit skip_var Q)
    (hvlt : lit.toNat / 2 < s.core.cur_vars)
    (h0 : (s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat = 0) : Q (true, ()) m :=
  hQ true s.core.mrk s.core.tmp s.scratch.work_stk1 s.core.min_clr_len s.core.tmp_cnt
    s.core.tmp_len s.scratch.ant_sz s.scratch.res_sz m hlen hwork htl_cv (Nat.le_refl _)
    (by omega) (Nat.le_refl _) (fun _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ h0 h => absurd h0 h)
    (fun _ h1 h2 => by omega) (by simp [h0]) (by rw [ite_eq_right (fun h => h.2.2 h.2.1)]; simp)
    (by rw [ite_eq_right (fun h => h.2.2.1 h.2.1)]; simp) (fun _ => ⟨hvlt, fun _ =>
      ⟨fun _ => by omega, fun _ => ⟨by omega, fun _ _ => by omega, fun _ => by omega⟩⟩⟩) hm

private theorem full_analyze_lit_ret_skip (lit skip_var : BitVec 32)
    {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m' : Mem 64} {Q : Post [.bool]}
    (hlen : s.LengthsOk c) (htl_cv : s.core.tmp_len ≤ s.core.cur_vars)
    (hwork : AnaWorkInv c s) (hQ : AnaLitQ c s R lit skip_var Q)
    (hvlt : lit.toNat / 2 < s.core.cur_vars)
    (hcase : lit.toNat / 2 = skip_var.toNat ∨ s.core.mrk[lit.toNat / 2]?.getD 0#8 ≠ 0#8)
    (hpos : 0 < (s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat)
    (hle : (s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat ≤ s.core.cur_level)
    (hm' : (FullMem c { s with scratch := { s.scratch with
      ant_sz := s.scratch.ant_sz + 1 } } ⋆ R) m') : Q (true, ()) m' :=
  hQ true s.core.mrk s.core.tmp s.scratch.work_stk1 s.core.min_clr_len s.core.tmp_cnt s.core.tmp_len
    (s.scratch.ant_sz + 1) s.scratch.res_sz m' ⟨hlen.core_ok, { hlen.scratch_ok with }⟩ hwork
    htl_cv (Nat.le_refl _) (by omega) (Nat.le_refl _) (fun _ _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ h0 h => absurd h0 h) (fun _ h1 h2 => by omega) (by simp [hvlt, hpos, hle])
    (by rw [ite_eq_right (fun h => h.2.2 h.2.1)]; simp)
    (by rw [ite_eq_right (fun h => h.2.2.1 h.2.1)]; simp) (fun _ => ⟨hvlt, fun hne =>
      hcase.elim (fun h => absurd h hne) fun h => ⟨fun _ => h, fun hm0 => absurd hm0 h⟩⟩) hm'

theorem full_analyze_lit_wp (Γ : Env) :
    ∀ args m Q X, fullAnalyzeLitSpec args m Q X → Func.wp Γ full_analyze_lit_body args m Q X := by
  rintro ⟨h, lit, skip_var, ⟨⟩⟩ m Q X
    ⟨c, s, R, rfl, hlen, hcur32, htl_cv, htc_fit, hwork, hm, hQ⟩
  have hmax32 := fullInv_max_vars_lt32 c; have hcv_le := hlen.core_ok.cur_vars_le
  have hmcl_le := hlen.core_ok.min_clr_len_le; have hml := hlen.core_ok.mrk_len
  have hll := hlen.core_ok.lvl_len; have htl := hlen.core_ok.tmp_len_arr
  have hws_l := hlen.scratch_ok.work_stk1_len
  have hcur_tr : ((BitVec.ofNat 64 s.core.cur_level).setWidth 32).toNat = s.core.cur_level := by
    rw [bv64_trunc32_ofNat hcur32, bv32_ofNat_toNat hcur32]
  have hm2_mod : s.core.cur_level % 2 ^ 64 = s.core.cur_level := Nat.mod_eq_of_lt (by omega)
  have hm3_mod : s.core.cur_vars % 2 ^ 64 = s.core.cur_vars := Nat.mod_eq_of_lt (by omega)
  have hm4_mod : s.core.tmp_len % 2 ^ 64 = s.core.tmp_len := Nat.mod_eq_of_lt (by omega)
  have hm5_mod : s.core.min_clr_len % 2 ^ 64 = s.core.min_clr_len := Nat.mod_eq_of_lt (by omega)
  have hv_lt_of (h : ¬ s.core.cur_vars % 2 ^ 64 ≤ lit.toNat / 2) :
      lit.toNat / 2 < s.core.cur_vars := by rw [hm3_mod] at h; omega
  have hm0_of (hvlt : lit.toNat / 2 < s.core.cur_vars)
      (h : s.core.mrk[lit.toNat / 2]'(by omega) = 0#8) :
      s.core.mrk[lit.toNat / 2]?.getD 0#8 = 0#8 := by
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; exact h
  have hmrk_set_eq : s.core.mrk.set ((lit >>> 1).setWidth 64).toNat 1#8 =
      s.core.mrk.set (lit.toNat / 2) 1#8 := by simp only [bv_c0_zext32_64, bv32_lshr_1]
  have hws_set_eq : s.scratch.work_stk1.set (BitVec.ofNat 64 s.core.min_clr_len).toNat (lit >>> 1) =
      s.scratch.work_stk1.set s.core.min_clr_len (lit >>> 1) := by rw [bv64_ofNat_toNat (by omega)]
  have hmcl1 : (BitVec.ofNat 64 s.core.min_clr_len + 1).toNat = s.core.min_clr_len + 1 := by
    simp only [bv_c0, BitVec.reduceToNat]; omega
  have hret_sk (hvlt : lit.toNat / 2 < s.core.cur_vars)
      (hnot : ¬ (s.core.cur_level % 2 ^ 64) % 2 ^ 32 < (s.core.lvl[lit.toNat / 2]'(by omega)).toNat)
      (hnz : s.core.lvl[lit.toNat / 2]'(by omega) ≠ 0#32)
      (hcase : lit.toNat / 2 = skip_var.toNat ∨ s.core.mrk[lit.toNat / 2]?.getD 0#8 ≠ 0#8)
      {m'} (hm' : (FullMem c { s with scratch := { s.scratch with
        ant_sz := s.scratch.ant_sz + 1 } } ⋆ R) m') : Q (true, ()) m' := by
    rw [hm2_mod, Nat.mod_eq_of_lt hcur32] at hnot
    have hle : (s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat ≤ s.core.cur_level := by
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; omega
    exact full_analyze_lit_ret_skip lit skip_var hlen htl_cv hwork hQ hvlt hcase (mk_lvl_pos hnz)
      hle hm'
  fa_steps
  · have hbad : s.core.cur_vars % 2 ^ 64 ≤ lit.toNat / 2 := by assumption
    rw [hm3_mod] at hbad
    exact full_analyze_lit_ret_false lit skip_var hlen htl_cv hwork hm hQ (by omega)
  · have hvlt := hv_lt_of ‹_›
    apply full_analyze_lit_ret_lvl0 lit skip_var hlen htl_cv hwork hm hQ hvlt
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some,
      show s.core.lvl[lit.toNat / 2]'(by omega) = 0#32 from ‹_›]; rfl
  · have hvlt := hv_lt_of ‹_›; apply full_analyze_lit_ret_false lit skip_var hlen htl_cv hwork hm hQ
    rintro ⟨_, hle⟩; rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hle
    have hgt : s.core.cur_level % 2 ^ 64 % 2 ^ 32 <
        (s.core.lvl[lit.toNat / 2]'(by omega)).toNat := ‹_›
    rw [hm2_mod, Nat.mod_eq_of_lt hcur32] at hgt; omega
  · have hvlt := hv_lt_of ‹_›; have hm0 := hm0_of hvlt ‹_›
    have hvl_eq : (s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat = s.core.cur_level := by
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some,
        show s.core.lvl[lit.toNat / 2]'(by omega) = (BitVec.ofNat 64 s.core.cur_level).setWidth 32
          from ‹_›, hcur_tr]
    have htc1 : (BitVec.ofNat 64 s.core.tmp_cnt + 1).toNat = s.core.tmp_cnt + 1 := by
      simp only [bv_c0, BitVec.reduceToNat]; omega
    try rw [show (1#64 : BitVec 64).setWidth 8 = 1#8 from rfl] at hm
    rw [hmrk_set_eq, hws_set_eq, htc1, hmcl1] at hm
    exact full_analyze_lit_mark true s.core.tmp (s.core.tmp_cnt + 1) s.core.tmp_len
      hlen hwork hvlt (mk_lit_ne_skip ‹_›) hm0 (mk_lvl_pos ‹_›) (by omega) htl (Nat.le_refl _)
      (by omega) htl_cv (by omega) (fun _ _ => rfl) (fun _ h1 h2 => by omega)
      (by simp [hvl_eq]) (fun _ => ⟨fun _ => rfl, fun h => by omega⟩) hm hQ
  · have hvlt := hv_lt_of ‹_›; have hm0 := hm0_of hvlt ‹_›
    have hle_lvl : ¬ (s.core.cur_level % 2 ^ 64) % 2 ^ 32 <
        (s.core.lvl[lit.toNat / 2]'(by omega)).toNat := ‹_›
    rw [hm2_mod] at hle_lvl; have hvl_lt := lvl_lt_cur_of_le_ne (by omega) hcur32 hle_lvl ‹_›
    try rw [show (1#64 : BitVec 64).setWidth 8 = 1#8 from rfl] at hm
    rw [hmrk_set_eq, hws_set_eq, hmcl1] at hm
    exact full_analyze_lit_mark false s.core.tmp s.core.tmp_cnt s.core.tmp_len
      hlen hwork hvlt (mk_lit_ne_skip ‹_›) hm0 (mk_lvl_pos ‹_›) (by omega) htl (Nat.le_refl _)
      (by omega) htl_cv (Nat.le_refl _) (fun _ _ => rfl) (fun _ h1 h2 => by omega)
      (by rw [ite_eq_right (fun _ => by omega), Nat.add_zero]) (fun hc => by cases hc) hm hQ
  · have hvlt := hv_lt_of ‹_›; have hm0 := hm0_of hvlt ‹_›
    have htl_b : ¬ s.core.cur_vars % 2 ^ 64 ≤ s.core.tmp_len % 2 ^ 64 := ‹_›
    rw [hm3_mod, hm4_mod] at htl_b
    have hle_lvl : ¬ (s.core.cur_level % 2 ^ 64) % 2 ^ 32 <
        (s.core.lvl[lit.toNat / 2]'(by omega)).toNat := ‹_›
    rw [hm2_mod] at hle_lvl; have hvl_lt := lvl_lt_cur_of_le_ne (by omega) hcur32 hle_lvl ‹_›
    have htl1 : (BitVec.ofNat 64 s.core.tmp_len + 1).toNat = s.core.tmp_len + 1 := by
      simp only [bv_c0, BitVec.reduceToNat]; omega
    try rw [show (1#64 : BitVec 64).setWidth 8 = 1#8 from rfl] at hm
    rw [hmrk_set_eq, hws_set_eq, show s.core.tmp.set (BitVec.ofNat 64 s.core.tmp_len).toNat lit =
        s.core.tmp.set s.core.tmp_len lit by rw [bv64_ofNat_toNat (by omega)], htl1, hmcl1] at hm
    exact full_analyze_lit_mark true (s.core.tmp.set s.core.tmp_len lit) s.core.tmp_cnt
      (s.core.tmp_len + 1) hlen hwork hvlt (mk_lit_ne_skip ‹_›) hm0 (mk_lvl_pos ‹_›) (by omega)
      (by simp [htl]) (by omega) (Nat.le_refl _) (by omega) (Nat.le_refl _)
      (fun _ hk => List.getElem?_set_ne (by omega)) (fun j h1 h2 => ⟨by
        have hje : j = s.core.tmp_len := by omega
        subst hje; rw [List.getElem?_set_self (by omega)]; rfl, hvl_lt⟩)
      (by rw [ite_eq_right (fun _ => by omega), Nat.add_zero])
      (fun _ => ⟨fun he => by omega, fun _ => ⟨rfl, List.getElem?_set_self (by omega)⟩⟩) hm hQ
  all_goals first
    | (have hvlt := hv_lt_of ‹_›; have hm0 := hm0_of hvlt ‹_›
       have hmcl : ¬ s.core.min_clr_len % 2 ^ 64 < s.core.cur_vars % 2 ^ 64 := ‹_›
       rw [hm5_mod, hm3_mod] at hmcl; exact absurd (anaWorkInv_step hlen hwork hvlt hm0).1 hmcl)
    | exact hret_sk (hv_lt_of ‹_›) ‹_› ‹_› (Or.inr (mrk_getD_ne_zero (hv := by omega) ‹_›)) hm
    | (refine hret_sk (hv_lt_of ‹_›) ‹_› ‹_› (Or.inl ?_) hm
       have := congrArg BitVec.toNat (‹lit >>> 1 = skip_var›); rwa [bv32_lshr_1] at this)

/-! ## 3. `full_clear_ana_wp` -/

theorem full_clear_ana_wp (Γ : Env) :
    ∀ args m Q X, fullClearAnaSpec args m Q X → Func.wp Γ full_clear_ana_body args m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hwork, hm0, hQ⟩
  have hmax32 := fullInv_max_vars_lt32 c; have hcv_le := hlen.core_ok.cur_vars_le
  have hm_len := hlen.core_ok.mrk_len; have hmcl_le := hwork.1
  let LoopInv : Nat → List (BitVec 8) → Prop := fun i mrk' =>
    i ≤ s.core.min_clr_len ∧ mrk'.length = c.max_vars ∧
    (∀ v < c.max_vars, (∀ k < i, (s.scratch.work_stk1[k]?.getD 0#32).toNat ≠ v) →
      mrk'[v]?.getD 0#8 = s.core.mrk[v]?.getD 0#8) ∧
    (∀ k < i, mrk'[(s.scratch.work_stk1[k]?.getD 0#32).toNat]?.getD 0#8 = 0#8)
  fa_steps
  refine wp_loop_group (fun r (iv, ()) ml => ∃ i mrk',
    r = s.core.min_clr_len - i ∧ iv = BitVec.ofNat 64 i ∧ LoopInv i mrk' ∧
    (FullMem c { s with core := { s.core with mrk := mrk' } } ⋆ R) ml) ?_ ?_
  · clear hm0; rintro L r ⟨iv, ⟨⟩⟩ ml ih ⟨i, mrk', rfl, rfl, ⟨hile, hml_l, hpres, hclr⟩, hml0⟩
    have himod : i % 2 ^ 64 = i := Nat.mod_eq_of_lt (by omega)
    have hcvmod : s.core.cur_vars % 2 ^ 64 = s.core.cur_vars := Nat.mod_eq_of_lt (by omega)
    fa_steps
    · have hilt : i < s.core.min_clr_len := by omega
      have hws_lt : i < s.scratch.work_stk1.length := by
        have := hlen.scratch_ok.work_stk1_len; omega
      have hv_lt : (s.scratch.work_stk1[i]'hws_lt).toNat < s.core.cur_vars := by
        have hw1 := (hwork.2.2.1 i hilt).1
        rwa [List.getElem?_eq_getElem hws_lt, Option.getD_some] at hw1
      have hv_get : (s.scratch.work_stk1[i]?.getD 0#32).toNat =
          (s.scratch.work_stk1[i]'hws_lt).toNat := by
        rw [List.getElem?_eq_getElem hws_lt, Option.getD_some]
      fa_steps
      · rw [show BitVec.ofNat 64 i + 1 = BitVec.ofNat 64 (i + 1) from
          BitVec.eq_of_toNat_eq (by bv_omega)]
        refine ih (s.core.min_clr_len - (i + 1)) _ _ (by omega)
          ⟨i + 1, mrk'.set (s.scratch.work_stk1[i]'hws_lt).toNat 0#8, rfl, rfl,
            ⟨by omega, by simp [hml_l], fun v hv hni => ?_, fun k hk => ?_⟩, ?_⟩
        · rw [List.getElem?_set_ne fun heq => hni i (Nat.lt_succ_self _) (by rw [hv_get, heq])]
          exact hpres v hv fun k hk => hni k (by omega)
        · by_cases hki : k = i
          · subst k; rw [hv_get, List.getElem?_set_self (by omega)]; rfl
          · by_cases heq : (s.scratch.work_stk1[k]?.getD 0#32).toNat =
                (s.scratch.work_stk1[i]'hws_lt).toNat
            · rw [heq, List.getElem?_set_self (by omega)]; rfl
            · rw [List.getElem?_set_ne (Ne.symm heq)]; exact hclr k (by omega)
        · have hidx_eq : s.scratch.work_stk1[(BitVec.ofNat 64 i).toNat]'(by
              rw [bv64_ofNat_toNat (by omega)]; exact hws_lt) = s.scratch.work_stk1[i]'hws_lt :=
            getElem_eq_of_idx (bv64_ofNat_toNat (by omega))
          have hmrk_eq : mrk'.set (BitVec.setWidth 64
              (s.scratch.work_stk1[(BitVec.ofNat 64 i).toNat]'(by
                rw [bv64_ofNat_toNat (by omega)]; exact hws_lt))).toNat 0#8 =
              mrk'.set (s.scratch.work_stk1[i]'hws_lt).toNat 0#8 := by rw [bv_c0_zext32_64, hidx_eq]
          rw [← hmrk_eq]; exact hm
      · exfalso
        have hcw : (s.scratch.work_stk1[i % 2 ^ 64]'(by rw [himod]; exact hws_lt)).toNat =
            (s.scratch.work_stk1[i]'hws_lt).toNat := congrArg BitVec.toNat (getElem_eq_of_idx himod)
        have hbad : ¬ (s.scratch.work_stk1[i % 2 ^ 64]'(by rw [himod]; exact hws_lt)).toNat <
            s.core.cur_vars % 2 ^ 64 := by assumption
        rw [hcw, hcvmod] at hbad; omega
    · have hieq : i = s.core.min_clr_len := by omega
      subst hieq; fa_steps
      exact hQ mrk' _ { hlen with core_ok := { hlen.core_ok with
        mrk_len := hml_l, min_clr_len_le := (by dsimp; omega) } }
        (clear_ana_restores_marksClear hwork hpres hclr) (by assumption)
  · intro L hL; fa_steps
    refine hL s.core.min_clr_len _ m ⟨0, s.core.mrk, by omega, rfl,
      ⟨Nat.zero_le _, hm_len, fun _ _ _ => rfl, fun _ hk => by omega⟩, hm0⟩

/-! ## 4. `full_analyze_rsn_wp` -/

private theorem bv64_ite_iff {P Q : Prop} [Decidable P] [Decidable Q] (h : P ↔ Q) :
    (if P then (1#64 : BitVec 64) else 0#64) = BitVec.ofNat 64 (if Q then 1 else 0) := by
  by_cases hp : P
  · simp [hp, h.mp hp]
  · simp [hp, mt h.mpr hp]

private theorem res_step_of_lit {s_mrk mrk1 mrk2 : List (BitVec 8)} {mv v : Nat}
    {r0 r1 r2 : BitVec 64}
    (hmp0 : ∀ w < mv, s_mrk[w]?.getD 0#8 ≠ 0#8 → mrk1[w]?.getD 0#8 = s_mrk[w]?.getD 0#8)
    (hmp1 : ∀ w < mv, mrk1[w]?.getD 0#8 ≠ 0#8 → mrk2[w]?.getD 0#8 = mrk1[w]?.getD 0#8)
    (hnew1 : ∀ w < mv, mrk1[w]?.getD 0#8 = 0#8 → mrk2[w]?.getD 0#8 ≠ 0#8 → v = w)
    (hr1 : r1 = r0 + BitVec.ofNat 64 ((List.range mv).filter fun w =>
      decide (s_mrk[w]?.getD 0#8 = 0#8) && decide (mrk1[w]?.getD 0#8 ≠ 0#8)).length)
    (hr2 : r2 = r1 + if v < mv ∧ mrk1[v]?.getD 0#8 = 0#8 ∧ mrk2[v]?.getD 0#8 ≠ 0#8
      then 1#64 else 0#64) : r2 = r0 + BitVec.ofNat 64 ((List.range mv).filter fun w =>
      decide (s_mrk[w]?.getD 0#8 = 0#8) && decide (mrk2[w]?.getD 0#8 ≠ 0#8)).length := by
  let c1 := ((List.range mv).filter fun w =>
    decide (s_mrk[w]?.getD 0#8 = 0#8) && decide (mrk1[w]?.getD 0#8 ≠ 0#8)).length
  have hf := filter_step_of_lit (fun _ => true) (tc0 := 0) (tc1 := c1)
    (tc2 := c1 + if v < mv ∧ mrk1[v]?.getD 0#8 = 0#8 ∧ mrk2[v]?.getD 0#8 ≠ 0#8 ∧
      (true : Bool) = true then 1 else 0) hmp0 hmp1 hnew1 (Nat.zero_le _) (by simp [c1]) rfl
  simp only [Nat.sub_zero, Bool.and_true, and_true] at hf
  rw [hr2, hr1, BitVec.add_assoc]; congr 1; dsimp only [c1] at hf; rw [← hf]
  split <;> simp [BitVec.ofNat_add]

theorem FullAnalyzeHelpers.mem_fullRsnLits_bin {s : FullState} {rsn : BitVec 32} {l : Nat}
    (hne : rsn ≠ 0xFFFFFFFF#32) (hbin : (rsn &&& 0x80000000#32) ≠ 0#32) :
    l ∈ fullRsnLits s rsn ↔ l = (rsn &&& 0x7FFFFFFF#32).toNat := by simp [fullRsnLits, hne, hbin]

theorem FullAnalyzeHelpers.mem_fullRsnLits_large {s : FullState} {rsn : BitVec 32} {l : Nat}
    (hne : rsn ≠ 0xFFFFFFFF#32) (hlarge : (rsn &&& 0x80000000#32) = 0#32) :
    l ∈ fullRsnLits s rsn ↔ l ∈ fullArenaClauseLits s rsn.toNat := by
  simp [fullRsnLits, hne, hlarge]

private theorem fullMem_arena_eq {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {ar1 ar2 : List (BitVec 32)} {gu : List (BitVec 32)} (h : ar1 = ar2)
    (hm : (FullMem c ⟨{ s.core with arena := ar1 }, { s.scratch with glue_used := gu }⟩ ⋆ R) m) :
    (FullMem c ⟨{ s.core with arena := ar2 }, { s.scratch with glue_used := gu }⟩ ⋆ R) m := by
  subst h; exact hm

private abbrev RsnStepPre (s : FullState) (rsn_lits : List Nat) (skip_var : BitVec 32)
    (mrk' : List (BitVec 8)) (tmp' : List (BitVec 32)) (tc' tl' : Nat) (res' : BitVec 64) : Prop :=
  (∀ w < s.core.cur_vars, s.core.mrk[w]?.getD 0#8 ≠ 0#8 →
    mrk'[w]?.getD 0#8 = s.core.mrk[w]?.getD 0#8) ∧
  (∀ k < s.core.tmp_len, tmp'[k]? = s.core.tmp[k]?) ∧
  (∀ w < s.core.cur_vars, s.core.mrk[w]?.getD 0#8 = 0#8 → mrk'[w]?.getD 0#8 ≠ 0#8 →
    ∃ l ∈ rsn_lits, l / 2 = w ∧ w ≠ skip_var.toNat ∧
      0 < (s.core.lvl[w]?.getD 0#32).toNat ∧ (s.core.lvl[w]?.getD 0#32).toNat ≤ s.core.cur_level) ∧
  (∀ j, s.core.tmp_len ≤ j → j < tl' → let l := (tmp'[j]?.getD 0#32).toNat
    l ∈ rsn_lits ∧ l < 2 * s.core.cur_vars ∧ l / 2 ≠ skip_var.toNat ∧
    s.core.mrk[l / 2]?.getD 0#8 = 0#8 ∧ 0 < (s.core.lvl[l / 2]?.getD 0#32).toNat ∧
    (s.core.lvl[l / 2]?.getD 0#32).toNat < s.core.cur_level ∧ mrk'[l / 2]?.getD 0#8 ≠ 0#8) ∧
  (∀ j1 j2, s.core.tmp_len ≤ j1 → j1 < j2 → j2 < tl' →
    (tmp'[j1]?.getD 0#32).toNat / 2 ≠ (tmp'[j2]?.getD 0#32).toNat / 2) ∧
  (tc' - s.core.tmp_cnt = ((List.range s.core.cur_vars).filter fun w =>
    decide (s.core.mrk[w]?.getD 0#8 = 0#8) && decide (mrk'[w]?.getD 0#8 ≠ 0#8) &&
    decide ((s.core.lvl[w]?.getD 0#32).toNat = s.core.cur_level)).length) ∧
  (res' = s.scratch.res_sz + BitVec.ofNat 64 ((List.range s.core.cur_vars).filter fun w =>
    decide (s.core.mrk[w]?.getD 0#8 = 0#8) && decide (mrk'[w]?.getD 0#8 ≠ 0#8)).length)

private theorem rsn_comb_step {s : FullState} {l_bv skip_var : BitVec 32} {rsn_lits : List Nat}
    {mrk' mrk2 : List (BitVec 8)} {tmp' tmp2 : List (BitVec 32)} {tc' tl' tc2 tl2 : Nat}
    {res' res2 : BitVec 64} (htl_ge : s.core.tmp_len ≤ tl') (htl2_ge : tl' ≤ tl2)
    (htl2_inc : tl2 ≤ tl' + 1) (htc_ge : s.core.tmp_cnt ≤ tc') (hl_mem : l_bv.toNat ∈ rsn_lits)
    (hpre : RsnStepPre s rsn_lits skip_var mrk' tmp' tc' tl' res')
    (hmp2 : ∀ w < s.core.cur_vars, mrk'[w]?.getD 0#8 ≠ 0#8 →
      mrk2[w]?.getD 0#8 = mrk'[w]?.getD 0#8) (htp2 : ∀ k < tl', tmp2[k]? = tmp'[k]?)
    (hnm2 : ∀ w < s.core.cur_vars, mrk'[w]?.getD 0#8 = 0#8 → mrk2[w]?.getD 0#8 ≠ 0#8 →
      l_bv.toNat / 2 = w ∧ w ≠ skip_var.toNat ∧ 0 < (s.core.lvl[w]?.getD 0#32).toNat ∧
      (s.core.lvl[w]?.getD 0#32).toNat ≤ s.core.cur_level)
    (hnt2 : ∀ j, tl' ≤ j → j < tl2 → (tmp2[j]?.getD 0#32).toNat = l_bv.toNat ∧
      l_bv.toNat / 2 < s.core.cur_vars ∧ l_bv.toNat / 2 ≠ skip_var.toNat ∧
      mrk'[l_bv.toNat / 2]?.getD 0#8 = 0#8 ∧ 0 < (s.core.lvl[l_bv.toNat / 2]?.getD 0#32).toNat ∧
      (s.core.lvl[l_bv.toNat / 2]?.getD 0#32).toNat < s.core.cur_level ∧
      mrk2[l_bv.toNat / 2]?.getD 0#8 ≠ 0#8)
    (hres2 : res2 = res' + if l_bv.toNat / 2 < s.core.cur_vars ∧
      mrk'[l_bv.toNat / 2]?.getD 0#8 = 0#8 ∧ mrk2[l_bv.toNat / 2]?.getD 0#8 ≠ 0#8
      then 1#64 else 0#64)
    (htc2_eq : tc2 = tc' + if l_bv.toNat / 2 < s.core.cur_vars ∧
      mrk'[l_bv.toNat / 2]?.getD 0#8 = 0#8 ∧ mrk2[l_bv.toNat / 2]?.getD 0#8 ≠ 0#8 ∧
      (s.core.lvl[l_bv.toNat / 2]?.getD 0#32).toNat = s.core.cur_level then 1 else 0) :
    RsnStepPre s rsn_lits skip_var mrk2 tmp2 tc2 tl2 res2 := by
  obtain ⟨hmp, htp, hnm, hnt, hnd, hcnt, hres_l⟩ := hpre
  refine ⟨fun w hw hnz => by have h1 := hmp w hw hnz; rw [hmp2 w hw (by rwa [h1]), h1],
    fun k hk => by rw [htp2 k (by omega), htp k hk], fun w hw hs0 hmnz => ?_, fun j hj1 hj2 => ?_,
    fun j1 j2 hj1 hj12 hj2 => ?_, ?_, ?_⟩
  · by_cases hm1 : mrk'[w]?.getD 0#8 = 0#8
    · obtain ⟨rfl, hne', hpos, hle⟩ := hnm2 w hw hm1 hmnz
      exact ⟨l_bv.toNat, hl_mem, rfl, hne', hpos, hle⟩
    · exact hnm w hw hs0 hm1
  · by_cases hjold : j < tl'
    · rw [htp2 j hjold]; obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hnt j hj1 hjold
      exact ⟨h1, h2, h3, h4, h5, h6, by rw [hmp2 _ (by omega) h7]; exact h7⟩
    · obtain ⟨heq, hlt, hne', hm1_0, hpos, hcl, _⟩ := hnt2 j (by omega) hj2
      have hs0 : s.core.mrk[l_bv.toNat / 2]?.getD 0#8 = 0#8 :=
        Classical.byContradiction fun hnz => by rw [hmp _ hlt hnz] at hm1_0; exact hnz hm1_0
      exact ⟨by rwa [heq], by omega, by omega, by rwa [heq], by rwa [heq], by rwa [heq],
        by rwa [heq]⟩
  · by_cases hj2_old : j2 < tl'
    · rw [htp2 j1 (by omega), htp2 j2 hj2_old]; exact hnd j1 j2 hj1 hj12 hj2_old
    · have hj1_old : j1 < tl' := by omega
      rw [htp2 j1 hj1_old]; have h1 := (hnt j1 hj1 hj1_old).2.2.2.2.2.2
      obtain ⟨heq, _, _, hm1_0, _⟩ := hnt2 j2 (by omega) hj2
      rw [heq]; intro heq_v; rw [← heq_v] at hm1_0; exact absurd hm1_0 h1
  · exact filter_step_of_lit (fun w => decide ((s.core.lvl[w]?.getD 0#32).toNat = s.core.cur_level))
      (mv := s.core.cur_vars) (tc0 := s.core.tmp_cnt) (tc1 := tc') (v := l_bv.toNat / 2)
      hmp hmp2 (fun w hw h0 hnz => (hnm2 w hw h0 hnz).1) htc_ge hcnt
      (by simpa only [decide_eq_true_eq] using htc2_eq)
  · exact res_step_of_lit (mv := s.core.cur_vars) (v := l_bv.toNat / 2) hmp hmp2
      (fun w hw h0 hnz => (hnm2 w hw h0 hnz).1) hres_l hres2

private abbrev rsnState (s : FullState) (mrk' : List (BitVec 8))
    (tmp' ws1' arena' gu' : List (BitVec 32)) (mcl' tc' tl' : Nat) (ant' res' : BitVec 64) :
    FullState :=
  { s with core := { s.core with mrk := mrk', tmp := tmp', tmp_cnt := tc', tmp_len := tl',
                                 min_clr_len := mcl', arena := arena' }
           scratch := { s.scratch with work_stk1 := ws1', glue_used := gu',
                                       ant_sz := ant', res_sz := res' } }

private abbrev RsnLoopInv (c : FullCfg) (s s1 : FullState) (rsn skip_var : BitVec 32)
    (antPred : Nat → Bool) (sz i : Nat) (mrk' : List (BitVec 8)) (tmp' ws1' : List (BitVec 32))
    (mcl' tc' tl' : Nat) (ant' res' : BitVec 64) : Prop :=
  i ≤ sz ∧ mrk'.length = c.max_vars ∧ tmp'.length = c.max_vars ∧ ws1'.length = 2 * c.max_vars ∧
  mcl' ≤ c.max_vars ∧ s.core.tmp_len ≤ tl' ∧ tl' ≤ s.core.cur_vars ∧ s.core.tmp_cnt ≤ tc' ∧
  AnaWorkInv c (rsnState s1 mrk' tmp' ws1' s1.core.arena s1.scratch.glue_used
    mcl' tc' tl' ant' res') ∧
  RsnStepPre s (fullArenaClauseLits s rsn.toNat) skip_var mrk' tmp' tc' tl' res' ∧
  (∀ w < s.core.cur_vars, s.core.mrk[w]?.getD 0#8 = 0#8 → mrk'[w]?.getD 0#8 ≠ 0#8 →
    (s.core.lvl[w]?.getD 0#32).toNat < s.core.cur_level →
    ∃ j, s.core.tmp_len ≤ j ∧ j < tl' ∧ (tmp'[j]?.getD 0#32).toNat / 2 = w) ∧
  ant' = s.scratch.ant_sz +
    BitVec.ofNat 64 (((fullArenaClauseLits s rsn.toNat).take i).countP antPred) ∧
  ∀ k < i, let l := (s.core.arena[rsn.toNat + 3 + k]?.getD 0#32).toNat
    l / 2 < s.core.cur_vars ∧ (l / 2 ≠ skip_var.toNat →
      (0 < (s.core.lvl[l / 2]?.getD 0#32).toNat → mrk'[l / 2]?.getD 0#8 ≠ 0#8) ∧
      (s.core.mrk[l / 2]?.getD 0#8 = 0#8 → (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ s.core.cur_level ∧
        (0 < (s.core.lvl[l / 2]?.getD 0#32).toNat → (s.core.lvl[l / 2]?.getD 0#32).toNat <
          s.core.cur_level → ∃ j, s.core.tmp_len ≤ j ∧ j < tl' ∧
          (tmp'[j]?.getD 0#32).toNat / 2 = l / 2)))

theorem full_analyze_rsn_wp (Γ : Env)
    (hLit : ∀ args m Q X, fullAnalyzeLitSpec args m Q X →
      Γ "full_analyze_lit" [i64, i32, i32] [.bool] args m Q X) :
    ∀ args m Q X, fullAnalyzeRsnSpec args m Q X → Func.wp Γ full_analyze_rsn_body args m Q X := by
  rintro ⟨h, rsn, skip_var, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, cut, s, R, rfl, hlen, hw, htl_cv, htc_fit, hwork, hrsn_ref, hm, hQ⟩
  have hmax32 := fullInv_max_vars_lt32 c; have hcv_le := hlen.core_ok.cur_vars_le
  have har_len := hlen.core_ok.arena_len_arr; have har_le := hlen.core_ok.arena_len_le
  have hgu_len := hlen.scratch_ok.glue_used_len
  have hcur32 : s.core.cur_level < 2 ^ 32 := by
    have := hw.cur_level_le; have := hlen.core_ok.trail_end_le; omega
  have hret_false_same : Q (false, ()) m :=
    hQ false s.core.mrk s.core.tmp s.scratch.work_stk1 s.core.min_clr_len s.core.tmp_cnt
      s.core.tmp_len s.core.arena s.scratch.glue_used s.scratch.ant_sz s.scratch.res_sz m
      hw hlen hwork (Nat.le_refl _) htl_cv (Nat.le_refl _) rfl (fun _ _ => ⟨rfl, rfl, rfl⟩)
      (fun _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ h0 h => absurd h0 h)
      (fun _ h1 h2 => by omega) (fun _ _ _ h1 h2 => by omega)
      (by rw [Nat.sub_self, filter_length_eq_zero_of_false]; intro _ _; simp)
      (by rw [filter_length_eq_zero_of_false (fun _ _ => by simp)]; simp) (fun hc => by cases hc) hm
  fa_unmdata; c0_step; c0_step
  · exact hret_false_same
  · c0_step
    · have hne : rsn ≠ 0xFFFFFFFF#32 := ‹_›; have hbin : (rsn &&& 0x80000000#32) ≠ 0#32 := ‹_›
      fa_steps
      refine wp_call_of_spec _ _ (hLit (c.hdr, rsn &&& 0x7FFFFFFF#32, skip_var, ()) _ _ _
        ⟨c, s, R, rfl, hlen, hcur32, htl_cv, by omega, hwork, hm, ?_⟩)
      intro ok mrk' tmp' ws1' mcl' tc' tl' ant' res' m' _ hlen' hwork' htl_le htl_ge _ htc_ge _
        hmpres htpres hnewm hnewt hant' hres' htc_eq hok hm'
      fa_steps
      have hsame_c := same_core_fullWitnessCut hw hlen'.core_ok.mrk_len hlen'.core_ok.tmp_len_arr
        hlen'.core_ok.min_clr_len_le htl_le (tc' := tc')
      have htc_f := filter_step_of_lit
        (fun w => decide ((s.core.lvl[w]?.getD 0#32).toNat = s.core.cur_level))
        (mv := s.core.cur_vars) (tc0 := s.core.tmp_cnt) (tc1 := s.core.tmp_cnt)
        (v := (rsn &&& 0x7FFFFFFF#32).toNat / 2) (fun _ _ _ => rfl) hmpres
        (fun w hw_lt h0 hnz => (hnewm w hw_lt h0 hnz).1) (Nat.le_refl _)
        (by rw [Nat.sub_self, filter_length_eq_zero_of_false]; intro _ _; simp)
        (by simpa only [decide_eq_true_eq] using htc_eq)
      have hres_f := res_step_of_lit (mv := s.core.cur_vars)
        (v := (rsn &&& 0x7FFFFFFF#32).toNat / 2) (r0 := s.scratch.res_sz)
        (r1 := s.scratch.res_sz) (fun _ _ _ => rfl) hmpres
        (fun w hw_lt h0 hnz => (hnewm w hw_lt h0 hnz).1)
        (by rw [filter_length_eq_zero_of_false (fun _ _ => by simp)]; simp) hres'
      refine hQ ok mrk' tmp' ws1' mcl' tc' tl' s.core.arena s.scratch.glue_used ant' res' m'
        hsame_c hlen' hwork' htl_ge htl_le htc_ge rfl (fun _ _ => ⟨rfl, rfl, rfl⟩)
        hmpres htpres ?_ ?_ (fun _ _ _ h1 h2 => by omega) htc_f hres_f ?_ hm'
      · intro w hw_lt h0 hnz; obtain ⟨rfl, hne', hpos, hle⟩ := hnewm w hw_lt h0 hnz
        exact ⟨(rsn &&& 0x7FFFFFFF#32).toNat, (mem_fullRsnLits_bin hne hbin).mpr rfl,
          rfl, hne', hpos, hle⟩
      · intro j hj1 hj2; obtain ⟨heq, _, _, h0, hpos, hcl, hmk⟩ := hnewt j hj1 hj2
        exact ⟨(mem_fullRsnLits_bin hne hbin).mpr heq, by omega, by omega, by rwa [heq],
          by rwa [heq], by rwa [heq], by rwa [heq]⟩
      · intro hok'; obtain ⟨hvlt, hrest⟩ := hok hok'
        refine ⟨hne, ?_, fun _ => hvlt, fun h0 => absurd h0 hbin, fun l hl => ?_⟩
        · rw [hant', fullRsnLits, ite_eq_right (fun h => hne h), ite_eq_left hbin,
            List.countP_cons, List.countP_nil, Nat.zero_add]
          exact congrArg (s.scratch.ant_sz + ·)
            (bv64_ite_iff (by simp only [decide_eq_true_eq]; rfl))
        · rw [mem_fullRsnLits_bin hne hbin] at hl; subst hl; refine ⟨hvlt, fun hne' => ?_⟩
          obtain ⟨hm1, h0r⟩ := hrest hne'; refine ⟨hm1, fun h0 => ?_⟩
          obtain ⟨hle, _, hlow⟩ := h0r h0
          exact ⟨hle, fun hpos hlt => let ⟨_, htget⟩ := hlow hpos hlt
            ⟨s.core.tmp_len, Nat.le_refl _, by omega, by rw [htget]; rfl⟩⟩
    · have hne : rsn ≠ 0xFFFFFFFF#32 := ‹_›; have hlarge : (rsn &&& 0x80000000#32) = 0#32 := ‹_›
      have href : rsn.toNat ∈ fullArenaClauseRefs s := hrsn_ref hne hlarge
      obtain ⟨hbd3, hsz3, hbd, hbd_le, _⟩ := hw.arena.refs_wf rsn.toNat href
      have hsz_get : (s.core.arena[rsn.toNat + 2]'(by omega)).toNat =
          fullArenaClauseSize s rsn.toNat := by
        unfold fullArenaClauseSize fullArenaClauseSizeCore
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      have hhdr_get : s.core.arena[rsn.toNat]'(by omega) = s.core.arena[rsn.toNat]?.getD 0#32 := by
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      fa_unmdata; (try c0_let_simp)
      c0_step; c0_step; c0_step; all_goals (try exact hret_false_same)
      c0_step; c0_step; c0_step; all_goals (try exact hret_false_same)
      c0_step; c0_step; all_goals (try exact hret_false_same)
      refine wp_join_group (ts := []) (fun () m1 => ∃ arena1 gu1,
          let s1 : FullState := { s with core := { s.core with arena := arena1 }
                                         scratch := { s.scratch with glue_used := gu1 } }
          FullWitnessCutInv c F0 F_cur cut s1.core ∧ s1.LengthsOk c ∧
          fullArenaClauseRefs s1 = fullArenaClauseRefs s ∧
          (∀ r ∈ fullArenaClauseRefs s, fullArenaClauseSize s1 r = fullArenaClauseSize s r ∧
            fullArenaClauseGarb s1 r = fullArenaClauseGarb s r ∧
            fullArenaClauseLits s1 r = fullArenaClauseLits s r) ∧
          (∀ k < fullArenaClauseSize s rsn.toNat,
            arena1[rsn.toNat + 3 + k]? = s.core.arena[rsn.toNat + 3 + k]?) ∧
          (FullMem c s1 ⋆ R) m1) ?_ ?_
      · rintro _ ⟨⟩ m1 ⟨arena1, gu1, hw1, hlen1, hrefs1, hcl1, har1_eq, hm1⟩
        fa_steps
        let s1 : FullState := { s with core := { s.core with arena := arena1 }
                                       scratch := { s.scratch with glue_used := gu1 } }
        have har1_len : arena1.length = c.arena_cap := hlen1.core_ok.arena_len_arr
        have har1_le : s.core.arena_len ≤ c.arena_cap := hlen1.core_ok.arena_len_le
        let sz : Nat := fullArenaClauseSize s rsn.toNat
        let antPred : Nat → Bool := fun l =>
          decide (l / 2 < s.core.cur_vars ∧ 0 < (s.core.lvl[l / 2]?.getD 0#32).toNat ∧
            (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ s.core.cur_level)
        refine wp_loop_group (fun r (iv, ()) ml => ∃ i mrk' tmp' ws1' mcl' tc' tl' ant' res',
          r = sz - i ∧ iv = BitVec.ofNat 32 i ∧
          RsnLoopInv c s s1 rsn skip_var antPred sz i mrk' tmp' ws1' mcl' tc' tl' ant' res' ∧
          (FullMem c (rsnState s mrk' tmp' ws1' arena1 gu1 mcl' tc' tl' ant' res') ⋆ R) ml) ?_ ?_
        · rintro L r ⟨iv, ⟨⟩⟩ ml ih ⟨i, mrk', tmp', ws1', mcl', tc', tl', ant', res', rfl, rfl,
            ⟨hile, hml_l, htl_l, hws_l, hmcl_le, htl_ge, htl_le, htc_ge, hwk', hpre, hnewlow,
              hant_l, hdone⟩, hml⟩
          have ⟨hmpres, htpres, hnewm, hnewt, hnd_t, hcnt, hres_l⟩ := hpre
          have hsz_mod : (rsn.toNat + (2#64).toNat) % 2 ^ 64 = rsn.toNat + 2 := by
            change (rsn.toNat + 2) % 2 ^ 64 = rsn.toNat + 2; omega
          have hidx_eq : s.core.arena[(rsn.toNat + (2#64).toNat) % 2 ^ 64]'(by omega) =
              s.core.arena[rsn.toNat + 2]'(by omega) := by simp only [hsz_mod]
          rw [Blocks.get_here]; fa_unmdata; (try c0_let_simp); c0_step
          · have hi32 : i < 2 ^ 32 := by omega
            have hilt : i < sz := by
              have hlt_bv : i % 2 ^ 32 <
                  (s.core.arena[(rsn.toNat + (2#64).toNat) % 2 ^ 64]'(by omega)).toNat := ‹_›
              rw [Nat.mod_eq_of_lt hi32, hidx_eq, hsz_get] at hlt_bv; exact hlt_bv
            have hidx_l : ((rsn.setWidth 64 + 3) + (BitVec.ofNat 32 i).setWidth 64).toNat =
                rsn.toNat + 3 + i := by simp only [bv_c0, BitVec.reduceToNat]; omega
            have hilt_core : i < fullArenaClauseSizeCore s.core rsn.toNat := hilt
            have hidx_lt : (rsn.setWidth 64 + 3 + (BitVec.ofNat 32 i).setWidth 64).toNat <
                arena1.length := by rw [hidx_l, har1_len]; omega
            fa_steps
            have htc_le_mv : tc' - s.core.tmp_cnt ≤ s.core.cur_vars := by
              rw [hcnt]; exact Nat.le_trans (List.length_filter_le _ _) (by simp)
            let st := rsnState s1 mrk' tmp' ws1' arena1 gu1 mcl' tc' tl' ant' res'
            have hst_len : st.LengthsOk c :=
              ⟨{ hlen1.core_ok with
                  mrk_len := hml_l
                  tmp_len_arr := htl_l
                  tmp_len_le := (by dsimp [st]; omega)
                  min_clr_len_le := hmcl_le },
               { hlen1.scratch_ok with work_stk1_len := hws_l }⟩
            let l_bv : BitVec 32 := arena1[rsn.toNat + 3 + i]'(by omega)
            have hl_eq : l_bv = s.core.arena[rsn.toNat + 3 + i]'(by omega) := by
              have h1 : arena1[rsn.toNat + 3 + i]? = some l_bv :=
                List.getElem?_eq_getElem (by omega)
              rw [har1_eq i hilt, List.getElem?_eq_getElem (by omega)] at h1
              exact (Option.some.inj h1).symm
            have hl_get : (s.core.arena[rsn.toNat + 3 + i]?.getD 0#32).toNat = l_bv.toNat := by
              rw [List.getElem?_eq_getElem (by omega), Option.getD_some, ← hl_eq]
            have hl_mem : l_bv.toNat ∈ fullArenaClauseLits s rsn.toNat :=
              (mem_fullArenaClauseLitsCore_iff (by omega)).mpr ⟨i, hilt, by rw [← hl_eq]⟩
            rw [getElem_eq_of_idx (hi := hidx_lt) (hj := by omega) hidx_l]
            refine wp_call_of_spec _ _ (hLit (c.hdr, l_bv, skip_var, ()) _ _ _
              ⟨c, st, R, rfl, hst_len, hcur32, htl_le, by dsimp [st]; omega, hwk', hml, ?_⟩)
            intro ok2 mrk2 tmp2 ws2 mcl2 tc2 tl2 ant2 res2 m2 _ hlen2 hwk2 htl2_le htl2_ge
              htl2_inc htc2_ge _ hmpres2 htpres2 hnewm2 hnewt2 hant2 hres2 htc2_eq hok2 hm2
            dsimp only [st, s1] at *
            have hpre2 := rsn_comb_step htl_ge htl2_ge htl2_inc htc_ge hl_mem hpre hmpres2 htpres2
              hnewm2 hnewt2 hres2 htc2_eq
            cases ok2 with
            | false =>
              wp_unfold; obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hpre2
              exact hQ false mrk2 tmp2 ws2 mcl2 tc2 tl2 arena1 gu1 ant2 res2 m2
                (same_core_fullWitnessCut hw1 hlen2.core_ok.mrk_len hlen2.core_ok.tmp_len_arr
                  hlen2.core_ok.min_clr_len_le htl2_le)
                hlen2 hwk2 (by omega) htl2_le (by omega) hrefs1 hcl1 h1 h2
                (fun w hw_lt hs0 hmnz => let ⟨l, hl, hr⟩ := h3 w hw_lt hs0 hmnz
                  ⟨l, (mem_fullRsnLits_large hne hlarge).mpr hl, hr⟩)
                (fun j hj1 hj2 => let ⟨ha, hr⟩ := h4 j hj1 hj2
                  ⟨(mem_fullRsnLits_large hne hlarge).mpr ha, hr⟩)
                h5 h6 h7 (fun hc => by cases hc) hm2
            | true =>
              wp_unfold; obtain ⟨hvlt, hrest⟩ := hok2 rfl
              have htake1 : (fullArenaClauseLits s rsn.toNat).take (i + 1) =
                  (fullArenaClauseLits s rsn.toNat).take i ++ [l_bv.toNat] := by
                have hlen_l : (fullArenaClauseLits s rsn.toNat).length = sz := by
                  simp [fullArenaClauseLits, fullArenaClauseLitsCore, sz,
                    fullArenaClauseSize]; omega
                rw [List.take_add_one, List.getElem?_eq_getElem (by omega), Option.toList_some]
                congr 2; unfold fullArenaClauseLits fullArenaClauseLitsCore
                simp [List.getElem_map, List.getElem_take, List.getElem_drop, ← hl_eq]
              have hant2_eq : ant2 = s.scratch.ant_sz + BitVec.ofNat 64
                  (((fullArenaClauseLits s rsn.toNat).take (i + 1)).countP antPred) := by
                rw [hant2, hant_l, htake1, List.countP_append, List.countP_cons, List.countP_nil,
                  Nat.zero_add, BitVec.add_assoc, BitVec.ofNat_add]
                exact congrArg (s.scratch.ant_sz + ·) (congrArg _
                  (bv64_ite_iff (by simp only [antPred, decide_eq_true_eq]; rfl)))
              rw [show BitVec.ofNat 32 i + 1 = BitVec.ofNat 32 (i + 1) from
                BitVec.eq_of_toNat_eq (by bv_omega)]
              refine ih (sz - (i + 1)) _ _ (by omega)
                ⟨i + 1, mrk2, tmp2, ws2, mcl2, tc2, tl2, ant2, res2, rfl, rfl,
                  ⟨by omega, hlen2.core_ok.mrk_len, hlen2.core_ok.tmp_len_arr,
                    hlen2.scratch_ok.work_stk1_len, hlen2.core_ok.min_clr_len_le,
                    by omega, htl2_le, by omega, hwk2, hpre2, ?_, hant2_eq, ?_⟩, hm2⟩
              · intro w hw_lt hs0 hmnz2 hltcl
                by_cases hm1_w : mrk'[w]?.getD 0#8 = 0#8
                · obtain ⟨rfl, hne', hpos, _⟩ := hnewm2 w hw_lt hm1_w hmnz2
                  obtain ⟨_, htget⟩ := ((hrest hne').2 hm1_w).2.2 hpos hltcl
                  exact ⟨tl', htl_ge, by omega, by rw [htget]; rfl⟩
                · obtain ⟨j, hj1, hj2, hjeq⟩ := hnewlow w hw_lt hs0 hm1_w hltcl
                  exact ⟨j, hj1, by omega, by rw [htpres2 j hj2]; exact hjeq⟩
              · intro k hk; by_cases hki : k = i
                · subst hki; dsimp only; rw [hl_get]; refine ⟨hvlt, fun hne' => ?_⟩
                  obtain ⟨hpos_m, hm1_r⟩ := hrest hne'; refine ⟨hpos_m, fun hs0 => ?_⟩
                  by_cases hm1_w : mrk'[l_bv.toNat / 2]?.getD 0#8 = 0#8
                  · obtain ⟨hle, _, hlow⟩ := hm1_r hm1_w
                    exact ⟨hle, fun hpos hltcl => let ⟨_, htget⟩ := hlow hpos hltcl
                      ⟨tl', htl_ge, by omega, by rw [htget]; rfl⟩⟩
                  · obtain ⟨_, _, _, _, _, hle⟩ := hnewm _ hvlt hs0 hm1_w
                    exact ⟨hle, fun _ hltcl =>
                      let ⟨j, hj1, hj2, hjeq⟩ := hnewlow _ hvlt hs0 hm1_w hltcl
                      ⟨j, hj1, by omega, by rw [htpres2 j hj2]; exact hjeq⟩⟩
                · obtain ⟨hkv, hkrest⟩ := hdone k (by omega)
                  refine ⟨hkv, fun hne' => ?_⟩; obtain ⟨h1, h2⟩ := hkrest hne'
                  refine ⟨fun hp => by rw [hmpres2 _ hkv (h1 hp)]; exact h1 hp, fun hs0 => ?_⟩
                  obtain ⟨hle, hlow⟩ := h2 hs0
                  exact ⟨hle, fun hpos hltcl => let ⟨j, hj1, hj2, hjeq⟩ := hlow hpos hltcl
                    ⟨j, hj1, by omega, by rw [htpres2 j hj2]; exact hjeq⟩⟩
          · fa_steps
            have hi32 : i < 2 ^ 32 := by omega
            have hieq : i = sz := by
              have hge_bv : ¬ i % 2 ^ 32 <
                  (s.core.arena[(rsn.toNat + (2#64).toNat) % 2 ^ 64]'(by omega)).toNat := ‹_›
              rw [Nat.mod_eq_of_lt hi32, hidx_eq, hsz_get] at hge_bv; omega
            refine hQ true mrk' tmp' ws1' mcl' tc' tl' arena1 gu1 ant' res' ml
              (same_core_fullWitnessCut hw1 hml_l htl_l hmcl_le htl_le (tc' := tc'))
              ⟨{ hlen1.core_ok with
                  mrk_len := hml_l
                  tmp_len_arr := htl_l
                  tmp_len_le := (by dsimp; omega)
                  min_clr_len_le := hmcl_le },
               { hlen1.scratch_ok with work_stk1_len := hws_l }⟩
              hwk' htl_ge htl_le htc_ge hrefs1 hcl1 hmpres htpres
              (fun w hw_lt hs0 hmnz => let ⟨l, hl, hr⟩ := hnewm w hw_lt hs0 hmnz
                ⟨l, (mem_fullRsnLits_large hne hlarge).mpr hl, hr⟩)
              (fun j hj1 hj2 => let ⟨h1, hr⟩ := hnewt j hj1 hj2
                ⟨(mem_fullRsnLits_large hne hlarge).mpr h1, hr⟩)
              hnd_t hcnt hres_l (fun _ => ?_) hml
            refine ⟨hne, ?_, fun hbad => absurd hlarge hbad, fun _ => ⟨by omega, hsz3, by
                change rsn.toNat + 3 + fullArenaClauseSizeCore s.core rsn.toNat ≤
                  s.core.arena_len; omega⟩, fun l hl => ?_⟩
            · have hlen_l : (fullArenaClauseLits s rsn.toNat).length = sz := by
                simp only [fullArenaClauseLits, fullArenaClauseLitsCore, sz, fullArenaClauseSize,
                  List.length_map, List.length_take, List.length_drop]; have := har_len; omega
              rw [hant_l, hieq, List.take_of_length_le (Nat.le_of_eq hlen_l)]
              simp [fullRsnLits, hne, hlarge, antPred]
            · rw [mem_fullRsnLits_large hne hlarge] at hl
              obtain ⟨k, hk, hget⟩ := (mem_fullArenaClauseLitsCore_iff (by omega)).mp hl
              have hkget : (s.core.arena[rsn.toNat + 3 + k]?.getD 0#32).toNat = l := by
                rw [List.getElem?_eq_getElem (by omega), Option.getD_some, hget]
              have hd := hdone k (by rw [hieq]; exact hk); rwa [hkget] at hd
        · intro L hL; fa_steps
          refine hL sz _ m1 ⟨0, s.core.mrk, s.core.tmp, s.scratch.work_stk1, s.core.min_clr_len,
            s.core.tmp_cnt, s.core.tmp_len, s.scratch.ant_sz, s.scratch.res_sz, by omega, rfl,
            ⟨Nat.zero_le _, hlen1.core_ok.mrk_len, hlen1.core_ok.tmp_len_arr,
              hlen1.scratch_ok.work_stk1_len, hlen1.core_ok.min_clr_len_le, Nat.le_refl _,
              htl_cv, Nat.le_refl _, hwork, ⟨fun _ _ _ => rfl, fun _ _ => rfl,
                fun _ _ h0 hnz => absurd h0 hnz, fun _ h1 h2 => by omega,
                fun _ _ _ h1 h2 => by omega,
                by rw [Nat.sub_self, filter_length_eq_zero_of_false]; intro _ _; simp,
                by rw [filter_length_eq_zero_of_false (fun _ _ => by simp)]; simp⟩,
              fun _ _ h0 hnz _ => absurd h0 hnz, by simp, fun _ hk => by omega⟩, hm1⟩
      · intro Jred hJred
        clear hLit hQ htl_cv htc_fit hwork hrsn_ref hsz_get hret_false_same skip_var
        c0_let_simp; c0_step
        · c0_step
          refine wp_join_group (ts := [i64])
            (fun (gi, ()) m_gi => gi.toNat < 64 ∧ (FullMem c s ⋆ R) m_gi) ?_ ?_
          · rintro _ ⟨gi, ⟨⟩⟩ m_gi ⟨hgi_lt, hm_gi⟩; clear hm; c0_let_simp
            refine wp_join_group (ts := []) (fun () m_gu => ∃ gu1, gu1.length = 64 ∧
              (FullMem c ⟨s.core, { s.scratch with glue_used := gu1 }⟩ ⋆ R) m_gu) ?_ ?_
            · rintro _ ⟨⟩ m_gu ⟨gu1, hgu1, hm_gu⟩; clear hm_gi
              let s_gu : FullState := ⟨s.core, { s.scratch with glue_used := gu1 }⟩
              change (FullMem c s_gu ⋆ R) m_gu at hm_gu; c0_let_simp
              refine wp_join_group (ts := [i32])
                (fun (new_u, ()) m_nu => (FullMem c s_gu ⋆ R) m_nu) ?_ ?_
              · rintro _ ⟨new_u, ⟨⟩⟩ m_nu hm_nu; clear hm_gu; dsimp only [s_gu] at hm_nu
                fa_steps
                · obtain ⟨hw', hr', hcl'⟩ :=
                    arenaBumpUsage_preserves_fullWitnessCut hlen.core_ok hw href new_u
                  have har_u_eq : s.core.arena.set (rsn.setWidth 64).toNat
                      ((s.core.arena[rsn.toNat]'(by omega) &&& 134217727#32) |||
                        (new_u <<< (27 : BitVec 32))) =
                      s.core.arena.set rsn.toNat ((fullArenaHdrCore s.core rsn.toNat &&&
                        0x07FFFFFF#32) ||| (new_u <<< 27)) := by
                    rw [bv_c0_zext32_64, hhdr_get]; rfl
                  let arena_u := s.core.arena.set rsn.toNat
                    ((fullArenaHdrCore s.core rsn.toNat &&& 0x07FFFFFF#32) ||| (new_u <<< 27))
                  exact hJred () _ ⟨arena_u, gu1, hw',
                    ⟨{ hlen.core_ok with arena_len_arr := by simp [arena_u, har_len] },
                     { hlen.scratch_ok with glue_used_len := hgu1 }⟩,
                    hr', hcl', fun k _ => List.getElem?_set_ne (by omega),
                    fullMem_arena_eq har_u_eq hm⟩
                · exact hJred () _ ⟨s.core.arena, gu1, hw,
                    ⟨hlen.core_ok, { hlen.scratch_ok with glue_used_len := hgu1 }⟩,
                    rfl, fun _ _ => ⟨rfl, rfl, rfl⟩, fun _ _ => rfl, hm_nu⟩
              · intro Jnu hJnu; fa_steps <;> exact hJnu _ _ hm_gu
            · intro Jgu hJgu; fa_steps
              · exact hJgu () _ ⟨s.scratch.glue_used.set gi.toNat
                  (s.scratch.glue_used[gi.toNat]'(by omega) + 1), by simp [hgu_len], hm⟩
              · exact hJgu () _ ⟨s.scratch.glue_used, hgu_len, hm_gi⟩
          · intro Jgi hJgi; fa_steps
            · exact hJgi _ _ ⟨by decide, hm⟩
            · refine hJgi _ _ ⟨?_, hm⟩; simp only [bv_c0, BitVec.reduceToNat] at *; omega
        · fa_steps
          exact hJred () _ ⟨s.core.arena, s.scratch.glue_used, hw, hlen, rfl,
            fun _ _ => ⟨rfl, rfl, rfl⟩, fun _ _ => rfl, hm⟩

/-! ## 5. Strictly scoped O(1)-per-step executor (`FullAnalyzeTactics`) -/

namespace FullAnalyzeTactics

theorem strip_wp {Γ rs Q X e m} (h : wp (rs := rs) Γ Q X e m) : wp Γ Q X e m := h
theorem strip_fwp {as rs Γ f args m Q X}
    (h : Func.wp (as := as) (rs := rs) Γ f args m Q X) : Func.wp Γ f args m Q X := h
theorem strip_le_wp {a b : Nat} {P : Prop} (h : a ≤ b) (hp : P) : a ≤ b ∧ P := ⟨h, hp⟩
attribute [scoped bv_c0] Bool.false_eq_true

section FaFastWp
variable {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
local notation "K " t => Tup Val [t] → Expr Val Cont rs
theorem fa_wp_copy {t} {a : Arg Val t} {k : K t} (h : wp Γ Q X (k (a.val, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.copy t) (a, ())) k) m := by simpa only [wp_let_copy_eq] using h
theorem fa_wp_add {n} {a b : Arg Val (.bits n)} {k : K (.bits n)}
    (h : wp Γ Q X (k (a.val + b.val, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.add _) (a, b, ())) k) m := by
  simpa only [wp_let_add_eq, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2] using h
theorem fa_wp_sub {n} {a b : Arg Val (.bits n)} {k : K (.bits n)}
    (h : wp Γ Q X (k (a.val - b.val, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.sub _) (a, b, ())) k) m := by
  simpa only [wp_let_sub_eq, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2] using h
theorem fa_wp_mul {n} {a b : Arg Val (.bits n)} {k : K (.bits n)}
    (h : wp Γ Q X (k (a.val * b.val, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.mul _) (a, b, ())) k) m := by
  simpa only [wp_let_mul_eq, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2] using h
theorem fa_wp_and {n} {a b : Arg Val (.bits n)} {k : K (.bits n)}
    (h : wp Γ Q X (k (a.val &&& b.val, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.and _) (a, b, ())) k) m := by simpa only [wp_let_and_eq, lift2] using h
theorem fa_wp_or {n} {a b : Arg Val (.bits n)} {k : K (.bits n)}
    (h : wp Γ Q X (k (a.val ||| b.val, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.or _) (a, b, ())) k) m := by simpa only [wp_let_or_eq, lift2] using h
theorem fa_wp_xor {n} {a b : Arg Val (.bits n)} {k : K (.bits n)}
    (h : wp Γ Q X (k (a.val ^^^ b.val, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.xor _) (a, b, ())) k) m := by simpa only [wp_let_xor_eq, lift2] using h
theorem fa_wp_lshr1_32 {a : Arg Val (.bits 32)} {k : K (.bits 32)}
    (h : wp Γ Q X (k (a.val >>> 1, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.lshr _) (a, Arg.imm 1#32, ())) k) m := by
  simpa only [wp_let_lshr_eq, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2, Arg.val_imm,
    BitVec.reduceToNat, Nat.reduceMod] using h
theorem fa_wp_zext32_64 {a : Arg Val (.bits 32)} {k : K (.bits 64)}
    (h : wp Γ Q X (k (a.val.setWidth 64, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.zext 32 64) (a, ())) k) m := by
  rw [wp_let_zext_eq]; exact ⟨by decide, h⟩
theorem fa_wp_zext8_32 {a : Arg Val (.bits 8)} {k : K (.bits 32)}
    (h : wp Γ Q X (k (a.val.setWidth 32, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.zext 8 32) (a, ())) k) m := by
  rw [wp_let_zext_eq]; exact ⟨by decide, h⟩
theorem fa_wp_sext32_64_0 {k : K (.bits 64)} (h : wp Γ Q X (k (0#64, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.sext 32 64) (Arg.imm 0#32, ())) k) m := by
  simpa only [wp_let_sext_eq] using ⟨by decide, h⟩
theorem fa_wp_sext32_64_1 {k : K (.bits 64)} (h : wp Γ Q X (k (1#64, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.sext 32 64) (Arg.imm 1#32, ())) k) m := by
  simpa only [wp_let_sext_eq] using ⟨by decide, h⟩
theorem fa_wp_sext8_32 {a : Arg Val (.bits 8)} {k : K (.bits 32)}
    (h : wp Γ Q X (k (a.val.signExtend 32, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.sext 8 32) (a, ())) k) m := by
  simpa only [wp_let_sext_eq] using ⟨by decide, h⟩
theorem fa_wp_trunc64_32 {a : Arg Val (.bits 64)} {k : K (.bits 32)}
    (h : wp Γ Q X (k (a.val.setWidth 32, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.trunc 64 32) (a, ())) k) m := by
  simpa only [wp_let_trunc_eq] using ⟨by decide, h⟩
theorem fa_wp_cmp {o n} {a b : Arg Val (.bits n)} {k : K .bool}
    (h : wp Γ Q X (k (o.evalBits a.val b.val, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.cmp o (.bits n) .bool rfl) (a, b, ())) k) m := by
  simpa only [wp_let_cmp_eq, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, cast_eq, liftCmp] using h
theorem fa_wp_cmp_eq {n} {a b : Arg Val (.bits n)} {k : K .bool}
    (h : wp Γ Q X (k ((a.val == b.val), ())) m) :
    wp Γ Q X (.let_ (Op.mk (.cmp .eq (.bits n) .bool rfl) (a, b, ())) k) m :=
  fa_wp_cmp (evalBits_eq_beq a.val b.val ▸ h)
theorem fa_wp_cmp_ne {n} {a b : Arg Val (.bits n)} {k : K .bool}
    (h : wp Γ Q X (k ((a.val != b.val), ())) m) :
    wp Γ Q X (.let_ (Op.mk (.cmp .ne (.bits n) .bool rfl) (a, b, ())) k) m :=
  fa_wp_cmp (evalBits_ne_bne a.val b.val ▸ h)
theorem fa_wp_cmp_ult {n} {a b : Arg Val (.bits n)} {k : K .bool}
    (h : wp Γ Q X (k (a.val.ult b.val, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.cmp .ult (.bits n) .bool rfl) (a, b, ())) k) m :=
  fa_wp_cmp (evalBits_ult_eq a.val b.val ▸ h)
theorem fa_wp_cmp_ule {n} {a b : Arg Val (.bits n)} {k : K .bool}
    (h : wp Γ Q X (k (a.val.ule b.val, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.cmp .ule (.bits n) .bool rfl) (a, b, ())) k) m :=
  fa_wp_cmp (evalBits_ule_eq a.val b.val ▸ h)
theorem fa_wp_cmp_ugt {n} {a b : Arg Val (.bits n)} {k : K .bool}
    (h : wp Γ Q X (k (b.val.ult a.val, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.cmp .ugt (.bits n) .bool rfl) (a, b, ())) k) m :=
  fa_wp_cmp (evalBits_ugt_eq a.val b.val ▸ h)
theorem fa_wp_cmp_uge {n} {a b : Arg Val (.bits n)} {k : K .bool}
    (h : wp Γ Q X (k (b.val.ule a.val, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.cmp .uge (.bits n) .bool rfl) (a, b, ())) k) m :=
  fa_wp_cmp (evalBits_uge_eq a.val b.val ▸ h)
theorem fa_wp_jump0 {L : Cont []} (h : L () m) : wp (rs := rs) Γ Q X (.jump L ()) m := h
theorem fa_wp_jump1 {t} {L : Cont [t]} {a : Arg Val t} (h : L (a.val, ()) m) :
    wp (rs := rs) Γ Q X (.jump L (a, ())) m := h
theorem fa_wp_jump2 {t1 t2} {L : Cont [t1, t2]} {a : Arg Val t1} {b : Arg Val t2}
    (h : L (a.val, b.val, ()) m) : wp (rs := rs) Γ Q X (.jump L (a, b, ())) m := h
theorem fa_wp_jump3 {t1 t2 t3} {L : Cont [t1, t2, t3]} {a : Arg Val t1} {b : Arg Val t2}
    {c : Arg Val t3} (h : L (a.val, b.val, c.val, ()) m) :
    wp (rs := rs) Γ Q X (.jump L (a, b, c, ())) m := h
end FaFastWp
theorem fa_wp_ret0 {Γ X m} {Q : Post []} (h : Q () m) : wp Γ Q X (.ret ()) m := h
theorem fa_wp_ret1 {Γ X m t} {Q : Post [t]} {a : Arg Val t} (h : Q (a.val, ()) m) :
    wp Γ Q X (.ret (a, ())) m := h

meta def faUnwrapCtor (ctorName : Lean.Name) : Lean.Expr → Option (Array Lean.Expr)
  | .mdata _ b => faUnwrapCtor ctorName b
  | .letE _ _ _ b _ => faUnwrapCtor ctorName b
  | e => if e.getAppFn.isConstOf ctorName then some e.getAppArgs else none

meta def faReduceProjOnce (env : Lean.Environment) (e : Lean.Expr) : Lean.Expr :=
  e.replace fun sub =>
    match sub with
    | .proj ``Prod 0 arg => if arg.isAppOfArity ``Prod.mk 4 then some (arg.getArg! 2) else none
    | .proj ``Prod 1 arg => if arg.isAppOfArity ``Prod.mk 4 then some (arg.getArg! 3) else none
    | .proj sName idx arg =>
      match Lean.getStructureInfo? env sName, env.find? sName with
      | some sInfo, some (.inductInfo ind) =>
        match ind.ctors.head? >>= (faUnwrapCtor · arg) with
        | some args =>
          let k := ind.numParams + idx
          if h : k < args.size then
            let r := args[k]
            if !r.hasLooseBVars && sInfo.fieldNames.size > idx then some r else none
          else none
        | none => none
      | _, _ => none
    | _ =>
      if sub.isAppOfArity ``Prod.fst 3 && sub.appArg!.isAppOfArity ``Prod.mk 4 then
        some (sub.appArg!.getArg! 2)
      else if sub.isAppOfArity ``Prod.snd 3 && sub.appArg!.isAppOfArity ``Prod.mk 4 then
        some (sub.appArg!.getArg! 3)
      else if sub.isAppOf ``Arg.val && sub.getAppNumArgs ≥ 1 then
        let arg := sub.appArg!
        if (arg.isAppOf ``Arg.var || arg.isAppOf ``Arg.imm) && arg.getAppNumArgs ≥ 1 then
          some arg.appArg!
        else none
      else if let some fn := sub.getAppFn.constName? then
        match env.getProjectionFnInfo? fn with
        | some info =>
          if sub.getAppNumArgs == info.numParams + 1 then
            match faUnwrapCtor info.ctorName sub.appArg! with
            | some args =>
              let k := info.numParams + info.i
              if h : k < args.size then
                let r := args[k]; if !r.hasLooseBVars then some r else none
              else none
            | none => none
          else none
        | none => none
      else none

meta def faReduceHeadE (env : Lean.Environment) (e : Lean.Expr) : Lean.Expr :=
  let r := faReduceProjOnce env
  r (r (r (r e.headBeta)))
meta def faNormWpGoal (g : Lean.MVarId) : Lean.Elab.Tactic.TacticM Lean.MVarId := do
  let ty := (← Lean.instantiateMVars (← g.getType)).headBeta
  if ty.isAppOf ``wp && ty.getAppNumArgs == 6 then
    let env ← Lean.getEnv
    let e := ty.getArg! 4; let e' := faReduceHeadE env e
    if e' != e then return ← g.change (Lean.mkAppN ty.getAppFn (ty.getAppArgs.set! 4 e'))
  return g
meta def faBvLit (w v : Nat) : Lean.Expr :=
  Lean.mkApp2 (Lean.mkConst ``BitVec.ofNat) (Lean.mkNatLit w) (Lean.mkNatLit v)
meta def faFastLetLemma? (op : Lean.Expr) : Option Lean.Name :=
  if op.isAppOf ``Op.mk && op.getAppNumArgs == 5 then
    let code := op.getArg! 3; let args := op.getArg! 4
    let hasImm1 := args.isAppOfArity ``Prod.mk 4 && (args.getArg! 2).isAppOf ``Arg.imm
    let hasImm2 := hasImm1 && (args.getArg! 3).isAppOfArity ``Prod.mk 4 &&
      ((args.getArg! 3).getArg! 2).isAppOf ``Arg.imm
    match code.getAppFn.constName? with
    | some ``OpCode.copy => some ``fa_wp_copy
    | some ``OpCode.add => if hasImm2 then none else some ``fa_wp_add
    | some ``OpCode.sub => if hasImm2 then none else some ``fa_wp_sub
    | some ``OpCode.mul => if hasImm2 then none else some ``fa_wp_mul
    | some ``OpCode.and => some ``fa_wp_and
    | some ``OpCode.or => some ``fa_wp_or
    | some ``OpCode.xor => some ``fa_wp_xor
    | some ``OpCode.lshr => some ``fa_wp_lshr1_32
    | some ``OpCode.zext =>
      if hasImm1 || code.getAppNumArgs != 2 then none
      else if (code.getArg! 0).nat? == some 32 && (code.getArg! 1).nat? == some 64 then
        some ``fa_wp_zext32_64
      else if (code.getArg! 0).nat? == some 8 && (code.getArg! 1).nat? == some 32 then
        some ``fa_wp_zext8_32
      else none
    | some ``OpCode.sext =>
      if code.getAppNumArgs != 2 then none
      else if (code.getArg! 0).nat? == some 32 && (code.getArg! 1).nat? == some 64 && hasImm1 then
        let a := (args.getArg! 2).appArg!
        if a == faBvLit 32 0 then some ``fa_wp_sext32_64_0
        else if a == faBvLit 32 1 then some ``fa_wp_sext32_64_1 else none
      else if !hasImm1 && (code.getArg! 0).nat? == some 8 && (code.getArg! 1).nat? == some 32 then
        some ``fa_wp_sext8_32
      else none
    | some ``OpCode.trunc =>
      if !hasImm1 && code.getAppNumArgs == 2 && (code.getArg! 0).nat? == some 64 &&
          (code.getArg! 1).nat? == some 32 then some ``fa_wp_trunc64_32 else none
    | some ``OpCode.cmp =>
      if code.getAppNumArgs == 4 then
        match (code.getArg! 0).getAppFn.constName? with
        | some ``CmpOp.eq => some ``fa_wp_cmp_eq | some ``CmpOp.ne => some ``fa_wp_cmp_ne
        | some ``CmpOp.ult => some ``fa_wp_cmp_ult | some ``CmpOp.ule => some ``fa_wp_cmp_ule
        | some ``CmpOp.ugt => some ``fa_wp_cmp_ugt | some ``CmpOp.uge => some ``fa_wp_cmp_uge
        | _ => none
      else none
    | _ => none
  else none

meta def faClearStale (m0 : Lean.Expr) : Lean.Elab.Tactic.TacticM Unit :=
  Lean.Elab.Tactic.withMainContext do
    let .fvar mId := m0 | return
    for d in (← Lean.getLCtx).decls.toArray.reverse do
      let some d := d | continue
      let t ← Lean.instantiateMVars d.type
      if t.isAppOf ``Std.ExtHashMap.sep && t.appArg! == m0 then
        try Lean.Elab.Tactic.liftMetaTactic1 fun g => some <$> g.clear d.fvarId catch _ => pure ()
    try Lean.Elab.Tactic.liftMetaTactic1 fun g => some <$> g.clear mId catch _ => pure ()
meta def faFindJoinHyp (J : Lean.FVarId) :
    Lean.Elab.Tactic.TacticM (Option Lean.Expr) :=
  Lean.Elab.Tactic.withMainContext do
    for d in (← Lean.getLCtx).decls.toArray.reverse do
      let some d := d | continue
      let ok ← Lean.Meta.forallTelescopeReducing d.type fun xs concl => do
        if xs.size < 1 then return false
        return concl.getAppFn.isFVarOf J && (← Lean.Meta.inferType xs[xs.size - 1]!).isAppOf ``wp
      if ok then return some d.toExpr
    return none
meta def faStepOnce (unrollGroup : Bool := true) : Lean.Elab.Tactic.TacticM Bool :=
  Lean.Elab.Tactic.withMainContext do
    let g ← Lean.Elab.Tactic.getMainGoal
    let ty := (← Lean.instantiateMVars (← g.getType)).consumeMData.headBeta
    if ty.isAppOf ``Func.wp && ty.getAppNumArgs ≥ 4 then
      let f := ty.getArg! 3
      if let some fn := f.getAppFn.constName? then
        Lean.Elab.Tactic.evalTactic (← `(tactic| unfold Func.wp $(Lean.mkIdent fn):ident))
        let [g'] ← Lean.Elab.Tactic.getUnsolvedGoals | return true
        Lean.Elab.Tactic.setGoals [← faNormWpGoal g']; return true
      return false
    if ty.isAppOf ``And then
      let s ← Lean.Elab.Tactic.saveState
      try Lean.Elab.Tactic.evalTactic (← `(tactic| refine strip_le_wp (by decide) ?_)); return true
      catch _ => s.restore; return false
    if ty.isAppOf ``wp && ty.getAppNumArgs == 6 then
      let e := (ty.getArg! 4).consumeMData.headBeta
      match e.getAppFn.constName? with
      | some ``Expr.let_ =>
        if e.getAppNumArgs != 6 then return false
        if let some lem := faFastLetLemma? (e.getArg! 4).headBeta then
          let s ← Lean.Elab.Tactic.saveState
          try
            let [hk] ← g.apply (← Lean.Meta.mkConstWithFreshMVarLevels lem)
              | s.restore; return false
            Lean.Elab.Tactic.setGoals [← faNormWpGoal hk]; return true
          catch _ => s.restore
        let s ← Lean.Elab.Tactic.saveState
        try Lean.Elab.Tactic.evalTactic (← `(tactic| c0_let_simp)); return true
        catch _ => s.restore; return false
      | some ``Expr.load =>
        let s ← Lean.Elab.Tactic.saveState
        try
          let [hl, hk] := (← g.apply (← Lean.Meta.mkConstWithFreshMVarLevels ``wp_load_of)).take 2
            | s.restore; return false
          LeanQbe.T.C0Step.memSolve true hl
          Lean.Elab.Tactic.setGoals [← faNormWpGoal hk]; return true
        catch _ => s.restore; return false
      | some ``Expr.store =>
        let s ← Lean.Elab.Tactic.saveState
        try
          let m0 := ty.getArg! 5
          let [hs, hk] := (← g.apply (← Lean.Meta.mkConstWithFreshMVarLevels ``wp_store_sep)).take 2
            | s.restore; return false
          LeanQbe.T.C0Step.memSolve false hs; Lean.Elab.Tactic.setGoals [hk]
          let mId := Lean.mkIdent `m; let hmId := Lean.mkIdent `hm
          Lean.Elab.Tactic.evalTactic (← `(tactic| intro $mId:ident $hmId:ident;
            try simp only [Arg.val_var, Arg.val_imm, Std.ExtHashMap.sep_emp] at $hmId:ident))
          faClearStale m0; return true
        catch _ => s.restore; return false
      | some ``Expr.jnz =>
        let hc := Lean.mkIdent `hc
        Lean.Elab.Tactic.evalTactic (← `(tactic|
          (refine wp_jnz_of (fun $hc:ident => ?_) (fun $hc:ident => ?_)) <;> (
            try simp only [Arg.val_var, Arg.val_imm] at $hc:ident; c0_cond $hc
            try (first | exact ($hc).elim | exact absurd rfl $hc | exact $hc rfl
                       | exact absurd trivial $hc))))
        return true
      | some ``Expr.jump | some ``Expr.ret =>
        let lems := if e.isAppOf ``Expr.ret then #[``fa_wp_ret0, ``fa_wp_ret1]
          else #[``fa_wp_jump0, ``fa_wp_jump1, ``fa_wp_jump2, ``fa_wp_jump3]
        for lem in lems do
          let s2 ← Lean.Elab.Tactic.saveState
          try
            let [hk] ← g.apply (← Lean.Meta.mkConstWithFreshMVarLevels lem) | s2.restore; continue
            let hkTy ← Lean.instantiateMVars (← hk.getType)
            let env ← Lean.getEnv
            let hkTy' := faReduceProjOnce env (faReduceProjOnce env hkTy)
            Lean.Elab.Tactic.setGoals [← if hkTy' != hkTy then hk.change hkTy' else pure hk]
            return true
          catch _ => s2.restore
        return false
      | some ``Expr.group =>
        if unrollGroup && e.getAppNumArgs == 6 then
          if let .lam _ _ b _ := e.getArg! 4 then
            if !b.hasLooseBVars then
              let J := Lean.mkIdent `J; let hJ := Lean.mkIdent `hJ
              Lean.Elab.Tactic.evalTactic (← `(tactic|
                refine wp_unroll_group fun $J:ident $hJ:ident => ?_))
              return true
        return false
      | some ``Blocks.get =>
        if e.getAppNumArgs == 8 then
          let bs := (e.getArg! 5).headBeta
          if bs.isAppOf ``Blocks.cons && bs.getAppNumArgs == 7 &&
              (e.getArg! 6).isAppOf ``Member.here then
            let env ← Lean.getEnv
            let newE := faReduceHeadE env (Lean.mkApp (bs.getArg! 5) (e.getArg! 7))
            let newTy := Lean.mkAppN ty.getAppFn (ty.getAppArgs.set! 4 newE)
            Lean.Elab.Tactic.setGoals [← g.change newTy]; return true
        return false
      | _ => return false
    if let .fvar J := ty.getAppFn then
      if let some h ← faFindJoinHyp J then
        Lean.Elab.Tactic.setGoals (← (← g.apply h).mapM faNormWpGoal); return true
    return false

meta partial def faStepsLoop (unrollGroup : Bool) (fuel : Nat) :
    Lean.Elab.Tactic.TacticM Unit := do
  if fuel = 0 then return
  let mut out : Array Lean.MVarId := #[]
  for g in (← Lean.Elab.Tactic.getUnsolvedGoals) do
    if ← g.isAssigned then continue
    Lean.Elab.Tactic.setGoals [g]
    if ← faStepOnce unrollGroup then faStepsLoop unrollGroup (fuel - 1)
    out := out ++ (← Lean.Elab.Tactic.getUnsolvedGoals)
  Lean.Elab.Tactic.setGoals out.toList

scoped elab "fa_fast_steps" : tactic => do
  Lean.Elab.Tactic.evalTactic (← `(tactic| try (first | refine strip_fwp ?_ | refine strip_wp ?_)))
  faStepsLoop true 2000

scoped elab "fa_fast_steps_nogrp" : tactic => do
  Lean.Elab.Tactic.evalTactic (← `(tactic| try (first | refine strip_fwp ?_ | refine strip_wp ?_)))
  faStepsLoop false 2000

scoped elab "fa_steps_n " n:num : tactic => do
  Lean.Elab.Tactic.evalTactic (← `(tactic| try (first | refine strip_fwp ?_ | refine strip_wp ?_)))
  faStepsLoop false n.getNat

end FullAnalyzeTactics

end LeanQbe.T.Examples.Kissat.Full
