/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Src.Forward
public import LeanQbe.T.Examples.Kissat.Proof.Forward.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Forward.Lemmas
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation
meta import LeanQbe.T.Logic.C0Step
meta import LeanQbe.T.Logic.C0HeadStep

/-!
# Forward WP Proofs Part 0 (`Proof.Forward.Wp0`)

Canonical `Env.Has` `Func.wp` proofs for:
1. `full_fwd_dedup_bins_wp` (`fullFwdDedupBinsSpec`)
2. `full_fwd_flush_large_m7_wp` (`fullFwdFlushLargeM7Spec`, sparse + dense)

Zero legacy imports (`Full*`, `PatchModule`, `Solver`), `0` `@[expose]` on theorems/lemmas,
every file `<= 1,500`L, every decl `<= 450`L, every line `<= 100` cols.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Forward

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Forward
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Forward.Spec
open Kraken.Bedrock2.Test

open scoped FullArenaTactics

local macro "fwd_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

/-! ## 1. `full_fwd_dedup_bins_wp` Helpers & Proof -/

section DedupBins

private theorem dedup_slice_step {F_cur : List (List Nat)} {k : FullCoreState} {lit p rem : Nat}
    (h : DenseWatchSliceOk F_cur k lit p rem) (hpos : 0 < rem) :
    (∃ r1 w0, rem = r1 + 1 ∧ k.wstk[p]? = some w0 ∧ (w0 &&& 0x80000000#32) ≠ 0#32 ∧
      w0 ≠ 0xFFFFFFFF#32 ∧ (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k.cur_vars ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause [lit, (w0 &&& 0x7FFFFFFF#32).toNat]) ∧
      DenseWatchSliceOk F_cur k lit (p + 1) r1) ∨
    (∃ r2 w0 cr, rem = r2 + 2 ∧ k.wstk[p]? = some w0 ∧ k.wstk[p + 1]? = some cr ∧
      (w0 &&& 0x80000000#32) = 0#32 ∧ 3 ≤ w0.toNat ∧ cr.toNat < 0x80000000 ∧
      cr.toNat ∈ fullArenaClauseRefsCore k ∧
      DenseWatchSliceOk F_cur k lit (p + 2) r2) := by
  cases h with
  | empty => omega
  | @bin _ r1 w0 hw hf hn hl he hr => exact Or.inl ⟨r1, w0, rfl, hw, hf, hn, hl, he, hr⟩
  | @occ _ r2 w0 cr hw hw1 hf hs hl hr hrest =>
    exact Or.inr ⟨r2, w0, cr, rfl, hw, hw1, hf, hs, hl, hr, hrest⟩

private theorem dedup_slice_bin_word_props {F_cur : List (List Nat)} {k : FullCoreState}
    {lit p rem : Nat} (h : DenseWatchSliceOk F_cur k lit p rem) :
    ∀ idx, p ≤ idx → idx < p + rem →
      (k.wstk[idx]?.getD 0#32 &&& 0x80000000#32) ≠ 0#32 →
      (k.wstk[idx]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat < 2 * k.cur_vars ∧
      (cnfOfClauses F_cur).EntailsClause
        (cnfClause [lit, (k.wstk[idx]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat]) := by
  induction h with
  | empty => intro _ hi1 hi2; omega
  | @bin p rem w0 hp _ _ hlt hent _ ih =>
    intro idx hi1 hi2 hbin
    by_cases hpe : idx = p
    · subst hpe; rw [hp, Option.getD_some]; exact ⟨hlt, hent⟩
    · exact ih idx (by omega) (by omega) hbin
  | @occ p rem w0 _ hp hp1 hflag _ _ _ _ ih =>
    intro idx hi1 hi2 hbin
    by_cases hpe : idx = p
    · subst hpe; rw [hp, Option.getD_some] at hbin; exact absurd hflag hbin
    · by_cases hp1e : idx = p + 1
      · subst hp1e; rw [hp1, Option.getD_some] at hbin
        exfalso; have := (FullBvaFwdTactics.bv32_and_bin_ne_zero_iff _).mp hbin; omega
      · exact ih idx (by omega) (by omega) hbin

private theorem dedup_denseInvW_of_shrink {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (h : FullDenseInvW c F0 F_cur s)
    {l nsz : Nat} (hl : l < 2 * s.core.cur_vars) (hnsz : nsz ≤ fullWatchSizeCore s.core l)
    {wstk' : List (BitVec 32)} {wu' nb' : BitVec 64} (hwl : wstk'.length = c.wcap)
    (hout : ∀ idx, idx < fullWatchOffCore s.core l ∨
      fullWatchOffCore s.core l + fullWatchSizeCore s.core l ≤ idx →
      wstk'[idx]? = s.core.wstk[idx]?)
    (hpref : DenseWatchSliceOk F_cur { s.core with wstk := wstk', num_binary := nb' } l
      (fullWatchOffCore s.core l) nsz) :
    let wvec' := s.core.wvec.set (2 * l + 1) (BitVec.ofNat 32 nsz)
    FullDenseInvW c F0 F_cur
      { s with core :=
        { s.core with wvec := wvec', wstk := wstk', wusable := wu', num_binary := nb' } } := by
  intro wvec'
  let s1 : FullState := { s with core := { s.core with num_binary := nb' } }
  have h1 : FullDenseInvW c F0 F_cur s1 :=
    ⟨⟨{ h.1.core_ok with wvec_len := h.1.core_ok.wvec_len }, h.1.scratch_ok⟩,
     { h.2.1 with
       arena := { h.2.1.arena with len_ok := h.2.1.arena.len_ok }
       watches := h.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) },
     h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩
  have hpre' : ModeWatchSliceOk F_cur { s1.core with wstk := wstk' } l
      (fullWatchOffCore s1.core l) nsz := by
    dsimp only [ModeWatchSliceOk, s1]
    rw [ite_eq_right h.2.2.2.2.2.2]
    exact hpref
  have ⟨hlen', hw'⟩ :=
    fwd_witnessInv_of_shrink_watch h1.1 h1.2.1 hl hnsz (wu' := wu') hwl hout hpre'
  exact ⟨hlen', hw', h1.2.2.1, h1.2.2.2.1, h1.2.2.2.2.1, h1.2.2.2.2.2.1, h1.2.2.2.2.2.2⟩

private def DedupLoop1Inv (c : FullCfg) (F_cur : List (List Nat)) (st : FullState)
    (l off sz p q : Nat) (ul : Bool) (st1 : FullState) : Prop :=
  ∃ wstk1 lm1 nb1,
    st1 = { st with core := { st.core with wstk := wstk1, lit_mark := lm1, num_binary := nb1 } } ∧
    wstk1.length = c.wcap ∧ lm1.length = 2 * c.max_vars ∧
    off ≤ q ∧ q ≤ p ∧ p ≤ off + sz ∧
    (∀ idx, idx < off ∨ off + sz ≤ idx → wstk1[idx]? = st.core.wstk[idx]?) ∧
    (∀ idx, p ≤ idx → idx < off + sz → wstk1[idx]? = st.core.wstk[idx]?) ∧
    DenseWatchSliceOk F_cur st1.core l off (q - off) ∧
    DenseWatchSliceOk F_cur st1.core l p (off + sz - p) ∧
    (∀ x < 2 * c.max_vars, lm1[x]?.getD 0#8 ≠ 0#8 →
      ∃ idx, off ≤ idx ∧ idx < q ∧
        (wstk1[idx]?.getD 0#32 &&& 0x80000000#32) ≠ 0#32 ∧
        (wstk1[idx]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat = x) ∧
    (ul = true → (cnfOfClauses F_cur).EntailsClause (cnfClause [l]))

private theorem dedup_step_occ_ok {c : FullCfg} {F_cur : List (List Nat)} {st st1 : FullState}
    {l off sz p q : Nat} {ul : Bool}
    (h : DedupLoop1Inv c F_cur st l off sz p q ul st1)
    (hp_lt : p < off + sz) (hp_ws : p < st1.core.wstk.length)
    (hflag : (st1.core.wstk[p]'hp_ws &&& 0x80000000#32) = 0#32) :
    p + 1 < off + sz ∧
    ∀ (hp1_ws : p + 1 < st1.core.wstk.length),
      let w0 := st1.core.wstk[p]'hp_ws
      let wstk' := st1.core.wstk.set q w0
      let w1 := wstk'[p + 1]'(by simp [wstk', hp1_ws])
      DedupLoop1Inv c F_cur st l off sz (p + 2) (q + 2) ul
        { st1 with core := { st1.core with wstk := wstk'.set (q + 1) w1 } } := by
  obtain ⟨wstk1, lm1, nb1, rfl, hws, hlm, hq_ge, hq_le, hp_le, hout, hrem_eq,
    hpref, hrem, hlmi, hul⟩ := h
  rcases dedup_slice_step hrem (by omega) with
    ⟨_, w0, _, hw0_some, hbin_ne, _, _, _, _⟩ |
    ⟨r2, w0, cr, h2eq, hw0_some, hcr_some, hbin_eq, hw0_sz3, hcr_lt, hcr_mem, hrem_next⟩
  · have hw0_val : wstk1[p]'hp_ws = w0 := by
      rw [List.getElem?_eq_getElem hp_ws] at hw0_some; exact Option.some.inj hw0_some
    exact absurd (hw0_val ▸ hflag) hbin_ne
  · refine ⟨by omega, fun hp1_ws => ?_⟩
    have hw0_val : wstk1[p]'hp_ws = w0 := by
      rw [List.getElem?_eq_getElem hp_ws] at hw0_some; exact Option.some.inj hw0_some
    have hcr_val : wstk1[p + 1]'hp1_ws = cr := by
      rw [List.getElem?_eq_getElem hp1_ws] at hcr_some; exact Option.some.inj hcr_some
    have hp_ws' : p < wstk1.length := hp_ws
    have hp1_ws' : p + 1 < wstk1.length := hp1_ws
    have hq_ws : q < wstk1.length := by omega
    have hq1_ws : q + 1 < wstk1.length := by omega
    let wstk2 := (wstk1.set q (wstk1[p]'hp_ws)).set (q + 1)
      ((wstk1.set q (wstk1[p]'hp_ws))[p + 1]'(by simp [hp1_ws]))
    have hw1_eq : (wstk1.set q (wstk1[p]'hp_ws))[p + 1]'(by simp [hp1_ws]) = cr := by
      rw [List.getElem_set_ne (by omega)]; exact hcr_val
    let k1 : FullCoreState := { st.core with wstk := wstk1, lit_mark := lm1, num_binary := nb1 }
    let k2 : FullCoreState := { st.core with wstk := wstk2, lit_mark := lm1, num_binary := nb1 }
    refine ⟨wstk2, lm1, nb1, rfl, by simp [wstk2, hws], hlm, by omega, by omega, by omega,
      fun idx hidx => by
        dsimp only [wstk2]
        rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
        exact hout idx hidx,
      fun idx hi1 hi2 => by
        dsimp only [wstk2]
        rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
        exact hrem_eq idx (by omega) hi2,
      ?_, ?_, ?_, hul⟩
    · rw [show q + 2 - off = (q - off) + 2 by omega]
      have hq0_s : wstk2[off + (q - off)]? = some w0 := by
        dsimp only [wstk2]
        rw [show off + (q - off) = q by omega, List.getElem?_set_ne (by omega),
          List.getElem?_set_self hq_ws, hw0_val]
      have hq1_s : wstk2[off + (q - off) + 1]? = some cr := by
        dsimp only [wstk2]
        rw [show off + (q - off) + 1 = q + 1 by omega, List.getElem?_set_self (by simp [hq1_ws]),
          hw1_eq]
      exact DenseWatchSliceOk.append_occ (k := k1) (k' := k2) (Nat.le_refl _)
        (fun _ hr => hr) (fun idx hi => by
          dsimp only [k2, k1, wstk2]
          rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)])
        hpref hq0_s hq1_s hbin_eq hw0_sz3 hcr_lt hcr_mem
    · rw [show off + sz - (p + 2) = r2 by omega]
      exact DenseWatchSliceOk.mono (k := k1) (k' := k2)
        (by rw [CNF.entails_def]; exact fun _ h => h) (Nat.le_refl _) (fun _ hr => hr)
        (fun idx hi1 hi2 => by
          dsimp only [k2, k1, wstk2]
          rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)])
        hrem_next
    · intro x hx hne
      obtain ⟨idx, hi1, hi2, hb, ho⟩ := hlmi x hx hne
      refine ⟨idx, hi1, by omega, ?_, ?_⟩
      · dsimp only [wstk2]
        rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]; exact hb
      · dsimp only [wstk2]
        rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]; exact ho

private theorem dedup_step_bin_info {c : FullCfg} {F_cur : List (List Nat)} {st st1 : FullState}
    {l off sz p q : Nat} {ul : Bool}
    (h : DedupLoop1Inv c F_cur st l off sz p q ul st1)
    (hp_lt : p < off + sz) (hp_ws : p < st1.core.wstk.length)
    (hflag : (st1.core.wstk[p]'hp_ws &&& 0x80000000#32) ≠ 0#32) :
    let w0 := st1.core.wstk[p]'hp_ws
    w0 ≠ 0xFFFFFFFF#32 ∧ (w0 &&& 0x7FFFFFFF#32).toNat < 2 * st.core.cur_vars ∧
    (cnfOfClauses F_cur).EntailsClause (cnfClause [l, (w0 &&& 0x7FFFFFFF#32).toNat]) ∧
    DenseWatchSliceOk F_cur st1.core l (p + 1) (off + sz - (p + 1)) := by
  obtain ⟨wstk1, lm1, nb1, rfl, _, _, _, _, _, _, _, _, hrem, _, _⟩ := h
  rcases dedup_slice_step hrem (by omega) with
    ⟨r1, w0, h1eq, hw0_some, _, hneff, hot_lt, hent, hrem_next⟩ |
    ⟨_, w0, _, _, hw0_some, _, hbin_eq, _, _, _, _⟩
  · have hw0_val : wstk1[p]'hp_ws = w0 := by
      rw [List.getElem?_eq_getElem hp_ws] at hw0_some; exact Option.some.inj hw0_some
    rw [hw0_val]
    exact ⟨hneff, hot_lt, hent, by rw [show off + sz - (p + 1) = r1 by omega]; exact hrem_next⟩
  · have hw0_val : wstk1[p]'hp_ws = w0 := by
      rw [List.getElem?_eq_getElem hp_ws] at hw0_some; exact Option.some.inj hw0_some
    exact absurd (hw0_val.symm ▸ hbin_eq) hflag

private theorem dedup_step_bin_drop {c : FullCfg} {F_cur : List (List Nat)} {st st1 : FullState}
    {l off sz p q : Nat} {ul : Bool}
    (h : DedupLoop1Inv c F_cur st l off sz p q ul st1)
    (hp_lt : p < off + sz) (hp_ws : p < st1.core.wstk.length)
    (hflag : (st1.core.wstk[p]'hp_ws &&& 0x80000000#32) ≠ 0#32) (nb' : BitVec 64) :
    DedupLoop1Inv c F_cur st l off sz (p + 1) q ul
      { st1 with core := { st1.core with num_binary := nb' } } := by
  have ⟨_, _, _, hrem_next⟩ := dedup_step_bin_info h hp_lt hp_ws hflag
  obtain ⟨wstk1, lm1, nb1, rfl, hws, hlm, hq_ge, hq_le, hp_le, hout, hrem_eq,
    hpref, _, hlmi, hul⟩ := h
  let k1 : FullCoreState := { st.core with wstk := wstk1, lit_mark := lm1, num_binary := nb1 }
  let k2 : FullCoreState := { st.core with wstk := wstk1, lit_mark := lm1, num_binary := nb' }
  exact ⟨wstk1, lm1, nb', rfl, hws, hlm, hq_ge, by omega, by omega, hout,
    fun idx hi1 hi2 => hrem_eq idx (by omega) hi2,
    DenseWatchSliceOk.mono (k := k1) (k' := k2)
      (by rw [CNF.entails_def]; exact fun _ h => h) (Nat.le_refl _) (fun _ hr => hr)
      (fun _ _ _ => rfl) hpref,
    DenseWatchSliceOk.mono (k := k1) (k' := k2)
      (by rw [CNF.entails_def]; exact fun _ h => h) (Nat.le_refl _) (fun _ hr => hr)
      (fun _ _ _ => rfl) hrem_next,
    hlmi, hul⟩

private theorem dedup_step_bin_keep {c : FullCfg} {F_cur : List (List Nat)} {st st1 : FullState}
    {l off sz p q : Nat} {ul ul2 : Bool}
    (h : DedupLoop1Inv c F_cur st l off sz p q ul st1)
    (hp_lt : p < off + sz) (hp_ws : p < st1.core.wstk.length)
    (hflag : (st1.core.wstk[p]'hp_ws &&& 0x80000000#32) ≠ 0#32)
    (hul2 : ul2 = true → (cnfOfClauses F_cur).EntailsClause (cnfClause [l])) :
    let w0 := st1.core.wstk[p]'hp_ws
    DedupLoop1Inv c F_cur st l off sz (p + 1) (q + 1) ul2
      { st1 with core := { st1.core with
        lit_mark := st1.core.lit_mark.set (w0 &&& 0x7FFFFFFF#32).toNat 1#8
        wstk := st1.core.wstk.set q w0 } } := by
  have ⟨hneff, hot_lt, hent, hrem_next⟩ := dedup_step_bin_info h hp_lt hp_ws hflag
  obtain ⟨wstk1, lm1, nb1, rfl, hws, hlm, hq_ge, hq_le, hp_le, hout, hrem_eq,
    hpref, _, hlmi, _⟩ := h
  have hq_ws : q < wstk1.length := by dsimp only at hp_ws; omega
  let w0 := wstk1[p]'hp_ws
  let lm2 := lm1.set (w0 &&& 0x7FFFFFFF#32).toNat 1#8
  let wstk2 := wstk1.set q w0
  let k1 : FullCoreState := { st.core with wstk := wstk1, lit_mark := lm1, num_binary := nb1 }
  let k2 : FullCoreState := { st.core with wstk := wstk2, lit_mark := lm2, num_binary := nb1 }
  refine ⟨wstk2, lm2, nb1, rfl, by simp [wstk2, hws], by simp [lm2, hlm],
    by omega, by omega, by omega,
    fun idx hidx => by
      dsimp only [wstk2]; rw [List.getElem?_set_ne (by omega)]; exact hout idx hidx,
    fun idx hi1 hi2 => by
      dsimp only [wstk2]; rw [List.getElem?_set_ne (by omega)]; exact hrem_eq idx (by omega) hi2,
    ?_, ?_, ?_, hul2⟩
  · rw [show q + 1 - off = (q - off) + 1 by omega]
    have hq_s : wstk2[off + (q - off)]? = some w0 := by
      dsimp only [wstk2]; rw [show off + (q - off) = q by omega]; exact List.getElem?_set_self hq_ws
    exact DenseWatchSliceOk.append_bin (k := k1) (k' := k2) (Nat.le_refl _) (fun _ hr => hr)
      (fun idx hi => by dsimp only [k2, k1, wstk2]; exact List.getElem?_set_ne (by omega))
      hpref hq_s hflag hneff hot_lt hent
  · exact DenseWatchSliceOk.mono (k := k1) (k' := k2)
      (by rw [CNF.entails_def]; exact fun _ h => h) (Nat.le_refl _) (fun _ hr => hr)
      (fun idx hi1 hi2 => by dsimp only [k2, k1, wstk2]; exact List.getElem?_set_ne (by omega))
      hrem_next
  · intro x hx hne; dsimp only [lm2] at hne
    by_cases hxo : x = (w0 &&& 0x7FFFFFFF#32).toNat
    · refine ⟨q, hq_ge, by omega, ?_, ?_⟩
      · dsimp only [wstk2]; rw [List.getElem?_set_self hq_ws, Option.getD_some]; exact hflag
      · dsimp only [wstk2]; rw [List.getElem?_set_self hq_ws, Option.getD_some]; exact hxo.symm
    · rw [List.getElem?_set_ne (Ne.symm hxo)] at hne
      obtain ⟨idx, hi1, hi2, hb, ho⟩ := hlmi x hx hne
      refine ⟨idx, hi1, by omega, ?_, ?_⟩
      · dsimp only [wstk2]; rw [List.getElem?_set_ne (by omega)]; exact hb
      · dsimp only [wstk2]; rw [List.getElem?_set_ne (by omega)]; exact ho

private theorem dedup_unit_of_neg_mark {c : FullCfg} {F_cur : List (List Nat)} {st st1 : FullState}
    {l off sz p q : Nat} {ul : Bool}
    (h : DedupLoop1Inv c F_cur st l off sz p q ul st1)
    (hcv_le : st.core.cur_vars ≤ c.max_vars)
    (hp_lt : p < off + sz) (hp_ws : p < st1.core.wstk.length)
    (hflag : (st1.core.wstk[p]'hp_ws &&& 0x80000000#32) ≠ 0#32)
    (hneg_lm : st1.core.lit_mark[((st1.core.wstk[p]'hp_ws &&& 0x7FFFFFFF#32) ^^^ 1#32).toNat]?.getD
      0#8 ≠ 0#8) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause [l]) := by
  have ⟨_, hot_lt, hent, _⟩ := dedup_step_bin_info h hp_lt hp_ws hflag
  obtain ⟨wstk1, lm1, nb1, rfl, _, _, hq_ge, _, _, _, _, hpref, _, hlmi, _⟩ := h
  have hnot_lt : ((wstk1[p]'hp_ws &&& 0x7FFFFFFF#32) ^^^ 1#32).toNat < 2 * c.max_vars := by
    rw [FullBvaFwdTactics.bv32_xor1_toNat]
    exact Nat.lt_of_lt_of_le (litNeg_lt_two_mul hot_lt) (by omega)
  obtain ⟨idx, hi1, hi2, hb, ho⟩ := hlmi _ hnot_lt hneg_lm
  have hent_neg := (dedup_slice_bin_word_props hpref idx hi1 (by omega) hb).2
  rw [ho, FullBvaFwdTactics.bv32_xor1_toNat] at hent_neg
  exact FullBvaFwdHelpers.entails_unit_of_bin_pair hent hent_neg

private theorem dedup_finalize_dense {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {st st1 : FullState} {l off sz q : Nat} {ul : Bool} {wstk3 : List (BitVec 32)}
    (hst : FullDenseInvW c F0 F_cur st) (hl_lt : l < 2 * st.core.cur_vars)
    (hoff_eq : off = fullWatchOffCore st.core l) (hsz_eq : sz = fullWatchSizeCore st.core l)
    (h1 : DedupLoop1Inv c F_cur st l off sz (off + sz) q ul st1)
    {lm2b : List (BitVec 8)} (hlm2 : lm2b.length = 2 * c.max_vars)
    (hlm2_clear : ∀ x < 2 * c.max_vars, lm2b[x]?.getD 0#8 = 0#8)
    (hws3 : wstk3.length = c.wcap)
    (hws3_eq : ∀ idx, idx < q ∨ off + sz ≤ idx → wstk3[idx]? = st1.core.wstk[idx]?)
    (wu' : BitVec 64) :
    let st3 : FullState :=
      { st1 with core := { st1.core with lit_mark := lm2b, wstk := wstk3 } }
    let st4 : FullState :=
      { st3 with core := { st3.core with
        wvec := st3.core.wvec.set (2 * l + 1) (BitVec.ofNat 32 (q - off))
        wusable := wu' } }
    FullDenseInvW c F0 F_cur st4 ∧ st4.core.cur_vars = st.core.cur_vars ∧
    st4.core.fuel = st.core.fuel := by
  obtain ⟨wstk1, lm1, nb1, rfl, _, _, hq_ge, hq_le, _, hout1, _, hpref1, _, _, _⟩ := h1
  have hlm2_eq : lm2b = st.core.lit_mark := by
    apply List.ext_getElem (by rw [hlm2, hst.1.core_ok.lit_mark_len])
    intro i hi1 hi2
    have h1' := hlm2_clear i (by omega)
    have h2' := hst.2.2.1.2 i (by omega)
    rw [List.getElem?_eq_getElem hi1, Option.getD_some] at h1'
    rw [List.getElem?_eq_getElem hi2, Option.getD_some] at h2'
    exact h1'.trans h2'.symm
  let k1 : FullCoreState := { st.core with wstk := wstk1, lit_mark := lm1, num_binary := nb1 }
  let k4 : FullCoreState :=
    { st.core with
      wstk := wstk3
      wvec := st.core.wvec.set (2 * l + 1) (BitVec.ofNat 32 (q - off))
      wusable := wu'
      num_binary := nb1 }
  have hslice4 : DenseWatchSliceOk F_cur { st.core with wstk := wstk3, num_binary := nb1 }
      l (fullWatchOffCore st.core l) (q - off) := by
    rw [← hoff_eq]
    exact DenseWatchSliceOk.mono (k := k1) (k' := { st.core with wstk := wstk3, num_binary := nb1 })
      (by rw [CNF.entails_def]; exact fun _ h => h) (Nat.le_refl _) (fun _ hr => hr)
      (fun idx hi1 hi2 => by dsimp only [k1]; exact hws3_eq idx (Or.inl (by omega))) hpref1
  have hdw4 := dedup_denseInvW_of_shrink hst hl_lt (nsz := q - off) (wu' := wu') (nb' := nb1)
    (by omega) hws3
    (fun idx hidx => by
      rw [← hoff_eq, ← hsz_eq] at hidx
      rcases hidx with hlt | hge
      · rw [hws3_eq idx (Or.inl (by omega))]; exact hout1 idx (Or.inl hlt)
      · rw [hws3_eq idx (Or.inr (by omega))]; exact hout1 idx (Or.inr hge))
    hslice4
  intro st3 st4
  have hst4_rw : st4 =
      { st with core :=
        { st.core with
          wvec := st.core.wvec.set (2 * l + 1) (BitVec.ofNat 32 (q - off))
          wstk := wstk3, wusable := wu', num_binary := nb1 } } := by
    dsimp only [st4, st3]; rw [hlm2_eq]
  rw [hst4_rw]
  exact ⟨hdw4, rfl, rfl⟩

/-- Parametric `Env.Has` `Func.wp` proof for `full_fwd_dedup_bins` (`fullFwdDedupBinsSpec`). -/
theorem full_fwd_dedup_bins_wp (Γ : Env)
    (hAddUnit : Γ.Has "full_add_unit" fullAddUnitSpec) :
    ∀ a m Q X, Forward.Spec.fullFwdDedupBinsSpec a m Q X →
      Func.wp Γ full_fwd_dedup_bins_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hinvW, hm, hQ⟩
  have hmx := c.hmaxv; have hwcap := c.hwcap; unfold dimacsBound at hmx hwcap
  have hcv_le_mx : s.core.cur_vars ≤ c.max_vars := hinvW.1.core_ok.cur_vars_le
  have hnlits : (BitVec.ofNat 64 s.core.cur_vars <<< (1 : Nat)).toNat = 2 * s.core.cur_vars := by
    c0_bound
  unfold Func.wp full_fwd_dedup_bins_body
  c0_hfast_nogrp
  refine wp_loop_inv
    (fun (l, ()) ml => ∃ st : FullState,
      l.toNat ≤ 2 * s.core.cur_vars ∧ FullDenseInvW c F0 F_cur st ∧
      st.core.cur_vars = s.core.cur_vars ∧ st.core.fuel = s.core.fuel ∧
      (FullMem c st ⋆ R) ml)
    (fun (l, ()) _ => 2 * s.core.cur_vars - l.toNat)
    (fun J hJ => by
      c0_hfast_nogrp
      exact hJ (0#64, ()) m ⟨s, Nat.zero_le _, hinvW, rfl, rfl, hm⟩)
    (fun J (l, ()) ml ⟨st, hl_le, hst, hcv_st, hfuel_st, hml⟩ ih => ?_)
  have hlen := hst.1.core_ok
  have hcv_st_le : st.core.cur_vars ≤ c.max_vars := hlen.cur_vars_le
  have hwv_len := hlen.wvec_len; have hws_len := hlen.wstk_len_arr
  have hwlen_le := hlen.wlen_le; have hlm_len := hlen.lit_mark_len
  c0_hfast_nogrp
  · have hl_lt : l.toNat < 2 * st.core.cur_vars := by c0_bound
    have hl1_toNat : (l + 1#64).toNat = l.toNat + 1 := by c0_bound
    exact ih _ _
      (by dsimp only; rw [show (l + 1 : BitVec 64) = l + 1#64 from rfl, hl1_toNat]; omega)
      ⟨st, by rw [show (l + 1 : BitVec 64) = l + 1#64 from rfl, hl1_toNat]; omega,
       hst, hcv_st, hfuel_st, hml⟩
  · have hl_lt : l.toNat < 2 * st.core.cur_vars := by c0_bound
    have hdw := fwd_denseWatchesInv_of_w hst
    have hoff_idx : (l <<< (1 : Nat)).toNat = 2 * l.toNat := by c0_bound
    have hsz_idx : ((l <<< (1 : Nat)) + 1#64).toNat = 2 * l.toNat + 1 := by c0_bound
    have hoff_eq : (BitVec.setWidth 64
        (st.core.wvec[(l <<< (1 : Nat)).toNat]'(by omega))).toNat =
        fullWatchOffCore st.core l.toNat := by
      unfold fullWatchOffCore
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some, fwd_zext32_toNat]
      exact congrArg BitVec.toNat (fwd_getElem_congr hoff_idx _ _)
    have hsz_eq : (BitVec.setWidth 64
        (st.core.wvec[((l <<< (1 : Nat)) + 1#64).toNat]'(by omega))).toNat =
        fullWatchSizeCore st.core l.toNat := by
      unfold fullWatchSizeCore
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some, fwd_zext32_toNat]
      exact congrArg BitVec.toNat (fwd_getElem_congr hsz_idx _ _)
    have hbd_l := hdw.layout.bounds l.toNat hl_lt
    have hslice0 := hdw.slices l.toNat hl_lt
    generalize hoff_v : BitVec.setWidth 64
        (st.core.wvec[(l <<< (1 : Nat)).toNat]'(by omega)) = off at *
    generalize hsz_v : BitVec.setWidth 64
        (st.core.wvec[((l <<< (1 : Nat)) + 1#64).toNat]'(by omega)) = sz at *
    have hend_toNat : (off + sz).toNat = off.toNat + sz.toNat := by bv_omega
    refine wp_loop_inv
      (fun (p, q, ul, ()) ml1 => ∃ st1 : FullState,
        DedupLoop1Inv c F_cur st l.toNat off.toNat sz.toNat p.toNat q.toNat ul st1 ∧
        (FullMem c st1 ⋆ R) ml1)
      (fun (p, _, _, _) _ => off.toNat + sz.toNat - p.toNat)
      (fun J1 hJ1 => by
        c0_hfast_nogrp
        refine hJ1 (off, off, false, ()) ml
          ⟨st, ⟨st.core.wstk, st.core.lit_mark, st.core.num_binary, rfl, hws_len, hlm_len,
            Nat.le_refl _, Nat.le_refl _, by omega,
            fun _ _ => rfl, fun _ _ _ => rfl, by simpa using DenseWatchSliceOk.empty,
            by rw [show off.toNat + sz.toNat - off.toNat = sz.toNat by omega, hoff_eq, hsz_eq]
               exact hslice0,
            fun x hx hne => absurd (hst.2.2.1.2 x hx) hne, fun h => by cases h⟩, hml⟩)
      (fun J1 (p, q, ul, ()) ml1 ⟨st1, hinv1, hml1⟩ ih1 => ?_)
    have ⟨wstk1, lm1, nb1, hst1_raw, hws1, hlm1, hq_ge, hq_le, hp_le, _⟩ := hinv1
    have hcv1 : st1.core.cur_vars = st.core.cur_vars := by rw [hst1_raw]
    have hws1_len : st1.core.wstk.length = c.wcap := by rw [hst1_raw]; exact hws1
    have hlm1_len : st1.core.lit_mark.length = 2 * c.max_vars := by rw [hst1_raw]; exact hlm1
    c0_hfast_nogrp
    · have hp_lt : p.toNat < off.toNat + sz.toNat := by c0_bound
      have hflag_c : (st1.core.wstk[p.toNat]'(by omega) &&& 0x80000000#32) = 0#32 := by
        assumption
      have hp1_n : (p + 1#64).toNat = p.toNat + 1 := by c0_bound
      have hp2_n : (p + 1#64 + 1#64).toNat = p.toNat + 2 := by c0_bound
      have hq1_n : (q + 1#64).toNat = q.toNat + 1 := by c0_bound
      have hq2_n : (q + 2#64).toNat = q.toNat + 2 := by c0_bound
      have hp1_lt_end := (dedup_step_occ_ok hinv1 hp_lt (by omega) hflag_c).1
      have hocc := (dedup_step_occ_ok hinv1 hp_lt (by omega) hflag_c).2 (by omega)
      refine wp_join_group (ts := [i64, i64])
        (fun (pn, qn, ()) m' => ∃ st2,
          pn.toNat = p.toNat + 2 ∧
          DedupLoop1Inv c F_cur st l.toNat off.toNat sz.toNat pn.toNat qn.toNat ul st2 ∧
          (FullMem c st2 ⋆ R) m')
        (fun _ ⟨pn, qn, ⟨⟩⟩ m' ⟨st2, hpn, hinv2, hm'⟩ => by
          c0_hsteps_nogrp
          exact ih1 (pn, qn, ul, ()) m' (by dsimp only; omega) ⟨st2, hinv2, hm'⟩)
        (fun Js hJs => by
          c0_hsplit
          · c0_hfast_nogrp
            refine hJs (p + 1#64 + 1#64, q + 2#64, ()) _ ⟨_, hp2_n, ?_, hm⟩
            rw [hp2_n, hq2_n]
            simpa only [show (p + 1 : BitVec 64) = p + 1#64 from rfl,
                        show (q + 1 : BitVec 64) = q + 1#64 from rfl, hp1_n, hq1_n] using hocc
          · exfalso; c0_bound)
    · have hp_lt : p.toNat < off.toNat + sz.toNat := by c0_bound
      have hflag_c : (st1.core.wstk[p.toNat]'(by omega) &&& 0x80000000#32) ≠ 0#32 := by
        intro h; exact hc (by simpa using h)
      have hp1_n : (p + 1#64).toNat = p.toNat + 1 := by c0_bound
      have hq1_n : (q + 1#64).toNat = q.toNat + 1 := by c0_bound
      have hot_lt := (dedup_step_bin_info hinv1 hp_lt (by omega) hflag_c).2.1
      have hlt_pos : (st1.core.wstk[p.toNat]'(by omega) &&& 0x7FFFFFFF#32).toNat <
          st1.core.lit_mark.length := by
        rw [hlm1_len]; exact Nat.lt_of_lt_of_le hot_lt (by omega)
      have hlt_lm : ((st1.core.wstk[p.toNat]'(by omega) &&& 0x7FFFFFFF#32) ^^^ 1#32).toNat <
          st1.core.lit_mark.length := by
        rw [FullBvaFwdTactics.bv32_xor1_toNat]
        exact Nat.lt_of_lt_of_le (litNeg_lt_two_mul hot_lt) (by omega)
      c0_hsteps!
      · refine ih1 (p + 1, q, ul, ()) _
          (by dsimp only; rw [show (p + 1 : BitVec 64) = p + 1#64 from rfl, hp1_n]; omega)
          ⟨_, by rw [show (p + 1 : BitVec 64) = p + 1#64 from rfl, hp1_n]
                 exact dedup_step_bin_drop hinv1 hp_lt (by omega) hflag_c
                   (st1.core.num_binary - 1),
           hm⟩
      · refine ih1 (p + 1, q, ul, ()) _
          (by dsimp only; rw [show (p + 1 : BitVec 64) = p + 1#64 from rfl, hp1_n]; omega)
          ⟨st1, by rw [show (p + 1 : BitVec 64) = p + 1#64 from rfl, hp1_n]
                   exact dedup_step_bin_drop hinv1 hp_lt (by omega) hflag_c st1.core.num_binary,
           hml1⟩
      · refine ih1 (p + 1, q, ul, ()) _
          (by dsimp only; rw [show (p + 1 : BitVec 64) = p + 1#64 from rfl, hp1_n]; omega)
          ⟨st1, by rw [show (p + 1 : BitVec 64) = p + 1#64 from rfl, hp1_n]
                   exact dedup_step_bin_drop hinv1 hp_lt (by omega) hflag_c st1.core.num_binary,
           hml1⟩
      · have hneg_eq : ((st1.core.wstk[p.toNat]'(by omega) &&& 0x7FFFFFFF#32) ^^^ 1#32).toNat =
            (st1.core.wstk[p.toNat]'(by omega) &&& 2147483647#32).toNat ^^^ 1 :=
          FullBvaFwdTactics.bv32_xor1_toNat _
        have hlt_lm_nat :
            (st1.core.wstk[p.toNat]'(by omega) &&& 2147483647#32).toNat ^^^ 1 <
            st1.core.lit_mark.length := hneg_eq ▸ hlt_lm
        have hneg_lm : st1.core.lit_mark[((st1.core.wstk[p.toNat]'(by omega) &&&
            0x7FFFFFFF#32) ^^^ 1#32).toNat]?.getD 0#8 ≠ 0#8 := by
          simp only [show (2147483647 : BitVec 32) = 2147483647#32 from rfl,
            show BitVec.ofNat (OfNat.ofNat 32) (OfNat.ofNat 0) = 0#32 from rfl] at *
          rw [hneg_eq, List.getElem?_eq_getElem hlt_lm_nat, Option.getD_some]
          intro h
          have hc0 : BitVec.setWidth 32 (st1.core.lit_mark[
              (st1.core.wstk[p.toNat]'(by omega) &&& 2147483647#32).toNat ^^^ 1]'
              hlt_lm_nat) = 0#32 := by rw [h]; rfl
          contradiction
        have hul_t := dedup_unit_of_neg_mark hinv1 hcv_st_le hp_lt (by omega) hflag_c hneg_lm
        refine ih1 (p + 1, q + 1, true, ()) _
          (by dsimp only; rw [show (p + 1 : BitVec 64) = p + 1#64 from rfl, hp1_n]; omega)
          ⟨_, by rw [show (p + 1 : BitVec 64) = p + 1#64 from rfl,
                     show (q + 1 : BitVec 64) = q + 1#64 from rfl, hp1_n, hq1_n]
                 exact dedup_step_bin_keep hinv1 hp_lt (by omega) hflag_c (fun _ => hul_t),
           hm⟩
      · have ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hul1⟩ := hinv1
        refine ih1 (p + 1, q + 1, ul, ()) _
          (by dsimp only; rw [show (p + 1 : BitVec 64) = p + 1#64 from rfl, hp1_n]; omega)
          ⟨_, by rw [show (p + 1 : BitVec 64) = p + 1#64 from rfl,
                     show (q + 1 : BitVec 64) = q + 1#64 from rfl, hp1_n, hq1_n]
                 exact dedup_step_bin_keep hinv1 hp_lt (by omega) hflag_c hul1,
           hm⟩
    · have hp_eq : p.toNat = off.toNat + sz.toNat := by c0_bound
      have hinv1_done : DedupLoop1Inv c F_cur st l.toNat off.toNat sz.toNat
          (off.toNat + sz.toNat) q.toNat ul st1 := hp_eq ▸ hinv1
      obtain ⟨ws_d, lm_d, nb_d, hst1_d, hws_d, hlm_d, _, _, _, _, _, hpref1, _,
        hlm_inv1, hul1⟩ := (hinv1_done : _)
      have hinv1_copy : DedupLoop1Inv c F_cur st l.toNat off.toNat sz.toNat
          (off.toNat + sz.toNat) q.toNat ul st1 := hp_eq ▸ hinv1
      refine wp_loop_inv
        (fun (c0, ()) ml2 => ∃ lm2b : List (BitVec 8),
          let st2 : FullState := { st1 with core := { st1.core with lit_mark := lm2b } }
          lm2b.length = 2 * c.max_vars ∧
          off.toNat ≤ c0.toNat ∧ c0.toNat ≤ q.toNat ∧
          (∀ x < 2 * c.max_vars, lm2b[x]?.getD 0#8 ≠ 0#8 →
            ∃ idx, off.toNat ≤ idx ∧ c0.toNat ≤ idx ∧ idx < q.toNat ∧
              (st1.core.wstk[idx]?.getD 0#32 &&& 0x80000000#32) ≠ 0#32 ∧
              (st1.core.wstk[idx]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat = x) ∧
          (FullMem c st2 ⋆ R) ml2)
        (fun (c0, ()) _ => q.toNat - c0.toNat)
        (fun J2 hJ2 => by
          c0_hfast_nogrp
          exact hJ2 (off, ()) ml1 ⟨st1.core.lit_mark, hlm1_len, Nat.le_refl _, hq_ge,
            fun x hx hne => by
              rw [hst1_d] at hne
              obtain ⟨idx, hi1, hi2, hb, ho⟩ := hlm_inv1 x hx hne
              exact ⟨idx, hi1, hi1, hi2, by rw [hst1_d]; exact hb, by rw [hst1_d]; exact ho⟩,
            hml1⟩)
        (fun J2 (c0, ()) ml2 ⟨lm2b, hlm2, hc0_ge, hc0_le, hlm_inv2, hml2⟩ ih2 => ?_)
      let st2 : FullState := { st1 with core := { st1.core with lit_mark := lm2b } }
      c0_hfast_nogrp
      · have hc0_lt : c0.toNat < q.toNat := by c0_bound
        have hc0_lt_ws : c0.toNat < st2.core.wstk.length := by
          dsimp only [st2]; rw [hws1_len]; omega
        have hc1_n : (c0 + 1#64).toNat = c0.toNat + 1 := by c0_bound
        c0_hsteps_nogrp
        c0_hstep
        c0_hsplit
        · have hbin_c : (st1.core.wstk[c0.toNat]?.getD 0#32 &&& 0x80000000#32) ≠ 0#32 := by
            rw [List.getElem?_eq_getElem (by rw [hws1_len]; omega), Option.getD_some]
            intro h; exact hc (by simpa using h)
          have hpref1_st1 :
              DenseWatchSliceOk F_cur st1.core l.toNat off.toNat (q.toNat - off.toNat) := hpref1
          have hprops := dedup_slice_bin_word_props hpref1_st1 c0.toNat hc0_ge (by omega) hbin_c
          have hot_lt_cv :
              (st1.core.wstk[c0.toNat]'(by rw [hws1_len]; omega) &&& 0x7FFFFFFF#32).toNat <
              2 * st.core.cur_vars := by
            have h1 := hprops.1
            rw [List.getElem?_eq_getElem (by rw [hws1_len]; omega), Option.getD_some, hcv1] at h1
            exact h1
          have hot_lt_lm :
              (st1.core.wstk[c0.toNat]'(by rw [hws1_len]; omega) &&& 0x7FFFFFFF#32).toNat <
              lm2b.length := by
            rw [hlm2]; omega
          c0_hsteps!
          refine ih2 (c0 + 1, ()) _
            (by dsimp only; rw [show (c0 + 1 : BitVec 64) = c0 + 1#64 from rfl, hc1_n]; omega)
            ⟨_, by simp [hlm2],
             by rw [show (c0 + 1 : BitVec 64) = c0 + 1#64 from rfl, hc1_n]; omega,
             by rw [show (c0 + 1 : BitVec 64) = c0 + 1#64 from rfl, hc1_n]; omega,
             fun x hx hne => ?_, hm⟩
          have hot64 : (BitVec.setWidth 64
              (st1.core.wstk[c0.toNat]'(by rw [hws1_len]; omega) &&& 0x7FFFFFFF)).toNat =
              (st1.core.wstk[c0.toNat]'(by rw [hws1_len]; omega) &&& 0x7FFFFFFF#32).toNat := by
            rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]; rfl
          have hxne : x ≠
              (st1.core.wstk[c0.toNat]'(by rw [hws1_len]; omega) &&& 0x7FFFFFFF#32).toNat := by
            intro heq
            dsimp only at hne hot64
            rw [heq, ← hot64, List.getElem?_set_self (by rw [hot64]; exact hot_lt_lm),
              Option.getD_some] at hne
            rw [show BitVec.ofNat (OfNat.ofNat 8) (OfNat.ofNat 0) = 0#8 from rfl] at hne
            exact hne rfl
          rw [List.getElem?_set_ne (by rw [hot64]; exact Ne.symm hxne)] at hne
          obtain ⟨idx, hi0, hi1, hi2, hb, ho⟩ := hlm_inv2 x hx hne
          have hidx_ne : idx ≠ c0.toNat := by
            intro heq; subst heq
            rw [List.getElem?_eq_getElem (by rw [hws1_len]; omega), Option.getD_some] at ho
            exact hxne ho.symm
          exact ⟨idx, hi0, by rw [show (c0 + 1 : BitVec 64) = c0 + 1#64 from rfl, hc1_n]; omega,
            hi2, hb, ho⟩
        · c0_hsteps!
          refine ih2 (c0 + 1, ()) _
            (by dsimp only; rw [show (c0 + 1 : BitVec 64) = c0 + 1#64 from rfl, hc1_n]; omega)
            ⟨lm2b, hlm2,
             by rw [show (c0 + 1 : BitVec 64) = c0 + 1#64 from rfl, hc1_n]; omega,
             by rw [show (c0 + 1 : BitVec 64) = c0 + 1#64 from rfl, hc1_n]; omega,
             fun x hx hne => ?_, hml2⟩
          obtain ⟨idx, hi0, hi1, hi2, hb, ho⟩ := hlm_inv2 x hx hne
          have hidx_ne : idx ≠ c0.toNat := by
            intro heq; subst heq
            rw [List.getElem?_eq_getElem (by rw [hws1_len]; omega), Option.getD_some] at hb
            exact hb hc
          exact ⟨idx, hi0, by rw [show (c0 + 1 : BitVec 64) = c0 + 1#64 from rfl, hc1_n]; omega,
            hi2, hb, ho⟩
      · have hc0_eq : c0.toNat = q.toNat := by c0_bound
        have hlm2_clear : ∀ x < 2 * c.max_vars, lm2b[x]?.getD 0#8 = 0#8 := by
          intro x hx
          exact Classical.byContradiction fun hne => by
            obtain ⟨idx, _, hi1, hi2, _, _⟩ := hlm_inv2 x hx hne; omega
        refine wp_loop_inv
          (fun (c1, ()) ml3 => ∃ wstk3 : List (BitVec 32),
            let st3 : FullState := { st2 with core := { st2.core with wstk := wstk3 } }
            wstk3.length = c.wcap ∧ q.toNat ≤ c1.toNat ∧ c1.toNat ≤ off.toNat + sz.toNat ∧
            (∀ idx, idx < q.toNat ∨ off.toNat + sz.toNat ≤ idx →
              wstk3[idx]? = st1.core.wstk[idx]?) ∧
            (FullMem c st3 ⋆ R) ml3)
          (fun (c1, ()) _ => off.toNat + sz.toNat - c1.toNat)
          (fun J3 hJ3 => by
            c0_hfast_nogrp
            exact hJ3 (q, ()) ml2 ⟨st1.core.wstk, hws1_len, Nat.le_refl _, by omega,
              fun _ _ => rfl, hml2⟩)
          (fun J3 (c1, ()) ml3 ⟨wstk3, hws3, hc1_ge, hc1_le, hws3_eq, hml3⟩ ih3 => ?_)
        let st3 : FullState := { st2 with core := { st2.core with wstk := wstk3 } }
        c0_hfast_nogrp
        · have hc1_lt : c1.toNat < off.toNat + sz.toNat := by c0_bound
          have hc1_n : (c1 + 1#64).toNat = c1.toNat + 1 := by c0_bound
          refine ih3 (c1 + 1, ()) _
            (by dsimp only; rw [show (c1 + 1 : BitVec 64) = c1 + 1#64 from rfl, hc1_n]; omega)
            ⟨_, by simp [hws3],
             by rw [show (c1 + 1 : BitVec 64) = c1 + 1#64 from rfl, hc1_n]; omega,
             by rw [show (c1 + 1 : BitVec 64) = c1 + 1#64 from rfl, hc1_n]; omega,
             fun idx hidx => by
               dsimp only; rw [List.getElem?_set_ne (by omega)]; exact hws3_eq idx hidx,
             hm⟩
        · have hwv_lt3 : ((l <<< (1 : Nat)) + 1#64).toNat < st3.core.wvec.length := by
            dsimp only [st3, st2]; rw [hst1_d]; dsimp only; omega
          have hqsub_eq : BitVec.setWidth 32 (q - off) = BitVec.ofNat 32 (q.toNat - off.toNat) := by
            apply BitVec.eq_of_toNat_eq
            rw [BitVec.toNat_setWidth, BitVec.toNat_sub_of_le hq_ge, BitVec.toNat_ofNat]
          have ⟨hst4_dense, hcv4, hfuel4⟩ :=
            dedup_finalize_dense hst hl_lt hoff_eq hsz_eq hinv1_copy hlm2 hlm2_clear
              hws3 hws3_eq (st3.core.wusable + ((off + sz) - q))
          have hl1_n : (l + 1#64).toNat = l.toNat + 1 := by c0_bound
          have hl32_n : (BitVec.setWidth 32 l).toNat = l.toNat := by
            rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
          have hst4_rw : ({ st3 with core := { st3.core with
              wvec := st3.core.wvec.set ((l <<< (1 : Nat)) + 1).toNat
                (BitVec.setWidth 32 (q - off))
              wusable := st3.core.wusable + ((off + sz) - q) } } : FullState) =
            { st3 with core := { st3.core with
              wvec := st3.core.wvec.set (2 * l.toNat + 1) (BitVec.ofNat 32 (q.toNat - off.toNat))
              wusable := st3.core.wusable + ((off + sz) - q) } } := by
            rw [show (l <<< (1 : Nat) + 1 : BitVec 64) = l <<< (1 : Nat) + 1#64 from rfl,
              hsz_idx, hqsub_eq]
          c0_hsteps_nogrp
          c0_hstep
          c0_hsplit
          · c0_hsteps_nogrp
            fwd_call hAddUnit
            refine ⟨c, F0, F_cur, _, R, rfl, hst4_dense.1, hst4_dense.2.1,
              fun _ => by
                change (cnfOfClauses F_cur).EntailsClause (cnfClause [(BitVec.setWidth 32 l).toNat])
                rw [hl32_n]; exact hul1 hc,
              by rw [← hst4_rw]; exact hm,
              fun ok5 vals5 flags5 lvl5 rsns5 trl5 tp5 te5 prop5 cl5 unass5 unfl5 inc5
                  ph5 ta5 ba5 pt5 pb5 hp5 ps5 hl5 qsi5 qss5 m5 hlen5 hw5 hcl5 hfalse5 _ hm5 => ?_⟩
            have hst5_dense := fwd_denseInvW_of_addUnit hst4_dense hlen5 hw5 hcl5
              rfl rfl rfl rfl rfl rfl rfl
            c0_hsteps!
            c0_hsplit
            · c0_hsteps!
              refine ih (l + 1, ()) _
                (by dsimp only; rw [show (l + 1 : BitVec 64) = l + 1#64 from rfl, hl1_n]; omega)
                ⟨_, by rw [show (l + 1 : BitVec 64) = l + 1#64 from rfl, hl1_n]; omega,
                 hst5_dense, hcv4.trans hcv_st, hfuel4.trans hfuel_st, hm5⟩
            · c0_hsteps!
              exact hQ false _ m5 hst5_dense (hcv4.trans hcv_st)
                (hfuel4.trans hfuel_st)
                (fun _ => (hfalse5 (by
                  dsimp only [Arg.val]; rw [hl32_n, hcv4]; exact hl_lt) hc).1) hm5
          · c0_hsteps!
            refine ih (l + 1, ()) _
              (by dsimp only; rw [show (l + 1 : BitVec 64) = l + 1#64 from rfl, hl1_n]; omega)
              ⟨_, by rw [show (l + 1 : BitVec 64) = l + 1#64 from rfl, hl1_n]; omega,
               hst4_dense, hcv4.trans hcv_st, hfuel4.trans hfuel_st, by rw [← hst4_rw]; exact hm⟩
  · exact hQ true st ml hst hcv_st hfuel_st (by simp) hml

end DedupBins

/-! ## 2. `full_fwd_flush_large_m7_wp` Helpers & Proof -/

section FlushLarge

private def FlushCoreOk (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s0 s : FullState) : Prop :=
  s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧ FullLitMarksClear c s ∧
  FullArenaVarsNodup s ∧ FullExtScratchOk c s ∧
  s.core.cur_vars = s0.core.cur_vars ∧ s.core.cur_level = s0.core.cur_level ∧
  s.core.dense_mode = s0.core.dense_mode ∧
  s.core.arena = s0.core.arena ∧ s.core.arena_len = s0.core.arena_len ∧
  s.core.vals = s0.core.vals ∧ s.core.lvl = s0.core.lvl ∧ s.core.flags = s0.core.flags ∧
  s.core.fuel = s0.core.fuel ∧ s.core.oom = s0.core.oom ∧
  s.core.inconsistent = s0.core.inconsistent ∧
  s.core.d_cur = s0.core.d_cur ∧ s.core.d_val = s0.core.d_val ∧
  s.core.num_binary = s0.core.num_binary ∧
  s.core.frame_trail = s0.core.frame_trail ∧ s.core.frame_dec = s0.core.frame_dec ∧
  s.core.trail_end = s0.core.trail_end ∧ s.core.propagated = s0.core.propagated ∧
  s.core.probing = s0.core.probing ∧
  s.scratch.last_learned = s0.scratch.last_learned ∧
  s.scratch.extend_len = s0.scratch.extend_len ∧
  s.scratch.walk_vals = s0.scratch.walk_vals ∧
  s.scratch.walk_best = s0.scratch.walk_best ∧
  s.scratch.red_refs = s0.scratch.red_refs ∧
  s.scratch.tarjan_mark = s0.scratch.tarjan_mark ∧
  s.scratch.tarjan_reach = s0.scratch.tarjan_reach ∧
  s.scratch.scratch_buf = s0.scratch.scratch_buf ∧
  s.scratch.work_stk1 = s0.scratch.work_stk1 ∧
  s.scratch.work_stk2 = s0.scratch.work_stk2 ∧
  s.scratch.sim_sig = s0.scratch.sim_sig

private theorem flushCoreOk_of_shrink {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 sl : FullState} (h : FlushCoreOk c F0 F_cur s0 sl) {l nsz : Nat}
    (hl : l < 2 * sl.core.cur_vars) (hnsz : nsz ≤ fullWatchSizeCore sl.core l)
    {wstk' : List (BitVec 32)} {wu' : BitVec 64} (hwl : wstk'.length = c.wcap)
    (hout : ∀ idx, idx < fullWatchOffCore sl.core l ∨
      fullWatchOffCore sl.core l + fullWatchSizeCore sl.core l ≤ idx →
      wstk'[idx]? = sl.core.wstk[idx]?)
    (hpref : ModeWatchSliceOk F_cur { sl.core with wstk := wstk' } l
      (fullWatchOffCore sl.core l) nsz) :
    let wvec' := sl.core.wvec.set (2 * l + 1) (BitVec.ofNat 32 nsz)
    FlushCoreOk c F0 F_cur s0
      { sl with core := { sl.core with wvec := wvec', wstk := wstk', wusable := wu' } } := by
  obtain ⟨hlen, hw, hlm, hnd, hext, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13,
    h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30⟩ := h
  have ⟨hlen', hw'⟩ := fwd_witnessInv_of_shrink_watch hlen hw hl hnsz (wu' := wu') hwl hout hpref
  exact ⟨hlen', hw', hlm, hnd, hext, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13,
    h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30⟩

private theorem flushCoreOk_of_defrag {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 sl : FullState} (h : FlushCoreOk c F0 F_cur s0 sl)
    {wvec' wstk' wsort' : List (BitVec 32)} {wlen' : Nat}
    (hlen' : ({ sl with
      core := { sl.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := 0#64 }
      scratch := { sl.scratch with wsort := wsort' } } : FullState).LengthsOk c)
    (hlay' : WatchStackLayout
      { sl.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := 0#64 })
    (hslice : ∀ l < 2 * sl.core.cur_vars,
      fullWatchSizeCore
        { sl.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := 0#64 } l =
        fullWatchSize sl l ∧
      ∀ k < fullWatchSize sl l,
        wstk'[fullWatchOffCore
          { sl.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := 0#64 } l + k]? =
        sl.core.wstk[fullWatchOff sl l + k]?) :
    FlushCoreOk c F0 F_cur s0
      { sl with
        core := { sl.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := 0#64 }
        scratch := { sl.scratch with wsort := wsort' } } := by
  obtain ⟨hlen, hw, hlm, hnd, hext, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13,
    h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30⟩ := h
  have ⟨hlen'', hw'⟩ := fwd_witnessInv_of_wstackDefrag hlen hw hlen' hlay' hslice
  exact ⟨hlen'', hw', hlm, hnd, hext, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13,
    h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30⟩

private theorem flushCoreOk_post {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 s1 : FullState} (h : FlushCoreOk c F0 F_cur s0 s1) {m1 : Mem 64}
    {R : Mem 64 → Prop} {Q : Post []}
    (hQ : ∀ s' m',
      s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
      FullLitMarksClear c s' → FullArenaVarsNodup s' → FullExtScratchOk c s' →
      s'.core.cur_vars = s0.core.cur_vars → s'.core.cur_level = s0.core.cur_level →
      s'.core.dense_mode = s0.core.dense_mode →
      s'.core.arena = s0.core.arena → s'.core.arena_len = s0.core.arena_len →
      s'.core.vals = s0.core.vals → s'.core.lvl = s0.core.lvl → s'.core.flags = s0.core.flags →
      s'.core.fuel = s0.core.fuel → s'.core.oom = s0.core.oom →
      s'.core.inconsistent = s0.core.inconsistent →
      s'.core.d_cur = s0.core.d_cur → s'.core.d_val = s0.core.d_val →
      s'.core.num_binary = s0.core.num_binary →
      s'.core.frame_trail = s0.core.frame_trail → s'.core.frame_dec = s0.core.frame_dec →
      s'.core.trail_end = s0.core.trail_end → s'.core.propagated = s0.core.propagated →
      s'.core.probing = s0.core.probing →
      s'.scratch.last_learned = s0.scratch.last_learned →
      s'.scratch.extend_len = s0.scratch.extend_len →
      s'.scratch.walk_vals = s0.scratch.walk_vals →
      s'.scratch.walk_best = s0.scratch.walk_best →
      s'.scratch.red_refs = s0.scratch.red_refs →
      s'.scratch.tarjan_mark = s0.scratch.tarjan_mark →
      s'.scratch.tarjan_reach = s0.scratch.tarjan_reach →
      s'.scratch.scratch_buf = s0.scratch.scratch_buf →
      s'.scratch.work_stk1 = s0.scratch.work_stk1 →
      s'.scratch.work_stk2 = s0.scratch.work_stk2 →
      s'.scratch.sim_sig = s0.scratch.sim_sig →
      (FullMem c s' ⋆ R) m' → Q () m')
    (hm1 : (FullMem c s1 ⋆ R) m1) : Q () m1 :=
  hQ s1 m1 h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2.1
    h.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.2.1
    h.2.2.2.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.2.2.2.2.1
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 hm1

/-- Parametric `Env.Has` `Func.wp` proof for `full_fwd_flush_large_m7`
(`fullFwdFlushLargeM7Spec`, sparse + dense). -/
theorem full_fwd_flush_large_m7_wp (Γ : Env)
    (hDefrag : Γ.Has "full_wstack_defrag" fullWstackDefragSpec) :
    ∀ a m Q X, fullFwdFlushLargeM7Spec a m Q X →
      Func.wp Γ full_fwd_flush_large_m7_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m0 Q X ⟨c, F0, F_cur, s0, R, rfl, hlen0, hw0, hlm0, hnd0, hext0, hm0, hQ⟩
  have hmx := c.hmaxv; have hwc := c.hwcap
  unfold dimacsBound at hmx hwc
  have hcv_le := hlen0.core_ok.cur_vars_le
  have hnl_eq : (BitVec.ofNat 64 s0.core.cur_vars <<< (1 : Nat)).toNat = 2 * s0.core.cur_vars := by
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]; omega
  have h0_ok : FlushCoreOk c F0 F_cur s0 s0 :=
    ⟨hlen0, hw0, hlm0, hnd0, hext0, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  unfold Func.wp full_fwd_flush_large_m7_body
  c0_hsteps_nogrp
  refine wp_loop_group (ts := [i64])
    (fun rem (l, ()) ml => ∃ sl : FullState,
      l.toNat ≤ 2 * s0.core.cur_vars ∧ rem = 2 * s0.core.cur_vars - l.toNat ∧
      FlushCoreOk c F0 F_cur s0 sl ∧ (FullMem c sl ⋆ R) ml)
    ?_ ?_
  · rintro L rem ⟨l, ⟨⟩⟩ ml hL ⟨sl, hl_le, rfl, hok_l, hml⟩
    have hcv_sl : sl.core.cur_vars = s0.core.cur_vars := hok_l.2.2.2.2.2.1
    have hl_nl_lt : ∀ h : l.toNat < (2 * (s0.core.cur_vars % 2 ^ 64)) % 2 ^ 64,
        l.toNat < 2 * sl.core.cur_vars := fun h => by
      rw [hcv_sl]; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h; exact h
    c0_hsplit
    · have hl_lt : l.toNat < 2 * sl.core.cur_vars := hl_nl_lt hc
      have hlen_l := hok_l.1; have hw_l := hok_l.2.1
      have hbd_l := hw_l.watches.bounds l.toNat hl_lt
      have hwlen_le := hlen_l.core_ok.wlen_le
      have hlv0 : (l <<< (1 : Nat)).toNat < sl.core.wvec.length := by
        rw [hlen_l.core_ok.wvec_len]; have := hlen_l.core_ok.cur_vars_le; c0_bound
      have hlv1 : (l <<< (1 : Nat) + 1#64).toNat < sl.core.wvec.length := by
        rw [hlen_l.core_ok.wvec_len]; have := hlen_l.core_ok.cur_vars_le; c0_bound
      have hl1 : (l + 1#64).toNat = l.toNat + 1 := by c0_bound
      c0_hsteps_nogrp
      let off_l := (sl.core.wvec[(l <<< (1 : Nat)).toNat]'hlv0).setWidth 64
      let sz_l := (sl.core.wvec[(l <<< (1 : Nat) + 1#64).toNat]'hlv1).setWidth 64
      have hoff_eq : off_l.toNat = fullWatchOffCore sl.core l.toNat := by
        unfold off_l fullWatchOffCore
        rw [List.getElem?_eq_getElem (by rw [hlen_l.core_ok.wvec_len]; omega), Option.getD_some,
          fwd_zext32_toNat]
        exact congrArg BitVec.toNat (fwd_getElem_congr (by c0_bound) _ _)
      have hsz_eq : sz_l.toNat = fullWatchSizeCore sl.core l.toNat := by
        unfold sz_l fullWatchSizeCore
        rw [List.getElem?_eq_getElem (by rw [hlen_l.core_ok.wvec_len]; omega), Option.getD_some,
          fwd_zext32_toNat]
        exact congrArg BitVec.toNat (fwd_getElem_congr (by c0_bound) _ _)
      refine wp_join0 (P := fun mj => ∃ sj : FullState,
          FlushCoreOk c F0 F_cur s0 sj ∧ (FullMem c sj ⋆ R) mj)
        (fun _ mj ⟨sj, hok_j, hmj⟩ => by
          c0_hsteps!
          exact hL (2 * s0.core.cur_vars - (l + 1#64).toNat) (l + 1#64, ()) mj (by omega)
            ⟨sj, by omega, rfl, hok_j, hmj⟩)
        (fun J hJ => by
          c0_hsplit
          · let end_l := off_l + sz_l
            have hend_eq : end_l.toNat = off_l.toNat + sz_l.toNat := by
              dsimp only [end_l]; rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
            have hsum_c0 :
                ((sl.core.wvec[2 * l.toNat % 2 ^ 64]'(by
                    rw [hlen_l.core_ok.wvec_len]; omega)).toNat +
                  (sl.core.wvec[(2 * l.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
                    rw [hlen_l.core_ok.wvec_len]; simp; omega)).toNat) % 2 ^ 64 = end_l.toNat := by
              have h1 : (sl.core.wvec[2 * l.toNat % 2 ^ 64]'(by
                  rw [hlen_l.core_ok.wvec_len]; omega)).toNat = off_l.toNat := by
                rw [hoff_eq]; unfold fullWatchOffCore
                rw [List.getElem?_eq_getElem (by rw [hlen_l.core_ok.wvec_len]; omega),
                  Option.getD_some]
                exact congrArg BitVec.toNat (fwd_getElem_congr (by omega) _ _)
              have h2 : (sl.core.wvec[(2 * l.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
                  rw [hlen_l.core_ok.wvec_len]; simp; omega)).toNat = sz_l.toNat := by
                rw [hsz_eq]; unfold fullWatchSizeCore
                rw [List.getElem?_eq_getElem (by rw [hlen_l.core_ok.wvec_len]; omega),
                  Option.getD_some]
                exact congrArg BitVec.toNat (fwd_getElem_congr (by simp; omega) _ _)
              rw [h1, h2, Nat.mod_eq_of_lt (by omega), hend_eq]
            c0_hsteps_nogrp
            refine wp_loop_group (ts := [i64, i64])
              (fun rem1 (p, q, ()) m1 => ∃ wstk1 : List (BitVec 32),
                let sp : FullState := { sl with core := { sl.core with wstk := wstk1 } }
                wstk1.length = c.wcap ∧
                off_l.toNat ≤ q.toNat ∧ q.toNat ≤ p.toNat ∧ p.toNat ≤ end_l.toNat ∧
                rem1 = end_l.toNat - p.toNat ∧
                (∀ idx, idx < off_l.toNat ∨ end_l.toNat ≤ idx →
                  wstk1[idx]? = sl.core.wstk[idx]?) ∧
                ModeWatchSliceOk F_cur sp.core l.toNat off_l.toNat (q.toNat - off_l.toNat) ∧
                ModeWatchSliceOk F_cur sp.core l.toNat p.toNat rem1 ∧
                (FullMem c sp ⋆ R) m1)
              ?_ ?_
            · rintro Lp rem1 ⟨p, q, ⟨⟩⟩ m1 hLp
                ⟨wstk1, hwl1, hq_ge, hq_le, hp_le, hrem1, hout1, hpref1, hsuf1, hm1⟩
              let sp : FullState := { sl with core := { sl.core with wstk := wstk1 } }
              c0_hsplit
              · have hp_lt : p.toNat < end_l.toNat := by rw [hsum_c0] at hc; exact hc
                have hpw : p.toNat < wstk1.length := by omega
                have hqw : q.toNat < wstk1.length := by omega
                have hp1_nat : (p + 1#64).toNat = p.toNat + 1 := by c0_bound
                have hq1_nat : (q + 1#64).toNat = q.toNat + 1 := by c0_bound
                rcases hsuf1.cases_step (by omega) with
                  ⟨r1, w0, hr1_eq, hwp, hflag, hne, hot_lt, hent_b, hrest⟩ |
                  ⟨r2, w0, cr, hr2_eq, hwp, _, hflag, hrest⟩
                · have hw0_eq : wstk1[p.toNat]'hpw = w0 := by
                    rw [List.getElem?_eq_getElem hpw] at hwp; exact Option.some.inj hwp
                  c0_hsteps_nogrp
                  refine wp_join_state (ts := [i64, i64])
                    (α := BitVec 64 × BitVec 64 × List (BitVec 32))
                    (fun x => (x.1, x.2.1, ()))
                    (fun x mj =>
                      let sj : FullState := { sl with core := { sl.core with wstk := x.2.2 } }
                      x.2.2.length = c.wcap ∧ off_l.toNat ≤ x.2.1.toNat ∧
                      x.2.1.toNat ≤ x.1.toNat ∧ x.1.toNat ≤ end_l.toNat ∧
                      end_l.toNat - x.1.toNat < end_l.toNat - p.toNat ∧
                      (∀ idx, idx < off_l.toNat ∨ end_l.toNat ≤ idx →
                        x.2.2[idx]? = sl.core.wstk[idx]?) ∧
                      ModeWatchSliceOk F_cur sj.core l.toNat off_l.toNat
                        (x.2.1.toNat - off_l.toNat) ∧
                      ModeWatchSliceOk F_cur sj.core l.toNat x.1.toNat
                        (end_l.toNat - x.1.toNat) ∧
                      (FullMem c sj ⋆ R) mj)
                    (fun _ ⟨pj, qj, wj⟩ mj ⟨hwlj, hqgj, hqlj, hplj, hltj, houtj, hpj, hsj, hmj⟩ =>
                      by
                        c0_hsteps!
                        dsimp only at hltj
                        exact hLp (end_l.toNat - pj.toNat) (pj, qj, ()) mj (by omega)
                          ⟨wj, hwlj, hqgj, hqlj, hplj, rfl, houtj, hpj, hsj, hmj⟩)
                    (fun Jb hJb => by
                      c0_hsplit
                      · c0_hsteps!
                        let wstk2 := wstk1.set q.toNat (wstk1[p.toNat]'hpw)
                        let sp2 : FullState := { sl with core := { sl.core with wstk := wstk2 } }
                        have hpref2 : ModeWatchSliceOk F_cur sp2.core l.toNat off_l.toNat
                            ((q + 1#64).toNat - off_l.toNat) := by
                          rw [hq1_nat, show q.toNat + 1 - off_l.toNat =
                            (q.toNat - off_l.toNat) + 1 by omega]
                          exact ModeWatchSliceOk.append_bin (k := sp.core) (k' := sp2.core)
                            rfl (Nat.le_refl _) (fun _ hr => hr)
                            (fun i hi => by
                              dsimp only [sp2, sp, wstk2]; exact List.getElem?_set_ne (by omega))
                            hpref1
                            (by
                              dsimp only [sp2, wstk2]
                              rw [show off_l.toNat + (q.toNat - off_l.toNat) = q.toNat by omega,
                                hw0_eq]
                              exact List.getElem?_set_self hqw)
                            hflag hne hot_lt hent_b
                        have hent_r : (cnfOfClauses F_cur).Entails (cnfOfClauses F_cur) := by
                          rw [CNF.entails_def]; exact fun _ hx => hx
                        have hsuf2 : ModeWatchSliceOk F_cur sp2.core l.toNat (p + 1#64).toNat
                            (end_l.toNat - (p + 1#64).toNat) := by
                          rw [show end_l.toNat - (p + 1#64).toNat = r1 by omega, hp1_nat]
                          exact ModeWatchSliceOk.mono (k := sp.core) (k' := sp2.core)
                            hent_r rfl (Nat.le_refl _) (fun _ hr => hr) (fun idx hi1 _ => by
                              dsimp only [sp2, sp, wstk2]; exact List.getElem?_set_ne (by omega))
                            hrest
                        exact hJb (p + 1#64, q + 1#64, wstk2) m
                          ⟨by simp [wstk2, hwl1], by dsimp only; omega, by dsimp only; omega,
                           by dsimp only; omega, by dsimp only; omega,
                           fun idx hidx => by
                             dsimp only [wstk2]; rw [List.getElem?_set_ne (by omega)]
                             exact hout1 idx hidx,
                           hpref2, hsuf2, hm⟩
                      · rw [hw0_eq] at hc; exact absurd hc hflag)
                · have hw0_eq : wstk1[p.toNat]'hpw = w0 := by
                    rw [List.getElem?_eq_getElem hpw] at hwp; exact Option.some.inj hwp
                  have hp2_nat : (p + 1#64 + 1#64).toNat = p.toNat + 2 := by c0_bound
                  c0_hsteps_nogrp
                  refine wp_join_state (ts := [i64, i64])
                    (α := BitVec 64 × BitVec 64 × List (BitVec 32))
                    (fun x => (x.1, x.2.1, ()))
                    (fun x mj =>
                      let sj : FullState := { sl with core := { sl.core with wstk := x.2.2 } }
                      x.2.2.length = c.wcap ∧ off_l.toNat ≤ x.2.1.toNat ∧
                      x.2.1.toNat ≤ x.1.toNat ∧ x.1.toNat ≤ end_l.toNat ∧
                      end_l.toNat - x.1.toNat < end_l.toNat - p.toNat ∧
                      (∀ idx, idx < off_l.toNat ∨ end_l.toNat ≤ idx →
                        x.2.2[idx]? = sl.core.wstk[idx]?) ∧
                      ModeWatchSliceOk F_cur sj.core l.toNat off_l.toNat
                        (x.2.1.toNat - off_l.toNat) ∧
                      ModeWatchSliceOk F_cur sj.core l.toNat x.1.toNat
                        (end_l.toNat - x.1.toNat) ∧
                      (FullMem c sj ⋆ R) mj)
                    (fun _ ⟨pj, qj, wj⟩ mj ⟨hwlj, hqgj, hqlj, hplj, hltj, houtj, hpj, hsj, hmj⟩ =>
                      by
                        c0_hsteps!
                        dsimp only at hltj
                        exact hLp (end_l.toNat - pj.toNat) (pj, qj, ()) mj (by omega)
                          ⟨wj, hwlj, hqgj, hqlj, hplj, rfl, houtj, hpj, hsj, hmj⟩)
                    (fun Jb hJb => by
                      c0_hsplit
                      · rw [hw0_eq] at hc; exact absurd hflag hc
                      · c0_hsteps_nogrp
                        refine wp_join_state_pure (ts := [i64]) (α := BitVec 64) (fun x => (x, ()))
                          (fun x => x = p + 1#64 + 1#64)
                          (fun _ px hpx => by
                            subst hpx; c0_hsteps!
                            exact hJb (p + 1#64 + 1#64, q, wstk1) m1
                              ⟨hwl1, hq_ge, by dsimp only; omega, by dsimp only; omega,
                               by dsimp only; omega, hout1, hpref1,
                               by dsimp only
                                  rw [show end_l.toNat - (p + 1#64 + 1#64).toNat = r2 by omega,
                                    hp2_nat]; exact hrest, hm1⟩)
                          (fun Jp hJp => by
                            c0_hsplit
                            · c0_hsteps!; exact hJp (p + 1#64 + 1#64) rfl
                            · rw [hsum_c0] at hc; simp at hc; omega))
              · c0_hsteps_nogrp
                refine wp_loop_group (ts := [i64])
                  (fun rem2 (cc, ()) m2 => ∃ wstk2 : List (BitVec 32),
                    let sc : FullState := { sl with core := { sl.core with wstk := wstk2 } }
                    wstk2.length = c.wcap ∧ q.toNat ≤ cc.toNat ∧ cc.toNat ≤ end_l.toNat ∧
                    rem2 = end_l.toNat - cc.toNat ∧
                    (∀ idx, idx < off_l.toNat ∨ end_l.toNat ≤ idx →
                      wstk2[idx]? = sl.core.wstk[idx]?) ∧
                    ModeWatchSliceOk F_cur sc.core l.toNat off_l.toNat (q.toNat - off_l.toNat) ∧
                    (FullMem c sc ⋆ R) m2)
                  ?_ ?_
                · rintro Lc rem2 ⟨cc, ⟨⟩⟩ m2 hLc
                    ⟨wstk2, hwl2, hc_ge, hc_le, hrem2, hout2, hpref2, hm2⟩
                  let sc : FullState := { sl with core := { sl.core with wstk := wstk2 } }
                  c0_hsplit
                  · have hc_lt : cc.toNat < end_l.toNat := by rw [hsum_c0] at hc; exact hc
                    have hcw : cc.toNat < wstk2.length := by omega
                    have hc1_nat : (cc + 1#64).toNat = cc.toNat + 1 := by c0_bound
                    c0_hsteps!
                    let wstk3 := wstk2.set cc.toNat 0xFFFFFFFF#32
                    let sc3 : FullState := { sl with core := { sl.core with wstk := wstk3 } }
                    have hent_r : (cnfOfClauses F_cur).Entails (cnfOfClauses F_cur) := by
                      rw [CNF.entails_def]; exact fun _ hx => hx
                    have hpref3 : ModeWatchSliceOk F_cur sc3.core l.toNat off_l.toNat
                        (q.toNat - off_l.toNat) :=
                      ModeWatchSliceOk.mono (k := sc.core) (k' := sc3.core)
                        hent_r rfl (Nat.le_refl _) (fun _ hr => hr) (fun idx _ hi2 => by
                          dsimp only [sc3, sc, wstk3]; exact List.getElem?_set_ne (by omega))
                        hpref2
                    exact hLc (end_l.toNat - (cc + 1#64).toNat) (cc + 1#64, ()) _ (by omega)
                      ⟨wstk3, by simp [wstk3, hwl2], by omega, by omega, rfl,
                       fun idx hidx => by
                         dsimp only [wstk3]; rw [List.getElem?_set_ne (by omega)]
                         exact hout2 idx hidx,
                       hpref3, hm⟩
                  · have hwv_idx : (l <<< (1 : Nat) + 1#64).toNat < sl.core.wvec.length := hlv1
                    have hwv_idx_eq : (l <<< (1 : Nat) + 1#64).toNat = 2 * l.toNat + 1 := by
                      c0_bound
                    c0_hsteps!
                    let nsz := q.toNat - off_l.toNat
                    have hq_sub : ((q - off_l).setWidth 32) = BitVec.ofNat 32 nsz := by
                      apply BitVec.eq_of_toNat_eq
                      rw [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat]
                      have hq_sub_eq : (2 ^ 64 - off_l.toNat + q.toNat) % 2 ^ 64 = nsz := by
                        dsimp only [nsz]; omega
                      rw [hq_sub_eq]
                    let wvec_f :=
                      sl.core.wvec.set (l <<< (1 : Nat) + 1#64).toNat ((q - off_l).setWidth 32)
                    let sf : FullState :=
                      { sc with
                        core := { sc.core with
                          wvec := wvec_f, wusable := sc.core.wusable + (end_l - q) } }
                    have hsf_eq : sf =
                        { sl with
                          core := { sl.core with
                            wvec := sl.core.wvec.set (2 * l.toNat + 1) (BitVec.ofNat 32 nsz),
                            wstk := wstk2,
                            wusable := sl.core.wusable + (end_l - q) } } := by
                      dsimp only [sf, sc, wvec_f]; rw [hwv_idx_eq, hq_sub]
                    have hok_f : FlushCoreOk c F0 F_cur s0 sf := by
                      rw [hsf_eq]
                      exact flushCoreOk_of_shrink hok_l hl_lt (nsz := nsz) (by omega) hwl2
                        (fun idx hidx => hout2 idx (by rw [hoff_eq, hsz_eq] at *; omega))
                        (by simpa only [hoff_eq, nsz] using hpref2)
                    exact hJ m ⟨sf, hok_f, hm⟩
                · intro Lc hLc; c0_hsteps!
                  exact hLc (end_l.toNat - q.toNat) (q, ()) m1
                    ⟨wstk1, hwl1, Nat.le_refl _, by omega, rfl, hout1, hpref1, hm1⟩
            · intro Lp hLp; c0_hsteps!
              exact hLp sz_l.toNat (off_l, off_l, ()) ml
                ⟨sl.core.wstk, hlen_l.core_ok.wstk_len_arr, Nat.le_refl _, Nat.le_refl _,
                 by omega, by omega, fun _ _ => rfl,
                 by rw [Nat.sub_self]; exact ModeWatchSliceOk.empty,
                 by rw [hoff_eq, hsz_eq]
                    exact ModeWatchSliceOk.of_modeWatchesInv hw_l.watches hl_lt,
                 hml⟩
          · c0_hsteps!; exact hJ ml ⟨sl, hok_l, hml⟩)
    · c0_hsteps_nogrp
      refine wp_join0 (P := fun mf => ∃ sf : FullState,
        FlushCoreOk c F0 F_cur s0 sf ∧ (FullMem c sf ⋆ R) mf)
        (fun _ mf ⟨sf, hok_f, hmf⟩ => by
          c0_hsteps!; exact flushCoreOk_post hok_f hQ hmf)
        (fun Jd hJd => by
          c0_hsplit
          · c0_hsteps_nogrp
            fwd_call hDefrag
            refine ⟨c, sl, R, rfl, hok_l.1, hok_l.2.1.watches.layout, hml, ?_⟩
            intro wvec' wstk' wlen' wsort' m1 sd hlen_d hlay_d _ hslice_d hm1
            have hok_d : FlushCoreOk c F0 F_cur s0 sd :=
              flushCoreOk_of_defrag hok_l hlen_d hlay_d hslice_d
            c0_hsteps!
            exact hJd m1 ⟨sd, hok_d, hm1⟩
          · c0_hsteps!; exact hJd ml ⟨sl, hok_l, hml⟩)
  · intro L hL; c0_hsteps!
    exact hL (2 * s0.core.cur_vars) (0#64, ()) m0
      ⟨s0, Nat.zero_le _, by simp, h0_ok, hm0⟩

end FlushLarge

end LeanQbe.T.Examples.Kissat.Proof.Forward
