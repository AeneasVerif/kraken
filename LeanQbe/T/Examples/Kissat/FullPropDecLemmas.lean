module

public import LeanQbe.T.Examples.Kissat.FullPropDecLemmas4
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Full` Propagate / Decide / Warmup / Rephase / Restart `Func.wp` Proofs (`Stage 4`)

Re-exports all 9 parametric `(Γ : Env)` `Func.wp` theorems for the Chronological BCP / Decide /
Warmup / Rephase / Restart shard:
1. `full_find_repl_wp` (`FullPropDecLemmas1`)
2. `full_assign_level_wp` (`FullPropDecLemmas1`)
3. `full_prop_lit_wp` (`FullPropDecLemmas3`)
4. `full_propagate_ignore_wp` (this file)
5. `full_propagate_wp` (this file)
6. `full_decide_wp` (this file)
7. `full_warmup_wp` (this file)
8. `full_rephase_wp` (this file)
9. `full_restart_wp` (this file)
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.ProofUtil
  LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat Kraken.Bedrock2.Test
open scoped FullArenaTactics FullPropDecTactics
open FullPropDecSpecs

local macro "fp_nojoin" : tactic =>
  `(tactic| repeat (any_goals ((fail_if_success (apply wp_unroll_group)); fp_step)))

/-! ## 1. `full_propagate_ignore` & `full_propagate` `Func.wp` proofs -/

private def propCoreMask (k : FullCoreState) : FullCoreState :=
  { propLitCoreMask k with propagated := 0, fuel := 0#64 }

private theorem prop_eq_upd {s st : FullState} (h : AgreesExcept propCoreMask s.core st.core)
    (hsc : st.scratch = { s.scratch with
      search_ticks := st.scratch.search_ticks, wsort := st.scratch.wsort,
      phases := st.scratch.phases }) :
    st =
      { core :=
          { s.core with
            vals := st.core.vals, flags := st.core.flags, lvl := st.core.lvl, rsns := st.core.rsns,
            trl := st.core.trl, trail_pos := st.core.trail_pos, trail_end := st.core.trail_end,
            propagated := st.core.propagated, unassigned := st.core.unassigned,
            unflushed := st.core.unflushed, wvec := st.core.wvec, arena := st.core.arena,
            wstk := st.core.wstk, wlen := st.core.wlen, wusable := st.core.wusable,
            fuel := st.core.fuel, confl_type := st.core.confl_type, confl_ref := st.core.confl_ref,
            confl_lit0 := st.core.confl_lit0, confl_lit1 := st.core.confl_lit1, oom := st.core.oom }
        scratch := { s.scratch with
          search_ticks := st.scratch.search_ticks, wsort := st.scratch.wsort,
          phases := st.scratch.phases } } := by
  have h1 := h.get FullCoreState.d_cur; have h2 := h.get FullCoreState.d_val
  have h3 := h.get FullCoreState.cur_vars; have h4 := h.get FullCoreState.arena_len
  have h5 := h.get FullCoreState.arena_garbage; have h6 := h.get FullCoreState.first_reducible
  have h7 := h.get FullCoreState.num_irred; have h8 := h.get FullCoreState.num_redundant
  have h9 := h.get FullCoreState.num_binary; have h10 := h.get FullCoreState.probing
  have h11 := h.get FullCoreState.cur_level; have h12 := h.get FullCoreState.tmp_cnt
  have h13 := h.get FullCoreState.tmp_len; have h14 := h.get FullCoreState.min_clr_len
  have h15 := h.get FullCoreState.min_clr_full; have h16 := h.get FullCoreState.dense_mode
  have h17 := h.get FullCoreState.inconsistent; have h18 := h.get FullCoreState.lit_mark
  have h19 := h.get FullCoreState.mrk; have h20 := h.get FullCoreState.tmp
  have h21 := h.get FullCoreState.min_clr; have h22 := h.get FullCoreState.frame_trail
  have h23 := h.get FullCoreState.frame_dec; have h24 := h.get FullCoreState.repr
  have h25 := h.get FullCoreState.min_stk
  cases st with | mk stc stsc =>
  cases s with | mk sc ssc =>
  dsimp only at hsc; rw [hsc]
  cases stc; cases sc; simp only at *; subst_vars; rfl

theorem full_propagate_ignore_wp (Γ : Env)
    (hPropLit : ∀ args m Q X, fullPropLitSpec args m Q X →
      Γ "full_prop_lit" [i64, i32, i64] [.bool] args m Q X) :
    ∀ args m Q X, fullPropagateIgnoreSpec args m Q X →
      Func.wp Γ full_propagate_ignore_body args m Q X := by
  rintro ⟨h, ignore_ref, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen0, hw0, hdense0, hm, hQ⟩
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  have hret_st : ∀ (r : BitVec 64) (st : FullState) (ml : Mem 64),
      st.LengthsOk c → FullWitnessInv c F0 F_cur st.core →
      AgreesExcept propCoreMask s.core st.core →
      FullTrailExt s.core st.core → FullArenaPermEq s.core st.core →
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
        FullConflOkW F_cur st.core ∧
        (st.core.confl_type = 2#64 → st.core.confl_ref ≠ ignore_ref) ∧
        (st.core.cur_level = 0 → F0.Unsat)) →
      (r = 2#64 → st.core.oom ≠ 0#64 ∨ st.core.fuel = 0#64) →
      (s.core.propagated = s.core.trail_end → r = 0#64 ∧ st = s) →
      (FullMem c st ⋆ R) ml → Q (r, ()) ml := by
    intro r st ml hst_l hst_w hag htr hperm hfl hsc hr hr0 hr1 hr2 hnoop hml
    have hst_eq := prop_eq_upd hag hsc
    have hst_l' := hst_l; have hst_w' := hst_w; have htr' := htr; have hperm' := hperm
    rw [hst_eq] at hst_l' hst_w' htr' hperm' hml
    refine hQ r st.core.vals st.core.flags st.core.lvl st.core.rsns st.core.trl st.core.trail_pos
      st.core.trail_end st.core.propagated st.core.unassigned st.core.unflushed st.core.wvec
      st.core.arena st.core.wstk st.core.wlen st.core.wusable st.core.fuel st.core.confl_type
      st.core.confl_ref st.core.confl_lit0 st.core.confl_lit1 st.core.oom
      st.scratch.search_ticks st.scratch.wsort st.scratch.phases ml
      hst_l' hst_w' htr' hperm' hfl hr hr0 ?_ hr2 ?_ hml
    · intro h1; have hcf := hr1 h1; rw [hst_eq] at hcf; exact hcf
    · intro hpe; obtain ⟨h0, heq⟩ := hnoop hpe; exact ⟨h0, hst_eq ▸ heq⟩
  fp_steps
  refine wp_loop_group
    (fun rem () ml => ∃ st : FullState,
      rem = st.core.fuel.toNat ∧ st.LengthsOk c ∧ FullWitnessInv c F0 F_cur st.core ∧
      AgreesExcept propCoreMask s.core st.core ∧ FullTrailExt s.core st.core ∧
      FullArenaPermEq s.core st.core ∧ st.core.fuel.toNat ≤ s.core.fuel.toNat ∧
      st.scratch = { s.scratch with
        search_ticks := st.scratch.search_ticks, wsort := st.scratch.wsort,
        phases := st.scratch.phases } ∧
      (s.core.oom = 0#64 → st.core.oom = 0#64) ∧
      st.core.confl_type = s.core.confl_type ∧
      (st.core.fuel.toNat = s.core.fuel.toNat → st = s) ∧
      (s.core.propagated = s.core.trail_end → st = s) ∧
      (FullMem c st ⋆ R) ml) ?_ ?_
  · rintro L rem ⟨⟩ ml ih
      ⟨st, rfl, hst_l, hst_w, hag, htr, hperm, hfuel_le, hsc, hoom_pres, hct_pres, hsame, hnoop,
        hml⟩
    have hcl := hst_l.core_ok
    have hcv_le := hcl.cur_vars_le
    have htl := hcl.trl_len; have hte_le := hcl.trail_end_le; have hpr_le := hcl.propagated_le
    have hdm_st : st.core.dense_mode = 0#64 := (hag.get FullCoreState.dense_mode).trans hdense0
    fp_steps
    · have hpr_lt : st.core.propagated < st.core.trail_end := by c0_bound
      have hne_end : s.core.propagated ≠ s.core.trail_end := fun h => by
        have := hnoop h; subst this; omega
      exact hret_st 2#64 st ml hst_l hst_w hag htr hperm hfuel_le hsc (Or.inr (Or.inr rfl))
        (by simp) (by simp) (fun _ => Or.inl hc) (fun hpe => absurd hpe hne_end) hml
    · have hpr_lt : st.core.propagated < st.core.trail_end := by c0_bound
      have hne_end : s.core.propagated ≠ s.core.trail_end := fun h => by
        have := hnoop h; subst this; omega
      exact hret_st 2#64 st ml hst_l hst_w hag htr hperm hfuel_le hsc (Or.inr (Or.inr rfl))
        (by simp) (by simp) (fun _ => Or.inr hc) (fun hpe => absurd hpe hne_end) hml
    · have hpr_lt : st.core.propagated < st.core.trail_end := by c0_bound
      have hne_end : s.core.propagated ≠ s.core.trail_end := fun h => by
        have := hnoop h; subst this; omega
      have hoom0_st : st.core.oom = 0#64 := by assumption
      have hfuel_sub : (st.core.fuel - 1#64).toNat = st.core.fuel.toNat - 1 := bv64_sub1_toNat hc
      have hfuel_pos : 0 < st.core.fuel.toNat :=
        Nat.pos_of_ne_zero fun h0 => hc (BitVec.eq_of_toNat_eq (by simpa using h0))
      have hpr1 : (BitVec.ofNat 64 st.core.propagated + 1#64).toNat = st.core.propagated + 1 := by
        c0_bound
      let st1 : FullState := { st with core := { st.core with
        fuel := st.core.fuel - 1#64,
        propagated := (BitVec.ofNat 64 st.core.propagated + 1#64).toNat } }
      have hlen1 : st1.LengthsOk c :=
        ⟨{ hcl with propagated_le := by dsimp only [st1]; rw [hpr1]; omega }, hst_l.scratch_ok⟩
      have hw1 : FullWitnessInv c F0 F_cur st1.core := hst_w.with_fuel_prop _ _
      c0_call hPropLit
      refine ⟨c, F0, F_cur, st1, R, rfl, hlen1, hw1, hdm_st, hoom0_st, hm,
        fun ok vals' flags' lvl' rsns' trl' tp' te' unas' unfl' wvec' arena' wstk' wlen' wu'
          ctype' cref' c0' c1' oom' ticks' wsort' phases' m2 hlen2 hw2 htr2 hperm2
          hok_oom hconfl hm2 => ?_⟩
      let st2 : FullState :=
        { core :=
            { st1.core with
              vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
              trail_pos := tp', trail_end := te', unassigned := unas', unflushed := unfl',
              wvec := wvec', arena := arena', wstk := wstk', wlen := wlen', wusable := wu',
              confl_type := ctype', confl_ref := cref', confl_lit0 := c0', confl_lit1 := c1',
              oom := oom' }
          scratch := { st1.scratch with
            search_ticks := ticks', wsort := wsort', phases := phases' } }
      have hag1 : AgreesExcept propCoreMask s.core st1.core :=
        hag.update (fun k => { k with fuel := st1.core.fuel, propagated := st1.core.propagated })
      have hag2 : AgreesExcept propCoreMask s.core st2.core :=
        hag1.update (fun k => { k with
          vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
          trail_pos := tp', trail_end := te', unassigned := unas', unflushed := unfl',
          wvec := wvec', arena := arena', wstk := wstk', wlen := wlen', wusable := wu',
          confl_type := ctype', confl_ref := cref', confl_lit0 := c0', confl_lit1 := c1',
          oom := oom' })
      have htr12 : FullTrailExt s.core st2.core :=
        (htr.congr (k2 := st1.core) rfl rfl rfl).trans htr2
      have hperm12 : FullArenaPermEq s.core st2.core := hperm.trans hperm2
      have hsc2 : st2.scratch = { s.scratch with
          search_ticks := st2.scratch.search_ticks, wsort := st2.scratch.wsort,
          phases := st2.scratch.phases } := by dsimp only [st2, st1]; rw [hsc]
      have hfl2_lt : st2.core.fuel.toNat < s.core.fuel.toNat := by dsimp [st2, st1]; omega
      fp_steps
      · have hok_t : ok = true := by assumption
        exact ih st2.core.fuel.toNat () m2 (by dsimp [st2, st1]; omega)
          ⟨st2, rfl, hlen2, hw2, hag2, htr12, hperm12, by omega, hsc2,
            fun _ => (hok_oom hok_t).1, (hok_oom hok_t).2.trans hct_pres,
            fun heq => by omega, fun hpe => absurd hpe hne_end, hm2⟩
      · have hok_f : ok = false := by assumption
        exact hret_st 2#64 st2 m2 hlen2 hw2 hag2 htr12 hperm12 (by omega) hsc2
          (Or.inr (Or.inr rfl)) (by simp) (by simp) (fun _ => Or.inl hc)
          (fun hpe => absurd hpe hne_end) hm2
      · have hok_f : ok = false := by assumption
        have hoom2_0 : oom' = 0#64 := by assumption
        have ⟨hcf_ok, hcf_ign⟩ := (hconfl hok_f).resolve_left (fun h => h hoom2_0)
        exact hret_st 1#64 st2 m2 hlen2 hw2 hag2 htr12 hperm12 (by omega) hsc2
          (Or.inr (Or.inl rfl)) (by simp)
          (fun _ => ⟨hfl2_lt, hoom2_0, hcf_ok, hcf_ign,
            fun hcl0 => hw2.level0_unsat_of_conflOkW hcl0 hcf_ok⟩)
          (by simp) (fun hpe => absurd hpe hne_end) hm2
    · have hpr_eq : st.core.propagated = st.core.trail_end := by c0_bound
      exact hret_st 0#64 st ml hst_l hst_w hag htr hperm hfuel_le hsc (Or.inl rfl)
        (fun _ => ⟨hpr_eq, hct_pres, hoom_pres, fun hlt => by
          by_cases hf : st.core.fuel.toNat = s.core.fuel.toNat
          · have := hsame hf; subst this; omega
          · omega⟩)
        (by simp) (by simp) (fun hpe => ⟨rfl, hnoop hpe⟩) hml
  · intro L hL; fp_steps
    exact hL s.core.fuel.toNat () m ⟨s, rfl, hlen0, hw0, .refl _ _, .refl _, .refl _,
      Nat.le_refl _, rfl, fun h => h, rfl, fun _ => rfl, fun _ => rfl, hm⟩

theorem full_propagate_wp (Γ : Env)
    (hPropIgn : ∀ args m Q X, fullPropagateIgnoreSpec args m Q X →
      Γ "full_propagate_ignore" [i64, i64] [i64] args m Q X) :
    ∀ args m Q X, fullPropagateSpec args m Q X →
      Func.wp Γ full_propagate_body args m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen0, hw0, hdense0, hm, hQ⟩
  fp_steps
  c0_call hPropIgn
  refine ⟨c, F0, F_cur, s, R, rfl, hlen0, hw0, hdense0, hm,
    fun r vals' flags' lvl' rsns' trl' tp' te' prop' unas' unfl' wvec' arena' wstk' wlen' wu'
      fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' m' hlen' hw' htr' hperm' hfl' hr hr0
      hr1 hr2 hnoop hm' => ?_⟩
  fp_steps
  exact hQ r vals' flags' lvl' rsns' trl' tp' te' prop' unas' unfl' wvec' arena' wstk' wlen' wu'
    fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' m' hlen' hw' htr' hperm'
    (fun hnd => hperm'.preserves_varsNodup hnd) hfl' hr
    (fun h0 => let ⟨hp, _, ho, hf⟩ := hr0 h0; ⟨hp, ho, hf⟩)
    (fun h1 => let ⟨hf, ho, hca, _, hu⟩ := hr1 h1; ⟨hf, ho, hca, hu⟩) hr2 hnoop hm'

/-! ## 2. Chronological decision invariant & `full_decide` `Func.wp` proof -/

private theorem bv32_dec_lit_even {v : BitVec 64} (hv : v.toNat < 2 ^ 30) :
    ((v <<< (1 : Nat)).setWidth 32).toNat = 2 * v.toNat := by
  have h1 : (v <<< (1 : Nat)).toNat = (2 * v.toNat) % 2 ^ 64 := FullArenaTactics.bv64_shl1_nat v
  rw [BitVec.toNat_setWidth, h1, Nat.mod_eq_of_lt (by omega : 2 * v.toNat < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : 2 * v.toNat < 2 ^ 32)]

private theorem bv32_dec_lit_odd {v : BitVec 64} (hv : v.toNat < 2 ^ 30) :
    (((v <<< (1 : Nat)).setWidth 32) ||| 1#32).toNat = 2 * v.toNat + 1 := by
  have hev := bv32_dec_lit_even hv
  have h1 : ((v <<< (1 : Nat)).setWidth 32 ||| 1#32).toNat =
      ((v <<< (1 : Nat)).setWidth 32).toNat ||| 1 := by simp [BitVec.toNat_or]
  rw [h1, hev]
  have : ∀ n : Nat, (2 * n) ||| 1 = 2 * n + 1 := fun n => by
    apply Nat.eq_of_testBit_eq; intro i
    rw [Nat.testBit_or, show 2 * n + 1 = 2 * n + 1 from rfl]
    cases i with
    | zero => simp [Nat.testBit_zero]
    | succ k =>
      have h0 : Nat.testBit 1 (k + 1) = false := by
        rw [Nat.testBit_succ]; simp
      rw [h0, Bool.or_false, Nat.testBit_succ, Nat.testBit_succ]
      congr 1; omega
  exact this v.toNat

/-- Decision step (`full_decide` and `full_warmup`): setting `frame_trail[cur_level+1]`,
`frame_dec[cur_level+1]`, `cur_level := cur_level + 1`, and assigning `lit` with `rsn = 0xFFFFFFFF`
preserves `FullCoreInv`. -/
theorem full_decide_preserves_fullCore {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hinv : FullCoreInv c F0 s) {v : Nat} {lit : BitVec 32}
    {flags' : List (BitVec 32)} {unas' unfl' : BitVec 64} {scratch' : FullScratch}
    (hsok' : scratch'.LengthsOk c) (hfll : flags'.length = c.max_vars)
    (hv_lt : v < s.core.cur_vars) (hval0 : s.core.vals[2 * v]?.getD 0#8 = 0#8)
    (hlit_eq : lit.toNat = 2 * v ∨ lit.toNat = 2 * v + 1) :
    let nlvl := s.core.cur_level + 1
    let ftrl' := s.core.frame_trail.set nlvl (BitVec.ofNat 32 s.core.trail_end)
    let fdec' := s.core.frame_dec.set nlvl lit
    let s' : FullState :=
      { core :=
          { s.core with
            vals := (s.core.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8
            flags := flags', lvl := s.core.lvl.set (lit.toNat / 2) (BitVec.ofNat 32 nlvl)
            rsns := s.core.rsns.set (lit.toNat / 2) 0xFFFFFFFF#32
            trl := s.core.trl.set s.core.trail_end lit
            trail_pos := s.core.trail_pos.set (lit.toNat / 2) (BitVec.ofNat 32 s.core.trail_end)
            frame_trail := ftrl', frame_dec := fdec', trail_end := s.core.trail_end + 1
            cur_level := nlvl, unassigned := unas', unflushed := unfl' }
        scratch := scratch' }
    FullCoreInv c F0 s' ∧ s.core.vals[lit.toNat]?.getD 0#8 = 0#8 ∧
    s.core.trail_end < s.core.cur_vars ∧ nlvl ≤ c.max_vars := by
  intro nlvl ftrl' fdec' s'
  obtain ⟨F_cur, hw⟩ := hinv.witness
  have hcl := hinv.lengths.core_ok
  have hcv := hcl.cur_vars_le; have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  have hlit_lt : lit.toNat < 2 * s.core.cur_vars := by omega
  have hlit_v : lit.toNat / 2 = v := by omega
  have hun : s.core.vals[lit.toNat]?.getD 0#8 = 0#8 := by
    rcases hlit_eq with he | ho
    · rw [he]; exact hval0
    · rw [ho]; exact hw.vals_zero_xor1 (by omega) hval0
  have hte_lt : s.core.trail_end < s.core.cur_vars := hw.trail_end_lt_of_unassigned hlit_lt hun
  have hcl_le : s.core.cur_level ≤ s.core.trail_end := hw.cur_level_le
  have hnlvl_le : nlvl ≤ c.max_vars := by dsimp [nlvl]; omega
  have hte_lt32 : s.core.trail_end < 2 ^ 32 := by omega
  have hnot_var : ∀ i < s.core.trail_end, (s.core.trl[i]?.getD 0#32).toNat / 2 ≠ lit.toNat / 2 :=
    (hw.vals_zero_iff hlit_lt).mp hun
  have hft_get : ∀ L ≤ nlvl, (ftrl'[L]?.getD 0#32).toNat =
      if L = nlvl then s.core.trail_end else (s.core.frame_trail[L]?.getD 0#32).toNat :=
    fun L _ => by
      by_cases hL : L = nlvl
      · subst hL; dsimp only [ftrl']
        rw [List.getElem?_set_self (by rw [hcl.frame_trail_len]; omega), Option.getD_some,
          bv32_ofNat_toNat hte_lt32]
        simp
      · dsimp only [ftrl']; rw [List.getElem?_set_ne (Ne.symm hL)]; simp [hL]
  have hfd_get : ∀ L ≤ nlvl, (fdec'[L]?.getD 0#32).toNat =
      if L = nlvl then lit.toNat else (s.core.frame_dec[L]?.getD 0#32).toNat :=
    fun L _ => by
      by_cases hL : L = nlvl
      · subst hL; dsimp only [fdec']
        rw [List.getElem?_set_self (by rw [hcl.frame_dec_len]; omega), Option.getD_some]; simp
      · dsimp only [fdec']; rw [List.getElem?_set_ne (Ne.symm hL)]; simp [hL]
  have hcore' := chronoAssign_preserves_fullCore hinv (lit := lit) (rsn := 0xFFFFFFFF#32)
    (alvl := nlvl) (cur_level' := nlvl) (propagated' := s.core.propagated)
    (flags' := flags') (frame_trail' := ftrl') (frame_dec' := fdec')
    (unassigned' := unas') (unflushed' := unfl') (scratch' := scratch')
    hsok' hfll (by simp [ftrl', hcl.frame_trail_len]) (by simp [fdec', hcl.frame_dec_len])
    hlit_lt hun (Nat.le_refl _) (by have := hcl.propagated_le; omega) (by dsimp [nlvl]; omega)
    (fun L hL => by
      rw [hft_get L hL]; split
      · omega
      · have := hw.frame_trail_lt L (by dsimp [nlvl] at *; omega); omega)
    (fun L1 L2 h12 h2 => by
      rw [hft_get L1 (by omega), hft_get L2 h2]
      by_cases h2e : L2 = nlvl
      · by_cases h1e : L1 = nlvl
        · simp [h1e, h2e]
        · simp only [h1e, h2e, ↓reduceIte]; exact hw.frame_trail_lt L1 (by dsimp [nlvl] at *; omega)
      · have h1n : L1 ≠ nlvl := by omega
        simp only [h1n, h2e, ↓reduceIte]
        exact hw.frame_trail_mono L1 L2 h12 (by dsimp [nlvl] at *; omega))
    (fun L hL1 hLle i hi => by
      rw [hft_get L hLle] at hi
      by_cases hLe : L = nlvl
      · subst hLe; simp only [↓reduceIte] at hi
        have hne_i : i ≠ s.core.trail_end := by omega
        have hnv : (s.core.trl[i]?.getD 0#32).toNat / 2 ≠ lit.toNat / 2 := hnot_var i hi
        simp only [hne_i, hnv, ↓reduceIte]
        have := hw.lvl_le i hi; dsimp [nlvl]; omega
      · simp only [hLe, ↓reduceIte] at hi
        have hLle' : L ≤ s.core.cur_level := by dsimp [nlvl] at *; omega
        have hi_lt : i < s.core.trail_end := Nat.lt_of_lt_of_le hi (hw.frame_trail_lt L hLle')
        have hne_i : i ≠ s.core.trail_end := by omega
        have hnv : (s.core.trl[i]?.getD 0#32).toNat / 2 ≠ lit.toNat / 2 := hnot_var i hi_lt
        simp only [hne_i, hnv, ↓reduceIte]
        exact hw.frame_trail_before_lt L hL1 hLle' i hi)
    (fun L hL1 hLle => by
      rw [hfd_get L hLle]; split
      · exact hlit_lt
      · exact hw.frame_dec_lt L hL1 (by dsimp [nlvl] at *; omega))
    (fun i hi => by have := hw.lvl_le i hi; dsimp [nlvl]; omega)
    (fun L hL1 hLle => by
      by_cases hLe : L = nlvl
      · exact Or.inl hLe
      · exact Or.inr (hw.levels_inhabited L hL1 (by dsimp [nlvl] at *; omega)))
    (fun _ _ i hi => by have := hw.lvl_le i hi; dsimp [nlvl]; omega)
    (fun hz => by dsimp [nlvl] at hz; omega)
    (fun _ hne => absurd rfl hne)
    (fun _ hne _ => absurd rfl hne)
  have hnlvl_ne0 : nlvl ≠ 0 := by dsimp [nlvl]; omega
  simpa only [s', hnlvl_ne0, ↓reduceIte] using ⟨hcore', hun, hte_lt, hnlvl_le⟩

theorem full_decide_wp (Γ : Env)
    (hNextDec : ∀ args m Q X, fullNextDecVarSpec args m Q X →
      Γ "full_next_dec_var" [i64] [i64] args m Q X)
    (hAssign : ∀ args m Q X, fullAssignSpec args m Q X →
      Γ "full_assign" [i64, i32, i32] [] args m Q X) :
    ∀ args m Q X, fullDecideSpec args m Q X →
      Func.wp Γ full_decide_body args m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, hm, hQ⟩
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  fp_steps
  c0_call hNextDec
  refine ⟨c, s, R, rfl, hinv.lengths, hm, fun chosen sc1 m1 hsc1 hll1 hext1 hch hm1 => ?_⟩
  let s1 : FullState := { s with scratch := sc1 }
  have hinv1 : FullCoreInv c F0 s1 := hinv.with_fuel_scratch hsc1
  have hcl1 := hinv1.lengths.core_ok
  have hcv1 : s.core.cur_vars ≤ c.max_vars := hcl1.cur_vars_le
  have hph1 := hsc1.phases_len; have hptgt1 := hsc1.phases_target_len
  have hftrl1 : s.core.frame_trail.length = c.max_vars + 1 := hcl1.frame_trail_len
  have hfdec1 : s.core.frame_dec.length = c.max_vars + 1 := hcl1.frame_dec_len
  fp_nojoin
  · exact hQ 0#64 s.core.vals s.core.flags s.core.lvl s.core.rsns s.core.trl s.core.trail_pos
      s.core.frame_trail s.core.frame_dec s.core.trail_end s.core.cur_level s.core.unassigned
      s.core.unflushed sc1 m1 hinv1 hll1 hext1 (Or.inl rfl) (fun _ => ⟨rfl, rfl⟩) (by simp) hm1
  · have hch_ne : chosen ≠ 0xFFFFFFFFFFFFFFFF#64 := hc
    obtain ⟨hv_lt, hval0⟩ := hch.resolve_left hch_ne
    have hch_lt_max : chosen.toNat < c.max_vars := by omega
    have hch_lt30 : chosen.toNat < 2 ^ 30 := by omega
    fp_nojoin
    refine wp_join_group (fun (dph, ()) m2 => m1 = m2) ?_ ?_
    · rintro _ ⟨dph, ⟨⟩⟩ _ rfl
      refine wp_join_group (fun (lit, ()) m3 =>
        m1 = m3 ∧ (lit.toNat = 2 * chosen.toNat ∨ lit.toNat = 2 * chosen.toNat + 1)) ?_ ?_
      · rintro _ ⟨lit, ⟨⟩⟩ _ ⟨rfl, hlit_eq⟩
        have hnlvl_nat : (BitVec.ofNat 64 s.core.cur_level + (1 : BitVec 64)).toNat =
            s.core.cur_level + 1 := by
          have hte1 : s.core.trail_end ≤ s.core.cur_vars := hcl1.trail_end_le
          obtain ⟨_, hw⟩ := hinv1.witness
          have hcl1_le : s.core.cur_level ≤ s.core.trail_end := hw.cur_level_le
          bv_omega
        fp_steps
        · exact hQ 0#64 s.core.vals s.core.flags s.core.lvl s.core.rsns s.core.trl s.core.trail_pos
            s.core.frame_trail s.core.frame_dec s.core.trail_end s.core.cur_level s.core.unassigned
            s.core.unflushed sc1 m1 hinv1 hll1 hext1 (Or.inl rfl) (fun _ => ⟨rfl, rfl⟩) (by simp)
            hm1
        · have hnlvl_le : s.core.cur_level + 1 ≤ c.max_vars := by c0_bound
          have ⟨hcore_ex, hun, hte_lt, _⟩ := full_decide_preserves_fullCore hinv1 hsc1
            hcl1.flags_len hv_lt hval0 hlit_eq (flags' := s.core.flags)
            (unas' := s.core.unassigned) (unfl' := s.core.unflushed)
          have hte_lt' : s.core.trail_end < s.core.cur_vars := hte_lt
          let nlvl := s.core.cur_level + 1
          let ftrl' := s.core.frame_trail.set nlvl (BitVec.ofNat 32 s.core.trail_end)
          let fdec' := s.core.frame_dec.set nlvl lit
          let s2 : FullState :=
            { core := { s.core with frame_trail := ftrl', frame_dec := fdec', cur_level := nlvl }
              scratch := sc1 }
          have hlen2 : s2.LengthsOk c :=
            ⟨{ hcl1 with
                frame_trail_len := by simp [s2, ftrl', hftrl1]
                frame_dec_len := by simp [s2, fdec', hfdec1] }, hsc1⟩
          have hm2 : (FullMem c s2 ⋆ R) m := by
            have hte_bv : (BitVec.ofNat 64 s.core.trail_end).setWidth 32 =
                BitVec.ofNat 32 s.core.trail_end := by
              apply BitVec.eq_of_toNat_eq
              rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
                Nat.mod_eq_of_lt (by omega : s.core.trail_end < 2 ^ 64),
                Nat.mod_eq_of_lt (by omega : s.core.trail_end < 2 ^ 32)]
            simpa only [s2, ftrl', fdec', nlvl, hnlvl_nat, hte_bv] using hm
          have hng : ¬ (s2.core.cur_vars ≤ lit.toNat / 2 ∨ c.max_vars ≤ s2.core.trail_end ∨
              s2.core.vals[lit.toNat]?.getD 0#8 ≠ 0#8) := by
            change ¬ (s1.core.cur_vars ≤ lit.toNat / 2 ∨ c.max_vars ≤ s1.core.trail_end ∨
              s1.core.vals[lit.toNat]?.getD 0#8 ≠ 0#8)
            simp only [hun, ne_eq, not_true_eq_false, or_false]
            change ¬ (s.core.cur_vars ≤ lit.toNat / 2 ∨ c.max_vars ≤ s.core.trail_end)
            omega
          c0_call hAssign
          refine ⟨c, s2, R, rfl, hlen2, by dsimp [s2, nlvl]; omega, hm2, ?_⟩
          simp only [hng, ↓reduceIte]
          intro flags' unas' unfl' phases' m3 hfl_l hph_l hm3
          have hsc3 : ({ sc1 with phases := phases' } : FullScratch).LengthsOk c :=
            { hsc1 with phases_len := hph_l }
          have ⟨hinv3, _, _, _⟩ := full_decide_preserves_fullCore hinv1 hsc3 hfl_l hv_lt hval0
            hlit_eq (flags' := flags') (unas' := unas') (unfl' := unfl')
          have hnl_ne0 : nlvl ≠ 0 := by dsimp [nlvl]; omega
          have hff : (4294967295 : BitVec 32) = 0xFFFFFFFF#32 := rfl
          have hm3' : (FullMem c
              { core := { s.core with
                  vals := (s.core.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8,
                  flags := flags', lvl := s.core.lvl.set (lit.toNat / 2) (BitVec.ofNat 32 nlvl),
                  rsns := s.core.rsns.set (lit.toNat / 2) 0xFFFFFFFF#32,
                  trl := s.core.trl.set s.core.trail_end lit,
                  trail_pos := s.core.trail_pos.set (lit.toNat / 2)
                    (BitVec.ofNat 32 s.core.trail_end),
                  frame_trail := ftrl', frame_dec := fdec', trail_end := s.core.trail_end + 1,
                  cur_level := nlvl, unassigned := unas', unflushed := unfl' }
                scratch := { sc1 with phases := phases' } } ⋆ R) m3 := by
            simpa only [s2, hnl_ne0, ↓reduceIte, hff] using hm3
          fp_steps
          exact hQ 1#64 _ flags' _ _ _ _ ftrl' fdec' (s.core.trail_end + 1) nlvl unas' unfl'
            { sc1 with phases := phases' } m3 hinv3 hll1 hext1 (Or.inr rfl) (by simp)
            (fun _ => ⟨rfl, rfl⟩) hm3'
      · intro Jlit hJlit; fp_steps
        · exact hJlit ((chosen <<< (1 : Nat)).setWidth 32 ||| 1#32, ()) m1
            ⟨rfl, Or.inr (bv32_dec_lit_odd hch_lt30)⟩
        · exact hJlit ((chosen <<< (1 : Nat)).setWidth 32, ()) m1
            ⟨rfl, Or.inl (bv32_dec_lit_even hch_lt30)⟩
    · intro Jdph hJdph; fp_steps
      · exact hJdph _ m1 rfl
      · exact hJdph _ m1 rfl
      · exact hJdph _ m1 rfl

/-! ## 3. `full_warmup` `Func.wp` proof -/

private def warmupCoreMask (k : FullCoreState) : FullCoreState :=
  { propCoreMask k with
    frame_trail := [], frame_dec := [], cur_level := 0, probing := 0#64 }

private theorem warmup_eq_upd {s st : FullState} (h : AgreesExcept warmupCoreMask s.core st.core)
    (hcl : st.core.cur_level = s.core.cur_level) :
    st =
      { core :=
          { s.core with
            vals := st.core.vals, flags := st.core.flags, lvl := st.core.lvl, rsns := st.core.rsns,
            trl := st.core.trl, trail_pos := st.core.trail_pos, frame_trail := st.core.frame_trail,
            frame_dec := st.core.frame_dec, trail_end := st.core.trail_end,
            propagated := st.core.propagated, probing := st.core.probing,
            unassigned := st.core.unassigned, unflushed := st.core.unflushed, wvec := st.core.wvec,
            arena := st.core.arena, wstk := st.core.wstk, wlen := st.core.wlen,
            wusable := st.core.wusable, fuel := st.core.fuel, confl_type := st.core.confl_type,
            confl_ref := st.core.confl_ref, confl_lit0 := st.core.confl_lit0,
            confl_lit1 := st.core.confl_lit1, oom := st.core.oom }
        scratch := st.scratch } := by
  have h1 := h.get FullCoreState.d_cur; have h2 := h.get FullCoreState.d_val
  have h3 := h.get FullCoreState.cur_vars; have h4 := h.get FullCoreState.arena_len
  have h5 := h.get FullCoreState.arena_garbage; have h6 := h.get FullCoreState.first_reducible
  have h7 := h.get FullCoreState.num_irred; have h8 := h.get FullCoreState.num_redundant
  have h9 := h.get FullCoreState.num_binary; have h10 := h.get FullCoreState.tmp_cnt
  have h11 := h.get FullCoreState.tmp_len; have h12 := h.get FullCoreState.min_clr_len
  have h13 := h.get FullCoreState.min_clr_full; have h14 := h.get FullCoreState.dense_mode
  have h15 := h.get FullCoreState.inconsistent; have h16 := h.get FullCoreState.lit_mark
  have h17 := h.get FullCoreState.mrk; have h18 := h.get FullCoreState.tmp
  have h19 := h.get FullCoreState.min_clr; have h20 := h.get FullCoreState.repr
  have h21 := h.get FullCoreState.min_stk
  cases st with | mk stc stsc =>
  cases s with | mk sc ssc =>
  cases stc; cases sc; simp only at *; subst_vars; rfl

theorem full_warmup_wp (Γ : Env)
    (hNextDec : ∀ args m Q X, fullNextDecVarSpec args m Q X →
      Γ "full_next_dec_var" [i64] [i64] args m Q X)
    (hAssign : ∀ args m Q X, fullAssignSpec args m Q X →
      Γ "full_assign" [i64, i32, i32] [] args m Q X)
    (hProp : ∀ args m Q X, fullPropagateSpec args m Q X →
      Γ "full_propagate" [i64] [i64] args m Q X)
    (hBt : ∀ args m Q X, fullBacktrackSpec args m Q X →
      Γ "full_backtrack" [i64, i64] [] args m Q X) :
    ∀ args m Q X, fullWarmupSpec args m Q X →
      Func.wp Γ full_warmup_body args m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, hdense0, hm, hQ⟩
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  have hret_noop : Q () m :=
    hQ s.core.vals s.core.flags s.core.lvl s.core.rsns s.core.trl s.core.trail_pos
      s.core.frame_trail s.core.frame_dec s.core.trail_end s.core.propagated s.core.probing
      s.core.unassigned s.core.unflushed s.core.wvec s.core.arena s.core.wstk s.core.wlen
      s.core.wusable s.core.fuel s.core.confl_type s.core.confl_ref s.core.confl_lit0
      s.core.confl_lit1 s.core.oom s.scratch m hinv (.refl _) (Nat.le_refl _) rfl rfl
      (fun h => h) hm
  have hcv0 : s.core.cur_vars ≤ c.max_vars := hinv.lengths.core_ok.cur_vars_le
  have hte0 : s.core.trail_end ≤ s.core.cur_vars := hinv.lengths.core_ok.trail_end_le
  obtain ⟨_, hw0⟩ := hinv.witness
  have hcl0_le : s.core.cur_level ≤ s.core.trail_end := hw0.cur_level_le
  fp_nojoin
  · exact hret_noop
  · exact hret_noop
  · have hcl0 : s.core.cur_level = 0 := by c0_bound
    let st0 : FullState := { s with core := { s.core with probing := 1#64 } }
    have hinv0 : FullCoreInv c F0 st0 := hinv.with_probing 1#64
    refine wp_loop_break_group
      (fun (_steps, ()) mb => ∃ st : FullState,
        FullCoreInv c F0 st ∧ AgreesExcept warmupCoreMask s.core st.core ∧
        FullArenaPermEq s.core st.core ∧ st.core.fuel.toNat ≤ s.core.fuel.toNat ∧
        st.scratch.last_learned = s.scratch.last_learned ∧
        st.scratch.extend_len = s.scratch.extend_len ∧ (FullMem c st ⋆ R) mb)
      (fun rem (steps, ()) ml => ∃ st : FullState,
        rem = s.core.cur_vars - steps.toNat ∧ steps.toNat ≤ s.core.cur_vars ∧
        FullCoreInv c F0 st ∧ AgreesExcept warmupCoreMask s.core st.core ∧
        FullArenaPermEq s.core st.core ∧ st.core.fuel.toNat ≤ s.core.fuel.toNat ∧
        st.scratch.last_learned = s.scratch.last_learned ∧
        st.scratch.extend_len = s.scratch.extend_len ∧ (FullMem c st ⋆ R) ml) ?_ ?_ ?_
    · -- Post-loop `B`: `full_backtrack(h, 0ULL); h->probing = 0ULL;`
      rintro _ ⟨_steps, ⟨⟩⟩ mb ⟨st, hst_inv, hag, hperm, hfl, hll, hext, hmb⟩
      fp_steps
      c0_call hBt
      refine ⟨c, F0, st, R, rfl, hst_inv, hmb,
        fun vals' lvl' rsns' trl' tp' te' prop' unas' sc' m1 hinv1 hll1 hext1 hm1 => ?_⟩
      let st1 : FullState :=
        { core := { st.core with
            vals := vals', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
            trail_end := te', propagated := prop', cur_level := min st.core.cur_level 0,
            unassigned := unas' }
          scratch := sc' }
      have hcl1 : st1.core.cur_level = 0 := by simp [st1]
      fp_steps
      let st2 : FullState := { st1 with core := { st1.core with probing := 0#64 } }
      have hinv2 : FullCoreInv c F0 st2 := hinv1.with_probing 0#64
      have hag2 : AgreesExcept warmupCoreMask s.core st2.core :=
        hag.update (fun k => { k with
          vals := vals', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
          trail_end := te', propagated := prop', cur_level := min st.core.cur_level 0,
          unassigned := unas', probing := 0#64 })
      have hst2_eq := warmup_eq_upd hag2 (by dsimp [st2, st1]; rw [Nat.min_zero, hcl0])
      have hinv2' := hinv2
      have hm2' : (FullMem c st2 ⋆ R) m := hm
      have hperm' : FullArenaPermEq s.core st2.core := hperm
      rw [hst2_eq] at hinv2' hm2' hperm'
      exact hQ st2.core.vals st2.core.flags st2.core.lvl st2.core.rsns st2.core.trl
        st2.core.trail_pos st2.core.frame_trail st2.core.frame_dec st2.core.trail_end
        st2.core.propagated st2.core.probing st2.core.unassigned st2.core.unflushed
        st2.core.wvec st2.core.arena st2.core.wstk st2.core.wlen st2.core.wusable
        st2.core.fuel st2.core.confl_type st2.core.confl_ref st2.core.confl_lit0
        st2.core.confl_lit1 st2.core.oom st2.scratch m hinv2' hperm' hfl
        (hll1.trans hll) (hext1.trans hext) (fun _ => rfl) hm2'
    · -- Loop body `L`
      rintro B L rem ⟨steps, ⟨⟩⟩ ml hB ih
        ⟨st, rfl, hst_le, hst_inv, hag, hperm, hfl, hll, hext, hml⟩
      have hcv_eq : st.core.cur_vars = s.core.cur_vars := hag.get FullCoreState.cur_vars
      have hdm_st : st.core.dense_mode = 0#64 := (hag.get FullCoreState.dense_mode).trans hdense0
      have hcv_le := hst_inv.lengths.core_ok.cur_vars_le
      fp_steps
      · have hst_lt : steps.toNat < s.core.cur_vars := by
          have h1 : steps.toNat < st.core.cur_vars % 2 ^ 64 := by assumption
          rw [Nat.mod_eq_of_lt (by omega : st.core.cur_vars < 2 ^ 64)] at h1; omega
        have hst1_nat : (steps + (1 : BitVec 64)).toNat = steps.toNat + 1 := bv64_add1_toNat
          (by omega)
        c0_call hNextDec
        refine ⟨c, st, R, rfl, hst_inv.lengths, hml, fun v sc1 m1 hsc1 hll1 hext1 hv hm1 => ?_⟩
        let st1 : FullState := { st with scratch := sc1 }
        have hinv1 : FullCoreInv c F0 st1 := hst_inv.with_fuel_scratch hsc1
        have hcl1 := hinv1.lengths.core_ok
        have hph1 := hsc1.phases_len
        have hftrl1 : st.core.frame_trail.length = c.max_vars + 1 := hcl1.frame_trail_len
        have hfdec1 : st.core.frame_dec.length = c.max_vars + 1 := hcl1.frame_dec_len
        fp_nojoin
        · exact hB (steps + (1 : BitVec 64), ()) m1
            ⟨st1, hinv1, hag, hperm, hfl, hll1.trans hll, hext1.trans hext, hm1⟩
        · obtain ⟨hv_lt, hval0⟩ := hv.resolve_left hc
          have hv_lt_max : v.toNat < c.max_vars := by omega
          have hv_lt30 : v.toNat < 2 ^ 30 := by omega
          refine wp_join_group (fun (lit, ()) m2 =>
            m1 = m2 ∧ (lit.toNat = 2 * v.toNat ∨ lit.toNat = 2 * v.toNat + 1)) ?_ ?_
          · rintro _ ⟨lit, ⟨⟩⟩ _ ⟨rfl, hlit_eq⟩
            have hte1 : st.core.trail_end ≤ st.core.cur_vars := hcl1.trail_end_le
            obtain ⟨_, hw1⟩ := hinv1.witness
            have hcl1_le : st.core.cur_level ≤ st.core.trail_end := hw1.cur_level_le
            have hnlvl_nat : (BitVec.ofNat 64 st.core.cur_level + (1 : BitVec 64)).toNat =
                st.core.cur_level + 1 := by bv_omega
            fp_steps
            · exact hB (steps + (1 : BitVec 64), ()) m1
                ⟨st1, hinv1, hag, hperm, hfl, hll1.trans hll, hext1.trans hext, hm1⟩
            · have hnlvl_le : st.core.cur_level + 1 ≤ c.max_vars := by c0_bound
              have ⟨_, hun, hte_lt, _⟩ := full_decide_preserves_fullCore hinv1 hsc1 hcl1.flags_len
                hv_lt hval0 hlit_eq (flags' := st.core.flags) (unas' := st.core.unassigned)
                (unfl' := st.core.unflushed)
              have hte_lt' : st.core.trail_end < st.core.cur_vars := hte_lt
              let nlvl := st.core.cur_level + 1
              let ftrl' := st.core.frame_trail.set nlvl (BitVec.ofNat 32 st.core.trail_end)
              let fdec' := st.core.frame_dec.set nlvl lit
              let st2 : FullState :=
                { core := { st.core with
                    frame_trail := ftrl', frame_dec := fdec', cur_level := nlvl }
                  scratch := sc1 }
              have hlen2 : st2.LengthsOk c :=
                ⟨{ hcl1 with
                    frame_trail_len := by simp [st2, ftrl', hftrl1]
                    frame_dec_len := by simp [st2, fdec', hfdec1] }, hsc1⟩
              have hm2 : (FullMem c st2 ⋆ R) m := by
                have hte_bv : (BitVec.ofNat 64 st.core.trail_end).setWidth 32 =
                    BitVec.ofNat 32 st.core.trail_end := by
                  apply BitVec.eq_of_toNat_eq
                  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
                    Nat.mod_eq_of_lt (by omega : st.core.trail_end < 2 ^ 64),
                    Nat.mod_eq_of_lt (by omega : st.core.trail_end < 2 ^ 32)]
                simpa only [st2, ftrl', fdec', nlvl, hnlvl_nat, hte_bv] using hm
              have hng : ¬ (st2.core.cur_vars ≤ lit.toNat / 2 ∨ c.max_vars ≤ st2.core.trail_end ∨
                  st2.core.vals[lit.toNat]?.getD 0#8 ≠ 0#8) := by
                change ¬ (st1.core.cur_vars ≤ lit.toNat / 2 ∨ c.max_vars ≤ st1.core.trail_end ∨
                  st1.core.vals[lit.toNat]?.getD 0#8 ≠ 0#8)
                simp only [hun, ne_eq, not_true_eq_false, or_false]
                change ¬ (st.core.cur_vars ≤ lit.toNat / 2 ∨ c.max_vars ≤ st.core.trail_end)
                omega
              c0_call hAssign
              refine ⟨c, st2, R, rfl, hlen2, by dsimp [st2, nlvl]; omega, hm2, ?_⟩
              simp only [hng, ↓reduceIte]
              intro flags' unas' unfl' phases' m3 hfl_l hph_l hm3
              have hsc3 : ({ sc1 with phases := phases' } : FullScratch).LengthsOk c :=
                { hsc1 with phases_len := hph_l }
              have ⟨hinv3, _, _, _⟩ := full_decide_preserves_fullCore hinv1 hsc3 hfl_l hv_lt hval0
                hlit_eq (flags' := flags') (unas' := unas') (unfl' := unfl')
              have hnl_ne0 : nlvl ≠ 0 := by dsimp [nlvl]; omega
              have hff : (4294967295 : BitVec 32) = 0xFFFFFFFF#32 := rfl
              let st3 : FullState :=
                { core := { st.core with
                    vals := (st.core.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8,
                    flags := flags', lvl := st.core.lvl.set (lit.toNat / 2) (BitVec.ofNat 32 nlvl),
                    rsns := st.core.rsns.set (lit.toNat / 2) 0xFFFFFFFF#32,
                    trl := st.core.trl.set st.core.trail_end lit,
                    trail_pos := st.core.trail_pos.set (lit.toNat / 2)
                      (BitVec.ofNat 32 st.core.trail_end),
                    frame_trail := ftrl', frame_dec := fdec', trail_end := st.core.trail_end + 1,
                    cur_level := nlvl, unassigned := unas', unflushed := unfl' }
                  scratch := { sc1 with phases := phases' } }
              have hm3' : (FullMem c st3 ⋆ R) m3 := by
                simpa only [st3, st2, hnl_ne0, ↓reduceIte, hff] using hm3
              have hag3 : AgreesExcept warmupCoreMask s.core st3.core :=
                hag.update (fun k => { k with
                  vals := st3.core.vals, flags := flags', lvl := st3.core.lvl,
                  rsns := st3.core.rsns, trl := st3.core.trl, trail_pos := st3.core.trail_pos,
                  frame_trail := ftrl', frame_dec := fdec', trail_end := st.core.trail_end + 1,
                  cur_level := nlvl, unassigned := unas', unflushed := unfl' })
              obtain ⟨F_cur, hw3⟩ := hinv3.witness
              c0_call hProp
              refine ⟨c, F0, F_cur, st3, R, rfl, hinv3.lengths, hw3, hdm_st, hm3',
                fun r vals'' flags'' lvl'' rsns'' trl'' tp'' te'' prop'' unas'' unfl''
                  wvec'' arena'' wstk'' wlen'' wu'' fuel'' ctype'' cref'' c0'' c1'' oom''
                  ticks'' wsort'' phases'' m4 hlen4 hw4 _ hperm4 _ hfl4 _ _ _ _ _ hm4 => ?_⟩
              let st4 : FullState :=
                { core := { st3.core with
                    vals := vals'', flags := flags'', lvl := lvl'', rsns := rsns'', trl := trl'',
                    trail_pos := tp'', trail_end := te'', propagated := prop'',
                    unassigned := unas'', unflushed := unfl'', wvec := wvec'', arena := arena'',
                    wstk := wstk'', wlen := wlen'', wusable := wu'', fuel := fuel'',
                    confl_type := ctype'', confl_ref := cref'', confl_lit0 := c0'',
                    confl_lit1 := c1'', oom := oom'' }
                  scratch := { st3.scratch with
                    search_ticks := ticks'', wsort := wsort'', phases := phases'' } }
              have hinv4 : FullCoreInv c F0 st4 := ⟨hlen4, F_cur, hw4⟩
              have hag4 : AgreesExcept warmupCoreMask s.core st4.core :=
                hag3.update (fun k => { k with
                  vals := vals'', flags := flags'', lvl := lvl'', rsns := rsns'', trl := trl'',
                  trail_pos := tp'', trail_end := te'', propagated := prop'',
                  unassigned := unas'', unflushed := unfl'', wvec := wvec'', arena := arena'',
                  wstk := wstk'', wlen := wlen'', wusable := wu'', fuel := fuel'',
                  confl_type := ctype'', confl_ref := cref'', confl_lit0 := c0'',
                  confl_lit1 := c1'', oom := oom'' })
              have hperm4' : FullArenaPermEq s.core st4.core := hperm.trans hperm4
              have hfl4' : st4.core.fuel.toNat ≤ s.core.fuel.toNat := Nat.le_trans hfl4 hfl
              fp_steps
              · exact hB (steps + (1 : BitVec 64), ()) m4 ⟨st4, hinv4, hag4, hperm4', hfl4',
                  hll1.trans hll, hext1.trans hext, hm4⟩
              · exact ih (s.core.cur_vars - (steps + (1 : BitVec 64)).toNat)
                  (steps + (1 : BitVec 64), ()) m4 (by omega)
                  ⟨st4, rfl, by omega, hinv4, hag4, hperm4', hfl4', hll1.trans hll,
                    hext1.trans hext, hm4⟩
          · intro Jlit hJlit; fp_steps
            · exact hJlit ((v <<< (1 : Nat)).setWidth 32 ||| 1#32, ()) m1
                ⟨rfl, Or.inr (bv32_dec_lit_odd hv_lt30)⟩
            · exact hJlit ((v <<< (1 : Nat)).setWidth 32, ()) m1
                ⟨rfl, Or.inl (bv32_dec_lit_even hv_lt30)⟩
      · exact hB (steps, ()) ml ⟨st, hst_inv, hag, hperm, hfl, hll, hext, hml⟩
      · exact hB (steps, ()) ml ⟨st, hst_inv, hag, hperm, hfl, hll, hext, hml⟩
      · exact hB (steps, ()) ml ⟨st, hst_inv, hag, hperm, hfl, hll, hext, hml⟩
    · intro _ L _ hL; fp_steps
      exact hL s.core.cur_vars (0#64, ()) m ⟨st0, by simp, Nat.zero_le _, hinv0,
        (AgreesExcept.refl warmupCoreMask s.core).update (fun k => { k with probing := 1#64 }),
        .refl _, Nat.le_refl _, rfl, rfl, hm⟩

/-! ## 4. `full_rephase` `Func.wp` proof -/

theorem full_rephase_wp (Γ : Env)
    (hBt : ∀ args m Q X, fullBacktrackSpec args m Q X →
      Γ "full_backtrack" [i64, i64] [] args m Q X)
    (hWalk : ∀ args m Q X, fullWalkSpec args m Q X →
      Γ "full_walk" [i64] [] args m Q X)
    (hIlog10 : ∀ args m Q X, fullIlog10Spec args m Q X →
      Γ "full_ilog10" [i64] [i64] args m Q X) :
    ∀ args m Q X, fullRephaseSpec args m Q X →
      Func.wp Γ full_rephase_body args m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, hm, hQ⟩
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  fp_steps
  c0_call hBt
  refine ⟨c, F0, s, R, rfl, hinv, hm,
    fun vals' lvl' rsns' trl' tp' te' prop' unas' sc1 m1 hinv1 hll1 hext1 hm1 => ?_⟩
  let st1 : FullState :=
    { core := { s.core with
        vals := vals', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
        trail_end := te', propagated := prop', cur_level := min s.core.cur_level 0,
        unassigned := unas' }
      scratch := sc1 }
  have hcl1 : min s.core.cur_level 0 = 0 := Nat.min_zero _
  have hcv_le : s.core.cur_vars ≤ c.max_vars := hinv1.lengths.core_ok.cur_vars_le
  fp_nojoin
  let sc2 : FullScratch := { sc1 with rephased := sc1.rephased + 1#64 }
  have hsc2_ok : sc2.LengthsOk c := { hinv1.lengths.scratch_ok with
    walk_vals_len := hinv1.lengths.scratch_ok.walk_vals_len }
  let st2 : FullState := { st1 with scratch := sc2 }
  have hinv2 : FullCoreInv c F0 st2 := hinv1.with_fuel_scratch hsc2_ok
  -- Join `J_sel` after 4-way rephase branch
  refine wp_join_group (fun (_k, ()) m2 => ∃ (fuel' : BitVec 64) (sc3 : FullScratch),
    sc3.LengthsOk c ∧ fuel'.toNat ≤ s.core.fuel.toNat ∧
    sc3.last_learned = s.scratch.last_learned ∧ sc3.extend_len = s.scratch.extend_len ∧
    (FullMem c { core := { st1.core with fuel := fuel' }, scratch := sc3 } ⋆ R) m2) ?_ ?_
  · rintro _ ⟨_k, ⟨⟩⟩ m2 ⟨fuel', sc3, hsc3, hfl3, hll3, hext3, hm2⟩
    -- Copy `ptgt[k] = ph[k]` for `k < cv`
    refine wp_loop_inv
      (fun (k, ()) m3 => ∃ ptgt' : List (BitVec 8),
        k.toNat ≤ s.core.cur_vars ∧ ptgt'.length = c.max_vars ∧
        (FullMem c
          { core := { st1.core with fuel := fuel' }
            scratch := { sc3 with phases_target := ptgt' } } ⋆ R) m3)
      (fun (k, ()) _ => s.core.cur_vars - k.toNat)
      (fun L hL => by
        fp_steps
        exact hL (0#64, ()) m2 ⟨sc3.phases_target, Nat.zero_le _, hsc3.phases_target_len, hm2⟩)
      (fun L (k, ()) m3 ⟨ptgt', hk_le, hpt_len, hm3⟩ ih => ?_)
    have hph3 := hsc3.phases_len
    fp_steps
    · have hk_lt : k.toNat < s.core.cur_vars := by c0_bound
      have hk1 : (k + (1 : BitVec 64)).toNat = k.toNat + 1 := bv64_add1_toNat (by omega)
      exact ih (k + (1 : BitVec 64), ()) m (by dsimp only; omega)
        ⟨ptgt'.set k.toNat (sc3.phases[k.toNat]'(by omega)), by omega, by simp [hpt_len], hm⟩
    · c0_call hIlog10
      intro lg _ _
      fp_steps
      let sc4 : FullScratch := { sc3 with
        phases_target := ptgt', target_assigned := 0#64,
        rephase_limit := sc3.conflicts + 1000#64 + 100#64 * sc3.rephased * lg }
      have hsc4 : sc4.LengthsOk c := { hsc3 with phases_target_len := hpt_len }
      have hinv4 : FullCoreInv c F0 { core := { st1.core with fuel := fuel' }, scratch := sc4 } :=
        hinv1.with_fuel_scratch hsc4
      have hinv4' : FullCoreInv c F0
          { core := { s.core with
              vals := vals', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
              trail_end := te', propagated := prop', cur_level := 0,
              unassigned := unas', fuel := fuel' }
            scratch := sc4 } := by
        simpa only [st1, hcl1] using hinv4
      have hm4' : (FullMem c
          { core := { s.core with
              vals := vals', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
              trail_end := te', propagated := prop', cur_level := 0,
              unassigned := unas', fuel := fuel' }
            scratch := sc4 } ⋆ R) m := by
        have hm' := hm; simp only [st1, hcl1] at hm'; exact hm'
      exact hQ vals' lvl' rsns' trl' tp' te' prop' unas' fuel' sc4 m hinv4' hfl3 hll3 hext3 hm4'
  · intro Jsel hJsel
    -- Inner join `Jbest` for `sel == 0 || sel == 3`
    refine wp_join_group (fun () m0 => m = m0) ?_ ?_
    · rintro _ ⟨⟩ _ rfl
      refine wp_loop_inv
        (fun (k, ()) m3 => ∃ ph' : List (BitVec 8),
          k.toNat ≤ s.core.cur_vars ∧ ph'.length = c.max_vars ∧
          (FullMem c { st2 with scratch := { sc2 with phases := ph' } } ⋆ R) m3)
        (fun (k, ()) _ => s.core.cur_vars - k.toNat)
        (fun L hL => by
          fp_steps; exact hL (0#64, ()) m
            ⟨sc2.phases, Nat.zero_le _, hsc2_ok.phases_len, hm⟩)
        (fun L (k, ()) m3 ⟨ph', hk_le, hph_l, hm3⟩ ih => ?_)
      have hpb_l := hsc2_ok.phases_best_len
      fp_steps
      · have hk_lt : k.toNat < s.core.cur_vars := by c0_bound
        have hk1 : (k + (1 : BitVec 64)).toNat = k.toNat + 1 := bv64_add1_toNat (by omega)
        exact ih (k + (1 : BitVec 64), ()) m (by dsimp only; omega)
          ⟨ph'.set k.toNat (sc2.phases_best[k.toNat]'(by omega)), by omega, by simp [hph_l], hm⟩
      · have hk_lt : k.toNat < s.core.cur_vars := by c0_bound
        have hk1 : (k + (1 : BitVec 64)).toNat = k.toNat + 1 := bv64_add1_toNat (by omega)
        exact ih (k + (1 : BitVec 64), ()) m3 (by dsimp only; omega) ⟨ph', by omega, hph_l, hm3⟩
      · exact hJsel (_, ()) m ⟨s.core.fuel, { sc2 with phases := ph', best_assigned := 0#64 },
          { hsc2_ok with phases_len := hph_l }, Nat.le_refl _, hll1, hext1, hm⟩
    · intro Jbest hJbest
      fp_nojoin
      · exact hJbest () m rfl
      · exact hJbest () m rfl
      · -- Unroll forwarding join `Jelse1` (`jump Jsel`), then join `Jwalk` (`sel == 1 || sel == 4`)
        apply wp_unroll_group; intro _ hJelse1
        refine wp_join_group (fun () m0 => m = m0) ?_ ?_
        · rintro _ ⟨⟩ _ rfl
          c0_call hWalk
          refine ⟨c, F0, st2, R, rfl, hinv2, hm, fun fuel' sc3 m3 hsc3 hfl3 hll3 hext3 hm3 => ?_⟩
          fp_steps
          exact hJsel (_, ()) m3 ⟨fuel', sc3, hsc3, hfl3, hll3.trans hll1, hext3.trans hext1, hm3⟩
        · intro Jwalk hJwalk
          fp_nojoin
          · exact hJwalk () m rfl
          · exact hJwalk () m rfl
          · -- Unroll forwarding join `Jelse2` around `sel == 2` / `else`
            apply wp_unroll_group; intro _ hJelse2
            fp_nojoin
            · -- `sel == 2`: set all `ph[k] = -1`
              refine wp_loop_inv
                (fun (k, ()) m3 => ∃ ph' : List (BitVec 8),
                  k.toNat ≤ s.core.cur_vars ∧ ph'.length = c.max_vars ∧
                  (FullMem c { st2 with scratch := { sc2 with phases := ph' } } ⋆ R) m3)
                (fun (k, ()) _ => s.core.cur_vars - k.toNat)
                (fun L hL => by
                  fp_steps; exact hL (0#64, ()) m
                    ⟨sc2.phases, Nat.zero_le _, hsc2_ok.phases_len, hm⟩)
                (fun L (k, ()) m3 ⟨ph', hk_le, hph_l, hm3⟩ ih => ?_)
              fp_steps
              · have hk_lt : k.toNat < s.core.cur_vars := by c0_bound
                have hk1 : (k + (1 : BitVec 64)).toNat = k.toNat + 1 := bv64_add1_toNat (by omega)
                exact ih (k + (1 : BitVec 64), ()) m (by dsimp only; omega)
                  ⟨ph'.set k.toNat _, by omega, by simp [hph_l], hm⟩
              · fp_steps
                exact hJsel (_, ()) m3 ⟨s.core.fuel, { sc2 with phases := ph' },
                  { hsc2_ok with phases_len := hph_l }, Nat.le_refl _, hll1, hext1, hm3⟩
            · -- `else`: set all `ph[k] = 1`
              refine wp_loop_inv
                (fun (k, ()) m3 => ∃ ph' : List (BitVec 8),
                  k.toNat ≤ s.core.cur_vars ∧ ph'.length = c.max_vars ∧
                  (FullMem c { st2 with scratch := { sc2 with phases := ph' } } ⋆ R) m3)
                (fun (k, ()) _ => s.core.cur_vars - k.toNat)
                (fun L hL => by
                  fp_steps; exact hL (0#64, ()) m
                    ⟨sc2.phases, Nat.zero_le _, hsc2_ok.phases_len, hm⟩)
                (fun L (k, ()) m3 ⟨ph', hk_le, hph_l, hm3⟩ ih => ?_)
              fp_steps
              · have hk_lt : k.toNat < s.core.cur_vars := by c0_bound
                have hk1 : (k + (1 : BitVec 64)).toNat = k.toNat + 1 := bv64_add1_toNat (by omega)
                exact ih (k + (1 : BitVec 64), ()) m (by dsimp only; omega)
                  ⟨ph'.set k.toNat _, by omega, by simp [hph_l], hm⟩
              · fp_steps
                exact hJsel (_, ()) m3 ⟨s.core.fuel, { sc2 with phases := ph' },
                  { hsc2_ok with phases_len := hph_l }, Nat.le_refl _, hll1, hext1, hm3⟩

/-! ## 5. `full_restart` `Func.wp` proof -/

theorem full_restart_wp (Γ : Env)
    (hNextDec : ∀ args m Q X, fullNextDecVarSpec args m Q X →
      Γ "full_next_dec_var" [i64] [i64] args m Q X)
    (hBt : ∀ args m Q X, fullBacktrackSpec args m Q X →
      Γ "full_backtrack" [i64, i64] [] args m Q X) :
    ∀ args m Q X, fullRestartSpec args m Q X →
      Func.wp Γ full_restart_body args m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, hm, hQ⟩
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  fp_steps
  let sc0 : FullScratch := { s.scratch with restarts := s.scratch.restarts + 1#64 }
  have hsc0 : sc0.LengthsOk c := { hinv.lengths.scratch_ok with
    walk_vals_len := hinv.lengths.scratch_ok.walk_vals_len }
  let s0 : FullState := { s with scratch := sc0 }
  have hinv0 : FullCoreInv c F0 s0 := hinv.with_fuel_scratch hsc0
  c0_call hNextDec
  refine ⟨c, s0, R, rfl, hinv0.lengths, hm, fun nv sc1 m1 hsc1 hll1 hext1 _ hm1 => ?_⟩
  let s1 : FullState := { s with scratch := sc1 }
  change (FullMem c s1 ⋆ R) m1 at hm1
  have hinv1 : FullCoreInv c F0 s1 := hinv.with_fuel_scratch hsc1
  have hcl1 := hinv1.lengths.core_ok
  have hcv_le : s.core.cur_vars ≤ c.max_vars := hcl1.cur_vars_le
  have hcv_le1 : s1.core.cur_vars ≤ c.max_vars := hcl1.cur_vars_le
  have hte_le : s.core.trail_end ≤ s.core.cur_vars := hcl1.trail_end_le
  have hte_le1 : s1.core.trail_end ≤ s1.core.cur_vars := hcl1.trail_end_le
  have hfdec_l : s.core.frame_dec.length = c.max_vars + 1 := hcl1.frame_dec_len
  have hfdec_l1 : s1.core.frame_dec.length = c.max_vars + 1 := hcl1.frame_dec_len
  have hsc_l : s1.scratch.score.length = c.max_vars := hsc1.score_len
  have hqs_l : s1.scratch.q_stamp.length = c.max_vars := hsc1.q_stamp_len
  obtain ⟨_, hw1⟩ := hinv1.witness
  have hcl_le : s.core.cur_level ≤ s.core.trail_end := hw1.cur_level_le
  have hcl_le1 : s1.core.cur_level ≤ s1.core.trail_end := hw1.cur_level_le
  fp_nojoin
  refine wp_join_group (fun (reuse, ()) m2 => reuse.toNat ≤ s.core.cur_level ∧ m1 = m2) ?_ ?_
  · rintro _ ⟨reuse, ⟨⟩⟩ _ ⟨hre_le, rfl⟩
    c0_call hBt
    refine ⟨c, F0, s1, R, rfl, hinv1, hm1,
      fun vals' lvl' rsns' trl' tp' te' prop' unas' sc2 m3 hinv3 hll3 hext3 hm3 => ?_⟩
    fp_steps
    exact hQ vals' lvl' rsns' trl' tp' te' prop' (min s.core.cur_level reuse.toNat) unas' sc2 m3
      hinv3 (Nat.min_le_left _ _) (hll3.trans hll1) (hext3.trans hext1) hm3
  · intro Jre hJre; fp_nojoin
    · -- `nv < cur_vars ∧ cur_level > 0`: step `Jif`, dispatch `stable`, unroll break block to `L`
      have hnv_lt : nv.toNat < s.core.cur_vars := by
        have h1 : nv.toNat < s1.core.cur_vars % 2 ^ 64 := by assumption
        change nv.toNat < s.core.cur_vars % 2 ^ 64 at h1
        rw [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)] at h1; exact h1
      fp_steps
      · -- `stable ≠ 0`: score-based trail reuse
        refine wp_loop_group
          (fun rem (reuse, ()) ml =>
            rem = s.core.cur_level - reuse.toNat ∧ reuse.toNat ≤ s.core.cur_level ∧ m1 = ml)
          ?_ ?_
        · rintro L rem ⟨reuse, ⟨⟩⟩ _ ih ⟨rfl, hre_le, rfl⟩
          fp_steps
          · exact hJre (reuse, ()) m1 ⟨hre_le, rfl⟩
          · exact hJre (reuse, ()) m1 ⟨hre_le, rfl⟩
          · have hre_lt : reuse.toNat < s.core.cur_level := by
              have h1 : reuse.toNat < s1.core.cur_level % 2 ^ 64 := by assumption
              change reuse.toNat < s.core.cur_level % 2 ^ 64 at h1
              rw [Nat.mod_eq_of_lt (by omega : s.core.cur_level < 2 ^ 64)] at h1; exact h1
            have hre1 : (reuse + (1 : BitVec 64)).toNat = reuse.toNat + 1 := bv64_add1_toNat
              (by omega)
            exact ih _ (reuse + (1 : BitVec 64), ()) m1 (by omega) ⟨rfl, by omega, rfl⟩
          · exact hJre (reuse, ()) m1 ⟨hre_le, rfl⟩
        · intro L hL; fp_steps; exact hL s.core.cur_level (0#64, ()) m1
            ⟨by simp, Nat.zero_le _, rfl⟩
      · -- `stable == 0`: VMTF stamp-based trail reuse
        refine wp_loop_group
          (fun rem (reuse, ()) ml =>
            rem = s.core.cur_level - reuse.toNat ∧ reuse.toNat ≤ s.core.cur_level ∧ m1 = ml)
          ?_ ?_
        · rintro L rem ⟨reuse, ⟨⟩⟩ _ ih ⟨rfl, hre_le, rfl⟩
          fp_steps
          · exact hJre (reuse, ()) m1 ⟨hre_le, rfl⟩
          · exact hJre (reuse, ()) m1 ⟨hre_le, rfl⟩
          · have hre_lt : reuse.toNat < s.core.cur_level := by
              have h1 : reuse.toNat < s1.core.cur_level % 2 ^ 64 := by assumption
              change reuse.toNat < s.core.cur_level % 2 ^ 64 at h1
              rw [Nat.mod_eq_of_lt (by omega : s.core.cur_level < 2 ^ 64)] at h1; exact h1
            have hre1 : (reuse + (1 : BitVec 64)).toNat = reuse.toNat + 1 := bv64_add1_toNat
              (by omega)
            exact ih _ (reuse + (1 : BitVec 64), ()) m1 (by omega) ⟨rfl, by omega, rfl⟩
          · exact hJre (reuse, ()) m1 ⟨hre_le, rfl⟩
        · intro L hL; fp_steps; exact hL s.core.cur_level (0#64, ()) m1
            ⟨by simp, Nat.zero_le _, rfl⟩
    · exact hJre (0#64, ()) m1 ⟨Nat.zero_le _, rfl⟩
    · exact hJre (0#64, ()) m1 ⟨Nat.zero_le _, rfl⟩

end LeanQbe.T.Examples.Kissat.Full
