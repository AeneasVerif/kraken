/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S1SweepDense
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S1Spec
import LeanQbe.T.Examples.Kissat.FullM6SweepProofEls
import LeanQbe.T.Examples.Kissat.FullDenseWatchLemmas
import LeanQbe.T.Examples.Kissat.FullCongLemmas1
import LeanQbe.T.Examples.Kissat.FullReduceLemmas1
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Fidelity Step 13 Shard S1-A Proofs — Part 2a (`full_m6_els_ar` Helpers)

Parametric `(Γ : Env)` helpers (`public section`, `0` `@[expose]` on theorems/lemmas, `0`
`import all`, `<= 100` cols, `< 1,400` LOC, every theorem `<= 420` lines) supporting
`full_m6_els_ar_s13_wp` (`step13ElsArSpec`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S1

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM6Sweep
open LeanQbe.T.Examples.Kissat.FullM6Sweep.M6ElsBv
open Kraken.Bedrock2.Test

open scoped FullArenaTactics FullM6Sweep.M6ElsBv

/-! ## 1. `FullDenseInvW`, `S13ElsArOut`, and `S13ElsLitMap` Helpers -/

structure S13ElsArOut (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s sR : FullState) : Prop where
  dinv : FullDenseInvW c F0 F_cur sR
  cv : sR.core.cur_vars = s.core.cur_vars
  fuel : sR.core.fuel = s.core.fuel
  repr : FullCongReprInv F_cur (2 * s.core.cur_vars) sR.core.repr
  tmk : sR.scratch.tarjan_mark = s.scratch.tarjan_mark
  trh : sR.scratch.tarjan_reach = s.scratch.tarjan_reach
  scr : sR.scratch.scratch_buf = s.scratch.scratch_buf
  ws1 : sR.scratch.work_stk1 = s.scratch.work_stk1
  ws2 : sR.scratch.work_stk2 = s.scratch.work_stk2
  gu : sR.scratch.glue_used = s.scratch.glue_used

theorem s13_elsArOut_init {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hinv : FullDenseInvW c F0 F_cur s)
    (hrep : FullCongReprInv F_cur (2 * s.core.cur_vars) s.core.repr) :
    S13ElsArOut c F0 F_cur s s :=
  ⟨hinv, rfl, rfl, hrep, rfl, rfl, rfl, rfl, rfl, rfl⟩

structure S13ElsLitMap (c : FullCfg) (s : FullState) (lm : List (BitVec 8))
    (tmp : List (BitVec 32)) (nsz : Nat) : Prop where
  lm_len : lm.length = 2 * c.max_vars
  tmp_len : tmp.length = c.max_vars
  cv_le : s.core.cur_vars ≤ c.max_vars
  nsz_le : nsz ≤ s.core.cur_vars
  tmp_lt : ∀ j < nsz, (tmp[j]?.getD 0#32).toNat < 2 * s.core.cur_vars
  nodup : ((tmp.take nsz).map fun x => x.toNat / 2).Nodup
  map : ∀ l < 2 * c.max_vars,
    lm[l]?.getD 0#8 = if decide (∃ j < nsz, (tmp[j]?.getD 0#32).toNat = l) then 1#8 else 0#8

private theorem nodup_nat_lt_len :
    ∀ {N : Nat} {xs : List Nat}, xs.Nodup → (∀ x ∈ xs, x < N) → xs.length ≤ N
  | 0, xs, _, hlt => by
    cases xs with
    | nil => exact Nat.zero_le 0
    | cons x _ => exfalso; have := hlt x List.mem_cons_self; omega
  | M + 1, xs, hnd, hlt => by
    have hnd' : (xs.erase M).Nodup := hnd.erase M
    have hlt' : ∀ x ∈ xs.erase M, x < M := by
      intro x hx
      have hxm : x ∈ xs := List.mem_of_mem_erase hx
      have hne : x ≠ M := fun heq => by
        subst heq; exact absurd hx (List.Nodup.not_mem_erase hnd)
      have := hlt x hxm; omega
    have ih := nodup_nat_lt_len hnd' hlt'
    by_cases hm : M ∈ xs
    · have hl := List.length_erase_of_mem hm; omega
    · rw [List.erase_of_not_mem hm] at ih; omega

private theorem list_take_set_succ {α : Type _} {xs : List α} {n : Nat} (hn : n < xs.length)
    {x : α} : (xs.set n x).take (n + 1) = xs.take n ++ [x] := by
  apply List.ext_getElem
  · simp [List.length_take, List.length_set]; omega
  · intro i hi1 _
    simp only [List.length_take, List.length_set] at hi1
    have hi : i < n + 1 := by omega
    rw [List.getElem_take]
    by_cases hin : i < n
    · rw [List.getElem_set_ne (by omega), List.getElem_append_left (by
        rw [List.length_take]; omega), List.getElem_take]
    · have hie : i = n := by omega
      subst hie
      rw [List.getElem_set_self (by rw [List.length_set]; exact hn),
        List.getElem_append_right (by rw [List.length_take]; omega)]
      simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hn)]

theorem s13_elsLitMap_init {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hinv : FullDenseInvW c F0 F_cur s) :
    S13ElsLitMap c s s.core.lit_mark s.core.tmp 0 :=
  ⟨hinv.1.core_ok.lit_mark_len, hinv.1.core_ok.tmp_len_arr,
   hinv.1.core_ok.cur_vars_le, Nat.zero_le _,
   (fun _ hj => by cases hj), by simp,
   fun l hl => by
     rw [decide_eq_false (by intro ⟨j, hj, _⟩; exact Nat.not_lt_zero j hj)]
     simpa using hinv.2.2.1.2 l hl⟩

theorem s13_elsLitMap_push {c : FullCfg} {s : FullState}
    {lm : List (BitVec 8)} {tmp : List (BitVec 32)} {nsz : Nat}
    (h : S13ElsLitMap c s lm tmp nsz) {rx : BitVec 32}
    (hrx_lt : rx.toNat < 2 * s.core.cur_vars)
    (h0 : lm[rx.toNat]?.getD 0#8 = 0#8)
    (h1 : lm[(rx ^^^ 1#32).toNat]?.getD 0#8 = 0#8) :
    nsz < c.max_vars ∧
    S13ElsLitMap c s (lm.set rx.toNat 1#8) (tmp.set nsz rx) (nsz + 1) := by
  rcases h with ⟨hlm, htmp, hcv, hnsz, hlt, hnd, hmap⟩
  have hrx1 : (rx ^^^ 1#32).toNat = rx.toNat ^^^ 1 := by simp
  have hnot_var : rx.toNat / 2 ∉ (tmp.take nsz).map (fun x => x.toNat / 2) := by
    intro hmem
    rw [List.mem_map] at hmem; obtain ⟨x, hx, hxv⟩ := hmem
    rw [List.mem_iff_getElem] at hx; obtain ⟨j, hj, rfl⟩ := hx
    have hj' : j < nsz := by simp only [List.length_take] at hj; omega
    rw [List.getElem_take] at hxv
    have hx_eq : (tmp[j]?.getD 0#32).toNat = (tmp[j]'(by omega)).toNat := by
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    have hcases : (tmp[j]?.getD 0#32).toNat = rx.toNat ∨
        (tmp[j]?.getD 0#32).toNat = rx.toNat ^^^ 1 := by
      rw [show rx.toNat ^^^ 1 = litNeg rx.toNat from rfl, litNeg_eq]; split <;> omega
    rcases hcases with he | he
    · have hl := hmap rx.toNat (by omega)
      rw [decide_eq_true ⟨j, hj', he⟩] at hl; simp only [ite_true] at hl
      rw [h0] at hl; cases hl
    · have hl := hmap (rx.toNat ^^^ 1) (by omega)
      rw [decide_eq_true ⟨j, hj', he⟩] at hl; simp only [ite_true] at hl
      rw [← hrx1, h1] at hl; cases hl
  have hlen_take : ((tmp.take nsz).map fun x => x.toNat / 2).length = nsz := by
    simp [List.length_take]; omega
  have hpig : nsz + 1 ≤ s.core.cur_vars := by
    have hnd' : (rx.toNat / 2 :: (tmp.take nsz).map fun x => x.toNat / 2).Nodup :=
      List.nodup_cons.mpr ⟨hnot_var, hnd⟩
    have hlt' : ∀ v ∈ rx.toNat / 2 :: (tmp.take nsz).map fun x => x.toNat / 2,
        v < s.core.cur_vars := by
      intro v hv; rcases List.mem_cons.mp hv with rfl | hm
      · omega
      · rw [List.mem_map] at hm; obtain ⟨x, hx, rfl⟩ := hm
        rw [List.mem_iff_getElem] at hx; obtain ⟨j, hj, rfl⟩ := hx
        have hj' : j < nsz := by simp only [List.length_take] at hj; omega
        rw [List.getElem_take]
        have := hlt j hj'
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at this; omega
    have hl := nodup_nat_lt_len hnd' hlt'
    simp only [List.length_cons, hlen_take] at hl; exact hl
  have hnsz_mx : nsz < c.max_vars := by omega
  refine ⟨hnsz_mx, by simp [hlm], by simp [htmp], hcv, hpig, ?_, ?_, ?_⟩
  · intro j hj
    by_cases hjn : j = nsz
    · subst hjn; rw [List.getElem?_set_self (by omega), Option.getD_some]; exact hrx_lt
    · rw [List.getElem?_set_ne (Ne.symm hjn)]; exact hlt j (by omega)
  · rw [list_take_set_succ (by omega), List.map_append, List.map_singleton,
      List.nodup_append]
    refine ⟨hnd, by simp, fun a ha b hb => ?_⟩
    simp only [List.mem_singleton] at hb; subst hb; rintro rfl; exact hnot_var ha
  · intro l hl
    by_cases hlx : l = rx.toNat
    · subst hlx
      rw [List.getElem?_set_self (by omega), Option.getD_some,
        decide_eq_true ⟨nsz, by omega, by
          rw [List.getElem?_set_self (by omega), Option.getD_some]⟩]
      rfl
    · rw [List.getElem?_set_ne (Ne.symm hlx)]
      have hmem_iff : (∃ j < nsz + 1, ((tmp.set nsz rx)[j]?.getD 0#32).toNat = l) ↔
          (∃ j < nsz, (tmp[j]?.getD 0#32).toNat = l) := by
        constructor
        · rintro ⟨j, hj, hjl⟩
          by_cases hjn : j = nsz
          · subst hjn; rw [List.getElem?_set_self (by omega), Option.getD_some] at hjl
            exact absurd hjl.symm hlx
          · rw [List.getElem?_set_ne (Ne.symm hjn)] at hjl; exact ⟨j, by omega, hjl⟩
        · rintro ⟨j, hj, hjl⟩
          exact ⟨j, by omega, by rw [List.getElem?_set_ne (by omega)]; exact hjl⟩
      rw [hmap l hl]; simp only [hmem_iff]

theorem s13_els_loop3_step {lm : List (BitVec 8)} {tmp : List (BitVec 32)}
    {nsz k mcv2 : Nat} (hk : k < nsz) (htmp_lt : tmp.length = mcv2 / 2) (hnsz_le : nsz ≤ mcv2 / 2)
    (hcov : ∀ l < mcv2, lm[l]?.getD 0#8 ≠ 0#8 →
      ∃ j, k ≤ j ∧ j < nsz ∧ (tmp[j]?.getD 0#32).toNat = l) :
    ∀ l < mcv2, (lm.set (tmp[k]'(by omega)).toNat 0#8)[l]?.getD 0#8 ≠ 0#8 →
      ∃ j, k + 1 ≤ j ∧ j < nsz ∧ (tmp[j]?.getD 0#32).toNat = l := by
  intro l hl hne
  have htk : k < tmp.length := by omega
  by_cases hlt : l = (tmp[k]'htk).toNat
  · subst hlt
    by_cases hbd : (tmp[k]'htk).toNat < lm.length
    · rw [List.getElem?_set_self hbd, Option.getD_some] at hne; exact absurd rfl hne
    · rw [List.set_eq_of_length_le (by omega), List.getElem?_eq_none (by omega),
        Option.getD_none] at hne; exact absurd rfl hne
  · rw [List.getElem?_set_ne (Ne.symm hlt)] at hne
    obtain ⟨j, hkj, hj, hjl⟩ := hcov l hl hne
    have hjk : j ≠ k := by
      intro heq; subst heq; rw [List.getElem?_eq_getElem htk, Option.getD_some] at hjl
      exact hlt hjl.symm
    exact ⟨j, by omega, hj, hjl⟩

theorem s13_bv8_zext32_eq0_iff (v : BitVec 8) :
    v.setWidth 32 = 0#32 ↔ v = 0#8 := by
  constructor <;> intro h
  · apply BitVec.eq_of_toNat_eq
    have ht := congrArg BitVec.toNat h
    simpa [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := v.isLt; omega : v.toNat < 2 ^ 32)]
      using ht
  · subst h; rfl

theorem s13_entails_clause_subst {f : CNF Nat} {cs cs' : List Nat}
    (hmap : ∀ l ∈ cs, ∃ l' ∈ cs', LitEquiv f l l')
    (hc : f.EntailsClause (cnfClause cs)) : f.EntailsClause (cnfClause cs') := by
  rw [CNF.entails_clause_def] at hc ⊢
  intro α hα
  have h1 := (clauseEvalVal_iff α _).mpr (hc α hα)
  rw [clauseEvalVal, List.any_eq_true] at h1
  obtain ⟨l, hl, hsat⟩ := h1
  obtain ⟨l', hl', heq⟩ := hmap l hl
  refine (clauseEvalVal_iff α _).mp ?_
  rw [clauseEvalVal, List.any_eq_true]
  exact ⟨l', hl', by rw [← litEquiv_eval hα heq]; exact hsat⟩

theorem s13_unsat_of_nil_entails {f : CNF Nat}
    (hc : f.EntailsClause (cnfClause [])) : f.Unsat :=
  m6_unsat_of_nil_entails hc

theorem s13_denseInvW_set_oom {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hinv : FullDenseInvW c F0 F_cur s) :
    FullDenseInvW c F0 F_cur { s with core := { s.core with oom := 1#64 } } :=
  ⟨⟨{ hinv.1.core_ok with vals_len := hinv.1.core_ok.vals_len }, hinv.1.scratch_ok⟩,
   { hinv.2.1 with
     arena := { hinv.2.1.arena with len_ok := hinv.2.1.arena.len_ok }
     watches := hinv.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) },
   hinv.2.2.1, hinv.2.2.2.1, hinv.2.2.2.2.1, hinv.2.2.2.2.2.1, hinv.2.2.2.2.2.2⟩

private theorem s13_arenaVarsNodup_of_eq {s s' : FullState} (h : FullArenaVarsNodup s)
    (har : s'.core.arena = s.core.arena) (hal : s'.core.arena_len = s.core.arena_len) :
    FullArenaVarsNodup s' := by
  unfold FullArenaVarsNodup fullArenaClauseRefs fullArenaClauseRefsCore
    fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
    fullArenaClauseLits fullArenaClauseLitsCore fullArenaClauseSizeCore at h ⊢
  rw [har, hal]; exact h

theorem s13_denseInvW_set_lm_clear {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hinv : FullDenseInvW c F0 F_cur s)
    {lm' : List (BitVec 8)} {tmp' : List (BitVec 32)}
    (hlm : lm'.length = 2 * c.max_vars) (htmp : tmp'.length = c.max_vars)
    (hclear : ∀ l < 2 * c.max_vars, lm'[l]?.getD 0#8 = 0#8) :
    FullDenseInvW c F0 F_cur
      { s with core := { s.core with lit_mark := lm', tmp := tmp' } } :=
  ⟨⟨{ hinv.1.core_ok with lit_mark_len := hlm, tmp_len_arr := htmp }, hinv.1.scratch_ok⟩,
   { hinv.2.1 with
     arena := { hinv.2.1.arena with len_ok := hinv.2.1.arena.len_ok }
     watches := hinv.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) },
   ⟨hinv.2.2.1.1, hclear⟩, s13_arenaVarsNodup_of_eq hinv.2.2.2.1 rfl rfl,
   hinv.2.2.2.2.1, hinv.2.2.2.2.2.1, hinv.2.2.2.2.2.2⟩

theorem s13_denseInvW_after_addBin {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hinv : FullDenseInvW c F0 F_cur s)
    {vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec' wstk' wlen' wu' nb' oom' inc'
      phases' wsort'}
    (hlen' : ({ s with
      core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                            trl := trl', trail_pos := tp', trail_end := te',
                            unassigned := unass', unflushed := unfl', wvec := wvec',
                            wstk := wstk', wlen := wlen', wusable := wu', num_binary := nb',
                            oom := oom', inconsistent := inc' }
      scratch := { s.scratch with phases := phases', wsort := wsort' } } : FullState).LengthsOk c)
    (hw' : FullWitnessInv c F0 F_cur
      { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                    trl := trl', trail_pos := tp', trail_end := te',
                    unassigned := unass', unflushed := unfl', wvec := wvec',
                    wstk := wstk', wlen := wlen', wusable := wu', num_binary := nb',
                    oom := oom', inconsistent := inc' }) :
    FullDenseInvW c F0 F_cur
      { s with
        core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                              trl := trl', trail_pos := tp', trail_end := te',
                              unassigned := unass', unflushed := unfl', wvec := wvec',
                              wstk := wstk', wlen := wlen', wusable := wu', num_binary := nb',
                              oom := oom', inconsistent := inc' }
        scratch := { s.scratch with phases := phases', wsort := wsort' } } :=
  ⟨hlen', hw', hinv.2.2.1, s13_arenaVarsNodup_of_eq hinv.2.2.2.1 rfl rfl,
   ⟨fun i hi => hinv.2.2.2.2.1.1 i hi, hinv.2.2.2.2.1.2⟩,
   hinv.2.2.2.2.2.1, hinv.2.2.2.2.2.2⟩

theorem s13_denseInvW_markGarb {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hinv : FullDenseInvW c F0 F_cur s)
    {cref : Nat} (href : cref ∈ fullArenaClauseRefs s) (ag' : BitVec 64) :
    let s' : FullState :=
      { s with core :=
        { s.core with
          arena := s.core.arena.set cref (fullArenaHdr s cref ||| 0x00080000#32)
          arena_garbage := ag' } }
    FullDenseInvW c F0 F_cur s' ∧ fullArenaClauseRefs s' = fullArenaClauseRefs s := by
  intro s'
  have hcl := hinv.1.core_ok; have hw := hinv.2.1; have hcl0 := hinv.2.2.2.2.2.1
  have hmg := hw.arena.markGarb hcl href ag'
  have hrefs : fullArenaClauseRefs s' = fullArenaClauseRefs s := hmg.1
  have hlen' : s'.LengthsOk c :=
    ⟨{ hcl with arena_len_arr := by simp [s', hcl.arena_len_arr] }, hinv.1.scratch_ok⟩
  have hnd' : FullArenaVarsNodup s' :=
    FullArenaVarsNodup.of_markGarb ⟨hinv.1, F_cur, hw⟩ hinv.2.2.2.1 href ag'
  have hno_rsn : ∀ idx < s.core.trail_end,
      s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 :=
    fun idx hidx => hw.level0_rsn_none idx hidx (by have := hw.lvl_le idx hidx; omega)
  have hw' : FullWitnessInv c F0 F_cur s'.core :=
    { hw with
      arena := hmg.2
      watches := hw.watches.with_wstk rfl rfl rfl rfl rfl
        fun r hr => by change r ∈ fullArenaClauseRefs s'; rw [hrefs]; exact hr
      reason_inv := fun idx hidx hne => absurd (hno_rsn idx hidx) hne
      reason_lit_mem := fun idx hidx hne _ => absurd (hno_rsn idx hidx) hne }
  exact ⟨⟨hlen', hw', hinv.2.2.1, hnd',
    FullExtScratchOk.of_pres hinv.2.2.2.2.1 ⟨rfl, rfl⟩ (fun r hr => hrefs ▸ hr),
    hcl0, hinv.2.2.2.2.2.2⟩, hrefs⟩

private theorem s13_denseInvW_watchPush {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hinv : FullDenseInvW c F0 F_cur s)
    {rl w0 w1 : BitVec 32} {ok : Bool}
    {wvec' wstk' : List (BitVec 32)} {wlen' : Nat} {wu' : BitVec 64} {wsort' : List (BitVec 32)}
    (hsok' : ({ s with
      core := { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' }
      scratch := { s.scratch with wsort := wsort' } } : FullState).LengthsOk c)
    (hlay' : WatchStackLayout
      { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' })
    (hflag : (w0 &&& 0x80000000#32) = 0#32) (hsz : 3 ≤ w0.toNat)
    (hlt : w1.toNat < 0x80000000) (href : w1.toNat ∈ fullArenaClauseRefs s)
    (hother : ∀ l < 2 * s.core.cur_vars, l ≠ rl.toNat →
      fullWatchSizeCore { s.core with wvec := wvec', wstk := wstk', wlen := wlen',
                                      wusable := wu' } l = fullWatchSize s l ∧
      ∀ k < fullWatchSize s l,
        wstk'[fullWatchOffCore { s.core with wvec := wvec', wstk := wstk', wlen := wlen',
                                             wusable := wu' } l + k]? =
          s.core.wstk[fullWatchOff s l + k]?)
    (hok_t : ok = true →
      rl.toNat < 2 * s.core.cur_vars ∧
      fullWatchSizeCore { s.core with wvec := wvec', wstk := wstk', wlen := wlen',
                                      wusable := wu' } rl.toNat =
        fullWatchSize s rl.toNat + 2 ∧
      (∀ k < fullWatchSize s rl.toNat,
        wstk'[fullWatchOffCore { s.core with wvec := wvec', wstk := wstk', wlen := wlen',
                                             wusable := wu' } rl.toNat + k]? =
          s.core.wstk[fullWatchOff s rl.toNat + k]?) ∧
      wstk'[fullWatchOffCore { s.core with wvec := wvec', wstk := wstk', wlen := wlen',
                                           wusable := wu' } rl.toNat +
        fullWatchSize s rl.toNat]? = some w0 ∧
      wstk'[fullWatchOffCore { s.core with wvec := wvec', wstk := wstk', wlen := wlen',
                                           wusable := wu' } rl.toNat +
        fullWatchSize s rl.toNat + 1]? = some w1)
    (hok_f : ok = false → rl.toNat < 2 * s.core.cur_vars →
      fullWatchSizeCore { s.core with wvec := wvec', wstk := wstk', wlen := wlen',
                                      wusable := wu' } rl.toNat =
        fullWatchSize s rl.toNat ∧
      ∀ k < fullWatchSize s rl.toNat,
        wstk'[fullWatchOffCore { s.core with wvec := wvec', wstk := wstk', wlen := wlen',
                                             wusable := wu' } rl.toNat + k]? =
          s.core.wstk[fullWatchOff s rl.toNat + k]?) :
    FullDenseInvW c F0 F_cur
      { s with
        core := { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' }
        scratch := { s.scratch with wsort := wsort' } } := by
  have hw := hinv.2.1
  have hwat' : ModeWatchesInv F_cur
      { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' } :=
    fullWatchPush_preserves_modeWatchesInv (cnt := 2#32) hw.watches hlay' rfl rfl (fun _ r => r)
      (fun hc => absurd (hc ▸ rfl : (1 : Nat) = 2) (by decide))
      (fun _ => ⟨hflag, fun _ => hsz, hlt, href⟩)
      hother (fun ht => by
        obtain ⟨h1, h2, h3, h4, h5⟩ := hok_t ht
        exact ⟨h1, Or.inr (by decide), h2, h3, h4, fun _ => h5⟩)
      hok_f
  exact ⟨hsok', { hw with arena := { hw.arena with len_ok := hw.arena.len_ok }, watches := hwat' },
    hinv.2.2.1, s13_arenaVarsNodup_of_eq hinv.2.2.2.1 rfl rfl,
    hinv.2.2.2.2.1, hinv.2.2.2.2.2.1, hinv.2.2.2.2.2.2⟩

private theorem s13_lits_eq_of_hold {ar1 ar2 : List (BitVec 32)} {cr sz : Nat}
    (hb1 : cr + 3 + sz ≤ ar1.length) (hb2 : cr + 3 + sz ≤ ar2.length)
    (h : ∀ j < sz, ar2[cr + 3 + j]? = ar1[cr + 3 + j]?) :
    ((ar2.drop (cr + 3)).take sz).map BitVec.toNat =
      ((ar1.drop (cr + 3)).take sz).map BitVec.toNat := by
  apply List.ext_getElem
  · simp [List.length_take, List.length_drop]; omega
  · intro j hj1 _; simp only [List.length_map, List.length_take, List.length_drop] at hj1
    have hj : j < sz := by omega
    simp only [List.getElem_map, List.getElem_take, List.getElem_drop]
    have hq := h j hj
    rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at hq
    exact congrArg BitVec.toNat (Option.some.inj hq)

private theorem s13_denseInvW_replaceSameLen {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hinv : FullDenseInvW c F0 F_cur s)
    {cref : Nat} (href : cref ∈ fullArenaClauseRefs s) (_hng : fullArenaClauseGarb s cref = false)
    {arena' : List (BitVec 32)} (har_len : arena'.length = c.arena_cap)
    (hout : ∀ i, i < cref + 3 ∨ cref + 3 + fullArenaClauseSize s cref ≤ i →
      arena'[i]? = s.core.arena[i]?)
    (hlits_lt' : ∀ l ∈ fullArenaClauseLits { s with core := { s.core with arena := arena' } } cref,
      l < 2 * s.core.cur_vars)
    (hnd_cr' : ((fullArenaClauseLits { s with core := { s.core with arena := arena' } } cref).map
      (· / 2)).Nodup)
    (hent' : (cnfOfClauses F_cur).EntailsClause
      (cnfClause (fullArenaClauseLits { s with core := { s.core with arena := arena' } } cref))) :
    let s' := { s with core := { s.core with arena := arena' } }
    FullDenseInvW c F0 F_cur s' ∧ fullArenaClauseRefs s' = fullArenaClauseRefs s := by
  intro s'
  have hcl := hinv.1.core_ok; have hw := hinv.2.1; have hcl0 := hinv.2.2.2.2.2.1
  let old_sz := fullArenaClauseSizeCore s.core cref
  have hwf := hw.arena.refs_wf cref href
  have hbd_wf := hwf.2.2.1; have hal_le := hcl.arena_len_le; have haa := hcl.arena_len_arr
  have hbd_ar : cref + 3 + old_sz ≤ s.core.arena.length := by omega
  have hbd_ar' : cref + 3 + old_sz ≤ arena'.length := by rw [har_len]; omega
  have hout_c : ∀ i, i < cref + 3 ∨ cref + 3 + old_sz ≤ i → arena'[i]? = s.core.arena[i]? := hout
  have hout_ref : ∀ r ∈ fullArenaClauseRefsCore s.core, r ≠ cref →
      (r + 3 + fullArenaClauseSizeCore s.core r ≤ cref ∧
        fullArenaNextOff s.core.arena s.core.arena_len r ≤ cref) ∨
      cref + 3 + old_sz ≤ r := fun r hr hne => by
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · exact Or.inl ⟨hw.arena.disjoint hr href hlt, fullArenaScanRefs_disjoint hr href hlt⟩
    · exact Or.inr (hw.arena.disjoint href hr hgt)
  have hnxt : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaNextOff arena' s.core.arena_len r =
        fullArenaNextOff s.core.arena s.core.arena_len r := fun r hr => by
    by_cases hrc : r = cref
    · subst r
      exact fullArenaNextOff_congr_block (hout_c cref (Or.inl (by omega)))
        (hout_c (cref + 2) (Or.inl (by omega))) fun k hk _ => hout_c k (Or.inr hk)
    · rcases hout_ref r hr hrc with ⟨_, _⟩ | hgt
      · have hr3 := (hw.arena.refs_wf r hr).2.1
        exact fullArenaNextOff_congr_block (hout_c r (Or.inl (by omega)))
          (hout_c (r + 2) (Or.inl (by omega))) fun i _ _ => hout_c i (Or.inl (by omega))
      · exact fullArenaNextOff_congr_block (hout_c r (Or.inr hgt))
          (hout_c (r + 2) (Or.inr (by omega))) fun i _ _ => hout_c i (Or.inr (by omega))
  have hrefs : fullArenaClauseRefsCore s'.core = fullArenaClauseRefsCore s.core :=
    fullArenaClauseRefsCore_congr rfl hnxt
  have hother : ∀ r ∈ fullArenaClauseRefsCore s.core, r ≠ cref →
      fullArenaClauseSizeCore s'.core r = fullArenaClauseSizeCore s.core r ∧
      fullArenaClauseGarbCore s'.core r = fullArenaClauseGarbCore s.core r ∧
      fullArenaClauseLitsCore s'.core r = fullArenaClauseLitsCore s.core r := fun r hr hne => by
    have hrwf := hw.arena.refs_wf r hr
    have hbd_r : r + 3 + fullArenaClauseSizeCore s.core r ≤ s.core.arena.length := by
      have := hrwf.2.2.1; omega
    have hbd_r' : r + 3 + fullArenaClauseSizeCore s.core r ≤ arena'.length := by
      rw [har_len]; have := hrwf.2.2.1; omega
    rcases hout_ref r hr hne with ⟨_, _⟩ | hgt
    · have hszr : fullArenaClauseSizeCore s'.core r = fullArenaClauseSizeCore s.core r := by
        unfold fullArenaClauseSizeCore; dsimp only [s']; rw [hout_c (r + 2) (Or.inl (by omega))]
      have hgar : fullArenaClauseGarbCore s'.core r = fullArenaClauseGarbCore s.core r := by
        unfold fullArenaClauseGarbCore fullArenaHdrCore; dsimp only [s']
        rw [hout_c r (Or.inl (by omega))]
      refine ⟨hszr, hgar, ?_⟩
      unfold fullArenaClauseLitsCore; rw [hszr]
      exact s13_lits_eq_of_hold hbd_r hbd_r' fun j hj => hout_c (r + 3 + j) (Or.inl (by omega))
    · have hszr : fullArenaClauseSizeCore s'.core r = fullArenaClauseSizeCore s.core r := by
        unfold fullArenaClauseSizeCore; dsimp only [s']; rw [hout_c (r + 2) (Or.inr (by omega))]
      have hgar : fullArenaClauseGarbCore s'.core r = fullArenaClauseGarbCore s.core r := by
        unfold fullArenaClauseGarbCore fullArenaHdrCore; dsimp only [s']
        rw [hout_c r (Or.inr hgt)]
      refine ⟨hszr, hgar, ?_⟩
      unfold fullArenaClauseLitsCore; rw [hszr]
      exact s13_lits_eq_of_hold hbd_r hbd_r' fun j hj => hout_c (r + 3 + j) (Or.inr (by omega))
  have hsz_cref : fullArenaClauseSizeCore s'.core cref = old_sz := by
    dsimp only [old_sz]; unfold fullArenaClauseSizeCore; dsimp only [s']
    rw [hout_c (cref + 2) (Or.inl (by omega))]
  have harena' : FullArenaClausesInv c F_cur s'.core := by
    refine ⟨hw.arena.len_ok, ?_, ?_, ?_, ?_⟩
    · intro r hr; rw [hrefs] at hr; rw [hnxt r hr]
      by_cases hrc : r = cref
      · subst r; rw [hsz_cref]; exact hwf
      · rw [(hother r hr hrc).1]; exact hw.arena.refs_wf r hr
    · intro r hr hsh; rw [hrefs] at hr
      by_cases hrc : r = cref
      · subst r
        have hsh0 : (fullArenaHdrCore s.core cref &&& 0x00800000#32) ≠ 0#32 := by
          unfold fullArenaHdrCore at hsh ⊢
          change (arena'[cref]?.getD 0#32 &&& 0x00800000#32) ≠ 0#32 at hsh
          rwa [hout_c cref (Or.inl (by omega))] at hsh
        obtain ⟨t, ht1, ht2, hsent⟩ := hw.arena.shrk_term cref hr hsh0
        rw [hsz_cref]
        exact ⟨t, ht1, ht2, by change arena'[t]? = _; rw [hout_c t (Or.inr ht1)]; exact hsent⟩
      · rcases hout_ref r hr hrc with ⟨_, _⟩ | hgt
        · have hsh0 : (fullArenaHdrCore s.core r &&& 0x00800000#32) ≠ 0#32 := by
            unfold fullArenaHdrCore at hsh ⊢
            change (arena'[r]?.getD 0#32 &&& 0x00800000#32) ≠ 0#32 at hsh
            rwa [hout_c r (Or.inl (by omega))] at hsh
          obtain ⟨t, ht1, ht2, hsent⟩ := hw.arena.shrk_term r hr hsh0
          obtain ⟨t0, ht0_lo, ht0_hi, _, ht0_sent⟩ :=
            fullArenaNextOff_hits_sentinel (hw.arena.refs_wf r hr).1 hsh0 ht1 ht2 hsent
          rw [(hother r hr hrc).1]
          exact ⟨t0, ht0_lo, Nat.lt_of_le_of_lt ht0_hi ht2, by
            change arena'[t0]? = _; rw [hout_c t0 (Or.inl (by omega))]; exact ht0_sent⟩
        · have hsh0 : (fullArenaHdrCore s.core r &&& 0x00800000#32) ≠ 0#32 := by
            unfold fullArenaHdrCore at hsh ⊢
            change (arena'[r]?.getD 0#32 &&& 0x00800000#32) ≠ 0#32 at hsh
            rwa [hout_c r (Or.inr hgt)] at hsh
          obtain ⟨t, ht1, ht2, hsent⟩ := hw.arena.shrk_term r hr hsh0
          rw [(hother r hr hrc).1]
          exact ⟨t, ht1, ht2, by
            change arena'[t]? = _; rw [hout_c t (Or.inr (by omega))]; exact hsent⟩
    · intro r hr hng'; rw [hrefs] at hr
      by_cases hrc : r = cref
      · subst r; exact hlits_lt'
      · rw [(hother r hr hrc).2.1] at hng'; rw [(hother r hr hrc).2.2]
        exact hw.arena.lits_lt r hr hng'
    · intro r hr hng'; rw [hrefs] at hr
      by_cases hrc : r = cref
      · subst r; exact hent'
      · rw [(hother r hr hrc).2.1] at hng'; rw [(hother r hr hrc).2.2]
        exact hw.arena.entails r hr hng'
  have hlen' : s'.LengthsOk c := ⟨{ hcl with arena_len_arr := har_len }, hinv.1.scratch_ok⟩
  have hnd' : FullArenaVarsNodup s' := fun r hr hng' => by
    change r ∈ fullArenaClauseRefsCore s'.core at hr; rw [hrefs] at hr
    by_cases hrc : r = cref
    · subst r; exact hnd_cr'
    · have hg0 : fullArenaClauseGarb s r = false := by
        change fullArenaClauseGarbCore s'.core r = false at hng'
        rwa [(hother r hr hrc).2.1] at hng'
      change ((fullArenaClauseLitsCore s'.core r).map (· / 2)).Nodup
      rw [(hother r hr hrc).2.2]; exact hinv.2.2.2.1 r hr hg0
  have hno_rsn : ∀ idx < s.core.trail_end,
      s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 :=
    fun idx hidx => hw.level0_rsn_none idx hidx (by have := hw.lvl_le idx hidx; omega)
  have hw' : FullWitnessInv c F0 F_cur s'.core :=
    { hw with
      arena := harena'
      watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun r hr => by
        change r ∈ fullArenaClauseRefsCore s'.core; rw [hrefs]; exact hr)
      reason_inv := fun idx hidx hne => absurd (hno_rsn idx hidx) hne
      reason_lit_mem := fun idx hidx hne _ => absurd (hno_rsn idx hidx) hne }
  exact ⟨⟨hlen', hw', hinv.2.2.1, hnd',
    FullExtScratchOk.of_pres hinv.2.2.2.2.1 ⟨rfl, rfl⟩ fun r hr => by
      change r ∈ fullArenaClauseRefsCore s'.core; rw [hrefs]; exact hr,
    hcl0, hinv.2.2.2.2.2.2⟩, hrefs⟩

private theorem s13_denseInvW_inPlaceShrink {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hinv : FullDenseInvW c F0 F_cur s)
    {cref nsz : Nat} (href : cref ∈ fullArenaClauseRefs s)
    (hng : fullArenaClauseGarb s cref = false) (h3 : 3 ≤ nsz)
    (hlt : nsz < fullArenaClauseSize s cref) {arena' : List (BitVec 32)}
    (har_len : arena'.length = c.arena_cap)
    (hhdr' : arena'[cref]? = some
      (if (fullArenaHdr s cref &&& 0x00800000#32) = 0#32 then
        fullArenaHdr s cref ||| 0x00800000#32
      else fullArenaHdr s cref))
    (hsz' : arena'[cref + 2]? = some (BitVec.ofNat 32 nsz))
    (hpad_old : ∀ j, nsz ≤ j → j < fullArenaClauseSize s cref - 1 →
      arena'[cref + 3 + j]? = s.core.arena[cref + 3 + j]?)
    (hlast_sent : (fullArenaHdr s cref &&& 0x00800000#32) = 0#32 →
      arena'[cref + 3 + fullArenaClauseSize s cref - 1]? = some 0xFFFFFFFF#32)
    (hlast_keep : (fullArenaHdr s cref &&& 0x00800000#32) ≠ 0#32 →
      arena'[cref + 3 + fullArenaClauseSize s cref - 1]? =
        s.core.arena[cref + 3 + fullArenaClauseSize s cref - 1]?)
    (hout : ∀ i, i < cref ∨ cref + 3 + fullArenaClauseSize s cref ≤ i →
      arena'[i]? = s.core.arena[i]?)
    (hlits_lt' : ∀ l ∈ fullArenaClauseLits { s with core := { s.core with arena := arena' } } cref,
      l < 2 * s.core.cur_vars)
    (hnd_cr' : ((fullArenaClauseLits { s with core := { s.core with arena := arena' } } cref).map
      (· / 2)).Nodup)
    (hent' : (cnfOfClauses F_cur).EntailsClause
      (cnfClause (fullArenaClauseLits { s with core := { s.core with arena := arena' } } cref))) :
    let s' := { s with core := { s.core with arena := arena' } }
    FullDenseInvW c F0 F_cur s' ∧ fullArenaClauseRefs s' = fullArenaClauseRefs s := by
  intro s'
  have hcl := hinv.1.core_ok; have hw := hinv.2.1; have hcl0 := hinv.2.2.2.2.2.1
  obtain ⟨hrefs, hother, _, _, harena'⟩ :=
    inPlaceShrink_preserves_arena hw.arena hcl href hng h3 hlt har_len hhdr' hsz' hpad_old
      hlast_sent hlast_keep hout hlits_lt' hent'
  have hlen' : s'.LengthsOk c := ⟨{ hcl with arena_len_arr := har_len }, hinv.1.scratch_ok⟩
  have hnd' : FullArenaVarsNodup s' := fun r hr hng' => by
    change r ∈ fullArenaClauseRefsCore s'.core at hr; rw [hrefs] at hr
    by_cases hrc : r = cref
    · subst r; exact hnd_cr'
    · have hg0 : fullArenaClauseGarb s r = false := by
        change fullArenaClauseGarbCore s'.core r = false at hng'
        rwa [(hother r hr hrc).2.1] at hng'
      change ((fullArenaClauseLitsCore s'.core r).map (· / 2)).Nodup
      rw [(hother r hr hrc).2.2]; exact hinv.2.2.2.1 r hr hg0
  have hno_rsn : ∀ idx < s.core.trail_end,
      s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 :=
    fun idx hidx => hw.level0_rsn_none idx hidx (by have := hw.lvl_le idx hidx; omega)
  have hw' : FullWitnessInv c F0 F_cur s'.core :=
    { hw with
      arena := harena'
      watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun r hr => by
        change r ∈ fullArenaClauseRefsCore s'.core; rw [hrefs]; exact hr)
      reason_inv := fun idx hidx hne => absurd (hno_rsn idx hidx) hne
      reason_lit_mem := fun idx hidx hne _ => absurd (hno_rsn idx hidx) hne }
  exact ⟨⟨hlen', hw', hinv.2.2.1, hnd',
    FullExtScratchOk.of_pres hinv.2.2.2.2.1 ⟨rfl, rfl⟩ fun r hr => by
      change r ∈ fullArenaClauseRefsCore s'.core; rw [hrefs]; exact hr,
    hcl0, hinv.2.2.2.2.2.2⟩, hrefs⟩

theorem s13_els_ar_push_watched {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (hWatch : M6EnvSpec Γ "full_watch_push" Full.fullWatchPushSpec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s s5 : FullState}
    {rl cr sz : BitVec 32} {R : Mem 64 → Prop} {m5 : Mem 64}
    {aH : Arg Val i64} {aRl aSz aCr aK : Arg Val i32}
    {cont : Tup Val [.bool] → Expr Val Cont rs}
    (haH : aH.val = c.hdr) (haRl : aRl.val = rl)
    (haSz : aSz.val = sz &&& 0x7FFFFFFF#32) (haCr : aCr.val = cr) (haK : aK.val = 2#32)
    (hinv5 : FullDenseInvW c F0 F_cur s5) (hcv5 : s5.core.cur_vars = s.core.cur_vars)
    (hfl5 : s5.core.fuel = s.core.fuel)
    (hrp5 : FullCongReprInv F_cur (2 * s.core.cur_vars) s5.core.repr)
    (htmk5 : s5.scratch.tarjan_mark = s.scratch.tarjan_mark)
    (htrh5 : s5.scratch.tarjan_reach = s.scratch.tarjan_reach)
    (hscr5 : s5.scratch.scratch_buf = s.scratch.scratch_buf)
    (hws15 : s5.scratch.work_stk1 = s.scratch.work_stk1)
    (hws25 : s5.scratch.work_stk2 = s.scratch.work_stk2)
    (hgu5 : s5.scratch.glue_used = s.scratch.glue_used)
    (hsz3 : 3 ≤ sz.toNat) (hsz_lt : sz.toNat < 2 ^ 31)
    (hcr_lt : cr.toNat < 0x80000000) (hcr_ne : cr ≠ 0xFFFFFFFF#32)
    (hcr5 : cr.toNat ∈ fullArenaClauseRefs s5) (hm5 : (FullMem c s5 ⋆ R) m5)
    (hk : ∀ (ok : Bool) (s' : FullState) (m' : Mem 64),
      S13ElsArOut c F0 F_cur s s' → (FullMem c s' ⋆ R) m' → wp Γ Q X (cont (ok, ())) m') :
    wp Γ Q X (Expr.call (as := [i64, i32, i32, i32, i32]) (bs := [.bool])
      "full_watch_push" (aH, aRl, aSz, aCr, aK, ()) cont) m5 := by
  have hbit : ((sz &&& 0x7FFFFFFF#32) &&& 0x80000000#32) = 0#32 := by
    rw [BitVec.and_assoc, show (0x7FFFFFFF#32 &&& 0x80000000#32) = 0#32 by decide, BitVec.and_zero]
  have hw0_ne : (sz &&& 0x7FFFFFFF#32) ≠ 0xFFFFFFFF#32 := fun heq => by
    rw [heq] at hbit; revert hbit; decide
  have hw0_3 : 3 ≤ (sz &&& 0x7FFFFFFF#32).toNat := by
    rw [BitVec.toNat_and, show (0x7FFFFFFF#32).toNat = 2 ^ 31 - 1 by decide,
      Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hsz_lt]; exact hsz3
  have hwm5 := hinv5.2.1.watches; unfold ModeWatchesInv at hwm5
  rw [ite_eq_right (fun h0 => hinv5.2.2.2.2.2.2 h0)] at hwm5
  refine wp_call_of_spec _ cont ?_
  dsimp only [vals]; rw [haH, haRl, haSz, haCr, haK]
  refine hWatch _ m5 (fun r m' => wp Γ Q X (cont r) m') X
    ⟨c, s5, R, rfl, hinv5.1, hwm5.layout, (fun h => by cases h),
      (fun _ => ⟨hw0_ne, hcr_ne⟩), hm5, ?_⟩
  intro ok wvec' wstk' wlen' wu' wsort' m' s' hlen' hlay' hother hok_t hok_f hm'
  have hinv' := s13_denseInvW_watchPush hinv5 hlen' hlay' hbit hw0_3 hcr_lt hcr5 hother
    (fun ht => by
      obtain ⟨h1, _, h2, h3, h4, h5⟩ := hok_t ht
      exact ⟨h1, h2, h3, h4, h5 rfl⟩)
    (fun hf hl => (hok_f hf).1 hl)
  exact hk ok s' m' ⟨hinv', hcv5, hfl5, hrp5, htmk5, htrh5, hscr5, hws15, hws25, hgu5⟩ hm'

theorem s13_els_ar_call_addUnit {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (hAddUnit : M6EnvSpec Γ "full_add_unit" Full.fullAddUnitSpec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s sG : FullState}
    {lit : BitVec 32} {R : Mem 64 → Prop} {mU : Mem 64}
    {aH : Arg Val i64} {aL : Arg Val i32} {cont : Tup Val [.bool] → Expr Val Cont rs}
    (haH : aH.val = c.hdr) (haL : aL.val = lit)
    (hoG : S13ElsArOut c F0 F_cur s sG)
    (hlt : lit.toNat < 2 * sG.core.cur_vars)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [lit.toNat]))
    (hmU : (FullMem c sG ⋆ R) mU)
      (hk : ∀ (okU : Bool) (sU : FullState) (mUn : Mem 64),
      S13ElsArOut c F0 F_cur s sU → sU.core.tmp = sG.core.tmp →
      (okU = false → F0.Unsat ∧ sU.core.inconsistent ≠ 0#64) →
      (FullMem c sU ⋆ R) mUn → wp Γ Q X (cont (okU, ())) mUn) :
    wp Γ Q X (Expr.call (as := [i64, i32]) (bs := [.bool])
      "full_add_unit" (aH, aL, ()) cont) mU := by
  refine wp_call_of_spec _ cont ?_
  dsimp only [vals]; rw [haH, haL]
  refine hAddUnit _ mU (fun r m' => wp Γ Q X (cont r) m') X
    ⟨c, F0, F_cur, sG, R, rfl, hoG.dinv.1, hoG.dinv.2.1, fun _ => hent, hmU, ?_⟩
  intro okU vals' flags' lvl' rsns' trl' tp' te' prop' cl' unass' unfl' inc'
    phases' ta' ba' pt' pb' hp' ps' hl' qsi' qss' mUn sU hlenU hwU hclU hfail _ hmUn
  have hinvU := m6_denseInvW_after_addUnit hoG.dinv hlenU hwU hclU
  exact hk okU sU mUn
    ⟨hinvU, hoG.cv, hoG.fuel, hoG.repr, hoG.tmk, hoG.trh, hoG.scr, hoG.ws1, hoG.ws2, hoG.gu⟩
    rfl (fun hokf => hfail hlt hokf) hmUn

theorem s13_els_ar_call_addBin {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (hAddBin : M6EnvSpec Γ "full_add_bin" Full.fullAddBinSpec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s sB : FullState}
    {l0 l1 : BitVec 32} {R : Mem 64 → Prop} {mB : Mem 64}
    {aH : Arg Val i64} {a0 a1 : Arg Val i32} {cont : Tup Val [i64] → Expr Val Cont rs}
    (haH : aH.val = c.hdr) (ha0 : a0.val = l0) (ha1 : a1.val = l1)
    (hoB : S13ElsArOut c F0 F_cur s sB)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [l0.toNat, l1.toNat]))
    (hmB : (FullMem c sB ⋆ R) mB)
    (hk : ∀ (rB : BitVec 64) (sBn : FullState) (mBn : Mem 64),
      S13ElsArOut c F0 F_cur s sBn →
      (rB = 20#64 → F0.Unsat ∧ sBn.core.inconsistent ≠ 0#64) →
      (FullMem c sBn ⋆ R) mBn → wp Γ Q X (cont (rB, ())) mBn) :
    wp Γ Q X (Expr.call (as := [i64, i32, i32]) (bs := [i64])
      "full_add_bin" (aH, a0, a1, ()) cont) mB := by
  refine wp_call_of_spec _ cont ?_
  dsimp only [vals]; rw [haH, ha0, ha1]
  refine hAddBin _ mB (fun r m' => wp Γ Q X (cont r) m') X
    ⟨c, F0, F_cur, sB, R, rfl, hoB.dinv.1, hoB.dinv.2.1, hoB.dinv.2.2.2.2.2.1,
      fun _ _ => hent, hmB, ?_⟩
  intro rB vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec' wstk' wlen' wu'
    nb' oom' inc' phases' wsort' mBn sBn hlenBn hwBn _ hr20 _ hmBn
  have hinvBn := s13_denseInvW_after_addBin hoB.dinv hlenBn hwBn
  exact hk rB sBn mBn
    ⟨hinvBn, hoB.cv, hoB.fuel, hoB.repr, hoB.tmk, hoB.trh, hoB.scr, hoB.ws1, hoB.ws2, hoB.gu⟩
    hr20 hmBn

theorem s13_els_ar_call_find {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (hFind : ∀ a m Q X, fullCongFindSpec a m Q X → Γ "full_cong_find" [i64, i32] [i32] a m Q X)
    {c : FullCfg} {F_cur : List (List Nat)} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {l : BitVec 32} {cont : Tup Val [i32] → Expr Val Cont rs}
    (hrep : FullCongReprInv F_cur (2 * s.core.cur_vars) s.core.repr)
    (hl : l.toNat < 2 * s.core.cur_vars) (hm : (FullMem c s ⋆ R) m)
    (hk : ∀ r repr' m', repr'.length = s.core.repr.length →
      FullCongReprInv F_cur (2 * s.core.cur_vars) repr' →
      r.toNat < 2 * s.core.cur_vars → LitEquiv (cnfOfClauses F_cur) l.toNat r.toNat →
      (FullMem c { s with core := { s.core with repr := repr' } } ⋆ R) m' →
      wp Γ Q X (cont (r, ())) m') :
    wp Γ Q X (Expr.call (as := [i64, i32]) (bs := [i32])
      "full_cong_find" (Arg.var c.pRepr, Arg.var l, ()) cont) m :=
  wp_call_of_spec _ cont
    (hFind (c.pRepr, l, ()) m (fun r m' => wp Γ Q X (cont r) m') X
      ⟨F_cur, 2 * s.core.cur_vars, s.core.repr, FullCongHelpers.FullReprRest c s ⋆ R, hrep, hl,
        FullCongHelpers.focus_full_repr hm, fun r repr' m' hlen' hrep' _ hr_lt heqv hm' =>
          hk r repr' m' hlen' hrep' hr_lt heqv (FullCongHelpers.unfocus_full_repr hm')⟩)

theorem s13_els_ar_ret_bool {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s sR : FullState} {R : Mem 64 → Prop} {mR : Mem 64} {Q : Post [.bool]}
    (ho : S13ElsArOut c F0 F_cur s sR) (hmR : (FullMem c sR ⋆ R) mR)
    (hQ : ∀ (ok : Bool) (s' : FullState) (m' : Mem 64),
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel = s.core.fuel → FullCongReprInv F_cur (2 * s.core.cur_vars) s'.core.repr →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
      s'.scratch.scratch_buf = s.scratch.scratch_buf →
      s'.scratch.work_stk1 = s.scratch.work_stk1 →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      s'.scratch.glue_used = s.scratch.glue_used →
      (ok = false → F0.Unsat ∧ s'.core.inconsistent ≠ 0#64) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    Q (true, ()) mR :=
  hQ true sR mR ho.dinv ho.cv ho.fuel ho.repr ho.tmk ho.trh ho.scr ho.ws1 ho.ws2 ho.gu
    (fun h => Bool.noConfusion h) hmR

theorem s13_els_ar_ret_false {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s sR : FullState} {R : Mem 64 → Prop} {mR : Mem 64} {Q : Post [.bool]}
    (ho : S13ElsArOut c F0 F_cur s sR) (huns : F0.Unsat ∧ sR.core.inconsistent ≠ 0#64)
    (hmR : (FullMem c sR ⋆ R) mR)
    (hQ : ∀ (ok : Bool) (s' : FullState) (m' : Mem 64),
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel = s.core.fuel → FullCongReprInv F_cur (2 * s.core.cur_vars) s'.core.repr →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
      s'.scratch.scratch_buf = s.scratch.scratch_buf →
      s'.scratch.work_stk1 = s.scratch.work_stk1 →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      s'.scratch.glue_used = s.scratch.glue_used →
      (ok = false → F0.Unsat ∧ s'.core.inconsistent ≠ 0#64) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    Q (false, ()) mR :=
  hQ false sR mR ho.dinv ho.cv ho.fuel ho.repr ho.tmk ho.trh ho.scr ho.ws1 ho.ws2 ho.gu
    (fun _ => huns) hmR

theorem s13_els_ar_shrink_helpers {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s1 sC : FullState} {lm2 : List (BitVec 8)} {tmp2 ar4 : List (BitVec 32)}
    {cr sz32 nsz2 : BitVec 32} (hinvC : FullDenseInvW c F0 F_cur sC)
    (hcr_ref : cr.toNat ∈ fullArenaClauseRefs sC) (hng_cr : fullArenaClauseGarb s1 cr.toNat = false)
    (hcr_bd : cr.toNat < s1.core.arena.length) (har4 : ar4.length = c.arena_cap)
    (hcr_bd2 : cr.toNat + 2 < ar4.length) (_hcr_bd1 : cr.toNat + 1 < ar4.length)
    (hsC_ar : sC.core.arena = s1.core.arena) (hsC_cv : sC.core.cur_vars = s1.core.cur_vars)
    (hsz_def : sz32.toNat = fullArenaClauseSize s1 cr.toNat)
    (h3n : 3 ≤ nsz2.toNat) (hlt_sz : nsz2.toNat < sz32.toNat)
    (hout4 : ∀ i, i < cr.toNat + 3 ∨ cr.toNat + 3 + nsz2.toNat ≤ i →
      ar4[i]? = sC.core.arena[i]?)
    (htmp_cp : ∀ j < nsz2.toNat, ar4[cr.toNat + 3 + j]? = tmp2[j]?)
    (hmap2 : S13ElsLitMap c s1 lm2 tmp2 nsz2.toNat)
    (hhent4 : (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((tmp2.take nsz2.toNat).map BitVec.toNat))) :
    let ar_b := (ar4.set (cr.toNat + 2) nsz2).set (cr.toNat + 1) 2#32
    let ar_0 := (ar_b.set cr.toNat (fullArenaHdr sC cr.toNat ||| 0x00800000#32)).set
      (cr.toNat + 3 + sz32.toNat - 1) 0xFFFFFFFF#32
    ((s1.core.arena[cr.toNat]'hcr_bd &&& 0x00800000#32) = 0#32 →
      FullDenseInvW c F0 F_cur { sC with core := { sC.core with arena := ar_0 } } ∧
      fullArenaClauseRefs { sC with core := { sC.core with arena := ar_0 } } =
        fullArenaClauseRefs sC) ∧
    ((s1.core.arena[cr.toNat]'hcr_bd &&& 0x00800000#32) ≠ 0#32 →
      FullDenseInvW c F0 F_cur { sC with core := { sC.core with arena := ar_b } } ∧
      fullArenaClauseRefs { sC with core := { sC.core with arena := ar_b } } =
        fullArenaClauseRefs sC) := by
  intro ar_b ar_0
  have har_set_sz : ar_b[cr.toNat + 2]? = some nsz2 := by
    dsimp only [ar_b]; rw [List.getElem?_set_ne (by omega), List.getElem?_set_self hcr_bd2]
  have hsz_eq_sC : fullArenaClauseSize sC cr.toNat = sz32.toNat := by
    unfold fullArenaClauseSize fullArenaClauseSizeCore at hsz_def ⊢; rw [hsC_ar, ← hsz_def]
  have hlt_sz_ar : nsz2.toNat < fullArenaClauseSize sC cr.toNat := by omega
  have hwf_cr := hinvC.2.1.arena.refs_wf cr.toNat hcr_ref
  have hal := hinvC.1.core_ok.arena_len_le
  have hsz_bd : cr.toNat + 3 + sz32.toNat ≤ c.arena_cap := by
    have h1 := hwf_cr.2.2.1; have h2 := hwf_cr.2.2.2.1
    have h3 : fullArenaClauseSize sC cr.toNat = fullArenaClauseSizeCore sC.core cr.toNat := rfl
    rw [hsz_eq_sC] at h3; rw [← h3] at h1; omega
  have htmp_l := hmap2.tmp_len; have hnsz_l := hmap2.nsz_le; have hcv_l := hmap2.cv_le
  have hng_sC : fullArenaClauseGarb sC cr.toNat = false := by
    unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore at hng_cr ⊢
    rw [hsC_ar]; exact hng_cr
  have hlits_of : ∀ (arX : List (BitVec 32)), arX.length = c.arena_cap →
      arX[cr.toNat + 2]? = some nsz2 → (∀ j < nsz2.toNat, arX[cr.toNat + 3 + j]? = tmp2[j]?) →
      fullArenaClauseLits { sC with core := { sC.core with arena := arX } } cr.toNat =
        ((tmp2.take nsz2.toNat).map BitVec.toNat) := fun arX hlenX hszX hlX => by
    unfold fullArenaClauseLits fullArenaClauseLitsCore fullArenaClauseSizeCore; dsimp only
    rw [hszX, Option.getD_some,
      show nsz2.toNat = (tmp2.take nsz2.toNat).length by rw [List.length_take_of_le (by omega)]]
    apply List.ext_getElem
    · simp only [List.length_map, List.length_take, List.length_drop, hlenX]; omega
    · intro j hj1 _; simp only [List.length_map, List.length_take] at hj1
      have hj : j < nsz2.toNat := by omega
      simp only [List.getElem_map, List.getElem_take, List.getElem_drop]
      have hq := hlX j hj
      rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at hq
      exact congrArg BitVec.toNat (Option.some.inj hq)
  constructor <;> intro hhd
  · have hhd0 : (fullArenaHdr sC cr.toNat &&& 0x00800000#32) = 0#32 := by
      unfold fullArenaHdr fullArenaHdrCore; rw [hsC_ar]
      change (s1.core.arena[cr.toNat]?.getD 0#32 &&& 0x00800000#32) = 0#32
      rw [List.getElem?_eq_getElem hcr_bd, Option.getD_some]; exact hhd
    have hsz0 : ar_0[cr.toNat + 2]? = some nsz2 := by
      dsimp only [ar_0]; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
        har_set_sz]
    have hlen0 : ar_0.length = c.arena_cap := by simp [ar_0, ar_b, har4]
    have hl0 : ∀ j < nsz2.toNat, ar_0[cr.toNat + 3 + j]? = tmp2[j]? := fun j hj => by
      dsimp only [ar_0, ar_b]
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
        List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
      exact htmp_cp j hj
    have heq := hlits_of ar_0 hlen0 hsz0 hl0
    exact s13_denseInvW_inPlaceShrink hinvC hcr_ref hng_sC h3n hlt_sz_ar hlen0
      (by dsimp only [ar_0]
          rw [ite_eq_left hhd0, List.getElem?_set_ne (by omega),
            List.getElem?_set_self (by simp [ar_b, har4]; omega)])
      (by rw [hsz0]; simp)
      (fun j hj1 hj2 => by
        dsimp only [ar_0, ar_b]; rw [hsz_eq_sC] at hj2
        rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
          List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
        exact hout4 (cr.toNat + 3 + j) (Or.inr (by omega)))
      (fun _ => by
        dsimp only [ar_0]; change ar_0[cr.toNat + 3 + fullArenaClauseSize sC cr.toNat - 1]? = _
        rw [hsz_eq_sC]; exact List.getElem?_set_self (by simp [ar_b, har4]; omega))
      (fun h => absurd hhd0 h)
      (fun i hi => by
        change i < cr.toNat ∨ cr.toNat + 3 + fullArenaClauseSize sC cr.toNat ≤ i at hi
        rw [hsz_eq_sC] at hi; dsimp only [ar_0, ar_b]
        rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
          List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
        cases hi with
        | inl h => exact hout4 i (Or.inl (by omega))
        | inr h => exact hout4 i (Or.inr (by omega)))
      (fun l hl => by
        rw [heq, List.mem_iff_getElem] at hl; obtain ⟨j, hj, rfl⟩ := hl
        have hj' : j < nsz2.toNat := by simp only [List.length_map, List.length_take] at hj; omega
        simp only [List.getElem_map, List.getElem_take]
        have := hsC_cv ▸ hmap2.tmp_lt j hj'
        rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at this)
      (by rw [heq, List.map_map]; exact hmap2.nodup) (by rw [heq]; exact hhent4)
  · have hhd1 : (fullArenaHdr sC cr.toNat &&& 0x00800000#32) ≠ 0#32 := by
      unfold fullArenaHdr fullArenaHdrCore; rw [hsC_ar]
      change (s1.core.arena[cr.toNat]?.getD 0#32 &&& 0x00800000#32) ≠ 0#32
      rw [List.getElem?_eq_getElem hcr_bd, Option.getD_some]; exact hhd
    have hlenb : ar_b.length = c.arena_cap := by simp [ar_b, har4]
    have hlb : ∀ j < nsz2.toNat, ar_b[cr.toNat + 3 + j]? = tmp2[j]? := fun j hj => by
      dsimp only [ar_b]
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]; exact htmp_cp j hj
    have heq := hlits_of ar_b hlenb har_set_sz hlb
    exact s13_denseInvW_inPlaceShrink hinvC hcr_ref hng_sC h3n hlt_sz_ar hlenb
      (by dsimp only [ar_b]
          rw [ite_eq_right hhd1, List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
          change ar4[cr.toNat]? = some (sC.core.arena[cr.toNat]?.getD 0#32)
          rw [hout4 cr.toNat (Or.inl (by omega)), hsC_ar]
          change s1.core.arena[cr.toNat]? = some (s1.core.arena[cr.toNat]?.getD 0#32)
          rw [List.getElem?_eq_getElem hcr_bd, Option.getD_some])
      (by rw [har_set_sz]; simp)
      (fun j hj1 hj2 => by
        dsimp only [ar_b]; rw [hsz_eq_sC] at hj2
        rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
        exact hout4 (cr.toNat + 3 + j) (Or.inr (by omega)))
      (fun h => absurd h hhd1)
      (fun _ => by
        dsimp only [ar_b]; change ar_b[cr.toNat + 3 + fullArenaClauseSize sC cr.toNat - 1]? = _
        rw [hsz_eq_sC, List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
        exact hout4 (cr.toNat + 3 + sz32.toNat - 1) (Or.inr (by omega)))
      (fun i hi => by
        change i < cr.toNat ∨ cr.toNat + 3 + fullArenaClauseSize sC cr.toNat ≤ i at hi
        rw [hsz_eq_sC] at hi; dsimp only [ar_b]
        rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
        cases hi with
        | inl h => exact hout4 i (Or.inl (by omega))
        | inr h => exact hout4 i (Or.inr (by omega)))
      (fun l hl => by
        rw [heq, List.mem_iff_getElem] at hl; obtain ⟨j, hj, rfl⟩ := hl
        have hj' : j < nsz2.toNat := by simp only [List.length_map, List.length_take] at hj; omega
        simp only [List.getElem_map, List.getElem_take]
        have := hsC_cv ▸ hmap2.tmp_lt j hj'
        rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at this)
      (by rw [heq, List.map_map]; exact hmap2.nodup) (by rw [heq]; exact hhent4)

theorem s13_els_ar_same_ok {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s1 sC : FullState} {lm2 : List (BitVec 8)} {tmp2 ar4 : List (BitVec 32)}
    {cr sz32 nsz2 : BitVec 32} (hinvC : FullDenseInvW c F0 F_cur sC)
    (hcr_ref : cr.toNat ∈ fullArenaClauseRefs sC) (hng_cr : fullArenaClauseGarb s1 cr.toNat = false)
    (har4 : ar4.length = c.arena_cap) (hcr_bd2 : cr.toNat + 2 < ar4.length)
    (hsC_ar : sC.core.arena = s1.core.arena) (hsC_cv : sC.core.cur_vars = s1.core.cur_vars)
    (hsz_def : sz32.toNat = fullArenaClauseSize s1 cr.toNat)
    (hnsz_eq : nsz2.toNat = sz32.toNat)
    (hout4 : ∀ i, i < cr.toNat + 3 ∨ cr.toNat + 3 + nsz2.toNat ≤ i →
      ar4[i]? = sC.core.arena[i]?)
    (htmp_cp : ∀ j < nsz2.toNat, ar4[cr.toNat + 3 + j]? = tmp2[j]?)
    (hmap2 : S13ElsLitMap c s1 lm2 tmp2 nsz2.toNat)
    (hhent4 : (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((tmp2.take nsz2.toNat).map BitVec.toNat))) :
    let s4 : FullState := { sC with core := { sC.core with arena := ar4 } }
    FullDenseInvW c F0 F_cur s4 ∧ fullArenaClauseRefs s4 = fullArenaClauseRefs sC := by
  intro s4
  have hsz_cr4 : fullArenaClauseSize sC cr.toNat = sz32.toNat := by
    unfold fullArenaClauseSize fullArenaClauseSizeCore at hsz_def ⊢; rw [hsC_ar, ← hsz_def]
  have hng_sC : fullArenaClauseGarb sC cr.toNat = false := by
    unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore at hng_cr ⊢
    rw [hsC_ar]; exact hng_cr
  have hwf_cr := hinvC.2.1.arena.refs_wf cr.toNat hcr_ref
  have hal := hinvC.1.core_ok.arena_len_le
  have hsz_bd : cr.toNat + 3 + sz32.toNat ≤ c.arena_cap := by
    have h1 := hwf_cr.2.2.1; have h2 := hwf_cr.2.2.2.1
    have h3 : fullArenaClauseSize sC cr.toNat = fullArenaClauseSizeCore sC.core cr.toNat := rfl
    rw [hsz_cr4] at h3; rw [← h3] at h1; omega
  have htmp_l := hmap2.tmp_len; have hnsz_l := hmap2.nsz_le; have hcv_l := hmap2.cv_le
  have hlits_eq : fullArenaClauseLits s4 cr.toNat = ((tmp2.take nsz2.toNat).map BitVec.toNat) := by
    unfold fullArenaClauseLits fullArenaClauseLitsCore fullArenaClauseSizeCore; dsimp only [s4]
    rw [hout4 (cr.toNat + 2) (Or.inl (by omega))]
    have hsz_ar4 : (sC.core.arena[cr.toNat + 2]?.getD 0#32).toNat = sz32.toNat := hsz_cr4
    rw [hsz_ar4, ← hnsz_eq,
      show nsz2.toNat = (tmp2.take nsz2.toNat).length by rw [List.length_take_of_le (by omega)]]
    apply List.ext_getElem
    · simp only [List.length_map, List.length_take, List.length_drop, har4]; omega
    · intro j hj1 _; simp only [List.length_map, List.length_take] at hj1
      have hj : j < nsz2.toNat := by omega
      simp only [List.getElem_map, List.getElem_take, List.getElem_drop]
      have hq := htmp_cp j hj
      rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at hq
      exact congrArg BitVec.toNat (Option.some.inj hq)
  exact s13_denseInvW_replaceSameLen hinvC hcr_ref hng_sC har4
    (fun i hi => by rw [hsz_cr4, ← hnsz_eq] at hi; exact hout4 i hi)
    (fun l hl => by
      rw [hlits_eq, List.mem_iff_getElem] at hl; obtain ⟨j, hj, rfl⟩ := hl
      have hj' : j < nsz2.toNat := by simp only [List.length_map, List.length_take] at hj; omega
      simp only [List.getElem_map, List.getElem_take]
      have := hsC_cv ▸ hmap2.tmp_lt j hj'
      rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at this)
    (by rw [hlits_eq, List.map_map]; exact hmap2.nodup) (by rw [hlits_eq]; exact hhent4)

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S1
