/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityCongProof0
public import LeanQbe.T.Examples.Kissat.FullM6CongSubstProof2a
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb

/-!
# Kissat 4.0.4 Congruence Parity Proofs — Part 1b (`GAP-CONG-01` Wide AND Extraction & Matcher)

Proves parametric `(Γ : Env)` `Func.wp` contracts for:
1. `full_cong_extract` (`full_cong_extract_wp`, `fidCongExtractSpec`, arity up to `64`)
2. `full_cong_and_match` (`full_cong_and_match_wp`, `fidCongAndMatchSpec`, 64-bit mask up to `64`)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityCong

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullCongHelpers
open LeanQbe.T.Examples.Kissat.FullM3CongBva
open LeanQbe.T.Examples.Kissat.FullM6CongSubst
open scoped LeanQbe.T.Examples.Kissat.FullM3CongBva.M3HeadTactics
open scoped LeanQbe.T.Examples.Kissat.FullM6CongSubst.M6HeadTactics
open scoped FullArenaTactics Full.FullCongTactics
open Kraken.Bedrock2.Test

/-! ## 1. Local Helpers (`Proof1b`) -/

section Helpers

private theorem fullWatchBounds_of_dense {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hd : FullDenseInvW c F0 F_cur s) :
    ∀ l < 2 * s.core.cur_vars,
      fullWatchOffCore s.core l + fullWatchSizeCore s.core l ≤ c.wcap := by
  intro l hl
  have hw_le := hd.1.core_ok.wlen_le
  have hwt := hd.2.1.watches
  unfold ModeWatchesInv at hwt
  split at hwt
  · exact Nat.le_trans (hwt.layout.bounds l hl) hw_le
  · exact Nat.le_trans (hwt.layout.bounds l hl) hw_le

private theorem fullDenseInvW_with_ws1 {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hd : FullDenseInvW c F0 F_cur s)
    {ws1' : List (BitVec 32)} (hl1 : ws1'.length = 2 * c.max_vars) :
    FullDenseInvW c F0 F_cur { s with scratch := { s.scratch with work_stk1 := ws1' } } :=
  ⟨⟨hd.1.core_ok, { hd.1.scratch_ok with work_stk1_len := hl1 }⟩,
   hd.2.1, hd.2.2.1, hd.2.2.2.1, hd.2.2.2.2.1, hd.2.2.2.2.2.1, hd.2.2.2.2.2.2⟩

private theorem fullDenseInvW_with_ws2 {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hd : FullDenseInvW c F0 F_cur s)
    {ws2' : List (BitVec 32)} (hl : ws2'.length = 2 * c.max_vars) :
    FullDenseInvW c F0 F_cur { s with scratch := { s.scratch with work_stk2 := ws2' } } :=
  ⟨⟨hd.1.core_ok, { hd.1.scratch_ok with work_stk2_len := hl }⟩,
   hd.2.1, hd.2.2.1, hd.2.2.2.1, hd.2.2.2.2.1, hd.2.2.2.2.2.1, hd.2.2.2.2.2.2⟩

private theorem fullDenseInvW_with_scr {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hd : FullDenseInvW c F0 F_cur s)
    {scr' : List (BitVec 32)} (hl : scr'.length = c.scratch_cap) :
    FullDenseInvW c F0 F_cur { s with scratch := { s.scratch with scratch_buf := scr' } } :=
  ⟨⟨hd.1.core_ok, { hd.1.scratch_ok with scratch_buf_len := hl }⟩,
   hd.2.1, hd.2.2.1, hd.2.2.2.1, hd.2.2.2.2.1, hd.2.2.2.2.2.1, hd.2.2.2.2.2.2⟩

private theorem core_fields_of_tmp_lm {a b : FullCoreState}
    (h : { a with tmp := b.tmp, lit_mark := b.lit_mark } = b) :
    a.inconsistent = b.inconsistent ∧ a.arena = b.arena ∧ a.arena_len = b.arena_len ∧
    a.cur_vars = b.cur_vars ∧ a.cur_level = b.cur_level ∧ a.dense_mode = b.dense_mode ∧
    a.fuel = b.fuel ∧ a.repr = b.repr ∧
    ({ b with tmp := a.tmp, lit_mark := a.lit_mark } : FullCoreState) = a := by
  cases a; cases b; cases h; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem scr_fields_of_buf {a b : FullScratch}
    (h : { a with scratch_buf := b.scratch_buf } = b) :
    a.last_learned = b.last_learned ∧ a.extend_len = b.extend_len := by
  cases a; cases b; cases h; exact ⟨rfl, rfl⟩

private theorem fullDenseInvW_of_xorK {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s s' : FullState} (hd : FullDenseInvW c F0 F_cur s)
    (hlen' : s'.LengthsOk c)
    (hce : { s'.core with tmp := s.core.tmp, lit_mark := s.core.lit_mark } = s.core)
    (hse : { s'.scratch with scratch_buf := s.scratch.scratch_buf } = s.scratch)
    (hmk' : FullLitMarksClear c s') :
    FullDenseInvW c F0 F_cur s' := by
  obtain ⟨_, har, hal, _, hcl, hdm, _, _, hkeq⟩ := core_fields_of_tmp_lm hce
  obtain ⟨hll, hext⟩ := scr_fields_of_buf hse
  have hnd' := fullArenaVarsNodup_of_eq hd.2.2.2.1 har hal
  have hext' := fullExtScratchOk_of_eq hd.2.2.2.2.1 har hal hll hext
  have hw_tm : FullWitnessInv c F0 F_cur
      { s.core with tmp := s'.core.tmp, lit_mark := s'.core.lit_mark } :=
    { hd.2.1 with
      arena := { hd.2.1.arena with len_ok := hd.2.1.arena.len_ok }
      watches := hd.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }
  exact ⟨hlen', hkeq ▸ hw_tm, hmk', hnd', hext', hcl.trans hd.2.2.2.2.2.1, hdm ▸ hd.2.2.2.2.2.2⟩

private theorem nodup_getElem_inj {α : Type _} :
    ∀ {l : List α}, l.Nodup → ∀ i j : Nat, (hi : i < l.length) → (hj : j < l.length) →
      l[i]'hi = l[j]'hj → i = j
  | [], _, i, _, hi, _, _ => absurd hi (Nat.not_lt_zero i)
  | _ :: _, _, 0, 0, _, _, _ => rfl
  | x :: xs, hnd, 0, j + 1, _, hj, heq => by
    have hcons := List.nodup_cons.mp hnd
    have hmem : xs[j]'(by simp at hj; omega) ∈ xs := List.getElem_mem _
    have hx : x = xs[j]'(by simp at hj; omega) := by simpa using heq
    exact absurd (hx ▸ hmem) hcons.1
  | x :: xs, hnd, i + 1, 0, hi, _, heq => by
    have hcons := List.nodup_cons.mp hnd
    have hmem : xs[i]'(by simp at hi; omega) ∈ xs := List.getElem_mem _
    have hx : x = xs[i]'(by simp at hi; omega) := by simpa using heq.symm
    exact absurd (hx ▸ hmem) hcons.1
  | _ :: xs, hnd, i + 1, j + 1, hi, hj, heq => by
    have hcons := List.nodup_cons.mp hnd
    exact congrArg Nat.succ (nodup_getElem_inj hcons.2 i j (by simp at hi; omega)
      (by simp at hj; omega) heq)

private theorem nodup_map_on {α β : Type _} {f : α → β} :
    ∀ {l : List α}, l.Nodup → (∀ a ∈ l, ∀ b ∈ l, f a = f b → a = b) → (l.map f).Nodup
  | [], _, _ => .nil
  | a :: xs, hnd, hinj => by
    have hcons := List.nodup_cons.mp hnd
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hmem => ?_, nodup_map_on hcons.2 fun x hx y hy hxy =>
      hinj x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy) hxy⟩
    rw [List.mem_map] at hmem; obtain ⟨b, hb, hfb⟩ := hmem
    have hba := hinj b (List.mem_cons_of_mem _ hb) a List.mem_cons_self hfb
    exact hcons.1 (hba ▸ hb)

private theorem list_nodup_filter_map (f : Nat → Nat) {idxs : List Nat}
    {ar : List (BitVec 32)} {sz p : Nat}
    (hnd : ((List.range sz).map fun q => (ar[p + 3 + q]?.getD 0#32).toNat / 2).Nodup)
    (hid_nd : idxs.Nodup) (hid_lt : ∀ q ∈ idxs, q < sz)
    (hf : ∀ q, f q = (ar[p + 3 + q]?.getD 0#32).toNat / 2) :
    (idxs.map f).Nodup := by
  refine nodup_map_on hid_nd fun a ha b hb hab => ?_
  rw [hf a, hf b] at hab
  have ha_s := hid_lt a ha; have hb_s := hid_lt b hb
  exact nodup_getElem_inj hnd a b (by simp; omega) (by simp; omega)
    (by simpa [List.getElem_map] using hab)

private theorem nat_xor1_mod2 (n : Nat) : (n ^^^ 1) % 2 = (n % 2) ^^^ 1 := by
  apply Nat.eq_of_testBit_eq; intro k
  cases k with
  | zero => simp [Nat.testBit_zero]
  | succ k =>
    have hlt : (n % 2) ^^^ 1 < 2 := by
      rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h]
    simp [Nat.testBit_succ, Nat.div_eq_of_lt hlt]

private theorem bv32_bit1_ne0_mod2 {l neg_p : BitVec 32} :
    ((if (l &&& 1#32) != 0#32 then neg_p ^^^ 1#32 else neg_p) &&& 1#32).toNat =
      (neg_p &&& 1#32).toNat ^^^ (l.toNat % 2) := by
  have hl1 : (l &&& 1#32).toNat = l.toNat % 2 := by
    rw [BitVec.toNat_and, show (1#32 : BitVec 32).toNat = 1 from rfl]
    exact Nat.and_one_is_mod l.toNat
  rcases Nat.mod_two_eq_zero_or_one l.toNat with hm | hm
  · have hb : (l &&& 1#32) = 0#32 := BitVec.eq_of_toNat_eq (by rw [hl1, hm]; rfl)
    simp [hb, hm]
  · have hb : (l &&& 1#32) = 1#32 := BitVec.eq_of_toNat_eq (by rw [hl1, hm]; rfl)
    have hne1 : ((1#32 : BitVec 32) != 0#32) = true := rfl
    simp only [hb, hne1, ↓reduceIte]
    rw [BitVec.toNat_and, BitVec.toNat_and, BitVec.toNat_xor,
      show (1#32 : BitVec 32).toNat = 1 from rfl,
      Nat.and_one_is_mod, Nat.and_one_is_mod, hm, nat_xor1_mod2]

/-- Generalization of `m6_andGate_of_emitted` to wide AND gates up to arity `64` (`usz ≤ 65`). -/
private theorem fid_andGate_of_emitted {F_cur : List (List Nat)} {cur_vars usz i g_len : Nat}
    {base scr : List (BitVec 32)} (hu3 : 3 ≤ usz) (hu65 : usz ≤ 65) (hucv : usz ≤ cur_vars)
    (hi : i < usz)
    (hlt : ∀ k < usz, (base[k]?.getD 0#32).toNat < 2 * cur_vars)
    (hcl : (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((List.range usz).map fun k => (base[k]?.getD 0#32).toNat)))
    (hbins : ∀ k < usz, k ≠ i →
      (cnfOfClauses F_cur).EntailsClause (cnfClause
        [litNeg (base[i]?.getD 0#32).toNat, litNeg (base[k]?.getD 0#32).toNat]))
    (hbd_g : g_len + 2 + (usz - 1) ≤ scr.length)
    (h0 : scr[g_len]? = some (base[i]?.getD 0#32))
    (h1 : scr[g_len + 1]? = some (BitVec.ofNat 32 (usz - 1)))
    (hrhs : ∀ k < usz, k ≠ i →
      scr[g_len + 2 + (if k < i then k else k - 1)]? = some ((base[k]?.getD 0#32) ^^^ 1#32)) :
    FidGateAt 64 F_cur cur_vars scr (g_len + 2 + (usz - 1)) g_len := by
  have hmword_tag : ((BitVec.ofNat 32 (usz - 1) >>> 28)).toNat = 0 := by
    rw [BitVec.toNat_ushiftRight, bv32_ofNat_toNat (by omega), Nat.shiftRight_eq_div_pow]
    exact Nat.div_eq_of_lt (by omega)
  have hmword_ar : ((BitVec.ofNat 32 (usz - 1) &&& 0xFF#32)).toNat = usz - 1 := by
    rw [BitVec.toNat_and, bv32_ofNat_toNat (by omega),
      show (0xFF#32 : BitVec 32).toNat = 255 from rfl]
    simpa [Nat.mod_eq_of_lt (show usz - 1 < 256 by omega)] using
      Nat.and_two_pow_sub_one_eq_mod (usz - 1) 8
  have hrhs_at : ∀ r < usz - 1,
      ∃ v : BitVec 32, scr[g_len + 2 + r]? = some v ∧ v.toNat < 2 * cur_vars ∧
        (cnfOfClauses F_cur).EntailsClause
          (cnfClause [litNeg (base[i]?.getD 0#32).toNat, v.toNat]) := by
    intro r hr
    let k := if r < i then r else r + 1
    have hk_lt : k < usz := by dsimp only [k]; split <;> omega
    have hk_ne : k ≠ i := by dsimp only [k]; split <;> omega
    have hk_eq : (if k < i then k else k - 1) = r := by
      dsimp only [k]; split <;> (try split) <;> omega
    have hget := hrhs k hk_lt hk_ne; rw [hk_eq] at hget
    exact ⟨_, hget,
      by rw [FullCongHelpers.bv32_xor1_eq_litNeg]; exact bv32_xor1_lt_even (hlt k hk_lt),
      by rw [FullCongHelpers.bv32_xor1_eq_litNeg]; exact hbins k hk_lt hk_ne⟩
  refine ⟨base[i]?.getD 0#32, BitVec.ofNat 32 (usz - 1), h0, h1, hlt i hi, by omega, by omega,
    by omega, fun r hr => let ⟨v, hv, hltv, _⟩ := hrhs_at r (by omega); ⟨v, hv, hltv⟩,
    Or.inl ⟨hmword_tag, by omega, ?_, ?_⟩⟩
  · refine entails_perm_clause (fun x hx => ?_) hcl
    rw [List.mem_map] at hx; obtain ⟨k, hk, rfl⟩ := hx; rw [List.mem_range] at hk
    rw [List.mem_cons]; by_cases hki : k = i
    · subst hki; exact Or.inl rfl
    · right; rw [List.mem_map]
      let r := if k < i then k else k - 1
      have hr_lt : r < usz - 1 := by dsimp only [r]; split <;> omega
      have hscr_r := hrhs k hk hki
      have hr_scr : g_len + 2 + r < scr.length := by omega
      have hval_r : scr[g_len + 2 + r]'hr_scr = (base[k]?.getD 0#32) ^^^ 1#32 := by
        rw [List.getElem?_eq_getElem hr_scr] at hscr_r; exact Option.some.inj hscr_r
      refine ⟨(scr[g_len + 2 + r]'hr_scr).toNat, List.mem_map.mpr ⟨_, ?_, rfl⟩, ?_⟩
      · have hlt_t : r < ((scr.drop (g_len + 2)).take
            ((BitVec.ofNat 32 (usz - 1) &&& 0xFF#32).toNat)).length := by
          rw [List.length_take, List.length_drop, hmword_ar]; omega
        simpa [List.getElem_take, List.getElem_drop] using List.getElem_mem hlt_t
      · rw [hval_r, FullCongHelpers.bv32_xor1_eq_litNeg, litNeg_litNeg]
  · intro x hx
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx; obtain ⟨r, hr, hget⟩ := List.mem_iff_getElem.mp hv
    rw [List.length_take, List.length_drop, hmword_ar] at hr
    rw [List.getElem_take, List.getElem_drop] at hget
    obtain ⟨v', hv', _, hent⟩ := hrhs_at r (by omega)
    rw [List.getElem?_eq_getElem (by omega)] at hv'
    rwa [(Option.some.inj hv').symm.trans hget] at hent

private theorem bv32_add1_lt_of {x : BitVec 32} (h : x.toNat + 1 < 2 ^ 32) :
    (x + 1#32).toNat = x.toNat + 1 := by
  rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl, Nat.mod_eq_of_lt h]

end Helpers

/-! ## 2. `full_cong_extract_wp` (`fidCongExtractSpec`) -/

theorem full_cong_extract_wp (Γ : Env)
    (hNext : ∀ args m Q X, FullCongSpecs.fullArenaNextSpec args m Q X →
      Γ "full_arena_next" [i64, i32] [i32] args m Q X)
    (hHasBin : ∀ args m Q X, FullCongSpecs.fullHasBinSpec args m Q X →
      Γ "full_has_bin" [i64, i32, i32] [.bool] args m Q X)
    (hCountBins : ∀ args m Q X, m6CongCountBinsSpec args m Q X →
      Γ "full_cong_count_bins" [i64] [] args m Q X)
    (hTryXorIte : ∀ args m Q X, fidCongTryXorIteSpec args m Q X →
      Γ "full_cong_try_xor_ite" [i64, i32, i32, i32, i64, i64] [i64] args m Q X)
    (hExtractXorK : ∀ args m Q X, fidCongExtractXorKSpec args m Q X →
      Γ "full_cong_extract_xor_k" [i64, i32, i32, i64, i64] [i64] args m Q X) :
    ∀ args m Q X, fidCongExtractSpec args m Q X →
      Func.wp Γ full_cong_extract_body args m Q X := by
  rintro ⟨h, g_cap, tick_lim, ⟨⟩⟩ m0 Q X ⟨c, F0, F_cur, s, R, rfl, hd, hg_cap, hm0, hQ⟩
  have hmx := c.hmaxv; have hac := c.harena; have hsc := c.hscr
  unfold dimacsBound at hmx hac hsc
  c0_hsteps!; m3_call hCountBins
  refine ⟨c, s, R, rfl, hd.1, fullWatchBounds_of_dense hd, hm0, fun ws1' m1 hws1_l hm1 => ?_⟩
  let s1 : FullState := { s with scratch := { s.scratch with work_stk1 := ws1' } }
  have hd1 : FullDenseInvW c F0 F_cur s1 := fullDenseInvW_with_ws1 hd hws1_l
  c0_hsteps_nogrp
  refine wp_loop_inv (ts := [i64, i64, i64])
    (fun (p, g_len, ticks, ()) mp => ∃ sp : FullState,
      FullDenseInvW c F0 F_cur sp ∧ sp.core.cur_vars = s.core.cur_vars ∧
      sp.core.fuel = s.core.fuel ∧ sp.core.repr = s.core.repr ∧
      sp.core.inconsistent = s.core.inconsistent ∧ sp.core.arena = s1.core.arena ∧
      sp.core.arena_len = s1.core.arena_len ∧ p.toNat ≤ s1.core.arena_len ∧
      (p.toNat = s1.core.arena_len ∨ p.toNat ∈ fullArenaClauseRefsCore s1.core) ∧
      g_len.toNat ≤ g_cap.toNat ∧
      FidGateSeqOk 64 F_cur s.core.cur_vars sp.scratch.scratch_buf g_len.toNat 0 ∧
      (FullMem c sp ⋆ R) mp)
    (fun (p, _, _, ()) _ => s1.core.arena_len - p.toNat)
    (fun J hJ => by
      c0_hsteps!
      have hmem0 : (0#64 : BitVec 64).toNat = s1.core.arena_len ∨
          (0#64 : BitVec 64).toNat ∈ fullArenaClauseRefsCore s1.core := by
        rcases Nat.eq_zero_or_pos s1.core.arena_len with hz | hpos
        · exact Or.inl hz.symm
        · exact Or.inr (fullArenaClauseRefs_zero_mem hd1.2.1 hpos)
      exact hJ (0#64, 0#64, 0#64, ()) m1 ⟨s1, hd1, rfl, rfl, rfl, rfl, rfl, rfl, Nat.zero_le _,
        hmem0, Nat.zero_le _, .done, hm1⟩)
    (fun J (p, g_len, ticks, ()) mp
      ⟨sp, hdp, hcv_p, hfl_p, hrep_p, hinc_p, har_p, hal_p, hp_le, hp_mem, hgl_le, hseq_p,
       hmp⟩ ihp => ?_)
  have hq_done : Q (g_len, ()) mp :=
    hQ g_len sp mp hdp hcv_p hfl_p hrep_p hinc_p hgl_le hseq_p hmp
  have hlen_p := hdp.1
  have harl_p := hlen_p.core_ok.arena_len_arr; have hale_p := hlen_p.core_ok.arena_len_le
  have hcv_ple := hlen_p.core_ok.cur_vars_le; have hvals_pl := hlen_p.core_ok.vals_len
  have hws1_pl := hlen_p.scratch_ok.work_stk1_len; have hws2_pl := hlen_p.scratch_ok.work_stk2_len
  have hscrl_p := hlen_p.scratch_ok.scratch_buf_len
  m6_split_fast
  · have hp_lt : p.toNat < sp.core.arena_len := by
      simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat] at hc
      rw [Nat.mod_eq_of_lt (by omega)] at hc; exact hc
    clear hc; m6_split_fast
    · clear hc; m6_split_fast
      · clear hc
        have hp_ref : p.toNat ∈ fullArenaClauseRefsCore sp.core := by
          have hmem := hp_mem.resolve_left (by omega)
          unfold fullArenaClauseRefsCore; rw [har_p, hal_p]; exact hmem
        have hp_wf := hdp.2.1.arena.refs_wf p.toNat hp_ref
        have hp_arr : p.toNat < sp.core.arena.length := by omega
        have hp2_n : (p + 2#64).toNat = p.toNat + 2 := by bv_omega
        have hp2_arr : (p + 2#64).toNat < sp.core.arena.length := by omega
        c0_hsteps!; m3_call hNext
        refine ⟨c, sp, R, rfl, hlen_p, hmp, ?_⟩
        have hp_tr : (p.setWidth 32).toNat = p.toNat := by
          rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
        have hnp_bd := fullArenaNextOff_bounds (ar := sp.core.arena) (alen := sp.core.arena_len)
          (cref := p.toNat) hp_wf.1
        let np_bv := (BitVec.ofNat 32 (fullArenaNextOff sp.core.arena sp.core.arena_len
          (p.setWidth 32).toNat)).setWidth 64
        have hnp_n : np_bv.toNat = fullArenaNextOff sp.core.arena sp.core.arena_len p.toNat := by
          dsimp only [np_bv]; rw [hp_tr, bv_zext32_toNat, bv32_ofNat_toNat (by omega)]
        have hnp_le : np_bv.toNat ≤ s1.core.arena_len := by
          rw [hnp_n, ← hal_p]; exact hnp_bd.2
        have hnp_mem : np_bv.toNat = s1.core.arena_len ∨
            np_bv.toNat ∈ fullArenaClauseRefsCore s1.core := by
          rw [hnp_n]
          rw [show fullArenaNextOff sp.core.arena sp.core.arena_len p.toNat =
            fullArenaNextOff s1.core.arena s1.core.arena_len p.toNat by rw [har_p, hal_p]]
          exact fullArenaClauseRefs_next_or_end hd1.2.1 (hp_mem.resolve_left (by omega))
        have hnp_gt : p.toNat < np_bv.toNat := by
          rw [hnp_n]; have := hp_wf.2.1; have := hp_wf.2.2.1; omega
        c0_hsteps_nogrp; refine wp_join_group (ts := [i64, i64])
          (fun (gl', tk', ()) mj => ∃ sj : FullState,
            FullDenseInvW c F0 F_cur sj ∧ sj.core.cur_vars = s.core.cur_vars ∧
            sj.core.fuel = s.core.fuel ∧ sj.core.repr = s.core.repr ∧
            sj.core.inconsistent = s.core.inconsistent ∧ sj.core.arena = s1.core.arena ∧
            sj.core.arena_len = s1.core.arena_len ∧ gl'.toNat ≤ g_cap.toNat ∧
            FidGateSeqOk 64 F_cur s.core.cur_vars sj.scratch.scratch_buf gl'.toNat 0 ∧
            (FullMem c sj ⋆ R) mj)
          (fun _ ⟨gl', tk', ⟨⟩⟩ mj
            ⟨sj, hdj, hcv_j, hfl_j, hrep_j, hinc_j, har_j, hal_j, hgl_j, hseq_j, hmj⟩ => by
            m3_let
            exact ihp (np_bv, gl', tk', ()) mj (by dsimp only; omega)
              ⟨sj, hdj, hcv_j, hfl_j, hrep_j, hinc_j, har_j, hal_j, by omega, hnp_mem, hgl_j,
               hseq_j, hmj⟩)
          ?_
        intro Jnext hJnext
        have hjnext_same : Jnext (g_len, ticks + 1#64, ()) mp :=
          hJnext (g_len, ticks + 1#64, ()) mp
            ⟨sp, hdp, hcv_p, hfl_p, hrep_p, hinc_p, har_p, hal_p, hgl_le, hseq_p, hmp⟩
        m6_split_fast
        · have hng_red := beq_iff_eq.mp hc; clear hc
          have hng : fullArenaClauseGarb sp p.toNat = false := by
            unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
            rw [List.getElem?_eq_getElem hp_arr, Option.getD_some]
            exact garb_false_of_and_480000 hng_red
          m6_split_fast
          · clear hc
            have hsz_p2 : sp.core.arena[(p + 2#64).toNat]'hp2_arr =
                sp.core.arena[p.toNat + 2]'(by omega) :=
              list_getElem_congr hp2_n hp2_arr (by omega)
            have hsz_eq : fullArenaClauseSizeCore sp.core p.toNat =
                (sp.core.arena[(p + 2#64).toNat]'hp2_arr).toNat := by
              unfold fullArenaClauseSizeCore
              rw [hsz_p2, List.getElem?_eq_getElem (by omega), Option.getD_some]
            have hsz3 : 3 ≤ (sp.core.arena[(p + 2#64).toNat]'hp2_arr).toNat := by
              rw [← hsz_eq]; exact hp_wf.2.1
            let sz_bv := sp.core.arena[(p + 2#64).toNat]'hp2_arr
            have hbd_sz : p.toNat + 3 + sz_bv.toNat ≤ sp.core.arena.length := by
              have h1 := hp_wf.2.2.1; have h2 := hp_wf.2.2.2.1
              have hsz_d : fullArenaClauseSizeCore sp.core p.toNat = sz_bv.toNat := hsz_eq
              omega
            c0_hsteps_nogrp
            refine wp_loop_break_group
              (brkTs := [i32, i32, i32, i32, .bool, i32]) (lpTs := [i32, i32, i32, i32, i32])
              (fun (usz, _, _, neg_p, sat, _, ()) mb => ∃ ws2 : List (BitVec 32),
                ws2.length = 2 * c.max_vars ∧
                (sat = false →
                  3 ≤ sz_bv.toNat ∧ usz.toNat ≤ 65 ∧
                  usz.toNat ≤ sz_bv.toNat ∧ usz.toNat ≤ sp.core.cur_vars ∧
                  (∀ j < usz.toNat, (ws2[j]?.getD 0#32).toNat < 2 * sp.core.cur_vars) ∧
                  ((neg_p &&& 1#32).toNat = (List.range usz.toNat).foldl
                    (fun acc i => acc ^^^ ((ws2[i]?.getD 0#32).toNat % 2)) 0) ∧
                  (∃ idxs : List Nat, idxs.length = usz.toNat ∧ idxs.Nodup ∧
                    (∀ q ∈ idxs, q < sz_bv.toNat) ∧
                    (∀ j < usz.toNat,
                      idxs[j]? = some (idxs[j]?.getD 0) →
                      ws2[j]? = sp.core.arena[p.toNat + 3 + (idxs[j]?.getD 0)]?) ∧
                    (∀ q < sz_bv.toNat, q ∈ idxs ∨
                      sp.core.vals[(sp.core.arena[p.toNat + 3 + q]?.getD 0#32).toNat]?.getD 0#8 =
                        0xFF#8)) ∧
                  (∀ j < usz.toNat, ∀ j2 < usz.toNat, j ≠ j2 →
                    (ws2[j]?.getD 0#32).toNat / 2 ≠ (ws2[j2]?.getD 0#32).toNat / 2) ∧
                  (cnfOfClauses F_cur).EntailsClause (cnfClause
                    ((List.range usz.toNat).map fun j => (ws2[j]?.getD 0#32).toNat))) ∧
                (FullMem c { sp with scratch := { sp.scratch with work_stk2 := ws2 } } ⋆ R) mb)
              (fun rem (usz, max_nbc, min_nbc, neg_p, k, ()) mk => ∃ ws2 : List (BitVec 32),
                ws2.length = 2 * c.max_vars ∧ k.toNat ≤ sz_bv.toNat ∧
                rem = sz_bv.toNat - k.toNat ∧
                usz.toNat ≤ 65 ∧ usz.toNat ≤ k.toNat ∧ usz.toNat ≤ sp.core.cur_vars ∧
                (∀ j < usz.toNat, (ws2[j]?.getD 0#32).toNat < 2 * sp.core.cur_vars) ∧
                ((neg_p &&& 1#32).toNat = (List.range usz.toNat).foldl
                  (fun acc i => acc ^^^ ((ws2[i]?.getD 0#32).toNat % 2)) 0) ∧
                (∃ idxs : List Nat, idxs.length = usz.toNat ∧ idxs.Nodup ∧
                  (∀ q ∈ idxs, q < k.toNat) ∧
                  (∀ j < usz.toNat,
                    ws2[j]? = sp.core.arena[p.toNat + 3 + (idxs[j]?.getD 0)]?) ∧
                  (∀ q < k.toNat, q ∈ idxs ∨
                    sp.core.vals[(sp.core.arena[p.toNat + 3 + q]?.getD 0#32).toNat]?.getD 0#8 =
                      0xFF#8)) ∧
                (FullMem c { sp with scratch := { sp.scratch with work_stk2 := ws2 } } ⋆ R) mk)
              ?_ ?_ ?_
            · rintro _ ⟨usz, _, _, neg_p, sat, _, ⟨⟩⟩ mb ⟨ws2, hws2_l, hnsat, hmb⟩
              let sb : FullState := { sp with scratch := { sp.scratch with work_stk2 := ws2 } }
              have hdb : FullDenseInvW c F0 F_cur sb := fullDenseInvW_with_ws2 hdp hws2_l
              m6_split_fast
              · clear hc; c0_hsteps!
                exact hJnext (g_len, ticks + 1#64, ()) mb
                  ⟨sb, hdb, hcv_p, hfl_p, hrep_p, hinc_p, har_p, hal_p, hgl_le, hseq_p, hmb⟩
              · have hsat_f : sat = false := hc; clear hc
                m6_split_fast
                · have hu_lt3 : 3 ≤ usz.toNat := by
                    simp only [BitVec.ule, decide_eq_true_eq] at hc; bv_omega
                  clear hc; m6_split_fast
                  · have hu_le65 : usz.toNat ≤ 65 := by
                      simp only [BitVec.ule, decide_eq_true_eq] at hc; bv_omega
                    clear hc; m6_split_fast
                    · have hu_cv : usz.toNat ≤ sb.core.cur_vars := by
                        simp only [BitVec.ule, decide_eq_true_eq, bv_zext32_toNat,
                          BitVec.toNat_ofNat] at hc
                        rw [Nat.mod_eq_of_lt (by omega)] at hc
                        dsimp only [sb]; rw [hcv_p]; exact hc
                      clear hc
                      obtain ⟨_, _, _, _, hlt_u, hneg_u, _, hdiff_u, hent_u⟩ := hnsat hsat_f
                      let arity := usz - 1#32
                      have har_n : arity.toNat = usz.toNat - 1 := by
                        dsimp only [arity]; bv_omega
                      c0_hsteps_nogrp; refine wp_join_group (ts := [i64])
                        (fun (gl', ()) mg => ∃ sg : FullState,
                          FullDenseInvW c F0 F_cur sg ∧ sg.core.cur_vars = s.core.cur_vars ∧
                          sg.core.fuel = s.core.fuel ∧ sg.core.repr = s.core.repr ∧
                          sg.core.inconsistent = s.core.inconsistent ∧
                          sg.core.arena = s1.core.arena ∧ sg.core.arena_len = s1.core.arena_len ∧
                          sg.scratch.work_stk2 = ws2 ∧
                          g_len.toNat ≤ gl'.toNat ∧ gl'.toNat ≤ g_cap.toNat ∧
                          FidGateSeqOk 64 F_cur s.core.cur_vars sg.scratch.scratch_buf gl'.toNat 0 ∧
                          (FullMem c sg ⋆ R) mg)
                        ?_ ?_
                      · rintro _ ⟨gl', ⟨⟩⟩ mg
                          ⟨sg, hdg, hcv_g, hfl_g, hrep_g, hinc_g, har_g, hal_g, hws2_g,
                           hgl_lo, hgl_hi, hseq_g, hmg⟩
                        have hlen_g := hdg.1
                        m6_split_fast
                        · have hu3 : usz = 3#32 := beq_iff_eq.mp hc; clear hc
                          have hu3_n : usz.toNat = 3 := congrArg BitVec.toNat hu3
                          m6_split_fast
                          · have hgl12_le : gl'.toNat + 12 ≤ g_cap.toNat := by
                              simp only [BitVec.ule, decide_eq_true_eq] at hc; bv_omega
                            have hlt3' := hlt_u; rw [hu3_n] at hlt3'
                            have hl0_lt := hlt3' 0 (by omega)
                            have hl1_lt := hlt3' 1 (by omega)
                            have hl2_lt := hlt3' 2 (by omega)
                            have hdiff01 := hdiff_u 0 (by omega) 1 (by omega) (by decide)
                            have hdiff02 := hdiff_u 0 (by omega) 2 (by omega) (by decide)
                            have hdiff12 := hdiff_u 1 (by omega) 2 (by omega) (by decide)
                            have hent3 : (cnfOfClauses F_cur).EntailsClause (cnfClause
                                [(ws2[0]?.getD 0#32).toNat, (ws2[1]?.getD 0#32).toNat,
                                 (ws2[2]?.getD 0#32).toNat]) := by
                              simpa [hu3_n, List.range_succ] using hent_u
                            have hws2_0 : 0 < sg.scratch.work_stk2.length := by
                              rw [hws2_g, hws2_l]; omega
                            have hws2_1 : 1 < sg.scratch.work_stk2.length := by
                              rw [hws2_g, hws2_l]; omega
                            have hws2_2 : 2 < sg.scratch.work_stk2.length := by
                              rw [hws2_g, hws2_l]; omega
                            have hget0 : sg.scratch.work_stk2[0]'hws2_0 = ws2[0]?.getD 0#32 := by
                              rw [List.getElem?_eq_getElem (by rw [hws2_l]; omega),
                                Option.getD_some]; simp [hws2_g]
                            have hget1 : sg.scratch.work_stk2[1]'hws2_1 = ws2[1]?.getD 0#32 := by
                              rw [List.getElem?_eq_getElem (by rw [hws2_l]; omega),
                                Option.getD_some]; simp [hws2_g]
                            have hget2 : sg.scratch.work_stk2[2]'hws2_2 = ws2[2]?.getD 0#32 := by
                              rw [List.getElem?_eq_getElem (by rw [hws2_l]; omega),
                                Option.getD_some]; simp [hws2_g]
                            have hload0 : loadVal mg i32 (c.pWorkStk2 + 0#64) =
                                some (sg.scratch.work_stk2[0]'hws2_0) := by
                              simpa using FullArenaTactics.load_full_work_stk2 (i := 0) hws2_0 hmg
                            have hload1 : loadVal mg i32 (c.pWorkStk2 + 4#64) =
                                some (sg.scratch.work_stk2[1]'hws2_1) := by
                              simpa using FullArenaTactics.load_full_work_stk2 (i := 1) hws2_1 hmg
                            have hload2 : loadVal mg i32 (c.pWorkStk2 + 8#64) =
                                some (sg.scratch.work_stk2[2]'hws2_2) := by
                              simpa using FullArenaTactics.load_full_work_stk2 (i := 2) hws2_2 hmg
                            m3_let; refine wp_load_of hload0 ?_
                            m3_let; refine wp_load_of hload1 ?_
                            m3_let; refine wp_load_of hload2 ?_
                            c0_hsteps!; m3_call hTryXorIte
                            refine ⟨64, c, F0, F_cur, sg, R, by decide, Nat.le_refl _, rfl, hlen_g,
                              hdg.2.1, hdg.2.2.2.1, hdg.2.2.2.2.2.1, ?_, ?_, ?_,
                              (by rw [hget0, hget1]; exact hdiff01),
                              (by rw [hget0, hget2]; exact hdiff02),
                              (by rw [hget1, hget2]; exact hdiff12), ?_,
                              by omega, hg_cap, by rw [hcv_g]; exact hseq_g, hmg,
                              fun ret scr' mg' hscrl' hret_lo hret_hi _ hseq' hmg' => ?_⟩
                            · rw [hget0, hcv_g, ← hcv_p]; exact hl0_lt
                            · rw [hget1, hcv_g, ← hcv_p]; exact hl1_lt
                            · rw [hget2, hcv_g, ← hcv_p]; exact hl2_lt
                            · rw [hget0, hget1, hget2]; exact hent3
                            · c0_hsteps!
                              exact hJnext (ret, ticks + 1#64 + 4#64, ()) mg'
                                ⟨{ sg with scratch := { sg.scratch with scratch_buf := scr' } },
                                 fullDenseInvW_with_scr hdg hscrl', hcv_g, hfl_g, hrep_g, hinc_g,
                                 har_g, hal_g, hret_hi, by rw [← hcv_g]; exact hseq', hmg'⟩
                          · clear hc; c0_hsteps!
                            exact hJnext (gl', ticks + 1#64, ()) mg
                              ⟨sg, hdg, hcv_g, hfl_g, hrep_g, hinc_g, har_g, hal_g, hgl_hi,
                               hseq_g, hmg⟩
                        · clear hc; m6_split_fast
                          · have hu4 : 4 ≤ usz.toNat := by
                              simp only [BitVec.ule, decide_eq_true_eq] at hc; bv_omega
                            clear hc; m6_split_fast
                            · have hu5 : usz.toNat ≤ 5 := by
                                simp only [BitVec.ule, decide_eq_true_eq] at hc; bv_omega
                              clear hc; m6_split_fast
                              · clear hc; c0_hsteps!; m3_call hExtractXorK
                                refine ⟨64, c, F0, F_cur, sg, R, by decide, Nat.le_refl _, rfl,
                                  hlen_g,
                                  hdg.2.1, hdg.2.2.1, hdg.2.2.2.1, hdg.2.2.2.2.2.1, by omega,
                                  by omega, by rw [hcv_g]; omega, hgl_hi, hg_cap,
                                  by rw [hcv_g]; exact hseq_g,
                                  by rw [hws2_g]; intro j hj; rw [hcv_g, ← hcv_p]
                                     exact hlt_u j hj,
                                  by rw [hws2_g]; exact hneg_u,
                                  by rw [hws2_g]; exact hent_u, hmg,
                                  fun ret sx mx hlen_x hce hse hmk_x hret_lo hret_hi _ hseq_x
                                    hmx => ?_⟩
                                have hdx := fullDenseInvW_of_xorK hdg hlen_x hce hse hmk_x
                                obtain ⟨hinc_ce, har_ce, hal_ce, hcv_ce, _, _, hfu_ce, hrep_ce,
                                  _⟩ := core_fields_of_tmp_lm hce
                                c0_hsteps!
                                exact hJnext (ret, ticks + 1#64 + 8#64, ()) mx
                                  ⟨sx, hdx, hcv_ce.trans hcv_g, hfu_ce.trans hfl_g,
                                   hrep_ce.trans hrep_g, hinc_ce.trans hinc_g,
                                   har_ce.trans har_g, hal_ce.trans hal_g, hret_hi,
                                   by rw [← hcv_g]; exact hseq_x, hmx⟩
                              · clear hc; c0_hsteps!
                                exact hJnext (gl', ticks + 1#64, ()) mg
                                  ⟨sg, hdg, hcv_g, hfl_g, hrep_g, hinc_g, har_g, hal_g, hgl_hi,
                                   hseq_g, hmg⟩
                            · clear hc; c0_hsteps!
                              exact hJnext (gl', ticks + 1#64, ()) mg
                                ⟨sg, hdg, hcv_g, hfl_g, hrep_g, hinc_g, har_g, hal_g, hgl_hi,
                                 hseq_g, hmg⟩
                          · clear hc; c0_hsteps!
                            exact hJnext (gl', ticks + 1#64, ()) mg
                              ⟨sg, hdg, hcv_g, hfl_g, hrep_g, hinc_g, har_g, hal_g, hgl_hi,
                               hseq_g, hmg⟩
                      · intro Jg hJg
                        have hjg0 : Jg (g_len, ()) mb :=
                          hJg (g_len, ()) mb ⟨sb, hdb, hcv_p, hfl_p, hrep_p, hinc_p, har_p, hal_p,
                            rfl, Nat.le_refl _, hgl_le, hseq_p, hmb⟩
                        m6_split_fast
                        · clear hc; m6_split_fast
                          · clear hc; c0_hsteps!
                            refine wp_loop_inv (ts := [i64, i32])
                              (fun (gc, i, ()) mi => ∃ scrc : List (BitVec 32),
                                scrc.length = c.scratch_cap ∧ g_len.toNat ≤ gc.toNat ∧
                                gc.toNat ≤ g_cap.toNat ∧ i.toNat ≤ usz.toNat ∧
                                FidGateSeqOk 64 F_cur s.core.cur_vars scrc gc.toNat 0 ∧
                                (FullMem c { sb with scratch :=
                                  { sb.scratch with scratch_buf := scrc } } ⋆ R) mi)
                              (fun (_, i, ()) _ => usz.toNat - i.toNat)
                              (fun Ji hJi => by
                                c0_hsteps!
                                exact hJi (g_len, 0#32, ()) mb
                                  ⟨sb.scratch.scratch_buf, hscrl_p, Nat.le_refl _, hgl_le,
                                   Nat.zero_le _, hseq_p, hmb⟩)
                              (fun Ji (gc, i, ()) mi
                                ⟨scrc, hscrl_c, hgc_lo, hgc_hi, hi_le, hseq_c, hmi⟩ ihi => ?_)
                            m6_split_fast
                            · have hi_lt : i.toNat < usz.toNat := by
                                simp only [BitVec.ult, decide_eq_true_eq] at hc; exact hc
                              clear hc; m6_split_fast
                              · have hgc_ar : gc.toNat + 2 + arity.toNat ≤ g_cap.toNat := by
                                  simp only [BitVec.ule, decide_eq_true_eq] at hc; bv_omega
                                clear hc
                                have hi_ws2 : i.toNat < ws2.length := by omega
                                let lhs := ws2[i.toNat]'hi_ws2
                                have hlhs_eq : ws2[i.toNat]?.getD 0#32 = lhs := by
                                  rw [List.getElem?_eq_getElem hi_ws2, Option.getD_some]
                                have hlhs_ws1 : (BitVec.setWidth 64 lhs).toNat <
                                    sb.scratch.work_stk1.length := by
                                  rw [bv_zext32_toNat]; dsimp only [sb]; rw [hws1_pl]
                                  have hlt_lhs := hlt_u i.toNat hi_lt
                                  rw [hlhs_eq] at hlt_lhs; omega
                                have hi1_n : (i + 1#32).toNat = i.toNat + 1 := by bv_omega
                                m6_split_fast
                                · clear hc
                                  let sc_c : FullState :=
                                    { sb with scratch := { sb.scratch with scratch_buf := scrc } }
                                  have hlen_c : sc_c.LengthsOk c :=
                                    ⟨hlen_p.core_ok,
                                     { hdb.1.scratch_ok with scratch_buf_len := hscrl_c }⟩
                                  have hwc_c : FullWitnessInv c F0 F_cur sc_c.core := hdb.2.1
                                  c0_hsteps_nogrp
                                  refine wp_loop_break_group (brkTs := [.bool, i32]) (lpTs := [i32])
                                    (fun (ok, _, ()) mj => mj = mi ∧
                                      (ok = true → ∀ k < usz.toNat, k ≠ i.toNat →
                                        (cnfOfClauses F_cur).EntailsClause (cnfClause
                                          [litNeg lhs.toNat,
                                           litNeg (ws2[k]?.getD 0#32).toNat])))
                                    (fun rem2 (j, ()) mj => mj = mi ∧ j.toNat ≤ usz.toNat ∧
                                      rem2 = usz.toNat - j.toNat ∧
                                      ∀ k < j.toNat, k ≠ i.toNat →
                                        (cnfOfClauses F_cur).EntailsClause (cnfClause
                                          [litNeg lhs.toNat,
                                           litNeg (ws2[k]?.getD 0#32).toNat]))
                                    ?_ ?_ ?_
                                  · rintro _ ⟨ok, _, ⟨⟩⟩ mj ⟨hmj_eq, hbins⟩
                                    subst mj
                                    m6_split_fast
                                    · have hbins' := hbins (by cases hc; rfl)
                                      have hgc0 : gc.toNat < scrc.length := by omega
                                      have hgc1_n : (gc + 1#64).toNat = gc.toNat + 1 := by bv_omega
                                      have hgc1 : (gc + 1#64).toNat < scrc.length := by omega
                                      c0_hsteps!
                                      let scrc0 := scrc.set gc.toNat lhs
                                      let scrc1 := scrc0.set (gc + 1#64).toNat arity
                                      refine wp_loop_inv (ts := [i32, i32])
                                        (fun (j2, rk, ()) mj2 => ∃ scrw : List (BitVec 32),
                                          scrw.length = c.scratch_cap ∧
                                          j2.toNat ≤ usz.toNat ∧
                                          rk.toNat = (if j2.toNat ≤ i.toNat then j2.toNat
                                            else j2.toNat - 1) ∧
                                          (∀ idx < gc.toNat, scrw[idx]? = scrc[idx]?) ∧
                                          scrw[gc.toNat]? = some lhs ∧
                                          scrw[gc.toNat + 1]? = some arity ∧
                                          (∀ k < j2.toNat, k ≠ i.toNat →
                                            scrw[gc.toNat + 2 + (if k < i.toNat then k else k - 1)]?
                                              = some ((ws2[k]?.getD 0#32) ^^^ 1#32)) ∧
                                          (FullMem c { sb with scratch :=
                                            { sb.scratch with scratch_buf := scrw } } ⋆ R) mj2)
                                        (fun (j2, _, ()) _ => usz.toNat - j2.toNat)
                                        (fun Jw hJw => by
                                          c0_hsteps!
                                          refine hJw (0#32, 0#32, ()) m
                                            ⟨scrc1, by simp [scrc1, scrc0, hscrl_c], Nat.zero_le _,
                                             by simp, fun idx hidx => ?_, ?_, ?_,
                                             (fun k hk => by cases hk), hm⟩
                                          · dsimp only [scrc1, scrc0]
                                            rw [List.getElem?_set_ne (by omega),
                                              List.getElem?_set_ne (by omega)]
                                          · dsimp only [scrc1, scrc0]
                                            rw [List.getElem?_set_ne (by omega),
                                              List.getElem?_set_self hgc0]
                                          · dsimp only [scrc1, scrc0]; rw [← hgc1_n]
                                            exact List.getElem?_set_self
                                              (by rw [List.length_set]; exact hgc1))
                                        (fun Jw (j2, rk, ()) mj2
                                          ⟨scrw, hscrlw, hj2_le, hrk_e, hprefw, hw0, hw1, hwrhs,
                                           hmj2⟩ ihw => ?_)
                                      m6_split_fast
                                      · have hj2_lt : j2.toNat < usz.toNat := by
                                          simp only [BitVec.ult, decide_eq_true_eq] at hc; exact hc
                                        have hj21_n : (j2 + 1#32).toNat = j2.toNat + 1 := by
                                          bv_omega
                                        clear hc; m6_split_fast
                                        · have hji : j2.toNat ≠ i.toNat := fun h =>
                                            (bne_iff_ne.mp hc) (BitVec.eq_of_toNat_eq h)
                                          have hj2_ws2 : j2.toNat < ws2.length := by omega
                                          have hrk1_n : (rk + 1#32).toNat = rk.toNat + 1 := by
                                            have hrk_lt : rk.toNat < arity.toNat := by
                                              rw [hrk_e, har_n]; split <;> omega
                                            bv_omega
                                          have hwr_n :
                                              (gc + 2#64 + rk.setWidth 64).toNat =
                                                gc.toNat + 2 + rk.toNat :=
                                            bv64_add_zext32 (k := 2) (by
                                              have hrk_lt : rk.toNat < arity.toNat := by
                                                rw [hrk_e, har_n]; split <;> omega
                                              have := hgc_ar; have := hg_cap; omega)
                                          have hwr_sc :
                                              (gc + 2#64 + rk.setWidth 64).toNat < scrw.length := by
                                            have hrk_lt : rk.toNat < arity.toNat := by
                                              rw [hrk_e, har_n]; split <;> omega
                                            have := hgc_ar; have := hg_cap
                                            rw [hwr_n, hscrlw]; omega
                                          c0_hsteps!
                                          refine ihw (j2 + 1#32, rk + 1#32, ()) m
                                            (by dsimp only; omega)
                                            ⟨scrw.set (gc + 2#64 + rk.setWidth 64).toNat
                                              (ws2[j2.toNat]'hj2_ws2 ^^^ 1#32),
                                             by simp [hscrlw], by omega,
                                             by rw [hj21_n, hrk1_n, hrk_e]
                                                split <;> split <;> omega,
                                             fun idx hidx => by
                                               rw [List.getElem?_set_ne (by omega)]
                                               exact hprefw idx hidx,
                                             by rw [List.getElem?_set_ne (by omega)]; exact hw0,
                                             by rw [List.getElem?_set_ne (by omega)]; exact hw1,
                                             fun k hk hkne => ?_, hm⟩
                                          by_cases hkj : k = j2.toNat
                                          · subst hkj
                                            have hset_lt :
                                                gc.toNat + 2 + (if j2.toNat < i.toNat then j2.toNat
                                                  else j2.toNat - 1) < scrw.length := by
                                              rw [hscrlw]; have := hgc_ar; have := hg_cap
                                              split <;> omega
                                            rw [hwr_n, hrk_e]
                                            rw [show (if j2.toNat ≤ i.toNat then j2.toNat
                                                  else j2.toNat - 1) =
                                                if j2.toNat < i.toNat then j2.toNat
                                                else j2.toNat - 1 by split <;> split <;> omega]
                                            rw [List.getElem?_set_self hset_lt,
                                              List.getElem?_eq_getElem hj2_ws2, Option.getD_some]
                                          · rw [List.getElem?_set_ne (by
                                              rw [hwr_n, hrk_e]; split <;> split <;> omega)]
                                            exact hwrhs k (by omega) hkne
                                        · have hji : j2.toNat = i.toNat :=
                                            congrArg BitVec.toNat (by simpa using hc)
                                          c0_hsteps!
                                          refine ihw (j2 + 1#32, rk, ()) mj2 (by dsimp only; omega)
                                            ⟨scrw, hscrlw, by omega,
                                             by rw [hj21_n, hrk_e]; split <;> split <;> omega,
                                             hprefw, hw0, hw1,
                                             fun k hk hkne => hwrhs k (by omega) hkne, hmj2⟩
                                      · have hj2_e : j2.toNat = usz.toNat := by
                                          simp only [BitVec.ult, decide_eq_false_iff_not] at hc
                                          omega
                                        rw [hj2_e] at hwrhs
                                        have har_bv : arity = BitVec.ofNat 32 (usz.toNat - 1) := by
                                          apply BitVec.eq_of_toNat_eq
                                          rw [har_n, bv32_ofNat_toNat (by omega)]
                                        have hgat := fid_andGate_of_emitted hu_lt3 hu_le65
                                          hu_cv hi_lt hlt_u hent_u (hlhs_eq ▸ hbins') (by omega)
                                          (hlhs_eq ▸ hw0) (har_bv ▸ hw1) hwrhs
                                        have hgl_next : (gc + 2#64 + arity.setWidth 64).toNat =
                                            gc.toNat + 2 + (usz.toNat - 1) := by
                                          rw [bv64_add_zext32 (k := 2)
                                            (by have := hgc_ar; have := hg_cap; omega), har_n]
                                        have hseq_new : FidGateSeqOk 64 F_cur s.core.cur_vars scrw
                                            (gc + 2#64 + arity.setWidth 64).toNat 0 := by
                                          rw [hgl_next]
                                          refine fidGateSeqOk_append_gate hprefw hseq_c ?_
                                            (by omega)
                                          refine .step ((show sb.core.cur_vars = s.core.cur_vars
                                            from hcv_p) ▸ hgat) ?_
                                          have hmword_ar :
                                              (arity &&& 0xFF#32).toNat = usz.toNat - 1 := by
                                            rw [BitVec.toNat_and, har_n,
                                              show (0xFF#32 : BitVec 32).toNat = 255 from rfl]
                                            simpa [Nat.mod_eq_of_lt
                                              (show usz.toNat - 1 < 256 by omega)]
                                              using Nat.and_two_pow_sub_one_eq_mod (usz.toNat - 1) 8
                                          simpa [hw1, hmword_ar] using FidGateSeqOk.done
                                        c0_hsteps!
                                        exact ihi (gc + 2#64 + arity.setWidth 64, i + 1#32, ()) mj2
                                          (by dsimp only; omega)
                                          ⟨scrw, hscrlw, by omega, by omega, by omega, hseq_new,
                                           hmj2⟩
                                    · clear hc; c0_hsteps!
                                      exact ihi (gc, i + 1#32, ()) mi (by dsimp only; omega)
                                        ⟨scrc, hscrl_c, hgc_lo, hgc_hi, by omega, hseq_c, hmi⟩
                                  · rintro B2 L2 rem2 ⟨j, ⟨⟩⟩ mj hB2 hL2 ⟨hmj_eq, hj_le, rfl, hseen⟩
                                    subst mj
                                    m6_split_fast
                                    · have hj_lt : j.toNat < usz.toNat := by
                                        simp only [BitVec.ult, decide_eq_true_eq] at hc; exact hc
                                      have hj1 : (j + 1#32).toNat = j.toNat + 1 := by bv_omega
                                      clear hc; c0_hsteps_nogrp; refine wp_join_group (ts := [])
                                        (fun () m_j => m_j = mi ∧
                                          ∀ k < (j + 1#32).toNat, k ≠ i.toNat →
                                            (cnfOfClauses F_cur).EntailsClause (cnfClause
                                              [litNeg lhs.toNat,
                                               litNeg (ws2[k]?.getD 0#32).toNat]))
                                        ?_ ?_
                                      · rintro _ ⟨⟩ m_j ⟨hmj2_eq, hseen'⟩; subst m_j; c0_hsteps!
                                        exact hL2 (usz.toNat - (j + 1#32).toNat) (j + 1#32, ()) mi
                                          (by omega) ⟨rfl, by omega, rfl, hseen'⟩
                                      · intro Jj hJj; m6_split_fast
                                        · have hji : j.toNat ≠ i.toNat := fun h =>
                                            (bne_iff_ne.mp hc) (BitVec.eq_of_toNat_eq h)
                                          have hj_ws2 : j.toNat < ws2.length := by omega
                                          c0_hsteps!; m3_call hHasBin
                                          refine ⟨c, F0, F_cur, sc_c, R, rfl, hlen_c, hwc_c, hmi,
                                            fun hb hhb => ?_⟩
                                          m6_split_fast
                                          · have hnew :
                                                (cnfOfClauses F_cur).EntailsClause (cnfClause
                                                  [litNeg lhs.toNat,
                                                   litNeg (ws2[j.toNat]?.getD 0#32).toNat]) := by
                                              have h0 := (hhb (by cases hc; rfl)).2.2.2.2
                                              simp only [sb, bv_zext32_toNat] at h0
                                              have h1 : (cnfOfClauses F_cur).EntailsClause
                                                  (cnfClause [(lhs ^^^ 1#32).toNat,
                                                    ((ws2[j.toNat]?.getD 0#32) ^^^ 1#32).toNat]) :=
                                                by
                                                dsimp only [lhs]
                                                rw [List.getElem?_eq_getElem hj_ws2,
                                                  Option.getD_some]
                                                exact h0
                                              rw [FullCongHelpers.bv32_xor1_eq_litNeg,
                                                FullCongHelpers.bv32_xor1_eq_litNeg] at h1
                                              exact h1
                                            c0_hsteps!
                                            exact hJj () mi ⟨rfl, fun k hk hkne => by
                                              rw [hj1] at hk
                                              by_cases hkj : k = j.toNat
                                              · subst hkj; exact hnew
                                              · exact hseen k (by omega) hkne⟩
                                          · c0_hsteps!
                                            exact hB2 (false, j, ()) mi ⟨rfl, fun hf => by cases hf⟩
                                        · have hji : j.toNat = i.toNat :=
                                            congrArg BitVec.toNat (by simpa using hc)
                                          c0_hsteps!
                                          exact hJj () mi ⟨rfl, fun k hk hkne =>
                                            hseen k (by omega) hkne⟩
                                    · have hj_e : j.toNat = usz.toNat := by
                                        simp only [BitVec.ult, decide_eq_false_iff_not] at hc; omega
                                      rw [hj_e] at hseen; c0_hsteps!
                                      exact hB2 (true, j, ()) mi ⟨rfl, fun _ => hseen⟩
                                  · intro _ L2 _ hL2; c0_hsteps!
                                    exact hL2 (usz.toNat - 0) (0#32, ()) mi
                                      ⟨rfl, Nat.zero_le _, rfl, fun _ h => by simp at h⟩
                                · clear hc; c0_hsteps!
                                  exact ihi (gc, i + 1#32, ()) mi (by dsimp only; omega)
                                    ⟨scrc, hscrl_c, hgc_lo, hgc_hi, by omega, hseq_c, hmi⟩
                              · clear hc; c0_hsteps!
                                exact hJg (gc, ()) mi
                                  ⟨{ sb with scratch := { sb.scratch with scratch_buf := scrc } },
                                   fullDenseInvW_with_scr hdb hscrl_c, hcv_p, hfl_p, hrep_p, hinc_p,
                                   har_p, hal_p, rfl, hgc_lo, hgc_hi, hseq_c, hmi⟩
                            · clear hc; c0_hsteps!
                              exact hJg (gc, ()) mi
                                ⟨{ sb with scratch := { sb.scratch with scratch_buf := scrc } },
                                 fullDenseInvW_with_scr hdb hscrl_c, hcv_p, hfl_p, hrep_p, hinc_p,
                                 har_p, hal_p, rfl, hgc_lo, hgc_hi, hseq_c, hmi⟩
                          · clear hc; c0_hsteps!; exact hjg0
                        · clear hc; c0_hsteps!; exact hjg0
                    · clear hc; c0_hsteps!
                      exact hJnext (g_len, ticks + 1#64, ()) mb
                        ⟨sb, hdb, hcv_p, hfl_p, hrep_p, hinc_p, har_p, hal_p, hgl_le, hseq_p, hmb⟩
                  · clear hc; c0_hsteps!
                    exact hJnext (g_len, ticks + 1#64, ()) mb
                      ⟨sb, hdb, hcv_p, hfl_p, hrep_p, hinc_p, har_p, hal_p, hgl_le, hseq_p, hmb⟩
                · clear hc; c0_hsteps!
                  exact hJnext (g_len, ticks + 1#64, ()) mb
                    ⟨sb, hdb, hcv_p, hfl_p, hrep_p, hinc_p, har_p, hal_p, hgl_le, hseq_p, hmb⟩
            · rintro B3 L3 rem3 ⟨usz, max_nbc, min_nbc, neg_p, k, ⟨⟩⟩ mk hB3 hL3
                ⟨ws2, hws2_l, hk_le, rfl, hu_65, hu_k, hu_cv, hlt_u, hneg_u,
                 ⟨idxs, hid_len, hid_nd, hid_lt, hws2_map, hcov_k⟩, hmk⟩
              m6_split_fast
              · have hk_lt : k.toNat < sz_bv.toNat := by
                  simp only [BitVec.ult, decide_eq_true_eq] at hc; exact hc
                have hk1_n : (k + 1#32).toNat = k.toNat + 1 := by bv_omega
                have hp3k_n : (p + 3#64 + k.setWidth 64).toNat = p.toNat + 3 + k.toNat :=
                  bv64_add_zext32 (k := 3) (by omega)
                have hp3k_arr : (p + 3#64 + k.setWidth 64).toNat < sp.core.arena.length := by omega
                let lk := sp.core.arena[(p + 3#64 + k.setWidth 64).toNat]'hp3k_arr
                have hlk_eq : lk = sp.core.arena[p.toNat + 3 + k.toNat]'(by omega) :=
                  list_getElem_congr hp3k_n hp3k_arr (by omega)
                have hlk_lt : lk.toNat < 2 * sp.core.cur_vars := by
                  have hmem_lk : lk.toNat ∈ fullArenaClauseLits sp p.toNat := by
                    unfold fullArenaClauseLits fullArenaClauseLitsCore
                    have hsz_szbv : fullArenaClauseSizeCore sp.core p.toNat = sz_bv.toNat := hsz_eq
                    have : p.toNat + 3 + fullArenaClauseSizeCore sp.core p.toNat ≤
                        sp.core.arena.length := by rw [hsz_szbv]; exact hbd_sz
                    simp only [List.mem_map]; refine ⟨lk, ?_, rfl⟩
                    have hk_s : k.toNat < fullArenaClauseSizeCore sp.core p.toNat := by
                      rw [hsz_szbv]; exact hk_lt
                    have hget : ((sp.core.arena.drop (p.toNat + 3)).take
                        (fullArenaClauseSizeCore sp.core p.toNat))[k.toNat]'(by
                          simp [List.length_take, List.length_drop]; omega) = lk := by
                      simp [List.getElem_take, List.getElem_drop, hlk_eq]
                    rw [← hget]; exact List.getElem_mem _
                  exact hdp.2.1.arena.lits_lt p.toNat hp_ref hng lk.toNat hmem_lk
                have hlk_v : (lk.setWidth 64).toNat < sp.core.vals.length := by
                  rw [bv_zext32_toNat]; omega
                have hlk_v' : lk.toNat < sp.core.vals.length := by
                  rw [bv_zext32_toNat] at hlk_v; exact hlk_v
                clear hc; m6_split_fast
                · c0_hsteps!
                  exact hB3 (usz, max_nbc, min_nbc, neg_p, true, k, ()) mk
                    ⟨ws2, hws2_l, (fun hf => by cases hf), hmk⟩
                · have hdom_lk : sp.core.vals[(lk.setWidth 64).toNat]'hlk_v = 0#8 ∨
                      sp.core.vals[(lk.setWidth 64).toNat]'hlk_v = 1#8 ∨
                      sp.core.vals[(lk.setWidth 64).toNat]'hlk_v = 0xFF#8 := by
                    have hdom_lk0 := hdp.2.1.vals_domain lk.toNat hlk_lt
                    rw [List.getElem?_eq_getElem hlk_v', Option.getD_some] at hdom_lk0
                    rw [list_getElem_congr (bv_zext32_toNat lk) hlk_v hlk_v']; exact hdom_lk0
                  have hnsgt : ¬ (0#32 : BitVec 32).slt
                      ((sp.core.vals[(lk.setWidth 64).toNat]'hlk_v).signExtend 32) = true := by
                    have hc0 : (0#32 : BitVec 32).slt
                        ((sp.core.vals[(lk.setWidth 64).toNat]'hlk_v).signExtend 32) = false := hc
                    rw [hc0]; decide
                  clear hc; m6_split_fast
                  · clear hc; m6_split_fast
                    · c0_hsteps!
                      exact hB3 (usz, max_nbc, min_nbc, neg_p, true, k, ()) mk
                        ⟨ws2, hws2_l, (fun hf => by cases hf), hmk⟩
                    · have hu_lt65 : usz.toNat < 65 := by
                        simp only [BitVec.ule, decide_eq_false_iff_not] at hc; bv_omega
                      clear hc; m6_split_fast
                      · c0_hsteps!
                        exact hB3 (usz, max_nbc, min_nbc, neg_p, true, k, ()) mk
                          ⟨ws2, hws2_l, (fun hf => by cases hf), hmk⟩
                      · have hu_lt_cv : usz.toNat < sp.core.cur_vars := by
                          rw [hcv_p]
                          simp only [BitVec.ule, decide_eq_false_iff_not, bv_zext32_toNat,
                            BitVec.toNat_ofNat] at hc
                          rw [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)] at hc; omega
                        have hu1_n : (usz + 1#32).toNat = usz.toNat + 1 := by bv_omega
                        have hu_ws2 : usz.toNat < ws2.length := by omega
                        have hu_ws2_64 : (usz.setWidth 64).toNat < ws2.length := by
                          rw [bv_zext32_toNat]; exact hu_ws2
                        let ws2' := ws2.set usz.toNat lk
                        have hlk_ws1 : (lk.setWidth 64).toNat < sp.scratch.work_stk1.length := by
                          rw [bv_zext32_toNat, hws1_pl]; exact Nat.lt_of_lt_of_le hlk_lt (by omega)
                        clear hc; m3_let
                        refine wp_store_sep
                          (FullArenaTactics.c0_store_full_work_stk2 lk hu_ws2_64 hmk) ?_
                        intro m_st hm_st
                        let sp2 : FullState :=
                          { sp with scratch := { sp.scratch with work_stk2 := ws2' } }
                        have hm2 : (FullMem c sp2 ⋆ R) m_st := by
                          simpa only [sp2, ws2', bv_zext32_toNat] using hm_st
                        have hlk_ws1' : (lk.setWidth 64).toNat < sp2.scratch.work_stk1.length :=
                          hlk_ws1
                        c0_hsteps_nogrp
                        refine wp_join_group (ts := [i32])
                          (fun (_mx, ()) mmx => mmx = m_st) ?_ ?_
                        · rintro _ ⟨mx', ⟨⟩⟩ mmx hmmx; rw [hmmx]
                          c0_hsteps_nogrp
                          refine wp_join_group (ts := [i32])
                            (fun (_mn, ()) mmn => mmn = m_st) ?_ ?_
                          · rintro _ ⟨mn', ⟨⟩⟩ mmn hmmn; rw [hmmn]
                            c0_hsteps_nogrp
                            refine wp_join_group (ts := [i32])
                              (fun (np', ()) mnp => mnp = m_st ∧
                                np' = (if (lk &&& 1#32) != 0#32 then neg_p ^^^ 1#32 else neg_p))
                              ?_ ?_
                            · rintro _ ⟨neg_p', ⟨⟩⟩ mnp ⟨hmnp, hnp'⟩; rw [hmnp, hnp']
                              c0_hsteps!
                              refine hL3 (sz_bv.toNat - (k + 1#32).toNat)
                                (usz + 1#32, _, _,
                                 (if (lk &&& 1#32) != 0#32 then neg_p ^^^ 1#32 else neg_p),
                                 k + 1#32, ()) m_st (by omega)
                                ⟨ws2', by simp [ws2', hws2_l], by omega, rfl, by omega, by omega,
                                 by omega, fun j hj => ?_, ?_, ?_, hm2⟩
                              · dsimp only [ws2']; by_cases hju : j = usz.toNat
                                · subst hju; rw [List.getElem?_set_self hu_ws2, Option.getD_some]
                                  exact hlk_lt
                                · rw [List.getElem?_set_ne (Ne.symm hju)]; exact hlt_u j (by omega)
                              · rw [hu1_n, List.range_succ, List.foldl_append, List.foldl_cons,
                                  List.foldl_nil]
                                have hfold_eq : ∀ n ≤ usz.toNat,
                                    List.foldl (fun acc i =>
                                      acc ^^^ ((ws2'[i]?.getD 0#32).toNat % 2)) 0 (List.range n) =
                                    List.foldl (fun acc i =>
                                      acc ^^^ ((ws2[i]?.getD 0#32).toNat % 2))
                                      0 (List.range n) := by
                                  intro n hn; induction n with
                                  | zero => rfl
                                  | succ n ih =>
                                    simp only [List.range_succ, List.foldl_append, List.foldl_cons,
                                      List.foldl_nil, ih (by omega)]
                                    congr 2; dsimp only [ws2']
                                    rw [List.getElem?_set_ne (by omega)]
                                rw [hfold_eq usz.toNat (Nat.le_refl _), ← hneg_u]
                                have hlast : ws2'[usz.toNat]?.getD 0#32 = lk := by
                                  dsimp only [ws2']
                                  rw [List.getElem?_set_self hu_ws2, Option.getD_some]
                                rw [hlast]; exact bv32_bit1_ne0_mod2
                              · refine ⟨idxs ++ [k.toNat], by simp [hid_len, hu1_n], ?_,
                                  fun q hq => ?_, fun j hj => ?_, fun q hq => ?_⟩
                                · rw [List.nodup_append]
                                  refine ⟨hid_nd, by simp, fun q hq b hb _ => ?_⟩
                                  cases hb with
                                  | head => have := hid_lt q hq; omega
                                  | tail _ ht => cases ht
                                · simp only [List.mem_append, List.mem_singleton] at hq
                                  rcases hq with hq | rfl
                                  · have := hid_lt q hq; omega
                                  · omega
                                · dsimp only [ws2']; rw [hu1_n] at hj
                                  by_cases hju : j = usz.toNat
                                  · subst hju; rw [List.getElem?_set_self hu_ws2]
                                    have hid_e :
                                        (idxs ++ [k.toNat])[usz.toNat]? = some k.toNat := by
                                      rw [List.getElem?_append_right (by omega), hid_len,
                                        Nat.sub_self]; simp
                                    rw [hid_e, Option.getD_some,
                                      List.getElem?_eq_getElem (by omega), hlk_eq]
                                  · rw [List.getElem?_set_ne (Ne.symm hju)]
                                    have hid_l : (idxs ++ [k.toNat])[j]? = idxs[j]? :=
                                      List.getElem?_append_left (by omega)
                                    rw [hid_l]; exact hws2_map j (by omega)
                                · simp only [List.mem_append, List.mem_singleton]
                                  by_cases hqk : q = k.toNat
                                  · subst hqk; exact Or.inl (Or.inr rfl)
                                  · rcases hcov_k q (by omega) with hin | hff
                                    · exact Or.inl (Or.inl hin)
                                    · exact Or.inr hff
                            · intro Jnp hJnp; m6_split_fast
                              · have hbnz : ((lk &&& 1#32) != 0#32) = true := hc
                                m3_let
                                exact hJnp (neg_p ^^^ 1#32, ()) m_st ⟨rfl, by rw [hbnz]; rfl⟩
                              · have hbnz : ((lk &&& 1#32) != 0#32) = false := hc
                                have hbz : ¬ ((lk &&& 1#32) != 0#32) = true := by
                                  rw [hbnz]; decide
                                m3_let
                                exact hJnp (neg_p, ()) m_st ⟨rfl, by rw [ite_eq_right hbz]⟩
                          · intro Jmn hJmn; m6_split_fast
                            · m3_let; exact hJmn (_, ()) m_st rfl
                            · m3_let; exact hJmn (_, ()) m_st rfl
                        · intro Jmx hJmx; m6_split_fast
                          · m3_let; exact hJmx (_, ()) m_st rfl
                          · m3_let; exact hJmx (_, ()) m_st rfl
                  · have hne0 : sp.core.vals[(lk.setWidth 64).toNat]'hlk_v ≠ 0#8 := by
                      apply FullM3CongBva.bv8_ne0_of_signExtend32 hdom_lk
                      exact beq_eq_false_iff_ne.mp hc
                    have hff_lk : sp.core.vals[(lk.setWidth 64).toNat]?.getD 0#8 = 0xFF#8 := by
                      rw [List.getElem?_eq_getElem hlk_v, Option.getD_some]
                      exact FullM3CongBva.bv8_ne0_not_signExtend32_sgt0_eqff hdom_lk hne0 hnsgt
                    c0_hsteps!
                    refine hL3 (sz_bv.toNat - (k + 1#32).toNat)
                      (usz, max_nbc, min_nbc, neg_p, k + 1#32, ()) mk (by omega)
                      ⟨ws2, hws2_l, by omega, rfl, hu_65, by omega, hu_cv, hlt_u, hneg_u,
                       ⟨idxs, hid_len, hid_nd, fun q hq => by have := hid_lt q hq; omega,
                        hws2_map, fun q hq => ?_⟩, hmk⟩
                    by_cases hqk : q = k.toNat
                    · subst hqk; right
                      have hk_ar : sp.core.arena[p.toNat + 3 + k.toNat]?.getD 0#32 = lk := by
                        rw [List.getElem?_eq_getElem (by omega), Option.getD_some, hlk_eq]
                      rw [hk_ar]; rw [bv_zext32_toNat] at hff_lk; exact hff_lk
                    · exact hcov_k q (by omega)
              · have hk_e : k.toNat = sz_bv.toNat := by
                  simp only [BitVec.ult, decide_eq_false_iff_not] at hc
                  change ¬ k.toNat < sz_bv.toNat at hc; omega
                have hsz_bv : fullArenaClauseSizeCore sp.core p.toNat = sz_bv.toNat := hsz_eq
                have hcov_all : ∀ l ∈ fullArenaClauseLits sp p.toNat,
                    sp.core.vals[l]?.getD 0#8 = 0xFF#8 ∨ l ∈
                      ((List.range usz.toNat).map fun j => (ws2[j]?.getD 0#32).toNat) := by
                  intro l hl
                  unfold fullArenaClauseLits fullArenaClauseLitsCore at hl; rw [hsz_bv] at hl
                  rw [List.mem_map] at hl; obtain ⟨bv, hbv, rfl⟩ := hl
                  obtain ⟨q, hq, hget⟩ := List.mem_iff_getElem.mp hbv
                  rw [List.length_take, List.length_drop, Nat.min_eq_left (by omega)] at hq
                  have hq_lt : q < sz_bv.toNat := hq
                  have hbd_q : p.toNat + 3 + q < sp.core.arena.length := by have := hbd_sz; omega
                  rw [List.getElem_take, List.getElem_drop] at hget
                  rcases hcov_k q (hk_e ▸ hq_lt) with hin | hff
                  · right; obtain ⟨j, hj, hgetj⟩ := List.mem_iff_getElem.mp hin
                    have hj_u : j < usz.toNat := by omega
                    have hm_j := hws2_map j hj_u
                    have hid_j : (idxs[j]?.getD 0) = q := by
                      rw [List.getElem?_eq_getElem hj, Option.getD_some, hgetj]
                    rw [hid_j, List.getElem?_eq_getElem (by omega),
                      List.getElem?_eq_getElem hbd_q, hget] at hm_j
                    rw [List.mem_map]; refine ⟨j, List.mem_range.mpr hj_u, ?_⟩
                    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                    exact congrArg BitVec.toNat (Option.some.inj hm_j)
                  · left; rw [List.getElem?_eq_getElem hbd_q, Option.getD_some, hget] at hff
                    exact hff
                have hent_u :=
                  unassigned_clause_entails hdp.2.1 hdp.2.2.2.2.2.1 hp_ref hng hcov_all
                have hnd_u : (idxs.map fun q =>
                    (sp.core.arena[p.toNat + 3 + q]?.getD 0#32).toNat / 2).Nodup := by
                  have hnd_sp := hdp.2.2.2.1 p.toNat hp_ref hng
                  have har_lits : fullArenaClauseLits sp p.toNat =
                      ((List.range sz_bv.toNat).map fun q =>
                        (sp.core.arena[p.toNat + 3 + q]?.getD 0#32).toNat) := by
                    unfold fullArenaClauseLits fullArenaClauseLitsCore; rw [hsz_bv]
                    apply List.ext_getElem
                    · simp only [List.length_map, List.length_take, List.length_drop,
                        List.length_range]
                      exact Nat.min_eq_left (by omega)
                    · intro q hq _
                      simp only [List.length_map, List.length_take, List.length_drop] at hq
                      rw [Nat.min_eq_left (by omega)] at hq
                      have hbd_q : p.toNat + 3 + q < sp.core.arena.length := by
                        have := hbd_sz; omega
                      simp only [List.getElem_map, List.getElem_take, List.getElem_drop,
                        List.getElem_range]
                      rw [List.getElem?_eq_getElem hbd_q, Option.getD_some]
                  rw [har_lits, List.map_map] at hnd_sp
                  exact list_nodup_filter_map
                    (fun q => (sp.core.arena[p.toNat + 3 + q]?.getD 0#32).toNat / 2)
                    hnd_sp hid_nd (fun q hq => by rw [← hk_e]; exact hid_lt q hq) (fun _ => rfl)
                have hdiff_u : ∀ j < usz.toNat, ∀ j2 < usz.toNat, j ≠ j2 →
                    (ws2[j]?.getD 0#32).toNat / 2 ≠ (ws2[j2]?.getD 0#32).toNat / 2 := by
                  intro j hj j2 hj2 hne
                  have hm1 := hws2_map j hj; have hm2 := hws2_map j2 hj2
                  rw [hm1, hm2]
                  have hind := nodup_getElem_inj hnd_u j j2 (by simp [hid_len, hj])
                    (by simp [hid_len, hj2])
                  intro heq
                  have hij1 : idxs[j]?.getD 0 = idxs[j]'(by simp [hid_len, hj]) := by
                    rw [List.getElem?_eq_getElem (by simp [hid_len, hj]), Option.getD_some]
                  have hij2 : idxs[j2]?.getD 0 = idxs[j2]'(by simp [hid_len, hj2]) := by
                    rw [List.getElem?_eq_getElem (by simp [hid_len, hj2]), Option.getD_some]
                  rw [hij1, hij2] at heq
                  exact hne (hind (by simp only [List.getElem_map]; exact heq))
                c0_hsteps!
                exact hB3 (usz, max_nbc, min_nbc, neg_p, false, k, ()) mk
                  ⟨ws2, hws2_l, fun _ => ⟨hsz3, hu_65, by omega, hu_cv, hlt_u, hneg_u,
                    ⟨idxs, hid_len, hid_nd, fun q hq => by rw [← hk_e]; exact hid_lt q hq,
                     fun j hj _ => hws2_map j hj,
                     fun q hq => by rw [← hk_e] at hq; exact hcov_k q hq⟩,
                    hdiff_u, hent_u⟩, hmk⟩
            · intro _ L3 _ hL3; c0_hsteps!
              exact hL3 (sz_bv.toNat - 0) (0#32, 0#32, 0xFFFFFFFF#32, 0#32, 0#32, ()) mp
                ⟨sp.scratch.work_stk2, hws2_pl, Nat.zero_le _, rfl, Nat.zero_le _, Nat.zero_le _,
                 Nat.zero_le _, (fun _ h => by cases h), (by simp),
                 ⟨[], rfl, .nil, (fun _ h => by cases h), (fun _ h => by cases h),
                  (fun _ h => by cases h)⟩, hmp⟩
          · clear hc; c0_hsteps!; exact hjnext_same
        · clear hc; c0_hsteps!; exact hjnext_same
      · clear hc; c0_hsteps!; exact hq_done
    · clear hc; c0_hsteps!; exact hq_done
  · clear hc; c0_hsteps!; exact hq_done

/-! ## 3. `full_cong_and_match_wp` (`fidCongAndMatchSpec`, 64-bit mask up to arity `64`) -/

theorem full_cong_and_match_wp (Γ : Env)
    (hFind : ∀ a m Q X, FullCongSpecs.fullCongFindSpec a m Q X →
      Γ "full_cong_find" [i64, i32] [i32] a m Q X) :
    ∀ a m Q X, fidCongAndMatchSpec a m Q X →
      Func.wp Γ full_cong_and_match_body a m Q X := by
  rintro ⟨h, ent, ua, ⟨⟩⟩ m0 Q X
    ⟨maxA, c, F0, F_cur, s, scr0, g_len, R, hmax64, rfl, hlen, hw, hcl0, hrepr0, hg_cap, hpref,
     hgat, htag0, hua_cv, hm0, hQ⟩
  have hsc := c.hscr; have hmx := c.hmaxv; unfold dimacsBound at hsc hmx
  have hcv_le := hlen.core_ok.cur_vars_le
  have hrl0 := hlen.core_ok.repr_len
  have htmpl0 := hlen.core_ok.tmp_len_arr
  have hscrl0 := hlen.scratch_ok.scratch_buf_len
  obtain ⟨lhs_ent, mword, he0, he1, _, hbd_e, _, hmax_e, hrhs_e, hsem_e⟩ := hgat
  have htag0' : (mword >>> 28).toNat = 0 := by
    rw [he1, Option.getD_some] at htag0; simpa using congrArg BitVec.toNat htag0
  obtain ⟨_, ha2_e, hand_e⟩ | ⟨ht_ne, _⟩ | ⟨ht_ne, _⟩ := hsem_e <;> (try omega)
  let ea := mword &&& 0xFF#32
  have ha_eq : ea.toNat = (mword &&& 0xFF#32).toNat := rfl
  let rhs := ((scr0.drop (ent.toNat + 2)).take ea.toNat).map BitVec.toNat
  have hrl_rhs : rhs.length = ea.toNat := by
    simp only [rhs, List.length_map, List.length_take, List.length_drop]
    rcases Nat.eq_zero_or_pos ea.toNat with hz | hpos
    · exact Nat.min_eq_left (by omega)
    · obtain ⟨_, hr, _⟩ := hrhs_e (ea.toNat - 1) (by rw [ha_eq] at *; omega)
      have := (List.getElem?_eq_some_iff.mp hr).1; omega
  have he1_n : (ent.setWidth 64 + 1).toNat = ent.toNat + 1 := by
    rw [BitVec.toNat_add, bv_zext32_toNat]
    have h1 : (1 : BitVec 64).toNat = 1 := rfl
    rw [h1]; exact Nat.mod_eq_of_lt (by omega)
  have he1_arr : (ent.setWidth 64 + 1).toNat < s.scratch.scratch_buf.length := by omega
  have hst_e1 : s.scratch.scratch_buf[(ent.setWidth 64 + 1).toNat]'he1_arr = mword := by
    have h := (hpref (ent.toNat + 1) (by omega)).trans he1
    rw [← he1_n, List.getElem?_eq_getElem he1_arr] at h; exact Option.some.inj h
  m6_split_fast
  · m6_steps; exact hQ false s.core.repr m0 hrl0 hrepr0 (fun h => by cases h) hm0
  · have h2_le_ua : 2 ≤ ua.toNat := by
      have h2_val : ((2 : BitVec 32).toNat) = 2 := rfl
      simp only [BitVec.ult, h2_val, decide_eq_false_iff_not] at hc; omega
    m6_split_fast
    · m6_steps; exact hQ false s.core.repr m0 hrl0 hrepr0 (fun h => by cases h) hm0
    · have hua_le_64 : ua.toNat ≤ 64 := by
        have h64_val : ((64 : BitVec 32).toNat) = 64 := rfl
        simp only [BitVec.ult, h64_val, decide_eq_false_iff_not] at hc; omega
      m6_steps
      refine wp_loop_inv (ts := [i64, i32])
        (fun (mask, j, ()) mj => ∃ reprj : List (BitVec 32),
          reprj.length = 2 * c.max_vars ∧ j.toNat ≤ ea.toNat ∧
          FullCongReprInv F_cur (2 * s.core.cur_vars) reprj ∧
          (∀ p (hp : p < j.toNat), ∃ er < 2 * s.core.cur_vars,
            LitEquiv (cnfOfClauses F_cur) (rhs[p]?.getD 0) er ∧
            (s.core.vals[er]?.getD 0#8 = 1#8 ∨
              ∃ k < ua.toNat, er = (s.core.tmp[k]?.getD 0#32).toNat)) ∧
          (∀ b < 64, mask.toNat.testBit b = true → b < ua.toNat ∧
            ∃ p < j.toNat, LitEquiv (cnfOfClauses F_cur)
              (rhs[p]?.getD 0) (s.core.tmp[b]?.getD 0#32).toNat) ∧
          (FullMem c { s with core := { s.core with repr := reprj } } ⋆ R) mj)
        (fun (_, j, ()) _ => ea.toNat - j.toNat)
        (fun J hJ => by
          m6_let
          exact hJ (0#64, 0#32, ()) m0 ⟨s.core.repr, hrl0, Nat.zero_le _, hrepr0,
            fun _ h => absurd h (by simp), fun _ _ h => by simp at h, hm0⟩)
        (fun J (mask, j, ()) mj ⟨reprj, hrlj, hj_le, hreprj, hfwdj, hbwdj, hmj⟩ ihj => ?_)
      let stj : FullState := { s with core := { s.core with repr := reprj } }
      have hlenj : stj.LengthsOk c := ⟨{ hlen.core_ok with repr_len := hrlj }, hlen.scratch_ok⟩
      have hwj : FullWitnessInv c F0 F_cur stj.core := fullWitnessInv_with_repr hw reprj
      m6_split_fast
      · have hj_lt : j.toNat < ea.toNat := by
          simp only [BitVec.ult, decide_eq_true_eq] at hc; rw [hst_e1] at hc; exact hc
        obtain ⟨rv, hrv_get, hrv_lt⟩ := hrhs_e j.toNat hj_lt
        have hrhs_j : rhs[j.toNat]?.getD 0 = rv.toNat := by
          simp only [rhs, List.getElem?_map, List.getElem?_take,
            ite_eq_left (by omega : j.toNat < ea.toNat), List.getElem?_drop, hrv_get]
          rfl
        have he2j_lt : ent.toNat + 2 + j.toNat < c.scratch_cap := by rw [ha_eq] at *; omega
        have he2j_n : (ent.setWidth 64 + 2 + j.setWidth 64).toNat = ent.toNat + 2 + j.toNat :=
          bv64_add_zext32 (k := 2) (by rw [bv_zext32_toNat]; omega)
        have he2j_arr : (ent.setWidth 64 + 2 + j.setWidth 64).toNat <
            stj.scratch.scratch_buf.length := by
          rw [he2j_n]; dsimp [stj]; exact Nat.lt_of_lt_of_le he2j_lt (Nat.le_of_eq hscrl0.symm)
        have hst_e2j : stj.scratch.scratch_buf[(ent.setWidth 64 + 2 + j.setWidth 64).toNat]'
            he2j_arr = rv := by
          have h := (hpref (ent.toNat + 2 + j.toNat) (by omega)).trans hrv_get
          rw [← he2j_n, List.getElem?_eq_getElem he2j_arr] at h; exact Option.some.inj h
        have hj1_n : (j + 1#32).toNat = j.toNat + 1 := bv32_add1_lt_of (by omega)
        m6_steps; m6_call hFind
        refine ⟨F_cur, 2 * s.core.cur_vars, reprj, FullReprRest c stj ⋆ R, hreprj,
          by rw [hst_e2j]; exact hrv_lt, focus_full_repr hmj,
          fun er repr_e me hrl_e hrepr_e _ her_lt her_eqv hme => ?_⟩
        let ste : FullState := { stj with core := { stj.core with repr := repr_e } }
        have hme' : (FullMem c ste ⋆ R) me := unfocus_full_repr hme; clear hme
        have hw_e : FullWitnessInv c F0 F_cur ste.core := fullWitnessInv_with_repr hwj repr_e
        have her_vals : (er.setWidth 64).toNat < ste.core.vals.length := by
          rw [bv_zext32_toNat]; dsimp [ste, stj]; rw [hlen.core_ok.vals_len]; omega
        have her_vals' : er.toNat < ste.core.vals.length := by
          rw [bv_zext32_toNat] at her_vals; exact her_vals
        have hrv_er_eqv : LitEquiv (cnfOfClauses F_cur) (rhs[j.toNat]?.getD 0) er.toNat := by
          rw [hrhs_j]; rwa [hst_e2j] at her_eqv
        have hev_dom : ste.core.vals[er.toNat]'her_vals' = 0#8 ∨
            ste.core.vals[er.toNat]'her_vals' = 1#8 ∨
            ste.core.vals[er.toNat]'her_vals' = 0xFF#8 := by
          have hd := hw_e.vals_domain er.toNat her_lt
          rwa [List.getElem?_eq_getElem her_vals', Option.getD_some] at hd
        m6_split_fast
        · m6_steps
          exact hQ false repr_e me (by omega) hrepr_e (fun h => by cases h) hme'
        · have hev_nslt : ¬ (ste.core.vals[er.toNat]'her_vals').slt 0#8 = true :=
            bv8_not_slt0_of_signExtend32_nslt0 hev_dom (by
              rw [list_getElem_congr (bv_zext32_toNat er) her_vals her_vals'] at hc; exact hc)
          m6_split_fast
          · m6_to_group
            refine wp_loop_break_group (brkTs := [i64, .bool, i32]) (lpTs := [i32])
              (fun (mask_b, found, _, ()) mb => mb = me ∧
                (found = true → ∃ k < ua.toNat, er = (s.core.tmp[k]?.getD 0#32) ∧
                  ∀ b < 64, mask_b.toNat.testBit b = true → b < ua.toNat ∧
                    (b = k ∨ ∃ p < j.toNat, LitEquiv (cnfOfClauses F_cur)
                      (rhs[p]?.getD 0) (s.core.tmp[b]?.getD 0#32).toNat)))
              (fun rem (k, ()) mk => mk = me ∧ k.toNat ≤ ua.toNat ∧ rem = ua.toNat - k.toNat)
              ?_ ?_ ?_
            · rintro _ ⟨mask_b, found, _, ⟨⟩⟩ mb ⟨hmb_eq, hfb⟩
              subst mb
              m6_split_fast
              · obtain ⟨k, hk_lt, htmp_k, hmask_b⟩ := hfb hc
                m6_steps
                refine ihj (mask_b, j + 1#32, ()) me (by dsimp only; omega)
                  ⟨repr_e, by omega, by omega, hrepr_e, ?_, ?_, hme'⟩
                · intro p hp; rw [hj1_n] at hp
                  by_cases hpj : p = j.toNat
                  · subst hpj; refine ⟨er.toNat, her_lt, hrv_er_eqv, Or.inr ⟨k, hk_lt, ?_⟩⟩
                    rw [htmp_k]
                  · exact hfwdj p (by omega)
                · intro b hb htb
                  obtain ⟨hb_ua, hbk | ⟨p, hp, heq⟩⟩ := hmask_b b hb htb
                  · refine ⟨hb_ua, j.toNat, by omega, ?_⟩; subst hbk; rwa [← htmp_k]
                  · exact ⟨hb_ua, p, by omega, heq⟩
              · m6_steps
                exact hQ false repr_e me (by omega) hrepr_e (fun h => by cases h) hme'
            · rintro Bk Lk rem ⟨k, ⟨⟩⟩ mk hBk hLk ⟨hmk_eq, hk_le, rfl⟩
              subst mk
              m6_split_fast
              · have hk_lt : k.toNat < ua.toNat := by
                  simp only [BitVec.ult, decide_eq_true_eq] at hc; exact hc
                have hk_tmp : (k.setWidth 64).toNat < ste.core.tmp.length := by
                  rw [bv_zext32_toNat]; dsimp [ste, stj]; omega
                have hk_tmp' : k.toNat < ste.core.tmp.length := by
                  rw [bv_zext32_toNat] at hk_tmp; exact hk_tmp
                have hk1_n : (k + 1#32).toNat = k.toNat + 1 := bv32_add1_lt_of (by omega)
                m6_split_fast
                · have htmp_eq : s.core.tmp[k.toNat]?.getD 0#32 = er := by
                    have h1 : ste.core.tmp[k.toNat]'hk_tmp' = er := by
                      have hc' := beq_iff_eq.mp hc
                      rw [list_getElem_congr (bv_zext32_toNat k) hk_tmp hk_tmp'] at hc'; exact hc'
                    change s.core.tmp[k.toNat]'_ = er at h1
                    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; exact h1
                  have hk_64 : k.toNat < 64 := by omega
                  m6_steps
                  have hkm : ((1 : BitVec 64) <<< ((k.setWidth 64).toNat % 64)) =
                      1#64 <<< BitVec.ofNat 64 k.toNat := by
                    rw [bv_zext32_toNat, Nat.mod_eq_of_lt hk_64]
                    change (1#64 : BitVec 64) <<< k.toNat =
                      (1#64 : BitVec 64) <<< (BitVec.ofNat 64 k.toNat).toNat
                    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
                  rw [hkm]
                  refine hBk (mask ||| (1#64 <<< BitVec.ofNat 64 k.toNat), true, k, ()) me
                    ⟨rfl, fun _ => ⟨k.toNat, hk_lt, htmp_eq.symm, fun b hb htb => ?_⟩⟩
                  rw [bv64_or_shl_testBit mask hk_64 b, Bool.or_eq_true,
                    decide_eq_true_eq] at htb
                  rcases htb with htb | rfl
                  · obtain ⟨hb_ua, p, hp, heq⟩ := hbwdj b hb htb
                    exact ⟨hb_ua, Or.inr ⟨p, hp, heq⟩⟩
                  · exact ⟨hk_lt, Or.inl rfl⟩
                · m6_steps
                  exact hLk (ua.toNat - (k + 1#32).toNat) (k + 1#32, ()) me (by omega)
                    ⟨rfl, by omega, rfl⟩
              · m6_steps; exact hBk (mask, false, k, ()) me ⟨rfl, fun h => by cases h⟩
            · intro _ Lk _ hLk; m6_let; exact hLk ua.toNat (0#32, ()) me ⟨rfl, Nat.zero_le _, rfl⟩
          · have hev_eq1 : s.core.vals[er.toNat]?.getD 0#8 = 1#8 := by
              have hne0 : (ste.core.vals[er.toNat]'her_vals').signExtend 32 ≠ 0#32 := by
                have hc' := beq_eq_false_iff_ne.mp hc
                rw [list_getElem_congr (bv_zext32_toNat er) her_vals her_vals'] at hc'; exact hc'
              have h1 := bv8_eq1_of_signExtend32_ne0_nslt0 hev_dom hne0 hev_nslt
              rw [List.getElem?_eq_getElem (by rw [hlen.core_ok.vals_len]; omega), Option.getD_some]
              exact h1
            m6_steps
            refine ihj (mask, j + 1#32, ()) me (by dsimp only; omega)
              ⟨repr_e, by omega, by omega, hrepr_e, ?_, ?_, hme'⟩
            · intro p hp; rw [hj1_n] at hp
              by_cases hpj : p = j.toNat
              · subst hpj; exact ⟨er.toNat, her_lt, hrv_er_eqv, Or.inl hev_eq1⟩
              · exact hfwdj p (by omega)
            · intro b hb htb
              obtain ⟨hb_ua, p, hp, heq⟩ := hbwdj b hb htb
              exact ⟨hb_ua, p, by omega, heq⟩
      · have hj_eq : j.toNat = ea.toNat := by
          simp only [BitVec.ult, decide_eq_false_iff_not] at hc; rw [hst_e1] at hc
          change ¬ j.toNat < ea.toNat at hc; omega
        rw [hj_eq] at hfwdj hbwdj
        m6_to_group
        refine wp_join_group (ts := [i64])
          (fun (full_mask, ()) mf => mf = mj ∧
            ∀ k < ua.toNat, full_mask.toNat.testBit k = true)
          ?_ ?_
        · rintro _ ⟨full_mask, ⟨⟩⟩ mf ⟨hmf, hfm_bits⟩
          rw [hmf]; m6_steps
          refine hQ (mask == full_mask) reprj mj hrlj hreprj ?_ hmj
          intro htrue
          have hm_eq : mask = full_mask := beq_iff_eq.mp htrue
          refine ⟨h2_le_ua, hua_le_64, ?_⟩
          rw [he0, Option.getD_some]
          refine andMatch_sound_equiv hwj hcl0 hand_e ?_ ?_
          · intro p hp
            have hp' : p < ea.toNat := by rw [← hrl_rhs]; exact hp
            have h1 := hfwdj p hp'; dsimp only [rhs] at h1
            rw [List.getElem?_eq_getElem hp, Option.getD_some] at h1; exact h1
          · intro k hk
            have htb : mask.toNat.testBit k = true := by rw [hm_eq]; exact hfm_bits k hk
            have ⟨_, p, hp, heq⟩ := hbwdj k (by omega) htb
            rw [← hrl_rhs] at hp; exact ⟨p, hp, heq⟩
        · intro Jf hJf; m6_split_fast
          · have hua64 : ua = 64#32 := beq_iff_eq.mp hc
            m6_let
            refine hJf (0xFFFFFFFFFFFFFFFF#64, ()) mj ⟨rfl, fun k hk => ?_⟩
            have := testBit_full_mask_iff64 h2_le_ua hua_le_64 hk
            simpa [hua64] using this
          · have hua_ne : ua ≠ 64#32 := beq_eq_false_iff_ne.mp hc
            have hua_lt64 : ua.toNat < 64 := by
              have : ua.toNat ≠ 64 := fun he => hua_ne (BitVec.eq_of_toNat_eq he)
              omega
            m6_let
            refine hJf (((1#64 <<< ((ua.setWidth 64).toNat % 64)) - 1#64), ()) mj
              ⟨rfl, fun k hk => ?_⟩
            have hmod : (ua.setWidth 64).toNat % 64 = ua.toNat := by
              rw [bv_zext32_toNat, Nat.mod_eq_of_lt hua_lt64]
            rw [hmod]
            have htb := testBit_full_mask_iff64 h2_le_ua hua_le_64 hk
            have hne' : ¬ (ua = 64#32) := hua_ne
            rw [ite_eq_right hne'] at htb
            have hshl_eq : (1#64 <<< ua.setWidth 64 : BitVec 64) = 1#64 <<< ua.toNat := by
              change 1#64 <<< (ua.setWidth 64).toNat = 1#64 <<< ua.toNat
              rw [bv_zext32_toNat]
            rwa [hshl_eq] at htb

end LeanQbe.T.Examples.Kissat.FullFidelityCong
