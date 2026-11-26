/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep12BProofSpec
import LeanQbe.T.Examples.Kissat.FullCongLemmas1
import LeanQbe.T.Examples.Kissat.FullCongLemmas2
import LeanQbe.T.Examples.Kissat.FullM6CongSubstProof2a
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb

/-!
# Kissat Fidelity Step 12B — Congruence Proofs Part 1b (`FullFidelityStep12BProofCong1b`)

Parametric `(Γ : Env)` `Func.wp` proofs (`public section`, `0` `@[expose]` on theorems/lemmas,
`0` `import all`, `std3`, `XPost`-polymorphic) for:
1. `full_cong_extract_from_fid_s12b_wp` (`step12BCongExtractFromSpec`, two-pass extraction: Pass 1
   narrow AND `≤ 64` + XOR/ITE preserving `FidGateSeqOk 64` and recording wide `66 ≤ usz ≤ 1e6 + 1`
   clause refs in `red_refs`, Pass 2 wide AND emission via `full_cong_extract_and_clause_fid`)
2. `full_cong_extract_s12b_wp` (`step12BCongExtractSpec`, wrapper at `g_start = 0`)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep12B

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullCongHelpers
open LeanQbe.T.Examples.Kissat.FullM3CongBva
open LeanQbe.T.Examples.Kissat.FullM6CongSubst
open LeanQbe.T.Examples.Kissat.FullFidelityCong
open scoped LeanQbe.T.Examples.Kissat.FullM3CongBva.M3HeadTactics
open scoped LeanQbe.T.Examples.Kissat.FullM6CongSubst.M6HeadTactics
open scoped FullArenaTactics Full.FullCongTactics
open Kraken.Bedrock2.Test

/-! ## 1. Local Helpers -/

section Helpers

private theorem s12b_watchBounds_of_dense {c : FullCfg} {F0 : CNF Nat}
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

private theorem s12b_denseInvW_with_ws1 {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hd : FullDenseInvW c F0 F_cur s)
    {ws1' : List (BitVec 32)} (hl1 : ws1'.length = 2 * c.max_vars) :
    FullDenseInvW c F0 F_cur { s with scratch := { s.scratch with work_stk1 := ws1' } } :=
  ⟨⟨hd.1.core_ok, { hd.1.scratch_ok with work_stk1_len := hl1 }⟩,
   hd.2.1, hd.2.2.1, hd.2.2.2.1, hd.2.2.2.2.1, hd.2.2.2.2.2.1, hd.2.2.2.2.2.2⟩

private theorem s12b_denseInvW_with_ws2 {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hd : FullDenseInvW c F0 F_cur s)
    {ws2' : List (BitVec 32)} (hl : ws2'.length = 2 * c.max_vars) :
    FullDenseInvW c F0 F_cur { s with scratch := { s.scratch with work_stk2 := ws2' } } :=
  ⟨⟨hd.1.core_ok, { hd.1.scratch_ok with work_stk2_len := hl }⟩,
   hd.2.1, hd.2.2.1, hd.2.2.2.1, hd.2.2.2.2.1, hd.2.2.2.2.2.1, hd.2.2.2.2.2.2⟩

private theorem s12b_denseInvW_with_scr {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hd : FullDenseInvW c F0 F_cur s)
    {scr' : List (BitVec 32)} (hl : scr'.length = c.scratch_cap) :
    FullDenseInvW c F0 F_cur { s with scratch := { s.scratch with scratch_buf := scr' } } :=
  ⟨⟨hd.1.core_ok, { hd.1.scratch_ok with scratch_buf_len := hl }⟩,
   hd.2.1, hd.2.2.1, hd.2.2.2.1, hd.2.2.2.2.1, hd.2.2.2.2.2.1, hd.2.2.2.2.2.2⟩

private theorem s12b_denseInvW_with_rsz {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hd : FullDenseInvW c F0 F_cur s)
    (rsz' : BitVec 64) :
    FullDenseInvW c F0 F_cur { s with scratch := { s.scratch with res_sz := rsz' } } :=
  ⟨⟨hd.1.core_ok, { hd.1.scratch_ok with }⟩,
   hd.2.1, hd.2.2.1, hd.2.2.2.1,
   fullExtScratchOk_of_eq hd.2.2.2.2.1 rfl rfl rfl rfl, hd.2.2.2.2.2.1, hd.2.2.2.2.2.2⟩

private theorem s12b_denseInvW_with_rr {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hd : FullDenseInvW c F0 F_cur s)
    {rr' : List (BitVec 32)} (hl : rr'.length = c.red_cap) :
    FullDenseInvW c F0 F_cur { s with scratch := { s.scratch with red_refs := rr' } } :=
  ⟨⟨hd.1.core_ok, { hd.1.scratch_ok with red_refs_len := hl }⟩,
   hd.2.1, hd.2.2.1, hd.2.2.2.1,
   fullExtScratchOk_of_eq hd.2.2.2.2.1 rfl rfl rfl rfl, hd.2.2.2.2.2.1, hd.2.2.2.2.2.2⟩

private theorem s12b_core_fields_of_tmp_lm {a b : FullCoreState}
    (h : { a with tmp := b.tmp, lit_mark := b.lit_mark } = b) :
    a.inconsistent = b.inconsistent ∧ a.arena = b.arena ∧ a.arena_len = b.arena_len ∧
    a.cur_vars = b.cur_vars ∧ a.cur_level = b.cur_level ∧ a.dense_mode = b.dense_mode ∧
    a.fuel = b.fuel ∧ a.repr = b.repr ∧
    ({ b with tmp := a.tmp, lit_mark := a.lit_mark } : FullCoreState) = a := by
  cases a; cases b; cases h; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem s12b_scr_fields_of_buf {a b : FullScratch}
    (h : { a with scratch_buf := b.scratch_buf } = b) :
    a.last_learned = b.last_learned ∧ a.extend_len = b.extend_len ∧ a.red_refs = b.red_refs := by
  cases a; cases b; cases h; exact ⟨rfl, rfl, rfl⟩

private theorem s12b_denseInvW_of_xorK {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s s' : FullState} (hd : FullDenseInvW c F0 F_cur s)
    (hlen' : s'.LengthsOk c)
    (hce : { s'.core with tmp := s.core.tmp, lit_mark := s.core.lit_mark } = s.core)
    (hse : { s'.scratch with scratch_buf := s.scratch.scratch_buf } = s.scratch)
    (hmk' : FullLitMarksClear c s') :
    FullDenseInvW c F0 F_cur s' := by
  obtain ⟨_, har, hal, _, hcl, hdm, _, _, hkeq⟩ := s12b_core_fields_of_tmp_lm hce
  obtain ⟨hll, hext, _⟩ := s12b_scr_fields_of_buf hse
  have hnd' := fullArenaVarsNodup_of_eq hd.2.2.2.1 har hal
  have hext' := fullExtScratchOk_of_eq hd.2.2.2.2.1 har hal hll hext
  have hw_tm : FullWitnessInv c F0 F_cur
      { s.core with tmp := s'.core.tmp, lit_mark := s'.core.lit_mark } :=
    { hd.2.1 with
      arena := { hd.2.1.arena with len_ok := hd.2.1.arena.len_ok }
      watches := hd.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }
  exact ⟨hlen', hkeq ▸ hw_tm, hmk', hnd', hext', hcl.trans hd.2.2.2.2.2.1, hdm ▸ hd.2.2.2.2.2.2⟩

private theorem s12b_nodup_getElem_inj {α : Type _} :
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
    exact congrArg Nat.succ (s12b_nodup_getElem_inj hcons.2 i j (by simp at hi; omega)
      (by simp at hj; omega) heq)

private theorem s12b_nodup_map_on {α β : Type _} {f : α → β} :
    ∀ {l : List α}, l.Nodup → (∀ a ∈ l, ∀ b ∈ l, f a = f b → a = b) → (l.map f).Nodup
  | [], _, _ => .nil
  | a :: xs, hnd, hinj => by
    have hcons := List.nodup_cons.mp hnd
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hmem => ?_, s12b_nodup_map_on hcons.2 fun x hx y hy hxy =>
      hinj x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy) hxy⟩
    rw [List.mem_map] at hmem; obtain ⟨b, hb, hfb⟩ := hmem
    have hba := hinj b (List.mem_cons_of_mem _ hb) a List.mem_cons_self hfb
    exact hcons.1 (hba ▸ hb)

private theorem s12b_list_nodup_filter_map (f : Nat → Nat) {idxs : List Nat}
    {ar : List (BitVec 32)} {sz p : Nat}
    (hnd : ((List.range sz).map fun q => (ar[p + 3 + q]?.getD 0#32).toNat / 2).Nodup)
    (hid_nd : idxs.Nodup) (hid_lt : ∀ q ∈ idxs, q < sz)
    (hf : ∀ q, f q = (ar[p + 3 + q]?.getD 0#32).toNat / 2) :
    (idxs.map f).Nodup := by
  refine s12b_nodup_map_on hid_nd fun a ha b hb hab => ?_
  rw [hf a, hf b] at hab
  have ha_s := hid_lt a ha; have hb_s := hid_lt b hb
  exact s12b_nodup_getElem_inj hnd a b (by simp; omega) (by simp; omega)
    (by simpa [List.getElem_map] using hab)

private theorem s12b_nat_xor1_mod2 (n : Nat) : (n ^^^ 1) % 2 = (n % 2) ^^^ 1 := by
  apply Nat.eq_of_testBit_eq; intro k
  cases k with
  | zero => simp [Nat.testBit_zero]
  | succ k =>
    have hlt : (n % 2) ^^^ 1 < 2 := by
      rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h]
    simp [Nat.testBit_succ, Nat.div_eq_of_lt hlt]

private theorem s12b_bv32_bit1_ne0_mod2 {l neg_p : BitVec 32} :
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
      Nat.and_one_is_mod, Nat.and_one_is_mod, hm, s12b_nat_xor1_mod2]

private theorem s12b_clause_collect_done {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {sp : FullState} {p sz_n usz_n : Nat} {ws2 : List (BitVec 32)} {idxs : List Nat}
    (hdp : FullDenseInvW c F0 F_cur sp)
    (hp_ref : p ∈ fullArenaClauseRefsCore sp.core)
    (hng : fullArenaClauseGarb sp p = false)
    (hsz_eq : fullArenaClauseSizeCore sp.core p = sz_n)
    (hbd_sz : p + 3 + sz_n ≤ sp.core.arena.length)
    (hws2_le : usz_n ≤ ws2.length)
    (hid_len : idxs.length = usz_n) (hid_nd : idxs.Nodup)
    (hid_lt : ∀ q ∈ idxs, q < sz_n)
    (hws2_map : ∀ j < usz_n, ws2[j]? = sp.core.arena[p + 3 + (idxs[j]?.getD 0)]?)
    (hcov_k : ∀ q < sz_n, q ∈ idxs ∨
      sp.core.vals[(sp.core.arena[p + 3 + q]?.getD 0#32).toNat]?.getD 0#8 = 0xFF#8) :
    (∀ j < usz_n, ∀ j2 < usz_n, j ≠ j2 →
      (ws2[j]?.getD 0#32).toNat / 2 ≠ (ws2[j2]?.getD 0#32).toNat / 2) ∧
    (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((List.range usz_n).map fun j => (ws2[j]?.getD 0#32).toNat)) := by
  have hcov_all : ∀ l ∈ fullArenaClauseLits sp p,
      sp.core.vals[l]?.getD 0#8 = 0xFF#8 ∨ l ∈
        ((List.range usz_n).map fun j => (ws2[j]?.getD 0#32).toNat) := by
    intro l hl
    unfold fullArenaClauseLits fullArenaClauseLitsCore at hl; rw [hsz_eq] at hl
    rw [List.mem_map] at hl; obtain ⟨bv, hbv, rfl⟩ := hl
    obtain ⟨q, hq, hget⟩ := List.mem_iff_getElem.mp hbv
    rw [List.length_take, List.length_drop, Nat.min_eq_left (by omega)] at hq
    have hq_lt : q < sz_n := hq
    have hbd_q : p + 3 + q < sp.core.arena.length := by omega
    rw [List.getElem_take, List.getElem_drop] at hget
    rcases hcov_k q hq_lt with hin | hff
    · right; obtain ⟨j, hj, hgetj⟩ := List.mem_iff_getElem.mp hin
      have hj_u : j < usz_n := by omega
      have hm_j := hws2_map j hj_u
      have hid_j : (idxs[j]?.getD 0) = q := by
        rw [List.getElem?_eq_getElem hj, Option.getD_some, hgetj]
      rw [hid_j, List.getElem?_eq_getElem (by omega),
        List.getElem?_eq_getElem hbd_q, hget] at hm_j
      rw [List.mem_map]; refine ⟨j, List.mem_range.mpr hj_u, ?_⟩
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      exact congrArg BitVec.toNat (Option.some.inj hm_j)
    · left; rw [List.getElem?_eq_getElem hbd_q, Option.getD_some, hget] at hff; exact hff
  have hent_u := unassigned_clause_entails hdp.2.1 hdp.2.2.2.2.2.1 hp_ref hng hcov_all
  have hnd_u : (idxs.map fun q => (sp.core.arena[p + 3 + q]?.getD 0#32).toNat / 2).Nodup := by
    have hnd_sp := hdp.2.2.2.1 p hp_ref hng
    have har_lits : fullArenaClauseLits sp p =
        ((List.range sz_n).map fun q => (sp.core.arena[p + 3 + q]?.getD 0#32).toNat) := by
      unfold fullArenaClauseLits fullArenaClauseLitsCore; rw [hsz_eq]
      apply List.ext_getElem
      · simp only [List.length_map, List.length_take, List.length_drop, List.length_range]
        exact Nat.min_eq_left (by omega)
      · intro q hq _
        simp only [List.length_map, List.length_take, List.length_drop] at hq
        rw [Nat.min_eq_left (by omega)] at hq
        have hbd_q : p + 3 + q < sp.core.arena.length := by omega
        simp only [List.getElem_map, List.getElem_take, List.getElem_drop, List.getElem_range]
        rw [List.getElem?_eq_getElem hbd_q, Option.getD_some]
    rw [har_lits, List.map_map] at hnd_sp
    exact s12b_list_nodup_filter_map (fun q => (sp.core.arena[p + 3 + q]?.getD 0#32).toNat / 2)
      hnd_sp hid_nd hid_lt (fun _ => rfl)
  refine ⟨fun j hj j2 hj2 hne => ?_, hent_u⟩
  rw [hws2_map j hj, hws2_map j2 hj2]
  have hind := s12b_nodup_getElem_inj hnd_u j j2 (by simp [hid_len, hj]) (by simp [hid_len, hj2])
  intro heq
  have hij1 : idxs[j]?.getD 0 = idxs[j]'(by simp [hid_len, hj]) := by
    rw [List.getElem?_eq_getElem (by simp [hid_len, hj]), Option.getD_some]
  have hij2 : idxs[j2]?.getD 0 = idxs[j2]'(by simp [hid_len, hj2]) := by
    rw [List.getElem?_eq_getElem (by simp [hid_len, hj2]), Option.getD_some]
  rw [hij1, hij2] at heq
  exact hne (hind (by simp only [List.getElem_map]; exact heq))

end Helpers

/-! ## 2. `full_cong_extract_from_fid_s12b_wp` (`step12BCongExtractFromSpec`) -/

theorem full_cong_extract_from_fid_s12b_wp (Γ : Env)
    (hNext : ∀ args m Q X, FullCongSpecs.fullArenaNextSpec args m Q X →
      Γ "full_arena_next" [i64, i32] [i32] args m Q X)
    (hCountBins : ∀ args m Q X, m6CongCountBinsSpec args m Q X →
      Γ "full_cong_count_bins" [i64] [] args m Q X)
    (hExtAnd : ∀ args m Q X, step12BCongExtractAndClauseSpec args m Q X →
      Γ "full_cong_extract_and_clause_fid" [i64, i32, i64, i64, i64] [i64] args m Q X)
    (hTryXorIte : ∀ args m Q X, fidCongTryXorIteSpec args m Q X →
      Γ "full_cong_try_xor_ite" [i64, i32, i32, i32, i64, i64] [i64] args m Q X)
    (hExtractXorK : ∀ args m Q X, fidCongExtractXorKSpec args m Q X →
      Γ "full_cong_extract_xor_k" [i64, i32, i32, i64, i64] [i64] args m Q X) :
    ∀ args m Q X, step12BCongExtractFromSpec args m Q X →
      Func.wp Γ fidStep12BCongExtractFromFn.body args m Q X := by
  rintro ⟨h, g_start, g_cap, tick_lim, ⟨⟩⟩ m0 Q X
    ⟨c, F0, F_cur, s, R, rfl, hd, hgs_le, hg_cap, hseq0, hm0, hQ⟩
  have hmx := c.hmaxv; have hac := c.harena; have hsc := c.hscr; have hrc := c.hred
  unfold dimacsBound at hmx hac hsc hrc
  unfold fidStep12BCongExtractFromFn; dsimp only
  m6_split_fast
  · exfalso
    have hgt : g_cap.toNat < g_start.toNat := by
      simp only [BitVec.ult, decide_eq_true_eq] at hc; exact hc
    omega
  clear hc; c0_hsteps!; m3_call hCountBins
  refine ⟨c, s, R, rfl, hd.1, s12b_watchBounds_of_dense hd, hm0, fun ws1' m1 hws1_l hm1 => ?_⟩
  let s1 : FullState := { s with scratch := { s.scratch with work_stk1 := ws1' } }
  have hd1 : FullDenseInvW c F0 F_cur s1 := s12b_denseInvW_with_ws1 hd hws1_l
  c0_hsteps_nogrp
  -- Pass 1 outer loop: `(p, g_len, ticks, wn)`
  refine wp_loop_inv (ts := [i64, i64, i64, i64])
    (fun (p, g_len, ticks, wn, ()) mp => ∃ sp : FullState,
      FullDenseInvW c F0 F_cur sp ∧ sp.core.cur_vars = s.core.cur_vars ∧
      sp.core.fuel = s.core.fuel ∧ sp.core.repr = s.core.repr ∧
      sp.core.inconsistent = s.core.inconsistent ∧ sp.core.arena = s1.core.arena ∧
      sp.core.arena_len = s1.core.arena_len ∧ p.toNat ≤ s1.core.arena_len ∧
      (p.toNat = s1.core.arena_len ∨ p.toNat ∈ fullArenaClauseRefsCore s1.core) ∧
      g_start.toNat ≤ g_len.toNat ∧ g_len.toNat ≤ g_cap.toNat ∧ wn.toNat ≤ c.red_cap ∧
      (∀ idx < wn.toNat, (sp.scratch.red_refs[idx]?.getD 0#32).toNat ∈
        fullArenaClauseRefsCore s1.core) ∧
      FidGateSeqOk 64 F_cur s.core.cur_vars sp.scratch.scratch_buf g_len.toNat 0 ∧
      (FullMem c sp ⋆ R) mp)
    (fun (p, _, _, _, ()) _ => s1.core.arena_len - p.toNat)
    (fun J hJ => by
      c0_hsteps!
      have hmem0 : (0#64 : BitVec 64).toNat = s1.core.arena_len ∨
          (0#64 : BitVec 64).toNat ∈ fullArenaClauseRefsCore s1.core := by
        rcases Nat.eq_zero_or_pos s1.core.arena_len with hz | hpos
        · exact Or.inl hz.symm
        · exact Or.inr (fullArenaClauseRefs_zero_mem hd1.2.1 hpos)
      exact hJ (0#64, g_start, 0#64, 0#64, ()) m1
        ⟨s1, hd1, rfl, rfl, rfl, rfl, rfl, rfl, Nat.zero_le _, hmem0, Nat.le_refl _, hgs_le,
         Nat.zero_le _, (fun _ h => absurd h (Nat.not_lt_zero _)), hseq0, hm1⟩)
    (fun J (p, g_len, ticks, wn, ()) mp
      ⟨sp, hdp, hcv_p, hfl_p, hrep_p, hinc_p, har_p, hal_p, hp_le, hp_mem, hgl_lo, hgl_hi,
       hwn_le, hrr_p, hseq_p, hmp⟩ ihp => ?_)
  -- Inner exit join from Pass 1 into Pass 2 (`ts := []`)
  refine wp_join_group (ts := []) (fun () m_p2 => m_p2 = mp) ?_ ?_
  · -- Pass 2: wide AND clauses recorded in `rr[0..wn)`
    rintro _ ⟨⟩ m_p2 rfl
    let sp1 := sp; let g_len1 := g_len; let ticks1 := ticks
    have hdp1 := hdp; have hcv1 := hcv_p; have hfl1 := hfl_p; have hrep1 := hrep_p
    have hinc1 := hinc_p; have har1 := har_p; have hal1 := hal_p
    have hgl1_lo := hgl_lo; have hgl1_hi := hgl_hi; have hrr_ok := hrr_p; have hmp2 := hmp
    have hseq1_w : Step12BGateSeqOk step12BCongAndArityMax F_cur s.core.cur_vars
        sp1.scratch.scratch_buf g_len1.toNat 0 :=
      step12BGateSeqOk_mono (by unfold step12BCongAndArityMax; decide)
        (step12BGateSeqOk_of_fid (by decide) hseq_p)
    c0_hsteps_nogrp
    refine wp_loop_inv (ts := [i64, i64, i64])
      (fun (g_len, ticks, wi, ()) mp => ∃ sp : FullState,
        FullDenseInvW c F0 F_cur sp ∧ sp.core.cur_vars = s.core.cur_vars ∧
        sp.core.fuel = s.core.fuel ∧ sp.core.repr = s.core.repr ∧
        sp.core.inconsistent = s.core.inconsistent ∧ sp.core.arena = s1.core.arena ∧
        sp.core.arena_len = s1.core.arena_len ∧ sp.scratch.red_refs = sp1.scratch.red_refs ∧
        wi.toNat ≤ wn.toNat ∧ g_start.toNat ≤ g_len.toNat ∧ g_len.toNat ≤ g_cap.toNat ∧
        Step12BGateSeqOk step12BCongAndArityMax F_cur s.core.cur_vars sp.scratch.scratch_buf
          g_len.toNat 0 ∧
        (FullMem c sp ⋆ R) mp)
      (fun (_, _, wi, ()) _ => wn.toNat - wi.toNat)
      (fun J2 hJ2 => by
        c0_hsteps!
        exact hJ2 (g_len1, ticks1, 0#64, ()) m_p2
          ⟨sp1, hdp1, hcv1, hfl1, hrep1, hinc1, har1, hal1, rfl, Nat.zero_le _, hgl1_lo, hgl1_hi,
           hseq1_w, hmp2⟩)
      (fun J2 (g_len, ticks, wi, ()) mp
        ⟨sp, hdp, hcv_p, hfl_p, hrep_p, hinc_p, har_p, hal_p, hrr_p, hwi_le, hgl_lo, hgl_hi,
         hseq_p, hmp⟩ ih2 => ?_)
    have hq_done : Q (g_len, ()) mp :=
      hQ g_len sp mp hdp hcv_p hfl_p hrep_p hinc_p hgl_lo hgl_hi hseq_p hmp
    have hlen_p := hdp.1
    have harl_p := hlen_p.core_ok.arena_len_arr; have hale_p := hlen_p.core_ok.arena_len_le
    have hcv_ple := hlen_p.core_ok.cur_vars_le; have hvals_pl := hlen_p.core_ok.vals_len
    have hws1_pl := hlen_p.scratch_ok.work_stk1_len; have hws2_pl := hlen_p.scratch_ok.work_stk2_len
    have hrrl_p := hlen_p.scratch_ok.red_refs_len
    m6_split_fast
    · have hwi_lt : wi.toNat < wn.toNat := by
        simp only [BitVec.ult, decide_eq_true_eq] at hc; exact hc
      clear hc; m6_split_fast
      · clear hc; m6_split_fast
        · clear hc
          have hwi_rr : wi.toNat < sp.scratch.red_refs.length := by omega
          let wp32 := sp.scratch.red_refs[wi.toNat]'hwi_rr
          let wp := wp32.setWidth 64
          have hwp_ref : wp.toNat ∈ fullArenaClauseRefsCore sp.core := by
            have h1 := hrr_ok wi.toNat hwi_lt
            rw [← hrr_p, List.getElem?_eq_getElem hwi_rr, Option.getD_some] at h1
            unfold fullArenaClauseRefsCore; rw [har_p, hal_p, bv_zext32_toNat]; exact h1
          have hwp_wf := hdp.2.1.arena.refs_wf wp.toNat hwp_ref
          have hwp_arr : wp.toNat < sp.core.arena.length := by omega
          have hwp2_n : (wp + 2#64).toNat = wp.toNat + 2 := by bv_omega
          have hwp2_arr : (wp + 2#64).toNat < sp.core.arena.length := by omega
          have hwi1_n : (wi + 1#64).toNat = wi.toNat + 1 := bv64_add1_lt (by omega)
          c0_hsteps_nogrp
          refine wp_join_group (ts := [i64, i64])
            (fun (gl', tk', ()) mj => ∃ sj : FullState,
              FullDenseInvW c F0 F_cur sj ∧ sj.core.cur_vars = s.core.cur_vars ∧
              sj.core.fuel = s.core.fuel ∧ sj.core.repr = s.core.repr ∧
              sj.core.inconsistent = s.core.inconsistent ∧ sj.core.arena = s1.core.arena ∧
              sj.core.arena_len = s1.core.arena_len ∧ sj.scratch.red_refs = sp1.scratch.red_refs ∧
              g_start.toNat ≤ gl'.toNat ∧ gl'.toNat ≤ g_cap.toNat ∧
              Step12BGateSeqOk step12BCongAndArityMax F_cur s.core.cur_vars
                sj.scratch.scratch_buf gl'.toNat 0 ∧
              (FullMem c sj ⋆ R) mj)
            (fun _ ⟨gl', tk', ⟨⟩⟩ mj
              ⟨sj, hdj, hcv_j, hfl_j, hrep_j, hinc_j, har_j, hal_j, hrr_j, hgl_lo', hgl_hi',
               hseq_j, hmj⟩ => by
              m3_let
              exact ih2 (gl', tk', wi + 1#64, ()) mj (by dsimp only; omega)
                ⟨sj, hdj, hcv_j, hfl_j, hrep_j, hinc_j, har_j, hal_j, hrr_j, by omega, hgl_lo',
                 hgl_hi', hseq_j, hmj⟩) ?_
          intro Jw2 hJw2
          have hjw2_same : Jw2 (g_len, ticks + 1#64, ()) mp :=
            hJw2 (g_len, ticks + 1#64, ()) mp
              ⟨sp, hdp, hcv_p, hfl_p, hrep_p, hinc_p, har_p, hal_p, hrr_p, hgl_lo, hgl_hi,
               hseq_p, hmp⟩
          m6_split_fast
          · have hng_red := beq_iff_eq.mp hc; clear hc
            have hng : fullArenaClauseGarb sp wp.toNat = false := by
              unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
              rw [List.getElem?_eq_getElem hwp_arr, Option.getD_some]
              exact garb_false_of_and_480000 hng_red
            m6_split_fast
            · clear hc
              have hsz_p2 : sp.core.arena[(wp + 2#64).toNat]'hwp2_arr =
                  sp.core.arena[wp.toNat + 2]'(by omega) :=
                list_getElem_congr hwp2_n hwp2_arr (by omega)
              have hsz_eq : fullArenaClauseSizeCore sp.core wp.toNat =
                  (sp.core.arena[(wp + 2#64).toNat]'hwp2_arr).toNat := by
                unfold fullArenaClauseSizeCore
                rw [hsz_p2, List.getElem?_eq_getElem (by omega), Option.getD_some]
              let sz_bv := sp.core.arena[(wp + 2#64).toNat]'hwp2_arr
              have hbd_sz : wp.toNat + 3 + sz_bv.toNat ≤ sp.core.arena.length := by
                have := hwp_wf.2.2.1; have := hwp_wf.2.2.2.1
                have hsz_d : fullArenaClauseSizeCore sp.core wp.toNat = sz_bv.toNat := hsz_eq
                omega
              c0_hsteps_nogrp
              refine wp_loop_break_group
                (brkTs := [i32, i32, i32, .bool, i32]) (lpTs := [i32, i32, i32, i32])
                (fun (usz, _, _, sat, _, ()) mb => ∃ ws2 : List (BitVec 32),
                  ws2.length = 2 * c.max_vars ∧
                  (sat = false →
                    usz.toNat ≤ 1000001 ∧ usz.toNat ≤ sp.core.cur_vars ∧
                    (∀ j < usz.toNat, (ws2[j]?.getD 0#32).toNat < 2 * sp.core.cur_vars) ∧
                    (∀ j < usz.toNat, ∀ j2 < usz.toNat, j ≠ j2 →
                      (ws2[j]?.getD 0#32).toNat / 2 ≠ (ws2[j2]?.getD 0#32).toNat / 2) ∧
                    (cnfOfClauses F_cur).EntailsClause (cnfClause
                      ((List.range usz.toNat).map fun j => (ws2[j]?.getD 0#32).toNat))) ∧
                  (FullMem c { sp with scratch := { sp.scratch with work_stk2 := ws2 } } ⋆ R) mb)
                (fun rem (usz, max_nbc, min_nbc, k, ()) mk => ∃ ws2 : List (BitVec 32),
                  ws2.length = 2 * c.max_vars ∧ k.toNat ≤ sz_bv.toNat ∧
                  rem = sz_bv.toNat - k.toNat ∧
                  usz.toNat ≤ 1000001 ∧ usz.toNat ≤ k.toNat ∧ usz.toNat ≤ sp.core.cur_vars ∧
                  (∀ j < usz.toNat, (ws2[j]?.getD 0#32).toNat < 2 * sp.core.cur_vars) ∧
                  (∃ idxs : List Nat, idxs.length = usz.toNat ∧ idxs.Nodup ∧
                    (∀ q ∈ idxs, q < k.toNat) ∧
                    (∀ j < usz.toNat,
                      ws2[j]? = sp.core.arena[wp.toNat + 3 + (idxs[j]?.getD 0)]?) ∧
                    (∀ q < k.toNat, q ∈ idxs ∨
                      sp.core.vals[(sp.core.arena[wp.toNat + 3 + q]?.getD 0#32).toNat]?.getD 0#8 =
                        0xFF#8)) ∧
                  (FullMem c { sp with scratch := { sp.scratch with work_stk2 := ws2 } } ⋆ R) mk)
                ?_ ?_ ?_
              · rintro _ ⟨usz, _, _, sat, _, ⟨⟩⟩ mb ⟨ws2, hws2_l, hnsat, hmb⟩
                let sb : FullState := { sp with scratch := { sp.scratch with work_stk2 := ws2 } }
                have hdb : FullDenseInvW c F0 F_cur sb := s12b_denseInvW_with_ws2 hdp hws2_l
                have hjb_same : Jw2 (g_len, ticks + 1#64, ()) mb :=
                  hJw2 (g_len, ticks + 1#64, ()) mb
                    ⟨sb, hdb, hcv_p, hfl_p, hrep_p, hinc_p, har_p, hal_p, hrr_p, hgl_lo, hgl_hi,
                     hseq_p, hmb⟩
                m6_split_fast
                · clear hc; c0_hsteps!; exact hjb_same
                · have hsat_f : sat = false := hc; clear hc
                  m6_split_fast
                  · have hu66 : 66 ≤ usz.toNat := by
                      simp only [BitVec.ule, decide_eq_true_eq] at hc; bv_omega
                    clear hc; m6_split_fast
                    · have hu_max : usz.toNat ≤ 1000001 := by
                        simp only [BitVec.ule, decide_eq_true_eq] at hc; bv_omega
                      clear hc; m6_split_fast
                      · clear hc
                        obtain ⟨_, hu_cv, hlt_u, hdiff_u, hent_u⟩ := hnsat hsat_f
                        m6_split_fast
                        · clear hc; m6_split_fast
                          · clear hc; c0_hsteps!; m3_call hExtAnd
                            refine ⟨step12BCongAndArityMax, c, F0, F_cur,
                              { sb with scratch := { sb.scratch with res_sz := ticks + 1#64 } },
                              R, Nat.le_refl _, rfl, s12b_denseInvW_with_rsz hdb _,
                              by omega, by unfold step12BCongAndArityMax; omega, hu_cv, hgl_hi,
                              hg_cap, by rw [hcv_p]; exact hseq_p, hlt_u,
                              fun j hj j2 hj2 hne heq =>
                                hdiff_u j hj j2 hj2 hne
                                  (by dsimp only at heq; exact congrArg (· / 2) heq),
                              hent_u, hm, fun ret lm' scr' rsz' m' hdw' hret_lo hret_hi _
                                hseq' hm' => ?_⟩
                            c0_hsteps!
                            exact hJw2 (ret, rsz', ()) m'
                              ⟨_, hdw', hcv_p, hfl_p, hrep_p, hinc_p, har_p, hal_p, hrr_p,
                               by omega, hret_hi, by rw [← hcv_p]; exact hseq', hm'⟩
                          · clear hc; c0_hsteps!; exact hjb_same
                        · clear hc; c0_hsteps!; exact hjb_same
                      · clear hc; c0_hsteps!; exact hjb_same
                    · clear hc; c0_hsteps!; exact hjb_same
                  · clear hc; c0_hsteps!; exact hjb_same
              · -- Pass 2 literal collection loop body
                rintro B3 L3 rem3 ⟨usz, max_nbc, min_nbc, k, ⟨⟩⟩ mk hB3 hL3
                  ⟨ws2, hws2_l, hk_le, rfl, hu_max, hu_k, hu_cv, hlt_u,
                   ⟨idxs, hid_len, hid_nd, hid_lt, hws2_map, hcov_k⟩, hmk⟩
                m6_split_fast
                · have hk_lt : k.toNat < sz_bv.toNat := by
                    simp only [BitVec.ult, decide_eq_true_eq] at hc; exact hc
                  have hk1_n : (k + 1#32).toNat = k.toNat + 1 := by bv_omega
                  have hp3k_n : (wp + 3#64 + k.setWidth 64).toNat = wp.toNat + 3 + k.toNat :=
                    bv64_add_zext32 (k := 3) (by omega)
                  have hp3k_arr : (wp + 3#64 + k.setWidth 64).toNat < sp.core.arena.length := by
                    omega
                  let lk := sp.core.arena[(wp + 3#64 + k.setWidth 64).toNat]'hp3k_arr
                  have hlk_eq : lk = sp.core.arena[wp.toNat + 3 + k.toNat]'(by omega) :=
                    list_getElem_congr hp3k_n hp3k_arr (by omega)
                  have hlk_lt : lk.toNat < 2 * sp.core.cur_vars := by
                    have hmem_lk : lk.toNat ∈ fullArenaClauseLits sp wp.toNat := by
                      unfold fullArenaClauseLits fullArenaClauseLitsCore
                      have hsz_szbv : fullArenaClauseSizeCore sp.core wp.toNat = sz_bv.toNat :=
                        hsz_eq
                      simp only [List.mem_map]; refine ⟨lk, ?_, rfl⟩
                      have hk_s : k.toNat < fullArenaClauseSizeCore sp.core wp.toNat := by
                        rw [hsz_szbv]; exact hk_lt
                      have hget : ((sp.core.arena.drop (wp.toNat + 3)).take
                          (fullArenaClauseSizeCore sp.core wp.toNat))[k.toNat]'(by
                            simp [List.length_take, List.length_drop, hsz_szbv]; omega) = lk := by
                        simp [List.getElem_take, List.getElem_drop, hlk_eq]
                      rw [← hget]; exact List.getElem_mem _
                    exact hdp.2.1.arena.lits_lt wp.toNat hwp_ref hng lk.toNat hmem_lk
                  have hlk_v : (lk.setWidth 64).toNat < sp.core.vals.length := by
                    rw [bv_zext32_toNat]; omega
                  have hlk_v' : lk.toNat < sp.core.vals.length := by
                    rw [bv_zext32_toNat] at hlk_v; exact hlk_v
                  clear hc; m6_split_fast
                  · c0_hsteps!
                    exact hB3 (usz, max_nbc, min_nbc, true, k, ()) mk
                      ⟨ws2, hws2_l, (fun hf => by cases hf), hmk⟩
                  · have hdom_lk : sp.core.vals[(lk.setWidth 64).toNat]'hlk_v = 0#8 ∨
                        sp.core.vals[(lk.setWidth 64).toNat]'hlk_v = 1#8 ∨
                        sp.core.vals[(lk.setWidth 64).toNat]'hlk_v = 0xFF#8 := by
                      have h0 := hdp.2.1.vals_domain lk.toNat hlk_lt
                      rw [List.getElem?_eq_getElem hlk_v', Option.getD_some] at h0
                      rw [list_getElem_congr (bv_zext32_toNat lk) hlk_v hlk_v']; exact h0
                    have hnsgt : ¬ (0#32 : BitVec 32).slt
                        ((sp.core.vals[(lk.setWidth 64).toNat]'hlk_v).signExtend 32) = true := by
                      have hc0 : (0#32 : BitVec 32).slt
                          ((sp.core.vals[(lk.setWidth 64).toNat]'hlk_v).signExtend 32) = false := hc
                      rw [hc0]; decide
                    clear hc; m6_split_fast
                    · clear hc; m6_split_fast
                      · c0_hsteps!
                        exact hB3 (usz, max_nbc, min_nbc, true, k, ()) mk
                          ⟨ws2, hws2_l, (fun hf => by cases hf), hmk⟩
                      · have hu_ltm : usz.toNat < 1000001 := by
                          simp only [BitVec.ule, decide_eq_false_iff_not] at hc; bv_omega
                        clear hc; m6_split_fast
                        · c0_hsteps!
                          exact hB3 (usz, max_nbc, min_nbc, true, k, ()) mk
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
                            rw [bv_zext32_toNat, hws1_pl]
                            exact Nat.lt_of_lt_of_le hlk_lt (by omega)
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
                          refine wp_join_group (ts := [i32]) (fun (_mx, ()) mmx => mmx = m_st) ?_ ?_
                          · rintro _ ⟨mx', ⟨⟩⟩ mmx hmmx; rw [hmmx]
                            c0_hsteps_nogrp
                            refine wp_join_group (ts := [i32]) (fun (_mn, ()) mmn => mmn = m_st)
                              ?_ ?_
                            · rintro _ ⟨mn', ⟨⟩⟩ mmn hmmn; rw [hmmn]; c0_hsteps!
                              refine hL3 (sz_bv.toNat - (k + 1#32).toNat)
                                (usz + 1#32, mx', mn', k + 1#32, ()) m_st (by omega)
                                ⟨ws2', by simp [ws2', hws2_l], by omega, rfl, by omega, by omega,
                                 by omega, fun j hj => ?_, ?_, hm2⟩
                              · dsimp only [ws2']; by_cases hju : j = usz.toNat
                                · subst hju; rw [List.getElem?_set_self hu_ws2, Option.getD_some]
                                  exact hlk_lt
                                · rw [List.getElem?_set_ne (Ne.symm hju)]; exact hlt_u j (by omega)
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
                                    rw [List.getElem?_append_left (by omega)]
                                    exact hws2_map j (by omega)
                                · simp only [List.mem_append, List.mem_singleton]
                                  by_cases hqk : q = k.toNat
                                  · subst hqk; exact Or.inl (Or.inr rfl)
                                  · rcases hcov_k q (by omega) with hin | hff
                                    · exact Or.inl (Or.inl hin)
                                    · exact Or.inr hff
                            · intro Jmn hJmn; m6_split_fast
                              · m3_let; exact hJmn (_, ()) m_st rfl
                              · m3_let; exact hJmn (_, ()) m_st rfl
                          · intro Jmx hJmx; m6_split_fast
                            · m3_let; exact hJmx (_, ()) m_st rfl
                            · m3_let; exact hJmx (_, ()) m_st rfl
                    · have hne0 : sp.core.vals[(lk.setWidth 64).toNat]'hlk_v ≠ 0#8 :=
                        FullM3CongBva.bv8_ne0_of_signExtend32 hdom_lk (beq_eq_false_iff_ne.mp hc)
                      have hff_lk : sp.core.vals[(lk.setWidth 64).toNat]?.getD 0#8 = 0xFF#8 := by
                        rw [List.getElem?_eq_getElem hlk_v, Option.getD_some]
                        exact FullM3CongBva.bv8_ne0_not_signExtend32_sgt0_eqff hdom_lk hne0 hnsgt
                      c0_hsteps!
                      refine hL3 (sz_bv.toNat - (k + 1#32).toNat)
                        (usz, max_nbc, min_nbc, k + 1#32, ()) mk (by omega)
                        ⟨ws2, hws2_l, by omega, rfl, hu_max, by omega, hu_cv, hlt_u,
                         ⟨idxs, hid_len, hid_nd, fun q hq => by have := hid_lt q hq; omega,
                          hws2_map, fun q hq => ?_⟩, hmk⟩
                      by_cases hqk : q = k.toNat
                      · subst hqk; right
                        have hk_ar : sp.core.arena[wp.toNat + 3 + k.toNat]?.getD 0#32 = lk := by
                          rw [List.getElem?_eq_getElem (by omega), Option.getD_some, hlk_eq]
                        rw [hk_ar]; rw [bv_zext32_toNat] at hff_lk; exact hff_lk
                      · exact hcov_k q (by omega)
                · have hk_e : k.toNat = sz_bv.toNat := by
                    simp only [BitVec.ult, decide_eq_false_iff_not] at hc
                    change ¬ k.toNat < sz_bv.toNat at hc; omega
                  obtain ⟨hdiff_u, hent_u⟩ := s12b_clause_collect_done hdp hwp_ref hng hsz_eq
                    hbd_sz (by omega) hid_len hid_nd (hk_e ▸ hid_lt) hws2_map (hk_e ▸ hcov_k)
                  c0_hsteps!
                  exact hB3 (usz, max_nbc, min_nbc, false, k, ()) mk
                    ⟨ws2, hws2_l, fun _ => ⟨hu_max, hu_cv, hlt_u, hdiff_u, hent_u⟩, hmk⟩
              · intro _ L3 _ hL3; c0_hsteps!
                exact hL3 sz_bv.toNat (0#32, 0#32, 0xFFFFFFFF#32, 0#32, ()) mp
                  ⟨sp.scratch.work_stk2, hws2_pl, Nat.zero_le _, rfl, Nat.zero_le _,
                   Nat.zero_le _, Nat.zero_le _, (fun _ h => by cases h),
                   ⟨[], rfl, .nil, (fun _ h => by cases h), (fun _ h => by cases h),
                    (fun _ h => by cases h)⟩, hmp⟩
            · clear hc; c0_hsteps!; exact hjw2_same
          · clear hc; c0_hsteps!; exact hjw2_same
        · clear hc; c0_hsteps!; exact hq_done
      · clear hc; c0_hsteps!; exact hq_done
    · clear hc; c0_hsteps!; exact hq_done
  · -- Pass 1: arena scan (`narrow AND <= 64` + XOR/ITE, recording `66 <= usz <= 1000001` in `rr`)
    intro Jp2 hJp2
    have hjp2_now : Jp2 () mp := hJp2 () mp rfl
    have hlen_p := hdp.1
    have harl_p := hlen_p.core_ok.arena_len_arr; have hale_p := hlen_p.core_ok.arena_len_le
    have hcv_ple := hlen_p.core_ok.cur_vars_le; have hvals_pl := hlen_p.core_ok.vals_len
    have hws1_pl := hlen_p.scratch_ok.work_stk1_len; have hws2_pl := hlen_p.scratch_ok.work_stk2_len
    have hrrl_p := hlen_p.scratch_ok.red_refs_len
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
          c0_hsteps_nogrp; refine wp_join_group (ts := [i64, i64, i64])
            (fun (gl', tk', wn', ()) mj => ∃ sj : FullState,
              FullDenseInvW c F0 F_cur sj ∧ sj.core.cur_vars = s.core.cur_vars ∧
              sj.core.fuel = s.core.fuel ∧ sj.core.repr = s.core.repr ∧
              sj.core.inconsistent = s.core.inconsistent ∧ sj.core.arena = s1.core.arena ∧
              sj.core.arena_len = s1.core.arena_len ∧
              g_start.toNat ≤ gl'.toNat ∧ gl'.toNat ≤ g_cap.toNat ∧ wn'.toNat ≤ c.red_cap ∧
              (∀ idx < wn'.toNat, (sj.scratch.red_refs[idx]?.getD 0#32).toNat ∈
                fullArenaClauseRefsCore s1.core) ∧
              FidGateSeqOk 64 F_cur s.core.cur_vars sj.scratch.scratch_buf gl'.toNat 0 ∧
              (FullMem c sj ⋆ R) mj)
            (fun _ ⟨gl', tk', wn', ⟨⟩⟩ mj
              ⟨sj, hdj, hcv_j, hfl_j, hrep_j, hinc_j, har_j, hal_j, hgl_lo', hgl_hi', hwn_j,
               hrr_j, hseq_j, hmj⟩ => by
              m3_let
              exact ihp (np_bv, gl', tk', wn', ()) mj (by dsimp only; omega)
                ⟨sj, hdj, hcv_j, hfl_j, hrep_j, hinc_j, har_j, hal_j, by omega, hnp_mem, hgl_lo',
                 hgl_hi', hwn_j, hrr_j, hseq_j, hmj⟩) ?_
          intro Jnext hJnext
          have hjnext_same : Jnext (g_len, ticks + 1#64, wn, ()) mp :=
            hJnext (g_len, ticks + 1#64, wn, ()) mp
              ⟨sp, hdp, hcv_p, hfl_p, hrep_p, hinc_p, har_p, hal_p, hgl_lo, hgl_hi, hwn_le, hrr_p,
               hseq_p, hmp⟩
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
              let sz_bv := sp.core.arena[(p + 2#64).toNat]'hp2_arr
              have hbd_sz : p.toNat + 3 + sz_bv.toNat ≤ sp.core.arena.length := by
                have := hp_wf.2.2.1; have := hp_wf.2.2.2.1
                have hsz_d : fullArenaClauseSizeCore sp.core p.toNat = sz_bv.toNat := hsz_eq
                omega
              c0_hsteps_nogrp
              refine wp_loop_break_group
                (brkTs := [i32, i32, i32, i32, .bool, i32]) (lpTs := [i32, i32, i32, i32, i32])
                (fun (usz, _, _, neg_p, sat, _, ()) mb => ∃ ws2 : List (BitVec 32),
                  ws2.length = 2 * c.max_vars ∧
                  (sat = false →
                    usz.toNat ≤ 1000001 ∧ usz.toNat ≤ sp.core.cur_vars ∧
                    (∀ j < usz.toNat, (ws2[j]?.getD 0#32).toNat < 2 * sp.core.cur_vars) ∧
                    ((neg_p &&& 1#32).toNat = (List.range usz.toNat).foldl
                      (fun acc i => acc ^^^ ((ws2[i]?.getD 0#32).toNat % 2)) 0) ∧
                    (∀ j < usz.toNat, ∀ j2 < usz.toNat, j ≠ j2 →
                      (ws2[j]?.getD 0#32).toNat / 2 ≠ (ws2[j2]?.getD 0#32).toNat / 2) ∧
                    (cnfOfClauses F_cur).EntailsClause (cnfClause
                      ((List.range usz.toNat).map fun j => (ws2[j]?.getD 0#32).toNat))) ∧
                  (FullMem c { sp with scratch := { sp.scratch with work_stk2 := ws2 } } ⋆ R) mb)
                (fun rem (usz, max_nbc, min_nbc, neg_p, k, ()) mk => ∃ ws2 : List (BitVec 32),
                  ws2.length = 2 * c.max_vars ∧ k.toNat ≤ sz_bv.toNat ∧
                  rem = sz_bv.toNat - k.toNat ∧
                  usz.toNat ≤ 1000001 ∧ usz.toNat ≤ k.toNat ∧ usz.toNat ≤ sp.core.cur_vars ∧
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
              · -- Post Pass-1 collection: narrow `3 ≤ usz ≤ 65` vs wide `66 ≤ usz ≤ 1,000,001`
                rintro _ ⟨usz, max_nbc, min_nbc, neg_p, sat, _, ⟨⟩⟩ mb ⟨ws2, hws2_l, hnsat, hmb⟩
                let sb : FullState := { sp with scratch := { sp.scratch with work_stk2 := ws2 } }
                have hdb : FullDenseInvW c F0 F_cur sb := s12b_denseInvW_with_ws2 hdp hws2_l
                have hjb_same : Jnext (g_len, ticks + 1#64, wn, ()) mb :=
                  hJnext (g_len, ticks + 1#64, wn, ()) mb
                    ⟨sb, hdb, hcv_p, hfl_p, hrep_p, hinc_p, har_p, hal_p, hgl_lo, hgl_hi, hwn_le,
                     hrr_p, hseq_p, hmb⟩
                c0_hsteps_nogrp
                refine wp_join_group (ts := [i64, i64, i64])
                  (fun (gl', tk', wn', ()) mj =>
                    ∃ sj : FullState,
                      FullDenseInvW c F0 F_cur sj ∧ sj.core.cur_vars = s.core.cur_vars ∧
                      sj.core.fuel = s.core.fuel ∧ sj.core.repr = s.core.repr ∧
                      sj.core.inconsistent = s.core.inconsistent ∧ sj.core.arena = s1.core.arena ∧
                      sj.core.arena_len = s1.core.arena_len ∧ g_start.toNat ≤ gl'.toNat ∧
                      gl'.toNat ≤ g_cap.toNat ∧ wn'.toNat ≤ c.red_cap ∧
                      (∀ i < wn'.toNat,
                        (sj.scratch.red_refs[i]?.getD 0#32).toNat ∈
                          fullArenaClauseRefsCore s1.core) ∧
                      FidGateSeqOk 64 F_cur s.core.cur_vars
                        sj.scratch.scratch_buf gl'.toNat 0 ∧ (FullMem c sj ⋆ R) mj)
                  (fun _ ⟨gl', tk', wn', ⟨⟩⟩ mj h => by
                    c0_hsteps!; exact hJnext (gl', tk', wn', ()) mj h) ?_
                intro Jnext hJnext
                have hjb_same : Jnext (g_len, ticks + 1#64, wn, ()) mb :=
                  hJnext (g_len, ticks + 1#64, wn, ()) mb
                    ⟨sb, hdb, hcv_p, hfl_p, hrep_p, hinc_p, har_p, hal_p, hgl_lo, hgl_hi, hwn_le,
                     hrr_p, hseq_p, hmb⟩
                refine wp_join_group (ts := []) (fun () m_el => m_el = mb) ?_ ?_
                · -- `else if (!sat && usz >= 66 && usz <= 1000001 && usz <= cv)`
                  rintro _ ⟨⟩ m_el hm_el; subst m_el
                  m6_split_fast
                  · clear hc; c0_hsteps!; exact hjb_same
                  · clear hc; m6_split_fast
                    · clear hc; m6_split_fast
                      · clear hc; m6_split_fast
                        · clear hc; m6_split_fast
                          · clear hc; m6_split_fast
                            · clear hc; m6_split_fast
                              · have hwn_lt : wn.toNat < c.red_cap := by
                                  simp only [BitVec.ult, decide_eq_true_eq,
                                    BitVec.toNat_ofNat] at hc
                                  rw [Nat.mod_eq_of_lt (by omega)] at hc; exact hc
                                have hwn_rr : wn.toNat < sb.scratch.red_refs.length := by
                                  dsimp only [sb]; omega
                                have hwn1_n : (wn + 1#64).toNat = wn.toNat + 1 :=
                                  bv64_add1_lt (by omega)
                                clear hc; c0_hsteps!
                                let rr' := sb.scratch.red_refs.set wn.toNat (p.setWidth 32)
                                refine hJnext (g_len, ticks + 1#64, wn + 1#64, ()) m
                                  ⟨{ sb with scratch := { sb.scratch with red_refs := rr' } },
                                   s12b_denseInvW_with_rr hdb
                                     (by dsimp only [rr', sb]; rw [List.length_set]; exact hrrl_p),
                                   hcv_p, hfl_p, hrep_p, hinc_p, har_p, hal_p, hgl_lo, hgl_hi,
                                   by rw [hwn1_n]; omega, fun idx hidx => ?_, hseq_p, hm⟩
                                dsimp only [rr']; rw [hwn1_n] at hidx
                                by_cases hidx_w : idx = wn.toNat
                                · subst hidx_w
                                  rw [List.getElem?_set_self hwn_rr, Option.getD_some, hp_tr]
                                  exact hp_mem.resolve_left (by omega)
                                · rw [List.getElem?_set_ne (Ne.symm hidx_w)]
                                  exact hrr_p idx (by omega)
                              · clear hc; c0_hsteps!; exact hjb_same
                            · clear hc; c0_hsteps!; exact hjb_same
                          · clear hc; c0_hsteps!; exact hjb_same
                        · clear hc; c0_hsteps!; exact hjb_same
                      · clear hc; c0_hsteps!; exact hjb_same
                    · clear hc; c0_hsteps!; exact hjb_same
                · -- First `if (!sat && usz >= 3 && usz <= 65 && usz <= cv)`
                  intro Jel hJel
                  m6_split_fast
                  · clear hc; c0_hsteps!; exact hJel () mb rfl
                  · have hsat_f : sat = false := hc; clear hc
                    m6_split_fast
                    · have hu_lt3 : 3 ≤ usz.toNat := by
                        simp only [BitVec.ule, decide_eq_true_eq] at hc; bv_omega
                      clear hc; m6_split_fast
                      · have hu_le65 : usz.toNat ≤ 65 := by
                          simp only [BitVec.ule, decide_eq_true_eq] at hc; bv_omega
                        clear hc; m6_split_fast
                        · clear hc
                          obtain ⟨_, hu_cv, hlt_u, hneg_u, hdiff_u, hent_u⟩ := hnsat hsat_f
                          c0_hsteps_nogrp; refine wp_join_group (ts := [i64, i64])
                            (fun (gl', tk', ()) mg => ∃ sg : FullState,
                              FullDenseInvW c F0 F_cur sg ∧ sg.core.cur_vars = s.core.cur_vars ∧
                              sg.core.fuel = s.core.fuel ∧ sg.core.repr = s.core.repr ∧
                              sg.core.inconsistent = s.core.inconsistent ∧
                              sg.core.arena = s1.core.arena ∧
                              sg.core.arena_len = s1.core.arena_len ∧
                              sg.scratch.work_stk2 = ws2 ∧
                              sg.scratch.red_refs = sp.scratch.red_refs ∧
                              g_start.toNat ≤ gl'.toNat ∧ gl'.toNat ≤ g_cap.toNat ∧
                              FidGateSeqOk 64 F_cur s.core.cur_vars sg.scratch.scratch_buf
                                gl'.toNat 0 ∧
                              (FullMem c sg ⋆ R) mg)
                            ?_ ?_
                          · -- Post narrow AND: XOR/ITE (`usz == 3`) and XOR-k (`4 <= usz <= 5`)
                            rintro _ ⟨gl', tk', ⟨⟩⟩ mg
                              ⟨sg, hdg, hcv_g, hfl_g, hrep_g, hinc_g, har_g, hal_g, hws2_g,
                               hrr_g, hgl_lo', hgl_hi', hseq_g, hmg⟩
                            have hlen_g := hdg.1
                            have hrr_g_ok : ∀ idx < wn.toNat,
                                (sg.scratch.red_refs[idx]?.getD 0#32).toNat ∈
                                  fullArenaClauseRefsCore s1.core := by
                              rw [hrr_g]; exact hrr_p
                            have hjg_same : Jnext (gl', tk', wn, ()) mg :=
                              hJnext (gl', tk', wn, ()) mg
                                ⟨sg, hdg, hcv_g, hfl_g, hrep_g, hinc_g, har_g, hal_g, hgl_lo',
                                 hgl_hi', hwn_le, hrr_g_ok, hseq_g, hmg⟩
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
                                have hget0 : sg.scratch.work_stk2[0]'hws2_0 =
                                    ws2[0]?.getD 0#32 := by
                                  rw [List.getElem?_eq_getElem (by rw [hws2_l]; omega),
                                    Option.getD_some]; simp [hws2_g]
                                have hget1 : sg.scratch.work_stk2[1]'hws2_1 =
                                    ws2[1]?.getD 0#32 := by
                                  rw [List.getElem?_eq_getElem (by rw [hws2_l]; omega),
                                    Option.getD_some]; simp [hws2_g]
                                have hget2 : sg.scratch.work_stk2[2]'hws2_2 =
                                    ws2[2]?.getD 0#32 := by
                                  rw [List.getElem?_eq_getElem (by rw [hws2_l]; omega),
                                    Option.getD_some]; simp [hws2_g]
                                have hload0 : loadVal mg i32 (c.pWorkStk2 + 0#64) =
                                    some (sg.scratch.work_stk2[0]'hws2_0) := by
                                  simpa using FullArenaTactics.load_full_work_stk2 (i := 0) hws2_0
                                    hmg
                                have hload1 : loadVal mg i32 (c.pWorkStk2 + 4#64) =
                                    some (sg.scratch.work_stk2[1]'hws2_1) := by
                                  simpa using FullArenaTactics.load_full_work_stk2 (i := 1) hws2_1
                                    hmg
                                have hload2 : loadVal mg i32 (c.pWorkStk2 + 8#64) =
                                    some (sg.scratch.work_stk2[2]'hws2_2) := by
                                  simpa using FullArenaTactics.load_full_work_stk2 (i := 2) hws2_2
                                    hmg
                                m3_let; refine wp_load_of hload0 ?_
                                m3_let; refine wp_load_of hload1 ?_
                                m3_let; refine wp_load_of hload2 ?_
                                c0_hsteps!; m3_call hTryXorIte
                                refine ⟨64, c, F0, F_cur, sg, R, by decide, Nat.le_refl _, rfl,
                                  hlen_g, hdg.2.1, hdg.2.2.2.1, hdg.2.2.2.2.2.1, ?_, ?_, ?_,
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
                                  exact hJnext (ret, tk' + 4#64, wn, ()) mg'
                                    ⟨{ sg with scratch := { sg.scratch with scratch_buf := scr' } },
                                     s12b_denseInvW_with_scr hdg hscrl', hcv_g, hfl_g, hrep_g,
                                     hinc_g, har_g, hal_g, by omega, hret_hi, hwn_le, hrr_g_ok,
                                     by rw [← hcv_g]; exact hseq', hmg'⟩
                              · clear hc; c0_hsteps!; exact hjg_same
                            · clear hc; m6_split_fast
                              · have hu4 : 4 ≤ usz.toNat := by
                                  simp only [BitVec.ule, decide_eq_true_eq] at hc; bv_omega
                                clear hc; m6_split_fast
                                · have hu5 : usz.toNat ≤ 5 := by
                                    simp only [BitVec.ule, decide_eq_true_eq] at hc; bv_omega
                                  clear hc; m6_split_fast
                                  · clear hc; c0_hsteps!; m3_call hExtractXorK
                                    refine ⟨64, c, F0, F_cur, sg, R, by decide, Nat.le_refl _, rfl,
                                      hlen_g, hdg.2.1, hdg.2.2.1, hdg.2.2.2.1, hdg.2.2.2.2.2.1,
                                      by omega, by omega, by rw [hcv_g]; omega, hgl_hi', hg_cap,
                                      by rw [hcv_g]; exact hseq_g,
                                      by rw [hws2_g]; intro j hj; rw [hcv_g, ← hcv_p]
                                         exact hlt_u j hj,
                                      by rw [hws2_g]; exact hneg_u,
                                      by rw [hws2_g]; exact hent_u, hmg,
                                      fun ret sx mx hlen_x hce hse hmk_x hret_lo hret_hi _ hseq_x
                                        hmx => ?_⟩
                                    have hdx := s12b_denseInvW_of_xorK hdg hlen_x hce hse hmk_x
                                    obtain ⟨hinc_ce, har_ce, hal_ce, hcv_ce, _, _, hfu_ce, hrep_ce,
                                      _⟩ := s12b_core_fields_of_tmp_lm hce
                                    obtain ⟨_, _, hrr_se⟩ := s12b_scr_fields_of_buf hse
                                    c0_hsteps!
                                    exact hJnext (ret, tk' + 8#64, wn, ()) mx
                                      ⟨sx, hdx, hcv_ce.trans hcv_g, hfu_ce.trans hfl_g,
                                       hrep_ce.trans hrep_g, hinc_ce.trans hinc_g,
                                       har_ce.trans har_g, hal_ce.trans hal_g, by omega, hret_hi,
                                       hwn_le, by rw [hrr_se]; exact hrr_g_ok,
                                       by rw [← hcv_g]; exact hseq_x, hmx⟩
                                  · clear hc; c0_hsteps!; exact hjg_same
                                · clear hc; c0_hsteps!; exact hjg_same
                              · clear hc; c0_hsteps!; exact hjg_same
                          · -- Narrow AND (`min_nbc > 0 && max_nbc >= arity`): `hExtAnd` (`64`)
                            intro Jg hJg
                            have hjg0 : Jg (g_len, ticks + 1#64, ()) mb :=
                              hJg (g_len, ticks + 1#64, ()) mb
                                ⟨sb, hdb, hcv_p, hfl_p, hrep_p, hinc_p, har_p, hal_p, rfl, rfl,
                                 hgl_lo, hgl_hi, hseq_p, hmb⟩
                            m6_split_fast
                            · clear hc; m6_split_fast
                              · clear hc; c0_hsteps!; m3_call hExtAnd
                                refine ⟨64, c, F0, F_cur,
                                  { sb with scratch := { sb.scratch with res_sz := ticks + 1#64 } },
                                  R, by unfold step12BCongAndArityMax; decide, rfl,
                                  s12b_denseInvW_with_rsz hdb _, hu_lt3, by omega, hu_cv, hgl_hi,
                                  hg_cap,
                                  step12BGateSeqOk_of_fid (by decide) (by rw [hcv_p]; exact hseq_p),
                                  hlt_u,
                                  fun j hj j2 hj2 hne heq =>
                                hdiff_u j hj j2 hj2 hne
                                  (by dsimp only at heq; exact congrArg (· / 2) heq),
                                  hent_u, hm, fun ret lm' scr' rsz' m' hdw' hret_lo hret_hi _
                                    hseq' hm' => ?_⟩
                                c0_hsteps!
                                exact hJg (ret, rsz', ()) m'
                                  ⟨_, hdw', hcv_p, hfl_p, hrep_p, hinc_p, har_p, hal_p, rfl, rfl,
                                   by omega, hret_hi,
                                   by rw [← hcv_p]
                                      exact step12BGateSeqOk_to_fid (by decide) hseq', hm'⟩
                              · clear hc; c0_hsteps!; exact hjg0
                            · clear hc; c0_hsteps!; exact hjg0
                        · clear hc; c0_hsteps!; exact hJel () mb rfl
                      · clear hc; c0_hsteps!; exact hJel () mb rfl
                    · clear hc; c0_hsteps!; exact hJel () mb rfl
              · -- Pass 1 literal collection loop body
                rintro B3 L3 rem3 ⟨usz, max_nbc, min_nbc, neg_p, k, ⟨⟩⟩ mk hB3 hL3
                  ⟨ws2, hws2_l, hk_le, rfl, hu_max, hu_k, hu_cv, hlt_u, hneg_u,
                   ⟨idxs, hid_len, hid_nd, hid_lt, hws2_map, hcov_k⟩, hmk⟩
                m6_split_fast
                · have hk_lt : k.toNat < sz_bv.toNat := by
                    simp only [BitVec.ult, decide_eq_true_eq] at hc; exact hc
                  have hk1_n : (k + 1#32).toNat = k.toNat + 1 := by bv_omega
                  have hp3k_n : (p + 3#64 + k.setWidth 64).toNat = p.toNat + 3 + k.toNat :=
                    bv64_add_zext32 (k := 3) (by omega)
                  have hp3k_arr : (p + 3#64 + k.setWidth 64).toNat < sp.core.arena.length := by
                    omega
                  let lk := sp.core.arena[(p + 3#64 + k.setWidth 64).toNat]'hp3k_arr
                  have hlk_eq : lk = sp.core.arena[p.toNat + 3 + k.toNat]'(by omega) :=
                    list_getElem_congr hp3k_n hp3k_arr (by omega)
                  have hlk_lt : lk.toNat < 2 * sp.core.cur_vars := by
                    have hmem_lk : lk.toNat ∈ fullArenaClauseLits sp p.toNat := by
                      unfold fullArenaClauseLits fullArenaClauseLitsCore
                      have hsz_szbv : fullArenaClauseSizeCore sp.core p.toNat = sz_bv.toNat :=
                        hsz_eq
                      simp only [List.mem_map]; refine ⟨lk, ?_, rfl⟩
                      have hk_s : k.toNat < fullArenaClauseSizeCore sp.core p.toNat := by
                        rw [hsz_szbv]; exact hk_lt
                      have hget : ((sp.core.arena.drop (p.toNat + 3)).take
                          (fullArenaClauseSizeCore sp.core p.toNat))[k.toNat]'(by
                            simp [List.length_take, List.length_drop, hsz_szbv]; omega) = lk := by
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
                      have h0 := hdp.2.1.vals_domain lk.toNat hlk_lt
                      rw [List.getElem?_eq_getElem hlk_v', Option.getD_some] at h0
                      rw [list_getElem_congr (bv_zext32_toNat lk) hlk_v hlk_v']; exact h0
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
                      · have hu_ltm : usz.toNat < 1000001 := by
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
                            rw [bv_zext32_toNat, hws1_pl]
                            exact Nat.lt_of_lt_of_le hlk_lt (by omega)
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
                          refine wp_join_group (ts := [i32]) (fun (_mx, ()) mmx => mmx = m_st) ?_ ?_
                          · rintro _ ⟨mx', ⟨⟩⟩ mmx hmmx; rw [hmmx]
                            c0_hsteps_nogrp
                            refine wp_join_group (ts := [i32]) (fun (_mn, ()) mmn => mmn = m_st)
                              ?_ ?_
                            · rintro _ ⟨mn', ⟨⟩⟩ mmn hmmn; rw [hmmn]
                              c0_hsteps_nogrp
                              refine wp_join_group (ts := [i32])
                                (fun (np', ()) mnp => mnp = m_st ∧
                                  np' = (if (lk &&& 1#32) != 0#32 then neg_p ^^^ 1#32 else neg_p))
                                ?_ ?_
                              · rintro _ ⟨neg_p', ⟨⟩⟩ mnp ⟨hmnp, hnp'⟩; rw [hmnp, hnp']
                                c0_hsteps!
                                refine hL3 (sz_bv.toNat - (k + 1#32).toNat)
                                  (usz + 1#32, mx', mn',
                                   (if (lk &&& 1#32) != 0#32 then neg_p ^^^ 1#32 else neg_p),
                                   k + 1#32, ()) m_st (by omega)
                                  ⟨ws2', by simp [ws2', hws2_l], by omega, rfl, by omega, by omega,
                                   by omega, fun j hj => ?_, ?_, ?_, hm2⟩
                                · dsimp only [ws2']; by_cases hju : j = usz.toNat
                                  · subst hju; rw [List.getElem?_set_self hu_ws2, Option.getD_some]
                                    exact hlk_lt
                                  · rw [List.getElem?_set_ne (Ne.symm hju)]
                                    exact hlt_u j (by omega)
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
                                      simp only [List.range_succ, List.foldl_append,
                                        List.foldl_cons, List.foldl_nil, ih (by omega)]
                                      congr 2; dsimp only [ws2']
                                      rw [List.getElem?_set_ne (by omega)]
                                  rw [hfold_eq usz.toNat (Nat.le_refl _), ← hneg_u]
                                  have hlast : ws2'[usz.toNat]?.getD 0#32 = lk := by
                                    dsimp only [ws2']
                                    rw [List.getElem?_set_self hu_ws2, Option.getD_some]
                                  rw [hlast]; exact s12b_bv32_bit1_ne0_mod2
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
                                      rw [List.getElem?_append_left (by omega)]
                                      exact hws2_map j (by omega)
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
                    · have hne0 : sp.core.vals[(lk.setWidth 64).toNat]'hlk_v ≠ 0#8 :=
                        FullM3CongBva.bv8_ne0_of_signExtend32 hdom_lk (beq_eq_false_iff_ne.mp hc)
                      have hff_lk : sp.core.vals[(lk.setWidth 64).toNat]?.getD 0#8 = 0xFF#8 := by
                        rw [List.getElem?_eq_getElem hlk_v, Option.getD_some]
                        exact FullM3CongBva.bv8_ne0_not_signExtend32_sgt0_eqff hdom_lk hne0 hnsgt
                      c0_hsteps!
                      refine hL3 (sz_bv.toNat - (k + 1#32).toNat)
                        (usz, max_nbc, min_nbc, neg_p, k + 1#32, ()) mk (by omega)
                        ⟨ws2, hws2_l, by omega, rfl, hu_max, by omega, hu_cv, hlt_u, hneg_u,
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
                  obtain ⟨hdiff_u, hent_u⟩ := s12b_clause_collect_done hdp hp_ref hng hsz_eq
                    hbd_sz (by omega) hid_len hid_nd (hk_e ▸ hid_lt) hws2_map (hk_e ▸ hcov_k)
                  c0_hsteps!
                  exact hB3 (usz, max_nbc, min_nbc, neg_p, false, k, ()) mk
                    ⟨ws2, hws2_l, fun _ => ⟨hu_max, hu_cv, hlt_u, hneg_u, hdiff_u, hent_u⟩, hmk⟩
              · intro _ L3 _ hL3; c0_hsteps!
                exact hL3 sz_bv.toNat (0#32, 0#32, 0xFFFFFFFF#32, 0#32, 0#32, ()) mp
                  ⟨sp.scratch.work_stk2, hws2_pl, Nat.zero_le _, rfl, Nat.zero_le _,
                   Nat.zero_le _, Nat.zero_le _, (fun _ h => by cases h), (by simp),
                   ⟨[], rfl, .nil, (fun _ h => by cases h), (fun _ h => by cases h),
                    (fun _ h => by cases h)⟩, hmp⟩
            · clear hc; c0_hsteps!; exact hjnext_same
          · clear hc; c0_hsteps!; exact hjnext_same
        · clear hc; c0_hsteps!; exact hjp2_now
      · clear hc; c0_hsteps!; exact hjp2_now
    · clear hc; c0_hsteps!; exact hjp2_now

/-! ## 3. `full_cong_extract_s12b_wp` (`step12BCongExtractSpec`) -/

theorem full_cong_extract_s12b_wp (Γ : Env)
    (hExtractFrom : ∀ args m Q X, step12BCongExtractFromSpec args m Q X →
      Γ "full_cong_extract_from_fid" [i64, i64, i64, i64] [i64] args m Q X) :
    ∀ args m Q X, step12BCongExtractSpec args m Q X →
      Func.wp Γ fidStep12BCongExtractFn.body args m Q X := by
  rintro ⟨h, g_cap, tick_lim, ⟨⟩⟩ m0 Q X ⟨c, F0, F_cur, s, R, rfl, hd, hg_cap, hm0, hQ⟩
  unfold fidStep12BCongExtractFn; dsimp only
  m3_call hExtractFrom
  refine ⟨c, F0, F_cur, s, R, rfl, hd, Nat.zero_le _, hg_cap, .done, hm0,
    fun ret s' m' hd' hcv' hfl' hrep' hinc' _ hret_hi hseq' hm' => ?_⟩
  c0_hsteps!
  exact hQ ret s' m' hd' hcv' hfl' hrep' hinc' hret_hi hseq' hm'

end LeanQbe.T.Examples.Kissat.FullFidelityStep12B

end
