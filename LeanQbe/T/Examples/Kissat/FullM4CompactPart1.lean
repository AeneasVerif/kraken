/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM4CompactLemmas
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Full` M4a Compaction Verification — Part 1 (`9/13` functions)

Proves `Func.wp` contracts for `needed`, `sift_q`, `vmtf`, `sift_h`, `heap`,
`assign_map`, `record_ext`, `vars`, and `mark_live` (`9/13` functions).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM4Compact

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.C0Step
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open Kraken.Bedrock2.Test

open FullArenaTactics FullCompactTactics
open scoped FullArenaTactics FullCompactTactics

private theorem bv8_sext32_eq0 {x : BitVec 8} (h : x.signExtend 32 = 0#32) : x = 0#8 := by
  ext i hi; have h1 := congrArg (·[i]) h
  simp [BitVec.getElem_signExtend, hi] at h1; simp [h1]

private theorem compact_scratch_len_eq {c : FullCfg} {a b : FullScratch}
    (h : FullScratch.LengthsOk c a)
    (h1 : b.walk_vals = a.walk_vals := by rfl) (h2 : b.phases = a.phases := by rfl)
    (h3 : b.phases_target = a.phases_target := by rfl)
    (h4 : b.phases_best = a.phases_best := by rfl)
    (h5 : b.walk_best = a.walk_best := by rfl) (h6 : b.heap = a.heap := by rfl)
    (h7 : b.pos = a.pos := by rfl) (h8 : b.shrink_stk = a.shrink_stk := by rfl)
    (h9 : b.q_prev = a.q_prev := by rfl) (h10 : b.q_next = a.q_next := by rfl)
    (h11 : b.q_stamp = a.q_stamp := by rfl) (h12 : b.wsort = a.wsort := by rfl)
    (h13 : b.work_stk1 = a.work_stk1 := by rfl)
    (h14 : b.work_stk2 = a.work_stk2 := by rfl)
    (h15 : b.tarjan_mark = a.tarjan_mark := by rfl)
    (h16 : b.tarjan_reach = a.tarjan_reach := by rfl) (h17 : b.score = a.score := by rfl)
    (h18 : b.sim_sig = a.sim_sig := by rfl) (h19 : b.glue_used = a.glue_used := by rfl)
    (h20 : b.last_learned = a.last_learned := by rfl)
    (h21 : b.delayed = a.delayed := by rfl) (h22 : b.red_refs = a.red_refs := by rfl)
    (h23 : b.extend_stk = a.extend_stk := by rfl)
    (h24 : b.scratch_buf = a.scratch_buf := by rfl) : FullScratch.LengthsOk c b :=
  ⟨h1 ▸ h.walk_vals_len, h2 ▸ h.phases_len, h3 ▸ h.phases_target_len, h4 ▸ h.phases_best_len,
   h5 ▸ h.walk_best_len, h6 ▸ h.heap_len_arr, h7 ▸ h.pos_len, h8 ▸ h.shrink_stk_len,
   h9 ▸ h.q_prev_len, h10 ▸ h.q_next_len, h11 ▸ h.q_stamp_len, h12 ▸ h.wsort_len,
   h13 ▸ h.work_stk1_len, h14 ▸ h.work_stk2_len, h15 ▸ h.tarjan_mark_len,
   h16 ▸ h.tarjan_reach_len, h17 ▸ h.score_len, h18 ▸ h.sim_sig_len, h19 ▸ h.glue_used_len,
   h20 ▸ h.last_learned_len, h21 ▸ h.delayed_len_arr, h22 ▸ h.red_refs_len,
   h23 ▸ h.extend_stk_len, h24 ▸ h.scratch_buf_len⟩

@[scoped c0_load] theorem load_full_wsort_z0 {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hi : 0 < s.scratch.wsort.length)
    (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 (c.pWsort + 0#64) = some s.scratch.wsort[0] := by
  rw [BitVec.add_zero]; exact load_full_wsort0 hi hm

@[scoped c0_store] theorem store_full_wsort_z0 {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32)
    (hi : 0 < s.scratch.wsort.length) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 (c.pWsort + 0#64) ∧
      (FullMem c { s with scratch := { s.scratch with
        wsort := s.scratch.wsort.set 0 v } } ⋆ R)
        (storeMem m i32 (c.pWsort + 0#64) v) := by
  rw [BitVec.add_zero]; exact store_full_wsort0 v hi hm

@[scoped c0_store] theorem store_full_frame_trail_z0 {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32)
    (hi : 0 < s.core.frame_trail.length) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 (c.pFrameTrail + 0#64) ∧
      (FullMem c { s with core := { s.core with
        frame_trail := s.core.frame_trail.set 0 v } } ⋆ R)
        (storeMem m i32 (c.pFrameTrail + 0#64) v) := by
  rw [BitVec.add_zero]; exact store_full_frame_trail0 v hi hm

@[scoped c0_store] theorem store_full_frame_dec_z0 {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32)
    (hi : 0 < s.core.frame_dec.length) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 (c.pFrameDec + 0#64) ∧
      (FullMem c { s with core := { s.core with
        frame_dec := s.core.frame_dec.set 0 v } } ⋆ R)
        (storeMem m i32 (c.pFrameDec + 0#64) v) := by
  rw [BitVec.add_zero]; exact store_full_frame_dec0 v hi hm

attribute [local bv_c0] Bool.true_eq_false Bool.false_eq_true

local macro "cm_while_true" : tactic =>
  `(tactic| (cm_split <;> try { exfalso; c0_bound }))

open Lean Elab Tactic in
local elab "cm_jnz" : tactic => do
  let rec go (fuel : Nat) : TacticM Unit := do
    if fuel = 0 then return
    let ty ← Lean.instantiateMVars (← (← getMainGoal).getType)
    if ty.isAppOf ``And && ty.getAppNumArgs == 2 then
      try evalTactic (← `(tactic| cm_strip)); go (fuel - 1); return catch _ => return
    if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
        ((ty.getArg! 4).headBeta).isAppOf ``LeanQbe.T.Expr.jnz then
      let hc := mkIdent `hc
      evalTactic (← `(tactic|
        refine LeanQbe.T.wp_jnz_of (fun $hc:ident => ?_) (fun $hc:ident => ?_)))
      evalTactic (← `(tactic| all_goals
        (try simp only [LeanQbe.T.Arg.val_var, LeanQbe.T.Arg.val_imm] at $hc:ident)
        c0_cond $hc
        try c0_let_simp))
      return
    if ← LeanQbe.T.C0Step.stepOnce then go (fuel - 1)
  evalTactic (← `(tactic| try cm_unmdata))
  go 100

/-! ## 1. `Func.wp` Proofs — Part 1 (`9/13` functions) -/

theorem full_compact_needed_wp (Γ : Env) :
    ∀ a m Q X, fullCompactNeededSpec a m Q X → Func.wp Γ full_compact_needed_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, _, hm, hQ⟩
  have hcv := hlen.core_ok.cur_vars_le
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  cm_steps <;>
    first
    | (exact hQ false fun hf => Bool.noConfusion hf)
    | (exact hQ _ fun hres => by
        have hcl0 : s.core.cur_level = 0 := by c0_bound
        have hdm0 : s.core.dense_mode = 0#64 := by c0_bound
        have hcv128 : 128 ≤ s.core.cur_vars := by c0_bound
        exact ⟨hcl0, hdm0, hcv128⟩)

theorem full_compact_sift_q_wp (Γ : Env) :
    ∀ a m Q X, fullCompactSiftQSpec a m Q X → Func.wp Γ full_compact_sift_q_body a m Q X := by
  rintro ⟨qs_ptr, ws_ptr, start, n, ⟨⟩⟩ m Q X ⟨qs, ws, R, hsn, hn_ws, hn62, hqs_ok, hm, hQ⟩
  cm_steps
  refine wp_loop_inv
    (fun (root, ()) mL =>
      root.toNat ≤ n.toNat ∧
      ∃ wsL : List (BitVec 32), wsL.length = ws.length ∧
        (∀ k, n.toNat ≤ k → wsL[k]? = ws[k]?) ∧
        (∀ k < n.toNat, ∃ j < n.toNat, wsL[k]? = ws[j]?) ∧
        (array (t := i32) qs_ptr qs ⋆ array (t := i32) ws_ptr wsL ⋆ R) mL)
    (fun (root, ()) _ => n.toNat - root.toNat)
    (fun JL hLoop => ?_) ?_
  · cm_steps; exact hLoop (start, ()) m ⟨hsn, ws, rfl, fun _ _ => rfl, fun k hk => ⟨k, hk, rfl⟩, hm⟩
  · rintro JL ⟨root, ⟨⟩⟩ mL ⟨hrt_le, wsL, hlenL, houtL, hmemL, hmL⟩ hLoop
    have hch0_eq : ((root <<< (1 : Nat)) + (1 : BitVec 64)).toNat = 2 * root.toNat + 1 := by
      rw [bv64_add1 (by rw [bv64_shl1_toNat (by omega)]; omega), bv64_shl1_toNat (by omega)]
    have hqsL : ∀ k < n.toNat, (wsL[k]?.getD 0#32).toNat < qs.length := fun k hk => by
      obtain ⟨j, hj, heq⟩ := hmemL k hk; rw [heq]; exact hqs_ok j hj
    cm_while_true
    cm_split
    · cm_steps; exact hQ wsL mL hlenL houtL hmemL hmL
    · have hch_lt : 2 * root.toNat + 1 < n.toNat := by c0_bound
      have hrt_lt : root.toNat < n.toNat := by omega
      have hch_ws : 2 * root.toNat + 1 < wsL.length := by omega
      have hch_qs : (wsL[2 * root.toNat + 1]'hch_ws).toNat < qs.length := by
        simpa [List.getElem?_eq_getElem hch_ws] using hqsL (2 * root.toNat + 1) hch_lt
      have hch0_ws : ((root <<< (1 : Nat)) + (1 : BitVec 64)).toNat < wsL.length := by
        rw [hch0_eq]; exact hch_ws
      have hch0_qs : (wsL[((root <<< (1 : Nat)) + (1 : BitVec 64)).toNat]'hch0_ws).toNat <
          qs.length := by
        simp only [hch0_eq]; exact hch_qs
      cm_to_group
      refine wp_join_group (ts := [i64, i32, i32])
        (fun (ch, _cv, _cs, ()) mJ =>
          mL = mJ ∧ ch.toNat < n.toNat ∧ root.toNat < ch.toNat ∧ ch.toNat < wsL.length ∧
          _cv = wsL[ch.toNat]?.getD 0#32 ∧
          _cs = qs[(wsL[ch.toNat]?.getD 0#32).toNat]?.getD 0#32)
        ?_ ?_
      · rintro _ ⟨ch, cv, cs, ⟨⟩⟩ mJ ⟨hm_eq, hch_n, hrt_ch, hch_len, hcv_eq, _⟩
        subst mJ
        rw [List.getElem?_eq_getElem hch_len, Option.getD_some] at hcv_eq
        have hrt_ws : root.toNat < wsL.length := by omega
        have hrt_qs : (wsL[root.toNat]'hrt_ws).toNat < qs.length := by
          simpa [List.getElem?_eq_getElem hrt_ws] using hqsL root.toNat hrt_lt
        cm_steps
        · exact hQ wsL mL hlenL houtL hmemL hmL
        · let rv := wsL[root.toNat]'hrt_ws
          let ws1 := wsL.set root.toNat (wsL[ch.toNat]'hch_len)
          let ws2 := ws1.set ch.toNat rv
          have hlen2 : ws2.length = ws.length := by
            dsimp only [ws2, ws1]; rw [List.length_set, List.length_set]; exact hlenL
          have hout2 : ∀ k, n.toNat ≤ k → ws2[k]? = ws[k]? := fun k hk => by
            dsimp only [ws2, ws1]
            rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
            exact houtL k hk
          have hmem2 : ∀ k < n.toNat, ∃ j < n.toNat, ws2[k]? = ws[j]? := fun k hk => by
            by_cases hkc : k = ch.toNat
            · subst hkc; obtain ⟨j, hj, heq⟩ := hmemL root.toNat hrt_lt
              refine ⟨j, hj, ?_⟩; dsimp only [ws2, ws1]
              rw [List.getElem?_set_self (by rw [List.length_set]; exact hch_len), ← heq]
              exact (List.getElem?_eq_getElem hrt_ws).symm
            · by_cases hkr : k = root.toNat
              · subst hkr; obtain ⟨j, hj, heq⟩ := hmemL ch.toNat hch_n
                refine ⟨j, hj, ?_⟩; dsimp only [ws2, ws1]
                rw [List.getElem?_set_ne (Ne.symm hkc), List.getElem?_set_self hrt_ws, ← heq]
                exact (List.getElem?_eq_getElem hch_len).symm
              · obtain ⟨j, hj, heq⟩ := hmemL k hk
                refine ⟨j, hj, ?_⟩; dsimp only [ws2, ws1]
                rw [List.getElem?_set_ne (Ne.symm hkc), List.getElem?_set_ne (Ne.symm hkr), heq]
          exact hLoop (ch, ()) m (by dsimp only; omega)
            ⟨by omega, ws2, hlen2, hout2, hmem2,
             by dsimp only [ws2, ws1, rv]; rw [← hcv_eq]
                rw [sep_comm (array (t := i32) qs_ptr qs), sep_assoc]; exact hm⟩
      · intro Jj hJj
        have hch0_z : ((wsL[2 * root.toNat + 1]'hch_ws).setWidth 64).toNat =
            (wsL[2 * root.toNat + 1]'hch_ws).toNat := zext_toNat _ (by decide)
        cm_split
        · have hch1_eq : (((root <<< (1 : Nat)) + (1 : BitVec 64)) + (1 : BitVec 64)).toNat =
              2 * root.toNat + 2 := by
            rw [bv64_add1 (by rw [hch0_eq]; omega), hch0_eq]
          have hch1_lt : 2 * root.toNat + 2 < n.toNat := by c0_bound
          have hch1_ws : 2 * root.toNat + 2 < wsL.length := by omega
          have hch1_qs : (wsL[2 * root.toNat + 2]'hch1_ws).toNat < qs.length := by
            simpa [List.getElem?_eq_getElem hch1_ws] using hqsL (2 * root.toNat + 2) hch1_lt
          have hch1_ws0 : (((root <<< (1 : Nat)) + (1 : BitVec 64)) + (1 : BitVec 64)).toNat <
              wsL.length := by rw [hch1_eq]; exact hch1_ws
          have hch1_qs0 :
              (wsL[(((root <<< (1 : Nat)) + (1 : BitVec 64)) +
                (1 : BitVec 64)).toNat]'hch1_ws0).toNat < qs.length := by
            simp only [hch1_eq]; exact hch1_qs
          have hch1_z : ((wsL[2 * root.toNat + 2]'hch1_ws).setWidth 64).toNat =
              (wsL[2 * root.toNat + 2]'hch1_ws).toNat := zext_toNat _ (by decide)
          cm_steps
          · refine hJj _ mL ⟨rfl, by rw [hch1_eq]; exact hch1_lt, by omega, by omega, ?_, ?_⟩
            · simp only [hch1_eq, List.getElem?_eq_getElem hch1_ws, Option.getD_some]
            · simp only [hch1_eq, List.getElem?_eq_getElem hch1_ws, Option.getD_some,
                hch1_z, List.getElem?_eq_getElem hch1_qs]
          · refine hJj _ mL ⟨rfl, by rw [hch0_eq]; exact hch_lt, by omega, by omega, ?_, ?_⟩
            · simp only [hch0_eq, List.getElem?_eq_getElem hch_ws, Option.getD_some]
            · simp only [hch0_eq, List.getElem?_eq_getElem hch_ws, Option.getD_some,
                hch0_z, List.getElem?_eq_getElem hch_qs]
        · cm_steps
          refine hJj _ mL ⟨rfl, by rw [hch0_eq]; exact hch_lt, by omega, by omega, ?_, ?_⟩
          · simp only [hch0_eq, List.getElem?_eq_getElem hch_ws, Option.getD_some]
          · simp only [hch0_eq, List.getElem?_eq_getElem hch_ws, Option.getD_some,
              hch0_z, List.getElem?_eq_getElem hch_qs]

theorem full_compact_vmtf_wp (Γ : Env)
    (hsift : ∀ a m Q X, fullCompactSiftQSpec a m Q X →
      Γ "full_compact_sift_q" [i64, i64, i64, i64] [] a m Q X) :
    ∀ a m Q X, fullCompactVmtfSpec a m Q X → Func.wp Γ full_compact_vmtf_body a m Q X := by
  rintro ⟨h, ncv, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hncv_le, hm, hQ⟩
  have hmax_lt : c.max_vars < 2 * 2 ^ 28 := c.hmaxv
  have hqs_len := hlen.scratch_ok.q_stamp_len
  have hqp_len := hlen.scratch_ok.q_prev_len
  have hqn_len := hlen.scratch_ok.q_next_len
  have hws_len := hlen.scratch_ok.wsort_len
  cm_split
  · cm_steps
    let sc' : FullScratch :=
      { s.scratch with q_first := 0xFFFFFFFF#64, q_last := 0xFFFFFFFF#64,
                       q_search_idx := 0xFFFFFFFF#64, q_search_stamp := 0#64,
                       q_cur_stamp := 0#64 }
    exact hQ sc' m ⟨hlen.core_ok, compact_scratch_len_eq hlen.scratch_ok⟩
      ⟨rfl, rfl⟩ rfl rfl (by dsimp only [sc']; exact hm)
  · have hncv_pos : 0 < ncv.toNat := by c0_bound
    have hncv_lt62 : ncv.toNat < 2 ^ 62 := by omega
    cm_steps
    refine wp_loop_inv
      (fun (i, ()) m1 =>
        i.toNat ≤ ncv.toNat ∧
        ∃ ws1 : List (BitVec 32), ws1.length = 2 * c.max_vars ∧
          (∀ k < i.toNat, ws1[k]? = some (BitVec.ofNat 32 k)) ∧
          (FullMem c { s with scratch := { s.scratch with wsort := ws1 } } ⋆ R) m1)
      (fun (i, ()) _ => ncv.toNat - i.toNat)
      (fun J1 hLoop1 => ?_) ?_
    · cm_steps; exact hLoop1 (0#64, ()) m ⟨Nat.zero_le _, s.scratch.wsort, hws_len,
        fun _ hk => by simp at hk, hm⟩
    · rintro J1 ⟨i, ⟨⟩⟩ m1 ⟨hi_le, ws1, hws1_len, hinit1, hm1⟩ hLoop1
      cm_split
      · have hi_lt : i.toNat < ncv.toNat := by c0_bound
        have hi1_eq : (i + (1 : BitVec 64)).toNat = i.toNat + 1 := bv64_add1 (by omega)
        cm_steps
        refine hLoop1 (i + (1 : BitVec 64), ()) m (by dsimp only; rw [hi1_eq]; omega)
          ⟨by rw [hi1_eq]; omega, ws1.set i.toNat (i.setWidth 32), by simp [hws1_len],
           fun k hk => ?_, compactMem_cast hm rfl⟩
        rw [hi1_eq] at hk
        by_cases hki : k = i.toNat
        · subst hki; rw [List.getElem?_set_self (by omega)]; congr 1
        · rw [List.getElem?_set_ne (Ne.symm hki)]; exact hinit1 k (by omega)
      · have hi_eq : i.toNat = ncv.toNat := by c0_bound
        rw [hi_eq] at hinit1
        clear hLoop1 J1
        cm_to_group
        refine wp_join_group
          (fun () m2 =>
            ∃ ws2 : List (BitVec 32), ws2.length = 2 * c.max_vars ∧
              (∀ k < ncv.toNat, (ws2[k]?.getD 0#32).toNat < ncv.toNat) ∧
              (FullMem c { s with scratch := { s.scratch with wsort := ws2 } } ⋆ R) m2)
          ?_ ?_
        · rintro _ ⟨⟩ m2 ⟨ws2, hws2_len, hws2_lt, hm2⟩
          cm_steps
          refine wp_loop_inv
            (fun (i2, ()) m3 =>
              i2.toNat ≤ ncv.toNat ∧
              ∃ qs3 qp3 qn3 : List (BitVec 32),
                qs3.length = c.max_vars ∧ qp3.length = c.max_vars ∧ qn3.length = c.max_vars ∧
                (FullMem c { s with scratch := { s.scratch with
                  wsort := ws2, q_stamp := qs3, q_prev := qp3, q_next := qn3 } } ⋆ R) m3)
            (fun (i2, ()) _ => ncv.toNat - i2.toNat)
            (fun J3 hLoop3 => ?_) ?_
          · cm_steps; exact hLoop3 (0#64, ()) m2 ⟨Nat.zero_le _, s.scratch.q_stamp,
              s.scratch.q_prev, s.scratch.q_next, hqs_len, hqp_len, hqn_len, hm2⟩
          · rintro J3 ⟨i2, ⟨⟩⟩ m3 ⟨hi2_le, qs3, qp3, qn3, hqs3, hqp3, hqn3, hm3⟩ hLoop3
            cm_split
            · have hi2_lt : i2.toNat < ncv.toNat := by c0_bound
              have hv_lt : (ws2[i2.toNat]'(by omega)).toNat < ncv.toNat := by
                simpa [List.getElem?_eq_getElem (by omega : i2.toNat < ws2.length)] using
                  hws2_lt i2.toNat hi2_lt
              have hi2_1_eq : (i2 + (1 : BitVec 64)).toNat = i2.toNat + 1 := bv64_add1 (by omega)
              have hv_lt64 : ((ws2[i2.toNat]'(by omega)).setWidth 64).toNat < c.max_vars := by
                rw [zext_toNat _ (by decide)]; omega
              cm_to_group
              refine wp_join_group (ts := [i32]) (fun (pv, ()) mP => mP = m3) ?_ ?_
              · rintro _ ⟨pv, ⟨⟩⟩ mP hmP
                rw [hmP]
                cm_to_group
                refine wp_join_group (ts := [i32]) (fun (nv, ()) mN => mN = m) ?_ ?_
                · rintro _ ⟨nv, ⟨⟩⟩ mN hmN
                  rw [hmN]
                  cm_steps
                  refine hLoop3 (i2 + (1 : BitVec 64), ()) m (by dsimp only; rw [hi2_1_eq]; omega)
                    ⟨by rw [hi2_1_eq]; omega, _, _, _,
                     by rw [List.length_set]; exact hqs3,
                     by rw [List.length_set]; exact hqp3,
                     by rw [List.length_set]; exact hqn3, hm⟩
                · intro Jn hJn
                  cm_split
                  · cm_steps; exact hJn _ m rfl
                  · have hi2p1_lt : (i2 + (1 : BitVec 64)).toNat < ws2.length := by
                      rw [hi2_1_eq]; c0_bound
                    cm_steps; exact hJn _ m rfl
              · intro Jp hJp
                cm_split
                · cm_steps; exact hJp _ m3 rfl
                · have hi2_pos : 0 < i2.toNat := by bv_omega
                  have hi2m1_eq : (i2 - (1 : BitVec 64)).toNat = i2.toNat - 1 := by bv_omega
                  have hi2m1_lt : (i2 - (1 : BitVec 64)).toNat < ws2.length := by
                    rw [hi2m1_eq]; omega
                  cm_steps; exact hJp _ m3 rfl
            · have h0_ws2 : 0 < ws2.length := by omega
              have hncvm1_eq : (ncv - (1 : BitVec 64)).toNat = ncv.toNat - 1 := by bv_omega
              have hncvm1_lt : (ncv - (1 : BitVec 64)).toNat < ws2.length := by
                rw [hncvm1_eq]; omega
              let sc3 : FullScratch :=
                { s.scratch with
                  wsort := ws2, q_stamp := qs3, q_prev := qp3, q_next := qn3,
                  q_first := (ws2[0]'h0_ws2).setWidth 64,
                  q_last := (ws2[(ncv - (1 : BitVec 64)).toNat]'hncvm1_lt).setWidth 64,
                  q_search_idx := (ws2[(ncv - (1 : BitVec 64)).toNat]'hncvm1_lt).setWidth 64,
                  q_search_stamp := ncv, q_cur_stamp := ncv }
              cm_steps
              exact hQ sc3 m (by
                dsimp only [sc3]
                exact ⟨hlen.core_ok, { hlen.scratch_ok with
                  q_prev_len := hqp3, q_next_len := hqn3, q_stamp_len := hqs3,
                  wsort_len := hws2_len }⟩) ⟨rfl, rfl⟩ rfl rfl (by dsimp only [sc3]; exact hm)
        · intro J2 hJ2
          cm_split
          · have hncv_gt1 : 1 < ncv.toNat := by c0_bound
            cm_steps
            refine wp_loop_inv
              (fun (st, ()) mB =>
                st.toNat ≤ ncv.toNat ∧
                ∃ wsB : List (BitVec 32), wsB.length = 2 * c.max_vars ∧
                  (∀ k < ncv.toNat, (wsB[k]?.getD 0#32).toNat < ncv.toNat) ∧
                  (FullMem c { s with scratch := { s.scratch with wsort := wsB } } ⋆ R) mB)
              (fun (st, ()) _ => st.toNat)
              (fun Jb hLoopB => ?_) ?_
            · cm_steps
              have hst0 : (ncv >>> (1 : Nat)).toNat ≤ ncv.toNat := by
                simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; omega
              exact hLoopB (ncv >>> (1 : Nat), ()) m1 ⟨hst0, ws1, hws1_len, fun k hk => by
                rw [hinit1 k hk, Option.getD_some, bv32_ofNat_toNat (by omega)]; exact hk, hm1⟩
            · rintro Jb ⟨st, ⟨⟩⟩ mB ⟨hst_le, wsB, hwsB_len, hwsB_lt, hmB⟩ hLoopB
              cm_split
              · have hst_pos : 0 < st.toNat := by c0_bound
                have hst1_eq : (st - (1 : BitVec 64)).toNat = st.toNat - 1 := by bv_omega
                let sB : FullState := { s with scratch := { s.scratch with wsort := wsB } }
                cm_steps; c0_call hsift
                refine ⟨s.scratch.q_stamp, wsB, CompactVmtfRest c sB ⋆ R,
                  by rw [hst1_eq]; omega, by omega, hncv_lt62,
                  fun k hk => by have := hwsB_lt k hk; omega,
                  focus_vmtf_arrays hmB,
                  fun wsB' mB' hlen' _ hmem' hmB' => ?_⟩
                cm_steps
                refine hLoopB (st - (1 : BitVec 64), ()) mB' (by dsimp only; rw [hst1_eq]; omega)
                  ⟨by rw [hst1_eq]; omega, wsB', by omega, fun k hk => ?_, ?_⟩
                · obtain ⟨j, hj, heq⟩ := hmem' k hk; rw [heq]; exact hwsB_lt j hj
                · exact unfocus_vmtf_arrays (s := sB) hmB'
              · cm_steps
                refine wp_loop_inv
                  (fun (ed, ()) mE =>
                    ed.toNat < ncv.toNat ∧
                    ∃ wsE : List (BitVec 32), wsE.length = 2 * c.max_vars ∧
                      (∀ k < ncv.toNat, (wsE[k]?.getD 0#32).toNat < ncv.toNat) ∧
                      (FullMem c { s with scratch := { s.scratch with wsort := wsE } } ⋆ R) mE)
                  (fun (ed, ()) _ => ed.toNat)
                  (fun Je hLoopE => ?_) ?_
                · cm_steps; exact hLoopE (ncv - 1#64, ()) mB ⟨by bv_omega, wsB, hwsB_len,
                    hwsB_lt, hmB⟩
                · rintro Je ⟨ed, ⟨⟩⟩ mE ⟨hed_lt, wsE, hwsE_len, hwsE_lt, hmE⟩ hLoopE
                  cm_split
                  · have hed_pos : 0 < ed.toNat := by c0_bound
                    have h0_ws : 0 < wsE.length := by omega
                    have hed_ws : ed.toNat < wsE.length := by omega
                    let ws_sw := (wsE.set 0 (wsE[ed.toNat]'hed_ws)).set ed.toNat (wsE[0]'h0_ws)
                    have hsw_len : ws_sw.length = 2 * c.max_vars := by simp [ws_sw, hwsE_len]
                    have hsw_lt : ∀ k < ncv.toNat, (ws_sw[k]?.getD 0#32).toNat < ncv.toNat := by
                      intro k hk; dsimp only [ws_sw]
                      by_cases hke : k = ed.toNat
                      · subst hke; rw [List.getElem?_set_self (by simp [hwsE_len]; omega),
                          Option.getD_some]
                        simpa [List.getElem?_eq_getElem h0_ws] using hwsE_lt 0 (by omega)
                      · by_cases hk0 : k = 0
                        · subst hk0; rw [List.getElem?_set_ne (Ne.symm hke),
                            List.getElem?_set_self h0_ws, Option.getD_some]
                          simpa [List.getElem?_eq_getElem hed_ws] using hwsE_lt ed.toNat hed_lt
                        · rw [List.getElem?_set_ne (Ne.symm hke),
                            List.getElem?_set_ne (Ne.symm hk0)]
                          exact hwsE_lt k hk
                    let s_sw : FullState := { s with scratch := { s.scratch with wsort := ws_sw } }
                    have h0_sw : 0 < s_sw.scratch.wsort.length := by dsimp only [s_sw]; omega
                    cm_steps; c0_call hsift
                    refine ⟨s.scratch.q_stamp, ws_sw, CompactVmtfRest c s_sw ⋆ R,
                      Nat.zero_le _, by omega, by omega,
                      fun k hk => by have := hsw_lt k (by omega); omega,
                      focus_vmtf_arrays hm,
                      fun ws3 m3 hlen3 hout3 hmem3 hm3 => ?_⟩
                    have hed1_eq : (ed - 1#64).toNat = ed.toNat - 1 := by bv_omega
                    cm_steps
                    refine hLoopE (ed - 1#64, ()) m3 (by dsimp only; rw [hed1_eq]; omega)
                      ⟨by rw [hed1_eq]; omega, ws3, by omega, fun k hk => ?_, ?_⟩
                    · by_cases hke : k < ed.toNat
                      · obtain ⟨j, hj, heq⟩ := hmem3 k hke; rw [heq]; exact hsw_lt j (by omega)
                      · rw [hout3 k (by omega)]; exact hsw_lt k hk
                    · exact unfocus_vmtf_arrays (s := s_sw) hm3
                  · cm_steps; exact hJ2 () mE ⟨wsE, hwsE_len, hwsE_lt, hmE⟩
          · cm_steps
            exact hJ2 () m1 ⟨ws1, hws1_len, fun k hk => by
              rw [hinit1 k hk, Option.getD_some, bv32_ofNat_toNat (by omega)]; exact hk, hm1⟩

theorem full_compact_sift_h_wp (Γ : Env) :
    ∀ a m Q X, fullCompactSiftHSpec a m Q X → Func.wp Γ full_compact_sift_h_body a m Q X := by
  rintro ⟨sc_ptr, hp_ptr, ps_ptr, start, n, ⟨⟩⟩ m Q X
    ⟨sc, hp, ps, R, hsn, hn_hp, hn_ps, hn32, hsc_ok, hm, hQ⟩
  have hst_hp : start.toNat < hp.length := by omega
  let rv := hp[start.toNat]'hst_hp
  have hrv_lt : rv.toNat < sc.length := by
    have := (hsc_ok start.toNat hsn).1
    simpa [rv, List.getElem?_eq_getElem hst_hp] using this
  have hrv_ps : rv.toNat < ps.length := by
    have := (hsc_ok start.toNat hsn).2
    simpa [rv, List.getElem?_eq_getElem hst_hp] using this
  cm_steps
  refine wp_loop_inv
    (fun (root, ()) mL =>
      root.toNat < n.toNat ∧
      ∃ hpL psL : List (BitVec 32), hpL.length = hp.length ∧ psL.length = ps.length ∧
        (∀ k, n.toNat ≤ k → hpL[k]? = hp[k]?) ∧
        (∀ k < n.toNat, ∃ j < n.toNat, hpL[k]? = hp[j]?) ∧
        (array64 sc_ptr sc ⋆ array (t := i32) hp_ptr hpL ⋆ array (t := i32) ps_ptr psL ⋆ R) mL)
    (fun (root, ()) _ => n.toNat - root.toNat)
    (fun JL hLoop => ?_) ?_
  · cm_steps
    exact hLoop (start, ()) m ⟨hsn, hp, ps, rfl, rfl, fun _ _ => rfl, fun k hk => ⟨k, hk, rfl⟩, hm⟩
  · rintro JL ⟨root, ⟨⟩⟩ mL ⟨hrt_lt, hpL, psL, hlen_hp, hlen_ps, houtL, hmemL, hmL⟩ hLoop
    have hch0_eq : ((root <<< (1 : Nat)) + (1 : BitVec 64)).toNat = 2 * root.toNat + 1 := by
      have hsh : (root <<< (1 : Nat)).toNat = 2 * root.toNat := bv64_shl1_toNat (by omega)
      rw [bv64_add1 (by rw [hsh]; omega), hsh]
    have hscL : ∀ k < n.toNat,
        (hpL[k]?.getD 0#32).toNat < sc.length ∧ (hpL[k]?.getD 0#32).toNat < ps.length :=
      fun k hk => by obtain ⟨j, hj, heq⟩ := hmemL k hk; rw [heq]; exact hsc_ok j hj
    have hrv_ps64 : (rv.setWidth 64).toNat < psL.length := by
      rw [zext_toNat _ (by decide)]; omega
    cm_while_true
    cm_split
    · cm_steps
      have hrv_eq : (rv.setWidth 64).toNat = rv.toNat := zext_toNat _ (by decide)
      change (array (t := i32) ps_ptr (psL.set (rv.setWidth 64).toNat (root.setWidth 32)) ⋆
        (array (t := i32) hp_ptr (hpL.set root.toNat rv) ⋆
          (array64 sc_ptr sc ⋆ R))) m at hm
      rw [hrv_eq] at hm
      refine hQ (hpL.set root.toNat rv) (psL.set rv.toNat (root.setWidth 32)) m
        (by simp [hlen_hp]) (by simp [hlen_ps]) ?_ ?_ (by ecancel)
      · intro k hk; rw [List.getElem?_set_ne (by omega)]; exact houtL k hk
      · intro k hk
        by_cases hkr : k = root.toNat
        · subst hkr; rw [List.getElem?_set_self (by omega)]
          exact ⟨start.toNat, hsn, (List.getElem?_eq_getElem hst_hp).symm⟩
        · rw [List.getElem?_set_ne (Ne.symm hkr)]; exact hmemL k hk
    · have hch_lt : 2 * root.toNat + 1 < n.toNat := by c0_bound
      have hch_hp : 2 * root.toNat + 1 < hpL.length := by omega
      have hch_sc : (hpL[2 * root.toNat + 1]'hch_hp).toNat < sc.length := by
        simpa [List.getElem?_eq_getElem hch_hp] using (hscL (2 * root.toNat + 1) hch_lt).1
      have hch_ps : (hpL[2 * root.toNat + 1]'hch_hp).toNat < psL.length := by
        rw [hlen_ps]
        simpa [List.getElem?_eq_getElem hch_hp] using (hscL (2 * root.toNat + 1) hch_lt).2
      have hch0_hp : ((root <<< (1 : Nat)) + (1 : BitVec 64)).toNat < hpL.length := by
        rw [hch0_eq]; exact hch_hp
      have hch0_sc : (hpL[((root <<< (1 : Nat)) + (1 : BitVec 64)).toNat]'hch0_hp).toNat <
          sc.length := by simp only [hch0_eq]; exact hch_sc
      have hch0_ps : (hpL[((root <<< (1 : Nat)) + (1 : BitVec 64)).toNat]'hch0_hp).toNat <
          psL.length := by simp only [hch0_eq]; exact hch_ps
      cm_to_group
      refine wp_join_group (ts := [i64, i32, i64])
        (fun (ch, cv, _cs, ()) mJ =>
          mL = mJ ∧ ch.toNat < n.toNat ∧ root.toNat < ch.toNat ∧ ch.toNat < hpL.length ∧
          cv = hpL[ch.toNat]?.getD 0#32 ∧ (hpL[ch.toNat]?.getD 0#32).toNat < psL.length ∧
          _cs = sc[(hpL[ch.toNat]?.getD 0#32).toNat]?.getD 0#64)
        ?_ ?_
      · rintro _ ⟨ch, cv, cs, ⟨⟩⟩ mJ ⟨hm_eq, hch_n, hrt_ch, hch_len, hcv_eq, hcv_ps, _⟩
        subst mJ
        rw [List.getElem?_eq_getElem hch_len, Option.getD_some] at hcv_eq hcv_ps
        have hcv_ps64 : (cv.setWidth 64).toNat < psL.length := by
          rw [zext_toNat _ (by decide), hcv_eq]; exact hcv_ps
        have hcv64 : (cv.setWidth 64).toNat = cv.toNat := zext_toNat _ (by decide)
        have hrv_eq : (rv.setWidth 64).toNat = rv.toNat := zext_toNat _ (by decide)
        cm_steps
        · change (array (t := i32) ps_ptr (psL.set (rv.setWidth 64).toNat (root.setWidth 32)) ⋆
            (array (t := i32) hp_ptr (hpL.set root.toNat rv) ⋆
              (array64 sc_ptr sc ⋆ R))) m at hm
          rw [hrv_eq] at hm
          refine hQ (hpL.set root.toNat rv) (psL.set rv.toNat (root.setWidth 32)) m
            (by simp [hlen_hp]) (by simp [hlen_ps]) ?_ ?_ (by ecancel)
          · intro k hk; rw [List.getElem?_set_ne (by omega)]; exact houtL k hk
          · intro k hk
            by_cases hkr : k = root.toNat
            · subst hkr; rw [List.getElem?_set_self (by omega)]
              exact ⟨start.toNat, hsn, (List.getElem?_eq_getElem hst_hp).symm⟩
            · rw [List.getElem?_set_ne (Ne.symm hkr)]; exact hmemL k hk
        · rw [hcv64] at hm
          refine hLoop (ch, ()) m (by dsimp only; omega)
            ⟨hch_n, hpL.set root.toNat cv, psL.set cv.toNat (root.setWidth 32),
             by simp [hlen_hp], by simp [hlen_ps], ?_, ?_, by ecancel⟩
          · intro k hk; rw [List.getElem?_set_ne (by omega)]; exact houtL k hk
          · intro k hk
            by_cases hkr : k = root.toNat
            · subst hkr; rw [List.getElem?_set_self (by omega), hcv_eq]
              obtain ⟨j, hj, heq⟩ := hmemL ch.toNat hch_n
              exact ⟨j, hj, (List.getElem?_eq_getElem hch_len).symm.trans heq⟩
            · rw [List.getElem?_set_ne (Ne.symm hkr)]; exact hmemL k hk
      · intro Jj hJj
        have hch0_z : ((hpL[2 * root.toNat + 1]'hch_hp).setWidth 64).toNat =
            (hpL[2 * root.toNat + 1]'hch_hp).toNat := zext_toNat _ (by decide)
        cm_split
        · have hch1_eq : (((root <<< (1 : Nat)) + (1 : BitVec 64)) + (1 : BitVec 64)).toNat =
              2 * root.toNat + 2 := by
            rw [bv64_add1 (by rw [hch0_eq]; omega), hch0_eq]
          have hch1_lt : 2 * root.toNat + 2 < n.toNat := by c0_bound
          have hch1_hp : 2 * root.toNat + 2 < hpL.length := by omega
          have hch1_sc : (hpL[2 * root.toNat + 2]'hch1_hp).toNat < sc.length := by
            simpa [List.getElem?_eq_getElem hch1_hp] using (hscL (2 * root.toNat + 2) hch1_lt).1
          have hch1_ps : (hpL[2 * root.toNat + 2]'hch1_hp).toNat < psL.length := by
            rw [hlen_ps]
            simpa [List.getElem?_eq_getElem hch1_hp] using (hscL (2 * root.toNat + 2) hch1_lt).2
          have hch1_hp0 : (((root <<< (1 : Nat)) + (1 : BitVec 64)) + (1 : BitVec 64)).toNat <
              hpL.length := by rw [hch1_eq]; exact hch1_hp
          have hch1_sc0 :
              (hpL[(((root <<< (1 : Nat)) + (1 : BitVec 64)) +
                (1 : BitVec 64)).toNat]'hch1_hp0).toNat < sc.length := by
            simp only [hch1_eq]; exact hch1_sc
          have hch1_ps0 :
              (hpL[(((root <<< (1 : Nat)) + (1 : BitVec 64)) +
                (1 : BitVec 64)).toNat]'hch1_hp0).toNat < psL.length := by
            simp only [hch1_eq]; exact hch1_ps
          have hch1_z : ((hpL[2 * root.toNat + 2]'hch1_hp).setWidth 64).toNat =
              (hpL[2 * root.toNat + 2]'hch1_hp).toNat := zext_toNat _ (by decide)
          cm_steps
          · refine hJj _ mL ⟨rfl, by rw [hch1_eq]; exact hch1_lt, by omega, by omega, ?_, ?_, ?_⟩
            · simp only [hch1_eq, List.getElem?_eq_getElem hch1_hp, Option.getD_some]
            · simp only [hch1_eq, List.getElem?_eq_getElem hch1_hp, Option.getD_some]
              exact hch1_ps
            · simp only [hch1_eq, List.getElem?_eq_getElem hch1_hp, Option.getD_some,
                hch1_z, List.getElem?_eq_getElem hch1_sc]
          · refine hJj _ mL ⟨rfl, by rw [hch0_eq]; exact hch_lt, by omega, by omega, ?_, ?_, ?_⟩
            · simp only [hch0_eq, List.getElem?_eq_getElem hch_hp, Option.getD_some]
            · simp only [hch0_eq, List.getElem?_eq_getElem hch_hp, Option.getD_some]
              exact hch_ps
            · simp only [hch0_eq, List.getElem?_eq_getElem hch_hp, Option.getD_some,
                hch0_z, List.getElem?_eq_getElem hch_sc]
        · cm_steps
          refine hJj _ mL ⟨rfl, by rw [hch0_eq]; exact hch_lt, by omega, by omega, ?_, ?_, ?_⟩
          · simp only [hch0_eq, List.getElem?_eq_getElem hch_hp, Option.getD_some]
          · simp only [hch0_eq, List.getElem?_eq_getElem hch_hp, Option.getD_some]
            exact hch_ps
          · simp only [hch0_eq, List.getElem?_eq_getElem hch_hp, Option.getD_some,
              hch0_z, List.getElem?_eq_getElem hch_sc]

theorem full_compact_heap_wp (Γ : Env)
    (hsift : ∀ a m Q X, fullCompactSiftHSpec a m Q X →
      Γ "full_compact_sift_h" [i64, i64, i64, i64, i64] [] a m Q X) :
    ∀ a m Q X, fullCompactHeapSpec a m Q X → Func.wp Γ full_compact_heap_body a m Q X := by
  rintro ⟨h, ncv, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hncv_le, hm, hQ⟩
  have hmax_lt : c.max_vars < 2 * 2 ^ 28 := c.hmaxv
  have hsc_len := hlen.scratch_ok.score_len
  have hhp_len := hlen.scratch_ok.heap_len_arr
  have hps_len := hlen.scratch_ok.pos_len
  cm_steps
  refine wp_loop_inv
    (fun (v, ()) m1 =>
      v.toNat ≤ ncv.toNat ∧
      ∃ hp1 ps1 : List (BitVec 32), hp1.length = c.max_vars ∧ ps1.length = c.max_vars ∧
        (∀ k < v.toNat, (hp1[k]?.getD 0#32).toNat < ncv.toNat) ∧
        (FullMem c { s with scratch := { s.scratch with heap := hp1, pos := ps1 } } ⋆ R) m1)
    (fun (v, ()) _ => ncv.toNat - v.toNat)
    (fun J1 hLoop1 => ?_) ?_
  · cm_steps; exact hLoop1 (0#64, ()) m ⟨Nat.zero_le _, s.scratch.heap, s.scratch.pos, hhp_len,
      hps_len, fun _ hk => by simp at hk, hm⟩
  · rintro J1 ⟨v, ⟨⟩⟩ m1 ⟨hv_le, hp1, ps1, hhp1, hps1, hbd1, hm1⟩ hLoop1
    cm_split
    · have hv_lt : v.toNat < ncv.toNat := by c0_bound
      have hv1_eq : (v + (1 : BitVec 64)).toNat = v.toNat + 1 := bv64_add1 (by omega)
      cm_steps
      refine hLoop1 (v + (1 : BitVec 64), ()) m (by dsimp only; rw [hv1_eq]; omega)
        ⟨by rw [hv1_eq]; omega, hp1.set v.toNat (v.setWidth 32),
         ps1.set v.toNat (v.setWidth 32), by simp [hhp1], by simp [hps1], fun k hk => ?_,
         compactMem_cast hm rfl⟩
      rw [hv1_eq] at hk
      by_cases hkv : k = v.toNat
      · subst hkv; rw [List.getElem?_set_self (by omega), Option.getD_some,
          BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]; exact hv_lt
      · rw [List.getElem?_set_ne (Ne.symm hkv)]; exact hbd1 k (by omega)
    · have hv_eq : v.toNat = ncv.toNat := by c0_bound
      rw [hv_eq] at hbd1
      cm_steps
      cm_split
      · have hncv_gt1 : 1 < ncv.toNat := by c0_bound
        cm_steps
        refine wp_loop_inv
          (fun (st, ()) m2 =>
            st.toNat ≤ ncv.toNat ∧
            ∃ hp2 ps2 : List (BitVec 32), hp2.length = c.max_vars ∧ ps2.length = c.max_vars ∧
              (∀ k < ncv.toNat, (hp2[k]?.getD 0#32).toNat < ncv.toNat) ∧
              (FullMem c { s with scratch := { s.scratch with heap := hp2, pos := ps2,
                                                              heap_len := ncv.toNat } } ⋆ R) m2)
          (fun (st, ()) _ => st.toNat)
          (fun J2 hLoop2 => ?_) ?_
        · cm_steps
          have hst0 : (ncv >>> (1 : Nat)).toNat ≤ ncv.toNat := by
            simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; omega
          exact hLoop2 (ncv >>> (1 : Nat), ()) m ⟨hst0, hp1, ps1, hhp1, hps1, hbd1,
            compactMem_cast hm rfl⟩
        · rintro J2 ⟨st, ⟨⟩⟩ m2 ⟨hst_le, hp2, ps2, hhp2, hps2, hbd2, hm2⟩ hLoop2
          cm_split
          · have hst_pos : 0 < st.toNat := by c0_bound
            have hst1_eq : (st - (1 : BitVec 64)).toNat = st.toNat - 1 := by bv_omega
            let s2 : FullState := { s with scratch := { s.scratch with heap := hp2, pos := ps2,
                                                                       heap_len := ncv.toNat } }
            cm_steps; c0_call hsift
            refine ⟨s.scratch.score, hp2, ps2, CompactHeapRest c s2 ⋆ R,
              by rw [hst1_eq]; omega, by omega, by omega, by omega,
              fun k hk => ⟨by have := hbd2 k hk; omega, by have := hbd2 k hk; omega⟩,
              focus_heap_arrays hm2,
              fun hp3 ps3 m3 hhp3 hps3 _ hmem3 hm3 => ?_⟩
            cm_steps
            refine hLoop2 (st - (1 : BitVec 64), ()) m3 (by dsimp only; rw [hst1_eq]; omega)
              ⟨by rw [hst1_eq]; omega, hp3, ps3, by omega, by omega, fun k hk => ?_, ?_⟩
            · obtain ⟨j, hj, heq⟩ := hmem3 k hk; rw [heq]; exact hbd2 j hj
            · exact unfocus_heap_arrays (s := s2) hm3
          · cm_steps
            let sc2 : FullScratch :=
              { s.scratch with heap := hp2, pos := ps2, heap_len := ncv.toNat }
            exact hQ sc2 m2 (by
              dsimp only [sc2]
              exact ⟨hlen.core_ok, { hlen.scratch_ok with heap_len_arr := hhp2, pos_len := hps2 }⟩)
              ⟨rfl, rfl⟩ rfl rfl (by dsimp only [sc2]; exact hm2)
      · cm_steps
        let sc1 : FullScratch :=
          { s.scratch with heap := hp1, pos := ps1, heap_len := ncv.toNat }
        exact hQ sc1 m (by
          dsimp only [sc1]
          exact ⟨hlen.core_ok, { hlen.scratch_ok with heap_len_arr := hhp1, pos_len := hps1 }⟩)
          ⟨rfl, rfl⟩ rfl rfl (by dsimp only [sc1]; exact hm)

theorem full_compact_assign_map_wp (Γ : Env) :
    ∀ a m Q X, fullCompactAssignMapSpec a m Q X →
      Func.wp Γ full_compact_assign_map_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  have hcv_le := hlen.core_ok.cur_vars_le
  have hmax_lt : c.max_vars < 2 * 2 ^ 28 := c.hmaxv
  have hcv_lt : s.core.cur_vars < 0x7FFFFFFF := by unfold dimacsBound at hmax_lt; omega
  have hv_len := hlen.core_ok.vals_len
  have hws1_len := hlen.scratch_ok.work_stk1_len
  have hws2_len := hlen.scratch_ok.work_stk2_len
  cm_steps
  refine wp_loop_inv
    (fun (ncv, v, ()) mL =>
      v.toNat ≤ s.core.cur_vars ∧ ncv.toNat ≤ v.toNat ∧
      ∃ ws1 ws2 : List (BitVec 32), ws1.length = 2 * c.max_vars ∧ ws2.length = 2 * c.max_vars ∧
        (∀ u < v.toNat,
          ws1[u]? = some 0xFFFFFFFF#32 ∨
          ∃ nv < ncv.toNat, nv ≤ u ∧ s.core.vals[2 * u]?.getD 0#8 = 0#8 ∧
            ws1[u]? = some (BitVec.ofNat 32 nv) ∧ ws2[nv]? = some (BitVec.ofNat 32 u)) ∧
        (∀ nv < ncv.toNat,
          ∃ ov < v.toNat, nv ≤ ov ∧ s.core.vals[2 * ov]?.getD 0#8 = 0#8 ∧
            ws2[nv]? = some (BitVec.ofNat 32 ov) ∧ ws1[ov]? = some (BitVec.ofNat 32 nv)) ∧
        (FullMem c { s with scratch := { s.scratch with work_stk1 := ws1, work_stk2 := ws2 } } ⋆
          R) mL)
    (fun (_, v, ()) _ => s.core.cur_vars - v.toNat)
    (fun J hLoop => ?_) ?_
  · cm_steps
    exact hLoop (0#64, 0#64, ()) m ⟨Nat.zero_le _, Nat.zero_le _, s.scratch.work_stk1,
      s.scratch.work_stk2, hws1_len, hws2_len, fun _ h => by simp at h,
      fun _ h => by simp at h, hm⟩
  · rintro J ⟨ncv, v, ⟨⟩⟩ mL ⟨hv_le, hnv_le, ws1, ws2, hlen1, hlen2, hmapL, hinvL, hmL⟩ hLoop
    cm_split
    · have hv_lt : v.toNat < s.core.cur_vars := by c0_bound
      have hv1_eq : (v + (1 : BitVec 64)).toNat = v.toNat + 1 := bv64_add1 (by omega)
      have h2v_eq : (v <<< (1 : Nat)).toNat = 2 * v.toNat := bv64_shl1_toNat (by omega)
      have h2v_lt : (v <<< (1 : Nat)).toNat < s.core.vals.length := by rw [h2v_eq]; omega
      have hv_ws1 : v.toNat < ws1.length := by omega
      cm_split
      · cm_split
        · have hncv_lt : ncv.toNat < ws2.length := by omega
          have hncv1_eq : (ncv + (1 : BitVec 64)).toNat = ncv.toNat + 1 := bv64_add1 (by omega)
          have hsext : (s.core.vals[(v <<< (1 : Nat)).toNat]'h2v_lt).signExtend 32 = 0#32 := by
            c0_bound
          have hv_zero : s.core.vals[2 * v.toNat]?.getD 0#8 = 0#8 := by
            rw [List.getElem?_eq_getElem (by omega : 2 * v.toNat < s.core.vals.length),
              Option.getD_some]
            exact bv8_sext32_eq0 (by simpa [h2v_eq] using hsext)
          cm_steps
          let ws1' := ws1.set v.toNat (ncv.setWidth 32)
          let ws2' := ws2.set ncv.toNat (v.setWidth 32)
          have hncv32 : ncv.setWidth 32 = BitVec.ofNat 32 ncv.toNat := BitVec.eq_of_toNat_eq (by
            rw [BitVec.toNat_setWidth, bv32_ofNat_toNat (by omega), Nat.mod_eq_of_lt (by omega)])
          have hv32 : v.setWidth 32 = BitVec.ofNat 32 v.toNat := BitVec.eq_of_toNat_eq (by
            rw [BitVec.toNat_setWidth, bv32_ofNat_toNat (by omega), Nat.mod_eq_of_lt (by omega)])
          refine hLoop (ncv + (1 : BitVec 64), v + (1 : BitVec 64), ()) m
            (by dsimp only; rw [hv1_eq]; omega)
            ⟨by rw [hv1_eq]; omega, by rw [hv1_eq, hncv1_eq]; omega, ws1', ws2',
             by simp [ws1', hlen1], by simp [ws2', hlen2], fun u hu => ?_, fun nv hnv => ?_,
             compactMem_cast hm rfl⟩
          · rw [hv1_eq] at hu
            by_cases huv : u = v.toNat
            · subst huv; right
              refine ⟨ncv.toNat, by rw [hncv1_eq]; omega, hnv_le, hv_zero, ?_, ?_⟩
              · dsimp only [ws1']; rw [List.getElem?_set_self hv_ws1, hncv32]
              · dsimp only [ws2']; rw [List.getElem?_set_self hncv_lt, hv32]
            · rcases hmapL u (by omega) with hff | ⟨nv, h1, h2, h3, h4, h5⟩
              · exact Or.inl ((List.getElem?_set_ne (Ne.symm huv)).trans hff)
              · refine Or.inr ⟨nv, by rw [hncv1_eq]; omega, h2, h3,
                  (List.getElem?_set_ne (Ne.symm huv)).trans h4,
                  (List.getElem?_set_ne (by omega)).trans h5⟩
          · rw [hncv1_eq] at hnv
            by_cases hnk : nv = ncv.toNat
            · subst hnk
              refine ⟨v.toNat, by rw [hv1_eq]; omega, hnv_le, hv_zero, ?_, ?_⟩
              · dsimp only [ws2']; rw [List.getElem?_set_self hncv_lt, hv32]
              · dsimp only [ws1']; rw [List.getElem?_set_self hv_ws1, hncv32]
            · obtain ⟨ov, hov_lt, h1, h2, h3, h4⟩ := hinvL nv (by omega)
              refine ⟨ov, by rw [hv1_eq]; omega, h1, h2, ?_, ?_⟩
              · dsimp only [ws2']; exact (List.getElem?_set_ne (Ne.symm hnk)).trans h3
              · dsimp only [ws1']; exact (List.getElem?_set_ne (by omega)).trans h4
        · cm_steps
          let ws1' := ws1.set v.toNat 0xFFFFFFFF#32
          refine hLoop (ncv, v + (1 : BitVec 64), ()) m (by dsimp only; rw [hv1_eq]; omega)
            ⟨by rw [hv1_eq]; omega, by rw [hv1_eq]; omega, ws1', ws2,
             by simp [ws1', hlen1], hlen2, fun u hu => ?_, fun nv hnv => ?_,
             compactMem_cast hm rfl⟩
          · rw [hv1_eq] at hu
            by_cases huv : u = v.toNat
            · subst huv; exact Or.inl (List.getElem?_set_self hv_ws1)
            · rcases hmapL u (by omega) with hff | ⟨nv, h1, h2, h3, h4, h5⟩
              · exact Or.inl ((List.getElem?_set_ne (Ne.symm huv)).trans hff)
              · exact Or.inr ⟨nv, h1, h2, h3, (List.getElem?_set_ne (Ne.symm huv)).trans h4, h5⟩
          · obtain ⟨ov, hov_lt, h1, h2, h3, h4⟩ := hinvL nv hnv
            refine ⟨ov, by omega, h1, h2, h3, ?_⟩
            exact (List.getElem?_set_ne (by omega)).trans h4
      · cm_steps
        let ws1' := ws1.set v.toNat 0xFFFFFFFF#32
        refine hLoop (ncv, v + (1 : BitVec 64), ()) m (by dsimp only; rw [hv1_eq]; omega)
          ⟨by rw [hv1_eq]; omega, by rw [hv1_eq]; omega, ws1', ws2,
           by simp [ws1', hlen1], hlen2, fun u hu => ?_, fun nv hnv => ?_,
           compactMem_cast hm rfl⟩
        · rw [hv1_eq] at hu
          by_cases huv : u = v.toNat
          · subst huv; exact Or.inl (List.getElem?_set_self hv_ws1)
          · rcases hmapL u (by omega) with hff | ⟨nv, h1, h2, h3, h4, h5⟩
            · exact Or.inl ((List.getElem?_set_ne (Ne.symm huv)).trans hff)
            · exact Or.inr ⟨nv, h1, h2, h3, (List.getElem?_set_ne (Ne.symm huv)).trans h4, h5⟩
        · obtain ⟨ov, hov_lt, h1, h2, h3, h4⟩ := hinvL nv hnv
          refine ⟨ov, by omega, h1, h2, h3, ?_⟩
          exact (List.getElem?_set_ne (by omega)).trans h4
    · have hv_eq : v.toNat = s.core.cur_vars := by c0_bound
      rw [hv_eq] at hmapL hinvL hnv_le
      cm_steps
      exact hQ ncv ws1 ws2 mL ⟨hlen.core_ok, { hlen.scratch_ok with
        work_stk1_len := hlen1, work_stk2_len := hlen2 }⟩
        ⟨hcv_lt, hnv_le, hmapL, hinvL⟩ hmL

theorem full_compact_record_ext_wp (Γ : Env) :
    ∀ a m Q X, fullCompactRecordExtSpec a m Q X →
      Func.wp Γ full_compact_record_ext_body a m Q X := by
  rintro ⟨h, old_cv, ncv, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hold, hncv_le, helen, hm, hQ⟩
  have hcv_le := hlen.core_ok.cur_vars_le
  have hv_len := hlen.core_ok.vals_len
  have hws2_len := hlen.scratch_ok.work_stk2_len
  have hext_len := hlen.scratch_ok.extend_stk_len
  have hext_lt : c.extend_cap < 2 ^ 28 := c.hext
  have hmax_lt : c.max_vars < 2 * 2 ^ 28 := c.hmaxv
  have hsub_eq : (BitVec.ofNat 64 c.extend_cap - BitVec.ofNat 64 s.scratch.extend_len).toNat =
      c.extend_cap - s.scratch.extend_len := by
    rw [bv_sub_ofNat helen (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  cm_split
  · cm_steps; exact hQ s.scratch.extend_stk s.scratch.extend_len m hlen helen hm
  · let cntFix (hi : Nat) : Nat :=
      (List.range hi).countP (fun u => decide (s.core.vals[2 * u]?.getD 0#8 ≠ 0#8))
    have hcf0 : cntFix 0 = 0 := rfl
    have hcf_step : ∀ u, cntFix (u + 1) =
        cntFix u + (if s.core.vals[2 * u]?.getD 0#8 ≠ 0#8 then 1 else 0) := by
      intro u; dsimp only [cntFix]
      rw [List.range_succ, List.countP_append, List.countP_singleton]
      by_cases hne : s.core.vals[2 * u]?.getD 0#8 ≠ 0#8 <;> simp [hne]
    have hcf_mono : ∀ {a b}, a ≤ b → cntFix a ≤ cntFix b := by
      intro a b hab
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
      induction d with
      | zero => simp
      | succ d ih =>
        rw [← Nat.add_assoc, hcf_step]
        exact Nat.le_trans (ih (Nat.le_add_right _ _)) (Nat.le_add_right _ _)
    cm_steps
    refine wp_loop_inv
      (fun (nfix, v, ()) m1 =>
        v.toNat ≤ old_cv.toNat ∧ nfix.toNat ≤ v.toNat ∧ nfix.toNat = cntFix v.toNat ∧ m = m1)
      (fun (_, v, ()) _ => old_cv.toNat - v.toNat)
      (fun J1 hLoop1 => ?_) ?_
    · cm_steps; exact hLoop1 (0#64, 0#64, ()) m ⟨Nat.zero_le _, Nat.zero_le _, rfl, rfl⟩
    · rintro J1 ⟨nfix, v, ⟨⟩⟩ m1 ⟨hv_le, hnf_le, hnf_eq, rfl⟩ hLoop1
      cm_split
      · have hv_lt : v.toNat < old_cv.toNat := by c0_bound
        have hv1_eq : (v + (1 : BitVec 64)).toNat = v.toNat + 1 := bv64_add1 (by omega)
        have h2v_eq : (v <<< (1 : Nat)).toNat = 2 * v.toNat := bv64_shl1_toNat (by omega)
        have h2v_lt : (v <<< (1 : Nat)).toNat < s.core.vals.length := by rw [h2v_eq]; omega
        have hnf1_eq : (nfix + (1 : BitVec 64)).toNat = nfix.toNat + 1 := bv64_add1 (by omega)
        cm_steps
        · have hnz : s.core.vals[2 * v.toNat]?.getD 0#8 ≠ 0#8 := by
            have hsext : (s.core.vals[(v <<< (1 : Nat)).toNat]'h2v_lt).signExtend 32 ≠ 0#32 := by
              c0_bound
            rw [List.getElem?_eq_getElem (by omega : 2 * v.toNat < s.core.vals.length),
              Option.getD_some]
            intro hz; apply hsext; simp [h2v_eq, hz]
          exact hLoop1 (nfix + (1 : BitVec 64), v + (1 : BitVec 64), ()) m
            (by dsimp only; rw [hv1_eq]; omega)
            ⟨by rw [hv1_eq]; omega, by rw [hv1_eq, hnf1_eq]; omega,
             by rw [hv1_eq, hnf1_eq, hcf_step, ite_eq_left hnz, hnf_eq], rfl⟩
        · have hze : ¬ s.core.vals[2 * v.toNat]?.getD 0#8 ≠ 0#8 := by
            have hsext : (s.core.vals[(v <<< (1 : Nat)).toNat]'h2v_lt).signExtend 32 = 0#32 := by
              c0_bound
            rw [List.getElem?_eq_getElem (by omega : 2 * v.toNat < s.core.vals.length),
              Option.getD_some]
            intro hne
            exact hne (bv8_sext32_eq0 (by simpa [h2v_eq] using hsext))
          exact hLoop1 (nfix, v + (1 : BitVec 64), ()) m
            (by dsimp only; rw [hv1_eq]; omega)
            ⟨by rw [hv1_eq]; omega, by rw [hv1_eq]; omega,
             by rw [hv1_eq, hcf_step, ite_eq_right hze, hnf_eq]; omega, rfl⟩
      · have hv_eq : v.toNat = old_cv.toNat := by c0_bound
        have hnf_le_cv : nfix.toNat ≤ old_cv.toNat := hv_eq ▸ hnf_le
        have hnf_tot : nfix.toNat = cntFix old_cv.toNat := hv_eq ▸ hnf_eq
        cm_split
        · cm_steps; exact hQ s.scratch.extend_stk s.scratch.extend_len m hlen helen hm
        · have hneed_le : nfix.toNat + ncv.toNat + 1 ≤ c.extend_cap - s.scratch.extend_len := by
            have hcmp :
                (nfix + ncv + (1 : BitVec 64)).toNat ≤
                  (BitVec.ofNat 64 c.extend_cap - BitVec.ofNat 64 s.scratch.extend_len).toNat := by
              c0_bound
            rw [hsub_eq] at hcmp
            have hsum : (nfix + ncv + (1 : BitVec 64)).toNat = nfix.toNat + ncv.toNat + 1 := by
              rw [BitVec.toNat_add, BitVec.toNat_add, show (1 : BitVec 64).toNat = 1 from rfl,
                Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
            omega
          cm_steps
          refine wp_loop_inv
            (fun (v2, p, ()) m2 =>
              v2.toNat ≤ old_cv.toNat ∧ p.toNat = s.scratch.extend_len + cntFix v2.toNat ∧
              ∃ ext2 : List (BitVec 32), ext2.length = c.extend_cap ∧
                (FullMem c { s with scratch := { s.scratch with extend_stk := ext2 } } ⋆ R) m2)
            (fun (v2, _, ()) _ => old_cv.toNat - v2.toNat)
            (fun J2 hLoop2 => ?_) ?_
          · have helen_64 : s.scratch.extend_len < 2 ^ 64 := by omega
            cm_steps; exact hLoop2 (0#64, BitVec.ofNat 64 s.scratch.extend_len, ()) m
              ⟨Nat.zero_le _, by dsimp only [cntFix]; simp [Nat.mod_eq_of_lt helen_64],
               s.scratch.extend_stk, hext_len, hm⟩
          · rintro J2 ⟨v2, p, ⟨⟩⟩ m2 ⟨hv2_le, hp_eq, ext2, hext2, hm2⟩ hLoop2
            cm_split
            · have hv2_lt : v2.toNat < old_cv.toNat := by c0_bound
              have hv2_1_eq : (v2 + (1 : BitVec 64)).toNat = v2.toNat + 1 := bv64_add1 (by omega)
              have h2v2_eq : (v2 <<< (1 : Nat)).toNat = 2 * v2.toNat := bv64_shl1_toNat (by omega)
              have h2v2_lt : (v2 <<< (1 : Nat)).toNat < s.core.vals.length := by rw [h2v2_eq]; omega
              cm_split
              · have hnz2 : s.core.vals[2 * v2.toNat]?.getD 0#8 ≠ 0#8 := by
                  have hsext : (s.core.vals[(v2 <<< (1 : Nat)).toNat]'h2v2_lt).signExtend 32 ≠
                      0#32 := by c0_bound
                  rw [List.getElem?_eq_getElem (by omega : 2 * v2.toNat < s.core.vals.length),
                    Option.getD_some]
                  intro hz; apply hsext; simp [h2v2_eq, hz]
                have hcf_lt : cntFix v2.toNat + 1 ≤ nfix.toNat := by
                  have h1 := hcf_step v2.toNat; rw [ite_eq_left hnz2] at h1
                  have h2 := hcf_mono (show v2.toNat + 1 ≤ old_cv.toNat by omega)
                  omega
                have hp_lt : p.toNat < ext2.length := by omega
                have hp1_eq : (p + (1 : BitVec 64)).toNat = p.toNat + 1 := bv64_add1 (by omega)
                cm_steps <;>
                refine hLoop2 (v2 + (1 : BitVec 64), p + (1 : BitVec 64), ()) m
                  (by dsimp only; rw [hv2_1_eq]; omega)
                  ⟨by rw [hv2_1_eq]; omega,
                   by rw [hp1_eq, hv2_1_eq, hcf_step, ite_eq_left hnz2, hp_eq]; omega,
                   _, ?_, hm⟩ <;>
                simp [hext2]
              · have hze2 : ¬ s.core.vals[2 * v2.toNat]?.getD 0#8 ≠ 0#8 := by
                  have hsext : (s.core.vals[(v2 <<< (1 : Nat)).toNat]'h2v2_lt).signExtend 32 =
                      0#32 := by c0_bound
                  rw [List.getElem?_eq_getElem (by omega : 2 * v2.toNat < s.core.vals.length),
                    Option.getD_some]
                  intro hne
                  exact hne (bv8_sext32_eq0 (by simpa [h2v2_eq] using hsext))
                cm_steps
                try (apply (‹∀ (xs : Tup Val [i64]) (m' : Mem 64),
                  wp _ _ _ _ m' → _›); cm_steps)
                exact hLoop2 (v2 + (1 : BitVec 64), p, ()) m2
                  (by dsimp only; rw [hv2_1_eq]; omega)
                  ⟨by rw [hv2_1_eq]; omega,
                   by rw [hv2_1_eq, hcf_step, ite_eq_right hze2, hp_eq]; omega,
                   ext2, hext2, hm2⟩
            · have hv2_eq : v2.toNat = old_cv.toNat := by c0_bound
              have hp_eq_tot : p.toNat = s.scratch.extend_len + nfix.toNat := by
                rw [hp_eq, hv2_eq, hnf_tot]
              have hp_lt_tag : p.toNat < ext2.length := by omega
              have hp1_eq : (p + (1 : BitVec 64)).toNat = p.toNat + 1 := bv64_add1 (by omega)
              cm_steps
              refine wp_loop_inv
                (fun (p3, nv, ()) m3 =>
                  nv.toNat ≤ ncv.toNat ∧ p3.toNat ≤ p.toNat + 1 + nv.toNat ∧
                  ∃ ext3 : List (BitVec 32), ext3.length = c.extend_cap ∧
                    (FullMem c { s with scratch := { s.scratch with extend_stk := ext3 } } ⋆
                      R) m3)
                (fun (_, nv, ()) _ => ncv.toNat - nv.toNat)
                (fun J3 hLoop3 => ?_) ?_
              · cm_steps
                refine hLoop3 (p + (1 : BitVec 64), 0#64, ()) m
                  ⟨Nat.zero_le _, by rw [hp1_eq]; omega, _, ?_, hm⟩
                simp [hext2]
              · rintro J3 ⟨p3, nv, ⟨⟩⟩ m3 ⟨hnv_le3, hp3_le, ext3, hext3, hm3⟩ hLoop3
                cm_split
                · have hnv_lt : nv.toNat < ncv.toNat := by c0_bound
                  have hnv_ws2 : nv.toNat < s.scratch.work_stk2.length := by omega
                  have hp3_lt : p3.toNat < ext3.length := by omega
                  have hnv1_eq : (nv + (1 : BitVec 64)).toNat = nv.toNat + 1 := bv64_add1 (by omega)
                  have hp3_1_eq : (p3 + (1 : BitVec 64)).toNat = p3.toNat + 1 :=
                    bv64_add1 (by omega)
                  cm_steps
                  refine hLoop3 (p3 + (1 : BitVec 64), nv + (1 : BitVec 64), ()) m
                    (by dsimp only; rw [hnv1_eq]; omega)
                    ⟨by rw [hnv1_eq]; omega, by rw [hp3_1_eq, hnv1_eq]; omega, _, ?_, hm⟩
                  simp [hext3]
                · have hnv_eq : nv.toNat = ncv.toNat := by c0_bound
                  have hp3_le_cap : p3.toNat ≤ c.extend_cap := by omega
                  cm_steps
                  let sc3 : FullScratch :=
                    { s.scratch with extend_stk := ext3, extend_len := p3.toNat }
                  exact hQ ext3 p3.toNat m
                    (by dsimp only [sc3]; exact ⟨hlen.core_ok, { hlen.scratch_ok with
                      extend_stk_len := hext3 }⟩)
                    hp3_le_cap (by dsimp only [sc3]; exact hm)

theorem full_compact_vars_wp (Γ : Env) :
    ∀ a m Q X, fullCompactVarsSpec a m Q X → Func.wp Γ full_compact_vars_body a m Q X := by
  rintro ⟨h, old_cv, ncv, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hold, hncv_le, hinv_ok, hm, hQ⟩
  have hmax_lt : c.max_vars < 2 * 2 ^ 28 := c.hmaxv
  have hcv_le := hlen.core_ok.cur_vars_le
  have hcv2_lt64 : 2 * old_cv.toNat < 2 ^ 64 := by unfold dimacsBound at hmax_lt; omega
  have hcv2_pow : 2 * old_cv.toNat < 18446744073709551616 := hcv2_lt64
  have hcv_lt64 : old_cv.toNat < 2 ^ 64 := by omega
  have hncv_lt64 : ncv.toNat < 2 ^ 64 := by omega
  have hv_len := hlen.core_ok.vals_len
  have hfl_len := hlen.core_ok.flags_len
  have hlv_len := hlen.core_ok.lvl_len
  have hrs_len := hlen.core_ok.rsns_len
  have hft_len := hlen.core_ok.frame_trail_len
  have hfd_len := hlen.core_ok.frame_dec_len
  have hph_len := hlen.scratch_ok.phases_len
  have hpt_len := hlen.scratch_ok.phases_target_len
  have hpb_len := hlen.scratch_ok.phases_best_len
  have hwb_len := hlen.scratch_ok.walk_best_len
  have hsc_len := hlen.scratch_ok.score_len
  have hqs_len := hlen.scratch_ok.q_stamp_len
  have hqp_len := hlen.scratch_ok.q_prev_len
  have hqn_len := hlen.scratch_ok.q_next_len
  have hps_len := hlen.scratch_ok.pos_len
  have hws2_len := hlen.scratch_ok.work_stk2_len
  have hnlits_eq : (old_cv <<< (1 : Nat)).toNat = 2 * old_cv.toNat := bv64_shl1_toNat (by omega)
  cm_steps
  refine wp_loop_inv
    (fun (l, ()) m1 =>
      l.toNat ≤ 2 * old_cv.toNat ∧
      ∃ vals1 : List (BitVec 8), vals1.length = 2 * c.max_vars ∧
        (∀ i < l.toNat, vals1[i]? = some 0#8) ∧
        (FullMem c { s with core := { s.core with vals := vals1 } } ⋆ R) m1)
    (fun (l, ()) _ => 2 * old_cv.toNat - l.toNat)
    (fun J1 hLoop1 => ?_) ?_
  · cm_steps; exact hLoop1 (0#64, ()) m ⟨Nat.zero_le _, s.core.vals, hv_len,
      fun _ h => by simp at h, hm⟩
  · rintro J1 ⟨l, ⟨⟩⟩ m1 ⟨hl_le, vals1, hvl1, hz1, hm1⟩ hLoop1
    cm_split
    · have hl_lt : l.toNat < 2 * old_cv.toNat := by
        have h1 := hc
        simp only [bv_c0, Nat.reducePow] at h1
        rwa [Nat.mod_eq_of_lt hcv2_pow] at h1
      have hl1_eq : (l + (1 : BitVec 64)).toNat = l.toNat + 1 :=
        bv64_add1 (Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hl_lt) hcv2_lt64)
      have hvals_eq :
          ({ s with core := { s.core with vals := vals1 } } : FullState).core.vals = vals1 := rfl
      have hl_vals :
          l.toNat < ({ s with core := { s.core with vals := vals1 } } :
            FullState).core.vals.length :=
        hvals_eq ▸ hvl1 ▸ Nat.lt_of_lt_of_le hl_lt (Nat.mul_le_mul_left 2 (hold ▸ hcv_le))
      cm_steps
      refine hLoop1 (l + (1 : BitVec 64), ()) m
        (by dsimp only; rw [hl1_eq]; exact Nat.sub_lt_sub_left hl_lt (Nat.lt_succ_self _))
        ⟨by rw [hl1_eq]; exact Nat.succ_le_of_lt hl_lt, vals1.set l.toNat 0#8,
         by rw [List.length_set, hvl1], fun i hi => ?_, hm⟩
      rw [hl1_eq] at hi
      by_cases hil : i = l.toNat
      · subst hil
        exact List.getElem?_set_self (hvl1 ▸ Nat.lt_of_lt_of_le hl_lt
          (Nat.mul_le_mul_left 2 (hold ▸ hcv_le)))
      · rw [List.getElem?_set_ne (Ne.symm hil)]
        exact hz1 i (Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hi) hil)
    · have hl_eq : l.toNat = 2 * old_cv.toNat := by
        have h2 := hc
        simp only [bv_c0, Nat.reducePow] at h2
        rw [Nat.mod_eq_of_lt hcv2_pow] at h2
        exact Nat.le_antisymm hl_le (Nat.le_of_not_lt h2)
      rw [hl_eq] at hz1
      clear hLoop1 J1
      cm_steps
      refine wp_loop_inv
        (fun (nv, ()) m2 =>
          nv.toNat ≤ ncv.toNat ∧
          ∃ fl2 lvl2 rsns2 : List (BitVec 32),
            fl2.length = c.max_vars ∧ lvl2.length = c.max_vars ∧ rsns2.length = c.max_vars ∧
            ∃ ph2 pt2 pb2 wb2 : List (BitVec 8),
              ph2.length = c.max_vars ∧ pt2.length = c.max_vars ∧
              pb2.length = c.max_vars ∧ wb2.length = c.max_vars ∧
              ∃ sc2 : List (BitVec 64), sc2.length = c.max_vars ∧
                ∃ qs2 : List (BitVec 32), qs2.length = c.max_vars ∧
                  (FullMem c {
                    core := { s.core with vals := vals1, flags := fl2, lvl := lvl2, rsns := rsns2 }
                    scratch := { s.scratch with phases := ph2, phases_target := pt2,
                                                  phases_best := pb2, walk_best := wb2,
                                                  score := sc2, q_stamp := qs2 } } ⋆ R) m2)
        (fun (nv, ()) _ => ncv.toNat - nv.toNat)
        (fun J2 hLoop2 => ?_) ?_
      · cm_steps
        exact hLoop2 (0#64, ()) m1 ⟨Nat.zero_le _, s.core.flags, s.core.lvl, s.core.rsns,
          hfl_len, hlv_len, hrs_len, s.scratch.phases, s.scratch.phases_target,
          s.scratch.phases_best, s.scratch.walk_best, hph_len, hpt_len, hpb_len, hwb_len,
          s.scratch.score, hsc_len, s.scratch.q_stamp, hqs_len, hm1⟩
      · clear hm1
        rintro J2 ⟨nv, ⟨⟩⟩ m2 ⟨hnv_le2, fl2, lvl2, rsns2, hfl2, hlv2, hrs2,
            ph2, pt2, pb2, wb2, hph2, hpt2, hpb2, hwb2, sc2, hsc2, qs2, hqs2, hm2⟩ hLoop2
        cm_split
        · have hnv_lt : nv.toNat < ncv.toNat := hc
          have hnv_cm : nv.toNat < c.max_vars :=
            Nat.lt_of_lt_of_le hnv_lt (Nat.le_trans hncv_le (hold ▸ hcv_le))
          have hnv_ws2 : nv.toNat < s.scratch.work_stk2.length := hws2_len ▸
            Nat.lt_of_lt_of_le hnv_cm (Nat.le_mul_of_pos_left _ Nat.zero_lt_two)
          have hov_lt : (s.scratch.work_stk2[nv.toNat]'hnv_ws2).toNat < old_cv.toNat := by
            simpa [List.getElem?_eq_getElem hnv_ws2] using hinv_ok nv.toNat hnv_lt
          have hov64_lt : ((s.scratch.work_stk2[nv.toNat]'hnv_ws2).setWidth 64).toNat <
              old_cv.toNat := by rw [zext_toNat _ (by decide)]; exact hov_lt
          have hov_cm : ((s.scratch.work_stk2[nv.toNat]'hnv_ws2).setWidth 64).toNat <
              c.max_vars := Nat.lt_of_lt_of_le hov64_lt (hold ▸ hcv_le)
          have hnv_fl2 : nv.toNat < fl2.length := hfl2 ▸ hnv_cm
          have hov_fl2 : ((s.scratch.work_stk2[nv.toNat]'hnv_ws2).setWidth 64).toNat <
              fl2.length := hfl2 ▸ hov_cm
          have hnv_ph2 : nv.toNat < ph2.length := hph2 ▸ hnv_cm
          have hov_ph2 : ((s.scratch.work_stk2[nv.toNat]'hnv_ws2).setWidth 64).toNat <
              ph2.length := hph2 ▸ hov_cm
          have hnv_pt2 : nv.toNat < pt2.length := hpt2 ▸ hnv_cm
          have hov_pt2 : ((s.scratch.work_stk2[nv.toNat]'hnv_ws2).setWidth 64).toNat <
              pt2.length := hpt2 ▸ hov_cm
          have hnv_pb2 : nv.toNat < pb2.length := hpb2 ▸ hnv_cm
          have hov_pb2 : ((s.scratch.work_stk2[nv.toNat]'hnv_ws2).setWidth 64).toNat <
              pb2.length := hpb2 ▸ hov_cm
          have hnv_wb2 : nv.toNat < wb2.length := hwb2 ▸ hnv_cm
          have hov_wb2 : ((s.scratch.work_stk2[nv.toNat]'hnv_ws2).setWidth 64).toNat <
              wb2.length := hwb2 ▸ hov_cm
          have hnv_sc2 : nv.toNat < sc2.length := hsc2 ▸ hnv_cm
          have hov_sc2 : ((s.scratch.work_stk2[nv.toNat]'hnv_ws2).setWidth 64).toNat <
              sc2.length := hsc2 ▸ hov_cm
          have hnv_qs2 : nv.toNat < qs2.length := hqs2 ▸ hnv_cm
          have hov_qs2 : ((s.scratch.work_stk2[nv.toNat]'hnv_ws2).setWidth 64).toNat <
              qs2.length := hqs2 ▸ hov_cm
          have hnv_lv2 : nv.toNat < lvl2.length := hlv2 ▸ hnv_cm
          have hnv_rs2 : nv.toNat < rsns2.length := hrs2 ▸ hnv_cm
          have hnv1_eq : (nv + (1 : BitVec 64)).toNat = nv.toNat + 1 :=
            bv64_add1 (Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hnv_lt) hncv_lt64)
          cm_steps
          refine hLoop2 (nv + (1 : BitVec 64), ()) m
            (by dsimp only; rw [hnv1_eq]; exact Nat.sub_lt_sub_left hnv_lt (Nat.lt_succ_self _))
            ⟨by rw [hnv1_eq]; exact Nat.succ_le_of_lt hnv_lt, _, _, _, ?_, ?_, ?_, _, _, _, _,
             ?_, ?_, ?_, ?_, _, ?_, _, ?_, hm⟩
          · rw [List.length_set]; exact hfl2
          · rw [List.length_set]; exact hlv2
          · rw [List.length_set]; exact hrs2
          · rw [List.length_set]; exact hph2
          · rw [List.length_set]; exact hpt2
          · rw [List.length_set]; exact hpb2
          · rw [List.length_set]; exact hwb2
          · rw [List.length_set]; exact hsc2
          · rw [List.length_set]; exact hqs2
        · clear hLoop2 J2 hinv_ok hws2_len hncv_lt64
          cm_steps
          refine wp_loop_inv
            (fun (v, ()) m3 =>
              v.toNat ≤ old_cv.toNat ∧
              ∃ fl3 lvl3 rsns3 qp3 qn3 qs3 ps3 : List (BitVec 32),
                fl3.length = c.max_vars ∧ lvl3.length = c.max_vars ∧ rsns3.length = c.max_vars ∧
                qp3.length = c.max_vars ∧ qn3.length = c.max_vars ∧ qs3.length = c.max_vars ∧
                ps3.length = c.max_vars ∧
                ∃ sc3 : List (BitVec 64), sc3.length = c.max_vars ∧
                  (FullMem c {
                    core := { s.core with vals := vals1, flags := fl3, lvl := lvl3, rsns := rsns3 }
                    scratch := { s.scratch with phases := ph2, phases_target := pt2,
                                                  phases_best := pb2, walk_best := wb2,
                                                  score := sc3, q_stamp := qs3, q_prev := qp3,
                                                  q_next := qn3, pos := ps3 } } ⋆ R) m3)
            (fun (v, ()) _ => old_cv.toNat - v.toNat)
            (fun J3 hLoop3 => ?_) ?_
          · cm_steps
            exact hLoop3 (ncv, ()) m2 ⟨hncv_le, fl2, lvl2, rsns2, s.scratch.q_prev,
              s.scratch.q_next, qs2, s.scratch.pos, hfl2, hlv2, hrs2, hqp_len, hqn_len,
              hqs2, hps_len, sc2, hsc2, hm2⟩
          · clear hm2
            rintro J3 ⟨v, ⟨⟩⟩ m3 ⟨hv_le3, fl3, lvl3, rsns3, qp3, qn3, qs3, ps3,
                hfl3, hlv3, hrs3, hqp3, hqn3, hqs3, hps3, sc3, hsc3, hm3⟩ hLoop3
            cm_split
            · have hv_lt : v.toNat < old_cv.toNat := hc
              have hv_cm : v.toNat < c.max_vars := Nat.lt_of_lt_of_le hv_lt (hold ▸ hcv_le)
              have hv_fl3 : v.toNat < fl3.length := hfl3 ▸ hv_cm
              have hv_lv3 : v.toNat < lvl3.length := hlv3 ▸ hv_cm
              have hv_rs3 : v.toNat < rsns3.length := hrs3 ▸ hv_cm
              have hv_sc3 : v.toNat < sc3.length := hsc3 ▸ hv_cm
              have hv_qs3 : v.toNat < qs3.length := hqs3 ▸ hv_cm
              have hv_qp3 : v.toNat < qp3.length := hqp3 ▸ hv_cm
              have hv_qn3 : v.toNat < qn3.length := hqn3 ▸ hv_cm
              have hv_ps3 : v.toNat < ps3.length := hps3 ▸ hv_cm
              have hv1_eq : (v + (1 : BitVec 64)).toNat = v.toNat + 1 :=
                bv64_add1 (Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hv_lt) hcv_lt64)
              cm_steps
              refine hLoop3 (v + (1 : BitVec 64), ()) m
                (by dsimp only; rw [hv1_eq]; exact Nat.sub_lt_sub_left hv_lt (Nat.lt_succ_self _))
                ⟨by rw [hv1_eq]; exact Nat.succ_le_of_lt hv_lt, _, _, _, _, _, _, _,
                 ?_, ?_, ?_, ?_, ?_, ?_, ?_, _, ?_, hm⟩
              · rw [List.length_set]; exact hfl3
              · rw [List.length_set]; exact hlv3
              · rw [List.length_set]; exact hrs3
              · rw [List.length_set]; exact hqp3
              · rw [List.length_set]; exact hqn3
              · rw [List.length_set]; exact hqs3
              · rw [List.length_set]; exact hps3
              · rw [List.length_set]; exact hsc3
            · have hft0 : 0 < s.core.frame_trail.length := by
                rw [hft_len]; exact Nat.zero_lt_succ _
              have hfd0 : 0 < s.core.frame_dec.length := by
                rw [hfd_len]; exact Nat.zero_lt_succ _
              clear hLoop3 J3 hfl_len hlv_len hrs_len hph_len hpt_len hpb_len hwb_len hsc_len
                hqs_len hqp_len hqn_len hps_len hmax_lt hcv2_lt64 hcv2_pow hcv_lt64 hv_len
              have hc_mv_lt : c.mv < 2 ^ 64 :=
                Nat.lt_trans c.hmv (by unfold dimacsBound; decide)
              have hmax_lt64 : c.max_vars < 2 ^ 64 :=
                Nat.lt_trans c.hmaxv (by unfold dimacsBound; decide)
              have hmv_lt_max : ncv.toNat ≤ c.max_vars :=
                Nat.le_trans hncv_le (hold ▸ hcv_le)
              have hncv_bv : ncv = BitVec.ofNat 64 ncv.toNat :=
                (@bv_ofNat_toNat_eq 64 ncv).symm
              have hsub_bv : BitVec.ofNat 64 c.max_vars - ncv =
                  BitVec.ofNat 64 (c.max_vars - ncv.toNat) :=
                (congrArg (BitVec.ofNat 64 c.max_vars - ·) hncv_bv).trans
                  (bv_sub_ofNat hmv_lt_max hmax_lt64)
              let sc_final : FullScratch :=
                { s.scratch with
                  phases := ph2, phases_target := pt2, phases_best := pb2, walk_best := wb2,
                  score := sc3, q_stamp := qs3, q_prev := qp3, q_next := qn3, pos := ps3,
                  target_assigned := 0#64, best_assigned := 0#64 }
              let s_final : FullState :=
                { core := { s.core with
                    vals := vals1, flags := fl3, lvl := lvl3, rsns := rsns3,
                    frame_trail := s.core.frame_trail.set 0 0#32,
                    frame_dec := s.core.frame_dec.set 0 0xFFFFFFFF#32,
                    trail_end := 0, propagated := 0, cur_level := 0,
                    unflushed := 0#64, confl_ref := 0xFFFFFFFF#64, confl_type := 0#64,
                    cur_vars := ncv.toNat, unassigned := ncv }
                  scratch := sc_final }
              cm_to_group
              refine wp_join_group
                (fun () mJ =>
                  ∃ c' : FullCfg, FullCfgCompat c c' ∧ c'.mv ≤ ncv.toNat ∧
                    (FullMem c' s_final ⋆ R) mJ)
                ?_ ?_
              · rintro _ ⟨⟩ mJ ⟨c', hcompat', hcv_ge', hmJ⟩
                cm_steps
                refine hQ c' vals1 fl3 lvl3 rsns3 0#32 0xFFFFFFFF#32 sc_final mJ hcompat'
                  ?_ rfl (fun l _ hl => hz1 l hl) ⟨rfl, rfl⟩ rfl rfl hmJ
                obtain ⟨_, _, _, hmax, _, har, hwc, hdel, hred, hext, hscr⟩ := hcompat'
                exact ⟨⟨hmax ▸ hvl1, hmax ▸ hlen.core_ok.lit_mark_len,
                    hmax ▸ hlen.core_ok.mrk_len, hmax ▸ hfl3, hmax ▸ hlv3, hmax ▸ hrs3,
                    hmax ▸ hlen.core_ok.trl_len, hmax ▸ hlen.core_ok.trail_pos_len,
                    hmax ▸ hlen.core_ok.tmp_len_arr, hmax ▸ hlen.core_ok.min_clr_len_arr,
                    hmax ▸ (by rw [List.length_set]; exact hft_len),
                    hmax ▸ (by rw [List.length_set]; exact hfd_len),
                    hmax ▸ hlen.core_ok.wvec_len, hmax ▸ hlen.core_ok.repr_len,
                    (by simp only [FullCfg.minDepth, hmax]; exact hlen.core_ok.min_stk_len),
                    har ▸ hlen.core_ok.arena_len_arr,
                    hwc ▸ hlen.core_ok.wstk_len_arr, hcv_ge', hmax ▸ hmv_lt_max,
                    har ▸ hlen.core_ok.arena_len_le, hwc ▸ hlen.core_ok.wlen_le,
                    Nat.zero_le _, Nat.zero_le _, hmax ▸ hlen.core_ok.tmp_len_le,
                    hmax ▸ hlen.core_ok.min_clr_len_le⟩,
                  ⟨hmax ▸ hlen.scratch_ok.walk_vals_len, hmax ▸ hph2, hmax ▸ hpt2,
                    hmax ▸ hpb2, hmax ▸ hwb2, hmax ▸ hlen.scratch_ok.heap_len_arr,
                    hmax ▸ hps3, hmax ▸ hlen.scratch_ok.shrink_stk_len, hmax ▸ hqp3,
                    hmax ▸ hqn3, hmax ▸ hqs3, hmax ▸ hlen.scratch_ok.wsort_len,
                    hmax ▸ hlen.scratch_ok.work_stk1_len, hmax ▸ hlen.scratch_ok.work_stk2_len,
                    hmax ▸ hlen.scratch_ok.tarjan_mark_len,
                    hmax ▸ hlen.scratch_ok.tarjan_reach_len, hmax ▸ hsc3,
                    hmax ▸ hlen.scratch_ok.sim_sig_len, hlen.scratch_ok.glue_used_len,
                    hlen.scratch_ok.last_learned_len, hdel ▸ hlen.scratch_ok.delayed_len_arr,
                    hred ▸ hlen.scratch_ok.red_refs_len, hext ▸ hlen.scratch_ok.extend_stk_len,
                    hscr ▸ hlen.scratch_ok.scratch_buf_len⟩⟩
              · intro Jmv hJmv
                cm_split
                · have hlt_mv : ncv.toNat < c.mv := by
                    have h1 := hc
                    simp only [bv_c0, Nat.mod_eq_of_lt hc_mv_lt] at h1
                    exact h1
                  let c' := fullCfgShrinkMv c ncv.toNat (Nat.le_of_lt hlt_mv)
                  try c0_let_simp
                  refine LeanQbe.T.wp_store_sep (full_store_mv_mid ncv hm) ?_
                  intro m4 hm4
                  c0_let_simp
                  refine LeanQbe.T.wp_load_of (full_load_max_vars_mid hm4) ?_
                  c0_let_simp
                  have hm4' :
                      (FullMemShrinkMid c (BitVec.ofNat 64 ncv.toNat) _ ⋆ R) m4 :=
                    (show ∀ {x : BitVec 64},
                        ncv = x → (FullMemShrinkMid c x _ ⋆ R) m4 from fun h => h ▸ hm4)
                      hncv_bv
                  refine LeanQbe.T.wp_store_sep (by
                    rw [hsub_bv]
                    exact full_store_bva_mid (Nat.le_of_lt hlt_mv) hm4') ?_
                  intro m5 hm5
                  cm_steps
                  exact hJmv () m5 ⟨c', FullCfgCompat.shrinkMv c ncv.toNat (Nat.le_of_lt hlt_mv),
                    Nat.le_refl _, compactMem_cast hm5 (by
                      dsimp only [s_final, sc_final]; simp only [← hncv_bv]; rfl)⟩
                · have hge_mv : c.mv ≤ ncv.toNat := by
                    have h1 := hc
                    simp only [bv_c0, Nat.mod_eq_of_lt hc_mv_lt] at h1
                    omega
                  cm_steps
                  exact hJmv () m ⟨c, FullCfgCompat.refl c, hge_mv,
                    compactMem_cast hm (by dsimp only [s_final, sc_final]; rfl)⟩

theorem full_compact_mark_live_wp (Γ : Env)
    (hnext : ∀ a m Q X, fullArenaNextSpec a m Q X →
      Γ "full_arena_next" [i64, i32] [i32] a m Q X) :
    ∀ a m Q X, fullCompactMarkLiveSpec a m Q X →
      Func.wp Γ full_compact_mark_live_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hsp, hm, hQ⟩
  have hlen := hsp.1
  have hw := hsp.2.1
  have hdm := hsp.2.2.2.2.2
  have hwat : WatchesInv F_cur s.core := by
    have hm' := hw.watches; unfold ModeWatchesInv at hm'; rwa [ite_eq_left hdm] at hm'
  have hcv_le := hlen.core_ok.cur_vars_le
  have hal_le := hlen.core_ok.arena_len_le
  have har_len := hlen.core_ok.arena_len_arr
  have hwl_le := hlen.core_ok.wlen_le
  have hws_len := hlen.core_ok.wstk_len_arr
  have hwv_len := hlen.core_ok.wvec_len
  have hv_len := hlen.core_ok.vals_len
  have hfl_len := hlen.core_ok.flags_len
  have hws1_len := hlen.scratch_ok.work_stk1_len
  have hmax_lt : c.max_vars < 2 * 2 ^ 28 := c.hmaxv
  have hcv_64 : (BitVec.ofNat 64 s.core.cur_vars).toNat = s.core.cur_vars := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hnlits_eq : ((BitVec.ofNat 64 s.core.cur_vars) <<< (1 : Nat)).toNat =
      2 * s.core.cur_vars := by
    rw [bv64_shl1_toNat (by rw [hcv_64]; omega), hcv_64]
  cm_steps
  refine wp_loop_inv
    (fun (v, ()) m1 =>
      v.toNat ≤ s.core.cur_vars ∧
      ∃ ws1 : List (BitVec 32), ws1.length = 2 * c.max_vars ∧
        (FullMem c { s with scratch := { s.scratch with work_stk1 := ws1 } } ⋆ R) m1)
    (fun (v, ()) _ => s.core.cur_vars - v.toNat)
    (fun J1 hLoop1 => ?_) ?_
  · cm_steps; exact hLoop1 (0#64, ()) m ⟨Nat.zero_le _, s.scratch.work_stk1, hws1_len, hm⟩
  · rintro J1 ⟨v, ⟨⟩⟩ m1 ⟨hv_le, ws1, hlen1, hm1⟩ hLoop1
    cm_jnz
    · have hv_lt : v.toNat < s.core.cur_vars := by c0_bound
      have hv1_eq : (v + (1 : BitVec 64)).toNat = v.toNat + 1 := bv64_add1 (by omega)
      have h2v_eq : (v <<< (1 : Nat)).toNat = 2 * v.toNat := bv64_shl1_toNat (by omega)
      have h2v_lt : (v <<< (1 : Nat)).toNat < s.core.vals.length := by rw [h2v_eq]; omega
      cm_steps
      · exact hLoop1 (v + (1 : BitVec 64), ()) m (by dsimp only; rw [hv1_eq]; omega)
          ⟨by rw [hv1_eq]; omega, ws1.set v.toNat 1#32, by simp [hlen1], compactMem_cast hm rfl⟩
      · exact hLoop1 (v + (1 : BitVec 64), ()) m (by dsimp only; rw [hv1_eq]; omega)
          ⟨by rw [hv1_eq]; omega, ws1.set v.toNat 0#32, by simp [hlen1], compactMem_cast hm rfl⟩
      · exact hLoop1 (v + (1 : BitVec 64), ()) m (by dsimp only; rw [hv1_eq]; omega)
          ⟨by rw [hv1_eq]; omega, ws1.set v.toNat 0#32, by simp [hlen1], compactMem_cast hm rfl⟩
    · clear hLoop1 J1
      cm_steps
      refine wp_loop_inv
        (fun (l, ()) m2 =>
          l.toNat ≤ 2 * s.core.cur_vars ∧
          ∃ ws2 : List (BitVec 32), ws2.length = 2 * c.max_vars ∧
            (FullMem c { s with scratch := { s.scratch with work_stk1 := ws2 } } ⋆ R) m2)
        (fun (l, ()) _ => 2 * s.core.cur_vars - l.toNat)
        (fun J2 hLoop2 => ?_) ?_
      · cm_steps; exact hLoop2 (0#64, ()) m1 ⟨Nat.zero_le _, ws1, hlen1, hm1⟩
      · rintro J2 ⟨l, ⟨⟩⟩ m2 ⟨hl_le, ws2, hlen2, hm2⟩ hLoop2
        cm_jnz
        · have hl_lt : l.toNat < 2 * s.core.cur_vars := by c0_bound
          have hl1_eq : (l + (1 : BitVec 64)).toNat = l.toNat + 1 := bv64_add1 (by omega)
          have h2l_eq : (l <<< (1 : Nat)).toNat = 2 * l.toNat := bv64_shl1_toNat (by omega)
          have h2l1_eq : ((l <<< (1 : Nat)) + (1 : BitVec 64)).toNat = 2 * l.toNat + 1 := by
            rw [bv64_add1 (by rw [h2l_eq]; omega), h2l_eq]
          have h2l_lt : 2 * l.toNat < s.core.wvec.length := by omega
          have h2l1_lt : 2 * l.toNat + 1 < s.core.wvec.length := by omega
          let off0 := fullWatchOffCore s.core l.toNat
          let sz0 := fullWatchSizeCore s.core l.toNat
          have hoff_eq : (s.core.wvec[2 * l.toNat]'h2l_lt).toNat = off0 := by
            unfold off0 fullWatchOffCore
            rw [List.getElem?_eq_getElem h2l_lt, Option.getD_some]
          have hsz_eq : (s.core.wvec[2 * l.toNat + 1]'h2l1_lt).toNat = sz0 := by
            unfold sz0 fullWatchSizeCore
            rw [List.getElem?_eq_getElem h2l1_lt, Option.getD_some]
          have hbd : off0 + sz0 ≤ s.core.wlen := hwat.layout.bounds l.toNat hl_lt
          have hslice0 : WatchSliceOk F_cur s.core l.toNat off0 sz0 := hwat.slices l.toNat hl_lt
          let end0 := off0 + sz0
          have hend_nat :
              ((s.core.wvec[(l <<< (1 : Nat)).toNat]'(by rw [h2l_eq]; omega)).setWidth 64 +
                (s.core.wvec[((l <<< (1 : Nat)) + (1 : BitVec 64)).toNat]'(by
                  rw [h2l1_eq]; omega)).setWidth 64).toNat = end0 := by
            rw [BitVec.toNat_add, zext_toNat _ (by decide), zext_toNat _ (by decide)]
            simp only [h2l_eq, h2l1_eq, hoff_eq, hsz_eq]
            exact Nat.mod_eq_of_lt (by omega)
          cm_steps
          refine wp_loop_inv
            (fun (p, ()) mP =>
              off0 ≤ p.toNat ∧ p.toNat ≤ end0 ∧
              WatchSliceOk F_cur s.core l.toNat p.toNat (end0 - p.toNat) ∧
              ∃ wsP : List (BitVec 32), wsP.length = 2 * c.max_vars ∧
                (FullMem c { s with scratch := { s.scratch with work_stk1 := wsP } } ⋆ R) mP)
            (fun (p, ()) _ => end0 - p.toNat)
            (fun Jp hLoopP => ?_) ?_
          · cm_steps
            have hoff64 :
                ((s.core.wvec[2 * l.toNat]'h2l_lt).setWidth 64).toNat = off0 := by
              rw [zext_toNat _ (by decide)]; exact hoff_eq
            refine hLoopP _ m2 ⟨by simp only [h2l_eq, hoff64]; exact Nat.le_refl _,
              by simp only [h2l_eq, hoff64]; omega, ?_, ws2, hlen2, hm2⟩
            simpa only [h2l_eq, hoff64, show end0 - off0 = sz0 by omega] using hslice0
          · rintro Jp ⟨p, ⟨⟩⟩ mP ⟨hop, hpe, hrem, wsP, hlenP, hmP⟩ hLoopP
            cm_jnz
            · have hp_lt : p.toNat < end0 := by
                have : p.toNat < ((s.core.wvec[(l <<< (1 : Nat)).toNat]'(by
                    rw [h2l_eq]; omega)).setWidth 64 +
                    (s.core.wvec[((l <<< (1 : Nat)) + (1 : BitVec 64)).toNat]'(by
                      rw [h2l1_eq]; omega)).setWidth 64).toNat := by c0_bound
                omega
              have hp_wstk : p.toNat < s.core.wstk.length := by omega
              let w0 := s.core.wstk[p.toNat]'hp_wstk
              have hw0_some : s.core.wstk[p.toNat]? = some w0 :=
                List.getElem?_eq_getElem hp_wstk
              have hstep := WatchSliceOk_step hrem (by omega) hw0_some
              cm_jnz
              · have hbin0 : (w0 &&& 0x80000000#32) ≠ 0#32 := by c0_bound
                have hrem' := (hstep.1 hbin0).2.2.2
                have hp1_eq : (p + (1 : BitVec 64)).toNat = p.toNat + 1 := bv64_add1 (by omega)
                have hlv_eq : (l >>> (1 : Nat)).toNat = l.toNat / 2 := bv64_shr1_toNat l
                have hrem_p1 : WatchSliceOk F_cur s.core l.toNat (p.toNat + 1)
                    (end0 - (p.toNat + 1)) := by
                  simpa [Nat.sub_sub] using hrem'
                cm_jnz
                · have hot_lt : (w0 &&& 0x7FFFFFFF#32).toNat < 2 * s.core.cur_vars := by c0_bound
                  have hl_wsP : (l >>> (1 : Nat)).toNat < wsP.length := by rw [hlv_eq]; omega
                  have hot_wsP : (((w0 &&& 0x7FFFFFFF#32) >>> 1#32).setWidth 64).toNat <
                      wsP.length := by rw [zext_toNat _ (by decide), bv32_shr1_toNat]; omega
                  cm_steps
                  · refine hLoopP (p + (1 : BitVec 64), ()) m (by dsimp only; rw [hp1_eq]; omega)
                      ⟨by rw [hp1_eq]; omega, by rw [hp1_eq]; omega,
                       by rw [hp1_eq]; exact hrem_p1, _, by simp [hlenP], hm⟩
                  · exact hLoopP (p + (1 : BitVec 64), ()) mP (by dsimp only; rw [hp1_eq]; omega)
                      ⟨by rw [hp1_eq]; omega, by rw [hp1_eq]; omega, by rw [hp1_eq]; exact hrem_p1,
                       wsP, hlenP, hmP⟩
                  · exact hLoopP (p + (1 : BitVec 64), ()) mP (by dsimp only; rw [hp1_eq]; omega)
                      ⟨by rw [hp1_eq]; omega, by rw [hp1_eq]; omega, by rw [hp1_eq]; exact hrem_p1,
                       wsP, hlenP, hmP⟩
                · cm_steps
                  exact hLoopP (p + (1 : BitVec 64), ()) mP (by dsimp only; rw [hp1_eq]; omega)
                    ⟨by rw [hp1_eq]; omega, by rw [hp1_eq]; omega, by rw [hp1_eq]; exact hrem_p1,
                     wsP, hlenP, hmP⟩
              · have hlg0 : (w0 &&& 0x80000000#32) = 0#32 := by c0_bound
                have ⟨hrem2, hrem'⟩ := hstep.2 hlg0
                have hp2_eq : (p + (2 : BitVec 64)).toNat = p.toNat + 2 := bv64_add2 (by omega)
                have hrem_p2 : WatchSliceOk F_cur s.core l.toNat (p.toNat + 2)
                    (end0 - (p.toNat + 2)) := by
                  simpa [Nat.sub_sub] using hrem'
                cm_steps
                try (apply (‹∀ (xs : Tup Val [i64]) (m' : Mem 64),
                  wp _ _ _ _ m' → _›); cm_steps)
                exact hLoopP (p + (2 : BitVec 64), ()) mP (by dsimp only; rw [hp2_eq]; omega)
                  ⟨by rw [hp2_eq]; omega, by rw [hp2_eq]; omega, by rw [hp2_eq]; exact hrem_p2,
                   wsP, hlenP, hmP⟩
            · cm_steps
              exact hLoop2 (l + (1 : BitVec 64), ()) mP (by dsimp only; rw [hl1_eq]; omega)
                ⟨by rw [hl1_eq]; omega, wsP, hlenP, hmP⟩
        · clear hLoop2 J2 hm1 hm ws1 hlen1 hw hdm hwat hwl_le hws_len hwv_len hfl_len
            hcv_64 hnlits_eq
          have hcur_64 : s.core.cur_vars < 2 ^ 64 := by unfold dimacsBound at hmax_lt; omega
          have hcur2_64 : 2 * s.core.cur_vars < 2 ^ 64 := by unfold dimacsBound at hmax_lt; omega
          cm_steps
          refine wp_loop_inv
            (fun (pos, ()) m3 =>
              pos.toNat ≤ s.core.arena_len ∧
              ∃ ws3 : List (BitVec 32), ws3.length = 2 * c.max_vars ∧
                (FullMem c { s with scratch := { s.scratch with work_stk1 := ws3 } } ⋆ R) m3)
            (fun (pos, ()) _ => s.core.arena_len - pos.toNat)
            (fun J3 hLoop3 => ?_) ?_
          · cm_steps; exact hLoop3 (0#64, ()) m2 ⟨Nat.zero_le _, ws2, hlen2, hm2⟩
          · clear hm2 ws2 hlen2
            rintro J3 ⟨pos, ⟨⟩⟩ m3 ⟨hpos_le, ws3, hlen3, hm3⟩ hLoop3
            cm_jnz
            · have hpos_lt : pos.toNat < s.core.arena_len := by c0_bound
              have hal_lt : s.core.arena_len < 2 ^ 31 := by
                have := c.harena; unfold dimacsBound at *; omega
              have hpos3_64 : pos.toNat + 3 < 2 ^ 64 := by omega
              cm_jnz
              · cm_steps
                exact hQ ws3 m3 (FullSparseInvW_with_work_stk1 hsp hlen3) hm3
              · have hpos3_le : pos.toNat + 3 ≤ s.core.arena_len := by c0_bound
                have hpos2_eq : (pos + (2 : BitVec 64)).toNat = pos.toNat + 2 :=
                  bv64_add2 (by omega)
                let csz :=
                  s.core.arena[(pos + (2 : BitVec 64)).toNat]'(by rw [hpos2_eq]; omega)
                have hn_bounds := fullArenaNextOff_bounds (ar := s.core.arena)
                  (alen := s.core.arena_len) (cref := pos.toNat) hpos3_le
                have hpos32_eq : (pos.setWidth 32).toNat = pos.toNat := by
                  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
                cm_steps; c0_call hnext
                refine ⟨c, { s with scratch := { s.scratch with work_stk1 := ws3 } }, R, rfl,
                  ⟨hlen.core_ok, { hlen.scratch_ok with work_stk1_len := hlen3 }⟩,
                  hm3, ?_⟩
                dsimp only
                simp only [hpos32_eq]
                let npos_nat := fullArenaNextOff s.core.arena s.core.arena_len pos.toNat
                have hnpos_eq : (BitVec.ofNat 32 npos_nat).setWidth 64 =
                    BitVec.ofNat 64 npos_nat := by
                  apply BitVec.eq_of_toNat_eq
                  rw [zext_toNat _ (by decide), bv32_ofNat_toNat (by omega),
                    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
                have hnpos_to : (BitVec.ofNat 64 npos_nat).toNat = npos_nat := by
                  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
                cm_to_group
                refine wp_join_group
                  (fun () m4 =>
                    ∃ ws4 : List (BitVec 32), ws4.length = 2 * c.max_vars ∧
                      (FullMem c { s with scratch := { s.scratch with work_stk1 := ws4 } } ⋆
                        R) m4)
                  ?_ ?_
                · rintro _ ⟨⟩ m4 ⟨ws4, hlen4, hm4⟩
                  cm_steps
                  exact hLoop3 _ m4 (by dsimp only; rw [hnpos_eq, hnpos_to]; omega)
                    ⟨by rw [hnpos_eq, hnpos_to]; omega, ws4, hlen4, hm4⟩
                · intro J4 hJ4
                  cm_jnz
                  · cm_jnz
                    · have hcsz_ge3 : 3 ≤ csz.toNat := by c0_bound
                      cm_jnz
                      · have hfit : pos.toNat + 3 + csz.toNat ≤ s.core.arena_len := by
                          have h1 := hc
                          simp only [bv_c0, BitVec.reduceToNat] at h1
                          simp only [Nat.mod_eq_of_lt (by omega : pos.toNat + 2 < 2 ^ 64)] at h1
                          have hcsz_eq : s.core.arena[pos.toNat + 2]'(by omega) = csz := by
                            dsimp only [csz]; simp only [hpos2_eq]
                          rw [hcsz_eq] at h1
                          have hcsz_32 := csz.isLt
                          rw [Nat.mod_eq_of_lt (by omega : pos.toNat + 3 + csz.toNat < 2 ^ 64),
                            Nat.mod_eq_of_lt (by omega : s.core.arena_len < 2 ^ 64)] at h1
                          exact h1
                        have hpos3csz_64 : pos.toNat + 3 + csz.toNat < 2 ^ 64 := by omega
                        cm_steps
                        refine wp_loop_inv
                          (fun (_, i, ()) mI => i.toNat ≤ csz.toNat ∧ mI = m3)
                          (fun (_, i, ()) _ => csz.toNat - i.toNat)
                          (fun Ji hLoopI => ?_) ?_
                        · cm_steps; exact hLoopI (0#32, 0#32, ()) m3 ⟨Nat.zero_le _, rfl⟩
                        · rintro Ji ⟨ucnt, i, ⟨⟩⟩ mI ⟨hi_le, hmI⟩ hLoopI
                          rw [hmI]
                          cm_jnz
                          · have hi_lt : i.toNat < csz.toNat := by c0_bound
                            have hi1_eq : (i + (1 : BitVec 32)).toNat = i.toNat + 1 :=
                              bv32_add1 (by omega)
                            have hpi_eq : (pos + (3 : BitVec 64) + i.setWidth 64).toNat =
                                pos.toNat + 3 + i.toNat := bv64_add3_zext_toNat (by omega)
                            have hpi_lt : pos.toNat + 3 + i.toNat < s.core.arena.length := by
                              omega
                            have hpi_ar : (pos + (3 : BitVec 64) + i.setWidth 64).toNat <
                                ({ s with scratch := { s.scratch with work_stk1 := ws3 } } :
                                  FullState).core.arena.length := by
                              change (pos + (3 : BitVec 64) + i.setWidth 64).toNat <
                                s.core.arena.length
                              rw [hpi_eq]; exact hpi_lt
                            have hpi_64 : pos.toNat + 3 + i.toNat < 2 ^ 64 :=
                              Nat.lt_trans (by omega) hpos3csz_64
                            cm_jnz
                            · let lit := s.core.arena[pos.toNat + 3 + i.toNat]'hpi_lt
                              have hlit_lt : lit.toNat < 2 * s.core.cur_vars := by
                                have h1 := hc
                                dsimp only [lit]
                                simp only [bv_c0, BitVec.reduceToNat,
                                  Nat.mod_eq_of_lt hpi_64, Nat.mod_eq_of_lt hcur_64,
                                  Nat.mod_eq_of_lt hcur2_64] at h1
                                exact h1
                              have hlit64 : (lit.setWidth 64).toNat < 2 * s.core.cur_vars := by
                                rw [zext_toNat _ (by decide)]; exact hlit_lt
                              have hlit_vals_bd :
                                  (({ s with scratch := { s.scratch with work_stk1 := ws3 } } :
                                      FullState).core.arena[(pos + (3 : BitVec 64) +
                                        i.setWidth 64).toNat]'hpi_ar |>.setWidth 64).toNat <
                                    ({ s with scratch := { s.scratch with work_stk1 := ws3 } } :
                                      FullState).core.vals.length := by
                                change ((s.core.arena[(pos + (3 : BitVec 64) +
                                    i.setWidth 64).toNat]'(by rw [hpi_eq]; omega)).setWidth
                                    64).toNat < s.core.vals.length
                                have heq : s.core.arena[(pos + (3 : BitVec 64) +
                                    i.setWidth 64).toNat]'(by rw [hpi_eq]; omega) = lit := by
                                  dsimp only [lit]; simp only [hpi_eq]
                                rw [heq]; exact Nat.lt_of_lt_of_le hlit64 (by
                                  rw [hv_len]; exact Nat.mul_le_mul_left 2 hcv_le)
                              cm_jnz
                              · clear hJ hLoopI Ji
                                cm_steps; exact hJ4 () m3 ⟨ws3, hlen3, hm3⟩
                              · cm_jnz
                                · cm_steps
                                  exact hLoopI (ucnt + (1 : BitVec 32), i + (1 : BitVec 32), ())
                                    m3 (by dsimp only; rw [hi1_eq]; omega)
                                    ⟨by rw [hi1_eq]; omega, rfl⟩
                                · cm_steps
                                  exact hLoopI (ucnt, i + (1 : BitVec 32), ())
                                    m3 (by dsimp only; rw [hi1_eq]; omega)
                                    ⟨by rw [hi1_eq]; omega, rfl⟩
                            · cm_steps
                              exact hLoopI (ucnt, i + (1 : BitVec 32), ())
                                m3 (by dsimp only; rw [hi1_eq]; omega) ⟨by rw [hi1_eq]; omega, rfl⟩
                          · clear hLoopI Ji
                            cm_jnz; cm_jnz
                            · cm_steps
                              refine wp_loop_inv
                                (fun (i2, ()) mK =>
                                  i2.toNat ≤ csz.toNat ∧
                                  ∃ wsK : List (BitVec 32), wsK.length = 2 * c.max_vars ∧
                                    (FullMem c { s with scratch :=
                                      { s.scratch with work_stk1 := wsK } } ⋆ R) mK)
                                (fun (i2, ()) _ => csz.toNat - i2.toNat)
                                (fun Jk hLoopK => ?_) ?_
                              · cm_steps
                                exact hLoopK (0#32, ()) m3 ⟨Nat.zero_le _, ws3, hlen3, hm3⟩
                              · rintro Jk ⟨i2, ⟨⟩⟩ mK ⟨hi2_le, wsK, hlenK, hmK⟩ hLoopK
                                cm_jnz
                                · have hi2_lt : i2.toNat < csz.toNat := by c0_bound
                                  have hi2_1_eq : (i2 + (1 : BitVec 32)).toNat = i2.toNat + 1 :=
                                    bv32_add1 (by omega)
                                  have hpi2_eq :
                                      (pos + (3 : BitVec 64) + i2.setWidth 64).toNat =
                                      pos.toNat + 3 + i2.toNat := bv64_add3_zext_toNat (by omega)
                                  have hpi2_lt :
                                      pos.toNat + 3 + i2.toNat < s.core.arena.length := by omega
                                  have hpi2_ar :
                                      (pos + (3 : BitVec 64) + i2.setWidth 64).toNat <
                                      ({ s with scratch := { s.scratch with work_stk1 := wsK } } :
                                        FullState).core.arena.length := by
                                    change (pos + (3 : BitVec 64) + i2.setWidth 64).toNat <
                                      s.core.arena.length
                                    rw [hpi2_eq]; exact hpi2_lt
                                  have hpi2_64 : pos.toNat + 3 + i2.toNat < 2 ^ 64 :=
                                    Nat.lt_trans (by omega) hpos3csz_64
                                  cm_jnz
                                  · have hlit2_lt :
                                        (s.core.arena[pos.toNat + 3 + i2.toNat]'hpi2_lt).toNat <
                                        2 * s.core.cur_vars := by
                                      have h1 := hc
                                      simp only [bv_c0, BitVec.reduceToNat,
                                        Nat.mod_eq_of_lt hpi2_64, Nat.mod_eq_of_lt hcur_64,
                                        Nat.mod_eq_of_lt hcur2_64] at h1
                                      exact h1
                                    have hlit2_64 :
                                        ((s.core.arena[pos.toNat + 3 +
                                          i2.toNat]'hpi2_lt).setWidth 64).toNat <
                                        2 * s.core.cur_vars := by
                                      rw [zext_toNat _ (by decide)]; exact hlit2_lt
                                    have hws_idx :
                                        (((s.core.arena[pos.toNat + 3 + i2.toNat]'hpi2_lt) >>>
                                          1#32).setWidth 64).toNat < wsK.length := by
                                      rw [zext_toNat _ (by decide), bv32_shr1_toNat, hlenK]
                                      exact Nat.lt_of_lt_of_le
                                        ((Nat.div_lt_iff_lt_mul (by decide)).mpr (by
                                          simpa [Nat.mul_comm] using hlit2_lt))
                                        (Nat.le_trans hcv_le
                                          (Nat.le_mul_of_pos_left _ Nat.zero_lt_two))
                                    have hlit2_vals_bd :
                                        (({ s with scratch := { s.scratch with
                                              work_stk1 := wsK } } : FullState).core.arena[
                                            (pos + (3 : BitVec 64) +
                                              i2.setWidth 64).toNat]'hpi2_ar |>.setWidth
                                              64).toNat <
                                          ({ s with scratch := { s.scratch with
                                              work_stk1 := wsK } } :
                                            FullState).core.vals.length := by
                                      change ((s.core.arena[(pos + (3 : BitVec 64) +
                                          i2.setWidth 64).toNat]'(by
                                            rw [hpi2_eq]; omega)).setWidth
                                          64).toNat < s.core.vals.length
                                      simp only [hpi2_eq]
                                      exact Nat.lt_of_lt_of_le hlit2_64 (by
                                        rw [hv_len]; exact Nat.mul_le_mul_left 2 hcv_le)
                                    have hlit2_ws_bd :
                                        ((({ s with scratch := { s.scratch with
                                              work_stk1 := wsK } } : FullState).core.arena[
                                            (pos + (3 : BitVec 64) +
                                              i2.setWidth 64).toNat]'hpi2_ar >>> 1#32).setWidth
                                              64).toNat <
                                          ({ s with scratch := { s.scratch with
                                              work_stk1 := wsK } } :
                                            FullState).scratch.work_stk1.length := by
                                      change (((s.core.arena[(pos + (3 : BitVec 64) +
                                          i2.setWidth 64).toNat]'(by rw [hpi2_eq]; omega)) >>>
                                          1#32).setWidth 64).toNat < wsK.length
                                      simp only [hpi2_eq]; exact hws_idx
                                    cm_jnz
                                    · cm_steps
                                      refine hLoopK (i2 + (1 : BitVec 32), ()) m
                                        (by dsimp only; rw [hi2_1_eq]; omega)
                                        ⟨by rw [hi2_1_eq]; omega, _, ?_, hm⟩
                                      rw [List.length_set]; exact hlenK
                                    · cm_steps
                                      exact hLoopK (i2 + (1 : BitVec 32), ()) mK
                                        (by dsimp only; rw [hi2_1_eq]; omega)
                                        ⟨by rw [hi2_1_eq]; omega, wsK, hlenK, hmK⟩
                                  · cm_steps
                                    exact hLoopK (i2 + (1 : BitVec 32), ()) mK
                                      (by dsimp only; rw [hi2_1_eq]; omega)
                                      ⟨by rw [hi2_1_eq]; omega, wsK, hlenK, hmK⟩
                                · cm_steps; exact hJ4 () mK ⟨wsK, hlenK, hmK⟩
                            · cm_steps; exact hJ4 () m3 ⟨ws3, hlen3, hm3⟩
                      · cm_steps; exact hJ4 () m3 ⟨ws3, hlen3, hm3⟩
                    · cm_steps; exact hJ4 () m3 ⟨ws3, hlen3, hm3⟩
                  · cm_steps; exact hJ4 () m3 ⟨ws3, hlen3, hm3⟩
            · cm_steps; exact hQ ws3 m3 (FullSparseInvW_with_work_stk1 hsp hlen3) hm3

theorem watchSliceOk_relocate {F_cur : List (List Nat)} {k k' : FullCoreState}
    {lit p p' rem : Nat} (hcv : k'.cur_vars = k.cur_vars)
    (har : k'.arena = k.arena) (hal : k'.arena_len = k.arena_len)
    (hwstk : ∀ idx < rem, k'.wstk[p' + idx]? = k.wstk[p + idx]?)
    (h : WatchSliceOk F_cur k lit p rem) : WatchSliceOk F_cur k' lit p' rem := by
  induction h generalizing p' with
  | empty => exact .empty
  | @bin p rem w0 hp hf hne hlt hent _ ih =>
    exact .bin (by simpa using (hwstk 0 (by omega)).trans hp) hf hne (hcv ▸ hlt) hent
      (ih (p' := p' + 1) fun idx hi => by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hwstk (idx + 1) (by omega))
  | @large p rem w0 w1 hp h1 hf hn hlt _ ih =>
    have hrefs : fullArenaClauseRefsCore k' = fullArenaClauseRefsCore k := by
      simp only [fullArenaClauseRefsCore, har, hal]
    exact .large (by simpa using (hwstk 0 (by omega)).trans hp)
      (by simpa [Nat.add_assoc] using (hwstk 1 (by omega)).trans h1) hf hn (hrefs ▸ hlt)
      (ih (p' := p' + 2) fun idx hi => by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hwstk (idx + 2) (by omega))

theorem bv32_two_mul_or_one (nv : Nat) :
    (BitVec.ofNat 32 (2 * nv) ||| 1#32) = BitVec.ofNat 32 (2 * nv + 1) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_ofNat, Nat.testBit]
  cases i with
  | zero => simp [hi]
  | succ j =>
    have h1 : 1 >>> (j + 1) % 2 = 0 := by
      rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt (Nat.one_lt_two_pow (by omega)), Nat.zero_mod]
    have h2 : (2 * nv + 1) >>> (j + 1) = (2 * nv) >>> (j + 1) := by
      rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.pow_succ',
        ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul,
        show (2 * nv + 1) / 2 = (2 * nv) / 2 by omega]
    simp [h1, h2]

theorem bv32_lit_pack {nv : Nat} (hnv : nv < 2 ^ 30) (ot : BitVec 32) :
    ((BitVec.ofNat 32 nv <<< 1#32) ||| (ot &&& 1#32)).toNat = 2 * nv + ot.toNat % 2 := by
  have ha : (ot &&& 1#32) = if ot.toNat % 2 = 0 then 0#32 else 1#32 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, show (1#32).toNat = 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod ot.toNat 1]
    rcases Nat.mod_two_eq_zero_or_one ot.toNat with hm | hm <;> simp [hm]
  have hs : (BitVec.ofNat 32 nv <<< 1#32) = BitVec.ofNat 32 (2 * nv) := by
    apply BitVec.eq_of_toNat_eq
    change (BitVec.ofNat 32 nv <<< (1 : Nat)).toNat = (BitVec.ofNat 32 (2 * nv)).toNat
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, bv32_ofNat_toNat (n := nv) (by omega),
      bv32_ofNat_toNat (n := 2 * nv) (by omega), show 2 ^ 1 = 2 from rfl, Nat.mul_comm nv 2,
      Nat.mod_eq_of_lt (by omega : 2 * nv < 2 ^ 32)]
  rw [ha, hs]
  rcases Nat.mod_two_eq_zero_or_one ot.toNat with hm | hm
  · simp only [hm, ↓reduceIte, BitVec.or_zero]
    exact bv32_ofNat_toNat (n := 2 * nv) (by omega)
  · simp only [hm, Nat.one_ne_zero, ↓reduceIte, bv32_two_mul_or_one]
    exact bv32_ofNat_toNat (n := 2 * nv + 1) (by omega)

private theorem compactBins_zero_slice_layout {c : FullCfg} {kL : FullCoreState}
    {wvecL : List (BitVec 32)} {l : Nat} (hwvec : kL.wvec = wvecL)
    (hwvL : wvecL.length = 4 * c.max_vars) (hcv : kL.cur_vars ≤ c.max_vars)
    (hl : l < 2 * kL.cur_vars) (hsz0 : fullWatchSizeCore kL l = 0)
    (hlayL : WatchStackLayout kL) :
    let wvec' := wvecL.set (2 * l) 0#32
    let k' : FullCoreState := { kL with wvec := wvec' }
    fullWatchOffCore k' l = 0 ∧ fullWatchSizeCore k' l = 0 ∧
    (∀ j, j ≠ l →
      fullWatchOffCore k' j = fullWatchOffCore kL j ∧
      fullWatchSizeCore k' j = fullWatchSizeCore kL j) ∧
    WatchStackLayout k' := by
  intro wvec' k'
  have h2l_lt : 2 * l < wvecL.length := by omega
  have hoff'_l : fullWatchOffCore k' l = 0 := by
    unfold fullWatchOffCore k' wvec'
    rw [List.getElem?_set_self h2l_lt, Option.getD_some]; rfl
  have hsz'_l : fullWatchSizeCore k' l = 0 := by
    unfold fullWatchSizeCore k' wvec'
    rw [List.getElem?_set_ne (by omega), ← hwvec]; exact hsz0
  have hne_eq : ∀ j, j ≠ l →
      fullWatchOffCore k' j = fullWatchOffCore kL j ∧
      fullWatchSizeCore k' j = fullWatchSizeCore kL j := fun j hj => by
    unfold fullWatchOffCore fullWatchSizeCore k' wvec'
    rw [← hwvec]; constructor <;> rw [List.getElem?_set_ne (by omega)]
  refine ⟨hoff'_l, hsz'_l, hne_eq,
    ⟨fun j hj => by
       by_cases hjl : j = l
       · subst hjl; rw [hoff'_l, hsz'_l]; exact Nat.zero_le _
       · obtain ⟨ho, hs⟩ := hne_eq j hjl; rw [ho, hs]; exact hlayL.bounds j hj,
     fun j hj hp => by
       by_cases hjl : j = l
       · subst hjl; rw [hsz'_l] at hp; omega
       · obtain ⟨ho, hs⟩ := hne_eq j hjl; rw [ho]; rw [hs] at hp; exact hlayL.pos_off j hj hp,
     fun j1 j2 h1 h2 hne hp1 hp2 => by
       by_cases hj1 : j1 = l
       · subst hj1; rw [hsz'_l] at hp1; omega
       · by_cases hj2 : j2 = l
         · subst hj2; rw [hsz'_l] at hp2; omega
         · obtain ⟨ho1, hs1⟩ := hne_eq j1 hj1; obtain ⟨ho2, hs2⟩ := hne_eq j2 hj2
           rw [ho1, hs1, ho2, hs2]; rw [hs1] at hp1; rw [hs2] at hp2
           exact hlayL.disjoint j1 j2 h1 h2 hne hp1 hp2,
     fun j hj idx hi => by
       by_cases hjl : j = l
       · subst hjl; rw [hsz'_l] at hi; omega
       · obtain ⟨ho, hs⟩ := hne_eq j hjl; rw [ho]; rw [hs] at hi
         exact hlayL.no_sentinel j hj idx hi⟩⟩

private theorem compactBins_loop2_step {old_cv ncv v nv cmax : Nat}
    {vals : List (BitVec 8)} {map inv : List (BitVec 32)}
    {wvecL wvec2 : List (BitVec 32)} (hbij : CompactBijOk old_cv ncv vals map inv)
    (hwv2 : wvec2.length = 4 * cmax) (hv_lt : v < old_cv) (hcv_le : old_cv ≤ cmax)
    (hnv_lt : nv < ncv) (hnv_lt_v : nv < v)
    (hi_v : inv[nv]? = some (BitVec.ofNat 32 v))
    (hhi2 : ∀ w, v ≤ w → w < old_cv → ∀ d < 4, wvec2[4 * w + d]? = wvecL[4 * w + d]?)
    (hmap2 : ∀ nv' < ncv, ∀ ov, (inv[nv']?.getD 0#32).toNat = ov → ov < v →
      ∀ d < 4, wvec2[4 * nv' + d]? = wvecL[4 * ov + d]?)
    (hb0 : 4 * v < wvec2.length) (hb1 : 4 * v + 1 < wvec2.length)
    (hb2 : 4 * v + 2 < wvec2.length) (hb3 : 4 * v + 3 < wvec2.length) :
    let wvec2' := (((wvec2.set (4 * nv) (wvec2[4 * v]'hb0)).set (4 * nv + 1)
      (wvec2[4 * v + 1]'hb1)).set (4 * nv + 2) (wvec2[4 * v + 2]'hb2)).set
      (4 * nv + 3) (wvec2[4 * v + 3]'hb3)
    wvec2'.length = 4 * cmax ∧
    (∀ w, v + 1 ≤ w → w < old_cv → ∀ d < 4, wvec2'[4 * w + d]? = wvecL[4 * w + d]?) ∧
    (∀ nv' < ncv, ∀ ov, (inv[nv']?.getD 0#32).toNat = ov → ov < v + 1 →
      ∀ d < 4, wvec2'[4 * nv' + d]? = wvecL[4 * ov + d]?) := by
  intro wvec2'
  have hncv_le := hbij.ncv_le
  have hov_lt32 : old_cv < 2 ^ 32 := by have := hbij.old_cv_lt; omega
  refine ⟨by simp [wvec2', hwv2], fun w hw1 hw2 d hd => ?_, fun nv' hnv' ov hov1 hov2 d hd => ?_⟩
  · dsimp only [wvec2']
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
    exact hhi2 w (by omega) hw2 d hd
  · by_cases heq : ov = v
    · have hnv_eq : nv' = nv := hbij.inv_inj (nv1 := nv') (nv2 := nv) hnv' hnv_lt
        (by rw [hov1, heq, hi_v, Option.getD_some, bv32_ofNat_toNat (by omega)])
      subst hnv_eq
      rw [heq]
      rcases (by omega : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3) with rfl | rfl | rfl | rfl <;>
        dsimp only [wvec2']
      · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
          List.getElem?_set_ne (by omega), Nat.add_zero,
          List.getElem?_set_self (by rw [hwv2]; omega)]
        simpa [List.getElem?_eq_getElem hb0] using hhi2 v (Nat.le_refl _) hv_lt 0 (by omega)
      · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
          List.getElem?_set_self (by simp [hwv2]; omega)]
        simpa [List.getElem?_eq_getElem hb1] using hhi2 v (Nat.le_refl _) hv_lt 1 (by omega)
      · rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by simp [hwv2]; omega)]
        simpa [List.getElem?_eq_getElem hb2] using hhi2 v (Nat.le_refl _) hv_lt 2 (by omega)
      · rw [List.getElem?_set_self (by simp [hwv2]; omega)]
        simpa [List.getElem?_eq_getElem hb3] using hhi2 v (Nat.le_refl _) hv_lt 3 (by omega)
    · have hnv'_ne : nv' ≠ nv := fun hsame => by
        subst hsame
        have : ov = v := by rw [hi_v, Option.getD_some, bv32_ofNat_toNat (by omega)] at hov1; omega
        exact heq this
      dsimp only [wvec2']
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
        List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
      exact hmap2 nv' hnv' ov hov1 (by omega) d hd

private theorem compactBins_loop3_step {ncv old_cv v3 cmax : Nat}
    {wvec2 wvec3 : List (BitVec 32)} (hwv3 : wvec3.length = 4 * cmax) (hncv_v3 : ncv ≤ v3)
    (hv3_lt : v3 < old_cv) (hcv_le : old_cv ≤ cmax)
    (hzero3 : ∀ w, ncv ≤ w → w < v3 → ∀ d < 4, wvec3[4 * w + d]? = some 0#32)
    (hpres3 : ∀ nv < ncv, ∀ d < 4, wvec3[4 * nv + d]? = wvec2[4 * nv + d]?) :
    let wvec3' := (((wvec3.set (4 * v3) 0#32).set (4 * v3 + 1) 0#32).set
      (4 * v3 + 2) 0#32).set (4 * v3 + 3) 0#32
    wvec3'.length = 4 * cmax ∧
    (∀ w, ncv ≤ w → w < v3 + 1 → ∀ d < 4, wvec3'[4 * w + d]? = some 0#32) ∧
    (∀ nv < ncv, ∀ d < 4, wvec3'[4 * nv + d]? = wvec2[4 * nv + d]?) := by
  intro wvec3'
  refine ⟨by simp [wvec3', hwv3], fun w hw1 hw2 d hd => ?_, fun nv hnv d hd => ?_⟩
  · by_cases hwv : w = v3
    · subst hwv
      rcases (by omega : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3) with rfl | rfl | rfl | rfl <;>
        dsimp only [wvec3']
      · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
          List.getElem?_set_ne (by omega), Nat.add_zero,
          List.getElem?_set_self (by rw [hwv3]; omega)]
      · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
          List.getElem?_set_self (by simp [hwv3]; omega)]
      · rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by simp [hwv3]; omega)]
      · rw [List.getElem?_set_self (by simp [hwv3]; omega)]
    · dsimp only [wvec3']
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
        List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
      exact hzero3 w hw1 (by omega) d hd
  · have hnv_lt_v3 : nv < v3 := by omega
    dsimp only [wvec3']
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
    exact hpres3 nv hnv d hd

private theorem compactBins_loop3_done {ncv old_cv : Nat} {inv : List (BitVec 32)}
    {kL k3 : FullCoreState} {wvecL wvec2 wvec3 : List (BitVec 32)}
    (hk3 : k3.wvec = wvec3) (hkL : kL.wvec = wvecL)
    (hzero3 : ∀ w, ncv ≤ w → w < old_cv → ∀ d < 4, wvec3[4 * w + d]? = some 0#32)
    (hpres3 : ∀ nv < ncv, ∀ d < 4, wvec3[4 * nv + d]? = wvec2[4 * nv + d]?)
    (hmap2 : ∀ nv < ncv, ∀ ov, (inv[nv]?.getD 0#32).toNat = ov → ov < old_cv →
      ∀ d < 4, wvec2[4 * nv + d]? = wvecL[4 * ov + d]?) :
    (∀ l, 2 * ncv ≤ l → l < 2 * old_cv →
      fullWatchOffCore k3 l = 0 ∧ fullWatchSizeCore k3 l = 0) ∧
    (∀ nv < ncv, ∀ ov, (inv[nv]?.getD 0#32).toNat = ov → ov < old_cv →
      k3.wvec[4 * nv]? = kL.wvec[4 * ov]? ∧ k3.wvec[4 * nv + 1]? = kL.wvec[4 * ov + 1]? ∧
      k3.wvec[4 * nv + 2]? = kL.wvec[4 * ov + 2]? ∧
      k3.wvec[4 * nv + 3]? = kL.wvec[4 * ov + 3]?) := by
  refine ⟨fun l h1 h2 => ?_, fun nv hnv ov hov1 hov2 => ?_⟩
  · have hz0 := hzero3 (l / 2) (by omega) (by omega)
    unfold fullWatchOffCore fullWatchSizeCore; rw [hk3]
    rcases Nat.mod_two_eq_zero_or_one l with hm2 | hm2
    · rw [show 2 * l + 1 = 4 * (l / 2) + 1 by omega, show 2 * l = 4 * (l / 2) + 0 by omega,
        hz0 0 (by omega), hz0 1 (by omega)]; exact ⟨rfl, rfl⟩
    · rw [show 2 * l + 1 = 4 * (l / 2) + 3 by omega, show 2 * l = 4 * (l / 2) + 2 by omega,
        hz0 2 (by omega), hz0 3 (by omega)]; exact ⟨rfl, rfl⟩
  · have hp := hpres3 nv hnv; have hm := hmap2 nv hnv ov hov1 hov2
    rw [hk3, hkL]
    exact ⟨(hp 0 (by omega)).trans (hm 0 (by omega)), (hp 1 (by omega)).trans (hm 1 (by omega)),
      (hp 2 (by omega)).trans (hm 2 (by omega)), (hp 3 (by omega)).trans (hm 3 (by omega))⟩

private def binsPostPExpr (h l off64 end64 keptP q wvecP wstkP : Val i64)
    (J1 : Cont [i64, i64]) : Expr Val Cont [] :=
  Expr.group (sig := [[i64]]) (fun Js_3 =>
  Blocks.cons (fun p_25 =>
  Expr.let_ ⟨OpCode.cmp CmpOp.ult i64 Ty.bool rfl, (Arg.var p_25.fst, Arg.var end64, ())⟩
    fun p_26 =>
  Expr.jnz (Arg.var p_26.fst)
  (Expr.let_ ⟨OpCode.mul i64, (Arg.var p_25.fst, Arg.imm 4, ())⟩ fun p =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var wstkP, Arg.var p.fst, ())⟩ fun p =>
  Expr.store (t := i32) (Arg.imm 4294967295) (Arg.var p.fst)
  (Expr.let_ ⟨OpCode.add i64, (Arg.var p_25.fst, Arg.imm 1, ())⟩ fun p =>
  Expr.jump Js_3.fst (Arg.var p.fst, ())))
  (Expr.group (sig := [[]]) (fun _Js_4 =>
  Blocks.cons (fun _ =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var h, Arg.imm 464, ())⟩ fun p_28 =>
  Expr.load i64 (Arg.var p_28.fst) fun ld =>
  Expr.let_ ⟨OpCode.sub i64, (Arg.var end64, Arg.var q, ())⟩ fun p_29 =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var ld, Arg.var p_29.fst, ())⟩ fun p_30 =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var h, Arg.imm 464, ())⟩ fun p =>
  Expr.store (Arg.var p_30.fst) (Arg.var p.fst)
  (Expr.let_ ⟨OpCode.add i64, (Arg.var l, Arg.imm 1, ())⟩ fun p =>
  Expr.jump J1 (Arg.var keptP, Arg.var p.fst, ()))) Blocks.nil) fun Js =>
  Expr.let_ ⟨OpCode.cmp CmpOp.eq i64 Ty.bool rfl, (Arg.var q, Arg.var off64,
    ())⟩ fun p =>
  Expr.jnz (Arg.var p.fst)
  (Expr.let_ ⟨OpCode.sext 32 64, (Arg.imm 1, ())⟩ fun p =>
  Expr.let_ ⟨OpCode.shl i64, (Arg.var l, Arg.var p.fst, ())⟩ fun p =>
  Expr.let_ ⟨OpCode.mul i64, (Arg.var p.fst, Arg.imm 4, ())⟩ fun p =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var wvecP, Arg.var p.fst, ())⟩ fun p =>
  Expr.store (t := i32) (Arg.imm 0) (Arg.var p.fst)
  (Expr.let_ ⟨OpCode.sext 32 64, (Arg.imm 1, ())⟩ fun p =>
  Expr.let_ ⟨OpCode.shl i64, (Arg.var l, Arg.var p.fst, ())⟩ fun p =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var p.fst, Arg.imm 1, ())⟩ fun p =>
  Expr.let_ ⟨OpCode.mul i64, (Arg.var p.fst, Arg.imm 4, ())⟩ fun p =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var wvecP, Arg.var p.fst, ())⟩ fun p =>
  Expr.store (t := i32) (Arg.imm 0) (Arg.var p.fst)
  (Expr.jump Js.fst ())))
  (Expr.let_ ⟨OpCode.sext 32 64, (Arg.imm 1, ())⟩ fun p =>
  Expr.let_ ⟨OpCode.shl i64, (Arg.var l, Arg.var p.fst, ())⟩ fun p =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var p.fst, Arg.imm 1, ())⟩ fun p =>
  Expr.let_ ⟨OpCode.mul i64, (Arg.var p.fst, Arg.imm 4, ())⟩ fun p =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var wvecP, Arg.var p.fst, ())⟩ fun p =>
  Expr.let_ ⟨OpCode.sub i64, (Arg.var q, Arg.var off64, ())⟩ fun p_27 =>
  Expr.let_ ⟨OpCode.trunc 64 32, (Arg.var p_27.fst, ())⟩ fun p_28 =>
  Expr.store (Arg.var p_28.fst) (Arg.var p.fst)
  (Expr.jump Js.fst ())))) Blocks.nil) fun Js =>
  Expr.jump Js.fst (Arg.var q, ())

private def binsPLoopExpr (h kept l off64 end64 wvecP wstkP mapP valsP nlits : Val i64)
    (keep_l : Val .bool) (J1 : Cont [i64, i64]) : Expr Val Cont [] :=
  Expr.group (sig := [[i64, i64, i64]]) (fun Js_2 =>
  Blocks.cons (fun p_23 =>
  Expr.let_ ⟨OpCode.cmp CmpOp.ult i64 Ty.bool rfl, (Arg.var p_23.snd.fst, Arg.var end64,
    ())⟩ fun p_24 =>
  Expr.jnz (Arg.var p_24.fst)
  (Expr.let_ ⟨OpCode.mul i64, (Arg.var p_23.snd.fst, Arg.imm 4, ())⟩ fun p =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var wstkP, Arg.var p.fst, ())⟩ fun p =>
  Expr.load i32 (Arg.var p.fst) fun ld_6 =>
  Expr.group (sig := [[i64, i64, i64]]) (fun _Js =>
  Blocks.cons (fun p =>
  Expr.jump Js_2.fst (Arg.var p.fst, Arg.var p.snd.fst, Arg.var p.snd.snd.fst, ()))
    Blocks.nil) fun Js =>
  Expr.let_ ⟨OpCode.and i32, (Arg.var ld_6, Arg.imm 2147483648, ())⟩ fun p =>
  Expr.let_ ⟨OpCode.cmp CmpOp.ne i32 Ty.bool rfl, (Arg.var p.fst, Arg.imm 0, ())⟩ fun p =>
  Expr.jnz (Arg.var p.fst)
  (Expr.let_ ⟨OpCode.and i32, (Arg.var ld_6, Arg.imm 2147483647, ())⟩ fun p =>
  Expr.group (sig := [[i64, i64]]) (fun _Js_3 =>
  Blocks.cons (fun p =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var p_23.snd.fst, Arg.imm 1, ())⟩ fun p_25 =>
  Expr.jump Js.fst (Arg.var p.fst, Arg.var p_25.fst, Arg.var p.snd.fst, ())) Blocks.nil)
    fun Js =>
  Expr.jnz (Arg.var keep_l)
  (Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p.fst, ())⟩ fun p_25 =>
  Expr.let_ ⟨OpCode.cmp CmpOp.ult i64 Ty.bool rfl, (Arg.var p_25.fst, Arg.var nlits, ())⟩
    fun p_26 =>
  Expr.jnz (Arg.var p_26.fst)
  (Expr.let_ ⟨OpCode.lshr i32, (Arg.var p.fst, Arg.imm 1, ())⟩ fun p_27 =>
  Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p_27.fst, ())⟩ fun p_28 =>
  Expr.let_ ⟨OpCode.mul i64, (Arg.var p_28.fst, Arg.imm 4, ())⟩ fun p_29 =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var mapP, Arg.var p_29.fst, ())⟩ fun p_30 =>
  Expr.load i32 (Arg.var p_30.fst) fun ld_7 =>
  Expr.let_ ⟨OpCode.cmp CmpOp.ne i32 Ty.bool rfl, (Arg.var ld_7, Arg.imm 4294967295, ())⟩
    fun p_31 =>
  Expr.jnz (Arg.var p_31.fst)
  (Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p.fst, ())⟩ fun p_32 =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var valsP, Arg.var p_32.fst, ())⟩ fun p_33 =>
  Expr.load i8 (Arg.var p_33.fst) fun ld =>
  Expr.let_ ⟨OpCode.trunc 32 8, (Arg.imm 0, ())⟩ fun p_34 =>
  Expr.let_ ⟨OpCode.sext 8 32, (Arg.var ld, ())⟩ fun p_35 =>
  Expr.let_ ⟨OpCode.sext 8 32, (Arg.var p_34.fst, ())⟩ fun p_36 =>
  Expr.let_ ⟨OpCode.cmp CmpOp.eq i32 Ty.bool rfl, (Arg.var p_35.fst, Arg.var p_36.fst, ())⟩
    fun p_37 =>
  Expr.jnz (Arg.var p_37.fst)
  (Expr.let_ ⟨OpCode.lshr i32, (Arg.var p.fst, Arg.imm 1, ())⟩ fun p_38 =>
  Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p_38.fst, ())⟩ fun p_39 =>
  Expr.let_ ⟨OpCode.mul i64, (Arg.var p_39.fst, Arg.imm 4, ())⟩ fun p_40 =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var mapP, Arg.var p_40.fst, ())⟩ fun p_41 =>
  Expr.load i32 (Arg.var p_41.fst) fun ld =>
  Expr.let_ ⟨OpCode.shl i32, (Arg.var ld, Arg.imm 1, ())⟩ fun p_42 =>
  Expr.let_ ⟨OpCode.and i32, (Arg.var p.fst, Arg.imm 1, ())⟩ fun p =>
  Expr.let_ ⟨OpCode.or i32, (Arg.var p_42.fst, Arg.var p.fst, ())⟩ fun p =>
  Expr.let_ ⟨OpCode.mul i64, (Arg.var p_23.snd.snd.fst, Arg.imm 4, ())⟩ fun p_43 =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var wstkP, Arg.var p_43.fst, ())⟩ fun p_44 =>
  Expr.let_ ⟨OpCode.and i32, (Arg.var p.fst, Arg.imm 2147483647, ())⟩ fun p =>
  Expr.let_ ⟨OpCode.or i32, (Arg.var p.fst, Arg.imm 2147483648, ())⟩ fun p =>
  Expr.store (Arg.var p.fst) (Arg.var p_44.fst)
  (Expr.let_ ⟨OpCode.add i64, (Arg.var p_23.snd.snd.fst, Arg.imm 1, ())⟩ fun p =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var p_23.fst, Arg.imm 1, ())⟩ fun p_45 =>
  Expr.jump Js.fst (Arg.var p_45.fst, Arg.var p.fst, ())))
  (Expr.jump Js.fst (Arg.var p_23.fst, Arg.var p_23.snd.snd.fst, ())))
  (Expr.jump Js.fst (Arg.var p_23.fst, Arg.var p_23.snd.snd.fst, ())))
  (Expr.jump Js.fst (Arg.var p_23.fst, Arg.var p_23.snd.snd.fst, ())))
  (Expr.jump Js.fst (Arg.var p_23.fst, Arg.var p_23.snd.snd.fst, ())))
  (Expr.let_ ⟨OpCode.add i64, (Arg.var p_23.snd.fst, Arg.imm 2, ())⟩ fun p =>
  Expr.jump Js.fst (Arg.var p_23.fst, Arg.var p.fst, Arg.var p_23.snd.snd.fst, ())))
    ((binsPostPExpr h l off64 end64 p_23.fst p_23.snd.snd.fst wvecP wstkP J1))) Blocks.nil)
    fun Js =>
  Expr.jump Js.fst (Arg.var kept, Arg.var off64, Arg.var off64, ())

private def binsTailExpr (h old_cv ncv kept mapP wvecP : Val i64) :
    Expr Val Cont [] :=
  Expr.store (t := i64) (Arg.var (kept >>> (1 : Nat))) (Arg.var (h + (504 : BitVec 64)))
  (Expr.group (sig := [[i64]]) (fun Js =>
  Blocks.cons (fun p_12 =>
  Expr.let_ ⟨OpCode.cmp CmpOp.ult i64 Ty.bool rfl, (Arg.var p_12.fst, Arg.var old_cv, ())⟩
    fun p_13 =>
  Expr.jnz (Arg.var p_13.fst)
  (Expr.let_ ⟨OpCode.mul i64, (Arg.var p_12.fst, Arg.imm 4, ())⟩ fun p =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var mapP, Arg.var p.fst, ())⟩ fun p =>
  Expr.load i32 (Arg.var p.fst) fun ld =>
  Expr.group (sig := [[]]) (fun _Js_1 =>
  Blocks.cons (fun _ =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var p_12.fst, Arg.imm 1, ())⟩ fun p =>
  Expr.jump Js.fst (Arg.var p.fst, ())) Blocks.nil) fun Js =>
  Expr.let_ ⟨OpCode.cmp CmpOp.ne i32 Ty.bool rfl, (Arg.var ld, Arg.imm 4294967295, ())⟩ fun p =>
  Expr.jnz (Arg.var p.fst)
  (Expr.let_ ⟨OpCode.zext 32 64, (Arg.var ld, ())⟩ fun p =>
  Expr.let_ ⟨OpCode.cmp CmpOp.ne i64 Ty.bool rfl, (Arg.var p.fst, Arg.var p_12.fst, ())⟩
    fun p =>
  Expr.jnz (Arg.var p.fst)
  (Expr.let_ ⟨OpCode.sext 32 64, (Arg.imm 2, ())⟩ fun p =>
  Expr.let_ ⟨OpCode.shl i64, (Arg.var p_12.fst, Arg.var p.fst, ())⟩ fun p =>
  Expr.let_ ⟨OpCode.zext 32 64, (Arg.var ld, ())⟩ fun p_14 =>
  Expr.let_ ⟨OpCode.sext 32 64, (Arg.imm 2, ())⟩ fun p_15 =>
  Expr.let_ ⟨OpCode.shl i64, (Arg.var p_14.fst, Arg.var p_15.fst, ())⟩ fun p_16 =>
  Expr.let_ ⟨OpCode.mul i64, (Arg.var p_16.fst, Arg.imm 4, ())⟩ fun p_17 =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var wvecP, Arg.var p_17.fst, ())⟩ fun p_18 =>
  Expr.let_ ⟨OpCode.mul i64, (Arg.var p.fst, Arg.imm 4, ())⟩ fun p_19 =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var wvecP, Arg.var p_19.fst, ())⟩ fun p_20 =>
  Expr.load i32 (Arg.var p_20.fst) fun ld =>
  Expr.store (Arg.var ld) (Arg.var p_18.fst)
  (Expr.let_ ⟨OpCode.add i64, (Arg.var p_16.fst, Arg.imm 1, ())⟩ fun p_21 =>
  Expr.let_ ⟨OpCode.mul i64, (Arg.var p_21.fst, Arg.imm 4, ())⟩ fun p_22 =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var wvecP, Arg.var p_22.fst, ())⟩ fun p_23 =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var p.fst, Arg.imm 1, ())⟩ fun p_24 =>
  Expr.let_ ⟨OpCode.mul i64, (Arg.var p_24.fst, Arg.imm 4, ())⟩ fun p_25 =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var wvecP, Arg.var p_25.fst, ())⟩ fun p_26 =>
  Expr.load i32 (Arg.var p_26.fst) fun ld =>
  Expr.store (Arg.var ld) (Arg.var p_23.fst)
  (Expr.let_ ⟨OpCode.add i64, (Arg.var p_16.fst, Arg.imm 2, ())⟩ fun p_27 =>
  Expr.let_ ⟨OpCode.mul i64, (Arg.var p_27.fst, Arg.imm 4, ())⟩ fun p_28 =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var wvecP, Arg.var p_28.fst, ())⟩ fun p_29 =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var p.fst, Arg.imm 2, ())⟩ fun p_30 =>
  Expr.let_ ⟨OpCode.mul i64, (Arg.var p_30.fst, Arg.imm 4, ())⟩ fun p_31 =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var wvecP, Arg.var p_31.fst, ())⟩ fun p_32 =>
  Expr.load i32 (Arg.var p_32.fst) fun ld =>
  Expr.store (Arg.var ld) (Arg.var p_29.fst)
  (Expr.let_ ⟨OpCode.add i64, (Arg.var p_16.fst, Arg.imm 3, ())⟩ fun p_33 =>
  Expr.let_ ⟨OpCode.mul i64, (Arg.var p_33.fst, Arg.imm 4, ())⟩ fun p_34 =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var wvecP, Arg.var p_34.fst, ())⟩ fun p_35 =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var p.fst, Arg.imm 3, ())⟩ fun p =>
  Expr.let_ ⟨OpCode.mul i64, (Arg.var p.fst, Arg.imm 4, ())⟩ fun p =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var wvecP, Arg.var p.fst, ())⟩ fun p =>
  Expr.load i32 (Arg.var p.fst) fun ld =>
  Expr.store (Arg.var ld) (Arg.var p_35.fst)
  (Expr.jump Js.fst ())))))
  (Expr.jump Js.fst ()))
  (Expr.jump Js.fst ()))
  (Expr.group (sig := [[i64]]) (fun Js =>
  Blocks.cons (fun p_14 =>
  Expr.let_ ⟨OpCode.cmp CmpOp.ult i64 Ty.bool rfl, (Arg.var p_14.fst, Arg.var old_cv, ())⟩
    fun p =>
  Expr.jnz (Arg.var p.fst)
  (Expr.let_ ⟨OpCode.sext 32 64, (Arg.imm 2, ())⟩ fun p =>
  Expr.let_ ⟨OpCode.shl i64, (Arg.var p_14.fst, Arg.var p.fst, ())⟩ fun p =>
  Expr.let_ ⟨OpCode.mul i64, (Arg.var p.fst, Arg.imm 4, ())⟩ fun p_15 =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var wvecP, Arg.var p_15.fst, ())⟩ fun p_16 =>
  Expr.store (t := i32) (Arg.imm 0) (Arg.var p_16.fst)
  (Expr.let_ ⟨OpCode.add i64, (Arg.var p.fst, Arg.imm 1, ())⟩ fun p_17 =>
  Expr.let_ ⟨OpCode.mul i64, (Arg.var p_17.fst, Arg.imm 4, ())⟩ fun p_18 =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var wvecP, Arg.var p_18.fst, ())⟩ fun p_19 =>
  Expr.store (t := i32) (Arg.imm 0) (Arg.var p_19.fst)
  (Expr.let_ ⟨OpCode.add i64, (Arg.var p.fst, Arg.imm 2, ())⟩ fun p_20 =>
  Expr.let_ ⟨OpCode.mul i64, (Arg.var p_20.fst, Arg.imm 4, ())⟩ fun p_21 =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var wvecP, Arg.var p_21.fst, ())⟩ fun p_22 =>
  Expr.store (t := i32) (Arg.imm 0) (Arg.var p_22.fst)
  (Expr.let_ ⟨OpCode.add i64, (Arg.var p.fst, Arg.imm 3, ())⟩ fun p =>
  Expr.let_ ⟨OpCode.mul i64, (Arg.var p.fst, Arg.imm 4, ())⟩ fun p =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var wvecP, Arg.var p.fst, ())⟩ fun p =>
  Expr.store (t := i32) (Arg.imm 0) (Arg.var p.fst)
  (Expr.let_ ⟨OpCode.add i64, (Arg.var p_14.fst, Arg.imm 1, ())⟩ fun p =>
  Expr.jump Js.fst (Arg.var p.fst, ()))))))
  (Expr.ret ())) Blocks.nil) fun Js =>
  Expr.jump Js.fst (Arg.var ncv, ()))) Blocks.nil) fun Js =>
  Expr.jump Js.fst (Arg.imm 0, ()))

private theorem full_compact_bins_post_p {Γ : Env} {Q : Post []} {X : XPost}
    {J1 : Cont [i64, i64]} {c : FullCfg} {F_cur : List (List Nat)} {ncv : BitVec 64}
    {inv : List (BitVec 32)} {s : FullState} {kL : FullCoreState} {R : Mem 64 → Prop}
    {old_cv l keptP q off64 end64 : BitVec 64} {off0 sz0 : Nat}
    {wvecL wstkL wstkP : List (BitVec 32)} {wuL : BitVec 64} {mP : Mem 64}
    (hkL : kL = { s.core with wvec := wvecL, wstk := wstkL, wusable := wuL })
    (hoff_def : off0 = fullWatchOffCore kL l.toNat)
    (hsz_def : sz0 = fullWatchSizeCore kL l.toNat)
    (hcv_le : s.core.cur_vars ≤ c.max_vars)
    (hwc_lt : c.wcap < 2 * 2 ^ 28) (hmax_lt : c.max_vars < 2 * 2 ^ 28)
    (hold : s.core.cur_vars = old_cv.toNat) (hckL : FullCoreState.LengthsOk c kL)
    (hlayL : WatchStackLayout kL) (hwvL : wvecL.length = 4 * c.max_vars)
    (hl_lt : l.toNat < 2 * old_cv.toNat) (hoff64 : off64.toNat = off0)
    (hend64 : end64.toNat = off0 + sz0) (hbd_l : off0 + sz0 ≤ kL.wlen)
    (hsz_pos : 0 < sz0) (hq_ge : off0 ≤ q.toNat) (hq_le : q.toNat ≤ off0 + sz0)
    (hkept_end : keptP.toNat ≤ (l.toNat + 1) * c.wcap) (hwsP : wstkP.length = c.wcap)
    (houtP : ∀ i, i < off0 ∨ off0 + sz0 ≤ i → wstkP[i]? = wstkL[i]?)
    (hpreP : CompactPreBinSliceOk ncv.toNat inv F_cur { kL with wstk := wstkP }
      l.toNat off0 (q.toNat - off0))
    (hpreL : ∀ ol < l.toNat, CompactPreBinSliceOk ncv.toNat inv F_cur kL ol
      (fullWatchOffCore kL ol) (fullWatchSizeCore kL ol))
    (hwatL : ∀ ol, l.toNat ≤ ol → ol < 2 * old_cv.toNat →
      WatchSliceOk F_cur kL ol (fullWatchOffCore kL ol) (fullWatchSizeCore kL ol))
    (hmP : (FullMem c { s with core := { kL with wstk := wstkP } } ⋆ R) mP)
    (hLoop1 : ∀ (ys : Tup Val [i64, i64]) (m' : Mem 64),
      2 * old_cv.toNat - ys.2.1.toNat < 2 * old_cv.toNat - l.toNat →
      (ys.2.1.toNat ≤ 2 * old_cv.toNat ∧ ys.1.toNat ≤ ys.2.1.toNat * c.wcap ∧
        ∃ (wvecL wstkL : List (BitVec 32)) (wuL : BitVec 64),
          wvecL.length = 4 * c.max_vars ∧ wstkL.length = c.wcap ∧
          let k1 : FullCoreState := { s.core with wvec := wvecL, wstk := wstkL, wusable := wuL }
          WatchStackLayout k1 ∧
          (∀ ol < ys.2.1.toNat, CompactPreBinSliceOk ncv.toNat inv F_cur k1 ol
            (fullWatchOffCore k1 ol) (fullWatchSizeCore k1 ol)) ∧
          (∀ ol, ys.2.1.toNat ≤ ol → ol < 2 * old_cv.toNat →
            WatchSliceOk F_cur k1 ol (fullWatchOffCore k1 ol) (fullWatchSizeCore k1 ol)) ∧
          (FullMem c { s with core := k1 } ⋆ R) m') →
      J1 ys m') :
    wp Γ Q X (binsPostPExpr c.hdr l off64 end64 keptP q c.pWvec c.pWstk J1) mP := by
  subst hoff_def; subst hsz_def
  let off0 := fullWatchOffCore kL l.toNat
  let sz0 := fullWatchSizeCore kL l.toNat
  have hl1_eq : (l + (1 : BitVec 64)).toNat = l.toNat + 1 := bv64_add1 (by omega)
  have h2l_eq : (l <<< (1 : Nat)).toNat = 2 * l.toNat := bv64_shl1_toNat (by omega)
  have h2l1_eq : ((l <<< (1 : Nat)) + (1 : BitVec 64)).toNat = 2 * l.toNat + 1 := by
    rw [bv64_add1 (by rw [h2l_eq]; omega), h2l_eq]
  have h2l_lt : 2 * l.toNat < wvecL.length := by omega
  have h2l1_lt : 2 * l.toNat + 1 < wvecL.length := by omega
  have h2l_lt' : (l <<< (1 : Nat)).toNat < wvecL.length := by rw [h2l_eq]; omega
  have h2l1_lt' : ((l <<< (1 : Nat)) + (1 : BitVec 64)).toNat < wvecL.length := by
    rw [h2l1_eq]; omega
  have hbd_cap : off0 + sz0 ≤ c.wcap := by have := hckL.wlen_le; omega
  have hend_bv : end64 = BitVec.ofNat 64 (off0 + sz0) :=
    BitVec.eq_of_toNat_eq (by rw [hend64, bv64_ofNat_toNat (by omega)])
  unfold binsPostPExpr
  cm_steps
  refine wp_loop_inv
    (fun (k, ()) mK =>
      q.toNat ≤ k.toNat ∧ k.toNat ≤ off0 + sz0 ∧
      ∃ wstkK : List (BitVec 32), wstkK.length = c.wcap ∧
        (∀ i, i < off0 ∨ off0 + sz0 ≤ i → wstkK[i]? = wstkL[i]?) ∧
        (∀ i, off0 ≤ i → i < q.toNat → wstkK[i]? = wstkP[i]?) ∧
        (FullMem c { s with core := { kL with wstk := wstkK } } ⋆ R) mK)
    (fun (k, ()) _ => off0 + sz0 - k.toNat)
    (fun Jk hLoopK => ?_) ?_
  · cm_steps
    exact hLoopK (q, ()) mP ⟨Nat.le_refl _, hq_le, wstkP, hwsP, houtP, fun _ _ _ => rfl, hmP⟩
  · rintro Jk ⟨k, ⟨⟩⟩ mK ⟨hqk, hke, wstkK, hwsK, houtK, hpreK, hmK⟩ hLoopK
    cm_split
    · have hk_lt : k.toNat < off0 + sz0 := by
        have h1 : k.toNat < end64.toNat := by c0_bound
        omega
      have hk_ws : k.toNat < wstkK.length := by omega
      have hk1_eq : (k + (1 : BitVec 64)).toNat = k.toNat + 1 := bv64_add1 (by omega)
      cm_steps
      refine hLoopK (k + (1 : BitVec 64), ()) m (by dsimp only; rw [hk1_eq]; omega)
        ⟨by rw [hk1_eq]; omega, by rw [hk1_eq]; omega, wstkK.set k.toNat 0xFFFFFFFF#32,
         by simp [hwsK], fun i hi => by
           rw [List.getElem?_set_ne (by omega)]; exact houtK i hi,
         fun i h1 h2 => by
           rw [List.getElem?_set_ne (by omega)]; exact hpreK i h1 h2,
         compactMem_cast hm rfl⟩
    · have hpreK_ok : CompactPreBinSliceOk ncv.toNat inv F_cur { kL with wstk := wstkK }
          l.toNat (fullWatchOffCore kL l.toNat) (q.toNat - fullWatchOffCore kL l.toNat) :=
        hpreP.relocate (k' := { kL with wstk := wstkK })
          (fun idx hi => hpreK (fullWatchOffCore kL l.toNat + idx) (by omega) (by omega))
      have hl_cv : l.toNat < 2 * kL.cur_vars := by rw [hkL]; exact hold ▸ hl_lt
      have houtK' : ∀ i,
          i < fullWatchOffCore kL l.toNat ∨
            fullWatchOffCore kL l.toNat + fullWatchSizeCore kL l.toNat ≤ i →
          wstkK[i]? = kL.wstk[i]? := fun i hi => by rw [hkL]; exact houtK i hi
      have hfin := compactBins_finish_lit (c := c) (ncv := ncv.toNat) (inv := inv)
        (F_cur := F_cur) hckL hlayL hl_cv hq_ge hq_le hwsK houtK' hpreK_ok
        (wu' := wuL + (BitVec.ofNat 64 (fullWatchOffCore kL l.toNat +
          fullWatchSizeCore kL l.toNat) - q))
        (nb' := kL.num_binary)
      let wvecG : List (BitVec 32) :=
        if q.toNat = off0 then (kL.wvec.set (2 * l.toNat) 0#32).set (2 * l.toNat + 1) 0#32
        else kL.wvec.set (2 * l.toNat + 1) (BitVec.ofNat 32 (q.toNat - off0))
      let wuG : BitVec 64 := wuL + (BitVec.ofNat 64 (off0 + sz0) - q)
      let kG : FullCoreState :=
        { kL with wvec := wvecG, wstk := wstkK, wusable := wuG, num_binary := kL.num_binary }
      have hkG_s : kG = { s.core with wvec := wvecG, wstk := wstkK, wusable := wuG } := by
        dsimp only [kG]; rw [hkL]
      cm_to_group
      refine wp_join_group (ts := [])
        (fun () mG =>
          (FullMem c { s with core := { kL with wvec := wvecG, wstk := wstkK } } ⋆ R) mG)
        ?_ ?_
      · rintro _ ⟨⟩ mG hmG
        cm_steps
        refine hLoop1 (keptP, l + (1 : BitVec 64), ()) m (by dsimp only; rw [hl1_eq]; omega)
          ⟨by rw [hl1_eq]; omega, by rw [hl1_eq]; exact hkept_end,
           wvecG, wstkK, wuG, hfin.1.wvec_len, hwsK, hkG_s ▸ hfin.2.1, fun ol hol => ?_,
           fun ol hlo hol => ?_,
           compactMem_cast hm (by rw [← hkG_s]; dsimp only [kG, wuG]; rw [hkL, hend_bv])⟩
        · rw [hl1_eq] at hol
          by_cases hol_eq : ol = l.toNat
          · subst hol_eq; rw [← hkG_s]; exact hfin.2.2.2.2.2
          · have hol_cv : ol < 2 * kL.cur_vars := by
              rw [hkL]; change ol < 2 * s.core.cur_vars; omega
            obtain ⟨hs_eq, hws_eq⟩ := hfin.2.2.1 ol hol_cv hol_eq
            rw [← hkG_s]
            change CompactPreBinSliceOk ncv.toNat inv F_cur kG ol
              (fullWatchOffCore kG ol) (fullWatchSizeCore kG ol)
            rw [hs_eq]
            exact CompactPreBinSliceOk.relocate (k := kL)
              (fun idx hidx => hws_eq idx hidx) (hpreL ol (by omega))
        · rw [hl1_eq] at hlo
          have hol_cv : ol < 2 * kL.cur_vars := by rw [hkL]; change ol < 2 * s.core.cur_vars; omega
          obtain ⟨hs_eq, hws_eq⟩ := hfin.2.2.1 ol hol_cv (by omega)
          rw [← hkG_s]
          change WatchSliceOk F_cur kG ol (fullWatchOffCore kG ol) (fullWatchSizeCore kG ol)
          rw [hs_eq]
          exact watchSliceOk_relocate (k := kL) (k' := kG)
            (p' := fullWatchOffCore kG ol) (by simp [kG]) (by simp [kG]) (by simp [kG]) hws_eq
            (hwatL ol (by omega) hol)
      · intro Jg hJg
        clear hLoop1 hpreL hwatL hlayL hckL hfin hpreK_ok hLoopK Jk hpreK houtK hpreP hkG_s
        have h2l_st : (l <<< (1 : Nat)).toNat <
            ({ s with core := { kL with wstk := wstkK } } : FullState).core.wvec.length := by
          change (l <<< (1 : Nat)).toNat < kL.wvec.length; rw [hkL]; exact h2l_lt'
        have h2l1_st : ((l <<< (1 : Nat)) + (1 : BitVec 64)).toNat <
            ({ s with core := { kL with wstk := wstkK } } : FullState).core.wvec.length := by
          change ((l <<< (1 : Nat)) + (1 : BitVec 64)).toNat < kL.wvec.length
          rw [hkL]; exact h2l1_lt'
        let kL0 := { kL with wvec := kL.wvec.set (l <<< (1 : Nat)).toNat 0, wstk := wstkK }
        have h2l1_st_set : ((l <<< (1 : Nat)) + (1 : BitVec 64)).toNat <
            ({ s with core := kL0 } : FullState).core.wvec.length := by
          change _ < (kL.wvec.set _ 0).length; rw [List.length_set, hkL]; exact h2l1_lt'
        cm_split
        · have hq_off : q.toNat = off0 := by
            have hbv : q = off64 := by c0_bound
            rw [hbv, hoff64]
          cm_steps
          exact hJg () m (compactMem_cast hm (by
            dsimp only [wvecG]; rw [ite_eq_left hq_off, h2l_eq, h2l1_eq]; rfl))
        · have hq_ne : q.toNat ≠ off0 := by
            have hbv : q ≠ off64 := by c0_bound
            intro heq; apply hbv; apply BitVec.eq_of_toNat_eq; rw [hoff64, heq]
          have hqsub64 : (q - off64).toNat = q.toNat - off0 := by
            rw [BitVec.toNat_sub, hoff64,
              show 2 ^ 64 - off0 + q.toNat = (q.toNat - off0) + 2 ^ 64 by omega,
              Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
          have hq_diff : q.toNat - off0 < 2 ^ 32 := by omega
          have hsub32 : (q - off64).setWidth 32 = BitVec.ofNat 32 (q.toNat - off0) := by
            apply BitVec.eq_of_toNat_eq
            rw [BitVec.toNat_setWidth, hqsub64, bv32_ofNat_toNat hq_diff,
              Nat.mod_eq_of_lt hq_diff]
          cm_steps
          exact hJg () m (compactMem_cast hm (by
            dsimp only [wvecG]; rw [ite_eq_right hq_ne, h2l1_eq, hsub32]))

private theorem full_compact_bins_ploop {Γ : Env} {Q : Post []} {X : XPost}
    {J1 : Cont [i64, i64]} {c : FullCfg} {F_cur : List (List Nat)} {ncv : BitVec 64}
    {inv : List (BitVec 32)} {s : FullState} {kL : FullCoreState} {R : Mem 64 → Prop}
    {old_cv kept l off64 end64 nlits : BitVec 64} {keep_l : Bool} {off0 sz0 : Nat}
    {wvecL wstkL : List (BitVec 32)} {wuL : BitVec 64} {mL : Mem 64}
    (hkL : kL = { s.core with wvec := wvecL, wstk := wstkL, wusable := wuL })
    (hoff_def : off0 = fullWatchOffCore kL l.toNat)
    (hsz_def : sz0 = fullWatchSizeCore kL l.toNat)
    (hcv_le : s.core.cur_vars ≤ c.max_vars) (hv_len : s.core.vals.length = 2 * c.max_vars)
    (hws1_len : s.scratch.work_stk1.length = 2 * c.max_vars)
    (hwc_lt : c.wcap < 2 * 2 ^ 28) (hmax_lt : c.max_vars < 2 * 2 ^ 28)
    (hkl_mul_lt : 2 * c.max_vars * c.wcap < 2 ^ 60)
    (hold : s.core.cur_vars = old_cv.toNat) (_hncv_le : ncv.toNat ≤ old_cv.toNat)
    (hbij : CompactBijOk old_cv.toNat ncv.toNat s.core.vals s.scratch.work_stk1 inv)
    (hckL : FullCoreState.LengthsOk c kL) (hlayL : WatchStackLayout kL)
    (hwvL : wvecL.length = 4 * c.max_vars) (hwsL : wstkL.length = c.wcap)
    (hl_lt : l.toNat < 2 * old_cv.toNat) (hkept_le : kept.toNat ≤ l.toNat * c.wcap)
    (hoff64 : off64.toNat = off0) (hend64 : end64.toNat = off0 + sz0)
    (hnlits : nlits.toNat = 2 * old_cv.toNat)
    (hbd_l : off0 + sz0 ≤ kL.wlen) (hsz_pos : 0 < sz0)
    (hslice_l : WatchSliceOk F_cur kL l.toNat off0 sz0)
    (hpreL : ∀ ol < l.toNat, CompactPreBinSliceOk ncv.toNat inv F_cur kL ol
      (fullWatchOffCore kL ol) (fullWatchSizeCore kL ol))
    (hwatL : ∀ ol, l.toNat ≤ ol → ol < 2 * old_cv.toNat →
      WatchSliceOk F_cur kL ol (fullWatchOffCore kL ol) (fullWatchSizeCore kL ol))
    (hmL : (FullMem c { s with core := kL } ⋆ R) mL)
    (hLoop1 : ∀ (ys : Tup Val [i64, i64]) (m' : Mem 64),
      2 * old_cv.toNat - ys.2.1.toNat < 2 * old_cv.toNat - l.toNat →
      (ys.2.1.toNat ≤ 2 * old_cv.toNat ∧ ys.1.toNat ≤ ys.2.1.toNat * c.wcap ∧
        ∃ (wvecL wstkL : List (BitVec 32)) (wuL : BitVec 64),
          wvecL.length = 4 * c.max_vars ∧ wstkL.length = c.wcap ∧
          let k1 : FullCoreState := { s.core with wvec := wvecL, wstk := wstkL, wusable := wuL }
          WatchStackLayout k1 ∧
          (∀ ol < ys.2.1.toNat, CompactPreBinSliceOk ncv.toNat inv F_cur k1 ol
            (fullWatchOffCore k1 ol) (fullWatchSizeCore k1 ol)) ∧
          (∀ ol, ys.2.1.toNat ≤ ol → ol < 2 * old_cv.toNat →
            WatchSliceOk F_cur k1 ol (fullWatchOffCore k1 ol) (fullWatchSizeCore k1 ol)) ∧
          (FullMem c { s with core := k1 } ⋆ R) m') →
      J1 ys m') :
    wp Γ Q X (binsPLoopExpr c.hdr kept l off64 end64 c.pWvec c.pWstk c.pWorkStk1 c.pVals nlits
      keep_l J1) mL := by
  have hbd_cap : off0 + sz0 ≤ c.wcap := by have := hckL.wlen_le; omega
  have hkL_wstk : ({ kL with wstk := wstkL } : FullCoreState) = kL := by rw [hkL]
  unfold binsPLoopExpr
  refine wp_loop_inv
    (fun (keptP, p, q, ()) mP =>
      off0 ≤ q.toNat ∧ q.toNat ≤ p.toNat ∧ p.toNat ≤ off0 + sz0 ∧
      keptP.toNat ≤ l.toNat * c.wcap + (q.toNat - off0) ∧
      ∃ wstkP : List (BitVec 32), wstkP.length = c.wcap ∧
        (∀ i, (i < off0 ∨ p.toNat ≤ i) → wstkP[i]? = wstkL[i]?) ∧
        CompactPreBinSliceOk ncv.toNat inv F_cur { kL with wstk := wstkP } l.toNat
          off0 (q.toNat - off0) ∧
        WatchSliceOk F_cur { kL with wstk := wstkP } l.toNat
          p.toNat (off0 + sz0 - p.toNat) ∧
        (FullMem c { s with core := { kL with wstk := wstkP } } ⋆ R) mP)
    (fun (_, p, _, ()) _ => off0 + sz0 - p.toNat)
    (fun Jp hLoopP => ?_) ?_
  · cm_steps
    refine hLoopP (kept, off64, off64, ()) mL
      ⟨by rw [hoff64]; exact Nat.le_refl _, by exact Nat.le_refl _,
       by rw [hoff64]; omega, by rw [hoff64, Nat.sub_self, Nat.add_zero]; exact hkept_le,
       wstkL, hwsL, fun _ _ => rfl, by rw [hoff64, Nat.sub_self]; exact .empty,
       by rw [hoff64, Nat.add_sub_cancel_left, hkL_wstk]; exact hslice_l,
       by rw [hkL_wstk]; exact hmL⟩
  · rintro Jp ⟨keptP, p, q, ⟨⟩⟩ mP
      ⟨hq_ge, hqp, hpe, hkp_le, wstkP, hwsP, houtP, hpreP, hremP, hmP⟩ hLoopP
    have hkp_bd : keptP.toNat ≤ (l.toNat + 1) * c.wcap := by
      have hq1 : q.toNat - off0 ≤ sz0 := by omega
      have hq2 : sz0 ≤ c.wcap := by omega
      rw [Nat.add_mul, Nat.one_mul]; omega
    cm_split
    · clear hLoop1 J1 hpreL hwatL hlayL hckL
      have hp_lt : p.toNat < off0 + sz0 := by
        have h1 : p.toNat < end64.toNat := by c0_bound
        omega
      have hp_wstk : p.toNat < wstkP.length := by omega
      let w0 := wstkP[p.toNat]'hp_wstk
      have hw0_some : wstkP[p.toNat]? = some w0 := List.getElem?_eq_getElem hp_wstk
      have hstep := WatchSliceOk_step hremP (by omega) hw0_some
      cm_split
      · have hbin0 : (w0 &&& 0x80000000#32) ≠ 0#32 := by c0_bound
        have ⟨_, _, hent, htail⟩ := hstep.1 hbin0
        have hrem' : WatchSliceOk F_cur { kL with wstk := wstkP } l.toNat
            (p.toNat + 1) (off0 + sz0 - (p.toNat + 1)) := by
          simpa [Nat.sub_sub] using htail
        have hp1_eq : (p + (1 : BitVec 64)).toNat = p.toNat + 1 := bv64_add1 (by omega)
        let ot := w0 &&& 0x7FFFFFFF#32
        cm_split
        · cm_split
          · have hot_lt : ot.toNat < 2 * old_cv.toNat := by
              have h1 : ot.toNat < nlits.toNat := by dsimp only [ot, w0]; c0_bound
              omega
            have hot_vals : ot.toNat < s.core.vals.length := by omega
            have hot_vals_64 :
                (((wstkP[p.toNat]'hp_wstk &&& 0x7FFFFFFF#32)).setWidth 64).toNat <
                  ({ s with core := { kL with wstk := wstkP } } : FullState).core.vals.length := by
              change (ot.setWidth 64).toNat < kL.vals.length
              rw [hkL, zext_toNat _ (by decide)]; exact hot_vals
            have hot_ws1 : (ot >>> 1#32).toNat < s.scratch.work_stk1.length := by
              rw [bv32_shr1_toNat]; omega
            have hot_ws1_64 :
                ((ot >>> 1#32).setWidth 64).toNat < s.scratch.work_stk1.length := by
              rw [zext_toNat _ (by decide), bv32_shr1_toNat]; omega
            cm_split
            · have hneq : (s.scratch.work_stk1[((ot >>> 1#32).setWidth 64).toNat]'hot_ws1_64) ≠
                  0xFFFFFFFF#32 := by dsimp only [ot, w0]; c0_bound
              have hmap_ot : s.scratch.work_stk1[ot.toNat / 2]? ≠ some 0xFFFFFFFF#32 := by
                intro heq
                rw [List.getElem?_eq_getElem
                  (by omega : ot.toNat / 2 < s.scratch.work_stk1.length)] at heq
                have hidx : ((ot >>> 1#32).setWidth 64).toNat = ot.toNat / 2 := by
                  rw [zext_toNat _ (by decide), bv32_shr1_toNat]
                simp only [hidx] at hneq
                exact hneq (Option.some.inj heq)
              cm_split
              · rcases hbij.map_ok (ot.toNat / 2) (by omega) with
                    hff | ⟨nv', hnv', _, _, hm_ot, hi_ot⟩
                · exact absurd hff hmap_ot
                · have hnv'_30 : nv' < 2 ^ 30 := by omega
                  have hpack := bv32_lit_pack hnv'_30 ot
                  have hnot_lt : ((BitVec.ofNat 32 nv' <<< 1#32) ||| (ot &&& 1#32)).toNat <
                      0x7FFFFFFF := by rw [hpack]; omega
                  have hbw := bv32_bin_word_props hnot_lt
                  let wnew := (((BitVec.ofNat 32 nv' <<< 1#32) ||| (ot &&& 1#32)) &&&
                    0x7FFFFFFF#32) ||| 0x80000000#32
                  have hq_wstk : q.toNat < wstkP.length := by omega
                  have hq1_eq : (q + (1 : BitVec 64)).toNat = q.toNat + 1 := bv64_add1 (by omega)
                  have hkp1_eq : (keptP + (1 : BitVec 64)).toNat = keptP.toNat + 1 := by
                    have : keptP.toNat + 1 < 2 ^ 64 := by
                      have : (l.toNat + 1) * c.wcap ≤ 2 * c.max_vars * c.wcap :=
                        Nat.mul_le_mul_right _ (by omega)
                      omega
                    exact bv64_add1 this
                  let wstkP' := wstkP.set q.toNat wnew
                  have hun : compactUnmapLit inv (wnew &&& 0x7FFFFFFF#32).toNat = ot.toNat := by
                    rw [hbw.2.2, hpack]; apply compactUnmapLit_pair
                    rw [hi_ot, Option.getD_some, bv32_ofNat_toNat (by omega)]
                  have hpre' : CompactPreBinSliceOk ncv.toNat inv F_cur
                      { kL with wstk := wstkP' } l.toNat off0 (q.toNat + 1 - off0) := by
                    rw [show q.toNat + 1 - off0 = (q.toNat - off0) + 1 by omega]
                    exact hpreP.append_bin
                      (fun idx hi => by dsimp only [wstkP']; rw [List.getElem?_set_ne (by omega)])
                      (by dsimp only [wstkP']
                          rw [show off0 + (q.toNat - off0) = q.toNat by omega,
                            List.getElem?_set_self hq_wstk])
                      hbw.1 hbw.2.1 (by rw [hbw.2.2, hpack]; omega) (hun ▸ hent)
                  have hrem_set : WatchSliceOk F_cur { kL with wstk := wstkP' } l.toNat
                      (p.toNat + 1) (off0 + sz0 - (p.toNat + 1)) := by
                    refine watchSliceOk_relocate (k := { kL with wstk := wstkP })
                      (p := p.toNat + 1) (p' := p.toNat + 1) rfl rfl rfl ?_ hrem'
                    intro idx _; dsimp only [wstkP']; rw [List.getElem?_set_ne (by omega)]
                  cm_steps
                  refine hLoopP (keptP + (1 : BitVec 64), p + (1 : BitVec 64),
                      q + (1 : BitVec 64), ()) m (by dsimp only; rw [hp1_eq]; omega)
                    ⟨by rw [hq1_eq]; omega, by rw [hq1_eq, hp1_eq]; omega,
                     by rw [hp1_eq]; omega, by rw [hkp1_eq, hq1_eq]; omega,
                     wstkP', by simp [wstkP', hwsP], fun i hi => ?_,
                     by rw [hq1_eq]; exact hpre', by rw [hp1_eq]; exact hrem_set,
                     compactMem_cast hm (by
                       dsimp only [wstkP', wnew, ot]
                       refine congrArg (fun x : BitVec 32 =>
                         ({ core := { kL with wstk := (wstkP.set q.toNat
                              (((x <<< 1#32 ||| (w0 &&& 0x7FFFFFFF#32) &&& 1#32) &&&
                                0x7FFFFFFF#32) ||| 0x80000000#32)) },
                            scratch := s.scratch } : FullState)) ?_
                       rw [← Option.some_inj]
                       change some (s.scratch.work_stk1[((ot >>> 1#32).setWidth 64).toNat]'
                         hot_ws1_64) = some (BitVec.ofNat 32 nv')
                       rw [← List.getElem?_eq_getElem hot_ws1_64, zext_toNat _ (by decide),
                         bv32_shr1_toNat]
                       exact hm_ot)⟩
                  dsimp only [wstkP']
                  rw [List.getElem?_set_ne (by rw [hp1_eq] at hi; omega)]
                  exact houtP i
                    (hi.elim Or.inl fun h2 => Or.inr (by rw [hp1_eq] at h2; omega))
              · cm_steps
                refine hLoopP (keptP, p + (1 : BitVec 64), q, ()) mP
                  (by dsimp only; rw [hp1_eq]; omega)
                  ⟨hq_ge, by rw [hp1_eq]; omega, by rw [hp1_eq]; omega, hkp_le,
                   wstkP, hwsP, fun i hi => houtP i
                     (hi.elim Or.inl fun h2 => Or.inr (by rw [hp1_eq] at h2; omega)),
                   hpreP, by rw [hp1_eq]; exact hrem', hmP⟩
            · cm_steps
              refine hLoopP (keptP, p + (1 : BitVec 64), q, ()) mP
                (by dsimp only; rw [hp1_eq]; omega)
                ⟨hq_ge, by rw [hp1_eq]; omega, by rw [hp1_eq]; omega, hkp_le,
                 wstkP, hwsP, fun i hi => houtP i
                   (hi.elim Or.inl fun h2 => Or.inr (by rw [hp1_eq] at h2; omega)),
                 hpreP, by rw [hp1_eq]; exact hrem', hmP⟩
          · cm_steps
            refine hLoopP (keptP, p + (1 : BitVec 64), q, ()) mP
              (by dsimp only; rw [hp1_eq]; omega)
              ⟨hq_ge, by rw [hp1_eq]; omega, by rw [hp1_eq]; omega, hkp_le,
               wstkP, hwsP, fun i hi => houtP i
                 (hi.elim Or.inl fun h2 => Or.inr (by rw [hp1_eq] at h2; omega)),
               hpreP, by rw [hp1_eq]; exact hrem', hmP⟩
        · cm_steps
          refine hLoopP (keptP, p + (1 : BitVec 64), q, ()) mP
            (by dsimp only; rw [hp1_eq]; omega)
            ⟨hq_ge, by rw [hp1_eq]; omega, by rw [hp1_eq]; omega, hkp_le,
             wstkP, hwsP, fun i hi => houtP i
               (hi.elim Or.inl fun h2 => Or.inr (by rw [hp1_eq] at h2; omega)),
             hpreP, by rw [hp1_eq]; exact hrem', hmP⟩
      · have hlg0 : (w0 &&& 0x80000000#32) = 0#32 := by c0_bound
        have ⟨_, hrem'⟩ := hstep.2 hlg0
        have hp2_eq : (p + (2 : BitVec 64)).toNat = p.toNat + 2 := bv64_add2 (by omega)
        have hrem_p2 : WatchSliceOk F_cur { kL with wstk := wstkP } l.toNat
            (p.toNat + 2) (off0 + sz0 - (p.toNat + 2)) := by
          simpa [Nat.sub_sub] using hrem'
        cm_steps
        apply (‹∀ (xs : Tup Val [i64, i64, i64]) (m' : Mem 64), wp _ _ _ _ m' → _›)
        cm_steps
        refine hLoopP (keptP, p + (2 : BitVec 64), q, ()) mP (by dsimp only; rw [hp2_eq]; omega)
          ⟨hq_ge, by rw [hp2_eq]; omega, by rw [hp2_eq]; omega, hkp_le,
           wstkP, hwsP, fun i hi => houtP i
             (hi.elim Or.inl fun h2 => Or.inr (by rw [hp2_eq] at h2; omega)),
           hpreP, by rw [hp2_eq]; exact hrem_p2, hmP⟩
    · have hp_eq : p.toNat = off0 + sz0 := by
        have h1 : ¬ p.toNat < end64.toNat := by c0_bound
        omega
      rw [hp_eq] at houtP
      clear hLoopP Jp
      exact full_compact_bins_post_p hkL hoff_def hsz_def hcv_le hwc_lt hmax_lt hold hckL hlayL
        hwvL hl_lt hoff64 hend64 hbd_l hsz_pos hq_ge (by omega) hkp_bd hwsP houtP hpreP hpreL
        hwatL hmP hLoop1

private theorem full_compact_bins_tail {Γ : Env} {Q : Post []} {X : XPost}
    {c : FullCfg} {F_cur : List (List Nat)} {ncv : BitVec 64}
    {inv : List (BitVec 32)} {s : FullState} {kL : FullCoreState} {R : Mem 64 → Prop}
    {old_cv kept : BitVec 64} {wvecL wstkL : List (BitVec 32)} {wuL : BitVec 64} {mL : Mem 64}
    (hkL : kL = { s.core with wvec := wvecL, wstk := wstkL, wusable := wuL })
    (hlen : FullState.LengthsOk c s) (hcv_le : s.core.cur_vars ≤ c.max_vars)
    (hws1_len : s.scratch.work_stk1.length = 2 * c.max_vars)
    (hmax_lt : c.max_vars < 2 * 2 ^ 28) (hold : s.core.cur_vars = old_cv.toNat)
    (hncv_le : ncv.toNat ≤ old_cv.toNat)
    (hbij : CompactBijOk old_cv.toNat ncv.toNat s.core.vals s.scratch.work_stk1 inv)
    (hckL : FullCoreState.LengthsOk c kL) (hlayL : WatchStackLayout kL)
    (hwvL : wvecL.length = 4 * c.max_vars) (_hwsL : wstkL.length = c.wcap)
    (hpreL : ∀ ol < 2 * old_cv.toNat, CompactPreBinSliceOk ncv.toNat inv F_cur kL ol
      (fullWatchOffCore kL ol) (fullWatchSizeCore kL ol))
    (hmL : (FullMem c { s with core := kL } ⋆ R) mL)
    (hQ : ∀ (wvec' wstk' : List (BitVec 32)) (wusable' num_bin' : BitVec 64) (m' : Mem 64),
      let k' : FullCoreState :=
        { s.core with wvec := wvec', wstk := wstk', wusable := wusable', num_binary := num_bin' }
      FullState.LengthsOk c { s with core := k' } →
      CompactUnmapBinsOk ncv.toNat inv F_cur k' →
      (FullMem c { s with core := k' } ⋆ R) m' → Q () m') :
    wp Γ Q X (binsTailExpr c.hdr old_cv ncv kept c.pWorkStk1 c.pWvec) mL := by
  let k1 : FullCoreState := { kL with num_binary := kept >>> (1 : Nat) }
  have hk1_mem : ({ s with core := k1 } : FullState) =
      { s with core := { kL with num_binary := kept >>> (1 : Nat) } } := rfl
  unfold binsTailExpr
  cm_steps
  refine wp_loop_inv
    (fun (v, ()) m2 =>
      v.toNat ≤ old_cv.toNat ∧
      ∃ wvec2 : List (BitVec 32), wvec2.length = 4 * c.max_vars ∧
        (∀ w, v.toNat ≤ w → w < old_cv.toNat → ∀ d < 4, wvec2[4 * w + d]? = wvecL[4 * w + d]?) ∧
        (∀ nv < ncv.toNat, ∀ ov, (inv[nv]?.getD 0#32).toNat = ov → ov < v.toNat →
          ∀ d < 4, wvec2[4 * nv + d]? = wvecL[4 * ov + d]?) ∧
        (FullMem c { s with core := { k1 with wvec := wvec2 } } ⋆ R) m2)
    (fun (v, ()) _ => old_cv.toNat - v.toNat)
    (fun J2 hLoop2 => ?_) ?_
  · cm_steps
    exact hLoop2 (0#64, ()) m ⟨Nat.zero_le _, wvecL, hwvL, fun _ _ _ _ _ => rfl,
      fun _ _ _ _ hlt => by simp at hlt, compactMem_cast hm (by dsimp only [k1]; rw [hkL])⟩
  · rintro J2 ⟨v, ⟨⟩⟩ m2 ⟨hv_le, wvec2, hwv2, hhi2, hmap2, hm2⟩ hLoop2
    cm_split
    · have hv_lt : v.toNat < old_cv.toNat := by c0_bound
      have hv1_eq : (v + (1 : BitVec 64)).toNat = v.toNat + 1 := bv64_add1 (by omega)
      have hv_ws1 : v.toNat < s.scratch.work_stk1.length := by omega
      cm_split
      · have hneq_ff : (s.scratch.work_stk1[v.toNat]'hv_ws1) ≠ 0xFFFFFFFF#32 := by c0_bound
        rcases hbij.map_ok v.toNat hv_lt with hff | ⟨nv, hnv_lt, hnv_le, _, hm_v, hi_v⟩
        · rw [List.getElem?_eq_getElem hv_ws1] at hff
          exact absurd (Option.some.inj hff) hneq_ff
        · have hnv32 : (s.scratch.work_stk1[v.toNat]'hv_ws1) = BitVec.ofNat 32 nv := by
            rw [List.getElem?_eq_getElem hv_ws1] at hm_v; exact Option.some.inj hm_v
          have hnv_to : (s.scratch.work_stk1[v.toNat]'hv_ws1).toNat = nv := by
            rw [hnv32, bv32_ofNat_toNat (by omega)]
          cm_split
          · have hnv_lt_v : nv < v.toNat := by
              have hne_v : (s.scratch.work_stk1[v.toNat]'hv_ws1).setWidth 64 ≠ v := by c0_bound
              refine Nat.lt_of_le_of_ne hnv_le fun he => ?_
              apply hne_v; apply BitVec.eq_of_toNat_eq
              rw [zext_toNat _ (by decide), hnv_to]; exact he
            have h4v_eq : (v <<< (2 : Nat)).toNat = 4 * v.toNat := bv64_shl2_toNat (by omega)
            have h4v1 : ((v <<< (2 : Nat)) + (1 : BitVec 64)).toNat = 4 * v.toNat + 1 := by
              rw [bv64_add1 (by rw [h4v_eq]; omega), h4v_eq]
            have h4v2 : ((v <<< (2 : Nat)) + (2 : BitVec 64)).toNat = 4 * v.toNat + 2 := by
              rw [bv64_add2 (by rw [h4v_eq]; omega), h4v_eq]
            have h4v3 : ((v <<< (2 : Nat)) + (3 : BitVec 64)).toNat = 4 * v.toNat + 3 := by
              rw [bv64_add3 (by rw [h4v_eq]; omega), h4v_eq]
            have h4nv_eq :
                ((s.scratch.work_stk1[v.toNat]'hv_ws1).setWidth 64 <<< (2 : Nat)).toNat =
                4 * nv := by
              rw [bv64_shl2_toNat (by rw [zext_toNat _ (by decide), hnv_to]; omega),
                zext_toNat _ (by decide), hnv_to]
            have h4nv1 :
                (((s.scratch.work_stk1[v.toNat]'hv_ws1).setWidth 64 <<< (2 : Nat)) +
                  (1 : BitVec 64)).toNat = 4 * nv + 1 := by
              rw [bv64_add1 (by rw [h4nv_eq]; omega), h4nv_eq]
            have h4nv2 :
                (((s.scratch.work_stk1[v.toNat]'hv_ws1).setWidth 64 <<< (2 : Nat)) +
                  (2 : BitVec 64)).toNat = 4 * nv + 2 := by
              rw [bv64_add2 (by rw [h4nv_eq]; omega), h4nv_eq]
            have h4nv3 :
                (((s.scratch.work_stk1[v.toNat]'hv_ws1).setWidth 64 <<< (2 : Nat)) +
                  (3 : BitVec 64)).toNat = 4 * nv + 3 := by
              rw [bv64_add3 (by rw [h4nv_eq]; omega), h4nv_eq]
            have h4v_bds : 4 * v.toNat < wvec2.length ∧ 4 * v.toNat + 1 < wvec2.length ∧
                4 * v.toNat + 2 < wvec2.length ∧ 4 * v.toNat + 3 < wvec2.length := by omega
            have h4nv_bds : 4 * nv < wvec2.length ∧ 4 * nv + 1 < wvec2.length ∧
                4 * nv + 2 < wvec2.length ∧ 4 * nv + 3 < wvec2.length := by omega
            cm_steps
            try (apply (‹∀ (xs : Tup Val []) (m' : Mem 64), wp _ _ _ _ m' → _›); cm_steps)
            let w0 := wvec2[4 * v.toNat]'h4v_bds.1
            let w1 := wvec2[4 * v.toNat + 1]'h4v_bds.2.1
            let w2 := wvec2[4 * v.toNat + 2]'h4v_bds.2.2.1
            let w3 := wvec2[4 * v.toNat + 3]'h4v_bds.2.2.2
            let wvec2' := (((wvec2.set (4 * nv) w0).set (4 * nv + 1) w1).set
              (4 * nv + 2) w2).set (4 * nv + 3) w3
            obtain ⟨hwv2', hhi2', hmap2'⟩ :=
              compactBins_loop2_step hbij hwv2 hv_lt (by omega) hnv_lt hnv_lt_v hi_v hhi2
                hmap2 h4v_bds.1 h4v_bds.2.1 h4v_bds.2.2.1 h4v_bds.2.2.2
            refine hLoop2 (v + (1 : BitVec 64), ()) m (by dsimp only; rw [hv1_eq]; omega)
              ⟨by rw [hv1_eq]; omega, wvec2', hwv2',
               fun w hw1 hw2 d hd => hhi2' w (by rw [hv1_eq] at hw1; exact hw1) hw2 d hd,
               fun nv' hnv' ov hov1 hov2 d hd =>
                 hmap2' nv' hnv' ov hov1 (by rw [hv1_eq] at hov2; exact hov2) d hd,
               compactMem_cast hm (by
                 dsimp only [wvec2', w0, w1, w2, w3]
                 simp only [h4v_eq, h4v1, h4v2, h4v3, h4nv_eq, h4nv1, h4nv2, h4nv3,
                   List.getElem_set_ne (by omega : 4 * nv ≠ 4 * v.toNat + 1),
                   List.getElem_set_ne (by omega : 4 * nv + 1 ≠ 4 * v.toNat + 2),
                   List.getElem_set_ne (by omega : 4 * nv ≠ 4 * v.toNat + 2),
                   List.getElem_set_ne (by omega : 4 * nv + 2 ≠ 4 * v.toNat + 3),
                   List.getElem_set_ne (by omega : 4 * nv + 1 ≠ 4 * v.toNat + 3),
                   List.getElem_set_ne (by omega : 4 * nv ≠ 4 * v.toNat + 3)])⟩
          · have hnv_eq_v : nv = v.toNat := by
              have h0 : (s.scratch.work_stk1[v.toNat]'hv_ws1).setWidth 64 = v := by c0_bound
              have ht := congrArg BitVec.toNat h0
              rwa [zext_toNat _ (by decide), hnv_to] at ht
            cm_steps
            try (apply (‹∀ (xs : Tup Val []) (m' : Mem 64), wp _ _ _ _ m' → _›); cm_steps)
            refine hLoop2 (v + (1 : BitVec 64), ()) m2 (by dsimp only; rw [hv1_eq]; omega)
              ⟨by rw [hv1_eq]; omega, wvec2, hwv2,
               fun w hw1 hw2 d hd => hhi2 w (by omega) hw2 d hd,
               fun nv' hnv' ov hov1 hov2 d hd => ?_, hm2⟩
            rw [hv1_eq] at hov2
            by_cases heq : ov = v.toNat
            · subst heq
              have hnv_eq : nv' = nv := hbij.inv_inj (nv1 := nv') (nv2 := nv) hnv' hnv_lt
                (by rw [hov1, hi_v, Option.getD_some, bv32_ofNat_toNat (by omega)])
              rw [hnv_eq, hnv_eq_v]; exact hhi2 v.toNat (Nat.le_refl _) hv_lt d hd
            · exact hmap2 nv' hnv' ov hov1 (by omega) d hd
      · have heq_ff : (s.scratch.work_stk1[v.toNat]'hv_ws1) = 0xFFFFFFFF#32 := by c0_bound
        cm_steps
        try (apply (‹∀ (xs : Tup Val []) (m' : Mem 64), wp _ _ _ _ m' → _›); cm_steps)
        refine hLoop2 (v + (1 : BitVec 64), ()) m2 (by dsimp only; rw [hv1_eq]; omega)
          ⟨by rw [hv1_eq]; omega, wvec2, hwv2, fun w hw1 hw2 d hd => hhi2 w (by omega) hw2 d hd,
           fun nv' hnv' ov hov1 hov2 d hd => ?_, hm2⟩
        rw [hv1_eq] at hov2
        by_cases heq : ov = v.toNat
        · subst heq
          obtain ⟨ov', _, _, _, hi_v, hm_v⟩ := hbij.inv_ok nv' hnv'
          have hov'_eq : ov' = v.toNat := by
            rw [hi_v, Option.getD_some, bv32_ofNat_toNat (by omega)] at hov1; exact hov1
          subst hov'_eq
          rw [List.getElem?_eq_getElem hv_ws1, heq_ff] at hm_v
          have hto := congrArg BitVec.toNat (Option.some.inj hm_v)
          rw [show (0xFFFFFFFF#32 : BitVec 32).toNat = 0xFFFFFFFF from rfl,
            bv32_ofNat_toNat (by omega)] at hto
          have := hbij.old_cv_lt; omega
        · exact hmap2 nv' hnv' ov hov1 (by omega) d hd
    · have hv_eq : v.toNat = old_cv.toNat := by c0_bound
      rw [hv_eq] at hmap2
      clear hLoop2 J2
      cm_steps
      refine wp_loop_inv
        (fun (v3, ()) m3 =>
          ncv.toNat ≤ v3.toNat ∧ v3.toNat ≤ old_cv.toNat ∧
          ∃ wvec3 : List (BitVec 32), wvec3.length = 4 * c.max_vars ∧
            (∀ w, ncv.toNat ≤ w → w < v3.toNat → ∀ d < 4, wvec3[4 * w + d]? = some 0#32) ∧
            (∀ nv < ncv.toNat, ∀ d < 4, wvec3[4 * nv + d]? = wvec2[4 * nv + d]?) ∧
            (FullMem c { s with core := { k1 with wvec := wvec3 } } ⋆ R) m3)
        (fun (v3, ()) _ => old_cv.toNat - v3.toNat)
        (fun J3 hLoop3 => ?_) ?_
      · cm_steps; exact hLoop3 (ncv, ()) m2 ⟨Nat.le_refl _, hncv_le, wvec2, hwv2,
          fun _ h1 h2 => by omega, fun _ _ _ _ => rfl, hm2⟩
      · rintro J3 ⟨v3, ⟨⟩⟩ m3 ⟨hv3_ge, hv3_le, wvec3, hwv3, hzero3, hpres3, hm3⟩ hLoop3
        cm_split
        · have hv3_lt : v3.toNat < old_cv.toNat := by c0_bound
          have hv3_1_eq : (v3 + (1 : BitVec 64)).toNat = v3.toNat + 1 := bv64_add1 (by omega)
          have h4v3_eq : (v3 <<< (2 : Nat)).toNat = 4 * v3.toNat := bv64_shl2_toNat (by omega)
          have h4v3_1 : ((v3 <<< (2 : Nat)) + (1 : BitVec 64)).toNat = 4 * v3.toNat + 1 := by
            rw [bv64_add1 (by rw [h4v3_eq]; omega), h4v3_eq]
          have h4v3_2 : ((v3 <<< (2 : Nat)) + (2 : BitVec 64)).toNat = 4 * v3.toNat + 2 := by
            rw [bv64_add2 (by rw [h4v3_eq]; omega), h4v3_eq]
          have h4v3_3 : ((v3 <<< (2 : Nat)) + (3 : BitVec 64)).toNat = 4 * v3.toNat + 3 := by
            rw [bv64_add3 (by rw [h4v3_eq]; omega), h4v3_eq]
          let wvec3' := (((wvec3.set (4 * v3.toNat) 0#32).set (4 * v3.toNat + 1) 0#32).set
            (4 * v3.toNat + 2) 0#32).set (4 * v3.toNat + 3) 0#32
          obtain ⟨hwv3', hzero3', hpres3'⟩ :=
            compactBins_loop3_step hwv3 hv3_ge hv3_lt (by omega) hzero3 hpres3
          cm_steps
          refine hLoop3 (v3 + (1 : BitVec 64), ()) m (by dsimp only; rw [hv3_1_eq]; omega)
            ⟨by rw [hv3_1_eq]; omega, by rw [hv3_1_eq]; omega, wvec3', hwv3',
             fun w hw1 hw2 d hd => hzero3' w hw1 (by rw [hv3_1_eq] at hw2; exact hw2) d hd,
             hpres3',
             compactMem_cast hm (by
               dsimp only [wvec3']; simp only [h4v3_eq, h4v3_1, h4v3_2, h4v3_3]; rfl)⟩
        · have hv3_eq : v3.toNat = old_cv.toNat := by c0_bound
          rw [hv3_eq] at hzero3
          cm_steps
          let k3 : FullCoreState := { k1 with wvec := wvec3 }
          obtain ⟨hhi3, hmap3⟩ :=
            compactBins_loop3_done (kL := kL) (k3 := k3) rfl (by simp [hkL]) hzero3 hpres3 hmap2
          have hck3 : FullState.LengthsOk c { s with core := k3 } :=
            ⟨{ hckL with wvec_len := hwv3 }, hlen.scratch_ok⟩
          have hpre1 : ∀ ol < 2 * old_cv.toNat,
              CompactPreBinSliceOk ncv.toNat inv F_cur k1 ol
                (fullWatchOffCore k1 ol) (fullWatchSizeCore k1 ol) := fun ol hol => by
            simpa only [fullWatchOffCore, fullWatchSizeCore] using
              (hpreL ol hol).relocate (k := kL) (k' := k1) (fun _ _ => rfl)
          have hcv1 : k1.cur_vars = old_cv.toNat := by dsimp only [k1]; rw [hkL]; exact hold
          have hcv3 : k3.cur_vars = old_cv.toNat := by dsimp only [k3, k1]; rw [hkL]; exact hold
          have hlay1 : WatchStackLayout k1 := by
            refine ⟨fun j hj => ?_, fun j hj hp => ?_,
              fun j1 j2 h1 h2 hne hp1 hp2 => ?_, fun j hj idx hi => ?_⟩ <;>
              dsimp only [fullWatchOffCore, fullWatchSizeCore, k1] at *
            · exact hlayL.bounds j hj
            · exact hlayL.pos_off j hj hp
            · exact hlayL.disjoint j1 j2 h1 h2 hne hp1 hp2
            · exact hlayL.no_sentinel j hj idx hi
          have hbin3 := compactBins_finalize (c := c) (k1 := k1) (k2 := k3)
            hcv1 hcv3 hbij hlay1 hwv3 rfl rfl hhi3 hmap3 hpre1
          let nb3 := kept >>> (1 : Nat)
          have hk3_eq : k3 = { s.core with
              wvec := wvec3, wstk := wstkL, wusable := wuL, num_binary := nb3 } := by
            simp only [k3, k1, hkL, nb3]
          rw [hk3_eq] at hck3 hbin3
          exact hQ wvec3 wstkL wuL (kept >>> (1 : Nat)) m3 hck3 hbin3
            (compactMem_cast hm3 (by simp only [k1, hkL]))

theorem full_compact_bins_wp (Γ : Env) :
    ∀ a m Q X, fullCompactBinsSpec a m Q X → Func.wp Γ full_compact_bins_body a m Q X := by
  rintro ⟨h, old_cv, ncv, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hsp, hold, hncv_le, hbij, hm, hQ⟩
  have hlen := hsp.1
  have hw := hsp.2.1
  have hdm := hsp.2.2.2.2.2
  have hwat : WatchesInv F_cur s.core := by
    have hm' := hw.watches; unfold ModeWatchesInv at hm'; rwa [ite_eq_left hdm] at hm'
  have hck0 := hlen.core_ok
  have hcv_le := hck0.cur_vars_le
  have hv_len := hck0.vals_len
  have hws1_len := hlen.scratch_ok.work_stk1_len
  have hwc_lt : c.wcap < 2 * 2 ^ 28 := c.hwcap
  have hmax_lt : c.max_vars < 2 * 2 ^ 28 := c.hmaxv
  have hnlits_eq : (old_cv <<< (1 : Nat)).toNat = 2 * old_cv.toNat := bv64_shl1_toNat (by omega)
  have hov_lt32 : old_cv.toNat < 0x7FFFFFFF := hbij.old_cv_lt
  let inv := s.scratch.work_stk2
  cm_steps
  refine wp_loop_inv
    (fun (kept, l, ()) mL =>
      l.toNat ≤ 2 * old_cv.toNat ∧ kept.toNat ≤ l.toNat * c.wcap ∧
      ∃ (wvecL wstkL : List (BitVec 32)) (wuL : BitVec 64),
        wvecL.length = 4 * c.max_vars ∧ wstkL.length = c.wcap ∧
        let kL : FullCoreState := { s.core with wvec := wvecL, wstk := wstkL, wusable := wuL }
        WatchStackLayout kL ∧
        (∀ ol < l.toNat,
          CompactPreBinSliceOk ncv.toNat inv F_cur kL ol
            (fullWatchOffCore kL ol) (fullWatchSizeCore kL ol)) ∧
        (∀ ol, l.toNat ≤ ol → ol < 2 * old_cv.toNat →
          WatchSliceOk F_cur kL ol (fullWatchOffCore kL ol) (fullWatchSizeCore kL ol)) ∧
        (FullMem c { s with core := kL } ⋆ R) mL)
    (fun (_, l, ()) _ => 2 * old_cv.toNat - l.toNat)
    (fun J1 hLoop1 => ?_) ?_
  · cm_steps
    refine hLoop1 (0#64, 0#64, ()) m ⟨Nat.zero_le _, Nat.zero_le _, s.core.wvec, s.core.wstk,
      s.core.wusable, hck0.wvec_len, hck0.wstk_len_arr, hwat.layout,
      fun _ h => by simp at h, fun ol _ hol => hwat.slices ol (hold ▸ hol), hm⟩
  · rintro J1 ⟨kept, l, ⟨⟩⟩ mL
      ⟨hl_le, hkept_le, wvecL, wstkL, wuL, hwvL, hwsL, hlayL, hpreL, hwatL, hmL⟩ hLoop1
    let kL : FullCoreState := { s.core with wvec := wvecL, wstk := wstkL, wusable := wuL }
    have hckL : FullCoreState.LengthsOk c kL :=
      { hck0 with wvec_len := hwvL, wstk_len_arr := hwsL }
    have hkl_mul_lt : 2 * c.max_vars * c.wcap < 2 ^ 60 := by
      have h1 : 2 * c.max_vars ≤ 2 ^ 30 := by omega
      have h2 : c.wcap < 2 ^ 29 := by omega
      have : 2 * c.max_vars * c.wcap < 2 ^ 30 * 2 ^ 29 :=
        Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ h1) (Nat.mul_lt_mul_of_pos_left h2 (by decide))
      omega
    cm_split
    · have hl_lt : l.toNat < 2 * old_cv.toNat := by c0_bound
      have hl1_eq : (l + (1 : BitVec 64)).toNat = l.toNat + 1 := bv64_add1 (by omega)
      have h2l_eq : (l <<< (1 : Nat)).toNat = 2 * l.toNat := bv64_shl1_toNat (by omega)
      have h2l1_eq : ((l <<< (1 : Nat)) + (1 : BitVec 64)).toNat = 2 * l.toNat + 1 := by
        rw [bv64_add1 (by rw [h2l_eq]; omega), h2l_eq]
      have h2l_lt : 2 * l.toNat < wvecL.length := by omega
      have h2l1_lt : 2 * l.toNat + 1 < wvecL.length := by omega
      have h2l_lt' : (l <<< (1 : Nat)).toNat < wvecL.length := by rw [h2l_eq]; omega
      have h2l1_lt' : ((l <<< (1 : Nat)) + (1 : BitVec 64)).toNat < wvecL.length := by
        rw [h2l1_eq]; omega
      let off0 := fullWatchOffCore kL l.toNat
      let sz0 := fullWatchSizeCore kL l.toNat
      have hoff_eq : (wvecL[2 * l.toNat]'h2l_lt).toNat = off0 := by
        unfold off0 fullWatchOffCore kL; rw [List.getElem?_eq_getElem h2l_lt, Option.getD_some]
      have hsz_eq : (wvecL[2 * l.toNat + 1]'h2l1_lt).toNat = sz0 := by
        unfold sz0 fullWatchSizeCore kL; rw [List.getElem?_eq_getElem h2l1_lt, Option.getD_some]
      have hbd_l : off0 + sz0 ≤ kL.wlen := hlayL.bounds l.toNat (hold ▸ hl_lt)
      have hwl_le := hck0.wlen_le
      have hslice_l : WatchSliceOk F_cur kL l.toNat off0 sz0 :=
        hwatL l.toNat (Nat.le_refl _) hl_lt
      cm_split
      · have hsz0_zero : sz0 = 0 := by
          have h1 : (1 : BitVec 64).toNat = 1 := rfl
          have hidx_mod : (2 * l.toNat + (1 : BitVec 64).toNat) % 2 ^ 64 = 2 * l.toNat + 1 := by
            rw [h1]; exact Nat.mod_eq_of_lt (by omega)
          have hbv : (wvecL[(2 * l.toNat + (1 : BitVec 64).toNat) % 2 ^ 64]'(by
              rw [hidx_mod]; exact h2l1_lt)).setWidth 64 = 0#64 := by c0_bound
          have ht0 := congrArg BitVec.toNat hbv
          simp only [BitVec.toNat_setWidth, hidx_mod] at ht0
          rw [Nat.mod_eq_of_lt (by omega)] at ht0
          exact hsz_eq.symm.trans ht0
        let wvec' := wvecL.set (2 * l.toNat) 0#32
        let k' : FullCoreState := { kL with wvec := wvec' }
        obtain ⟨_, hsz'_l, hne_eq, hlay'⟩ :=
          compactBins_zero_slice_layout (kL := kL) rfl hwvL (by omega) (hold ▸ hl_lt) hsz0_zero
            hlayL
        cm_steps
        refine hLoop1 (kept, l + (1 : BitVec 64), ()) m (by dsimp only; rw [hl1_eq]; omega)
          ⟨by rw [hl1_eq]; omega, by rw [hl1_eq, Nat.add_mul, Nat.one_mul]; omega,
           wvec', wstkL, wuL, by simp [wvec', hwvL], hwsL, hlay', fun ol hol => ?_,
           fun ol hlo hol => ?_,
           compactMem_cast hm (by dsimp only [wvec', k', kL]; rw [h2l_eq]; rfl)⟩
        · rw [hl1_eq] at hol
          by_cases hol_eq : ol = l.toNat
          · subst hol_eq; rw [hsz'_l]; exact .empty
          · obtain ⟨ho, hs⟩ := hne_eq ol hol_eq; rw [ho, hs]
            exact CompactPreBinSliceOk.relocate (k := kL) (k' := k') (fun _ _ => rfl)
              (hpreL ol (by omega))
        · rw [hl1_eq] at hlo
          obtain ⟨ho, hs⟩ := hne_eq ol (by omega); rw [ho, hs]
          exact watchSliceOk_relocate (k := kL) (k' := k') rfl rfl rfl (fun _ _ => rfl)
            (hwatL ol (by omega) hol)
      · have hsz_pos : 0 < sz0 := by
          have h1 : (1 : BitVec 64).toNat = 1 := rfl
          have hidx_mod : (2 * l.toNat + (1 : BitVec 64).toNat) % 2 ^ 64 = 2 * l.toNat + 1 := by
            rw [h1]; exact Nat.mod_eq_of_lt (by omega)
          have hne : (wvecL[(2 * l.toNat + (1 : BitVec 64).toNat) % 2 ^ 64]'(by
              rw [hidx_mod]; exact h2l1_lt)).setWidth 64 ≠ 0#64 := by c0_bound
          refine Nat.pos_of_ne_zero fun hz => ?_
          have h2 : (wvecL[(2 * l.toNat + (1 : BitVec 64).toNat) % 2 ^ 64]'(by
              rw [hidx_mod]; exact h2l1_lt)).toNat = 0 := by simp only [hidx_mod, hsz_eq]; exact hz
          apply hne; apply BitVec.eq_of_toNat_eq; rw [zext_toNat _ (by decide), h2]; rfl
        have hbd_cap : off0 + sz0 ≤ c.wcap := by
          have h1 : off0 + sz0 ≤ s.core.wlen := hbd_l
          omega
        have hl2_ws1 : (l >>> (1 : Nat)).toNat < s.scratch.work_stk1.length := by
          rw [bv64_shr1_toNat]; omega
        have hl_vals : l.toNat < s.core.vals.length := by omega
        cm_to_group
        refine wp_join_group (ts := [.bool]) (fun (keep_l, ()) mK => mL = mK) ?_ ?_
        · rintro _ ⟨keep_l, ⟨⟩⟩ mK hm_eq; subst mK
          cm_steps
          have hoff64 :
              ((wvecL[(l <<< (1 : Nat)).toNat]'h2l_lt').setWidth 64).toNat = off0 := by
            rw [zext_toNat _ (by decide)]; simp only [h2l_eq, hoff_eq]
          have hsz64 :
              ((wvecL[((l <<< (1 : Nat)) + (1 : BitVec 64)).toNat]'h2l1_lt').setWidth 64).toNat =
                sz0 := by
            rw [zext_toNat _ (by decide)]; simp only [h2l1_eq, hsz_eq]
          have hend64 :
              ((wvecL[(l <<< (1 : Nat)).toNat]'h2l_lt').setWidth 64 +
                (wvecL[((l <<< (1 : Nat)) + (1 : BitVec 64)).toNat]'h2l1_lt').setWidth
                  64).toNat = off0 + sz0 := by
            rw [BitVec.toNat_add, hoff64, hsz64, Nat.mod_eq_of_lt (by omega)]
          refine full_compact_bins_ploop rfl rfl rfl hcv_le hv_len hws1_len hwc_lt hmax_lt
            hkl_mul_lt hold.symm hncv_le hbij hckL hlayL hwvL hwsL hl_lt hkept_le hoff64 hend64 ?_
            hbd_l hsz_pos hslice_l hpreL hwatL hmL hLoop1
          simpa [bv_c0] using hnlits_eq
        · intro Jk hJk
          clear hpreL hwatL hlayL hckL hsp hw hwat
          cm_split
          · cm_steps <;> exact hJk _ mL rfl
          · cm_steps <;> exact hJk _ mL rfl
    · have hl_eq : l.toNat = 2 * old_cv.toNat := by c0_bound
      rw [hl_eq] at hpreL
      clear hLoop1 J1 hwatL hck0 hsp hw hwat
      exact full_compact_bins_tail rfl hlen hcv_le hws1_len hmax_lt hold.symm hncv_le hbij hckL
        hlayL hwvL hwsL hpreL hmL hQ

end LeanQbe.T.Examples.Kissat.FullM4Compact
