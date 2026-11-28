/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Congruence.WpEvalGate0

/-!
# Congruence Gate Re-Evaluation XOR-Gate WP Proof (`WpEvalGateTag1`)

Proves `ev_tag1_wp` for `evTag1Expr` (XOR gate simplification, parity folding,
deduplication, self-cancellation, unit/equivalence folding, and hash-gate preparation
in `full_cong_eval_gate`).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Congruence

open Std Std.Sat
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Congruence
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Congruence.Spec
open Kraken.Bedrock2.Test

open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Proof.Congruence.CongTactics

attribute [local c0_load] ev_c0_load_full_tmp0 ev_c0_load_full_tmp1 ev_c0_load_full_tmp2
attribute [local c0_store] ev_c0_store_full_tmp0 ev_c0_store_full_tmp1 ev_c0_store_full_tmp2

local macro "ev_u" : tactic =>
  `(tactic| try dsimp only [evL2, evCmp32, evCmp64, evLd32, evLdK32, evLd8, evSgn0])

local macro "ev_steps" : tactic =>
  `(tactic| (ev_u; c0_hsteps!))

local macro "ev_steps_ng" : tactic =>
  `(tactic| (ev_u; c0_hsteps_nogrp))

local macro "ev_split" : tactic =>
  `(tactic| (ev_u; c0_hsplit))

/-! ## 1. Pure XOR-Fold, Bit0, and Self-Cancellation Semantic Lemmas -/

private theorem t1_bv32_and_not1_lt {x : BitVec 32} {n : Nat} (hx : x.toNat < n) :
    (x &&& ~~~1#32).toNat < n := by
  rw [m6_bv32_and_not1_toNat]; omega

private theorem t1_take_one {α : Type} (xs : List α) (h0 : 0 < xs.length) :
    xs.take 1 = [xs[0]'h0] := by
  rcases xs with _ | ⟨a, as⟩
  · cases h0
  · rfl

private theorem t1_take_two {α : Type} (xs : List α) (h0 : 0 < xs.length) (h1 : 1 < xs.length) :
    xs.take 2 = [xs[0]'h0, xs[1]'h1] := by
  rcases xs with _ | ⟨a, _ | ⟨b, cs⟩⟩
  · cases h0
  · simp at h1
  · rfl

private theorem t1_xor_bit0_flip_cancel (b : Bool) (x : BitVec 32) :
    ((b != decide ((x &&& 1#32) = 1#32)) != decide ((x &&& 1#32) = 1#32)) = b := by
  cases b <;> cases decide ((x &&& 1#32) = 1#32) <;> rfl

private theorem t1_xor_bit0_flip_decide (fl x : BitVec 32)
    (hfl : fl = 0#32 ∨ fl = 1#32) :
    decide ((fl ^^^ (x &&& 1#32)) = 1#32) =
      (decide (fl = 1#32) != decide ((x &&& 1#32) = 1#32)) := by
  rcases hfl with rfl | rfl <;> rcases ev_bv32_and1_eq01 x with h | h <;> simp [h]

private theorem t1_xor_eval_bit0_step (α : Nat → Bool) (fl x : BitVec 32)
    (hfl : fl = 0#32 ∨ fl = 1#32) :
    (evalLitVal α (x &&& ~~~1#32).toNat != decide ((fl ^^^ (x &&& 1#32)) = 1#32)) =
      (evalLitVal α x.toNat != decide (fl = 1#32)) := by
  rw [ev_xor_bit0_eval, t1_xor_bit0_flip_decide fl x hfl]
  cases evalLitVal α x.toNat <;> cases decide (fl = 1#32) <;>
    cases decide ((x &&& 1#32) = 1#32) <;> rfl

private theorem t1_xor_eval_flip_lhs (α : Nat → Bool) (lhs fl : BitVec 32)
    (hfl : fl = 0#32 ∨ fl = 1#32) :
    evalLitVal α (lhs ^^^ fl).toNat = (evalLitVal α lhs.toNat != decide (fl = 1#32)) := by
  rcases hfl with rfl | rfl
  · simp
  · rw [bv32_xor1_eq_litNeg, evalLitVal_litNeg]; simp

private theorem t1_xor_take_set_append (α : Nat → Bool) {xs : List (BitVec 32)} {n : Nat}
    {v : BitVec 32} (hn : n < xs.length) :
    xorEvalList α (((xs.set n v).take (n + 1)).map BitVec.toNat) =
      (xorEvalList α ((xs.take n).map BitVec.toNat) != evalLitVal α v.toNat) := by
  have htake : (xs.set n v).take (n + 1) = xs.take n ++ [v] := by
    apply List.ext_getElem
    · simp [List.length_take]; omega
    · intro j hj1 _
      simp only [List.length_take, List.length_set] at hj1
      by_cases hjn : j = n
      · subst hjn; simp [List.length_take, Nat.min_eq_left (by omega : j ≤ xs.length)]
      · have hj_lt : j < n := by omega
        rw [List.getElem_take, List.getElem_set_ne (by omega),
          List.getElem_append_left (by simp [List.length_take]; omega), List.getElem_take]
  rw [htake, List.map_append, List.map_cons, List.map_nil, xorEvalList_append,
    xorEvalList_cons, xorEvalList_nil, Bool.bne_false]

private theorem t1_xor_dedup_keep (α : Nat → Bool) {tmpd tmps : List (BitVec 32)}
    {ua si na : Nat} (hua : ua < tmpd.length) (hsi : si < na) (hna : na ≤ tmps.length)
    (heval : xorEvalList α ((tmps.take na).map BitVec.toNat) =
      (xorEvalList α ((tmpd.take ua).map BitVec.toNat) !=
        xorEvalList α (((tmps.drop si).take (na - si)).map BitVec.toNat))) :
    xorEvalList α ((tmps.take na).map BitVec.toNat) =
      (xorEvalList α ((((tmpd.set ua (tmps[si]' (by omega))).take (ua + 1))).map BitVec.toNat) !=
        xorEvalList α (((tmps.drop (si + 1)).take (na - (si + 1))).map BitVec.toNat)) := by
  rw [t1_xor_take_set_append α hua]
  have hdrop : (tmps.drop si).take (na - si) =
      tmps[si]'(by omega) :: (tmps.drop (si + 1)).take (na - (si + 1)) := by
    have := ev_list_drop_take_succ tmps (i := si) (k := na - (si + 1)) (by omega)
    simpa [show na - (si + 1) + 1 = na - si by omega] using this
  rw [heval, hdrop, List.map_cons, xorEvalList_cons]
  cases xorEvalList α ((tmpd.take ua).map BitVec.toNat) <;>
    cases evalLitVal α (tmps[si]'(by omega)).toNat <;>
    cases xorEvalList α (((tmps.drop (si + 1)).take (na - (si + 1))).map BitVec.toNat) <;> rfl

private theorem t1_xor_dedup_cancel (α : Nat → Bool) {tmpd tmps : List (BitVec 32)}
    {ua si na : Nat} (hsi1 : si + 1 < na) (hna : na ≤ tmps.length)
    (heq : tmps[si]'(by omega) = tmps[si + 1]'(by omega))
    (heval : xorEvalList α ((tmps.take na).map BitVec.toNat) =
      (xorEvalList α ((tmpd.take ua).map BitVec.toNat) !=
        xorEvalList α (((tmps.drop si).take (na - si)).map BitVec.toNat))) :
    xorEvalList α ((tmps.take na).map BitVec.toNat) =
      (xorEvalList α ((tmpd.take ua).map BitVec.toNat) !=
        xorEvalList α (((tmps.drop (si + 2)).take (na - (si + 2))).map BitVec.toNat)) := by
  have hdrop1 := ev_list_drop_take_succ tmps (i := si) (k := na - (si + 1)) (by omega)
  have hdrop2 := ev_list_drop_take_succ tmps (i := si + 1) (k := na - (si + 2)) (by omega)
  have hdrop : (tmps.drop si).take (na - si) =
      tmps[si]'(by omega) :: tmps[si]'(by omega) ::
        (tmps.drop (si + 2)).take (na - (si + 2)) := by
    rw [show na - si = na - (si + 1) + 1 by omega, hdrop1,
      show na - (si + 1) = na - (si + 2) + 1 by omega, hdrop2, heq]
  rw [heval, hdrop, List.map_cons, List.map_cons, xorEvalList_dedup_adj]

private theorem t1_list_eraseIdx_perm {α : Type} :
    ∀ (xs : List α) (i : Nat) (hi : i < xs.length),
      List.Perm xs (xs[i]'hi :: xs.eraseIdx i)
  | [], _, hi => absurd hi (Nat.not_lt_zero _)
  | x :: xs, 0, _ => List.Perm.refl _
  | x :: xs, i + 1, hi => by
    simp only [List.getElem_cons_succ, List.eraseIdx_cons_succ]
    exact ((t1_list_eraseIdx_perm xs i (by simpa using hi)).cons x).trans (List.Perm.swap ..)

private theorem t1_self_cancel_shift_perm {tmp tmps : List (BitVec 32)} {ua si : Nat}
    (hsi : si < ua) (hua : ua ≤ tmp.length) (htl : tmps.length = tmp.length)
    (hhead : ∀ j < si, tmps[j]? = tmp[j]?)
    (hmid : ∀ j, si ≤ j → j < ua - 1 → tmps[j]? = tmp[j + 1]?) :
    List.Perm (tmps.take (ua - 1)) ((tmp.take ua).eraseIdx si) := by
  have hlen1 : (tmps.take (ua - 1)).length = ua - 1 := by
    simp [List.length_take]; omega
  have hlen2 : ((tmp.take ua).eraseIdx si).length = ua - 1 := by
    rw [List.length_eraseIdx, List.length_take, Nat.min_eq_left hua, ite_eq_left hsi]
  have heq : tmps.take (ua - 1) = (tmp.take ua).eraseIdx si := by
    apply List.ext_getElem (hlen1.trans hlen2.symm)
    intro j hj1 hj2
    have hj_lt : j < ua - 1 := by omega
    rw [List.getElem_take, List.getElem_eraseIdx]; split
    · rename_i hjs; rw [List.getElem_take]
      have h1 := hhead j hjs
      rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at h1
      exact Option.some.inj h1
    · rename_i hjs; have hj_ge : si ≤ j := by omega
      rw [List.getElem_take]
      have h1 := hmid j hj_ge hj_lt
      rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at h1
      exact Option.some.inj h1
  rw [heq]

private theorem t1_self_cancel_eval {F : CNF Nat} {lhs : BitVec 32}
    {tmp tmps : List (BitVec 32)} {ua si : Nat} (hsi : si < ua) (hua : ua ≤ tmp.length)
    (htl : tmps.length = tmp.length)
    (hlhs : ∀ α : Nat → Bool, F.Sat α →
      evalLitVal α lhs.toNat = xorEvalList α ((tmp.take ua).map BitVec.toNat))
    (hs_eq : tmp[si]' (by omega) = (lhs &&& ~~~1#32))
    (hhead : ∀ j < si, tmps[j]? = tmp[j]?)
    (hmid : ∀ j, si ≤ j → j < ua - 1 → tmps[j]? = tmp[j + 1]?) :
    ∀ α : Nat → Bool, F.Sat α →
      xorEvalList α ((tmps.take (ua - 1)).map BitVec.toNat) =
        decide ((lhs &&& 1#32) = 1#32) := by
  intro α hα
  have hperm := (t1_self_cancel_shift_perm hsi hua htl hhead hmid).map BitVec.toNat
  have hsi_t : si < (tmp.take ua).length := by rw [List.length_take]; omega
  have hperm2 := (t1_list_eraseIdx_perm (tmp.take ua) si hsi_t).map BitVec.toNat
  have hget_si : ((tmp.take ua)[si]'hsi_t) = (lhs &&& ~~~1#32) := by
    rw [List.getElem_take]; exact hs_eq
  have hx : xorEvalList α ((tmp.take ua).map BitVec.toNat) =
      (evalLitVal α (lhs &&& ~~~1#32).toNat !=
        xorEvalList α ((tmps.take (ua - 1)).map BitVec.toNat)) := by
    rw [xorEvalList_perm α hperm2, List.map_cons, xorEvalList_cons, hget_si,
      xorEvalList_perm α hperm.symm]
  have hev := hlhs α hα
  rw [hx, ev_xor_bit0_eval] at hev
  cases hl : evalLitVal α lhs.toNat <;>
    cases hs : decide ((lhs &&& 1#32) = 1#32) <;>
    cases xr : xorEvalList α ((tmps.take (ua - 1)).map BitVec.toNat) <;>
    simp_all

/-! ## 2. Self-Cancellation Sub-Block WP Proof (`ev_tag1_self_cancel_wp`) -/

private theorem ev_tag1_self_cancel_wp (Γ : Env)
    (hUnit : Γ.Has "full_cong_unit_fold" Spec.fullCongUnitFoldSpec)
    (hEquiv : Γ.Has "full_cong_equiv_fold" Spec.fullCongEquivFoldSpec)
    (hEnq : Γ.Has "full_cong_enq_var" Spec.fullCongEnqVarSpec)
    {maxA : Nat} {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {cv0 : Nat}
    {fl0 : BitVec 64} {ar0 : List (BitVec 32)} {arl0 g_len ht_off ht_sz : Nat}
    {scr0 scr_in : List (BitVec 32)} {s0 : FullState} {m0 : Mem 64}
    {ctrl_off : BitVec 64} {next_ep lhs iw ua : BitVec 32}
    {J55 : Cont [i32, .bool, .bool, i32]}
    {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost}
    (hg_ht : g_len ≤ ht_off) (hua_le4 : ua.toNat ≤ 4) (hua_cv : ua.toNat ≤ cv0)
    (hlhs_lt : lhs.toNat < 2 * cv0)
    (htmp_lt : ∀ k < ua.toNat, (s0.core.tmp[k]?.getD 0#32).toNat < 2 * cv0)
    (hxor : ∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α →
      evalLitVal α lhs.toNat = xorEvalList α ((s0.core.tmp.take ua.toNat).map BitVec.toNat))
    (hok0 : EvCoreOk maxA c F0 F_cur cv0 fl0 ar0 arl0 g_len ctrl_off.toNat ht_off ht_sz
      scr0 scr_in s0)
    (hm0 : (FullMem c s0 ⋆ R) m0)
    (hQ2 : ∀ s' m', EvCoreOk maxA c F0 F_cur cv0 fl0 ar0 arl0 g_len ctrl_off.toNat ht_off ht_sz
      scr0 scr_in s' → F0.Unsat → (FullMem c s' ⋆ R) m' → Q (2#64, ()) m')
    (hJ55 : ∀ iw' (nh' ch' : Bool) har' s' m',
      EvCoreOk maxA c F0 F_cur cv0 fl0 ar0 arl0 g_len ctrl_off.toNat ht_off ht_sz scr0 scr_in s' →
      (nh' = true → har' = ua ∧ s'.core.tmp = s0.core.tmp) →
      (FullMem c s' ⋆ R) m' → J55 (iw', nh', ch', har', ()) m') :
    wp Γ Q X (evTag1SelfCancelExpr c.hdr c.pTmp ctrl_off next_ep lhs iw ua J55) m0 := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv_eq := hok0.2.1; have hcv_le : cv0 ≤ c.max_vars := hcv_eq ▸ hok0.1.1.core_ok.cur_vars_le
  have htmpl0 := hok0.1.1.core_ok.tmp_len_arr
  unfold evTag1SelfCancelExpr; ev_split
  rotate_left
  · ev_steps; exact hJ55 iw true false ua s0 m0 hok0 (fun _ => ⟨rfl, rfl⟩) hm0
  have hua_pos : 0 < ua.toNat := by omega
  clear hc; ev_steps_ng
  refine wp_join_group (ts := [i32, i32])
    (fun (iw', si, ()) msi => msi = m0 ∧ si.toNat ≤ ua.toNat ∧
      (∀ h : si.toNat < ua.toNat, s0.core.tmp[si.toNat]'(by omega) = (lhs &&& ~~~1#32))) ?_ ?_
  · rintro _ ⟨iw', si, ⟨⟩⟩ msi ⟨hms, hsi_le, hsi_eq⟩; subst msi
    ev_steps_ng
    refine wp_join_group (ts := [.bool, .bool, i32])
      (fun (nh', ch', har', ()) mj => ∃ sj : FullState,
        EvCoreOk maxA c F0 F_cur cv0 fl0 ar0 arl0 g_len ctrl_off.toNat ht_off ht_sz
          scr0 scr_in sj ∧
        (nh' = true → har' = ua ∧ sj.core.tmp = s0.core.tmp) ∧
        (FullMem c sj ⋆ R) mj)
      (fun _ ⟨nh', ch', har', ⟨⟩⟩ mj ⟨sj, hokj, hnhj, hmj⟩ => by
        ev_steps; exact hJ55 iw' nh' ch' har' sj mj hokj hnhj hmj) ?_
    intro J62 hJ62; ev_split
    rotate_left
    · ev_steps; exact hJ62 (true, false, ua, ()) m0 ⟨s0, hok0, fun _ => ⟨rfl, rfl⟩, hm0⟩
    have hsi_lt : si.toNat < ua.toNat := by omega
    have hsi_eq' : s0.core.tmp[si.toNat]'(by omega) = (lhs &&& ~~~1#32) := hsi_eq hsi_lt
    ev_steps_ng
    refine wp_loop_inv (ts := [i32])
      (fun (j, ()) mj => si.toNat ≤ j.toNat ∧ j.toNat ≤ ua.toNat - 1 ∧
        ∃ tmps : List (BitVec 32), tmps.length = c.max_vars ∧
          (∀ k < si.toNat, tmps[k]? = s0.core.tmp[k]?) ∧
          (∀ k, si.toNat ≤ k → k < j.toNat → tmps[k]? = s0.core.tmp[k + 1]?) ∧
          (∀ k, j.toNat ≤ k → k < ua.toNat → tmps[k]? = s0.core.tmp[k]?) ∧
          (FullMem c { s0 with core := { s0.core with tmp := tmps } } ⋆ R) mj)
      (fun (j, ()) _ => ua.toNat - 1 - j.toNat)
      (fun _ hJ64 => by
        ev_steps; exact hJ64 (si, ()) m0 ⟨Nat.le_refl _, by omega, s0.core.tmp, htmpl0,
          fun _ _ => rfl, fun k h1 h2 => by omega, fun _ _ _ => rfl, hm0⟩)
      (fun _ ⟨j, ⟨⟩⟩ mj ⟨hj_ge, hj_le, tmps, htl_s, hhead, hmid, htail, hmj⟩ ih64 => ?_)
    let sj : FullState := { s0 with core := { s0.core with tmp := tmps } }
    have hmj' : (FullMem c sj ⋆ R) mj := hmj
    ev_split
    · have hj1 : (j + 1#32).toNat = j.toNat + 1 := bv32_add1_lt_of (by omega)
      have hj1_lt : j.toNat + 1 < ua.toNat := by rw [← hj1]; exact hc
      have hj_arr : (j.setWidth 64).toNat < sj.core.tmp.length := by
        change (j.setWidth 64).toNat < tmps.length; rw [bv_zext32_toNat]; omega
      have hj1_arr : ((j + 1#32).setWidth 64).toNat < sj.core.tmp.length := by
        change ((j + 1#32).setWidth 64).toNat < tmps.length; rw [bv_zext32_toNat, hj1]; omega
      have hj1_s0 : j.toNat + 1 < s0.core.tmp.length := by omega
      have hld_eq : tmps[j.toNat + 1]'(by omega) = s0.core.tmp[j.toNat + 1]'hj1_s0 := by
        have h1 := htail (j.toNat + 1) (by omega) hj1_lt
        rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem hj1_s0] at h1
        exact Option.some.inj h1
      clear hc; ev_steps
      refine ih64 (j + 1#32, ()) m (by dsimp only; rw [hj1]; omega)
        ⟨by omega, by omega, tmps.set j.toNat (s0.core.tmp[j.toNat + 1]'hj1_s0),
         by simp [htl_s],
         (fun k hk => by rw [List.getElem?_set_ne (by omega)]; exact hhead k hk),
         (fun k hk1 hk2 => by
           rw [hj1] at hk2; by_cases hkj : k = j.toNat
           · subst hkj; rw [List.getElem?_set_self (by omega), List.getElem?_eq_getElem hj1_s0]
           · rw [List.getElem?_set_ne (by omega)]; exact hmid k hk1 (by omega)),
         (fun k hk1 hk2 => by
           rw [hj1] at hk1; rw [List.getElem?_set_ne (by omega)]; exact htail k (by omega) hk2),
         by have hj1' : (j + 1 : BitVec 32).toNat = j.toNat + 1 := hj1
            simpa only [sj, bv_zext32_toNat, hj1', hld_eq] using hm⟩
    have hj_eq : j.toNat = ua.toNat - 1 := by
      have h1 : (j + 1#32).toNat = j.toNat + 1 := bv32_add1_lt_of (by omega)
      have hnot : ¬ (j + 1#32).toNat < ua.toNat := hc
      rw [h1] at hnot; omega
    rw [hj_eq] at hmid
    let s_sc : FullState := { s0 with core := { s0.core with tmp := tmps } }
    have hok_sc := evCoreOk_tmp hok0 htl_s
    have hperm_sc := t1_self_cancel_shift_perm hsi_lt (by omega)
      (htl_s.trans htmpl0.symm) hhead hmid
    have htmps_lt : ∀ k < ua.toNat - 1, (tmps[k]?.getD 0#32).toNat < 2 * cv0 := fun k hk => by
      have hmem : tmps[k]'(by omega) ∈ tmps.take (ua.toNat - 1) :=
        ev_mem_take_of_lt hk (by omega)
      have hmem2 : tmps[k]'(by omega) ∈ (s0.core.tmp.take ua.toNat).eraseIdx si.toNat :=
        hperm_sc.mem_iff.mp hmem
      have hmem3 : tmps[k]'(by omega) ∈ s0.core.tmp.take ua.toNat :=
        List.mem_of_mem_eraseIdx hmem2
      obtain ⟨q, hq, hgq⟩ := ev_lt_take_of_mem hmem3
      simp only [Nat.lt_min] at hq
      have hlt := htmp_lt q (by omega)
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hlt
      have h2 := Option.some.inj ((List.getElem?_eq_getElem (by omega)).symm.trans hgq)
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some, ← h2]
      exact hlt
    have hsc_ev := t1_self_cancel_eval hsi_lt (by omega) (htl_s.trans htmpl0.symm) hxor hsi_eq'
      hhead hmid
    have hua_sub1 : (ua - 1#32).toNat = ua.toNat - 1 := ev_bv32_sub1_toNat hua_pos
    rcases ev_bv32_and1_eq01 lhs with hls0 | hls1 <;>
      have hls_eq : lhs &&& 1#32 = 0#32 ∨ lhs &&& 1#32 = 1#32 := by
        first | exact Or.inl hls0 | exact Or.inr hls1
    all_goals
      clear hc; ev_steps_ng
      refine wp_join_group (ts := [.bool, .bool])
        (fun (nh', ch', ()) mj' => nh' = false ∧ ∃ sj : FullState,
          EvCoreOk maxA c F0 F_cur cv0 fl0 ar0 arl0 g_len ctrl_off.toNat ht_off ht_sz
            scr0 scr_in sj ∧ (FullMem c sj ⋆ R) mj')
        (fun _ ⟨nh', ch', ⟨⟩⟩ mj' ⟨hnh, sj, hokj, hmj'⟩ => by
          ev_steps; exact hJ62 (nh', ch', ua - 1#32, ()) mj'
            ⟨sj, hokj, (fun h => absurd (hnh.symm.trans h) (by decide)), hmj'⟩) ?_
      intro J70 hJ70; ev_split
    · -- Case `ua - 1 == 0` (left, hls0)
      ev_split
      · exact absurd hls0 hc
      · ev_steps; exact hJ70 (false, false, ()) mj ⟨rfl, s_sc, hok_sc, hmj⟩
    · -- Case `ua - 1 ≠ 0` (left, hls0)
      clear hc; ev_steps_ng
      refine wp_join_group (ts := [.bool, .bool])
        (fun (nh', ch', ()) mj' => nh' = false ∧ ∃ sj : FullState,
          EvCoreOk maxA c F0 F_cur cv0 fl0 ar0 arl0 g_len ctrl_off.toNat ht_off ht_sz
            scr0 scr_in sj ∧ (FullMem c sj ⋆ R) mj')
        (fun _ ⟨nh', ch', ⟨⟩⟩ mj' h => by ev_steps; exact hJ70 (nh', ch', ()) mj' h) ?_
      intro J72 hJ72; ev_split
      · -- `ua - 1 = 1`
        have hua1 : ua.toNat - 1 = 1 := by
          simpa [hua_sub1] using congrArg BitVec.toNat hc
        have h0_tmps : 0 < tmps.length := by omega
        have h0_lt : (tmps[0]'h0_tmps).toNat < 2 * cv0 := by
          have h := htmps_lt 0 (by omega)
          rwa [List.getElem?_eq_getElem h0_tmps, Option.getD_some] at h
        have hent : (cnfOfClauses F_cur).EntailsClause
            (cnfClause [(tmps[0]'h0_tmps ^^^ (1#32 ^^^ (lhs &&& 1#32))).toNat]) := by
          refine ev_entails_of_eval fun α hα => ?_
          have hev := hsc_ev α hα
          rw [hua1, t1_take_one tmps h0_tmps, List.map_singleton, xorEvalList_cons,
            xorEvalList_nil, Bool.bne_false] at hev
          rw [hls0, show (1#32 ^^^ 0#32 : BitVec 32) = 1#32 from rfl, bv32_xor1_eq_litNeg,
            evalLitVal_litNeg, hev, hls0]; rfl
        clear hc; ev_steps
        refine ev_unit_wp Γ hUnit hok_sc
          (ev_xor1_bit01_lt h0_lt (by simp [hls0]))
          hent hmj hQ2 fun ch' s' m' _ _ hok' hm' => by
            ev_steps; exact hJ72 (false, ch', ()) m' ⟨rfl, s', hok', hm'⟩
      · clear hc; ev_steps_ng
        refine wp_join_group (ts := [.bool, .bool])
          (fun (nh', ch', ()) mj' => nh' = false ∧ ∃ sj : FullState,
            EvCoreOk maxA c F0 F_cur cv0 fl0 ar0 arl0 g_len ctrl_off.toNat ht_off ht_sz
              scr0 scr_in sj ∧ (FullMem c sj ⋆ R) mj')
          (fun _ ⟨nh', ch', ⟨⟩⟩ mj' h => by ev_steps; exact hJ72 (nh', ch', ()) mj' h) ?_
        intro J74 hJ74; ev_split
        · -- `ua - 1 = 2`
          have hua2 : ua.toNat - 1 = 2 := by
            simpa [hua_sub1] using congrArg BitVec.toNat hc
          have h0_tmps : 0 < tmps.length := by omega
          have h1_tmps : 1 < tmps.length := by omega
          have h0_lt : (tmps[0]'h0_tmps).toNat < 2 * cv0 := by
            have h := htmps_lt 0 (by omega)
            rwa [List.getElem?_eq_getElem h0_tmps, Option.getD_some] at h
          have ha0_lt : (tmps[0]'h0_tmps ^^^ (lhs &&& 1#32)).toNat < 2 * cv0 :=
            ev_xor1_bit01_lt h0_lt hls_eq
          have ha1_lt : (tmps[1]'h1_tmps).toNat < 2 * cv0 := by
            have h := htmps_lt 1 (by omega)
            rwa [List.getElem?_eq_getElem h1_tmps, Option.getD_some] at h
          have heqv : LitEquiv (cnfOfClauses F_cur)
              (tmps[0]'h0_tmps ^^^ (lhs &&& 1#32)).toNat (tmps[1]'h1_tmps).toNat := by
            refine ev_litEquiv_of_eval fun α hα => ?_
            have hev := hsc_ev α hα
            rw [hua2, t1_take_two tmps h0_tmps h1_tmps, List.map_cons, List.map_singleton,
              xorEvalList_pair] at hev
            rw [hls0, BitVec.xor_zero]
            cases h0e : evalLitVal α (tmps[0]'h0_tmps).toNat <;>
              cases h1e : evalLitVal α (tmps[1]'h1_tmps).toNat <;>
              rw [h0e, h1e, hls0] at hev <;>
              first | rfl | (exfalso; revert hev; decide)
          clear hc; ev_steps
          refine ev_equiv_enq2_wp Γ hEquiv hEnq hg_ht rfl hok_sc ha0_lt ha1_lt heqv hmj hQ2
            fun ch' s' m' _ hok' hm' => by
              ev_steps; exact hJ74 (false, ch', ()) m' ⟨rfl, s', hok', hm'⟩
        · ev_steps; exact hJ74 (false, false, ()) mj ⟨rfl, s_sc, hok_sc, hmj⟩
    · -- Case `ua - 1 == 0` (right, hls1)
      have hua0 : ua.toNat - 1 = 0 := by
        simpa [hua_sub1] using congrArg BitVec.toNat hc
      clear hc; ev_split
      · have huns : (cnfOfClauses F_cur).Unsat := CNF.unsat_iff_not_sat.mpr fun α hα => by
          have hev := hsc_ev α hα
          rw [hua0, List.take_zero, List.map_nil, xorEvalList_nil, hls1] at hev; cases hev
        clear hc; ev_steps
        exact hQ2 _ m (evCoreOk_inc hok_sc huns) (hok_sc.1.2.1.ext_sound.2 huns) hm
      · exfalso; simp [hls1] at hc
    · -- Case `ua - 1 ≠ 0` (right, hls1)
      clear hc; ev_steps_ng
      refine wp_join_group (ts := [.bool, .bool])
        (fun (nh', ch', ()) mj' => nh' = false ∧ ∃ sj : FullState,
          EvCoreOk maxA c F0 F_cur cv0 fl0 ar0 arl0 g_len ctrl_off.toNat ht_off ht_sz
            scr0 scr_in sj ∧ (FullMem c sj ⋆ R) mj')
        (fun _ ⟨nh', ch', ⟨⟩⟩ mj' h => by ev_steps; exact hJ70 (nh', ch', ()) mj' h) ?_
      intro J72 hJ72; ev_split
      · -- `ua - 1 = 1`
        have hua1 : ua.toNat - 1 = 1 := by
          simpa [hua_sub1] using congrArg BitVec.toNat hc
        have h0_tmps : 0 < tmps.length := by omega
        have h0_lt : (tmps[0]'h0_tmps).toNat < 2 * cv0 := by
          have h := htmps_lt 0 (by omega)
          rwa [List.getElem?_eq_getElem h0_tmps, Option.getD_some] at h
        have hent : (cnfOfClauses F_cur).EntailsClause
            (cnfClause [(tmps[0]'h0_tmps ^^^ (1#32 ^^^ (lhs &&& 1#32))).toNat]) := by
          refine ev_entails_of_eval fun α hα => ?_
          have hev := hsc_ev α hα
          rw [hua1, t1_take_one tmps h0_tmps, List.map_singleton, xorEvalList_cons,
            xorEvalList_nil, Bool.bne_false] at hev
          rw [hls1, show (1#32 ^^^ 1#32 : BitVec 32) = 0#32 from rfl, BitVec.xor_zero, hev, hls1]
          rfl
        clear hc; ev_steps
        refine ev_unit_wp Γ hUnit hok_sc
          (ev_xor1_bit01_lt h0_lt (by simp [hls1]))
          hent hmj hQ2 fun ch' s' m' _ _ hok' hm' => by
            ev_steps; exact hJ72 (false, ch', ()) m' ⟨rfl, s', hok', hm'⟩
      · clear hc; ev_steps_ng
        refine wp_join_group (ts := [.bool, .bool])
          (fun (nh', ch', ()) mj' => nh' = false ∧ ∃ sj : FullState,
            EvCoreOk maxA c F0 F_cur cv0 fl0 ar0 arl0 g_len ctrl_off.toNat ht_off ht_sz
              scr0 scr_in sj ∧ (FullMem c sj ⋆ R) mj')
          (fun _ ⟨nh', ch', ⟨⟩⟩ mj' h => by ev_steps; exact hJ72 (nh', ch', ()) mj' h) ?_
        intro J74 hJ74; ev_split
        · -- `ua - 1 = 2`
          have hua2 : ua.toNat - 1 = 2 := by
            simpa [hua_sub1] using congrArg BitVec.toNat hc
          have h0_tmps : 0 < tmps.length := by omega
          have h1_tmps : 1 < tmps.length := by omega
          have h0_lt : (tmps[0]'h0_tmps).toNat < 2 * cv0 := by
            have h := htmps_lt 0 (by omega)
            rwa [List.getElem?_eq_getElem h0_tmps, Option.getD_some] at h
          have ha0_lt : (tmps[0]'h0_tmps ^^^ (lhs &&& 1#32)).toNat < 2 * cv0 :=
            ev_xor1_bit01_lt h0_lt hls_eq
          have ha1_lt : (tmps[1]'h1_tmps).toNat < 2 * cv0 := by
            have h := htmps_lt 1 (by omega)
            rwa [List.getElem?_eq_getElem h1_tmps, Option.getD_some] at h
          have heqv : LitEquiv (cnfOfClauses F_cur)
              (tmps[0]'h0_tmps ^^^ (lhs &&& 1#32)).toNat (tmps[1]'h1_tmps).toNat := by
            refine ev_litEquiv_of_eval fun α hα => ?_
            have hev := hsc_ev α hα
            rw [hua2, t1_take_two tmps h0_tmps h1_tmps, List.map_cons, List.map_singleton,
              xorEvalList_pair] at hev
            rw [hls1, bv32_xor1_eq_litNeg, evalLitVal_litNeg]
            cases h0e : evalLitVal α (tmps[0]'h0_tmps).toNat <;>
              cases h1e : evalLitVal α (tmps[1]'h1_tmps).toNat <;>
              rw [h0e, h1e, hls1] at hev <;>
              first | rfl | (exfalso; revert hev; decide)
          clear hc; ev_steps
          refine ev_equiv_enq2_wp Γ hEquiv hEnq hg_ht rfl hok_sc ha0_lt ha1_lt heqv hmj hQ2
            fun ch' s' m' _ hok' hm' => by
              ev_steps; exact hJ74 (false, ch', ()) m' ⟨rfl, s', hok', hm'⟩
        · ev_steps; exact hJ74 (false, false, ()) mj ⟨rfl, s_sc, hok_sc, hmj⟩
  · intro J60 hJ60
    refine wp_loop_inv (ts := [i32])
      (fun (si, ()) msi => msi = m0 ∧ si.toNat ≤ ua.toNat)
      (fun (si, ()) _ => ua.toNat - si.toNat)
      (fun _ hJ => by ev_steps; exact hJ (0#32, ()) m0 ⟨rfl, Nat.zero_le _⟩)
      (fun _ ⟨si, ⟨⟩⟩ msi ⟨hm_i, hsi_le⟩ ih60 => ?_)
    subst msi; ev_split
    · have hsi_lt : si.toNat < ua.toNat := by omega
      have hsi_arr : (si.setWidth 64).toNat < s0.core.tmp.length := by
        rw [bv_zext32_toNat]; omega
      have hsi1 : (si + 1#32).toNat = si.toNat + 1 := bv32_add1_lt_of (by omega)
      have hsi_eq : s0.core.tmp[(si.setWidth 64).toNat]'hsi_arr =
          s0.core.tmp[si.toNat]'(by omega) := list_getElem_congr (bv_zext32_toNat si) _ _
      ev_split
      · ev_steps; exact hJ60 (si, si, ()) m0 ⟨rfl, by omega, fun _ => by rw [← hsi_eq]; exact hc⟩
      · ev_steps; exact ih60 (si + 1#32, ()) m0 (by dsimp only; rw [hsi1]; omega)
          ⟨rfl, by omega⟩
    · have hsi_eq : si.toNat = ua.toNat := by omega
      ev_steps; exact hJ60 (si, ua, ()) m0 ⟨rfl, Nat.le_refl _, fun h => by omega⟩

/-! ## 3. Main XOR-Gate WP Theorem (`ev_tag1_wp`) -/

private abbrev T1Out (maxA : Nat) (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (cv0 : Nat) (fl0 : BitVec 64) (ar0 : List (BitVec 32))
    (arl0 g_len ctrl_off ht_off ht_sz : Nat) (scr0 scr_in : List (BitVec 32))
    (gtype lhs' : BitVec 32) (R : Mem 64 → Prop) : Tup Val [i32, .bool, .bool] → Mem 64 → Prop :=
  fun (har', nh', _, ()) mj => ∃ stj : FullState,
    EvCoreOk maxA c F0 F_cur cv0 fl0 ar0 arl0 g_len ctrl_off ht_off ht_sz scr0 scr_in stj ∧
    (nh' = true → EvHashGateOk maxA F_cur cv0 gtype gtype har' lhs' stj.core.tmp) ∧
    (FullMem c stj ⋆ R) mj

private abbrev T1J44Inv (c : FullCfg) (F_cur : List (List Nat)) (cv0 : Nat) (s0 : FullState)
    (arity lhs : BitVec 32) (raw : List (BitVec 32)) (R : Mem 64 → Prop) :
    Tup Val [i32, i32, i32] → Mem 64 → Prop :=
  fun (il, fl, na, ()) ml => il.toNat ≤ arity.toNat ∧ na.toNat ≤ il.toNat ∧
    (fl = 0#32 ∨ fl = 1#32) ∧
    ∃ tmpl : List (BitVec 32), tmpl.length = c.max_vars ∧
      (∀ j, il.toNat ≤ j → j < arity.toNat → tmpl[j]? = raw[j]?) ∧
      (∀ j < na.toNat, (tmpl[j]?.getD 0#32).toNat < 2 * cv0) ∧
      (∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α →
        evalLitVal α lhs.toNat =
          ((xorEvalList α ((tmpl.take na.toNat).map BitVec.toNat) !=
            xorEvalList α ((raw.drop il.toNat).map BitVec.toNat)) != decide (fl = 1#32))) ∧
      (FullMem c { s0 with core := { s0.core with tmp := tmpl } } ⋆ R) ml

private abbrev T1J51Inv (c : FullCfg) (F_cur : List (List Nat)) (cv0 : Nat) (s0 : FullState)
    (na lhs' : BitVec 32) (tmps : List (BitVec 32)) (R : Mem 64 → Prop) :
    Tup Val [i32, i32] → Mem 64 → Prop :=
  fun (si, ua, ()) md => si.toNat ≤ na.toNat ∧ ua.toNat ≤ si.toNat ∧
    ∃ tmpd : List (BitVec 32), tmpd.length = c.max_vars ∧
      (∀ j, si.toNat ≤ j → j < na.toNat → tmpd[j]? = tmps[j]?) ∧
      (∀ j < ua.toNat, (tmpd[j]?.getD 0#32).toNat < 2 * cv0) ∧
      (∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α →
        evalLitVal α lhs'.toNat =
          (xorEvalList α ((tmpd.take ua.toNat).map BitVec.toNat) !=
            xorEvalList α
              (((tmps.drop si.toNat).take (na.toNat - si.toNat)).map BitVec.toNat))) ∧
      (FullMem c { s0 with core := { s0.core with tmp := tmpd } } ⋆ R) md

private theorem t1_eval_raw_equiv {F : CNF Nat} {lhs lhs0 arity : BitVec 32} {g_n : Nat}
    {scr0 tmp : List (BitVec 32)} (hlhs_eqv : LitEquiv F lhs0.toNat lhs.toNat)
    (hxor0 : XorListGateDef F lhs0.toNat
      (((scr0.drop (g_n + 2)).take arity.toNat).map BitVec.toNat))
    (hscr_ge : g_n + 2 + arity.toNat ≤ scr0.length) (har_tmp : arity.toNat ≤ tmp.length)
    (htmp_i : ∀ k < arity.toNat, LitEquiv F (scr0[g_n + 2 + k]?.getD 0#32).toNat
      (tmp[k]?.getD 0#32).toNat) :
    ∀ α : Nat → Bool, F.Sat α →
      evalLitVal α lhs.toNat = xorEvalList α ((tmp.take arity.toNat).map BitVec.toNat) := by
  intro α hα
  have h0 := (litEquiv_eval hα hlhs_eqv).symm.trans (hxor0 α hα)
  refine h0.trans (xorEvalList_of_litEquiv hα ?_ fun k hk => ?_)
  · simp [List.length_map, List.length_take, List.length_drop]; omega
  · simp only [List.length_map, List.length_take, List.length_drop] at hk
    have hk_lt : k < arity.toNat := by omega
    have hk_scr : g_n + 2 + k < scr0.length := by omega
    have hk_tmp : k < tmp.length := by omega
    have h1 := htmp_i k hk_lt
    simp only [List.getElem?_map, List.getElem?_take_of_lt hk_lt, List.getElem?_drop,
      List.getElem?_eq_getElem hk_scr, List.getElem?_eq_getElem hk_tmp, Option.map,
      Option.getD_some]
    rwa [List.getElem?_eq_getElem hk_scr, List.getElem?_eq_getElem hk_tmp,
      Option.getD_some, Option.getD_some] at h1

private theorem t1_j61_flip_eval {α : Nat → Bool} {lhs fl x : BitVec 32} {A B : Bool}
    (hfl : fl = 0#32 ∨ fl = 1#32) (hx : evalLitVal α x.toNat = true)
    (h1 : evalLitVal α lhs.toNat = ((A != (evalLitVal α x.toNat != B)) != decide (fl = 1#32))) :
    evalLitVal α lhs.toNat = ((A != B) != decide ((fl ^^^ 1#32) = 1#32)) := by
  rw [hx] at h1; rcases hfl with rfl | rfl <;> cases A <;> cases B <;> simp at h1 ⊢ <;> exact h1

private theorem t1_j56_step_eval {α : Nat → Bool} {lhs fl : BitVec 32} {na il : Nat}
    {tmpl raw : List (BitVec 32)} (hna : na < tmpl.length) (hil : il < raw.length)
    (hfl : fl = 0#32 ∨ fl = 1#32)
    (h1 : evalLitVal α lhs.toNat =
      ((xorEvalList α ((tmpl.take na).map BitVec.toNat) !=
        xorEvalList α ((raw.drop il).map BitVec.toNat)) != decide (fl = 1#32))) :
    evalLitVal α lhs.toNat =
      ((xorEvalList α (((tmpl.set na (raw[il]'hil &&& ~~~1#32)).take (na + 1)).map BitVec.toNat) !=
        xorEvalList α ((raw.drop (il + 1)).map BitVec.toNat)) !=
        decide ((fl ^^^ (raw[il]'hil &&& 1#32)) = 1#32)) := by
  rw [List.drop_eq_getElem_cons hil, List.map_cons, xorEvalList_cons] at h1
  rw [h1, t1_xor_take_set_append α hna, ev_xor_bit0_eval,
    t1_xor_bit0_flip_decide fl (raw[il]'hil) hfl]
  cases xorEvalList α ((tmpl.take na).map BitVec.toNat) <;>
    cases evalLitVal α (raw[il]'hil).toNat <;>
    cases xorEvalList α ((raw.drop (il + 1)).map BitVec.toNat) <;>
    cases decide (fl = 1#32) <;>
    cases decide ((raw[il]'hil &&& 1#32) = 1#32) <;> rfl

private theorem t1_sort_tmp_ok {F : CNF Nat} {cv0 na : Nat} {lhs' : BitVec 32}
    {tmpl tmps : List (BitVec 32)} (hna_s : na ≤ tmps.length)
    (hperm : List.Perm (tmps.take na) (tmpl.take na))
    (htmp_lt : ∀ j < na, (tmpl[j]?.getD 0#32).toNat < 2 * cv0)
    (hev : ∀ α : Nat → Bool, F.Sat α →
      evalLitVal α lhs'.toNat = xorEvalList α ((tmpl.take na).map BitVec.toNat)) :
    (∀ j < na, (tmps[j]?.getD 0#32).toNat < 2 * cv0) ∧
      (∀ α : Nat → Bool, F.Sat α →
        evalLitVal α lhs'.toNat = xorEvalList α ((tmps.take na).map BitVec.toNat)) := by
  refine ⟨fun j hj => ?_, fun α hα =>
    (hev α hα).trans (xorEvalList_perm α (hperm.symm.map BitVec.toNat))⟩
  have hmem : tmps[j]'(by omega) ∈ tmps.take na := ev_mem_take_of_lt hj hna_s
  obtain ⟨q, hq, hgq⟩ := ev_lt_take_of_mem (hperm.mem_iff.mp hmem)
  simp only [Nat.lt_min] at hq
  have h1 := htmp_lt q hq.1
  rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at h1
  have h2 := Option.some.inj ((List.getElem?_eq_getElem (by omega)).symm.trans hgq)
  rw [List.getElem?_eq_getElem (by omega), Option.getD_some, ← h2]
  exact h1

private theorem t1_j74_pair0 {F : CNF Nat} {lhs' : BitVec 32}
    {tmp : List (BitVec 32)} (h0 : 0 < tmp.length) (h1 : 1 < tmp.length)
    (hev : ∀ α, F.Sat α → evalLitVal α lhs'.toNat =
      xorEvalList α ((tmp.take 2).map BitVec.toNat))
    (hv1 : ∀ α, F.Sat α → evalLitVal α lhs'.toNat = true) :
    LitEquiv F (tmp[0]'h0 ^^^ 1#32).toNat (tmp[1]'h1).toNat := by
  refine ev_litEquiv_of_eval fun α hα => ?_
  have h := hev α hα
  rw [hv1 α hα, t1_take_two tmp h0 h1, List.map_cons, List.map_singleton, xorEvalList_pair] at h
  rw [bv32_xor1_eq_litNeg, evalLitVal_litNeg]
  cases h0e : evalLitVal α (tmp[0]'h0).toNat <;>
    cases h1e : evalLitVal α (tmp[1]'h1).toNat <;>
    rw [h0e, h1e] at h <;> first | rfl | (exfalso; revert h; decide)

private theorem t1_j74_pair1 {F : CNF Nat} {lhs' : BitVec 32}
    {tmp : List (BitVec 32)} (h0 : 0 < tmp.length) (h1 : 1 < tmp.length)
    (hev : ∀ α, F.Sat α → evalLitVal α lhs'.toNat =
      xorEvalList α ((tmp.take 2).map BitVec.toNat))
    (hv0 : ∀ α, F.Sat α → evalLitVal α lhs'.toNat = false) :
    LitEquiv F (tmp[0]'h0).toNat (tmp[1]'h1).toNat := by
  refine ev_litEquiv_of_eval fun α hα => ?_
  have h := hev α hα
  rw [hv0 α hα, t1_take_two tmp h0 h1, List.map_cons, List.map_singleton, xorEvalList_pair] at h
  cases h0e : evalLitVal α (tmp[0]'h0).toNat <;>
    cases h1e : evalLitVal α (tmp[1]'h1).toNat <;>
    rw [h0e, h1e] at h <;> first | rfl | (exfalso; revert h; decide)

private theorem t1_evHashGateOk {maxA : Nat} {F_cur : List (List Nat)} {cv0 : Nat}
    {gtype har' lhs' : BitVec 32} {tmp : List (BitVec 32)}
    (hlhs : lhs'.toNat < 2 * cv0) (hcv : har'.toNat ≤ cv0) (hmax : har'.toNat ≤ maxA)
    (h2 : 2 ≤ har'.toNat) (h4 : har'.toNat ≤ 4)
    (hlt : ∀ k < har'.toNat, (tmp[k]?.getD 0#32).toNat < 2 * cv0)
    (hev : ∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α →
      evalLitVal α lhs'.toNat = xorEvalList α ((tmp.take har'.toNat).map BitVec.toNat))
    (hg : gtype = 1#32) :
    EvHashGateOk maxA F_cur cv0 gtype gtype har' lhs' tmp :=
  ⟨hlhs, hcv, hmax, h2, hlt, Or.inl rfl, fun h => absurd (hg.symm.trans h) (by decide),
   fun _ => ⟨h4, hev⟩, fun h => absurd (hg.symm.trans h) (by decide), Or.inr (Or.inl hg)⟩

public section

/-- Canonical WP proof for the XOR gate branch `evTag1Expr`. -/
theorem ev_tag1_wp (Γ : Env)
    (hSort : Γ.Has "full_sort_u32" fullSortU32Spec)
    (hUnit : Γ.Has "full_cong_unit_fold" Spec.fullCongUnitFoldSpec)
    (hEquiv : Γ.Has "full_cong_equiv_fold" Spec.fullCongEquivFoldSpec)
    (hEnq : Γ.Has "full_cong_enq_var" Spec.fullCongEnqVarSpec)
    {maxA : Nat} {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {cv0 : Nat}
    {fl0 : BitVec 64} {ar0 : List (BitVec 32)} {arl0 g_len ht_off ht_sz g_n : Nat}
    {scr0 scr_in : List (BitVec 32)} {s0 : FullState} {m0 : Mem 64}
    {ctrl_off : BitVec 64} {next_ep arity gtype lhs lhs0 : BitVec 32}
    {J39 : Cont [i32, i32, i32, i32, .bool, .bool]} {J40 : Cont []}
    {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost}
    (hg_ht : g_len ≤ ht_off) (har_cv : arity.toNat ≤ cv0) (har_max : arity.toNat ≤ maxA)
    (hscr_ge : g_n + 2 + arity.toNat ≤ scr0.length)
    (hlhs_lt : lhs.toNat < 2 * cv0) (hlhs_eqv : LitEquiv (cnfOfClauses F_cur) lhs0.toNat lhs.toNat)
    (hxor0 : gtype = 1#32 → 2 ≤ arity.toNat → arity.toNat ≤ 4 →
      XorListGateDef (cnfOfClauses F_cur) lhs0.toNat
        (((scr0.drop (g_n + 2)).take arity.toNat).map BitVec.toNat))
    (htmp_i : ∀ k < arity.toNat, (s0.core.tmp[k]?.getD 0#32).toNat < 2 * cv0 ∧
      LitEquiv (cnfOfClauses F_cur) (scr0[g_n + 2 + k]?.getD 0#32).toNat
        (s0.core.tmp[k]?.getD 0#32).toNat)
    (hok0 : EvCoreOk maxA c F0 F_cur cv0 fl0 ar0 arl0 g_len ctrl_off.toNat ht_off ht_sz
      scr0 scr_in s0)
    (hm0 : (FullMem c s0 ⋆ R) m0)
    (hQ2 : ∀ s' m', EvCoreOk maxA c F0 F_cur cv0 fl0 ar0 arl0 g_len ctrl_off.toNat ht_off ht_sz
      scr0 scr_in s' → F0.Unsat → (FullMem c s' ⋆ R) m' → Q (2#64, ()) m')
    (hJ39 : ∀ lhs' iw har' nh' ch' s' m',
      EvCoreOk maxA c F0 F_cur cv0 fl0 ar0 arl0 g_len ctrl_off.toNat ht_off ht_sz scr0 scr_in s' →
      (nh' = true → EvHashGateOk maxA F_cur cv0 gtype gtype har' lhs' s'.core.tmp) →
      (FullMem c s' ⋆ R) m' → J39 (lhs', iw, gtype, har', nh', ch', ()) m')
    (hJ40 : (gtype ≠ 1#32 ∨ arity.toNat < 2 ∨ 4 < arity.toNat) → J40 () m0) :
    wp Γ Q X (evTag1Expr c.hdr ctrl_off c.pTmp c.pVals next_ep arity gtype lhs J39 J40) m0 := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hw0 := hok0.1.2.1; have hcl0 := hok0.1.2.2.2.2.2.1
  have hcv_eq := hok0.2.1; have hcv_le : cv0 ≤ c.max_vars := hcv_eq ▸ hok0.1.1.core_ok.cur_vars_le
  have htmpl0 := hok0.1.1.core_ok.tmp_len_arr; have hvlen0 := hok0.1.1.core_ok.vals_len
  unfold evTag1Expr; ev_split
  rotate_left; · ev_steps; exact hJ40 (Or.inl hc)
  have hgtype : gtype = 1#32 := hc; clear hc; ev_split
  rotate_left
  · ev_steps
    exact hJ40 (Or.inr (Or.inl (by revert hc; exact fun h => Nat.lt_of_not_ge (by simpa using h))))
  have har_ge2 : 2 ≤ arity.toNat := by simpa using hc
  clear hc; ev_split
  rotate_left
  · ev_steps
    exact hJ40 (Or.inr (Or.inr (by revert hc; exact fun h => Nat.lt_of_not_ge (by simpa using h))))
  have har_le4 : arity.toNat ≤ 4 := by simpa using hc
  clear hc
  let raw := s0.core.tmp.take arity.toNat
  have hraw_len : raw.length = arity.toNat := by simp only [raw, List.length_take]; omega
  have hraw_lt : ∀ k < arity.toNat, (raw[k]?.getD 0#32).toNat < 2 * cv0 := fun k hk => by
    have h := (htmp_i k hk).1; simpa only [raw, List.getElem?_take_of_lt hk] using h
  have hlhs_xor : ∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α →
      evalLitVal α lhs.toNat = xorEvalList α (raw.map BitVec.toNat) :=
    t1_eval_raw_equiv hlhs_eqv (hxor0 hgtype har_ge2 har_le4) hscr_ge (by omega)
      fun k hk => (htmp_i k hk).2
  ev_steps_ng
  refine wp_loop_inv (ts := [i32, i32, i32]) (T1J44Inv c F_cur cv0 s0 arity lhs raw R)
    (fun (il, _, _, ()) _ => arity.toNat - il.toNat)
    (fun _ hJ44 => by
      ev_steps; exact hJ44 (0#32, 0#32, 0#32, ()) m0 ⟨Nat.zero_le _, Nat.zero_le _, Or.inl rfl,
        s0.core.tmp, htmpl0, fun j _ hj => by simp only [raw, List.getElem?_take_of_lt hj],
        fun _ h => absurd h (Nat.not_lt_zero _),
        fun α hα => by simp [hlhs_xor α hα, xorEvalList_nil], hm0⟩) ?_
  rintro _ ⟨il, fl, na, ⟨⟩⟩ ml ⟨hil_le, hna_le, hfl_eq, tmpl, htl_l, htail_l, htmp_lt, hev_l, hml⟩
    ih44
  let sl : FullState := { s0 with core := { s0.core with tmp := tmpl } }
  ev_split
  · have hil_lt : il.toNat < arity.toNat := by omega
    have hil_arr : il.toNat < tmpl.length := by omega
    have hil_raw : il.toNat < raw.length := by omega
    have hr_eq : tmpl[il.toNat]'hil_arr = raw[il.toNat]'hil_raw := by
      have h1 := (htail_l il.toNat (Nat.le_refl _) hil_lt).trans (List.getElem?_eq_getElem hil_raw)
      rw [List.getElem?_eq_getElem hil_arr] at h1; exact Option.some.inj h1
    have hr_lt : (raw[il.toNat]'hil_raw).toNat < 2 * cv0 := by
      simpa [List.getElem?_eq_getElem hil_raw] using hraw_lt il.toNat hil_lt
    have hr_vals' : (raw[il.toNat]'hil_raw).toNat < s0.core.vals.length := by omega
    have hr_vals : (tmpl[il.toNat]'hil_arr).toNat < s0.core.vals.length := hr_eq ▸ hr_vals'
    have hrv_get : s0.core.vals[(tmpl[il.toNat]'hil_arr).toNat]'hr_vals =
        s0.core.vals[(raw[il.toNat]'hil_raw).toNat]'hr_vals' :=
      list_getElem_congr (by rw [hr_eq]) hr_vals hr_vals'
    have hrv_dom : s0.core.vals[(raw[il.toNat]'hil_raw).toNat]'hr_vals' = 0#8 ∨
        s0.core.vals[(raw[il.toNat]'hil_raw).toNat]'hr_vals' = 1#8 ∨
        s0.core.vals[(raw[il.toNat]'hil_raw).toNat]'hr_vals' = 0xFF#8 := by
      have h := hw0.vals_domain (raw[il.toNat]'hil_raw).toNat (hcv_eq.symm ▸ hr_lt)
      rwa [List.getElem?_eq_getElem hr_vals', Option.getD_some] at h
    have hr_1 : s0.core.vals[(raw[il.toNat]'hil_raw).toNat]?.getD 0#8 = 1#8 →
        ∀ α, (cnfOfClauses F_cur).Sat α → evalLitVal α (raw[il.toNat]'hil_raw).toNat = true :=
      fun hv _ hα => entails_eval_true (vals1_entails hw0 hcl0 (hcv_eq.symm ▸ hr_lt) hv) hα
    have hr_ff : s0.core.vals[(raw[il.toNat]'hil_raw).toNat]?.getD 0#8 = 0xFF#8 →
        ∀ α, (cnfOfClauses F_cur).Sat α →
          evalLitVal α (raw[il.toNat]'hil_raw).toNat = false := fun hv _ hα =>
      entails_neg_eval_false (valsff_entails_neg hw0 hcl0 (hcv_eq.symm ▸ hr_lt) hv) hα
    have hil1 : (il + 1#32).toNat = il.toNat + 1 := bv32_add1_lt_of (by omega)
    have hna1 : (na + 1#32).toNat = na.toNat + 1 := bv32_add1_lt_of (by omega)
    have hdrop_r : raw.drop il.toNat = raw[il.toNat]'hil_raw :: raw.drop (il.toNat + 1) :=
      List.drop_eq_getElem_cons hil_raw
    clear hc; ev_steps_ng
    refine wp_join_group (ts := [i32, i32])
      (fun (fl', na', ()) ml' => na'.toNat ≤ il.toNat + 1 ∧ (fl' = 0#32 ∨ fl' = 1#32) ∧
        ∃ t' : List (BitVec 32), t'.length = c.max_vars ∧
          (∀ j, il.toNat + 1 ≤ j → j < arity.toNat → t'[j]? = raw[j]?) ∧
          (∀ j < na'.toNat, (t'[j]?.getD 0#32).toNat < 2 * cv0) ∧
          (∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α →
            evalLitVal α lhs.toNat =
              ((xorEvalList α ((t'.take na'.toNat).map BitVec.toNat) !=
                xorEvalList α ((raw.drop (il.toNat + 1)).map BitVec.toNat)) !=
                decide (fl' = 1#32))) ∧
          (FullMem c { s0 with core := { s0.core with tmp := t' } } ⋆ R) ml')
      (fun _ ⟨fl', na', ⟨⟩⟩ ml' ⟨hnal, hfl', t', htl', htl_tail, htl_lt, htl_ev, hml'⟩ => by
        ev_steps; exact ih44 (il + 1#32, fl', na', ()) ml' (by dsimp only; rw [hil1]; omega)
          ⟨by omega, by rw [hil1]; exact hnal, hfl', t', htl', fun j hj => htl_tail j (by omega),
           htl_lt, fun α hα => by rw [hil1]; exact htl_ev α hα, hml'⟩) ?_
    intro J56 hJ56; ev_split
    · have hne_c := hc; clear hc; ev_steps_ng
      refine wp_join_group (ts := [i32])
        (fun (fl', ()) mf => mf = ml ∧ (fl' = 0#32 ∨ fl' = 1#32) ∧
          ∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α →
            evalLitVal α lhs.toNat =
              ((xorEvalList α ((tmpl.take na.toNat).map BitVec.toNat) !=
                xorEvalList α ((raw.drop (il.toNat + 1)).map BitVec.toNat)) !=
                decide (fl' = 1#32)))
        (fun _ ⟨fl', ⟨⟩⟩ mf ⟨hmf, hfl', hev'⟩ => by
          subst mf; ev_steps; exact hJ56 (fl', na, ()) ml ⟨by omega, hfl', tmpl, htl_l,
            fun j hj => htail_l j (by omega), htmp_lt, hev', hml⟩) ?_
      intro J61 hJ61; ev_split
      · have hsgt : (0#32 : BitVec 32).slt
            ((s0.core.vals[(raw[il.toNat]'hil_raw).toNat]'hr_vals').signExtend 32) = true := by
          simpa only [← hrv_get, show (0#32 : BitVec 32) = BitVec.ofNat 32 0 from rfl] using hc
        have h1_ev := hr_1 (by
          rw [List.getElem?_eq_getElem hr_vals', Option.getD_some]
          exact bv8_eq1_of_signExtend32_sgt0 hrv_dom hsgt)
        ev_steps; refine hJ61 (fl ^^^ 1#32, ()) ml ⟨rfl, ?_, fun α hα => ?_⟩
        · rcases hfl_eq with rfl | rfl <;> simp
        · exact t1_j61_flip_eval hfl_eq (h1_ev α hα)
            (by simpa only [hdrop_r, List.map_cons, xorEvalList_cons] using hev_l α hα)
      · have hne0 : (s0.core.vals[(raw[il.toNat]'hil_raw).toNat]'hr_vals').signExtend 32 ≠
            0#32 := by
          simpa only [← hrv_get, show (0#32 : BitVec 32) = BitVec.ofNat 32 0 from rfl] using hne_c
        have hnsgt : ¬ (0#32 : BitVec 32).slt
            ((s0.core.vals[(raw[il.toNat]'hil_raw).toNat]'hr_vals').signExtend 32) = true := by
          intro h; rw [← hrv_get] at h
          rw [show (0#32 : BitVec 32) = BitVec.ofNat 32 0 from rfl] at h
          rw [h] at hc; cases hc
        have hff_ev := hr_ff (by
          rw [List.getElem?_eq_getElem hr_vals', Option.getD_some]
          exact bv8_ne0_not_signExtend32_sgt0_eqff hrv_dom (bv8_ne0_of_signExtend32 hrv_dom hne0)
            hnsgt)
        ev_steps; refine hJ61 (fl, ()) ml ⟨rfl, hfl_eq, fun α hα => ?_⟩
        have h1 := hev_l α hα
        rw [hdrop_r, List.map_cons, xorEvalList_cons, hff_ev α hα, Bool.false_bne] at h1
        exact h1
    · have hna_arr : (na.setWidth 64).toNat < tmpl.length := by rw [bv_zext32_toNat]; omega
      have hr_eq_zw : tmpl[(il.setWidth 64).toNat]'(by rw [bv_zext32_toNat]; omega) =
          raw[il.toNat]'hil_raw := by
        simpa only [bv_zext32_toNat] using hr_eq
      clear hc; ev_steps
      rw [hr_eq_zw, show (1 : BitVec 32) = 1#32 from rfl]
      refine hJ56 (fl ^^^ (raw[il.toNat]'hil_raw &&& 1#32), na + 1#32, ()) m
        ⟨by omega,
         by rcases hfl_eq with rfl | rfl <;>
              rcases ev_bv32_and1_eq01 (raw[il.toNat]'hil_raw) with h | h <;> simp [h],
         tmpl.set na.toNat (raw[il.toNat]'hil_raw &&& ~~~1#32), by simp [htl_l],
         (fun j hj1 hj2 => by
           rw [List.getElem?_set_ne (by omega)]; exact htail_l j (by omega) hj2),
         (fun j hj => by
           rw [hna1] at hj; by_cases hjn : j = na.toNat
           · subst hjn; rw [List.getElem?_set_self (by omega), Option.getD_some]
             exact t1_bv32_and_not1_lt hr_lt
           · rw [List.getElem?_set_ne (Ne.symm hjn)]; exact htmp_lt j (by omega)),
         (fun α hα => by
           rw [hna1]; exact t1_j56_step_eval (by omega) hil_raw hfl_eq (hev_l α hα)),
         by dsimp only [sl] at hm
            simpa only [bv_zext32_toNat, hr_eq, show (~~~1 : BitVec 32) = ~~~1#32 from rfl]
              using hm⟩
  -- Loop exit (`il = arity`)
  clear ih44
  have hil_eq : il.toNat = arity.toNat := by omega
  have hna_le_ar : na.toNat ≤ arity.toNat := by omega
  let lhs' := lhs ^^^ fl
  have hlhs'_lt : lhs'.toNat < 2 * cv0 := ev_xor1_bit01_lt hlhs_lt hfl_eq
  have hlhs'_ev : ∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α →
      evalLitVal α lhs'.toNat = xorEvalList α ((tmpl.take na.toNat).map BitVec.toNat) :=
    fun α hα => by
      have h1 := hev_l α hα
      rw [hil_eq, show raw.drop arity.toNat = [] from List.drop_of_length_le (by omega),
        List.map_nil, xorEvalList_nil, Bool.bne_false] at h1
      rw [t1_xor_eval_flip_lhs α lhs fl hfl_eq, h1]
      cases xorEvalList α ((tmpl.take na.toNat).map BitVec.toNat) <;>
        cases decide (fl = 1#32) <;> rfl
  let P_t1 := T1Out maxA c F0 F_cur cv0 fl0 ar0 arl0 g_len ctrl_off.toNat ht_off ht_sz scr0 scr_in
    gtype lhs' R
  clear hc; ev_steps_ng
  refine wp_join_group (ts := [])
    (fun () ms => ∃ tmps : List (BitVec 32), tmps.length = c.max_vars ∧
      (∀ j < na.toNat, (tmps[j]?.getD 0#32).toNat < 2 * cv0) ∧
      (∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α →
        evalLitVal α lhs'.toNat = xorEvalList α ((tmps.take na.toNat).map BitVec.toNat)) ∧
      (FullMem c { s0 with core := { s0.core with tmp := tmps } } ⋆ R) ms) ?_ ?_
  · rintro _ ⟨⟩ ms ⟨tmps, htl_s, htmps_lt, htmps_ev, hms⟩
    ev_steps_ng
    refine wp_loop_inv (ts := [i32, i32]) (T1J51Inv c F_cur cv0 s0 na lhs' tmps R)
      (fun (si, _, ()) _ => na.toNat - si.toNat)
      (fun _ hJ51 => by
        ev_steps; exact hJ51 (0#32, 0#32, ()) ms ⟨Nat.zero_le _, Nat.zero_le _, tmps, htl_s,
          fun _ _ _ => rfl, fun _ h => absurd h (Nat.not_lt_zero _),
          fun α hα => by simp [htmps_ev α hα, xorEvalList_nil],
          hms⟩) ?_
    rintro _ ⟨si, ua, ⟨⟩⟩ md ⟨hsi_le, hua_le, tmpd, htl_d, htail_d, htmpd_lt, hev_d, hmd⟩ ih51
    let sd : FullState := { s0 with core := { s0.core with tmp := tmpd } }
    ev_split
    · have hsi_lt : si.toNat < na.toNat := by omega
      have hna_tmps : na.toNat ≤ tmps.length := by omega
      have hna_tmpd : na.toNat ≤ tmpd.length := by omega
      have hsi1 : (si + 1#32).toNat = si.toNat + 1 := bv32_add1_lt_of (by omega)
      have hua1 : (ua + 1#32).toNat = ua.toNat + 1 := bv32_add1_lt_of (by omega)
      have hsi_arr : (si.setWidth 64).toNat < tmpd.length := by rw [bv_zext32_toNat]; omega
      have hcur_eq : tmpd[(si.setWidth 64).toNat]'hsi_arr = tmps[si.toNat]'(by omega) := by
        have h1 := (htail_d si.toNat (Nat.le_refl _) hsi_lt).trans
          (List.getElem?_eq_getElem (by omega))
        rw [List.getElem?_eq_getElem (by omega)] at h1
        exact (list_getElem_congr (bv_zext32_toNat si) hsi_arr (by omega)).trans
          (Option.some.inj h1)
      ev_steps_ng
      refine wp_join_group (ts := [i32, i32])
        (fun (si', ua', ()) md' => si.toNat < si'.toNat ∧
          T1J51Inv c F_cur cv0 s0 na lhs' tmps R (si', ua', ()) md')
        (fun _ ⟨si', ua', ⟨⟩⟩ md' ⟨hgt, h1⟩ => by
          ev_steps; exact ih51 (si', ua', ()) md' (by dsimp only; omega) h1) ?_
      intro J55 hJ55; ev_steps_ng
      refine wp_join_group (ts := [])
        (fun () md' => md' = md ∧ ∀ hsi1_na : si.toNat + 1 < na.toNat,
          tmps[si.toNat]'(Nat.lt_of_lt_of_le hsi_lt hna_tmps) ≠
          tmps[si.toNat + 1]'(Nat.lt_of_lt_of_le hsi1_na hna_tmps)) ?_ ?_
      · rintro _ ⟨⟩ md' ⟨hm', hneq⟩; subst md'
        have hua_arr : (ua.setWidth 64).toNat < tmpd.length := by rw [bv_zext32_toNat]; omega
        have hua_tmpd : ua.toNat < tmpd.length :=
          Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt hua_le hsi_lt) hna_tmpd
        have hsi_tmps : si.toNat < tmps.length := Nat.lt_of_lt_of_le hsi_lt hna_tmps
        have hcur_eq' : tmpd[si.toNat]'(by omega) = tmps[si.toNat]'hsi_tmps := by
          simpa only [bv_zext32_toNat] using hcur_eq
        ev_steps
        exact hJ55 (si + 1#32, ua + 1#32, ()) m ⟨by rw [hsi1]; omega, by rw [hsi1]; omega,
          by rw [hsi1, hua1]; omega,
          tmpd.set ua.toNat (tmps[si.toNat]'hsi_tmps), by simp [htl_d],
          (fun j hj1 hj2 => by
            rw [hsi1] at hj1; rw [List.getElem?_set_ne (by omega)]; exact htail_d j (by omega) hj2),
          (fun j hj => by
            rw [hua1] at hj; by_cases hju : j = ua.toNat
            · subst hju; rw [List.getElem?_set_self hua_tmpd, Option.getD_some]
              have h := htmps_lt si.toNat hsi_lt
              rwa [List.getElem?_eq_getElem hsi_tmps, Option.getD_some] at h
            · rw [List.getElem?_set_ne (Ne.symm hju)]; exact htmpd_lt j (by omega)),
          (fun α hα => by
            rw [hsi1, hua1]
            exact (htmps_ev α hα).trans
              (t1_xor_dedup_keep α hua_tmpd hsi_lt hna_tmps
                ((htmps_ev α hα).symm.trans (hev_d α hα)))),
          by dsimp only [sd] at hm; simpa only [hcur_eq', bv_zext32_toNat] using hm⟩
      · have hsi1' : (si.toNat + (1 : BitVec 32).toNat) % 2 ^ 32 = si.toNat + 1 := hsi1
        intro J56 hJ56; ev_split
        · have hsi1_lt : si.toNat + 1 < na.toNat := by rw [hsi1'] at hc; omega
          have hsi1_tmps : si.toNat + 1 < tmps.length := Nat.lt_of_lt_of_le hsi1_lt hna_tmps
          have hsi_tmps : si.toNat < tmps.length := Nat.lt_of_lt_of_le hsi_lt hna_tmps
          have hsi1_arr : ((si + 1#32).setWidth 64).toNat < tmpd.length := by
            rw [bv_zext32_toNat, hsi1]; omega
          have hcur1_eq : tmpd[((si + 1#32).setWidth 64).toNat]'hsi1_arr =
              tmps[si.toNat + 1]'hsi1_tmps := by
            have h1 := (htail_d (si.toNat + 1) (by omega) hsi1_lt).trans
              (List.getElem?_eq_getElem hsi1_tmps)
            rw [List.getElem?_eq_getElem (by omega)] at h1
            exact (list_getElem_congr (by rw [bv_zext32_toNat, hsi1]) hsi1_arr (by omega)).trans
              (Option.some.inj h1)
          have hsi2 : (si + 2#32).toNat = si.toNat + 2 := ev_bv32_add2_lt_of (by omega)
          clear hc; ev_split
          · have heq : tmps[si.toNat]'hsi_tmps = tmps[si.toNat + 1]'hsi1_tmps := by
              rw [← hcur_eq, ← hcur1_eq]; exact hc
            ev_steps
            exact hJ55 (si + 2#32, ua, ()) md ⟨by rw [hsi2]; omega, by rw [hsi2]; omega,
              by rw [hsi2]; omega, tmpd, htl_d,
              (fun j hj1 hj2 => by rw [hsi2] at hj1; exact htail_d j (by omega) hj2), htmpd_lt,
              (fun α hα => by
                rw [hsi2]
                exact (htmps_ev α hα).trans
                  (t1_xor_dedup_cancel α hsi1_lt hna_tmps heq
                    ((htmps_ev α hα).symm.trans (hev_d α hα)))),
              hmd⟩
          · exact hJ56 () md ⟨rfl, fun _ h => hc (by rw [← hcur_eq, ← hcur1_eq] at h; exact h)⟩
        · exact hJ56 () md ⟨rfl, fun h => by rw [hsi1'] at hc; omega⟩
    · -- Dedup loop exit (`si = na`)
      clear ih51
      have hsi_eq : si.toNat = na.toNat := by omega
      have hua_na : ua.toNat ≤ na.toNat := by omega
      have hokd := evCoreOk_tmp hok0 htl_d
      have hd_ev : ∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α →
          evalLitVal α lhs'.toNat = xorEvalList α ((tmpd.take ua.toNat).map BitVec.toNat) :=
        fun α hα => by
          have h1 := hev_d α hα
          rw [hsi_eq, Nat.sub_self, List.take_zero, List.map_nil, xorEvalList_nil,
            Bool.bne_false] at h1
          exact h1
      clear hc; ev_steps_ng
      refine wp_join_group (ts := [i32, .bool, .bool, i32])
        (fun (iw', nh', ch', har', ()) mj => ∃ sj : FullState,
          EvCoreOk maxA c F0 F_cur cv0 fl0 ar0 arl0 g_len ctrl_off.toNat ht_off ht_sz
            scr0 scr_in sj ∧
          (nh' = true → har' = ua ∧ sj.core.tmp = tmpd) ∧
          (FullMem c sj ⋆ R) mj) ?_ ?_
      · rintro _ ⟨iw', nh', ch', har', ⟨⟩⟩ mj ⟨sj, hokj, hnhj, hmj⟩
        ev_steps_ng
        refine wp_join_group P_t1
          (fun _ ⟨har_o, nh_o, ch_o, ⟨⟩⟩ mk ⟨sk, hokk, hgk, hmk⟩ => by
            ev_steps; exact hJ39 lhs' iw' har_o nh_o ch_o sk mk hokk hgk hmk) ?_
        intro J60 hJ60; ev_split
        rotate_left
        · ev_steps; exact hJ60 (arity, nh', ch', ()) mj
            ⟨sj, hokj, (fun h => absurd h (by simpa using hc)), hmj⟩
        have hnh_t : nh' = true := hc; obtain ⟨hhar, htmp_j⟩ := hnhj hnh_t
        have htmps_j_lt : ∀ k < har'.toNat, (sj.core.tmp[k]?.getD 0#32).toNat < 2 * cv0 := by
          rw [htmp_j, hhar]; exact htmpd_lt
        have hj_ev : ∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α →
            evalLitVal α lhs'.toNat =
              xorEvalList α ((sj.core.tmp.take har'.toNat).map BitVec.toNat) := by
          rw [htmp_j, hhar]; exact hd_ev
        clear hc; ev_steps_ng
        refine wp_join_group P_t1 (fun _ ⟨har_o, nh_o, ch_o, ⟨⟩⟩ mk h => by
          ev_steps; exact hJ60 (har_o, nh_o, ch_o, ()) mk h) ?_
        intro J61 hJ61; ev_split
        · have hua0 : har'.toNat = 0 := by rw [hc]; rfl
          have hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [(lhs' ^^^ 1#32).toNat]) :=
            ev_entails_of_eval fun α hα => by
              have h1 := hj_ev α hα
              rw [hua0, List.take_zero, List.map_nil, xorEvalList_nil] at h1
              rw [bv32_xor1_eq_litNeg, evalLitVal_litNeg, h1]; rfl
          clear hc; ev_steps
          refine ev_unit_wp Γ hUnit hokj (ev_bv32_xor1_lt_cv hlhs'_lt) hent hmj hQ2
            fun ch_u su mu _ _ hoku hmu => by
              ev_steps; exact hJ61 (arity, false, ch_u, ()) mu
                ⟨su, hoku, (fun h => False.elim (Bool.noConfusion h)), hmu⟩
        · have hne0 : har' ≠ 0#32 := hc; clear hc; ev_steps_ng
          refine wp_join_group P_t1 (fun _ ⟨har_o, nh_o, ch_o, ⟨⟩⟩ mk h => by
            ev_steps; exact hJ61 (har_o, nh_o, ch_o, ()) mk h) ?_
          intro J63 hJ63; ev_split
          · have hua1 : har'.toNat = 1 := by rw [hc]; rfl
            have h0_j : 0 < sj.core.tmp.length := by rw [htmp_j]; omega
            have hr0_lt : (sj.core.tmp[0]'h0_j).toNat < 2 * cv0 := by
              have h := htmps_j_lt 0 (by omega); rwa [List.getElem?_eq_getElem h0_j] at h
            have heqv : LitEquiv (cnfOfClauses F_cur) lhs'.toNat (sj.core.tmp[0]'h0_j).toNat :=
              ev_litEquiv_of_eval fun α hα => by
                have h1 := hj_ev α hα
                rwa [hua1, t1_take_one sj.core.tmp h0_j, List.map_singleton, xorEvalList_cons,
                  xorEvalList_nil, Bool.bne_false] at h1
            clear hc; ev_steps
            refine ev_equiv_enq2_wp Γ hEquiv hEnq hg_ht rfl hokj hlhs'_lt hr0_lt heqv hmj hQ2
              fun ch_e se me _ hoke hme => by
                ev_steps; exact hJ63 (arity, false, ch_e, ()) me
                  ⟨se, hoke, (fun h => False.elim (Bool.noConfusion h)), hme⟩
          · have hne1 : har' ≠ 1#32 := hc; clear hc; ev_steps_ng
            refine wp_join_group P_t1 (fun _ ⟨har_o, nh_o, ch_o, ⟨⟩⟩ mk h => by
              ev_steps; exact hJ63 (har_o, nh_o, ch_o, ()) mk h) ?_
            intro J65 hJ65; ev_split
            · have hua2 : har'.toNat = 2 := by rw [hc]; rfl
              have h0_j : 0 < sj.core.tmp.length := by rw [htmp_j]; omega
              have h1_j : 1 < sj.core.tmp.length := by rw [htmp_j]; omega
              have hlv_len : sj.core.vals.length = 2 * c.max_vars := hokj.1.1.core_ok.vals_len
              have hl_v : (lhs'.setWidth 64).toNat < sj.core.vals.length := by
                rw [bv_zext32_toNat, hlv_len]; omega
              have hdom := hokj.1.2.1.vals_domain lhs'.toNat (hokj.2.1.symm ▸ hlhs'_lt)
              have hlev1 : sj.core.vals[lhs'.toNat]?.getD 0#8 = 1#8 →
                  ∀ α, (cnfOfClauses F_cur).Sat α → evalLitVal α lhs'.toNat = true :=
                fun hv _ hα => entails_eval_true
                  (vals1_entails hokj.1.2.1 hokj.1.2.2.2.2.2.1 (hokj.2.1.symm ▸ hlhs'_lt) hv) hα
              have hlevff : sj.core.vals[lhs'.toNat]?.getD 0#8 = 0xFF#8 →
                  ∀ α, (cnfOfClauses F_cur).Sat α → evalLitVal α lhs'.toNat = false :=
                fun hv _ hα => entails_neg_eval_false (valsff_entails_neg
                  hokj.1.2.1 hokj.1.2.2.2.2.2.1 (hokj.2.1.symm ▸ hlhs'_lt) hv) hα
              have hget_v : sj.core.vals[(lhs'.setWidth 64).toNat]'hl_v =
                  sj.core.vals[lhs'.toNat]?.getD 0#8 := by
                rw [List.getElem?_eq_getElem (by rw [hlv_len]; omega), Option.getD_some]
                exact list_getElem_congr (bv_zext32_toNat lhs') _ _
              clear hc; ev_split
              · have hv_ne0 := bv8_ne0_of_signExtend32 hdom (by rw [← hget_v]; exact hc)
                have hlt0 : (sj.core.tmp[0]'h0_j).toNat < 2 * cv0 := by
                  have h := htmps_j_lt 0 (by omega); rwa [List.getElem?_eq_getElem h0_j] at h
                have hlt1 : (sj.core.tmp[1]'h1_j).toNat < 2 * cv0 := by
                  have h := htmps_j_lt 1 (by omega); rwa [List.getElem?_eq_getElem h1_j] at h
                clear hc; ev_steps_ng
                refine wp_join_group (ts := [i32])
                  (fun (a0, ()) ma => ma = mj ∧ a0.toNat < 2 * cv0 ∧
                    LitEquiv (cnfOfClauses F_cur) a0.toNat (sj.core.tmp[1]'h1_j).toNat)
                  (fun _ ⟨a0, ⟨⟩⟩ ma ⟨hma, ha0_lt, heqv⟩ => by
                    subst ma; ev_steps
                    refine ev_equiv_enq2_wp Γ hEquiv hEnq hg_ht rfl hokj ha0_lt hlt1 heqv hmj hQ2
                      fun ch_e se me _ hoke hme => by
                        ev_steps; exact hJ65 (arity, false, ch_e, ()) me
                          ⟨se, hoke, (fun h => False.elim (Bool.noConfusion h)), hme⟩) ?_
                intro J74 hJ74; ev_split
                · have hv1 := hlev1 (bv8_eq1_of_signExtend32_sgt0 hdom (by rw [← hget_v]; exact hc))
                  ev_steps; exact hJ74 (sj.core.tmp[0]'h0_j ^^^ 1#32, ()) mj
                    ⟨rfl, ev_bv32_xor1_lt_cv hlt0,
                      t1_j74_pair0 h0_j h1_j (by rw [hua2] at hj_ev; exact hj_ev) hv1⟩
                · have hnsgt : ¬ (0#32 : BitVec 32).slt
                      ((sj.core.vals[lhs'.toNat]?.getD 0#8).signExtend 32) = true := by
                    intro h; rw [← hget_v] at h
                    have h2 : sj.core.vals[(lhs'.setWidth 64).toNat]'hl_v =
                        sj.core.vals[lhs'.toNat]'(by rw [hlv_len]; omega) :=
                      list_getElem_congr (bv_zext32_toNat lhs') _ _
                    rw [h2] at h
                    change (BitVec.ofNat 32 0).slt
                      (BitVec.signExtend 32 sj.core.vals[(lhs ^^^ fl).toNat]) = true at h
                    rw [h] at hc; cases hc
                  have hvff := hlevff (bv8_ne0_not_signExtend32_sgt0_eqff hdom hv_ne0 hnsgt)
                  ev_steps; exact hJ74 (sj.core.tmp[0]'h0_j, ()) mj
                    ⟨rfl, hlt0,
                      t1_j74_pair1 h0_j h1_j (by rw [hua2] at hj_ev; exact hj_ev) hvff⟩
              · ev_steps; exact hJ65 (har', nh', ch', ()) mj
                  ⟨sj, hokj, fun _ => t1_evHashGateOk hlhs'_lt (by rw [hhar]; omega)
                    (by rw [hhar]; omega) (by omega) (by rw [hhar]; omega)
                    htmps_j_lt hj_ev hgtype, hmj⟩
            · have hne2 : har' ≠ 2#32 := hc
              have hua_ge2 : 2 ≤ har'.toNat := by
                have : har'.toNat ≠ 0 := fun h => hne0 (BitVec.eq_of_toNat_eq h)
                have : har'.toNat ≠ 1 := fun h => hne1 (BitVec.eq_of_toNat_eq h)
                have : har'.toNat ≠ 2 := fun h => hne2 (BitVec.eq_of_toNat_eq h)
                omega
              ev_steps; exact hJ65 (har', nh', ch', ()) mj
                ⟨sj, hokj, fun _ => t1_evHashGateOk hlhs'_lt (by rw [hhar]; omega)
                  (by rw [hhar]; omega) hua_ge2 (by rw [hhar]; omega)
                  htmps_j_lt hj_ev hgtype, hmj⟩
      · intro J55 hJ55
        exact ev_tag1_self_cancel_wp Γ hUnit hEquiv hEnq hg_ht (by omega) (by omega) hlhs'_lt
          htmpd_lt hd_ev hokd hmd hQ2
          fun iw' nh' ch' har' sj mj hokj hnhj hmj => hJ55 (iw', nh', ch', har', ()) mj
            ⟨sj, hokj, hnhj, hmj⟩
  · intro _ hJsort; ev_split
    · clear hc; ev_steps; c0_call hSort
      refine ⟨tmpl, ArrayField.tmp.rest c sl ⋆ R, by omega, focus_full_tmp hml,
        fun tmps ms htl_s hperm_s _ hms => ?_⟩
      have hms' : (FullMem c { s0 with core := { s0.core with tmp := tmps } } ⋆ R) ms :=
        unfocus_full_tmp hms
      obtain ⟨htmps_lt, htmps_ev⟩ := t1_sort_tmp_ok (by omega) hperm_s htmp_lt hlhs'_ev
      ev_steps; exact hJsort () ms ⟨tmps, htl_s.trans htl_l, htmps_lt, htmps_ev, hms'⟩
    · ev_steps; exact hJsort () ml ⟨tmpl, htl_l, htmp_lt, hlhs'_ev, hml⟩

end

end LeanQbe.T.Examples.Kissat.Proof.Congruence
