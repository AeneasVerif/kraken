/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityCongProof0
public import LeanQbe.T.Examples.Kissat.FullM7CongIteProof1
import all LeanQbe.T.Examples.Kissat.FullM7CongIteProof0
import all LeanQbe.T.Examples.Kissat.FullM7CongIteProof1
import LeanQbe.T.Examples.Kissat.FullCongLemmas1
import LeanQbe.T.Examples.Kissat.FullCongLemmas2
import LeanQbe.T.Examples.Kissat.FullDenseWatchLemmas1
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb

/-!
# Kissat 4.0.4 Congruence Parity Proofs — Part 3b (`FullFidelityCongProof3b`)

Proves the 4 parametric `(Γ : Env)` `Func.wp` theorems for `FullFidelityCong.lean` lines 1205-1407:
1. `full_cong_copy_condbin_m7_wp` (`fidCongCopyCondbinLv0Spec`, scanning `sz ≥ 3` clauses skipping
   root-falsified literals via `unassigned_clause_entails`)
2. `full_cong_merge_condeq_m7_wp` (`fidCongMergeCondeqSpec`, emitting `e == t` trivial ITEs)
3. `full_cong_extract_ite_all_m7_wp` (`fidCongExtractIteAllSpec`, polymorphic in `3 ≤ maxA ≤ 64`)
4. `full_congruence_dense_wp` (`m3CongruenceDenseSpec`, dynamic `ht_max ≤ 1M` & `ht_sz` sizing)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityCong

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullCongHelpers
open LeanQbe.T.Examples.Kissat.Full.FullDenseWatchHelpers
open LeanQbe.T.Examples.Kissat.FullM3CongBva (m3CongruenceDenseSpec)
open LeanQbe.T.Examples.Kissat.FullM6CongSubst (m6CongExtractBinariesSpec m6CongFindUnitsEquivsSpec
  m6CongFwdSubsumeSpec unassigned_clause_entails m6_fullDenseInvW_with_repr bv64_add1_lt)
open LeanQbe.T.Examples.Kissat.FullM7CongIte (FullMemNoWks3 SortedRange64 CondBinElemOk
  CondEqElemOk m7U64SortSpec m7U64SortSpec_mk m7ExtractCondeqSpec condBin_of_perm3
  condEq_to_iteGateDef packU64_hi packU64_lo u64_trunc32_hi_eq u64_trunc32_lo_eq
  bv32_ushiftRight_imm1_toNat packU64_eq_lt_rhs packU64_eq_ge_rhs dense_slice_pop_step
  bv64_shl1_bv_toNat bv64_lit0_toNat bv64_lit1_toNat bv64_lit0_xor1 bv64_lit1_xor1
  bv32_zext64_shl1_add1_toNat focus_full_wks3_u64 unfocus_full_wks3_u64
  c0_load_arr64 c0_load_arr64_0 c0_load_arr64_zext0
  c0_store_arr64 c0_store_arr64_0 c0_store_arr64_zext0
  load_noWks3_arena_len load_noWks3_vals_ptr load_noWks3_wvec_ptr
  load_noWks3_arena_ptr load_noWks3_wstk_ptr load_noWks3_flags_ptr
  load_noWks3_work_stk1_ptr load_noWks3_work_stk2_ptr
  load_noWks3_scratch_buf_ptr load_noWks3_scratch_cap
  c0_load_noWks3_vals c0_load_noWks3_flags c0_load_noWks3_wvec
  c0_load_noWks3_wstk c0_load_noWks3_arena c0_store_noWks3_scratch_buf)
open LeanQbe.T.Examples.Kissat.FullM8FidV12 (M8CtrlLayout)
open Kraken.Bedrock2.Test
open scoped FullArenaTactics Full.FullCongTactics
open scoped LeanQbe.T.Examples.Kissat.FullM6CongSubst.M6bHeadTactics

/-! ## 1. Level-0 `copy_condbin` Spec & Pure Semantic Helpers -/

/-- Level-0 contract for `full_cong_copy_condbin_m7` (`GAP-CONG-04`): strengthens
`m7CopyCondbinSpec` with `s.core.cur_level = 0` so skipping falsified literals (`vals[l] < 0`)
in `sz ≥ 3` clauses is sound via `unassigned_clause_entails`. -/
@[expose] def fidCongCopyCondbinLv0Spec : Spec [i64, i32, i64, i64] [i64] :=
  fun (h, lit, out, cap, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : Std.Sat.CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (out0 : List (BitVec 64)) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
      s.core.cur_level = 0 ∧ s.core.dense_mode ≠ 0#64 ∧
      lit.toNat < 2 * s.core.cur_vars ∧
      out0.length = cap.toNat ∧ cap.toNat < 2 ^ 61 ∧
      (FullMemNoWks3 c s ⋆ array64 out out0 ⋆ R) m ∧
      ∀ (cnt : BitVec 64) (out' : List (BitVec 64)) m',
        out'.length = cap.toNat →
        cnt.toNat ≤ cap.toNat →
        SortedRange64 out' 0 cnt.toNat →
        (∀ k < cnt.toNat, CondBinElemOk F_cur s.core.cur_vars lit.toNat (out'[k]?.getD 0#64)) →
        (FullMemNoWks3 c s ⋆ array64 out out' ⋆ R) m' →
        Q (cnt, ()) m'

theorem fidCongCopyCondbinLv0Spec_mk {c F0 F_cur s out cap m Q X} {lit : BitVec 32}
    (out0 : List (BitVec 64)) (R : Mem 64 → Prop)
    (h1 : s.LengthsOk c) (h2 : FullWitnessInv c F0 F_cur s.core)
    (hcl0 : s.core.cur_level = 0) (h3 : s.core.dense_mode ≠ 0#64)
    (h4 : lit.toNat < 2 * s.core.cur_vars)
    (h5 : out0.length = cap.toNat) (h6 : cap.toNat < 2 ^ 61)
    (h7 : (FullMemNoWks3 c s ⋆ array64 out out0 ⋆ R) m)
    (hQ : ∀ cnt out' m', out'.length = cap.toNat → cnt.toNat ≤ cap.toNat →
      SortedRange64 out' 0 cnt.toNat →
      (∀ k < cnt.toNat, CondBinElemOk F_cur s.core.cur_vars lit.toNat (out'[k]?.getD 0#64)) →
      (FullMemNoWks3 c s ⋆ array64 out out' ⋆ R) m' → Q (cnt, ()) m') :
    fidCongCopyCondbinLv0Spec (c.hdr, lit, out, cap, ()) m Q X :=
  ⟨c, F0, F_cur, s, out0, R, rfl, h1, h2, hcl0, h3, h4, h5, h6, h7, hQ⟩

section IteHelpers

private theorem condBin_of_entails3 {F_cur : List (List Nat)} {cur_vars : Nat}
    {lit a b : BitVec 32}
    (hcl : (cnfOfClauses F_cur).EntailsClause (cnfClause [lit.toNat, a.toNat, b.toNat]))
    (ha : a.toNat < 2 * cur_vars) (hb : b.toNat < 2 * cur_vars)
    (h1 : a.toNat / 2 ≠ b.toNat / 2) (h2 : a.toNat / 2 ≠ lit.toNat / 2)
    (h3 : b.toNat / 2 ≠ lit.toNat / 2) :
    CondBinElemOk F_cur cur_vars lit.toNat
      (((if b.ult a then b else a).setWidth 64 <<< 32#64) |||
        (if b.ult a then a else b).setWidth 64) :=
  condBin_of_perm3 hcl (Or.inl ⟨rfl, rfl, rfl⟩) ha hb h1 h2 h3

private theorem fidGateAt_ite_append {maxA : Nat} {F_cur : List (List Nat)} {cur_vars : Nat}
    {scr0 scr1 : List (BitVec 32)} {g_len : Nat} {y c t e : BitVec 32}
    (hmaxA : 3 ≤ maxA) (hcv : 3 ≤ cur_vars)
    (hy : y.toNat < 2 * cur_vars) (hc : c.toNat < 2 * cur_vars)
    (ht : t.toNat < 2 * cur_vars) (he : e.toNat < 2 * cur_vars)
    (hite : IteGateDef (cnfOfClauses F_cur) y.toNat c.toNat t.toNat e.toNat)
    (hlen0 : g_len + 5 ≤ scr0.length)
    (hscr1 : scr1 = ((((scr0.set g_len y).set (g_len + 1)
      ((2#32 <<< 28#32) ||| 3#32)).set (g_len + 2) c).set (g_len + 3) t).set (g_len + 4) e)
    (hseq0 : FidGateSeqOk maxA F_cur cur_vars scr0 g_len 0) :
    scr1.length = scr0.length ∧ (∀ idx < g_len, scr1[idx]? = scr0[idx]?) ∧
    FidGateSeqOk maxA F_cur cur_vars scr1 (g_len + 5) 0 := by
  have hlen1 : scr1.length = scr0.length := by subst scr1; simp only [List.length_set]
  have hpref : ∀ idx < g_len, scr1[idx]? = scr0[idx]? := fun idx hidx => by
    subst scr1; repeat rw [List.getElem?_set_ne (by omega)]
  have hg0 : scr1[g_len]? = some y := by
    subst scr1; repeat rw [List.getElem?_set_ne (by omega)]
    exact List.getElem?_set_self (by omega)
  have hmword : scr1[g_len + 1]? = some ((2#32 <<< 28#32) ||| 3#32) := by
    subst scr1; repeat rw [List.getElem?_set_ne (by omega)]
    exact List.getElem?_set_self (by simp; omega)
  have hg2 : scr1[g_len + 2]? = some c := by
    subst scr1; repeat rw [List.getElem?_set_ne (by omega)]
    exact List.getElem?_set_self (by simp; omega)
  have hg3 : scr1[g_len + 3]? = some t := by
    subst scr1; rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by simp; omega)]
  have hg4 : scr1[g_len + 4]? = some e := by
    subst scr1; exact List.getElem?_set_self (by simp; omega)
  have htag : (((2#32 <<< 28#32) ||| 3#32) >>> 28).toNat = 2 := by decide
  have har : (((2#32 <<< 28#32) ||| 3#32) &&& 0xFF#32).toNat = 3 := by decide
  have hgat : FidGateAt maxA F_cur cur_vars scr1 (g_len + 5) g_len := by
    refine ⟨y, (2#32 <<< 28#32) ||| 3#32, hg0, hmword, hy, ?_⟩
    dsimp only; rw [htag, har]
    refine ⟨Nat.le_refl _, hcv, hmaxA, fun k hk => ?_, Or.inr (Or.inr ⟨rfl, rfl, ?_⟩)⟩
    · rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl
      · exact ⟨c, hg2, hc⟩
      · exact ⟨t, hg3, ht⟩
      · exact ⟨e, hg4, he⟩
    · simpa [hg2, hg3, hg4] using hite
  have hnew : FidGateSeqOk maxA F_cur cur_vars scr1 (g_len + 5) g_len := by
    refine FidGateSeqOk.step hgat ?_
    rw [hmword, Option.getD_some, har]; exact FidGateSeqOk.done
  exact ⟨hlen1, hpref, fidGateSeqOk_append_gate hpref hseq0 hnew (by omega)⟩

private theorem merge_condeq_fidgate_ok {maxA : Nat} {F_cur : List (List Nat)} {cur_vars : Nat}
    {scr scr1 : List (BitVec 32)} {g_len cond : Nat} {pv nv : BitVec 64}
    {y t e yy tt ee : BitVec 32}
    (hmaxA : 3 ≤ maxA) (hcv : 3 ≤ cur_vars) (hcond : cond < 2 * cur_vars)
    (hw1 : CondEqElemOk F_cur cur_vars (litNeg cond) pv)
    (hw2 : CondEqElemOk F_cur cur_vars cond nv)
    (hy : y = (pv >>> (32 : Nat)).setWidth 32)
    (ht : t = pv.setWidth 32) (he : e = nv.setWidth 32)
    (hsame : (nv >>> (32 : Nat)).setWidth 32 = y)
    (hflip : ((t &&& 1#32 = 0#32 → yy = y ∧ tt = t ∧ ee = e) ∧
              (t &&& 1#32 ≠ 0#32 → yy = y ^^^ 1#32 ∧ tt = t ^^^ 1#32 ∧ ee = e ^^^ 1#32)))
    (hc_bd : cond < 2 ^ 32) (hlen0 : g_len + 5 ≤ scr.length)
    (hscr1 : scr1 = ((((scr.set g_len yy).set (g_len + 1)
      ((2#32 <<< 28#32) ||| 3#32)).set (g_len + 2) (BitVec.ofNat 32 cond)).set
      (g_len + 3) tt).set (g_len + 4) ee)
    (hseq0 : FidGateSeqOk maxA F_cur cur_vars scr g_len 0) :
    scr1.length = scr.length ∧ (∀ idx < g_len, scr1[idx]? = scr[idx]?) ∧
    FidGateSeqOk maxA F_cur cur_vars scr1 (g_len + 5) 0 := by
  have hy_n : (pv >>> 32).toNat = y.toNat := by rw [hy]; exact (u64_trunc32_hi_eq pv).symm
  have ht_n : (pv &&& 0xFFFFFFFF#64).toNat = t.toNat := by
    rw [ht]; exact (u64_trunc32_lo_eq pv).symm
  have he_n : (nv &&& 0xFFFFFFFF#64).toNat = e.toNat := by
    rw [he]; exact (u64_trunc32_lo_eq nv).symm
  have hsame_n : (pv >>> 32).toNat = (nv >>> 32).toNat := by
    rw [hy_n, ← hsame]
    change (BitVec.setWidth 32 (nv >>> 32)).toNat = (nv >>> 32).toNat; bv_omega
  have hite := condEq_to_iteGateDef hw1 hw2 hsame_n
  rw [hy_n, ht_n, he_n] at hite
  have hy_lt : y.toNat < 2 * cur_vars := by rw [← hy_n]; exact hw1.1
  have ht_lt : t.toNat < 2 * cur_vars := by rw [← ht_n]; exact hw1.2.1
  have he_lt : e.toNat < 2 * cur_vars := by rw [← he_n]; exact hw2.2.1
  have hc32 : (BitVec.ofNat 32 cond).toNat = cond := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hc_bd
  by_cases hpar : t &&& 1#32 = 0#32
  · obtain ⟨rfl, rfl, rfl⟩ := hflip.1 hpar
    exact fidGateAt_ite_append hmaxA hcv hy_lt (by rw [hc32]; exact hcond) ht_lt he_lt
      (by rw [hc32]; exact hite) hlen0 hscr1 hseq0
  · obtain ⟨rfl, rfl, rfl⟩ := hflip.2 hpar
    have hyy_lt : (y ^^^ 1#32).toNat < 2 * cur_vars := by
      rw [FullCongHelpers.bv32_xor1_eq_litNeg]; exact litNeg_lt_two_mul hy_lt
    have htt_lt : (t ^^^ 1#32).toNat < 2 * cur_vars := by
      rw [FullCongHelpers.bv32_xor1_eq_litNeg]; exact litNeg_lt_two_mul ht_lt
    have hee_lt : (e ^^^ 1#32).toNat < 2 * cur_vars := by
      rw [FullCongHelpers.bv32_xor1_eq_litNeg]; exact litNeg_lt_two_mul he_lt
    have hite' : IteGateDef (cnfOfClauses F_cur)
        (y ^^^ 1#32).toNat cond (t ^^^ 1#32).toNat (e ^^^ 1#32).toNat := by
      simp only [FullCongHelpers.bv32_xor1_eq_litNeg]; exact iteGateDef_flip_out hite
    exact fidGateAt_ite_append hmaxA hcv hyy_lt (by rw [hc32]; exact hcond) htt_lt hee_lt
      (by rw [hc32]; exact hite') hlen0 hscr1 hseq0

private theorem fid_wp_add_vi {rs : List Ty} {Γ : Env} {Q : Post rs} {X : XPost} {m : Mem 64}
    (a n : BitVec 64) (k : Tup Val [i64] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (.mk (.add i64) (.var a, .imm n, ())) k) m =
      wp Γ Q X (k (a + n, ())) m := by rw [wp_let_add_eq]; simp [Ty.hasFloat, lift2]

private theorem fid_wp_add_vv {rs : List Ty} {Γ : Env} {Q : Post rs} {X : XPost} {m : Mem 64}
    (a b : BitVec 64) (k : Tup Val [i64] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (.mk (.add i64) (.var a, .var b, ())) k) m =
      wp Γ Q X (k (a + b, ())) m := by rw [wp_let_add_eq]; simp [Ty.hasFloat, lift2]

private theorem fid_wp_mul_vi {rs : List Ty} {Γ : Env} {Q : Post rs} {X : XPost} {m : Mem 64}
    (a n : BitVec 64) (k : Tup Val [i64] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (.mk (.mul i64) (.var a, .imm n, ())) k) m =
      wp Γ Q X (k (a * n, ())) m := by rw [wp_let_mul_eq]; simp [Ty.hasFloat, lift2]

private theorem fid_wp_shl1_v {rs : List Ty} {Γ : Env} {Q : Post rs} {X : XPost} {m : Mem 64}
    (a : BitVec 64) (k : Tup Val [i64] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (.mk (.shl i64) (.var a, .imm 1, ())) k) m =
      wp Γ Q X (k (a <<< (1 : Nat), ())) m := by rw [wp_let_shl_eq]; simp [Ty.hasFloat, lift2]

private theorem fid_wp_zext_v {rs : List Ty} {Γ : Env} {Q : Post rs} {X : XPost} {m : Mem 64}
    (a : BitVec 32) (k : Tup Val [i64] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (.mk (.zext 32 64) (.var a, ())) k) m =
      wp Γ Q X (k (a.setWidth 64, ())) m := by rw [wp_let_zext_eq]; simp

private def CopyScanOk (s : FullState) (cr lit : BitVec 32)
    (a b ocnt : BitVec 32) (found_lit : Bool) (n : Nat) : Prop :=
  ocnt.toNat ≤ 2 ∧
  (1 ≤ ocnt.toNat → a.toNat < 2 * s.core.cur_vars) ∧
  (ocnt.toNat = 2 → b.toNat < 2 * s.core.cur_vars) ∧
  ∀ q < n,
    let cl := (s.core.arena[cr.toNat + 3 + q]?.getD 0#32).toNat
    s.core.vals[cl]?.getD 0#8 = 0xFF#8 ∨
    (found_lit = true ∧ cl = lit.toNat) ∨
    (1 ≤ ocnt.toNat ∧ cl = a.toNat) ∨
    (ocnt.toNat = 2 ∧ cl = b.toNat)

private theorem copyScanOk_step_lit {s : FullState} {cr lit a b ocnt : BitVec 32} {fl : Bool}
    {k : Nat} (h : CopyScanOk s cr lit a b ocnt fl k)
    (hk : (s.core.arena[cr.toNat + 3 + k]?.getD 0#32).toNat = lit.toNat) :
    CopyScanOk s cr lit a b ocnt true (k + 1) := by
  refine ⟨h.1, h.2.1, h.2.2.1, fun q hq => ?_⟩
  by_cases hqk : q = k
  · subst hqk; exact Or.inr (Or.inl ⟨rfl, hk⟩)
  · rcases h.2.2.2 q (by omega) with h0 | ⟨_, h1⟩ | h2 | h3
    · exact Or.inl h0
    · exact Or.inr (Or.inl ⟨rfl, h1⟩)
    · exact Or.inr (Or.inr (Or.inl h2))
    · exact Or.inr (Or.inr (Or.inr h3))

private theorem copyScanOk_step_a {s : FullState} {cr lit a b ocnt cl : BitVec 32} {fl : Bool}
    {k : Nat} (h : CopyScanOk s cr lit a b ocnt fl k) (hoc0 : ocnt.toNat = 0)
    (hcl : cl.toNat < 2 * s.core.cur_vars)
    (hk : (s.core.arena[cr.toNat + 3 + k]?.getD 0#32).toNat = cl.toNat) :
    CopyScanOk s cr lit cl b 1#32 fl (k + 1) := by
  refine ⟨by decide, fun _ => hcl, fun h => (by cases h), fun q hq => ?_⟩
  by_cases hqk : q = k
  · subst hqk; exact Or.inr (Or.inr (Or.inl ⟨by decide, hk⟩))
  · rcases h.2.2.2 q (by omega) with h0 | h1 | ⟨h2, _⟩ | ⟨h3, _⟩
    · exact Or.inl h0
    · exact Or.inr (Or.inl h1)
    · omega
    · omega

private theorem copyScanOk_step_b {s : FullState} {cr lit a b ocnt cl : BitVec 32} {fl : Bool}
    {k : Nat} (h : CopyScanOk s cr lit a b ocnt fl k) (hoc1 : ocnt.toNat = 1)
    (hcl : cl.toNat < 2 * s.core.cur_vars)
    (hk : (s.core.arena[cr.toNat + 3 + k]?.getD 0#32).toNat = cl.toNat) :
    CopyScanOk s cr lit a cl 2#32 fl (k + 1) := by
  refine ⟨by decide, fun _ => h.2.1 (by omega), fun _ => hcl, fun q hq => ?_⟩
  by_cases hqk : q = k
  · subst hqk; exact Or.inr (Or.inr (Or.inr ⟨rfl, hk⟩))
  · rcases h.2.2.2 q (by omega) with h0 | h1 | ⟨_, h2⟩ | ⟨h3, _⟩
    · exact Or.inl h0
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl ⟨by decide, h2⟩))
    · omega

private theorem copyScanOk_step_ff {s : FullState} {cr lit a b ocnt : BitVec 32} {fl : Bool}
    {k : Nat} (h : CopyScanOk s cr lit a b ocnt fl k)
    (hff : s.core.vals[(s.core.arena[cr.toNat + 3 + k]?.getD 0#32).toNat]?.getD 0#8 = 0xFF#8) :
    CopyScanOk s cr lit a b ocnt fl (k + 1) := by
  refine ⟨h.1, h.2.1, h.2.2.1, fun q hq => ?_⟩
  by_cases hqk : q = k
  · subst hqk; exact Or.inl hff
  · exact h.2.2.2 q (by omega)

end IteHelpers

/-! ## 2. Conditional Binary Extraction, Merge & ITE Driver (`Func.wp`) -/

section IteProofs

attribute [local c0_load] c0_load_arr64 c0_load_arr64_0 c0_load_arr64_zext0
  load_noWks3_arena_len load_noWks3_vals_ptr load_noWks3_wvec_ptr
  load_noWks3_arena_ptr load_noWks3_wstk_ptr load_noWks3_flags_ptr
  load_noWks3_work_stk1_ptr load_noWks3_work_stk2_ptr
  load_noWks3_scratch_buf_ptr load_noWks3_scratch_cap
  c0_load_noWks3_vals c0_load_noWks3_flags c0_load_noWks3_wvec
  c0_load_noWks3_wstk c0_load_noWks3_arena
attribute [local c0_store] c0_store_arr64 c0_store_arr64_0 c0_store_arr64_zext0
  c0_store_noWks3_scratch_buf

theorem full_cong_copy_condbin_m7_wp (Γ : Env)
    (hSort : ∀ a m Q X, m7U64SortSpec a m Q X →
      Γ "full_cong_u64_sort_m7" [i64, i64] [] a m Q X) :
    ∀ args m Q X, fidCongCopyCondbinLv0Spec args m Q X →
      Func.wp Γ full_cong_copy_condbin_m7_body args m Q X := by
  rintro ⟨h, lit, out, cap, ⟨⟩⟩ m0 Q X
    ⟨c, F0, F_cur, s, out0, R, rfl, hlen, hw, hcl0, hdm, hlit_lt, hout_len, hcap_bd, hm0, hQ⟩
  have hmx := c.hmaxv; have hwc := c.hwcap; have hac := c.harena
  unfold dimacsBound at hmx hwc hac
  have hcl := hlen.core_ok
  have hcv_le := hcl.cur_vars_le; have hwvl := hcl.wvec_len
  have hwsl := hcl.wstk_len_arr; have hwle := hcl.wlen_le
  have harl := hcl.arena_len_arr; have hale := hcl.arena_len_le
  have hvl := hcl.vals_len
  have hw_bd := hw.watches.bounds lit.toNat hlit_lt
  have hshl : (lit.setWidth 64 <<< (1 : Nat)).toNat = 2 * lit.toNat := by
    rw [FullCongHelpers.bv64_shl1_toNat, bv_zext32_toNat]; omega
  have hshl1 : (lit.setWidth 64 <<< (1 : Nat) + 1#64).toNat = 2 * lit.toNat + 1 := by
    rw [BitVec.toNat_add, hshl]; show (2 * lit.toNat + 1) % 2 ^ 64 = 2 * lit.toNat + 1; omega
  have hw0_arr : (lit.setWidth 64 <<< (1 : Nat)).toNat < s.core.wvec.length := by omega
  have hw1_arr : (lit.setWidth 64 <<< (1 : Nat) + 1#64).toNat < s.core.wvec.length := by omega
  have hslice0 : DenseWatchSliceOk F_cur s.core lit.toNat (fullWatchOffCore s.core lit.toNat)
      (fullWatchSizeCore s.core lit.toNat) := by
    have hwat := hw.watches; unfold ModeWatchesInv at hwat
    rw [ite_eq_right hdm] at hwat; exact hwat.slices lit.toNat hlit_lt
  have hm0' : (FullMemNoWks3 c s ⋆ (array64 out out0 ⋆ R)) m0 := sep_ac hm0
  unfold Func.wp full_cong_copy_condbin_m7_body; dsimp only
  rw [fid_wp_add_vi]; dsimp only; refine wp_load_of (load_noWks3_wvec_ptr hm0') ?_
  rw [fid_wp_add_vi]; dsimp only; refine wp_load_of (load_noWks3_wstk_ptr hm0') ?_
  rw [fid_wp_add_vi]; dsimp only; refine wp_load_of (load_noWks3_arena_ptr hm0') ?_
  rw [fid_wp_add_vi]; dsimp only; refine wp_load_of (load_noWks3_vals_ptr hm0') ?_
  rw [fid_wp_add_vi]; dsimp only; refine wp_load_of (load_noWks3_arena_len hm0') ?_
  rw [fid_wp_zext_v]; dsimp only; rw [fid_wp_shl1_v]; dsimp only
  rw [fid_wp_mul_vi]; dsimp only; rw [fid_wp_add_vv]; dsimp only
  refine wp_load_of (c0_load_noWks3_wvec hw0_arr hm0') ?_
  rw [fid_wp_zext_v]; dsimp only; rw [fid_wp_add_vi]; dsimp only
  rw [fid_wp_mul_vi]; dsimp only; rw [fid_wp_add_vv]; dsimp only
  refine wp_load_of (c0_load_noWks3_wvec hw1_arr hm0') ?_
  rw [fid_wp_zext_v]; dsimp only; rw [fid_wp_add_vv]; dsimp only
  generalize hoff_v :
    (s.core.wvec[(lit.setWidth 64 <<< (1 : Nat)).toNat]'hw0_arr).setWidth 64 = off
  generalize hwsz_v :
    (s.core.wvec[(lit.setWidth 64 <<< (1 : Nat) + 1#64).toNat]'hw1_arr).setWidth 64 = wsz
  have hoff_n : off.toNat = fullWatchOffCore s.core lit.toNat := by
    rw [← hoff_v, bv_zext32_toNat]; unfold fullWatchOffCore
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    exact congrArg BitVec.toNat (list_getElem_congr hshl hw0_arr (by omega))
  have hwsz_n : wsz.toNat = fullWatchSizeCore s.core lit.toNat := by
    rw [← hwsz_v, bv_zext32_toNat]; unfold fullWatchSizeCore
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    exact congrArg BitVec.toNat (list_getElem_congr hshl1 hw1_arr (by omega))
  have hend_n : (off + wsz).toNat = off.toNat + wsz.toNat := by bv_omega
  refine wp_join_group (ts := [i64, i64])
    (fun (_p, cnt, ()) ml => ∃ out1 : List (BitVec 64),
      out1.length = cap.toNat ∧ cnt.toNat ≤ cap.toNat ∧
      (∀ k < cnt.toNat, CondBinElemOk F_cur s.core.cur_vars lit.toNat (out1[k]?.getD 0#64)) ∧
      (FullMemNoWks3 c s ⋆ array64 out out1 ⋆ R) ml)
    (fun _ ⟨_p, cnt, ⟨⟩⟩ ml ⟨out1, hout1_len, hcnt_le, hcb1, hml⟩ => ?_)
    (fun J0 hJ0 => ?_)
  · -- Post watch-scan: if cnt ≤ 1 return cnt; else sort & dedup
    fc_split_fast
    · have hcnt1 : cnt.toNat ≤ 1 := by
        simp only [BitVec.ule, decide_eq_true_eq] at hc; exact hc
      fc_steps
      refine hQ cnt out1 ml hout1_len hcnt_le (fun i j hi hij hj => ?_) hcb1 hml
      have : i = j := by omega
      subst this; exact BitVec.le_refl _
    · have hcnt_gt1 : 1 < cnt.toNat := by
        simp only [BitVec.ule, decide_eq_false_iff_not, not_le] at hc; exact hc
      have hm_s0 : (array64 out out1 ⋆ (FullMemNoWks3 c s ⋆ R)) ml := sep_ac hml
      refine wp_call_of_spec _ _ (hSort (out, cnt, ()) ml _ X
        (m7U64SortSpec_mk out1 (FullMemNoWks3 c s ⋆ R) (by omega) (by omega) hm_s0
          fun out_s m_s hos_len _hos_tail hos_sub hos_sort hm_s => ?_))
      have hos_cb : ∀ k < cnt.toNat,
          CondBinElemOk F_cur s.core.cur_vars lit.toNat (out_s[k]?.getD 0#64) := by
        intro k hk; obtain ⟨j, hj, hget⟩ := hos_sub k hk
        have hok := hcb1 j hj; rwa [← hget] at hok
      fc_to_group
      refine wp_loop_inv (ts := [i64, i64])
        (fun (u, i, ()) md => ∃ out_d : List (BitVec 64),
          1 ≤ u.toNat ∧ u.toNat ≤ i.toNat ∧ i.toNat ≤ cnt.toNat ∧ out_d.length = cap.toNat ∧
          (∀ k, i.toNat ≤ k → k < cnt.toNat → out_d[k]? = out_s[k]?) ∧
          (∀ k < u.toNat, ∃ j < i.toNat, out_d[k]? = out_s[j]?) ∧
          SortedRange64 out_d 0 u.toNat ∧ (array64 out out_d ⋆ (FullMemNoWks3 c s ⋆ R)) md)
        (fun (_, i, ()) _ => cnt.toNat - i.toNat)
        (fun Jd hJd => by
          fc_steps
          refine hJd (1#64, 1#64, ()) m_s ⟨out_s, Nat.le_refl _, by bv_omega, by bv_omega,
            by omega, fun _ _ _ => rfl, fun k hk => ⟨k, hk, rfl⟩,
            fun i j hi hij hj => by
              have : i = j := (by bv_omega)
              subst this; exact BitVec.le_refl _,
            hm_s⟩)
        (fun Jd ⟨u, i, ⟨⟩⟩ md ⟨out_d, hu1, hui, hic, hod_len, htail_d, hsub_d, hsort_d, hmd⟩ ihd =>
          ?_)
      fc_split_fast
      · have hi_lt : i.toNat < cnt.toNat := by
          simp only [BitVec.ult, decide_eq_true_eq] at hc; exact hc
        have hum1_n : (u - 1#64).toNat = u.toNat - 1 := by bv_omega
        have hi_arr : i.toNat < out_d.length := by omega
        have hum1_arr : (u - 1#64).toNat < out_d.length := by omega
        have hu_arr : u.toNat < out_d.length := by omega
        have hip1_n : (i + 1#64).toNat = i.toNat + 1 := by bv_omega
        fc_to_group
        refine wp_join_group (ts := [i64])
          (fun (u2, ()) md2 => ∃ out_d2 : List (BitVec 64),
            1 ≤ u2.toNat ∧ u2.toNat ≤ i.toNat + 1 ∧ out_d2.length = cap.toNat ∧
            (∀ k, i.toNat + 1 ≤ k → k < cnt.toNat → out_d2[k]? = out_s[k]?) ∧
            (∀ k < u2.toNat, ∃ j < i.toNat + 1, out_d2[k]? = out_s[j]?) ∧
            SortedRange64 out_d2 0 u2.toNat ∧ (array64 out out_d2 ⋆ (FullMemNoWks3 c s ⋆ R)) md2)
          (fun _ ⟨u2, ⟨⟩⟩ md2 ⟨out_d2, hu2_1, hu2_le, hod2_len, ht2, hs2, hso2, hmd2⟩ => by
            fc_steps
            exact ihd (u2, i + 1#64, ()) md2 (by dsimp only; omega)
              ⟨out_d2, hu2_1, by omega, by omega, hod2_len, fun k hk1 hk2 => ht2 k (by omega) hk2,
                fun k hk => by obtain ⟨j, hj, hg⟩ := hs2 k hk; exact ⟨j, by omega, hg⟩,
                hso2, hmd2⟩)
          (fun Jd2 hJd2 => ?_)
        fc_split_fast
        · have hup1_n : (u + 1#64).toNat = u.toNat + 1 := by bv_omega
          fc_steps
          let vi := out_d[i.toNat]'hi_arr
          let out_d2 := out_d.set u.toNat vi
          have hod2_len : out_d2.length = cap.toNat := by simp [out_d2, hod_len]
          have hvi_eq : out_s[i.toNat]? = some vi := by
            rw [← htail_d i.toNat (Nat.le_refl _) hi_lt, List.getElem?_eq_getElem hi_arr]
          have hle_prev : out_d[(u - 1#64).toNat]?.getD 0#64 ≤ vi := by
            obtain ⟨j0, hj0, hget0⟩ := hsub_d (u.toNat - 1) (by omega)
            have hget0' : out_d[(u - 1#64).toNat]? = out_s[j0]? := by rw [hum1_n]; exact hget0
            have hs0 := hos_sort j0 i.toNat (Nat.zero_le _) (by omega) hi_lt
            rw [← hget0', hvi_eq, Option.getD_some] at hs0; exact hs0
          refine hJd2 (u + 1#64, ()) m ⟨out_d2, by omega, by omega, hod2_len, ?_, ?_, ?_, hm⟩
          · intro k hk1 hk2; dsimp [out_d2]
            rw [List.getElem?_set_ne (by omega)]; exact htail_d k (by omega) hk2
          · intro k hk; rw [hup1_n] at hk
            by_cases hku : k = u.toNat
            · subst hku; dsimp [out_d2]; rw [List.getElem?_set_self (by omega)]
              exact ⟨i.toNat, by omega, hvi_eq.symm⟩
            · dsimp [out_d2]; rw [List.getElem?_set_ne (Ne.symm hku)]
              obtain ⟨j, hj, hget⟩ := hsub_d k (by omega); exact ⟨j, by omega, hget⟩
          · intro x y hx hxy hy; rw [hup1_n] at hy
            by_cases hyu : y = u.toNat
            · subst hyu; dsimp [out_d2]; rw [List.getElem?_set_self (by omega), Option.getD_some]
              by_cases hxu : x = u.toNat
              · subst hxu; rw [List.getElem?_set_self (by omega), Option.getD_some]
                exact BitVec.le_refl _
              · rw [List.getElem?_set_ne (Ne.symm hxu)]
                have hsd := hsort_d x (u.toNat - 1) hx (by omega) (by omega)
                rw [← hum1_n] at hsd; exact BitVec.le_trans hsd hle_prev
            · dsimp [out_d2]
              rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (Ne.symm hyu)]
              exact hsort_d x y hx hxy (by omega)
        · fc_steps
          refine hJd2 (u, ()) md ⟨out_d, hu1, by omega, hod_len,
            fun k hk1 hk2 => htail_d k (by omega) hk2,
            fun k hk => by obtain ⟨j, hj, hg⟩ := hsub_d k hk; exact ⟨j, by omega, hg⟩,
            hsort_d, hmd⟩
      · have hi_ge : cnt.toNat ≤ i.toNat := by
          simp only [BitVec.ult, decide_eq_false_iff_not, not_lt] at hc; exact hc
        fc_steps
        refine hQ u out_d md hod_len (by omega) hsort_d (fun k hk => ?_) (sep_ac hmd)
        obtain ⟨j, hj, hget⟩ := hsub_d k hk
        have hok := hos_cb j (by omega); rwa [← hget] at hok
  · -- Watch scan loop
    fc_to_group
    refine wp_loop_inv (ts := [i64, i64])
      (fun (p, cnt, ()) ml => ∃ out1 : List (BitVec 64),
        out1.length = cap.toNat ∧ cnt.toNat ≤ cap.toNat ∧ p.toNat ≤ (off + wsz).toNat ∧
        DenseWatchSliceOk F_cur s.core lit.toNat p.toNat ((off + wsz).toNat - p.toNat) ∧
        (∀ k < cnt.toNat, CondBinElemOk F_cur s.core.cur_vars lit.toNat (out1[k]?.getD 0#64)) ∧
        (FullMemNoWks3 c s ⋆ array64 out out1 ⋆ R) ml)
      (fun (p, _, ()) _ => (off + wsz).toNat - p.toNat)
      (fun J1 hJ1 => by
        fc_steps
        refine hJ1 (off, 0#64, ()) m0 ⟨out0, hout_len, Nat.zero_le _, by bv_omega, ?_,
          fun k hk => by simp at hk, hm0⟩
        simpa [hoff_n, hwsz_n, hend_n, Nat.add_sub_cancel_left] using hslice0)
      (fun J1 ⟨p, cnt, ⟨⟩⟩ ml ⟨out1, hout1_len, hcnt_le, hp_le, hslice, hcb1, hml⟩ ih1 => ?_)
    fc_split_fast
    · have hp_lt : p.toNat < (off + wsz).toNat := by
        simp only [BitVec.ult, decide_eq_true_eq] at hc; exact hc
      have hp_w : p.toNat < s.core.wstk.length := by omega
      obtain ⟨w0, hw0_get, hcase⟩ := dense_slice_pop_step hslice (by omega)
      have hw0_eq : s.core.wstk[p.toNat]'hp_w = w0 := by
        rw [List.getElem?_eq_getElem hp_w] at hw0_get; exact Option.some.inj hw0_get
      have hp1_n : (p + 1#64).toNat = p.toNat + 1 := by bv_omega
      c0_steps; fc_to_group
      refine wp_join_group (ts := [i64, i64])
        (fun (pn, cn, ()) mn => ∃ outn : List (BitVec 64),
          outn.length = cap.toNat ∧ cn.toNat ≤ cap.toNat ∧
          p.toNat < pn.toNat ∧ pn.toNat ≤ (off + wsz).toNat ∧
          DenseWatchSliceOk F_cur s.core lit.toNat pn.toNat ((off + wsz).toNat - pn.toNat) ∧
          (∀ k < cn.toNat, CondBinElemOk F_cur s.core.cur_vars lit.toNat (outn[k]?.getD 0#64)) ∧
          (FullMemNoWks3 c s ⋆ array64 out outn ⋆ R) mn)
        (fun _ ⟨pn, cn, ⟨⟩⟩ mn ⟨outn, hon_len, hcn_le, hinc, hpn_le, hsln, hcbn, hmn⟩ => by
          fc_steps
          exact ih1 (pn, cn, ()) mn (by dsimp only; omega)
            ⟨outn, hon_len, hcn_le, hpn_le, hsln, hcbn, hmn⟩)
        (fun J2 hJ2 => ?_)
      fc_split_fast
      · rcases hcase with ⟨_, hrest⟩ | ⟨hf0, _⟩
        · fc_steps
          exact hJ2 (p + 1#64, cnt, ()) ml ⟨out1, hout1_len, hcnt_le, by omega, by omega,
            by simpa [hp1_n, Nat.sub_sub] using hrest, hcb1, hml⟩
        · exfalso; rw [hw0_eq] at hc; exact absurd hf0 (bne_iff_ne.mp hc)
      · rcases hcase with ⟨hf1, _⟩ | ⟨_, hrem2, cr, hcr_get, hcr_ref, hrest2⟩
        · exfalso; rw [hw0_eq] at hc; exact hf1 (by simpa using hc)
        · fc_split_fast
          · have hge_end : (off + wsz).toNat ≤ (p + 1#64).toNat := by
              simp only [BitVec.ule, decide_eq_true_eq] at hc; exact hc
            omega
          · have hp1_lt : p.toNat + 1 < (off + wsz).toNat := by omega
            have hp1_w : (p + 1#64).toNat < s.core.wstk.length := by omega
            have hp2_n : (p + 2#64).toNat = p.toNat + 2 := by bv_omega
            let crw := s.core.wstk[(p + 1#64).toNat]'hp1_w
            have hp1_bv : (p + 1).toNat = (p + 1#64).toNat := by bv_omega
            have hcr_c0 : ∀ (hwk : (p + 1).toNat < s.core.wstk.length),
                s.core.wstk[(p + 1).toNat]'hwk = crw := fun hwk =>
              list_getElem_congr hp1_bv hwk hp1_w
            have hcr_eq : crw = cr := by
              rw [show crw = s.core.wstk[p.toNat + 1]'(by omega) from
                list_getElem_congr hp1_n hp1_w (by omega)]
              rw [List.getElem?_eq_getElem (by omega)] at hcr_get; exact Option.some.inj hcr_get
            have hcr_ref' : crw.toNat ∈ fullArenaClauseRefsCore s.core := hcr_eq.symm ▸ hcr_ref
            have hslice2 : DenseWatchSliceOk F_cur s.core lit.toNat (p + 2#64).toNat
                ((off + wsz).toNat - (p + 2#64).toNat) := by
              simpa [hp2_n, Nat.sub_sub] using hrest2
            let StepOut (cn : BitVec 64) (mn : Mem 64) : Prop := ∃ outn : List (BitVec 64),
              outn.length = cap.toNat ∧ cn.toNat ≤ cap.toNat ∧
              (∀ k < cn.toNat,
                CondBinElemOk F_cur s.core.cur_vars lit.toNat (outn[k]?.getD 0#64)) ∧
              (FullMemNoWks3 c s ⋆ array64 out outn ⋆ R) mn
            have hskip0 : StepOut cnt ml := ⟨out1, hout1_len, hcnt_le, hcb1, hml⟩
            c0_steps; fc_to_group
            refine wp_join_group (ts := [i64]) (fun (cn, ()) mn => StepOut cn mn)
              (fun _ ⟨cn, ⟨⟩⟩ mn ⟨outn, hon_len, hcn_le, hcbn, hmn⟩ => by
                fc_steps
                exact hJ2 (p + 2#64, cn, ()) mn
                  ⟨outn, hon_len, hcn_le, by omega, by omega, hslice2, hcbn, hmn⟩)
              (fun J3 hJ3 => ?_)
            fc_split_fast
            · have hcr2_lt : crw.toNat + 2 < s.core.arena_len := by
                simp only [BitVec.ult, decide_eq_true_eq] at hc
                have hpk : (p + 1).toNat < s.core.wstk.length := by rw [hp1_bv]; exact hp1_w
                have hc' : (crw.setWidth 64 + 2).toNat < s.core.arena_len := by
                  have hlt := Nat.lt_of_lt_of_le hc
                    (by rw [BitVec.toNat_ofNat]; exact Nat.mod_le _ _)
                  rw [hcr_c0 hpk] at hlt; exact hlt
                rw [BitVec.toNat_add, bv_zext32_toNat] at hc'; bv_omega
              have har_bd0 : (crw.setWidth 64).toNat < s.core.arena.length := by
                rw [bv_zext32_toNat]; omega
              have har_bd2 : (crw.setWidth 64 + 2#64).toNat < s.core.arena.length := by
                rw [BitVec.toNat_add, bv_zext32_toNat]; bv_omega
              have hcr2_c0 :
                  (BitVec.setWidth 64 (s.core.wstk[(p + 1).toNat]'(by rw [hp1_bv]; exact hp1_w)) +
                    (2 : BitVec 64)).toNat = crw.toNat + 2 := by
                rw [BitVec.toNat_add, bv_zext32_toNat,
                  congrArg BitVec.toNat (hcr_c0 (by rw [hp1_bv]; exact hp1_w))]; bv_omega
              have har_bd2_c0 :
                  (BitVec.setWidth 64 (s.core.wstk[(p + 1).toNat]'(by rw [hp1_bv]; exact hp1_w)) +
                    (2 : BitVec 64)).toNat < s.core.arena.length := by rw [hcr2_c0]; omega
              c0_steps; fc_to_group
              refine wp_join_group (ts := [i64]) (fun (cn, ()) mn => StepOut cn mn)
                (fun _ ⟨cn, ⟨⟩⟩ mn hstep => by fc_steps; exact hJ3 (cn, ()) mn hstep)
                (fun J4 hJ4 => ?_)
              fc_split_fast
              · have hhdr_eq : s.core.arena[(crw.setWidth 64).toNat]'har_bd0 =
                    Full.fullArenaHdrCore s.core crw.toNat := by
                  unfold fullArenaHdrCore
                  rw [List.getElem?_eq_getElem (by rw [bv_zext32_toNat] at har_bd0; exact har_bd0),
                    Option.getD_some]
                  exact list_getElem_congr (bv_zext32_toNat crw) har_bd0 (by omega)
                have hng : fullArenaClauseGarbCore s.core crw.toNat = false := by
                  unfold fullArenaClauseGarbCore; rw [← hhdr_eq]
                  have hhdr0 : (s.core.arena[(crw.setWidth 64).toNat]'har_bd0 &&& 0x00480000#32) =
                      0#32 := by
                    have h0 := beq_iff_eq.mp hc
                    have hmask : (524288 ||| 4194304 : BitVec 32) = 0x00480000#32 := by decide
                    rw [hmask] at h0
                    rwa [← list_getElem_congr (by simp only [bv_zext32_toNat]) har_bd0 _]
                  exact garb_false_of_and_480000 hhdr0
                clear hc; fc_split_fast
                · clear hc
                  let sz_bv := s.core.arena[(crw.setWidth 64 + 2#64).toNat]'har_bd2
                  have hsz_eq : fullArenaClauseSizeCore s.core crw.toNat = sz_bv.toNat := by
                    unfold fullArenaClauseSizeCore
                    have hidx2 : (crw.setWidth 64 + 2#64).toNat = crw.toNat + 2 := by
                      rw [BitVec.toNat_add, bv_zext32_toNat]; bv_omega
                    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                    exact congrArg BitVec.toNat (list_getElem_congr hidx2 har_bd2 (by omega)).symm
                  have hsz_c0 :
                      s.core.arena[(BitVec.setWidth 64
                        (s.core.wstk[(p + 1).toNat]'(by rw [hp1_bv]; exact hp1_w)) +
                        (2 : BitVec 64)).toNat]'har_bd2_c0 = sz_bv :=
                    list_getElem_congr
                      (by rw [hcr2_c0, BitVec.toNat_add, bv_zext32_toNat]; bv_omega)
                      har_bd2_c0 har_bd2
                  fc_split_fast
                  · have hbd_ar : crw.toNat + 2 + sz_bv.toNat < s.core.arena_len := by
                      simp only [BitVec.ult, decide_eq_true_eq] at hc
                      have hpk : (p + 1).toNat < s.core.wstk.length := by rw [hp1_bv]; exact hp1_w
                      have hlt := Nat.lt_of_lt_of_le hc
                        (by rw [BitVec.toNat_ofNat]; exact Nat.mod_le _ _)
                      rw [hsz_c0, hcr_c0 hpk, BitVec.toNat_add, BitVec.toNat_add,
                        bv_zext32_toNat, bv_zext32_toNat] at hlt
                      bv_omega
                    clear hc; fc_to_group
                    refine wp_loop_break_group
                      (brkTs := [i32, i32, i32, .bool, .bool, i32])
                      (lpTs := [i32, i32, i32, .bool, i32])
                      (fun (a, b, ocnt, found_lit, ok, _k, ()) mb => mb = ml ∧
                        (ok = true → CopyScanOk s crw lit a b ocnt found_lit sz_bv.toNat))
                      (fun rem (a, b, ocnt, found_lit, k, ()) mk => mk = ml ∧
                        rem = sz_bv.toNat - k.toNat ∧ k.toNat ≤ sz_bv.toNat ∧
                        CopyScanOk s crw lit a b ocnt found_lit k.toNat)
                      ?_ ?_ ?_
                    · -- Post scan-loop break
                      rintro _ ⟨a, b, ocnt, found_lit, ok, _k, ⟨⟩⟩ mb ⟨hmb, hpost⟩
                      subst mb; fc_to_group
                      refine wp_join_group (ts := [i64]) (fun (cn, ()) mn => StepOut cn mn)
                        (fun _ ⟨cn, ⟨⟩⟩ mn hstep => by fc_steps; exact hJ4 (cn, ()) mn hstep)
                        (fun J5 hJ5 => ?_)
                      fc_split_fast
                      · have hok_t : ok = true := by simpa using hc
                        clear hc; fc_split_fast
                        · have hfl_t : found_lit = true := by simpa using hc
                          clear hc; fc_split_fast
                          · have hoc2 : ocnt.toNat = 2 := congrArg BitVec.toNat (beq_iff_eq.mp hc)
                            clear hc
                            obtain ⟨_, ha_lt, hb_lt, hcov_q⟩ := hpost hok_t
                            have ha_lt' : a.toNat < 2 * s.core.cur_vars := ha_lt (by omega)
                            have hb_lt' : b.toNat < 2 * s.core.cur_vars := hb_lt hoc2
                            fc_split_fast
                            · have h1 : a.toNat / 2 ≠ b.toNat / 2 := by
                                rw [← bv32_ushiftRight_imm1_toNat a,
                                  ← bv32_ushiftRight_imm1_toNat b]
                                exact fun heq => bne_iff_ne.mp hc (BitVec.eq_of_toNat_eq heq)
                              clear hc; fc_split_fast
                              · have h2 : a.toNat / 2 ≠ lit.toNat / 2 := by
                                  rw [← bv32_ushiftRight_imm1_toNat a,
                                    ← bv32_ushiftRight_imm1_toNat lit]
                                  exact fun heq => bne_iff_ne.mp hc (BitVec.eq_of_toNat_eq heq)
                                clear hc; fc_split_fast
                                · have h3 : b.toNat / 2 ≠ lit.toNat / 2 := by
                                    rw [← bv32_ushiftRight_imm1_toNat b,
                                      ← bv32_ushiftRight_imm1_toNat lit]
                                    exact fun heq => bne_iff_ne.mp hc (BitVec.eq_of_toNat_eq heq)
                                  clear hc; fc_split_fast
                                  · fc_steps
                                    refine hQ 0#64 out1 ml hout1_len (Nat.zero_le _)
                                      (fun i j hi hij hj => by simp at hj)
                                      (fun k hk => by simp at hk) hml
                                  · have hcnt_lt_cap : cnt.toNat < cap.toNat := by
                                      simp only [BitVec.ule, decide_eq_false_iff_not, not_le] at hc
                                      exact hc
                                    have hcnt_arr : cnt.toNat < out1.length := by omega
                                    have hcp1_n : (cnt + 1#64).toNat = cnt.toNat + 1 := by bv_omega
                                    have hcov : ∀ l ∈ fullArenaClauseLits s crw.toNat,
                                        s.core.vals[l]?.getD 0#8 = 0xFF#8 ∨
                                        l ∈ [lit.toNat, a.toNat, b.toNat] := fun l hl => by
                                      obtain ⟨q, hq, hql⟩ :=
                                        (mem_fullArenaClauseLitsCore_iff (by rw [hsz_eq]; omega)).mp
                                          hl
                                      rw [hsz_eq] at hq
                                      have h := hcov_q q hq; dsimp only at h
                                      rw [List.getElem?_eq_getElem
                                        (by omega : crw.toNat + 3 + q < s.core.arena.length),
                                        Option.getD_some, hql] at h
                                      rcases h with hff | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
                                      · exact Or.inl hff
                                      · exact Or.inr (by simp)
                                      · exact Or.inr (by simp)
                                      · exact Or.inr (by simp)
                                    have hent3 := unassigned_clause_entails hw hcl0 hcr_ref'
                                      hng hcov
                                    fc_to_group
                                    refine wp_join_group (ts := [i32])
                                      (fun (mn, ()) mt => mt = ml ∧
                                        mn = (if b.ult a then b else a))
                                      ?_ (fun Jmn hJmn => ?_)
                                    · rintro _ ⟨mn, ⟨⟩⟩ mt ⟨hmt, hmn⟩; subst mt; fc_to_group
                                      refine wp_join_group (ts := [i32])
                                        (fun (mx, ()) mt2 => mt2 = ml ∧
                                          mx = (if b.ult a then a else b))
                                        ?_ (fun Jmx hJmx => ?_)
                                      · rintro _ ⟨mx, ⟨⟩⟩ mt2 ⟨hmt2, hmx⟩; subst mt2
                                        have hml' :
                                            (array64 out out1 ⋆ (FullMemNoWks3 c s ⋆ R)) ml :=
                                          sep_ac hml
                                        have sep_swap12 : ∀ {P Q S : Mem 64 → Prop} {mx : Mem 64},
                                            (P ⋆ (Q ⋆ S)) mx → (Q ⋆ P ⋆ S) mx := fun h => sep_ac h
                                        fc_steps
                                        let packed :=
                                          ((mn.setWidth 64 <<< (32 : Nat)) ||| mx.setWidth 64)
                                        let out2 := out1.set cnt.toNat packed
                                        have hcb_new :
                                            CondBinElemOk F_cur s.core.cur_vars lit.toNat
                                              packed := by
                                          dsimp [packed]; rw [hmn, hmx]
                                          exact condBin_of_entails3 hent3 ha_lt' hb_lt' h1 h2 h3
                                        refine hJ5 (cnt + 1#64, ()) m
                                          ⟨out2, by simp [out2, hout1_len], by omega,
                                            fun k hk => ?_, sep_swap12 hm⟩
                                        rw [hcp1_n] at hk
                                        by_cases hk_last : k = cnt.toNat
                                        · subst hk_last; dsimp [out2]
                                          rw [List.getElem?_set_self hcnt_arr, Option.getD_some]
                                          exact hcb_new
                                        · dsimp [out2]; rw [List.getElem?_set_ne (Ne.symm hk_last)]
                                          exact hcb1 k (by omega)
                                      · fc_split_fast
                                        · exact hJmx (a, ()) ml ⟨rfl, by simp [hc]⟩
                                        · exact hJmx (b, ()) ml ⟨rfl, by simp [hc]⟩
                                    · fc_split_fast
                                      · exact hJmn (b, ()) ml ⟨rfl, by simp [hc]⟩
                                      · exact hJmn (a, ()) ml ⟨rfl, by simp [hc]⟩
                                · fc_steps; exact hJ5 (cnt, ()) ml hskip0
                              · fc_steps; exact hJ5 (cnt, ()) ml hskip0
                            · fc_steps; exact hJ5 (cnt, ()) ml hskip0
                          · fc_steps; exact hJ5 (cnt, ()) ml hskip0
                        · fc_steps; exact hJ5 (cnt, ()) ml hskip0
                      · fc_steps; exact hJ5 (cnt, ()) ml hskip0
                    · -- Scan loop body (`while (k < sz)`)
                      rintro Bk Lk rem ⟨a, b, ocnt, found_lit, k, ⟨⟩⟩ mk hBk hLk
                        ⟨hmk, rfl, hk_le, hinv⟩
                      subst mk; fc_split_fast
                      · have hk_lt : k.toNat < sz_bv.toNat := by
                          rw [hsz_c0] at hc
                          simp only [BitVec.ult, decide_eq_true_eq] at hc; exact hc
                        clear hc
                        have hkp1_n : (k + 1#32).toNat = k.toNat + 1 := by bv_omega
                        have hcr3k_n :
                            ((s.core.wstk[(p + 1).toNat]'(by rw [hp1_bv]; exact hp1_w)).setWidth 64
                              + 3 + k.setWidth 64).toNat = crw.toNat + 3 + k.toNat := by
                          rw [hcr_c0 (by rw [hp1_bv]; exact hp1_w), BitVec.toNat_add,
                            BitVec.toNat_add, bv_zext32_toNat, bv_zext32_toNat]; bv_omega
                        have hcr3k_arr :
                            ((s.core.wstk[(p + 1).toNat]'(by rw [hp1_bv]; exact hp1_w)).setWidth 64
                              + 3 + k.setWidth 64).toNat < s.core.arena.length := by
                          rw [hcr3k_n]; omega
                        let cl := s.core.arena[crw.toNat + 3 + k.toNat]'(by omega)
                        have hcl_get : (s.core.arena[crw.toNat + 3 + k.toNat]?.getD 0#32).toNat =
                            cl.toNat := by
                          rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                        have hcl_mem : cl.toNat ∈ fullArenaClauseLitsCore s.core crw.toNat := by
                          rw [mem_fullArenaClauseLitsCore_iff (by rw [hsz_eq]; omega)]
                          exact ⟨k.toNat, by rw [hsz_eq]; exact hk_lt, rfl⟩
                        have hcl_lt : cl.toNat < 2 * s.core.cur_vars :=
                          hw.arena.lits_lt crw.toNat hcr_ref' hng cl.toNat hcl_mem
                        have hcl_eq : s.core.arena[((s.core.wstk[(p + 1).toNat]'(by
                            rw [hp1_bv]; exact hp1_w)).setWidth 64 + 3 +
                            k.setWidth 64).toNat]'hcr3k_arr = cl :=
                          list_getElem_congr hcr3k_n hcr3k_arr (by omega)
                        have hcl_v_c0 :
                            ((s.core.arena[((s.core.wstk[(p + 1).toNat]'(by
                              rw [hp1_bv]; exact hp1_w)).setWidth 64 + 3 +
                              k.setWidth 64).toNat]'hcr3k_arr).setWidth 64).toNat <
                              s.core.vals.length := by rw [hcl_eq, bv_zext32_toNat]; omega
                        fc_split_fast
                        · fc_steps
                          exact hBk (a, b, ocnt, found_lit, false, k, ()) ml
                            ⟨rfl, fun h => by cases h⟩
                        · have hne1_cl : s.core.vals[cl.toNat]?.getD 0#8 ≠ 1#8 := by
                            intro h1
                            have hdom : s.core.vals[cl.toNat]'(by omega) = 1#8 := by
                              rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at h1
                              exact h1
                            have hidx : ((s.core.arena[((s.core.wstk[(p + 1).toNat]'(by
                                rw [hp1_bv]; exact hp1_w)).setWidth 64 + 3 +
                                k.setWidth 64).toNat]'hcr3k_arr).setWidth 64).toNat =
                                cl.toNat := by rw [hcl_eq, bv_zext32_toNat]
                            change (0#32).slt
                              (BitVec.signExtend 32 (s.core.vals[_]'_)) = false at hc
                            rw [list_getElem_congr hidx _ (by omega), hdom] at hc; cases hc
                          clear hc; fc_to_group
                          refine wp_join_group (ts := [i32, i32, i32, .bool, .bool])
                            (fun (a', b', ocnt', fl', _ok', ()) mj => mj = ml ∧
                              CopyScanOk s crw lit a' b' ocnt' fl' (k.toNat + 1))
                            ?_ (fun Js hJs => ?_)
                          · rintro _ ⟨a', b', ocnt', fl', _ok', ⟨⟩⟩ mj ⟨hmj, hinv'⟩
                            subst mj; fc_steps
                            exact hLk (sz_bv.toNat - (k + 1#32).toNat)
                              (a', b', ocnt', fl', k + 1#32, ()) ml
                              (by rw [hkp1_n]; omega)
                              ⟨rfl, rfl, by rw [hkp1_n]; omega, hkp1_n ▸ hinv'⟩
                          · fc_split_fast
                            · clear hc; fc_to_group
                              refine wp_join_group (ts := [i32, i32, i32, .bool, .bool])
                                (fun (a', b', ocnt', fl', _ok', ()) mj => mj = ml ∧
                                  CopyScanOk s crw lit a' b' ocnt' fl' (k.toNat + 1))
                                ?_ (fun Js1 hJs1 => ?_)
                              · rintro _ ⟨a', b', ocnt', fl', _ok', ⟨⟩⟩ mj h1
                                fc_steps; exact hJs (a', b', ocnt', fl', _ok', ()) mj h1
                              · fc_split_fast
                                · have hl_eq_lit : cl.toNat = lit.toNat := by
                                    rw [← congrArg BitVec.toNat hcl_eq]
                                    exact congrArg BitVec.toNat (beq_iff_eq.mp hc)
                                  clear hc; fc_steps
                                  exact hJs1 (a, b, ocnt, true, true, ()) ml
                                    ⟨rfl, copyScanOk_step_lit hinv (hcl_get.trans hl_eq_lit)⟩
                                · clear hc; fc_to_group
                                  refine wp_join_group (ts := [i32, i32, i32, .bool])
                                    (fun (a', b', ocnt', _ok', ()) mj => mj = ml ∧
                                      CopyScanOk s crw lit a' b' ocnt' found_lit (k.toNat + 1))
                                    ?_ (fun Js2 hJs2 => ?_)
                                  · rintro _ ⟨a', b', ocnt', _ok', ⟨⟩⟩ mj h2
                                    fc_steps; exact hJs1 (a', b', ocnt', found_lit, _ok', ()) mj h2
                                  · fc_split_fast
                                    · have hoc0 : ocnt.toNat = 0 :=
                                        congrArg BitVec.toNat (beq_iff_eq.mp hc)
                                      clear hc; fc_steps
                                      exact hJs2 (_, b, 1#32, true, ()) ml
                                        ⟨rfl, (by
                                          rw [hcl_eq]
                                          exact copyScanOk_step_a hinv hoc0 hcl_lt hcl_get)⟩
                                    · clear hc; fc_split_fast
                                      · have hoc1 : ocnt.toNat = 1 :=
                                          congrArg BitVec.toNat (beq_iff_eq.mp hc)
                                        clear hc; fc_steps
                                        exact hJs2 (a, _, 2#32, true, ()) ml
                                          ⟨rfl, (by
                                            rw [hcl_eq]
                                            exact copyScanOk_step_b hinv hoc1 hcl_lt hcl_get)⟩
                                      · clear hc; fc_steps
                                        exact hBk (a, b, ocnt, found_lit, false, k, ()) ml
                                          ⟨rfl, fun h => by cases h⟩
                            · have hval_ff : s.core.vals[cl.toNat]?.getD 0#8 = 0xFF#8 := by
                                have hne0 : s.core.vals[cl.toNat]?.getD 0#8 ≠ 0#8 := by
                                  intro h0
                                  have hidx : ((s.core.arena[((s.core.wstk[(p + 1).toNat]'(by
                                      rw [hp1_bv]; exact hp1_w)).setWidth 64 + 3 +
                                      k.setWidth 64).toNat]'hcr3k_arr).setWidth 64).toNat =
                                      cl.toNat := by rw [hcl_eq, bv_zext32_toNat]
                                  change (BitVec.signExtend 32 (s.core.vals[_]'_) == 0#32) =
                                    false at hc
                                  rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at h0
                                  rw [list_getElem_congr hidx _ (by omega), h0] at hc; cases hc
                                rcases hw.vals_domain cl.toNat hcl_lt with h0 | h1 | hff
                                · exact absurd h0 hne0
                                · exact absurd h1 hne1_cl
                                · exact hff
                              clear hc; fc_steps
                              exact hJs (a, b, ocnt, found_lit, true, ()) ml
                                ⟨rfl, copyScanOk_step_ff hinv (by rw [hcl_get]; exact hval_ff)⟩
                      · have hk_eq : k.toNat = sz_bv.toNat := by
                          rw [hsz_c0] at hc
                          simp only [BitVec.ult, decide_eq_false_iff_not, not_lt] at hc; omega
                        clear hc; fc_steps
                        exact hBk (a, b, ocnt, found_lit, true, k, ()) ml
                          ⟨rfl, fun _ => hk_eq ▸ hinv⟩
                    · intro Bk Lk hBk hLk; fc_steps
                      exact hLk sz_bv.toNat (0#32, 0#32, 0#32, false, 0#32, ()) ml
                        ⟨rfl, by simp, Nat.zero_le _, Nat.zero_le _, fun h => by simp at h,
                          fun h => by simp at h, fun _ h => by simp at h⟩
                  · fc_steps; exact hJ4 (cnt, ()) ml hskip0
                · fc_steps; exact hJ4 (cnt, ()) ml hskip0
              · fc_steps; exact hJ4 (cnt, ()) ml hskip0
            · fc_steps; exact hJ3 (cnt, ()) ml hskip0
    · have hp_ge : (off + wsz).toNat ≤ p.toNat := by
        simp only [BitVec.ult, decide_eq_false_iff_not, not_lt] at hc; exact hc
      fc_steps; exact hJ0 (p, cnt, ()) ml ⟨out1, hout1_len, hcnt_le, hcb1, hml⟩

theorem full_cong_merge_condeq_m7_wp (Γ : Env) :
    ∀ args m Q X, fidCongMergeCondeqSpec args m Q X →
      Func.wp Γ full_cong_merge_condeq_m7_body args m Q X := by
  rintro ⟨h, cond, pos_n, neg_n, g_len, g_cap, ⟨⟩⟩ m0 Q X
    ⟨maxA, c, F0, F_cur, s, wk1, wk2, R, hmaxA_lo, _hmaxA_hi, rfl, hsl, hw, hcv3, hcond_lt,
      hcap_le, hpn_le, hnn_le, hwk1_bd, hwk2_bd, hpos_ok, hneg_ok, hseq0, hm0, hQ⟩
  unfold Func.wp full_cong_merge_condeq_m7_body
  have sep_wk1_head : ∀ {s0 : FullState} {mx : Mem 64},
      (FullMemNoWks3 c s0 ⋆ array64 c.pWorkStk1 wk1 ⋆ array64 c.pWorkStk2 wk2 ⋆ R) mx →
      (array64 c.pWorkStk1 wk1 ⋆
        (FullMemNoWks3 c s0 ⋆ array64 c.pWorkStk2 wk2 ⋆ R)) mx := fun mx_h => sep_ac mx_h
  have sep_wk2_head : ∀ {s0 : FullState} {mx : Mem 64},
      (FullMemNoWks3 c s0 ⋆ array64 c.pWorkStk1 wk1 ⋆ array64 c.pWorkStk2 wk2 ⋆ R) mx →
      (array64 c.pWorkStk2 wk2 ⋆
        (FullMemNoWks3 c s0 ⋆ array64 c.pWorkStk1 wk1 ⋆ R)) mx := fun mx_h => sep_ac mx_h
  have hscr_len := hsl.scratch_ok.scratch_buf_len
  fc_split_fast
  · fc_steps
    exact hQ g_len s.scratch.scratch_buf m0 hscr_len (fun hg => ⟨Nat.le_refl _, hg⟩)
      (fun _ _ => rfl) hseq0 hm0
  · fc_split_fast
    · fc_steps
      exact hQ g_len s.scratch.scratch_buf m0 hscr_len (fun hg => ⟨Nat.le_refl _, hg⟩)
        (fun _ _ => rfl) hseq0 hm0
    · fc_split_fast
      · have hgt : g_cap.toNat < g_len.toNat := by
          simp only [BitVec.ult, decide_eq_true_eq] at hc; exact hc
        fc_steps
        exact hQ g_len s.scratch.scratch_buf m0 hscr_len (fun hle => by omega)
          (fun _ _ => rfl) hseq0 hm0
      · have hg_le_cap : g_len.toNat ≤ g_cap.toNat := by
          simp only [BitVec.ult, decide_eq_false_iff_not, not_lt] at hc; exact hc
        clear hc; c0_steps; fc_split_fast
        · have hscr_bd := c.hscr; unfold dimacsBound at hscr_bd
          have hbad : c.scratch_cap < g_cap.toNat := by
            simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat, bv_zext32_toNat] at hc
            rw [Nat.mod_eq_of_lt (by omega)] at hc; exact hc
          omega
        · clear hc; fc_steps
          refine wp_loop_inv (ts := [i32, i64, i64])
            (fun (gl, p, q, ()) ml => ∃ scr : List (BitVec 32),
              scr.length = c.scratch_cap ∧ g_len.toNat ≤ gl.toNat ∧ gl.toNat ≤ g_cap.toNat ∧
              p.toNat ≤ pos_n.toNat ∧ q.toNat ≤ neg_n.toNat ∧
              (∀ idx < g_len.toNat, scr[idx]? = s.scratch.scratch_buf[idx]?) ∧
              FidGateSeqOk maxA F_cur s.core.cur_vars scr gl.toNat 0 ∧
              (FullMemNoWks3 c { s with scratch := { s.scratch with scratch_buf := scr } } ⋆
                array64 c.pWorkStk1 wk1 ⋆ array64 c.pWorkStk2 wk2 ⋆ R) ml)
            (fun (_, p, q, ()) _ => (pos_n.toNat - p.toNat) + (neg_n.toNat - q.toNat))
            (fun J0 hJ0 => by
              fc_steps
              exact hJ0 (g_len, 0#64, 0#64, ()) m0 ⟨s.scratch.scratch_buf, hscr_len, Nat.le_refl _,
                hg_le_cap, Nat.zero_le _, Nat.zero_le _, fun _ _ => rfl, hseq0, hm0⟩)
            (fun J0 ⟨gl, p, q, ⟨⟩⟩ ml ⟨scr, hsl_l, hgl_ge, hgl_le, hp_le, hq_le, hpref,
              hseq, hml⟩ ih0 => ?_)
          fc_split_fast
          · have hp_lt : p.toNat < pos_n.toNat := by
              simp only [BitVec.ult, decide_eq_true_eq] at hc; exact hc
            clear hc; fc_split_fast
            · have hq_lt : q.toNat < neg_n.toNat := by
                simp only [BitVec.ult, decide_eq_true_eq] at hc; exact hc
              clear hc; fc_split_fast
              · have hgl5 : gl.toNat + 5 ≤ g_cap.toNat := by
                  simp only [BitVec.ule, decide_eq_true_eq] at hc; bv_omega
                clear hc
                have hp_arr : p.toNat < wk1.length := by omega
                have hq_arr : q.toNat < wk2.length := by omega
                let sl : FullState := { s with scratch := { s.scratch with scratch_buf := scr } }
                have hml1 : (array64 c.pWorkStk1 wk1 ⋆
                    (FullMemNoWks3 c sl ⋆ array64 c.pWorkStk2 wk2 ⋆ R)) ml := sep_wk1_head hml
                c0_steps
                let pv := wk1[p.toNat]'hp_arr
                let lhs_p := (pv >>> (32 : Nat)).setWidth 32
                have hml2 : (array64 c.pWorkStk2 wk2 ⋆
                    (FullMemNoWks3 c sl ⋆ array64 c.pWorkStk1 wk1 ⋆ R)) ml := sep_wk2_head hml
                c0_steps
                let qv := wk2[q.toNat]'hq_arr
                let lhs_n := (qv >>> (32 : Nat)).setWidth 32
                have hpp1_n : (p + 1#64).toNat = p.toNat + 1 := by bv_omega
                have hqp1_n : (q + 1#64).toNat = q.toNat + 1 := by bv_omega
                fc_split_fast
                · clear hc; fc_steps
                  exact ih0 (gl, p + 1#64, q, ()) ml (by dsimp only; omega)
                    ⟨scr, hsl_l, hgl_ge, hgl_le, by omega, hq_le, hpref, hseq, hml⟩
                · have h1 : lhs_n.toNat ≤ lhs_p.toNat := by
                    simp only [BitVec.ult, decide_eq_false_iff_not, not_lt] at hc; exact hc
                  clear hc; fc_split_fast
                  · clear hc; fc_steps
                    exact ih0 (gl, p, q + 1#64, ()) ml (by dsimp only; omega)
                      ⟨scr, hsl_l, hgl_ge, hgl_le, hp_le, by omega, hpref, hseq, hml⟩
                  · have h2 : lhs_p.toNat ≤ lhs_n.toNat := by
                      simp only [BitVec.ult, decide_eq_false_iff_not, not_lt] at hc; exact hc
                    clear hc
                    have hlhs_eq : lhs_n = lhs_p := BitVec.eq_of_toNat_eq (by omega)
                    fc_to_group
                    refine wp_join_group (ts := [i32, i64])
                      (fun (gl2, _q2, ()) mn => ∃ scr2 : List (BitVec 32),
                        scr2.length = c.scratch_cap ∧ gl.toNat ≤ gl2.toNat ∧
                        gl2.toNat ≤ g_cap.toNat ∧ (∀ idx < gl.toNat, scr2[idx]? = scr[idx]?) ∧
                        FidGateSeqOk maxA F_cur s.core.cur_vars scr2 gl2.toNat 0 ∧
                        (FullMemNoWks3 c
                          { s with scratch := { s.scratch with scratch_buf := scr2 } } ⋆
                          array64 c.pWorkStk1 wk1 ⋆ array64 c.pWorkStk2 wk2 ⋆ R) mn)
                      (fun _ ⟨gl2, _q2, ⟨⟩⟩ mn ⟨scr2, hsl2, hgl2_ge, hgl2_le, hp2, hsq2, hmn⟩ => by
                        fc_steps
                        exact ih0 (gl2, p + 1#64, q, ()) mn (by dsimp only; omega)
                          ⟨scr2, hsl2, by omega, hgl2_le, by omega, hq_le,
                            fun idx hi => (hp2 idx (by omega)).trans (hpref idx hi), hsq2, hmn⟩)
                      (fun Jq hJq => ?_)
                    refine wp_loop_inv (ts := [i32, i64])
                      (fun (gl2, q2, ()) mn => ∃ scr2 : List (BitVec 32),
                        scr2.length = c.scratch_cap ∧ gl.toNat ≤ gl2.toNat ∧
                        gl2.toNat ≤ g_cap.toNat ∧ q.toNat ≤ q2.toNat ∧ q2.toNat ≤ neg_n.toNat ∧
                        (∀ idx < gl.toNat, scr2[idx]? = scr[idx]?) ∧
                        FidGateSeqOk maxA F_cur s.core.cur_vars scr2 gl2.toNat 0 ∧
                        (FullMemNoWks3 c
                          { s with scratch := { s.scratch with scratch_buf := scr2 } } ⋆
                          array64 c.pWorkStk1 wk1 ⋆ array64 c.pWorkStk2 wk2 ⋆ R) mn)
                      (fun (_, q2, ()) _ => neg_n.toNat - q2.toNat)
                      (fun J2 hJ2 => by
                        fc_steps
                        exact hJ2 (gl, q, ()) ml ⟨scr, hsl_l, Nat.le_refl _, hgl_le,
                          Nat.le_refl _, hq_le, fun _ _ => rfl, hseq, hml⟩)
                      (fun J2 ⟨gl2, q2, ⟨⟩⟩ mn
                        ⟨scr2, hsl2, hgl2_ge, hgl2_le, hqq2, hq2_le, hp2, hsq2, hmn⟩ ih2 => ?_)
                    fc_split_fast
                    · have hq2_lt : q2.toNat < neg_n.toNat := by
                        simp only [BitVec.ult, decide_eq_true_eq] at hc; exact hc
                      clear hc; fc_split_fast
                      · have hgl2_5 : gl2.toNat + 5 ≤ g_cap.toNat := by
                          simp only [BitVec.ule, decide_eq_true_eq] at hc; bv_omega
                        clear hc
                        have hq2_arr : q2.toNat < wk2.length := by omega
                        have hq2p1_n : (q2 + 1#64).toNat = q2.toNat + 1 := by bv_omega
                        let sl2 : FullState :=
                          { s with scratch := { s.scratch with scratch_buf := scr2 } }
                        have hmn2 : (array64 c.pWorkStk2 wk2 ⋆
                            (FullMemNoWks3 c sl2 ⋆ array64 c.pWorkStk1 wk1 ⋆ R)) mn :=
                          sep_wk2_head hmn
                        c0_steps
                        let nv := wk2[q2.toNat]'hq2_arr
                        fc_split_fast
                        · clear hc; fc_steps
                          exact hJq (gl2, q2, ()) mn ⟨scr2, hsl2, hgl2_ge, hgl2_le, hp2, hsq2, hmn⟩
                        · have hnv_eq : (nv >>> (32 : Nat)).setWidth 32 = lhs_p := by
                            simpa [nv, lhs_p, pv] using hc
                          clear hc; fc_to_group
                          refine wp_join_group (ts := [i32])
                            (fun (gl3, ()) mp => ∃ scr3 : List (BitVec 32),
                              scr3.length = c.scratch_cap ∧ gl2.toNat ≤ gl3.toNat ∧
                              gl3.toNat ≤ g_cap.toNat ∧
                              (∀ idx < gl2.toNat, scr3[idx]? = scr2[idx]?) ∧
                              FidGateSeqOk maxA F_cur s.core.cur_vars scr3 gl3.toNat 0 ∧
                              (FullMemNoWks3 c
                                { s with scratch := { s.scratch with scratch_buf := scr3 } } ⋆
                                array64 c.pWorkStk1 wk1 ⋆ array64 c.pWorkStk2 wk2 ⋆ R) mp)
                            (fun _ ⟨gl3, ⟨⟩⟩ mp
                              ⟨scr3, hsl3, hgl3_ge, hgl3_le, hp3, hsq3, hmp⟩ => by
                              fc_steps
                              exact ih2 (gl3, q2 + 1#64, ()) mp (by dsimp only; omega)
                                ⟨scr3, hsl3, by omega, hgl3_le, by omega, by omega,
                                  fun idx hi => (hp3 idx (by omega)).trans (hp2 idx hi),
                                  hsq3, hmp⟩)
                            (fun J3 hJ3 => ?_)
                          let t := pv.setWidth 32
                          let e := nv.setWidth 32
                          fc_split_fast
                          · clear hc; fc_to_group
                            refine wp_join_group (ts := [i32, i32, i32])
                              (fun (yy, tt, ee, ()) mr => mr = mn ∧
                                (t &&& 1#32 = 0#32 → yy = lhs_p ∧ tt = t ∧ ee = e) ∧
                                (t &&& 1#32 ≠ 0#32 →
                                  yy = lhs_p ^^^ 1#32 ∧ tt = t ^^^ 1#32 ∧ ee = e ^^^ 1#32))
                              (fun _ ⟨yy, tt, ee, ⟨⟩⟩ mr ⟨hmr, hfl0, hfl1⟩ => ?_)
                              (fun J4 hJ4 => ?_)
                            · subst mr
                              have hgl2_z0 : (gl2.setWidth 64).toNat < scr2.length := by
                                rw [bv_zext32_toNat]; omega
                              have hgl2_n1 : (gl2.setWidth 64 + 1#64).toNat < scr2.length := by
                                rw [BitVec.toNat_add, bv_zext32_toNat]; bv_omega
                              have hgl2_n2 : (gl2.setWidth 64 + 2#64).toNat < scr2.length := by
                                rw [BitVec.toNat_add, bv_zext32_toNat]; bv_omega
                              have hgl2_n3 : (gl2.setWidth 64 + 3#64).toNat < scr2.length := by
                                rw [BitVec.toNat_add, bv_zext32_toNat]; bv_omega
                              have hgl2_n4 : (gl2.setWidth 64 + 4#64).toNat < scr2.length := by
                                rw [BitVec.toNat_add, bv_zext32_toNat]; bv_omega
                              have hgl2_5_n : (gl2 + 5#32).toNat = gl2.toNat + 5 := by bv_omega
                              fc_steps
                              let scr3 := ((((scr2.set gl2.toNat yy).set (gl2.toNat + 1)
                                ((2#32 <<< 28#32) ||| 3#32)).set (gl2.toNat + 2) cond).set
                                (gl2.toNat + 3) tt).set (gl2.toNat + 4) ee
                              have hw1_p := hpos_ok p.toNat hp_lt
                              rw [List.getElem?_eq_getElem hp_arr, Option.getD_some] at hw1_p
                              have hw2_q := hneg_ok q2.toNat hq2_lt
                              rw [List.getElem?_eq_getElem hq2_arr, Option.getD_some] at hw2_q
                              obtain ⟨hs3_l, hs3_p, hs3_ok⟩ := merge_condeq_fidgate_ok
                                hmaxA_lo hcv3 hcond_lt hw1_p hw2_q rfl rfl rfl hnv_eq
                                ⟨hfl0, hfl1⟩ (BitVec.isLt cond) (by omega) rfl hsq2
                              have hcond32 : BitVec.ofNat 32 cond.toNat = cond :=
                                BitVec.eq_of_toNat_eq (by
                                  rw [BitVec.toNat_ofNat]
                                  exact Nat.mod_eq_of_lt (BitVec.isLt cond))
                              rw [hcond32] at hs3_l hs3_p hs3_ok
                              dsimp only [sl2] at hm
                              try rw [show ((2 : BitVec 32) <<< (28 : Nat) ||| 3) =
                                (2#32 <<< 28#32 ||| 3#32) from rfl] at hm
                              try rw [show ((2 : BitVec 32) <<< (28 : BitVec 32) ||| 3) =
                                (2#32 <<< 28#32 ||| 3#32) from rfl] at hm
                              have heq_scr : ((((scr2.set
                                    (gl2.setWidth 64).toNat yy).set
                                    (gl2.setWidth 64 + 1).toNat (2#32 <<< 28#32 ||| 3#32)).set
                                    (gl2.setWidth 64 + 2).toNat cond).set
                                    (gl2.setWidth 64 + 3).toNat tt).set
                                    (gl2.setWidth 64 + 4).toNat ee = scr3 := by
                                dsimp only [scr3]; congr 1; congr 1; congr 1; congr 1
                                all_goals first
                                  | rfl
                                  | rw [bv_zext32_toNat]
                                  | (rw [BitVec.toNat_add, bv_zext32_toNat]; bv_omega)
                              rw [heq_scr] at hm
                              exact hJ3 (gl2 + 5#32, ()) m ⟨scr3, hs3_l.trans hsl2,
                                by rw [hgl2_5_n]; exact Nat.le_add_right _ _,
                                by rw [hgl2_5_n]; exact hgl2_5, hs3_p, by rwa [hgl2_5_n],
                                sep_ac hm⟩
                            · fc_split_fast
                              · have hne : t &&& 1#32 ≠ 0#32 := by simpa [t] using hc
                                clear hc; fc_steps
                                exact hJ4 (lhs_p ^^^ 1#32, t ^^^ 1#32, e ^^^ 1#32, ()) mn
                                  ⟨rfl, fun h => absurd h hne, fun _ => ⟨rfl, rfl, rfl⟩⟩
                              · have h0 : t &&& 1#32 = 0#32 := by simpa [t] using hc
                                clear hc; fc_steps
                                exact hJ4 (lhs_p, t, e, ()) mn
                                  ⟨rfl, fun _ => ⟨rfl, rfl, rfl⟩, fun h => absurd h0 h⟩
                          · clear hc; fc_steps
                            exact hJ3 (gl2, ()) mn ⟨scr2, hsl2, Nat.le_refl _, hgl2_le,
                              fun _ _ => rfl, hsq2, hmn⟩
                      · clear hc; fc_steps
                        exact hJq (gl2, q2, ()) mn ⟨scr2, hsl2, hgl2_ge, hgl2_le, hp2, hsq2, hmn⟩
                    · clear hc; fc_steps
                      exact hJq (gl2, q2, ()) mn ⟨scr2, hsl2, hgl2_ge, hgl2_le, hp2, hsq2, hmn⟩
              · fc_steps; exact hQ gl scr ml hsl_l (fun _ => ⟨hgl_ge, hgl_le⟩) hpref hseq hml
            · fc_steps; exact hQ gl scr ml hsl_l (fun _ => ⟨hgl_ge, hgl_le⟩) hpref hseq hml
          · fc_steps; exact hQ gl scr ml hsl_l (fun _ => ⟨hgl_ge, hgl_le⟩) hpref hseq hml

private def FidIteScrPres (s s' : FullState) : Prop :=
  s'.scratch.tarjan_mark = s.scratch.tarjan_mark ∧
  s'.scratch.tarjan_reach = s.scratch.tarjan_reach ∧
  s'.scratch.extend_stk = s.scratch.extend_stk ∧
  s'.scratch.extend_len = s.scratch.extend_len ∧
  s'.scratch.last_learned = s.scratch.last_learned ∧
  s'.scratch.ant_sz = s.scratch.ant_sz ∧
  s'.scratch.res_sz = s.scratch.res_sz

private def fidAllInv (maxA : Nat) (c : FullCfg) (F_cur : List (List Nat)) (s : FullState)
    (g_len g_cap : BitVec 32) (R : Mem 64 → Prop) (gl : BitVec 32) (m : Mem 64) : Prop :=
  ∃ (s_cur : FullState) (ws wk1 wk2 : List (BitVec 64)),
    s_cur.LengthsOk c ∧ s_cur.core = s.core ∧ FidIteScrPres s s_cur ∧
    ws.length = c.max_vars ∧ wk1.length = c.max_vars ∧ wk2.length = c.max_vars ∧
    g_len.toNat ≤ gl.toNat ∧ gl.toNat ≤ g_cap.toNat ∧
    (∀ idx < g_len.toNat, s_cur.scratch.scratch_buf[idx]? = s.scratch.scratch_buf[idx]?) ∧
    FidGateSeqOk maxA F_cur s.core.cur_vars s_cur.scratch.scratch_buf gl.toNat 0 ∧
    (FullMemNoWks3 c s_cur ⋆
      array64 c.pWsort ws ⋆ array64 c.pWorkStk1 wk1 ⋆ array64 c.pWorkStk2 wk2 ⋆ R) m

private theorem fid_denseInvW_after_ite {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s s' : FullState} (hd : FullDenseInvW c F0 F_cur s)
    (hlen' : s'.LengthsOk c) (hcore : s'.core = s.core)
    (hll : s'.scratch.last_learned = s.scratch.last_learned)
    (hel : s'.scratch.extend_len = s.scratch.extend_len) :
    FullDenseInvW c F0 F_cur s' :=
  ⟨hlen', hcore.symm ▸ hd.2.1,
   fullLitMarksClear_of_eq hd.2.2.1 (congrArg FullCoreState.mrk hcore)
     (congrArg FullCoreState.lit_mark hcore),
   fullArenaVarsNodup_of_eq hd.2.2.2.1 (congrArg FullCoreState.arena hcore)
     (congrArg FullCoreState.arena_len hcore),
   fullExtScratchOk_of_eq hd.2.2.2.2.1 (congrArg FullCoreState.arena hcore)
     (congrArg FullCoreState.arena_len hcore) hll hel,
   by rw [hcore]; exact hd.2.2.2.2.2.1, by rw [hcore]; exact hd.2.2.2.2.2.2⟩

theorem full_cong_extract_ite_all_m7_wp (Γ : Env)
    (hCopy : ∀ a m Q X, fidCongCopyCondbinLv0Spec a m Q X →
      Γ "full_cong_copy_condbin_m7" [i64, i32, i64, i64] [i64] a m Q X)
    (hExt : ∀ a m Q X, m7ExtractCondeqSpec a m Q X →
      Γ "full_cong_extract_condeq_m7" [i64, i64, i64, i64] [i64] a m Q X)
    (hMerge : ∀ a m Q X, fidCongMergeCondeqSpec a m Q X →
      Γ "full_cong_merge_condeq_m7" [i64, i32, i64, i64, i32, i32] [i32] a m Q X) :
    ∀ args m Q X, fidCongExtractIteAllSpec args m Q X →
      Func.wp Γ full_cong_extract_ite_all_m7_body args m Q X := by
  rintro ⟨h, g_len, g_cap, tick_lim, ⟨⟩⟩ m0 Q X
    ⟨maxA, c, F0, F_cur, s, R, hmaxA_lo, hmaxA_hi, rfl, hdw, hgl_le, hcap_sc, hseq0, hm0, hQ⟩
  have hlen := hdw.1; have hw := hdw.2.1
  have hcl0 := hdw.2.2.2.2.2.1; have hdm := hdw.2.2.2.2.2.2
  have hcv_le : s.core.cur_vars ≤ c.max_vars := hlen.core_ok.cur_vars_le
  have hmv_max : c.max_vars < 2 * dimacsBound := c.hmaxv
  have hsc_lt : c.scratch_cap < dimacsBound := c.hscr
  unfold dimacsBound at hmv_max hsc_lt
  have hmv_u64 : (BitVec.ofNat 64 c.max_vars).toNat = c.max_vars := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hmv_lt61 : c.max_vars < 2 ^ 61 := by omega
  have hmv_u64_lt61 : (BitVec.ofNat 64 c.max_vars).toNat < 2 ^ 61 := hmv_u64.symm ▸ hmv_lt61
  have hcv_lt : s.core.cur_vars < 2 ^ 64 := by omega
  unfold Func.wp full_cong_extract_ite_all_m7_body
  fc_split_fast
  · have hgt : g_cap.toNat < g_len.toNat := by
      simp only [BitVec.ult, decide_eq_true_eq] at hc; exact hc
    omega
  · clear hc; fc_split_fast
    · simp only [BitVec.ult, decide_eq_true_eq, bv_zext32_toNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : c.scratch_cap < 2 ^ 64)] at hc; omega
    · clear hc; fc_split_fast
      · fc_steps
        exact hQ g_len s m0 hdw rfl rfl rfl rfl rfl rfl rfl rfl (Nat.le_refl _) hgl_le
          (fun _ _ => rfl) hseq0 hm0
      · have hcv3 : 3 ≤ s.core.cur_vars := by
          have h3n : (3 : BitVec 64).toNat = 3 := rfl
          simp only [BitVec.ult, decide_eq_false_iff_not, not_lt, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt hcv_lt, h3n] at hc; exact hc
        clear hc; fc_split_fast
        · simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (by omega : c.max_vars < 2 ^ 64),
            Nat.mod_eq_of_lt hcv_lt] at hc; omega
        · clear hc; fc_split_fast
          · fc_steps
            exact hQ g_len s m0 hdw rfl rfl rfl rfl rfl rfl rfl rfl (Nat.le_refl _) hgl_le
              (fun _ _ => rfl) hseq0 hm0
          · clear hc
            obtain ⟨ws0, wk1_0, wk2_0, hws0_l, hwk1_0_l, hwk2_0_l, hm_wks⟩ :=
              focus_full_wks3_u64 hlen hm0
            let LoopInv : Tup Val [i64, i64, i32] → Mem 64 → Prop :=
              fun (v, _, gl, ()) ml =>
                v.toNat ≤ s.core.cur_vars ∧ fidAllInv maxA c F_cur s g_len g_cap R gl ml
            fc_steps; fc_to_group
            refine wp_loop_inv (ts := [i64, i64, i32]) LoopInv
              (fun (v, _, _) _ => s.core.cur_vars - v.toNat)
              (fun Jlp hJlp => by
                fc_steps
                exact hJlp (0#64, 0#64, g_len, ()) m0 ⟨Nat.zero_le _,
                  ⟨s, ws0, wk1_0, wk2_0, hlen, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
                    hws0_l, hwk1_0_l, hwk2_0_l, Nat.le_refl _, hgl_le, fun _ _ => rfl, hseq0,
                    hm_wks⟩⟩)
              (fun Jlp ⟨v, ticks, gl, ⟨⟩⟩ ml ⟨hv_le, hm_all⟩ ih => ?_)
            rcases hm_all with
              ⟨s_cur, ws, wk1, wk2, hlen_cur, hsc_core, hsc_pr, hwsl, hwk1l, hwk2l,
                hgl_ge, hgl_le', hpref, hseq, hml⟩
            have hret_exit : wp Γ Q X (.ret (.var gl, ())) ml := by
              obtain ⟨ws32, k1, k2, hws32l, hk1l, hk2l, hm'⟩ :=
                unfocus_full_wks3_u64 hwsl hwk1l hwk2l hml
              let s' : FullState := { s_cur with scratch :=
                { s_cur.scratch with wsort := ws32, work_stk1 := k1, work_stk2 := k2 } }
              have hs'_len : s'.LengthsOk c :=
                ⟨hlen_cur.core_ok, { hlen_cur.scratch_ok with
                  wsort_len := hws32l, work_stk1_len := hk1l, work_stk2_len := hk2l }⟩
              have hdw' := fid_denseInvW_after_ite hdw hs'_len hsc_core hsc_pr.2.2.2.2.1
                hsc_pr.2.2.2.1
              fc_steps
              exact hQ gl s' ml hdw' hsc_core hsc_pr.1 hsc_pr.2.1 hsc_pr.2.2.1 hsc_pr.2.2.2.1
                hsc_pr.2.2.2.2.1 hsc_pr.2.2.2.2.2.1 hsc_pr.2.2.2.2.2.2
                hgl_ge hgl_le' hpref hseq hm'
            fc_split_fast
            · have hv_lt : v.toNat < s.core.cur_vars := by
                simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat,
                  Nat.mod_eq_of_lt hcv_lt] at hc; exact hc
              have hv_bd : v.toNat < 2 ^ 30 := by omega
              clear hc; fc_split_fast
              · clear hc; fc_split_fast
                · clear hc
                  have hv_fl : v.toNat < s_cur.core.flags.length := by
                    have := hlen_cur.core_ok.flags_len; omega
                  have hv2_bd : (v <<< (1 : BitVec 64)).toNat < s_cur.core.vals.length := by
                    have := hlen_cur.core_ok.vals_len; rw [bv64_shl1_bv_toNat]; omega
                  have hvp1_n : (v + 1#64).toNat = v.toNat + 1 := by
                    have h1n : (1#64 : BitVec 64).toNat = 1 := rfl
                    rw [BitVec.toNat_add, h1n, Nat.mod_eq_of_lt (by omega)]
                  let StepInv : Tup Val [i64, i32] → Mem 64 → Prop :=
                    fun (_, gn, ()) mn => fidAllInv maxA c F_cur s g_len g_cap R gn mn
                  fc_to_group
                  refine wp_join_group (ts := [i64, i32]) StepInv
                    (fun _ ⟨tn, gn, ⟨⟩⟩ mn hmn => by
                      fc_steps
                      exact ih (v + 1#64, tn, gn, ()) mn (by dsimp only; omega) ⟨by omega, hmn⟩)
                    (fun Jstep hJstep => ?_)
                  have hStep0 : StepInv (ticks, gl, ()) ml :=
                    ⟨s_cur, ws, wk1, wk2, hlen_cur, hsc_core, hsc_pr, hwsl, hwk1l, hwk2l,
                      hgl_ge, hgl_le', hpref, hseq, hml⟩
                  fc_split_fast
                  · clear hc; fc_split_fast
                    · clear hc
                      let lit0 := (v <<< (1 : BitVec 64)).setWidth 32
                      let lit1 := lit0 ||| 1#32
                      have hlit0_n : lit0.toNat = 2 * v.toNat := bv64_lit0_toNat hv_bd
                      have hlit1_n : lit1.toNat = 2 * v.toNat + 1 := bv64_lit1_toNat hv_bd
                      have hlit0_lt : lit0.toNat < 2 * s.core.cur_vars := by omega
                      have hlit1_lt : lit1.toNat < 2 * s.core.cur_vars := by omega
                      have hlit0_opp : litNeg lit0.toNat = lit1.toNat := by
                        unfold litNeg; change lit0.toNat ^^^ (1#32).toNat = lit1.toNat
                        rw [← BitVec.toNat_xor, bv64_lit0_xor1]
                      have hwv0_bd :
                          ((lit0.setWidth 64 <<< (1 : BitVec 64)) + 1#64).toNat <
                            s_cur.core.wvec.length := by
                        have := hlen_cur.core_ok.wvec_len
                        rw [bv32_zext64_shl1_add1_toNat (by omega)]; omega
                      have hwv1_bd :
                          ((lit1.setWidth 64 <<< (1 : BitVec 64)) + 1#64).toNat <
                            s_cur.core.wvec.length := by
                        have := hlen_cur.core_ok.wvec_len
                        rw [bv32_zext64_shl1_add1_toNat (by omega)]; omega
                      fc_to_group
                      refine wp_join_group (ts := [i64, i32]) StepInv
                        (fun _ ⟨tn, gn, ⟨⟩⟩ mn hst => by
                          fc_steps; exact hJstep (tn, gn, ()) mn hst)
                        (fun Jskip hJskip => ?_)
                      fc_to_group
                      refine wp_join_group (ts := []) (fun _ mn => mn = ml)
                        (fun _ _ mn hmn => by
                          subst mn; fc_steps; exact hJskip (ticks + 1#64, gl, ()) ml hStep0)
                        (fun Jsk hJsk => ?_)
                      fc_split_fast
                      · fc_steps; exact hJsk () ml rfl
                      · clear hc; fc_split_fast
                        · fc_steps; exact hJsk () ml rfl
                        · clear hc
                          let ticks' := ticks + 1#64 +
                            (s_cur.core.wvec[((lit0.setWidth 64 <<< (1 : BitVec 64)) +
                              1#64).toNat]'hwv0_bd).setWidth 64 +
                            (s_cur.core.wvec[((lit1.setWidth 64 <<< (1 : BitVec 64)) +
                              1#64).toNat]'hwv1_bd).setWidth 64
                          let FlipInv (sl ll : BitVec 32) (d0 d1 : BitVec 64)
                              (flp : Bool) : Prop :=
                            sl.toNat < 2 * s.core.cur_vars ∧ ll.toNat < 2 * s.core.cur_vars ∧
                            (flp = true → sl = lit1 ∧ ll = lit0 ∧
                              d0 = c.pWorkStk1 ∧ d1 = c.pWorkStk2) ∧
                            (flp = false → sl = lit0 ∧ ll = lit1 ∧
                              d0 = c.pWorkStk2 ∧ d1 = c.pWorkStk1)
                          fc_to_group
                          refine wp_join_group (ts := [i32, i32, i64, i64, .bool])
                            (fun (sl, ll, d0, d1, flp, ()) mf =>
                              mf = ml ∧ FlipInv sl ll d0 d1 flp)
                            (fun _ ⟨sl, ll, d0, d1, flp, ⟨⟩⟩ mf
                              ⟨hmf, hsl_lt, hll_lt, hft, hff⟩ => ?_)
                            (fun Jfl hJfl => ?_)
                          · subst mf
                            have hw_cur : FullWitnessInv c F0 F_cur s_cur.core := hsc_core.symm ▸ hw
                            have hcl0_cur : s_cur.core.cur_level = 0 := by rw [hsc_core]; exact hcl0
                            have hdm_cur : s_cur.core.dense_mode ≠ 0#64 := by
                              rw [hsc_core]; exact hdm
                            have hsl_lt' : sl.toNat < 2 * s_cur.core.cur_vars := by
                              rw [hsc_core]; exact hsl_lt
                            have hll_lt' : ll.toNat < 2 * s_cur.core.cur_vars := by
                              rw [hsc_core]; exact hll_lt
                            have hcv3' : 3 ≤ s_cur.core.cur_vars := by rw [hsc_core]; exact hcv3
                            have hlit0_lt' : lit0.toNat < 2 * s_cur.core.cur_vars := by
                              rw [hsc_core]; exact hlit0_lt
                            have hm_unswap : ∀ {wsx : List (BitVec 64)} {mx : Mem 64},
                                (FullMemNoWks3 c s_cur ⋆ array64 c.pWsort wsx ⋆
                                  (array64 c.pWorkStk1 wk1 ⋆ array64 c.pWorkStk2 wk2 ⋆ R)) mx →
                                (array64 c.pWsort wsx ⋆ array64 d0 (if flp then wk1 else wk2) ⋆
                                  (FullMemNoWks3 c s_cur ⋆
                                    array64 d1 (if flp then wk2 else wk1) ⋆ R)) mx := by
                              intro wsx mx hmx
                              cases flp
                              · have hq := hff rfl; rw [hq.2.2.1, hq.2.2.2]; exact sep_ac hmx
                              · have hq := hft rfl; rw [hq.2.2.1, hq.2.2.2]; exact sep_ac hmx
                            have hm_swap : ∀ {wsx x y : List (BitVec 64)} {scx : FullState}
                                {mx : Mem 64},
                                (FullMemNoWks3 c scx ⋆ array64 c.pWsort wsx ⋆
                                  array64 d0 x ⋆ array64 d1 y ⋆ R) mx →
                                (FullMemNoWks3 c scx ⋆
                                  array64 c.pWorkStk1 (if flp then x else y) ⋆
                                  array64 c.pWorkStk2 (if flp then y else x) ⋆
                                  (array64 c.pWsort wsx ⋆ R)) mx := by
                              intro wsx x y scx mx hmx
                              cases flp
                              · have hq := hff rfl; rw [hq.2.2.1, hq.2.2.2] at hmx; exact sep_ac hmx
                              · have hq := hft rfl; rw [hq.2.2.1, hq.2.2.2] at hmx; exact sep_ac hmx
                            have mkInv : ∀ {ws' wk1' wk2' : List (BitVec 64)} {mx},
                                ws'.length = c.max_vars → wk1'.length = c.max_vars →
                                wk2'.length = c.max_vars →
                                (FullMemNoWks3 c s_cur ⋆ array64 c.pWsort ws' ⋆
                                  array64 c.pWorkStk1 wk1' ⋆ array64 c.pWorkStk2 wk2' ⋆ R) mx →
                                fidAllInv maxA c F_cur s g_len g_cap R gl mx :=
                              fun hws hk1 hk2 hmx =>
                                ⟨s_cur, _, _, _, hlen_cur, hsc_core, hsc_pr, hws, hk1, hk2,
                                  hgl_ge, hgl_le', hpref, hseq, hmx⟩
                            fc_steps; c0_call hCopy
                            refine fidCongCopyCondbinLv0Spec_mk ws
                              (array64 c.pWorkStk1 wk1 ⋆ array64 c.pWorkStk2 wk2 ⋆ R)
                              hlen_cur hw_cur hcl0_cur hdm_cur hsl_lt' (hwsl.trans hmv_u64.symm)
                              hmv_u64_lt61 (sep_ac hml)
                              fun m0c ws1 m1c hws1_l hm0_le hcb0_sort hcb0_ok hm1c => ?_
                            fc_to_group
                            refine wp_join_group (ts := [i32])
                              (fun (g5, ()) m5 => fidAllInv maxA c F_cur s g_len g_cap R g5 m5)
                              (fun _ ⟨g5, ⟨⟩⟩ m5 h5 => by
                                fc_steps; exact hJskip (ticks', g5, ()) m5 h5)
                              (fun J5 hJ5 => ?_)
                            fc_split_fast
                            · clear hc
                              have hd0_l : (if flp then wk1 else wk2).length = c.max_vars := by
                                cases flp <;> simp [hwk1l, hwk2l]
                              fc_steps; c0_call hExt
                              refine ⟨F_cur, s_cur.core.cur_vars, sl.toNat, ws1,
                                if flp then wk1 else wk2,
                                FullMemNoWks3 c s_cur ⋆
                                  array64 d1 (if flp then wk2 else wk1) ⋆ R,
                                Nat.le_trans hm0_le (Nat.le_of_eq hws1_l.symm),
                                hws1_l ▸ hmv_u64_lt61, hcb0_sort, hcb0_ok,
                                hd0_l.trans hmv_u64.symm, hmv_u64_lt61, hm_unswap (sep_ac hm1c),
                                fun n0 d0_1 m2c hd01_l hn0_le hceq0_ok hm2c => ?_⟩
                              fc_to_group
                              refine wp_join_group (ts := [i32])
                                (fun (g6, ()) m6 => fidAllInv maxA c F_cur s g_len g_cap R g6 m6)
                                (fun _ ⟨g6, ⟨⟩⟩ m6 h6 => by fc_steps; exact hJ5 (g6, ()) m6 h6)
                                (fun J6 hJ6 => ?_)
                              fc_split_fast
                              · clear hc; fc_steps; c0_call hCopy
                                refine fidCongCopyCondbinLv0Spec_mk ws1
                                  (array64 d0 d0_1 ⋆
                                    array64 d1 (if flp then wk2 else wk1) ⋆ R)
                                  hlen_cur hw_cur hcl0_cur hdm_cur hll_lt' hws1_l
                                  (hws1_l ▸ hmv_u64_lt61) (sep_ac hm2c)
                                  fun m1c' ws2 m3c hws2_l hm1_le hcb1_sort hcb1_ok hm3c => ?_
                                fc_to_group
                                refine wp_join_group (ts := [i32])
                                  (fun (g7, ()) m7 => fidAllInv maxA c F_cur s g_len g_cap R g7 m7)
                                  (fun _ ⟨g7, ⟨⟩⟩ m7 h7 => by fc_steps; exact hJ6 (g7, ()) m7 h7)
                                  (fun J7 hJ7 => ?_)
                                fc_split_fast
                                · clear hc
                                  have hd1_l : (if flp then wk2 else wk1).length = c.max_vars := by
                                    cases flp <;> simp [hwk1l, hwk2l]
                                  fc_steps; c0_call hExt
                                  refine ⟨F_cur, s_cur.core.cur_vars, ll.toNat, ws2,
                                    if flp then wk2 else wk1,
                                    FullMemNoWks3 c s_cur ⋆ array64 d0 d0_1 ⋆ R,
                                    Nat.le_trans hm1_le (Nat.le_of_eq hws2_l.symm),
                                    hws2_l ▸ hmv_u64_lt61, hcb1_sort, hcb1_ok,
                                    hd1_l.trans hmv_u64.symm, hmv_u64_lt61, sep_ac hm3c,
                                    fun n1 d1_1 m4c hd11_l hn1_le hceq1_ok hm4c => ?_⟩
                                  fc_to_group
                                  refine wp_join_group (ts := [i32])
                                    (fun (g8, ()) m8 =>
                                      fidAllInv maxA c F_cur s g_len g_cap R g8 m8)
                                    (fun _ ⟨g8, ⟨⟩⟩ m8 h8 => by fc_steps; exact hJ7 (g8, ()) m8 h8)
                                    (fun J8 hJ8 => ?_)
                                  fc_split_fast
                                  · clear hc; fc_to_group
                                    refine wp_join_group (ts := [i32])
                                      (fun (g9, ()) m9 =>
                                        fidAllInv maxA c F_cur s g_len g_cap R g9 m9)
                                      (fun _ ⟨g9, ⟨⟩⟩ m9 h9 => by
                                        fc_steps; exact hJ8 (g9, ()) m9 h9)
                                      (fun J9 hJ9 => ?_)
                                    let w1f := if flp then d0_1 else d1_1
                                    let w2f := if flp then d1_1 else d0_1
                                    have hw1f_l : w1f.length = c.max_vars := by
                                      cases flp <;> simp [w1f, hd01_l, hd11_l, hmv_u64]
                                    have hw2f_l : w2f.length = c.max_vars := by
                                      cases flp <;> simp [w2f, hd01_l, hd11_l, hmv_u64]
                                    have hm4c_w := hm_swap (sep_ac hm4c)
                                    have hMPost : ∀ {gl' scr' m5c},
                                        scr'.length = c.scratch_cap →
                                        g_len.toNat ≤ gl'.toNat → gl'.toNat ≤ g_cap.toNat →
                                        (∀ idx < gl.toNat,
                                          scr'[idx]? = s_cur.scratch.scratch_buf[idx]?) →
                                        FidGateSeqOk maxA F_cur s_cur.core.cur_vars scr'
                                          gl'.toNat 0 →
                                        (FullMemNoWks3 c
                                          { s_cur with scratch :=
                                            { s_cur.scratch with scratch_buf := scr' } } ⋆
                                          array64 c.pWorkStk1 w1f ⋆ array64 c.pWorkStk2 w2f ⋆
                                          (array64 c.pWsort ws2 ⋆ R)) m5c →
                                        wp Γ Q X (.jump J9 (.var gl', ())) m5c := by
                                      intro gl' scr' m5c hs'_l hg1 hg2 hp' hsq' hm5c
                                      let s_nxt : FullState := { s_cur with scratch :=
                                        { s_cur.scratch with scratch_buf := scr' } }
                                      have hn_len : s_nxt.LengthsOk c :=
                                        ⟨hlen_cur.core_ok, { hlen_cur.scratch_ok with
                                          scratch_buf_len := hs'_l }⟩
                                      fc_steps
                                      exact hJ9 (gl', ()) m5c ⟨s_nxt, ws2, w1f, w2f, hn_len,
                                        hsc_core, hsc_pr, hws2_l.trans hmv_u64, hw1f_l, hw2f_l,
                                        hg1, hg2, fun idx hidx =>
                                          (hp' idx (Nat.lt_of_lt_of_le hidx hgl_ge)).trans
                                            (hpref idx hidx),
                                        by rw [← hsc_core]; exact hsq', sep_ac hm5c⟩
                                    have hDoMerge : ∀ {pn nn : BitVec 64},
                                        pn.toNat ≤ w1f.length → nn.toNat ≤ w2f.length →
                                        (∀ idx < pn.toNat, CondEqElemOk F_cur s_cur.core.cur_vars
                                          (litNeg (BitVec.setWidth 32 (v <<< 1)).toNat)
                                          (w1f[idx]?.getD 0#64)) →
                                        (∀ idx < nn.toNat, CondEqElemOk F_cur s_cur.core.cur_vars
                                          (BitVec.setWidth 32 (v <<< 1)).toNat
                                          (w2f[idx]?.getD 0#64)) →
                                        fidCongMergeCondeqSpec
                                          (c.hdr, BitVec.setWidth 32 (v <<< 1), pn, nn, gl, g_cap,
                                            ()) m4c
                                          (fun r m' => wp Γ Q X (.jump J9 (.var r.fst, ())) m')
                                          X := fun hpl hnl hp_ok hn_ok =>
                                      ⟨maxA, c, F0, F_cur, s_cur, w1f, w2f,
                                        array64 c.pWsort ws2 ⋆ R, hmaxA_lo, hmaxA_hi, rfl,
                                        hlen_cur, hw_cur, hcv3', hlit0_lt', hcap_sc,
                                        hpl, hnl, hw1f_l.symm ▸ hmv_lt61, hw2f_l.symm ▸ hmv_lt61,
                                        hp_ok, hn_ok, by rw [hsc_core]; exact hseq, hm4c_w,
                                        fun _ _ _ hs'_l hgl_b =>
                                          hMPost hs'_l (Nat.le_trans hgl_ge (hgl_b hgl_le').1)
                                            (hgl_b hgl_le').2⟩
                                    fc_split_fast
                                    · have hfl_t : flp = true := hc; have hq := hft hfl_t
                                      have hw1_t : w1f = d0_1 := by simp [w1f, hfl_t]
                                      have hw2_t : w2f = d1_1 := by simp [w2f, hfl_t]
                                      fc_steps; c0_call hMerge
                                      refine hDoMerge
                                        (hw1_t ▸ Nat.le_trans hn0_le (Nat.le_of_eq hd01_l.symm))
                                        (hw2_t ▸ Nat.le_trans hn1_le (Nat.le_of_eq hd11_l.symm))
                                        (fun idx hidx => by
                                          have heq : litNeg (BitVec.setWidth 32 (v <<< 1)).toNat =
                                              sl.toNat := by
                                            change litNeg lit0.toNat = sl.toNat
                                            rw [hlit0_opp, hq.1]
                                          rw [hw1_t, heq]; exact hceq0_ok idx hidx)
                                        (fun idx hidx => by
                                          have heq : (BitVec.setWidth 32 (v <<< 1)).toNat =
                                              ll.toNat := congrArg BitVec.toNat hq.2.1.symm
                                          rw [hw2_t, heq]; exact hceq1_ok idx hidx)
                                    · have hfl_f : flp = false := hc; have hq := hff hfl_f
                                      have hw1_f : w1f = d1_1 := by simp [w1f, hfl_f]
                                      have hw2_f : w2f = d0_1 := by simp [w2f, hfl_f]
                                      fc_steps; c0_call hMerge
                                      refine hDoMerge
                                        (hw1_f ▸ Nat.le_trans hn1_le (Nat.le_of_eq hd11_l.symm))
                                        (hw2_f ▸ Nat.le_trans hn0_le (Nat.le_of_eq hd01_l.symm))
                                        (fun idx hidx => by
                                          have heq : litNeg (BitVec.setWidth 32 (v <<< 1)).toNat =
                                              ll.toNat := by
                                            change litNeg lit0.toNat = ll.toNat
                                            rw [hlit0_opp, hq.2.1]
                                          rw [hw1_f, heq]; exact hceq1_ok idx hidx)
                                        (fun idx hidx => by
                                          have heq : (BitVec.setWidth 32 (v <<< 1)).toNat =
                                              sl.toNat := congrArg BitVec.toNat hq.1.symm
                                          rw [hw2_f, heq]; exact hceq0_ok idx hidx)
                                  · fc_steps
                                    have h1l : (if flp then d0_1 else d1_1).length =
                                        c.max_vars := by
                                      cases flp <;> simp [hd01_l, hd11_l, hmv_u64]
                                    have h2l : (if flp then d1_1 else d0_1).length =
                                        c.max_vars := by
                                      cases flp <;> simp [hd01_l, hd11_l, hmv_u64]
                                    exact hJ8 (gl, ()) m4c (mkInv (hws2_l.trans hmv_u64)
                                      h1l h2l (sep_ac (hm_swap (sep_ac hm4c))))
                                · fc_steps
                                  have hxl : (if flp then d0_1 else
                                      if flp then wk2 else wk1).length = c.max_vars := by
                                    cases flp <;> simp [hd01_l, hwk1l, hmv_u64]
                                  have hyl : (if flp then (if flp then wk2 else wk1) else
                                      d0_1).length = c.max_vars := by
                                    cases flp <;> simp [hd01_l, hwk2l, hmv_u64]
                                  exact hJ7 (gl, ()) m3c (mkInv (hws2_l.trans hmv_u64)
                                    hxl hyl (sep_ac (hm_swap (sep_ac hm3c))))
                              · fc_steps
                                have hxl : (if flp then d0_1 else
                                    if flp then wk2 else wk1).length = c.max_vars := by
                                  cases flp <;> simp [hd01_l, hwk1l, hmv_u64]
                                have hyl : (if flp then (if flp then wk2 else wk1) else
                                    d0_1).length = c.max_vars := by
                                  cases flp <;> simp [hd01_l, hwk2l, hmv_u64]
                                exact hJ6 (gl, ()) m2c (mkInv (hws1_l.trans hmv_u64)
                                  hxl hyl (sep_ac (hm_swap (sep_ac hm2c))))
                            · fc_steps
                              exact hJ5 (gl, ()) m1c
                                (mkInv (hws1_l.trans hmv_u64) hwk1l hwk2l (sep_ac hm1c))
                          · fc_split_fast
                            · fc_steps
                              exact hJfl (lit1, lit0, c.pWorkStk1, c.pWorkStk2, true, ()) ml
                                ⟨rfl, hlit1_lt, hlit0_lt, fun _ => ⟨rfl, rfl, rfl, rfl⟩,
                                  fun h => False.elim (Bool.noConfusion h)⟩
                            · fc_steps
                              exact hJfl (lit0, lit1, c.pWorkStk2, c.pWorkStk1, false, ()) ml
                                ⟨rfl, hlit0_lt, hlit1_lt,
                                  fun h => False.elim (Bool.noConfusion h),
                                  fun _ => ⟨rfl, rfl, rfl, rfl⟩⟩
                    · fc_steps; exact hJstep (ticks, gl, ()) ml hStep0
                  · fc_steps; exact hJstep (ticks, gl, ()) ml hStep0
                · exact hret_exit
              · exact hret_exit
            · exact hret_exit

end IteProofs

/-! ## 3. Top-Level Congruence Driver (`full_congruence_dense`) -/

section CongDenseFid

private theorem bv64_ult_lt {a b : BitVec 64} (h : a.ult b = true) : a.toNat < b.toNat := by
  simpa [BitVec.ult] using h

private theorem bv64_ult_not_lt {a b : BitVec 64} (h : a.ult b = false) : ¬ a.toNat < b.toNat := by
  simpa [BitVec.ult] using h

private theorem bv64_ule_true_le {a b : BitVec 64} (h : a.ule b = true) : a.toNat ≤ b.toNat := by
  simpa [BitVec.ule] using h

private theorem bv64_ule_false_lt {a b : BitVec 64} (h : a.ule b = false) : b.toNat < a.toNat := by
  simpa [BitVec.ule] using h

private theorem bv64_ofNat_toNat_lt {n : Nat} (h : n < 2 ^ 64) :
    (BitVec.ofNat 64 n).toNat = n := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

private theorem bv64_setWidth32_eq {x : BitVec 64} {n : Nat} (hx : x.toNat = n) :
    x.setWidth 32 = BitVec.ofNat 32 n := by
  subst hx; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]

private theorem fid_denseInvW_with_antsz_ressz {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hd : FullDenseInvW c F0 F_cur s)
    (ant' res' : BitVec 64) :
    FullDenseInvW c F0 F_cur
      { s with scratch := { s.scratch with ant_sz := ant', res_sz := res' } } :=
  ⟨⟨hd.1.core_ok, { hd.1.scratch_ok with }⟩, hd.2.1, hd.2.2.1, hd.2.2.2.1,
   fullExtScratchOk_of_eq hd.2.2.2.2.1 rfl rfl rfl rfl, hd.2.2.2.2.2.1, hd.2.2.2.2.2.2⟩

private theorem fid_denseInvW_with_tmk_ar {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hd : FullDenseInvW c F0 F_cur s)
    {tmk' : List (BitVec 32)} (ht : tmk'.length = 2 * c.max_vars)
    (ant' res' : BitVec 64) :
    FullDenseInvW c F0 F_cur
      { s with scratch :=
        { s.scratch with tarjan_mark := tmk', ant_sz := ant', res_sz := res' } } :=
  ⟨⟨hd.1.core_ok, { hd.1.scratch_ok with tarjan_mark_len := ht }⟩, hd.2.1, hd.2.2.1,
   hd.2.2.2.1, fullExtScratchOk_of_eq hd.2.2.2.2.1 rfl rfl rfl rfl,
   hd.2.2.2.2.2.1, hd.2.2.2.2.2.2⟩

private theorem fid_denseInvW_with_scr_res0 {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hd : FullDenseInvW c F0 F_cur s)
    {scr' : List (BitVec 32)} (hsl : scr'.length = c.scratch_cap) :
    FullDenseInvW c F0 F_cur
      { s with scratch := { s.scratch with scratch_buf := scr', res_sz := 0#64 } } :=
  ⟨⟨hd.1.core_ok, { hd.1.scratch_ok with scratch_buf_len := hsl }⟩, hd.2.1, hd.2.2.1,
   hd.2.2.2.1, fullExtScratchOk_of_eq hd.2.2.2.2.1 rfl rfl rfl rfl,
   hd.2.2.2.2.2.1, hd.2.2.2.2.2.2⟩

private theorem fid_cd_repr_init_inv {F_cur : List (List Nat)} {repri : List (BitVec 32)}
    {cv0 maxv : Nat} (hrl : repri.length = 2 * maxv) (hcv : cv0 ≤ maxv)
    (hmax : maxv < 2 * 268435456)
    (hinit : ∀ k < 2 * cv0, repri[k]? = some (BitVec.ofNat 32 k)) :
    FullCongReprInv F_cur (2 * cv0) repri := by
  refine ⟨⟨by omega, fun l hl => ?_⟩, fun l hl => ?_⟩
  · rw [hinit l hl, Option.getD_some, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact Nat.le_refl _
  · rw [hinit l hl, Option.getD_some, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact LitEquiv.refl _ _

private theorem fid_cd_ht_max_step {ht_max : BitVec 64} {k free_scr : Nat}
    (hk : k ≤ 14) (heq : ht_max.toNat = 64 * 2 ^ k)
    (hlt : ht_max.toNat < 1048576) (hmul : ht_max.toNat * 4 ≤ free_scr) :
    k + 1 ≤ 14 ∧ (ht_max <<< 1#64).toNat = 64 * 2 ^ (k + 1) ∧
    (ht_max <<< 1#64).toNat ≤ 1048576 ∧ (ht_max <<< 1#64).toNat * 2 ≤ free_scr := by
  have hk_lt : k < 14 :=
    Nat.lt_of_le_of_ne hk fun h => by subst h; rw [heq] at hlt; simp at hlt
  have h2k_le : 2 ^ k ≤ 8192 := Nat.pow_le_pow_right (by decide) (by omega : k ≤ 13)
  have hshl : (ht_max <<< 1#64).toNat = 2 * ht_max.toNat := by
    rw [show (ht_max <<< 1#64 : BitVec 64) = ht_max <<< (1 : Nat) from rfl,
      BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm]
    exact Nat.mod_eq_of_lt (by omega)
  have hpow : 64 * 2 ^ (k + 1) = 2 * (64 * 2 ^ k) := by rw [Nat.pow_succ]; omega
  refine ⟨by omega, by rw [hshl, heq, hpow], by rw [hshl, heq]; omega, by rw [hshl]; omega⟩

private theorem fid_cd_layout_params {g_len ht_max ht_off rem_occ cap : Nat}
    (hht_lo : 64 ≤ ht_max) (hht_hi : ht_max ≤ 1048576)
    (hmul2 : ht_max * 2 ≤ cap - g_len) (hg_le : g_len ≤ cap) (hcap : cap < 2 ^ 28)
    (hho : ht_off = cap - ht_max) (hrem : rem_occ = ht_off - g_len) :
    let occ_bkt :=
      if 262144 ≤ rem_occ then 8192
      else if 65536 ≤ rem_occ then 2048
      else if 16384 ≤ rem_occ then 512
      else if 2048 ≤ rem_occ then 256
      else if 256 ≤ rem_occ then 32 else 16
    let bkt_off := ht_off - occ_bkt
    let inq_off := bkt_off - occ_bkt
    let q_off := inq_off - occ_bkt
    let ctrl_off := q_off - 8
    0 < occ_bkt ∧ occ_bkt ≤ 8192 ∧
    (∃ p : Nat, 1 ≤ p ∧ p ≤ 13 ∧ occ_bkt = 2 ^ p) ∧
    occ_bkt * 3 + 8 ≤ rem_occ ∧ g_len ≤ ctrl_off ∧
    ctrl_off + 8 ≤ q_off ∧ q_off + occ_bkt ≤ inq_off ∧
    inq_off + occ_bkt ≤ bkt_off ∧ bkt_off + occ_bkt ≤ ht_off ∧
    ctrl_off < cap ∧ ctrl_off + 8 ≤ cap ∧ ht_off + ht_max ≤ cap := by
  intro occ_bkt bkt_off inq_off q_off ctrl_off
  have hrem_ge : 64 ≤ rem_occ := by omega
  have hpow : 0 < occ_bkt ∧ occ_bkt ≤ 8192 ∧
      (∃ p : Nat, 1 ≤ p ∧ p ≤ 13 ∧ occ_bkt = 2 ^ p) ∧ occ_bkt * 3 + 8 ≤ rem_occ := by
    dsimp only [occ_bkt]
    split
    · exact ⟨by decide, by decide, ⟨13, by decide, by decide, rfl⟩, by omega⟩
    · split
      · exact ⟨by decide, by decide, ⟨11, by decide, by decide, rfl⟩, by omega⟩
      · split
        · exact ⟨by decide, by decide, ⟨9, by decide, by decide, rfl⟩, by omega⟩
        · split
          · exact ⟨by decide, by decide, ⟨8, by decide, by decide, rfl⟩, by omega⟩
          · split
            · exact ⟨by decide, by decide, ⟨5, by decide, by decide, rfl⟩, by omega⟩
            · exact ⟨by decide, by decide, ⟨4, by decide, by decide, rfl⟩, by omega⟩
  refine ⟨hpow.1, hpow.2.1, hpow.2.2.1, hpow.2.2.2, by omega, by omega, by omega, by omega,
    by omega, by omega, by omega, by omega⟩

private theorem fid_cd_ctrl_off_toNat {cap : Nat} {ht_max occ : BitVec 64}
    (hht : ht_max.toNat ≤ cap) (h38 : occ.toNat * 3 + 8 ≤ cap - ht_max.toNat)
    (hcap : cap < 2 ^ 28) :
    (BitVec.ofNat 64 cap - ht_max - occ - occ - occ - 8#64).toNat =
      cap - ht_max.toNat - occ.toNat - occ.toNat - occ.toNat - 8 := by
  have hsc : (BitVec.ofNat 64 cap).toNat = cap := bv64_ofNat_toNat_lt (by omega)
  have h1 : (BitVec.ofNat 64 cap - ht_max).toNat = cap - ht_max.toNat := by
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by rw [hsc]; exact hht)), hsc]
  have h2 : (BitVec.ofNat 64 cap - ht_max - occ).toNat = cap - ht_max.toNat - occ.toNat := by
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by rw [h1]; omega)), h1]
  have h3 : (BitVec.ofNat 64 cap - ht_max - occ - occ).toNat =
      cap - ht_max.toNat - occ.toNat - occ.toNat := by
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by rw [h2]; omega)), h2]
  have h4 : (BitVec.ofNat 64 cap - ht_max - occ - occ - occ).toNat =
      cap - ht_max.toNat - occ.toNat - occ.toNat - occ.toNat := by
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by rw [h3]; omega)), h3]
  rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by
    rw [h4, show (8#64 : BitVec 64).toNat = 8 from rfl]; omega)), h4]; rfl

private theorem fid_cd_ht_set_step {g_len ht_off i : Nat} {scr0 scri : List (BitVec 32)}
    (hg_le : g_len ≤ ht_off) (hinv1 : ∀ idx < g_len, scri[idx]? = scr0[idx]?)
    (hinv2 : ∀ k < i, scri[ht_off + k]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32)
    (hi_len : ht_off + i < scri.length) :
    (∀ idx < g_len, (scri.set (ht_off + i) 0xFFFFFFFF#32)[idx]? = scr0[idx]?) ∧
    (∀ k < i + 1,
      (scri.set (ht_off + i) 0xFFFFFFFF#32)[ht_off + k]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32) := by
  refine ⟨fun idx hidx => by rw [List.getElem?_set_ne (by omega)]; exact hinv1 idx hidx,
    fun k hk => ?_⟩
  by_cases hki : k = i
  · subst hki; rw [List.getElem?_set_self hi_len, Option.getD_some]
  · rw [List.getElem?_set_ne (by omega)]; exact hinv2 k (by omega)

private theorem fid_cd_ctrl_store_layout {c : FullCfg} {F_cur : List (List Nat)} {cv0 : Nat}
    {scr0 scri : List (BitVec 32)}
    {g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz : Nat}
    (hg_co : g_len ≤ ctrl_off) (hg_24 : g_len ≤ 0x01000000)
    (ho_pos : 0 < occ_bkt) (ho_8192 : occ_bkt ≤ 8192)
    (hopow : ∃ p : Nat, 1 ≤ p ∧ p ≤ 13 ∧ occ_bkt = 2 ^ p) (hht_pos : 0 < ht_sz)
    (hc_cap : ctrl_off < c.scratch_cap) (hc8 : ctrl_off + 8 ≤ c.scratch_cap)
    (hcq : ctrl_off + 8 ≤ q_off) (hqi : q_off + occ_bkt ≤ inq_off)
    (hib : inq_off + occ_bkt ≤ bkt_off) (hbh : bkt_off + occ_bkt ≤ ht_off)
    (hhc : ht_off + ht_sz ≤ c.scratch_cap) (hscrl : scri.length = c.scratch_cap)
    (hpref : ∀ idx < g_len, scri[idx]? = scr0[idx]?)
    (hht : FidCongHtInv 64 F_cur cv0 scr0 scri g_len ht_off ht_sz) :
    let scr' := (((((((scri.set ctrl_off (BitVec.ofNat 32 occ_bkt)).set
      (ctrl_off + 1) (BitVec.ofNat 32 bkt_off)).set
      (ctrl_off + 2) (BitVec.ofNat 32 inq_off)).set
      (ctrl_off + 3) (BitVec.ofNat 32 q_off)).set
      (ctrl_off + 4) 0#32).set (ctrl_off + 5) 0#32).set
      (ctrl_off + 6) (BitVec.ofNat 32 ht_off)).set (ctrl_off + 7) (BitVec.ofNat 32 ht_sz)
    scr'.length = c.scratch_cap ∧
    M8CtrlLayout c scr' g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz ∧
    (∀ idx < g_len, scr'[idx]? = scr0[idx]?) ∧
    FidCongHtInv 64 F_cur cv0 scr0 scr' g_len ht_off ht_sz := by
  intro scr'
  have hsl : scr'.length = c.scratch_cap := by dsimp only [scr']; simp [hscrl]
  have hhold_out : ∀ idx, idx < ctrl_off ∨ ctrl_off + 8 ≤ idx → scr'[idx]? = scri[idx]? := by
    intro idx hidx; dsimp only [scr']; repeat rw [List.getElem?_set_ne (by omega)]
  have hpref' : ∀ idx < g_len, scr'[idx]? = scr0[idx]? := fun idx hidx =>
    (hhold_out idx (Or.inl (by omega))).trans (hpref idx hidx)
  have hht' : FidCongHtInv 64 F_cur cv0 scr0 scr' g_len ht_off ht_sz := fun k hk => by
    dsimp only; rw [hhold_out (ht_off + k) (Or.inr (by omega))]; exact hht k hk
  have hg : ∀ j, j < 8 → scr'[ctrl_off + j]? =
      ([BitVec.ofNat 32 occ_bkt, BitVec.ofNat 32 bkt_off, BitVec.ofNat 32 inq_off,
        BitVec.ofNat 32 q_off, 0#32, 0#32, BitVec.ofNat 32 ht_off,
        BitVec.ofNat 32 ht_sz])[j]? := by
    intro j _; dsimp only [scr']
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      (repeat rw [List.getElem?_set_ne (by omega)]) <;>
      (try rw [Nat.add_zero]) <;>
      rw [List.getElem?_set_self (by simp [hscrl]; omega)] <;> rfl
  have hs0 : scr'[ctrl_off]?.getD 0#32 = BitVec.ofNat 32 occ_bkt := by
    have h0 := hg 0 (by decide); rw [Nat.add_zero] at h0; exact congrArg (Option.getD · 0#32) h0
  have h5 := hg 5 (by decide)
  have h5' : scr'[ctrl_off + 5]?.getD 0#32 = 0#32 := congrArg (Option.getD · 0#32) h5
  exact ⟨hsl,
    ⟨hc_cap, hc8, hg_co, hg_24, hs0,
     congrArg (Option.getD · 0#32) (hg 1 (by decide)),
     congrArg (Option.getD · 0#32) (hg 2 (by decide)),
     congrArg (Option.getD · 0#32) (hg 3 (by decide)),
     congrArg (Option.getD · 0#32) (hg 6 (by decide)),
     congrArg (Option.getD · 0#32) (hg 7 (by decide)),
     ho_pos, ho_8192, hopow, hht_pos, hcq, hqi, hib, hbh, hhc,
     by have := hg 4 (by decide); rw [this]; simpa using ho_pos,
     by rw [h5]; exact Nat.zero_le _,
     fun k hk => by rw [h5', show (0#32 : BitVec 32).toNat = 0 from rfl] at hk; omega⟩,
    hpref', hht'⟩

theorem full_congruence_dense_wp (Γ : Env)
    (hExtBins : ∀ a m Q X, m6CongExtractBinariesSpec a m Q X →
      Γ "full_cong_extract_binaries" [i64, i64] [i64] a m Q X)
    (hFindUE : ∀ a m Q X, m6CongFindUnitsEquivsSpec a m Q X →
      Γ "full_cong_find_units_equivs" [i64] [i64] a m Q X)
    (hExtract : ∀ a m Q X, fidCongExtractSpec a m Q X →
      Γ "full_cong_extract" [i64, i64, i64] [i64] a m Q X)
    (hExtIteAll : ∀ a m Q X, fidCongExtractIteAllSpec a m Q X →
      Γ "full_cong_extract_ite_all_m7" [i64, i32, i32, i64] [i32] a m Q X)
    (hWorklist : ∀ a m Q X, fidCongWorklistSpec a m Q X →
      Γ "full_cong_worklist" [i64, i64, i64, i64] [i64] a m Q X)
    (hFwdSub : ∀ a m Q X, m6CongFwdSubsumeSpec a m Q X →
      Γ "full_cong_fwd_subsume" [i64, i64] [i64] a m Q X) :
    ∀ a m Q X, m3CongruenceDenseSpec a m Q X →
      Func.wp Γ full_congruence_dense_body a m Q X := by
  rintro ⟨h, tick_lim, ⟨⟩⟩ m0 Q X ⟨c, F0, s0, R, rfl, hden0, hm0, hQ⟩
  have hsc : c.scratch_cap < 2 ^ 28 := Nat.lt_of_lt_of_le c.hscr (by decide)
  have hmx : c.max_vars < 2 * 268435456 := Nat.lt_of_lt_of_le c.hmaxv (by decide)
  obtain ⟨hlen0, ⟨F_cur, hw0⟩⟩ := hden0.1
  have hdw0 : FullDenseInvW c F0 F_cur s0 :=
    ⟨hlen0, hw0, hden0.2.1, hden0.2.2.1, hden0.2.2.2.1, hden0.2.2.2.2.1, hden0.2.2.2.2.2⟩
  let cv0 := s0.core.cur_vars; let fuel0 := s0.core.fuel
  have hcv_le : cv0 ≤ c.max_vars := hlen0.core_ok.cur_vars_le
  unfold Func.wp full_congruence_dense_body
  m6b_split
  · m6b_steps; exact hQ 1#64 s0 m0 hden0 rfl rfl (Or.inl rfl) (fun h => by cases h) hm0
  · have h256 : 256 ≤ c.scratch_cap := by
      have := bv64_ult_not_lt hc
      rw [show (256 : BitVec 64).toNat = 256 from rfl, bv64_ofNat_toNat_lt (by omega)] at this
      omega
    clear hc; m6b_split
    · m6b_steps; exact hQ 1#64 s0 m0 hden0 rfl rfl (Or.inl rfl) (fun h => by cases h) hm0
    · clear hc; m6b_steps
      let s0a : FullState := { s0 with scratch := { s0.scratch with ant_sz := 0#64 } }
      have hdw0a : FullDenseInvW c F0 F_cur s0a :=
        fid_denseInvW_with_antsz_ressz hdw0 0#64 s0.scratch.res_sz
      m6b_call hExtBins
      refine ⟨c, F0, F_cur, s0a, R, rfl, hdw0a, hm,
        fun r1 s1 m1 hdw1 hcv1 hfl1 _hr1_dom hr1_uns hm1 => ?_⟩
      have hcv10 : s1.core.cur_vars = cv0 := hcv1
      m6b_split
      · m6b_steps
        exact hQ 20#64 _ m (fid_denseInvW_with_antsz_ressz hdw1 0#64 s1.scratch.res_sz).toDense
          hcv1 hfl1 (Or.inr rfl) (fun _ => hr1_uns (beq_iff_eq.mp hc)) hm
      · clear hc
        have hcv1_lt : cv0 < 2 ^ 32 := by omega
        have h2cv1_64 : 2 * cv0 < 2 ^ 64 := by omega
        m6b_to_group
        refine wp_loop_inv (ts := [i64])
          (fun (i, ()) mi => ∃ repri : List (BitVec 32),
            repri.length = 2 * c.max_vars ∧ i.toNat ≤ 2 * cv0 ∧
            (∀ k < i.toNat, repri[k]? = some (BitVec.ofNat 32 k)) ∧
            (FullMem c { s1 with core := { s1.core with repr := repri } } ⋆ R) mi)
          (fun (i, ()) _ => 2 * cv0 - i.toNat)
          (fun Ji hJi => by
            m6b_let
            exact hJi (0#64, ()) m1
              ⟨s1.core.repr, hdw1.1.core_ok.repr_len, Nat.zero_le _,
               fun _ h => by simp at h, hm1⟩)
          (fun Ji (i, ()) mi ⟨repri, hrl, hi_le, hinit, hmi⟩ ihi => ?_)
        m6b_split
        · have hi_lt : i.toNat < 2 * cv0 := by
            have h := bv64_ult_lt hc; rw [hcv10] at h
            change i.toNat < (BitVec.ofNat 64 cv0 <<< (1 : Nat)).toNat at h
            rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm,
              bv64_ofNat_toNat_lt (by omega), Nat.mod_eq_of_lt h2cv1_64] at h; exact h
          have hi1_n : (i + 1#64).toNat = i.toNat + 1 := bv64_add1_lt (by omega)
          have hi_arr : i.toNat < repri.length := by omega
          have hi_tr : i.setWidth 32 = BitVec.ofNat 32 i.toNat := by
            apply BitVec.eq_of_toNat_eq
            rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          clear hc; m6b_steps
          exact ihi (i + 1#64, ()) m (by dsimp only; omega)
            ⟨repri.set i.toNat (i.setWidth 32), by simp [hrl], by rw [hi1_n]; omega,
             fun k hk => by
               rw [hi1_n] at hk
               by_cases hki : k = i.toNat
               · subst hki; rw [List.getElem?_set_self hi_arr, hi_tr]
               · rw [List.getElem?_set_ne (Ne.symm hki)]; exact hinit k (by omega),
             hm⟩
        · have hi_eq : i.toNat = 2 * cv0 := by
            have h := bv64_ult_not_lt hc; rw [hcv10] at h
            change ¬ i.toNat < (BitVec.ofNat 64 cv0 <<< (1 : Nat)).toNat at h
            rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm,
              bv64_ofNat_toNat_lt (by omega), Nat.mod_eq_of_lt h2cv1_64] at h; omega
          rw [hi_eq] at hinit
          let s2 : FullState := { s1 with core := { s1.core with repr := repri } }
          have hdw2 := m6_fullDenseInvW_with_repr hdw1 hrl
          have hrepr2 : FullCongReprInv F_cur (2 * s2.core.cur_vars) s2.core.repr := by
            rw [show s2.core.cur_vars = cv0 from hcv1]
            exact fid_cd_repr_init_inv hrl hcv_le hmx hinit
          clear hc; m6b_steps; m6b_call hFindUE
          refine ⟨c, F0, F_cur, s2, R, rfl, hdw2, hrepr2, hmi,
            fun r2 s3 m3 hdw3 hcv3 hfl3 hrepr3 _hr2_dom hr2_uns hm3 => ?_⟩
          have hcv30 : s3.core.cur_vars = cv0 := hcv3.trans hcv1
          have hfl30 : s3.core.fuel = fuel0 := hfl3.trans hfl1
          m6b_split
          · m6b_to_group
            refine wp_loop_inv (ts := [i64])
              (fun (it, ()) mt => ∃ tmkt : List (BitVec 32),
                tmkt.length = 2 * c.max_vars ∧ it.toNat ≤ cv0 ∧
                (FullMem c { s3 with scratch := { s3.scratch with tarjan_mark := tmkt } } ⋆ R) mt)
              (fun (it, ()) _ => cv0 - it.toNat)
              (fun Jt hJt => by
                m6b_let; exact hJt (0#64, ()) m3
                  ⟨s3.scratch.tarjan_mark, hdw3.1.scratch_ok.tarjan_mark_len, Nat.zero_le _, hm3⟩)
              (fun Jt (it, ()) mt ⟨tmkt, htlt, hit_le, hmt⟩ iht => ?_)
            m6b_split
            · have hit_lt : it.toNat < cv0 := by
                have h := bv64_ult_lt hc; rwa [hcv10, bv64_ofNat_toNat_lt (by omega)] at h
              have hit1 : (it + 1#64).toNat = it.toNat + 1 := bv64_add1_lt (by omega)
              have hit_arr : it.toNat < tmkt.length := by omega
              clear hc; m6b_steps
              exact iht (it + 1#64, ()) m (by dsimp only; omega)
                ⟨tmkt.set it.toNat 0#32, by simp [htlt], by rw [hit1]; omega, hm⟩
            · clear hc; m6b_steps
              exact hQ 20#64 _ m (fid_denseInvW_with_tmk_ar hdw3 htlt 0#64 0#64).toDense
                hcv30 hfl30 (Or.inr rfl) (fun _ => hr2_uns (beq_iff_eq.mp hc)) hm
          · clear hc
            have hhalf : (BitVec.ofNat 64 c.scratch_cap >>> (1 : Nat)).toNat =
                c.scratch_cap / 2 := by
              rw [BitVec.toNat_ushiftRight, bv64_ofNat_toNat_lt (by omega),
                Nat.shiftRight_eq_div_pow]
            m6b_to_group
            refine wp_join_group (ts := [i64])
              (fun (g_cap, ()) mg => mg = m3 ∧
                g_cap.toNat ≤ c.scratch_cap / 2 ∧ g_cap.toNat ≤ 0x00FFFFFF)
              ?_
              (fun Jgc hJgc => by
                m6b_split
                · have hlt := bv64_ult_lt hc
                  rw [show (0x00FFFFFF : BitVec 64).toNat = 0x00FFFFFF from rfl] at hlt
                  change 0x00FFFFFF < (BitVec.ofNat 64 c.scratch_cap >>> (1 : Nat)).toNat at hlt
                  rw [hhalf] at hlt; m6b_steps
                  exact hJgc (0x00FFFFFF#64, ()) m3 ⟨rfl, by
                    rw [show (0x00FFFFFF#64 : BitVec 64).toNat = 0x00FFFFFF from rfl]; omega,
                    by decide⟩
                · have hnot := bv64_ult_not_lt hc
                  rw [show (0x00FFFFFF : BitVec 64).toNat = 0x00FFFFFF from rfl] at hnot
                  change ¬ 0x00FFFFFF < (BitVec.ofNat 64 c.scratch_cap >>> (1 : Nat)).toNat at hnot
                  m6b_let
                  exact hJgc (_, ()) m3 ⟨rfl, by rw [hhalf]; exact Nat.le_refl _,
                    by rw [hhalf] at hnot ⊢; omega⟩)
            rintro _ ⟨g_cap, ⟨⟩⟩ mg ⟨hmg, hgc_half, hgc_24⟩
            m6b_steps; m6b_call hExtract
            refine ⟨c, F0, F_cur, s3, R, rfl, hdw3, by omega, hmg ▸ hm3,
              fun g_len0 s4a m4a hdw4a hcv4a hfl4a hrepr4a _hinc4a hgl0_le hseq4a hm4a => ?_⟩
            have hcv4a0 : s4a.core.cur_vars = cv0 := hcv4a.trans hcv30
            have hfl4a0 : s4a.core.fuel = fuel0 := hfl4a.trans hfl30
            have hrepr4a_inv : FullCongReprInv F_cur (2 * cv0) s4a.core.repr := by
              rw [hrepr4a, ← hcv30]; exact hrepr3
            m6b_to_group
            refine wp_join_group (ts := [i64])
              (fun (g_len, ()) m4 => ∃ s4 : FullState,
                FullDenseInvW c F0 F_cur s4 ∧ s4.core.cur_vars = cv0 ∧ s4.core.fuel = fuel0 ∧
                FullCongReprInv F_cur (2 * cv0) s4.core.repr ∧ g_len.toNat ≤ g_cap.toNat ∧
                FidGateSeqOk 64 F_cur s4.core.cur_vars s4.scratch.scratch_buf g_len.toNat 0 ∧
                (FullMem c s4 ⋆ R) m4)
              (fun _ ⟨g_len, ⟨⟩⟩ m4
                  ⟨s4, hdw4, hcv40, hfl40, hrepr4_inv, hgl_le, hseq4, hm4⟩ => by
                clear hExtBins hFindUE hExtract hExtIteAll
                  hdw0 hdw0a hdw1 hdw2 hdw3 hdw4a hden0 hw0 hlen0 hrepr2 hrepr3 hrepr4a hrepr4a_inv
                  hm1 hm3 hm4a hmg hcv1 hfl1 hcv3 hfl3 hcv30 hfl30 hcv4a hfl4a hcv4a0 hfl4a0
                  hcv1_lt h2cv1_64 hgl0_le hseq4a _hinc4a hhalf
                m6b_to_group
                refine wp_join_group (ts := [i64])
                  (fun (_i', ()) mj => ∃ sj : FullState,
                    FullDenseInvW c F0 F_cur sj ∧ sj.core.cur_vars = cv0 ∧ sj.core.fuel = fuel0 ∧
                    FullCongReprInv F_cur (2 * cv0) sj.core.repr ∧ (FullMem c sj ⋆ R) mj)
                  (fun _ ⟨_i', ⟨⟩⟩ mj ⟨sj, hdj, hcvj, hflj, hreprj, hmj⟩ => by
                    m6b_steps; m6b_call hFwdSub
                    refine ⟨c, F0, F_cur, sj, R, rfl, hdj, hcvj ▸ hreprj, hmj,
                      fun r5 s5 m5 hdw5 hcv5 hfl5 hrepr5 _hr5_dom hr5_uns hm5 => ?_⟩
                    have hcv50 : s5.core.cur_vars = cv0 := hcv5.trans hcvj
                    have hfl50 : s5.core.fuel = fuel0 := hfl5.trans hflj
                    m6b_split
                    · m6b_to_group
                      refine wp_loop_inv (ts := [i64])
                        (fun (it, ()) mt => ∃ tmkt : List (BitVec 32),
                          tmkt.length = 2 * c.max_vars ∧ it.toNat ≤ cv0 ∧
                          (FullMem c { s5 with scratch :=
                            { s5.scratch with tarjan_mark := tmkt } } ⋆ R) mt)
                        (fun (it, ()) _ => cv0 - it.toNat)
                        (fun Jt hJt => by
                          m6b_let; exact hJt (0#64, ()) m5
                            ⟨s5.scratch.tarjan_mark, hdw5.1.scratch_ok.tarjan_mark_len,
                             Nat.zero_le _, hm5⟩)
                        (fun Jt (it, ()) mt ⟨tmkt, htlt, hit_le, hmt⟩ iht => ?_)
                      m6b_split
                      · have hit_lt : it.toNat < cv0 := by
                          have h := bv64_ult_lt hc; rwa [hcv10, bv64_ofNat_toNat_lt (by omega)] at h
                        have hit1 : (it + 1#64).toNat = it.toNat + 1 := bv64_add1_lt (by omega)
                        have hit_arr : it.toNat < tmkt.length := by omega
                        clear hc; m6b_steps
                        exact iht (it + 1#64, ()) m (by dsimp only; omega)
                          ⟨tmkt.set it.toNat 0#32, by simp [htlt], by rw [hit1]; omega, hm⟩
                      · clear hc; m6b_steps
                        exact hQ 20#64 _ m (fid_denseInvW_with_tmk_ar hdw5 htlt 0#64 0#64).toDense
                          hcv50 hfl50 (Or.inr rfl) (fun _ => hr5_uns (beq_iff_eq.mp hc)) hm
                    · clear hc; m6b_to_group
                      refine wp_loop_inv (ts := [i64])
                        (fun (it, ()) mt => ∃ tmkt : List (BitVec 32),
                          tmkt.length = 2 * c.max_vars ∧ it.toNat ≤ cv0 ∧
                          (FullMem c { s5 with scratch :=
                            { s5.scratch with tarjan_mark := tmkt } } ⋆ R) mt)
                        (fun (it, ()) _ => cv0 - it.toNat)
                        (fun Jt hJt => by
                          m6b_let; exact hJt (0#64, ()) m5
                            ⟨s5.scratch.tarjan_mark, hdw5.1.scratch_ok.tarjan_mark_len,
                             Nat.zero_le _, hm5⟩)
                        (fun Jt (it, ()) mt ⟨tmkt, htlt, hit_le, hmt⟩ iht => ?_)
                      m6b_split
                      · have hit_lt : it.toNat < cv0 := by
                          have h := bv64_ult_lt hc; rwa [hcv10, bv64_ofNat_toNat_lt (by omega)] at h
                        have hit1 : (it + 1#64).toNat = it.toNat + 1 := bv64_add1_lt (by omega)
                        have hit_arr : it.toNat < tmkt.length := by omega
                        clear hc; m6b_steps
                        exact iht (it + 1#64, ()) m (by dsimp only; omega)
                          ⟨tmkt.set it.toNat 0#32, by simp [htlt], by rw [hit1]; omega, hm⟩
                      · clear hc; m6b_steps
                        let sf := { s5 with scratch :=
                          { s5.scratch with tarjan_mark := tmkt, res_sz := 0#64, ant_sz := 0#64 } }
                        have hdwf := fid_denseInvW_with_tmk_ar hdw5 htlt 0#64 0#64
                        m6b_split
                        · m6b_steps; apply_assumption; m6b_steps
                          exact hQ 20#64 sf m hdwf.toDense hcv50 hfl50 (Or.inr rfl)
                            (fun _ => FullM3CongBva.unsat_of_inconsistent_w hdwf.2.1
                              (bne_iff_ne.mp hc)) hm
                        · m6b_steps; apply_assumption; m6b_steps
                          exact hQ 1#64 sf m hdwf.toDense hcv50 hfl50 (Or.inl rfl)
                            (fun h => by cases h) hm)
                  ?_
                intro Jwl_if hJwl_if
                m6b_split
                · have hg_pos : 0 < g_len.toNat := by
                    have h := bv64_ult_lt hc; rwa [show (0 : BitVec 64).toNat = 0 from rfl] at h
                  clear hc; m6b_split
                  · clear hc; m6b_to_group
                    let free_scr := BitVec.ofNat 64 c.scratch_cap - g_len
                    have hfree_n : free_scr.toNat = c.scratch_cap - g_len.toNat := by
                      dsimp only [free_scr]
                      rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by
                        rw [bv64_ofNat_toNat_lt (by omega)]; omega)),
                        bv64_ofNat_toNat_lt (by omega)]
                    have hfree_ge : 128 ≤ free_scr.toNat := by rw [hfree_n]; omega
                    refine wp_loop_inv (ts := [i64])
                      (fun (ht_max, ()) mhm => mhm = m4 ∧ ∃ k : Nat,
                        k ≤ 14 ∧ ht_max.toNat = 64 * 2 ^ k ∧ ht_max.toNat ≤ 1048576 ∧
                        ht_max.toNat * 2 ≤ free_scr.toNat)
                      (fun (ht_max, ()) _ => 1048576 - ht_max.toNat)
                      (fun Jhm hJhm => by
                        m6b_let
                        exact hJhm (64#64, ()) m4
                          ⟨rfl, 0, Nat.zero_le _, rfl, by decide,
                           by rw [show (64#64 : BitVec 64).toNat = 64 from rfl]; omega⟩)
                      (fun Jhm (ht_max, ()) mhm ⟨hmhm, k, hk_le, hpow, h1m, hmul2⟩ ih_hm => ?_)
                    have hhm_ge : 64 ≤ ht_max.toNat := by
                      rw [hpow]; have := Nat.one_le_two_pow (n := k); omega
                    m6b_to_group
                    refine wp_join_group (ts := []) (fun () me => me = m4) ?_
                      (fun Jhm_exit hJhm_exit => by
                        m6b_steps; m6b_split
                        · have hmul4 : ht_max.toNat * 4 ≤ free_scr.toNat := by
                            have h := bv64_ule_true_le hc
                            rw [show (4 : BitVec 64) = 4#64 from rfl, BitVec.toNat_mul,
                              show (4#64 : BitVec 64).toNat = 4 from rfl,
                              Nat.mod_eq_of_lt (by omega)] at h; exact h
                          clear hc; m6b_split
                          · have hlt : ht_max.toNat < 1048576 := bv64_ult_lt hc
                            obtain ⟨hk1, hpow1, h1m1, hmul2_1⟩ :=
                              fid_cd_ht_max_step hk_le hpow hlt hmul4
                            clear hc; m6b_steps
                            exact ih_hm (ht_max <<< 1#64, ()) mhm
                              (by dsimp only; rw [hpow1, hpow]; omega)
                              ⟨hmhm, k + 1, hk1, hpow1, h1m1, hmul2_1⟩
                          · m6b_let; exact hJhm_exit () mhm hmhm
                        · m6b_let; exact hJhm_exit () mhm hmhm)
                    rintro _ ⟨⟩ me hme
                    have hme4 : (FullMem c s4 ⋆ R) me := hme ▸ hm4
                    let ht_off := BitVec.ofNat 64 c.scratch_cap - ht_max
                    have hht_off_n : ht_off.toNat = c.scratch_cap - ht_max.toNat := by
                      dsimp only [ht_off]
                      rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by
                        rw [bv64_ofNat_toNat_lt (by omega)]; omega)),
                        bv64_ofNat_toNat_lt (by omega)]
                    let rem_occ := ht_off - g_len
                    have hrem_n : rem_occ.toNat = ht_off.toNat - g_len.toNat := by
                      dsimp only [rem_occ]
                      rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by omega))]
                    m6b_to_group
                    refine wp_join_group (ts := [i64])
                      (fun (occ_bkt_bv, ()) mo => mo = m4 ∧
                        occ_bkt_bv.toNat =
                          (if 262144 ≤ rem_occ.toNat then 8192
                           else if 65536 ≤ rem_occ.toNat then 2048
                           else if 16384 ≤ rem_occ.toNat then 512
                           else if 2048 ≤ rem_occ.toNat then 256
                           else if 256 ≤ rem_occ.toNat then 32 else 16))
                      ?_
                      (fun Jocc hJocc => by
                        m6b_split
                        · have h262k : 262144 ≤ rem_occ.toNat := by
                            have h := bv64_ule_true_le hc
                            rw [show (262144 : BitVec 64).toNat = 262144 from rfl] at h; exact h
                          m6b_let; exact hJocc (8192#64, ()) me ⟨hme, by simp [h262k]⟩
                        · have hlt262k : ¬ 262144 ≤ rem_occ.toNat := by
                            have h := bv64_ule_false_lt hc
                            rw [show (262144 : BitVec 64).toNat = 262144 from rfl] at h
                            change rem_occ.toNat < 262144 at h; omega
                          clear hc; m6b_to_group
                          refine wp_join_group (ts := [i64])
                            (fun (o1, ()) mo1 => mo1 = m4 ∧ o1.toNat =
                              (if 65536 ≤ rem_occ.toNat then 2048
                               else if 16384 ≤ rem_occ.toNat then 512
                               else if 2048 ≤ rem_occ.toNat then 256
                               else if 256 ≤ rem_occ.toNat then 32 else 16))
                            (fun _ ⟨o1, ⟨⟩⟩ mo1 ⟨hmo1, ho1⟩ =>
                              hJocc (o1, ()) mo1 ⟨hmo1, by simp [hlt262k, ho1]⟩)
                            (fun Jocc1 hJocc1 => by
                              m6b_split
                              · have h65k : 65536 ≤ rem_occ.toNat := by
                                  have h := bv64_ule_true_le hc
                                  rw [show (65536 : BitVec 64).toNat = 65536 from rfl] at h; exact h
                                m6b_let; exact hJocc1 (2048#64, ()) me ⟨hme, by simp [h65k]⟩
                              · have hlt65k : ¬ 65536 ≤ rem_occ.toNat := by
                                  have h := bv64_ule_false_lt hc
                                  rw [show (65536 : BitVec 64).toNat = 65536 from rfl] at h
                                  change rem_occ.toNat < 65536 at h; omega
                                clear hc; m6b_to_group
                                refine wp_join_group (ts := [i64])
                                  (fun (o2, ()) mo2 => mo2 = m4 ∧ o2.toNat =
                                    (if 16384 ≤ rem_occ.toNat then 512
                                     else if 2048 ≤ rem_occ.toNat then 256
                                     else if 256 ≤ rem_occ.toNat then 32 else 16))
                                  (fun _ ⟨o2, ⟨⟩⟩ mo2 ⟨hmo2, ho2⟩ =>
                                    hJocc1 (o2, ()) mo2 ⟨hmo2, by simp [hlt65k, ho2]⟩)
                                  (fun Jocc2 hJocc2 => by
                                    m6b_split
                                    · have h16k : 16384 ≤ rem_occ.toNat := by
                                        have h := bv64_ule_true_le hc
                                        rw [show (16384 : BitVec 64).toNat = 16384 from rfl] at h
                                        exact h
                                      m6b_let; exact hJocc2 (512#64, ()) me ⟨hme, by simp [h16k]⟩
                                    · have hlt16k : ¬ 16384 ≤ rem_occ.toNat := by
                                        have h := bv64_ule_false_lt hc
                                        rw [show (16384 : BitVec 64).toNat = 16384 from rfl] at h
                                        change rem_occ.toNat < 16384 at h; omega
                                      clear hc; m6b_to_group
                                      refine wp_join_group (ts := [i64])
                                        (fun (o3, ()) mo3 => mo3 = m4 ∧ o3.toNat =
                                          (if 2048 ≤ rem_occ.toNat then 256
                                           else if 256 ≤ rem_occ.toNat then 32 else 16))
                                        (fun _ ⟨o3, ⟨⟩⟩ mo3 ⟨hmo3, ho3⟩ =>
                                          hJocc2 (o3, ()) mo3 ⟨hmo3, by simp [hlt16k, ho3]⟩)
                                        (fun Jocc3 hJocc3 => by
                                          m6b_split
                                          · have h2k : 2048 ≤ rem_occ.toNat := by
                                              have h := bv64_ule_true_le hc
                                              rw [show (2048 : BitVec 64).toNat = 2048 from rfl]
                                                at h; exact h
                                            m6b_let
                                            exact hJocc3 (256#64, ()) me ⟨hme, by simp [h2k]⟩
                                          · have hlt2k : ¬ 2048 ≤ rem_occ.toNat := by
                                              have h := bv64_ule_false_lt hc
                                              rw [show (2048 : BitVec 64).toNat = 2048 from rfl]
                                                at h
                                              change rem_occ.toNat < 2048 at h; omega
                                            clear hc; m6b_to_group
                                            refine wp_join_group (ts := [i64])
                                              (fun (o4, ()) mo4 => mo4 = m4 ∧ o4.toNat =
                                                (if 256 ≤ rem_occ.toNat then 32 else 16))
                                              (fun _ ⟨o4, ⟨⟩⟩ mo4 ⟨hmo4, ho4⟩ =>
                                                hJocc3 (o4, ()) mo4 ⟨hmo4, by simp [hlt2k, ho4]⟩)
                                              (fun Jocc4 hJocc4 => by
                                                m6b_split
                                                · have h256o : 256 ≤ rem_occ.toNat := by
                                                    have h := bv64_ule_true_le hc
                                                    rw [show (256 : BitVec 64).toNat = 256 from rfl]
                                                      at h; exact h
                                                  m6b_let
                                                  exact hJocc4 (32#64, ()) me
                                                    ⟨hme, by simp [h256o]⟩
                                                · have hlt256o : ¬ 256 ≤ rem_occ.toNat := by
                                                    have h := bv64_ule_false_lt hc
                                                    rw [show (256 : BitVec 64).toNat = 256 from rfl]
                                                      at h
                                                    change rem_occ.toNat < 256 at h; omega
                                                  m6b_let
                                                  exact hJocc4 (16#64, ()) me
                                                    ⟨hme, by simp [hlt256o]⟩)))))
                    rintro _ ⟨occ_bkt_bv, ⟨⟩⟩ mo ⟨hmo, hocc_eq⟩
                    let occ_bkt := occ_bkt_bv.toNat
                    have ⟨ho_pos, ho_8192, hopow, hocc38, hg_le_co, hcq, hqi, hib, hbh, hc_cap,
                        hc8, hhm_cap⟩ :=
                      fid_cd_layout_params hhm_ge h1m (by rw [← hfree_n]; exact hmul2) (by omega)
                        hsc hht_off_n hrem_n
                    rw [← hocc_eq] at ho_pos ho_8192 hopow hocc38 hg_le_co hcq hqi hib hbh
                    rw [← hocc_eq] at hc_cap hc8
                    let bkt_off := ht_off.toNat - occ_bkt
                    let inq_off := bkt_off - occ_bkt
                    let q_off := inq_off - occ_bkt
                    let ctrl_off := q_off - 8
                    have hco_n : (BitVec.ofNat 64 c.scratch_cap - ht_max - occ_bkt_bv -
                        occ_bkt_bv - occ_bkt_bv - 8#64).toNat = ctrl_off := by
                      dsimp only [ctrl_off, q_off, inq_off, bkt_off]; rw [hht_off_n]
                      exact fid_cd_ctrl_off_toNat (by omega) (by omega) hsc
                    have hco_eq : BitVec.ofNat 64 c.scratch_cap - ht_max - occ_bkt_bv - occ_bkt_bv -
                        occ_bkt_bv - 8#64 = BitVec.ofNat 64 ctrl_off :=
                      BitVec.eq_of_toNat_eq (hco_n.trans (bv64_ofNat_toNat_lt (by omega)).symm)
                    m6b_to_group
                    refine wp_loop_inv (ts := [i64])
                      (fun (ht_sz, ()) mhs => mhs = m4 ∧ 64 ≤ ht_sz.toNat ∧
                        ht_sz.toNat ≤ ht_max.toNat)
                      (fun (ht_sz, ()) _ => ht_max.toNat - ht_sz.toNat)
                      (fun Jhs hJhs => by
                        m6b_let
                        exact hJhs (64#64, ()) mo ⟨hmo, by decide,
                          by rw [show (64#64 : BitVec 64).toNat = 64 from rfl]; omega⟩)
                      (fun Jhs (ht_sz, ()) mhs ⟨hmhs, hhs_lo, hhs_hi⟩ ih_hs => ?_)
                    m6b_to_group
                    refine wp_join_group (ts := []) (fun () mhs2 => mhs2 = m4) ?_
                      (fun Jhs_exit hJhs_exit => by
                        m6b_steps; m6b_split
                        · clear hc; m6b_split
                          · have hshl_n : (ht_sz <<< 1#64).toNat = 2 * ht_sz.toNat := by
                              rw [show (ht_sz <<< 1#64 : BitVec 64) = ht_sz <<< (1 : Nat) from rfl,
                                BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm]
                              exact Nat.mod_eq_of_lt (by omega)
                            have hle_hm : (ht_sz <<< 1#64).toNat ≤ ht_max.toNat :=
                              bv64_ule_true_le hc
                            clear hc; m6b_steps
                            exact ih_hs (ht_sz <<< 1#64, ()) mhs
                              (by dsimp only; rw [hshl_n]; omega)
                              ⟨hmhs, by rw [hshl_n]; omega, hle_hm⟩
                          · m6b_let; exact hJhs_exit () mhs hmhs
                        · m6b_let; exact hJhs_exit () mhs hmhs)
                    rintro _ ⟨⟩ mhs2 hmhs2
                    m6b_to_group
                    refine wp_loop_inv (ts := [i64])
                      (fun (i3, ()) ms => ∃ scri : List (BitVec 32),
                        scri.length = c.scratch_cap ∧ i3.toNat ≤ ht_sz.toNat ∧
                        (∀ idx < g_len.toNat, scri[idx]? = s4.scratch.scratch_buf[idx]?) ∧
                        (∀ k' < i3.toNat,
                          scri[ht_off.toNat + k']?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32) ∧
                        (FullMem c
                          { s4 with scratch := { s4.scratch with scratch_buf := scri } } ⋆ R) ms)
                      (fun (i3, ()) _ => ht_sz.toNat - i3.toNat)
                      (fun Js hJs => by
                        m6b_let
                        exact hJs (0#64, ()) mhs2
                          ⟨s4.scratch.scratch_buf, hdw4.1.scratch_ok.scratch_buf_len,
                           Nat.zero_le _, fun _ _ => rfl, fun _ h => by simp at h, hmhs2 ▸ hm4⟩)
                      (fun Js (i3, ()) ms ⟨scri, hscrl_i, hi3_le, hpref_i, hinit_i, hms⟩ ihs => ?_)
                    m6b_split
                    · have hi3_lt : i3.toNat < ht_sz.toNat := bv64_ult_lt hc
                      have hi3_1 : (i3 + 1#64).toNat = i3.toNat + 1 := bv64_add1_lt (by omega)
                      have hadd_n : (ht_off + i3).toNat = ht_off.toNat + i3.toNat := by
                        rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
                      have hadd_arr : (ht_off + i3).toNat < scri.length := by rw [hadd_n]; omega
                      clear hc; m6b_steps; rw [hadd_n] at hm
                      obtain ⟨hpref_i', hinit_i'⟩ :=
                        fid_cd_ht_set_step (by omega) hpref_i hinit_i (by omega)
                      exact ihs (i3 + 1#64, ()) m (by dsimp only; omega)
                        ⟨scri.set (ht_off.toNat + i3.toNat) 0xFFFFFFFF#32, by simp [hscrl_i],
                         by rw [hi3_1]; omega, hpref_i', hi3_1 ▸ hinit_i', hm⟩
                    · have hi3_eq : i3.toNat = ht_sz.toNat := by
                        have := bv64_ult_not_lt hc; omega
                      rw [hi3_eq] at hinit_i
                      have hht4 : FidCongHtInv 64 F_cur cv0 s4.scratch.scratch_buf scri
                          g_len.toNat ht_off.toNat ht_sz.toNat :=
                        fun k' hk' => Or.inl (hinit_i k' hk')
                      have hctrl_st := fid_cd_ctrl_store_layout hg_le_co (by omega) ho_pos
                        ho_8192 hopow (by omega) hc_cap hc8 hcq hqi hib hbh (by omega)
                        hscrl_i hpref_i (hcv40 ▸ hht4)
                      have hco_add : ∀ j : BitVec 64, j.toNat < 8 →
                          (BitVec.ofNat 64 ctrl_off + j).toNat = ctrl_off + j.toNat := fun j hj =>
                        by rw [BitVec.toNat_add, bv64_ofNat_toNat_lt (by omega),
                          Nat.mod_eq_of_lt (by omega)]
                      have hco_b1 := hco_add 1 (by decide)
                      have hco_b2 := hco_add 2 (by decide)
                      have hco_b3 := hco_add 3 (by decide)
                      have hco_b4 := hco_add 4 (by decide)
                      have hco_b5 := hco_add 5 (by decide)
                      have hco_b6 := hco_add 6 (by decide)
                      have hco_b7 := hco_add 7 (by decide)
                      clear hc
                      try rw [show (8 : BitVec 64) = 8#64 from rfl, hco_eq]
                      m6b_steps
                      have hbkt_n : (BitVec.ofNat 64 c.scratch_cap - ht_max - occ_bkt_bv).toNat =
                          bkt_off := by
                        dsimp only [bkt_off]
                        rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by
                          change occ_bkt ≤ ht_off.toNat; omega))]
                      have hinq_n : (BitVec.ofNat 64 c.scratch_cap - ht_max - occ_bkt_bv -
                          occ_bkt_bv).toNat = inq_off := by
                        dsimp only [inq_off]
                        rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by rw [hbkt_n]; omega)),
                          hbkt_n]
                      have hq_n : (BitVec.ofNat 64 c.scratch_cap - ht_max - occ_bkt_bv -
                          occ_bkt_bv - occ_bkt_bv).toNat = q_off := by
                        dsimp only [q_off]
                        rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by rw [hinq_n]; omega)),
                          hinq_n]
                      simp only [bv64_ofNat_toNat_lt (by omega : ctrl_off < 2 ^ 64),
                        hco_b1, hco_b2, hco_b3, hco_b4, hco_b5, hco_b6, hco_b7,
                        bv64_setWidth32_eq (rfl : occ_bkt_bv.toNat = occ_bkt),
                        bv64_setWidth32_eq hbkt_n, bv64_setWidth32_eq hinq_n,
                        bv64_setWidth32_eq hq_n,
                        bv64_setWidth32_eq (rfl : ht_sz.toNat = ht_sz.toNat)] at hm
                      try rw [show (8 : BitVec 64) = 8#64 from rfl, hco_eq]
                      m6b_call hWorklist
                      refine ⟨c, F0, F_cur, _, s4.scratch.scratch_buf, occ_bkt,
                        bkt_off, inq_off, q_off, ht_off.toNat, ht_sz.toNat, R, rfl,
                        fid_denseInvW_with_scr_res0 hdw4 hctrl_st.1,
                        hcv40 ▸ hrepr4_inv, hg_pos, by unfold fidCongHashMaxSz; omega,
                        by rw [bv64_ofNat_toNat_lt (by omega)]; exact hctrl_st.2.1,
                        hseq4, hctrl_st.2.2.1, hcv40 ▸ hctrl_st.2.2.2,
                        hm, fun r4 s4w m4w hdw4w hcv4w hfl4w hrepr4w _hr4_dom hr4_uns hm4w => ?_⟩
                      have hcv4w0 : s4w.core.cur_vars = cv0 := hcv4w.trans hcv40
                      have hfl4w0 : s4w.core.fuel = fuel0 := hfl4w.trans hfl40
                      m6b_split
                      · m6b_to_group
                        refine wp_loop_inv (ts := [i64])
                          (fun (it, ()) mt => ∃ tmkt : List (BitVec 32),
                            tmkt.length = 2 * c.max_vars ∧ it.toNat ≤ cv0 ∧
                            (FullMem c { s4w with scratch :=
                              { s4w.scratch with tarjan_mark := tmkt } } ⋆ R) mt)
                          (fun (it, ()) _ => cv0 - it.toNat)
                          (fun Jt hJt => by
                            m6b_let; exact hJt (0#64, ()) m4w
                              ⟨s4w.scratch.tarjan_mark, hdw4w.1.scratch_ok.tarjan_mark_len,
                               Nat.zero_le _, hm4w⟩)
                          (fun Jt (it, ()) mt ⟨tmkt, htlt, hit_le, hmt⟩ iht => ?_)
                        m6b_split
                        · have hit_lt : it.toNat < cv0 := by
                            have h := bv64_ult_lt hc
                            rwa [hcv10, bv64_ofNat_toNat_lt (by omega)] at h
                          have hit1 : (it + 1#64).toNat = it.toNat + 1 := bv64_add1_lt (by omega)
                          have hit_arr : it.toNat < tmkt.length := by omega
                          clear hc; m6b_steps
                          exact iht (it + 1#64, ()) m (by dsimp only; omega)
                            ⟨tmkt.set it.toNat 0#32, by simp [htlt], by rw [hit1]; omega, hm⟩
                        · clear hc; m6b_steps
                          exact hQ 20#64 _ m
                            (fid_denseInvW_with_tmk_ar hdw4w htlt 0#64 0#64).toDense
                            hcv4w0 hfl4w0 (Or.inr rfl) (fun _ => hr4_uns (beq_iff_eq.mp hc)) hm
                      · m6b_let
                        exact hJwl_if (_, ()) m4w
                          ⟨s4w, hdw4w, hcv4w0, hfl4w0, hcv4w0 ▸ hcv4w ▸ hrepr4w, hm4w⟩
                  · clear hc; m6b_let
                    exact hJwl_if (i, ()) m4 ⟨s4, hdw4, hcv40, hfl40, hrepr4_inv, hm4⟩
                · clear hc; m6b_let
                  exact hJwl_if (i, ()) m4 ⟨s4, hdw4, hcv40, hfl40, hrepr4_inv, hm4⟩)
              ?_
            intro Jite hJite
            m6b_split
            · have hgl32 : (g_len0.setWidth 32).toNat = g_len0.toNat := by
                rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
              have hgc32 : (g_cap.setWidth 32).toNat = g_cap.toNat := by
                rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
              clear hc; m6b_steps; m6b_call hExtIteAll
              refine ⟨64, c, F0, F_cur, s4a, R, by decide, by decide, rfl, hdw4a,
                by rw [hgl32, hgc32]; exact hgl0_le, by rw [hgc32]; omega,
                by rw [hgl32, hcv4a]; exact hseq4a, hm4a,
                fun ret32 s4b m4b hdw4b hcore4b _ _ _ _ _ _ _ _ hg_hi _ hseq4b hm4b => ?_⟩
              have hret64 : (ret32.setWidth 64).toNat = ret32.toNat := by
                rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := ret32.isLt; omega)]
              have hcv4b0 : s4b.core.cur_vars = cv0 :=
                (congrArg FullCoreState.cur_vars hcore4b).trans hcv4a0
              have hfl4b0 : s4b.core.fuel = fuel0 :=
                (congrArg FullCoreState.fuel hcore4b).trans hfl4a0
              have hrepr4b_inv : FullCongReprInv F_cur (2 * cv0) s4b.core.repr := by
                rw [congrArg FullCoreState.repr hcore4b]; exact hrepr4a_inv
              m6b_steps
              exact hJite (ret32.setWidth 64, ()) m4b
                ⟨s4b, hdw4b, hcv4b0, hfl4b0, hrepr4b_inv,
                 by rw [← hret64, hgc32] at hg_hi; exact hg_hi,
                 by rw [hret64, hcore4b]; exact hseq4b, hm4b⟩
            · exfalso
              have hgt := bv64_ule_false_lt hc
              omega

end CongDenseFid

end LeanQbe.T.Examples.Kissat.FullFidelityCong

end
