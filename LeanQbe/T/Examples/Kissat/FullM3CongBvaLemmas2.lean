module

public import LeanQbe.T.Examples.Kissat.FullM3CongBvaLemmas1
public meta import Lean.Elab.Tactic
public meta import LeanQbe.T.Logic.C0HeadStep
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Full` M3b Congruence & BVA/BVE Proofs — Part 2 (`full_cong_work_step` Helpers)

Builds on `FullM3CongBvaLemmas1` to provide pure XOR/ITE/AND folding helpers, `WorkStepOk`,
`HashGateOk`, `wsState`, branch-step lemmas, and fast C0 head tactics for `full_cong_work_step`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM3CongBva

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullCongHelpers
open Kraken.Bedrock2.Test

/-! ## 1. Pure BitVec, List, XOR/ITE/AND Folding & Hash-Matching Helpers -/

section FoldAndHashHelpers

private theorem c0_load_full_tmp0 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem c s ⋆ R) m) (h0 : 0 < s.core.tmp.length) :
    loadVal m i32 (c.pTmp + 0#64) = some (s.core.tmp[0]'h0) := by
  simpa using FullArenaTactics.c0_load_full_tmp (i := 0#64) (by simpa using h0) hm

private theorem c0_load_full_tmp1 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem c s ⋆ R) m) (h1 : 1 < s.core.tmp.length) :
    loadVal m i32 (c.pTmp + 4#64) = some (s.core.tmp[1]'h1) := by
  simpa using FullArenaTactics.c0_load_full_tmp (i := 1#64) (by simpa using h1) hm

private theorem c0_load_full_tmp2 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem c s ⋆ R) m) (h2 : 2 < s.core.tmp.length) :
    loadVal m i32 (c.pTmp + 8#64) = some (s.core.tmp[2]'h2) := by
  simpa using FullArenaTactics.c0_load_full_tmp (i := 2#64) (by simpa using h2) hm

private theorem c0_store_full_tmp0 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (v : BitVec 32) (h0 : 0 < s.core.tmp.length) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 (c.pTmp + 0#64) ∧
      (FullMem c { s with core := { s.core with tmp := s.core.tmp.set 0 v } } ⋆ R)
        (storeMem m i32 (c.pTmp + 0#64) v) := by
  simpa using FullArenaTactics.c0_store_full_tmp (i := 0#64) v (by simpa using h0) hm

private theorem c0_store_full_tmp1 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (v : BitVec 32) (h1 : 1 < s.core.tmp.length) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 (c.pTmp + 4#64) ∧
      (FullMem c { s with core := { s.core with tmp := s.core.tmp.set 1 v } } ⋆ R)
        (storeMem m i32 (c.pTmp + 4#64) v) := by
  simpa using FullArenaTactics.c0_store_full_tmp (i := 1#64) v (by simpa using h1) hm

private theorem c0_store_full_tmp2 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (v : BitVec 32) (h2 : 2 < s.core.tmp.length) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 (c.pTmp + 8#64) ∧
      (FullMem c { s with core := { s.core with tmp := s.core.tmp.set 2 v } } ⋆ R)
        (storeMem m i32 (c.pTmp + 8#64) v) := by
  simpa using FullArenaTactics.c0_store_full_tmp (i := 2#64) v (by simpa using h2) hm

attribute [local c0_load] c0_load_full_tmp0 c0_load_full_tmp1 c0_load_full_tmp2
attribute [local c0_store] c0_store_full_tmp0 c0_store_full_tmp1 c0_store_full_tmp2

theorem bv32_ult_lt {a b : BitVec 32} (h : (a.ult b) = true) : a.toNat < b.toNat := by
  simpa [BitVec.ult] using h

theorem bv32_ult_not_lt {a b : BitVec 32} (h : (a.ult b) = false) : ¬ a.toNat < b.toNat := by
  simpa [BitVec.ult] using h

theorem bv64_ult_lt {a b : BitVec 64} (h : (a.ult b) = true) : a.toNat < b.toNat := by
  simpa [BitVec.ult] using h

theorem bv64_ult_not_lt {a b : BitVec 64} (h : (a.ult b) = false) : ¬ a.toNat < b.toNat := by
  simpa [BitVec.ult] using h

theorem bv32_add1_toNat {a : BitVec 32} {n : Nat} (ha : a.toNat < n) (hn : n < 2 ^ 32) :
    (a + 1#32).toNat = a.toNat + 1 :=
  show (a.toNat + 1) % 2 ^ 32 = a.toNat + 1 from Nat.mod_eq_of_lt (by omega)

theorem bv32_sub1_toNat {a : BitVec 32} (hp : 0 < a.toNat) :
    (a - 1#32).toNat = a.toNat - 1 := by bv_omega

theorem bv64_add1_toNat {a : BitVec 64} {n : Nat} (ha : a.toNat < n) (hn : n < 2 ^ 64) :
    (a + 1#64).toNat = a.toNat + 1 :=
  show (a.toNat + 1) % 2 ^ 64 = a.toNat + 1 from Nat.mod_eq_of_lt (by omega)

theorem bv32_shr1_eq_div2 {a b : BitVec 32} (h : (a >>> 1 == b >>> 1) = true) :
    a.toNat / 2 = b.toNat / 2 := by
  have h1 := congrArg BitVec.toNat (beq_iff_eq.mp h)
  simpa [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] using h1

theorem list_getElem_zext32_eq {α : Type} {xs ys : List α} (heq : xs = ys) {k : BitVec 32}
    (hz : (k.setWidth 64).toNat < xs.length) (hk : k.toNat < ys.length) :
    xs[(k.setWidth 64).toNat]'hz = ys[k.toNat]'hk := by
  subst heq; exact list_getElem_congr (bv_zext32_toNat k) hz hk

theorem list_getElem_eq_of_eqD {α : Type} [Inhabited α] {xs : List α} {i : Nat} {x : α}
    (hi : i < xs.length) (h : xs[i]? = some x) : xs[i]'hi = x := by
  rw [List.getElem?_eq_getElem hi] at h; exact Option.some.inj h

theorem ws_tag_eq {w mword c : BitVec 32} (hw : w = mword) (hc : (w >>> 28 == c) = true) :
    mword >>> 28 = c := by rw [hw] at hc; exact beq_iff_eq.mp hc

theorem ws_tag_ne {w mword c : BitVec 32} (hw : w = mword) (hc : (w >>> 28 == c) = false) :
    mword >>> 28 ≠ c := by rw [hw] at hc; exact beq_eq_false_iff_ne.mp hc

theorem ws_har_eq {w mword c : BitVec 32} (hw : w = mword) (hc : (w &&& 0xFF#32 == c) = true) :
    mword &&& 0xFF#32 = c := by rw [hw] at hc; exact beq_iff_eq.mp hc

theorem ws_har_ne {w mword c : BitVec 32} (hw : w = mword) (hc : (w &&& 0xFF#32 == c) = false) :
    mword &&& 0xFF#32 ≠ c := by rw [hw] at hc; exact beq_eq_false_iff_ne.mp hc

theorem bv8_eqff_of_signExtend32_slt0 {v : BitVec 8}
    (hdom : v = 0#8 ∨ v = 1#8 ∨ v = 0xFF#8)
    (hslt : (v.signExtend 32).slt 0#32 = true) : v = 0xFF#8 := by
  rcases hdom with rfl | rfl | rfl <;> first | rfl | cases hslt

theorem vals_sgt0_eq1 {vals : List (BitVec 8)} {l : BitVec 32}
    (hl : l.toNat < vals.length) (hz : (l.setWidth 64).toNat < vals.length)
    (hdom : vals[l.toNat]?.getD 0#8 = 0#8 ∨ vals[l.toNat]?.getD 0#8 = 1#8 ∨
      vals[l.toNat]?.getD 0#8 = 0xFF#8)
    (hc : (0#32 : BitVec 32).slt ((vals[(l.setWidth 64).toNat]'hz).signExtend 32) = true) :
    vals[l.toNat]?.getD 0#8 = 1#8 := by
  rw [List.getElem?_eq_getElem hl, Option.getD_some] at hdom ⊢
  rw [list_getElem_congr (bv_zext32_toNat l) hz hl] at hc
  exact bv8_eq1_of_signExtend32_sgt0 hdom hc

theorem vals_slt0_eqff {vals : List (BitVec 8)} {l : BitVec 32}
    (hl : l.toNat < vals.length) (hz : (l.setWidth 64).toNat < vals.length)
    (hdom : vals[l.toNat]?.getD 0#8 = 0#8 ∨ vals[l.toNat]?.getD 0#8 = 1#8 ∨
      vals[l.toNat]?.getD 0#8 = 0xFF#8)
    (hc : ((vals[(l.setWidth 64).toNat]'hz).signExtend 32).slt 0#32 = true) :
    vals[l.toNat]?.getD 0#8 = 0xFF#8 := by
  rw [List.getElem?_eq_getElem hl, Option.getD_some] at hdom ⊢
  rw [list_getElem_congr (bv_zext32_toNat l) hz hl] at hc
  exact bv8_eqff_of_signExtend32_slt0 hdom hc

theorem vals_ne0_1_or_ff {vals : List (BitVec 8)} {l : BitVec 32}
    (hl : l.toNat < vals.length) (hz : (l.setWidth 64).toNat < vals.length)
    (hdom : vals[l.toNat]?.getD 0#8 = 0#8 ∨ vals[l.toNat]?.getD 0#8 = 1#8 ∨
      vals[l.toNat]?.getD 0#8 = 0xFF#8)
    (hc : ((vals[(l.setWidth 64).toNat]'hz).signExtend 32 != 0#32) = true) :
    vals[l.toNat]?.getD 0#8 = 1#8 ∨ vals[l.toNat]?.getD 0#8 = 0xFF#8 := by
  rw [List.getElem?_eq_getElem hl, Option.getD_some] at hdom ⊢
  rw [list_getElem_congr (bv_zext32_toNat l) hz hl] at hc
  have hne := bv8_ne0_of_signExtend32 hdom (bne_iff_ne.mp hc)
  rcases hdom with h0 | h1 | hff
  · exact absurd h0 hne
  · exact Or.inl h1
  · exact Or.inr hff

theorem vals_ne0_nsgt0_eqff {vals : List (BitVec 8)} {l : BitVec 32}
    (hl : l.toNat < vals.length) (hz : (l.setWidth 64).toNat < vals.length)
    (hdom : vals[l.toNat]?.getD 0#8 = 0#8 ∨ vals[l.toNat]?.getD 0#8 = 1#8 ∨
      vals[l.toNat]?.getD 0#8 = 0xFF#8)
    (h1ff : vals[l.toNat]?.getD 0#8 = 1#8 ∨ vals[l.toNat]?.getD 0#8 = 0xFF#8)
    (hc : (0#32 : BitVec 32).slt ((vals[(l.setWidth 64).toNat]'hz).signExtend 32) = false) :
    vals[l.toNat]?.getD 0#8 = 0xFF#8 := by
  rw [List.getElem?_eq_getElem hl, Option.getD_some] at hdom h1ff ⊢
  rw [list_getElem_congr (bv_zext32_toNat l) hz hl] at hc
  have hne : vals[l.toNat]'hl ≠ 0#8 := by
    rcases h1ff with h1 | hff
    · rw [h1]; decide
    · rw [hff]; decide
  exact bv8_ne0_not_signExtend32_sgt0_eqff hdom hne (Bool.eq_false_iff.mp hc)

theorem vals_nslt0_ne0_eq1 {vals : List (BitVec 8)} {l : BitVec 32}
    (hl : l.toNat < vals.length) (hz : (l.setWidth 64).toNat < vals.length)
    (hdom : vals[l.toNat]?.getD 0#8 = 0#8 ∨ vals[l.toNat]?.getD 0#8 = 1#8 ∨
      vals[l.toNat]?.getD 0#8 = 0xFF#8)
    (hnslt : ((vals[(l.setWidth 64).toNat]'hz).signExtend 32).slt 0#32 = false)
    (hne0 : ((vals[(l.setWidth 64).toNat]'hz).signExtend 32 == 0#32) = false) :
    vals[l.toNat]?.getD 0#8 = 1#8 := by
  rw [List.getElem?_eq_getElem hl, Option.getD_some] at hdom ⊢
  rw [list_getElem_congr (bv_zext32_toNat l) hz hl] at hnslt hne0
  exact bv8_eq1_of_signExtend32_ne0_nslt0 hdom (beq_eq_false_iff_ne.mp hne0)
    (bv8_not_slt0_of_signExtend32_nslt0 hdom hnslt)

theorem scr_e_lt {scr : List (BitVec 32)} {g_len : Nat} {ent : BitVec 32} (k : Nat)
    (hk_lt : ent.toNat + k < g_len) (hg_le : g_len ≤ scr.length)
    (hk64 : ent.toNat + k < 2 ^ 64) : (ent.setWidth 64 + BitVec.ofNat 64 k).toNat <
      scr.length := by
  rw [BitVec.toNat_add, bv_zext32_toNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega), Nat.mod_eq_of_lt hk64]; omega

theorem scr_e_get {scr scr0 : List (BitVec 32)} {g_len : Nat} {ent r : BitVec 32}
    (k : Nat) (hk_lt : ent.toNat + k < g_len)
    (hpref : ∀ idx < g_len, scr[idx]? = scr0[idx]?) (hscr0 : scr0[ent.toNat + k]? = some r)
    (harr : (ent.setWidth 64 + BitVec.ofNat 64 k).toNat < scr.length)
    (hk64 : ent.toNat + k < 2 ^ 64) :
    scr[(ent.setWidth 64 + BitVec.ofNat 64 k).toNat]'harr = r := by
  have hn : (ent.setWidth 64 + BitVec.ofNat 64 k).toNat = ent.toNat + k := by
    rw [BitVec.toNat_add, bv_zext32_toNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega)]
    exact Nat.mod_eq_of_lt hk64
  have h := (hpref (ent.toNat + k) hk_lt).trans hscr0
  rw [← hn, List.getElem?_eq_getElem harr] at h; exact Option.some.inj h

theorem scr_g2i_get {scr scr0 : List (BitVec 32)} {g : BitVec 64} {i : BitVec 32}
    {g_len : Nat} {ri : BitVec 32} (hpref : ∀ idx < g_len, scr[idx]? = scr0[idx]?)
    (hget : scr0[g.toNat + 2 + i.toNat]? = some ri) (hlt : g.toNat + 2 + i.toNat < g_len)
    (hadd : (g + 2 + i.setWidth 64).toNat = g.toNat + 2 + i.toNat)
    (harr : (g + 2 + i.setWidth 64).toNat < scr.length) :
    scr[(g + 2 + i.setWidth 64).toNat]'harr = ri := by
  have h := (hpref (g.toNat + 2 + i.toNat) hlt).trans hget
  rw [← hadd, List.getElem?_eq_getElem harr] at h; exact Option.some.inj h

theorem tmp_st_get {xs ys : List (BitVec 32)} {k : Nat} (heq : xs = ys)
    (hx : k < xs.length) : xs[k]'hx = ys[k]?.getD 0#32 := by
  rw [List.getElem?_eq_getElem (heq ▸ hx), Option.getD_some]; exact Option.some.inj
    (by rw [← List.getElem?_eq_getElem hx, ← List.getElem?_eq_getElem (heq ▸ hx), heq])

theorem xorGateDef_comm {f : CNF Nat} {g a b : Nat} (h : XorGateDef f g a b) :
    XorGateDef f g b a :=
  xorGateDef_of_eval_eq fun α hα => by
    rw [xorGateDef_eval hα h]; cases evalLitVal α a <;> cases evalLitVal α b <;> rfl

theorem xor_eval_congr {f : CNF Nat} {lhs0 lhs a0 a b0 b : Nat}
    (hx : XorGateDef f lhs0 a0 b0) (hl : LitEquiv f lhs0 lhs)
    (ha : LitEquiv f a0 a) (hb : LitEquiv f b0 b) :
    XorGateDef f lhs a b :=
  xorGateDef_of_eval_eq fun α hα => by
    rw [← litEquiv_eval hα hl, ← litEquiv_eval hα ha, ← litEquiv_eval hα hb, xorGateDef_eval hα hx]

theorem xor_const_equiv {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {k : FullCoreState}
    (hw : FullWitnessInv c F0 F_cur k) (hcl0 : k.cur_level = 0)
    {lhs a b : Nat} (hx : XorGateDef (cnfOfClauses F_cur) lhs a b)
    (ha_lt : a < 2 * k.cur_vars)
    (hdom : k.vals[a]?.getD 0#8 = 1#8 ∨ k.vals[a]?.getD 0#8 = 0xFF#8) :
    LitEquiv (cnfOfClauses F_cur) lhs
      (if k.vals[a]?.getD 0#8 = 1#8 then litNeg b else b) := by
  refine litEquiv_of_eval_eq fun α hα => ?_
  rw [xorGateDef_eval hα hx]
  rcases hdom with h1 | hff
  · rw [h1, ite_eq_left rfl, evalLitVal_litNeg,
      entails_eval_true (vals1_entails hw hcl0 ha_lt h1) hα]; cases evalLitVal α b <;> rfl
  · have hne : (0xFF#8 : BitVec 8) ≠ 1#8 := by decide
    rw [hff, ite_eq_right hne, entails_neg_eval_false (valsff_entails_neg hw hcl0 ha_lt hff) hα]
    cases evalLitVal α b <;> rfl

theorem ite_eval_congr {f : CNF Nat} {lhs0 lhs c0 c t0 t e0 e : Nat}
    (hi : IteGateDef f lhs0 c0 t0 e0) (hl : LitEquiv f lhs0 lhs)
    (hc : LitEquiv f c0 c) (ht : LitEquiv f t0 t) (he : LitEquiv f e0 e) :
    IteGateDef f lhs c t e :=
  iteGateDef_of_eval_eq fun α hα => by
    rw [← litEquiv_eval hα hl, ← litEquiv_eval hα hc, ← litEquiv_eval hα ht,
      ← litEquiv_eval hα he, iteGateDef_eval hα hi]

theorem ite_cond_const_equiv {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (hcl0 : k.cur_level = 0)
    {lhs condLit t e : Nat} (hi : IteGateDef (cnfOfClauses F_cur) lhs condLit t e)
    (hc_lt : condLit < 2 * k.cur_vars)
    (hdom : k.vals[condLit]?.getD 0#8 = 1#8 ∨ k.vals[condLit]?.getD 0#8 = 0xFF#8) :
    LitEquiv (cnfOfClauses F_cur) lhs
      (if k.vals[condLit]?.getD 0#8 = 1#8 then t else e) := by
  refine litEquiv_of_eval_eq fun α hα => ?_
  rw [iteGateDef_eval hα hi]
  rcases hdom with h1 | hff
  · rw [h1, ite_eq_left rfl, entails_eval_true (vals1_entails hw hcl0 hc_lt h1) hα]; rfl
  · have hne : (0xFF#8 : BitVec 8) ≠ 1#8 := by decide
    rw [hff, ite_eq_right hne, entails_neg_eval_false (valsff_entails_neg hw hcl0 hc_lt hff) hα]
    rfl

theorem ite_branches_true_false_equiv {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (hcl0 : k.cur_level = 0)
    {lhs condLit t e : Nat} (hi : IteGateDef (cnfOfClauses F_cur) lhs condLit t e)
    (ht_lt : t < 2 * k.cur_vars) (he_lt : e < 2 * k.cur_vars)
    (ht1 : k.vals[t]?.getD 0#8 = 1#8) (heff : k.vals[e]?.getD 0#8 = 0xFF#8) :
    LitEquiv (cnfOfClauses F_cur) lhs condLit := by
  refine litEquiv_of_eval_eq fun α hα => ?_
  rw [iteGateDef_eval hα hi, entails_eval_true (vals1_entails hw hcl0 ht_lt ht1) hα,
    entails_neg_eval_false (valsff_entails_neg hw hcl0 he_lt heff) hα]
  cases evalLitVal α condLit <;> rfl

theorem ite_branches_false_true_equiv {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (hcl0 : k.cur_level = 0)
    {lhs condLit t e : Nat} (hi : IteGateDef (cnfOfClauses F_cur) lhs condLit t e)
    (ht_lt : t < 2 * k.cur_vars) (he_lt : e < 2 * k.cur_vars)
    (htff : k.vals[t]?.getD 0#8 = 0xFF#8) (he1 : k.vals[e]?.getD 0#8 = 1#8) :
    LitEquiv (cnfOfClauses F_cur) lhs (litNeg condLit) := by
  refine litEquiv_of_eval_eq fun α hα => ?_
  rw [iteGateDef_eval hα hi, evalLitVal_litNeg,
    entails_neg_eval_false (valsff_entails_neg hw hcl0 ht_lt htff) hα,
    entails_eval_true (vals1_entails hw hcl0 he_lt he1) hα]; cases evalLitVal α condLit <;> rfl

theorem ite_branches_both_true_entails {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (hcl0 : k.cur_level = 0)
    {lhs condLit t e : Nat} (hi : IteGateDef (cnfOfClauses F_cur) lhs condLit t e)
    (ht_lt : t < 2 * k.cur_vars) (he_lt : e < 2 * k.cur_vars)
    (ht1 : k.vals[t]?.getD 0#8 = 1#8) (he1 : k.vals[e]?.getD 0#8 = 1#8) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause [lhs]) := by
  refine entails_of_eval_mem fun α hα => ⟨lhs, List.mem_cons_self .., ?_⟩
  rw [iteGateDef_eval hα hi, entails_eval_true (vals1_entails hw hcl0 ht_lt ht1) hα,
    entails_eval_true (vals1_entails hw hcl0 he_lt he1) hα]
  cases evalLitVal α condLit <;> rfl

theorem ite_branches_both_false_entails {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (hcl0 : k.cur_level = 0)
    {lhs condLit t e : Nat} (hi : IteGateDef (cnfOfClauses F_cur) lhs condLit t e)
    (ht_lt : t < 2 * k.cur_vars) (he_lt : e < 2 * k.cur_vars)
    (htff : k.vals[t]?.getD 0#8 = 0xFF#8) (heff : k.vals[e]?.getD 0#8 = 0xFF#8) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause [litNeg lhs]) := by
  refine entails_of_eval_mem fun α hα => ⟨litNeg lhs, List.mem_cons_self .., ?_⟩
  rw [evalLitVal_litNeg, iteGateDef_eval hα hi,
    entails_neg_eval_false (valsff_entails_neg hw hcl0 ht_lt htff) hα,
    entails_neg_eval_false (valsff_entails_neg hw hcl0 he_lt heff) hα]
  cases evalLitVal α condLit <;> rfl

theorem mem_take_of_lt {α : Type} {xs : List α} {n k : Nat} (hk : k < n) (hn : n ≤ xs.length) :
    xs[k]'(by omega) ∈ xs.take n := by
  have hlt : k < (xs.take n).length := by rw [List.length_take]; omega
  simpa [List.getElem_take] using List.getElem_mem hlt

theorem lt_take_of_mem {α : Type} {xs : List α} {n : Nat} {x : α} (h : x ∈ xs.take n) :
    ∃ k < min n xs.length, xs[k]?.getD x = x := by
  obtain ⟨k, hk, hget⟩ := List.mem_iff_getElem.mp h
  rw [List.length_take] at hk
  refine ⟨k, hk, ?_⟩
  rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
  rwa [List.getElem_take] at hget

end FoldAndHashHelpers

/-! ## 2. WorkStep State Invariants, Branch Lemmas & Fast Head Tactics -/

section WorkStepSupport

open scoped FullArenaTactics FullCongTactics

/-- Flat `FullState` update touching only `repr` and `tmp` (avoids nested record wrappers). -/
def wsState (st : FullState) (repr tmp : List (BitVec 32)) : FullState :=
  { st with core := { st.core with repr := repr, tmp := tmp } }

theorem ws_unfocus_repr {c : FullCfg} {st : FullState} {repr0 tmp repr' : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (array (t := i32) c.pRepr repr' ⋆
      (FullReprRest c (wsState st repr0 tmp) ⋆ R)) m) :
    (FullMem c (wsState st repr' tmp) ⋆ R) m :=
  unfocus_full_repr hm

theorem ws_unfocus_tmp {c : FullCfg} {st : FullState} {repr tmp0 tmp' : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (array (t := i32) c.pTmp tmp' ⋆
      (FullTmpRest c (wsState st repr tmp0) ⋆ R)) m) :
    (FullMem c (wsState st repr tmp') ⋆ R) m :=
  unfocus_full_tmp hm

/-- Work-step loop invariant for `full_cong_work_step`. -/
def WorkStepOk (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (fuel0 : BitVec 64) (ar0 : List (BitVec 32)) (alen0 cv0 g_len ht_off ht_sz : Nat)
    (scr0 : List (BitVec 32)) (st : FullState) : Prop :=
  st.LengthsOk c ∧ FullWitnessInv c F0 F_cur st.core ∧
  FullLitMarksClear c st ∧ FullArenaVarsNodup st ∧ FullExtScratchOk c st ∧
  st.core.cur_level = 0 ∧ st.core.dense_mode ≠ 0#64 ∧
  st.core.cur_vars = cv0 ∧ st.core.fuel = fuel0 ∧
  st.core.arena = ar0 ∧ st.core.arena_len = alen0 ∧
  FullCongReprInv F_cur (2 * cv0) st.core.repr ∧
  (∀ idx < g_len, st.scratch.scratch_buf[idx]? = scr0[idx]?) ∧
  FullCongSpecs.CongHtInv F_cur cv0 scr0 st.scratch.scratch_buf g_len ht_off ht_sz

/-- Normalized gate invariant passed into the hash-probe loop. -/
def HashGateOk (F_cur : List (List Nat)) (cv0 : Nat) (lhs : BitVec 32)
    (tmps : List (BitVec 32)) (htag harity : BitVec 32) : Prop :=
  harity.toNat ≤ cv0 ∧
  (htag = 0#32 → 2 ≤ harity.toNat ∧ harity.toNat ≤ 8 ∧
    ∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α →
      evalLitVal α lhs.toNat =
        (List.range harity.toNat).all (fun k => evalLitVal α (tmps[k]?.getD 0#32).toNat)) ∧
  (htag = 1#32 → harity = 2#32 ∧
    XorGateDef (cnfOfClauses F_cur) lhs.toNat
      (tmps[0]?.getD 0#32).toNat (tmps[1]?.getD 0#32).toNat) ∧
  (htag = 2#32 → harity = 3#32 ∧
    IteGateDef (cnfOfClauses F_cur) lhs.toNat
      (tmps[0]?.getD 0#32).toNat (tmps[1]?.getD 0#32).toNat (tmps[2]?.getD 0#32).toNat)

theorem workStepOk_of_fold {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {fuel0 : BitVec 64} {ar0 : List (BitVec 32)} {alen0 cv0 g_len ht_off ht_sz : Nat}
    {scr0 : List (BitVec 32)} {st s' : FullState}
    (hok : WorkStepOk c F0 F_cur fuel0 ar0 alen0 cv0 g_len ht_off ht_sz scr0 st)
    (hl' : s'.LengthsOk c) (hw' : FullWitnessInv c F0 F_cur s'.core)
    (hmk' : FullLitMarksClear c s') (hnd' : FullArenaVarsNodup s')
    (hext' : FullExtScratchOk c s') (hcl' : s'.core.cur_level = 0)
    (hdm' : s'.core.dense_mode ≠ 0#64) (hcv' : s'.core.cur_vars = st.core.cur_vars)
    (hfl' : s'.core.fuel = st.core.fuel) (har' : s'.core.arena = st.core.arena)
    (hal' : s'.core.arena_len = st.core.arena_len)
    (hscr' : s'.scratch.scratch_buf = st.scratch.scratch_buf)
    (hrepr' : FullCongReprInv F_cur (2 * s'.core.cur_vars) s'.core.repr) :
    WorkStepOk c F0 F_cur fuel0 ar0 alen0 cv0 g_len ht_off ht_sz scr0 s' :=
  ⟨hl', hw', hmk', hnd', hext', hcl', hdm', hcv'.trans hok.2.2.2.2.2.2.2.1,
   hfl'.trans hok.2.2.2.2.2.2.2.2.1, har'.trans hok.2.2.2.2.2.2.2.2.2.1,
   hal'.trans hok.2.2.2.2.2.2.2.2.2.2.1,
   by rw [hcv'.trans hok.2.2.2.2.2.2.2.1] at hrepr'; exact hrepr',
   fun idx hi => by rw [hscr']; exact hok.2.2.2.2.2.2.2.2.2.2.2.2.1 idx hi,
   by unfold FullCongSpecs.CongHtInv; rw [hscr']; exact hok.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

theorem workStepOk_wsState {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {fuel0 : BitVec 64} {ar0 : List (BitVec 32)} {alen0 cv0 g_len ht_off ht_sz : Nat}
    {scr0 : List (BitVec 32)} {st : FullState}
    (hok : WorkStepOk c F0 F_cur fuel0 ar0 alen0 cv0 g_len ht_off ht_sz scr0 st)
    {repr' tmp' : List (BitVec 32)}
    (hrl' : repr'.length = 2 * c.max_vars) (htl' : tmp'.length = c.max_vars)
    (hrepr' : FullCongReprInv F_cur (2 * cv0) repr') :
    WorkStepOk c F0 F_cur fuel0 ar0 alen0 cv0 g_len ht_off ht_sz scr0
      (wsState st repr' tmp') :=
  ⟨⟨{ hok.1.core_ok with repr_len := hrl', tmp_len_arr := htl' }, hok.1.scratch_ok⟩,
   fullWitnessInv_with_tmp (fullWitnessInv_with_repr hok.2.1 repr') tmp',
   hok.2.2.1, hok.2.2.2.1, hok.2.2.2.2.1, hok.2.2.2.2.2.1, hok.2.2.2.2.2.2.1,
   hok.2.2.2.2.2.2.2.1, hok.2.2.2.2.2.2.2.2.1, hok.2.2.2.2.2.2.2.2.2.1,
   hok.2.2.2.2.2.2.2.2.2.2.1, hrepr',
   hok.2.2.2.2.2.2.2.2.2.2.2.2.1, hok.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

theorem workStepOk_with_repr {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {fuel0 : BitVec 64} {ar0 : List (BitVec 32)} {alen0 cv0 g_len ht_off ht_sz : Nat}
    {scr0 : List (BitVec 32)} {st : FullState}
    (hok : WorkStepOk c F0 F_cur fuel0 ar0 alen0 cv0 g_len ht_off ht_sz scr0 st)
    {repr' : List (BitVec 32)} (hrl' : repr'.length = 2 * c.max_vars)
    (hrepr' : FullCongReprInv F_cur (2 * cv0) repr') :
    WorkStepOk c F0 F_cur fuel0 ar0 alen0 cv0 g_len ht_off ht_sz scr0
      { st with core := { st.core with repr := repr' } } :=
  ⟨⟨{ hok.1.core_ok with repr_len := hrl' }, hok.1.scratch_ok⟩,
   fullWitnessInv_with_repr hok.2.1 repr', hok.2.2.1, hok.2.2.2.1, hok.2.2.2.2.1,
   hok.2.2.2.2.2.1, hok.2.2.2.2.2.2.1, hok.2.2.2.2.2.2.2.1, hok.2.2.2.2.2.2.2.2.1,
   hok.2.2.2.2.2.2.2.2.2.1, hok.2.2.2.2.2.2.2.2.2.2.1, hrepr',
   hok.2.2.2.2.2.2.2.2.2.2.2.2.1, hok.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

theorem ws_ret2_q {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {fuel0 : BitVec 64} {ar0 : List (BitVec 32)} {alen0 cv0 g_len ht_off ht_sz : Nat}
    {scr0 : List (BitVec 32)} {su : FullState} {R : Mem 64 → Prop} {mu : Mem 64}
    {Q : Post [i64]} {s0 : FullState}
    (hQ : ∀ (r : BitVec 64) s' m',
      s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
      FullLitMarksClear c s' → FullArenaVarsNodup s' → FullExtScratchOk c s' →
      s'.core.cur_level = 0 → s'.core.dense_mode ≠ 0#64 →
      s'.core.cur_vars = s0.core.cur_vars → s'.core.fuel = s0.core.fuel →
      s'.core.arena = s0.core.arena → s'.core.arena_len = s0.core.arena_len →
      FullCongReprInv F_cur (2 * s'.core.cur_vars) s'.core.repr →
      (∀ idx < g_len, s'.scratch.scratch_buf[idx]? = scr0[idx]?) →
      FullCongSpecs.CongHtInv F_cur s'.core.cur_vars scr0 s'.scratch.scratch_buf
        g_len ht_off ht_sz →
      ((r &&& 3#64) = 0#64 ∨ (r &&& 3#64) = 1#64 ∨ (r &&& 3#64) = 2#64) →
      ((r &&& 3#64) = 2#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m')
    (hcv0 : cv0 = s0.core.cur_vars) (hf0 : fuel0 = s0.core.fuel)
    (ha0 : ar0 = s0.core.arena) (hal0 : alen0 = s0.core.arena_len)
    (hoku : WorkStepOk c F0 F_cur fuel0 ar0 alen0 cv0 g_len ht_off ht_sz scr0 su)
    (huns : F0.Unsat) (hmu : (FullMem c su ⋆ R) mu) (wk : BitVec 64) :
    Q ((wk <<< (2 : Nat)) ||| 2#64, ()) mu := by
  have hand3 := bv64_shl2_or_low2_and3 (w := wk) (by decide : (2#64 : BitVec 64).toNat < 4)
  exact hQ ((wk <<< (2 : Nat)) ||| 2#64) su mu hoku.1 hoku.2.1 hoku.2.2.1 hoku.2.2.2.1
    hoku.2.2.2.2.1 hoku.2.2.2.2.2.1 hoku.2.2.2.2.2.2.1
    (hoku.2.2.2.2.2.2.2.1.trans hcv0) (hoku.2.2.2.2.2.2.2.2.1.trans hf0)
    (hoku.2.2.2.2.2.2.2.2.2.1.trans ha0) (hoku.2.2.2.2.2.2.2.2.2.2.1.trans hal0)
    (by rw [hoku.2.2.2.2.2.2.2.1]; exact hoku.2.2.2.2.2.2.2.2.2.2.2.1)
    hoku.2.2.2.2.2.2.2.2.2.2.2.2.1
    (by rw [hoku.2.2.2.2.2.2.2.1]; exact hoku.2.2.2.2.2.2.2.2.2.2.2.2.2)
    (Or.inr (Or.inr hand3)) (fun _ => huns) hmu

theorem ws_exit_q {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {fuel0 : BitVec 64} {ar0 : List (BitVec 32)} {alen0 cv0 g_len ht_off ht_sz : Nat}
    {scr0 : List (BitVec 32)} {ste : FullState} {R : Mem 64 → Prop} {me : Mem 64}
    {Q : Post [i64]} {s0 : FullState}
    (hQ : ∀ (r : BitVec 64) s' m',
      s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
      FullLitMarksClear c s' → FullArenaVarsNodup s' → FullExtScratchOk c s' →
      s'.core.cur_level = 0 → s'.core.dense_mode ≠ 0#64 →
      s'.core.cur_vars = s0.core.cur_vars → s'.core.fuel = s0.core.fuel →
      s'.core.arena = s0.core.arena → s'.core.arena_len = s0.core.arena_len →
      FullCongReprInv F_cur (2 * s'.core.cur_vars) s'.core.repr →
      (∀ idx < g_len, s'.scratch.scratch_buf[idx]? = scr0[idx]?) →
      FullCongSpecs.CongHtInv F_cur s'.core.cur_vars scr0 s'.scratch.scratch_buf
        g_len ht_off ht_sz →
      ((r &&& 3#64) = 0#64 ∨ (r &&& 3#64) = 1#64 ∨ (r &&& 3#64) = 2#64) →
      ((r &&& 3#64) = 2#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m')
    (hcv0 : cv0 = s0.core.cur_vars) (hf0 : fuel0 = s0.core.fuel)
    (ha0 : ar0 = s0.core.arena) (hal0 : alen0 = s0.core.arena_len)
    (hoke : WorkStepOk c F0 F_cur fuel0 ar0 alen0 cv0 g_len ht_off ht_sz scr0 ste)
    (hme : (FullMem c ste ⋆ R) me) (ch_e : Bool) (wk_e : BitVec 64) :
    let st_v : BitVec 64 :=
      if ste.core.inconsistent ≠ 0#64 then 2#64 else if ch_e then 1#64 else 0#64
    Q ((wk_e <<< (2 : Nat)) ||| st_v, ()) me := by
  intro st_v
  have hstv_lt : st_v.toNat < 4 := by
    dsimp only [st_v]
    split
    · decide
    · split <;> decide
  have hand3 := bv64_shl2_or_low2_and3 (w := wk_e) hstv_lt
  refine hQ ((wk_e <<< (2 : Nat)) ||| st_v) ste me hoke.1 hoke.2.1 hoke.2.2.1 hoke.2.2.2.1
    hoke.2.2.2.2.1 hoke.2.2.2.2.2.1 hoke.2.2.2.2.2.2.1
    (hoke.2.2.2.2.2.2.2.1.trans hcv0) (hoke.2.2.2.2.2.2.2.2.1.trans hf0)
    (hoke.2.2.2.2.2.2.2.2.2.1.trans ha0) (hoke.2.2.2.2.2.2.2.2.2.2.1.trans hal0)
    (by rw [hoke.2.2.2.2.2.2.2.1]; exact hoke.2.2.2.2.2.2.2.2.2.2.2.1)
    hoke.2.2.2.2.2.2.2.2.2.2.2.2.1
    (by rw [hoke.2.2.2.2.2.2.2.1]; exact hoke.2.2.2.2.2.2.2.2.2.2.2.2.2)
    ?_ (fun h2 => ?_) hme
  · rw [hand3]; dsimp only [st_v]; split
    · exact Or.inr (Or.inr rfl)
    · split
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl rfl
  · rw [hand3] at h2
    have hinc : ste.core.inconsistent ≠ 0#64 := by
      dsimp only [st_v] at h2; split at h2
      · assumption
      · split at h2 <;> cases h2
    exact unsat_of_inconsistent_w hoke.2.1 hinc

theorem ws_unit_call {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {fuel0 : BitVec 64} {ar0 : List (BitVec 32)} {alen0 cv0 g_len ht_off ht_sz : Nat}
    {scr0 : List (BitVec 32)} {st : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} {lit next_ep : BitVec 32}
    (hok : WorkStepOk c F0 F_cur fuel0 ar0 alen0 cv0 g_len ht_off ht_sz scr0 st)
    (hl : lit.toNat < 2 * cv0) (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [lit.toNat]))
    (hm : (FullMem c st ⋆ R) m)
    (k : ∀ (r : BitVec 64) (s' : FullState) (m' : Mem 64),
      WorkStepOk c F0 F_cur fuel0 ar0 alen0 cv0 g_len ht_off ht_sz scr0 s' →
      s'.core.tmp = st.core.tmp → (r = 2#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m') :
    m3CongUnitFoldSpec (c.hdr, lit, next_ep, ()) m Q X :=
  ⟨c, F0, F_cur, st, R, rfl, hok.1, hok.2.1, hok.2.2.1, hok.2.2.2.1, hok.2.2.2.2.1,
   hok.2.2.2.2.2.1, hok.2.2.2.2.2.2.1, hok.2.2.2.2.2.2.2.1 ▸ hok.2.2.2.2.2.2.2.2.2.2.2.1,
   hok.2.2.2.2.2.2.2.1 ▸ hl, hent, hm,
   fun r s' m' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 htmp h12 h13 _ h2u hm' =>
     k r s' m' (workStepOk_of_fold hok h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13)
       htmp (fun h => (h2u h).2) hm'⟩

theorem ws_unit_xor1 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {fuel0 : BitVec 64} {ar0 : List (BitVec 32)} {alen0 cv0 g_len ht_off ht_sz : Nat}
    {scr0 : List (BitVec 32)} {st : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} {lit next_ep : BitVec 32}
    (hok : WorkStepOk c F0 F_cur fuel0 ar0 alen0 cv0 g_len ht_off ht_sz scr0 st)
    (hl : lit.toNat < 2 * cv0)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [litNeg lit.toNat]))
    (hm : (FullMem c st ⋆ R) m)
    (k : ∀ (r : BitVec 64) (s' : FullState) (m' : Mem 64),
      WorkStepOk c F0 F_cur fuel0 ar0 alen0 cv0 g_len ht_off ht_sz scr0 s' →
      s'.core.tmp = st.core.tmp → (r = 2#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m') :
    m3CongUnitFoldSpec (c.hdr, lit ^^^ 1#32, next_ep, ()) m Q X :=
  ws_unit_call hok (by rw [bv32_xor1_eq_litNeg]; exact bv32_xor1_lt_even hl)
    (by rw [bv32_xor1_eq_litNeg]; exact hent) hm k

theorem ws_equiv_call {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {fuel0 : BitVec 64} {ar0 : List (BitVec 32)} {alen0 cv0 g_len ht_off ht_sz : Nat}
    {scr0 : List (BitVec 32)} {st : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} {a b next_ep : BitVec 32}
    (hok : WorkStepOk c F0 F_cur fuel0 ar0 alen0 cv0 g_len ht_off ht_sz scr0 st)
    (ha : a.toNat < 2 * cv0) (hb : b.toNat < 2 * cv0)
    (heqv : LitEquiv (cnfOfClauses F_cur) a.toNat b.toNat) (hm : (FullMem c st ⋆ R) m)
    (k : ∀ (r : BitVec 64) (s' : FullState) (m' : Mem 64),
      WorkStepOk c F0 F_cur fuel0 ar0 alen0 cv0 g_len ht_off ht_sz scr0 s' →
      s'.core.tmp = st.core.tmp → (r = 2#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m') :
    m3CongEquivFoldSpec (c.hdr, a, b, next_ep, ()) m Q X :=
  ⟨c, F0, F_cur, st, R, rfl, hok.1, hok.2.1, hok.2.2.1, hok.2.2.2.1, hok.2.2.2.2.1,
   hok.2.2.2.2.2.1, hok.2.2.2.2.2.2.1, hok.2.2.2.2.2.2.2.1 ▸ hok.2.2.2.2.2.2.2.2.2.2.2.1,
   hok.2.2.2.2.2.2.2.1 ▸ ha, hok.2.2.2.2.2.2.2.1 ▸ hb, heqv, hm,
   fun r s' m' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 htmp h12 h13 _ h2u hm' =>
     k r s' m' (workStepOk_of_fold hok h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13)
       htmp h2u hm'⟩

theorem ws_find_tmp_step {F_cur : List (List Nat)} {cv0 g maxv : Nat}
    {scr0 tmpi : List (BitVec 32)} {i ri rval : BitVec 32}
    (htmp_i : ∀ k' < i.toNat, (tmpi[k']?.getD 0#32).toNat < 2 * cv0 ∧
      LitEquiv (cnfOfClauses F_cur) (scr0[g + 2 + k']?.getD 0#32).toNat
        (tmpi[k']?.getD 0#32).toNat)
    (htl : tmpi.length = maxv) (hi_lt : i.toNat < maxv)
    (hri_get : scr0[g + 2 + i.toNat]? = some ri)
    (hrval_lt : rval.toNat < 2 * cv0)
    (hrval_eqv : LitEquiv (cnfOfClauses F_cur) ri.toNat rval.toNat)
    (k' : Nat) (hk' : k' < i.toNat + 1) :
    ((tmpi.set i.toNat rval)[k']?.getD 0#32).toNat < 2 * cv0 ∧
    LitEquiv (cnfOfClauses F_cur) (scr0[g + 2 + k']?.getD 0#32).toNat
      ((tmpi.set i.toNat rval)[k']?.getD 0#32).toNat := by
  by_cases hki : k' = i.toNat
  · subst hki
    rw [List.getElem?_set_self (by omega), Option.getD_some, hri_get, Option.getD_some]
    exact ⟨hrval_lt, hrval_eqv⟩
  · rw [List.getElem?_set_ne (Ne.symm hki)]
    exact htmp_i k' (by omega)

theorem ws_probe_insert_ok {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {fuel0 : BitVec 64} {ar0 : List (BitVec 32)} {alen0 cv0 : Nat}
    {g_len ht_off ht_sz g : BitVec 64}
    {scr0 : List (BitVec 32)} {stp : FullState} {slot : BitVec 64}
    (hok : WorkStepOk c F0 F_cur fuel0 ar0 alen0 cv0 g_len.toNat ht_off.toNat ht_sz.toNat scr0 stp)
    (hg_lt : g.toNat < g_len.toNat) (hg_le_ht : g_len.toNat ≤ ht_off.toNat)
    (hht_le : ht_off.toNat + ht_sz.toNat ≤ c.scratch_cap)
    (hslot_lt : slot.toNat < ht_sz.toNat)
    (hgat : FullCongSpecs.GateAt F_cur cv0 scr0 g_len.toNat g.toNat) :
    let scr_ins := stp.scratch.scratch_buf.set (ht_off.toNat + slot.toNat) (g.setWidth 32)
    let stp' : FullState :=
      { stp with scratch := { stp.scratch with
        scratch_buf := scr_ins, res_sz := stp.scratch.res_sz + 1#64 } }
    WorkStepOk c F0 F_cur fuel0 ar0 alen0 cv0 g_len.toNat ht_off.toNat ht_sz.toNat scr0 stp' := by
  intro scr_ins stp'
  have hscrl_p := hok.1.scratch_ok.scratch_buf_len
  have hlen_p' : stp'.LengthsOk c :=
    ⟨hok.1.core_ok,
     { hok.1.scratch_ok with scratch_buf_len := by rw [List.length_set]; exact hscrl_p }⟩
  have hext_p' := fullExtScratchOk_of_eq hok.2.2.2.2.1 rfl rfl rfl rfl
  have hpref_p := hok.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hht_p := hok.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hg_tr : (g.setWidth 32).toNat = g.toNat := by
    have hsc := c.hscr; unfold dimacsBound at hsc
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
  have hpref_p' : ∀ idx < g_len.toNat, scr_ins[idx]? = scr0[idx]? := fun idx hi => by
    rw [List.getElem?_set_ne (by omega)]; exact hpref_p idx hi
  have hht_p' : FullCongSpecs.CongHtInv F_cur cv0 scr0 scr_ins g_len.toNat ht_off.toNat
      ht_sz.toNat := fun k' hk' => by
    by_cases hks : k' = slot.toNat
    · subst hks; right; rw [List.getElem?_set_self (by omega), Option.getD_some, hg_tr]
      exact hgat
    · rw [List.getElem?_set_ne (by omega)]; exact hht_p k' hk'
  exact ⟨hlen_p', hok.2.1, hok.2.2.1, hok.2.2.2.1, hext_p', hok.2.2.2.2.2.1, hok.2.2.2.2.2.2.1,
    hok.2.2.2.2.2.2.2.1, hok.2.2.2.2.2.2.2.2.1, hok.2.2.2.2.2.2.2.2.2.1,
    hok.2.2.2.2.2.2.2.2.2.2.1, hok.2.2.2.2.2.2.2.2.2.2.2.1, hpref_p', hht_p'⟩

theorem ws_match_and_equiv {F_cur : List (List Nat)} {tmps scr0 : List (BitVec 32)}
    {lhs elhs : BitVec 32} {ent ha : Nat}
    (hand_eq : ∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α →
      evalLitVal α lhs.toNat =
        (List.range ha).all (fun k => evalLitVal α (tmps[k]?.getD 0#32).toNat))
    (he0 : scr0[ent]? = some elhs)
    (hm_all : ∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α →
      evalLitVal α (scr0[ent]?.getD 0#32).toNat =
        (List.range ha).all (fun k => evalLitVal α (tmps[k]?.getD 0#32).toNat)) :
    LitEquiv (cnfOfClauses F_cur) lhs.toNat elhs.toNat := by
  refine litEquiv_of_eval_eq fun α hα => ?_
  have hm' := hm_all α hα
  rw [he0, Option.getD_some] at hm'
  rw [hand_eq α hα, hm']

theorem ws_hash_ite_equiv {F_cur : List (List Nat)} {elhs ec' et' ee' lhs : BitVec 32}
    {tmps : List (BitVec 32)} (htmp_ge3 : 3 ≤ tmps.length)
    (hite_s : IteGateDef (cnfOfClauses F_cur) lhs.toNat (tmps[0]?.getD 0#32).toNat
      (tmps[1]?.getD 0#32).toNat (tmps[2]?.getD 0#32).toNat)
    (hite_f : IteGateDef (cnfOfClauses F_cur) elhs.toNat ec'.toNat et'.toNat ee'.toNat)
    (hc0 : ec' = tmps[0]'(by omega)) (hc1 : et' = tmps[1]'(by omega))
    (hc2 : ee' = tmps[2]'(by omega)) :
    LitEquiv (cnfOfClauses F_cur) lhs.toNat elhs.toNat := by
  refine litEquiv_of_eval_eq fun α hα => ?_
  rw [iteGateDef_eval hα hite_s, iteGateDef_eval hα hite_f, hc0, hc1, hc2,
    List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega),
    List.getElem?_eq_getElem (by omega), Option.getD_some, Option.getD_some, Option.getD_some]

theorem ws_hash_xor_equiv {F_cur : List (List Nat)} {elhs e0 e1 lhs : BitVec 32}
    {tmps : List (BitVec 32)} (htmp_ge2 : 2 ≤ tmps.length)
    (hxor_s : XorGateDef (cnfOfClauses F_cur) lhs.toNat
      (tmps[0]?.getD 0#32).toNat (tmps[1]?.getD 0#32).toNat)
    (hxor_e : XorGateDef (cnfOfClauses F_cur) elhs.toNat e0.toNat e1.toNat)
    (hc0 : e0 = tmps[0]'(by omega)) (hc1 : e1 = tmps[1]'(by omega)) :
    LitEquiv (cnfOfClauses F_cur) lhs.toNat elhs.toNat := by
  refine litEquiv_of_eval_eq fun α hα => ?_
  rw [xorGateDef_eval hα hxor_s, xorGateDef_eval hα hxor_e, hc0, hc1,
    List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega),
    Option.getD_some, Option.getD_some]

theorem ws_tag0_and_def {F_cur : List (List Nat)} {lhs0 mword : BitVec 32} {g : Nat}
    {scr0 : List (BitVec 32)} (htag : mword >>> 28 = 0#32)
    (hsem : ((mword >>> 28).toNat = 0 ∧ 2 ≤ (mword &&& 0xFF#32).toNat ∧
        AndGateDef (cnfOfClauses F_cur) lhs0.toNat
          (((scr0.drop (g + 2)).take (mword &&& 0xFF#32).toNat).map BitVec.toNat)) ∨
      ((mword >>> 28).toNat = 1 ∧ (mword &&& 0xFF#32).toNat = 2 ∧
        XorGateDef (cnfOfClauses F_cur) lhs0.toNat
          (scr0[g + 2]?.getD 0#32).toNat (scr0[g + 3]?.getD 0#32).toNat) ∨
      ((mword >>> 28).toNat = 2 ∧ (mword &&& 0xFF#32).toNat = 3 ∧
        IteGateDef (cnfOfClauses F_cur) lhs0.toNat (scr0[g + 2]?.getD 0#32).toNat
          (scr0[g + 3]?.getD 0#32).toNat (scr0[g + 4]?.getD 0#32).toNat)) :
    AndGateDef (cnfOfClauses F_cur) lhs0.toNat
      (((scr0.drop (g + 2)).take (mword &&& 0xFF#32).toNat).map BitVec.toNat) := by
  have h0 : (mword >>> 28).toNat = 0 := by rw [htag]; decide
  rcases hsem with ⟨_, _, h⟩ | ⟨ht, _⟩ | ⟨ht, _⟩
  · exact h
  · omega
  · omega

theorem ws_tag1_xor_def {F_cur : List (List Nat)} {lhs0 mword : BitVec 32} {g : Nat}
    {scr0 : List (BitVec 32)} (htag : mword >>> 28 = 1#32)
    (hsem : ((mword >>> 28).toNat = 0 ∧ 2 ≤ (mword &&& 0xFF#32).toNat ∧
        AndGateDef (cnfOfClauses F_cur) lhs0.toNat
          (((scr0.drop (g + 2)).take (mword &&& 0xFF#32).toNat).map BitVec.toNat)) ∨
      ((mword >>> 28).toNat = 1 ∧ (mword &&& 0xFF#32).toNat = 2 ∧
        XorGateDef (cnfOfClauses F_cur) lhs0.toNat
          (scr0[g + 2]?.getD 0#32).toNat (scr0[g + 3]?.getD 0#32).toNat) ∨
      ((mword >>> 28).toNat = 2 ∧ (mword &&& 0xFF#32).toNat = 3 ∧
        IteGateDef (cnfOfClauses F_cur) lhs0.toNat (scr0[g + 2]?.getD 0#32).toNat
          (scr0[g + 3]?.getD 0#32).toNat (scr0[g + 4]?.getD 0#32).toNat)) :
    XorGateDef (cnfOfClauses F_cur) lhs0.toNat
      (scr0[g + 2]?.getD 0#32).toNat (scr0[g + 3]?.getD 0#32).toNat := by
  have h1 : (mword >>> 28).toNat = 1 := by rw [htag]; decide
  rcases hsem with ⟨ht, _⟩ | ⟨_, _, h⟩ | ⟨ht, _⟩
  · omega
  · exact h
  · omega

theorem ws_tag2_ite_def {F_cur : List (List Nat)} {lhs0 mword : BitVec 32} {g : Nat}
    {scr0 : List (BitVec 32)} (htag : mword >>> 28 = 2#32)
    (hsem : ((mword >>> 28).toNat = 0 ∧ 2 ≤ (mword &&& 0xFF#32).toNat ∧
        AndGateDef (cnfOfClauses F_cur) lhs0.toNat
          (((scr0.drop (g + 2)).take (mword &&& 0xFF#32).toNat).map BitVec.toNat)) ∨
      ((mword >>> 28).toNat = 1 ∧ (mword &&& 0xFF#32).toNat = 2 ∧
        XorGateDef (cnfOfClauses F_cur) lhs0.toNat
          (scr0[g + 2]?.getD 0#32).toNat (scr0[g + 3]?.getD 0#32).toNat) ∨
      ((mword >>> 28).toNat = 2 ∧ (mword &&& 0xFF#32).toNat = 3 ∧
        IteGateDef (cnfOfClauses F_cur) lhs0.toNat (scr0[g + 2]?.getD 0#32).toNat
          (scr0[g + 3]?.getD 0#32).toNat (scr0[g + 4]?.getD 0#32).toNat)) :
    IteGateDef (cnfOfClauses F_cur) lhs0.toNat (scr0[g + 2]?.getD 0#32).toNat
      (scr0[g + 3]?.getD 0#32).toNat (scr0[g + 4]?.getD 0#32).toNat := by
  have h2 : (mword >>> 28).toNat = 2 := by rw [htag]; decide
  rcases hsem with ⟨ht, _⟩ | ⟨ht, _⟩ | ⟨_, _, h⟩
  · omega
  · omega
  · exact h

theorem ws_tag0_raw_of_rhs {F_cur : List (List Nat)} {scr0 tmpi : List (BitVec 32)}
    {g ar_n : Nat} (har_le : ar_n ≤ tmpi.length) (hscr_ge : g + 2 + ar_n ≤ scr0.length)
    (hraw_eqv : ∀ k < ar_n, LitEquiv (cnfOfClauses F_cur) (scr0[g + 2 + k]?.getD 0#32).toNat
      ((tmpi.take ar_n)[k]?.getD 0#32).toNat) :
    (∀ x ∈ (((scr0.drop (g + 2)).take ar_n).map BitVec.toNat),
      ∃ k < ar_n, LitEquiv (cnfOfClauses F_cur) x ((tmpi.take ar_n)[k]?.getD 0#32).toNat) ∧
    (∀ k < ar_n, ∃ x ∈ (((scr0.drop (g + 2)).take ar_n).map BitVec.toNat),
      LitEquiv (cnfOfClauses F_cur) x ((tmpi.take ar_n)[k]?.getD 0#32).toNat) := by
  have hraw_len : (tmpi.take ar_n).length = ar_n := by simp [har_le]
  refine ⟨fun x hx => ?_, fun k hk => ?_⟩
  · rw [List.mem_map] at hx; obtain ⟨b, hb, rfl⟩ := hx
    obtain ⟨k, hk, hget⟩ := List.mem_iff_getElem.mp hb
    rw [List.length_take, List.length_drop] at hk
    have hk' : k < ar_n := by omega
    refine ⟨k, hk', ?_⟩
    rw [List.getElem_take, List.getElem_drop] at hget
    have he := hraw_eqv k hk'
    rwa [List.getElem?_eq_getElem (by omega), Option.getD_some, hget] at he
  · have hlt : k < ((scr0.drop (g + 2)).take ar_n).length := by
      rw [List.length_take, List.length_drop]; omega
    have hmem : scr0[g + 2 + k]'(by omega) ∈ (scr0.drop (g + 2)).take ar_n := by
      simpa [List.getElem_take, List.getElem_drop] using List.getElem_mem hlt
    refine ⟨(scr0[g + 2 + k]'(by omega)).toNat, List.mem_map_of_mem hmem, ?_⟩
    have he := hraw_eqv k hk
    rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at he

theorem ws_tag0_il_push_inv {vals : List (BitVec 8)} {tmpl raw : List (BitVec 32)}
    {il_n na_n ar_n maxv : Nat} (htl : tmpl.length = maxv) (hna : na_n ≤ il_n)
    (hil : il_n < ar_n) (har_le : ar_n ≤ maxv) (hraw_len : raw.length = ar_n)
    (htail : ∀ j, il_n ≤ j → j < ar_n → tmpl[j]? = raw[j]?)
    (hsub : ∀ j < na_n, ∃ k < ar_n, tmpl[j]? = raw[k]?)
    (hnohf : false = false → ∀ k < il_n,
      vals[(raw[k]?.getD 0#32).toNat]?.getD 0#8 = 1#8 ∨ ∃ j < na_n, tmpl[j]? = raw[k]?) :
    let tmpl' := tmpl.set na_n (raw[il_n]'(by omega))
    tmpl'.length = maxv ∧ na_n + 1 ≤ il_n + 1 ∧ il_n + 1 ≤ ar_n ∧
    (∀ j, il_n + 1 ≤ j → j < ar_n → tmpl'[j]? = raw[j]?) ∧
    (∀ j < na_n + 1, ∃ k < ar_n, tmpl'[j]? = raw[k]?) ∧
    (false = false → ∀ k < il_n + 1,
      vals[(raw[k]?.getD 0#32).toNat]?.getD 0#8 = 1#8 ∨ ∃ j < na_n + 1, tmpl'[j]? = raw[k]?) := by
  refine ⟨by rw [List.length_set]; exact htl, by omega, by omega, ?_, ?_, ?_⟩
  · intro j hj1 hj2; rw [List.getElem?_set_ne (by omega)]; exact htail j (by omega) hj2
  · intro j hj; by_cases hjn : j = na_n
    · subst hjn; refine ⟨il_n, hil, ?_⟩
      rw [List.getElem?_set_self (by omega), List.getElem?_eq_getElem (by omega)]
    · rw [List.getElem?_set_ne (Ne.symm hjn)]; exact hsub j (by omega)
  · intro hhf k hk; by_cases hki : k = il_n
    · subst hki; right; refine ⟨na_n, by omega, ?_⟩
      rw [List.getElem?_set_self (by omega), List.getElem?_eq_getElem (by omega)]
    · obtain h1 | ⟨j, hj, hget⟩ := hnohf hhf k (by omega)
      · exact Or.inl h1
      · right; refine ⟨j, by omega, ?_⟩
        rw [List.getElem?_set_ne (by omega)]; exact hget

theorem ws_tag0_il_true_inv {hf : Bool} {vals : List (BitVec 8)} {tmpl raw : List (BitVec 32)}
    {il_n na_n : Nat} (h1 : vals[(raw[il_n]?.getD 0#32).toNat]?.getD 0#8 = 1#8)
    (hnohf : hf = false → ∀ k < il_n,
      vals[(raw[k]?.getD 0#32).toNat]?.getD 0#8 = 1#8 ∨ ∃ j < na_n, tmpl[j]? = raw[k]?) :
    hf = false → ∀ k < il_n + 1,
      vals[(raw[k]?.getD 0#32).toNat]?.getD 0#8 = 1#8 ∨ ∃ j < na_n, tmpl[j]? = raw[k]? := by
  intro hhf k hk; by_cases hki : k = il_n
  · subst hki; exact Or.inl h1
  · exact hnohf hhf k (by omega)

theorem ws_tag0_all_true_entails {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} {lhs0 lhs : BitVec 32} {rhs : List Nat} {raw tmpl : List (BitVec 32)}
    {ar_n : Nat} (hw : FullWitnessInv c F0 F_cur k) (hcl0 : k.cur_level = 0)
    (hand0 : AndGateDef (cnfOfClauses F_cur) lhs0.toNat rhs)
    (hlhs_eqv : LitEquiv (cnfOfClauses F_cur) lhs0.toNat lhs.toNat)
    (hraw_lt : ∀ m < ar_n, (raw[m]?.getD 0#32).toNat < 2 * k.cur_vars)
    (hraw_of_rhs : ∀ x ∈ rhs, ∃ m < ar_n, LitEquiv (cnfOfClauses F_cur) x (raw[m]?.getD 0#32).toNat)
    (hnohf : ∀ m < ar_n,
      k.vals[(raw[m]?.getD 0#32).toNat]?.getD 0#8 = 1#8 ∨ ∃ j < 0, tmpl[j]? = raw[m]?) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause [lhs.toNat]) := by
  refine andFold_all_true_entails hw hcl0 hand0 hlhs_eqv fun x hx => ?_
  obtain ⟨m, hm, heqv⟩ := hraw_of_rhs x hx
  refine ⟨(raw[m]?.getD 0#32).toNat, hraw_lt m hm, heqv, ?_⟩
  rcases hnohf m hm with h1 | ⟨j, hj, _⟩
  · exact h1
  · omega

theorem ws_tag0_hf_false_fwd {vals : List (BitVec 8)} {lhs_cv : Nat} {rhs : List Nat}
    {raw tmpl : List (BitVec 32)} {ar_n na_n : Nat}
    (F_cur : List (List Nat)) (hraw_lt : ∀ k < ar_n, (raw[k]?.getD 0#32).toNat < 2 * lhs_cv)
    (hraw_of_rhs : ∀ x ∈ rhs, ∃ k < ar_n, LitEquiv (cnfOfClauses F_cur) x (raw[k]?.getD 0#32).toNat)
    (hnohf : ∀ k < ar_n,
      vals[(raw[k]?.getD 0#32).toNat]?.getD 0#8 = 1#8 ∨ ∃ j < na_n, tmpl[j]? = raw[k]?) :
    ∀ x ∈ rhs, ∃ r < 2 * lhs_cv, LitEquiv (cnfOfClauses F_cur) x r ∧
      (vals[r]?.getD 0#8 = 1#8 ∨ ∃ j < na_n, (tmpl[j]?.getD 0#32).toNat = r) := by
  intro x hx; obtain ⟨k, hk, heqv⟩ := hraw_of_rhs x hx
  refine ⟨(raw[k]?.getD 0#32).toNat, hraw_lt k hk, heqv, ?_⟩
  rcases hnohf k hk with h1 | ⟨j, hj, hget⟩
  · exact Or.inl h1
  · right; refine ⟨j, hj, ?_⟩; rw [hget]

theorem ws_tag0_post_sort {F_cur : List (List Nat)} {vals : List (BitVec 8)}
    {cv0 ar_n na_n maxv : Nat} {rhs : List Nat} {tmpl tmps raw : List (BitVec 32)}
    (htl_s : tmps.length = maxv) (htl_l : tmpl.length = maxv)
    (hna_le : na_n ≤ ar_n) (har_le : ar_n ≤ maxv)
    (hperm : List.Perm (tmps.take na_n) (tmpl.take na_n))
    (hsub_l : ∀ j < na_n, ∃ k < ar_n, tmpl[j]? = raw[k]?)
    (hfwd_l : ∀ x ∈ rhs, ∃ r < 2 * cv0, LitEquiv (cnfOfClauses F_cur) x r ∧
      (vals[r]?.getD 0#8 = 1#8 ∨ ∃ j < na_n, (tmpl[j]?.getD 0#32).toNat = r)) :
    (∀ j < na_n, ∃ k < ar_n, tmps[j]? = raw[k]?) ∧
    (∀ x ∈ rhs, ∃ r < 2 * cv0, LitEquiv (cnfOfClauses F_cur) x r ∧
      (vals[r]?.getD 0#8 = 1#8 ∨ ∃ j < na_n, (tmps[j]?.getD 0#32).toNat = r)) := by
  have htake_mem : ∀ {x : BitVec 32}, x ∈ tmps.take na_n ↔ x ∈ tmpl.take na_n := fun {x} =>
    hperm.mem_iff
  refine ⟨fun j hj => ?_, fun x hx => ?_⟩
  · have hmem : tmps[j]'(by omega) ∈ tmpl.take na_n :=
      htake_mem.mp (mem_take_of_lt hj (by omega))
    obtain ⟨q, hq, hgetq⟩ := lt_take_of_mem hmem
    simp only [Nat.lt_min] at hq
    obtain ⟨k, hk, hgetk⟩ := hsub_l q hq.1
    refine ⟨k, hk, ?_⟩
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hgetq
    rw [List.getElem?_eq_getElem (by omega), ← hgetq, ← List.getElem?_eq_getElem (by omega)]
    exact hgetk
  · obtain ⟨r, hr_lt, heqv, h1 | ⟨j, hj, rfl⟩⟩ := hfwd_l x hx
    · exact ⟨r, hr_lt, heqv, Or.inl h1⟩
    · have hmem : tmpl[j]'(by omega) ∈ tmps.take na_n :=
        htake_mem.mpr (mem_take_of_lt hj (by omega))
      obtain ⟨q, hq, hgetq⟩ := lt_take_of_mem hmem
      simp only [Nat.lt_min] at hq
      refine ⟨_, hr_lt, heqv, Or.inr ⟨q, hq.1, ?_⟩⟩
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hgetq
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some, hgetq,
        List.getElem?_eq_getElem (by omega), Option.getD_some]

theorem ws_tag0_sub_raw_d {F_cur : List (List Nat)} {tmpd tmps raw : List (BitVec 32)}
    {ua_n na_n ar_n : Nat} {rhs : List Nat}
    (hsub_tmps : ∀ j < ua_n, ∃ k < na_n, tmpd[j]? = tmps[k]?)
    (hsub_s : ∀ j < na_n, ∃ k < ar_n, tmps[j]? = raw[k]?)
    (hrhs_of_raw : ∀ k < ar_n, ∃ x ∈ rhs,
      LitEquiv (cnfOfClauses F_cur) x (raw[k]?.getD 0#32).toNat)
    (_htld : ua_n ≤ tmpd.length) (hraw_len : raw.length = ar_n) :
    (∀ j < ua_n, ∃ k < ar_n, tmpd[j]? = raw[k]?) ∧
    (∀ j < ua_n, ∃ x ∈ rhs, LitEquiv (cnfOfClauses F_cur) x (tmpd[j]?.getD 0#32).toNat) := by
  have hsub_d : ∀ j < ua_n, ∃ k < ar_n, tmpd[j]? = raw[k]? := fun j hj => by
    obtain ⟨k, hk, hget⟩ := hsub_tmps j hj
    obtain ⟨kr, hkr, hgetr⟩ := hsub_s k hk
    exact ⟨kr, hkr, hget.trans hgetr⟩
  refine ⟨hsub_d, fun j hj => ?_⟩
  obtain ⟨k, hk, hget⟩ := hsub_d j hj
  obtain ⟨x, hx, heqv⟩ := hrhs_of_raw k hk; refine ⟨x, hx, ?_⟩
  rw [hget, List.getElem?_eq_getElem (by omega), Option.getD_some]
  rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at heqv

theorem ws_tag0_clash_entails {F_cur : List (List Nat)} {lhs0 lhs : BitVec 32}
    {rhs : List Nat} {tmps raw : List (BitVec 32)} {na_n ar_n : Nat}
    (hand0 : AndGateDef (cnfOfClauses F_cur) lhs0.toNat rhs)
    (hlhs_eqv : LitEquiv (cnfOfClauses F_cur) lhs0.toNat lhs.toNat)
    (hsub_s : ∀ j < na_n, ∃ k < ar_n, tmps[j]? = raw[k]?)
    (hrhs_of_raw : ∀ k < ar_n, ∃ x ∈ rhs,
      LitEquiv (cnfOfClauses F_cur) x (raw[k]?.getD 0#32).toNat)
    (hraw_len : raw.length = ar_n) (hna_s : na_n ≤ tmps.length)
    (hclash : ∃ z ∈ (tmps.take na_n).map BitVec.toNat,
      litNeg z ∈ (tmps.take na_n).map BitVec.toNat) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause [litNeg lhs.toNat]) := by
  obtain ⟨z, hz1, hz2⟩ := hclash
  refine andFold_clash_entails hand0 hlhs_eqv (fun l hl => ?_) hz1 hz2
  rw [List.mem_map] at hl; obtain ⟨b, hb, rfl⟩ := hl
  obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp hb
  rw [List.length_take] at hj; rw [List.getElem_take] at hget
  obtain ⟨k, hk, hraw_j⟩ := hsub_s j (by omega)
  obtain ⟨x, hx, heqv⟩ := hrhs_of_raw k hk; refine ⟨x, hx, ?_⟩
  rw [← hget]
  rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at hraw_j
  have hraw_j' := Option.some.inj hraw_j
  rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at heqv
  rw [hraw_j']; exact heqv

theorem ws_tag0_dedup_eval {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} {lhs0 lhs : BitVec 32} {rhs : List Nat} {tmps tmpd : List (BitVec 32)}
    {ua_n na_n cv0 : Nat} (hw : FullWitnessInv c F0 F_cur k) (hcl0 : k.cur_level = 0)
    (hcv : k.cur_vars = cv0) (htld : ua_n ≤ tmpd.length)
    (hand0 : AndGateDef (cnfOfClauses F_cur) lhs0.toNat rhs)
    (hlhs_eqv : LitEquiv (cnfOfClauses F_cur) lhs0.toNat lhs.toNat)
    (hfwd_s : ∀ x ∈ rhs, ∃ r < 2 * cv0, LitEquiv (cnfOfClauses F_cur) x r ∧
      (k.vals[r]?.getD 0#8 = 1#8 ∨ ∃ j < na_n, (tmps[j]?.getD 0#32).toNat = r))
    (hcov_d : ∀ j < na_n, ∃ q < ua_n, (tmpd[q]?.getD 0#32) = tmps[j]?.getD 0#32)
    (hsub_raw_d : ∀ j < ua_n, ∃ x ∈ rhs,
      LitEquiv (cnfOfClauses F_cur) x (tmpd[j]?.getD 0#32).toNat) :
    ∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α →
      evalLitVal α lhs.toNat =
        (List.range ua_n).all (fun i => evalLitVal α (tmpd[i]?.getD 0#32).toNat) := by
  let unass_n := (tmpd.take ua_n).map BitVec.toNat
  have hfwd_n : ∀ x ∈ rhs, ∃ r < 2 * k.cur_vars, LitEquiv (cnfOfClauses F_cur) x r ∧
      (k.vals[r]?.getD 0#8 = 1#8 ∨ r ∈ unass_n) := by
    intro x hx; obtain ⟨r, hr_lt, heqv, h1 | ⟨j, hj, rfl⟩⟩ := hfwd_s x hx
    · exact ⟨r, hcv ▸ hr_lt, heqv, Or.inl h1⟩
    · obtain ⟨q, hq, hq_eq⟩ := hcov_d j hj
      refine ⟨_, hcv ▸ hr_lt, heqv, Or.inr (List.mem_map.mpr ⟨tmpd[q]?.getD 0#32, ?_, ?_⟩)⟩
      · rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
        exact mem_take_of_lt hq htld
      · exact congrArg BitVec.toNat hq_eq
  have hbwd_n : ∀ l ∈ unass_n, ∃ x ∈ rhs, LitEquiv (cnfOfClauses F_cur) x l := by
    intro l hl; rw [List.mem_map] at hl; obtain ⟨b, hb, rfl⟩ := hl
    obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp hb
    rw [List.length_take] at hj; rw [List.getElem_take] at hget
    obtain ⟨x, hx, heqv⟩ := hsub_raw_d j (by omega)
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some, hget] at heqv
    exact ⟨x, hx, heqv⟩
  intro α hα
  have h1 := andFold_eval_iff hw hcl0 hand0 hlhs_eqv hfwd_n hbwd_n α hα
  rw [h1, List.all_map]
  have htake_eq : tmpd.take ua_n = (List.range ua_n).map (fun i => tmpd[i]?.getD 0#32) := by
    apply List.ext_getElem
    · simp [List.length_take, List.length_map, List.length_range, Nat.min_eq_left htld]
    · intro i hi1 _
      have hi_d : i < tmpd.length := by rw [List.length_take] at hi1; omega
      simp [List.getElem_take, List.getElem_map, List.getElem_range, List.getElem?_eq_getElem hi_d]
  rw [htake_eq, List.all_map]; rfl

theorem ws_tag0_ua1_equiv {F_cur : List (List Nat)} {tmpd raw : List (BitVec 32)}
    {cv0 ar_n : Nat} {lhs : BitVec 32} (h0d : 0 < tmpd.length) (hraw_len : raw.length = ar_n)
    (hsub_d0 : ∃ k < ar_n, tmpd[0]? = raw[k]?)
    (hraw_lt : ∀ k < ar_n, (raw[k]?.getD 0#32).toNat < 2 * cv0)
    (hev1 : ∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α →
      evalLitVal α lhs.toNat =
        (List.range 1).all (fun k => evalLitVal α (tmpd[k]?.getD 0#32).toNat)) :
    (tmpd[0]'h0d).toNat < 2 * cv0 ∧
    LitEquiv (cnfOfClauses F_cur) lhs.toNat (tmpd[0]'h0d).toNat := by
  refine ⟨?_, litEquiv_of_eval_eq fun α hα => ?_⟩
  · obtain ⟨k, hk, hget⟩ := hsub_d0
    rw [List.getElem?_eq_getElem h0d, List.getElem?_eq_getElem (by omega)] at hget
    have hhl := hraw_lt k hk
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hhl
    rw [Option.some.inj hget]; exact hhl
  · have he := hev1 α hα
    rw [List.range_one, List.all_cons, List.all_nil, Bool.and_true,
      List.getElem?_eq_getElem h0d, Option.getD_some] at he
    exact he

theorem ws_tag0_lhs_true_ents {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} {lhs : BitVec 32} {tmpd : List (BitVec 32)} {ua_n : Nat}
    (hw : FullWitnessInv c F0 F_cur k) (hcl0 : k.cur_level = 0)
    (hlhs_lt : lhs.toNat < 2 * k.cur_vars) (hv1 : k.vals[lhs.toNat]?.getD 0#8 = 1#8)
    (hev : ∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α →
      evalLitVal α lhs.toNat =
        (List.range ua_n).all (fun i => evalLitVal α (tmpd[i]?.getD 0#32).toNat)) :
    ∀ j < ua_n, (cnfOfClauses F_cur).EntailsClause (cnfClause [(tmpd[j]?.getD 0#32).toNat]) := by
  have hall := andFold_lhs_true_entails hw hcl0 hlhs_lt hv1
    (us := (List.range ua_n).map fun i => (tmpd[i]?.getD 0#32).toNat)
    fun α hα => by rw [hev α hα, List.all_map]; rfl
  intro j hj
  exact hall (tmpd[j]?.getD 0#32).toNat (List.mem_map_of_mem (List.mem_range.mpr hj))

theorem ws_tag0_unit_k_args {F_cur : List (List Nat)} {stk_tmp tmpd raw : List (BitVec 32)}
    {k : BitVec 32} {cv0 ua_n ar_n : Nat} (htmp_k : stk_tmp = tmpd)
    (hk_lt : k.toNat < ua_n) (hraw_len : raw.length = ar_n) (htld : ua_n ≤ tmpd.length)
    (hsub_d : ∀ j < ua_n, ∃ q < ar_n, tmpd[j]? = raw[q]?)
    (hraw_lt : ∀ q < ar_n, (raw[q]?.getD 0#32).toNat < 2 * cv0)
    (hents : ∀ j < ua_n, (cnfOfClauses F_cur).EntailsClause
      (cnfClause [(tmpd[j]?.getD 0#32).toNat]))
    (hk_stk : (k.setWidth 64).toNat < stk_tmp.length) :
    (stk_tmp[(k.setWidth 64).toNat]'hk_stk).toNat < 2 * cv0 ∧
    (cnfOfClauses F_cur).EntailsClause
      (cnfClause [(stk_tmp[(k.setWidth 64).toNat]'hk_stk).toNat]) := by
  have hk_d : k.toNat < tmpd.length := by omega
  have htk_eq : stk_tmp[(k.setWidth 64).toNat]'hk_stk = tmpd[k.toNat]'hk_d :=
    list_getElem_zext32_eq htmp_k hk_stk hk_d
  rw [htk_eq]; refine ⟨?_, ?_⟩
  · obtain ⟨k0, hk0, hget0⟩ := hsub_d k.toNat hk_lt
    rw [List.getElem?_eq_getElem hk_d, List.getElem?_eq_getElem (by omega)] at hget0
    have hl := hraw_lt k0 hk0
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hl
    rw [Option.some.inj hget0]; exact hl
  · have h := hents k.toNat hk_lt
    rwa [List.getElem?_eq_getElem hk_d, Option.getD_some] at h

theorem ws_tag0_dedup_first_inv {tmpd tmps : List (BitVec 32)} {si_n na_n maxv : Nat}
    (hsi0 : si_n = 0)
    (htl : tmpd.length = maxv) (hsi_lt : si_n < na_n) (hna_le : na_n ≤ maxv)
    (htail : ∀ j, si_n ≤ j → j < na_n → tmpd[j]? = tmps[j]?) (htmps_len : na_n ≤ tmps.length) :
    let tmpd' := tmpd.set 0 (tmps[si_n]'(by omega))
    tmpd'.length = maxv ∧ 1 ≤ si_n + 1 ∧ si_n + 1 ≤ na_n ∧ (0 < si_n + 1 → 0 < 1) ∧
    (∀ j, si_n + 1 ≤ j → j < na_n → tmpd'[j]? = tmps[j]?) ∧
    (∀ j < 1, ∃ k < na_n, tmpd'[j]? = tmps[k]?) ∧
    (∀ j < si_n + 1, ∃ q < 1, (tmpd'[q]?.getD 0#32) = tmps[j]?.getD 0#32) := by
  subst hsi0
  refine ⟨by rw [List.length_set]; exact htl, by decide, hsi_lt, fun _ => by decide, ?_, ?_, ?_⟩
  · intro j hj1 hj2; rw [List.getElem?_set_ne (by omega)]; exact htail j (by omega) hj2
  · intro j hj; have hj0 : j = 0 := by omega
    subst hj0; refine ⟨0, hsi_lt, ?_⟩
    rw [List.getElem?_set_self (by omega), List.getElem?_eq_getElem (by omega)]
  · intro j hj; have hj0 : j = 0 := by omega
    subst hj0; refine ⟨0, by decide, ?_⟩
    rw [List.getElem?_set_self (by omega), Option.getD_some,
      List.getElem?_eq_getElem (by omega), Option.getD_some]

theorem ws_tag0_dedup_dup_inv' {tmpd tmps : List (BitVec 32)} {ua_n si_n na_n : Nat}
    (htl : tmpd.length ≥ na_n) (htmps_len : na_n ≤ tmps.length)
    (hua_pos : 0 < ua_n) (hua_le : ua_n ≤ si_n) (hsi_lt : si_n < na_n)
    (hcur_prev : tmps[si_n]'(by omega) = tmpd[ua_n - 1]'(by omega))
    (htail : ∀ j, si_n ≤ j → j < na_n → tmpd[j]? = tmps[j]?)
    (hcov : ∀ j < si_n, ∃ q < ua_n, (tmpd[q]?.getD 0#32) = tmps[j]?.getD 0#32) :
    ua_n ≤ si_n + 1 ∧ si_n + 1 ≤ na_n ∧ (0 < si_n + 1 → 0 < ua_n) ∧
    (∀ j, si_n + 1 ≤ j → j < na_n → tmpd[j]? = tmps[j]?) ∧
    (∀ j < si_n + 1, ∃ q < ua_n, (tmpd[q]?.getD 0#32) = tmps[j]?.getD 0#32) := by
  refine ⟨by omega, by omega, fun _ => hua_pos, fun j hj1 hj2 => htail j (by omega) hj2, ?_⟩
  intro j hj; by_cases hjs : j = si_n
  · subst hjs; refine ⟨ua_n - 1, by omega, ?_⟩
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some, ← hcur_prev,
      List.getElem?_eq_getElem (by omega), Option.getD_some]
  · exact hcov j (by omega)

theorem ws_tag0_dedup_clash {tmpd tmps : List (BitVec 32)} {ua_n si_n na_n : Nat}
    {prev : BitVec 32} (htl : ua_n ≤ tmpd.length) (htmps_len : na_n ≤ tmps.length)
    (hua_pos : 0 < ua_n) (_hua_le : ua_n ≤ si_n) (hsi_lt : si_n < na_n)
    (hprev_eq : prev = tmpd[ua_n - 1]'(by omega))
    (hsub_tmps : ∀ j < ua_n, ∃ k < na_n, tmpd[j]? = tmps[k]?)
    (hcur_xor : tmps[si_n]'(by omega) = prev ^^^ 1#32) :
    ∃ z ∈ (tmps.take na_n).map BitVec.toNat,
      litNeg z ∈ (tmps.take na_n).map BitVec.toNat := by
  obtain ⟨kp, hkp, hgetp⟩ := hsub_tmps (ua_n - 1) (by omega)
  rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at hgetp
  have hp_tmps : prev = tmps[kp]'(by omega) := hprev_eq.trans (Option.some.inj hgetp)
  have hcur_mem : (tmps[si_n]'(by omega)).toNat ∈ (tmps.take na_n).map BitVec.toNat :=
    List.mem_map_of_mem (mem_take_of_lt hsi_lt htmps_len)
  have hprev_mem : prev.toNat ∈ (tmps.take na_n).map BitVec.toNat := by
    rw [hp_tmps]; exact List.mem_map_of_mem (mem_take_of_lt hkp htmps_len)
  refine ⟨prev.toNat, hprev_mem, ?_⟩
  rw [← bv32_xor1_eq_litNeg, ← hcur_xor]; exact hcur_mem

theorem ws_tag0_dedup_push_inv {tmpd tmps : List (BitVec 32)} {ua_n si_n na_n maxv : Nat}
    (htl : tmpd.length = maxv) (hna_le : na_n ≤ maxv) (htmps_len : na_n ≤ tmps.length)
    (hua_le : ua_n ≤ si_n) (hsi_lt : si_n < na_n)
    (htail : ∀ j, si_n ≤ j → j < na_n → tmpd[j]? = tmps[j]?)
    (hsub_tmps : ∀ j < ua_n, ∃ k < na_n, tmpd[j]? = tmps[k]?)
    (hcov : ∀ j < si_n, ∃ q < ua_n, (tmpd[q]?.getD 0#32) = tmps[j]?.getD 0#32) :
    let tmpd' := tmpd.set ua_n (tmps[si_n]'(by omega))
    tmpd'.length = maxv ∧ ua_n + 1 ≤ si_n + 1 ∧ si_n + 1 ≤ na_n ∧ (0 < si_n + 1 → 0 < ua_n + 1) ∧
    (∀ j, si_n + 1 ≤ j → j < na_n → tmpd'[j]? = tmps[j]?) ∧
    (∀ j < ua_n + 1, ∃ k < na_n, tmpd'[j]? = tmps[k]?) ∧
    (∀ j < si_n + 1, ∃ q < ua_n + 1, (tmpd'[q]?.getD 0#32) = tmps[j]?.getD 0#32) := by
  refine ⟨by rw [List.length_set]; exact htl, by omega, by omega, fun _ => by omega, ?_, ?_, ?_⟩
  · intro j hj1 hj2; rw [List.getElem?_set_ne (by omega)]; exact htail j (by omega) hj2
  · intro j hj; by_cases hju : j = ua_n
    · subst hju; refine ⟨si_n, hsi_lt, ?_⟩
      rw [List.getElem?_set_self (by omega), List.getElem?_eq_getElem (by omega)]
    · rw [List.getElem?_set_ne (Ne.symm hju)]; exact hsub_tmps j (by omega)
  · intro j hj; by_cases hjs : j = si_n
    · subst hjs; refine ⟨ua_n, by omega, ?_⟩
      rw [List.getElem?_set_self (by omega), Option.getD_some,
        List.getElem?_eq_getElem (by omega), Option.getD_some]
    · obtain ⟨q, hq, hcovq⟩ := hcov j (by omega)
      refine ⟨q, by omega, ?_⟩; rw [List.getElem?_set_ne (by omega)]; exact hcovq

theorem ws_tag1_same_var_unit_args {F_cur : List (List Nat)} {lhs t0 t1 : BitVec 32} {cv0 : Nat}
    {lhs0 : BitVec 32} {g : Nat} {scr0 : List (BitVec 32)}
    (hxor0 : XorGateDef (cnfOfClauses F_cur) lhs0.toNat
      (scr0[g + 2]?.getD 0#32).toNat (scr0[g + 3]?.getD 0#32).toNat)
    (hlhs_eqv : LitEquiv (cnfOfClauses F_cur) lhs0.toNat lhs.toNat)
    (ht0_eqv : LitEquiv (cnfOfClauses F_cur) (scr0[g + 2]?.getD 0#32).toNat t0.toNat)
    (ht1_eqv : LitEquiv (cnfOfClauses F_cur) (scr0[g + 3]?.getD 0#32).toNat t1.toNat)
    (hlhs_lt : lhs.toNat < 2 * cv0) (hdiv : t0.toNat / 2 = t1.toNat / 2) :
    let ul := if t0 = t1 then lhs ^^^ 1#32 else lhs
    ul.toNat < 2 * cv0 ∧ (cnfOfClauses F_cur).EntailsClause (cnfClause [ul.toNat]) := by
  have hunit := xor_same_var_unit hxor0 hlhs_eqv (List.Perm.refl _) ht0_eqv ht1_eqv hdiv
  split
  · next heq =>
    refine ⟨by rw [bv32_xor1_eq_litNeg]; exact bv32_xor1_lt_even hlhs_lt, ?_⟩
    simpa [heq] using hunit
  · next hne => refine ⟨hlhs_lt, ?_⟩; simpa [hne] using hunit

end WorkStepSupport

/-! ## 3. Fast Head-Step & Join Tactics -/

namespace M3HeadTactics
open Lean Meta Elab Tactic

/-- Peel nested `Blocks.get` applications down to the underlying `Expr` node. -/
public meta partial def m3PeelBlocks (e : Lean.Expr) : Lean.Expr :=
  let e := e.consumeMData.headBeta
  if e.isAppOfArity ``LeanQbe.T.Blocks.get 8 then
    let bs := (e.getArg! 5).consumeMData.headBeta
    let idx := (e.getArg! 6).consumeMData.headBeta
    if bs.isAppOfArity ``LeanQbe.T.Blocks.cons 7 then
      if idx.isAppOf ``LeanQbe.T.Member.here then
        m3PeelBlocks (Lean.mkApp (bs.getArg! 5) (e.getArg! 7))
      else if idx.isAppOfArity ``LeanQbe.T.Member.there 4 then
        m3PeelBlocks <| Lean.mkAppN e.getAppFn
          #[e.getArg! 0, e.getArg! 1, e.getArg! 2, e.getArg! 3,
            bs.getArg! 4, bs.getArg! 6, idx.getArg! 3, e.getArg! 7]
      else e
    else e
  else e

/-- Check whether `ty` is a `wp`, `Func.wp`, or `(_ ≤ _) ∧ ...` loop-variant goal. -/
public meta def m3IsWpOrLe (ty : Lean.Expr) : Bool :=
  let ty := ty.consumeMData.headBeta
  ty.isAppOfArity ``LeanQbe.T.wp 6 ||
  ty.isAppOf ``LeanQbe.T.Func.wp ||
  (ty.isAppOfArity ``And 2 &&
    ((ty.getArg! 0).consumeMData.headBeta.isAppOfArity ``LE.le 4))

/-- Fast check whether `e` already exposes a recognized `LeanQbe.T.Expr` head constructor. -/
public meta def m3IsExprHead (e : Lean.Expr) : Bool :=
  match e.getAppFn.consumeMData.constName? with
  | some ``LeanQbe.T.Expr.let_ | some ``LeanQbe.T.Expr.load | some ``LeanQbe.T.Expr.store
  | some ``LeanQbe.T.Expr.jnz | some ``LeanQbe.T.Expr.jump | some ``LeanQbe.T.Expr.ret
  | some ``LeanQbe.T.Expr.exit | some ``LeanQbe.T.Expr.group | some ``LeanQbe.T.Expr.call
  | some ``LeanQbe.T.Expr.hlt => true
  | _ => false

/-- Normalize a stopped `wp` goal head once without full `whnf` on `FullState` projections. -/
public meta def m3NormWpHead : TacticM Unit := do
  let g ← getMainGoal
  let g' ← g.withContext do
    let ty0 ← instantiateMVars (← g.getType)
    let ty := ty0.consumeMData.headBeta
    if ty.isAppOfArity ``LeanQbe.T.wp 6 then
      let e0 := m3PeelBlocks (ty.getArg! 4)
      let e' ← if m3IsExprHead e0 then pure e0 else m3PeelBlocks <$> whnfCore e0
      if e' != ty.getArg! 4 || ty != ty0 then
        let args := ty.getAppArgs.set! 4 e'
        return ← g.change (Lean.mkAppN ty.getAppFn args) (checkDefEq := false)
    else if ty != ty0 then
      return ← g.change ty (checkDefEq := false)
    return g
  setGoals [g']

/-- Run `headStepOnceRes` until stuck or non-`wp`/non-variant (`J*` join-hyp) goal. -/
public meta partial def m3HeadLoop (cfg : HeadStepConfig) (fuel : Nat := 10000) :
    TacticM Unit := do
  if fuel = 0 then return
  let mut out : Array MVarId := #[]
  for g in ← getUnsolvedGoals do
    if ← g.isAssigned then continue
    setGoals [g]
    let ty ← instantiateMVars (← g.getType)
    if m3IsWpOrLe ty then
      match ← headStepOnceRes cfg with
      | .progressed =>
        m3HeadLoop cfg (fuel - 1)
        out := out ++ (← getUnsolvedGoals)
      | .stuck =>
        m3NormWpHead
        out := out ++ (← getUnsolvedGoals)
      | .memFailed msg =>
        if cfg.strictMem then throwError msg
        m3NormWpHead
        out := out ++ (← getUnsolvedGoals)
    else
      out := out.push g
  setGoals out.toList

/-- Step only `let_`/`jump`/`ret`/`exit` and `Func.wp`/variant goals (`O(1)` without chasing
`J*` continuation hyps). -/
public meta partial def m3LetLoop (fuel : Nat := 200) : TacticM Unit := do
  if fuel = 0 then return
  let g ← getMainGoal
  let ty0 ← instantiateMVars (← g.getType)
  let ty := ty0.consumeMData.headBeta
  if ty.isAppOf ``LeanQbe.T.Func.wp ||
     (ty.isAppOfArity ``And 2 &&
       ((ty.getArg! 0).consumeMData.headBeta.isAppOfArity ``LE.le 4)) then
    match ← headStepOnceRes { unrollGroup := false, splitJnz := false, strictMem := false } with
    | .progressed => m3LetLoop (fuel - 1)
    | _ => pure ()
  else if ty.isAppOfArity ``LeanQbe.T.wp 6 then
    let e0 := m3PeelBlocks (ty.getArg! 4)
    let e ← if m3IsExprHead e0 then pure e0 else m3PeelBlocks <$> whnfCore e0
    if e.isAppOf ``LeanQbe.T.Expr.let_ || e.isAppOf ``LeanQbe.T.Expr.jump ||
       e.isAppOf ``LeanQbe.T.Expr.ret || e.isAppOf ``LeanQbe.T.Expr.exit then
      match ← headStepOnceRes { unrollGroup := false, splitJnz := false, strictMem := false } with
      | .progressed => m3LetLoop (fuel - 1)
      | _ => pure ()

scoped elab "m3_steps" : tactic => m3HeadLoop { strictMem := true } 10000

scoped elab "m3_to_group" : tactic =>
  m3HeadLoop { unrollGroup := false, strictMem := false } 10000

scoped elab "m3_let" : tactic => do focus do m3LetLoop 200; m3NormWpHead

scoped elab "m3_split_fast" : tactic => do
  focus do
    m3HeadLoop { unrollGroup := false, splitJnz := false, strictMem := false } 2000
    let g ← getMainGoal
    let ty ← instantiateMVars (← g.getType)
    if ty.isAppOfArity ``LeanQbe.T.wp 6 then
      let e := (ty.getArg! 4).consumeMData
      if e.isAppOfArity ``LeanQbe.T.Expr.jnz 6 then
        let c0 := (e.getArg! 3).consumeMData
        if c0.isAppOf ``LeanQbe.T.Arg.var && c0.getAppNumArgs ≥ 2 then
          let inner0 := c0.appArg!
          let inner := m3PeelBlocks inner0
          if inner != inner0 then
            let cArg := Lean.mkAppN c0.getAppFn
              (c0.getAppArgs.set! (c0.getAppNumArgs - 1) inner)
            let e' := Lean.mkAppN e.getAppFn (e.getAppArgs.set! 3 cArg)
            let g' ← g.change (Lean.mkAppN ty.getAppFn (ty.getAppArgs.set! 4 e'))
              (checkDefEq := false)
            setGoals [g']
        else
          let cArg ← whnf c0
          let e' := Lean.mkAppN e.getAppFn (e.getAppArgs.set! 3 cArg)
          let g' ← g.change (Lean.mkAppN ty.getAppFn (ty.getAppArgs.set! 4 e'))
            (checkDefEq := false)
          setGoals [g']
    let hcId := Lean.mkIdent `hc
    let tac1 ← `(tactic| refine Full.FullCongTactics.wp_jnz_var (fun $hcId => ?_)
      (fun $hcId => ?_))
    let tac2 ← `(tactic| refine head_wp_jnz (vc := _) rfl (fun $hcId => ?_)
      (fun $hcId => ?_))
    evalTactic tac1 <|> evalTactic tac2

/-- Fast call discharge skipping full `c0_let_simp` (reduces only `vals`/`Arg.val` args). -/
scoped macro "m3_call " h:ident : tactic =>
  `(tactic| (
    refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_)
    try simp only [LeanQbe.T.vals_nil, LeanQbe.T.vals_cons,
      LeanQbe.T.Arg.val_var, LeanQbe.T.Arg.val_imm]))

/-- Uniform continuation handler after every `full_cong_unit_fold` or `full_cong_equiv_fold`
call: early-return `2#64` if `r == 2#64`, else update `changed` and jump cleanly. -/
scoped elab "m3_after_fold " hq:ident hres:ident ch0:ident wk:ident hc_ok:ident
    mm:ident hmem:ident chVar:ident " => " k:tacticSeq : tactic => do
  let hcId := Lean.mkIdent `hc
  Lean.Elab.Tactic.evalTactic <| ← `(tactic| (
    m3_split_fast
    · m3_let; exact ws_ret2_q $hq rfl rfl rfl rfl $hc_ok ($hres (beq_iff_eq.mp $hcId))
        $hmem ($wk + 4#64)
    · m3_to_group; refine wp_join_group (ts := [.bool]) (fun _ m_af => m_af = $mm)
        (fun _ ⟨$chVar, ⟨⟩⟩ m_af hm_af => by rw [hm_af]; m3_let; ($k:tacticSeq)) ?_
      intro Jef hJef; m3_split_fast
      · m3_let; exact hJef (true, ()) $mm rfl
      · m3_let; exact hJef ($ch0, ()) $mm rfl))

end M3HeadTactics

end LeanQbe.T.Examples.Kissat.FullM3CongBva
