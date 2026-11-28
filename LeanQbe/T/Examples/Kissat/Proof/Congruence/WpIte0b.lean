/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Congruence.Inv
public import LeanQbe.T.Examples.Kissat.Src.Congruence

/-!
# Congruence ITE M7 WP Proofs — Part 0b (`copy_condbin`)

Canonical `Func.wp` proofs for `Src.Congruence`:
4. `full_cong_copy_condbin_m7_wp` (`Spec.fullCongCopyCondbinM7Spec`)
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Congruence

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Congruence
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Congruence.Spec
open Kraken.Bedrock2.Test

open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Proof.Congruence.CongTactics

local macro "cong_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

public section

/-! ## 4. `full_cong_copy_condbin_m7_wp` -/

private theorem packU64_hi (x y : BitVec 32) :
    ((x.setWidth 64 <<< 32#64 ||| y.setWidth 64) >>> (32 : Nat)).toNat = x.toNat := by
  have heq : (x.setWidth 64 <<< 32#64 ||| y.setWidth 64) >>> (32 : Nat) = x.setWidth 64 := by
    rw [BitVec.shiftLeft_eq']
    simp only [show (32#64).toNat = 32 by rfl]
    ext i hi
    rw [BitVec.getElem_ushiftRight]
    simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
      BitVec.getElem_setWidth]
    have hx := x.isLt
    by_cases hlt : 32 + i < 64
    · have hi32 : i < 32 := by omega
      simp [hlt, show ¬(32 + i < 32) from by omega, hi32, hi]
    · have hx0 : x.getLsbD i = false := by
        simp only [BitVec.getLsbD]
        exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx
          (Nat.pow_le_pow_right (by decide) (by omega)))
      simp [hlt, hx0]
  rw [heq, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := x.isLt; omega)]

private theorem packU64_lo (x y : BitVec 32) :
    ((x.setWidth 64 <<< 32#64 ||| y.setWidth 64) &&& 4294967295#64).toNat = y.toNat := by
  have heq : (x.setWidth 64 <<< 32#64 ||| y.setWidth 64) &&& 4294967295#64 = y.setWidth 64 := by
    rw [BitVec.shiftLeft_eq']
    simp only [show (32#64).toNat = 32 by rfl]
    ext i hi
    rw [BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_shiftLeft, BitVec.getElem_setWidth]
    have hy := y.isLt
    by_cases h32 : i < 32
    · have hm : (4294967295#64)[i] = true := by
        have ht : (4294967295 : Nat).testBit i = true := by
          rw [show (4294967295 : Nat) = 2 ^ 32 - 1 by decide, Nat.testBit_two_pow_sub_one 32 i]
          exact decide_eq_true h32
        simpa [BitVec.getElem_eq_testBit_toNat] using ht
      simp [h32, hm]
    · have hm : (4294967295#64)[i] = false := by
        have ht : (4294967295 : Nat).testBit i = false :=
          Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (by decide : 4294967295 < 2 ^ 32)
            (Nat.pow_le_pow_right (by decide) (by omega)))
        simpa [BitVec.getElem_eq_testBit_toNat] using ht
      have hy0 : y.getLsbD i = false := by
        simp only [BitVec.getLsbD]
        exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hy
          (Nat.pow_le_pow_right (by decide) (by omega)))
      simp [h32, hm, hy0]
  rw [heq, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := y.isLt; omega)]

private theorem condBin_of_pack {F_cur : List (List Nat)} {cv lit : Nat}
    {x y : BitVec 32} (hx : x.toNat < 2 * cv) (hy : y.toNat < 2 * cv)
    (hd1 : x.toNat / 2 ≠ y.toNat / 2)
    (hd2 : x.toNat / 2 ≠ lit / 2)
    (hd3 : y.toNat / 2 ≠ lit / 2)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [lit, x.toNat, y.toNat])) :
    CondBinElemOk F_cur cv lit (x.setWidth 64 <<< 32#64 ||| y.setWidth 64) := by
  dsimp only [CondBinElemOk]
  rw [packU64_hi, packU64_lo]
  exact ⟨hx, hy, hd1, hd2, hd3, hent⟩

private theorem condBin_perm3 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {lit : Nat} {s : FullState} {cr : Nat} {u0 u1 : BitVec 32}
    (hw : FullWitnessInv c F0 F_cur s.core) (hlvl0 : s.core.cur_level = 0)
    (hcr : cr ∈ fullArenaClauseRefs s) (hgarb : fullArenaClauseGarb s cr = false)
    (hmem : ∀ l ∈ fullArenaClauseLits s cr,
      s.core.vals[l]?.getD 0#8 = 255#8 ∨ l = lit ∨ l = u0.toNat ∨ l = u1.toNat) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause [lit, u0.toNat, u1.toNat]) :=
  unassigned_clause_entails hw hlvl0 hcr hgarb fun l hl => by
    rcases hmem l hl with hff | rfl | rfl | rfl
    · exact Or.inl hff
    · exact Or.inr List.mem_cons_self
    · exact Or.inr (List.mem_cons_of_mem _ List.mem_cons_self)
    · exact Or.inr (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))

private theorem copy_condbin_dedup_step {F_cur : List (List Nat)} {cv lit : Nat}
    {xs_s xs_cur : List (BitVec 64)} {w i cnt cap : Nat}
    (hw1 : 1 ≤ w) (hwi : w ≤ i) (hic : i < cnt) (hcn : cnt ≤ cap)
    (hlen_s : xs_s.length = cap) (hlen : xs_cur.length = cap)
    (hsort_s : SortedRange64 xs_s 0 cnt)
    (hcb_s : ∀ k < cnt, CondBinElemOk F_cur cv lit (xs_s[k]?.getD 0#64))
    (hsort_w : SortedRange64 xs_cur 0 w)
    (hcb_w : ∀ k < w, CondBinElemOk F_cur cv lit (xs_cur[k]?.getD 0#64))
    (htail : ∀ k, i ≤ k → k < cnt → xs_cur[k]? = xs_s[k]?)
    (hlast : ∀ k, i ≤ k → k < cnt → xs_cur[w - 1]?.getD 0#64 ≤ xs_cur[k]?.getD 0#64) :
    let xs' := xs_cur.set w (xs_cur[i]'(by omega))
    SortedRange64 xs' 0 (w + 1) ∧
    (∀ k < w + 1, CondBinElemOk F_cur cv lit (xs'[k]?.getD 0#64)) ∧
    (∀ k, i + 1 ≤ k → k < cnt → xs'[k]? = xs_s[k]?) ∧
    (∀ k, i + 1 ≤ k → k < cnt → xs'[w]?.getD 0#64 ≤ xs'[k]?.getD 0#64) := by
  intro xs'
  have hi_len : i < xs_cur.length := by omega
  have hw_len : w < xs_cur.length := by omega
  have hle_wi : xs_cur[w - 1]?.getD 0#64 ≤ xs_cur[i]?.getD 0#64 := hlast i (Nat.le_refl _) hic
  have hw_val : xs'[w]?.getD 0#64 = xs_cur[i]?.getD 0#64 := by
    rw [show xs'[w]? = some (xs_cur[i]'hi_len) from List.getElem?_set_self hw_len,
      Option.getD_some, List.getElem?_eq_getElem hi_len, Option.getD_some]
  refine ⟨fun a b ha hab hb => ?_, fun k hk => ?_, fun k hk1 hk2 => ?_, fun k hk1 hk2 => ?_⟩
  · by_cases hbw : b = w
    · rw [hbw, hw_val]
      by_cases haw : a = w
      · rw [haw, hw_val]; exact BitVec.le_refl _
      · have hal : a < w := by omega
        rw [show xs'[a]? = xs_cur[a]? from List.getElem?_set_ne (by omega)]
        exact BitVec.le_trans (hsort_w a (w - 1) ha (by omega) (by omega)) hle_wi
    · have hbl : b < w := by omega
      rw [show xs'[a]? = xs_cur[a]? from List.getElem?_set_ne (by omega),
        show xs'[b]? = xs_cur[b]? from List.getElem?_set_ne (by omega)]
      exact hsort_w a b ha hab hbl
  · by_cases hkw : k = w
    · rw [hkw, hw_val, htail i (Nat.le_refl _) hic]; exact hcb_s i hic
    · rw [show xs'[k]? = xs_cur[k]? from List.getElem?_set_ne (by omega)]
      exact hcb_w k (by omega)
  · rw [show xs'[k]? = xs_cur[k]? from List.getElem?_set_ne (by omega)]
    exact htail k (by omega) hk2
  · rw [hw_val, show xs'[k]? = xs_cur[k]? from List.getElem?_set_ne (by omega),
      htail i (Nat.le_refl _) hic, htail k (by omega) hk2]
    exact hsort_s i k (Nat.zero_le _) (by omega) hk2

private theorem copy_condbin_arena_lits_mem {k : FullCoreState} {cr : Nat}
    {lit : Nat} {u0 u1 : BitVec 32} {found : Bool} {rem : BitVec 32}
    (_ : fullArenaClauseSizeCore k cr ≤ k.arena.length - (cr + 3))
    (hstep : ∀ idx < fullArenaClauseSizeCore k cr,
      let l := (k.arena[cr + 3 + idx]?.getD 0#32).toNat
      k.vals[l]?.getD 0#8 = 255#8 ∨ (found = true ∧ l = lit) ∨
        (1 ≤ rem.toNat ∧ l = u0.toNat) ∨ (rem.toNat = 2 ∧ l = u1.toNat))
    (hfound : found = true) (hrem : rem = 2#32) :
    ∀ l ∈ fullArenaClauseLitsCore k cr,
      k.vals[l]?.getD 0#8 = 255#8 ∨ l = lit ∨ l = u0.toNat ∨ l = u1.toNat := by
  intro l hl
  dsimp only [fullArenaClauseLitsCore] at hl
  rw [List.mem_map] at hl
  obtain ⟨bv, hbv, rfl⟩ := hl
  have hmem_drop : bv ∈
      List.drop (cr + 3) (List.take (cr + 3 + fullArenaClauseSizeCore k cr) k.arena) := by
    rw [List.drop_take, Nat.add_sub_cancel_left]; exact hbv
  obtain ⟨idx, hidx, hbv_eq⟩ := List.getElem_of_mem hmem_drop
  simp only [List.length_take, List.length_drop] at hidx
  have hidx_sz : idx < fullArenaClauseSizeCore k cr := by omega
  have hbv_at : k.arena[cr + 3 + idx]?.getD 0#32 = bv := by
    rw [← hbv_eq]
    simp only [List.getElem_take, List.getElem_drop, List.getElem?_eq_getElem
      (by omega : cr + 3 + idx < k.arena.length), Option.getD_some]
  have hs := hstep idx hidx_sz
  rw [hbv_at, hfound, hrem] at hs
  rcases hs with h | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

private def CopyCondbinDedupInv (c : FullCfg) (F_cur : List (List Nat)) (s : FullState)
    (lit : Nat) (out : Val i64) (cap cnt : Nat) (xs_s : List (BitVec 64))
    (R : Mem 64 → Prop) (w i : Nat) (m_d : Mem 64) : Prop :=
  ∃ out_d : List (BitVec 64), out_d.length = cap ∧ 1 ≤ w ∧ w ≤ i ∧ i ≤ cnt ∧
    SortedRange64 out_d 0 w ∧
    (∀ k < w, CondBinElemOk F_cur s.core.cur_vars lit (out_d[k]?.getD 0#64)) ∧
    (∀ k, i ≤ k → k < cnt → out_d[k]? = xs_s[k]?) ∧
    (∀ k, i ≤ k → k < cnt → out_d[w - 1]?.getD 0#64 ≤ out_d[k]?.getD 0#64) ∧
    (FullMemNoWks3 c s ⋆ array64 out out_d ⋆ R) m_d

private def CopyCondbinWatchInv (c : FullCfg) (F_cur : List (List Nat)) (s : FullState)
    (lit : Nat) (out : Val i64) (cap off wsz : Nat) (R : Mem 64 → Prop)
    (p cnt : Nat) (mg : Mem 64) : Prop :=
  ∃ out_c : List (BitVec 64), out_c.length = cap ∧
    off ≤ p ∧ p ≤ off + wsz ∧ cnt ≤ cap ∧
    DenseWatchSliceOk F_cur s.core lit p (off + wsz - p) ∧
    (∀ k < cnt, CondBinElemOk F_cur s.core.cur_vars lit (out_c[k]?.getD 0#64)) ∧
    (FullMemNoWks3 c s ⋆ array64 out out_c ⋆ R) mg

private def CopyCondbinClausePost (c : FullCfg) (F_cur : List (List Nat)) (s : FullState)
    (lit : Nat) (out : Val i64) (cap off wsz p : Nat) (R : Mem 64 → Prop)
    (cnt' : Nat) (m' : Mem 64) : Prop :=
  ∃ out_c' : List (BitVec 64), out_c'.length = cap ∧ cnt' ≤ cap ∧
    DenseWatchSliceOk F_cur s.core lit (p + 2) (off + wsz - p - 2) ∧
    (∀ k < cnt', CondBinElemOk F_cur s.core.cur_vars lit (out_c'[k]?.getD 0#64)) ∧
    (FullMemNoWks3 c s ⋆ array64 out out_c' ⋆ R) m'

private def CopyCondbinScanInv (s : FullState) (cr lit sz : Nat) (mg : Mem 64)
    (u0 u1 rem : BitVec 32) (found : Bool) (i : Nat) (ml : Mem 64) : Prop :=
  ml = mg ∧ i ≤ sz ∧ rem.toNat ≤ 2 ∧
  (1 ≤ rem.toNat → u0.toNat < 2 * s.core.cur_vars ∧ u0.toNat ≠ lit) ∧
  (rem.toNat = 2 → u1.toNat < 2 * s.core.cur_vars ∧ u1.toNat ≠ lit) ∧
  ∀ k < i,
    let l := (s.core.arena[cr + 3 + k]?.getD 0#32).toNat
    s.core.vals[l]?.getD 0#8 = 255#8 ∨ (found = true ∧ l = lit) ∨
      (1 ≤ rem.toNat ∧ l = u0.toNat) ∨ (rem.toNat = 2 ∧ l = u1.toNat)

private theorem copy_condbin_wvec_bounds {c : FullCfg} {F_cur : List (List Nat)} {s : FullState}
    {lit : BitVec 32} (hlen : FullState.LengthsOk c s)
    (hdense_w : DenseWatchesInv F_cur s.core) (hlit_lt : lit.toNat < 2 * s.core.cur_vars) :
    let off := fullWatchOffCore s.core lit.toNat
    let wsz := fullWatchSizeCore s.core lit.toNat
    off < 2 ^ 64 ∧ wsz < 2 ^ 64 ∧ off + wsz < 2 ^ 64 ∧
    (∃ (_ : (lit.setWidth 64 <<< (1 : BitVec 64)).toNat < s.core.wvec.length)
       (_ : (lit.setWidth 64 <<< (1 : BitVec 64) + (1 : BitVec 64)).toNat < s.core.wvec.length),
      ∀ h0 : (lit.setWidth 64 <<< (1 : BitVec 64)).toNat < s.core.wvec.length,
        (s.core.wvec[(lit.setWidth 64 <<< (1 : BitVec 64)).toNat]'h0).setWidth 64 =
          BitVec.ofNat 64 off) ∧
    (∀ h0 : 2 * lit.toNat % 2 ^ 64 < s.core.wvec.length,
      (s.core.wvec[2 * lit.toNat % 2 ^ 64]'h0).toNat = off) ∧
    (∀ h1 : (2 * lit.toNat + (1 : BitVec 64).toNat) % 2 ^ 64 < s.core.wvec.length,
      (s.core.wvec[(2 * lit.toNat + (1 : BitVec 64).toNat) % 2 ^ 64]'h1).toNat = wsz) := by
  have hbounds := hdense_w.layout.bounds lit.toNat hlit_lt
  have hwc := c.hwcap; dsimp only [dimacsBound] at hwc
  have hmaxv := c.hmaxv; dsimp only [dimacsBound] at hmaxv
  have hwlen_le := hlen.core_ok.wlen_le
  have hwvec_len := hlen.core_ok.wvec_len
  have hcv_le := hlen.core_ok.cur_vars_le
  have hw0_idx : (lit.setWidth 64 <<< (1 : BitVec 64)).toNat = 2 * lit.toNat := by
    rw [show (1 : BitVec 64) = 1#64 from rfl,
      bv64_shl1_lt (by rw [bv_zext32_toNat]; omega), bv_zext32_toNat]
  have hw1_idx : (lit.setWidth 64 <<< (1 : BitVec 64) + (1 : BitVec 64)).toNat =
      2 * lit.toNat + 1 := by
    rw [show (1 : BitVec 64) = 1#64 from rfl,
      bv64_shl1_add1_lt (by rw [bv_zext32_toNat]; omega), bv_zext32_toNat]
  refine ⟨by omega, by omega, by omega, ⟨by omega, by omega, fun h0 => ?_⟩,
    fun h0 => ?_, fun h1 => ?_⟩
  · apply BitVec.eq_of_toNat_eq
    rw [bv_zext32_toNat, list_getElem_congr hw0_idx, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega)]
    · simp [fullWatchOffCore,
        List.getElem?_eq_getElem (by omega : 2 * lit.toNat < s.core.wvec.length)]
    · omega
  · rw [list_getElem_congr (Nat.mod_eq_of_lt (by omega) :
      2 * lit.toNat % 2 ^ 64 = 2 * lit.toNat)]
    · simp [fullWatchOffCore,
        List.getElem?_eq_getElem (by omega : 2 * lit.toNat < s.core.wvec.length)]
    · omega
  · rw [list_getElem_congr (by
      rw [show (1 : BitVec 64).toNat = 1 by rfl]; exact Nat.mod_eq_of_lt (by omega) :
      (2 * lit.toNat + (1 : BitVec 64).toNat) % 2 ^ 64 = 2 * lit.toNat + 1)]
    · simp [fullWatchSizeCore,
        List.getElem?_eq_getElem (by omega : 2 * lit.toNat + 1 < s.core.wvec.length)]
    · omega

private theorem copy_condbin_l32_dom {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {cr sz i : Nat}
    (hlen : FullState.LengthsOk c s) (hw : FullWitnessInv c F0 F_cur s.core)
    (hcr : cr ∈ fullArenaClauseRefs s) (hgarb : fullArenaClauseGarb s cr = false)
    (hsz_core : fullArenaClauseSizeCore s.core cr = sz)
    (hcr_sz : cr + 2 + sz < s.core.arena_len) (hi : i < sz) :
    have har : cr + 3 + i < s.core.arena.length := by
      have := hlen.core_ok.arena_len_le; have := hlen.core_ok.arena_len_arr; omega
    let l32 := s.core.arena[cr + 3 + i]'har
    have hlt : l32.toNat < 2 * s.core.cur_vars := by
      refine hw.arena.lits_lt cr hcr hgarb l32.toNat ?_
      dsimp only [fullArenaClauseLitsCore, l32]
      rw [List.mem_map]
      refine ⟨s.core.arena[cr + 3 + i]'har, ?_, rfl⟩
      exact List.mem_of_getElem? (i := i) (by
        simp only [List.getElem?_take, List.getElem?_drop, hsz_core, hi, ↓reduceIte,
          List.getElem?_eq_getElem har])
    have hvl : l32.toNat < s.core.vals.length := by
      have := hlen.core_ok.cur_vars_le; have := hlen.core_ok.vals_len; omega
    l32.toNat < 2 * s.core.cur_vars ∧
    (s.core.vals[l32.toNat]'hvl = 0#8 ∨ s.core.vals[l32.toNat]'hvl = 1#8 ∨
      s.core.vals[l32.toNat]'hvl = 255#8) := by
  intro har l32 hlt hvl
  refine ⟨hlt, ?_⟩
  have hv := hw.vals_domain l32.toNat hlt
  rwa [List.getElem?_eq_getElem hvl, Option.getD_some] at hv

private theorem copy_condbin_emit_ok {F_cur : List (List Nat)} {cv lit : Nat}
    {hi32 lo32 u0 u1 : BitVec 32} {out_c : List (BitVec 64)} {cnt : Nat}
    (hu0 : u0.toNat < 2 * cv) (hu1 : u1.toNat < 2 * cv)
    (hnl0 : u0.toNat / 2 ≠ lit / 2) (hnl1 : u1.toNat / 2 ≠ lit / 2)
    (hn01 : u0.toNat / 2 ≠ u1.toNat / 2)
    (hent_raw : CNF.EntailsClause (cnfOfClauses F_cur) (cnfClause [lit, u0.toNat, u1.toNat]))
    (hp : (hi32 = u0 ∧ lo32 = u1) ∨ (hi32 = u1 ∧ lo32 = u0))
    (hcnt : cnt < out_c.length)
    (hcb : ∀ k < cnt, CondBinElemOk F_cur cv lit (out_c[k]?.getD 0#64)) :
    ∀ k < cnt + 1, CondBinElemOk F_cur cv lit
      ((out_c.set cnt (hi32.setWidth 64 <<< 32#64 ||| lo32.setWidth 64))[k]?.getD 0#64) := by
  have hnew : CondBinElemOk F_cur cv lit
      (hi32.setWidth 64 <<< 32#64 ||| lo32.setWidth 64) := by
    rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact condBin_of_pack hu0 hu1 hn01 hnl0 hnl1 hent_raw
    · refine condBin_of_pack hu1 hu0 hn01.symm hnl1 hnl0 ?_
      exact entails_perm_clause (fun x hx => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
        rcases hx with rfl | rfl | rfl <;> simp) hent_raw
  intro k hk
  by_cases hkc : k = cnt
  · rw [hkc, List.getElem?_set_self hcnt, Option.getD_some]; exact hnew
  · rw [List.getElem?_set_ne (Ne.symm hkc)]; exact hcb k (by omega)

private theorem copy_condbin_cr_clause {c : FullCfg} {s : FullState} {p : BitVec 64}
    {cr' : BitVec 32} (hlen : FullState.LengthsOk c s)
    (hp_wstk : p.toNat + 1 < s.core.wstk.length)
    (hcr_eq : s.core.wstk[p.toNat + 1]? = some cr') :
    ∀ h, s.core.wstk[(p.toNat + (1 : BitVec 64).toNat) % 2 ^ 64]'h = cr' := by
  have hac := c.harena; dsimp only [dimacsBound] at hac
  have hwc := c.hwcap; dsimp only [dimacsBound] at hwc
  have hwstk_len := hlen.core_ok.wstk_len_arr
  have hp1_mod : (p.toNat + (1 : BitVec 64).toNat) % 2 ^ 64 = p.toNat + 1 := by
    rw [show (1 : BitVec 64).toNat = 1 by rfl]; exact Nat.mod_eq_of_lt (by omega)
  intro h
  rw [list_getElem_congr hp1_mod (hj := hp_wstk)]
  rw [List.getElem?_eq_getElem hp_wstk] at hcr_eq
  exact Option.some.inj hcr_eq

private theorem copy_condbin_arena_ok {c : FullCfg} {s : FullState} {p : BitVec 64}
    {cr' : BitVec 32} (hlen : FullState.LengthsOk c s)
    (hcr_val : ∀ h, s.core.wstk[(p.toNat + (1 : BitVec 64).toNat) % 2 ^ 64]'h = cr')
    (hc2 : ∃ h, ((s.core.wstk[(p.toNat + (1 : BitVec 64).toNat) % 2 ^ 64]'h).toNat +
      (2 : BitVec 64).toNat) % 2 ^ 64 < s.core.arena_len % 2 ^ 64) :
    cr'.toNat + 2 < s.core.arena_len ∧
    cr'.toNat < s.core.arena.length ∧ cr'.toNat + 2 < s.core.arena.length := by
  have hac := c.harena; dsimp only [dimacsBound] at hac
  have harenal_le := hlen.core_ok.arena_len_le; have harena_len := hlen.core_ok.arena_len_arr
  obtain ⟨hw, hlt⟩ := hc2
  rw [hcr_val hw, show (2 : BitVec 64).toNat = 2 by rfl,
    Nat.mod_eq_of_lt (by have := cr'.isLt; omega),
    Nat.mod_eq_of_lt (by omega : s.core.arena_len < 2 ^ 64)] at hlt
  exact ⟨hlt, by omega, by omega⟩

private theorem copy_condbin_scan_step {s : FullState} {cr lit sz i : Nat} {mg : Mem 64}
    {u0 u1 rem u0' u1' rem' : BitVec 32} {found found' : Bool}
    (hi : i < sz) (har : cr + 3 + i < s.core.arena.length)
    (hprev : ∀ k < i, let l := (s.core.arena[cr + 3 + k]?.getD 0#32).toNat
      s.core.vals[l]?.getD 0#8 = 255#8 ∨ (found = true ∧ l = lit) ∨
        (1 ≤ rem.toNat ∧ l = u0.toNat) ∨ (rem.toNat = 2 ∧ l = u1.toNat))
    (hrem' : rem'.toNat ≤ 2)
    (hu0' : 1 ≤ rem'.toNat → u0'.toNat < 2 * s.core.cur_vars ∧ u0'.toNat ≠ lit)
    (hu1' : rem'.toNat = 2 → u1'.toNat < 2 * s.core.cur_vars ∧ u1'.toNat ≠ lit)
    (hkeep : ∀ l,
      (s.core.vals[l]?.getD 0#8 = 255#8 ∨ (found = true ∧ l = lit) ∨
        (1 ≤ rem.toNat ∧ l = u0.toNat) ∨ (rem.toNat = 2 ∧ l = u1.toNat)) →
      (s.core.vals[l]?.getD 0#8 = 255#8 ∨ (found' = true ∧ l = lit) ∨
        (1 ≤ rem'.toNat ∧ l = u0'.toNat) ∨ (rem'.toNat = 2 ∧ l = u1'.toNat)))
    (hcur : let l := (s.core.arena[cr + 3 + i]'har).toNat
      s.core.vals[l]?.getD 0#8 = 255#8 ∨ (found' = true ∧ l = lit) ∨
        (1 ≤ rem'.toNat ∧ l = u0'.toNat) ∨ (rem'.toNat = 2 ∧ l = u1'.toNat)) :
    CopyCondbinScanInv s cr lit sz mg u0' u1' rem' found' (i + 1) mg := by
  refine ⟨rfl, by omega, hrem', hu0', hu1', fun k hk => ?_⟩
  by_cases hki : k < i
  · exact hkeep _ (hprev k hki)
  · have : k = i := by omega
    subst this; rw [List.getElem?_eq_getElem har, Option.getD_some]; exact hcur

private theorem copy_condbin_keep {c : FullCfg} {F_cur : List (List Nat)} {s : FullState}
    {lit : Nat} {out : Val i64} {cap off wsz p : Nat} {R : Mem 64 → Prop}
    {out_c : List (BitVec 64)} {cnt : Nat} {mg : Mem 64}
    (hlen : out_c.length = cap) (hcn : cnt ≤ cap)
    (hsl : DenseWatchSliceOk F_cur s.core lit (p + 2) (off + wsz - (p + 2)))
    (hcb : ∀ k < cnt, CondBinElemOk F_cur s.core.cur_vars lit (out_c[k]?.getD 0#64))
    (hmg : (FullMemNoWks3 c s ⋆ array64 out out_c ⋆ R) mg) :
    CopyCondbinClausePost c F_cur s lit out cap off wsz p R cnt mg :=
  ⟨out_c, hlen, hcn, by simpa only [show off + wsz - p - 2 = off + wsz - (p + 2) by omega]
    using hsl, hcb, hmg⟩

private theorem bv32_shr1_nat (x : BitVec 32) : (x >>> (1 : Nat)).toNat = x.toNat / 2 := by
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

private theorem bv32_shr1_bv (x : BitVec 32) : (x >>> 1#32).toNat = x.toNat / 2 := by
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

private theorem copy_condbin_arena_zext_eq {s : FullState} {cr' : BitVec 32} {p : BitVec 64}
    {i : BitVec 32} (hp1_nat : (p + 1).toNat = p.toNat + 1)
    (_hp1_wstk : p.toNat + 1 < s.core.wstk.length)
    (hcr_val : ∀ h, s.core.wstk[(p.toNat + (1 : BitVec 64).toNat) % 2 ^ 64]'h = cr')
    (_hcr_sz_lt : cr'.toNat + 2 + i.toNat + 1 < s.core.arena_len)
    (hl_ar : cr'.toNat + 3 + i.toNat < s.core.arena.length) :
    ∀ h1 h2,
      s.core.arena[(BitVec.setWidth 64 (s.core.wstk[(p + 1).toNat]'h1) + 3 +
        BitVec.setWidth 64 i).toNat]'h2 = s.core.arena[cr'.toNat + 3 + i.toNat]'hl_ar := by
  intro h1 h2
  have hwp1 : s.core.wstk[(p + 1).toNat]'h1 = cr' := by
    have he : (p + 1).toNat = (p.toNat + (1 : BitVec 64).toNat) % 2 ^ 64 := by
      rw [hp1_nat, show (1 : BitVec 64).toNat = 1 by rfl, Nat.mod_eq_of_lt (by omega)]
    rw [list_getElem_congr he (hj := (by rw [← he]; exact h1))]; exact hcr_val _
  have hidx_eq : (BitVec.setWidth 64 (s.core.wstk[(p + 1).toNat]'h1) + 3 +
      BitVec.setWidth 64 i).toNat = cr'.toNat + 3 + i.toNat := by
    have hc32 : cr'.toNat < 4294967296 := cr'.isLt
    have hi32 : i.toNat < 4294967296 := i.isLt
    rw [hwp1, BitVec.toNat_add, BitVec.toNat_add, bv_zext32_toNat, bv_zext32_toNat,
      show (3 : BitVec 64).toNat = 3 by rfl,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  exact list_getElem_congr hidx_eq h2 hl_ar

private theorem copy_condbin_arena_mod_eq {s : FullState} {cr' : BitVec 32} {p : BitVec 64}
    {i : BitVec 32}
    (hcr_val : ∀ h, s.core.wstk[(p.toNat + (1 : BitVec 64).toNat) % 2 ^ 64]'h = cr')
    (hl_ar : cr'.toNat + 3 + i.toNat < s.core.arena.length) :
    ∀ h1 h2,
      s.core.arena[((s.core.wstk[(p.toNat + (1 : BitVec 64).toNat) % 2 ^ 64]'h1).toNat +
        (3 : BitVec 64).toNat + i.toNat) % 2 ^ 64]'h2 =
        s.core.arena[cr'.toNat + 3 + i.toNat]'hl_ar := by
  intro h1 h2
  have heq : ((s.core.wstk[(p.toNat + (1 : BitVec 64).toNat) % 2 ^ 64]'h1).toNat +
      (3 : BitVec 64).toNat + i.toNat) % 2 ^ 64 = cr'.toNat + 3 + i.toNat := by
    have hc32 : cr'.toNat < 4294967296 := cr'.isLt
    have hi32 : i.toNat < 4294967296 := i.isLt
    rw [hcr_val h1, show (3 : BitVec 64).toNat = 3 by rfl, Nat.mod_eq_of_lt (by omega)]
  exact list_getElem_congr heq h2 hl_ar

private theorem copy_condbin_vals_mod_eq {s : FullState} {cr' : BitVec 32} {p : BitVec 64}
    {i : BitVec 32}
    (hcr_val : ∀ h, s.core.wstk[(p.toNat + (1 : BitVec 64).toNat) % 2 ^ 64]'h = cr')
    (hl_ar : cr'.toNat + 3 + i.toNat < s.core.arena.length)
    (hl_vals : (s.core.arena[cr'.toNat + 3 + i.toNat]'hl_ar).toNat < s.core.vals.length) :
    ∀ h1 h2 h3,
      s.core.vals[(s.core.arena[((s.core.wstk[(p.toNat + (1 : BitVec 64).toNat) %
        2 ^ 64]'h1).toNat + (3 : BitVec 64).toNat + i.toNat) % 2 ^ 64]'h2).toNat]'h3 =
        s.core.vals[(s.core.arena[cr'.toNat + 3 + i.toNat]'hl_ar).toNat]'hl_vals := by
  intro h1 h2 h3
  have ha := copy_condbin_arena_mod_eq hcr_val hl_ar h1 h2
  exact list_getElem_congr (congrArg BitVec.toNat ha) h3 hl_vals

private theorem copy_condbin_scan_elem_facts {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} {cr' : BitVec 32} {p : BitVec 64}
    {sz32 i : BitVec 32} (hlen : FullState.LengthsOk c s)
    (hw : FullWitnessInv c F0 F_cur s.core) (hcr_mem : cr'.toNat ∈ fullArenaClauseRefs s)
    (hgarb : fullArenaClauseGarb s cr'.toNat = false)
    (hsz_core : fullArenaClauseSizeCore s.core cr'.toNat = sz32.toNat)
    (hcr_sz_lt : cr'.toNat + 2 + sz32.toNat < s.core.arena_len) (hi_lt : i.toNat < sz32.toNat)
    (hp1_nat : (p + 1).toNat = p.toNat + 1) (hp1_wstk : p.toNat + 1 < s.core.wstk.length)
    (hcr_val : ∀ h, s.core.wstk[(p.toNat + (1 : BitVec 64).toNat) % 2 ^ 64]'h = cr') :
    ∃ (hl_ar : cr'.toNat + 3 + i.toNat < s.core.arena.length)
      (hl_lt : (s.core.arena[cr'.toNat + 3 + i.toNat]'hl_ar).toNat < 2 * s.core.cur_vars)
      (hl_vals : (s.core.arena[cr'.toNat + 3 + i.toNat]'hl_ar).toNat < s.core.vals.length)
      (hcr3i_lt :
        (BitVec.setWidth 64 (s.core.wstk[(p + 1).toNat]'(by rw [hp1_nat]; exact hp1_wstk)) +
          3 + BitVec.setWidth 64 i).toNat < s.core.arena.length),
      let l32 := s.core.arena[cr'.toNat + 3 + i.toNat]'hl_ar
      let v8 := s.core.vals[l32.toNat]'hl_vals
      (v8 = 0#8 ∨ v8 = 1#8 ∨ v8 = 255#8) ∧
      ((BitVec.setWidth 64 (s.core.arena[(BitVec.setWidth 64
        (s.core.wstk[(p + 1).toNat]'(by rw [hp1_nat]; exact hp1_wstk)) + 3 +
        BitVec.setWidth 64 i).toNat]'hcr3i_lt)).toNat < s.core.vals.length) := by
  obtain ⟨hl_lt, hv_dom⟩ :=
    copy_condbin_l32_dom hlen hw hcr_mem hgarb hsz_core hcr_sz_lt hi_lt
  have harenal_le := hlen.core_ok.arena_len_le; have harena_len := hlen.core_ok.arena_len_arr
  have hcv_le := hlen.core_ok.cur_vars_le; have hvals_len := hlen.core_ok.vals_len
  have hl_ar : cr'.toNat + 3 + i.toNat < s.core.arena.length := by omega
  have hl_vals : (s.core.arena[cr'.toNat + 3 + i.toNat]'hl_ar).toNat < s.core.vals.length := by
    omega
  have hz := copy_condbin_arena_zext_eq hp1_nat hp1_wstk hcr_val (by omega) hl_ar
  have hwp1_lt : (p + 1).toNat < s.core.wstk.length := by rw [hp1_nat]; exact hp1_wstk
  have hwp1 : s.core.wstk[(p + 1).toNat]'hwp1_lt = cr' := by
    have he : (p + 1).toNat = (p.toNat + (1 : BitVec 64).toNat) % 2 ^ 64 := by
      rw [hp1_nat, show (1 : BitVec 64).toNat = 1 by rfl, Nat.mod_eq_of_lt (by omega)]
    rw [list_getElem_congr he (hj := (by rw [← he]; exact hwp1_lt))]; exact hcr_val _
  have hcr3i_lt : (BitVec.setWidth 64 (s.core.wstk[(p + 1).toNat]'hwp1_lt) + 3 +
      BitVec.setWidth 64 i).toNat < s.core.arena.length := by
    have hc32 : cr'.toNat < 4294967296 := cr'.isLt
    have hi32 : i.toNat < 4294967296 := i.isLt
    rw [hwp1, BitVec.toNat_add, BitVec.toNat_add, bv_zext32_toNat, bv_zext32_toNat,
      show (3 : BitVec 64).toNat = 3 by rfl,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    exact hl_ar
  refine ⟨hl_ar, hl_lt, hl_vals, hcr3i_lt, hv_dom, ?_⟩
  rw [hz hwp1_lt hcr3i_lt, bv_zext32_toNat]; exact hl_vals

private theorem copy_condbin_step_rem0 {s : FullState} {cr lit sz i : Nat} {mg : Mem 64}
    {u0 u1 rem : BitVec 32} {found : Bool} (hi : i < sz) (har : cr + 3 + i < s.core.arena.length)
    (hl_lt : (s.core.arena[cr + 3 + i]'har).toNat < 2 * s.core.cur_vars)
    (hl_ne : (s.core.arena[cr + 3 + i]'har).toNat ≠ lit) (hrem0 : rem = 0#32)
    (hprev : ∀ k < i, let l := (s.core.arena[cr + 3 + k]?.getD 0#32).toNat
      s.core.vals[l]?.getD 0#8 = 255#8 ∨ (found = true ∧ l = lit) ∨
        (1 ≤ rem.toNat ∧ l = u0.toNat) ∨ (rem.toNat = 2 ∧ l = u1.toNat)) :
    CopyCondbinScanInv s cr lit sz mg (s.core.arena[cr + 3 + i]'har) u1 1#32 found
      (i + 1) mg :=
  copy_condbin_scan_step hi har hprev (by decide) (fun _ => ⟨hl_lt, hl_ne⟩)
    (fun h => by simp at h) (fun _ h => by
      rcases h with h | h | ⟨h1, _⟩ | ⟨h2, _⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exfalso; rw [hrem0] at h1; simp at h1
      · exfalso; rw [hrem0] at h2; simp at h2)
    (Or.inr (Or.inr (Or.inl ⟨by decide, rfl⟩)))

private theorem copy_condbin_step_rem1 {s : FullState} {cr lit sz i : Nat} {mg : Mem 64}
    {u0 u1 rem : BitVec 32} {found : Bool} (hi : i < sz) (har : cr + 3 + i < s.core.arena.length)
    (hl_lt : (s.core.arena[cr + 3 + i]'har).toNat < 2 * s.core.cur_vars)
    (hl_ne : (s.core.arena[cr + 3 + i]'har).toNat ≠ lit) (hrem1 : rem = 1#32)
    (hu0 : 1 ≤ rem.toNat → u0.toNat < 2 * s.core.cur_vars ∧ u0.toNat ≠ lit)
    (hprev : ∀ k < i, let l := (s.core.arena[cr + 3 + k]?.getD 0#32).toNat
      s.core.vals[l]?.getD 0#8 = 255#8 ∨ (found = true ∧ l = lit) ∨
        (1 ≤ rem.toNat ∧ l = u0.toNat) ∨ (rem.toNat = 2 ∧ l = u1.toNat)) :
    CopyCondbinScanInv s cr lit sz mg u0 (s.core.arena[cr + 3 + i]'har) 2#32 found
      (i + 1) mg :=
  copy_condbin_scan_step hi har hprev (by decide) (fun _ => hu0 (by rw [hrem1]; decide))
    (fun _ => ⟨hl_lt, hl_ne⟩) (fun _ h => by
      rcases h with h | h | ⟨_, h⟩ | ⟨h2, _⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl ⟨by decide, h⟩))
      · exfalso; rw [hrem1] at h2; simp at h2)
    (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))

/-- Canonical `Func.wp` proof for `full_cong_copy_condbin_m7`. -/
theorem full_cong_copy_condbin_m7_wp (Γ : Env)
    (hSort : Γ.Has "full_cong_u64_sort_m7" Spec.fullCongU64SortM7Spec) :
    ∀ a m Q X, Spec.fullCongCopyCondbinM7Spec a m Q X →
      Func.wp Γ full_cong_copy_condbin_m7_body a m Q X := by
  rintro ⟨h, lit, out, cap, ⟨⟩⟩ m0 Q X
    ⟨c, F0, F_cur, s, out0, R, rfl, hlen, hw, hlvl0, hdense, hlit_lt, hout_len, hcap, hm0, hQ⟩
  have hdense_w : DenseWatchesInv F_cur s.core := by
    simpa only [ModeWatchesInv, hdense, ↓reduceIte] using hw.watches
  have hslice := hdense_w.slices lit.toNat hlit_lt
  have hbounds := hdense_w.layout.bounds lit.toNat hlit_lt
  have hwc := c.hwcap; dsimp only [dimacsBound] at hwc
  have hac := c.harena; dsimp only [dimacsBound] at hac
  have hwlen_le := hlen.core_ok.wlen_le; have hwstk_len := hlen.core_ok.wstk_len_arr
  have harenal_le := hlen.core_ok.arena_len_le; have harena_len := hlen.core_ok.arena_len_arr
  let off := fullWatchOffCore s.core lit.toNat
  let wsz := fullWatchSizeCore s.core lit.toNat
  obtain ⟨hoff_lt64, _, hbd, ⟨hwv0_lt, hwv1_lt, hoff_eq⟩, hwvec0_toNat, hwvec1_toNat⟩ :=
    copy_condbin_wvec_bounds hlen hdense_w hlit_lt
  unfold Func.wp full_cong_copy_condbin_m7_body
  c0_hsteps_nogrp
  refine wp_join_group
    (fun (pcnt : Tup Val [i64, i64]) mg =>
      ∃ out_s : List (BitVec 64), out_s.length = cap.toNat ∧
        pcnt.2.1.toNat ≤ cap.toNat ∧
        (∀ k < pcnt.2.1.toNat,
          CondBinElemOk F_cur s.core.cur_vars lit.toNat (out_s[k]?.getD 0#64)) ∧
        (FullMemNoWks3 c s ⋆ array64 out out_s ⋆ R) mg)
    ?_ (fun J_out hJ_out => ?_)
  · rintro J_out ⟨_, cnt, ⟨⟩⟩ mg ⟨out_s, hlen_os, hcnt_cap, hcb_os, hmg⟩
    dsimp only at hcnt_cap hcb_os
    c0_hsteps_nogrp; c0_hsplit
    · have hcnt_le1 : cnt.toNat ≤ 1 := by
        simpa only [show (1 : BitVec 64).toNat = 1 by rfl] using hc
      refine hQ cnt out_s mg hlen_os hcnt_cap (fun i j hi hij hj => ?_) hcb_os hmg
      have hij_eq : i = j := by omega
      rw [hij_eq]; exact BitVec.le_refl _
    · have h1bv : (1 : BitVec 64).toNat = 1 := rfl
      have hcnt_gt1 : 1 < cnt.toNat := by rw [h1bv] at hc; omega
      c0_hsteps_nogrp; cong_call hSort; dsimp only [vals, Arg.val]
      refine ⟨out_s, (FullMemNoWks3 c s ⋆ R), by omega, by omega,
        by rw [← sep_assoc, sep_comm (array64 out out_s)]; exact hmg,
        fun xs_s m_s hlen_s _ hperm_s hsort_s hm_s => ?_⟩
      have hm_s' : (FullMemNoWks3 c s ⋆ array64 out xs_s ⋆ R) m_s := by
        rw [← sep_assoc, sep_comm (array64 out xs_s)] at hm_s; exact hm_s
      have hcb_s : ∀ k < cnt.toNat,
          CondBinElemOk F_cur s.core.cur_vars lit.toNat (xs_s[k]?.getD 0#64) := by
        intro k hk; obtain ⟨j, hj, heq⟩ := hperm_s k hk; rw [heq]; exact hcb_os j hj
      c0_hsteps_nogrp
      refine wp_loop_inv (ts := [i64, i64])
        (fun (w, i, ()) m_d =>
          CopyCondbinDedupInv c F_cur s lit.toNat out cap.toNat cnt.toNat xs_s R
            w.toNat i.toNat m_d)
        (fun (_, i, ()) _ => cnt.toNat - i.toNat)
        (fun Jd hJd => by
          c0_hsteps!
          exact hJd (1, 1, ()) m_s ⟨xs_s, by omega, by omega, Nat.le_refl _, by omega,
            fun a b ha hab hb => by
              have hab_eq : a = b := by omega
              rw [hab_eq]; exact BitVec.le_refl _,
            fun k hk => hcb_s k (by omega), fun _ _ _ => rfl,
            fun k hk1 hk2 => hsort_s 0 k (Nat.zero_le _) (by omega) hk2, hm_s'⟩)
        (fun Jd (w, i, ()) m_d
            ⟨out_d, hlen_od, hw1, hwi, hic, hsort_d, hcb_d, htail_d, hlast_d, hmd⟩ ihd => by
          c0_hsplit
          · have hi_lt : i.toNat < cnt.toNat := hc
            have hw1_nat : (w - 1).toNat = w.toNat - 1 := by
              rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by rw [h1bv]; omega)), h1bv]
            have hi_len : i.toNat < out_d.length := by omega
            have hw1_len : (w - 1).toNat < out_d.length := by omega
            c0_hsteps_nogrp
            refine wp_join_group
              (fun (w', ()) m_w =>
                CopyCondbinDedupInv c F_cur s lit.toNat out cap.toNat cnt.toNat xs_s R
                  w'.toNat (i.toNat + 1) m_w)
              ?_ (fun Jw hJw => ?_)
            · rintro Jw ⟨w', ⟨⟩⟩ m_w
                ⟨out_w, hlen_ow, hw'1, hw'i, _, hsort_w, hcb_w, htail_w, hlast_w, hmw⟩
              have hi1'_nat : (i + 1).toNat = i.toNat + 1 := by
                rw [BitVec.toNat_add, h1bv, Nat.mod_eq_of_lt (by omega)]
              c0_hsteps!
              exact ihd (w', i + 1, ()) m_w (by dsimp only; omega)
                ⟨out_w, hlen_ow, hw'1, by omega, by omega, hsort_w, hcb_w,
                  fun k hk1 hk2 => htail_w k (by omega) hk2,
                  fun k hk1 hk2 => hlast_w k (by omega) hk2, hmw⟩
            · c0_hsteps!; c0_hsplit
              · have hstep := copy_condbin_dedup_step hw1 hwi hi_lt hcnt_cap
                  (by omega) hlen_od hsort_s hcb_s hsort_d hcb_d htail_d hlast_d
                have hle_wi := hlast_d i.toNat (Nat.le_refl _) hi_lt
                have hw_lt : w.toNat < out_d.length := by omega
                have hw1'_nat : (w + 1).toNat = w.toNat + 1 := by
                  rw [BitVec.toNat_add, h1bv, Nat.mod_eq_of_lt (by omega)]
                c0_hsteps!
                have hm' : (FullMemNoWks3 c s ⋆
                    array64 out (out_d.set w.toNat (out_d[i.toNat]'hi_len)) ⋆ R) m := by
                  simp only [sep_emp] at hm
                  rw [← sep_assoc, sep_comm (array64 _ _)] at hm; exact hm
                exact hJw (w + 1, ()) m
                  ⟨out_d.set w.toNat (out_d[i.toNat]'hi_len), by simp [hlen_od], by omega,
                    by omega, by omega, by simpa only [hw1'_nat] using hstep.1,
                    by simpa only [hw1'_nat] using hstep.2.1, hstep.2.2.1,
                    by simpa only [hw1'_nat, show w.toNat + 1 - 1 = w.toNat by omega] using
                      hstep.2.2.2, hm'⟩
              · c0_hsteps!
                exact hJw (w, ()) m_d ⟨out_d, hlen_od, hw1, by omega, by omega, hsort_d, hcb_d,
                  fun k hk1 hk2 => htail_d k (by omega) hk2,
                  fun k hk1 hk2 => hlast_d k (by omega) hk2, hmd⟩
          · c0_hsteps!
            exact hQ w out_d m_d hlen_od (by omega) hsort_d hcb_d hmd)
  · refine wp_loop_inv (ts := [i64, i64])
      (fun (p, cnt, ()) mg =>
        CopyCondbinWatchInv c F_cur s lit.toNat out cap.toNat off wsz R p.toNat cnt.toNat mg)
      (fun (p, _, ()) _ => off + wsz - p.toNat)
      (fun J hJ => by
        c0_hsteps!
        have hslice' : DenseWatchSliceOk F_cur s.core lit.toNat
            (BitVec.ofNat 64 off).toNat (off + wsz - (BitVec.ofNat 64 off).toNat) := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoff_lt64, Nat.add_sub_cancel_left]
          exact hslice
        refine Eq.mpr (congrArg (fun x => J (x, 0, ()) m0) (hoff_eq _)) ?_
        exact hJ (BitVec.ofNat 64 off, 0, ()) m0 ⟨out0, hout_len,
          by simp [BitVec.toNat_ofNat]; omega, by simp [BitVec.toNat_ofNat]; omega,
          Nat.zero_le _, hslice', fun _ h => absurd h (Nat.not_lt_zero _), hm0⟩)
      (fun J (p, cnt, ()) mg
          ⟨out_c, hlen_oc, hpoff, hpend, hcnt_cap, hrem_slice, hcb_c, hmg⟩ ih => by
        c0_hsplit
        · have hp_lt : p.toNat < off + wsz := by
            rw [hwvec0_toNat, hwvec1_toNat, Nat.mod_eq_of_lt hbd] at hc; exact hc
          have hp_wstk : p.toNat < s.core.wstk.length := by omega
          have hpop := slice_pop_step (by rw [ite_eq_right hdense]; exact hrem_slice) (by omega)
          rcases hpop with ⟨w0', hw0_eq, hpop_case⟩
          have hw0_val : s.core.wstk[p.toNat]'hp_wstk = w0' := by
            rw [List.getElem?_eq_getElem hp_wstk] at hw0_eq; exact Option.some.inj hw0_eq
          c0_hsteps_nogrp
          refine wp_join_group
            (fun (p', cnt', ()) mg' => p.toNat < p'.toNat ∧
              CopyCondbinWatchInv c F_cur s lit.toNat out cap.toNat off wsz R
                p'.toNat cnt'.toNat mg')
            ?_ (fun Jn hJn => ?_)
          · rintro Jn ⟨p', cnt', ⟨⟩⟩ mg' ⟨_, inv'⟩
            c0_hsteps!; exact ih (p', cnt', ()) mg' (by dsimp only; omega) inv'
          · c0_hsteps_nogrp; c0_hsplit
            · rcases hpop_case with ⟨hbin_ne, _, hslice1⟩ | ⟨hbin_eq, _⟩
              · have hp1_nat : (p + 1).toNat = p.toNat + 1 := by
                  rw [BitVec.toNat_add, show (1 : BitVec 64).toNat = 1 by rfl,
                    Nat.mod_eq_of_lt (by omega)]
                c0_hsteps!
                exact hJn (p + 1, cnt, ()) mg ⟨by omega, out_c, hlen_oc, by omega, by omega,
                  hcnt_cap, by
                    rw [ite_eq_right hdense] at hslice1
                    simpa only [hp1_nat,
                      show off + wsz - (p.toNat + 1) = off + wsz - p.toNat - 1 by omega] using
                      hslice1,
                  hcb_c, hmg⟩
              · exfalso; rw [hw0_val] at hc; exact hc hbin_eq
            · rename_i hbin0
              rcases hpop_case with ⟨hbin_ne, _⟩ | ⟨_, _, _⟩
              · exfalso; rw [hw0_val] at hbin0; exact hbin_ne hbin0
              · exfalso
                rw [hwvec0_toNat, hwvec1_toNat, Nat.mod_eq_of_lt hbd,
                  show (p.toNat + (1 : BitVec 64).toNat) % 2 ^ 64 = p.toNat + 1 by
                    rw [show (1 : BitVec 64).toNat = 1 by rfl]; exact Nat.mod_eq_of_lt (by omega)]
                  at hc
                omega
            · rename_i hbin0
              rcases hpop_case with ⟨hbin_ne, _⟩ | ⟨hbin_eq, _, cr', hcr_eq, hcr_mem, hslice2⟩
              · exfalso; rw [hw0_val] at hbin0; exact hbin_ne hbin0
              · rw [ite_eq_right hdense] at hslice2
                have hp1_nat : (p + 1).toNat = p.toNat + 1 := by
                  rw [BitVec.toNat_add, show (1 : BitVec 64).toNat = 1 by rfl,
                    Nat.mod_eq_of_lt (by omega)]
                have hp1_wstk : p.toNat + 1 < s.core.wstk.length := by omega
                have hcr_val := copy_condbin_cr_clause hlen hp1_wstk hcr_eq
                have hp2_nat : (p + 2).toNat = p.toNat + 2 := by
                  rw [BitVec.toNat_add, show (2 : BitVec 64).toNat = 2 by rfl,
                    Nat.mod_eq_of_lt (by omega)]
                have hslice2' : DenseWatchSliceOk F_cur s.core lit.toNat (p.toNat + 2)
                    (off + wsz - (p.toNat + 2)) := by
                  simpa only [show off + wsz - p.toNat - 2 = off + wsz - (p.toNat + 2) by omega]
                    using hslice2
                c0_hsteps_nogrp
                refine wp_join_group
                  (fun (cnt', ()) mg' => CopyCondbinClausePost c F_cur s lit.toNat out
                    cap.toNat off wsz p.toNat R cnt'.toNat mg') ?_ (fun Jnp1 hJnp1 => ?_)
                · rintro Jnp1 ⟨cnt', ⟨⟩⟩ mg' ⟨out', hlen', hcn', hsl', hcb', hm'⟩
                  c0_hsteps!
                  exact hJn (p + 2, cnt', ()) mg' ⟨by omega, out', hlen', by omega, by omega,
                    hcn', by simpa only [hp2_nat, show off + wsz - p.toNat - 2 =
                      off + wsz - (p.toNat + 2) by omega] using hsl', hcb', hm'⟩
                · c0_hsteps_nogrp; c0_hsplit
                  · obtain ⟨hcr2_lt, hcr_al, hcr2_al⟩ := copy_condbin_arena_ok hlen hcr_val ⟨_, hc⟩
                    have hcr0_idx : ∀ hw,
                        (s.core.wstk[(p.toNat + (1 : BitVec 64).toNat) % 2 ^ 64]'hw).toNat =
                          cr'.toNat := fun hw => by rw [hcr_val hw]
                    have hcr2_idx : ∀ hw,
                        ((s.core.wstk[(p.toNat + (1 : BitVec 64).toNat) % 2 ^ 64]'hw).toNat +
                          (2 : BitVec 64).toNat) % 2 ^ 64 = cr'.toNat + 2 := fun hw => by
                      rw [hcr_val hw, show (2 : BitVec 64).toNat = 2 by rfl,
                        Nat.mod_eq_of_lt (by omega)]
                    c0_hsteps_nogrp
                    refine wp_join_group
                      (fun (cnt', ()) mg' => CopyCondbinClausePost c F_cur s lit.toNat out
                        cap.toNat off wsz p.toNat R cnt'.toNat mg') ?_ (fun Jnp2 hJnp2 => ?_)
                    · rintro Jnp2 ⟨cnt', ⟨⟩⟩ mg' hpost
                      c0_hsteps!; exact hJnp1 (cnt', ()) mg' hpost
                    · c0_hsteps_nogrp; c0_hsplit
                      · rename_i hgarb_hc hsz3_hc
                        rw [list_getElem_congr (hcr0_idx _) (hj := hcr_al)] at hgarb_hc
                        rw [list_getElem_congr (hcr2_idx _) (hj := hcr2_al)] at hsz3_hc
                        rw [list_getElem_congr (hcr2_idx _) (hj := hcr2_al),
                          show (2 : BitVec 64).toNat = 2 by rfl, hcr0_idx _] at hc
                        have hmask : (524288 ||| 4194304 : BitVec 32) = 4718592#32 := by decide
                        rw [hmask, show (0 : BitVec 32) = 0#32 by rfl] at hgarb_hc
                        have hgarb : fullArenaClauseGarb s cr'.toNat = false :=
                          garb_false_of_and_480000 (by
                            simpa only [fullArenaHdrCore,
                              List.getElem?_eq_getElem hcr_al, Option.getD_some] using hgarb_hc)
                        have hsz3 : 3 ≤ (s.core.arena[cr'.toNat + 2]'hcr2_al).toNat := by
                          simpa only [show (3 : BitVec 32).toNat = 3 by rfl] using hsz3_hc
                        let sz32 := s.core.arena[cr'.toNat + 2]'hcr2_al
                        have hcr_sz_lt : cr'.toNat + 2 + sz32.toNat < s.core.arena_len := by
                          have := sz32.isLt
                          rw [Nat.mod_eq_of_lt (by omega : cr'.toNat + 2 + sz32.toNat < 2 ^ 64),
                            Nat.mod_eq_of_lt (by omega : s.core.arena_len < 2 ^ 64)] at hc
                          exact hc
                        have hsz_core :
                            fullArenaClauseSizeCore s.core cr'.toNat = sz32.toNat := by
                          simp [sz32, fullArenaClauseSizeCore, List.getElem?_eq_getElem hcr2_al]
                        c0_hsteps_nogrp
                        refine wp_join_group
                          (fun (u0, u1, rem, found, ok, _, ()) m_ps => m_ps = mg ∧
                            (ok = true → found = true → rem = 2#32 →
                              u0.toNat < 2 * s.core.cur_vars ∧ u1.toNat < 2 * s.core.cur_vars ∧
                              u0.toNat ≠ lit.toNat ∧ u1.toNat ≠ lit.toNat ∧
                              ∀ l ∈ fullArenaClauseLits s cr'.toNat,
                                s.core.vals[l]?.getD 0#8 = 255#8 ∨
                                  l = lit.toNat ∨ l = u0.toNat ∨ l = u1.toNat))
                          ?_ (fun Jps hJps => ?_)
                        · rintro Jps ⟨u0, u1, rem, found, ok, _, ⟨⟩⟩ m_ps ⟨hm_ps, hps_ok⟩
                          subst m_ps
                          c0_hsteps_nogrp
                          refine wp_join_group
                            (fun (cnt', ()) mg' =>
                              CopyCondbinClausePost c F_cur s lit.toNat out cap.toNat off wsz
                                p.toNat R cnt'.toNat mg')
                            ?_ (fun Jnp3 hJnp3 => ?_)
                          · rintro Jnp3 ⟨cnt', ⟨⟩⟩ mg' hpost
                            c0_hsteps!; exact hJnp2 (cnt', ()) mg' hpost
                          · have hkeep : Jnp3 (cnt, ()) mg := hJnp3 (cnt, ()) mg
                              (copy_condbin_keep hlen_oc hcnt_cap hslice2' hcb_c hmg)
                            c0_hsteps_nogrp
                            c0_hsplit
                            · refine hQ 0#64 out_c mg hlen_oc (Nat.zero_le _)
                                (fun _ _ _ _ hj => by simp at hj)
                                (fun _ h => absurd h (Nat.not_lt_zero _)) hmg
                            · rename_i hok hfd hrem2 hne01_bv hnl0_bv hnl1_bv
                              have hps := hps_ok hok hfd hrem2
                              have hne01 : u0.toNat / 2 ≠ u1.toNat / 2 := by
                                intro he; apply hne01_bv; apply BitVec.eq_of_toNat_eq
                                simpa only [bv32_shr1_nat, bv32_shr1_bv] using he
                              have hnl0 : u0.toNat / 2 ≠ lit.toNat / 2 := by
                                intro he; apply hnl0_bv; apply BitVec.eq_of_toNat_eq
                                simpa only [bv32_shr1_nat, bv32_shr1_bv] using he
                              have hnl1 : u1.toNat / 2 ≠ lit.toNat / 2 := by
                                intro he; apply hnl1_bv; apply BitVec.eq_of_toNat_eq
                                simpa only [bv32_shr1_nat, bv32_shr1_bv] using he
                              have hcnt_lt : cnt.toNat < cap.toNat := by omega
                              c0_hsteps_nogrp
                              refine wp_join_group
                                (fun (hi32, ()) m1 => m1 = mg ∧
                                  (u1.toNat < u0.toNat → hi32 = u1) ∧
                                  (¬ u1.toNat < u0.toNat → hi32 = u0))
                                ?_ (fun Jhi hJhi => ?_)
                              · rintro Jhi ⟨hi32, ⟨⟩⟩ m1 ⟨hm1, hhi_t, hhi_f⟩
                                subst m1
                                c0_hsteps_nogrp
                                refine wp_join_group
                                  (fun (lo32, ()) m2 => m2 = mg ∧
                                    ((hi32 = u0 ∧ lo32 = u1) ∨ (hi32 = u1 ∧ lo32 = u0)))
                                  ?_ (fun Jlo hJlo => ?_)
                                · rintro Jlo ⟨lo32, ⟨⟩⟩ m2 ⟨hm2, hpair⟩
                                  subst m2
                                  have hcb_ok := copy_condbin_emit_ok hps.1 hps.2.1 hnl0 hnl1 hne01
                                    (condBin_perm3 hw hlvl0 hcr_mem hgarb hps.2.2.2.2)
                                    hpair (by omega) hcb_c
                                  have hcnt1_nat : (cnt + 1).toNat = cnt.toNat + 1 := by
                                    rw [BitVec.toNat_add, show (1 : BitVec 64).toNat = 1 by rfl,
                                      Nat.mod_eq_of_lt (by omega)]
                                  c0_hsteps!
                                  have hm' : (FullMemNoWks3 c s ⋆ array64 out (out_c.set cnt.toNat
                                      (hi32.setWidth 64 <<< 32#64 ||| lo32.setWidth 64)) ⋆ R)
                                      m := by
                                    simp only [sep_emp] at hm
                                    rw [← sep_assoc, sep_comm (array64 _ _)] at hm; exact hm
                                  exact hJnp3 (cnt + 1, ()) m
                                    ⟨_, by simp [hlen_oc], by omega, hslice2',
                                      by simpa only [hcnt1_nat] using hcb_ok, hm'⟩
                                · c0_hsteps!; c0_hsplit
                                  · c0_hsteps!
                                    exact hJlo (u0, ()) mg ⟨rfl, Or.inr ⟨hhi_t hc, rfl⟩⟩
                                  · c0_hsteps!
                                    exact hJlo (u1, ()) mg ⟨rfl, Or.inl ⟨hhi_f hc, rfl⟩⟩
                              · c0_hsteps!; c0_hsplit
                                · c0_hsteps!; exact hJhi (u1, ()) mg
                                    ⟨rfl, fun _ => rfl, fun h => absurd hc h⟩
                                · c0_hsteps!; exact hJhi (u0, ()) mg
                                    ⟨rfl, fun h => absurd h hc, fun _ => rfl⟩
                            all_goals exact hkeep
                        · refine wp_loop_inv (ts := [i32, i32, i32, .bool, i32])
                            (fun (u0, u1, rem, found, i, ()) ml =>
                              CopyCondbinScanInv s cr'.toNat lit.toNat sz32.toNat mg
                                u0 u1 rem found i.toNat ml)
                            (fun (_, _, _, _, i, ()) _ => sz32.toNat - i.toNat)
                            (fun Jl hJl => by
                              c0_hsteps!
                              exact hJl (0, 0, 0, false, 0, ()) mg
                                ⟨rfl, Nat.zero_le _, Nat.zero_le _,
                                 fun h => absurd h (by decide), fun h => absurd h (by decide),
                                 fun _ h => absurd h (Nat.not_lt_zero _)⟩)
                            (fun Jl (u0, u1, rem, found, i, ()) ml
                                ⟨hm_eq, hi_sz, hrem_le, hu0, hu1, hprev⟩ ihl => by
                              subst hm_eq
                              c0_hsplit
                              · rw [list_getElem_congr (hcr2_idx _) (hj := hcr2_al)] at hc
                                have hi_lt : i.toNat < sz32.toNat := hc
                                obtain ⟨hl_ar, hl_lt, hl_vals, hcr3i_lt, hv_dom, hv_lt'⟩ :=
                                  copy_condbin_scan_elem_facts hlen hw hcr_mem hgarb hsz_core
                                    hcr_sz_lt hi_lt hp1_nat hp1_wstk hcr_val
                                have hz_eq := copy_condbin_arena_zext_eq hp1_nat hp1_wstk
                                  hcr_val (by omega) hl_ar
                                have hm_eq' := copy_condbin_arena_mod_eq hcr_val hl_ar
                                have hv_eq' := copy_condbin_vals_mod_eq hcr_val hl_ar hl_vals
                                let l32 := s.core.arena[cr'.toNat + 3 + i.toNat]'hl_ar
                                let v8 := s.core.vals[l32.toNat]'hl_vals
                                c0_hsteps_nogrp; c0_hsplit
                                · c0_hsteps!
                                  exact hJps (u0, u1, rem, found, false, i, ()) ml
                                    ⟨rfl, fun h => by cases h⟩
                                · have hi1_nat : (i + 1).toNat = i.toNat + 1 := by
                                    rw [BitVec.toNat_add, show (1 : BitVec 32).toNat = 1 by rfl,
                                      Nat.mod_eq_of_lt (by have := sz32.isLt; omega)]
                                  c0_hsteps_nogrp
                                  refine wp_join_group
                                    (fun (u0', u1', rem', found', _, ()) mn =>
                                      CopyCondbinScanInv s cr'.toNat lit.toNat sz32.toNat ml
                                        u0' u1' rem' found' (i.toNat + 1) mn)
                                    ?_ (fun Jn2 hJn2 => ?_)
                                  · rintro Jn2 ⟨u0', u1', rem', found', _, ⟨⟩⟩ mn inv'
                                    c0_hsteps!
                                    exact ihl (u0', u1', rem', found', i + 1, ()) mn
                                      (by dsimp only; omega) (by simpa only [hi1_nat] using inv')
                                  · c0_hsplit
                                    · have hv0 : v8 = 0#8 := by
                                        rw [hv_eq' _ _ _] at hc
                                        exact bv8_eq0_of_signExtend32 hv_dom hc
                                      c0_hsteps_nogrp
                                      refine wp_join_group
                                        (fun (u0', u1', rem', found', _, ()) mn =>
                                          CopyCondbinScanInv s cr'.toNat lit.toNat sz32.toNat ml
                                            u0' u1' rem' found' (i.toNat + 1) mn)
                                        ?_ (fun Jn3 hJn3 => ?_)
                                      · rintro Jn3 ⟨u0', u1', rem', found', ok', ⟨⟩⟩ mn inv'
                                        c0_hsteps!
                                        exact hJn2 (u0', u1', rem', found', ok', ()) mn inv'
                                      · c0_hsplit
                                        · have hlit_eq : l32 = lit := by rwa [hm_eq' _ _] at hc
                                          c0_hsteps!
                                          refine hJn3 (u0, u1, rem, true, true, ()) ml
                                            (copy_condbin_scan_step hi_lt hl_ar hprev hrem_le hu0
                                              hu1 (fun _ h => by
                                                rcases h with h | ⟨_, h⟩ | h | h
                                                · exact Or.inl h
                                                · exact Or.inr (Or.inl ⟨rfl, h⟩)
                                                · exact Or.inr (Or.inr (Or.inl h))
                                                · exact Or.inr (Or.inr (Or.inr h)))
                                              (Or.inr (Or.inl
                                                ⟨rfl, congrArg BitVec.toNat hlit_eq⟩)))
                                        · have hlit_ne : l32.toNat ≠ lit.toNat := fun he => by
                                            rw [hm_eq' _ _] at hc
                                            exact hc (BitVec.eq_of_toNat_eq he)
                                          c0_hsteps_nogrp
                                          refine wp_join_group
                                            (fun (u0', u1', rem', _, ()) mn =>
                                              CopyCondbinScanInv s cr'.toNat lit.toNat
                                                sz32.toNat ml u0' u1' rem' found
                                                (i.toNat + 1) mn)
                                            ?_ (fun Jn4 hJn4 => ?_)
                                          · rintro Jn4 ⟨u0', u1', rem', ok', ⟨⟩⟩ mn inv'
                                            c0_hsteps!
                                            exact hJn3 (u0', u1', rem', found, ok', ()) mn inv'
                                          · c0_hsplit
                                            · c0_hsteps!; rw [hz_eq _ _]
                                              exact hJn4 (l32, u1, 1, true, ()) ml
                                                (copy_condbin_step_rem0 hi_lt hl_ar hl_lt hlit_ne hc
                                                  hprev)
                                            · rename_i hrem_ne0
                                              c0_hsplit
                                              · c0_hsteps!; rw [hz_eq _ _]
                                                exact hJn4 (u0, l32, 2, true, ()) ml
                                                  (copy_condbin_step_rem1 hi_lt hl_ar hl_lt hlit_ne
                                                    hc hu0 hprev)
                                              · c0_hsteps!
                                                exact hJps (u0, u1, rem, found, false, i, ()) ml
                                                  ⟨rfl, fun h => by cases h⟩
                                    · rename_i hsgt_n
                                      rw [hv_eq' _ _ _] at hsgt_n hc
                                      have hv_ff : v8 = 255#8 := by
                                        refine bv8_ne0_not_signExtend32_sgt0_eqff hv_dom ?_ ?_
                                        · intro h0
                                          dsimp only [v8, l32] at h0
                                          exact hc (by rw [h0]; decide)
                                        · intro h
                                          dsimp only [v8, l32] at h
                                          exact Bool.false_ne_true (hsgt_n.symm.trans h)
                                      c0_hsteps!
                                      refine hJn2 (u0, u1, rem, found, true, ()) ml
                                        (copy_condbin_scan_step hi_lt hl_ar hprev hrem_le hu0 hu1
                                          (fun _ h => h) (Or.inl (by
                                            rw [List.getElem?_eq_getElem hl_vals,
                                              Option.getD_some]; exact hv_ff)))
                              · rw [list_getElem_congr (hcr2_idx _) (hj := hcr2_al)] at hc
                                have hi_eq : i.toNat = sz32.toNat := by
                                  dsimp only [sz32] at *; omega
                                c0_hsteps!
                                refine hJps (u0, u1, rem, found, true, i, ()) ml ⟨rfl, ?_⟩
                                intro _ hfd hrem2
                                refine ⟨(hu0 (by rw [hrem2]; decide)).1,
                                  (hu1 (by rw [hrem2]; rfl)).1,
                                  (hu0 (by rw [hrem2]; decide)).2,
                                  (hu1 (by rw [hrem2]; rfl)).2,
                                  copy_condbin_arena_lits_mem (by rw [hsz_core]; omega)
                                    (by rw [hsz_core, ← hi_eq]; exact hprev) hfd hrem2⟩)
                      · exact hJnp2 (cnt, ()) mg
                          (copy_condbin_keep hlen_oc hcnt_cap hslice2' hcb_c hmg)
                      · exact hJnp2 (cnt, ()) mg
                          (copy_condbin_keep hlen_oc hcnt_cap hslice2' hcb_c hmg)
                      · exact hJnp2 (cnt, ()) mg
                          (copy_condbin_keep hlen_oc hcnt_cap hslice2' hcb_c hmg)
                  · c0_hsteps!
                    exact hJnp1 (cnt, ()) mg (copy_condbin_keep hlen_oc hcnt_cap hslice2' hcb_c hmg)
        · c0_hsteps!
          exact hJ_out (p, cnt, ()) mg ⟨out_c, hlen_oc, hcnt_cap, hcb_c, hmg⟩)

end

end LeanQbe.T.Examples.Kissat.Proof.Congruence
