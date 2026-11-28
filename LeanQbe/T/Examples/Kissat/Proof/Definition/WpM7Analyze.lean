/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Definition.WpM7Basic
public import LeanQbe.T.Examples.Kissat.Proof.Definition.WpM7Prop

/-!
# Kissat M7 K6 Conflict Analysis Preservation Proof (`Proof.Definition.WpM7Analyze`)

Certifies `fullK6AnalyzeM7Spec` for `full_k6_analyze_m7` on flat `CanonicalEnv`, split across
`k6_analyze_copy_append_wp`, `k6_analyze_bt_mtf_wp`, `k6_analyze_jlv_wp`, `k6_analyze_min_wp`,
`k6_analyze_uip_wp`, and `full_k6_analyze_m7_wp`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Definition

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Definition
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Definition.Spec
open Kraken.Bedrock2.Test

open scoped FullArenaTactics FidK6Tactics K6Tactics

public section

/-- Frame preservation of `PropKeep` across `full_k6_mtf_m7`. -/
theorem propKeep_of_mtf {kbuf kb kb' : List (BitVec 32)} (hk : PropKeep kbuf kb)
    (hlen : kb'.length = kb.length)
    (hkeep : ∀ idx < kb.length, idx ≠ 8 → idx ≠ 9 → idx ≠ 10 → idx ≠ 11 →
      (idx < 160 ∨ 352 ≤ idx) → kb'[idx]? = kb[idx]?) :
    PropKeep kbuf kb' := by
  have hb := hk.1.base_ge
  exact propKeep_of_frame hk hlen fun idx hi hor => by
    rcases hor with rfl | rfl | rfl | rfl | rfl | ⟨h1, h2⟩ <;>
      exact hkeep _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

/-- Frame preservation of `PropKeep` across `full_k6_ana_cl_m7`. -/
theorem propKeep_of_ana_cl {kbuf kb kb' : List (BitVec 32)} (hk : PropKeep kbuf kb)
    (hlen : kb'.length = kb.length)
    (hkeep : ∀ idx < kb.length, idx ≠ 16 → idx ≠ 17 → idx ≠ 18 → idx ≠ 20 →
      (idx < 416 ∨ 608 ≤ idx) → (idx < 2784 ∨ 2912 ≤ idx) → kb'[idx]? = kb[idx]?) :
    PropKeep kbuf kb' := by
  have hb := hk.1.base_ge
  exact propKeep_of_frame hk hlen fun idx hi hor => by
    rcases hor with rfl | rfl | rfl | rfl | rfl | ⟨h1, h2⟩ <;>
      exact hkeep _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

/-- Frame preservation of `PropKeep` across `full_k6_backtrack_m7`. -/
theorem propKeep_of_backtrack {kbuf kb kb' : List (BitVec 32)} (hk : PropKeep kbuf kb)
    (hlen : kb'.length = kb.length)
    (hkeep : ∀ idx < kb.length, idx ≠ 3 → idx ≠ 4 → idx ≠ 5 → idx ≠ 6 → idx ≠ 10 →
      (idx < 32 ∨ 160 ≤ idx) → (idx < 608 ∨ 736 ≤ idx) → kb'[idx]? = kb[idx]?) :
    PropKeep kbuf kb' := by
  have hb := hk.1.base_ge
  exact propKeep_of_frame hk hlen fun idx hi hor => by
    rcases hor with rfl | rfl | rfl | rfl | rfl | ⟨h1, h2⟩ <;>
      exact hkeep _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega)

/-- Appending a learned clause in `analyze` preserves `K6BufOk` and all analyze output header
fields (`0`, `2`, `15`, monotonic `1`). -/
theorem analyze_append_k6BufOk {kbuf kb : List (BitVec 32)} (hk : PropKeep kbuf kb)
    {nc_old alen lsz n_ant : BitVec 32}
    (hnc_eq : kb[1]?.getD 0#32 = nc_old) (hnc_lt : nc_old.toNat < 256)
    (hl_le : lsz.toNat ≤ 64) (ha_le : n_ant.toNat ≤ 128)
    (hfit : alen.toNat + lsz.toNat + n_ant.toNat ≤ (kb[15]?.getD 0#32).toNat)
    (hle : kb.length ≥ 2912) :
    let kb1 := kb.set 14 (alen + lsz + n_ant)
    let kb2 := kb1.set (1888 + nc_old.toNat) alen
    let kb3 := kb2.set (2144 + nc_old.toNat) (lsz ||| 0x40000000#32)
    let kb4 := kb3.set (2400 + nc_old.toNat) n_ant
    let kb5 := kb4.set 1 (nc_old + 1#32)
    K6BufOk kb5 ∧ kb5.length = kbuf.length ∧
      kb5[0]? = kbuf[0]? ∧ kb5[2]? = kbuf[2]? ∧ kb5[15]? = kbuf[15]? ∧
      (kbuf[1]?.getD 0#32).toNat ≤ (kb5[1]?.getD 0#32).toNat := by
  intro kb1 kb2 kb3 kb4 kb5
  have hok := hk.1; have hlen := hk.2.1
  have hnc1 : (nc_old + 1#32).toNat = nc_old.toNat + 1 := by
    rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
  have hal_lt : alen.toNat + lsz.toNat + n_ant.toNat < 2 ^ 32 := by
    have := hok.length_ge; have := hok.length_lt; omega
  have hal_add : (alen + lsz + n_ant).toNat = alen.toNat + lsz.toNat + n_ant.toNat := by
    rw [BitVec.toNat_add, BitVec.toNat_add, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have hk15 : kb5[15]? = kb[15]? := by
    dsimp only [kb5, kb4, kb3, kb2, kb1]
    repeat rw [List.getElem?_set_ne (by omega)]
  have hk1 : kb5[1]? = some (nc_old + 1#32) := by
    dsimp only [kb5, kb4, kb3, kb2, kb1]
    apply List.getElem?_set_self; simp [List.length_set]; omega
  have hk14 : kb5[14]? = some (alen + lsz + n_ant) := by
    dsimp only [kb5, kb4, kb3, kb2, kb1]
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
    apply List.getElem?_set_self; omega
  have hk0 : kb5[0]? = kb[0]? := by
    dsimp only [kb5, kb4, kb3, kb2, kb1]; repeat rw [List.getElem?_set_ne (by omega)]
  have hk2 : kb5[2]? = kb[2]? := by
    dsimp only [kb5, kb4, kb3, kb2, kb1]; repeat rw [List.getElem?_set_ne (by omega)]
  have hlen5 : kb5.length = kb.length := by simp [kb5, kb4, kb3, kb2, kb1, List.length_set]
  have hok5 : K6BufOk kb5 := by
    refine K6BufOk.mk_of ?_ ?_ ?_ ?_ ?_
    · rw [hlen5, hk15]; exact hok.length_ge
    · rw [hlen5]; exact hok.length_lt
    · rw [hk1, Option.getD_some, hnc1]; omega
    · rw [hk14, hk15, Option.getD_some, hal_add]; exact hfit
    · intro cid hcid
      rw [hk1, Option.getD_some, hnc1] at hcid
      by_cases hcur : cid = nc_old.toNat
      · subst hcur
        have ho_c : kb5[1888 + nc_old.toNat]? = some alen := by
          dsimp only [kb5, kb4, kb3, kb2, kb1]
          rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
            List.getElem?_set_ne (by omega)]
          apply List.getElem?_set_self; simp [List.length_set]; omega
        have hm_c : kb5[2144 + nc_old.toNat]? = some (lsz ||| 0x40000000#32) := by
          dsimp only [kb5, kb4, kb3, kb2, kb1]
          rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
          apply List.getElem?_set_self; simp [List.length_set]; omega
        have ha_c : kb5[2400 + nc_old.toNat]? = some n_ant := by
          dsimp only [kb5, kb4, kb3, kb2, kb1]
          rw [List.getElem?_set_ne (by omega)]
          apply List.getElem?_set_self; simp [List.length_set]; omega
        have hsz_msk : ((lsz ||| 0x40000000#32) &&& 0xFFFF#32) = lsz := by
          have h65 : ∀ k : Fin 65,
              ((BitVec.ofNat 32 k.1 ||| 0x40000000#32) &&& 0xFFFF#32) = BitVec.ofNat 32 k.1 := by
            decide
          have hlsz : BitVec.ofNat 32 lsz.toNat = lsz := BitVec.eq_of_toNat_eq (by simp)
          simpa [hlsz] using h65 ⟨lsz.toNat, by omega⟩
        rw [ho_c, hm_c, ha_c]
        refine ⟨?_, fun _ => ?_⟩
        · show alen.toNat + ((lsz ||| 0x40000000#32) &&& 0xFFFF#32).toNat ≤
              (kb5[15]?.getD 0#32).toNat
          rw [hsz_msk, hk15]; omega
        · show alen.toNat + ((lsz ||| 0x40000000#32) &&& 0xFFFF#32).toNat + n_ant.toNat ≤
              (kb5[15]?.getD 0#32).toNat
          rw [hsz_msk, hk15]; omega
      · have hcid_lt : cid < (kb[1]?.getD 0#32).toNat := by rw [hnc_eq]; omega
        have ho_c : kb5[1888 + cid]? = kb[1888 + cid]? := by
          dsimp only [kb5, kb4, kb3, kb2, kb1]; repeat rw [List.getElem?_set_ne (by omega)]
        have hm_c : kb5[2144 + cid]? = kb[2144 + cid]? := by
          dsimp only [kb5, kb4, kb3, kb2, kb1]; repeat rw [List.getElem?_set_ne (by omega)]
        have ha_c : kb5[2400 + cid]? = kb[2400 + cid]? := by
          dsimp only [kb5, kb4, kb3, kb2, kb1]; repeat rw [List.getElem?_set_ne (by omega)]
        rw [ho_c, hm_c, ha_c, hk15]; exact hok.clause_ok hcid_lt
  refine ⟨hok5, hlen5.trans hlen, hk0.trans hk.2.2.1, hk2.trans hk.2.2.2.2.1,
    hk15.trans hk.2.2.2.2.2.2.1, ?_⟩
  rw [← hk.2.2.2.1, hnc_eq, hk1, Option.getD_some, hnc1]; omega

/-- Updating an isolated slot outside header `{0, 1, 2, 14, 15}` and clause tables
`[1888, 2656)` preserves `PropKeep`. -/
theorem propKeep_of_set {kbuf kb : List (BitVec 32)} (hk : PropKeep kbuf kb)
    (idx : Nat) (v : BitVec 32) (h0 : idx ≠ 0) (h1 : idx ≠ 1) (h2 : idx ≠ 2)
    (h14 : idx ≠ 14) (h15 : idx ≠ 15) (hmet : idx < 1888 ∨ 2656 ≤ idx) :
    PropKeep kbuf (kb.set idx v) :=
  propKeep_set hk ⟨h0, h1, h2, h14, h15, by omega⟩ v

end

private def AnaPost (kbuf kb : List (BitVec 32)) : Prop :=
  K6BufOk kb ∧ kb.length = kbuf.length ∧ kb[0]? = kbuf[0]? ∧
  kb[2]? = kbuf[2]? ∧ kb[15]? = kbuf[15]? ∧
  (kbuf[1]?.getD 0#32).toNat ≤ (kb[1]?.getD 0#32).toNat

private theorem anaPost_of_watch {kbuf kb kb' : List (BitVec 32)} (hs : AnaPost kbuf kb)
    (hlen : kb'.length = kb.length)
    (hkeep : ∀ idx < kb.length, (idx < 736 ∨ 1888 ≤ idx) → kb'[idx]? = kb[idx]?) :
    AnaPost kbuf kb' := by
  have hb := hs.1.base_ge
  have hok := k6BufOk_of_frame hs.1 hlen fun idx _ hor => by
    rcases hor with rfl | rfl | rfl | ⟨_, _⟩
    · exact hkeep 1 (by omega) (Or.inl (by decide))
    · exact hkeep 14 (by omega) (Or.inl (by decide))
    · exact hkeep 15 (by omega) (Or.inl (by decide))
    · exact hkeep idx (by omega) (Or.inr (by omega))
  refine ⟨hok, hlen.trans hs.2.1, (hkeep 0 (by omega) (Or.inl (by decide))).trans hs.2.2.1,
    (hkeep 2 (by omega) (Or.inl (by decide))).trans hs.2.2.2.1,
    (hkeep 15 (by omega) (Or.inl (by decide))).trans hs.2.2.2.2.1, ?_⟩
  rw [hkeep 1 (by omega) (Or.inl (by decide))]; exact hs.2.2.2.2.2

private theorem anaPost_of_assign {kbuf kb kb' : List (BitVec 32)} (hs : AnaPost kbuf kb)
    (hlen : kb'.length = kb.length)
    (hkeep : ∀ idx < kb.length, idx ≠ 5 → idx ≠ 6 → (idx < 32 ∨ 480 ≤ idx) →
      (idx < 608 ∨ 736 ≤ idx) → kb'[idx]? = kb[idx]?) :
    AnaPost kbuf kb' := by
  have hb := hs.1.base_ge
  have hok := k6BufOk_of_frame hs.1 hlen fun idx _ hor => by
    rcases hor with rfl | rfl | rfl | ⟨_, _⟩
    · exact hkeep 1 (by omega) (by decide) (by decide) (Or.inl (by decide)) (Or.inl (by decide))
    · exact hkeep 14 (by omega) (by decide) (by decide) (Or.inl (by decide)) (Or.inl (by decide))
    · exact hkeep 15 (by omega) (by decide) (by decide) (Or.inl (by decide)) (Or.inl (by decide))
    · exact hkeep idx (by omega) (by omega) (by omega) (Or.inr (by omega)) (Or.inr (by omega))
  have hk0 := hkeep 0 (by omega) (by decide) (by decide) (Or.inl (by decide)) (Or.inl (by decide))
  have hk1 := hkeep 1 (by omega) (by decide) (by decide) (Or.inl (by decide)) (Or.inl (by decide))
  have hk2 := hkeep 2 (by omega) (by decide) (by decide) (Or.inl (by decide)) (Or.inl (by decide))
  have hk15 := hkeep 15 (by omega) (by decide) (by decide) (Or.inl (by decide)) (Or.inl (by decide))
  refine ⟨hok, hlen.trans hs.2.1, hk0.trans hs.2.2.1, hk2.trans hs.2.2.2.1,
    hk15.trans hs.2.2.2.2.1, ?_⟩
  rw [hk1]; exact hs.2.2.2.2.2

private theorem bv64_add2_lt {a b : BitVec 32} (h : a.toNat + b.toNat < 2 ^ 32) :
    (BitVec.setWidth 64 (a + b)).toNat = a.toNat + b.toNat := by
  rw [BitVec.toNat_setWidth, BitVec.toNat_add, Nat.mod_eq_of_lt h,
    Nat.mod_eq_of_lt (Nat.lt_trans h (by decide))]

private def aDflt : (t : Ty) → Val t
  | .bool => false | .bits _ => 0 | .float _ => 0 | .pair a b => (aDflt a, aDflt b)
private def aDfltT : (ts : List Ty) → Tup Val ts
  | [] => () | t :: r => (aDflt t, aDfltT r)

private def aSLd {L rs} (v : BitVec 32) : Expr Val L rs → Expr Val L rs
  | .load (.bits 32) _ k => k v | _ => .hlt
private def aSLt {L rs} : Expr Val L rs → Expr Val L rs
  | .let_ (ts := ts) _ k => k (aDfltT ts) | _ => .hlt
private def aSL2 {L rs} : Expr Val L rs → Expr Val L rs
  | .let_ (ts := t1) _ k1 => match k1 (aDfltT t1) with
    | .let_ (ts := t2) _ k2 => k2 (aDfltT t2) | _ => .hlt
  | _ => .hlt
private def aSL3 {L rs} : Expr Val L rs → Expr Val L rs
  | .let_ (ts := t1) _ k1 => match k1 (aDfltT t1) with
    | .let_ (ts := t2) _ k2 => match k2 (aDfltT t2) with
      | .let_ (ts := t3) _ k3 => k3 (aDfltT t3) | _ => .hlt
    | _ => .hlt
  | _ => .hlt
private def aSLd3 {L rs} (v : BitVec 32) (e : Expr Val L rs) : Expr Val L rs := aSLd v (aSL3 e)
private def aSSt3 {L rs} : Expr Val L rs → Expr Val L rs
  | e => match aSL3 e with | .store _ _ r => r | _ => .hlt
private def aSJF {L rs} : Expr Val L rs → Expr Val L rs | .jnz _ _ e => e | _ => .hlt

private def aSGrpB1 {rs} (x : BitVec 32) : Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 32]]) bs _ =>
      match bs ((fun _ _ => True), ()) with | .cons b _ => b (x, ())
  | _ => .hlt
private def aSGrpK2 {rs} (J : Cont [.bits 32, .bits 32]) : Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 32, .bits 32]]) _ k => k (J, ()) | _ => .hlt
private def aSGrpB2 {rs} (x y : BitVec 32) : Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 32, .bits 32]]) bs _ =>
      match bs ((fun _ _ => True), ()) with | .cons b _ => b (x, y, ())
  | _ => .hlt
private def aSGrpB3 {rs} (x y z : BitVec 32) : Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 32, .bits 32, .bits 32]]) bs _ =>
      match bs ((fun _ _ => True), ()) with | .cons b _ => b (x, y, z, ())
  | _ => .hlt
private def aSGrpBN {rs} : Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[]]) bs _ =>
      match bs ((fun _ _ => True), ()) with | .cons b _ => b ()
  | _ => .hlt

private def aAfterAnaCl (pk : BitVec 64) (cfl nv clvl qh : BitVec 32) :
    Expr Val Cont [.bool] :=
  let e := aSLd3 nv (full_k6_analyze_m7_body Val Cont (pk, cfl, ()))
  let e := aSJF (aSLt e)
  let e := aSSt3 (aSSt3 (aSSt3 (aSSt3 e)))
  match e with
  | .call (bs := []) "full_k6_ana_cl_m7" _ k => aSLd3 qh (aSLd3 clvl (k ()))
  | _ => .hlt

private def aB26Body (pk : BitVec 64) (cfl nv clvl qh b26 : BitVec 32) : Expr Val Cont [.bool] :=
  aSGrpB1 b26 (aAfterAnaCl pk cfl nv clvl qh)

private def aUipGrpE (pk : BitVec 64) (cfl nv clvl qh b26 : BitVec 32)
    (Jq2 : Cont [.bits 32, .bits 32]) : Expr Val Cont [.bool] :=
  aSGrpK2 Jq2 (aB26Body pk cfl nv clvl qh b26)

private def aMinJoinE (pk : BitVec 64) (cfl nv clvl qh b26 uip nana : BitVec 32) :
    Expr Val Cont [.bool] :=
  aSLd3 nana (aSGrpB2 0#32 uip (aB26Body pk cfl nv clvl qh b26))

private def aMinLoopE (pk : BitVec 64) (cfl nv clvl qh b26 uip nana1 nana2 : BitVec 32) :
    Expr Val Cont [.bool] :=
  aSGrpB1 nana2 (aMinJoinE pk cfl nv clvl qh b26 uip nana1)

private def aMinBodyE (pk : BitVec 64) (cfl nv clvl qh b26 uip nana1 nana2 ai : BitVec 32) :
    Expr Val Cont [.bool] :=
  aSGrpB1 ai (aMinLoopE pk cfl nv clvl qh b26 uip nana1 nana2)

private def aJlvGrpE (pk : BitVec 64) (cfl nv clvl qh b26 uip nana1 nana2 nres nkl : BitVec 32) :
    Expr Val Cont [.bool] :=
  let e := aSJF (aSLt (aMinBodyE pk cfl nv clvl qh b26 uip nana1 nana2 0#32))
  let e := aSLd3 nkl (aSLd3 nres e)
  let e := aSJF (aSLt e)
  let e := aSJF (aSL2 e)
  let e := aSJF (aSLt e)
  let e := aSJF (aSLt e)
  let e := aSJF (aSLt e)
  aSSt3 e

private def aSwapGrpE (pk : BitVec 64) (cfl nv clvl qh b26 uip nana1 nana2 nres nkl jlv wi :
    BitVec 32) : Expr Val Cont [.bool] :=
  aSJF (aSLt (aSGrpB3 jlv wi 0#32 (aJlvGrpE pk cfl nv clvl qh b26 uip nana1 nana2 nres nkl)))

private def aMtfGrpE (pk : BitVec 64) (cfl nv clvl qh b26 uip nana1 nana2 nres nkl jlv wi :
    BitVec 32) : Expr Val Cont [.bool] :=
  aSGrpBN (aSwapGrpE pk cfl nv clvl qh b26 uip nana1 nana2 nres nkl jlv wi)

private def aCopy1GrpE (pk : BitVec 64) (cfl nv clvl qh b26 uip nana1 nana2 nres nkl jlv wi
    nc0 alen0 : BitVec 32) : Expr Val Cont [.bool] :=
  let e0 := match aMtfGrpE pk cfl nv clvl qh b26 uip nana1 nana2 nres nkl jlv wi with
    | .call (bs := []) "full_k6_backtrack_m7" _ k => k ()
    | _ => .hlt
  let e := aSJF (aSLt (aSGrpB1 0#32 e0))
  let e := aSJF (aSLt (aSLd3 alen0 (aSLd3 nc0 e)))
  aSJF (aSLt (aSLd3 0#32 (aSL2 e)))

private theorem k6_analyze_copy_append_wp {Γ : Env} (hΓ : Γ.Sat Spec.specs)
    {pk : BitVec 64} {cfl nv clvl qh b26 uip nana1 nana2 nres nkl jlv wi nc0 alen0 : BitVec 32}
    {kbuf kbm : List (BitVec 32)} {acap : BitVec 32} {R : Mem 64 → Prop}
    {Q : Post [.bool]} {X : XPost} {mm : Mem 64}
    (hlen : 2912 ≤ kbuf.length)
    (hQ : ∀ (ok : Bool) (kbuf' : List (BitVec 32)) (m' : Mem 64),
      K6BufOk kbuf' → kbuf'.length = kbuf.length → kbuf'[0]? = kbuf[0]? →
      kbuf'[2]? = kbuf[2]? → kbuf'[15]? = kbuf[15]? →
      (kbuf[1]?.getD 0#32).toNat ≤ (kbuf'[1]?.getD 0#32).toNat →
      (array (t := i32) pk kbuf' ⋆ R) m' → Q (ok, ()) m')
    (hkbm : PropKeep kbuf kbm) (hnc0 : kbm[1]?.getD 0#32 = nc0) (hnc_lt : nc0.toNat < 256)
    (hnres_le : nres.toNat ≤ 128) (hnkl_le : nkl.toNat ≤ 64)
    (hfit : alen0.toNat + nkl.toNat + nres.toNat ≤ acap.toNat)
    (hkbm15 : kbm[15]?.getD 0#32 = acap) (hmm : (array (t := i32) pk kbm ⋆ R) mm) :
    wp Γ Q X (aCopy1GrpE pk cfl nv clvl qh b26 uip nana1 nana2 nres nkl jlv wi nc0 alen0)
      mm := by
  have hbm_ge := hkbm.1.base_ge; have hbm_lt28 := hkbm.1.length_lt
  have hbm_l : 2912 ≤ kbm.length := by rw [hkbm.2.1]; exact hlen
  have hbm_cap : 2912 + acap.toNat ≤ kbm.length := by
    have h := hkbm.1.length_ge; rwa [hkbm15] at h
  dsimp only [aCopy1GrpE, aMtfGrpE, aSwapGrpE, aJlvGrpE, aMinBodyE, aMinLoopE, aMinJoinE,
    aB26Body, aAfterAnaCl, aSGrpBN, aSGrpB3, aSGrpB2, aSGrpB1, aSSt3, aSJF, aSLd3, aSL3, aSL2,
    aSLt, aSLd, aDfltT, aDflt, Prod.fst]
  refine wp_while_state1 (t := i32)
    (fun st : BitVec 32 × List (BitVec 32) => (st.1 : Val i32)) (fun st => nkl.toNat - st.1.toNat)
    (fun (ci, kbc5) mc5 =>
      ci.toNat ≤ nkl.toNat ∧ PropKeep kbuf kbc5 ∧ (array (t := i32) pk kbc5 ⋆ R) mc5) ?_ ?_
  · intro L5 hL5; c0_hsteps!; exact hL5 (0#32, kbm) mm ⟨Nat.zero_le _, hkbm, hmm⟩
  · rintro L5 ⟨ci, kbc5⟩ mc5 ⟨hci_le, hkc5, hmc5⟩ ih5
    have hkc5_l := hkc5.2.1; have hkc5_l2 : 2912 ≤ kbc5.length := by rw [hkc5_l]; exact hlen
    c0_hsplit
    · have hci_lt : ci.toNat < nkl.toNat := hc
      clear hc
      have hlen_c5 : kbc5.length = kbm.length := hkc5_l.trans hkbm.2.1.symm
      have hci1_eq : (ci + 1#32).toNat = ci.toNat + 1 := by have := hci_lt; c0_bound
      have h544_bd : (BitVec.setWidth 64 ((544 : BitVec 32) + ci)).toNat < kbc5.length := by
        have := hci_lt; c0_bound
      have h2912_a : ((2912 : BitVec 32) + alen0).toNat = 2912 + alen0.toNat := by c0_bound
      have hdst_nat : (BitVec.setWidth 64 ((2912 : BitVec 32) + alen0 + ci)).toNat =
          2912 + alen0.toNat + ci.toNat := by rw [bv64_add2_lt (by rw [h2912_a]; omega), h2912_a]
      have hdst_bd : (BitVec.setWidth 64 ((2912 : BitVec 32) + alen0 + ci)).toNat <
          kbc5.length := by rw [hdst_nat]; omega
      c0_hsteps!
      let v5 := kbc5[(BitVec.setWidth 64 ((544 : BitVec 32) + ci)).toNat]'h544_bd
      have hkc5' := propKeep_of_set hkc5
        (BitVec.setWidth 64 ((2912 : BitVec 32) + alen0 + ci)).toNat v5
        (by rw [hdst_nat]; omega) (by rw [hdst_nat]; omega) (by rw [hdst_nat]; omega)
        (by rw [hdst_nat]; omega) (by rw [hdst_nat]; omega) (Or.inr (by rw [hdst_nat]; omega))
      exact ih5 (ci + 1#32, _) m (by dsimp only; rw [hci1_eq]; omega)
        ⟨by rw [hci1_eq]; omega, hkc5', hm⟩
    · clear hc
      refine wp_while_state1 (t := i32)
        (fun st : BitVec 32 × List (BitVec 32) => (st.1 : Val i32))
        (fun st => nres.toNat - st.1.toNat)
        (fun (ri, kbc6) mc6 =>
          ri.toNat ≤ nres.toNat ∧ PropKeep kbuf kbc6 ∧ (array (t := i32) pk kbc6 ⋆ R) mc6) ?_ ?_
      · intro L6 hL6; c0_hsteps!; exact hL6 (0#32, kbc5) mc5 ⟨Nat.zero_le _, hkc5, hmc5⟩
      · rintro L6 ⟨ri, kbc6⟩ mc6 ⟨hri_le, hkc6, hmc6⟩ ih6
        have hkc6_l := hkc6.2.1; have hkc6_l2 : 2912 ≤ kbc6.length := by rw [hkc6_l]; exact hlen
        c0_hsplit
        · have hri_lt : ri.toNat < nres.toNat := hc
          clear hc
          have hlen_c6 : kbc6.length = kbm.length := hkc6_l.trans hkbm.2.1.symm
          have hri1_eq : (ri + 1#32).toNat = ri.toNat + 1 := by have := hri_lt; c0_bound
          have h2784_bd : (BitVec.setWidth 64 ((2784 : BitVec 32) + ri)).toNat < kbc6.length := by
            have := hri_lt; c0_bound
          have h2912_a : ((2912 : BitVec 32) + alen0).toNat = 2912 + alen0.toNat := by c0_bound
          have h2912_b : ((2912 : BitVec 32) + alen0 + nkl).toNat =
              2912 + alen0.toNat + nkl.toNat := by
            rw [BitVec.toNat_add, h2912_a, Nat.mod_eq_of_lt (by omega)]
          have hdst_nat : (BitVec.setWidth 64 ((2912 : BitVec 32) + alen0 + nkl + ri)).toNat =
              2912 + alen0.toNat + nkl.toNat + ri.toNat := by
            rw [bv64_add2_lt (by rw [h2912_b]; omega), h2912_b]
          have hdst_bd : (BitVec.setWidth 64 ((2912 : BitVec 32) + alen0 + nkl + ri)).toNat <
              kbc6.length := by rw [hdst_nat]; omega
          c0_hsteps!
          let v6 := kbc6[(BitVec.setWidth 64 ((2784 : BitVec 32) + ri)).toNat]'h2784_bd
          have hkc6' := propKeep_of_set hkc6
            (BitVec.setWidth 64 ((2912 : BitVec 32) + alen0 + nkl + ri)).toNat v6
            (by rw [hdst_nat]; omega) (by rw [hdst_nat]; omega) (by rw [hdst_nat]; omega)
            (by rw [hdst_nat]; omega) (by rw [hdst_nat]; omega) (Or.inr (by rw [hdst_nat]; omega))
          exact ih6 (ri + 1#32, _) m (by dsimp only; rw [hri1_eq]; omega)
            ⟨by rw [hri1_eq]; omega, hkc6', hm⟩
        · clear hc
          have hk15_c6 : kbc6[15]?.getD 0#32 = acap := by
            rw [hkc6.2.2.2.2.2.2.1, ← hkbm.2.2.2.2.2.2.1]; exact hkbm15
          have hk1_c6 : kbc6[1]?.getD 0#32 = nc0 := by
            rw [hkc6.2.2.2.1, ← hkbm.2.2.2.1]; exact hnc0
          have happ := analyze_append_k6BufOk hkc6 hk1_c6 hnc_lt hnkl_le hnres_le
            (by rw [hk15_c6]; exact hfit) (by omega)
          let kb1 := kbc6.set 14 (alen0 + nkl + nres)
          let kb2 := kb1.set (1888 + nc0.toNat) alen0
          let kb3 := kb2.set (2144 + nc0.toNat) (nkl ||| 1073741824#32)
          let kb4 := kb3.set (2400 + nc0.toNat) nres
          let kb5 := kb4.set 1 (nc0 + 1#32)
          have hs_app : AnaPost kbuf kb5 :=
            ⟨happ.1, happ.2.1, happ.2.2.1, happ.2.2.2.1, happ.2.2.2.2.1, happ.2.2.2.2.2⟩
          have h14_nat : (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 14)).toNat = 14 := rfl
          have h1_nat : (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 1)).toNat = 1 := rfl
          have h1888_nat : (BitVec.setWidth 64 ((1888 : BitVec 32) + nc0)).toNat =
              1888 + nc0.toNat := by c0_bound
          have h2144_nat : (BitVec.setWidth 64 ((2144 : BitVec 32) + nc0)).toNat =
              2144 + nc0.toNat := by c0_bound
          have h2400_nat : (BitVec.setWidth 64 ((2400 : BitVec 32) + nc0)).toNat =
              2400 + nc0.toNat := by c0_bound
          have hlen_kb5 : 2912 ≤ kb5.length := by rw [hs_app.2.1]; exact hlen
          try clear ih5 ih6 hmc5
          c0_hstraight
          c0_hsplit
          · rw [h14_nat, h1_nat, h1888_nat, h2144_nat, h2400_nat] at hm
            c0_hcall (Spec.has_full_k6_assign_m7 hΓ)
            refine fullK6AssignM7Spec_intro hlen_kb5 hm ?_
            intro kbf mf hlenf hkeepf hmf
            have hs_f := anaPost_of_assign hs_app hlenf hkeepf
            c0_hsteps!
            exact hQ true kbf mf hs_f.1 hs_f.2.1 hs_f.2.2.1 hs_f.2.2.2.1
              hs_f.2.2.2.2.1 hs_f.2.2.2.2.2 hmf
          · rw [h14_nat, h1_nat, h1888_nat, h2144_nat, h2400_nat] at hm
            c0_hstraight
            c0_hcall (Spec.has_full_k6_watch_m7 hΓ)
            refine fullK6WatchM7Spec_intro hlen_kb5 hm ?_
            intro kbw mw hlenw hkeepw hmw
            have hs_w := anaPost_of_watch hs_app hlenw hkeepw
            have hlen_kbw : 2912 ≤ kbw.length := by rw [hs_w.2.1]; exact hlen
            c0_hcall (Spec.has_full_k6_assign_m7 hΓ)
            refine fullK6AssignM7Spec_intro hlen_kbw hmw ?_
            intro kbf mf hlenf hkeepf hmf
            have hs_f := anaPost_of_assign hs_w hlenf hkeepf
            c0_hsteps!
            exact hQ true kbf mf hs_f.1 hs_f.2.1 hs_f.2.2.1 hs_f.2.2.2.1
              hs_f.2.2.2.2.1 hs_f.2.2.2.2.2 hmf

private theorem k6_analyze_bt_mtf_wp {Γ : Env} (hΓ : Γ.Sat Spec.specs)
    {pk : BitVec 64} {cfl nv clvl qh b26 uip nana nres nkl jlv wi : BitVec 32}
    {kbuf kbsw : List (BitVec 32)} {acap : BitVec 32} {R : Mem 64 → Prop}
    {Q : Post [.bool]} {X : XPost} {msw : Mem 64}
    (hlen : 2912 ≤ kbuf.length) (hnana_le : nana.toNat ≤ 64)
    (hnres_le : nres.toNat ≤ 128) (hnkl_le : nkl.toNat ≤ 64)
    (hQ : ∀ (ok : Bool) (kbuf' : List (BitVec 32)) (m' : Mem 64),
      K6BufOk kbuf' → kbuf'.length = kbuf.length → kbuf'[0]? = kbuf[0]? →
      kbuf'[2]? = kbuf[2]? → kbuf'[15]? = kbuf[15]? →
      (kbuf[1]?.getD 0#32).toNat ≤ (kbuf'[1]?.getD 0#32).toNat →
      (array (t := i32) pk kbuf' ⋆ R) m' → Q (ok, ()) m')
    (hksw : PropKeep kbuf kbsw) (hbuf15 : kbuf[15]?.getD 0#32 = acap)
    (hmsw : (array (t := i32) pk kbsw ⋆ R) msw) :
    wp Γ Q X (aMtfGrpE pk cfl nv clvl qh b26 uip nana nana nres nkl jlv wi) msw := by
  have hksw_l := hksw.2.1; have hksw_l2 : 2912 ≤ kbsw.length := by rw [hksw_l]; exact hlen
  dsimp only [aMtfGrpE, aSwapGrpE, aJlvGrpE, aMinBodyE, aMinLoopE, aMinJoinE, aB26Body,
    aAfterAnaCl, aSGrpBN, aSGrpB3, aSGrpB2, aSGrpB1, aSSt3, aSJF, aSLd3, aSL3, aSL2, aSLt, aSLd,
    aDfltT, aDflt, Prod.fst]
  c0_hcall (Spec.has_full_k6_backtrack_m7 hΓ)
  refine fullK6BacktrackM7Spec_intro (by omega) hmsw ?_
  intro kbb mbb hlenb hkeepb hmbb
  have hkpb := propKeep_of_backtrack hksw hlenb hkeepb
  have hkpb_l := hkpb.2.1; have hkpb_l2 : 2912 ≤ kbb.length := by rw [hkpb_l]; exact hlen
  refine wp_while_state1 (t := i32)
    (fun st : BitVec 32 × List (BitVec 32) => (st.1 : Val i32)) (fun st => nana.toNat - st.1.toNat)
    (fun (ai, kbm) mm =>
      ai.toNat ≤ nana.toNat ∧ PropKeep kbuf kbm ∧ (array (t := i32) pk kbm ⋆ R) mm) ?_ ?_
  · intro L4 hL4; c0_hsteps!; exact hL4 (0#32, kbb) mbb ⟨Nat.zero_le _, hkpb, hmbb⟩
  · rintro L4 ⟨ai, kbm⟩ mm ⟨hai_le, hkbm, hmm⟩ ih4
    have hkbm_l := hkbm.2.1; have hkbm_l2 : 2912 ≤ kbm.length := by rw [hkbm_l]; exact hlen
    c0_hsplit
    · have hai_lt : ai.toNat < nana.toNat := hc
      clear hc
      have hai1_eq : (ai + 1#32).toNat = ai.toNat + 1 := by have := hai_lt; c0_bound
      have h480_bd : (BitVec.setWidth 64 (480#32 + ai)).toNat < kbm.length := by
        have := hai_lt; c0_bound
      c0_hsteps_nogrp
      c0_hcall (Spec.has_full_k6_mtf_m7 hΓ)
      refine fullK6MtfM7Spec_intro (by omega) hmm ?_
      intro kbm' mm' hlenm hkeepm hmm'
      c0_hsteps!
      exact ih4 (ai + 1#32, kbm') mm' (by dsimp only; rw [hai1_eq]; omega)
        ⟨by rw [hai1_eq]; omega, propKeep_of_mtf hkbm hlenm hkeepm, hmm'⟩
    · clear hc
      have hkbm_ok := hkbm.1
      have hbm_ge := hkbm_ok.base_ge; have hbm_lt28 := hkbm_ok.length_lt
      have hkbm15 : kbm[15]?.getD 0#32 = acap := by rw [hkbm.2.2.2.2.2.2.1]; exact hbuf15
      let nc0 := kbm[(BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 1)).toNat]'(by
        change 1 % 2 ^ 64 < _; omega)
      let alen0 := kbm[(BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 14)).toNat]'(by
        change 14 % 2 ^ 64 < _; omega)
      have hnc0_eq : kbm[1]?.getD 0#32 = nc0 := by
        rw [List.getElem?_eq_getElem (by omega)]; rfl
      have hret_false_m : Q (false, ()) mm :=
        hQ false kbm mm hkbm.1 hkbm.2.1 hkbm.2.2.1 hkbm.2.2.2.2.1 hkbm.2.2.2.2.2.2.1
          (by rw [← hkbm.2.2.2.1]; exact Nat.le_refl _) hmm
      c0_hsplit
      · c0_hsteps!; exact hret_false_m
      · have hnc_lt256 : nc0.toNat < 256 := by
          have hnot : ¬(256#32 : BitVec 32).toNat ≤ nc0.toNat := hc
          exact Nat.lt_of_not_le (by simpa using hnot)
        clear hc
        c0_hsplit
        · c0_hsteps!; exact hret_false_m
        · have hfit : alen0.toNat + nkl.toNat + nres.toNat ≤ acap.toNat := by
            have h14e : kbm[OfNat.ofNat 14 % 18446744073709551616]'(by
                change 14 % 2 ^ 64 < _; omega) = alen0 := rfl
            have h15e : kbm[OfNat.ofNat 15 % 18446744073709551616]'(by
                change 15 % 2 ^ 64 < _; omega) = acap := by
              rw [← hkbm15, show kbm[15]? = some (kbm[15]'(by omega)) from
                List.getElem?_eq_getElem (by omega)]
              rfl
            have hle : (alen0.toNat + nkl.toNat + nres.toNat) % 2 ^ 32 ≤ acap.toNat := by
              rw [← h14e, ← h15e]; simpa [BitVec.toNat_add] using hc
            have halen_le : alen0.toNat ≤ acap.toNat := by
              have h := hkbm_ok.alen_le
              rw [show kbm[14]?.getD 0#32 = alen0 from by
                  rw [List.getElem?_eq_getElem (by omega)]; rfl,
                hkbm15] at h
              exact h
            have hbm_cap : 2912 + acap.toNat ≤ kbm.length := by
              have h := hkbm_ok.length_ge; rwa [hkbm15] at h
            rw [Nat.mod_eq_of_lt (by omega)] at hle; exact hle
          clear hc
          have h_ca := k6_analyze_copy_append_wp hΓ (pk := pk) (cfl := cfl) (nv := nv)
            (clvl := clvl) (qh := qh) (b26 := b26) (uip := uip) (nana1 := nana) (nana2 := nana)
            (nres := nres) (nkl := nkl) (jlv := jlv) (wi := wi) (nc0 := nc0) (alen0 := alen0)
            (kbuf := kbuf) (kbm := kbm) (acap := acap) (R := R) (Q := Q) (X := X) (mm := mm)
            hlen hQ hkbm hnc0_eq hnc_lt256 hnres_le hnkl_le hfit hkbm15 hmm
          dsimp only [aCopy1GrpE, aMtfGrpE, aSwapGrpE, aJlvGrpE, aMinBodyE, aMinLoopE, aMinJoinE,
            aB26Body, aAfterAnaCl, aSGrpBN, aSGrpB3, aSGrpB2, aSGrpB1, aSSt3, aSJF, aSLd3, aSL3,
            aSL2, aSLt, aSLd, aDfltT, aDflt, Prod.fst] at h_ca
          exact h_ca

private theorem k6_analyze_jlv_wp {Γ : Env} (hΓ : Γ.Sat Spec.specs)
    {pk : BitVec 64} {cfl nv clvl qh b26 uip nana nres nkl : BitVec 32}
    {kbuf kbd : List (BitVec 32)} {acap : BitVec 32} {R : Mem 64 → Prop}
    {Q : Post [.bool]} {X : XPost} {md : Mem 64}
    (hlen : 2912 ≤ kbuf.length) (hnv_le : nv.toNat ≤ 64) (hnana_le : nana.toNat ≤ 64)
    (hnres_le : nres.toNat ≤ 128) (hnkl_pos : 0 < nkl.toNat) (hnkl_le : nkl.toNat ≤ 64)
    (hQ : ∀ (ok : Bool) (kbuf' : List (BitVec 32)) (m' : Mem 64),
      K6BufOk kbuf' → kbuf'.length = kbuf.length → kbuf'[0]? = kbuf[0]? →
      kbuf'[2]? = kbuf[2]? → kbuf'[15]? = kbuf[15]? →
      (kbuf[1]?.getD 0#32).toNat ≤ (kbuf'[1]?.getD 0#32).toNat →
      (array (t := i32) pk kbuf' ⋆ R) m' → Q (ok, ()) m')
    (hpk_kl0 : PropKeep kbuf (kbd.set 544 uip)) (hnv0 : kbuf[0]?.getD 0#32 = nv)
    (hbuf15 : kbuf[15]?.getD 0#32 = acap)
    (hm : (array (t := i32) pk (kbd.set 544 uip) ⋆ R) md) :
    wp Γ Q X (aJlvGrpE pk cfl nv clvl qh b26 uip nana nana nres nkl) md := by
  have hkl0_len : 2912 ≤ (kbd.set 544 uip).length := by rw [hpk_kl0.2.1]; exact hlen
  dsimp only [aJlvGrpE, aMinBodyE, aMinLoopE, aMinJoinE, aB26Body, aAfterAnaCl, aSGrpB2, aSGrpB1,
    aSSt3, aSJF, aSLd3, aSL3, aSL2, aSLt, aSLd, aDfltT, aDflt, Prod.fst]
  refine wp_while_state_pure (ts := [i32, i32, i32])
    (fun st : BitVec 32 × BitVec 32 × BitVec 32 => (st.1, st.2.1, st.2.2, ()))
    (fun st => nkl.toNat - st.2.2.toNat)
    (fun (_, wi, i) => 1 ≤ wi.toNat ∧ wi.toNat ≤ 64 ∧
      (wi.toNat < nkl.toNat ∨ (nkl.toNat = 1 ∧ wi = 1#32)) ∧
      1 ≤ i.toNat ∧ i.toNat ≤ nkl.toNat) ?_ ?_
  · intro L3 hL3; c0_hsteps!
    have hw_disj : (1 : Nat) < nkl.toNat ∨ (nkl.toNat = 1 ∧ (1#32 : BitVec 32) = 1#32) := by
      rcases Nat.eq_or_lt_of_le hnkl_pos with h1 | hgt
      · exact Or.inr ⟨h1.symm, rfl⟩
      · exact Or.inl hgt
    exact hL3 (0#32, 1#32, 1#32) ⟨by decide, by decide, hw_disj, by decide, hnkl_pos⟩
  · rintro L3 ⟨jlvl, wi, i⟩ ⟨hwi_ge, hwi_64, hwi_disj, hi_ge, hi_le⟩ ih3
    c0_hsplit
    · have hi_lt : i.toNat < nkl.toNat := hc
      clear hc
      have h544_bd : (BitVec.setWidth 64 (544#32 + i)).toNat < (kbd.set 544 uip).length := by
        have := hi_lt; c0_bound
      have hi1_eq : (i + 1#32).toNat = i.toNat + 1 := by have := hi_lt; c0_bound
      c0_hsteps_nogrp
      refine wp_join_state_pure (ts := [i32, i32]) (α := BitVec 32 × BitVec 32)
        (fun st => (st.1, st.2, ())) (fun (_, w') => 1 ≤ w'.toNat ∧ w'.toNat ≤ 64 ∧
          (w'.toNat < nkl.toNat ∨ (nkl.toNat = 1 ∧ w' = 1#32)))
        (fun _ (j', w') hgw => by
          c0_hsteps!
          exact ih3 (j', w', i + 1#32) (by dsimp only; rw [hi1_eq]; omega)
            ⟨hgw.1, hgw.2.1, hgw.2.2, by rw [hi1_eq]; omega, by rw [hi1_eq]; omega⟩)
        (fun _ hJ3a => by
          c0_hsplit
          · let kl := (kbd.set 544 uip)[(BitVec.setWidth 64 (544#32 + i)).toNat]'h544_bd
            have h544_nat : (BitVec.setWidth 64 (544#32 + i)).toNat = 544 + i.toNat := by
              have := hi_lt; c0_bound
            have h544_mod : (BitVec.toNat (544 : BitVec 32) + i.toNat) % 2 ^ 32 =
                544 + i.toNat := by
              have h544n : BitVec.toNat (544 : BitVec 32) = 544 := rfl
              rw [h544n]; exact Nat.mod_eq_of_lt (by omega)
            have hkl_c0 : (kbd.set 544 uip)[(BitVec.toNat (544 : BitVec 32) + i.toNat) % 2 ^ 32]'(by
                rw [h544_mod, ← h544_nat]; exact h544_bd) = kl :=
              m8_k6_get_congr (by rw [h544_mod, h544_nat]) _ _
            let kv := kl >>> (1 : Nat)
            have hkv_bd : kv.toNat < nv.toNat := by
              dsimp only [kv]; rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, ← hkl_c0]
              simpa [hnv0, Nat.reducePow] using hc
            clear hc
            have h32_bd : (BitVec.setWidth 64 (32#32 + kv)).toNat < (kbd.set 544 uip).length := by
              have := hkv_bd; c0_bound
            c0_hsteps_nogrp
            refine wp_join_state_pure (ts := [i32, i32]) (α := BitVec 32 × BitVec 32)
              (fun st => (st.1, st.2, ())) (fun (_, w') => 1 ≤ w'.toNat ∧ w'.toNat ≤ 64 ∧
                (w'.toNat < nkl.toNat ∨ (nkl.toNat = 1 ∧ w' = 1#32)))
              (fun _ (j', w') hgw => by c0_hsteps!; exact hJ3a (j', w') hgw)
              (fun _ hJ3b => by
                c0_hsplit
                · c0_hsteps!; exact hJ3b (_, i) ⟨hi_ge, by omega, Or.inl hi_lt⟩
                · c0_hsteps!; exact hJ3b (jlvl, wi) ⟨hwi_ge, hwi_64, hwi_disj⟩)
          · clear hc; c0_hsteps!; exact hJ3a (jlvl, wi) ⟨hwi_ge, hwi_64, hwi_disj⟩)
    · clear hc
      refine wp_join0 (fun msw => ∃ kbsw, PropKeep kbuf kbsw ∧ (array (t := i32) pk kbsw ⋆ R) msw)
          ?_ ?_
      · intro _ msw ⟨kbsw, hksw, hmsw⟩
        exact k6_analyze_bt_mtf_wp hΓ (pk := pk) (cfl := cfl) (nv := nv) (clvl := clvl)
          (qh := qh) (b26 := b26) (uip := uip) (nana := nana) (nres := nres) (nkl := nkl)
          (jlv := jlvl) (wi := wi) (kbuf := kbuf) (kbsw := kbsw) (acap := acap) (R := R) (Q := Q)
          (X := X) (msw := msw) hlen hnana_le hnres_le hnkl_le hQ hksw hbuf15 hmsw
      · intro Jsw hJsw
        c0_hsplit
        · c0_hsplit
          · have h545_add : (BitVec.setWidth 64 ((544 : BitVec 32) + 1)).toNat = 545 := rfl
            have h545_bd : 545 < (kbd.set 544 uip).length := by omega
            have h544w_nat : (BitVec.setWidth 64 ((544 : BitVec 32) + wi)).toNat =
                544 + wi.toNat := by c0_bound
            have h544w_bd : (BitVec.setWidth 64 ((544 : BitVec 32) + wi)).toNat <
                (kbd.set 544 uip).length := by rw [h544w_nat]; omega
            let wlit := (kbd.set 544 uip)[(BitVec.setWidth 64
              ((544 : BitVec 32) + wi)).toNat]'h544w_bd
            let tlit := (kbd.set 544 uip)[545]'h545_bd
            have hpk_s1 := propKeep_of_set hpk_kl0 545 wlit (by decide) (by decide) (by decide)
              (by decide) (by decide) (Or.inl (by decide))
            have hs1_len : 2912 ≤ ((kbd.set 544 uip).set 545 wlit).length := by
              rw [hpk_s1.2.1]; exact hlen
            c0_hsteps_nogrp
            have h545_val : ∀ h, (kbd.set 544 uip)[(BitVec.setWidth 64
                ((544 : BitVec 32) + 1)).toNat]'h = tlit := fun _ => by simp only [tlit, h545_add]
            rw [h545_val, h545_add] at hm
            have hpk_s2 := propKeep_of_set hpk_s1 (544 + wi.toNat) tlit (by omega) (by omega)
              (by omega) (by omega) (by omega) (Or.inl (by omega))
            rw [← h544w_nat] at hpk_s2
            exact hJsw m ⟨_, hpk_s2, hm⟩
          · c0_hsteps!; exact hJsw _ ⟨_, hpk_kl0, hm⟩
        · c0_hsteps!; exact hJsw _ ⟨_, hpk_kl0, hm⟩

private theorem k6_analyze_min_wp {Γ : Env} (hΓ : Γ.Sat Spec.specs)
    {pk : BitVec 64} {cfl nv clvl qh b26 uip : BitVec 32} {kbuf kbb : List (BitVec 32)}
    {acap : BitVec 32} {R : Mem 64 → Prop} {Q : Post [.bool]} {X : XPost} {mb : Mem 64}
    (hlen : 2912 ≤ kbuf.length) (hnv_le : nv.toNat ≤ 64)
    (hQ : ∀ (ok : Bool) (kbuf' : List (BitVec 32)) (m' : Mem 64),
      K6BufOk kbuf' → kbuf'.length = kbuf.length → kbuf'[0]? = kbuf[0]? →
      kbuf'[2]? = kbuf[2]? → kbuf'[15]? = kbuf[15]? →
      (kbuf[1]?.getD 0#32).toNat ≤ (kbuf'[1]?.getD 0#32).toNat →
      (array (t := i32) pk kbuf' ⋆ R) m' → Q (ok, ()) m')
    (hkb : PropKeep kbuf kbb) (hnv0 : kbuf[0]?.getD 0#32 = nv)
    (hbuf15 : kbuf[15]?.getD 0#32 = acap) (hmb : (array (t := i32) pk kbb ⋆ R) mb) :
    wp Γ Q X (aSGrpB2 0#32 uip (aB26Body pk cfl nv clvl qh b26)) mb := by
  have hkb_l := hkb.2.1; have hkb_l2 : 2912 ≤ kbb.length := by rw [hkb_l]; exact hlen
  dsimp only [aB26Body, aAfterAnaCl, aSGrpB2, aSGrpB1, aSSt3, aSJF, aSLd3, aSL3, aSLt, aSLd,
    aDfltT, aDflt, Prod.fst]
  c0_hsteps_nogrp
  refine wp_join_state1 (t := i32) (fun st : BitVec 32 × List (BitVec 32) => (st.1 : Val i32))
    (fun (nana, kb) mn => PropKeep kbuf kb ∧ nana.toNat ≤ 64 ∧ (array (t := i32) pk kb ⋆ R) mn)
    ?_ ?_
  · rintro _ ⟨nana, kbc⟩ mc ⟨hkc, hnana_le, hmc⟩
    refine wp_while_state1 (t := i32) (fun st : BitVec 32 × List (BitVec 32) => (st.1 : Val i32))
      (fun st => nana.toNat - st.1.toNat)
      (fun (ai, kb) mi => ai.toNat ≤ nana.toNat ∧ PropKeep kbuf kb ∧
          (array (t := i32) pk kb ⋆ R) mi)
      ?_ ?_
    · intro L2 hL2; c0_hsteps!; exact hL2 (0#32, kbc) mc ⟨Nat.zero_le _, hkc, hmc⟩
    · rintro _ ⟨ai, kbd⟩ md ⟨hai_le, hkd, hmd⟩ ih2
      have hkd_l := hkd.2.1; have hkd_l2 : 2912 ≤ kbd.length := by rw [hkd_l]; exact hlen
      have hret_false : Q (false, ()) md :=
        hQ false kbd md hkd.1 hkd.2.1 hkd.2.2.1 hkd.2.2.2.2.1 hkd.2.2.2.2.2.2.1
          (by rw [← hkd.2.2.2.1]; exact Nat.le_refl _) hmd
      c0_hsteps_nogrp
      · have hai_lt : ai.toNat < nana.toNat := hc
        have hai1_eq : (ai + 1#32).toNat = ai.toNat + 1 := by have := hai_lt; c0_bound
        have h480_bd : (BitVec.setWidth 64 (480#32 + ai)).toNat < kbd.length := by
          have := hai_lt; c0_bound
        refine wp_join0 (fun mj => ∃ kbj, PropKeep kbuf kbj ∧ (array (t := i32) pk kbj ⋆ R) mj)
            ?_ ?_
        · intro _ mj ⟨kbj, hkj, hmj⟩
          c0_hsteps!
          exact ih2 (ai + 1#32, kbj) mj (by dsimp only; rw [hai1_eq]; omega)
            ⟨by rw [hai1_eq]; omega, hkj, hmj⟩
        · intro _ hJ2
          c0_hsplit
          · let av := kbd[(BitVec.setWidth 64 (480#32 + ai)).toNat]'h480_bd
            have h480_nat : (BitVec.setWidth 64 (480#32 + ai)).toNat = 480 + ai.toNat := by
              have := hai_lt; c0_bound
            have h480_mod : (BitVec.toNat (480 : BitVec 32) + ai.toNat) % 2 ^ 32 =
                480 + ai.toNat := by
              have h480n : BitVec.toNat (480 : BitVec 32) = 480 := rfl
              rw [h480n]; exact Nat.mod_eq_of_lt (by omega)
            have hav_c0 : kbd[(BitVec.toNat (480 : BitVec 32) + ai.toNat) % 2 ^ 32]'(by
                rw [h480_mod, ← h480_nat]; exact h480_bd) = av :=
              m8_k6_get_congr (by rw [h480_mod, h480_nat]) _ _
            have hav_lt : av.toNat < nv.toNat := by rw [← hav_c0]; simpa [hnv0] using hc
            clear hc
            have h416_nat : (BitVec.setWidth 64 (416#32 + av)).toNat = 416 + av.toNat := by
              have := hav_lt; c0_bound
            have h416_bd : (BitVec.setWidth 64 (416#32 + av)).toNat < kbd.length := by
              rw [h416_nat]; omega
            c0_hsteps!
            exact hJ2 m ⟨_, propKeep_of_set hkd (BitVec.setWidth 64 (416#32 + av)).toNat _
              (by rw [h416_nat]; omega) (by rw [h416_nat]; omega) (by rw [h416_nat]; omega)
              (by rw [h416_nat]; omega) (by rw [h416_nat]; omega)
              (Or.inl (by rw [h416_nat]; omega)), hm⟩
          · clear hc; c0_hsteps!; exact hJ2 md ⟨kbd, hkd, hmd⟩
      · exact hret_false
      · exact hret_false
      · exact hret_false
      · exact hret_false
      · exact hret_false
      · let nres := kbd[(BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 18)).toNat]'(by
          change 18 % 2 ^ 64 < _; omega)
        let nkl := kbd[(BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 17)).toNat]'(by
          change 17 % 2 ^ 64 < _; omega)
        have hnres_le : nres.toNat ≤ 128 := by
          have hnot : ¬BitVec.toNat (128 : BitVec 32) < nres.toNat := by assumption
          exact Nat.le_of_not_lt hnot
        have hnkl_pos : 0 < nkl.toNat := by
          have hnot : ¬nkl = 0 := by assumption
          exact Nat.pos_of_ne_zero fun h => hnot (BitVec.eq_of_toNat_eq (by simpa using h))
        have hnkl_le : nkl.toNat ≤ 64 := by
          have hnot : ¬BitVec.toNat (64 : BitVec 32) < nkl.toNat := by assumption
          exact Nat.le_of_not_lt hnot
        have h544_nat : (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 544)).toNat = 544 := rfl
        rw [h544_nat] at hm
        have hpk_kl0 := propKeep_of_set hkd 544 uip (by decide) (by decide) (by decide)
          (by decide) (by decide) (Or.inl (by decide))
        have h_jlv := k6_analyze_jlv_wp hΓ (pk := pk) (cfl := cfl) (nv := nv) (clvl := clvl)
          (qh := qh) (b26 := b26) (uip := uip) (nana := nana) (nres := nres) (nkl := nkl)
          (kbuf := kbuf) (kbd := kbd) (acap := acap) (R := R) (Q := Q) (X := X) (md := m)
          hlen hnv_le hnana_le hnres_le hnkl_pos hnkl_le hQ hpk_kl0 hnv0 hbuf15 hm
        dsimp only [aJlvGrpE, aMinBodyE, aMinLoopE, aMinJoinE, aB26Body, aAfterAnaCl, aSGrpB2,
          aSGrpB1, aSSt3, aSJF, aSLd3, aSL3, aSL2, aSLt, aSLd, aDfltT, aDflt, Prod.fst] at h_jlv
        exact h_jlv
  · intro Jn hJn
    c0_hsplit
    · c0_hsteps!; exact hJn (64#32, kbb) mb ⟨hkb, by decide, hmb⟩
    · c0_hsteps!
      have hk16_le : (kbb[(BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 16)).toNat]'(by
          change 16 % 2 ^ 64 < _; omega)).toNat ≤ 64 := by
        exact Nat.le_of_not_lt hc
      exact hJn (kbb[(BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 16)).toNat]'(by
        change 16 % 2 ^ 64 < _; omega), kbb) mb ⟨hkb, hk16_le, hmb⟩

private def aUipBodyE (pk : BitVec 64) (cfl nv clvl qh idx0 : BitVec 32)
    (B : Cont [.bits 32, .bits 32]) (L : Cont [.bits 32]) (idx : BitVec 32) :
    Expr Val Cont [.bool] :=
  match aUipGrpE pk cfl nv clvl qh idx0 B with
  | .group (sig := [[.bits 32]]) bs _ => match bs (L, ()) with | .cons b _ => b (idx, ())
  | _ => .hlt

private theorem k6_analyze_uip_step_wp {Γ : Env} (hΓ : Γ.Sat Spec.specs)
    {pk : BitVec 64} {cfl nv clvl qh idx0 idx : BitVec 32}
    {kbuf kbi : List (BitVec 32)} {R : Mem 64 → Prop} {Q : Post [.bool]} {X : XPost}
    {mi : Mem 64} {B : Cont [.bits 32, .bits 32]} {L : Cont [.bits 32]}
    (hlen : 2912 ≤ kbuf.length) (hnv_le : nv.toNat ≤ 64) (hidx_le : idx.toNat ≤ 64)
    (hnv0 : kbuf[0]?.getD 0#32 = nv) (hki : PropKeep kbuf kbi)
    (hmi : (array (t := i32) pk kbi ⋆ R) mi)
    (hB : ∀ bst : BitVec 32 × BitVec 32 × List (BitVec 32), ∀ m',
      PropKeep kbuf bst.2.2 → (array (t := i32) pk bst.2.2 ⋆ R) m' → B (bst.1, bst.2.1, ()) m')
    (ih1 : ∀ idx' kbi' m', idx'.toNat < idx.toNat →
      PropKeep kbuf kbi' → idx'.toNat ≤ 64 → (array (t := i32) pk kbi' ⋆ R) m' →
      L (idx', ()) m') :
    wp Γ Q X (aUipBodyE pk cfl nv clvl qh idx0 B L idx) mi := by
  have hki_l := hki.2.1; have hki_l2 : 2912 ≤ kbi.length := by rw [hki_l]; exact hlen
  dsimp only [aUipBodyE, aUipGrpE, aB26Body, aAfterAnaCl, aSGrpK2, aSGrpB1, aSSt3, aSJF, aSLd3,
    aSL3, aSLt, aSLd, aDfltT, aDflt, Prod.fst]
  c0_hsplit
  · clear hc
    c0_hsplit
    · c0_hsteps!; exact hB (idx, 0xFFFFFFFF#32, kbi) mi hki hmi
    · have hidx_pos : 0 < idx.toNat :=
        Nat.pos_of_ne_zero fun h => hc (BitVec.eq_of_toNat_eq (by simpa using h))
      clear hc
      have hidx1_eq : (idx - 1#32).toNat = idx.toNat - 1 := m8_bv32_sub1_toNat hidx_pos
      have h352_bd : (BitVec.setWidth 64 (352#32 + (idx - 1#32))).toNat < kbi.length := by
        have : (idx - 1#32).toNat < 64 := by omega
        c0_bound
      c0_hsteps_nogrp
      let p := kbi[(BitVec.setWidth 64 (352#32 + (idx - 1#32))).toNat]'h352_bd
      let pv := p >>> (1 : Nat)
      refine wp_join_group (fun _ mj => ∃ kbj, PropKeep kbuf kbj ∧ (array (t := i32) pk kbj ⋆ R) mj)
          ?_ ?_
      · rintro _ _ mj ⟨kbj, hkj, hmj⟩
        c0_hsteps!; exact ih1 (idx - 1#32) kbj mj (by rw [hidx1_eq]; omega) hkj (by omega) hmj
      · intro J1 hJ1
        c0_hsplit
        · have h352_nat : (BitVec.setWidth 64 (352#32 + (idx - 1#32))).toNat =
              352 + (idx - 1#32).toNat := by
            have : (idx - 1#32).toNat < 64 := by omega
            c0_bound
          have h352_mod : (BitVec.toNat (352 : BitVec 32) + (2 ^ 32 - BitVec.toNat (1 : BitVec 32) +
              idx.toNat)) % 2 ^ 32 = 352 + (idx - 1#32).toNat := by
            have h352n : BitVec.toNat (352 : BitVec 32) = 352 := rfl
            have h1n : BitVec.toNat (1 : BitVec 32) = 1 := rfl
            rw [h352n, h1n, hidx1_eq]; omega
          have hp_c0 : kbi[(BitVec.toNat (352 : BitVec 32) + (2 ^ 32 -
              BitVec.toNat (1 : BitVec 32) + idx.toNat)) % 2 ^ 32]'(by
                rw [h352_mod, ← h352_nat]; exact h352_bd) = p :=
            m8_k6_get_congr (by rw [h352_mod, h352_nat]) _ _
          have hpv_lt : pv.toNat < nv.toNat := by
            dsimp only [pv]; rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, ← hp_c0]
            simpa [hnv0, Nat.reducePow] using hc
          clear hc
          have h416_bd : (BitVec.setWidth 64 (416#32 + pv)).toNat < kbi.length := by
            have := hpv_lt; c0_bound
          c0_hsplit
          · clear hc
            have h32_bd : (BitVec.setWidth 64 (32#32 + pv)).toNat < kbi.length := by
              have := hpv_lt; c0_bound
            c0_hsplit
            · clear hc
              have h20n : (BitVec.ofNat 64 20).toNat = 20 := rfl
              have h20_bd : (BitVec.ofNat 64 20).toNat < kbi.length := by rw [h20n]; omega
              let decv := kbi[(BitVec.ofNat 64 20).toNat]'h20_bd - 1#32
              have hkbi20_len : 2912 ≤ (kbi.set (BitVec.ofNat 64 20).toNat decv).length := by
                rw [List.length_set]; exact hki_l2
              have hpk_dec := propKeep_of_set hki (BitVec.ofNat 64 20).toNat decv
                (by rw [h20n]; decide) (by rw [h20n]; decide) (by rw [h20n]; decide)
                (by rw [h20n]; decide) (by rw [h20n]; decide) (Or.inl (by rw [h20n]; decide))
              c0_hsplit
              · c0_hsteps!; exact hB (idx - 1#32, p ^^^ 1#32, _) m hpk_dec hm
              · clear hc
                have h96_bd : (BitVec.setWidth 64 (96#32 + pv)).toNat <
                    (kbi.set (BitVec.ofNat 64 20).toNat decv).length := by
                  have := hpv_lt; c0_bound
                c0_hsplit
                · c0_hsteps!; exact hB (idx - 1#32, p ^^^ 1#32, _) m hpk_dec hm
                · clear hc
                  c0_hcall (Spec.has_full_k6_ana_cl_m7 hΓ)
                  refine fullK6AnaClM7Spec_intro hpk_dec.1 hm ?_
                  intro kba ma hlena hkeepa hma
                  c0_hsteps!; exact hJ1 _ ma ⟨kba, propKeep_of_ana_cl hpk_dec hlena hkeepa, hma⟩
            · clear hc; c0_hsteps!; exact hJ1 _ mi ⟨kbi, hki, hmi⟩
          · clear hc; c0_hsteps!; exact hJ1 _ mi ⟨kbi, hki, hmi⟩
        · clear hc; c0_hsteps!; exact hJ1 _ mi ⟨kbi, hki, hmi⟩
  · clear hc; c0_hsteps!; exact hB (idx, 0xFFFFFFFF#32, kbi) mi hki hmi

public section

/-- Certifies `fullK6AnalyzeM7Spec` for `full_k6_analyze_m7` on flat `CanonicalEnv`. -/
theorem full_k6_analyze_m7_wp (Γ : Env) (hΓ : Γ.Sat Spec.specs) :
    ∀ a m Q X, fullK6AnalyzeM7Spec a m Q X → Func.wp Γ full_k6_analyze_m7_body a m Q X := by
  rintro ⟨pk, cfl, ⟨⟩⟩ m0 Q X hSpec
  obtain ⟨kbuf, R, hok0, hm0, hQ⟩ := fullK6AnalyzeM7Spec_elim hSpec
  have hlen := hok0.base_ge; have hlt28 := hok0.length_lt
  let nv : BitVec 32 := kbuf[(BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 0)).toNat]'(by
    change 0 % 2 ^ 64 < _; omega)
  have hnv0 : kbuf[0]?.getD 0#32 = nv := by rw [List.getElem?_eq_getElem (by omega)]; rfl
  let acap : BitVec 32 := kbuf[15]'(by omega)
  have hbuf15 : kbuf[15]?.getD 0#32 = acap := by rw [List.getElem?_eq_getElem (by omega)]; rfl
  unfold Func.wp full_k6_analyze_m7_body
  c0_hsplit
  · c0_hsteps!; exact hQ false kbuf m0 hok0 rfl rfl rfl rfl (Nat.le_refl _) hm0
  · have hnv_le : nv.toNat ≤ 64 := Nat.le_of_not_lt (by simpa [nv] using hc)
    clear hc
    have h17 : (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 17)).toNat = 17 := rfl
    have h16 : (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 16)).toNat = 16 := rfl
    have h18 : (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 18)).toNat = 18 := rfl
    have h20 : (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 20)).toNat = 20 := rfl
    have hpk0 := propKeep_of_set (propKeep_refl hok0) 17 1#32 (by decide) (by decide)
      (by decide) (by decide) (by decide) (Or.inl (by decide))
    have hpk1 := propKeep_of_set hpk0 16 0#32 (by decide) (by decide)
      (by decide) (by decide) (by decide) (Or.inl (by decide))
    have hpk2 := propKeep_of_set hpk1 18 0#32 (by decide) (by decide)
      (by decide) (by decide) (by decide) (Or.inl (by decide))
    have hpk3 := propKeep_of_set hpk2 20 0#32 (by decide) (by decide)
      (by decide) (by decide) (by decide) (Or.inl (by decide))
    c0_hstraight; rw [h17] at hm
    have hl0 : 2912 ≤ (kbuf.set 17 1#32).length := by rw [hpk0.2.1]; exact hlen
    c0_hstraight; rw [h16] at hm
    have hl1 : 2912 ≤ ((kbuf.set 17 1#32).set 16 0#32).length := by rw [hpk1.2.1]; exact hlen
    c0_hstraight; rw [h18] at hm
    have hl2 : 2912 ≤ (((kbuf.set 17 1#32).set 16 0#32).set 18 0#32).length := by
      rw [hpk2.2.1]; exact hlen
    c0_hstraight; rw [h20] at hm
    c0_hcall (Spec.has_full_k6_ana_cl_m7 hΓ)
    refine fullK6AnaClM7Spec_intro hpk3.1 hm ?_
    intro kb4 m4 hlen4 hkeep4 hm4
    have hpk4 := propKeep_of_ana_cl hpk3 hlen4 hkeep4
    have hl4 : 2912 ≤ kb4.length := by rw [hpk4.2.1]; exact hlen
    c0_hsteps_nogrp
    let clvl := kb4[(BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 3)).toNat]'(by
      change 3 % 2 ^ 64 < _; omega)
    let qh := kb4[(BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 5)).toNat]'(by
      change 5 % 2 ^ 64 < _; omega)
    refine wp_join_state1 (t := i32) (fun st : BitVec 32 × List (BitVec 32) => (st.1 : Val i32))
      (fun (idx0, kb) mi => PropKeep kbuf kb ∧ idx0.toNat ≤ 64 ∧ (array (t := i32) pk kb ⋆ R) mi)
      ?_ ?_
    · rintro _ ⟨idx0, kbi0⟩ mi0 ⟨hki0, hidx0_le, hmi0⟩
      refine wp_while_break_state (brkTs := [i32, i32]) (lpTs := [i32])
        (fun st : BitVec 32 × BitVec 32 × List (BitVec 32) => (st.1, st.2.1, ()))
        (fun (_, _, kb) mb => PropKeep kbuf kb ∧ (array (t := i32) pk kb ⋆ R) mb)
        (fun st : BitVec 32 × List (BitVec 32) => (st.1, ())) (fun st => st.1.toNat)
        (fun (idx, kb) mi => PropKeep kbuf kb ∧ idx.toNat ≤ 64 ∧ (array (t := i32) pk kb ⋆ R) mi)
        ?_ ?_ ?_
      · rintro _ ⟨b28, uip, kbb⟩ mb ⟨hkb, hmb⟩
        have h_min := k6_analyze_min_wp hΓ (pk := pk) (cfl := cfl) (nv := nv) (clvl := clvl)
          (qh := qh) (b26 := idx0) (uip := uip) (kbuf := kbuf) (kbb := kbb) (acap := acap)
          (R := R) (Q := Q) (X := X) (mb := mb) hlen hnv_le hQ hkb hnv0 hbuf15 hmb
        dsimp only [aB26Body, aAfterAnaCl, aSGrpB2, aSGrpB1, aSSt3, aSJF, aSLd3, aSL3, aSLt, aSLd,
          aDfltT, aDflt, Prod.fst] at h_min
        exact h_min
      · rintro B L ⟨idx, kbi⟩ mi hB ih1 ⟨hki, hidx_le, hmi⟩
        have h_uip := k6_analyze_uip_step_wp hΓ (pk := pk) (cfl := cfl) (nv := nv) (clvl := clvl)
          (qh := qh) (idx0 := idx0) (idx := idx) (kbuf := kbuf) (kbi := kbi) (R := R) (Q := Q)
          (X := X) (mi := mi) (B := B) (L := L) hlen hnv_le hidx_le hnv0 hki hmi
          (fun bst m' hk' hm' => hB bst m' ⟨hk', hm'⟩)
          (fun idx' kbi' m' hlt hk' hle hm' => ih1 (idx', kbi') m' hlt ⟨hk', hle, hm'⟩)
        dsimp only [aUipBodyE, aUipGrpE, aB26Body, aAfterAnaCl, aSGrpK2, aSGrpB1, aSSt3, aSJF,
          aSLd3, aSL3, aSLt, aSLd, aDfltT, aDflt, Prod.fst] at h_uip
        exact h_uip
      · intro B L _ hL; c0_hsteps!; exact hL (idx0, kbi0) mi0 ⟨hki0, hidx0_le, hmi0⟩
    · intro J hJ
      c0_hsplit
      · c0_hsteps!; exact hJ (64#32, kb4) m4 ⟨hpk4, by decide, hm4⟩
      · c0_hsteps!
        have hk5_le : qh.toNat ≤ 64 := Nat.le_of_not_lt (by simpa [qh] using hc)
        exact hJ (qh, kb4) m4 ⟨hpk4, hk5_le, hm4⟩

end
