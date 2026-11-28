/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Definition.WpM7Basic
public import LeanQbe.T.Examples.Kissat.Proof.Definition.WpM7Prop
public import LeanQbe.T.Examples.Kissat.Proof.Definition.WpM7Analyze

/-!
# Kissat M7 K6 Solver Preservation Proof (`Proof.Definition.WpM7Solve`)

Certifies `fullK6SolveM7Spec` for `full_k6_solve_m7` on flat `CanonicalEnv`, defining `SolveKeep`
and splitting the proof across `k6_solve_pick_wp`, `k6_solve_cdcl_wp`, `k6_solve_units_wp`, and
`full_k6_solve_m7_wp`.
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

/-- Weak solve-loop invariant preserving `K6BufOk`, length, `nv`, monotonic `nc`, `2`, `acap`. -/
@[expose] def SolveKeep (kbuf kb : List (BitVec 32)) : Prop :=
  K6BufOk kb ∧ kb.length = kbuf.length ∧ kb[0]? = kbuf[0]? ∧
  (kbuf[1]?.getD 0#32).toNat ≤ (kb[1]?.getD 0#32).toNat ∧
  kb[2]? = kbuf[2]? ∧ kb[15]? = kbuf[15]?

/-- Reflexivity of `SolveKeep` when `K6BufOk kbuf` holds. -/
theorem solveKeep_refl {kbuf : List (BitVec 32)} (h : K6BufOk kbuf) :
    SolveKeep kbuf kbuf :=
  ⟨h, rfl, rfl, Nat.le_refl _, rfl, rfl⟩

/-- Updating an isolated slot outside `{0, 1, 2, 14, 15}` and `[1888, 2656)` preserves
`SolveKeep`. -/
theorem solveKeep_of_set {kbuf kb : List (BitVec 32)} (hs : SolveKeep kbuf kb)
    (idx : Nat) (v : BitVec 32) (h1 : idx ≠ 1) (h14 : idx ≠ 14) (h15 : idx ≠ 15)
    (h0 : idx ≠ 0) (h2 : idx ≠ 2) (hmet : idx < 1888 ∨ 2656 ≤ idx) :
    SolveKeep kbuf (kb.set idx v) := by
  have hok : K6BufOk (kb.set idx v) :=
    k6BufOk_of_frame hs.1 List.length_set fun i _ hor => by
      have hne : idx ≠ i := by rcases hor with rfl | rfl | rfl | ⟨_, _⟩ <;> omega
      exact List.getElem?_set_ne hne
  refine ⟨hok, List.length_set.trans hs.2.1,
    (List.getElem?_set_ne h0).trans hs.2.2.1, ?_,
    (List.getElem?_set_ne h2).trans hs.2.2.2.2.1,
    (List.getElem?_set_ne h15).trans hs.2.2.2.2.2⟩
  rw [List.getElem?_set_ne h1]; exact hs.2.2.2.1

/-- Frame preservation of `SolveKeep` across `full_k6_watch_m7`. -/
theorem solveKeep_of_watch {kbuf kb kb' : List (BitVec 32)} (hs : SolveKeep kbuf kb)
    (hlen : kb'.length = kb.length)
    (hkeep : ∀ idx < kb.length, (idx < 736 ∨ 1888 ≤ idx) → kb'[idx]? = kb[idx]?) :
    SolveKeep kbuf kb' := by
  have hb := hs.1.base_ge
  have hok := k6BufOk_of_frame hs.1 hlen fun idx _ hor => by
    rcases hor with rfl | rfl | rfl | ⟨_, _⟩
    · exact hkeep 1 (by omega) (Or.inl (by decide))
    · exact hkeep 14 (by omega) (Or.inl (by decide))
    · exact hkeep 15 (by omega) (Or.inl (by decide))
    · exact hkeep idx (by omega) (Or.inr (by omega))
  refine ⟨hok, hlen.trans hs.2.1,
    (hkeep 0 (by omega) (Or.inl (by decide))).trans hs.2.2.1, ?_,
    (hkeep 2 (by omega) (Or.inl (by decide))).trans hs.2.2.2.2.1,
    (hkeep 15 (by omega) (Or.inl (by decide))).trans hs.2.2.2.2.2⟩
  rw [hkeep 1 (by omega) (Or.inl (by decide))]; exact hs.2.2.2.1

/-- Frame preservation of `SolveKeep` across `full_k6_backtrack_m7`. -/
theorem solveKeep_of_backtrack {kbuf kb kb' : List (BitVec 32)} (hs : SolveKeep kbuf kb)
    (hlen : kb'.length = kb.length)
    (hkeep : ∀ idx < kb.length, idx ≠ 3 → idx ≠ 4 → idx ≠ 5 → idx ≠ 6 → idx ≠ 10 →
      (idx < 32 ∨ 160 ≤ idx) → (idx < 608 ∨ 736 ≤ idx) → kb'[idx]? = kb[idx]?) :
    SolveKeep kbuf kb' := by
  have hb := hs.1.base_ge
  have hk_at : ∀ idx, idx < 16 → idx ≠ 3 → idx ≠ 4 → idx ≠ 5 → idx ≠ 6 → idx ≠ 10 →
      kb'[idx]? = kb[idx]? :=
    fun idx hi h3 h4 h5 h6 h10 =>
      hkeep idx (by omega) h3 h4 h5 h6 h10 (Or.inl (by omega)) (Or.inl (by omega))
  have hok := k6BufOk_of_frame hs.1 hlen fun idx _ hor => by
    rcases hor with rfl | rfl | rfl | ⟨_, _⟩
    · exact hk_at 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact hk_at 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact hk_at 15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact hkeep idx (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (Or.inr (by omega)) (Or.inr (by omega))
  refine ⟨hok, hlen.trans hs.2.1,
    (hk_at 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      hs.2.2.1, ?_,
    (hk_at 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      hs.2.2.2.2.1,
    (hk_at 15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      hs.2.2.2.2.2⟩
  rw [hk_at 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  exact hs.2.2.2.1

/-- Frame preservation of `SolveKeep` across `full_k6_assign_m7`. -/
theorem solveKeep_of_assign {kbuf kb kb' : List (BitVec 32)} (hs : SolveKeep kbuf kb)
    (hlen : kb'.length = kb.length)
    (hkeep : ∀ idx < kb.length, idx ≠ 5 → idx ≠ 6 → (idx < 32 ∨ 480 ≤ idx) →
      (idx < 608 ∨ 736 ≤ idx) → kb'[idx]? = kb[idx]?) :
    SolveKeep kbuf kb' := by
  have hb := hs.1.base_ge
  have hk_at : ∀ idx, idx < 16 → idx ≠ 5 → idx ≠ 6 → kb'[idx]? = kb[idx]? :=
    fun idx hi h5 h6 => hkeep idx (by omega) h5 h6 (Or.inl (by omega)) (Or.inl (by omega))
  have hok := k6BufOk_of_frame hs.1 hlen fun idx _ hor => by
    rcases hor with rfl | rfl | rfl | ⟨_, _⟩
    · exact hk_at 1 (by decide) (by decide) (by decide)
    · exact hk_at 14 (by decide) (by decide) (by decide)
    · exact hk_at 15 (by decide) (by decide) (by decide)
    · exact hkeep idx (by omega) (by omega) (by omega) (Or.inr (by omega)) (Or.inr (by omega))
  refine ⟨hok, hlen.trans hs.2.1,
    (hk_at 0 (by decide) (by decide) (by decide)).trans hs.2.2.1, ?_,
    (hk_at 2 (by decide) (by decide) (by decide)).trans hs.2.2.2.2.1,
    (hk_at 15 (by decide) (by decide) (by decide)).trans hs.2.2.2.2.2⟩
  rw [hk_at 1 (by decide) (by decide) (by decide)]; exact hs.2.2.2.1

/-- Preservation of `SolveKeep` across `full_k6_prop_m7`. -/
theorem solveKeep_of_prop {kbuf kb kb' : List (BitVec 32)} (hs : SolveKeep kbuf kb)
    (hok : K6BufOk kb') (hlen : kb'.length = kb.length)
    (h0 : kb'[0]? = kb[0]?) (h1 : kb'[1]? = kb[1]?) (h2 : kb'[2]? = kb[2]?)
    (h15 : kb'[15]? = kb[15]?) : SolveKeep kbuf kb' :=
  ⟨hok, hlen.trans hs.2.1, h0.trans hs.2.2.1, by rw [h1]; exact hs.2.2.2.1,
    h2.trans hs.2.2.2.2.1, h15.trans hs.2.2.2.2.2⟩

/-- Preservation of `SolveKeep` across `full_k6_analyze_m7`. -/
theorem solveKeep_of_analyze {kbuf kb kb' : List (BitVec 32)} (hs : SolveKeep kbuf kb)
    (hok : K6BufOk kb') (hlen : kb'.length = kb.length)
    (h0 : kb'[0]? = kb[0]?) (h2 : kb'[2]? = kb[2]?) (h15 : kb'[15]? = kb[15]?)
    (h1 : (kb[1]?.getD 0#32).toNat ≤ (kb'[1]?.getD 0#32).toNat) : SolveKeep kbuf kb' :=
  ⟨hok, hlen.trans hs.2.1, h0.trans hs.2.2.1, Nat.le_trans hs.2.2.2.1 h1,
    h2.trans hs.2.2.2.2.1, h15.trans hs.2.2.2.2.2⟩

end

private theorem k6_fuel_addr_ofnat (h : BitVec 64) :
    h + (168 : BitVec 64) = (h + 32) + BitVec.ofNat 64 (8 * 17) := by
  rw [BitVec.add_assoc]; congr 1

private theorem k6_fuel_addr_bv (h : BitVec 64) :
    h + 168#64 = (h + 32) + BitVec.ofNat 64 (8 * 17) := by
  rw [BitVec.add_assoc]; congr 1

namespace K6FuelTactics

@[scoped c0_load] theorem k6_load_fuel_ofnat {h : BitVec 64} {hdr : List (BitVec 64)}
    {R : Mem 64 → Prop} {m : Mem 64} (hh : 17 < hdr.length)
    (hm : (array64 (h + 32) hdr ⋆ R) m) :
    loadVal m i64 (h + (168 : BitVec 64)) = some hdr[17] := by
  rw [k6_fuel_addr_ofnat]; exact loadVal_array64 hh hm

@[scoped c0_store] theorem k6_store_fuel_ofnat {h : BitVec 64} {hdr : List (BitVec 64)}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 64) (hh : 17 < hdr.length)
    (hm : (array64 (h + 32) hdr ⋆ R) m) :
    storeOk m i64 (h + (168 : BitVec 64)) ∧
      (array64 (h + 32) (hdr.set 17 v) ⋆ R) (storeMem m i64 (h + (168 : BitVec 64)) v) := by
  rw [k6_fuel_addr_ofnat]; exact store_array64 v hh hm

@[scoped c0_load] theorem k6_load_fuel_bv {h : BitVec 64} {hdr : List (BitVec 64)}
    {R : Mem 64 → Prop} {m : Mem 64} (hh : 17 < hdr.length)
    (hm : (array64 (h + 32) hdr ⋆ R) m) :
    loadVal m i64 (h + 168#64) = some hdr[17] := by
  rw [k6_fuel_addr_bv]; exact loadVal_array64 hh hm

@[scoped c0_store] theorem k6_store_fuel_bv {h : BitVec 64} {hdr : List (BitVec 64)}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 64) (hh : 17 < hdr.length)
    (hm : (array64 (h + 32) hdr ⋆ R) m) :
    storeOk m i64 (h + 168#64) ∧
      (array64 (h + 32) (hdr.set 17 v) ⋆ R) (storeMem m i64 (h + 168#64) v) := by
  rw [k6_fuel_addr_bv]; exact store_array64 v hh hm

end K6FuelTactics

open scoped K6FuelTactics

private theorem bv64_add2_lt_s {a b : BitVec 32} (h : a.toNat + b.toNat < 2 ^ 32) :
    (BitVec.setWidth 64 (a + b)).toNat = a.toNat + b.toNat := by
  rw [BitVec.toNat_setWidth, BitVec.toNat_add, Nat.mod_eq_of_lt h,
    Nat.mod_eq_of_lt (Nat.lt_trans h (by decide))]

private theorem k6_pick_bounds {kb : List (BitVec 32)} {nv cur : BitVec 32}
    (hlen : 2912 ≤ kb.length) (hnv : nv.toNat ≤ 64) (hcur : cur.toNat < nv.toNat) :
    (BitVec.setWidth 64 ((608 : BitVec 32) + (cur <<< (1 : Nat)))).toNat < kb.length ∧
    (BitVec.setWidth 64 ((160 : BitVec 32) + cur)).toNat < kb.length := by
  have hsh : (cur <<< (1 : Nat)).toNat = 2 * cur.toNat := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]; omega
  have h608n : (608 : BitVec 32).toNat = 608 := rfl
  have h160n : (160 : BitVec 32).toNat = 160 := rfl
  exact ⟨by rw [bv64_add2_lt_s (by rw [h608n, hsh]; omega), h608n, hsh]; omega,
    by rw [bv64_add2_lt_s (by rw [h160n]; omega), h160n]; omega⟩

private theorem k6_sep_swap (p q r : Mem 64 → Prop) : (p ⋆ q ⋆ r) = (q ⋆ (p ⋆ r)) := by
  rw [sep_assoc, sep_comm_l]

private def sDflt : (t : Ty) → Val t
  | .bool => false | .bits _ => 0 | .float _ => 0 | .pair a b => (sDflt a, sDflt b)
private def sDfltT : (ts : List Ty) → Tup Val ts
  | [] => () | t :: r => (sDflt t, sDfltT r)

private def sSLdAny {L rs} : Expr Val L rs → Expr Val L rs
  | .load t _ k => k (sDflt t) | _ => .hlt
private def sSLd {L rs} (v : BitVec 32) : Expr Val L rs → Expr Val L rs
  | .load (.bits 32) _ k => k v | _ => .hlt
private def sSLt {L rs} : Expr Val L rs → Expr Val L rs
  | .let_ (ts := ts) _ k => k (sDfltT ts) | _ => .hlt
private def sSL3 {L rs} : Expr Val L rs → Expr Val L rs
  | .let_ (ts := t1) _ k1 => match k1 (sDfltT t1) with
    | .let_ (ts := t2) _ k2 => match k2 (sDfltT t2) with
      | .let_ (ts := t3) _ k3 => k3 (sDfltT t3) | _ => .hlt
    | _ => .hlt
  | _ => .hlt
private def sSLd3 {L rs} (v : BitVec 32) (e : Expr Val L rs) : Expr Val L rs := sSLd v (sSL3 e)
private def sSSt3 {L rs} : Expr Val L rs → Expr Val L rs
  | e => match sSL3 e with | .store _ _ r => r | _ => .hlt
private def sSStAny {L rs} : Expr Val L rs → Expr Val L rs | .store _ _ r => r | _ => .hlt
private def sSJF {L rs} : Expr Val L rs → Expr Val L rs | .jnz _ _ e => e | _ => .hlt
private def sSJT {L rs} : Expr Val L rs → Expr Val L rs | .jnz _ e _ => e | _ => .hlt

private def sSGrpB1 {rs} (J : Cont [.bits 32]) (x : BitVec 32) :
    Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 32]]) bs _ => match bs (J, ()) with | .cons b _ => b (x, ())
  | _ => .hlt

private def sAfterBt (hp pk : BitVec 64) (tlim nv nc acap nunits : BitVec 32) :
    Expr Val Cont [.bits 64] :=
  let e := full_k6_solve_m7_body Val Cont (hp, pk, tlim, ())
  let e := match e with
    | .call (bs := []) "full_k6_backtrack_m7" _ k => k ()
    | _ => .hlt
  let e := sSJF (sSLt (sSLd3 0#32 e))
  let e := sSSt3 (sSSt3 e)
  let e := sSLd3 nunits (sSLd3 acap (sSLd3 nc (sSLd3 nv e)))
  sSJF (sSLt (sSJF (sSLt (sSJF (sSLt e)))))

private def sCdclGrpE (hp pk : BitVec 64) (tlim nv nc acap nunits c33 : BitVec 32) :
    Expr Val Cont [.bits 64] :=
  let e := sSJF (sSLt (sSGrpB1 (fun _ _ => True) 0#32 (sAfterBt hp pk tlim nv nc acap nunits)))
  let e := match e with
    | .call (bs := [.bits 32]) "full_k6_prop_m7" _ k => k (c33, ())
    | _ => .hlt
  sSJF (sSLt e)

private def sCdclBodyE (hp pk : BitVec 64) (tlim nv nc acap nunits c33 b36 : BitVec 32)
    (Jo : Cont [.bits 32]) : Expr Val Cont [.bits 64] :=
  sSGrpB1 Jo b36 (sCdclGrpE hp pk tlim nv nc acap nunits c33)

private def sPickGrpE (hp pk : BitVec 64) (tlim nv nc acap nunits c33 b36 cur : BitVec 32)
    (Jo : Cont [.bits 32]) : Expr Val Cont [.bits 64] :=
  let e := sSJT (sSLt (sSLd3 0#32 (sSLd3 0#32
    (sCdclBodyE hp pk tlim nv nc acap nunits c33 b36 Jo))))
  let e := sSJT (sSLt (sSLdAny (sSLt e)))
  let e := sSStAny (sSLt (sSLt (sSLdAny (sSLt e))))
  let e := sSJF (sSLt e)
  let e := sSJF (sSLt (sSLd3 0#32 e))
  sSLd3 cur e

private theorem k6_solve_pick_wp {Γ : Env} (hΓ : Γ.Sat Spec.specs)
    {hp pk : BitVec 64} {tlim nv nc acap nunits c33 b36 cur : BitVec 32}
    {fl1 : BitVec 64} {hdr : List (BitVec 64)} {kbuf kb : List (BitVec 32)}
    {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost} {Jo : Cont [.bits 32]} {m : Mem 64}
    (hlen : 2912 ≤ kbuf.length) (hnv_le : nv.toNat ≤ 64)
    (hfl1_le : fl1.toNat ≤ (hdr[17]?.getD 0#64).toNat)
    (hsk : SolveKeep kbuf kb)
    (hm : (array (t := i32) pk kb ⋆ (array64 (hp + 32) (hdr.set 17 fl1) ⋆ R)) m)
    (retQ : ∀ (r fuel' : BitVec 64) (kb' : List (BitVec 32)) {m' : Mem 64},
      fuel'.toNat ≤ (hdr[17]?.getD 0#64).toNat → SolveKeep kbuf kb' →
      (array (t := i32) pk kb' ⋆ (array64 (hp + 32) (hdr.set 17 fuel') ⋆ R)) m' →
      Q (r, ()) m')
    (ih : ∀ (cf' : BitVec 32) (kbp' : List (BitVec 32)) (mp' : Mem 64),
      SolveKeep kbuf kbp' →
      (array (t := i32) pk kbp' ⋆ (array64 (hp + 32) (hdr.set 17 fl1) ⋆ R)) mp' →
      Jo (cf', ()) mp') :
    wp Γ Q X (sPickGrpE hp pk tlim nv nc acap nunits c33 b36 cur Jo) m := by
  have hkb_l : 2912 ≤ kb.length := by rw [hsk.2.1]; exact hlen
  dsimp only [sPickGrpE, sCdclBodyE, sCdclGrpE, sAfterBt, sSGrpB1, sSStAny, sSSt3, sSJT, sSJF,
    sSLd3, sSL3, sSLt, sSLd, sSLdAny, sDfltT, sDflt, Prod.fst]
  refine wp_while_break_state
    (brkTs := [i32, i32, i32]) (lpTs := [i32, i32])
    (fun st : BitVec 32 × BitVec 32 × BitVec 32 => (st.1, st.2.1, st.2.2, ()))
    (fun st mp => (st.2.1 = 0xFFFFFFFF#32 ∨ st.2.1.toNat < nv.toNat) ∧ mp = m)
    (fun st : BitVec 32 × BitVec 32 => (st.1, st.2, ()))
    (fun st => nv.toNat - st.2.toNat) (fun st mp => st.2.toNat ≤ nv.toNat ∧ mp = m) ?_ ?_ ?_
  · rintro _ ⟨cur1, pk1, stp1⟩ mp1 ⟨hpk1, hmp1⟩
    rcases hmp1.symm with rfl; c0_hsteps_nogrp
    refine wp_join_state (ts := [i32, i32, i32]) (α := BitVec 32 × BitVec 32 × BitVec 32)
      (fun st => (st.1, st.2.1, st.2.2, ()))
      (fun st mp => (st.2.1 = 0xFFFFFFFF#32 ∨ st.2.1.toNat < nv.toNat) ∧ mp = m) ?_ ?_
    · intro _ ⟨c2, pk2, stp2⟩ mp2 ⟨hpk2, hmp2⟩
      rcases hmp2.symm with rfl; c0_hsteps_nogrp
      refine wp_join_state (ts := [i32, i32]) (α := BitVec 32 × BitVec 32)
        (fun st => (st.1, st.2, ()))
        (fun st mp => (st.2 = 0xFFFFFFFF#32 ∨ st.2.toNat < nv.toNat) ∧ mp = m) ?_ ?_
      · intro _ ⟨c3, pk3⟩ mp3 ⟨hpk3, hmp3⟩
        rcases hmp3.symm with rfl; c0_hsplit
        · c0_hsteps!; exact retQ 10#64 fl1 kb hfl1_le hsk hm
        · have hpk3_lt : pk3.toNat < nv.toNat := by
            rcases hpk3 with rfl | hlt
            · exact absurd rfl hc
            · exact hlt
          have h10n : (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 10)).toNat = 10 := rfl
          have h3n : (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 3)).toNat = 3 := rfl
          have h416n : (416 : BitVec 32).toNat = 416 := rfl
          have h416_bd : (BitVec.setWidth 64 ((416 : BitVec 32) + pk3)).toNat <
              (kb.set 10 pk3).length := by
            rw [bv64_add2_lt_s (by rw [h416n]; omega), List.length_set, h416n]
            have := hnv_le; omega
          have hsk10 := solveKeep_of_set hsk 10 pk3 (by decide) (by decide) (by decide)
            (by decide) (by decide) (Or.inl (by decide))
          c0_hsteps!
          try rw [h10n] at hm
          try rw [h3n] at hm
          try rw [sep_emp] at hm
          c0_hcall (Spec.has_full_k6_assign_m7 hΓ)
          refine fullK6AssignM7Spec_intro ?_ hm ?_
          · rw [List.length_set, List.length_set]; exact hkb_l
          · intro kba ma hlena hkeepa hma
            have hska := solveKeep_of_assign (solveKeep_of_set hsk10 3 _ (by decide) (by decide)
              (by decide) (by decide) (by decide) (Or.inl (by decide))) hlena hkeepa
            c0_hcall (Spec.has_full_k6_prop_m7 hΓ)
            refine fullK6PropM7Spec_intro hska.1 hma ?_
            intro cf' kbp' mp' hokp' hlenp' hp0' hp1' hp2' hp15' _ hmp'
            have hskp' := solveKeep_of_prop hska hokp' hlenp' hp0' hp1' hp2' hp15'
            c0_hsteps!; exact ih cf' kbp' mp' hskp' hmp'
      · intro J3 hJ3; c0_hsplit
        · c0_hsteps_nogrp
          refine wp_while_break_state (brkTs := [i32, i32]) (lpTs := [i32])
            (fun st : BitVec 32 × BitVec 32 => (st.1, st.2, ()))
            (fun st mp => (st.2 = 0xFFFFFFFF#32 ∨ st.2.toNat < nv.toNat) ∧ mp = m)
            (fun c : BitVec 32 => (c, ())) (fun c => nv.toNat - c.toNat)
            (fun c mp => c.toNat ≤ nv.toNat ∧ mp = m) ?_ ?_ ?_
          · rintro _ ⟨c3, pk3⟩ mp3 ⟨hpk3, hmp3⟩
            rcases hmp3.symm with rfl; c0_hsteps!; exact hJ3 (c3, pk3) m ⟨hpk3, rfl⟩
          · rintro B3 L3 c3 mp3 hB3 ih3 ⟨hc3_le, hmp3⟩
            rcases hmp3.symm with rfl; c0_hsplit
            · have hc3_lt : c3.toNat < nv.toNat := hc
              obtain ⟨h608_bd, _⟩ := k6_pick_bounds hkb_l hnv_le hc3_lt
              c0_hsplit
              · c0_hsteps!; exact hB3 (c3, c3) m ⟨Or.inr hc3_lt, rfl⟩
              · have hc31 : (c3 + 1#32).toNat = c3.toNat + 1 := by have := hnv_le; c0_bound
                c0_hsteps!; exact ih3 (c3 + 1#32) m (by rw [hc31]; omega) ⟨by rw [hc31]; omega, rfl⟩
            · c0_hsteps!; exact hB3 (c3, pk2) m ⟨hpk2, rfl⟩
          · intro B3 L3 _ hL3; c0_hsteps!; exact hL3 0#32 m ⟨Nat.zero_le _, rfl⟩
        · c0_hsteps!; exact hJ3 (c2, pk2) m ⟨hpk2, rfl⟩
    · intro J2 hJ2; c0_hsplit
      · c0_hsteps_nogrp
        refine wp_while_break_state (brkTs := [i32, i32, i32]) (lpTs := [i32, i32])
          (fun st : BitVec 32 × BitVec 32 × BitVec 32 => (st.1, st.2.1, st.2.2, ()))
          (fun st mp => (st.2.1 = 0xFFFFFFFF#32 ∨ st.2.1.toNat < nv.toNat) ∧ mp = m)
          (fun st : BitVec 32 × BitVec 32 => (st.1, st.2, ()))
          (fun st => nv.toNat - st.2.toNat) (fun st mp => st.2.toNat ≤ nv.toNat ∧ mp = m) ?_ ?_ ?_
        · rintro _ ⟨c2, pk2, stp2⟩ mp2 ⟨hpk2, hmp2⟩
          rcases hmp2.symm with rfl; c0_hsteps!; exact hJ2 (c2, pk2, stp2) m ⟨hpk2, rfl⟩
        · rintro B2 L2 ⟨c2, stp2⟩ mp2 hB2 ih2 ⟨hstp2_le, hmp2⟩
          rcases hmp2.symm with rfl; c0_hsplit
          · have hc2_lt : c2.toNat < nv.toNat := hc
            clear hc; c0_hsplit
            · have hstp2_lt : stp2.toNat < nv.toNat := hc
              obtain ⟨h608_bd, h160_bd⟩ := k6_pick_bounds hkb_l hnv_le hc2_lt
              c0_hsplit
              · c0_hsteps!; exact hB2 (c2, c2, stp2) m ⟨Or.inr hc2_lt, rfl⟩
              · have hstp21 : (stp2 + 1#32).toNat = stp2.toNat + 1 := by
                  have := hnv_le; c0_bound
                let nc2 := kb[(BitVec.setWidth 64 ((160 : BitVec 32) + c2)).toNat]'h160_bd
                c0_hsteps!
                exact ih2 (nc2, stp2 + 1#32) m (by dsimp only; rw [hstp21]; omega)
                  ⟨by dsimp only; rw [hstp21]; omega, rfl⟩
            · c0_hsteps!; exact hB2 (c2, pk1, stp2) m ⟨hpk1, rfl⟩
          · c0_hsteps!; exact hB2 (c2, pk1, stp2) m ⟨hpk1, rfl⟩
        · intro B2 L2 _ hL2; c0_hsteps!; exact hL2 (_, 0#32) m ⟨Nat.zero_le _, rfl⟩
      · c0_hsteps!; exact hJ2 (cur1, pk1, stp1) m ⟨hpk1, rfl⟩
  · rintro B1 L1 ⟨c1, stp1⟩ mp1 hB1 ih1 ⟨hstp1_le, hmp1⟩
    rcases hmp1.symm with rfl; c0_hsplit
    · have hc1_lt : c1.toNat < nv.toNat := hc
      clear hc; c0_hsplit
      · have hstp1_lt : stp1.toNat < nv.toNat := hc
        obtain ⟨h608_bd, h160_bd⟩ := k6_pick_bounds hkb_l hnv_le hc1_lt
        c0_hsplit
        · c0_hsteps!; exact hB1 (c1, c1, stp1) m ⟨Or.inr hc1_lt, rfl⟩
        · have hstp11 : (stp1 + 1#32).toNat = stp1.toNat + 1 := by have := hnv_le; c0_bound
          let nc1 := kb[(BitVec.setWidth 64 ((160 : BitVec 32) + c1)).toNat]'h160_bd
          c0_hsteps!
          exact ih1 (nc1, stp1 + 1#32) m (by dsimp only; rw [hstp11]; omega)
            ⟨by dsimp only; rw [hstp11]; omega, rfl⟩
      · c0_hsteps!; exact hB1 (c1, 0xFFFFFFFF#32, stp1) m ⟨Or.inl rfl, rfl⟩
    · c0_hsteps!; exact hB1 (c1, 0xFFFFFFFF#32, stp1) m ⟨Or.inl rfl, rfl⟩
  · intro B1 L1 _ hL1; c0_hsteps!; exact hL1 (_, 0#32) m ⟨Nat.zero_le _, rfl⟩

private theorem k6_solve_cdcl_wp {Γ : Env} (hΓ : Γ.Sat Spec.specs)
    {hp pk : BitVec 64} {tlim nv nc acap nunits c33 : BitVec 32}
    {fuel0 : BitVec 64} {hdr : List (BitVec 64)} {kbuf kbp : List (BitVec 32)}
    {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost} {mp : Mem 64}
    (hlen : 2912 ≤ kbuf.length) (hhdr : hdr.length = 140) (hnv_le : nv.toNat ≤ 64)
    (hfuel0_le : fuel0.toNat ≤ (hdr[17]?.getD 0#64).toNat) (hhdr_self : hdr.set 17 fuel0 = hdr)
    (hskp : SolveKeep kbuf kbp)
    (hmp : (array (t := i32) pk kbp ⋆ (array64 (hp + 32) hdr ⋆ R)) mp)
    (retQ : ∀ (r fuel' : BitVec 64) (kb' : List (BitVec 32)) {m' : Mem 64},
      fuel'.toNat ≤ (hdr[17]?.getD 0#64).toNat → SolveKeep kbuf kb' →
      (array (t := i32) pk kb' ⋆ (array64 (hp + 32) (hdr.set 17 fuel') ⋆ R)) m' →
      Q (r, ()) m') :
    wp Γ Q X (sCdclGrpE hp pk tlim nv nc acap nunits c33) mp := by
  dsimp only [sCdclGrpE, sAfterBt, sSGrpB1, sSSt3, sSJF, sSLd3, sSL3, sSLt, sSLd, sDfltT, sDflt,
    Prod.fst]
  refine wp_while_state (ts := [i32])
    (fun st : BitVec 32 × BitVec 64 × List (BitVec 32) => (st.1, ())) (fun st => st.2.1.toNat)
    (fun (cf, fl, kb) mi => fl.toNat ≤ (hdr[17]?.getD 0#64).toNat ∧ SolveKeep kbuf kb ∧
      (array (t := i32) pk kb ⋆ (array64 (hp + 32) (hdr.set 17 fl) ⋆ R)) mi) ?_ ?_
  · intro Jo hJo; c0_hsteps!
    exact hJo (c33, fuel0, kbp) mp ⟨hfuel0_le, hskp, by rw [hhdr_self]; exact hmp⟩
  · rintro Jo ⟨cf, fl, kb⟩ mi ⟨hfl_le, hsk, hmi⟩ ih
    have hkb_l : 2912 ≤ kb.length := by rw [hsk.2.1]; exact hlen
    c0_hsplit
    · clear hc
      have h17_hdr : 17 < (hdr.set 17 fl).length := by simp [hhdr]
      c0_hsplit
      · have hfl_pos : 0 < fl.toNat := by simpa [List.getElem_set_self h17_hdr] using hc
        clear hc
        let fl1 := fl - 1#64
        have hfl1_eq : fl1.toNat = fl.toNat - 1 := by
          dsimp only [fl1]; rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
        have hfl1_lt : fl1.toNat < fl.toNat := by omega
        have hfl1_le : fl1.toNat ≤ (hdr[17]?.getD 0#64).toNat := by omega
        have hfl_val : (hdr.set 17 fl)[17]'h17_hdr - (1 : BitVec 64) = fl1 := by
          rw [List.getElem_set_self h17_hdr]; rfl
        c0_hsplit
        · clear hc; rw [hfl_val, List.set_set, sep_comm_l] at hm; try rw [sep_emp] at hm
          c0_hsplit
          · have h7n : (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 7)).toNat = 7 := rfl
            c0_hsteps_nogrp; rw [h7n] at hm
            try rw [sep_emp] at hm
            have hsk7 := solveKeep_of_set hsk 7 cf (by decide) (by decide) (by decide)
              (by decide) (by decide) (Or.inl (by decide))
            exact retQ 20#64 fl1 (kb.set 7 cf) hfl1_le hsk7 hm
          · clear hc; c0_hcall (Spec.has_full_k6_analyze_m7 hΓ)
            refine fullK6AnalyzeM7Spec_intro hsk.1 hm ?_
            intro oka kba ma hoka hlena ha0 ha2 ha15 ha1_le hma
            have hska := solveKeep_of_analyze hsk hoka hlena ha0 ha2 ha15 ha1_le
            c0_hsplit
            · c0_hcall (Spec.has_full_k6_prop_m7 hΓ)
              refine fullK6PropM7Spec_intro hska.1 hma ?_
              intro cf' kbp' mp' hokp' hlenp' hp0' hp1' hp2' hp15' _ hmp'
              have hskp' := solveKeep_of_prop hska hokp' hlenp' hp0' hp1' hp2' hp15'
              c0_hsteps!; exact ih (cf', fl1, kbp') mp' hfl1_lt ⟨hfl1_le, hskp', hmp'⟩
            · c0_hsteps!; exact retQ 0#64 fl1 kba hfl1_le hska hma
        · clear hc; rw [hfl_val, List.set_set, sep_comm_l] at hm; try rw [sep_emp] at hm
          c0_hsplit
          · c0_hsteps!; exact retQ 10#64 fl1 kb hfl1_le hsk hm
          · clear hc; c0_hsteps_nogrp
            let cur := kb[(BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 10)).toNat]'(by
              change 10 % 2 ^ 64 < _; omega)
            have h_pk := k6_solve_pick_wp hΓ (hp := hp) (pk := pk) (tlim := tlim) (nv := nv)
              (nc := nc) (acap := acap) (nunits := nunits) (c33 := c33) (b36 := cf) (cur := cur)
              (fl1 := fl1) (hdr := hdr) (kbuf := kbuf) (kb := kb) (R := R) (Q := Q) (X := X)
              (Jo := Jo) (m := m) hlen hnv_le hfl1_le hsk hm retQ
              (fun cf' kbp' mp' hskp' hmp' =>
                ih (cf', fl1, kbp') mp' hfl1_lt ⟨hfl1_le, hskp', hmp'⟩)
            dsimp only [sPickGrpE, sCdclBodyE, sCdclGrpE, sAfterBt, sSGrpB1, sSStAny, sSSt3, sSJT,
              sSJF, sSLd3, sSL3, sSLt, sSLd, sSLdAny, sDfltT, sDflt, Prod.fst] at h_pk
            exact h_pk
      · c0_hsteps!; exact retQ 0#64 fl kb hfl_le hsk hmi
    · c0_hsteps!; exact retQ 0#64 fl kb hfl_le hsk hmi

private theorem k6_solve_units_wp {Γ : Env} (hΓ : Γ.Sat Spec.specs)
    {hp pk : BitVec 64} {tlim nv nc acap nunits : BitVec 32} {fuel0 : BitVec 64}
    {hdr : List (BitVec 64)} {kbuf kb2 : List (BitVec 32)} {R : Mem 64 → Prop}
    {Q : Post [i64]} {X : XPost} {m0 : Mem 64}
    (hlen : 2912 ≤ kbuf.length) (hhdr : hdr.length = 140)
    (hnv_le : nv.toNat ≤ 64) (hnc_le : nc.toNat ≤ 256) (hnu_le : nunits.toNat ≤ 128)
    (hfuel0_le : fuel0.toNat ≤ (hdr[17]?.getD 0#64).toNat) (hhdr_self : hdr.set 17 fuel0 = hdr)
    (hs2 : SolveKeep kbuf kb2) (hk2_15 : kb2[15]?.getD 0#32 = acap)
    (hm0 : (array (t := i32) pk kb2 ⋆ (array64 (hp + 32) hdr ⋆ R)) m0)
    (retQ : ∀ (r fuel' : BitVec 64) (kb' : List (BitVec 32)) {m' : Mem 64},
      fuel'.toNat ≤ (hdr[17]?.getD 0#64).toNat → SolveKeep kbuf kb' →
      (array (t := i32) pk kb' ⋆ (array64 (hp + 32) (hdr.set 17 fuel') ⋆ R)) m' →
      Q (r, ()) m') :
    wp Γ Q X (sAfterBt hp pk tlim nv nc acap nunits) m0 := by
  dsimp only [sAfterBt, sSSt3, sSJF, sSLd3, sSL3, sSLt, sSLd, sDfltT, sDflt, Prod.fst]
  refine wp_while_state (ts := [i32])
    (fun st : BitVec 32 × List (BitVec 32) => (st.1, ())) (fun st => nunits.toNat - st.1.toNat)
    (fun (ui, kb) mi => ui.toNat ≤ nunits.toNat ∧ SolveKeep kbuf kb ∧
      (array (t := i32) pk kb ⋆ (array64 (hp + 32) hdr ⋆ R)) mi) ?_ ?_
  · intro J1 hJ1; c0_hsteps!; exact hJ1 (0#32, kb2) m0 ⟨Nat.zero_le _, hs2, hm0⟩
  · rintro J1 ⟨ui, kb⟩ mi ⟨hui_le, hsk, hmi⟩ ih1
    have hkb_l : 2912 ≤ kb.length := by rw [hsk.2.1]; exact hlen
    have hkb_lt28 := hsk.1.length_lt
    have hk15 : kb[15]?.getD 0#32 = acap := by
      have hk15_eq : kb[15]? = kb2[15]? := hsk.2.2.2.2.2.trans hs2.2.2.2.2.2.symm
      rw [hk15_eq]; exact hk2_15
    c0_hsplit
    · have hui_lt : ui.toNat < nunits.toNat := hc
      clear hc
      have hui1_eq : (ui + 1#32).toNat = ui.toNat + 1 := by have := hnu_le; c0_bound
      have h2656_nat : (BitVec.setWidth 64 ((2656 : BitVec 32) + ui)).toNat = 2656 + ui.toNat := by
        have := hnu_le; c0_bound
      have h2656_bd : (BitVec.setWidth 64 ((2656 : BitVec 32) + ui)).toNat < kb.length := by
        rw [h2656_nat]; omega
      let ucid := kb[(BitVec.setWidth 64 ((2656 : BitVec 32) + ui)).toNat]'h2656_bd
      have h2656_mod : (BitVec.toNat (2656 : BitVec 32) + ui.toNat) % 2 ^ 32 = 2656 + ui.toNat := by
        have h2656n : BitVec.toNat (2656 : BitVec 32) = 2656 := rfl
        rw [h2656n]; exact Nat.mod_eq_of_lt (by omega)
      have hucid_c0 : kb[(BitVec.toNat (2656 : BitVec 32) + ui.toNat) % 2 ^ 32]'(by
          rw [h2656_mod, ← h2656_nat]; exact h2656_bd) = ucid :=
        m8_k6_get_congr (by rw [h2656_mod, h2656_nat]) _ _
      c0_hsteps_nogrp
      refine wp_join0 (fun mj => ∃ kbj, SolveKeep kbuf kbj ∧
          (array (t := i32) pk kbj ⋆ (array64 (hp + 32) hdr ⋆ R)) mj) ?_ ?_
      · intro _ mj ⟨kbj, hskj, hmj⟩
        c0_hsteps!; exact ih1 (ui + 1#32, kbj) mj (by dsimp only; rw [hui1_eq]; omega)
          ⟨by rw [hui1_eq]; omega, hskj, hmj⟩
      · intro Ju1 hJu1; c0_hsplit
        · have hucid_lt : ucid.toNat < nc.toNat := by rw [← hucid_c0]; exact hc
          clear hc
          have h1888_nat : (BitVec.setWidth 64 ((1888 : BitVec 32) + ucid)).toNat =
              1888 + ucid.toNat := by have := hnc_le; c0_bound
          have h1888_bd : (BitVec.setWidth 64 ((1888 : BitVec 32) + ucid)).toNat < kb.length := by
            rw [h1888_nat]; omega
          let off := kb[(BitVec.setWidth 64 ((1888 : BitVec 32) + ucid)).toNat]'h1888_bd
          have h1888_mod : (BitVec.toNat (1888 : BitVec 32) + ucid.toNat) % 2 ^ 32 =
              1888 + ucid.toNat := by
            have h1888n : BitVec.toNat (1888 : BitVec 32) = 1888 := rfl
            rw [h1888n]; exact Nat.mod_eq_of_lt (by omega)
          have hoff_c0 : kb[(BitVec.toNat (1888 : BitVec 32) +
              BitVec.toNat kb[(BitVec.toNat (2656 : BitVec 32) + ui.toNat) % 2 ^ 32]) % 2 ^ 32]'(by
                rw [hucid_c0, h1888_mod, ← h1888_nat]; exact h1888_bd) = off :=
            m8_k6_get_congr (by rw [hucid_c0, h1888_mod, h1888_nat]) _ _
          c0_hsteps_nogrp
          refine wp_join0 (fun mj => ∃ kbj, SolveKeep kbuf kbj ∧
              (array (t := i32) pk kbj ⋆ (array64 (hp + 32) hdr ⋆ R)) mj) ?_ ?_
          · intro _ mj ⟨kbj, hskj, hmj⟩; c0_hsteps!; exact hJu1 mj ⟨kbj, hskj, hmj⟩
          · intro Ju2 hJu2; c0_hsplit
            · have hoff_lt : off.toNat < acap.toNat := by rw [← hoff_c0]; exact hc
              clear hc
              have hkb_cap : 2912 + acap.toNat ≤ kb.length := by
                have h := hsk.1.length_ge; rwa [hk15] at h
              have h2912_nat : (BitVec.setWidth 64 ((2912 : BitVec 32) + off)).toNat =
                  2912 + off.toNat := by c0_bound
              have h2912_bd : (BitVec.setWidth 64 ((2912 : BitVec 32) + off)).toNat <
                  kb.length := by rw [h2912_nat]; omega
              let ul := kb[(BitVec.setWidth 64 ((2912 : BitVec 32) + off)).toNat]'h2912_bd
              have h2912_mod : (BitVec.toNat (2912 : BitVec 32) + off.toNat) % 2 ^ 32 =
                  2912 + off.toNat := by
                have h2912n : BitVec.toNat (2912 : BitVec 32) = 2912 := rfl
                rw [h2912n]; exact Nat.mod_eq_of_lt (by omega)
              have hul_c0 : kb[(BitVec.toNat (2912 : BitVec 32) +
                  BitVec.toNat kb[(BitVec.toNat (1888 : BitVec 32) + BitVec.toNat kb[(BitVec.toNat
                    (2656 : BitVec 32) + ui.toNat) % 2 ^ 32]) % 2 ^ 32]) % 2 ^ 32]'(by
                    rw [hoff_c0, h2912_mod, ← h2912_nat]; exact h2912_bd) = ul :=
                m8_k6_get_congr (by rw [hoff_c0, h2912_mod, h2912_nat]) _ _
              c0_hsteps_nogrp
              refine wp_join0 (fun mj => ∃ kbj, SolveKeep kbuf kbj ∧
                  (array (t := i32) pk kbj ⋆ (array64 (hp + 32) hdr ⋆ R)) mj) ?_ ?_
              · intro _ mj ⟨kbj, hskj, hmj⟩; c0_hsteps!; exact hJu2 mj ⟨kbj, hskj, hmj⟩
              · intro Ju3 hJu3; c0_hsplit
                · have hul_lt : ul.toNat < 2 * nv.toNat := by
                    have hmod : nv.toNat * 2 % 2 ^ 32 = nv.toNat * 2 :=
                      Nat.mod_eq_of_lt (by omega)
                    have hul_lt' : ul.toNat < nv.toNat * 2 := by
                      rw [← hul_c0]; simpa [hmod] using hc
                    omega
                  clear hc
                  have h608_bd : (BitVec.setWidth 64 ((608 : BitVec 32) + ul)).toNat <
                      kb.length := by have := hnv_le; c0_bound
                  c0_hsplit
                  · have h7n : (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 7)).toNat = 7 := rfl
                    c0_hsteps_nogrp; rw [h7n] at hm
                    have hsk7 := solveKeep_of_set hsk 7 ucid (by decide) (by decide) (by decide)
                      (by decide) (by decide) (Or.inl (by decide))
                    exact retQ 20#64 fuel0 (kb.set 7 ucid) hfuel0_le hsk7
                      (by rw [hhdr_self]; exact hm)
                  · clear hc
                    refine wp_join0 (fun mj => ∃ kbj, SolveKeep kbuf kbj ∧
                        (array (t := i32) pk kbj ⋆ (array64 (hp + 32) hdr ⋆ R)) mj) ?_ ?_
                    · intro _ mj ⟨kbj, hskj, hmj⟩; c0_hsteps!; exact hJu3 mj ⟨kbj, hskj, hmj⟩
                    · intro Ju4 hJu4; c0_hsplit
                      · c0_hcall (Spec.has_full_k6_assign_m7 hΓ)
                        refine fullK6AssignM7Spec_intro hkb_l hmi ?_
                        intro kba ma hlena hkeepa hma
                        c0_hsteps!; exact hJu4 ma ⟨kba, solveKeep_of_assign hsk hlena hkeepa, hma⟩
                      · c0_hsteps!; exact hJu4 mi ⟨kb, hsk, hmi⟩
                · c0_hsteps!; exact hJu3 mi ⟨kb, hsk, hmi⟩
            · c0_hsteps!; exact hJu2 mi ⟨kb, hsk, hmi⟩
        · c0_hsteps!; exact hJu1 mi ⟨kb, hsk, hmi⟩
    · clear hc
      c0_hcall (Spec.has_full_k6_prop_m7 hΓ)
      refine fullK6PropM7Spec_intro hsk.1 hmi ?_
      intro confl kbp mp hokp hlenp hp0 hp1 hp2 hp15 _ hmp
      have hskp := solveKeep_of_prop hsk hokp hlenp hp0 hp1 hp2 hp15
      have hkp_l : 2912 ≤ kbp.length := by rw [hskp.2.1]; exact hlen
      c0_hsplit
      · have h7n : (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 7)).toNat = 7 := rfl
        c0_hsteps_nogrp; rw [h7n] at hm
        have hskp7 := solveKeep_of_set hskp 7 confl (by decide) (by decide) (by decide)
          (by decide) (by decide) (Or.inl (by decide))
        exact retQ 20#64 fuel0 (kbp.set 7 confl) hfuel0_le hskp7 (by rw [hhdr_self]; exact hm)
      · clear hc
        have h_cdcl := k6_solve_cdcl_wp hΓ (hp := hp) (pk := pk) (tlim := tlim) (nv := nv)
          (nc := nc) (acap := acap) (nunits := nunits) (c33 := confl) (fuel0 := fuel0)
          (hdr := hdr) (kbuf := kbuf) (kbp := kbp) (R := R) (Q := Q) (X := X) (mp := mp)
          hlen hhdr hnv_le hfuel0_le hhdr_self hskp hmp retQ
        dsimp only [sCdclGrpE, sAfterBt, sSGrpB1, sSSt3, sSJF, sSLd3, sSL3, sSLt, sSLd, sDfltT,
          sDflt, Prod.fst] at h_cdcl
        exact h_cdcl

public section

/-- Certifies `fullK6SolveM7Spec` for `full_k6_solve_m7` on flat `CanonicalEnv`. -/
theorem full_k6_solve_m7_wp (Γ : Env) (hΓ : Γ.Sat Spec.specs) :
    ∀ a m Q X, fullK6SolveM7Spec a m Q X → Func.wp Γ full_k6_solve_m7_body a m Q X := by
  rintro ⟨hp, pk, tlim, ⟨⟩⟩ m0 Q X hSpec
  obtain ⟨hdr, kbuf, R, hhdr, hok0, hm0, hQ⟩ := fullK6SolveM7Spec_elim hSpec
  have hlen := hok0.base_ge
  let fuel0 : BitVec 64 := hdr[17]'(by omega)
  have hfuel0_le : fuel0.toNat ≤ (hdr[17]?.getD 0#64).toNat := by
    simp [fuel0, List.getElem?_eq_getElem (by omega : 17 < hdr.length)]
  have hhdr_self : hdr.set 17 fuel0 = hdr := List.set_getElem_self (by omega : 17 < hdr.length)
  have retQ : ∀ (r fuel' : BitVec 64) (kb' : List (BitVec 32)) {m' : Mem 64},
      fuel'.toNat ≤ (hdr[17]?.getD 0#64).toNat → SolveKeep kbuf kb' →
      (array (t := i32) pk kb' ⋆ (array64 (hp + 32) (hdr.set 17 fuel') ⋆ R)) m' →
      Q (r, ()) m' := fun r fuel' kb' m' hfl' hsk' hm' =>
    hQ r fuel' kb' m' hfl' hsk'.1 hsk'.2.1 hsk'.2.2.1 hsk'.2.2.2.1 hsk'.2.2.2.2.1
      hsk'.2.2.2.2.2 ((k6_sep_swap (array64 (hp + 32) (hdr.set 17 fuel'))
        (array (t := i32) pk kb') R) ▸ hm')
  have hm0' : (array (t := i32) pk kbuf ⋆ (array64 (hp + 32) hdr ⋆ R)) m0 :=
    (k6_sep_swap (array64 (hp + 32) hdr) (array (t := i32) pk kbuf) R) ▸ hm0
  unfold Func.wp full_k6_solve_m7_body
  c0_hcall (Spec.has_full_k6_backtrack_m7 hΓ)
  refine fullK6BacktrackM7Spec_intro hlen hm0' ?_
  intro kb1 m1 hlen1 hkeep1 hm1
  have hs1 := solveKeep_of_backtrack (solveKeep_refl hok0) hlen1 hkeep1
  have hs1_l : 2912 ≤ kb1.length := by rw [hs1.2.1]; exact hlen
  c0_hsplit
  · c0_hsteps!; exact retQ 20#64 fuel0 kb1 hfuel0_le hs1 (by rw [hhdr_self]; exact hm1)
  · clear hc
    have h13n : (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 13)).toNat = 13 := rfl
    have h12n : (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 12)).toNat = 12 := rfl
    c0_hstraight
    rw [h13n, h12n] at hm
    let kb2 := (kb1.set 13 tlim).set 12 0#32
    have hs2' := solveKeep_of_set hs1 13 tlim (by decide) (by decide) (by decide)
      (by decide) (by decide) (Or.inl (by decide))
    have hs2 := solveKeep_of_set hs2' 12 0#32 (by decide) (by decide) (by decide)
      (by decide) (by decide) (Or.inl (by decide))
    have hs2_l : 2912 ≤ kb2.length := by rw [hs2.2.1]; exact hlen
    let nv := kb2[(BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 0)).toNat]'(by
      change 0 % 2 ^ 64 < _; omega)
    let nc := kb2[(BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 1)).toNat]'(by
      change 1 % 2 ^ 64 < _; omega)
    let acap := kb2[(BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 15)).toNat]'(by
      change 15 % 2 ^ 64 < _; omega)
    let nunits := kb2[(BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 19)).toNat]'(by
      change 19 % 2 ^ 64 < _; omega)
    c0_hsplit
    · c0_hsteps!; exact retQ 0#64 fuel0 kb2 hfuel0_le hs2 (by rw [hhdr_self]; exact hm)
    · have hnv_le : nv.toNat ≤ 64 := Nat.le_of_not_lt (by simpa [nv, kb2] using hc)
      clear hc; c0_hsplit
      · c0_hsteps!; exact retQ 0#64 fuel0 kb2 hfuel0_le hs2 (by rw [hhdr_self]; exact hm)
      · have h_13 : (OfNat.ofNat 13 % 18446744073709551616 : Nat) = 13 := rfl
        have h_12 : (OfNat.ofNat 12 % 18446744073709551616 : Nat) = 12 := rfl
        have hnc_le : nc.toNat ≤ 256 := Nat.le_of_not_lt (by simpa [nc, kb2, h_13, h_12] using hc)
        clear hc; c0_hsplit
        · c0_hsteps!; exact retQ 0#64 fuel0 kb2 hfuel0_le hs2 (by rw [hhdr_self]; exact hm)
        · have hnu_le : nunits.toNat ≤ 128 :=
            Nat.le_of_not_lt (by simpa [nunits, kb2, h_13, h_12] using hc)
          clear hc
          have h_u := k6_solve_units_wp hΓ (hp := hp) (pk := pk) (tlim := tlim) (nv := nv)
            (nc := nc) (acap := acap) (nunits := nunits) (fuel0 := fuel0) (hdr := hdr)
            (kbuf := kbuf) (kb2 := kb2) (R := R) (Q := Q) (X := X) (m0 := m)
            hlen hhdr hnv_le hnc_le hnu_le hfuel0_le hhdr_self hs2
            (by rw [List.getElem?_eq_getElem (by omega)]; rfl) hm retQ
          dsimp only [sAfterBt, sSSt3, sSJF, sSLd3, sSL3, sSLt, sSLd, sDfltT, sDflt,
            Prod.fst] at h_u
          exact h_u

end

end LeanQbe.T.Examples.Kissat.Proof.Definition
