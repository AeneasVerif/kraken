/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S1Core
public import LeanQbe.T.Examples.Kissat.FullM7BveGatesProof4a
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Fidelity Step 13 Shard S1-C Proofs — Part 0 (`full_k6_core_m7`)

Certifies `FullM7BveGates.fullK6CoreM7Spec` for Step-13 `full_k6_core_m7` (`F-P0-1` non-exclusive
level-0 trace in the fixpoint loop), split into modular `<= 420`-line theorems (`public section`,
`0` `@[expose]`, `0` `import all`, `<= 100` cols, `< 1,400` LOC).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S1

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM7BveGates
open Kraken.Bedrock2.Test

open scoped FullArenaTactics FullM7BveGates.K6Tactics

attribute [local bv_c0] List.length_set

section S13CoreM7Proof

private theorem s13_c1 : (OfNat.ofNat 1 % 18446744073709551616 : Nat) = 1 := rfl
private theorem s13_c7 : (OfNat.ofNat 7 % 18446744073709551616 : Nat) = 7 := rfl
private theorem s13_c15 : (OfNat.ofNat 15 % 18446744073709551616 : Nat) = 15 := rfl

private theorem s13_set_congr {α : Type} {xs : List α} {i j : Nat} {a b : α}
    (hi : i = j) (ha : a = b) : xs.set i a = xs.set j b := by
  subst hi ha; rfl

private theorem s13_get_congr {α : Type} {xs : List α} {i j : Nat}
    (h : i = j) (hi : i < xs.length) (hj : j < xs.length) : xs[i]'hi = xs[j]'hj := by
  subst h; rfl

private theorem s13_buf_get_eq {kbuf : List (BitVec 32)} {i : Nat} (hi : i < kbuf.length) :
    kbuf[i]?.getD 0#32 = kbuf[i]'hi := by
  rw [List.getElem?_eq_getElem hi, Option.getD_some]

private theorem s13_bv32_bit_disj (x mask target : BitVec 32)
    (hm : (mask &&& target) = 0#32) :
    ((x ||| mask) &&& target) = (x &&& target) ∧
    ((x &&& ~~~mask) &&& target) = (x &&& target) := by
  have h1 : ((x ||| mask) &&& target) = (x &&& target) := by
    ext i hi
    have hmi := congrArg (·[i]) hm
    simp only [BitVec.getElem_and, BitVec.getElem_zero] at hmi
    simp only [BitVec.getElem_and, BitVec.getElem_or]
    rw [Bool.and_or_distrib_right, hmi, Bool.or_false]
  have h2 : ((x &&& ~~~mask) &&& target) = (x &&& target) := by
    ext i hi
    have hmi := congrArg (·[i]) hm
    simp only [BitVec.getElem_and, BitVec.getElem_zero] at hmi
    simp only [BitVec.getElem_and, BitVec.getElem_not]
    cases ht : target[i]
    · simp
    · simp only [ht, Bool.and_true] at hmi ⊢; simp [hmi]
  exact ⟨h1, h2⟩

private theorem s13_km_core_clear_pres (x : BitVec 32) :
    ((x &&& ~~~0x80000000#32) &&& 0xFFFF#32) = (x &&& 0xFFFF#32) ∧
    ((x &&& ~~~0x80000000#32) &&& 0x40000000#32) = (x &&& 0x40000000#32) :=
  ⟨(s13_bv32_bit_disj x 0x80000000#32 0xFFFF#32 (by decide)).2,
   (s13_bv32_bit_disj x 0x80000000#32 0x40000000#32 (by decide)).2⟩

private theorem s13_km_core_or_pres (x : BitVec 32) :
    ((x ||| 0x80000000#32) &&& 0xFFFF#32) = (x &&& 0xFFFF#32) ∧
    ((x ||| 0x80000000#32) &&& 0x40000000#32) = (x &&& 0x40000000#32) :=
  ⟨(s13_bv32_bit_disj x 0x80000000#32 0xFFFF#32 (by decide)).1,
   (s13_bv32_bit_disj x 0x80000000#32 0x40000000#32 (by decide)).1⟩

private theorem s13_k6BufOk_set_core_meta {kbuf : List (BitVec 32)} (h : K6BufOk kbuf)
    {cid : Nat} (hcid : cid < 256) {v : BitVec 32}
    (hsz : (v &&& 0xFFFF#32) = ((kbuf[2144 + cid]?.getD 0#32) &&& 0xFFFF#32))
    (hlrn : (v &&& 0x40000000#32) = ((kbuf[2144 + cid]?.getD 0#32) &&& 0x40000000#32)) :
    K6BufOk (kbuf.set (2144 + cid) v) := by
  have hb := h.base_ge
  have hk1 : (kbuf.set (2144 + cid) v)[1]? = kbuf[1]? := List.getElem?_set_ne (by omega)
  have hk14 : (kbuf.set (2144 + cid) v)[14]? = kbuf[14]? := List.getElem?_set_ne (by omega)
  have hk15 : (kbuf.set (2144 + cid) v)[15]? = kbuf[15]? := List.getElem?_set_ne (by omega)
  refine K6BufOk.mk_of (by rw [hk15, List.length_set]; exact h.length_ge)
    (by rw [List.length_set]; exact h.length_lt)
    (by rw [hk1]; exact h.nc_le) (by rw [hk14, hk15]; exact h.alen_le) fun j hj => ?_
  rw [hk1] at hj
  have hnc := h.nc_le
  have hj256 : j < 256 := by omega
  have ho : (kbuf.set (2144 + cid) v)[1888 + j]? = kbuf[1888 + j]? :=
    List.getElem?_set_ne (by omega)
  have ha : (kbuf.set (2144 + cid) v)[2400 + j]? = kbuf[2400 + j]? :=
    List.getElem?_set_ne (by omega)
  rw [ho, ha, hk15]
  by_cases heq : j = cid
  · subst heq
    dsimp only
    rw [List.getElem?_set_self (by omega), Option.getD_some, hsz, hlrn]
    exact h.clause_ok hj
  · rw [List.getElem?_set_ne (by omega)]
    exact h.clause_ok hj

private theorem s13_k6BufOk_set_flags {kbuf : List (BitVec 32)} (h : K6BufOk kbuf)
    {i : Nat} (hi : i < 64) (v : BitVec 32) :
    K6BufOk (kbuf.set (416 + i) v) :=
  k6BufOk_of_frame h (List.length_set) fun idx _ hor => by
    rcases hor with rfl | rfl | rfl | ⟨_, _⟩ <;> exact List.getElem?_set_ne (by omega)

private def s13CoreInv (kbuf : List (BitVec 32)) (nc : BitVec 32)
    (kb : List (BitVec 32)) : Prop :=
  K6BufOk kb ∧ kb.length = kbuf.length ∧
  (∀ idx < kbuf.length, (idx < 416 ∨ (480 ≤ idx ∧ idx < 2144) ∨ 2400 ≤ idx) →
    kb[idx]? = kbuf[idx]?) ∧
  (∀ cid < nc.toNat,
    let m0 := kbuf[2144 + cid]?.getD 0#32
    let m1 := kb[2144 + cid]?.getD 0#32
    (m1 &&& 0xFFFF#32) = (m0 &&& 0xFFFF#32) ∧
      (m1 &&& 0x40000000#32) = (m0 &&& 0x40000000#32))

private theorem s13CoreInv_set_meta {kbuf : List (BitVec 32)} {nc : BitVec 32}
    (hnc_le : nc.toNat ≤ 256) {kb : List (BitVec 32)} (hik : s13CoreInv kbuf nc kb)
    {cid : Nat} (hcid : cid < nc.toNat) {v : BitVec 32}
    (hsz : (v &&& 0xFFFF#32) = ((kb[2144 + cid]?.getD 0#32) &&& 0xFFFF#32))
    (hlrn : (v &&& 0x40000000#32) = ((kb[2144 + cid]?.getD 0#32) &&& 0x40000000#32)) :
    s13CoreInv kbuf nc (kb.set (2144 + cid) v) := by
  refine ⟨s13_k6BufOk_set_core_meta hik.1 (by omega) hsz hlrn, by simp [hik.2.1],
    fun idx hi hor => ?_, fun j hj => ?_⟩
  · rw [List.getElem?_set_ne (by omega)]; exact hik.2.2.1 idx hi hor
  · by_cases heq : j = cid
    · subst heq
      have hk_l : 2144 + j < kb.length := by have := hik.1.base_ge; omega
      dsimp only
      rw [List.getElem?_set_self hk_l, Option.getD_some, hsz, hlrn]
      exact hik.2.2.2 j hj
    · rw [List.getElem?_set_ne (by omega)]; exact hik.2.2.2 j hj

private theorem s13CoreInv_set_flags {kbuf : List (BitVec 32)} {nc : BitVec 32}
    {kb : List (BitVec 32)} (hik : s13CoreInv kbuf nc kb)
    {v : Nat} (hv : v < 64) (val : BitVec 32) :
    s13CoreInv kbuf nc (kb.set (416 + v) val) := by
  refine ⟨s13_k6BufOk_set_flags hik.1 hv val, by simp [hik.2.1],
    fun idx hi hor => ?_, fun j hj => ?_⟩
  · rw [List.getElem?_set_ne (by omega)]; exact hik.2.2.1 idx hi hor
  · rw [List.getElem?_set_ne (by omega)]; exact hik.2.2.2 j hj

private theorem s13_cid_sub_toNat {cid nc : BitVec 32} (hpos : 0 < cid.toNat)
    (hle : cid.toNat ≤ nc.toNat) (hnc : nc.toNat ≤ 256) :
    (cid - 1#32).toNat = cid.toNat - 1 := by
  rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat, Nat.reducePow]; omega

private theorem s13_cid_sub_mod {cid nc : BitVec 32} (hpos : 0 < cid.toNat)
    (hle : cid.toNat ≤ nc.toNat) (hnc : nc.toNat ≤ 256) :
    (1888 + (2 ^ 32 - 1 + cid.toNat)) % 2 ^ 32 = 1888 + (cid - 1#32).toNat := by
  rw [s13_cid_sub_toNat hpos hle hnc]; omega

private theorem s13_2912_mod_eq {o s j na acap15 acap len : Nat}
    (hge : 2912 + acap15 ≤ len) (heq : acap15 = acap) (hl28 : len < 2 ^ 28)
    (hna : o + s + na ≤ acap) (hj : j < na) :
    (2912 + o + s + j) % 2 ^ 32 = 2912 + o + s + j :=
  Nat.mod_eq_of_lt (by omega)

private theorem s13_2144_lt {a nc l1 l2 : Nat} (ha : a < nc) (hnc : nc ≤ 256)
    (hl : 2912 ≤ l2) (heq : l1 = l2) : 2144 + a < l1 := by omega

private theorem s13_sw64_add {base : BitVec 32} {a : BitVec 32} (hb : base.toNat ≤ 2400)
    (ha : a.toNat < 256) :
    (BitVec.setWidth 64 (base + a)).toNat = base.toNat + a.toNat := by c0_bound

private theorem s13_k6_h15_eq {kbuf kb : List (BitVec 32)} {nc acap : BitVec 32}
    (hlen : 2912 ≤ kbuf.length) (hac : acap = kbuf[15]'(by omega))
    (hik : s13CoreInv kbuf nc kb) :
    kb[15]'(by have := hik.2.1; omega) = acap ∧ (kb[15]?.getD 0#32).toNat = acap.toNat := by
  have h15 := hik.2.2.1 15 (by omega) (Or.inl (by omega))
  have hk_l : 15 < kb.length := by rw [hik.2.1]; omega
  rw [List.getElem?_eq_getElem hk_l, List.getElem?_eq_getElem (by omega)] at h15
  have heq : kb[15]'hk_l = acap := by rw [hac]; exact Option.some.inj h15
  exact ⟨heq, by rw [s13_buf_get_eq hk_l, heq]⟩

private theorem s13_k6_h1_lt {kbuf kb : List (BitVec 32)} {nc : BitVec 32}
    (hlen : 2912 ≤ kbuf.length) (hnc : nc = kbuf[1]'(by omega))
    (hik : s13CoreInv kbuf nc kb) {cid : Nat} (hcid : cid < nc.toNat) :
    cid < (kb[1]?.getD 0#32).toNat := by
  have h1 := hik.2.2.1 1 (by omega) (Or.inl (by omega))
  have hk_l : 1 < kb.length := by rw [hik.2.1]; omega
  rw [List.getElem?_eq_getElem hk_l, List.getElem?_eq_getElem (by omega)] at h1
  have heq : kb[1]'hk_l = nc := by rw [hnc]; exact Option.some.inj h1
  rw [s13_buf_get_eq hk_l, heq]; exact hcid

private theorem s13_1888_len_lt {i nc l : Nat} (hi : i < nc) (hnc : nc ≤ 256)
    (hl : 2912 ≤ l) : 1888 + i < l := by omega

private theorem s13_2144_len_lt {i nc l : Nat} (hi : i < nc) (hnc : nc ≤ 256)
    (hl : 2912 ≤ l) : 2144 + i < l := by omega

private theorem s13_add_mod_lt {c i nc : Nat} (hc : c ≤ 2144) (hi : i < nc)
    (hnc : nc ≤ 256) : (c + i) % 4294967296 = c + i := by omega

private def s13Dflt : (t : Ty) → Val t
  | .bool => false | .bits _ => 0 | .float _ => 0 | .pair a b => (s13Dflt a, s13Dflt b)
private def s13DfltT : (ts : List Ty) → Tup Val ts
  | [] => () | t :: r => (s13Dflt t, s13DfltT r)
private def s13SLet {L rs} : Expr Val L rs → Expr Val L rs
  | .let_ (ts := ts) _ k => k (s13DfltT ts) | _ => .hlt
private def s13SLet32 {L rs} (v : Val (.bits 32)) : Expr Val L rs → Expr Val L rs
  | .let_ (ts := [.bits 32]) _ k => k (v, ()) | _ => .hlt
private def s13SLd {L rs} (v : Val i32) : Expr Val L rs → Expr Val L rs
  | .load (.bits 32) _ k => k v | _ => .hlt
private def s13SJF {L rs} : Expr Val L rs → Expr Val L rs
  | .jnz _ _ e => e | _ => .hlt
private def s13SJT {L rs} : Expr Val L rs → Expr Val L rs
  | .jnz _ e _ => e | _ => .hlt
private def s13SGrpB {rs} (x : Val i32) : Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 32]]) bs _ =>
      match bs ((fun _ _ => True), ()) with | .cons b _ => b (x, ())
  | _ => .hlt

private def s13M7FixE (pk : BitVec 64) (nc nv acap : BitVec 32) : Expr Val Cont [] :=
  let e := s13SLd nc (s13SLet (s13SLet (s13SLet (full_k6_core_m7_body Val Cont (pk, ())))))
  let e := s13SJF (s13SLet (s13SJF (s13SLet (s13SLd acap (s13SLet (s13SLet (s13SLet
    (s13SLd nv (s13SLet (s13SLet (s13SLet e)))))))))))
  let e := s13SLd 0#32 (s13SLet (s13SLet (s13SLet (s13SJF (s13SLet (s13SGrpB nc e))))))
  s13SGrpB 0#32 e

private def s13M7Lvl0E (pk : BitVec 64) (nc nv acap off_c sz_c : BitVec 32)
    (ch' : Bool) (Jcid : Cont [.bool]) : Expr Val Cont [] :=
  let e := s13M7FixE pk nc nv acap
  let e := match e with
    | .group (sig := [[.bits 32, .bool]]) bs _ =>
        match bs ((fun _ _ => True), ()) with
        | .cons b _ => b (0#32, true, ())
    | _ => .hlt
  let e := s13SLet (s13SJT (s13SLet (s13SJT e)))
  let e := match e with
    | .group (sig := [[.bool, .bits 32]]) bs _ =>
        match bs ((fun _ _ => True), ()) with
        | .cons b _ => b (false, nc, ())
    | _ => .hlt
  let e := s13SLd (0#32 : Val i32) (s13SLet (s13SLet (s13SLet (s13SLet (s13SLet
    (s13SJT (s13SLet e)))))))
  let e := match e with
    | .group (sig := [[.bool]]) _ body => body (Jcid, ())
    | _ => .hlt
  let e := s13SLet32 sz_c (s13SLd (off_c : Val i32) (s13SLet (s13SLet (s13SLet (s13SLet
    (s13SJT (s13SLet (s13SLet e))))))))
  match e with
  | .group (sig := [[.bool]]) bs _ =>
      match bs (Jcid, ()) with | .cons b _ => b ((ch' : Val .bool), ())
  | _ => .hlt

private theorem s13_m7_lvl0_lits_wp {Γ : Env} {pk : BitVec 64} {kbuf : List (BitVec 32)}
    {nc nv acap off_c sz_c : BitVec 32} {R : Mem 64 → Prop} {Q : Post []} {X : XPost}
    {Jcid : Cont [.bool]}
    (hlen : 2912 ≤ kbuf.length) (_hnc_def : nc = kbuf[1]'(by omega))
    (hacap_def : acap = kbuf[15]'(by omega)) (hnc_le : nc.toNat ≤ 256) (hnv_le : nv.toNat ≤ 64)
    {kbc : List (BitVec 32)} {mc : Mem 64} {ch_c : Bool}
    (hkc : s13CoreInv kbuf nc kbc) (hoff_sz : off_c.toNat + sz_c.toNat ≤ acap.toNat)
    (hmc : (array (t := i32) pk kbc ⋆ R) mc)
    (hJcid : ∀ xs mc', (match xs with
      | (_ch', ()) => ∃ kbc', s13CoreInv kbuf nc kbc' ∧
          (array (t := i32) pk kbc' ⋆ R) mc') → Jcid xs mc') :
    wp Γ Q X (s13M7Lvl0E pk nc nv acap off_c sz_c ch_c Jcid) mc := by
  let invCore := s13CoreInv kbuf nc
  have invCore_set_meta := @s13CoreInv_set_meta kbuf nc hnc_le
  have h15_eq : kbc[15]'(by have := hkc.2.1; omega) = acap := by
    have h15 := hkc.2.2.1 15 (by omega) (Or.inl (by omega))
    have hk_l : 15 < kbc.length := by rw [hkc.2.1]; omega
    rw [List.getElem?_eq_getElem hk_l, List.getElem?_eq_getElem (by omega)] at h15
    rw [hacap_def]; exact Option.some.inj h15
  have h15' : (kbc[15]?.getD 0#32).toNat = acap.toNat := by
    rw [s13_buf_get_eq (by have := hkc.2.1; omega), h15_eq]
  have hlt28 := hkc.1.length_lt; have hlen_ge := hkc.1.length_ge
  have hno_ov : off_c.toNat + sz_c.toNat < 2 ^ 32 := by omega
  have hsz_lt : sz_c.toNat < 2 ^ 32 := by omega
  dsimp only [s13M7Lvl0E, s13M7FixE, full_k6_core_m7_body, s13SLet, s13SLet32, s13SLd,
    s13SJF, s13SJT, s13SGrpB, s13DfltT, s13Dflt]
  c0_hsteps_nogrp
  refine wp_join_state1 (t := .bool) (α := List (BitVec 32) × Bool) (fun x => x.2)
    (fun x mc' => invCore x.1 ∧ (array (t := i32) pk x.1 ⋆ R) mc') ?_ ?_
  · rintro _ ⟨kbc', ch''⟩ mc' ⟨hkc', hmc'⟩
    c0_hsteps!; exact hJcid (ch'', ()) mc' ⟨kbc', hkc', hmc'⟩
  · intro J_l0 hJ_l0
    c0_hsplit
    · have hcmp_le : off_c.toNat + sz_c.toNat ≤ acap.toNat := hoff_sz
      clear hc
      c0_hsteps_nogrp
      refine wp_loop_group (ts := [.bool, i32])
        (fun remj (chj, jc, ()) mj => ∃ kbj, invCore kbj ∧ jc.toNat ≤ sz_c.toNat ∧
          remj = sz_c.toNat - jc.toNat ∧ (array (t := i32) pk kbj ⋆ R) mj) ?_ ?_
      · rintro Lj remj ⟨ch_j, j_c, ⟨⟩⟩ mj hLj ⟨kbj, hkj, hj_le, rfl, hmj⟩
        have hkj_l := hkj.2.1
        c0_hsplit
        · have hj_lt : j_c.toNat < sz_c.toNat := hc; clear hc
          have hj1 : (j_c + 1#32).toNat = j_c.toNat + 1 := by
            have := hlt28; have := hlen_ge; have := h15'; have := hoff_sz; c0_bound
          have hkj15 := (s13_k6_h15_eq hlen hacap_def hkj).2
          have hkj_ge := hkj.1.length_ge
          have hidx_lt : 2912 + off_c.toNat + j_c.toNat < kbj.length := by
            have := hj_lt; omega
          have hidx_c0 : (BitVec.setWidth 64 (2912#32 + off_c + j_c)).toNat =
              2912 + off_c.toNat + j_c.toNat := by
            have := hidx_lt; have := hno_ov; have := hlt28; have := hlen_ge; have := h15'; c0_bound
          have hidx_c0_lt : (BitVec.setWidth 64 (2912#32 + off_c + j_c)).toNat < kbj.length := by
            rw [hidx_c0]; exact hidx_lt
          let lv := (kbj[2912 + off_c.toNat + j_c.toNat]'hidx_lt) >>> (1 : Nat)
          have hget_lv_c0 : kbj[(BitVec.setWidth 64 (2912#32 + off_c + j_c)).toNat]'hidx_c0_lt =
              kbj[2912 + off_c.toNat + j_c.toNat]'hidx_lt := s13_get_congr hidx_c0 _ _
          c0_hsteps_nogrp
          refine wp_join_state1 (t := .bool) (α := List (BitVec 32) × Bool) (fun x => x.2)
            (fun x mj' => invCore x.1 ∧ (array (t := i32) pk x.1 ⋆ R) mj') ?_ ?_
          · rintro _ ⟨kbj', chj'⟩ mj' ⟨hkj', hmj'⟩
            c0_hsteps!
            exact hLj (sz_c.toNat - (j_c + 1#32).toNat) (chj', j_c + 1#32, ()) mj'
              (by have := hj1; omega) ⟨kbj', hkj', by omega, rfl, hmj'⟩
          · intro Jlv hJlv
            c0_hsplit
            · have har_mod : (2912 + off_c.toNat + j_c.toNat) % 2 ^ 32 =
                  2912 + off_c.toNat + j_c.toNat := by
                have := hidx_lt; have := hlt28; omega
              have hlv_lt : lv.toNat < nv.toNat := by
                dsimp only [lv]; rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
                  ← s13_get_congr har_mod (by rw [har_mod]; exact hidx_lt) hidx_lt]
                simpa [Nat.reducePow] using hc
              clear hc
              have h32_c0 : (BitVec.setWidth 64 (32#32 +
                  ((kbj[(BitVec.setWidth 64 (2912#32 + off_c + j_c)).toNat]'hidx_c0_lt) >>>
                    (1 : Nat)))).toNat < kbj.length := by
                rw [hget_lv_c0]
                change (BitVec.setWidth 64 (32#32 + lv)).toNat < kbj.length
                have := hlv_lt; have := hnv_le; have := hkj_l; have := hlen; c0_bound
              c0_hsplit
              · clear hc
                have h96_c0 : (BitVec.setWidth 64 (96#32 +
                    ((kbj[(BitVec.setWidth 64 (2912#32 + off_c + j_c)).toNat]'hidx_c0_lt) >>>
                      (1 : Nat)))).toNat < kbj.length := by
                  rw [hget_lv_c0]
                  change (BitVec.setWidth 64 (96#32 + lv)).toNat < kbj.length
                  have := hlv_lt; have := hnv_le; have := hkj_l; have := hlen; c0_bound
                let r0 := kbj[96 + lv.toNat]'(by
                  have := hlv_lt; have := hnv_le; have := hkj_l; have := hlen; omega)
                have hr0_c0_eq : kbj[(BitVec.setWidth 64 (96#32 +
                    ((kbj[(BitVec.setWidth 64 (2912#32 + off_c + j_c)).toNat]'hidx_c0_lt) >>>
                      (1 : Nat)))).toNat]'h96_c0 = r0 := by
                  refine s13_get_congr ?_ h96_c0 _
                  rw [hget_lv_c0]; change (BitVec.setWidth 64 (96#32 + lv)).toNat = 96 + lv.toNat
                  have := hlv_lt; have := hnv_le; c0_bound
                c0_hsteps_nogrp
                refine wp_join_state1 (t := .bool) (α := List (BitVec 32) × Bool) (fun x => x.2)
                  (fun x mj' => invCore x.1 ∧ (array (t := i32) pk x.1 ⋆ R) mj') ?_ ?_
                · rintro _ ⟨kbj', chj'⟩ mj' ⟨hkj', hmj'⟩
                  c0_hsteps!; exact hJlv (kbj', chj') mj' ⟨hkj', hmj'⟩
                · intro Jr0 hJr0
                  have h96_mod : (96 + (kbj[(2912 + off_c.toNat + j_c.toNat) % 2 ^ 32]'(by
                      rw [har_mod]; exact hidx_lt)).toNat / 2) % 2 ^ 32 = 96 + lv.toNat := by
                    rw [s13_get_congr har_mod _ hidx_lt]
                    dsimp only [lv]; rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
                    have := hlv_lt; have := hnv_le; omega
                  have hget_r0_raw : kbj[(96 + (kbj[(2912 + off_c.toNat + j_c.toNat) % 2 ^ 32]'(by
                      rw [har_mod]; exact hidx_lt)).toNat / 2) % 2 ^ 32]'(by
                      rw [h96_mod]; have := hlv_lt; have := hnv_le; have := hkj_l
                      have := hlen; omega) = r0 := s13_get_congr h96_mod _ _
                  c0_hsplit
                  · have hr0_lt : r0.toNat < nc.toNat := by
                      rw [← hget_r0_raw]; simpa [s13_c1] using hc
                    clear hc
                    let oldr := kbj[2144 + r0.toNat]'(s13_2144_lt hr0_lt hnc_le hlen hkj_l)
                    have hpr := s13_km_core_or_pres oldr
                    have h2144_r_idx : (BitVec.setWidth 64 (2144#32 +
                        kbj[(BitVec.setWidth 64 (96#32 + ((kbj[(BitVec.setWidth 64
                          (2912#32 + off_c + j_c)).toNat]'hidx_c0_lt) >>> (1 : Nat)))).toNat]'
                          h96_c0)).toNat = 2144 + r0.toNat := by
                      rw [hr0_c0_eq]
                      exact s13_sw64_add (base := 2144#32) (by decide)
                        (Nat.lt_of_lt_of_le hr0_lt hnc_le)
                    have h2144_r_c0 : (BitVec.setWidth 64 (2144#32 +
                        kbj[(BitVec.setWidth 64 (96#32 + ((kbj[(BitVec.setWidth 64
                          (2912#32 + off_c + j_c)).toNat]'hidx_c0_lt) >>> (1 : Nat)))).toNat]'
                          h96_c0)).toNat < kbj.length := by
                      rw [h2144_r_idx]; exact s13_2144_lt hr0_lt hnc_le hlen hkj_l
                    c0_hsplit
                    · clear hc; c0_hsteps!
                      have hm_eq := s13_set_congr (xs := kbj) h2144_r_idx
                        (congrArg (· ||| (2147483648 : BitVec 32))
                          (s13_get_congr (xs := kbj) h2144_r_idx h2144_r_c0
                            (s13_2144_lt hr0_lt hnc_le hlen hkj_l)))
                      erw [hm_eq] at hm; dsimp only [oldr] at hpr hm
                      rw [← s13_buf_get_eq (kbuf := kbj) (i := 2144 + r0.toNat)
                        (s13_2144_lt hr0_lt hnc_le hlen hkj_l)] at hpr hm
                      exact hJr0 (_, true) m ⟨invCore_set_meta hkj hr0_lt hpr.1 hpr.2, hm⟩
                    · c0_hsteps!; exact hJr0 (kbj, ch_j) mj ⟨hkj, hmj⟩
                  · c0_hsteps!; exact hJr0 (kbj, ch_j) mj ⟨hkj, hmj⟩
              · c0_hsteps!; exact hJlv (kbj, ch_j) mj ⟨hkj, hmj⟩
            · c0_hsteps!; exact hJlv (kbj, ch_j) mj ⟨hkj, hmj⟩
        · c0_hsteps!; exact hJ_l0 (kbj, ch_j) mj ⟨hkj, hmj⟩
      · intro Lj hLj; c0_hsteps!; exact hLj sz_c.toNat (ch_c, 0#32, ()) mc
          ⟨kbc, hkc, Nat.zero_le _, by simp, hmc⟩
    · c0_hsteps!; exact hJ_l0 (kbc, ch_c) mc ⟨hkc, hmc⟩

private theorem s13_m7_fixpoint_wp {Γ : Env} {pk : BitVec 64} {kbuf : List (BitVec 32)}
    {nc nv acap : BitVec 32} {R : Mem 64 → Prop} {Q : Post []} {X : XPost}
    (hlen : 2912 ≤ kbuf.length) (hnc_def : nc = kbuf[1]'(by omega))
    (hacap_def : acap = kbuf[15]'(by omega))
    (hnc_le : nc.toNat ≤ 256) (hnv_le : nv.toNat ≤ 64)
    (hRet : ∀ kbp mp, s13CoreInv kbuf nc kbp → (array (t := i32) pk kbp ⋆ R) mp → Q () mp)
    {kbj : List (BitVec 32)} {mj : Mem 64}
    (hkj : s13CoreInv kbuf nc kbj) (hmj : (array (t := i32) pk kbj ⋆ R) mj) :
    wp Γ Q X (s13M7FixE pk nc nv acap) mj := by
  let invCore := s13CoreInv kbuf nc
  have invCore_set_meta := @s13CoreInv_set_meta kbuf nc hnc_le
  dsimp only [s13M7FixE, s13SLet, s13SLd, s13SJF, s13SGrpB, s13DfltT, s13Dflt]
  c0_hsteps_nogrp
  refine wp_loop_group (ts := [i32, .bool])
    (fun rem (pass, _ch, ()) mp => ∃ kbp, invCore kbp ∧ pass.toNat ≤ nc.toNat ∧
      rem = nc.toNat - pass.toNat ∧ (array (t := i32) pk kbp ⋆ R) mp) ?_ ?_
  · rintro Lp remp ⟨pass, ch, ⟨⟩⟩ mp hLp ⟨kbp, hkp, hpass_le, rfl, hmp⟩
    c0_hsplit
    · clear hc; c0_hsplit
      · have hpass_lt : pass.toNat < nc.toNat := hc; clear hc
        have hpass1 : (pass + 1#32).toNat = pass.toNat + 1 := by
          have := hnc_le; have := hpass_lt; c0_bound
        c0_hsteps_nogrp
        refine wp_loop_group (ts := [.bool, i32])
          (fun rem (_chc, cid_c, ()) mc => ∃ kbc, invCore kbc ∧ cid_c.toNat ≤ nc.toNat ∧
            rem = cid_c.toNat ∧ (array (t := i32) pk kbc ⋆ R) mc) ?_ ?_
        · rintro Lc remc ⟨ch_c, cid_c, ⟨⟩⟩ mc hLc ⟨kbc, hkc, hc_le, rfl, hmc⟩
          have hkc_l := hkc.2.1
          c0_hsplit
          · have hcid_pos : 0 < cid_c.toNat := hc; clear hc
            have hcid1_lt : (cid_c - 1#32).toNat < nc.toNat := by
              rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]
              have := hcid_pos; have := hc_le; have := hnc_le; omega
            let c_i := cid_c - 1#32
            have hc_i_lt : c_i.toNat < nc.toNat := hcid1_lt
            have hbd_c := s13_2144_len_lt hc_i_lt hnc_le (by omega : 2912 ≤ kbc.length)
            have hc_2144_idx := s13_sw64_add (base := 2144#32) (by decide)
              (Nat.lt_of_lt_of_le hc_i_lt hnc_le)
            have hbd_c_c0 : (BitVec.setWidth 64 (2144#32 + c_i)).toNat < kbc.length := by
              rw [hc_2144_idx]; exact hbd_c
            let cm := kbc[2144 + c_i.toNat]'hbd_c
            c0_hsteps_nogrp
            refine wp_join_state1 (t := .bool) (α := List (BitVec 32) × Bool) (fun x => x.2)
              (fun x mc' => invCore x.1 ∧ (array (t := i32) pk x.1 ⋆ R) mc') ?_ ?_
            · rintro _ ⟨kbc', ch'⟩ mc' ⟨hkc', hmc'⟩
              c0_hsteps!
              exact hLc (cid_c - 1#32).toNat (ch', cid_c - 1#32, ()) mc'
                (by rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]
                    have := hcid_pos; have := hc_le; have := hnc_le; omega)
                ⟨kbc', hkc', by omega, rfl, hmc'⟩
            · intro Jcid hJcid
              have hc_2144_mod : (2144 + (2 ^ 32 - 1 + cid_c.toNat)) % 2 ^ 32 =
                  2144 + c_i.toNat := by
                rw [show (cid_c - 1#32).toNat = cid_c.toNat - 1 from
                  s13_cid_sub_toNat hcid_pos hc_le hnc_le]; omega
              have hbd_1888 := s13_1888_len_lt hc_i_lt hnc_le (by omega : 2912 ≤ kbc.length)
              have hc_1888_idx := s13_sw64_add (base := 1888#32) (by decide)
                (Nat.lt_of_lt_of_le hc_i_lt hnc_le)
              have hbd_1888_c0 : (BitVec.setWidth 64 (1888#32 + c_i)).toNat < kbc.length := by
                rw [hc_1888_idx]; exact hbd_1888
              c0_hsplit
              · clear hc
                let off_c := kbc[1888 + c_i.toNat]'hbd_1888
                let sz_c := cm &&& 0xFFFF#32
                have hlt28 := hkc.1.length_lt; have hlen_ge := hkc.1.length_ge
                obtain ⟨h15_eq, h15'⟩ := s13_k6_h15_eq hlen hacap_def hkc
                have hkcl := hkc.1.clause_ok (s13_k6_h1_lt hlen hnc_def hkc hc_i_lt)
                have hoff_sz : off_c.toNat + sz_c.toNat ≤ acap.toNat := by
                  have h1 := hkcl.1; rw [s13_buf_get_eq hbd_1888, s13_buf_get_eq hbd_c] at h1
                  dsimp only [off_c, sz_c, cm] at h1 ⊢; rw [h15'] at h1; exact h1
                have hno_ov1 : off_c.toNat + sz_c.toNat < 2 ^ 32 := by omega
                have hc_1888_mod := s13_cid_sub_mod hcid_pos hc_le hnc_le
                have hget_1888 : kbc[(1888 + (2 ^ 32 - 1 + cid_c.toNat)) % 2 ^ 32]'(by
                    rw [hc_1888_mod]; exact hbd_1888) = off_c :=
                  s13_get_congr hc_1888_mod _ hbd_1888
                have hget_2144 : kbc[(2144 + (2 ^ 32 - 1 + cid_c.toNat)) % 2 ^ 32]'(by
                    rw [hc_2144_mod]; exact hbd_c) = cm := s13_get_congr hc_2144_mod _ hbd_c
                have hget_1888_c0 : kbc[(BitVec.setWidth 64 (1888#32 + c_i)).toNat]'hbd_1888_c0 =
                    off_c := s13_get_congr hc_1888_idx hbd_1888_c0 hbd_1888
                have hget_2144_c0 : kbc[(BitVec.setWidth 64 (2144#32 + c_i)).toNat]'hbd_c_c0 =
                    cm := s13_get_congr hc_2144_idx hbd_c_c0 hbd_c
                c0_hsteps_nogrp
                refine wp_join_state1 (t := .bool) (α := List (BitVec 32) × Bool) (fun x => x.2)
                  (fun x mc' => invCore x.1 ∧ (array (t := i32) pk x.1 ⋆ R) mc') ?_ ?_
                · rintro _ ⟨kbc', ch'⟩ mc' ⟨hkc', hmc'⟩
                  dsimp only [Blocks.get, sz_c]
                  erw [hget_1888_c0, hget_2144_c0]
                  exact s13_m7_lvl0_lits_wp hlen hnc_def hacap_def hnc_le hnv_le hkc' hoff_sz hmc'
                    (fun xs mc'' h => by
                      rcases xs with ⟨ch'', ⟨⟩⟩
                      obtain ⟨kbc'', hk'', hm''⟩ := h
                      exact hJcid (kbc'', ch'') mc'' ⟨hk'', hm''⟩)
                · intro Jbr hJbr
                  c0_hsplit
                  · have hlrn_cm :
                        (kbc[2144 + c_i.toNat]?.getD 0#32 &&& 0x40000000#32) ≠ 0#32 := by
                      have hraw : (kbc[(2144 + (2 ^ 32 - 1 + cid_c.toNat)) % 2 ^ 32]'(by
                          rw [hc_2144_mod]; exact hbd_c) &&& 1073741824#32) ≠ 0#32 := hc
                      rw [s13_buf_get_eq hbd_c]
                      rw [s13_get_congr hc_2144_mod (by omega) hbd_c] at hraw; exact hraw
                    clear hc
                    have hbd_2400 : 2400 + c_i.toNat < kbc.length := by
                      have := hkc_l; have := hlen; have := hnc_le; have := hc_i_lt; omega
                    have hc_2400_idx := s13_sw64_add (base := 2400#32) (by decide)
                      (Nat.lt_of_lt_of_le hc_i_lt hnc_le)
                    have hbd_2400_c0 : (BitVec.setWidth 64 (2400#32 + c_i)).toNat < kbc.length := by
                      rw [hc_2400_idx]; exact hbd_2400
                    let na_c := kbc[2400 + c_i.toNat]'hbd_2400
                    have hoff_na' : off_c.toNat + sz_c.toNat + na_c.toNat ≤ acap.toNat := by
                      have h2 := hkcl.2 hlrn_cm
                      rw [s13_buf_get_eq hbd_1888, s13_buf_get_eq hbd_c, s13_buf_get_eq hbd_2400,
                        s13_buf_get_eq (by omega)] at h2
                      dsimp only [off_c, sz_c, na_c, cm] at h2 ⊢; rw [h15_eq] at h2; exact h2
                    have hno_ov2 : off_c.toNat + sz_c.toNat + na_c.toNat < 2 ^ 32 := by omega
                    c0_hsteps_nogrp
                    refine wp_join_state1 (t := .bool) (α := List (BitVec 32) × Bool)
                      (fun x => x.2) (fun x mc' => invCore x.1 ∧ (array (t := i32) pk x.1 ⋆ R) mc')
                      ?_ ?_
                    · rintro _ ⟨kbc', ch'⟩ mc' ⟨hkc', hmc'⟩
                      c0_hsteps!; exact hJbr (kbc', ch') mc' ⟨hkc', hmc'⟩
                    · intro J805 hJ805
                      c0_hsplit
                      · clear hc
                        have hc_2400_mod : (2400 + (2 ^ 32 - 1 + cid_c.toNat)) % 2 ^ 32 =
                            2400 + c_i.toNat := by
                          rw [show (cid_c - 1#32).toNat = cid_c.toNat - 1 from
                            s13_cid_sub_toNat hcid_pos hc_le hnc_le]; omega
                        c0_hsteps_nogrp
                        refine wp_loop_group (ts := [.bool, i32])
                          (fun remj (_chj, j_c, ()) mj2 => ∃ kbj2, invCore kbj2 ∧
                            j_c.toNat ≤ na_c.toNat ∧ remj = na_c.toNat - j_c.toNat ∧
                            (array (t := i32) pk kbj2 ⋆ R) mj2) ?_ ?_
                        · rintro Lj remj ⟨ch_j, j_c, ⟨⟩⟩ mj2 hLj
                            ⟨kbj2, hkj2, hj_le, rfl, hmj2⟩
                          have hkj2_l := hkj2.2.1
                          c0_hsplit
                          · have hj_lt : j_c.toNat < na_c.toNat := by
                              have hc' : j_c.toNat < (kbc[(2400 + (2 ^ 32 - 1 + cid_c.toNat)) %
                                  2 ^ 32]'(by rw [hc_2400_mod]; exact hbd_2400)).toNat := by
                                simpa [BitVec.toNat_ofNat] using hc
                              rwa [s13_get_congr hc_2400_mod (by omega) hbd_2400] at hc'
                            clear hc
                            have hj1 : (j_c + 1#32).toNat = j_c.toNat + 1 := by
                              have := hlt28; have := hlen_ge; have := h15'
                              have := hoff_na'; have := hj_lt; c0_bound
                            have hidx_lt : 2912 + off_c.toNat + sz_c.toNat + j_c.toNat <
                                kbj2.length := by
                              have := hkj2_l; have := hlt28; have := hlen_ge; have := h15'
                              have := hoff_na'; have := hj_lt; omega
                            have hidx_c0_lt : (BitVec.setWidth 64 (2912#32 +
                                kbc[(BitVec.setWidth 64 (1888#32 + c_i)).toNat]'hbd_1888_c0 +
                                (kbc[(BitVec.setWidth 64 (2144#32 + c_i)).toNat]'hbd_c_c0 &&&
                                  65535#32) + j_c)).toNat < kbj2.length := by
                              rw [hget_1888_c0, hget_2144_c0]
                              change (BitVec.setWidth 64 (2912#32 + off_c + sz_c + j_c)).toNat <
                                kbj2.length
                              have := hidx_lt; have := hno_ov1; have := hno_ov2; have := hlt28
                              have := hlen_ge; have := h15'; have := hoff_na'; have := hj_lt
                              c0_bound
                            let ant := kbj2[2912 + off_c.toNat + sz_c.toNat + j_c.toNat]'hidx_lt
                            have hant_c0_eq : kbj2[(BitVec.setWidth 64 (2912#32 +
                                kbc[(BitVec.setWidth 64 (1888#32 + c_i)).toNat]'hbd_1888_c0 +
                                (kbc[(BitVec.setWidth 64 (2144#32 + c_i)).toNat]'hbd_c_c0 &&&
                                  65535#32) + j_c)).toNat]'hidx_c0_lt = ant := by
                              refine s13_get_congr ?_ hidx_c0_lt hidx_lt
                              rw [hget_1888_c0, hget_2144_c0]
                              change (BitVec.setWidth 64 (2912#32 + off_c + sz_c + j_c)).toNat =
                                2912 + off_c.toNat + sz_c.toNat + j_c.toNat
                              have := hidx_lt; have := hno_ov1; have := hno_ov2; have := hlt28
                              have := hlen_ge; have := h15'; have := hoff_na'; have := hj_lt
                              c0_bound
                            c0_hsteps_nogrp
                            refine wp_join_state1 (t := .bool) (α := List (BitVec 32) × Bool)
                              (fun x => x.2) (fun x mj3 => invCore x.1 ∧
                                (array (t := i32) pk x.1 ⋆ R) mj3) ?_ ?_
                            · rintro _ ⟨kbj3, chj3⟩ mj3 ⟨hkj3, hmj3⟩
                              c0_hsteps!
                              exact hLj (na_c.toNat - (j_c + 1#32).toNat) (chj3, j_c + 1#32, ())
                                mj3 (by have := hj1; omega) ⟨kbj3, hkj3, by omega, rfl, hmj3⟩
                            · intro Jant hJant
                              have hc_2912_mod : (2912 + (kbc[(1888 + (2 ^ 32 - 1 +
                                  cid_c.toNat)) % 2 ^ 32]'(by
                                    rw [hc_1888_mod]; exact hbd_1888)).toNat
                                  + ((kbc[(2144 + (2 ^ 32 - 1 + cid_c.toNat)) % 2 ^ 32]'(by
                                    rw [hc_2144_mod]; exact hbd_c) &&& 65535).toNat) +
                                  j_c.toNat) % 2 ^ 32 =
                                  2912 + off_c.toNat + sz_c.toNat + j_c.toNat := by
                                rw [hget_1888, hget_2144]
                                exact s13_2912_mod_eq hlen_ge h15' hlt28 hoff_na' hj_lt
                              have hget_ant : kbj2[(2912 + (kbc[(1888 + (2 ^ 32 - 1 +
                                  cid_c.toNat)) % 2 ^ 32]'(by
                                    rw [hc_1888_mod]; exact hbd_1888)).toNat
                                  + ((kbc[(2144 + (2 ^ 32 - 1 + cid_c.toNat)) % 2 ^ 32]'(by
                                    rw [hc_2144_mod]; exact hbd_c) &&& 65535).toNat) +
                                  j_c.toNat) % 2 ^ 32]'(by rw [hc_2912_mod]; exact hidx_lt) =
                                  ant := s13_get_congr hc_2912_mod _ hidx_lt
                              c0_hsplit
                              · have hant_lt : ant.toNat < nc.toNat := by
                                  rw [← hget_ant]; simpa [s13_c1] using hc
                                clear hc
                                let olda := kbj2[2144 + ant.toNat]'(
                                  s13_2144_lt hant_lt hnc_le hlen hkj2_l)
                                have hpa := s13_km_core_or_pres olda
                                have h2144_a_idx : (BitVec.setWidth 64 (2144#32 +
                                    kbj2[(BitVec.setWidth 64 (2912#32 + kbc[(BitVec.setWidth 64
                                      (1888#32 + c_i)).toNat]'hbd_1888_c0 +
                                      (kbc[(BitVec.setWidth 64 (2144#32 + c_i)).toNat]'hbd_c_c0 &&&
                                        65535#32) + j_c)).toNat]'hidx_c0_lt)).toNat =
                                    2144 + ant.toNat := by
                                  rw [hant_c0_eq]
                                  exact s13_sw64_add (base := 2144#32) (by decide)
                                    (Nat.lt_of_lt_of_le hant_lt hnc_le)
                                have h2144_a_c0 : (BitVec.setWidth 64 (2144#32 +
                                    kbj2[(BitVec.setWidth 64 (2912#32 + kbc[(BitVec.setWidth 64
                                      (1888#32 + c_i)).toNat]'hbd_1888_c0 +
                                      (kbc[(BitVec.setWidth 64 (2144#32 + c_i)).toNat]'hbd_c_c0 &&&
                                        65535#32) + j_c)).toNat]'hidx_c0_lt)).toNat <
                                    kbj2.length := by
                                  rw [h2144_a_idx]; exact s13_2144_lt hant_lt hnc_le hlen hkj2_l
                                c0_hsplit
                                · clear hc; c0_hsteps!
                                  have hm_eq := s13_set_congr (xs := kbj2) h2144_a_idx
                                    (congrArg (· ||| (2147483648 : BitVec 32))
                                      (s13_get_congr (xs := kbj2) h2144_a_idx h2144_a_c0
                                        (s13_2144_lt hant_lt hnc_le hlen hkj2_l)))
                                  erw [hm_eq] at hm; dsimp only [olda] at hpa hm
                                  rw [← s13_buf_get_eq (kbuf := kbj2) (i := 2144 + ant.toNat)
                                    (s13_2144_lt hant_lt hnc_le hlen hkj2_l)] at hpa hm
                                  exact hJant (_, true) m
                                    ⟨invCore_set_meta hkj2 hant_lt hpa.1 hpa.2, hm⟩
                                · c0_hsteps!; exact hJant (kbj2, ch_j) mj2 ⟨hkj2, hmj2⟩
                              · c0_hsteps!; exact hJant (kbj2, ch_j) mj2 ⟨hkj2, hmj2⟩
                          · c0_hsteps!; exact hJ805 (kbj2, ch_j) mj2 ⟨hkj2, hmj2⟩
                        · intro Lj hLj; c0_hsteps!
                          exact hLj na_c.toNat (ch_c, 0#32, ()) mc
                            ⟨kbc, hkc, Nat.zero_le _, rfl, hmc⟩
                      · c0_hsteps!; exact hJ805 (kbc, ch_c) mc ⟨hkc, hmc⟩
                  · c0_hsteps!; exact hJbr (kbc, ch_c) mc ⟨hkc, hmc⟩
              · c0_hsteps!; exact hJcid (kbc, ch_c) mc ⟨hkc, hmc⟩
          · c0_hsteps!
            exact hLp (nc.toNat - (pass + 1#32).toNat) (pass + 1#32, ch_c, ()) mc
              (by omega) ⟨kbc, hkc, by omega, rfl, hmc⟩
        · intro Lc hLc; c0_hsteps!
          exact hLc nc.toNat (false, nc, ()) mp ⟨kbp, hkp, Nat.le_refl _, rfl, hmp⟩
      · c0_hsteps!; exact hRet kbp mp hkp hmp
    · c0_hsteps!; exact hRet kbp mp hkp hmp
  · intro Lp hLp; c0_hsteps!
    exact hLp nc.toNat (0#32, true, ()) mj ⟨kbj, hkj, Nat.zero_le _, by simp, hmj⟩

private def s13SSt {L rs} : Expr Val L rs → Expr Val L rs
  | .store _ _ k => k | _ => .hlt
private def s13SGrp0 {rs} : Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[]]) bs _ => match bs ((fun _ _ => True), ()) with | .cons b _ => b ()
  | _ => .hlt

private def s13M7TiE (pk : BitVec 64) (nc nv acap ti0 : BitVec 32)
    (Jinc : Cont [i32]) : Expr Val Cont [] :=
  let e := s13SLd nc (s13SLet (s13SLet (s13SLet (full_k6_core_m7_body Val Cont (pk, ())))))
  let e := s13SJF (s13SLet (s13SJF (s13SLet (s13SLd acap (s13SLet (s13SLet (s13SLet
    (s13SLd nv (s13SLet (s13SLet (s13SLet e)))))))))))
  let e := s13SLd 0#32 (s13SLet (s13SLet (s13SLet (s13SJF (s13SLet (s13SGrpB nc e))))))
  let e := match e with
    | .group (sig := [[.bits 32]]) _ body => body (Jinc, ())
    | _ => .hlt
  let e := s13SGrpB 0#32 (s13SJT (s13SLet e))
  let e := s13SJF (s13SLet e)
  let e := s13SLet (s13SLd 0#32 (s13SLet (s13SLet (s13SLet (s13SLet (s13SLd 0#32 (s13SLet
    (s13SLet (s13SLet (s13SLet (s13SSt (s13SLet (s13SLd 0#32 (s13SLet (s13SLet (s13SLet
      (s13SLet (s13SLet (s13SLet (s13SLet (s13SLet e)))))))))))))))))))))
  s13SGrpB ti0 (s13SLd 0#32 (s13SLet (s13SLet (s13SLet (s13SGrp0 e)))))

private theorem s13_m7_ti_loop_wp {Γ : Env} {pk : BitVec 64} {kbuf : List (BitVec 32)}
    {nc nv acap ti0 : BitVec 32} {R : Mem 64 → Prop} {Q : Post []} {X : XPost}
    {Jinc : Cont [i32]}
    (hlen : 2912 ≤ kbuf.length) (hnc_def : nc = kbuf[1]'(by omega))
    (hacap_def : acap = kbuf[15]'(by omega))
    (hnc_le : nc.toNat ≤ 256) (hnv_le : nv.toNat ≤ 64)
    (hti0 : ti0.toNat ≤ 64)
    (hJinc : ∀ xs mf2, (match xs with
      | (_i2, ()) => ∃ kbf2, s13CoreInv kbuf nc kbf2 ∧ (array (t := i32) pk kbf2 ⋆ R) mf2) →
      Jinc xs mf2)
    {kbj : List (BitVec 32)} {mj : Mem 64}
    (hkj : s13CoreInv kbuf nc kbj) (hmj : (array (t := i32) pk kbj ⋆ R) mj) :
    wp Γ Q X (s13M7TiE pk nc nv acap ti0 Jinc) mj := by
  let invCore := s13CoreInv kbuf nc
  have invCore_set_meta := @s13CoreInv_set_meta kbuf nc hnc_le
  have invCore_set_flags := @s13CoreInv_set_flags kbuf nc
  dsimp only [s13M7TiE, full_k6_core_m7_body, s13SLet, s13SLd, s13SSt, s13SJF, s13SJT,
    s13SGrpB, s13SGrp0, s13DfltT, s13Dflt]
  c0_hsteps_nogrp
  refine wp_loop_group (ts := [i32])
    (fun rem (tic, ()) mt => ∃ kbt, invCore kbt ∧ tic.toNat ≤ 64 ∧ rem = tic.toNat ∧
      (array (t := i32) pk kbt ⋆ R) mt) ?_ ?_
  · rintro Lt remt ⟨tic, ⟨⟩⟩ mt hLt ⟨kbt, hkt, htic, rfl, hmt⟩
    have hkt_l := hkt.2.1
    c0_hsplit
    · have ht_pos : 0 < tic.toNat := hc; clear hc
      let t1 := tic - 1#32
      have ht1_lt : t1.toNat < 64 := by
        dsimp only [t1]; rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
      have ht1_dec : t1.toNat < tic.toNat := by
        dsimp only [t1]; rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
      c0_hsplit
      · c0_hsteps!; exact hLt t1.toNat (t1, ()) mt ht1_dec ⟨kbt, hkt, by omega, rfl, hmt⟩
      · have ht_352_mod : (352 + (2 ^ 32 - 1 + tic.toNat)) % 2 ^ 32 = 352 + t1.toNat := by
          have : t1.toNat = tic.toNat - 1 := by
            dsimp only [t1]; rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
          rw [this]; omega
        have ht_352_c0 : (BitVec.setWidth 64 (352#32 + (tic - 1#32))).toNat = 352 + t1.toNat := by
          change (BitVec.setWidth 64 (352#32 + t1)).toNat = 352 + t1.toNat; c0_bound
        have ht_352_bd_mod : (352 + (2 ^ 32 - 1 + tic.toNat)) % 2 ^ 32 < kbt.length := by
          rw [ht_352_mod]; omega
        have ht_352_bd_c0 : (BitVec.setWidth 64 (352#32 + (tic - 1#32))).toNat < kbt.length := by
          rw [ht_352_c0]; omega
        let v_t := (kbt[352 + t1.toNat]'(by omega)) >>> (1 : Nat)
        have hvt_lt : v_t.toNat < nv.toNat := by
          refine Nat.lt_of_not_le (show ¬nv.toNat ≤ v_t.toNat from ?_)
          dsimp only [v_t]; rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
            ← s13_get_congr ht_352_mod ht_352_bd_mod (by omega)]
          simpa [Nat.reducePow] using hc
        clear hc
        have hget_352_c0 : kbt[(BitVec.setWidth 64 (352#32 + (tic - 1#32))).toNat]'ht_352_bd_c0 =
            kbt[352 + t1.toNat]'(by omega) := s13_get_congr ht_352_c0 ht_352_bd_c0 (by omega)
        have h416_t_eq : (BitVec.setWidth 64 (416#32 +
            (kbt[(BitVec.setWidth 64 (352#32 + (tic - 1#32))).toNat]'ht_352_bd_c0 >>>
              (1 : Nat)))).toNat = 416 + v_t.toNat := by
          rw [hget_352_c0]; change (BitVec.setWidth 64 (416#32 + v_t)).toNat = 416 + v_t.toNat
          have := hvt_lt; have := hnv_le; c0_bound
        have h416_t_c0 : (BitVec.setWidth 64 (416#32 +
            (kbt[(BitVec.setWidth 64 (352#32 + (tic - 1#32))).toNat]'ht_352_bd_c0 >>>
              (1 : Nat)))).toNat < kbt.length := by rw [h416_t_eq]; omega
        have h96_t_eq : (BitVec.setWidth 64 (96#32 +
            (kbt[(BitVec.setWidth 64 (352#32 + (tic - 1#32))).toNat]'ht_352_bd_c0 >>>
              (1 : Nat)))).toNat = 96 + v_t.toNat := by
          rw [hget_352_c0]; change (BitVec.setWidth 64 (96#32 + v_t)).toNat = 96 + v_t.toNat
          have := hvt_lt; have := hnv_le; c0_bound
        have h96_t_c0 : (BitVec.setWidth 64 (96#32 +
            (kbt[(BitVec.setWidth 64 (352#32 + (tic - 1#32))).toNat]'ht_352_bd_c0 >>>
              (1 : Nat)))).toNat < kbt.length := by rw [h96_t_eq]; omega
        c0_hsplit
        · c0_hsteps!; exact hLt t1.toNat (t1, ()) mt ht1_dec ⟨kbt, hkt, by omega, rfl, hmt⟩
        · clear hc
          have hm1_eq := s13_set_congr (xs := kbt) h416_t_eq
            (congrArg (· &&& ~~~(2 : BitVec 32))
              (s13_get_congr (xs := kbt) h416_t_eq h416_t_c0 (by omega)))
          c0_hsplit
          · c0_hsteps!; erw [hm1_eq] at hm
            exact hLt t1.toNat (t1, ()) _ ht1_dec
              ⟨_, invCore_set_flags hkt (v := v_t.toNat) (by omega) _, by omega, rfl, hm⟩
          · erw [hm1_eq] at hm
            let kbt1 := kbt.set (416 + v_t.toNat) ((kbt[416 + v_t.toNat]'(by omega)) &&& ~~~2#32)
            have hkt1 : invCore kbt1 := invCore_set_flags hkt (v := v_t.toNat) (by omega) _
            have hkt1_l : kbt1.length = kbuf.length := by simp [kbt1, hkt_l]
            have hkbt1_96 : kbt1[96 + v_t.toNat]'(by omega) = kbt[96 + v_t.toNat]'(by omega) :=
              List.getElem_set_ne (by omega) _
            have hrsn : (kbt1[96 + v_t.toNat]'(by omega)).toNat < nc.toNat := by
              have hvt_div : v_t.toNat = (kbt[352 + t1.toNat]'(by omega)).toNat / 2 := by
                dsimp only [v_t]; rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
              have hk_raw :
                  (kbt[(352 + (2 ^ 32 - 1 + tic.toNat)) % 2 ^ 32]'ht_352_bd_mod).toNat / 2 =
                    v_t.toNat := by
                rw [s13_get_congr ht_352_mod ht_352_bd_mod (by omega)]; exact hvt_div.symm
              have h416_ne : (416 + (kbt[(352 + (2 ^ 32 - 1 + tic.toNat)) % 2 ^ 32]'
                  ht_352_bd_mod).toNat / 2) % 2 ^ 32 ≠
                  (96 + (kbt[(352 + (2 ^ 32 - 1 + tic.toNat)) % 2 ^ 32]'
                  ht_352_bd_mod).toNat / 2) % 2 ^ 32 := by rw [hk_raw]; omega
              have h96_idx_eq : (96 + (kbt[(352 + (2 ^ 32 - 1 + tic.toNat)) % 2 ^ 32]'
                  ht_352_bd_mod).toNat / 2) % 2 ^ 32 = 96 + v_t.toNat := by rw [hk_raw]; omega
              have hc' := hc
              erw [List.getElem_set_ne h416_ne] at hc'
              erw [s13_get_congr h96_idx_eq _ (by omega)] at hc'
              rw [hkbt1_96]; exact Nat.lt_of_not_le (by simpa using hc')
            clear hc
            let rsn := kbt1[96 + v_t.toNat]'(by omega)
            have hget_raw_rsn : ∀ hbd,
                (kbt.set (BitVec.setWidth 64 ((416 : BitVec 32) + (kbt[(BitVec.setWidth 64
                  ((352 : BitVec 32) + (tic - (1 : BitVec 32)))).toNat]'ht_352_bd_c0 >>>
                    (1 : Nat)))).toNat
                  (kbt[(BitVec.setWidth 64 ((416 : BitVec 32) + (kbt[(BitVec.setWidth 64
                    ((352 : BitVec 32) + (tic - (1 : BitVec 32)))).toNat]'ht_352_bd_c0 >>>
                      (1 : Nat)))).toNat]'h416_t_c0 &&& ~~~(2 : BitVec 32)))[(BitVec.setWidth 64
                  ((96 : BitVec 32) + (kbt[(BitVec.setWidth 64 ((352 : BitVec 32) +
                    (tic - (1 : BitVec 32)))).toNat]'ht_352_bd_c0 >>> (1 : Nat)))).toNat]'hbd =
                  rsn := by
              intro hbd; erw [List.getElem_set_ne (by erw [h416_t_eq, h96_t_eq]; omega)]
              exact (s13_get_congr h96_t_eq _ _).trans hkbt1_96.symm
            simp only [hget_raw_rsn]
            clear hm1_eq hget_raw_rsn
            have hk_rsn := hkt1.1.clause_ok (s13_k6_h1_lt hlen hnc_def hkt1 hrsn)
            let oldmr := kbt1[2144 + rsn.toNat]'(s13_2144_len_lt hrsn hnc_le (by omega))
            have hpr := s13_km_core_or_pres oldmr
            have h2144_r_eq := s13_sw64_add (base := 2144#32) (by decide)
              (Nat.lt_of_lt_of_le hrsn hnc_le)
            have h1888_r_eq := s13_sw64_add (base := 1888#32) (by decide)
              (Nat.lt_of_lt_of_le hrsn hnc_le)
            have h2144_r_c0 : (BitVec.setWidth 64 (2144#32 + rsn)).toNat < kbt1.length := by
              rw [h2144_r_eq]; exact s13_2144_len_lt hrsn hnc_le (by omega)
            have h1888_r_c0 : (BitVec.setWidth 64 (1888#32 + rsn)).toNat < kbt1.length := by
              rw [h1888_r_eq]; exact s13_1888_len_lt hrsn hnc_le (by omega)
            obtain ⟨h15_k1eq, h15_k1⟩ := s13_k6_h15_eq hlen hacap_def hkt1
            have hrsn_nw : (kbt1[1888 + rsn.toNat]'(s13_1888_len_lt hrsn hnc_le (by omega))).toNat +
                ((oldmr ||| 0x80000000#32) &&& 0xFFFF#32).toNat < 2 ^ 32 := by
              rw [s13_buf_get_eq (s13_1888_len_lt hrsn hnc_le (by omega)),
                s13_buf_get_eq (s13_2144_len_lt hrsn hnc_le (by omega)), h15_k1] at hk_rsn
              dsimp only [oldmr, rsn] at hpr hk_rsn ⊢; rw [hpr.1]
              have := hkt1.1.length_lt; have := hkt1.1.length_ge; omega
            have hm2_eq := s13_set_congr (xs := kbt1) h2144_r_eq
              (congrArg (· ||| (2147483648 : BitVec 32))
                (s13_get_congr (xs := kbt1) h2144_r_eq h2144_r_c0
                  (s13_2144_len_lt hrsn hnc_le (by omega))))
            let roff := kbt1[1888 + rsn.toNat]'(s13_1888_len_lt hrsn hnc_le (by omega))
            let rsz := (oldmr ||| 0x80000000#32) &&& 0xFFFF#32
            change (array (t := i32) pk kbt1 ⋆ R) m at hm
            c0_hsteps_nogrp; erw [hm2_eq] at hm
            let kbt2 := kbt1.set (2144 + rsn.toNat) (oldmr ||| 0x80000000#32)
            have hkt2 : invCore kbt2 := invCore_set_meta hkt1 hrsn
              (by rw [s13_buf_get_eq (s13_2144_len_lt hrsn hnc_le (by omega))]; exact hpr.1)
              (by rw [s13_buf_get_eq (s13_2144_len_lt hrsn hnc_le (by omega))]; exact hpr.2)
            have hkbt2_l : kbt2.length = kbuf.length := by simp [kbt2, hkt1_l]
            have h2144_r_c0_2 : (BitVec.setWidth 64 (2144 + rsn)).toNat < kbt2.length := by
              rw [hkbt2_l, ← hkt1_l]; exact h2144_r_c0
            change (array (t := i32) pk kbt2 ⋆ R) m at hm
            c0_hsteps_nogrp
            have hget_raw_roff : ∀ hbd, (kbt1.set (BitVec.setWidth 64 (2144 + rsn)).toNat
                (kbt1[(BitVec.setWidth 64 (2144 + rsn)).toNat]'h2144_r_c0 |||
                  2147483648))[(BitVec.setWidth 64 (1888 + rsn)).toNat]'hbd = roff := by
              intro hbd
              have hne : (BitVec.setWidth 64 (2144 + rsn)).toNat ≠
                  (BitVec.setWidth 64 (1888 + rsn)).toNat := by
                change (BitVec.setWidth 64 (2144#32 + kbt1[96 + v_t.toNat])).toNat ≠
                  (BitVec.setWidth 64 (1888#32 + kbt1[96 + v_t.toNat])).toNat
                rw [h2144_r_eq, h1888_r_eq]; simp only [BitVec.toNat_ofNat]; omega
              erw [List.getElem_set_ne hne hbd]
              exact s13_get_congr h1888_r_eq _ _
            simp only [hget_raw_roff]
            have h2144_r_mod := s13_add_mod_lt (c := 2144) (by decide) hrsn hnc_le
            have hkbt2_2144 : kbt2[(2144 + rsn.toNat) % 4294967296]'(by
                rw [hkbt2_l, h2144_r_mod]; exact s13_2144_len_lt hrsn hnc_le (by omega)) =
                oldmr ||| 0x80000000#32 := by
              rw [s13_get_congr h2144_r_mod (by
                rw [hkbt2_l, h2144_r_mod]; exact s13_2144_len_lt hrsn hnc_le (by omega))
                (by rw [hkbt2_l]; exact s13_2144_len_lt hrsn hnc_le (by omega))]
              exact List.getElem_set_self
                (by rw [List.length_set, hkt1_l]; exact s13_2144_len_lt hrsn hnc_le (by omega))
            refine wp_join0 (fun mr => ∃ kbr, invCore kbr ∧ (array (t := i32) pk kbr ⋆ R) mr) ?_ ?_
            · intro _ mr ⟨kbr, hkr, hmr⟩; c0_hsteps!
              exact hLt t1.toNat (t1, ()) mr ht1_dec ⟨kbr, hkr, by omega, rfl, hmr⟩
            · intro Jg hJg
              c0_hsplit
              · have hrsz_bd : roff.toNat + rsz.toNat ≤ acap.toNat := by
                  have hmod : (roff.toNat + rsz.toNat) % 4294967296 = roff.toNat + rsz.toNat :=
                    Nat.mod_eq_of_lt hrsn_nw
                  have hc' := hc
                  erw [hkbt2_2144] at hc'
                  change (roff.toNat + rsz.toNat) % 4294967296 ≤ acap.toNat at hc'
                  rwa [hmod] at hc'
                clear hc; c0_hsteps_nogrp
                refine wp_loop_group (ts := [i32]) (fun remj (jr, ()) mr =>
                  ∃ kbr, invCore kbr ∧ jr.toNat ≤ rsz.toNat ∧ remj = rsz.toNat - jr.toNat ∧
                    (array (t := i32) pk kbr ⋆ R) mr) ?_ ?_
                · rintro Lr remr ⟨jr, ⟨⟩⟩ mr hLr ⟨kbr, hkr, hjr_le, rfl, hmr⟩
                  have hkr_l := hkr.2.1
                  c0_hsplit
                  · have hjr_lt : jr.toNat < rsz.toNat := by
                      have hc' := hc
                      erw [hkbt2_2144] at hc'
                      change jr.toNat < rsz.toNat at hc'
                      exact hc'
                    clear hc
                    have hrsz_lt : rsz.toNat < 65536 := by
                      dsimp only [rsz]; rw [BitVec.toNat_and]
                      exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
                    have hj1 : (jr + 1#32).toNat = jr.toNat + 1 := by
                      have := hrsz_lt; have := hjr_lt; c0_bound
                    have h15_kr := (s13_k6_h15_eq hlen hacap_def hkr).2
                    have har_r : 2912 + roff.toNat + jr.toNat < kbr.length := by
                      have := hkr.1.length_ge; omega
                    have h2912_r_c0 : (BitVec.setWidth 64 (2912#32 + roff + jr)).toNat <
                        kbr.length := by have := har_r; have := hkr.1.length_lt; c0_bound
                    c0_hsteps_nogrp
                    refine wp_join0 (fun mr1 => ∃ kbr1, invCore kbr1 ∧
                        (array (t := i32) pk kbr1 ⋆ R) mr1) ?_ ?_
                    · intro _ mr1 ⟨kbr1, hkr1, hmr1⟩; c0_hsteps!
                      exact hLr (rsz.toNat - (jr + 1#32).toNat) (jr + 1#32, ()) mr1
                        (by have := hj1; omega) ⟨kbr1, hkr1, by have := hj1; omega, rfl, hmr1⟩
                    · intro Jlv hJlv
                      c0_hsplit
                      · have hlv_lt : ((kbr[2912 + roff.toNat + jr.toNat]'har_r) >>>
                            (1 : Nat)).toNat < nv.toNat := by
                          have har_mod : (2912 + roff.toNat + jr.toNat) % 2 ^ 32 =
                              2912 + roff.toNat + jr.toNat := by
                            have := har_r; have := hkr.1.length_lt; omega
                          rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
                            ← s13_get_congr har_mod (by rw [har_mod]; exact har_r) har_r]
                          simpa [Nat.reducePow] using hc
                        clear hc
                        have hget_lr : kbr[(BitVec.setWidth 64 (2912#32 + roff + jr)).toNat]'
                            h2912_r_c0 = kbr[2912 + roff.toNat + jr.toNat]'har_r :=
                          s13_get_congr (by have := har_r; have := hkr.1.length_lt; c0_bound) _ _
                        have h416_r_eq : (BitVec.setWidth 64 (416#32 +
                            (kbr[(BitVec.setWidth 64 (2912#32 + roff + jr)).toNat]'h2912_r_c0 >>>
                              (1 : Nat)))).toNat = 416 + ((kbr[2912 + roff.toNat +
                                jr.toNat]'har_r) >>> (1 : Nat)).toNat := by
                          rw [hget_lr]; have := hlv_lt; have := hnv_le; c0_bound
                        have h416_r_c0 : (BitVec.setWidth 64 (416#32 +
                            (kbr[(BitVec.setWidth 64 (2912#32 + roff + jr)).toNat]'h2912_r_c0 >>>
                              (1 : Nat)))).toNat < kbr.length := by rw [h416_r_eq]; omega
                        c0_hsplit
                        · c0_hsteps!
                          have hmr_eq := s13_set_congr (xs := kbr) h416_r_eq
                            (congrArg (· ||| (2 : BitVec 32))
                              (s13_get_congr (xs := kbr) h416_r_eq h416_r_c0 (by omega)))
                          erw [hmr_eq] at hm
                          exact hJlv _ ⟨_, invCore_set_flags hkr
                            (v := ((kbr[2912 + roff.toNat + jr.toNat]'har_r) >>> (1 : Nat)).toNat)
                            (by omega) _, hm⟩
                        · c0_hsteps!; exact hJlv mr ⟨kbr, hkr, hmr⟩
                      · c0_hsteps!; exact hJlv mr ⟨kbr, hkr, hmr⟩
                  · c0_hsteps!; exact hJg mr ⟨kbr, hkr, hmr⟩
                · intro Lr hLr; c0_hsteps!
                  exact hLr rsz.toNat (0#32, ()) _ ⟨kbt2, hkt2, Nat.zero_le _, by simp, hm⟩
              · c0_hsteps!; exact hJg _ ⟨kbt2, hkt2, by assumption⟩
    · c0_hsteps_nogrp
      refine wp_loop_group (ts := [i32])
        (fun rem (i2, ()) mf2 => ∃ kbf2, invCore kbf2 ∧ i2.toNat ≤ nv.toNat ∧
          rem = nv.toNat - i2.toNat ∧ (array (t := i32) pk kbf2 ⋆ R) mf2) ?_ ?_
      · rintro Lf2 remf2 ⟨if2, ⟨⟩⟩ mf2 hLf2 ⟨kbf2, hkf2, hif2, rfl, hmf2⟩
        have hkf2_l := hkf2.2.1
        c0_hsplit
        · have hi_lt : if2.toNat < nv.toNat := hc; clear hc
          have hif2_s : (if2 + 1#32).toNat = if2.toNat + 1 := by
            have := hnv_le; have := hi_lt; c0_bound
          have h416_i2 : (BitVec.setWidth 64 (416#32 + if2)).toNat = 416 + if2.toNat := by
            have := hnv_le; have := hi_lt; c0_bound
          c0_hsteps!; erw [s13_set_congr h416_i2 rfl] at hm
          exact hLf2 (nv.toNat - (if2 + 1#32).toNat) (if2 + 1#32, ()) _ (by omega)
            ⟨_, invCore_set_flags hkf2 (by omega) _, by omega, rfl, hm⟩
        · c0_hsteps!; exact hJinc (if2, ()) mf2 ⟨kbf2, hkf2, hmf2⟩
      · intro Lf2 hLf2; c0_hsteps!
        exact hLf2 nv.toNat (0#32, ()) mt ⟨kbt, hkt, Nat.zero_le _, by simp, hmt⟩
  · intro Lt hLt; c0_hsteps!; exact hLt ti0.toNat (ti0, ()) mj ⟨kbj, hkj, hti0, rfl, hmj⟩

/-- Certifies `fullK6CoreM7Spec` for Step-13 `full_k6_core_m7` (`F-P0-1`). -/
theorem full_k6_core_m7_s13_wp (Γ : Env) :
    ∀ a m Q X, fullK6CoreM7Spec a m Q X → Func.wp Γ full_k6_core_m7_body a m Q X := by
  rintro ⟨pk, ⟨⟩⟩ m0 Q X hSpec
  obtain ⟨kbuf, R, hok0, hm0, hQ⟩ := fullK6CoreM7Spec_elim hSpec
  have hlen := hok0.base_ge
  let nc := kbuf[1]'(by omega); let nv := kbuf[0]'(by omega); let acap := kbuf[15]'(by omega)
  unfold Func.wp full_k6_core_m7_body; c0_hsplit
  · c0_hsteps!; exact hQ kbuf m0 rfl (fun _ _ _ => rfl) (fun _ _ => ⟨rfl, rfl⟩) hm0
  · have hnc_le : nc.toNat ≤ 256 := Nat.le_of_not_lt (by simpa [nc] using hc); clear hc
    c0_hsplit
    · c0_hsteps!; exact hQ kbuf m0 rfl (fun _ _ _ => rfl) (fun _ _ => ⟨rfl, rfl⟩) hm0
    · have hnv_le : nv.toNat ≤ 64 := Nat.le_of_not_lt (by simpa [nv] using hc); clear hc
      let invCore := s13CoreInv kbuf nc
      have invCore_set_meta := @s13CoreInv_set_meta kbuf nc hnc_le
      have invCore_set_flags := @s13CoreInv_set_flags kbuf nc
      c0_hsteps_nogrp
      refine wp_loop_group (ts := [i32])
        (fun rem (i, ()) mi => ∃ kbi, invCore kbi ∧ i.toNat ≤ nc.toNat ∧
          rem = nc.toNat - i.toNat ∧ (array (t := i32) pk kbi ⋆ R) mi) ?_ ?_
      · rintro L1 rem1 ⟨i1, ⟨⟩⟩ m1 hL1 ⟨kb1, hk1, hi1_le, rfl, hm1⟩
        have hk1_l := hk1.2.1; c0_hsplit
        · have hi1_lt : i1.toNat < nc.toNat := hc; clear hc
          have hi1_succ : (i1 + 1#32).toNat = i1.toNat + 1 := by
            have := hnc_le; have := hi1_lt; c0_bound
          have hbd1 : 2144 + i1.toNat < kb1.length := by
            have := hk1_l; have := hlen; have := hnc_le; have := hi1_lt; omega
          let oldm := kb1[2144 + i1.toNat]'hbd1
          have hpres := s13_km_core_clear_pres oldm; c0_hsteps!
          have hidx1 : (BitVec.setWidth 64 (2144 + i1)).toNat = 2144 + i1.toNat := by
            have := hnc_le; have := hi1_lt; c0_bound
          have hkb1_eq : kb1.set (BitVec.setWidth 64 (2144 + i1)).toNat
                (kb1[(BitVec.setWidth 64 (2144 + i1)).toNat]'(by omega) &&& ~~~2147483648) =
              kb1.set (2144 + i1.toNat) (oldm &&& ~~~2147483648#32) :=
            s13_set_congr hidx1 (congrArg (· &&& ~~~2147483648#32) (s13_get_congr hidx1 _ _))
          rw [hkb1_eq] at hm; dsimp only [oldm] at hpres hm
          rw [← s13_buf_get_eq hbd1] at hpres hm
          exact hL1 (nc.toNat - (i1 + 1#32).toNat) (i1 + 1#32, ()) _ (by omega)
            ⟨_, invCore_set_meta hk1 hi1_lt hpres.1 hpres.2, by omega, rfl, hm⟩
        · have hi1_nc : i1 = nc := BitVec.eq_of_toNat_eq (by
            have : ¬i1.toNat < nc.toNat := hc; omega)
          clear hc; c0_hsteps_nogrp
          refine wp_join_state1 (t := i32) (α := List (BitVec 32) × BitVec 32) (fun x => x.2)
            (fun x mj => invCore x.1 ∧ (array (t := i32) pk x.1 ⋆ R) mj) ?_ ?_
          · rintro _ ⟨kbj, _⟩ mj ⟨hkj, hmj⟩
            exact s13_m7_fixpoint_wp hlen rfl rfl hnc_le hnv_le
              (fun kbp mp hkp hmp => hQ kbp mp hkp.2.1 hkp.2.2.1
                (fun cid hcid => hkp.2.2.2 cid
                  (by rw [s13_buf_get_eq (by omega)] at hcid; exact hcid)) hmp) hkj hmj
          · intro Jinc hJinc
            let inc := kb1[7]'(by omega)
            c0_hsplit
            · have hinc : inc.toNat < nc.toNat :=
                Nat.lt_of_not_le (by simpa [s13_c1, s13_c7] using hc)
              clear hc
              refine wp_loop_group (ts := [i32]) (fun rem (i, ()) mf =>
                ∃ kbf, invCore kbf ∧ i.toNat ≤ nv.toNat ∧ rem = nv.toNat - i.toNat ∧
                  (array (t := i32) pk kbf ⋆ R) mf) ?_ ?_
              · rintro Lf remf ⟨if1, ⟨⟩⟩ mf1 hLf ⟨kbf1, hkf1, hif1, rfl, hmf1⟩
                have hkf1_l := hkf1.2.1
                c0_hsplit
                · have hi_lt : if1.toNat < nv.toNat := hc; clear hc
                  have hif1_s : (if1 + 1#32).toNat = if1.toNat + 1 := by
                    have := hnv_le; have := hi_lt; c0_bound
                  have h416_i : (BitVec.setWidth 64 (416#32 + if1)).toNat = 416 + if1.toNat := by
                    have := hnv_le; have := hi_lt; c0_bound
                  c0_hsteps!; erw [s13_set_congr h416_i rfl] at hm
                  exact hLf (nv.toNat - (if1 + 1#32).toNat) (if1 + 1#32, ()) _ (by omega)
                    ⟨_, invCore_set_flags hkf1 (by omega) _, by omega, rfl, hm⟩
                · clear hc
                  have hkb_inc := hkf1.1.clause_ok (s13_k6_h1_lt hlen rfl hkf1 hinc)
                  let oldmi := kbf1[2144 + inc.toNat]'(s13_2144_len_lt hinc hnc_le (by omega))
                  have hpmi := s13_km_core_or_pres oldmi
                  have hlt28 := hkf1.1.length_lt; have hlen_ge := hkf1.1.length_ge
                  have h15 := (s13_k6_h15_eq hlen rfl hkf1).2
                  have hinc_sz_nw : (kbf1[1888 + inc.toNat]'(
                        s13_1888_len_lt hinc hnc_le (by omega))).toNat +
                      ((oldmi ||| 0x80000000#32) &&& 0xFFFF#32).toNat < 2 ^ 32 := by
                    rw [s13_buf_get_eq (s13_1888_len_lt hinc hnc_le (by omega)),
                      s13_buf_get_eq (s13_2144_len_lt hinc hnc_le (by omega)), h15] at hkb_inc
                    dsimp only [oldmi] at hpmi ⊢; rw [hpmi.1]; omega
                  have hk7_bd : (7 : BitVec 64).toNat < kb1.length := by
                    rw [hk1_l]; change 7 % 2 ^ 64 < kbuf.length; omega
                  have hk7_lt : (kb1[(7 : BitVec 64).toNat]'hk7_bd).toNat < nc.toNat := hinc
                  have h1888_inc_c0 :
                      (BitVec.setWidth 64 (1888#32 + kb1[(7 : BitVec 64).toNat]'hk7_bd)).toNat <
                        kbf1.length := by
                    have := hkf1_l; have := hlen; have := hnc_le; have := hk7_lt; c0_bound
                  have h2144_inc_c0 :
                      (BitVec.setWidth 64 (2144#32 + kb1[(7 : BitVec 64).toNat]'hk7_bd)).toNat <
                        kbf1.length := by
                    have := hkf1_l; have := hlen; have := hnc_le; have := hk7_lt; c0_bound
                  have h2144_set_bd :
                      (BitVec.setWidth 64 (2144 + kb1[(BitVec.ofNat 64 7).toNat]'hk7_bd)).toNat <
                        (kbf1.set
                          (BitVec.setWidth 64 (2144 + kb1[(BitVec.ofNat 64 7).toNat]'hk7_bd)).toNat
                          (kbf1[(BitVec.setWidth 64
                            (2144 + kb1[(BitVec.ofNat 64 7).toNat]'hk7_bd)).toNat]'h2144_inc_c0
                            ||| 2147483648)).length := by
                    rw [List.length_set]; exact h2144_inc_c0
                  c0_hsteps_nogrp
                  refine wp_join0 (fun mj => ∃ kbj, invCore kbj ∧
                      (array (t := i32) pk kbj ⋆ R) mj) ?_ ?_
                  · intro _ mj ⟨kbj, hkj, hmj⟩
                    have hkj_l := hkj.2.1; c0_hsteps_nogrp
                    refine wp_join_state_pure (ts := [i32]) (α := BitVec 32) (fun ti => (ti, ()))
                      (fun ti => ti.toNat ≤ 64) ?_ ?_
                    · intro _ ti hti
                      exact s13_m7_ti_loop_wp hlen rfl rfl hnc_le hnv_le hti
                        (fun xs mf2 ⟨kbf2, hkf2, hmf2⟩ => by
                          rcases xs with ⟨i2, ⟨⟩⟩; exact hJinc (kbf2, i2) mf2 ⟨hkf2, hmf2⟩)
                        hkj hmj
                    · intro Jti hJti; c0_hsplit
                      · c0_hsteps!; exact hJti 64#32 (by decide)
                      · c0_hsteps!; exact hJti _ (by c0_bound)
                  · intro JincCl hJincCl
                    let off_i := kbf1[1888 + inc.toNat]'(s13_1888_len_lt hinc hnc_le (by omega))
                    let sz_i := (oldmi ||| 0x80000000#32) &&& 0xFFFF#32
                    have h2144_idx := s13_sw64_add (base := 2144#32) (by decide)
                      (Nat.lt_of_lt_of_le hinc hnc_le)
                    have h1888_idx := s13_sw64_add (base := 1888#32) (by decide)
                      (Nat.lt_of_lt_of_le hinc hnc_le)
                    have h2144_inc_eq : (BitVec.setWidth 64
                        (2144#32 + kb1[7 % 2 ^ 64]'hk7_bd)).toNat = 2144 + inc.toNat := h2144_idx
                    have h1888_inc_eq : (BitVec.setWidth 64
                        (1888#32 + kb1[7 % 2 ^ 64]'hk7_bd)).toNat = 1888 + inc.toNat := h1888_idx
                    have hm_s_eq := s13_set_congr (xs := kbf1) h2144_inc_eq
                      (congrArg (· ||| (2147483648 : BitVec 32))
                        (s13_get_congr (xs := kbf1) h2144_inc_eq h2144_inc_c0
                          (s13_2144_len_lt hinc hnc_le (by omega))))
                    erw [hm_s_eq] at hm
                    let kbf1s := kbf1.set (2144 + inc.toNat) (oldmi ||| 0x80000000#32)
                    have h_kbf1s : invCore kbf1s := invCore_set_meta hkf1 hinc
                      (by
                        rw [s13_buf_get_eq (s13_2144_len_lt hinc hnc_le (by omega))]; exact hpmi.1)
                      (by
                        rw [s13_buf_get_eq (s13_2144_len_lt hinc hnc_le (by omega))]; exact hpmi.2)
                    have hk1s_l : kbf1s.length = kbuf.length := by simp [kbf1s, hkf1_l]
                    c0_hsplit
                    · have h1888_inc_mod : (1888 + (kb1[(7 : BitVec 64).toNat]'hk7_bd).toNat) %
                          4294967296 = 1888 + inc.toNat :=
                        s13_add_mod_lt (by decide) hinc hnc_le
                      have h2144_inc_mod : (2144 + (kb1[(7 : BitVec 64).toNat]'hk7_bd).toNat) %
                          4294967296 = 2144 + inc.toNat :=
                        s13_add_mod_lt (by decide) hinc hnc_le
                      have h1888_bd : (1888 + (kb1[(7 : BitVec 64).toNat]'hk7_bd).toNat) %
                          4294967296 < kbf1.length := by
                        rw [h1888_inc_mod]; exact s13_1888_len_lt hinc hnc_le (by omega)
                      have h2144_bd : (2144 + (kb1[(7 : BitVec 64).toNat]'hk7_bd).toNat) %
                          4294967296 < kbf1.length := by
                        rw [h2144_inc_mod]; exact s13_2144_len_lt hinc hnc_le (by omega)
                      have hget_1888_s : kbf1[(1888 + (kb1[(7 : BitVec 64).toNat]'hk7_bd).toNat) %
                          4294967296]'h1888_bd = off_i := s13_get_congr h1888_inc_mod _ _
                      have hget_2144_s : kbf1[(2144 + (kb1[(7 : BitVec 64).toNat]'hk7_bd).toNat) %
                          4294967296]'h2144_bd = oldmi := s13_get_congr h2144_inc_mod _ _
                      have hisz_bd : off_i.toNat + sz_i.toNat ≤ acap.toNat := by
                        have hmod : (off_i.toNat + sz_i.toNat) % 4294967296 =
                            off_i.toNat + sz_i.toNat := Nat.mod_eq_of_lt hinc_sz_nw
                        have hnw : (oldmi.toNat ||| 2147483648) &&& 65535 = sz_i.toNat := by
                          dsimp only [sz_i]; rw [BitVec.toNat_and, BitVec.toNat_or]; rfl
                        have hbd1 : (1888 + kb1[7].toNat) % 4294967296 < kbf1.length := by
                          erw [h1888_inc_mod]; exact s13_1888_len_lt hinc hnc_le (by omega)
                        have hbd2 : (2144 + kb1[7].toNat) % 4294967296 < kbf1.length := by
                          erw [h2144_inc_mod]; exact s13_2144_len_lt hinc hnc_le (by omega)
                        have hne12 : (2144 + kb1[7].toNat) % 4294967296 ≠
                            (1888 + kb1[7].toNat) % 4294967296 := by
                          erw [h1888_inc_mod, h2144_inc_mod]; omega
                        have hc' := hc; simp only [Nat.reducePow] at hc'
                        erw [List.getElem_set_ne hne12,
                          List.getElem_set_self (by rw [List.length_set]; exact hbd2),
                          hget_1888_s, hget_2144_s, BitVec.toNat_and, BitVec.toNat_or] at hc'
                        simpa [hnw, hmod] using hc'
                      clear hc
                      have hget_raw_off_i : ∀ hbd, (kbf1.set (BitVec.setWidth 64
                          (2144 + kb1[(BitVec.ofNat 64 7).toNat]'hk7_bd)).toNat
                          (kbf1[(BitVec.setWidth 64
                            (2144 + kb1[(BitVec.ofNat 64 7).toNat]'hk7_bd)).toNat]'
                            h2144_inc_c0 ||| 2147483648))[(BitVec.setWidth 64
                            (1888 + kb1[(BitVec.ofNat 64 7).toNat]'hk7_bd)).toNat]'hbd =
                          off_i := by
                        intro hbd
                        rw [List.getElem_set_ne (by erw [h2144_inc_eq, h1888_inc_eq]; omega)]
                        exact s13_get_congr h1888_inc_eq _ _
                      simp only [hget_raw_off_i]
                      c0_hsteps_nogrp
                      refine wp_loop_group (ts := [i32]) (fun rem (j, ()) mj1 =>
                        ∃ kbj1, invCore kbj1 ∧ j.toNat ≤ sz_i.toNat ∧ rem = sz_i.toNat - j.toNat ∧
                          (array (t := i32) pk kbj1 ⋆ R) mj1) ?_ ?_
                      · rintro Li remi ⟨ji, ⟨⟩⟩ mj1 hLi ⟨kbj1, hkj1, hji, rfl, hmj1⟩
                        have hkj1_l := hkj1.2.1; c0_hsplit
                        · have hj_lt : ji.toNat < sz_i.toNat := by
                            have hc' := hc
                            have hbd2 : (2144 + kb1[7].toNat) % 4294967296 < kbf1.length := by
                              erw [h2144_inc_mod]; exact s13_2144_len_lt hinc hnc_le (by omega)
                            have hnw : (oldmi.toNat ||| 2147483648) &&& 65535 = sz_i.toNat := by
                              dsimp only [sz_i]; rw [BitVec.toNat_and, BitVec.toNat_or]; rfl
                            simp only [Nat.reducePow] at hc'
                            erw [List.getElem_set_self (by rw [List.length_set]; exact hbd2),
                              hget_2144_s, BitVec.toNat_and, BitVec.toNat_or] at hc'
                            simpa [hnw] using hc'
                          clear hc
                          have hsz_lt : sz_i.toNat < 65536 := by
                            dsimp only [sz_i]; rw [BitVec.toNat_and]
                            exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
                          have hji1 : (ji + 1#32).toNat = ji.toNat + 1 := by
                            have := hsz_lt; have := hj_lt; c0_bound
                          have h15_j := (s13_k6_h15_eq hlen rfl hkj1).2
                          have har_j : 2912 + off_i.toNat + ji.toNat < kbj1.length := by
                            have := hkj1.1.length_ge; have := h15_j; dsimp only [acap] at hisz_bd
                            omega
                          have har_j_c0 : (BitVec.setWidth 64 (2912#32 + off_i + ji)).toNat <
                              kbj1.length := by have := har_j; have := hkj1.1.length_lt; c0_bound
                          c0_hsteps_nogrp
                          refine wp_join0 (fun mj2 => ∃ kbj2, invCore kbj2 ∧
                              (array (t := i32) pk kbj2 ⋆ R) mj2) ?_ ?_
                          · intro _ mj2 ⟨kbj2, hkj2, hmj2⟩; c0_hsteps!
                            exact hLi (sz_i.toNat - (ji + 1#32).toNat) (ji + 1#32, ()) mj2
                              (by have := hji1; omega)
                              ⟨kbj2, hkj2, by have := hji1; omega, rfl, hmj2⟩
                          · intro Jlv hJlv; c0_hsplit
                            · have hget_j_c0 : kbj1[(BitVec.setWidth 64
                                  (2912#32 + off_i + ji)).toNat]'har_j_c0 =
                                  kbj1[2912 + off_i.toNat + ji.toNat]'har_j :=
                                s13_get_congr (by have := har_j; have := hkj1.1.length_lt; c0_bound)
                                  _ _
                              have hj_v_lt : ((kbj1[2912 + off_i.toNat + ji.toNat]'har_j) >>>
                                  (1 : Nat)).toNat < nv.toNat := by
                                have har_mod : (2912 + off_i.toNat + ji.toNat) % 4294967296 =
                                    2912 + off_i.toNat + ji.toNat := by
                                  have := har_j; have := hkj1.1.length_lt; omega
                                rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
                                  ← s13_get_congr har_mod (by rw [har_mod]; exact har_j) har_j]
                                simpa [Nat.reducePow] using hc
                              clear hc
                              have h416_j_eq : (BitVec.setWidth 64 (416#32 +
                                  (kbj1[(BitVec.setWidth 64 (2912#32 + off_i + ji)).toNat]'
                                    har_j_c0 >>> (1 : Nat)))).toNat =
                                  416 + ((kbj1[2912 + off_i.toNat + ji.toNat]'har_j) >>>
                                    (1 : Nat)).toNat := by
                                rw [hget_j_c0]; have := hj_v_lt; have := hnv_le; c0_bound
                              have h416_j_c0 : (BitVec.setWidth 64 (416#32 +
                                  (kbj1[(BitVec.setWidth 64 (2912#32 + off_i + ji)).toNat]'
                                    har_j_c0 >>> (1 : Nat)))).toNat < kbj1.length := by
                                rw [h416_j_eq]; omega
                              c0_hsteps!
                              have hmj_eq := s13_set_congr (xs := kbj1) h416_j_eq
                                (congrArg (· ||| (2 : BitVec 32))
                                  (s13_get_congr (xs := kbj1) h416_j_eq h416_j_c0 (by omega)))
                              erw [hmj_eq] at hm
                              exact hJlv _ ⟨_, invCore_set_flags hkj1
                                (v := ((kbj1[2912 + off_i.toNat + ji.toNat]'har_j) >>>
                                  (1 : Nat)).toNat) (by omega) _, hm⟩
                            · c0_hsteps!; exact hJlv mj1 ⟨kbj1, hkj1, hmj1⟩
                        · c0_hsteps!; exact hJincCl mj1 ⟨kbj1, hkj1, hmj1⟩
                      · intro Li hLi; c0_hsteps!
                        exact hLi sz_i.toNat (0#32, ()) _
                          ⟨kbf1s, h_kbf1s, Nat.zero_le _, by simp, hm⟩
                    · c0_hsteps!; exact hJincCl _ ⟨kbf1s, h_kbf1s, hm⟩
              · intro Lf hLf; c0_hsteps!
                exact hLf nv.toNat (0#32, ()) m1 ⟨kb1, hk1, Nat.zero_le _, by simp, hm1⟩
            · dsimp only; c0_hsteps!; rw [hi1_nc]; exact hJinc (kb1, nc) m1 ⟨hk1, hm1⟩
      · intro L1 hL1; c0_hsteps!
        exact hL1 nc.toNat (0#32, ()) m0
          ⟨kbuf, ⟨hok0, rfl, fun _ _ _ => rfl, fun _ _ => ⟨rfl, rfl⟩⟩, Nat.zero_le _, by simp, hm0⟩

end S13CoreM7Proof

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S1
