/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Definition.Inv
public import LeanQbe.T.Examples.Kissat.Src.Definition

/-!
# Kissat M7 K6 Core Helper Proofs (`Proof.Definition.WpM7CoreHelpers`)

Invariant `CoreInv`, bit-preservation lemmas for `KM_CORE = 0x80000000#32`, AST extractors,
and split WP lemmas culminating in `k6_core_fixpoint_wp` for `full_k6_core_m7`.
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

@[local bv_c0]
private theorem k6_ofnat_one :
    @OfNat.ofNat Nat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
      (instOfNatNat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) = 1 := rfl

public section

/-- Invariant maintained throughout `full_k6_core_m7`: `K6BufOk`, immutable regions outside
variable flags (`[416, 480)`) and clause metadata (`[2144, 2400)`), and unchanged clause sizes
and `KM_LRN` bits. -/
@[expose] def CoreInv (kbuf : List (BitVec 32)) (nc : BitVec 32)
    (kb : List (BitVec 32)) : Prop :=
  K6BufOk kb ∧ kb.length = kbuf.length ∧
  (∀ idx < kbuf.length, (idx < 416 ∨ (480 ≤ idx ∧ idx < 2144) ∨ 2400 ≤ idx) →
    kb[idx]? = kbuf[idx]?) ∧
  (∀ cid < nc.toNat,
    let m0 := kbuf[2144 + cid]?.getD 0#32
    let m1 := kb[2144 + cid]?.getD 0#32
    (m1 &&& 0xFFFF#32) = (m0 &&& 0xFFFF#32) ∧
      (m1 &&& 0x40000000#32) = (m0 &&& 0x40000000#32))

/-- Updating clause metadata entry `2144 + cid` preserves `CoreInv`. -/
theorem coreInv_set_meta {kbuf : List (BitVec 32)} {nc : BitVec 32}
    (hnc_le : nc.toNat ≤ 256) {kb : List (BitVec 32)} (hik : CoreInv kbuf nc kb)
    {cid : Nat} (hcid : cid < nc.toNat) {v : BitVec 32}
    (hsz : (v &&& 0xFFFF#32) = ((kb[2144 + cid]?.getD 0#32) &&& 0xFFFF#32))
    (hlrn : (v &&& 0x40000000#32) = ((kb[2144 + cid]?.getD 0#32) &&& 0x40000000#32)) :
    CoreInv kbuf nc (kb.set (2144 + cid) v) := by
  refine ⟨k6BufOk_set_core_meta hik.1 (by omega) hsz hlrn, by simp [hik.2.1],
    fun idx hi hor => ?_, fun j hj => ?_⟩
  · rw [List.getElem?_set_ne (by omega)]; exact hik.2.2.1 idx hi hor
  · by_cases heq : j = cid
    · subst heq
      have hk_l : 2144 + j < kb.length := by have := hik.1.base_ge; omega
      dsimp only
      rw [List.getElem?_set_self hk_l, Option.getD_some, hsz, hlrn]
      exact hik.2.2.2 j hj
    · rw [List.getElem?_set_ne (by omega)]; exact hik.2.2.2 j hj

/-- Updating variable flag entry `416 + v` preserves `CoreInv`. -/
theorem coreInv_set_flags {kbuf : List (BitVec 32)} {nc : BitVec 32}
    {kb : List (BitVec 32)} (hik : CoreInv kbuf nc kb)
    {v : Nat} (hv : v < 64) (val : BitVec 32) :
    CoreInv kbuf nc (kb.set (416 + v) val) := by
  refine ⟨k6BufOk_set_flags hik.1 hv val, by simp [hik.2.1],
    fun idx hi hor => ?_, fun j hj => ?_⟩
  · rw [List.getElem?_set_ne (by omega)]; exact hik.2.2.1 idx hi hor
  · rw [List.getElem?_set_ne (by omega)]; exact hik.2.2.2 j hj

/-- Clearing `KM_CORE = 0x80000000#32` preserves size and `KM_LRN`. -/
theorem k6_km_core_clear_pres (m : BitVec 32) :
    ((m &&& ~~~0x80000000#32) &&& 0xFFFF#32 = m &&& 0xFFFF#32) ∧
    ((m &&& ~~~0x80000000#32) &&& 0x40000000#32 = m &&& 0x40000000#32) := by
  constructor <;> rw [BitVec.and_assoc] <;> rfl

/-- Setting `KM_CORE = 0x80000000#32` preserves size and `KM_LRN`. -/
theorem k6_km_core_or_pres (m : BitVec 32) :
    ((m ||| 0x80000000#32) &&& 0xFFFF#32 = m &&& 0xFFFF#32) ∧
    ((m ||| 0x80000000#32) &&& 0x40000000#32 = m &&& 0x40000000#32) := by
  constructor <;> rw [BitVec.and_or_distrib_right] <;>
    simp [show (0x80000000#32 &&& 0xFFFF#32) = 0#32 from rfl,
          show (0x80000000#32 &&& 0x40000000#32) = 0#32 from rfl]

/-- C0 constant helper `(0 % 2^64) = 0`. -/
theorem k6_c0 : (OfNat.ofNat 0 % 18446744073709551616 : Nat) = 0 := rfl

/-- C0 constant helper `(1 % 2^64) = 1`. -/
theorem k6_c1 : (OfNat.ofNat 1 % 18446744073709551616 : Nat) = 1 := rfl

/-- C0 constant helper `(7 % 2^64) = 7`. -/
theorem k6_c7 : (OfNat.ofNat 7 % 18446744073709551616 : Nat) = 7 := rfl

/-- C0 constant helper `(15 % 2^64) = 15`. -/
theorem k6_c15 : (OfNat.ofNat 15 % 18446744073709551616 : Nat) = 15 := rfl

/-- Helper bound for `2912 + o + s + j` modulo `2^32`. -/
theorem k6_2912_mod_eq {o s j na acap15 acap len : Nat}
    (hge : 2912 + acap15 ≤ len) (heq : acap15 = acap) (hl28 : len < 2 ^ 28)
    (hna : o + s + na ≤ acap) (hj : j < na) :
    (2912 + o + s + j) % 2 ^ 32 = 2912 + o + s + j :=
  Nat.mod_eq_of_lt (by omega)

/-- Helper bound `2144 + a < l1`. -/
theorem k6_2144_lt {a nc l1 l2 : Nat} (ha : a < nc) (hnc : nc ≤ 256)
    (hl : 2912 ≤ l2) (heq : l1 = l2) : 2144 + a < l1 := by omega

/-- Helper bound `BitVec.setWidth 64 (2144#32 + a)`. -/
theorem k6_sw64_add_2144 {a : BitVec 32} (ha : a.toNat < 256) :
    (BitVec.setWidth 64 (2144#32 + a)).toNat = 2144 + a.toNat := by c0_bound

/-- Helper bound `BitVec.setWidth 64 (1888#32 + a)`. -/
theorem k6_sw64_add_1888 {a : BitVec 32} (ha : a.toNat < 256) :
    (BitVec.setWidth 64 (1888#32 + a)).toNat = 1888 + a.toNat := by c0_bound

/-- Helper bound `1888 + i < l`. -/
theorem k6_1888_len_lt {i nc l : Nat} (hi : i < nc) (hnc : nc ≤ 256)
    (hl : 2912 ≤ l) : 1888 + i < l := by omega

/-- Helper bound `2144 + i < l`. -/
theorem k6_2144_len_lt {i nc l : Nat} (hi : i < nc) (hnc : nc ≤ 256)
    (hl : 2912 ≤ l) : 2144 + i < l := by omega

/-- Helper bound `(c + i) % 2^32 = c + i`. -/
theorem k6_add_mod_lt {c i nc : Nat} (hc : c ≤ 2400) (hi : i < nc)
    (hnc : nc ≤ 256) : (c + i) % 4294967296 = c + i := by omega

/-- Default placeholder value for AST subtree extraction. -/
@[expose] def k6Dflt : (t : Ty) → Val t
  | .bool => false | .bits _ => 0 | .float _ => 0 | .pair a b => (k6Dflt a, k6Dflt b)

/-- Default placeholder tuple for AST subtree extraction. -/
@[expose] def k6DfltT : (ts : List Ty) → Tup Val ts
  | [] => () | t :: r => (k6Dflt t, k6DfltT r)

/-- Step past `Expr.let_` using placeholder values. -/
@[expose] def k6SLet {L rs} : Expr Val L rs → Expr Val L rs
  | .let_ (ts := ts) _ k => k (k6DfltT ts) | _ => .hlt

/-- Step past single-`i32` `Expr.let_` supplying concrete value `v`. -/
@[expose] def k6SLetI {L rs} (v : Val (.bits 32)) : Expr Val L rs → Expr Val L rs
  | .let_ (ts := [.bits 32]) _ k => k (v, ()) | _ => .hlt

/-- Step past `Expr.load i32` supplying value `v`. -/
@[expose] def k6SLd {L rs} (v : Val (.bits 32)) : Expr Val L rs → Expr Val L rs
  | .load (.bits 32) _ k => k v | _ => .hlt

/-- Step past `Expr.store`. -/
@[expose] def k6SSt {L rs} : Expr Val L rs → Expr Val L rs
  | .store _ _ e => e | _ => .hlt

/-- Step past `Expr.jnz` taking the false branch. -/
@[expose] def k6SJF {L rs} : Expr Val L rs → Expr Val L rs
  | .jnz _ _ e => e | _ => .hlt

/-- Step past `Expr.jnz` taking the true branch. -/
@[expose] def k6SJT {L rs} : Expr Val L rs → Expr Val L rs
  | .jnz _ e _ => e | _ => .hlt

/-- Enter single-`i32` `Expr.group` block with argument `x`. -/
@[expose] def k6SGrpBI {rs} (x : Val (.bits 32)) : Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 32]]) bs _ =>
      match bs ((fun _ _ => True), ()) with | .cons b _ => b (x, ())
  | _ => .hlt

/-- Enter empty-arg `Expr.group` block. -/
@[expose] def k6SGrpBN {rs} : Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[]]) bs _ =>
      match bs ((fun _ _ => True), ()) with | .cons b _ => b ()
  | _ => .hlt

/-- Enter `(i32, bool)` `Expr.group` block with arguments `(x1, x2)`. -/
@[expose] def k6SGrpB2 {rs} (x1 : Val (.bits 32)) (x2 : Val .bool) :
    Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 32, .bool]]) bs _ =>
      match bs ((fun _ _ => True), ()) with | .cons b _ => b (x1, x2, ())
  | _ => .hlt

/-- Enter `(bool, i32)` `Expr.group` block with arguments `(x1, x2)`. -/
@[expose] def k6SGrpB2b {rs} (x1 : Val .bool) (x2 : Val (.bits 32)) :
    Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bool, .bits 32]]) bs _ =>
      match bs ((fun _ _ => True), ()) with | .cons b _ => b (x1, x2, ())
  | _ => .hlt

/-- Enter single-`bool` `Expr.group` block with argument `x`. -/
@[expose] def k6SGrpBB {rs} (x : Val .bool) : Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bool]]) bs _ =>
      match bs ((fun _ _ => True), ()) with | .cons b _ => b (x, ())
  | _ => .hlt

/-- Skip single-`i32` `Expr.group` to its continuation with `J`. -/
@[expose] def k6SGrpKI {rs} (J : Cont [.bits 32]) : Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 32]]) _ k => k (J, ())
  | _ => .hlt

/-- Skip single-`bool` `Expr.group` to its continuation with `J`. -/
@[expose] def k6SGrpKB {rs} (J : Cont [.bool]) : Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bool]]) _ k => k (J, ())
  | _ => .hlt

/-- Skip empty-arg `Expr.group` to its continuation with `J`. -/
@[expose] def k6SGrpKN {rs} (J : Cont []) : Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[]]) _ k => k (J, ())
  | _ => .hlt

/-- Extracted fixpoint-loop subexpression of `full_k6_core_m7_body`. -/
@[expose] def k6FixpointE (pk : BitVec 64) (nc nv acap : BitVec 32) : Expr Val Cont [] :=
  let e := k6SLd nc (k6SLet (k6SLet (k6SLet (full_k6_core_m7_body Val Cont (pk, ())))))
  let e := k6SJF (k6SLet (k6SJF (k6SLet (k6SLd acap (k6SLet (k6SLet (k6SLet
    (k6SLd nv (k6SLet (k6SLet (k6SLet e)))))))))))
  let e := k6SLd 0#32 (k6SLet (k6SLet (k6SLet (k6SJF (k6SLet (k6SGrpBI nc e))))))
  k6SGrpBI 0#32 e

private def k6CoreCidStepE (pk : BitVec 64) (nc nv acap c_i cm off_c sz_c : BitVec 32)
    (ch_c : Bool) (Jcid : Cont [.bool]) : Expr Val Cont [] :=
  let e := k6SGrpB2 0#32 true (k6FixpointE pk nc nv acap)
  let e := k6SLet (k6SJT (k6SLet (k6SJT e)))
  let e := k6SGrpB2b ch_c 0#32 e
  let e := k6SLet (k6SLet (k6SLet (k6SLet (k6SLetI c_i (k6SJT (k6SLet e))))))
  let e := k6SGrpKB Jcid (k6SLd cm e)
  let e := k6SLd off_c (k6SLet (k6SLet (k6SLet (k6SLet (k6SJT (k6SLet (k6SLet e)))))))
  k6SLetI sz_c e

private def k6CoreLrnE (pk : BitVec 64) (nc acap c_i cm off_c sz_c : BitVec 32)
    (ch_c : Bool) (Jlrn : Cont [.bool]) : Expr Val Cont [] :=
  k6SGrpKB Jlrn (k6CoreCidStepE pk nc 0#32 acap c_i cm off_c sz_c ch_c (fun _ _ => True))

private def k6CoreLitsE (pk : BitVec 64) (nc nv acap off_c sz_c : BitVec 32)
    (ch_c : Bool) (Jcid : Cont [.bool]) : Expr Val Cont [] :=
  k6SGrpBB ch_c (k6CoreCidStepE pk nc nv acap 0#32 0#32 off_c sz_c ch_c Jcid)

end

private theorem k6_core_lrn_wp {Γ : Env} {pk : BitVec 64} {kbuf : List (BitVec 32)}
    {nc acap c_i cm off_c sz_c : BitVec 32} {ch_c : Bool} {R : Mem 64 → Prop}
    {Q : Post []} {X : XPost} {Jlrn : Cont [.bool]}
    (hlen : 2912 ≤ kbuf.length) (hnc_le : nc.toNat ≤ 256) (hc_i : c_i.toNat < nc.toNat)
    (hsz_eq : sz_c = cm &&& 0xFFFF#32)
    (hJlrn : ∀ ch' mj', ∀ kbj, CoreInv kbuf nc kbj → (array (t := i32) pk kbj ⋆ R) mj' →
      Jlrn (ch', ()) mj')
    {kbc : List (BitVec 32)} {mc : Mem 64}
    (hkc : CoreInv kbuf nc kbc) (hmc : (array (t := i32) pk kbc ⋆ R) mc)
    (hkbcl : off_c.toNat + (cm &&& 0xFFFF#32).toNat ≤ acap.toNat ∧
      ((cm &&& 0x40000000#32) ≠ 0#32 →
        off_c.toNat + (cm &&& 0xFFFF#32).toNat + (kbc[2400 + c_i.toNat]?.getD 0#32).toNat ≤
          acap.toNat))
    (hsz_nw : off_c.toNat + sz_c.toNat < 2 ^ 32)
    (hacap15 : kbuf[15]'(by omega) = acap) :
    wp Γ Q X (k6CoreLrnE pk nc acap c_i cm off_c sz_c ch_c Jlrn) mc := by
  let invCore := CoreInv kbuf nc
  have invCore_set_meta := @coreInv_set_meta kbuf nc hnc_le
  have hkc_l := hkc.2.1; have hlt28 := hkc.1.length_lt; have hlen_ge := hkc.1.length_ge
  have h15c : (kbc[15]?.getD 0#32).toNat = acap.toNat := by
    have := hkc.2.2.1 15 (by omega) (Or.inl (by omega))
    rw [this, m8_k6_get_eq (by omega), hacap15]
  dsimp only [k6CoreLrnE, k6CoreCidStepE, k6FixpointE, k6SLet, k6SLetI, k6SLd,
    k6SJF, k6SJT, k6SGrpBI, k6SGrpB2, k6SGrpB2b, k6SGrpKB, k6DfltT, k6Dflt]
  c0_hsplit
  · have hlrn_cm : (cm &&& 0x40000000#32) ≠ 0#32 := hc
    clear hc
    have hbd_2400 : 2400 + c_i.toNat < kbc.length := by
      have := hkc_l; have := hlen; have := hnc_le; have := hc_i; omega
    have hc_2400_idx : (BitVec.setWidth 64 (2400#32 + c_i)).toNat = 2400 + c_i.toNat := by
      have := hnc_le; have := hc_i; c0_bound
    have hbd_2400_c0 : (BitVec.setWidth 64 (2400#32 + c_i)).toNat < kbc.length := by
      rw [hc_2400_idx]; exact hbd_2400
    let na_c := kbc[2400 + c_i.toNat]'hbd_2400
    have hoff_na' : off_c.toNat + sz_c.toNat + na_c.toNat ≤ acap.toNat := by
      have h2 := hkbcl.2 hlrn_cm
      rw [m8_k6_get_eq hbd_2400] at h2; rw [hsz_eq]; exact h2
    have hno_ov2 : off_c.toNat + sz_c.toNat + na_c.toNat < 2 ^ 32 := by
      have := hlt28; have := hlen_ge; have := h15c; omega
    c0_hsteps_nogrp
    refine wp_join_state1 (t := .bool) (α := List (BitVec 32) × Bool) (fun x => x.2)
      (fun x mc' => invCore x.1 ∧ (array (t := i32) pk x.1 ⋆ R) mc') ?_ ?_
    · rintro _ ⟨kbc', ch'⟩ mc' ⟨hkc', hmc'⟩
      c0_hsteps!; exact hJlrn ch' mc' kbc' hkc' hmc'
    · intro J805 hJ805
      have hget_2400_raw : kbc[(BitVec.toNat (2400 : BitVec 32) + c_i.toNat) % 2 ^ 32]'(by
          have : (2400 + c_i.toNat) % 2 ^ 32 = 2400 + c_i.toNat :=
            k6_add_mod_lt (by decide) hc_i hnc_le
          simpa using by rw [this]; exact hbd_2400) = na_c :=
        m8_k6_get_congr (k6_add_mod_lt (by decide) hc_i hnc_le) _ hbd_2400
      c0_hsplit
      · clear hc; c0_hsteps_nogrp
        refine wp_loop_group (ts := [.bool, i32])
          (fun remj (_chj, j_c, ()) mj2 => ∃ kbj2, invCore kbj2 ∧ j_c.toNat ≤ na_c.toNat ∧
            remj = na_c.toNat - j_c.toNat ∧ (array (t := i32) pk kbj2 ⋆ R) mj2) ?_ ?_
        · rintro Lj remj ⟨ch_j, j_c, ⟨⟩⟩ mj2 hLj ⟨kbj2, hkj2, hj_le, rfl, hmj2⟩
          have hkj2_l := hkj2.2.1; have hlt28' := hkj2.1.length_lt; have hge' := hkj2.1.length_ge
          have h15j : (kbj2[15]?.getD 0#32).toNat = acap.toNat := by
            have h15e := hkj2.2.2.1 15 (by omega) (Or.inl (by omega))
            rw [h15e, m8_k6_get_eq (by omega), hacap15]
          c0_hsplit
          · have hj_lt : j_c.toNat < na_c.toNat := by
              rw [hget_2400_raw] at hc; exact hc
            clear hc
            have hj1 : (j_c + 1#32).toNat = j_c.toNat + 1 := by
              have := hlt28'; have := hge'; have := h15j; have := hoff_na'; have := hj_lt; c0_bound
            have hidx_lt : 2912 + off_c.toNat + sz_c.toNat + j_c.toNat < kbj2.length := by
              have := hkj2_l; have := hlt28'; have := hge'; have := h15j
              have := hoff_na'; have := hj_lt; omega
            have hidx_c0 : (BitVec.setWidth 64 ((2912 : BitVec 32) + off_c + sz_c + j_c)).toNat =
                2912 + off_c.toNat + sz_c.toNat + j_c.toNat := by
              have := hidx_lt; have := hsz_nw; have := hno_ov2; have := hlt28'
              have := hge'; have := h15j; have := hoff_na'; have := hj_lt; c0_bound
            have hidx_c0_lt : (BitVec.setWidth 64
                ((2912 : BitVec 32) + off_c + sz_c + j_c)).toNat < kbj2.length := by
              rw [hidx_c0]; exact hidx_lt
            let ant := kbj2[2912 + off_c.toNat + sz_c.toNat + j_c.toNat]'hidx_lt
            have hant_c0_eq : kbj2[(BitVec.setWidth 64
                ((2912 : BitVec 32) + off_c + sz_c + j_c)).toNat]'hidx_c0_lt = ant :=
              m8_k6_get_congr hidx_c0 hidx_c0_lt hidx_lt
            c0_hsteps_nogrp
            refine wp_join_state1 (t := .bool) (α := List (BitVec 32) × Bool) (fun x => x.2)
              (fun x mj3 => invCore x.1 ∧ (array (t := i32) pk x.1 ⋆ R) mj3) ?_ ?_
            · rintro _ ⟨kbj3, chj3⟩ mj3 ⟨hkj3, hmj3⟩; c0_hsteps!
              exact hLj (na_c.toNat - (j_c + 1#32).toNat) (chj3, j_c + 1#32, ()) mj3
                (by have := hj1; omega) ⟨kbj3, hkj3, by omega, rfl, hmj3⟩
            · intro Jant hJant
              have hc_2912_mod : (2912 + off_c.toNat + sz_c.toNat + j_c.toNat) % 2 ^ 32 =
                  2912 + off_c.toNat + sz_c.toNat + j_c.toNat :=
                k6_2912_mod_eq hge' h15j hlt28' hoff_na' hj_lt
              have hget_ant : kbj2[(2912 + off_c.toNat + sz_c.toNat + j_c.toNat) % 2 ^ 32]'(by
                    rw [hc_2912_mod]; exact hidx_lt) = ant :=
                m8_k6_get_congr hc_2912_mod _ hidx_lt
              c0_hsplit
              · have hant_lt : ant.toNat < nc.toNat := by
                  rw [← hget_ant]; exact hc
                clear hc
                let olda := kbj2[2144 + ant.toNat]'(k6_2144_lt hant_lt hnc_le hlen hkj2_l)
                have hpa := k6_km_core_or_pres olda
                have h2144_a_idx : (BitVec.setWidth 64 ((2144 : BitVec 32) +
                    kbj2[(BitVec.setWidth 64
                      ((2912 : BitVec 32) + off_c + sz_c + j_c)).toNat]'hidx_c0_lt)).toNat =
                    2144 + ant.toNat := by
                  rw [hant_c0_eq]; exact k6_sw64_add_2144 (Nat.lt_of_lt_of_le hant_lt hnc_le)
                have h2144_a_c0 : (BitVec.setWidth 64 ((2144 : BitVec 32) +
                    kbj2[(BitVec.setWidth 64
                      ((2912 : BitVec 32) + off_c + sz_c + j_c)).toNat]'hidx_c0_lt)).toNat <
                    kbj2.length := by
                  rw [h2144_a_idx]; exact k6_2144_lt hant_lt hnc_le hlen hkj2_l
                c0_hsplit
                · clear hc; c0_hsteps!
                  have hm_eq := m8_k6_set_congr (xs := kbj2) h2144_a_idx
                    (congrArg (· ||| (2147483648 : BitVec 32))
                      (m8_k6_get_congr (xs := kbj2) h2144_a_idx h2144_a_c0
                        (k6_2144_lt hant_lt hnc_le hlen hkj2_l)))
                  rw [hm_eq] at hm
                  dsimp only [olda] at hpa hm
                  rw [← m8_k6_get_eq (k6_2144_lt hant_lt hnc_le hlen hkj2_l)] at hpa hm
                  exact hJant (_, true) m ⟨invCore_set_meta hkj2 hant_lt hpa.1 hpa.2, hm⟩
                · c0_hsteps!; exact hJant (kbj2, ch_j) mj2 ⟨hkj2, hmj2⟩
              · c0_hsteps!; exact hJant (kbj2, ch_j) mj2 ⟨hkj2, hmj2⟩
          · c0_hsteps!; exact hJ805 (kbj2, ch_j) mj2 ⟨hkj2, hmj2⟩
        · intro Lj hLj; c0_hsteps!
          exact hLj na_c.toNat (ch_c, 0#32, ()) mc ⟨kbc, hkc, Nat.zero_le _, by simp, hmc⟩
      · c0_hsteps!; exact hJ805 (kbc, ch_c) mc ⟨hkc, hmc⟩
  · c0_hsteps!; exact hJlrn ch_c mc kbc hkc hmc

private theorem k6_core_lits_wp {Γ : Env} {pk : BitVec 64} {kbuf : List (BitVec 32)}
    {nc nv acap off_c sz_c : BitVec 32} {ch_c : Bool} {R : Mem 64 → Prop}
    {Q : Post []} {X : XPost} {Jcid : Cont [.bool]}
    (hlen : 2912 ≤ kbuf.length) (hnc_le : nc.toNat ≤ 256) (hnv_le : nv.toNat ≤ 64)
    (hJcid : ∀ ch' mc', ∀ kbc', CoreInv kbuf nc kbc' → (array (t := i32) pk kbc' ⋆ R) mc' →
      Jcid (ch', ()) mc')
    {kbc : List (BitVec 32)} {mc : Mem 64}
    (hkc : CoreInv kbuf nc kbc) (hmc : (array (t := i32) pk kbc ⋆ R) mc)
    (hoff_nw : off_c.toNat + sz_c.toNat < 2 ^ 32)
    (hsz_le : sz_c.toNat < 65536) (hacap15 : kbuf[15]'(by omega) = acap)
    (hnv0 : kbuf[0]'(by omega) = nv) :
    wp Γ Q X (k6CoreLitsE pk nc nv acap off_c sz_c ch_c Jcid) mc := by
  let invCore := CoreInv kbuf nc
  have invCore_set_meta := @coreInv_set_meta kbuf nc hnc_le
  dsimp only [k6CoreLitsE, k6CoreCidStepE, k6FixpointE, k6SLet, k6SLetI, k6SLd,
    k6SJF, k6SJT, k6SGrpBI, k6SGrpB2, k6SGrpB2b, k6SGrpKB, k6SGrpBB, k6DfltT, k6Dflt]
  c0_hsteps_nogrp
  refine wp_join_state1 (t := .bool) (α := List (BitVec 32) × Bool) (fun x => x.2)
    (fun x mc' => invCore x.1 ∧ (array (t := i32) pk x.1 ⋆ R) mc') ?_ ?_
  · rintro _ ⟨kbc', ch'⟩ mc' ⟨hkc', hmc'⟩; c0_hsteps!
    exact hJcid ch' mc' kbc' hkc' hmc'
  · intro Jelse hJelse; c0_hsplit
    · have hoff_sz : off_c.toNat + sz_c.toNat ≤ acap.toNat := by
        simpa [Nat.mod_eq_of_lt hoff_nw, k6_c15] using hc
      clear hc; c0_hsteps_nogrp
      refine wp_loop_group (ts := [.bool, i32])
        (fun remj (_chj, j_c, ()) mj => ∃ kbj, invCore kbj ∧ j_c.toNat ≤ sz_c.toNat ∧
          remj = sz_c.toNat - j_c.toNat ∧ (array (t := i32) pk kbj ⋆ R) mj) ?_ ?_
      · rintro Lj remj ⟨ch_j, j_c, ⟨⟩⟩ mj hLj ⟨kbj, hkj, hj_le, rfl, hmj⟩
        have hkj_l := hkj.2.1; have hlt28 := hkj.1.length_lt; have hge := hkj.1.length_ge
        have h15j : (kbj[15]?.getD 0#32).toNat = acap.toNat := by
          have := hkj.2.2.1 15 (by omega) (Or.inl (by omega))
          rw [this, m8_k6_get_eq (by omega), hacap15]
        c0_hsplit
        · have hj_lt : j_c.toNat < sz_c.toNat := hc
          clear hc
          have hj1 : (j_c + 1#32).toNat = j_c.toNat + 1 := by
            have := hsz_le; have := hj_lt; c0_bound
          have hidx_lt : 2912 + off_c.toNat + j_c.toNat < kbj.length := by
            have := hkj_l; have := hlt28; have := hge; have := h15j; omega
          have hidx_c0 : (BitVec.setWidth 64 ((2912 : BitVec 32) + off_c + j_c)).toNat =
              2912 + off_c.toNat + j_c.toNat := by
            have := hidx_lt; have := hoff_nw; have := hlt28; have := hge
            have := h15j; have := hoff_sz; c0_bound
          have hidx_c0_lt : (BitVec.setWidth 64 ((2912 : BitVec 32) + off_c + j_c)).toNat <
              kbj.length := by
            rw [hidx_c0]; exact hidx_lt
          c0_hsteps_nogrp
          refine wp_join_state1 (t := .bool) (α := List (BitVec 32) × Bool) (fun x => x.2)
            (fun x mj' => invCore x.1 ∧ (array (t := i32) pk x.1 ⋆ R) mj') ?_ ?_
          · rintro _ ⟨kbj', chj'⟩ mj' ⟨hkj', hmj'⟩; c0_hsteps!
            exact hLj (sz_c.toNat - (j_c + 1#32).toNat) (chj', j_c + 1#32, ()) mj'
              (by have := hj1; omega) ⟨kbj', hkj', by omega, rfl, hmj'⟩
          · intro Jlv hJlv
            let lv := (kbj[2912 + off_c.toNat + j_c.toNat]'hidx_lt) >>> (1 : Nat)
            have hget_lv_c0 : kbj[(BitVec.setWidth 64
                ((2912 : BitVec 32) + off_c + j_c)).toNat]'hidx_c0_lt =
                kbj[2912 + off_c.toNat + j_c.toNat]'hidx_lt :=
              m8_k6_get_congr hidx_c0 hidx_c0_lt hidx_lt
            have har_mod : (2912 + off_c.toNat + j_c.toNat) % 2 ^ 32 =
                2912 + off_c.toNat + j_c.toNat := by
              have := hidx_lt; have := hlt28; omega
            c0_hsplit
            · have hlv_lt : lv.toNat < nv.toNat := by
                dsimp only [lv]
                rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
                  ← m8_k6_get_congr har_mod (by rw [har_mod]; exact hidx_lt) hidx_lt]
                simpa [hnv0, Nat.reducePow] using hc
              clear hc
              have h32_c0 : (BitVec.setWidth 64 ((32 : BitVec 32) + (kbj[(BitVec.setWidth 64
                  ((2912 : BitVec 32) + off_c + j_c)).toNat]'hidx_c0_lt >>> (1 : Nat)))).toNat <
                  kbj.length := by
                rw [hget_lv_c0]; change (BitVec.setWidth 64 (32#32 + lv)).toNat < kbj.length
                have := hlv_lt; have := hnv_le; have := hkj_l; have := hlen; c0_bound
              c0_hsplit
              · clear hc
                have h96_c0 : (BitVec.setWidth 64 ((96 : BitVec 32) + (kbj[(BitVec.setWidth 64
                    ((2912 : BitVec 32) + off_c + j_c)).toNat]'hidx_c0_lt >>>
                      (1 : Nat)))).toNat < kbj.length := by
                  rw [hget_lv_c0]; change (BitVec.setWidth 64 (96#32 + lv)).toNat < kbj.length
                  have := hlv_lt; have := hnv_le; have := hkj_l; have := hlen; c0_bound
                let r0 := kbj[96 + lv.toNat]'
                    (by have := hlv_lt; have := hnv_le; have := hkj_l; omega)
                have hr0_c0_eq : kbj[(BitVec.setWidth 64 ((96 : BitVec 32) +
                    (kbj[(BitVec.setWidth 64 ((2912 : BitVec 32) + off_c +
                      j_c)).toNat]'hidx_c0_lt >>> (1 : Nat)))).toNat]'h96_c0 = r0 := by
                  refine m8_k6_get_congr ?_ h96_c0 _
                  rw [hget_lv_c0]; change (BitVec.setWidth 64 (96#32 + lv)).toNat = 96 + lv.toNat
                  have := hlv_lt; have := hnv_le; c0_bound
                c0_hsteps_nogrp
                refine wp_join_state1 (t := .bool) (α := List (BitVec 32) × Bool) (fun x => x.2)
                  (fun x mj' => invCore x.1 ∧ (array (t := i32) pk x.1 ⋆ R) mj') ?_ ?_
                · rintro _ ⟨kbj', chj'⟩ mj' ⟨hkj', hmj'⟩; c0_hsteps!
                  exact hJlv (kbj', chj') mj' ⟨hkj', hmj'⟩
                · intro Jr0 hJr0
                  have h96_mod : (96 + (kbj[2912 + off_c.toNat + j_c.toNat]'hidx_lt).toNat / 2) %
                      2 ^ 32 = 96 + lv.toNat := by
                    dsimp only [lv]; rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
                    have := hlv_lt; have := hnv_le; omega
                  have hget_r0_raw : kbj[(96 + (kbj[(2912 + off_c.toNat + j_c.toNat) % 2 ^ 32]'(by
                      rw [har_mod]; exact hidx_lt)).toNat / 2) % 2 ^ 32]'(by
                        rw [m8_k6_get_congr har_mod (by rw [har_mod]; exact hidx_lt) hidx_lt,
                          h96_mod]
                        have := hlv_lt; have := hnv_le; have := hkj_l; have := hlen; omega) = r0 :=
                    m8_k6_get_congr (by rw [m8_k6_get_congr har_mod _ hidx_lt]; exact h96_mod) _ _
                  c0_hsplit
                  · have hr0_lt : r0.toNat < nc.toNat := by
                      have h96_raw : BitVec.toNat (96 : BitVec 32) = 96 := rfl
                      have h2912_raw : BitVec.toNat (2912 : BitVec 32) = 2912 := rfl
                      simp only [h96_raw, h2912_raw] at hc
                      rw [← hget_r0_raw]; exact hc
                    clear hc
                    let oldr := kbj[2144 + r0.toNat]'(k6_2144_lt hr0_lt hnc_le hlen hkj_l)
                    have hpr := k6_km_core_or_pres oldr
                    have h2144_r_idx : (BitVec.setWidth 64 ((2144 : BitVec 32) +
                        kbj[(BitVec.setWidth 64 ((96 : BitVec 32) + (kbj[(BitVec.setWidth 64
                          ((2912 : BitVec 32) + off_c + j_c)).toNat]'hidx_c0_lt >>>
                          (1 : Nat)))).toNat]'h96_c0)).toNat = 2144 + r0.toNat := by
                      rw [hr0_c0_eq]; exact k6_sw64_add_2144 (Nat.lt_of_lt_of_le hr0_lt hnc_le)
                    have h2144_r_c0 : (BitVec.setWidth 64 ((2144 : BitVec 32) +
                        kbj[(BitVec.setWidth 64 ((96 : BitVec 32) + (kbj[(BitVec.setWidth 64
                          ((2912 : BitVec 32) + off_c + j_c)).toNat]'hidx_c0_lt >>>
                          (1 : Nat)))).toNat]'h96_c0)).toNat < kbj.length := by
                      rw [h2144_r_idx]; exact k6_2144_lt hr0_lt hnc_le hlen hkj_l
                    c0_hsplit
                    · clear hc; c0_hsteps!
                      have hm_eq := m8_k6_set_congr (xs := kbj) h2144_r_idx
                        (congrArg (· ||| (2147483648 : BitVec 32))
                          (m8_k6_get_congr (xs := kbj) h2144_r_idx h2144_r_c0
                            (k6_2144_lt hr0_lt hnc_le hlen hkj_l)))
                      simp only [k6_ofnat_one] at hm; rw [hm_eq] at hm
                      dsimp only [oldr] at hpr hm
                      rw [← m8_k6_get_eq (k6_2144_lt hr0_lt hnc_le hlen hkj_l)] at hpr hm
                      exact hJr0 (_, true) m ⟨invCore_set_meta hkj hr0_lt hpr.1 hpr.2, hm⟩
                    · c0_hsteps!; exact hJr0 (kbj, ch_j) mj ⟨hkj, hmj⟩
                  · c0_hsteps!; exact hJr0 (kbj, ch_j) mj ⟨hkj, hmj⟩
              · c0_hsteps!; exact hJlv (kbj, ch_j) mj ⟨hkj, hmj⟩
            · c0_hsteps!; exact hJlv (kbj, ch_j) mj ⟨hkj, hmj⟩
        · c0_hsteps!; exact hJelse (kbj, ch_j) mj ⟨hkj, hmj⟩
      · intro Lj hLj; c0_hsteps!
        exact hLj sz_c.toNat (ch_c, 0#32, ()) mc ⟨kbc, hkc, Nat.zero_le _, by simp, hmc⟩
    · c0_hsteps!; exact hJelse (kbc, ch_c) mc ⟨hkc, hmc⟩

public section

/-- Fixpoint marking loop WP (`while (changed && pass < nc)` inside `full_k6_core_m7`). -/
theorem k6_core_fixpoint_wp {Γ : Env} {pk : BitVec 64} {kbuf : List (BitVec 32)}
    {nc nv acap : BitVec 32} {R : Mem 64 → Prop} {Q : Post []} {X : XPost}
    (hlen : 2912 ≤ kbuf.length) (hnc_def : nc = kbuf[1]'(by omega))
    (hnv_def : nv = kbuf[0]'(by omega)) (hacap_def : acap = kbuf[15]'(by omega))
    (hnc_le : nc.toNat ≤ 256) (hnv_le : nv.toNat ≤ 64)
    (hRet : ∀ kbp mp, CoreInv kbuf nc kbp → (array (t := i32) pk kbp ⋆ R) mp → Q () mp)
    {kbj : List (BitVec 32)} {mj : Mem 64}
    (hkj : CoreInv kbuf nc kbj) (hmj : (array (t := i32) pk kbj ⋆ R) mj) :
    wp Γ Q X (k6FixpointE pk nc nv acap) mj := by
  let invCore := CoreInv kbuf nc
  dsimp only [k6FixpointE, k6SLet, k6SLd, k6SJF, k6SGrpBI, k6DfltT, k6Dflt]
  c0_hsteps_nogrp
  refine wp_loop_group (ts := [i32, .bool])
    (fun rem (pass, _ch, ()) mp => ∃ kbp, invCore kbp ∧ pass.toNat ≤ nc.toNat ∧
      rem = nc.toNat - pass.toNat ∧ (array (t := i32) pk kbp ⋆ R) mp) ?_ ?_
  · rintro Lp remp ⟨pass, ch, ⟨⟩⟩ mp hLp ⟨kbp, hkp, hpass_le, rfl, hmp⟩
    c0_hsplit
    · clear hc
      c0_hsplit
      · have hpass_lt : pass.toNat < nc.toNat := hc
        clear hc
        have hpass1 : (pass + 1#32).toNat = pass.toNat + 1 := by
          have := hnc_le; have := hpass_lt; c0_bound
        c0_hsteps_nogrp
        refine wp_loop_group (ts := [.bool, i32])
          (fun rem (_chc, cid_c, ()) mc => ∃ kbc, invCore kbc ∧ cid_c.toNat ≤ nc.toNat ∧
            rem = cid_c.toNat ∧ (array (t := i32) pk kbc ⋆ R) mc) ?_ ?_
        · rintro Lc remc ⟨ch_c, cid_c, ⟨⟩⟩ mc hLc ⟨kbc, hkc, hc_le, rfl, hmc⟩
          have hkc_l := hkc.2.1
          c0_hsplit
          · have hcid_pos : 0 < cid_c.toNat := hc
            clear hc
            let c_i := cid_c - 1#32
            have hc_i_lt : c_i.toNat < nc.toNat := by
              dsimp only [c_i]; rw [m8_bv32_sub1_toNat hcid_pos]; omega
            have hbd_c : 2144 + c_i.toNat < kbc.length := by
              have := hkc_l; have := hlen; have := hnc_le; omega
            have hc_2144_idx : (BitVec.setWidth 64 (2144#32 + c_i)).toNat = 2144 + c_i.toNat :=
              k6_sw64_add_2144 (Nat.lt_of_lt_of_le hc_i_lt hnc_le)
            have hbd_c_c0 : (BitVec.setWidth 64 (2144#32 + c_i)).toNat < kbc.length := by
              rw [hc_2144_idx]; exact hbd_c
            let cm := kbc[2144 + c_i.toNat]'hbd_c
            have hget_c_c0 : kbc[(BitVec.setWidth 64 (2144#32 + c_i)).toNat]'hbd_c_c0 = cm :=
              m8_k6_get_congr hc_2144_idx hbd_c_c0 hbd_c
            c0_hsteps_nogrp
            refine wp_join_state1 (t := .bool) (α := List (BitVec 32) × Bool) (fun x => x.2)
              (fun x mc' => invCore x.1 ∧ (array (t := i32) pk x.1 ⋆ R) mc') ?_ ?_
            · rintro _ ⟨kbc', ch'⟩ mc' ⟨hkc', hmc'⟩
              c0_hsteps!
              exact hLc c_i.toNat (ch', c_i, ()) mc'
                (by dsimp only [c_i]; rw [m8_bv32_sub1_toNat hcid_pos]; omega)
                ⟨kbc', hkc', by omega, rfl, hmc'⟩
            · intro Jcid hJcid
              have hbd_1888 : 1888 + c_i.toNat < kbc.length := by
                have := hkc_l; have := hlen; have := hnc_le; omega
              have hc_1888_idx : (BitVec.setWidth 64 (1888#32 + c_i)).toNat = 1888 + c_i.toNat :=
                k6_sw64_add_1888 (Nat.lt_of_lt_of_le hc_i_lt hnc_le)
              have hbd_1888_c0 : (BitVec.setWidth 64 (1888#32 + c_i)).toNat < kbc.length := by
                rw [hc_1888_idx]; exact hbd_1888
              c0_hsplit
              · clear hc
                let off_c := kbc[1888 + c_i.toNat]'hbd_1888
                let sz_c := cm &&& 0xFFFF#32
                have hlt28 := hkc.1.length_lt; have hlen_ge := hkc.1.length_ge
                have h15 : (kbc[15]?.getD 0#32).toNat = acap.toNat := by
                  have := hkc.2.2.1 15 (by omega) (Or.inl (by omega))
                  rw [this, m8_k6_get_eq (by omega), hacap_def]
                have h1nc : (kbc[1]?.getD 0#32) = nc := by
                  have := hkc.2.2.1 1 (by omega) (Or.inl (by omega))
                  rw [this, m8_k6_get_eq (by omega), hnc_def]
                have hkcl := hkc.1.clause_ok (by rw [h1nc]; exact hc_i_lt)
                have hno_ov1 : off_c.toNat + sz_c.toNat < 2 ^ 32 := by
                  have h1 := hkcl.1
                  rw [m8_k6_get_eq hbd_1888, m8_k6_get_eq hbd_c, h15] at h1
                  dsimp only [off_c, sz_c, cm] at h1 ⊢
                  have := hlt28; have := hlen_ge; omega
                have hsz_lt : sz_c.toNat < 65536 := by
                  dsimp only [sz_c]; rw [BitVec.toNat_and]
                  exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
                c0_hsteps_nogrp
                dsimp only [Prod.fst]
                have hget_c_raw : ∀ h, kbc[(BitVec.setWidth 64
                    ((2144 : BitVec 32) + (cid_c - (1 : BitVec 32)))).toNat]'h = cm := fun h =>
                  m8_k6_get_congr (show (BitVec.setWidth 64
                    ((2144 : BitVec 32) + (cid_c - (1 : BitVec 32)))).toNat = 2144 + c_i.toNat from
                    hc_2144_idx) h hbd_c
                have hget_1888_raw : ∀ h, kbc[(BitVec.setWidth 64
                    ((1888 : BitVec 32) + (cid_c - (1 : BitVec 32)))).toNat]'h = off_c := fun h =>
                  m8_k6_get_congr (show (BitVec.setWidth 64
                    ((1888 : BitVec 32) + (cid_c - (1 : BitVec 32)))).toNat = 1888 + c_i.toNat from
                    hc_1888_idx) h hbd_1888
                simp only [hget_c_raw, hget_1888_raw]
                refine wp_join_state1 (t := .bool) (α := List (BitVec 32) × Bool) (fun x => x.2)
                  (fun x mc' => invCore x.1 ∧ (array (t := i32) pk x.1 ⋆ R) mc') ?_ ?_
                · rintro _ ⟨kbc', ch'⟩ mc' ⟨hkc', hmc'⟩
                  have h_lits := k6_core_lits_wp (Γ := Γ) (Q := Q) (X := X) (ch_c := ch')
                    (Jcid := Jcid) hlen hnc_le hnv_le
                    (fun ch'' mc'' kbc'' hkc'' hmc'' => hJcid (kbc'', ch'') mc'' ⟨hkc'', hmc''⟩)
                    hkc' hmc' hno_ov1 hsz_lt hacap_def.symm hnv_def.symm
                  dsimp only [k6CoreLitsE, k6CoreCidStepE, k6FixpointE, k6SLet, k6SLetI, k6SLd,
                    k6SJF, k6SJT, k6SGrpBI, k6SGrpB2, k6SGrpB2b, k6SGrpKB, k6SGrpBB,
                    k6DfltT, k6Dflt] at h_lits
                  exact h_lits
                · intro Jlrn hJlrn
                  have h_lrn := k6_core_lrn_wp (Γ := Γ) (Q := Q) (X := X) (ch_c := ch_c)
                    (Jlrn := Jlrn) hlen hnc_le hc_i_lt rfl
                    (fun ch' mj' kbj' hkj' hmj' => hJlrn (kbj', ch') mj' ⟨hkj', hmj'⟩)
                    hkc hmc (by
                      rw [m8_k6_get_eq hbd_1888, m8_k6_get_eq hbd_c, h15] at hkcl; exact hkcl)
                    hno_ov1 hacap_def.symm
                  dsimp only [k6CoreLrnE, k6CoreCidStepE, k6FixpointE, k6SLet, k6SLetI, k6SLd,
                    k6SJF, k6SJT, k6SGrpBI, k6SGrpB2, k6SGrpB2b, k6SGrpKB,
                    k6DfltT, k6Dflt] at h_lrn
                  exact h_lrn
              · c0_hsteps!; exact hJcid (kbc, ch_c) mc ⟨hkc, hmc⟩
          · c0_hsteps!; exact hLp (nc.toNat - (pass + 1#32).toNat)
              (pass + 1#32, ch_c, ()) mc (by omega) ⟨kbc, hkc, by omega, rfl, hmc⟩
        · intro Lc hLc; c0_hsteps!
          exact hLc nc.toNat (false, nc, ()) mp ⟨kbp, hkp, Nat.le_refl _, rfl, hmp⟩
      · c0_hsteps!; exact hRet kbp mp hkp hmp
    · c0_hsteps!; exact hRet kbp mp hkp hmp
  · intro Lp hLp; c0_hsteps!
    exact hLp nc.toNat (0#32, true, ()) mj ⟨kbj, hkj, Nat.zero_le _, by simp, hmj⟩

end

end LeanQbe.T.Examples.Kissat.Proof.Definition
