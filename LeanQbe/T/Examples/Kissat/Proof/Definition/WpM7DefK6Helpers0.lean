/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Definition.Inv

/-!
# M7 `def_k6_m7` Sub-Phase Helpers Part 0 (`Proof.Definition.WpM7DefK6Helpers0`)

Exports:
- Shared bitvector/metadata/K6BufOk helpers not in `Inv`:
  `m7_p6_trivial_widx`, `m7_p6_post_widx`, `m7_p6_fullMem_subst`, `m7_p6_tmk_reg`,
  `m7_p6_eid_bounds`, `m7_p6_k6BufOk_of_init`, `m7_p6_k6BufOk_watch_frame`,
  `m7_p6_k6BufOk_core_frame`, `m7_p6_scr_h`, `m7_p6_scr_h_props`
- `m7_p6_k6_watch_solve_wp`
- `m7_p6_copy_clause_wp`
- `m7_p6_scan_large_wp`
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Definition

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Definition.Spec
open Kraken.Bedrock2.Test

open scoped FullArenaTactics K6Tactics P6Tactics

local macro "m7_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

public section

private theorem m6_getElem_congr {α : Type} {xs : List α} {i j : Nat} (h : i = j)
    (hi : i < xs.length) (hj : j < xs.length) : xs[i]'hi = xs[j]'hj := by
  subst h; rfl

theorem m7_p6_trivial_widx (eid : BitVec 32)
    (hidx : (eid &&& 0x3FF#32).toNat < 512) :
    let idx := eid &&& 0x3FF#32
    let mbase := if (eid >>> (10 : Nat)) == 0#32 then 1024#32 else 1040#32
    1024 ≤ (mbase + (idx >>> (5 : Nat))).toNat ∧
    (mbase + (idx >>> (5 : Nat))).toNat < 1056 := by
  intro idx mbase
  have hsh : (idx >>> (5 : Nat)).toNat < 16 := by
    dsimp only [idx]
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, show 2 ^ 5 = 32 from rfl]
    omega
  dsimp only [mbase]
  split
  · rw [BitVec.toNat_add, show (1024#32 : BitVec 32).toNat = 1024 from rfl,
      Nat.mod_eq_of_lt (by omega)]; omega
  · rw [BitVec.toNat_add, show (1040#32 : BitVec 32).toNat = 1040 from rfl,
      Nat.mod_eq_of_lt (by omega)]; omega

theorem m7_p6_post_widx (eid : BitVec 32) :
    let idx := eid &&& 0x3FF#32
    let mbase := if (eid >>> (10 : Nat)) == 0#32 then 1024#32 else 1040#32
    1024 ≤ (mbase + (idx >>> (5 : Nat))).toNat ∧
    (mbase + (idx >>> (5 : Nat))).toNat < 1072 := by
  intro idx mbase
  have hidx : idx.toNat < 1024 := by
    dsimp only [idx]
    rw [BitVec.toNat_and, show (0x3FF#32 : BitVec 32).toNat = 2 ^ 10 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod]
    omega
  have hsh : (idx >>> (5 : Nat)).toNat < 32 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, show 2 ^ 5 = 32 from rfl]; omega
  dsimp only [mbase]
  split
  · rw [BitVec.toNat_add, show (1024#32 : BitVec 32).toNat = 1024 from rfl,
      Nat.mod_eq_of_lt (by omega)]; omega
  · rw [BitVec.toNat_add, show (1040#32 : BitVec 32).toNat = 1040 from rfl,
      Nat.mod_eq_of_lt (by omega)]; omega

theorem m7_p6_fullMem_subst {c : FullCfg} {s1 s2 : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (FullMem c s1 ⋆ R) m)
    (hc : s1.core = s2.core := by rfl) (hs : s1.scratch = s2.scratch := by rfl) :
    (FullMem c s2 ⋆ R) m := by
  cases s1; cases s2; simp only at hc hs; subst hc; subst hs; exact hm

theorem m7_p6_tmk_reg {cv mc : Nat} {nv : BitVec 32}
    {exp tmk : List (BitVec 32)} {lv : BitVec 32}
    (hnv_lt : nv.toNat < 64) (hnv_cv : nv.toNat < 2 * cv)
    (hexpl : nv.toNat < exp.length) (htmkl : tmk.length = 2 * mc)
    (hcv_le : cv ≤ mc) (hlv : lv.toNat < cv)
    (hexp_bnd : ∀ k < nv.toNat, (exp[k]?.getD 0#32).toNat < cv)
    (htmk_inv : ∀ u < cv, tmk[u]?.getD 0#32 ≠ 0#32 →
      1 ≤ (tmk[u]?.getD 0#32).toNat ∧ (tmk[u]?.getD 0#32).toNat ≤ nv.toNat ∧
      ∃ k < nv.toNat, (exp[k]?.getD 0#32).toNat = u) :
    let exp' := exp.set nv.toNat lv
    let nv' := nv + 1#32
    let tmk' := tmk.set lv.toNat nv'
    nv'.toNat = nv.toNat + 1 ∧
    nv'.toNat ≤ 64 ∧ nv'.toNat ≤ 2 * cv ∧
    (∀ k < nv'.toNat, (exp'[k]?.getD 0#32).toNat < cv) ∧
    (∀ u < cv, tmk'[u]?.getD 0#32 ≠ 0#32 →
      1 ≤ (tmk'[u]?.getD 0#32).toNat ∧ (tmk'[u]?.getD 0#32).toNat ≤ nv'.toNat ∧
      ∃ k < nv'.toNat, (exp'[k]?.getD 0#32).toNat = u) ∧
    1 ≤ (tmk'[lv.toNat]?.getD 0#32).toNat ∧ (tmk'[lv.toNat]?.getD 0#32).toNat ≤ nv'.toNat := by
  intro exp' nv' tmk'
  have hlv_tmk : lv.toNat < tmk.length := by omega
  have hnv1 : nv'.toNat = nv.toNat + 1 := by
    dsimp only [nv']; rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl,
      Nat.mod_eq_of_lt (by omega)]
  have hset_lv : tmk'[lv.toNat]?.getD 0#32 = nv' := by
    dsimp only [tmk']; rw [List.getElem?_set_self hlv_tmk, Option.getD_some]
  refine ⟨hnv1, by omega, by omega, fun k hk => ?_, fun u hu hnz => ?_,
    by rw [hset_lv, hnv1]; omega, by rw [hset_lv, hnv1]; omega⟩
  · dsimp only [exp']
    rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp (hnv1 ▸ hk)) with hlt | rfl
    · rw [List.getElem?_set_ne (by omega)]; exact hexp_bnd k hlt
    · rw [List.getElem?_set_self hexpl, Option.getD_some]; exact hlv
  · dsimp only [tmk']
    by_cases hul : u = lv.toNat
    · subst hul; rw [List.getElem?_set_self hlv_tmk, Option.getD_some, hnv1]
      refine ⟨by omega, by omega, nv.toNat, by omega, ?_⟩
      dsimp only [exp']; rw [List.getElem?_set_self hexpl, Option.getD_some]
    · rw [List.getElem?_set_ne (Ne.symm hul)] at hnz ⊢
      obtain ⟨h1, h2, k, hk, hwk⟩ := htmk_inv u hu hnz
      refine ⟨h1, by omega, k, by omega, ?_⟩
      dsimp only [exp']; rw [List.getElem?_set_ne (by omega)]; exact hwk

theorem m7_p6_eid_bounds {side idx : BitVec 32} (hside : side.toNat < 2)
    (hidx : idx.toNat < 128) :
    let eid := (side <<< (10 : Nat)) ||| idx
    eid ≠ 0xFFFFFFFF#32 ∧ (eid &&& 0x3FF#32).toNat < 512 := by
  intro eid
  have hsh : (side <<< (10 : Nat)).toNat = side.toNat * 1024 := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]
  have heid_lt : eid.toNat < 2048 := by
    dsimp only [eid]; rw [BitVec.toNat_or, hsh]
    exact Nat.or_lt_two_pow (by omega : side.toNat * 1024 < 2 ^ 11) (by omega)
  refine ⟨fun heq => by
    have h0 := congrArg BitVec.toNat heq
    rw [show (0xFFFFFFFF#32 : BitVec 32).toNat = 4294967295 from rfl] at h0; omega, ?_⟩
  have hmod : (eid &&& 0x3FF#32).toNat = idx.toNat := by
    rw [BitVec.toNat_and, show (0x3FF#32 : BitVec 32).toNat = 1023 from rfl]
    apply Nat.eq_of_testBit_eq; intro k
    rw [Nat.testBit_and, BitVec.toNat_or, Nat.testBit_or, hsh]
    by_cases hk : k < 10
    · have ht1 : Nat.testBit (side.toNat * 1024) k = false := by
        rw [show side.toNat * 1024 = side.toNat * 2 ^ 10 from rfl,
          Nat.mul_comm, Nat.testBit_two_pow_mul]
        simp [Nat.not_le_of_lt hk]
      have ht2 : Nat.testBit 1023 k = true := by
        rw [show (1023 : Nat) = 2 ^ 10 - 1 from rfl, Nat.testBit_two_pow_sub_one]
        exact decide_eq_true hk
      simp [ht1, ht2]
    · have ht3 : Nat.testBit 1023 k = false := by
        rw [show (1023 : Nat) = 2 ^ 10 - 1 from rfl, Nat.testBit_two_pow_sub_one]
        exact decide_eq_false hk
      have ht4 : Nat.testBit idx.toNat k = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hidx
          (Nat.le_trans (by decide : 128 ≤ 2 ^ 10)
            (Nat.pow_le_pow_right (by decide) (by omega))))
      simp [ht3, ht4]
  omega

theorem m7_p6_k6BufOk_of_init {kb : List (BitVec 32)}
    (hcap : 2912 + (kb[15]?.getD 0#32).toNat ≤ kb.length)
    (hlt28 : kb.length < 2 ^ 28)
    (hnc : (kb[1]?.getD 0#32).toNat ≤ 128)
    (halen : (kb[14]?.getD 0#32).toNat ≤ (kb[15]?.getD 0#32).toNat)
    (hcl : ∀ cid < (kb[1]?.getD 0#32).toNat,
      (kb[1888 + cid]?.getD 0#32).toNat + ((kb[2144 + cid]?.getD 0#32) &&& 0xFFFF#32).toNat ≤
        (kb[15]?.getD 0#32).toNat ∧
      ((kb[2144 + cid]?.getD 0#32) &&& 0x40000000#32) = 0#32) :
    K6BufOk kb :=
  Spec.K6BufOk.mk_of hcap hlt28 (by omega) halen fun cid hcid =>
    let hc := hcl cid hcid
    ⟨hc.1, fun hnz => absurd hc.2 hnz⟩

theorem m7_p6_k6BufOk_watch_frame {kb kb' : List (BitVec 32)}
    (h : K6BufOk kb) (hlen : kb'.length = kb.length)
    (hkeep : ∀ idx < kb.length, (idx < 736 ∨ 1888 ≤ idx) → kb'[idx]? = kb[idx]?) :
    K6BufOk kb' := by
  have hb := h.base_ge
  exact k6BufOk_of_frame h hlen fun idx hi hor => by
    rcases hor with rfl | rfl | rfl | ⟨_, _⟩
    · exact hkeep 1 (by omega) (Or.inl (by decide))
    · exact hkeep 14 (by omega) (Or.inl (by decide))
    · exact hkeep 15 (by omega) (Or.inl (by decide))
    · exact hkeep idx hi (Or.inr (by omega))

theorem m7_p6_k6BufOk_core_frame {kb kb' : List (BitVec 32)}
    (h : K6BufOk kb) (hlen : kb'.length = kb.length)
    (hkeep : ∀ idx < kb.length,
      (idx < 416 ∨ (480 ≤ idx ∧ idx < 2144) ∨ 2400 ≤ idx) → kb'[idx]? = kb[idx]?)
    (hm : ∀ cid < (kb[1]?.getD 0#32).toNat,
      let m0 := kb[2144 + cid]?.getD 0#32
      let m1 := kb'[2144 + cid]?.getD 0#32
      (m1 &&& 0xFFFF#32) = (m0 &&& 0xFFFF#32) ∧
      (m1 &&& 0x40000000#32) = (m0 &&& 0x40000000#32)) :
    K6BufOk kb' := by
  have hb := h.base_ge
  have hk1 : kb'[1]? = kb[1]? := hkeep 1 (by omega) (Or.inl (by decide))
  have hk14 : kb'[14]? = kb[14]? := hkeep 14 (by omega) (Or.inl (by decide))
  have hk15 : kb'[15]? = kb[15]? := hkeep 15 (by omega) (Or.inl (by decide))
  refine Spec.K6BufOk.mk_of (by rw [hk15, hlen]; exact h.length_ge)
    (by rw [hlen]; exact h.length_lt)
    (by rw [hk1]; exact h.nc_le) (by rw [hk14, hk15]; exact h.alen_le) fun cid hcid => ?_
  rw [hk1] at hcid
  have hnc := h.nc_le
  have ho : kb'[1888 + cid]? = kb[1888 + cid]? :=
    hkeep (1888 + cid) (by omega) (Or.inr (Or.inl (by omega)))
  have ha : kb'[2400 + cid]? = kb[2400 + cid]? :=
    hkeep (2400 + cid) (by omega) (Or.inr (Or.inr (by omega)))
  have hmc := hm cid hcid
  dsimp only at hmc ⊢
  rw [ho, ha, hk15, hmc.1, hmc.2]
  exact h.clause_ok hcid

@[expose] def m7_p6_scr_h (scr_e : List (BitVec 32))
    (nv_s nc_s alen_s acap_w nunits_s : BitVec 32) : List (BitVec 32) :=
  (((((((((((((((((((((scr_e.set 1096 nv_s).set 1097 nc_s).set
    1098 nc_s).set 1099 0#32).set 1100 0#32).set 1101 0#32).set
    1102 nv_s).set 1103 0xFFFFFFFF#32).set 1104 0#32).set
    1105 (nv_s - 1#32)).set 1106 (nv_s - 1#32)).set
    1107 nv_s).set 1108 0#32).set 1109 512#32).set
    1110 alen_s).set 1111 acap_w).set
    1112 0#32).set 1113 0#32).set 1114 0#32).set
    1115 nunits_s).set 1116 0#32).set 1117 0#32

theorem m7_p6_scr_h_props {scr_e : List (BitVec 32)} {cap : Nat}
    (hlen : scr_e.length = cap) (h8192 : 8192 ≤ cap)
    (nv_s nc_s alen_s acap_w nunits_s : BitVec 32) :
    let scr_h := m7_p6_scr_h scr_e nv_s nc_s alen_s acap_w nunits_s
    scr_h.length = cap ∧
    (∀ k < 1096, scr_h[k]? = scr_e[k]?) ∧
    (∀ k, 1888 ≤ k → k < 2656 → scr_h[1096 + k]? = scr_e[1096 + k]?) ∧
    scr_h[1096 + 1]? = some nc_s ∧ scr_h[1096 + 2]? = some nc_s ∧
    scr_h[1096 + 14]? = some alen_s ∧ scr_h[1096 + 15]? = some acap_w := by
  refine ⟨by simp [m7_p6_scr_h, hlen], fun k hk => ?_, fun k hk1 hk2 => ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [m7_p6_scr_h]; repeat rw [List.getElem?_set_ne (by omega)]
  · dsimp only [m7_p6_scr_h]; repeat rw [List.getElem?_set_ne (by omega)]
  · dsimp only [m7_p6_scr_h]; repeat rw [List.getElem?_set_ne (by decide)]
    exact List.getElem?_set_self (by simp [hlen]; omega)
  · dsimp only [m7_p6_scr_h]; repeat rw [List.getElem?_set_ne (by decide)]
    exact List.getElem?_set_self (by simp [hlen]; omega)
  · dsimp only [m7_p6_scr_h]; repeat rw [List.getElem?_set_ne (by decide)]
    exact List.getElem?_set_self (by simp [hlen]; omega)
  · dsimp only [m7_p6_scr_h]; repeat rw [List.getElem?_set_ne (by decide)]
    exact List.getElem?_set_self (by simp [hlen]; omega)

/-! ## 1. K6 Watch/Solve/Core/Mark Sub-Phase Helper (`m7_p6_k6_watch_solve_wp`) -/

@[expose] def m7P6K6WatchBody (pk : BitVec 64) (i sz : BitVec 32)
    (k : Expr Val Cont []) : Expr Val Cont [] :=
  Expr.let_ ⟨OpCode.add i32, (Arg.imm 1888, Arg.var i, ())⟩ fun p1 =>
  Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p1.fst, ())⟩ fun p2 =>
  Expr.let_ ⟨OpCode.mul i64, (Arg.var p2.fst, Arg.imm 4, ())⟩ fun p3 =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var pk, Arg.var p3.fst, ())⟩ fun p4 =>
  Expr.load i32 (Arg.var p4.fst) fun ld0 =>
  Expr.let_ ⟨OpCode.add i32, (Arg.imm 2912, Arg.var ld0, ())⟩ fun p5 =>
  Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p5.fst, ())⟩ fun p6 =>
  Expr.let_ ⟨OpCode.mul i64, (Arg.var p6.fst, Arg.imm 4, ())⟩ fun p7 =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var pk, Arg.var p7.fst, ())⟩ fun p8 =>
  Expr.load i32 (Arg.var p8.fst) fun ld1 =>
  Expr.let_ ⟨OpCode.add i32, (Arg.imm 2912, Arg.var ld0, ())⟩ fun p9 =>
  Expr.let_ ⟨OpCode.add i32, (Arg.var p9.fst, Arg.imm 1, ())⟩ fun p10 =>
  Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p10.fst, ())⟩ fun p11 =>
  Expr.let_ ⟨OpCode.mul i64, (Arg.var p11.fst, Arg.imm 4, ())⟩ fun p12 =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var pk, Arg.var p12.fst, ())⟩ fun p13 =>
  Expr.load i32 (Arg.var p13.fst) fun ld2 =>
  Expr.call (as := [i64, i32, i32, i32, i32]) (bs := []) "full_k6_watch_m7"
    (Arg.var pk, Arg.var i, Arg.var ld1, Arg.var ld2, Arg.var sz, ()) fun _ => k

@[expose] def m7P6K6CoreMaskExpr (pScr : BitVec 64) (eid : BitVec 32)
    (k : Expr Val Cont []) : Expr Val Cont [] :=
  Expr.let_ ⟨OpCode.and i32, (Arg.var eid, Arg.imm 1023, ())⟩ fun pidx =>
  Expr.group (fun (_Js : Tup Cont [[i32]]) => Blocks.cons (fun pm =>
    Expr.let_ ⟨OpCode.lshr i32, (Arg.var pidx.fst, Arg.imm 5, ())⟩ fun p1 =>
    Expr.let_ ⟨OpCode.add i32, (Arg.var pm.fst, Arg.var p1.fst, ())⟩ fun p2 =>
    Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p2.fst, ())⟩ fun p3 =>
    Expr.let_ ⟨OpCode.mul i64, (Arg.var p3.fst, Arg.imm 4, ())⟩ fun p4 =>
    Expr.let_ ⟨OpCode.add i64, (Arg.var pScr, Arg.var p4.fst, ())⟩ fun p5 =>
    Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p2.fst, ())⟩ fun p6 =>
    Expr.let_ ⟨OpCode.mul i64, (Arg.var p6.fst, Arg.imm 4, ())⟩ fun p7 =>
    Expr.let_ ⟨OpCode.add i64, (Arg.var pScr, Arg.var p7.fst, ())⟩ fun p8 =>
    Expr.load i32 (Arg.var p8.fst) fun ld =>
    Expr.let_ ⟨OpCode.and i32, (Arg.var pidx.fst, Arg.imm 31, ())⟩ fun p9 =>
    Expr.let_ ⟨OpCode.shl i32, (Arg.imm 1, Arg.var p9.fst, ())⟩ fun p10 =>
    Expr.let_ ⟨OpCode.or i32, (Arg.var ld, Arg.var p10.fst, ())⟩ fun p11 =>
    Expr.store (t := i32) (Arg.var p11.fst) (Arg.var p5.fst) k) Blocks.nil) fun Js =>
  Expr.let_ ⟨OpCode.lshr i32, (Arg.var eid, Arg.imm 10, ())⟩ fun p1 =>
  Expr.let_ ⟨OpCode.cmp CmpOp.eq i32 Ty.bool rfl, (Arg.var p1.fst, Arg.imm 0, ())⟩ fun p2 =>
  Expr.jnz (Arg.var p2.fst) (Expr.jump Js.fst (Arg.imm 1024, ()))
    (Expr.jump Js.fst (Arg.imm 1040, ()))

@[expose] def m7P6K6StoreFlagExpr (pScr : BitVec 64) (off : Nat)
    (k : Expr Val Cont []) : Expr Val Cont [] :=
  Expr.let_ ⟨OpCode.sext 32 64, (Arg.imm off, ())⟩ fun p1 =>
  Expr.let_ ⟨OpCode.mul i64, (Arg.var p1.fst, Arg.imm 4, ())⟩ fun p2 =>
  Expr.let_ ⟨OpCode.add i64, (Arg.var pScr, Arg.var p2.fst, ())⟩ fun p3 =>
  Expr.store (t := i32) (Arg.imm 1) (Arg.var p3.fst) k

@[expose] def m7P6K6WatchSolveExpr (hdr pk pScr : BitVec 64) (nc : BitVec 32) :
    Expr Val Cont [] :=
  Expr.group (fun (Js3 : Tup Cont [[i32]]) => Blocks.cons (fun p =>
    Expr.let_ ⟨OpCode.cmp CmpOp.ult i32 Ty.bool rfl, (Arg.var p.fst, Arg.var nc, ())⟩ fun pc =>
    Expr.jnz (Arg.var pc.fst)
      (Expr.let_ ⟨OpCode.add i32, (Arg.imm 2144, Arg.var p.fst, ())⟩ fun p7 =>
      Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p7.fst, ())⟩ fun p8 =>
      Expr.let_ ⟨OpCode.mul i64, (Arg.var p8.fst, Arg.imm 4, ())⟩ fun p9 =>
      Expr.let_ ⟨OpCode.add i64, (Arg.var pk, Arg.var p9.fst, ())⟩ fun p10 =>
      Expr.load i32 (Arg.var p10.fst) fun ld =>
      Expr.let_ ⟨OpCode.and i32, (Arg.var ld, Arg.imm 65535, ())⟩ fun psz =>
      Expr.group (fun (_ : Tup Cont [[]]) => Blocks.cons (fun _ =>
        Expr.let_ ⟨OpCode.add i32, (Arg.var p.fst, Arg.imm 1, ())⟩ fun pi =>
        Expr.jump Js3.fst (Arg.var pi.fst, ())) Blocks.nil) fun JsN =>
      Expr.let_ ⟨OpCode.cmp CmpOp.uge i32 Ty.bool rfl, (Arg.var psz.fst, Arg.imm 2, ())⟩
        fun pg =>
      Expr.jnz (Arg.var pg.fst)
        (m7P6K6WatchBody pk p.fst psz.fst (Expr.jump JsN.fst ()))
        (Expr.jump JsN.fst ()))
      (Expr.call (as := [i64, i64, i32]) (bs := [i64]) "full_k6_solve_m7"
        (Arg.var hdr, Arg.var pk, Arg.imm 512, ()) fun ps =>
      Expr.let_ ⟨OpCode.cmp CmpOp.ne i64 Ty.bool rfl, (Arg.var ps.fst, Arg.imm 20, ())⟩ fun pn =>
      Expr.jnz (Arg.var pn.fst) (Expr.ret ())
        (Expr.call (as := [i64]) (bs := []) "full_k6_core_m7" (Arg.var pk, ()) fun _ =>
        Expr.let_ ⟨OpCode.zext 32 64, (Arg.imm 2, ())⟩ fun q1 =>
        Expr.let_ ⟨OpCode.mul i64, (Arg.var q1.fst, Arg.imm 4, ())⟩ fun q2 =>
        Expr.let_ ⟨OpCode.add i64, (Arg.var pk, Arg.var q2.fst, ())⟩ fun q3 =>
        Expr.load i32 (Arg.var q3.fst) fun onc =>
        Expr.group (fun (Js4 : Tup Cont [[i32, .bool]]) => Blocks.cons (fun p4 =>
          Expr.let_ ⟨OpCode.cmp CmpOp.ult i32 Ty.bool rfl, (Arg.var p4.fst, Arg.var onc, ())⟩
            fun p7 =>
          Expr.jnz (Arg.var p7.fst)
            (Expr.group (fun (_ : Tup Cont [[.bool]]) => Blocks.cons (fun p8 =>
              Expr.let_ ⟨OpCode.add i32, (Arg.var p4.fst, Arg.imm 1, ())⟩ fun pi =>
              Expr.jump Js4.fst (Arg.var pi.fst, Arg.var p8.fst, ())) Blocks.nil) fun JsS =>
            Expr.let_ ⟨OpCode.add i32, (Arg.imm 2144, Arg.var p4.fst, ())⟩ fun p8 =>
            Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p8.fst, ())⟩ fun p9 =>
            Expr.let_ ⟨OpCode.mul i64, (Arg.var p9.fst, Arg.imm 4, ())⟩ fun p10 =>
            Expr.let_ ⟨OpCode.add i64, (Arg.var pk, Arg.var p10.fst, ())⟩ fun p11 =>
            Expr.load i32 (Arg.var p11.fst) fun ld =>
            Expr.let_ ⟨OpCode.and i32, (Arg.var ld, Arg.imm 536870912, ())⟩ fun p12 =>
            Expr.let_ ⟨OpCode.cmp CmpOp.ne i32 Ty.bool rfl, (Arg.var p12.fst, Arg.imm 0, ())⟩
              fun p13 =>
            Expr.jnz (Arg.var p13.fst)
              (Expr.let_ ⟨OpCode.add i32, (Arg.imm 2400, Arg.var p4.fst, ())⟩ fun r1 =>
              Expr.let_ ⟨OpCode.zext 32 64, (Arg.var r1.fst, ())⟩ fun r2 =>
              Expr.let_ ⟨OpCode.mul i64, (Arg.var r2.fst, Arg.imm 4, ())⟩ fun r3 =>
              Expr.let_ ⟨OpCode.add i64, (Arg.var pk, Arg.var r3.fst, ())⟩ fun r4 =>
              Expr.load i32 (Arg.var r4.fst) fun eid =>
              m7P6K6CoreMaskExpr pScr eid (Expr.jump JsS.fst (Arg.imm true, ())))
              (Expr.jump JsS.fst (Arg.var p4.snd.fst, ())))
            (Expr.group (fun (_JsR : Tup Cont [[]]) => Blocks.cons (fun _ => Expr.ret ())
                Blocks.nil) fun JsR =>
              Expr.jnz (Arg.var p4.snd.fst)
                (m7P6K6StoreFlagExpr pScr 1056
                  (m7P6K6StoreFlagExpr pScr 1057 (Expr.jump JsR.fst ())))
                (Expr.jump JsR.fst ()))) Blocks.nil) fun Js4 =>
          Expr.jump Js4.fst (Arg.imm 0, Arg.imm false, ()))))
    Blocks.nil) fun Js3 => Expr.jump Js3.fst (Arg.imm 0, ())

private theorem m7_p6_k6_core_mark_wp (Γ : Env) (c : FullCfg) (s0 s_clr : FullState)
    (R : Mem 64 → Prop) (scr_pre kb5 scr2 : List (BitVec 32)) (pk : BitVec 64)
    (fuel64 : BitVec 64) (m5 : Mem 64) (Q : Post []) (X : XPost)
    (hpk : pk = c.pScratchBuf + BitVec.ofNat 64 1096 * 4)
    (hsc_cap : c.scratch_cap < 2 ^ 28) (hsc8192 : 8192 ≤ c.scratch_cap)
    (hfl4' : fuel64.toNat ≤ s0.core.fuel.toNat) (hsc2_l : scr2.length = c.scratch_cap)
    (hpre_l : scr_pre.length = 1096) (hpre_take : scr_pre = scr2.take 1096)
    (hpre2 : ∀ k < 1024, scr2[k]? = s0.scratch.scratch_buf[k]?)
    (h5_nc : (kb5[2]?.getD 0#32).toNat ≤ 128)
    (hkb5_l : scr_pre.length + kb5.length = c.scratch_cap)
    (hQ : ∀ fl' scr' m',
      fl'.toNat ≤ s0.core.fuel.toNat → scr'.length = c.scratch_cap →
      (∀ k < 1024, scr'[k]? = s0.scratch.scratch_buf[k]?) →
      (FullMem c { s_clr with
        core := { s_clr.core with fuel := fl' }
        scratch := { s_clr.scratch with scratch_buf := scr' } } ⋆ R) m' →
      Q () m')
    (hm5 : (array (t := i32) (c.pScratchBuf + BitVec.ofNat 64 1096 * 4) kb5 ⋆
      (array64 (c.hdr + 32) ((hdrTailWords c s_clr).set 17 fuel64) ⋆
       array (t := i32) c.pScratchBuf scr_pre ⋆ m7_p6_fullK6Outer c s_clr ⋆ R)) m5) :
    wp Γ Q X
      (Expr.let_ ⟨OpCode.zext 32 64, (Arg.imm 2, ())⟩ fun q1 =>
       Expr.let_ ⟨OpCode.mul i64, (Arg.var q1.fst, Arg.imm 4, ())⟩ fun q2 =>
       Expr.let_ ⟨OpCode.add i64, (Arg.var pk, Arg.var q2.fst, ())⟩ fun q3 =>
       Expr.load i32 (Arg.var q3.fst) fun onc =>
       Expr.group (fun (Js4 : Tup Cont [[i32, .bool]]) => Blocks.cons (fun p4 =>
         Expr.let_ ⟨OpCode.cmp CmpOp.ult i32 Ty.bool rfl, (Arg.var p4.fst, Arg.var onc, ())⟩
           fun p7 =>
         Expr.jnz (Arg.var p7.fst)
           (Expr.group (fun (_ : Tup Cont [[.bool]]) => Blocks.cons (fun p8 =>
             Expr.let_ ⟨OpCode.add i32, (Arg.var p4.fst, Arg.imm 1, ())⟩ fun pi =>
             Expr.jump Js4.fst (Arg.var pi.fst, Arg.var p8.fst, ())) Blocks.nil) fun JsS =>
           Expr.let_ ⟨OpCode.add i32, (Arg.imm 2144, Arg.var p4.fst, ())⟩ fun p8 =>
           Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p8.fst, ())⟩ fun p9 =>
           Expr.let_ ⟨OpCode.mul i64, (Arg.var p9.fst, Arg.imm 4, ())⟩ fun p10 =>
           Expr.let_ ⟨OpCode.add i64, (Arg.var pk, Arg.var p10.fst, ())⟩ fun p11 =>
           Expr.load i32 (Arg.var p11.fst) fun ld =>
           Expr.let_ ⟨OpCode.and i32, (Arg.var ld, Arg.imm 536870912, ())⟩ fun p12 =>
           Expr.let_ ⟨OpCode.cmp CmpOp.ne i32 Ty.bool rfl, (Arg.var p12.fst, Arg.imm 0, ())⟩
             fun p13 =>
           Expr.jnz (Arg.var p13.fst)
             (Expr.let_ ⟨OpCode.add i32, (Arg.imm 2400, Arg.var p4.fst, ())⟩ fun r1 =>
             Expr.let_ ⟨OpCode.zext 32 64, (Arg.var r1.fst, ())⟩ fun r2 =>
             Expr.let_ ⟨OpCode.mul i64, (Arg.var r2.fst, Arg.imm 4, ())⟩ fun r3 =>
             Expr.let_ ⟨OpCode.add i64, (Arg.var pk, Arg.var r3.fst, ())⟩ fun r4 =>
             Expr.load i32 (Arg.var r4.fst) fun eid =>
             m7P6K6CoreMaskExpr c.pScratchBuf eid (Expr.jump JsS.fst (Arg.imm true, ())))
             (Expr.jump JsS.fst (Arg.var p4.snd.fst, ())))
           (Expr.group (fun (_JsR : Tup Cont [[]]) => Blocks.cons (fun _ => Expr.ret ())
               Blocks.nil) fun JsR =>
             Expr.jnz (Arg.var p4.snd.fst)
               (m7P6K6StoreFlagExpr c.pScratchBuf 1056
                 (m7P6K6StoreFlagExpr c.pScratchBuf 1057 (Expr.jump JsR.fst ())))
               (Expr.jump JsR.fst ()))) Blocks.nil) fun Js4 =>
         Expr.jump Js4.fst (Arg.imm 0, Arg.imm false, ())) m5 := by
  let s5 : FullState :=
    { s_clr with
      core := { s_clr.core with fuel := fuel64 }
      scratch := { s_clr.scratch with scratch_buf := scr_pre ++ kb5 } }
  have hm_un5 : (FullMem c s5 ⋆ R) m5 :=
    m7_p6_fullMem_unsplit_k6 (c := c) (s := s_clr)
      (fl' := fuel64) (scr_pre := scr_pre) (kb' := kb5) (R := R) hpre_l (sep_ac hm5)
  have hscr5_l : (scr_pre ++ kb5).length = c.scratch_cap := by
    rw [List.length_append]; exact hkb5_l
  have h1098_bd :
      1096 + (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 2)).toNat <
        s5.scratch.scratch_buf.length := by
    rw [show (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 2)).toNat = 2 from rfl]
    dsimp only [s5]; rw [hscr5_l]; omega
  have honc_eq : s5.scratch.scratch_buf[1096 + 2]?.getD 0#32 = kb5[2]?.getD 0#32 := by
    dsimp only [s5]
    rw [List.getElem?_append_right (by omega), hpre_l, show 1096 + 2 - 1096 = 2 from rfl]
  clear hm5
  subst hpk
  c0_hsteps_nogrp
  refine wp_loop_group (ts := [i32, .bool])
    (fun rem4 (i, any4, ()) m4' => ∃ scr4' : List (BitVec 32),
      let s4' : FullState := { s5 with scratch := { s5.scratch with scratch_buf := scr4' } }
      scr4'.length = c.scratch_cap ∧
      i.toNat ≤ (kb5[2]?.getD 0#32).toNat ∧
      rem4 = (kb5[2]?.getD 0#32).toNat - i.toNat ∧
      (∀ k < 1024, scr4'[k]? = s0.scratch.scratch_buf[k]?) ∧
      (∀ k, 1096 ≤ k → k < c.scratch_cap → scr4'[k]? = s5.scratch.scratch_buf[k]?) ∧
      (FullMem c s4' ⋆ R) m4') ?_ ?_
  · rintro L4 rem4 ⟨i, any4, ⟨⟩⟩ m4' hL4 ⟨scr4', hsc4'_l, hi_le, rfl, hpre4', hhi4', hm4'⟩
    c0_hsplit
    · have hi_lt : i.toNat < (kb5[2]?.getD 0#32).toNat := by
        have h2_bd : 1096 + 2 < s5.scratch.scratch_buf.length := by
          dsimp only [s5]; rw [hscr5_l]; omega
        have hval : (s5.scratch.scratch_buf[1096 + 2]'h2_bd) = kb5[2]?.getD 0#32 := by
          have hgd : (some (s5.scratch.scratch_buf[1096 + 2]'h2_bd)).getD 0#32 =
              s5.scratch.scratch_buf[1096 + 2]'h2_bd := rfl
          rw [← hgd, ← List.getElem?_eq_getElem h2_bd]
          exact honc_eq
        change i.toNat < (s5.scratch.scratch_buf[1096 + 2]'h2_bd).toNat at hc
        simpa [hval] using hc
      have hi1 : (i + 1#32).toNat = i.toNat + 1 := m7_p6_add1_toNat (by omega)
      have hm_bd : 1096 + (2144 + i.toNat) < scr4'.length := by rw [hsc4'_l]; omega
      have hm_bd2 :
          1096 + (((@OfNat.ofNat (BitVec 32) 2144 (BitVec.instOfNat)) +
            i).setWidth 64).toNat < scr4'.length := by
        rw [m7_p6_off_add 2144 (by decide) i (by omega)]; exact hm_bd
      have ha_bd : 1096 + (2400 + i.toNat) < scr4'.length := by rw [hsc4'_l]; omega
      have ha_bd2 :
          1096 + (((@OfNat.ofNat (BitVec 32) 2400 (BitVec.instOfNat)) +
            i).setWidth 64).toNat < scr4'.length := by
        rw [m7_p6_off_add 2400 (by decide) i (by omega)]; exact ha_bd
      c0_hsteps_nogrp; c0_hstep; c0_hsplit
      · unfold m7P6K6CoreMaskExpr
        let eid4 :=
          scr4'[(1096 + (((@OfNat.ofNat (BitVec 32) 2400 (BitVec.instOfNat)) +
            i).setWidth 64).toNat)]'ha_bd2
        let idx4 := eid4 &&& 0x3FF#32
        have hidx4_sh : (idx4 >>> (5 : Nat)).toNat < 32 := by
          dsimp only [idx4]
          rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, show 2 ^ 5 = 32 from rfl,
            BitVec.toNat_and, show (0x3FF#32 : BitVec 32).toNat = 2 ^ 10 - 1 from rfl,
            Nat.and_two_pow_sub_one_eq_mod]
          omega
        c0_hsteps_nogrp
        refine wp_join_state_pure (ts := [i32]) (α := BitVec 32) (fun m => (m, ()))
          (fun mb => mb = 1024#32 ∨ mb = 1040#32) ?_ ?_
        · intro _ mb hmb
          have hwi_lo : 1024 ≤ (mb + (idx4 >>> (5 : Nat))).toNat ∧
              (mb + (idx4 >>> (5 : Nat))).toNat < 1072 := by
            rcases hmb with rfl | rfl
            · rw [BitVec.toNat_add,
                show (1024#32 : BitVec 32).toNat = 1024 from rfl,
                Nat.mod_eq_of_lt (by omega)]; omega
            · rw [BitVec.toNat_add,
                show (1040#32 : BitVec 32).toNat = 1040 from rfl,
                Nat.mod_eq_of_lt (by omega)]; omega
          have hwi_sc : ((mb + (idx4 >>> (5 : Nat))).setWidth 64).toNat <
              scr4'.length := by
            rw [hsc4'_l, m6_zext32_toNat]; omega
          have hwi_lo' : 1024 ≤ ((mb + (idx4 >>> (5 : Nat))).setWidth 64).toNat := by
            rw [m6_zext32_toNat]; exact hwi_lo.1
          have hwi_hi' : ((mb + (idx4 >>> (5 : Nat))).setWidth 64).toNat < 1072 := by
            rw [m6_zext32_toNat]; exact hwi_lo.2
          c0_hsteps!
          let scr4'' := scr4'.set ((mb + (idx4 >>> (5 : Nat))).setWidth 64).toNat
            (scr4'[((mb + (idx4 >>> (5 : Nat))).setWidth 64).toNat]'hwi_sc |||
              (1#32 <<< ((idx4 &&& 31#32).toNat % 32)))
          exact hL4 ((kb5[2]?.getD 0#32).toNat - (i + 1#32).toNat)
            (i + 1#32, true, ()) _ (by omega)
            ⟨scr4'', by simp [scr4'', hsc4'_l], by omega, rfl,
              fun k hk => by
                dsimp only [scr4'']; rw [List.getElem?_set_ne (by omega)]; exact hpre4' k hk,
              fun k hk1 hk2 => by
                dsimp only [scr4'']; rw [List.getElem?_set_ne (by omega)]
                exact hhi4' k hk1 hk2,
              hm⟩
        · intro _ hJm; c0_hsplit
          · c0_hsteps!; exact hJm 1024#32 (Or.inl rfl)
          · c0_hsteps!; exact hJm 1040#32 (Or.inr rfl)
      · c0_hsteps!
        exact hL4 ((kb5[2]?.getD 0#32).toNat - (i + 1#32).toNat) (i + 1#32, any4, ()) m4'
          (by omega) ⟨scr4', hsc4'_l, by omega, rfl, hpre4', hhi4', hm4'⟩
    · unfold m7P6K6StoreFlagExpr
      have h1056_bd : (1056#64 : BitVec 64).toNat < scr4'.length := by
        rw [show (1056#64 : BitVec 64).toNat = 1056 from rfl, hsc4'_l]; omega
      c0_hsteps_nogrp; c0_hstep; c0_hsplit
      · have hm_s := m7_p6_scrBuf_split hsc8192 hsc4'_l hm4'
        have h1056_lt :
            (BitVec.signExtend 64 (Nat.cast 1056 : BitVec 32)).toNat < 8192 := by decide
        have h1057_lt :
            (BitVec.signExtend 64 (Nat.cast 1057 : BitVec 32)).toNat < 8192 := by decide
        c0_hsteps!
        let scrf := (scr4'.set 1056 1#32).set 1057 1#32
        have hscrf_l : scrf.length = c.scratch_cap := by simp [scrf, hsc4'_l]
        have hm' := m7_p6_scrBuf_unsplit hm
        refine hQ fuel64 scrf _ hfl4' hscrf_l (fun k hk => ?_)
          (m7_p6_fullMem_subst hm' rfl (by dsimp only [scrf]; rfl))
        dsimp only [scrf]
        rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
        exact hpre4' k (by omega)
      · c0_hsteps!
        exact hQ fuel64 scr4' m4' hfl4' hsc4'_l (fun k hk => hpre4' k (by omega)) hm4'
  · intro L4 hL4; c0_hsteps!
    refine hL4 (kb5[2]?.getD 0#32).toNat (0#32, false, ()) m5
      ⟨s5.scratch.scratch_buf, hscr5_l, Nat.zero_le _, rfl, fun k hk => ?_,
        fun _ _ _ => rfl, hm_un5⟩
    dsimp only [s5]
    rw [List.getElem?_append_left (by omega), hpre_take]
    have htake := List.getElem?_take (i := 1096) (l := scr2) (j := k)
    rw [ite_eq_left (by omega)] at htake
    rw [htake]; exact hpre2 k (by omega)

theorem m7_p6_k6_watch_solve_wp (Γ : Env)
    (hWatch : ∀ a m Q X, fullK6WatchM7Spec a m Q X →
      Γ "full_k6_watch_m7" [i64, i32, i32, i32, i32] [] a m Q X)
    (hSolve : ∀ a m Q X, fullK6SolveM7Spec a m Q X →
      Γ "full_k6_solve_m7" [i64, i64, i32] [i64] a m Q X)
    (hCore : ∀ a m Q X, fullK6CoreM7Spec a m Q X →
      Γ "full_k6_core_m7" [i64] [] a m Q X)
    (c : FullCfg) (s0 s_clr : FullState) (R : Mem 64 → Prop)
    (scr_pre kb_w0 scr2 : List (BitVec 32)) (nc_s : BitVec 32)
    (m_sp : Mem 64) (Q : Post []) (X : XPost)
    (hsc_cap : c.scratch_cap < 2 ^ 28) (hsc8192 : 8192 ≤ c.scratch_cap)
    (hnc128 : nc_s.toNat ≤ 128)
    (hclr_fl : s_clr.core.fuel = s0.core.fuel)
    (hscr2_l : scr2.length = c.scratch_cap)
    (hpre_l : scr_pre.length = 1096)
    (hpre_take : scr_pre = scr2.take 1096)
    (hpre2 : ∀ k < 1024, scr2[k]? = s0.scratch.scratch_buf[k]?)
    (hkbw0_eq : kb_w0 = scr2.drop 1096)
    (hkbw0_ok : K6BufOk kb_w0) (hkbw0_l : kb_w0.length = c.scratch_cap - 1096)
    (hs2_1 : scr2[1096 + 1]? = some nc_s) (hs2_2 : scr2[1096 + 2]? = some nc_s)
    (hm_sp : (array64 (c.hdr + 32) (hdrTailWords c s_clr) ⋆
      array (t := i32) (c.pScratchBuf + BitVec.ofNat 64 1096 * 4) kb_w0 ⋆
      (array (t := i32) c.pScratchBuf scr_pre ⋆
       m7_p6_fullK6Outer c s_clr ⋆ R)) m_sp)
    (hQ : ∀ fl' scr' m',
      fl'.toNat ≤ s0.core.fuel.toNat → scr'.length = c.scratch_cap →
      (∀ k < 1024, scr'[k]? = s0.scratch.scratch_buf[k]?) →
      (FullMem c { s_clr with
        core := { s_clr.core with fuel := fl' }
        scratch := { s_clr.scratch with scratch_buf := scr' } } ⋆ R) m' →
      Q () m') :
    let pk := c.pScratchBuf + BitVec.ofNat 64 1096 * 4
    wp Γ Q X (Expr.group (fun (Js3 : Tup Cont [[i32]]) => Blocks.cons (fun p =>
      Expr.let_ ⟨OpCode.cmp CmpOp.ult i32 Ty.bool rfl, (Arg.var p.fst, Arg.var nc_s, ())⟩
        fun pc =>
      Expr.jnz (Arg.var pc.fst)
        (Expr.let_ ⟨OpCode.add i32, (Arg.imm 2144, Arg.var p.fst, ())⟩ fun p7 =>
        Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p7.fst, ())⟩ fun p8 =>
        Expr.let_ ⟨OpCode.mul i64, (Arg.var p8.fst, Arg.imm 4, ())⟩ fun p9 =>
        Expr.let_ ⟨OpCode.add i64, (Arg.var pk, Arg.var p9.fst, ())⟩ fun p10 =>
        Expr.load i32 (Arg.var p10.fst) fun ld =>
        Expr.let_ ⟨OpCode.and i32, (Arg.var ld, Arg.imm 65535, ())⟩ fun psz =>
        Expr.group (fun (_ : Tup Cont [[]]) => Blocks.cons (fun _ =>
          Expr.let_ ⟨OpCode.add i32, (Arg.var p.fst, Arg.imm 1, ())⟩ fun pi =>
          Expr.jump Js3.fst (Arg.var pi.fst, ())) Blocks.nil) fun JsN =>
        Expr.let_ ⟨OpCode.cmp CmpOp.uge i32 Ty.bool rfl, (Arg.var psz.fst, Arg.imm 2, ())⟩
          fun pg =>
        Expr.jnz (Arg.var pg.fst)
          (Expr.let_ ⟨OpCode.add i32, (Arg.imm 1888, Arg.var p.fst, ())⟩ fun w1 =>
          Expr.let_ ⟨OpCode.zext 32 64, (Arg.var w1.fst, ())⟩ fun w2 =>
          Expr.let_ ⟨OpCode.mul i64, (Arg.var w2.fst, Arg.imm 4, ())⟩ fun w3 =>
          Expr.let_ ⟨OpCode.add i64, (Arg.var pk, Arg.var w3.fst, ())⟩ fun w4 =>
          Expr.load i32 (Arg.var w4.fst) fun ld0 =>
          Expr.let_ ⟨OpCode.add i32, (Arg.imm 2912, Arg.var ld0, ())⟩ fun w5 =>
          Expr.let_ ⟨OpCode.zext 32 64, (Arg.var w5.fst, ())⟩ fun w6 =>
          Expr.let_ ⟨OpCode.mul i64, (Arg.var w6.fst, Arg.imm 4, ())⟩ fun w7 =>
          Expr.let_ ⟨OpCode.add i64, (Arg.var pk, Arg.var w7.fst, ())⟩ fun w8 =>
          Expr.load i32 (Arg.var w8.fst) fun ld1 =>
          Expr.let_ ⟨OpCode.add i32, (Arg.imm 2912, Arg.var ld0, ())⟩ fun w9 =>
          Expr.let_ ⟨OpCode.add i32, (Arg.var w9.fst, Arg.imm 1, ())⟩ fun w10 =>
          Expr.let_ ⟨OpCode.zext 32 64, (Arg.var w10.fst, ())⟩ fun w11 =>
          Expr.let_ ⟨OpCode.mul i64, (Arg.var w11.fst, Arg.imm 4, ())⟩ fun w12 =>
          Expr.let_ ⟨OpCode.add i64, (Arg.var pk, Arg.var w12.fst, ())⟩ fun w13 =>
          Expr.load i32 (Arg.var w13.fst) fun ld2 =>
          Expr.call (as := [i64, i32, i32, i32, i32]) (bs := []) "full_k6_watch_m7"
            (Arg.var pk, Arg.var p.fst, Arg.var ld1, Arg.var ld2, Arg.var psz.fst, ())
            fun _ => Expr.jump JsN.fst ())
          (Expr.jump JsN.fst ()))
        (Expr.call (as := [i64, i64, i32]) (bs := [i64]) "full_k6_solve_m7"
          (Arg.var c.hdr, Arg.var pk, Arg.imm 512, ()) fun ps =>
        Expr.let_ ⟨OpCode.cmp CmpOp.ne i64 Ty.bool rfl, (Arg.var ps.fst, Arg.imm 20, ())⟩
          fun pn =>
        Expr.jnz (Arg.var pn.fst) (Expr.ret ())
          (Expr.call (as := [i64]) (bs := []) "full_k6_core_m7" (Arg.var pk, ()) fun _ =>
          Expr.let_ ⟨OpCode.zext 32 64, (Arg.imm 2, ())⟩ fun q1 =>
          Expr.let_ ⟨OpCode.mul i64, (Arg.var q1.fst, Arg.imm 4, ())⟩ fun q2 =>
          Expr.let_ ⟨OpCode.add i64, (Arg.var pk, Arg.var q2.fst, ())⟩ fun q3 =>
          Expr.load i32 (Arg.var q3.fst) fun onc =>
          Expr.group (fun (Js4 : Tup Cont [[i32, .bool]]) => Blocks.cons (fun p4 =>
            Expr.let_ ⟨OpCode.cmp CmpOp.ult i32 Ty.bool rfl, (Arg.var p4.fst, Arg.var onc, ())⟩
              fun p7 =>
            Expr.jnz (Arg.var p7.fst)
              (Expr.group (fun (_ : Tup Cont [[.bool]]) => Blocks.cons (fun p8 =>
                Expr.let_ ⟨OpCode.add i32, (Arg.var p4.fst, Arg.imm 1, ())⟩ fun pi =>
                Expr.jump Js4.fst (Arg.var pi.fst, Arg.var p8.fst, ())) Blocks.nil) fun JsS =>
              Expr.let_ ⟨OpCode.add i32, (Arg.imm 2144, Arg.var p4.fst, ())⟩ fun p8 =>
              Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p8.fst, ())⟩ fun p9 =>
              Expr.let_ ⟨OpCode.mul i64, (Arg.var p9.fst, Arg.imm 4, ())⟩ fun p10 =>
              Expr.let_ ⟨OpCode.add i64, (Arg.var pk, Arg.var p10.fst, ())⟩ fun p11 =>
              Expr.load i32 (Arg.var p11.fst) fun ld =>
              Expr.let_ ⟨OpCode.and i32, (Arg.var ld, Arg.imm 536870912, ())⟩ fun p12 =>
              Expr.let_ ⟨OpCode.cmp CmpOp.ne i32 Ty.bool rfl, (Arg.var p12.fst, Arg.imm 0, ())⟩
                fun p13 =>
              Expr.jnz (Arg.var p13.fst)
                (Expr.let_ ⟨OpCode.add i32, (Arg.imm 2400, Arg.var p4.fst, ())⟩ fun r1 =>
                Expr.let_ ⟨OpCode.zext 32 64, (Arg.var r1.fst, ())⟩ fun r2 =>
                Expr.let_ ⟨OpCode.mul i64, (Arg.var r2.fst, Arg.imm 4, ())⟩ fun r3 =>
                Expr.let_ ⟨OpCode.add i64, (Arg.var pk, Arg.var r3.fst, ())⟩ fun r4 =>
                Expr.load i32 (Arg.var r4.fst) fun eid =>
                Expr.let_ ⟨OpCode.and i32, (Arg.var eid, Arg.imm 1023, ())⟩ fun pidx =>
                Expr.group (fun (_Js : Tup Cont [[i32]]) => Blocks.cons (fun pm =>
                  Expr.let_ ⟨OpCode.lshr i32, (Arg.var pidx.fst, Arg.imm 5, ())⟩ fun k1 =>
                  Expr.let_ ⟨OpCode.add i32, (Arg.var pm.fst, Arg.var k1.fst, ())⟩ fun k2 =>
                  Expr.let_ ⟨OpCode.zext 32 64, (Arg.var k2.fst, ())⟩ fun k3 =>
                  Expr.let_ ⟨OpCode.mul i64, (Arg.var k3.fst, Arg.imm 4, ())⟩ fun k4 =>
                  Expr.let_ ⟨OpCode.add i64, (Arg.var c.pScratchBuf, Arg.var k4.fst, ())⟩
                    fun k5 =>
                  Expr.let_ ⟨OpCode.zext 32 64, (Arg.var k2.fst, ())⟩ fun k6 =>
                  Expr.let_ ⟨OpCode.mul i64, (Arg.var k6.fst, Arg.imm 4, ())⟩ fun k7 =>
                  Expr.let_ ⟨OpCode.add i64, (Arg.var c.pScratchBuf, Arg.var k7.fst, ())⟩
                    fun k8 =>
                  Expr.load i32 (Arg.var k8.fst) fun kld =>
                  Expr.let_ ⟨OpCode.and i32, (Arg.var pidx.fst, Arg.imm 31, ())⟩ fun k9 =>
                  Expr.let_ ⟨OpCode.shl i32, (Arg.imm 1, Arg.var k9.fst, ())⟩ fun k10 =>
                  Expr.let_ ⟨OpCode.or i32, (Arg.var kld, Arg.var k10.fst, ())⟩ fun k11 =>
                  Expr.store (t := i32) (Arg.var k11.fst) (Arg.var k5.fst)
                    (Expr.jump JsS.fst (Arg.imm true, ()))) Blocks.nil) fun Js =>
                Expr.let_ ⟨OpCode.lshr i32, (Arg.var eid, Arg.imm 10, ())⟩ fun m1 =>
                Expr.let_ ⟨OpCode.cmp CmpOp.eq i32 Ty.bool rfl, (Arg.var m1.fst, Arg.imm 0, ())⟩
                  fun m2 =>
                Expr.jnz (Arg.var m2.fst) (Expr.jump Js.fst (Arg.imm 1024, ()))
                  (Expr.jump Js.fst (Arg.imm 1040, ())))
                (Expr.jump JsS.fst (Arg.var p4.snd.fst, ())))
              (Expr.group (fun (_JsR : Tup Cont [[]]) => Blocks.cons (fun _ => Expr.ret ())
                  Blocks.nil) fun JsR =>
                Expr.jnz (Arg.var p4.snd.fst)
                  (Expr.let_ ⟨OpCode.sext 32 64, (Arg.imm 1056, ())⟩ fun s1 =>
                  Expr.let_ ⟨OpCode.mul i64, (Arg.var s1.fst, Arg.imm 4, ())⟩ fun s2 =>
                  Expr.let_ ⟨OpCode.add i64, (Arg.var c.pScratchBuf, Arg.var s2.fst, ())⟩
                    fun s3 =>
                  Expr.store (t := i32) (Arg.imm 1) (Arg.var s3.fst)
                    (Expr.let_ ⟨OpCode.sext 32 64, (Arg.imm 1057, ())⟩ fun t1 =>
                    Expr.let_ ⟨OpCode.mul i64, (Arg.var t1.fst, Arg.imm 4, ())⟩ fun t2 =>
                    Expr.let_ ⟨OpCode.add i64, (Arg.var c.pScratchBuf, Arg.var t2.fst, ())⟩
                      fun t3 =>
                    Expr.store (t := i32) (Arg.imm 1) (Arg.var t3.fst) (Expr.jump JsR.fst ())))
                  (Expr.jump JsR.fst ()))) Blocks.nil) fun Js4 =>
            Expr.jump Js4.fst (Arg.imm 0, Arg.imm false, ()))))
      Blocks.nil) fun Js3 => Expr.jump Js3.fst (Arg.imm 0, ())) m_sp := by
  change wp Γ Q X (m7P6K6WatchSolveExpr c.hdr (c.pScratchBuf + BitVec.ofNat 64 1096 * 4)
    c.pScratchBuf nc_s) m_sp
  unfold m7P6K6WatchSolveExpr
  c0_hsteps_nogrp
  refine wp_loop_group (ts := [i32])
    (fun rem3 (i, ()) m3 => ∃ kb3 : List (BitVec 32),
      K6BufOk kb3 ∧ kb3.length = kb_w0.length ∧
      i.toNat ≤ nc_s.toNat ∧ rem3 = nc_s.toNat - i.toNat ∧
      (∀ idx < kb3.length, (idx < 736 ∨ 1888 ≤ idx) → kb3[idx]? = kb_w0[idx]?) ∧
      (array64 (c.hdr + 32) (hdrTailWords c s_clr) ⋆
       array (t := i32) (c.pScratchBuf + BitVec.ofNat 64 1096 * 4) kb3 ⋆
       (array (t := i32) c.pScratchBuf scr_pre ⋆ m7_p6_fullK6Outer c s_clr ⋆ R)) m3) ?_ ?_
  · rintro L3 rem3 ⟨i, ⟨⟩⟩ m3 hL3 ⟨kb3, hok3, hkb3_l, hi_le, rfl, h3_keep, hm3⟩
    have hkb3_ge : 2912 ≤ kb3.length := hok3.base_ge
    have h3_1 : kb3[1]? = some nc_s := by
      rw [h3_keep 1 (by omega) (Or.inl (by decide))]
      have h := List.getElem?_drop (i := 1096) (j := 1) (xs := scr2)
      rw [← hkbw0_eq] at h; rw [h, hs2_1]
    c0_hsplit
    · have hi_lt : i.toNat < nc_s.toNat := hc
      have hi1 : (i + 1#32).toNat = i.toNat + 1 := m7_p6_add1_toNat (by omega)
      have hbd_2144 :
          (((@OfNat.ofNat (BitVec 32) 2144 (BitVec.instOfNat)) + i).setWidth 64).toNat <
            kb3.length := by
        rw [m7_p6_off_add 2144 (by decide) i (by omega)]; omega
      c0_hsteps_nogrp; c0_hstep; c0_hsplit
      · have hsz_ge2 : 2 ≤ (kb3[(2144 + i.toNat) % 2 ^ 64]?.getD 0#32 &&& 0xFFFF#32).toNat := by
          simpa [show (2144 : BitVec 32).toNat = 2144 from rfl,
            show (2 : BitVec 32).toNat = 2 from rfl,
            Nat.mod_eq_of_lt (by omega : 2144 + i.toNat < 2 ^ 32),
            Nat.mod_eq_of_lt (by omega : 2144 + i.toNat < 2 ^ 64),
            List.getElem?_eq_getElem (by omega : 2144 + i.toNat < kb3.length)] using hc
        have hci_lt1 : i.toNat < (kb3[1]?.getD 0#32).toNat := by
          rw [h3_1, Option.getD_some]; exact hi_lt
        have hcl3 := hok3.clause_ok hci_lt1
        have hcap_ge := hok3.length_ge
        have hoff_bd : (kb3[1888 + i.toNat]?.getD 0#32).toNat + 1 <
            (kb3[15]?.getD 0#32).toNat := by
          have hmod : (2144 + i.toNat) % 2 ^ 64 = 2144 + i.toNat := Nat.mod_eq_of_lt (by omega)
          rw [hmod] at hsz_ge2
          have hget_m : kb3[2144 + i.toNat]?.getD 0#32 = kb3[2144 + i.toNat]'(by omega) := by
            rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
          omega
        have h1888_bd :
            (((@OfNat.ofNat (BitVec 32) 1888 (BitVec.instOfNat)) + i).setWidth 64).toNat <
              kb3.length := by
          rw [m7_p6_off_add 1888 (by decide) i (by omega)]; omega
        have hoff_eq :
            (kb3[(((@OfNat.ofNat (BitVec 32) 1888 (BitVec.instOfNat)) + i).setWidth
              64).toNat]'h1888_bd).toNat = (kb3[1888 + i.toNat]?.getD 0#32).toNat := by
          rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
          exact congrArg BitVec.toNat
            (m6_getElem_congr (m7_p6_off_add 1888 (by decide) i (by omega)) _ _)
        have h2912_bd0 :
            (((@OfNat.ofNat (BitVec 32) 2912 (BitVec.instOfNat)) +
              kb3[(((@OfNat.ofNat (BitVec 32) 1888 (BitVec.instOfNat)) + i).setWidth
                64).toNat]'h1888_bd).setWidth 64).toNat < kb3.length := by
          rw [m7_p6_off_add 2912 (by decide) _ (by omega)]; omega
        have h2912_bd1 :
            ((((@OfNat.ofNat (BitVec 32) 2912 (BitVec.instOfNat)) +
              kb3[(((@OfNat.ofNat (BitVec 32) 1888 (BitVec.instOfNat)) + i).setWidth
                64).toNat]'h1888_bd) + 1#32).setWidth 64).toNat < kb3.length := by
          rw [m6_zext32_toNat, BitVec.toNat_add, BitVec.toNat_add,
            show (@OfNat.ofNat (BitVec 32) 2912 (BitVec.instOfNat)).toNat = 2912 from rfl,
            show (1#32 : BitVec 32).toNat = 1 from rfl,
            Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
          omega
        have hpk_m' : (array (t := i32) (c.pScratchBuf + BitVec.ofNat 64 1096 * 4) kb3 ⋆
            (array64 (c.hdr + 32) (hdrTailWords c s_clr) ⋆
             array (t := i32) c.pScratchBuf scr_pre ⋆ m7_p6_fullK6Outer c s_clr ⋆ R)) m3 :=
          sep_ac hm3
        unfold m7P6K6WatchBody
        c0_hsteps_nogrp
        m7_call hWatch
        refine fullK6WatchM7Spec_intro hkb3_ge hpk_m' ?_
        intro kbw mw hlenw hkeepw hmw
        have hokw := m7_p6_k6BufOk_watch_frame hok3 hlenw hkeepw
        have hkeepw' : ∀ idx < kbw.length, (idx < 736 ∨ 1888 ≤ idx) →
            kbw[idx]? = kb_w0[idx]? := fun idx hi hor => by
          rw [hkeepw idx (hlenw ▸ hi) hor]; exact h3_keep idx (hlenw ▸ hi) hor
        c0_hsteps!
        exact hL3 (nc_s.toNat - (i + 1#32).toNat) (i + 1#32, ()) mw (by omega)
          ⟨kbw, hokw, hlenw.trans hkb3_l, by omega, rfl, hkeepw', sep_ac hmw⟩
      · c0_hsteps!
        exact hL3 (nc_s.toNat - (i + 1#32).toNat) (i + 1#32, ()) m3 (by omega)
          ⟨kb3, hok3, hkb3_l, by omega, rfl, h3_keep, hm3⟩
    · have h3_2 : kb3[2]? = some nc_s := by
        rw [h3_keep 2 (by omega) (Or.inl (by decide))]
        have h := List.getElem?_drop (i := 1096) (j := 2) (xs := scr2)
        rw [← hkbw0_eq] at h; rw [h, hs2_2]
      c0_hsteps_nogrp
      m7_call hSolve
      refine fullK6SolveM7Spec_intro (hdrTailWords_length c s_clr) hok3 hm3 ?_
      intro res4 fuel4 kb4 m4 hfl4 hok4 hlen4 _ _ h4_2 _ hm4
      have hfl4' : fuel4.toNat ≤ s0.core.fuel.toNat := by
        have h17 : (hdrTailWords c s_clr)[17]?.getD 0#64 = s0.core.fuel := by
          change s_clr.core.fuel = s0.core.fuel; exact hclr_fl
        rw [h17] at hfl4; exact hfl4
      c0_hsplit
      · have hm_un := m7_p6_fullMem_unsplit_k6 hpre_l hm4
        have hscr4_l : (scr_pre ++ kb4).length = c.scratch_cap := by
          rw [List.length_append, hpre_l, hlen4, hkb3_l, hkbw0_l]; omega
        c0_hsteps!
        refine hQ fuel4 (scr_pre ++ kb4) m4 hfl4' hscr4_l (fun k hk => ?_) hm_un
        rw [List.getElem?_append_left (by omega), hpre_take]
        have htake := List.getElem?_take (i := 1096) (l := scr2) (j := k)
        rw [ite_eq_left (by omega)] at htake
        rw [htake]; exact hpre2 k (by omega)
      · have hm4_k : (array (t := i32) (c.pScratchBuf + BitVec.ofNat 64 1096 * 4) kb4 ⋆
            (array64 (c.hdr + 32) ((hdrTailWords c s_clr).set 17 fuel4) ⋆
             array (t := i32) c.pScratchBuf scr_pre ⋆ m7_p6_fullK6Outer c s_clr ⋆ R)) m4 :=
          sep_ac hm4
        m7_call hCore
        refine fullK6CoreM7Spec_intro hok4 hm4_k ?_
        intro kb5 m5 hlen5 hkeep5 hmeta5 hm5
        have hok5 := m7_p6_k6BufOk_core_frame hok4 hlen5 hkeep5 hmeta5
        have h5_nc : (kb5[2]?.getD 0#32).toNat ≤ 128 := by
          have hb4 := hok4.base_ge
          rw [hkeep5 2 (by omega) (Or.inl (by decide)), h4_2, h3_2, Option.getD_some]
          exact hnc128
        change (array (t := i32) (c.pScratchBuf + BitVec.ofNat 64 1096 * 4) kb5 ⋆ _) m5 at hm5
        exact m7_p6_k6_core_mark_wp Γ c s0 s_clr R scr_pre kb5 scr2 _ fuel4 m5 Q X rfl
          hsc_cap hsc8192 hfl4' hscr2_l hpre_l hpre_take hpre2 h5_nc
          (by rw [hpre_l, hlen5, hlen4, hkb3_l, hkbw0_l]; omega) hQ hm5
  · intro L3 hL3; c0_hsteps!
    exact hL3 nc_s.toNat (0#32, ()) _
      ⟨kb_w0, hkbw0_ok, rfl, Nat.zero_le _, rfl, fun _ _ _ => rfl, hm_sp⟩

/-! ## 2. Clause-Copy + Unit-Registration Sub-Phase (`m7_p6_copy_clause_wp`) -/

private theorem m7_p6_lt2pow30_and_bit30 {x : BitVec 32} (hx : x.toNat < 2 ^ 30) :
    (x &&& 0x40000000#32) = 0#32 := by
  apply BitVec.eq_of_toNat_eq
  apply Nat.eq_of_testBit_eq; intro k
  rw [BitVec.toNat_and,
    show (0x40000000#32 : BitVec 32).toNat = 2 ^ 30 from rfl,
    Nat.testBit_and, Nat.testBit_two_pow,
    show (0#32 : BitVec 32).toNat = 0 from rfl,
    Nat.zero_testBit]
  by_cases hk : 30 = k
  · subst hk; simp [Nat.testBit_lt_two_pow hx]
  · simp [hk]

/-- Copies `csz_m` normalized literals from `tmp` into `k[2912 + al_i ..]`, writes clause
header `(al_i, csz_m, eid)` at clause `nc_i`, records unit clause if `csz_m == 1`, and jumps
into `J`. -/
theorem m7_p6_copy_clause_wp (Γ : Env) (Q : Post []) (X : XPost)
    (J : Cont [i32, i32, i32, i32, .bool, i32])
    (c : FullCfg) (s_base : FullState) (R : Mem 64 → Prop)
    (pk pTmp : BitVec 64)
    (nc_i al_i nu_i eid te_s csz_m : BitVec 32) (ab_m : Bool)
    (scr_pre : Nat → Option (BitVec 32)) (m_init : Mem 64)
    (hpk : pk = c.pScratchBuf + BitVec.ofNat 64 1096 * 4)
    (hpTmp : pTmp = c.pTmp)
    (h8192 : 8192 ≤ c.scratch_cap)
    (hsc28 : c.scratch_cap < 2 ^ 28)
    (hscl : s_base.scratch.scratch_buf.length = c.scratch_cap)
    (htmp_len : s_base.core.tmp.length = c.max_vars)
    (hcsz_pos : 0 < csz_m.toNat)
    (hcsz_le100 : csz_m.toNat ≤ 100)
    (hcsz_mc : csz_m.toNat ≤ c.max_vars)
    (hnc128 : nc_i.toNat < 128)
    (hnu_le : nu_i.toNat ≤ nc_i.toNat)
    (halc_le : al_i.toNat + csz_m.toNat ≤ c.scratch_cap - 4008)
    (hpre0 : ∀ k < 1096, s_base.scratch.scratch_buf[k]? = scr_pre k)
    (hcls0 : ∀ cid < nc_i.toNat,
      (s_base.scratch.scratch_buf[1096 + 1888 + cid]?.getD 0#32).toNat +
        ((s_base.scratch.scratch_buf[1096 + 2144 + cid]?.getD 0#32) &&&
          0xFFFF#32).toNat ≤ al_i.toNat ∧
      ((s_base.scratch.scratch_buf[1096 + 2144 + cid]?.getD 0#32) &&&
        0x40000000#32) = 0#32)
    (hm_init : (FullMem c s_base ⋆ R) m_init)
    (hJ : ∀ (nu_j m_done : BitVec 32) (scr_j : List (BitVec 32)) (mj : Mem 64),
      scr_j.length = c.scratch_cap →
      nu_j.toNat ≤ nc_i.toNat + 1 →
      (∀ k < 1096, scr_j[k]? = scr_pre k) →
      (∀ cid < nc_i.toNat + 1,
        (scr_j[1096 + 1888 + cid]?.getD 0#32).toNat +
          ((scr_j[1096 + 2144 + cid]?.getD 0#32) &&& 0xFFFF#32).toNat ≤
          al_i.toNat + csz_m.toNat ∧
        ((scr_j[1096 + 2144 + cid]?.getD 0#32) &&& 0x40000000#32) = 0#32) →
      (FullMem c
        { s_base with scratch := { s_base.scratch with scratch_buf := scr_j } } ⋆ R) mj →
      J (nc_i + 1#32, al_i + csz_m, nu_j, te_s, ab_m, m_done, ()) mj) :
    wp Γ Q X
      (Expr.group
        (fun (Lc : Tup Cont [[i32]]) =>
          Blocks.cons (fun pmc =>
            Expr.let_ ⟨OpCode.cmp CmpOp.ult i32 Ty.bool rfl,
                (Arg.var pmc.fst, Arg.var csz_m, ())⟩ fun pc =>
            Expr.jnz (Arg.var pc.fst)
              (Expr.let_ ⟨OpCode.add i32, (Arg.imm 2912, Arg.var al_i, ())⟩ fun p2 =>
               Expr.let_ ⟨OpCode.add i32, (Arg.var p2.fst, Arg.var pmc.fst, ())⟩ fun p3 =>
               Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p3.fst, ())⟩ fun p4 =>
               Expr.let_ ⟨OpCode.mul i64, (Arg.var p4.fst, Arg.imm 4, ())⟩ fun p5 =>
               Expr.let_ ⟨OpCode.add i64, (Arg.var pk, Arg.var p5.fst, ())⟩ fun p6 =>
               Expr.let_ ⟨OpCode.zext 32 64, (Arg.var pmc.fst, ())⟩ fun p7 =>
               Expr.let_ ⟨OpCode.mul i64, (Arg.var p7.fst, Arg.imm 4, ())⟩ fun p8 =>
               Expr.let_ ⟨OpCode.add i64, (Arg.var pTmp, Arg.var p8.fst, ())⟩ fun p9 =>
               Expr.load i32 (Arg.var p9.fst) fun ld =>
               Expr.store (t := i32) (Arg.var ld) (Arg.var p6.fst)
                 (Expr.let_ ⟨OpCode.add i32, (Arg.var pmc.fst, Arg.imm 1, ())⟩ fun p1 =>
                  Expr.jump Lc.fst (Arg.var p1.fst, ())))
              (Expr.let_ ⟨OpCode.add i32, (Arg.imm 1888, Arg.var nc_i, ())⟩ fun p2 =>
               Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p2.fst, ())⟩ fun p3 =>
               Expr.let_ ⟨OpCode.mul i64, (Arg.var p3.fst, Arg.imm 4, ())⟩ fun p4 =>
               Expr.let_ ⟨OpCode.add i64, (Arg.var pk, Arg.var p4.fst, ())⟩ fun p5 =>
               Expr.store (t := i32) (Arg.var al_i) (Arg.var p5.fst)
                 (Expr.let_ ⟨OpCode.add i32, (Arg.imm 2144, Arg.var nc_i, ())⟩ fun p6 =>
                  Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p6.fst, ())⟩ fun p7 =>
                  Expr.let_ ⟨OpCode.mul i64, (Arg.var p7.fst, Arg.imm 4, ())⟩ fun p8 =>
                  Expr.let_ ⟨OpCode.add i64, (Arg.var pk, Arg.var p8.fst, ())⟩ fun p9 =>
                  Expr.store (t := i32) (Arg.var csz_m) (Arg.var p9.fst)
                    (Expr.let_ ⟨OpCode.add i32, (Arg.imm 2400, Arg.var nc_i, ())⟩ fun p10 =>
                     Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p10.fst, ())⟩ fun p11 =>
                     Expr.let_ ⟨OpCode.mul i64, (Arg.var p11.fst, Arg.imm 4, ())⟩ fun p12 =>
                     Expr.let_ ⟨OpCode.add i64, (Arg.var pk, Arg.var p12.fst, ())⟩ fun p13 =>
                     Expr.store (t := i32) (Arg.var eid) (Arg.var p13.fst)
                       (Expr.group
                         (fun (_Js : Tup Cont [[i32]]) =>
                           Blocks.cons (fun p14 =>
                             Expr.let_ ⟨OpCode.add i32, (Arg.var nc_i, Arg.imm 1, ())⟩
                               fun p15 =>
                             Expr.let_ ⟨OpCode.add i32, (Arg.var al_i, Arg.var csz_m, ())⟩
                               fun p16 =>
                             Expr.jump J
                               (Arg.var p15.fst, Arg.var p16.fst, Arg.var p14.fst,
                                Arg.var te_s, Arg.var ab_m, Arg.var pmc.fst, ()))
                             Blocks.nil)
                         fun Js =>
                         Expr.let_ ⟨OpCode.cmp CmpOp.eq i32 Ty.bool rfl,
                             (Arg.var csz_m, Arg.imm 1, ())⟩ fun p =>
                         Expr.jnz (Arg.var p.fst)
                           (Expr.let_ ⟨OpCode.add i32, (Arg.imm 2656, Arg.var nu_i, ())⟩
                              fun pu1 =>
                            Expr.let_ ⟨OpCode.zext 32 64, (Arg.var pu1.fst, ())⟩ fun pu2 =>
                            Expr.let_ ⟨OpCode.mul i64, (Arg.var pu2.fst, Arg.imm 4, ())⟩
                              fun pu3 =>
                            Expr.let_ ⟨OpCode.add i64, (Arg.var pk, Arg.var pu3.fst, ())⟩
                              fun pu4 =>
                            Expr.store (t := i32) (Arg.var nc_i) (Arg.var pu4.fst)
                              (Expr.let_ ⟨OpCode.add i32, (Arg.var nu_i, Arg.imm 1, ())⟩
                                 fun pu5 =>
                               Expr.jump Js.fst (Arg.var pu5.fst, ())))
                           (Expr.jump Js.fst (Arg.var nu_i, ())))))))
            Blocks.nil)
        fun Lc => Expr.jump Lc.fst (Arg.imm 0, ())) m_init := by
  subst hpk hpTmp
  refine wp_loop_group (ts := [i32])
    (fun rem_c (mc_i, ()) mc_m =>
      ∃ scr_c : List (BitVec 32),
      let sc_m : FullState :=
        { s_base with scratch := { s_base.scratch with scratch_buf := scr_c } }
      scr_c.length = c.scratch_cap ∧
      mc_i.toNat ≤ csz_m.toNat ∧ rem_c = csz_m.toNat - mc_i.toNat ∧
      (∀ k < 1096, scr_c[k]? = scr_pre k) ∧
      (∀ cid < nc_i.toNat,
        (scr_c[1096 + 1888 + cid]?.getD 0#32).toNat +
          ((scr_c[1096 + 2144 + cid]?.getD 0#32) &&& 0xFFFF#32).toNat ≤ al_i.toNat ∧
        ((scr_c[1096 + 2144 + cid]?.getD 0#32) &&& 0x40000000#32) = 0#32) ∧
      (FullMem c sc_m ⋆ R) mc_m) ?_ ?_
  · rintro Lc rem_c ⟨mc_i, ⟨⟩⟩ mc_m hLc ⟨scr_c, hscc_l, hmc_le, rfl, hpre_c, hcls_c, hmc_m⟩
    c0_hsplit
    · have hmc_lt : mc_i.toNat < csz_m.toNat := hc
      have hmc1 : (mc_i + 1#32).toNat = mc_i.toNat + 1 := m7_p6_add1_toNat (by omega)
      have htmp_bd : (mc_i.setWidth 64).toNat < s_base.core.tmp.length := by
        rw [htmp_len, m6_zext32_toNat]; omega
      have hsc_bd_eq : 1096 + (((2912 : BitVec 32) + al_i + mc_i).setWidth 64).toNat =
          1096 + 2912 + al_i.toNat + mc_i.toNat := by
        rw [m6_zext32_toNat, BitVec.toNat_add, BitVec.toNat_add,
          show (2912 : BitVec 32).toNat = 2912 from rfl,
          Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        omega
      have hsc_bd' : 1096 + (((2912 : BitVec 32) + al_i + mc_i).setWidth 64).toNat <
          c.scratch_cap := by rw [hsc_bd_eq]; omega
      have hmc_scr := m7_p6_scrBuf_split h8192 hscc_l hmc_m
      c0_hsteps!
      have hm := m7_p6_scrBuf_unsplit hm
      rw [hsc_bd_eq] at hm
      let scr_c' := scr_c.set (1096 + 2912 + al_i.toNat + mc_i.toNat)
        (s_base.core.tmp[(mc_i.setWidth 64).toNat]'htmp_bd)
      refine hLc (csz_m.toNat - (mc_i + 1#32).toNat) (mc_i + 1#32, ()) _ (by omega)
        ⟨scr_c', by simp [scr_c', hscc_l], by omega, rfl,
         fun k hk => by
           dsimp only [scr_c']; rw [List.getElem?_set_ne (by omega)]; exact hpre_c k hk,
         fun cid hcid => by
           dsimp only [scr_c']
           rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
           exact hcls_c cid hcid,
         m7_p6_fullMem_subst hm⟩
    · have hbd_o : 1096 + (((@OfNat.ofNat (BitVec 32) 1888 (BitVec.instOfNat)) +
          nc_i).setWidth 64).toNat < c.scratch_cap := by
        rw [m7_p6_off_add 1888 (by decide) nc_i (by omega)]; omega
      have hbd_m : 1096 + (((@OfNat.ofNat (BitVec 32) 2144 (BitVec.instOfNat)) +
          nc_i).setWidth 64).toNat < c.scratch_cap := by
        rw [m7_p6_off_add 2144 (by decide) nc_i (by omega)]; omega
      have hbd_a : 1096 + (((@OfNat.ofNat (BitVec 32) 2400 (BitVec.instOfNat)) +
          nc_i).setWidth 64).toNat < c.scratch_cap := by
        rw [m7_p6_off_add 2400 (by decide) nc_i (by omega)]; omega
      have hcsz_ff : (csz_m &&& 0xFFFF#32).toNat = csz_m.toNat := by
        rw [BitVec.toNat_and, show (0xFFFF#32 : BitVec 32).toNat = 2 ^ 16 - 1 from rfl,
          Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by omega)]
      have hcsz_lrn : (csz_m &&& 0x40000000#32) = 0#32 :=
        m7_p6_lt2pow30_and_bit30 (by omega)
      have hmc_scr := m7_p6_scrBuf_split h8192 hscc_l hmc_m
      c0_hsteps_nogrp
      let scr_m := ((scr_c.set (1096 + 1888 + nc_i.toNat) al_i).set
        (1096 + 2144 + nc_i.toNat) csz_m).set (1096 + 2400 + nc_i.toNat) eid
      have hm_m := m7_p6_scrBuf_unsplit hm
      rw [m7_p6_off_add 1888 (by decide) nc_i (by omega),
        m7_p6_off_add 2144 (by decide) nc_i (by omega),
        m7_p6_off_add 2400 (by decide) nc_i (by omega)] at hm_m
      simp only [← Nat.add_assoc] at hm_m
      have hscm_l : scr_m.length = c.scratch_cap := by simp [scr_m, hscc_l]
      refine wp_join_group (ts := [i32])
        (fun (nu_j, ()) mj =>
          ∃ scr_j : List (BitVec 32),
          scr_j.length = c.scratch_cap ∧ nu_j.toNat ≤ nc_i.toNat + 1 ∧
          (∀ k < 1096, scr_j[k]? = scr_pre k) ∧
          (∀ cid < nc_i.toNat + 1,
            (scr_j[1096 + 1888 + cid]?.getD 0#32).toNat +
              ((scr_j[1096 + 2144 + cid]?.getD 0#32) &&& 0xFFFF#32).toNat ≤
              al_i.toNat + csz_m.toNat ∧
            ((scr_j[1096 + 2144 + cid]?.getD 0#32) &&& 0x40000000#32) = 0#32) ∧
          (FullMem c { s_base with scratch := { s_base.scratch with scratch_buf := scr_j } } ⋆ R)
            mj) ?_ ?_
      · rintro _ ⟨nu_j, ⟨⟩⟩ mj ⟨scr_j, hscj_l, hnu_j, hpre_j, hcls_j, hmj⟩
        c0_hsteps!
        exact hJ nu_j mc_i scr_j mj hscj_l hnu_j hpre_j hcls_j hmj
      · intro _ hJ1
        c0_hsplit
        · have hnu1 : (nu_i + 1#32).toNat = nu_i.toNat + 1 := m7_p6_add1_toNat (by omega)
          have hbd_u : 1096 + (((@OfNat.ofNat (BitVec 32) 2656 (BitVec.instOfNat)) +
              nu_i).setWidth 64).toNat < c.scratch_cap := by
            rw [m7_p6_off_add 2656 (by decide) nu_i (by omega)]; omega
          have hm_u_scr := m7_p6_scrBuf_split h8192 hscm_l (m7_p6_fullMem_subst hm_m)
          c0_hsteps!
          have hm := m7_p6_scrBuf_unsplit hm
          rw [m7_p6_off_add 2656 (by decide) nu_i (by omega)] at hm
          simp only [← Nat.add_assoc] at hm
          let scr_u := scr_m.set (1096 + 2656 + nu_i.toNat) nc_i
          refine hJ1 _ _ ⟨scr_u, by simp [scr_u, hscm_l],
            by rw [show (nu_i + 1 : BitVec 32).toNat = nu_i.toNat + 1 from
              m7_p6_add1_toNat (by omega)]; omega,
            fun k hk => by
              dsimp only [scr_u, scr_m]
              repeat rw [List.getElem?_set_ne (by omega)]
              exact hpre_c k hk,
            fun cid hcid => ?_, m7_p6_fullMem_subst hm⟩
          dsimp only [scr_u, scr_m]
          rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hcid) with hlt | rfl
          · repeat rw [List.getElem?_set_ne (by omega)]
            have hp := hcls_c cid hlt
            exact ⟨Nat.le_trans hp.1 (by omega), hp.2⟩
          · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
              List.getElem?_set_ne (by omega), List.getElem?_set_self (by simp [hscc_l]; omega),
              List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
              List.getElem?_set_self (by simp [hscc_l]; omega),
              Option.getD_some, Option.getD_some, hcsz_ff]
            exact ⟨Nat.le_refl _, hcsz_lrn⟩
        · c0_hsteps!
          refine hJ1 _ _ ⟨scr_m, hscm_l, by omega,
            (fun k hk => by
              dsimp only [scr_m]
              repeat rw [List.getElem?_set_ne (by omega)]
              exact hpre_c k hk),
            fun cid hcid => ?_, m7_p6_fullMem_subst hm_m⟩
          dsimp only [scr_m]
          rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hcid) with hlt | rfl
          · repeat rw [List.getElem?_set_ne (by omega)]
            have hp := hcls_c cid hlt
            exact ⟨Nat.le_trans hp.1 (by omega), hp.2⟩
          · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
              List.getElem?_set_self (by simp [hscc_l]; omega), List.getElem?_set_ne (by omega),
              List.getElem?_set_self (by simp [hscc_l]; omega),
              Option.getD_some, Option.getD_some, hcsz_ff]
            exact ⟨Nat.le_refl _, hcsz_lrn⟩
  · intro Lc hLc; c0_hsteps!
    exact hLc csz_m.toNat (0#32, ()) m_init
      ⟨s_base.scratch.scratch_buf, hscl, Nat.zero_le _, rfl, hpre0, hcls0,
       m7_p6_fullMem_subst hm_init⟩

/-! ## 3. Large-Clause Literal Scan Sub-Phase (`m7_p6_scan_large_wp`) -/

/-- Scans literals `m ∈ [0..sz)` of large clause `w`, filtering `except`, breaking early on
satisfied or overflowed clauses, registering unseen variables in `exp`/`tmk`, and normalizing
unassigned literals into `tmp[0..csz)`. -/
theorem m7_p6_scan_large_wp (Γ : Env) (Q : Post []) (X : XPost)
    (Bm : Cont [i32, .bool, .bool, i32, i32])
    (c : FullCfg) (s_base : FullState) (R : Mem 64 → Prop)
    (pAr pVals pTmk pExp pTmp : BitVec 64)
    (nv_i except w sz mc : BitVec 32) (ab_i : Bool) (m_init : Mem 64)
    (hpAr : pAr = c.pArena) (hpVals : pVals = c.pVals) (hpTmk : pTmk = c.pTarjanMark)
    (hpExp : pExp = c.pWsort) (hpTmp : pTmp = c.pTmp)
    (har_len : s_base.core.arena.length = c.arena_cap)
    (har_le : s_base.core.arena_len ≤ c.arena_cap)
    (hvals_len : s_base.core.vals.length = 2 * c.max_vars)
    (hcv_le : s_base.core.cur_vars ≤ c.max_vars)
    (hmx28 : c.max_vars < 2 * 2 ^ 28)
    (hw_sz_bd : w.toNat + 3 + sz.toNat ≤ s_base.core.arena_len)
    (hw_lits_lt : ∀ j < sz.toNat,
      (s_base.core.arena[w.toNat + 3 + j]?.getD 0#32).toNat < 2 * s_base.core.cur_vars)
    (hexp_l : s_base.scratch.wsort.length = 2 * c.max_vars)
    (htmk_l : s_base.scratch.tarjan_mark.length = 2 * c.max_vars)
    (htmp_l : s_base.core.tmp.length = c.max_vars)
    (hmc_lo : 1 ≤ mc.toNat) (hmc_hi : mc.toNat ≤ 100) (hmc_cv : mc.toNat ≤ c.max_vars)
    (hnv64 : nv_i.toNat ≤ 64) (hnvcv : nv_i.toNat ≤ 2 * s_base.core.cur_vars)
    (hab_fi : ab_i = false)
    (hexp_bnd : ∀ k < nv_i.toNat, (s_base.scratch.wsort[k]?.getD 0#32).toNat < s_base.core.cur_vars)
    (htmk_inv : ∀ u < s_base.core.cur_vars, s_base.scratch.tarjan_mark[u]?.getD 0#32 ≠ 0#32 →
      1 ≤ (s_base.scratch.tarjan_mark[u]?.getD 0#32).toNat ∧
      (s_base.scratch.tarjan_mark[u]?.getD 0#32).toNat ≤ nv_i.toNat ∧
      ∃ k < nv_i.toNat, (s_base.scratch.wsort[k]?.getD 0#32).toNat = u)
    (hm_init : (FullMem c s_base ⋆ R) m_init)
    (hBm : ∀ (nv_m : BitVec 32) (ab_m sat_m : Bool) (csz_m m_idx : BitVec 32)
      (exp_m tmk_m tmp_m : List (BitVec 32)) (mm : Mem 64),
      exp_m.length = 2 * c.max_vars → tmk_m.length = 2 * c.max_vars →
      tmp_m.length = c.max_vars → nv_m.toNat ≤ 64 → nv_m.toNat ≤ 2 * s_base.core.cur_vars →
      csz_m.toNat ≤ mc.toNat →
      (∀ k < nv_m.toNat, (exp_m[k]?.getD 0#32).toNat < s_base.core.cur_vars) →
      (∀ u < s_base.core.cur_vars, tmk_m[u]?.getD 0#32 ≠ 0#32 →
        1 ≤ (tmk_m[u]?.getD 0#32).toNat ∧ (tmk_m[u]?.getD 0#32).toNat ≤ nv_m.toNat ∧
        ∃ k < nv_m.toNat, (exp_m[k]?.getD 0#32).toNat = u) →
      (FullMem c
        { s_base with
          core := { s_base.core with tmp := tmp_m }
          scratch := { s_base.scratch with wsort := exp_m, tarjan_mark := tmk_m } } ⋆ R) mm →
      Bm (nv_m, ab_m, sat_m, csz_m, m_idx, ()) mm) :
    wp Γ Q X
      (Expr.group
        (fun (Lm : Tup Cont [[i32, i32, i32]]) =>
          Blocks.cons (fun p =>
            Expr.let_ ⟨OpCode.cmp CmpOp.ult i32 Ty.bool rfl,
                (Arg.var p.snd.snd.fst, Arg.var sz, ())⟩ fun p1 =>
            Expr.jnz (Arg.var p1.fst)
              (Expr.let_ ⟨OpCode.zext 32 64, (Arg.var w, ())⟩ fun p2 =>
               Expr.let_ ⟨OpCode.add i64, (Arg.var p2.fst, Arg.imm 3, ())⟩ fun p3 =>
               Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p.snd.snd.fst, ())⟩ fun p4 =>
               Expr.let_ ⟨OpCode.add i64, (Arg.var p3.fst, Arg.var p4.fst, ())⟩ fun p5 =>
               Expr.let_ ⟨OpCode.mul i64, (Arg.var p5.fst, Arg.imm 4, ())⟩ fun p6 =>
               Expr.let_ ⟨OpCode.add i64, (Arg.var pAr, Arg.var p6.fst, ())⟩ fun p7 =>
               Expr.load i32 (Arg.var p7.fst) fun ld_l =>
               Expr.group
                 (fun (_ : Tup Cont [[i32, .bool, .bool, i32]]) =>
                   Blocks.cons (fun p8 =>
                     Expr.let_ ⟨OpCode.add i32, (Arg.var p.snd.snd.fst, Arg.imm 1, ())⟩
                       fun pm1 =>
                     Expr.jump Lm.fst
                       (Arg.var p8.fst, Arg.var p8.snd.snd.snd.fst, Arg.var pm1.fst, ()))
                     Blocks.nil)
                 fun Js2 =>
               Expr.let_ ⟨OpCode.cmp CmpOp.ne i32 Ty.bool rfl,
                   (Arg.var ld_l, Arg.var except, ())⟩ fun p8 =>
               Expr.jnz (Arg.var p8.fst)
                 (Expr.let_ ⟨OpCode.zext 32 64, (Arg.var ld_l, ())⟩ fun p9 =>
                  Expr.let_ ⟨OpCode.add i64, (Arg.var pVals, Arg.var p9.fst, ())⟩ fun p10 =>
                  Expr.load i8 (Arg.var p10.fst) fun ld1 =>
                  Expr.let_ ⟨OpCode.trunc 32 8, (Arg.imm 0, ())⟩ fun p11 =>
                  Expr.let_ ⟨OpCode.sext 8 32, (Arg.var ld1, ())⟩ fun p12 =>
                  Expr.let_ ⟨OpCode.sext 8 32, (Arg.var p11.fst, ())⟩ fun p13 =>
                  Expr.let_ ⟨OpCode.cmp CmpOp.sgt i32 Ty.bool rfl,
                      (Arg.var p12.fst, Arg.var p13.fst, ())⟩ fun p14 =>
                  Expr.jnz (Arg.var p14.fst)
                    (Expr.jump Bm
                      (Arg.var p.fst, Arg.var ab_i, Arg.imm true, Arg.var p.snd.fst,
                       Arg.var p.snd.snd.fst, ()))
                    (Expr.group
                      (fun (_ : Tup Cont [[i32, .bool, i32]]) =>
                        Blocks.cons (fun ps =>
                          Expr.jump Js2.fst
                            (Arg.var ps.fst, Arg.var ps.snd.fst, Arg.imm false,
                             Arg.var ps.snd.snd.fst, ())) Blocks.nil)
                      fun Js3 =>
                    Expr.let_ ⟨OpCode.trunc 32 8, (Arg.imm 0, ())⟩ fun p15 =>
                    Expr.let_ ⟨OpCode.sext 8 32, (Arg.var ld1, ())⟩ fun p16 =>
                    Expr.let_ ⟨OpCode.sext 8 32, (Arg.var p15.fst, ())⟩ fun p17 =>
                    Expr.let_ ⟨OpCode.cmp CmpOp.eq i32 Ty.bool rfl,
                        (Arg.var p16.fst, Arg.var p17.fst, ())⟩ fun p18 =>
                    Expr.jnz (Arg.var p18.fst)
                      (Expr.let_ ⟨OpCode.lshr i32, (Arg.var ld_l, Arg.imm 1, ())⟩ fun p19 =>
                       Expr.group
                         (fun (_ : Tup Cont [[i32, .bool]]) =>
                           Blocks.cons (fun p20 =>
                             Expr.let_ ⟨OpCode.cmp CmpOp.uge i32 Ty.bool rfl,
                                 (Arg.var p.snd.fst, Arg.var mc, ())⟩ fun p21 =>
                             Expr.jnz (Arg.var p21.fst)
                               (Expr.jump Bm
                                 (Arg.var p20.fst, Arg.imm true, Arg.imm false,
                                  Arg.var p.snd.fst, Arg.var p.snd.snd.fst, ()))
                               (Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p.snd.fst, ())⟩ fun p22 =>
                                Expr.let_ ⟨OpCode.mul i64, (Arg.var p22.fst, Arg.imm 4, ())⟩
                                  fun p23 =>
                                Expr.let_ ⟨OpCode.add i64, (Arg.var pTmp, Arg.var p23.fst, ())⟩
                                  fun p24 =>
                                Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p19.fst, ())⟩ fun p25 =>
                                Expr.let_ ⟨OpCode.mul i64, (Arg.var p25.fst, Arg.imm 4, ())⟩
                                  fun p26 =>
                                Expr.let_ ⟨OpCode.add i64, (Arg.var pTmk, Arg.var p26.fst, ())⟩
                                  fun p27 =>
                                Expr.load i32 (Arg.var p27.fst) fun ld2 =>
                                Expr.let_ ⟨OpCode.sub i32, (Arg.var ld2, Arg.imm 1, ())⟩ fun p28 =>
                                Expr.let_ ⟨OpCode.shl i32, (Arg.var p28.fst, Arg.imm 1, ())⟩
                                  fun p29 =>
                                Expr.let_ ⟨OpCode.and i32, (Arg.var ld_l, Arg.imm 1, ())⟩ fun p30 =>
                                Expr.let_ ⟨OpCode.or i32, (Arg.var p29.fst, Arg.var p30.fst, ())⟩
                                  fun p31 =>
                                Expr.store (t := i32) (Arg.var p31.fst) (Arg.var p24.fst)
                                  (Expr.let_ ⟨OpCode.add i32, (Arg.var p.snd.fst, Arg.imm 1, ())⟩
                                     fun pc1 =>
                                   Expr.jump Js3.fst
                                     (Arg.var p20.fst, Arg.var p20.snd.fst, Arg.var pc1.fst, ()))))
                             Blocks.nil)
                         fun Js4 =>
                       Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p19.fst, ())⟩ fun p20 =>
                       Expr.let_ ⟨OpCode.mul i64, (Arg.var p20.fst, Arg.imm 4, ())⟩ fun p21 =>
                       Expr.let_ ⟨OpCode.add i64, (Arg.var pTmk, Arg.var p21.fst, ())⟩ fun p22 =>
                       Expr.load i32 (Arg.var p22.fst) fun ld3 =>
                       Expr.let_ ⟨OpCode.cmp CmpOp.eq i32 Ty.bool rfl,
                           (Arg.var ld3, Arg.imm 0, ())⟩ fun p23 =>
                       Expr.jnz (Arg.var p23.fst)
                         (Expr.let_ ⟨OpCode.cmp CmpOp.uge i32 Ty.bool rfl,
                              (Arg.var p.fst, Arg.imm 64, ())⟩ fun p24 =>
                          Expr.jnz (Arg.var p24.fst)
                            (Expr.jump Bm
                              (Arg.var p.fst, Arg.imm true, Arg.imm false, Arg.var p.snd.fst,
                               Arg.var p.snd.snd.fst, ()))
                            (Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p.fst, ())⟩ fun p25 =>
                             Expr.let_ ⟨OpCode.add i64, (Arg.var c.hdr, Arg.imm 776, ())⟩ fun p26 =>
                             Expr.load i64 (Arg.var p26.fst) fun ld4 =>
                             Expr.let_ ⟨OpCode.sext 32 64, (Arg.imm 1, ())⟩ fun p27 =>
                             Expr.let_ ⟨OpCode.shl i64, (Arg.var ld4, Arg.var p27.fst, ())⟩
                               fun p28 =>
                             Expr.let_ ⟨OpCode.cmp CmpOp.uge i64 Ty.bool rfl,
                                 (Arg.var p25.fst, Arg.var p28.fst, ())⟩ fun p29 =>
                             Expr.jnz (Arg.var p29.fst)
                               (Expr.jump Bm
                                 (Arg.var p.fst, Arg.imm true, Arg.imm false, Arg.var p.snd.fst,
                                  Arg.var p.snd.snd.fst, ()))
                               (Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p.fst, ())⟩ fun p30 =>
                                Expr.let_ ⟨OpCode.mul i64, (Arg.var p30.fst, Arg.imm 4, ())⟩
                                  fun p31 =>
                                Expr.let_ ⟨OpCode.add i64, (Arg.var pExp, Arg.var p31.fst, ())⟩
                                  fun p32 =>
                                Expr.store (t := i32) (Arg.var p19.fst) (Arg.var p32.fst)
                                  (Expr.let_ ⟨OpCode.add i32, (Arg.var p.fst, Arg.imm 1, ())⟩
                                     fun pn1 =>
                                   Expr.let_ ⟨OpCode.zext 32 64, (Arg.var p19.fst, ())⟩ fun p33 =>
                                   Expr.let_ ⟨OpCode.mul i64, (Arg.var p33.fst, Arg.imm 4, ())⟩
                                     fun p34 =>
                                   Expr.let_ ⟨OpCode.add i64, (Arg.var pTmk, Arg.var p34.fst, ())⟩
                                     fun p35 =>
                                   Expr.store (t := i32) (Arg.var pn1.fst) (Arg.var p35.fst)
                                     (Expr.jump Js4.fst (Arg.var pn1.fst, Arg.var ab_i, ()))))))
                         (Expr.jump Js4.fst (Arg.var p.fst, Arg.var ab_i, ())))
                      (Expr.jump Js3.fst (Arg.var p.fst, Arg.var ab_i, Arg.var p.snd.fst, ()))))
                 (Expr.jump Js2.fst
                   (Arg.var p.fst, Arg.var ab_i, Arg.imm false, Arg.var p.snd.fst, ())))
              (Expr.jump Bm
                (Arg.var p.fst, Arg.var ab_i, Arg.imm false, Arg.var p.snd.fst,
                 Arg.var p.snd.snd.fst, ())))
            Blocks.nil)
        fun Lm => Expr.jump Lm.fst (Arg.var nv_i, Arg.imm 0, Arg.imm 0, ())) m_init := by
  subst hpAr hpVals hpTmk hpExp hpTmp
  refine wp_loop_group (ts := [i32, i32, i32])
    (fun rem_m (nv_m, csz_m, m_idx, ()) mm =>
      ∃ (exp_m tmk_m tmp_m : List (BitVec 32)),
        let sm : FullState :=
          { s_base with
            core := { s_base.core with tmp := tmp_m }
            scratch := { s_base.scratch with wsort := exp_m, tarjan_mark := tmk_m } }
        exp_m.length = 2 * c.max_vars ∧ tmk_m.length = 2 * c.max_vars ∧
        tmp_m.length = c.max_vars ∧ m_idx.toNat ≤ sz.toNat ∧
        rem_m = sz.toNat - m_idx.toNat ∧
        nv_m.toNat ≤ 64 ∧ nv_m.toNat ≤ 2 * s_base.core.cur_vars ∧ csz_m.toNat ≤ mc.toNat ∧
        (∀ k < nv_m.toNat, (exp_m[k]?.getD 0#32).toNat < s_base.core.cur_vars) ∧
        (∀ u < s_base.core.cur_vars, tmk_m[u]?.getD 0#32 ≠ 0#32 →
          1 ≤ (tmk_m[u]?.getD 0#32).toNat ∧ (tmk_m[u]?.getD 0#32).toNat ≤ nv_m.toNat ∧
          ∃ k < nv_m.toNat, (exp_m[k]?.getD 0#32).toNat = u) ∧
        (FullMem c sm ⋆ R) mm) ?_ ?_
  · rintro Lm rem_m ⟨nv_m, csz_m, m_idx, ⟨⟩⟩ mm hLm
      ⟨exp_m, tmk_m, tmp_m, hexpm, htmkm, htmpm, hm_le, rfl, hnv64m, hnvcvm, hcszm, hexpbm,
       htmkinvm, hmm⟩
    c0_hsplit
    · have hm_lt : m_idx.toNat < sz.toNat := hc
      have hm1 : (m_idx + 1#32).toNat = m_idx.toNat + 1 := m7_p6_add1_toNat (by omega)
      have har_lt29 : c.arena_cap < 2 * 2 ^ 28 := c.harena
      have hm_ar_eq : (w.setWidth 64 + 3#64 + m_idx.setWidth 64).toNat =
          w.toNat + 3 + m_idx.toNat := by
        rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_setWidth,
          show (3#64 : BitVec 64).toNat = 3 from rfl,
          Nat.mod_eq_of_lt (by have := w.isLt; omega),
          Nat.mod_eq_of_lt (by omega),
          Nat.mod_eq_of_lt (by have := m_idx.isLt; omega),
          Nat.mod_eq_of_lt (by omega)]
      have hm_ar_bd : (w.setWidth 64 + 3#64 + m_idx.setWidth 64).toNat <
          s_base.core.arena.length := by rw [har_len, hm_ar_eq]; omega
      let l := s_base.core.arena[(w.setWidth 64 + 3#64 + m_idx.setWidth 64).toNat]'hm_ar_bd
      have hl_lt : l.toNat < 2 * s_base.core.cur_vars := by
        dsimp only [l]
        have hget : (s_base.core.arena[w.toNat + 3 + m_idx.toNat]?.getD 0#32).toNat =
            (s_base.core.arena[(w.setWidth 64 + 3#64 + m_idx.setWidth 64).toNat]'
              hm_ar_bd).toNat := by
          rw [List.getElem?_eq_getElem (by rw [har_len]; omega), Option.getD_some]
          exact congrArg BitVec.toNat (m6_getElem_congr hm_ar_eq.symm _ _)
        rw [← hget]; exact hw_lits_lt m_idx.toNat hm_lt
      c0_hsteps_nogrp
      refine wp_join_group (ts := [i32, .bool, .bool, i32])
        (fun (nv_o, _ab_o, _sat_o, csz_o, ()) mo =>
          ∃ (exp_o tmk_o tmp_o : List (BitVec 32)),
            let so : FullState :=
              { s_base with
                core := { s_base.core with tmp := tmp_o }
                scratch := { s_base.scratch with wsort := exp_o, tarjan_mark := tmk_o } }
            exp_o.length = 2 * c.max_vars ∧ tmk_o.length = 2 * c.max_vars ∧
            tmp_o.length = c.max_vars ∧ nv_o.toNat ≤ 64 ∧ nv_o.toNat ≤ 2 * s_base.core.cur_vars ∧
            csz_o.toNat ≤ mc.toNat ∧
            (∀ k < nv_o.toNat, (exp_o[k]?.getD 0#32).toNat < s_base.core.cur_vars) ∧
            (∀ u < s_base.core.cur_vars, tmk_o[u]?.getD 0#32 ≠ 0#32 →
              1 ≤ (tmk_o[u]?.getD 0#32).toNat ∧ (tmk_o[u]?.getD 0#32).toNat ≤ nv_o.toNat ∧
              ∃ k < nv_o.toNat, (exp_o[k]?.getD 0#32).toNat = u) ∧
            (FullMem c so ⋆ R) mo) ?_ ?_
      · rintro _ ⟨nv_o, _ab_o, _sat_o, csz_o, ⟨⟩⟩ mo
          ⟨exp_o, tmk_o, tmp_o, hexpo, htmko, htmpo, hnv64o, hnvcvo, hcszo, hexpbo, htmkinvo, hmo⟩
        c0_hsteps!
        exact hLm (sz.toNat - (m_idx + 1#32).toNat) (nv_o, csz_o, m_idx + 1#32, ()) mo
          (by simp [hm1]; omega)
          ⟨exp_o, tmk_o, tmp_o, hexpo, htmko, htmpo, by omega, by simp [hm1], hnv64o, hnvcvo,
           hcszo, hexpbo, htmkinvo, hmo⟩
      · intro _ hJ2
        c0_hsplit
        · have hl_val_bd : (l.setWidth 64).toNat < s_base.core.vals.length := by
            rw [hvals_len, m6_zext32_toNat]; omega
          c0_hsplit
          · c0_hsteps!
            exact hBm nv_m ab_i true csz_m m_idx exp_m tmk_m tmp_m mm
              hexpm htmkm htmpm hnv64m hnvcvm hcszm hexpbm htmkinvm hmm
          · clear hc
            c0_hsteps_nogrp
            refine wp_join_group (ts := [i32, .bool, i32])
              (fun (nv_o, ab_o, csz_o, ()) mo =>
                ab_o = false ∧
                ∃ (exp_o tmk_o tmp_o : List (BitVec 32)),
                  let so : FullState :=
                    { s_base with
                      core := { s_base.core with tmp := tmp_o }
                      scratch := { s_base.scratch with wsort := exp_o, tarjan_mark := tmk_o } }
                  exp_o.length = 2 * c.max_vars ∧ tmk_o.length = 2 * c.max_vars ∧
                  tmp_o.length = c.max_vars ∧ nv_o.toNat ≤ 64 ∧
                  nv_o.toNat ≤ 2 * s_base.core.cur_vars ∧ csz_o.toNat ≤ mc.toNat ∧
                  (∀ k < nv_o.toNat, (exp_o[k]?.getD 0#32).toNat < s_base.core.cur_vars) ∧
                  (∀ u < s_base.core.cur_vars, tmk_o[u]?.getD 0#32 ≠ 0#32 →
                    1 ≤ (tmk_o[u]?.getD 0#32).toNat ∧ (tmk_o[u]?.getD 0#32).toNat ≤ nv_o.toNat ∧
                    ∃ k < nv_o.toNat, (exp_o[k]?.getD 0#32).toNat = u) ∧
                  (FullMem c so ⋆ R) mo) ?_ ?_
            · rintro _ ⟨nv_o, ab_o, csz_o, ⟨⟩⟩ mo
                ⟨rfl, exp_o, tmk_o, tmp_o, hexpo, htmko, htmpo, hnv64o, hnvcvo, hcszo, hexpbo,
                 htmkinvo, hmo⟩
              c0_hsteps!
              exact hJ2 _ _ ⟨exp_o, tmk_o, tmp_o, hexpo, htmko, htmpo, hnv64o, hnvcvo, hcszo,
                hexpbo, htmkinvo, hmo⟩
            · intro _ hJ3
              c0_hsplit
              · have hlv := m7_p6_shr1_lt hl_lt
                let lv := l >>> (1 : Nat)
                have hlv_cv : lv.toNat < s_base.core.cur_vars := hlv.2
                have hlv_tmk : (lv.setWidth 64).toNat < tmk_m.length := by
                  dsimp only [lv]; rw [htmkm, m6_zext32_toNat]; omega
                c0_hsteps_nogrp
                refine wp_join_group (ts := [i32, .bool])
                  (fun (nv_n, ab_n, ()) mn =>
                    ab_n = false ∧
                    ∃ (exp_n tmk_n : List (BitVec 32)),
                      let sn : FullState :=
                        { s_base with
                          core := { s_base.core with tmp := tmp_m }
                          scratch :=
                            { s_base.scratch with wsort := exp_n, tarjan_mark := tmk_n } }
                      exp_n.length = 2 * c.max_vars ∧ tmk_n.length = 2 * c.max_vars ∧
                      nv_n.toNat ≤ 64 ∧ nv_n.toNat ≤ 2 * s_base.core.cur_vars ∧
                      (∀ k < nv_n.toNat, (exp_n[k]?.getD 0#32).toNat < s_base.core.cur_vars) ∧
                      (∀ u < s_base.core.cur_vars, tmk_n[u]?.getD 0#32 ≠ 0#32 →
                        1 ≤ (tmk_n[u]?.getD 0#32).toNat ∧ (tmk_n[u]?.getD 0#32).toNat ≤ nv_n.toNat ∧
                        ∃ k < nv_n.toNat, (exp_n[k]?.getD 0#32).toNat = u) ∧
                      1 ≤ (tmk_n[lv.toNat]?.getD 0#32).toNat ∧
                      (tmk_n[lv.toNat]?.getD 0#32).toNat ≤ nv_n.toNat ∧
                      (FullMem c sn ⋆ R) mn) ?_ ?_
                · rintro _ ⟨nv_n, ab_n, ⟨⟩⟩ mn
                    ⟨hab_fn, exp_n, tmk_n, hexpn, htmkn, hnv64n, hnvcvn, hexpbn, htmkinvn, ht1n,
                     ht2n, hmn⟩
                  c0_hsplit
                  · c0_hsteps!
                    exact hBm nv_n true false csz_m m_idx exp_n tmk_n tmp_m mn
                      hexpn htmkn htmpm hnv64n hnvcvn hcszm hexpbn htmkinvn hmn
                  · have hcsz_lt : csz_m.toNat < mc.toNat := Nat.lt_of_not_le hc
                    have hcsz1 : (csz_m + 1#32).toNat = csz_m.toNat + 1 :=
                      m7_p6_add1_toNat (by omega)
                    have hcsz_tmp : (csz_m.setWidth 64).toNat < tmp_m.length := by
                      rw [htmpm, m6_zext32_toNat]; omega
                    have hlv_tmkn : (lv.setWidth 64).toNat < tmk_n.length := by
                      dsimp only [lv]; rw [htmkn, m6_zext32_toNat]; omega
                    c0_hsteps!
                    exact hJ3 _ _ ⟨hab_fn, exp_n, tmk_n, tmp_m.set (csz_m.setWidth 64).toNat _,
                      hexpn, htmkn, by simp [htmpm], hnv64n, hnvcvn,
                      by rw [show (csz_m + 1 : BitVec 32).toNat = csz_m.toNat + 1 from
                        m7_p6_add1_toNat (by omega)]; omega,
                      hexpbn, htmkinvn, hm⟩
                · intro _ hJ4
                  c0_hsplit
                  · have htmk0_lv : tmk_m[lv.toNat]?.getD 0#32 = 0#32 := by
                      rw [List.getElem?_eq_getElem (by rw [htmkm]; omega), Option.getD_some]
                      simpa [lv, l, m6_zext32_toNat, BitVec.toNat_ushiftRight,
                        Nat.shiftRight_eq_div_pow,
                        Nat.mod_eq_of_lt (by omega : w.toNat + 3 + m_idx.toNat < 2 ^ 64)] using hc
                    c0_hsplit
                    · c0_hsteps!
                      exact hBm nv_m true false csz_m m_idx exp_m tmk_m tmp_m mm
                        hexpm htmkm htmpm hnv64m hnvcvm hcszm hexpbm htmkinvm hmm
                    · have hnv64_lt : nv_m.toNat < 64 :=
                        Nat.lt_of_not_le (show ¬ 64 ≤ nv_m.toNat from hc)
                      clear hc
                      c0_hsplit
                      · c0_hsteps!
                        exact hBm nv_m true false csz_m m_idx exp_m tmk_m tmp_m mm
                          hexpm htmkm htmpm hnv64m hnvcvm hcszm hexpbm htmkinvm hmm
                      · have hnvcv_lt : nv_m.toNat < 2 * s_base.core.cur_vars := by
                          have hlt' : nv_m.toNat < (2 * (s_base.core.cur_vars % 2 ^ 64)) % 2 ^ 64 :=
                            by simpa [m6_zext32_toNat] using Nat.lt_of_not_le hc
                          rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hlt'
                          exact hlt'
                        have hexp_bd : (nv_m.setWidth 64).toNat < exp_m.length := by
                          rw [hexpm, m6_zext32_toNat]; omega
                        have hreg := m7_p6_tmk_reg hnv64_lt hnvcv_lt (by rw [hexpm]; omega) htmkm
                          hcv_le hlv_cv hexpbm htmkinvm
                        c0_hsteps!
                        rw [m6_zext32_toNat] at hm
                        exact hJ4 _ _ ⟨hab_fi, exp_m.set nv_m.toNat lv,
                          tmk_m.set lv.toNat (nv_m + 1#32), by simp [hexpm], by simp [htmkm],
                          hreg.2.1, hreg.2.2.1, hreg.2.2.2.1, hreg.2.2.2.2.1, hreg.2.2.2.2.2.1,
                          hreg.2.2.2.2.2.2, hm⟩
                  · have htmk_nz : tmk_m[lv.toNat]?.getD 0#32 ≠ 0#32 := by
                      rw [List.getElem?_eq_getElem (by rw [htmkm]; omega), Option.getD_some]
                      intro h0; apply hc
                      simpa [lv, l, m6_zext32_toNat, hm_ar_eq, BitVec.toNat_ushiftRight,
                        Nat.shiftRight_eq_div_pow,
                        Nat.mod_eq_of_lt (by omega : w.toNat + 3 + m_idx.toNat < 2 ^ 64)] using h0
                    have hinv_lv := htmkinvm lv.toNat hlv_cv htmk_nz
                    c0_hsteps!
                    exact hJ4 _ _ ⟨hab_fi, exp_m, tmk_m, hexpm, htmkm, hnv64m, hnvcvm,
                      hexpbm, htmkinvm, hinv_lv.1, hinv_lv.2.1, hmm⟩
              · c0_hsteps!
                exact hJ3 _ _ ⟨hab_fi, exp_m, tmk_m, tmp_m, hexpm, htmkm, htmpm, hnv64m, hnvcvm,
                  hcszm, hexpbm, htmkinvm, hmm⟩
        · c0_hsteps!
          exact hJ2 _ _ ⟨exp_m, tmk_m, tmp_m, hexpm, htmkm, htmpm, hnv64m, hnvcvm, hcszm, hexpbm,
            htmkinvm, hmm⟩
    · c0_hsteps!
      exact hBm nv_m ab_i false csz_m m_idx exp_m tmk_m tmp_m mm
        hexpm htmkm htmpm hnv64m hnvcvm hcszm hexpbm htmkinvm hmm
  · intro Lm hLm; c0_hsteps!
    exact hLm sz.toNat (nv_i, 0#32, 0#32, ()) m_init
      ⟨s_base.scratch.wsort, s_base.scratch.tarjan_mark, s_base.core.tmp, hexp_l, htmk_l, htmp_l,
       Nat.zero_le _, rfl, hnv64, hnvcv, Nat.zero_le _, hexp_bnd, htmk_inv,
       m7_p6_fullMem_subst hm_init⟩

end

end LeanQbe.T.Examples.Kissat.Proof.Definition
