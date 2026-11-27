/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Dimacs.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Spec.MemBridges
public import LeanQbe.T.Examples.Kissat.Src.Dimacs
public import LeanQbe.T.Logic.C0Step
public import LeanQbe.T.Logic.C0HeadStep

/-!
# Soundness Proofs for `Kissat.Src.Dimacs` Header, Next-Lit, and Skip (`Proof.Dimacs.Wp1`)

Proves parametric `(Γ : Env)` `Func.wp` theorems for:
- `kissat_parse_header_wp`
- `kissat_next_lit_wp`
- `full_skip_cl_wp`
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Dimacs

open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Src.Dimacs
open Kraken.Bedrock2.Test
open Std.Sat

private theorem u8_zext64_ofNat (b : UInt8) :
    (BitVec.ofNat 8 b.toNat).setWidth 64 = BitVec.ofNat 64 b.toNat := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  have hb := b.toNat_lt
  omega

private theorem u8_zext32_ofNat (b : UInt8) :
    (BitVec.ofNat 8 b.toNat).setWidth 32 = BitVec.ofNat 32 b.toNat := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  have hb := b.toNat_lt
  omega

private theorem bv32_u8_eq {a b : UInt8} :
    BitVec.ofNat 32 a.toNat = BitVec.ofNat 32 b.toNat ↔ a = b := by
  constructor
  · intro h
    have ht := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat] at ht
    rcases a with ⟨av⟩
    rcases b with ⟨bv⟩
    have ha := av.isLt
    have hb := bv.isLt
    have hav : ({ toBitVec := av } : UInt8).toNat = av.toNat := rfl
    have hbv : ({ toBitVec := bv } : UInt8).toNat = bv.toNat := rfl
    rw [hav, hbv] at ht
    congr
    apply BitVec.eq_of_toNat_eq
    omega
  · intro h; subst h; rfl

private theorem wp_load_bytes_at {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {base p : BitVec 64} {bs : List UInt8} {i : Nat} {R : Mem 64 → Prop}
    {k : Val i8 → Expr Val Cont rs}
    (hp : p = base + BitVec.ofNat 64 i) (hi : i < bs.length) (hlen : bs.length ≤ 2 ^ 64)
    (hm : (bytes base bs ⋆ R) m)
    (hk : wp Γ Q X (k (BitVec.ofNat 8 bs[i].toNat)) m) :
    wp Γ Q X (.load i8 (Arg.var p) k) m := by
  subst hp
  exact wp_load_of (load_bytes_at hi hlen hm) hk

open Std.ExtHashMap in
private theorem sep_mid_to_front {P Q R : Mem 64 → Prop} {m : Mem 64}
    (h : (P ⋆ Q ⋆ R) m) : (Q ⋆ (P ⋆ R)) m := by
  rw [sep_comm P Q, sep_assoc] at h
  exact h

open Std.ExtHashMap in
private theorem sep_front_to_mid {P Q R : Mem 64 → Prop} {m : Mem 64}
    (h : (Q ⋆ (P ⋆ R)) m) : (P ⋆ Q ⋆ R) m := by
  rw [← sep_assoc, sep_comm Q P] at h
  exact h

private theorem wp_load_d_mv {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {cnf_ptr : BitVec 64} {d mv nc cur val : Val i64} {bs : List UInt8} {R : Mem 64 → Prop}
    {k : Val i64 → Expr Val Cont rs}
    (hm : (bytes cnf_ptr bs ⋆ dimacsState d mv nc cur val ⋆ R) m)
    (hk : wp Γ Q X (k mv) m) :
    wp Γ Q X (.load i64 (Arg.var d) k) m := by
  refine wp_load_of ?_ hk
  simpa only [Arg.val_var] using load_dimacs_mv (sep_mid_to_front hm)

private theorem wp_load_d_cur {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {cnf_ptr : BitVec 64} {d mv nc cur val : Val i64} {bs : List UInt8} {R : Mem 64 → Prop}
    {k : Val i64 → Expr Val Cont rs}
    (hm : (bytes cnf_ptr bs ⋆ dimacsState d mv nc cur val ⋆ R) m)
    (hk : wp Γ Q X (k cur) m) :
    wp Γ Q X (.load i64 (Arg.var (d + 16)) k) m := by
  refine wp_load_of ?_ hk
  simpa only [Arg.val_var] using load_dimacs_cur (sep_mid_to_front hm)

private theorem wp_load_d_val {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {cnf_ptr : BitVec 64} {d mv nc cur val : Val i64} {bs : List UInt8} {R : Mem 64 → Prop}
    {k : Val i64 → Expr Val Cont rs}
    (hm : (bytes cnf_ptr bs ⋆ dimacsState d mv nc cur val ⋆ R) m)
    (hk : wp Γ Q X (k val) m) :
    wp Γ Q X (.load i64 (Arg.var (d + 24)) k) m := by
  refine wp_load_of ?_ hk
  simpa only [Arg.val_var] using load_dimacs_val (sep_mid_to_front hm)

private theorem wp_store_d_mv {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {cnf_ptr : BitVec 64} {d mv nc cur val mv' : Val i64} {bs : List UInt8} {R : Mem 64 → Prop}
    {k : Expr Val Cont rs}
    (hm : (bytes cnf_ptr bs ⋆ dimacsState d mv nc cur val ⋆ R) m)
    (hk : ∀ m', (bytes cnf_ptr bs ⋆ dimacsState d mv' nc cur val ⋆ R) m' → wp Γ Q X k m') :
    wp Γ Q X (.store (Arg.var mv') (Arg.var d) k) m := by
  refine wp_store_sep ?_ fun m' hm' => hk m' (sep_front_to_mid hm')
  simpa only [Arg.val_var] using store_dimacs_mv mv' (sep_mid_to_front hm)

private theorem wp_store_d_nc {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {cnf_ptr : BitVec 64} {d mv nc cur val nc' : Val i64} {bs : List UInt8} {R : Mem 64 → Prop}
    {k : Expr Val Cont rs}
    (hm : (bytes cnf_ptr bs ⋆ dimacsState d mv nc cur val ⋆ R) m)
    (hk : ∀ m', (bytes cnf_ptr bs ⋆ dimacsState d mv nc' cur val ⋆ R) m' → wp Γ Q X k m') :
    wp Γ Q X (.store (Arg.var nc') (Arg.var (d + 8)) k) m := by
  refine wp_store_sep ?_ fun m' hm' => hk m' (sep_front_to_mid hm')
  simpa only [Arg.val_var] using store_dimacs_nc nc' (sep_mid_to_front hm)

private theorem wp_store_d_cur {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {cnf_ptr : BitVec 64} {d mv nc cur val cur' : Val i64} {bs : List UInt8} {R : Mem 64 → Prop}
    {k : Expr Val Cont rs}
    (hm : (bytes cnf_ptr bs ⋆ dimacsState d mv nc cur val ⋆ R) m)
    (hk : ∀ m', (bytes cnf_ptr bs ⋆ dimacsState d mv nc cur' val ⋆ R) m' → wp Γ Q X k m') :
    wp Γ Q X (.store (Arg.var cur') (Arg.var (d + 16)) k) m := by
  refine wp_store_sep ?_ fun m' hm' => hk m' (sep_front_to_mid hm')
  simpa only [Arg.val_var] using store_dimacs_cur cur' (sep_mid_to_front hm)

private theorem wp_store_d_val {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {cnf_ptr : BitVec 64} {d mv nc cur val val' : Val i64} {bs : List UInt8} {R : Mem 64 → Prop}
    {k : Expr Val Cont rs}
    (hm : (bytes cnf_ptr bs ⋆ dimacsState d mv nc cur val ⋆ R) m)
    (hk : ∀ m', (bytes cnf_ptr bs ⋆ dimacsState d mv nc cur val' ⋆ R) m' → wp Γ Q X k m') :
    wp Γ Q X (.store (Arg.var val') (Arg.var (d + 24)) k) m := by
  refine wp_store_sep ?_ fun m' hm' => hk m' (sep_front_to_mid hm')
  simpa only [Arg.val_var] using store_dimacs_val val' (sep_mid_to_front hm)

private theorem bv64_add1_eq_add_succ {ptr : BitVec 64} {k : Nat} :
    ptr + BitVec.ofNat 64 k + 1 = ptr + BitVec.ofNat 64 (k + 1) := by
  rw [BitVec.add_assoc, show BitVec.ofNat 64 k + (1 : BitVec 64) =
    BitVec.ofNat 64 (k + 1) from (BitVec.ofNat_add k 1).symm]

private theorem bv64_sub1_shl1 (v : Nat) (hv1 : 1 ≤ v) (hv : v < dimacsBound) :
    (BitVec.ofNat 64 v - 1#64) <<< (1 : Nat) = BitVec.ofNat 64 (2 * (v - 1)) := by
  have hbnd : dimacsBound = 2 ^ 28 := rfl
  have hsub : (BitVec.ofNat 64 v - 1#64).toNat = v - 1 := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; simp; omega),
      BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    have : v < 2 ^ 64 := by omega
    omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, hsub, BitVec.toNat_ofNat]
  omega

private theorem nat_two_mul_or_one (n : Nat) : 2 * n ||| 1 = 2 * n + 1 := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_or]
  cases k with
  | zero => simp [Nat.testBit_zero]
  | succ k =>
    simp only [Nat.testBit_succ]
    rw [show (2 * n + 1) / 2 = n from by omega,
      show (2 * n) / 2 = n from by omega,
      show 1 / 2 = 0 from rfl, Nat.zero_testBit, Bool.or_false]

private theorem two_mul_or_one_bv (v : Nat) (hv1 : 1 ≤ v) (hv : v < dimacsBound)
    {o1 o3 : BitVec 64} {o2 : Nat} (ho1 : o1 = 1#64) (ho2 : o2 = 1) (ho3 : o3 = 1#64) :
    ((BitVec.ofNat 64 v - o1) <<< o2) ||| o3 = BitVec.ofNat 64 (mkLit (v - 1) false) := by
  subst ho1 ho2 ho3
  have hbnd : dimacsBound = 2 ^ 28 := rfl
  rw [bv64_sub1_shl1 v hv1 hv]
  simp only [mkLit, Bool.false_eq_true, ↓reduceIte]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_or, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega), show (1 % 2 ^ 64 : Nat) = 1 from rfl, nat_two_mul_or_one]
  omega

private theorem bv_encode_pos_lit (v : Nat) (hv1 : 1 ≤ v) (hv : v < dimacsBound)
    {o1 : BitVec 64} {o2 : Nat} (ho1 : o1 = 1#64) (ho2 : o2 = 1) :
    (BitVec.ofNat 64 v - o1) <<< o2 = BitVec.ofNat 64 (mkLit (v - 1) true) := by
  subst ho1 ho2
  rw [bv64_sub1_shl1 v hv1 hv]
  simp [mkLit]

private theorem parseHeader_of_tail {bs : List UInt8} {i1 : Nat}
    (hsw : bs.drop i1 = skipWsComments bs)
    (heq : i1 = bs.length ∨ (∃ hlt : i1 < bs.length, bs[i1] ≠ 112)) :
    parseHeader bs = none := by
  unfold parseHeader
  rcases heq with rfl | ⟨hlt, hne⟩
  · rw [← hsw, List.drop_length]
  · rw [← hsw, List.drop_eq_getElem_cons hlt]
    split
    · next h => exact absurd (List.cons.inj h).1 hne
    · rfl

private theorem parseHeader_of_112 {bs rest : List UInt8}
    (hsw : skipWsComments bs = 112 :: rest) :
    parseHeader bs =
      (skipWs1 rest).bind fun bs2 =>
        match bs2 with
        | 99 :: 110 :: 102 :: bs3 =>
          (skipWs1 bs3).bind fun bs4 =>
            (parseNat bs4).bind fun p1 =>
              (skipWs1 p1.2).bind fun bs6 =>
                (parseNat bs6).bind fun p2 => some (p1.1, p2.1, p2.2)
        | _ => none := by
  unfold parseHeader
  rw [hsw]
  rfl

private theorem match_cnf_eq {α} (k : List UInt8 → Option α) (bs3 : List UInt8) :
    (match (99 :: 110 :: 102 :: bs3 : List UInt8) with
    | 99 :: 110 :: 102 :: r => k r
    | _ => none) = k bs3 := rfl

private theorem match_cnf_short {α} (k : List UInt8 → Option α) {xs : List UInt8}
    (hlen : xs.length < 3) :
    (match xs with
    | 99 :: 110 :: 102 :: r => k r
    | _ => none) = none := by
  split
  · simp at hlen; omega
  · rfl

private theorem bv64_sub_cursor_lt_three_iff {ptr : BitVec 64} {n i : Nat}
    (hb : ptr.toNat + n < 2 ^ 64) (hi : i ≤ n) :
    ((2 ^ 64 - (ptr.toNat + i) % 2 ^ 64 + (ptr.toNat + n)) % 2 ^ 64 <
      BitVec.toNat (3 : BitVec 64)) ↔ n - i < 3 := by
  rw [Nat.mod_eq_of_lt (show ptr.toNat + i < 2 ^ 64 by omega),
    show 2 ^ 64 - (ptr.toNat + i) + (ptr.toNat + n) = 2 ^ 64 + (n - i) from by omega,
    Nat.add_mod_left, Nat.mod_eq_of_lt (show n - i < 2 ^ 64 by omega)]
  rfl

private theorem match_cnf_ne0 {α} (k : List UInt8 → Option α) {b : UInt8} {rest : List UInt8}
    (hb : b ≠ 99) :
    (match (b :: rest : List UInt8) with
    | 99 :: 110 :: 102 :: r => k r
    | _ => none) = none := by
  split
  · next heq => exact absurd (List.cons.inj heq).1 hb
  · rfl

private theorem match_cnf_ne1 {α} (k : List UInt8 → Option α) {b1 : UInt8} {rest : List UInt8}
    (hb : b1 ≠ 110) :
    (match (99 :: b1 :: rest : List UInt8) with
    | 99 :: 110 :: 102 :: r => k r
    | _ => none) = none := by
  split
  · next heq => exact absurd (List.cons.inj (List.cons.inj heq).2).1 hb
  · rfl

private theorem match_cnf_ne2 {α} (k : List UInt8 → Option α) {b2 : UInt8} {rest : List UInt8}
    (hb : b2 ≠ 102) :
    (match (99 :: 110 :: b2 :: rest : List UInt8) with
    | 99 :: 110 :: 102 :: r => k r
    | _ => none) = none := by
  split
  · next heq => exact absurd (List.cons.inj (List.cons.inj (List.cons.inj heq).2).2).1 hb
  · rfl

/-- Soundness proof for `kissat_parse_header`. -/
theorem kissat_parse_header_wp (Γ : Env)
    (hSkip : Γ.Has "kissat_skip_ws_comments" Spec.kissatSkipWsCommentsSpec)
    (hWs1 : Γ.Has "kissat_skip_ws1" Spec.kissatSkipWs1Spec)
    (hNat : Γ.Has "kissat_read_nat" Spec.kissatReadNatSpec) :
    ∀ a m Q X, Spec.kissatParseHeaderSpec a m Q X →
      Func.wp Γ kissat_parse_header_body a m Q X := by
  rintro ⟨cnf_ptr, cend, d, ⟨⟩⟩ m Q X ⟨mv0, nc0, cur0, val0, bs, R, rfl, hbound, hm, hQ⟩
  unfold Func.wp kissat_parse_header_body
  c0_hsteps_nogrp
  c0_call hSkip
  refine ⟨cnf_ptr, bs, 0, dimacsState d mv0 nc0 cur0 val0 ⋆ R, (BitVec.add_zero cnf_ptr).symm,
    rfl, hbound, Nat.zero_le _, by simpa only [Std.ExtHashMap.sep_assoc] using hm,
    fun i1 _ hi1_le hsw => ?_⟩
  dsimp only
  rw [cursor_ule_rev_eq hbound hi1_le]
  c0_hsteps_nogrp
  · have hi1_eq : i1 = bs.length := by c0_bound
    rw [parseHeader_of_tail (by simpa [List.drop_zero] using hsw)
      (Or.inl hi1_eq)] at hQ
    c0_hsteps; exact hQ _ _ _ _ _ hm
  · have hi1_lt : i1 < bs.length := by c0_bound
    refine wp_load_bytes_at rfl hi1_lt (by omega)
      (by simpa only [Std.ExtHashMap.sep_assoc] using hm) ?_
    c0_hsteps_nogrp
    · have hne112 : bs[i1] ≠ 112 := fun h => by
        have hb : (BitVec.ofNat 8 bs[i1].toNat).setWidth 32 = BitVec.ofNat 32 112 := by
          rw [u8_zext32_ofNat, h]; rfl
        exact (by assumption :
          (BitVec.ofNat 8 bs[i1].toNat).setWidth 32 ≠ BitVec.ofNat 32 112) hb
      rw [parseHeader_of_tail (by simpa [List.drop_zero] using hsw)
        (Or.inr ⟨hi1_lt, hne112⟩)] at hQ
      c0_hsteps; exact hQ _ _ _ _ _ hm
    · have hp112 : bs[i1] = 112 := by
        have hb : (BitVec.ofNat 8 bs[i1].toNat).setWidth 32 = BitVec.ofNat 32 112 := by assumption
        rw [u8_zext32_ofNat] at hb; exact bv32_u8_eq.mp hb
      have hsw1 : skipWsComments bs = 112 :: bs.drop (i1 + 1) := by
        rw [List.drop_zero] at hsw
        rw [← hsw, List.drop_eq_getElem_cons hi1_lt, hp112]
      try c0_hstraight
      refine wp_store_d_cur hm fun m1 hm1' => ?_
      dsimp only at hm1'
      rw [bv64_add1_eq_add_succ] at hm1'
      c0_hsteps_nogrp
      c0_call hWs1
      refine ⟨cnf_ptr, mv0, nc0, val0, bs, i1 + 1, R, rfl, hbound, hi1_lt, hm1', ?_⟩
      rw [parseHeader_of_112 hsw1] at hQ
      cases hws1 : skipWs1 (bs.drop (i1 + 1)) with
      | none =>
        rw [hws1] at hQ; simp only [Option.bind_none] at hQ
        dsimp only; c0_hsteps
        · exact absurd (by assumption : false = true) (by decide)
        · exact hQ mv0 nc0 (cnf_ptr + BitVec.ofNat 64 (i1 + 1)) val0 m1 hm1'
      | some rest1 =>
        rw [hws1] at hQ
        intro i2 m2 _ hi2_le hdrop2 hm2
        dsimp only; c0_hsteps_nogrp
        · refine wp_load_d_cur hm2 ?_
          c0_hsteps_nogrp
          · have hlt3 : bs.length - i2 < 3 :=
              (bv64_sub_cursor_lt_three_iff hbound hi2_le).mp (by assumption)
            simp only [Option.bind_some] at hQ
            rw [match_cnf_short _ (by rw [← hdrop2, List.length_drop]; exact hlt3)] at hQ
            c0_hsteps; exact hQ _ _ _ _ _ hm2
          · have hge3 : 3 ≤ bs.length - i2 := by
              have hnot : ¬ bs.length - i2 < 3 := fun h =>
                (by assumption : ¬ (2 ^ 64 - (cnf_ptr.toNat + i2) % 2 ^ 64 +
                  (cnf_ptr.toNat + bs.length)) % 2 ^ 64 < BitVec.toNat (3 : BitVec 64))
                  ((bv64_sub_cursor_lt_three_iff hbound hi2_le).mpr h)
              omega
            · have hi2_lt : i2 < bs.length := by omega
              have hi2p1_lt : i2 + 1 < bs.length := by omega
              have hi2p2_lt : i2 + 2 < bs.length := by omega
              have hm2_s : (bytes cnf_ptr bs ⋆
                  (dimacsState d mv0 nc0 (cnf_ptr + BitVec.ofNat 64 i2) val0 ⋆ R)) m2 := by
                simpa only [Std.ExtHashMap.sep_assoc] using hm2
              rw [← hdrop2] at hQ
              simp only [Option.bind_some] at hQ
              refine wp_load_bytes_at rfl hi2_lt (by omega) hm2_s ?_
              c0_hsteps_nogrp
              · have hne99 : bs[i2] ≠ 99 := fun h => by
                  have hb : (BitVec.ofNat 8 bs[i2].toNat).setWidth 32 = BitVec.ofNat 32 99 := by
                    rw [u8_zext32_ofNat, h]; rfl
                  exact (by assumption :
                    (BitVec.ofNat 8 bs[i2].toNat).setWidth 32 ≠ BitVec.ofNat 32 99) hb
                rw [List.drop_eq_getElem_cons hi2_lt, match_cnf_ne0 _ hne99] at hQ
                dsimp only at hQ
                c0_hsteps; exact hQ _ _ _ _ _ hm2
              · have hc99 : bs[i2] = 99 := by
                  have hb : (BitVec.ofNat 8 bs[i2].toNat).setWidth 32 = BitVec.ofNat 32 99 := by
                    assumption
                  rw [u8_zext32_ofNat] at hb; exact bv32_u8_eq.mp hb
                refine wp_load_bytes_at bv64_add1_eq_add_succ hi2p1_lt (by omega) hm2_s ?_
                c0_hsteps_nogrp
                · have hne110 : bs[i2 + 1] ≠ 110 := fun h => by
                    have hb : (BitVec.ofNat 8 bs[i2 + 1].toNat).setWidth 32 =
                        BitVec.ofNat 32 110 := by
                      rw [u8_zext32_ofNat, h]; rfl
                    exact (by assumption :
                      (BitVec.ofNat 8 bs[i2 + 1].toNat).setWidth 32 ≠ BitVec.ofNat 32 110) hb
                  rw [List.drop_eq_getElem_cons hi2_lt, List.drop_eq_getElem_cons hi2p1_lt,
                    hc99, match_cnf_ne1 _ hne110] at hQ
                  dsimp only at hQ
                  c0_hsteps; exact hQ _ _ _ _ _ hm2
                · have hn110 : bs[i2 + 1] = 110 := by
                    have hb : (BitVec.ofNat 8 bs[i2 + 1].toNat).setWidth 32 =
                        BitVec.ofNat 32 110 := by
                      assumption
                    rw [u8_zext32_ofNat] at hb; exact bv32_u8_eq.mp hb
                  refine wp_load_bytes_at
                    (by
                      dsimp only
                      rw [BitVec.add_assoc]
                      congr 1
                      apply BitVec.eq_of_toNat_eq
                      simp [Nat.mod_eq_of_lt (by omega : i2 + 2 < 2 ^ 64)])
                    hi2p2_lt (by omega) hm2_s ?_
                  c0_hsteps_nogrp
                  · have hne102 : bs[i2 + 2] ≠ 102 := fun h => by
                      have hb : (BitVec.ofNat 8 bs[i2 + 2].toNat).setWidth 32 =
                          BitVec.ofNat 32 102 := by
                        rw [u8_zext32_ofNat, h]; rfl
                      exact (by assumption :
                        (BitVec.ofNat 8 bs[i2 + 2].toNat).setWidth 32 ≠ BitVec.ofNat 32 102) hb
                    rw [List.drop_eq_getElem_cons hi2_lt, List.drop_eq_getElem_cons hi2p1_lt,
                      List.drop_eq_getElem_cons hi2p2_lt, hc99, hn110, match_cnf_ne2 _ hne102] at hQ
                    dsimp only at hQ
                    c0_hsteps; exact hQ _ _ _ _ _ hm2
                  · have hf102 : bs[i2 + 2] = 102 := by
                      have hb : (BitVec.ofNat 8 bs[i2 + 2].toNat).setWidth 32 =
                          BitVec.ofNat 32 102 := by
                        assumption
                      rw [u8_zext32_ofNat] at hb; exact bv32_u8_eq.mp hb
                    have hdrop_cnf : bs.drop i2 = 99 :: 110 :: 102 :: bs.drop (i2 + 3) := by
                      rw [List.drop_eq_getElem_cons hi2_lt,
                        List.drop_eq_getElem_cons hi2p1_lt,
                        List.drop_eq_getElem_cons hi2p2_lt, hc99, hn110, hf102]
                    rw [hdrop_cnf, match_cnf_eq] at hQ
                    try c0_hstraight
                    refine wp_store_d_cur hm2 fun m2' hm2' => ?_
                    dsimp only at hm2'
                    rw [show cnf_ptr + BitVec.ofNat 64 i2 + (3 : BitVec 64) =
                        cnf_ptr + BitVec.ofNat 64 (i2 + 3) from by
                      rw [BitVec.add_assoc]
                      congr 1
                      apply BitVec.eq_of_toNat_eq
                      simp [Nat.mod_eq_of_lt (by omega : i2 + 3 < 2 ^ 64)]] at hm2'
                    c0_hsteps_nogrp
                    c0_call hWs1
                    refine ⟨cnf_ptr, mv0, nc0, val0, bs, i2 + 3, R, rfl, hbound, hi2p2_lt,
                      hm2', ?_⟩
                    cases hws2 : skipWs1 (bs.drop (i2 + 3)) with
                    | none =>
                      rw [hws2] at hQ; simp only [Option.bind_none] at hQ
                      dsimp only; c0_hsteps
                      · exact absurd (by assumption : false = true) (by decide)
                      · exact hQ _ _ _ _ _ hm2'
                    | some rest2 =>
                      rw [hws2] at hQ; simp only [Option.bind_some] at hQ
                      intro i3 m3 _ hi3_le hdrop3 hm3
                      dsimp only; c0_hsteps_nogrp
                      · rw [← hdrop3] at hQ
                        c0_call hNat
                        refine ⟨cnf_ptr, mv0, nc0, val0, bs, i3, R, rfl, hbound, hi3_le,
                          hm3, ?_⟩
                        cases hpn1 : parseNat (bs.drop i3) with
                        | none =>
                          rw [hpn1] at hQ
                          simp only [Option.bind_none] at hQ
                          dsimp only; c0_hsteps
                          · exact absurd (by assumption : false = true) (by decide)
                          · exact hQ _ _ _ _ _ hm3
                        | some p1 =>
                          rcases p1 with ⟨mv, rest3⟩
                          rw [hpn1] at hQ; simp only [Option.bind_some] at hQ
                          intro i4 m4 hmv_lt _ hi4_le hdrop4 hm4
                          dsimp only; c0_hsteps_nogrp
                          · rw [← hdrop4] at hQ
                            refine wp_load_d_val hm4 ?_
                            c0_call hWs1
                            refine ⟨cnf_ptr, mv0, nc0, BitVec.ofNat 64 mv, bs,
                              i4, R, rfl, hbound, hi4_le, hm4, ?_⟩
                            cases hws3 : skipWs1 (bs.drop i4) with
                            | none =>
                              rw [hws3] at hQ
                              simp only [Option.bind_none] at hQ
                              dsimp only; c0_hsteps
                              · exact absurd (by assumption : false = true) (by decide)
                              · exact hQ _ _ _ _ _ hm4
                            | some rest4 =>
                              rw [hws3] at hQ; simp only [Option.bind_some] at hQ
                              intro i5 m5 _ hi5_le hdrop5 hm5
                              dsimp only; c0_hsteps_nogrp
                              · rw [← hdrop5] at hQ
                                c0_call hNat
                                refine ⟨cnf_ptr, mv0, nc0,
                                  BitVec.ofNat 64 mv, bs, i5, R, rfl, hbound, hi5_le, hm5, ?_⟩
                                cases hpn2 : parseNat (bs.drop i5) with
                                | none =>
                                  rw [hpn2] at hQ
                                  simp only [Option.bind_none] at hQ
                                  dsimp only; c0_hsteps
                                  · exact absurd (by assumption : false = true) (by decide)
                                  · exact hQ _ _ _ _ _ hm5
                                | some p2 =>
                                  rcases p2 with ⟨nc, rest5⟩
                                  rw [hpn2] at hQ; simp only [Option.bind_some] at hQ
                                  intro i6 m6 hnc_lt _ hi6_le hdrop6 hm6
                                  dsimp only; c0_hsteps_nogrp
                                  · refine wp_load_d_val hm6 ?_
                                    refine wp_store_d_mv hm6 fun m6' hm6' => ?_
                                    try c0_hstraight
                                    refine wp_store_d_nc hm6' fun m6'' hm6'' => ?_
                                    c0_hsteps
                                    exact hQ i6 m6'' hmv_lt hnc_lt hi6_le hdrop6 hm6''
                                  · exact absurd (by assumption : true = false) (by decide)
                              · exact absurd (by assumption : true = false) (by decide)
                          · exact absurd (by assumption : true = false) (by decide)
                      · exact absurd (by assumption : true = false) (by decide)
        · exact absurd (by assumption : true = false) (by decide)

private theorem nextLitPure_eq_of_ne45 (mv : Nat) {xs : List UInt8} {b : UInt8}
    {rest : List UInt8} (hsw : skipWsComments xs = b :: rest) (hb : b ≠ 45) :
    nextLitPure mv xs =
      match parseNat (b :: rest) with
      | none => NextLitRes.err
      | some (0, rest') => NextLitRes.endClause rest'
      | some (v, rest') => if v ≤ mv then NextLitRes.lit (mkLit (v - 1) true) rest'
        else NextLitRes.err := by
  unfold nextLitPure
  rw [hsw]
  simp [beq_eq_false_iff_ne.mpr hb]
  rfl

/-- Soundness proof for `kissat_next_lit`. -/
theorem kissat_next_lit_wp (Γ : Env)
    (hSkip : Γ.Has "kissat_skip_ws_comments" Spec.kissatSkipWsCommentsSpec)
    (hNat : Γ.Has "kissat_read_nat" Spec.kissatReadNatSpec) :
    ∀ a m Q X, Spec.kissatNextLitSpec a m Q X → Func.wp Γ kissat_next_lit_body a m Q X := by
  rintro ⟨cend, d, ⟨⟩⟩ m Q X ⟨cnf_ptr, nc, val0, mv, bs, i0, R, rfl, hbound, hmv64, hi0, hm, hQ⟩
  unfold Func.wp kissat_next_lit_body
  c0_hsteps_nogrp
  refine wp_load_d_cur hm ?_
  c0_hsteps_nogrp
  c0_call hSkip
  refine ⟨cnf_ptr, bs, i0,
    dimacsState d (BitVec.ofNat 64 mv) nc (cnf_ptr + BitVec.ofNat 64 i0) val0 ⋆ R,
    rfl, rfl, hbound, hi0, by simpa only [Std.ExtHashMap.sep_assoc] using hm,
    fun i1 hi0_1 hi1_le hsw => ?_⟩
  dsimp only
  rw [cursor_ule_rev_eq hbound hi1_le]
  c0_hsteps_nogrp
  · have hi1_eq : i1 = bs.length := by c0_bound
    have hnil : skipWsComments (bs.drop i0) = [] := by
      rw [← hsw, hi1_eq, List.drop_length]
    unfold nextLitPure at hQ
    rw [hnil] at hQ; dsimp only at hQ
    c0_hsteps; exact hQ _ _ _ hm
  · have hi1_lt : i1 < bs.length := by c0_bound
    refine wp_load_bytes_at rfl hi1_lt (by omega)
      (by simpa only [Std.ExtHashMap.sep_assoc] using hm) ?_
    c0_hsteps_nogrp
    · have h45 : bs[i1] = 45 := by
        have hb : (BitVec.ofNat 8 bs[i1].toNat).setWidth 64 = 45#64 := by assumption
        rw [u8_zext64_ofNat] at hb; exact bv64_u8_eq.mp hb
      have hsw1 : skipWsComments (bs.drop i0) = 45 :: bs.drop (i1 + 1) := by
        rw [← hsw, List.drop_eq_getElem_cons hi1_lt, h45]
      try c0_hstraight
      refine wp_store_d_cur hm fun m1 hm1' => ?_
      dsimp only at hm1'
      rw [bv64_add1_eq_add_succ] at hm1'
      c0_hsteps_nogrp
      c0_call hNat
      refine ⟨cnf_ptr, BitVec.ofNat 64 mv, nc, val0, bs, i1 + 1, R, rfl, hbound, hi1_lt, hm1', ?_⟩
      unfold nextLitPure at hQ
      rw [hsw1] at hQ
      simp only [beq_self_eq_true, ↓reduceIte] at hQ
      cases hpn : parseNat (bs.drop (i1 + 1)) with
      | none =>
        rw [hpn] at hQ; dsimp only at hQ
        dsimp only; c0_hsteps
        · exact absurd (by assumption : false = true) (by decide)
        · exact hQ _ _ m1 hm1'
      | some p =>
        rcases p with ⟨v, rest'⟩
        rw [hpn] at hQ; dsimp only at hQ
        intro i2 m2 hv_lt _ hi2_le hdrop2 hm2
        dsimp only; c0_hsteps_nogrp
        · refine wp_load_d_val hm2 ?_
          c0_hsteps_nogrp
          · have hv0 : v = 0 := by
              have hc' : v % 2 ^ 64 < BitVec.toNat (1 : BitVec 64) := by assumption
              rw [show BitVec.toNat (1 : BitVec 64) = 1 from rfl] at hc'
              unfold dimacsBound at hv_lt
              omega
            subst hv0; simp at hQ
            c0_hsteps; exact hQ _ _ _ hm2
          · have hv0 : v ≠ 0 := fun h => by
              subst h
              have hc' : ¬ 0 % 2 ^ 64 < BitVec.toNat (1 : BitVec 64) := by assumption
              rw [show BitVec.toNat (1 : BitVec 64) = 1 from rfl] at hc'
              omega
            try c0_hstraight
            refine wp_load_d_mv hm2 ?_
            c0_hsteps_nogrp
            · have hgt : ¬ (1 ≤ v ∧ v ≤ mv) := by
                have hc : BitVec.ofNat 64 mv < BitVec.ofNat 64 v := by c0_bound
                rw [BitVec.lt_def, bv64_ofNat_toNat hmv64,
                  bv64_ofNat_toNat (by unfold dimacsBound at *; omega)] at hc
                omega
              have hfalse : (decide (1 ≤ v) && decide (v ≤ mv)) = false := by simp; omega
              rw [hfalse] at hQ
              c0_hsteps; exact hQ _ _ _ hm2
            · have hle : 1 ≤ v ∧ v ≤ mv := by
                have hc : ¬ BitVec.ofNat 64 mv < BitVec.ofNat 64 v := by c0_bound
                rw [BitVec.lt_def, bv64_ofNat_toNat hmv64,
                  bv64_ofNat_toNat (by unfold dimacsBound at *; omega)] at hc
                omega
              have htrue : (decide (1 ≤ v) && decide (v ≤ mv)) = true := by simp; omega
              rw [htrue] at hQ
              try c0_hstraight
              dsimp only
              rw [two_mul_or_one_bv v hle.1 hv_lt (by rfl) (by rfl) (by rfl)]
              refine wp_store_d_val hm2 fun m2' hm2' => ?_
              c0_hsteps
              refine hQ i2 m2' ?_ ?_ (by omega) hi2_le hdrop2 hm2'
              · simp only [mkLit, Bool.false_eq_true, ↓reduceIte]; omega
              · simp only [mkLit, Bool.false_eq_true, ↓reduceIte]; unfold dimacsBound at *; omega
        · exact absurd (by assumption : true = false) (by decide)
    · have hne45 : bs[i1] ≠ 45 := fun h => by
        have hb : (BitVec.ofNat 8 bs[i1].toNat).setWidth 64 = 45#64 := by
          rw [u8_zext64_ofNat, h]; rfl
        exact (by assumption : (BitVec.ofNat 8 bs[i1].toNat).setWidth 64 ≠ 45#64) hb
      have hsw1 : skipWsComments (bs.drop i0) = bs[i1] :: bs.drop (i1 + 1) := by
        rw [← hsw, List.drop_eq_getElem_cons hi1_lt]
      try c0_hstraight
      refine wp_store_d_cur hm fun m1 hm1' => ?_
      try dsimp only at hm1'
      c0_hsteps_nogrp
      c0_call hNat
      refine ⟨cnf_ptr, BitVec.ofNat 64 mv, nc, val0, bs, i1, R, rfl, hbound, hi1_le, hm1', ?_⟩
      rw [nextLitPure_eq_of_ne45 mv hsw1 hne45, ← List.drop_eq_getElem_cons hi1_lt] at hQ
      cases hpn : parseNat (bs.drop i1) with
      | none =>
        rw [hpn] at hQ; dsimp only at hQ
        dsimp only; c0_hsteps
        · exact absurd (by assumption : false = true) (by decide)
        · exact hQ _ _ m1 hm1'
      | some p =>
        rcases p with ⟨v, rest'⟩
        rw [hpn] at hQ
        intro i2 m2 hv_lt hi1_2 hi2_le hdrop2 hm2
        dsimp only; c0_hsteps_nogrp
        · refine wp_load_d_val hm2 ?_
          c0_hsteps_nogrp
          · have hv0 : v = 0 := by unfold dimacsBound at hv_lt; c0_bound
            subst hv0
            c0_hsteps
            exact hQ i2 m2 (by omega) hi2_le hdrop2 hm2
          · have hv0 : v ≠ 0 := by unfold dimacsBound at hv_lt; c0_bound
            try c0_hstraight
            refine wp_load_d_mv hm2 ?_
            c0_hsteps_nogrp
            · have hgt : ¬ v ≤ mv := by
                have hc : BitVec.ofNat 64 mv < BitVec.ofNat 64 v := by c0_bound
                rw [BitVec.lt_def, bv64_ofNat_toNat hmv64,
                  bv64_ofNat_toNat (by unfold dimacsBound at *; omega)] at hc
                omega
              rcases Nat.exists_eq_succ_of_ne_zero hv0 with ⟨k, rfl⟩
              simp only [hgt, ↓reduceIte] at hQ
              c0_hsteps; exact hQ _ _ _ hm2
            · have hle : v ≤ mv := by
                have hc : ¬ BitVec.ofNat 64 mv < BitVec.ofNat 64 v := by c0_bound
                rw [BitVec.lt_def, bv64_ofNat_toNat hmv64,
                  bv64_ofNat_toNat (by unfold dimacsBound at *; omega)] at hc
                omega
              rcases Nat.exists_eq_succ_of_ne_zero hv0 with ⟨k, rfl⟩
              simp only [hle, ↓reduceIte] at hQ
              try c0_hstraight
              dsimp only
              rw [bv_encode_pos_lit (k + 1) (by omega) hv_lt (by rfl) (by rfl)]
              refine wp_store_d_val hm2 fun m2' hm2' => ?_
              c0_hsteps
              refine hQ i2 m2' ?_ ?_ (by omega) hi2_le hdrop2 hm2'
              · simp only [mkLit, ↓reduceIte]; omega
              · simp only [mkLit, ↓reduceIte]; unfold dimacsBound at *; omega
        · exact absurd (by assumption : true = false) (by decide)

/-- Soundness proof for `full_skip_cl`. -/
theorem full_skip_cl_wp (Γ : Env)
    (hLit : Γ.Has "kissat_next_lit" Spec.kissatNextLitSpec) :
    ∀ a m Q X, fullSkipClSpec a m Q X → Func.wp Γ full_skip_cl_body a m Q X := by
  rintro ⟨cend, d, ⟨⟩⟩ m Q X ⟨cnf_ptr, nc, val0, mv, bs, i0, R, rfl, hbound, hmv64, hi0, hm, hQ⟩
  unfold Func.wp full_skip_cl_body
  c0_hsteps
  refine wp_loop_group
    (fun (n : Nat) (_ : Tup Val []) (mL : Mem 64) =>
      ∃ (k : Nat) (val' : BitVec 64) (acc : List (Literal Nat)),
        i0 ≤ k ∧ k ≤ bs.length ∧ n = bs.length - k ∧ (∀ lit ∈ acc, 1 ≤ lit.1) ∧
        parseClauseAux (bs.length - k + 1) mv acc (bs.drop k) = parseClause mv (bs.drop i0) ∧
        (bytes cnf_ptr bs ⋆
          dimacsState d (BitVec.ofNat 64 mv) nc (cnf_ptr + BitVec.ofNat 64 k) val' ⋆ R) mL)
    (fun J n _ mL hLoop ⟨k, val', acc, hik, hkl, hn_eq, hacc_pos, hparse, hmL⟩ => ?_)
    (fun J hLoop => ?_)
  · rw [Blocks.get_here]; dsimp only
    c0_hsteps_nogrp
    · c0_call hLit
      refine ⟨cnf_ptr, nc, val', mv, bs, k, R, rfl, hbound, hmv64, hkl, hmL, ?_⟩
      have hstep := parseClauseAux_eq_nextLitPure (bs.length - k) mv acc (bs.drop k)
      cases hnl : nextLitPure mv (bs.drop k) with
      | err =>
        rw [hnl] at hstep; dsimp only at hstep
        have hpc : parseClause mv (bs.drop i0) = none := by rw [← hparse, ← hstep]
        rw [hpc] at hQ; dsimp only at hQ
        intro cur' val'' m' hm'
        c0_hsteps; exact hQ cur' val'' m' hm'
      | endClause rest' =>
        rw [hnl] at hstep; dsimp only at hstep
        have hpc :
            parseClause mv (bs.drop i0) = some (CNF.Clause.ofLiterals acc.reverse, rest') := by
          rw [← hparse, ← hstep]
        rw [hpc] at hQ; dsimp only at hQ
        have hvars : ∀ lit ∈ (CNF.Clause.ofLiterals acc.reverse).literals, 1 ≤ lit.1 := by
          intro lit hlit
          simp only [CNF.Clause.literals_ofLiterals, List.mem_reverse] at hlit
          exact hacc_pos lit hlit
        intro j m' hk_j hj_le hdrop_j hm'
        c0_hsteps
        exact hQ j m' hvars (by omega) hj_le hdrop_j hm'
      | lit l rest' =>
        rw [hnl] at hstep; dsimp only at hstep
        intro j m' _ _ hk_j hj_le hdrop_j hm'
        have hlen_j : (bs.drop j).length < bs.length - j + 1 := by simp
        have hlen_k : (bs.drop j).length < bs.length - k := by
          have : (bs.drop j).length = bs.length - j := by simp
          omega
        have hirr := parseClauseAux_fuel_irrel (f1 := bs.length - j + 1) (f2 := bs.length - k)
          (mv := mv) (acc := kissatLitToDimacsLiteral l :: acc) (bs := bs.drop j) hlen_j hlen_k
        rw [← hdrop_j] at hstep
        have hparse' : parseClauseAux (bs.length - j + 1) mv (kissatLitToDimacsLiteral l :: acc)
            (bs.drop j) = parseClause mv (bs.drop i0) := hirr.trans (hstep.symm.trans hparse)
        have hacc_pos' : ∀ lit ∈ kissatLitToDimacsLiteral l :: acc, 1 ≤ lit.1 := by
          intro lit hlit
          rcases List.mem_cons.mp hlit with rfl | hm_acc
          · simp [kissatLitToDimacsLiteral]
          · exact hacc_pos lit hm_acc
        c0_hsteps
        exact hLoop (bs.length - j) () m' (by omega)
          ⟨j, BitVec.ofNat 64 l, kissatLitToDimacsLiteral l :: acc,
            by omega, hj_le, rfl, hacc_pos', hparse', hm'⟩
    · exact absurd (by assumption : true = false) (by decide)
  · c0_hsteps
    exact hLoop (bs.length - i0) () m
      ⟨i0, val0, [], Nat.le_refl _, hi0, rfl, (fun _ h => by simp at h),
        (by unfold parseClause; rw [List.length_drop]), hm⟩

end LeanQbe.T.Examples.Kissat.Proof.Dimacs