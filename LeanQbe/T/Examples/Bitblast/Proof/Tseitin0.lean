/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Bitblast.Proof.Specs
public import LeanQbe.T.Examples.Bitblast.Src.Tseitin
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.ProofKit
import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.Logic.Bytes

/-!
# COI Marking & DIMACS Writer Helpers and Foundational WP Proofs (`Bitblast.Proof.Tseitin0`)

Proves:
- Pure `BitVec`, decimal byte-encoding (`natToBytes`), `encodeDimacsLit`, and `coiMark` lemmas
- Byte / region split & merge helpers and `@[local c0_load]` / `@[local c0_store]` wrappers
- Canonical `Γ`-parametric `Func.wp` proofs for `7` of the `8` `Tseitin` functions:
  `bv_coi_mark_wp`, `bv_dec_len_wp`, `bv_lit_bytes_wp`, `bv_write_dec_wp`,
  `bv_write_lit_wp`, `bv_write_dimacs_hdr_wp`, `bv_write_clause_end_wp`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Bitblast.Proof

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofKit
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Bitblast.Src
open LeanQbe.T.Examples.Bitblast.Src.Tseitin
open LeanQbe.T.Examples.Bitblast.Ref
open LeanQbe.T.Examples.Bitblast.Ref.Tseitin

/-! ## 1. Pure `BitVec`, `natToBytes`, `encodeDimacsLit`, and `coiMark` Lemmas -/

public section

theorem bv64_sub_eq_ofNat {a b : BitVec 64} (hle : b.toNat ≤ a.toNat) :
    a - b = BitVec.ofNat 64 (a.toNat - b.toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr hle), BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by have := a.isLt; omega)]

theorem bv64_sub_toNat {a b : BitVec 64} (hle : b.toNat ≤ a.toNat) :
    (a - b).toNat = a.toNat - b.toNat :=
  BitVec.toNat_sub_of_le (BitVec.le_def.mpr hle)

theorem bv32_lsr1_add1_toNat (x : BitVec 32) :
    ((x >>> 1) + (1 : BitVec 32)).toNat = x.toNat / 2 + 1 := by
  have hx := x.isLt
  have h1 : (x >>> 1).toNat = x.toNat / 2 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_one]
  rw [BitVec.toNat_add, h1, show (1 : BitVec 32).toNat = 1 from rfl,
    Nat.mod_eq_of_lt (by omega)]

theorem natToBytesAux_succ (fuel n : Nat) (acc : List UInt8) :
    natToBytesAux (fuel + 1) n acc =
      if n < 10 then (48 + n % 10).toUInt8 :: acc
      else natToBytesAux fuel (n / 10) ((48 + n % 10).toUInt8 :: acc) := rfl

theorem natToBytesAux_acc (fuel n : Nat) (acc : List UInt8) :
    natToBytesAux fuel n acc = natToBytesAux fuel n [] ++ acc := by
  induction fuel generalizing n acc with
  | zero => simp [natToBytesAux]
  | succ fuel ih =>
    rw [natToBytesAux_succ, natToBytesAux_succ]
    by_cases h : n < 10
    · simp [h]
    · simp only [h, ↓reduceIte]
      rw [ih, ih (acc := [(48 + n % 10).toUInt8]), List.append_assoc, List.singleton_append]

theorem natToBytesAux_fuel_irrel {f1 f2 n : Nat} (acc : List UInt8)
    (h1 : n < f1) (h2 : n < f2) :
    natToBytesAux f1 n acc = natToBytesAux f2 n acc := by
  induction f1 generalizing f2 n acc with
  | zero => omega
  | succ f1 ih =>
    cases f2 with
    | zero => omega
    | succ f2 =>
      rw [natToBytesAux_succ, natToBytesAux_succ]
      by_cases h : n < 10
      · simp [h]
      · simp only [h, ↓reduceIte]
        exact ih _ (by omega) (by omega)

theorem natToBytes_lt_10 {n : Nat} (h : n < 10) :
    natToBytes n = [(48 + n).toUInt8] := by
  unfold natToBytes
  rw [natToBytesAux_succ]
  simp [h]

theorem natToBytes_ge_10 {n : Nat} (h : 10 ≤ n) :
    natToBytes n = natToBytes (n / 10) ++ [(48 + n % 10).toUInt8] := by
  unfold natToBytes
  conv => lhs; rw [natToBytesAux_succ]
  simp only [show ¬ n < 10 by omega, ↓reduceIte]
  rw [natToBytesAux_acc, natToBytesAux_fuel_irrel (f2 := n / 10 + 1) [] (by omega) (by omega)]

theorem natToBytes_length_pos (n : Nat) : 0 < (natToBytes n).length := by
  by_cases h : n < 10
  · rw [natToBytes_lt_10 h, List.length_singleton]; decide
  · rw [natToBytes_ge_10 (by omega), List.length_append, List.length_singleton]; omega

private theorem natToBytes_length_pow10 :
    ∀ k n : Nat, n < 10 ^ (k + 1) → (natToBytes n).length ≤ k + 1
  | 0, n, hn => by
    have h10 : n < 10 := by simpa using hn
    rw [natToBytes_lt_10 h10, List.length_singleton]
    decide
  | k + 1, n, hn => by
    by_cases h10 : n < 10
    · rw [natToBytes_lt_10 h10, List.length_singleton]; omega
    · rw [natToBytes_ge_10 (by omega), List.length_append, List.length_singleton]
      have hd : n / 10 < 10 ^ (k + 1) := by
        rw [Nat.div_lt_iff_lt_mul (by decide), ← Nat.pow_succ]
        exact hn
      have ih := natToBytes_length_pow10 k (n / 10) hd
      omega

theorem natToBytes_length_le_10 {n : Nat} (hn : n < 2 ^ 32) :
    (natToBytes n).length ≤ 10 :=
  natToBytes_length_pow10 9 n (Nat.lt_trans hn (by decide))

theorem encodeDimacsLit_eq_bv (l : BitVec 32) :
    encodeDimacsLit (litToDimacs (UInt32.ofBitVec l)) =
      (if (l &&& 1#32) == 0#32 then [] else [asciiMinus]) ++
        natToBytes ((l >>> 1).toNat + 1) ++ [asciiSpace] := by
  unfold encodeDimacsLit litToDimacs
  have h1 : (UInt32.ofBitVec l >>> 1).toNat = (l >>> 1).toNat := rfl
  have h2 : ((UInt32.ofBitVec l &&& 1) == 0) = ((l &&& 1#32) == 0#32) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq]
    constructor
    · intro h
      have hn : (UInt32.ofBitVec l &&& 1).toNat = 0 := by rw [h]; rfl
      exact BitVec.eq_of_toNat_eq hn
    · intro h
      have hn : (l &&& 1#32).toNat = 0 := by rw [h]; rfl
      exact UInt32.toBitVec_inj.mp (BitVec.eq_of_toNat_eq hn)
  rw [h1, h2]

theorem encodeDimacsLit_length_bv (l : BitVec 32) :
    (encodeDimacsLit (litToDimacs (UInt32.ofBitVec l))).length =
      (l &&& 1#32).toNat + (natToBytes ((l >>> 1).toNat + 1)).length + 1 := by
  rw [encodeDimacsLit_eq_bv]
  have hand := bv_c0_toNat_and_one_32 l
  by_cases hc : ((l &&& 1#32) == 0#32) = true
  · have hz : (l &&& 1#32).toNat = 0 := by
      have := beq_iff_eq.mp hc; rw [this]; rfl
    simp [hc, hz, Nat.add_comm]
  · have hne : (l &&& 1#32) ≠ 0#32 := beq_eq_false_iff_ne.mp (Bool.eq_false_iff.mpr hc)
    have h1 : (l &&& 1#32).toNat = 1 := by
      have : (l &&& 1#32).toNat ≠ 0 := fun hz =>
        hne (BitVec.eq_of_toNat_eq (by simpa using hz))
      omega
    simp [hc, h1]; omega

theorem encodeDimacsLit_length_le_bv (l : BitVec 32) :
    (encodeDimacsLit (litToDimacs (UInt32.ofBitVec l))).length ≤ 12 := by
  rw [encodeDimacsLit_length_bv]
  have ha := bv_c0_toNat_and_one_32 l
  have hl : (l >>> 1).toNat + 1 < 2 ^ 32 := by
    have := l.isLt
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_one]
    omega
  have hn := natToBytes_length_le_10 hl
  omega

theorem marksToBool_size (ms : List UInt8) : (marksToBool ms).size = ms.length := by
  simp [marksToBool]

theorem marksToBool_getD (ms : List UInt8) {i : Nat} (hi : i < ms.length) :
    (marksToBool ms).getD i false = (ms[i] != 0) := by
  simp [marksToBool, hi]

theorem marksToBool_replicate_false (n : Nat) :
    marksToBool (List.replicate n 0) = Array.replicate n false := by
  unfold marksToBool
  apply Array.ext'
  simp [List.map_replicate]

theorem marksToBool_set_one (ms : List UInt8) (i : Nat) :
    marksToBool (if i < ms.length then ms.set i 1 else ms) =
      (marksToBool ms).setIfInBounds i true := by
  unfold marksToBool
  by_cases hi : i < ms.length
  · simp only [hi, ↓reduceIte, Array.setIfInBounds]
    have hsz : i < (ms.map (· != 0)).toArray.size := by simpa using hi
    simp only [hsz, ↓reduceDIte]
    apply Array.ext'
    simp [List.map_set]
  · simp [hi, Array.setIfInBounds]

theorem coiMarkLoop_succ {g : Aig} {k : Nat} (hk : k < g.nodes.size) (marks : Array Bool) :
    coiMarkLoop g (k + 1) marks =
      coiMarkLoop g k (if marks.getD (g.A + 1 + k) false then
        match detectIte g k hk with
        | some (c, t, f) =>
          ((marks.setIfInBounds (c >>> 1).toNat true).setIfInBounds
            (t >>> 1).toNat true).setIfInBounds (f >>> 1).toNat true
        | none =>
          let gate := g.nodes[k]
          (marks.setIfInBounds (gate.1 >>> 1).toNat true).setIfInBounds (gate.2 >>> 1).toNat true
      else marks) := by
  simp only [coiMarkLoop, hk, ↓reduceDIte]; rfl

/-- Shared PHOAS AST for inline `detectIte` used in `bv_coi_mark` and `bv_dimacs_write`. -/
@[expose] def detectIteExpr {V L} {rs : List Ty} (aigPtr : V i64) (A lhs rhs : V i32)
    (cont : Tup V [i32, i32, i32, i32] → Expr V L rs) : Expr V L rs :=
  Expr.group (sig := [[i32, i32, i32, i32]])
    (fun _ => Blocks.cons cont Blocks.nil) fun Js =>
  Expr.let_ ⟨OpCode.and i32, (Arg.var lhs, Arg.var rhs, ())⟩ fun p1 =>
  Expr.let_ ⟨OpCode.and i32, (Arg.var p1.1, Arg.imm 1#32, ())⟩ fun p2 =>
  Expr.let_ ⟨OpCode.cmp CmpOp.ne i32 Ty.bool rfl, (Arg.var p2.1, Arg.imm 0#32, ())⟩ fun p3 =>
  Expr.jnz (Arg.var p3.1)
    (Expr.let_ ⟨OpCode.lshr i32, (Arg.var lhs, Arg.imm 1#32, ())⟩ fun ln =>
    Expr.let_ ⟨OpCode.lshr i32, (Arg.var rhs, Arg.imm 1#32, ())⟩ fun rn =>
    Expr.group (sig := [[i32, i32, i32, i32]])
      (fun _ => Blocks.cons (fun p =>
        Expr.jump Js.1 (Arg.var p.1, Arg.var p.2.1, Arg.var p.2.2.1, Arg.var p.2.2.2.1, ()))
        Blocks.nil) fun Js1 =>
    Expr.let_ ⟨OpCode.cmp CmpOp.ugt i32 Ty.bool rfl, (Arg.var ln.1, Arg.var A, ())⟩ fun c1 =>
    Expr.jnz (Arg.var c1.1)
      (Expr.let_ ⟨OpCode.cmp CmpOp.ugt i32 Ty.bool rfl, (Arg.var rn.1, Arg.var A, ())⟩ fun c2 =>
      Expr.jnz (Arg.var c2.1)
        (Expr.let_ ⟨OpCode.zext 32 64, (Arg.var ln.1, ())⟩ fun ln64 =>
        Expr.let_ ⟨OpCode.mul i64, (Arg.var ln64.1, Arg.imm 8#64, ())⟩ fun loff =>
        Expr.let_ ⟨OpCode.add i64, (Arg.var aigPtr, Arg.var loff.1, ())⟩ fun lptr =>
        Expr.load i64 (Arg.var lptr.1) fun lp =>
        Expr.let_ ⟨OpCode.zext 32 64, (Arg.var rn.1, ())⟩ fun rn64 =>
        Expr.let_ ⟨OpCode.mul i64, (Arg.var rn64.1, Arg.imm 8#64, ())⟩ fun roff =>
        Expr.let_ ⟨OpCode.add i64, (Arg.var aigPtr, Arg.var roff.1, ())⟩ fun rptr =>
        Expr.load i64 (Arg.var rptr.1) fun rp =>
        Expr.let_ ⟨OpCode.and i64, (Arg.var lp, Arg.imm 4294967295#64, ())⟩ fun l0a =>
        Expr.let_ ⟨OpCode.trunc 64 32, (Arg.var l0a.1, ())⟩ fun l0 =>
        Expr.let_ ⟨OpCode.sext 32 64, (Arg.imm 32#32, ())⟩ fun s1 =>
        Expr.let_ ⟨OpCode.lshr i64, (Arg.var lp, Arg.var s1.1, ())⟩ fun l1a =>
        Expr.let_ ⟨OpCode.trunc 64 32, (Arg.var l1a.1, ())⟩ fun l1 =>
        Expr.let_ ⟨OpCode.and i64, (Arg.var rp, Arg.imm 4294967295#64, ())⟩ fun r0a =>
        Expr.let_ ⟨OpCode.trunc 64 32, (Arg.var r0a.1, ())⟩ fun r0 =>
        Expr.let_ ⟨OpCode.sext 32 64, (Arg.imm 32#32, ())⟩ fun s2 =>
        Expr.let_ ⟨OpCode.lshr i64, (Arg.var rp, Arg.var s2.1, ())⟩ fun r1a =>
        Expr.let_ ⟨OpCode.trunc 64 32, (Arg.var r1a.1, ())⟩ fun r1 =>
        Expr.group (sig := [[i32, i32, i32, i32]])
          (fun _ => Blocks.cons (fun p =>
            Expr.jump Js1.1 (Arg.var p.1, Arg.var p.2.1, Arg.var p.2.2.1, Arg.var p.2.2.2.1, ()))
            Blocks.nil) fun Js2 =>
        Expr.let_ ⟨OpCode.xor i32, (Arg.var r0.1, Arg.imm 1#32, ())⟩ fun nr0 =>
        Expr.let_ ⟨OpCode.cmp CmpOp.eq i32 Ty.bool rfl,
          (Arg.var l0.1, Arg.var nr0.1, ())⟩ fun m1 =>
        Expr.jnz (Arg.var m1.1)
          (Expr.let_ ⟨OpCode.xor i32, (Arg.var l1.1, Arg.imm 1#32, ())⟩ fun nl1 =>
          Expr.let_ ⟨OpCode.xor i32, (Arg.var r1.1, Arg.imm 1#32, ())⟩ fun nr1 =>
          Expr.jump Js2.1 (Arg.imm 1#32, Arg.var l0.1, Arg.var nl1.1, Arg.var nr1.1, ()))
          (Expr.group (sig := [[i32, i32, i32, i32]])
            (fun _ => Blocks.cons (fun p =>
              Expr.jump Js2.1
                (Arg.var p.1, Arg.var p.2.1, Arg.var p.2.2.1, Arg.var p.2.2.2.1, ()))
              Blocks.nil) fun Js3 =>
          Expr.let_ ⟨OpCode.xor i32, (Arg.var r1.1, Arg.imm 1#32, ())⟩ fun nr1 =>
          Expr.let_ ⟨OpCode.cmp CmpOp.eq i32 Ty.bool rfl,
            (Arg.var l0.1, Arg.var nr1.1, ())⟩ fun m2 =>
          Expr.jnz (Arg.var m2.1)
            (Expr.let_ ⟨OpCode.xor i32, (Arg.var l1.1, Arg.imm 1#32, ())⟩ fun nl1 =>
            Expr.let_ ⟨OpCode.xor i32, (Arg.var r0.1, Arg.imm 1#32, ())⟩ fun nr0 =>
            Expr.jump Js3.1 (Arg.imm 1#32, Arg.var l0.1, Arg.var nl1.1, Arg.var nr0.1, ()))
            (Expr.group (sig := [[i32, i32, i32, i32]])
              (fun _ => Blocks.cons (fun p =>
                Expr.jump Js3.1
                  (Arg.var p.1, Arg.var p.2.1, Arg.var p.2.2.1, Arg.var p.2.2.2.1, ()))
                Blocks.nil) fun Js4 =>
            Expr.let_ ⟨OpCode.xor i32, (Arg.var r0.1, Arg.imm 1#32, ())⟩ fun nr0 =>
            Expr.let_ ⟨OpCode.cmp CmpOp.eq i32 Ty.bool rfl,
              (Arg.var l1.1, Arg.var nr0.1, ())⟩ fun m3 =>
            Expr.jnz (Arg.var m3.1)
              (Expr.let_ ⟨OpCode.xor i32, (Arg.var l0.1, Arg.imm 1#32, ())⟩ fun nl0 =>
              Expr.let_ ⟨OpCode.xor i32, (Arg.var r1.1, Arg.imm 1#32, ())⟩ fun nr1 =>
              Expr.jump Js4.1 (Arg.imm 1#32, Arg.var l1.1, Arg.var nl0.1, Arg.var nr1.1, ()))
              (Expr.group (sig := [[i32, i32, i32, i32]])
                (fun _ => Blocks.cons (fun p =>
                  Expr.jump Js4.1
                    (Arg.var p.1, Arg.var p.2.1, Arg.var p.2.2.1, Arg.var p.2.2.2.1, ()))
                  Blocks.nil) fun Js5 =>
              Expr.let_ ⟨OpCode.xor i32, (Arg.var r1.1, Arg.imm 1#32, ())⟩ fun nr1 =>
              Expr.let_ ⟨OpCode.cmp CmpOp.eq i32 Ty.bool rfl,
                (Arg.var l1.1, Arg.var nr1.1, ())⟩ fun m4 =>
              Expr.jnz (Arg.var m4.1)
                (Expr.let_ ⟨OpCode.xor i32, (Arg.var l0.1, Arg.imm 1#32, ())⟩ fun nl0 =>
                Expr.let_ ⟨OpCode.xor i32, (Arg.var r0.1, Arg.imm 1#32, ())⟩ fun nr0 =>
                Expr.jump Js5.1 (Arg.imm 1#32, Arg.var l1.1, Arg.var nl0.1, Arg.var nr0.1, ()))
                (Expr.jump Js5.1
                  (Arg.imm 0#32, Arg.imm 0#32, Arg.imm 0#32, Arg.imm 0#32, ()))))))
        (Expr.jump Js1.1 (Arg.imm 0#32, Arg.imm 0#32, Arg.imm 0#32, Arg.imm 0#32, ())))
      (Expr.jump Js1.1 (Arg.imm 0#32, Arg.imm 0#32, Arg.imm 0#32, Arg.imm 0#32, ())))
    (Expr.jump Js.1 (Arg.imm 0#32, Arg.imm 0#32, Arg.imm 0#32, Arg.imm 0#32, ()))

end

/-! ## 2. Byte / Region Memory Helpers and `@[local c0_load]` / `@[local c0_store]` -/

public section

theorem region_to_bytes_sep {a : BitVec 64} {n : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (region a n ⋆ R) m) :
    ∃ bs : List UInt8, bs.length = n ∧ (bytes a bs ⋆ R) m := by
  obtain ⟨bs, hlen, hbm⟩ := region_sep_elim hm
  exact ⟨bs, hlen, hbm⟩

theorem store_bytes_at {base : BitVec 64} {bs : List UInt8} {i : Nat} (v : BitVec 8)
    {R : Mem 64 → Prop} {m : Mem 64} (hi : i < bs.length) (hlen : bs.length ≤ 2 ^ 64)
    (hm : (bytes base bs ⋆ R) m) :
    storeOk m i8 (base + BitVec.ofNat 64 i) ∧
      (bytes base (bs.set i (UInt8.ofBitVec v)) ⋆ R)
        (storeMem m i8 (base + BitVec.ofNat 64 i) v) := by
  have hsplit : bs = bs.take i ++ ([bs[i]] ++ bs.drop (i + 1)) := by
    rw [List.singleton_append, ← List.drop_eq_getElem_cons hi, List.take_append_drop]
  have hlen_t : (bs.take i).length = i := List.length_take_of_le (Nat.le_of_lt hi)
  have hlen_d : (bs.drop (i + 1)).length = bs.length - (i + 1) := List.length_drop
  have heq : bytes base bs =
      (bytes base (bs.take i) ⋆
        (bytes (base + BitVec.ofNat 64 i) [bs[i]] ⋆
          bytes (base + BitVec.ofNat 64 i + BitVec.ofNat 64 1) (bs.drop (i + 1)))) := by
    unfold bytes
    conv => lhs; rw [hsplit]
    rw [eq_append_At base (bs.take i) ([bs[i]] ++ bs.drop (i + 1)) (by simp [hlen_t]; omega),
      hlen_t, eq_append_At (base + BitVec.ofNat 64 i) [bs[i]] (bs.drop (i + 1)) (by simp; omega),
      List.length_singleton]
  rw [heq] at hm
  have hm' : (Eq ((Int.toBytes (Ty.bits 8).bytes (bs[i].toNat : Int)).At
        (base + BitVec.ofNat 64 i)) ⋆
      ((bytes base (bs.take i) ⋆
        bytes (base + BitVec.ofNat 64 i + BitVec.ofNat 64 1) (bs.drop (i + 1))) ⋆ R)) m := by
    rw [show (Ty.bits 8).bytes = 1 from rfl, toBytes_u8 bs[i]]
    exact (sep_ac hm : (bytes (base + BitVec.ofNat 64 i) [bs[i]] ⋆
      ((bytes base (bs.take i) ⋆
        bytes (base + BitVec.ofNat 64 i + BitVec.ofNat 64 1) (bs.drop (i + 1))) ⋆ R)) m)
  obtain ⟨hok, hst⟩ := store_toBytes_bits (n := 8) v rfl (by decide) hm'
  refine ⟨hok, ?_⟩
  have hv_toNat : (UInt8.ofBitVec v).toNat = v.toNat := rfl
  have htb2 : Int.toBytes (Ty.bits 8).bytes (v.toNat : Int) = [UInt8.ofBitVec v] := by
    rw [← hv_toNat]; exact toBytes_u8 (UInt8.ofBitVec v)
  rw [htb2] at hst
  have hset : bs.set i (UInt8.ofBitVec v) =
      bs.take i ++ ([UInt8.ofBitVec v] ++ bs.drop (i + 1)) := by
    rw [List.set_eq_take_append_cons_drop]; simp [hi]
  have heq2 : bytes base (bs.set i (UInt8.ofBitVec v)) =
      (bytes base (bs.take i) ⋆
        (bytes (base + BitVec.ofNat 64 i) [UInt8.ofBitVec v] ⋆
          bytes (base + BitVec.ofNat 64 i + BitVec.ofNat 64 1) (bs.drop (i + 1)))) := by
    unfold bytes
    conv => lhs; rw [hset]
    rw [eq_append_At base (bs.take i) ([UInt8.ofBitVec v] ++ bs.drop (i + 1))
        (by simp [hlen_t]; omega),
      hlen_t, eq_append_At (base + BitVec.ofNat 64 i) [UInt8.ofBitVec v] (bs.drop (i + 1))
        (by simp; omega),
      List.length_singleton]
  rw [heq2]
  have hst' : (bytes (base + BitVec.ofNat 64 i) [UInt8.ofBitVec v] ⋆
      ((bytes base (bs.take i) ⋆
        bytes (base + BitVec.ofNat 64 i + BitVec.ofNat 64 1) (bs.drop (i + 1))) ⋆ R))
      (storeMem m i8 (base + BitVec.ofNat 64 i) v) := hst
  exact (sep_ac hst' : ((bytes base (bs.take i) ⋆
    (bytes (base + BitVec.ofNat 64 i) [UInt8.ofBitVec v] ⋆
      bytes (base + BitVec.ofNat 64 i + BitVec.ofNat 64 1) (bs.drop (i + 1)))) ⋆ R) _)

theorem store_region_one {a : BitVec 64} (v : BitVec 8) {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (region a 1 ⋆ R) m) :
    storeOk m i8 a ∧ (bytes a [UInt8.ofBitVec v] ⋆ R) (storeMem m i8 a v) := by
  obtain ⟨bs, hbs, hbm⟩ := region_to_bytes_sep hm
  have h0 : 0 < bs.length := by omega
  have hst := store_bytes_at (i := 0) v h0 (by omega) hbm
  simp only [BitVec.add_zero] at hst
  have heq : bs.set 0 (UInt8.ofBitVec v) = [UInt8.ofBitVec v] := by
    rcases bs with _ | ⟨b0, _ | _⟩ <;> simp at hbs
    rfl
  rw [heq] at hst
  exact hst

theorem store_region_tail_byte {p : BitVec 64} {k : Nat} (hk : 1 ≤ k) (hk64 : k ≤ 2 ^ 64)
    (v : BitVec 8) {suffix : List UInt8} {R : Mem 64 → Prop} {m : Mem 64}
    (hsuf : 1 + suffix.length ≤ 2 ^ 64)
    (hm : (region p k ⋆ (bytes (p + BitVec.ofNat 64 k) suffix ⋆ R)) m) :
    storeOk m i8 (p + BitVec.ofNat 64 (k - 1)) ∧
      (region p (k - 1) ⋆
        (bytes (p + BitVec.ofNat 64 (k - 1)) (UInt8.ofBitVec v :: suffix) ⋆ R))
        (storeMem m i8 (p + BitVec.ofNat 64 (k - 1)) v) := by
  have hsp : region p k = (region p (k - 1) ⋆ region (p + BitVec.ofNat 64 (k - 1)) 1) := by
    rw [region_merge_eq (a := p) (n1 := k - 1) (n2 := 1) (n := k) (by omega) hk64]
  rw [hsp] at hm
  have hm' : (region (p + BitVec.ofNat 64 (k - 1)) 1 ⋆
      (region p (k - 1) ⋆ (bytes (p + BitVec.ofNat 64 k) suffix ⋆ R))) m := sep_ac hm
  obtain ⟨hok, hst⟩ := store_region_one v hm'
  refine ⟨hok, ?_⟩
  have hptr : p + BitVec.ofNat 64 (k - 1) + BitVec.ofNat 64 1 = p + BitVec.ofNat 64 k := by
    rw [ptr_add_ofNat]; congr 2; omega
  have hmrg : (bytes (p + BitVec.ofNat 64 (k - 1)) [UInt8.ofBitVec v] ⋆
      bytes (p + BitVec.ofNat 64 k) suffix) =
      bytes (p + BitVec.ofNat 64 (k - 1)) (UInt8.ofBitVec v :: suffix) := by
    unfold bytes
    have heq := eq_append_At (p + BitVec.ofNat 64 (k - 1)) [UInt8.ofBitVec v] suffix
      (by simp; omega)
    rw [List.length_singleton, hptr] at heq
    exact heq.symm
  have hst' : (region p (k - 1) ⋆
      ((bytes (p + BitVec.ofNat 64 (k - 1)) [UInt8.ofBitVec v] ⋆
        bytes (p + BitVec.ofNat 64 k) suffix) ⋆ R))
      (storeMem m i8 (p + BitVec.ofNat 64 (k - 1)) v) := sep_ac hst
  rw [hmrg] at hst'
  exact hst'

theorem region_split_prefix {a : BitVec 64} {n1 n2 : Nat} (hfit : n1 + n2 ≤ 2 ^ 64)
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (region a (n1 + n2) ⋆ R) m) :
    (region a n1 ⋆ (region (a + BitVec.ofNat 64 n1) n2 ⋆ R)) m := by
  rw [region_split hfit] at hm
  exact sep_ac hm

theorem bytes_append_merge {a : BitVec 64} {b1 b2 : List UInt8}
    (hfit : b1.length + b2.length ≤ 2 ^ 64) :
    (bytes a b1 ⋆ bytes (a + BitVec.ofNat 64 b1.length) b2) = bytes a (b1 ++ b2) := by
  unfold bytes
  exact (eq_append_At a b1 b2 hfit).symm

end

@[local c0_load] private theorem c0_load_bytes_u32 {base : BitVec 64} {i : BitVec 32}
    {bs : List UInt8} {R : Mem 64 → Prop} {m : Mem 64}
    (hi : i.toNat < bs.length) (hlen : bs.length ≤ 2 ^ 64) (hm : (bytes base bs ⋆ R) m) :
    loadVal m i8 (base + i.setWidth 64) = some (BitVec.ofNat 8 (bs[i.toNat]'hi).toNat) := by
  have heq : base + i.setWidth 64 = base + BitVec.ofNat 64 i.toNat := by
    congr 1; apply BitVec.eq_of_toNat_eq; simp
  rw [heq]; exact load_bytes_at hi hlen hm

@[local c0_store] private theorem c0_store_bytes_base {base : BitVec 64} {bs : List UInt8}
    (v : BitVec 8) {R : Mem 64 → Prop} {m : Mem 64}
    (hi : 0 < bs.length) (hlen : bs.length ≤ 2 ^ 64) (hm : (bytes base bs ⋆ R) m) :
    storeOk m i8 base ∧
      (bytes base (bs.set 0 (UInt8.ofBitVec v)) ⋆ R) (storeMem m i8 base v) := by
  simpa using store_bytes_at (i := 0) v hi hlen hm

@[local c0_store] private theorem c0_store_bytes_off {base off : BitVec 64} {bs : List UInt8}
    (v : BitVec 8) {R : Mem 64 → Prop} {m : Mem 64}
    (hi : off.toNat < bs.length) (hlen : bs.length ≤ 2 ^ 64) (hm : (bytes base bs ⋆ R) m) :
    storeOk m i8 (base + off) ∧
      (bytes base (bs.set off.toNat (UInt8.ofBitVec v)) ⋆ R) (storeMem m i8 (base + off) v) := by
  have heq : base + off = base + BitVec.ofNat 64 off.toNat := by
    congr 1; apply BitVec.eq_of_toNat_eq; simp
  rw [heq]; exact store_bytes_at (i := off.toNat) v hi hlen hm

@[local c0_store] private theorem c0_store_bytes_u32 {base : BitVec 64} {i : BitVec 32}
    {bs : List UInt8} (v : BitVec 8) {R : Mem 64 → Prop} {m : Mem 64}
    (hi : i.toNat < bs.length) (hlen : bs.length ≤ 2 ^ 64) (hm : (bytes base bs ⋆ R) m) :
    storeOk m i8 (base + i.setWidth 64) ∧
      (bytes base (bs.set i.toNat (UInt8.ofBitVec v)) ⋆ R)
        (storeMem m i8 (base + i.setWidth 64) v) := by
  have heq : base + i.setWidth 64 = base + BitVec.ofNat 64 i.toNat := by
    congr 1; apply BitVec.eq_of_toNat_eq; simp
  rw [heq]; exact store_bytes_at (i := i.toNat) v hi hlen hm

@[local c0_store] private theorem c0_store_region_one {a : BitVec 64} (v : BitVec 8)
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (region a 1 ⋆ R) m) :
    storeOk m i8 a ∧ (bytes a [UInt8.ofBitVec v] ⋆ R) (storeMem m i8 a v) :=
  store_region_one v hm

@[local c0_load] private theorem c0_load_array64_u32_mul8 {a : BitVec 64} {i : BitVec 32}
    {xs : List (BitVec 64)} {R : Mem 64 → Prop} {m : Mem 64}
    (h : (array64 a xs ⋆ R) m) (hi : i.toNat < xs.length) :
    loadVal m i64 (a + i.setWidth 64 * 8#64) = some (xs[i.toNat]'hi) := by
  have heq : i.setWidth 64 * 8#64 = BitVec.ofNat 64 (8 * i.toNat) := BitVec.eq_of_toNat_eq <| by
    have := i.isLt
    simp [BitVec.toNat_mul, Nat.mod_eq_of_lt (by omega : 8 * i.toNat < 2 ^ 64), Nat.mul_comm]
  rw [heq]; exact loadVal_array64 hi h

/-! ## 3. Foundational WP Theorems (`wp_detectIteExpr`, `bv_coi_mark` .. `bv_write_clause_end`) -/

public section

/-- Reusable WP proof for `detectIteExpr` matching `Ref.Tseitin.detectIte`. -/
theorem wp_detectIteExpr {rs : List Ty} (Γ : Env) (Q : Post rs) (X : XPost)
    (aigPtr : Val i64) (A : Val i32) (g : Aig) (aigUsed : List (BitVec 64))
    (R : Mem 64 → Prop) (m : Mem 64) (k : Nat) (hk : k < g.nodes.size)
    (hA : A.toNat = g.A) (hwf : g.Wf) (haig_w : AigWordsMatch g aigUsed)
    (haig_l : aigUsed.length = g.A + 1 + g.nodes.size)
    (hm : (array64 aigPtr aigUsed ⋆ R) m)
    (cont : Tup Val [i32, i32, i32, i32] → Expr Val Cont rs)
    (hSome : ∀ c t f, detectIte g k hk = some (c, t, f) →
      wp Γ Q X (cont (1#32, c.toBitVec, t.toBitVec, f.toBitVec, ())) m)
    (hNone : detectIte g k hk = none →
      wp Γ Q X (cont (0#32, 0#32, 0#32, 0#32, ())) m) :
    wp Γ Q X (detectIteExpr aigPtr A (g.nodes[k]'hk).1.toBitVec (g.nodes[k]'hk).2.toBitVec cont)
      m := by
  let P : Val i32 × Val i32 × Val i32 × Val i32 → Mem 64 → Prop :=
    fun st ml => ml = m ∧
      match detectIte g k hk with
      | some (c, t, f) => st = (1#32, c.toBitVec, t.toBitVec, f.toBitVec)
      | none => st = (0#32, 0#32, 0#32, 0#32)
  have hP_cont : ∀ (st : Val i32 × Val i32 × Val i32 × Val i32) (ml : Mem 64),
      P st ml → wp Γ Q X (cont (st.1, st.2.1, st.2.2.1, st.2.2.2, ())) ml := by
    intro st ml ⟨hml, hst⟩; subst hml
    cases hd : detectIte g k hk with
    | none => rw [hd] at hst; subst hst; exact hNone hd
    | some ctf => rcases ctf with ⟨c, t, f⟩; rw [hd] at hst; subst hst; exact hSome c t f hd
  have h1ne : ∀ x y : UInt32,
      (x.toBitVec &&& y.toBitVec &&& 1#32 ≠ 0#32) ↔ ((x &&& y &&& 1) != 0) = true := by
    intro x y; simp only [bne_iff_ne]
    exact ⟨fun h hz => h (congrArg UInt32.toBitVec hz),
      fun h hz => h (UInt32.eq_of_toBitVec_eq hz)⟩
  have heq_xor : ∀ x y : UInt32,
      (x.toBitVec = y.toBitVec ^^^ 1#32) ↔ (x == (y ^^^ 1)) = true := by
    intro x y; simp only [beq_iff_eq]
    exact ⟨fun h => UInt32.eq_of_toBitVec_eq h, fun h => congrArg UInt32.toBitVec h⟩
  have hshr1_eq : ∀ x : UInt32, (x.toBitVec >>> (1 : Nat)).toNat = (x >>> 1).toNat := fun _ => rfl
  have hshr1_div : ∀ x : UInt32, x.toBitVec.toNat / 2 ^ OfNat.ofNat 1 = (x >>> 1).toNat := by
    intro x
    change x.toBitVec.toNat / 2 ^ 1 = (x.toBitVec >>> (1 : Nat)).toNat
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  unfold detectIteExpr
  refine wp_join_state (ts := [i32, i32, i32, i32])
    (fun s => (s.1, s.2.1, s.2.2.1, s.2.2.2, ())) P
    (fun _ st ml h => by exact hP_cont st ml h) fun _ hJ0 => ?_
  c0_hstraight; c0_hsplit
  · have hneg : (((g.nodes[k]'hk).1 &&& (g.nodes[k]'hk).2 &&& 1) != 0) = true :=
      (h1ne _ _).mp hc
    clear hc
    c0_hstraight
    refine wp_join_state (ts := [i32, i32, i32, i32])
      (fun s => (s.1, s.2.1, s.2.2.1, s.2.2.2, ())) P
      (fun _ st ml h => by c0_hsteps; exact hJ0 st ml h) fun _ hJ1 => ?_
    c0_hstraight; c0_hsplit
    · have hln_gt : g.A < ((g.nodes[k]'hk).1 >>> 1).toNat := by
        rw [← hA, ← hshr1_div]; exact hc
      clear hc
      have hln_lt_g : ((g.nodes[k]'hk).1 >>> 1).toNat < g.A + 1 + k := (hwf k hk).1
      have hln_sub : ((g.nodes[k]'hk).1 >>> 1).toNat - (g.A + 1) < g.nodes.size := by omega
      c0_hstraight; c0_hsplit
      · have hrn_gt : g.A < ((g.nodes[k]'hk).2 >>> 1).toNat := by
          rw [← hA, ← hshr1_div]; exact hc
        clear hc
        have hrn_lt_g : ((g.nodes[k]'hk).2 >>> 1).toNat < g.A + 1 + k := (hwf k hk).2
        have hrn_sub : ((g.nodes[k]'hk).2 >>> 1).toNat - (g.A + 1) < g.nodes.size := by omega
        have hln_aw : ((g.nodes[k]'hk).1.toBitVec >>> (1 : Nat)).toNat < aigUsed.length := by
          rw [hshr1_eq]; omega
        have hrn_aw : ((g.nodes[k]'hk).2.toBitVec >>> (1 : Nat)).toNat < aigUsed.length := by
          rw [hshr1_eq]; omega
        have hln_eq : g.A + 1 + (((g.nodes[k]'hk).1 >>> 1).toNat - (g.A + 1)) =
            ((g.nodes[k]'hk).1 >>> 1).toNat := by omega
        have hrn_eq : g.A + 1 + (((g.nodes[k]'hk).2 >>> 1).toNat - (g.A + 1)) =
            ((g.nodes[k]'hk).2 >>> 1).toNat := by omega
        have hlp_get : aigUsed[((g.nodes[k]'hk).1.toBitVec >>> (1 : Nat)).toNat]'hln_aw =
            packAigGate (g.nodes[((g.nodes[k]'hk).1 >>> 1).toNat - (g.A + 1)]'hln_sub).1
              (g.nodes[((g.nodes[k]'hk).1 >>> 1).toNat - (g.A + 1)]'hln_sub).2 := by
          have hg := haig_w.gate_eq _ hln_sub
          simpa only [hln_eq, hshr1_eq] using hg
        have hrp_get : aigUsed[((g.nodes[k]'hk).2.toBitVec >>> (1 : Nat)).toNat]'hrn_aw =
            packAigGate (g.nodes[((g.nodes[k]'hk).2 >>> 1).toNat - (g.A + 1)]'hrn_sub).1
              (g.nodes[((g.nodes[k]'hk).2 >>> 1).toNat - (g.A + 1)]'hrn_sub).2 := by
          have hg := haig_w.gate_eq _ hrn_sub
          simpa only [hrn_eq, hshr1_eq] using hg
        c0_hstraight
        simp only [hlp_get, hrp_get, packAigGate_lo, packAigGate_hi]
        have hdet_eq : detectIte g k hk =
            let l0 := (g.nodes[((g.nodes[k]'hk).1 >>> 1).toNat - (g.A + 1)]'hln_sub).1
            let l1 := (g.nodes[((g.nodes[k]'hk).1 >>> 1).toNat - (g.A + 1)]'hln_sub).2
            let r0 := (g.nodes[((g.nodes[k]'hk).2 >>> 1).toNat - (g.A + 1)]'hrn_sub).1
            let r1 := (g.nodes[((g.nodes[k]'hk).2 >>> 1).toNat - (g.A + 1)]'hrn_sub).2
            if l0 == (r0 ^^^ 1) then some (l0, l1 ^^^ 1, r1 ^^^ 1)
            else if l0 == (r1 ^^^ 1) then some (l0, l1 ^^^ 1, r0 ^^^ 1)
            else if l1 == (r0 ^^^ 1) then some (l1, l0 ^^^ 1, r1 ^^^ 1)
            else if l1 == (r1 ^^^ 1) then some (l1, l0 ^^^ 1, r0 ^^^ 1)
            else none := by
          unfold detectIte; dsimp only
          simp only [hneg, ↓reduceIte, hln_gt, hln_sub, hrn_gt, hrn_sub, and_self, ↓reduceDIte]
        refine wp_join_state (ts := [i32, i32, i32, i32])
          (fun s => (s.1, s.2.1, s.2.2.1, s.2.2.2, ())) P
          (fun _ st ml h => by c0_hsteps; exact hJ1 st ml h) fun _ hJ2 => ?_
        c0_hstraight; c0_hsplit
        · have hm1 := (heq_xor _ _).mp hc
          c0_hstraight
          exact hJ2 _ m ⟨rfl, by rw [hdet_eq]; dsimp only; simp only [hm1, ↓reduceIte]; rfl⟩
        · have hm1 : ((g.nodes[((g.nodes[k]'hk).1 >>> 1).toNat - (g.A + 1)]'hln_sub).1 ==
              ((g.nodes[((g.nodes[k]'hk).2 >>> 1).toNat - (g.A + 1)]'hrn_sub).1 ^^^ 1)) = false :=
            Bool.eq_false_iff.mpr fun h => hc ((heq_xor _ _).mpr h)
          clear hc
          refine wp_join_state (ts := [i32, i32, i32, i32])
            (fun s => (s.1, s.2.1, s.2.2.1, s.2.2.2, ())) P
            (fun _ st ml h => by c0_hsteps; exact hJ2 st ml h)
            fun _ hJ3 => ?_
          c0_hstraight; c0_hsplit
          · have hm2 := (heq_xor _ _).mp hc
            c0_hstraight
            exact hJ3 _ m ⟨rfl, by
              rw [hdet_eq]; dsimp only
              simp only [hm1, Bool.false_eq_true, ↓reduceIte, hm2]; rfl⟩
          · have hm2 : ((g.nodes[((g.nodes[k]'hk).1 >>> 1).toNat - (g.A + 1)]'hln_sub).1 ==
                ((g.nodes[((g.nodes[k]'hk).2 >>> 1).toNat - (g.A + 1)]'hrn_sub).2 ^^^ 1)) = false :=
              Bool.eq_false_iff.mpr fun h => hc ((heq_xor _ _).mpr h)
            clear hc
            refine wp_join_state (ts := [i32, i32, i32, i32])
              (fun s => (s.1, s.2.1, s.2.2.1, s.2.2.2, ())) P
              (fun _ st ml h => by c0_hsteps; exact hJ3 st ml h)
              fun _ hJ4 => ?_
            c0_hstraight; c0_hsplit
            · have hm3 := (heq_xor _ _).mp hc
              c0_hstraight
              exact hJ4 _ m ⟨rfl, by
                rw [hdet_eq]; dsimp only
                simp only [hm1, hm2, Bool.false_eq_true, ↓reduceIte, hm3]; rfl⟩
            · have hm3 : ((g.nodes[((g.nodes[k]'hk).1 >>> 1).toNat - (g.A + 1)]'hln_sub).2 ==
                  ((g.nodes[((g.nodes[k]'hk).2 >>> 1).toNat - (g.A + 1)]'hrn_sub).1 ^^^ 1)) =
                  false :=
                Bool.eq_false_iff.mpr fun h => hc ((heq_xor _ _).mpr h)
              clear hc
              refine wp_join_state (ts := [i32, i32, i32, i32])
                (fun s => (s.1, s.2.1, s.2.2.1, s.2.2.2, ())) P
                (fun _ st ml h => by c0_hsteps; exact hJ4 st ml h)
                fun _ hJ5 => ?_
              c0_hstraight; c0_hsplit
              · have hm4 := (heq_xor _ _).mp hc
                c0_hstraight
                exact hJ5 _ m ⟨rfl, by
                  rw [hdet_eq]; dsimp only
                  simp only [hm1, hm2, hm3, Bool.false_eq_true, ↓reduceIte, hm4]; rfl⟩
              · have hm4 : ((g.nodes[((g.nodes[k]'hk).1 >>> 1).toNat - (g.A + 1)]'hln_sub).2 ==
                    ((g.nodes[((g.nodes[k]'hk).2 >>> 1).toNat - (g.A + 1)]'hrn_sub).2 ^^^ 1)) =
                    false :=
                  Bool.eq_false_iff.mpr fun h => hc ((heq_xor _ _).mpr h)
                c0_hstraight
                exact hJ5 (0#32, 0#32, 0#32, 0#32) m ⟨rfl, by
                  rw [hdet_eq]; dsimp only
                  simp only [hm1, hm2, hm3, hm4, Bool.false_eq_true, ↓reduceIte]⟩
      · have hrn_le : ¬ g.A < ((g.nodes[k]'hk).2 >>> 1).toNat := by
          rw [← hA, ← hshr1_div]; exact hc
        have hd_none : detectIte g k hk = none := by
          unfold detectIte; dsimp only
          simp only [hneg, ↓reduceIte, hln_gt, hln_sub, and_self, ↓reduceDIte, hrn_le, false_and]
        c0_hstraight
        exact hJ1 _ m ⟨rfl, by rw [hd_none]⟩
    · have hln_le : ¬ g.A < ((g.nodes[k]'hk).1 >>> 1).toNat := by
        rw [← hA, ← hshr1_div]; exact hc
      have hd_none : detectIte g k hk = none := by
        unfold detectIte; dsimp only
        simp only [hneg, ↓reduceIte, hln_le, false_and, ↓reduceDIte]
      c0_hstraight
      exact hJ1 _ m ⟨rfl, by rw [hd_none]⟩
  · have hneg : (((g.nodes[k]'hk).1 &&& (g.nodes[k]'hk).2 &&& 1) != 0) = false :=
      Bool.eq_false_iff.mpr fun h => ((h1ne _ _).mpr h) hc
    have hd_none : detectIte g k hk = none := by
      unfold detectIte; dsimp only; simp only [hneg, Bool.false_eq_true, ↓reduceIte]
    c0_hstraight
    exact hJ0 _ m ⟨rfl, by rw [hd_none]⟩

theorem bv_coi_mark_wp (Γ : Env) :
    ∀ xs m Q X, bvCoiMarkSpec xs m Q X → Func.wp Γ bv_coi_mark_body xs m Q X := by
  rintro ⟨h, root, ⟨⟩⟩ m Q X
    ⟨hdr, g, aigUsed, marks0, R, hwf, hA, hlen, hbd, haig_w, haig_l, hm_l, hmptr, hfit, hm, hQ⟩
  unfold bvDimacsBound at hbd
  c0_hsteps_nogrp
  have hlen_bd : hdr.aig_len.toNat < 2 ^ 32 := by omega
  have hA1_lt : g.A + 1 < 2 ^ 32 := by omega
  have hA1_eq : (hdr.num_atoms + (1 : BitVec 32)).toNat = g.A + 1 := by
    rw [BitVec.toNat_add, hA, show (1 : BitVec 32).toNat = 1 from rfl,
      Nat.mod_eq_of_lt hA1_lt]
  refine wp_while_state (ts := [i32]) (α := Nat × List UInt8)
    (fun st => (BitVec.ofNat 32 st.1, ()))
    (fun st => hdr.aig_len.toNat - st.1)
    (fun st ml => st.1 ≤ hdr.aig_len.toNat ∧ st.2.length = hdr.aig_len.toNat ∧
      st.2.take st.1 = List.replicate st.1 0 ∧
      (bvHdrMem h hdr ⋆ array64 hdr.aig_ptr aigUsed ⋆ bytes hdr.marks_ptr st.2 ⋆ R) ml)
    ?_ ?_
  · intro J hJ
    c0_hsteps
    exact hJ (0, marks0) m ⟨Nat.zero_le _, hm_l, by simp, hm⟩
  · intro J ⟨i, ms⟩ ml ⟨hi_le, hms_l, htake, hml⟩ ih
    dsimp only at hi_le hms_l htake hml
    c0_hsteps_nogrp
    · have hi_lt : i < hdr.aig_len.toNat := by c0_bv_omega [hc, hms_l]
      c0_hsteps!
      dsimp only at *
      rw [Std.ExtHashMap.sep_emp] at hm
      have heq_i : (BitVec.setWidth 64 (BitVec.ofNat 32 i)).toNat = i := by simp
      have h0_eq : (UInt8.ofBitVec (BitVec.ofNat 8 0)) = (0 : UInt8) := rfl
      rw [heq_i, h0_eq] at hm
      have htake' : (ms.set i 0).take (i + 1) = List.replicate (i + 1) 0 := by
        rw [List.take_succ_eq_append_getElem (by simpa [hms_l] using hi_lt),
          List.take_set_of_le (Nat.le_refl i), htake,
          List.getElem_set_self (by simpa [hms_l] using hi_lt),
          List.replicate_succ']
      have hi1 : BitVec.ofNat 32 i + (1 : BitVec 32) = BitVec.ofNat 32 (i + 1) := by
        apply BitVec.eq_of_toNat_eq
        simp [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega : i + 1 < 2 ^ 32)]
      rw [hi1]
      exact ih (i + 1, ms.set i 0) m (by omega)
        ⟨hi_lt, by simpa using hms_l, htake', sep_ac hm⟩
    · have hi_eq : i = hdr.aig_len.toNat := by c0_bv_omega [hc, hi_le, hms_l]
      subst hi_eq
      have hms_rep : ms = List.replicate hdr.aig_len.toNat 0 := by
        rw [← List.take_length (l := ms), hms_l]; exact htake
      clear hc htake
      c0_hsteps_nogrp
      refine wp_join_state0 (α := List UInt8)
        (fun ms1 ml1 => ms1.length = hdr.aig_len.toNat ∧
          marksToBool ms1 = (Array.replicate (g.A + 1 + g.nodes.size) false).setIfInBounds
            (UInt32.ofBitVec root >>> 1).toNat true ∧
          (bvHdrMem h hdr ⋆ array64 hdr.aig_ptr aigUsed ⋆ bytes hdr.marks_ptr ms1 ⋆ R) ml1)
        ?_ ?_
      · intro J2 ms1 ml1 ⟨hms1_l, hinit, hml1⟩
        c0_hsteps_nogrp
        refine wp_while_state (ts := [i32]) (α := Nat × List UInt8)
          (fun st => (BitVec.ofNat 32 (g.A + 1 + st.1), ()))
          (fun st => st.1)
          (fun st ml2 => st.1 ≤ g.nodes.size ∧ st.2.length = hdr.aig_len.toNat ∧
            coiMarkLoop g st.1 (marksToBool st.2) =
              Ref.Tseitin.coiMark g (UInt32.ofBitVec root) ∧
            (bvHdrMem h hdr ⋆ array64 hdr.aig_ptr aigUsed ⋆ bytes hdr.marks_ptr st.2 ⋆ R) ml2)
          ?_ ?_
        · intro J3 hJ3
          c0_hsteps
          have hlen_bv : hdr.aig_len = BitVec.ofNat 32 (g.A + 1 + g.nodes.size) := by
            apply BitVec.eq_of_toNat_eq; simp [hlen]
          rw [hlen_bv]
          have hloop0 : coiMarkLoop g g.nodes.size (marksToBool ms1) =
              Ref.Tseitin.coiMark g (UInt32.ofBitVec root) := by
            unfold Ref.Tseitin.coiMark; dsimp only; rw [← hinit]
          exact hJ3 (g.nodes.size, ms1) ml1 ⟨Nat.le_refl _, hms1_l, hloop0, hml1⟩
        · intro J3 ⟨k, ms2⟩ ml2 ⟨hk_le, hms2_l, hloop, hml2⟩ ih2
          dsimp only at hk_le hms2_l hloop hml2
          c0_hsteps_nogrp
          · have hk_pos : 0 < k := by c0_bv_omega [hc, hA1_eq, hms2_l]
            obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk_pos)
            clear hc
            have h1_32 : (1 : BitVec 32).toNat = 1 := rfl
            have hdec : BitVec.ofNat 32 (g.A + 1 + (k' + 1)) - (1 : BitVec 32) =
                BitVec.ofNat 32 (g.A + 1 + k') := by
              apply BitVec.eq_of_toNat_eq
              have hsub := U32Kit.bv32_toNat_sub_of_le
                (x := BitVec.ofNat 32 (g.A + 1 + (k' + 1))) (y := (1 : BitVec 32)) (by
                  simp only [BitVec.toNat_ofNat, h1_32,
                    Nat.mod_eq_of_lt (by omega : g.A + 1 + (k' + 1) < 2 ^ 32)]
                  omega)
              simp only [hsub, BitVec.toNat_ofNat, h1_32,
                Nat.mod_eq_of_lt (by omega : g.A + 1 + (k' + 1) < 2 ^ 32),
                Nat.mod_eq_of_lt (by omega : g.A + 1 + k' < 2 ^ 32)]
              omega
            rw [hdec] at *
            c0_hsteps_nogrp
            refine wp_join_state0 (α := List UInt8) (fun ms_fin ml_fin =>
                ms_fin.length = hdr.aig_len.toNat ∧
                coiMarkLoop g k' (marksToBool ms_fin) =
                  Ref.Tseitin.coiMark g (UInt32.ofBitVec root) ∧
                (bvHdrMem h hdr ⋆ array64 hdr.aig_ptr aigUsed ⋆
                  bytes hdr.marks_ptr ms_fin ⋆ R) ml_fin) ?_ ?_
            · intro J_out ms_fin ml_fin ⟨hmsf_l, hloop_f, hmlf⟩
              c0_hsteps
              exact ih2 (k', ms_fin) ml_fin (by omega) ⟨by omega, hmsf_l, hloop_f, hmlf⟩
            · intro J_out hJ_out
              c0_hsteps_nogrp
              · have hg_lt : g.A + 1 + k' < hdr.aig_len.toNat := by omega
                have hmark_nz : ms2[g.A + 1 + k'] ≠ 0 := by
                  intro hz
                  apply hc
                  apply BitVec.eq_of_toNat_eq
                  have h1 : (ms2[g.A + 1 + k']'(by omega)).toNat = 0 := by rw [hz]; rfl
                  simp [h1]
                have hgetD : (marksToBool ms2).getD (g.A + 1 + k') false = true := by
                  rw [marksToBool_getD ms2 (by omega)]
                  exact bne_iff_ne.mpr hmark_nz
                have haig_get : aigUsed[g.A + 1 + k']'(by omega) =
                    packAigGate g.nodes[k'].1 g.nodes[k'].2 := haig_w.gate_eq k' (by omega)
                have hidx : (BitVec.setWidth 64 (BitVec.ofNat 32 (g.A + 1 + k'))).toNat =
                    g.A + 1 + k' := by simp
                have h42 : (4294967295 : BitVec 64) = 0xFFFFFFFF#64 := rfl
                have hlo_eq : BitVec.setWidth 32 (packAigGate g.nodes[k'].1 g.nodes[k'].2 &&&
                    0xFFFFFFFF#64) = g.nodes[k'].1.toBitVec := packAigGate_lo _ _
                have hhi_eq : BitVec.setWidth 32 (packAigGate g.nodes[k'].1 g.nodes[k'].2 >>>
                    (32 : Nat)) = g.nodes[k'].2.toBitVec := packAigGate_hi _ _
                have hln_lt : (g.nodes[k'].1 >>> 1).toNat < hdr.aig_len.toNat :=
                  Nat.lt_trans (hwf k' (by omega)).1 (by omega)
                have hrn_lt : (g.nodes[k'].2 >>> 1).toNat < hdr.aig_len.toNat :=
                  Nat.lt_trans (hwf k' (by omega)).2 (by omega)
                simp only [hidx, haig_get, h42, hlo_eq, hhi_eq]
                refine (wp_detectIteExpr Γ Q X hdr.aig_ptr hdr.num_atoms g aigUsed
                  (bvHdrMem h hdr ⋆ bytes hdr.marks_ptr ms2 ⋆ R) ml2 k' (by omega) hA hwf haig_w
                  (by omega) (sep_ac hml2) _ (fun c t f hd => ?_) (fun hd => ?_))
                · have ⟨hc_lt, ht_lt, hf_lt⟩ := detectIte_bounds hwf hd
                  have hcn_lt : (c >>> 1).toNat < hdr.aig_len.toNat := by omega
                  have htn_lt : (t >>> 1).toNat < hdr.aig_len.toNat := by omega
                  have hfn_lt : (f >>> 1).toNat < hdr.aig_len.toNat := by omega
                  dsimp only
                  refine wp_join_state0 (α := List UInt8) (fun ms_fin ml_fin =>
                      ms_fin.length = hdr.aig_len.toNat ∧
                      coiMarkLoop g k' (marksToBool ms_fin) =
                        Ref.Tseitin.coiMark g (UInt32.ofBitVec root) ∧
                      (bvHdrMem h hdr ⋆ array64 hdr.aig_ptr aigUsed ⋆
                        bytes hdr.marks_ptr ms_fin ⋆ R) ml_fin)
                    (fun _ ms_fin ml_fin hf => by c0_hsteps; exact hJ_out ms_fin ml_fin hf)
                    fun _ hJ_ite => ?_
                  c0_hsteps_nogrp
                  refine wp_join_state0 (α := List UInt8) (fun ms3 ml3 =>
                      ms3.length = hdr.aig_len.toNat ∧
                      marksToBool ms3 = (marksToBool ms2).setIfInBounds (c >>> 1).toNat true ∧
                      (bvHdrMem h hdr ⋆ array64 hdr.aig_ptr aigUsed ⋆
                        bytes hdr.marks_ptr ms3 ⋆ R) ml3) ?_ ?_
                  · intro J4 ms3 ml3 ⟨hms3_l, hms3_b, hml3⟩; c0_hsteps_nogrp
                    refine wp_join_state0 (α := List UInt8) (fun ms4 ml4 =>
                        ms4.length = hdr.aig_len.toNat ∧
                        marksToBool ms4 = (marksToBool ms3).setIfInBounds (t >>> 1).toNat true ∧
                        (bvHdrMem h hdr ⋆ array64 hdr.aig_ptr aigUsed ⋆
                          bytes hdr.marks_ptr ms4 ⋆ R) ml4) ?_ ?_
                    · intro J5 ms4 ml4 ⟨hms4_l, hms4_b, hml4⟩; c0_hsteps_nogrp
                      refine wp_join_state0 (α := List UInt8) (fun ms5 ml5 =>
                          ms5.length = hdr.aig_len.toNat ∧
                          marksToBool ms5 = (marksToBool ms4).setIfInBounds (f >>> 1).toNat true ∧
                          (bvHdrMem h hdr ⋆ array64 hdr.aig_ptr aigUsed ⋆
                            bytes hdr.marks_ptr ms5 ⋆ R) ml5) ?_ ?_
                      · intro J6 ms5 ml5 ⟨hms5_l, hms5_b, hml5⟩; c0_hsteps
                        rw [coiMarkLoop_succ (by omega), hgetD, hd] at hloop
                        simp only [↓reduceIte] at hloop; rw [← hms3_b, ← hms4_b, ← hms5_b] at hloop
                        exact hJ_ite ms5 ml5 ⟨hms5_l, hloop, hml5⟩
                      · intro J6 hJ6; c0_hsteps_nogrp
                        · c0_hsteps!; dsimp only at *; rw [Std.ExtHashMap.sep_emp] at hm
                          rw [show UInt8.ofBitVec (BitVec.ofNat 8 1) = (1 : UInt8) from rfl,
                            show (BitVec.setWidth 64 (f.toBitVec >>> 1)).toNat = (f >>> 1).toNat by
                              simp] at hm
                          have hset := marksToBool_set_one ms4 (f >>> 1).toNat
                          simp only [show (f >>> 1).toNat < ms4.length by omega, ↓reduceIte] at hset
                          exact hJ6 (ms4.set (f >>> 1).toNat 1) m
                            ⟨by simpa using hms4_l, hset, sep_ac hm⟩
                        · exfalso; have ht : (f.toBitVec >>> 1).toNat < hdr.aig_len.toNat := hfn_lt
                          rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at ht
                          exact hc ht
                    · intro J5 hJ5; c0_hsteps_nogrp
                      · c0_hsteps!; dsimp only at *; rw [Std.ExtHashMap.sep_emp] at hm
                        rw [show UInt8.ofBitVec (BitVec.ofNat 8 1) = (1 : UInt8) from rfl,
                          show (BitVec.setWidth 64 (t.toBitVec >>> 1)).toNat = (t >>> 1).toNat by
                            simp] at hm
                        have hset := marksToBool_set_one ms3 (t >>> 1).toNat
                        simp only [show (t >>> 1).toNat < ms3.length by omega, ↓reduceIte] at hset
                        exact hJ5 (ms3.set (t >>> 1).toNat 1) m
                          ⟨by simpa using hms3_l, hset, sep_ac hm⟩
                      · exfalso; have htmp : (t.toBitVec >>> 1).toNat < hdr.aig_len.toNat := htn_lt
                        rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at htmp
                        exact hc htmp
                  · intro J4 hJ4; c0_hsteps_nogrp
                    · c0_hsteps!; dsimp only at *; rw [Std.ExtHashMap.sep_emp] at hm
                      rw [show UInt8.ofBitVec (BitVec.ofNat 8 1) = (1 : UInt8) from rfl,
                        show (BitVec.setWidth 64 (c.toBitVec >>> 1)).toNat = (c >>> 1).toNat by
                          simp] at hm
                      have hset := marksToBool_set_one ms2 (c >>> 1).toNat
                      simp only [show (c >>> 1).toNat < ms2.length by omega, ↓reduceIte] at hset
                      exact hJ4 (ms2.set (c >>> 1).toNat 1) m
                        ⟨by simpa using hms2_l, hset, sep_ac hm⟩
                    · exfalso; have ht : (c.toBitVec >>> 1).toNat < hdr.aig_len.toNat := hcn_lt
                      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at ht; exact hc ht
                · dsimp only
                  refine wp_join_state0 (α := List UInt8) (fun ms_fin ml_fin =>
                      ms_fin.length = hdr.aig_len.toNat ∧
                      coiMarkLoop g k' (marksToBool ms_fin) =
                        Ref.Tseitin.coiMark g (UInt32.ofBitVec root) ∧
                      (bvHdrMem h hdr ⋆ array64 hdr.aig_ptr aigUsed ⋆
                        bytes hdr.marks_ptr ms_fin ⋆ R) ml_fin)
                    (fun _ ms_fin ml_fin hf => by c0_hsteps; exact hJ_out ms_fin ml_fin hf)
                    fun _ hJ_and => ?_
                  c0_hsteps_nogrp
                  refine wp_join_state0 (α := List UInt8) (fun ms3 ml3 =>
                      ms3.length = hdr.aig_len.toNat ∧
                      marksToBool ms3 = (marksToBool ms2).setIfInBounds
                        (g.nodes[k'].1 >>> 1).toNat true ∧
                      (bvHdrMem h hdr ⋆ array64 hdr.aig_ptr aigUsed ⋆
                        bytes hdr.marks_ptr ms3 ⋆ R) ml3) ?_ ?_
                  · intro J4 ms3 ml3 ⟨hms3_l, hms3_b, hml3⟩
                    c0_hsteps_nogrp
                    refine wp_join_state0 (α := List UInt8) (fun ms4 ml4 =>
                        ms4.length = hdr.aig_len.toNat ∧
                        marksToBool ms4 = (marksToBool ms3).setIfInBounds
                          (g.nodes[k'].2 >>> 1).toNat true ∧
                        (bvHdrMem h hdr ⋆ array64 hdr.aig_ptr aigUsed ⋆
                          bytes hdr.marks_ptr ms4 ⋆ R) ml4) ?_ ?_
                    · intro J5 ms4 ml4 ⟨hms4_l, hms4_b, hml4⟩
                      c0_hsteps; rw [coiMarkLoop_succ (by omega), hgetD, hd] at hloop
                      simp only [↓reduceIte] at hloop; rw [← hms3_b, ← hms4_b] at hloop
                      exact hJ_and ms4 ml4 ⟨hms4_l, hloop, hml4⟩
                    · intro J5 hJ5; c0_hsteps_nogrp
                      · c0_hsteps!; dsimp only at *; rw [Std.ExtHashMap.sep_emp] at hm
                        rw [show UInt8.ofBitVec (BitVec.ofNat 8 1) = (1 : UInt8) from rfl,
                          show (BitVec.setWidth 64 (g.nodes[k'].2.toBitVec >>> 1)).toNat =
                            (g.nodes[k'].2 >>> 1).toNat by simp] at hm
                        have hset := marksToBool_set_one ms3 (g.nodes[k'].2 >>> 1).toNat
                        simp only [show (g.nodes[k'].2 >>> 1).toNat < ms3.length by omega,
                          ↓reduceIte] at hset
                        exact hJ5 (ms3.set (g.nodes[k'].2 >>> 1).toNat 1) m
                          ⟨by simpa using hms3_l, hset, sep_ac hm⟩
                      · exfalso
                        have htmp : (g.nodes[k'].2.toBitVec >>> 1).toNat < hdr.aig_len.toNat :=
                          hrn_lt
                        rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at htmp
                        exact hc htmp
                  · intro J4 hJ4; c0_hsteps_nogrp
                    · c0_hsteps!; dsimp only at *; rw [Std.ExtHashMap.sep_emp] at hm
                      rw [show UInt8.ofBitVec (BitVec.ofNat 8 1) = (1 : UInt8) from rfl,
                        show (BitVec.setWidth 64 (g.nodes[k'].1.toBitVec >>> 1)).toNat =
                          (g.nodes[k'].1 >>> 1).toNat by simp] at hm
                      have hset := marksToBool_set_one ms2 (g.nodes[k'].1 >>> 1).toNat
                      simp only [show (g.nodes[k'].1 >>> 1).toNat < ms2.length by omega,
                        ↓reduceIte] at hset
                      exact hJ4 (ms2.set (g.nodes[k'].1 >>> 1).toNat 1) m
                        ⟨by simpa using hms2_l, hset, sep_ac hm⟩
                    · exfalso
                      have htmp : (g.nodes[k'].1.toBitVec >>> 1).toNat < hdr.aig_len.toNat := hln_lt
                      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at htmp
                      exact hc htmp
              · have hmark_z : ms2[g.A + 1 + k'] = 0 := by
                  have hmod : (g.A + 1 + k') % 2 ^ 32 = g.A + 1 + k' :=
                    Nat.mod_eq_of_lt (by omega)
                  simp only [hmod] at hc
                  have h2 := congrArg BitVec.toNat hc
                  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat] at h2
                  have hlt8 := (ms2[g.A + 1 + k']'(by omega)).toNat_lt
                  rw [Nat.mod_eq_of_lt (by omega : (ms2[g.A + 1 + k']'(by omega)).toNat < 2 ^ 8),
                    Nat.mod_eq_of_lt
                      (by omega : (ms2[g.A + 1 + k']'(by omega)).toNat < 2 ^ 32)] at h2
                  exact UInt8.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq h2)
                have hgetD : (marksToBool ms2).getD (g.A + 1 + k') false = false := by
                  rw [marksToBool_getD ms2 (by omega), hmark_z]; rfl
                rw [coiMarkLoop_succ (by omega), hgetD] at hloop
                exact hJ_out ms2 ml2 ⟨hms2_l, hloop, hml2⟩
          · have hk0 : k = 0 := by c0_bv_omega [hc, hA1_eq, hms2_l]
            subst hk0
            simp only [coiMarkLoop] at hloop
            exact hQ ms2 ml2 hms2_l hloop hml2
      · intro J1 hJ1
        c0_hsteps
        · have hrn_lt : (root >>> 1).toNat < hdr.aig_len.toNat := by c0_bv_omega [hc, hlen_bd]
          c0_hsteps!
          dsimp only at *
          rw [Std.ExtHashMap.sep_emp] at hm
          have h1_eq : UInt8.ofBitVec (BitVec.ofNat 8 1) = (1 : UInt8) := rfl
          have heq_r : (BitVec.setWidth 64 (root >>> 1)).toNat = (root >>> 1).toNat := by simp
          rw [h1_eq, heq_r] at hm
          refine hJ1 (ms.set (root >>> 1).toNat 1) m ⟨by simpa using hms_l, ?_, sep_ac hm⟩
          have hset := marksToBool_set_one ms (root >>> 1).toNat
          simp only [show (root >>> 1).toNat < ms.length by omega, ↓reduceIte] at hset
          rw [hms_rep, hlen]
          rw [hms_rep, hlen, marksToBool_replicate_false] at hset
          exact hset
        · have hroot_nat : (root >>> 1).toNat = root.toNat / 2 := by
            rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_one]
          have hrn_ge : ¬ (root >>> 1).toNat < hdr.aig_len.toNat := by
            rw [show (root >>> 1).toNat = root.toNat / 2 ^ 1 from by
              rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]]
            c0_bv_omega [hc, hlen_bd]
          refine hJ1 ms ml ⟨hms_l, ?_, hml⟩
          rw [hms_rep, marksToBool_replicate_false, hlen]
          dsimp only [Array.setIfInBounds]
          split
          · next h =>
            exfalso
            rw [Array.size_replicate,
              show (UInt32.ofBitVec root >>> 1).toNat = (root >>> 1).toNat from rfl,
              ← hlen] at h
            exact hrn_ge h
          · rfl

theorem bv_dec_len_wp (Γ : Env) :
    ∀ xs m Q X, bvDecLenSpec xs m Q X → Func.wp Γ bv_dec_len_body xs m Q X := by
  rintro ⟨v, ⟨⟩⟩ m Q X hQ
  unfold bvDecLenSpec at hQ
  dsimp only at hQ
  c0_hsteps_nogrp
  · have hlt : v.toNat < 10 := by c0_bv_omega [hc]
    rw [natToBytes_lt_10 hlt] at hQ
    exact hQ
  · have hge : 10 ≤ v.toNat := by c0_bv_omega [hc]
    clear hc
    refine wp_while_state (ts := [i32, i64]) (α := Nat × Nat)
      (fun p => (BitVec.ofNat 32 p.1, BitVec.ofNat 64 p.2, ()))
      (fun p => p.1)
      (fun p ml => ml = m ∧ p.1 < 2 ^ 32 ∧ p.2 ≤ 10 ∧
        (if p.1 = 0 then p.2 = (natToBytes v.toNat).length
         else p.2 + (natToBytes p.1).length = (natToBytes v.toNat).length))
      ?_ ?_
    · intro J hJ
      c0_hsteps
      have hof : BitVec.ofNat 32 v.toNat = v := BitVec.eq_of_toNat_eq (by simp)
      have h0 := hJ (v.toNat, 0) m ⟨rfl, v.isLt, by omega, by simp [show v.toNat ≠ 0 by omega]⟩
      simpa [hof] using h0
    · intro J ⟨vc, n⟩ ml ⟨hml, hvc32, hn10, hinv⟩ ih
      subst hml
      c0_hsteps_nogrp
      · have hpos : 0 < vc := by c0_bv_omega [hc, hvc32]
        clear hc
        simp only [Nat.ne_of_gt hpos, ↓reduceIte] at hinv
        have hn1 : n + 1 ≤ 10 := by
          by_cases h10 : vc < 10
          · have : (natToBytes vc).length = 1 := by rw [natToBytes_lt_10 h10]; simp
            have hle := natToBytes_length_le_10 v.isLt
            omega
          · have hge10 : 10 ≤ vc := by omega
            rw [natToBytes_ge_10 hge10] at hinv
            simp only [List.length_append, List.length_singleton] at hinv
            have hle := natToBytes_length_le_10 v.isLt
            have := natToBytes_length_pos (vc / 10)
            omega
        have hinv' : (if vc / 10 = 0 then n + 1 = (natToBytes v.toNat).length
            else n + 1 + (natToBytes (vc / 10)).length = (natToBytes v.toNat).length) := by
          by_cases h10 : vc < 10
          · have hdiv0 : vc / 10 = 0 := Nat.div_eq_of_lt h10
            have hlen1 : (natToBytes vc).length = 1 := by rw [natToBytes_lt_10 h10]; simp
            simp only [hdiv0, ↓reduceIte]; omega
          · have hge10 : 10 ≤ vc := by omega
            have hdiv0 : vc / 10 ≠ 0 := by omega
            rw [natToBytes_ge_10 hge10] at hinv
            simp only [List.length_append, List.length_singleton] at hinv
            simp only [hdiv0, ↓reduceIte]; omega
        have heq_v : BitVec.ofNat 32 vc / 10 = BitVec.ofNat 32 (vc / 10) := by
          apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_udiv]
        have heq_n : BitVec.ofNat 64 n + 1 = BitVec.ofNat 64 (n + 1) := by
          apply BitVec.eq_of_toNat_eq
          simp [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega : n + 1 < 2 ^ 64)]
        have hstep := ih (vc / 10, n + 1) ml (Nat.div_lt_self hpos (by decide))
          ⟨rfl, by omega, hn1, hinv'⟩
        dsimp only at hstep ⊢
        rw [heq_v, heq_n]
        exact hstep
      · have hvc0 : vc = 0 := by c0_bv_omega [hc, hvc32]
        subst hvc0
        simp only [↓reduceIte] at hinv
        rw [hinv]
        exact hQ

theorem bv_lit_bytes_wp (Γ : Env)
    (hDecLen : ∀ xs m Q X, bvDecLenSpec xs m Q X →
      Γ "bv_dec_len" [i32] [i64] xs m Q X) :
    ∀ xs m Q X, bvLitBytesSpec xs m Q X → Func.wp Γ bv_lit_bytes_body xs m Q X := by
  rintro ⟨lit, ⟨⟩⟩ m Q X hQ
  unfold bvLitBytesSpec at hQ
  dsimp only at hQ
  c0_hstraight
  c0_call hDecLen
  unfold bvDecLenSpec
  dsimp only
  c0_hsteps
  have h1 : BitVec.ofNat 64 (encodeDimacsLit (litToDimacs (UInt32.ofBitVec lit))).length =
      (lit &&& 1).setWidth 64 +
        BitVec.ofNat 64 (natToBytes ((lit >>> 1) + 1).toNat).length + 1 := by
    apply BitVec.eq_of_toNat_eq
    rw [encodeDimacsLit_length_bv, bv32_lsr1_add1_toNat]
    have hlen := natToBytes_length_le_10 (n := (lit >>> 1).toNat + 1) (by
      have := lit.isLt
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_one]; omega)
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_one] at hlen
    have h1_64 : (1 : BitVec 64).toNat = 1 := rfl
    have ha := bv_c0_toNat_and_one_32 lit
    have hand_eq : (lit &&& 1).toNat = (lit &&& 1#32).toNat := rfl
    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, h1_64, hand_eq,
      BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_one]
    rw [Nat.mod_eq_of_lt (by omega : (natToBytes (lit.toNat / 2 + 1)).length < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : (lit &&& 1#32).toNat < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega :
        (lit &&& 1#32).toNat + (natToBytes (lit.toNat / 2 + 1)).length < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega :
        (lit &&& 1#32).toNat + (natToBytes (lit.toNat / 2 + 1)).length + 1 < 2 ^ 64)]
  rw [← h1]
  exact hQ

theorem bv_write_dec_wp (Γ : Env)
    (hDecLen : ∀ xs m Q X, bvDecLenSpec xs m Q X →
      Γ "bv_dec_len" [i32] [i64] xs m Q X) :
    ∀ xs m Q X, bvWriteDecSpec xs m Q X → Func.wp Γ bv_write_dec_body xs m Q X := by
  rintro ⟨p, v, ⟨⟩⟩ m Q X ⟨R, hfit, hm, hQ⟩
  c0_hstraight
  c0_call hDecLen
  unfold bvDecLenSpec
  dsimp only
  c0_hsteps_nogrp
  · have hv0 : v = 0#32 := by c0_bv_omega [hc]
    subst hv0
    have hbs : natToBytes (0#32 : BitVec 32).toNat = [48] := by
      rw [show (0#32 : BitVec 32).toNat = 0 from rfl, natToBytes_lt_10 (by decide)]; rfl
    have hlen1 : (natToBytes (0#32 : BitVec 32).toNat).length = 1 := by rw [hbs]; rfl
    rw [hlen1] at hfit hm
    rw [hbs] at hQ ⊢
    c0_hsteps!
    exact hQ _ (by assumption)
  · have hv_ne : v ≠ 0#32 := by c0_bv_omega [hc]
    have hv_pos : 0 < v.toNat := by c0_bv_omega [hv_ne]
    clear hc
    let len := (natToBytes v.toNat).length
    have hlen_le : len ≤ 10 := natToBytes_length_le_10 v.isLt
    have hlen_pos : 0 < len := natToBytes_length_pos v.toNat
    refine wp_while_state (ts := [i32, i64]) (α := Nat × List UInt8)
      (fun st => (BitVec.ofNat 32 st.1, p + BitVec.ofNat 64 (len - st.2.length), ()))
      (fun st => st.1)
      (fun st ml => st.1 < 2 ^ 32 ∧ st.2.length ≤ len ∧
        (if st.1 = 0 then st.2 = natToBytes v.toNat
         else natToBytes st.1 ++ st.2 = natToBytes v.toNat) ∧
        (region p (len - st.2.length) ⋆
          (bytes (p + BitVec.ofNat 64 (len - st.2.length)) st.2 ⋆ R)) ml)
      ?_ ?_
    · intro J hJ
      c0_hsteps
      have hv_of : BitVec.ofNat 32 v.toNat = v := BitVec.eq_of_toNat_eq (by simp)
      have hm_init : (region p len ⋆ (bytes (p + BitVec.ofNat 64 len) [] ⋆ R)) m := by
        have hb : (bytes (p + BitVec.ofNat 64 len) [] ⋆ R) = R := by
          unfold bytes; rw [← eq_nil_At, emp_sep]
        rw [hb]; exact hm
      have h0 := hJ (v.toNat, []) m ⟨v.isLt, Nat.zero_le _, by simp [Nat.ne_of_gt hv_pos], hm_init⟩
      simpa [hv_of, len] using h0
    · intro J ⟨vc, suf⟩ ml ⟨hvc32, hsuf_le, hinv, hml⟩ ih
      c0_hsteps_nogrp
      · have hpos : 0 < vc := by c0_bv_omega [hc, hvc32]
        clear hc
        simp only [Nat.ne_of_gt hpos, ↓reduceIte] at hinv
        have hk_eq : len - suf.length = (natToBytes vc).length := by
          have := congrArg List.length hinv
          simp only [List.length_append] at this
          omega
        have hk_pos : 1 ≤ len - suf.length := by
          rw [hk_eq]; exact natToBytes_length_pos vc
        have hk64 : len - suf.length ≤ 2 ^ 64 := by omega
        let dig : UInt8 := (48 + vc % 10).toUInt8
        let dv : BitVec 8 := (48 + BitVec.ofNat 32 vc % 10#32).setWidth 8
        have hdv_eq : UInt8.ofBitVec dv = dig := by
          apply UInt8.eq_of_toBitVec_eq; apply BitVec.eq_of_toNat_eq
          change dv.toNat = dig.toNat
          have h10_32 : (10#32 : BitVec 32).toNat = 10 := rfl
          have h48_32 : (48 : BitVec 32).toNat = 48 := rfl
          have hdv_lt : 48 + vc % 10 < 2 ^ 8 := by omega
          have hdv_32 : 48 + vc % 10 < 2 ^ 32 := by omega
          dsimp only [dv, dig, Nat.toUInt8]
          rw [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_umod,
            h48_32, h10_32, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hvc32,
            Nat.mod_eq_of_lt hdv_32, Nat.mod_eq_of_lt hdv_lt,
            UInt8.toNat_ofNat', Nat.mod_eq_of_lt hdv_lt]
        have h1_64 : (1 : BitVec 64).toNat = 1 := rfl
        have hptr_sub : p + BitVec.ofNat 64 (len - suf.length) - 1 =
            p + BitVec.ofNat 64 (len - suf.length - 1) := by
          rw [bv64_sub_eq_ofNat]
          · apply BitVec.eq_of_toNat_eq
            simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
              Nat.mod_eq_of_lt (by omega : len - suf.length < 2 ^ 64),
              Nat.mod_eq_of_lt (by omega : p.toNat + (len - suf.length) < 2 ^ 64),
              Nat.mod_eq_of_lt (by omega : len - suf.length - 1 < 2 ^ 64),
              Nat.mod_eq_of_lt (by omega : p.toNat + (len - suf.length - 1) < 2 ^ 64)]
            omega
          · rw [BitVec.toNat_add, BitVec.toNat_ofNat, h1_64,
              Nat.mod_eq_of_lt (by omega : len - suf.length < 2 ^ 64),
              Nat.mod_eq_of_lt (by omega : p.toNat + (len - suf.length) < 2 ^ 64)]
            omega
        have hst := store_region_tail_byte hk_pos hk64 dv (by omega) hml
        rw [← hptr_sub] at hst
        refine head_wp_store rfl rfl hst (fun ml' hml' => ?_)
        · rw [hdv_eq] at hml'
          c0_hsteps_nogrp
          have hlen_suf' : (dig :: suf).length = suf.length + 1 := rfl
          have hsuf'_le : (dig :: suf).length ≤ len := by omega
          have hsub_eq : len - (dig :: suf).length = len - suf.length - 1 := by omega
          have hinv' : (if vc / 10 = 0 then dig :: suf = natToBytes v.toNat
              else natToBytes (vc / 10) ++ (dig :: suf) = natToBytes v.toNat) := by
            by_cases h10 : vc < 10
            · have hdiv0 : vc / 10 = 0 := Nat.div_eq_of_lt h10
              rw [natToBytes_lt_10 h10, List.singleton_append] at hinv
              simp only [hdiv0, ↓reduceIte, dig, Nat.mod_eq_of_lt h10]; exact hinv
            · have hge10 : 10 ≤ vc := by omega
              have hdiv0 : vc / 10 ≠ 0 := by omega
              rw [natToBytes_ge_10 hge10, List.append_assoc, List.singleton_append] at hinv
              simp only [hdiv0, ↓reduceIte, dig]; exact hinv
          have heq_v : BitVec.ofNat 32 vc / 10 = BitVec.ofNat 32 (vc / 10) := by
            apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_udiv]
          rw [hptr_sub, ← hsub_eq] at hml'
          have hstep := ih (vc / 10, dig :: suf) ml' (Nat.div_lt_self hpos (by decide))
            ⟨by omega, hsuf'_le, hinv', hml'⟩
          dsimp only at hstep ⊢
          rw [hptr_sub, ← hsub_eq, heq_v]
          exact hstep
      · have hvc0 : vc = 0 := by c0_bv_omega [hc, hvc32]
        subst hvc0
        simp only [↓reduceIte] at hinv
        subst hinv
        have hsub0 : len - (natToBytes v.toNat).length = 0 := Nat.sub_self _
        rw [hsub0, region_zero, emp_sep, show BitVec.ofNat 64 0 = 0#64 from rfl,
          BitVec.add_zero] at hml
        exact hQ ml hml

theorem bv_write_lit_wp (Γ : Env)
    (hWriteDec : ∀ xs m Q X, bvWriteDecSpec xs m Q X →
      Γ "bv_write_dec" [i64, i32] [i64] xs m Q X) :
    ∀ xs m Q X, bvWriteLitSpec xs m Q X → Func.wp Γ bv_write_lit_body xs m Q X := by
  rintro ⟨p, lit, ⟨⟩⟩ m Q X ⟨R, hfit, hm, hQ⟩
  let v := (lit >>> (1 : BitVec 32)) + (1 : BitVec 32)
  let dbs := natToBytes v.toNat
  have hdbs_le : dbs.length ≤ 10 := natToBytes_length_le_10 v.isLt
  have hv_eq : v.toNat = (lit >>> 1).toNat + 1 := bv32_lsr1_add1_toNat lit
  have hbs_eq : encodeDimacsLit (litToDimacs (UInt32.ofBitVec lit)) =
      (if (lit &&& 1#32) == 0#32 then [] else [asciiMinus]) ++ dbs ++ [asciiSpace] := by
    rw [encodeDimacsLit_eq_bv, ← hv_eq]
  rw [hbs_eq] at hfit hm hQ
  c0_hsteps_nogrp
  refine wp_join_state1 (fun isNeg : Bool =>
      if isNeg then p + BitVec.ofNat 64 1 else p)
    (fun isNeg ml => isNeg = !((lit &&& 1#32) == 0#32) ∧
      (region (if isNeg then p + BitVec.ofNat 64 1 else p) (dbs.length + 1) ⋆
        (bytes p (if isNeg then [asciiMinus] else []) ⋆ R)) ml)
    ?_ ?_
  · intro _ isNeg ml ⟨his, hml⟩
    subst his
    c0_hstraight
    let q := if !((lit &&& 1#32) == 0#32) then p + BitVec.ofNat 64 1 else p
    have hsp := region_split_prefix (a := q) (n1 := dbs.length) (n2 := 1)
      (by omega) (hml : (region q (dbs.length + 1) ⋆ _) ml)
    c0_call hWriteDec
    refine ⟨region _ 1 ⋆ (bytes p (if !((lit &&& 1#32) == 0#32) then [asciiMinus] else []) ⋆ R),
      ?_, hsp, ?_⟩
    · simp only [List.length_append, List.length_cons, List.length_nil] at hfit
      by_cases h0 : (lit &&& 1#32) == 0#32
      · have hfit' : p.toNat + dbs.length + 1 < 2 ^ 64 := by
          simp only [h0, ↓reduceIte, List.length_nil, Nat.zero_add] at hfit; omega
        simp only [h0, Bool.not_true]
        change p.toNat + dbs.length < 2 ^ 64; omega
      · have hfit' : p.toNat + 1 + dbs.length + 1 < 2 ^ 64 := by
          simp only [h0, Bool.false_eq_true, ↓reduceIte, List.length_cons, List.length_nil] at hfit
          omega
        simp only [h0, Bool.not_false, ↓reduceIte]
        have hp1 : (p + BitVec.ofNat 64 1).toNat = p.toNat + 1 := by
          rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
            Nat.mod_eq_of_lt (by omega)]
        change (p + BitVec.ofNat 64 1).toNat + dbs.length < 2 ^ 64
        omega
    · intro ml' hml'
      have hml_reg : (region (q + BitVec.ofNat 64 dbs.length) 1 ⋆
          (bytes q dbs ⋆ (bytes p (if !((lit &&& 1#32) == 0#32) then [asciiMinus] else []) ⋆ R)))
          ml' := by
        have htmp : (region (q + BitVec.ofNat 64 dbs.length) 1 ⋆
            (bytes (if !((lit &&& 1#32) == 0#32) then p + 1#64 else p)
              (natToBytes (1 + (lit >>> (1 : BitVec 32))).toNat) ⋆
              (bytes p (if !((lit &&& 1#32) == 0#32) then [asciiMinus] else []) ⋆ R)))
            ml' := sep_ac hml'
        rw [BitVec.add_comm 1 (lit >>> (1 : BitVec 32))] at htmp
        exact htmp
      have hst := store_region_one (BitVec.ofNat 8 32) hml_reg
      refine head_wp_store rfl (by dsimp [q, dbs, v]) hst (fun m_fin hm_fin => ?_)
      c0_hsteps
      have hmrg : (bytes p (if !((lit &&& 1#32) == 0#32) then [asciiMinus] else []) ⋆
          bytes q dbs ⋆ bytes (q + BitVec.ofNat 64 dbs.length) [asciiSpace] ⋆ R) m_fin := by
        have hv32 : UInt8.ofBitVec (BitVec.ofNat 8 32) = asciiSpace := rfl
        rw [hv32] at hm_fin; exact sep_ac hm_fin
      have hbytes_eq : (bytes p (if !((lit &&& 1#32) == 0#32) then [asciiMinus] else []) ⋆
          bytes q dbs ⋆ bytes (q + BitVec.ofNat 64 dbs.length) [asciiSpace]) =
          bytes p ((if (lit &&& 1#32) == 0#32 then [] else [asciiMinus]) ++
            dbs ++ [asciiSpace]) := by
        by_cases h0 : (lit &&& 1#32) == 0#32
        · simp only [q, h0, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          rw [show (bytes p [] ⋆ bytes p dbs ⋆ bytes (p + BitVec.ofNat 64 dbs.length) [asciiSpace])
              = (bytes p dbs ⋆ bytes (p + BitVec.ofNat 64 dbs.length) [asciiSpace]) from by
            rw [sep_assoc]; unfold bytes; rw [← eq_nil_At, emp_sep]]
          rw [bytes_append_merge (by simp; omega)]; simp
        · simp only [q, h0, Bool.not_false, ↓reduceIte]
          have h1 : (bytes p [asciiMinus] ⋆ bytes (p + BitVec.ofNat 64 1) dbs) =
              bytes p ([asciiMinus] ++ dbs) := by
            simpa using bytes_append_merge (a := p) (b1 := [asciiMinus]) (b2 := dbs)
              (by simp; omega)
          have hlen1 : 1 + dbs.length = ([asciiMinus] ++ dbs).length := by simp [Nat.add_comm]
          rw [h1, show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl,
            ptr_add_ofNat, hlen1, bytes_append_merge (by simp; omega)]; simp
      have hmem_fin : (bytes p ((if (lit &&& 1#32) == 0#32 then [] else [asciiMinus]) ++
          dbs ++ [asciiSpace]) ⋆ R) m_fin := by rw [← hbytes_eq]; exact sep_ac hmrg
      have hp_fin : q + BitVec.ofNat 64 dbs.length + 1 =
          p + BitVec.ofNat 64 ((if (lit &&& 1#32) == 0#32 then [] else [asciiMinus]) ++
            dbs ++ [asciiSpace]).length := by
        by_cases h0 : (lit &&& 1#32) == 0#32
        · simp [q, dbs, v, h0, ptr_add_ofNat]
        · simp [q, dbs, v, h0, ptr_add_ofNat, Nat.add_comm]
      change Q (q + BitVec.ofNat 64 dbs.length + 1, ()) m_fin
      rw [hp_fin]; exact hQ m_fin hmem_fin
  · intro J hJ
    c0_hsteps_nogrp
    · have hne : ((lit &&& 1#32) == 0#32) = false := by
        rw [beq_eq_false_iff_ne]
        intro heq
        change lit &&& 1 = 0 at heq
        exact hc heq
      have hlen_tot : ((if (lit &&& 1#32) == 0#32 then [] else [asciiMinus]) ++
          dbs ++ [asciiSpace]).length = 1 + (dbs.length + 1) := by
        simp [hne]; omega
      rw [hlen_tot] at hm
      have h12 : 1 + (dbs.length + 1) ≤ 2 ^ 64 := by omega
      have hsp := region_split_prefix (a := p) (n1 := 1) (n2 := dbs.length + 1) h12 hm
      c0_hsteps!
      have hv45 : UInt8.ofBitVec (BitVec.ofNat 8 45) = asciiMinus := rfl
      rw [hv45] at hm
      exact hJ true m ⟨by simp [hne], by simpa [hne] using sep_ac hm⟩
    · have heq : ((lit &&& 1#32) == 0#32) = true := by
        rw [beq_iff_eq]
        change lit &&& 1 = 0
        c0_bv_omega [hc]
      have hlen_tot : ((if (lit &&& 1#32) == 0#32 then [] else [asciiMinus]) ++
          dbs ++ [asciiSpace]).length = dbs.length + 1 := by
        simp [heq]
      rw [hlen_tot] at hm
      have hm' : (region p (dbs.length + 1) ⋆ (bytes p [] ⋆ R)) m := by
        have hb : (bytes p [] ⋆ R) = R := by unfold bytes; rw [← eq_nil_At, emp_sep]
        rw [hb]; exact hm
      exact hJ false m ⟨by simp [heq], by simpa [heq] using hm'⟩

theorem bv_write_dimacs_hdr_wp (Γ : Env)
    (hWriteDec : ∀ xs m Q X, bvWriteDecSpec xs m Q X →
      Γ "bv_write_dec" [i64, i32] [i64] xs m Q X) :
    ∀ xs m Q X, bvWriteDimacsHdrSpec xs m Q X →
      Func.wp Γ bv_write_dimacs_hdr_body xs m Q X := by
  rintro ⟨p, mv, nc, ⟨⟩⟩ m Q X ⟨R, hfit, hm, hQ⟩
  let bs_mv := natToBytes mv.toNat
  let bs_nc := natToBytes nc.toNat
  have hlen_tot : (dimacsHeaderPrefix ++ bs_mv ++ [asciiSpace] ++ bs_nc ++
      [asciiNewline]).length = 6 + (bs_mv.length + (1 + (bs_nc.length + 1))) := by
    simp [dimacsHeaderPrefix]; omega
  rw [hlen_tot] at hfit hm
  have hfit64 : 6 + (bs_mv.length + (1 + (bs_nc.length + 1))) ≤ 2 ^ 64 := by omega
  have hfit_m : p.toNat + (6 + bs_mv.length + 1 + bs_nc.length + 1) < 2 ^ 64 := by omega
  have hp6 : (p + 6#64).toNat = p.toNat + 6 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have h1 := region_split_prefix (a := p) (n1 := 6)
    (n2 := bs_mv.length + (1 + (bs_nc.length + 1))) hfit64 hm
  obtain ⟨bs6, hbs6, hbm6⟩ := region_to_bytes_sep (a := p) (n := 6) h1
  rcases bs6 with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | _⟩⟩⟩⟩⟩⟩ <;>
    (simp only [List.length_nil, List.length_cons] at hbs6; try omega)
  c0_hstraight
  refine head_wp_store rfl (by simp) (store_bytes_at (i := 0) _ (by simp) (by simp) hbm6)
    (fun _ hm_0 => ?_)
  c0_hstraight
  refine head_wp_store rfl rfl (store_bytes_at (i := 1) _ (by simp) (by simp) hm_0)
    (fun _ hm_1 => ?_)
  c0_hstraight
  refine head_wp_store rfl rfl (store_bytes_at (i := 2) _ (by simp) (by simp) hm_1)
    (fun _ hm_2 => ?_)
  c0_hstraight
  refine head_wp_store rfl rfl (store_bytes_at (i := 3) _ (by simp) (by simp) hm_2)
    (fun _ hm_3 => ?_)
  c0_hstraight
  refine head_wp_store rfl rfl (store_bytes_at (i := 4) _ (by simp) (by simp) hm_3)
    (fun _ hm_4 => ?_)
  c0_hstraight
  refine head_wp_store rfl rfl (store_bytes_at (i := 5) _ (by simp) (by simp) hm_4)
    (fun m1 hm1 => ?_)
  dsimp only at hm1
  have hm1' : (bytes p dimacsHeaderPrefix ⋆
      (region (p + 6#64) (bs_mv.length + (1 + (bs_nc.length + 1))) ⋆ R)) m1 := hm1
  have h2 := region_split_prefix (a := p + BitVec.ofNat 64 6) (n1 := bs_mv.length)
    (n2 := 1 + (bs_nc.length + 1)) (by omega)
    (sep_ac hm1' : (region (p + BitVec.ofNat 64 6) _ ⋆ (bytes p dimacsHeaderPrefix ⋆ R)) m1)
  c0_hstraight
  c0_call hWriteDec
  refine ⟨_, by change (p + 6#64).toNat + bs_mv.length < 2 ^ 64; omega, h2, fun m2 hm2 => ?_⟩
  have h3 := region_split_prefix (a := p + BitVec.ofNat 64 6 + BitVec.ofNat 64 bs_mv.length)
    (n1 := 1) (n2 := bs_nc.length + 1) (by omega)
    (sep_ac hm2 : (region _ _ ⋆ (bytes p dimacsHeaderPrefix ⋆
      bytes (p + BitVec.ofNat 64 6) bs_mv ⋆ R)) m2)
  refine head_wp_store rfl (by dsimp [bs_mv]) (store_region_one _ h3) (fun m2' hm2' => ?_)
  have hp6mv : (p + BitVec.ofNat 64 6 + BitVec.ofNat 64 bs_mv.length + (1 : BitVec 64)).toNat =
      p.toNat + 6 + bs_mv.length + 1 := by
    have h1_64 : (1 : BitVec 64).toNat = 1 := rfl
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, h1_64]
    rw [Nat.mod_eq_of_lt (by omega : 6 < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : p.toNat + 6 < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : bs_mv.length < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : p.toNat + 6 + bs_mv.length < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : p.toNat + 6 + bs_mv.length + 1 < 2 ^ 64)]
  have h4 := region_split_prefix
    (a := p + BitVec.ofNat 64 6 + BitVec.ofNat 64 bs_mv.length + (1 : BitVec 64))
    (n1 := bs_nc.length) (n2 := 1) (by omega)
    (sep_ac hm2' : (region _ _ ⋆ (bytes p dimacsHeaderPrefix ⋆
      bytes (p + BitVec.ofNat 64 6) bs_mv ⋆
      bytes (p + BitVec.ofNat 64 6 + BitVec.ofNat 64 bs_mv.length)
        [UInt8.ofBitVec ((32#32).setWidth 8)] ⋆ R)) m2')
  c0_hstraight
  c0_call hWriteDec
  have hfit_nc : (p + BitVec.ofNat 64 6 + BitVec.ofNat 64 bs_mv.length + (1 : BitVec 64)).toNat +
      bs_nc.length < 2 ^ 64 := by
    rw [hp6mv]; omega
  refine ⟨_, hfit_nc, h4, fun m3 hm3 => ?_⟩
  have h32 : UInt8.ofBitVec ((32#32).setWidth 8) = asciiSpace := rfl
  have hm3' : (region (p + BitVec.ofNat 64 6 + BitVec.ofNat 64 bs_mv.length +
        (1 : BitVec 64) + BitVec.ofNat 64 bs_nc.length) 1 ⋆
      (bytes p dimacsHeaderPrefix ⋆ bytes (p + BitVec.ofNat 64 6) bs_mv ⋆
        bytes (p + BitVec.ofNat 64 6 + BitVec.ofNat 64 bs_mv.length) [asciiSpace] ⋆
        bytes (p + BitVec.ofNat 64 6 + BitVec.ofNat 64 bs_mv.length + (1 : BitVec 64)) bs_nc ⋆
        R)) m3 := by
    change (bytes (p + BitVec.ofNat 64 6 + BitVec.ofNat 64 bs_mv.length + (1 : BitVec 64)) bs_nc ⋆
      (region (p + BitVec.ofNat 64 6 + BitVec.ofNat 64 bs_mv.length + (1 : BitVec 64) +
          BitVec.ofNat 64 bs_nc.length) 1 ⋆
        (bytes p dimacsHeaderPrefix ⋆ bytes (p + BitVec.ofNat 64 6) bs_mv ⋆
          bytes (p + BitVec.ofNat 64 6 + BitVec.ofNat 64 bs_mv.length) [asciiSpace] ⋆ R))) m3 at hm3
    exact sep_ac hm3
  refine head_wp_store rfl (by dsimp [bs_mv, bs_nc]) (store_region_one _ hm3')
    (fun m_fin hm_fin => ?_)
  c0_hstraight
  have hfin : (bytes p (dimacsHeaderPrefix ++ bs_mv ++ [asciiSpace] ++ bs_nc ++
      [asciiNewline]) ⋆ R) m_fin := by
    have ha1 : (bytes p dimacsHeaderPrefix ⋆ bytes (p + BitVec.ofNat 64 6) bs_mv) =
        bytes p (dimacsHeaderPrefix ++ bs_mv) :=
      bytes_append_merge (by simp [dimacsHeaderPrefix]; omega)
    have h6mv : (dimacsHeaderPrefix ++ bs_mv).length = 6 + bs_mv.length := by
      simp [dimacsHeaderPrefix]; omega
    have ha2 : (bytes p (dimacsHeaderPrefix ++ bs_mv) ⋆
        bytes (p + BitVec.ofNat 64 6 + BitVec.ofNat 64 bs_mv.length) [asciiSpace]) =
        bytes p (dimacsHeaderPrefix ++ bs_mv ++ [asciiSpace]) := by
      rw [ptr_add_ofNat, ← h6mv]
      exact bytes_append_merge (by simp [dimacsHeaderPrefix]; omega)
    have h6mvs : (dimacsHeaderPrefix ++ bs_mv ++ [asciiSpace]).length =
        6 + bs_mv.length + 1 := by
      simp [dimacsHeaderPrefix]; omega
    have ha3 : (bytes p (dimacsHeaderPrefix ++ bs_mv ++ [asciiSpace]) ⋆
        bytes (p + BitVec.ofNat 64 6 + BitVec.ofNat 64 bs_mv.length + (1 : BitVec 64)) bs_nc) =
        bytes p (dimacsHeaderPrefix ++ bs_mv ++ [asciiSpace] ++ bs_nc) := by
      rw [ptr_add_ofNat, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ptr_add_ofNat,
        ← h6mvs]
      exact bytes_append_merge (by simp [dimacsHeaderPrefix]; omega)
    have h6mvsn : (dimacsHeaderPrefix ++ bs_mv ++ [asciiSpace] ++ bs_nc).length =
        6 + bs_mv.length + (1 + bs_nc.length) := by
      simp [dimacsHeaderPrefix]; omega
    have ha4 : (bytes p (dimacsHeaderPrefix ++ bs_mv ++ [asciiSpace] ++ bs_nc) ⋆
        bytes (p + BitVec.ofNat 64 6 + BitVec.ofNat 64 bs_mv.length + (1 : BitVec 64) +
            BitVec.ofNat 64 bs_nc.length) [asciiNewline]) =
        bytes p (dimacsHeaderPrefix ++ bs_mv ++ [asciiSpace] ++ bs_nc ++ [asciiNewline]) := by
      rw [ptr_add_ofNat, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ptr_add_ofNat,
        ptr_add_ofNat, ← h6mvsn]
      exact bytes_append_merge (by simp [dimacsHeaderPrefix]; omega)
    have hm_fin' : (bytes (p + BitVec.ofNat 64 6 + BitVec.ofNat 64 bs_mv.length +
            (1 : BitVec 64) + BitVec.ofNat 64 bs_nc.length) [asciiNewline] ⋆
        (bytes p dimacsHeaderPrefix ⋆ bytes (p + BitVec.ofNat 64 6) bs_mv ⋆
          bytes (p + BitVec.ofNat 64 6 + BitVec.ofNat 64 bs_mv.length) [asciiSpace] ⋆
          bytes (p + BitVec.ofNat 64 6 + BitVec.ofNat 64 bs_mv.length + (1 : BitVec 64)) bs_nc ⋆
          R)) m_fin := hm_fin
    have hsep : ((bytes p dimacsHeaderPrefix ⋆ bytes (p + BitVec.ofNat 64 6) bs_mv) ⋆
        bytes (p + BitVec.ofNat 64 6 + BitVec.ofNat 64 bs_mv.length) [asciiSpace] ⋆
        bytes (p + BitVec.ofNat 64 6 + BitVec.ofNat 64 bs_mv.length + (1 : BitVec 64)) bs_nc ⋆
        bytes (p + BitVec.ofNat 64 6 + BitVec.ofNat 64 bs_mv.length + (1 : BitVec 64) +
            BitVec.ofNat 64 bs_nc.length) [asciiNewline] ⋆ R) m_fin :=
      sep_ac hm_fin'
    rw [ha1, ha2, ha3, ha4] at hsep
    exact hsep
  have hp_fin : p + BitVec.ofNat 64 6 + BitVec.ofNat 64 bs_mv.length + 1 +
      BitVec.ofNat 64 bs_nc.length + 1 =
      p + BitVec.ofNat 64 (dimacsHeaderPrefix ++ bs_mv ++ [asciiSpace] ++ bs_nc ++
        [asciiNewline]).length := by
    rw [hlen_tot, ptr_add_ofNat, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl,
      ptr_add_ofNat, ptr_add_ofNat, ptr_add_ofNat]
    congr 2; omega
  change Q (p + BitVec.ofNat 64 6 + BitVec.ofNat 64 bs_mv.length + 1 +
      BitVec.ofNat 64 bs_nc.length + 1, ()) m_fin
  rw [hp_fin]
  exact hQ m_fin hfin

theorem bv_write_clause_end_wp (Γ : Env) :
    ∀ xs m Q X, bvWriteClauseEndSpec xs m Q X →
      Func.wp Γ bv_write_clause_end_body xs m Q X := by
  rintro ⟨p, ⟨⟩⟩ m Q X ⟨R, hfit, hm, hQ⟩
  have hm1 := region_split_prefix (a := p) (n1 := 1) (n2 := 1) (by decide) hm
  rw [show p + BitVec.ofNat 64 1 = p + (1 : BitVec 64) from rfl] at hm1
  c0_hsteps!; rw [Std.ExtHashMap.sep_emp] at hm
  have hmrg : (bytes p [UInt8.ofBitVec ((48#32).setWidth 8)] ⋆
      bytes (p + BitVec.ofNat 64 1) [UInt8.ofBitVec ((10#32).setWidth 8)] ⋆ R) m := sep_ac hm
  have h1 : (bytes p [48] ⋆ bytes (p + BitVec.ofNat 64 1) [10]) =
      bytes p [asciiZero, asciiNewline] := by
    simpa [List.length_singleton, asciiZero, asciiNewline] using
      bytes_append_merge (a := p) (b1 := [48]) (b2 := [10]) (by decide)
  rw [show p + (2 : BitVec 64) = p + BitVec.ofNat 64 2 from rfl]
  exact hQ m (by rw [← h1]; exact hmrg)

end

end LeanQbe.T.Examples.Bitblast.Proof
