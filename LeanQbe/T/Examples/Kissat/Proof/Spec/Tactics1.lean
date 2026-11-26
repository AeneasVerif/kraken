/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts4
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
public meta import Lean.Elab.Tactic
public meta import Lean.Meta.Tactic.Replace
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Fidelity BVE & BVA Heap Tactics / Scan Helpers (`Proof.Spec.Tactics1`)

1. `FidK6Tactics`, `fid_norm_ofnat`, `fid_ne`, `fid_omega`, `fid_call`, `fidScr*`.
2. `pack64` / `repr64Get` / `repr64Set` and `FullBvaHeapTactics`.
3. `FullBvaHeapScanHelpers` (`LmBit2Inv`, bit-mask restoration, `arViv_congr`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Spec

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.C0Step LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open Kraken.Bedrock2.Test

private meta def isCanonNatLit (e : Lean.Expr) : Bool :=
  if e.isAppOfArity ``OfNat.ofNat 3 then
    let inner := e.getArg! 1
    let inst := e.getArg! 2
    inner.isRawNatLit && inst.isAppOfArity ``instOfNatNat 1 && inst.getArg! 0 == inner
  else
    false

private meta def extractNestedNat? (e : Lean.Expr) : Option Nat := do
  guard (e.isAppOfArity ``OfNat.ofNat 3)
  guard ((e.getArg! 0).isConstOf ``Nat)
  guard (!isCanonNatLit e)
  let rec go : Nat → Lean.Expr → Option Nat
    | 0, _ => none
    | fuel + 1, x =>
      if let .lit (.natVal n) := x then some n
      else if x.isAppOfArity ``OfNat.ofNat 3 && (x.getArg! 0).isConstOf ``Nat then
        go fuel (x.getArg! 1)
      else none
  go 16 (e.getArg! 1)

private meta def normOfNatExpr (e : Lean.Expr) : Lean.Expr :=
  e.replace fun sub =>
    if let some n := extractNestedNat? sub then
      some (Lean.mkNatLit n)
    else
      none

/-- Normalize nested `OfNat.ofNat` numerals produced by C0 lowering across hypotheses
and the goal so `omega` and `rw` see canonical `Nat` literals. -/
scoped elab "fid_norm_ofnat" : tactic => Lean.Elab.Tactic.withMainContext do
  let mut g ← Lean.Elab.Tactic.getMainGoal
  let lctx ← g.withContext Lean.getLCtx
  for ldecl in lctx do
    if !ldecl.isImplementationDetail then
      let ty ← Lean.instantiateMVars ldecl.type
      let ty' := normOfNatExpr ty
      if ty' != ty then
        g ← g.replaceLocalDeclDefEq ldecl.fvarId ty'
  let tgt ← Lean.instantiateMVars (← g.getType)
  let tgt' := normOfNatExpr tgt
  if tgt' != tgt then
    g ← g.replaceTargetDefEq tgt'
  Lean.Elab.Tactic.replaceMainGoal [g]

namespace FidK6Tactics

@[scoped bv_c0] theorem fid_nat_xor1 (n : Nat) : n ^^^ 1 = n + 1 - 2 * (n % 2) := by
  have h := litNeg_eq n
  unfold litNeg at h
  rw [h]
  split <;> omega

@[scoped bv_c0] theorem fid_bv32_xor1_ofNat (x : BitVec 32) :
    (x ^^^ (1 : BitVec 32)).toNat = x.toNat + 1 - 2 * (x.toNat % 2) := by
  rw [bv32_xor_1]
  exact fid_nat_xor1 x.toNat

@[scoped bv_c0] theorem fid_bv32_xor1_lit (x : BitVec 32) :
    (x ^^^ 1#32).toNat = x.toNat + 1 - 2 * (x.toNat % 2) := by
  have h1 : (1#32 : BitVec 32) = (1 : BitVec 32) := rfl
  rw [h1]
  exact fid_bv32_xor1_ofNat x

@[scoped bv_c0] theorem fid_bv32_shr1_ofNat (x : BitVec 32) :
    (x >>> (1 : BitVec 32)).toNat = x.toNat / 2 := bv32_lshr_1 x

attribute [scoped bv_c0] bv32_lshr_1

@[scoped bv_c0] theorem fid_bv32_shl_nat (x : BitVec 32) (k : Nat) :
    (x <<< k).toNat = (x.toNat * 2 ^ k) % 2 ^ 32 := by
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]

@[scoped bv_c0] theorem fid_bv32_and_ffff_toNat (x : BitVec 32) :
    (x &&& 0xFFFF#32).toNat = x.toNat % 65536 := by
  rw [BitVec.toNat_and, show (0xFFFF#32 : BitVec 32).toNat = 2 ^ 16 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]

@[scoped bv_c0] theorem fid_bv32_and_ffff_ofNat_toNat (x : BitVec 32) :
    (x &&& (0xFFFF : BitVec 32)).toNat = x.toNat % 65536 :=
  fid_bv32_and_ffff_toNat x

@[scoped bv_c0] theorem fid_bv32_and_litMask_toNat (x : BitVec 32) :
    (x &&& (0x7FFFFFFF : BitVec 32)).toNat = x.toNat % 2 ^ 31 := by
  rw [BitVec.toNat_and, show (0x7FFFFFFF : BitVec 32).toNat = 2 ^ 31 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]

end FidK6Tactics

theorem fid_pow2_2 : (2 : Nat) ^ (@OfNat.ofNat Nat 2 _) = 4 := rfl

/-- Robust side-goal closer for `List.getElem?_set_ne` with nested-numeral C0 addresses. -/
scoped macro "fid_ne" : tactic => `(tactic| (
  try fid_norm_ofnat
  first
  | omega
  | (simp (disch := omega) only [bv_c0, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv,
       BitVec.reduceToNat, Nat.mod_eq_of_lt]
     try fid_norm_ofnat
     omega)))

/-- Normalizes C0 nested `OfNat` / `BitVec` address terms, then discharges by `omega`. -/
scoped macro "fid_omega" : tactic => `(tactic| (
  try fid_norm_ofnat
  first
  | omega
  | (simp (disch := omega) only [bv_c0, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv,
       BitVec.reduceToNat, Nat.mod_eq_of_lt]
     try fid_norm_ofnat
     omega)))

scoped macro "fid_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

theorem fidScr_lengthsOk {c : FullCfg} {s : FullState} {scr : List (BitVec 32)}
    (hlen : FullState.LengthsOk c s) (hscr : scr.length = c.scratch_cap) :
    FullState.LengthsOk c { s with scratch := { s.scratch with scratch_buf := scr } } :=
  ⟨hlen.core_ok, { hlen.scratch_ok with scratch_buf_len := hscr }⟩

theorem fidScrFuel_lengthsOk {c : FullCfg} {s : FullState} {fl : BitVec 64}
    {scr : List (BitVec 32)}
    (hlen : FullState.LengthsOk c s) (hscr : scr.length = c.scratch_cap) :
    FullState.LengthsOk c
      { core := { s.core with fuel := fl },
        scratch := { s.scratch with scratch_buf := scr } } :=
  ⟨{ hlen.core_ok with arena_len_le := hlen.core_ok.arena_len_le },
    { hlen.scratch_ok with scratch_buf_len := hscr }⟩


/-! ## 2. `i64` Reinterpretation over `repr` & `FullBvaHeapTactics` (`c0_hfast`) -/

@[expose] def pack64 (lo hi : BitVec 32) : BitVec 64 :=
  lo.setWidth 64 ||| (hi.setWidth 64 <<< 32)

@[expose] def repr64Get (r : List (BitVec 32)) (i : Nat) : BitVec 64 :=
  pack64 (r[2 * i]?.getD 0#32) (r[2 * i + 1]?.getD 0#32)

@[expose] def repr64Set (r : List (BitVec 32)) (i : Nat) (v : BitVec 64) : List (BitVec 32) :=
  (r.set (2 * i) (v.setWidth 32)).set (2 * i + 1) ((v >>> 32).setWidth 32)

theorem repr64Set_length (r : List (BitVec 32)) (i : Nat) (v : BitVec 64) :
    (repr64Set r i v).length = r.length := by
  simp [repr64Set]

private theorem toBytes_append_nat (a b n : Nat) :
    Int.toBytes (a + b) (n : Int) =
      Int.toBytes a (n : Int) ++ Int.toBytes b ((n / 256 ^ a : Nat) : Int) := by
  induction a generalizing n with
  | zero => simp [Int.toBytes]
  | succ a ih =>
    rw [Nat.succ_add, Int.toBytes, Int.toBytes, List.cons_append]
    congr 1
    have h1 : (n : Int) / 256 = ((n / 256 : Nat) : Int) := by omega
    rw [h1, ih (n / 256), Nat.div_div_eq_div_mul, Nat.mul_comm 256, ← Nat.pow_succ]

private theorem toBytes8_eq_append (v : BitVec 64) :
    Int.toBytes 8 v.toInt =
      Int.toBytes 4 (v.setWidth 32).toInt ++ Int.toBytes 4 ((v >>> 32).setWidth 32).toInt := by
  have h0 (n : Nat) (x : Int) : Int.toBytes n x = Int.toBytes n (x % (2 ^ (8 * n) : Int)) :=
    (Int.toBytes_emod n x).symm
  have hnat (n : Nat) (b : BitVec (8 * n)) :
      Int.toBytes n b.toInt = Int.toBytes n (b.toNat : Int) := by
    rw [h0, h0 n (b.toNat : Int)]
    congr 1
    rw [BitVec.toInt_eq_msb_cond]
    have ha : 0 ≤ (b.toNat : Int) ∧ (b.toNat : Int) < (2 ^ (8 * n) : Int) :=
      ⟨Int.natCast_nonneg _, by exact_mod_cast b.isLt⟩
    cases b.msb
    · simp [Int.emod_eq_of_lt ha.1 ha.2]
    · simp only [↓reduceIte]
      have hpow : (2 : Int) ^ (8 * n) = ((2 ^ (8 * n) : Nat) : Int) := by push_cast; rfl
      rw [← hpow, Int.sub_emod_right, Int.emod_eq_of_lt ha.1 ha.2]
  rw [hnat 8 v, hnat 4 (v.setWidth 32), hnat 4 ((v >>> 32).setWidth 32)]
  have hlo : ((v.setWidth 32).toNat : Int) = (v.toNat : Int) % 2 ^ 32 := by
    rw [BitVec.toNat_setWidth]; exact_mod_cast rfl
  have hhi : (((v >>> 32).setWidth 32).toNat : Int) = ((v.toNat / 2 ^ 32 : Nat) : Int) := by
    rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    have hlt : v.toNat / 2 ^ 32 < 2 ^ 32 := by have := v.isLt; omega
    rw [Nat.mod_eq_of_lt hlt]
  rw [hlo, hhi, Int.toBytes_emod 4 (v.toNat : Int)]
  exact toBytes_append_nat 4 4 v.toNat

private theorem nat_or_mul_two_pow32 {a b : Nat} (ha : a < 2 ^ 32) :
    a ||| (b * 2 ^ 32) = a + b * 2 ^ 32 := by
  apply Nat.eq_of_testBit_eq; intro k
  rw [Nat.testBit_or]
  by_cases hk : k < 32
  · have h0 : Nat.testBit (b * 2 ^ 32) k = false := by
      rw [Nat.mul_comm, Nat.testBit_two_pow_mul]; simp [Nat.not_le.mpr hk]
    have hpow : 2 ^ 32 = 2 ^ k * 2 ^ (32 - k) := by
      rw [← Nat.pow_add, Nat.add_sub_cancel' (by omega)]
    have hdiv : (a + b * 2 ^ 32) / 2 ^ k = a / 2 ^ k + b * 2 ^ (32 - k) := by
      rw [hpow, ← Nat.mul_assoc, Nat.mul_comm b (2 ^ k), Nat.mul_assoc,
        Nat.add_mul_div_left _ _ (Nat.two_pow_pos k)]
    have heven : 2 ∣ 2 ^ (32 - k) := by
      obtain ⟨m, hm⟩ : ∃ m, 32 - k = m + 1 := ⟨31 - k, by omega⟩
      rw [hm, Nat.pow_succ]; exact Nat.dvd_mul_left 2 _
    obtain ⟨q, hq⟩ := heven
    rw [h0, Bool.or_false, Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq,
      hdiv, hq, Nat.mul_comm 2 q, ← Nat.mul_assoc, Nat.add_mul_mod_self_right]
  · have h0 : Nat.testBit a k = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) (by omega)))
    have hhi' : Nat.testBit (b * 2 ^ 32) k = Nat.testBit b (k - 32) := by
      rw [Nat.mul_comm, Nat.testBit_two_pow_mul]; simp [Nat.le_of_not_lt hk]
    have hpow : 2 ^ k = 2 ^ 32 * 2 ^ (k - 32) := by
      rw [← Nat.pow_add, Nat.add_sub_cancel' (by omega)]
    have hdiv : (a + b * 2 ^ 32) / 2 ^ k = b / 2 ^ (k - 32) := by
      rw [hpow, ← Nat.div_div_eq_div_mul, Nat.add_mul_div_right _ _ (by decide),
        Nat.div_eq_of_lt ha, Nat.zero_add]
    rw [h0, hhi', Bool.false_or, Nat.testBit_eq_decide_div_mod_eq,
      Nat.testBit_eq_decide_div_mod_eq, hdiv]

private theorem pack64_lo (lo hi : BitVec 32) : (pack64 lo hi).setWidth 32 = lo := by
  unfold pack64; apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_or, BitVec.toNat_shiftLeft]
  have h1 : lo.toNat < 2 ^ 32 := lo.isLt
  have h2 : hi.toNat < 2 ^ 32 := hi.isLt
  rw [Nat.mod_eq_of_lt (by omega : lo.toNat < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : hi.toNat < 2 ^ 64), Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (by omega : hi.toNat * 2 ^ 32 < 2 ^ 64),
    nat_or_mul_two_pow32 h1, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h1]

private theorem pack64_hi (lo hi : BitVec 32) : ((pack64 lo hi) >>> 32).setWidth 32 = hi := by
  unfold pack64; apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_or,
    BitVec.toNat_shiftLeft, Nat.shiftRight_eq_div_pow]
  have h1 : lo.toNat < 2 ^ 32 := lo.isLt
  have h2 : hi.toNat < 2 ^ 32 := hi.isLt
  rw [Nat.mod_eq_of_lt (by omega : lo.toNat < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : hi.toNat < 2 ^ 64), Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (by omega : hi.toNat * 2 ^ 32 < 2 ^ 64),
    nat_or_mul_two_pow32 h1, Nat.add_mul_div_right _ _ (by decide), Nat.div_eq_of_lt h1,
    Nat.zero_add, Nat.mod_eq_of_lt h2]

private theorem cell64_eq_cell32_sep (a : BitVec 64) (v : BitVec 64) :
    cell64 a v =
      (cell (t := i32) a (v.setWidth 32) ⋆ cell (t := i32) (a + 4) ((v >>> 32).setWidth 32)) := by
  unfold cell64 cell
  simp only [Ty.bytes, Ty.size, i32, toBits, BitVec.setWidth_eq]
  rw [toBytes8_eq_append v]
  exact Mem.At_append_sep _ _ a (by simp [Int.toBytes_length])

private theorem cell32_sep_eq_cell64 (a : BitVec 64) (lo hi : BitVec 32) :
    (cell (t := i32) a lo ⋆ cell (t := i32) (a + 4) hi) = cell64 a (pack64 lo hi) := by
  rw [cell64_eq_cell32_sep a (pack64 lo hi), pack64_lo, pack64_hi]

private theorem array32_focus_pair (a : BitVec 64) (xs : List (BitVec 32)) {i : Nat}
    (hi : 2 * i + 1 < xs.length) :
    array (t := i32) a xs =
      (cell64 (a + BitVec.ofNat 64 (8 * i)) (repr64Get xs i) ⋆
        (array (t := i32) a (xs.take (2 * i)) ⋆
          array (t := i32) (a + BitVec.ofNat 64 (8 * i) + 8) (xs.drop (2 * i + 2)))) := by
  have h1 : 2 * i < xs.length := by omega
  have hdrop : xs.drop (2 * i) = xs[2 * i] :: xs[2 * i + 1] :: xs.drop (2 * i + 2) := by
    rw [List.drop_eq_getElem_cons h1, List.drop_eq_getElem_cons hi]
  conv => lhs; rw [← List.take_append_drop (2 * i) xs, hdrop]
  rw [array_append, array_cons, array_cons, List.length_take_of_le (Nat.le_of_lt h1)]
  have h42 : (i32.bytes * (2 * i)) = 8 * i := by simp [Ty.bytes, Ty.size]; omega
  have h4 : BitVec.ofNat 64 i32.bytes = 4 := rfl
  have h44 : a + BitVec.ofNat 64 (8 * i) + 4 + 4 = a + BitVec.ofNat 64 (8 * i) + 8 := by
    bv_omega
  rw [h42, h4, h44]
  have hget : repr64Get xs i = pack64 xs[2 * i] xs[2 * i + 1] := by
    unfold repr64Get
    rw [List.getElem?_eq_getElem h1, List.getElem?_eq_getElem hi, Option.getD_some,
      Option.getD_some]
  rw [hget, ← sep_assoc (cell (a + BitVec.ofNat 64 (8 * i)) _), cell32_sep_eq_cell64,
    ← sep_assoc, sep_comm (array a _), sep_assoc]

private theorem array32_set_pair (a : BitVec 64) (xs : List (BitVec 32)) {i : Nat}
    (hi : 2 * i + 1 < xs.length) (v : BitVec 64) :
    array (t := i32) a (repr64Set xs i v) =
      (cell64 (a + BitVec.ofNat 64 (8 * i)) v ⋆
        (array (t := i32) a (xs.take (2 * i)) ⋆
          array (t := i32) (a + BitVec.ofNat 64 (8 * i) + 8) (xs.drop (2 * i + 2)))) := by
  have h1 : 2 * i < xs.length := by omega
  have hlen : (repr64Set xs i v).length = xs.length := repr64Set_length xs i v
  have htake : (repr64Set xs i v).take (2 * i) = xs.take (2 * i) := by
    unfold repr64Set
    rw [List.take_set_of_le (by omega), List.take_set_of_le (Nat.le_refl _)]
  have hdrop : (repr64Set xs i v).drop (2 * i + 2) = xs.drop (2 * i + 2) := by
    unfold repr64Set
    rw [List.drop_set_of_lt (by omega), List.drop_set_of_lt (by omega)]
  have hget : repr64Get (repr64Set xs i v) i = v := by
    unfold repr64Get repr64Set
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_self h1,
      List.getElem?_set_self (by simp [hi]), Option.getD_some, Option.getD_some]
    unfold pack64
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_or, BitVec.toNat_setWidth, BitVec.toNat_shiftLeft,
      BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
    have hv := v.isLt
    rw [Nat.mod_eq_of_lt (by omega : v.toNat % 2 ^ 32 < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : v.toNat / 2 ^ 32 < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega : v.toNat / 2 ^ 32 < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : (v.toNat / 2 ^ 32) * 2 ^ 32 < 2 ^ 64),
      nat_or_mul_two_pow32 (Nat.mod_lt _ (by decide))]
    omega
  rw [array32_focus_pair a (repr64Set xs i v) (by rw [hlen]; exact hi), hget, htake, hdrop]

namespace FullBvaHeapTactics

open FullArenaTactics
open scoped FullArenaTactics

private def reprRest (c : FullCfg) (s : FullState) (R : Mem 64 → Prop) : Mem 64 → Prop :=
  (array (t := i32) c.pFrameTrail s.core.frame_trail ⋆
    array (t := i32) c.pFrameDec s.core.frame_dec ⋆
    array (t := i32) c.pWvec s.core.wvec ⋆ array (t := i32) c.pMinStk s.core.min_stk ⋆
    (FullCoreByteArrs c s.core ⋆ FullCoreU32A c s.core ⋆ FullCoreDynArrs c s.core ⋆
      fullCoreOuter c s)) ⋆ R

@[scoped c0_load] theorem load_full_repr64 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} {i : Nat} (hi : 2 * i + 1 < s.core.repr.length) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i64 (c.pRepr + BitVec.ofNat 64 (8 * i)) = some (repr64Get s.core.repr i) := by
  rw [fullMem_eq_coreU32B] at hm; unfold FullCoreU32B at hm
  have h1 : (array (t := i32) c.pRepr s.core.repr ⋆ reprRest c s R) m := by
    unfold reprRest; ecancel
  rw [array32_focus_pair c.pRepr s.core.repr hi, sep_assoc] at h1
  exact loadVal_cell64 h1

@[scoped c0_load] theorem c0_load_full_repr64 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} {i : BitVec 64} (hi : 2 * i.toNat + 1 < s.core.repr.length)
    (hm : (FullMem c s ⋆ R) m) :
    loadVal m i64 (c.pRepr + i * 8) = some (repr64Get s.core.repr i.toNat) := by
  rw [m8]; exact load_full_repr64 hi hm

@[scoped c0_store] theorem store_full_repr64 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} {i : Nat} (v : BitVec 64) (hi : 2 * i + 1 < s.core.repr.length)
    (hm : (FullMem c s ⋆ R) m) :
    storeOk m i64 (c.pRepr + BitVec.ofNat 64 (8 * i)) ∧
      (FullMem c { s with core := { s.core with repr := repr64Set s.core.repr i v } } ⋆ R)
        (storeMem m i64 (c.pRepr + BitVec.ofNat 64 (8 * i)) v) := by
  have h1 := hm; rw [fullMem_eq_coreU32B] at h1; unfold FullCoreU32B at h1
  have h2 : (array (t := i32) c.pRepr s.core.repr ⋆ reprRest c s R) m := by
    unfold reprRest; ecancel
  rw [array32_focus_pair c.pRepr s.core.repr hi, sep_assoc] at h2
  obtain ⟨hok, hst⟩ := store_cell64 v h2
  rw [← sep_assoc, ← array32_set_pair c.pRepr s.core.repr hi v] at hst
  exact ⟨hok, ufM (fullMem_eq_coreU32B c s) (fullMem_eq_coreU32B c _) rfl
    (by unfold FullCoreU32B; unfold reprRest at hst; dsimp only; ecancel)⟩

@[scoped c0_store] theorem c0_store_full_repr64 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} {i : BitVec 64} (v : BitVec 64) (hi : 2 * i.toNat + 1 < s.core.repr.length)
    (hm : (FullMem c s ⋆ R) m) :
    storeOk m i64 (c.pRepr + i * 8) ∧
      (FullMem c { s with core := { s.core with repr := repr64Set s.core.repr i.toNat v } } ⋆ R)
        (storeMem m i64 (c.pRepr + i * 8) v) := by
  rw [m8]; exact store_full_repr64 v hi hm

@[scoped c0_load] theorem load_full_scratch_buf0 {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hi : 0 < s.scratch.scratch_buf.length)
    (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 c.pScratchBuf = some s.scratch.scratch_buf[0] := by
  simpa using load_full_scratch_buf (i := 0) hi hm

@[scoped c0_store] theorem store_full_scratch_buf0 {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) (hi : 0 < s.scratch.scratch_buf.length)
    (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 c.pScratchBuf ∧
      (FullMem c { s with scratch :=
        { s.scratch with scratch_buf := s.scratch.scratch_buf.set 0 v } } ⋆ R)
        (storeMem m i32 c.pScratchBuf v) := by
  simpa using store_full_scratch_buf (i := 0) v hi hm

@[scoped c0_load] theorem load_full_scratch_buf_imm {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {d : Nat} (hd : d % 4 = 0) (hd64 : d < 2 ^ 64)
    (hi : d / 4 < s.scratch.scratch_buf.length) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 (c.pScratchBuf + BitVec.ofNat 64 d) = some s.scratch.scratch_buf[d / 4] := by
  have heq : BitVec.ofNat 64 d = BitVec.ofNat 64 (4 * (d / 4)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd64,
      Nat.mod_eq_of_lt (by omega)]; omega
  rw [heq]; exact load_full_scratch_buf hi hm

@[scoped c0_store] theorem store_full_scratch_buf_imm {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {d : Nat} (v : BitVec 32) (hd : d % 4 = 0)
    (hd64 : d < 2 ^ 64) (hi : d / 4 < s.scratch.scratch_buf.length) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 (c.pScratchBuf + BitVec.ofNat 64 d) ∧
      (FullMem c { s with scratch :=
        { s.scratch with scratch_buf := s.scratch.scratch_buf.set (d / 4) v } } ⋆ R)
        (storeMem m i32 (c.pScratchBuf + BitVec.ofNat 64 d) v) := by
  have heq : BitVec.ofNat 64 d = BitVec.ofNat 64 (4 * (d / 4)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd64,
      Nat.mod_eq_of_lt (by omega)]; omega
  rw [heq]; exact store_full_scratch_buf v hi hm

@[scoped c0_load] theorem load_full_tmp0 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} (hi : 0 < s.core.tmp.length) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 c.pTmp = some s.core.tmp[0] := by
  simpa using load_full_tmp (i := 0) hi hm

@[scoped c0_store] theorem store_full_tmp0 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} (v : BitVec 32) (hi : 0 < s.core.tmp.length) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 c.pTmp ∧
      (FullMem c { s with core := { s.core with tmp := s.core.tmp.set 0 v } } ⋆ R)
        (storeMem m i32 c.pTmp v) := by
  simpa using store_full_tmp (i := 0) v hi hm

@[scoped c0_load] theorem load_full_tarjan_mark0 {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hi : 0 < s.scratch.tarjan_mark.length)
    (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 c.pTarjanMark = some s.scratch.tarjan_mark[0] := by
  simpa using load_full_tarjan_mark (i := 0) hi hm

@[scoped c0_store] theorem store_full_tarjan_mark0 {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) (hi : 0 < s.scratch.tarjan_mark.length)
    (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 c.pTarjanMark ∧
      (FullMem c { s with scratch :=
        { s.scratch with tarjan_mark := s.scratch.tarjan_mark.set 0 v } } ⋆ R)
        (storeMem m i32 c.pTarjanMark v) := by
  simpa using store_full_tarjan_mark (i := 0) v hi hm

attribute [scoped bv_c0] bv32_lshr_1 FidK6Tactics.fid_bv32_shr1_ofNat repr64Set_length

@[scoped bv_c0] theorem bv64_lshr1_nat (x : BitVec 64) : (x >>> (1 : Nat)).toNat = x.toNat / 2 := by
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

@[scoped bv_c0] theorem bv64_lshr1_bv (x : BitVec 64) :
    (x >>> (1 : BitVec 64)).toNat = x.toNat / 2 := by
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

@[scoped bv_c0] theorem bv32_shl1_nat (x : BitVec 32) :
    (x <<< (1 : Nat)).toNat = (2 * x.toNat) % 2 ^ 32 := by
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm]

@[scoped bv_c0] theorem bv32_shl1_bv (x : BitVec 32) :
    (x <<< (1 : BitVec 32)).toNat = (2 * x.toNat) % 2 ^ 32 := by
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm]

@[scoped bv_c0] theorem bv64_shl1_bv (x : BitVec 64) :
    (x <<< (1 : BitVec 64)).toNat = (2 * x.toNat) % 2 ^ 64 := by
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm]

@[scoped bv_c0] theorem bv64_shl2_nat (x : BitVec 64) :
    (x <<< (2 : Nat)).toNat = (4 * x.toNat) % 2 ^ 64 := by
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm]

@[scoped bv_c0] theorem bv64_shl2_bv (x : BitVec 64) :
    (x <<< (2 : BitVec 64)).toNat = (4 * x.toNat) % 2 ^ 64 := by
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm]

@[scoped bv_c0] theorem bv64_setWidth_32 (x : BitVec 32) :
    (BitVec.setWidth 64 x).toNat = x.toNat := by
  simp [BitVec.toNat_setWidth]; have := x.isLt; omega

@[scoped bv_c0] theorem bv32_lshr1_shl1_or_lt2 {x y : BitVec 32} (hy : y.toNat < 2) :
    (((x >>> (1 : Nat)) <<< (1 : Nat)) ||| y).toNat = 2 * (x.toNat / 2) + y.toNat := by
  have hlt : 2 * (x.toNat / 2) < 2 ^ 32 := by have := x.isLt; omega
  have hev : ((x >>> (1 : Nat)) <<< (1 : Nat)).toNat = 2 * (x.toNat / 2) := by
    rw [bv32_shl1_nat, bv32_lshr_1, Nat.mod_eq_of_lt hlt]
  rcases (by omega : y.toNat = 0 ∨ y.toNat = 1) with h0 | h1
  · have hy0 : y = 0#32 := BitVec.eq_of_toNat_eq h0; subst hy0
    rw [BitVec.or_zero, hev]; rfl
  · have hy1 : y = 1#32 := BitVec.eq_of_toNat_eq h1; subst hy1
    rw [FullBvaFwdTactics.bv32_or1_of_even (by omega), hev]; rfl

end FullBvaHeapTactics

open FullBvaHeapTactics FullBvaHeapHelpers
open scoped FullArenaTactics FullBvaHeapTactics

/-! ## 1. Pure Bit-Mask & Exact-Restoration Helpers -/

namespace FullBvaHeapScanHelpers

theorem bv32_garb_zero_of_and_580000 {x : BitVec 32} (h : (x &&& 0x00580000#32) = 0#32) :
    (x &&& 0x00080000#32) = 0#32 := by
  have h1 := congrArg (· &&& 0x00080000#32) h
  rw [BitVec.and_assoc, show (0x00580000#32 &&& 0x00080000#32) = 0x00080000#32 from rfl,
    BitVec.zero_and] at h1
  exact h1

theorem bv32_viv_zero_of_and_580000 {x : BitVec 32} (h : (x &&& 0x00580000#32) = 0#32) :
    (x &&& 0x00100000#32) = 0#32 := by
  have h1 := congrArg (· &&& 0x00100000#32) h
  rw [BitVec.and_assoc, show (0x00580000#32 &&& 0x00100000#32) = 0x00100000#32 from rfl,
    BitVec.zero_and] at h1
  exact h1

theorem bv8_bit_zero_of_and_fe {x : BitVec 8} (h : (x &&& 0xFE#8) = 0#8) :
    (x &&& 2#8) = 0#8 ∧ (x &&& 4#8) = 0#8 := by
  constructor
  · have h1 := congrArg (· &&& 2#8) h
    rw [BitVec.and_assoc, show (0xFE#8 &&& 2#8) = 2#8 from rfl, BitVec.zero_and] at h1; exact h1
  · have h1 := congrArg (· &&& 4#8) h
    rw [BitVec.and_assoc, show (0xFE#8 &&& 4#8) = 4#8 from rfl, BitVec.zero_and] at h1; exact h1

theorem bv8_clear_bit1_of_zero {x : BitVec 8} (hx : (x &&& 2#8) = 0#8) :
    (x &&& 0xFD#8) = x := by
  have h1 : x = x &&& (0xFD#8 ||| 2#8) := by
    rw [show (0xFD#8 ||| 2#8) = BitVec.allOnes 8 from rfl, BitVec.and_allOnes]
  conv => rhs; rw [h1, BitVec.and_or_distrib_left, hx, BitVec.or_zero]

theorem bv8_clear_bit2_of_zero {x : BitVec 8} (hx : (x &&& 4#8) = 0#8) :
    (x &&& 0xFB#8) = x := by
  have h1 : x = x &&& (0xFB#8 ||| 4#8) := by
    rw [show (0xFB#8 ||| 4#8) = BitVec.allOnes 8 from rfl, BitVec.and_allOnes]
  conv => rhs; rw [h1, BitVec.and_or_distrib_left, hx, BitVec.or_zero]

theorem bv8_clear_bit1_eq_of_or2 {x y : BitVec 8} (hx : (x &&& 2#8) = 0#8)
    (hy : y = x ∨ y = (x ||| 2#8)) : (y &&& 0xFD#8) = x := by
  rcases hy with rfl | rfl
  · exact bv8_clear_bit1_of_zero hx
  · rw [BitVec.and_or_distrib_right, show (2#8 &&& 0xFD#8) = 0#8 from rfl, BitVec.or_zero]
    exact bv8_clear_bit1_of_zero hx

theorem bv8_clear_bit2_eq_of_or4 {x y : BitVec 8} (hx : (x &&& 4#8) = 0#8)
    (hy : y = x ∨ y = (x ||| 4#8)) : (y &&& 0xFB#8) = x := by
  rcases hy with rfl | rfl
  · exact bv8_clear_bit2_of_zero hx
  · rw [BitVec.and_or_distrib_right, show (4#8 &&& 0xFB#8) = 0#8 from rfl, BitVec.or_zero]
    exact bv8_clear_bit2_of_zero hx

theorem bv8_or2_and_bit2 (x : BitVec 8) : ((x ||| 2#8) &&& 4#8) = (x &&& 4#8) := by
  rw [BitVec.and_or_distrib_right, show (2#8 &&& 4#8) = 0#8 from rfl, BitVec.or_zero]

theorem bv8_or2_and_bit0 (x : BitVec 8) : ((x ||| 2#8) &&& 1#8) = (x &&& 1#8) := by
  rw [BitVec.and_or_distrib_right, show (2#8 &&& 1#8) = 0#8 from rfl, BitVec.or_zero]

theorem bv8_or4_and_bit1 (x : BitVec 8) : ((x ||| 4#8) &&& 2#8) = (x &&& 2#8) := by
  rw [BitVec.and_or_distrib_right, show (4#8 &&& 2#8) = 0#8 from rfl, BitVec.or_zero]

theorem bv8_or2_idem (x : BitVec 8) : ((x ||| 2#8) ||| 2#8) = (x ||| 2#8) := by
  rw [BitVec.or_assoc, show (2#8 ||| 2#8) = 2#8 from rfl]

theorem bv8_or4_idem (x : BitVec 8) : ((x ||| 4#8) ||| 4#8) = (x ||| 4#8) := by
  rw [BitVec.or_assoc, show (4#8 ||| 4#8) = 4#8 from rfl]

theorem bv32_clear_viv_of_zero {x : BitVec 32} (hx : (x &&& 0x00100000#32) = 0#32) :
    (x &&& ~~~0x00100000#32) = x := by
  have h1 : x = x &&& (~~~0x00100000#32 ||| 0x00100000#32) := by
    rw [show (~~~0x00100000#32 ||| 0x00100000#32) = BitVec.allOnes 32 from rfl, BitVec.and_allOnes]
  conv => rhs; rw [h1, BitVec.and_or_distrib_left, hx, BitVec.or_zero]

theorem bv32_clear_viv_eq_of_or {x y : BitVec 32} (hx : (x &&& 0x00100000#32) = 0#32)
    (hy : y = x ∨ y = (x ||| 0x00100000#32)) : (y &&& ~~~0x00100000#32) = x := by
  rcases hy with rfl | rfl
  · exact bv32_clear_viv_of_zero hx
  · exact bv32_viv_roundtrip hx

theorem bv32_or_viv_idem (x : BitVec 32) :
    ((x ||| 0x00100000#32) ||| 0x00100000#32) = (x ||| 0x00100000#32) := by
  rw [BitVec.or_assoc, show (0x00100000#32 ||| 0x00100000#32) = 0x00100000#32 from rfl]

theorem bv32_and_not_viv_eq (x : BitVec 32) :
    (x &&& (0x00100000#32 ^^^ 0xFFFFFFFF#32)) = (x &&& ~~~0x00100000#32) := rfl

theorem list_eq_of_getElem?_eq {α : Type _} {xs ys : List α} (hlen : xs.length = ys.length)
    (h : ∀ i < ys.length, xs[i]? = ys[i]?) : xs = ys := by
  apply List.ext_getElem?; intro i
  by_cases hi : i < ys.length
  · exact h i hi
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

/-- Preserve `FullArenaVarsNodup` across bit-20 (`PH_VIV`) header updates. -/
theorem fullArenaVarsNodup_of_bit20 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {cref : Nat} {v : BitVec 32} (hlen : s.core.LengthsOk c)
    (hw : FullWitnessInv c F0 F_cur s.core) (hl0 : s.core.cur_level = 0)
    (hnodup : FullArenaVarsNodup s) (href : cref ∈ fullArenaClauseRefsCore s.core)
    (h19 : (v &&& 0x00080000#32) = (fullArenaHdrCore s.core cref &&& 0x00080000#32))
    (h23 : (v &&& 0x00800000#32) = (fullArenaHdrCore s.core cref &&& 0x00800000#32)) :
    FullArenaVarsNodup { s with core := { s.core with arena := s.core.arena.set cref v } } := by
  have ⟨_, hrefs, _, hall⟩ := fullWitnessInv_set_hdr_bit20 hlen hw hl0 href v h19 h23
  intro r hr hng
  change r ∈ fullArenaClauseRefsCore { s.core with arena := s.core.arena.set cref v } at hr
  rw [hrefs] at hr
  have ⟨hgb, _, hlts⟩ := hall r hr
  change fullArenaClauseGarbCore { s.core with arena := s.core.arena.set cref v } r = false at hng
  rw [hgb] at hng
  change ((fullArenaClauseLitsCore { s.core with arena := s.core.arena.set cref v } r).map
    (· / 2)).Nodup
  rw [hlts]; exact hnodup r hr hng

theorem fullArenaClauseLitsCore_congr {k1 k2 : FullCoreState} {r : Nat}
    (hsz : fullArenaClauseSizeCore k2 r = fullArenaClauseSizeCore k1 r)
    (hlits : ∀ j < fullArenaClauseSizeCore k1 r, k2.arena[r + 3 + j]? = k1.arena[r + 3 + j]?) :
    fullArenaClauseLitsCore k2 r = fullArenaClauseLitsCore k1 r := by
  unfold fullArenaClauseLitsCore; rw [hsz]
  apply congrArg (List.map BitVec.toNat)
  apply List.ext_getElem?; intro j
  by_cases hj : j < fullArenaClauseSizeCore k1 r
  · simp only [List.getElem?_take_of_lt hj, List.getElem?_drop]; exact hlits j hj
  · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]

/-- Zero-AST-duplication HOAS `Expr` slicers for factoring inner loop `wp` sub-theorems. -/
@[expose] def eLet64 {rs : List Ty} (v : Val i64) : Expr Val Cont rs → Expr Val Cont rs
  | .let_ (ts := [.bits 64]) _ k => k (v, ()) | _ => .hlt

@[expose] def eLet32 {rs : List Ty} (v : Val i32) : Expr Val Cont rs → Expr Val Cont rs
  | .let_ (ts := [.bits 32]) _ k => k (v, ()) | _ => .hlt

@[expose] def eLetBool {rs : List Ty} (v : Val .bool) : Expr Val Cont rs → Expr Val Cont rs
  | .let_ (ts := [.bool]) _ k => k (v, ()) | _ => .hlt

@[expose] def eLoad64 {rs : List Ty} (v : Val i64) : Expr Val Cont rs → Expr Val Cont rs
  | .load (.bits 64) _ k => k v | _ => .hlt

@[expose] def eLoad32 {rs : List Ty} (v : Val i32) : Expr Val Cont rs → Expr Val Cont rs
  | .load (.bits 32) _ k => k v | _ => .hlt

@[expose] def eThen {rs : List Ty} : Expr Val Cont rs → Expr Val Cont rs
  | .jnz _ t _ => t | _ => .hlt

@[expose] def eElse {rs : List Ty} : Expr Val Cont rs → Expr Val Cont rs
  | .jnz _ _ e => e | _ => .hlt

@[expose] def eGrp0_3 {rs : List Ty} (J : Cont [i32, i32, i32]) (xs : Tup Val [i32, i32, i32]) :
    Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 32, .bits 32, .bits 32]]) bs _ =>
    match bs (J, ()) with | .cons f .nil => f xs
  | _ => .hlt

@[expose]
def eGrp0_4 {rs : List Ty} (J : Cont [i32, i32, i32, i32]) (xs : Tup Val [i32, i32, i32, i32]) :
    Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 32, .bits 32, .bits 32, .bits 32]]) bs _ =>
    match bs (J, ()) with | .cons f .nil => f xs
  | _ => .hlt

@[expose] def eGrpBody_2 {rs : List Ty} (J : Cont [i32, i32]) : Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 32, .bits 32]]) _ body => body (J, ()) | _ => .hlt

@[expose]
def eGrpBody_3 {rs : List Ty} (J : Cont [i32, i32, i32]) : Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 32, .bits 32, .bits 32]]) _ body => body (J, ()) | _ => .hlt

@[expose]
def eGrpBody_mp {rs : List Ty} (J : Cont [i32, i32, i64, i32]) : Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 32, .bits 32, .bits 64, .bits 32]]) _ body => body (J, ()) | _ => .hlt

@[expose]
def eGrp0_mp {rs : List Ty} (J : Cont [i32, i32, i64, i32]) (xs : Tup Val [i32, i32, i64, i32]) :
    Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 32, .bits 32, .bits 64, .bits 32]]) bs _ =>
    match bs (J, ()) with | .cons f .nil => f xs
  | _ => .hlt

@[expose]
def eGrp0_dj {rs : List Ty} (J : Cont [i32, .bool, i32]) (xs : Tup Val [i32, .bool, i32]) :
    Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 32, .bool, .bits 32]]) bs _ =>
    match bs (J, ()) with | .cons f .nil => f xs
  | _ => .hlt

@[expose] def eSkip {rs : List Ty} : Nat → Expr Val Cont rs → Expr Val Cont rs
  | 0, e => e
  | n + 1, .let_ (ts := [.bits 64]) _ k => eSkip n (k (0#64, ()))
  | n + 1, .let_ (ts := [.bits 32]) _ k => eSkip n (k (0#32, ()))
  | n + 1, .let_ (ts := [.bool]) _ k => eSkip n (k (true, ()))
  | n + 1, .load (.bits 64) _ k => eSkip n (k 0#64)
  | n + 1, .load (.bits 32) _ k => eSkip n (k 0#32)
  | _, e => e

end FullBvaHeapScanHelpers

open FullBvaHeapScanHelpers

theorem bv8_trunc_and_w (x y : BitVec 8) :
    BitVec.setWidth 8 (BitVec.setWidth 32 x &&& BitVec.setWidth 32 y) = x &&& y := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_and]
  have hx := x.isLt; have hy := y.isLt
  rw [Nat.mod_eq_of_lt (Nat.lt_trans hx (by decide)),
    Nat.mod_eq_of_lt (Nat.lt_trans hy (by decide)),
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt Nat.and_le_left hx)]

theorem bv8_trunc_or_w (x y : BitVec 8) :
    BitVec.setWidth 8 (BitVec.setWidth 32 x ||| BitVec.setWidth 32 y) = x ||| y := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_or]
  have hx := x.isLt; have hy := y.isLt
  rw [Nat.mod_eq_of_lt (Nat.lt_trans hx (by decide)),
    Nat.mod_eq_of_lt (Nat.lt_trans hy (by decide)),
    Nat.mod_eq_of_lt (Nat.or_lt_two_pow (n := 8) hx hy)]

theorem bv8_trunc_and_fb (x : BitVec 8) :
    BitVec.setWidth 8 (BitVec.setWidth 32 x &&&
      BitVec.ofNat (OfNat.ofNat 32) (OfNat.ofNat 251)) = x &&& 0xFB#8 :=
  bv8_trunc_and_w x 0xFB#8

theorem bv8_trunc_and_fd (x : BitVec 8) :
    BitVec.setWidth 8 (BitVec.setWidth 32 x &&&
      BitVec.ofNat (OfNat.ofNat 32) (OfNat.ofNat 253)) = x &&& 0xFD#8 :=
  bv8_trunc_and_w x 0xFD#8

theorem bv8_trunc_or_2 (x : BitVec 8) :
    BitVec.setWidth 8 (BitVec.setWidth 32 x |||
      BitVec.ofNat (OfNat.ofNat 32) (OfNat.ofNat 2)) = x ||| 2#8 :=
  bv8_trunc_or_w x 2#8

theorem bv8_trunc_or_4 (x : BitVec 8) :
    BitVec.setWidth 8 (BitVec.setWidth 32 x |||
      BitVec.ofNat (OfNat.ofNat 32) (OfNat.ofNat 4)) = x ||| 4#8 :=
  bv8_trunc_or_w x 4#8

theorem fullWitnessInv_with_litMark {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {k : FullCoreState} (h : FullWitnessInv c F0 F_cur k)
    (lm : List (BitVec 8)) : FullWitnessInv c F0 F_cur { k with lit_mark := lm } :=
  { h with arena := { h.arena with len_ok := h.arena.len_ok }
           watches := h.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }


theorem arViv_congr {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hcl : s.core.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core)
    {ar : List (BitVec 32)}
    (hpt : ∀ i < c.arena_cap, ar[i]? = s.core.arena[i]? ∨
      (i ∈ fullArenaClauseRefsCore s.core ∧
        ar[i]? = some (s.core.arena[i]?.getD 0#32 ||| 0x00100000#32))) :
    fullArenaClauseRefsCore { s.core with arena := ar } = fullArenaClauseRefsCore s.core ∧
    (∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaClauseGarbCore { s.core with arena := ar } r = fullArenaClauseGarbCore s.core r ∧
      fullArenaClauseSizeCore { s.core with arena := ar } r = fullArenaClauseSizeCore s.core r ∧
      fullArenaClauseLitsCore { s.core with arena := ar } r =
        fullArenaClauseLitsCore s.core r) := by
  have hal_le := hcl.arena_len_le
  have hgt_eq : ∀ r ∈ fullArenaClauseRefsCore s.core, ∀ i,
      r < i → i < fullArenaNextOff s.core.arena s.core.arena_len r →
      ar[i]? = s.core.arena[i]? := by
    intro r hr i hgt hlt
    have hwf := hw.arena.refs_wf r hr
    rcases hpt i (by omega) with heq | ⟨hi_ref, _⟩
    · exact heq
    · exfalso; have := fullArenaScanRefs_disjoint hr hi_ref hgt; omega
  have hnxt : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaNextOff ar s.core.arena_len r =
      fullArenaNextOff s.core.arena s.core.arena_len r := by
    intro r hr
    have hwf := hw.arena.refs_wf r hr
    have h2eq : ar[r + 2]? = s.core.arena[r + 2]? := hgt_eq r hr (r + 2) (by omega) (by omega)
    rcases hpt r (by omega) with heq | ⟨_, hset_r⟩
    · exact fullArenaNextOff_congr_block heq h2eq fun i hi1 hi2 => hgt_eq r hr i (by omega) hi2
    · have h1 : ¬ (r + 3 > s.core.arena_len) := by omega
      have h2 : ¬ (r + 3 + (s.core.arena[r + 2]?.getD 0#32).toNat > s.core.arena_len) := by
        unfold fullArenaClauseSizeCore at hwf; omega
      unfold fullArenaNextOff
      simp only [h1, ↓reduceIte, h2eq, h2, hset_r, Option.getD_some, bv32_or_viv_shrk]
      split
      · rename_i hshrk
        have hnxt_eq : fullArenaNextOff s.core.arena s.core.arena_len r =
            fullArenaSkipShrk s.core.arena s.core.arena_len
              (r + 3 + (s.core.arena[r + 2]?.getD 0#32).toNat)
              (s.core.arena_len - (r + 3 + (s.core.arena[r + 2]?.getD 0#32).toNat)) := by
          unfold fullArenaNextOff; simp only [h1, ↓reduceIte, h2]; rw [ite_eq_left hshrk]
        exact fullArenaSkipShrk_congr fun i hi1 hi2 =>
          hgt_eq r hr i (by omega) (by rw [hnxt_eq]; exact hi2)
      · rfl
  refine ⟨fullArenaClauseRefsCore_congr rfl hnxt, fun r hr => ?_⟩
  have hwf := hw.arena.refs_wf r hr
  have h2eq : ar[r + 2]? = s.core.arena[r + 2]? := hgt_eq r hr (r + 2) (by omega) (by omega)
  have hsz : fullArenaClauseSizeCore { s.core with arena := ar } r =
      fullArenaClauseSizeCore s.core r := by unfold fullArenaClauseSizeCore; rw [h2eq]
  refine ⟨?_, hsz, ?_⟩
  · unfold fullArenaClauseGarbCore fullArenaHdrCore
    rcases hpt r (by omega) with heq | ⟨_, hset_r⟩
    · rw [heq]
    · rw [hset_r, Option.getD_some, bv32_or_viv_garb]
  · exact fullArenaClauseLitsCore_congr hsz fun j hj =>
      hgt_eq r hr (r + 3 + j) (by omega) (by omega)


/-- Bit-2 `lit_mark` restoration invariant over literals `ar[qw + 3 + lo ..< qw + 3 + hi)`. -/
@[expose] def LmBit2Inv (c : FullCfg) (ar : List (BitVec 32)) (lm0 : List (BitVec 8))
    (qw lo hi : Nat) (lm : List (BitVec 8)) : Prop :=
  lm.length = 2 * c.max_vars ∧
  ∀ l < 2 * c.max_vars, lm[l]? = lm0[l]? ∨
    (∃ k, lo ≤ k ∧ k < hi ∧ (ar[qw + 3 + k]?.getD 0#32).toNat = l ∧
      lm[l]? = some (lm0[l]?.getD 0#8 ||| 2#8))

theorem lmBit2Inv_init {c : FullCfg} {ar : List (BitVec 32)} {lm0 : List (BitVec 8)}
    {qw : Nat} (hlm0 : lm0.length = 2 * c.max_vars) : LmBit2Inv c ar lm0 qw 0 0 lm0 :=
  ⟨hlm0, fun _ _ => Or.inl rfl⟩

theorem lmBit2Inv_skip {c : FullCfg} {ar : List (BitVec 32)} {lm0 lm : List (BitVec 8)}
    {qw j : Nat} (h : LmBit2Inv c ar lm0 qw 0 j lm) : LmBit2Inv c ar lm0 qw 0 (j + 1) lm :=
  ⟨h.1, fun l hl => by
    rcases h.2 l hl with heq | ⟨k, h0, hk, har, hset⟩
    · exact Or.inl heq
    · exact Or.inr ⟨k, h0, by omega, har, hset⟩⟩

theorem lmBit2Inv_or2 {c : FullCfg} {ar : List (BitVec 32)} {lm0 lm : List (BitVec 8)}
    {qw j : Nat} (_hlm0 : lm0.length = 2 * c.max_vars) (h : LmBit2Inv c ar lm0 qw 0 j lm)
    (hj_ar : qw + 3 + j < ar.length)
    (hl_lt : (ar[qw + 3 + j]'hj_ar).toNat < 2 * c.max_vars) :
    let l := (ar[qw + 3 + j]'hj_ar).toNat
    LmBit2Inv c ar lm0 qw 0 (j + 1) (lm.set l ((lm[l]'(by rw [h.1]; exact hl_lt)) ||| 2#8)) := by
  obtain ⟨hlm, hall⟩ := h
  intro l
  refine ⟨by simp [hlm], fun i hi => ?_⟩
  by_cases hil : i = l
  · subst hil
    refine Or.inr ⟨j, Nat.zero_le _, by omega,
      by rw [List.getElem?_eq_getElem hj_ar, Option.getD_some], ?_⟩
    rw [List.getElem?_set_self (by omega)]
    rcases hall l hl_lt with heq | ⟨_, _, _, _, hset⟩
    · have : lm[l]'(by omega) = lm0[l]?.getD 0#8 := by
        rw [← heq, List.getElem?_eq_getElem (by omega), Option.getD_some]
      rw [this]
    · rw [List.getElem?_eq_getElem (by omega)] at hset
      rw [Option.some.inj hset, bv8_or2_idem]
  · rw [List.getElem?_set_ne (Ne.symm hil)]
    rcases hall i hi with heq | ⟨k, h0, hk, har, hset⟩
    · exact Or.inl heq
    · exact Or.inr ⟨k, h0, by omega, har, hset⟩

theorem lmBit2Inv_clear_step {c : FullCfg} {ar : List (BitVec 32)}
    {lm0 lm : List (BitVec 8)}
    {qw j csz : Nat} (hlm0 : lm0.length = 2 * c.max_vars)
    (hlm0_b1 : ∀ l < 2 * c.max_vars, (lm0[l]?.getD 0#8 &&& 2#8) = 0#8)
    (h : LmBit2Inv c ar lm0 qw j csz lm) (hj : j < csz) (hj_ar : qw + 3 + j < ar.length)
    (hl_lt : (ar[qw + 3 + j]'hj_ar).toNat < 2 * c.max_vars) :
    let cj := (ar[qw + 3 + j]'hj_ar).toNat
    LmBit2Inv c ar lm0 qw (j + 1) csz
      (lm.set cj ((lm[cj]'(by rw [h.1]; exact hl_lt)) &&& 0xFD#8)) := by
  obtain ⟨hlm, hall⟩ := h
  intro cj
  have hcj_eq : (ar[qw + 3 + j]?.getD 0#32).toNat = cj := by
    rw [List.getElem?_eq_getElem hj_ar, Option.getD_some]
  have hclr : ((lm[cj]'(by omega)) &&& 0xFD#8) = lm0[cj]?.getD 0#8 := by
    apply bv8_clear_bit1_eq_of_or2 (hlm0_b1 cj hl_lt)
    rcases hall cj hl_lt with heq | ⟨_, _, _, _, hset⟩
    · left; rw [← heq, List.getElem?_eq_getElem (by omega), Option.getD_some]
    · right; rw [List.getElem?_eq_getElem (by omega)] at hset; exact Option.some.inj hset
  refine ⟨by simp [hlm], fun i hi => ?_⟩
  by_cases hic : i = cj
  · subst hic; left
    rw [List.getElem?_set_self (by omega), hclr,
      List.getElem?_eq_getElem (by omega), Option.getD_some]
  · rw [List.getElem?_set_ne (Ne.symm hic)]
    rcases hall i hi with heq | ⟨k, hk1, hk2, har, hset⟩
    · exact Or.inl heq
    · have hkne : k ≠ j := fun h => by subst h; rw [hcj_eq] at har; exact hic har.symm
      exact Or.inr ⟨k, by omega, hk2, har, hset⟩

theorem lmBit2Inv_done {c : FullCfg} {ar : List (BitVec 32)} {lm0 lm : List (BitVec 8)}
    {qw csz : Nat} (hlm0 : lm0.length = 2 * c.max_vars)
    (h : LmBit2Inv c ar lm0 qw csz csz lm) : lm = lm0 := by
  apply list_eq_of_getElem?_eq (by rw [h.1, hlm0])
  intro i hi
  rcases h.2 i (by omega) with heq | ⟨k, hk1, hk2, _⟩
  · exact heq
  · omega

theorem lmBit2Inv_preserves_bit0 {c : FullCfg} {ar : List (BitVec 32)}
    {lm0 lm : List (BitVec 8)} {qw lo hi : Nat} (h : LmBit2Inv c ar lm0 qw lo hi lm)
    {l : Nat} (hl : l < 2 * c.max_vars) :
    (lm[l]?.getD 0#8 &&& 1#8) = (lm0[l]?.getD 0#8 &&& 1#8) := by
  rcases h.2 l hl with heq | ⟨_, _, _, _, hset⟩
  · rw [heq]
  · rw [hset, Option.getD_some, bv8_or2_and_bit0]

theorem lmBit2Inv_preserves_bit2 {c : FullCfg} {ar : List (BitVec 32)}
    {lm0 lm : List (BitVec 8)} {qw lo hi : Nat} (h : LmBit2Inv c ar lm0 qw lo hi lm)
    {l : Nat} (hl : l < 2 * c.max_vars) :
    (lm[l]?.getD 0#8 &&& 4#8) = (lm0[l]?.getD 0#8 &&& 4#8) := by
  rcases h.2 l hl with heq | ⟨_, _, _, _, hset⟩
  · rw [heq]
  · rw [hset, Option.getD_some, bv8_or2_and_bit2]

theorem fullDenseInvW_set_flags {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hinv : FullDenseInvW c F0 F_cur s)
    {fl' : List (BitVec 32)} (hfl : fl'.length = c.max_vars) :
    FullDenseInvW c F0 F_cur { s with core := { s.core with flags := fl' } } :=
  fullDenseInv_with_core_aux (tc' := s.core.tmp_cnt) (tl' := s.core.tmp_len) (sc' := s.scratch)
    hinv hinv.1.core_ok.repr_len hinv.1.core_ok.min_clr_len_arr hinv.1.core_ok.tmp_len_arr
    hfl hinv.1.core_ok.tmp_len_le hinv.1.scratch_ok rfl rfl


end LeanQbe.T.Examples.Kissat.Proof.Spec
