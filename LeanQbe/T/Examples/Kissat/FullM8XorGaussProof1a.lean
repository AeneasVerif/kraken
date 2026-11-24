/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM8XorGaussProof0
import LeanQbe.T.Examples.Kissat.FullAssignAddLemmas1
import LeanQbe.T.Examples.Kissat.FullLearnAnaLemmas1
import LeanQbe.T.Examples.Kissat.FullM6ProofUtil
import LeanQbe.T.Examples.Kissat.FullM4VivBceProof1
import LeanQbe.T.Examples.Kissat.FullM6Transport1
public meta import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.C0Agrees
public meta import Lean.Elab.Tactic
public meta import LeanQbe.T.Logic.C0Step

/-!
# Kissat M8 XOR / $\mathbb{F}_2$ Gauss-Jordan — Hash Insert & Pool Ops (`FullM8XorGaussProof1a`)

`Func.wp` proofs for `full_xor_ht_insert`, `full_xor_compact_pool`, and `full_xor_merge_two`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM8XorGauss

open Std Std.Sat Std.ExtHashMap LeanQbe.T.C0Step
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open Kraken.Bedrock2.Test

open scoped FullArenaTactics FullAssignAddTactics
open FullAssignAddTactics LeanQbe.T.Examples.Kissat.FullM6ProofUtil
open LeanQbe.T.Examples.Kissat.Full.FullDenseWatchHelpers

local elab "c0_hstraight" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { unrollGroup := false, splitJnz := false } 2000

local elab "c0_hstraight!" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { unrollGroup := false, splitJnz := false, strictMem := true } 2000

private theorem nat_le_of_testBit_imp :
    ∀ (x y : Nat), (∀ i, x.testBit i = true → y.testBit i = true) → x ≤ y := by
  intro x
  induction x using Nat.strongRecOn with
  | ind x ih =>
    intro y h
    by_cases hx0 : x = 0
    · subst hx0; exact Nat.zero_le _
    · have hdiv : ∀ z k, (z / 2).testBit k = z.testBit (k + 1) := fun z k => by
        simp only [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, Nat.pow_succ,
          Nat.mul_comm 2 (2 ^ k)]
      have hhalf : x / 2 ≤ y / 2 := by
        apply ih (x / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero hx0) (by decide))
        intro i hi
        rw [hdiv]; exact h (i + 1) (by rwa [← hdiv])
      rcases Nat.lt_or_eq_of_le hhalf with hlt | heq
      · omega
      · by_cases hx1 : x % 2 = 0
        · omega
        · have hxb : x.testBit 0 = true := by
            simp only [Nat.testBit, Nat.shiftRight_zero]
            have : x % 2 = 1 := by omega
            simp [this]
          have hyb : y.testBit 0 = true := h 0 hxb
          simp only [Nat.testBit, Nat.shiftRight_zero] at hyb
          have hy1 : y % 2 ≠ 0 := by intro h0; simp [h0] at hyb
          omega

theorem bv64_land_le_right (a b : BitVec 64) : (a &&& b).toNat ≤ b.toNat := by
  rw [BitVec.toNat_and]
  apply nat_le_of_testBit_imp
  intro i hi
  rw [Nat.testBit_and, Bool.and_eq_true] at hi
  exact hi.2

theorem bv64_land_sub1_lt (x cap : BitVec 64) (hc : 0 < cap.toNat) :
    (x &&& (cap - (1 : BitVec 64))).toNat < cap.toNat := by
  rw [BitVec.toNat_and]
  have hle : x.toNat &&& (cap - (1 : BitVec 64)).toNat ≤ (cap - (1 : BitVec 64)).toNat := by
    apply nat_le_of_testBit_imp
    intro i hi
    rw [Nat.testBit_and, Bool.and_eq_true] at hi
    exact hi.2
  have hsub : (cap - (1 : BitVec 64)).toNat = cap.toNat - 1 := by bv_omega
  omega

private meta def findAndSubTerm? (e : Lean.Expr) : Option Lean.Expr :=
  e.find? fun t =>
    t.isAppOfArity ``HAnd.hAnd 6 && (t.getArg! 5).isAppOfArity ``HSub.hSub 6

local elab "ht_note_slot_lt" hcap:ident : tactic => Lean.Elab.Tactic.withMainContext do
  let g ← Lean.Elab.Tactic.getMainGoal
  let ty ← Lean.instantiateMVars (← g.getType)
  let some slotTerm := findAndSubTerm? ty
    | throwError "ht_note_slot_lt: could not find `(hval + probe) &&& (ht_cap - 1)` in goal"
  let x := slotTerm.getArg! 4
  let cap := (slotTerm.getArg! 5).getArg! 4
  let hcapExpr ← Lean.Elab.Term.elabTerm hcap none
  let pf ← Lean.Meta.mkAppM ``bv64_land_sub1_lt #[x, cap, hcapExpr]
  let (_, g') ← g.note `hslot_lt pf
  Lean.Elab.Tactic.replaceMainGoal [g']

theorem bv32_shr1 (x : BitVec 32) : (x >>> (1 : BitVec 32)).toNat = x.toNat / 2 := by
  have : (x >>> (1 : BitVec 32)) = x >>> 1 := rfl
  rw [this, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_one]

theorem bv32_shr1_nat (x : BitVec 32) : (x >>> (1 : Nat)).toNat = x.toNat / 2 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_one]

theorem bv32_and_one_toNat (x : BitVec 32) : (x &&& 1#32).toNat = x.toNat % 2 := by
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by decide), Nat.and_one_is_mod]

private theorem bv32_shiftLeft_one_toNat {s : BitVec 32} (hs : s.toNat < 32) :
    (1#32 <<< s).toNat = 2 ^ s.toNat := by
  have h1 : (1#32 <<< s) = 1#32 <<< s.toNat := rfl
  have h1_lt : (1 : Nat) < 2 ^ 32 := by decide
  have hlt : 2 ^ s.toNat < 2 ^ 32 := Nat.pow_lt_pow_right (by decide : 1 < 2) hs
  rw [h1, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1_lt,
    Nat.shiftLeft_eq, Nat.one_mul, Nat.mod_eq_of_lt hlt]

private theorem bv32_getLsbD_shiftLeft_one {s : BitVec 32} (hs : s.toNat < 32) (m : Nat) :
    (1#32 <<< s).getLsbD m = decide (m = s.toNat) := by
  have hpow : (1#32 <<< s).toNat = 2 ^ s.toNat := bv32_shiftLeft_one_toNat hs
  have hs64 : 1#32 <<< s = BitVec.ofNat 32 (2 ^ s.toNat) := by
    apply BitVec.eq_of_toNat_eq
    rw [hpow, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hs)]
  rw [hs64, BitVec.getLsbD_ofNat]
  by_cases hm : m < 32
  · rw [decide_eq_true hm, Bool.true_and, Nat.testBit_two_pow]
    by_cases heq : s.toNat = m
    · subst heq; simp
    · simp [heq, Ne.symm heq]
  · have hne : m ≠ s.toNat := by omega
    simp [hm, hne]

private theorem star_array_congr {a b : List (BitVec 32)} {p : Val i64}
    {Rest : Mem 64 → Prop} {m : Mem 64}
    (h_eq : a = b) (hm : (array (t := i32) p a ⋆ Rest) m) :
    (array (t := i32) p b ⋆ Rest) m := h_eq ▸ hm

private theorem list_set7_congr {α : Type} {xs : List α}
    {i0 i1 i2 i3 i4 i5 i6 j0 j1 j2 j3 j4 j5 j6 : Nat}
    {x0 x1 x2 x3 x4 x5 x6 y0 y1 y2 y3 y4 y5 y6 : α}
    (hi0 : i0 = j0) (hi1 : i1 = j1) (hi2 : i2 = j2) (hi3 : i3 = j3)
    (hi4 : i4 = j4) (hi5 : i5 = j5) (hi6 : i6 = j6)
    (hx0 : x0 = y0) (hx1 : x1 = y1) (hx2 : x2 = y2) (hx3 : x3 = y3)
    (hx4 : x4 = y4) (hx5 : x5 = y5) (hx6 : x6 = y6) :
    ((((((xs.set i0 x0).set i1 x1).set i2 x2).set i3 x3).set i4 x4).set i5 x5).set i6 x6 =
    ((((((xs.set j0 y0).set j1 y1).set j2 y2).set j3 y3).set j4 y4).set j5 y5).set j6 y6 := by
  subst_vars; rfl

private theorem list_set7_slot_eq {scr : List (BitVec 32)} {s : BitVec 64}
    {x0 x1 x2 x3 x4 x5 x6 y0 y1 y2 y3 y4 y5 y6 : BitVec 32}
    (hs_mul : (s * 7#64).toNat = s.toNat * 7)
    (hs_bd : s.toNat * 7 + 6 < 2 ^ 64)
    (hx0 : x0 = y0) (hx1 : x1 = y1) (hx2 : x2 = y2) (hx3 : x3 = y3)
    (hx4 : x4 = y4) (hx5 : x5 = y5) (hx6 : x6 = y6) :
    ((((((scr.set (s * 7#64).toNat x0).set (s * 7#64 + 1#64).toNat x1).set
      (s * 7#64 + 2#64).toNat x2).set (s * 7#64 + 3#64).toNat x3).set
      (s * 7#64 + 4#64).toNat x4).set (s * 7#64 + 5#64).toNat x5).set
      (s * 7#64 + 6#64).toNat x6 =
    ((((((scr.set (s.toNat * 7) y0).set (s.toNat * 7 + 1) y1).set
      (s.toNat * 7 + 2) y2).set (s.toNat * 7 + 3) y3).set
      (s.toNat * 7 + 4) y4).set (s.toNat * 7 + 5) y5).set
      (s.toNat * 7 + 6) y6 := by
  apply list_set7_congr <;>
    first | exact hs_mul | bv_omega | exact hx0 | exact hx1 | exact hx2 |
      exact hx3 | exact hx4 | exact hx5 | exact hx6

local elab "ht_rw_slot_lhs" hslot:ident hv0:ident hv1:ident hv2:ident : tactic =>
    Lean.Elab.Tactic.withMainContext do
  let g ← Lean.Elab.Tactic.getMainGoal
  let ty ← Lean.instantiateMVars (← g.getType)
  let lhs := ty.getArg! 1
  let some slot_c0 := findAndSubTerm? lhs
    | throwError "ht_rw_slot_lhs: could not find slot term in LHS"
  let slotExpr ← Lean.Elab.Term.elabTerm hslot none
  let eqTy ← Lean.Meta.mkEq slot_c0 slotExpr
  let eqGoal ← Lean.Meta.mkFreshExprMVar eqTy
  let rem ← Lean.Elab.Tactic.run eqGoal.mvarId! do
    Lean.Elab.Tactic.evalTactic (← `(tactic|
      dsimp only [$hslot:ident, $hv0:ident, $hv1:ident, $hv2:ident]; rfl))
  if !rem.isEmpty then
    throwError "ht_rw_slot_lhs: could not prove {eqTy}"
  let pf ← Lean.instantiateMVars eqGoal
  let (_, g1) ← g.note `hslot_c0_eq pf
  Lean.Elab.Tactic.replaceMainGoal [g1]
  Lean.Elab.Tactic.evalTactic (← `(tactic| simp only [$(Lean.mkIdent `hslot_c0_eq):term]))

private theorem list_set1_or_congr {scr : List (BitVec 32)} {i j : Nat}
    {hi_lt : i < scr.length}
    {b1 b2 : BitVec 32} (hij : i = j) (hb : b1 = b2) :
    scr.set i ((scr[i]'hi_lt) ||| b1) =
    scr.set j ((scr[j]?.getD 0#32) ||| b2) := by
  subst hij; subst hb
  rw [List.getElem?_eq_getElem hi_lt, Option.getD_some]

private theorem bv64_mul7_add_toNat (s : BitVec 64) (hs : (s * 7#64).toNat = s.toNat * 7)
    (k : BitVec 64) (hk : k.toNat ≤ 6) (hbd : s.toNat * 7 + 6 < 2 ^ 64) :
    (s * 7#64 + k).toNat = s.toNat * 7 + k.toNat := by bv_omega

private theorem bv64_mul7_add_lt {s k : BitVec 64} {len : Nat}
    (hs : (s * 7#64).toNat = s.toNat * 7)
    (hk : k.toNat ≤ 6) (hbd : s.toNat * 7 + 6 < len) (_hlen : len < 2 ^ 32) :
    (s * 7#64 + k).toNat < len := by bv_omega

private theorem bv64_mul7_add1 {s : BitVec 64} {len : Nat}
    (hs : (s * 7#64).toNat = s.toNat * 7) (hbd : s.toNat * 7 + 6 < len) (_hl : len < 2 ^ 32) :
    (s * 7#64 + 1#64).toNat = s.toNat * 7 + 1 := by bv_omega

private theorem bv64_mul7_add2 {s : BitVec 64} {len : Nat}
    (hs : (s * 7#64).toNat = s.toNat * 7) (hbd : s.toNat * 7 + 6 < len) (_hl : len < 2 ^ 32) :
    (s * 7#64 + 2#64).toNat = s.toNat * 7 + 2 := by bv_omega

private theorem bv64_mul7_add3 {s : BitVec 64} {len : Nat}
    (hs : (s * 7#64).toNat = s.toNat * 7) (hbd : s.toNat * 7 + 6 < len) (_hl : len < 2 ^ 32) :
    (s * 7#64 + 3#64).toNat = s.toNat * 7 + 3 := by bv_omega

private theorem bv64_mul7_add4 {s : BitVec 64} {len : Nat}
    (hs : (s * 7#64).toNat = s.toNat * 7) (hbd : s.toNat * 7 + 6 < len) (_hl : len < 2 ^ 32) :
    (s * 7#64 + 4#64).toNat = s.toNat * 7 + 4 := by bv_omega

private theorem bv64_mul7_add5 {s : BitVec 64} {len : Nat}
    (hs : (s * 7#64).toNat = s.toNat * 7) (hbd : s.toNat * 7 + 6 < len) (_hl : len < 2 ^ 32) :
    (s * 7#64 + 5#64).toNat = s.toNat * 7 + 5 := by bv_omega

private theorem bv64_mul7_add6 {s : BitVec 64} {len : Nat}
    (hs : (s * 7#64).toNat = s.toNat * 7) (hbd : s.toNat * 7 + 6 < len) (_hl : len < 2 ^ 32) :
    (s * 7#64 + 6#64).toNat = s.toNat * 7 + 6 := by bv_omega

private theorem bv32_shr1_eq (x : BitVec 32) : x >>> (1 : BitVec 32) = x >>> (1 : Nat) := rfl

private theorem bv32_shl1_and31 (s : BitVec 32) (hs : s.toNat < 32) :
    1#32 <<< (s &&& 31#32) = 1#32 <<< s := by
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_and]
  by_cases hk : k < 5
  · have h31 : (31#32).toNat.testBit k = true := by
      rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4) with
        rfl | rfl | rfl | rfl | rfl <;> decide
    rw [h31, Bool.and_true]
  · have h5k : 5 ≤ k := by omega
    have hpow : 32 ≤ 2 ^ k := by simpa using Nat.pow_le_pow_right (by decide : 0 < 2) h5k
    have hlt : s.toNat < 2 ^ k := Nat.lt_of_lt_of_le hs hpow
    have hbit : s.toNat.testBit k = false := by
      simp [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hlt]
    rw [hbit, Bool.false_and]

private theorem slot_mod0 {s len : Nat} (hbd : s * 7 + 6 < len) (_hl : len < 2 ^ 32) :
    (s * BitVec.toNat (7 : BitVec 64)) % 2 ^ 64 = s * 7 := by
  change (s * 7) % 2 ^ 64 = s * 7; exact Nat.mod_eq_of_lt (by omega)

private theorem slot_mod2 {s len : Nat} (hbd : s * 7 + 6 < len) (_hl : len < 2 ^ 32) :
    (s * BitVec.toNat (7 : BitVec 64) + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64 = s * 7 + 2 := by
  change (s * 7 + 2) % 2 ^ 64 = s * 7 + 2; exact Nat.mod_eq_of_lt (by omega)

private theorem slot_mod3 {s len : Nat} (hbd : s * 7 + 6 < len) (_hl : len < 2 ^ 32) :
    (s * BitVec.toNat (7 : BitVec 64) + BitVec.toNat (3 : BitVec 64)) % 2 ^ 64 = s * 7 + 3 := by
  change (s * 7 + 3) % 2 ^ 64 = s * 7 + 3; exact Nat.mod_eq_of_lt (by omega)

private theorem slot_mod4 {s len : Nat} (hbd : s * 7 + 6 < len) (_hl : len < 2 ^ 32) :
    (s * BitVec.toNat (7 : BitVec 64) + BitVec.toNat (4 : BitVec 64)) % 2 ^ 64 = s * 7 + 4 := by
  change (s * 7 + 4) % 2 ^ 64 = s * 7 + 4; exact Nat.mod_eq_of_lt (by omega)

private theorem slot_mod5 {s len : Nat} (hbd : s * 7 + 6 < len) (_hl : len < 2 ^ 32) :
    (s * BitVec.toNat (7 : BitVec 64) + BitVec.toNat (5 : BitVec 64)) % 2 ^ 64 = s * 7 + 5 := by
  change (s * 7 + 5) % 2 ^ 64 = s * 7 + 5; exact Nat.mod_eq_of_lt (by omega)

private theorem slot_mod6 {s len : Nat} (hbd : s * 7 + 6 < len) (_hl : len < 2 ^ 32) :
    (s * BitVec.toNat (7 : BitVec 64) + BitVec.toNat (6 : BitVec 64)) % 2 ^ 64 = s * 7 + 6 := by
  change (s * 7 + 6) % 2 ^ 64 = s * 7 + 6; exact Nat.mod_eq_of_lt (by omega)

local elab "ht_match_field" hslt:ident hslot:ident _hsb:ident hbd:ident h32:ident
    hv0:ident hv1:ident hv2:ident : tactic => Lean.Elab.Tactic.withMainContext do
  let hsltExpr ← Lean.Elab.Term.elabTerm hslt none
  let hsltTy ← Lean.instantiateMVars (← Lean.Meta.inferType hsltExpr)
  let some slot_c0 := findAndSubTerm? hsltTy
    | throwError "ht_match_field: could not find slot term in {hsltTy}"
  let slotExpr ← Lean.Elab.Term.elabTerm hslot none
  let eqTy ← Lean.Meta.mkEq (← Lean.Meta.mkAppM ``BitVec.toNat #[slot_c0])
    (← Lean.Meta.mkAppM ``BitVec.toNat #[slotExpr])
  let eqGoal ← Lean.Meta.mkFreshExprMVar eqTy
  let rem ← Lean.Elab.Tactic.run eqGoal.mvarId! do
    Lean.Elab.Tactic.evalTactic (← `(tactic|
      exact congrArg BitVec.toNat
        (by dsimp only [$hslot:ident, $hv0:ident, $hv1:ident, $hv2:ident]; rfl)))
  if !rem.isEmpty then
    throwError "ht_match_field: could not prove {eqTy}"
  let pf ← Lean.instantiateMVars eqGoal
  let g0 ← Lean.Elab.Tactic.getMainGoal
  let mut toClear : Array Lean.FVarId := #[]
  let dropNames : Array Lean.Name :=
    #[`hQ, `hm0, `hht, `hEntails, `hss_tmp, `hcv_tmp, `ih3, `hhi_i, `hbits_i,
      `hsm_bits, `hclause_eq, `ihp, `hJ]
  for ldecl in ← Lean.getLCtx do
    if !ldecl.isImplementationDetail &&
        (dropNames.contains ldecl.userName ||
         (ldecl.type.isForall && !ldecl.type.isAppOf ``Not)) then
      toClear := toClear.push ldecl.fvarId
  let g1 ← g0.tryClearMany toClear
  let (_, g2) ← g1.note `hslot_toNat pf
  Lean.Elab.Tactic.replaceMainGoal [g2]
  let hEq := Lean.mkIdent `hslot_toNat
  Lean.Elab.Tactic.evalTactic (← `(tactic| conv at $hEq:ident => lhs; simp only [bv_c0]))
  Lean.Elab.Tactic.evalTactic (← `(tactic|
    try simp only [$hEq:ident,
      slot_mod0 $hbd:ident $h32:ident,
      slot_mod2 $hbd:ident $h32:ident,
      slot_mod3 $hbd:ident $h32:ident,
      slot_mod4 $hbd:ident $h32:ident,
      slot_mod5 $hbd:ident $h32:ident,
      slot_mod6 $hbd:ident $h32:ident] at *))
  Lean.Elab.Tactic.evalTactic (← `(tactic|
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]))
  Lean.Elab.Tactic.evalTactic (← `(tactic|
    try simp only [$hv0:ident, $hv1:ident, $hv2:ident, bv32_shr1_eq]))
  Lean.Elab.Tactic.evalTactic (← `(tactic| bv_omega))

private theorem ht_insert_empty_ok {F : CNF Nat} {cv ht_cap slot : Nat}
    {scr : List (BitVec 32)} {k bit v0 v1 v2 v3 v4 : BitVec 32}
    {tmp : List (BitVec 32)} {smask : BitVec 32}
    (hht : XorHtInv F cv ht_cap scr)
    (hslot_lt : slot < ht_cap)
    (hcap_bd : 7 * ht_cap ≤ scr.length)
    (hk3 : 3 ≤ k.toNat) (hk5 : k.toNat ≤ 5) (hk_tmp : k.toNat ≤ tmp.length)
    (hsm_lt32 : smask.toNat < 32)
    (hbit : bit = 1#32 <<< smask)
    (hv0 : v0.toNat = (tmp[0]?.getD 0#32).toNat / 2)
    (hv1 : v1.toNat = (tmp[1]?.getD 0#32).toNat / 2)
    (hv2 : v2.toNat = (tmp[2]?.getD 0#32).toNat / 2)
    (hv3 : 4 ≤ k.toNat → v3.toNat = (tmp[3]?.getD 0#32).toNat / 2)
    (hv4 : 5 ≤ k.toNat → v4.toNat = (tmp[4]?.getD 0#32).toNat / 2)
    (hcv_tmp : ∀ i < k.toNat, (tmp[i]?.getD 0#32).toNat / 2 < cv)
    (hss_tmp : List.Pairwise (· < ·) ((tmp.take k.toNat).map fun x => x.toNat / 2))
    (hclause_eq : xorMaskClause ((tmp.take k.toNat).map fun x => x.toNat / 2) smask.toNat =
      (tmp.take k.toNat).map BitVec.toNat)
    (hEntails : F.EntailsClause (cnfClause ((tmp.take k.toNat).map BitVec.toNat))) :
    let scr' := ((((((scr.set (slot * 7) k).set
      (slot * 7 + 1) bit).set (slot * 7 + 2) v0).set
      (slot * 7 + 3) v1).set (slot * 7 + 4) v2).set
      (slot * 7 + 5) v3).set (slot * 7 + 6) v4
    scr'.length = scr.length ∧
    (∀ i, 7 * ht_cap ≤ i → scr'[i]? = scr[i]?) ∧
    XorHtInv F cv ht_cap scr' := by
  intro scr'
  have hsb_bd : slot * 7 + 6 < scr.length := by omega
  have hscr'_len : scr'.length = scr.length := by simp [scr']
  have hscr'_out : ∀ i, i < slot * 7 ∨ slot * 7 + 7 ≤ i → scr'[i]? = scr[i]? := by
    intro i hi; simp only [scr']
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega)]
  have hg6 : scr'[slot * 7 + 6]? = some v4 := by
    simp only [scr']; rw [List.getElem?_set_self (by simp; omega)]
  have hg5 : scr'[slot * 7 + 5]? = some v3 := by
    simp only [scr']; rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by simp; omega)]
  have hg4 : scr'[slot * 7 + 4]? = some v2 := by
    simp only [scr']; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_self (by simp; omega)]
  have hg3 : scr'[slot * 7 + 3]? = some v1 := by
    simp only [scr']; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega), List.getElem?_set_self (by simp; omega)]
  have hg2 : scr'[slot * 7 + 2]? = some v0 := by
    simp only [scr']; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_self (by simp; omega)]
  have hg1 : scr'[slot * 7 + 1]? = some bit := by
    simp only [scr']; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega), List.getElem?_set_self (by simp; omega)]
  have hg0 : scr'[slot * 7]? = some k := by
    simp only [scr']; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_self (by omega)]
  refine ⟨hscr'_len, fun i hi => hscr'_out i (Or.inr (by omega)), ?_⟩
  intro s hs
  by_cases heq : s = slot
  · subst heq
    dsimp only
    rw [hg0, Option.getD_some]
    refine Or.inr ⟨hk3, hk5, ?_⟩
    have hvs_eq : (List.range k.toNat).map (fun i => (scr'[s * 7 + 2 + i]?.getD 0#32).toNat) =
        (tmp.take k.toNat).map fun x => x.toNat / 2 := by
      apply List.ext_getElem
      · simp [List.length_map, List.length_range, List.length_take, Nat.min_eq_left hk_tmp]
      · intro i hi1 _
        rw [List.length_map, List.length_range] at hi1
        simp only [List.getElem_map, List.getElem_range, List.getElem_take]
        rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl
        · rw [hg2, Option.getD_some, hv0, List.getElem?_eq_getElem (by omega), Option.getD_some]
        · rw [hg3, Option.getD_some, hv1, List.getElem?_eq_getElem (by omega), Option.getD_some]
        · rw [hg4, Option.getD_some, hv2, List.getElem?_eq_getElem (by omega), Option.getD_some]
        · rw [hg5, Option.getD_some, hv3 (by omega),
            List.getElem?_eq_getElem (by omega), Option.getD_some]
        · rw [hg6, Option.getD_some, hv4 (by omega),
            List.getElem?_eq_getElem (by omega), Option.getD_some]
    have hlt_vs : ∀ v ∈ (tmp.take k.toNat).map (fun x => x.toNat / 2), v < cv := by
      intro v hv
      rcases List.mem_map.mp hv with ⟨x, hx, rfl⟩
      rcases List.getElem_of_mem hx with ⟨idx, hidx, rfl⟩
      rw [List.length_take, Nat.min_eq_left hk_tmp] at hidx
      rw [List.getElem_take]
      have hc := hcv_tmp idx hidx
      rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at hc
    rw [hvs_eq, hg1, Option.getD_some, hbit]
    refine ⟨hss_tmp, hlt_vs, fun m' hm' hbm => ?_⟩
    rw [bv32_getLsbD_shiftLeft_one hsm_lt32] at hbm
    have hmeq : m' = smask.toNat := of_decide_eq_true hbm
    subst hmeq
    rw [hclause_eq]; exact hEntails
  · have hdisj : ∀ a : Nat, a < 7 → s * 7 + a < slot * 7 ∨ slot * 7 + 7 ≤ s * 7 + a := by
      intro a ha
      rcases Nat.lt_or_gt_of_ne heq with hlt | hgt <;> omega
    have hs_same : ∀ i < 7, scr'[s * 7 + i]? = scr[s * 7 + i]? := fun i hi =>
      hscr'_out (s * 7 + i) (hdisj i hi)
    dsimp only
    have hs0 := hs_same 0 (by decide); simp only [Nat.add_zero] at hs0; rw [hs0]
    rcases hht s hs with hz | ⟨h3, h5, hss, hltv, hseen⟩
    · exact Or.inl hz
    · refine Or.inr ⟨h3, h5, ?_⟩
      have hvs_same : (List.range (scr[s * 7]?.getD 0#32).toNat).map
          (fun i => (scr'[s * 7 + 2 + i]?.getD 0#32).toNat) =
          (List.range (scr[s * 7]?.getD 0#32).toNat).map
          (fun i => (scr[s * 7 + 2 + i]?.getD 0#32).toNat) := by
        refine List.map_congr_left fun i hi => ?_
        have him : 2 + i < 7 := by have := List.mem_range.mp hi; omega
        have hsi := hs_same (2 + i) him
        rw [← Nat.add_assoc] at hsi; rw [hsi]
      rw [hvs_same, hs_same 1 (by decide)]
      exact ⟨hss, hltv, hseen⟩

private theorem bv32_lt_two_pow_of_msb {x : BitVec 32} {n : Nat} (hn : n ≤ 32)
    (hhi : ∀ i, n ≤ i → i < 32 → x.getLsbD i = false) : x.toNat < 2 ^ n := by
  by_cases h32 : n = 32
  · subst h32; exact x.isLt
  · have hn32 : n < 32 := by omega
    have hmod : x = x &&& BitVec.ofNat 32 (2 ^ n - 1) := by
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      rw [BitVec.getLsbD_and, BitVec.getLsbD_ofNat, decide_eq_true hi, Bool.true_and]
      by_cases hin : i < n
      · rw [Nat.testBit_two_pow_sub_one, decide_eq_true hin, Bool.and_true]
      · have hf : x.getLsbD i = false := hhi i (by omega) hi
        rw [hf, Bool.false_and]
    rw [hmod, BitVec.toNat_and]
    have hle : x.toNat &&& (BitVec.ofNat 32 (2 ^ n - 1)).toNat ≤
        (BitVec.ofNat 32 (2 ^ n - 1)).toNat := by
      apply nat_le_of_testBit_imp
      intro i hi
      rw [Nat.testBit_and, Bool.and_eq_true] at hi
      exact hi.2
    have hm1 : (BitVec.ofNat 32 (2 ^ n - 1)).toNat = 2 ^ n - 1 := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt
        (by have := Nat.pow_lt_pow_right (by decide : 1 < 2) hn32; omega)]
    have hpos : 0 < 2 ^ n := Nat.two_pow_pos n
    omega

private theorem xorMaskClause_of_tmp {tmp : List (BitVec 32)} {k : Nat} {smask : BitVec 32}
    (hk : k ≤ tmp.length) (_hk5 : k ≤ 5) (_hsm_lt : smask.toNat < 2 ^ k)
    (hbits : ∀ i < k, smask.getLsbD i = ((tmp[i]?.getD 0#32).toNat % 2 == 1)) :
    xorMaskClause ((tmp.take k).map fun x => x.toNat / 2) smask.toNat =
      (tmp.take k).map BitVec.toNat := by
  unfold xorMaskClause
  apply List.ext_getElem
  · simp [List.length_map, List.length_range, List.length_take, Nat.min_eq_left hk]
  · intro i hi1 hi2
    rw [List.length_map, List.length_range, List.length_map, List.length_take,
      Nat.min_eq_left hk] at hi1
    simp only [List.getElem_map, List.getElem_range, List.getElem_take]
    rw [List.getElem?_eq_getElem (by rw [List.length_map, List.length_take]; omega),
      Option.getD_some, List.getElem_map, List.getElem_take]
    have hbit := hbits i hi1
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hbit
    have hsh_eq : (smask.toNat >>> i % 2 == 1) = ((tmp[i]'(by omega)).toNat % 2 == 1) := by
      rw [← hbit]
      change decide (smask.toNat >>> i % 2 = 1) = smask.getLsbD i
      simp only [BitVec.getLsbD, Nat.testBit, Nat.shiftRight_eq_div_pow]
      cases Nat.mod_two_eq_zero_or_one (smask.toNat / 2 ^ i) with
      | inl h0 => simp [h0]
      | inr h1 => simp [h1]
    rw [hsh_eq]
    unfold mkLit
    have hmod := Nat.div_add_mod ((tmp[i]'(by omega)).toNat) 2
    cases hrem : (tmp[i]'(by omega)).toNat % 2 with
    | zero => simp [hrem] at hmod ⊢; omega
    | succ r =>
      have : r = 0 := by omega
      subst this
      simp [hrem] at hmod ⊢; omega

private theorem set7_eq {α : Type} {xs : List α} {b : Nat} {x0 x1 x2 x3 x4 x5 x6 : α} :
    let xs' := ((((((xs.set b x0).set (b + 1) x1).set (b + 2) x2).set (b + 3) x3).set
      (b + 4) x4).set (b + 5) x5).set (b + 6) x6
    xs'.length = xs.length ∧
    (∀ t, (t < b ∨ b + 7 ≤ t) → xs'[t]? = xs[t]?) ∧
    (b + 6 < xs.length →
      xs'[b]? = some x0 ∧ xs'[b + 1]? = some x1 ∧ xs'[b + 2]? = some x2 ∧
      xs'[b + 3]? = some x3 ∧ xs'[b + 4]? = some x4 ∧ xs'[b + 5]? = some x5 ∧
      xs'[b + 6]? = some x6) := by
  intro xs'
  refine ⟨by simp [xs'], fun t ht => ?_, fun hbd => ?_⟩
  · have h0 : t ≠ b := by omega
    have h1 : t ≠ b + 1 := by omega
    have h2 : t ≠ b + 2 := by omega
    have h3 : t ≠ b + 3 := by omega
    have h4 : t ≠ b + 4 := by omega
    have h5 : t ≠ b + 5 := by omega
    have h6 : t ≠ b + 6 := by omega
    simp only [xs']
    rw [List.getElem?_set_ne h6.symm, List.getElem?_set_ne h5.symm,
      List.getElem?_set_ne h4.symm, List.getElem?_set_ne h3.symm,
      List.getElem?_set_ne h2.symm, List.getElem?_set_ne h1.symm,
      List.getElem?_set_ne h0.symm]
  · simp only [xs']
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
        List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
        List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
        List.getElem?_set_self (by omega)]
    · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
        List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
        List.getElem?_set_ne (by omega), List.getElem?_set_self (by simp; omega)]
    · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
        List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
        List.getElem?_set_self (by simp; omega)]
    · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
        List.getElem?_set_ne (by omega), List.getElem?_set_self (by simp; omega)]
    · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
        List.getElem?_set_self (by simp; omega)]
    · rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by simp; omega)]
    · rw [List.getElem?_set_self (by simp; omega)]

private theorem ht_update_slot_ok {F : CNF Nat} {cv ht_cap k : Nat}
    {scr tmp : List (BitVec 32)} {slot : Nat} {smask : BitVec 32}
    (hht : XorHtInv F cv ht_cap scr) (hslot : slot < ht_cap) (hcap : 7 * ht_cap ≤ scr.length)
    (hk3 : 3 ≤ k) (hk5 : k ≤ 5) (hk_tmp : k ≤ tmp.length)
    (hsm_lt32 : smask.toNat < 32)
    (hclause_eq : xorMaskClause ((tmp.take k).map fun x => x.toNat / 2) smask.toNat =
      (tmp.take k).map BitVec.toNat)
    (hEntails : F.EntailsClause (cnfClause ((tmp.take k).map BitVec.toNat)))
    (hsk_k : (scr[slot * 7]?.getD 0#32).toNat = k)
    (hvs_eq : ∀ i < k, (scr[slot * 7 + 2 + i]?.getD 0#32).toNat = (tmp[i]?.getD 0#32).toNat / 2) :
    let old_seen := scr[slot * 7 + 1]?.getD 0#32
    let scr' := scr.set (slot * 7 + 1) (old_seen ||| (1#32 <<< smask))
    scr'.length = scr.length ∧
    (∀ i, 7 * ht_cap ≤ i → scr'[i]? = scr[i]?) ∧
    XorHtInv F cv ht_cap scr' := by
  intro old_seen scr'
  refine ⟨by simp [scr'], fun i hi => by simp only [scr']; rw [List.getElem?_set_ne (by omega)], ?_⟩
  intro s hs
  by_cases heq : s = slot
  · subst heq
    have hsk' : scr'[s * 7]?.getD 0#32 = scr[s * 7]?.getD 0#32 := by
      simp only [scr']; rw [List.getElem?_set_ne (by omega)]
    have hvs_same : (List.range (scr'[s * 7]?.getD 0#32).toNat).map
        (fun i => (scr'[s * 7 + 2 + i]?.getD 0#32).toNat) =
        (List.range (scr[s * 7]?.getD 0#32).toNat).map
        (fun i => (scr[s * 7 + 2 + i]?.getD 0#32).toNat) := by
      rw [hsk']
      refine List.map_congr_left fun i _ => ?_
      simp only [scr']; rw [List.getElem?_set_ne (by omega)]
    have hvs_tmp : (List.range (scr[s * 7]?.getD 0#32).toNat).map
        (fun i => (scr[s * 7 + 2 + i]?.getD 0#32).toNat) =
        (tmp.take k).map fun x => x.toNat / 2 := by
      rw [hsk_k]
      apply List.ext_getElem
      · simp [List.length_map, List.length_range, List.length_take, Nat.min_eq_left hk_tmp]
      · intro i hi1 _
        rw [List.length_map, List.length_range] at hi1
        simp only [List.getElem_map, List.getElem_range, List.getElem_take]
        rw [hvs_eq i hi1, List.getElem?_eq_getElem (by omega), Option.getD_some]
    rcases hht s hslot with hz | ⟨h3, h5, hss, hltv, hseen⟩
    · omega
    · dsimp only
      rw [hvs_same]
      rw [hsk']
      refine Or.inr ⟨h3, h5, ?_⟩
      refine ⟨hss, hltv, fun m' hm' hbit => ?_⟩
      have hseen' : scr'[s * 7 + 1]?.getD 0#32 = old_seen ||| (1#32 <<< smask) := by
        simp only [scr']; rw [List.getElem?_set_self (by omega), Option.getD_some]
      rw [hseen', BitVec.getLsbD_or] at hbit
      rcases Bool.or_eq_true _ _ |>.mp hbit with hold | hnew
      · exact hseen m' hm' hold
      · rw [bv32_getLsbD_shiftLeft_one hsm_lt32] at hnew
        have hmeq : m' = smask.toNat := of_decide_eq_true hnew
        subst hmeq
        rw [hvs_tmp, hclause_eq]; exact hEntails
  · have hs_same : ∀ i < 7, scr'[s * 7 + i]? = scr[s * 7 + i]? := fun i hi => by
      simp only [scr']; rw [List.getElem?_set_ne (fun h => heq (by omega))]
    dsimp only
    have hs0 := hs_same 0 (by decide)
    simp only [Nat.add_zero] at hs0
    rw [hs0]
    rcases hht s hs with hz | ⟨h3, h5, hss, hltv, hseen⟩
    · exact Or.inl hz
    · refine Or.inr ⟨h3, h5, ?_⟩
      have hvs_same : (List.range (scr[s * 7]?.getD 0#32).toNat).map
          (fun i => (scr'[s * 7 + 2 + i]?.getD 0#32).toNat) =
          (List.range (scr[s * 7]?.getD 0#32).toNat).map
          (fun i => (scr[s * 7 + 2 + i]?.getD 0#32).toNat) := by
        refine List.map_congr_left fun i hi => ?_
        have him : 2 + i < 7 := by have := List.mem_range.mp hi; omega
        have hsi := hs_same (2 + i) him
        rw [← Nat.add_assoc] at hsi
        rw [hsi]
      rw [hvs_same, hs_same 1 (by decide)]
      exact ⟨hss, hltv, hseen⟩


private theorem ht_get_of_idx {scr : List (BitVec 32)} {i j : Nat} {val : BitVec 32}
    (hidx : i = j) (hj : j < scr.length)
    (heq : scr[i]'(by rw [hidx]; exact hj) = val) :
    scr[j]?.getD 0#32 = val := by
  have hi : i < scr.length := by rw [hidx]; exact hj
  have hget : scr[j]? = scr[i]? := congrArg (fun k => scr[k]?) hidx.symm
  rw [hget, List.getElem?_eq_getElem hi, Option.getD_some]
  exact heq

theorem full_xor_ht_insert_wp (Γ : Env) :
    ∀ a m Q X, fullXorHtInsertSpec a m Q X →
      Func.wp Γ full_xor_ht_insert_body a m Q X := by
  rintro ⟨scr_ptr, tmp_ptr, ht_cap, used, k, ⟨⟩⟩ m0 Q X
    ⟨F, cv, scr, tmp, R, hcap_bd, hscr32, hk_tmp, htmp32, ⟨hk3, hk5⟩, hcv_tmp, hss_tmp,
     hEntails, hht, hm0, hQ⟩
  by_cases hcap0 : ht_cap = 0#64
  · subst hcap0
    c0_hsteps
    exact hQ used scr m0 rfl (fun _ _ => rfl) hht hm0
  · have hcap_pos : 0 < ht_cap.toNat := by bv_omega
    have hcap_lt : ht_cap.toNat < 2 ^ 30 := by omega
    c0_hsplit
    · exfalso; bv_omega
    · c0_hsplit
      · exfalso; bv_omega
      · c0_hsplit
        · exfalso; bv_omega
        · have h0_tmp : (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 0)).toNat < tmp.length := by
            rw [show (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 0)).toNat = 0 from rfl]; omega
          have h1_tmp : (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 1)).toNat < tmp.length := by
            rw [show (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 1)).toNat = 1 from rfl]; omega
          have h2_tmp : (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 2)).toNat < tmp.length := by
            rw [show (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 2)).toNat = 2 from rfl]; omega
          c0_hstraight!
          let v0 : BitVec 32 :=
            (tmp[(BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 0)).toNat]'h0_tmp) >>> (1 : BitVec 32)
          let v1 : BitVec 32 :=
            (tmp[(BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 1)).toNat]'h1_tmp) >>> (1 : BitVec 32)
          let v2 : BitVec 32 :=
            (tmp[(BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 2)).toNat]'h2_tmp) >>> (1 : BitVec 32)
          have hv0 : v0.toNat = (tmp[0]?.getD 0#32).toNat / 2 := by
            have h0eq :
                tmp[(BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 0)).toNat]'h0_tmp =
                  tmp[0]'(by omega) := rfl
            dsimp [v0]; rw [h0eq, List.getElem?_eq_getElem (by omega), Option.getD_some]; bv_omega
          have hv1 : v1.toNat = (tmp[1]?.getD 0#32).toNat / 2 := by
            have h1eq :
                tmp[(BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 1)).toNat]'h1_tmp =
                  tmp[1]'(by omega) := rfl
            dsimp [v1]; rw [h1eq, List.getElem?_eq_getElem (by omega), Option.getD_some]; bv_omega
          have hv2 : v2.toNat = (tmp[2]?.getD 0#32).toNat / 2 := by
            have h2eq :
                tmp[(BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 2)).toNat]'h2_tmp =
                  tmp[2]'(by omega) := rfl
            dsimp [v2]; rw [h2eq, List.getElem?_eq_getElem (by omega), Option.getD_some]; bv_omega
          refine wp_join_state1 (fun st : Val i32 => st)
            (fun v3 mj => (4 ≤ k.toNat → v3.toNat = (tmp[3]?.getD 0#32).toNat / 2) ∧ mj = m0)
            ?_ ?_
          · intro J1 v3 m1 ⟨hv3, hm1_eq⟩
            subst m1
            c0_hstraight
            refine wp_join_state1 (fun st : Val i32 => st)
              (fun v4 mj => (5 ≤ k.toNat → v4.toNat = (tmp[4]?.getD 0#32).toNat / 2) ∧ mj = m0)
              ?_ ?_
            · intro J2 v4 m2 ⟨hv4, hm2_eq⟩
              subst m2
              c0_hstraight
              refine wp_loop_inv
                (fun (smask, si, ()) ms =>
                  si.toNat ≤ k.toNat ∧
                  (∀ i < si.toNat, smask.getLsbD i = ((tmp[i]?.getD 0#32).toNat % 2 == 1)) ∧
                  (∀ i, si.toNat ≤ i → i < 32 → smask.getLsbD i = false) ∧
                  ms = m0)
                (fun (_, si, ()) _ => k.toNat - si.toNat)
                (fun J3 hJ3 => by
                  c0_hstraight
                  exact hJ3 (0#32, 0#32, ()) m0
                    ⟨Nat.zero_le _, fun _ hi => absurd hi (Nat.not_lt_zero _),
                    fun i _ _ => BitVec.getLsbD_zero, rfl⟩)
                (fun J3 (smask, si, ()) ms ⟨hsi_le, hbits_i, hhi_i, hms_eq⟩ ih3 => ?_)
              subst ms
              c0_hsplit
              · have hsi_lt : si.toNat < k.toNat := by bv_omega
                have hsi_len : si.toNat < tmp.length := by omega
                have hsi_z : (si.setWidth 64).toNat = si.toNat := bv_zext32_toNat si
                have hsi_32 : si.toNat < 32 := by omega
                have hsi_succ : (si + 1#32).toNat = si.toNat + 1 := by bv_omega
                c0_hstraight
                refine wp_join_state1 (fun st : Val i32 => st)
                  (fun sm' m3 =>
                    (∀ i < si.toNat + 1, sm'.getLsbD i = ((tmp[i]?.getD 0#32).toNat % 2 == 1)) ∧
                    (∀ i, si.toNat + 1 ≤ i → i < 32 → sm'.getLsbD i = false) ∧ m3 = m0)
                  ?_ ?_
                · intro J4 sm' m3 ⟨hb', hhi', hm3_eq⟩
                  c0_hstraight
                  exact ih3 (sm', si + 1#32, ()) m3 (by dsimp only; omega)
                    ⟨by omega, by simpa [hsi_succ] using hb',
                     by simpa [hsi_succ] using hhi', hm3_eq⟩
                · intro J4 hJ4
                  c0_hsplit
                  · c0_hstraight
                    have hodd : ((tmp[si.toNat]?.getD 0#32).toNat % 2 == 1) = true := by
                      rw [List.getElem?_eq_getElem hsi_len, Option.getD_some]
                      have hne : (tmp[si.toNat]'hsi_len &&& 1#32) ≠ 0#32 := by bv_omega
                      have htn : (tmp[si.toNat]'hsi_len &&& 1#32).toNat ≠ 0 :=
                        fun h => hne (BitVec.eq_of_toNat_eq (by simpa using h))
                      rw [bv32_and_one_toNat] at htn
                      have : (tmp[si.toNat]'hsi_len).toNat % 2 = 1 := by omega
                      simp [this]
                    have hsh_mod : (1 : BitVec 32) <<< (si.toNat % 32) = 1#32 <<< si := by
                      rw [Nat.mod_eq_of_lt hsi_32]; rfl
                    refine hJ4 (smask ||| ((1 : BitVec 32) <<< (si.toNat % 32))) m0 ⟨?_, ?_, rfl⟩
                    · intro i hi
                      rw [hsh_mod, BitVec.getLsbD_or, bv32_getLsbD_shiftLeft_one hsi_32]
                      rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with hil | rfl
                      · have hne : decide (i = si.toNat) = false := by
                          simp [show i ≠ si.toNat by omega]
                        rw [hne, Bool.or_false, hbits_i i hil]
                      · simp [hodd]
                    · intro i hi1 hi2
                      rw [hsh_mod, BitVec.getLsbD_or, bv32_getLsbD_shiftLeft_one hsi_32,
                        hhi_i i (by omega) hi2, Bool.false_or]
                      simp [show i ≠ si.toNat by omega]
                  · c0_hstraight
                    have heven : ((tmp[si.toNat]?.getD 0#32).toNat % 2 == 1) = false := by
                      rw [List.getElem?_eq_getElem hsi_len, Option.getD_some]
                      have heq0 : (tmp[si.toNat]'hsi_len &&& 1#32) = 0#32 := by bv_omega
                      have htn : (tmp[si.toNat]'hsi_len &&& 1#32).toNat = 0 := by rw [heq0]; rfl
                      rw [bv32_and_one_toNat] at htn
                      simp [htn]
                    refine hJ4 smask m0 ⟨?_, fun i hi1 hi2 => hhi_i i (by omega) hi2, rfl⟩
                    intro i hi
                    rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with hil | rfl
                    · exact hbits_i i hil
                    · rw [hhi_i si.toNat (Nat.le_refl _) hsi_32, heven]
              · have hsi_eq : si.toNat = k.toNat := by bv_omega
                have hsm_lt : smask.toNat < 2 ^ k.toNat :=
                  bv32_lt_two_pow_of_msb (by omega) fun i hi1 hi2 => hhi_i i (by omega) hi2
                have hsm_lt32 : smask.toNat < 32 := by
                  have : 2 ^ k.toNat ≤ 2 ^ 5 := Nat.pow_le_pow_right (by decide) hk5
                  omega
                have hsm_bits :
                    ∀ i < k.toNat, smask.getLsbD i = ((tmp[i]?.getD 0#32).toNat % 2 == 1) :=
                  fun i hi => hbits_i i (by omega)
                have hclause_eq :
                    xorMaskClause ((tmp.take k.toNat).map fun x => x.toNat / 2) smask.toNat =
                    (tmp.take k.toNat).map BitVec.toNat :=
                  xorMaskClause_of_tmp hk_tmp hk5 hsm_lt hsm_bits
                c0_hstraight
                obtain ⟨gv0, hgv0_eq⟩ : ∃ x : Val i32,
                    tmp[(BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 0)).toNat] >>>
                      OfNat.ofNat 1 = x := ⟨_, rfl⟩
                obtain ⟨gv1, hgv1_eq⟩ : ∃ x : Val i32,
                    tmp[(BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 1)).toNat] >>>
                      OfNat.ofNat 1 = x := ⟨_, rfl⟩
                obtain ⟨gv2, hgv2_eq⟩ : ∃ x : Val i32,
                    tmp[(BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 2)).toNat] >>>
                      OfNat.ofNat 1 = x := ⟨_, rfl⟩
                rw [hgv0_eq, hgv1_eq, hgv2_eq]
                obtain ⟨hval, hhval_eq⟩ : ∃ x : Val i64,
                    (BitVec.setWidth 64 gv0 * 2654435761 ^^^
                      BitVec.setWidth 64 gv1 * 2246822519 ^^^
                      BitVec.setWidth 64 gv2 * 3266489917 ^^^
                      BitVec.setWidth 64 v3 * 668265263 ^^^
                      BitVec.setWidth 64 v4 * 374761393) = x := ⟨_, rfl⟩
                obtain ⟨mask, hmask_eq⟩ : ∃ x : Val i64, ht_cap - 1 = x := ⟨_, rfl⟩
                obtain ⟨max_slots, hmax_eq⟩ :
                    ∃ x : Val i64, (ht_cap * 3) >>> OfNat.ofNat 2 = x := ⟨_, rfl⟩
                rw [hhval_eq, hmask_eq, hmax_eq]
                have hgv0_nat : gv0.toNat = (tmp[0]?.getD 0#32).toNat / 2 := by
                  rw [← hgv0_eq]; exact hv0
                have hgv1_nat : gv1.toNat = (tmp[1]?.getD 0#32).toNat / 2 := by
                  rw [← hgv1_eq]; exact hv1
                have hgv2_nat : gv2.toNat = (tmp[2]?.getD 0#32).toNat / 2 := by
                  rw [← hgv2_eq]; exact hv2
                clear v0 v1 v2 hv0 hv1 hv2
                refine wp_loop_inv
                  (fun (probe, ()) mp => probe.toNat ≤ 64 ∧ mp = m0)
                  (fun (probe, ()) _ => 64 - probe.toNat)
                  (fun Jp hJp => by c0_hstraight; exact hJp (0#64, ()) m0 ⟨Nat.zero_le _, rfl⟩)
                  (fun Jp (probe, ()) mp ⟨hp_le, hmp_eq⟩ ihp => ?_)
                c0_hsplit
                · have hp_lt : probe.toNat < 64 := by bv_omega
                  subst mp
                  c0_hstraight
                  let slot : BitVec 64 := (hval + probe) &&& mask
                  have hslot_lt : slot.toNat < ht_cap.toNat := by
                    dsimp only [slot]; rw [← hmask_eq]; exact bv64_land_sub1_lt _ ht_cap hcap_pos
                  have hsb_mul : (slot * 7#64).toNat = slot.toNat * 7 := by bv_omega
                  have hsb_bd : slot.toNat * 7 + 6 < scr.length := by omega
                  have hsb0_len : (slot * 7#64).toNat < scr.length := by omega
                  have hsb1_len : (slot * 7#64 + 1#64).toNat < scr.length :=
                    bv64_mul7_add_lt hsb_mul (by decide) hsb_bd hscr32
                  have hsb2_len : (slot * 7#64 + 2#64).toNat < scr.length :=
                    bv64_mul7_add_lt hsb_mul (by decide) hsb_bd hscr32
                  have hsb3_len : (slot * 7#64 + 3#64).toNat < scr.length :=
                    bv64_mul7_add_lt hsb_mul (by decide) hsb_bd hscr32
                  have hsb4_len : (slot * 7#64 + 4#64).toNat < scr.length :=
                    bv64_mul7_add_lt hsb_mul (by decide) hsb_bd hscr32
                  have hsb5_len : (slot * 7#64 + 5#64).toNat < scr.length :=
                    bv64_mul7_add_lt hsb_mul (by decide) hsb_bd hscr32
                  have hsb6_len : (slot * 7#64 + 6#64).toNat < scr.length :=
                    bv64_mul7_add_lt hsb_mul (by decide) hsb_bd hscr32
                  c0_hsplit
                  · c0_hsplit
                    · let bit : BitVec 32 := (1 : BitVec 32) <<< (smask.toNat % 32)
                      let scr1 := scr.set (slot * 7#64).toNat k
                      let scr2 := scr1.set (slot * 7#64 + 1#64).toNat bit
                      let scr3 := scr2.set (slot * 7#64 + 2#64).toNat gv0
                      let scr4 := scr3.set (slot * 7#64 + 3#64).toNat gv1
                      let scr5 := scr4.set (slot * 7#64 + 4#64).toNat gv2
                      let scr6 := scr5.set (slot * 7#64 + 5#64).toNat v3
                      have hsb1' : (slot * 7#64 + 1#64).toNat < scr1.length := by
                        simp only [scr1, List.length_set]; exact hsb1_len
                      have hsb2' : (slot * 7#64 + 2#64).toNat < scr2.length := by
                        simp only [scr2, scr1, List.length_set]; exact hsb2_len
                      have hsb3' : (slot * 7#64 + 3#64).toNat < scr3.length := by
                        simp only [scr3, scr2, scr1, List.length_set]; exact hsb3_len
                      have hsb4' : (slot * 7#64 + 4#64).toNat < scr4.length := by
                        simp only [scr4, scr3, scr2, scr1, List.length_set]; exact hsb4_len
                      have hsb5' : (slot * 7#64 + 5#64).toNat < scr5.length := by
                        simp only [scr5, scr4, scr3, scr2, scr1, List.length_set]; exact hsb5_len
                      have hsb6' : (slot * 7#64 + 6#64).toNat < scr6.length := by
                        simp only [scr6, scr5, scr4, scr3, scr2, scr1, List.length_set]
                        exact hsb6_len
                      c0_hstraight
                      have hbit_eq : bit = 1#32 <<< smask := by
                        dsimp [bit]; rw [Nat.mod_eq_of_lt hsm_lt32]
                      let scr' := ((((((scr.set (slot.toNat * 7) k).set
                        (slot.toNat * 7 + 1) bit).set (slot.toNat * 7 + 2) gv0).set
                        (slot.toNat * 7 + 3) gv1).set (slot.toNat * 7 + 4) gv2).set
                        (slot.toNat * 7 + 5) v3).set (slot.toNat * 7 + 6) v4
                      have hok_ins := ht_insert_empty_ok hht hslot_lt hcap_bd hk3 hk5 hk_tmp
                        hsm_lt32 hbit_eq hgv0_nat hgv1_nat hgv2_nat hv3 hv4 hcv_tmp
                        hss_tmp hclause_eq hEntails
                      dsimp only at hok_ins
                      rcases hok_ins with ⟨hscr'_len, hscr'_out2, hht'⟩
                      rw [Std.ExtHashMap.sep_emp] at hm
                      have hm7 := star_array_congr (b := scr') ?_ hm
                      · have hm7' :
                            (array (t := i32) scr_ptr scr' ⋆
                              array (t := i32) tmp_ptr tmp ⋆ R) m := by
                          ecancel
                        exact hQ (used + 1#64) scr' m hscr'_len hscr'_out2 hht' hm7'
                      · apply list_set7_slot_eq hsb_mul (by omega) <;>
                          first | rfl | exact hbit_eq.symm | bv_omega
                    · c0_hstraight
                      exact hQ used scr m0 rfl (fun _ _ => rfl) hht hm0
                  · c0_hstraight
                    refine wp_join0 (fun mj => mj = m0)
                      (fun J mj hmj => by
                        subst mj; c0_hstraight
                        exact ihp (probe + 1#64, ()) m0 (by dsimp only; bv_omega)
                          ⟨by bv_omega, rfl⟩)
                      (fun J hJ => ?_)
                    have hslot_c0 :
                        ((BitVec.toNat hval + BitVec.toNat probe) % 2 ^ 64 &&&
                          BitVec.toNat mask) = slot.toNat := by
                      dsimp only [slot]; rw [BitVec.toNat_and, BitVec.toNat_add]
                    have hsb0_c0 :
                        ((BitVec.toNat hval + BitVec.toNat probe) % 2 ^ 64 &&&
                          BitVec.toNat mask) *
                        BitVec.toNat (7 : BitVec 64) % 2 ^ 64 = slot.toNat * 7 := by
                      rw [hslot_c0]; exact hsb_mul
                    have hsb1_c0 :
                        (((BitVec.toNat hval + BitVec.toNat probe) % 2 ^ 64 &&&
                          BitVec.toNat mask) *
                        BitVec.toNat (7 : BitVec 64) % 2 ^ 64 +
                          BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 = slot.toNat * 7 + 1 := by
                      rw [hsb0_c0, show BitVec.toNat (1 : BitVec 64) = 1 from rfl,
                        Nat.mod_eq_of_lt (by omega)]
                    have hsb2_c0 :
                        (((BitVec.toNat hval + BitVec.toNat probe) % 2 ^ 64 &&&
                          BitVec.toNat mask) *
                        BitVec.toNat (7 : BitVec 64) + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64 =
                        slot.toNat * 7 + 2 := by
                      rw [hslot_c0, show BitVec.toNat (7 : BitVec 64) = 7 from rfl,
                        show BitVec.toNat (2 : BitVec 64) = 2 from rfl, Nat.mod_eq_of_lt (by omega)]
                    have hsb3_c0 :
                        (((BitVec.toNat hval + BitVec.toNat probe) % 2 ^ 64 &&&
                          BitVec.toNat mask) *
                        BitVec.toNat (7 : BitVec 64) + BitVec.toNat (3 : BitVec 64)) % 2 ^ 64 =
                        slot.toNat * 7 + 3 := by
                      rw [hslot_c0, show BitVec.toNat (7 : BitVec 64) = 7 from rfl,
                        show BitVec.toNat (3 : BitVec 64) = 3 from rfl, Nat.mod_eq_of_lt (by omega)]
                    have hsb4_c0 :
                        (((BitVec.toNat hval + BitVec.toNat probe) % 2 ^ 64 &&&
                          BitVec.toNat mask) *
                        BitVec.toNat (7 : BitVec 64) + BitVec.toNat (4 : BitVec 64)) % 2 ^ 64 =
                        slot.toNat * 7 + 4 := by
                      rw [hslot_c0, show BitVec.toNat (7 : BitVec 64) = 7 from rfl,
                        show BitVec.toNat (4 : BitVec 64) = 4 from rfl, Nat.mod_eq_of_lt (by omega)]
                    have hsb5_c0 :
                        (((BitVec.toNat hval + BitVec.toNat probe) % 2 ^ 64 &&&
                          BitVec.toNat mask) *
                        BitVec.toNat (7 : BitVec 64) + BitVec.toNat (5 : BitVec 64)) % 2 ^ 64 =
                        slot.toNat * 7 + 5 := by
                      rw [hslot_c0, show BitVec.toNat (7 : BitVec 64) = 7 from rfl,
                        show BitVec.toNat (5 : BitVec 64) = 5 from rfl, Nat.mod_eq_of_lt (by omega)]
                    have hsb6_c0 :
                        (((BitVec.toNat hval + BitVec.toNat probe) % 2 ^ 64 &&&
                          BitVec.toNat mask) *
                        BitVec.toNat (7 : BitVec 64) + BitVec.toNat (6 : BitVec 64)) % 2 ^ 64 =
                        slot.toNat * 7 + 6 := by
                      rw [hslot_c0, show BitVec.toNat (7 : BitVec 64) = 7 from rfl,
                        show BitVec.toNat (6 : BitVec 64) = 6 from rfl, Nat.mod_eq_of_lt (by omega)]
                    c0_hsplit
                    · have hc_k := hc; clear hc
                      c0_hsplit
                      · have hc_v0 := hc; clear hc
                        c0_hsplit
                        · have hc_v1 := hc; clear hc
                          c0_hsplit
                          · have hc_v2 := hc; clear hc
                            have hsk_m : scr[slot.toNat * 7]?.getD 0#32 = k :=
                              ht_get_of_idx hsb0_c0 (by omega) hc_k
                            have hv0_m : scr[slot.toNat * 7 + 2]?.getD 0#32 = gv0 :=
                              ht_get_of_idx hsb2_c0 (by omega) hc_v0
                            have hv1_m : scr[slot.toNat * 7 + 3]?.getD 0#32 = gv1 :=
                              ht_get_of_idx hsb3_c0 (by omega) hc_v1
                            have hv2_m : scr[slot.toNat * 7 + 4]?.getD 0#32 = gv2 :=
                              ht_get_of_idx hsb4_c0 (by omega) hc_v2
                            refine wp_join0
                              (fun mj => mj = m0 ∧
                                (4 ≤ k.toNat → scr[slot.toNat * 7 + 5]?.getD 0#32 = v3))
                              (fun Jv3 mj ⟨hmj, hv3_m⟩ => ?_)
                              (fun Jv3 hJv3 => ?_)
                            · subst mj
                              refine wp_join0
                                (fun mk => mk = m0 ∧
                                  (5 ≤ k.toNat → scr[slot.toNat * 7 + 6]?.getD 0#32 = v4))
                                (fun Jv4 mk ⟨hmk, hv4_m⟩ => ?_)
                                (fun Jv4 hJv4 => ?_)
                              · subst mk
                                have h1_c0_lt :
                                    (((BitVec.toNat hval + BitVec.toNat probe) % 2 ^ 64 &&&
                                      BitVec.toNat mask) * BitVec.toNat (7 : BitVec 64) % 2 ^ 64 +
                                      BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 < scr.length := by
                                  rw [hsb1_c0]; omega
                                c0_hstraight!
                                have hbit_eq :
                                    (1 : BitVec 32) <<< (smask.toNat % 32) = 1#32 <<< smask := by
                                  rw [Nat.mod_eq_of_lt hsm_lt32]; rfl
                                have hupd :=
                                  ht_update_slot_ok hht hslot_lt hcap_bd hk3 hk5 hk_tmp hsm_lt32
                                  hclause_eq hEntails (by rw [hsk_m]) (fun i hi => by
                                    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with
                                      rfl | rfl | rfl | rfl | rfl
                                    · rw [hv0_m, hgv0_nat]
                                    · rw [hv1_m, hgv1_nat]
                                    · rw [hv2_m, hgv2_nat]
                                    · rw [hv3_m (by omega), hv3 (by omega)]
                                    · rw [hv4_m (by omega), hv4 (by omega)])
                                let scr' := scr.set (slot.toNat * 7 + 1)
                                  ((scr[slot.toNat * 7 + 1]?.getD 0#32) ||| (1#32 <<< smask))
                                rw [Std.ExtHashMap.sep_emp] at hm
                                have hm_s := star_array_congr (b := scr') ?_ hm
                                · have hm_s' : (array (t := i32) scr_ptr scr' ⋆
                                      array (t := i32) tmp_ptr tmp ⋆ R) m := by ecancel
                                  exact hQ used scr' m hupd.1 hupd.2.1 hupd.2.2 hm_s'
                                · dsimp only [scr']
                                  have h1_lt : slot.toNat * 7 + 1 < scr.length := by omega
                                  have hsb1_set :
                                      ((hval + probe &&& mask) * (7 : BitVec 64) +
                                        (1 : BitVec 64)).toNat = slot.toNat * 7 + 1 := by
                                    change (slot * 7#64 + 1#64).toNat = slot.toNat * 7 + 1
                                    exact (bv64_mul7_add_toNat slot hsb_mul 1#64
                                      (by decide) (by omega)).trans
                                      (congrArg (slot.toNat * 7 + ·)
                                        (show (1#64).toNat = 1 from rfl))
                                  refine congr (congrArg (List.set scr) hsb1_set) ?_
                                  rw [← hbit_eq]
                                  refine congrArg (· ||| (1 : BitVec 32) <<< (smask.toNat % 32)) ?_
                                  exact (ht_get_of_idx hsb1_set h1_lt rfl).symm
                              · c0_hsplit
                                · c0_hstraight
                                  exact hJv4 m0 ⟨rfl, fun h => absurd h (by bv_omega)⟩
                                · c0_hsplit
                                  · have hc_v4 := hc; clear hc
                                    c0_hstraight
                                    exact hJv4 m0
                                      ⟨rfl, fun _ => ht_get_of_idx hsb6_c0 (by omega) hc_v4⟩
                                  · c0_hstraight; exact hJ m0 rfl
                            · c0_hsplit
                              · c0_hstraight
                                exact hJv3 m0 ⟨rfl, fun h => absurd h (by bv_omega)⟩
                              · c0_hsplit
                                · have hc_v3 := hc; clear hc
                                  c0_hstraight
                                  exact hJv3 m0
                                    ⟨rfl, fun _ => ht_get_of_idx hsb5_c0 (by omega) hc_v3⟩
                                · c0_hstraight; exact hJ m0 rfl
                          · c0_hstraight; exact hJ m0 rfl
                        · c0_hstraight; exact hJ m0 rfl
                      · c0_hstraight; exact hJ m0 rfl
                    · c0_hstraight; exact hJ m0 rfl
                · c0_hstraight
                  exact hQ used scr mp rfl (fun _ _ => rfl) hht (by subst mp; exact hm0)
            · intro J2 hJ2
              c0_hsplit
              · have h4_len : 4 < tmp.length := by bv_omega
                c0_hstraight
                refine hJ2 (tmp[(4 : BitVec 64).toNat] >>> 1#32) m0 ⟨?_, rfl⟩
                intro _
                change ((tmp[4]'h4_len) >>> (1 : Nat)).toNat = (tmp[4]?.getD 0#32).toNat / 2
                rw [List.getElem?_eq_getElem h4_len, Option.getD_some, BitVec.toNat_ushiftRight,
                  Nat.shiftRight_eq_div_pow, Nat.pow_one]
              · c0_hstraight
                exact hJ2 0#32 m0 ⟨fun h => absurd h (by bv_omega), rfl⟩
          · intro J1 hJ1
            c0_hsplit
            · have h3_len : 3 < tmp.length := by bv_omega
              c0_hstraight
              refine hJ1 (tmp[(3 : BitVec 64).toNat] >>> 1#32) m0 ⟨?_, rfl⟩
              intro _
              change ((tmp[3]'h3_len) >>> (1 : Nat)).toNat = (tmp[3]?.getD 0#32).toNat / 2
              rw [List.getElem?_eq_getElem h3_len, Option.getD_some, BitVec.toNat_ushiftRight,
                Nat.shiftRight_eq_div_pow, Nat.pow_one]
            · c0_hstraight
              exact hJ1 0#32 m0 ⟨fun h => absurd h (by bv_omega), rfl⟩

/-! ## 4. Pool Compaction & 2-Way Merge `Func.wp` (`compact_pool`, `merge_two`) -/

private theorem mem_symDiffSorted_or :
    ∀ (n : Nat) (xs ys : List Nat), xs.length + ys.length ≤ n →
      ∀ x, x ∈ symDiffSorted xs ys → x ∈ xs ∨ x ∈ ys
  | 0, xs, ys, hn, x, hx => by
    have hxs : xs = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hys : ys = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hxs hys
    rw [symDiffSorted.eq_def] at hx
    exact nomatch hx
  | n + 1, [], ys, _, x, hx => by
    rw [symDiffSorted.eq_def] at hx
    exact Or.inr hx
  | n + 1, a :: as, [], _, x, hx => by
    rw [symDiffSorted.eq_def] at hx
    exact Or.inl hx
  | n + 1, a :: as, b :: bs, hn, x, hx => by
    rw [symDiffSorted.eq_def] at hx
    dsimp only at hx
    split at hx
    · rcases List.mem_cons.mp hx with rfl | hrest
      · exact Or.inl List.mem_cons_self
      · rcases mem_symDiffSorted_or n as (b :: bs)
          (by simp at hn ⊢; omega) x hrest with h1 | h2
        · exact Or.inl (List.mem_cons_of_mem _ h1)
        · exact Or.inr h2
    · split at hx
      · rcases List.mem_cons.mp hx with rfl | hrest
        · exact Or.inr List.mem_cons_self
        · rcases mem_symDiffSorted_or n (a :: as) bs
            (by simp at hn ⊢; omega) x hrest with h1 | h2
          · exact Or.inl h1
          · exact Or.inr (List.mem_cons_of_mem _ h2)
      · rcases mem_symDiffSorted_or n as bs
          (by simp at hn ⊢; omega) x hx with h1 | h2
        · exact Or.inl (List.mem_cons_of_mem _ h1)
        · exact Or.inr (List.mem_cons_of_mem _ h2)

private theorem bv32_getLsbD_false_of_lt {x : BitVec 32} {k i : Nat}
    (hx : x.toNat < 2 ^ k) (hi : k ≤ i) : x.getLsbD i = false := by
  simp only [BitVec.getLsbD, Nat.testBit, Nat.shiftRight_eq_div_pow]
  have hd : x.toNat / 2 ^ i = 0 :=
    Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) hi))
  simp [hd]

theorem bv32_shr31_le_one (x : BitVec 32) : (x >>> 31#32).toNat ≤ 1 := by
  change (x >>> (31 : Nat)).toNat ≤ 1
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have := x.isLt; omega

private theorem bv32_bit_lt15_true {b : Nat} (hb : b < 15) :
    (0x7FFF#32 : BitVec 32).getLsbD b = true := by
  have hc : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 ∨ b = 6 ∨ b = 7 ∨
      b = 8 ∨ b = 9 ∨ b = 10 ∨ b = 11 ∨ b = 12 ∨ b = 13 ∨ b = 14 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private theorem bv32_bit_ge15_false {b : Nat} (hb : 15 ≤ b) :
    (0x7FFF#32 : BitVec 32).getLsbD b = false :=
  bv32_getLsbD_false_of_lt (by decide) hb

private theorem bv32_bit_hi15_true {b : Nat} (hb : b < 15) :
    (0x7FFF0000#32 : BitVec 32).getLsbD (b + 16) = true := by
  have hc : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 ∨ b = 6 ∨ b = 7 ∨
      b = 8 ∨ b = 9 ∨ b = 10 ∨ b = 11 ∨ b = 12 ∨ b = 13 ∨ b = 14 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem xor_pack_hdr_fields (clen rbit31 : BitVec 32)
    (hlt : clen.toNat < 2 ^ 15) (hr : ∀ i < 31, rbit31.getLsbD i = false) :
    let nh := clen ||| (clen <<< 16#32) ||| rbit31
    ((nh >>> 16#32) &&& 0x7FFF#32).toNat = clen.toNat ∧
    (nh &&& 0xFFFF#32).toNat = clen.toNat ∧
    ((nh >>> 31#32) != 0#32) = rbit31.getLsbD 31 := by
  intro nh
  have hc_lt16 : ∀ i, 15 ≤ i → clen.getLsbD i = false := fun i hi =>
    bv32_getLsbD_false_of_lt hlt hi
  have hsh : ((nh >>> 16#32) &&& 0x7FFF#32) = clen := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    dsimp only [nh]
    rw [BitVec.getLsbD_and]
    by_cases h15 : i < 15
    · have h0x := bv32_bit_lt15_true h15
      have hr_f : rbit31[16 + i]'(by omega) = false :=
        (BitVec.getLsbD_eq_getElem (by omega)).symm.trans (hr (16 + i) (by omega))
      have hc_f : clen[16 + i]'(by omega) = false :=
        (BitVec.getLsbD_eq_getElem (by omega)).symm.trans (hc_lt16 (16 + i) (by omega))
      have hge16 : ¬ (16 + i < 16) := by omega
      have hlt32 : 16 + i < 32 := by omega
      simp [h0x, hr_f, hc_f, hge16, hlt32]
      exact (BitVec.getLsbD_eq_getElem hi).symm
    · have h0x := bv32_bit_ge15_false (b := i) (by omega)
      rw [h0x, Bool.and_false, hc_lt16 i (by omega)]
  have hlo : (nh &&& 0xFFFF#32) = clen := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [nh, BitVec.getLsbD_and, BitVec.getLsbD_or]
    by_cases h16 : i < 16
    · have h0x : (0xFFFF#32 : BitVec 32).getLsbD i = true := by
        have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨
            i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 := by omega
        rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      have hr_f : rbit31.getLsbD i = false := hr i (by omega)
      have hn16 : ¬ (16 ≤ i) := by omega
      simp [h0x, hr_f, hn16]
    · have h0x :=
        bv32_getLsbD_false_of_lt (k := 16) (i := i) (x := 0xFFFF#32) (by decide) (by omega)
      rw [h0x, Bool.and_false, hc_lt16 i (by omega)]
  have hbit31 : ((nh >>> 31#32) != 0#32) = rbit31.getLsbD 31 := by
    have hsh1 : (nh >>> 31#32).toNat ≤ 1 := bv32_shr31_le_one nh
    have hlsb0 : (nh >>> 31#32).getLsbD 0 = rbit31.getLsbD 31 := by
      have hc31 : clen[31] = false :=
        (BitVec.getLsbD_eq_getElem (by decide)).symm.trans (hc_lt16 31 (by omega))
      have hc15 : clen[15] = false :=
        (BitVec.getLsbD_eq_getElem (by decide)).symm.trans (hc_lt16 15 (by omega))
      simp [nh, hc31, hc15]
    rcases (by omega : (nh >>> 31#32).toNat = 0 ∨ (nh >>> 31#32).toNat = 1) with hz | ho
    · have heq : nh >>> 31#32 = 0#32 := BitVec.eq_of_toNat_eq hz
      rw [heq] at hlsb0 ⊢; simpa using hlsb0
    · have heq : nh >>> 31#32 = 1#32 := BitVec.eq_of_toNat_eq ho
      rw [heq] at hlsb0 ⊢; simpa using hlsb0
  refine ⟨congrArg BitVec.toNat hsh, congrArg BitVec.toNat hlo, hbit31⟩

theorem rbit31_and_msb (hdr : BitVec 32) :
    (∀ i < 31, (hdr &&& 0x80000000#32).getLsbD i = false) ∧
    ((hdr &&& 0x80000000#32).getLsbD 31 = ((hdr >>> 31#32) != 0#32)) := by
  constructor
  · intro i hi
    rw [BitVec.getLsbD_and]
    have hm : (0x80000000#32 : BitVec 32).getLsbD i = false := by
      simp only [BitVec.getLsbD, BitVec.toNat_ofNat]
      have : (2 ^ 31 : Nat).testBit i = false := by
        rw [Nat.testBit_two_pow]; simp [show 31 ≠ i by omega]
      simpa using this
    rw [hm, Bool.and_false]
  · rw [BitVec.getLsbD_and, show (0x80000000#32 : BitVec 32).getLsbD 31 = true from by decide,
      Bool.and_true]
    have hsh1 : (hdr >>> 31#32).toNat ≤ 1 := bv32_shr31_le_one hdr
    have hlsb : (hdr >>> 31#32).getLsbD 0 = hdr.getLsbD 31 := by simp
    rcases (by omega : (hdr >>> 31#32).toNat = 0 ∨ (hdr >>> 31#32).toNat = 1) with hz | ho
    · have heq : hdr >>> 31#32 = 0#32 := BitVec.eq_of_toNat_eq hz
      rw [heq] at hlsb ⊢; simpa using hlsb
    · have heq : hdr >>> 31#32 = 1#32 := BitVec.eq_of_toNat_eq ho
      rw [heq] at hlsb ⊢; simpa using hlsb

theorem rbit31_shl31 {b : BitVec 32} (hb : b.toNat ≤ 1) :
    (∀ i < 31, (b <<< 31#32).getLsbD i = false) ∧
    ((b <<< 31#32).getLsbD 31 = (b != 0#32)) := by
  rcases (by omega : b.toNat = 0 ∨ b.toNat = 1) with hz | ho
  · have : b = 0#32 := BitVec.eq_of_toNat_eq hz; subst this
    exact ⟨fun i hi => by simp, by decide⟩
  · have : b = 1#32 := BitVec.eq_of_toNat_eq ho; subst this
    exact ⟨fun i hi => by
      change (1#32 <<< (31 : Nat)).getLsbD i = false
      rw [BitVec.getLsbD_shiftLeft]; simp [show ¬ (31 ≤ i) by omega], by decide⟩

theorem bv32_xor_shr31_ne_zero (h1 h2 : BitVec 32) :
    (((h1 >>> 31#32) ^^^ (h2 >>> 31#32)) != 0#32) =
    (((h1 >>> 31#32) != 0#32) != ((h2 >>> 31#32) != 0#32)) := by
  have h1_le := bv32_shr31_le_one h1
  have h2_le := bv32_shr31_le_one h2
  rcases (by omega : (h1 >>> 31#32).toNat = 0 ∨ (h1 >>> 31#32).toNat = 1) with a0 | a1 <;>
  rcases (by omega : (h2 >>> 31#32).toNat = 0 ∨ (h2 >>> 31#32).toNat = 1) with b0 | b1
  · rw [@BitVec.eq_of_toNat_eq 32 _ 0#32 a0, @BitVec.eq_of_toNat_eq 32 _ 0#32 b0]; decide
  · rw [@BitVec.eq_of_toNat_eq 32 _ 0#32 a0, @BitVec.eq_of_toNat_eq 32 _ 1#32 b1]; decide
  · rw [@BitVec.eq_of_toNat_eq 32 _ 1#32 a1, @BitVec.eq_of_toNat_eq 32 _ 0#32 b0]; decide
  · rw [@BitVec.eq_of_toNat_eq 32 _ 1#32 a1, @BitVec.eq_of_toNat_eq 32 _ 1#32 b1]; decide

theorem bv32_stride_and_zero_low (h : BitVec 32) :
    (((h &&& 0x7FFF0000#32) >>> 16#32) &&& 0x7FFF#32) = ((h >>> 16#32) &&& 0x7FFF#32) := by
  apply BitVec.eq_of_getLsbD_eq; intro b hb
  rw [BitVec.getLsbD_and, BitVec.getLsbD_and]
  by_cases hb15 : b < 15
  · rw [show (h &&& 0x7FFF0000#32) >>> 16#32 = (h &&& 0x7FFF0000#32) >>> (16 : Nat) from rfl,
      show h >>> 16#32 = h >>> (16 : Nat) from rfl,
      BitVec.getLsbD_ushiftRight, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_and,
      bv32_bit_lt15_true hb15, Nat.add_comm 16 b, bv32_bit_hi15_true hb15, Bool.and_true,
      Bool.and_true]
  · rw [bv32_bit_ge15_false (b := b) (by omega), Bool.and_false, Bool.and_false]

theorem xorEqPoolOk_at_mem_poolStarts {F : CNF Nat} {cv : Nat} {scr : List (BitVec 32)}
    {eq_end : Nat} :
    ∀ {fuel p q : Nat}, XorEqPoolOk F cv scr eq_end p → q ∈ poolStarts scr eq_end p fuel →
      XorEqPoolOk F cv scr eq_end q
  | 0, _, _, _, hq => nomatch hq
  | fuel + 1, p, q, hx, hq => by
    cases hx with
    | done => unfold poolStarts at hq; simp at hq
    | @step p hdr st cl hp hhdr hst hcl hbd hbody hrest =>
      rw [poolStarts_step_iff hp] at hq
      have hst' : (((scr[p]?.getD 0#32) >>> 16#32) &&& 0x7FFF#32).toNat = st := by
        simp [hhdr, hst]
      rw [hst'] at hq
      rcases hq with rfl | ⟨_, hr⟩
      · exact .step hp hhdr hst hcl hbd hbody hrest
      · exact xorEqPoolOk_at_mem_poolStarts hrest hr

theorem list_range_map_succ {α : Type} (n : Nat) (f : Nat → α) :
    (List.range (n + 1)).map f = (List.range n).map f ++ [f n] := by
  rw [List.range_succ, List.map_append]; rfl

@[expose] def fullXorCompactPoolSpec : Spec [i64, i64] [i64] := fun (scr_ptr, eq_end, ()) m Q _ =>
  ∃ (F : CNF Nat) (cv : Nat) (scr : List (BitVec 32)) (R : Mem 64 → Prop),
    eq_end.toNat ≤ scr.length ∧ scr.length < 2 ^ 32 ∧
    XorEqPoolOk F cv scr eq_end.toNat 0 ∧
    (array (t := i32) scr_ptr scr ⋆ R) m ∧
    ∀ (out' : BitVec 64) (scr' : List (BitVec 32)) (m' : Mem 64),
      scr'.length = scr.length → out'.toNat ≤ eq_end.toNat →
      XorEqPoolOk F cv scr' out'.toNat 0 →
      (∀ i, eq_end.toNat ≤ i → scr'[i]? = scr[i]?) →
      (array (t := i32) scr_ptr scr' ⋆ R) m' → Q (out', ()) m'

theorem full_xor_compact_pool_wp (Γ : Env) :
    ∀ a m Q X, fullXorCompactPoolSpec a m Q X →
      Func.wp Γ full_xor_compact_pool_body a m Q X := by
  rintro ⟨scr_ptr, eq_end, ⟨⟩⟩ m0 Q X ⟨F, cv, scr, R, heq_len, hscr32, hpool0, hm0, hQ⟩
  c0_hstraight
  refine wp_join_state (fun x : Tup Val [i64, i64] => x)
    (fun (p, out, ()) m => ∃ scr_cur,
      out.toNat ≤ eq_end.toNat ∧ scr_cur.length = scr.length ∧
      XorEqPoolOk F cv scr_cur out.toNat 0 ∧
      (∀ i, eq_end.toNat ≤ i → scr_cur[i]? = scr[i]?) ∧
      (array (t := i32) scr_ptr scr_cur ⋆ R) m)
    ?_ ?_
  · intro J0 (p, out, ()) m ⟨scr_cur, hout_le, hlen, hpool, htail, hm⟩
    c0_hstraight
    exact hQ out scr_cur m hlen hout_le hpool htail hm
  · intro J0 hJ0
    refine wp_loop_inv
      (fun (p, out, ()) m => ∃ scr_cur,
        out.toNat ≤ p.toNat ∧ p.toNat ≤ eq_end.toNat ∧
        scr_cur.length = scr.length ∧
        (∀ i, p.toNat ≤ i → scr_cur[i]? = scr[i]?) ∧
        XorEqPoolOk F cv scr_cur out.toNat 0 ∧
        XorEqPoolOk F cv scr eq_end.toNat p.toNat ∧
        (array (t := i32) scr_ptr scr_cur ⋆ R) m)
      (fun (p, _, ()) _ => eq_end.toNat - p.toNat)
      (fun J hJ => by
        c0_hstraight
        exact hJ (0#64, 0#64, ()) m0 ⟨scr, Nat.zero_le _, Nat.zero_le _, rfl,
          fun _ _ => rfl, .done, hpool0, hm0⟩)
      (fun J (p, out, ()) m ⟨scr_cur, hout_le, hp_le, hlen_cur, htail_cur, hpool_out,
          hpool_p, hm_cur⟩ ih => ?_)
    c0_hsplit
    · have hp_lt : p.toNat < eq_end.toNat := by bv_omega
      generalize hp_nat : p.toNat = p_nat at hpool_p
      cases hpool_p with
      | done => rw [hp_nat] at hp_lt; exact absurd hp_lt (Nat.lt_irrefl _)
      | @step _ hdr stride clen _ hhdr hst hcl hbd hbody hrest =>
        rw [← hp_nat] at hhdr hbd hbody hrest
        have hp_len_cur : p.toNat < scr_cur.length := by omega
        have hcur_p : scr_cur[p.toNat]? = some hdr := by rw [htail_cur _ (Nat.le_refl _), hhdr]
        have hg_p : scr_cur[p.toNat]'hp_len_cur = hdr := by
          have := hcur_p; rw [List.getElem?_eq_getElem hp_len_cur] at this
          exact Option.some.inj this
        have hst_lt : stride < 2 ^ 15 := by
          rw [hst, BitVec.toNat_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
        c0_hstraight
        rw [hg_p]
        obtain ⟨cl32, hcl32⟩ : ∃ x : BitVec 32, hdr &&& 65535 = x := ⟨_, rfl⟩
        have hcl_eq : cl32.toNat = clen := by
          rw [← hcl32, show hdr &&& (65535 : BitVec 32) = hdr &&& 0xFFFF#32 from rfl, ← hcl]
        obtain ⟨wcl, hwcl⟩ : ∃ w : BitVec 64, cl32.setWidth 64 = w := ⟨_, rfl⟩
        have hcl_w : wcl.toNat = clen := by rw [← hwcl, bv_zext32_toNat, hcl_eq]
        obtain ⟨wst, hwst⟩ : ∃ w : BitVec 64, ((hdr >>> 16 &&& 32767).setWidth 64) = w := ⟨_, rfl⟩
        have hst_w : wst.toNat = stride := by
          rw [← hwst, bv_zext32_toNat,
            show (hdr >>> 16 &&& (32767 : BitVec 32)) = hdr >>> 16#32 &&& 0x7FFF#32 from rfl,
            ← hst]
        rw [hcl32, hwst]
        c0_hsplit
        · exfalso
          have : p.toNat + 1 + stride ≤ eq_end.toNat := hbd
          rw [← hst_w] at this; bv_omega
        · refine wp_join_state1 (fun st : Val i64 => st)
            (fun out' m' => ∃ scr',
              out'.toNat ≤ p.toNat + 1 + stride ∧
              scr'.length = scr.length ∧
              (∀ i, p.toNat + 1 + stride ≤ i → scr'[i]? = scr[i]?) ∧
              XorEqPoolOk F cv scr' out'.toNat 0 ∧
              (array (t := i32) scr_ptr scr' ⋆ R) m')
            ?_ ?_
          · intro J1 out' m' ⟨scr', hout'_le, hlen', htail', hpool', hm'⟩
            have hp_next : (p + 1#64 + wst).toNat = p.toNat + 1 + stride := by
              rw [← hst_w]; bv_omega
            c0_hstraight
            exact ih (p + 1#64 + wst, out', ()) m' (by dsimp only; omega)
              ⟨scr', by rw [hp_next]; exact hout'_le, by rw [hp_next]; exact hbd,
               hlen', fun i hi => htail' i (by rw [hp_next] at hi; exact hi),
               hpool', by rw [hp_next]; exact hrest, hm'⟩
          · intro J1 hJ1
            c0_hsplit
            · c0_hstraight; rw [hwcl]; c0_hsplit
              · rcases hbody with h0 | ⟨hpos, hcl_le, hss, hcv_vs, hsnd⟩
                · exfalso; rw [← hcl_eq] at h0; bv_omega
                · have hcl_15 : clen < 2 ^ 15 := by omega
                  let nh : BitVec 32 := cl32 ||| (cl32 <<< 16#32) ||| (hdr &&& 0x80000000#32)
                  have hout_len : out.toNat < scr_cur.length := by omega
                  c0_hstraight
                  let scr0 := scr_cur.set out.toNat nh
                  refine wp_loop_inv
                    (fun (i, ()) mi => ∃ scr_i,
                      i.toNat ≤ clen ∧
                      scr_i.length = scr.length ∧
                      (∀ k, k < out.toNat → scr_i[k]? = scr_cur[k]?) ∧
                      scr_i[out.toNat]? = some nh ∧
                      (∀ k, k < i.toNat → scr_i[out.toNat + 1 + k]? = scr[p.toNat + 1 + k]?) ∧
                      (∀ k, i.toNat ≤ k → k < clen →
                        scr_i[p.toNat + 1 + k]? = scr[p.toNat + 1 + k]?) ∧
                      (∀ k, p.toNat + 1 + stride ≤ k → scr_i[k]? = scr[k]?) ∧
                      (array (t := i32) scr_ptr scr_i ⋆ R) mi)
                    (fun (i, ()) _ => clen - i.toNat)
                    (fun J2 hJ2 => by
                      c0_hstraight
                      refine hJ2 (0#64, ()) _ ⟨scr0, Nat.zero_le _, by simp [scr0, hlen_cur],
                        fun k hk => List.getElem?_set_ne (by omega), ?_,
                        fun _ hk => absurd hk (Nat.not_lt_zero _),
                        fun k _ _ => by
                          rw [List.getElem?_set_ne (by omega), htail_cur _ (by omega)],
                        fun k hk => by rw [List.getElem?_set_ne (by omega), htail_cur _ (by omega)],
                        ?_⟩
                      · simp only [scr0, List.getElem?_set_self hout_len]
                      · simpa [scr0, nh] using hm)
                    (fun J2 (i, ()) mi ⟨scr_i, hi_le, hlen_i, hpre_i, hhdr_i, hcp_i, hsrc_i,
                        htail_i, hm_i⟩ ih2 => ?_)
                  c0_hsplit
                  · have hi_lt : i.toNat < clen := by rw [← hcl_w]; bv_omega
                    have hsrc_lt : p.toNat + 1 + i.toNat < scr_i.length := by omega
                    have hdst_lt : out.toNat + 1 + i.toNat < scr_i.length := by omega
                    have hp_idx : (p + 1 + i).toNat = p.toNat + 1 + i.toNat := by bv_omega
                    have hout_idx : (out + 1 + i).toNat = out.toNat + 1 + i.toNat := by bv_omega
                    c0_hstraight
                    let val := scr_i[p.toNat + 1 + i.toNat]'hsrc_lt
                    have hval_eq : some val = scr[p.toNat + 1 + i.toNat]? := by
                      rw [← hsrc_i i.toNat (Nat.le_refl _) hi_lt, List.getElem?_eq_getElem hsrc_lt]
                    simp only [hp_idx, hout_idx] at hm
                    refine ih2 (i + 1#64, ()) _ (by
                        dsimp only; have hi_s : (i + 1#64).toNat = i.toNat + 1 := by bv_omega
                        rw [hi_s]; omega)
                      ⟨scr_i.set (out.toNat + 1 + i.toNat) val, by bv_omega,
                       by simp [hlen_i],
                       fun k hk => by rw [List.getElem?_set_ne (by omega), hpre_i k hk],
                       by rw [List.getElem?_set_ne (by omega), hhdr_i],
                       fun k hk => by
                         have hk' : k < i.toNat + 1 := Nat.lt_of_lt_of_le hk (by
                           have hi_s : (i + 1#64).toNat = i.toNat + 1 := by bv_omega
                           omega)
                         rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hk') with hlt | rfl
                         · rw [List.getElem?_set_ne (by omega), hcp_i k hlt]
                         · rw [List.getElem?_set_self hdst_lt, hval_eq],
                       fun k hk1 hk2 => by
                         have hk1' : i.toNat + 1 ≤ k := Nat.le_trans (by
                           have hi_s : (i + 1#64).toNat = i.toNat + 1 := by bv_omega
                           omega) hk1
                         rw [List.getElem?_set_ne (by omega), hsrc_i k (by omega) hk2],
                       fun k hk => by rw [List.getElem?_set_ne (by omega), htail_i k hk],
                       hm⟩
                  · have hi_eq : i.toNat = clen := by rw [← hcl_w]; bv_omega
                    have hout_next : (out + 1 + wcl).toNat = out.toNat + 1 + clen := by
                      rw [← hcl_w]; bv_omega
                    have hfields := xor_pack_hdr_fields cl32 (hdr &&& 0x80000000#32)
                      (by rw [hcl_eq]; exact hcl_15) (rbit31_and_msb hdr).1
                    have hpool_pre : XorEqPoolOk F cv scr_i out.toNat 0 :=
                      xorEqPoolOk_congr hpool_out fun k _ hk => hpre_i k hk
                    have hvs_eq : (List.range clen).map
                          (fun k => (scr_i[out.toNat + 1 + k]?.getD 0#32).toNat) =
                        (List.range clen).map
                          (fun k => (scr[p.toNat + 1 + k]?.getD 0#32).toNat) := by
                      refine List.map_congr_left fun k hk => ?_
                      rw [hcp_i k (by rw [List.mem_range] at hk; omega)]
                    have hsnd' : XorVarsSound F
                        ((List.range clen).map fun k => (scr_i[out.toNat + 1 + k]?.getD 0#32).toNat)
                        ((nh >>> 31#32) != 0#32) := by
                      rw [hvs_eq, hfields.2.2, (rbit31_and_msb hdr).2]; exact hsnd
                    have hss' : List.Pairwise (· < ·)
                        ((List.range clen).map
                          fun k => (scr_i[out.toNat + 1 + k]?.getD 0#32).toNat) := by
                      rw [hvs_eq]; exact hss
                    have hcv' : ∀ v ∈ (List.range clen).map
                          (fun k => (scr_i[out.toNat + 1 + k]?.getD 0#32).toNat), v < cv := by
                      rw [hvs_eq]; exact hcv_vs
                    have hpool_app : XorEqPoolOk F cv scr_i (out.toNat + 1 + clen) 0 :=
                      xorEqPoolOk_append hpool_pre (by omega) hhdr_i
                        (by rw [hfields.1, hcl_eq]) (by rw [hfields.2.1, hcl_eq])
                        hpos hss' hcv' hsnd'
                    c0_hstraight
                    rw [hwcl]
                    exact hJ1 (out + 1 + wcl) mi
                      ⟨scr_i, by rw [hout_next]; omega, hlen_i, htail_i,
                       by rw [hout_next]; exact hpool_app, hm_i⟩
              · c0_hstraight
                exact hJ1 out m ⟨scr_cur, by omega, hlen_cur,
                  fun i hi => htail_cur i (by omega), hpool_out, hm_cur⟩
            · c0_hstraight
              exact hJ1 out m ⟨scr_cur, by omega, hlen_cur,
                fun i hi => htail_cur i (by omega), hpool_out, hm_cur⟩
    · have hp_eq : p.toNat = eq_end.toNat := by bv_omega
      c0_hstraight
      exact hJ0 (p, out, ()) m ⟨scr_cur, by omega, hlen_cur, hpool_out,
        fun i hi => htail_cur i (by omega), hm_cur⟩

private theorem merge_two_zero_pool {F : CNF Nat} {cv eq_end fuel1 fuel2 : Nat}
    {p1 p2 dst : BitVec 64} {gh1 gh2 : BitVec 32} {scr scr2 : List (BitVec 32)}
    (hp1_lt : p1.toNat < eq_end) (hp2_lt : p2.toNat < eq_end) (hp_ne : p1 ≠ p2)
    (hdst_eq : dst.toNat = eq_end)
    (hmem1 : p1.toNat ∈ poolStarts scr eq_end 0 fuel1)
    (hmem2 : p2.toNat ∈ poolStarts scr eq_end 0 fuel2)
    (hh1 : scr[p1.toNat]?.getD 0#32 = gh1) (hh2 : scr[p2.toNat]?.getD 0#32 = gh2)
    (hscr2_len : scr2.length = scr.length) (hscr_len : eq_end ≤ scr.length)
    (hpre2 : ∀ idx, idx ≤ dst.toNat → scr2[idx]? = scr[idx]?)
    (hpool0 : XorEqPoolOk F cv scr eq_end 0) :
    let scr_z1 := scr2.set p1.toNat (gh1 &&& 0x7FFF0000#32)
    let scr_z2 := scr_z1.set p2.toNat (gh2 &&& 0x7FFF0000#32)
    XorEqPoolOk F cv scr_z2 eq_end 0 ∧
    (∀ idx, idx < eq_end → (((scr_z2[idx]?.getD 0#32) >>> 16#32) &&& 0x7FFF#32) =
      (((scr[idx]?.getD 0#32) >>> 16#32) &&& 0x7FFF#32)) ∧
    (∀ idx, idx < eq_end → (scr_z2[idx]?.getD 0#32 &&& 0xFFFF#32) ≠ 0#32 →
      scr_z2[idx]? = scr[idx]?) := by
  intro scr_z1 scr_z2
  have hp_ne_nat : p1.toNat ≠ p2.toNat := fun h => hp_ne (BitVec.eq_of_toNat_eq h)
  have hp1_bd2 : p1.toNat < scr2.length := by omega
  have hp2_bd2 : p2.toNat < scr_z1.length := by simp [scr_z1]; omega
  have hpool_pre : XorEqPoolOk F cv scr2 eq_end 0 :=
    xorEqPoolOk_congr hpool0 fun idx _ hidx => hpre2 idx (by omega)
  have hstarts1 : p1.toNat ∈ poolStarts scr2 eq_end 0 fuel1 := by
    rw [poolStarts_congr (scr1 := scr) fun idx _ hidx => by rw [hpre2 idx (by omega)]]
    exact hmem1
  have hpool_z1 := xorEqPoolOk_zero_at hpool_pre hstarts1 (by omega)
  have hscr2_p1 : scr2[p1.toNat]?.getD 0#32 = gh1 := by
    rw [hpre2 _ (by omega), hh1]
  rw [hscr2_p1] at hpool_z1
  have hstarts2 : p2.toNat ∈ poolStarts scr_z1 eq_end 0 fuel2 := by
    rw [poolStarts_congr (scr1 := scr) fun idx _ hidx => ?_]
    · exact hmem2
    · by_cases hip : idx = p1.toNat
      · subst hip
        rw [show scr_z1[p1.toNat]?.getD 0#32 = gh1 &&& 0x7FFF0000#32 by
          simp [scr_z1, List.getElem?_set_self hp1_bd2]]
        rw [hh1, bv32_stride_and_zero_low]
      · rw [show scr_z1[idx]? = scr[idx]? by
          dsimp only [scr_z1]; rw [List.getElem?_set_ne (Ne.symm hip), hpre2 idx (by omega)]]
  have hpool_z2 := xorEqPoolOk_zero_at hpool_z1 hstarts2 (by rw [List.length_set]; omega)
  have hscr_z1_p2 : scr_z1[p2.toNat]?.getD 0#32 = gh2 := by
    dsimp only [scr_z1]
    rw [List.getElem?_set_ne hp_ne_nat, hpre2 _ (by omega), hh2]
  rw [hscr_z1_p2] at hpool_z2
  refine ⟨hpool_z2, ?_, ?_⟩
  · intro idx hidx
    by_cases h1 : idx = p1.toNat
    · subst h1
      rw [show scr_z2[p1.toNat]?.getD 0#32 = gh1 &&& 0x7FFF0000#32 by
        dsimp only [scr_z2, scr_z1]
        rw [List.getElem?_set_ne hp_ne_nat.symm, List.getElem?_set_self hp1_bd2]; rfl]
      rw [hh1, bv32_stride_and_zero_low]
    · by_cases h2 : idx = p2.toNat
      · subst h2
        rw [show scr_z2[p2.toNat]?.getD 0#32 = gh2 &&& 0x7FFF0000#32 by
          dsimp only [scr_z2]; rw [List.getElem?_set_self hp2_bd2]; rfl]
        rw [hh2, bv32_stride_and_zero_low]
      · rw [show scr_z2[idx]? = scr[idx]? by
          dsimp only [scr_z2, scr_z1]
          rw [List.getElem?_set_ne (Ne.symm h2), List.getElem?_set_ne (Ne.symm h1),
            hpre2 idx (by omega)]]
  · intro idx hidx hne
    by_cases h1 : idx = p1.toNat
    · subst h1; exfalso; apply hne
      rw [show scr_z2[p1.toNat]?.getD 0#32 = gh1 &&& 0x7FFF0000#32 by
        dsimp only [scr_z2, scr_z1]
        rw [List.getElem?_set_ne hp_ne_nat.symm, List.getElem?_set_self hp1_bd2]; rfl]
      rw [BitVec.and_assoc, show (0x7FFF0000#32 &&& 0xFFFF#32 : BitVec 32) = 0#32 from rfl,
        BitVec.and_zero]
    · by_cases h2 : idx = p2.toNat
      · subst h2; exfalso; apply hne
        rw [show scr_z2[p2.toNat]?.getD 0#32 = gh2 &&& 0x7FFF0000#32 by
          dsimp only [scr_z2]; rw [List.getElem?_set_self hp2_bd2]; rfl]
        rw [BitVec.and_assoc, show (0x7FFF0000#32 &&& 0xFFFF#32 : BitVec 32) = 0#32 from rfl,
          BitVec.and_zero]
      · dsimp only [scr_z2, scr_z1]
        rw [List.getElem?_set_ne (Ne.symm h2), List.getElem?_set_ne (Ne.symm h1),
          hpre2 idx (by omega)]

private theorem merge_two_pack_ok {F : CNF Nat} {cv eq_end : Nat}
    {p1 p2 dst out_n : BitVec 64} {gh1 gh2 : BitVec 32}
    {vs1 vs2 : List Nat} {scr scr2 : List (BitVec 32)}
    (ho_pos : 0 < out_n.toNat) (ho_bd : out_n.toNat ≤ 512)
    (hdst_eq : dst.toNat = eq_end) (hp1_lt : p1.toNat < eq_end) (hp2_lt : p2.toNat < eq_end)
    (hscr2_len : scr2.length = scr.length) (hbd_dst : dst.toNat + 1 + out_n.toNat ≤ scr.length)
    (hss1 : List.Pairwise (· < ·) vs1) (hss2 : List.Pairwise (· < ·) vs2)
    (hcv1 : ∀ v ∈ vs1, v < cv) (hcv2 : ∀ v ∈ vs2, v < cv)
    (hsym_vars : XorVarsSound F
      ((List.range out_n.toNat).map fun k => (scr2[dst.toNat + 1 + k]?.getD 0#32).toNat)
      (((gh1 >>> 31#32) ^^^ (gh2 >>> 31#32)) != 0#32))
    (hsym_eq : ((List.range out_n.toNat).map fun k => (scr2[dst.toNat + 1 + k]?.getD 0#32).toNat) =
      symDiffSorted vs1 vs2)
    (hpool_z2 : XorEqPoolOk F cv
      ((scr2.set p1.toNat (gh1 &&& 0x7FFF0000#32)).set p2.toNat (gh2 &&& 0x7FFF0000#32))
      eq_end 0) :
    let scr_z2 := (scr2.set p1.toNat (gh1 &&& 0x7FFF0000#32)).set p2.toNat (gh2 &&& 0x7FFF0000#32)
    let nr := (gh1 >>> 31#32) ^^^ (gh2 >>> 31#32)
    let nl := out_n.setWidth 32
    let nh_dst := nl ||| (nl <<< 16#32) ||| (nr <<< 31#32)
    let scr_f := scr_z2.set dst.toNat nh_dst
    XorEqPoolOk F cv scr_f (dst.toNat + 1 + out_n.toNat) 0 := by
  intro scr_z2 nr nl nh_dst scr_f
  have hdst_lt : dst.toNat < scr_z2.length := by simp [scr_z2, hscr2_len]; omega
  have hnl_eq : nl.toNat = out_n.toNat := by
    dsimp only [nl]; rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
  have hnr_le : nr.toNat ≤ 1 := by
    have h1_le := bv32_shr31_le_one gh1
    have h2_le := bv32_shr31_le_one gh2
    rcases (by omega : (gh1 >>> 31#32).toNat = 0 ∨ (gh1 >>> 31#32).toNat = 1) with a0 | a1 <;>
    rcases (by omega : (gh2 >>> 31#32).toNat = 0 ∨ (gh2 >>> 31#32).toNat = 1) with b0 | b1
    · dsimp only [nr]
      rw [@BitVec.eq_of_toNat_eq 32 _ 0#32 a0, @BitVec.eq_of_toNat_eq 32 _ 0#32 b0]; decide
    · dsimp only [nr]
      rw [@BitVec.eq_of_toNat_eq 32 _ 0#32 a0, @BitVec.eq_of_toNat_eq 32 _ 1#32 b1]; decide
    · dsimp only [nr]
      rw [@BitVec.eq_of_toNat_eq 32 _ 1#32 a1, @BitVec.eq_of_toNat_eq 32 _ 0#32 b0]; decide
    · dsimp only [nr]
      rw [@BitVec.eq_of_toNat_eq 32 _ 1#32 a1, @BitVec.eq_of_toNat_eq 32 _ 1#32 b1]; decide
  have hr31 := rbit31_shl31 hnr_le
  have hfields := xor_pack_hdr_fields nl (nr <<< 31#32) (by omega) hr31.1
  have hvs_f : (List.range out_n.toNat).map (fun k => (scr_f[dst.toNat + 1 + k]?.getD 0#32).toNat) =
      (List.range out_n.toNat).map (fun k => (scr2[dst.toNat + 1 + k]?.getD 0#32).toNat) := by
    refine List.map_congr_left fun k hk => ?_
    have hk_lt : k < out_n.toNat := List.mem_range.mp hk
    dsimp only [scr_f, scr_z2]
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega)]
  have hss_f : List.Pairwise (· < ·)
      ((List.range out_n.toNat).map fun k => (scr_f[dst.toNat + 1 + k]?.getD 0#32).toNat) := by
    rw [hvs_f, hsym_eq]; exact symDiffSorted_strictSorted hss1 hss2
  have hcv_f : ∀ v ∈ (List.range out_n.toNat).map
      (fun k => (scr_f[dst.toNat + 1 + k]?.getD 0#32).toNat), v < cv := by
    intro v hv; rw [hvs_f, hsym_eq] at hv
    rcases mem_symDiffSorted_or (vs1.length + vs2.length) vs1 vs2 (Nat.le_refl _) v hv with h | h
    · exact hcv1 v h
    · exact hcv2 v h
  have hsnd_f : XorVarsSound F
      ((List.range out_n.toNat).map fun k => (scr_f[dst.toNat + 1 + k]?.getD 0#32).toNat)
      ((nh_dst >>> 31#32) != 0#32) := by
    rw [hvs_f, hfields.2.2, hr31.2]; exact hsym_vars
  have hpool_pre_f : XorEqPoolOk F cv scr_f eq_end 0 :=
    xorEqPoolOk_congr hpool_z2 fun idx _ hidx => List.getElem?_set_ne (by omega)
  have hpool_app : XorEqPoolOk F cv scr_f (dst.toNat + 1 + out_n.toNat) 0 := by
    have hpool_pre_d : XorEqPoolOk F cv scr_f dst.toNat 0 := by rw [hdst_eq]; exact hpool_pre_f
    exact xorEqPoolOk_append hpool_pre_d (by simp [scr_f, scr_z2, hscr2_len]; omega)
      (by simp [scr_f, List.getElem?_set_self hdst_lt])
      (by rw [hfields.1, hnl_eq]) (by rw [hfields.2.1, hnl_eq]) ho_pos hss_f hcv_f hsnd_f
  exact hpool_app

@[expose] def fullXorMergeTwoSpec : Spec [i64, i64, i64, i64] [i64] :=
  fun (scr_ptr, p1, p2, dst, ()) m Q _ =>
    ∃ (F : CNF Nat) (cv eq_end fuel1 fuel2 : Nat) (scr : List (BitVec 32)) (R : Mem 64 → Prop),
      p1.toNat < eq_end ∧ p2.toNat < eq_end ∧ p1 ≠ p2 ∧ dst.toNat = eq_end ∧
      p1.toNat ∈ poolStarts scr eq_end 0 fuel1 ∧
      p2.toNat ∈ poolStarts scr eq_end 0 fuel2 ∧
      0 < ((scr[p1.toNat]?.getD 0#32) &&& 0xFFFF#32).toNat ∧
      0 < ((scr[p2.toNat]?.getD 0#32) &&& 0xFFFF#32).toNat ∧
      ((scr[p1.toNat]?.getD 0#32) &&& 0xFFFF#32).toNat +
        ((scr[p2.toNat]?.getD 0#32) &&& 0xFFFF#32).toNat ≤ 512 ∧
      dst.toNat + 1 +
        ((scr[p1.toNat]?.getD 0#32) &&& 0xFFFF#32).toNat +
        ((scr[p2.toNat]?.getD 0#32) &&& 0xFFFF#32).toNat ≤ scr.length ∧
      scr.length < 2 ^ 32 ∧
      XorEqPoolOk F cv scr eq_end 0 ∧
      (array (t := i32) scr_ptr scr ⋆ R) m ∧
      ∀ (res : BitVec 64) (scr' : List (BitVec 32)) (m' : Mem 64),
        scr'.length = scr.length →
        (res = 0xFFFFFFFFFFFFFFFF#64 → F.Unsat) →
        (res ≠ 0xFFFFFFFFFFFFFFFF#64 →
          dst.toNat ≤ res.toNat ∧
          res.toNat ≤ dst.toNat + 1 +
            ((scr[p1.toNat]?.getD 0#32) &&& 0xFFFF#32).toNat +
            ((scr[p2.toNat]?.getD 0#32) &&& 0xFFFF#32).toNat ∧
          XorEqPoolOk F cv scr' res.toNat 0 ∧
          (∀ i, res.toNat ≤ i → scr'[i]? = scr[i]?) ∧
          (∀ i, i < eq_end → (((scr'[i]?.getD 0#32) >>> 16#32) &&& 0x7FFF#32) =
            (((scr[i]?.getD 0#32) >>> 16#32) &&& 0x7FFF#32)) ∧
          (∀ i, i < eq_end → (scr'[i]?.getD 0#32 &&& 0xFFFF#32) ≠ 0#32 →
            scr'[i]? = scr[i]?)) →
        (array (t := i32) scr_ptr scr' ⋆ R) m' → Q (res, ()) m'

theorem full_xor_merge_two_wp (Γ : Env) :
    ∀ a m Q X, fullXorMergeTwoSpec a m Q X →
      Func.wp Γ full_xor_merge_two_body a m Q X := by
  rintro ⟨scr_ptr, p1, p2, dst, ⟨⟩⟩ m0 Q X
    ⟨F, cv, eq_end, fuel1, fuel2, scr, R, hp1_lt, hp2_lt, hp_ne, hdst_eq, hmem1, hmem2,
     hl1_pos, hl2_pos, hl_sum, hbd_scr, hscr32, hpool0, hm0, hQ⟩
  have hpool1 := xorEqPoolOk_at_mem_poolStarts hpool0 hmem1
  have hpool2 := xorEqPoolOk_at_mem_poolStarts hpool0 hmem2
  cases hpool1 with
  | done => exact absurd hp1_lt (Nat.lt_irrefl _)
  | @step _ h1 st1 len1 _ hh1 hst1 hl1_eq hbd1 hbody1 _ =>
  cases hpool2 with
  | done => exact absurd hp2_lt (Nat.lt_irrefl _)
  | @step _ h2 st2 len2 _ hh2 hst2 hl2_eq hbd2 hbody2 _ =>
  have h1_eq_get : scr[p1.toNat]?.getD 0#32 = h1 := by rw [hh1]; rfl
  have h2_eq_get : scr[p2.toNat]?.getD 0#32 = h2 := by rw [hh2]; rfl
  have hl1_val : ((scr[p1.toNat]?.getD 0#32) &&& 0xFFFF#32).toNat = len1 := by
    rw [h1_eq_get, ← hl1_eq]
  have hl2_val : ((scr[p2.toNat]?.getD 0#32) &&& 0xFFFF#32).toNat = len2 := by
    rw [h2_eq_get, ← hl2_eq]
  rw [hl1_val] at hl1_pos hl_sum hbd_scr
  rw [hl2_val] at hl2_pos hl_sum hbd_scr
  rcases hbody1 with h0 | ⟨_, hls1, hss1, hcv1, hsnd1⟩
  · exact absurd h0 (by omega)
  rcases hbody2 with h0 | ⟨_, hls2, hss2, hcv2, hsnd2⟩
  · exact absurd h0 (by omega)
  let vs1 := (List.range len1).map fun k => (scr[p1.toNat + 1 + k]?.getD 0#32).toNat
  let vs2 := (List.range len2).map fun k => (scr[p2.toNat + 1 + k]?.getD 0#32).toNat
  have hvs1_len : vs1.length = len1 := by simp [vs1]
  have hvs2_len : vs2.length = len2 := by simp [vs2]
  have hp1_bd : p1.toNat < scr.length := by omega
  have hp2_bd : p2.toNat < scr.length := by omega
  c0_hstraight
  obtain ⟨gh1, hgh1⟩ : ∃ x : BitVec 32, scr[p1.toNat]'hp1_bd = x := ⟨_, rfl⟩
  obtain ⟨gh2, hgh2⟩ : ∃ x : BitVec 32, scr[p2.toNat]'hp2_bd = x := ⟨_, rfl⟩
  have heq_h1 : gh1 = h1 := by
    have := hh1; rw [List.getElem?_eq_getElem hp1_bd] at this
    rw [← hgh1]; exact Option.some.inj this
  have heq_h2 : gh2 = h2 := by
    have := hh2; rw [List.getElem?_eq_getElem hp2_bd] at this
    rw [← hgh2]; exact Option.some.inj this
  subst heq_h1 heq_h2
  rw [hgh1, hgh2]
  obtain ⟨wlen1, hwlen1⟩ : ∃ w : BitVec 64, (gh1 &&& 65535).setWidth 64 = w := ⟨_, rfl⟩
  obtain ⟨wlen2, hwlen2⟩ : ∃ w : BitVec 64, (gh2 &&& 65535).setWidth 64 = w := ⟨_, rfl⟩
  have hl1_w : wlen1.toNat = len1 := by
    rw [← hwlen1, bv_zext32_toNat, show (gh1 &&& (65535 : BitVec 32)) = gh1 &&& 0xFFFF#32 from rfl,
      hl1_eq]
  have hl2_w : wlen2.toNat = len2 := by
    rw [← hwlen2, bv_zext32_toNat, show (gh2 &&& (65535 : BitVec 32)) = gh2 &&& 0xFFFF#32 from rfl,
      hl2_eq]
  rw [hwlen1, hwlen2]
  refine wp_loop_inv
    (fun (i, j, out_n, ()) m1 => ∃ scr1,
      i.toNat ≤ len1 ∧ j.toNat ≤ len2 ∧ out_n.toNat ≤ i.toNat + j.toNat ∧
      scr1.length = scr.length ∧
      (∀ idx, idx ≤ dst.toNat ∨ dst.toNat + 1 + out_n.toNat ≤ idx → scr1[idx]? = scr[idx]?) ∧
      ((List.range out_n.toNat).map fun k => (scr1[dst.toNat + 1 + k]?.getD 0#32).toNat) ++
        symDiffSorted (vs1.drop i.toNat) (vs2.drop j.toNat) = symDiffSorted vs1 vs2 ∧
      (array (t := i32) scr_ptr scr1 ⋆ R) m1)
    (fun (i, j, _, ()) _ => (len1 - i.toNat) + (len2 - j.toNat))
    (fun J1 hJ1 => by
      c0_hstraight
      exact hJ1 (0#64, 0#64, 0#64, ()) m0 ⟨scr, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, rfl,
        fun _ _ => rfl, by simp, hm0⟩)
    (fun J1 (i, j, out_n, ()) m1 ⟨scr1, hi_le, hj_le, ho_le, hlen1, hpre1, hsym1, hm1⟩ ih1 => ?_)
  have hnil_r : ∀ xs : List Nat, symDiffSorted xs [] = xs := fun xs => by
    cases xs <;> rw [symDiffSorted.eq_def]
  refine wp_join0 (fun m_brk => (i.toNat = len1 ∨ j.toNat = len2) ∧ m_brk = m1) ?_
    (fun Jbrk hJbrk => ?_)
  · intro _ m_brk ⟨hbrk, hm_brk⟩; rcases hm_brk.symm with rfl
    dsimp only [Blocks.get]
    refine wp_loop_inv
      (fun (i2, out2, ()) m2 => ∃ scr2,
        i2.toNat ≤ len1 ∧ out2.toNat ≤ i2.toNat + j.toNat ∧
        (i2.toNat < len1 → j.toNat = len2) ∧ scr2.length = scr.length ∧
        (∀ idx, idx ≤ dst.toNat ∨ dst.toNat + 1 + out2.toNat ≤ idx →
          scr2[idx]? = scr[idx]?) ∧
        ((List.range out2.toNat).map fun k => (scr2[dst.toNat + 1 + k]?.getD 0#32).toNat) ++
          symDiffSorted (vs1.drop i2.toNat) (vs2.drop j.toNat) = symDiffSorted vs1 vs2 ∧
        (array (t := i32) scr_ptr scr2 ⋆ R) m2)
      (fun (i2, _, ()) _ => len1 - i2.toNat)
      (fun J2 hJ2 => by
        c0_hstraight
        exact hJ2 (i, out_n, ()) m1 ⟨scr1, hi_le, ho_le,
          fun hi => Or.resolve_left hbrk (by omega), hlen1, hpre1, hsym1, hm1⟩)
      (fun J2 (i2, out2, ()) m2 ⟨scr2, hi2_le, ho2_le, hbrk2, hlen2, hpre2, hsym2, hm2⟩ ih2 => ?_)
    c0_hsplit
    · have hi2_lt : i2.toNat < len1 := by rw [← hl1_w]; bv_omega
      have hj_eq2 : j.toNat = len2 := hbrk2 hi2_lt
      have ha_bd : p1.toNat + 1 + i2.toNat < scr2.length := by omega
      have hdst_bd : dst.toNat + 1 + out2.toNat < scr2.length := by omega
      have hp1i2 : (p1 + 1 + i2).toNat = p1.toNat + 1 + i2.toNat := by bv_omega
      have hdst_w : (dst + 1 + out2).toNat = dst.toNat + 1 + out2.toNat := by bv_omega
      have ha_pre : scr2[p1.toNat + 1 + i2.toNat]? = scr[p1.toNat + 1 + i2.toNat]? :=
        hpre2 _ (Or.inl (by omega))
      c0_hstraight
      obtain ⟨va, hva⟩ : ∃ x : BitVec 32,
          scr2[(p1 + 1 + i2).toNat]'(by rw [hp1i2]; exact ha_bd) = x := ⟨_, rfl⟩
      rw [hdst_w, hva] at hm
      have hva_vs1 : vs1[i2.toNat]'(by omega) = va.toNat := by
        dsimp only [vs1]; rw [List.getElem_map, List.getElem_range]
        have : scr[p1.toNat + 1 + i2.toNat]? = some va := by
          rw [← ha_pre, show scr2[p1.toNat + 1 + i2.toNat]? = scr2[(p1 + 1 + i2).toNat]? from
            congrArg (scr2[·]?) hp1i2.symm,
            List.getElem?_eq_getElem (by rw [hp1i2]; exact ha_bd), hva]
        simp [this]
      have hdrop1 := List.drop_eq_getElem_cons (i := i2.toNat) (l := vs1) (by omega)
      rw [hva_vs1] at hdrop1
      have ho_succ : (out2 + 1#64).toNat = out2.toNat + 1 := by bv_omega
      have hi_succ : (i2 + 1#64).toNat = i2.toNat + 1 := by bv_omega
      refine ih2 (i2 + 1#64, out2 + 1#64, ()) _ (by dsimp only; rw [hi_succ]; omega)
        ⟨scr2.set (dst.toNat + 1 + out2.toNat) va, by rw [hi_succ]; omega,
         by rw [ho_succ, hi_succ]; omega, fun _ => hj_eq2,
         by simp [hlen2],
         fun idx hidx => by
           rw [ho_succ] at hidx
           rw [List.getElem?_set_ne (by omega)]
           exact hpre2 idx (by rcases hidx with h | h; exact Or.inl h; exact Or.inr (by omega)),
         ?_, hm⟩
      rw [ho_succ, hi_succ, list_range_map_succ]
      have hmap_eq : (List.range out2.toNat).map (fun k =>
            ((scr2.set (dst.toNat + 1 + out2.toNat) va)[dst.toNat + 1 + k]?.getD 0#32).toNat) =
          (List.range out2.toNat).map (fun k => (scr2[dst.toNat + 1 + k]?.getD 0#32).toNat) := by
        refine List.map_congr_left fun k hk => ?_
        have hk_lt : k < out2.toNat := List.mem_range.mp hk
        rw [List.getElem?_set_ne (by omega)]
      rw [hmap_eq, List.getElem?_set_self hdst_bd, Option.getD_some, List.append_assoc,
        List.singleton_append]
      rw [hj_eq2, show vs2.drop len2 = [] from List.drop_of_length_le (by omega), hnil_r] at hsym2 ⊢
      rw [← hdrop1]; exact hsym2
    · have hi2_eq : i2.toNat = len1 := by rw [← hl1_w]; bv_omega
      rw [hi2_eq, show vs1.drop len1 = [] from List.drop_of_length_le (by omega),
        symDiffSorted.eq_def] at hsym2
      c0_hstraight
      refine wp_loop_inv
        (fun (j3, out3, ()) m3 => ∃ scr3,
          j3.toNat ≤ len2 ∧ out3.toNat ≤ len1 + j3.toNat ∧ scr3.length = scr.length ∧
          (∀ idx, idx ≤ dst.toNat ∨ dst.toNat + 1 + out3.toNat ≤ idx →
            scr3[idx]? = scr[idx]?) ∧
          ((List.range out3.toNat).map fun k => (scr3[dst.toNat + 1 + k]?.getD 0#32).toNat) ++
            (vs2.drop j3.toNat) = symDiffSorted vs1 vs2 ∧
          (array (t := i32) scr_ptr scr3 ⋆ R) m3)
        (fun (j3, _, ()) _ => len2 - j3.toNat)
        (fun J3 hJ3 => by
          c0_hstraight
          exact hJ3 (j, out2, ()) m2 ⟨scr2, hj_le, by omega, hlen2, hpre2, hsym2, hm2⟩)
        (fun J3 (j3, out3, ()) m3 ⟨scr3, hj3_le, ho3_le, hlen3, hpre3, hsym3, hm3⟩ ih3 => ?_)
      c0_hsplit
      · have hj3_lt : j3.toNat < len2 := by rw [← hl2_w]; bv_omega
        have hb_bd : p2.toNat + 1 + j3.toNat < scr3.length := by omega
        have hdst_bd : dst.toNat + 1 + out3.toNat < scr3.length := by omega
        have hp2j3 : (p2 + 1 + j3).toNat = p2.toNat + 1 + j3.toNat := by bv_omega
        have hdst_w : (dst + 1 + out3).toNat = dst.toNat + 1 + out3.toNat := by bv_omega
        have hb_pre : scr3[p2.toNat + 1 + j3.toNat]? = scr[p2.toNat + 1 + j3.toNat]? :=
          hpre3 _ (Or.inl (by omega))
        c0_hstraight
        obtain ⟨vb, hvb⟩ : ∃ x : BitVec 32,
            scr3[(p2 + 1 + j3).toNat]'(by rw [hp2j3]; exact hb_bd) = x := ⟨_, rfl⟩
        rw [hdst_w, hvb] at hm
        have hvb_vs2 : vs2[j3.toNat]'(by omega) = vb.toNat := by
          dsimp only [vs2]; rw [List.getElem_map, List.getElem_range]
          have : scr[p2.toNat + 1 + j3.toNat]? = some vb := by
            rw [← hb_pre, show scr3[p2.toNat + 1 + j3.toNat]? = scr3[(p2 + 1 + j3).toNat]? from
              congrArg (scr3[·]?) hp2j3.symm,
              List.getElem?_eq_getElem (by rw [hp2j3]; exact hb_bd), hvb]
          simp [this]
        have hdrop2 := List.drop_eq_getElem_cons (i := j3.toNat) (l := vs2) (by omega)
        rw [hvb_vs2] at hdrop2
        have ho_succ : (out3 + 1#64).toNat = out3.toNat + 1 := by bv_omega
        have hj_succ : (j3 + 1#64).toNat = j3.toNat + 1 := by bv_omega
        refine ih3 (j3 + 1#64, out3 + 1#64, ()) _ (by dsimp only; rw [hj_succ]; omega)
          ⟨scr3.set (dst.toNat + 1 + out3.toNat) vb, by rw [hj_succ]; omega,
           by rw [ho_succ, hj_succ]; omega, by simp [hlen3],
           fun idx hidx => by
             rw [ho_succ] at hidx
             rw [List.getElem?_set_ne (by omega)]
             exact hpre3 idx (by rcases hidx with h | h; exact Or.inl h; exact Or.inr (by omega)),
           ?_, hm⟩
        rw [ho_succ, hj_succ, list_range_map_succ]
        have hmap_eq : (List.range out3.toNat).map (fun k =>
              ((scr3.set (dst.toNat + 1 + out3.toNat) vb)[dst.toNat + 1 + k]?.getD 0#32).toNat) =
            (List.range out3.toNat).map (fun k => (scr3[dst.toNat + 1 + k]?.getD 0#32).toNat) := by
          refine List.map_congr_left fun k hk => ?_
          have hk_lt : k < out3.toNat := List.mem_range.mp hk
          rw [List.getElem?_set_ne (by omega)]
        rw [hmap_eq, List.getElem?_set_self hdst_bd, Option.getD_some, List.append_assoc,
          List.singleton_append]
        rw [← hdrop2]; exact hsym3
      · have hj3_eq : j3.toNat = len2 := by rw [← hl2_w]; bv_omega
        rw [hj3_eq, show vs2.drop len2 = [] from List.drop_of_length_le (by omega),
          List.append_nil] at hsym3
        have hp1_bd2 : p1.toNat < scr3.length := by omega
        have hp2_bd2 : p2.toNat < (scr3.set p1.toNat (gh1 &&& 0x7FFF0000#32)).length := by
          simp; omega
        c0_hstraight
        have hz := merge_two_zero_pool hp1_lt hp2_lt hp_ne hdst_eq hmem1 hmem2
          h1_eq_get h2_eq_get hlen3 (by omega) (fun idx hi => hpre3 idx (Or.inl hi)) hpool0
        dsimp only at hz
        let scr_z1 := scr3.set p1.toNat (gh1 &&& 0x7FFF0000#32)
        let scr_z2 := scr_z1.set p2.toNat (gh2 &&& 0x7FFF0000#32)
        have hsym_vars := xorVarsSound_symDiffSorted hsnd1 hsnd2
        rw [← hsym3, ← bv32_xor_shr31_ne_zero] at hsym_vars
        c0_hsplit
        · have ho3_0 : out3.toNat = 0 := by bv_omega
          have hnil : ((List.range out3.toNat).map fun k =>
              (scr3[dst.toNat + 1 + k]?.getD 0#32).toNat) = [] := by rw [ho3_0]; rfl
          rw [hnil] at hsym_vars
          c0_hsplit
          · have hnr : ((gh1 >>> 31#32 ^^^ gh2 >>> 31#32) != 0#32) = true := by
              simp only [bne_iff_ne, ne_eq]; assumption
            rw [hnr] at hsym_vars
            c0_hstraight
            exact hQ 0xFFFFFFFFFFFFFFFF#64 scr_z2 m (by simp [scr_z2, scr_z1, hlen3])
              (fun _ => unsat_of_xorVars_nil hsym_vars) (fun h => absurd rfl h)
              (by simpa [scr_z2, scr_z1] using hm)
          · c0_hstraight
            exact hQ dst scr_z2 m (by simp [scr_z2, scr_z1, hlen3])
              (fun h => absurd h (by bv_omega))
              (fun _ => ⟨Nat.le_refl _, by rw [hl1_val, hl2_val]; omega,
                by rw [hdst_eq]; exact hz.1,
                fun idx hidx => by
                  dsimp only [scr_z2, scr_z1]
                  rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
                    hpre3 idx (by omega)],
                hz.2.1, hz.2.2⟩)
              (by simpa [scr_z2, scr_z1] using hm)
        · have ho3_pos : 0 < out3.toNat := by bv_omega
          have hdst_lt : dst.toNat < scr_z2.length := by simp [scr_z2, scr_z1, hlen3]; omega
          c0_hstraight
          have hpk := merge_two_pack_ok (scr := scr) (scr2 := scr3) ho3_pos (by omega) hdst_eq
            hp1_lt hp2_lt hlen3 (by omega) hss1 hss2 hcv1 hcv2 hsym_vars hsym3 hz.1
          dsimp only at hpk
          have hret_ne : dst + 1#64 + out3 ≠ 0xFFFFFFFFFFFFFFFF#64 := by bv_omega
          exact hQ (dst + 1#64 + out3) (scr_z2.set dst.toNat _) m (by simp [scr_z2, scr_z1, hlen3])
            (fun h => absurd h hret_ne)
            (fun _ => ⟨by bv_omega, by rw [hl1_val, hl2_val]; bv_omega, by
              have hto : (dst + 1#64 + out3).toNat = dst.toNat + 1 + out3.toNat := by bv_omega
              rw [hto]; exact hpk,
              fun idx hidx => by
                have hto : (dst + 1#64 + out3).toNat = dst.toNat + 1 + out3.toNat := by bv_omega
                rw [hto] at hidx
                rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
                  List.getElem?_set_ne (by omega), hpre3 idx (Or.inr hidx)],
              fun idx hidx => by
                rw [List.getElem?_set_ne (by omega)]; exact hz.2.1 idx hidx,
              fun idx hidx hne => by
                rw [List.getElem?_set_ne (by omega)]
                exact hz.2.2 idx hidx (by
                  rw [List.getElem?_set_ne (by omega)] at hne; exact hne)⟩)
            (by simpa [scr_z2, scr_z1] using hm)
  · c0_hsplit
    · have hi_lt : i.toNat < len1 := by rw [← hl1_w]; bv_omega
      c0_hsplit
      · have hj_lt : j.toNat < len2 := by rw [← hl2_w]; bv_omega
        have ha_bd : p1.toNat + 1 + i.toNat < scr1.length := by omega
        have hb_bd : p2.toNat + 1 + j.toNat < scr1.length := by omega
        have hp1i : (p1 + 1 + i).toNat = p1.toNat + 1 + i.toNat := by bv_omega
        have hp2j : (p2 + 1 + j).toNat = p2.toNat + 1 + j.toNat := by bv_omega
        have ha_pre : scr1[p1.toNat + 1 + i.toNat]? = scr[p1.toNat + 1 + i.toNat]? :=
          hpre1 _ (Or.inl (by omega))
        have hb_pre : scr1[p2.toNat + 1 + j.toNat]? = scr[p2.toNat + 1 + j.toNat]? :=
          hpre1 _ (Or.inl (by omega))
        c0_hstraight
        obtain ⟨va, hva⟩ : ∃ x : BitVec 32,
            scr1[(p1 + 1 + i).toNat]'(by rw [hp1i]; exact ha_bd) = x := ⟨_, rfl⟩
        obtain ⟨vb, hvb⟩ : ∃ x : BitVec 32,
            scr1[(p2 + 1 + j).toNat]'(by rw [hp2j]; exact hb_bd) = x := ⟨_, rfl⟩
        rw [hva, hvb]
        have hva_vs1 : vs1[i.toNat]'(by omega) = va.toNat := by
          dsimp only [vs1]; rw [List.getElem_map, List.getElem_range]
          have : scr[p1.toNat + 1 + i.toNat]? = some va := by
            rw [← ha_pre, show scr1[p1.toNat + 1 + i.toNat]? = scr1[(p1 + 1 + i).toNat]? from
              congrArg (scr1[·]?) hp1i.symm,
              List.getElem?_eq_getElem (by rw [hp1i]; exact ha_bd), hva]
          simp [this]
        have hvb_vs2 : vs2[j.toNat]'(by omega) = vb.toNat := by
          dsimp only [vs2]; rw [List.getElem_map, List.getElem_range]
          have : scr[p2.toNat + 1 + j.toNat]? = some vb := by
            rw [← hb_pre, show scr1[p2.toNat + 1 + j.toNat]? = scr1[(p2 + 1 + j).toNat]? from
              congrArg (scr1[·]?) hp2j.symm,
              List.getElem?_eq_getElem (by rw [hp2j]; exact hb_bd), hvb]
          simp [this]
        have hdrop1 := List.drop_eq_getElem_cons (i := i.toNat) (l := vs1) (by omega)
        have hdrop2 := List.drop_eq_getElem_cons (i := j.toNat) (l := vs2) (by omega)
        rw [hva_vs1] at hdrop1
        rw [hvb_vs2] at hdrop2
        have hdst_bd : dst.toNat + 1 + out_n.toNat < scr1.length := by omega
        refine wp_join_state
          (fun st : Val i64 × Val i64 × Val i64 => (st.1, st.2.1, st.2.2, ()))
          (fun (i', j', out') m' => ∃ scr',
            (len1 - i'.toNat) + (len2 - j'.toNat) < (len1 - i.toNat) + (len2 - j.toNat) ∧
            i'.toNat ≤ len1 ∧ j'.toNat ≤ len2 ∧ out'.toNat ≤ i'.toNat + j'.toNat ∧
            scr'.length = scr.length ∧
            (∀ idx, idx ≤ dst.toNat ∨ dst.toNat + 1 + out'.toNat ≤ idx →
              scr'[idx]? = scr[idx]?) ∧
            ((List.range out'.toNat).map fun k => (scr'[dst.toNat + 1 + k]?.getD 0#32).toNat) ++
              symDiffSorted (vs1.drop i'.toNat) (vs2.drop j'.toNat) = symDiffSorted vs1 vs2 ∧
            (array (t := i32) scr_ptr scr' ⋆ R) m')
          (fun _ (i', j', out') m' ⟨scr', hdec, hi', hj', ho', hlen', hpre', hsym', hm'⟩ => by
            dsimp only [Blocks.get]
            exact ih1 (i', j', out', ()) m' hdec
              ⟨scr', hi', hj', ho', hlen', hpre', hsym', hm'⟩)
          (fun Jif hJif => ?_)
        c0_hsplit
        · have hlt_ab : va.toNat < vb.toNat := by bv_omega
          c0_hstraight
          have hdst_w : (dst + 1 + out_n).toNat = dst.toNat + 1 + out_n.toNat := by bv_omega
          have ho_succ : (out_n + 1#64).toNat = out_n.toNat + 1 := by bv_omega
          have hi_succ : (i + 1#64).toNat = i.toNat + 1 := by bv_omega
          rw [hdst_w] at hm
          refine hJif (i + 1#64, j, out_n + 1#64) _ ⟨scr1.set (dst.toNat + 1 + out_n.toNat) va,
            by rw [hi_succ]; omega, by rw [hi_succ]; omega, hj_le,
            by rw [hi_succ, ho_succ]; omega, by simp [hlen1],
            fun idx hidx => by
              rw [ho_succ] at hidx
              rw [List.getElem?_set_ne (by omega)]
              exact hpre1 idx (by rcases hidx with h | h; exact Or.inl h; exact Or.inr (by omega)),
            ?_, hm⟩
          rw [ho_succ, hi_succ, list_range_map_succ]
          have hmap_eq : (List.range out_n.toNat).map (fun k =>
                ((scr1.set (dst.toNat + 1 + out_n.toNat) va)[dst.toNat + 1 + k]?.getD 0#32).toNat) =
              (List.range out_n.toNat).map
                (fun k => (scr1[dst.toNat + 1 + k]?.getD 0#32).toNat) := by
            refine List.map_congr_left fun k hk => ?_
            have hk_lt : k < out_n.toNat := List.mem_range.mp hk
            rw [List.getElem?_set_ne (by omega)]
          rw [hmap_eq, List.getElem?_set_self hdst_bd, Option.getD_some, List.append_assoc,
            List.singleton_append]
          rw [hdrop1, hdrop2, symDiffSorted.eq_def] at hsym1
          simp only [hlt_ab, ↓reduceIte] at hsym1
          rw [← hdrop2] at hsym1; exact hsym1
        · refine wp_join_group (fun xs m' => Jif xs m')
            (fun _ ⟨a, b, c, ⟨⟩⟩ m' h => h) (fun Jif2 hJif2 => ?_)
          c0_hsplit
          · have hlt_ba : vb.toNat < va.toNat := by bv_omega
            c0_hstraight
            have hdst_w : (dst + 1 + out_n).toNat = dst.toNat + 1 + out_n.toNat := by bv_omega
            have ho_succ : (out_n + 1#64).toNat = out_n.toNat + 1 := by bv_omega
            have hj_succ : (j + 1#64).toNat = j.toNat + 1 := by bv_omega
            rw [hdst_w] at hm
            refine hJif2 _ _ (hJif (i, j + 1#64, out_n + 1#64) _
              ⟨scr1.set (dst.toNat + 1 + out_n.toNat) vb,
               by rw [hj_succ]; omega, hi_le, by rw [hj_succ]; omega,
               by rw [ho_succ, hj_succ]; omega, by simp [hlen1],
               fun idx hidx => by
                 rw [ho_succ] at hidx
                 rw [List.getElem?_set_ne (by omega)]
                 exact hpre1 idx
                   (by rcases hidx with h | h; exact Or.inl h; exact Or.inr (by omega)),
               ?_, hm⟩)
            rw [ho_succ, hj_succ, list_range_map_succ]
            have hmap_eq : (List.range out_n.toNat).map (fun k =>
                  ((scr1.set (dst.toNat + 1 + out_n.toNat) vb)[dst.toNat + 1 + k]?.getD
                    0#32).toNat) =
                (List.range out_n.toNat).map
                (fun k => (scr1[dst.toNat + 1 + k]?.getD 0#32).toNat) := by
              refine List.map_congr_left fun k hk => ?_
              have hk_lt : k < out_n.toNat := List.mem_range.mp hk
              rw [List.getElem?_set_ne (by omega)]
            rw [hmap_eq, List.getElem?_set_self hdst_bd, Option.getD_some, List.append_assoc,
              List.singleton_append]
            rw [hdrop1, hdrop2, symDiffSorted.eq_def] at hsym1
            have hnot : ¬ va.toNat < vb.toNat := by omega
            simp only [hnot, ↓reduceIte, hlt_ba] at hsym1
            rw [← hdrop1] at hsym1; exact hsym1
          · have heq_ab : va.toNat = vb.toNat := by bv_omega
            c0_hstraight
            have hi_succ : (i + 1#64).toNat = i.toNat + 1 := by bv_omega
            have hj_succ : (j + 1#64).toNat = j.toNat + 1 := by bv_omega
            refine hJif2 _ _ (hJif (i + 1#64, j + 1#64, out_n) _
              ⟨scr1, by rw [hi_succ, hj_succ]; omega, by rw [hi_succ]; omega,
               by rw [hj_succ]; omega, by rw [hi_succ, hj_succ]; omega, hlen1, hpre1, ?_, hm1⟩)
            rw [hi_succ, hj_succ]
            rw [hdrop1, hdrop2, symDiffSorted.eq_def] at hsym1
            have hn1 : ¬ va.toNat < vb.toNat := by omega
            have hn2 : ¬ vb.toNat < va.toNat := by omega
            simp only [hn1, ↓reduceIte, hn2] at hsym1
            exact hsym1
      · have hj_eq : j.toNat = len2 := by rw [← hl2_w]; bv_omega
        c0_hstraight
        exact hJbrk m1 ⟨Or.inr hj_eq, rfl⟩
    · have hi_eq : i.toNat = len1 := by rw [← hl1_w]; bv_omega
      c0_hstraight
      exact hJbrk m1 ⟨Or.inl hi_eq, rfl⟩


end LeanQbe.T.Examples.Kissat.FullM8XorGauss
