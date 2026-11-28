/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Arisca.ArtCore
public import LeanQbe.T.Examples.Arisca.ArtSoundPoly
public import LeanQbe.T.Examples.Arisca.ArtSoundAux
public import LeanQbe.T.Examples.Arisca.ArtSound
public import LeanQbe.T.Examples.Arisca.Proof.Arena
public import LeanQbe.T.Examples.Arisca.Proof.Arith
public import LeanQbe.T.Logic.Mem
public import LeanQbe.T.Logic.Bytes
public import LeanQbe.T.Logic.Rules
public import LeanQbe.T.Logic.SlabChain
import LeanQbe.T.Logic.MemLemmas
import Kraken.Separation

/-!
# Semantic Invariants, AIG/ART Bridges & Workspace Slab Predicates (`Arisca.Proof.Sem`)

Defines the shared soundness-only semantic predicates and slab separation layouts used across
`Parse`, `Poly{0,1,2}`, `Driver{0,1,2}`, and `Full`:
- AIG representation (`AigRep`), C0 signal valuation `cSig`, and binding invariant (`BindRep`)
- Monomial & polynomial evaluation (`symListAt`, `monoValL`, `termEval`, `polyEvalRange`,
  `polyEval`, `polyEvalIdx`) and permutation/set invariance lemmas
- Vanishing pairs (`PartnerRep`), rule store (`RulesRep`), and expanded rule (`CurRRep`)
- Aligned `SlabChain`-backed memory groups (`aigArraysMem`, `netTablesMem`, `gateScratchMem`,
  `rsMem`, `tMem`, `qMem`, `rMem`) with linear `O(K)` collapse to `region`
- Word-level bridges from `cSig` / `polyEval` to `ArtSound.outSum_eq`, `ArtSound.inSum_eq`, and
  `ArtSound.checkArt_sound`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Arisca.Proof

open Std Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Arisca
open LeanQbe.T.Examples.Arisca.Src
open LeanQbe.T.Examples.Arisca.Src.Header
open Kraken.Bedrock2.Test

@[expose] public section

/-! ## 1. Constants, AIG Representation & Signal Valuation (`cSig`) -/

def cNone32 : BitVec 32 := 0xFFFFFFFF#32
def arAccept64 : BitVec 64 := 20#64
def arReject64 : BitVec 64 := 0#64
def arArtMagic32 : BitVec 32 := 0x31545241#32
def arTTMaxAnd : Nat := 64
def arTTStk : Nat := 160
def arRMaxF : Nat := 24
def arWRatio : Nat := 12

/-- Byte list converted to `List Nat` matching `ArtCore.parseAig`. -/
def toNatBytes (bs : List UInt8) : List Nat := bs.map UInt8.toNat

/-- Soundness invariant linking parsed `Aig` to C0's `(rhs0, rhs1, olit)` arrays. -/
structure AigRep (g : Aig) (rhs0 rhs1 olit : List (BitVec 32)) : Prop where
  i_le_m : g.I ≤ g.M
  m_eq : g.M = g.I + g.ands.length
  rhs0_len : rhs0.length = g.ands.length
  rhs1_len : rhs1.length = g.ands.length
  olit_len : olit.length = g.outs.length
  rhs0_eq : ∀ j, j < g.ands.length → (rhs0.getD j 0#32).toNat = (g.ands.getD j (0, 0)).1
  rhs1_eq : ∀ j, j < g.ands.length → (rhs1.getD j 0#32).toNat = (g.ands.getD j (0, 0)).2
  olit_eq : ∀ j, j < g.outs.length → (olit.getD j 0#32).toNat = g.outs.getD j 0
  ands_wf : ∀ j, j < g.ands.length →
    (g.ands.getD j (0, 0)).1 / 2 < g.I + 1 + j ∧ (g.ands.getD j (0, 0)).2 / 2 < g.I + 1 + j
  outs_wf : ∀ j, j < g.outs.length → g.outs.getD j 0 / 2 ≤ g.M

/-- C0 polynomial signal assignment induced by AIG input valuation `ρ` and `bind` array. -/
def cSig (g : Aig) (ρ : Nat → Bool) (bindArr : List (BitVec 32)) (x : Nat) : Bool :=
  g.litVal ρ (bindArr.getD (x / 2) 0#32).toNat ^^ (x % 2 == 1)

/-- Soundness invariant on C0's `bind`, `in_net`, and `out_ref` tables. -/
structure BindRep (s : ArCtxState) (g : Aig)
    (bindArr inNetArr outRefArr : List (BitVec 32)) : Prop where
  bind_len : s.n_nets.toNat ≤ bindArr.length
  bind_bound : ∀ v < s.n_nets.toNat, bindArr.getD v 0#32 ≠ cNone32 →
    (bindArr.getD v 0#32).toNat ≤ 2 * g.M + 1
  in_len : s.n_in.toNat ≤ inNetArr.length
  in_eq : s.n_in.toNat = g.I
  i_even : g.I % 2 = 0 ∧ 2 ≤ g.I
  in_ok : ∀ i < s.n_in.toNat, (inNetArr.getD i 0#32).toNat < s.n_nets.toNat ∧
    (bindArr.getD (inNetArr.getD i 0#32).toNat 0#32).toNat = 2 * (i + 1)
  out_len : s.n_out.toNat ≤ outRefArr.length
  out_eq : s.n_out.toNat = g.outs.length
  out_bounds : 1 ≤ s.n_out.toNat ∧ s.n_out.toNat ≤ 128
  out_ok : ∀ j < s.n_out.toNat, ((outRefArr.getD j 0#32) >>> 1).toNat < s.n_nets.toNat ∧
    let b := bindArr.getD ((outRefArr.getD j 0#32) >>> 1).toNat 0#32
    b ≠ cNone32 ∧ (b ^^^ ((outRefArr.getD j 0#32) &&& 1#32)).toNat = g.outs.getD j 0

/-! ## 2. Monomials, Polynomials, Vanishing Pairs & Rules -/

/-- List of C0 symbols stored in `pool` at monomial offset `off` (`pool[off]` = length). -/
def symListAt (pool : List (BitVec 32)) (off : Nat) : List Nat :=
  let len := (pool.getD off 0#32).toNat
  (List.range len).map (fun i => (pool.getD (off + 1 + i) 0#32).toNat)

/-- Boolean product of a list of C0 signal variables under valuation `σ`. -/
def monoValL (σ : Nat → Bool) : List Nat → Bool
  | [] => true
  | s :: rest => σ s && monoValL σ rest

/-- BitVec `nOut` evaluation of term `i` in SoA polynomial `(pool, mOff, cl, ch)`. -/
def termEval (nOut : Nat) (σ : Nat → Bool) (pool mOff : List (BitVec 32))
    (cl ch : List (BitVec 64)) (i : Nat) : BitVec nOut :=
  if monoValL σ (symListAt pool (mOff.getD i 0#32).toNat) then
    coeff128 nOut (cl.getD i 0#64) (ch.getD i 0#64)
  else 0#nOut

/-- Sum of `termEval` over indices `lo .. lo + n - 1` modulo `2 ^ nOut`. -/
def polyEvalRange (nOut : Nat) (σ : Nat → Bool) (pool mOff : List (BitVec 32))
    (cl ch : List (BitVec 64)) (lo n : Nat) : BitVec nOut :=
  (List.range n).foldl (fun acc k => acc + termEval nOut σ pool mOff cl ch (lo + k)) 0#nOut

/-- Sum of `termEval` over indices `0 .. n - 1`. -/
def polyEval (nOut : Nat) (σ : Nat → Bool) (pool mOff : List (BitVec 32))
    (cl ch : List (BitVec 64)) (n : Nat) : BitVec nOut :=
  polyEvalRange nOut σ pool mOff cl ch 0 n

/-- Sum of `termEval` over indirect index table `ix[lo .. lo + n - 1]`. -/
def polyEvalIdxOf (nOut : Nat) (σ : Nat → Bool) (pool mOff : List (BitVec 32))
    (cl ch : List (BitVec 64)) (ix : List (BitVec 32)) (lo n : Nat) : BitVec nOut :=
  (List.range n).foldl
    (fun acc k => acc + termEval nOut σ pool mOff cl ch (ix.getD (lo + k) 0#32).toNat) 0#nOut

/-- Well-formedness of a monomial slice `pool[off .. off + pool[off]]`. -/
def MonoSliceOk (pool : List (BitVec 32)) (off bound : Nat) : Prop :=
  off < bound ∧ off + 1 + (pool.getD off 0#32).toNat ≤ bound

/-- Soundness invariant on C0 HA vanishing pairs (`partner`). -/
def PartnerRep (σ : Nat → Bool) (nNets : Nat) (partnerArr : List (BitVec 32)) : Prop :=
  nNets ≤ partnerArr.length ∧
  ∀ v < nNets, partnerArr.getD v 0#32 ≠ cNone32 →
    let p := (partnerArr.getD v 0#32).toNat
    p < nNets ∧ ¬ (σ (2 * v) = true ∧ σ (2 * p) = true)

/-- Soundness invariant on C0 stored gate/cone rules (`rs_m`, `rs_l`, `rs_h`, `rs_pool`). -/
def RulesRep (nOut : Nat) (σ : Nat → Bool) (s : ArCtxState)
    (ruleOff ruleN rsM : List (BitVec 32)) (rsL rsH : List (BitVec 64))
    (rsPool : List (BitVec 32)) : Prop :=
  s.n_nets.toNat ≤ ruleOff.length ∧ s.n_nets.toNat ≤ ruleN.length ∧
  s.rs_n.toNat ≤ s.rs_cap.toNat ∧ s.rs_ptop.toNat ≤ s.rs_pcap.toNat ∧
  s.rs_cap.toNat ≤ rsM.length ∧ s.rs_cap.toNat ≤ rsL.length ∧ s.rs_cap.toNat ≤ rsH.length ∧
  s.rs_pcap.toNat ≤ rsPool.length ∧
  (∀ i < s.rs_n.toNat, MonoSliceOk rsPool (rsM.getD i 0#32).toNat s.rs_ptop.toNat) ∧
  (∀ v < s.n_nets.toNat, ruleN.getD v 0#32 ≠ cNone32 →
    let off := (ruleOff.getD v 0#32).toNat
    let cnt := (ruleN.getD v 0#32).toNat
    off + cnt ≤ s.rs_n.toNat ∧
    bv nOut (σ (2 * v)) = polyEvalRange nOut σ rsPool rsM rsL rsH off cnt)

/-- Soundness invariant on C0 expanded replacement polynomial `cur_r*` for target symbol `sym`. -/
def CurRRep (nOut : Nat) (σ : Nat → Bool) (curNr : Nat) (sym : Nat)
    (curRm : List (BitVec 32)) (curRl curRh : List (BitVec 64))
    (curRp : List (BitVec 32)) : Prop :=
  curNr ≤ curRm.length ∧ curNr ≤ curRl.length ∧ curNr ≤ curRh.length ∧
  (∀ i < curNr, MonoSliceOk curRp (curRm.getD i 0#32).toNat curRp.length) ∧
  bv nOut (σ sym) = polyEval nOut σ curRp curRm curRl curRh curNr

/-- 64-bit Bloom signature bit matching `ar_sigbit(sym)` in `Src/Poly.lean`. -/
def sigBit (sym : BitVec 32) : BitVec 64 :=
  1#64 <<< (((sym * 0x9E3779B1#32) >>> 26).toNat)

/-- Strict ascending variable ordering on the monomial slice `pool[off .. off + pool[off]]`. -/
def MonoSorted (pool : List (BitVec 32)) (off : Nat) : Prop :=
  (symListAt pool off).Pairwise (· < ·)

/-- Bloom signature soundness invariant for `n` polynomial terms `(pool, tm, ts)`. -/
def SigOk (pool tm : List (BitVec 32)) (ts : List (BitVec 64)) (n : Nat) : Prop :=
  ∀ i < n, ∀ x ∈ symListAt pool (tm.getD i 0#32).toNat,
    (ts.getD i 0#64 &&& sigBit (BitVec.ofNat 32 x)) ≠ 0#64

/-- All `rs_n` stored monomials in `rs_pool[rs_m[i]]` are strictly sorted. -/
def RulesSorted (rsPool rsM : List (BitVec 32)) (n : Nat) : Prop :=
  ∀ i < n, MonoSorted rsPool (rsM.getD i 0#32).toNat

/-! ## 3. Aligned Workspace Slab Groups -/

/-- `array ty ptr xs` followed by `align8`-rounding to `align8 (ty.bytes * xs.length)`. -/
def arrayPad (ty : Ty) (ptr : BitVec 64) (xs : List (Val ty)) : Mem 64 → Prop :=
  (SlabSeg.ofArrayAlign8 ty xs (ty.bytes * xs.length) rfl).pred ptr

/-- Allocated AIG arrays (`rhs0`, `rhs1`, `olit`). -/
def aigArraysMem (s : ArCtxState) (rhs0 rhs1 olit : List (BitVec 32)) : Mem 64 → Prop :=
  arrayPad i32 s.rhs0 rhs0 ⋆
  arrayPad i32 s.rhs1 rhs1 ⋆
  arrayPad i32 s.olit olit

/-- ART network & binding tables (`bind`, `rule_off`, `rule_n`, `partner`, `flipped`, `in_net`,
`out_ref`). -/
def netTablesMem (s : ArCtxState) (bindArr ruleOff ruleN partnerArr : List (BitVec 32))
    (flippedArr : List (BitVec 8)) (inNetArr outRefArr : List (BitVec 32)) : Mem 64 → Prop :=
  arrayPad i32 s.bind bindArr ⋆
  arrayPad i32 s.rule_off ruleOff ⋆
  arrayPad i32 s.rule_n ruleN ⋆
  arrayPad i32 s.partner partnerArr ⋆
  arrayPad i8 s.flipped flippedArr ⋆
  arrayPad i32 s.in_net inNetArr ⋆
  arrayPad i32 s.out_ref outRefArr

/-- Gate-validation scratch arrays (`stk_n`, `stk_p`, `memo_n`, `memo_v`, `dense`, `gsy`, `gcl`,
`gch`). -/
def gateScratchMem (s : ArCtxState) (stkN stkP memoN : List (BitVec 32))
    (memoV dense : List (BitVec 64)) (gsy : List (BitVec 32))
    (gcl gch : List (BitVec 64)) : Mem 64 → Prop :=
  arrayPad i32 s.stk_n stkN ⋆
  arrayPad i32 s.stk_p stkP ⋆
  arrayPad i32 s.memo_n memoN ⋆
  array64 s.memo_v memoV ⋆
  array64 s.dense dense ⋆
  arrayPad i32 s.gsy gsy ⋆
  array64 s.gcl gcl ⋆
  array64 s.gch gch

/-- Dynamic rule-store arrays (`rs_m`, `rs_l`, `rs_h`, `rs_pool`). -/
def rsMem (s : ArCtxState) (rsM : List (BitVec 32)) (rsL rsH : List (BitVec 64))
    (rsPool : List (BitVec 32)) : Mem 64 → Prop :=
  arrayPad i32 s.rs_m rsM ⋆
  array64 s.rs_l rsL ⋆
  array64 s.rs_h rsH ⋆
  arrayPad i32 s.rs_pool rsPool

/-- Dynamic target-polynomial ping-pong arrays (`tm[0..1]`, `ts/tl/th[0..1]`, `pool[0..1]`). -/
def tMem (s : ArCtxState) (tm0 tm1 : List (BitVec 32))
    (ts0 tl0 th0 ts1 tl1 th1 : List (BitVec 64))
    (pool0 pool1 : List (BitVec 32)) : Mem 64 → Prop :=
  arrayPad i32 (s.tm.getD 0 0#64) tm0 ⋆
  array64 (s.ts.getD 0 0#64) ts0 ⋆
  array64 (s.tl.getD 0 0#64) tl0 ⋆
  array64 (s.th.getD 0 0#64) th0 ⋆
  arrayPad i32 (s.tm.getD 1 0#64) tm1 ⋆
  array64 (s.ts.getD 1 0#64) ts1 ⋆
  array64 (s.tl.getD 1 0#64) tl1 ⋆
  array64 (s.th.getD 1 0#64) th1 ⋆
  arrayPad i32 (s.pool.getD 0 0#64) pool0 ⋆
  arrayPad i32 (s.pool.getD 1 0#64) pool1

/-- Dynamic merge/substitution scratch arrays (`qm..vq_skip`). -/
def qMem (s : ArCtxState) (qm : List (BitVec 32)) (qs ql qh : List (BitVec 64))
    (ix ix2 bx vqOff vq : List (BitVec 32)) (vqSkip : List (BitVec 8)) : Mem 64 → Prop :=
  arrayPad i32 s.qm qm ⋆
  array64 s.qs qs ⋆
  array64 s.ql ql ⋆
  array64 s.qh qh ⋆
  arrayPad i32 s.ix ix ⋆
  arrayPad i32 s.ix2 ix2 ⋆
  arrayPad i32 s.bx bx ⋆
  arrayPad i32 s.vq_off vqOff ⋆
  arrayPad i32 s.vq vq ⋆
  arrayPad i8 s.vq_skip vqSkip

/-- Dynamic `FLIP`-expansion scratch arrays (`rm`, `rl`, `rh`, `rm2`, `rl2`, `rh2`, `rpool`). -/
def rMem (s : ArCtxState) (rm : List (BitVec 32)) (rl rh : List (BitVec 64))
    (rm2 : List (BitVec 32)) (rl2 rh2 : List (BitVec 64))
    (rpool : List (BitVec 32)) : Mem 64 → Prop :=
  arrayPad i32 s.rm rm ⋆
  array64 s.rl rl ⋆
  array64 s.rh rh ⋆
  arrayPad i32 s.rm2 rm2 ⋆
  array64 s.rl2 rl2 ⋆
  array64 s.rh2 rh2 ⋆
  arrayPad i32 s.rpool rpool

end

/-! ## 4. AIG, `cSig`, and Word-Level End-to-End Theorems -/

public section

theorem AigRep.nodeVal_and {g : Aig} {rhs0 rhs1 olit : List (BitVec 32)}
    (ha : AigRep g rhs0 rhs1 olit) (ρ : Nat → Bool) {nd : Nat}
    (hgt : g.I < nd) (hle : nd ≤ g.M) :
    g.nodeVal ρ nd =
      (g.litVal ρ (rhs0.getD (nd - g.I - 1) 0#32).toNat &&
       g.litVal ρ (rhs1.getD (nd - g.I - 1) 0#32).toNat) := by
  have hj : nd - g.I - 1 < g.ands.length := by rw [ha.m_eq] at hle; omega
  have hwf := ha.ands_wf (nd - g.I - 1) hj
  have h1 : (g.andAt nd).1 / 2 < nd := by simp only [Aig.andAt]; omega
  have h2 : (g.andAt nd).2 / 2 < nd := by simp only [Aig.andAt]; omega
  rw [LeanQbe.T.Examples.Arisca.Aig.nodeVal_and g ρ nd (by omega) (by omega) h1 h2]
  simp only [Aig.andAt]
  rw [ha.rhs0_eq _ hj, ha.rhs1_eq _ hj]

theorem cSig_even (g : Aig) (ρ : Nat → Bool) (bindArr : List (BitVec 32)) (v : Nat) :
    cSig g ρ bindArr (2 * v) = g.litVal ρ (bindArr.getD v 0#32).toNat := by
  simp [cSig, show (2 * v) / 2 = v by omega, show (2 * v) % 2 = 0 by omega]

theorem cSig_odd (g : Aig) (ρ : Nat → Bool) (bindArr : List (BitVec 32)) (v : Nat) :
    cSig g ρ bindArr (2 * v + 1) = !(cSig g ρ bindArr (2 * v)) := by
  simp [cSig, show (2 * v + 1) / 2 = v by omega, show (2 * v) / 2 = v by omega,
    show (2 * v + 1) % 2 = 1 by omega, show (2 * v) % 2 = 0 by omega]

theorem cSig_flip (g : Aig) (ρ : Nat → Bool) (bindArr : List (BitVec 32)) (x : Nat) :
    cSig g ρ bindArr (2 * x + 1) = !(cSig g ρ bindArr (2 * x)) :=
  cSig_odd g ρ bindArr x

theorem cSig_half_mod (g : Aig) (ρ : Nat → Bool) (bindArr : List (BitVec 32)) (x : Nat) :
    cSig g ρ bindArr x = (cSig g ρ bindArr (2 * (x / 2)) ^^ (x % 2 == 1)) := by
  rw [cSig_even]; rfl

theorem BindRep.in_sig {s : ArCtxState} {g : Aig} {bindArr inNetArr outRefArr : List (BitVec 32)}
    (hb : BindRep s g bindArr inNetArr outRefArr) (ρ : Nat → Bool)
    {i : Nat} (hi : i < s.n_in.toNat) :
    cSig g ρ bindArr (2 * (inNetArr.getD i 0#32).toNat) = ρ i := by
  have hiI : i < g.I := by rw [← hb.in_eq]; exact hi
  have hin := hb.in_ok i hi
  rw [cSig_even, hin.2]
  show (g.nodeVal ρ ((2 * (i + 1)) / 2) ^^ ((2 * (i + 1)) % 2 == 1)) = ρ i
  rw [show (2 * (i + 1)) / 2 = i + 1 by omega, show (2 * (i + 1)) % 2 = 0 by omega,
    LeanQbe.T.Examples.Arisca.Aig.nodeVal_pi g ρ (i + 1) (by omega) (by omega)]
  simp

private theorem nat_xor_one_div_mod (x : Nat) :
    (x ^^^ 1) / 2 = x / 2 ∧ (x ^^^ 1) % 2 = 1 - x % 2 := by
  have hx : (x ^^^ 1) = if x % 2 = 0 then x + 1 else x - 1 := by
    apply Nat.eq_of_testBit_eq
    intro i
    cases i with
    | zero =>
      simp only [Nat.testBit_zero]
      by_cases h0 : x % 2 = 0
      · have h1 : (x + 1) % 2 = 1 := by omega
        simp [h0, h1]
      · have h1 : x % 2 = 1 := by omega
        have h2 : (x - 1) % 2 = 0 := by omega
        simp [h1, h2]
    | succ i =>
      have hbit1 : (1 : Nat).testBit (i + 1) = false := by
        rw [Nat.testBit, Nat.shiftRight_eq_div_pow,
          Nat.div_eq_of_lt (Nat.one_lt_pow (by omega) (by decide))]
        decide
      rw [Nat.testBit_xor, hbit1, Bool.xor_false]
      by_cases h0 : x % 2 = 0
      · simp only [h0, ↓reduceIte, Nat.testBit, Nat.shiftRight_eq_div_pow]
        have hd : (x + 1) / 2 ^ (i + 1) = x / 2 ^ (i + 1) := by
          rw [Nat.pow_succ', ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul]
          congr 1; omega
        rw [hd]
      · simp only [h0, ↓reduceIte, Nat.testBit, Nat.shiftRight_eq_div_pow]
        have hd : (x - 1) / 2 ^ (i + 1) = x / 2 ^ (i + 1) := by
          rw [Nat.pow_succ', ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul]
          congr 1; omega
        rw [hd]
  rw [hx]
  by_cases h0 : x % 2 = 0 <;> simp [h0] <;> omega

private theorem bv32_xor_bit0 (b r : BitVec 32) :
    (b ^^^ (r &&& 1#32)).toNat / 2 = b.toNat / 2 ∧
    (b ^^^ (r &&& 1#32)).toNat % 2 = ((b.toNat % 2) ^^^ (r.toNat % 2)) := by
  have hand : (r &&& 1#32).toNat = r.toNat % 2 := by
    rw [BitVec.toNat_and, show (1#32 : BitVec 32).toNat = 1 from rfl, Nat.and_one_is_mod]
  rw [BitVec.toNat_xor, hand]
  rcases Nat.mod_two_eq_zero_or_one r.toNat with hr0 | hr1
  · simp [hr0]
  · simp only [hr1, nat_xor_one_div_mod]
    rcases Nat.mod_two_eq_zero_or_one b.toNat with hb0 | hb1
    · rw [hb0]; decide
    · rw [hb1]; decide

theorem BindRep.out_sig {s : ArCtxState} {g : Aig} {bindArr inNetArr outRefArr : List (BitVec 32)}
    (hb : BindRep s g bindArr inNetArr outRefArr) (ρ : Nat → Bool)
    {j : Nat} (hj : j < s.n_out.toNat) :
    let r := (outRefArr.getD j 0#32).toNat
    (cSig g ρ bindArr (2 * (r / 2)) ^^ (r % 2 == 1)) = g.litVal ρ (g.outs.getD j 0) := by
  dsimp only
  have hout := hb.out_ok j hj
  let r32 := outRefArr.getD j 0#32
  let b := bindArr.getD (r32 >>> 1).toNat 0#32
  have hsh : (r32 >>> (1 : Nat)).toNat = r32.toNat / 2 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_one]
  rw [cSig_even, ← hsh]
  show (g.litVal ρ b.toNat ^^ (r32.toNat % 2 == 1)) = _
  have hxb := bv32_xor_bit0 b r32
  have hlit_xor : (g.litVal ρ b.toNat ^^ (r32.toNat % 2 == 1)) =
      g.litVal ρ (b ^^^ (r32 &&& 1#32)).toNat := by
    show (g.nodeVal ρ (b.toNat / 2) ^^ (b.toNat % 2 == 1) ^^ (r32.toNat % 2 == 1)) =
      (g.nodeVal ρ ((b ^^^ (r32 &&& 1#32)).toNat / 2) ^^
        ((b ^^^ (r32 &&& 1#32)).toNat % 2 == 1))
    rw [hxb.1, hxb.2]
    rcases Nat.mod_two_eq_zero_or_one b.toNat with hb0 | hb1 <;>
      rcases Nat.mod_two_eq_zero_or_one r32.toNat with hr0 | hr1 <;>
      cases g.nodeVal ρ (b.toNat / 2)
    all_goals simp_all
  rw [hlit_xor, hout.2.2]

/-- Word-level output identity connecting C0 `out_ref` polynomial to `outWord g ρ`. -/
theorem BindRep.outSum_eq {s : ArCtxState} {g : Aig}
    {bindArr inNetArr outRefArr : List (BitVec 32)}
    (hb : BindRep s g bindArr inNetArr outRefArr) (ρ : Nat → Bool) :
    let w := s.n_out.toNat
    let refs := (outRefArr.take w).map BitVec.toNat
    outSum w (cSig g ρ bindArr) refs 0 = BitVec.ofNat w (outWord g ρ) := by
  dsimp only
  have hout_len := hb.out_len
  have hout_eq := hb.out_eq
  have hlen : ((outRefArr.take s.n_out.toNat).map BitVec.toNat).length = g.outs.length := by
    simp only [List.length_map, List.length_take]; omega
  have hres := LeanQbe.T.Examples.Arisca.outSum_eq (w := s.n_out.toNat) (σ := cSig g ρ bindArr) g ρ
    ((outRefArr.take s.n_out.toNat).map BitVec.toNat) 0 ?_
  · rw [hlen, ← List.range_eq_range'] at hres
    simpa [outWord, outWordL] using hres
  · intro k hk
    simp only [List.length_map, List.length_take] at hk
    have hk_out : k < s.n_out.toNat := by omega
    have hk_arr : k < outRefArr.length := by omega
    have hnth : nthN ((outRefArr.take s.n_out.toNat).map BitVec.toNat) k =
        (outRefArr.getD k 0#32).toNat := by
      rw [nthN_eq_getD]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_take,
        hk_out, ↓reduceIte, List.getElem?_eq_getElem hk_arr, Option.map_some, Option.getD_some]
    rw [hnth, Nat.zero_add]
    exact hb.out_sig ρ hk_out

/-- Word-level input identity connecting half of C0 `in_net` (`0` or `n`) to `inWord`. -/
theorem BindRep.inSum_eq {s : ArCtxState} {g : Aig}
    {bindArr inNetArr outRefArr : List (BitVec 32)}
    (hb : BindRep s g bindArr inNetArr outRefArr) (ρ : Nat → Bool)
    (signed : Bool) (off : Nat) (hoff : off = 0 ∨ off = g.I / 2) :
    let w := s.n_out.toNat
    let n := g.I / 2
    let xs := ((inNetArr.drop off).take n).map BitVec.toNat
    inSum w (cSig g ρ bindArr) signed n xs 0 = BitVec.ofInt w (inWord signed n ρ off) := by
  dsimp only
  have heven := hb.i_even.1
  have hin_eq := hb.in_eq
  have hin_len := hb.in_len
  have hn_add : off + g.I / 2 ≤ s.n_in.toNat := by
    rcases hoff with rfl | rfl <;> omega
  have hlen : (((inNetArr.drop off).take (g.I / 2)).map BitVec.toNat).length = g.I / 2 := by
    simp only [List.length_map, List.length_take, List.length_drop]; omega
  have hres := LeanQbe.T.Examples.Arisca.inSum_eq (w := s.n_out.toNat) (σ := cSig g ρ bindArr)
    signed (g.I / 2) ρ off (((inNetArr.drop off).take (g.I / 2)).map BitVec.toNat) 0 ?_
  · rw [hlen, ← List.range_eq_range'] at hres
    simpa [inWord] using hres
  · intro k hk
    simp only [List.length_map, List.length_take, List.length_drop] at hk
    have hk' : k < g.I / 2 := by omega
    have hok : off + k < inNetArr.length := by omega
    have hnth : nthN (((inNetArr.drop off).take (g.I / 2)).map BitVec.toNat) k =
        (inNetArr.getD (off + k) 0#32).toNat := by
      rw [nthN_eq_getD]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_take,
        hk', ↓reduceIte, List.getElem?_drop, List.getElem?_eq_getElem hok,
        Option.map_some, Option.getD_some]
    rw [hnth, Nat.zero_add]
    exact hb.in_sig ρ (by omega)

/-! ## 5. Monomial, Polynomial & Permutation Lemmas -/

theorem monoValL_nil (σ : Nat → Bool) : monoValL σ [] = true := rfl

theorem monoValL_cons (σ : Nat → Bool) (s : Nat) (xs : List Nat) :
    monoValL σ (s :: xs) = (σ s && monoValL σ xs) := rfl

theorem monoValL_eq_decide (σ : Nat → Bool) (xs : List Nat) :
    monoValL σ xs = decide (∀ s ∈ xs, σ s = true) := by
  induction xs with
  | nil => simp [monoValL]
  | cons x xs ih =>
    rw [monoValL_cons, ih]
    cases hx : σ x <;> simp [hx]

theorem monoValL_eq_of_mem_iff {σ : Nat → Bool} {xs ys : List Nat}
    (h : ∀ s, s ∈ xs ↔ s ∈ ys) : monoValL σ xs = monoValL σ ys := by
  rw [monoValL_eq_decide, monoValL_eq_decide]
  congr 1
  exact propext ⟨fun hx s hs => hx s ((h s).mpr hs), fun hy s hs => hy s ((h s).mp hs)⟩

theorem monoValL_false_of_mem {σ : Nat → Bool} {xs : List Nat} {s : Nat}
    (hm : s ∈ xs) (hs : σ s = false) : monoValL σ xs = false := by
  rw [monoValL_eq_decide, decide_eq_false_iff_not]
  intro h; exact absurd (h s hm) (by rw [hs]; decide)

theorem mem_symListAt_iff (pool : List (BitVec 32)) (off x : Nat) :
    x ∈ symListAt pool off ↔
      ∃ i, 1 ≤ i ∧ i ≤ (pool.getD off 0#32).toNat ∧ (pool.getD (off + i) 0#32).toNat = x := by
  simp only [symListAt, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i + 1, Nat.succ_le_succ (Nat.zero_le _), hi, by congr 2; omega⟩
  · rintro ⟨i, h1, hle, rfl⟩
    exact ⟨i - 1, by omega, by congr 2; omega⟩

theorem monoSorted_congr {p1 p2 : List (BitVec 32)} {o1 o2 : Nat}
    (h : symListAt p1 o1 = symListAt p2 o2) (hs : MonoSorted p1 o1) : MonoSorted p2 o2 := by
  simpa [MonoSorted, h] using hs

theorem monoSorted_iff (pool : List (BitVec 32)) (off : Nat) :
    MonoSorted pool off ↔
      ∀ i j, i < j → j < (pool.getD off 0#32).toNat →
        (pool.getD (off + 1 + i) 0#32).toNat < (pool.getD (off + 1 + j) 0#32).toNat := by
  unfold MonoSorted symListAt
  rw [List.pairwise_iff_getElem]
  simp only [List.length_map, List.length_range, List.getElem_map, List.getElem_range]
  exact ⟨fun h i j hij hj => h i j (by omega) hj hij,
    fun h i j _ hj hij => h i j hij hj⟩

theorem monoSorted_of_le1 {pool : List (BitVec 32)} {off : Nat}
    (hlen : (pool.getD off 0#32).toNat ≤ 1) : MonoSorted pool off := by
  rw [monoSorted_iff]; intro i j hij hj; omega

theorem monoSorted_two {pool : List (BitVec 32)} {off : Nat}
    (hlen : (pool.getD off 0#32).toNat = 2)
    (hlt : (pool.getD (off + 1) 0#32).toNat < (pool.getD (off + 2) 0#32).toNat) :
    MonoSorted pool off := by
  rw [monoSorted_iff]; intro i j hij hj
  have hi0 : i = 0 := by omega
  have hj1 : j = 1 := by omega
  subst hi0; subst hj1; simpa using hlt

theorem sigOk_not_and_zero {pool tm : List (BitVec 32)} {ts : List (BitVec 64)} {n i : Nat}
    (hs : SigOk pool tm ts n) (hi : i < n) (sym : BitVec 32)
    (hz : (ts.getD i 0#64 &&& sigBit sym) = 0#64) :
    sym.toNat ∉ symListAt pool (tm.getD i 0#32).toNat := by
  intro hmem
  have hne := hs i hi sym.toNat hmem
  rw [BitVec.ofNat_toNat] at hne
  exact hne hz

theorem sigOk_empty (pool tm : List (BitVec 32)) (ts : List (BitVec 64)) :
    SigOk pool tm ts 0 := fun _ hi => absurd hi (Nat.not_lt_zero _)

theorem foldl_add_init {α : Type} {w : Nat} (f : α → BitVec w) :
    ∀ (l : List α) (init : BitVec w),
      l.foldl (fun acc x => acc + f x) init = init + l.foldl (fun acc x => acc + f x) 0#w
  | [], init => by simp
  | x :: xs, init => by
    simp only [List.foldl_cons, BitVec.zero_add]
    rw [foldl_add_init f xs (init + f x), foldl_add_init f xs (f x), BitVec.add_assoc]

theorem foldl_add_append {α : Type} {w : Nat} (f : α → BitVec w) (l1 l2 : List α) :
    (l1 ++ l2).foldl (fun acc x => acc + f x) 0#w =
      l1.foldl (fun acc x => acc + f x) 0#w + l2.foldl (fun acc x => acc + f x) 0#w := by
  rw [List.foldl_append, foldl_add_init f l2]

theorem foldl_add_perm {α : Type} {w : Nat} (f : α → BitVec w) {l1 l2 : List α}
    (hp : l1.Perm l2) :
    l1.foldl (fun acc x => acc + f x) 0#w = l2.foldl (fun acc x => acc + f x) 0#w := by
  induction hp with
  | nil => rfl
  | cons x _ ih =>
    simp only [List.foldl_cons, BitVec.zero_add]
    rw [foldl_add_init, foldl_add_init f _ (f x), ih]
  | swap x y l =>
    simp only [List.foldl_cons, BitVec.zero_add]
    rw [foldl_add_init, foldl_add_init f l (f x + f y), BitVec.add_comm (f x) (f y)]
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem polyEvalRange_zero (nOut : Nat) (σ : Nat → Bool) (pool mOff : List (BitVec 32))
    (cl ch : List (BitVec 64)) (lo : Nat) :
    polyEvalRange nOut σ pool mOff cl ch lo 0 = 0#nOut := rfl

theorem polyEvalRange_succ (nOut : Nat) (σ : Nat → Bool) (pool mOff : List (BitVec 32))
    (cl ch : List (BitVec 64)) (lo n : Nat) :
    polyEvalRange nOut σ pool mOff cl ch lo (n + 1) =
      polyEvalRange nOut σ pool mOff cl ch lo n +
        termEval nOut σ pool mOff cl ch (lo + n) := by
  simp only [polyEvalRange, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem polyEvalRange_add (nOut : Nat) (σ : Nat → Bool) (pool mOff : List (BitVec 32))
    (cl ch : List (BitVec 64)) (lo a b : Nat) :
    polyEvalRange nOut σ pool mOff cl ch lo (a + b) =
      polyEvalRange nOut σ pool mOff cl ch lo a +
        polyEvalRange nOut σ pool mOff cl ch (lo + a) b := by
  induction b with
  | zero => simp [polyEvalRange_zero]
  | succ b ih =>
    rw [← Nat.add_assoc, polyEvalRange_succ, polyEvalRange_succ, ih, BitVec.add_assoc,
      show lo + (a + b) = lo + a + b by omega]

theorem polyEval_zero (nOut : Nat) (σ : Nat → Bool) (pool mOff : List (BitVec 32))
    (cl ch : List (BitVec 64)) :
    polyEval nOut σ pool mOff cl ch 0 = 0#nOut := rfl

theorem polyEval_succ (nOut : Nat) (σ : Nat → Bool) (pool mOff : List (BitVec 32))
    (cl ch : List (BitVec 64)) (n : Nat) :
    polyEval nOut σ pool mOff cl ch (n + 1) =
      polyEval nOut σ pool mOff cl ch n + termEval nOut σ pool mOff cl ch n := by
  simpa [polyEval] using polyEvalRange_succ nOut σ pool mOff cl ch 0 n

theorem polyEvalIdxOf_nil (nOut : Nat) (σ : Nat → Bool) (pool mOff : List (BitVec 32))
    (cl ch : List (BitVec 64)) (ix : List (BitVec 32)) (lo : Nat) :
    polyEvalIdxOf nOut σ pool mOff cl ch ix lo 0 = 0#nOut := rfl

theorem polyEvalIdxOf_succ (nOut : Nat) (σ : Nat → Bool) (pool mOff : List (BitVec 32))
    (cl ch : List (BitVec 64)) (ix : List (BitVec 32)) (lo n : Nat) :
    polyEvalIdxOf nOut σ pool mOff cl ch ix lo (n + 1) =
      polyEvalIdxOf nOut σ pool mOff cl ch ix lo n +
        termEval nOut σ pool mOff cl ch (ix.getD (lo + n) 0#32).toNat := by
  simp only [polyEvalIdxOf, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem polyEvalIdxOf_add (nOut : Nat) (σ : Nat → Bool) (pool mOff : List (BitVec 32))
    (cl ch : List (BitVec 64)) (ix : List (BitVec 32)) (lo a b : Nat) :
    polyEvalIdxOf nOut σ pool mOff cl ch ix lo (a + b) =
      polyEvalIdxOf nOut σ pool mOff cl ch ix lo a +
        polyEvalIdxOf nOut σ pool mOff cl ch ix (lo + a) b := by
  induction b with
  | zero => simp [polyEvalIdxOf_nil]
  | succ b ih =>
    rw [← Nat.add_assoc, polyEvalIdxOf_succ, polyEvalIdxOf_succ, ih, BitVec.add_assoc,
      show lo + (a + b) = lo + a + b by omega]

theorem polyEvalIdxOf_perm (nOut : Nat) (σ : Nat → Bool) (pool mOff : List (BitVec 32))
    (cl ch : List (BitVec 64)) {ix1 ix2 : List (BitVec 32)} {n : Nat}
    (hp : ((List.range n).map (fun k => (ix1.getD k 0#32).toNat)).Perm
      ((List.range n).map (fun k => (ix2.getD k 0#32).toNat))) :
    polyEvalIdxOf nOut σ pool mOff cl ch ix1 0 n =
      polyEvalIdxOf nOut σ pool mOff cl ch ix2 0 n := by
  have h1 : ∀ ix : List (BitVec 32), polyEvalIdxOf nOut σ pool mOff cl ch ix 0 n =
      ((List.range n).map (fun k => (ix.getD k 0#32).toNat)).foldl
        (fun acc idx => acc + termEval nOut σ pool mOff cl ch idx) 0#nOut := by
    intro ix; simp [polyEvalIdxOf, List.foldl_map]
  rw [h1 ix1, h1 ix2]
  exact foldl_add_perm (termEval nOut σ pool mOff cl ch) hp

theorem polyEvalIdxOf_id (nOut : Nat) (σ : Nat → Bool) (pool mOff : List (BitVec 32))
    (cl ch : List (BitVec 64)) (ix : List (BitVec 32)) (n : Nat)
    (hid : ∀ k < n, (ix.getD k 0#32).toNat = k) :
    polyEvalIdxOf nOut σ pool mOff cl ch ix 0 n = polyEval nOut σ pool mOff cl ch n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [polyEvalIdxOf_succ, polyEval, polyEvalRange_succ,
      ih (fun k hk => hid k (Nat.lt_succ_of_lt hk)), Nat.zero_add,
      hid n (Nat.lt_succ_self n)]
    rfl

/-! ## 6. `SlabChain` Alignment & Heap Collapse Helpers -/

theorem arrayPad_eq_array {ty : Ty} {ptr : BitVec 64} {xs : List (Val ty)}
    (h : (ty.bytes * xs.length) % 8 = 0) :
    arrayPad ty ptr xs = array (t := ty) ptr xs := by
  unfold arrayPad SlabSeg.ofArrayAlign8 SlabSeg.ofArray
  dsimp only
  have ha : align8 (ty.bytes * xs.length) = ty.bytes * xs.length := by unfold align8; omega
  rw [ha, Nat.sub_self, region_zero, sep_emp]

theorem arrayPad_eq_array64 (ptr : BitVec 64) (xs : List (BitVec 64)) :
    arrayPad i64 ptr xs = array64 ptr xs := by
  rw [arrayPad_eq_array (by simp [Ty.bytes, Ty.size]), array64_eq_array]

theorem align8_add_mul8 {a b : Nat} (ha : a % 8 = 0) :
    align8 (a + b) = a + align8 b := by
  unfold align8; omega

theorem align8_sub_add_mul8 {a b : Nat} (ha : a % 8 = 0) :
    align8 (a + b) - (a + b) = align8 b - b := by
  rw [align8_add_mul8 ha]; omega

private theorem setWidth_self {w : Nat} (v : BitVec w) : v.setWidth w = v :=
  BitVec.eq_of_toNat_eq (by simp)

private theorem toBytes_bv_toInt {b : Nat} (v : BitVec (8 * b)) :
    Int.toBytes b v.toInt = Int.toBytes b (v.toNat : Int) := by
  rw [← Int.toBytes_emod, ← Int.toBytes_emod (x := (v.toNat : Int))]
  congr 1
  rw [BitVec.toInt_eq_msb_cond]
  cases v.msb
  · simp only [Bool.false_eq_true, ↓reduceIte]
  · simp only [↓reduceIte, Int.natCast_pow, Int.cast_ofNat_Int, Int.sub_emod_right]

private theorem cell_u8_eq_byte1 (a : BitVec 64) (v : BitVec 8) :
    cell (t := i8) a v = byte1 a (v.setWidth 64) := by
  have h1 : Int.toBytes 1 (((v.setWidth 8).setWidth 8).toInt) =
      Int.toBytes 1 ((v.setWidth 64).toNat : Int) := by
    rw [setWidth_self, setWidth_self, toBytes_bv_toInt (b := 1) v]
    have hv := v.isLt
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
  show Eq ((Int.toBytes 1 (((v.setWidth 8).setWidth 8).toInt)).At a) =
    Eq ((Int.toBytes 1 (v.setWidth 64).toNat).At a)
  rw [h1]

private theorem cell_u32_eq_int4 (a : BitVec 64) (v : BitVec 32) :
    cell (t := i32) a v = int4 a (v.setWidth 64) := by
  have h1 : Int.toBytes 4 (((v.setWidth 32).setWidth 32).toInt) =
      Int.toBytes 4 ((v.setWidth 64).toNat : Int) := by
    rw [setWidth_self, setWidth_self, toBytes_bv_toInt (b := 4) v]
    have hv := v.isLt
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
  show Eq ((Int.toBytes 4 (((v.setWidth 32).setWidth 32).toInt)).At a) =
    Eq ((Int.toBytes 4 (v.setWidth 64).toNat).At a)
  rw [h1]

private theorem cell64_eq_word8 (a v : BitVec 64) : cell64 a v = word8 a v := by
  show Eq ((Int.toBytes 8 v.toInt).At a) = Eq ((Int.toBytes 8 v.toNat).At a)
  rw [toBytes_bv_toInt (b := 8) v]

private theorem byte1Array_eq_array_u8 (a : BitVec 64) (xs : List (BitVec 64)) :
    byte1Array a xs = array (t := i8) a (xs.map (BitVec.setWidth 8)) := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih =>
    rw [List.map_cons, byte1Array_cons, array_cons, ih]
    have hcell : byte1 a x = cell (t := i8) a (x.setWidth 8) := by
      rw [cell_u8_eq_byte1]
      have hsw : ((x.setWidth 8).setWidth 64).toNat = x.toNat % 2 ^ 8 := by
        rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth,
          Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide))]
      show Eq ((Int.toBytes 1 x.toNat).At a) =
        Eq ((Int.toBytes 1 ((x.setWidth 8).setWidth 64).toNat).At a)
      rw [← Int.toBytes_emod, ← Int.toBytes_emod (x := (((x.setWidth 8).setWidth 64).toNat : Int))]
      congr 2
      simp only [Int.take, hsw, Int.natCast_emod, Int.natCast_pow, Int.cast_ofNat_Int,
        Nat.reduceMul]
      rw [show (2 ^ 8 : Int) = (256 : Int) from rfl, Int.emod_emod]
    rw [hcell]; rfl

private theorem int4Array_eq_array_u32 (a : BitVec 64) (xs : List (BitVec 64)) :
    int4Array a xs = array (t := i32) a (xs.map (BitVec.setWidth 32)) := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih =>
    rw [List.map_cons, int4Array_cons, array_cons, ih]
    have hcell : int4 a x = cell (t := i32) a (x.setWidth 32) := by
      rw [cell_u32_eq_int4]
      have hsw : ((x.setWidth 32).setWidth 64).toNat = x.toNat % 2 ^ 32 := by
        rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth,
          Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide))]
      show Eq ((Int.toBytes 4 x.toNat).At a) =
        Eq ((Int.toBytes 4 ((x.setWidth 32).setWidth 64).toNat).At a)
      rw [← Int.toBytes_emod, ← Int.toBytes_emod (x := (((x.setWidth 32).setWidth 64).toNat : Int))]
      congr 2
      simp only [Int.take, hsw, Int.natCast_emod, Int.natCast_pow, Int.cast_ofNat_Int,
        Nat.reduceMul]
      rw [show (2 ^ 32 : Int) = (4294967296 : Int) from rfl, Int.emod_emod]
    rw [hcell]; rfl

private theorem word8Array_eq_array64 (a : BitVec 64) (xs : List (BitVec 64)) :
    word8Array a xs = array64 a xs := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih => rw [word8Array_cons, array64_cons, cell64_eq_word8, ih]

theorem region_to_array_u8 {a : BitVec 64} (n : Nat) (hn : n ≤ 2 ^ 64) {f : Mem 64}
    (hf : region a n f) : ∃ xs : List (BitVec 8), xs.length = n ∧ array (t := i8) a xs f := by
  obtain ⟨xs, hlen, harr⟩ := region_to_byte1Array n hn hf
  rw [byte1Array_eq_array_u8] at harr
  exact ⟨xs.map (BitVec.setWidth 8), by simp [hlen], harr⟩

theorem region_to_array_u32 {a : BitVec 64} (n : Nat) (hn : 4 * n ≤ 2 ^ 64) {f : Mem 64}
    (hf : region a (4 * n) f) :
    ∃ xs : List (BitVec 32), xs.length = n ∧ array (t := i32) a xs f := by
  obtain ⟨xs, hlen, harr⟩ := region_to_int4Array n hn hf
  rw [int4Array_eq_array_u32] at harr
  exact ⟨xs.map (BitVec.setWidth 32), by simp [hlen], harr⟩

theorem region_to_array_u64 {a : BitVec 64} (n : Nat) (hn : 8 * n ≤ 2 ^ 64) {f : Mem 64}
    (hf : region a (8 * n) f) : ∃ xs : List (BitVec 64), xs.length = n ∧ array64 a xs f := by
  obtain ⟨xs, hlen, harr⟩ := region_to_word8Array n hn hf
  rw [word8Array_eq_array64] at harr
  exact ⟨xs, hlen, harr⟩

private def decodeU8 : List UInt8 → List (BitVec 8)
  | [] => []
  | b :: bs => BitVec.ofNat 8 b.toNat :: decodeU8 bs

private def decodeU32 : Nat → List UInt8 → List (BitVec 32)
  | 0, _ => []
  | n + 1, bs => BitVec.ofInt 32 (Int.ofBytes (bs.take 4)) :: decodeU32 n (bs.drop 4)

private def decodeU64 : Nat → List UInt8 → List (BitVec 64)
  | 0, _ => []
  | n + 1, bs => BitVec.ofInt 64 (Int.ofBytes (bs.take 8)) :: decodeU64 n (bs.drop 8)

private theorem toBytes_ofBytes_u32 (bs : List UInt8) (hl : bs.length = 4) :
    Int.toBytes 4 ((BitVec.ofInt 32 (Int.ofBytes bs)).setWidth 32).toInt = bs := by
  rw [setWidth_self, toBytes_bv_toInt (b := 4) (BitVec.ofInt 32 (Int.ofBytes bs))]
  have h1 : ((BitVec.ofInt 32 (Int.ofBytes bs)).toNat : Int) % (2 ^ (8 * 4) : Int) =
      ((BitVec.ofInt 64 (Int.ofBytes bs)).toNat : Int) % (2 ^ (8 * 4) : Int) := by
    simp only [BitVec.toNat_ofInt]
    have hnn1 : 0 ≤ Int.ofBytes bs % (2 : Int) ^ 32 := Int.emod_nonneg _ (by decide)
    have hnn2 : 0 ≤ Int.ofBytes bs % (2 : Int) ^ 64 := Int.emod_nonneg _ (by decide)
    have h32 : ((2 : Int) ^ 32) = ((2 ^ 32 : Nat) : Int) := by decide
    have h64 : ((2 : Int) ^ 64) = ((2 ^ 64 : Nat) : Int) := by decide
    rw [h32] at hnn1
    rw [h64] at hnn2
    rw [Int.toNat_of_nonneg hnn1, Int.toNat_of_nonneg hnn2]
    rw [show (2 ^ (8 * 4) : Int) = ((2 ^ 32 : Nat) : Int) from by decide,
      Int.emod_emod,
      Int.emod_emod_of_dvd _ (by decide : ((2 ^ 32 : Nat) : Int) ∣ ((2 ^ 64 : Nat) : Int))]
  rw [← Int.toBytes_emod]
  have heq : Int.toBytes 4 (Int.take ((BitVec.ofInt 32 (Int.ofBytes bs)).toNat : Int) (8 * 4)) =
      Int.toBytes 4 (Int.take ((BitVec.ofInt 64 (Int.ofBytes bs)).toNat : Int) (8 * 4)) := by
    simp only [Int.take]; rw [h1]
  rw [heq, Int.toBytes_emod]
  grind

private theorem toBytes_ofBytes_u64 (bs : List UInt8) (hl : bs.length = 8) :
    Int.toBytes 8 ((BitVec.ofInt 64 (Int.ofBytes bs)).toInt) = bs := by
  rw [toBytes_bv_toInt (b := 8) (BitVec.ofInt 64 (Int.ofBytes bs))]
  grind

private theorem At_eq_array_u8 (a : BitVec 64) :
    ∀ (bs : List UInt8), bs.length ≤ 2 ^ 64 →
      Eq (bs.At a) = array (t := i8) a (decodeU8 bs)
  | [], _ => by
    simp only [decodeU8]
    exact (eq_nil_At a).symm
  | b :: bs, hlen => by
    have hblt := b.toNat_lt
    have h1 : bs.length + 1 ≤ 2 ^ 64 := by simpa using hlen
    have ih := At_eq_array_u8 (a + BitVec.ofNat 64 1) bs (by omega)
    have hcell : Eq ([b].At a) = cell (t := i8) a (BitVec.ofNat 8 b.toNat) := by
      rw [cell_u8_eq_byte1]
      have hsw : ((BitVec.ofNat 8 b.toNat).setWidth 64).toNat = b.toNat := by
        rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hblt,
          Nat.mod_eq_of_lt (by omega)]
      show Eq ([b].At a) = Eq ((Int.toBytes 1 ((BitVec.ofNat 8 b.toNat).setWidth 64).toNat).At a)
      rw [hsw, toBytes_u8 b]
    rw [decodeU8, array_cons, show (b :: bs) = [b] ++ bs from rfl,
      eq_append_At a [b] bs (by simp; omega), List.length_singleton, hcell, ih]
    rfl

private theorem At_eq_array_u32 (a : BitVec 64) :
    ∀ (n : Nat) (bs : List UInt8), bs.length = 4 * n → 4 * n ≤ 2 ^ 64 →
      Eq (bs.At a) = array (t := i32) a (decodeU32 n bs)
  | 0, bs, hlen, _ => by
    simp only [Nat.mul_zero, List.length_eq_zero_iff] at hlen; subst hlen
    simp only [decodeU32]; exact (eq_nil_At a).symm
  | n + 1, bs, hlen, hfit => by
    have h4 : (bs.take 4).length = 4 := by simp [hlen]; omega
    have hdrop : (bs.drop 4).length = 4 * n := by simp [hlen]; omega
    have ih := At_eq_array_u32 (a + BitVec.ofNat 64 4) n (bs.drop 4) hdrop (by omega)
    have hcell : Eq ((bs.take 4).At a) =
        cell (t := i32) a (BitVec.ofInt 32 (Int.ofBytes (bs.take 4))) := by
      show Eq ((bs.take 4).At a) =
        Eq ((Int.toBytes 4 (((BitVec.ofInt 32 (Int.ofBytes (bs.take 4))).setWidth 32).setWidth
          32).toInt).At a)
      rw [setWidth_self, toBytes_ofBytes_u32 _ h4]
    conv => lhs; rw [← List.take_append_drop 4 bs]
    rw [eq_append_At a (bs.take 4) (bs.drop 4) (by rw [h4, hdrop]; omega), h4,
      decodeU32, array_cons, hcell, ih]
    rfl

private theorem At_eq_array64 (a : BitVec 64) :
    ∀ (n : Nat) (bs : List UInt8), bs.length = 8 * n → 8 * n ≤ 2 ^ 64 →
      Eq (bs.At a) = array64 a (decodeU64 n bs)
  | 0, bs, hlen, _ => by
    simp only [Nat.mul_zero, List.length_eq_zero_iff] at hlen; subst hlen
    simp only [decodeU64, array64_nil]; exact (eq_nil_At a).symm
  | n + 1, bs, hlen, hfit => by
    have h8 : (bs.take 8).length = 8 := by simp [hlen]; omega
    have hdrop : (bs.drop 8).length = 8 * n := by simp [hlen]; omega
    have ih := At_eq_array64 (a + 8) n (bs.drop 8) hdrop (by omega)
    have hcell : Eq ((bs.take 8).At a) =
        cell64 a (BitVec.ofInt 64 (Int.ofBytes (bs.take 8))) := by
      show Eq ((bs.take 8).At a) =
        Eq ((Int.toBytes 8 (BitVec.ofInt 64 (Int.ofBytes (bs.take 8))).toInt).At a)
      rw [toBytes_ofBytes_u64 _ h8]
    conv => lhs; rw [← List.take_append_drop 8 bs]
    rw [eq_append_At a (bs.take 8) (bs.drop 8) (by rw [h8, hdrop]; omega), h8,
      decodeU64, array64_cons, hcell, show a + 8#64 = a + 8 from rfl, ih]

theorem arrayPad_to_region {ty : Ty} {ptr : BitVec 64} {xs : List (Val ty)} {m : Mem 64}
    (hfit : align8 (ty.bytes * xs.length) ≤ 2 ^ 64)
    (hm : arrayPad ty ptr xs m) :
    region ptr (align8 (ty.bytes * xs.length)) m :=
  (SlabSeg.ofArrayAlign8 ty xs (ty.bytes * xs.length) rfl).toReg ptr m hfit hm

theorem array64_to_region {ptr : BitVec 64} {xs : List (BitVec 64)} {m : Mem 64}
    (hfit : 8 * xs.length ≤ 2 ^ 64) (hm : array64 ptr xs m) :
    region ptr (8 * xs.length) m :=
  (SlabSeg.ofArray64 xs xs.length rfl).toReg ptr m hfit hm

theorem region_merge_pad_u8 {a : BitVec 64} {xs : List (BitVec 8)} {R : Mem 64 → Prop} {m : Mem 64}
    (h : (array (t := i8) a xs ⋆ region (a + BitVec.ofNat 64 xs.length)
      (align8 xs.length - xs.length) ⋆ R) m) :
    (arrayPad i8 a xs ⋆ R) m := by
  simpa [arrayPad, SlabSeg.ofArrayAlign8, SlabSeg.ofArray, Ty.bytes, Ty.size, sep_assoc] using h

theorem region_merge_pad_u32 {a : BitVec 64} {xs : List (BitVec 32)} {R : Mem 64 → Prop}
    {m : Mem 64}
    (h : (array (t := i32) a xs ⋆ region (a + BitVec.ofNat 64 (4 * xs.length))
      (align8 (4 * xs.length) - 4 * xs.length) ⋆ R) m) :
    (arrayPad i32 a xs ⋆ R) m := by
  simpa [arrayPad, SlabSeg.ofArrayAlign8, SlabSeg.ofArray, Ty.bytes, Ty.size, sep_assoc] using h

private theorem region_pop_split {ty : Ty} {w : BitVec 64} {top rem : Nat}
    {m : Mem 64} {R : Mem 64 → Prop} (n : Nat)
    (hfit : align8 top - top + ty.bytes * n ≤ rem)
    (hle64 : rem ≤ 2 ^ 64)
    (h : (region (w + BitVec.ofNat 64 top) rem ⋆ R) m) :
    (region (w + BitVec.ofNat 64 (align8 top)) (ty.bytes * n) ⋆
     region (w + BitVec.ofNat 64 top) (align8 top - top) ⋆
     region (w + BitVec.ofNat 64 (align8 top + ty.bytes * n))
       (rem - (align8 top - top + ty.bytes * n)) ⋆ R) m := by
  have hge := align8_ge top
  have hn1 :
      align8 top - top + (ty.bytes * n + (rem - (align8 top - top + ty.bytes * n))) = rem := by
    omega
  have hm1 := h
  rw [← hn1, region_split (by omega), sep_assoc] at hm1
  have hadr1 : w + BitVec.ofNat 64 top + BitVec.ofNat 64 (align8 top - top) =
      w + BitVec.ofNat 64 (align8 top) := by
    rw [BitVec.add_assoc]; congr 1
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  rw [hadr1] at hm1
  have hm2 := hm1
  rw [region_split (a := w + BitVec.ofNat 64 (align8 top)) (by omega)] at hm2
  have hadr2 : w + BitVec.ofNat 64 (align8 top) + BitVec.ofNat 64 (ty.bytes * n) =
      w + BitVec.ofNat 64 (align8 top + ty.bytes * n) := by
    rw [BitVec.add_assoc]; congr 1
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [hadr2] at hm2
  exact sep_cast hm2 (by ac_rfl)

private theorem decodeU8_length : ∀ bs : List UInt8, (decodeU8 bs).length = bs.length
  | [] => rfl
  | _ :: bs => by simp [decodeU8, decodeU8_length bs]

private theorem decodeU32_length : ∀ (n : Nat) (bs : List UInt8), (decodeU32 n bs).length = n
  | 0, _ => rfl
  | n + 1, bs => by simp [decodeU32, decodeU32_length n]

private theorem decodeU64_length : ∀ (n : Nat) (bs : List UInt8), (decodeU64 n bs).length = n
  | 0, _ => rfl
  | n + 1, bs => by simp [decodeU64, decodeU64_length n]

theorem region_pop_alloc_u8 {w : BitVec 64} {top rem : Nat} {m : Mem 64} {R : Mem 64 → Prop}
    (n : Nat) (hfit : align8 top - top + n ≤ rem) (hle64 : rem ≤ 2 ^ 64)
    (h : (region (w + BitVec.ofNat 64 top) rem ⋆ R) m) :
    ∃ xs : List (BitVec 8), xs.length = n ∧
      (region (w + BitVec.ofNat 64 top) (align8 top - top) ⋆
       array (t := i8) (w + BitVec.ofNat 64 (align8 top)) xs ⋆
       region (w + BitVec.ofNat 64 (align8 top + n)) (rem - (align8 top - top + n)) ⋆ R) m := by
  have hm := region_pop_split (ty := i8) n (by simpa [Ty.bytes, Ty.size] using hfit) hle64 h
  simp only [Ty.bytes, Ty.size, Nat.reduceDiv, Nat.reduceAdd, Nat.one_mul] at hm
  rw [sep_assoc, sep_assoc] at hm
  obtain ⟨bs, hbl, hmem⟩ := region_sep_elim hm
  refine ⟨decodeU8 bs, by rw [decodeU8_length, hbl], ?_⟩
  rw [At_eq_array_u8 _ bs (by omega)] at hmem
  exact sep_cast hmem (by ac_rfl)

theorem region_pop_alloc_u32 {w : BitVec 64} {top rem : Nat} {m : Mem 64} {R : Mem 64 → Prop}
    (n : Nat) (hfit : align8 top - top + 4 * n ≤ rem) (hle64 : rem ≤ 2 ^ 64)
    (h : (region (w + BitVec.ofNat 64 top) rem ⋆ R) m) :
    ∃ xs : List (BitVec 32), xs.length = n ∧
      (region (w + BitVec.ofNat 64 top) (align8 top - top) ⋆
       array (t := i32) (w + BitVec.ofNat 64 (align8 top)) xs ⋆
       region (w + BitVec.ofNat 64 (align8 top + 4 * n))
         (rem - (align8 top - top + 4 * n)) ⋆ R) m := by
  have hm := region_pop_split (ty := i32) n (by simpa [Ty.bytes, Ty.size] using hfit) hle64 h
  simp only [Ty.bytes, Ty.size, Nat.reduceDiv, Nat.reduceAdd] at hm
  rw [sep_assoc, sep_assoc] at hm
  obtain ⟨bs, hbl, hmem⟩ := region_sep_elim hm
  refine ⟨decodeU32 n bs, decodeU32_length n bs, ?_⟩
  rw [At_eq_array_u32 _ n bs hbl (by omega)] at hmem
  exact sep_cast hmem (by ac_rfl)

theorem region_pop_alloc_u64 {w : BitVec 64} {top rem : Nat} {m : Mem 64} {R : Mem 64 → Prop}
    (n : Nat) (hfit : align8 top - top + 8 * n ≤ rem) (hle64 : rem ≤ 2 ^ 64)
    (h : (region (w + BitVec.ofNat 64 top) rem ⋆ R) m) :
    ∃ xs : List (BitVec 64), xs.length = n ∧
      (region (w + BitVec.ofNat 64 top) (align8 top - top) ⋆
       array64 (w + BitVec.ofNat 64 (align8 top)) xs ⋆
       region (w + BitVec.ofNat 64 (align8 top + 8 * n))
         (rem - (align8 top - top + 8 * n)) ⋆ R) m := by
  have hm := region_pop_split (ty := i64) n (by simpa [Ty.bytes, Ty.size] using hfit) hle64 h
  simp only [Ty.bytes, Ty.size, Nat.reduceDiv, Nat.reduceAdd] at hm
  rw [sep_assoc, sep_assoc] at hm
  obtain ⟨bs, hbl, hmem⟩ := region_sep_elim hm
  refine ⟨decodeU64 n bs, decodeU64_length n bs, ?_⟩
  rw [At_eq_array64 _ n bs hbl (by omega)] at hmem
  exact sep_cast hmem (by ac_rfl)

end

end LeanQbe.T.Examples.Arisca.Proof
