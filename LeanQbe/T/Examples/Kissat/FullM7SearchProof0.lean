module

public import LeanQbe.T.Examples.Kissat.FullM7Search
public import LeanQbe.T.Examples.Kissat.FullSpec3
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat M7 Search Parity `Func.wp` Proofs — Part 0 (`FullM7SearchProof0`)

M1-clean proof foundation (`public section`, zero `@[expose]`, zero `import all`, UNSAT-only):
1. Scoped `M7SearchTactics` + BV/arith helper lemmas (`m7_steps`, `m7_to_group`, `m7_split`).
2. Pure state models (`m7LcgNextVal`, `m7Get64Val`, `m7Set64List`, `m7StateInitGu`, `m7EmaSwapSc`)
   with roundtrip EMA preservation (`m7EmaSwapSc_roundtrip`) & `glue_used[0..35]` framing
   (`M7GuPrefixPres`).
3. Arena literal-permutation / watched-prefix preservation (`swapLits_preserves_sparseInvW`,
   `setSrch_preserves_sparseInvW`), chronological decision invariant
   (`m7_decide_preserves_fullCore`), and level-0 UNSAT witness helper.
4. All `15` `FullM7Search` `Spec` contracts + `_of` / `_elim` / `_monoX` bridges + drop-in adapters
   to `Full.fullLuckySpec`, `Full.fullDecideSpec`, and `Full.fullSwitchModeSpec`.
5. Group-A parametric `(Γ : Env)` `Func.wp` proofs (`full_lcg_next_m7`, `full_m7_get64`,
   `full_m7_set64`, `full_m7_state_init`, `full_log10_q16_m7`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM7Search

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open Kraken.Bedrock2.Test

/-- Parameterized environment assumption shorthand for callee `Spec` contracts. -/
abbrev EnvSpec (Γ : Env) (nm : String) {as rs : List Ty} (sp : Spec as rs) : Prop :=
  ∀ a m Q X, sp a m Q X → Γ nm as rs a m Q X

/-! ## 1. Scoped Tactics & BitVector Arithmetic Helpers (`M7SearchTactics`) -/

namespace M7SearchTactics

theorem strip_le_32_64 {P : Prop} (h : P) : 32 ≤ 64 ∧ P := ⟨by decide, h⟩
theorem strip_le_8_32 {P : Prop} (h : P) : 8 ≤ 32 ∧ P := ⟨by decide, h⟩
theorem strip_le_8_64 {P : Prop} (h : P) : 8 ≤ 64 ∧ P := ⟨by decide, h⟩

scoped macro "m7_strip" : tactic =>
  `(tactic| first | apply strip_le_32_64 | apply strip_le_8_32 | apply strip_le_8_64)
scoped macro "m7_unmdata" : tactic =>
  `(tactic| first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)
scoped macro "m7_steps" : tactic =>
  `(tactic| (
      (try m7_unmdata)
      (repeat m7_strip)
      c0_steps
      repeat (any_goals (m7_strip; repeat m7_strip); c0_steps)))

open Lean Elab Tactic in
/-- Step straight-line ops and branches like `c0_steps`, stopping at `Expr.group`. -/
scoped elab "m7_to_group_core" : tactic => do
  for _ in [:500] do
    let mut progressed := false
    let mut out : Array MVarId := #[]
    for g in ← getUnsolvedGoals do
      if ← g.isAssigned then continue
      setGoals [g]
      evalTactic (← `(tactic| all_goals (repeat m7_strip)))
      for g' in ← getUnsolvedGoals do
        if ← g'.isAssigned then continue
        setGoals [g']
        let ty := (← Lean.instantiateMVars (← g'.getType)).consumeMData
        if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
            ((ty.getArg! 4).headBeta.consumeMData).isAppOf ``LeanQbe.T.Expr.group then
          out := out.push g'
        else if ← LeanQbe.T.C0Step.stepOnce then
          progressed := true
          evalTactic (← `(tactic| all_goals (repeat m7_strip)))
          out := out ++ (← getUnsolvedGoals)
        else
          out := out.push g'
    setGoals out.toList
    if !progressed then break

scoped macro "m7_to_group" : tactic =>
  `(tactic| (
      (try m7_unmdata)
      (repeat m7_strip)
      m7_to_group_core
      repeat (any_goals (m7_strip; repeat m7_strip); m7_to_group_core)))

scoped macro "m7_split" : tactic => `(tactic| c0_hsplit)
scoped macro "m7_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

theorem bv64_add_toNat {a b : BitVec 64} (h : a.toNat + b.toNat < 2 ^ 64) :
    (a + b).toNat = a.toNat + b.toNat := by
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt h]

theorem bv64_add1_toNat {g : BitVec 64} (h : g.toNat + 1 < 2 ^ 64) :
    (g + 1#64).toNat = g.toNat + 1 := bv64_add_toNat h

theorem bv64_shl1_toNat {v : BitVec 64} (h : 2 * v.toNat < 2 ^ 64) :
    (v <<< 1#64).toNat = 2 * v.toNat := by
  have hsh : v <<< 1#64 = v <<< (1#64).toNat := rfl
  rw [hsh, BitVec.toNat_shiftLeft, show (1#64).toNat = 1 by decide, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (by omega)]
  omega

theorem bv64_sub1_toNat {f : BitVec 64} (hf : f ≠ 0#64) : (f - 1#64).toNat = f.toNat - 1 := by
  have hpos : 0 < f.toNat := Nat.pos_of_ne_zero fun h0 =>
    hf (BitVec.eq_of_toNat_eq (by simpa using h0))
  bv_omega

theorem bv64_ofNat_toNat {n : Nat} (hn : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

theorem bv32_ofNat_toNat {n : Nat} (hn : n < 2 ^ 32) : (BitVec.ofNat 32 n).toNat = n := by
  simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

theorem bv32_xor1_div2 (x : BitVec 32) : (x ^^^ 1#32).toNat / 2 = x.toNat / 2 := by
  have hsr : (x ^^^ 1#32) >>> 1 = x >>> 1 := by
    ext i hi
    simp [BitVec.getLsbD_xor, show (1#32).getLsbD (1 + i) = false by
      simp [BitVec.getLsbD_one]]
  have h1 : ((x ^^^ 1#32) >>> 1).toNat = (x ^^^ 1#32).toNat / 2 := by
    simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have h2 : (x >>> 1).toNat = x.toNat / 2 := by
    simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  rw [← h1, ← h2, hsr]

theorem zext_toNat {w1 w2 : Nat} (x : BitVec w1) (hle : w1 ≤ w2) :
    (x.setWidth w2).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right
    (by omega) hle))]

theorem bv64_trunc32_ofNat {n : Nat} (hn : n < 2 ^ 32) :
    (BitVec.ofNat 64 n).setWidth 32 = BitVec.ofNat 32 n := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, bv64_ofNat_toNat (by omega), bv32_ofNat_toNat hn,
    Nat.mod_eq_of_lt hn]

private theorem nat_two_mul_or_one (k : Nat) : (2 * k) ||| 1 = 2 * k + 1 := by
  apply Nat.eq_of_testBit_eq
  intro i
  cases i with
  | zero => simp [Nat.testBit_zero]
  | succ j =>
    rw [Nat.testBit_or]
    simp only [Nat.testBit_succ]
    have h10 : Nat.testBit (1 / 2) j = false := by simp
    have hd1 : (2 * k) / 2 = k := by omega
    have hd2 : (2 * k + 1) / 2 = k := by omega
    rw [h10, hd1, hd2, Bool.or_false]

theorem bv32_lit_even {x : BitVec 64} (hx : x.toNat < 2 ^ 30) :
    ((x <<< 1#64).setWidth 32).toNat = 2 * x.toNat := by
  rw [BitVec.toNat_setWidth, bv64_shl1_toNat (by omega), Nat.mod_eq_of_lt (by omega)]

theorem bv32_lit_odd {x : BitVec 64} (hx : x.toNat < 2 ^ 30) :
    (((x <<< 1#64).setWidth 32 ||| 1#32)).toNat = 2 * x.toNat + 1 := by
  rw [BitVec.toNat_or, bv32_lit_even hx, show (1#32 : BitVec 32).toNat = 1 by decide]
  exact nat_two_mul_or_one x.toNat

end M7SearchTactics

open M7SearchTactics
open scoped M7SearchTactics

/-! ## 2. Pure Models, EMA Preservation & `glue_used[0..35]` Non-Interference -/

/-- One upstream Knuth 64-bit LCG step returning `(new_rng_state, upper_32_bits)`. -/
def m7LcgNextVal (x : BitVec 64) : BitVec 64 × BitVec 64 :=
  (x * m7LcgMul + m7LcgInc, (x * m7LcgMul + m7LcgInc) >>> 32)

/-- Reads two consecutive `u32` words in `gu` as a little-endian `u64`. -/
def m7Get64Val (gu : List (BitVec 32)) (idx : Nat) : BitVec 64 :=
  (gu[idx]?.getD 0#32).setWidth 64 ||| ((gu[idx + 1]?.getD 0#32).setWidth 64 <<< 32)

/-- Writes a `u64` into two consecutive `u32` words in `gu` (`lo`, then `hi`). -/
def m7Set64List (gu : List (BitVec 32)) (idx : Nat) (val : BitVec 64) : List (BitVec 32) :=
  (gu.set idx (val.setWidth 32)).set (idx + 1) ((val >>> 32).setWidth 32)

theorem m7Set64List_length (gu : List (BitVec 32)) (idx : Nat) (val : BitVec 64) :
    (m7Set64List gu idx val).length = gu.length := by
  simp [m7Set64List]

theorem m7Set64List_get_lt (gu : List (BitVec 32)) {idx : Nat} (val : BitVec 64)
    {k : Nat} (hk : k < idx) : (m7Set64List gu idx val)[k]? = gu[k]? := by
  unfold m7Set64List
  rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]

theorem m7Set64List_get_ge (gu : List (BitVec 32)) {idx : Nat} (val : BitVec 64)
    {k : Nat} (hk : idx + 2 ≤ k) : (m7Set64List gu idx val)[k]? = gu[k]? := by
  unfold m7Set64List
  rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]

theorem m7Get64Val_set64_self {gu : List (BitVec 32)} {idx : Nat} (val : BitVec 64)
    (hi : idx + 1 < gu.length) : m7Get64Val (m7Set64List gu idx val) idx = val := by
  unfold m7Get64Val m7Set64List
  have hlen : (gu.set idx (val.setWidth 32)).length = gu.length := List.length_set
  rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega),
    List.getElem?_set_self (by rw [hlen]; exact hi)]
  simp only [Option.getD_some]
  apply BitVec.eq_of_getElem_eq; intro k hk
  simp only [BitVec.getElem_or, BitVec.getElem_shiftLeft, BitVec.getElem_setWidth]
  by_cases h32 : k < 32
  · simp [h32]; rfl
  · have hlo : k - 32 < 32 := by omega
    have hk' : 32 + (k - 32) = k := by omega
    simp [h32, hlo, hk']; rfl

theorem m7Get64Val_set64_ne {gu : List (BitVec 32)} {idx j : Nat} (val : BitVec 64)
    (hdisj : j + 2 ≤ idx ∨ idx + 2 ≤ j) :
    m7Get64Val (m7Set64List gu idx val) j = m7Get64Val gu j := by
  unfold m7Get64Val
  rcases hdisj with hlt | hgt
  · rw [m7Set64List_get_lt gu val (by omega), m7Set64List_get_lt gu val (by omega)]
  · rw [m7Set64List_get_ge gu val (by omega), m7Set64List_get_ge gu val (by omega)]

/-- Non-interference with standard LBD glue histogram slots `gu[0..35]`. -/
def M7GuPrefixPres (s s' : FullState) : Prop :=
  ∀ k < 36, s'.scratch.glue_used[k]? = s.scratch.glue_used[k]?

theorem M7GuPrefixPres.refl (s : FullState) : M7GuPrefixPres s s := fun _ _ => rfl

theorem M7GuPrefixPres.trans {s1 s2 s3 : FullState}
    (h12 : M7GuPrefixPres s1 s2) (h23 : M7GuPrefixPres s2 s3) : M7GuPrefixPres s1 s3 :=
  fun k hk => (h23 k hk).trans (h12 k hk)

theorem M7GuPrefixPres.of_set64 {s : FullState} {idx : Nat} (val : BitVec 64)
    (hge : 36 ≤ idx) :
    M7GuPrefixPres s { s with scratch := { s.scratch with
      glue_used := m7Set64List s.scratch.glue_used idx val } } :=
  fun _ hk => m7Set64List_get_lt _ val (by omega)

/-- M7 search state initialization predicate in `gu[36..37]`. -/
def M7StateInitOk (gu : List (BitVec 32)) : Prop :=
  gu.length = 64 ∧ m7Get64Val gu m7GuMagicIdx = m7SearchMagic

theorem M7StateInitOk.len {gu : List (BitVec 32)} (h : M7StateInitOk gu) : gu.length = 64 := h.1
theorem M7StateInitOk.magic {gu : List (BitVec 32)} (h : M7StateInitOk gu) :
    m7Get64Val gu m7GuMagicIdx = m7SearchMagic := h.2

/-- Pure specification of `full_m7_state_init(h)` updating `gu[36..63]`. -/
def m7StateInitGu (sc : FullScratch) : List (BitVec 32) :=
  let gu := sc.glue_used
  if m7Get64Val gu m7GuMagicIdx = m7SearchMagic then gu
  else
    let cm : Nat := if sc.stable ≠ 0#64 then 1 else 0
    let g0 := m7Set64List gu m7GuMagicIdx m7SearchMagic
    let g1 := m7Set64List g0 m7GuEmaMaskIdx (1#64 <<< cm)
    let g2 := if cm = 0 then
      m7Set64List (m7Set64List (m7Set64List (m7Set64List (m7Set64List (m7Set64List
        (m7Set64List (m7Set64List g1 m7GuEma0FbIdx sc.ema_fast_biased)
          m7GuEma0FeIdx sc.ema_fast_exp)
          m7GuEma0SbIdx sc.ema_slow_biased)
          m7GuEma0SeIdx sc.ema_slow_exp)
          m7GuEma1FbIdx 0#64) m7GuEma1FeIdx m7EmaInitExp)
          m7GuEma1SbIdx 0#64) m7GuEma1SeIdx m7EmaInitExp
    else
      m7Set64List (m7Set64List (m7Set64List (m7Set64List (m7Set64List (m7Set64List
        (m7Set64List (m7Set64List g1 m7GuEma1FbIdx sc.ema_fast_biased)
          m7GuEma1FeIdx sc.ema_fast_exp)
          m7GuEma1SbIdx sc.ema_slow_biased)
          m7GuEma1SeIdx sc.ema_slow_exp)
          m7GuEma0FbIdx 0#64) m7GuEma0FeIdx m7EmaInitExp)
          m7GuEma0SbIdx 0#64) m7GuEma0SeIdx m7EmaInitExp
    m7Set64List (m7Set64List (m7Set64List (m7Set64List g2
      m7GuRandecRemIdx 0#64) m7GuRandecLimIdx (sc.conflicts + BitVec.ofNat 64 m7RandecInitLim))
      m7GuRandecSeqIdx 0#64) m7GuRandecConflIdx sc.conflicts

theorem m7StateInitGu_of_magic {sc : FullScratch}
    (hm : m7Get64Val sc.glue_used m7GuMagicIdx = m7SearchMagic) :
    m7StateInitGu sc = sc.glue_used := by
  unfold m7StateInitGu; dsimp only; simp [hm]

theorem m7StateInitGu_length (sc : FullScratch) :
    (m7StateInitGu sc).length = sc.glue_used.length := by
  unfold m7StateInitGu; dsimp only
  by_cases hm : m7Get64Val sc.glue_used m7GuMagicIdx = m7SearchMagic
  · simp [hm]
  · simp only [hm, ↓reduceIte]; split <;> simp [m7Set64List_length]

theorem m7StateInitGu_prefix (sc : FullScratch) {k : Nat} (hk : k < 36) :
    (m7StateInitGu sc)[k]? = sc.glue_used[k]? := by
  unfold m7StateInitGu; dsimp only
  by_cases hm : m7Get64Val sc.glue_used m7GuMagicIdx = m7SearchMagic
  · simp [hm]
  · simp only [hm, ↓reduceIte]
    unfold m7GuMagicIdx m7GuEmaMaskIdx m7GuEma0FbIdx m7GuEma0FeIdx m7GuEma0SbIdx m7GuEma0SeIdx
      m7GuEma1FbIdx m7GuEma1FeIdx m7GuEma1SbIdx m7GuEma1SeIdx m7GuRandecRemIdx m7GuRandecLimIdx
      m7GuRandecSeqIdx m7GuRandecConflIdx
    have hite1 : ((1 : Nat) = 0) ↔ False := by decide
    by_cases hst : sc.stable = 0#64
    · simp only [hst, ne_eq, not_true_eq_false, ↓reduceIte]
      repeat (rw [m7Set64List_get_lt]; case hk => omega)
      try rfl
    · simp only [hst, ne_eq, not_false_eq_true, ↓reduceIte, hite1]
      repeat (rw [m7Set64List_get_lt]; case hk => omega)
      try rfl

theorem m7StateInitGu_initOk {sc : FullScratch} (hlen : sc.glue_used.length = 64) :
    M7StateInitOk (m7StateInitGu sc) := by
  refine ⟨by rw [m7StateInitGu_length, hlen], ?_⟩
  unfold m7StateInitGu; dsimp only
  by_cases hm : m7Get64Val sc.glue_used m7GuMagicIdx = m7SearchMagic
  · simp [hm]
  · simp only [hm, ↓reduceIte]
    unfold m7GuMagicIdx m7GuEmaMaskIdx m7GuEma0FbIdx m7GuEma0FeIdx m7GuEma0SbIdx m7GuEma0SeIdx
      m7GuEma1FbIdx m7GuEma1FeIdx m7GuEma1SbIdx m7GuEma1SeIdx m7GuRandecRemIdx m7GuRandecLimIdx
      m7GuRandecSeqIdx m7GuRandecConflIdx
    have hite1 : ((1 : Nat) = 0) ↔ False := by decide
    by_cases hst : sc.stable = 0#64
    · simp only [hst, ne_eq, not_true_eq_false, ↓reduceIte]
      iterate 13 (rw [m7Get64Val_set64_ne]; case hdisj => exact Or.inl (by decide))
      exact m7Get64Val_set64_self _ (by omega)
    · simp only [hst, ne_eq, not_false_eq_true, ↓reduceIte, hite1]
      iterate 13 (rw [m7Get64Val_set64_ne]; case hdisj => exact Or.inl (by decide))
      exact m7Get64Val_set64_self _ (by omega)

/-- Reads the `4`-tuple `(fast_biased, fast_exp, slow_biased, slow_exp)` saved for mode `m`
(`0` = focused, `1` = stable). -/
def m7ModeEmaGet (gu : List (BitVec 32)) (mode : Nat) :
    BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 :=
  let base := if mode = 0 then m7GuEma0FbIdx else m7GuEma1FbIdx
  (m7Get64Val gu base, m7Get64Val gu (base + 2), m7Get64Val gu (base + 4),
   m7Get64Val gu (base + 6))

/-- Writes a `4`-tuple of Q32 EMAs into mode `mode` slots inside `gu`. -/
def m7ModeEmaSet (gu : List (BitVec 32)) (mode : Nat)
    (v : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64) : List (BitVec 32) :=
  let base := if mode = 0 then m7GuEma0FbIdx else m7GuEma1FbIdx
  m7Set64List (m7Set64List (m7Set64List (m7Set64List gu base v.1) (base + 2) v.2.1)
    (base + 4) v.2.2.1) (base + 6) v.2.2.2

theorem m7ModeEmaSet_length (gu : List (BitVec 32)) (mode : Nat)
    (v : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64) :
    (m7ModeEmaSet gu mode v).length = gu.length := by
  unfold m7ModeEmaSet; simp [m7Set64List_length]

theorem m7ModeEmaSet_get_lt (gu : List (BitVec 32)) (mode : Nat)
    (v : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64) {k : Nat} (hk : k < 40) :
    (m7ModeEmaSet gu mode v)[k]? = gu[k]? := by
  unfold m7ModeEmaSet m7GuEma0FbIdx m7GuEma1FbIdx
  split <;>
    (rw [m7Set64List_get_lt _ _ (by omega), m7Set64List_get_lt _ _ (by omega),
       m7Set64List_get_lt _ _ (by omega), m7Set64List_get_lt _ _ (by omega)])

private theorem m7ModeEmaGet_set_self_base (gu : List (BitVec 32)) (base : Nat)
    (v : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64) (hb : base + 7 < gu.length) :
    let gu' := m7Set64List (m7Set64List (m7Set64List (m7Set64List gu base v.1)
      (base + 2) v.2.1) (base + 4) v.2.2.1) (base + 6) v.2.2.2
    (m7Get64Val gu' base, m7Get64Val gu' (base + 2), m7Get64Val gu' (base + 4),
     m7Get64Val gu' (base + 6)) = v := by
  intro gu'
  have hl1 : (m7Set64List gu base v.1).length = gu.length := m7Set64List_length _ _ _
  have hl2 : (m7Set64List (m7Set64List gu base v.1) (base + 2) v.2.1).length = gu.length := by
    simp [m7Set64List_length, hl1]
  have hl3 : (m7Set64List (m7Set64List (m7Set64List gu base v.1) (base + 2) v.2.1)
      (base + 4) v.2.2.1).length = gu.length := by
    simp [m7Set64List_length, hl2]
  have e0 : m7Get64Val gu' base = v.1 := by
    dsimp only [gu']
    rw [m7Get64Val_set64_ne _ (Or.inl (by omega)), m7Get64Val_set64_ne _ (Or.inl (by omega)),
      m7Get64Val_set64_ne _ (Or.inl (by omega)), m7Get64Val_set64_self _ (by omega)]
  have e1 : m7Get64Val gu' (base + 2) = v.2.1 := by
    dsimp only [gu']
    rw [m7Get64Val_set64_ne _ (Or.inl (by omega)), m7Get64Val_set64_ne _ (Or.inl (by omega)),
      m7Get64Val_set64_self _ (by omega)]
  have e2 : m7Get64Val gu' (base + 4) = v.2.2.1 := by
    dsimp only [gu']
    rw [m7Get64Val_set64_ne _ (Or.inl (by omega)), m7Get64Val_set64_self _ (by omega)]
  have e3 : m7Get64Val gu' (base + 6) = v.2.2.2 := by
    dsimp only [gu']
    rw [m7Get64Val_set64_self _ (by omega)]
  rw [e0, e1, e2, e3]

theorem m7ModeEmaGet_set_self {gu : List (BitVec 32)} {mode : Nat}
    (v : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64) (hlen : gu.length = 64) :
    m7ModeEmaGet (m7ModeEmaSet gu mode v) mode = v := by
  unfold m7ModeEmaGet m7ModeEmaSet m7GuEma0FbIdx m7GuEma1FbIdx
  split
  · exact m7ModeEmaGet_set_self_base gu 40 v (by omega)
  · exact m7ModeEmaGet_set_self_base gu 48 v (by omega)

theorem m7ModeEmaGet_set_other {gu : List (BitVec 32)} {m1 m2 : Nat}
    (v : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64) (hne : (m1 = 0) ≠ (m2 = 0)) :
    m7ModeEmaGet (m7ModeEmaSet gu m1 v) m2 = m7ModeEmaGet gu m2 := by
  unfold m7ModeEmaGet m7ModeEmaSet m7GuEma0FbIdx m7GuEma1FbIdx
  by_cases h1 : m1 = 0 <;> by_cases h2 : m2 = 0
  · exact absurd (by simp [h1, h2]) hne
  · simp only [h1, h2, ↓reduceIte]
    have hn : ∀ (g : List (BitVec 32)) (i j : Nat) (w : BitVec 64),
        40 ≤ i → i ≤ 46 → 48 ≤ j → m7Get64Val (m7Set64List g i w) j = m7Get64Val g j :=
      fun g i j w _ hi hj => m7Get64Val_set64_ne w (Or.inr (by omega))
    rw [hn _ _ _ _ (by decide) (by decide) (by decide),
      hn _ _ _ _ (by decide) (by decide) (by decide),
      hn _ _ _ _ (by decide) (by decide) (by decide),
      hn _ _ _ _ (by decide) (by decide) (by decide),
      hn _ _ _ _ (by decide) (by decide) (by decide),
      hn _ _ _ _ (by decide) (by decide) (by decide),
      hn _ _ _ _ (by decide) (by decide) (by decide),
      hn _ _ _ _ (by decide) (by decide) (by decide),
      hn _ _ _ _ (by decide) (by decide) (by decide),
      hn _ _ _ _ (by decide) (by decide) (by decide),
      hn _ _ _ _ (by decide) (by decide) (by decide),
      hn _ _ _ _ (by decide) (by decide) (by decide),
      hn _ _ _ _ (by decide) (by decide) (by decide),
      hn _ _ _ _ (by decide) (by decide) (by decide),
      hn _ _ _ _ (by decide) (by decide) (by decide),
      hn _ _ _ _ (by decide) (by decide) (by decide)]
  · simp only [h1, h2, ↓reduceIte]
    have hn : ∀ (g : List (BitVec 32)) (i j : Nat) (w : BitVec 64),
        48 ≤ i → j ≤ 46 → m7Get64Val (m7Set64List g i w) j = m7Get64Val g j :=
      fun g i j w hi hj => m7Get64Val_set64_ne w (Or.inl (by omega))
    rw [hn _ _ _ _ (by decide) (by decide), hn _ _ _ _ (by decide) (by decide),
      hn _ _ _ _ (by decide) (by decide), hn _ _ _ _ (by decide) (by decide),
      hn _ _ _ _ (by decide) (by decide), hn _ _ _ _ (by decide) (by decide),
      hn _ _ _ _ (by decide) (by decide), hn _ _ _ _ (by decide) (by decide),
      hn _ _ _ _ (by decide) (by decide), hn _ _ _ _ (by decide) (by decide),
      hn _ _ _ _ (by decide) (by decide), hn _ _ _ _ (by decide) (by decide),
      hn _ _ _ _ (by decide) (by decide), hn _ _ _ _ (by decide) (by decide),
      hn _ _ _ _ (by decide) (by decide), hn _ _ _ _ (by decide) (by decide)]
  · exact absurd (by simp [h1, h2]) hne

private def m7FlagNat (x : BitVec 64) : Nat := if x ≠ 0#64 then 1 else 0

/-- Pure functional model of `full_ema_swap_m7(h, old_m, new_m)`. -/
def m7EmaSwapSc (sc : FullScratch) (old_m new_m : BitVec 64) : FullScratch :=
  let om : Nat := m7FlagNat old_m
  let nm : Nat := m7FlagNat new_m
  let gu0 := m7StateInitGu { sc with stable := BitVec.ofNat 64 om }
  let curV := (sc.ema_fast_biased, sc.ema_fast_exp, sc.ema_slow_biased, sc.ema_slow_exp)
  let gu1 := m7ModeEmaSet gu0 om curV
  let mask := m7Get64Val gu1 m7GuEmaMaskIdx ||| (1#64 <<< om)
  let bit := 1#64 <<< nm
  if mask &&& bit ≠ 0#64 then
    let nw := m7ModeEmaGet gu1 nm
    let gu2 := m7Set64List gu1 m7GuEmaMaskIdx mask
    { sc with
      stable := BitVec.ofNat 64 nm
      glue_used := gu2
      ema_fast_biased := nw.1
      ema_fast_exp := nw.2.1
      ema_slow_biased := nw.2.2.1
      ema_slow_exp := nw.2.2.2 }
  else
    let initV := (0#64, m7EmaInitExp, 0#64, m7EmaInitExp)
    let gu2 := m7ModeEmaSet gu1 nm initV
    let gu3 := m7Set64List gu2 m7GuEmaMaskIdx (mask ||| bit)
    { sc with
      stable := BitVec.ofNat 64 nm
      glue_used := gu3
      ema_fast_biased := 0#64
      ema_fast_exp := m7EmaInitExp
      ema_slow_biased := 0#64
      ema_slow_exp := m7EmaInitExp }

theorem m7EmaSwapSc_lengths {c : FullCfg} {sc : FullScratch} (hok : sc.LengthsOk c)
    (old_m new_m : BitVec 64) : (m7EmaSwapSc sc old_m new_m).LengthsOk c := by
  unfold m7EmaSwapSc; dsimp only; split <;> exact {
    hok with
    glue_used_len := by
      simp [m7Set64List_length, m7ModeEmaSet_length, m7StateInitGu_length, hok.glue_used_len] }

theorem m7EmaSwapSc_prefix (sc : FullScratch) (old_m new_m : BitVec 64) {k : Nat} (hk : k < 36) :
    (m7EmaSwapSc sc old_m new_m).glue_used[k]? = sc.glue_used[k]? := by
  unfold m7EmaSwapSc; dsimp only; split
  · rw [m7Set64List_get_lt]; case hk => unfold m7GuEmaMaskIdx; omega
    rw [m7ModeEmaSet_get_lt]; case hk => omega
    exact m7StateInitGu_prefix _ hk
  · rw [m7Set64List_get_lt]; case hk => unfold m7GuEmaMaskIdx; omega
    rw [m7ModeEmaSet_get_lt]; case hk => omega
    rw [m7ModeEmaSet_get_lt]; case hk => omega
    exact m7StateInitGu_prefix _ hk

theorem m7EmaSwapSc_initOk {sc : FullScratch} (hlen : sc.glue_used.length = 64)
    (old_m new_m : BitVec 64) : M7StateInitOk (m7EmaSwapSc sc old_m new_m).glue_used := by
  unfold m7EmaSwapSc; dsimp only
  have hi := m7StateInitGu_initOk (sc := { sc with stable := BitVec.ofNat 64 (m7FlagNat old_m) })
    hlen
  have hlen0 : (m7StateInitGu { sc with stable := BitVec.ofNat 64 (m7FlagNat old_m) }).length =
      64 := hi.len
  have hne_mask : ∀ (g : List (BitVec 32)) (w : BitVec 64),
      m7Get64Val (m7Set64List g m7GuEmaMaskIdx w) m7GuMagicIdx = m7Get64Val g m7GuMagicIdx :=
    fun g w => m7Get64Val_set64_ne w (Or.inl (by decide))
  have hne_ema : ∀ (g : List (BitVec 32)) (md : Nat) (v : BitVec 64 × _ × _ × _),
      m7Get64Val (m7ModeEmaSet g md v) m7GuMagicIdx = m7Get64Val g m7GuMagicIdx := by
    intro g md v; unfold m7ModeEmaSet m7GuEma0FbIdx m7GuEma1FbIdx m7GuMagicIdx
    split <;>
      · iterate 4 (rw [m7Get64Val_set64_ne]; case hdisj => exact Or.inl (by omega))
        try rfl
  split
  · refine ⟨by simp [m7Set64List_length, m7ModeEmaSet_length, hlen0], ?_⟩
    rw [hne_mask, hne_ema]; exact hi.magic
  · refine ⟨by simp [m7Set64List_length, m7ModeEmaSet_length, hlen0], ?_⟩
    rw [hne_mask, hne_ema, hne_ema]; exact hi.magic

theorem m7EmaSwapSc_roundtrip {sc : FullScratch} (hlen : sc.glue_used.length = 64)
    (fb fe sb se : BitVec 64) :
    let sc0 := {
      sc with
      ema_fast_biased := fb
      ema_fast_exp := fe
      ema_slow_biased := sb
      ema_slow_exp := se }
    let sc1 := m7EmaSwapSc sc0 0#64 1#64
    let sc2 := m7EmaSwapSc sc1 1#64 0#64
    sc2.ema_fast_biased = fb ∧ sc2.ema_fast_exp = fe ∧
    sc2.ema_slow_biased = sb ∧ sc2.ema_slow_exp = se := by
  intro sc0 sc1 sc2
  have h1_init : m7Get64Val sc1.glue_used m7GuMagicIdx = m7SearchMagic :=
    (m7EmaSwapSc_initOk (sc := sc0) hlen 0#64 1#64).magic
  have hfn0 : m7FlagNat 0#64 = 0 := by decide
  have hfn1 : m7FlagNat 1#64 = 1 := by decide
  have hne_mask : ∀ (g : List (BitVec 32)) (w : BitVec 64) (j : Nat),
      40 ≤ j → m7Get64Val (m7Set64List g m7GuEmaMaskIdx w) j = m7Get64Val g j :=
    fun g w j hj => m7Get64Val_set64_ne w (Or.inr (by unfold m7GuEmaMaskIdx; omega))
  have h_saved0 : m7ModeEmaGet sc1.glue_used 0 = (fb, fe, sb, se) := by
    dsimp only [sc1, m7EmaSwapSc]
    rw [hfn0, hfn1]
    have hl0 : (m7StateInitGu { sc0 with stable := BitVec.ofNat 64 0 }).length = 64 := by
      rw [m7StateInitGu_length, hlen]
    let gInit := m7StateInitGu { sc0 with stable := BitVec.ofNat 64 0 }
    let gE0 := m7ModeEmaSet gInit 0 (fb, fe, sb, se)
    split
    · unfold m7ModeEmaGet
      simp only [↓reduceIte]
      rw [hne_mask _ _ _ (by unfold m7GuEma0FbIdx; decide),
        hne_mask _ _ _ (by unfold m7GuEma0FbIdx; decide),
        hne_mask _ _ _ (by unfold m7GuEma0FbIdx; decide),
        hne_mask _ _ _ (by unfold m7GuEma0FbIdx; decide)]
      exact m7ModeEmaGet_set_self (gu := gInit) (mode := 0) (fb, fe, sb, se) hl0
    · unfold m7ModeEmaGet
      simp only [↓reduceIte]
      rw [hne_mask _ _ _ (by unfold m7GuEma0FbIdx; decide),
        hne_mask _ _ _ (by unfold m7GuEma0FbIdx; decide),
        hne_mask _ _ _ (by unfold m7GuEma0FbIdx; decide),
        hne_mask _ _ _ (by unfold m7GuEma0FbIdx; decide)]
      change m7ModeEmaGet (m7ModeEmaSet gE0 1 (0#64, m7EmaInitExp, 0#64, m7EmaInitExp)) 0 = _
      rw [m7ModeEmaGet_set_other (gu := gE0) (m1 := 1) (m2 := 0) _ (by decide),
        m7ModeEmaGet_set_self (gu := gInit) (mode := 0) (fb, fe, sb, se) hl0]
  have h_mask0 : (m7Get64Val sc1.glue_used m7GuEmaMaskIdx &&& 1#64) ≠ 0#64 := by
    dsimp only [sc1, m7EmaSwapSc]
    rw [hfn0, hfn1]
    have hl0 : (m7StateInitGu { sc0 with stable := BitVec.ofNat 64 0 }).length = 64 := by
      rw [m7StateInitGu_length, hlen]
    split
    · rw [m7Get64Val_set64_self _ (by simp [m7ModeEmaSet_length, hl0, m7GuEmaMaskIdx])]
      intro hc
      have hlsb : ((m7Get64Val (m7ModeEmaSet
          (m7StateInitGu { sc0 with stable := BitVec.ofNat 64 0 }) 0 (fb, fe, sb, se))
          m7GuEmaMaskIdx ||| 1#64 <<< 0) &&& 1#64).getLsbD 0 = true := by
        rw [BitVec.getLsbD_and, BitVec.getLsbD_or,
          show (1#64 <<< 0 : BitVec 64).getLsbD 0 = true by decide,
          show (1#64 : BitVec 64).getLsbD 0 = true by decide, Bool.or_true, Bool.true_and]
      rw [hc] at hlsb; exact absurd hlsb (by decide)
    · rw [m7Get64Val_set64_self _ (by simp [m7ModeEmaSet_length, hl0, m7GuEmaMaskIdx])]
      intro hc
      have hlsb : (((m7Get64Val (m7ModeEmaSet
          (m7StateInitGu { sc0 with stable := BitVec.ofNat 64 0 }) 0 (fb, fe, sb, se))
          m7GuEmaMaskIdx ||| 1#64 <<< 0) ||| (1#64 <<< 1)) &&& 1#64).getLsbD 0 = true := by
        rw [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_or,
          show (1#64 <<< 0 : BitVec 64).getLsbD 0 = true by decide,
          show (1#64 : BitVec 64).getLsbD 0 = true by decide, Bool.or_true, Bool.true_or,
          Bool.true_and]
      rw [hc] at hlsb; exact absurd hlsb (by decide)
  have h_gu0 : m7StateInitGu { sc1 with stable := BitVec.ofNat 64 1 } = sc1.glue_used :=
    m7StateInitGu_of_magic (by simpa using h1_init)
  have h_cond : (m7Get64Val (m7ModeEmaSet sc1.glue_used 1
      (sc1.ema_fast_biased, sc1.ema_fast_exp, sc1.ema_slow_biased, sc1.ema_slow_exp))
      m7GuEmaMaskIdx ||| 1#64 <<< 1) &&& (1#64 <<< 0) ≠ 0#64 := by
    have hme : m7Get64Val (m7ModeEmaSet sc1.glue_used 1
        (sc1.ema_fast_biased, sc1.ema_fast_exp, sc1.ema_slow_biased, sc1.ema_slow_exp))
        m7GuEmaMaskIdx = m7Get64Val sc1.glue_used m7GuEmaMaskIdx := by
      unfold m7ModeEmaSet m7GuEmaMaskIdx
      rw [show (if (1 : Nat) = 0 then m7GuEma0FbIdx else m7GuEma1FbIdx) = 48 by
        unfold m7GuEma1FbIdx; decide]
      rw [m7Get64Val_set64_ne _ (Or.inl (by decide)), m7Get64Val_set64_ne _ (Or.inl (by decide)),
        m7Get64Val_set64_ne _ (Or.inl (by decide)), m7Get64Val_set64_ne _ (Or.inl (by decide))]
    rw [hme]
    intro hc
    have hlsb := congrArg (fun x : BitVec 64 => x.getLsbD 0) hc
    have hl0 : (m7Get64Val sc1.glue_used m7GuEmaMaskIdx &&& 1#64).getLsbD 0 = true := by
      by_cases hb : (m7Get64Val sc1.glue_used m7GuEmaMaskIdx).getLsbD 0
      · rw [BitVec.getLsbD_and, hb, show (1#64 : BitVec 64).getLsbD 0 = true by decide,
          Bool.and_true]
      · exfalso; apply h_mask0
        have hb0 : (m7Get64Val sc1.glue_used m7GuEmaMaskIdx).getLsbD 0 = false :=
          Bool.eq_false_iff.mpr hb
        apply BitVec.eq_of_getLsbD_eq; intro k _
        cases k with
        | zero =>
          change (m7Get64Val sc1.glue_used m7GuEmaMaskIdx &&& 1#64).getLsbD 0 =
            (0#64 : BitVec 64).getLsbD 0
          rw [BitVec.getLsbD_and, hb0, Bool.false_and]; simp
        | succ j =>
          change (m7Get64Val sc1.glue_used m7GuEmaMaskIdx &&& 1#64).getLsbD (j + 1) =
            (0#64 : BitVec 64).getLsbD (j + 1)
          rw [BitVec.getLsbD_and, show (1#64 : BitVec 64).getLsbD (j + 1) = false by
            simp [BitVec.getLsbD_one], Bool.and_false]; simp
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or] at hlsb hl0
    simp_all
  have h_rest0 : m7ModeEmaGet (m7ModeEmaSet sc1.glue_used 1
      (sc1.ema_fast_biased, sc1.ema_fast_exp, sc1.ema_slow_biased, sc1.ema_slow_exp)) 0 =
      (fb, fe, sb, se) := by
    rw [m7ModeEmaGet_set_other _ (by decide), h_saved0]
  dsimp only [sc2, m7EmaSwapSc]
  rw [hfn1, hfn0, h_gu0]
  simp only [h_cond, ne_eq, not_false_eq_true, ↓reduceIte, h_rest0]
  exact ⟨trivial, trivial, trivial, trivial⟩

/-! ## 3. Arena Permutation, Decision & UNSAT Witness Helpers -/

theorem fullArenaPermEq_refl (k : FullCoreState) : FullArenaPermEq k k :=
  ⟨rfl, rfl, fun _ _ => ⟨rfl, rfl, List.Perm.refl _⟩⟩

theorem fullArenaPermEq_trans {k1 k2 k3 : FullCoreState}
    (h1 : FullArenaPermEq k1 k2) (h2 : FullArenaPermEq k2 k3) : FullArenaPermEq k1 k3 :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, fun r hr =>
    let ⟨s1, g1, p1⟩ := h1.2.2 r hr
    let ⟨s2, g2, p2⟩ := h2.2.2 r (h1.2.1.symm ▸ hr)
    ⟨s2.trans s1, g2.trans g1, p2.trans p1⟩⟩

private theorem fullInv_arena_cap_lt32 (c : FullCfg) : c.arena_cap < 2 ^ 32 := by
  have h := c.harena; unfold dimacsBound at h; omega

private theorem fullInv_max_vars_lt32 (c : FullCfg) : c.max_vars < 2 ^ 32 := by
  have h := c.hmaxv; unfold dimacsBound at h; omega

theorem fullArenaScanRefs_zero_mem {ar : List (BitVec 32)} {alen : Nat}
    (hlen : alen = 0 ∨ 3 ≤ alen) (hpos : 0 < alen) :
    0 ∈ fullArenaScanRefs ar alen 0 alen := by
  have h3 : 3 ≤ alen := by omega
  cases alen with
  | zero => omega
  | succ n => unfold fullArenaScanRefs; simp [show 0 + 3 ≤ n + 1 by omega]

private theorem fullArenaScanRefs_next_mem {ar : List (BitVec 32)} {alen : Nat} :
    ∀ {fuel pos p : Nat}, alen - pos ≤ fuel → p ∈ fullArenaScanRefs ar alen pos fuel →
      fullArenaNextOff ar alen p + 3 ≤ alen →
      fullArenaNextOff ar alen p ∈ fullArenaScanRefs ar alen pos fuel
  | 0, _, _, _, h, _ => by simp [fullArenaScanRefs] at h
  | fuel + 1, pos, p, hfl, hmem, hnext3 => by
    unfold fullArenaScanRefs at hmem ⊢; split at hmem
    · rename_i hpos3
      simp only [hpos3, ↓reduceIte, List.mem_cons] at hmem ⊢
      have hnb := fullArenaNextOff_bounds (ar := ar) (alen := alen) (cref := pos) hpos3
      rcases hmem with rfl | hrest
      · right; cases fuel with | zero => omega | succ _ => unfold fullArenaScanRefs; simp [hnext3]
      · exact Or.inr (fullArenaScanRefs_next_mem (by omega) hrest hnext3)
    · simp at hmem

theorem fullArenaClauseRefs_next_or_end {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k)
    {p : Nat} (hp : p ∈ fullArenaClauseRefsCore k) :
    let np := fullArenaNextOff k.arena k.arena_len p
    p < np ∧ np ≤ k.arena_len ∧ (np = k.arena_len ∨ np ∈ fullArenaClauseRefsCore k) := by
  have hwf := hw.arena.refs_wf p hp
  have hnb := fullArenaNextOff_bounds (ar := k.arena) (alen := k.arena_len) (cref := p) hwf.1
  exact ⟨hnb.1, hnb.2, hwf.2.2.2.2.imp id (fullArenaScanRefs_next_mem (Nat.le_refl _) hp)⟩

private theorem list_count_set (xs : List Nat) (k v a : Nat) (hk : k < xs.length) :
    (xs.set k v).count a + (if xs[k] = a then 1 else 0) =
      xs.count a + (if v = a then 1 else 0) := by
  induction xs generalizing k with
  | nil => simp at hk
  | cons x xs ih =>
    cases k with
    | zero =>
      simp only [List.set_cons_zero, List.count_cons, List.getElem_cons_zero, beq_iff_eq]
      by_cases hx : x = a <;> by_cases hv : v = a <;> simp [hx, hv] <;> omega
    | succ k =>
      have hk' : k < xs.length := by simpa using hk
      have ihk := ih k hk'
      simp only [List.set_cons_succ, List.count_cons, List.getElem_cons_succ] at *
      omega

private theorem list_swap_perm_nat (xs : List Nat) {k1 k2 : Nat}
    (hk1 : k1 < xs.length) (hk2 : k2 < xs.length) :
    ((xs.set k1 (xs[k2]'hk2)).set k2 (xs[k1]'hk1)).Perm xs := by
  by_cases heq : k1 = k2
  · subst k2; simp [List.set_getElem_self]
  · refine List.perm_iff_count.mpr fun a => ?_
    have hl1 : (xs.set k1 (xs[k2]'hk2)).length = xs.length := List.length_set
    have hget : (xs.set k1 (xs[k2]'hk2))[k2]'(by rw [hl1]; exact hk2) = xs[k2]'hk2 :=
      List.getElem_set_ne heq (by rw [hl1]; exact hk2)
    have c1 := list_count_set xs k1 (xs[k2]'hk2) a hk1
    have c2 := list_count_set (xs.set k1 (xs[k2]'hk2)) k2 (xs[k1]'hk1) a (by rw [hl1]; exact hk2)
    rw [hget] at c2
    omega

private theorem entailsClause_of_perm {F : CNF Nat} {xs ys : List Nat} (hp : xs.Perm ys)
    (h : F.EntailsClause (cnfClause xs)) : F.EntailsClause (cnfClause ys) := by
  rw [CNF.entails_clause_def] at h ⊢
  intro α hα
  rw [clause_sat_cnfClause_iff]
  obtain ⟨l, hl, hs⟩ := (clause_sat_cnfClause_iff α xs).mp (h α hα)
  exact ⟨l, hp.mem_iff.mp hl, hs⟩

private theorem fullArenaClauseLitsCore_eq_of_hold {k1 k2 : FullCoreState} {r : Nat}
    (hbd1 : r + 3 + fullArenaClauseSizeCore k1 r ≤ k1.arena.length)
    (hbd2 : r + 3 + fullArenaClauseSizeCore k2 r ≤ k2.arena.length)
    (hsz : fullArenaClauseSizeCore k1 r = fullArenaClauseSizeCore k2 r)
    (hlit : ∀ j < fullArenaClauseSizeCore k2 r, k1.arena[r + 3 + j]? = k2.arena[r + 3 + j]?) :
    fullArenaClauseLitsCore k1 r = fullArenaClauseLitsCore k2 r := by
  apply List.ext_getElem
  · simp only [fullArenaClauseLitsCore, List.length_map, List.length_take, List.length_drop, hsz]
    omega
  · intro j hj1 hj2
    have hj_sz : j < fullArenaClauseSizeCore k2 r := by
      simp only [fullArenaClauseLitsCore, List.length_map, List.length_take,
        List.length_drop] at hj2; omega
    simp only [fullArenaClauseLitsCore, List.getElem_map, List.getElem_take, List.getElem_drop]
    have he := hlit j hj_sz
    rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at he
    exact congrArg BitVec.toNat (Option.some.inj he)

private theorem swapCl_preserves_sparseInvW {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hsp : FullSparseInvW c F0 F_cur s)
    {cref k1 k2 : Nat} {srch : BitVec 32} (hcref : cref ∈ fullArenaClauseRefsCore s.core)
    (hk1 : k1 < fullArenaClauseSizeCore s.core cref)
    (hk2 : k2 < fullArenaClauseSizeCore s.core cref) :
    have hbd : cref + 3 + fullArenaClauseSizeCore s.core cref ≤ s.core.arena.length := by
      have hwf := hsp.2.1.arena.refs_wf cref hcref; have := hwf.2.2.1; have := hwf.2.2.2.1
      have := hsp.1.core_ok.arena_len_le; have := hsp.1.core_ok.arena_len_arr; omega
    let l1 := s.core.arena[cref + 3 + k1]'(by omega)
    let l2 := s.core.arena[cref + 3 + k2]'(by omega)
    let arena' := ((s.core.arena.set (cref + 1) srch).set (cref + 3 + k1) l2).set (cref + 3 + k2) l1
    let s' : FullState := { s with core := { s.core with arena := arena' } }
    FullSparseInvW c F0 F_cur s' ∧ FullArenaPermEq s.core s'.core := by
  intro hbd l1 l2 arena' s'
  have hlen := hsp.1; have hw := hsp.2.1; have hwf := hw.arena.refs_wf cref hcref
  have har_len' : arena'.length = c.arena_cap := by simp [arena', hlen.core_ok.arena_len_arr]
  have har0 : arena'[cref]? = s.core.arena[cref]? := by
    simp only [arena']; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega)]
  have har2 : arena'[cref + 2]? = s.core.arena[cref + 2]? := by
    simp only [arena']; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega)]
  have har_out : ∀ i, (i < cref ∨ cref + 3 + fullArenaClauseSizeCore s.core cref ≤ i) →
      arena'[i]? = s.core.arena[i]? := fun i hi => by
    simp only [arena']; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega)]
  have hout : ∀ r ∈ fullArenaClauseRefsCore s.core, r ≠ cref →
      (r + 3 + fullArenaClauseSizeCore s.core r ≤ cref ∧
        fullArenaNextOff s.core.arena s.core.arena_len r ≤ cref) ∨
      (cref + 3 + fullArenaClauseSizeCore s.core cref ≤ r) := fun r hr hne => by
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · exact Or.inl ⟨hw.arena.disjoint hr hcref hlt, fullArenaScanRefs_disjoint hr hcref hlt⟩
    · exact Or.inr (hw.arena.disjoint hcref hr hgt)
  have hnxt : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaNextOff arena' s.core.arena_len r =
        fullArenaNextOff s.core.arena s.core.arena_len r := by
    intro r hr; by_cases hrc : r = cref
    · subst hrc; exact fullArenaNextOff_congr_block har0 har2 fun j hj1 _ => har_out j (Or.inr hj1)
    · rcases hout r hr hrc with ⟨h1, h2⟩ | hgt
      · have h3 := (hw.arena.refs_wf r hr).2.1
        exact fullArenaNextOff_congr_block (har_out r (Or.inl (by omega)))
          (har_out (r + 2) (Or.inl (by omega))) fun j _ hj2 => har_out j (Or.inl (by omega))
      · exact fullArenaNextOff_congr_block (har_out r (Or.inr hgt))
          (har_out (r + 2) (Or.inr (by omega))) fun j _ _ => har_out j (Or.inr (by omega))
  have hrefs : fullArenaClauseRefsCore s'.core = fullArenaClauseRefsCore s.core :=
    fullArenaClauseRefsCore_congr (k1 := s.core) (k2 := s'.core) rfl fun r hr => hnxt r hr
  have hsz_eq : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaClauseSizeCore s'.core r = fullArenaClauseSizeCore s.core r := fun r hr => by
    unfold fullArenaClauseSizeCore; dsimp only [s']
    by_cases hrc : r = cref
    · subst hrc; exact congrArg (fun o => (o.getD 0#32).toNat) har2
    · rcases hout r hr hrc with ⟨h1, _⟩ | hgt
      · have h3 := (hw.arena.refs_wf r hr).2.1; rw [har_out (r + 2) (Or.inl (by omega))]
      · rw [har_out (r + 2) (Or.inr (by omega))]
  have hgb_eq : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaClauseGarbCore s'.core r = fullArenaClauseGarbCore s.core r := fun r hr => by
    unfold fullArenaClauseGarbCore fullArenaHdrCore; dsimp only [s']
    by_cases hrc : r = cref
    · subst hrc; rw [har0]
    · rcases hout r hr hrc with ⟨h1, _⟩ | hgt
      · rw [har_out r (Or.inl (by omega))]
      · rw [har_out r (Or.inr hgt)]
  have hperm_all : ∀ r ∈ fullArenaClauseRefsCore s.core,
      (fullArenaClauseLitsCore s'.core r).Perm (fullArenaClauseLitsCore s.core r) := by
    intro r hr
    have hbd_r : r + 3 + fullArenaClauseSizeCore s.core r ≤ s.core.arena.length := by
      have hwf_r := hw.arena.refs_wf r hr; have := hwf_r.2.2.1; have := hwf_r.2.2.2.1
      have := hlen.core_ok.arena_len_le; have := hlen.core_ok.arena_len_arr; omega
    by_cases hrc : r = cref
    · subst r
      let xs := fullArenaClauseLitsCore s.core cref
      have hxs_len : xs.length = fullArenaClauseSizeCore s.core cref := by
        simp only [xs, fullArenaClauseLitsCore, List.length_map, List.length_take, List.length_drop]
        omega
      have hxs_get : ∀ j (hj : j < fullArenaClauseSizeCore s.core cref),
          xs[j]'(by omega) = (s.core.arena[cref + 3 + j]'(by omega)).toNat := fun j hj => by
        simp [xs, fullArenaClauseLitsCore]
      have heq_lits : fullArenaClauseLitsCore s'.core cref =
          ((xs.set k1 (xs[k2]'(by omega))).set k2 (xs[k1]'(by omega))) := by
        apply List.ext_getElem
        · simp only [fullArenaClauseLitsCore, hsz_eq cref hr, List.length_map, List.length_take,
            List.length_drop, List.length_set, hxs_len, s', arena']
          omega
        · intro j hj1 _
          have hj : j < fullArenaClauseSizeCore s.core cref := by
            simp only [fullArenaClauseLitsCore, hsz_eq cref hr, List.length_map, List.length_take,
              List.length_drop, s', arena'] at hj1; omega
          simp only [fullArenaClauseLitsCore, List.getElem_map, List.getElem_take,
            List.getElem_drop, s', arena']
          by_cases h2 : j = k2
          · subst j; simp [List.getElem_set_self, l1]; exact (hxs_get k1 hk1).symm
          · rw [List.getElem_set_ne (by omega : cref + 3 + k2 ≠ cref + 3 + j),
              List.getElem_set_ne (by omega : k2 ≠ j)]
            by_cases h1 : j = k1
            · subst j; simp [List.getElem_set_self, l2]; exact (hxs_get k2 hk2).symm
            · rw [List.getElem_set_ne (by omega : cref + 3 + k1 ≠ cref + 3 + j),
                List.getElem_set_ne (by omega : cref + 1 ≠ cref + 3 + j),
                List.getElem_set_ne (by omega : k1 ≠ j), hxs_get j hj]
      rw [heq_lits]; exact list_swap_perm_nat xs (by omega) (by omega)
    · rw [fullArenaClauseLitsCore_eq_of_hold (k1 := s'.core) (k2 := s.core)
        (by simp [s', arena', hsz_eq r hr, hbd_r]) hbd_r (hsz_eq r hr) fun j hj => by
          dsimp only [s']; rcases hout r hr hrc with ⟨h1, _⟩ | hgt
          · exact har_out (r + 3 + j) (Or.inl (by omega))
          · exact har_out (r + 3 + j) (Or.inr (by omega))]
  have hshrk_ok : ∀ r ∈ fullArenaClauseRefsCore s.core,
      (fullArenaHdrCore s'.core r &&& 0x00800000#32) ≠ 0#32 →
      ∃ t, r + 3 + fullArenaClauseSizeCore s'.core r ≤ t ∧
        t < s.core.arena_len ∧ arena'[t]? = some 0xFFFFFFFF#32 := by
    intro r hr hsh
    have hsh0 : (fullArenaHdrCore s.core r &&& 0x00800000#32) ≠ 0#32 := by
      unfold fullArenaHdrCore at hsh ⊢; dsimp only [s'] at hsh ⊢
      by_cases hrc : r = cref
      · subst hrc; rwa [har0] at hsh
      · rcases hout r hr hrc with ⟨h1, _⟩ | hgt
        · rwa [har_out r (Or.inl (by omega))] at hsh
        · rwa [har_out r (Or.inr hgt)] at hsh
    obtain ⟨t, ht1, ht2, hsent⟩ := hw.arena.shrk_term r hr hsh0
    have hr3 := (hw.arena.refs_wf r hr).1
    obtain ⟨t0, ht0_lo, ht0_lt, ht0_nxt, ht0_sent⟩ :=
      fullArenaNextOff_hits_sentinel hr3 hsh0 ht1 ht2 hsent
    have ht0_out : t0 < cref ∨ cref + 3 + fullArenaClauseSizeCore s.core cref ≤ t0 := by
      by_cases hrc : r = cref
      · subst hrc; exact Or.inr ht0_lo
      · rcases hout r hr hrc with ⟨_, h2⟩ | hgt
        · exact Or.inl (by omega)
        · exact Or.inr (by omega)
    exact ⟨t0, by rw [hsz_eq r hr]; exact ht0_lo, by omega,
      by rw [har_out t0 ht0_out]; exact ht0_sent⟩
  have hlen' : s'.LengthsOk c := ⟨{ hlen.core_ok with arena_len_arr := har_len' }, hlen.scratch_ok⟩
  have har'_inv : FullArenaClausesInv c F_cur s'.core :=
    { len_ok := hw.arena.len_ok
      shrk_term := fun r hr hsh => hshrk_ok r (hrefs ▸ hr) hsh
      refs_wf := fun r hr => by
        have hr0 : r ∈ fullArenaClauseRefsCore s.core := hrefs ▸ hr
        have hw0 := hw.arena.refs_wf r hr0
        refine ⟨hw0.1, hsz_eq r hr0 ▸ hw0.2.1, ?_, ?_, ?_⟩
        · change r + 3 + fullArenaClauseSizeCore s'.core r ≤
            fullArenaNextOff arena' s.core.arena_len r
          rw [hsz_eq r hr0, hnxt r hr0]; exact hw0.2.2.1
        · change fullArenaNextOff arena' s.core.arena_len r ≤ s.core.arena_len
          rw [hnxt r hr0]; exact hw0.2.2.2.1
        · change fullArenaNextOff arena' s.core.arena_len r = s.core.arena_len ∨
            fullArenaNextOff arena' s.core.arena_len r + 3 ≤ s.core.arena_len
          rw [hnxt r hr0]; exact hw0.2.2.2.2
      lits_lt := fun r hr hg l hl => by
        have hr0 : r ∈ fullArenaClauseRefsCore s.core := hrefs ▸ hr
        rw [hgb_eq r hr0] at hg
        exact hw.arena.lits_lt r hr0 hg l ((hperm_all r hr0).subset hl)
      entails := fun r hr hg => by
        have hr0 : r ∈ fullArenaClauseRefsCore s.core := hrefs ▸ hr
        rw [hgb_eq r hr0] at hg
        exact entailsClause_of_perm (hperm_all r hr0).symm (hw.arena.entails r hr0 hg) }
  have hw' : FullWitnessInv c F0 F_cur s'.core :=
    { hw with
      arena := har'_inv
      watches := hw.watches.with_wstk rfl rfl rfl rfl rfl fun r hr => by
        change r ∈ fullArenaClauseRefsCore s'.core; rw [hrefs]; exact hr
      reason_inv := fun i hi hne => by
        have hrs := hw.reason_inv i hi hne
        by_cases hb : (s.core.rsns[(s.core.trl[i]?.getD 0#32).toNat / 2]?.getD
            0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32
        · rw [ite_eq_left hb] at hrs ⊢; exact hrs
        · rw [ite_eq_right hb] at hrs ⊢
          exact ⟨hrefs ▸ hrs.1, (hgb_eq _ hrs.1).trans hrs.2.1,
            fun q hq => hrs.2.2 q ((hperm_all _ hrs.1).mem_iff.mp hq)⟩
      reason_lit_mem := fun i hi hne hlg => by
        have hrs := hw.reason_inv i hi hne
        rw [ite_eq_right (fun h => h hlg)] at hrs
        exact ((hperm_all _ hrs.1).mem_iff).mpr (hw.reason_lit_mem i hi hne hlg) }
  have hnd' : FullArenaVarsNodup s' := fun r hr hg => by
    have hr0 : r ∈ fullArenaClauseRefsCore s.core := by
      change r ∈ fullArenaClauseRefsCore s'.core at hr; rwa [hrefs] at hr
    have hg0 : fullArenaClauseGarbCore s.core r = false := by
      change fullArenaClauseGarbCore s'.core r = false at hg; rwa [hgb_eq r hr0] at hg
    exact ((hperm_all r hr0).map (· / 2)).nodup_iff.mpr (hsp.2.2.2.1 r hr0 hg0)
  have hext' : FullExtScratchOk c s' := by
    refine ⟨fun i hi => ?_, hsp.2.2.2.2.1.2⟩
    change (s'.scratch.last_learned[i]?.getD 0xFFFFFFFF#32) = 0xFFFFFFFF#32 ∨
      (s'.scratch.last_learned[i]?.getD 0xFFFFFFFF#32).toNat ∈ fullArenaClauseRefsCore s'.core
    rw [hrefs]; exact hsp.2.2.2.2.1.1 i hi
  exact ⟨⟨hlen', hw', hsp.2.2.1, hnd', hext', hsp.2.2.2.2.2⟩,
    ⟨rfl, hrefs, fun r hr => ⟨hsz_eq r hr, hgb_eq r hr, hperm_all r hr⟩⟩⟩

theorem setSrch_preserves_sparseInvW {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hsp : FullSparseInvW c F0 F_cur s)
    {cref : Nat} {srch : BitVec 32} (hcref : cref ∈ fullArenaClauseRefsCore s.core) :
    let s' : FullState :=
      { s with core := { s.core with arena := s.core.arena.set (cref + 1) srch } }
    FullSparseInvW c F0 F_cur s' ∧ FullArenaPermEq s.core s'.core := by
  have hwf := hsp.2.1.arena.refs_wf cref hcref
  have h3 : 3 ≤ fullArenaClauseSizeCore s.core cref := hwf.2.1
  have hbd : cref + 3 + fullArenaClauseSizeCore s.core cref ≤ s.core.arena.length := by
    have := hwf.2.2.1; have := hwf.2.2.2.1
    have := hsp.1.core_ok.arena_len_le; have := hsp.1.core_ok.arena_len_arr; omega
  have hsw := swapCl_preserves_sparseInvW hsp (cref := cref) (k1 := 0) (k2 := 0) (srch := srch)
    hcref (by omega) (by omega)
  have heq : (((s.core.arena.set (cref + 1) srch).set (cref + 3 + 0)
      (s.core.arena[cref + 3 + 0]'(by omega))).set (cref + 3 + 0)
      (s.core.arena[cref + 3 + 0]'(by omega))) = s.core.arena.set (cref + 1) srch := by
    apply List.ext_getElem (by simp); intro j hj _
    by_cases h0 : j = cref + 3 + 0
    · subst h0; simp [List.getElem_set_self, List.getElem_set_ne (by omega : cref + 1 ≠ cref + 3)]
    · rw [List.getElem_set_ne (Ne.symm h0), List.getElem_set_ne (Ne.symm h0)]
  simpa only [heq] using hsw

theorem swapLits_preserves_sparseInvW {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hsp : FullSparseInvW c F0 F_cur s)
    {cref k1 k2 : Nat} (hcref : cref ∈ fullArenaClauseRefsCore s.core)
    (hk1 : k1 < fullArenaClauseSizeCore s.core cref)
    (hk2 : k2 < fullArenaClauseSizeCore s.core cref) :
    have hbd : cref + 3 + fullArenaClauseSizeCore s.core cref ≤ s.core.arena.length := by
      have hwf := hsp.2.1.arena.refs_wf cref hcref; have := hwf.2.2.1; have := hwf.2.2.2.1
      have := hsp.1.core_ok.arena_len_le; have := hsp.1.core_ok.arena_len_arr; omega
    let l1 := s.core.arena[cref + 3 + k1]'(by omega)
    let l2 := s.core.arena[cref + 3 + k2]'(by omega)
    let s' : FullState :=
      { s with core := { s.core with arena :=
          (s.core.arena.set (cref + 3 + k1) l2).set (cref + 3 + k2) l1 } }
    FullSparseInvW c F0 F_cur s' ∧ FullArenaPermEq s.core s'.core := by
  intro hbd l1 l2 s'
  have h1_lt : cref + 1 < s.core.arena.length := by omega
  have hsw := swapCl_preserves_sparseInvW hsp (cref := cref) (k1 := k1) (k2 := k2)
    (srch := s.core.arena[cref + 1]'h1_lt) hcref hk1 hk2
  have hset1 : s.core.arena.set (cref + 1) (s.core.arena[cref + 1]'h1_lt) = s.core.arena := by
    apply List.ext_getElem (by simp); intro j hj _
    by_cases h : j = cref + 1
    · subst h; simp
    · rw [List.getElem_set_ne (Ne.symm h)]
  simpa only [hset1] using hsw

theorem fullSparseInvW_with_rng_gu {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hsp : FullSparseInvW c F0 F_cur s)
    {sc' : FullScratch} (hok : sc'.LengthsOk c)
    (hll : sc'.last_learned = s.scratch.last_learned)
    (hext : sc'.extend_len = s.scratch.extend_len) :
    FullSparseInvW c F0 F_cur { s with scratch := sc' } :=
  ⟨hsp.1.with_scratch hok, hsp.2.1, hsp.2.2.1, hsp.2.2.2.1,
    ⟨fun i hi => by change (sc'.last_learned[i]?.getD 0xFFFFFFFF#32) = 0xFFFFFFFF#32 ∨ _; rw [hll]
                    exact hsp.2.2.2.2.1.1 i hi, by rw [hext]; exact hsp.2.2.2.2.1.2⟩,
    hsp.2.2.2.2.2⟩

theorem fullSparseInv_with_probing {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hsp : FullSparseInv c F0 s) (pr : BitVec 64) :
    FullSparseInv c F0 { s with core := { s.core with probing := pr } } := by
  obtain ⟨F_cur, hw⟩ := hsp.1.witness
  refine ⟨⟨⟨{ hsp.1.lengths.core_ok with vals_len := hsp.1.lengths.core_ok.vals_len },
    hsp.1.lengths.scratch_ok⟩, F_cur,
    { hw with arena := { hw.arena with len_ok := hw.arena.len_ok }
              watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }⟩,
    hsp.2.1, hsp.2.2.1, hsp.2.2.2.1, hsp.2.2.2.2⟩

theorem fullSparseInv_with_fuel {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hsp : FullSparseInv c F0 s) (fl : BitVec 64) :
    FullSparseInv c F0 { s with core := { s.core with fuel := fl } } := by
  obtain ⟨F_cur, hw⟩ := hsp.1.witness
  refine ⟨⟨⟨{ hsp.1.lengths.core_ok with vals_len := hsp.1.lengths.core_ok.vals_len },
    hsp.1.lengths.scratch_ok⟩, F_cur,
    { hw with arena := { hw.arena with len_ok := hw.arena.len_ok }
              watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }⟩,
    hsp.2.1, hsp.2.2.1, hsp.2.2.2.1, hsp.2.2.2.2⟩

theorem fullSparseInv_of_fullPropagate {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s s' : FullState}
    (hsp : FullSparseInv c F0 s) (hlen' : s'.LengthsOk c)
    (hw' : FullWitnessInv c F0 F_cur s'.core) (hperm : FullArenaPermEq s.core s'.core)
    (hmrk : s'.core.mrk = s.core.mrk) (hlmrk : s'.core.lit_mark = s.core.lit_mark)
    (hdense : s'.core.dense_mode = s.core.dense_mode)
    (hll : s'.scratch.last_learned = s.scratch.last_learned)
    (hext : s'.scratch.extend_len = s.scratch.extend_len) :
    FullSparseInv c F0 s' := by
  refine ⟨⟨hlen', F_cur, hw'⟩, ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩, ?_⟩
  · intro v hv; rw [hmrk]; exact hsp.2.1.1 v hv
  · intro l hl; rw [hlmrk]; exact hsp.2.1.2 l hl
  · intro r hr hg
    have hr0 : r ∈ fullArenaClauseRefs s := by
      change r ∈ fullArenaClauseRefsCore s.core; rw [← hperm.2.1]; exact hr
    have hg0 : fullArenaClauseGarb s r = false := by
      change fullArenaClauseGarbCore s.core r = false
      rw [← (hperm.2.2 r hr0).2.1]; exact hg
    exact (((hperm.2.2 r hr0).2.2).map (· / 2)).nodup_iff.mpr (hsp.2.2.1 r hr0 hg0)
  · intro i hi
    change (s'.scratch.last_learned[i]?.getD 0xFFFFFFFF#32) = 0xFFFFFFFF#32 ∨
      (s'.scratch.last_learned[i]?.getD 0xFFFFFFFF#32).toNat ∈ fullArenaClauseRefsCore s'.core
    rw [hll, hperm.2.1]; exact hsp.2.2.2.1.1 i hi
  · rw [hext]; exact hsp.2.2.2.1.2
  · rw [hdense]; exact hsp.2.2.2.2

theorem fullSparseInv_of_fullBacktrack {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s s' : FullState}
    (hsp : FullSparseInv c F0 s) (hlen' : s'.LengthsOk c)
    (hw' : FullWitnessInv c F0 F_cur s'.core)
    (hmrk : s'.core.mrk = s.core.mrk) (hlmrk : s'.core.lit_mark = s.core.lit_mark)
    (har : s'.core.arena = s.core.arena) (harl : s'.core.arena_len = s.core.arena_len)
    (hdense : s'.core.dense_mode = s.core.dense_mode)
    (hll : s'.scratch.last_learned = s.scratch.last_learned)
    (hext : s'.scratch.extend_len = s.scratch.extend_len) :
    FullSparseInv c F0 s' := by
  have hperm : FullArenaPermEq s.core s'.core := by
    refine ⟨harl, ?_, fun r _ => ⟨?_, ?_, ?_⟩⟩ <;>
      simp [fullArenaClauseRefsCore, fullArenaHdrCore, fullArenaClauseSizeCore,
        fullArenaClauseGarbCore, fullArenaClauseLitsCore, har, harl]
  exact fullSparseInv_of_fullPropagate hsp hlen' hw' hperm hmrk hlmrk hdense hll hext

theorem level0_unsat_of_conflict_okW {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hw : FullWitnessInv c F0 F_cur s.core) (hl0 : s.core.cur_level = 0)
    (hc : FullConflictOkW F_cur s) : F0.Unsat := by
  rcases hc with ⟨_, h0lt, h1lt, hf0, hf1, hent⟩ | ⟨_, href, hng, hfals⟩
  · refine hw.ext_sound.2 (unsat_of_entails_nil (entails_of_mem_or_false hent fun l hl => ?_))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    right; rcases hl with rfl | rfl
    · obtain ⟨i, hi, heq⟩ := (hw.vals_false_iff _ h0lt).mp hf0
      have hs := hw.level0_sound i hi (by have := hw.lvl_le i hi; omega); rwa [heq] at hs
    · obtain ⟨i, hi, heq⟩ := (hw.vals_false_iff _ h1lt).mp hf1
      have hs := hw.level0_sound i hi (by have := hw.lvl_le i hi; omega); rwa [heq] at hs
  · refine hw.ext_sound.2
      (unsat_of_entails_nil (entails_of_mem_or_false (hw.arena.entails _ href hng) fun l hl => ?_))
    right
    obtain ⟨i, hi, heq⟩ := (hw.vals_false_iff _ (hw.arena.lits_lt _ href hng l hl)).mp (hfals l hl)
    have hs := hw.level0_sound i hi (by have := hw.lvl_le i hi; omega); rwa [heq] at hs

/-- Chronological decision step preserving `FullCoreInv`. -/
theorem m7_decide_preserves_fullCore {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hinv : FullCoreInv c F0 s) {v : Nat} {lit : BitVec 32}
    {flags' : List (BitVec 32)} {unas' unfl' : BitVec 64} {scratch' : FullScratch}
    (hsok' : scratch'.LengthsOk c) (hfll : flags'.length = c.max_vars)
    (hv_lt : v < s.core.cur_vars) (hval0 : s.core.vals[2 * v]?.getD 0#8 = 0#8)
    (hlit_eq : lit.toNat = 2 * v ∨ lit.toNat = 2 * v + 1) :
    let nlvl := s.core.cur_level + 1
    let ftrl' := s.core.frame_trail.set nlvl (BitVec.ofNat 32 s.core.trail_end)
    let fdec' := s.core.frame_dec.set nlvl lit
    let s' : FullState :=
      { core :=
          { s.core with
            vals := (s.core.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8
            flags := flags', lvl := s.core.lvl.set (lit.toNat / 2) (BitVec.ofNat 32 nlvl)
            rsns := s.core.rsns.set (lit.toNat / 2) 0xFFFFFFFF#32
            trl := s.core.trl.set s.core.trail_end lit
            trail_pos := s.core.trail_pos.set (lit.toNat / 2) (BitVec.ofNat 32 s.core.trail_end)
            frame_trail := ftrl', frame_dec := fdec', trail_end := s.core.trail_end + 1
            cur_level := nlvl, unassigned := unas', unflushed := unfl' }
        scratch := scratch' }
    FullCoreInv c F0 s' ∧ s.core.vals[lit.toNat]?.getD 0#8 = 0#8 ∧
    s.core.trail_end < s.core.cur_vars ∧ nlvl ≤ c.max_vars := by
  intro nlvl ftrl' fdec' s'
  obtain ⟨F_cur, hw⟩ := hinv.witness; have hcl := hinv.lengths.core_ok
  have hcv := hcl.cur_vars_le; have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  have hlit_lt : lit.toNat < 2 * s.core.cur_vars := by omega
  have hlit_v : lit.toNat / 2 = v := by omega
  have hun : s.core.vals[lit.toNat]?.getD 0#8 = 0#8 := by
    rcases hlit_eq with he | ho
    · rw [he]; exact hval0
    · have hnot0 := (hw.vals_zero_iff (by omega : 2 * v < 2 * s.core.cur_vars)).mp hval0
      rw [ho]
      exact (hw.vals_zero_iff (by omega : 2 * v + 1 < 2 * s.core.cur_vars)).mpr fun i hi => by
        have := hnot0 i hi; omega
  have hte_lt : s.core.trail_end < s.core.cur_vars := hw.trail_end_lt_of_unassigned hlit_lt hun
  have hcl_le : s.core.cur_level ≤ s.core.trail_end := hw.cur_level_le
  have hnlvl_le : nlvl ≤ c.max_vars := by dsimp [nlvl]; omega
  have hte_lt32 : s.core.trail_end < 2 ^ 32 := by omega
  have hnot_var : ∀ i < s.core.trail_end, (s.core.trl[i]?.getD 0#32).toNat / 2 ≠ lit.toNat / 2 :=
    (hw.vals_zero_iff hlit_lt).mp hun
  have hft_get : ∀ L ≤ nlvl, (ftrl'[L]?.getD 0#32).toNat =
      if L = nlvl then s.core.trail_end
      else (s.core.frame_trail[L]?.getD 0#32).toNat := fun L _ => by
    by_cases hL : L = nlvl
    · subst hL; dsimp only [ftrl']
      rw [List.getElem?_set_self (by rw [hcl.frame_trail_len]; omega), Option.getD_some,
        bv32_ofNat_toNat hte_lt32]; simp
    · dsimp only [ftrl']; rw [List.getElem?_set_ne (Ne.symm hL)]; simp [hL]
  have hfd_get : ∀ L ≤ nlvl, (fdec'[L]?.getD 0#32).toNat =
      if L = nlvl then lit.toNat else (s.core.frame_dec[L]?.getD 0#32).toNat := fun L _ => by
    by_cases hL : L = nlvl
    · subst hL; dsimp only [fdec']
      rw [List.getElem?_set_self (by rw [hcl.frame_dec_len]; omega), Option.getD_some]; simp
    · dsimp only [fdec']; rw [List.getElem?_set_ne (Ne.symm hL)]; simp [hL]
  have hcore' := chronoAssign_preserves_fullCore hinv (lit := lit) (rsn := 0xFFFFFFFF#32)
    (alvl := nlvl) (cur_level' := nlvl) (propagated' := s.core.propagated)
    (flags' := flags') (frame_trail' := ftrl') (frame_dec' := fdec')
    (unassigned' := unas') (unflushed' := unfl') (scratch' := scratch')
    hsok' hfll (by simp [ftrl', hcl.frame_trail_len]) (by simp [fdec', hcl.frame_dec_len])
    hlit_lt hun (Nat.le_refl _) (by have := hcl.propagated_le; omega) (by dsimp [nlvl]; omega)
    (fun L hL => by
      rw [hft_get L hL]; split
      · omega
      · have := hw.frame_trail_lt L (by dsimp [nlvl] at *; omega); omega)
    (fun L1 L2 h12 h2 => by
      rw [hft_get L1 (by omega), hft_get L2 h2]
      by_cases h2e : L2 = nlvl
      · by_cases h1e : L1 = nlvl
        · simp [h1e, h2e]
        · simp only [h1e, h2e, ↓reduceIte]; exact hw.frame_trail_lt L1 (by dsimp [nlvl] at *; omega)
      · have h1n : L1 ≠ nlvl := by omega
        simp only [h1n, h2e, ↓reduceIte]
        exact hw.frame_trail_mono L1 L2 h12 (by dsimp [nlvl] at *; omega))
    (fun L hL1 hLle i hi => by
      rw [hft_get L hLle] at hi
      by_cases hLe : L = nlvl
      · subst hLe; simp only [↓reduceIte] at hi
        have hne_i : i ≠ s.core.trail_end := by omega
        have hnv : (s.core.trl[i]?.getD 0#32).toNat / 2 ≠ lit.toNat / 2 := hnot_var i hi
        simp only [hne_i, hnv, ↓reduceIte]
        have := hw.lvl_le i hi; dsimp [nlvl]; omega
      · simp only [hLe, ↓reduceIte] at hi
        have hLle' : L ≤ s.core.cur_level := by dsimp [nlvl] at *; omega
        have hi_lt : i < s.core.trail_end := Nat.lt_of_lt_of_le hi (hw.frame_trail_lt L hLle')
        have hne_i : i ≠ s.core.trail_end := by omega
        have hnv : (s.core.trl[i]?.getD 0#32).toNat / 2 ≠ lit.toNat / 2 := hnot_var i hi_lt
        simp only [hne_i, hnv, ↓reduceIte]
        exact hw.frame_trail_before_lt L hL1 hLle' i hi)
    (fun L hL1 hLle => by
      rw [hfd_get L hLle]; split
      · exact hlit_lt
      · exact hw.frame_dec_lt L hL1 (by dsimp [nlvl] at *; omega))
    (fun i hi => by have := hw.lvl_le i hi; dsimp [nlvl]; omega)
    (fun L hL1 hLle => by
      by_cases hLe : L = nlvl
      · exact Or.inl hLe
      · exact Or.inr (hw.levels_inhabited L hL1 (by dsimp [nlvl] at *; omega)))
    (fun _ _ i hi => by have := hw.lvl_le i hi; dsimp [nlvl]; omega)
    (fun hz => by dsimp [nlvl] at hz; omega)
    (fun _ hne => absurd rfl hne)
    (fun _ hne _ => absurd rfl hne)
  have hnlvl_ne0 : nlvl ≠ 0 := by dsimp [nlvl]; omega
  simpa only [s', hnlvl_ne0, ↓reduceIte] using ⟨hcore', hun, hte_lt, hnlvl_le⟩

/-! ## 4. Per-Function `Spec` Contracts, `_of` / `_elim` Bridges & Drop-In Adapters -/

def m7LcgNextSpec : Spec [i64] [i64] :=
  SafetySlice.spec fullSafetySlice (fun c (h, ()) _ => h = c.hdr)
    (fun _ _ (r, ()) s s' =>
      let p := m7LcgNextVal s.scratch.rng_state
      r = p.2 ∧ s'.scratch = { s.scratch with rng_state := p.1 })

def m7Get64Spec : Spec [i64, i64] [i64] := fun (h, idx, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
    Q ((if idx.toNat < 63 then m7Get64Val s.scratch.glue_used idx.toNat else 0#64), ()) m

def m7Set64Spec : Spec [i64, i64, i64] [] := fun (h, idx, val, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
    let gu' := if idx.toNat < 63 then m7Set64List s.scratch.glue_used idx.toNat val
               else s.scratch.glue_used
    let s' : FullState := { s with scratch := { s.scratch with glue_used := gu' } }
    s'.LengthsOk c → ∀ m', (FullMem c s' ⋆ R) m' → Q () m'

def m7StateInitSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
    let s' : FullState :=
      { s with scratch := { s.scratch with glue_used := m7StateInitGu s.scratch } }
    s'.LengthsOk c → M7StateInitOk s'.scratch.glue_used → M7GuPrefixPres s s' →
    ∀ m', (FullMem c s' ⋆ R) m' → Q () m'

def m7Log10Q16Spec : Spec [i64] [i64] := fun (x, ()) m Q _ =>
  ∀ r : BitVec 64, r.toNat < 20 * 65536 → (10 ≤ x.toNat → 65536 ≤ r.toNat) → Q (r, ()) m

def m7TumbleClauseSpec : Spec [i64, i32] [.bool] := fun (h, cref, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInvW c F0 F_cur s ∧ cref.toNat ∈ fullArenaClauseRefs s ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) ar' rng' m',
      let s' : FullState :=
        { core := { s.core with arena := ar' }, scratch := { s.scratch with rng_state := rng' } }
      FullSparseInvW c F0 F_cur s' → FullArenaPermEq s.core s'.core →
      (∀ i < s.core.arena_len,
        (i ≠ cref.toNat + 1 ∧ ¬ (cref.toNat + 5 ≤ i ∧ i < cref.toNat + 3 +
          fullArenaClauseSizeCore s.core cref.toNat)) →
        ar'[i]? = s.core.arena[i]?) →
      (ok = false → ar' = s.core.arena ∧ rng' = s.scratch.rng_state) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

def m7TumbleClausesSpec : Spec [i64, i64] [i64] := fun (h, _budget, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInvW c F0 F_cur s ∧ (FullMem c s ⋆ R) m ∧
    ∀ (done : BitVec 64) ar' rng' m',
      let s' : FullState :=
        { core := { s.core with arena := ar' }, scratch := { s.scratch with rng_state := rng' } }
      FullSparseInvW c F0 F_cur s' → FullArenaPermEq s.core s'.core →
      (∀ r ∈ fullArenaClauseRefs s, 3 ≤ fullArenaClauseSize s r →
        ar'[r + 3]? = s.core.arena[r + 3]? ∧ ar'[r + 4]? = s.core.arena[r + 4]?) →
      (FullMem c s' ⋆ R) m' → Q (done, ()) m'

def m7TumbleSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInvW c F0 F_cur s ∧ (FullMem c s ⋆ R) m ∧
    ∀ (done : BitVec 64) ar' rng' m',
      let s' : FullState :=
        { core := { s.core with arena := ar' }, scratch := { s.scratch with rng_state := rng' } }
      FullSparseInvW c F0 F_cur s' → FullArenaPermEq s.core s'.core →
      (∀ r ∈ fullArenaClauseRefs s, 3 ≤ fullArenaClauseSize s r →
        ar'[r + 3]? = s.core.arena[r + 3]? ∧ ar'[r + 4]? = s.core.arena[r + 4]?) →
      (FullMem c s' ⋆ R) m' → Q (done, ()) m'

def m7LuckyLateSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      s'.LengthsOk c → (r = 0#64 ∨ r = 2#64 ∨ r = 10#64 ∨ r = 20#64) →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat → s'.core.probing = 0#64 →
      (r = 20#64 → F0.Unsat) →
      (r = 0#64 ∨ r = 2#64 → FullSparseInv c F0 s' ∧ s'.core.cur_level = 0) →
      (r = 10#64 → s'.scratch.extend_len ≤ c.extend_cap) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

def m7RandecStepSpec : Spec [i64] [] :=
  SafetySlice.spec fullSafetySlice (fun c (h, ()) _ => h = c.hdr)
    (fun _ _ _ s s' => FullProbeScratchPres s s' ∧ M7GuPrefixPres s s' ∧
      M7StateInitOk s'.scratch.glue_used ∧
      ∃ gu', s'.scratch = { s.scratch with glue_used := gu' })

def m7RandecVarSpec : Spec [i64] [i64] :=
  SafetySlice.spec fullSafetySlice (fun c (h, ()) _ => h = c.hdr)
    (fun _ _ (r, ()) s s' =>
      FullProbeScratchPres s s' ∧ M7GuPrefixPres s s' ∧
      (r = 0xFFFFFFFFFFFFFFFF#64 ∨
        (r.toNat < s.core.cur_vars ∧
          (s.core.flags[r.toNat]?.getD 0#32 &&& 1#32) ≠ 0#32 ∧
          s.core.vals[2 * r.toNat]?.getD 0#8 = 0#8)))

def m7DecideSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullCoreInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r vals' flags' lvl' rsns' trl' tp' ftrl' fdec' te' cl' unass' unfl' sc' m',
      let s' : FullState :=
        { core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                                trl := trl', trail_pos := tp', frame_trail := ftrl',
                                frame_dec := fdec', trail_end := te', cur_level := cl',
                                unassigned := unass', unflushed := unfl' }
          scratch := sc' }
      FullCoreInv c F0 s' → FullExtScratchPres s s' →
      (r = 0#64 ∨ r = 1#64) →
      (r = 0#64 → cl' = s.core.cur_level ∧ te' = s.core.trail_end) →
      (r = 1#64 → cl' = s.core.cur_level + 1 ∧ te' = s.core.trail_end + 1 ∧
        s.core.trail_end < trl'.length ∧
        s.core.vals[(trl'[s.core.trail_end]?.getD 0#32).toNat]?.getD 0#8 = 0#8) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

def m7EmaSwapSpec : Spec [i64, i64, i64] [] := fun (h, old_m, new_m, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
    let s' : FullState := { s with scratch := m7EmaSwapSc s.scratch old_m new_m }
    s'.LengthsOk c → M7GuPrefixPres s s' → M7StateInitOk s'.scratch.glue_used →
    ∀ m', (FullMem c s' ⋆ R) m' → Q () m'

def m7SwitchModeSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
    ∀ s' m',
      s'.core = s.core → s'.LengthsOk c → FullProbeScratchPres s s' →
      ((s.scratch.stable = 0#64 ∧ s.scratch.conflicts < s.scratch.mode_confl_lim) ∨
       (s.scratch.stable ≠ 0#64 ∧ s.scratch.search_ticks < s.scratch.mode_tick_lim) → s' = s) →
      (s.scratch.stable = 0#64 ∧ s.scratch.mode_confl_lim ≤ s.scratch.conflicts →
        M7StateInitOk s'.scratch.glue_used ∧ s'.scratch.stable = 1#64) →
      (s.scratch.stable ≠ 0#64 ∧ s.scratch.mode_tick_lim ≤ s.scratch.search_ticks →
        M7GuPrefixPres s s' ∧ M7StateInitOk s'.scratch.glue_used ∧
        m7ModeEmaGet s'.scratch.glue_used 1 =
          (s.scratch.ema_fast_biased, s.scratch.ema_fast_exp,
           s.scratch.ema_slow_biased, s.scratch.ema_slow_exp) ∧
        s'.scratch.stable = 0#64 ∧
        ((m7Get64Val s.scratch.glue_used m7GuMagicIdx = m7SearchMagic ∧
          (m7Get64Val s.scratch.glue_used m7GuEmaMaskIdx &&& 1#64) ≠ 0#64) →
         let saved := m7ModeEmaGet s.scratch.glue_used 0
         s'.scratch.ema_fast_biased = saved.1 ∧ s'.scratch.ema_fast_exp = saved.2.1 ∧
         s'.scratch.ema_slow_biased = saved.2.2.1 ∧ s'.scratch.ema_slow_exp = saved.2.2.2)) →
      (FullMem c s' ⋆ R) m' → Q () m'

/-! ### Public Spec Constructors, Destructors & Drop-In Canonical Bridges -/

theorem m7LcgNextSpec_of {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} (hlen : s.LengthsOk c) (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ (r : BitVec 64) s' m', s'.core = s.core → s'.LengthsOk c →
      (let p := m7LcgNextVal s.scratch.rng_state
       r = p.2 ∧ s'.scratch = { s.scratch with rng_state := p.1 }) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m') : m7LcgNextSpec (c.hdr, ()) m Q X :=
  ⟨c, s, R, rfl, hlen, hm, fun ⟨r, ⟨⟩⟩ _ _ hc hlen' hp hm' => hQ r _ _ hc hlen' hp hm'⟩

theorem m7LcgNextSpec_monoX {xs : Tup Val [i64]} {m : Mem 64} {Q : Post [i64]} {X X' : XPost}
    (h : m7LcgNextSpec xs m Q X) : m7LcgNextSpec xs m Q X' := h

theorem m7Get64Spec_of {c : FullCfg} {idx : BitVec 64} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} {Q : Post [i64]} {X : XPost} (hlen : s.LengthsOk c) (hm : (FullMem c s ⋆ R) m)
    (hQ : Q ((if idx.toNat < 63 then m7Get64Val s.scratch.glue_used idx.toNat else 0#64), ()) m) :
    m7Get64Spec (c.hdr, idx, ()) m Q X :=
  ⟨c, s, R, rfl, hlen, hm, hQ⟩

theorem m7Get64Spec_monoX {xs : Tup Val [i64, i64]} {m : Mem 64} {Q : Post [i64]} {X X' : XPost}
    (h : m7Get64Spec xs m Q X) : m7Get64Spec xs m Q X' := h

theorem m7Set64Spec_of {c : FullCfg} {idx val : BitVec 64} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} {Q : Post []} {X : XPost} (hlen : s.LengthsOk c) (hm : (FullMem c s ⋆ R) m)
    (hQ : let gu' := if idx.toNat < 63 then m7Set64List s.scratch.glue_used idx.toNat val
                     else s.scratch.glue_used
          let s' : FullState := { s with scratch := { s.scratch with glue_used := gu' } }
          s'.LengthsOk c → ∀ m', (FullMem c s' ⋆ R) m' → Q () m') :
    m7Set64Spec (c.hdr, idx, val, ()) m Q X :=
  ⟨c, s, R, rfl, hlen, hm, hQ⟩

theorem m7Set64Spec_monoX {xs : Tup Val [i64, i64, i64]} {m : Mem 64} {Q : Post []} {X X' : XPost}
    (h : m7Set64Spec xs m Q X) : m7Set64Spec xs m Q X' := h

theorem m7StateInitSpec_of {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post []} {X : XPost} (hlen : s.LengthsOk c) (hm : (FullMem c s ⋆ R) m)
    (hQ : let s' : FullState :=
            { s with scratch := { s.scratch with glue_used := m7StateInitGu s.scratch } }
          s'.LengthsOk c → M7StateInitOk s'.scratch.glue_used → M7GuPrefixPres s s' →
          ∀ m', (FullMem c s' ⋆ R) m' → Q () m') :
    m7StateInitSpec (c.hdr, ()) m Q X :=
  ⟨c, s, R, rfl, hlen, hm, hQ⟩

theorem m7StateInitSpec_monoX {xs : Tup Val [i64]} {m : Mem 64} {Q : Post []} {X X' : XPost}
    (h : m7StateInitSpec xs m Q X) : m7StateInitSpec xs m Q X' := h

theorem m7Log10Q16Spec_monoX {xs : Tup Val [i64]} {m : Mem 64} {Q : Post [i64]} {X X' : XPost}
    (h : m7Log10Q16Spec xs m Q X) : m7Log10Q16Spec xs m Q X' := h

theorem m7TumbleClauseSpec_of {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {cref : BitVec 32} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [.bool]}
    {X : XPost} (hsp : FullSparseInvW c F0 F_cur s) (hcr : cref.toNat ∈ fullArenaClauseRefs s)
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ ok ar' rng' m',
      let s' : FullState :=
        { core := { s.core with arena := ar' }, scratch := { s.scratch with rng_state := rng' } }
      FullSparseInvW c F0 F_cur s' → FullArenaPermEq s.core s'.core →
      (∀ i < s.core.arena_len,
        (i ≠ cref.toNat + 1 ∧ ¬ (cref.toNat + 5 ≤ i ∧ i < cref.toNat + 3 +
          fullArenaClauseSizeCore s.core cref.toNat)) →
        ar'[i]? = s.core.arena[i]?) →
      (ok = false → ar' = s.core.arena ∧ rng' = s.scratch.rng_state) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    m7TumbleClauseSpec (c.hdr, cref, ()) m Q X :=
  ⟨c, F0, F_cur, s, R, rfl, hsp, hcr, hm, hQ⟩

theorem m7TumbleClauseSpec_elim {a m Q X} (hs : m7TumbleClauseSpec a m Q X) :
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      a.1 = c.hdr ∧ FullSparseInvW c F0 F_cur s ∧ a.2.1.toNat ∈ fullArenaClauseRefs s ∧
      (FullMem c s ⋆ R) m ∧
      ∀ ok ar' rng' m',
        let s' : FullState :=
          { core := { s.core with arena := ar' }, scratch := { s.scratch with rng_state := rng' } }
        FullSparseInvW c F0 F_cur s' → FullArenaPermEq s.core s'.core →
        (∀ i < s.core.arena_len,
          (i ≠ a.2.1.toNat + 1 ∧ ¬ (a.2.1.toNat + 5 ≤ i ∧ i < a.2.1.toNat + 3 +
            fullArenaClauseSizeCore s.core a.2.1.toNat)) →
          ar'[i]? = s.core.arena[i]?) →
        (ok = false → ar' = s.core.arena ∧ rng' = s.scratch.rng_state) →
        (FullMem c s' ⋆ R) m' → Q (ok, ()) m' := by
  rcases a with ⟨h, cref, ⟨⟩⟩; exact hs

theorem m7TumbleClauseSpec_monoX {xs : Tup Val [i64, i32]} {m : Mem 64} {Q : Post [.bool]}
    {X X' : XPost} (h : m7TumbleClauseSpec xs m Q X) : m7TumbleClauseSpec xs m Q X' := h

theorem m7TumbleClausesSpec_of {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {budget : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [i64]}
    {X : XPost} (hsp : FullSparseInvW c F0 F_cur s) (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ done ar' rng' m',
      let s' : FullState :=
        { core := { s.core with arena := ar' }, scratch := { s.scratch with rng_state := rng' } }
      FullSparseInvW c F0 F_cur s' → FullArenaPermEq s.core s'.core →
      (∀ r ∈ fullArenaClauseRefs s, 3 ≤ fullArenaClauseSize s r →
        ar'[r + 3]? = s.core.arena[r + 3]? ∧ ar'[r + 4]? = s.core.arena[r + 4]?) →
      (FullMem c s' ⋆ R) m' → Q (done, ()) m') :
    m7TumbleClausesSpec (c.hdr, budget, ()) m Q X :=
  ⟨c, F0, F_cur, s, R, rfl, hsp, hm, hQ⟩

theorem m7TumbleClausesSpec_elim {a m Q X} (hs : m7TumbleClausesSpec a m Q X) :
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      a.1 = c.hdr ∧ FullSparseInvW c F0 F_cur s ∧ (FullMem c s ⋆ R) m ∧
      ∀ done ar' rng' m',
        let s' : FullState :=
          { core := { s.core with arena := ar' }, scratch := { s.scratch with rng_state := rng' } }
        FullSparseInvW c F0 F_cur s' → FullArenaPermEq s.core s'.core →
        (∀ r ∈ fullArenaClauseRefs s, 3 ≤ fullArenaClauseSize s r →
          ar'[r + 3]? = s.core.arena[r + 3]? ∧ ar'[r + 4]? = s.core.arena[r + 4]?) →
        (FullMem c s' ⋆ R) m' → Q (done, ()) m' := by
  rcases a with ⟨h, budget, ⟨⟩⟩; exact hs

theorem m7TumbleClausesSpec_monoX {xs : Tup Val [i64, i64]} {m : Mem 64} {Q : Post [i64]}
    {X X' : XPost} (h : m7TumbleClausesSpec xs m Q X) : m7TumbleClausesSpec xs m Q X' := h

theorem m7TumbleSpec_of {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hsp : FullSparseInvW c F0 F_cur s) (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ done ar' rng' m',
      let s' : FullState :=
        { core := { s.core with arena := ar' }, scratch := { s.scratch with rng_state := rng' } }
      FullSparseInvW c F0 F_cur s' → FullArenaPermEq s.core s'.core →
      (∀ r ∈ fullArenaClauseRefs s, 3 ≤ fullArenaClauseSize s r →
        ar'[r + 3]? = s.core.arena[r + 3]? ∧ ar'[r + 4]? = s.core.arena[r + 4]?) →
      (FullMem c s' ⋆ R) m' → Q (done, ()) m') :
    m7TumbleSpec (c.hdr, ()) m Q X :=
  ⟨c, F0, F_cur, s, R, rfl, hsp, hm, hQ⟩

theorem m7TumbleSpec_elim {a m Q X} (hs : m7TumbleSpec a m Q X) :
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      a.1 = c.hdr ∧ FullSparseInvW c F0 F_cur s ∧ (FullMem c s ⋆ R) m ∧
      ∀ done ar' rng' m',
        let s' : FullState :=
          { core := { s.core with arena := ar' }, scratch := { s.scratch with rng_state := rng' } }
        FullSparseInvW c F0 F_cur s' → FullArenaPermEq s.core s'.core →
        (∀ r ∈ fullArenaClauseRefs s, 3 ≤ fullArenaClauseSize s r →
          ar'[r + 3]? = s.core.arena[r + 3]? ∧ ar'[r + 4]? = s.core.arena[r + 4]?) →
        (FullMem c s' ⋆ R) m' → Q (done, ()) m' := by
  rcases a with ⟨h, ⟨⟩⟩; exact hs

theorem m7TumbleSpec_monoX {xs : Tup Val [i64]} {m : Mem 64} {Q : Post [i64]} {X X' : XPost}
    (h : m7TumbleSpec xs m Q X) : m7TumbleSpec xs m Q X' := h

theorem m7LuckyLateSpec_of {c : FullCfg} {F0 : CNF Nat} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} {Q : Post [i64]} {X : XPost} (hsp : FullSparseInv c F0 s)
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ r s' m',
      s'.LengthsOk c → (r = 0#64 ∨ r = 2#64 ∨ r = 10#64 ∨ r = 20#64) →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat → s'.core.probing = 0#64 →
      (r = 20#64 → F0.Unsat) →
      (r = 0#64 ∨ r = 2#64 → FullSparseInv c F0 s' ∧ s'.core.cur_level = 0) →
      (r = 10#64 → s'.scratch.extend_len ≤ c.extend_cap) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m') :
    m7LuckyLateSpec (c.hdr, ()) m Q X :=
  ⟨c, F0, s, R, rfl, hsp, hm, hQ⟩

theorem m7LuckyLateSpec_elim {a m Q X} (hs : m7LuckyLateSpec a m Q X) :
    ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
      a.1 = c.hdr ∧ FullSparseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
      ∀ r s' m',
        s'.LengthsOk c → (r = 0#64 ∨ r = 2#64 ∨ r = 10#64 ∨ r = 20#64) →
        s'.core.fuel.toNat ≤ s.core.fuel.toNat → s'.core.probing = 0#64 →
        (r = 20#64 → F0.Unsat) →
        (r = 0#64 ∨ r = 2#64 → FullSparseInv c F0 s' ∧ s'.core.cur_level = 0) →
        (r = 10#64 → s'.scratch.extend_len ≤ c.extend_cap) →
        (FullMem c s' ⋆ R) m' → Q (r, ()) m' := by
  rcases a with ⟨h, ⟨⟩⟩; exact hs

theorem m7LuckyLateSpec_monoX {xs : Tup Val [i64]} {m : Mem 64} {Q : Post [i64]} {X X' : XPost}
    (h : m7LuckyLateSpec xs m Q X) : m7LuckyLateSpec xs m Q X' := h

theorem m7LuckyLateSpec_to_canon {a m Q X} (hc : Full.fullLuckySpec a m Q X) :
    m7LuckyLateSpec a m Q X := by
  rcases a with ⟨h, ⟨⟩⟩
  rcases hc with ⟨c, F0, s, R, rfl, hsp, _, hm, hQ⟩
  exact ⟨c, F0, s, R, rfl, hsp, hm, hQ⟩

theorem m7RandecStepSpec_of {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post []} {X : XPost} (hlen : s.LengthsOk c) (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ s' m', s'.core = s.core → s'.LengthsOk c → FullProbeScratchPres s s' →
      M7GuPrefixPres s s' → M7StateInitOk s'.scratch.glue_used →
      (∃ gu', s'.scratch = { s.scratch with glue_used := gu' }) →
      (FullMem c s' ⋆ R) m' → Q () m') :
    m7RandecStepSpec (c.hdr, ()) m Q X :=
  ⟨c, s, R, rfl, hlen, hm, fun ⟨⟩ _ _ hc hlen' ⟨h1, h2, h3, h4⟩ hm' =>
    hQ _ _ hc hlen' h1 h2 h3 h4 hm'⟩

theorem m7RandecStepSpec_monoX {xs : Tup Val [i64]} {m : Mem 64} {Q : Post []} {X X' : XPost}
    (h : m7RandecStepSpec xs m Q X) : m7RandecStepSpec xs m Q X' := h

theorem m7RandecVarSpec_of {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} (hlen : s.LengthsOk c) (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ (r : BitVec 64) s' m', s'.core = s.core → s'.LengthsOk c →
      FullProbeScratchPres s s' → M7GuPrefixPres s s' →
      (r = 0xFFFFFFFFFFFFFFFF#64 ∨
        (r.toNat < s.core.cur_vars ∧
          (s.core.flags[r.toNat]?.getD 0#32 &&& 1#32) ≠ 0#32 ∧
          s.core.vals[2 * r.toNat]?.getD 0#8 = 0#8)) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m') :
    m7RandecVarSpec (c.hdr, ()) m Q X :=
  ⟨c, s, R, rfl, hlen, hm, fun ⟨r, ⟨⟩⟩ _ _ hc hlen' ⟨hp, hg, hr⟩ hm' =>
    hQ r _ _ hc hlen' hp hg hr hm'⟩

theorem m7RandecVarSpec_monoX {xs : Tup Val [i64]} {m : Mem 64} {Q : Post [i64]} {X X' : XPost}
    (h : m7RandecVarSpec xs m Q X) : m7RandecVarSpec xs m Q X' := h

theorem m7RandecVarSpec_to_canon {a m Q X} (hc : Full.fullNextDecVarSpec a m Q X) :
    m7RandecVarSpec a m Q X := by
  rcases a with ⟨h, ⟨⟩⟩
  rcases hc with ⟨c, s, R, rfl, hlen, hm, hQ⟩
  exact ⟨c, s, R, rfl, hlen, hm, fun ⟨r, ⟨⟩⟩ s' _ hc hlen' ⟨hp, _, hr⟩ hm' =>
    hQ (r, ()) s' _ hc hlen' ⟨hp.1, hr.imp id fun h2 => ⟨h2.1, h2.2.2⟩⟩ hm'⟩

theorem m7DecideSpec_of {c : FullCfg} {F0 : CNF Nat} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} {Q : Post [i64]} {X : XPost} (hinv : FullCoreInv c F0 s)
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ r vals' flags' lvl' rsns' trl' tp' ftrl' fdec' te' cl' unass' unfl' sc' m',
      let s' : FullState :=
        { core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                                trl := trl', trail_pos := tp', frame_trail := ftrl',
                                frame_dec := fdec', trail_end := te', cur_level := cl',
                                unassigned := unass', unflushed := unfl' }
          scratch := sc' }
      FullCoreInv c F0 s' → FullExtScratchPres s s' →
      (r = 0#64 ∨ r = 1#64) →
      (r = 0#64 → cl' = s.core.cur_level ∧ te' = s.core.trail_end) →
      (r = 1#64 → cl' = s.core.cur_level + 1 ∧ te' = s.core.trail_end + 1 ∧
        s.core.trail_end < trl'.length ∧
        s.core.vals[(trl'[s.core.trail_end]?.getD 0#32).toNat]?.getD 0#8 = 0#8) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m') :
    m7DecideSpec (c.hdr, ()) m Q X :=
  ⟨c, F0, s, R, rfl, hinv, hm, hQ⟩

theorem m7DecideSpec_elim {a m Q X} (hs : m7DecideSpec a m Q X) :
    ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
      a.1 = c.hdr ∧ FullCoreInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
      ∀ r vals' flags' lvl' rsns' trl' tp' ftrl' fdec' te' cl' unass' unfl' sc' m',
        let s' : FullState :=
          { core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                                  trl := trl', trail_pos := tp', frame_trail := ftrl',
                                  frame_dec := fdec', trail_end := te', cur_level := cl',
                                  unassigned := unass', unflushed := unfl' }
            scratch := sc' }
        FullCoreInv c F0 s' → FullExtScratchPres s s' →
        (r = 0#64 ∨ r = 1#64) →
        (r = 0#64 → cl' = s.core.cur_level ∧ te' = s.core.trail_end) →
        (r = 1#64 → cl' = s.core.cur_level + 1 ∧ te' = s.core.trail_end + 1 ∧
          s.core.trail_end < trl'.length ∧
          s.core.vals[(trl'[s.core.trail_end]?.getD 0#32).toNat]?.getD 0#8 = 0#8) →
        (FullMem c s' ⋆ R) m' → Q (r, ()) m' := by
  rcases a with ⟨h, ⟨⟩⟩; exact hs

theorem m7DecideSpec_monoX {xs : Tup Val [i64]} {m : Mem 64} {Q : Post [i64]} {X X' : XPost}
    (h : m7DecideSpec xs m Q X) : m7DecideSpec xs m Q X' := h

theorem m7DecideSpec_to_canon {a m Q X} (hc : Full.fullDecideSpec a m Q X) :
    m7DecideSpec a m Q X := by
  rcases a with ⟨h, ⟨⟩⟩
  rcases hc with ⟨c, F0, s, R, rfl, hinv, hm, hQ⟩
  exact ⟨c, F0, s, R, rfl, hinv, hm, fun r vals' flags' lvl' rsns' trl' tp' ftrl' fdec' te' cl'
      unass' unfl' sc' m' hinv' hps hr h0 h1 hm' =>
    hQ r vals' flags' lvl' rsns' trl' tp' ftrl' fdec' te' cl' unass' unfl' sc' m' hinv' hps hr h0
      (fun h => ⟨(h1 h).1, (h1 h).2.1⟩) hm'⟩

theorem m7EmaSwapSpec_of {c : FullCfg} {old_m new_m : BitVec 64} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post []} {X : XPost} (hlen : s.LengthsOk c)
    (hm : (FullMem c s ⋆ R) m)
    (hQ : let s' : FullState := { s with scratch := m7EmaSwapSc s.scratch old_m new_m }
          s'.LengthsOk c → M7GuPrefixPres s s' → M7StateInitOk s'.scratch.glue_used →
          ∀ m', (FullMem c s' ⋆ R) m' → Q () m') :
    m7EmaSwapSpec (c.hdr, old_m, new_m, ()) m Q X :=
  ⟨c, s, R, rfl, hlen, hm, hQ⟩

theorem m7EmaSwapSpec_monoX {xs : Tup Val [i64, i64, i64]} {m : Mem 64} {Q : Post []}
    {X X' : XPost} (h : m7EmaSwapSpec xs m Q X) : m7EmaSwapSpec xs m Q X' := h

theorem m7SwitchModeSpec_of {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post []} {X : XPost} (hlen : s.LengthsOk c) (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ s' m',
      s'.core = s.core → s'.LengthsOk c → FullProbeScratchPres s s' →
      ((s.scratch.stable = 0#64 ∧ s.scratch.conflicts < s.scratch.mode_confl_lim) ∨
       (s.scratch.stable ≠ 0#64 ∧ s.scratch.search_ticks < s.scratch.mode_tick_lim) → s' = s) →
      (s.scratch.stable = 0#64 ∧ s.scratch.mode_confl_lim ≤ s.scratch.conflicts →
        M7StateInitOk s'.scratch.glue_used ∧ s'.scratch.stable = 1#64) →
      (s.scratch.stable ≠ 0#64 ∧ s.scratch.mode_tick_lim ≤ s.scratch.search_ticks →
        M7GuPrefixPres s s' ∧ M7StateInitOk s'.scratch.glue_used ∧
        m7ModeEmaGet s'.scratch.glue_used 1 =
          (s.scratch.ema_fast_biased, s.scratch.ema_fast_exp,
           s.scratch.ema_slow_biased, s.scratch.ema_slow_exp) ∧
        s'.scratch.stable = 0#64 ∧
        ((m7Get64Val s.scratch.glue_used m7GuMagicIdx = m7SearchMagic ∧
          (m7Get64Val s.scratch.glue_used m7GuEmaMaskIdx &&& 1#64) ≠ 0#64) →
         let saved := m7ModeEmaGet s.scratch.glue_used 0
         s'.scratch.ema_fast_biased = saved.1 ∧ s'.scratch.ema_fast_exp = saved.2.1 ∧
         s'.scratch.ema_slow_biased = saved.2.2.1 ∧ s'.scratch.ema_slow_exp = saved.2.2.2)) →
      (FullMem c s' ⋆ R) m' → Q () m') :
    m7SwitchModeSpec (c.hdr, ()) m Q X :=
  ⟨c, s, R, rfl, hlen, hm, hQ⟩

theorem m7SwitchModeSpec_elim {a m Q X} (hs : m7SwitchModeSpec a m Q X) :
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      a.1 = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
      ∀ s' m',
        s'.core = s.core → s'.LengthsOk c → FullProbeScratchPres s s' →
        ((s.scratch.stable = 0#64 ∧ s.scratch.conflicts < s.scratch.mode_confl_lim) ∨
         (s.scratch.stable ≠ 0#64 ∧ s.scratch.search_ticks < s.scratch.mode_tick_lim) → s' = s) →
        (s.scratch.stable = 0#64 ∧ s.scratch.mode_confl_lim ≤ s.scratch.conflicts →
          M7StateInitOk s'.scratch.glue_used ∧ s'.scratch.stable = 1#64) →
        (s.scratch.stable ≠ 0#64 ∧ s.scratch.mode_tick_lim ≤ s.scratch.search_ticks →
          M7GuPrefixPres s s' ∧ M7StateInitOk s'.scratch.glue_used ∧
          m7ModeEmaGet s'.scratch.glue_used 1 =
            (s.scratch.ema_fast_biased, s.scratch.ema_fast_exp,
             s.scratch.ema_slow_biased, s.scratch.ema_slow_exp) ∧
          s'.scratch.stable = 0#64 ∧
          ((m7Get64Val s.scratch.glue_used m7GuMagicIdx = m7SearchMagic ∧
            (m7Get64Val s.scratch.glue_used m7GuEmaMaskIdx &&& 1#64) ≠ 0#64) →
           let saved := m7ModeEmaGet s.scratch.glue_used 0
           s'.scratch.ema_fast_biased = saved.1 ∧ s'.scratch.ema_fast_exp = saved.2.1 ∧
           s'.scratch.ema_slow_biased = saved.2.2.1 ∧ s'.scratch.ema_slow_exp = saved.2.2.2)) →
        (FullMem c s' ⋆ R) m' → Q () m' := by
  rcases a with ⟨h, ⟨⟩⟩; exact hs

theorem m7SwitchModeSpec_monoX {xs : Tup Val [i64]} {m : Mem 64} {Q : Post []} {X X' : XPost}
    (h : m7SwitchModeSpec xs m Q X) : m7SwitchModeSpec xs m Q X' := h

theorem m7SwitchModeSpec_to_canon {a m Q X} (hc : Full.fullSwitchModeSpec a m Q X) :
    m7SwitchModeSpec a m Q X := by
  rcases a with ⟨h, ⟨⟩⟩
  rcases hc with ⟨c, s, R, rfl, hlen, hm, hQ⟩
  exact ⟨c, s, R, rfl, hlen, hm, fun s' m' hc hlen' hps _ _ _ hm' =>
    hQ () s' m' hc hlen' hps hm'⟩

/-! ## 5. Group-A `Func.wp` Proofs (`5` Helpers) -/

private theorem m7_ite_lt63 {α : Type} {idx : BitVec 64} (h : idx.toNat < 63) (a b : α) :
    (if idx.toNat < 63 then a else b) = a := by simp [h]

private theorem lengthsOk_set_rng {c : FullCfg} {s : FullState} (h : s.LengthsOk c)
    (r : BitVec 64) :
    ({ s with scratch := { s.scratch with rng_state := r } } : FullState).LengthsOk c :=
  ⟨h.core_ok,
    ⟨h.scratch_ok.walk_vals_len, h.scratch_ok.phases_len, h.scratch_ok.phases_target_len,
     h.scratch_ok.phases_best_len, h.scratch_ok.walk_best_len, h.scratch_ok.heap_len_arr,
     h.scratch_ok.pos_len, h.scratch_ok.shrink_stk_len, h.scratch_ok.q_prev_len,
     h.scratch_ok.q_next_len, h.scratch_ok.q_stamp_len, h.scratch_ok.wsort_len,
     h.scratch_ok.work_stk1_len, h.scratch_ok.work_stk2_len, h.scratch_ok.tarjan_mark_len,
     h.scratch_ok.tarjan_reach_len, h.scratch_ok.score_len, h.scratch_ok.sim_sig_len,
     h.scratch_ok.glue_used_len, h.scratch_ok.last_learned_len, h.scratch_ok.delayed_len_arr,
     h.scratch_ok.red_refs_len, h.scratch_ok.extend_stk_len, h.scratch_ok.scratch_buf_len⟩⟩

theorem full_lcg_next_m7_wp (Γ : Env) :
    ∀ a m Q X, m7LcgNextSpec a m Q X → Func.wp Γ full_lcg_next_m7_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  change FullState.LengthsOk c s at hlen
  change (FullMem c s ⋆ R) m at hm
  unfold Func.wp full_lcg_next_m7_body
  m7_steps
  let x' := s.scratch.rng_state * m7LcgMul + m7LcgInc
  let s' : FullState := { s with scratch := { s.scratch with rng_state := x' } }
  have hlen' : s'.LengthsOk c := lengthsOk_set_rng hlen x'
  exact hQ (_, ()) s' _ rfl hlen' ⟨rfl, rfl⟩ (by assumption)

theorem full_m7_get64_wp (Γ : Env) :
    ∀ a m Q X, m7Get64Spec a m Q X → Func.wp Γ full_m7_get64_body a m Q X := by
  rintro ⟨h, idx, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  have hgul : s.scratch.glue_used.length = 64 := hlen.scratch_ok.glue_used_len
  unfold Func.wp full_m7_get64_body
  m7_split
  · have hge : ¬ idx.toNat < 63 := by c0_bound
    m7_steps; simp only [hge, ↓reduceIte] at hQ; exact hQ
  · have hlt : idx.toNat < 63 := by c0_bound
    have hadd : (idx + 1#64).toNat = idx.toNat + 1 := bv64_add1_toNat (by omega)
    have h0 : idx.toNat < s.scratch.glue_used.length := by omega
    have h1 : (idx + 1#64).toNat < s.scratch.glue_used.length := by rw [hadd]; omega
    have h1' : idx.toNat + 1 < s.scratch.glue_used.length := by omega
    m7_steps
    rw [m7_ite_lt63 hlt] at hQ
    have helem :
        s.scratch.glue_used[(idx + 1#64).toNat]'h1 = s.scratch.glue_used[idx.toNat + 1]'h1' :=
      Option.some.inj (by
        rw [← List.getElem?_eq_getElem h1, ← List.getElem?_eq_getElem h1', hadd])
    have heq : ((s.scratch.glue_used[idx.toNat]'h0).setWidth 64 |||
        ((s.scratch.glue_used[(idx + 1#64).toNat]'h1).setWidth 64 <<< 32)) =
        m7Get64Val s.scratch.glue_used idx.toNat := by
      unfold m7Get64Val
      rw [helem, List.getElem?_eq_getElem h0, List.getElem?_eq_getElem h1']
      rfl
    have h1_bv : (idx + 1 : BitVec 64) = idx + 1#64 := rfl
    change Q (((s.scratch.glue_used[idx.toNat]'h0).setWidth 64 |||
      ((s.scratch.glue_used[(idx + 1#64).toNat]'h1).setWidth 64 <<< 32)), ()) m
    rw [heq]
    exact hQ

theorem full_m7_set64_wp (Γ : Env) :
    ∀ a m Q X, m7Set64Spec a m Q X → Func.wp Γ full_m7_set64_body a m Q X := by
  rintro ⟨h, idx, val, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  have hgul : s.scratch.glue_used.length = 64 := hlen.scratch_ok.glue_used_len
  unfold Func.wp full_m7_set64_body
  m7_split
  · have hge : ¬ idx.toNat < 63 := by c0_bound
    m7_steps; simp only [hge, ↓reduceIte] at hQ; exact hQ hlen m hm
  · have hlt : idx.toNat < 63 := by c0_bound
    have hadd : (idx + 1#64).toNat = idx.toNat + 1 := bv64_add1_toNat (by omega)
    have h0 : idx.toNat < s.scratch.glue_used.length := by omega
    have h1_len :
        (s.scratch.glue_used.set idx.toNat (val.setWidth 32)).length = 64 := by
      rw [List.length_set, hgul]
    have h1 : (idx + 1#64).toNat <
        (s.scratch.glue_used.set idx.toNat (val.setWidth 32)).length := by
      rw [h1_len, hadd]; omega
    m7_steps
    have hsh : val >>> 32#64 = val >>> (32 : Nat) := rfl
    have heq : ((s.scratch.glue_used.set idx.toNat (val.setWidth 32)).set (idx + 1#64).toNat
        ((val >>> (32 : Nat)).setWidth 32)) = m7Set64List s.scratch.glue_used idx.toNat val := by
      unfold m7Set64List; rw [hadd]
    have hlen' : ({ s with scratch := { s.scratch with
        glue_used := m7Set64List s.scratch.glue_used idx.toNat val } } : FullState).LengthsOk
          c :=
      hlen.with_scratch {
        hlen.scratch_ok with
        glue_used_len := by rw [m7Set64List_length, hgul] }
    simp only [hlt, ↓reduceIte] at hQ
    refine hQ hlen' _ ?_
    rw [← heq]
    try rw [← hsh]
    assumption

local macro "m7_step_set64" hs:term "," hm:term "," hSet:ident ","
    hs':ident "," m':ident "," hm':ident : tactic =>
  `(tactic| (
    m7_to_group
    m7_call $hSet
    refine m7Set64Spec_of $hs $hm ?_
    dsimp only
    rw [m7_ite_lt63]; case h => dsimp only [Arg.val]; decide
    intro $hs':ident $m':ident $hm':ident
    dsimp only [Arg.val] at $hs':ident $hm':ident))

private theorem m7_len_gu_congr {c : FullCfg} {s : FullState} {g1 g2 : List (BitVec 32)}
    (heq : g1 = g2)
    (h : ({ s with scratch := { s.scratch with glue_used := g1 } } : FullState).LengthsOk c) :
    ({ s with scratch := { s.scratch with glue_used := g2 } } : FullState).LengthsOk c := by
  subst heq; exact h

private theorem m7_mem_gu_congr {c : FullCfg} {s : FullState} {g1 g2 : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64} (heq : g1 = g2)
    (h : (FullMem c { s with scratch := { s.scratch with glue_used := g1 } } ⋆ R) m) :
    (FullMem c { s with scratch := { s.scratch with glue_used := g2 } } ⋆ R) m := by
  subst heq; exact h

theorem full_m7_state_init_wp (Γ : Env)
    (hGet : EnvSpec Γ "full_m7_get64" m7Get64Spec)
    (hSet : EnvSpec Γ "full_m7_set64" m7Set64Spec) :
    ∀ a m Q X, m7StateInitSpec a m Q X → Func.wp Γ full_m7_state_init_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  have hgul : s.scratch.glue_used.length = 64 := hlen.scratch_ok.glue_used_len
  unfold Func.wp full_m7_state_init_body
  m7_to_group; m7_call hGet
  refine m7Get64Spec_of hlen hm ?_
  rw [m7_ite_lt63]; case h => dsimp only [Arg.val]; decide
  m7_split
  · m7_steps
    have hm_eq : m7Get64Val s.scratch.glue_used m7GuMagicIdx = m7SearchMagic := by assumption
    have hgu_eq : m7StateInitGu s.scratch = s.scratch.glue_used := m7StateInitGu_of_magic hm_eq
    have hi : M7StateInitOk s.scratch.glue_used := ⟨hgul, hm_eq⟩
    simp only [hgu_eq] at hQ
    exact hQ hlen hi (M7GuPrefixPres.refl s) m hm
  · have hneq_mag : m7Get64Val s.scratch.glue_used m7GuMagicIdx ≠ m7SearchMagic := by assumption
    m7_step_set64 hlen, hm, hSet, hlen0, m0, hm0
    m7_to_group
    refine wp_join_group (ts := [i64]) (fun (cm, ()) m1 => m1 = m0 ∧
        (cm = 0#64 ∧ s.scratch.stable = 0#64 ∨ cm = 1#64 ∧ s.scratch.stable ≠ 0#64)) ?_ ?_
    · rintro _ ⟨cm, ⟨⟩⟩ m1 ⟨rfl, hcm⟩
      m7_step_set64 hlen0, hm0, hSet, hlen1, m1, hm1
      let g0_base := m7Set64List (m7Set64List s.scratch.glue_used m7GuMagicIdx m7SearchMagic)
        m7GuEmaMaskIdx (1#64 <<< (if s.scratch.stable ≠ 0#64 then 1 else 0))
      have hlen1' : ({ s with scratch := { s.scratch with
          glue_used := g0_base } } : FullState).LengthsOk c :=
        m7_len_gu_congr (by
          dsimp only [g0_base, m7GuMagicIdx, m7GuEmaMaskIdx]
          rcases hcm with ⟨rfl, hst⟩ | ⟨rfl, hst⟩ <;> simp [hst] <;> rfl) hlen1
      have hm1' : (FullMem c { s with scratch := { s.scratch with
          glue_used := g0_base } } ⋆ R) m1 :=
        m7_mem_gu_congr (by
          dsimp only [g0_base, m7GuMagicIdx, m7GuEmaMaskIdx]
          rcases hcm with ⟨rfl, hst⟩ | ⟨rfl, hst⟩ <;> simp [hst] <;> rfl) hm1
      let g_mid :=
        if s.scratch.stable = 0#64 then
          m7Set64List (m7Set64List (m7Set64List (m7Set64List (m7Set64List (m7Set64List
            (m7Set64List (m7Set64List g0_base m7GuEma0FbIdx s.scratch.ema_fast_biased)
              m7GuEma0FeIdx s.scratch.ema_fast_exp)
              m7GuEma0SbIdx s.scratch.ema_slow_biased)
              m7GuEma0SeIdx s.scratch.ema_slow_exp)
              m7GuEma1FbIdx 0#64) m7GuEma1FeIdx m7EmaInitExp)
              m7GuEma1SbIdx 0#64) m7GuEma1SeIdx m7EmaInitExp
        else
          m7Set64List (m7Set64List (m7Set64List (m7Set64List (m7Set64List (m7Set64List
            (m7Set64List (m7Set64List g0_base m7GuEma1FbIdx s.scratch.ema_fast_biased)
              m7GuEma1FeIdx s.scratch.ema_fast_exp)
              m7GuEma1SbIdx s.scratch.ema_slow_biased)
              m7GuEma1SeIdx s.scratch.ema_slow_exp)
              m7GuEma0FbIdx 0#64) m7GuEma0FeIdx m7EmaInitExp)
              m7GuEma0SbIdx 0#64) m7GuEma0SeIdx m7EmaInitExp
      let s_mid : FullState := { s with scratch := { s.scratch with glue_used := g_mid } }
      m7_to_group
      refine wp_join_group (ts := []) (fun _ m_mid =>
          s_mid.LengthsOk c ∧ (FullMem c s_mid ⋆ R) m_mid) ?_ ?_
      · rintro _ ⟨⟩ m_mid ⟨hsm_ok, hm_mid⟩
        m7_steps; m7_step_set64 hsm_ok, hm_mid, hSet, h3, m3, hm3
        m7_step_set64 h3, hm3, hSet, h4, m4, hm4
        m7_step_set64 h4, hm4, hSet, h5, m5, hm5
        m7_steps; m7_step_set64 h5, hm5, hSet, h6, m6, hm6
        m7_steps
        have hpref : M7GuPrefixPres s
            { s with scratch := { s.scratch with glue_used := m7StateInitGu s.scratch } } :=
          fun _ hk => m7StateInitGu_prefix s.scratch hk
        have hinit := m7StateInitGu_initOk hgul
        refine hQ (m7_len_gu_congr ?_ h6) hinit hpref m6 (m7_mem_gu_congr ?_ hm6) <;>
        · rw [show BitVec.toNat (56 : BitVec 64) = m7GuRandecRemIdx by decide,
            show BitVec.toNat (58 : BitVec 64) = m7GuRandecLimIdx by decide,
            show BitVec.toNat (60 : BitVec 64) = m7GuRandecSeqIdx by decide,
            show BitVec.toNat (62 : BitVec 64) = m7GuRandecConflIdx by decide,
            show (500 : BitVec 64) = BitVec.ofNat 64 m7RandecInitLim by decide,
            show (0 : BitVec 64) = 0#64 by rfl]
          dsimp only [s_mid, g_mid, g0_base]
          unfold m7StateInitGu
          simp only [hneq_mag, ↓reduceIte]
          by_cases hst : s.scratch.stable = 0#64
          · simp [hst]
          · simp [hst]
      · intro _ hJ
        rcases hcm with ⟨rfl, hst0⟩ | ⟨rfl, hst1⟩
        · m7_split
          · m7_steps; m7_step_set64 hlen1', hm1', hSet, h2, m2, hm2
            m7_steps; m7_step_set64 h2, hm2, hSet, h3, m3, hm3
            m7_steps; m7_step_set64 h3, hm3, hSet, h4, m4, hm4
            m7_steps; m7_step_set64 h4, hm4, hSet, h5, m5, hm5
            m7_steps; m7_step_set64 h5, hm5, hSet, h6, m6, hm6
            m7_steps; m7_step_set64 h6, hm6, hSet, h7, m7, hm7
            m7_steps; m7_step_set64 h7, hm7, hSet, h8, m8, hm8
            m7_steps; m7_step_set64 h8, hm8, hSet, h9, m9, hm9
            m7_steps
            refine hJ () m9 ⟨m7_len_gu_congr ?_ h9, m7_mem_gu_congr ?_ hm9⟩ <;>
            · rw [show BitVec.toNat (40 : BitVec 64) = m7GuEma0FbIdx by decide,
                show BitVec.toNat (42 : BitVec 64) = m7GuEma0FeIdx by decide,
                show BitVec.toNat (44 : BitVec 64) = m7GuEma0SbIdx by decide,
                show BitVec.toNat (46 : BitVec 64) = m7GuEma0SeIdx by decide,
                show BitVec.toNat (48 : BitVec 64) = m7GuEma1FbIdx by decide,
                show BitVec.toNat (50 : BitVec 64) = m7GuEma1FeIdx by decide,
                show BitVec.toNat (52 : BitVec 64) = m7GuEma1SbIdx by decide,
                show BitVec.toNat (54 : BitVec 64) = m7GuEma1SeIdx by decide,
                show ((1 : BitVec 64) <<< 32) = m7EmaInitExp by decide,
                show (0 : BitVec 64) = 0#64 by rfl]
              simp only [g_mid, hst0, ↓reduceIte]
          · exfalso; exact absurd ‹_› (by decide)
        · m7_split
          · exfalso; exact absurd ‹_› (by decide)
          · m7_steps; m7_step_set64 hlen1', hm1', hSet, h2, m2, hm2
            m7_steps; m7_step_set64 h2, hm2, hSet, h3, m3, hm3
            m7_steps; m7_step_set64 h3, hm3, hSet, h4, m4, hm4
            m7_steps; m7_step_set64 h4, hm4, hSet, h5, m5, hm5
            m7_steps; m7_step_set64 h5, hm5, hSet, h6, m6, hm6
            m7_steps; m7_step_set64 h6, hm6, hSet, h7, m7, hm7
            m7_steps; m7_step_set64 h7, hm7, hSet, h8, m8, hm8
            m7_steps; m7_step_set64 h8, hm8, hSet, h9, m9, hm9
            m7_steps
            refine hJ () m9 ⟨m7_len_gu_congr ?_ h9, m7_mem_gu_congr ?_ hm9⟩ <;>
            · rw [show BitVec.toNat (40 : BitVec 64) = m7GuEma0FbIdx by decide,
                show BitVec.toNat (42 : BitVec 64) = m7GuEma0FeIdx by decide,
                show BitVec.toNat (44 : BitVec 64) = m7GuEma0SbIdx by decide,
                show BitVec.toNat (46 : BitVec 64) = m7GuEma0SeIdx by decide,
                show BitVec.toNat (48 : BitVec 64) = m7GuEma1FbIdx by decide,
                show BitVec.toNat (50 : BitVec 64) = m7GuEma1FeIdx by decide,
                show BitVec.toNat (52 : BitVec 64) = m7GuEma1SbIdx by decide,
                show BitVec.toNat (54 : BitVec 64) = m7GuEma1SeIdx by decide,
                show ((1 : BitVec 64) <<< 32) = m7EmaInitExp by decide,
                show (0 : BitVec 64) = 0#64 by rfl]
              simp only [g_mid, hst1, ↓reduceIte]
    · intro _ hJcm; m7_steps
      · exact hJcm (1#64, ()) m0 ⟨rfl, Or.inr ⟨rfl, by assumption⟩⟩
      · exact hJcm (0#64, ()) m0 ⟨rfl, Or.inl ⟨rfl, by assumption⟩⟩

private theorem pow10_lt_64 {d : Nat} (hd : d ≤ 19) : 10 ^ d < 2 ^ 64 :=
  Nat.lt_of_le_of_lt (Nat.pow_le_pow_right (by omega) hd) (by decide)

theorem full_log10_q16_m7_wp (Γ : Env) :
    ∀ a m Q X, m7Log10Q16Spec a m Q X → Func.wp Γ full_log10_q16_m7_body a m Q X := by
  rintro ⟨x, ⟨⟩⟩ m Q X hQ
  unfold Func.wp full_log10_q16_m7_body
  m7_to_group
  · have hx1 : x.toNat ≤ 1 := by c0_bound
    exact hQ 0#64 (by decide) (fun hx10 => by omega)
  · refine wp_loop_inv (ts := [i64, i64])
      (fun (d, pow10, ()) m1 =>
        m = m1 ∧ d.toNat ≤ 19 ∧ 1 ≤ pow10.toNat ∧ pow10.toNat ≤ 10 ^ d.toNat ∧
        (d.toNat = 0 → pow10.toNat = 1))
      (fun (d, _, ()) _ => 19 - d.toNat) ?_ ?_
    · intro J hJ
      m7_to_group; exact hJ (0#64, 1#64, ()) m ⟨rfl, by decide, by decide, by decide, fun _ => rfl⟩
    · rintro J ⟨d, pow10, ⟨⟩⟩ _ ⟨rfl, hd19, hp1, hple, hd0p⟩ hJ
      refine wp_join_group (ts := []) (fun _ m1 => m = m1 ∧ (10 ≤ x.toNat → 1 ≤ d.toNat))
        ?_ ?_
      · rintro _ ⟨⟩ _ ⟨rfl, hd10⟩
        m7_to_group
        refine wp_join_group (ts := [i64, i64]) (fun (_, pm', ()) m2 => m = m2 ∧ 1 ≤ pm'.toNat)
          ?_ ?_
        · rintro _ ⟨xm', pm', ⟨⟩⟩ m2 ⟨hm2, hpm⟩
          subst m2
          have hpm_ne : pm' ≠ 0#64 := fun h0 => by subst h0; simp at hpm
          m7_to_group
          all_goals try exact hpm_ne
          refine wp_loop_inv (ts := [i64, i64, i64])
            (fun (_mv, frac, i, ()) m3 => m = m3 ∧ i.toNat ≤ 16 ∧ frac.toNat < 2 ^ i.toNat)
            (fun (_, _, i, ()) _ => 16 - i.toNat) ?_ ?_
          · intro J2 hJ2; m7_to_group; exact hJ2 (_, 0#64, 0#64, ()) m ⟨rfl, by decide, by decide⟩
          · rintro J2 ⟨mv, frac, i, ⟨⟩⟩ m3 ⟨hm3, hi16, hfl⟩ hJ2
            subst m3; m7_steps
            · have hi_lt : i.toNat < 16 := by c0_bound
              have hf_lt : frac.toNat < 2 ^ 15 :=
                Nat.lt_of_lt_of_le hfl (Nat.pow_le_pow_right (by omega) (by omega))
              have hi1 : (i + 1#64).toNat = i.toNat + 1 := bv64_add1_toNat (by omega)
              have hf2p1 : (frac <<< (1 : Nat) + 1#64).toNat = 2 * frac.toNat + 1 := by bv_omega
              have hf2p1_lt : 2 * frac.toNat + 1 < 2 ^ (i.toNat + 1) := by
                rw [Nat.pow_succ]; omega
              exact hJ2 (_, (frac <<< (1 : Nat)) + 1#64, i + 1#64, ()) m
                (by dsimp only; omega) ⟨rfl, by omega, by rw [hi1, hf2p1]; exact hf2p1_lt⟩
            · have hi_lt : i.toNat < 16 := by c0_bound
              have hf_lt : frac.toNat < 2 ^ 15 :=
                Nat.lt_of_lt_of_le hfl (Nat.pow_le_pow_right (by omega) (by omega))
              have hf_sh : (frac <<< (1 : Nat)).toNat = 2 * frac.toNat := by
                rw [BitVec.toNat_shiftLeft]; simp [Nat.shiftLeft_eq]; omega
              have hf2_lt : 2 * frac.toNat < 2 ^ (i.toNat + 1) := by rw [Nat.pow_succ]; omega
              have hi1 : (i + 1#64).toNat = i.toNat + 1 := bv64_add1_toNat (by omega)
              exact hJ2 (_, frac <<< (1 : Nat), i + 1#64, ()) m (by dsimp only; omega)
                ⟨rfl, by omega, by rw [hi1, hf_sh]; exact hf2_lt⟩
            · have hflt : frac.toNat < 65536 :=
                Nat.lt_of_lt_of_le hfl (Nat.pow_le_pow_right (by omega) hi16)
              have hd_sh : (d <<< (16 : Nat)).toNat = d.toNat * 65536 := by
                rw [BitVec.toNat_shiftLeft]; simp [Nat.shiftLeft_eq]; omega
              have hres_lt : ((d <<< (16 : Nat)) + frac).toNat < 20 * 65536 := by
                have hsum : d.toNat * 65536 + frac.toNat < 20 * 65536 := by omega
                rw [BitVec.toNat_add, hd_sh, Nat.mod_eq_of_lt (by omega)]; exact hsum
              have hres_ge : 10 ≤ x.toNat → 65536 ≤ ((d <<< (16 : Nat)) + frac).toNat := by
                intro hx10; have hd1 := hd10 hx10
                have hsum : 65536 ≤ d.toNat * 65536 + frac.toNat := by omega
                rw [BitVec.toNat_add, hd_sh, Nat.mod_eq_of_lt (by omega)]; exact hsum
              exact hQ ((d <<< (16 : Nat)) + frac) hres_lt hres_ge
        · intro _ hJm; m7_to_group
          · have hpm_gt : 100000000 < pow10.toNat := by c0_bound
            intro h0; have ht := congrArg BitVec.toNat h0
            change pow10.toNat / 100000000 = 0 at ht
            have hpos : 0 < pow10.toNat / 100000000 :=
              Nat.div_pos (Nat.le_of_lt hpm_gt) (by decide)
            omega
          · exact hJm (x / (pow10 / 100000000#64), 100000000#64, ()) m ⟨rfl, by decide⟩
          · exact hJm (x, pow10, ()) m ⟨rfl, hp1⟩
      · intro _ hJexit; m7_to_group
        · have hd_lt : d.toNat < 19 := by c0_bound
          have hpow_10 : pow10.toNat * 10 ≤ 10 ^ (d.toNat + 1) := by
            rw [Nat.pow_succ]; exact Nat.mul_le_mul_right 10 hple
          have hpow_lt64 : pow10.toNat * 10 < 2 ^ 64 := Nat.lt_of_le_of_lt hpow_10
            (pow10_lt_64 (by omega))
          have hpow_mul : (pow10 * 10#64).toNat = pow10.toNat * 10 := by
            rw [BitVec.toNat_mul, show (10#64).toNat = 10 by rfl, Nat.mod_eq_of_lt hpow_lt64]
          have hd1 : (d + 1#64).toNat = d.toNat + 1 := bv64_add1_toNat (by omega)
          exact hJ (d + 1#64, pow10 * 10#64, ()) m (by dsimp only; omega)
            ⟨rfl, by omega, by omega, by rw [hd1, hpow_mul]; exact hpow_10,
             fun h0 => by rw [hd1] at h0; omega⟩
        · have hge : 19 ≤ d.toNat := by c0_bound
          exact hJexit () m ⟨rfl, fun _ => by omega⟩
        · have hlt : x.toNat / 10 < pow10.toNat := by
            have hdiv : (x / 10#64).toNat < pow10.toNat := by c0_bound
            have hmod : (x / 10#64).toNat = x.toNat / 10 := by bv_omega
            omega
          refine hJexit () m ⟨rfl, fun hx10 => ?_⟩
          rcases Nat.eq_zero_or_pos d.toNat with hd0 | hdpos
          · have hp1' := hd0p hd0; omega
          · exact hdpos

theorem m7RandecStepSpec_elim {h : Val i64} {m : Mem 64} {Q : Post []} {X : XPost}
    (hs : m7RandecStepSpec (h, ()) m Q X) :
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
      ∀ s' m', PreservesCoreSlice (fullSafetySlice c).coreProj s s' → s'.LengthsOk c →
        (FullProbeScratchPres s s' ∧ M7GuPrefixPres s s' ∧ M7StateInitOk s'.scratch.glue_used ∧
          ∃ gu', s'.scratch = { s.scratch with glue_used := gu' }) →
        (FullMem c s' ⋆ R) m' → Q () m' := by
  rcases hs with ⟨c, s, R, hpre, hlen, hm, hQ⟩
  exact ⟨c, s, R, hpre, hlen, hm, fun s' m' hc hl hp hm' => hQ () s' m' hc hl hp hm'⟩

theorem m7EmaSwapSpec_elim {h old_m new_m : Val i64} {m : Mem 64} {Q : Post []} {X : XPost}
    (hs : m7EmaSwapSpec (h, old_m, new_m, ()) m Q X) :
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
      (let s' : FullState := { core := s.core, scratch := m7EmaSwapSc s.scratch old_m new_m }
       s'.LengthsOk c → M7GuPrefixPres s s' → M7StateInitOk s'.scratch.glue_used →
       ∀ m', (FullMem c s' ⋆ R) m' → Q () m') := hs

theorem M7StateInitOk.of_set64 {gu : List (BitVec 32)} (h : M7StateInitOk gu)
    {idx : Nat} (hidx : 38 ≤ idx) (val : BitVec 64) :
    M7StateInitOk (m7Set64List gu idx val) := by
  refine ⟨by rw [m7Set64List_length]; exact h.len, ?_⟩
  change m7Get64Val (m7Set64List gu idx val) m7GuMagicIdx = m7SearchMagic
  rw [m7Get64Val_set64_ne val (by dsimp only [m7GuMagicIdx]; omega)]
  exact h.magic

theorem M7GuPrefixPres.of_forall {s s' : FullState}
    (h : ∀ k : Nat, k < 36 → s'.scratch.glue_used[k]? = s.scratch.glue_used[k]?) :
    M7GuPrefixPres s s' := h

theorem M7GuPrefixPres.elim {s s' : FullState} (h : M7GuPrefixPres s s')
    {k : Nat} (hk : k < 36) : s'.scratch.glue_used[k]? = s.scratch.glue_used[k]? := h k hk

theorem M7GuPrefixPres.congr_glue {s₁ s₁' s₂ s₂' : FullState}
    (h1 : s₂.scratch.glue_used = s₁.scratch.glue_used)
    (h2 : s₂'.scratch.glue_used = s₁'.scratch.glue_used)
    (h : M7GuPrefixPres s₁ s₁') : M7GuPrefixPres s₂ s₂' := by
  intro k hk; rw [h2, h1]; exact h k hk

theorem M7StateInitOk.of_fields {gu : List (BitVec 32)}
    (hlen : gu.length = 64) (hmag : m7Get64Val gu m7GuMagicIdx = m7SearchMagic) :
    M7StateInitOk gu := ⟨hlen, hmag⟩

theorem m7GuMagicIdx_eq : m7GuMagicIdx = 36 := rfl
theorem m7GuEmaMaskIdx_eq : m7GuEmaMaskIdx = 38 := rfl
theorem m7GuEma0FbIdx_eq : m7GuEma0FbIdx = 40 := rfl
theorem m7GuEma0FeIdx_eq : m7GuEma0FeIdx = 42 := rfl
theorem m7GuEma0SbIdx_eq : m7GuEma0SbIdx = 44 := rfl
theorem m7GuEma0SeIdx_eq : m7GuEma0SeIdx = 46 := rfl
theorem m7GuEma1FbIdx_eq : m7GuEma1FbIdx = 48 := rfl
theorem m7GuEma1FeIdx_eq : m7GuEma1FeIdx = 50 := rfl
theorem m7GuEma1SbIdx_eq : m7GuEma1SbIdx = 52 := rfl
theorem m7GuEma1SeIdx_eq : m7GuEma1SeIdx = 54 := rfl
theorem m7GuRandecRemIdx_eq : m7GuRandecRemIdx = 56 := rfl
theorem m7GuRandecLimIdx_eq : m7GuRandecLimIdx = 58 := rfl
theorem m7GuRandecSeqIdx_eq : m7GuRandecSeqIdx = 60 := rfl
theorem m7GuRandecConflIdx_eq : m7GuRandecConflIdx = 62 := rfl
theorem m7RandecLen_eq : m7RandecLen = 10 := rfl
theorem m7RandecInitLim_eq : m7RandecInitLim = 500 := rfl
theorem m7SearchMagic_eq : m7SearchMagic = 0x4D37534541524348#64 := rfl
theorem m7EmaInitExp_eq : m7EmaInitExp = 4294967296#64 := rfl
theorem m7LcgMul_eq : m7LcgMul = 6364136223846793005#64 := rfl
theorem m7LcgInc_eq : m7LcgInc = 1442695040888963407#64 := rfl

theorem m7Get64Val_eq (gu : List (BitVec 32)) (idx : Nat) :
    m7Get64Val gu idx =
      (gu[idx]?.getD 0#32).setWidth 64 |||
        ((gu[idx + 1]?.getD 0#32).setWidth 64 <<< (32 : Nat)) := by
  unfold m7Get64Val; rfl

theorem m7Set64List_eq (gu : List (BitVec 32)) (idx : Nat) (val : BitVec 64) :
    m7Set64List gu idx val =
      (gu.set idx (val.setWidth 32)).set (idx + 1) ((val >>> (32 : Nat)).setWidth 32) := by
  unfold m7Set64List; rfl

theorem m7ModeEmaGet_eq (gu : List (BitVec 32)) (mode : Nat) :
    m7ModeEmaGet gu mode =
      let base := if mode = 0 then m7GuEma0FbIdx else m7GuEma1FbIdx
      (m7Get64Val gu base, m7Get64Val gu (base + 2),
        m7Get64Val gu (base + 4), m7Get64Val gu (base + 6)) := by
  unfold m7ModeEmaGet; rfl

theorem m7ModeEmaSet_eq (gu : List (BitVec 32)) (mode : Nat)
    (v : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64) :
    m7ModeEmaSet gu mode v =
      let base := if mode = 0 then m7GuEma0FbIdx else m7GuEma1FbIdx
      m7Set64List (m7Set64List (m7Set64List (m7Set64List gu base v.1) (base + 2) v.2.1)
        (base + 4) v.2.2.1) (base + 6) v.2.2.2 := by
  unfold m7ModeEmaSet; rfl

theorem m7EmaSwapSc_eq (sc : FullScratch) (old_m new_m : BitVec 64) :
    m7EmaSwapSc sc old_m new_m =
      let om := if old_m ≠ 0#64 then 1 else 0
      let nm := if new_m ≠ 0#64 then 1 else 0
      let gu0 := m7StateInitGu { sc with stable := BitVec.ofNat 64 om }
      let curV := (sc.ema_fast_biased, sc.ema_fast_exp, sc.ema_slow_biased, sc.ema_slow_exp)
      let gu1 := m7ModeEmaSet gu0 om curV
      let mask := m7Get64Val gu1 m7GuEmaMaskIdx ||| (1#64 <<< om)
      let bit := 1#64 <<< nm
      if mask &&& bit ≠ 0#64 then
        let nw := m7ModeEmaGet gu1 nm
        let gu2 := m7Set64List gu1 m7GuEmaMaskIdx mask
        { sc with
          stable := BitVec.ofNat 64 nm
          ema_fast_biased := nw.1
          ema_fast_exp := nw.2.1
          ema_slow_biased := nw.2.2.1
          ema_slow_exp := nw.2.2.2
          glue_used := gu2 }
      else
        let initV := (0#64, m7EmaInitExp, 0#64, m7EmaInitExp)
        let gu2 := m7ModeEmaSet gu1 nm initV
        let gu3 := m7Set64List gu2 m7GuEmaMaskIdx (mask ||| bit)
        { sc with
          stable := BitVec.ofNat 64 nm
          ema_fast_biased := 0#64
          ema_fast_exp := m7EmaInitExp
          ema_slow_biased := 0#64
          ema_slow_exp := m7EmaInitExp
          glue_used := gu3 } := by
  unfold m7EmaSwapSc m7FlagNat; rfl

theorem m7RandecVarSpec_elim {h : Val i64} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hs : m7RandecVarSpec (h, ()) m Q X) :
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
      ∀ (r : BitVec 64) s' m',
        PreservesCoreSlice (fullSafetySlice c).coreProj s s' → s'.LengthsOk c →
        (FullProbeScratchPres s s' ∧ M7GuPrefixPres s s' ∧
          (r = 18446744073709551615#64 ∨
            r.toNat < s.core.cur_vars ∧
              s.core.flags[r.toNat]?.getD 0#32 &&& 1#32 ≠ 0#32 ∧
              s.core.vals[2 * r.toNat]?.getD 0#8 = 0#8)) →
        (FullMem c s' ⋆ R) m' → Q (r, ()) m' := by
  rcases hs with ⟨c, s, R, hpre, hlen, hm, hQ⟩
  exact ⟨c, s, R, hpre, hlen, hm, fun r s' m' hc hl hp hm' => hQ (r, ()) s' m' hc hl hp hm'⟩

theorem m7Log10Q16Spec_of {x : Val i64} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hQ : ∀ (r : BitVec 64), r.toNat < 20 * 65536 → (10 ≤ x.toNat → 65536 ≤ r.toNat) →
      Q (r, ()) m) :
    m7Log10Q16Spec (x, ()) m Q X := hQ

theorem m7Log10Q16Spec_elim {x : Val i64} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hs : m7Log10Q16Spec (x, ()) m Q X) :
    ∀ (r : BitVec 64), r.toNat < 20 * 65536 → (10 ≤ x.toNat → 65536 ≤ r.toNat) → Q (r, ()) m :=
  hs

end LeanQbe.T.Examples.Kissat.FullM7Search
