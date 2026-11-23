module

public import LeanQbe.T.Examples.Kissat.Dimacs
public import LeanQbe.T.Examples.Kissat.CoreLemmas1
public import LeanQbe.T.Examples.LratBytesDimacsLemmas
public import LeanQbe.T.Logic.Bytes
public import LeanQbe.T.Logic.Rules
import all Kraken.Mem
import all Kraken.Separation

/-!
# Soundness Proofs for the Kissat C0 DIMACS Scanner (Part 1)

Defines:
1. `dimacsState` memory predicate (`KissatDimacs { mv; nc; cur; val }`), field load/store helpers,
   and `BitVec`/cursor arithmetic helpers.
2. Pure mirrors (`nextLitPure`, `evalLitVals`, `checkClauseValsAux`, `checkClausesVals`,
   `runKissatCheckModel`, `modelOfVals`) and pure soundness bridging `LratBytes.parseDimacs` to
   `CoreLemmas1.checkModel_sound`.
3. `Spec` contracts for all 8 functions in `dimacs_fns`, plus `mkDimacsEnv`, `dimacsExactEnv`,
   and `dimacsEnv`.
4. `Func.wp` proofs for the 5 low-level scanner primitives: `kissat_is_ws`, `kissat_is_digit`,
   `kissat_skip_ws_comments`, `kissat_skip_ws1`, and `kissat_read_nat`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open Kraken.Bedrock2.Test

/-! ## 1. `KissatDimacs` memory predicate, field helpers, and bit-vector lemmas -/

/-- Memory footprint of `KissatDimacs { mv; nc; cur; val }` at address `d` (32 bytes = 4 `u64`s). -/
def dimacsState (d mv nc cur val : BitVec 64) : Mem 64 → Prop :=
  array64 d [mv, nc, cur, val]

theorem dimacsState_eq_word8Array (d mv nc cur val : BitVec 64) :
    dimacsState d mv nc cur val = word8Array d [mv, nc, cur, val] :=
  array64_eq_word8Array d [mv, nc, cur, val]

theorem dimacsState_to_region {d mv nc cur val : BitVec 64} {f : Mem 64}
    (h : dimacsState d mv nc cur val f) : region d 32 f := by
  rw [dimacsState_eq_word8Array] at h
  simpa using word8Array_to_region (by simp) h

theorem region32_to_dimacsState {d : BitVec 64} {f : Mem 64}
    (h : region d 32 f) : ∃ mv nc cur val, dimacsState d mv nc cur val f := by
  obtain ⟨ws, hlen, hwa⟩ := region_to_word8Array 4 (by decide) (by simpa using h)
  rcases ws with _ | ⟨mv, _ | ⟨nc, _ | ⟨cur, _ | ⟨val, _ | _⟩⟩⟩⟩ <;> simp at hlen
  exact ⟨mv, nc, cur, val, by rwa [dimacsState_eq_word8Array]⟩

theorem dimacsState_bytes (d mv nc cur val : BitVec 64) :
    dimacsState d mv nc cur val ((bytes64 [mv, nc, cur, val]).At d) :=
  array64_bytes d [mv, nc, cur, val] (by simp)

theorem load_dimacs_mv {d mv nc cur val : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (dimacsState d mv nc cur val ⋆ R) m) : loadVal m i64 d = some mv := by
  simpa [dimacsState] using loadVal_array64 (i := 0) (by simp) hm

theorem load_dimacs_nc {d mv nc cur val : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (dimacsState d mv nc cur val ⋆ R) m) : loadVal m i64 (d + 8) = some nc := by
  simpa [dimacsState] using loadVal_array64 (i := 1) (by simp) hm

theorem load_dimacs_cur {d mv nc cur val : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (dimacsState d mv nc cur val ⋆ R) m) : loadVal m i64 (d + 16) = some cur := by
  simpa [dimacsState] using loadVal_array64 (i := 2) (by simp) hm

theorem load_dimacs_val {d mv nc cur val : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (dimacsState d mv nc cur val ⋆ R) m) : loadVal m i64 (d + 24) = some val := by
  simpa [dimacsState] using loadVal_array64 (i := 3) (by simp) hm

theorem store_dimacs_mv {d mv nc cur val : BitVec 64} (mv' : BitVec 64)
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (dimacsState d mv nc cur val ⋆ R) m) :
    storeOk m i64 d ∧ (dimacsState d mv' nc cur val ⋆ R) (storeMem m i64 d mv') := by
  simpa [dimacsState] using store_array64 (i := 0) mv' (by simp) hm

theorem store_dimacs_nc {d mv nc cur val : BitVec 64} (nc' : BitVec 64)
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (dimacsState d mv nc cur val ⋆ R) m) :
    storeOk m i64 (d + 8) ∧ (dimacsState d mv nc' cur val ⋆ R) (storeMem m i64 (d + 8) nc') := by
  simpa [dimacsState] using store_array64 (i := 1) nc' (by simp) hm

theorem store_dimacs_cur {d mv nc cur val : BitVec 64} (cur' : BitVec 64)
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (dimacsState d mv nc cur val ⋆ R) m) :
    storeOk m i64 (d + 16) ∧
      (dimacsState d mv nc cur' val ⋆ R) (storeMem m i64 (d + 16) cur') := by
  simpa [dimacsState] using store_array64 (i := 2) cur' (by simp) hm

theorem store_dimacs_val {d mv nc cur val : BitVec 64} (val' : BitVec 64)
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (dimacsState d mv nc cur val ⋆ R) m) :
    storeOk m i64 (d + 24) ∧
      (dimacsState d mv nc cur val' ⋆ R) (storeMem m i64 (d + 24) val') := by
  simpa [dimacsState] using store_array64 (i := 3) val' (by simp) hm

/-- Word-level predicate computed by `kissat_is_ws`. -/
def isWsWord (b : BitVec 64) : Bool :=
  (b == 32) || (BitVec.ule 9 b && BitVec.ule b 13)

/-- Word-level predicate computed by `kissat_is_digit`. -/
def isDigitWord (b : BitVec 64) : Bool :=
  BitVec.ule 48 b && BitVec.ule b 57

theorem isWsWord_ofUInt8 (b : UInt8) :
    isWsWord (BitVec.ofNat 64 b.toNat) = isDimacsWs b := by
  unfold isWsWord isDimacsWs
  have hb := b.toNat_lt
  simp only [BitVec.ule, BitVec.toNat_ofNat, u8_le_iff_toNat,
    Nat.mod_eq_of_lt (by omega : b.toNat < 2 ^ 64)]
  grind

theorem isDigitWord_ofUInt8 (b : UInt8) :
    isDigitWord (BitVec.ofNat 64 b.toNat) = isDimacsDigit b := by
  unfold isDigitWord isDimacsDigit
  have hb := b.toNat_lt
  simp only [BitVec.ule, BitVec.toNat_ofNat, u8_le_iff_toNat,
    Nat.mod_eq_of_lt (by omega : b.toNat < 2 ^ 64)]
  grind

theorem cursor_ult_eq {base : BitVec 64} {i n : Nat}
    (hfit : base.toNat + n < 2 ^ 64) (hi : i ≤ n) :
    (base + BitVec.ofNat 64 i).ult (base + BitVec.ofNat 64 n) = decide (i < n) := by
  simp only [BitVec.ult, bv_add_ofNat_toNat (by omega : base.toNat + i < 2 ^ 64),
    bv_add_ofNat_toNat hfit]
  grind

theorem cursor_ule_rev_eq {base : BitVec 64} {i n : Nat}
    (hfit : base.toNat + n < 2 ^ 64) (hi : i ≤ n) :
    (base + BitVec.ofNat 64 n).ule (base + BitVec.ofNat 64 i) = decide (i = n) := by
  simp only [BitVec.ule, bv_add_ofNat_toNat (by omega : base.toNat + i < 2 ^ 64),
    bv_add_ofNat_toNat hfit]
  grind

theorem cursor_ult_rev_false {base : BitVec 64} {i n : Nat}
    (hfit : base.toNat + n < 2 ^ 64) (hi : i ≤ n) :
    (base + BitVec.ofNat 64 n).ult (base + BitVec.ofNat 64 i) = false := by
  simp only [BitVec.ult, bv_add_ofNat_toNat (by omega : base.toNat + i < 2 ^ 64),
    bv_add_ofNat_toNat hfit]
  grind

theorem cursor_sub_eq {base : BitVec 64} {i n : Nat}
    (hfit : base.toNat + n < 2 ^ 64) (hi : i ≤ n) :
    (base + BitVec.ofNat 64 n) - (base + BitVec.ofNat 64 i) = BitVec.ofNat 64 (n - i) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub_of_le (by
      rw [BitVec.le_def, bv_add_ofNat_toNat (by omega), bv_add_ofNat_toNat hfit]; omega),
    bv_add_ofNat_toNat hfit, bv_add_ofNat_toNat (by omega),
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

theorem bv32_u8_eq {b k : UInt8} :
    (BitVec.ofNat 8 b.toNat).setWidth 32 = (BitVec.ofNat 8 k.toNat).setWidth 32 ↔ b = k := by
  grind

/-! ## 2. Pure mirror of `kissat_next_lit` & `kissat_check_model` and soundness bridge -/

/-- Signed `i8` byte is strictly positive (`1..127`). -/
@[inline] def i8BytePos (b : UInt8) : Bool :=
  0 < b.toNat && b.toNat < 128

/-- Signed `i8` byte is strictly negative (`128..255`). -/
@[inline] def i8ByteNeg (b : UInt8) : Bool :=
  128 ≤ b.toNat

theorem i8_sext32_sgt_zero (b : UInt8) :
    (0#32).slt ((BitVec.ofNat 8 b.toNat).signExtend 32) = i8BytePos b := by
  have hb := b.toNat_lt
  unfold i8BytePos BitVec.slt
  grind

theorem i8_sext32_slt_zero (b : UInt8) :
    ((BitVec.ofNat 8 b.toNat).signExtend 32).slt 0#32 = i8ByteNeg b := by
  have hb := b.toNat_lt
  unfold i8ByteNeg BitVec.slt
  grind

/-- Convert a 0-based Kissat internal literal (`2*(v-1)` / `2*(v-1)+1`) into the 1-based
`Std.Sat.Literal Nat` used by `LratBytes.parseDimacs`. -/
@[inline] def kissatLitToDimacsLiteral (l : Nat) : Literal Nat :=
  (litVar l + 1, !(litSign l))

/-- Outcome of parsing a single DIMACS literal token (`kissat_next_lit`). -/
inductive NextLitRes where
  | err
  | endClause (rest : List UInt8)
  | lit (l : Nat) (rest : List UInt8)
  deriving Repr, DecidableEq

/-- Pure executable specification of `kissat_next_lit` with max variable `mv`. -/
def nextLitPure (mv : Nat) (bs : List UInt8) : NextLitRes :=
  match skipWsComments bs with
  | [] => .err
  | b :: rest =>
    if b == 45 then
      match parseNat rest with
      | none => .err
      | some (v, rest') =>
        if 1 ≤ v && v ≤ mv then .lit (mkLit (v - 1) false) rest' else .err
    else
      match parseNat (b :: rest) with
      | none => .err
      | some (0, rest') => .endClause rest'
      | some (v, rest') =>
        if v ≤ mv then .lit (mkLit (v - 1) true) rest' else .err

theorem nextLitPure_endClause_length_lt {mv : Nat} {bs rest : List UInt8}
    (h : nextLitPure mv bs = .endClause rest) : rest.length < bs.length := by
  unfold nextLitPure at h
  have hsw_len := skipWsComments_length_le bs
  cases hsw : skipWsComments bs with
  | nil => rw [hsw] at h; cases h
  | cons b tail =>
    rw [hsw] at h hsw_len
    by_cases hb : b = 45
    · simp only [hb, beq_self_eq_true, ↓reduceIte] at h
      cases hpn : parseNat tail with
      | none => rw [hpn] at h; cases h
      | some p =>
        rcases p with ⟨v, rest'⟩; rw [hpn] at h; dsimp only at h
        by_cases hc : (1 ≤ v && v ≤ mv) = true <;> simp [hc] at h
    · simp only [beq_eq_false_iff_ne.mpr hb, Bool.false_eq_true, ↓reduceIte] at h
      cases hpn : parseNat (b :: tail) with
      | none => rw [hpn] at h; cases h
      | some p =>
        rcases p with ⟨v, rest'⟩; rw [hpn] at h
        cases v with
        | zero =>
          simp only [NextLitRes.endClause.injEq] at h; subst h
          have hlt := parseNat_length_lt hpn
          omega
        | succ k => by_cases hc : k + 1 ≤ mv <;> simp [hc] at h

theorem nextLitPure_lit_bounds {mv l : Nat} {bs rest : List UInt8}
    (h : nextLitPure mv bs = .lit l rest) :
    l < 2 * mv ∧ l < 2 * dimacsBound ∧ rest.length < bs.length := by
  unfold nextLitPure at h
  have hsw_len := skipWsComments_length_le bs
  cases hsw : skipWsComments bs with
  | nil => rw [hsw] at h; cases h
  | cons b tail =>
    rw [hsw] at h hsw_len
    by_cases hb : b = 45
    · simp only [hb, beq_self_eq_true, ↓reduceIte] at h
      cases hpn : parseNat tail with
      | none => rw [hpn] at h; cases h
      | some p =>
        rcases p with ⟨v, rest'⟩; rw [hpn] at h; dsimp only at h
        by_cases hc : (1 ≤ v && v ≤ mv) = true
        · simp only [hc, ↓reduceIte, NextLitRes.lit.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
          have hvlt := parseNat_lt_bound hpn
          have hlen := parseNat_length_lt hpn
          simp only [mkLit, Bool.false_eq_true, ↓reduceIte, List.length_cons] at hsw_len ⊢
          omega
        · simp [Bool.eq_false_iff.mpr hc] at h
    · simp only [beq_eq_false_iff_ne.mpr hb, Bool.false_eq_true, ↓reduceIte] at h
      cases hpn : parseNat (b :: tail) with
      | none => rw [hpn] at h; cases h
      | some p =>
        rcases p with ⟨v, rest'⟩; rw [hpn] at h
        cases v with
        | zero => cases h
        | succ k =>
          by_cases hle : k + 1 ≤ mv
          · simp only [hle, ↓reduceIte, NextLitRes.lit.injEq] at h
            rcases h with ⟨rfl, rfl⟩
            have hvlt := parseNat_lt_bound hpn
            have hlen := parseNat_length_lt hpn
            simp only [mkLit, ↓reduceIte] at ⊢
            omega
          · simp [hle] at h

private theorem parseClauseAux_succ_pos' {fuel mv : Nat} {acc : List (Literal Nat)}
    {b : UInt8} {bs tail : List UInt8} (hsw : skipWsComments bs = b :: tail) (hb : b ≠ 45) :
    parseClauseAux (fuel + 1) mv acc bs =
      match parseNat (b :: tail) with
      | some (0, rest') => some (CNF.Clause.ofLiterals acc.reverse, rest')
      | some (v, rest') =>
        if 1 ≤ v && v ≤ mv then parseClauseAux fuel mv ((v, true) :: acc) rest' else none
      | none => none := by
  have := hb
  simp only [parseClauseAux, hsw]
  rcases parseNat (b :: tail) with _ | ⟨v, rest'⟩
  · simp
  · cases v <;> simp

/-- Exact one-step equivalence between `LratBytes.parseClauseAux` and `nextLitPure`. -/
theorem parseClauseAux_eq_nextLitPure (fuel mv : Nat) (acc : List (Literal Nat))
    (bs : List UInt8) :
    parseClauseAux (fuel + 1) mv acc bs =
      match nextLitPure mv bs with
      | .err => none
      | .endClause rest' => some (CNF.Clause.ofLiterals acc.reverse, rest')
      | .lit l rest' => parseClauseAux fuel mv (kissatLitToDimacsLiteral l :: acc) rest' := by
  cases hsw : skipWsComments bs with
  | nil => simp [parseClauseAux, nextLitPure, hsw]
  | cons b tail =>
    by_cases hb : b = 45
    · subst hb
      simp only [parseClauseAux, nextLitPure, hsw, beq_self_eq_true, ↓reduceIte]
      cases hpn : parseNat tail with
      | none => rfl
      | some p =>
        rcases p with ⟨v, rest'⟩
        by_cases hcond : (1 ≤ v && v ≤ mv) = true
        · simp only [hcond, ↓reduceIte]
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
          have hlit : kissatLitToDimacsLiteral (mkLit (v - 1) false) = (v, false) := by
            simp [kissatLitToDimacsLiteral]; omega
          rw [hlit]
        · have hf : (1 ≤ v && v ≤ mv) = false := Bool.eq_false_iff.mpr hcond
          simp [hf]
    · rw [parseClauseAux_succ_pos' hsw hb]
      simp only [nextLitPure, hsw, beq_eq_false_iff_ne.mpr hb, Bool.false_eq_true, ↓reduceIte]
      cases hpn : parseNat (b :: tail) with
      | none => rfl
      | some p =>
        rcases p with ⟨v, rest'⟩
        cases v with
        | zero => rfl
        | succ k =>
          by_cases hle : k + 1 ≤ mv
          · have hlit : kissatLitToDimacsLiteral (mkLit k true) = (k + 1, true) := by
              simp [kissatLitToDimacsLiteral]
            simp only [hle, Nat.succ_le_succ_iff, Nat.zero_le, Bool.true_and,
              Nat.add_sub_cancel, decide_true, ↓reduceIte, hlit]
          · simp [hle]

/-- Evaluate a 0-based Kissat literal `l` against `valsBytes` (at byte `2 * litVar l`). -/
def evalLitVals (valsBytes : List UInt8) (l : Nat) : Bool :=
  let b := valsBytes.getD (2 * litVar l) 0
  if litSign l then i8ByteNeg b else i8BytePos b

/-- Pure mirror of the inner clause loop in `kissat_check_model`. -/
def checkClauseValsAux : Nat → Nat → List UInt8 → Bool → List UInt8 → Option (Bool × List UInt8)
  | 0, _, _, _, _ => none
  | fuel + 1, mv, valsBytes, sat, bs =>
    match nextLitPure mv bs with
    | .err => none
    | .endClause rest => some (sat, rest)
    | .lit l rest => checkClauseValsAux fuel mv valsBytes (sat || evalLitVals valsBytes l) rest

/-- Pure mirror of the outer clause loop in `kissat_check_model`. -/
def checkClausesVals (mv : Nat) (valsBytes : List UInt8) : Nat → List UInt8 → Bool
  | 0, bs => (skipWsComments bs).isEmpty
  | k + 1, bs =>
    match checkClauseValsAux (bs.length + 1) mv valsBytes false bs with
    | some (true, rest) => checkClausesVals mv valsBytes k rest
    | _ => false

/-- Total executable mirror of `kissat_check_model(cnfBytes, valsBytes, mv_max)`. -/
def runKissatCheckModel (cnfBytes valsBytes : List UInt8) (mv_max : Nat) : Bool :=
  match parseHeader cnfBytes with
  | none => false
  | some (mv, nc, rest) =>
    if mv > mv_max then false
    else checkClausesVals mv valsBytes nc rest

/-- Extract a 1-based `Bool` model array of size `mv + 1` from `valsBytes`, matching the
1-based variable indexing of `LratBytes.parseDimacs`. -/
def modelOfVals (mv : Nat) (valsBytes : List UInt8) : Array Bool :=
  Array.ofFn (n := mv + 1) fun i =>
    if i.1 == 0 then false else i8BytePos (valsBytes.getD (2 * (i.1 - 1)) 0)

theorem evalLitVals_implies_model {mv l : Nat} {valsBytes : List UInt8}
    (hlt : l < 2 * mv) (h : evalLitVals valsBytes l = true) :
    evalVar (modelOfVals mv valsBytes) (kissatLitToDimacsLiteral l).1 =
      (kissatLitToDimacsLiteral l).2 := by
  have hvlt : litVar l < mv := by unfold litVar; omega
  have hev : evalVar (modelOfVals mv valsBytes) (litVar l + 1) =
      i8BytePos (valsBytes.getD (2 * litVar l) 0) := by
    simp [evalVar, modelOfVals, hvlt]
  unfold evalLitVals at h
  simp only [kissatLitToDimacsLiteral, hev]
  cases hs : litSign l
  · rw [hs] at h; simpa using h
  · rw [hs] at h; dsimp only at h
    unfold i8ByteNeg at h; unfold i8BytePos
    grind

theorem checkClauseValsAux_fuel_irrel {f1 f2 mv : Nat} {valsBytes : List UInt8} {sat : Bool}
    {bs : List UInt8} (h1 : bs.length < f1) (h2 : bs.length < f2) :
    checkClauseValsAux f1 mv valsBytes sat bs = checkClauseValsAux f2 mv valsBytes sat bs := by
  induction f1 generalizing f2 sat bs with
  | zero => omega
  | succ f1 ih =>
    cases f2 with
    | zero => omega
    | succ f2 =>
      simp only [checkClauseValsAux]
      cases hn : nextLitPure mv bs with
      | err => rfl
      | endClause rest => rfl
      | lit l rest =>
        have ⟨_, _, hlt⟩ := nextLitPure_lit_bounds hn
        exact ih (by omega) (by omega)

private theorem checkClauseValsAux_sound {fuel mv : Nat} {valsBytes : List UInt8} {sat sat' : Bool}
    {acc : List (Literal Nat)} {bs rest : List UInt8}
    (hsat : sat = true → ∃ lit ∈ acc, evalVar (modelOfVals mv valsBytes) lit.1 = lit.2)
    (h : checkClauseValsAux fuel mv valsBytes sat bs = some (sat', rest)) :
    ∃ cl, parseClauseAux fuel mv acc bs = some (cl, rest) ∧
      (sat' = true → cl.Sat (evalVar (modelOfVals mv valsBytes))) := by
  induction fuel generalizing sat acc bs with
  | zero => simp [checkClauseValsAux] at h
  | succ fuel ih =>
    rw [checkClauseValsAux] at h
    rw [parseClauseAux_eq_nextLitPure]
    cases hn : nextLitPure mv bs with
    | err => rw [hn] at h; cases h
    | endClause rest' =>
      rw [hn] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      refine ⟨CNF.Clause.ofLiterals acc.reverse, rfl, fun ht => ?_⟩
      obtain ⟨lit, hmem, heq⟩ := hsat ht
      rw [CNF.Clause.sat_iff_exists_mem_eq]
      exact ⟨lit, by rw [← CNF.Clause.mem_literals_iff]; simp [hmem], heq⟩
    | lit l rest' =>
      rw [hn] at h
      have ⟨hlt, _, _⟩ := nextLitPure_lit_bounds hn
      refine ih (fun ht => ?_) h
      simp only [Bool.or_eq_true] at ht
      rcases ht with h1 | h2
      · obtain ⟨lit, hmem, heq⟩ := hsat h1
        exact ⟨lit, List.mem_cons_of_mem _ hmem, heq⟩
      · exact ⟨kissatLitToDimacsLiteral l, List.mem_cons_self,
          evalLitVals_implies_model hlt h2⟩

private theorem checkClausesVals_sound {mv k : Nat} {valsBytes bs : List UInt8}
    {accCnf : CNF Nat}
    (hacc : accCnf.Sat (evalVar (modelOfVals mv valsBytes)))
    (h : checkClausesVals mv valsBytes k bs = true) :
    ∃ cnf, parseClauses mv k accCnf bs = some cnf ∧
      cnf.Sat (evalVar (modelOfVals mv valsBytes)) := by
  induction k generalizing accCnf bs with
  | zero =>
    simp only [checkClausesVals] at h
    exact ⟨accCnf, by simp [parseClauses, h], hacc⟩
  | succ k ih =>
    simp only [checkClausesVals] at h
    cases hc : checkClauseValsAux (bs.length + 1) mv valsBytes false bs with
    | none => rw [hc] at h; cases h
    | some p =>
      rcases p with ⟨sat, rest⟩
      rw [hc] at h
      cases sat with
      | false => cases h
      | true =>
        obtain ⟨cl, hcl, hcl_sat⟩ := checkClauseValsAux_sound (acc := []) (by simp) hc
        have hpc : parseClause mv bs = some (cl, rest) := hcl
        have hadd_sat : (accCnf.add cl).Sat (evalVar (modelOfVals mv valsBytes)) :=
          CNF.sat_add.mpr ⟨hcl_sat rfl, hacc⟩
        obtain ⟨cnf, hpc', hsat'⟩ := ih hadd_sat h
        exact ⟨cnf, by simp [parseClauses, hpc, hpc'], hsat'⟩

/-- Pure soundness of `runKissatCheckModel`, bridging `LratBytes.parseDimacs` directly to
`CoreLemmas1.checkModel_sound`. -/
theorem runKissatCheckModel_sound {cnfBytes valsBytes : List UInt8} {mv_max : Nat}
    (h : runKissatCheckModel cnfBytes valsBytes mv_max = true) :
    ∃ cnf mv, parseDimacs cnfBytes = some cnf ∧
      checkModel cnf (modelOfVals mv valsBytes) = true ∧
      ¬ cnf.Unsat ∧ ∃ α, cnf.Sat α := by
  unfold runKissatCheckModel at h
  cases hh : parseHeader cnfBytes with
  | none => rw [hh] at h; cases h
  | some p =>
    rcases p with ⟨mv, nc, rest⟩
    rw [hh] at h; dsimp only at h
    split at h
    · cases h
    · obtain ⟨cnf, hcls, hsat⟩ := checkClausesVals_sound (accCnf := CNF.empty) (by simp) h
      have hcm : checkModel cnf (modelOfVals mv valsBytes) = true :=
        (checkModel_iff_sat cnf (modelOfVals mv valsBytes)).mpr hsat
      have hsound := checkModel_sound hcm
      exact ⟨cnf, mv, by simp [parseDimacs, hh, hcls], hcm, hsound.1, hsound.2⟩

/-! ## 3. Specifications for all 8 C0 functions in `dimacs_fns` -/

/-- Specification of `kissat_is_ws(b)`. -/
def kissatIsWsSpec : Spec [i64] [.bool] := fun (b, ()) m Q _ =>
  Q (isWsWord b, ()) m

/-- Specification of `kissat_is_digit(b)`. -/
def kissatIsDigitSpec : Spec [i64] [.bool] := fun (b, ()) m Q _ =>
  Q (isDigitWord b, ()) m

/-- Specification of `kissat_skip_ws_comments(p, end)`. -/
def kissatSkipWsCommentsSpec : Spec [i64, i64] [i64] := fun (p, cend, ()) m Q _ =>
  ∃ (cnf_ptr : BitVec 64) (cnfBytes : List UInt8) (i0 : Nat) (R : Mem 64 → Prop),
    p = cnf_ptr + BitVec.ofNat 64 i0 ∧
    cend = cnf_ptr + BitVec.ofNat 64 cnfBytes.length ∧
    cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧
    i0 ≤ cnfBytes.length ∧
    (bytes cnf_ptr cnfBytes ⋆ R) m ∧
    ∀ j, i0 ≤ j → j ≤ cnfBytes.length →
      cnfBytes.drop j = skipWsComments (cnfBytes.drop i0) →
      Q (cnf_ptr + BitVec.ofNat 64 j, ()) m

/-- Specification of `kissat_skip_ws1(end, d)`. -/
def kissatSkipWs1Spec : Spec [i64, i64] [.bool] := fun (cend, d, ()) m Q _ =>
  ∃ (cnf_ptr mv nc val : BitVec 64) (cnfBytes : List UInt8) (i0 : Nat) (R : Mem 64 → Prop),
    cend = cnf_ptr + BitVec.ofNat 64 cnfBytes.length ∧
    cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧
    i0 ≤ cnfBytes.length ∧
    (bytes cnf_ptr cnfBytes ⋆ dimacsState d mv nc (cnf_ptr + BitVec.ofNat 64 i0) val ⋆ R) m ∧
    match skipWs1 (cnfBytes.drop i0) with
    | none => Q (false, ()) m
    | some rest =>
      ∀ j m', i0 < j → j ≤ cnfBytes.length → cnfBytes.drop j = rest →
        (bytes cnf_ptr cnfBytes ⋆ dimacsState d mv nc (cnf_ptr + BitVec.ofNat 64 j) val ⋆ R) m' →
        Q (true, ()) m'

/-- Specification of `kissat_read_nat(end, d)`. -/
def kissatReadNatSpec : Spec [i64, i64] [.bool] := fun (cend, d, ()) m Q _ =>
  ∃ (cnf_ptr mv nc val : BitVec 64) (cnfBytes : List UInt8) (i0 : Nat) (R : Mem 64 → Prop),
    cend = cnf_ptr + BitVec.ofNat 64 cnfBytes.length ∧
    cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧
    i0 ≤ cnfBytes.length ∧
    (bytes cnf_ptr cnfBytes ⋆ dimacsState d mv nc (cnf_ptr + BitVec.ofNat 64 i0) val ⋆ R) m ∧
    match parseNat (cnfBytes.drop i0) with
    | none => Q (false, ()) m
    | some (v, rest) =>
      ∀ j m', v < dimacsBound → i0 < j → j ≤ cnfBytes.length → cnfBytes.drop j = rest →
        (bytes cnf_ptr cnfBytes ⋆
          dimacsState d mv nc (cnf_ptr + BitVec.ofNat 64 j) (BitVec.ofNat 64 v) ⋆ R) m' →
        Q (true, ()) m'

/-- Specification of `kissat_parse_header(cnf_ptr, cnf_end, d)`. -/
def kissatParseHeaderSpec : Spec [i64, i64, i64] [.bool] := fun (cnf_ptr, cend, d, ()) m Q _ =>
  ∃ (mv0 nc0 cur0 val0 : BitVec 64) (cnfBytes : List UInt8) (R : Mem 64 → Prop),
    cend = cnf_ptr + BitVec.ofNat 64 cnfBytes.length ∧
    cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧
    (bytes cnf_ptr cnfBytes ⋆ dimacsState d mv0 nc0 cur0 val0 ⋆ R) m ∧
    match parseHeader cnfBytes with
    | none =>
      ∀ mv' nc' cur' val' m',
        (bytes cnf_ptr cnfBytes ⋆ dimacsState d mv' nc' cur' val' ⋆ R) m' →
        Q (false, ()) m'
    | some (mv, nc, rest) =>
      ∀ j m', mv < dimacsBound → nc < dimacsBound →
        j ≤ cnfBytes.length → cnfBytes.drop j = rest →
        (bytes cnf_ptr cnfBytes ⋆
          dimacsState d (BitVec.ofNat 64 mv) (BitVec.ofNat 64 nc)
            (cnf_ptr + BitVec.ofNat 64 j) (BitVec.ofNat 64 nc) ⋆ R) m' →
        Q (true, ()) m'

/-- Specification of `kissat_next_lit(cnf_end, d)` returning status `0` (err), `1` (end of
clause), or `2` (0-based encoded literal in `d->val`). -/
def kissatNextLitSpec : Spec [i64, i64] [i64] := fun (cend, d, ()) m Q _ =>
  ∃ (cnf_ptr nc val0 : BitVec 64) (mv : Nat) (cnfBytes : List UInt8) (i0 : Nat)
    (R : Mem 64 → Prop),
    cend = cnf_ptr + BitVec.ofNat 64 cnfBytes.length ∧
    cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧
    mv < 2 ^ 64 ∧
    i0 ≤ cnfBytes.length ∧
    (bytes cnf_ptr cnfBytes ⋆
      dimacsState d (BitVec.ofNat 64 mv) nc (cnf_ptr + BitVec.ofNat 64 i0) val0 ⋆ R) m ∧
    match nextLitPure mv (cnfBytes.drop i0) with
    | .err =>
      ∀ cur' val' m',
        (bytes cnf_ptr cnfBytes ⋆
          dimacsState d (BitVec.ofNat 64 mv) nc cur' val' ⋆ R) m' →
        Q (0#64, ()) m'
    | .endClause rest =>
      ∀ j m', i0 < j → j ≤ cnfBytes.length → cnfBytes.drop j = rest →
        (bytes cnf_ptr cnfBytes ⋆
          dimacsState d (BitVec.ofNat 64 mv) nc (cnf_ptr + BitVec.ofNat 64 j) 0#64 ⋆ R) m' →
        Q (1#64, ()) m'
    | .lit l rest =>
      ∀ j m', l < 2 * mv → l < 2 * dimacsBound →
        i0 < j → j ≤ cnfBytes.length → cnfBytes.drop j = rest →
        (bytes cnf_ptr cnfBytes ⋆
          dimacsState d (BitVec.ofNat 64 mv) nc
            (cnf_ptr + BitVec.ofNat 64 j) (BitVec.ofNat 64 l) ⋆ R) m' →
        Q (2#64, ()) m'

/-- Exact decision specification of `kissat_check_model(cnf_ptr, cnf_end, d, vals, mv_max)`. -/
def kissatCheckModelExactSpec : Spec [i64, i64, i64, i64, i64] [i64] :=
  fun (cnf_ptr, cend, d, vals_ptr, mv_max_v, ()) m Q _ =>
    ∃ (mv0 nc0 cur0 val0 : BitVec 64) (cnfBytes valsBytes : List UInt8) (mv_max : Nat)
      (R : Mem 64 → Prop),
      cend = cnf_ptr + BitVec.ofNat 64 cnfBytes.length ∧
      mv_max_v = BitVec.ofNat 64 mv_max ∧
      cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧
      mv_max < 2 ^ 64 ∧
      2 * mv_max ≤ valsBytes.length ∧
      valsBytes.length ≤ 2 ^ 64 ∧
      (bytes cnf_ptr cnfBytes ⋆ dimacsState d mv0 nc0 cur0 val0 ⋆
        bytes vals_ptr valsBytes ⋆ R) m ∧
      ∀ (r mv' nc' cur' val' : BitVec 64) (m' : Mem 64),
        r = (if runKissatCheckModel cnfBytes valsBytes mv_max then 1#64 else 0#64) →
        (bytes cnf_ptr cnfBytes ⋆ dimacsState d mv' nc' cur' val' ⋆
          bytes vals_ptr valsBytes ⋆ R) m' →
        Q (r, ()) m'

/-- High-level soundness specification of `kissat_check_model`: returns `0` or `1`, and `1`
certifies `∃ cnf, LratBytes.parseDimacs cnfBytes = some cnf ∧ ¬ cnf.Unsat ∧ ∃ α, cnf.Sat α`. -/
def kissatCheckModelSpec : Spec [i64, i64, i64, i64, i64] [i64] :=
  fun (cnf_ptr, cend, d, vals_ptr, mv_max_v, ()) m Q _ =>
    ∃ (mv0 nc0 cur0 val0 : BitVec 64) (cnfBytes valsBytes : List UInt8) (mv_max : Nat)
      (R : Mem 64 → Prop),
      cend = cnf_ptr + BitVec.ofNat 64 cnfBytes.length ∧
      mv_max_v = BitVec.ofNat 64 mv_max ∧
      cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧
      mv_max < 2 ^ 64 ∧
      2 * mv_max ≤ valsBytes.length ∧
      valsBytes.length ≤ 2 ^ 64 ∧
      (bytes cnf_ptr cnfBytes ⋆ dimacsState d mv0 nc0 cur0 val0 ⋆
        bytes vals_ptr valsBytes ⋆ R) m ∧
      ∀ (r mv' nc' cur' val' : BitVec 64) (m' : Mem 64),
        (r = 0#64 ∨ r = 1#64) →
        (r = 1#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ ¬ cnf.Unsat ∧ ∃ α, cnf.Sat α) →
        (bytes cnf_ptr cnfBytes ⋆ dimacsState d mv' nc' cur' val' ⋆
          bytes vals_ptr valsBytes ⋆ R) m' →
        Q (r, ()) m'

/-- Parameterized specification environment for all 8 functions in `dimacs_fns`. -/
def mkDimacsEnv (checkSpec : Spec [i64, i64, i64, i64, i64] [i64]) : Env
  | "kissat_is_ws", [.bits 64], [.bool] => kissatIsWsSpec
  | "kissat_is_digit", [.bits 64], [.bool] => kissatIsDigitSpec
  | "kissat_skip_ws_comments", [.bits 64, .bits 64], [.bits 64] => kissatSkipWsCommentsSpec
  | "kissat_skip_ws1", [.bits 64, .bits 64], [.bool] => kissatSkipWs1Spec
  | "kissat_read_nat", [.bits 64, .bits 64], [.bool] => kissatReadNatSpec
  | "kissat_parse_header", [.bits 64, .bits 64, .bits 64], [.bool] => kissatParseHeaderSpec
  | "kissat_next_lit", [.bits 64, .bits 64], [.bits 64] => kissatNextLitSpec
  | "kissat_check_model", [.bits 64, .bits 64, .bits 64, .bits 64, .bits 64], [.bits 64] =>
      checkSpec
  | _, _, _ => fun _ _ _ _ => False

/-- Exact decision environment for `dimacsModule`. -/
def dimacsExactEnv : Env := mkDimacsEnv kissatCheckModelExactSpec

/-- Top-level soundness environment for `dimacsModule`. -/
def dimacsEnv : Env := mkDimacsEnv kissatCheckModelSpec

/-! ## 4. `Func.wp` proofs for scanner primitives (`is_ws`, `is_digit`, `skip_*`, `read_nat`) -/

theorem kissat_is_ws_wp (Γ : Env) :
    ∀ args m Q X, kissatIsWsSpec args m Q X → Func.wp Γ kissat_is_ws_body args m Q X := by
  rintro ⟨b, ⟨⟩⟩ m Q X hQ
  unfold Func.wp kissat_is_ws_body
  refine wp_join_group (fun (res, ()) m' => res = isWsWord b ∧ m' = m) ?_ ?_
  · rintro _ ⟨res, ⟨⟩⟩ _ ⟨rfl, rfl⟩; wp_unfold; exact hQ
  · intro J hJ; wp_unfold
    refine ⟨fun h32 => hJ (true, ()) m ⟨by simp only [isWsWord]; grind, rfl⟩,
      fun hn32 => ⟨fun h9 => ⟨fun h13 => hJ (true, ()) m ⟨by simp only [isWsWord]; grind, rfl⟩,
        fun hn13 => hJ (false, ()) m ⟨by simp only [isWsWord]; grind, rfl⟩⟩,
      fun hn9 => hJ (false, ()) m ⟨by simp only [isWsWord]; grind, rfl⟩⟩⟩

theorem kissat_is_digit_wp (Γ : Env) :
    ∀ args m Q X, kissatIsDigitSpec args m Q X → Func.wp Γ kissat_is_digit_body args m Q X := by
  rintro ⟨b, ⟨⟩⟩ m Q X hQ
  unfold Func.wp kissat_is_digit_body
  refine wp_join_group (fun (res, ()) m' => res = isDigitWord b ∧ m' = m) ?_ ?_
  · rintro _ ⟨res, ⟨⟩⟩ _ ⟨rfl, rfl⟩; wp_unfold; exact hQ
  · intro J hJ; wp_unfold
    refine ⟨fun h48 => ⟨fun h57 => hJ (true, ()) m ⟨by simp only [isDigitWord]; grind, rfl⟩,
        fun hn57 => hJ (false, ()) m ⟨by simp only [isDigitWord]; grind, rfl⟩⟩,
      fun hn48 => hJ (false, ()) m ⟨by simp only [isDigitWord]; grind, rfl⟩⟩

private theorem skipWsCommentsAux_true_cons' (c : UInt8) (bs : List UInt8) :
    skipWsCommentsAux true (c :: bs) =
      if c = 10 then skipWsCommentsAux false bs else skipWsCommentsAux true bs := by
  by_cases h : c = 10 <;> simp [skipWsCommentsAux, h]

theorem kissat_skip_ws_comments_wp (Γ : Env)
    (hWs : ∀ args m Q X, kissatIsWsSpec args m Q X → Γ "kissat_is_ws" [i64] [.bool] args m Q X) :
    ∀ args m Q X, kissatSkipWsCommentsSpec args m Q X →
      Func.wp Γ kissat_skip_ws_comments_body args m Q X := by
  rintro ⟨p, cend, ⟨⟩⟩ m Q X ⟨cnf_ptr, bs, i0, R, rfl, rfl, hfit, hi0, hm, hQ⟩
  unfold Func.wp kissat_skip_ws_comments_body
  refine wp_loop_break_group
    (fun (res_v, ()) m' => ∃ j, i0 ≤ j ∧ j ≤ bs.length ∧
      bs.drop j = skipWsComments (bs.drop i0) ∧ res_v = cnf_ptr + BitVec.ofNat 64 j ∧ m' = m)
    (fun r (p_v, ()) m' => ∃ i, i0 ≤ i ∧ i ≤ bs.length ∧ r = bs.length - i ∧
      skipWsCommentsAux false (bs.drop i) = skipWsComments (bs.drop i0) ∧
      p_v = cnf_ptr + BitVec.ofNat 64 i ∧ m' = m)
    ?_ ?_ ?_
  · rintro _ ⟨res_v, ⟨⟩⟩ _ ⟨j, hj1, hj2, hdrop, rfl, rfl⟩
    wp_unfold; exact hQ j hj1 hj2 hdrop
  · rintro B L r ⟨p_v, ⟨⟩⟩ m' hB ih ⟨i, hi1, hi2, rfl, hinv, rfl, hm'⟩
    subst m'; wp_unfold
    rw [cursor_ult_eq hfit hi2]
    simp only [decide_eq_true_eq, decide_eq_false_iff_not]
    refine ⟨fun hlt => ?_, fun hnlt => ?_⟩
    · have hd_i := List.drop_eq_getElem_cons hlt
      refine ⟨_, load_bytes_at hlt (by omega) hm, ?_⟩
      rw [setWidth64_ofNat8]
      refine wp_join_group
        (fun (p_next, ()) m2 => ∃ i', i < i' ∧ i' ≤ bs.length ∧
          skipWsCommentsAux false (bs.drop i') = skipWsComments (bs.drop i0) ∧
          p_next = cnf_ptr + BitVec.ofNat 64 i' ∧ m2 = m) ?_ ?_
      · rintro _ ⟨p_next, ⟨⟩⟩ m2 ⟨i', hi'1, hi'2, hinv', rfl, hm2⟩
        subst m2; wp_unfold
        exact ih (bs.length - i') _ m (by omega) ⟨i', by omega, hi'2, rfl, hinv', rfl, rfl⟩
      · intro Jif hJif
        apply wp_call_of_spec; apply hWs
        wp_unfold; dsimp only [kissatIsWsSpec]; rw [isWsWord_ofUInt8]
        refine ⟨fun hws => ?_, fun hnws => ?_⟩
        · rw [ptr_step_1]
          exact hJif _ m ⟨i + 1, by omega, by omega,
            by rw [hd_i, skipWsCommentsAux] at hinv; simpa [hws] using hinv, rfl, rfl⟩
        · refine ⟨fun h99 => ?_, fun hn99 => ?_⟩
          · have hb99 : bs[i] = 99 := (bv64_u8_eq (k := 99)).mp h99
            have hinv_c : skipWsCommentsAux true (bs.drop (i + 1)) =
                skipWsComments (bs.drop i0) := by
              rw [hd_i, skipWsCommentsAux, hb99] at hinv
              simpa [show isDimacsWs 99 = false by decide] using hinv
            rw [ptr_step_1]
            refine wp_loop_break_group
              (fun (q_v, ()) m2 => ∃ i', i < i' ∧ i' ≤ bs.length ∧
                skipWsCommentsAux false (bs.drop i') = skipWsComments (bs.drop i0) ∧
                q_v = cnf_ptr + BitVec.ofNat 64 i' ∧ m2 = m)
              (fun r2 (q_v, ()) m2 => ∃ k, i + 1 ≤ k ∧ k ≤ bs.length ∧ r2 = bs.length - k ∧
                skipWsCommentsAux true (bs.drop k) = skipWsComments (bs.drop i0) ∧
                q_v = cnf_ptr + BitVec.ofNat 64 k ∧ m2 = m)
              ?_ ?_ ?_
            · rintro _ ⟨q_v, ⟨⟩⟩ _ hpost
              wp_unfold; exact hJif _ _ hpost
            · rintro B2 L2 r2 ⟨q_v, ⟨⟩⟩ m2 hB2 ih2 ⟨k, hk1, hk2, rfl, hinv2, rfl, hm2⟩
              subst m2; wp_unfold; rw [cursor_ult_eq hfit hk2]
              simp only [decide_eq_true_eq, decide_eq_false_iff_not]
              refine ⟨fun hklt => ?_, fun hnklt => ?_⟩
              · have hd_k := List.drop_eq_getElem_cons hklt
                refine ⟨_, load_bytes_at hklt (by omega) hm, ?_⟩
                rw [setWidth64_ofNat8, ptr_step_1]
                refine ⟨fun h10 => ?_, fun hn10 => ?_⟩
                · have hc10 : bs[k] = 10 := (bv64_u8_eq (k := 10)).mp h10
                  exact hB2 _ m ⟨k + 1, by omega, by omega,
                    by rw [hd_k, skipWsCommentsAux_true_cons'] at hinv2; simpa [hc10] using hinv2,
                    rfl, rfl⟩
                · have hc10 : bs[k] ≠ 10 := fun h => hn10 ((bv64_u8_eq (k := 10)).mpr h)
                  exact ih2 (bs.length - (k + 1)) _ m (by omega)
                    ⟨k + 1, by omega, by omega, rfl,
                      by rw [hd_k, skipWsCommentsAux_true_cons'] at hinv2; simpa [hc10] using hinv2,
                      rfl, rfl⟩
              · have hkeq : k = bs.length := by omega
                subst hkeq
                exact hB2 _ m ⟨bs.length, by omega, Nat.le_refl _,
                  by simpa [skipWsCommentsAux] using hinv2, rfl, rfl⟩
            · intro B2 L2 _ hL2; wp_unfold
              exact hL2 (bs.length - (i + 1)) _ m
                ⟨i + 1, Nat.le_refl _, by omega, rfl, hinv_c, rfl, rfl⟩
          · have hb99 : (bs[i] == 99) = false :=
              beq_eq_false_iff_ne.mpr (fun h => hn99 ((bv64_u8_eq (k := 99)).mpr h))
            exact hB _ m ⟨i, hi1, hi2,
              by rw [hd_i, skipWsCommentsAux, hnws, hb99] at hinv; simpa [← hd_i] using hinv,
              rfl, rfl⟩
    · have hieq : i = bs.length := by omega
      subst hieq
      exact hB _ m ⟨bs.length, hi1, Nat.le_refl _,
        by simpa [skipWsCommentsAux] using hinv, rfl, rfl⟩
  · intro B L _ hL; wp_unfold
    exact hL (bs.length - i0) _ m ⟨i0, Nat.le_refl _, hi0, rfl, rfl, rfl, rfl⟩

theorem kissat_skip_ws1_wp (Γ : Env)
    (hWs : ∀ args m Q X, kissatIsWsSpec args m Q X → Γ "kissat_is_ws" [i64] [.bool] args m Q X) :
    ∀ args m Q X, kissatSkipWs1Spec args m Q X →
      Func.wp Γ kissat_skip_ws1_body args m Q X := by
  rintro ⟨cend, d, ⟨⟩⟩ m Q X ⟨cnf_ptr, mv, nc, val, bs, i0, R, rfl, hfit, hi0, hm, hQ⟩
  unfold Func.wp kissat_skip_ws1_body; wp_unfold
  have hm_bs : (bytes cnf_ptr bs ⋆
      (dimacsState d mv nc (cnf_ptr + BitVec.ofNat 64 i0) val ⋆ R)) m := sep_ac hm
  have hm_d : (dimacsState d mv nc (cnf_ptr + BitVec.ofNat 64 i0) val ⋆
      (bytes cnf_ptr bs ⋆ R)) m := sep_ac hm
  refine ⟨_, load_dimacs_cur hm_d, ?_⟩
  rw [cursor_ule_rev_eq hfit hi0]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  refine ⟨fun heq => by
      have hnil : bs.drop i0 = [] := by simp [heq]
      simpa [hnil, skipWs1] using hQ,
    fun hne => ?_⟩
  have hlt0 : i0 < bs.length := by omega
  have hd0 := List.drop_eq_getElem_cons hlt0
  refine ⟨_, load_bytes_at hlt0 (by omega) hm_bs, ?_⟩
  rw [setWidth64_ofNat8]
  apply wp_call_of_spec; apply hWs
  wp_unfold; dsimp only [kissatIsWsSpec]; rw [isWsWord_ofUInt8]
  refine ⟨fun hws0 => ?_, fun hnws0 => by
      have hnone : skipWs1 (bs.drop i0) = none := by rw [hd0]; simp [skipWs1, hnws0]
      simpa [hnone] using hQ⟩
  have hsw1 : skipWs1 (bs.drop i0) = some (skipWs (bs.drop (i0 + 1))) := by
    rw [hd0]; simp [skipWs1, hws0]
  rw [hsw1] at hQ
  rw [ptr_step_1]
  refine wp_loop_break_group
    (fun (res_v, ()) m' => ∃ j, i0 < j ∧ j ≤ bs.length ∧
      bs.drop j = skipWs (bs.drop (i0 + 1)) ∧ res_v = cnf_ptr + BitVec.ofNat 64 j ∧ m' = m)
    (fun r (p_v, ()) m' => ∃ i, i0 < i ∧ i ≤ bs.length ∧ r = bs.length - i ∧
      skipWs (bs.drop i) = skipWs (bs.drop (i0 + 1)) ∧
      p_v = cnf_ptr + BitVec.ofNat 64 i ∧ m' = m)
    ?_ ?_ ?_
  · rintro _ ⟨res_v, ⟨⟩⟩ m' ⟨j, hj1, hj2, hdrop, rfl, hm'⟩
    subst m'; wp_unfold
    obtain ⟨hok, hm1⟩ := store_dimacs_cur (cnf_ptr + BitVec.ofNat 64 j) hm_d
    exact ⟨hok, hQ j _ hj1 hj2 hdrop (sep_ac hm1)⟩
  · rintro B L r ⟨p_v, ⟨⟩⟩ m' hB ih ⟨i, hi1, hi2, rfl, hinv, rfl, hm'⟩
    subst m'; wp_unfold; rw [cursor_ult_eq hfit hi2]
    simp only [decide_eq_true_eq, decide_eq_false_iff_not]
    refine ⟨fun hlt => ?_, fun hnlt => ?_⟩
    · have hd_i := List.drop_eq_getElem_cons hlt
      refine ⟨_, load_bytes_at hlt (by omega) hm_bs, ?_⟩
      rw [setWidth64_ofNat8]
      apply wp_call_of_spec; apply hWs
      wp_unfold; dsimp only [kissatIsWsSpec]; rw [isWsWord_ofUInt8]
      refine ⟨fun hws => by
          rw [ptr_step_1]
          exact ih (bs.length - (i + 1)) _ m (by omega) ⟨i + 1, by omega, by omega, rfl,
            by rw [hd_i, skipWs] at hinv; simpa [hws] using hinv, rfl, rfl⟩,
        fun hnws => hB _ m ⟨i, hi1, hi2,
          by rw [hd_i, skipWs, hnws] at hinv; simpa [← hd_i] using hinv, rfl, rfl⟩⟩
    · have hieq : i = bs.length := by omega
      subst hieq
      exact hB _ m ⟨bs.length, hi1, Nat.le_refl _, by simpa [skipWs] using hinv, rfl, rfl⟩
  · intro B L _ hL; wp_unfold
    exact hL (bs.length - (i0 + 1)) _ m ⟨i0 + 1, by omega, by omega, rfl, rfl, rfl, rfl⟩

private theorem digit_bounds' {b : UInt8} (hd : isDimacsDigit b = true) :
    48 ≤ b.toNat ∧ b.toNat - 48 < 10 ∧
      BitVec.ofNat 64 b.toNat - (48 : BitVec 64) = BitVec.ofNat 64 (b.toNat - 48) := by
  unfold isDimacsDigit at hd; grind

theorem kissat_read_nat_wp (Γ : Env)
    (hDig : ∀ args m Q X, kissatIsDigitSpec args m Q X →
      Γ "kissat_is_digit" [i64] [.bool] args m Q X)
    (hWs : ∀ args m Q X, kissatIsWsSpec args m Q X →
      Γ "kissat_is_ws" [i64] [.bool] args m Q X) :
    ∀ args m Q X, kissatReadNatSpec args m Q X →
      Func.wp Γ kissat_read_nat_body args m Q X := by
  rintro ⟨cend, d, ⟨⟩⟩ m Q X ⟨cnf_ptr, mv, nc, val, bs, i0, R, rfl, hfit, hi0, hm, hQ⟩
  unfold Func.wp kissat_read_nat_body; wp_unfold
  have hm_bs : (bytes cnf_ptr bs ⋆
      (dimacsState d mv nc (cnf_ptr + BitVec.ofNat 64 i0) val ⋆ R)) m := sep_ac hm
  have hm_d : (dimacsState d mv nc (cnf_ptr + BitVec.ofNat 64 i0) val ⋆
      (bytes cnf_ptr bs ⋆ R)) m := sep_ac hm
  refine ⟨_, load_dimacs_cur hm_d, ?_⟩
  rw [cursor_ule_rev_eq hfit hi0]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  refine ⟨fun heq => by
      have hnil : bs.drop i0 = [] := by simp [heq]
      simpa [hnil, parseNat] using hQ,
    fun hne => ?_⟩
  have hlt0 : i0 < bs.length := by omega
  have hd0 := List.drop_eq_getElem_cons hlt0
  refine ⟨_, load_bytes_at hlt0 (by omega) hm_bs, ?_⟩
  rw [setWidth64_ofNat8]
  apply wp_call_of_spec; apply hDig
  wp_unfold; dsimp only [kissatIsDigitSpec]; rw [isDigitWord_ofUInt8]
  refine ⟨fun hdig0 => ?_, fun hndig0 => by
      have hnone : parseNat (bs.drop i0) = none := by rw [hd0]; simp [parseNat, hndig0]
      simpa [hnone] using hQ⟩
  obtain ⟨_, _, hd0_bv⟩ := digit_bounds' hdig0
  have hp0 : parseNat (bs.drop i0) = parseDigitsAux (bs[i0].toNat - 48) (bs.drop (i0 + 1)) := by
    rw [hd0]; simp [parseNat, hdig0]
  rw [hd0_bv, ptr_step_1]
  refine wp_loop_break_group
    (fun (p_v, acc_v, ()) m' => ∃ v j rest,
      parseNat (bs.drop i0) = some (v, rest) ∧ v < dimacsBound ∧
      i0 < j ∧ j ≤ bs.length ∧ bs.drop j = rest ∧
      p_v = cnf_ptr + BitVec.ofNat 64 j ∧ acc_v = BitVec.ofNat 64 v ∧ m' = m)
    (fun r (p_v, acc_v, ()) m' => ∃ i acc,
      i0 < i ∧ i ≤ bs.length ∧ r = bs.length - i ∧ acc < dimacsBound ∧
      parseDigitsAux acc (bs.drop i) = parseNat (bs.drop i0) ∧
      p_v = cnf_ptr + BitVec.ofNat 64 i ∧ acc_v = BitVec.ofNat 64 acc ∧ m' = m)
    ?_ ?_ ?_
  · rintro _ ⟨p_v, acc_v, ⟨⟩⟩ m' ⟨v, j, rest, hpn, hv, hj1, hj2, hdrop, rfl, rfl, hm'⟩
    subst m'; wp_unfold
    obtain ⟨ok1, hm1⟩ := store_dimacs_cur (cnf_ptr + BitVec.ofNat 64 j) hm_d
    obtain ⟨ok2, hm2⟩ := store_dimacs_val (BitVec.ofNat 64 v) hm1
    rw [hpn] at hQ
    exact ⟨ok1, ok2, hQ j _ hv hj1 hj2 hdrop (sep_ac hm2)⟩
  · rintro B L r ⟨p_v, acc_v, ⟨⟩⟩ m' hB ih ⟨i, acc, hi1, hi2, rfl, hacc, hinv, rfl, rfl, hm'⟩
    subst m'; wp_unfold; rw [cursor_ult_eq hfit hi2]
    simp only [decide_eq_true_eq, decide_eq_false_iff_not]
    refine ⟨fun hlt => ?_, fun hnlt => ?_⟩
    · have hd_i := List.drop_eq_getElem_cons hlt
      refine ⟨_, load_bytes_at hlt (by omega) hm_bs, ?_⟩
      rw [setWidth64_ofNat8]
      apply wp_call_of_spec; apply hDig
      wp_unfold; dsimp only [kissatIsDigitSpec]; rw [isDigitWord_ofUInt8]
      refine ⟨fun hdig => ?_, fun hndig => ?_⟩
      · obtain ⟨_, _, hdbv⟩ := digit_bounds' hdig
        rw [hdbv]
        let acc2 := acc * 10 + (bs[i].toNat - 48)
        have hmul_add : BitVec.ofNat 64 acc * (10 : BitVec 64) +
            BitVec.ofNat 64 (bs[i].toNat - 48) = BitVec.ofNat 64 acc2 := by
          unfold dimacsBound at hacc; apply BitVec.eq_of_toNat_eq
          simp [acc2, BitVec.toNat_add, BitVec.toNat_mul]
        rw [hmul_add]
        have huge : (268435456 : BitVec 64).ule (BitVec.ofNat 64 acc2) =
            decide (268435456 ≤ acc2) := by
          unfold dimacsBound at hacc
          simp only [BitVec.ule, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (by omega : acc2 < 2 ^ 64)]
          rfl
        rw [huge]
        simp only [decide_eq_true_eq, decide_eq_false_iff_not]
        refine ⟨fun hge => ?_, fun hlt28 => ?_⟩
        · have hnone : parseNat (bs.drop i0) = none := by
            have hnb : ¬ acc2 < dimacsBound := by unfold dimacsBound; omega
            rw [← hinv, hd_i, parseDigitsAux]; simp [hdig, hnb, acc2]
          simpa [hnone] using hQ
        · rw [ptr_step_1]
          have hok : acc2 < dimacsBound := by unfold dimacsBound; omega
          exact ih (bs.length - (i + 1)) _ m (by omega)
            ⟨i + 1, acc2, by omega, by omega, rfl, hok,
              by rw [hd_i, parseDigitsAux] at hinv; simpa [hdig, hok, acc2] using hinv,
              rfl, rfl, rfl⟩
      · apply wp_call_of_spec; apply hWs
        wp_unfold; dsimp only [kissatIsWsSpec]; rw [isWsWord_ofUInt8]
        refine ⟨fun hws => hB _ m ⟨acc, i, bs.drop i,
            by rw [← hinv, hd_i, parseDigitsAux]; simp [hndig, hws],
            hacc, hi1, hi2, rfl, rfl, rfl, rfl⟩,
          fun hnws => by
            have hnone : parseNat (bs.drop i0) = none := by
              rw [← hinv, hd_i, parseDigitsAux]; simp [hndig, hnws]
            simpa [hnone] using hQ⟩
    · have hieq : i = bs.length := by omega
      subst hieq
      exact hB _ m ⟨acc, bs.length, [],
        by simpa [parseDigitsAux] using hinv.symm, hacc, hi1, Nat.le_refl _,
        by simp, rfl, rfl, rfl⟩
  · intro B L _ hL; wp_unfold
    exact hL (bs.length - (i0 + 1)) _ m ⟨i0 + 1, bs[i0].toNat - 48, by omega, by omega, rfl,
      by unfold dimacsBound; omega, hp0.symm, rfl, rfl, rfl⟩

end LeanQbe.T.Examples.Kissat
