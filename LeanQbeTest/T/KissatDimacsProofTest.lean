module

public import LeanQbe.T.Examples.Kissat.DimacsLemmas
public import LeanQbe.T.Examples.LratBytesLemmas
meta import LeanQbe.T.Examples.Kissat.DimacsLemmas1
meta import LeanQbe.T.Examples.LratBytes
import all Kraken.Mem
import all Kraken.Separation

/-!
# Verification, Non-Vacuity, and Axiom Audit for `X1` Stage B1 (`Kissat.DimacsLemmas`)

1. Executable `#guard` checks covering `runKissatCheckModel`, `nextLitPure`, `modelOfVals`,
   SAT / UNSAT / empty / comment+CRLF / wrong-model / unassigned / `mv > mv_max` / malformed inputs.
2. Concrete-memory source-level `Func.wp` non-vacuity theorems (`X = False`) for
   `kissat_check_model` (SAT positive, SAT negative-only, UNSAT, malformed) and
   `kissat_parse_header` (valid and malformed).
3. Single-line `#print axioms` audit on all key exported Stage-B1 theorems, checking strictly
   `[propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbeTest.T.KissatDimacsProofTest

open Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.LratBytes

/-! ## 1. Test vectors (SAT, UNSAT, and malformed DIMACS byte strings) -/

/-- Kernel-reducible SAT DIMACS bytes `"c sat\np cnf 2 3\n1 2 0\n-1 2 0\n-2 1 0\n"`. -/
def sat2Bytes : List UInt8 :=
  [ 99, 32, 115, 97, 116, 10
  , 112, 32, 99, 110, 102, 32, 50, 32, 51, 10
  , 49, 32, 50, 32, 48, 10
  , 45, 49, 32, 50, 32, 48, 10
  , 45, 50, 32, 49, 32, 48, 10 ]

/-- Kernel-reducible negative-literal SAT bytes `"p cnf 2 2\n-1 0\n-2 0\n"`. -/
def negSatBytes : List UInt8 :=
  [ 112, 32, 99, 110, 102, 32, 50, 32, 50, 10
  , 45, 49, 32, 48, 10
  , 45, 50, 32, 48, 10 ]

/-- Empty 0-var 0-clause CNF (`p cnf 0 0\n`). -/
def emptyCnfBytes : List UInt8 :=
  ("p cnf 0 0\n").toUTF8.toList

/-- Satisfiable formula with CRLF line endings, tabs, and header/body/trailing comments. -/
def crlfCommentBytes : List UInt8 :=
  ("c hdr\r\np  cnf\t 2   2\r\nc mid\r\n1 -2 0\r\n2 0\r\nc tail\r\n").toUTF8.toList

/-- Kernel-reducible 2-var 4-clause UNSAT bytes
`"p cnf 2 4\n1 2 0\n1 -2 0\n-1 2 0\n-1 -2 0\n"`. -/
def unsat2Bytes : List UInt8 :=
  [ 112, 32, 99, 110, 102, 32, 50, 32, 52, 10
  , 49, 32, 50, 32, 48, 10
  , 49, 32, 45, 50, 32, 48, 10
  , 45, 49, 32, 50, 32, 48, 10
  , 45, 49, 32, 45, 50, 32, 48, 10 ]

/-- Kernel-reducible malformed header `"p sat 1 1\n1 0\n"` (`sat` instead of `cnf`). -/
def badHeaderBytes : List UInt8 :=
  [112, 32, 115, 97, 116, 32, 49, 32, 49, 10, 49, 32, 48, 10]

/-- Out-of-bounds variable (`var 2 > mv 1`). -/
def oobVarBytes : List UInt8 :=
  ("p cnf 1 1\n2 0\n").toUTF8.toList

/-- Illegal `-0` literal. -/
def negZeroBytes : List UInt8 :=
  ("p cnf 1 1\n-0 0\n").toUTF8.toList

/-- Clause missing terminating `0`. -/
def missingZeroBytes : List UInt8 :=
  ("p cnf 1 1\n1\n").toUTF8.toList

/-- Trailing non-comment garbage after declared clauses. -/
def trailingGarbageBytes : List UInt8 :=
  ("p cnf 1 1\n1 0\nextra\n").toUTF8.toList

/-- More clauses than declared in header (`nc = 1`, two clauses present). -/
def extraClauseBytes : List UInt8 :=
  ("p cnf 1 1\n1 0\n-1 0\n").toUTF8.toList

/-- Fewer clauses than declared in header (`nc = 2`, one clause present). -/
def shortClauseBytes : List UInt8 :=
  ("p cnf 1 2\n1 0\n").toUTF8.toList

/-- Header `mv = 2^28` exceeding `dimacsBound`. -/
def overflowHeaderBytes : List UInt8 :=
  ("p cnf 268435456 0\n").toUTF8.toList

/-- `vals` encodings in `i8` stride-2 layout (`vals[2*v]`: `+1` = true, `-1` = `255` = false,
`0` = unassigned). -/
def valsTT : List UInt8 := [1, 255, 1, 255]
def valsTF : List UInt8 := [1, 255, 255, 1]
def valsFT : List UInt8 := [255, 1, 1, 255]
def valsFF : List UInt8 := [255, 1, 255, 1]
def valsUnassigned : List UInt8 := [0, 0, 0, 0]

/-! ## 2. Executable `#guard` checks -/

#guard dimacs_fns.length == 8
#guard dimacsModule.checkAcyclic == true
#guard sat2Bytes == ("c sat\np cnf 2 3\n1 2 0\n-1 2 0\n-2 1 0\n").toUTF8.toList
#guard negSatBytes == ("p cnf 2 2\n-1 0\n-2 0\n").toUTF8.toList
#guard unsat2Bytes == ("p cnf 2 4\n1 2 0\n1 -2 0\n-1 2 0\n-1 -2 0\n").toUTF8.toList
#guard badHeaderBytes == ("p sat 1 1\n1 0\n").toUTF8.toList

-- SAT positive & negative models
#guard runKissatCheckModel sat2Bytes valsTT 2 == true
#guard runKissatCheckModel sat2Bytes valsTF 2 == false
#guard runKissatCheckModel sat2Bytes valsFT 2 == false
#guard runKissatCheckModel sat2Bytes valsFF 2 == false
#guard runKissatCheckModel sat2Bytes valsUnassigned 2 == false
#guard runKissatCheckModel sat2Bytes valsTT 1 == false
#guard runKissatCheckModel sat2Bytes valsTT 8 == true

#guard runKissatCheckModel negSatBytes valsFF 2 == true
#guard runKissatCheckModel negSatBytes valsTT 2 == false
#guard runKissatCheckModel negSatBytes valsTF 2 == false
#guard runKissatCheckModel negSatBytes valsFT 2 == false

#guard runKissatCheckModel emptyCnfBytes [] 0 == true
#guard runKissatCheckModel crlfCommentBytes valsTT 2 == true
#guard runKissatCheckModel crlfCommentBytes valsFT 2 == false

-- UNSAT rejected under every assignment
#guard runKissatCheckModel unsat2Bytes valsTT 2 == false
#guard runKissatCheckModel unsat2Bytes valsTF 2 == false
#guard runKissatCheckModel unsat2Bytes valsFT 2 == false
#guard runKissatCheckModel unsat2Bytes valsFF 2 == false
#guard runKissatCheckModel nvDimacsBytes [1, 255] 1 == false
#guard runKissatCheckModel nvDimacsBytes [255, 1] 1 == false

-- Malformed inputs rejected
#guard runKissatCheckModel badHeaderBytes valsTT 2 == false
#guard runKissatCheckModel oobVarBytes valsTT 2 == false
#guard runKissatCheckModel negZeroBytes valsTT 2 == false
#guard runKissatCheckModel missingZeroBytes valsTT 2 == false
#guard runKissatCheckModel trailingGarbageBytes valsTT 2 == false
#guard runKissatCheckModel extraClauseBytes valsTT 2 == false
#guard runKissatCheckModel shortClauseBytes valsTT 2 == false
#guard runKissatCheckModel overflowHeaderBytes valsTT 2 == false

-- `nextLitPure` unit checks
#guard match nextLitPure 3 ("  c skip\n -2 0".toUTF8.toList) with
  | .lit 3 _ => true | _ => false
#guard match nextLitPure 3 ("1 0".toUTF8.toList) with
  | .lit 0 _ => true | _ => false
#guard match nextLitPure 3 (" 0 ".toUTF8.toList) with
  | .endClause _ => true | _ => false
#guard match nextLitPure 1 ("2 0".toUTF8.toList) with
  | .err => true | _ => false
#guard match nextLitPure 3 ("-0 0".toUTF8.toList) with
  | .err => true | _ => false
#guard match nextLitPure 3 ("c eof only".toUTF8.toList) with
  | .err => true | _ => false

-- `modelOfVals` agrees with `Core.checkModel` on `parseDimacs`
#guard match parseDimacs sat2Bytes with
  | some cnf => checkModel cnf (modelOfVals 2 valsTT) == true &&
      checkModel cnf (modelOfVals 2 valsTF) == false
  | none => false

/-! ## 3. Concrete-memory source-level non-vacuity (`Func.wp`, `X = False`) -/

abbrev nvBase : BitVec 64 := 0x1000#64
abbrev nvDimPtr (cnfBytes : List UInt8) : BitVec 64 :=
  nvBase + BitVec.ofNat 64 cnfBytes.length
abbrev nvValsPtr (cnfBytes : List UInt8) : BitVec 64 :=
  nvDimPtr cnfBytes + 32#64

def nvZeroDimacs : List UInt8 := bytes64 [0, 0, 0, 0]

private theorem nvZeroDimacs_length : nvZeroDimacs.length = 32 := by
  decide

private theorem concreteCheckMem_sep (cnfBytes valsBytes : List UInt8)
    (hcb : cnfBytes.length ≤ 4096) (hvb : valsBytes.length ≤ 4096) :
    (bytes nvBase cnfBytes ⋆ dimacsState (nvDimPtr cnfBytes) 0 0 0 0 ⋆
      bytes (nvValsPtr cnfBytes) valsBytes ⋆ emp)
      (((cnfBytes ++ nvZeroDimacs) ++ valsBytes).At nvBase) := by
  have hdlen : nvZeroDimacs.length = 32 := nvZeroDimacs_length
  have h1 := Mem.At_append_sep (cnfBytes ++ nvZeroDimacs) valsBytes nvBase
    (by simp only [List.length_append, hdlen]; omega)
  have he1 : nvBase + BitVec.ofNat 64 (cnfBytes ++ nvZeroDimacs).length = nvValsPtr cnfBytes := by
    simp only [nvValsPtr, nvDimPtr, List.length_append, hdlen]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  rw [he1] at h1
  have h2 := Mem.At_append_sep cnfBytes nvZeroDimacs nvBase (by omega)
  have h0 : (Eq (((cnfBytes ++ nvZeroDimacs) ++ valsBytes).At nvBase))
      (((cnfBytes ++ nvZeroDimacs) ++ valsBytes).At nvBase) := rfl
  rw [h1] at h0
  have hL : (bytes nvBase cnfBytes ⋆ dimacsState (nvDimPtr cnfBytes) 0 0 0 0)
      ((cnfBytes ++ nvZeroDimacs).At nvBase) := by
    have hs : (Eq (cnfBytes.At nvBase) ⋆ Eq (nvZeroDimacs.At (nvDimPtr cnfBytes)))
        ((cnfBytes ++ nvZeroDimacs).At nvBase) := by
      rw [← h2]
    refine sep_mono (fun f hf => ?_) (sep_mono_r (fun g hg => ?_) hs)
    · rw [bytes]; exact hf
    · rw [← hg]; exact dimacsState_bytes (nvDimPtr cnfBytes) 0 0 0 0
  have hAll : ((bytes nvBase cnfBytes ⋆ dimacsState (nvDimPtr cnfBytes) 0 0 0 0) ⋆
      bytes (nvValsPtr cnfBytes) valsBytes)
      (((cnfBytes ++ nvZeroDimacs) ++ valsBytes).At nvBase) := by
    refine sep_mono (fun f hf => by rw [← hf]; exact hL)
      (sep_mono_r (fun g hg => by rw [bytes]; exact hg) h0)
  rwa [Std.ExtHashMap.sep_emp]

private theorem concreteHdrMem_sep (cnfBytes : List UInt8) (hcb : cnfBytes.length ≤ 4096) :
    (bytes nvBase cnfBytes ⋆ dimacsState (nvDimPtr cnfBytes) 0 0 0 0 ⋆ emp)
      ((cnfBytes ++ nvZeroDimacs).At nvBase) := by
  have hdlen : nvZeroDimacs.length = 32 := nvZeroDimacs_length
  have h2 := Mem.At_append_sep cnfBytes nvZeroDimacs nvBase (by omega)
  have hs : (Eq (cnfBytes.At nvBase) ⋆ Eq (nvZeroDimacs.At (nvDimPtr cnfBytes)))
      ((cnfBytes ++ nvZeroDimacs).At nvBase) := by
    rw [← h2]
  have hL : (bytes nvBase cnfBytes ⋆ dimacsState (nvDimPtr cnfBytes) 0 0 0 0)
      ((cnfBytes ++ nvZeroDimacs).At nvBase) :=
    sep_mono (fun f hf => by rw [bytes]; exact hf)
      (sep_mono_r (fun g hg => by rw [← hg]; exact dimacsState_bytes (nvDimPtr cnfBytes) 0 0 0 0)
        hs)
  rwa [Std.ExtHashMap.sep_emp]

/-- Non-vacuity (SAT positive): `kissat_check_model` returns `(1, ())` with `X = False` on
`sat2Bytes` + `valsTT`, certifying `∃ cnf, parseDimacs sat2Bytes = some cnf ∧ ¬ cnf.Unsat ∧
∃ α, cnf.Sat α`. -/
theorem nv_sat :
    let m0 : Mem 64 := ((sat2Bytes ++ nvZeroDimacs) ++ valsTT).At nvBase
    Func.wp dimacsExactEnv kissat_check_model_body
      (nvBase, nvDimPtr sat2Bytes, nvDimPtr sat2Bytes, nvValsPtr sat2Bytes, 2#64, ())
      m0
      (fun rs m' => rs = (1#64, ()) ∧
        (∃ cnf, parseDimacs sat2Bytes = some cnf ∧ ¬ cnf.Unsat ∧ ∃ α, cnf.Sat α) ∧
        ∃ mv' nc' cur' val',
          (bytes nvBase sat2Bytes ⋆ dimacsState (nvDimPtr sat2Bytes) mv' nc' cur' val' ⋆
            bytes (nvValsPtr sat2Bytes) valsTT ⋆ emp) m')
      (fun _ _ _ _ => False) := by
  intro m0
  have hrun : runKissatCheckModel sat2Bytes valsTT 2 = true := by decide
  have hsat : ∃ cnf, parseDimacs sat2Bytes = some cnf ∧ ¬ cnf.Unsat ∧ ∃ α, cnf.Sat α := by
    obtain ⟨cnf, _, hp, _, hnu, hs⟩ := runKissatCheckModel_sound hrun
    exact ⟨cnf, hp, hnu, hs⟩
  exact dimacsExactEnv_sound kissat_check_model (by simp [dimacs_fns]) _ m0 _ _
    ⟨0, 0, 0, 0, sat2Bytes, valsTT, 2, emp, rfl, rfl, by decide, by decide, by decide, by decide,
      concreteCheckMem_sep sat2Bytes valsTT (by decide) (by decide),
      fun r mv' nc' cur' val' m' hr hm' => by
        rw [hrun] at hr; simp only [↓reduceIte] at hr; subst hr
        exact ⟨rfl, hsat, mv', nc', cur', val', hm'⟩⟩

/-- Non-vacuity (SAT negative literals): `kissat_check_model` returns `(1, ())` with `X = False`
on `negSatBytes` + `valsFF`, exercising the signed `i8` `< 0` branch. -/
theorem nv_neg_sat :
    let m0 : Mem 64 := ((negSatBytes ++ nvZeroDimacs) ++ valsFF).At nvBase
    Func.wp dimacsExactEnv kissat_check_model_body
      (nvBase, nvDimPtr negSatBytes, nvDimPtr negSatBytes, nvValsPtr negSatBytes, 2#64, ())
      m0
      (fun rs m' => rs = (1#64, ()) ∧
        (∃ cnf, parseDimacs negSatBytes = some cnf ∧ ¬ cnf.Unsat ∧ ∃ α, cnf.Sat α) ∧
        ∃ mv' nc' cur' val',
          (bytes nvBase negSatBytes ⋆ dimacsState (nvDimPtr negSatBytes) mv' nc' cur' val' ⋆
            bytes (nvValsPtr negSatBytes) valsFF ⋆ emp) m')
      (fun _ _ _ _ => False) := by
  intro m0
  have hrun : runKissatCheckModel negSatBytes valsFF 2 = true := by decide
  have hsat : ∃ cnf, parseDimacs negSatBytes = some cnf ∧ ¬ cnf.Unsat ∧ ∃ α, cnf.Sat α := by
    obtain ⟨cnf, _, hp, _, hnu, hs⟩ := runKissatCheckModel_sound hrun
    exact ⟨cnf, hp, hnu, hs⟩
  exact dimacsExactEnv_sound kissat_check_model (by simp [dimacs_fns]) _ m0 _ _
    ⟨0, 0, 0, 0, negSatBytes, valsFF, 2, emp, rfl, rfl, by decide, by decide, by decide, by decide,
      concreteCheckMem_sep negSatBytes valsFF (by decide) (by decide),
      fun r mv' nc' cur' val' m' hr hm' => by
        rw [hrun] at hr; simp only [↓reduceIte] at hr; subst hr
        exact ⟨rfl, hsat, mv', nc', cur', val', hm'⟩⟩

/-- Non-vacuity (UNSAT): `kissat_check_model` returns `(0, ())` with `X = False` on
`unsat2Bytes`. -/
theorem nv_unsat :
    let m0 : Mem 64 := ((unsat2Bytes ++ nvZeroDimacs) ++ valsTT).At nvBase
    Func.wp dimacsExactEnv kissat_check_model_body
      (nvBase, nvDimPtr unsat2Bytes, nvDimPtr unsat2Bytes, nvValsPtr unsat2Bytes, 2#64, ())
      m0
      (fun rs m' => rs = (0#64, ()) ∧
        ∃ mv' nc' cur' val',
          (bytes nvBase unsat2Bytes ⋆ dimacsState (nvDimPtr unsat2Bytes) mv' nc' cur' val' ⋆
            bytes (nvValsPtr unsat2Bytes) valsTT ⋆ emp) m')
      (fun _ _ _ _ => False) := by
  intro m0
  have hrun : runKissatCheckModel unsat2Bytes valsTT 2 = false := by decide
  exact dimacsExactEnv_sound kissat_check_model (by simp [dimacs_fns]) _ m0 _ _
    ⟨0, 0, 0, 0, unsat2Bytes, valsTT, 2, emp, rfl, rfl, by decide, by decide, by decide, by decide,
      concreteCheckMem_sep unsat2Bytes valsTT (by decide) (by decide),
      fun r mv' nc' cur' val' m' hr hm' => by
        rw [hrun] at hr; simp only [Bool.false_eq_true, ↓reduceIte] at hr; subst hr
        exact ⟨rfl, mv', nc', cur', val', hm'⟩⟩

/-- Non-vacuity (malformed DIMACS): `kissat_check_model` returns `(0, ())` with `X = False` on
`badHeaderBytes`. -/
theorem nv_malformed :
    let m0 : Mem 64 := ((badHeaderBytes ++ nvZeroDimacs) ++ valsTT).At nvBase
    Func.wp dimacsExactEnv kissat_check_model_body
      (nvBase, nvDimPtr badHeaderBytes, nvDimPtr badHeaderBytes, nvValsPtr badHeaderBytes, 2#64, ())
      m0
      (fun rs m' => rs = (0#64, ()) ∧
        ∃ mv' nc' cur' val',
          (bytes nvBase badHeaderBytes ⋆ dimacsState (nvDimPtr badHeaderBytes) mv' nc' cur' val' ⋆
            bytes (nvValsPtr badHeaderBytes) valsTT ⋆ emp) m')
      (fun _ _ _ _ => False) := by
  intro m0
  have hrun : runKissatCheckModel badHeaderBytes valsTT 2 = false := by decide
  exact dimacsExactEnv_sound kissat_check_model (by simp [dimacs_fns]) _ m0 _ _
    ⟨0, 0, 0, 0, badHeaderBytes, valsTT, 2, emp, rfl, rfl,
      by decide, by decide, by decide, by decide,
      concreteCheckMem_sep badHeaderBytes valsTT (by decide) (by decide),
      fun r mv' nc' cur' val' m' hr hm' => by
        rw [hrun] at hr; simp only [Bool.false_eq_true, ↓reduceIte] at hr; subst hr
        exact ⟨rfl, mv', nc', cur', val', hm'⟩⟩

/-- Non-vacuity (`kissat_parse_header` on `sat2Bytes`): returns `(true, ())` with `mv = 2, nc = 3`
and `X = False`. -/
theorem nv_hdr_ok :
    let m0 : Mem 64 := (sat2Bytes ++ nvZeroDimacs).At nvBase
    Func.wp dimacsEnv kissat_parse_header_body
      (nvBase, nvDimPtr sat2Bytes, nvDimPtr sat2Bytes, ())
      m0
      (fun rs m' => rs = (true, ()) ∧
        ∃ j, j ≤ sat2Bytes.length ∧
          (bytes nvBase sat2Bytes ⋆
            dimacsState (nvDimPtr sat2Bytes) 2#64 3#64 (nvBase + BitVec.ofNat 64 j) 3#64 ⋆
            emp) m')
      (fun _ _ _ _ => False) := by
  intro m0
  have hhdr : (parseHeader sat2Bytes).map (fun (mv, nc, _) => (mv, nc)) = some (2, 3) := by decide
  refine kissat_parse_header_spec (R := emp) (by decide)
    (concreteHdrMem_sep sat2Bytes (by decide)) ?_
  cases h : parseHeader sat2Bytes with
  | none => rw [h] at hhdr; cases hhdr
  | some p =>
    rcases p with ⟨mv, nc, rest⟩
    rw [h] at hhdr
    have heq : (mv, nc) = (2, 3) := Option.some.inj hhdr
    rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
    intro j m' _ _ hj _ hm'
    exact ⟨rfl, j, hj, hm'⟩

/-- Non-vacuity (`kissat_parse_header` on `badHeaderBytes`): returns `(false, ())` with
`X = False`. -/
theorem nv_hdr_err :
    let m0 : Mem 64 := (badHeaderBytes ++ nvZeroDimacs).At nvBase
    Func.wp dimacsEnv kissat_parse_header_body
      (nvBase, nvDimPtr badHeaderBytes, nvDimPtr badHeaderBytes, ())
      m0
      (fun rs m' => rs = (false, ()) ∧
        ∃ mv' nc' cur' val',
          (bytes nvBase badHeaderBytes ⋆
            dimacsState (nvDimPtr badHeaderBytes) mv' nc' cur' val' ⋆ emp) m')
      (fun _ _ _ _ => False) := by
  intro m0
  have hhdr : parseHeader badHeaderBytes = none := by decide
  refine kissat_parse_header_spec (R := emp) (by decide)
    (concreteHdrMem_sep badHeaderBytes (by decide)) ?_
  rw [hhdr]
  intro mv' nc' cur' val' m' hm'
  exact ⟨rfl, mv', nc', cur', val', hm'⟩

/-- Non-vacuity (`kissat_check_model_sound` under `dimacsEnv` on `sat2Bytes` + `valsTT`). -/
theorem nv_sound :
    let m0 : Mem 64 := ((sat2Bytes ++ nvZeroDimacs) ++ valsTT).At nvBase
    Func.wp dimacsEnv kissat_check_model_body
      (nvBase, nvDimPtr sat2Bytes, nvDimPtr sat2Bytes, nvValsPtr sat2Bytes, 2#64, ())
      m0
      (fun (r, ()) m' =>
        (r = 0#64 ∨ r = 1#64) ∧
        (r = 1#64 → ∃ cnf, parseDimacs sat2Bytes = some cnf ∧ ¬ cnf.Unsat ∧ ∃ α, cnf.Sat α) ∧
        ∃ mv' nc' cur' val',
          (bytes nvBase sat2Bytes ⋆ dimacsState (nvDimPtr sat2Bytes) mv' nc' cur' val' ⋆
            bytes (nvValsPtr sat2Bytes) valsTT ⋆ emp) m')
      (fun _ _ _ _ => False) :=
  kissat_check_model_sound (mv_max := 2) (R := emp) (by decide) (by decide) (by decide) (by decide)
    (concreteCheckMem_sep sat2Bytes valsTT (by decide) (by decide))

/-! ## 4. Single-line `#print axioms` audit on exported theorems -/

#print axioms LeanQbe.T.Examples.Kissat.dimacsFns_wf
#print axioms LeanQbe.T.Examples.Kissat.runKissatCheckModel_sound
#print axioms LeanQbe.T.Examples.Kissat.kissat_parse_header_wp
#print axioms LeanQbe.T.Examples.Kissat.kissat_next_lit_wp
#print axioms LeanQbe.T.Examples.Kissat.kissat_check_model_wp
#print axioms LeanQbe.T.Examples.Kissat.dimacsExactEnv_sound
#print axioms LeanQbe.T.Examples.Kissat.dimacsExactEnv_moduleOk
#print axioms LeanQbe.T.Examples.Kissat.dimacsEnv_sound
#print axioms LeanQbe.T.Examples.Kissat.dimacsEnv_moduleOk
#print axioms LeanQbe.T.Examples.Kissat.kissat_check_model_sound
#print axioms LeanQbe.T.Examples.Kissat.kissat_parse_header_spec
#print axioms LeanQbe.T.Examples.Kissat.kissat_next_lit_spec
#print axioms LeanQbe.T.Examples.Kissat.kissat_skip_ws_comments_spec
#print axioms nv_sat
#print axioms nv_neg_sat
#print axioms nv_unsat
#print axioms nv_malformed
#print axioms nv_hdr_ok
#print axioms nv_hdr_err
#print axioms nv_sound

end LeanQbeTest.T.KissatDimacsProofTest
