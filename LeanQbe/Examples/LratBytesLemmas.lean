module

public import LeanQbe.Examples.LratBytesDimacsLemmas
public import LeanQbe.Examples.LratBytesRupLemmas
public import LeanQbe.Examples.LratBytesCheckLemmas
public import LeanQbe.MainLemmas
import all Kraken.Mem
import all Kraken.Separation

/-!
# Total-Correctness Proofs for the Untrusted-Bytes LRAT Checker (`lratBytesFns`)

Links the per-function and pure-mirror proofs from:
- `LratBytesSpec.lean`: `lratBytesFns_wf`, pure mirror `runLratCheckBytes`, `WorkState`, contracts
- `LratBytesDimacsLemmas.lean`: `lbParseDimacsHeader_correct`, `lbParseDimacsBody_correct`,
  `parseBodyPure_sound`, `ValidDimacsCnf`, `parseDimacs_encodeDimacs`
- `LratBytesRupLemmas.lean`: `lbReadAddLits_correct`, `lbRupCheck_correct`, `rupCheckPure_sound`
- `LratBytesCheckLemmas.lean`: `lbCheckPrf_correct_of`, `lratCheckBytes_exact_of`,
  `runLratCheckBytes_sound_of`

and exports:
1. `runLratCheckBytes_sound`: if `runLratCheckBytes cnfBytes prfBytes work_len = true`, then
   `∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat`.
2. `lratBytesExactEnv` and `lratBytesExactEnv_sound`: exact decision contract
   (`r = if runLratCheckBytes cnfBytes prfBytes work_len then 1 else 0`) for `lratBytesFns`.
3. `lratBytesEnv` and `lratBytesEnv_sound`: top-level soundness contract `lratCheckBytesSpec`
   (`r = 0 ∨ r = 1`, `r = 1 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat`, memory restored,
   `exits = []` / `X` unconstrained) for `compileModule` + `compile_sound`.
4. `lratCheckBytesEncodedSpec` + `lratCheckBytes_encoded_correct`: combining `lratCheckBytesSpec`
   with `parseDimacs_encodeDimacs` so callers starting from `ValidDimacsCnf cnf` get `r = 1 → cnf.Unsat`
   without `parseDimacs` in the postcondition.
5. Concrete accepting (`nvDimacsBytes`, `nvLratAcceptBytes`, `work_len = 512` → `r = 1 ∧ nvBytesCnf.Unsat`)
   and rejecting (`nvDimacsBytes`, `nvLratRejectBytes`, `work_len = 512` → `r = 0`) instances
   (`nvAccept_run`, `nvReject_run`, `nvBytesCnf_unsat`, `lratBytesAcceptEnv_sound`,
   `lratBytesRejectEnv_sound`, `lratCheckBytes_accepts_nonvacuous`,
   `lratCheckBytes_rejects_nonvacuous`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.LratBytes

open Std.ExtHashMap Std.Sat

/-! ## 1. Pure mirror soundness -/

/-- Pure soundness of `runLratCheckBytes`: whenever the mirror returns `true`, `parseDimacs cnfBytes`
succeeds on an unsatisfiable `CNF Nat`. -/
theorem runLratCheckBytes_sound {cnfBytes prfBytes : List UInt8} {work_len : Nat}
    (hrun : runLratCheckBytes cnfBytes prfBytes work_len = true) :
    ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat :=
  runLratCheckBytes_sound_of (@parseBodyPure_sound) (@rupCheckPure_sound) hrun

/-! ## 2. Closed per-function correctness and exact module environment -/

/-- Closed correctness of `lb_check_prf` given `lbReadAddLitsSpec` and `lbRupCheckSpec` in `Γ`. -/
theorem lbCheckPrf_correct (Γ : Env)
    (hReadAddLits : ∀ args m Q X, lbReadAddLitsSpec args m Q X → Γ "lb_read_add_lits" args m Q X)
    (hRupCheck : ∀ args m Q X, lbRupCheckSpec args m Q X → Γ "lb_rup_check" args m Q X) :
    ∀ args m Q X, lbCheckPrfSpec args m Q X → Func.spec Γ lbCheckPrf args m Q X :=
  lbCheckPrf_correct_of Γ hReadAddLits hRupCheck

/-- Closed exact correctness of `lrat_check_bytes` given its three direct callees in `Γ`. -/
theorem lratCheckBytes_exact (Γ : Env)
    (hParseHeader : ∀ args m Q X,
      lbParseDimacsHeaderSpec args m Q X → Γ "lb_parse_dimacs_header" args m Q X)
    (hParseBody : ∀ args m Q X,
      lbParseDimacsBodySpec args m Q X → Γ "lb_parse_dimacs_body" args m Q X)
    (hCheckPrf : ∀ args m Q X,
      lbCheckPrfSpec args m Q X → Γ "lb_check_prf" args m Q X) :
    ∀ args m Q X, lratCheckBytesExactSpec args m Q X → Func.spec Γ lratCheckBytes args m Q X :=
  lratCheckBytes_exact_of Γ hParseHeader hParseBody hCheckPrf

/-- Weakening from `lratCheckBytesSpec` to `lratCheckBytesExactSpec` via `runLratCheckBytes_sound`. -/
theorem lratCheckBytesExactSpec_of_spec {args : List Val} {m : Mem 64} {Q : Post} {X : XPost}
    (h : lratCheckBytesSpec args m Q X) :
    lratCheckBytesExactSpec args m Q X := by
  obtain ⟨cnf_ptr, prf_ptr, work_ptr, cnfBytes, prfBytes, work_len, R_mem,
    hargs, hcnf, hprf, hwork, hm, hQ⟩ := h
  refine ⟨cnf_ptr, prf_ptr, work_ptr, cnfBytes, prfBytes, work_len, R_mem,
    hargs, hcnf, hprf, hwork, hm, fun r m' hr hm' => ?_⟩
  cases hrun : runLratCheckBytes cnfBytes prfBytes work_len
  · grind
  · rw [hrun] at hr
    simp only [↓reduceIte] at hr
    subst hr
    exact hQ 1 m' (Or.inr rfl) (fun _ => runLratCheckBytes_sound hrun) hm'

/-- Closed top-level soundness of `lrat_check_bytes` against `lratCheckBytesSpec`. -/
theorem lratCheckBytes_correct (Γ : Env)
    (hParseHeader : ∀ args m Q X,
      lbParseDimacsHeaderSpec args m Q X → Γ "lb_parse_dimacs_header" args m Q X)
    (hParseBody : ∀ args m Q X,
      lbParseDimacsBodySpec args m Q X → Γ "lb_parse_dimacs_body" args m Q X)
    (hCheckPrf : ∀ args m Q X,
      lbCheckPrfSpec args m Q X → Γ "lb_check_prf" args m Q X) :
    ∀ args m Q X, lratCheckBytesSpec args m Q X → Func.spec Γ lratCheckBytes args m Q X :=
  fun args m Q X hspec =>
    lratCheckBytes_exact Γ hParseHeader hParseBody hCheckPrf args m Q X
      (lratCheckBytesExactSpec_of_spec hspec)

/-- Parameterized specification environment for `lratBytesFns` with configurable `"lrat_check_bytes"`
contract `mainSpec`. -/
abbrev mkLratBytesEnv (mainSpec : Spec) : Env
  | "lb_parse_dimacs_header" => lbParseDimacsHeaderSpec
  | "lb_parse_dimacs_body"   => lbParseDimacsBodySpec
  | "lb_read_add_lits"       => lbReadAddLitsSpec
  | "lb_rup_check"           => lbRupCheckSpec
  | "lb_check_prf"           => lbCheckPrfSpec
  | "lrat_check_bytes"       => mainSpec
  | _                        => fun _ _ _ _ => False

private theorem mkLratBytesEnv_sound (mainSpec : Spec)
    (hweaken : ∀ args m Q X, mainSpec args m Q X → lratCheckBytesExactSpec args m Q X) :
    ∀ f ∈ lratBytesFns, ∀ args m Q X,
      mkLratBytesEnv mainSpec f.name args m Q X →
      Func.spec (mkLratBytesEnv mainSpec) f.body args m Q X := by
  intro f hf args m Q X hspec
  simp only [lratBytesFns, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lbParseDimacsHeader_correct (mkLratBytesEnv mainSpec) args m Q X hspec
  · exact lbParseDimacsBody_correct (mkLratBytesEnv mainSpec) args m Q X hspec
  · exact lbReadAddLits_correct (mkLratBytesEnv mainSpec) args m Q X hspec
  · exact lbRupCheck_correct (mkLratBytesEnv mainSpec) args m Q X hspec
  · exact lbCheckPrf_correct (mkLratBytesEnv mainSpec)
      (fun _ _ _ _ h => h) (fun _ _ _ _ h => h) args m Q X hspec
  · exact lratCheckBytes_exact (mkLratBytesEnv mainSpec)
      (fun _ _ _ _ h => h) (fun _ _ _ _ h => h) (fun _ _ _ _ h => h) args m Q X
      (hweaken args m Q X hspec)

/-- Function-specification environment giving `lrat_check_bytes` its exact decision contract
`lratCheckBytesExactSpec` (`r = if runLratCheckBytes cnfBytes prfBytes work_len then 1 else 0`). -/
def lratBytesExactEnv : Env := mkLratBytesEnv lratCheckBytesExactSpec

@[simp] theorem lratBytesExactEnv_entry :
    lratBytesExactEnv "lrat_check_bytes" = lratCheckBytesExactSpec := rfl

/-- All 6 functions in `lratBytesFns` satisfy their contracts in `lratBytesExactEnv`. -/
theorem lratBytesExactEnv_sound :
    ∀ f ∈ lratBytesFns, ∀ args m Q X,
      lratBytesExactEnv f.name args m Q X → Func.spec lratBytesExactEnv f.body args m Q X :=
  mkLratBytesEnv_sound lratCheckBytesExactSpec (fun _ _ _ _ h => h)

/-! ## 3. Top-level soundness environment (`lratBytesEnv`, `lratBytesEnv_sound`) -/

/-- Function-specification environment for `compileModule` / `compile_sound` exposing
`lratCheckBytesSpec` at `"lrat_check_bytes"`. -/
def lratBytesEnv : Env := mkLratBytesEnv lratCheckBytesSpec

@[simp] theorem lratBytesEnv_entry :
    lratBytesEnv "lrat_check_bytes" = lratCheckBytesSpec := rfl

/-- All 6 functions in `lratBytesFns` satisfy their contracts in `lratBytesEnv`. -/
theorem lratBytesEnv_sound :
    ∀ f ∈ lratBytesFns, ∀ args m Q X,
      lratBytesEnv f.name args m Q X → Func.spec lratBytesEnv f.body args m Q X :=
  mkLratBytesEnv_sound lratCheckBytesSpec (fun _ _ _ _ => lratCheckBytesExactSpec_of_spec)

/-! ## 4. Trivial-postcondition corollary for encoded `CNF Nat` formulas -/

/-- Source contract specialized to `(encodeDimacs cnf)` for any `ValidDimacsCnf cnf`:
the postcondition mentions only `r = 0 ∨ r = 1` and `r = 1 → cnf.Unsat` (no parser in the conclusion). -/
def lratCheckBytesEncodedSpec (cnf : CNF Nat) : Spec := fun args m Q _ =>
  ValidDimacsCnf cnf ∧
  ∃ (cnf_ptr prf_ptr work_ptr : Val) (prfBytes : List UInt8) (work_len : Nat)
    (R_mem : Mem 64 → Prop),
    args = [cnf_ptr, BitVec.ofNat 64 (encodeDimacs cnf).length,
            prf_ptr, BitVec.ofNat 64 prfBytes.length,
            work_ptr, BitVec.ofNat 64 work_len] ∧
    cnf_ptr.toNat + (encodeDimacs cnf).length < 2 ^ 64 ∧
    prf_ptr.toNat + prfBytes.length < 2 ^ 64 ∧
    work_ptr.toNat + work_len < 2 ^ 64 ∧
    ((Eq ((encodeDimacs cnf).At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆ region work_ptr work_len) ⋆
      R_mem) m ∧
    ∀ (r : Val) (m' : Mem 64),
      (r = 0 ∨ r = 1) →
      (r = 1 → cnf.Unsat) →
      ((Eq ((encodeDimacs cnf).At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆ region work_ptr work_len) ⋆
        R_mem) m' →
      Q [r] m'

theorem lratCheckBytesSpec_of_encoded {cnf : CNF Nat} {args : List Val} {m : Mem 64}
    {Q : Post} {X : XPost}
    (h : lratCheckBytesEncodedSpec cnf args m Q X) :
    lratCheckBytesSpec args m Q X := by
  obtain ⟨hvalid, cnf_ptr, prf_ptr, work_ptr, prfBytes, work_len, R_mem,
    hargs, hcnf, hprf, hwork, hm, hQ⟩ := h
  refine ⟨cnf_ptr, prf_ptr, work_ptr, encodeDimacs cnf, prfBytes, work_len, R_mem,
    hargs, hcnf, hprf, hwork, hm, fun r m' hr01 hunsat hm' => ?_⟩
  refine hQ r m' hr01 (fun hr1 => ?_) hm'
  obtain ⟨cnf', hp, hu⟩ := hunsat hr1
  rw [parseDimacs_encodeDimacs hvalid] at hp
  grind

theorem lratCheckBytes_encoded_correct (cnf : CNF Nat) :
    ∀ args m Q X,
      lratCheckBytesEncodedSpec cnf args m Q X →
      Func.spec lratBytesEnv lratCheckBytes args m Q X :=
  fun args m Q X h =>
    lratBytesEnv_sound ⟨"lrat_check_bytes", lratCheckBytes⟩ (by simp [lratBytesFns])
      args m Q X (lratCheckBytesSpec_of_encoded h)

/-! ## 5. Concrete accepting and rejecting instances -/

/-- `nvBytesCnf` satisfies `ValidDimacsCnf`. -/
theorem nvBytesCnf_valid : ValidDimacsCnf nvBytesCnf := by
  refine ⟨?_, ?_, ?_⟩
  · simp [nvBytesCnf, cnfMaxVar, dimacsBound, CNF.empty, CNF.add]
  · simp [nvBytesCnf, dimacsBound, CNF.empty, CNF.add]
  · intro cl hcl l hl
    simp [nvBytesCnf, CNF.empty, CNF.add] at hcl
    rcases hcl with rfl | rfl <;> simp at hl <;> subst hl <;> omega

/-- Explicit 19-byte expansion of `nvDimacsBytes` (`"p cnf 1 2\n1 0\n-1 0\n"`). -/
theorem nvDimacsBytes_eq :
    nvDimacsBytes =
      [112, 32, 99, 110, 102, 32, 49, 32, 50, 10, 49, 32, 48, 10, 45, 49, 32, 48, 10] := by
  simp [nvDimacsBytes, nvBytesCnf, encodeDimacs, cnfMaxVar, encodeDimacsClause,
    encodeDimacsLit, natToBytes, natToBytesAux, CNF.empty, CNF.add]

@[simp] theorem nvDimacsBytes_length : nvDimacsBytes.length = 19 := by
  rw [nvDimacsBytes_eq]; rfl

@[simp] theorem nvLratAcceptBytes_length : nvLratAcceptBytes.length = 15 := rfl

@[simp] theorem nvLratRejectBytes_length : nvLratRejectBytes.length = 5 := rfl

/-- `parseDimacs nvDimacsBytes = some nvBytesCnf` via `parseDimacs_encodeDimacs`. -/
theorem nvDimacsBytes_parse : parseDimacs nvDimacsBytes = some nvBytesCnf :=
  parseDimacs_encodeDimacs nvBytesCnf_valid

/-- Concrete accepting execution: `runLratCheckBytes` accepts `(nvDimacsBytes, nvLratAcceptBytes, 512)`
(exercising DIMACS parsing, `'a'` RUP step, `'d'` clause deletion, and empty-clause derivation). -/
theorem nvAccept_run : runLratCheckBytes nvDimacsBytes nvLratAcceptBytes 512 = true := by
  rw [nvDimacsBytes_eq]; rfl

/-- Concrete rejecting execution: `runLratCheckBytes` rejects `(nvDimacsBytes, nvLratRejectBytes, 512)`. -/
theorem nvReject_run : runLratCheckBytes nvDimacsBytes nvLratRejectBytes 512 = false := by
  rw [nvDimacsBytes_eq]; rfl

/-- Unconditional unsatisfiability of `nvBytesCnf` proved via `runLratCheckBytes_sound`! -/
theorem nvBytesCnf_unsat : nvBytesCnf.Unsat := by
  obtain ⟨cnf, hp, hu⟩ := runLratCheckBytes_sound nvAccept_run
  rw [nvDimacsBytes_parse] at hp
  grind

/-- Specialized accepting contract for `(nvDimacsBytes, nvLratAcceptBytes, 512)`:
returns `r = 1` and `nvBytesCnf.Unsat` with `X` unconstrained (`exits = []`). -/
def lratCheckBytesAcceptSpec : Spec := fun args m Q _ =>
  ∃ (cnf_ptr prf_ptr work_ptr : Val) (R_mem : Mem 64 → Prop),
    args = [cnf_ptr, BitVec.ofNat 64 nvDimacsBytes.length,
            prf_ptr, BitVec.ofNat 64 nvLratAcceptBytes.length,
            work_ptr, 512#64] ∧
    cnf_ptr.toNat + nvDimacsBytes.length < 2 ^ 64 ∧
    prf_ptr.toNat + nvLratAcceptBytes.length < 2 ^ 64 ∧
    work_ptr.toNat + 512 < 2 ^ 64 ∧
    ((Eq (nvDimacsBytes.At cnf_ptr) ⋆ Eq (nvLratAcceptBytes.At prf_ptr) ⋆ region work_ptr 512) ⋆
      R_mem) m ∧
    ∀ (m' : Mem 64),
      nvBytesCnf.Unsat →
      ((Eq (nvDimacsBytes.At cnf_ptr) ⋆ Eq (nvLratAcceptBytes.At prf_ptr) ⋆ region work_ptr 512) ⋆
        R_mem) m' →
      Q [1] m'

theorem lratCheckBytesExactSpec_of_accept {args : List Val} {m : Mem 64} {Q : Post} {X : XPost}
    (h : lratCheckBytesAcceptSpec args m Q X) :
    lratCheckBytesExactSpec args m Q X := by
  obtain ⟨cnf_ptr, prf_ptr, work_ptr, R_mem, hargs, hcnf, hprf, hwork, hm, hQ⟩ := h
  refine ⟨cnf_ptr, prf_ptr, work_ptr, nvDimacsBytes, nvLratAcceptBytes, 512, R_mem,
    hargs, hcnf, hprf, hwork, hm, fun r m' hr hm' => ?_⟩
  rw [nvAccept_run] at hr
  simp only [↓reduceIte] at hr
  subst hr
  exact hQ m' nvBytesCnf_unsat hm'

/-- Function environment exposing `lratCheckBytesAcceptSpec` at `"lrat_check_bytes"`. -/
def lratBytesAcceptEnv : Env := mkLratBytesEnv lratCheckBytesAcceptSpec

@[simp] theorem lratBytesAcceptEnv_entry :
    lratBytesAcceptEnv "lrat_check_bytes" = lratCheckBytesAcceptSpec := rfl

theorem lratBytesAcceptEnv_sound :
    ∀ f ∈ lratBytesFns, ∀ args m Q X,
      lratBytesAcceptEnv f.name args m Q X → Func.spec lratBytesAcceptEnv f.body args m Q X :=
  mkLratBytesEnv_sound lratCheckBytesAcceptSpec (fun _ _ _ _ => lratCheckBytesExactSpec_of_accept)

/-- Specialized rejecting contract for `(nvDimacsBytes, nvLratRejectBytes, 512)`:
returns `r = 0` with `X` unconstrained (`exits = []`). -/
def lratCheckBytesRejectSpec : Spec := fun args m Q _ =>
  ∃ (cnf_ptr prf_ptr work_ptr : Val) (R_mem : Mem 64 → Prop),
    args = [cnf_ptr, BitVec.ofNat 64 nvDimacsBytes.length,
            prf_ptr, BitVec.ofNat 64 nvLratRejectBytes.length,
            work_ptr, 512#64] ∧
    cnf_ptr.toNat + nvDimacsBytes.length < 2 ^ 64 ∧
    prf_ptr.toNat + nvLratRejectBytes.length < 2 ^ 64 ∧
    work_ptr.toNat + 512 < 2 ^ 64 ∧
    ((Eq (nvDimacsBytes.At cnf_ptr) ⋆ Eq (nvLratRejectBytes.At prf_ptr) ⋆ region work_ptr 512) ⋆
      R_mem) m ∧
    ∀ (m' : Mem 64),
      ((Eq (nvDimacsBytes.At cnf_ptr) ⋆ Eq (nvLratRejectBytes.At prf_ptr) ⋆ region work_ptr 512) ⋆
        R_mem) m' →
      Q [0] m'

theorem lratCheckBytesExactSpec_of_reject {args : List Val} {m : Mem 64} {Q : Post} {X : XPost}
    (h : lratCheckBytesRejectSpec args m Q X) :
    lratCheckBytesExactSpec args m Q X := by
  obtain ⟨cnf_ptr, prf_ptr, work_ptr, R_mem, hargs, hcnf, hprf, hwork, hm, hQ⟩ := h
  refine ⟨cnf_ptr, prf_ptr, work_ptr, nvDimacsBytes, nvLratRejectBytes, 512, R_mem,
    hargs, hcnf, hprf, hwork, hm, fun r m' hr hm' => ?_⟩
  rw [nvReject_run] at hr
  grind

/-- Function environment exposing `lratCheckBytesRejectSpec` at `"lrat_check_bytes"`. -/
def lratBytesRejectEnv : Env := mkLratBytesEnv lratCheckBytesRejectSpec

@[simp] theorem lratBytesRejectEnv_entry :
    lratBytesRejectEnv "lrat_check_bytes" = lratCheckBytesRejectSpec := rfl

theorem lratBytesRejectEnv_sound :
    ∀ f ∈ lratBytesFns, ∀ args m Q X,
      lratBytesRejectEnv f.name args m Q X → Func.spec lratBytesRejectEnv f.body args m Q X :=
  mkLratBytesEnv_sound lratCheckBytesRejectSpec (fun _ _ _ _ => lratCheckBytesExactSpec_of_reject)

/-! ## 6. Concrete-memory source-level non-vacuity (`accepts` and `rejects`) -/

abbrev nvCnfPtr : BitVec 64 := 0x1000#64
abbrev nvPrfPtr (cnfBytes : List UInt8) : BitVec 64 :=
  nvCnfPtr + BitVec.ofNat 64 cnfBytes.length
abbrev nvWorkPtr (cnfBytes prfBytes : List UInt8) : BitVec 64 :=
  nvPrfPtr cnfBytes + BitVec.ofNat 64 prfBytes.length

def lratBytesPayload (cnfBytes prfBytes : List UInt8) : List UInt8 :=
  (cnfBytes ++ prfBytes) ++ stackZeros 512

theorem lratBytesPayload_length (cnfBytes prfBytes : List UInt8) :
    (lratBytesPayload cnfBytes prfBytes).length = cnfBytes.length + prfBytes.length + 512 := by
  simp [lratBytesPayload, stackZeros_length, Nat.add_assoc]

theorem lratBytesPayload_sep (cnfBytes prfBytes : List UInt8)
    (hcb : cnfBytes.length ≤ 4096) (hpb : prfBytes.length ≤ 4096) :
    (Eq (cnfBytes.At nvCnfPtr) ⋆
      Eq (prfBytes.At (nvPrfPtr cnfBytes)) ⋆
      region (nvWorkPtr cnfBytes prfBytes) 512)
      ((lratBytesPayload cnfBytes prfBytes).At nvCnfPtr) := by
  have hptr : nvCnfPtr.toNat = 4096 := rfl
  have h512 : (stackZeros 512).length = 512 := stackZeros_length 512
  have h1 := Mem.At_append_sep (cnfBytes ++ prfBytes) (stackZeros 512) nvCnfPtr
    (by simp only [List.length_append, h512]; omega)
  have e1 : nvCnfPtr + BitVec.ofNat 64 (cnfBytes ++ prfBytes).length =
      nvWorkPtr cnfBytes prfBytes := by
    grind
  rw [e1] at h1
  have h2 := Mem.At_append_sep cnfBytes prfBytes nvCnfPtr (by omega)
  have h0 : (Eq (((cnfBytes ++ prfBytes) ++ stackZeros 512).At nvCnfPtr))
      ((lratBytesPayload cnfBytes prfBytes).At nvCnfPtr) := rfl
  rw [h1] at h0
  exact sep_mono (fun fL hfL => by rwa [h2] at hfL)
    (sep_mono_r (fun fW hfW => ⟨stackZeros 512, h512, hfW.symm⟩) h0)

private theorem concreteMem_sep (cnfBytes prfBytes : List UInt8)
    (hcb : cnfBytes.length ≤ 4096) (hpb : prfBytes.length ≤ 4096) :
    let cnf_ptr : Val := 0x1000#64
    let prf_ptr : Val := cnf_ptr + BitVec.ofNat 64 cnfBytes.length
    let work_ptr : Val := prf_ptr + BitVec.ofNat 64 prfBytes.length
    let m0 : Mem 64 := ((cnfBytes ++ prfBytes) ++ List.replicate 512 0).At cnf_ptr
    ((Eq (cnfBytes.At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆ region work_ptr 512) ⋆ emp) m0 := by
  intro cnf_ptr prf_ptr work_ptr m0
  rw [Std.ExtHashMap.sep_emp]
  have hptr : cnf_ptr.toNat = 4096 := rfl
  have h512 : (List.replicate 512 (0 : UInt8)).length = 512 := List.length_replicate
  have h1 := Mem.At_append_sep (cnfBytes ++ prfBytes) (List.replicate 512 0) cnf_ptr
    (by simp only [List.length_append, h512]; omega)
  have e1 : cnf_ptr + BitVec.ofNat 64 (cnfBytes ++ prfBytes).length = work_ptr := by
    grind
  rw [e1] at h1
  have h2 := Mem.At_append_sep cnfBytes prfBytes cnf_ptr
    (by omega)
  have h0 : (Eq (((cnfBytes ++ prfBytes) ++ List.replicate 512 0).At cnf_ptr)) m0 := rfl
  rw [h1] at h0
  exact sep_mono (fun fL hfL => by rwa [h2] at hfL)
    (sep_mono_r (fun fW hfW => ⟨List.replicate 512 0, h512, hfW.symm⟩) h0)

/-- Source-level concrete accepting non-vacuity: on concrete memory containing
`nvDimacsBytes ++ nvLratAcceptBytes ++ replicate 512 0` at `0x1000`, `lratCheckBytes` terminates
without exits (`X = False`), returning `[1]` and proving `nvBytesCnf.Unsat`. -/
theorem lratCheckBytes_accepts_nonvacuous :
    let cnf_ptr : Val := 0x1000#64
    let prf_ptr : Val := cnf_ptr + BitVec.ofNat 64 nvDimacsBytes.length
    let work_ptr : Val := prf_ptr + BitVec.ofNat 64 nvLratAcceptBytes.length
    let m0 : Mem 64 := ((nvDimacsBytes ++ nvLratAcceptBytes) ++ List.replicate 512 0).At cnf_ptr
    Func.spec lratBytesAcceptEnv lratCheckBytes
      [cnf_ptr, BitVec.ofNat 64 nvDimacsBytes.length,
       prf_ptr, BitVec.ofNat 64 nvLratAcceptBytes.length,
       work_ptr, 512#64]
      m0
      (fun rs m' => rs = [1] ∧ nvBytesCnf.Unsat ∧
        ((Eq (nvDimacsBytes.At cnf_ptr) ⋆ Eq (nvLratAcceptBytes.At prf_ptr) ⋆
          region work_ptr 512) ⋆ emp) m')
      (fun _ _ _ => False) := by
  intro cnf_ptr prf_ptr work_ptr m0
  have hcb : nvDimacsBytes.length = 19 := nvDimacsBytes_length
  have hpb : nvLratAcceptBytes.length = 15 := rfl
  refine lratBytesAcceptEnv_sound ⟨"lrat_check_bytes", lratCheckBytes⟩ (by simp [lratBytesFns])
    _ m0 _ _ ⟨cnf_ptr, prf_ptr, work_ptr, emp, rfl, ?_, ?_, ?_,
      concreteMem_sep nvDimacsBytes nvLratAcceptBytes (by omega) (by omega),
      fun m' hunsat hm' => ⟨rfl, hunsat, hm'⟩⟩
  · simp [cnf_ptr, hcb]
  · simp [prf_ptr, cnf_ptr, hcb, hpb]
  · simp [work_ptr, prf_ptr, cnf_ptr, hcb, hpb]

/-- Source-level concrete rejecting non-vacuity: on concrete memory containing
`nvDimacsBytes ++ nvLratRejectBytes ++ replicate 512 0` at `0x1000`, `lratCheckBytes` terminates
without exits (`X = False`), returning `[0]`. -/
theorem lratCheckBytes_rejects_nonvacuous :
    let cnf_ptr : Val := 0x1000#64
    let prf_ptr : Val := cnf_ptr + BitVec.ofNat 64 nvDimacsBytes.length
    let work_ptr : Val := prf_ptr + BitVec.ofNat 64 nvLratRejectBytes.length
    let m0 : Mem 64 := ((nvDimacsBytes ++ nvLratRejectBytes) ++ List.replicate 512 0).At cnf_ptr
    Func.spec lratBytesRejectEnv lratCheckBytes
      [cnf_ptr, BitVec.ofNat 64 nvDimacsBytes.length,
       prf_ptr, BitVec.ofNat 64 nvLratRejectBytes.length,
       work_ptr, 512#64]
      m0
      (fun rs m' => rs = [0] ∧
        ((Eq (nvDimacsBytes.At cnf_ptr) ⋆ Eq (nvLratRejectBytes.At prf_ptr) ⋆
          region work_ptr 512) ⋆ emp) m')
      (fun _ _ _ => False) := by
  intro cnf_ptr prf_ptr work_ptr m0
  have hcb : nvDimacsBytes.length = 19 := nvDimacsBytes_length
  have hpb : nvLratRejectBytes.length = 5 := rfl
  refine lratBytesRejectEnv_sound ⟨"lrat_check_bytes", lratCheckBytes⟩ (by simp [lratBytesFns])
    _ m0 _ _ ⟨cnf_ptr, prf_ptr, work_ptr, emp, rfl, ?_, ?_, ?_,
      concreteMem_sep nvDimacsBytes nvLratRejectBytes (by omega) (by omega),
      fun m' hm' => ⟨rfl, hm'⟩⟩
  · simp [cnf_ptr, hcb]
  · simp [prf_ptr, cnf_ptr, hcb, hpb]
  · simp [work_ptr, prf_ptr, cnf_ptr, hcb, hpb]

/-! ## 7. Target-generic `compile_sound` linking -/

theorem lrat_bytes_fnSpec {T : Target} {maxBound : Nat}
    (M : Compiled T [] [] 0 lratBytesFns maxBound)
    (hh : T.Host) (k₀ : Nat) (hc : M.code.IsInfixAt (T.prog hh) k₀)
    (hu : T.LabelsUnique hh) {nm : String} (hnm : nm ∈ lratBytesFns.map Fn.name) :
    T.Defined hh nm ∧ T.FnSpec hh nm (lratBytesEnv nm) (M.bound nm) 0 :=
  M.fnSpec hh lratBytesEnv k₀ hc hu lratBytesFns_wf lratBytesEnv_sound
    (fun _ h => nomatch h) (fun _ h => nomatch h) hnm

theorem lrat_bytes_accepts_fnSpec {T : Target} {maxBound : Nat}
    (M : Compiled T [] [] 0 lratBytesFns maxBound) :
    T.FnSpec M.host "lrat_check_bytes" lratCheckBytesAcceptSpec (M.bound "lrat_check_bytes") 0 := by
  simpa [lratBytesAcceptEnv_entry] using
    (M.fnSpec_host lratBytesAcceptEnv lratBytesFns_wf lratBytesAcceptEnv_sound
      (nm := "lrat_check_bytes") (by simp [lratBytesFns])).2

theorem lrat_bytes_rejects_fnSpec {T : Target} {maxBound : Nat}
    (M : Compiled T [] [] 0 lratBytesFns maxBound) :
    T.FnSpec M.host "lrat_check_bytes" lratCheckBytesRejectSpec (M.bound "lrat_check_bytes") 0 := by
  simpa [lratBytesRejectEnv_entry] using
    (M.fnSpec_host lratBytesRejectEnv lratBytesFns_wf lratBytesRejectEnv_sound
      (nm := "lrat_check_bytes") (by simp [lratBytesFns])).2

theorem lratCheckBytesAcceptSpec_nv (m : Mem 64)
    (hm : ((Eq (nvDimacsBytes.At nvCnfPtr) ⋆ Eq (nvLratAcceptBytes.At (nvPrfPtr nvDimacsBytes)) ⋆
      region (nvWorkPtr nvDimacsBytes nvLratAcceptBytes) 512) ⋆ Std.ExtHashMap.emp) m) :
    lratCheckBytesAcceptSpec
      [nvCnfPtr, BitVec.ofNat 64 nvDimacsBytes.length,
       nvPrfPtr nvDimacsBytes, BitVec.ofNat 64 nvLratAcceptBytes.length,
       nvWorkPtr nvDimacsBytes nvLratAcceptBytes, 512#64]
      m (fun rs _ => rs = [1] ∧ nvBytesCnf.Unsat) (fun _ _ _ => False) :=
  ⟨nvCnfPtr, nvPrfPtr nvDimacsBytes, nvWorkPtr nvDimacsBytes nvLratAcceptBytes,
    Std.ExtHashMap.emp, rfl,
    by simp only [nvCnfPtr, nvDimacsBytes_length]; decide,
    by simp only [nvPrfPtr, nvCnfPtr, nvDimacsBytes_length, nvLratAcceptBytes_length]; decide,
    by simp only [nvWorkPtr, nvPrfPtr, nvCnfPtr, nvDimacsBytes_length, nvLratAcceptBytes_length]; decide,
    hm, fun _ hu _ => ⟨rfl, hu⟩⟩

theorem lratCheckBytesRejectSpec_nv (m : Mem 64)
    (hm : ((Eq (nvDimacsBytes.At nvCnfPtr) ⋆ Eq (nvLratRejectBytes.At (nvPrfPtr nvDimacsBytes)) ⋆
      region (nvWorkPtr nvDimacsBytes nvLratRejectBytes) 512) ⋆ Std.ExtHashMap.emp) m) :
    lratCheckBytesRejectSpec
      [nvCnfPtr, BitVec.ofNat 64 nvDimacsBytes.length,
       nvPrfPtr nvDimacsBytes, BitVec.ofNat 64 nvLratRejectBytes.length,
       nvWorkPtr nvDimacsBytes nvLratRejectBytes, 512#64]
      m (fun rs _ => rs = [0]) (fun _ _ _ => False) :=
  ⟨nvCnfPtr, nvPrfPtr nvDimacsBytes, nvWorkPtr nvDimacsBytes nvLratRejectBytes,
    Std.ExtHashMap.emp, rfl,
    by simp only [nvCnfPtr, nvDimacsBytes_length]; decide,
    by simp only [nvPrfPtr, nvCnfPtr, nvDimacsBytes_length, nvLratRejectBytes_length]; decide,
    by simp only [nvWorkPtr, nvPrfPtr, nvCnfPtr, nvDimacsBytes_length, nvLratRejectBytes_length]; decide,
    hm, fun _ _ => rfl⟩

end LeanQbe.LratBytes
