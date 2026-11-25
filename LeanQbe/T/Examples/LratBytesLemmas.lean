module

public import LeanQbe.T.Examples.LratBytesDimacsLemmas
import LeanQbe.T.Examples.LratBytesRupLemmas
import LeanQbe.T.Examples.LratBytesCheckLemmas

/-!
# Total-Correctness and `ModuleOk` Proofs for `lratBytesModule` in `LeanQbe.T`

Links `LratBytesDimacsLemmas`, `LratBytesRupLemmas`, `LratBytesCheckLemmas` and exports
`runLratCheckBytes_sound`, `lratBytesExactEnv*`, `lratBytesEnv*`,
`lratCheckBytes_encoded_correct`, and concrete accepting/rejecting instances.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.LratBytes

open Std.ExtHashMap Std.Sat LeanQbe.T

/-! ## 1. Pure mirror soundness -/

/-- Pure soundness of `runLratCheckBytes`. -/
theorem runLratCheckBytes_sound {cnfBytes prfBytes : List UInt8} {work_len : Nat}
    (hrun : runLratCheckBytes cnfBytes prfBytes work_len = true) :
    ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat :=
  runLratCheckBytes_sound_of (@parseBodyPure_sound) (@rupCheckPure_sound) hrun

/-! ## 2. Closed per-function correctness and exact module environment -/

theorem lbCheckPrf_correct (Γ : Env)
    (hReadAddLits : ∀ args m Q X,
      lbReadAddLitsSpec args m Q X → Γ "lb_read_add_lits" [i64, i64] [i64] args m Q X)
    (hRupCheck : ∀ args m Q X,
      lbRupCheckSpec args m Q X → Γ "lb_rup_check" [i64, i64, i64, i64] [i64] args m Q X) :
    ∀ args m Q X, lbCheckPrfSpec args m Q X → Func.spec Γ lbCheckPrf args m Q X :=
  lbCheckPrf_correct_of Γ hReadAddLits hRupCheck

theorem lratCheckBytes_exact (Γ : Env)
    (hParseHeader : ∀ args m Q X, lbParseDimacsHeaderSpec args m Q X →
      Γ "lb_parse_dimacs_header" [i64, i64, i64] [i64] args m Q X)
    (hParseBody : ∀ args m Q X, lbParseDimacsBodySpec args m Q X →
      Γ "lb_parse_dimacs_body" [i64, i64] [i64] args m Q X)
    (hCheckPrf : ∀ args m Q X, lbCheckPrfSpec args m Q X →
      Γ "lb_check_prf" [i64, i64] [i64] args m Q X) :
    ∀ args m Q X, lratCheckBytesExactSpec args m Q X → Func.spec Γ lratCheckBytes args m Q X :=
  lratCheckBytes_exact_of Γ hParseHeader hParseBody hCheckPrf

theorem lratCheckBytesExactSpec_of_spec {args : Tup Val [i64, i64, i64, i64, i64, i64]}
    {m : Mem 64} {Q : Post [i64]} {X : XPost} (h : lratCheckBytesSpec args m Q X) :
    lratCheckBytesExactSpec args m Q X := by
  obtain ⟨cp, pp, wp, cb, pb, wl, Rm, ha, hc, hp, hw, hm, hQ⟩ := h
  refine ⟨cp, pp, wp, cb, pb, wl, Rm, ha, hc, hp, hw, hm, fun r m' hr hm' => ?_⟩
  cases hrun : runLratCheckBytes cb pb wl <;> rw [hrun] at hr
  · exact hQ r m' (Or.inl (by simpa using hr)) (fun h => by simp [h] at hr) hm'
  · simp only [↓reduceIte] at hr; subst hr
    exact hQ 1 m' (Or.inr rfl) (fun _ => runLratCheckBytes_sound hrun) hm'

theorem lratCheckBytes_correct (Γ : Env)
    (hParseHeader : ∀ args m Q X, lbParseDimacsHeaderSpec args m Q X →
      Γ "lb_parse_dimacs_header" [i64, i64, i64] [i64] args m Q X)
    (hParseBody : ∀ args m Q X, lbParseDimacsBodySpec args m Q X →
      Γ "lb_parse_dimacs_body" [i64, i64] [i64] args m Q X)
    (hCheckPrf : ∀ args m Q X, lbCheckPrfSpec args m Q X →
      Γ "lb_check_prf" [i64, i64] [i64] args m Q X) :
    ∀ args m Q X, lratCheckBytesSpec args m Q X → Func.spec Γ lratCheckBytes args m Q X :=
  fun _ _ _ _ h => lratCheckBytes_exact Γ hParseHeader hParseBody hCheckPrf _ _ _ _
    (lratCheckBytesExactSpec_of_spec h)

@[expose] def mkLratBytesEnv (mainSpec : Spec [i64, i64, i64, i64, i64, i64] [i64]) : Env
  | "lb_parse_dimacs_header", [.bits 64, .bits 64, .bits 64], [.bits 64] => lbParseDimacsHeaderSpec
  | "lb_parse_dimacs_body",   [.bits 64, .bits 64], [.bits 64]           => lbParseDimacsBodySpec
  | "lb_read_add_lits",       [.bits 64, .bits 64], [.bits 64]           => lbReadAddLitsSpec
  | "lb_rup_check",           [.bits 64, .bits 64, .bits 64, .bits 64], [.bits 64] => lbRupCheckSpec
  | "lb_check_prf",           [.bits 64, .bits 64], [.bits 64]           => lbCheckPrfSpec
  | "lrat_check_bytes", [.bits 64, .bits 64, .bits 64, .bits 64, .bits 64, .bits 64],
      [.bits 64] => mainSpec
  | _, _, _ => fun _ _ _ _ => False

private theorem mkLratBytesEnv_sound (mainSpec : Spec [i64, i64, i64, i64, i64, i64] [i64])
    (hweaken : ∀ args m Q X, mainSpec args m Q X → lratCheckBytesExactSpec args m Q X) :
    ∀ f ∈ lratBytesFns, ∀ args m Q X,
      mkLratBytesEnv mainSpec f.name f.as f.rs args m Q X →
      Func.spec (mkLratBytesEnv mainSpec) f.body args m Q X := by
  intro f hf args m Q X hspec
  simp only [lratBytesFns, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lbParseDimacsHeader_correct _ args m Q X hspec
  · exact lbParseDimacsBody_correct _ args m Q X hspec
  · exact lbReadAddLits_correct _ args m Q X hspec
  · exact lbRupCheck_correct _ args m Q X hspec
  · exact lbCheckPrf_correct _ (fun _ _ _ _ h => h) (fun _ _ _ _ h => h) args m Q X hspec
  · exact lratCheckBytes_exact _ (fun _ _ _ _ h => h) (fun _ _ _ _ h => h)
      (fun _ _ _ _ h => h) args m Q X (hweaken args m Q X hspec)

theorem lratBytesModule_checkAcyclic : lratBytesModule.checkAcyclic = true := by rfl

private theorem mkLratBytesEnv_moduleOk (mainSpec : Spec [i64, i64, i64, i64, i64, i64] [i64])
    (hweaken : ∀ args m Q X, mainSpec args m Q X → lratCheckBytesExactSpec args m Q X) :
    ModuleOk (mkLratBytesEnv mainSpec) lratBytesModule :=
  Module.moduleOk_of_checkAcyclic lratBytesModule_checkAcyclic
    lratBytesFns_wf (mkLratBytesEnv_sound mainSpec hweaken)

@[expose] def lratBytesExactEnv : Env := mkLratBytesEnv lratCheckBytesExactSpec

@[simp] theorem lratBytesExactEnv_entry :
    lratBytesExactEnv "lrat_check_bytes" [i64, i64, i64, i64, i64, i64] [i64] =
      lratCheckBytesExactSpec := rfl

theorem lratBytesExactEnv_sound : ∀ f ∈ lratBytesFns, ∀ args m Q X,
    lratBytesExactEnv f.name f.as f.rs args m Q X → Func.spec lratBytesExactEnv f.body args m Q X :=
  mkLratBytesEnv_sound lratCheckBytesExactSpec (fun _ _ _ _ h => h)

theorem lratBytesExactEnv_moduleOk : ModuleOk lratBytesExactEnv lratBytesModule :=
  mkLratBytesEnv_moduleOk lratCheckBytesExactSpec (fun _ _ _ _ h => h)

/-! ## 3. Top-level soundness environment (`lratBytesEnv`, `lratBytesEnv_moduleOk`) -/

@[expose] def lratBytesEnv : Env := mkLratBytesEnv lratCheckBytesSpec

@[simp] theorem lratBytesEnv_entry :
    lratBytesEnv "lrat_check_bytes" [i64, i64, i64, i64, i64, i64] [i64] =
      lratCheckBytesSpec := rfl

theorem lratBytesEnv_sound : ∀ f ∈ lratBytesFns, ∀ args m Q X,
    lratBytesEnv f.name f.as f.rs args m Q X → Func.spec lratBytesEnv f.body args m Q X :=
  mkLratBytesEnv_sound lratCheckBytesSpec (fun _ _ _ _ => lratCheckBytesExactSpec_of_spec)

theorem lratBytesEnv_moduleOk : ModuleOk lratBytesEnv lratBytesModule :=
  mkLratBytesEnv_moduleOk lratCheckBytesSpec (fun _ _ _ _ => lratCheckBytesExactSpec_of_spec)

theorem lratBytesEnv_ofModule_ok :
    ModuleOk (Env.ofModule lratBytesModule lratBytesEnv) lratBytesModule :=
  lratBytesEnv_moduleOk.ofModule

/-! ## 4. Trivial-postcondition corollary for encoded `CNF Nat` formulas -/

@[expose] def lratCheckBytesEncodedSpec (cnf : CNF Nat) :
    Spec [i64, i64, i64, i64, i64, i64] [i64] :=
  fun args m Q _ =>
    ValidDimacsCnf cnf ∧
    ∃ (cnf_ptr prf_ptr work_ptr : BitVec 64) (prfBytes : List UInt8) (work_len : Nat)
      (R_mem : Mem 64 → Prop),
      args = (cnf_ptr, BitVec.ofNat 64 (encodeDimacs cnf).length,
              prf_ptr, BitVec.ofNat 64 prfBytes.length,
              work_ptr, BitVec.ofNat 64 work_len, ()) ∧
      cnf_ptr.toNat + (encodeDimacs cnf).length < 2 ^ 64 ∧
      prf_ptr.toNat + prfBytes.length < 2 ^ 64 ∧
      work_ptr.toNat + work_len < 2 ^ 64 ∧
      ((Eq ((encodeDimacs cnf).At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆ region work_ptr work_len) ⋆
        R_mem) m ∧
      ∀ (r : BitVec 64) (m' : Mem 64),
        (r = 0 ∨ r = 1) → (r = 1 → cnf.Unsat) →
        ((Eq ((encodeDimacs cnf).At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆
          region work_ptr work_len) ⋆ R_mem) m' →
        Q (r, ()) m'

theorem lratCheckBytesSpec_of_encoded {cnf : CNF Nat}
    {args : Tup Val [i64, i64, i64, i64, i64, i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (h : lratCheckBytesEncodedSpec cnf args m Q X) : lratCheckBytesSpec args m Q X := by
  obtain ⟨hv, cp, pp, wp, pb, wl, Rm, ha, hc, hp, hw, hm, hQ⟩ := h
  refine ⟨cp, pp, wp, encodeDimacs cnf, pb, wl, Rm, ha, hc, hp, hw, hm, fun r m' hr01 hu hm' => ?_⟩
  refine hQ r m' hr01 (fun hr1 => ?_) hm'
  obtain ⟨_, hp', _⟩ := hu hr1; rw [parseDimacs_encodeDimacs hv] at hp'; grind

theorem lratCheckBytes_encoded_correct (cnf : CNF Nat) : ∀ args m Q X,
    lratCheckBytesEncodedSpec cnf args m Q X → Func.spec lratBytesEnv lratCheckBytes args m Q X :=
  fun args m Q X h => lratBytesEnv_sound
    ⟨"lrat_check_bytes", [i64, i64, i64, i64, i64, i64], [i64], lratCheckBytes⟩
    (by simp [lratBytesFns]) args m Q X (lratCheckBytesSpec_of_encoded h)

/-! ## 5. Concrete accepting and rejecting instances -/

theorem nvBytesCnf_valid : ValidDimacsCnf nvBytesCnf := by
  refine ⟨by simp [nvBytesCnf, cnfMaxVar, dimacsBound, CNF.empty, CNF.add],
    by simp [nvBytesCnf, dimacsBound, CNF.empty, CNF.add], fun cl hcl l hl => ?_⟩
  simp [nvBytesCnf, CNF.empty, CNF.add] at hcl
  rcases hcl with rfl | rfl <;> simp at hl <;> subst hl <;> omega

theorem nvDimacsBytes_eq : nvDimacsBytes =
    [112, 32, 99, 110, 102, 32, 49, 32, 50, 10, 49, 32, 48, 10, 45, 49, 32, 48, 10] := by
  simp [nvDimacsBytes, nvBytesCnf, encodeDimacs, cnfMaxVar, encodeDimacsClause,
    encodeDimacsLit, natToBytes, natToBytesAux, CNF.empty, CNF.add]

@[simp] theorem nvDimacsBytes_length : nvDimacsBytes.length = 19 := by rw [nvDimacsBytes_eq]; rfl
@[simp] theorem nvLratAcceptBytes_length : nvLratAcceptBytes.length = 15 := rfl
@[simp] theorem nvLratRejectBytes_length : nvLratRejectBytes.length = 5 := rfl

theorem nvDimacsBytes_parse : parseDimacs nvDimacsBytes = some nvBytesCnf :=
  parseDimacs_encodeDimacs nvBytesCnf_valid

theorem nvAccept_run : runLratCheckBytes nvDimacsBytes nvLratAcceptBytes 512 = true := by
  rw [nvDimacsBytes_eq]; rfl

theorem nvReject_run : runLratCheckBytes nvDimacsBytes nvLratRejectBytes 512 = false := by
  rw [nvDimacsBytes_eq]; rfl

theorem nvBytesCnf_unsat : nvBytesCnf.Unsat := by
  obtain ⟨cnf, hp, hu⟩ := runLratCheckBytes_sound nvAccept_run
  rw [nvDimacsBytes_parse] at hp; grind

@[expose] def lratCheckBytesAcceptSpec :
    Spec [i64, i64, i64, i64, i64, i64] [i64] := fun args m Q _ =>
  ∃ (cnf_ptr prf_ptr work_ptr : BitVec 64) (R_mem : Mem 64 → Prop),
    args = (cnf_ptr, BitVec.ofNat 64 nvDimacsBytes.length,
            prf_ptr, BitVec.ofNat 64 nvLratAcceptBytes.length,
            work_ptr, 512#64, ()) ∧
    cnf_ptr.toNat + nvDimacsBytes.length < 2 ^ 64 ∧
    prf_ptr.toNat + nvLratAcceptBytes.length < 2 ^ 64 ∧
    work_ptr.toNat + 512 < 2 ^ 64 ∧
    ((Eq (nvDimacsBytes.At cnf_ptr) ⋆ Eq (nvLratAcceptBytes.At prf_ptr) ⋆ region work_ptr 512) ⋆
      R_mem) m ∧
    ∀ (m' : Mem 64),
      nvBytesCnf.Unsat →
      ((Eq (nvDimacsBytes.At cnf_ptr) ⋆ Eq (nvLratAcceptBytes.At prf_ptr) ⋆ region work_ptr 512) ⋆
        R_mem) m' →
      Q (1, ()) m'

theorem lratCheckBytesExactSpec_of_accept {args : Tup Val [i64, i64, i64, i64, i64, i64]}
    {m : Mem 64} {Q : Post [i64]} {X : XPost} (h : lratCheckBytesAcceptSpec args m Q X) :
    lratCheckBytesExactSpec args m Q X := by
  obtain ⟨cp, pp, wp, Rm, ha, hc, hp, hw, hm, hQ⟩ := h
  refine ⟨cp, pp, wp, nvDimacsBytes, nvLratAcceptBytes, 512, Rm,
    ha, hc, hp, hw, hm, fun r m' hr hm' => ?_⟩
  rw [nvAccept_run] at hr; simp only [↓reduceIte] at hr; subst hr
  exact hQ m' nvBytesCnf_unsat hm'

@[expose] def lratBytesAcceptEnv : Env := mkLratBytesEnv lratCheckBytesAcceptSpec

@[simp] theorem lratBytesAcceptEnv_entry :
    lratBytesAcceptEnv "lrat_check_bytes" [i64, i64, i64, i64, i64, i64] [i64] =
      lratCheckBytesAcceptSpec := rfl

theorem lratBytesAcceptEnv_sound : ∀ f ∈ lratBytesFns, ∀ args m Q X,
    lratBytesAcceptEnv f.name f.as f.rs args m Q X →
    Func.spec lratBytesAcceptEnv f.body args m Q X :=
  mkLratBytesEnv_sound lratCheckBytesAcceptSpec (fun _ _ _ _ => lratCheckBytesExactSpec_of_accept)

theorem lratBytesAcceptEnv_moduleOk : ModuleOk lratBytesAcceptEnv lratBytesModule :=
  mkLratBytesEnv_moduleOk lratCheckBytesAcceptSpec
    (fun _ _ _ _ => lratCheckBytesExactSpec_of_accept)

@[expose] def lratCheckBytesRejectSpec :
    Spec [i64, i64, i64, i64, i64, i64] [i64] := fun args m Q _ =>
  ∃ (cnf_ptr prf_ptr work_ptr : BitVec 64) (R_mem : Mem 64 → Prop),
    args = (cnf_ptr, BitVec.ofNat 64 nvDimacsBytes.length,
            prf_ptr, BitVec.ofNat 64 nvLratRejectBytes.length,
            work_ptr, 512#64, ()) ∧
    cnf_ptr.toNat + nvDimacsBytes.length < 2 ^ 64 ∧
    prf_ptr.toNat + nvLratRejectBytes.length < 2 ^ 64 ∧
    work_ptr.toNat + 512 < 2 ^ 64 ∧
    ((Eq (nvDimacsBytes.At cnf_ptr) ⋆ Eq (nvLratRejectBytes.At prf_ptr) ⋆ region work_ptr 512) ⋆
      R_mem) m ∧
    ∀ (m' : Mem 64),
      ((Eq (nvDimacsBytes.At cnf_ptr) ⋆ Eq (nvLratRejectBytes.At prf_ptr) ⋆ region work_ptr 512) ⋆
        R_mem) m' →
      Q (0, ()) m'

theorem lratCheckBytesExactSpec_of_reject {args : Tup Val [i64, i64, i64, i64, i64, i64]}
    {m : Mem 64} {Q : Post [i64]} {X : XPost} (h : lratCheckBytesRejectSpec args m Q X) :
    lratCheckBytesExactSpec args m Q X := by
  obtain ⟨cp, pp, wp, Rm, ha, hc, hp, hw, hm, hQ⟩ := h
  refine ⟨cp, pp, wp, nvDimacsBytes, nvLratRejectBytes, 512, Rm,
    ha, hc, hp, hw, hm, fun r m' hr hm' => ?_⟩
  rw [nvReject_run] at hr; grind

@[expose] def lratBytesRejectEnv : Env := mkLratBytesEnv lratCheckBytesRejectSpec

@[simp] theorem lratBytesRejectEnv_entry :
    lratBytesRejectEnv "lrat_check_bytes" [i64, i64, i64, i64, i64, i64] [i64] =
      lratCheckBytesRejectSpec := rfl

theorem lratBytesRejectEnv_sound : ∀ f ∈ lratBytesFns, ∀ args m Q X,
    lratBytesRejectEnv f.name f.as f.rs args m Q X →
    Func.spec lratBytesRejectEnv f.body args m Q X :=
  mkLratBytesEnv_sound lratCheckBytesRejectSpec (fun _ _ _ _ => lratCheckBytesExactSpec_of_reject)

theorem lratBytesRejectEnv_moduleOk : ModuleOk lratBytesRejectEnv lratBytesModule :=
  mkLratBytesEnv_moduleOk lratCheckBytesRejectSpec
    (fun _ _ _ _ => lratCheckBytesExactSpec_of_reject)

/-! ## 6. Concrete-memory source-level non-vacuity (`accepts` and `rejects`) -/

abbrev nvCnfPtr : BitVec 64 := 0x1000#64
abbrev nvPrfPtr (cnfBytes : List UInt8) : BitVec 64 :=
  nvCnfPtr + BitVec.ofNat 64 cnfBytes.length
abbrev nvWorkPtr (cnfBytes prfBytes : List UInt8) : BitVec 64 :=
  nvPrfPtr cnfBytes + BitVec.ofNat 64 prfBytes.length

@[expose] def lratBytesPayload (cnfBytes prfBytes : List UInt8) : List UInt8 :=
  (cnfBytes ++ prfBytes) ++ List.replicate 512 0

theorem lratBytesPayload_length (cnfBytes prfBytes : List UInt8) :
    (lratBytesPayload cnfBytes prfBytes).length = cnfBytes.length + prfBytes.length + 512 := by
  simp only [lratBytesPayload, List.length_append, List.length_replicate]

theorem lratBytesPayload_sep (cnfBytes prfBytes : List UInt8)
    (hcb : cnfBytes.length ≤ 4096) (hpb : prfBytes.length ≤ 4096) :
    (Eq (cnfBytes.At nvCnfPtr) ⋆
      Eq (prfBytes.At (nvPrfPtr cnfBytes)) ⋆
      region (nvWorkPtr cnfBytes prfBytes) 512)
      ((lratBytesPayload cnfBytes prfBytes).At nvCnfPtr) := by
  have hptr : nvCnfPtr.toNat = 4096 := rfl
  have h512 : (List.replicate 512 (0 : UInt8)).length = 512 := List.length_replicate
  have h1 := Mem.At_append_sep (cnfBytes ++ prfBytes) (List.replicate 512 0) nvCnfPtr
    (by simp only [List.length_append, h512]; omega)
  rw [show nvCnfPtr + BitVec.ofNat 64 (cnfBytes ++ prfBytes).length =
      nvWorkPtr cnfBytes prfBytes by grind] at h1
  have h2 := Mem.At_append_sep cnfBytes prfBytes nvCnfPtr (by omega)
  have h0 : (Eq (((cnfBytes ++ prfBytes) ++ List.replicate 512 0).At nvCnfPtr))
      ((lratBytesPayload cnfBytes prfBytes).At nvCnfPtr) := rfl
  rw [h1] at h0
  exact sep_mono (fun fL hfL => by rwa [h2] at hfL)
    (sep_mono_r (fun fW hfW => ⟨List.replicate 512 0, h512, hfW.symm⟩) h0)

private theorem concreteMem_sep (cnfBytes prfBytes : List UInt8)
    (hcb : cnfBytes.length ≤ 4096) (hpb : prfBytes.length ≤ 4096) :
    let cnf_ptr : BitVec 64 := 0x1000#64
    let prf_ptr : BitVec 64 := cnf_ptr + BitVec.ofNat 64 cnfBytes.length
    let work_ptr : BitVec 64 := prf_ptr + BitVec.ofNat 64 prfBytes.length
    let m0 : Mem 64 := ((cnfBytes ++ prfBytes) ++ List.replicate 512 0).At cnf_ptr
    ((Eq (cnfBytes.At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆ region work_ptr 512) ⋆ emp) m0 := by
  intro _ _ _ _
  have h := lratBytesPayload_sep cnfBytes prfBytes hcb hpb
  unfold lratBytesPayload at h; rwa [Std.ExtHashMap.sep_emp]

theorem lratCheckBytes_accepts_nonvacuous :
    let cnf_ptr : BitVec 64 := 0x1000#64
    let prf_ptr : BitVec 64 := cnf_ptr + BitVec.ofNat 64 nvDimacsBytes.length
    let work_ptr : BitVec 64 := prf_ptr + BitVec.ofNat 64 nvLratAcceptBytes.length
    let m0 : Mem 64 := ((nvDimacsBytes ++ nvLratAcceptBytes) ++ List.replicate 512 0).At cnf_ptr
    Func.spec lratBytesAcceptEnv lratCheckBytes
      (cnf_ptr, BitVec.ofNat 64 nvDimacsBytes.length,
       prf_ptr, BitVec.ofNat 64 nvLratAcceptBytes.length,
       work_ptr, 512#64, ())
      m0
      (fun rs m' => rs = (1, ()) ∧ nvBytesCnf.Unsat ∧
        ((Eq (nvDimacsBytes.At cnf_ptr) ⋆ Eq (nvLratAcceptBytes.At prf_ptr) ⋆
          region work_ptr 512) ⋆ emp) m')
      (fun _ _ _ _ => False) := by
  intro cp pp wp m0
  exact lratBytesAcceptEnv_sound
    ⟨"lrat_check_bytes", [i64, i64, i64, i64, i64, i64], [i64], lratCheckBytes⟩
    (by simp [lratBytesFns]) _ m0 _ _
    ⟨cp, pp, wp, emp, rfl, by simp [cp], by simp [pp, cp], by simp [wp, pp, cp],
      concreteMem_sep _ _ (by simp) (by simp), fun m' h hm' => ⟨rfl, h, hm'⟩⟩

theorem lratCheckBytes_rejects_nonvacuous :
    let cnf_ptr : BitVec 64 := 0x1000#64
    let prf_ptr : BitVec 64 := cnf_ptr + BitVec.ofNat 64 nvDimacsBytes.length
    let work_ptr : BitVec 64 := prf_ptr + BitVec.ofNat 64 nvLratRejectBytes.length
    let m0 : Mem 64 := ((nvDimacsBytes ++ nvLratRejectBytes) ++ List.replicate 512 0).At cnf_ptr
    Func.spec lratBytesRejectEnv lratCheckBytes
      (cnf_ptr, BitVec.ofNat 64 nvDimacsBytes.length,
       prf_ptr, BitVec.ofNat 64 nvLratRejectBytes.length,
       work_ptr, 512#64, ())
      m0
      (fun rs m' => rs = (0, ()) ∧
        ((Eq (nvDimacsBytes.At cnf_ptr) ⋆ Eq (nvLratRejectBytes.At prf_ptr) ⋆
          region work_ptr 512) ⋆ emp) m')
      (fun _ _ _ _ => False) := by
  intro cp pp wp m0
  exact lratBytesRejectEnv_sound
    ⟨"lrat_check_bytes", [i64, i64, i64, i64, i64, i64], [i64], lratCheckBytes⟩
    (by simp [lratBytesFns]) _ m0 _ _
    ⟨cp, pp, wp, emp, rfl, by simp [cp], by simp [pp, cp], by simp [wp, pp, cp],
      concreteMem_sep _ _ (by simp) (by simp), fun m' hm' => ⟨rfl, hm'⟩⟩

theorem lratCheckBytes_accepts :
    let cnf_ptr : BitVec 64 := 0x1000#64
    let prf_ptr : BitVec 64 := cnf_ptr + BitVec.ofNat 64 nvDimacsBytes.length
    let work_ptr : BitVec 64 := prf_ptr + BitVec.ofNat 64 nvLratAcceptBytes.length
    let m0 : Mem 64 := ((nvDimacsBytes ++ nvLratAcceptBytes) ++ List.replicate 512 0).At cnf_ptr
    Func.spec lratBytesAcceptEnv lratCheckBytes
      (cnf_ptr, BitVec.ofNat 64 nvDimacsBytes.length,
       prf_ptr, BitVec.ofNat 64 nvLratAcceptBytes.length,
       work_ptr, 512#64, ())
      m0
      (fun rs m' => rs = (1, ()) ∧ nvBytesCnf.Unsat ∧
        ((Eq (nvDimacsBytes.At cnf_ptr) ⋆ Eq (nvLratAcceptBytes.At prf_ptr) ⋆
          region work_ptr 512) ⋆ emp) m')
      (fun _ _ _ _ => False) := lratCheckBytes_accepts_nonvacuous

theorem lratCheckBytes_rejects :
    let cnf_ptr : BitVec 64 := 0x1000#64
    let prf_ptr : BitVec 64 := cnf_ptr + BitVec.ofNat 64 nvDimacsBytes.length
    let work_ptr : BitVec 64 := prf_ptr + BitVec.ofNat 64 nvLratRejectBytes.length
    let m0 : Mem 64 := ((nvDimacsBytes ++ nvLratRejectBytes) ++ List.replicate 512 0).At cnf_ptr
    Func.spec lratBytesRejectEnv lratCheckBytes
      (cnf_ptr, BitVec.ofNat 64 nvDimacsBytes.length,
       prf_ptr, BitVec.ofNat 64 nvLratRejectBytes.length,
       work_ptr, 512#64, ())
      m0
      (fun rs m' => rs = (0, ()) ∧
        ((Eq (nvDimacsBytes.At cnf_ptr) ⋆ Eq (nvLratRejectBytes.At prf_ptr) ⋆
          region work_ptr 512) ⋆ emp) m')
      (fun _ _ _ _ => False) := lratCheckBytes_rejects_nonvacuous

end LeanQbe.T.Examples.LratBytes