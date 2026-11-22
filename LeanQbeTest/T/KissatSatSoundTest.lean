/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM5SatNv
meta import LeanQbe.T.Examples.Kissat.FullM4
meta import LeanQbe.T.Examples.Kissat.FullM5

/-!
# Kissat End-to-End Source-Level UNSAT+SAT Soundness & Concrete SAT Non-Vacuity Audit

Standalone `-DwarningAsError=true` audit restating the headline source-level UNSAT+SAT soundness
theorems (`m4SoundEnv`, `m5SoundEnv`), generic acyclic/disjunctive `ModuleOk` transports
(`ModuleOk.respec_tail`, `moduleOk_or_env`), constructive `readModelFromWork` transparency and
framing, and Tier-3b concrete `Mem 64` SAT non-vacuity (`m5_sat_nonvacuous`, `XPost := False`) on
`"p cnf 1 1\n1 0\n"`.
-/

set_option autoImplicit false

public section

open Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full (fullAlignPad fullNvCnfPtr fullNvWorkPtr fullPayload)
open Kraken.Bedrock2.Test

/-- Generic acyclic tail-respec transport audit. -/
theorem audit_respec_tail {Γ₀ Γ₁ : Env} {M : Module} {pfx tail : List Fn}
    (hM₀ : ModuleOk Γ₀ M) (hsplit : M.fns = pfx ++ tail)
    (hAgree : ∀ f as bs, (f, as, bs) ∈ pfx.map Fn.sig ++ M.externs.map Extern.sig →
      ∀ xs m Q X, Γ₀ f as bs xs m Q X ↔ Γ₁ f as bs xs m Q X)
    (hTail : ∀ fn ∈ tail, ∀ xs m Q X,
      Γ₁ fn.name fn.as fn.rs xs m Q X → Func.wp Γ₁ fn.body xs m Q X) :
    ModuleOk Γ₁ M :=
  hM₀.respec_tail hsplit hAgree hTail

/-- Constructive `readModelFromWork` transparency audit (indirection via `h->values` at `+64`). -/
theorem audit_read_model_eq (m' : Mem 64) (work_ptr : BitVec 64) (v : Nat) :
    readModelFromWork m' work_ptr v =
      if v == 0 then false
      else
        match loadVal m' i64 (work_ptr + BitVec.ofNat 64 (fullAlignPad work_ptr) + 64#64) with
        | none => false
        | some vals_ptr =>
          match loadVal m' i8 (vals_ptr + BitVec.ofNat 64 (2 * (v - 1))) with
          | none => false
          | some b => i8BytePos (UInt8.ofBitVec b) :=
  readModelFromWork_eq m' work_ptr v

/-- Constructive `readModelFromWork` framing audit. -/
theorem audit_read_model_frame {m' M : Mem 64} {F : Mem 64 → Prop}
    {work_ptr vals_ptr : BitVec 64} {v : Nat} {b : BitVec 8} (hM : (Eq m' ⋆ F) M)
    (hptr : loadVal m' i64 (work_ptr + BitVec.ofNat 64 (fullAlignPad work_ptr) + 64#64) =
      some vals_ptr)
    (hb : loadVal m' i8 (vals_ptr + BitVec.ofNat 64 (2 * (v - 1))) = some b) :
    readModelFromWork M work_ptr v = if v == 0 then false else i8BytePos (UInt8.ofBitVec b) :=
  readModelFromWork_frame hM hptr hb

/-- Closed `231`-function M4 UNSAT + SAT `ModuleOk` audit. -/
theorem audit_m4_sound_modok : ModuleOk m4SoundEnv FullM4.m4Module :=
  m4SoundEnv_moduleOk

/-- Source-level M4 UNSAT + constructive SAT model soundness audit. -/
theorem audit_m4_model_src
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8} {wlen : Nat}
    {R : Mem 64 → Prop} {m : Mem 64} {X : XPost}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp m4SoundEnv FullM4.kissat_solve_bytes_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun (r, ()) m' =>
        (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
        (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (r = 10#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧
          cnf.Sat (readModelFromWork m' work_ptr)) ∧
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m') X :=
  m4_solve_bytes_model_correct hcfit hwfit hm

/-- Source-level M4 UNSAT + existential SAT soundness audit. -/
theorem audit_m4_sound_src
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8} {wlen : Nat}
    {R : Mem 64 → Prop} {m : Mem 64} {X : XPost}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp m4SoundEnv FullM4.kissat_solve_bytes_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun (r, ()) m' =>
        (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
        (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (r = 10#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ ¬ cnf.Unsat ∧ ∃ α, cnf.Sat α) ∧
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m') X :=
  m4_solve_bytes_sound_correct hcfit hwfit hm

/-- Closed `270`-function M5 UNSAT + SAT `ModuleOk` audit. -/
theorem audit_m5_sound_modok : ModuleOk m5SoundEnv FullM5.m5Module :=
  m5SoundEnv_moduleOk

/-- Source-level M5 UNSAT + constructive SAT model soundness audit. -/
theorem audit_m5_model_src
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8} {wlen : Nat}
    {R : Mem 64 → Prop} {m : Mem 64} {X : XPost}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp m5SoundEnv FullM5.kissat_solve_bytes_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun (r, ()) m' =>
        (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
        (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (r = 10#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧
          cnf.Sat (readModelFromWork m' work_ptr)) ∧
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m') X :=
  m5_solve_bytes_model_correct hcfit hwfit hm

/-- Source-level M5 UNSAT + existential SAT soundness audit. -/
theorem audit_m5_sound_src
    {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8} {wlen : Nat}
    {R : Mem 64 → Prop} {m : Mem 64} {X : XPost}
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m) :
    Func.wp m5SoundEnv FullM5.kissat_solve_bytes_body
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun (r, ()) m' =>
        (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
        (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (r = 10#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ ¬ cnf.Unsat ∧ ∃ α, cnf.Sat α) ∧
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m') X :=
  m5_solve_bytes_sound_correct hcfit hwfit hm

/-- Generic disjunctive-environment `ModuleOk` transport audit. -/
theorem audit_or_env {Γ₀ Γ_extra : Env} {M : Module}
    (hM₀ : ModuleOk Γ₀ M)
    (hExtra : ∀ fn ∈ M.fns, ∀ xs m Q X,
      Γ_extra fn.name fn.as fn.rs xs m Q X →
      Func.wp (fun f as bs ys m' P E => Γ₀ f as bs ys m' P E ∨ Γ_extra f as bs ys m' P E)
        fn.body xs m Q X) :
    ModuleOk (fun f as bs ys m' P E => Γ₀ f as bs ys m' P E ∨ Γ_extra f as bs ys m' P E) M :=
  moduleOk_or_env hM₀ hExtra

/-- Closed `270`-function concrete SAT non-vacuity `ModuleOk` audit. -/
theorem audit_m5_sat_nv_modok : ModuleOk m5SatNvEnv FullM5.m5Module :=
  m5SatNvEnv_moduleOk

/-- Concrete `Mem 64` SAT non-vacuity (`r = 10#64`, `XPost := False`) on `"p cnf 1 1\n1 0\n"`. -/
theorem audit_m5_sat_nv :
    let m0 : Mem 64 := (fullPayload fullNvSatBytes).At fullNvCnfPtr
    Func.wp m5SatNvEnv FullM5.kissat_solve_bytes_body
      (fullNvCnfPtr, BitVec.ofNat 64 fullNvSatBytes.length,
        fullNvWorkPtr fullNvSatBytes, 4096#64, 16#64, ()) m0
      (fun (r, ()) m' =>
        r = 10#64 ∧
        fullNvSatCnf.Sat (readModelFromWork m' (fullNvWorkPtr fullNvSatBytes)) ∧
        (bytes fullNvCnfPtr fullNvSatBytes ⋆
          region (fullNvWorkPtr fullNvSatBytes) 4096 ⋆ emp) m')
      (fun _ _ _ _ => False) :=
  m5_sat_nonvacuous

/-- Concrete `Mem 64` SAT non-vacuity (`kissat_solve_bytes_m5`, `r = 10#64`, `XPost := False`). -/
theorem audit_m5_sat_nv_m5 :
    let m0 : Mem 64 := (fullPayload fullNvSatBytes).At fullNvCnfPtr
    Func.wp m5SatNvEnv FullM5Orch.kissat_solve_bytes_m5_body
      (fullNvCnfPtr, BitVec.ofNat 64 fullNvSatBytes.length,
        fullNvWorkPtr fullNvSatBytes, 4096#64, 16#64, ()) m0
      (fun (r, ()) m' =>
        r = 10#64 ∧
        fullNvSatCnf.Sat (readModelFromWork m' (fullNvWorkPtr fullNvSatBytes)) ∧
        (bytes fullNvCnfPtr fullNvSatBytes ⋆
          region (fullNvWorkPtr fullNvSatBytes) 4096 ⋆ emp) m')
      (fun _ _ _ _ => False) :=
  m5_sat_nonvacuous_m5

/-- Concrete non-empty formula parse audit (`"p cnf 1 1\n1 0\n"` -> `[+1]`). -/
theorem audit_parse_sat_nv : parseDimacs fullNvSatBytes = some fullNvSatCnf :=
  parseDimacs_fullNvSatBytes

#guard FullM4.m4Fns.length == 231
#guard FullM5.m5Fns.length == 270

#print axioms audit_respec_tail
#print axioms audit_read_model_eq
#print axioms audit_read_model_frame
#print axioms audit_m4_sound_modok
#print axioms audit_m4_model_src
#print axioms audit_m4_sound_src
#print axioms audit_m5_sound_modok
#print axioms audit_m5_model_src
#print axioms audit_m5_sound_src
#print axioms audit_or_env
#print axioms audit_m5_sat_nv_modok
#print axioms audit_m5_sat_nv
#print axioms audit_m5_sat_nv_m5
#print axioms audit_parse_sat_nv
