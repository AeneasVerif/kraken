module

public import LeanQbe.T.Bootstrap0.Mod0
public import LeanQbe.T.Bootstrap0.Cert
public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.MainCertCore
meta import LeanQbe.T.Bootstrap0.Mod0
meta import LeanQbe.T.Bootstrap0.Cert

/-!
# Bootstrap Stage A (`LeanQbeBootstrap0`) — Certification Scope & TCB Audit

This file is meant to be read by a human auditor. It restates, with full unabbreviated types, the
four Stage-A artifacts currently certified by the Lean 4 kernel for `leanqbe0Compile`, followed by
a candid Trusted Computing Base (TCB) and Non-Claims Checklist separating what Stage A proves today
from what Stage B is actively building.

## What Stage A Proves Today

1. **`audit_leanqbe0Mod0_wf`** (`leanqbe0Mod0_wf`): every one of the `124` functions in the
   lowered `LeanQbe.T.Module` `leanqbe0Mod0` satisfies parametric PHOAS well-formedness (`Fn.Wf`).
2. **`audit_leanqbe0Mod0_acyclic`** (`leanqbe0Mod0_acyclic`): `leanqbe0Mod0` has a strictly acyclic
   call graph (`Module.checkAcyclic = true`).
3. **`audit_leanqbe0Mod0_legalSig`** (`leanqbe0Mod0_legalSig`): every function signature in
   `leanqbe0Mod0.fns` is fixed by `x64LegalTarget.legalSig`.
4. **`audit_leanqbe0Cert`** (`leanqbe0Cert`): `LeanQbe.T`'s existing compiler compiles all `124`
   functions of `leanqbe0Mod0` into `17,150` SysV x86-64 directives with stack bounds `≤ 2048` B,
   checked by the Lean 4 kernel (`LinkedCert`) against `x64Target` / `x64Layout` /
   `x64LegalTarget` / `x64LabelClean`, parameterized by assumed `rtExtBounds0` (`64` per extern)
   and `rtExitSyms = ["lcnf_panic"]` (`nX = 64`).

## TCB & Non-Claims Checklist (What Stage A Does NOT Prove)

Do **not** interpret Stage A (`leanqbe0Cert`) as a "self-certified compiler" claim. The following
remain in the TCB or in-flight for Stage B:

1. **No `ModuleOk` / `FnSpec` / `Eventually` for `leanqbe0Mod0`:** `leanqbe0Cert` is a syntactic
   IR-to-x64 compilation certificate only. Because `lcnf_rt.c` externs (`rtCalls` / `rtExterns`)
   and `lcnf_panic` carry no formal behavioral contracts — only assumed `64`-byte stack/exit bounds
   (`rtExtBounds0`, `nX = 64`) — `leanqbe0Cert` does not yet instantiate `x64Target.FnSpec` or
   `Eventually (step1 Host.exe)`.
2. **Untrusted `LeanLCNF` meta extraction (`lcnf_of_lean!` / `splice_lcnf_tflat!`):** extracting
   `leanqbe0LcMod` from Lean's compiler IR and lowering it to `leanqbe0Mod0` proves `Fn.Wf` and
   `checkAcyclic = true`, **not** semantic equivalence to Lean's `leanqbe0Compile` evaluation.
3. **No `Sound0` compiler-correctness proof (`Compiler0.lean`):** `leanqbe0Compile` (including
   `PrePass0`, `Legal0`, `Isel0`, `Rega0`, and `.tailCall`) has zero `Func.wp` or `x64`
   correctness proofs today (and `preWorkLoop0` / `regaWorkLoop0` use bounded `0x7fffffff` fuel).
4. **Unverified `Bridge0` / `Codec0` & unwired `PrintAsm0`:** `Bridge0` (`ofTFlatModule`,
   `toAmd64Program`) and binary/ELF emission (`Codec0`) are unverified; `PrintAsm0Lemmas` proves
   `printModule0 = Driver.emitAsm` on `DirSubset0`, but `PrintAsm0` is not yet wired into
   `leanqbe0`; and a native binary self-compilation fixpoint has not yet been executed or proved.
-/

set_option autoImplicit false

@[expose] public section

namespace Bootstrap0Audit

open LeanQbe.T LeanQbe.T.LeanLCNF LeanQbe.T.Amd64 LeanQbe.T.Bootstrap0

/-- **Stage-A WF** (`Mod0.lean`): every function in `leanqbe0Mod0` satisfies `Fn.Wf`. -/
theorem audit_leanqbe0Mod0_wf :
    ∀ f ∈ leanqbe0Mod0.fns, f.Wf :=
  leanqbe0Mod0_wf

/-- **Stage-A acyclicity** (`Mod0.lean`): `leanqbe0Mod0` has a strictly acyclic call graph. -/
theorem audit_leanqbe0Mod0_acyclic :
    leanqbe0Mod0.checkAcyclic = true :=
  leanqbe0Mod0_acyclic

/-- **Stage-A signature legality** (`Cert.lean`): every function in `leanqbe0Mod0.fns` has
identity `x64LegalTarget.legalSig`. -/
theorem audit_leanqbe0Mod0_legalSig :
    ∀ f ∈ leanqbe0Mod0.fns,
      x64LegalTarget.legalSig f.as = f.as ∧ x64LegalTarget.legalSig f.rs = f.rs :=
  leanqbe0Mod0_legalSig

/-- **Stage-A kernel compilation certificate** (`Cert.lean`): `leanqbe0Mod0` (`124` functions)
compiles to SysV x86-64 directives with stack frame bounds `≤ 2048` B under assumed `rtExtBounds0`
(`64` per `rtExterns` entry) and `rtExitSyms = ["lcnf_panic"]` (`nX = 64`). -/
noncomputable def audit_leanqbe0Cert :
    LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean
      leanqbe0Mod0
      (rtExterns.map fun ex => ((ex.name, ex.as, ex.rs), 64))
      ["lcnf_panic"] 64 2048 :=
  leanqbe0Cert

/-- All `124` lowered functions have a recorded stack bound in `leanqbe0Cert`. -/
theorem audit_leanqbe0Cert_bounds_len :
    audit_leanqbe0Cert.bounds.length = 124 :=
  leanqbe0Cert_bounds_len

/-- Every stack bound recorded in `leanqbe0Cert` is at most `2048` bytes. -/
theorem audit_leanqbe0Cert_bounds_le :
    audit_leanqbe0Cert.bounds.all (fun p => Nat.ble p.2 2048) = true :=
  leanqbe0Cert_bounds_le

/-- `leanqbe0Cert` emits a non-empty x86-64 directive stream. -/
theorem audit_leanqbe0Cert_code_nonempty :
    (!audit_leanqbe0Cert.code.isEmpty) = true :=
  leanqbe0Cert_code_nonempty

#guard leanqbe0Mod0.fns.length == 124
#guard leanqbe0Mod0.exits == ["lcnf_panic"]
#guard rtExtBounds0.all (fun p => p.2 == 64)

#print axioms audit_leanqbe0Mod0_wf
#print axioms audit_leanqbe0Mod0_acyclic
#print axioms audit_leanqbe0Mod0_legalSig
#print axioms audit_leanqbe0Cert
#print axioms audit_leanqbe0Cert_bounds_len
#print axioms audit_leanqbe0Cert_bounds_le
#print axioms audit_leanqbe0Cert_code_nonempty

end Bootstrap0Audit
