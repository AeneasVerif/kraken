module

public import LeanQbe.T.Bootstrap0.Mod0
public import LeanQbe.T.Bootstrap0.Cert
public import LeanQbe.T.Amd64.LcnfC0FullCertX64
public import LeanQbe.T.Amd64.LcnfC0FullCertX64Bounds
public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.MainCertCore
meta import LeanQbe.T.Bootstrap0.Mod0
meta import LeanQbe.T.Bootstrap0.Cert
meta import LeanQbe.T.Amd64.LcnfC0FullCertX64Bounds

/-!
# Bootstrap Stage A (`LeanQbeBootstrap0`) — Certification Scope & TCB Audit

This file is meant to be read by a human auditor. It restates, with full unabbreviated types, the
Stage-A artifacts certified by the Lean 4 kernel for `leanqbe0Mod0` / `leanqbe0Cert` and the closed
`210`-function linked artifact `leanqbe0LinkedMod` / `leanqbe0LinkedCert`, followed by a Trusted
Computing Base (TCB) and Non-Claims Checklist separating what Stage A proves from what Stage B/C
audit separately and what remains unproved.

## What Stage A Proves

1. **`audit_leanqbe0Mod0_wf`** (`leanqbe0Mod0_wf`): every one of the `124` functions in the
   lowered `LeanQbe.T.Module` `leanqbe0Mod0` satisfies parametric PHOAS well-formedness (`Fn.Wf`).
2. **`audit_leanqbe0Mod0_acyclic`** (`leanqbe0Mod0_acyclic`): `leanqbe0Mod0` has a strictly acyclic
   call graph (`Module.checkAcyclic = true`).
3. **`audit_leanqbe0Mod0_legalSig`** (`leanqbe0Mod0_legalSig`): every function signature in
   `leanqbe0Mod0.fns` is fixed by `x64LegalTarget.legalSig`.
4. **`audit_leanqbe0Cert`** (`leanqbe0Cert`): `LeanQbe.T`'s existing compiler compiles all `124`
   functions of `leanqbe0Mod0` into SysV x86-64 directives with stack bounds `≤ 1136 ≤ 2048` B,
   checked by the Lean 4 kernel (`LinkedCert`) against `x64Target` / `x64Layout` /
   `x64LegalTarget` / `x64LabelClean`, parameterized by verified `rtC0CoreAllExt` stack bounds
   (`≤ 272` B across the `86` pure-C0 runtime functions) and `rtExitSyms = ["lcnf_panic"]`
   (`nX = 64`).
5. **`audit_leanqbe0LinkedCert`** (`leanqbe0LinkedCert`): appending `leanqbe0Cert` onto
   `rtC0CoreCert` via `rtC0CoreCert.append` produces a closed `210`-function (`86` pure-C0 runtime
   + `124` `leanqbe0` compiler fns), `0`-extern (`externs := []`) SysV x86-64 `LinkedCert` over
   the well-formed, strictly acyclic, `x64LegalTarget`-legal module `leanqbe0LinkedMod` with stack
   bounds `≤ 1136 ≤ 2048` B.

## TCB & Non-Claims Checklist (What Stage A Does NOT Prove)

Do **not** interpret Stage A (`leanqbe0Cert` / `leanqbe0LinkedCert`) as a "self-certified compiler"
claim. The following remain outside Stage A or in the TCB:

1. **No `ModuleOk` / `FnSpec` / `Eventually` for `leanqbe0Mod0`:** while linking with `rtC0CoreCert`
   provides a closed `0`-extern `210`-function certificate using verified runtime stack bounds (and
   `rtC0CoreCert` independently carries machine-level `FnSpec`s for the `86` `rtC0CoreMod` runtime
   functions), `B0-Link` (`leanqbe0Cert` / `leanqbe0LinkedCert`) provides syntactic IR-to-x64
   compilation certification only for the `124` `leanqbe0Mod0` functions. It does **not** prove
   `ModuleOk`, `x64Target.FnSpec`, or `Eventually (step1 Host.exe)` for the compiled `leanqbe0`
   functions themselves, and `lcnf_panic` remains an unmodeled exit symbol (`nX = 64`).
2. **Untrusted `LeanLCNF` meta extraction (`lcnf_of_lean!` / `splice_lcnf_tflat!`):** extracting
   `leanqbe0LcMod` from Lean's compiler IR and lowering it to `leanqbe0Mod0` proves `Fn.Wf` and
   `checkAcyclic = true`, **not** semantic equivalence to Lean's `leanqbe0Compile` evaluation.
3. **Separate Stage-B / Stage-C scope (`Sound0`, `Codec0`, `PrintDir0`, `PrintAsm0`, `StageC`):**
   semantic soundness for `leanqbe0Compile` on guarded scalar programs (with bounded `0x7fffffff`
   worklist fuel in `preWorkLoop0` / `regaWorkLoop0`), binary codec round-trips (`Codec0`), and
   AT&T printer parity (`PrintAsm0`, `PrintDir0`) are proved and audited separately in
   `Sound0Test.lean`, `Codec0Test.lean`, `PrintDir0Test.lean`, `PrintAsm0Test.lean`, and
   `StageCTest.lean`, rather than discharged through `leanqbe0Cert` itself.
4. **No native binary self-compilation fixpoint:** a native `leanqbe0` binary compiling itself to a
   verified fixpoint has not yet been executed or proved.
-/

set_option autoImplicit false

public section

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
compiles to SysV x86-64 directives with stack frame bounds `≤ 1136 ≤ 2048` B against verified
`rtC0CoreAllExt` runtime stack bounds (`86` pure-C0 fns) and `rtExitSyms = ["lcnf_panic"]`
(`nX = 64`). -/
@[expose] noncomputable def audit_leanqbe0Cert :
    LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean
      leanqbe0Mod0 rtC0CoreAllExt ["lcnf_panic"] 64 2048 :=
  leanqbe0Cert

/-- All `124` lowered functions have a recorded stack bound in `leanqbe0Cert`. -/
theorem audit_leanqbe0Cert_bounds_len :
    audit_leanqbe0Cert.bounds.length = 124 :=
  leanqbe0Cert_bounds_len

/-- Every stack bound recorded in `leanqbe0Cert` is at most `2048` bytes. -/
theorem audit_leanqbe0Cert_bounds_le :
    audit_leanqbe0Cert.bounds.all (fun p => Nat.ble p.2 2048) = true :=
  leanqbe0Cert_bounds_le

/-- Every stack bound recorded in `leanqbe0Cert` is at most `1136` bytes. -/
theorem audit_leanqbe0Cert_bounds_le_max :
    audit_leanqbe0Cert.bounds.all (fun p => Nat.ble p.2 1136) = true :=
  leanqbe0Cert_bounds_le_max

/-- `leanqbe0Cert` emits a non-empty x86-64 directive stream. -/
theorem audit_leanqbe0Cert_code_nonempty :
    (!audit_leanqbe0Cert.code.isEmpty) = true :=
  leanqbe0Cert_code_nonempty

/-- **Closed `210`-fn WF** (`Mod0.lean`): every function in `leanqbe0LinkedMod` (`86` runtime +
`124` `leanqbe0`) satisfies `Fn.Wf`. -/
theorem audit_leanqbe0LinkedMod_wf :
    ∀ f ∈ leanqbe0LinkedMod.fns, f.Wf :=
  leanqbe0LinkedMod_wf

/-- **Closed `210`-fn acyclicity** (`Mod0.lean`): `leanqbe0LinkedMod` is strictly acyclic. -/
theorem audit_leanqbe0LinkedMod_acyclic :
    leanqbe0LinkedMod.checkAcyclic = true :=
  leanqbe0LinkedMod_acyclic

/-- **Closed `210`-fn signature legality** (`Cert.lean`): every function in `leanqbe0LinkedMod.fns`
has identity `x64LegalTarget.legalSig`. -/
theorem audit_leanqbe0LinkedMod_legalSig :
    ∀ f ∈ leanqbe0LinkedMod.fns,
      x64LegalTarget.legalSig f.as = f.as ∧ x64LegalTarget.legalSig f.rs = f.rs :=
  leanqbe0LinkedMod_legalSig

/-- **Closed `210`-fn kernel compilation certificate** (`Cert.lean`): appends `leanqbe0Cert` onto
`rtC0CoreCert` over `leanqbe0LinkedMod` with `0` externs (`[]`), `["lcnf_panic"]`, and `nX = 64`.
-/
@[expose] noncomputable def audit_leanqbe0LinkedCert :
    LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean
      leanqbe0LinkedMod [] ["lcnf_panic"] 64 2048 :=
  leanqbe0LinkedCert

/-- All `210` linked functions have a recorded stack bound in `leanqbe0LinkedCert`. -/
theorem audit_leanqbe0LinkedCert_bounds_len :
    audit_leanqbe0LinkedCert.bounds.length = 210 :=
  leanqbe0LinkedCert_bounds_len

/-- Every stack bound recorded in `leanqbe0LinkedCert` is at most `2048` bytes. -/
theorem audit_leanqbe0LinkedCert_bounds_le :
    audit_leanqbe0LinkedCert.bounds.all (fun p => Nat.ble p.2 2048) = true :=
  leanqbe0LinkedCert_bounds_le

/-- Every stack bound recorded in `leanqbe0LinkedCert` is at most `1136` bytes. -/
theorem audit_leanqbe0LinkedCert_bounds_le_max :
    audit_leanqbe0LinkedCert.bounds.all (fun p => Nat.ble p.2 1136) = true :=
  leanqbe0LinkedCert_bounds_le_max

/-- `leanqbe0LinkedCert` emits a non-empty x86-64 directive stream. -/
theorem audit_leanqbe0LinkedCert_code_nonempty :
    (!audit_leanqbe0LinkedCert.code.isEmpty) = true :=
  leanqbe0LinkedCert_code_nonempty

#guard leanqbe0Mod0.fns.length == 124
#guard leanqbe0Mod0.exits == ["lcnf_panic"]
#guard leanqbe0LinkedMod.fns.length == 210 && leanqbe0LinkedMod.externs.isEmpty &&
  leanqbe0LinkedMod.exits == ["lcnf_panic"]
#guard rtC0CoreAllExt.all (fun p => p.2 <= 272)

#print axioms audit_leanqbe0Mod0_wf
#print axioms audit_leanqbe0Mod0_acyclic
#print axioms audit_leanqbe0Mod0_legalSig
#print axioms audit_leanqbe0Cert
#print axioms audit_leanqbe0Cert_bounds_len
#print axioms audit_leanqbe0Cert_bounds_le
#print axioms audit_leanqbe0Cert_bounds_le_max
#print axioms audit_leanqbe0Cert_code_nonempty
#print axioms audit_leanqbe0LinkedMod_wf
#print axioms audit_leanqbe0LinkedMod_acyclic
#print axioms audit_leanqbe0LinkedMod_legalSig
#print axioms audit_leanqbe0LinkedCert
#print axioms audit_leanqbe0LinkedCert_bounds_len
#print axioms audit_leanqbe0LinkedCert_bounds_le
#print axioms audit_leanqbe0LinkedCert_bounds_le_max
#print axioms audit_leanqbe0LinkedCert_code_nonempty

end Bootstrap0Audit
