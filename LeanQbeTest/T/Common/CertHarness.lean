module

public import LeanQbe.T.MainLemmas
public import LeanQbe.T.MainCertProof
public import LeanQbe.T.Spill

/-!
# Architecture-Generic Certificate & Linker Test Harness (`Common.CertHarness`)

Target-generic helpers for invoking compiler passes, checking link invariants,
and gathering `Spill.hints` across dual-architecture test suites without importing
either `Kraken.X64` or `Kraken.AArch64`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbeTest.T.Common.CertHarness

open LeanQbe.T

/-- Compute hints for a function list under target `T` and legal rules `lt`. -/
@[reducible] def hintsOf (T : Target) (lt : LegalTarget) (fs : List Fn) : List T.toIsa.Hints :=
  fs.map (Fn.computeHints T.toIsa lt)

/-- End-to-end verified compilation check (lowering, labels, stack bounds). -/
@[reducible] def chk (T : Target) (L : TargetLayout T) (lt : LegalTarget) (fs : List Fn)
    (maxBound : Nat := 2048) : Bool :=
  checkCompile T L lt [] [] 0 fs (hintsOf T lt fs) maxBound

/-- Emitted directive list of a module under target `T` (empty on compile error). -/
@[reducible] def codeOf (T : Target) (lt : LegalTarget) (fs : List Fn) :
    List T.toIsa.Directive :=
  extractCode (compileModule T.toIsa lt T.frame.raBytes [] [] 0 fs (hintsOf T lt fs))

/-- Check that all chunks in a LinkedCert satisfy target layout and linker hygiene. -/
@[reducible] def checkLinksOk {T : Target} (L : TargetLayout T) {lt : LegalTarget}
    {C : Rega.LabelClean T.toIsa} {m : Module} {b : Nat}
    (cert : LinkedCert T L lt C m [] [] 0 b) : Bool :=
  checkLinkList L [] cert.chunks

end LeanQbeTest.T.Common.CertHarness
