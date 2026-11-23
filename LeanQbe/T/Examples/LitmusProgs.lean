module

public import LeanQbe.T.Notation
public import LeanQbe.T.Module

public import LeanQbe.T.Examples.LitmusProgsProg
/-!
# Typed-IR Generic Scalar Litmus Suite

Typed-IR (`LeanQbe.T`) suite of 12 scalar litmus functions
(ported from the earlier untyped IR),
preserving exact C symbol names, `i64` signatures, low-32-bit `jnz` semantics (`trunc` + `cnew`),
`group`/`loop` control flow, and abnormal `exit "fail"` in `check`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Litmus

open LeanQbe.T
open LeanQbe.T.Notation

/-! ## Module Definitions and Sanity Checks -/

def tracerModule  : Module := ⟨[tracer], [], []⟩
def ifelseModule  : Module := ⟨[ifelse], [], []⟩
def sumtoModule   : Module := ⟨[sumto], [], []⟩
def evenoddModule : Module := ⟨[evenodd], [], []⟩
def nestedModule  : Module := ⟨[nested], [], []⟩
def swapModule    : Module := ⟨[swap], [], []⟩
def spill10Module : Module := ⟨[spill10], [], []⟩
def callincModule : Module := ⟨[inc, callinc], [], []⟩
def twiceModule   : Module := ⟨[check, twice], [], ["fail"]⟩
def sumcallModule : Module := ⟨[inc, sumcall], [], []⟩

/-- All 7 single-function scalar litmus modules. -/
def allSingleModules : List Module :=
  [tracerModule, ifelseModule, sumtoModule, evenoddModule, nestedModule, swapModule, spill10Module]

/-- All 10 litmus modules (single-function and multi-function). -/
def allModules : List Module :=
  allSingleModules ++ [callincModule, twiceModule, sumcallModule]

end LeanQbe.T.Examples.Litmus
