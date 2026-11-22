module

public import LeanQbe.T.Examples.Programs
public import LeanQbe.T.Main
public import LeanQbe.T.PrintQbe
public import LeanQbe.T.Spill

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Driver

/-! # Target-Generic CLI Driver

Target-parameterized entrypoint matching `LeanQbe.Driver` without importing any
architecture backend. Note that SIMD-only programs (such as `chacha20`) cleanly
fail `--il` with exit code `1` because `PrintQbe` only lowers scalar QBE IL.
-/

/-- Emit the `.text` section header, `.globl` declarations for each function,
and target assembly directives. -/
def emitAsm {I : Isa} (printCode : List I.Directive → String)
    (fs : List Fn) (code : List I.Directive) : String :=
  ".text\n" ++ String.join (fs.map fun f => s!".globl {f.name}\n") ++ printCode code

/-- Look up a program by name, run a fallible emitter, and write stdout/stderr
with matching exit codes (`0` on success, `1` on compile/print error, `2` if unknown). -/
def runProgram (tool name : String)
    (emit : List Fn → Except String String) : IO UInt32 :=
  match programs.lookup name with
  | none => do
    IO.eprintln s!"{tool}: unknown program {name} (try --list)"
    pure 2
  | some fs =>
    match emit fs with
    | .ok out => do
      IO.print out
      pure 0
    | .error e => do
      IO.eprintln s!"{tool}: {e}"
      pure 1

/-- Materialize `fn.body` once into a concrete `TFlat` so downstream PHOAS passes,
`Spill.hints`, `Fn.ext`, and `Rega.lowerFn` never re-evaluate nested closures. -/
def matFn (fn : Fn) : Fn :=
  let tf := reifyFunc fn.body
  ⟨fn.name, fn.as, fn.rs, denoteFunc tf⟩

/-- Lower each function through the mid-end (`earlyOpt → legal → lateOpt`) once,
materializing stage boundaries and sharing the result across `Spill.hints`, `Fn.ext`,
and `Rega.lowerFn`. -/
def compileFns (I : Isa) (lt : LegalTarget) :
    List Fn → Except String (List I.Directive)
  | [] => .ok []
  | f :: fs =>
    let ef := matFn f.earlyOpt
    let lf := matFn (ef.legal lt)
    let mf := matFn lf.lateOpt
    let h := Spill.hints I mf
    match Rega.lowerFn I h mf.ext mf, compileFns I lt fs with
    | .ok c, .ok cs => .ok (c ++ cs)
    | .error e, _ => .error s!"{f.name}: {e}"
    | _, .error e => .error e

/-- Run the target-generic CLI: `--list`, `--il <program>`, or `<program>`. -/
def main (tool : String) (I : Isa) (lt : LegalTarget)
    (printCode : List I.Directive → String) (args : List String) : IO UInt32 :=
  match args with
  | ["--list"] => do
    for (n, _) in programs do
      IO.println n
    pure 0
  | ["--il", name] =>
    runProgram tool name fun fs => (· ++ "\n") <$> PrintQbe.fns fs
  | [name] =>
    runProgram tool name fun fs =>
      let fs' := (Module.optInline { fns := fs }).fns
      emitAsm printCode fs' <$> compileFns I lt fs'
  | _ => do
    IO.eprintln s!"usage: {tool} <program> | {tool} --il <program> | {tool} --list"
    pure 2

end LeanQbe.T.Driver
