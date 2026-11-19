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
      let hints := fs'.map fun f => Spill.hints I (f.mid lt)
      emitAsm printCode fs' <$> compile I lt fs' hints
  | _ => do
    IO.eprintln s!"usage: {tool} <program> | {tool} --il <program> | {tool} --list"
    pure 2

end LeanQbe.T.Driver
