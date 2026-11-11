module

public import LeanQbe.Main
public import LeanQbe.Print
public import LeanQbe.Examples.Programs

/-!
# The command-line driver, generic in the target

`Driver.main tool I printCode` is the whole of an executable that prints the built-in programs
(`LeanQbe.programs`) for the instruction set `I`:

* `<tool> <program>` compiles the program with `compile I` and prints GNU assembler input;
* `<tool> --il <program>` prints its QBE IL text (the input for stock QBE, the same on every
  target);
* `<tool> --list` prints the names of the programs, one per line.

Exit code 0 on success, 1 when printing or compiling fails, 2 for an unknown program or a wrong
command line; every message goes to stderr and names the executable, `tool`.

An executable is one line: it picks `tool`, `I` and `printCode`, the function that prints the
directives of `I` as assembler text. `Main.lean` does so for x64 (`leanqbe`) and `MainArm64.lean`
for AArch64 (`leanqbe-arm64`); they are two executables because no module can import both
`Kraken.X64` and `Kraken.AArch64` (the two declare the same names). This module imports neither.
-/

@[expose] public section

namespace LeanQbe.Driver

/-- GNU assembler input for the compiled functions `fs`: `.text`, a `.globl` per function, then the
code as printed by the target's `printCode` (everything after the `.globl` lines, including an
alignment directive if the target needs one). -/
def emitAsm {I : Isa} (printCode : List I.Directive → String) (fs : List Fn)
    (code : List I.Directive) : String :=
  ".text\n" ++ String.join (fs.map fun f => s!".globl {f.name}\n") ++ printCode code

/-- The command-line interface of `tool`, an executable for the instruction set `I` whose
directives `printCode` prints. -/
def main (tool : String) (I : Isa) (printCode : List I.Directive → String) (args : List String) :
    IO UInt32 := do
  match args with
  | ["--list"] =>
    for (n, _) in programs do IO.println n
    return 0
  | ["--il", name] =>
    match programs.find? (·.1 == name) with
    | none =>
      IO.eprintln s!"{tool}: unknown program {name} (try --list)"
      return 2
    | some (_, fs) =>
      match Print.module fs with
      | .ok t =>
        IO.println t
        return 0
      | .error e =>
        IO.eprintln s!"{tool}: {e}"
        return 1
  | [name] =>
    match programs.find? (·.1 == name) with
    | none =>
      IO.eprintln s!"{tool}: unknown program {name} (try --list)"
      return 2
    | some (_, fs) =>
      match compile I fs with
      | .ok code =>
        IO.print (emitAsm printCode fs code)
        return 0
      | .error e =>
        IO.eprintln s!"{tool}: {e}"
        return 1
  | _ =>
    IO.eprintln s!"usage: {tool} <program> | {tool} --il <program> | {tool} --list"
    return 2

end LeanQbe.Driver
