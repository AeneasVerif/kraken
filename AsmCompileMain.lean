/-
AsmCompileMain - CLI for Assembly to Lean Compiler

Usage: asmcompile <input.S> <output.lean> [--def-name NAME]

Arguments:
- input.S: Assembly source file (AT&T syntax)
- output.lean: Output Lean file path
- --def-name: Name for the program definition (default: "program")

Example:
  asmcompile test.S Test.lean --def-name testProgram
-/

import Kraken.AsmCompiler

open Kraken.AsmCompiler

def parseArgs (args : List String) : Option (String × String × String) :=
  match args with
  | [input, output] => some (input, output, "program")
  | [input, output, "--def-name", name] => some (input, output, name)
  | _ => none

def main (args : List String) : IO UInt32 := do
  match parseArgs args with
  | none =>
    IO.eprintln "Usage: asmcompile <input.S> <output.lean> [--def-name NAME]"
    IO.eprintln ""
    IO.eprintln "Arguments:"
    IO.eprintln "  input.S      Assembly source file (AT&T syntax)"
    IO.eprintln "  output.lean  Output Lean file path"
    IO.eprintln "  --def-name   Name for the program definition (default: program)"
    return 1
  | some (inputFile, outputFile, defName) =>
    -- Read input assembly
    let asmCode ← IO.FS.readFile inputFile

    -- Derive module name from output file (just use basename without extension)
    let outputPath := outputFile.splitOn "/" |>.getLast!
    let moduleName := outputPath.splitOn "." |>.head!

    -- Compile to Lean source
    match compileToLean moduleName defName asmCode with
    | .error msg =>
      IO.eprintln s!"Error: {msg}"
      return 1
    | .ok leanSource =>
      -- Write output
      IO.FS.writeFile outputFile leanSource

      IO.println s!"Compiled {inputFile} -> {outputFile}"
      IO.println s!"  Definition: {defName}"
      return 0
