import LeanQbeArm64
import LeanQbe.Main
import LeanQbe.Print
import LeanQbe.Examples.LitmusProgs

/-!
AArch64 assembly and QBE IL emitter for the litmus and union-find programs (not a module; run with
`lake env lean --run test/arm64/Emit.lean [--il] <name>`). Compiles with `compileFn Arm64.isa` (or
`compile Arm64.isa` for multi-function targets like `unionfind`) and prints with Kraken's AArch64
printer.
-/

open LeanQbe

def suites : List (String × List Fn) :=
  [("tracer", [Litmus.tracer]),
   ("ifelse", [Litmus.ifelse]),
   ("sumto", [Litmus.sumto]),
   ("evenodd", [Litmus.evenodd]),
   ("nested", [Litmus.nested]),
   ("swap", [Litmus.swap]),
   ("unionfind", [Arm64.UnionFind.findFn, Arm64.UnionFind.unionInlineFn])]

def emitAsm (fs : List Fn) (code : List Arm64.isa.Directive) : String :=
  let hdr := ".text\n" ++ String.join (fs.map fun f => s!".globl {f.name}\n") ++ ".p2align 2\n"
  hdr ++ String.intercalate "\n" (code.map Kraken.AArch64.Print.directive) ++ "\n"

def main (args : List String) : IO UInt32 := do
  let (il, name) ← match args with
    | ["--il", n] => pure (true, n)
    | [n] => pure (false, n)
    | _ => IO.eprintln "usage: Emit.lean [--il] <name>"; return 2
  match suites.find? (·.1 == name) with
  | none => IO.eprintln s!"unknown suite {name}"; return 2
  | some (_, fs) =>
    if il then
      match Print.module fs with
      | .ok s => IO.println s; return 0
      | .error e => IO.eprintln s!"{name}: {e}"; return 1
    else
      match compile Arm64.isa fs with
      | .ok code => IO.print (emitAsm fs code); return 0
      | .error e => IO.eprintln s!"{name}: {e}"; return 1
