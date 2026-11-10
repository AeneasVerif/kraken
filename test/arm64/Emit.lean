import LeanQbeArm64

/-!
AArch64 assembly emitter for the litmus programs (not a module; run with
`lake env lean --run test/arm64/Emit.lean <name>`). Compiles with the same pipeline as `leanqbe`
(`compileFn`), instantiated with `Arm64.isa`, and prints with Kraken's AArch64 printer.
-/

open LeanQbe

def progs : List Fn := [Arm64.Tracer.tracer]

def emitAsm (fs : List Fn) (code : List Arm64.isa.Directive) : String :=
  let hdr := ".text\n" ++ String.join (fs.map fun f => s!".globl {f.name}\n") ++ ".p2align 2\n"
  hdr ++ String.intercalate "\n" (code.map Kraken.AArch64.Print.directive) ++ "\n"

def main (args : List String) : IO UInt32 := do
  match args with
  | [name] =>
    match progs.find? (·.name == name) with
    | none => IO.eprintln s!"unknown function {name}"; return 2
    | some f =>
      match compileFn Arm64.isa f with
      | .ok code => IO.print (emitAsm [f] code); return 0
      | .error e => IO.eprintln s!"{name}: {e}"; return 1
  | _ => IO.eprintln "usage: Emit.lean <name>"; return 2
