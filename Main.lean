module

public import LeanQbe.Main
public import LeanQbe.Examples.Litmus
public import Kraken.X64.PrintATT

/-!
`leanqbe` command-line driver (x64). Version 0: `leanqbe <program>` prints GNU assembler input for
one of the built-in litmus programs (`leanqbe --list` lists them). A parser for QBE IL text comes
in step 3.
-/

open LeanQbe

/-- Built-in programs: name, units. -/
def programs : List (String × List (FnHints Amd64.isa)) :=
  [("tracer", [⟨Litmus.tracer, Litmus.tracerHints⟩])]

/-- GNU as text for x64: `.text`, a `.globl` per function, then Kraken's AT&T printer. -/
def emitAsm (us : List (FnHints Amd64.isa)) (code : List Amd64.isa.Directive) : String :=
  let globls := us.map (fun u => s!".globl {u.fn.name}\n") |>.foldl (· ++ ·) ""
  ".text\n" ++ globls ++ Kraken.X64.toATT code ++ "\n"

public def main (args : List String) : IO UInt32 := do
  match args with
  | ["--list"] =>
    for (n, _) in programs do IO.println n
    return 0
  | [name] =>
    match programs.find? (·.1 == name) with
    | none =>
      IO.eprintln s!"leanqbe: unknown program {name} (try --list)"
      return 2
    | some (_, us) =>
      match compile us with
      | .ok code =>
        IO.print (emitAsm us code)
        return 0
      | .error e =>
        IO.eprintln s!"leanqbe: {e}"
        return 1
  | _ =>
    IO.eprintln "usage: leanqbe <program> | --list"
    return 2
