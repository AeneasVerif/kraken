module

public import LeanQbe.Main
public import LeanQbe.Examples.Litmus
public import LeanQbe.Examples.LitmusCf
public import Kraken.X64.PrintATT
public import LeanQbe.Print

/-!
`leanqbe` command-line driver (x64). Version 0: `leanqbe <program>` prints GNU assembler input for
one of the built-in litmus programs, `leanqbe --il <program>` its QBE IL text (for stock QBE),
`leanqbe --list` lists them. A parser for QBE IL text comes
in step 3.
-/

open LeanQbe

/-- Built-in programs: name, functions. -/
def programs : List (String × List Fn) :=
  [Litmus.tracer, Litmus.ifelse, Litmus.sumto, Litmus.evenodd, Litmus.nested, Litmus.swap].map
    fun f => (f.name, [f])

/-- GNU as text for x64: `.text`, a `.globl` per function, then Kraken's AT&T printer. -/
def emitAsm (fs : List Fn) (code : List Amd64.isa.Directive) : String :=
  let globls := fs.map (fun f => s!".globl {f.name}\n") |>.foldl (· ++ ·) ""
  ".text\n" ++ globls ++ Kraken.X64.toATT code ++ "\n"

public def main (args : List String) : IO UInt32 := do
  match args with
  | ["--list"] =>
    for (n, _) in programs do IO.println n
    return 0
  | ["--il", name] =>
    match programs.find? (·.1 == name) with
    | none =>
      IO.eprintln s!"leanqbe: unknown program {name} (try --list)"
      return 2
    | some (_, fs) =>
      match Print.module fs with
      | .ok t =>
        IO.println t
        return 0
      | .error e =>
        IO.eprintln s!"leanqbe: {e}"
        return 1
  | [name] =>
    match programs.find? (·.1 == name) with
    | none =>
      IO.eprintln s!"leanqbe: unknown program {name} (try --list)"
      return 2
    | some (_, us) =>
      match compile Amd64.isa us with
      | .ok code =>
        IO.print (emitAsm us code)
        return 0
      | .error e =>
        IO.eprintln s!"leanqbe: {e}"
        return 1
  | _ =>
    IO.eprintln "usage: leanqbe <program> | leanqbe --il <program> | leanqbe --list"
    return 2
