module

public import Kraken.X64.Semantics
public import Kraken.Data.List.Infix

public class Host where
  prog : Program
  layout : WellFormedLayout prog

public instance [Host] : WellFormedLayout Host.prog := Host.layout

@[expose] public def Host.exe [Host] : Executable := Host.prog.toExecutable

@[expose] public def Host.addrOf [Host] (k : Nat) : Int64 := Host.exe.addrOf k

public abbrev Host.size [Host] (d : Directive) (i : Nat) : Nat := Host.layout.size d i

public instance [Host] : Labels := Executable.labels Host.exe

public theorem Host.sizeBefore_eq_of_addrOf_eq [Host] {j k : Nat} (h : Host.addrOf j = Host.addrOf k) :
    Host.exe.sizeBefore j = Host.exe.sizeBefore k :=
  Kraken.Program.sizeBefore_eq_of_addrOf_eq Host.prog h

@[expose] public def Host.startAddr [Host] {p : Program} (h : p.IsInfix Host.prog) : Int64 :=
  Host.addrOf (p.infixIdx Host.prog h)

@[expose] public def Host.endAddr [Host] {p : Program} (h : p.IsInfix Host.prog) : Int64 :=
  Host.addrOf (p.infixIdx Host.prog h + p.length)

export Host (startAddr endAddr)
