module

public import Kraken.X64.Semantics
public import Kraken.Data.List.Infix

open Kraken (Layout)

public class Host where
  prog : Program
  layout : Layout
  wf : layout.WellFormed prog

public instance [Host] : Host.layout.WellFormed Host.prog := Host.wf

@[expose] public def Host.exe [Host] : Executable := Host.layout.apply Host.prog

@[expose] public def Host.addrOf [Host] (k : Nat) : Int64 := Host.exe.addrOf k

public abbrev Host.size [Host] (i : Nat) : Nat := Host.layout.dirSize Host.prog i

public instance [Host] : Labels := Executable.labels Host.exe

public theorem Host.offsetOf_eq_of_addrOf_eq [Host] {j k : Nat} (h : Host.addrOf j = Host.addrOf k) :
    Host.exe.offsetOf j = Host.exe.offsetOf k :=
  Kraken.Program.offsetOf_eq_of_addrOf_eq Host.wf h
@[expose] public def Host.startAddr [Host] {p : Program} (h : p.IsInfix Host.prog) : Int64 :=
  Host.addrOf (p.infixIdx Host.prog h)

@[expose] public def Host.endAddr [Host] {p : Program} (h : p.IsInfix Host.prog) : Int64 :=
  Host.addrOf (p.infixIdx Host.prog h + p.length)

export Host (startAddr endAddr)
