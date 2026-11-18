module

public import Kraken.X64.Semantics
public import Kraken.Data.List.Infix

open Kraken (Layout WellFormedLayout)

public class Host where
  prog : Program
  layout : WellFormedLayout prog

public instance [Host] : WellFormedLayout Host.prog := Host.layout

@[expose] public def Host.exe [Host] : Executable := Host.prog.toExecutable

@[expose] public def Host.addrOf [Host] (k : Nat) : Int64 := Host.exe.addrOf k

public abbrev Host.size [Host] (i : Nat) : Nat := Host.layout.size i

public instance [Host] : Labels := Executable.labels Host.exe

public theorem Host.sizeBefore_eq_of_addrOf_eq [Host] {j k : Nat} (h : Host.addrOf j = Host.addrOf k) :
    Host.exe.sizeBefore j = Host.exe.sizeBefore k :=
  Kraken.Program.sizeBefore_eq_of_addrOf_eq Host.prog h
@[expose] public def Host.startAddr [Host] {p : Program} (h : p.IsInfix Host.prog) : Int64 :=
  Host.addrOf (p.infixIdx Host.prog h)

@[expose] public def Host.endAddr [Host] {p : Program} (h : p.IsInfix Host.prog) : Int64 :=
  Host.addrOf (p.infixIdx Host.prog h + p.length)

export Host (startAddr endAddr)
/-- The address of a label is the address of its first occurrence in the ambient program. -/
public theorem Host.label_addrOf [Host] {l : Label} {j : Nat} (hj : Host.prog[j]? = some (.label l))
    (hfirst : ∀ i, i < j → Host.prog[i]? ≠ some (.label l)) :
    label l = Host.addrOf j := by
  show ((Host.prog.toExecutable.withAddresses.findSome?
      (fun {directive, addr, ..} => if directive = .label l then .some addr else .none)).getD (-1))
    = Host.prog.toExecutable.addrOf j
  apply Kraken.Layout.withAddresses_findSome?_label
  obtain ⟨hlt, hjl⟩ := List.getElem?_eq_some_iff.mp hj
  rw [List.findIdx?_eq_some_iff_getElem]
  refine ⟨hlt, by simp [hjl], fun i hi => ?_⟩
  have := hfirst i hi
  simp_all [List.getElem?_eq_getElem (Nat.lt_trans hi hlt)]
