module

public import Kraken.X64.Semantics
public import Kraken.X64.Inert
public import Kraken.Data.List.Infix

public class Host where
  prog : Program
  layout : Layout
  /-- Two directives at the same address have the same offset in the executable. -/
  addr_determines_offset : ∀ j k, (layout.apply prog).addrOf j = (layout.apply prog).addrOf k →
    (layout.apply prog).sizeBefore j = (layout.apply prog).sizeBefore k

public instance [Host] : Layout := Host.layout

@[expose] public def Host.exe [Host] : Executable := Host.layout.apply Host.prog

@[expose] public def Host.addrOf [Host] (k : Nat) : Int64 := Host.exe.addrOf k

public instance [Host] : Labels := Executable.labels Host.exe

public theorem Host.sizeBefore_eq_of_addrOf_eq [Host] {j k : Nat} (h : Host.addrOf j = Host.addrOf k) :
    Host.exe.sizeBefore j = Host.exe.sizeBefore k :=
  Host.addr_determines_offset j k h

@[expose] public def Host.startAddr [Host] {p : Program} (h : p.IsInfix Host.prog) : Int64 :=
  Host.addrOf (p.infixIdx Host.prog h)

@[expose] public def Host.endAddr [Host] {p : Program} (h : p.IsInfix Host.prog) : Int64 :=
  Host.addrOf (p.infixIdx Host.prog h + p.length)

export Host (startAddr endAddr)

public theorem Layout.apply_getElem? [layout : Layout] (p : Program) (i : Nat) :
    (layout p).program[i]? = (p[i]?).map (fun d => {directive := d, size := layout.size d i}) := by
  simp [Kraken.Layout.apply, List.getElem?_mapIdx]

public theorem Host.exe_getElem? [Host] (i : Nat) :
    Host.exe.program[i]? = Host.prog[i]?.map (fun d => {directive := d, size := Host.layout.size d i}) :=
  Layout.apply_getElem? _ _

public theorem Host.addrOf_succ [Host] {k : Nat} {d : Directive} (hd : Host.prog[k]? = some d) :
    Host.addrOf (k + 1) = Host.addrOf k + .ofNat (Host.layout.size d k) :=
  Kraken.Executable.addrOf_succ _ (c := {directive := d, size := Host.layout.size d k}) (by rw [Host.exe_getElem?, hd]; rfl)

section
variable [Host]

public theorem Host.inert_of_size_zero {d : Directive} (h : {directive := d, size := 0} ∈ Host.exe.program) : d.Inert :=
  Host.layout.inert_of_mem h rfl

public theorem Host.directivesAtAddress_addrOf {k : Nat} {c : Kraken.Sized Directive}
    (hc : Host.exe.program[k]? = some c) (hz : 0 < c.size) :
    ∃ pre : List (Kraken.Sized Directive), Host.exe.directivesAtAddress (Host.addrOf k) = pre ++ [c] ∧
      ∀ c ∈ pre, c.size = 0 :=
  Host.exe.directivesAtAddress_addrOf (fun _ _ h => Host.sizeBefore_eq_of_addrOf_eq h) hc hz

end
