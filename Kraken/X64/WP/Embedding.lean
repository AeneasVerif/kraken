module

public import Kraken.X64.WP.Host

public structure Embedding [Host] (p : Program) where
  start : Nat
  isInfixAt : p.IsInfixAt Host.prog start

section
variable [Host]

@[expose] public def Embedding.ofIsInfixAt {p q : Program} (e : Embedding q) {i : Nat}
    (h : p.IsInfixAt q i) : Embedding p :=
  ⟨e.start + i, List.IsInfixAt.trans h e.isInfixAt⟩

@[expose] public def Embedding.startAddr {p : Program} (e : Embedding p) : Int64 := Host.addrOf e.start

@[expose] public def Embedding.endAddr {p : Program} (e : Embedding p) : Int64 :=
  Host.addrOf (e.start + p.length)

end
