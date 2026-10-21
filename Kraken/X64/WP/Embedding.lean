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

@[expose] public def Embedding.ofIsInfix {p : Program} (h : p.IsInfix Host.prog) : Embedding p :=
  ⟨p.infixIdx Host.prog h, List.isInfixAt_infixIdx h⟩

@[expose] public def Embedding.startAddr {p : Program} (e : Embedding p) : Int64 := Host.addrOf e.start

@[expose] public def Embedding.endAddr {p : Program} (e : Embedding p) : Int64 :=
  Host.addrOf (e.start + p.length)

@[grind =] public theorem Embedding.endAddr_def {p : Program} (e : Embedding p) :
    e.endAddr = Host.addrOf (e.start + p.length) := rfl

@[grind =] public theorem Embedding.startAddr_def {p : Program} (e : Embedding p) :
    e.startAddr = Host.addrOf e.start := rfl

@[grind =] public theorem Embedding.start_ofIsInfixAt {p q : Program} (e : Embedding q) {i : Nat}
    (h : p.IsInfixAt q i) : (e.ofIsInfixAt h).start = e.start + i := rfl

@[grind =] public theorem Embedding.endAddr_cons_head (d : Directive) (p : Program) (e : Embedding (d :: p)) :
    (e.ofIsInfixAt (List.isInfixAt_cons_head d p)).endAddr =
      (e.ofIsInfixAt (List.isInfixAt_cons_tail d p)).startAddr :=
  rfl

end
