module

-- Ported from bedrock2/src/bedrock2/Memory.v at mit-plv/bedrock2@757f17c6083bf8d43b5293a0db545c8d0aa32a13

public import Kraken.Bedrock2.Syntax
public import Kraken.Mem

@[expose] public section

open Std

namespace Kraken.Bedrock2

variable {w : Nat}

def load? (sz : AccessSize) (m : Mem w) (a : BitVec w) : Option (BitVec w) :=
  (m.loadInt a sz.bytes).map (BitVec.ofInt w)

def store? (sz : AccessSize) (m : Mem w) (a v : BitVec w) : Option (Mem w) :=
  (m.loadBytes a sz.bytes).map fun _ => m.storeInt a sz.bytes v.toNat

def anybytes (a : BitVec w) (n : Nat) (m : Mem w) : Prop :=
  ∃ bs : List UInt8, bs.At a = m ∧ bs.length = n ∧ n ≤ 2 ^ w

def split (m m1 m2 : Mem w) : Prop :=
  m1.union m2 = m ∧ m1.inter m2 = ∅

end Kraken.Bedrock2
