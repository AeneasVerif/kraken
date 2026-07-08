import KrakenStdlibCandidates
import Init.Grind
import Init.Data.BitVec
import Init.Data.Int.Bitwise.Lemmas
open Lean.Grind in #remove_toint_instances

@[grind_homo] theorem natCast_toNat {w} (x : BitVec w) : (x.toNat : Int) = x.unsigned := rfl

example (α : Type) (l1 l2 : List α) (x : α) (a b : BitVec 32)
  (h_len : (l1 ++ l2).length = (a + b).toNat)
  (h_a : a < b) :
  (((l1.take a.toNat).reverse ++ (l2.drop b.toNat)).concat x).length ≤ (a + b).toNat + 1 := by
  grind
