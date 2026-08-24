import Kraken.Mem
import Kraken.SeparationTactics

open Std.ExtHashMap

namespace Kraken.SeparationTests

def indexed {w} (index : Nat) (p : Mem w → Prop) : Mem w → Prop :=
  fun m => p m ∧ index = index

example {w} (A B : Mem w → Prop) : A ⋆ B = B ⋆ A := by ecancel

example {w} (A B : Mem w → Prop) : indexed 0 A ⋆ B = B ⋆ indexed 0 A := by ecancel

example {w} (A B : Mem w → Prop) : emp ⋆ A ⋆ B = B ⋆ A := by ecancel

example {w} (A B C D : Mem w → Prop) : A ⋆ (B ⋆ C) ⋆ D = (D ⋆ B) ⋆ (A ⋆ C) := by ecancel

example {w} (A B C : Mem w → Prop) (m : Mem w) (h : (A ⋆ (B ⋆ C)) m) : ((C ⋆ A) ⋆ B) m := by ecancel

example (v2 rax rdi : UInt64) (R : Mem 64 → Prop) (mem : Mem 64)
    (h : (Eq ((BitVec.toBytes 8 rax.toBitVec).At rdi.toBitVec) ⋆
      (Eq (v2.At (rdi.toBitVec + 8#64)) ⋆ R))
      (Mem.storeBV mem rdi.toBitVec 8 rax.toBitVec)) :
    (Eq (v2.At (rdi.toBitVec + 8#64)) ⋆
      (Eq ((BitVec.toBytes 8 rax.toBitVec).At rdi.toBitVec) ⋆ R))
      (Mem.storeBV mem rdi.toBitVec 8 rax.toBitVec) := by
  ecancel

example (v : UInt64) (a : BitVec 64) (R : Mem 64 → Prop) :
    Eq (v.At a) ⋆ R = R ⋆ Eq (v.toBytes.At a) := by
  ecancel

example {w} (A : Mem w → Prop) : ∃ X : Mem w → Prop, A = X ⋆ A := by refine ⟨?_, by ecancel⟩

example {w} (A B C : Mem w → Prop) : ∃ X : Mem w → Prop, A ⋆ (B ⋆ C) = X ⋆ A := by refine ⟨?_, by ecancel⟩

example {w} (A B : Mem w → Prop) :
    ∃ index : Nat, indexed index A ⋆ B = B ⋆ indexed 3 A := by
  refine ⟨?_, by ecancel⟩

example {w} (A : Mem w → Prop) :
    ∃ index : Nat,
      indexed index A ⋆ indexed 1 A = indexed 1 A ⋆ indexed 2 A := by
  refine ⟨?_, by ecancel⟩

example {w} (A : Mem w → Prop) :
    ∃ x y : Nat, indexed x A ⋆ indexed 1 A = indexed y A ⋆ indexed 2 A := by
  refine ⟨?_, ?_, by ecancel⟩

end Kraken.SeparationTests
