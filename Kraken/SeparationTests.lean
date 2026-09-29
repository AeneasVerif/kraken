module

import Kraken.Mem
import Kraken.Separation
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
    (h : (Eq ((Int.toBytes 8 rax.toBitVec.toInt).At rdi.toBitVec) ⋆
      (Eq (v2.At (rdi.toBitVec + 8#64)) ⋆ R))
      (Mem.storeInt mem rdi.toBitVec 8 rax.toBitVec.toInt)) :
    (Eq (v2.At (rdi.toBitVec + 8#64)) ⋆
      (Eq ((Int.toBytes 8 rax.toBitVec.toInt).At rdi.toBitVec) ⋆ R))
      (Mem.storeInt mem rdi.toBitVec 8 rax.toBitVec.toInt) := by
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

-- Regression test: unification should fail fast without unfolding `List.At` or `sep`.
/--
error: Application type mismatch: The argument
  h
has type
  (Eq (UInt64.At 0 addr) ⋆ (Eq (v.At (addr + 8#64)) ⋆ R)) m
but is expected to have type
  (Eq (v.At (addr + 8#64)) ⋆ ?m.54) m
in the application
  Exists.intro ?m.54 h

Note: The following definitions were not unfolded because their definition is not exposed:
  List.At ↦ 4
  sep ↦ 6
---
error: unsolved goals
v : UInt64
addr : BitVec 64
R : Mem 64 → Prop
m : Mem 64
h : (Eq (UInt64.At 0 addr) ⋆ (Eq (v.At (addr + 8#64)) ⋆ R)) m
⊢ ∃ R', (Eq (v.At (addr + 8#64)) ⋆ R') m
-/
#guard_msgs in
set_option maxHeartbeats 1000 in
example (v : UInt64) (addr : BitVec 64) (R : Mem 64 → Prop) (m : Mem 64)
    (h : (Eq ((0 : UInt64).At addr) ⋆ (Eq (v.At (addr + 8#64)) ⋆ R)) m) :
    ∃ R', (Eq (v.At (addr + 8#64)) ⋆ R') m := by
  exact ⟨_, h⟩

end Kraken.SeparationTests
