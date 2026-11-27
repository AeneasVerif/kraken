module

public import LeanQbe.T.Logic.SlabLayoutElab
public import LeanQbe.T.Logic.SepTree
public import LeanQbe.T.Logic.SlabChain
meta import LeanQbe.T.Logic.SlabLayoutElab

/-!
# Tests for `C0Lens`, `SepTree`, and `SlabChain`

Verifies lawful lens composition (`C0Lens.comp`), `C0Lens.modify`, list element updates
(`C0Lens.set_list`), `AgreesExcept` framing (`C0Lens.agreesExcept_set`,
`C0Lens.get_of_agreesExcept`), and standard axioms (`[propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

namespace LeanQbeTest.T.SlabLayoutTest

open LeanQbe.T

@[expose] public section

structure SlicedCore where
  arenaLen : Nat
  arena : List (BitVec 32)

structure SlicedScratch where
  ticks : BitVec 64
  heap : List (BitVec 32)

structure SlicedState where
  core : SlicedCore
  scratch : SlicedScratch

def lensCore : C0Lens SlicedState SlicedCore where
  get s := s.core
  set s k := { s with core := k }
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

def lensCoreArena : C0Lens SlicedCore (List (BitVec 32)) where
  get k := k.arena
  set k xs := { k with arena := xs }
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

def lensScratchHeap : C0Lens SlicedState (List (BitVec 32)) where
  get s := s.scratch.heap
  set s xs := { s with scratch := { s.scratch with heap := xs } }
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

def lensArena : C0Lens SlicedState (List (BitVec 32)) :=
  C0Lens.comp lensCore lensCoreArena

end

public section

theorem sliced_lens_comp_get (s : SlicedState) :
    lensArena.get s = s.core.arena := rfl

theorem sliced_lens_comp_set (s : SlicedState) (xs : List (BitVec 32)) :
    (lensArena.set s xs).core.arena = xs := rfl

theorem sliced_scratch_agrees (s : SlicedState) (i : Nat) (v : BitVec 32) :
    AgreesExcept (fun t : SlicedState => { t with scratch := s.scratch })
      s (lensScratchHeap.set_list s i v) :=
  lensScratchHeap.agreesExcept_set (fun t => { t with scratch := s.scratch }) s _

theorem sliced_core_preserved (s : SlicedState) (i : Nat) (v : BitVec 32) :
    lensArena.get (lensScratchHeap.set_list s i v) = lensArena.get s :=
  lensArena.get_of_agreesExcept (sliced_scratch_agrees s i v)

theorem sliced_heap_length (s : SlicedState) (i : Nat) (v : BitVec 32) :
    (lensScratchHeap.get (lensScratchHeap.set_list s i v)).length =
      (lensScratchHeap.get s).length :=
  lensScratchHeap.length_set_list s i v

theorem sliced_heap_get_self (s : SlicedState) {i : Nat} (v : BitVec 32)
    (hi : i < s.scratch.heap.length) :
    (lensScratchHeap.get (lensScratchHeap.set_list s i v))[i]? = some v :=
  lensScratchHeap.getElem?_set_list_self s v hi

theorem sliced_heap_get_ne (s : SlicedState) {i j : Nat} (v : BitVec 32) (hne : i ≠ j) :
    (lensScratchHeap.get (lensScratchHeap.set_list s i v))[j]? = s.scratch.heap[j]? :=
  lensScratchHeap.getElem?_set_list_ne s v hne

#guard
  let s : SlicedState :=
    { core := { arenaLen := 1, arena := [10#32] }
      scratch := { ticks := 0#64, heap := [1#32, 2#32] } }
  (lensArena.modify (fun xs => xs ++ [20#32]) s).core.arena == [10#32, 20#32]

#print axioms SepTree.eval_eq_focus
#print axioms SepTree.focus
#print axioms SepTree.unfocus_eq
#print axioms SlabChain.to_region
#print axioms SlabChain.balancedTree_to_region
#print axioms C0Lens.comp
#print axioms C0Lens.agreesExcept_set
#print axioms sliced_core_preserved

end

end LeanQbeTest.T.SlabLayoutTest
