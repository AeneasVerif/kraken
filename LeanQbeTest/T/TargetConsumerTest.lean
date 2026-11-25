module
public import LeanQbe.T.CoreHub
public import LeanQbe.T.FlatLemmas
public import LeanQbe.T.Target

/-!
# Cross-Module `t_kernel_rfl`, Co-Import, `ToExpr`, and Axiom Audit for `Target.lean`

Verifies in a separate downstream `module` that:
1. `Target` co-imports cleanly alongside `LeanQbe.T.CoreHub` (no `region`/`cell64`/`array64`
   collisions).
2. `Fn.backendOk` (across `.let_` `zext`/`bswap`/`add`, `.group`/`.jump`, `.load`/`.store`,
   `assignArgs`/`assignRets`) and `Trie.insert`/`erase`/`find?` reduce in the Lean kernel across a
   `module` boundary via `t_kernel_rfl`.
3. `Hints` derives `Lean.ToExpr` for elaborator literal splicing.
4. Every theorem in `Target.lean` has standard axioms `[propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false
@[expose] public section
namespace LeanQbe.T.TargetConsumerTest
open LeanQbe.T

def toyIsa : Isa where
  Reg := Nat; VReg := Empty; Cond := Bool; Directive := Unit
  gpr := {
    condReads := fun _ => 0#8, negCond := not, zeroFlags := [], clearFlags := [],
    mov := fun _ _ => [], movi := fun _ _ => [], setcc := fun _ _ => [],
    jmp := fun _ => [], jcc := fun _ _ => [], jnzGpr := fun _ _ => ([], 0#8),
    op := fun _ _ _ _ => none, load := fun _ _ _ => none, store := fun _ _ _ => none,
    supportsScalarOp := defaultSupportsScalarOp [8, 16, 32, 64] false false false
  }
  vec := VecIsa.empty Nat Bool Unit
  frame := {
    label := fun _ => (), sp := 0, scratch := [1], allocatable := [2, 3], calleeSaved := [4],
    raRegs := [], argRegs := [2, 3], retRegs := [2], raBytes := 8, frameSize := (8 * ·),
    prologue := fun _ => ([], 0#8), epilogue := fun _ => ([], 0#8),
    slotSt := fun _ _ => [], slotLd := fun _ _ => [], canonAbi := fun _ _ => ([], 0#8),
    call := fun _ => [], exitJmp := fun _ => [], ret := []
  }

def sampleFn : Fn := ⟨"f", [i32, i64], [i64], fun _ _ (a, ptr, ()) =>
  .let_ ⟨.zext 32 64, (.var a, ())⟩ fun (z, ()) =>
  .let_ ⟨.bswap i64, (.var z, ())⟩ fun (sw, ()) =>
  .group (sig := [[i64]])
    (fun _ => .cons (ts := [i64])
      (fun (acc, ()) => .store (.var acc) (.var ptr) (.ret (.var acc, ()))) .nil)
    (fun (lbl, ()) => .jump lbl (.var sw, ()))⟩

def badFloatFn : Fn := ⟨"bad", [i64], [i64], fun _ _ (a, ()) =>
  .let_ ⟨.fadd (.float .d), (.imm 0#64, .imm 0#64, ())⟩ fun _ => .ret (.var a, ())⟩

theorem backendOk_cross_module_rfl : sampleFn.backendOk toyIsa = true := by t_kernel_rfl
theorem backendOk_rejects_float_rfl : badFloatFn.backendOk toyIsa = false := by t_kernel_rfl

theorem trie_cross_module_rfl :
    (((Trie.empty.insert (2 ^ 80 + 5) (42 : Nat)).insert 7 99).erase 7).find? (2 ^ 80 + 5) =
      some 42 ∧
    (((Trie.empty.insert (2 ^ 80 + 5) (42 : Nat)).insert 7 99).erase 7).find? 7 = none := by
  exact ⟨by t_kernel_rfl, by t_kernel_rfl⟩

def sampleHintsExpr : Lean.Expr :=
  Lean.toExpr ({ dest := Trie.empty.insert 0 (.gpr (2 : Nat)), nslots := 2 } : Hints Nat Nat Bool)

#print axioms backendOk_cross_module_rfl
#print axioms backendOk_rejects_float_rfl
#print axioms trie_cross_module_rfl
#print axioms LeanQbe.T.trie_insert_rfl
#print axioms LeanQbe.T.Trie.find?_insert
#print axioms LeanQbe.T.Trie.find?_insert_self
#print axioms LeanQbe.T.Trie.find?_insert_ne
#print axioms LeanQbe.T.Trie.find?_erase
#print axioms LeanQbe.T.Trie.find?_erase_self
#print axioms LeanQbe.T.Trie.find?_erase_ne
#print axioms LeanQbe.T.Fn.assign_of_backendOk
#print axioms LeanQbe.T.AbiGprHolds.toGprHolds
#print axioms LeanQbe.T.VecTarget.empty
#print axioms LeanQbe.T.core_bitcount_and_fp_gates

end LeanQbe.T.TargetConsumerTest
