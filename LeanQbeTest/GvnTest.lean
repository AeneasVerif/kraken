module

public import LeanQbe.GvnLemmas
public import LeanQbe.WPLemmas
public import LeanQbe.FlatLemmas

/-! Tests of `Func.gvn`: outputs by `rfl` in the kernel, `Wf`, and a contract through `gvn_spec`.

The elaborator's `rfl` fails on `Func.gvn prog = …` (its `isDefEq` gives up on the table lookups under
the binders), while the kernel checks it at once; hence `kernel_rfl` (`LeanQbe.FlatLemmas`), which hands
`Eq.refl` to the kernel without the elaborator's check. -/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.GvnTest

/-- `x = add a b; y = add a b; jnz a, (u = add a b; z = mul x u; ret z), (w = load p; v = load p; ret v)` -/
def prog : Func := fun _ _ =>
  .param fun a => .param fun b => .param fun p =>
  .let_ (.bin .l .add (.var a) (.var b)) fun x =>
  .let_ (.bin .l .add (.var a) (.var b)) fun y =>
  .jnz (.var a)
    (.let_ (.bin .l .add (.var a) (.var b)) fun u =>
     .let_ (.bin .l .mul (.var y) (.var u)) fun z => .ret [.var z, .var x])
    (.load .l .l false (.var p) fun _ => .load .l .l false (.var p) fun v => .ret [.var v, .var y])

/-- Both repeated `add`s, including the one inside the branch, are replaced by `x`; loads are kept. -/
theorem gvn_prog_out : Func.gvn prog = fun _ _ =>
    .param fun a => .param fun b => .param fun p =>
    .let_ (.bin .l .add (.var a) (.var b)) fun x =>
    .jnz (.var a)
      (.let_ (.bin .l .mul (.var x) (.var x)) fun z => .ret [.var z, .var x])
      (.load .l .l false (.var p) fun _ => .load .l .l false (.var p) fun v => .ret [.var v, .var x]) := by
  kernel_rfl

theorem prog_wf : prog.Wf := by wf_tac

theorem gvn_prog_wf : (Func.gvn prog).Wf := Func.gvn_wf prog_wf

/-- The contract of the optimised function, proved on the source. -/
theorem gvn_prog_spec (Γ : Env) (a b p : Val) (m : Mem 64) (hp : ∃ v, loadVal m .l .l false p = some v) :
    Func.spec Γ (Func.gvn prog) [a, b, p] m
      (fun r m' => (r.head? = some ((a + b) * (a + b)) ∨ r.tail = [a + b]) ∧ m' = m)
      (fun _ _ _ => False) := by
  apply Func.gvn_spec prog_wf
  obtain ⟨v, hv⟩ := hp
  simp only [Func.spec, prog, wp, Op.wp, Op.eval, BinOp.eval, Arg.val, List.map, Option.some.injEq,
    exists_eq_left', hv, true_and, List.head?_cons, List.tail_cons, and_true]
  exact ⟨fun _ => .inl trivial, fun _ => .inr trivial⟩

end LeanQbe.GvnTest
