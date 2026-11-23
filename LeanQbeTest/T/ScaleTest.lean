module

public import LeanQbe.T.FlatLemmas

/-!
# Scaling checks for `TFlat` reification

Verifies `Func.Wf` by kernel `rfl` (`t_wf_reify`) and `Func.checkTFlat ... = true` at
250, 1000, and 2000 `let`s (`sl 250`, `sl 1000`, `sl 2000`), a self-jumping 50-block `group`
(`bl 50`, 151 instructions), and a cross-block jumping 50-block `group` (`bl50_cross`). Detailed
elaboration, codegen, and kernel timings for literal syntax programs are recorded in
`docs/reports/core.md`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.ScaleTest

def mkSL {V : Ty → Type} {L : List Ty → Type} : Nat → V i64 → V i64 → Expr V L [i64]
  | 0, _, x => .ret (.var x, ())
  | n + 1, a, x => .let_ (op2 (.add i64) (.var x) (.var a)) fun (y, ()) => mkSL n a y

noncomputable def sl250 : Func [i64] [i64] := fun _ _ (a, ()) => mkSL 250 a a
noncomputable def sl1000 : Func [i64] [i64] := fun _ _ (a, ()) => mkSL 1000 a a
noncomputable def sl2000 : Func [i64] [i64] := fun _ _ (a, ()) => mkSL 2000 a a

def mkBlocks {V : Ty → Type} {L : List Ty → Type} :
    (k : Nat) → V i64 → Tup L (List.replicate k [i64]) → Blocks V L [i64] (List.replicate k [i64])
  | 0, _, () => .nil
  | _ + 1, a, (l, ls) =>
    .cons (fun (x, ()) =>
      .let_ (op2 (.add i64) (.var x) (.imm 1)) fun (y1, ()) =>
      .let_ (op2 (.add i64) (.var y1) (.var a)) fun (y2, ()) =>
      .let_ (op2 (.add i64) (.var y2) (.imm 2)) fun (y3, ()) =>
      .jump l (.var y3, ()))
      (mkBlocks _ a ls)

noncomputable def bl50 : Func [i64] [i64] := fun _ _ (a, ()) =>
  .group (sig := List.replicate 50 [i64])
    (fun Js => mkBlocks 50 a Js)
    (fun Js => .jump Js.1 (.var a, ()))

def mkBlocksCrossAux {V : Ty → Type} {L : List Ty → Type} (l0 : L [i64]) (a : V i64) :
    (k : Nat) → Tup L (List.replicate k [i64]) → Blocks V L [i64] (List.replicate k [i64])
  | 0, () => .nil
  | 1, (_, ()) =>
    .cons (fun (x, ()) =>
      .let_ (op2 (.add i64) (.var x) (.imm 1)) fun (y1, ()) =>
      .let_ (op2 (.add i64) (.var y1) (.var a)) fun (y2, ()) =>
      .let_ (op2 (.add i64) (.var y2) (.imm 2)) fun (y3, ()) =>
      .jump l0 (.var y3, ()))
      .nil
  | k + 2, (_, ls) =>
    .cons (fun (x, ()) =>
      .let_ (op2 (.add i64) (.var x) (.imm 1)) fun (y1, ()) =>
      .let_ (op2 (.add i64) (.var y1) (.var a)) fun (y2, ()) =>
      .let_ (op2 (.add i64) (.var y2) (.imm 2)) fun (y3, ()) =>
      .jump ls.1 (.var y3, ()))
      (mkBlocksCrossAux l0 a (k + 1) ls)

noncomputable def bl50_cross : Func [i64] [i64] := fun _ _ (a, ()) =>
  .group (sig := List.replicate 50 [i64])
    (fun Js => mkBlocksCrossAux Js.1 a 50 Js)
    (fun Js => .jump Js.1 (.var a, ()))

theorem sl250_wf : Func.Wf sl250 := by t_wf_reify
theorem sl1000_wf : Func.Wf sl1000 := by t_wf_reify
theorem sl2000_wf : Func.Wf sl2000 := by t_wf_reify
theorem bl50_wf : Func.Wf bl50 := by t_wf_reify
theorem bl50_cross_wf : Func.Wf bl50_cross := by t_wf_reify

theorem sl250_check : Func.checkTFlat sl250 = true := by t_kernel_rfl
theorem sl1000_check : Func.checkTFlat sl1000 = true := by t_kernel_rfl
theorem sl2000_check : Func.checkTFlat sl2000 = true := by t_kernel_rfl
theorem bl50_check : Func.checkTFlat bl50 = true := by t_kernel_rfl
theorem bl50_cross_check : Func.checkTFlat bl50_cross = true := by t_kernel_rfl

end LeanQbe.T.ScaleTest
