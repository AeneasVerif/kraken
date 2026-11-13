module

public import LeanQbe.Ops

/-!
# Lemmas about operations

Monotonicity of `Op.wp`, and the evaluation equations of the 64-bit operations as `simp` lemmas.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe

theorem Op.wp_mono {op : Op Val} {p q : Val → Prop} (h : ∀ v, p v → q v) : op.wp p → op.wp q :=
  fun ⟨v, hv, hp⟩ => ⟨v, hv, h v hp⟩

theorem Op.wp_of_eval {op : Op Val} {v : Val} (h : op.eval = some v) (p : Val → Prop) :
    op.wp p ↔ p v := by
  simp only [Op.wp, h, Option.some.injEq, exists_eq_left']

@[simp] theorem Arg.val_var (v : Val) : (Arg.var v).val = v := rfl
@[simp] theorem Arg.val_imm (c : Val) : (Arg.imm c : Arg Val).val = c := rfl

@[simp] theorem Cls.trunc_l (x : Val) : Cls.l.trunc x = x := rfl

@[simp] theorem Op.eval_bin_l (o : BinOp) (a b : Arg Val) :
    (Op.bin .l o a b).eval = o.eval a.val b.val := rfl

@[simp] theorem Op.eval_cmp_l (o : CmpOp) (a b : Arg Val) :
    (Op.cmp .l o a b).eval = some (boolVal (o.eval a.val b.val)) := rfl

@[simp] theorem Op.eval_copy (k : Cls) (a : Arg Val) : (Op.copy k a).eval = some (k.trunc a.val) := rfl

@[simp] theorem BinOp.eval_add {n : Nat} (a b : BitVec n) : BinOp.add.eval a b = some (a + b) := rfl
@[simp] theorem BinOp.eval_sub {n : Nat} (a b : BitVec n) : BinOp.sub.eval a b = some (a - b) := rfl
@[simp] theorem BinOp.eval_mul {n : Nat} (a b : BitVec n) : BinOp.mul.eval a b = some (a * b) := rfl
@[simp] theorem BinOp.eval_and {n : Nat} (a b : BitVec n) : BinOp.and.eval a b = some (a &&& b) := rfl
@[simp] theorem BinOp.eval_or {n : Nat} (a b : BitVec n) : BinOp.or.eval a b = some (a ||| b) := rfl
@[simp] theorem BinOp.eval_xor {n : Nat} (a b : BitVec n) : BinOp.xor.eval a b = some (a ^^^ b) := rfl

/-- The class-`w` result of every operation is zero-extended. -/
theorem Op.eval_w_hi {op : Op Val} {v : Val}
    (hk : (∃ o a b, op = .bin .w o a b) ∨ (∃ s sg a, op = .ext .w s sg a) ∨ (∃ a, op = .copy .w a))
    (h : op.eval = some v) : v = zext32 (lo32 v) := by
  rcases hk with ⟨o, a, b, rfl⟩ | ⟨s, sg, a, rfl⟩ | ⟨a, rfl⟩
  · simp only [Op.eval, Option.map_eq_some_iff] at h
    grind
  all_goals
    simp only [Op.eval, Cls.trunc, Option.some.injEq] at h
    grind

end LeanQbe
