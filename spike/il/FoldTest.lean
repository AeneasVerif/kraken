module

public import LeanQbe.FoldLemmas
public import LeanQbe.WPLemmas

/-! Tests of `Func.fold`: constant folding, copy propagation, algebraic identities, annihilators,
self-rules, power-of-two multiply strength reduction, and redundant `ext`/`copy` elimination, all checked
by `rfl`, plus `Func.fold_wf` and `Func.fold_spec`. -/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.FoldTest

/-- `x = add 1 2; y = copy.l x; z = add a y; c = cult y 4; jnz c, ret z, ret 0` -/
def prog : Func := fun _ _ =>
  .param fun a =>
  .let_ (.bin .l .add (.imm 1) (.imm 2)) fun x =>
  .let_ (.copy .l (.var x)) fun y =>
  .let_ (.bin .l .add (.var a) (.var y)) fun z =>
  .let_ (.cmp .l .ult (.var y) (.imm 4)) fun c =>
  .jnz (.var c) (.ret [.var z]) (.ret [.imm 0])

/-- Folded: `z = add a 3; ret z`. -/
example : Func.fold prog = fun _ _ => .param fun a => .let_ (.bin .l .add (.var a) (.imm 3)) fun z =>
    .ret [.var z] := rfl

theorem prog_wf : prog.Wf := by wf_tac

theorem fold_prog_wf : (Func.fold prog).Wf := Func.fold_wf prog_wf

/-- A pending label is not folded across (junk shape: `label`, then an instruction). -/
example : Func.fold (fun _ _ => .label fun _ => .let_ (.copy .l (.imm 7)) fun x => .ret [.var x]) =
    fun _ _ => .label fun _ => .let_ (.copy .l (.imm 7)) fun x => .ret [.var x] := rfl

theorem prog_fold_spec (Γ : Env) (a : Val) (m : Mem 64) :
    Func.spec Γ (Func.fold prog) [a] m (fun r m' => r = [a + 3] ∧ m' = m) (fun _ _ _ => False) := by
  apply Func.fold_spec prog_wf
  simp [Func.spec, prog, wp, Op.wp, Op.eval, BinOp.eval, CmpOp.eval, boolVal, Truthy, Arg.val,
    Cls.trunc]

/-! ## Algebraic identities, annihilators, self-rules, strength reduction, redundant `ext` -/

/-- Array-indexing pattern:
- `z0 = sub b b` → `0` (self-annihilator)
- `z1 = xor a a` → `0` (self-annihilator)
- `a1 = add a z0` → `a` (`add x 0`)
- `a2 = add z1 a1` → `a` (`add 0 x`)
- `a3 = sub a2 0` → `a` (`sub x 0`)
- `a4 = mul a3 1` → `a` (`mul x 1`)
- `a5 = mul 1 a4` → `a` (`mul 1 x`)
- `a6 = or a5 0` → `a` (`or x 0`)
- `a7 = xor a6 0` → `a` (`xor x 0`)
- `a8 = shl a7 0` → `a` (`shl x 0`)
- `a9 = and a8 (-1)` → `a` (`and x (-1)`)
- `a10 = ext .l .l true a9` → `a` (redundant 64-bit extension)
- `m0 = mul b 0` → `0`, `n0 = and b 0` → `0` (annihilators)
- `ce = ceql a10 a` → `1`, `cn = cnel b b` → `0`, `cu = cultl a a` → `0`, `cs = csltl b b` → `0`
- `jnz ce` taken; inside: `off = mul a10 8` → `shl a 3`, `off2 = mul 4 b` → `shl b 2`. -/
def algProg : Func := fun _ _ =>
  .param fun a => .param fun b =>
  .let_ (.bin .l .sub (.var b) (.var b)) fun z0 =>
  .let_ (.bin .l .xor (.var a) (.var a)) fun z1 =>
  .let_ (.bin .l .add (.var a) (.var z0)) fun a1 =>
  .let_ (.bin .l .add (.var z1) (.var a1)) fun a2 =>
  .let_ (.bin .l .sub (.var a2) (.imm 0)) fun a3 =>
  .let_ (.bin .l .mul (.var a3) (.imm 1)) fun a4 =>
  .let_ (.bin .l .mul (.imm 1) (.var a4)) fun a5 =>
  .let_ (.bin .l .or (.var a5) (.imm 0)) fun a6 =>
  .let_ (.bin .l .xor (.var a6) (.imm 0)) fun a7 =>
  .let_ (.bin .l .shl (.var a7) (.imm 0)) fun a8 =>
  .let_ (.bin .l .and (.var a8) (.imm (BitVec.allOnes 64))) fun a9 =>
  .let_ (.ext .l .l true (.var a9)) fun a10 =>
  .let_ (.bin .l .mul (.var b) (.imm 0)) fun m0 =>
  .let_ (.bin .w .and (.var b) (.imm 0)) fun n0 =>
  .let_ (.cmp .l .eq (.var a10) (.var a)) fun ce =>
  .let_ (.cmp .l .ne (.var b) (.var b)) fun cn =>
  .let_ (.cmp .l .ult (.var a) (.var a)) fun cu =>
  .let_ (.cmp .w .slt (.var b) (.var b)) fun cs =>
  .let_ (.bin .l .or (.var m0) (.var n0)) fun z2 =>
  .let_ (.bin .l .or (.var cn) (.var cu)) fun z3 =>
  .let_ (.bin .l .or (.var z2) (.var z3)) fun z4 =>
  .let_ (.bin .l .or (.var z4) (.var cs)) fun z5 =>
  .jnz (.var ce)
    (.let_ (.bin .l .mul (.var a10) (.imm 8)) fun off =>
     .let_ (.bin .w .mul (.imm 4) (.var b)) fun off2 =>
     .let_ (.ext .l .w false (.var b)) fun bw =>
     .ret [.var off, .var off2, .var bw, .var z5])
    (.ret [.imm 99])

/-- All 20 identity/annihilator/self-comparison `let_`s and the branch disappear; `mul _ 8` becomes
`shl _ 3`, `mul.w 4 _` becomes `shl.w _ 2`, and `extuw` (`ext .l .w false`) becomes `copy .w`. -/
theorem algProg_fold_out : Func.fold algProg = fun _ _ =>
    .param fun a => .param fun b =>
    .let_ (.bin .l .shl (.var a) (.imm 3)) fun off =>
    .let_ (.bin .w .shl (.var b) (.imm 2)) fun off2 =>
    .let_ (.copy .w (.var b)) fun bw =>
    .ret [.var off, .var off2, .var bw, .imm 0] := rfl

theorem algProg_wf : algProg.Wf := by wf_tac

theorem algProg_fold_wf : (Func.fold algProg).Wf := Func.fold_wf algProg_wf

end LeanQbe.FoldTest
