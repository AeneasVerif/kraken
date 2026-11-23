module

public import LeanQbe.T.FoldLemmas
public import LeanQbe.T.WPLemmas
public import LeanQbe.T.FlatLemmas
public import LeanQbe.T.Logic.Rules

/-!
# Tests of `LeanQbe.T.Fold`

Covers constant folding and algebraic simplification in `LeanQbe.T`:
- Multi-result constant folding and algebraic identities (`addc`, `subb`, `umulw`, `smulw`),
- Strength reduction (`mul → shl`, `udiv → lshr`, `urem → and`, div by 1, safe `udiv0`/`sdiv0`),
- Non-foldable UB preservation (`udiv x 0` is kept),
- Vector (`v4i32`, `v2i64`) folding, `ternlog`, `blend`, `shufd`,
- Floating-point deterministic folding (`fneg`, `fabs`, finite `fadd`) and sound refinement of
  nondeterministic quiet NaN results via `canonNaN`,
- `group` block folding and static `jnz` elimination,
- Kernel reduction (`t_kernel_rfl`), well-formedness (`t_wf_reify`, `Func.fold_wf`), and WP
  refinement (`Func.fold_spec`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.FoldTest

open LeanQbe.T

/-! ## 1. Baseline `prog`: constant + copy + comparison + static `jnz` -/

/-- `x = add 1 2; y = copy x; z = add a y; c = cult y 4; jnz c, ret z, ret 0` -/
def prog : Func [i64] [i64] := fun _ _ p =>
  .let_ (op2 (.add i64) (.imm 1) (.imm 2)) fun x =>
  .let_ (op1 (.copy i64) (.var x.1)) fun y =>
  .let_ (op2 (.add i64) (.var p.1) (.var y.1)) fun z =>
  .let_ (op2 (.ult i64) (.var y.1) (.imm 4)) fun c =>
  .jnz (.var c.1) (.ret (.var z.1, ())) (.ret (.imm 0, ()))

/-- Folded: `z = add a 3; ret z`. -/
theorem prog_fold_out : Func.fold prog = fun _ _ p =>
    .let_ (op2 (.add i64) (.var p.1) (.imm 3)) fun z =>
    .ret (.var z.1, ()) := by
  t_kernel_rfl

theorem prog_wf : prog.Wf := by t_wf_reify

theorem fold_prog_wf : (Func.fold prog).Wf := Func.fold_wf prog_wf

theorem prog_fold_spec (Γ : Env) (a : BitVec 64) (m : Mem 64) :
    Func.spec Γ (Func.fold prog) (a, ()) m
      (fun (r, ()) m' => r = a + 3#64 ∧ m' = m)
      (fun _ _ _ _ => False) := by
  apply Func.fold_spec prog_wf
  dsimp only [Func.spec, Func.wp, prog]
  wp_unfold
  exact ⟨fun _ => rfl, fun hc => by cases hc⟩

/-! ## 2. `algProg`: algebraic identities, annihilators, self-rules, strength reduction -/

def algProg : Func [i64, i64] [i64, i64, i32, i64] := fun _ _ p =>
  let a := p.1
  let b := p.2.1
  .let_ (op2 (.sub i64) (.var b) (.var b)) fun z0 =>
  .let_ (op2 (.xor i64) (.var a) (.var a)) fun z1 =>
  .let_ (op2 (.add i64) (.var a) (.var z0.1)) fun a1 =>
  .let_ (op2 (.add i64) (.var z1.1) (.var a1.1)) fun a2 =>
  .let_ (op2 (.sub i64) (.var a2.1) (.imm 0)) fun a3 =>
  .let_ (op2 (.mul i64) (.var a3.1) (.imm 1)) fun a4 =>
  .let_ (op2 (.mul i64) (.imm 1) (.var a4.1)) fun a5 =>
  .let_ (op2 (.or i64) (.var a5.1) (.imm 0)) fun a6 =>
  .let_ (op2 (.xor i64) (.var a6.1) (.imm 0)) fun a7 =>
  .let_ (op2 (.shl i64) (.var a7.1) (.imm 0)) fun a8 =>
  .let_ (op2 (.and i64) (.var a8.1) (.imm (BitVec.allOnes 64))) fun a9 =>
  .let_ (op1 (.sext 64 64) (.var a9.1)) fun a10 =>
  .let_ (op2 (.mul i64) (.var b) (.imm 0)) fun m0 =>
  .let_ (op2 (.and i64) (.var b) (.imm 0)) fun n0 =>
  .let_ (op2 (.eq i64) (.var a10.1) (.var a)) fun ce =>
  .let_ (op2 (.ne i64) (.var b) (.var b)) fun cn =>
  .let_ (op2 (.ult i64) (.var a) (.var a)) fun cu =>
  .let_ (op2 (.slt i64) (.var b) (.var b)) fun cs =>
  .let_ (op1 (.ofBool 64) (.var cn.1)) fun bcn =>
  .let_ (op1 (.ofBool 64) (.var cu.1)) fun bcu =>
  .let_ (op1 (.ofBool 64) (.var cs.1)) fun bcs =>
  .let_ (op2 (.or i64) (.var m0.1) (.var n0.1)) fun z2 =>
  .let_ (op2 (.or i64) (.var bcn.1) (.var bcu.1)) fun z3 =>
  .let_ (op2 (.or i64) (.var z2.1) (.var z3.1)) fun z4 =>
  .let_ (op2 (.or i64) (.var z4.1) (.var bcs.1)) fun z5 =>
  .jnz (.var ce.1)
    (.let_ (op2 (.mul i64) (.var a10.1) (.imm 8)) fun off =>
     .let_ (op2 (.mul i64) (.imm 4) (.var b)) fun off2 =>
     .let_ (op1 (.trunc 64 32) (.var b)) fun bw =>
     .ret (.var off.1, .var off2.1, .var bw.1, .var z5.1, ()))
    (.ret (.imm 99, .imm 99, .imm 99, .imm 99, ()))

/-- All identity/annihilator/self-comparison `let_`s and the dead `jnz` arm collapse;
`mul a 8` becomes `shl a 3`, `mul 4 b` becomes `shl b 2`, and `trunc 64 32` is preserved. -/
theorem algProg_fold_out : Func.fold algProg = fun _ _ p =>
    let a := p.1
    let b := p.2.1
    .let_ (op2 (.shl i64) (.var a) (.imm 3)) fun off =>
    .let_ (op2 (.shl i64) (.var b) (.imm 2)) fun off2 =>
    .let_ (op1 (.trunc 64 32) (.var b)) fun bw =>
    .ret (.var off.1, .var off2.1, .var bw.1, .imm 0, ()) := by
  t_kernel_rfl

theorem algProg_wf : algProg.Wf := by t_wf_reify

theorem fold_algProg_wf : (Func.fold algProg).Wf := Func.fold_wf algProg_wf

theorem algProg_fold_spec (Γ : Env) (a b : BitVec 64) (m : Mem 64) :
    Func.spec Γ (Func.fold algProg) (a, b, ()) m
      (fun (r0, r1, r2, r3, ()) m' =>
        r0 = a <<< 3 ∧ r1 = b <<< 2 ∧ r2 = b.setWidth 32 ∧ r3 = 0#64 ∧ m' = m)
      (fun _ _ _ _ => False) := by
  apply Func.fold_spec algProg_wf
  dsimp only [Func.spec, Func.wp, algProg]
  have hall : (18446744073709551615#64 : BitVec 64) = BitVec.allOnes 64 := rfl
  wp_unfold
  simp [BitVec.sub_self, BitVec.xor_self, BitVec.add_zero, BitVec.zero_add,
    BitVec.sub_zero, BitVec.mul_one, BitVec.one_mul, BitVec.or_zero, BitVec.zero_or,
    BitVec.xor_zero, BitVec.mul_zero, BitVec.and_zero, BitVec.slt, ← hall]
  rw [hall, BitVec.and_allOnes]
  refine ⟨fun _ => ⟨?_, ?_, ?_⟩, rfl⟩
  · apply BitVec.eq_of_toNat_eq; simp [Nat.mul_comm]
  · apply BitVec.eq_of_toNat_eq; simp [Nat.shiftLeft_eq, Nat.mul_comm]
  · simp [BitVec.ult]

/-! ## 3. Division/remainder strength reduction and UB preservation -/

def divRemProg : Func [i64, i64] [i64, i64, i64, i64, i64, i64, i64] := fun _ _ p =>
  let x := p.1
  let y := p.2.1
  .let_ (op2 (.udiv 64) (.var x) (.imm 8)) fun q1 =>
  .let_ (op2 (.urem 64) (.var x) (.imm 8)) fun r1 =>
  .let_ (op2 (.udiv 64) (.var x) (.imm 1)) fun q2 =>
  .let_ (op2 (.sdiv 64) (.var y) (.imm 1)) fun q3 =>
  .let_ (op2 (.udiv0 64) (.var y) (.imm 0)) fun q4 =>
  .let_ (op2 (.sdiv0 64) (.var y) (.imm 1)) fun q5 =>
  .let_ (op2 (.udiv 64) (.var y) (.imm 0)) fun keepUB =>
  .ret (.var q1.1, .var r1.1, .var q2.1, .var q3.1, .var q4.1, .var q5.1, .var keepUB.1, ())

/-- Power-of-two `udiv`/`urem` reduce to `lshr`/`and`; division by 1 and safe `udiv0`/`sdiv0`
fold away; UB-prone `udiv y 0` is conservatively preserved. -/
theorem divRemProg_fold_out : Func.fold divRemProg = fun _ _ p =>
    let x := p.1
    let y := p.2.1
    .let_ (op2 (.lshr i64) (.var x) (.imm 3)) fun q1 =>
    .let_ (op2 (.and i64) (.var x) (.imm 7)) fun r1 =>
    .let_ (op2 (.udiv 64) (.var y) (.imm 0)) fun keepUB =>
    .ret (.var q1.1, .var r1.1, .var x, .var y, .imm 0, .var y, .var keepUB.1, ()) := by
  t_kernel_rfl

theorem divRemProg_wf : divRemProg.Wf := by t_wf_reify

theorem fold_divRemProg_wf : (Func.fold divRemProg).Wf := Func.fold_wf divRemProg_wf

/-! ## 4. Multi-result operations (`addc`, `subb`, `umulw`, `smulw`) -/

def multiResProg : Func [i64] [i64, .bool, i64, .bool, i64, i64] := fun _ _ p =>
  let a := p.1
  .let_ (op3 (.addc 64) (.imm (BitVec.allOnes 64)) (.imm 1) (.imm false)) fun r1 =>
  .let_ (op3 (.addc 64) (.var a) (.imm 0) (.imm false)) fun r2 =>
  .let_ (op3 (.subb 64) (.var a) (.var a) (.imm false)) fun r3 =>
  .let_ (op2 (.umulw 64) (.imm 0x100000000) (.imm 0x100000000)) fun r4 =>
  .let_ (op2 (.umulw 64) (.var a) (.imm 0)) fun r5 =>
  .ret (.var r2.1, .var r1.2.1, .var r3.1, .var r3.2.1, .var r4.2.1, .var r5.2.1, ())

theorem multiResProg_fold_out : Func.fold multiResProg = fun _ _ p =>
    .ret (.var p.1, .imm true, .imm 0, .imm false, .imm 1, .imm 0, ()) := by
  t_kernel_rfl

theorem multiResProg_wf : multiResProg.Wf := by t_wf_reify

theorem multiResProg_fold_spec (Γ : Env) (a : BitVec 64) (m : Mem 64) :
    Func.spec Γ (Func.fold multiResProg) (a, ()) m
      (fun (r0, r1, r2, r3, r4, r5, ()) m' =>
        r0 = a ∧ r1 = true ∧ r2 = 0#64 ∧ r3 = false ∧ r4 = 1#64 ∧ r5 = 0#64 ∧ m' = m)
      (fun _ _ _ _ => False) := by
  apply Func.fold_spec multiResProg_wf
  dsimp only [Func.spec, Func.wp, multiResProg]
  wp_unfold_all
  simp [BitVec.sub_self]

/-! ## 5. Vector (`v4i32`) & Float (`fneg`, finite `fadd`, canonical NaN `fadd`) -/

def qnan32 : BitVec 32 := 0x7fc00001#32

def vecFloatProg : Func [v4i32] [v4i32, v4i32, f32, f32] := fun _ _ p =>
  let v := p.1
  .let_ (op2 (.add v4i32) (.imm ((1#32, 2#32), (3#32, 4#32)))
                           (.imm ((10#32, 20#32), (30#32, 40#32)))) fun vc =>
  .let_ (op3 (.ternlog v4i32 0xff#8) (.var v) (.var v) (.var vc.1)) fun _vones =>
  .let_ (op2 (.xor v4i32) (.var v) (.imm ((0#32, 0#32), (0#32, 0#32)))) fun vid =>
  .let_ (op1 (.fneg f32) (.imm 0x3f800000#32)) fun fn =>
  .let_ (op2 (.fadd f32) (.imm qnan32) (.imm 0x3f800000#32)) fun fnan =>
  .ret (.var vc.1, .var vid.1, .var fn.1, .var fnan.1, ())

theorem vecFloatProg_fold_out : Func.fold vecFloatProg = fun _ _ p =>
    .ret (.imm ((11#32, 22#32), (33#32, 44#32)), .var p.1,
      .imm 0xbf800000#32, .imm (canonNaN .s), ()) := by
  t_kernel_rfl

theorem vecFloatProg_wf : vecFloatProg.Wf := by t_wf_reify

theorem fold_vecFloatProg_wf : (Func.fold vecFloatProg).Wf := Func.fold_wf vecFloatProg_wf

theorem vecFloatProg_fold_spec (Γ : Env) (v : Val v4i32) (m : Mem 64) :
    Func.spec Γ (Func.fold vecFloatProg) (v, ()) m
      (fun (r0, r1, r2, r3, ()) m' =>
        r0 = ((11#32, 22#32), (33#32, 44#32)) ∧ r1 = v ∧
        r2 = 0xbf800000#32 ∧ isFloatNaN .s r3 = true ∧ m' = m)
      (fun _ _ _ _ => False) := by
  apply Func.fold_spec vecFloatProg_wf
  dsimp only [Func.spec, Func.wp, vecFloatProg]
  wp_unfold_all
  simp only [liftFloatRel2, floatResultWp]
  have hnan : (Float.Model.UnpackedFloat.add Fmt.s.format (unpackFloat .s qnan32)
      (unpackFloat .s 0x3f800000#32)).isNaN = true := by
    decide
  simp only [hnan, ↓reduceIte]
  intro r hr
  simp [hr]
  decide

/-! ## 6. `group` block folding -/

def groupProg : Func [i64] [i64] := fun _ _ p =>
  .let_ (op2 (.add i64) (.imm 2) (.imm 3)) fun c =>
  .group (sig := [[i64]])
    (fun (_lp, ()) =>
      .cons (fun x =>
        .let_ (op2 (.add i64) (.var x.1) (.imm 0)) fun x' =>
        .let_ (op2 (.mul i64) (.var c.1) (.imm 2)) fun k =>
        .let_ (op2 (.add i64) (.var x'.1) (.var k.1)) fun y =>
        .ret (.var y.1, ()))
      .nil)
    (fun (lp, ()) => .jump lp (.var p.1, ()))

theorem groupProg_fold_out : Func.fold groupProg = fun _ _ p =>
    .group (sig := [[i64]])
      (fun (_lp, ()) =>
        .cons (fun x =>
          .let_ (op2 (.add i64) (.var x.1) (.imm 10)) fun y =>
          .ret (.var y.1, ()))
        .nil)
      (fun (lp, ()) => .jump lp (.var p.1, ())) := by
  t_kernel_rfl

theorem groupProg_wf : groupProg.Wf := by t_wf_reify

theorem fold_groupProg_wf : (Func.fold groupProg).Wf := Func.fold_wf groupProg_wf

/-! ## 7. Vector strength reduction, `cmp`/`blend` self-rules, `smulw`, `bitcast`, `fptoui` -/

def vecBitcastFpProg : Func [v4i32, v4i32] [v4i32, v4i32, Ty.mask v4i32, i64, i64, i32, i32] :=
  fun _ _ p =>
  let x := p.1
  let y := p.2.1
  .let_ (op2 (.mul v4i32) (.var x) (.imm ((1#32, 2#32), (4#32, 8#32)))) fun vsh =>
  .let_ (op2 (.eq v4i32) (.var x) (.var x)) fun meq =>
  .let_ (op3 (.blend v4i32) (.var meq.1) (.var x) (.var y)) fun bself =>
  .let_ (op2 (.slt v4i32) (.var y) (.var y)) fun mlt =>
  .let_ (op1 (.bitcast v4i32 v4i32 rfl) (.var bself.1)) fun bcId =>
  .let_ (op1 (.bitcast (i32.pair i32) i64 rfl) (.imm (1#32, 2#32))) fun bcConst =>
  .let_ (op2 (.smulw 64) (.imm (-5#64)) (.imm 3#64)) fun sm =>
  .let_ (op1 (.fptoui .s 32) (.imm 0xbf000000#32)) fun fpNegHalf =>
  .let_ (op1 (.fptoui .s 32) (.imm qnan32)) fun fpNaN =>
  .ret (.var vsh.1, .var bcId.1, .var mlt.1, .var bcConst.1, .var sm.2.1,
    .var fpNegHalf.1, .var fpNaN.1, ())

theorem vecBitcastFpProg_fold_out : Func.fold vecBitcastFpProg = fun _ _ p =>
    let x := p.1
    .let_ (op2 (.shl v4i32) (.var x) (.imm ((0#32, 1#32), (2#32, 3#32)))) fun vsh =>
    .let_ (op1 (.fptoui .s 32) (.imm qnan32)) fun fpNaN =>
    .ret (.var vsh.1, .var x, .imm ((false, false), (false, false)),
      .imm 0x0000000200000001#64, .imm (-1#64), .imm 0#32, .var fpNaN.1, ()) := by
  t_kernel_rfl

theorem vecBitcastFpProg_wf : vecBitcastFpProg.Wf := by t_wf_reify

theorem fold_vecBitcastFpProg_wf : (Func.fold vecBitcastFpProg).Wf :=
  Func.fold_wf vecBitcastFpProg_wf

/-! ## 6. Involutions, boolean `select`, shift-zero LHS, and extension chains -/

/-- `select c true false -> c`, `select c false true -> not c`,
`not (select c false true) -> c`, `not (not x) -> x`, `bswap (bswap y) -> y`,
`rbit (rbit y) -> y`. -/
def invSelectProg : Func [.bool, i64, i32] [.bool, i32, i64, i32, .bool] := fun _ _ p =>
  let c := p.1
  let x := p.2.1
  let y := p.2.2.1
  .let_ (op3 (.select .bool) (.var c) (.imm true) (.imm false)) fun s0 =>
  .let_ (op3 (.select .bool) (.var c) (.imm false) (.imm true)) fun s1 =>
  .let_ (op1 (.not .bool) (.var s1.1)) fun ns1 =>
  .let_ (op1 (.not i64) (.var x)) fun nx0 =>
  .let_ (op1 (.not i64) (.var nx0.1)) fun nx1 =>
  .let_ (op1 (.bswap i32) (.var y)) fun bs0 =>
  .let_ (op1 (.bswap i32) (.var bs0.1)) fun bs1 =>
  .let_ (op1 (.rbit 32) (.var bs1.1)) fun rb0 =>
  .let_ (op1 (.rbit 32) (.var rb0.1)) fun rb1 =>
  .ret (.var s0.1, .var rb1.1, .var nx1.1, .var y, .var ns1.1, ())

theorem invSelectProg_fold_out : Func.fold invSelectProg = fun _ _ p =>
    let c := p.1
    let x := p.2.1
    let y := p.2.2.1
    .let_ (op1 (.not .bool) (.var c)) fun _ =>
    .let_ (op1 (.not i64) (.var x)) fun _ =>
    .let_ (op1 (.bswap i32) (.var y)) fun _ =>
    .let_ (op1 (.rbit 32) (.var y)) fun _ =>
    .ret (.var c, .var y, .var x, .var y, .var c, ()) := by
  t_kernel_rfl

theorem invSelectProg_wf : invSelectProg.Wf := by t_wf_reify

theorem invSelectProg_fold_wf : (Func.fold invSelectProg).Wf :=
  Func.fold_wf invSelectProg_wf

theorem invSelectProg_fold_spec (Γ : Env) (c : Bool) (x : BitVec 64) (y : BitVec 32)
    (m : Mem 64) :
    Func.spec Γ (Func.fold invSelectProg) (c, x, y, ()) m
      (fun (r0, r1, r2, r3, r4, ()) m' =>
        r0 = c ∧ r1 = y ∧ r2 = x ∧ r3 = y ∧ r4 = c ∧ m' = m)
      (fun _ _ _ _ => False) := by
  apply Func.fold_spec invSelectProg_wf
  dsimp only [Func.spec, Func.wp, invSelectProg]
  wp_unfold
  cases c <;> simp [bswapBits_bswapBits]

/-- Non-byte-multiple `bswap` (UB) must be preserved, not cancelled. -/
def bswapBadProg : Func [.bits 12] [.bits 12] := fun _ _ p =>
  .let_ (op1 (.bswap (.bits 12)) (.var p.1)) fun a =>
  .let_ (op1 (.bswap (.bits 12)) (.var a.1)) fun b =>
  .ret (.var b.1, ())

theorem bswapBadProg_fold_out : Func.fold bswapBadProg = bswapBadProg := by
  t_kernel_rfl

theorem bswapBadProg_wf : bswapBadProg.Wf := by t_wf_reify

theorem bswapBadProg_fold_wf : (Func.fold bswapBadProg).Wf :=
  Func.fold_wf bswapBadProg_wf

/-- Left-hand zero shifts/rotates (`0 op y -> 0`) and `zext`/`sext`/`trunc` chains. -/
def shiftExtProg : Func [i64, .bool, i16] [i64, i64, i64, .bool, i64, i16, i32, i64, i8] :=
  fun _ _ p =>
  let y := p.1
  let b := p.2.1
  let x := p.2.2.1
  .let_ (op2 (.shl i64) (.imm 0) (.var y)) fun s0 =>
  .let_ (op2 (.lshr i64) (.imm 0) (.var y)) fun s1 =>
  .let_ (op2 (.ashr i64) (.imm 0) (.var y)) fun s2 =>
  .let_ (op2 (.rotl .bool) (.imm false) (.var b)) fun s3 =>
  .let_ (op2 (.rotr i64) (.imm 0) (.var y)) fun s4 =>
  .let_ (op1 (.zext 16 64) (.var x)) fun zx =>
  .let_ (op1 (.trunc 64 16) (.var zx.1)) fun rt =>
  .let_ (op1 (.sext 16 64) (.var x)) fun sx0 =>
  .let_ (op1 (.trunc 64 32) (.var sx0.1)) fun sx1 =>
  .let_ (op1 (.zext 16 32) (.var x)) fun zx0 =>
  .let_ (op1 (.zext 32 64) (.var zx0.1)) fun zx1 =>
  .let_ (op1 (.sext 16 32) (.var x)) fun sx2 =>
  .let_ (op1 (.trunc 32 8) (.var sx2.1)) fun tr =>
  .ret (.var s0.1, .var s1.1, .var s2.1, .var s3.1, .var s4.1,
    .var rt.1, .var sx1.1, .var zx1.1, .var tr.1, ())

theorem shiftExtProg_fold_out : Func.fold shiftExtProg = fun _ _ p =>
    let x := p.2.2.1
    .let_ (op1 (.zext 16 64) (.var x)) fun _ =>
    .let_ (op1 (.sext 16 64) (.var x)) fun _ =>
    .let_ (op1 (.sext 16 32) (.var x)) fun sx1 =>
    .let_ (op1 (.zext 16 32) (.var x)) fun _ =>
    .let_ (op1 (.zext 16 64) (.var x)) fun zx1 =>
    .let_ (op1 (.sext 16 32) (.var x)) fun _ =>
    .let_ (op1 (.trunc 16 8) (.var x)) fun tr =>
    .ret (.imm 0, .imm 0, .imm 0, .imm false, .imm 0,
      .var x, .var sx1.1, .var zx1.1, .var tr.1, ()) := by
  t_kernel_rfl

theorem shiftExtProg_wf : shiftExtProg.Wf := by t_wf_reify

theorem shiftExtProg_fold_wf : (Func.fold shiftExtProg).Wf :=
  Func.fold_wf shiftExtProg_wf

theorem shiftExtProg_fold_spec (Γ : Env) (y : BitVec 64) (b : Bool) (x : BitVec 16)
    (m : Mem 64) :
    Func.spec Γ (Func.fold shiftExtProg) (y, b, x, ()) m
      (fun (r0, r1, r2, r3, r4, r5, r6, r7, r8, ()) m' =>
        r0 = 0#64 ∧ r1 = 0#64 ∧ r2 = 0#64 ∧ r3 = false ∧ r4 = 0#64 ∧
        r5 = x ∧ r6 = x.signExtend 32 ∧ r7 = x.setWidth 64 ∧ r8 = x.setWidth 8 ∧ m' = m)
      (fun _ _ _ _ => False) := by
  apply Func.fold_spec shiftExtProg_wf
  dsimp only [Func.spec, Func.wp, shiftExtProg]
  wp_unfold
  refine ⟨by simp, by simp, by simp, ?_, ?_, ?_, ?_, ?_⟩
  · ext i _; simp [BitVec.rotateRight, BitVec.rotateRightAux]
  · rw [setWidth_setWidth_le (by omega) x, BitVec.setWidth_eq]
  · exact setWidth_signExtend_of_mid (by omega) (by omega) x
  · exact setWidth_setWidth_trans (by omega) (by omega) x
  · exact setWidth_signExtend_of_narrow (by omega) (by omega) x

/-- `select (.bits n) c 1 0 -> ofBool n c`, `select .bool c true b -> or c b`,
`select .bool c a false -> and c a`. -/
def selectFoldProg : Func [.bool, .bool, .bool] [i64, i32, .bool, .bool] := fun _ _ p =>
  let c := p.1
  let a := p.2.1
  let b := p.2.2.1
  .let_ (op3 (.select i64) (.var c) (.imm 1) (.imm 0)) fun b64 =>
  .let_ (op3 (.select i32) (.var c) (.imm 1) (.imm 0)) fun b32 =>
  .let_ (op3 (.select .bool) (.var c) (.imm true) (.var b)) fun sor =>
  .let_ (op3 (.select .bool) (.var c) (.var a) (.imm false)) fun sand =>
  .ret (.var b64.1, .var b32.1, .var sor.1, .var sand.1, ())

theorem selectFoldProg_fold_out : Func.fold selectFoldProg = fun _ _ p =>
    let c := p.1
    let a := p.2.1
    let b := p.2.2.1
    .let_ (op1 (.ofBool 64) (.var c)) fun b64 =>
    .let_ (op1 (.ofBool 32) (.var c)) fun b32 =>
    .let_ (op2 (.or .bool) (.var c) (.var b)) fun sor =>
    .let_ (op2 (.and .bool) (.var c) (.var a)) fun sand =>
    .ret (.var b64.1, .var b32.1, .var sor.1, .var sand.1, ()) := by
  t_kernel_rfl

theorem selectFoldProg_wf : selectFoldProg.Wf := by t_wf_reify

theorem selectFoldProg_fold_wf : (Func.fold selectFoldProg).Wf := Func.fold_wf selectFoldProg_wf

theorem selectFoldProg_fold_spec (Γ : Env) (c a b : Bool) (m : Mem 64) :
    Func.spec Γ (Func.fold selectFoldProg) (c, a, b, ()) m
      (fun (r0, r1, r2, r3, ()) m' =>
        r0 = (if c then 1#64 else 0#64) ∧ r1 = (if c then 1#32 else 0#32) ∧
        r2 = (c || b) ∧ r3 = (c && a) ∧ m' = m)
      (fun _ _ _ _ => False) := by
  apply Func.fold_spec selectFoldProg_wf
  dsimp only [Func.spec, Func.wp, selectFoldProg]
  wp_unfold
  cases c <;> simp

#print axioms LeanQbe.T.FoldTest.invSelectProg_fold_spec
#print axioms LeanQbe.T.FoldTest.bswapBadProg_fold_wf
#print axioms LeanQbe.T.FoldTest.shiftExtProg_fold_spec
#print axioms LeanQbe.T.FoldTest.selectFoldProg_fold_spec

end LeanQbe.T.FoldTest
