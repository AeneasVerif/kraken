module

import LeanQbe.T.DivConstLemmas
import LeanQbe.T.WPLemmas
import LeanQbe.T.FlatLemmas
import LeanQbe.T.Logic.Rules

/-!
# Tests of `LeanQbe.T.DivConst`

Verifies constant division and remainder lowering (`udiv`, `urem`, `sdiv`, `srem` at `32`-bit and
`64`-bit):
- Certificate checks (`pow2ShiftCert`, `uNoAddCert`, `uAddShiftCert`, `sPow2Cert`, `sDivCert`) on
  representative divisors `/ 3`, `/ 7`, `/ 8`, `/ 10`, `/ 65521` (Adler-32 prime), `/ (-3)`,
  `/ (-10)`;
- Golden lowered AST checks via `t_kernel_rfl` (including both no-add and add-shift unsigned
  paths, signed positive/negative magic with `+x`, `-x`, no-fixup, and `s = 0`/`s > 0` shifts);
- Complete division/remainder elimination (`noDivRem`) on certified 32-bit and 64-bit programs;
- Conservative UB & guard preservation: `d = 0` on all 4 ops, signed `d = -1` (`allOnes n`,
  where `INT_MIN / -1` is UB), variable divisors, and non-`32/64` bitwidths remain untouched;
- Universal semantic preservation (`Func.divConst_spec`) and boundary-input execution on
  `0, 1, 2, -1, INT_MIN, INT_MAX` at both `32`-bit and `64`-bit;
- `group` loop + memory effect preservation, `Func.checkTFlat = true`, `Func.divConst_wf`, and
  axiom cleanliness (`#print axioms`).
-/

set_option autoImplicit false

section

namespace LeanQbe.T.DivConstTest

open LeanQbe.T

/-! ## 1. Pure expression helpers for structural & concrete boundary checks -/

/-- Returns `true` iff `code` is any integer division or remainder opcode. -/
def isDivRemCode : {sig ts : List Ty} → OpCode sig ts → Bool
  | _, _, .udiv _ | _, _, .urem _ | _, _, .sdiv _ | _, _, .srem _ => true
  | _, _, _ => false

mutual
/-- Returns `true` iff `e` contains no `.udiv`, `.urem`, `.sdiv`, or `.srem` instructions. -/
def noDivRem {rs : List Ty} : TFlat rs → Bool
  | .let_ op k => !isDivRemCode op.code && noDivRem k
  | .load _ _ k => noDivRem k
  | .store _ _ k => noDivRem k
  | .call _ _ _ k => noDivRem k
  | .jnz _ t e => noDivRem t && noDivRem e
  | .jump _ _ | .ret _ | .exit _ _ | .hlt => true
  | .group bodies k => noDivRemB bodies && noDivRem k

def noDivRemB {rs : List Ty} : {sig : List (List Ty)} → TBlocks rs sig → Bool
  | _, .nil => true
  | _, .cons b bs => noDivRem b && noDivRemB bs
end

def funcTFlat {as rs : List Ty} (f : Func as rs) : TFlat rs :=
  toTFlat (f K KL (Tup.levels as 0)) as.length 0

/-- Pure small-step evaluator helper matching indexed `OpCode` and `Tup (Arg Val)`. -/
def evalOpCode : {sig ts : List Ty} → OpCode sig ts → Tup (Arg Val) sig → Option (Tup Val ts)
  | _, _, .add (.bits _), (a, b, ()) => some (a.val + b.val, ())
  | _, _, .sub (.bits _), (a, b, ()) => some (a.val - b.val, ())
  | _, _, .mul (.bits _), (a, b, ()) => some (a.val * b.val, ())
  | _, _, .and (.bits _), (a, b, ()) => some (a.val &&& b.val, ())
  | _, _, .lshr (.bits n), (a, b, ()) => some (a.val >>> (b.val.toNat % n), ())
  | _, _, .ashr (.bits n), (a, b, ()) => some (a.val.sshiftRight (b.val.toNat % n), ())
  | _, _, .umulw n, (a, b, ()) =>
    some (a.val * b.val, BitVec.ofNat n (a.val.toNat * b.val.toNat / 2 ^ n), ())
  | _, _, .smulw n, (a, b, ()) =>
    some (a.val * b.val, (BitVec.ofInt (n + n) (a.val.toInt * b.val.toInt)).extractLsb' n n, ())
  | _, _, .udiv n, (a, b, ()) => if b.val == 0#n then none else some (a.val / b.val, ())
  | _, _, .urem n, (a, b, ()) => if b.val == 0#n then none else some (a.val % b.val, ())
  | _, _, .sdiv _, (a, b, ()) =>
    if sdivDefined a.val b.val then some (a.val.sdiv b.val, ()) else none
  | _, _, .srem _, (a, b, ()) =>
    if sdivDefined a.val b.val then some (a.val.srem b.val, ()) else none
  | _, _, _, _ => none

def evalPure {rs : List Ty} : Expr Val (fun _ => Empty) rs → Option (Tup Val rs)
  | .let_ op k => match evalOpCode op.code op.args with | some xs => evalPure (k xs) | none => none
  | .ret vs => some (vals vs)
  | _ => none

/-! ## 2. Boolean certificate smoke tests at `32`-bit and `64`-bit -/

theorem certs_32_ok :
    pow2ShiftCert 32 8#32 3 = true ∧
    uNoAddCert 32 3#32 2863311531 1 = true ∧
    uAddShiftCert 32 7#32 4908534053 3 = true ∧
    uNoAddCert 32 10#32 3435973837 3 = true ∧
    uNoAddCert 32 65521#32 2147975281 15 = true ∧
    sPow2Cert 32 4#32 2 = true ∧
    sDivCert 32 3#32 1431655766 0 = true ∧
    sDivCert 32 7#32 2454267027 2 = true ∧
    sDivCert 32 (-3#32) 2863311531 1 = true ∧
    sDivCert 32 (-10#32) 1717986919 2 = true ∧
    sDivCert 32 65521#32 2147975281 15 = true := by
  decide

theorem certs_64_ok :
    pow2ShiftCert 64 8#64 3 = true ∧
    uNoAddCert 64 3#64 12297829382473034411 1 = true ∧
    uAddShiftCert 64 7#64 21081993227096630419 3 = true ∧
    uNoAddCert 64 10#64 14757395258967641293 3 = true ∧
    uAddShiftCert 64 65521#64 18450967164949087693 16 = true ∧
    sPow2Cert 64 4#64 2 = true ∧
    sDivCert 64 3#64 6148914691236517206 0 = true ∧
    sDivCert 64 7#64 5270498306774157605 1 = true ∧
    sDivCert 64 (-3#64) 12297829382473034411 1 = true ∧
    sDivCert 64 (-10#64) 7378697629483820647 2 = true ∧
    sDivCert 64 65521#64 9225483582474543847 15 = true := by
  decide

/-! ## 3. Golden lowered AST tests (`t_kernel_rfl`) -/

def u32Div3 : Func [i32] [i32] := fun _ _ p =>
  .let_ (op2 (.udiv 32) (.var p.1) (.imm 3#32)) fun q => .ret (.var q.1, ())

theorem u32Div3_out : Func.divConst u32Div3 = fun _ _ p =>
    .let_ (op2 (.umulw 32) (.var p.1) (.imm 2863311531#32)) fun mul =>
    .let_ (op2 (.lshr i32) (.var mul.2.1) (.imm 1#32)) fun q =>
    .ret (.var q.1, ()) := by
  t_kernel_rfl

def u32Div7 : Func [i32] [i32] := fun _ _ p =>
  .let_ (op2 (.udiv 32) (.var p.1) (.imm 7#32)) fun q => .ret (.var q.1, ())

theorem u32Div7_out : Func.divConst u32Div7 = fun _ _ p =>
    let x := p.1
    .let_ (op2 (.umulw 32) (.var x) (.imm 613566757#32)) fun mul =>
    .let_ (op2 (.sub i32) (.var x) (.var mul.2.1)) fun t1 =>
    .let_ (op2 (.lshr i32) (.var t1.1) (.imm 1#32)) fun t2 =>
    .let_ (op2 (.add i32) (.var mul.2.1) (.var t2.1)) fun t3 =>
    .let_ (op2 (.lshr i32) (.var t3.1) (.imm 2#32)) fun q =>
    .ret (.var q.1, ()) := by
  t_kernel_rfl

def u32Rem10 : Func [i32] [i32] := fun _ _ p =>
  .let_ (op2 (.urem 32) (.var p.1) (.imm 10#32)) fun r => .ret (.var r.1, ())

theorem u32Rem10_out : Func.divConst u32Rem10 = fun _ _ p =>
    let x := p.1
    .let_ (op2 (.umulw 32) (.var x) (.imm 3435973837#32)) fun mul =>
    .let_ (op2 (.lshr i32) (.var mul.2.1) (.imm 3#32)) fun q =>
    .let_ (op2 (.mul i32) (.var q.1) (.imm 10#32)) fun prod =>
    .let_ (op2 (.sub i32) (.var x) (.var prod.1)) fun r =>
    .ret (.var r.1, ()) := by
  t_kernel_rfl

def s32DivNeg3 : Func [i32] [i32] := fun _ _ p =>
  .let_ (op2 (.sdiv 32) (.var p.1) (.imm (-3#32))) fun q => .ret (.var q.1, ())

theorem s32DivNeg3_out : Func.divConst s32DivNeg3 = fun _ _ p =>
    let x := p.1
    .let_ (op2 (.smulw 32) (.var x) (.imm (BitVec.ofInt 32 (-2863311531)))) fun mul =>
    .let_ (op2 (.sub i32) (.var mul.2.1) (.var x)) fun t =>
    .let_ (op2 (.ashr i32) (.var t.1) (.imm 1#32)) fun q0 =>
    .let_ (op2 (.lshr i32) (.var q0.1) (.imm 31#32)) fun sgn =>
    .let_ (op2 (.add i32) (.var q0.1) (.var sgn.1)) fun q =>
    .ret (.var q.1, ()) := by
  t_kernel_rfl

def s64Div3 : Func [i64] [i64] := fun _ _ p =>
  .let_ (op2 (.sdiv 64) (.var p.1) (.imm 3#64)) fun q => .ret (.var q.1, ())

theorem s64Div3_out : Func.divConst s64Div3 = fun _ _ p =>
    .let_ (op2 (.smulw 64) (.var p.1) (.imm (BitVec.ofInt 64 6148914691236517206))) fun mul =>
    .let_ (op2 (.lshr i64) (.var mul.2.1) (.imm 63#64)) fun sgn =>
    .let_ (op2 (.add i64) (.var mul.2.1) (.var sgn.1)) fun q =>
    .ret (.var q.1, ()) := by
  t_kernel_rfl

def s64RemNeg10 : Func [i64] [i64] := fun _ _ p =>
  .let_ (op2 (.srem 64) (.var p.1) (.imm (-10#64))) fun r => .ret (.var r.1, ())

theorem s64RemNeg10_out : Func.divConst s64RemNeg10 = fun _ _ p =>
    let x := p.1
    .let_ (op2 (.smulw 64) (.var x) (.imm (BitVec.ofInt 64 (-7378697629483820647)))) fun mul =>
    .let_ (op2 (.ashr i64) (.var mul.2.1) (.imm 2#64)) fun q0 =>
    .let_ (op2 (.lshr i64) (.var q0.1) (.imm 63#64)) fun sgn =>
    .let_ (op2 (.add i64) (.var q0.1) (.var sgn.1)) fun q =>
    .let_ (op2 (.mul i64) (.var q.1) (.imm (-10#64))) fun prod =>
    .let_ (op2 (.sub i64) (.var x) (.var prod.1)) fun r =>
    .ret (.var r.1, ()) := by
  t_kernel_rfl

/-! ## 4. Full `32`-bit suite (`/ 3`, `/ 7`, `/ 10`, `% 10`, `% 65521`, `/ (-3)`, `% (-10)`) -/

abbrev Out32 :=
  [i32, i32, i32, i32, i32, i32,
   i32, i32, i32, i32,
   i32, i32, i32, i32, i32, i32,
   i32, i32, i32, i32]

def prog32 : Func [i32] Out32 := fun _ _ p =>
  let x := p.1
  .let_ (op2 (.udiv 32) (.var x) (.imm 1#32)) fun u1 =>
  .let_ (op2 (.udiv 32) (.var x) (.imm 3#32)) fun u3 =>
  .let_ (op2 (.udiv 32) (.var x) (.imm 7#32)) fun u7 =>
  .let_ (op2 (.udiv 32) (.var x) (.imm 8#32)) fun u8 =>
  .let_ (op2 (.udiv 32) (.var x) (.imm 10#32)) fun u10 =>
  .let_ (op2 (.udiv 32) (.var x) (.imm 65521#32)) fun uMb8 =>
  .let_ (op2 (.urem 32) (.var x) (.imm 1#32)) fun ur1 =>
  .let_ (op2 (.urem 32) (.var x) (.imm 8#32)) fun ur8 =>
  .let_ (op2 (.urem 32) (.var x) (.imm 10#32)) fun ur10 =>
  .let_ (op2 (.urem 32) (.var x) (.imm 65521#32)) fun urMb8 =>
  .let_ (op2 (.sdiv 32) (.var x) (.imm 1#32)) fun s1 =>
  .let_ (op2 (.sdiv 32) (.var x) (.imm 2#32)) fun s2 =>
  .let_ (op2 (.sdiv 32) (.var x) (.imm 4#32)) fun s4 =>
  .let_ (op2 (.sdiv 32) (.var x) (.imm 3#32)) fun s3 =>
  .let_ (op2 (.sdiv 32) (.var x) (.imm 7#32)) fun s7 =>
  .let_ (op2 (.sdiv 32) (.var x) (.imm (-3#32))) fun sN3 =>
  .let_ (op2 (.srem 32) (.var x) (.imm 1#32)) fun sr1 =>
  .let_ (op2 (.srem 32) (.var x) (.imm 65521#32)) fun srMb8 =>
  .let_ (op2 (.srem 32) (.var x) (.imm (-3#32))) fun srN3 =>
  .let_ (op2 (.srem 32) (.var x) (.imm (-10#32))) fun srN10 =>
  .ret (.var u1.1, .var u3.1, .var u7.1, .var u8.1, .var u10.1, .var uMb8.1,
    .var ur1.1, .var ur8.1, .var ur10.1, .var urMb8.1,
    .var s1.1, .var s2.1, .var s4.1, .var s3.1, .var s7.1, .var sN3.1,
    .var sr1.1, .var srMb8.1, .var srN3.1, .var srN10.1, ())

theorem prog32_wf : prog32.Wf := by t_wf_reify

theorem opt32_wf : (Func.divConst prog32).Wf := Func.divConst_wf prog32_wf

theorem opt32_checkTFlat : (Func.divConst prog32).checkTFlat = true := by t_kernel_rfl

theorem opt32_noDivRem : noDivRem (funcTFlat (Func.divConst prog32)) = true := by
  t_kernel_rfl

private theorem sdivDefined_of_ne {n : Nat} (a : BitVec n) {b : BitVec n}
    (hb0 : b ≠ 0#n) (hb1 : b ≠ BitVec.allOnes n) : sdivDefined a b = true := by
  simp only [sdivDefined, Bool.and_eq_true, bne_iff_ne, Bool.not_eq_true',
    Bool.and_eq_false_iff, beq_eq_false_iff_ne]
  exact ⟨by simpa using hb0, .inr hb1⟩

theorem spec32 (Γ : Env) (x : BitVec 32) (m : Mem 64) :
    Func.spec Γ (Func.divConst prog32) (x, ()) m
      (fun (r1, r2, r3, r4, r5, r6,
            r7, r8, r9, r10,
            r11, r12, r13, r14, r15, r16,
            r17, r18, r19, r20, ()) m' =>
        r1 = x / 1#32 ∧ r2 = x / 3#32 ∧ r3 = x / 7#32 ∧ r4 = x / 8#32 ∧
        r5 = x / 10#32 ∧ r6 = x / 65521#32 ∧
        r7 = x % 1#32 ∧ r8 = x % 8#32 ∧ r9 = x % 10#32 ∧ r10 = x % 65521#32 ∧
        r11 = x.sdiv 1#32 ∧ r12 = x.sdiv 2#32 ∧ r13 = x.sdiv 4#32 ∧ r14 = x.sdiv 3#32 ∧
        r15 = x.sdiv 7#32 ∧ r16 = x.sdiv (-3#32) ∧
        r17 = x.srem 1#32 ∧ r18 = x.srem 65521#32 ∧ r19 = x.srem (-3#32) ∧
        r20 = x.srem (-10#32) ∧ m' = m)
      (fun _ _ _ _ => False) := by
  apply Func.divConst_spec prog32_wf
  dsimp only [Func.spec, Func.wp, prog32]
  wp_unfold_all
  repeat' apply And.intro
  all_goals first | exact (by decide) | exact sdivDefined_of_ne _ (by decide) (by decide)

def bounds32 : List (BitVec 32) :=
  [0#32, 1#32, 2#32, -1#32, BitVec.intMin 32, 0x7fffffff#32]

theorem boundary32_exec :
    bounds32.all (fun x =>
      evalPure (Func.divConst prog32 Val (fun _ => Empty) (x, ())) ==
        evalPure (prog32 Val (fun _ => Empty) (x, ()))) = true := by
  decide

theorem boundary32_spec (Γ : Env) (m : Mem 64) :
    ∀ x ∈ bounds32,
      Func.spec Γ (Func.divConst prog32) (x, ()) m
        (fun res m' => some res = evalPure (prog32 Val (fun _ => Empty) (x, ())) ∧ m' = m)
        (fun _ _ _ _ => False) := by
  intro x hx
  refine Func.spec_mono Γ (Func.divConst prog32) (x, ()) m _ _ _ _
    (fun (r1, r2, r3, r4, r5, r6, r7, r8, r9, r10,
          r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, ()) _ h => ?_)
    (fun _ _ _ _ hf => hf) (spec32 Γ x m)
  rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, hm⟩
  subst h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 hm
  simp only [bounds32, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩

/-! ## 5. Full `64`-bit suite (`/ 3`, `/ 7`, `/ 10`, `% 10`, `% 65521`, `/ (-3)`, `% (-10)`) -/

abbrev Out64 :=
  [i64, i64, i64, i64, i64, i64,
   i64, i64, i64, i64,
   i64, i64, i64, i64, i64, i64,
   i64, i64, i64, i64]

def prog64 : Func [i64] Out64 := fun _ _ p =>
  let x := p.1
  .let_ (op2 (.udiv 64) (.var x) (.imm 1#64)) fun u1 =>
  .let_ (op2 (.udiv 64) (.var x) (.imm 3#64)) fun u3 =>
  .let_ (op2 (.udiv 64) (.var x) (.imm 7#64)) fun u7 =>
  .let_ (op2 (.udiv 64) (.var x) (.imm 8#64)) fun u8 =>
  .let_ (op2 (.udiv 64) (.var x) (.imm 10#64)) fun u10 =>
  .let_ (op2 (.udiv 64) (.var x) (.imm 65521#64)) fun uMb8 =>
  .let_ (op2 (.urem 64) (.var x) (.imm 1#64)) fun ur1 =>
  .let_ (op2 (.urem 64) (.var x) (.imm 8#64)) fun ur8 =>
  .let_ (op2 (.urem 64) (.var x) (.imm 10#64)) fun ur10 =>
  .let_ (op2 (.urem 64) (.var x) (.imm 65521#64)) fun urMb8 =>
  .let_ (op2 (.sdiv 64) (.var x) (.imm 1#64)) fun s1 =>
  .let_ (op2 (.sdiv 64) (.var x) (.imm 2#64)) fun s2 =>
  .let_ (op2 (.sdiv 64) (.var x) (.imm 4#64)) fun s4 =>
  .let_ (op2 (.sdiv 64) (.var x) (.imm 3#64)) fun s3 =>
  .let_ (op2 (.sdiv 64) (.var x) (.imm 7#64)) fun s7 =>
  .let_ (op2 (.sdiv 64) (.var x) (.imm (-3#64))) fun sN3 =>
  .let_ (op2 (.srem 64) (.var x) (.imm 1#64)) fun sr1 =>
  .let_ (op2 (.srem 64) (.var x) (.imm 65521#64)) fun srMb8 =>
  .let_ (op2 (.srem 64) (.var x) (.imm (-3#64))) fun srN3 =>
  .let_ (op2 (.srem 64) (.var x) (.imm (-10#64))) fun srN10 =>
  .ret (.var u1.1, .var u3.1, .var u7.1, .var u8.1, .var u10.1, .var uMb8.1,
    .var ur1.1, .var ur8.1, .var ur10.1, .var urMb8.1,
    .var s1.1, .var s2.1, .var s4.1, .var s3.1, .var s7.1, .var sN3.1,
    .var sr1.1, .var srMb8.1, .var srN3.1, .var srN10.1, ())

theorem prog64_wf : prog64.Wf := by t_wf_reify

theorem opt64_wf : (Func.divConst prog64).Wf := Func.divConst_wf prog64_wf

theorem opt64_checkTFlat : (Func.divConst prog64).checkTFlat = true := by t_kernel_rfl

theorem opt64_noDivRem : noDivRem (funcTFlat (Func.divConst prog64)) = true := by
  t_kernel_rfl

theorem spec64 (Γ : Env) (x : BitVec 64) (m : Mem 64) :
    Func.spec Γ (Func.divConst prog64) (x, ()) m
      (fun (r1, r2, r3, r4, r5, r6,
            r7, r8, r9, r10,
            r11, r12, r13, r14, r15, r16,
            r17, r18, r19, r20, ()) m' =>
        r1 = x / 1#64 ∧ r2 = x / 3#64 ∧ r3 = x / 7#64 ∧ r4 = x / 8#64 ∧
        r5 = x / 10#64 ∧ r6 = x / 65521#64 ∧
        r7 = x % 1#64 ∧ r8 = x % 8#64 ∧ r9 = x % 10#64 ∧ r10 = x % 65521#64 ∧
        r11 = x.sdiv 1#64 ∧ r12 = x.sdiv 2#64 ∧ r13 = x.sdiv 4#64 ∧ r14 = x.sdiv 3#64 ∧
        r15 = x.sdiv 7#64 ∧ r16 = x.sdiv (-3#64) ∧
        r17 = x.srem 1#64 ∧ r18 = x.srem 65521#64 ∧ r19 = x.srem (-3#64) ∧
        r20 = x.srem (-10#64) ∧ m' = m)
      (fun _ _ _ _ => False) := by
  apply Func.divConst_spec prog64_wf
  dsimp only [Func.spec, Func.wp, prog64]
  wp_unfold_all
  repeat' apply And.intro
  all_goals first | exact (by decide) | exact sdivDefined_of_ne _ (by decide) (by decide)

def bounds64 : List (BitVec 64) :=
  [0#64, 1#64, 2#64, -1#64, BitVec.intMin 64, 0x7fffffffffffffff#64]

theorem boundary64_exec :
    bounds64.all (fun x =>
      evalPure (Func.divConst prog64 Val (fun _ => Empty) (x, ())) ==
        evalPure (prog64 Val (fun _ => Empty) (x, ()))) = true := by
  decide

theorem boundary64_spec (Γ : Env) (m : Mem 64) :
    ∀ x ∈ bounds64,
      Func.spec Γ (Func.divConst prog64) (x, ()) m
        (fun res m' => some res = evalPure (prog64 Val (fun _ => Empty) (x, ())) ∧ m' = m)
        (fun _ _ _ _ => False) := by
  intro x hx
  refine Func.spec_mono Γ (Func.divConst prog64) (x, ()) m _ _ _ _
    (fun (r1, r2, r3, r4, r5, r6, r7, r8, r9, r10,
          r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, ()) _ h => ?_)
    (fun _ _ _ _ hf => hf) (spec64 Γ x m)
  rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, hm⟩
  subst h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 hm
  simp only [bounds64, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩

/-! ## 6. UB preservation (`d = 0`, signed `d = -1`), variable divisors, and bitwidth guards -/

def ubGuard32 : Func [i32, i32, .bits 16] [i32, i32, i32, i32, i32, i32, i32, i32, .bits 16] :=
  fun _ _ p =>
  let x := p.1
  let y := p.2.1
  let z := p.2.2.1
  .let_ (op2 (.udiv 32) (.var x) (.imm 0#32)) fun u0 =>
  .let_ (op2 (.urem 32) (.var x) (.imm 0#32)) fun ur0 =>
  .let_ (op2 (.sdiv 32) (.var x) (.imm 0#32)) fun s0 =>
  .let_ (op2 (.srem 32) (.var x) (.imm 0#32)) fun sr0 =>
  .let_ (op2 (.sdiv 32) (.var x) (.imm (BitVec.allOnes 32))) fun sm1 =>
  .let_ (op2 (.srem 32) (.var x) (.imm (BitVec.allOnes 32))) fun srm1 =>
  .let_ (op2 (.udiv 32) (.var x) (.var y)) fun uv =>
  .let_ (op2 (.sdiv 32) (.var x) (.var y)) fun sv =>
  .let_ (op2 (.udiv 16) (.var z) (.imm 3#16)) fun u16 =>
  .ret (.var u0.1, .var ur0.1, .var s0.1, .var sr0.1, .var sm1.1, .var srm1.1,
    .var uv.1, .var sv.1, .var u16.1, ())

theorem ubGuard32_untouched : Func.divConst ubGuard32 = ubGuard32 := by t_kernel_rfl

theorem ubGuard32_wf : (Func.divConst ubGuard32).Wf := Func.divConst_wf (by t_wf_reify)

theorem ubGuard32_checkTFlat : (Func.divConst ubGuard32).checkTFlat = true := by t_kernel_rfl

def ubGuard64 : Func [i64, i64] [i64, i64, i64, i64, i64, i64, i64, i64] := fun _ _ p =>
  let x := p.1
  let y := p.2.1
  .let_ (op2 (.udiv 64) (.var x) (.imm 0#64)) fun u0 =>
  .let_ (op2 (.urem 64) (.var x) (.imm 0#64)) fun ur0 =>
  .let_ (op2 (.sdiv 64) (.var x) (.imm 0#64)) fun s0 =>
  .let_ (op2 (.srem 64) (.var x) (.imm 0#64)) fun sr0 =>
  .let_ (op2 (.sdiv 64) (.var x) (.imm (BitVec.allOnes 64))) fun sm1 =>
  .let_ (op2 (.srem 64) (.var x) (.imm (BitVec.allOnes 64))) fun srm1 =>
  .let_ (op2 (.udiv 64) (.var x) (.var y)) fun uv =>
  .let_ (op2 (.sdiv 64) (.var x) (.var y)) fun sv =>
  .ret (.var u0.1, .var ur0.1, .var s0.1, .var sr0.1, .var sm1.1, .var srm1.1,
    .var uv.1, .var sv.1, ())

theorem ubGuard64_untouched : Func.divConst ubGuard64 = ubGuard64 := by t_kernel_rfl

theorem ubGuard64_wf : (Func.divConst ubGuard64).Wf := Func.divConst_wf (by t_wf_reify)

theorem ubGuard64_checkTFlat : (Func.divConst ubGuard64).checkTFlat = true := by t_kernel_rfl

def s32DivNeg1 : Func [i32] [i32] := fun _ _ p =>
  .let_ (op2 (.sdiv 32) (.var p.1) (.imm (BitVec.allOnes 32))) fun q => .ret (.var q.1, ())

theorem s32DivNeg1_untouched : Func.divConst s32DivNeg1 = s32DivNeg1 := by t_kernel_rfl

theorem s32DivNeg1_intMin_ub (Γ : Env) (m : Mem 64) :
    ¬ Func.spec Γ (Func.divConst s32DivNeg1) (BitVec.intMin 32, ()) m
        (fun _ _ => True) (fun _ _ _ _ => False) := by
  rw [s32DivNeg1_untouched]
  dsimp only [Func.spec, Func.wp, s32DivNeg1]
  wp_unfold_all
  decide

/-! ## 7. `group` loop + memory effects (Adler-32 `% 65521`, `/ 10`) -/

def mb8LoopProg : Func [i64, i64] [i64, i64] := fun _ _ p =>
  let seed := p.1
  let ptr := p.2.1
  .group (sig := [[i64]])
    (fun (_blk, ()) =>
      .cons (fun x =>
        .load i64 (.var ptr) fun acc =>
        .let_ (op2 (.add i64) (.var x.1) (.var acc)) fun sum =>
        .let_ (op2 (.urem 64) (.var sum.1) (.imm 65521#64)) fun modVal =>
        .let_ (op2 (.udiv 64) (.var sum.1) (.imm 10#64)) fun divVal =>
        .ret (.var modVal.1, .var divVal.1, ()))
      .nil)
    (fun (blk, ()) =>
      .store (.var seed) (.var ptr)
        (.jump blk (.var seed, ())))

theorem mb8LoopProg_wf : mb8LoopProg.Wf := by t_wf_reify

theorem opt_mb8LoopProg_wf : (Func.divConst mb8LoopProg).Wf := Func.divConst_wf mb8LoopProg_wf

theorem opt_mb8LoopProg_checkTFlat : (Func.divConst mb8LoopProg).checkTFlat = true := by
  t_kernel_rfl

theorem opt_mb8LoopProg_noDivRem :
    noDivRem (funcTFlat (Func.divConst mb8LoopProg)) = true := by
  t_kernel_rfl

theorem mb8LoopProg_spec (Γ : Env) (seed ptr v0 : BitVec 64) (R : Mem 64 → Prop) (m : Mem 64)
    (hm : (cell64 ptr v0 ⋆ R) m) :
    Func.spec Γ (Func.divConst mb8LoopProg) (seed, ptr, ()) m
      (fun (rmod, rdiv, ()) m' =>
        rmod = (seed + seed) % 65521#64 ∧ rdiv = (seed + seed) / 10#64 ∧ (cell64 ptr seed ⋆ R) m')
      (fun _ _ _ _ => False) := by
  apply Func.divConst_spec mb8LoopProg_wf
  dsimp only [Func.spec, Func.wp, mb8LoopProg]
  refine wp_join_group (fun (x, ()) m' => x = seed ∧ (cell64 ptr seed ⋆ R) m') ?_ ?_
  · intro _ ⟨x, ⟨⟩⟩ m' ⟨hx, hm'⟩
    simp only [Blocks.get_here]
    refine wp_load_cell64 hm' ?_
    wp_unfold_all
    refine ⟨by decide, by decide, ?_⟩
    subst hx
    exact ⟨rfl, rfl, hm'⟩
  · intro J hJ
    refine wp_store_cell64 hm fun m' hm' => ?_
    exact hJ (seed, ()) m' ⟨rfl, hm'⟩

/-! ## 8. Axiom audit -/

#print axioms LeanQbe.T.uNoAddCert_sound
#print axioms LeanQbe.T.uAddShiftCert_sound
#print axioms LeanQbe.T.sDivCert_sound
#print axioms LeanQbe.T.Func.divConst_wf
#print axioms LeanQbe.T.Func.divConst_spec
#print axioms LeanQbe.T.DivConstTest.spec32
#print axioms LeanQbe.T.DivConstTest.spec64

end LeanQbe.T.DivConstTest
