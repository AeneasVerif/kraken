module

public import LeanQbe.T.OptLemmas
public import LeanQbe.T.WPLemmas
public import LeanQbe.T.FlatLemmas
public import LeanQbe.T.Logic.Rules

/-!
# Mid-End Pass-Order Wiring (`ZeroPeel`, `AssumeBits`, `assumeElim` Cleanup) & `Fn.renorm` Tests

Covers:
1. `ZeroPeel` constant-fill widening (`fillLoop`) and bounded 1st-iter loop peeling
   (`peelLoop`, budget `≤ 24`) wired into `Func.earlyOpt` (`checkTFlat`, `zpLoops`, `Wf`,
   `Func.spec`).
2. `AssumeBits` branch-implied mask elimination (`x &&& 0x80000000 == 0` dominating
   `x &&& 0x7fffffff`) wired into `Func.lateCore` / `Func.lateOpt` (`t_kernel_rfl`, `Wf`,
   `Func.spec`).
3. Post-`assumeElim` cleanup (`assumeElim → fold → gvn`) in `Func.lateCfg` / `Func.lateOpt`
   deduplicating expressions exposed after dead-branch removal (`t_kernel_rfl`, `Wf`, `Func.spec`).
4. Materialized `Fn.renorm` definition equality (`(Fn.renorm fn).body = Func.renorm fn.body`
   by `rfl`, `Fn.renorm_wf`, `Fn.renorm_spec`).
5. Single-line standard-axiom `#print axioms`.
-/

set_option autoImplicit false

section

namespace Stage1Test

open LeanQbe.T

/-! ## 1. `ZeroPeel` wired in `Func.earlyOpt` -/

/-- Byte zero-fill loop widened by `ZeroPeel.widenFillSingle` inside `Func.earlyOpt`. -/
def fillLoop : Func [i64, i64] [i64] := fun _ _ (ptr, n, ()) =>
  loop1 (ts := [i64])
    (fun loop (i, ()) =>
      .let_ (op2 (.ult i64) (.var i) (.var n)) fun (cond, ()) =>
      .jnz (.var cond)
        (.let_ (op2 (.add i64) (.var ptr) (.var i)) fun (addr, ()) =>
         .store (t := .bits 8) (.imm 0#8) (.var addr)
           (.let_ (op2 (.add i64) (.var i) (.imm 1)) fun (i', ()) =>
            .jump loop (.var i', ())))
        (.ret (.var ptr, ())))
    (fun loop => .jump loop (.imm 0, ()))

theorem fill_wf : fillLoop.Wf := by t_wf_reify

theorem fill_early_wf : (Func.earlyOpt fillLoop).Wf := Func.earlyOpt_wf fill_wf

theorem fill_early_check : Func.checkTFlat (Func.earlyOpt fillLoop) = true := by
  decide +kernel

theorem fill_early_loops :
    ZeroPeel.zpLoops (reifyFunc (Func.earlyOpt fillLoop)) = 2 := by
  decide +kernel

/-- Single-block byte-scanning loop peeled (1st iter) inside `Func.earlyOpt` (budget ≤ 24). -/
def peelLoop : Func [i64] [.bits 8] := fun _ _ (ptr, ()) =>
  loop1 (ts := [i64, i64])
    (fun loop (p, n, ()) =>
      .load (.bits 8) (.var p) fun b =>
      .let_ (op2 (.ult (.bits 8)) (.var b) (.imm 128#8)) fun (c, ()) =>
      .jnz (.var c) (.ret (.var b, ()))
        (.let_ (op2 (.add i64) (.var p) (.imm 1)) fun (p', ()) =>
         .let_ (op2 (.add i64) (.var n) (.imm 1)) fun (n', ()) =>
         .let_ (op2 (.ult i64) (.var n') (.imm 10)) fun (ok, ()) =>
         .jnz (.var ok) (.jump loop (.var p', .var n', ())) (.ret (.var b, ()))))
    (fun loop => .jump loop (.var ptr, .imm 0, ()))

theorem peel_wf : peelLoop.Wf := by t_wf_reify

theorem peel_early_check : Func.checkTFlat (Func.earlyOpt peelLoop) = true := by
  decide +kernel

theorem peel_early_loops :
    ZeroPeel.zpLoops (reifyFunc (Func.earlyOpt peelLoop)) = 1 := by
  decide +kernel

theorem peel_early_size :
    tflatSize (reifyFunc (Func.earlyOpt peelLoop)) = 17 := by
  decide +kernel

/-! ## 2. `AssumeBits` wired in `Func.lateCore` / `Func.lateOpt` -/

/-- `(w0 & 0x80000000) == 0` eliminates `w0 & 0x7fffffff` in `Func.lateOpt`. -/
def abMaskProg : Func [i32] [i64] := fun _ _ (w0, ()) =>
  .let_ (op2 (.and i32) (.var w0) (.imm 0x80000000)) fun (bin, ()) =>
  .let_ (op2 (.eq i32) (.var bin) (.imm 0)) fun (c, ()) =>
  .jnz (.var c)
    (.let_ (op2 (.and i32) (.var w0) (.imm 0x7fffffff)) fun (lo, ()) =>
     .let_ (op1 (.zext 32 64) (.var lo)) fun (z, ()) => .ret (.var z, ()))
    (.ret (.imm 0, ()))

theorem abMask_late_out : Func.lateOpt abMaskProg = fun _ _ (w0, ()) =>
    .let_ (op2 (.and i32) (.var w0) (.imm 0x80000000)) fun (bin, ()) =>
    .let_ (op2 (.eq i32) (.var bin) (.imm 0)) fun (c, ()) =>
    .let_ (op1 (.zext 32 64) (.var w0)) fun (z, ()) =>
    .let_ (op3 (.select i64) (.var c) (.var z) (.imm 0)) fun (sel, ()) =>
    .ret (.var sel, ()) := by
  t_kernel_rfl

theorem abMask_wf : abMaskProg.Wf := by t_wf_reify

private theorem abMask_src_spec (Γ : Env) (w0 : BitVec 32) (m : Mem 64) :
    Func.spec Γ abMaskProg (w0, ()) m
      (fun (r, ()) m' =>
        r = (if w0 &&& 0x80000000#32 == 0#32 then (w0 &&& 0x7fffffff#32).setWidth 64
             else 0#64) ∧ m' = m)
      (fun _ _ _ _ => False) := by
  dsimp only [Func.spec, Func.wp, abMaskProg, wp, Op.wp, OpCode.wp, op1, op2, vals, Arg.val,
    lift1, lift2, lift3, liftCmp, CmpOp.evalBits, i32, i64, Closed]
  by_cases h : w0 &&& 0x80000000#32 = 0#32 <;> simp [h]

theorem abMask_late_spec (Γ : Env) (w0 : BitVec 32) (m : Mem 64) :
    Func.spec Γ (Func.lateOpt abMaskProg) (w0, ()) m
      (fun (r, ()) m' =>
        r = (if w0 &&& 0x80000000#32 == 0#32 then (w0 &&& 0x7fffffff#32).setWidth 64
             else 0#64) ∧ m' = m)
      (fun _ _ _ _ => False) :=
  Func.lateOpt_spec abMask_wf (abMask_src_spec Γ w0 m)

/-! ## 3. `cf` (`assumeElim → fold → gvn`) post-`ifOptBits` cleanup in `Func.lateCfg` -/

/-- `assumeElim` drops `.jnz (.var c) _ .hlt` exposing duplicate `x + 1` collapsed by `cf`. -/
def cfProg : Func [i64, .bool] [i64, i64] := fun _ _ (x, c, ()) =>
  .jnz (.var c)
    (.let_ (op2 (.add i64) (.var x) (.imm 1)) fun (y, ()) =>
     .jnz (.var c)
       (.let_ (op2 (.add i64) (.var x) (.imm 1)) fun (z, ()) => .ret (.var y, .var z, ()))
       .hlt)
    (.ret (.imm 0, .imm 0, ()))

theorem cf_lateCfg_out : Func.lateCfg cfProg = fun _ _ (x, c, ()) =>
    .jnz (.var c)
      (.let_ (op2 (.add i64) (.var x) (.imm 1)) fun (y, ()) => .ret (.var y, .var y, ()))
      (.ret (.imm 0, .imm 0, ())) := by
  t_kernel_rfl

theorem cf_wf : cfProg.Wf := by t_wf_reify

theorem cf_lateCfg_spec (Γ : Env) (x : BitVec 64) (c : Bool) (m : Mem 64) :
    Func.spec Γ (Func.lateCfg cfProg) (x, c, ()) m
      (fun (r0, r1, ()) m' =>
        (if c then r0 = x + 1#64 ∧ r1 = x + 1#64 else r0 = 0#64 ∧ r1 = 0#64) ∧ m' = m)
      (fun _ _ _ _ => False) := by
  apply Func.lateCfg_spec cf_wf
  dsimp only [Func.spec, Func.wp, cfProg, wp, Op.wp, OpCode.wp, op2, vals, Arg.val,
    lift1, lift2, lift3, Closed]
  cases c <;> simp

/-! ## 4. Materialized `Fn.renorm` definition & contract -/

def abMaskFn : Fn := ⟨"abMask", [i32], [i64], abMaskProg⟩

theorem fnRenorm_eq : (Fn.renorm abMaskFn).body = Func.renorm abMaskFn.body := rfl

theorem fnRenorm_wf : (Fn.renorm abMaskFn).Wf := Fn.renorm_wf abMaskFn

theorem fnRenorm_spec (Γ : Env) (w0 : BitVec 32) (m : Mem 64) :
    Func.spec Γ (Fn.renorm abMaskFn).body (w0, ()) m
      (fun (r, ()) m' =>
        r = (if w0 &&& 0x80000000#32 == 0#32 then (w0 &&& 0x7fffffff#32).setWidth 64
             else 0#64) ∧ m' = m)
      (fun _ _ _ _ => False) :=
  Fn.renorm_spec (fn := abMaskFn) abMask_wf (abMask_src_spec Γ w0 m)

#print axioms fill_early_wf
#print axioms fill_early_check
#print axioms fill_early_loops
#print axioms peel_early_check
#print axioms peel_early_loops
#print axioms peel_early_size
#print axioms abMask_late_spec
#print axioms cf_lateCfg_spec
#print axioms fnRenorm_wf
#print axioms fnRenorm_spec

end Stage1Test
