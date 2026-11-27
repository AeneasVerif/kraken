module

public import LeanQbe.T.AssumeBitsLemmas
public import LeanQbe.T.FlatLemmas
public import LeanQbe.T.WPLemmas
public import LeanQbe.T.Main
public import LeanQbe.T.Examples.LratBytes
public import LeanQbe.T.Examples.Kissat.FullM4
meta import LeanQbe.T.AssumeBits
meta import LeanQbe.T.Main
meta import LeanQbe.T.Examples.LratBytes
meta import LeanQbe.T.Examples.Kissat.FullM4

/-!
# Tests of `LeanQbe.T.AssumeBits`

Covers:
1. Exact kernel-checked (`t_kernel_rfl`) rewrites, including the `full_prop_lit_raw` watch-scan
   pattern (`test $0x80000000; jne` dominating `and $0x7fffffff`), the same fact flowing into a
   nested loop body, sign tests (`x <s 0`, `x >=s 0`), unsigned bounds (`x <u 256`), `!c`, and
   known-zero masks from `zext`, `lshr`, and `and` (`and x c → x`, `and x c → 0`).
2. Negative cases: the mask is kept on the arm where the tested bit is set and on `var &&& var`.
3. `Func.assumeBits_{wf,spec,callsOk}` instantiations and an end-to-end contract transported
   from a source proof.
4. Corpus checks after `Fn.mid`: the pass fires on the hot `FullM4` BCP functions (including
   `full_prop_lit_raw`), and every rewritten `FullM4` / `LratBytes` body passes `checkTFlat`.
5. `#print axioms` audit (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

section

namespace LeanQbeTest.T.AssumeBitsTest

open LeanQbe.T

/-! ## 1. `full_prop_lit_raw` watch scan: `(w0 & 0x80000000) != 0` dominates `w0 & 0x7fffffff` -/

/-- Watch-scan step: binary watches keep the mask; clause watches have bit `31` clear. -/
def propLitL5 : Func [i32, i64] [i64] := fun _ _ (w0, nlits, ()) =>
  .let_ (op2 (.and i32) (.var w0) (.imm 0x80000000)) fun (bin, ()) =>
  .let_ (op2 (.ne i32) (.var bin) (.imm 0)) fun (c, ()) =>
  .jnz (.var c)
    (.let_ (op2 (.and i32) (.var w0) (.imm 0x7fffffff)) fun (other, ()) =>
     .let_ (op1 (.zext 32 64) (.var other)) fun (o64, ()) =>
     .ret (.var o64, ()))
    (.let_ (op2 (.and i32) (.var w0) (.imm 0x7fffffff)) fun (blk, ()) =>
     .let_ (op1 (.zext 32 64) (.var blk)) fun (b64, ()) =>
     .let_ (op2 (.ult i64) (.var b64) (.var nlits)) fun (inb, ()) =>
     .jnz (.var inb) (.ret (.var b64, ())) (.ret (.imm 0, ())))

theorem propLitL5_ab : Func.assumeBits propLitL5 = fun _ _ (w0, nlits, ()) =>
    .let_ (op2 (.and i32) (.var w0) (.imm 0x80000000)) fun (bin, ()) =>
    .let_ (op2 (.ne i32) (.var bin) (.imm 0)) fun (c, ()) =>
    .jnz (.var c)
      (.let_ (op2 (.and i32) (.var w0) (.imm 0x7fffffff)) fun (other, ()) =>
       .let_ (op1 (.zext 32 64) (.var other)) fun (o64, ()) =>
       .ret (.var o64, ()))
      (.let_ (op1 (.zext 32 64) (.var w0)) fun (b64, ()) =>
       .let_ (op2 (.ult i64) (.var b64) (.var nlits)) fun (inb, ()) =>
       .jnz (.var inb) (.ret (.var b64, ())) (.ret (.imm 0, ()))) := by
  t_kernel_rfl

theorem propLitL5_wf : propLitL5.Wf := by t_wf_reify
theorem propLitL5_ab_wf : (Func.assumeBits propLitL5).Wf := Func.assumeBits_wf propLitL5_wf
theorem propLitL5_ab_check : Func.checkTFlat (Func.assumeBits propLitL5) = true := by
  t_kernel_rfl

/-- `(w0 & 0x80000000) == 0` guards a loop whose body masks `w0`: the fact reaches the body. -/
def maskInLoop : Func [i32, i64] [i64] := fun _ _ (w0, n, ()) =>
  .let_ (op2 (.and i32) (.var w0) (.imm 0x80000000)) fun (bin, ()) =>
  .let_ (op2 (.eq i32) (.var bin) (.imm 0)) fun (c, ()) =>
  .jnz (.var c)
    (loop1 (ts := [i64])
      (fun loop (i, ()) =>
        .let_ (op2 (.and i32) (.var w0) (.imm 0x7fffffff)) fun (blk, ()) =>
        .let_ (op1 (.zext 32 64) (.var blk)) fun (b64, ()) =>
        .let_ (op2 (.ult i64) (.var i) (.var b64)) fun (lt, ()) =>
        .jnz (.var lt)
          (.let_ (op2 (.add i64) (.var i) (.imm 1)) fun (i', ()) => .jump loop (.var i', ()))
          (.ret (.var i, ())))
      (fun loop => .jump loop (.var n, ())))
    (.ret (.imm 0, ()))

theorem maskInLoop_ab : Func.assumeBits maskInLoop = fun _ _ (w0, n, ()) =>
    .let_ (op2 (.and i32) (.var w0) (.imm 0x80000000)) fun (bin, ()) =>
    .let_ (op2 (.eq i32) (.var bin) (.imm 0)) fun (c, ()) =>
    .jnz (.var c)
      (loop1 (ts := [i64])
        (fun loop (i, ()) =>
          .let_ (op1 (.zext 32 64) (.var w0)) fun (b64, ()) =>
          .let_ (op2 (.ult i64) (.var i) (.var b64)) fun (lt, ()) =>
          .jnz (.var lt)
            (.let_ (op2 (.add i64) (.var i) (.imm 1)) fun (i', ()) => .jump loop (.var i', ()))
            (.ret (.var i, ())))
        (fun loop => .jump loop (.var n, ())))
      (.ret (.imm 0, ())) := by
  t_kernel_rfl

/-! ## 2. Sign tests, unsigned bounds, and negated conditions -/

/-- `x <s 0` is false on the else arm, so bit `31` is clear there. -/
def signTest : Func [i32] [i32] := fun _ _ (x, ()) =>
  .let_ (op2 (.slt i32) (.var x) (.imm 0)) fun (neg, ()) =>
  .jnz (.var neg) (.ret (.imm 0, ()))
    (.let_ (op2 (.and i32) (.var x) (.imm 0x7fffffff)) fun (y, ()) => .ret (.var y, ()))

theorem signTest_ab : Func.assumeBits signTest = fun _ _ (x, ()) =>
    .let_ (op2 (.slt i32) (.var x) (.imm 0)) fun (neg, ()) =>
    .jnz (.var neg) (.ret (.imm 0, ())) (.ret (.var x, ())) := by
  t_kernel_rfl

/-- `x >=s 0` is true on the then arm. -/
def sgeTest : Func [i64] [i64] := fun _ _ (x, ()) =>
  .let_ (op2 (.sge i64) (.var x) (.imm 0)) fun (pos, ()) =>
  .jnz (.var pos)
    (.let_ (op2 (.and i64) (.var x) (.imm 0x7fffffffffffffff)) fun (y, ()) => .ret (.var y, ()))
    (.ret (.imm 0, ()))

theorem sgeTest_ab : Func.assumeBits sgeTest = fun _ _ (x, ()) =>
    .let_ (op2 (.sge i64) (.var x) (.imm 0)) fun (pos, ()) =>
    .jnz (.var pos) (.ret (.var x, ())) (.ret (.imm 0, ())) := by
  t_kernel_rfl

/-- `x <u 256` clears bits `[8, 32)` on the then arm. -/
def boundTest : Func [i32] [i32] := fun _ _ (x, ()) =>
  .let_ (op2 (.ult i32) (.var x) (.imm 256)) fun (small, ()) =>
  .jnz (.var small)
    (.let_ (op2 (.and i32) (.var x) (.imm 0xff)) fun (y, ()) => .ret (.var y, ()))
    (.ret (.imm 0, ()))

theorem boundTest_ab : Func.assumeBits boundTest = fun _ _ (x, ()) =>
    .let_ (op2 (.ult i32) (.var x) (.imm 256)) fun (small, ()) =>
    .jnz (.var small) (.ret (.var x, ())) (.ret (.imm 0, ())) := by
  t_kernel_rfl

/-- `!((x & 0x80000000) != 0)` swaps the arms of the fact. -/
def notTest : Func [i32] [i32] := fun _ _ (x, ()) =>
  .let_ (op2 (.and i32) (.var x) (.imm 0x80000000)) fun (t, ()) =>
  .let_ (op2 (.ne i32) (.var t) (.imm 0)) fun (c, ()) =>
  .let_ (op1 (.not .bool) (.var c)) fun (nc, ()) =>
  .jnz (.var nc)
    (.let_ (op2 (.and i32) (.var x) (.imm 0x7fffffff)) fun (y, ()) => .ret (.var y, ()))
    (.ret (.imm 0, ()))

theorem notTest_ab : Func.assumeBits notTest = fun _ _ (x, ()) =>
    .let_ (op2 (.and i32) (.var x) (.imm 0x80000000)) fun (t, ()) =>
    .let_ (op2 (.ne i32) (.var t) (.imm 0)) fun (c, ()) =>
    .let_ (op1 (.not .bool) (.var c)) fun (nc, ()) =>
    .jnz (.var nc) (.ret (.var x, ())) (.ret (.imm 0, ())) := by
  t_kernel_rfl

/-! ## 3. Known-zero masks (`zext`, `lshr`, `and`) and negative cases -/

/-- `zext 8 32` clears bits `[8, 32)`: `z & 0xff → z` and `z & 0xff00 → 0`. -/
def zextMask : Func [i8] [i32, i32] := fun _ _ (b, ()) =>
  .let_ (op1 (.zext 8 32) (.var b)) fun (z, ()) =>
  .let_ (op2 (.and i32) (.var z) (.imm 0xff)) fun (y, ()) =>
  .let_ (op2 (.and i32) (.imm 0xff00) (.var z)) fun (w, ()) =>
  .ret (.var y, .var w, ())

theorem zextMask_ab : Func.assumeBits zextMask = fun _ _ (b, ()) =>
    .let_ (op1 (.zext 8 32) (.var b)) fun (z, ()) =>
    .ret (.var z, .imm 0, ()) := by
  t_kernel_rfl

/-- `x >>> 24` clears bits `[8, 32)`, and `(x & 0xf0) & 0x0f` is `0`. -/
def lshrMask : Func [i32] [i32, i32] := fun _ _ (x, ()) =>
  .let_ (op2 (.lshr i32) (.var x) (.imm 24)) fun (h, ()) =>
  .let_ (op2 (.and i32) (.var h) (.imm 0xff)) fun (y, ()) =>
  .let_ (op2 (.and i32) (.var x) (.imm 0xf0)) fun (n, ()) =>
  .let_ (op2 (.and i32) (.var n) (.imm 0x0f)) fun (z, ()) =>
  .ret (.var y, .var z, ())

theorem lshrMask_ab : Func.assumeBits lshrMask = fun _ _ (x, ()) =>
    .let_ (op2 (.lshr i32) (.var x) (.imm 24)) fun (h, ()) =>
    .let_ (op2 (.and i32) (.var x) (.imm 0xf0)) fun (_n, ()) =>
    .ret (.var h, .imm 0, ()) := by
  t_kernel_rfl

/-- Nothing is known about `x` on the set-bit arm or about `x &&& y`: no rewrite. -/
def keepTest : Func [i32, i32] [i32] := fun _ _ (x, y, ()) =>
  .let_ (op2 (.and i32) (.var x) (.imm 0x80000000)) fun (t, ()) =>
  .let_ (op2 (.ne i32) (.var t) (.imm 0)) fun (c, ()) =>
  .jnz (.var c)
    (.let_ (op2 (.and i32) (.var x) (.imm 0x7fffffff)) fun (r, ()) => .ret (.var r, ()))
    (.let_ (op2 (.and i32) (.var x) (.var y)) fun (r, ()) => .ret (.var r, ()))

theorem keepTest_ab : Func.assumeBits keepTest = keepTest := by
  t_kernel_rfl

/-! ## 4. Soundness instantiations -/

theorem signTest_wf : signTest.Wf := by t_wf_reify

/-- Source contract of `signTest`: memory is unchanged and the result is non-negative. -/
theorem signTest_spec (Γ : Env) (x : BitVec 32) (m : Mem 64) (X : XPost) :
    Func.spec Γ signTest (x, ()) m (fun (r, ()) m' => m' = m ∧ r.msb = false) X := by
  dsimp only [Func.spec, Func.wp, signTest]
  simp only [wp, Op.wp, op2, vals, Arg.val, OpCode.wp_cmp, OpCode.wp_and, liftCmp, lift2,
    CmpOp.evalBits, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, cast_eq, true_and]
  refine ⟨fun _ => rfl, fun h => ?_⟩
  have h' : x.msb = false := by rw [← BitVec.slt_zero_eq_msb]; exact h
  rw [BitVec.msb_and, h', Bool.false_and]

/-- The contract transfers to the simplified function (where the mask is gone). -/
theorem signTest_ab_spec (Γ : Env) (x : BitVec 32) (m : Mem 64) (X : XPost) :
    Func.spec Γ (Func.assumeBits signTest) (x, ()) m
      (fun (r, ()) m' => m' = m ∧ r.msb = false) X :=
  Func.assumeBits_spec signTest_wf (signTest_spec Γ x m X)

theorem propLitL5_ab_callsOk :
    ((Func.assumeBits propLitL5) (fun _ => Unit) (fun _ => Unit) (Tup.units _)).callsOk [] [] :=
  Func.assumeBits_callsOk propLitL5_wf (by
    simp [propLitL5, Expr.callsOk])

theorem maskInLoop_ab_wf : (Func.assumeBits maskInLoop).Wf :=
  Func.assumeBits_wf (by t_wf_reify)

/-! ## 5. Real-corpus checks (`FullM4` hot BCP loops and `LratBytes`) -/

/-- Eliminated op count at the `lateCore` `assumeBits` point and `Fn.mid` `checkTFlat`. -/
def abDelta (f : Fn) : Nat × Bool :=
  let lf := (f.earlyOpt).legal LegalTarget.x64
  let pre := Func.gvn (Func.memLoad (Func.renorm (Func.copy
    (Func.divConst (Func.canon (Func.fold lf.body))))))
  let a := Func.assumeBits pre
  let mf := f.mid LegalTarget.x64
  let postMid := Func.assumeBits mf.body
  (tflatSize (reifyFunc pre) - tflatSize (reifyFunc (as := lf.as) a),
    Func.checkTFlat a && Func.checkTFlat mf.body &&
      tflatSize (reifyFunc mf.body) == tflatSize (reifyFunc (as := mf.as) postMid))

/-- Five `FullM4` BCP functions with a branch-implied redundant `and $0x7fffffff` (including
`full_prop_lit_raw`). The guards below only require well-formed output and at least one surviving
elimination, so source-level edits of these functions (e.g. reordering the blocking-literal test)
do not break this file. -/
def m4Hot : List String :=
  ["full_prop_lit_raw", "full_probe_prop_lit", "full_promote_clause", "full_reduce",
    "full_analyze_rsn"]

/-- `abDelta` of every present `m4Hot` function. -/
def m4HotDeltas : List (Nat × Bool) :=
  m4Hot.filterMap fun n =>
    (LeanQbe.T.Examples.Kissat.FullM4.m4Fns.find? (·.name == n)).map abDelta

#guard m4HotDeltas.all (·.2)
#guard m4HotDeltas.foldl (· + ·.1) 0 ≥ 1
#guard LeanQbe.T.Examples.LratBytes.lratBytesModule.fns.all fun f => (abDelta f).2

/-! ## 6. Axiom audit (`⊆ [propext, Classical.choice, Quot.sound]`) -/

#print axioms LeanQbe.T.assumeBits_wp
#print axioms LeanQbe.T.assumeBits_wf
#print axioms LeanQbe.T.assumeBits_callsOk
#print axioms LeanQbe.T.OpRel.abLet_wp
#print axioms LeanQbe.T.Func.assumeBits_wf
#print axioms LeanQbe.T.Func.assumeBits_spec
#print axioms LeanQbe.T.Func.assumeBits_correct
#print axioms LeanQbe.T.Func.assumeBits_callsOk
#print axioms LeanQbeTest.T.AssumeBitsTest.propLitL5_ab
#print axioms LeanQbeTest.T.AssumeBitsTest.signTest_ab_spec
#print axioms LeanQbeTest.T.AssumeBitsTest.propLitL5_ab_callsOk

end LeanQbeTest.T.AssumeBitsTest
