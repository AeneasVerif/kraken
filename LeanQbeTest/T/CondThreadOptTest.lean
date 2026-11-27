module

public import LeanQbe.T.CondThreadOptLemmas
public import LeanQbe.T.FlatLemmas
public import LeanQbe.T.WPLemmas
public import LeanQbe.T.Main
public import LeanQbe.T.Examples.LratBytes
public import LeanQbe.T.Examples.Kissat.FullM4
meta import LeanQbe.T.CondThreadOpt
meta import LeanQbe.T.Main
meta import LeanQbe.T.Examples.LratBytes
meta import LeanQbe.T.Examples.Kissat.FullM4

/-!
# Targeted Unit, Soundness, Corpus & Axiom Tests for `LeanQbe.T.CondThreadOpt`

Covers:
1. Path-fact and known-condition elimination (`Func.pathCondOpt` / `Func.condThreadOpt`):
   redundant re-tests (`v <u cur_vars` along dominating arm), implication lattice (`x <u 10`
   implies `x <u 20` and `!(x == 15)`, `x <u y` implies `y != 0`), propagation into loops,
   and negative non-elimination when facts do not imply the branch condition.
2. Constant-arg branch threading & bool-param block splitting (`Func.condThreadOpt` /
   `Func.condThreadLateOpt`): bool-param `splitBool` specialization + dead-dispatcher pruning,
   and constant-arg `cmp; jnz` head threading via `simCanThread`.
3. Closed-function `Wf`, `condThread_ok` / `Func.condThreadLateOpt_spec`, and
   `Func.condThreadOpt_callsOk` / `Func.condThreadLateOpt_callsOk` instantiations.
4. Corpus checks after `Fn.mid LegalTarget.x64` on `FullM4` (`231` functions) and `LratBytes`.
5. `#print axioms` audit (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

section

namespace LeanQbeTest.T.CondThreadOptTest

open LeanQbe.T

/-! ## 1. Known-condition elimination & path-fact propagation -/

/-- Dominated redundant `v <u cur_vars` re-test along the same path (as in `full_sweep_copy`). -/
def retestLt : Func [i64, i64] [i64] := fun _ _ (v, curVars, ()) =>
  .let_ (op2 (.ult i64) (.var v) (.var curVars)) fun (c1, ()) =>
  .jnz (.var c1)
    (.let_ (op2 (.add i64) (.var v) (.imm 1)) fun (v1, ()) =>
     .let_ (op2 (.ult i64) (.var v) (.var curVars)) fun (c2, ()) =>
     .jnz (.var c2) (.ret (.var v1, ())) (.ret (.imm 999, ())))
    (.ret (.imm 0, ()))

theorem retestLt_pc : Func.pathCondOpt retestLt = fun _ _ (v, curVars, ()) =>
    .let_ (op2 (.ult i64) (.var v) (.var curVars)) fun (c1, ()) =>
    .jnz (.var c1)
      (.let_ (op2 (.add i64) (.var v) (.imm 1)) fun (v1, ()) =>
       .ret (.var v1, ()))
      (.ret (.imm 0, ())) := by
  t_kernel_rfl

theorem retestLt_ct_flat :
    reifyFunc (Func.condThreadOpt retestLt) = reifyFunc (Func.pathCondOpt retestLt) := by
  t_kernel_rfl

theorem retestLt_wf : retestLt.Wf := by t_wf_reify
theorem retestLt_ct_wf : (Func.condThreadOpt retestLt).Wf := Func.condThreadOpt_wf retestLt_wf
theorem retestLt_late_check : Func.checkTFlat (Func.condThreadLateOpt retestLt) = true := by
  t_kernel_rfl

/-- Constant bounds (`x <u 10` implies `x <u 20` and `x != 15`) and non-zero (`x <u y` implies
`y != 0`). -/
def cmpImpliesChain : Func [i64, i64] [i64] := fun _ _ (x, y, ()) =>
  .let_ (op2 (.ult i64) (.var x) (.imm 10)) fun (c1, ()) =>
  .jnz (.var c1)
    (.let_ (op2 (.ult i64) (.var x) (.imm 20)) fun (c2, ()) =>
     .jnz (.var c2)
       (.let_ (op2 (.eq i64) (.var x) (.imm 15)) fun (c3, ()) =>
        .jnz (.var c3) (.ret (.imm 77, ()))
          (.let_ (op2 (.ult i64) (.var x) (.var y)) fun (c4, ()) =>
           .jnz (.var c4)
             (.let_ (op2 (.ne i64) (.var y) (.imm 0)) fun (c5, ()) =>
              .jnz (.var c5) (.ret (.var x, ())) (.ret (.imm 88, ())))
             (.ret (.imm 1, ()))))
       (.ret (.imm 99, ())))
    (.ret (.imm 0, ()))

theorem cmpImpliesChain_pc : Func.pathCondOpt cmpImpliesChain = fun _ _ (x, y, ()) =>
    .let_ (op2 (.ult i64) (.var x) (.imm 10)) fun (c1, ()) =>
    .jnz (.var c1)
      (.let_ (op2 (.ult i64) (.var x) (.var y)) fun (c4, ()) =>
       .jnz (.var c4) (.ret (.var x, ())) (.ret (.imm 1, ())) )
      (.ret (.imm 0, ())) := by
  t_kernel_rfl

theorem cmpImpliesChain_wf : cmpImpliesChain.Wf := by t_wf_reify

/-- Dominating `v <u lim` before `loop1` flows into the loop body and eliminates a re-test. -/
def loopPathFact : Func [i64, i64, i64] [i64] := fun _ _ (i0, v, lim, ()) =>
  .let_ (op2 (.ult i64) (.var v) (.var lim)) fun (ok, ()) =>
  .jnz (.var ok)
    (loop1 (ts := [i64])
      (fun loop (i, ()) =>
        .let_ (op2 (.ult i64) (.var v) (.var lim)) fun (recheck, ()) =>
        .jnz (.var recheck)
          (.let_ (op2 (.ult i64) (.var i) (.var lim)) fun (lt, ()) =>
           .jnz (.var lt)
             (.let_ (op2 (.add i64) (.var i) (.imm 1)) fun (i', ()) =>
              .jump loop (.var i', ()))
             (.ret (.var i, ())))
          (.ret (.imm 999, ())))
      (fun loop => .jump loop (.var i0, ())))
    (.ret (.imm 0, ()))

theorem loopPathFact_pc : Func.pathCondOpt loopPathFact = fun _ _ (i0, v, lim, ()) =>
    .let_ (op2 (.ult i64) (.var v) (.var lim)) fun (ok, ()) =>
    .jnz (.var ok)
      (loop1 (ts := [i64])
        (fun loop (i, ()) =>
          .let_ (op2 (.ult i64) (.var i) (.var lim)) fun (lt, ()) =>
          .jnz (.var lt)
            (.let_ (op2 (.add i64) (.var i) (.imm 1)) fun (i', ()) =>
             .jump loop (.var i', ()))
            (.ret (.var i, ())))
        (fun loop => .jump loop (.var i0, ())))
      (.ret (.imm 0, ())) := by
  t_kernel_rfl

theorem loopPathFact_ct_check : Func.checkTFlat (Func.condThreadLateOpt loopPathFact) = true := by
  t_kernel_rfl

/-- Negative case: `v <u lim1` does not imply `v <u lim2` for unrelated `lim2`. -/
def unrelatedCmpKeep : Func [i64, i64, i64] [i64] := fun _ _ (v, lim1, lim2, ()) =>
  .let_ (op2 (.ult i64) (.var v) (.var lim1)) fun (c1, ()) =>
  .jnz (.var c1)
    (.let_ (op2 (.ult i64) (.var v) (.var lim2)) fun (c2, ()) =>
     .jnz (.var c2) (.ret (.var v, ())) (.ret (.imm 1, ())))
    (.ret (.imm 0, ()))

theorem unrelatedCmpKeep_pc : Func.pathCondOpt unrelatedCmpKeep = unrelatedCmpKeep := by
  t_kernel_rfl

/-! ## 2. Constant-arg branch threading & bool-param block splitting -/

/-- Join block `J(flag, v)` with two constant-bool callers (`true`, `false`) and one dynamic
bool caller (`d`): `condThreadOpt` splits `J` on `flag`, inlines both constant callers directly,
and omits the dispatcher block (rewriting the single dynamic call to `.jnz (.var d)`). -/
def constArgSplit : Func [.bool, i64, i64] [i64] := fun _ _ (d, x, y, ()) =>
  .group (sig := [[.bool, i64]])
    (fun _ => .cons (fun (flag, v, ()) =>
      .jnz (.var flag)
        (.let_ (op2 (.add i64) (.var v) (.imm 1)) fun (r1, ()) => .ret (.var r1, ()))
        (.let_ (op2 (.sub i64) (.var v) (.imm 1)) fun (r2, ()) => .ret (.var r2, ()))) .nil)
    (fun (J, ()) =>
      .let_ (op2 (.eq i64) (.var x) (.imm 0)) fun (isZ, ()) =>
      .jnz (.var isZ)
        (.jump J (.imm true, .var y, ()))
        (.let_ (op2 (.eq i64) (.var x) (.imm 1)) fun (isOne, ()) =>
         .jnz (.var isOne)
           (.jump J (.imm false, .var y, ()))
           (.jump J (.var d, .var y, ()))))

theorem constArgSplit_ct : Func.condThreadOpt constArgSplit = fun _ _ (d, x, y, ()) =>
    .group (sig := [[i64], [i64]])
      (fun _ =>
        .cons (fun (v, ()) =>
          .let_ (op2 (.add i64) (.var v) (.imm 1)) fun (r1, ()) => .ret (.var r1, ()))
        (.cons (fun (v, ()) =>
          .let_ (op2 (.sub i64) (.var v) (.imm 1)) fun (r2, ()) => .ret (.var r2, ())) .nil))
      (fun (JT, JF, ()) =>
        .let_ (op2 (.eq i64) (.var x) (.imm 0)) fun (isZ, ()) =>
        .jnz (.var isZ)
          (.let_ (op2 (.add i64) (.var y) (.imm 1)) fun (r1, ()) => .ret (.var r1, ()))
          (.let_ (op2 (.eq i64) (.var x) (.imm 1)) fun (isOne, ()) =>
           .jnz (.var isOne)
             (.let_ (op2 (.sub i64) (.var y) (.imm 1)) fun (r2, ()) => .ret (.var r2, ()))
             (.jnz (.var d) (.jump JT (.var y, ())) (.jump JF (.var y, ()))))) := by
  t_kernel_rfl

theorem constArgSplit_wf : constArgSplit.Wf := by t_wf_reify
theorem constArgSplit_check : Func.checkTFlat (Func.condThreadLateOpt constArgSplit) = true := by
  t_kernel_rfl

/-- Constant integer block-arg head threading: `.jump J (.imm 0, .var y, ())` evaluates `tag == 0`
at the head of `J` and threads directly into `y + 10`, while the dynamic caller keeps `.jump J`. -/
def constHeadThread : Func [.bool, i64, i64] [i64] := fun _ _ (c, a, y, ()) =>
  .group (sig := [[i64, i64]])
    (fun _ => .cons (fun (tag, x, ()) =>
      .let_ (op2 (.eq i64) (.var tag) (.imm 0)) fun (isZero, ()) =>
      .jnz (.var isZero)
        (.let_ (op2 (.add i64) (.var x) (.imm 10)) fun (r1, ()) => .ret (.var r1, ()))
        (.let_ (op2 (.add i64) (.var x) (.var tag)) fun (s1, ()) =>
         .let_ (op2 (.mul i64) (.var s1) (.imm 3)) fun (s2, ()) =>
         .let_ (op2 (.add i64) (.var s2) (.imm 1)) fun (s3, ()) =>
         .ret (.var s3, ()))) .nil)
    (fun (J, ()) =>
      .jnz (.var c)
        (.jump J (.imm 0, .var y, ()))
        (.jump J (.var a, .var y, ())))

theorem constHeadThread_ct : Func.condThreadOpt constHeadThread = fun _ _ (c, a, y, ()) =>
    .group (sig := [[i64, i64]])
      (fun _ => .cons (fun (tag, x, ()) =>
        .let_ (op2 (.eq i64) (.var tag) (.imm 0)) fun (isZero, ()) =>
        .jnz (.var isZero)
          (.let_ (op2 (.add i64) (.var x) (.imm 10)) fun (r1, ()) => .ret (.var r1, ()))
          (.let_ (op2 (.add i64) (.var x) (.var tag)) fun (s1, ()) =>
           .let_ (op2 (.mul i64) (.var s1) (.imm 3)) fun (s2, ()) =>
           .let_ (op2 (.add i64) (.var s2) (.imm 1)) fun (s3, ()) =>
           .ret (.var s3, ()))) .nil)
      (fun (J, ()) =>
        .jnz (.var c)
          (.let_ (op2 (.add i64) (.var y) (.imm 10)) fun (r1, ()) => .ret (.var r1, ()))
          (.jump J (.var a, .var y, ()))) := by
  t_kernel_rfl

theorem constHeadThread_wf : constHeadThread.Wf := by t_wf_reify
theorem constHeadThread_check :
    Func.checkTFlat (Func.condThreadLateOpt constHeadThread) = true := by
  t_kernel_rfl

/-! ## 3. Formal soundness & `callsOk` instantiations -/

/-- Source specification of `retestLt`: memory unchanged, result is `v + 1` if `v <u curVars` else `0`. -/
theorem retestLt_spec (Γ : Env) (v curVars : BitVec 64) (m : Mem 64) (X : XPost) :
    Func.spec Γ retestLt (v, curVars, ()) m
      (fun (r, ()) m' => m' = m ∧ r = if v < curVars then v + 1 else 0) X := by
  dsimp only [Func.spec, Func.wp, retestLt]
  simp only [wp, Op.wp, op2, vals, Arg.val, OpCode.wp_cmp, OpCode.wp_add, liftCmp, lift2,
    CmpOp.evalBits, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, cast_eq]
  by_cases hlt : v.toNat < curVars.toNat <;>
    simp [BitVec.ult, BitVec.lt_def, hlt]

/-- Contract transported to `Func.condThreadOpt retestLt` via `condThread_ok`. -/
theorem retestLt_ct_spec (Γ : Env) (v curVars : BitVec 64) (m : Mem 64) (X : XPost) :
    Func.spec Γ (Func.condThreadOpt retestLt) (v, curVars, ()) m
      (fun (r, ()) m' => m' = m ∧ r = if v < curVars then v + 1 else 0) X :=
  condThread_ok retestLt_wf (retestLt_spec Γ v curVars m X)

/-- Contract transported to `Func.condThreadLateOpt retestLt`. -/
theorem retestLt_late_spec (Γ : Env) (v curVars : BitVec 64) (m : Mem 64) (X : XPost) :
    Func.spec Γ (Func.condThreadLateOpt retestLt) (v, curVars, ()) m
      (fun (r, ()) m' => m' = m ∧ r = if v < curVars then v + 1 else 0) X :=
  Func.condThreadLateOpt_spec retestLt_wf (retestLt_spec Γ v curVars m X)

/-- Source specification of `constArgSplit`. -/
theorem constArgSplit_spec (Γ : Env) (d : Bool) (x y : BitVec 64) (m : Mem 64) (X : XPost) :
    Func.spec Γ constArgSplit (d, x, y, ()) m
      (fun (r, ()) m' => m' = m ∧
        r = if (if x = 0 then true else if x = 1 then false else d) then y + 1 else y - 1) X := by
  dsimp only [Func.spec, Func.wp, constArgSplit]
  simp only [wp, Op.wp, op2, vals, Arg.val, OpCode.wp_cmp, liftCmp, CmpOp.evalBits,
    Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, cast_eq]
  intro Js hClosed
  have hJ : ∀ b : Bool,
      b = (if x = 0 then true else if x = 1 then false else d) → Js.1 (b, y, ()) m := by
    intro b hb
    apply hClosed.1 (b, y, ()) m
    dsimp only [wp, Op.wp, op2, vals, Arg.val, OpCode.wp_add, OpCode.wp_sub, lift2,
      Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, cast_eq]
    rw [← hb]
    cases b <;> simp
  exact ⟨
    fun hx0 => hJ true (by have h0 := of_decide_eq_true hx0; simp only [h0, ↓reduceIte]),
    fun hx0 => ⟨
      fun hx1 => hJ false (by
        split
        · exact absurd ‹_› (of_decide_eq_false hx0)
        · split
          · rfl
          · exact absurd (of_decide_eq_true hx1) ‹_›),
      fun hx1 => hJ d (by
        split
        · exact absurd ‹_› (of_decide_eq_false hx0)
        · split
          · exact absurd ‹_› (of_decide_eq_false hx1)
          · rfl)⟩⟩

/-- Contract transported to `Func.condThreadOpt constArgSplit` via `condThread_ok`. -/
theorem constArgSplit_ct_spec (Γ : Env) (d : Bool) (x y : BitVec 64) (m : Mem 64) (X : XPost) :
    Func.spec Γ (Func.condThreadOpt constArgSplit) (d, x, y, ()) m
      (fun (r, ()) m' => m' = m ∧
        r = if (if x = 0 then true else if x = 1 then false else d) then y + 1 else y - 1) X :=
  condThread_ok constArgSplit_wf (constArgSplit_spec Γ d x y m X)

theorem constArgSplit_callsOk :
    ((Func.condThreadOpt constArgSplit) (fun _ => Unit) (fun _ => Unit)
      (Tup.units _)).callsOk [] [] :=
  Func.condThreadOpt_callsOk constArgSplit_wf (by
    simp [constArgSplit, Expr.callsOk, Blocks.callsOk])

theorem constHeadThread_late_callsOk :
    ((Func.condThreadLateOpt constHeadThread) (fun _ => Unit) (fun _ => Unit)
      (Tup.units _)).callsOk [] [] :=
  Func.condThreadLateOpt_callsOk constHeadThread_wf (by
    simp [constHeadThread, Expr.callsOk, Blocks.callsOk])

/-! ## 4. Corpus checks (`FullM4` 231 functions & `LratBytes`) -/

/-- Count conditional branches (`jnz`) and total nodes after `Fn.mid LegalTarget.x64` vs
`Func.condThreadLateOpt`, plus `checkTFlat`. -/
def ctStats (f : Fn) : Bool × Nat × Nat × Nat :=
  let mf := f.mid LegalTarget.x64
  let ct := Func.condThreadLateOpt mf.body
  let tf0 := reifyFunc mf.body
  let tf1 := reifyFunc (as := mf.as) ct
  let rec countJnz {rs : List Ty} : TFlat rs → Nat
    | .let_ _ k | .load _ _ k | .store _ _ k | .call _ _ _ k => countJnz k
    | .jnz _ t e => 1 + countJnz t + countJnz e
    | .group bs k =>
      let rec countB : {sig : List (List Ty)} → TBlocks rs sig → Nat
        | _, .nil => 0
        | _, .cons b bs => countJnz b + countB bs
      countB bs + countJnz k
    | _ => 0
  (Func.checkTFlat ct, tflatSize tf0, tflatSize tf1, countJnz tf0 - countJnz tf1)

def m4CtReport : List (String × Bool × Nat × Nat × Nat) :=
  LeanQbe.T.Examples.Kissat.FullM4.m4Fns.map fun f => (f.name, ctStats f)

#eval show IO Unit from do
  let totalJnzDrop := m4CtReport.foldl (fun acc r => acc + r.2.2.2.2) 0
  let touched := m4CtReport.filter fun r => r.2.2.1 != r.2.2.2.1 || r.2.2.2.2 > 0
  IO.println s!"[FullM4] fns={m4CtReport.length} touched={touched.length} jnz_drop={totalJnzDrop}"
  for (name, ok, s0, s1, jd) in touched.take 15 do
    IO.println s!"  {name}: ok={ok} nodes={s0}->{s1} jnz_drop={jd}"

#guard m4CtReport.all (·.2.1)
#guard m4CtReport.foldl (fun acc r => acc + r.2.2.2.2) 0 ≥ 1
#guard LeanQbe.T.Examples.LratBytes.lratBytesModule.fns.all fun f => (ctStats f).1

/-! ## 5. Axiom audit (`⊆ [propext, Classical.choice, Quot.sound]`) -/

#print axioms LeanQbe.T.Func.pathCondOpt_wf
#print axioms LeanQbe.T.Func.pathCondOpt_spec
#print axioms LeanQbe.T.Func.pathCondOpt_callsOk
#print axioms LeanQbe.T.Func.condThreadWithPlan_wf
#print axioms LeanQbe.T.Func.condThreadWithPlan_spec
#print axioms LeanQbe.T.Func.condThreadWithPlan_callsOk
#print axioms LeanQbe.T.Func.condThreadPass_wf
#print axioms LeanQbe.T.Func.condThreadPass_spec
#print axioms LeanQbe.T.Func.condThreadPass_callsOk
#print axioms LeanQbe.T.Func.condThreadOpt_wf
#print axioms LeanQbe.T.Func.condThreadOpt_spec
#print axioms LeanQbe.T.condThread_ok
#print axioms LeanQbe.T.Func.condThreadOpt_callsOk
#print axioms LeanQbe.T.Fn.condThreadOpt_wf
#print axioms LeanQbe.T.Fn.condThreadOpt_spec
#print axioms LeanQbe.T.Fn.condThreadOpt_callsOk
#print axioms LeanQbe.T.Func.condThreadLateOpt_wf
#print axioms LeanQbe.T.Func.condThreadLateOpt_spec
#print axioms LeanQbe.T.Func.condThreadLateOpt_callsOk
#print axioms LeanQbeTest.T.CondThreadOptTest.retestLt_ct_spec
#print axioms LeanQbeTest.T.CondThreadOptTest.constArgSplit_ct_spec
#print axioms LeanQbeTest.T.CondThreadOptTest.constArgSplit_callsOk

end LeanQbeTest.T.CondThreadOptTest
