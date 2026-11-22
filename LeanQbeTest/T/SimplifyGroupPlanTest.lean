module

public import LeanQbe.T.SimplifyGroupPlanLemmas
public import LeanQbe.T.IfOptLemmas
public import LeanQbe.T.Opt
public import LeanQbe.T.LeanLCNF.Lower1
public import LeanQbe.T.LeanLCNF.Demo
public import LeanQbe.T.Examples.LratBytesProg
public import LeanQbe.T.Examples.Kissat.Full
meta import LeanQbe.T.SimplifyGroupPlan
meta import LeanQbe.T.IfOpt
meta import LeanQbe.T.Opt
meta import LeanQbe.T.LeanLCNF.Lower1
meta import LeanQbe.T.LeanLCNF.Demo
meta import LeanQbe.T.Examples.LratBytesProg
meta import LeanQbe.T.Examples.Kissat.Full

/-!
# Tests and Scaling Benchmarks for `LeanQbe.T.SimplifyGroupPlan`

Covers:
1. Exact kernel-checked (`t_kernel_rfl`) unit tests plus cascading edge cases:
   - `IfOpt` + `SimplifyGroupPlan` diamond collapse,
   - Multi-block group collapsing to 1 spliced block,
   - Chained nested tail-jump splice,
   - Inner dead group hiding jumps to an outer group (cascading unwrap & non-recursive splice),
   - Adversarial / invalid `SimpPlan` rejection via `Func.simplifyGroupWithPlan`.
2. Deep synthetic `.group` ladder (`d = 60`) scaling test (`checkTFlat = true`, exact group count).
3. `checkTFlat = true` and sub-second (`< 1s`) benchmark across:
   - All 102 `LeanLCNF.Demo` functions (including 622-deep `RBNode_balance` and 35-deep `run`,
     both unmodified and with deep dead + single-use joins injected at the bottom of the spine),
   - All 6 `LratBytes` functions (raw and post-`earlyCore`),
   - All 166 `Kissat.Full` functions (raw and post-`earlyCore` + `ifOptBits`).
4. `#print axioms` audit (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbeTest.T.SimplifyGroupPlanTest

open LeanQbe.T
open LeanQbe.T.SgpImpl
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat.Full

/-! ## 1. Group depth and count metrics helpers -/

mutual
/-- Maximum `.group` nesting depth of a `TFlat`. -/
def tflatGroupDepth {rs : List Ty} : TFlat rs → Nat
  | .let_ _ k | .load _ _ k | .store _ _ k | .call _ _ _ k => tflatGroupDepth k
  | .jnz _ t e => max (tflatGroupDepth t) (tflatGroupDepth e)
  | .jump _ _ | .ret _ | .exit _ _ | .hlt => 0
  | .group bs k => 1 + max (tblocksGroupDepth bs) (tflatGroupDepth k)

def tblocksGroupDepth {rs : List Ty} : {sig : List (List Ty)} → TBlocks rs sig → Nat
  | _, .nil => 0
  | _, .cons b bs => max (tflatGroupDepth b) (tblocksGroupDepth bs)
end

mutual
/-- Total number of `.group` nodes in a `TFlat`. -/
def tflatGroupCount {rs : List Ty} : TFlat rs → Nat
  | .let_ _ k | .load _ _ k | .store _ _ k | .call _ _ _ k => tflatGroupCount k
  | .jnz _ t e => tflatGroupCount t + tflatGroupCount e
  | .jump _ _ | .ret _ | .exit _ _ | .hlt => 0
  | .group bs k => 1 + tblocksGroupCount bs + tflatGroupCount k

def tblocksGroupCount {rs : List Ty} : {sig : List (List Ty)} → TBlocks rs sig → Nat
  | _, .nil => 0
  | _, .cons b bs => tflatGroupCount b + tblocksGroupCount bs
end

/-- Inject a dead `.group` wrapping a small non-tail single-use `.group` at the first `.ret`
along the deepest `.group` continuation spine, triggering `changed = true` at maximum depth. -/
def injectDeepCliff {rs : List Ty} : TFlat rs → TFlat rs × Bool
  | .let_ op k => let (k', ok) := injectDeepCliff k; (.let_ op k', ok)
  | .load t a k => let (k', ok) := injectDeepCliff k; (.load t a k', ok)
  | .store v a k => let (k', ok) := injectDeepCliff k; (.store v a k', ok)
  | .call f bs args k => let (k', ok) := injectDeepCliff k; (.call f bs args k', ok)
  | .jnz c t e =>
    if tflatGroupDepth t ≥ tflatGroupDepth e then
      let (t', ok) := injectDeepCliff t
      if ok then (.jnz c t' e, true)
      else let (e', ok2) := injectDeepCliff e; (.jnz c t e', ok2)
    else
      let (e', ok) := injectDeepCliff e
      if ok then (.jnz c t e', true)
      else let (t', ok2) := injectDeepCliff t; (.jnz c t' e, ok2)
  | .group bs k =>
    let (k', ok) := injectDeepCliff k
    if ok then (.group bs k', true)
    else
      let (bs', ok2) := injectDeepCliffB bs
      (.group bs' k, ok2)
  | .ret vs =>
    let inner : TFlat rs :=
      .group (sig := [[]]) (.cons (.ret vs) .nil)
        (.let_ (op2 (.add i64) (.imm 1) (.imm 2)) (.jump (ts := []) 0 ()))
    (.group (sig := [[]]) (.cons .hlt .nil) inner, true)
  | t => (t, false)
where
  injectDeepCliffB {rs : List Ty} : {sig : List (List Ty)} → TBlocks rs sig → TBlocks rs sig × Bool
    | _, .nil => (.nil, false)
    | _, .cons b bs =>
      let (b', ok) := injectDeepCliff b
      if ok then (.cons b' bs, true)
      else let (bs', ok2) := injectDeepCliffB bs; (.cons b bs', ok2)

/-! ## 2. Kernel-checked unit & edge-case tests (`t_kernel_rfl`, `Wf`, `spec`) -/

def ifSimpPlan {as rs : List Ty} (f : Func as rs) : Func as rs :=
  Func.simplifyGroupPlan (Func.ifOpt f)

theorem ifSimpPlan_wf {as rs : List Ty} {f : Func as rs} (hf : f.Wf) : (ifSimpPlan f).Wf :=
  Func.simplifyGroupPlan_wf (Func.ifOpt_wf hf)

theorem ifSimpPlan_spec {as rs : List Ty} {f : Func as rs} (hf : f.Wf) {Γ : Env}
    {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Func.spec Γ f xs m Q X) : Func.spec Γ (ifSimpPlan f) xs m Q X :=
  Func.simplifyGroupPlan_spec (Func.ifOpt_wf hf) (Func.ifOpt_spec hf h)

/-- Classic `MB3` diamond lowered by `IfOpt` and collapsed by `SimplifyGroupPlan`. -/
def mb3Diamond : Func [i64, i64, i64] [i64] := fun _ _ (x, y, a, ()) =>
  .let_ (op2 (.cmp .slt i64) (.var x) (.var y)) fun (c, ()) =>
  .group (sig := [[i64]])
    (fun _ => .cons (fun (r, ()) => .ret (.var r, ())) .nil)
    (fun (J, ()) =>
      .jnz (.var c)
        (.let_ (op2 (.add i64) (.var a) (.imm 10)) fun (t, ()) => .jump J (.var t, ()))
        (.let_ (op2 (.sub i64) (.var a) (.imm 10)) fun (e, ()) => .jump J (.var e, ())))

theorem mb3Diamond_out : ifSimpPlan mb3Diamond = fun _ _ (x, y, a, ()) =>
    .let_ (op2 (.cmp .slt i64) (.var x) (.var y)) fun (c, ()) =>
    .let_ (op2 (.add i64) (.var a) (.imm 10)) fun (t, ()) =>
    .let_ (op2 (.sub i64) (.var a) (.imm 10)) fun (e, ()) =>
    .let_ (op3 (.select i64) (.var c) (.var t) (.var e)) fun (s, ()) =>
    .ret (.var s, ()) := by
  t_kernel_rfl

theorem mb3Diamond_wf : mb3Diamond.Wf := by t_wf_reify

theorem mb3Diamond_spec (Γ : Env) (x y a : BitVec 64) (m : Mem 64) :
    Func.spec Γ (ifSimpPlan mb3Diamond) (x, y, a, ()) m
      (fun (r, ()) m' =>
        r = (if BitVec.slt x y then a + 10#64 else a - 10#64) ∧ m' = m)
      (fun _ _ _ _ => False) := by
  apply ifSimpPlan_spec mb3Diamond_wf
  dsimp only [Func.spec, Func.wp, mb3Diamond]
  simp only [wp, Op.wp, OpCode.wp, op2, vals, Arg.val, liftCmp, CmpOp.evalBits, i64, Closed]
  intro ⟨J, ⟨⟩⟩ hJ
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact hJ.1 (a + 10#64, ()) m ⟨by simp [h], rfl⟩
  · exact hJ.1 (a - 10#64, ()) m ⟨by simp [h], rfl⟩

/-- Multi-block group where only the middle block (`idx = 1`) is reachable and small 1-use
collapses completely via `.splice 1`. -/
def multiBlockSpliceMidProg : Func [i64] [i64] := fun _ _ (x, ()) =>
  .group (sig := [[i64], [i64], [i64]])
    (fun (b0, _, b2, ()) =>
      .cons (fun (a, ()) => .jump b0 (.var a, ()))
      (.cons (fun (m, ()) => .let_ (op2 (.mul i64) (.var m) (.imm 7)) fun (r, ()) =>
        .ret (.var r, ()))
      (.cons (fun (c, ()) => .jump b2 (.var c, ()))
      .nil)))
    (fun (_, b1, _, ()) =>
      .let_ (op2 (.add i64) (.var x) (.imm 3)) fun (y, ()) =>
      .jump b1 (.var y, ()))

theorem multiBlockSpliceMidProg_out : Func.simplifyGroupPlan multiBlockSpliceMidProg =
    fun _ _ (x, ()) =>
      .let_ (op2 (.add i64) (.var x) (.imm 3)) fun (y, ()) =>
      .let_ (op2 (.mul i64) (.var y) (.imm 7)) fun (r, ()) =>
      .ret (.var r, ()) := by
  t_kernel_rfl

/-- Chained nested tail-jump splice: inner splice exposes outer tail jump. -/
def chainedTailSpliceProg : Func [i64] [i64] := fun _ _ (x, ()) =>
  .group (sig := [[i64]])
    (fun _ =>
      .cons (fun (a, ()) =>
        .let_ (op2 (.add i64) (.var a) (.imm 100)) fun (r, ()) => .ret (.var r, ())) .nil)
    (fun (outer, ()) =>
      .group (sig := [[i64]])
        (fun _ => .cons (fun (b, ()) => .jump outer (.var b, ())) .nil)
        (fun (inner, ()) => .jump inner (.var x, ())))

theorem chainedTailSpliceProg_out : Func.simplifyGroupPlan chainedTailSpliceProg =
    fun _ _ (x, ()) =>
      .let_ (op2 (.add i64) (.var x) (.imm 100)) fun (r, ()) => .ret (.var r, ()) := by
  t_kernel_rfl

/-- Inner dead group inside `b_outer` jumps to `L_outer`: after inner unwrap, `L_outer` becomes
non-recursive and splices cleanly! -/
def deadInnerHidesLoopProg : Func [i64] [i64] := fun _ _ (x, ()) =>
  .group (sig := [[i64]])
    (fun (outer, ()) =>
      .cons (fun (a, ()) =>
        .group (sig := [[i64]])
          (fun _ => .cons (fun (u, ()) => .jump outer (.var u, ())) .nil)
          (fun _ => .let_ (op2 (.add i64) (.var a) (.imm 4)) fun (r, ()) => .ret (.var r, ())))
        .nil)
    (fun (outer, ()) =>
      .let_ (op2 (.mul i64) (.var x) (.imm 2)) fun (y, ()) => .jump outer (.var y, ()))

theorem deadInnerHidesLoopProg_out : Func.simplifyGroupPlan deadInnerHidesLoopProg =
    fun _ _ (x, ()) =>
      .let_ (op2 (.mul i64) (.var x) (.imm 2)) fun (y, ()) =>
      .let_ (op2 (.add i64) (.var y) (.imm 4)) fun (r, ()) =>
      .ret (.var r, ()) := by
  t_kernel_rfl

/-- Self-recursive single-block loop is preserved untouched. -/
def selfLoopProg : Func [i64] [i64] := fun _ _ (n, ()) =>
  .group (sig := [[i64]])
    (fun (loop, ()) =>
      .cons (fun (i, ()) =>
        .let_ (op2 (.cmp .eq i64) (.var i) (.imm 0)) fun (done, ()) =>
        .jnz (.var done) (.ret (.var i, ()))
          (.let_ (op2 (.sub i64) (.var i) (.imm 1)) fun (i', ()) => .jump loop (.var i', ())))
        .nil)
    (fun (loop, ()) => .jump loop (.var n, ()))

theorem selfLoopProg_unchanged : Func.simplifyGroupPlan selfLoopProg = selfLoopProg := by
  t_kernel_rfl

/-- Adversarial invalid `SimpPlan` (trying to `.unwrap` or `.splice 0` a live self-loop) is
rejected by `validatePlan` and safely falls back to `selfLoopProg`. -/
def badUnwrapPlan : SimpPlan := .group .unwrap (.cons .leaf .nil) .leaf
def badSpliceLoopPlan : SimpPlan :=
  .group (.splice 0)
    (.cons (.node1 (.node2 .leaf (.node1 .leaf))) .nil)
    .leaf

theorem badUnwrap_rejected :
    Func.simplifyGroupWithPlan badUnwrapPlan selfLoopProg = selfLoopProg := by
  t_kernel_rfl

theorem badSpliceLoop_rejected :
    Func.simplifyGroupWithPlan badSpliceLoopPlan selfLoopProg = selfLoopProg := by
  t_kernel_rfl

/-! ## 3. Deep synthetic `.group` ladder (`d = 60`) -/

/-- Builds a depth-`n` right-nested `.group` ladder alternating kept 2-use joins, dead groups,
small single-use joins, and tail-jump wrappers (`4 * n` total groups, collapsing to `n`). -/
def mkDeepLadder : Nat → TFlat [i64]
  | 0 => .ret (.var 0, ())
  | n + 1 =>
    let rest := mkDeepLadder n
    let singleUse : TFlat [i64] :=
      .group (sig := [[i64]])
        (.cons (.let_ (op2 (.add i64) (.var 0) (.imm 1))
          (.jump (ts := [i64]) 3 (.var 0, ()))) .nil)
        (.let_ (op2 (.add i64) (.var 0) (.imm 2)) (.jump (ts := [i64]) 0 (.var 0, ())))
    let deadGrp : TFlat [i64] :=
      .group (sig := [[i64]]) (.cons .hlt .nil) singleUse
    .group (sig := [[i64]])
      (.cons rest .nil)
      (.jnz (.imm true)
        (.group (sig := [[i64]]) (.cons deadGrp .nil) (.jump (ts := [i64]) 0 (.var 0, ())))
        (.jump (ts := [i64]) 0 (.var 0, ())))

def deepLadderFn (n : Nat) : Func [i64] [i64] :=
  denoteFunc (mkDeepLadder n)

#guard (Func.simplifyGroupPlan (deepLadderFn 20)).checkTFlat == true
#guard tflatGroupCount (reifyFunc (deepLadderFn 20)) == 80
#guard tflatGroupCount (reifyFunc (Func.simplifyGroupPlan (deepLadderFn 20))) == 20
#guard (Func.simplifyGroupPlan (deepLadderFn 60)).checkTFlat == true
#guard tflatGroupCount (reifyFunc (deepLadderFn 60)) == 240
#guard tflatGroupCount (reifyFunc (Func.simplifyGroupPlan (deepLadderFn 60))) == 60

/-! ## 4. Real-corpus soundness `#guard`s (`LratBytes`, `LeanLCNF.Demo`, `Kissat.Full`) -/

def demoTfs : List LeanQbe.T.Frontend.C0.TFlatFn :=
  (LeanLCNF.lowerModule LeanLCNF.Demo.lcnfProgram).toOption.getD []

def demoFns : List Fn := LeanLRC.tflatFnsToFns demoTfs

-- LratBytes: all 6 functions (raw + post-`earlyCore`)
#guard lratBytesFns.length == 6
#guard lratBytesFns.all fun fn => (Func.simplifyGroupPlan fn.body).checkTFlat
#guard lratBytesFns.all fun fn => (Func.simplifyGroupPlan (Func.earlyCore fn.body)).checkTFlat

-- LeanLCNF.Demo: all 102 functions (raw + post-`earlyCore`)
#guard demoFns.length == 102
#guard demoFns.all fun fn => (Func.simplifyGroupPlan fn.body).checkTFlat
#guard demoFns.all fun fn => (Func.simplifyGroupPlan (Func.earlyCore fn.body)).checkTFlat

-- Cliff stress test on 622-deep `RBNode_balance` and 35-deep `run`!
def cliffCheckFn (suffix : String) : Bool :=
  match demoFns.find? (fun fn => fn.name.endsWith suffix) with
  | none => false
  | some fn =>
    let tf0 := reifyFunc fn.body
    let g0 := tflatGroupCount tf0
    let (tfInj, ok) := injectDeepCliff tf0
    let fInj : Func fn.as fn.rs := denoteFunc tfInj
    let fSimp := Func.simplifyGroupPlan fInj
    let tfSimp := reifyFunc fSimp
    ok && fSimp.checkTFlat && tflatGroupCount tfInj == g0 + 2 && tflatGroupCount tfSimp == g0

#guard cliffCheckFn "RBNode_balance"
#guard cliffCheckFn "_run"

-- Kissat.Full: all 166 functions (`checkTFlat`)
#guard fullFns.length == 166
#guard fullFns.all fun fn => (Func.simplifyGroupPlan fn.body).checkTFlat

/-! ## 5. Axiom audits -/

#print axioms LeanQbe.T.Func.simplifyGroupWithPlan_wf
#print axioms LeanQbe.T.Func.simplifyGroupWithPlan_spec
#print axioms LeanQbe.T.Func.simplifyGroupPlan_wf
#print axioms LeanQbe.T.Func.simplifyGroupPlan_spec
#print axioms mb3Diamond_spec

/-! ## 6. Wall-clock benchmark (`main`) -/

/-- Pre-reified function entry (`Type 0`) for isolating `Func.simplifyGroupPlan` timing. -/
structure ReifiedEntry : Type where
  name : Sym
  as : List Ty
  rs : List Ty
  tf : TFlat rs

def reifyEntry (fn : Fn) : ReifiedEntry :=
  ⟨fn.name, fn.as, fn.rs, reifyFunc fn.body⟩

def runBench : IO Unit := do
  -- 1. LeanLCNF.Demo (all 102 fns: raw + cliff-injected RBNode_balance & run)
  let lcnfReified := demoFns.map reifyEntry
  let t0 ← IO.monoMsNow
  let mut lcnfOut : Array ReifiedEntry := #[]
  for r in lcnfReified do
    let fp : Func r.as r.rs := Func.simplifyGroupPlan (denoteFunc r.tf)
    lcnfOut := lcnfOut.push ⟨r.name, r.as, r.rs, reifyFunc fp⟩
  let t1 ← IO.monoMsNow
  let mut lcnfOk := 0
  let mut lcnfGroupsBefore := 0
  let mut lcnfGroupsAfter := 0
  for (r0, r1) in lcnfReified.zip lcnfOut.toList do
    lcnfGroupsBefore := lcnfGroupsBefore + tflatGroupCount r0.tf
    lcnfGroupsAfter := lcnfGroupsAfter + tflatGroupCount r1.tf
    if r1.tf.wfCheck (pushTypes r1.as []) [] then lcnfOk := lcnfOk + 1

  -- Cliff test on RBNode_balance (631 groups) and run (38 groups), injecting dead + 1-use joins
  let mut cliffMs := 0
  for suf in ["RBNode_balance", "_run"] do
    match demoFns.find? (fun fn => fn.name.endsWith suf) with
    | none => throw (IO.userError s!"missing LeanLCNF fn {suf}")
    | some fn =>
      let tf0 := reifyFunc fn.body
      let d0 := tflatGroupDepth tf0
      let g0 := tflatGroupCount tf0
      let (tfInj, ok) := injectDeepCliff tf0
      if !ok then throw (IO.userError s!"injectDeepCliff failed on {fn.name}")
      let fInj : Func fn.as fn.rs := denoteFunc tfInj
      let ts0 ← IO.monoMsNow
      let fp : Func fn.as fn.rs := Func.simplifyGroupPlan fInj
      let tfp := reifyFunc fp
      let ts1 ← IO.monoMsNow
      cliffMs := cliffMs + (ts1 - ts0)
      let gp := tflatGroupCount tfp
      if !tfp.wfCheck (pushTypes fn.as []) [] || gp != g0 then
        throw (IO.userError s!"cliff check failed on {fn.name}: g0={g0} gp={gp}")
      IO.println s!"  cliff {fn.name}: depth={d0} groups {g0}+2 -> {gp} in {ts1 - ts0} ms"

  -- 2. LratBytes (all 6 fns)
  let lratReified := lratBytesFns.map reifyEntry
  let tLrat0 ← IO.monoMsNow
  let mut lratOut : Array ReifiedEntry := #[]
  for r in lratReified do
    let fp : Func r.as r.rs := Func.simplifyGroupPlan (denoteFunc r.tf)
    lratOut := lratOut.push ⟨r.name, r.as, r.rs, reifyFunc fp⟩
  let tLrat1 ← IO.monoMsNow
  let mut lratOk := 0
  for r in lratOut do
    if r.tf.wfCheck (pushTypes r.as []) [] then lratOk := lratOk + 1

  -- 3. Kissat.Full (all 166 fns: raw + post-earlyCore/ifOptBits)
  let kissatRaw := fullFns.map reifyEntry
  let tKis0 ← IO.monoMsNow
  let mut kissatOut : Array ReifiedEntry := #[]
  for r in kissatRaw do
    let fp : Func r.as r.rs := Func.simplifyGroupPlan (denoteFunc r.tf)
    kissatOut := kissatOut.push ⟨r.name, r.as, r.rs, reifyFunc fp⟩
  let tKis1 ← IO.monoMsNow
  let mut kisOk := 0
  let mut kisGroupsBefore := 0
  let mut kisGroupsAfter := 0
  for (r0, r1) in kissatRaw.zip kissatOut.toList do
    kisGroupsBefore := kisGroupsBefore + tflatGroupCount r0.tf
    kisGroupsAfter := kisGroupsAfter + tflatGroupCount r1.tf
    if r1.tf.wfCheck (pushTypes r1.as []) [] then kisOk := kisOk + 1

  -- Post-ifOptBits Kissat.Full (exercises real join-group elimination across all 166 fns)
  let kissatIfOpt := kissatRaw.map fun (r : ReifiedEntry) =>
    let f0 : Func r.as r.rs := denoteFunc r.tf
    (⟨r.name, r.as, r.rs, reifyFunc (Func.ifOptBits (Func.earlyCore f0))⟩ : ReifiedEntry)
  let tKisOpt0 ← IO.monoMsNow
  let mut kissatOptOut : Array ReifiedEntry := #[]
  for r in kissatIfOpt do
    let fp : Func r.as r.rs := Func.simplifyGroupPlan (denoteFunc r.tf)
    kissatOptOut := kissatOptOut.push ⟨r.name, r.as, r.rs, reifyFunc fp⟩
  let tKisOpt1 ← IO.monoMsNow
  let mut kisOptOk := 0
  let mut kisOptBefore := 0
  let mut kisOptAfter := 0
  for (r0, r1) in kissatIfOpt.zip kissatOptOut.toList do
    kisOptBefore := kisOptBefore + tflatGroupCount r0.tf
    kisOptAfter := kisOptAfter + tflatGroupCount r1.tf
    if r1.tf.wfCheck (pushTypes r1.as []) [] then kisOptOk := kisOptOk + 1

  let lcnfMs := t1 - t0
  let lratMs := tLrat1 - tLrat0
  let kisMs := tKis1 - tKis0
  let kisOptMs := tKisOpt1 - tKisOpt0
  let totalMs := lcnfMs + cliffMs + lratMs + kisMs
  IO.println (s!"LeanLCNF.Demo (102 fns): {lcnfMs} ms, ok={lcnfOk}/102, " ++
    s!"groups={lcnfGroupsBefore}->{lcnfGroupsAfter}")
  IO.println s!"LratBytes (6 fns):       {lratMs} ms, ok={lratOk}/6"
  IO.println (s!"Kissat.Full raw (166):   {kisMs} ms, ok={kisOk}/166, " ++
    s!"groups={kisGroupsBefore}->{kisGroupsAfter}")
  IO.println (s!"Kissat.Full opt (166):   {kisOptMs} ms, ok={kisOptOk}/166, " ++
    s!"groups={kisOptBefore}->{kisOptAfter}")
  IO.println s!"TOTAL simplifyGroupPlan (274 fns + cliff): {totalMs} ms"
  if lcnfMs ≥ 1000 || cliffMs ≥ 1000 || lratMs ≥ 1000 || kisMs ≥ 1000 || kisOptMs ≥ 1000 then
    throw (IO.userError s!"PER-CORPUS SPEED REGRESSION: {lcnfMs}/{cliffMs}/{lratMs}/{kisMs} ms")

end LeanQbeTest.T.SimplifyGroupPlanTest

public def main : IO Unit :=
  LeanQbeTest.T.SimplifyGroupPlanTest.runBench
