module

import LeanQbe.T.OptPolicy
import LeanQbe.T.MainLateInline
import LeanQbe.T.SpillSnippet
import LeanQbe.T.SnippetCheck
import LeanQbe.T.Examples.Kissat.Dimacs
import LeanQbe.T.Examples.Kissat.Plain1
import LeanQbe.T.FlatLemmas
import LeanQbe.T.MainLemmas

/-!
# Phase 1 Target-Generic Predictable Codegen Tests

Arch-free tests covering:
1. `SnippetOptPolicy` (`noIfOpt`, `noRotate`, `noPeel`, `noMergeRets`, `noNormCmpImm`,
   `noHoistOut`), `Func.constFoldNoCmp` preserving `.sgt`, `Fn.midPolicy_default_eq`, and
   `Fn.midPolicy_spec`.
2. `MainLateInline` (`makeLateInlinePolicy`, `Module.midThenLateInline`): optimizing outer caller
   while preserving late-inlined snippet branches inside `.group` and keeping cold callees
   out-of-line.
3. Kissat inner loop structural audits (`kissat_is_ws`, `kissat_is_digit`, `plain_red_less`) and
   generic IP-attributed `@predictable` diagnostic theorems (`call_in_snippet`, `if_conv`,
   `interior_spill`) proved universally over arbitrary `(I : Isa)`.
4. Standard-axiom (`std3`) `#print axioms` audit.
-/

set_option autoImplicit false

section

namespace LeanQbeTest.T.SnippetPhase1Test

open LeanQbe.T LeanQbe.T.SnippetCheck LeanQbe.T.SpillSnippet

/-! ## 1. `SnippetOptPolicy` & `Func.constFoldNoCmp` checks -/

def sgt0Fn : Fn :=
  ⟨"sgt0", [i64], [i64], fun _ _ (x, ()) =>
    .let_ ⟨.cmp .sgt i64 .bool rfl, (.var x, .imm 0#64, ())⟩ fun (c, ()) =>
    .jnz (.var c) (.ret (.var x, ())) (.ret (.imm 0#64, ()))⟩

def minFn : Fn :=
  ⟨"min_fn", [i64, i64], [i64], fun _ _ (a, b, ()) =>
    .group (sig := [[i64]])
      (fun _ => .cons (ts := [i64]) (fun (r, ()) => .ret (.var r, ())) .nil)
      (fun (j, ()) =>
        .let_ ⟨.cmp .slt i64 .bool rfl, (.var a, .var b, ())⟩ fun (c, ()) =>
        .jnz (.var c) (.jump j (.var a, ())) (.jump j (.var b, ())))⟩

def branchyFn : Fn :=
  ⟨"branchy", [i64, i64], [i64], fun _ _ (a, b, ()) =>
    .let_ ⟨.cmp .slt i64 .bool rfl, (.var a, .var b, ())⟩ fun (c, ()) =>
    .jnz (.var c)
      (.let_ ⟨.add i64, (.var a, .imm 1#64, ())⟩ fun (r1, ()) => .ret (.var r1, ()))
      (.let_ ⟨.add i64, (.var b, .imm 2#64, ())⟩ fun (r2, ()) => .ret (.var r2, ()))⟩

def isCmpOpCode (co : CmpOp) : {as bs : List Ty} → OpCode as bs → Bool
  | _, _, .cmp co' _ _ _ => co' == co
  | _, _, _ => false

def isSelectOpCode : {as bs : List Ty} → OpCode as bs → Bool
  | _, _, .select _ => true
  | _, _, _ => false

mutual
def hasCmpOp (co : CmpOp) {rs : List Ty} : TFlat rs → Bool
  | .let_ op k => isCmpOpCode co op.code || hasCmpOp co k
  | .load _ _ k | .store _ _ k | .call _ _ _ k => hasCmpOp co k
  | .jnz _ t e => hasCmpOp co t || hasCmpOp co e
  | .group bs k => hasCmpBlocks co bs || hasCmpOp co k
  | _ => false

def hasCmpBlocks (co : CmpOp) {rs : List Ty} : {sig : List (List Ty)} → TBlocks rs sig → Bool
  | _, .nil => false
  | _, .cons b bs => hasCmpOp co b || hasCmpBlocks co bs
end

mutual
def hasSelectOp {rs : List Ty} : TFlat rs → Bool
  | .let_ op k => isSelectOpCode op.code || hasSelectOp k
  | .load _ _ k | .store _ _ k | .call _ _ _ k => hasSelectOp k
  | .jnz _ t e => hasSelectOp t || hasSelectOp e
  | .group bs k => hasSelectBlocks bs || hasSelectOp k
  | _ => false

def hasSelectBlocks {rs : List Ty} : {sig : List (List Ty)} → TBlocks rs sig → Bool
  | _, .nil => false
  | _, .cons b bs => hasSelectOp b || hasSelectBlocks bs
end

def funcTFlat (fn : Fn) : TFlat fn.rs :=
  toTFlat (fn.body K KL (Tup.levels fn.as 0)) fn.as.length 0

theorem constFoldNoCmp_keeps_sgt :
    hasCmpOp .sgt (funcTFlat { sgt0Fn with body := Func.constFoldNoCmp sgt0Fn.body }) = true := by
  decide

theorem fold_normalizes_sgt_to_sge :
    hasCmpOp .sgt (funcTFlat { sgt0Fn with body := Func.fold sgt0Fn.body }) = false ∧
      hasCmpOp .sge (funcTFlat { sgt0Fn with body := Func.fold sgt0Fn.body }) = true := by
  decide

theorem default_earlyOpt_uses_select :
    hasSelectOp (funcTFlat { minFn with body := Func.earlyOpt minFn.body }) = true := by
  t_kernel_rfl

theorem predictable_earlyOpt_avoids_select :
    hasSelectOp (funcTFlat
      { minFn with body := Func.earlyOptPolicy SnippetOptPolicy.predictable minFn.body }) =
      false := by
  t_kernel_rfl

theorem sgt0Fn_wf : sgt0Fn.Wf := by t_wf_reify
theorem branchyFn_wf : branchyFn.Wf := by t_wf_reify

theorem branchyFn_pred_wp (Γ : Env) (a b : BitVec 64) (m : Mem 64) (Q : Post [i64]) (X : XPost)
    (h : Q (if a.slt b then a + 1#64 else b + 2#64, ()) m) :
    Func.spec (legalEnv LegalTarget.aarch64 Γ)
      (branchyFn.midPolicy LegalTarget.aarch64 .predictable).body
      (encodeTup LegalTarget.aarch64 [i64, i64] (a, b, ())) m Q X := by
  refine Fn.midPolicy_spec (lt := LegalTarget.aarch64) (pol := .predictable) branchyFn_wf ?_
    Γ (P := Q) (E := fun _ _ _ _ => False) rfl ?_ ?_ ?_
  · t_kernel_rfl
  · rintro r m₁ ⟨⟨x, ⟨⟩⟩, rfl, hr⟩; exact hr
  · rintro _ _ _ _ ⟨_, _, _, _, _, ⟨⟩⟩
  · dsimp only [Func.wp, branchyFn, wp, Op.wp, OpCode.wp, op2, lift2, Ty.hasFloat, Arg.val, vals]
    change (a.slt b = true → _) ∧ (a.slt b = false → _)
    constructor
    · intro ht
      simp only [wp, Op.wp, OpCode.wp, lift2, Ty.hasFloat, Arg.val, vals]
      simpa [ht] using h
    · intro hf
      simp only [wp, Op.wp, OpCode.wp, lift2, Ty.hasFloat, Arg.val, vals]
      simpa [hf] using h

/-! ## 2. `MainLateInline` structural preservation & selective inlining -/

def fnCold : Fn :=
  ⟨"cold_helper", [i64], [i64], fun _ _ (x, ()) =>
    .let_ ⟨.add i64, (.var x, .imm 100#64, ())⟩ fun (r, ()) => .ret (.var r, ())⟩

def fnOuter : Fn :=
  ⟨"outer", [i64, i64], [i64], fun _ _ (x, k, ()) =>
    .call "branchy" (as := [i64, i64]) (bs := [i64]) (.var x, .var k, ()) fun (r, ()) =>
    .let_ ⟨.cmp .eq i64 .bool rfl, (.var k, .imm 0#64, ())⟩ fun (isCold, ()) =>
    .group (sig := [[i64]])
      (fun _ => .cons (ts := [i64]) (fun (res, ()) => .ret (.var res, ())) .nil)
      (fun (joinL, ()) =>
        .jnz (.var isCold)
          (.call "cold_helper" (as := [i64]) (bs := [i64]) (.var r, ()) fun (c, ()) =>
            .jump joinL (.var c, ()))
          (.jump joinL (.var r, ())))⟩

def phase1Mod : Module :=
  { fns := [fnCold, branchyFn, fnOuter] }

def latePolicyOf (s : Sym) : SnippetOptPolicy :=
  if s == "branchy" then .predictable else .default

def lateInlinedMod : Module :=
  phase1Mod.midThenLateInline LegalTarget.aarch64 latePolicyOf
    (lateInlineSnippetsPolicy ["branchy"])

def dummyFn : Fn := ⟨"", [], [], fun _ _ _ => .hlt⟩

def lateOuterFn : Fn :=
  (lateInlinedMod.fns.find? (·.name == "outer")).getD dummyFn

theorem lateOuter_calls_cold_only :
    lateOuterFn.checkCallsOk [("cold_helper", [i64], [i64])] [] = true := by
  t_kernel_rfl

theorem lateOuter_not_call_free :
    lateOuterFn.checkCallsOk [] [] = false := by
  t_kernel_rfl

theorem lateOuter_no_select :
    hasSelectOp (funcTFlat lateOuterFn) = false := by
  t_kernel_rfl

theorem lateInlinedMod_names_eq :
    lateInlinedMod.names = phase1Mod.names := by
  t_kernel_rfl

/-! ## 3. Kissat inner loop checks & fail-loud `SnippetDiag` checks -/

def treeWs : Live.Tree :=
  (Live.Tree.ofFn LeanQbe.T.Examples.Kissat.kissat_is_ws).1

def treeDigit : Live.Tree :=
  (Live.Tree.ofFn LeanQbe.T.Examples.Kissat.kissat_is_digit).1

def plainRedLessFn : Fn :=
  ⟨"plain_red_less", [i64, i32, i32], [.bool],
    LeanQbe.T.Examples.Kissat.Plain.plain_red_less_body⟩

def treeRedLess : Live.Tree :=
  (Live.Tree.ofFn plainRedLessFn).1

theorem kissat_ws_call_free : treeHasCall treeWs = false := by t_kernel_rfl
theorem kissat_digit_call_free : treeHasCall treeDigit = false := by t_kernel_rfl
theorem kissat_red_less_call_free : treeHasCall treeRedLess = false := by t_kernel_rfl
theorem kissat_red_less_ops_gt_10 : Nat.blt 10 (countTreeIrOps treeRedLess) = true := by
  t_kernel_rfl

def callSnipTree : Live.Tree :=
  (Live.Tree.ofFn fnOuter).1

def selSnipFn : Fn :=
  ⟨"sel_snip", [i64, i64], [i64], fun _ _ (a, b, ()) =>
    .let_ ⟨.cmp .slt i64 .bool rfl, (.var a, .var b, ())⟩ fun (c, ()) =>
    .let_ ⟨.select i64, (.var c, .var a, .var b, ())⟩ fun (r, ()) =>
    .ret (.var r, ())⟩

def selectSnipTree : Live.Tree :=
  (Live.Tree.ofFn selSnipFn).1

theorem rejects_call (I : Isa) :
    let hEmpty : I.Hints :=
      { dest := .empty, entry := .empty, pre := .empty, variant := .empty,
        elide := .empty, invertJnz := .empty, nslots := 0, saved := [] }
    let reg : RegionFind :=
      { startIp := 0, exitIp := some 1, exitNextIp := 2, calleeTree := callSnipTree,
        contLid := 0, contPlocVars := [], contLiveOut := [],
        calleeIps := [0, 1], calleeNvs := [], calleeLids := [] }
    (match auditRegionHints I hEmpty reg (SnippetBudget.predictable "outer") with
      | .error ds => ds.any (·.kind == "call_in_snippet")
      | .ok _ => false) = true := by
  rfl

theorem rejects_ifconv (I : Isa) :
    let hEmpty : I.Hints :=
      { dest := .empty, entry := .empty, pre := .empty, variant := .empty,
        elide := .empty, invertJnz := .empty, nslots := 0, saved := [] }
    let reg : RegionFind :=
      { startIp := 0, exitIp := some 1, exitNextIp := 2, calleeTree := selectSnipTree,
        contLid := 0, contPlocVars := [], contLiveOut := [],
        calleeIps := [0, 1], calleeNvs := [], calleeLids := [] }
    (match auditRegionHints I hEmpty reg (SnippetBudget.predictable "branchy") with
      | .error ds => ds.any (·.kind == "if_conv")
      | .ok _ => false) = true := by
  rfl

theorem auditRegionHints_rejects_interior_spill (I : Isa) (r : I.Reg) :
    let preSp := Trie.insert .empty 1 { clearFlags := false, moves := [Move.st 0 r] }
    let hSpill : I.Hints :=
      { dest := .empty, entry := .empty, pre := preSp, variant := .empty,
        elide := .empty, invertJnz := .empty, nslots := 1, saved := [] }
    let reg : RegionFind :=
      { startIp := 0, exitIp := some 1, exitNextIp := 2, calleeTree := treeWs,
        contLid := 0, contPlocVars := [], contLiveOut := [],
        calleeIps := [0, 1], calleeNvs := [], calleeLids := [] }
    (match auditRegionHints I hSpill reg (SnippetBudget.predictable "kissat_is_ws") with
      | .error ds => ds.any (fun d => d.kind == "interior_spill" && d.ip? == some 1)
      | .ok _ => false) = true := by
  rfl

/-! ## 4. Standard-axiom (`std3`) audit -/

#print axioms LeanQbe.T.Func.constFoldNoCmp_wf
#print axioms LeanQbe.T.Func.constFoldNoCmp_spec
#print axioms LeanQbe.T.Fn.midPolicy_wf
#print axioms LeanQbe.T.Fn.midPolicy_spec
#print axioms LeanQbe.T.Fn.midPolicy_default_eq
#print axioms LeanQbe.T.Module.midThenLateInline_fns_sigs
#print axioms LeanQbe.T.compileDirectModule_sound
#print axioms LeanQbe.T.compileLateInlined_sound
#print axioms branchyFn_pred_wp
#print axioms rejects_call
#print axioms rejects_ifconv

end LeanQbeTest.T.SnippetPhase1Test