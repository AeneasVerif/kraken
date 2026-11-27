module

public import LeanQbe.T.Arm64.Snippet
public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.MainLateInline
public import LeanQbe.T.Logic.MemLemmas
import all Kraken.Separation
public import LeanQbe.T.Notation
public import LeanQbe.T.NotationSugar
public import LeanQbe.T.Examples.Kissat.Dimacs
public import LeanQbe.T.Examples.Kissat.FullM7HotTernary
import LeanQbe.T.FlatLemmas
public meta import Lean
public meta import LeanQbe.T.OptPolicy
public meta import LeanQbe.T.Main
public meta import LeanQbe.T.MainLateInline
public meta import LeanQbe.T.Spill
public meta import LeanQbe.T.SpillSnippet
public meta import LeanQbe.T.SnippetCheck
public meta import LeanQbe.T.Arm64.Targ
public meta import LeanQbe.T.Arm64.TargLemmas
public meta import LeanQbe.T.Arm64.Snippet
public meta import LeanQbe.T.MainSplice
public meta import LeanQbe.T.MainLinkSplice
public meta import LeanQbe.T.Notation
public meta import LeanQbe.T.NotationSugar
public meta import LeanQbe.T.Examples.Kissat.Dimacs
public meta import LeanQbe.T.Examples.Kissat.FullM7HotTernary

/-!
# Phase 1 AAPCS64 Arm64 Predictable Codegen, `AsmIso`, & Certified Late-Inline Tests

Tests end-to-end on `armTarget` (`armLegalTarget`, `armLayout`, `armInit`):
1. Phase 0's 10 expressible call-free V1 Arm64 snippets (`sum`, `cmp3`, `tworet`, `setlt`,
   `minsel`, `ld`, `madd`, `andshift`, `divmod`, `add128`) + 5 Kissat hot inner kernels +
   `kissat_is_ws` + `kissat_is_digit` (`Arm64.liftSnippet` `AsmIso` PASS on 7 Tier-1/2 V1
   snippets + 28-live-through & cold-call outer harness via real post-`mid` `lateInline` +
   `splice_snippet_hints`, confirming **`inSp = 0`** and `@predictable` `checkRegaAndBudget`
   PASS on all 17 call-free snippets).
2. Fail-loud negative `@predictable` checks (`callinc` rejected with `snippet_contains_call` and
   `call_in_snippet`).
3. Standalone Kissat `m7HasTernaryFn` (`full_has_ternary`) lowering under `Fn.midPolicy`.
4. Certified 3-function `certModArm64` (`cold_helper`, `k_ws_check`, 28-live-through `caller28`)
   compiled via `compileLateInlined` + `splice_snippet_hints`, verifying `inSp = 0`,
   `compileLateInlined_sound` `armTarget.FnSpec`, closed `arm64_of_returns` `Eventually`, and
   strictly `std3` axioms (`0` `sorry`).
-/

set_option autoImplicit false

section

namespace LeanQbeTest.T.SnippetPhase1Arm64Test

open Std Std.ExtHashMap
open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.SnippetCheck LeanQbe.T.SpillSnippet Kraken.AArch64
open LeanQbe.T.Notation

/-! ## 1. Phase 0 Expressible V1 Arm64 Snippets (10 call-free + 1 calling) & Kissat Kernels -/

def sn_sum : Fn := tqbe $sum(%n:l) -> l {
@loop(%i:l, %acc:l) {
  %acc1 =l add %acc, %i
  %i1 =l sub %i, 1:l
  %c1 =b cnel %i1, 0:l
  jnz %c1, @loop(%i1, %acc1), @done(%acc1)
}
@done(%out:l) { ret %out }
  %c0 =b ceql %n, 0:l
  jnz %c0, @done(0:l), @loop(%n, 0:l)
}

def sn_cmp3 : Fn := tqbe $cmp3(%a:l, %b:l) -> l {
@lt { ret -1:l }
@eq { ret 0:l }
@gt { ret 1:l }
@ge { %ceq =b ceql %a, %b
  jnz %ceq, @eq, @gt }
  %clt =b csltl %a, %b
  jnz %clt, @lt, @ge
}

def sn_tworet : Fn := tqbe $tworet(%x:l, %y:l) -> l {
@nz { %r =l add %x, %y
      ret %r }
@z  { ret 7:l }
  %cz =b ceql %x, 0:l
  jnz %cz, @z, @nz
}

def sn_setlt : Fn := tqbe $setlt(%a:l, %b:l) -> l {
  %c =b csltl %a, %b
  %r =l ofBool %c
  ret %r
}

def sn_minsel : Fn := tqbe $minsel(%a:l, %b:l) -> l {
  %c =b csltl %a, %b
  %r =l select %c, %a, %b
  ret %r
}

def sn_ld : Fn := tqbe $ld(%base:l, %idx:l) -> l {
  %sc =l shl %idx, 2:l
  %p1 =l add %base, %sc
  %p2 =l add %p1, 8:l
  %v32 =w load %p2
  %v64 =l extuw %v32
  ret %v64
}

def sn_madd : Fn := tqbe $madd(%a:l, %b:l, %c:l) -> l {
  %p =l mul %a, %b
  %r =l add %p, %c
  ret %r
}

def sn_andshift : Fn := tqbe $andshift(%a:l, %b:l) -> l {
  %s =l lshr %b, 3:l
  %r =l and %a, %s
  ret %r
}

def sn_divmod : Fn := tqbe $divmod(%a:l, %b:l) -> (l, l) {
  %q =l udiv %a, %b
  %r =l urem %a, %b
  ret %q, %r
}

def sn_add128 : Fn := tqbe $add128(%a0:l, %a1:l, %b0:l, %b1:l) -> (l, l) {
  %lo, %cy =l addc %a0, %b0, false
  %hi, %_ =l addc %a1, %b1, %cy
  ret %lo, %hi
}

def sn_callinc : Fn := tqbe $callinc(%x:l, %y:l) -> l {
  %t =l call $ext1(%x)
  %r =l add %t, %y
  ret %r
}

def sn_k_ws_check : Fn := tqbe $k_ws_check(%c64:l) -> l {
  %c =w trunc %c64
  %b0 =b ceqw %c, 32:w
  %b1 =b ceqw %c, 9:w
  %o0 =b or %b0, %b1
  %b2 =b ceqw %c, 10:w
  %b3 =b ceqw %c, 13:w
  %o1 =b or %b2, %b3
  %o =b or %o0, %o1
  %r =l ofBool %o
  ret %r
}

def sn_k_bcp_bin_val : Fn := tqbe $k_bcp_bin_val(%vals:l, %w0:l) -> l {
  %w32 =w trunc %w0
  %isb =w and %w32, 0x80000000:w
  %cb =b cnew %isb, 0:w
@sat { ret 1:l } @confl { ret 2:l } @unit { ret 3:l } @large { ret 0:l }
@checkneg(%bv32:w) { %neg =b csltw %bv32, 0:w
  jnz %neg, @confl, @unit }
@bin {
  %blk =w and %w32, 0x7FFFFFFF:w
  %blk64 =l extuw %blk
  %va =l add %vals, %blk64
  %bv =i8 load %va
  %bv32 =w sext %bv
  %pos =b csgtw %bv32, 0:w
  jnz %pos, @sat, @checkneg(%bv32)
}
  jnz %cb, @bin, @large
}

def sn_k_bcp_clamp_best : Fn := tqbe $k_bcp_clamp_best(%kl:l, %best:l, %k:l, %bi:l) -> (l, l) {
  %gt =b cugtl %kl, %best
  %best1 =l select %gt, %kl, %best
  %bi1 =l select %gt, %k, %bi
  ret %best1, %bi1
}

def sn_k_watch_need : Fn := tqbe $k_watch_need(%cap:l, %len:l, %cnt:l) -> l {
  %rem =l sub %cap, %len
  %need =b cultl %rem, %cnt
  %r =l ofBool %need
  ret %r
}

def sn_k_sweep_hdr_test : Fn := tqbe $k_sweep_hdr_test(%ar:l, %r:l) -> l {
  %off =l shl %r, 2:l
  %p0 =l add %ar, %off
  %hdr =w load %p0
  %g =w and %hdr, 0x80000:w
  %cg =b cnew %g, 0:w
@skip { ret 0:l } @ok { ret 1:l }
@chk {
  %p2 =l add %p0, 8:l
  %csz =w load %p2
  %c3 =b cultw %csz, 3:w
  jnz %c3, @skip, @ok
}
  jnz %cg, @skip, @chk
}

-- Call-free Arm64 V1 + Kissat benchmark suite: `(fn, forbidIfConv)`.
def v1SuiteArm64 : List (Fn × Bool) := [
  (sn_sum, true), (sn_cmp3, true), (sn_tworet, true), (sn_setlt, true),
  (sn_minsel, false), (sn_ld, true), (sn_madd, true), (sn_andshift, true),
  (sn_divmod, true), (sn_add128, true),
  (sn_k_ws_check, true), (sn_k_bcp_bin_val, true), (sn_k_bcp_clamp_best, false),
  (sn_k_watch_need, true), (sn_k_sweep_hdr_test, true),
  (LeanQbe.T.Examples.Kissat.kissat_is_ws, true),
  (LeanQbe.T.Examples.Kissat.kissat_is_digit, true)
]

-- Tier-1/Tier-2 Arm64 V1 subset passing `liftSnippet` (`AsmIso`) cleanly:
def tier1IsoArm64 : List Fn := [
  sn_sum, sn_cmp3, sn_tworet, sn_setlt, sn_minsel, sn_madd, sn_andshift
]

/-! ## 2. 28-Live-Through + Cold-Call Outer Stress Harness (> 26 Arm64 GPRs) -/

def makeColdHelper : Fn :=
  ⟨"cold_helper", [i64, i64, i64, i64, i64], [i64], fun _ _ (a, b, _, _, _, ()) =>
    .let_ ⟨.add i64, (.var a, .var b, ())⟩ fun (s, ()) => .ret (.var s, ())⟩

def loadChainExpr {V : Ty → Type} {L : List Ty → Type} (ptr : V i64) :
    (idx rem : Nat) → List (V i64) → (List (V i64) → Expr V L [i64]) → Expr V L [i64]
  | _, 0, acc, cont => cont acc.reverse
  | idx, rem' + 1, acc, cont =>
    if idx == 0 then
      Expr.load i64 (.var ptr) fun x0 => loadChainExpr ptr 1 rem' [x0] cont
    else
      Expr.let_ ⟨.add i64, (.var ptr, .imm (BitVec.ofNat 64 (idx * 8)), ())⟩ fun (p, ()) =>
      Expr.load i64 (.var p) fun xi =>
      loadChainExpr ptr (idx + 1) rem' (xi :: acc) cont

def xorListExprGo {V : Ty → Type} {L : List Ty → Type}
    (cont : V i64 → Expr V L [i64]) (acc : V i64) : List (V i64) → Expr V L [i64]
  | [] => cont acc
  | v :: vs' =>
    Expr.let_ ⟨.xor i64, (.var acc, .var v, ())⟩ fun (acc', ()) => xorListExprGo cont acc' vs'

def xorListExpr {V : Ty → Type} {L : List Ty → Type} (fallback : V i64)
    (vs : List (V i64)) (cont : V i64 → Expr V L [i64]) : Expr V L [i64] :=
  match vs with
  | [] => cont fallback
  | v0 :: rest => xorListExprGo cont v0 rest

def makeStressHarness (snipName : Sym) (as rs : List Ty) (marked : Bool) : Fn :=
  let body : Func [i64, i64] [i64] := fun V L (ptr, k, ()) =>
    let callSnip (xs : List (V i64)) (afterCall : V i64 → Expr V L [i64]) : Expr V L [i64] :=
      let x0 := xs.headD ptr
      let x1 := (xs.drop 1).headD x0
      let x2 := (xs.drop 2).headD x1
      let x3 := (xs.drop 3).headD x2
      let wrapEnd (rv : V i64) : Expr V L [i64] :=
        if marked then
          Expr.let_ ⟨.add i64, (.var ptr, .imm 224#64, ())⟩ fun (m1, ()) =>
          Expr.store (t := i64) (.imm 0x51A80000#64) (.var m1) (afterCall rv)
        else afterCall rv
      match as, rs with
      | [.bits 64], [.bits 64] =>
        Expr.call snipName (as := [i64]) (bs := [i64]) (.var x0, ()) fun (r0, ()) => wrapEnd r0
      | [.bits 64], [.bool] =>
        Expr.call snipName (as := [i64]) (bs := [.bool]) (.var x0, ()) fun (r0, ()) =>
          Expr.let_ ⟨.ofBool 64, (.var r0, ())⟩ fun (r0l, ()) => wrapEnd r0l
      | [.bits 64, .bits 64], [.bits 64] =>
        Expr.call snipName (as := [i64, i64]) (bs := [i64]) (.var x0, .var x1, ()) fun (r0, ()) =>
          wrapEnd r0
      | [.bits 64, .bits 64, .bits 64], [.bits 64] =>
        Expr.call snipName (as := [i64, i64, i64]) (bs := [i64]) (.var x0, .var x1, .var x2, ())
          fun (r0, ()) => wrapEnd r0
      | [.bits 64, .bits 64, .bits 64, .bits 64], [.bits 64] =>
        Expr.call snipName (as := [i64, i64, i64, i64]) (bs := [i64])
          (.var x0, .var x1, .var x2, .var x3, ()) fun (r0, ()) => wrapEnd r0
      | [.bits 64, .bits 64], [.bits 64, .bits 64] =>
        Expr.call snipName (as := [i64, i64]) (bs := [i64, i64]) (.var x0, .var x1, ())
          fun (r0, r1, ()) =>
            Expr.let_ ⟨.xor i64, (.var r0, .var r1, ())⟩ fun (rx, ()) => wrapEnd rx
      | [.bits 64, .bits 64, .bits 64, .bits 64], [.bits 64, .bits 64] =>
        Expr.call snipName (as := [i64, i64, i64, i64]) (bs := [i64, i64])
          (.var x0, .var x1, .var x2, .var x3, ()) fun (r0, r1, ()) =>
          Expr.let_ ⟨.xor i64, (.var r0, .var r1, ())⟩ fun (rx, ()) => wrapEnd rx
      | _, _ => Expr.hlt
    loadChainExpr ptr 0 26 [] fun xs =>
      let x0 := xs.headD ptr; let x1 := (xs.drop 1).headD x0
      let x2 := (xs.drop 2).headD x1; let x3 := (xs.drop 3).headD x2
      let afterStart (cont : Expr V L [i64]) : Expr V L [i64] :=
        if marked then
          Expr.let_ ⟨.add i64, (.var ptr, .imm 216#64, ())⟩ fun (m0, ()) =>
          Expr.store (t := i64) (.imm 0x51A70000#64) (.var m0) cont
        else cont
      afterStart <|
      callSnip xs fun rXor =>
        Expr.let_ ⟨.cmp .eq i64 .bool rfl, (.var k, .imm 0#64, ())⟩ fun (isCold, ()) =>
        Expr.group (sig := [[i64]])
          (fun _ => .cons (ts := [i64]) (fun (rvFin, ()) =>
            xorListExpr ptr (rvFin :: xs) fun finalSum =>
            Expr.ret (.var finalSum, ())) .nil)
          fun (joinLbl, ()) =>
          Expr.jnz (.var isCold)
            (.call "cold_helper" (as := [i64, i64, i64, i64, i64]) (bs := [i64])
              (.var rXor, .var x0, .var x1, .var x2, .var x3, ())
              fun (cRet, ()) => .jump joinLbl (.var cRet, ()))
            (.jump joinLbl (.var rXor, ()))
  ⟨"__caller", [i64, i64], [i64], body⟩

def isMarkerMov (val16 : Int64) (i : Instr) : Bool :=
  match i.operation with
  | .MOVZ _ (.int64 c) .LSL16 => c == val16
  | _ => false

def countMarkedInSp (ds : List ADir) : Nat :=
  let ds0 := stripNops ds
  let rec go (inReg : Bool) (inSp : Nat) : List ADir → Nat
    | [] => inSp
    | .instr ins :: rest =>
      if isMarkerMov 0x51A7 ins then go true 0 rest
      else if isMarkerMov 0x51A8 ins then inSp
      else if inReg then go true (inSp + (if isBodySpillInstr ins then 1 else 0)) rest
      else go false inSp rest
    | _ :: rest => go inReg inSp rest
  go false 0 ds0

def runStressEntry (s : Fn) (forbidIf : Bool) (marked : Bool) : Bool :=
  let sMid := s.midPolicy armLegalTarget SnippetOptPolicy.predictable
  let hBase := Spill.hints armIsa sMid
  match Rega.lowerFn armIsa hBase sMid.ext sMid with
  | .error _ => false
  | .ok baseDirs =>
    if (profileDirs baseDirs true).spills > 0 then false
    else
      let caller := makeStressHarness s.name s.as s.rs marked
      let m : Module := { fns := [makeColdHelper, s, caller] }
      let polOf (nm : Sym) : SnippetOptPolicy :=
        if nm == s.name then .predictable else .default
      let mLate := m.midThenLateInline armLegalTarget polOf (lateInlineSnippetsPolicy [s.name])
      let outerLate := (mLate.fns.find? (·.name == "__caller")).getD caller
      let hOuterAuto := Spill.hints armIsa outerLate
      match splice_snippet_hints armIsa sMid outerLate hOuterAuto [] (some hBase) with
      | .error _ => false
      | .ok (hSpliced, _) =>
        let bgt : SnippetBudget := {
          name := s.name
          maxInteriorSpills := 0
          forbidIfConv := forbidIf
          requireZeroCalls := true
        }
        match checkRegaAndBudget sMid outerLate hSpliced bgt with
        | .error _ => false
        | .ok (dirs, rep) =>
          rep.interiorSpills == 0 && (!marked || countMarkedInSp dirs == 0)

def runLiftIsoCheck (s : Fn) : Bool :=
  let sMid := s.midPolicy armLegalTarget SnippetOptPolicy.predictable
  let hBase := Spill.hints armIsa sMid
  match Rega.lowerFn armIsa hBase sMid.ext sMid with
  | .error _ => false
  | .ok baseDirs =>
    match liftSnippet s.name sMid.as sMid.rs baseDirs with
    | .ok res => res.iso.passed
    | .error _ => false

def liftIsoVerdictKind (s : Fn) : Option String :=
  let sMid := s.midPolicy armLegalTarget SnippetOptPolicy.predictable
  let hBase := Spill.hints armIsa sMid
  match Rega.lowerFn armIsa hBase sMid.ext sMid with
  | .error _ => none
  | .ok baseDirs =>
    match liftSnippet s.name sMid.as sMid.rs baseDirs with
    | .error e => some s!"err:{e}"
    | .ok res =>
      if res.iso.passed then some "pass"
      else match res.iso with
        | .fail k _ => some k
        | _ => some "pass"

-- All 17 call-free V1 + Kissat Arm64 snippets achieve `inSp = 0` inside both marked AND unmarked
-- 28-live-through + cold-call outer functions via real post-`mid` `lateInline` + `splice_snippet_hints`!
#guard v1SuiteArm64.all (fun (s, fIf) => runStressEntry s fIf true && runStressEntry s fIf false)

-- All 7 Tier-1/Tier-2 Arm64 V1 snippets pass `liftSnippet` (`AsmIso`) round-trip check!
#guard tier1IsoArm64.all runLiftIsoCheck

-- Diagnostic `AsmIso` regression checks on Arm64:
#guard liftIsoVerdictKind sn_ld == some "insn_or_cfg_diff"
#guard liftIsoVerdictKind sn_divmod == some "insn_or_cfg_diff"
#guard liftIsoVerdictKind sn_add128 == some "err:adds_s_xzr"
#guard (liftIsoVerdictKind LeanQbe.T.Examples.Kissat.kissat_is_ws).any (·.startsWith "err:")
#guard (liftIsoVerdictKind LeanQbe.T.Examples.Kissat.kissat_is_digit).any (·.startsWith "err:")

-- Negative fail-loud checks on `sn_callinc`:
#guard
  let sMid := sn_callinc.midPolicy armLegalTarget .predictable
  let hBase := Spill.hints armIsa sMid
  let caller := makeStressHarness sn_callinc.name sn_callinc.as sn_callinc.rs false
  let m : Module := {
    fns := [makeColdHelper, sn_callinc, caller]
    externs := [{ name := "ext1", as := [i64], rs := [i64] }]
  }
  let polOf (nm : Sym) : SnippetOptPolicy :=
    if nm == sn_callinc.name then .predictable else .default
  let forcePol : InlinePolicy := {
    lateInlineSnippetsPolicy [sn_callinc.name] with
      leafMax := 1000, singleSiteMax := 1000, maxCallerSize := 10000, maxCalleeCalls := 10,
      maxTotalDup := 10000, leafNoLoopMaxDup := 10000,
      maxCallerCalls := 10, exemptNoLoopMax := 10000
  }
  let mForce := m.midThenLateInline armLegalTarget polOf forcePol
  let outerForce := (mForce.fns.find? (·.name == "__caller")).getD caller
  let hOuterForce := Spill.hints armIsa outerForce
  let spliceRejected :=
    match splice_snippet_hints armIsa sMid outerForce hOuterForce [] (some hBase) with
    | .error "snippet_contains_call" => true
    | _ => false
  let auditRejected :=
    match auditSnippetInOuter armIsa sMid outerForce hOuterForce
        (SnippetBudget.predictable "callinc") with
    | .error ds => ds.any (·.kind == "call_in_snippet")
    | .ok _ => false
  spliceRejected && auditRejected

-- Standalone Kissat `full_has_ternary_m7` (`m7HasTernaryFn`) lowers cleanly under `Fn.midPolicy`
-- with zero calls on Arm64 under `SnippetOptPolicy.predictable`.
#guard
  let m7 := LeanQbe.T.Examples.Kissat.FullM7HotTernary.m7HasTernaryFn
  let m7Mid := m7.midPolicy armLegalTarget .predictable
  let h := Spill.hints armIsa m7Mid
  match Rega.lowerFn armIsa h m7Mid.ext m7Mid with
  | .ok ds => (profileDirs ds true).calls == 0 && (profileDirs ds true).bodyInsns > 0
  | .error _ => false

/-! ## 3. Certified `compileLateInlined` + `splice_snippet_hints` + `armInit` Proof (`std3`) -/

def certColdFn : Fn := makeColdHelper
def certWsFn : Fn := sn_k_ws_check
def certCallerFn : Fn :=
  { makeStressHarness certWsFn.name certWsFn.as certWsFn.rs false with name := "caller28" }

def certModArm64 : Module :=
  { fns := [certColdFn, certWsFn, certCallerFn] }

def certPolicyArm64 (s : Sym) : SnippetOptPolicy :=
  if s == "k_ws_check" then .predictable else .default

def certInlPolArm64 : InlinePolicy :=
  lateInlineSnippetsPolicy ["k_ws_check"]

def computeCertHintsArm64 : Except String (List armIsa.Hints) := do
  let mMid := certModArm64.midPolicy armLegalTarget certPolicyArm64
  let mLate := mMid.lateInline certInlPolArm64
  let sMid := mMid.fns.getD 1 certWsFn
  let hSnip := Spill.hints armIsa sMid
  mLate.fns.mapM fun f => do
    let hAuto := Spill.hints armIsa f
    if f.name == "caller28" then
      let (hSpliced, _) ← splice_snippet_hints armIsa sMid f hAuto [] (some hSnip)
      pure hSpliced
    else
      pure hAuto

def computeCertArm64Bundle :
    Except String (List armIsa.Hints × List armIsa.Directive × List (Sym × Nat)) := do
  let hs ← computeCertHintsArm64
  let (code, bounds) ← compileLateInlined armIsa armLegalTarget armTarget.frame.raBytes
    [] [] 0 certModArm64 certPolicyArm64 certInlPolArm64 hs
  pure (hs, code, bounds)

meta section
open Lean Elab Command Term Meta

def addLitDefArm64 (declNm : Name) (ty val : Lean.Expr) : CoreM Unit := do
  let decl := Declaration.defnDecl {
    name := declNm, levelParams := [], type := ty, value := val,
    hints := .abbrev, safety := .safe }
  addDecl decl (forceExpose := true)
  compileDecl decl

elab "splice_arm64_late_cert " hintsId:ident codeId:ident boundsId:ident : command => do
  let ns ← getCurrNamespace
  let evalRes ← liftTermElabM do
    let resTy :=
      mkApp2 (mkConst ``Except [.zero, .zero]) (mkConst ``String)
        (mkApp2 (mkConst ``Prod [.zero, .zero])
          (mkApp (mkConst ``List [.zero])
            (mkApp (mkConst ``LeanQbe.T.Isa.Hints) (mkConst ``LeanQbe.T.Arm64.armIsa)))
          (mkApp2 (mkConst ``Prod [.zero, .zero])
            (mkApp (mkConst ``List [.zero])
              (mkApp (mkConst ``LeanQbe.T.Isa.Directive) (mkConst ``LeanQbe.T.Arm64.armIsa)))
            (mkApp (mkConst ``List [.zero])
              (mkApp2 (mkConst ``Prod [.zero, .zero])
                (mkConst ``LeanQbe.T.Sym) (mkConst ``Nat)))))
    unsafe evalExpr
      (Except String (List armIsa.Hints × List armIsa.Directive × List (Sym × Nat)))
      resTy (mkConst ``LeanQbeTest.T.SnippetPhase1Arm64Test.computeCertArm64Bundle)
  match evalRes with
  | .error e => throwError "splice_arm64_late_cert: {e}"
  | .ok (hs, code, bounds) =>
    let hTy := mkApp (mkConst ``List [.zero])
      (mkApp (mkConst ``LeanQbe.T.Isa.Hints) (mkConst ``LeanQbe.T.Arm64.armIsa))
    let cTy := mkApp (mkConst ``List [.zero])
      (mkApp (mkConst ``LeanQbe.T.Isa.Directive) (mkConst ``LeanQbe.T.Arm64.armIsa))
    let symNatTy := mkApp2 (mkConst ``Prod [.zero, .zero])
      (mkConst ``LeanQbe.T.Sym) (mkConst ``Nat)
    let bTy := mkApp (mkConst ``List [.zero]) symNatTy
    liftCoreM do
      addLitDefArm64 (ns ++ hintsId.getId) hTy (Lean.toExpr hs)
      addLitDefArm64 (ns ++ codeId.getId) cTy (Lean.toExpr code)
      addLitDefArm64 (ns ++ boundsId.getId) bTy (Lean.toExpr bounds)

end

splice_arm64_late_cert certHintsArm64 certCodeArm64 certBoundsArm64

theorem certArm64_cm :
    compileLateInlined armIsa armLegalTarget armTarget.frame.raBytes
      [] [] 0 certModArm64 certPolicyArm64 certInlPolArm64 certHintsArm64 =
      .ok (certCodeArm64, certBoundsArm64) := by
  t_kernel_rfl

-- Verify `inSp = 0` inside `caller28` for the literal spliced cert hints too!
#guard
  let mMid := certModArm64.midPolicy armLegalTarget certPolicyArm64
  let mLate := mMid.lateInline certInlPolArm64
  let sMid := mMid.fns.getD 1 certWsFn
  let outerLate := mLate.fns.getD 2 certCallerFn
  let hOuter := certHintsArm64.getD 2 (Spill.hints armIsa outerLate)
  match checkRegaAndBudget sMid outerLate hOuter (SnippetBudget.predictable "k_ws_check") with
  | .ok (_, rep) => rep.interiorSpills == 0
  | .error _ => false

theorem certArm64_small : armLayout.progSmall (certCodeArm64 ++ []) = true := by t_kernel_rfl

@[instance_reducible] def certHostArm64 : armTarget.mach.Host :=
  armLayout.layoutOf (certCodeArm64 ++ []) certArm64_small

theorem certArm64_labelsUnique : armTarget.LabelsUnique certHostArm64 := by
  have hcm : compileDirectModule armIsa armTarget.frame.raBytes [] [] 0
      (certModArm64.midThenLateInline armLegalTarget certPolicyArm64 certInlPolArm64).fns
      certHintsArm64 = .ok (certCodeArm64, certBoundsArm64) := by
    have h := certArm64_cm
    dsimp only [compileLateInlined] at h
    split at h
    · exact h
    · cases h
  refine compileDirectModule_labelsUnique armLabelClean certHostArm64 ?_ hcm ?_ ?_
  · rw [certHostArm64]
    exact armLayout.prog_layoutOf (certCodeArm64 ++ []) certArm64_small
  · rw [certModArm64.midThenLateInline_fns_names armLegalTarget certPolicyArm64 certInlPolArm64]
    decide
  · rw [certModArm64.midThenLateInline_fns_names armLegalTarget certPolicyArm64 certInlPolArm64]
    decide

theorem certModArm64_acyclic : certModArm64.checkAcyclic = true := by t_kernel_rfl

theorem certColdFn_wf : certColdFn.Wf := by t_wf_reify
theorem certWsFn_wf : certWsFn.Wf := by t_wf_reify
theorem certCallerFn_wf : certCallerFn.Wf := by t_wf_reify

theorem certModArm64_wf : ∀ f ∈ certModArm64.fns, f.Wf := by
  intro f hf
  simp only [certModArm64, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · exact certColdFn_wf
  · exact certWsFn_wf
  · exact certCallerFn_wf

def wsCheckVal (c64 : BitVec 64) : BitVec 64 :=
  let c : BitVec 32 := c64.setWidth 32
  let b := (c == 32#32 || c == 9#32) || (c == 10#32 || c == 13#32)
  if b then 1#64 else 0#64

def foldXor : List (BitVec 64) → BitVec 64
  | [] => 0#64
  | v :: vs => vs.foldl (· ^^^ ·) v

def caller28Val (xs : List (BitVec 64)) (k : BitVec 64) : BitVec 64 :=
  let x0 := xs.headD 0#64
  let ws := wsCheckVal x0
  let rvFin := if k == 0#64 then ws + x0 else ws
  foldXor (rvFin :: xs)

def coldSpec : Spec [i64, i64, i64, i64, i64] [i64] := fun (a, b, _, _, _, ()) m Q _ =>
  Q (a + b, ()) m

def wsSpec : Spec [i64] [i64] := fun (c64, ()) m Q _ =>
  Q (wsCheckVal c64, ()) m

def caller28Spec : Spec [i64, i64] [i64] := fun (ptr, k, ()) m Q _ =>
  ∃ (xs : List (BitVec 64)) (R : Mem 64 → Prop), xs.length = 26 ∧ (m =⋆ array64 ptr xs ⋆ R) ∧
    Q (caller28Val xs k, ()) m

def certΓArm64 : Env
  | "cold_helper", [.bits 64, .bits 64, .bits 64, .bits 64, .bits 64], [.bits 64], xs, m, Q, X =>
      coldSpec xs m Q X
  | "k_ws_check", [.bits 64], [.bits 64], xs, m, Q, X => wsSpec xs m Q X
  | "caller28", [.bits 64, .bits 64], [.bits 64], xs, m, Q, X => caller28Spec xs m Q X
  | _, _, _, _, _, _, _ => False

private theorem bool_ofNat_64 (b : Bool) : BitVec.ofNat 64 b.toNat = if b then 1#64 else 0#64 := by
  cases b <;> decide

private theorem liftCmp_eq_bits {n : Nat} (a b : BitVec n) :
    liftCmp (fun {_} => CmpOp.eq.evalBits) CmpOp.eq.evalBool (.bits n) a b = (a == b) := rfl

private theorem certColdFn_wp {xs : Tup Val [i64, i64, i64, i64, i64]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} (h : coldSpec xs m Q X) :
    Func.wp certΓArm64 certColdFn.body xs m Q X := by
  rcases xs with ⟨a, b, _, _, _, ⟨⟩⟩
  exact h

private theorem certWsFn_wp {xs : Tup Val [i64]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} (h : wsSpec xs m Q X) :
    Func.wp certΓArm64 certWsFn.body xs m Q X := by
  rcases xs with ⟨c64, ⟨⟩⟩
  unfold wsSpec wsCheckVal at h
  dsimp only [Func.wp, certWsFn, sn_k_ws_check, wp, Op.wp, OpCode.wp, lift1, lift2,
    Ty.hasFloat, Arg.val, vals]
  simp only [liftCmp_eq_bits, bool_ofNat_64, Bool.false_eq_true, ↓reduceIte]
  exact ⟨by decide, h⟩

private theorem loadChainExpr_wp (Γ : Env) (Q : Post [i64]) (X : XPost) (m : Mem 64)
    {ptr : BitVec 64} {xs : List (BitVec 64)} {R : Mem 64 → Prop}
    (hm : (array64 ptr xs ⋆ R) m)
    (cont : List (BitVec 64) → Expr Val Cont [i64]) :
    ∀ (rem idx : Nat) (acc : List (BitVec 64)),
      idx + rem ≤ xs.length →
      acc.reverse = xs.take idx →
      wp Γ Q X (cont (xs.take (idx + rem))) m →
      wp Γ Q X (loadChainExpr ptr idx rem acc cont) m
  | 0, idx, acc, _, hacc, hk => by
    dsimp only [loadChainExpr]
    rw [hacc]
    simpa [Nat.add_zero] using hk
  | rem' + 1, 0, acc, hlen, hacc, hk => by
    have ha0 : acc = [] := by
      have : acc.reverse = [] := by simpa using hacc
      exact List.reverse_eq_nil_iff.mp this
    subst ha0
    dsimp only [loadChainExpr, wp]
    refine ⟨xs[0], ?_, ?_⟩
    · simpa using loadVal_array64 (i := 0) (by omega) hm
    · refine loadChainExpr_wp Γ Q X m hm cont rem' 1 [xs[0]] (by omega) ?_
        (by rw [show 0 + (rem' + 1) = 1 + rem' by omega] at hk; exact hk)
      cases xs with
      | nil => simp at hlen
      | cons x0 _ => simp
  | rem' + 1, idx + 1, acc, hlen, hacc, hk => by
    dsimp only [loadChainExpr, wp, Op.wp, OpCode.wp, lift2, Ty.hasFloat, Arg.val, vals]
    refine ⟨xs[idx + 1], ?_, ?_⟩
    · rw [Nat.mul_comm]
      exact loadVal_array64 (i := idx + 1) (by omega) hm
    · refine loadChainExpr_wp Γ Q X m hm cont rem' (idx + 2) (xs[idx + 1] :: acc)
        (by omega) ?_ (by rw [show idx + 2 + rem' = idx + 1 + (rem' + 1) by omega]; exact hk)
      rw [List.reverse_cons, hacc]
      symm
      rw [show idx + 2 = (idx + 1) + 1 from rfl, List.take_add_one,
        List.getElem?_eq_getElem (by omega : idx + 1 < xs.length)]
      simp

private theorem xorListExprGo_wp (Γ : Env) (Q : Post [i64]) (X : XPost) (m : Mem 64)
    (cont : BitVec 64 → Expr Val Cont [i64]) :
    ∀ (vs : List (BitVec 64)) (acc : BitVec 64),
      wp Γ Q X (cont (vs.foldl (· ^^^ ·) acc)) m →
      wp Γ Q X (xorListExprGo cont acc vs) m
  | [], _, h => h
  | _ :: vs, _, h => xorListExprGo_wp Γ Q X m cont vs _ h

private theorem xorListExpr_cons_wp (Γ : Env) (Q : Post [i64]) (X : XPost) (m : Mem 64)
    (fallback v0 : BitVec 64) (rest : List (BitVec 64))
    (cont : BitVec 64 → Expr Val Cont [i64])
    (h : wp Γ Q X (cont (foldXor (v0 :: rest))) m) :
    wp Γ Q X (xorListExpr fallback (v0 :: rest) cont) m :=
  xorListExprGo_wp Γ Q X m cont rest v0 h

private theorem certCallerFn_wp {xs : Tup Val [i64, i64]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} (h : caller28Spec xs m Q X) :
    Func.wp certΓArm64 certCallerFn.body xs m Q X := by
  rcases xs with ⟨ptr, k, ⟨⟩⟩
  rcases h with ⟨ys, R, hlen, hm, hQ⟩
  rcases ys with _ | ⟨y0, ys'⟩
  · simp at hlen
  dsimp only [Func.wp, certCallerFn, makeStressHarness, i64]
  refine loadChainExpr_wp certΓArm64 Q X m hm _ 26 0 [] (by omega) rfl ?_
  rw [show (y0 :: ys').take (0 + 26) = y0 :: ys' from List.take_of_length_le (by omega)]
  refine ⟨fun (r, _) m₁ => r = wsCheckVal y0 ∧ m₁ = m, X, ⟨rfl, rfl⟩, ?_,
    fun _ _ _ _ hx => hx⟩
  rintro ⟨rXor, ⟨⟩⟩ m₁ ⟨hrXor, hm1⟩
  subst hrXor
  rw [hm1]
  simp only [wp, Op.wp, OpCode.wp, liftCmp, CmpOp.evalBits, Ty.hasFloat, Arg.val, vals,
    Bool.false_eq_true, ↓reduceIte]
  intro Js hClosed
  have hret : ∀ rvFin : BitVec 64,
      Q (foldXor (rvFin :: y0 :: ys'), ()) m →
      Js.get .here (rvFin, ()) m := by
    intro rvFin hqv
    refine hClosed.1 (rvFin, ()) m ?_
    exact xorListExpr_cons_wp certΓArm64 Q X m ptr rvFin (y0 :: ys')
      (fun res => Expr.ret (.var res, ())) hqv
  constructor
  · intro heq
    have hk : (k == 0#64) = true := heq
    refine ⟨fun (c, _) m₂ => c = wsCheckVal y0 + y0 ∧ m₂ = m, X,
      ⟨rfl, rfl⟩, ?_, fun _ _ _ _ hx => hx⟩
    rintro ⟨cRet, ⟨⟩⟩ m₂ ⟨hcRet, hm2⟩
    subst hcRet
    rw [hm2]
    refine hret _ ?_
    simpa [caller28Val, hk] using hQ
  · intro hne
    have hk : (k == 0#64) = false := hne
    refine hret _ ?_
    simpa [caller28Val, hk] using hQ

theorem certModArm64_modOk : ModuleOk certΓArm64 certModArm64 := by
  refine Module.moduleOk_of_checkAcyclic certModArm64_acyclic certModArm64_wf ?_
  intro f hf xs m Q X hΓ
  simp only [certModArm64, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · dsimp only [certΓArm64, certColdFn, makeColdHelper, i64] at hΓ
    exact certColdFn_wp hΓ
  · dsimp only [certΓArm64, certWsFn, sn_k_ws_check, i64] at hΓ
    exact certWsFn_wp hΓ
  · dsimp only [certΓArm64, certCallerFn, makeStressHarness, i64] at hΓ
    exact certCallerFn_wp hΓ

theorem certArm64_fnSpec :
    armTarget.Defined certHostArm64 "caller28" ∧
      armTarget.FnSpec certHostArm64 "caller28" caller28Spec
        (lookupFnBound certBoundsArm64 "caller28").get! 0 := by
  have hmem : ("caller28", (lookupFnBound certBoundsArm64 "caller28").get!) ∈ certBoundsArm64 :=
    of_decide_eq_true (by t_kernel_rfl)
  obtain ⟨f, hf, hnm, hdef, hspec⟩ := compileLateInlined_sound armTarget certHostArm64
    armLegalTarget certModArm64 certPolicyArm64 certInlPolArm64 certΓArm64 [] [] 0 certHintsArm64
    certCodeArm64 certBoundsArm64 0 certArm64_cm
    ⟨[], by
      change certCodeArm64 ++ [] =
        armTarget.mach.prog (armLayout.layoutOf (certCodeArm64 ++ []) certArm64_small)
      exact (armLayout.prog_layoutOf (certCodeArm64 ++ []) certArm64_small).symm⟩
    certArm64_labelsUnique certModArm64_modOk (fun _ hx => nomatch hx)
    (And.intro (fun _ hx => nomatch hx) (fun _ hx => nomatch hx)) (fun _ hx => nomatch hx)
    _ hmem
  have hfnEq : f = certCallerFn := by
    simp only [certModArm64, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl
    · simp [certColdFn, makeColdHelper] at hnm
    · simp [certWsFn, sn_k_ws_check] at hnm
    · rfl
  subst hfnEq
  refine ⟨hdef, ?_⟩
  intro args m Q X hcaller s ra R hargs hra hsp hm
  refine hspec args m Q X ?_ s ra R hargs hra hsp hm
  refine ⟨[i64, i64], [i64], rfl, rfl, args, Q, (fun _ _ _ _ => False), rfl, ?_, ?_, ?_⟩
  · intro r m' ⟨⟨v, ⟨⟩⟩, he, hq⟩
    subst he
    exact hq
  · intro _ _ _ _ ⟨_, _, _, _, hx⟩
    exact nomatch hx
  · refine ⟨List.mem_append_left _ ?_, hcaller⟩
    dsimp only [certModArm64, Module.sigs, List.map, Fn.sig, certCallerFn, makeStressHarness]
    exact .tail _ (.tail _ (.head _))

def sampleWords26 : List (BitVec 64) :=
  [32#64, 1#64, 2#64, 3#64, 4#64, 5#64, 6#64, 7#64, 8#64, 9#64, 10#64, 11#64, 12#64,
   13#64, 14#64, 15#64, 16#64, 17#64, 18#64, 19#64, 20#64, 21#64, 22#64, 23#64, 24#64, 25#64]

theorem certArm64_fast (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hx0 : s.regs.getXReg .X0 = 0x1000#64) (hx1 : s.regs.getXReg .X1 = 1#64)
    (hra : s.regs.X30 = ra.toUInt64)
    (hsp : s.regs.SP.toNat % 16 = 0)
    (hmem : s.dmem =⋆ array64 0x1000#64 sampleWords26 ⋆
      region (s.regs.SP.toBitVec - BitVec.ofNat 64 (lookupFnBound certBoundsArm64 "caller28").get!)
        (lookupFnBound certBoundsArm64 "caller28").get! ⋆ R) :
    Eventually (armTarget.mach.step certHostArm64)
      (fun st => st.pc = ra ∧
        (st.data.regs.getXReg .X0).toBitVec = caller28Val sampleWords26 1#64)
      ⟨s, armTarget.mach.labelAddr certHostArm64 "caller28"⟩ := by
  have hfn := certArm64_fnSpec.2
  have hargs : armTarget.ArgsIn (as := [i64, i64]) (0x1000#64, 1#64, ()) s :=
    ⟨_, rfl, .cons ⟨by decide, by simpa [get_reg] using hx0⟩
      (.cons ⟨by decide, by simpa [get_reg] using hx1⟩ .nil)⟩
  obtain ⟨mf, mR, hu1, hd1, ⟨mArr, f, hu2, hd2, hmArr, hf⟩, hmRest⟩ := hmem
  have hmEq : s.dmem =⋆ Eq mArr ⋆
      region (s.regs.SP.toBitVec - BitVec.ofNat 64 (lookupFnBound certBoundsArm64 "caller28").get!)
        (lookupFnBound certBoundsArm64 "caller28").get! ⋆ R :=
    ⟨mf, mR, hu1, hd1, ⟨mArr, f, hu2, hd2, rfl, hf⟩, hmRest⟩
  have hspec : caller28Spec (0x1000#64, 1#64, ()) mArr
      (fun r _ => r = (caller28Val sampleWords26 1#64, ())) (fun _ _ _ _ => False) :=
    ⟨sampleWords26, emp, rfl, by rwa [sep_emp], rfl⟩
  refine eventually_weaken _ _ _ _ ?_
    (@arm64_of_returns certHostArm64 _ _ _ _ _ _ hfn _ _ _ hspec s ra R hargs hra hsp hmEq)
  rintro st ⟨hpc, _, _, _, _, rfl, hrets, _⟩
  exact ⟨hpc, by
    simpa [armInit, get_reg] using
      armInit.retsIn_singleton (caller28Val sampleWords26 1#64) st.data hrets⟩

/-! ## 4. Standard-Axiom (`std3`) Audit -/

#print axioms certArm64_cm
#print axioms certArm64_labelsUnique
#print axioms certArm64_fnSpec
#print axioms certArm64_fast

end LeanQbeTest.T.SnippetPhase1Arm64Test
