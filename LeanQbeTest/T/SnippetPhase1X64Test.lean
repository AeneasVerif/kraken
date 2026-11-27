module

public import LeanQbe.T.Amd64.Snippet
public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.MainLateInline
public import LeanQbe.T.Logic.MemLemmas
public import LeanQbe.T.Notation
public import LeanQbe.T.NotationSugar
public import LeanQbe.T.Examples.Kissat.Dimacs
public import LeanQbe.T.Examples.Kissat.Plain1
import LeanQbe.T.FlatLemmas
import all Kraken.Mem
import all Kraken.Separation
public meta import Lean
public meta import LeanQbe.T.OptPolicy
public meta import LeanQbe.T.Main
public meta import LeanQbe.T.MainLateInline
public meta import LeanQbe.T.Spill
public meta import LeanQbe.T.SpillSnippet
public meta import LeanQbe.T.SnippetCheck
public meta import LeanQbe.T.Amd64.Targ
public meta import LeanQbe.T.Amd64.TargLemmas
public meta import LeanQbe.T.Amd64.Snippet
public meta import LeanQbe.T.MainSplice
public meta import LeanQbe.T.MainLinkSplice
public meta import LeanQbe.T.Notation
public meta import LeanQbe.T.NotationSugar
public meta import LeanQbe.T.Examples.Kissat.Dimacs
public meta import LeanQbe.T.Examples.Kissat.Plain1

/-!
# Phase 1 SysV x86-64 Predictable Codegen, `AsmIso`, & Certified Late-Inline Tests

Tests end-to-end on `x64Target` (`x64LegalTarget`, `x64Layout`, `x64Init`):
1. Phase 0's 22 expressible call-free V1 x64 snippets (`sum`, `cmp3`, `tworet`, `lea3`, `mr`,
   `setlt`, `minsel`, `m3`, `m4`, `m1`, `m2`, `wsum_rot`, `wsum_hdr`, `lohi`, `tbit`, `sgt5`,
   `mixw`, `add128`, `divmod`, `div10`, `add32`, `lowbyte`) + 5 Kissat hot inner kernels +
   `kissat_is_ws` + `kissat_is_digit` (`Amd64.liftSnippet` `AsmIso` PASS + 14-live-through &
   cold-call outer harness via real post-`mid` `lateInline` + `splice_snippet_hints`, confirming
   **`inSp = 0`** and `@predictable` `checkRegaAndBudget` PASS).
2. Fail-loud negative `@predictable` checks (`callinc`, `trc` rejected with `call_in_snippet`).
3. Standalone Kissat `plain_red_less` lowering under `Fn.midPolicy`.
4. Certified 3-function `certModX64` (`cold_helper`, `k_ws_check`, 14-live-through `caller14`)
   compiled via `compileLateInlined` + `splice_snippet_hints`, verifying `inSp = 0`,
   `compileLateInlined_sound` `x64Target.FnSpec`, closed `x64_of_returns` `Eventually`, and
   strictly `std3` axioms (`0` `sorry`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbeTest.T.SnippetPhase1X64Test

open Std Std.ExtHashMap
open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.SnippetCheck LeanQbe.T.SpillSnippet Kraken.X64
open LeanQbe.T.Notation

/-! ## 1. Phase 0 Expressible V1 x64 Snippets (22 call-free + 2 calling) & Kissat Kernels -/

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

def sn_lea3 : Fn := tqbe $lea3(%a:l, %b:l) -> l {
  %s =l shl %b, 3:l
  %t =l add %a, %s
  %u =l add %t, 7:l
  ret %u
}

def sn_mr : Fn := tqbe $mr(%p:l, %a:l, %b:l) -> l {
@arm1 { store l %a, %p
  ret 1:l }
@arm2 { store l %b, %p
  ret 2:l }
  %c =b ceql %b, 0:l
  jnz %c, @arm1, @arm2
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

def sn_m3 : Fn := tqbe $m3(%base:l, %idx:l) -> l {
  %sc =l shl %idx, 2:l
  %p1 =l add %base, %sc
  %p2 =l add %p1, 8:l
  %v32 =w load %p2
  %v64 =l extuw %v32
  ret %v64
}

def sn_m4 : Fn := tqbe $m4(%p:l, %a:l) -> l {
  %v =w load %p
  %c =b ceqw %v, 0:w
@hit  { ret %a }
@miss { ret 0:l }
  jnz %c, @hit, @miss
}

def sn_m1 : Fn := tqbe $m1(%p:l, %y:l) -> l {
  %v =l load %p
  %r =l add %v, %y
  ret %r
}

def sn_m2 : Fn := tqbe $m2(%p:l, %y:l) -> l {
  %v =l load %p
  %s =l add %v, %y
  store l %s, %p
  ret %s
}

def sn_wsum_rot : Fn := tqbe $wsum_rot(%a:l, %n:l) -> l {
@loop(%i:l, %s:l) {
  %off =l shl %i, 3:l
  %addr =l add %a, %off
  %v =l load %addr
  %s1 =l add %s, %v
  %i1 =l add %i, 1:l
  %c1 =b cultl %i1, %n
  jnz %c1, @loop(%i1, %s1), @done(%s1)
}
@done(%out:l) { ret %out }
  %c0 =b cultl 0:l, %n
  jnz %c0, @loop(0:l, 0:l), @done(0:l)
}

def sn_wsum_hdr : Fn := tqbe $wsum_hdr(%a:l, %n:l) -> l {
@done(%out:l) { ret %out }
@hdr(%i:l, %s:l) {
  %c =b cultl %i, %n
  jnz %c, @body(%i, %s), @done(%s)
}
@body(%bi:l, %bs:l) {
  %off =l shl %bi, 3:l
  %addr =l add %a, %off
  %v =l load %addr
  %s1 =l add %bs, %v
  %i1 =l add %bi, 1:l
  jmp @hdr(%i1, %s1)
}
  jmp @hdr(0:l, 0:l)
}

def sn_lohi : Fn := tqbe $lohi(%x:l) -> l {
  %lo32 =w trunc %x
  %lo =l extuw %lo32
  %hi =l lshr %x, 32:l
  %r =l add %lo, %hi
  ret %r
}

def sn_tbit : Fn := tqbe $tbit(%x:l, %a:l) -> l {
  %m =l and %x, 1:l
  %c =b cnel %m, 0:l
@t { ret %a }
@f { ret 0:l }
  jnz %c, @t, @f
}

def sn_sgt5 : Fn := tqbe $sgt5(%x:l, %a:l) -> l {
  %c =b csgtl %x, 5:l
@t { ret %a }
@f { ret 0:l }
  jnz %c, @t, @f
}

def sn_mixw : Fn := tqbe $mixw(%a:l, %b:l) -> l {
  %a32 =w trunc %a
  %b32 =w trunc %b
  %c =b cultw %a32, %b32
@lt { %b2 =l shl %b, 1:l
  %r =l add %a, %b2
  ret %r }
@ge { ret %b }
  jnz %c, @lt, @ge
}

def sn_add128 : Fn := tqbe $add128(%a0:l, %a1:l, %b0:l, %b1:l) -> (l, l) {
  %lo, %cy =l addc %a0, %b0, false
  %hi, %_ =l addc %a1, %b1, %cy
  ret %lo, %hi
}

def sn_divmod : Fn := tqbe $divmod(%a:l, %b:l) -> (l, l) {
  %q =l udiv %a, %b
  %r =l urem %a, %b
  ret %q, %r
}

def sn_div10 : Fn := tqbe $div10(%a:l) -> l {
  %q =l udiv %a, 10:l
  ret %q
}

def sn_add32 : Fn := tqbe $add32(%a:l, %b:l) -> l {
  %a32 =w trunc %a
  %b32 =w trunc %b
  %s =w add %a32, %b32
  %r =l extuw %s
  ret %r
}

def sn_lowbyte : Fn := tqbe $lowbyte(%x:l) -> l {
  %b =i8 trunc %x
  %r =l extub %b
  ret %r
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

-- Call-free V1 + Kissat benchmark suite: `(fn, forbidIfConv)`.
-- `minsel` & `k_bcp_clamp_best` intentionally use `select`; all other snippets forbid `.select`.
def v1Suite : List (Fn × Bool) := [
  (sn_sum, true), (sn_cmp3, true), (sn_tworet, true), (sn_lea3, true),
  (sn_mr, true), (sn_setlt, true), (sn_minsel, false), (sn_m3, true),
  (sn_m4, true), (sn_m1, true), (sn_m2, true), (sn_wsum_rot, true),
  (sn_wsum_hdr, true), (sn_lohi, true), (sn_tbit, true), (sn_sgt5, true),
  (sn_mixw, true), (sn_add128, true), (sn_divmod, true), (sn_div10, true),
  (sn_add32, true), (sn_lowbyte, true),
  (sn_k_ws_check, true), (sn_k_bcp_bin_val, true), (sn_k_bcp_clamp_best, false),
  (sn_k_watch_need, true), (sn_k_sweep_hdr_test, true),
  (LeanQbe.T.Examples.Kissat.kissat_is_ws, true),
  (LeanQbe.T.Examples.Kissat.kissat_is_digit, true)
]

/-! ## 2. 14-Live-Through + Cold-Call Outer Stress Harness (Unmarked & Marked Post-`mid`) -/

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
          Expr.let_ ⟨.add i64, (.var ptr, .imm 104#64, ())⟩ fun (m1, ()) =>
          Expr.store (t := i64) (.imm 1369899010#64) (.var m1) (afterCall rv)
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
    loadChainExpr ptr 0 12 [] fun xs =>
      let x0 := xs.headD ptr; let x1 := (xs.drop 1).headD x0
      let x2 := (xs.drop 2).headD x1; let x3 := (xs.drop 3).headD x2
      let afterStart (cont : Expr V L [i64]) : Expr V L [i64] :=
        if marked then
          Expr.let_ ⟨.add i64, (.var ptr, .imm 96#64, ())⟩ fun (m0, ()) =>
          Expr.store (t := i64) (.imm 1369899009#64) (.var m0) cont
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

def isMarkerMov (val : Int64) : Instr → Bool
  | .regular _ _ (.mov _ (.imm (.int64 c))) => c == val
  | _ => false

def countMarkedInSp (ds : List XDir) : Nat :=
  let ds0 := stripNops ds
  let rec go (inReg : Bool) (inSp : Nat) : List XDir → Nat
    | [] => inSp
    | .instr ins :: rest =>
      if isMarkerMov 1369899009 ins then go true 0 rest
      else if isMarkerMov 1369899010 ins then inSp
      else if inReg then go true (inSp + (if isBodySpillInstr ins then 1 else 0)) rest
      else go false inSp rest
    | _ :: rest => go inReg inSp rest
  go false 0 ds0

-- Call-free V1 + Kissat subset that passes Tier-1 exact `liftSnippet` (`AsmIso` round-trip):
def tier1IsoSnippets : List Fn := [
  sn_sum, sn_cmp3, sn_tworet, sn_lea3, sn_mr, sn_minsel, sn_m3, sn_m1, sn_m2,
  sn_wsum_rot, sn_wsum_hdr, sn_lohi, sn_sgt5, sn_mixw, sn_lowbyte
]

def runStressEntry (s : Fn) (forbidIf : Bool) (marked : Bool) : Bool :=
  let sMid := s.midPolicy x64LegalTarget SnippetOptPolicy.predictable
  let hBase := Spill.hints x64Isa sMid
  match Rega.lowerFn x64Isa hBase sMid.ext sMid with
  | .error _ => false
  | .ok baseDirs =>
    if (profileDirs baseDirs true).spills > 0 then false
    else
      let caller := makeStressHarness s.name s.as s.rs marked
      let m : Module := { fns := [makeColdHelper, s, caller] }
      let polOf (nm : Sym) : SnippetOptPolicy :=
        if nm == s.name then .predictable else .default
      let mLate := m.midThenLateInline x64LegalTarget polOf (lateInlineSnippetsPolicy [s.name])
      let outerLate := (mLate.fns.find? (·.name == "__caller")).getD caller
      let hOuterAuto := Spill.hints x64Isa outerLate
      match splice_snippet_hints x64Isa sMid outerLate hOuterAuto [] (some hBase) with
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
  let sMid := s.midPolicy x64LegalTarget SnippetOptPolicy.predictable
  let hBase := Spill.hints x64Isa sMid
  match Rega.lowerFn x64Isa hBase sMid.ext sMid with
  | .error _ => false
  | .ok baseDirs =>
    match liftSnippet s.name sMid.as sMid.rs baseDirs with
    | .ok res => res.iso.passed
    | .error _ => false

def liftIsoVerdictKind (s : Fn) : Option String :=
  let sMid := s.midPolicy x64LegalTarget SnippetOptPolicy.predictable
  let hBase := Spill.hints x64Isa sMid
  match Rega.lowerFn x64Isa hBase sMid.ext sMid with
  | .error _ => none
  | .ok baseDirs =>
    match liftSnippet s.name sMid.as sMid.rs baseDirs with
    | .error e => some s!"err:{e}"
    | .ok res =>
      if res.iso.passed then some "pass"
      else match res.iso with
        | .fail k _ => some k
        | _ => some "pass"

-- All 29 call-free V1 + Kissat snippets achieve `inSp = 0` inside both marked and unmarked
-- 14-live-through + cold-call outer fns via post-`mid` `lateInline` + `splice_snippet_hints`!
#guard v1Suite.all (fun (s, fIf) => runStressEntry s fIf true && runStressEntry s fIf false)

-- All 15 Tier-1 call-free V1 snippets pass strict `liftSnippet` (`AsmIso`) round-trip check!
#guard tier1IsoSnippets.all runLiftIsoCheck

-- Diagnostic `AsmIso` regression checks: G1/G2 bool materialization, mov-copy diffs, errors.
#guard liftIsoVerdictKind sn_setlt == some "extra_mov_copy"
#guard liftIsoVerdictKind sn_add32 == some "extra_mov_copy"
#guard liftIsoVerdictKind sn_tbit == some "extra_mov_copy"
#guard liftIsoVerdictKind LeanQbe.T.Examples.Kissat.kissat_is_ws == some "bool_movzx_chain"
#guard liftIsoVerdictKind LeanQbe.T.Examples.Kissat.kissat_is_digit == some "bool_movzx_chain"
#guard (liftIsoVerdictKind sn_div10).any (·.startsWith "err:")
#guard (liftIsoVerdictKind sn_add128).any (·.startsWith "err:")

-- Negative fail-loud checks on `sn_callinc`:
-- When inlined, BOTH `splice_snippet_hints` (`snippet_contains_call`) AND `auditSnippetInOuter`
-- (`call_in_snippet`) reject it loudly!
#guard
  let sMid := sn_callinc.midPolicy x64LegalTarget .predictable
  let hBase := Spill.hints x64Isa sMid
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
      maxTotalDup := 10000, leafNoLoopMaxDup := 10000, maxCallerCalls := 10,
      exemptNoLoopMax := 10000
  }
  let mForce := m.midThenLateInline x64LegalTarget polOf forcePol
  let outerForce := (mForce.fns.find? (·.name == "__caller")).getD caller
  let hOuterForce := Spill.hints x64Isa outerForce
  let spliceRejected :=
    match splice_snippet_hints x64Isa sMid outerForce hOuterForce [] (some hBase) with
    | .error "snippet_contains_call" => true
    | _ => false
  let auditRejected :=
    match auditSnippetInOuter x64Isa sMid outerForce hOuterForce
        (SnippetBudget.predictable "callinc") with
    | .error ds => ds.any (·.kind == "call_in_snippet")
    | .ok _ => false
  spliceRejected && auditRejected

-- Standalone Kissat `plain_red_less` lowers cleanly under `Fn.midPolicy`
-- with zero calls under `SnippetOptPolicy.predictable`.
#guard
  let fn : Fn :=
    ⟨"plain_red_less", [i64, i32, i32], [.bool],
      LeanQbe.T.Examples.Kissat.Plain.plain_red_less_body⟩
  let fnMid := fn.midPolicy x64LegalTarget .predictable
  let h := Spill.hints x64Isa fnMid
  match Rega.lowerFn x64Isa h fnMid.ext fnMid with
  | .ok ds => (profileDirs ds true).calls == 0 && (profileDirs ds true).bodyInsns > 0
  | .error _ => false

/-! ## 3. Certified `compileLateInlined` + `splice_snippet_hints` + `x64Init` Proof (`std3`) -/

def certColdFn : Fn := makeColdHelper
def certWsFn : Fn := sn_k_ws_check
def certCallerFn : Fn :=
  { makeStressHarness certWsFn.name certWsFn.as certWsFn.rs false with name := "caller14" }

def certModX64 : Module :=
  { fns := [certColdFn, certWsFn, certCallerFn] }

def certPolicyX64 (s : Sym) : SnippetOptPolicy :=
  if s == "k_ws_check" then .predictable else .default

def certInlPolX64 : InlinePolicy :=
  lateInlineSnippetsPolicy ["k_ws_check"]

def computeCertHintsX64 : Except String (List x64Isa.Hints) := do
  let mMid := certModX64.midPolicy x64LegalTarget certPolicyX64
  let mLate := mMid.lateInline certInlPolX64
  let sMid := mMid.fns.getD 1 certWsFn
  let hSnip := Spill.hints x64Isa sMid
  mLate.fns.mapM fun f => do
    let hAuto := Spill.hints x64Isa f
    if f.name == "caller14" then
      let (hSpliced, _) ← splice_snippet_hints x64Isa sMid f hAuto [] (some hSnip)
      pure hSpliced
    else
      pure hAuto

def computeCertX64Bundle :
    Except String (List x64Isa.Hints × List x64Isa.Directive × List (Sym × Nat)) := do
  let hs ← computeCertHintsX64
  let (code, bounds) ← compileLateInlined x64Isa x64LegalTarget x64Target.frame.raBytes
    [] [] 0 certModX64 certPolicyX64 certInlPolX64 hs
  pure (hs, code, bounds)

meta section
open Lean Elab Command Term Meta

def addLitDefX64 (declNm : Name) (ty val : Lean.Expr) : CoreM Unit := do
  let decl := Declaration.defnDecl {
    name := declNm, levelParams := [], type := ty, value := val,
    hints := .abbrev, safety := .safe }
  addDecl decl (forceExpose := true)
  compileDecl decl

elab "splice_x64_late_cert " hintsId:ident codeId:ident boundsId:ident : command => do
  let ns ← getCurrNamespace
  let evalRes ← liftTermElabM do
    let resTy :=
      mkApp2 (mkConst ``Except [.zero, .zero]) (mkConst ``String)
        (mkApp2 (mkConst ``Prod [.zero, .zero])
          (mkApp (mkConst ``List [.zero])
            (mkApp (mkConst ``LeanQbe.T.Isa.Hints) (mkConst ``LeanQbe.T.Amd64.x64Isa)))
          (mkApp2 (mkConst ``Prod [.zero, .zero])
            (mkApp (mkConst ``List [.zero])
              (mkApp (mkConst ``LeanQbe.T.Isa.Directive) (mkConst ``LeanQbe.T.Amd64.x64Isa)))
            (mkApp (mkConst ``List [.zero])
              (mkApp2 (mkConst ``Prod [.zero, .zero])
                (mkConst ``LeanQbe.T.Sym) (mkConst ``Nat)))))
    unsafe evalExpr
      (Except String (List x64Isa.Hints × List x64Isa.Directive × List (Sym × Nat)))
      resTy (mkConst ``LeanQbeTest.T.SnippetPhase1X64Test.computeCertX64Bundle)
  match evalRes with
  | .error e => throwError "splice_x64_late_cert: {e}"
  | .ok (hs, code, bounds) =>
    let hTy := mkApp (mkConst ``List [.zero])
      (mkApp (mkConst ``LeanQbe.T.Isa.Hints) (mkConst ``LeanQbe.T.Amd64.x64Isa))
    let cTy := mkApp (mkConst ``List [.zero])
      (mkApp (mkConst ``LeanQbe.T.Isa.Directive) (mkConst ``LeanQbe.T.Amd64.x64Isa))
    let symNatTy := mkApp2 (mkConst ``Prod [.zero, .zero])
      (mkConst ``LeanQbe.T.Sym) (mkConst ``Nat)
    let bTy := mkApp (mkConst ``List [.zero]) symNatTy
    liftCoreM do
      addLitDefX64 (ns ++ hintsId.getId) hTy (Lean.toExpr hs)
      addLitDefX64 (ns ++ codeId.getId) cTy (Lean.toExpr code)
      addLitDefX64 (ns ++ boundsId.getId) bTy (Lean.toExpr bounds)

end

splice_x64_late_cert certHintsX64 certCodeX64 certBoundsX64

theorem certX64_cm :
    compileLateInlined x64Isa x64LegalTarget x64Target.frame.raBytes
      [] [] 0 certModX64 certPolicyX64 certInlPolX64 certHintsX64 =
      .ok (certCodeX64, certBoundsX64) := by
  t_kernel_rfl

-- Verify `inSp = 0` inside `caller14` for the literal spliced cert hints too!
#guard
  let mMid := certModX64.midPolicy x64LegalTarget certPolicyX64
  let mLate := mMid.lateInline certInlPolX64
  let sMid := mMid.fns.getD 1 certWsFn
  let outerLate := mLate.fns.getD 2 certCallerFn
  let hOuter := certHintsX64.getD 2 (Spill.hints x64Isa outerLate)
  match checkRegaAndBudget sMid outerLate hOuter (SnippetBudget.predictable "k_ws_check") with
  | .ok (_, rep) => rep.interiorSpills == 0
  | .error _ => false

theorem certX64_small : x64Layout.progSmall (certCodeX64 ++ []) = true := by t_kernel_rfl

@[instance_reducible] def certHostX64 : x64Target.mach.Host :=
  x64Layout.layoutOf (certCodeX64 ++ []) certX64_small

theorem certX64_labelsUnique : x64Target.LabelsUnique certHostX64 := by
  have hcm : compileDirectModule x64Isa x64Target.frame.raBytes [] [] 0
      (certModX64.midThenLateInline x64LegalTarget certPolicyX64 certInlPolX64).fns certHintsX64 =
      .ok (certCodeX64, certBoundsX64) := by
    have h := certX64_cm
    dsimp only [compileLateInlined] at h
    split at h
    · exact h
    · cases h
  refine compileDirectModule_labelsUnique x64LabelClean certHostX64 ?_ hcm ?_ ?_
  · rw [certHostX64]
    exact x64Layout.prog_layoutOf (certCodeX64 ++ []) certX64_small
  · rw [certModX64.midThenLateInline_fns_names x64LegalTarget certPolicyX64 certInlPolX64]
    decide
  · rw [certModX64.midThenLateInline_fns_names x64LegalTarget certPolicyX64 certInlPolX64]
    decide

theorem certModX64_acyclic : certModX64.checkAcyclic = true := by t_kernel_rfl

theorem certColdFn_wf : certColdFn.Wf := by t_wf_reify
theorem certWsFn_wf : certWsFn.Wf := by t_wf_reify
theorem certCallerFn_wf : certCallerFn.Wf := by t_wf_reify

theorem certModX64_wf : ∀ f ∈ certModX64.fns, f.Wf := by
  intro f hf
  simp only [certModX64, List.mem_cons, List.not_mem_nil, or_false] at hf
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

def caller14Val (xs : List (BitVec 64)) (k : BitVec 64) : BitVec 64 :=
  let x0 := xs.headD 0#64
  let ws := wsCheckVal x0
  let rvFin := if k == 0#64 then ws + x0 else ws
  foldXor (rvFin :: xs)

def coldSpec : Spec [i64, i64, i64, i64, i64] [i64] := fun (a, b, _, _, _, ()) m Q _ =>
  Q (a + b, ()) m

def wsSpec : Spec [i64] [i64] := fun (c64, ()) m Q _ =>
  Q (wsCheckVal c64, ()) m

def caller14Spec : Spec [i64, i64] [i64] := fun (ptr, k, ()) m Q _ =>
  ∃ (xs : List (BitVec 64)) (R : Mem 64 → Prop), xs.length = 12 ∧ (m =⋆ array64 ptr xs ⋆ R) ∧
    Q (caller14Val xs k, ()) m

def certΓX64 : Env
  | "cold_helper", [.bits 64, .bits 64, .bits 64, .bits 64, .bits 64], [.bits 64], xs, m, Q, X =>
      coldSpec xs m Q X
  | "k_ws_check", [.bits 64], [.bits 64], xs, m, Q, X => wsSpec xs m Q X
  | "caller14", [.bits 64, .bits 64], [.bits 64], xs, m, Q, X => caller14Spec xs m Q X
  | _, _, _, _, _, _, _ => False

private theorem bool_ofNat_64 (b : Bool) : BitVec.ofNat 64 b.toNat = if b then 1#64 else 0#64 := by
  cases b <;> decide

private theorem liftCmp_eq_bits {n : Nat} (a b : BitVec n) :
    liftCmp (fun {_} => CmpOp.eq.evalBits) CmpOp.eq.evalBool (.bits n) a b = (a == b) := rfl

private theorem certColdFn_wp {xs : Tup Val [i64, i64, i64, i64, i64]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} (h : coldSpec xs m Q X) :
    Func.wp certΓX64 certColdFn.body xs m Q X := by
  rcases xs with ⟨a, b, _, _, _, ⟨⟩⟩
  exact h

private theorem certWsFn_wp {xs : Tup Val [i64]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} (h : wsSpec xs m Q X) :
    Func.wp certΓX64 certWsFn.body xs m Q X := by
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
    {Q : Post [i64]} {X : XPost} (h : caller14Spec xs m Q X) :
    Func.wp certΓX64 certCallerFn.body xs m Q X := by
  rcases xs with ⟨ptr, k, ⟨⟩⟩
  rcases h with ⟨ys, R, hlen, hm, hQ⟩
  rcases ys with _ | ⟨y0, ys'⟩
  · simp at hlen
  dsimp only [Func.wp, certCallerFn, makeStressHarness, i64]
  refine loadChainExpr_wp certΓX64 Q X m hm _ 12 0 [] (by omega) rfl ?_
  rw [show (y0 :: ys').take (0 + 12) = y0 :: ys' from List.take_of_length_le (by omega)]
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
    exact xorListExpr_cons_wp certΓX64 Q X m ptr rvFin (y0 :: ys')
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
    simpa [caller14Val, hk] using hQ
  · intro hne
    have hk : (k == 0#64) = false := hne
    refine hret _ ?_
    simpa [caller14Val, hk] using hQ

theorem certModX64_modOk : ModuleOk certΓX64 certModX64 := by
  refine Module.moduleOk_of_checkAcyclic certModX64_acyclic certModX64_wf ?_
  intro f hf xs m Q X hΓ
  simp only [certModX64, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · dsimp only [certΓX64, certColdFn, makeColdHelper, i64] at hΓ
    exact certColdFn_wp hΓ
  · dsimp only [certΓX64, certWsFn, sn_k_ws_check, i64] at hΓ
    exact certWsFn_wp hΓ
  · dsimp only [certΓX64, certCallerFn, makeStressHarness, i64] at hΓ
    exact certCallerFn_wp hΓ

theorem certX64_caller_fnSpec :
    x64Target.Defined certHostX64 "caller14" ∧
      x64Target.FnSpec certHostX64 "caller14" caller14Spec
        (lookupFnBound certBoundsX64 "caller14").get! 0 := by
  have hmem : ("caller14", (lookupFnBound certBoundsX64 "caller14").get!) ∈ certBoundsX64 :=
    of_decide_eq_true (by t_kernel_rfl)
  obtain ⟨f, hf, hnm, hdef, hspec⟩ := compileLateInlined_sound x64Target certHostX64
    x64LegalTarget certModX64 certPolicyX64 certInlPolX64 certΓX64 [] [] 0 certHintsX64
    certCodeX64 certBoundsX64 0 certX64_cm
    ⟨[], by
      change certCodeX64 ++ [] =
        x64Target.mach.prog (x64Layout.layoutOf (certCodeX64 ++ []) certX64_small)
      exact (x64Layout.prog_layoutOf (certCodeX64 ++ []) certX64_small).symm⟩
    certX64_labelsUnique certModX64_modOk (fun _ hx => nomatch hx)
    (And.intro (fun _ hx => nomatch hx) (fun _ hx => nomatch hx)) (fun _ hx => nomatch hx)
    _ hmem
  have hfnEq : f = certCallerFn := by
    simp only [certModX64, List.mem_cons, List.not_mem_nil, or_false] at hf
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
    dsimp only [certModX64, Module.sigs, List.map, Fn.sig, certCallerFn, makeStressHarness]
    exact .tail _ (.tail _ (.head _))

def sampleWords12 : List (BitVec 64) :=
  [32#64, 1#64, 2#64, 3#64, 4#64, 5#64, 6#64, 7#64, 8#64, 9#64, 10#64, 11#64]

theorem certX64_eventually_fast (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hrdi : s.regs.get64 .rdi = 0x1000#64) (hrsi : s.regs.get64 .rsi = 1#64)
    (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hmem : s.dmem =⋆ array64 0x1000#64 sampleWords12 ⋆
      (region (s.regs.get64 .rsp - BitVec.ofNat 64 (lookupFnBound certBoundsX64 "caller14").get!)
          (lookupFnBound certBoundsX64 "caller14").get! ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) :
    Eventually (x64Target.mach.step certHostX64)
      (fun st => st.pc = ra ∧ st.data.regs.get64 .rax = caller14Val sampleWords12 1#64)
      ⟨s, x64Target.mach.labelAddr certHostX64 "caller14"⟩ := by
  have hfn := certX64_caller_fnSpec.2
  have hargs : x64Target.ArgsIn (as := [i64, i64]) (0x1000#64, 1#64, ()) s :=
    ⟨_, rfl, .cons ⟨by decide, by simpa using hrdi⟩
      (.cons ⟨by decide, by simpa using hrsi⟩ .nil)⟩
  obtain ⟨mf, mR, hu1, hd1, ⟨mArr, f, hu2, hd2, hmArr, hf⟩, hmRest⟩ := hmem
  have hmEq : s.dmem =⋆ Eq mArr ⋆
      (region (s.regs.get64 .rsp - BitVec.ofNat 64 (lookupFnBound certBoundsX64 "caller14").get!)
          (lookupFnBound certBoundsX64 "caller14").get! ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R :=
    ⟨mf, mR, hu1, hd1, ⟨mArr, f, hu2, hd2, rfl, hf⟩, hmRest⟩
  have hspec : caller14Spec (0x1000#64, 1#64, ()) mArr
      (fun r _ => r = (caller14Val sampleWords12 1#64, ())) (fun _ _ _ _ => False) :=
    ⟨sampleWords12, emp, rfl, by rwa [sep_emp], rfl⟩
  refine eventually_weaken _ _ _ _ ?_
    (@x64_of_returns certHostX64 _ _ _ _ _ _ hfn _ _ _ hspec s ra R hargs hsp hmEq)
  rintro st ⟨hpc, _, _, _, _, rfl, hrets, _⟩
  exact ⟨hpc, x64Init.retsIn_singleton (caller14Val sampleWords12 1#64) st.data hrets⟩

/-! ## 4. Standard-Axiom (`std3`) Audit -/

#print axioms certX64_cm
#print axioms certX64_labelsUnique
#print axioms certX64_caller_fnSpec
#print axioms certX64_eventually_fast

end LeanQbeTest.T.SnippetPhase1X64Test
