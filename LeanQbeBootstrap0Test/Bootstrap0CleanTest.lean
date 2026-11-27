module

public import LeanQbe.T.Bootstrap0.Compiler0
public import LeanQbeBootstrap0Test.Dummies0
public import LeanQbe.T.Bootstrap0.Bridge0
public import LeanQbe.T.Bootstrap0.Mod0
public import LeanQbe.T.Bootstrap0.Splice0
public import LeanQbe.T.Bootstrap0.Cert
public import Kraken.X64.PrintATT
meta import LeanQbe.T.Bootstrap0.Compiler0
meta import LeanQbeBootstrap0Test.Dummies0
meta import LeanQbe.T.Bootstrap0.Bridge0
meta import LeanQbe.T.Bootstrap0.Mod0
meta import LeanQbe.T.Bootstrap0.Splice0
meta import LeanQbe.T.Bootstrap0.Cert
meta import LeanQbe.T.Amd64.Targ
meta import Kraken.X64.PrintATT

/-!
# Bootstrap Stage A (`leanqbe0`) Clean LCNF, Kernel Cert & Assembly Validation Gate

Verifies that `leanqbe0Compile` (general `TFlatModule0 → CompileRes0`):
1. Lowers via `LeanLCNF` with zero closures (`papTargets = []`, `maxAp = 0`), zero globals,
   `≤ 125` functions (`124`), `≤ 260` x64 directives/fn, `Func.checkTFlat`, `checkAcyclic`.
2. Compiles end-to-end inside the Lean 4 kernel (`leanqbe0Cert : LinkedCert ... leanqbe0Mod0 ...`).
3. Compiles dummy witness ASTs, exhaustive scalar opcodes, and real bridged `Frontend.C0.TFlatFn`
   IR into valid x86-64 assembly, and rejects malformed IR cleanly.
4. Regression witnesses: multi-block `.group`s, `.jump`s into `.group`s opened after a `.jnz`, and
   `.un .neg .bool` rejection.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbeBootstrap0Test.Bootstrap0CleanTest

open LeanQbe.T
open LeanQbe.T.LeanLCNF
open LeanQbe.T.Amd64
open LeanQbe.T.Bootstrap0

eval_dir_stats! leanqbe0DirStats x64Target x64LegalTarget leanqbe0Mod0 rtExtBounds0 rtExitSyms

/-- Count non-scalar constant decls, string literals, and big nat literals in an `LcModule`. -/
def lcGlobalsCount (m : LcModule) : Nat :=
  let consts := m.decls.filter fun d => d.params.isEmpty && !d.retTy.isScalar
  let allLits := m.decls.map (·.body.lits)
  consts.length + (dedupStr (allLits.flatMap (·.1))).length +
    (dedupNat (allLits.flatMap (·.2))).length

local macro "singleFnMod0" fn:term : term =>
  `({ fns := [$fn], externs := [], exits := [] : TFlatModule0 })

private def isCompileOk (m : TFlatModule0) : Bool :=
  match leanqbe0Compile m with | .ok _ _ => true | .err _ _ => false

private def isCompileErr (m : TFlatModule0) (ec fn : UInt32) : Bool :=
  match leanqbe0Compile m with | .err c f => c == ec && f == fn | .ok _ _ => false

#guard leanqbe0LcMod.papTargets.isEmpty && leanqbe0LcMod.maxAp == 0 &&
  lcGlobalsCount leanqbe0LcMod == 0 && leanqbe0Mod0.fns.length == 124 &&
  leanqbe0DirStats.length == leanqbe0Mod0.fns.length &&
  (leanqbe0DirStats.all fun p => p.2 <= 260) &&
  (leanqbe0Mod0.fns.all fun f => Func.checkTFlat f.body) && leanqbe0Mod0.checkAcyclic

example : leanqbe0Cert.bounds.length = 124 := leanqbe0Cert_bounds_len
example : leanqbe0Cert.numChunks > 0 := leanqbe0Cert_numChunks_pos
example : leanqbe0Cert.bounds.all (fun p => Nat.ble p.2 2048) = true := leanqbe0Cert_bounds_le
example : (!leanqbe0Cert.code.isEmpty) = true := leanqbe0Cert_code_nonempty

#guard [dummyAddMod0, dummyLoopMod0, dummyCallTailMod0].all isCompileOk

/-- Exhaustive scalar opcode witness exercising `.un`, `.bin`, `.cmp`, `.select`, `.conv`, `.div`,
`.let2Umulw64`, `.load`, `.store`, `.bool`, `.b8`/`.b16`/`.b32`/`.b64`, `.exit`, and `.hlt`. -/
def dummyAllOpsFn0 : TFlatFn0 :=
  { name := 0, as := [.bool, .b8, .b16, .b32, .b64, .b64], rs := [.b64]
    body :=
      .let1 (.un .not .bool) [.var 5] <|
      .let1 (.bin .xor .bool) [.var 0, .var 6] <|
      .let1 (.un .neg .b8) [.var 6] <|
      .let1 (.bin .shl .b8) [.var 0, .immBits .W8 3] <|
      .let1 (.div .sdiv .W8) [.var 0, .immBits .W8 2] <|
      .let1 (.un .not .b16) [.var 8] <|
      .let1 (.bin .rotr .b16) [.var 0, .immBits .W16 5] <|
      .let1 (.div .udiv .W16) [.var 0, .immBits .W16 3] <|
      .let1 (.cmp .ugt .b16) [.var 0, .immBits .W16 1] <|
      .let1 (.conv .ofBool .W8 .W32) [.var 0] <|
      .let1 (.bin .ashr .b32) [.var 0, .immBits .W32 1] <|
      .let1 (.div .srem .W32) [.var 0, .immBits .W32 7] <|
      .let1 (.conv .sext .W32 .W64) [.var 0] <|
      .let1 (.bin .rotl .b64) [.var 0, .immBits .W64 7] <|
      .let2Umulw64 (.var 0) (.var 15) <|
      .let1 (.select .b64) [.var 7, .var 0, .var 1] <|
      .store .b8 (.immBits .W8 9) (.var 17) <|
      .store .b16 (.immBits .W16 11) (.var 17) <|
      .load .b16 (.var 17) <|
      .let1 (.conv .zext .W16 .W64) [.var 0] <|
      .let1 (.bin .add .b64) [.var 3, .var 0] <|
      .ret [.var 0] }

/-- Dead exit / halt witness checking `.exit` and `.hlt` termination branches. -/
def dummyExitHltFn0 : TFlatFn0 :=
  { name := 1, as := [.bool, .b64], rs := [.b64]
    body := .jnz (.var 1) (.exit 99 [.b64] [.var 0]) .hlt }

/-- Combined exhaustive opcode + exit/halt witness module. -/
def dummyAllOpsMod0 : TFlatModule0 :=
  { fns := [dummyAllOpsFn0, dummyExitHltFn0], externs := [], exits := [99] }

private def compileModToATTOk (m : TFlatModule0) (names : Sym0 → Sym) : Bool :=
  match leanqbe0Compile m with
  | .ok dirs _ => !(Kraken.X64.toATT (toAmd64Program names dirs)).isEmpty
  | .err _ _ => false

#guard compileModToATTOk dummyAllOpsMod0 (fun s => if s == 99 then "abort" else s!"f_{s}")

/-- Negative check: type-mismatched binary operands rejected cleanly with `.err 10 0`. -/
def badTypedMod0 : TFlatModule0 :=
  singleFnMod0 { name := 0, as := [], rs := [.b64]
                 body := .let1 (.bin .add .b64) [.immBits .W32 1, .immBits .W64 2] (.ret [.var 0]) }

/-- Negative check: duplicate function symbols rejected cleanly with `.err 1 0`. -/
def badDupSymMod0 : TFlatModule0 :=
  { fns := [dummyAddFn0, dummyAddFn0], externs := [], exits := [] }

#guard isCompileErr badTypedMod0 10 0 && isCompileErr badDupSymMod0 1 0

private def bridgedSelfTest : Bool :=
  match ofTFlatModule (leanqbe0Tfs.take 15) with
  | .ok (m0, tbl) => compileModToATTOk m0 (symNameOf tbl)
  | .error _ => false

/-- Full self-compile: all `124` bridged `leanqbe0Tfs` functions pass `Legal0` and compile. -/
private def bridgedSelfAll : Nat :=
  match ofTFlatModule leanqbe0Tfs with
  | .ok (m0, _) => if isCompileOk m0 then m0.fns.length else 0
  | .error _ => 0

#guard bridgedSelfTest && bridgedSelfAll == 124

/-! ## Regression: multi-block `.group` `vid` numbering (`prePushGroup0` / `preEnqueueGroup0`) -/

/-- `group2(c, a, b) = if c then b + a else a` via a 2-block `.group` with differing liveness. -/
def group2Fn0 : TFlatFn0 :=
  { name := 0, as := [.bool, .b64, .b64], rs := [.b64]
    body :=
      let blk0 : TFlat0 := .let1 (.bin .add .b64) [.var 0, .var 2] (.ret [.var 0])
      let blk1 : TFlat0 := .let1 (.bin .sub .b64) [.var 0, .var 1] (.ret [.var 1])
      .group [([.b64], blk0), ([.b64], blk1)] <|
        .jnz (.var 2) (.jump 1 [.var 0]) (.jump 0 [.var 1]) }

/-- Single-function module for `group2Fn0`. -/
def group2Mod0 : TFlatModule0 := singleFnMod0 group2Fn0

/-- Exact directives expected for `group2Mod0` (`5` slots). -/
def group2Dirs0 : List Dir0 :=
  [ .label (.sym 0), .spAdd true 40,
    .movzx32 .W8 .rdi .rdi, .stSlot 0 .rdi, .stSlot 8 .rsi, .stSlot 16 .rdx,
    .ldSlot .rax 0, .testbRR .rax .rax, .jcc .nz (.loc 0 3),
    .ldSlot .rax 8, .stSlot 32 .rax, .jmp (.loc 0 2),
    .label (.loc 0 3), .ldSlot .rax 16, .stSlot 24 .rax, .jmp (.loc 0 1),
    .label (.loc 0 1), .ldSlot .rdi 24, .ldSlot .rsi 8,
    .movRR .W64 .rax .rdi, .aluRR .W64 .add .rax .rsi, .stSlot 24 .rax,
    .ldSlot .rax 24, .spAdd false 40, .ret,
    .label (.loc 0 2), .ldSlot .rdi 32, .ldSlot .rsi 16,
    .movRR .W64 .rax .rdi, .aluRR .W64 .sub .rax .rsi,
    .ldSlot .rax 32, .spAdd false 40, .ret ]

#guard match leanqbe0Compile group2Mod0 with
  | .ok dirs 5 => reprStr dirs == reprStr group2Dirs0
  | _ => false

/-- `group3(c1, c2, a) = if c1 then a + 1 else if c2 then a + 2 else 2 * (a + 3)`. -/
def group3Fn0 : TFlatFn0 :=
  { name := 0, as := [.bool, .bool, .b64], rs := [.b64]
    body :=
      let blk0 : TFlat0 := .let1 (.bin .add .b64) [.var 0, .immBits .W64 1] (.ret [.var 0])
      let blk1 : TFlat0 :=
        .let1 (.bin .add .b64) [.var 0, .var 0] <|
        .let1 (.bin .add .b64) [.var 1, .immBits .W64 2] (.ret [.var 0])
      let blk2 : TFlat0 :=
        .let1 (.bin .add .b64) [.var 0, .immBits .W64 3] <|
        .let1 (.bin .add .b64) [.var 0, .var 0] (.ret [.var 0])
      .group [([.b64], blk0), ([.b64], blk1), ([.b64], blk2)] <|
        .jnz (.var 2) (.jump 2 [.var 0]) (.jnz (.var 1) (.jump 1 [.var 0]) (.jump 0 [.var 0])) }

/-- Single-function module for `group3Fn0`. -/
def group3Mod0 : TFlatModule0 := singleFnMod0 group3Fn0

private structure Cpu0 where
  reg : Reg64 → UInt64
  slots : Array UInt64
  zf : Bool

private def Cpu0.set (s : Cpu0) (r : Reg64) (v : UInt64) : Cpu0 :=
  { s with reg := fun r' => if r' == r then v else s.reg r' }

private def lblEq0 : Label0 → Label0 → Bool
  | .sym a, .sym b => a == b
  | .loc f i, .loc g j => f == g && i == j
  | _, _ => false

private def findLbl0 (l : Label0) : List Dir0 → Option (List Dir0)
  | [] => none
  | .label l' :: rest => if lblEq0 l l' then some rest else findLbl0 l rest
  | _ :: rest => findLbl0 l rest

private def run0 (all : List Dir0) : Nat → List Dir0 → Cpu0 → Option UInt64
  | 0, _, _ | _, [], _ => none
  | fuel + 1, d :: rest, s =>
    match d with
    | .label _ | .spAdd _ _ => run0 all fuel rest s
    | .movRR .W64 rd rs => run0 all fuel rest (s.set rd (s.reg rs))
    | .movRI rd imm => run0 all fuel rest (s.set rd imm)
    | .movzx32 .W8 rd rs => run0 all fuel rest (s.set rd (s.reg rs &&& 0xff))
    | .stSlot disp rs =>
      run0 all fuel rest { s with slots := s.slots.set! (disp / 8).toNat (s.reg rs) }
    | .ldSlot rd disp =>
      run0 all fuel rest (s.set rd (s.slots.getD (disp / 8).toNat 0xdeadbeef))
    | .aluRR .W64 .add rd rs => run0 all fuel rest (s.set rd (s.reg rd + s.reg rs))
    | .aluRR .W64 .sub rd rs => run0 all fuel rest (s.set rd (s.reg rd - s.reg rs))
    | .testbRR ra rb =>
      run0 all fuel rest { s with zf := (s.reg ra &&& s.reg rb &&& 0xff) == 0 }
    | .jcc .nz l =>
      if s.zf then run0 all fuel rest s
      else (findLbl0 l all).bind (run0 all fuel · s)
    | .jmp l => (findLbl0 l all).bind (run0 all fuel · s)
    | .ret => some (s.reg .rax)
    | _ => none

private def runMod0 (m : TFlatModule0) (a0 a1 a2 : UInt64) : Option UInt64 :=
  match leanqbe0Compile m with
  | .ok dirs _ =>
    let reg : Reg64 → UInt64 := fun r =>
      match r with | .rdi => a0 | .rsi => a1 | .rdx => a2 | _ => 0xdeadbeef
    run0 dirs 1000 dirs { reg, slots := Array.replicate 16 0xdeadbeef, zf := false }
  | .err _ _ => none

#guard run0 group2Dirs0 1000 group2Dirs0
  { reg := fun _ => 9, slots := Array.replicate 16 0xdeadbeef, zf := false } == some 18
#guard [(1, 5, 7, 12), (0, 5, 7, 5)].all fun (c, a, b, v) => runMod0 group2Mod0 c a b == some v
#guard [(1, 0, 10, 11), (1, 1, 10, 11), (0, 1, 10, 12), (0, 0, 10, 26)].all fun (c, d, a, v) =>
  runMod0 group3Mod0 c d a == some v

/-! ## Regression: `.jump` into a `.group` opened after a `.jnz` (`lblSlots` indexing) -/

/-- `jnzGroup(c, a, b) = if c then b else a`. -/
def jnzGroupFn0 : TFlatFn0 :=
  { name := 0, as := [.bool, .b64, .b64], rs := [.b64]
    body := .jnz (.var 2) (.ret [.var 0]) (.group [([.b64], .ret [.var 0])] (.jump 0 [.var 1])) }

/-- Single-function module for `jnzGroupFn0`. -/
def jnzGroupMod0 : TFlatModule0 := singleFnMod0 jnzGroupFn0

/-- `jnzGroup2(c1, c2, a) = if c1 then a else if c2 then a - 3 else 30 - a`. -/
def jnzGroup2Fn0 : TFlatFn0 :=
  { name := 0, as := [.bool, .bool, .b64], rs := [.b64]
    body :=
      let blk : TFlat0 := .let1 (.bin .sub .b64) [.var 1, .var 0] (.ret [.var 0])
      .jnz (.var 2) (.ret [.var 0]) <|
        .group [([.b64, .b64], blk)] <|
          .jnz (.var 1) (.jump 0 [.var 0, .immBits .W64 3]) (.jump 0 [.immBits .W64 30, .var 0]) }

/-- Single-function module for `jnzGroup2Fn0`. -/
def jnzGroup2Mod0 : TFlatModule0 := singleFnMod0 jnzGroup2Fn0

#guard [(1, 5, 7, 7), (0, 5, 7, 5)].all fun (c, a, b, v) => runMod0 jnzGroupMod0 c a b == some v
#guard [(1, 0, 10, 10), (1, 1, 10, 10), (0, 1, 10, 7), (0, 0, 10, 20)].all fun (c, d, a, v) =>
  runMod0 jnzGroup2Mod0 c d a == some v

/-! ## Regression: `.un .neg .bool` is rejected by `checkOpArith0` -/

/-- Negative check: `.un .neg .bool` rejected cleanly with `.err 10 0`. -/
def badNegBoolMod0 : TFlatModule0 :=
  singleFnMod0 { name := 0, as := [.bool], rs := [.bool]
                 body := .let1 (.un .neg .bool) [.var 0] (.ret [.var 0]) }

#guard isCompileErr badNegBoolMod0 10 0 &&
  !checkOpArith0 [.bool] (.un .neg .bool) [.var 0] &&
  !checkOpArith0 [.bool] (.un .neg .bool) [.immBool true]

/-- Positive check: every other `.un` opcode/type pair (`14` of `15`) is still accepted. -/
def okUnOps0 : List (UnOp0 × Ty0) :=
  [(.copy, .bool), (.not, .bool),
   (.copy, .b8), (.neg, .b8), (.not, .b8), (.copy, .b16), (.neg, .b16), (.not, .b16),
   (.copy, .b32), (.neg, .b32), (.not, .b32), (.copy, .b64), (.neg, .b64), (.not, .b64)]

#guard okUnOps0.all fun p =>
  isCompileOk (singleFnMod0 { name := 0, as := [p.2], rs := [p.2]
                              body := .let1 (.un p.1 p.2) [.var 0] (.ret [.var 0]) })

#print axioms leanqbe0Mod0_wf
#print axioms leanqbe0Mod0_acyclic
#print axioms leanqbe0Mod0_legalSig
#print axioms leanqbe0Cert

end LeanQbeBootstrap0Test.Bootstrap0CleanTest
