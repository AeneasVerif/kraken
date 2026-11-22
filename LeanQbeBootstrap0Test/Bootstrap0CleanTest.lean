module

public import LeanQbe.T.Bootstrap0.Compiler0
public import LeanQbe.T.Bootstrap0.Dummies0
public import LeanQbe.T.Bootstrap0.Bridge0
public import LeanQbe.T.Bootstrap0.Mod0
public import LeanQbe.T.Bootstrap0.Splice0
public import LeanQbe.T.Bootstrap0.Cert
public import Kraken.X64.PrintATT
meta import LeanQbe.T.Bootstrap0.Compiler0
meta import LeanQbe.T.Bootstrap0.Dummies0
meta import LeanQbe.T.Bootstrap0.Bridge0
meta import LeanQbe.T.Bootstrap0.Mod0
meta import LeanQbe.T.Bootstrap0.Splice0
meta import LeanQbe.T.Bootstrap0.Cert
meta import LeanQbe.T.Amd64.Targ
meta import Kraken.X64.PrintATT

/-!
# Bootstrap Stage A (`leanqbe0`) Clean LCNF, Kernel Cert & Assembly Validation Gate

Verifies that `leanqbe0Compile` (general `TFlatModule0 → CompileRes0`):
1. Lowers via `LeanLCNF` with zero closures (`papTargets = []`, `maxAp = 0`), zero globals
   (`consts = 0`, `strs = 0`, `bigNats = 0`), `≤ 125` functions (`124`), `≤ 260` x64 directives per
   function (`over260 = 0`), `Func.checkTFlat = true`, and `checkAcyclic = true`.
2. Compiles end-to-end inside the Lean 4 kernel (`leanqbe0Cert : LinkedCert ... leanqbe0Mod0 ...`).
3. Compiles dummy witness ASTs, exhaustive scalar opcodes, and real bridged `Frontend.C0.TFlatFn`
   IR (`leanqbe0Tfs.take 15` to AT&T, all `124` functions to `Dir0`) into valid x86-64 assembly, and
   rejects malformed IR cleanly.
4. Regression witnesses: multi-block `.group`s (`PrePass0` and `Rega0` must number `vid`s in the
   same block order; exact `Dir0` pin plus reference execution), `.jump`s into `.group`s opened
   after a `.jnz` (`lblSlots` must stay indexed by label id), and `.un .neg .bool` rejection.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbeBootstrap0Test.Bootstrap0CleanTest

open LeanQbe.T
open LeanQbe.T.LeanLCNF
open LeanQbe.T.Amd64
open LeanQbe.T.Bootstrap0

eval_dir_stats! leanqbe0DirStats x64Target x64LegalTarget leanqbe0Mod0 rtExtBounds0 rtExitSyms

#guard leanqbe0LcMod.papTargets.isEmpty
#guard leanqbe0LcMod.maxAp == 0

private def totalGlobalsCount : Nat :=
  let consts := leanqbe0LcMod.decls.filter fun d => d.params.isEmpty && !d.retTy.isScalar
  let allLits := leanqbe0LcMod.decls.map (·.body.lits)
  let strs := dedupStr (allLits.flatMap (·.1))
  let bigNats := dedupNat (allLits.flatMap (·.2))
  consts.length + strs.length + bigNats.length

#guard totalGlobalsCount == 0
#guard leanqbe0Mod0.fns.length <= 125
#guard leanqbe0Mod0.fns.length == 124
#guard leanqbe0DirStats.length == leanqbe0Mod0.fns.length
#guard leanqbe0DirStats.all fun p => p.2 <= 260
#guard leanqbe0Mod0.fns.all fun f => Func.checkTFlat f.body
#guard leanqbe0Mod0.checkAcyclic

example : leanqbe0Cert.bounds.length = 124 := leanqbe0Cert_bounds_len
example : leanqbe0Cert.numChunks > 0 := leanqbe0Cert_numChunks_pos
example : leanqbe0Cert.bounds.all (fun p => Nat.ble p.2 2048) = true := leanqbe0Cert_bounds_le
example : (!leanqbe0Cert.code.isEmpty) = true := leanqbe0Cert_code_nonempty

#guard match leanqbe0Compile dummyAddMod0 with | .ok _ _ => true | .err _ _ => false
#guard match leanqbe0Compile dummyLoopMod0 with | .ok _ _ => true | .err _ _ => false
#guard match leanqbe0Compile dummyCallTailMod0 with | .ok _ _ => true | .err _ _ => false

/-- Exhaustive scalar opcode witness exercising `.un`, `.bin`, `.cmp`, `.select`, `.conv`, `.div`,
`.let2Umulw64`, `.load`, `.store`, `.bool`, `.b8`/`.b16`/`.b32`/`.b64`, `.exit`, and `.hlt`. -/
def dummyAllOpsFn0 : TFlatFn0 :=
  { name := 0
    as := [.bool, .b8, .b16, .b32, .b64, .b64]
    rs := [.b64]
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
  { name := 1
    as := [.bool, .b64]
    rs := [.b64]
    body :=
      .jnz (.var 1)
        (.exit 99 [.b64] [.var 0])
        .hlt }

/-- Combined exhaustive opcode + exit/halt witness module. -/
def dummyAllOpsMod0 : TFlatModule0 :=
  { fns := [dummyAllOpsFn0, dummyExitHltFn0]
    externs := []
    exits := [99] }

private def compileModToATT (m : TFlatModule0) (names : Sym0 → Sym) : Except String String :=
  match leanqbe0Compile m with
  | .ok dirs _ => .ok (Kraken.X64.toATT (toAmd64Program names dirs))
  | .err ec fn => .error s!"err {ec} at fn {fn}"

#guard match compileModToATT dummyAllOpsMod0 (fun s => if s == 99 then "abort" else s!"f_{s}") with
  | .ok s => !s.isEmpty
  | .error _ => false

/-- Negative check: type-mismatched binary operands rejected cleanly with `.err 10 0`. -/
def badTypedMod0 : TFlatModule0 :=
  { fns := [{ name := 0, as := [], rs := [.b64],
              body := .let1 (.bin .add .b64) [.immBits .W32 1, .immBits .W64 2] (.ret [.var 0]) }]
    externs := [], exits := [] }

#guard match leanqbe0Compile badTypedMod0 with | .err 10 0 => true | _ => false

/-- Negative check: duplicate function symbols rejected cleanly with `.err 1 0`. -/
def badDupSymMod0 : TFlatModule0 :=
  { fns := [dummyAddFn0, dummyAddFn0], externs := [], exits := [] }

#guard match leanqbe0Compile badDupSymMod0 with | .err 1 0 => true | _ => false

private def bridgedSelfTest : Except String Bool := do
  let (m0, tbl) ← ofTFlatModule (leanqbe0Tfs.take 15)
  match leanqbe0Compile m0 with
  | .ok dirs _ =>
    let att := Kraken.X64.toATT (toAmd64Program (symNameOf tbl) dirs)
    .ok (!att.isEmpty)
  | .err ec fn => .error s!"bridged err {ec} at {fn}"

#guard match bridgedSelfTest with | .ok b => b | .error _ => false

/-- Full self-compile: all `124` bridged `leanqbe0Tfs` functions pass `Legal0` and compile. -/
private def bridgedSelfAll : Except String Nat := do
  let (m0, _) ← ofTFlatModule leanqbe0Tfs
  match leanqbe0Compile m0 with
  | .ok _ _ => .ok m0.fns.length
  | .err ec fn => .error s!"bridged err {ec} at {fn}"

#guard match bridgedSelfAll with | .ok n => n == 124 | .error _ => false

/-! ## Regression: multi-block `.group` `vid` numbering (`prePushGroup0` / `preEnqueueGroup0`) -/

/-- `group2(c, a, b) = if c then b + a else a` via a 2-block `.group` whose blocks both bind
variables of different liveness (`blk0`: live sum, `blk1`: dead difference). `PrePass0` must visit
`blk0` before `blk1` exactly like `Rega0`, otherwise `uses`/`escaped` are read at swapped `vid`s
(the live sum's store is dropped and a stale slot is returned). -/
def group2Fn0 : TFlatFn0 :=
  { name := 0
    as := [.bool, .b64, .b64]
    rs := [.b64]
    body :=
      let blk0 : TFlat0 :=
        .let1 (.bin .add .b64) [.var 0, .var 2] <|
          .ret [.var 0]
      let blk1 : TFlat0 :=
        .let1 (.bin .sub .b64) [.var 0, .var 1] <|
          .ret [.var 1]
      .group [([.b64], blk0), ([.b64], blk1)] <|
        .jnz (.var 2) (.jump 1 [.var 0]) (.jump 0 [.var 1]) }

/-- Single-function module for `group2Fn0`. -/
def group2Mod0 : TFlatModule0 := { fns := [group2Fn0], externs := [], exits := [] }

/-- Exact directives expected for `group2Mod0` (`5` slots: `c`, `a`, `b`, `blk0`/`blk1` params; the
sum reuses the released `blk0` parameter slot `24(%rsp)`, the dead difference is never stored). -/
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

/-- `group3(c1, c2, a) = if c1 then a + 1 else if c2 then a + 2 else 2 * (a + 3)` via a 3-block
`.group` whose blocks bind `1` live / `1` dead + `1` live / `2` live variables. -/
def group3Fn0 : TFlatFn0 :=
  { name := 0
    as := [.bool, .bool, .b64]
    rs := [.b64]
    body :=
      let blk0 : TFlat0 :=
        .let1 (.bin .add .b64) [.var 0, .immBits .W64 1] <|
          .ret [.var 0]
      let blk1 : TFlat0 :=
        .let1 (.bin .add .b64) [.var 0, .var 0] <|
          .let1 (.bin .add .b64) [.var 1, .immBits .W64 2] <|
            .ret [.var 0]
      let blk2 : TFlat0 :=
        .let1 (.bin .add .b64) [.var 0, .immBits .W64 3] <|
          .let1 (.bin .add .b64) [.var 0, .var 0] <|
            .ret [.var 0]
      .group [([.b64], blk0), ([.b64], blk1), ([.b64], blk2)] <|
        .jnz (.var 2) (.jump 2 [.var 0]) <|
          .jnz (.var 1) (.jump 1 [.var 0]) (.jump 0 [.var 0]) }

/-- Single-function module for `group3Fn0`. -/
def group3Mod0 : TFlatModule0 := { fns := [group3Fn0], externs := [], exits := [] }

/-- State of the reference `Dir0` executor: registers, `%rsp`-relative slots, and zero flag. -/
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

/-- Fuel-bounded reference executor for the slot / `W64` ALU / branch `Dir0` subset emitted for the
`.group` witnesses (returns `%rax` at `.ret`; any other directive fails closed with `none`). -/
private def run0 (all : List Dir0) : Nat → List Dir0 → Cpu0 → Option UInt64
  | 0, _, _ => none
  | _, [], _ => none
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
      else match findLbl0 l all with | some tgt => run0 all fuel tgt s | none => none
    | .jmp l => match findLbl0 l all with | some tgt => run0 all fuel tgt s | none => none
    | .ret => some (s.reg .rax)
    | _ => none

/-- Compile `m` and execute its first function on SysV arguments `(%rdi, %rsi, %rdx)` starting
from poisoned (`0xdeadbeef`) registers and slots. -/
private def runMod0 (m : TFlatModule0) (a0 a1 a2 : UInt64) : Option UInt64 :=
  match leanqbe0Compile m with
  | .ok dirs _ =>
    let reg : Reg64 → UInt64 := fun r =>
      match r with | .rdi => a0 | .rsi => a1 | .rdx => a2 | _ => 0xdeadbeef
    run0 dirs 1000 dirs { reg := reg, slots := Array.replicate 16 0xdeadbeef, zf := false }
  | .err _ _ => none

#guard run0 group2Dirs0 1000 group2Dirs0
  { reg := fun _ => 9, slots := Array.replicate 16 0xdeadbeef, zf := false } == some 18
#guard runMod0 group2Mod0 1 5 7 == some 12
#guard runMod0 group2Mod0 0 5 7 == some 5
#guard runMod0 group3Mod0 1 0 10 == some 11
#guard runMod0 group3Mod0 1 1 10 == some 11
#guard runMod0 group3Mod0 0 1 10 == some 12
#guard runMod0 group3Mod0 0 0 10 == some 26

/-! ## Regression: `.jump` into a `.group` opened after a `.jnz` (`lblSlots` indexing) -/

/-- `jnzGroup(c, a, b) = if c then b else a`: the else-arm opens a `.group` after the `.jnz` label
was allocated, then enters it with a `1`-argument `.jump` (whose parameter move must be emitted). -/
def jnzGroupFn0 : TFlatFn0 :=
  { name := 0
    as := [.bool, .b64, .b64]
    rs := [.b64]
    body :=
      .jnz (.var 2) (.ret [.var 0]) <|
        .group [([.b64], .ret [.var 0])] <|
          .jump 0 [.var 1] }

/-- Single-function module for `jnzGroupFn0`. -/
def jnzGroupMod0 : TFlatModule0 := { fns := [jnzGroupFn0], externs := [], exits := [] }

/-- `jnzGroup2(c1, c2, a) = if c1 then a else if c2 then a - 3 else 30 - a`: a `2`-parameter
`.group` opened after one `.jnz` and entered by multi-argument `.jump`s from both arms of a second
`.jnz` (the staged moves must target the block's own parameter slots, in order). -/
def jnzGroup2Fn0 : TFlatFn0 :=
  { name := 0
    as := [.bool, .bool, .b64]
    rs := [.b64]
    body :=
      let blk : TFlat0 :=
        .let1 (.bin .sub .b64) [.var 1, .var 0] <|
          .ret [.var 0]
      .jnz (.var 2) (.ret [.var 0]) <|
        .group [([.b64, .b64], blk)] <|
          .jnz (.var 1)
            (.jump 0 [.var 0, .immBits .W64 3])
            (.jump 0 [.immBits .W64 30, .var 0]) }

/-- Single-function module for `jnzGroup2Fn0`. -/
def jnzGroup2Mod0 : TFlatModule0 := { fns := [jnzGroup2Fn0], externs := [], exits := [] }

#guard runMod0 jnzGroupMod0 1 5 7 == some 7
#guard runMod0 jnzGroupMod0 0 5 7 == some 5
#guard runMod0 jnzGroup2Mod0 1 0 10 == some 10
#guard runMod0 jnzGroup2Mod0 1 1 10 == some 10
#guard runMod0 jnzGroup2Mod0 0 1 10 == some 7
#guard runMod0 jnzGroup2Mod0 0 0 10 == some 20

/-! ## Regression: `.un .neg .bool` is rejected by `checkOpArith0` -/

/-- Negative check: `.un .neg .bool` rejected cleanly with `.err 10 0` (`negb` would map `true` to
`0xff`, whereas `OpCode.wp (.neg .bool)` is the identity). -/
def badNegBoolMod0 : TFlatModule0 :=
  { fns := [{ name := 0, as := [.bool], rs := [.bool],
              body := .let1 (.un .neg .bool) [.var 0] (.ret [.var 0]) }]
    externs := [], exits := [] }

#guard match leanqbe0Compile badNegBoolMod0 with | .err 10 0 => true | _ => false
#guard !checkOpArith0 [.bool] (.un .neg .bool) [.var 0]
#guard !checkOpArith0 [.bool] (.un .neg .bool) [.immBool true]

/-- Positive check: every other `.un` opcode/type pair (`14` of `15`) is still accepted. -/
def okUnOps0 : List (UnOp0 × Ty0) :=
  [(.copy, .bool), (.not, .bool),
   (.copy, .b8), (.neg, .b8), (.not, .b8), (.copy, .b16), (.neg, .b16), (.not, .b16),
   (.copy, .b32), (.neg, .b32), (.not, .b32), (.copy, .b64), (.neg, .b64), (.not, .b64)]

#guard okUnOps0.all fun p =>
  match leanqbe0Compile
    { fns := [{ name := 0, as := [p.2], rs := [p.2],
                body := .let1 (.un p.1 p.2) [.var 0] (.ret [.var 0]) }]
      externs := [], exits := [] } with
  | .ok _ _ => true
  | .err _ _ => false

#print axioms leanqbe0Mod0_wf
#print axioms leanqbe0Mod0_acyclic
#print axioms leanqbe0Mod0_legalSig
#print axioms leanqbe0Cert

end LeanQbeBootstrap0Test.Bootstrap0CleanTest
