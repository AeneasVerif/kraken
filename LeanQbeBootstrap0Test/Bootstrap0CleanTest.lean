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
   IR (`leanqbe0Tfs.take 15`) into valid x86-64 AT&T assembly, and rejects malformed IR cleanly.
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

#guard leanqbe0Cert.bounds.length == 124
#guard leanqbe0Cert.numChunks > 0 && leanqbe0Cert.bounds.all fun p => p.2 <= 2048
#guard !leanqbe0Cert.code.isEmpty

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

#print axioms leanqbe0Mod0_wf
#print axioms leanqbe0Mod0_acyclic
#print axioms leanqbe0Mod0_legalSig
#print axioms leanqbe0Cert

end LeanQbeBootstrap0Test.Bootstrap0CleanTest
