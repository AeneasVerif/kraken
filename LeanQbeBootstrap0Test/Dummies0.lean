module

public import LeanQbe.T.Bootstrap0.Types0

/-!
# Dummy Witness AST Modules for `leanqbe0Compile`

Hardcoded first-order `TFlatModule0` test inputs exercising the general compiler end-to-end:
* `dummyAddMod0`: simple 2-arg `b64` addition.
* `dummyLoopMod0`: iterative `sumto(n)` loop via `.group` / `.jump` / `.jnz`.
* `dummyCallTailMod0`: multi-function module exercising `.call`, `.tailCall`, multi-block
  `.group` dispatch, cyclic `.jump` swap moves, signed/unsigned division & shifts, `select`,
  `umulw64`, `zext`/`sext`/`trunc`, `load`/`store`, and dead-slot reuse.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Bootstrap0

/-- `add2(a, b) = a + b` (`sym 0`). -/
def dummyAddFn0 : TFlatFn0 :=
  { name := 0
    as := [.b64, .b64]
    rs := [.b64]
    body :=
      .let1 (.bin .add .b64) [.var 1, .var 0] <|
        .ret [.var 0] }

/-- Single-function `dummyAddMod0`. -/
def dummyAddMod0 : TFlatModule0 :=
  { fns := [dummyAddFn0], externs := [], exits := [] }

/-- `sumto(n) = 1 + 2 + ... + n` via `.group` / `.jump` loop (`sym 0`). -/
def dummySumToFn0 : TFlatFn0 :=
  { name := 0
    as := [.b64]
    rs := [.b64]
    body :=
      let loopBody : TFlat0 :=
        .let1 (.cmp .eq .b64) [.var 1, .immBits .W64 0] <|
          .jnz (.var 0)
            (.ret [.var 1])
            (.let1 (.bin .add .b64) [.var 1, .var 2] <|
              .let1 (.bin .sub .b64) [.var 3, .immBits .W64 1] <|
                .jump 0 [.var 0, .var 1])
      .group [([.b64, .b64], loopBody)] <|
        .jump 0 [.var 0, .immBits .W64 0] }

/-- Single-function `dummyLoopMod0` (`sumto`). -/
def dummyLoopMod0 : TFlatModule0 :=
  { fns := [dummySumToFn0], externs := [], exits := [] }

/-- Helper `leaf_math(x : i64, y : i64) -> i64` exercising scalar ops & dead-slot reuse. -/
def dummyLeafMathFn0 : TFlatFn0 :=
  { name := 0
    as := [.b64, .b64]
    rs := [.b64]
    body :=
      .let1 (.conv .trunc .W64 .W8) [.var 1] <|
        .let1 (.conv .sext .W8 .W64) [.var 0] <|
          .let1 (.div .sdiv .W64) [.var 3, .var 0] <|
            .let1 (.div .srem .W64) [.var 4, .var 1] <|
              .let2Umulw64 (.var 5) (.var 4) <|
                .let1 (.bin .xor .b64) [.var 1, .var 0] <|
                  .let1 (.cmp .slt .b64) [.var 4, .immBits .W64 0] <|
                    .let1 (.select .b64) [.var 0, .var 3, .var 1] <|
                      .let1 (.bin .add .b64) [.var 0, .var 6] <|
                        .ret [.var 0] }

/-- Helper `gcd_like(a : i64, b : i64) -> i64` testing cyclic swap `.jump 1 [b, a % b]`. -/
def dummyGcdLikeFn0 : TFlatFn0 :=
  { name := 1
    as := [.b64, .b64]
    rs := [.b64]
    body :=
      let blkSwap : TFlat0 :=
        .let1 (.cmp .eq .b64) [.var 0, .immBits .W64 0] <|
          .jnz (.var 0)
            (.ret [.var 2])
            (.let1 (.div .urem .W64) [.var 2, .var 1] <|
              .jump 1 [.var 2, .var 0])
      let blkEntry : TFlat0 :=
        .jump 1 [.var 1, .var 0]
      .group [([.b64, .b64], blkSwap), ([.b64, .b64], blkEntry)] <|
        .jump 0 [.var 1, .var 0] }

/-- Entry `dispatch(x : i64, y : i64, ptr : i64) -> i64` testing `.call`, `store`, `load`,
`tailCall`. -/
def dummyDispatchFn0 : TFlatFn0 :=
  { name := 2
    as := [.b64, .b64, .b64]
    rs := [.b64]
    body :=
      .call 0 [.b64, .b64] [.b64] [.var 2, .var 1] <|
        .store .b32 (.immBits .W32 7) (.var 1) <|
          .load .b32 (.var 1) <|
            .let1 (.conv .zext .W32 .W64) [.var 0] <|
              .let1 (.bin .add .b64) [.var 2, .var 0] <|
                .tailCall 1 [.b64, .b64] [.var 0, .var 4] }

/-- Multi-function module exercising calls, tail calls, loops, switches, and memory ops. -/
def dummyCallTailMod0 : TFlatModule0 :=
  { fns := [dummyLeafMathFn0, dummyGcdLikeFn0, dummyDispatchFn0]
    externs := []
    exits := [] }

end LeanQbe.T.Bootstrap0
