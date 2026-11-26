module

public import LeanQbe.T.Amd64.Base
public import LeanQbe.T.IselStepAttr

/-!
# Typed x64 Scalar Zero-Idiom Helper (`Amd64.IselZero`)

Defines `x64InsI`, `fitsUImm32`, `moviI`, and `x64MoviDeadFlags` (emitting 2-byte
`xorl %ed, %ed` with `maskAll` when `c == 0#64` and flags are dead, falling back to `moviI`
with `maskNone` otherwise).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Amd64

/-- Width-indexed 64-bit-addressed instruction constructor. -/
abbrev x64InsI (w : Width) (op : Operation w) : Instr := .regular .W64 w op

/-- Whether `c` fits in a zero-extended 32-bit immediate (`0 .. 2^32 - 1`). -/
def fitsUImm32 (c : BitVec 64) : Bool :=
  (c >>> 32) == 0#64

/-- `mov $c, %rd` (5-byte `movl` when `0 ≤ c < 2^32`, else `movq`; preserves all status flags). -/
abbrev moviI (rd : Reg64) (c : BitVec 64) : Instr :=
  if fitsUImm32 c then
    x64InsI .W32 (.mov (.reg (d rd)) (.imm (.int64 (Int64.ofBitVec c))))
  else
    x64InsI .W64 (.mov (.reg (q rd)) (.imm (.int64 (Int64.ofBitVec c))))

/-- Load 64-bit constant `c` into `rd` when status flags are statically known dead, emitting
2-byte `xorl %ed, %ed` (`maskAll`) when `c == 0#64` and `moviI` (`maskNone`) otherwise. -/
def x64MoviDeadFlags (rd : Reg64) (c : BitVec 64) : List Directive × FlagMask :=
  if c == 0#64 then
    (emitClean [x64InsI .W32 (.xor (.reg (d rd)) (.reg (d rd)))], maskAll)
  else
    (emitClean [moviI rd c], maskNone)

end LeanQbe.T.Amd64
