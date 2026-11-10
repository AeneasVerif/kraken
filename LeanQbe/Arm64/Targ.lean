module

public import Kraken.AArch64.Semantics
public import LeanQbe.Abi

/-!
# AArch64 registers and basic snippets (QBE `arm64/targ.c`, `arm64/emit.c` in spirit)

The executable part of the AArch64 target that does not depend on the IL operations: register sets
of the AAPCS64 and the snippets for moves, constants, jumps and return, as Kraken AArch64
directives. Operations, loads and stores are in `Isel.lean`. The step lemmas are in
`TargLemmas.lean` and `IselLemmas.lean`, the `Target` instance in `Abi.lean`.

Registers are `XRegOrSp`: `x0` to `x30` and `sp`. Register roles (version 0):

* scratch: `x16`, `x17` (IP0, IP1);
* allocatable: the caller-saved `x0` to `x15` (leaf functions do not save callee-saved registers yet);
* arguments `x0` to `x7`, results `x0`, `x1`;
* callee-saved `x19` to `x29`; `x18` (platform register) and `x30` (link register) are never used;
* stack pointer `sp`.

Encoding choices:

* `mov rd, rs` is `add rd, rs, #0`, which is valid for every pair of registers including `sp`.
* A 64-bit constant is loaded from the literal pool (`ldr r, =c`).
* Operands in `sp` are moved to a scratch register first where an instruction would read register 31
  as `xzr`.
* Frames (version 1) use immediate forms only: `sub sp, sp, #F` and `[sp, #8i]`. A frame of 4096
  bytes or more does not assemble (a loud failure at assembly time, like an out-of-range branch).
-/

@[expose] public section

namespace LeanQbe.Arm64

/-- General-purpose registers as the lowering sees them. -/
abbrev Reg := XRegOrSp

/-- An instruction of operation width `w`. -/
abbrev ins {w : RegWidth} (op : Operation w) : Directive :=
  .instr { operation_size := w, operation := op }

/-- `x r` or `w r`, in a position where register 31 would be `xzr`. -/
abbrev zr (r : XReg) (w : RegWidth) : RegOrZr w := .low (.reg r) w

/-- `xzr` or `wzr`. -/
abbrev xzr (w : RegWidth) : RegOrZr w := .low .XZR w

/-- The immediate `#0` of an arithmetic instruction. -/
abbrev imm0 : ExtOrImmReg := .imm { imm := .int64 0, shift := .S0 }

/-- A register operand with no shift. -/
abbrev sh {w : RegWidth} (r : XReg) : ShiftRegExpr w := { reg := zr r w, amount := 0, shift := .LSL }

/-- `[r]`: base register `r`, offset 0. -/
abbrev atReg (r : XReg) : AddrExpr := { base := .low (.reg r) .W64, off := .imm { imm := .int64 0, index := none } }

/-- `mov rd, rs`, encoded as `add rd, rs, #0` (valid for `sp` on either side). -/
def mov (rd rs : Reg) : List Directive := [ins (w := .W64) (.ADD_e (.low rd .W64) (.low rs .W64) imm0)]

/-- `ldr r, =c`: load the 64-bit constant `c` from the literal pool (an assembler pseudo-instruction;
Kraken's semantics returns the constant directly). -/
def movImm (r : XReg) (c : Val) : List Directive :=
  [ins (w := .W64) (.LDR (zr r .W64) (.lit (.pool { expr := .int64 (Int64.ofBitVec c) })))]

/-- `rd := c` (through `x16` if `rd` is `sp`). -/
def movi (rd : Reg) (c : Val) : List Directive :=
  match rd with
  | .reg r => movImm r c
  | .SP => movImm .X16 c ++ mov .SP (.reg .X16)

/-- `b l` (the encoding the parser produces). -/
def jmp (l : String) : List Directive := [ins (w := .W64) (.B (.label l))]

/-- `cbnz w_r, l`: jump if the low 32 bits of `r` are nonzero (QBE's `jnz`). -/
def jnz (r : Reg) (l : String) : List Directive :=
  match r with
  | .reg x => [ins (w := .W32) (.CBNZ (zr x .W32) (.label l))]
  | .SP => mov (.reg .X16) .SP ++ [ins (w := .W32) (.CBNZ (zr .X16 .W32) (.label l))]

/-- `ret` (to `x30`). -/
def ret : List Directive := [ins (w := .W64) (.RET (zr .X30 .W64))]

/-! ## Frames and calls (Target v1) -/

/-- Bytes of a frame with `ns` slots and the saved `x30`, rounded up to 16 (AAPCS64 alignment). -/
def frameSize (ns : Nat) : Nat := (8 * ns + 8 + 15) / 16 * 16

/-- `[b, #o]` -/
abbrev atOff (b : Reg) (o : Nat) : AddrExpr :=
  { base := .low b .W64, off := .imm { imm := .int64 (Int64.ofNat o), index := none } }

/-- `sub sp, sp, #n`. The immediate must fit 12 bits (`n < 4096`) to assemble. -/
def subSp (n : Nat) : List Directive :=
  [ins (w := .W64) (.SUB_e (.low .SP .W64) (.low .SP .W64) (.imm { imm := .int64 (Int64.ofNat n), shift := .S0 }))]

/-- `add sp, sp, #n`. The immediate must fit 12 bits (`n < 4096`) to assemble. -/
def addSp (n : Nat) : List Directive :=
  [ins (w := .W64) (.ADD_e (.low .SP .W64) (.low .SP .W64) (.imm { imm := .int64 (Int64.ofNat n), shift := .S0 }))]

/-- `str x_v, [sp, #o]`. The offset must be below 32768 to assemble. -/
def stSp (v : XReg) (o : Nat) : List Directive := [ins (w := .W64) (.STR (zr v .W64) (atOff .SP o))]

/-- `ldr x_d, [sp, #o]`. The offset must be below 32768 to assemble. -/
def ldSp (d : XReg) (o : Nat) : List Directive := [ins (w := .W64) (.LDR (zr d .W64) (.addr (atOff .SP o)))]

/-- `sub sp, sp, #F; str x30, [sp, #8ns]` -/
def prologue (ns : Nat) : List Directive := subSp (frameSize ns) ++ stSp .X30 (8 * ns)

/-- `ldr x30, [sp, #8ns]; add sp, sp, #F` -/
def epilogue (ns : Nat) : List Directive := ldSp .X30 (8 * ns) ++ addSp (frameSize ns)

/-- Slot `i` := `r` (`sp` through `x17`). -/
def slotSt (i : Nat) (r : Reg) : List Directive :=
  match r with
  | .reg x => stSp x (8 * i)
  | .SP => mov (.reg .X17) .SP ++ stSp .X17 (8 * i)

/-- `rd` := slot `i` (`sp` through `x17`). -/
def slotLd (rd : Reg) (i : Nat) : List Directive :=
  match rd with
  | .reg x => ldSp x (8 * i)
  | .SP => ldSp .X17 (8 * i) ++ mov .SP (.reg .X17)

/-- `bl sym` -/
def call (sym : String) : List Directive := [ins (w := .W64) (.BL (.label sym))]

/-- `b sym` -/
def tailJmp (sym : String) : List Directive := [ins (w := .W64) (.B (.label sym))]

def scratch : List Reg := [.reg .X16, .reg .X17]

def allocatable : List Reg :=
  [.reg .X0, .reg .X1, .reg .X2, .reg .X3, .reg .X4, .reg .X5, .reg .X6, .reg .X7,
   .reg .X8, .reg .X9, .reg .X10, .reg .X11, .reg .X12, .reg .X13, .reg .X14, .reg .X15]

def argRegs : List Reg :=
  [.reg .X0, .reg .X1, .reg .X2, .reg .X3, .reg .X4, .reg .X5, .reg .X6, .reg .X7]

def retRegs : List Reg := [.reg .X0, .reg .X1]

def calleeSaved : List Reg :=
  [.reg .X19, .reg .X20, .reg .X21, .reg .X22, .reg .X23, .reg .X24, .reg .X25, .reg .X26,
   .reg .X27, .reg .X28, .reg .X29]

end LeanQbe.Arm64
