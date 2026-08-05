import Lean
import Std

/--
Architectural operand and register width for AArch64 instructions.
- `W32`: 32-bit register (`W0`-`W30`, `WSP`, `WZR`) or 32-bit operation.
- `W64`: 64-bit register (`X0`-`X30`, `SP`, `XZR`) or 64-bit operation.
-/
inductive Width | W32 | W64 deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

instance : ToString Width where
  toString | .W32 => "w32" | .W64 => "w64"

namespace Width
def bits : Width → Nat | W32 => 32 | W64 => 64
def bytes : Width → Nat | W32 => 4 | W64 => 8
abbrev bytesv (w : Width) {n} : BitVec n := BitVec.ofNat n w.bytes
abbrev type (w : Width) : Type := BitVec w.bits
instance {w : Width} : Coe Bool w.type where coe := fun b : Bool => BitVec.ofNat _ b.toNat
end Width

unif_hint (w : Width) where
  w =?= Width.W32 |- Width.type w =?= BitVec 32

unif_hint (w : Width) where
  w =?= Width.W64 |- Width.type w =?= BitVec 64

/--
AArch64 General Purpose Registers (GPRs) `X0` through `X30`.
-/
inductive XReg
  |  X0 |  X1 |  X2 |  X3 |  X4 |  X5 |  X6 |  X7
  |  X8 |  X9 | X10 | X11 | X12 | X13 | X14 | X15
  | X16 | X17 | X18 | X19 | X20 | X21 | X22 | X23
  | X24 | X25 | X26 | X27 | X28 | X29 | X30
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

/--
GPR or Stack Pointer (`SP`/`WSP`), used in contexts where index 31 means SP.
-/
inductive XRegOrSp
  | reg (_ : XReg)
  | SP
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

/--
GPR or Zero Register (`XZR`/`WZR`), used in contexts where index 31 means ZR.
-/
inductive XRegOrXzr
  | reg (_ : XReg)
  | XZR
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

inductive RegOrSp : Width → Type
  | low (_ : XRegOrSp) (w : Width) : RegOrSp w
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

inductive RegOrZr : Width → Type
  | low (_ : XRegOrXzr) (w : Width) : RegOrZr w
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

instance {w} : Coe XRegOrSp (RegOrSp w) where coe := fun r => .low r w
instance {w} : Coe XRegOrXzr (RegOrZr w) where coe := fun r => .low r w
instance {w} : Coe XReg (RegOrSp w) where coe := fun r => .low (.reg r) w
instance {w} : Coe XReg (RegOrZr w) where coe := fun r => .low (.reg r) w
attribute [coe] XRegOrSp.reg
attribute [coe] XRegOrXzr.reg
attribute [coe] RegOrSp.low
attribute [coe] RegOrZr.low

abbrev Label := String

inductive ConstExpr
  | label (_ : Label)
  | int64 (_ : Int64)
  | before_current_instruction | after_current_instruction
  | add (_ _ : ConstExpr) | sub (_ _ : ConstExpr)
  | pg_hi21 (_ : ConstExpr)
  | lo12 (_ : ConstExpr)
  -- Careful adding operations here! Need to match overflow behavior of all
  -- assemblers we want compatibility with. We assume oversized literals error;
  -- clang and gcc seem to always use 64-bit arithmetic (MCValue has an int64).
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr
instance : Coe Label ConstExpr where coe := .label
instance : Coe Int64 ConstExpr where coe := .int64
instance {n} [OfNat Int64 n] : OfNat ConstExpr n where ofNat := .int64 (OfNat.ofNat n)
attribute [coe] ConstExpr.label
attribute [coe] ConstExpr.int64

structure RegOrSpW where (w : Width) (reg : RegOrSp w)
  deriving Repr, DecidableEq, Hashable, Lean.ToExpr

structure RegOrZrW where (w : Width) (reg : RegOrZr w)
  deriving Repr, DecidableEq, Hashable, Lean.ToExpr

/--
Architectural extension types for arithmetic instructions.
- Supports unsigned/signed byte (`UXTB`, `SXTB`), halfword (`UXTH`, `SXTH`),
  word (`UXTW`, `SXTW`), and doubleword (`UXTX`, `SXTX`). `UXTW` and `UXTX` are
  also aliased as `LSL`, respectively, depending on operand width.
-/
inductive ExtendType | UXTB | SXTB | UXTH | SXTH | UXTW | SXTW | UXTX | SXTX
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

/--
Architectural extension types for memory addressing index registers.
- Supports `UXTW`, `SXTW`, `UXTX`, `SXTX`, `LSL` alias.
- `UXTW`/`SXTW` require a 32-bit index register `Wn`.
- `SXTX`/`UXTX` require a 64-bit index register `Xn`.
-/
inductive MemExtendType | UXTW | SXTW | UXTX | SXTX
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

/--
Shift amount applied after extension in arithmetic instructions.
-/
inductive ExtendAmount | E0 | E1 | E2 | E3 | E4
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

/--
Shift amount applied to index registers in memory addressing.
- Restricted to either unshifted (`E0`, shift `#0` / omitted)
  or scaled by log2 of the access size in bytes:
  - `E2` (`#2`) for 32-bit (`.W32`, 4-byte) operations.
  - `E3` (`#3`) for 64-bit (`.W64`, 8-byte) operations.
-/
inductive MemExtendAmount : Width → Type
  | E0 {w} : MemExtendAmount w
  | E2 : MemExtendAmount .W32
  | E3 : MemExtendAmount .W64
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

/--
Shift types for shifted-register operands.
- `LSL`, `LSR`, `ASR` are allowed in both logical and arithmetic instructions.
- `ROR` (rotate right) is only valid in logical instructions.
-/
inductive ShiftType | LSL | LSR | ASR | ROR
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

/--
Optional shift for immediate operands in arithmetic instructions.
- Immediate values can only be unshifted (`S0`, `LSL #0` / omitted)
  or shifted left by 12 bits (`S12`, `LSL #12`).
-/
inductive ImmShift | S0 | S12
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

/--
Allowed shift amounts for move wide immediate instructions.
- For 32-bit registers (`.W32`): Can shift by `#0` (`LSL0`) or `#16` (`LSL16`).
- For 64-bit registers (`.W64`): Can shift by `#0` (`LSL0`), `#16` (`LSL16`),
  `#32` (`LSL32`), or `#48` (`LSL48`).
-/
inductive MovShift : Width → Type
  | LSL0 {w}  : MovShift w
  | LSL16 {w} : MovShift w
  | LSL32     : MovShift .W64
  | LSL48     : MovShift .W64
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

def MovShift.toNat {w} : MovShift w → Nat
  | .LSL0  => 0
  | .LSL16 => 16
  | .LSL32 => 32
  | .LSL48 => 48

/--
Addressing indexing mode for immediate memory offsets.
- `Pre`: Pre-indexed writeback (`[Xn, #imm]!`). Base updated before access.
- `Post`: Post-indexed writeback (`[Xn], #imm`). Base updated after access.
- `none` (Option.none): Offset addressing (`[Xn, #imm]`) without base writeback.
-/
inductive Index | Pre | Post
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

/-- Combined extension type and shift amount for arithmetic instructions. -/
structure Extend where
  type : ExtendType
  amount : ExtendAmount
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

/-- Combined extension type and shift amount for memory index registers. -/
structure MemExtend (w : Width) where
  type : MemExtendType
  amount : MemExtendAmount w
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

/-- Register operand with extension and shift for arithmetic instructions (`Xm, <extend> #<amount>`). -/
structure ExtRegExpr where
  reg : RegOrZrW
  ext : Extend
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

/-- Register operand with extension and shift for memory addressing (`[Xn, Xm, <extend> #<amount>]`). -/
structure MemExtRegExpr (w : Width) where
  reg : RegOrZrW
  ext : MemExtend w
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

/--
12-bit unsigned immediate operand with optional `LSL #0` or `LSL #12` shift for arithmetic instructions.
- The unsigned immediate `imm` must be in range $[0, 4095]$.
-/
structure ImmExpr (w : Width) where
  imm : ConstExpr -- 12-bit unsigned immediate value, must be in [0, 4095] when evaluated.
  shift : ImmShift
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

/--
Shifted register operand for logical and arithmetic instructions (`Xm, <shift> #<amount>`).
- Shift amount `amount` must be in $[0, 31]$ for 32-bit (`.W32`) operations
  and $[0, 63]$ for 64-bit (`.W64`) operations.
-/
structure ShiftRegExpr (w : Width) where
  reg : RegOrZr w
  amount : Int64 -- Must be in the range $[0, 31]$ for 32-bit instructions and [0, 63] for 64-bit instructions.
  shift : ShiftType
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

/--
Memory access byte offset. Valid architectural ranges depend on the addressing mode and access size:
- **Unsigned scaled offset (`index = none`)**: A multiple of 4 in [0, 16380]
  for 32-bit operations and a multiple of 8 in [0, 32760] for 64-bit operations.
- **Signed unscaled / pre / post-indexed offset**: A 9-bit signed integer in
  $[-256, 255]$ (`index = some .Pre | some .Post` or unscaled `LDUR/STUR`).
- **Load/Store Pair (`LDP/STP`)**: A 7-bit signed integer scaled by instruction
  size, giving $[-256, 252]$ (multiples of 4) for 32-bit and $[-512, 504]$
  (multiples of 8) for 64-bit.
-/
structure ImmAddrExpr (w : Width) where
  imm : ConstExpr
  index : Option Index
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

-- Address given by label (PC relative).
structure LitAddrExpr (w : Width) where
  label : Label
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

-- Value held in literal pool (PC relative).
structure LitPoolExpr (w : Width) where
  expr : ConstExpr
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

inductive CondCode | EQ | NE | CS | CC | MI | PL | VS | VC | HI | LS | GE | LT | GT | LE | AL | NV
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr
abbrev CondCode.HS := CondCode.CS
abbrev CondCode.LO := CondCode.CC

def CondCode.invert : CondCode → CondCode
  | .EQ => .NE | .NE => .EQ
  | .CS => .CC | .CC => .CS
  | .MI => .PL | .PL => .MI
  | .VS => .VC | .VC => .VS
  | .HI => .LS | .LS => .HI
  | .GE => .LT | .LT => .GE
  | .GT => .LE | .LE => .GT
  | .AL => .NV | .NV => .AL

inductive AddrOff w | imm (_ : ImmAddrExpr w) | reg (_ : MemExtRegExpr w)
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr
instance {w} : Coe (ImmAddrExpr w) (AddrOff w) where coe := .imm
instance {w} : Coe (MemExtRegExpr w) (AddrOff w) where coe := .reg
instance {w} : Coe ConstExpr (ImmAddrExpr w) where coe := fun e => { imm := e, index := none }
instance {w} : Coe ConstExpr (AddrOff w) where coe := fun e => .imm { imm := e, index := none }
instance {w} : Coe Int64 (ImmAddrExpr w) where coe := fun i => { imm := .int64 i, index := none }
instance {w} : Coe Int64 (AddrOff w) where coe := fun i => .imm { imm := .int64 i, index := none }
instance {w n} [OfNat Int64 n] : OfNat (ImmAddrExpr w) n where
  ofNat := { imm := .int64 (OfNat.ofNat n), index := none }
instance {w n} [OfNat Int64 n] : OfNat (AddrOff w) n where
  ofNat := .imm { imm := .int64 (OfNat.ofNat n), index := none }
attribute [coe] AddrOff.imm
attribute [coe] AddrOff.reg

inductive Literal w | addr (_ : LitAddrExpr w) | pool (_ : LitPoolExpr w)
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr
instance {w} : Coe (LitAddrExpr w) (Literal w) where coe := .addr
instance {w} : Coe (LitPoolExpr w) (Literal w) where coe := .pool
attribute [coe] Literal.addr
attribute [coe] Literal.pool

structure AddrExpr (w : Width) where
  base : RegOrSp .W64 -- Memory base register is always Xn|SP.
  off : AddrOff w
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

structure UnscaledAddrExpr where
  base : RegOrSp .W64 -- Memory base register is always Xn|SP.
  imm : ConstExpr -- Literal `imm` must be a 9-bit signed unscaled integer in [-256, 255].
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

inductive AddrOrLit w | addr (_ : AddrExpr w) | lit (_ : Literal w)
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr
instance {w} : Coe (AddrExpr w) (AddrOrLit w) where coe := .addr
instance {w} : Coe (Literal w) (AddrOrLit w) where coe := .lit
attribute [coe] AddrOrLit.addr
attribute [coe] AddrOrLit.lit

inductive ExtOrImmReg w | ext (_ : ExtRegExpr) | imm (_ : ImmExpr w)
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr
instance {w} : Coe ExtRegExpr (ExtOrImmReg w) where coe := .ext
instance {w} : Coe (ImmExpr w) (ExtOrImmReg w) where coe := .imm
instance {w} : Coe ConstExpr (ImmExpr w) where coe := fun e => { imm := e, shift := .S0 }
instance {w} : Coe ConstExpr (ExtOrImmReg w) where coe := fun e => .imm { imm := e, shift := .S0 }
instance {w} : Coe Int64 (ImmExpr w) where coe := fun i => { imm := .int64 i, shift := .S0 }
instance {w} : Coe Int64 (ExtOrImmReg w) where coe := fun i => .imm { imm := .int64 i, shift := .S0 }
instance {w n} [OfNat Int64 n] : OfNat (ImmExpr w) n where
  ofNat := { imm := .int64 (OfNat.ofNat n), shift := .S0 }
instance {w n} [OfNat Int64 n] : OfNat (ExtOrImmReg w) n where
  ofNat := .imm { imm := .int64 (OfNat.ofNat n), shift := .S0 }
attribute [coe] ExtOrImmReg.ext
attribute [coe] ExtOrImmReg.imm

instance {w} : Coe (RegOrZr w) (ShiftRegExpr w) where coe := fun r => { reg := r, amount := 0, shift := .LSL }

inductive Operation : Width → Type
  -- Loads and Stores.
  | LDR {w} (dst : RegOrZr w) (src : AddrOrLit w) : Operation w
  | STR {w} (src : RegOrZr w) (dst : AddrExpr w) : Operation w
  | LDUR {w} (dst : RegOrZr w) (src : UnscaledAddrExpr) : Operation w
  | STUR {w} (src : RegOrZr w) (dst : UnscaledAddrExpr) : Operation w
  | LDP {w} (dst1 : RegOrZr w) (dst2 : RegOrZr w) (src : AddrExpr w) : Operation w
  | STP {w} (src1 : RegOrZr w) (src2 : RegOrZr w) (dst : AddrExpr w) : Operation w
  --
  -- Arithmetic (instructions have an extended (_e) and shifted reg (_s) form).
  | ADD_e {w} (dst : RegOrSp w) (src1 : RegOrSp w) (src2 : ExtOrImmReg w) : Operation w
  | ADD_s {w} (dst : RegOrZr w) (src1 : RegOrZr w) (src2 : ShiftRegExpr w) : Operation w
  | ADDS_e {w} (dst : RegOrZr w) (src1 : RegOrSp w) (src2 : ExtOrImmReg w) : Operation w
  | ADDS_s {w} (dst : RegOrZr w) (src1 : RegOrZr w) (src2 : ShiftRegExpr w) : Operation w
  | SUB_e {w} (dst : RegOrSp w) (src1 : RegOrSp w) (src2 : ExtOrImmReg w) : Operation w
  | SUB_s {w} (dst : RegOrZr w) (src1 : RegOrZr w) (src2 : ShiftRegExpr w) : Operation w
  | SUBS_e {w} (dst : RegOrZr w) (src1 : RegOrSp w) (src2 : ExtOrImmReg w) : Operation w
  | SUBS_s {w} (dst : RegOrZr w) (src1 : RegOrZr w) (src2 : ShiftRegExpr w) : Operation w
  --
  -- Carry Arithmetic.
  | ADC {w} (dst : RegOrZr w) (src1 : RegOrZr w) (src2 : RegOrZr w) : Operation w
  | ADCS {w} (dst : RegOrZr w) (src1 : RegOrZr w) (src2 : RegOrZr w) : Operation w
  | SBC {w} (dst : RegOrZr w) (src1 : RegOrZr w) (src2 : RegOrZr w) : Operation w
  | SBCS {w} (dst : RegOrZr w) (src1 : RegOrZr w) (src2 : RegOrZr w) : Operation w
  --
  -- Division.
  | SDIV {w} (dst : RegOrZr w) (src1 : RegOrZr w) (src2 : RegOrZr w) : Operation w
  | UDIV {w} (dst : RegOrZr w) (src1 : RegOrZr w) (src2 : RegOrZr w) : Operation w
  --
  -- Multiply.
  | MADD {w} (dst : RegOrZr w) (src1 : RegOrZr w) (src2 : RegOrZr w) (src3 : RegOrZr w) : Operation w
  | MSUB {w} (dst : RegOrZr w) (src1 : RegOrZr w) (src2 : RegOrZr w) (src3 : RegOrZr w) : Operation w
  | SMULH (dst : RegOrZr .W64) (src1 : RegOrZr .W64) (src2 : RegOrZr .W64) : Operation .W64
  | UMULH (dst : RegOrZr .W64) (src1 : RegOrZr .W64) (src2 : RegOrZr .W64) : Operation .W64
  | SMADDL (dst : RegOrZr .W64) (src1 : RegOrZr .W32) (src2 : RegOrZr .W32) (src3 : RegOrZr .W64) : Operation .W64
  | UMADDL (dst : RegOrZr .W64) (src1 : RegOrZr .W32) (src2 : RegOrZr .W32) (src3 : RegOrZr .W64) : Operation .W64
  | SMSUBL (dst : RegOrZr .W64) (src1 : RegOrZr .W32) (src2 : RegOrZr .W32) (src3 : RegOrZr .W64) : Operation .W64
  | UMSUBL (dst : RegOrZr .W64) (src1 : RegOrZr .W32) (src2 : RegOrZr .W32) (src3 : RegOrZr .W64) : Operation .W64
  --
  -- Logic (instructions have an immediate (_i) and shifted reg (_s) form).
  | AND_i  {w} (dst : RegOrSp w) (src1 : RegOrZr w) (imm : ConstExpr) : Operation w
  | AND_s  {w} (dst : RegOrZr w) (src1 : RegOrZr w) (src2 : ShiftRegExpr w) : Operation w
  | ANDS_i {w} (dst : RegOrZr w) (src1 : RegOrZr w) (imm : ConstExpr) : Operation w
  | ANDS_s {w} (dst : RegOrZr w) (src1 : RegOrZr w) (src2 : ShiftRegExpr w) : Operation w
  | ORR_i  {w} (dst : RegOrSp w) (src1 : RegOrZr w) (imm : ConstExpr) : Operation w
  | ORR_s  {w} (dst : RegOrZr w) (src1 : RegOrZr w) (src2 : ShiftRegExpr w) : Operation w
  | ORN_s  {w} (dst : RegOrZr w) (src1 : RegOrZr w) (src2 : ShiftRegExpr w) : Operation w
  | EOR_i  {w} (dst : RegOrSp w) (src1 : RegOrZr w) (imm : ConstExpr) : Operation w
  | EOR_s  {w} (dst : RegOrZr w) (src1 : RegOrZr w) (src2 : ShiftRegExpr w) : Operation w
  | EON_s  {w} (dst : RegOrZr w) (src1 : RegOrZr w) (src2 : ShiftRegExpr w) : Operation w
  | BIC_s  {w} (dst : RegOrZr w) (src1 : RegOrZr w) (src2 : ShiftRegExpr w) : Operation w
  | BICS_s {w} (dst : RegOrZr w) (src1 : RegOrZr w) (src2 : ShiftRegExpr w) : Operation w
  --
  -- Bitfield & Bit Manipulation.
  | BFM  {w} (dst : RegOrZr w) (src : RegOrZr w) (immr : Nat) (imms : Nat) : Operation w
  | SBFM {w} (dst : RegOrZr w) (src : RegOrZr w) (immr : Nat) (imms : Nat) : Operation w
  | UBFM {w} (dst : RegOrZr w) (src : RegOrZr w) (immr : Nat) (imms : Nat) : Operation w
  | CLZ  {w} (dst : RegOrZr w) (src : RegOrZr w) : Operation w
  | CLS  {w} (dst : RegOrZr w) (src : RegOrZr w) : Operation w
  | RBIT {w} (dst : RegOrZr w) (src : RegOrZr w) : Operation w
  | REV  {w} (dst : RegOrZr w) (src : RegOrZr w) : Operation w
  | REV16 {w} (dst : RegOrZr w) (src : RegOrZr w) : Operation w
  | REV32 (dst : RegOrZr .W64) (src : RegOrZr .W64) : Operation .W64
  | EXTR {w} (dst : RegOrZr w) (src1 : RegOrZr w) (src2 : RegOrZr w) (lsb : Nat) : Operation w
  --
  -- Move Wide Immediates.
  | MOVZ {w} (dst : RegOrZr w) (imm : ConstExpr) (shift : MovShift w) : Operation w
  | MOVK {w} (dst : RegOrZr w) (imm : ConstExpr) (shift : MovShift w) : Operation w
  | MOVN {w} (dst : RegOrZr w) (imm : ConstExpr) (shift : MovShift w) : Operation w
  --
  -- Variable Shifts / Rotates.
  | LSLV {w} (dst : RegOrZr w) (src1 : RegOrZr w) (src2 : RegOrZr w) : Operation w
  | LSRV {w} (dst : RegOrZr w) (src1 : RegOrZr w) (src2 : RegOrZr w) : Operation w
  | ASRV {w} (dst : RegOrZr w) (src1 : RegOrZr w) (src2 : RegOrZr w) : Operation w
  | RORV {w} (dst : RegOrZr w) (src1 : RegOrZr w) (src2 : RegOrZr w) : Operation w
  --
  -- Conditional Select.
  | CSEL {w} (dst : RegOrZr w) (src1 src2 : RegOrZr w) (cond : CondCode) : Operation w
  | CSINC {w} (dst : RegOrZr w) (src1 src2 : RegOrZr w) (cond : CondCode) : Operation w
  | CSINV {w} (dst : RegOrZr w) (src1 src2 : RegOrZr w) (cond : CondCode) : Operation w
  | CSNEG {w} (dst : RegOrZr w) (src1 src2 : RegOrZr w) (cond : CondCode) : Operation w
  --
  -- Conditional Compare (instructions have a reg (_r) and immediate (_i) form).
  | CCMP_reg {w} (src1 : RegOrZr w) (src2 : RegOrZr w) (nzcv : Nat) (cond : CondCode) : Operation w
  | CCMP_imm {w} (src1 : RegOrZr w) (imm : Nat) (nzcv : Nat) (cond : CondCode) : Operation w
  | CCMN_reg {w} (src1 : RegOrZr w) (src2 : RegOrZr w) (nzcv : Nat) (cond : CondCode) : Operation w
  | CCMN_imm {w} (src1 : RegOrZr w) (imm : Nat) (nzcv : Nat) (cond : CondCode) : Operation w
  --
  -- Addressing.
  | ADR (dst : RegOrZr .W64) (target : ConstExpr) : Operation .W64
  | ADRP (dst : RegOrZr .W64) (target : ConstExpr) : Operation .W64
  --
  -- Control flow.
  | B (target : ConstExpr) : Operation .W64
  | B_cond (cond : CondCode) (target : ConstExpr) : Operation .W64
  | BL (target : ConstExpr) : Operation .W64
  | BLR (target : RegOrZr .W64) : Operation .W64
  | BR (target : RegOrZr .W64) : Operation .W64
  | RET (target : RegOrZr .W64) : Operation .W64
  | CBZ {w} (reg : RegOrZr w) (target : ConstExpr) : Operation w
  | CBNZ {w} (reg : RegOrZr w) (target : ConstExpr) : Operation w
  | TBZ {w} (reg : RegOrZr w) (bit : Nat) (target : ConstExpr) : Operation w
  | TBNZ {w} (reg : RegOrZr w) (bit : Nat) (target : ConstExpr) : Operation w
  --
  -- Misc.
  | NOP {w} : Operation w
  deriving Repr, DecidableEq, Hashable, Lean.ToExpr

structure Instr where
  operation_size : Width
  operation : Operation operation_size
  deriving Repr, DecidableEq, Hashable, Lean.ToExpr

instance : Repr ByteArray where reprPrec _ _ := "<opaque byte array>"

deriving instance Lean.ToExpr for ByteArray
inductive Directive
  | instr (_ : Instr)
  | label (_ : Label)
  | byteArray (_ : ByteArray)
  deriving BEq, DecidableEq, Repr, Hashable, Lean.ToExpr

abbrev Program := List Directive
abbrev Executable := Int64 × List (Directive × Nat) -- start and sizes

namespace RegOrSp
@[match_pattern] abbrev X0 := low (.reg .X0) .W64
@[match_pattern] abbrev X1 := low (.reg .X1) .W64
@[match_pattern] abbrev X2 := low (.reg .X2) .W64
@[match_pattern] abbrev X3 := low (.reg .X3) .W64
@[match_pattern] abbrev X4 := low (.reg .X4) .W64
@[match_pattern] abbrev X5 := low (.reg .X5) .W64
@[match_pattern] abbrev X6 := low (.reg .X6) .W64
@[match_pattern] abbrev X7 := low (.reg .X7) .W64
@[match_pattern] abbrev X8 := low (.reg .X8) .W64
@[match_pattern] abbrev X9 := low (.reg .X9) .W64
@[match_pattern] abbrev X10 := low (.reg .X10) .W64
@[match_pattern] abbrev X11 := low (.reg .X11) .W64
@[match_pattern] abbrev X12 := low (.reg .X12) .W64
@[match_pattern] abbrev X13 := low (.reg .X13) .W64
@[match_pattern] abbrev X14 := low (.reg .X14) .W64
@[match_pattern] abbrev X15 := low (.reg .X15) .W64
@[match_pattern] abbrev X16 := low (.reg .X16) .W64
@[match_pattern] abbrev X17 := low (.reg .X17) .W64
@[match_pattern] abbrev X18 := low (.reg .X18) .W64
@[match_pattern] abbrev X19 := low (.reg .X19) .W64
@[match_pattern] abbrev X20 := low (.reg .X20) .W64
@[match_pattern] abbrev X21 := low (.reg .X21) .W64
@[match_pattern] abbrev X22 := low (.reg .X22) .W64
@[match_pattern] abbrev X23 := low (.reg .X23) .W64
@[match_pattern] abbrev X24 := low (.reg .X24) .W64
@[match_pattern] abbrev X25 := low (.reg .X25) .W64
@[match_pattern] abbrev X26 := low (.reg .X26) .W64
@[match_pattern] abbrev X27 := low (.reg .X27) .W64
@[match_pattern] abbrev X28 := low (.reg .X28) .W64
@[match_pattern] abbrev X29 := low (.reg .X29) .W64
@[match_pattern] abbrev X30 := low (.reg .X30) .W64
@[match_pattern] abbrev SP := low .SP .W64

@[match_pattern] abbrev W0 := low (.reg .X0) .W32
@[match_pattern] abbrev W1 := low (.reg .X1) .W32
@[match_pattern] abbrev W2 := low (.reg .X2) .W32
@[match_pattern] abbrev W3 := low (.reg .X3) .W32
@[match_pattern] abbrev W4 := low (.reg .X4) .W32
@[match_pattern] abbrev W5 := low (.reg .X5) .W32
@[match_pattern] abbrev W6 := low (.reg .X6) .W32
@[match_pattern] abbrev W7 := low (.reg .X7) .W32
@[match_pattern] abbrev W8 := low (.reg .X8) .W32
@[match_pattern] abbrev W9 := low (.reg .X9) .W32
@[match_pattern] abbrev W10 := low (.reg .X10) .W32
@[match_pattern] abbrev W11 := low (.reg .X11) .W32
@[match_pattern] abbrev W12 := low (.reg .X12) .W32
@[match_pattern] abbrev W13 := low (.reg .X13) .W32
@[match_pattern] abbrev W14 := low (.reg .X14) .W32
@[match_pattern] abbrev W15 := low (.reg .X15) .W32
@[match_pattern] abbrev W16 := low (.reg .X16) .W32
@[match_pattern] abbrev W17 := low (.reg .X17) .W32
@[match_pattern] abbrev W18 := low (.reg .X18) .W32
@[match_pattern] abbrev W19 := low (.reg .X19) .W32
@[match_pattern] abbrev W20 := low (.reg .X20) .W32
@[match_pattern] abbrev W21 := low (.reg .X21) .W32
@[match_pattern] abbrev W22 := low (.reg .X22) .W32
@[match_pattern] abbrev W23 := low (.reg .X23) .W32
@[match_pattern] abbrev W24 := low (.reg .X24) .W32
@[match_pattern] abbrev W25 := low (.reg .X25) .W32
@[match_pattern] abbrev W26 := low (.reg .X26) .W32
@[match_pattern] abbrev W27 := low (.reg .X27) .W32
@[match_pattern] abbrev W28 := low (.reg .X28) .W32
@[match_pattern] abbrev W29 := low (.reg .X29) .W32
@[match_pattern] abbrev W30 := low (.reg .X30) .W32
@[match_pattern] abbrev WSP := low .SP .W32
end RegOrSp

namespace RegOrZr
@[match_pattern] abbrev X0 := low (.reg .X0) .W64
@[match_pattern] abbrev X1 := low (.reg .X1) .W64
@[match_pattern] abbrev X2 := low (.reg .X2) .W64
@[match_pattern] abbrev X3 := low (.reg .X3) .W64
@[match_pattern] abbrev X4 := low (.reg .X4) .W64
@[match_pattern] abbrev X5 := low (.reg .X5) .W64
@[match_pattern] abbrev X6 := low (.reg .X6) .W64
@[match_pattern] abbrev X7 := low (.reg .X7) .W64
@[match_pattern] abbrev X8 := low (.reg .X8) .W64
@[match_pattern] abbrev X9 := low (.reg .X9) .W64
@[match_pattern] abbrev X10 := low (.reg .X10) .W64
@[match_pattern] abbrev X11 := low (.reg .X11) .W64
@[match_pattern] abbrev X12 := low (.reg .X12) .W64
@[match_pattern] abbrev X13 := low (.reg .X13) .W64
@[match_pattern] abbrev X14 := low (.reg .X14) .W64
@[match_pattern] abbrev X15 := low (.reg .X15) .W64
@[match_pattern] abbrev X16 := low (.reg .X16) .W64
@[match_pattern] abbrev X17 := low (.reg .X17) .W64
@[match_pattern] abbrev X18 := low (.reg .X18) .W64
@[match_pattern] abbrev X19 := low (.reg .X19) .W64
@[match_pattern] abbrev X20 := low (.reg .X20) .W64
@[match_pattern] abbrev X21 := low (.reg .X21) .W64
@[match_pattern] abbrev X22 := low (.reg .X22) .W64
@[match_pattern] abbrev X23 := low (.reg .X23) .W64
@[match_pattern] abbrev X24 := low (.reg .X24) .W64
@[match_pattern] abbrev X25 := low (.reg .X25) .W64
@[match_pattern] abbrev X26 := low (.reg .X26) .W64
@[match_pattern] abbrev X27 := low (.reg .X27) .W64
@[match_pattern] abbrev X28 := low (.reg .X28) .W64
@[match_pattern] abbrev X29 := low (.reg .X29) .W64
@[match_pattern] abbrev X30 := low (.reg .X30) .W64
@[match_pattern] abbrev XZR := low .XZR .W64

@[match_pattern] abbrev W0 := low (.reg .X0) .W32
@[match_pattern] abbrev W1 := low (.reg .X1) .W32
@[match_pattern] abbrev W2 := low (.reg .X2) .W32
@[match_pattern] abbrev W3 := low (.reg .X3) .W32
@[match_pattern] abbrev W4 := low (.reg .X4) .W32
@[match_pattern] abbrev W5 := low (.reg .X5) .W32
@[match_pattern] abbrev W6 := low (.reg .X6) .W32
@[match_pattern] abbrev W7 := low (.reg .X7) .W32
@[match_pattern] abbrev W8 := low (.reg .X8) .W32
@[match_pattern] abbrev W9 := low (.reg .X9) .W32
@[match_pattern] abbrev W10 := low (.reg .X10) .W32
@[match_pattern] abbrev W11 := low (.reg .X11) .W32
@[match_pattern] abbrev W12 := low (.reg .X12) .W32
@[match_pattern] abbrev W13 := low (.reg .X13) .W32
@[match_pattern] abbrev W14 := low (.reg .X14) .W32
@[match_pattern] abbrev W15 := low (.reg .X15) .W32
@[match_pattern] abbrev W16 := low (.reg .X16) .W32
@[match_pattern] abbrev W17 := low (.reg .X17) .W32
@[match_pattern] abbrev W18 := low (.reg .X18) .W32
@[match_pattern] abbrev W19 := low (.reg .X19) .W32
@[match_pattern] abbrev W20 := low (.reg .X20) .W32
@[match_pattern] abbrev W21 := low (.reg .X21) .W32
@[match_pattern] abbrev W22 := low (.reg .X22) .W32
@[match_pattern] abbrev W23 := low (.reg .X23) .W32
@[match_pattern] abbrev W24 := low (.reg .X24) .W32
@[match_pattern] abbrev W25 := low (.reg .X25) .W32
@[match_pattern] abbrev W26 := low (.reg .X26) .W32
@[match_pattern] abbrev W27 := low (.reg .X27) .W32
@[match_pattern] abbrev W28 := low (.reg .X28) .W32
@[match_pattern] abbrev W29 := low (.reg .X29) .W32
@[match_pattern] abbrev W30 := low (.reg .X30) .W32
@[match_pattern] abbrev WZR := low .XZR .W32
end RegOrZr
