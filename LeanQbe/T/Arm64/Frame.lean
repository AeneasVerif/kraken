module

public import LeanQbe.T.Arm64.Base
public import LeanQbe.T.AbiLemmas
public import LeanQbe.T.IselStepAttr

/-!
# AAPCS64 Arm64 Frame ISA (`T11b`)

Defines `armFrame : FrameIsa Reg Directive` implementing AAPCS64 stack frames, slot access,
ABI register canonicalization (`UBFM` / `MOV Wd, Ws`, zero-extending low bits to 64 bits with no
flag clobber), calls (`bl`), tail jumps (`b`), and returns (`ret`).

Frames larger than the 12-bit `ADD`/`SUB` immediate limit (`4096`) and slot offsets beyond the
unsigned scaled 64-bit `LDR`/`STR` limit (`32768`) fall back cleanly via `.X16` literal-pool loads
(`ldr x16, =offset` followed by `[sp, x16]` / `sub sp, sp, x16` / `add sp, sp, x16`), and `.SP`
slot/ABI operations route through scratch `.X16`/`.X17`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64

/-- AAPCS64 16-byte aligned frame size for `ns` 64-bit stack slots plus saved link register `x30`. -/
def armFrameSize (ns : Nat) : Nat :=
  (8 * ns + 8 + 15) / 16 * 16

/-- Boolean check whether `n` fits in an unshifted 12-bit unsigned `ADD`/`SUB` immediate (`< 4096`). -/
abbrev armFitsImm12 (n : Nat) : Bool := Nat.blt n 4096

/-- Boolean check whether byte offset `o` fits in scaled unsigned 64-bit `LDR`/`STR` (`< 32768`). -/
abbrev armFitsMemOff (o : Nat) : Bool := Nat.blt o 32768

/-- 64-bit unsigned-extended arithmetic operand `x_r, uxtx #0`. -/
abbrev armUxtx (r : XReg) : ExtRegExpr :=
  { reg := ⟨.W64, zr r .W64⟩, ext := { type := .UXTX, amount := .E0 } }

/-- 64-bit unsigned-extended memory index operand `x_r, uxtx #0`. -/
abbrev armMemUxtx (r : XReg) : MemExtRegExpr :=
  { reg := ⟨.W64, zr r .W64⟩, ext := { type := .UXTX, amount := .E0 } }

/-- Memory operand `[sp, x_r]`. -/
abbrev armAtSpIdx (r : XReg) : AddrExpr :=
  { base := .low .SP .W64, off := .reg (armMemUxtx r) }

/-- AArch64 instruction constructor. -/
abbrev armInsI {w : RegWidth} (op : Operation w) : Instr :=
  { operation_size := w, operation := op }

/-- Load unsigned 64-bit constant `c` into `x_d` via literal pool (`Instr`). -/
abbrev armLdrPoolBvI (d : XReg) (c : BitVec 64) : Instr :=
  armInsI (w := .W64) (.LDR (zr d .W64) (.lit (.pool { expr := .int64 (Int64.ofBitVec c) })))

/-- Load unsigned 64-bit constant `n` into `x_d` via literal pool (`Instr`). -/
abbrev armLdrPoolI (d : XReg) (n : Nat) : Instr :=
  armLdrPoolBvI d (BitVec.ofNat 64 n)

/-- Load unsigned 64-bit constant `n` into `x_d` via literal pool (`ldr xd, =n`). -/
abbrev armLdrPool (d : XReg) (n : Nat) : Directive :=
  armLdrPoolBv d (BitVec.ofNat 64 n)

/-- Copy 64-bit GP or stack register `s` into `x_d` (`Instr`). -/
abbrev armMovToXI (d : XReg) (s : Reg) : Instr :=
  armInsI (w := .W64) (.ADD_e (.low (.reg d) .W64) (.low s .W64) imm0)

/-- Copy 64-bit GP register `s` into `sp` (`Instr`). -/
abbrev armMovToSpI (s : XReg) : Instr :=
  armInsI (w := .W64) (.ADD_e (.low .SP .W64) (.low (.reg s) .W64) imm0)

/-- Internal instruction stream for `armSubSp`. -/
def armSubSpIns (n : Nat) : List Instr :=
  if armFitsImm12 n then
    [armInsI (.SUB_e (.low .SP .W64) (.low .SP .W64)
      (.imm { imm := .int64 (Int64.ofNat n), shift := .S0 }))]
  else
    [armLdrPoolI .X16 n, armInsI (.SUB_e (.low .SP .W64) (.low .SP .W64) (.ext (armUxtx .X16)))]

/-- Allocate `n` bytes on `sp` (`sub sp, sp, #n`, or literal-pool `x16` fallback). -/
def armSubSp (n : Nat) : List Directive :=
  emitClean (armSubSpIns n)

/-- Internal instruction stream for `armAddSp`. -/
def armAddSpIns (n : Nat) : List Instr :=
  if armFitsImm12 n then
    [armInsI (.ADD_e (.low .SP .W64) (.low .SP .W64)
      (.imm { imm := .int64 (Int64.ofNat n), shift := .S0 }))]
  else
    [armLdrPoolI .X16 n, armInsI (.ADD_e (.low .SP .W64) (.low .SP .W64) (.ext (armUxtx .X16)))]

/-- Deallocate `n` bytes on `sp` (`add sp, sp, #n`, or literal-pool `x16` fallback). -/
def armAddSp (n : Nat) : List Directive :=
  emitClean (armAddSpIns n)

/-- Internal instruction stream for `armStSpXReg`. -/
def armStSpXRegIns (r : XReg) (o : Nat) : List Instr :=
  if armFitsMemOff o then [armInsI (.STR (zr r .W64) (atOff .SP o))]
  else [armLdrPoolI .X16 o, armInsI (.STR (zr r .W64) (armAtSpIdx .X16))]

/-- Store 64-bit GP register `r` to `[sp, #o]` (with `x16` fallback for `o ≥ 32768`). -/
def armStSpXReg (r : XReg) (o : Nat) : List Directive :=
  emitClean (armStSpXRegIns r o)

/-- Internal instruction stream for `armLdSpXReg`. -/
def armLdSpXRegIns (rd : XReg) (o : Nat) : List Instr :=
  if armFitsMemOff o then [armInsI (.LDR (zr rd .W64) (.addr (atOff .SP o)))]
  else [armLdrPoolI .X16 o, armInsI (.LDR (zr rd .W64) (.addr (armAtSpIdx .X16)))]

/-- Load 64-bit GP register `rd` from `[sp, #o]` (with `x16` fallback for `o ≥ 32768`). -/
def armLdSpXReg (rd : XReg) (o : Nat) : List Directive :=
  emitClean (armLdSpXRegIns rd o)

/-- Internal instruction stream for `armPrologue`. -/
def armPrologueIns (ns : Nat) : List Instr :=
  armSubSpIns (armFrameSize ns) ++ armStSpXRegIns .X30 (8 * ns)

/-- AAPCS64 prologue: decrement `sp` by `armFrameSize ns` and save `x30` at `[sp, #(8 * ns)]`. -/
def armPrologue (ns : Nat) : List Directive × FlagMask :=
  (emitClean (armPrologueIns ns), maskNone)

/-- Internal instruction stream for `armEpilogue`. -/
def armEpilogueIns (ns : Nat) : List Instr :=
  armLdSpXRegIns .X30 (8 * ns) ++ armAddSpIns (armFrameSize ns)

/-- AAPCS64 epilogue: reload `x30` from `[sp, #(8 * ns)]` and increment `sp` by `armFrameSize ns`. -/
def armEpilogue (ns : Nat) : List Directive × FlagMask :=
  (emitClean (armEpilogueIns ns), maskNone)

/-- Internal instruction stream for `armSlotSt`. -/
def armSlotStIns (i : Nat) (r : Reg) : List Instr :=
  match r with
  | .reg x => armStSpXRegIns x (8 * i)
  | .SP => [armMovToXI .X17 .SP] ++ armStSpXRegIns .X17 (8 * i)

/-- Store 64-bit GP or stack register `r` to stack slot `i`. -/
def armSlotSt (i : Nat) (r : Reg) : List Directive :=
  emitClean (armSlotStIns i r)

/-- Internal instruction stream for `armSlotLd`. -/
def armSlotLdIns (rd : Reg) (i : Nat) : List Instr :=
  match rd with
  | .reg x => armLdSpXRegIns x (8 * i)
  | .SP => armLdSpXRegIns .X17 (8 * i) ++ [armMovToSpI .X17]

/-- Load 64-bit GP or stack register `rd` from stack slot `i`. -/
def armSlotLd (rd : Reg) (i : Nat) : List Directive :=
  emitClean (armSlotLdIns rd i)

/-- Internal instruction stream for `armCanonAbiXReg`. -/
def armCanonAbiXRegIns (t : Ty) (x : XReg) : List Instr :=
  match t with
  | .bool => [armInsI (.UBFM (zr x .W64) (zr x .W64) 0 7)]
  | .bits n =>
    if n == 8 then [armInsI (.UBFM (zr x .W64) (zr x .W64) 0 7)]
    else if n == 16 then [armInsI (.UBFM (zr x .W64) (zr x .W64) 0 15)]
    else if n == 32 then [armInsI (.ORR_s (zr x .W32) (xzr .W32) (sh x))]
    else []
  | _ => []

/-- ABI zero-extension canonicalization on a GP `XReg`. -/
def armCanonAbiXReg (t : Ty) (x : XReg) : List Directive :=
  emitClean (armCanonAbiXRegIns t x)

/-- Internal instruction stream for `armCanonAbi`. -/
def armCanonAbiIns (t : Ty) (r : Reg) : List Instr :=
  match r with
  | .reg x => armCanonAbiXRegIns t x
  | .SP =>
    match t with
    | .bool => [armMovToXI .X16 .SP] ++ armCanonAbiXRegIns t .X16 ++ [armMovToSpI .X16]
    | .bits n =>
      if n == 8 || n == 16 || n == 32 then
        [armMovToXI .X16 .SP] ++ armCanonAbiXRegIns t .X16 ++ [armMovToSpI .X16]
      else []
    | _ => []

/-- Unified ABI zero-extension canonicalization for integer/bool types (`maskNone` flags). -/
def armCanonAbi (t : Ty) (r : Reg) : List Directive × FlagMask :=
  (emitClean (armCanonAbiIns t r), maskNone)

/-- Direct function call `bl sym`. -/
abbrev armCallI (sym : Sym) : Instr := armInsI (.BL (.label sym))

/-- Direct function call `bl sym`. -/
def armCallD (sym : Sym) : Directive := .instr (armCallI sym)

/-- Direct tail jump `b sym`. -/
abbrev armJmpI (sym : Sym) : Instr := armInsI (.B (.label sym))

/-- Direct tail jump `b sym`. -/
def armJmpD (sym : Sym) : Directive := .instr (armJmpI sym)

/-- Function return `ret` (branch to `x30`). -/
abbrev armRetI : Instr := armInsI (.RET (.low (.reg .X30) .W64))

/-- Function return `ret` (branch to `x30`). -/
def armRetD : Directive := .instr armRetI

/-- AAPCS64 Arm64 `FrameIsa` instance (`allocatable`: `x0..x15`, `calleeSaved`: `x19..x29`,
`scratch`: `x16..x17`, `raRegs`: `[x30]`, `argRegs`/`retRegs`: `x0..x7`). -/
@[reducible] def armFrame : FrameIsa Reg Directive where
  label := .label
  sp := .SP
  scratch := armScratch
  allocatable :=
    [.reg .X0, .reg .X1, .reg .X2, .reg .X3, .reg .X4, .reg .X5, .reg .X6, .reg .X7,
     .reg .X8, .reg .X9, .reg .X10, .reg .X11, .reg .X12, .reg .X13, .reg .X14, .reg .X15]
  calleeSaved :=
    [.reg .X19, .reg .X20, .reg .X21, .reg .X22, .reg .X23, .reg .X24,
     .reg .X25, .reg .X26, .reg .X27, .reg .X28, .reg .X29]
  raRegs := [.reg .X30]
  argRegs :=
    [.reg .X0, .reg .X1, .reg .X2, .reg .X3, .reg .X4, .reg .X5, .reg .X6, .reg .X7]
  retRegs :=
    [.reg .X0, .reg .X1, .reg .X2, .reg .X3, .reg .X4, .reg .X5, .reg .X6, .reg .X7]
  bitWidths := [8, 16, 32, 64]
  raBytes := 0
  frameSize := armFrameSize
  prologue := armPrologue
  epilogue := armEpilogue
  slotSt := armSlotSt
  slotLd := armSlotLd
  canonAbi := armCanonAbi
  call sym := emitClean [armCallI sym]
  exitJmp sym := emitClean [armJmpI sym]
  ret := emitClean [armRetI]

end LeanQbe.T.Arm64
