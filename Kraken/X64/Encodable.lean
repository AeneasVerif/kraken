module

public import Kraken.X64.Syntax

@[expose] public section
/-!
# Encodable instructions

`Instr.encodable i` holds when GNU `as` assembles `toATT i` (64-bit mode, legacy, VEX and EVEX
encodings, no APX) without errors or warnings into an encoding of exactly `i`.
CPU features are not checked: an EVEX form counts as encodable on any width it exists at.

Literal constants are checked against the field `as` puts them in.
A symbolic constant is accepted when it is one label plus or minus a literal: `as` then emits a
relocation for the field, and the linker rejects a value that does not fit it.
Differences of labels, `.` and other arithmetic are rejected.

The address size counts only for instructions that compute an address; the operation size only
for instructions whose meaning depends on it.

Forms the parser does not read back are rejected too (an index without a base, a symbolic shift
count), so that the printed file means the same to `as` and to Kraken.

`KrakenRunnerX64 --encodable` compares this predicate with `as` on random instructions.
-/
namespace Kraken.X64.Encodable

/-! ## Fields -/

/-- `v` fits a signed field of `bits` bits. -/
def fitsSigned (bits : Nat) (v : Int) : Bool := -2 ^ (bits - 1) ≤ v && v < 2 ^ (bits - 1)

/-- `v` fits a field of `bits` bits that `as` fills by truncation: it accepts `v` when `v` or `-v`
is below `2 ^ bits`. -/
def fitsTrunc (bits : Nat) (v : Int) : Bool := -2 ^ bits < v && v < 2 ^ bits

/-- `v` fits an unsigned byte. -/
def fitsU8 (v : Int) : Bool := 0 ≤ v && v < 256

/-- `v` fits a byte that `as` reads as signed or unsigned. -/
def fitsS8 (v : Int) : Bool := -128 ≤ v && v < 256

/-- A name `as` reads as one symbol. -/
def label (l : Label) : Bool :=
  let ok c := c.isAlphanum || c == '_' || c == '.' || c == '$'
  match l.toList with
  | c :: cs => (c.isAlpha || c == '_' || c == '.') && cs.all ok
  | [] => false

/-- One label plus or minus a literal: a relocation can carry it. -/
def symbolic : ConstExpr → Bool
  | .label l | .add (.label l) (.int64 _) | .sub (.label l) (.int64 _) => label l
  | _ => false

/-- A literal that satisfies `fits`, or a symbolic constant. -/
def const (fits : Int → Bool) (e : ConstExpr) : Bool :=
  match e with
  | .int64 i => fits i.toInt
  | e => symbolic e

/-- How `as` first reads a literal for an operation of width `w`: as signed 16 bits at 8 and 16
bits when it is below `2 ^ 16`, then as signed 32 bits up to 32 bits when it is below `2 ^ 32`.
Only the bits outside the field change. -/
def reduce (w : Width) (v : Int) : Int :=
  let v :=
    if (w == .W8 || w == .W16) && 0 ≤ v && v < 2 ^ 16 then (v + 2 ^ 15) % 2 ^ 16 - 2 ^ 15 else v
  if w != .W64 && 0 ≤ v && v < 2 ^ 32 then (v + 2 ^ 31) % 2 ^ 32 - 2 ^ 31 else v

/-- The immediate of an ALU operation: sign-extended from 32 bits at 64 bits, else truncated. -/
def fitsImm (w : Width) (v : Int) : Bool :=
  if w == .W64 then fitsSigned 32 v else fitsTrunc w.bits (reduce w v)

def imm (w : Width) : ConstExpr → Bool := const (fitsImm w)

/-! ## Operands -/

/-- A rip-relative displacement. `sym(%rip)` names the target, so its displacement is `sym` minus
the address of the next instruction. -/
def ripDisp (wide : Bool) : ConstExpr → Bool
  | .int64 i => if wide then fitsTrunc 32 i.toInt else fitsSigned 32 i.toInt
  | .sub e .after_current_instruction => symbolic e
  | _ => false

/-- A memory operand at address size `aw`.
`wide` accepts any 32-bit displacement (`as` truncates the address); `moffs` any 64-bit absolute
address (the `movabs` forms of `mov`). -/
def mem (aw : Width) (a : AddrExpr) (wide moffs : Bool := false) : Bool :=
  let disp := const (if wide || aw == .W32 then fitsTrunc 32 else fitsSigned 32) a.disp
  match a.base, a.idx with
  -- The printer always spells `%rip`, and rip-relative addressing has no index.
  | some .rip, none => aw == .W64 && ripDisp wide a.disp
  | some .rip, some _ => false
  -- An absolute address is printed without registers, which `as` reads at 64 bits.
  | none, none => aw == .W64 && (moffs && (a.disp matches .int64 _) || disp)
  -- The parser reads back no index without a base.
  | none, some _ => false
  -- `%rsp` cannot be an index; 16-bit addressing does not exist in 64-bit mode.
  | _, some ⟨.rsp, _⟩ => false
  | _, _ => (aw == .W64 || aw == .W32) && disp

def rm (aw : Width) {w} : RegOrMem w → Bool
  | .reg _ => true
  | .mem a => mem aw a

/-- Two operands, at most one in memory, where an immediate source satisfies `immOk`. -/
def binary (aw : Width) {w} (immOk : ConstExpr → Bool) (d : RegOrMem w) : Operand w → Bool
  | .imm v => rm aw d && immOk v
  | .regOrMem (.mem a) => (d matches .reg _) && mem aw a
  | .regOrMem (.reg _) => rm aw d

/-- A shift count. The parser reads back a literal count only. -/
def count (fits : Int → Bool) : ShiftCountExpr → Bool
  | .cl => true
  | .imm8 (.int64 i) => fits i.toInt
  | .imm8 _ => false

def mov (aw : Width) {w} (d : RegOrMem w) (x : Operand w) : Bool :=
  match d, x with
  -- `al`, `ax`, `eax`, `rax` load and store any absolute address (`movabs`).
  | .reg (.low .rax _), .regOrMem (.mem a) | .mem a, .regOrMem (.reg (.low .rax _)) =>
    mem aw a (moffs := true)
  -- A register takes any immediate of its width (`movabs` at 64 bits).
  | .reg _, .imm v => const (fun i => w == .W64 || fitsImm w i) v
  | d, x => binary aw (imm w) d x

/-- The source of `movsx` (`signed`) or `movzx` from `w'` to `w` bits.
The printer spells only the register forms of the same-width extensions. -/
def extend (aw : Width) (signed : Bool) (w' w : Width) (x : RegOrMem w') : Bool :=
  match w', w with
  | .W8, .W16 | .W8, .W32 | .W8, .W64 | .W16, .W32 | .W16, .W64 => rm aw x
  | .W32, .W64 => signed && rm aw x
  | .W16, .W16 => (x matches .reg _)
  | .W32, .W32 => signed && (x matches .reg _)
  | _, _ => false

/-- A branch target. The parser reads back a bare label only, and reads a symbolic displacement
or a memory operand without registers as a direct target. -/
def target (aw : Width) : RelRegOrMem → Bool
  | .rel (.sub (.label l) .after_current_instruction) => label l
  | .rel _ => false
  | .reg _ => true
  | .mem a => a.base.isSome && (a.disp matches .int64 _) && mem aw a

/-! ## High byte registers -/

def Reg64.isExtended : Reg64 → Bool
  | .r8 | .r9 | .r10 | .r11 | .r12 | .r13 | .r14 | .r15 => true
  | _ => false

/-- A register only a REX prefix can name: `r8`–`r15` at any width, and `spl`, `bpl`, `sil`,
`dil`. -/
def Reg.needsRex {w} : Reg w → Bool
  | .low r w => Reg64.isExtended r || w == .W8 && [.rsp, .rbp, .rsi, .rdi].contains r
  | _ => false

def AddrExpr.needsRex (a : AddrExpr) : Bool :=
  (match a.base with | some (.reg r) => Reg64.isExtended r | _ => false) ||
  (match a.idx with | some ⟨r, _⟩ => Reg64.isExtended r | none => false)

/-- Whether an operand names `ah`, `bh`, `ch` or `dh`, and whether it needs a REX prefix. -/
def rmBytes {w} : RegOrMem w → Bool × Bool
  | .reg r => (!(r matches .low ..), Reg.needsRex r)
  | .mem a => (false, AddrExpr.needsRex a)

def operandBytes {w} : Operand w → Bool × Bool
  | .regOrMem x => rmBytes x
  | .imm _ => (false, false)

/-- `ah`, `bh`, `ch` and `dh` cannot appear in an instruction with a REX prefix. -/
def noHighWithRex (ops : List (Bool × Bool)) (rexW : Bool := false) : Bool :=
  !(ops.any (·.1) && (rexW || ops.any (·.2)))

/-! ## General-purpose instructions -/

def Operation.encodable (aw : Width) {w} (op : Operation w) : Bool :=
  let wide := w != .W8
  let dw := w == .W32 || w == .W64
  let stack := w == .W16 || w == .W64
  match op with
  | .mov d x => noHighWithRex [rmBytes d, operandBytes x] && mov aw d x
  | .movsx (w' := w') d x =>
    noHighWithRex [rmBytes d, rmBytes x] (rexW := w == .W64) && (d matches .reg _) &&
    extend aw true w' w x
  | .movzx (w' := w') d x =>
    noHighWithRex [rmBytes d, rmBytes x] (rexW := w == .W64) && (d matches .reg _) &&
    extend aw false w' w x
  -- 64-bit mode pushes and pops 16 or 64 bits.
  | .push (.imm v) => stack && imm w v
  | .push (.regOrMem x) | .pop x => stack && rm aw x
  | .setcc _ d => w == .W8 && noHighWithRex [rmBytes d] && rm aw d
  | .cmovcc _ _ x => wide && rm aw x
  -- The pointers and the count are read at the address size, and `addr32` is printed.
  | .movs _ | .stos _ => aw == .W64 || aw == .W32
  -- A narrow destination truncates the address, so `as` takes any 32-bit displacement.
  | .lea _ a => wide && mem aw a (wide := w != .W64)
  | .add d x | .adc d x | .sub d x | .sbb d x | .and d x | .or d x | .xor d x
  | .cmp d x | .test d x => noHighWithRex [rmBytes d, operandBytes x] && binary aw (imm w) d x
  | .adcx _ x | .adox _ x | .mulx _ _ x => dw && rm aw x
  | .inc x | .dec x | .neg x | .not x | .mul x | .imul1 x | .div x =>
    noHighWithRex [rmBytes x] && rm aw x
  -- Two operands: `imul r/m, r` or `imul $imm, r`; three: only `imul $imm, r/m, r`.
  | .imul none (.reg _) x => wide && (match x with | .imm v => imm w v | .regOrMem y => rm aw y)
  | .imul (some (.reg _)) x (.imm v) => wide && rm aw x && imm w v
  | .imul _ _ _ => false
  -- `as` takes a signed or unsigned byte count for rotates, an unsigned one for other shifts,
  -- and any truncated byte at 8 bits.
  | .shl d c | .shr d c | .sar d c | .rcl d c | .rcr d c =>
    noHighWithRex [rmBytes d] && rm aw d && count (if wide then fitsU8 else fitsImm .W8) c
  | .rol d c | .ror d c =>
    noHighWithRex [rmBytes d] && rm aw d &&
    count (if wide then fitsS8 ∘ reduce w else fitsImm .W8) c
  | .shld d _ c | .shrd d _ c => wide && rm aw d && count fitsU8 c
  | .bswap _ => dw
  | .cld | .std | .cpuid | .xgetbv | .ret => true
  | .jcc _ l => label l
  | .jmp t | .call t => target aw t
  -- `nop n` prints as a `nop` with a memory operand: only the one-byte `nop` is printed right.
  | .nop n => n == 1
  -- The padding is executed, so it must be `nop` (0x90); alignments 0 and 1 pad nothing.
  | .nopalign a pad => a &&& (a - 1) == 0 && (a ≤ 1 || pad == none || pad == some 0x90)

/-! ## Vector instructions -/

def RegMm.isUpper : RegMm → Bool
  | .mm16 | .mm17 | .mm18 | .mm19 | .mm20 | .mm21 | .mm22 | .mm23
  | .mm24 | .mm25 | .mm26 | .mm27 | .mm28 | .mm29 | .mm30 | .mm31 => true
  | _ => false

/-- A vector register; only EVEX (`evex`) reaches registers 16–31. -/
def avxReg (evex : Bool) {w} : AvxReg w → Bool
  | .xmm r | .ymm r | .zmm r => evex || !RegMm.isUpper r

def avxRm (aw : Width) (evex : Bool) {w} : AvxRegOrMem w → Bool
  | .avx r => avxReg evex r
  | .mem a => mem aw a

/-- A register destination. -/
def avxDst (evex : Bool) {w} : AvxRegOrMem w → Bool
  | .avx r => avxReg evex r
  | .mem _ => false

/-- A move: at most one operand in memory. -/
def avxMove (aw : Width) (evex : Bool) {w} (d x : AvxRegOrMem w) : Bool :=
  !((d matches .mem _) && (x matches .mem _)) && avxRm aw evex d && avxRm aw evex x

/-- `op src2, src1, dst`: `src1` is a register, `src2` a register or memory. -/
def avx3 (aw : Width) (evex : Bool) {w w'} (d a : AvxRegOrMem w) (b : AvxRegOrMem w') : Bool :=
  avxDst evex d && avxDst evex a && avxRm aw evex b

def AvxOperation.encodable (aw : Width) {w} (op : AvxOperation w) : Bool :=
  let xmm := w == .W128
  let vex := w != .W512
  match op with
  -- Legacy SSE: 128 bits, registers 0–15.
  | .movups d x | .movaps d x | .movdqu d x | .movdqa d x => xmm && avxMove aw false d x
  | .subps d x | .addps d x | .paddd d x | .pxor d x | .pand d x | .pandn d x | .pshufb d x
  | .sha256rnds2 d x | .sha256msg1 d x | .sha256msg2 d x =>
    xmm && avxDst false d && avxRm aw false x
  | .psrld d i | .pslld d i => xmm && avxDst false d && const fitsU8 i
  | .pshufd d x i | .pblendw d x i => xmm && avxDst false d && avxRm aw false x && const fitsS8 i
  | .palignr d x i => xmm && avxDst false d && avxRm aw false x && const fitsU8 i
  -- VEX only: 128 and 256 bits, registers 0–15.
  | .vmovdqu d x | .vmovdqa d x => vex && avxMove aw false d x
  | .vpand d a b | .vpandn d a b | .vpor d a b | .vpxor d a b => vex && avx3 aw false d a b
  | .vperm2i128 d a b i => w == .W256 && avx3 aw false d a b && const fitsS8 i
  -- EVEX forms exist at every width they are defined at: registers 0–31.
  | .vmovups d x | .vmovdqu32 d x | .vmovdqa32 d x => avxMove aw true d x
  | .vmovIn n _ x | .vmovOut n x _ => xmm && (n == .W32 || n == .W64) && rm aw x
  | .vmovq _ _ => xmm
  | .vzeroupper => true
  | .vpaddd d a b | .vpshufb d a b | .vpermi2q d a b | .vpermi2d d a b
  | .vpunpckldq d a b | .vpunpckhdq d a b | .vpunpcklqdq d a b | .vpunpckhqdq d a b =>
    avx3 aw true d a b
  | .vprord d x i => avxDst true d && avxRm aw true x && const fitsS8 i
  | .vpsrld d x i | .vpslld d x i => avxDst true d && avxRm aw true x && const fitsU8 i
  | .vpternlogd d b c i | .vshufps d b c i => avx3 aw true d b c && const fitsS8 i
  | .vinserti64x4 d a b i => w == .W512 && avx3 aw true d a b && const fitsU8 i

end Kraken.X64.Encodable

open Kraken.X64.Encodable in
/-- `as` assembles `toATT i` into an encoding of exactly `i`. -/
def Instr.encodable : Instr → Bool
  | .regular aw _ op => Operation.encodable aw op
  | .avx aw _ op => AvxOperation.encodable aw op
