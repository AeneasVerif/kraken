module

public import Kraken.X64.Parser.Basic
public meta import Kraken.X64.Parser.Basic
public import Kraken.X64.Parser.Syntax
public meta import Kraken.X64.Parser.Syntax
public meta import Lean

namespace Kraken.X64.Parser

open Lean Meta Elab Term

public meta section

-- ============================================================================
-- Helper Types & Named Range Constants
-- ============================================================================

/-- Maximum value of `UInt64` as an `Int` (`2^64 - 1`). -/
def UInt64.maxValue.toInt : Int := 0xffffffffffffffff

/-- Total number of distinct `UInt64` values (`2^64`). -/
def UInt64.modulus : Int := UInt64.maxValue.toInt + 1

@[expose]
def MaybeOpWidth (T : Width → Type) :=
  Σ w : Option Width, match w with
    | some w => T w
    | none   => {w : Width} → T w

@[expose]
def MaybeAvxOpWidth (T : AvxWidth → Type) :=
  Σ w : Option AvxWidth, match w with
    | some w => T w
    | none   => {w : AvxWidth} → T w

abbrev MaybeAddrWidth := Option Width

def toInstr (addr : MaybeAddrWidth) {w : Width} (op : Operation w) : Instr :=
  let _ : AddressSize := { address_size := addr.getD .W64 }
  ↑op

def toAvxInstr (addr : MaybeAddrWidth) {w : AvxWidth} (op : AvxOperation w) : Instr :=
  let _ : AddressSize := { address_size := addr.getD .W64 }
  ↑op

-- ============================================================================
-- Identifier & Constant Expression Elaboration
-- ============================================================================

/-- Extract the raw assembly identifier string from an `x64_ident` syntax node. -/
def getAsmIdent : TSyntax `x64_ident → TermElabM String
  | ⟨.node _ _ #[.atom _ s]⟩ => pure s
  | stx => throwErrorAt stx "expected assembly identifier"

/-- Convert a signed arbitrary-precision `Int` into `Int64`, enforcing 64-bit signed/unsigned range. -/
def intToInt64Checked (stx : Syntax) (v : Int) : TermElabM Int64 := do
  if v < Int64.minValue.toInt || v > UInt64.maxValue.toInt then
    throwErrorAt stx "integer {v} out of 64-bit range"
  if v > Int64.maxValue.toInt then
    pure (Int64.ofInt (v - UInt64.modulus))
  else
    pure (Int64.ofInt v)

/-- Elaborate an `x64_const` syntax node into a `ConstExpr`. -/
def elabConstExpr (stx : TSyntax `x64_const) : TermElabM ConstExpr :=
  match stx with
  | `(x64_const| $n:num) => do
    let i ← intToInt64Checked n (Int.ofNat n.getNat)
    pure (.int64 i)
  | `(x64_const| -$n:num) => do
    let i ← intToInt64Checked stx (-(Int.ofNat n.getNat))
    pure (.int64 i)
  | `(x64_const| +$n:num) => do
    let i ← intToInt64Checked stx (Int.ofNat n.getNat)
    pure (.int64 i)
  | `(x64_const| $id:x64_ident + $n:num) => do
    let s ← getAsmIdent id
    let i ← intToInt64Checked n (Int.ofNat n.getNat)
    pure (.add (.label s) (.int64 i))
  | `(x64_const| $id:x64_ident - $n:num) => do
    let s ← getAsmIdent id
    let i ← intToInt64Checked n (Int.ofNat n.getNat)
    pure (.sub (.label s) (.int64 i))
  | `(x64_const| $id:x64_ident) => do
    let s ← getAsmIdent id
    pure (.label s)
  | _ => throwErrorAt stx "invalid constant expression"

-- ============================================================================
-- Register Elaboration
-- ============================================================================

/-- Elaborate an `x64_reg` syntax node into a general-purpose register `RegW`. -/
def elabRegW (stx : TSyntax `x64_reg) : TermElabM RegW :=
  open Reg in
  match stx with
  | `(x64_reg| %rax) => pure ⟨.W64, rax⟩ | `(x64_reg| %rbx) => pure ⟨.W64, rbx⟩
  | `(x64_reg| %rcx) => pure ⟨.W64, rcx⟩ | `(x64_reg| %rdx) => pure ⟨.W64, rdx⟩
  | `(x64_reg| %rsi) => pure ⟨.W64, rsi⟩ | `(x64_reg| %rdi) => pure ⟨.W64, rdi⟩
  | `(x64_reg| %rsp) => pure ⟨.W64, rsp⟩ | `(x64_reg| %rbp) => pure ⟨.W64, rbp⟩
  | `(x64_reg| %r8)  => pure ⟨.W64, r8⟩  | `(x64_reg| %r9)  => pure ⟨.W64, r9⟩
  | `(x64_reg| %r10) => pure ⟨.W64, r10⟩ | `(x64_reg| %r11) => pure ⟨.W64, r11⟩
  | `(x64_reg| %r12) => pure ⟨.W64, r12⟩ | `(x64_reg| %r13) => pure ⟨.W64, r13⟩
  | `(x64_reg| %r14) => pure ⟨.W64, r14⟩ | `(x64_reg| %r15) => pure ⟨.W64, r15⟩
  | `(x64_reg| %eax) => pure ⟨.W32, eax⟩ | `(x64_reg| %ebx) => pure ⟨.W32, ebx⟩
  | `(x64_reg| %ecx) => pure ⟨.W32, ecx⟩ | `(x64_reg| %edx) => pure ⟨.W32, edx⟩
  | `(x64_reg| %esi) => pure ⟨.W32, esi⟩ | `(x64_reg| %edi) => pure ⟨.W32, edi⟩
  | `(x64_reg| %esp) => pure ⟨.W32, esp⟩ | `(x64_reg| %ebp) => pure ⟨.W32, ebp⟩
  | `(x64_reg| %r8d)  => pure ⟨.W32, r8d⟩  | `(x64_reg| %r9d)  => pure ⟨.W32, r9d⟩
  | `(x64_reg| %r10d) => pure ⟨.W32, r10d⟩ | `(x64_reg| %r11d) => pure ⟨.W32, r11d⟩
  | `(x64_reg| %r12d) => pure ⟨.W32, r12d⟩ | `(x64_reg| %r13d) => pure ⟨.W32, r13d⟩
  | `(x64_reg| %r14d) => pure ⟨.W32, r14d⟩ | `(x64_reg| %r15d) => pure ⟨.W32, r15d⟩
  | `(x64_reg| %ax)  => pure ⟨.W16, ax⟩  | `(x64_reg| %bx)  => pure ⟨.W16, bx⟩
  | `(x64_reg| %cx)  => pure ⟨.W16, cx⟩  | `(x64_reg| %dx)  => pure ⟨.W16, dx⟩
  | `(x64_reg| %si)  => pure ⟨.W16, si⟩  | `(x64_reg| %di)  => pure ⟨.W16, di⟩
  | `(x64_reg| %sp)  => pure ⟨.W16, sp⟩  | `(x64_reg| %bp)  => pure ⟨.W16, bp⟩
  | `(x64_reg| %r8w)  => pure ⟨.W16, r8w⟩  | `(x64_reg| %r9w)  => pure ⟨.W16, r9w⟩
  | `(x64_reg| %r10w) => pure ⟨.W16, r10w⟩ | `(x64_reg| %r11w) => pure ⟨.W16, r11w⟩
  | `(x64_reg| %r12w) => pure ⟨.W16, r12w⟩ | `(x64_reg| %r13w) => pure ⟨.W16, r13w⟩
  | `(x64_reg| %r14w) => pure ⟨.W16, r14w⟩ | `(x64_reg| %r15w) => pure ⟨.W16, r15w⟩
  | `(x64_reg| %al)  => pure ⟨.W8, al⟩   | `(x64_reg| %bl)  => pure ⟨.W8, bl⟩
  | `(x64_reg| %cl)  => pure ⟨.W8, cl⟩   | `(x64_reg| %dl)  => pure ⟨.W8, dl⟩
  | `(x64_reg| %sil) => pure ⟨.W8, sil⟩  | `(x64_reg| %dil) => pure ⟨.W8, dil⟩
  | `(x64_reg| %spl) => pure ⟨.W8, spl⟩  | `(x64_reg| %bpl) => pure ⟨.W8, bpl⟩
  | `(x64_reg| %r8b)  => pure ⟨.W8, r8b⟩  | `(x64_reg| %r9b)  => pure ⟨.W8, r9b⟩
  | `(x64_reg| %r10b) => pure ⟨.W8, r10b⟩ | `(x64_reg| %r11b) => pure ⟨.W8, r11b⟩
  | `(x64_reg| %r12b) => pure ⟨.W8, r12b⟩ | `(x64_reg| %r13b) => pure ⟨.W8, r13b⟩
  | `(x64_reg| %r14b) => pure ⟨.W8, r14b⟩ | `(x64_reg| %r15b) => pure ⟨.W8, r15b⟩
  | `(x64_reg| %ah)  => pure ⟨.W8, ah⟩   | `(x64_reg| %bh)  => pure ⟨.W8, bh⟩
  | `(x64_reg| %ch)  => pure ⟨.W8, ch⟩   | `(x64_reg| %dh)  => pure ⟨.W8, dh⟩
  | _ => throwErrorAt stx "expected general-purpose register"

/-- Elaborate an `x64_reg` syntax node into an AVX vector register `AvxRegW`. -/
def elabAvxRegW (stx : TSyntax `x64_reg) : TermElabM AvxRegW :=
  match stx with
  | `(x64_reg| %xmm0)  => pure ⟨.W128, .xmm .mm0⟩  | `(x64_reg| %xmm1)  => pure ⟨.W128, .xmm .mm1⟩
  | `(x64_reg| %xmm2)  => pure ⟨.W128, .xmm .mm2⟩  | `(x64_reg| %xmm3)  => pure ⟨.W128, .xmm .mm3⟩
  | `(x64_reg| %xmm4)  => pure ⟨.W128, .xmm .mm4⟩  | `(x64_reg| %xmm5)  => pure ⟨.W128, .xmm .mm5⟩
  | `(x64_reg| %xmm6)  => pure ⟨.W128, .xmm .mm6⟩  | `(x64_reg| %xmm7)  => pure ⟨.W128, .xmm .mm7⟩
  | `(x64_reg| %xmm8)  => pure ⟨.W128, .xmm .mm8⟩  | `(x64_reg| %xmm9)  => pure ⟨.W128, .xmm .mm9⟩
  | `(x64_reg| %xmm10) => pure ⟨.W128, .xmm .mm10⟩ | `(x64_reg| %xmm11) => pure ⟨.W128, .xmm .mm11⟩
  | `(x64_reg| %xmm12) => pure ⟨.W128, .xmm .mm12⟩ | `(x64_reg| %xmm13) => pure ⟨.W128, .xmm .mm13⟩
  | `(x64_reg| %xmm14) => pure ⟨.W128, .xmm .mm14⟩ | `(x64_reg| %xmm15) => pure ⟨.W128, .xmm .mm15⟩
  | `(x64_reg| %xmm16) => pure ⟨.W128, .xmm .mm16⟩ | `(x64_reg| %xmm17) => pure ⟨.W128, .xmm .mm17⟩
  | `(x64_reg| %xmm18) => pure ⟨.W128, .xmm .mm18⟩ | `(x64_reg| %xmm19) => pure ⟨.W128, .xmm .mm19⟩
  | `(x64_reg| %xmm20) => pure ⟨.W128, .xmm .mm20⟩ | `(x64_reg| %xmm21) => pure ⟨.W128, .xmm .mm21⟩
  | `(x64_reg| %xmm22) => pure ⟨.W128, .xmm .mm22⟩ | `(x64_reg| %xmm23) => pure ⟨.W128, .xmm .mm23⟩
  | `(x64_reg| %xmm24) => pure ⟨.W128, .xmm .mm24⟩ | `(x64_reg| %xmm25) => pure ⟨.W128, .xmm .mm25⟩
  | `(x64_reg| %xmm26) => pure ⟨.W128, .xmm .mm26⟩ | `(x64_reg| %xmm27) => pure ⟨.W128, .xmm .mm27⟩
  | `(x64_reg| %xmm28) => pure ⟨.W128, .xmm .mm28⟩ | `(x64_reg| %xmm29) => pure ⟨.W128, .xmm .mm29⟩
  | `(x64_reg| %xmm30) => pure ⟨.W128, .xmm .mm30⟩ | `(x64_reg| %xmm31) => pure ⟨.W128, .xmm .mm31⟩
  | `(x64_reg| %ymm0)  => pure ⟨.W256, .ymm .mm0⟩  | `(x64_reg| %ymm1)  => pure ⟨.W256, .ymm .mm1⟩
  | `(x64_reg| %ymm2)  => pure ⟨.W256, .ymm .mm2⟩  | `(x64_reg| %ymm3)  => pure ⟨.W256, .ymm .mm3⟩
  | `(x64_reg| %ymm4)  => pure ⟨.W256, .ymm .mm4⟩  | `(x64_reg| %ymm5)  => pure ⟨.W256, .ymm .mm5⟩
  | `(x64_reg| %ymm6)  => pure ⟨.W256, .ymm .mm6⟩  | `(x64_reg| %ymm7)  => pure ⟨.W256, .ymm .mm7⟩
  | `(x64_reg| %ymm8)  => pure ⟨.W256, .ymm .mm8⟩  | `(x64_reg| %ymm9)  => pure ⟨.W256, .ymm .mm9⟩
  | `(x64_reg| %ymm10) => pure ⟨.W256, .ymm .mm10⟩ | `(x64_reg| %ymm11) => pure ⟨.W256, .ymm .mm11⟩
  | `(x64_reg| %ymm12) => pure ⟨.W256, .ymm .mm12⟩ | `(x64_reg| %ymm13) => pure ⟨.W256, .ymm .mm13⟩
  | `(x64_reg| %ymm14) => pure ⟨.W256, .ymm .mm14⟩ | `(x64_reg| %ymm15) => pure ⟨.W256, .ymm .mm15⟩
  | `(x64_reg| %ymm16) => pure ⟨.W256, .ymm .mm16⟩ | `(x64_reg| %ymm17) => pure ⟨.W256, .ymm .mm17⟩
  | `(x64_reg| %ymm18) => pure ⟨.W256, .ymm .mm18⟩ | `(x64_reg| %ymm19) => pure ⟨.W256, .ymm .mm19⟩
  | `(x64_reg| %ymm20) => pure ⟨.W256, .ymm .mm20⟩ | `(x64_reg| %ymm21) => pure ⟨.W256, .ymm .mm21⟩
  | `(x64_reg| %ymm22) => pure ⟨.W256, .ymm .mm22⟩ | `(x64_reg| %ymm23) => pure ⟨.W256, .ymm .mm23⟩
  | `(x64_reg| %ymm24) => pure ⟨.W256, .ymm .mm24⟩ | `(x64_reg| %ymm25) => pure ⟨.W256, .ymm .mm25⟩
  | `(x64_reg| %ymm26) => pure ⟨.W256, .ymm .mm26⟩ | `(x64_reg| %ymm27) => pure ⟨.W256, .ymm .mm27⟩
  | `(x64_reg| %ymm28) => pure ⟨.W256, .ymm .mm28⟩ | `(x64_reg| %ymm29) => pure ⟨.W256, .ymm .mm29⟩
  | `(x64_reg| %ymm30) => pure ⟨.W256, .ymm .mm30⟩ | `(x64_reg| %ymm31) => pure ⟨.W256, .ymm .mm31⟩
  | `(x64_reg| %zmm0)  => pure ⟨.W512, .zmm .mm0⟩  | `(x64_reg| %zmm1)  => pure ⟨.W512, .zmm .mm1⟩
  | `(x64_reg| %zmm2)  => pure ⟨.W512, .zmm .mm2⟩  | `(x64_reg| %zmm3)  => pure ⟨.W512, .zmm .mm3⟩
  | `(x64_reg| %zmm4)  => pure ⟨.W512, .zmm .mm4⟩  | `(x64_reg| %zmm5)  => pure ⟨.W512, .zmm .mm5⟩
  | `(x64_reg| %zmm6)  => pure ⟨.W512, .zmm .mm6⟩  | `(x64_reg| %zmm7)  => pure ⟨.W512, .zmm .mm7⟩
  | `(x64_reg| %zmm8)  => pure ⟨.W512, .zmm .mm8⟩  | `(x64_reg| %zmm9)  => pure ⟨.W512, .zmm .mm9⟩
  | `(x64_reg| %zmm10) => pure ⟨.W512, .zmm .mm10⟩ | `(x64_reg| %zmm11) => pure ⟨.W512, .zmm .mm11⟩
  | `(x64_reg| %zmm12) => pure ⟨.W512, .zmm .mm12⟩ | `(x64_reg| %zmm13) => pure ⟨.W512, .zmm .mm13⟩
  | `(x64_reg| %zmm14) => pure ⟨.W512, .zmm .mm14⟩ | `(x64_reg| %zmm15) => pure ⟨.W512, .zmm .mm15⟩
  | `(x64_reg| %zmm16) => pure ⟨.W512, .zmm .mm16⟩ | `(x64_reg| %zmm17) => pure ⟨.W512, .zmm .mm17⟩
  | `(x64_reg| %zmm18) => pure ⟨.W512, .zmm .mm18⟩ | `(x64_reg| %zmm19) => pure ⟨.W512, .zmm .mm19⟩
  | `(x64_reg| %zmm20) => pure ⟨.W512, .zmm .mm20⟩ | `(x64_reg| %zmm21) => pure ⟨.W512, .zmm .mm21⟩
  | `(x64_reg| %zmm22) => pure ⟨.W512, .zmm .mm22⟩ | `(x64_reg| %zmm23) => pure ⟨.W512, .zmm .mm23⟩
  | `(x64_reg| %zmm24) => pure ⟨.W512, .zmm .mm24⟩ | `(x64_reg| %zmm25) => pure ⟨.W512, .zmm .mm25⟩
  | `(x64_reg| %zmm26) => pure ⟨.W512, .zmm .mm26⟩ | `(x64_reg| %zmm27) => pure ⟨.W512, .zmm .mm27⟩
  | `(x64_reg| %zmm28) => pure ⟨.W512, .zmm .mm28⟩ | `(x64_reg| %zmm29) => pure ⟨.W512, .zmm .mm29⟩
  | `(x64_reg| %zmm30) => pure ⟨.W512, .zmm .mm30⟩ | `(x64_reg| %zmm31) => pure ⟨.W512, .zmm .mm31⟩
  | _ => throwErrorAt stx "expected AVX register"

/-- Elaborate a low register for memory index addressing (rejecting `%ah`/`%bh`/`%ch`/`%dh`). -/
def elabLowReg (stx : TSyntax `x64_reg) : TermElabM (Width × Reg64) := do
  let ⟨w, r⟩ ← elabRegW stx
  match r with
  | .low r64 _ => pure (w, r64)
  | _ => throwErrorAt stx "high byte register cannot be used for an addrexpr"

/-- Elaborate a base register for memory addressing (`%rip` or a low GPR). -/
def elabRegOrRip (stx : TSyntax `x64_reg) : TermElabM (Width × RegOrRip) :=
  match stx with
  | `(x64_reg| %rip) => pure (.W64, .rip)
  | _ => do
    let (w, r) ← elabLowReg stx
    pure (w, .reg r)

-- ============================================================================
-- Memory & General Operand Elaboration
-- ============================================================================

/-- Finalize parenthesized memory addressing given optional displacement, base register, index register, and scale. -/
private def buildParenMem (stx : Syntax) (disp : ConstExpr) (baseStx : TSyntax `x64_reg)
    (idxStx? : Option (TSyntax `x64_reg)) (scaleNat : Nat) : TermElabM (Width × AddrExpr) := do
  let (wBase, base) ← elabRegOrRip baseStx
  let idx? ← idxStx?.mapM elabLowReg
  let scaleWidth ← match scaleNat with
    | 1 => pure Width.W8
    | 2 => pure Width.W16
    | 4 => pure Width.W32
    | 8 => pure Width.W64
    | s => throwErrorAt stx "invalid scale {s}, must be 1, 2, 4, or 8"
  let addrW ← match wBase, idx? with
    | w1, some (w2, _) =>
      if w1 ≠ w2 then
        throwErrorAt stx "type mismatch in memory addressing operands: base ({w1}) and index ({w2}) have different widths"
      else pure w1
    | w1, none => pure w1
  let idx := idx?.map fun (_, reg) => ({ reg, scale := scaleWidth } : AddrIndex)
  let finalDisp := match base, disp with
    | .rip, .int64 _ => disp
    | .rip, _        => .sub disp .after_current_instruction
    | _, _           => disp
  pure (addrW, { base := some base, idx, disp := finalDisp })

/-- Elaborate an `x64_mem` syntax node into `(address_width, AddrExpr)`. -/
def elabMem (stx : TSyntax `x64_mem) : TermElabM (Width × AddrExpr) :=
  match stx with
  | `(x64_mem| ($base:x64_reg)) =>
    buildParenMem stx (.int64 0) base none 1
  | `(x64_mem| $disp:x64_const($base:x64_reg)) => do
    buildParenMem stx (← elabConstExpr disp) base none 1
  | `(x64_mem| ($base:x64_reg, $idx:x64_reg)) =>
    buildParenMem stx (.int64 0) base (some idx) 1
  | `(x64_mem| $disp:x64_const($base:x64_reg, $idx:x64_reg)) => do
    buildParenMem stx (← elabConstExpr disp) base (some idx) 1
  | `(x64_mem| ($base:x64_reg, $idx:x64_reg, $sc:num)) =>
    buildParenMem stx (.int64 0) base (some idx) sc.getNat
  | `(x64_mem| $disp:x64_const($base:x64_reg, $idx:x64_reg, $sc:num)) => do
    buildParenMem stx (← elabConstExpr disp) base (some idx) sc.getNat
  | `(x64_mem| $disp:x64_const) => do
    let d ← elabConstExpr disp
    pure (.W64, { base := none, idx := none, disp := d })
  | _ => throwErrorAt stx "invalid memory operand"

/-- Extract symbol name from an antiquotation syntax node (`$sym`). -/
def getAntiquotSym (stx : Syntax) : TermElabM String :=
  if stx.isAntiquot then
    match stx.getAntiquotTerm.getId with
    | .str .anonymous s => pure s
    | n =>
      if !n.isAnonymous then pure n.toString
      else throwErrorAt stx "invalid operand"
  else
    throwErrorAt stx "invalid operand"

/-- Elaborate an `x64_imm` (`$const`) into a `ConstExpr`. -/
def elabImmConst : TSyntax `x64_imm → TermElabM ConstExpr
  | ⟨.node _ _ #[.atom _ "$", c]⟩ => elabConstExpr ⟨c⟩
  | stx => throwErrorAt stx "invalid immediate operand"

/-- Elaborate an `x64_operand` into a width-polymorphic `Operand`. -/
def elabOperand (stx : TSyntax `x64_operand) : TermElabM (MaybeAddrWidth × MaybeOpWidth Operand) :=
  if stx.raw.isAntiquot then do
    let s ← getAntiquotSym stx.raw
    let ce : ConstExpr := .label s
    pure (none, ⟨none, fun {w} => (@Operand.imm w ce)⟩)
  else match stx with
  | `(x64_operand| $r:x64_reg) => do
    let ⟨w, reg⟩ ← elabRegW r
    pure (none, ⟨some w, .reg reg⟩)
  | `(x64_operand| $imm:x64_imm) => do
    let ce ← elabImmConst imm
    pure (none, ⟨none, fun {w} => (@Operand.imm w ce)⟩)
  | `(x64_operand| $op:x64_operand + $n:num) => do
    let s ← getAntiquotSym op.raw
    let i ← intToInt64Checked n (Int.ofNat n.getNat)
    let ce : ConstExpr := .add (.label s) (.int64 i)
    pure (none, ⟨none, fun {w} => (@Operand.imm w ce)⟩)
  | `(x64_operand| $op:x64_operand - $n:num) => do
    let s ← getAntiquotSym op.raw
    let i ← intToInt64Checked n (Int.ofNat n.getNat)
    let ce : ConstExpr := .sub (.label s) (.int64 i)
    pure (none, ⟨none, fun {w} => (@Operand.imm w ce)⟩)
  | `(x64_operand| $m:x64_mem) => do
    let (w, mem) ← elabMem m
    pure (some w, ⟨none, fun {w} => (@Operand.mem w mem)⟩)
  | _ => throwErrorAt stx "invalid operand"

/-- Elaborate an `x64_operand` into a width-polymorphic `RegOrMem`. -/
def elabRegOrMem (stx : TSyntax `x64_operand) : TermElabM (MaybeAddrWidth × MaybeOpWidth RegOrMem) :=
  if stx.raw.isAntiquot then
    throwErrorAt stx "expected register or memory operand, got $"
  else match stx with
  | `(x64_operand| $r:x64_reg) => do
    let ⟨w, reg⟩ ← elabRegW r
    pure (none, ⟨some w, .reg reg⟩)
  | `(x64_operand| $_:x64_imm)
  | `(x64_operand| $_:x64_operand + $_:num)
  | `(x64_operand| $_:x64_operand - $_:num) =>
    throwErrorAt stx "expected register or memory operand, got $"
  | `(x64_operand| $m:x64_mem) => do
    let (w, mem) ← elabMem m
    pure (some w, ⟨none, fun {w} => (@RegOrMem.mem w mem)⟩)
  | _ => throwErrorAt stx "expected register or memory operand"

/-- Elaborate an `x64_operand` into a width-polymorphic `AvxRegOrMem`. -/
def elabAvxRegOrMem (stx : TSyntax `x64_operand) : TermElabM (MaybeAddrWidth × MaybeAvxOpWidth AvxRegOrMem) :=
  if stx.raw.isAntiquot then
    throwErrorAt stx "expected AVX register or memory operand, got $"
  else match stx with
  | `(x64_operand| $r:x64_reg) => do
    let ⟨w, reg⟩ ← elabAvxRegW r
    pure (none, ⟨some w, .avx reg⟩)
  | `(x64_operand| $_:x64_imm)
  | `(x64_operand| $_:x64_operand + $_:num)
  | `(x64_operand| $_:x64_operand - $_:num) =>
    throwErrorAt stx "expected AVX register or memory operand, got $"
  | `(x64_operand| $m:x64_mem) => do
    let (w, mem) ← elabMem m
    pure (some w, ⟨none, fun {w} => (@AvxRegOrMem.mem w mem)⟩)
  | _ => throwErrorAt stx "expected AVX register or memory operand"

/-- Elaborate an `x64_operand` as a register only (for destinations requiring a register). -/
def elabRegOnly (stx : TSyntax `x64_operand) : TermElabM (MaybeAddrWidth × MaybeOpWidth Reg) :=
  match stx with
  | `(x64_operand| $r:x64_reg) => do
    let ⟨w, reg⟩ ← elabRegW r
    pure (none, ⟨some w, reg⟩)
  | _ =>
    throwErrorAt stx "expected register operand"

/-- Elaborate an `x64_operand` into a relative branch target (`RelRegOrMem`). -/
def elabRelTarget (stx : TSyntax `x64_operand) : TermElabM (MaybeAddrWidth × RelRegOrMem) :=
  match stx with
  | `(x64_operand| $r:x64_reg) => do
    let ⟨w, reg⟩ ← elabRegW r
    if h : w = .W64 then
      pure (none, .reg (h ▸ reg))
    else
      throwErrorAt r "expected a 64-bit register in relative addressing position"
  | `(x64_operand| $m:x64_mem) =>
    match m with
    | `(x64_mem| $c:x64_const) =>
      match c with
      | `(x64_const| $id:x64_ident) => do
        let lbl ← getAsmIdent id
        pure (none, .rel (.sub (.label lbl) .after_current_instruction))
      | _ =>
        throwErrorAt m "absolute branch targets are not supported"
    | _ => do
      let (w, mem) ← elabMem m
      if mem.base.isNone && mem.idx.isNone then
        throwErrorAt m "absolute branch targets are not supported"
      pure (some w, .mem mem)
  | _ => throwErrorAt stx "invalid branch target operand"

/-- Elaborate a shift count operand (`$imm` or `%cl`). -/
def elabShiftCount (stx : TSyntax `x64_operand) : TermElabM ShiftCountExpr :=
  match stx with
  | `(x64_operand| $imm:x64_imm) => do
    let ce ← elabImmConst imm
    pure (.imm8 ce)
  | `(x64_operand| %cl) => pure .cl
  | `(x64_operand| $r:x64_reg) =>
    throwErrorAt r "shift count register must be %cl"
  | _ => throwErrorAt stx "expected immediate or %cl shift count"

-- ============================================================================
-- Width Unification Helpers
-- ============================================================================

def mergeAddrM (stx : Syntax) (w1 w2 : MaybeAddrWidth) : TermElabM MaybeAddrWidth :=
  match w1, w2 with
  | none, none => pure none
  | some w, none | none, some w => pure (some w)
  | some _, some _ => throwErrorAt stx "can't have two memory operands"

def ascribeM {T : Width → Type} (stx : Syntax) (w : Width) (v : MaybeOpWidth T) : TermElabM (T w) :=
  match v with
  | ⟨none, f⟩ => pure f
  | ⟨some w2, x⟩ =>
    if h : w = w2 then pure (h ▸ x)
    else throwErrorAt stx "type error: {w} != {w2}"

def ascribeAvxM {T : AvxWidth → Type} (stx : Syntax) (w : AvxWidth) (v : MaybeAvxOpWidth T) : TermElabM (T w) :=
  match v with
  | ⟨none, f⟩ => pure f
  | ⟨some w2, x⟩ =>
    if h : w = w2 then pure (h ▸ x)
    else throwErrorAt stx "type error: {w} != {w2}"

def requireWidthM {T : Width → Type} (stx : Syntax) (v : MaybeOpWidth T) : TermElabM (Σ w : Width, T w) :=
  match v with
  | ⟨none, _⟩ => throwErrorAt stx "missing type annotation"
  | ⟨some w, x⟩ => pure ⟨w, x⟩

def charWidthM (stx : Syntax) (c : Char) : TermElabM Width :=
  match c with
  | 'b' => pure .W8
  | 'w' => pure .W16
  | 'l' => pure .W32
  | 'q' => pure .W64
  | _   => throwErrorAt stx "unknown width suffix: {c}"

def suffixWidthM (stx : Syntax) (mn : String) : TermElabM Width :=
  match mn.back? with
  | some c => charWidthM stx c
  | none   => throwErrorAt stx "empty mnemonic"

def elabCondCodeM (stx : Syntax) (cc : String) : TermElabM CondCode :=
  match cc.toLower with
  | "z"  | "e"           => pure .z
  | "nz" | "ne"          => pure .nz
  | "b"  | "c"  | "nae"  => pure .b
  | "ae" | "nc" | "nb"   => pure .ae
  | "a"  | "nbe"         => pure .a
  | "be" | "na"          => pure .be
  | "l"  | "nge"         => pure .l
  | "le" | "ng"          => pure .le
  | _ => throwErrorAt stx "unknown condition code: {cc}"

-- ============================================================================
-- Instruction Family Elaborators
-- ============================================================================

abbrev OperandStx := TSyntax `x64_operand

/-- Elaborate two-operand AT&T instructions (`op src, dst`). -/
def elabBinaryInstr {T1 T2 : Width → Type}
    (stx : Syntax) (opW : Option Width) (ops : Array OperandStx)
    (e1 : OperandStx → TermElabM (MaybeAddrWidth × MaybeOpWidth T1))
    (e2 : OperandStx → TermElabM (MaybeAddrWidth × MaybeOpWidth T2))
    (mk : {w : Width} → T2 w → T1 w → Operation w) : TermElabM Instr := do
  match ops with
  | #[op1, op2] =>
    let (aw1, v1) ← e1 op1
    let (aw2, v2) ← e2 op2
    let aw ← mergeAddrM stx aw1 aw2
    match opW with
    | some w =>
      let s1 ← ascribeM op1 w v1
      let d2 ← ascribeM op2 w v2
      pure (toInstr aw (mk d2 s1))
    | none =>
      match v1 with
      | ⟨some w1, s1⟩ =>
        let d2 ← ascribeM op2 w1 v2
        pure (toInstr aw (mk d2 s1))
      | ⟨none, f1⟩ =>
        match v2 with
        | ⟨some _, d2⟩ => pure (toInstr aw (mk d2 f1))
        | ⟨none, _⟩ => throwErrorAt stx "missing type annotation"
  | _ =>
    match ops.toList with
    | op1 :: op2 :: _ =>
      let _ ← e1 op1
      let _ ← e2 op2
      throwErrorAt stx "expected 2 operands, got {ops.size}"
    | [op1] =>
      let _ ← e1 op1
      throwErrorAt stx "expected 2 operands, got {ops.size}"
    | [] =>
      throwErrorAt stx "expected 2 operands, got {ops.size}"

/-- Elaborate two-operand AVX instructions (`op src, dst`). -/
def elabAvxBinaryInstr (stx : Syntax) (ops : Array OperandStx)
    (mk : {w : AvxWidth} → AvxRegOrMem w → AvxRegOrMem w → AvxOperation w) : TermElabM Instr := do
  match ops with
  | #[op1, op2] =>
    let (aw1, v1) ← elabAvxRegOrMem op1
    let (aw2, v2) ← elabAvxRegOrMem op2
    let aw ← mergeAddrM stx aw1 aw2
    match v1 with
    | ⟨some w1, s1⟩ =>
      let d2 ← ascribeAvxM op2 w1 v2
      pure (toAvxInstr aw (mk d2 s1))
    | ⟨none, f1⟩ =>
      match v2 with
      | ⟨some _, d2⟩ => pure (toAvxInstr aw (mk d2 f1))
      | ⟨none, _⟩ => throwErrorAt stx "missing AVX vector width annotation"
  | _ => throwErrorAt stx "expected 2 operands, got {ops.size}"

/-- Elaborate one-operand AT&T instructions (`op dst`). -/
def elabUnaryInstr (stx : Syntax) (opW : Option Width) (ops : Array OperandStx)
    (mk : {w : Width} → RegOrMem w → Operation w) : TermElabM Instr := do
  match ops with
  | #[op1] =>
    let (aw, v) ← elabRegOrMem op1
    match opW with
    | some w =>
      let d ← ascribeM op1 w v
      pure (toInstr aw (mk d))
    | none =>
      let ⟨_, d⟩ ← requireWidthM op1 v
      pure (toInstr aw (mk d))
  | _ => throwErrorAt stx "expected 1 operand, got {ops.size}"

/-- Elaborate shift/rotate instructions (`shl dst` or `shl cnt, dst`). -/
def elabShiftInstr (stx : Syntax) (opW : Option Width) (ops : Array OperandStx)
    (mk : {w : Width} → RegOrMem w → ShiftCountExpr → Operation w) : TermElabM Instr := do
  let (cnt, dstStx) ← match ops with
    | #[dst] => pure (.imm8 (.int64 1), dst)
    | #[cntStx, dst] => pure (← elabShiftCount cntStx, dst)
    | _ => throwErrorAt stx "expected 1 or 2 operands, got {ops.size}"
  let (aw, v) ← elabRegOrMem dstStx
  match opW with
  | some w =>
    let d ← ascribeM dstStx w v
    pure (toInstr aw (mk d cnt))
  | none =>
    let ⟨_, d⟩ ← requireWidthM dstStx v
    pure (toInstr aw (mk d cnt))

/-- Elaborate 1-, 2-, or 3-operand `imul*` instructions. -/
def elabImulInstr (stx : Syntax) (opW : Option Width) (ops : Array OperandStx) : TermElabM Instr := do
  match ops with
  | #[op1] =>
    let (aw, v) ← elabRegOrMem op1
    match opW with
    | some w =>
      let src ← ascribeM op1 w v
      pure (toInstr aw (.imul1 src))
    | none =>
      let ⟨_, src⟩ ← requireWidthM op1 v
      pure (toInstr aw (.imul1 src))
  | #[op1, op2] =>
    let (aw1, v1) ← elabOperand op1
    let (aw2, v2) ← elabRegOrMem op2
    let aw ← mergeAddrM stx aw1 aw2
    match opW with
    | some w =>
      let s1 ← ascribeM op1 w v1
      let s2 ← ascribeM op2 w v2
      pure (toInstr aw (.imul none s2 s1))
    | none =>
      match v1 with
      | ⟨some w1, s1⟩ =>
        let s2 ← ascribeM op2 w1 v2
        pure (toInstr aw (.imul none s2 s1))
      | ⟨none, f1⟩ =>
        match v2 with
        | ⟨some _, s2⟩ => pure (toInstr aw (.imul none s2 f1))
        | ⟨none, _⟩ => throwErrorAt stx "missing type annotation"
  | #[op1, op2, op3] =>
    let (aw1, v1) ← elabOperand op1
    let (aw2, v2) ← elabRegOrMem op2
    let (aw3, v3) ← elabRegOnly op3
    let aw12 ← mergeAddrM stx aw1 aw2
    let aw ← mergeAddrM stx aw12 aw3
    match opW with
    | some w =>
      let s1 ← ascribeM op1 w v1
      let s2 ← ascribeM op2 w v2
      let dst ← ascribeM op3 w v3
      pure (toInstr aw (.imul (some (.reg dst)) s2 s1))
    | none =>
      let ⟨w3, dst⟩ ← requireWidthM op3 v3
      let s2 ← ascribeM op2 w3 v2
      let s1 ← ascribeM op1 w3 v1
      pure (toInstr aw (.imul (some (.reg dst)) s2 s1))
  | _ => throwErrorAt stx "imul expects 1, 2, or 3 operands, got {ops.size}"

/-- Extract a raw unsigned natural literal from an operand syntax node (for `nop N` and `.align N, pad`). -/
def elabNatOperand (stx : OperandStx) : TermElabM Nat := do
  let (_, v) ← elabOperand stx
  match v with
  | ⟨none, f⟩ =>
    match (@f .W64) with
    | .regOrMem (.mem { base := none, idx := none, disp := .int64 i }) =>
      if i.toInt < 0 then throwErrorAt stx "expected non-negative integer literal"
      else pure i.toInt.toNat
    | _ => throwErrorAt stx "expected integer literal"
  | _ => throwErrorAt stx "expected integer literal"

/-- Elaborate a concrete `x64_instr` syntax node into a `Lean.Expr` of type `Instr`. -/
def elabInstr (stx : TSyntax `x64_instr) : TermElabM Expr :=
  match stx with
  | `(x64_instr| ${ $t:term }) => elabTerm t (some (mkConst ``Instr))
  | `(x64_instr| $mnStx:x64_ident $opSep:x64_operand,*) => do
    let mnemonic ← getAsmIdent mnStx
    let mn := mnemonic.toLower
    let ops : Array OperandStx := opSep.getElems
    let instr : Instr ← match mn with
      | ".align" => do
        match ops with
        | #[op1] =>
          let align ← elabNatOperand op1
          pure (toInstr none (w := .W64) (.nopalign align none))
        | #[op1, op2] =>
          let align ← elabNatOperand op1
          let pad ← elabNatOperand op2
          pure (toInstr none (w := .W64) (.nopalign align (some pad)))
        | _ =>
          throwErrorAt stx ".align expects 1 or 2 operands"
      | "add" => elabBinaryInstr stx none ops elabOperand elabRegOrMem .add
      | "addq" | "addl" | "addw" | "addb" => do
        elabBinaryInstr stx (some (← suffixWidthM mnStx mn)) ops elabOperand elabRegOrMem .add
      | "adc" => elabBinaryInstr stx none ops elabOperand elabRegOrMem .adc
      | "adcq" | "adcl" | "adcw" | "adcb" => do
        elabBinaryInstr stx (some (← suffixWidthM mnStx mn)) ops elabOperand elabRegOrMem .adc
      | "adcx" => elabBinaryInstr stx none ops elabRegOrMem elabRegOnly .adcx
      | "adcxq" | "adcxl" => do
        elabBinaryInstr stx (some (← suffixWidthM mnStx mn)) ops elabRegOrMem elabRegOnly .adcx
      | "adox" => elabBinaryInstr stx none ops elabRegOrMem elabRegOnly .adox
      | "adoxq" | "adoxl" => do
        elabBinaryInstr stx (some (← suffixWidthM mnStx mn)) ops elabRegOrMem elabRegOnly .adox
      | "sub" => elabBinaryInstr stx none ops elabOperand elabRegOrMem .sub
      | "subq" | "subl" | "subw" | "subb" => do
        elabBinaryInstr stx (some (← suffixWidthM mnStx mn)) ops elabOperand elabRegOrMem .sub
      | "sbb" => elabBinaryInstr stx none ops elabOperand elabRegOrMem .sbb
      | "sbbq" | "sbbl" | "sbbw" | "sbbb" => do
        elabBinaryInstr stx (some (← suffixWidthM mnStx mn)) ops elabOperand elabRegOrMem .sbb
      | "mul" => elabUnaryInstr stx none ops .mul
      | "mulq" | "mull" | "mulw" | "mulb" => do
        elabUnaryInstr stx (some (← suffixWidthM mnStx mn)) ops .mul
      | "mulx" => do
        match ops with
        | #[op1, op2, op3] =>
          let (aw, src) ← elabRegOrMem op1
          let ⟨_, vLo⟩ ← elabRegOnly op2
          let ⟨_, vHi⟩ ← elabRegOnly op3
          let ⟨w1, lo⟩ ← requireWidthM op2 vLo
          let ⟨w2, hi⟩ ← requireWidthM op3 vHi
          if h : w1 = w2 then
            let s ← ascribeM op1 w1 src
            pure (toInstr aw (.mulx (h ▸ hi) lo s))
          else throwErrorAt stx "mulx not homogenous"
        | _ => throwErrorAt stx "mulx expects 3 operands"
      | "mulxq" | "mulxl" => do
        match ops with
        | #[op1, op2, op3] =>
          let w ← suffixWidthM mnStx mn
          let (aw, vSrc) ← elabRegOrMem op1
          let (_, vLo) ← elabRegOnly op2
          let (_, vHi) ← elabRegOnly op3
          let src ← ascribeM op1 w vSrc
          let lo ← ascribeM op2 w vLo
          let hi ← ascribeM op3 w vHi
          pure (toInstr aw (.mulx hi lo src))
        | _ => throwErrorAt stx "mulx expects 3 operands"
      | "imul" => elabImulInstr stx none ops
      | "imulq" | "imull" | "imulw" | "imulb" => do
        elabImulInstr stx (some (← suffixWidthM mnStx mn)) ops
      | "neg" => elabUnaryInstr stx none ops .neg
      | "negq" | "negl" | "negw" | "negb" => do
        elabUnaryInstr stx (some (← suffixWidthM mnStx mn)) ops .neg
      | "dec" => elabUnaryInstr stx none ops .dec
      | "decq" | "decl" | "decw" | "decb" => do
        elabUnaryInstr stx (some (← suffixWidthM mnStx mn)) ops .dec
      | "inc" => elabUnaryInstr stx none ops .inc
      | "incq" | "incl" | "incw" | "incb" => do
        elabUnaryInstr stx (some (← suffixWidthM mnStx mn)) ops .inc
      | "mov" | "movabs" => elabBinaryInstr stx none ops elabOperand elabRegOrMem .mov
      | "movq" | "movl" | "movw" | "movb"
      | "movabsq" | "movabsl" | "movabsw" | "movabsb" => do
        elabBinaryInstr stx (some (← suffixWidthM mnStx mn)) ops elabOperand elabRegOrMem .mov
      | "movsx" => do
        match ops with
        | #[op1, op2] =>
          let (_, v1) ← elabRegOnly op1
          let (_, v2) ← elabRegOnly op2
          let ⟨_, src⟩ ← requireWidthM op1 v1
          let ⟨_, dst⟩ ← requireWidthM op2 v2
          pure (toInstr none (.movsx (.reg dst) (.reg src)))
        | _ => throwErrorAt stx "movsx expects 2 register operands"
      | "movzx" => do
        match ops with
        | #[op1, op2] =>
          let (_, v1) ← elabRegOnly op1
          let (_, v2) ← elabRegOnly op2
          let ⟨_, src⟩ ← requireWidthM op1 v1
          let ⟨_, dst⟩ ← requireWidthM op2 v2
          pure (toInstr none (.movzx (.reg dst) (.reg src)))
        | _ => throwErrorAt stx "movzx expects 2 register operands"
      | "movsbw" | "movsbl" | "movsbq" | "movswl" | "movswq" | "movslq" => do
        match ops with
        | #[op1, op2] =>
          let wDst ← suffixWidthM mnStx mn
          let some cSrc := String.Pos.Raw.get? mn ⟨mn.length - 2⟩
            | throwErrorAt mnStx "invalid mnemonic {mn}"
          let wSrc ← charWidthM mnStx cSrc
          let (aw, vSrc) ← elabRegOrMem op1
          let (_, vDst) ← elabRegOnly op2
          let src ← ascribeM op1 wSrc vSrc
          let dst ← ascribeM op2 wDst vDst
          pure (toInstr aw (.movsx (.reg dst) src))
        | _ => throwErrorAt stx "{mn} expects 2 operands"
      | "movsxd" => do
        match ops with
        | #[op1, op2] =>
          let (aw, vSrc) ← elabRegOrMem op1
          let (_, vDst) ← elabRegOnly op2
          let src ← ascribeM op1 .W32 vSrc
          let dst ← ascribeM op2 .W64 vDst
          pure (toInstr aw (.movsx (.reg dst) src))
        | _ => throwErrorAt stx "movsxd expects 2 operands"
      | "movzbw" | "movzbl" | "movzbq" | "movzwl" | "movzwq" => do
        match ops with
        | #[op1, op2] =>
          let wDst ← suffixWidthM mnStx mn
          let some cSrc := String.Pos.Raw.get? mn ⟨mn.length - 2⟩
            | throwErrorAt mnStx "invalid mnemonic {mn}"
          let wSrc ← charWidthM mnStx cSrc
          let (aw, vSrc) ← elabRegOrMem op1
          let (_, vDst) ← elabRegOnly op2
          let src ← ascribeM op1 wSrc vSrc
          let dst ← ascribeM op2 wDst vDst
          pure (toInstr aw (.movzx (.reg dst) src))
        | _ => throwErrorAt stx "{mn} expects 2 operands"
      | "lea" => do
        match ops with
        | #[op1, op2] =>
          let m ← match op1 with
            | `(x64_operand| $m:x64_mem) => pure m
            | _ => throwErrorAt op1 "expected memory operand"
          let (addrW, src) ← elabMem m
          let (_, vDst) ← elabRegOnly op2
          let ⟨_, dst⟩ ← requireWidthM op2 vDst
          pure (toInstr (some addrW) (.lea dst src))
        | _ => throwErrorAt stx "lea expects 2 operands"
      | "leaq" | "leal" | "leaw" | "leab" => do
        match ops with
        | #[op1, op2] =>
          let w2 ← suffixWidthM mnStx mn
          let m ← match op1 with
            | `(x64_operand| $m:x64_mem) => pure m
            | _ => throwErrorAt op1 "expected memory operand"
          let (addrW, src) ← elabMem m
          let (_, vDst) ← elabRegOnly op2
          let dst ← ascribeM op2 w2 vDst
          pure (toInstr (some addrW) (.lea dst src))
        | _ => throwErrorAt stx "{mn} expects 2 operands"
      | "movups"  => elabAvxBinaryInstr stx ops .movups
      | "vmovups" => elabAvxBinaryInstr stx ops .vmovups
      | "movaps"  => elabAvxBinaryInstr stx ops .movaps
      | "addps"   => elabAvxBinaryInstr stx ops .addps
      | "subps"   => elabAvxBinaryInstr stx ops .subps
      | "xor" => elabBinaryInstr stx none ops elabOperand elabRegOrMem .xor
      | "xorq" | "xorl" | "xorw" | "xorb" => do
        elabBinaryInstr stx (some (← suffixWidthM mnStx mn)) ops elabOperand elabRegOrMem .xor
      | "and" => elabBinaryInstr stx none ops elabOperand elabRegOrMem .and
      | "andq" | "andl" | "andw" | "andb" => do
        elabBinaryInstr stx (some (← suffixWidthM mnStx mn)) ops elabOperand elabRegOrMem .and
      | "not" => elabUnaryInstr stx none ops .not
      | "notq" | "notl" | "notw" | "notb" => do
        elabUnaryInstr stx (some (← suffixWidthM mnStx mn)) ops .not
      | "or" => elabBinaryInstr stx none ops elabOperand elabRegOrMem .or
      | "orq" | "orl" | "orw" | "orb" => do
        elabBinaryInstr stx (some (← suffixWidthM mnStx mn)) ops elabOperand elabRegOrMem .or
      | "cmp" => elabBinaryInstr stx none ops elabOperand elabRegOrMem .cmp
      | "cmpq" | "cmpl" | "cmpw" | "cmpb" => do
        elabBinaryInstr stx (some (← suffixWidthM mnStx mn)) ops elabOperand elabRegOrMem .cmp
      | "test" => elabBinaryInstr stx none ops elabOperand elabRegOrMem .test
      | "testq" | "testl" | "testw" | "testb" => do
        elabBinaryInstr stx (some (← suffixWidthM mnStx mn)) ops elabOperand elabRegOrMem .test
      | "shl" | "sal" => elabShiftInstr stx none ops .shl
      | "shlq" | "shll" | "shlw" | "shlb" | "salq" | "sall" | "salw" | "salb" => do
        elabShiftInstr stx (some (← suffixWidthM mnStx mn)) ops .shl
      | "shr" => elabShiftInstr stx none ops .shr
      | "shrq" | "shrl" | "shrw" | "shrb" => do
        elabShiftInstr stx (some (← suffixWidthM mnStx mn)) ops .shr
      | "sar" => elabShiftInstr stx none ops .sar
      | "sarq" | "sarl" | "sarw" | "sarb" => do
        elabShiftInstr stx (some (← suffixWidthM mnStx mn)) ops .sar
      | "shld" => do
        match ops with
        | #[op1, op2, op3] =>
          let cnt ← elabShiftCount op1
          elabBinaryInstr stx none #[op2, op3] elabRegOnly elabRegOrMem fun dst src => .shld dst src cnt
        | _ => throwErrorAt stx "shld expects 3 operands"
      | "shldq" | "shldl" | "shldw" => do
        match ops with
        | #[op1, op2, op3] =>
          let cnt ← elabShiftCount op1
          elabBinaryInstr stx (some (← suffixWidthM mnStx mn)) #[op2, op3] elabRegOnly elabRegOrMem fun dst src => .shld dst src cnt
        | _ => throwErrorAt stx "{mn} expects 3 operands"
      | "shrd" => do
        match ops with
        | #[op1, op2, op3] =>
          let cnt ← elabShiftCount op1
          elabBinaryInstr stx none #[op2, op3] elabRegOnly elabRegOrMem fun dst src => .shrd dst src cnt
        | _ => throwErrorAt stx "shrd expects 3 operands"
      | "shrdq" | "shrdl" | "shrdw" => do
        match ops with
        | #[op1, op2, op3] =>
          let cnt ← elabShiftCount op1
          elabBinaryInstr stx (some (← suffixWidthM mnStx mn)) #[op2, op3] elabRegOnly elabRegOrMem fun dst src => .shrd dst src cnt
        | _ => throwErrorAt stx "{mn} expects 3 operands"
      | "rol" => elabShiftInstr stx none ops .rol
      | "rolq" | "roll" | "rolw" | "rolb" => do
        elabShiftInstr stx (some (← suffixWidthM mnStx mn)) ops .rol
      | "ror" => elabShiftInstr stx none ops .ror
      | "rorq" | "rorl" | "rorw" | "rorb" => do
        elabShiftInstr stx (some (← suffixWidthM mnStx mn)) ops .ror
      | "rcl" => elabShiftInstr stx none ops .rcl
      | "rclq" | "rcll" | "rclw" | "rclb" => do
        elabShiftInstr stx (some (← suffixWidthM mnStx mn)) ops .rcl
      | "rcr" => elabShiftInstr stx none ops .rcr
      | "rcrq" | "rcrl" | "rcrw" | "rcrb" => do
        elabShiftInstr stx (some (← suffixWidthM mnStx mn)) ops .rcr
      | "bswap" => do
        match ops with
        | #[op1] =>
          let (_, v) ← elabRegOnly op1
          let ⟨_, dst⟩ ← requireWidthM op1 v
          pure (toInstr none (.bswap dst))
        | _ => throwErrorAt stx "bswap expects 1 operand"
      | "bswapq" | "bswapl" => do
        match ops with
        | #[op1] =>
          let w2 ← suffixWidthM mnStx mn
          let (_, v) ← elabRegOnly op1
          let dst ← ascribeM op1 w2 v
          pure (toInstr none (.bswap dst))
        | _ => throwErrorAt stx "{mn} expects 1 operand"
      | "push" => do
        match ops with
        | #[op1] =>
          let (aw, v) ← elabOperand op1
          let src ← ascribeM op1 (v.1.getD .W64) v
          pure (toInstr aw (.push src))
        | _ => throwErrorAt stx "push expects 1 operand"
      | "pushq" | "pushl" | "pushw" | "pushb" => do
        match ops with
        | #[op1] =>
          let w ← suffixWidthM mnStx mn
          let (aw, v) ← elabOperand op1
          let src ← ascribeM op1 w v
          pure (toInstr aw (.push src))
        | _ => throwErrorAt stx "{mn} expects 1 operand"
      | "pop" => do
        match ops with
        | #[op1] =>
          let (aw, v) ← elabRegOrMem op1
          let dst ← ascribeM op1 (v.1.getD .W64) v
          pure (toInstr aw (.pop dst))
        | _ => throwErrorAt stx "pop expects 1 operand"
      | "popq" | "popl" | "popw" | "popb" => do
        match ops with
        | #[op1] =>
          let w ← suffixWidthM mnStx mn
          let (aw, v) ← elabRegOrMem op1
          let dst ← ascribeM op1 w v
          pure (toInstr aw (.pop dst))
        | _ => throwErrorAt stx "{mn} expects 1 operand"
      | "ret" | "retq" => do
        match ops with
        | #[] => pure (toInstr none (w := .W64) .ret)
        | _ => throwErrorAt stx "{mn} takes no operands"
      | "call" | "callq" => do
        match ops with
        | #[op1] =>
          let (aw, target) ← elabRelTarget op1
          pure (toInstr aw (w := .W64) (.call target))
        | _ => throwErrorAt stx "{mn} expects 1 operand"
      | "jmp" | "jmpq" => do
        match ops with
        | #[op1] =>
          let (aw, target) ← elabRelTarget op1
          pure (toInstr aw (w := .W64) (.jmp target))
        | _ => throwErrorAt stx "{mn} expects 1 operand"
      | "nop" => do
        match ops with
        | #[] => pure (toInstr none (w := .W64) (.nop 1))
        | #[op1] =>
          let sz ← elabNatOperand op1
          pure (toInstr none (w := .W64) (.nop sz))
        | _ => throwErrorAt stx "nop expects at most 1 operand"
      | _ => do
        if mn.startsWith "j" then
          match ops with
          | #[op] =>
            let cc ← elabCondCodeM mnStx (mn.drop 1).toString
            match op with
            | `(x64_operand| $id:x64_ident) =>
              let target ← getAsmIdent id
              pure (toInstr none (w := .W64) (.jcc cc target))
            | _ => throwErrorAt op "expected label target"
          | _ => throwErrorAt stx "{mn} expects 1 target label operand"
        else if mn.startsWith "set" then
          match ops with
          | #[op] =>
            let cc ← elabCondCodeM mnStx (mn.drop 3).toString
            let (aw, vDst) ← elabRegOrMem op
            let dst ← ascribeM op .W8 vDst
            pure (toInstr aw (.setcc cc dst))
          | _ => throwErrorAt stx "{mn} expects 1 operand"
        else if mn.startsWith "cmov" then
          let cc ← elabCondCodeM mnStx (mn.drop 4).toString
          elabBinaryInstr stx none ops elabRegOrMem elabRegOnly (.cmovcc cc)
        else
          throwErrorAt mnStx "unsupported instruction: {mnemonic}"
    pure (Lean.toExpr instr)
  | _ => throwErrorAt stx "invalid instruction syntax"

-- ============================================================================
-- Directive & Program Elaboration
-- ============================================================================

/-- Elaborate an `x64_directive` syntax node into a `Lean.Expr` of type `Directive`. -/
def elabDirective (stx : TSyntax `x64_directive) : TermElabM Expr :=
  match stx with
  | `(x64_directive| $lbl:x64_ident :)
  | `(x64_directive| $lbl:x64_ident : ;) => do
    let name ← getAsmIdent lbl
    pure (Lean.toExpr (Directive.label name))
  | `(x64_directive| $ins:x64_instr ;)
  | `(x64_directive| $ins:x64_instr) => do
    let insExpr ← elabInstr ins
    mkAppM ``Directive.instr #[insExpr]
  | `(x64_directive| ${ $t:term } ;)
  | `(x64_directive| ${ $t:term }) =>
    elabTerm t (some (mkConst ``Directive))
  | _ => throwErrorAt stx "invalid assembly directive"

/-- Elaborate an `x64_prog` syntax node into a `Lean.Expr` of type `Program` (`List Directive`). -/
def elabProgram (stx : TSyntax `x64_prog) : TermElabM Expr := do
  match stx with
  | `(x64_prog| $dirs:x64_directive*) =>
    let dirExprs ← dirs.mapM elabDirective
    mkListLit (mkConst ``Directive) dirExprs.toList
  | _ => throwErrorAt stx "invalid assembly program"

-- ============================================================================
-- Public String Parser/Elaborator & Macros
-- ============================================================================

/-- Replace X64 `# ...` line comments with Lean `-- ...` comments so comments are preserved in `Syntax`. -/
private def replaceX64Comments (input : String) : String :=
  String.intercalate "\n" <| input.splitOn "\n" |>.map fun line =>
    match line.splitOn "#" with
    | [] => ""
    | code :: rest =>
      if rest.isEmpty then code
      else code ++ "--" ++ String.intercalate "#" rest

/-- Parse and elaborate an X64 assembly string into a `Lean.Expr` representing a Kraken `Program`,
    using `Lean.Parser.runParserCategory` on the `x64_prog` syntax category. -/
public def elabX64 (s : String) : TermElabM Lean.Expr := do
  match Parser.runParserCategory (← getEnv) `x64_prog (replaceX64Comments s) with
  | .ok stx    => elabProgram ⟨stx⟩
  | .error err => throwError "{err}"

end

/-- Inline unquoted X64 assembly block macro/elaborator (`[x64| ... ]`). -/
elab "[x64|" p:x64_prog "]" : term => elabProgram p

/-- Inline unquoted X64 assembly block macro/elaborator (`parse( ... )`). -/
elab "parse(" p:x64_prog ")" : term => elabProgram p

/-- Compile-time X64 string parser/elaborator (`parse("...")`). -/
elab "parse(" s:str ")" : term => do
  withRef s <| elabX64 s.getString

/-- Read a file at elaboration time and return its contents as a string literal. -/
elab "fileAsString(" path:str ")" : term => do
  let contents ← IO.FS.readFile path.getString
  return mkStrLit contents

/-- Read an X64 assembly file, strip assembler directives, parse via `runParserCategory`,
    and elaborate into a Kraken `Program`. -/
elab "include_x64" path:str : term => do
  let content ← IO.FS.readFile path.getString
  let stripped := stripDirectives content
  withRef path <| elabX64 stripped

end Kraken.X64.Parser
