module

public import Kraken.X64.Parser.Syntax
public meta import Kraken.X64.Parser.Syntax
public import Kraken.X64.Syntax
public meta import Kraken.X64.Syntax
public meta import Lean

/-!
Delaborators for Kraken X64 assembly terms into the embedded `[x64| ... ]` syntax defined in
`Kraken.X64.Parser.Syntax`.

Closed directives, instructions, operands and registers delaborate to their concrete AT&T syntax. Open or
non-canonical subterms at any position that admits an antiquotation (`%❰t❱` for registers, `❰t❱` for
operands and directives) fall back to Lean's standard delaborator at that subexpression position.
-/

namespace Kraken.X64.Parser

open Lean Meta PrettyPrinter Delaborator SubExpr Kraken.Parser

public meta section

-- ============================================================================
-- Delaboration State & Low-Level Helpers
-- ============================================================================

structure X64DelabState where
  /-- Whether the instruction being delaborated has a memory operand (at most one is valid). -/
  hasMem : Bool := false
  /-- Whether a memory operand's base/index register encodes the instruction's address width. -/
  hasAddrReg : Bool := false

abbrev X64DelabM := StateRefT X64DelabState DelabM

/-- Run `act`, restoring the `X64DelabState` and running `fallback` if `act` fails. -/
private def tryX64Delab {α : Type} (act : X64DelabM α) (fallback : X64DelabM α) : X64DelabM α := do
  let saved ← get
  try
    act
  catch _ =>
    set saved
    fallback

/-- Construct a suffixed keyword node of category `cat` in `Kraken.X64.Parser`. -/
private def mkSuffixed (cat : Name) (stem sfx : String) : TSyntax cat :=
  Kraken.mkSuffixed `Kraken.X64.Parser cat stem sfx

/-- Wrap an `x64_const` into an `x64_imm` (`$const`). -/
private def mkImm (c : TSyntax `x64_const) : TSyntax `x64_imm :=
  ⟨.node .none ``«x64_imm$_» #[.atom .none "$", c.raw]⟩

/-- Annotate a syntax node of any category with the current `SubExpr` term info. -/
private def annotateStx {cat : Name} (stx : TSyntax cat) : DelabM (TSyntax cat) := do
  return ⟨(← annotateTermInfo ⟨stx.raw⟩).raw⟩

private def evalNat? (e : Expr) : Option Nat :=
  e.nat? <|> e.rawNatLit?

private def evalInt64? (e : Expr) : Option Int :=
  e.int?.map fun i => (Int64.ofInt i).toInt

-- NOTE: `evalWidth?` can be used in `ppWidth` as well. Factor the definition in `Elab.lean` and use it here.
private def evalWidth? (e : Expr) : Option Width :=
  match_expr e with
  | Width.W8  => some .W8
  | Width.W16 => some .W16
  | Width.W32 => some .W32
  | Width.W64 => some .W64
  | _         => none

private def evalAvxWidth? (e : Expr) : Option AvxWidth :=
  match_expr e with
  | AvxWidth.W128 => some .W128
  | AvxWidth.W256 => some .W256
  | AvxWidth.W512 => some .W512
  | _             => none

private def evalReg64? (e : Expr) : Option Reg64 :=
  match_expr e with
  | Reg64.rax => some .rax | Reg64.rbx => some .rbx | Reg64.rcx => some .rcx | Reg64.rdx => some .rdx
  | Reg64.rsi => some .rsi | Reg64.rdi => some .rdi | Reg64.rsp => some .rsp | Reg64.rbp => some .rbp
  | Reg64.r8  => some .r8  | Reg64.r9  => some .r9  | Reg64.r10 => some .r10 | Reg64.r11 => some .r11
  | Reg64.r12 => some .r12 | Reg64.r13 => some .r13 | Reg64.r14 => some .r14 | Reg64.r15 => some .r15
  | _         => none

private def evalRegMm? (e : Expr) : Option RegMm :=
  match_expr e with
  | RegMm.mm0  => some .mm0  | RegMm.mm1  => some .mm1  | RegMm.mm2  => some .mm2  | RegMm.mm3  => some .mm3
  | RegMm.mm4  => some .mm4  | RegMm.mm5  => some .mm5  | RegMm.mm6  => some .mm6  | RegMm.mm7  => some .mm7
  | RegMm.mm8  => some .mm8  | RegMm.mm9  => some .mm9  | RegMm.mm10 => some .mm10 | RegMm.mm11 => some .mm11
  | RegMm.mm12 => some .mm12 | RegMm.mm13 => some .mm13 | RegMm.mm14 => some .mm14 | RegMm.mm15 => some .mm15
  | RegMm.mm16 => some .mm16 | RegMm.mm17 => some .mm17 | RegMm.mm18 => some .mm18 | RegMm.mm19 => some .mm19
  | RegMm.mm20 => some .mm20 | RegMm.mm21 => some .mm21 | RegMm.mm22 => some .mm22 | RegMm.mm23 => some .mm23
  | RegMm.mm24 => some .mm24 | RegMm.mm25 => some .mm25 | RegMm.mm26 => some .mm26 | RegMm.mm27 => some .mm27
  | RegMm.mm28 => some .mm28 | RegMm.mm29 => some .mm29 | RegMm.mm30 => some .mm30 | RegMm.mm31 => some .mm31
  | _          => none

private def evalCondCode? (e : Expr) : Option CondCode :=
  match_expr e with
  | CondCode.o  => some .o  | CondCode.no => some .no
  | CondCode.c  => some .c  | CondCode.b  => some .b
  | CondCode.nc => some .nc | CondCode.ae => some .ae
  | CondCode.z  => some .z  | CondCode.e  => some .e
  | CondCode.nz => some .nz | CondCode.ne => some .ne
  | CondCode.be => some .be | CondCode.a  => some .a
  | CondCode.s  => some .s  | CondCode.ns => some .ns
  | CondCode.p  => some .p  | CondCode.np => some .np
  | CondCode.l  => some .l  | CondCode.ge => some .ge
  | CondCode.le => some .le | CondCode.g  => some .g
  | _           => none

-- ============================================================================
-- Identifiers & Constant Expressions
-- ============================================================================

/-- Delaborate a `String` literal into an `x64_ident` if it is a valid assembly identifier. -/
def delabIdent : DelabM (TSyntax `x64_ident) := do
  let .lit (.strVal s) ← getExpr | failure
  unless isAsmIdent s do failure
  annotateStx ⟨Syntax.node .none ``x64_ident_ #[Syntax.atom .none s]⟩

/-- Delaborate a `ConstExpr` into an `x64_const`. -/
def delabConstExpr : DelabM (TSyntax `x64_const) := do
  let stx ← match_expr ← getExpr with
  | ConstExpr.int64 iExpr =>
    let some i := evalInt64? iExpr | failure
    if i ≥ 0 then
      let n := Syntax.mkNumLit (toString i.toNat)
      `(x64_const| $n:num)
    else
      let n := Syntax.mkNumLit (toString (-i).toNat)
      `(x64_const| -$n:num)
  | ConstExpr.label _ =>
    let id ← withAppArg delabIdent
    `(x64_const| $id:x64_ident)
  | ConstExpr.add aExpr bExpr =>
    unless aExpr.isAppOfArity ``ConstExpr.label 1 do failure
    match_expr bExpr with
    | ConstExpr.int64 iExpr =>
      let id ← withNaryArg 0 (withAppArg delabIdent)
      let some i := evalInt64? iExpr | failure
      if i ≥ 0 then
        let n := Syntax.mkNumLit (toString i.toNat)
        `(x64_const| $id:x64_ident + $n:num)
      else
        let n := Syntax.mkNumLit (toString (-i).toNat)
        `(x64_const| $id:x64_ident - $n:num)
    | _ => failure
  | ConstExpr.sub aExpr bExpr =>
    unless aExpr.isAppOfArity ``ConstExpr.label 1 do failure
    match_expr bExpr with
    | ConstExpr.int64 iExpr =>
      let id ← withNaryArg 0 (withAppArg delabIdent)
      let some i := evalInt64? iExpr | failure
      if i ≥ 0 then
        let n := Syntax.mkNumLit (toString i.toNat)
        `(x64_const| $id:x64_ident - $n:num)
      else
        let n := Syntax.mkNumLit (toString (-i).toNat)
        `(x64_const| $id:x64_ident + $n:num)
    | _ => failure
  | _ => failure
  annotateStx stx

-- ============================================================================
-- Registers
-- ============================================================================

/-- The `(stem, suffix)` pair of a general-purpose register in `x64_reg_name`, inverse to `evalReg`. -/
private def regStemSuffix : {w : Width} → Reg w → String × String
  | .W8,  .ah => ("a", "h")
  | .W8,  .bh => ("b", "h")
  | .W8,  .ch => ("c", "h")
  | .W8,  .dh => ("d", "h")
  | .W64, .low .rax _ => ("r", "ax") | .W32, .low .rax _ => ("e", "ax") | .W16, .low .rax _ => ("a", "x")  | .W8, .low .rax _ => ("a", "l")
  | .W64, .low .rbx _ => ("r", "bx") | .W32, .low .rbx _ => ("e", "bx") | .W16, .low .rbx _ => ("b", "x")  | .W8, .low .rbx _ => ("b", "l")
  | .W64, .low .rcx _ => ("r", "cx") | .W32, .low .rcx _ => ("e", "cx") | .W16, .low .rcx _ => ("c", "x")  | .W8, .low .rcx _ => ("c", "l")
  | .W64, .low .rdx _ => ("r", "dx") | .W32, .low .rdx _ => ("e", "dx") | .W16, .low .rdx _ => ("d", "x")  | .W8, .low .rdx _ => ("d", "l")
  | .W64, .low .rsi _ => ("r", "si") | .W32, .low .rsi _ => ("e", "si") | .W16, .low .rsi _ => ("si", "")  | .W8, .low .rsi _ => ("si", "l")
  | .W64, .low .rdi _ => ("r", "di") | .W32, .low .rdi _ => ("e", "di") | .W16, .low .rdi _ => ("di", "")  | .W8, .low .rdi _ => ("di", "l")
  | .W64, .low .rsp _ => ("r", "sp") | .W32, .low .rsp _ => ("e", "sp") | .W16, .low .rsp _ => ("sp", "")  | .W8, .low .rsp _ => ("sp", "l")
  | .W64, .low .rbp _ => ("r", "bp") | .W32, .low .rbp _ => ("e", "bp") | .W16, .low .rbp _ => ("bp", "")  | .W8, .low .rbp _ => ("bp", "l")
  | w, .low r64 _ =>
    let stem := match r64 with
      | .r8  => "r8"  | .r9  => "r9"  | .r10 => "r10" | .r11 => "r11"
      | .r12 => "r12" | .r13 => "r13" | .r14 => "r14" | .r15 => "r15"
      | _    => unreachable!
    let sfx := match w with
      | .W64 => "" | .W32 => "d" | .W16 => "w" | .W8 => "b"
    (stem, sfx)

private def evalReg? (e : Expr) : Option ((w : Width) × Reg w) :=
  match_expr e with
  | Reg.low r64Expr wExpr => do
    let r64 ← evalReg64? r64Expr
    let w ← evalWidth? wExpr
    pure ⟨w, .low r64 w⟩
  | Reg.ah => some ⟨.W8, .ah⟩
  | Reg.bh => some ⟨.W8, .bh⟩
  | Reg.ch => some ⟨.W8, .ch⟩
  | Reg.dh => some ⟨.W8, .dh⟩
  | Reg.rax  => some ⟨.W64, .rax⟩  | Reg.rbx  => some ⟨.W64, .rbx⟩  | Reg.rcx  => some ⟨.W64, .rcx⟩  | Reg.rdx  => some ⟨.W64, .rdx⟩
  | Reg.rsi  => some ⟨.W64, .rsi⟩  | Reg.rdi  => some ⟨.W64, .rdi⟩  | Reg.rsp  => some ⟨.W64, .rsp⟩  | Reg.rbp  => some ⟨.W64, .rbp⟩
  | Reg.r8   => some ⟨.W64, .r8⟩   | Reg.r9   => some ⟨.W64, .r9⟩   | Reg.r10  => some ⟨.W64, .r10⟩  | Reg.r11  => some ⟨.W64, .r11⟩
  | Reg.r12  => some ⟨.W64, .r12⟩  | Reg.r13  => some ⟨.W64, .r13⟩  | Reg.r14  => some ⟨.W64, .r14⟩  | Reg.r15  => some ⟨.W64, .r15⟩
  | Reg.eax  => some ⟨.W32, .eax⟩  | Reg.ebx  => some ⟨.W32, .ebx⟩  | Reg.ecx  => some ⟨.W32, .ecx⟩  | Reg.edx  => some ⟨.W32, .edx⟩
  | Reg.esi  => some ⟨.W32, .esi⟩  | Reg.edi  => some ⟨.W32, .edi⟩  | Reg.esp  => some ⟨.W32, .esp⟩  | Reg.ebp  => some ⟨.W32, .ebp⟩
  | Reg.r8d  => some ⟨.W32, .r8d⟩  | Reg.r9d  => some ⟨.W32, .r9d⟩  | Reg.r10d => some ⟨.W32, .r10d⟩ | Reg.r11d => some ⟨.W32, .r11d⟩
  | Reg.r12d => some ⟨.W32, .r12d⟩ | Reg.r13d => some ⟨.W32, .r13d⟩ | Reg.r14d => some ⟨.W32, .r14d⟩ | Reg.r15d => some ⟨.W32, .r15d⟩
  | Reg.ax   => some ⟨.W16, .ax⟩   | Reg.bx   => some ⟨.W16, .bx⟩   | Reg.cx   => some ⟨.W16, .cx⟩   | Reg.dx   => some ⟨.W16, .dx⟩
  | Reg.si   => some ⟨.W16, .si⟩   | Reg.di   => some ⟨.W16, .di⟩   | Reg.sp   => some ⟨.W16, .sp⟩   | Reg.bp   => some ⟨.W16, .bp⟩
  | Reg.r8w  => some ⟨.W16, .r8w⟩  | Reg.r9w  => some ⟨.W16, .r9w⟩  | Reg.r10w => some ⟨.W16, .r10w⟩ | Reg.r11w => some ⟨.W16, .r11w⟩
  | Reg.r12w => some ⟨.W16, .r12w⟩ | Reg.r13w => some ⟨.W16, .r13w⟩ | Reg.r14w => some ⟨.W16, .r14w⟩ | Reg.r15w => some ⟨.W16, .r15w⟩
  | Reg.al   => some ⟨.W8,  .al⟩   | Reg.bl   => some ⟨.W8,  .bl⟩   | Reg.cl   => some ⟨.W8,  .cl⟩   | Reg.dl   => some ⟨.W8,  .dl⟩
  | Reg.sil  => some ⟨.W8,  .sil⟩  | Reg.dil  => some ⟨.W8,  .dil⟩  | Reg.spl  => some ⟨.W8,  .spl⟩  | Reg.bpl  => some ⟨.W8,  .bpl⟩
  | Reg.r8b  => some ⟨.W8,  .r8b⟩  | Reg.r9b  => some ⟨.W8,  .r9b⟩  | Reg.r10b => some ⟨.W8,  .r10b⟩ | Reg.r11b => some ⟨.W8,  .r11b⟩
  | Reg.r12b => some ⟨.W8,  .r12b⟩ | Reg.r13b => some ⟨.W8,  .r13b⟩ | Reg.r14b => some ⟨.W8,  .r14b⟩ | Reg.r15b => some ⟨.W8,  .r15b⟩
  | _        => none

/-- Delaborate a `Reg w` expression into an `x64_reg`, falling back to `%❰t❱` for open terms. -/
def delabReg : DelabM (TSyntax `x64_reg) := do
  if let some ⟨_, r⟩ := evalReg? (← getExpr) then
    let (stem, sfx) := regStemSuffix r
    let rn := mkSuffixed `x64_reg_name stem sfx
    annotateStx (← `(x64_reg| %$rn:x64_reg_name))
  else
    let t ← delab
    annotateStx (← `(x64_reg| %❰ $t ❱))

/-- Delaborate a `Reg64` expression inside a memory operand at address width `aw` into an `x64_reg`. -/
def delabLowReg (aw : Width) : X64DelabM (TSyntax `x64_reg) := do
  modify ({ · with hasAddrReg := true })
  if let some r64 := evalReg64? (← getExpr) then
    let (stem, sfx) := regStemSuffix (.low r64 aw)
    let rn := mkSuffixed `x64_reg_name stem sfx
    annotateStx (← `(x64_reg| %$rn:x64_reg_name))
  else
    -- An antiquotation `%❰t❱` in an address position always elaborates with 64-bit address width.
    unless aw == .W64 do failure
    let t ← delab
    annotateStx (← `(x64_reg| %❰ $t ❱))

/-- Delaborate a `RegOrRip` expression at address width `aw` into an `x64_reg_or_rip`. -/
def delabRegOrRip (aw : Width) : X64DelabM (TSyntax `x64_reg_or_rip) := do
  match_expr ← getExpr with
  | RegOrRip.rip =>
    unless aw == .W64 do failure
    annotateStx (← `(x64_reg_or_rip| %rip))
  | RegOrRip.reg _ =>
    let r ← withAppArg (delabLowReg aw)
    annotateStx (← `(x64_reg_or_rip| $r:x64_reg))
  | _ => failure

private def regMmIndex : RegMm → String
  | .mm0  => "0"  | .mm1  => "1"  | .mm2  => "2"  | .mm3  => "3"
  | .mm4  => "4"  | .mm5  => "5"  | .mm6  => "6"  | .mm7  => "7"
  | .mm8  => "8"  | .mm9  => "9"  | .mm10 => "10" | .mm11 => "11"
  | .mm12 => "12" | .mm13 => "13" | .mm14 => "14" | .mm15 => "15"
  | .mm16 => "16" | .mm17 => "17" | .mm18 => "18" | .mm19 => "19"
  | .mm20 => "20" | .mm21 => "21" | .mm22 => "22" | .mm23 => "23"
  | .mm24 => "24" | .mm25 => "25" | .mm26 => "26" | .mm27 => "27"
  | .mm28 => "28" | .mm29 => "29" | .mm30 => "30" | .mm31 => "31"

private def evalAvxReg? (e : Expr) : Option ((w : AvxWidth) × AvxReg w) :=
  match_expr e with
  | AvxReg.xmm mmExpr => do pure ⟨.W128, .xmm (← evalRegMm? mmExpr)⟩
  | AvxReg.ymm mmExpr => do pure ⟨.W256, .ymm (← evalRegMm? mmExpr)⟩
  | AvxReg.zmm mmExpr => do pure ⟨.W512, .zmm (← evalRegMm? mmExpr)⟩
  | _                 => none

/-- Delaborate an `AvxReg w` expression into an `x64_avx_reg`, falling back to `%❰t❱` for open terms. -/
def delabAvxReg : DelabM (TSyntax `x64_avx_reg) := do
  if let some ⟨_, r⟩ := evalAvxReg? (← getExpr) then
    let (stem, sfx) := match r with
      | .xmm mm => ("xmm", regMmIndex mm)
      | .ymm mm => ("ymm", regMmIndex mm)
      | .zmm mm => ("zmm", regMmIndex mm)
    let rn := mkSuffixed `x64_avx_reg_name stem sfx
    annotateStx (← `(x64_avx_reg| %$rn:x64_avx_reg_name))
  else
    let t ← delab
    annotateStx (← `(x64_avx_reg| %❰ $t ❱))

-- ============================================================================
-- Memory & General Operands
-- ============================================================================

private def delabScale? : Width → Option (TSyntax `num)
  | .W8  => none
  | .W16 => some (Syntax.mkNumLit "2")
  | .W32 => some (Syntax.mkNumLit "4")
  | .W64 => some (Syntax.mkNumLit "8")

private def isZeroDisp (e : Expr) : Bool :=
  match_expr e with
  | ConstExpr.int64 iExpr => evalInt64? iExpr == some 0
  | _ => false

/-- Delaborate an `AddrExpr` at address width `aw` into an `x64_mem`. -/
def delabMem (aw : Width) : X64DelabM (TSyntax `x64_mem) := do
  if (← get).hasMem then failure
  modify ({ · with hasMem := true })
  match_expr ← getExpr with
  | AddrExpr.mk baseOpt idxOpt dispExpr =>
    match_expr baseOpt with
    | Option.some _ baseExpr =>
      let baseStx ← withNaryArg 0 (withAppArg (delabRegOrRip aw))
      let disp? : Option (TSyntax `x64_const) ←
        if baseExpr.isConstOf ``RegOrRip.rip then
          match_expr dispExpr with
          | ConstExpr.sub dExpr afterExpr =>
            unless afterExpr.isConstOf ``ConstExpr.after_current_instruction do failure
            if dExpr.isAppOfArity ``ConstExpr.int64 1 then failure
            some <$> withNaryArg 2 (withNaryArg 0 delabConstExpr)
          | ConstExpr.int64 _ =>
            if isZeroDisp dispExpr then pure none
            else some <$> withNaryArg 2 delabConstExpr
          | _ => failure
        else if isZeroDisp dispExpr then
          pure none
        else
          some <$> withNaryArg 2 delabConstExpr
      let stx ← match_expr idxOpt with
        | Option.none _ =>
          `(x64_mem| $[$disp?:x64_const]?($baseStx:x64_reg_or_rip))
        | Option.some _ idxExpr =>
          match_expr idxExpr with
          | AddrIndex.mk _ scaleExpr =>
            let some scale := evalWidth? scaleExpr | failure
            let idxReg ← withNaryArg 1 (withAppArg (withNaryArg 0 (delabLowReg aw)))
            let sc? := delabScale? scale
            `(x64_mem| $[$disp?:x64_const]?($baseStx:x64_reg_or_rip, $idxReg:x64_reg $[, $sc?:num]?))
          | _ => failure
        | _ => failure
      annotateStx stx
    | Option.none _ =>
      unless aw == .W64 && idxOpt.isAppOfArity ``Option.none 1 do failure
      let disp ← withNaryArg 2 delabConstExpr
      annotateStx (← `(x64_mem| $disp:x64_const))
    | _ => failure
  | _ => failure

/-- Delaborate a concrete `RegOrMem w` (`.reg` or `.mem`) into an `x64_reg_or_mem`. -/
def delabRegOrMem (aw : Width) : X64DelabM (TSyntax `x64_reg_or_mem) := do
  match_expr ← getExpr with
  | RegOrMem.reg _ _ =>
    let r ← withAppArg delabReg
    annotateStx (← `(x64_reg_or_mem| $r:x64_reg))
  | RegOrMem.mem _ _ =>
    let m ← withAppArg (delabMem aw)
    annotateStx (← `(x64_reg_or_mem| $m:x64_mem))
  | _ => failure

/-- Delaborate a `RegOrMem w` into an `x64_operand`, falling back to `❰t❱` for open terms. -/
def delabRegOrMemOperand (aw : Width) : X64DelabM (TSyntax `x64_operand) :=
  tryX64Delab
    (do
      let rm ← delabRegOrMem aw
      annotateStx (← `(x64_operand| $rm:x64_reg_or_mem)))
    (do
      let t ← delab
      annotateStx (← `(x64_operand| ❰ $t ❱)))

/-- Delaborate an `Operand w` into an `x64_operand`, falling back to `❰t❱` for open terms. -/
def delabOperand (aw : Width) : X64DelabM (TSyntax `x64_operand) :=
  tryX64Delab
    (do
      match_expr ← getExpr with
      | Operand.regOrMem _ _ =>
        let rm ← withAppArg (delabRegOrMem aw)
        annotateStx (← `(x64_operand| $rm:x64_reg_or_mem))
      | Operand.imm _ _ =>
        let c ← withAppArg delabConstExpr
        let imm := mkImm c
        annotateStx (← `(x64_operand| $imm:x64_imm))
      | _ => failure)
    (do
      let t ← delab
      annotateStx (← `(x64_operand| ❰ $t ❱)))

/-- Delaborate an `AvxRegOrMem w` into an `x64_avx_operand`, falling back to `❰t❱` for open terms. -/
def delabAvxRegOrMem (aw : Width) : X64DelabM (TSyntax `x64_avx_operand) :=
  tryX64Delab
    (do
      match_expr ← getExpr with
      | AvxRegOrMem.avx _ _ =>
        let r ← withAppArg delabAvxReg
        annotateStx (← `(x64_avx_operand| $r:x64_avx_reg))
      | AvxRegOrMem.mem _ _ =>
        let m ← withAppArg (delabMem aw)
        annotateStx (← `(x64_avx_operand| $m:x64_mem))
      | _ => failure)
    (do
      let t ← delab
      annotateStx (← `(x64_avx_operand| ❰ $t ❱)))

/-- Delaborate a `ShiftCountExpr` into an `x64_shift_count`. -/
def delabShiftCount : DelabM (TSyntax `x64_shift_count) := do
  match_expr ← getExpr with
  | ShiftCountExpr.cl =>
    annotateStx (← `(x64_shift_count| %cl))
  | ShiftCountExpr.imm8 _ =>
    let c ← withAppArg delabConstExpr
    let imm := mkImm c
    annotateStx (← `(x64_shift_count| $imm:x64_imm))
  | _ => failure

/-- Delaborate a `RelRegOrMem` branch target into an `x64_operand`, falling back to `❰t❱` for open terms. -/
def delabRelTarget (aw : Width) : X64DelabM (TSyntax `x64_operand) :=
  tryX64Delab
    (do
      match_expr ← getExpr with
      | RelRegOrMem.rel cExpr =>
        unless aw == .W64 do failure
        match_expr cExpr with
        | ConstExpr.sub lblExpr afterExpr =>
          unless afterExpr.isConstOf ``ConstExpr.after_current_instruction do failure
          unless lblExpr.isAppOfArity ``ConstExpr.label 1 do failure
          let id ← withAppArg (withNaryArg 0 (withAppArg delabIdent))
          annotateStx (← `(x64_operand| $id:x64_ident))
        | _ => failure
      | RelRegOrMem.reg _ =>
        unless aw == .W64 do failure
        let r ← withAppArg delabReg
        annotateStx (← `(x64_operand| $r:x64_reg))
      | RelRegOrMem.mem mExpr =>
        match_expr mExpr with
        | AddrExpr.mk baseOpt _ _ =>
          unless baseOpt.isAppOfArity ``Option.some 2 do failure
          let m ← withAppArg (delabMem aw)
          annotateStx (← `(x64_operand| $m:x64_mem))
        | _ => failure
      | _ => failure)
    (do
      unless aw == .W64 do failure
      let t ← delab
      annotateStx (← `(x64_operand| ❰ $t ❱)))

-- ============================================================================
-- Mnemonic Suffixes & Width Inference Checks
-- ============================================================================

private def widthSuffix : Option Width → String
  | none      => ""
  | some .W8  => "b"
  | some .W16 => "w"
  | some .W32 => "l"
  | some .W64 => "q"

private def condCodeSuffix? : CondCode → Option String
  | .z  => some "z"
  | .nz => some "nz"
  | .c  => some "b"
  | .nc => some "ae"
  | .a  => some "a"
  | .be => some "be"
  | .l  => some "l"
  | .le => some "le"
  | _   => none

private def extMovSuffix? (isSigned : Bool) (wSrc wDst : Width) : Option String :=
  match wSrc, wDst with
  | .W8,  .W16 => some "bw"
  | .W8,  .W32 => some "bl"
  | .W8,  .W64 => some "bq"
  | .W16, .W32 => some "wl"
  | .W16, .W64 => some "wq"
  | .W32, .W64 => if isSigned then some "lq" else none
  | _,    _    => none

/-- Whether an `x64_operand` syntax node determines the instruction's operation width during elaboration
    (registers and `❰t❱` antiquotations do; concrete memory and immediate operands do not). -/
private def operandDeterminesWidth (stx : TSyntax `x64_operand) : Bool :=
  match stx with
  | `(x64_operand| $_:x64_reg) => true
  | `(x64_operand| ❰ $_ ❱)     => true
  | _                          => false

/-- Check that an instruction with a symbolic operation width `w? == none` has at least one operand that
    determines the width. -/
private def ensureWidthDetermined (w? : Option Width) (ops : Array (TSyntax `x64_operand)) : X64DelabM Unit := do
  if w?.isNone then
    unless ops.any operandDeterminesWidth do failure

-- ============================================================================
-- Instruction Delaboration
-- ============================================================================

/-- Delaborate a binary `Operation` constructor (`add`, `mov`, `xor`, ...) at `(aw, w?)`. -/
private def delabBinOp (stem : String) (aw : Width) (w? : Option Width) : X64DelabM (TSyntax `x64_instr) := do
  let op := mkSuffixed `x64_bin_op stem (widthSuffix w?)
  let dst ← withNaryArg 1 (delabRegOrMemOperand aw)
  let src ← withNaryArg 2 (delabOperand aw)
  ensureWidthDetermined w? #[src, dst]
  `(x64_instr| $op:x64_bin_op $src:x64_operand, $dst:x64_operand)

/-- Delaborate a unary `Operation` constructor (`mul`, `neg`, `dec`, `inc`, `not`) at `(aw, w?)`. -/
private def delabUnaryOp (stem : String) (aw : Width) (w? : Option Width) : X64DelabM (TSyntax `x64_instr) := do
  let op := mkSuffixed `x64_unary_op stem (widthSuffix w?)
  let dst ← withNaryArg 1 (delabRegOrMemOperand aw)
  ensureWidthDetermined w? #[dst]
  `(x64_instr| $op:x64_unary_op $dst:x64_operand)

/-- Delaborate a shift/rotate `Operation` constructor (`shl`, `shr`, `sar`, `rol`, `ror`, `rcl`, `rcr`). -/
private def delabShiftOp (stem : String) (aw : Width) (w? : Option Width) : X64DelabM (TSyntax `x64_instr) := do
  let op := mkSuffixed `x64_shift_op stem (widthSuffix w?)
  let dst ← withNaryArg 1 (delabRegOrMemOperand aw)
  let cnt ← withNaryArg 2 delabShiftCount
  ensureWidthDetermined w? #[dst]
  `(x64_instr| $op:x64_shift_op $cnt:x64_shift_count, $dst:x64_operand)

/-- Delaborate a double-precision shift `Operation` constructor (`shld`, `shrd`). -/
private def delabShdOp (stem : String) (aw : Width) : X64DelabM (TSyntax `x64_instr) := do
  let op := mkSuffixed `x64_shd_op stem ""
  let dst ← withNaryArg 1 (delabRegOrMemOperand aw)
  let src ← withNaryArg 2 delabReg
  let cnt ← withNaryArg 3 delabShiftCount
  `(x64_instr| $op:x64_shd_op $cnt:x64_shift_count, $src:x64_reg, $dst:x64_operand)

/-- Delaborate an extending move (`movsx` / `movzx`). -/
private def delabExtMov (isSigned : Bool) (aw : Width) (wDst? : Option Width) (wSrcExpr dstExpr srcExpr : Expr) :
    X64DelabM (TSyntax `x64_instr) := do
  unless dstExpr.isAppOfArity ``RegOrMem.reg 2 do failure
  let dst ← withNaryArg 2 (withAppArg delabReg)
  if srcExpr.isAppOfArity ``RegOrMem.reg 2 then
    if let (some wSrc, some wDst) := (evalWidth? wSrcExpr, wDst?) then
      unless wSrc.bits < wDst.bits do failure
    let src ← withNaryArg 3 (withAppArg delabReg)
    if isSigned then
      `(x64_instr| movsx $src:x64_reg, $dst:x64_reg)
    else
      `(x64_instr| movzx $src:x64_reg, $dst:x64_reg)
  else
    let some wSrc := evalWidth? wSrcExpr | failure
    let some wDst := wDst? | failure
    let some sfx := extMovSuffix? isSigned wSrc wDst | failure
    let op := mkSuffixed `x64_ext_mov_op (if isSigned then "movs" else "movz") sfx
    let src ← withNaryArg 3 (delabRegOrMemOperand aw)
    `(x64_instr| $op:x64_ext_mov_op $src:x64_operand, $dst:x64_reg)

/-- Delaborate an `Operation w` inside `Instr.regular aw w op` into an `x64_instr`. -/
private def delabOperation (aw : Width) (w? : Option Width) : X64DelabM (TSyntax `x64_instr) := do
  let sfx := widthSuffix w?
  match_expr ← getExpr with
  -- Binary ALU / move
  | Operation.add  _ _ _ => delabBinOp "add"  aw w?
  | Operation.adc  _ _ _ => delabBinOp "adc"  aw w?
  | Operation.sub  _ _ _ => delabBinOp "sub"  aw w?
  | Operation.sbb  _ _ _ => delabBinOp "sbb"  aw w?
  | Operation.mov  _ _ _ => delabBinOp "mov"  aw w?
  | Operation.xor  _ _ _ => delabBinOp "xor"  aw w?
  | Operation.and  _ _ _ => delabBinOp "and"  aw w?
  | Operation.or   _ _ _ => delabBinOp "or"   aw w?
  | Operation.cmp  _ _ _ => delabBinOp "cmp"  aw w?
  | Operation.test _ _ _ => delabBinOp "test" aw w?
  -- Carry-chain
  | Operation.adcx _ _ _ =>
    let op := mkSuffixed `x64_rm_reg_op "adcx" ""
    let dst ← withNaryArg 1 delabReg
    let src ← withNaryArg 2 (delabRegOrMemOperand aw)
    `(x64_instr| $op:x64_rm_reg_op $src:x64_operand, $dst:x64_reg)
  | Operation.adox _ _ _ =>
    let op := mkSuffixed `x64_rm_reg_op "adox" ""
    let dst ← withNaryArg 1 delabReg
    let src ← withNaryArg 2 (delabRegOrMemOperand aw)
    `(x64_instr| $op:x64_rm_reg_op $src:x64_operand, $dst:x64_reg)
  -- Conditional move
  | Operation.cmovcc _ ccExpr _ _ =>
    let some cc := evalCondCode? ccExpr | failure
    let some ccSfx := condCodeSuffix? cc | failure
    let op := mkSuffixed `x64_cmov_op "cmov" ccSfx
    let dst ← withNaryArg 2 delabReg
    let src ← withNaryArg 3 (delabRegOrMemOperand aw)
    `(x64_instr| $op:x64_cmov_op $src:x64_operand, $dst:x64_reg)
  -- Unary arithmetic / bitwise
  | Operation.mul _ _ => delabUnaryOp "mul" aw w?
  | Operation.neg _ _ => delabUnaryOp "neg" aw w?
  | Operation.dec _ _ => delabUnaryOp "dec" aw w?
  | Operation.inc _ _ => delabUnaryOp "inc" aw w?
  | Operation.not _ _ => delabUnaryOp "not" aw w?
  -- Conditional byte-set
  | Operation.setcc _ ccExpr _ =>
    unless w? == some .W8 do failure
    let some cc := evalCondCode? ccExpr | failure
    let some ccSfx := condCodeSuffix? cc | failure
    let op := mkSuffixed `x64_set_op "set" ccSfx
    let dst ← withNaryArg 2 (delabRegOrMemOperand aw)
    `(x64_instr| $op:x64_set_op $dst:x64_operand)
  -- Signed & unsigned multiply variants
  | Operation.imul1 _ _ =>
    let op := mkSuffixed `x64_imul_op "imul" sfx
    let src ← withNaryArg 1 (delabRegOrMemOperand aw)
    ensureWidthDetermined w? #[src]
    `(x64_instr| $op:x64_imul_op $src:x64_operand)
  | Operation.imul _ dstOpt _ _ =>
    let op := mkSuffixed `x64_imul_op "imul" sfx
    match_expr dstOpt with
    | Option.none _ =>
      let dst ← withNaryArg 2 (delabRegOrMemOperand aw)
      let src ← withNaryArg 3 (delabOperand aw)
      ensureWidthDetermined w? #[src, dst]
      `(x64_instr| $op:x64_imul_op $src:x64_operand, $dst:x64_operand)
    | Option.some _ dstExpr =>
      unless dstExpr.isAppOfArity ``RegOrMem.reg 2 do failure
      let dst ← withNaryArg 1 (withAppArg (withAppArg delabReg))
      let src2 ← withNaryArg 2 (delabRegOrMemOperand aw)
      let src1 ← withNaryArg 3 (delabOperand aw)
      `(x64_instr| $op:x64_imul_op $src1:x64_operand, $src2:x64_operand, $dst:x64_reg)
    | _ => failure
  | Operation.mulx _ _ _ _ =>
    let op := mkSuffixed `x64_mulx_op "mulx" ""
    let hi ← withNaryArg 1 delabReg
    let lo ← withNaryArg 2 delabReg
    let src ← withNaryArg 3 (delabRegOrMemOperand aw)
    `(x64_instr| $op:x64_mulx_op $src:x64_operand, $lo:x64_reg, $hi:x64_reg)
  -- Extending moves
  | Operation.movsx _ wSrcExpr dstExpr srcExpr =>
    delabExtMov true aw w? wSrcExpr dstExpr srcExpr
  | Operation.movzx _ wSrcExpr dstExpr srcExpr =>
    delabExtMov false aw w? wSrcExpr dstExpr srcExpr
  -- Load effective address
  | Operation.lea _ _ _ =>
    let op := mkSuffixed `x64_lea_op "lea" ""
    let dst ← withNaryArg 1 delabReg
    let src ← withNaryArg 2 (delabMem aw)
    `(x64_instr| $op:x64_lea_op $src:x64_mem, $dst:x64_reg)
  -- Shifts, rotates & byte swap
  | Operation.shl  _ _ _ => delabShiftOp "shl" aw w?
  | Operation.shr  _ _ _ => delabShiftOp "shr" aw w?
  | Operation.sar  _ _ _ => delabShiftOp "sar" aw w?
  | Operation.rol  _ _ _ => delabShiftOp "rol" aw w?
  | Operation.ror  _ _ _ => delabShiftOp "ror" aw w?
  | Operation.rcl  _ _ _ => delabShiftOp "rcl" aw w?
  | Operation.rcr  _ _ _ => delabShiftOp "rcr" aw w?
  | Operation.shld _ _ _ _ => delabShdOp "shld" aw
  | Operation.shrd _ _ _ _ => delabShdOp "shrd" aw
  | Operation.bswap _ _ =>
    let op := mkSuffixed `x64_bswap_op "bswap" ""
    let dst ← withNaryArg 1 delabReg
    `(x64_instr| $op:x64_bswap_op $dst:x64_reg)
  -- Stack push / pop
  | Operation.push _ _ =>
    let op := mkSuffixed `x64_push_op "push" sfx
    let src ← withNaryArg 1 (delabOperand aw)
    ensureWidthDetermined w? #[src]
    `(x64_instr| $op:x64_push_op $src:x64_operand)
  | Operation.pop _ _ =>
    let op := mkSuffixed `x64_pop_op "pop" sfx
    let dst ← withNaryArg 1 (delabRegOrMemOperand aw)
    ensureWidthDetermined w? #[dst]
    `(x64_instr| $op:x64_pop_op $dst:x64_operand)
  -- Control flow & nop/align
  | Operation.ret _ =>
    unless w? == some .W64 do failure
    `(x64_instr| ret)
  | Operation.call _ _ =>
    unless w? == some .W64 do failure
    let target ← withNaryArg 1 (delabRelTarget aw)
    `(x64_instr| call $target:x64_operand)
  | Operation.jmp _ _ =>
    unless w? == some .W64 do failure
    let target ← withNaryArg 1 (delabRelTarget aw)
    `(x64_instr| jmp $target:x64_operand)
  | Operation.jcc _ ccExpr _ =>
    unless w? == some .W64 do failure
    let some cc := evalCondCode? ccExpr | failure
    let some ccSfx := condCodeSuffix? cc | failure
    let op := mkSuffixed `x64_jcc_op "j" ccSfx
    let lbl ← withNaryArg 2 delabIdent
    `(x64_instr| $op:x64_jcc_op $lbl:x64_ident)
  | Operation.nop _ lenExpr =>
    unless w? == some .W64 do failure
    let some len := evalNat? lenExpr | failure
    if len == 1 then
      `(x64_instr| nop)
    else
      let sz := Syntax.mkNumLit (toString len)
      `(x64_instr| nop $sz:num)
  | Operation.nopalign _ alignExpr padOpt =>
    unless w? == some .W64 do failure
    let some align := evalNat? alignExpr | failure
    let alignStx := Syntax.mkNumLit (toString align)
    match_expr padOpt with
    | Option.none _ =>
      `(x64_instr| .align $alignStx:num)
    | Option.some _ padExpr =>
      let some pad := evalNat? padExpr | failure
      let padStx := Syntax.mkNumLit (toString pad)
      `(x64_instr| .align $alignStx:num, $padStx:num)
    | _ => failure
  | _ => failure

/-- Delaborate an `AvxOperation w` inside `Instr.avx aw w op` into an `x64_instr`. -/
private def delabAvxOperation (aw : Width) (w? : Option AvxWidth) : X64DelabM (TSyntax `x64_instr) := do
  let stem ← match_expr ← getExpr with
    | AvxOperation.movups  _ _ _ => pure "movu"
    | AvxOperation.vmovups _ _ _ => pure "vmovu"
    | AvxOperation.movaps  _ _ _ => pure "mova"
    | AvxOperation.addps   _ _ _ => pure "add"
    | AvxOperation.subps   _ _ _ => pure "sub"
    | _                          => failure
  let op := mkSuffixed `x64_avx_op stem "ps"
  let dst ← withNaryArg 1 (delabAvxRegOrMem aw)
  let src ← withNaryArg 2 (delabAvxRegOrMem aw)
  let determinesWidth (stx : TSyntax `x64_avx_operand) : Bool :=
    match stx with
    | `(x64_avx_operand| $_:x64_avx_reg) => true
    | `(x64_avx_operand| ❰ $_ ❱)         => true
    | _                                  => false
  unless determinesWidth src || determinesWidth dst do failure
  let _ := w?
  `(x64_instr| $op:x64_avx_op $src:x64_avx_operand, $dst:x64_avx_operand)

/-- Delaborate an `Instr` into an `x64_instr`. Fails for open or non-canonical instructions so the enclosing
    `delabDirective` falls back to `❰t❱`. -/
def delabInstr : DelabM (TSyntax `x64_instr) := do
  let act : X64DelabM (TSyntax `x64_instr) := do
    match_expr ← getExpr with
    | Instr.regular awExpr wExpr _ =>
      let some aw := evalWidth? awExpr | failure
      let w? := evalWidth? wExpr
      withNaryArg 2 (delabOperation aw w?)
    | Instr.avx awExpr wExpr _ =>
      let some aw := evalWidth? awExpr | failure
      let w? := evalAvxWidth? wExpr
      withNaryArg 2 (delabAvxOperation aw w?)
    | _ => failure
  let (stx, st) ← act.run {}
  unless st.hasAddrReg || evalWidth? ((← getExpr).getArg! 0) == some Width.W64 do failure
  annotateStx stx

-- ============================================================================
-- Directive & Program Delaboration
-- ============================================================================

/-- Delaborate a `Directive` into an `x64_directive`, falling back to `❰t❱` for open or non-canonical terms. -/
def delabDirective : DelabM (TSyntax `x64_directive) := do
  match_expr ← getExpr with
  | Directive.label _ _ =>
    try
      let lbl ← withAppArg delabIdent
      annotateStx (← `(x64_directive| $lbl:x64_ident :))
    catch _ =>
      let t ← delab
      annotateStx (← `(x64_directive| ❰ $t ❱))
  | Directive.instr _ _ =>
    try
      let ins ← withAppArg delabInstr
      annotateStx (← `(x64_directive| $ins:x64_instr))
    catch _ =>
      let t ← delab
      annotateStx (← `(x64_directive| ❰ $t ❱))
  | _ =>
    let t ← delab
    annotateStx (← `(x64_directive| ❰ $t ❱))

/-- Delaborate the spine of a `List Directive`, returning its delaborated directives and any non-`[]` tail. -/
private partial def delabDirectiveListSpine :
    DelabM (Array (TSyntax `x64_directive) × Option Term) := do
  match_expr ← getExpr with
  | List.cons _ _ _ =>
    let hd ← withAppFn (withAppArg delabDirective)
    let (tl, tail?) ← withAppArg delabDirectiveListSpine
    return (#[hd] ++ tl, tail?)
  | List.nil _ =>
    return (#[], none)
  | _ =>
    return (#[], some (← delab))

/-- Delaborate a non-empty `List Directive` (`Program`) into an `[x64| ... ]` block (or `[x64| ... ] ++ tail`
    when the list ends in an open tail). -/
@[app_delab List.cons]
def delabProgram : Delab := do
  if ← getPPOption getPPExplicit then failure
  match ←getExpr with
  | mkApp3 (.const ``List.cons _) (.const ``_root_.Directive _) _ _
  | mkApp3 (.const ``List.cons _) (mkApp (.const ``Kraken.Directive _) _) _ _ =>
    let (dirs, tail?) ← delabDirectiveListSpine
    let prog ← `(x64_prog| $dirs:x64_directive*)
    let listing ← annotateTermInfo (← `([x64| $prog:x64_prog]))
    match tail? with
    | none => return listing
    | some tail => `($listing ++ $tail)
  | _ => failure

end

end Kraken.X64.Parser
