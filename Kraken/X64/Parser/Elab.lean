module

public import Kraken.X64.Parser.Basic
public meta import Kraken.X64.Parser.Basic
public import Kraken.X64.Parser.Syntax
public meta import Kraken.X64.Parser.Syntax
public meta import Lean

/-!
Operands may contain antiquotations (`%❰t❱`), whose value is only known as a term, so everything from
operands upwards is elaborated to `Expr`s. The widths of an instruction are kept in the `X64ElabM` state
rather than threaded through the operand elaborators: a register reports its width, which must agree with
what the mnemonic suffix and the other operands determined; immediates and memory operands are valid at any
width and simply use the instruction's.
-/

namespace Kraken.X64.Parser

open Lean Meta Elab Kraken.Parser
open Term hiding mkConst  -- `mkConst` is the pure `Lean.mkConst`, not the environment lookup `Term.mkConst`

public meta section

-- ============================================================================
-- Elaboration Monad: Operation & Address Widths
-- ============================================================================

structure X64ElabM.State where
  /-- Operand width of the scope being elaborated. Usually, instructions only have one operand width,
      but there are exceptions such as `.movsx` or `.movzx`. This `Expr` has one of three shapes:
       • A metavariable, if it has not been inferred yet
       • A value of type `Width`, if parsing a regular instruction
       • A value of type `AvxWidth`, if parsing an AVX instruction.
      -/
  operandWidth : Expr
  /-- Whether the instruction has a memory operand, and if so, its address width -/
  addressWidth? : Option Expr := none

abbrev X64ElabM := StateRefT X64ElabM.State TermElabM

/-- Run the elaboration of an instruction, whose operation width is yet to be determined. -/
nonrec def X64ElabM.run' {α : Type} (x : X64ElabM α) : TermElabM α := do
  x.run' { operandWidth := ← mkFreshExprMVar none }

/-- Print a `Width` or `AvxWidth` expression as values if possible, using its `ToString` instance -/
def ppWidth (wExpr : Expr) : MetaM MessageData := do
  let wExpr ← instantiateMVars wExpr  -- an assigned metavariable is not syntactically `Width.W64`
  if let some wValue := [Width.W8, .W16, .W32, .W64].find? (toExpr · == wExpr) then return m!"{wValue}"
  if let some wValue := [AvxWidth.W128, .W256, .W512].find? (toExpr · == wExpr) then return m!"{wValue}"
  return m!"{wExpr}"

/-- The operation width of the current instruction. May be of type `Width` or `Avx` depending on the instruction -/
def getOperandWidth : X64ElabM Expr :=
  return (← get).operandWidth

/-- Record that the current operand has width `w`, which must agree with the width already determined by
    the already processed part of the instruction. -/
def setOperandWidth (w : Expr) : X64ElabM Unit := do
  let w' ← getOperandWidth
  unless ← isDefEq w' w do throwError "type error: {← ppWidth w'} != {← ppWidth w}"

/-- Apply `f`, whose first argument is a width (a constructor `c {w} ...` or a type `T w`), to the
    instruction's operation width and to `args`. -/
def mkAppWidth (f : Expr) (args : Array Expr := #[]) : X64ElabM Expr :=
  return mkAppN (f.app <| ← getOperandWidth) args

/-- Run `body` with its own operation width, initially `w?`, and return the width it determined. -/
private def withOperandWidth {α : Type} (w? : Option Width) (body : X64ElabM α) : X64ElabM (α × Expr) := do
  let saved ← getOperandWidth
  let w ← match w? with
    | some w => pure (toExpr w)
    | none => mkFreshExprMVar (toTypeExpr Width)
  modify ({ · with operandWidth := w })
  try
    let res ← body
    pure (res, ← instantiateMVars w)
  finally
    modify ({ · with operandWidth := saved })

/-- Run `body` with its own operation width, initially `w?`, and return the width it determined. -/
private def withOperandWidth' {α : Type} (w? : Option Width) (body : X64ElabM α) : X64ElabM (α × Expr) := do
  let w ← (toExpr <$> w?).getDM (mkFreshExprMVar (toTypeExpr Width))
  let (res, {operandWidth, ..}) ← body.run {operandWidth := w}
  pure (res, operandWidth)

/-- Elaborate a memory operand: the widths its registers report make up the address width of the
    instruction, not its operation width. x86 instructions take at most one memory operand. -/
def computingAddrWidth {α : Type} (body : X64ElabM α) : X64ElabM α := do
  let (res, w) ← withOperandWidth none body
  if (← get).addressWidth?.isSome then throwError "can't have two memory operands"
  modify ({ · with addressWidth? := some w })
  pure res

/-- Elaborate the source operand of an unsuffixed widening move (`movsx`/`movzx`) in its own operation
    width, which must be narrower than the instruction's; checked once both are known. Returns the
    source width. -/
def withOperandWidthUnderCurrent {α : Type} (body : X64ElabM α) : X64ElabM (α × Expr) := do
  let (res, wSrc) ← withOperandWidth none body
  checkUnder wSrc
  pure (res, wSrc)
where
  checkUnder (wSrc) : X64ElabM Unit := do
    let wDst ← instantiateMVars (← getOperandWidth)
    let value? (w : Expr) := [Width.W8, .W16, .W32, .W64].find? (toExpr · == w)
    if let (some s, some d) := (value? wSrc, value? wDst) then
      unless s.bits < d.bits do throwError "source width {s} must be narrower than destination width {d}"

/-- Build `Instr.regular` from the instruction's widths and its operation `op`. The operation width must
    have been determined, unless `ifUndetermined` provides it (`push`/`pop` default to 64 bits). -/
def mkRegularInstr (op : Expr) (ifUndetermined : Option Width := none) : X64ElabM Expr := do
  let w ← instantiateMVars (← getOperandWidth)
  if w.isMVar then
    let d ← ifUndetermined.getDM <| throwError "could not infer operand width"
    w.mvarId!.assign (toExpr d)
  let aw := (← get).addressWidth?.getD (toExpr Width.W64)
  instantiateMVars (mkApp3 (mkConst ``Instr.regular) aw w op)

/-- Build `Instr.avx` from the instruction's widths and its AVX operation `op`. -/
def mkAvxInstr (op : Expr) : X64ElabM Expr := do
  let w ← instantiateMVars (← getOperandWidth)
  if w.isMVar then throwError "could not infer operand width"
  let aw := (← get).addressWidth?.getD (toExpr Width.W64)
  instantiateMVars (mkApp3 (mkConst ``Instr.avx) aw w op)

/-- Elaborate the term `t` of an antiquotation at the type `ty` expected by its position. Elaboration is
    forced to finish here (`withSynthesize`) because the instruction inspects the result right away: the
    unification of `ty` against `t`'s type is what determines the operation width, and `mkRegularInstr`
    rejects a width that is still a metavariable. A postponed `t` would leave a placeholder of type `ty`
    behind, with the width undetermined. A type mismatch aborts the instruction instead of being recovered
    as `sorry`. -/
def elabAntiquot (t : Term) (ty : Expr) : TermElabM Expr :=
  withoutErrToSorry <| withSynthesize <| elabTermEnsuringType t ty

-- ============================================================================
-- Constant Expression Evaluation
-- ============================================================================

/-- Evaluate an `x64_const` syntax node into a `ConstExpr`. -/
def evalConstExpr (stx : TSyntax `x64_const) : TermElabM ConstExpr := withRef stx do
  match stx with
  | `(x64_const| +$n:num)
  | `(x64_const| $n:num) =>
    let i ← Int64.ofNatNoOverflow n.getNat
    pure (.int64 i)
  | `(x64_const| -$n:num) =>
    let i ← Int64.ofIntNoOverflow (-(Int.ofNat n.getNat))
    pure (.int64 i)
  | `(x64_const| $id:x64_ident + $n:num) =>
    let s ← getAsmIdent id
    let i ← withRef n <| Int64.ofNatNoOverflow n.getNat
    pure (.add (.label s) (.int64 i))
  | `(x64_const| $id:x64_ident - $n:num) =>
    let s ← getAsmIdent id
    let i ← withRef n <| Int64.ofNatNoOverflow n.getNat
    pure (.sub (.label s) (.int64 i))
  | `(x64_const| $id:x64_ident) =>
    let s ← getAsmIdent id
    pure (.label s)
  | _ => throwError "invalid constant expression"

/-- The constant of an `x64_imm` (`$const`). -/
def getImmConst (stx : TSyntax `x64_imm) : TermElabM (TSyntax `x64_const) := withRef stx do
  match stx with
  | ⟨.node _ _ #[.atom _ "$", c]⟩ => pure ⟨c⟩
  | _ => throwError "invalid immediate operand"

-- ============================================================================
-- Register Evaluation & Elaboration
-- ============================================================================

/-- Evaluate an `x64_reg` syntax node into a general-purpose register and its width. -/
def evalReg (stx : TSyntax `x64_reg) : TermElabM ((w : Width) × Reg w) := withRef stx do
  let `(x64_reg| %$r:x64_reg_name) := stx
    | throwError "expected general-purpose register"
  let (stem, sfx) ← splitSuffixed r
  let legacy64 : String → Option Reg64
    | "ax" | "a" => some .rax | "bx" | "b" => some .rbx
    | "cx" | "c" => some .rcx | "dx" | "d" => some .rdx
    | "si"       => some .rsi | "di"       => some .rdi
    | "sp"       => some .rsp | "bp"       => some .rbp
    | _          => none
  let ext64 : String → Option Reg64
    | "r8"  => some .r8  | "r9"  => some .r9  | "r10" => some .r10 | "r11" => some .r11
    | "r12" => some .r12 | "r13" => some .r13 | "r14" => some .r14 | "r15" => some .r15
    | _     => none
  match stem, sfx with
  -- 64-bit legacy registers (`%rax`..`%rbp`)
  | "r", s =>
    let some reg := legacy64 s | throwError "invalid 64-bit register"
    pure ⟨.W64, .low reg .W64⟩
  -- 32-bit legacy registers (`%eax`..`%ebp`)
  | "e", s =>
    let some reg := legacy64 s | throwError "invalid 32-bit register"
    pure ⟨.W32, .low reg .W32⟩
  -- 8-bit high byte registers (`%ah`, `%bh`, `%ch`, `%dh`)
  | "a", "h" => pure ⟨.W8, .ah⟩
  | "b", "h" => pure ⟨.W8, .bh⟩
  | "c", "h" => pure ⟨.W8, .ch⟩
  | "d", "h" => pure ⟨.W8, .dh⟩
  -- 16-bit accumulator/base/counter/data registers (`%ax`, `%bx`, `%cx`, `%dx`)
  | s, "x" =>
    let some reg := legacy64 s | throwError "invalid 16-bit register"
    pure ⟨.W16, .low reg .W16⟩
  -- 8-bit low legacy registers (`%al`..`%dl`, `%sil`..`%bpl`)
  | s, "l" =>
    let some reg := legacy64 s | throwError "invalid 8-bit register"
    pure ⟨.W8, .low reg .W8⟩
  -- Unsuffixed registers: 64-bit extended (`%r8`..`%r15`) or 16-bit index/pointer (`%si`..`%bp`)
  | s, "" =>
    if let some reg := ext64 s then pure ⟨.W64, .low reg .W64⟩
    else if let some reg := legacy64 s then pure ⟨.W16, .low reg .W16⟩
    else throwError "invalid register"
  -- 32-bit extended registers (`%r8d`..`%r15d`)
  | s, "d" =>
    let some reg := ext64 s | throwError "invalid 32-bit extended register"
    pure ⟨.W32, .low reg .W32⟩
  -- 16-bit extended registers (`%r8w`..`%r15w`)
  | s, "w" =>
    let some reg := ext64 s | throwError "invalid 16-bit extended register"
    pure ⟨.W16, .low reg .W16⟩
  -- 8-bit extended registers (`%r8b`..`%r15b`)
  | s, "b" =>
    let some reg := ext64 s | throwError "invalid 8-bit extended register"
    pure ⟨.W8, .low reg .W8⟩
  | _, _ => throwError "expected general-purpose register"

/-- Elaborate an `x64_reg` into an `Expr` of type `Reg w`, where `w` is the operation width of the
    instruction: a concrete register determines it, an antiquotation `%❰t❱` is elaborated at it. -/
def elabReg (stx : TSyntax `x64_reg) : X64ElabM Expr := withRef stx do
  match stx with
  | `(x64_reg| %❰ $t ❱) =>
    elabAntiquot t (←mkAppWidth (mkConst ``Reg))
  | _ =>
    let ⟨w, reg⟩ ← evalReg stx
    setOperandWidth (toExpr w)
    pure (toExpr reg)

/-- Evaluate an `x64_avx_reg` syntax node into an AVX vector register and its width. -/
def evalAvxReg (stx : TSyntax `x64_avx_reg) : TermElabM ((w : AvxWidth) × AvxReg w) := withRef stx do
  let `(x64_avx_reg| %$r:x64_avx_reg_name) := stx
    | throwError "expected AVX register"
  let (stem, sfx) ← splitSuffixed r
  let mm ← match sfx with
    | "0"  => pure RegMm.mm0  | "1"  => pure RegMm.mm1  | "2"  => pure RegMm.mm2  | "3"  => pure RegMm.mm3
    | "4"  => pure RegMm.mm4  | "5"  => pure RegMm.mm5  | "6"  => pure RegMm.mm6  | "7"  => pure RegMm.mm7
    | "8"  => pure RegMm.mm8  | "9"  => pure RegMm.mm9  | "10" => pure RegMm.mm10 | "11" => pure RegMm.mm11
    | "12" => pure RegMm.mm12 | "13" => pure RegMm.mm13 | "14" => pure RegMm.mm14 | "15" => pure RegMm.mm15
    | "16" => pure RegMm.mm16 | "17" => pure RegMm.mm17 | "18" => pure RegMm.mm18 | "19" => pure RegMm.mm19
    | "20" => pure RegMm.mm20 | "21" => pure RegMm.mm21 | "22" => pure RegMm.mm22 | "23" => pure RegMm.mm23
    | "24" => pure RegMm.mm24 | "25" => pure RegMm.mm25 | "26" => pure RegMm.mm26 | "27" => pure RegMm.mm27
    | "28" => pure RegMm.mm28 | "29" => pure RegMm.mm29 | "30" => pure RegMm.mm30 | "31" => pure RegMm.mm31
    | _    => throwError "invalid AVX register index '{sfx}'"
  match stem with
  | "xmm" => pure ⟨.W128, .xmm mm⟩
  | "ymm" => pure ⟨.W256, .ymm mm⟩
  | "zmm" => pure ⟨.W512, .zmm mm⟩
  | _     => throwError "invalid AVX register prefix '{stem}'"

/-- Elaborate an `x64_avx_reg` into an `Expr` of type `AvxReg w`, where `w` is the operation width of the
    instruction. -/
def elabAvxReg (stx : TSyntax `x64_avx_reg) : X64ElabM Expr := withRef stx do
  match stx with
  | `(x64_avx_reg| %❰ $t ❱) =>
    elabAntiquot t (←mkAppWidth (mkConst ``AvxReg))
  | _ =>
    let ⟨w, reg⟩ ← evalAvxReg stx
    setOperandWidth (toExpr w)
    pure (toExpr reg)

/-- Evaluate a low register for memory addressing (rejecting `%ah`/`%bh`/`%ch`/`%dh`). -/
def evalLowReg (stx : TSyntax `x64_reg) : TermElabM (Width × Reg64) := withRef stx do
  let ⟨w, r⟩ ← evalReg stx
  match r with
  | .low r64 _ => pure (w, r64)
  | _ => throwError "high byte register cannot be used for an addrexpr"

/-- Elaborate a low register for memory addressing into an `Expr` of type `Reg64`, reporting its width
    (the address width, see `computingAddrWidth`); an antiquotation `%❰t❱` is elaborated at `Reg64` and
    denotes a 64-bit address. -/
def elabLowReg (stx : TSyntax `x64_reg) : X64ElabM Expr := withRef stx do
  match stx with
  | `(x64_reg| %❰ $t ❱) =>
    setOperandWidth (toExpr Width.W64)
    elabAntiquot t (mkConst ``Reg64)
  | _ =>
    let (w, r) ← evalLowReg stx
    setOperandWidth (toExpr w)
    pure (toExpr r)

/-- Elaborate a base register for memory addressing (`%rip` or a low GPR) into an `Expr` of type
    `RegOrRip`. -/
def elabRegOrRip (stx : TSyntax `x64_reg_or_rip) : X64ElabM Expr := withRef stx do
  match stx with
  | `(x64_reg_or_rip| %rip) =>
    setOperandWidth (toExpr Width.W64)
    pure (toExpr RegOrRip.rip)
  | `(x64_reg_or_rip| $r:x64_reg) =>
    return mkApp (mkConst ``RegOrRip.reg) (← elabLowReg r)
  | _ => throwError "expected memory base register"

-- ============================================================================
-- Memory & General Operand Elaboration
-- ============================================================================

/-- Evaluate a numeric memory index scale (`1`, `2`, `4`, or `8`) into its corresponding `Width`. -/
def evalScale (stx : TSyntax `num) : X64ElabM Width := withRef stx do
  match stx.getNat with
  | 1 => pure .W8
  | 2 => pure .W16
  | 4 => pure .W32
  | 8 => pure .W64
  | s => throwError "invalid scale {s}, must be 1, 2, 4, or 8"

/-- Elaborate an `x64_mem` syntax node into an `Expr` of type `AddrExpr`, recording the instruction's
    address width. -/
def elabMem (stx : TSyntax `x64_mem) : X64ElabM Expr := withRef stx <| computingAddrWidth do
  match stx with
  | `(x64_mem| $[$disp?:x64_const]?($baseStx:x64_reg_or_rip $[, $idxStx?:x64_reg $[, $scStx??:num]?]?)) =>
    let base ← elabRegOrRip baseStx
    let disp ← match disp? with
      | some disp =>
        let disp ← evalConstExpr disp
        if base.isConstOf ``RegOrRip.rip && ! disp matches .int64 _ then
          pure <| .sub disp .after_current_instruction
        else pure disp
      | none => pure <| .int64 0
    let scale ← (evalScale <$> scStx??.join).getD (pure .W8)
    let idx? ← idxStx?.mapM fun idx => do
        let idx ← elabLowReg idx
        pure (mkApp2 (mkConst ``AddrIndex.mk) idx (toExpr scale))
    mkAddrExpr disp (some base) idx?
  | `(x64_mem| $disp:x64_const) =>
    setOperandWidth (toExpr Width.W64)
    let d ← evalConstExpr disp
    mkAddrExpr d
  | _ => throwError "invalid memory operand"
where
  /-- `AddrExpr.mk base? idx? disp`, with `base? : Option RegOrRip` and `idx? : Option AddrIndex`. -/
  mkAddrExpr (disp : ConstExpr) (base? : Option Expr := none) (idx? : Option Expr := none) : Id Expr :=
    let optionify (ty : Name) : Option Expr → Expr
      | some e => mkApp2 (Lean.mkConst ``Option.some [0]) (Lean.mkConst ty) e
      | none => mkApp (Lean.mkConst ``Option.none [0]) (Lean.mkConst ty)
    return mkApp3 (Lean.mkConst ``AddrExpr.mk) (optionify ``RegOrRip base?) (optionify ``AddrIndex idx?) (toExpr disp)

/-- Extract the symbol name of a `$sym` immediate, which Lean parses as an antiquotation node. -/
def getAntiquotSym (stx : Syntax) : TermElabM String := withRef stx do
  unless stx.isAntiquot do throwError "invalid operand"
  let name := stx.getAntiquotTerm.getId
  if name.isAnonymous then throwError "invalid operand"
  pure name.toString

/-- Elaborate an `x64_reg_or_mem` into an `Expr` of type `RegOrMem w`. -/
def elabRegOrMem (stx : TSyntax `x64_reg_or_mem) : X64ElabM Expr := withRef stx do
  match stx with
  | `(x64_reg_or_mem| $r:x64_reg) => mkAppWidth (mkConst ``RegOrMem.reg) #[← elabReg r]
  | `(x64_reg_or_mem| $m:x64_mem) => mkAppWidth (mkConst ``RegOrMem.mem) #[← elabMem m]
  | _ => throwError "expected register or memory operand"

/-- Elaborate an `x64_operand` in a position that admits no immediate (a destination) into an `Expr` of
    type `RegOrMem w`. -/
def elabRegOrMemOperand (stx : TSyntax `x64_operand) : X64ElabM Expr := withRef stx do
  match stx with
  | `(x64_operand| $rm:x64_reg_or_mem) => elabRegOrMem rm
  | `(x64_operand| ❰ $t ❱) => elabAntiquot t (← mkAppWidth (mkConst ``RegOrMem))
  | _ => throwError "expected register or memory operand, got $"

/-- Elaborate an `x64_operand` into an `Expr` of type `Operand w`. -/
def elabOperand (stx : TSyntax `x64_operand) : X64ElabM Expr := withRef stx do
  let imm (ce : ConstExpr) : X64ElabM Expr := mkAppWidth (mkConst ``Operand.imm) #[toExpr ce]
  if stx.raw.isAntiquot then
    imm (.label (← getAntiquotSym stx.raw))
  else match stx with
  | `(x64_operand| $rm:x64_reg_or_mem) => mkAppWidth (mkConst ``Operand.regOrMem) #[← elabRegOrMem rm]
  | `(x64_operand| $i:x64_imm) => imm (← evalConstExpr (← getImmConst i))
  | `(x64_operand| ❰ $t ❱) => elabAntiquot t (← mkAppWidth (mkConst ``Operand))
  -- `$sym ± n`: the left operand is the `$sym` antiquotation node (see the grammar).
  | `(x64_operand| $sym:x64_operand + $n:num) =>
    let s ← getAntiquotSym sym.raw
    let i ← withRef n <| Int64.ofNatNoOverflow n.getNat
    imm (.add (.label s) (.int64 i))
  | `(x64_operand| $sym:x64_operand - $n:num) =>
    let s ← getAntiquotSym sym.raw
    let i ← withRef n <| Int64.ofNatNoOverflow n.getNat
    imm (.sub (.label s) (.int64 i))
  | _ => throwError "invalid operand"

/-- Elaborate an `x64_avx_operand` into an `Expr` of type `AvxRegOrMem w`. -/
def elabAvxRegOrMem (stx : TSyntax `x64_avx_operand) : X64ElabM Expr := withRef stx do
  match stx with
  | `(x64_avx_operand| $r:x64_avx_reg) => mkAppWidth (mkConst ``AvxRegOrMem.avx) #[← elabAvxReg r]
  | `(x64_avx_operand| $m:x64_mem) => mkAppWidth (mkConst ``AvxRegOrMem.mem) #[← elabMem m]
  | `(x64_avx_operand| ❰ $t ❱) => elabAntiquot t (← mkAppWidth (mkConst ``AvxRegOrMem))
  | _ => throwError "expected AVX register or memory operand"

/-- Elaborate a relative branch target (`RelRegOrMem`) from an `x64_operand`. -/
def elabRelTarget (stx : TSyntax `x64_operand) : X64ElabM Expr := withRef stx do
  match stx with
  | `(x64_operand| $r:x64_reg) =>
    let (reg, w) ← withOperandWidth none (elabReg r)
    unless ← isDefEq w (toExpr Width.W64) do
      throwError "expected a 64-bit register in relative addressing position"
    pure (mkApp (mkConst ``RelRegOrMem.reg) reg)
  | `(x64_operand| $id:x64_ident) =>
    let lbl ← getAsmIdent id
    pure (toExpr (RelRegOrMem.rel (.sub (.label lbl) .after_current_instruction)))
  | `(x64_operand| $_:x64_const) =>
    -- Labels are handled above.
    throwError "absolute branch targets are not supported"
  | `(x64_operand| $m:x64_mem) =>
    return mkApp (mkConst ``RelRegOrMem.mem) (← elabMem m)
  | `(x64_operand| ❰ $t ❱) =>
    elabAntiquot t (mkConst ``RelRegOrMem)
  | _ => throwError "invalid branch target operand"

/-- Evaluate an `x64_shift_count` (`$imm` or `%cl`) into a `ShiftCountExpr`. -/
def evalShiftCount (stx : TSyntax `x64_shift_count) : TermElabM ShiftCountExpr := withRef stx do
  if stx.raw.isAntiquot then
    let s ← getAntiquotSym stx.raw
    pure (.imm8 (.label s))
  else match stx with
  | `(x64_shift_count| %cl) => pure .cl
  | `(x64_shift_count| $imm:x64_imm) => return .imm8 (← evalConstExpr (← getImmConst imm))
  | _ => throwError "expected immediate or %cl shift count"

-- ============================================================================
-- Mnemonic Suffixes & Constructors
-- ============================================================================

/-- Evaluate the operand-width suffix of a mnemonic (`""`, `"b"`, `"w"`, `"l"`, `"q"`). -/
def evalWidthSuffix (suffix : String) : TermElabM (Option Width) :=
  match suffix with
  | ""  => return none
  | "b" => return (some .W8)
  | "w" => return (some .W16)
  | "l" => return (some .W32)
  | "q" => return (some .W64)
  | sfx => throwError "invalid operand width suffix '{sfx}'"

/-- Set the instruction's operation width from its mnemonic's width suffix, when present. -/
def setSuffixWidth (stx : Syntax) : X64ElabM Unit := do
  if let some w ← evalWidthSuffix (← getAffixedSuffix stx) then
    setOperandWidth (toExpr w)

/-- Evaluate the condition-code suffix of a mnemonic (`cmov<cc>`, `set<cc>`, `j<cc>`). -/
def evalCondCodeSuffix (stx : Syntax) : TermElabM CondCode := withRef stx do
  match ← getAffixedSuffix stx with
  | "z"  | "e"          => return .z
  | "nz" | "ne"         => return .nz
  | "b"  | "c"  | "nae" => return .b
  | "ae" | "nc" | "nb"  => return .ae
  | "a"  | "nbe"        => return .a
  | "be" | "na"         => return .be
  | "l"  | "nge"        => return .l
  | "le" | "ng"         => return .le
  | sfx                 => throwError "invalid condition code '{sfx}'"

/-- The `Operation` constructor of an `x64_bin_op`. -/
def elabBinOp (stx : TSyntax `x64_bin_op) : TermElabM Expr := withRef stx do
  match (← splitSuffixed stx).1 with
  | "add"            => pure (mkConst ``Operation.add)
  | "adc"            => pure (mkConst ``Operation.adc)
  | "sub"            => pure (mkConst ``Operation.sub)
  | "sbb"            => pure (mkConst ``Operation.sbb)
  | "mov" | "movabs" => pure (mkConst ``Operation.mov)
  | "xor"            => pure (mkConst ``Operation.xor)
  | "and"            => pure (mkConst ``Operation.and)
  | "or"             => pure (mkConst ``Operation.or)
  | "cmp"            => pure (mkConst ``Operation.cmp)
  | "test"           => pure (mkConst ``Operation.test)
  | stem             => throwError "invalid binary instruction mnemonic '{stem}'"

/-- The `Operation` constructor of an `x64_rm_reg_op`. -/
def elabRmRegOp (stx : TSyntax `x64_rm_reg_op) : TermElabM Expr := withRef stx do
  match (← splitSuffixed stx).1 with
  | "adcx" => pure (mkConst ``Operation.adcx)
  | "adox" => pure (mkConst ``Operation.adox)
  | stem   => throwError "invalid carry-chain mnemonic '{stem}'"

/-- The `Operation` constructor of an `x64_unary_op`. -/
def elabUnaryOp (stx : TSyntax `x64_unary_op) : TermElabM Expr := withRef stx do
  match (← splitSuffixed stx).1 with
  | "mul" => pure (mkConst ``Operation.mul)
  | "neg" => pure (mkConst ``Operation.neg)
  | "dec" => pure (mkConst ``Operation.dec)
  | "inc" => pure (mkConst ``Operation.inc)
  | "not" => pure (mkConst ``Operation.not)
  | stem  => throwError "invalid unary instruction mnemonic '{stem}'"

/-- The `(srcWidth, dstWidth)` and `Operation` constructor of an `x64_ext_mov_op`. -/
def elabExtMovOp (stx : TSyntax `x64_ext_mov_op) : TermElabM (Expr × Width × Width) := withRef stx do
  let (stem, sfx) ← splitSuffixed stx
  let op : Expr ← match stem with
    | "movs" => pure (mkConst ``Operation.movsx)
    | "movz" => pure (mkConst ``Operation.movzx)
    | _      => throwError "invalid extending move mnemonic '{stem}'"
  let ws ← match sfx with
    | "bw"        => pure (.W8,  .W16)
    | "bl"        => pure (.W8,  .W32)
    | "bq"        => pure (.W8,  .W64)
    | "wl"        => pure (.W16, .W32)
    | "wq"        => pure (.W16, .W64)
    | "lq" | "xd" => pure (.W32, .W64)
    | _           => throwError "invalid extension width suffix '{sfx}'"
  pure (op, ws)

/-- The `AvxOperation` constructor of an `x64_avx_op`. -/
def elabAvxOp (stx : TSyntax `x64_avx_op) : TermElabM Expr := withRef stx do
  let (stem, sfx) ← splitSuffixed stx
  match stem, sfx with
  | "movu",  "ps" => pure (mkConst ``AvxOperation.movups)
  | "vmovu", "ps" => pure (mkConst ``AvxOperation.vmovups)
  | "mova",  "ps" => pure (mkConst ``AvxOperation.movaps)
  | "add",   "ps" => pure (mkConst ``AvxOperation.addps)
  | "sub",   "ps" => pure (mkConst ``AvxOperation.subps)
  | _, _          => throwError "invalid AVX mnemonic"

/-- The `Operation` constructor of an `x64_shift_op`. -/
def elabShiftOp (stx : TSyntax `x64_shift_op) : TermElabM Expr := withRef stx do
  match (← splitSuffixed stx).1 with
  | "shl" | "sal" => pure (mkConst ``Operation.shl)
  | "shr"         => pure (mkConst ``Operation.shr)
  | "sar"         => pure (mkConst ``Operation.sar)
  | "rol"         => pure (mkConst ``Operation.rol)
  | "ror"         => pure (mkConst ``Operation.ror)
  | "rcl"         => pure (mkConst ``Operation.rcl)
  | "rcr"         => pure (mkConst ``Operation.rcr)
  | stem          => throwError "invalid shift/rotate mnemonic '{stem}'"

/-- The `Operation` constructor of an `x64_shd_op`. -/
def elabShdOp (stx : TSyntax `x64_shd_op) : TermElabM Expr := withRef stx do
  match ← getAffixedStem stx with
  | "shld" => pure (mkConst ``Operation.shld)
  | "shrd" => pure (mkConst ``Operation.shrd)
  | stem   => throwError "invalid double-precision shift mnemonic '{stem}'"

-- ============================================================================
-- Instruction Elaboration
-- ============================================================================


/-- Elaborate an `x64_instr` syntax node into a `Lean.Expr` of type `Instr`. Each arm names the
    operation's constructor `mk` and records the mnemonic's width suffix before elaborating the operands,
    so that an operand disagreeing with the suffix is reported against the suffix. -/
def elabInstr (stx : TSyntax `x64_instr) : X64ElabM Expr := withRef stx do
  match stx with
  | `(x64_instr| .align $align:num $[, $pad?:num]?) =>
    mkClosedInstr (.nopalign align.getNat (pad?.map (·.getNat)))
  | `(x64_instr| $op:x64_bin_op $src:x64_operand, $dst:x64_operand) =>
    let mk ← elabBinOp op
    setSuffixWidth op
    let src ← elabOperand src
    let dst ← elabRegOrMemOperand dst
    mkRegularInstr (← mkAppWidth mk #[dst, src])
  | `(x64_instr| $op:x64_rm_reg_op $src:x64_operand, $dst:x64_reg) =>
    let mk ← elabRmRegOp op
    setSuffixWidth op
    let src ← elabRegOrMemOperand src
    let dst ← elabReg dst
    mkRegularInstr (← mkAppWidth mk #[dst, src])
  | `(x64_instr| $op:x64_cmov_op $src:x64_operand, $dst:x64_reg) =>
    let mk := mkConst ``Operation.cmovcc
    let cc ← evalCondCodeSuffix op
    let src ← elabRegOrMemOperand src
    let dst ← elabReg dst
    mkRegularInstr (← mkAppWidth mk #[toExpr cc, dst, src])
  | `(x64_instr| $op:x64_unary_op $dst:x64_operand) =>
    let mk ← elabUnaryOp op
    setSuffixWidth op
    let dst ← elabRegOrMemOperand dst
    mkRegularInstr (← mkAppWidth mk #[dst])
  | `(x64_instr| $op:x64_set_op $dst:x64_operand) =>
    let mk := mkConst ``Operation.setcc
    let cc ← evalCondCodeSuffix op
    setOperandWidth (toExpr Width.W8)
    let dst ← elabRegOrMemOperand dst
    mkRegularInstr (← mkAppWidth mk #[toExpr cc, dst])
  | `(x64_instr| $op:x64_imul_op $src:x64_operand) =>
    let mk := mkConst ``Operation.imul1
    setSuffixWidth op
    let src ← elabRegOrMemOperand src
    mkRegularInstr (← mkAppWidth mk #[src])
  | `(x64_instr| $op:x64_imul_op $src:x64_operand, $dst:x64_operand) =>
    let mk := mkConst ``Operation.imul
    setSuffixWidth op
    let src ← elabOperand src
    let dst ← elabRegOrMemOperand dst
    let noDst ← mkNone (← mkAppWidth (mkConst ``RegOrMem))
    mkRegularInstr (← mkAppWidth mk #[noDst, dst, src])
  | `(x64_instr| $op:x64_imul_op $src1:x64_operand, $src2:x64_operand, $dst:x64_reg) =>
    let mk := mkConst ``Operation.imul
    setSuffixWidth op
    let src1 ← elabOperand src1
    let src2 ← elabRegOrMemOperand src2
    let dst ← mkAppWidth (mkConst ``RegOrMem.reg) #[← elabReg dst]
    let dst ← mkSome (← mkAppWidth (mkConst ``RegOrMem)) dst
    mkRegularInstr (← mkAppWidth mk #[dst, src2, src1])
  | `(x64_instr| $op:x64_mulx_op $src:x64_operand, $lo:x64_reg, $hi:x64_reg) =>
    let mk := mkConst ``Operation.mulx
    setSuffixWidth op
    let src ← elabRegOrMemOperand src
    let lo ← elabReg lo
    let hi ← elabReg hi
    mkRegularInstr (← mkAppWidth mk #[hi, lo, src])
  | `(x64_instr| movsx $src:x64_reg, $dst:x64_reg) =>
    let mk := mkConst ``Operation.movsx
    let dst ← mkAppWidth (mkConst ``RegOrMem.reg) #[← elabReg dst]
    let (src, wSrc) ← withOperandWidthUnderCurrent do mkAppWidth (mkConst ``RegOrMem.reg) #[← elabReg src]
    mkRegularInstr (← mkAppWidth mk #[wSrc, dst, src])
  | `(x64_instr| movzx $src:x64_reg, $dst:x64_reg) =>
    let mk := mkConst ``Operation.movzx
    let dst ← mkAppWidth (mkConst ``RegOrMem.reg) #[← elabReg dst]
    let (src, wSrc) ← withOperandWidthUnderCurrent do mkAppWidth (mkConst ``RegOrMem.reg) #[← elabReg src]
    mkRegularInstr (← mkAppWidth mk #[wSrc, dst, src])
  | `(x64_instr| $op:x64_ext_mov_op $src:x64_operand, $dst:x64_reg) =>
    let (mk, wSrc, wDst) ← elabExtMovOp op
    setOperandWidth (toExpr wDst)
    let dst ← mkAppWidth (mkConst ``RegOrMem.reg) #[← elabReg dst]
    let (src, _) ← withOperandWidth (some wSrc) (elabRegOrMemOperand src)
    mkRegularInstr (← mkAppWidth mk #[toExpr wSrc, dst, src])
  | `(x64_instr| $op:x64_lea_op $m:x64_mem, $dst:x64_reg) =>
    let mk := mkConst ``Operation.lea
    setSuffixWidth op
    let src ← elabMem m
    let dst ← elabReg dst
    mkRegularInstr (← mkAppWidth mk #[dst, src])
  | `(x64_instr| $op:x64_avx_op $src:x64_avx_operand, $dst:x64_avx_operand) =>
    let mk ← elabAvxOp op
    let src ← elabAvxRegOrMem src
    let dst ← elabAvxRegOrMem dst
    mkAvxInstr (← mkAppWidth mk #[dst, src])
  | `(x64_instr| $op:x64_shift_op $dst:x64_operand) =>
    let mk ← elabShiftOp op
    setSuffixWidth op
    let dst ← elabRegOrMemOperand dst
    mkRegularInstr (← mkAppWidth mk #[dst, toExpr (ShiftCountExpr.imm8 (.int64 1))])
  | `(x64_instr| $op:x64_shift_op $cnt:x64_shift_count, $dst:x64_operand) =>
    let mk ← elabShiftOp op
    setSuffixWidth op
    let cnt ← evalShiftCount cnt
    let dst ← elabRegOrMemOperand dst
    mkRegularInstr (← mkAppWidth mk #[dst, toExpr cnt])
  | `(x64_instr| $op:x64_shd_op $cnt:x64_shift_count, $src:x64_reg, $dst:x64_operand) =>
    let mk ← elabShdOp op
    setSuffixWidth op
    let cnt ← evalShiftCount cnt
    let src ← elabReg src
    let dst ← elabRegOrMemOperand dst
    mkRegularInstr (← mkAppWidth mk #[dst, src, toExpr cnt])
  | `(x64_instr| $op:x64_bswap_op $dst:x64_reg) =>
    let mk := mkConst ``Operation.bswap
    setSuffixWidth op
    let dst ← elabReg dst
    mkRegularInstr (← mkAppWidth mk #[dst])
  | `(x64_instr| $op:x64_push_op $src:x64_operand) =>
    let mk := mkConst ``Operation.push
    setSuffixWidth op
    let src ← elabOperand src
    mkRegularInstr (← mkAppWidth mk #[src]) (ifUndetermined := some .W64)
  | `(x64_instr| $op:x64_pop_op $dst:x64_operand) =>
    let mk := mkConst ``Operation.pop
    setSuffixWidth op
    let dst ← elabRegOrMemOperand dst
    mkRegularInstr (← mkAppWidth mk #[dst]) (ifUndetermined := some .W64)
  | `(x64_instr| ret) | `(x64_instr| retq) =>
    mkClosedInstr .ret
  | `(x64_instr| call $target:x64_operand) | `(x64_instr| callq $target:x64_operand) =>
    let mk := mkConst ``Operation.call
    setOperandWidth (toExpr Width.W64)
    let target ← elabRelTarget target
    mkRegularInstr (← mkAppWidth mk #[target])
  | `(x64_instr| jmp $target:x64_operand) | `(x64_instr| jmpq $target:x64_operand) =>
    let mk := mkConst ``Operation.jmp
    setOperandWidth (toExpr Width.W64)
    let target ← elabRelTarget target
    mkRegularInstr (← mkAppWidth mk #[target])
  | `(x64_instr| nop) =>
    mkClosedInstr (.nop 1)
  | `(x64_instr| nop $sz:num) =>
    mkClosedInstr (.nop sz.getNat)
  | `(x64_instr| $op:x64_jcc_op $lbl:x64_ident) =>
    let cc ← evalCondCodeSuffix op
    let target ← getAsmIdent lbl
    mkClosedInstr (.jcc cc target)
  | _ => throwError "invalid instruction syntax"
where
  /-- A 64-bit instruction without operands to infer widths from. -/
  mkClosedInstr (op : Operation .W64) : X64ElabM Expr :=
    pure (toExpr (Instr.regular .W64 .W64 op))

-- ============================================================================
-- Directive & Program Elaboration
-- ============================================================================

/-- Elaborate an `x64_directive` syntax node into a `Lean.Expr` of type `Directive`. -/
def elabDirective (stx : TSyntax `x64_directive) : TermElabM Expr := withRef stx do
  match stx with
  | `(x64_directive| $lbl:x64_ident : $[;]?) =>
    let name ← getAsmIdent lbl
    return (Lean.toExpr (Kraken.Directive.label name : _root_.Directive))
  | `(x64_directive| $ins:x64_instr ;)
  | `(x64_directive| $ins:x64_instr) =>
    return mkApp2 (mkConst ``Kraken.Directive.instr) (mkConst ``Instr) (← (elabInstr ins).run')
  | `(x64_directive| ❰ $t ❱ $[;]?) =>
    elabAntiquot t (mkConst ``_root_.Directive)
  | _ => throwError "invalid assembly directive"

/-- Elaborate an `x64_prog` syntax node into a `Lean.Expr` of type `Program` (`List Directive`). -/
def elabProgram (stx : TSyntax `x64_prog) : TermElabM Expr := withRef stx do
  match stx with
  | `(x64_prog| $dirs:x64_directive*) =>
    let dirExprs ← dirs.mapM elabDirective
    mkListLit (mkConst ``_root_.Directive) dirExprs.toList
  | _ => throwError "invalid assembly program"

-- ============================================================================
-- Public String Parser/Elaborator & Macros
-- ============================================================================

/-- Parse and elaborate an X64 assembly string (with `# ...` line comments) into a `Lean.Expr`
    representing a Kraken `Program`. -/
public def elabX64 (s : String) : TermElabM Expr :=
  elabCategory `x64_prog elabProgram (replaceLineComments "#" s)

end

/-- Inline unquoted X64 assembly block macro/elaborator (`[x64| ... ]`). -/
elab "[x64|" p:x64_prog "]" : term => elabProgram p

/-- Read an X64 assembly file, strip assembler directives, parse via `runParserCategory`,
    and elaborate into a Kraken `Program`. -/
elab "include_x64" path:str : term => do
  let content ← IO.FS.readFile path.getString
  withRef path <| elabX64 (stripDirectives content)

end Kraken.X64.Parser
