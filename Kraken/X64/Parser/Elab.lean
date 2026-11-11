module

public import Kraken.X64.Parser.Basic
public meta import Kraken.X64.Parser.Basic
public import Kraken.X64.Parser.Syntax
public meta import Kraken.X64.Parser.Syntax
public meta import Lean

/-!
Operands may contain antiquotations (`%❰t❱`, `❰t❱`), whose value is only known as a term, so everything
from operands upwards is elaborated to `Expr`s. The widths of an instruction are kept in the `X64ElabM` state
rather than threaded through the operand elaborators: a register reports its width, which must agree with
what the mnemonic suffix and the other operands determined; immediates and memory operands are valid at any
width and simply use the instruction's. Where bare `❰t❱` matches nested categories, parser priorities choose
the widest type (`Operand w` / `RegOrMem w` / `RelRegOrMem` over `ConstExpr` over `Label`, into which
narrower types coerce).
-/

namespace Kraken.X64.Parser

open Lean Meta Elab Kraken.Parser
open Term hiding mkConst  -- `mkConst` is the pure `Lean.mkConst`, not the environment lookup `Term.mkConst`

public meta section

-- ============================================================================
-- Elaboration Monad: Operation & Address Widths
-- ============================================================================

structure X64ElabM.State where
  /-- Operand width of the scope being elaborated, of type `Width` (for regular instructions and
      memory address calculations) or `AvxWidth` (for AVX instructions): either a concrete value or
      a metavariable if it has not been inferred yet. Usually, instructions only have one operand
      width, with exceptions such as `.movsx` or `.movzx`. -/
  operandWidth : Expr
  /-- Whether the instruction has a memory operand, and if so, its address width -/
  addressWidth? : Option Expr := none

abbrev X64ElabM := StateRefT X64ElabM.State TermElabM

/-- Run the elaboration of an instruction with operation width type `W` (`Width` or `AvxWidth`),
    initialized to `width?` when already known or a fresh metavariable of type `W` otherwise. -/
nonrec def X64ElabM.run' {W α : Type} [ToExpr W] (x : X64ElabM α) (width? : Option W := none) : TermElabM α := do
  let operandWidth ← (toExpr <$> width?).getDM (mkFreshExprMVar (toTypeExpr W))
  x.run' { operandWidth }

def evalWidth? (wExpr : Expr) : Option Width := [Width.W8, .W16, .W32, .W64].find? (toExpr · == wExpr)

def evalAvxWidth? (wExpr : Expr) : Option AvxWidth := [AvxWidth.W128, .W256, .W512].find? (toExpr · == wExpr)

/-- Print a `Width` or `AvxWidth` expression as values if possible, using its `ToString` instance -/
private def ppWidth (wExpr : Expr) : MetaM MessageData := do
  let wExpr ← instantiateMVars wExpr  -- an assigned metavariable is not syntactically `Width.W64`
  if let some wValue := evalWidth? wExpr then return m!"{wValue}"
  if let some wValue := evalAvxWidth? wExpr then return m!"{wValue}"
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

/-- Run `body` at the AVX operation width `w`, for the one operand of a mixed-width instruction. -/
private def withAvxOperandWidth {α : Type} (w : AvxWidth) (body : X64ElabM α) : X64ElabM α := do
  let saved ← getOperandWidth
  modify ({ · with operandWidth := toExpr w })
  try body finally modify ({ · with operandWidth := saved })

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
    if let (some s, some d) := (evalWidth? wSrc, evalWidth? wDst) then
      unless s.bits < d.bits do throwError "source width {s} must be narrower than destination width {d}"

/-- Elaborate a regular instruction via `body` and build `Instr.regular` from the resulting operation
    and widths. The operation width may be fixed upfront via `width?`; otherwise it must be determined
    by the operands, unless `ifUndetermined` provides a default (`push`/`pop` default to 64 bits). -/
def mkRegularInstr (body : X64ElabM Expr) (width? : Option Width := none)
    (ifUndetermined : Option Width := none) : TermElabM Expr :=
  X64ElabM.run' (width? := width?) do
    let op ← body
    let w ← instantiateMVars (← getOperandWidth)
    if w.isMVar then
      let d ← ifUndetermined.getDM <| throwError "could not infer operand width"
      w.mvarId!.assign (toExpr d)
    let aw := (← get).addressWidth?.getD (toExpr Width.W64)
    instantiateMVars (mkApp3 (mkConst ``Instr.regular) aw w op)

/-- Elaborate an AVX instruction via `body` and build `Instr.avx` from the resulting operation and widths. -/
def mkAvxInstr (body : X64ElabM Expr) (width? : Option AvxWidth := none) : TermElabM Expr :=
  X64ElabM.run' (W := AvxWidth) (width? := width?) do
    let op ← body
    let w ← instantiateMVars (← getOperandWidth)
    if w.isMVar then throwError "could not infer operand width"
    let aw := (← get).addressWidth?.getD (toExpr Width.W64)
    instantiateMVars (mkApp3 (mkConst ``Instr.avx) aw w op)

/-- Reject the 512-bit form of a VEX-only mnemonic in the instruction `i`, which EVEX spells
    differently. -/
def checkNo512 (ref : Syntax) (i : Expr) : TermElabM Expr := do
  let vexOnly := [``AvxOperation.vmovdqa, ``AvxOperation.vpand, ``AvxOperation.vpandn,
    ``AvxOperation.vpor, ``AvxOperation.vpxor]
  if let .const n _ := (i.getArg! 2).getAppFn then
    if vexOnly.contains n && (← whnf (i.getArg! 1)).isConstOf ``AvxWidth.W512 then
      throwErrorAt ref "{n.getString!} has no 512-bit form"
  return i

/-- Elaborate the term `t` of an antiquotation at the type `ty` expected by its position. Elaboration is
    forced to finish here (`withSynthesize`) because the instruction inspects the result right away: the
    unification of `ty` against `t`'s type is what determines the operation width, and `mkRegularInstr`
    rejects a width that is still a metavariable. A postponed `t` would leave a placeholder of type `ty`
    behind, with the width undetermined. A type mismatch aborts the instruction instead of being recovered
    as `sorry`. -/
def elabAntiquot (t : Term) (ty : Expr) : TermElabM Expr :=
  withoutErrToSorry <| withSynthesize <| elabTermEnsuringType t ty

-- ============================================================================
-- Constant Expression Elaboration
-- ============================================================================

/-- Elaborate an `x64_ident` syntax node into an `Expr` of type `Label`. -/
def elabIdent (stx : TSyntax `x64_ident) : TermElabM Expr := withRef stx do
  match stx with
  | `(x64_ident| ❰ $t ❱) => elabAntiquot t (mkConst ``Label)
  | _ => return toExpr (← getAsmIdent stx)

def elabConstExprIdent (id : TSyntax `x64_ident) : TermElabM Expr :=
  return (mkApp (mkConst ``ConstExpr.label) <| ← elabIdent id)

/-- Elaborate an `x64_const` syntax node into an `Expr` of type `ConstExpr`. -/
def elabConstExpr (stx : TSyntax `x64_const) : TermElabM Expr := withRef stx do
  match stx with
  | `(x64_const| ❰ $t ❱) => elabAntiquot t (mkConst ``ConstExpr)
  | `(x64_const| +$n:num)
  | `(x64_const| $n:num) =>
    let i ← Int64.ofNatNoOverflow n.getNat
    pure (toExpr (ConstExpr.int64 i))
  | `(x64_const| -$n:num) =>
    let i ← Int64.ofIntNoOverflow (-(Int.ofNat n.getNat))
    pure (toExpr (ConstExpr.int64 i))
  | `(x64_const| $id:x64_ident + $n:num) =>
    let s ← elabConstExprIdent id
    let i ← withRef n <| Int64.ofNatNoOverflow n.getNat
    pure (mkApp2 (mkConst ``ConstExpr.add) s (toExpr (ConstExpr.int64 i)))
  | `(x64_const| $id:x64_ident - $n:num) =>
    let s ← elabConstExprIdent id
    let i ← withRef n <| Int64.ofNatNoOverflow n.getNat
    pure (mkApp2 (mkConst ``ConstExpr.sub) s (toExpr (ConstExpr.int64 i)))
  | `(x64_const| $a:x64_ident - $b:x64_ident) =>
    pure (mkApp2 (mkConst ``ConstExpr.sub) (← elabConstExprIdent a) (← elabConstExprIdent b))
  | `(x64_const| $id:x64_ident) =>
    elabConstExprIdent id
  | _ => throwError "invalid constant expression"

/-- The constant of an `x64_imm` (`$const`). -/
def getImmConst (stx : TSyntax `x64_imm) : TermElabM (TSyntax `x64_const) := withRef stx do
  match stx with
  | ⟨.node _ _ #[.atom _ "$", c]⟩ => pure ⟨c⟩
  | _ => throwError "invalid immediate operand"

/-- Extract the symbol name of a `$sym` immediate, which Lean parses as an antiquotation node. -/
def getAntiquotSym (stx : Syntax) : TermElabM String := withRef stx do
  unless stx.isAntiquot do throwError "invalid operand"
  let name := stx.getAntiquotTerm.getId
  if name.isAnonymous then throwError "invalid operand"
  pure name.toString

/-- Elaborate an `x64_imm` (`$const` or `$sym` antiquotation) into an `Expr` of type `ConstExpr`. -/
def elabImm (stx : TSyntax `x64_imm) : TermElabM Expr := withRef stx do
  if stx.raw.isAntiquot then
    return toExpr (ConstExpr.label (← getAntiquotSym stx.raw))
  else
    elabConstExpr (← getImmConst stx)

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
    elabAntiquot t (← mkAppWidth (mkConst ``Reg))
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
    elabAntiquot t (← mkAppWidth (mkConst ``AvxReg))
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
        let disp ← elabConstExpr disp
        if base.isConstOf ``RegOrRip.rip && !disp.isAppOfArity ``ConstExpr.int64 1 then
          pure <| mkApp2 (mkConst ``ConstExpr.sub) disp (mkConst ``ConstExpr.after_current_instruction)
        else pure disp
      | none => pure <| toExpr (ConstExpr.int64 0)
    let scale ← (evalScale <$> scStx??.join).getD (pure .W8)
    let idx? ← idxStx?.mapM fun idx => do
        let idx ← elabLowReg idx
        pure (mkApp2 (mkConst ``AddrIndex.mk) idx (toExpr scale))
    mkAddrExpr disp (some base) idx?
  | `(x64_mem| $disp:x64_const) =>
    setOperandWidth (toExpr Width.W64)
    let d ← elabConstExpr disp
    mkAddrExpr d
  | _ => throwError "invalid memory operand"
where
  /-- `AddrExpr.mk base? idx? disp`, with `base? : Option RegOrRip` and `idx? : Option AddrIndex`. -/
  mkAddrExpr (disp : Expr) (base? : Option Expr := none) (idx? : Option Expr := none) : Id Expr :=
    let optionify (ty : Name) : Option Expr → Expr
      | some e => mkApp2 (Lean.mkConst ``Option.some [0]) (Lean.mkConst ty) e
      | none => mkApp (Lean.mkConst ``Option.none [0]) (Lean.mkConst ty)
    return mkApp3 (Lean.mkConst ``AddrExpr.mk) (optionify ``RegOrRip base?) (optionify ``AddrIndex idx?) disp

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
  let imm (ce : Expr) : X64ElabM Expr := mkAppWidth (mkConst ``Operand.imm) #[ce]
  if stx.raw.isAntiquot then
    imm (toExpr (ConstExpr.label (← getAntiquotSym stx.raw)))
  else match stx with
  | `(x64_operand| $rm:x64_reg_or_mem) => mkAppWidth (mkConst ``Operand.regOrMem) #[← elabRegOrMem rm]
  | `(x64_operand| $i:x64_imm) => imm (← elabImm i)
  | `(x64_operand| ❰ $t ❱) => elabAntiquot t (← mkAppWidth (mkConst ``Operand))
  -- `$sym ± n` / `$sym - b`: the left operand is the `$sym` antiquotation node (see the grammar).
  | `(x64_operand| $sym:x64_operand + $n:num) =>
    let s ← getAntiquotSym sym.raw
    let i ← withRef n <| Int64.ofNatNoOverflow n.getNat
    imm (toExpr (ConstExpr.add (.label s) (.int64 i)))
  | `(x64_operand| $sym:x64_operand - $n:num) =>
    let s ← getAntiquotSym sym.raw
    let i ← withRef n <| Int64.ofNatNoOverflow n.getNat
    imm (toExpr (ConstExpr.sub (.label s) (.int64 i)))
  | `(x64_operand| $sym:x64_operand - $b:x64_ident) =>
    let s := toExpr (ConstExpr.label (← getAntiquotSym sym.raw))
    imm (mkApp2 (mkConst ``ConstExpr.sub) s (← elabConstExprIdent b))
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
    let lbl ← elabIdent id
    pure <| mkApp (mkConst ``RelRegOrMem.rel) <|
      mkApp2 (mkConst ``ConstExpr.sub) (mkApp (mkConst ``ConstExpr.label) lbl) (mkConst ``ConstExpr.after_current_instruction)
  | `(x64_operand| $_:x64_const) =>
    -- Labels are handled above.
    throwError "absolute branch targets are not supported"
  | `(x64_operand| $m:x64_mem) =>
    return mkApp (mkConst ``RelRegOrMem.mem) (← elabMem m)
  | `(x64_operand| ❰ $t ❱) =>
    elabAntiquot t (mkConst ``RelRegOrMem)
  | _ => throwError "invalid branch target operand"

/-- Elaborate an `x64_shift_count` (`$imm` or `%cl`) into an `Expr` of type `ShiftCountExpr`. -/
def elabShiftCount (stx : TSyntax `x64_shift_count) : TermElabM Expr := withRef stx do
  if stx.raw.isAntiquot then
    let s ← getAntiquotSym stx.raw
    pure (toExpr (ShiftCountExpr.imm8 (.label s)))
  else match stx with
  | `(x64_shift_count| %cl) => pure (toExpr ShiftCountExpr.cl)
  | `(x64_shift_count| $imm:x64_imm) =>
    return mkApp (mkConst ``ShiftCountExpr.imm8) (← elabImm imm)
  | _ => throwError "expected immediate or %cl shift count"

-- ============================================================================
-- Mnemonic Suffixes & Constructors
-- ============================================================================

/-- Evaluate the operand-width suffix of a mnemonic (`""`, `"b"`, `"w"`, `"l"`, `"q"`). -/
def evalWidthSuffix : String → TermElabM (Option Width)
  | ""  => return none
  | "b" => return (some .W8)
  | "w" => return (some .W16)
  | "l" => return (some .W32)
  | "q" => return (some .W64)
  | sfx => throwError "invalid operand width suffix '{sfx}'"

/-- Split a width-suffixed mnemonic into its `(stem, width?)` pair. -/
def splitWidthSuffixed (stx : Syntax) : TermElabM (String × Option Width) := withRef stx do
  let (stem, sfx) ← splitSuffixed stx
  return (stem, ← evalWidthSuffix sfx)

/-- Evaluate the operand-width suffix of a single-stem mnemonic (`imul*`, `lea*`, `push*`, ...). -/
def evalSuffixWidth? (stx : Syntax) : TermElabM (Option Width) := withRef stx do
  evalWidthSuffix (← getAffixedSuffix stx)

/-- Evaluate the `(srcWidth, dstWidth)` suffix of an extending move (`movs*`, `movz*`). -/
def evalExtWidthSuffix : String → TermElabM (Width × Width)
  | "bw"        => return (.W8,  .W16)
  | "bl"        => return (.W8,  .W32)
  | "bq"        => return (.W8,  .W64)
  | "wl"        => return (.W16, .W32)
  | "wq"        => return (.W16, .W64)
  | "lq" | "xd" => return (.W32, .W64)
  | sfx         => throwError "invalid extension width suffix '{sfx}'"

/-- Evaluate the condition-code suffix of a mnemonic (`cmov<cc>`, `set<cc>`, `j<cc>`). -/
def evalCondCodeSuffix (stx : Syntax) : TermElabM CondCode := withRef stx do
  match ← getAffixedSuffix stx with
  | "o"                 => return .o
  | "no"                => return .no
  | "z"  | "e"          => return .z
  | "nz" | "ne"         => return .nz
  | "b"  | "c"  | "nae" => return .b
  | "ae" | "nc" | "nb"  => return .ae
  | "a"  | "nbe"        => return .a
  | "be" | "na"         => return .be
  | "s"                 => return .s
  | "ns"                => return .ns
  | "p"  | "pe"         => return .p
  | "np" | "po"         => return .np
  | "l"  | "nge"        => return .l
  | "ge" | "nl"         => return .ge
  | "le" | "ng"         => return .le
  | "g"  | "nle"        => return .g
  | sfx                 => throwError "invalid condition code '{sfx}'"

/-- The `Operation` constructor for the stem of an `x64_bin_op`. -/
def elabBinOp : String → TermElabM Expr
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

/-- The `Operation` constructor for the stem of an `x64_rm_reg_op`. -/
def elabRmRegOp : String → TermElabM Expr
  | "adcx" => pure (mkConst ``Operation.adcx)
  | "adox" => pure (mkConst ``Operation.adox)
  | stem   => throwError "invalid carry-chain mnemonic '{stem}'"

/-- The `Operation` constructor for the stem of an `x64_unary_op`. -/
def elabUnaryOp : String → TermElabM Expr
  | "mul" => pure (mkConst ``Operation.mul)
  | "neg" => pure (mkConst ``Operation.neg)
  | "dec" => pure (mkConst ``Operation.dec)
  | "inc" => pure (mkConst ``Operation.inc)
  | "not" => pure (mkConst ``Operation.not)
  | stem  => throwError "invalid unary instruction mnemonic '{stem}'"

/-- The `Operation` constructor for the stem of an `x64_ext_mov_op`. -/
def elabExtMovOp : String → TermElabM Expr
  | "movs" => pure (mkConst ``Operation.movsx)
  | "movz" => pure (mkConst ``Operation.movzx)
  | stem   => throwError "invalid extending move mnemonic '{stem}'"

/-- The `AvxOperation` constructor of an `x64_avx_op`. -/
def elabAvxOp (stx : TSyntax `x64_avx_op) : TermElabM Expr := withRef stx do
  match stx with
  | `(x64_avx_op| movdqu)  => pure (mkConst ``AvxOperation.movdqu)
  | `(x64_avx_op| vmovdqu) => pure (mkConst ``AvxOperation.vmovdqu)
  | `(x64_avx_op| movdqa)  => pure (mkConst ``AvxOperation.movdqa)
  | `(x64_avx_op| paddd)   => pure (mkConst ``AvxOperation.paddd)
  | `(x64_avx_op| pshufb)  => pure (mkConst ``AvxOperation.pshufb)
  | `(x64_avx_op| sha256msg1) => pure (mkConst ``AvxOperation.sha256msg1)
  | `(x64_avx_op| sha256msg2) => pure (mkConst ``AvxOperation.sha256msg2)
  | `(x64_avx_op| vmovdqu32)  => pure (mkConst ``AvxOperation.vmovdqu32)
  | `(x64_avx_op| vmovdqa32)  => pure (mkConst ``AvxOperation.vmovdqa32)
  | `(x64_avx_op| vmovdqa)    => pure (mkConst ``AvxOperation.vmovdqa)
  | _ =>
    let (stem, sfx) ← splitSuffixed stx
    match stem, sfx with
    | "movu",  "ps" => pure (mkConst ``AvxOperation.movups)
    | "vmovu", "ps" => pure (mkConst ``AvxOperation.vmovups)
    | "mova",  "ps" => pure (mkConst ``AvxOperation.movaps)
    | "add",   "ps" => pure (mkConst ``AvxOperation.addps)
    | "sub",   "ps" => pure (mkConst ``AvxOperation.subps)
    | _, _          => throwError "invalid AVX mnemonic"

/-- The `AvxOperation` constructor of an `x64_avx_imm_op`. -/
def elabAvxImmOp (stx : TSyntax `x64_avx_imm_op) : TermElabM Expr := withRef stx do
  match stx with
  | `(x64_avx_imm_op| pshufd)  => pure (mkConst ``AvxOperation.pshufd)
  | `(x64_avx_imm_op| palignr) => pure (mkConst ``AvxOperation.palignr)
  | `(x64_avx_imm_op| pblendw) => pure (mkConst ``AvxOperation.pblendw)
  | `(x64_avx_imm_op| vprord)  => pure (mkConst ``AvxOperation.vprord)
  | `(x64_avx_imm_op| vpsrld)  => pure (mkConst ``AvxOperation.vpsrld)
  | `(x64_avx_imm_op| vpslld)  => pure (mkConst ``AvxOperation.vpslld)
  | _                          => throwError "invalid AVX immediate mnemonic"

/-- The `AvxOperation` constructor of an `x64_avx3_op`. -/
def elabAvx3Op (stx : TSyntax `x64_avx3_op) : TermElabM Expr := withRef stx do
  match stx with
  | `(x64_avx3_op| vpaddd)   => pure (mkConst ``AvxOperation.vpaddd)
  | `(x64_avx3_op| vpshufb)  => pure (mkConst ``AvxOperation.vpshufb)
  | `(x64_avx3_op| vpermi2q) => pure (mkConst ``AvxOperation.vpermi2q)
  | `(x64_avx3_op| vpermi2d) => pure (mkConst ``AvxOperation.vpermi2d)
  | `(x64_avx3_op| vpand)    => pure (mkConst ``AvxOperation.vpand)
  | `(x64_avx3_op| vpandn)   => pure (mkConst ``AvxOperation.vpandn)
  | `(x64_avx3_op| vpor)     => pure (mkConst ``AvxOperation.vpor)
  | `(x64_avx3_op| vpxor)    => pure (mkConst ``AvxOperation.vpxor)
  | `(x64_avx3_op| vpunpckldq)  => pure (mkConst ``AvxOperation.vpunpckldq)
  | `(x64_avx3_op| vpunpckhdq)  => pure (mkConst ``AvxOperation.vpunpckhdq)
  | `(x64_avx3_op| vpunpcklqdq) => pure (mkConst ``AvxOperation.vpunpcklqdq)
  | `(x64_avx3_op| vpunpckhqdq) => pure (mkConst ``AvxOperation.vpunpckhqdq)
  | _                        => throwError "invalid AVX 3-operand mnemonic"

/-- The `AvxOperation` constructor of an `x64_avx3_imm_op`. -/
def elabAvx3ImmOp (stx : TSyntax `x64_avx3_imm_op) : TermElabM Expr := withRef stx do
  match stx with
  | `(x64_avx3_imm_op| vpternlogd) => pure (mkConst ``AvxOperation.vpternlogd)
  | `(x64_avx3_imm_op| vshufps)    => pure (mkConst ``AvxOperation.vshufps)
  | `(x64_avx3_imm_op| vperm2i128) => pure (mkConst ``AvxOperation.vperm2i128)
  | _                              => throwError "invalid AVX 3-operand immediate mnemonic"

/-- The scalar transfer width of `vmovd` (`.W32`) or `vmovq` (`.W64`). -/
def evalVmovGpWidth (stx : TSyntax `x64_vmov_gp_op) : TermElabM Width := withRef stx do
  match stx with
  | `(x64_vmov_gp_op| vmovd) => pure .W32
  | `(x64_vmov_gp_op| vmovq) => pure .W64
  | _                        => throwError "invalid VEX scalar move mnemonic"

/-- The `Operation` constructor for the stem of an `x64_shift_op`. -/
def elabShiftOp : String → TermElabM Expr
  | "shl" | "sal" => pure (mkConst ``Operation.shl)
  | "shr"         => pure (mkConst ``Operation.shr)
  | "sar"         => pure (mkConst ``Operation.sar)
  | "rol"         => pure (mkConst ``Operation.rol)
  | "ror"         => pure (mkConst ``Operation.ror)
  | "rcl"         => pure (mkConst ``Operation.rcl)
  | "rcr"         => pure (mkConst ``Operation.rcr)
  | stem          => throwError "invalid shift/rotate mnemonic '{stem}'"

/-- The `Operation` constructor for the stem of an `x64_shd_op`. -/
def elabShdOp : String → TermElabM Expr
  | "shld" => pure (mkConst ``Operation.shld)
  | "shrd" => pure (mkConst ``Operation.shrd)
  | stem   => throwError "invalid double-precision shift mnemonic '{stem}'"

-- ============================================================================
-- Instruction Elaboration
-- ============================================================================

/-- Elaborate an `x64_instr` syntax node into a `Lean.Expr` of type `Instr`. Each arm extracts any
    mnemonic stem and width suffix upfront (passing the width to `mkRegularInstr`), so that each
    mnemonic is split at most once and any operand disagreeing with the suffix is reported against it. -/
def elabInstr (stx : TSyntax `x64_instr) : TermElabM Expr := withRef stx do
  match stx with
  | `(x64_instr| .align $align:num $[, $pad?:num]?) =>
    mkClosedInstr (.nopalign align.getNat (pad?.map (·.getNat)))
  | `(x64_instr| $op:x64_bin_op $src:x64_operand, $dst:x64_operand) =>
    let (stem, width?) ← splitWidthSuffixed op
    mkRegularInstr (width? := width?) do
      let mk ← elabBinOp stem
      let src ← elabOperand src
      let dst ← elabRegOrMemOperand dst
      mkAppWidth mk #[dst, src]
  | `(x64_instr| $op:x64_rm_reg_op $src:x64_operand, $dst:x64_reg) =>
    let (stem, width?) ← splitWidthSuffixed op
    mkRegularInstr (width? := width?) do
      let mk ← elabRmRegOp stem
      let src ← elabRegOrMemOperand src
      let dst ← elabReg dst
      mkAppWidth mk #[dst, src]
  | `(x64_instr| $op:x64_cmov_op $src:x64_operand, $dst:x64_reg) =>
    mkRegularInstr do
      let mk := mkConst ``Operation.cmovcc
      let cc ← evalCondCodeSuffix op
      let src ← elabRegOrMemOperand src
      let dst ← elabReg dst
      mkAppWidth mk #[toExpr cc, dst, src]
  | `(x64_instr| $op:x64_unary_op $dst:x64_operand) =>
    let (stem, width?) ← splitWidthSuffixed op
    mkRegularInstr (width? := width?) do
      let mk ← elabUnaryOp stem
      let dst ← elabRegOrMemOperand dst
      mkAppWidth mk #[dst]
  | `(x64_instr| $op:x64_set_op $dst:x64_operand) =>
    mkRegularInstr (width? := some .W8) do
      let mk := mkConst ``Operation.setcc
      let cc ← evalCondCodeSuffix op
      let dst ← elabRegOrMemOperand dst
      mkAppWidth mk #[toExpr cc, dst]
  | `(x64_instr| $op:x64_imul_op $src:x64_operand) =>
    let width? ← evalSuffixWidth? op
    mkRegularInstr (width? := width?) do
      let mk := mkConst ``Operation.imul1
      let src ← elabRegOrMemOperand src
      mkAppWidth mk #[src]
  | `(x64_instr| $op:x64_imul_op $src:x64_operand, $dst:x64_operand) =>
    let width? ← evalSuffixWidth? op
    mkRegularInstr (width? := width?) do
      let mk := mkConst ``Operation.imul
      let src ← elabOperand src
      let dst ← elabRegOrMemOperand dst
      let noDst ← mkNone (← mkAppWidth (mkConst ``RegOrMem))
      mkAppWidth mk #[noDst, dst, src]
  | `(x64_instr| $op:x64_imul_op $src1:x64_operand, $src2:x64_operand, $dst:x64_reg) =>
    let width? ← evalSuffixWidth? op
    mkRegularInstr (width? := width?) do
      let mk := mkConst ``Operation.imul
      let src1 ← elabOperand src1
      let src2 ← elabRegOrMemOperand src2
      let dst ← mkAppWidth (mkConst ``RegOrMem.reg) #[← elabReg dst]
      let dst ← mkSome (← mkAppWidth (mkConst ``RegOrMem)) dst
      mkAppWidth mk #[dst, src2, src1]
  | `(x64_instr| $op:x64_mulx_op $src:x64_operand, $lo:x64_reg, $hi:x64_reg) =>
    let width? ← evalSuffixWidth? op
    mkRegularInstr (width? := width?) do
      let mk := mkConst ``Operation.mulx
      let src ← elabRegOrMemOperand src
      let lo ← elabReg lo
      let hi ← elabReg hi
      mkAppWidth mk #[hi, lo, src]
  | `(x64_instr| movsx $src:x64_reg, $dst:x64_reg) =>
    mkRegularInstr do
      let mk := mkConst ``Operation.movsx
      let dst ← mkAppWidth (mkConst ``RegOrMem.reg) #[← elabReg dst]
      let (src, wSrc) ← withOperandWidthUnderCurrent do mkAppWidth (mkConst ``RegOrMem.reg) #[← elabReg src]
      mkAppWidth mk #[wSrc, dst, src]
  | `(x64_instr| movzx $src:x64_reg, $dst:x64_reg) =>
    mkRegularInstr do
      let mk := mkConst ``Operation.movzx
      let dst ← mkAppWidth (mkConst ``RegOrMem.reg) #[← elabReg dst]
      let (src, wSrc) ← withOperandWidthUnderCurrent do mkAppWidth (mkConst ``RegOrMem.reg) #[← elabReg src]
      mkAppWidth mk #[wSrc, dst, src]
  | `(x64_instr| $op:x64_ext_mov_op $src:x64_operand, $dst:x64_reg) =>
    let (stem, sfx) ← splitSuffixed op
    let (wSrc, wDst) ← withRef op <| evalExtWidthSuffix sfx
    mkRegularInstr (width? := some wDst) do
      let mk ← withRef op <| elabExtMovOp stem
      let dst ← mkAppWidth (mkConst ``RegOrMem.reg) #[← elabReg dst]
      let (src, _) ← withOperandWidth (some wSrc) (elabRegOrMemOperand src)
      mkAppWidth mk #[toExpr wSrc, dst, src]
  | `(x64_instr| $op:x64_lea_op $m:x64_mem, $dst:x64_reg) =>
    let width? ← evalSuffixWidth? op
    mkRegularInstr (width? := width?) do
      let mk := mkConst ``Operation.lea
      let src ← elabMem m
      let dst ← elabReg dst
      mkAppWidth mk #[dst, src]
  | `(x64_instr| $op:x64_avx_op $src:x64_avx_operand, $dst:x64_avx_operand) =>
    checkNo512 op <| ← mkAvxInstr do
      let mk ← elabAvxOp op
      let src ← elabAvxRegOrMem src
      let dst ← elabAvxRegOrMem dst
      mkAppWidth mk #[dst, src]
  | `(x64_instr| $op:x64_avx_imm_op $imm:x64_imm, $src:x64_avx_operand, $dst:x64_avx_operand) =>
    mkAvxInstr do
      let mk ← elabAvxImmOp op
      let imm ← elabImm imm
      let src ← elabAvxRegOrMem src
      let dst ← elabAvxRegOrMem dst
      mkAppWidth mk #[dst, src, imm]
  | `(x64_instr| $op:x64_avx3_op $src2:x64_avx_operand, $src1:x64_avx_operand, $dst:x64_avx_operand) =>
    checkNo512 op <| ← mkAvxInstr do
      let mk ← elabAvx3Op op
      let src2 ← elabAvxRegOrMem src2
      let src1 ← elabAvxRegOrMem src1
      let dst ← elabAvxRegOrMem dst
      mkAppWidth mk #[dst, src1, src2]
  | `(x64_instr| $op:x64_avx3_imm_op $imm:x64_imm, $src2:x64_avx_operand, $src1:x64_avx_operand, $dst:x64_avx_operand) =>
    -- `vperm2i128` exists at 256 bits only.
    let width? := match op with
      | `(x64_avx3_imm_op| vperm2i128) => some .W256
      | _ => none
    mkAvxInstr (width? := width?) do
      let mk ← elabAvx3ImmOp op
      let imm ← elabImm imm
      let src2 ← elabAvxRegOrMem src2
      let src1 ← elabAvxRegOrMem src1
      let dst ← elabAvxRegOrMem dst
      mkAppWidth mk #[dst, src1, src2, imm]
  | `(x64_instr| sha256rnds2 $src:x64_avx_operand, $dst:x64_avx_operand) =>
    mkAvxInstr do
      let src ← elabAvxRegOrMem src
      let dst ← elabAvxRegOrMem dst
      mkAppWidth (mkConst ``AvxOperation.sha256rnds2) #[dst, src]
  | `(x64_instr| sha256rnds2 $k:x64_avx_reg, $src:x64_avx_operand, $dst:x64_avx_operand) =>
    let ⟨.W128, .xmm .mm0⟩ ← evalAvxReg k
      | throwErrorAt k "the implicit operand of sha256rnds2 is %xmm0"
    mkAvxInstr do
      let src ← elabAvxRegOrMem src
      let dst ← elabAvxRegOrMem dst
      mkAppWidth (mkConst ``AvxOperation.sha256rnds2) #[dst, src]
  | `(x64_instr| vinserti64x4 $imm:x64_imm, $src2:x64_avx_operand, $src1:x64_avx_operand, $dst:x64_avx_operand) =>
    mkAvxInstr (width? := some .W512) do
      let imm ← elabImm imm
      let src2 ← withAvxOperandWidth .W256 (elabAvxRegOrMem src2)
      let src1 ← elabAvxRegOrMem src1
      let dst ← elabAvxRegOrMem dst
      mkAppWidth (mkConst ``AvxOperation.vinserti64x4) #[dst, src1, src2, imm]
  | `(x64_instr| $op:x64_vmov_gp_op $src:x64_avx_reg, $dst:x64_avx_reg) =>
    let n ← evalVmovGpWidth op
    if n != .W64 then throwErrorAt op "vmovd takes no two xmm operands"
    mkAvxInstr (width? := some .W128) do
      let src ← elabAvxReg src
      let dst ← elabAvxReg dst
      mkAppWidth (mkConst ``AvxOperation.vmovq) #[dst, src]
  | `(x64_instr| $op:x64_vmov_gp_op $src:x64_avx_reg, $dst:x64_operand) =>
    let n ← evalVmovGpWidth op
    mkAvxInstr (width? := some .W128) do
      let src ← elabAvxReg src
      let (dst, _) ← withOperandWidth (some n) (elabRegOrMemOperand dst)
      mkAppWidth (mkConst ``AvxOperation.vmovOut) #[toExpr n, dst, src]
  | `(x64_instr| $op:x64_vmov_gp_op $src:x64_operand, $dst:x64_avx_reg) =>
    let n ← evalVmovGpWidth op
    mkAvxInstr (width? := some .W128) do
      let (src, _) ← withOperandWidth (some n) (elabRegOrMemOperand src)
      let dst ← elabAvxReg dst
      mkAppWidth (mkConst ``AvxOperation.vmovIn) #[toExpr n, dst, src]
  | `(x64_instr| vzeroupper) =>
    pure (toExpr (Instr.avx .W64 .W128 .vzeroupper))
  | `(x64_instr| $op:x64_shift_op $dst:x64_operand) =>
    let (stem, width?) ← splitWidthSuffixed op
    mkRegularInstr (width? := width?) do
      let mk ← elabShiftOp stem
      let dst ← elabRegOrMemOperand dst
      mkAppWidth mk #[dst, toExpr (ShiftCountExpr.imm8 (.int64 1))]
  | `(x64_instr| $op:x64_shift_op $cnt:x64_shift_count, $dst:x64_operand) =>
    let (stem, width?) ← splitWidthSuffixed op
    mkRegularInstr (width? := width?) do
      let mk ← elabShiftOp stem
      let cnt ← elabShiftCount cnt
      let dst ← elabRegOrMemOperand dst
      mkAppWidth mk #[dst, cnt]
  | `(x64_instr| $op:x64_shd_op $cnt:x64_shift_count, $src:x64_reg, $dst:x64_operand) =>
    let (stem, width?) ← splitWidthSuffixed op
    mkRegularInstr (width? := width?) do
      let mk ← elabShdOp stem
      let cnt ← elabShiftCount cnt
      let src ← elabReg src
      let dst ← elabRegOrMemOperand dst
      mkAppWidth mk #[dst, src, cnt]
  | `(x64_instr| $op:x64_bswap_op $dst:x64_reg) =>
    let width? ← evalSuffixWidth? op
    mkRegularInstr (width? := width?) do
      let mk := mkConst ``Operation.bswap
      let dst ← elabReg dst
      mkAppWidth mk #[dst]
  | `(x64_instr| $op:x64_push_op $src:x64_operand) =>
    let width? ← evalSuffixWidth? op
    mkRegularInstr (width? := width?) (ifUndetermined := some .W64) do
      let mk := mkConst ``Operation.push
      let src ← elabOperand src
      mkAppWidth mk #[src]
  | `(x64_instr| $op:x64_pop_op $dst:x64_operand) =>
    let width? ← evalSuffixWidth? op
    mkRegularInstr (width? := width?) (ifUndetermined := some .W64) do
      let mk := mkConst ``Operation.pop
      let dst ← elabRegOrMemOperand dst
      mkAppWidth mk #[dst]
  | `(x64_instr| ret) | `(x64_instr| retq) =>
    mkClosedInstr .ret
  | `(x64_instr| cld) =>
    mkClosedInstr .cld
  | `(x64_instr| std) =>
    mkClosedInstr .std
  | `(x64_instr| call $target:x64_operand) | `(x64_instr| callq $target:x64_operand) =>
    mkRegularInstr (width? := some .W64) do
      let mk := mkConst ``Operation.call
      let target ← elabRelTarget target
      mkAppWidth mk #[target]
  | `(x64_instr| jmp $target:x64_operand) | `(x64_instr| jmpq $target:x64_operand) =>
    mkRegularInstr (width? := some .W64) do
      let mk := mkConst ``Operation.jmp
      let target ← elabRelTarget target
      mkAppWidth mk #[target]
  | `(x64_instr| nop) =>
    mkClosedInstr (.nop 1)
  | `(x64_instr| nop $sz:num) =>
    mkClosedInstr (.nop sz.getNat)
  | `(x64_instr| $op:x64_jcc_op $lbl:x64_ident) =>
    mkRegularInstr (width? := some .W64) do
      let mk := mkConst ``Operation.jcc
      let cc ← evalCondCodeSuffix op
      let target ← elabIdent lbl
      mkAppWidth mk #[toExpr cc, target]
  | _ => throwError "invalid instruction syntax"
where
  /-- A 64-bit instruction without operands to infer widths from. -/
  mkClosedInstr (op : Operation .W64) : TermElabM Expr :=
    pure (toExpr (Instr.regular .W64 .W64 op))

-- ============================================================================
-- Directive & Program Elaboration
-- ============================================================================

/-- Elaborate an `x64_directive` syntax node into a `Lean.Expr` of type `Directive`. -/
def elabDirective (stx : TSyntax `x64_directive) : TermElabM Expr := withRef stx do
  let word (n : Nat) (c : TSyntax `x64_const) : TermElabM Expr := do
    return mkApp4 (mkConst ``Kraken.Directive.word) (mkConst ``Instr) (mkConst ``ConstExpr)
      (toExpr n) (← elabConstExpr c)
  match stx with
  | `(x64_directive| $lbl:x64_ident : $[;]?) =>
    return mkApp3 (mkConst ``Kraken.Directive.label) (mkConst ``Instr) (mkConst ``ConstExpr) (← elabIdent lbl)
  | `(x64_directive| $ins:x64_instr ;)
  | `(x64_directive| $ins:x64_instr) =>
    return mkApp3 (mkConst ``Kraken.Directive.instr) (mkConst ``Instr) (mkConst ``ConstExpr) (← elabInstr ins)
  | `(x64_directive| .short $c:x64_const $[;]?) => word 2 c
  | `(x64_directive| .long $c:x64_const $[;]?) => word 4 c
  | `(x64_directive| .quad $c:x64_const $[;]?) => word 8 c
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

-- ============================================================================
-- Standalone Embeddings (`⸨instr|`, `⸨operand|`, `⸨mem|`, `⸨reg|`, `⸨const|`)
-- ============================================================================

/-- Elaborate a standalone operand-level embedding via `body`, against the expected type. When
    `widthIndexed`, the result is indexed by an operation width of type `W` (`Reg w`, `AvxReg w`,
    `Operand w`), determined by its registers, by the type of an antiquotation, or else by the expected
    type; if none of these determines it, elaboration fails. -/
def elabEmbedding (W : Type) [ToExpr W] (body : X64ElabM Expr) (expectedType? : Option Expr)
    (widthIndexed := true) : TermElabM Expr := do
  let w ← mkFreshExprMVar (toTypeExpr W)
  let e ← StateRefT'.run' body { operandWidth := w }
  let e ← ensureHasType expectedType? e
  if widthIndexed && (← instantiateMVars w).isMVar then
    throwError "could not infer operand width, consider adding a type ascription"
  instantiateMVars e

end

/-- Inline unquoted X64 assembly directive elaborator (`⸨dir| ... ⸩`). -/
elab_rules : term
  | `(⸨dir| $d:x64_directive⸩) => elabDirective d

macro_rules
  | `(⸨dir $n | $dir:x64_directive⸩) =>
    `({directive := ⸨dir| $dir⸩, size := Kraken.Layout.size _root_.Instr _root_.ConstExpr $n : Kraken.Sized _root_.Directive})

/-- Inline unquoted X64 assembly block elaborator (`⸨prog| ...⸩`). -/
elab_rules : term
  | `(⸨prog| $p:x64_prog⸩) => elabProgram p

/-- Standalone embeddings of the elements of a program:
    * `⸨instr| ... ⸩ : Instr`
    * `⸨operand| ... ⸩ : Operand w`
    * `⸨mem| ... ⸩ : AddrExpr`. An `AddrExpr` only holds 64-bit registers: the address width that the
      registers of a memory operand determine (`0(%eax)` is a 32-bit address) is part of the
      instruction (`Instr.regular`), so it is dropped here, and `⸨mem| 0(%eax) ⸩ = ⸨mem| 0(%rax) ⸩`.
    * `⸨reg| ... ⸩ : Reg w` for general-purpose registers and `AvxReg w` for AVX registers
    * `⸨const| ... ⸩ : ConstExpr`

    Width-indexed results take their width from their registers, from the type of an antiquotation, or
    else from the expected type (`(⸨operand| $1 ⸩ : Operand .W64)`). -/
elab_rules : term <= expectedType?
  | `(⸨instr| $i:x64_instr ⸩) => do ensureHasType expectedType? (← elabInstr i)
  | `(⸨operand| $o:x64_operand ⸩) => elabEmbedding Width (elabOperand o) expectedType?
  | `(⸨mem| $m:x64_mem ⸩) => elabEmbedding Width (elabMem m) expectedType? (widthIndexed := false)
  | `(⸨reg| $r:x64_reg ⸩) => elabEmbedding Width (elabReg r) expectedType?
  | `(⸨reg| $r:x64_avx_reg ⸩) => elabEmbedding AvxWidth (elabAvxReg r) expectedType?
  | `(⸨const| $c:x64_const ⸩) => do ensureHasType expectedType? (← elabConstExpr c)

/-- Read an X64 assembly file, strip assembler directives, parse via `runParserCategory`,
    and elaborate into a Kraken `Program`. -/
elab "include_x64" path:str : term => do
  let content ← IO.FS.readFile path.getString
  withRef path <| elabX64 (stripDirectives content)

end Kraken.X64.Parser
