module

public import Kraken.X64.Parser.Basic
public meta import Kraken.X64.Parser.Basic
public import Kraken.X64.Parser.Syntax
public meta import Kraken.X64.Parser.Syntax
public meta import Lean

namespace Kraken.X64.Parser

open Lean Meta Elab Term Kraken.Parser

public meta section

-- ============================================================================
-- Helper Types
-- ============================================================================

abbrev MaybeOpWidth (T : Width → Type) := Postponable T
abbrev MaybeAvxOpWidth (T : AvxWidth → Type) := Postponable T

abbrev MaybeAddrWidth := Option Width

def toInstr (addr : MaybeAddrWidth) {w : Width} (op : Operation w) : Instr :=
  letI _ : AddressSize := { address_size := addr.getD .W64 }
  ↑op

def toAvxInstr (addr : MaybeAddrWidth) {w : AvxWidth} (op : AvxOperation w) : Instr :=
  letI _ : AddressSize := { address_size := addr.getD .W64 }
  ↑op

-- ============================================================================
-- Constant Expression Elaboration
-- ============================================================================

/-- Elaborate an `x64_const` syntax node into a `ConstExpr`. -/
def elabConstExpr (stx : TSyntax `x64_const) : TermElabM ConstExpr := withRef stx do
  match stx with
  | `(x64_const| $n:num) =>
    let i ← intToInt64Checked (Int.ofNat n.getNat)
    pure (.int64 i)
  | `(x64_const| -$n:num) =>
    let i ← intToInt64Checked (-(Int.ofNat n.getNat))
    pure (.int64 i)
  | `(x64_const| +$n:num) =>
    let i ← intToInt64Checked (Int.ofNat n.getNat)
    pure (.int64 i)
  | `(x64_const| $id:x64_ident + $n:num) =>
    let s ← getAsmIdent id
    let i ← withRef n <| intToInt64Checked (Int.ofNat n.getNat)
    pure (.add (.label s) (.int64 i))
  | `(x64_const| $id:x64_ident - $n:num) =>
    let s ← getAsmIdent id
    let i ← withRef n <| intToInt64Checked (Int.ofNat n.getNat)
    pure (.sub (.label s) (.int64 i))
  | `(x64_const| $id:x64_ident) =>
    let s ← getAsmIdent id
    pure (.label s)
  | _ => throwError "invalid constant expression"

-- ============================================================================
-- Register Elaboration
-- ============================================================================

/-- Elaborate an `x64_reg` syntax node into a general-purpose register `RegW`. -/
def elabRegW (stx : TSyntax `x64_reg) : TermElabM RegW := withRef stx do
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

/-- Elaborate an `x64_avx_reg` syntax node into an AVX vector register `AvxRegW`. -/
def elabAvxRegW (stx : TSyntax `x64_avx_reg) : TermElabM AvxRegW := withRef stx do
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

/-- Elaborate a low register for memory index addressing (rejecting `%ah`/`%bh`/`%ch`/`%dh`). -/
def elabLowReg (stx : TSyntax `x64_reg) : TermElabM (Width × Reg64) := withRef stx do
  let ⟨w, r⟩ ← elabRegW stx
  match r with
  | .low r64 _ => pure (w, r64)
  | _ => throwError "high byte register cannot be used for an addrexpr"

/-- Elaborate a base register for memory addressing (`%rip` or a low GPR). -/
def elabRegOrRip (stx : TSyntax `x64_reg_or_rip) : TermElabM (Width × RegOrRip) := withRef stx do
  match stx with
  | `(x64_reg_or_rip| %rip) => pure (.W64, .rip)
  | `(x64_reg_or_rip| $r:x64_reg) =>
    let (w, reg) ← elabLowReg r
    pure (w, .reg reg)
  | _ => throwError "expected memory base register"

-- ============================================================================
-- Memory & General Operand Elaboration
-- ============================================================================

/-- Elaborate a numeric memory index scale (`1`, `2`, `4`, or `8`) into its corresponding `Width`. -/
def elabScale (stx : TSyntax `num) : TermElabM Width := withRef stx do
  match stx.getNat with
  | 1 => pure .W8
  | 2 => pure .W16
  | 4 => pure .W32
  | 8 => pure .W64
  | s => throwError "invalid scale {s}, must be 1, 2, 4, or 8"

/-- Elaborate an `x64_mem` syntax node into `(address_width, AddrExpr)`. -/
def elabMem (stx : TSyntax `x64_mem) : TermElabM (Width × AddrExpr) := withRef stx do
  match stx with
  | `(x64_mem| $[$disp?:x64_const]?($baseStx:x64_reg_or_rip $[, $idxStx?:x64_reg $[, $scStx?:num]?]?)) =>
    let disp ← (·.getD (.int64 0)) <$> disp?.mapM elabConstExpr
    let (wBase, base) ← elabRegOrRip baseStx
    let idx? ← idxStx?.mapM fun idxStx => do
      let (wIdx, reg) ← elabLowReg idxStx
      if wBase ≠ wIdx then
        throwError "type mismatch in memory addressing operands: base ({wBase}) and index ({wIdx}) have different widths"
      let scale ← (·.getD .W8) <$> scStx?.join.mapM elabScale
      pure ({ reg, scale } : AddrIndex)
    let finalDisp := match base, disp with
      | .rip, .int64 _ => disp
      | .rip, _        => .sub disp .after_current_instruction
      | _, _           => disp
    pure (wBase, { base := some base, idx := idx?, disp := finalDisp })
  | `(x64_mem| $disp:x64_const) =>
    let d ← elabConstExpr disp
    pure (.W64, { base := none, idx := none, disp := d })
  | _ => throwError "invalid memory operand"

/-- Extract symbol name from an antiquotation syntax node (`$sym`). -/
def getAntiquotSym (stx : Syntax) : TermElabM String := withRef stx do
  if stx.isAntiquot then
    match stx.getAntiquotTerm.getId with
    | .str .anonymous s => pure s
    | n =>
      if !n.isAnonymous then pure n.toString
      else throwError "invalid operand"
  else
    throwError "invalid operand"

/-- Elaborate an `x64_imm` (`$const`) into a `ConstExpr`. -/
def elabImmConst (stx : TSyntax `x64_imm) : TermElabM ConstExpr := withRef stx do
  match stx with
  | ⟨.node _ _ #[.atom _ "$", c]⟩ => elabConstExpr ⟨c⟩
  | _ => throwError "invalid immediate operand"

/-- Elaborate an `x64_operand` into a width-polymorphic `Operand`. -/
def elabOperand (stx : TSyntax `x64_operand) : TermElabM (MaybeAddrWidth × MaybeOpWidth Operand) := withRef stx do
  if stx.raw.isAntiquot then
    let s ← getAntiquotSym stx.raw
    let ce : ConstExpr := .label s
    pure (none, .postponed (.imm ce))
  else match stx with
  | `(x64_operand| $r:x64_reg) =>
    let ⟨w, reg⟩ ← elabRegW r
    pure (none, .instantiated w (.reg reg))
  | `(x64_operand| $imm:x64_imm) =>
    let ce ← elabImmConst imm
    pure (none, .postponed (.imm ce))
  | `(x64_operand| $op:x64_operand + $n:num) =>
    let s ← getAntiquotSym op.raw
    let i ← withRef n <| intToInt64Checked (Int.ofNat n.getNat)
    let ce : ConstExpr := .add (.label s) (.int64 i)
    pure (none, .postponed (.imm ce))
  | `(x64_operand| $op:x64_operand - $n:num) =>
    let s ← getAntiquotSym op.raw
    let i ← withRef n <| intToInt64Checked (Int.ofNat n.getNat)
    let ce : ConstExpr := .sub (.label s) (.int64 i)
    pure (none, .postponed (.imm ce))
  | `(x64_operand| $m:x64_mem) =>
    let (w, mem) ← elabMem m
    pure (some w, .postponed (.mem mem))
  | _ => throwError "invalid operand"

/-- Elaborate an `x64_operand` into a width-polymorphic `RegOrMem`. -/
def elabRegOrMem (stx : TSyntax `x64_operand) : TermElabM (MaybeAddrWidth × MaybeOpWidth RegOrMem) := withRef stx do
  if stx.raw.isAntiquot then
    throwError "expected register or memory operand, got $"
  else match stx with
  | `(x64_operand| $r:x64_reg) =>
    let ⟨w, reg⟩ ← elabRegW r
    pure (none, .instantiated w (.reg reg))
  | `(x64_operand| $_:x64_imm)
  | `(x64_operand| $_:x64_operand + $_:num)
  | `(x64_operand| $_:x64_operand - $_:num) =>
    throwError "expected register or memory operand, got $"
  | `(x64_operand| $m:x64_mem) =>
    let (w, mem) ← elabMem m
    pure (some w, .postponed (.mem mem))
  | _ => throwError "expected register or memory operand"

/-- Elaborate an `x64_reg` into a width-tagged `Reg` with no address-width hint. -/
def elabRegA (stx : TSyntax `x64_reg) : TermElabM (MaybeAddrWidth × MaybeOpWidth Reg) := do
  let ⟨w, reg⟩ ← elabRegW stx
  pure (none, .instantiated w reg)

/-- Elaborate an `x64_avx_operand` into a width-polymorphic `AvxRegOrMem`. -/
def elabAvxRegOrMem (stx : TSyntax `x64_avx_operand) : TermElabM (MaybeAddrWidth × MaybeAvxOpWidth AvxRegOrMem) := withRef stx do
  match stx with
  | `(x64_avx_operand| $r:x64_avx_reg) =>
    let ⟨w, reg⟩ ← elabAvxRegW r
    pure (none, .instantiated w (.avx reg))
  | `(x64_avx_operand| $m:x64_mem) =>
    let (w, mem) ← elabMem m
    pure (some w, .postponed (.mem mem))
  | _ => throwError "expected AVX register or memory operand"

/-- Elaborate an `x64_operand` into a relative branch target (`RelRegOrMem`). -/
def elabRelTarget (stx : TSyntax `x64_operand) : TermElabM (MaybeAddrWidth × RelRegOrMem) := withRef stx do
  match stx with
  | `(x64_operand| $r:x64_reg) =>
    let ⟨w, reg⟩ ← elabRegW r
    if h : w = .W64 then
      pure (none, .reg (h ▸ reg))
    else
      throwError "expected a 64-bit register in relative addressing position"
  | `(x64_operand| $m:x64_mem) =>
    match m with
    | `(x64_mem| $c:x64_const) =>
      match c with
      | `(x64_const| $id:x64_ident) =>
        let lbl ← getAsmIdent id
        pure (none, .rel (.sub (.label lbl) .after_current_instruction))
      | _ =>
        throwError "absolute branch targets are not supported"
    | _ =>
      let (w, mem) ← elabMem m
      if mem.base.isNone && mem.idx.isNone then
        throwError "absolute branch targets are not supported"
      pure (some w, .mem mem)
  | _ => throwError "invalid branch target operand"

/-- Elaborate an `x64_shift_count` (`$imm` or `%cl`) into a `ShiftCountExpr`. -/
def elabShiftCount (stx : TSyntax `x64_shift_count) : TermElabM ShiftCountExpr := withRef stx do
  if stx.raw.isAntiquot then
    let s ← getAntiquotSym stx.raw
    pure (.imm8 (.label s))
  else match stx with
  | `(x64_shift_count| %cl) => pure .cl
  | `(x64_shift_count| $imm:x64_imm) => return .imm8 (← elabImmConst imm)
  | _ => throwError "expected immediate or %cl shift count"

-- ============================================================================
-- Width Unification Helpers
-- ============================================================================

def mergeAddrM (w1 w2 : MaybeAddrWidth) : TermElabM MaybeAddrWidth :=
  match w1, w2 with
  | none, none => pure none
  | some w, none | none, some w => pure (some w)
  | some _, some _ => throwError "can't have two memory operands"

-- ============================================================================
-- Mnemonic Category & Suffix Elaborators
-- ============================================================================

/-- Elaborate the operand-width suffix of a mnemonic (`""`, `"b"`, `"w"`, `"l"`, `"q"`). -/
def elabWidthSfx (stx : Syntax) : TermElabM (Option Width) := withRef stx do
  let (_, sfx) ← splitSuffixed stx
  match sfx with
  | ""  => pure none
  | "b" => pure (some .W8)
  | "w" => pure (some .W16)
  | "l" => pure (some .W32)
  | "q" => pure (some .W64)
  | _   => throwError "invalid operand width suffix '{sfx}'"

/-- Elaborate the condition-code suffix of a mnemonic (`cmov<cc>`, `set<cc>`, `j<cc>`). -/
def elabCondCodeSfx (stx : Syntax) : TermElabM CondCode := withRef stx do
  let (_, sfx) ← splitSuffixed stx
  match sfx with
  | "z"  | "e"          => pure .z
  | "nz" | "ne"         => pure .nz
  | "b"  | "c"  | "nae" => pure .b
  | "ae" | "nc" | "nb"  => pure .ae
  | "a"  | "nbe"        => pure .a
  | "be" | "na"         => pure .be
  | "l"  | "nge"        => pure .l
  | "le" | "ng"         => pure .le
  | _                   => throwError "invalid condition code '{sfx}'"

/-- Elaborate an `x64_bin_op` into `(Option Width, constructor)`. -/
def elabBinOp (stx : TSyntax `x64_bin_op) :
    TermElabM (Option Width × ({w : Width} → RegOrMem w → Operand w → Operation w)) := withRef stx do
  let (stem, _) ← splitSuffixed stx
  let w ← elabWidthSfx stx
  let op ← match stem with
    | "add"            => pure .add
    | "adc"            => pure .adc
    | "sub"            => pure .sub
    | "sbb"            => pure .sbb
    | "mov" | "movabs" => pure .mov
    | "xor"            => pure .xor
    | "and"            => pure .and
    | "or"             => pure .or
    | "cmp"            => pure .cmp
    | "test"           => pure .test
    | _                => throwError "invalid binary instruction mnemonic '{stem}'"
  pure (w, op)

/-- Elaborate an `x64_rm_reg_op` into `(Option Width, constructor)`. -/
def elabRmRegOp (stx : TSyntax `x64_rm_reg_op) :
    TermElabM (Option Width × ({w : Width} → Reg w → RegOrMem w → Operation w)) := withRef stx do
  let (stem, _) ← splitSuffixed stx
  let w ← elabWidthSfx stx
  let op ← match stem with
    | "adcx" => pure .adcx
    | "adox" => pure .adox
    | _      => throwError "invalid carry-chain mnemonic '{stem}'"
  pure (w, op)

/-- Elaborate an `x64_unary_op` into `(Option Width, constructor)`. -/
def elabUnaryOp (stx : TSyntax `x64_unary_op) :
    TermElabM (Option Width × ({w : Width} → RegOrMem w → Operation w)) := withRef stx do
  let (stem, _) ← splitSuffixed stx
  let w ← elabWidthSfx stx
  let op ← match stem with
    | "mul" => pure .mul
    | "neg" => pure .neg
    | "dec" => pure .dec
    | "inc" => pure .inc
    | "not" => pure .not
    | _     => throwError "invalid unary instruction mnemonic '{stem}'"
  pure (w, op)

/-- Elaborate an `x64_ext_mov_op` into `((srcWidth, dstWidth), constructor)`. -/
def elabExtMovOp (stx : TSyntax `x64_ext_mov_op) :
    TermElabM ((Width × Width) × ({w1 w2 : Width} → RegOrMem w1 → RegOrMem w2 → Operation w1)) := withRef stx do
  let (stem, sfx) ← splitSuffixed stx
  let op ← match stem with
    | "movs" => pure .movsx
    | "movz" => pure .movzx
    | _      => throwError "invalid extending move mnemonic '{stem}'"
  let ws ← match sfx with
    | "bw"        => pure (.W8,  .W16)
    | "bl"        => pure (.W8,  .W32)
    | "bq"        => pure (.W8,  .W64)
    | "wl"        => pure (.W16, .W32)
    | "wq"        => pure (.W16, .W64)
    | "lq" | "xd" => pure (.W32, .W64)
    | _           => throwError "invalid extension width suffix '{sfx}'"
  pure (ws, op)

/-- Elaborate an `x64_avx_op` into its `AvxOperation` constructor. -/
def elabAvxOp (stx : TSyntax `x64_avx_op) :
    TermElabM ({w : AvxWidth} → AvxRegOrMem w → AvxRegOrMem w → AvxOperation w) := withRef stx do
  let (stem, sfx) ← splitSuffixed stx
  match stem, sfx with
  | "movu",  "ps" => pure .movups
  | "vmovu", "ps" => pure .vmovups
  | "mova",  "ps" => pure .movaps
  | "add",   "ps" => pure .addps
  | "sub",   "ps" => pure .subps
  | _, _          => throwError "invalid AVX mnemonic"

/-- Elaborate an `x64_shift_op` into `(Option Width, constructor)`. -/
def elabShiftOp (stx : TSyntax `x64_shift_op) :
    TermElabM (Option Width × ({w : Width} → RegOrMem w → ShiftCountExpr → Operation w)) := withRef stx do
  let (stem, _) ← splitSuffixed stx
  let w ← elabWidthSfx stx
  let op ← match stem with
    | "shl" | "sal" => pure .shl
    | "shr"         => pure .shr
    | "sar"         => pure .sar
    | "rol"         => pure .rol
    | "ror"         => pure .ror
    | "rcl"         => pure .rcl
    | "rcr"         => pure .rcr
    | _             => throwError "invalid shift/rotate mnemonic '{stem}'"
  pure (w, op)

/-- Elaborate an `x64_shd_op` into `(Option Width, constructor)`. -/
def elabShdOp (stx : TSyntax `x64_shd_op) :
    TermElabM (Option Width × ({w : Width} → RegOrMem w → Reg w → ShiftCountExpr → Operation w)) := withRef stx do
  let (stem, _) ← splitSuffixed stx
  let w ← elabWidthSfx stx
  let op ← match stem with
    | "shld" => pure .shld
    | "shrd" => pure .shrd
    | _      => throwError "invalid double-precision shift mnemonic '{stem}'"
  pure (w, op)

-- ============================================================================
-- Instruction Family & Statement Elaboration
-- ============================================================================

/-- Elaborate three-operand AT&T instructions (`op src1, src2, dst`). -/
def elabTernaryInstr {k1 k2 k3 : SyntaxNodeKinds} {T1 T2 T3 : Width → Type}
    (opW : Option Width) (op1 : TSyntax k1) (op2 : TSyntax k2) (op3 : TSyntax k3)
    (e1 : TSyntax k1 → TermElabM (MaybeAddrWidth × MaybeOpWidth T1))
    (e2 : TSyntax k2 → TermElabM (MaybeAddrWidth × MaybeOpWidth T2))
    (e3 : TSyntax k3 → TermElabM (MaybeAddrWidth × MaybeOpWidth T3))
    (mk : {w : Width} → T3 w → T2 w → T1 w → Operation w) : TermElabM Instr := do
  let (aw1, v1) ← e1 op1
  let (aw2, v2) ← e2 op2
  let (aw3, v3) ← e3 op3
  let aw ← mergeAddrM (← mergeAddrM aw1 aw2) aw3
  let ⟨_, (s1, s2), d3⟩ ← (← (← (← opW.syncM v1 op1).syncM v2 op2).syncM v3 op3).getM
  pure (toInstr aw (mk d3 s2 s1))

/-- Elaborate two-operand AT&T instructions (`op src, dst`). -/
def elabBinaryInstr {k1 k2 : SyntaxNodeKinds} {T1 T2 : Width → Type}
    (opW : Option Width) (op1 : TSyntax k1) (op2 : TSyntax k2)
    (e1 : TSyntax k1 → TermElabM (MaybeAddrWidth × MaybeOpWidth T1))
    (e2 : TSyntax k2 → TermElabM (MaybeAddrWidth × MaybeOpWidth T2))
    (mk : {w : Width} → T2 w → T1 w → Operation w) : TermElabM Instr := do
  let (aw1, v1) ← e1 op1
  let (aw2, v2) ← e2 op2
  let aw ← mergeAddrM aw1 aw2
  let ⟨_, s1, d2⟩ ← (← (← opW.syncM v1 op1).syncM v2 op2).getM
  pure (toInstr aw (mk d2 s1))

/-- Elaborate two-operand AVX instructions (`op src, dst`). -/
def elabAvxBinaryInstr (op1 op2 : TSyntax `x64_avx_operand)
    (mk : {w : AvxWidth} → AvxRegOrMem w → AvxRegOrMem w → AvxOperation w) : TermElabM Instr := do
  let (aw1, v1) ← elabAvxRegOrMem op1
  let (aw2, v2) ← elabAvxRegOrMem op2
  let aw ← mergeAddrM aw1 aw2
  let ⟨_, s1, d2⟩ ← (← v1.syncM v2 op2).getM
  pure (toAvxInstr aw (mk d2 s1))

/-- Elaborate one-operand AT&T instructions (`op dst`). -/
def elabUnaryInstr (opW : Option Width) (op1 : TSyntax `x64_operand)
    (mk : {w : Width} → RegOrMem w → Operation w) : TermElabM Instr := withRef op1 do
  let (aw, v) ← elabRegOrMem op1
  let ⟨_, d⟩ ← (← opW.syncM v op1).getM
  pure (toInstr aw (mk d))

/-- Elaborate a concrete `x64_instr` syntax node into a `Lean.Expr` of type `Instr`. -/
def elabInstr (stx : TSyntax `x64_instr) : TermElabM Expr := withRef stx do
  match stx with
  | `(x64_instr| ${ $t:term }) => elabTerm t (some (mkConst ``Instr))
  | _ =>
    let instr : Instr ← match stx with
      | `(x64_instr| .align $align:num $[, $pad?:num]?) =>
        pure (toInstr none (w := .W64) (.nopalign align.getNat (pad?.map (·.getNat))))
      | `(x64_instr| $op:x64_bin_op $src:x64_operand, $dst:x64_operand) =>
        let (opW, mk) ← elabBinOp op
        elabBinaryInstr opW src dst elabOperand elabRegOrMem mk
      | `(x64_instr| $op:x64_rm_reg_op $src:x64_operand, $dst:x64_reg) =>
        let (opW, mk) ← elabRmRegOp op
        elabBinaryInstr opW src dst elabRegOrMem elabRegA mk
      | `(x64_instr| $op:x64_cmov_op $src:x64_operand, $dst:x64_reg) =>
        let cc ← elabCondCodeSfx op
        elabBinaryInstr none src dst elabRegOrMem elabRegA (.cmovcc cc)
      | `(x64_instr| $op:x64_unary_op $dst:x64_operand) =>
        let (opW, mk) ← elabUnaryOp op
        elabUnaryInstr opW dst mk
      | `(x64_instr| $op:x64_set_op $dst:x64_operand) =>
        let cc ← elabCondCodeSfx op
        elabUnaryInstr (some .W8) dst (.setcc cc)
      | `(x64_instr| $op:x64_imul_op $src:x64_operand) =>
        let opW ← elabWidthSfx op
        elabUnaryInstr opW src .imul1
      | `(x64_instr| $op:x64_imul_op $src:x64_operand, $dst:x64_operand) =>
        let opW ← elabWidthSfx op
        elabBinaryInstr opW src dst elabOperand elabRegOrMem (.imul none)
      | `(x64_instr| $op:x64_imul_op $op1:x64_operand, $op2:x64_operand, $r3:x64_reg) =>
        let opW ← elabWidthSfx op
        elabTernaryInstr opW op1 op2 r3 elabOperand elabRegOrMem elabRegA
          fun dst s2 s1 => .imul (some (.reg dst)) s2 s1
      | `(x64_instr| $op:x64_mulx_op $srcOp:x64_operand, $rLo:x64_reg, $rHi:x64_reg) =>
        let opW ← elabWidthSfx op
        elabTernaryInstr opW srcOp rLo rHi elabRegOrMem elabRegA elabRegA .mulx
      | `(x64_instr| movsx $r1:x64_reg, $r2:x64_reg) =>
        let ⟨_, src⟩ ← elabRegW r1
        let ⟨_, dst⟩ ← elabRegW r2
        pure (toInstr none (.movsx (.reg dst) (.reg src)))
      | `(x64_instr| movzx $r1:x64_reg, $r2:x64_reg) =>
        let ⟨_, src⟩ ← elabRegW r1
        let ⟨_, dst⟩ ← elabRegW r2
        pure (toInstr none (.movzx (.reg dst) (.reg src)))
      | `(x64_instr| $op:x64_ext_mov_op $srcOp:x64_operand, $dstReg:x64_reg) =>
        let ((wSrc, wDst), mk) ← elabExtMovOp op
        let (aw, vSrc) ← elabRegOrMem srcOp
        let (_, vDst) ← elabRegA dstReg
        let src ← withRef srcOp <| vSrc.instantiateM wSrc
        let dst ← withRef dstReg <| vDst.instantiateM wDst
        pure (toInstr aw (mk (.reg dst) src))
      | `(x64_instr| $op:x64_lea_op $m:x64_mem, $r:x64_reg) =>
        let opW ← elabWidthSfx op
        let (addrW, src) ← elabMem m
        let (_, vDst) ← elabRegA r
        let ⟨_, dst⟩ ← withRef r (← opW.syncM vDst r).getM
        pure (toInstr (some addrW) (.lea dst src))
      | `(x64_instr| $op:x64_avx_op $src:x64_avx_operand, $dst:x64_avx_operand) =>
        let mk ← elabAvxOp op
        elabAvxBinaryInstr src dst mk
      | `(x64_instr| $op:x64_shift_op $dst:x64_operand) =>
        let (opW, mk) ← elabShiftOp op
        elabUnaryInstr opW dst fun d => mk d (.imm8 (.int64 1))
      | `(x64_instr| $op:x64_shift_op $cntStx:x64_shift_count, $dst:x64_operand) =>
        let (opW, mk) ← elabShiftOp op
        let cnt ← elabShiftCount cntStx
        elabUnaryInstr opW dst fun d => mk d cnt
      | `(x64_instr| $op:x64_shd_op $cntStx:x64_shift_count, $src:x64_reg, $dst:x64_operand) =>
        let (opW, mk) ← elabShdOp op
        let cnt ← elabShiftCount cntStx
        elabBinaryInstr opW src dst elabRegA elabRegOrMem fun d s => mk d s cnt
      | `(x64_instr| $op:x64_bswap_op $r:x64_reg) =>
        let opW ← elabWidthSfx op
        let (_, vDst) ← elabRegA r
        let ⟨_, dst⟩ ← withRef r (← opW.syncM vDst r).getM
        pure (toInstr none (.bswap dst))
      | `(x64_instr| $op:x64_push_op $srcOp:x64_operand) =>
        let opW ← elabWidthSfx op
        let (aw, v) ← elabOperand srcOp
        let ⟨_, src⟩ := (← opW.syncM v srcOp).getD .W64
        pure (toInstr aw (.push src))
      | `(x64_instr| $op:x64_pop_op $dstOp:x64_operand) =>
        let opW ← elabWidthSfx op
        let (aw, v) ← elabRegOrMem dstOp
        let ⟨_, dst⟩ := (← opW.syncM v dstOp).getD .W64
        pure (toInstr aw (.pop dst))
      | `(x64_instr| ret) | `(x64_instr| retq) =>
        pure (toInstr none (w := .W64) .ret)
      | `(x64_instr| call $op1:x64_operand) | `(x64_instr| callq $op1:x64_operand) =>
        let (aw, target) ← elabRelTarget op1
        pure (toInstr aw (w := .W64) (.call target))
      | `(x64_instr| jmp $op1:x64_operand) | `(x64_instr| jmpq $op1:x64_operand) =>
        let (aw, target) ← elabRelTarget op1
        pure (toInstr aw (w := .W64) (.jmp target))
      | `(x64_instr| nop) =>
        pure (toInstr none (w := .W64) (.nop 1))
      | `(x64_instr| nop $sz:num) =>
        pure (toInstr none (w := .W64) (.nop sz.getNat))
      | `(x64_instr| $op:x64_jcc_op $lbl:x64_ident) =>
        let cc ← elabCondCodeSfx op
        let target ← getAsmIdent lbl
        pure (toInstr none (w := .W64) (.jcc cc target))
      | _ => throwError "invalid instruction syntax"
    pure (Lean.toExpr instr)

-- ============================================================================
-- Directive & Program Elaboration
-- ============================================================================

/-- Elaborate an `x64_directive` syntax node into a `Lean.Expr` of type `Directive`. -/
def elabDirective (stx : TSyntax `x64_directive) : TermElabM Expr := withRef stx do
  match stx with
  | `(x64_directive| $lbl:x64_ident :)
  | `(x64_directive| $lbl:x64_ident : ;) =>
    let name ← getAsmIdent lbl
    pure (Lean.toExpr (Directive.label name))
  | `(x64_directive| $ins:x64_instr ;)
  | `(x64_directive| $ins:x64_instr) =>
    let insExpr ← elabInstr ins
    mkAppM ``Directive.instr #[insExpr]
  | `(x64_directive| ${ $t:term } ;)
  | `(x64_directive| ${ $t:term }) =>
    elabTerm t (some (mkConst ``Directive))
  | _ => throwError "invalid assembly directive"

/-- Elaborate an `x64_prog` syntax node into a `Lean.Expr` of type `Program` (`List Directive`). -/
def elabProgram (stx : TSyntax `x64_prog) : TermElabM Expr := withRef stx do
  match stx with
  | `(x64_prog| $dirs:x64_directive*) =>
    let dirExprs ← dirs.mapM elabDirective
    mkListLit (mkConst ``Directive) dirExprs.toList
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
