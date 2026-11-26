module

public import LeanQbe.T.Amd64.VllX64
public import LeanQbe.T.Vll.Syntax
public import LeanQbe.T.Amd64.Isel

/-!
# Context-Free 1:1 x86-64 Assembler (`Amd64.VllAsmX64`)

Pure, deterministic, context-free 1:1 lowering `asmX64 : Instr x64Arch → List _root_.Directive`,
plus `asmX64List`, `asmX64Block`, and `asmX64Prog`:
* Shares exact directives with `Amd64/Frame.lean` (`x64Prologue`, `x64Epilogue`, `x64SlotSt`,
  `x64SlotLd`, `x64CanonAbi`, `x64SymAddr`, `x64CallReg`, `x64JmpReg`, `x64Frame`) and
  `Amd64/Isel.lean` (`x64Gpr`, `x64Load`, `x64LoadSext`, `x64Store`, `x64JnzGpr`, `cmpDirectIns`,
  `testDirectIns`, `aluBinI`, `opBinLeaImm?`, `opBinLeaReg?`).
* Respects `writeSubX64` (`movb`/`movw` preserve upper bits on `w8`/`w16`, `movl` zero-extends
  on `w32`, `movq` writes 64 bits) and emits exact status flags when `setFlags = true`.
* Passes through `.native d` as `[d]`, zero `*Lemmas*` imports, zero Arm64/AArch64 imports.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Amd64

open LeanQbe.T
open LeanQbe.T.Vll

/-! ## 1. Operand and Sub-Word Helpers -/

/-- Convert a VLL `Src x64Arch` operand to a `PArg` at width `w`. -/
@[expose] def srcToPArg (w : _root_.Width) :
    Src x64Arch → PArg Reg64 RegMm CondCode (.bits w.bits)
  | .reg r => .gpr r
  | .imm c => .imm (c.setWidth w.bits)

/-- Width-faithful move instruction writing via `writeSubX64` (`movb`/`movw`/`movl`/`movq`). -/
@[expose] def movSubWI (w : _root_.Width) (rd rs : Reg64) : _root_.Instr :=
  x64InsI w (.mov (.reg (regW w rd)) (.reg (regW w rs)))

/-- Two-address binary core for `k ∈ {add, sub, and, or, xor}` or `mul` at `w ∈ {W16, W32, W64}`,
preserving upper bits on sub-word writes and setting exact `sub` flags on `rs == rd`. -/
@[expose] def asmX64BinCoreIns (w : _root_.Width) (k : AluBinKind) (rd lhs : Reg64)
    (rhs : Src x64Arch) : List _root_.Instr :=
  match rhs with
  | .reg rs =>
    if lhs == rd then [aluBinI w k rd (.reg (regW w rs))]
    else if k.isComm && rs == rd then [aluBinI w k rd (.reg (regW w lhs))]
    else if rs != rd then [movSubWI w rd lhs, aluBinI w k rd (.reg (regW w rs))]
    else [movSubWI w .r11 lhs, aluBinI w k .r11 (.reg (regW w rs)), movSubWI w rd .r11]
  | .imm imm =>
    let c := imm.setWidth w.bits
    let pre := if lhs == rd then [] else [movSubWI w rd lhs]
    if w != .W64 || fitsImm32 (c.setWidth 64) then
      pre ++ [aluBinI w k rd (immBitsOp w c)]
    else
      [moviI .r10 (c.setWidth 64)] ++ pre ++ [aluBinI w k rd (.reg (regW w .r10))]

/-- Lower `.add`/`.sub`/`.and`/`.or`/`.xor`, optionally using 3-op `lea` when `sf = false`. -/
@[expose] def asmX64AluBinIns (w : _root_.Width) (k : AluBinKind) (rd lhs : Reg64)
    (rhs : Src x64Arch) (sf : Bool) : List _root_.Instr :=
  let leaOpt : Option (List _root_.Instr) :=
    if sf then none
    else match rhs with
      | .reg rs => (opBinLeaReg? w k lhs rs rd).map Prod.fst
      | .imm imm => (opBinLeaImm? w k lhs (imm.setWidth w.bits) rd).map Prod.fst
  match leaOpt with
  | some insns => insns
  | none => asmX64BinCoreIns w k rd lhs rhs

/-- Lower `.mul` across `{8, 16, 32, 64}` bits, merging low byte for `.W8` via `.r11`. -/
@[expose] def asmX64AluMulIns (w : _root_.Width) (rd lhs : Reg64) (rhs : Src x64Arch)
    (sf : Bool) : List _root_.Instr :=
  let core : List _root_.Instr :=
    match w with
    | .W8 =>
      match rhs with
      | .reg rs =>
        [movWI .W32 .r11 lhs, aluBinI .W32 .mul .r11 (.reg (d rs)), movSubWI .W8 rd .r11]
      | .imm imm =>
        let c := (imm.setWidth 8).setWidth 32
        [movWI .W32 .r11 lhs, aluBinI .W32 .mul .r11 (immBitsOp .W32 c), movSubWI .W8 rd .r11]
    | _ => asmX64BinCoreIns w .mul rd lhs rhs
  if sf then core ++ [x64InsI w (.test (.reg (regW w rd)) (.reg (regW w rd)))] else core

/-- Map `ShiftKind` for `.shl`/`.lshr`/`.ashr` to BMI2 3-operand instruction constructor. -/
@[expose] def asmX64Bmi2Op (sk : ShiftKind) {w : _root_.Width} :
    Reg w → RegOrMem w → Reg w → Operation w :=
  match sk with
  | .shl => .shlx
  | .lshr => .shrx
  | _ => .sarx

/-- Lower `.shl`/`.lshr`/`.ashr` across `{8, 16, 32, 64}` bits, appending `test` if `sf = true`. -/
@[expose] def asmX64AluShiftIns (w : _root_.Width) (sk : ShiftKind) (rd lhs : Reg64)
    (rhs : Src x64Arch) (sf : Bool) : List _root_.Instr :=
  let core : List _root_.Instr :=
    match rhs with
    | .imm imm =>
      let cnt := imm.toNat % w.bits
      let pre := if lhs == rd && (cnt != 0 || w != .W32) then [] else [movSubWI w rd lhs]
      if cnt == 0 then pre
      else pre ++ [x64InsI w (sk.toOp (.reg (regW w rd)) (.imm8 (.int64 (Int64.ofNat cnt))))]
    | .reg rb =>
      if w == .W32 || w == .W64 then
        [x64InsI w (asmX64Bmi2Op sk (regW w rd) (.reg (regW w lhs)) (regW w rb))]
      else
        let mvRcx := if rb == .rcx then [] else [movI .rcx rb]
        [movSubWI w .r11 lhs, movI .r10 .rcx] ++ mvRcx ++ shiftMaskRcxIns w ++
          [x64InsI w (sk.toOp (.reg (regW w .r11)) .cl), movI .rcx .r10, movSubWI w rd .r11]
  if sf then core ++ [x64InsI w (.test (.reg (regW w rd)) (.reg (regW w rd)))] else core

/-- Assemble `CoreAlu` instruction into raw Kraken `Instr` list. -/
@[expose] def asmX64AluIns (op : CoreAlu) (w : _root_.Width) (rd lhs : Reg64)
    (rhs : Src x64Arch) (sf : Bool) : List _root_.Instr :=
  match op with
  | .add  => asmX64AluBinIns w .add rd lhs rhs sf
  | .sub  => asmX64AluBinIns w .sub rd lhs rhs sf
  | .and  => asmX64AluBinIns w .and rd lhs rhs sf
  | .or   => asmX64AluBinIns w .or  rd lhs rhs sf
  | .xor  => asmX64AluBinIns w .xor rd lhs rhs sf
  | .mul  => asmX64AluMulIns w rd lhs rhs sf
  | .shl  => asmX64AluShiftIns w .shl  rd lhs rhs sf
  | .lshr => asmX64AluShiftIns w .lshr rd lhs rhs sf
  | .ashr => asmX64AluShiftIns w .ashr rd lhs rhs sf

/-! ## 2. Context-Free 1:1 Assembler `asmX64`, `asmX64List`, `asmX64Block`, `asmX64Prog` -/

/-- Assemble one `BedrockMach` L1 instruction `Instr x64Arch` to Kraken `x64` directives 1:1. -/
@[expose] def asmX64 : Instr x64Arch → List _root_.Directive
  | .label s => [.label s]
  | .mov w rd rs => emitClean [movSubWI w.toX64 rd rs]
  | .movi rd imm => [moviD rd imm]
  | .alu op w rd lhs rhs sf => emitClean (asmX64AluIns op w.toX64 rd lhs rhs sf)
  | .cmp w lhs rhs =>
    let xw := w.toX64
    emitClean ((cmpDirectIns xw (.gpr lhs) (srcToPArg xw rhs)).getD [])
  | .test w lhs rhs =>
    let xw := w.toX64
    emitClean ((testDirectIns xw (.gpr lhs) (srcToPArg xw rhs)).getD [])
  | .clearFlags => x64Gpr.clearFlags
  | .setcc rd cc => setccOnly rd cc
  | .load w ext rd addr =>
    match ext with
    | .zx => ((x64Load w.toTy rd addr).map Prod.fst).getD []
    | .sx =>
      match w with
      | .w64 => ((x64Load (.bits 64) rd addr).map Prod.fst).getD []
      | _    => ((x64LoadSext w.bits 64 rd addr).map Prod.fst).getD []
    | .sub =>
      match w with
      | .w8 | .w16 =>
        if !x64AddrValid addr then []
        else
          let xw := w.toX64
          let ae := addrToExpr addr
          ae.1 ++ [insW xw (.mov (.reg (regW xw rd)) (.mem ae.2.1))]
      | .w32 | .w64 => ((x64Load w.toTy rd addr).map Prod.fst).getD []
  | .store w rs addr => ((x64Store w.toTy (.gpr rs) addr).map Prod.fst).getD []
  | .slotSt i rs => x64SlotSt i rs
  | .slotLd rd i => x64SlotLd rd i
  | .prologue ns => (x64Prologue ns).1
  | .epilogue ns => (x64Epilogue ns).1
  | .canonAbi t r => (x64CanonAbi t r).1
  | .jmp l => x64Gpr.jmp l
  | .jcc cc l => x64Gpr.jcc cc l
  | .jnzGpr r l => (x64JnzGpr r false l).1
  | .call sym => x64Frame.call sym
  | .icall r => x64CallReg r
  | .ret => x64Frame.ret
  | .exitJmp sym => x64Frame.exitJmp sym
  | .tailJmpR r => x64JmpReg r
  | .symAddr sym rd => x64SymAddr sym rd
  | .ijmp r => x64JmpReg r
  | .pad _ => [ins (.nop 1)]
  | .native d => [d]

/-- Assemble a flat list of `BedrockMach` L1 instructions (`is.flatMap asmX64`). -/
@[expose] def asmX64List (is : List (Instr x64Arch)) : List _root_.Directive :=
  is.flatMap asmX64

/-- Assemble a `Block x64Arch` given optional fall-through successor label. -/
@[expose] def asmX64Block (nextLabel? : Option Sym) (b : Block x64Arch) : List _root_.Directive :=
  asmX64List (b.toInstrs nextLabel?)

/-- Assemble a complete `VllCodeMap x64Arch` program into Kraken `x64` directives. -/
@[expose] def asmX64Prog (cm : VllCodeMap x64Arch) : List _root_.Directive :=
  asmX64List cm.flatten

end LeanQbe.T.Amd64
