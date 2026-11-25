module

public import LeanQbe.T.Vll.Syntax
public import LeanQbe.T.Vll.Arm64

/-!
# Context-Free 1:1 AArch64 Assembler (`Vll.AsmArm64`)

Pure, computable, context-free assembler `asmArm64 : Instr arm64Arch → List Directive` lowering
every `BedrockMach` L1 `Instr arm64Arch` instruction to Kraken AArch64 directives with zero
`Amd64`, `Kraken.X64`, or `*Lemmas*` imports:

* `.native d ↦ [d]` (exact 1:1 pass-through).
* Core moves, 64-bit immediates, ALU (all 9 `CoreAlu` ops × 4 widths × `setFlags`), `cmp`, `test`,
  `clearFlags`, `setcc`, `load` (`zx`/`sx`/`sub`), `store`, `slotSt`, `slotLd`, `prologue`,
  `epilogue`, `canonAbi`, `jmp`, `jcc`, `jnzGpr` (low-byte `uxtb + cbnz`, flag-preserving),
  `call`, `icall`, `ret`, `exitJmp`, `tailJmpR`, `symAddr` (`adrp + add :lo12:`), `ijmp`, and
  `pad` (`nop`).
* Program flattening (`asmArm64List`, `asmArm64CodeMap`), label-index map `ρ` (`asmArm64Offset`),
  and assembly-simulation side conditions (`arm64InstrStaticOk`, `arm64InstrOk`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Vll

open LeanQbe.T
open LeanQbe.T.Arm64

/-! ## 1. Width & Operand Lowering Helpers -/

/-- AArch64 architectural register width corresponding to a VLL `Width` (`W64` for 64-bit, `W32`
for 8/16/32-bit). -/
@[expose, reducible] def widthToRegWidth : Width → RegWidth
  | .w64 => .W64
  | _ => .W32

/-- Materialize GPR-or-SP register `r` into an `XReg` (copying `.SP` into `tmp`). -/
@[expose] def armSrcToXIns (tmp : XReg) : Arm64.Reg → List _root_.Instr × XReg
  | .reg x => ([], x)
  | .SP => ([armIselMovToXI tmp .SP], tmp)

/-- Materialize `Src arm64Arch` at width `w` into an `XReg` using scratch `tmp` if needed. -/
@[expose] def armRhsToXIns (tmp : XReg) (w : Width) :
    Src arm64Arch → List _root_.Instr × XReg
  | .reg (.reg x) => ([], x)
  | .reg .SP => ([armIselMovToXI tmp .SP], tmp)
  | .imm v => (armMovImmI tmp ((v.setWidth w.bits).setWidth 64), tmp)

/-! ## 2. Moves, ALU, `cmp`, and `test` Builders -/

/-- Lower `.mov w rd rs` preserving `writeSubZeroExtend` semantics for all `w`, `rd`, `rs`. -/
@[expose] def asmMovIns (w : Width) (rd rs : Arm64.Reg) : List _root_.Instr :=
  match w with
  | .w64 => armMovIns rd rs
  | .w32 =>
    let op32 (d x : XReg) : _root_.Instr :=
      armIselInsI (.ORR_s (zr d .W32) (xzr .W32) (sh x))
    match rd, rs with
    | .reg d, .reg x => [op32 d x]
    | .reg d, .SP => [armIselMovToXI d .SP, op32 d d]
    | .SP, .reg x => [op32 .X16 x, armIselMovToSpI .X16]
    | .SP, .SP => [armIselMovToXI .X16 .SP, op32 .X16 .X16, armIselMovToSpI .X16]
  | .w8 | .w16 =>
    let imms := w.bits - 1
    let opSub (d x : XReg) : _root_.Instr :=
      armIselInsI (.UBFM (zr d .W64) (zr x .W64) 0 imms)
    match rd, rs with
    | .reg d, .reg x => [opSub d x]
    | .reg d, .SP => [armIselMovToXI d .SP, opSub d d]
    | .SP, .reg x => [opSub .X16 x, armIselMovToSpI .X16]
    | .SP, .SP => [armIselMovToXI .X16 .SP, opSub .X16 .X16, armIselMovToSpI .X16]

/-- Single-instruction 32/64-bit register-register ALU core (without trailing flag test). -/
@[expose] def asmAluWideRegI (op : CoreAlu) (rw : RegWidth) (sf : Bool) (d ra rb : XReg) :
    _root_.Instr :=
  match op with
  | .add =>
    if sf then armIselInsI (.ADDS_s (zr d rw) (zr ra rw) (sh rb))
    else armIselInsI (.ADD_s (zr d rw) (zr ra rw) (sh rb))
  | .sub =>
    if sf then armIselInsI (.SUBS_s (zr d rw) (zr ra rw) (sh rb))
    else armIselInsI (.SUB_s (zr d rw) (zr ra rw) (sh rb))
  | .and =>
    if sf then armIselInsI (.ANDS_s (zr d rw) (zr ra rw) (sh rb))
    else armIselInsI (.AND_s (zr d rw) (zr ra rw) (sh rb))
  | .or => armIselInsI (.ORR_s (zr d rw) (zr ra rw) (sh rb))
  | .xor => armIselInsI (.EOR_s (zr d rw) (zr ra rw) (sh rb))
  | .shl => armIselInsI (.LSLV (zr d rw) (zr ra rw) (zr rb rw))
  | .lshr => armIselInsI (.LSRV (zr d rw) (zr ra rw) (zr rb rw))
  | .ashr => armIselInsI (.ASRV (zr d rw) (zr ra rw) (zr rb rw))
  | .mul => armIselInsI (.MADD (zr d rw) (zr ra rw) (zr rb rw) (xzr rw))

/-- Non-flag-setting sub-word (`w8`/`w16`) register-register ALU core, producing exact
zero-extended 64-bit output in `d`. Assumes `ra ≠ .X17` and `rb ≠ .X16`. -/
@[expose] def asmAluSubNoFlagsIns (op : CoreAlu) (n : Nat) (d ra rb : XReg) :
    List _root_.Instr :=
  let maskRes : _root_.Instr := armIselInsI (.UBFM (zr d .W64) (zr d .W64) 0 (n - 1))
  let maskSh : _root_.Instr :=
    armIselInsI (.AND_i (.low (.reg .X17) .W32) (zr rb .W32) (armShiftMaskConst n))
  match op with
  | .add => [armIselInsI (.ADD_s (zr d .W32) (zr ra .W32) (sh rb)), maskRes]
  | .sub => [armIselInsI (.SUB_s (zr d .W32) (zr ra .W32) (sh rb)), maskRes]
  | .and => [armIselInsI (.AND_s (zr d .W32) (zr ra .W32) (sh rb)), maskRes]
  | .or => [armIselInsI (.ORR_s (zr d .W32) (zr ra .W32) (sh rb)), maskRes]
  | .xor => [armIselInsI (.EOR_s (zr d .W32) (zr ra .W32) (sh rb)), maskRes]
  | .mul => [armIselInsI (.MADD (zr d .W32) (zr ra .W32) (zr rb .W32) (xzr .W32)), maskRes]
  | .shl => [maskSh, armIselInsI (.LSLV (zr d .W32) (zr ra .W32) (zr .X17 .W32)), maskRes]
  | .lshr =>
    [armExt32I false n .X16 ra, maskSh,
     armIselInsI (.LSRV (zr d .W32) (zr .X16 .W32) (zr .X17 .W32))]
  | .ashr =>
    [armExt32I true n .X16 ra, maskSh,
     armIselInsI (.ASRV (zr d .W32) (zr .X16 .W32) (zr .X17 .W32)), maskRes]

/-- Register-register ALU lowering for all 9 `CoreAlu` ops, all 4 widths, and `sf : Bool`.
Preserves `d` even when `d = .X16` (used for `.SP` destination routing). -/
@[expose] def asmAluCoreIns (op : CoreAlu) (w : Width) (sf : Bool) (d ra rb : XReg) :
    List _root_.Instr :=
  match w with
  | .w32 | .w64 =>
    let rw := widthToRegWidth w
    let base := asmAluWideRegI op rw sf d ra rb
    if !sf then [base]
    else match op with
      | .add | .sub | .and => [base]
      | _ => [base, armIselInsI (.ANDS_s (xzr rw) (zr d rw) (sh d))]
  | .w8 | .w16 =>
    let n := w.bits
    if !sf then asmAluSubNoFlagsIns op n d ra rb
    else match op with
      | .add =>
        [armIselInsI (.UBFM (zr .X16 .W32) (zr ra .W32) n (n - 1)),
         armIselInsI (.UBFM (zr .X17 .W32) (zr rb .W32) n (n - 1)),
         armIselInsI (.ADDS_s (zr d .W32) (zr .X16 .W32) (sh .X17)),
         armIselInsI (.UBFM (zr d .W32) (zr d .W32) (32 - n) 31)]
      | .sub =>
        [armIselInsI (.UBFM (zr .X16 .W32) (zr ra .W32) n (n - 1)),
         armIselInsI (.UBFM (zr .X17 .W32) (zr rb .W32) n (n - 1)),
         armIselInsI (.SUBS_s (zr d .W32) (zr .X16 .W32) (sh .X17)),
         armIselInsI (.UBFM (zr d .W32) (zr d .W32) (32 - n) 31)]
      | _ =>
        asmAluSubNoFlagsIns op n d ra rb ++
          [armIselInsI (.UBFM (zr .X17 .W32) (zr d .W32) n (n - 1)),
           armIselInsI (.ANDS_s (xzr .W32) (zr .X17 .W32) (sh .X17))]

/-- Fast-path single-instruction 32/64-bit ALU with immediate RHS when representable. -/
@[expose] def asmAluImmFastIns? (op : CoreAlu) (w : Width) (sf : Bool) (d ra : XReg)
    (v : BitVec 64) : Option (List _root_.Instr) :=
  match w with
  | .w8 | .w16 => none
  | .w32 | .w64 =>
    let rw := widthToRegWidth w
    let vw := v.setWidth w.bits
    match op with
    | .add =>
      (armImm12? vw).map fun ei =>
        if sf then [armIselInsI (.ADDS_e (zr d rw) (.low (.reg ra) rw) ei)]
        else [armIselInsI (.ADD_e (.low (.reg d) rw) (.low (.reg ra) rw) ei)]
    | .sub =>
      (armImm12? vw).map fun ei =>
        if sf then [armIselInsI (.SUBS_e (zr d rw) (.low (.reg ra) rw) ei)]
        else [armIselInsI (.SUB_e (.low (.reg d) rw) (.low (.reg ra) rw) ei)]
    | .and =>
      let c64 := vw.setWidth 64
      if armIsValidLogicalImm rw c64 then
        if sf then some [armIselInsI (.ANDS_i (zr d rw) (zr ra rw) (.int64 (Int64.ofBitVec c64)))]
        else some [armIselInsI (.AND_i (.low (.reg d) rw) (zr ra rw) (.int64 (Int64.ofBitVec c64)))]
      else none
    | .or =>
      let c64 := vw.setWidth 64
      if !sf && armIsValidLogicalImm rw c64 then
        some [armIselInsI (.ORR_i (.low (.reg d) rw) (zr ra rw) (.int64 (Int64.ofBitVec c64)))]
      else none
    | .xor =>
      let c64 := vw.setWidth 64
      if !sf && armIsValidLogicalImm rw c64 then
        some [armIselInsI (.EOR_i (.low (.reg d) rw) (zr ra rw) (.int64 (Int64.ofBitVec c64)))]
      else none
    | .shl =>
      if !sf then
        let amt := vw.toNat % w.bits
        some [armIselInsI
          (.UBFM (zr d rw) (zr ra rw) ((rw.bits - amt) % rw.bits) (rw.bits - 1 - amt))]
      else none
    | .lshr =>
      if !sf then
        let amt := vw.toNat % w.bits
        some [armIselInsI (.UBFM (zr d rw) (zr ra rw) amt (rw.bits - 1))]
      else none
    | .ashr =>
      if !sf then
        let amt := vw.toNat % w.bits
        some [armIselInsI (.SBFM (zr d rw) (zr ra rw) amt (rw.bits - 1))]
      else none
    | .mul => none

/-- Full `.alu op w rd lhs rhs sf` lowering to AArch64 `Instr` list. -/
@[expose] def asmAluIns (op : CoreAlu) (w : Width) (rd lhs : Arm64.Reg) (rhs : Src arm64Arch)
    (sf : Bool) : List _root_.Instr :=
  let fallback : List _root_.Instr :=
    let (ca, ra) := armSrcToXIns .X16 lhs
    let (cb, rb) := armRhsToXIns .X17 w rhs
    match rd with
    | .reg d => ca ++ cb ++ asmAluCoreIns op w sf d ra rb
    | .SP => ca ++ cb ++ asmAluCoreIns op w sf .X16 ra rb ++ [armIselMovToSpI .X16]
  match rd, lhs, rhs with
  | .reg d, .reg ra, .imm v => (asmAluImmFastIns? op w sf d ra v).getD fallback
  | _, _, _ => fallback

/-- Full `.cmp w lhs rhs` lowering to AArch64 `Instr` list (`SUBS`, exact NZCV at all widths). -/
@[expose] def asmCmpIns (w : Width) (lhs : Arm64.Reg) (rhs : Src arm64Arch) :
    List _root_.Instr :=
  match w with
  | .w32 | .w64 =>
    let rw := widthToRegWidth w
    let fallback : List _root_.Instr :=
      let (ca, ra) := armSrcToXIns .X16 lhs
      let (cb, rb) := armRhsToXIns .X17 w rhs
      ca ++ cb ++ [armIselInsI (.SUBS_s (xzr rw) (zr ra rw) (sh rb))]
    match lhs, rhs with
    | .reg ra, .imm v =>
      match armImm12? (v.setWidth w.bits) with
      | some ei => [armIselInsI (.SUBS_e (xzr rw) (.low (.reg ra) rw) ei)]
      | none => fallback
    | _, _ => fallback
  | .w8 | .w16 =>
    let n := w.bits
    let (ca, ra) := armSrcToXIns .X16 lhs
    let (cb, rb) := armRhsToXIns .X17 w rhs
    ca ++ cb ++
      [armIselInsI (.UBFM (zr .X16 .W32) (zr ra .W32) n (n - 1)),
       armIselInsI (.UBFM (zr .X17 .W32) (zr rb .W32) n (n - 1)),
       armIselInsI (.SUBS_s (xzr .W32) (zr .X16 .W32) (sh .X17))]

/-- Full `.test w lhs rhs` lowering to AArch64 `Instr` list (`ANDS`, exact NZCV at all widths). -/
@[expose] def asmTestIns (w : Width) (lhs : Arm64.Reg) (rhs : Src arm64Arch) :
    List _root_.Instr :=
  match w with
  | .w32 | .w64 =>
    let rw := widthToRegWidth w
    let fallback : List _root_.Instr :=
      let (ca, ra) := armSrcToXIns .X16 lhs
      let (cb, rb) := armRhsToXIns .X17 w rhs
      ca ++ cb ++ [armIselInsI (.ANDS_s (xzr rw) (zr ra rw) (sh rb))]
    match lhs, rhs with
    | .reg ra, .imm v =>
      let c64 := (v.setWidth w.bits).setWidth 64
      if armIsValidLogicalImm rw c64 then
        [armIselInsI (.ANDS_i (xzr rw) (zr ra rw) (.int64 (Int64.ofBitVec c64)))]
      else fallback
    | _, _ => fallback
  | .w8 | .w16 =>
    let n := w.bits
    let (ca, ra) := armSrcToXIns .X16 lhs
    let (cb, rb) := armRhsToXIns .X17 w rhs
    ca ++ cb ++
      [armIselInsI (.UBFM (zr .X16 .W32) (zr ra .W32) n (n - 1)),
       armIselInsI (.UBFM (zr .X17 .W32) (zr rb .W32) n (n - 1)),
       armIselInsI (.ANDS_s (xzr .W32) (zr .X16 .W32) (sh .X17))]

/-! ## 3. Total Address Lowering, Loads, Stores, and Branches -/

/-- Total effective-address builder for all `AddrArg Arm64.Reg`, matching `armSetupAddrIns` on
all `armAddrValid` fast paths and materializing arbitrary `baseIdxDisp` into `.X16`. -/
@[expose] def armSetupAddrTotalIns (scale : Nat) (a : AddrArg Arm64.Reg) :
    List _root_.Instr × AddrExpr :=
  if armAddrValid scale a then
    armSetupAddrIns scale a
  else
    match a with
    | .baseIdxDisp base idx sc disp =>
      let (cb, rb) := armSrcToXIns .X16 base
      let (ci, ri) := armSrcToXIns .X17 idx
      let addIdx : _root_.Instr :=
        armIselInsI (.ADD_s (zr .X16 .W64) (zr rb .W64)
          { reg := zr ri .W64, amount := Int64.ofNat sc.shift, shift := .LSL })
      let addDisp : List _root_.Instr :=
        if disp == 0 then []
        else armMovImmI .X17 disp.toBitVec ++
          [armIselInsI (.ADD_s (zr .X16 .W64) (zr .X16 .W64) (sh .X17))]
      (cb ++ ci ++ [addIdx] ++ addDisp, atReg .X16)
    | _ => armSetupAddrIns scale a

/-- Single load `Instr` for `(w, ext)` into `d : XReg` from effective address `addr`. -/
@[expose] def asmLoadDirI (w : Width) (ext : LoadExt) (d : XReg) (addr : AddrExpr) :
    _root_.Instr :=
  match ext, w with
  | .sx, .w8 => armIselInsI (w := .W64) (.LDRSB (zr d .W64) addr)
  | .sx, .w16 => armIselInsI (w := .W64) (.LDRSH (zr d .W64) addr)
  | .sx, .w32 => armIselInsI (w := .W64) (.LDRSW (zr d .W64) (.addr addr))
  | .sx, .w64 => armIselInsI (w := .W64) (.LDR (zr d .W64) (.addr addr))
  | _, .w8 => armIselInsI (.LDRB (zr d .W32) addr)
  | _, .w16 => armIselInsI (.LDRH (zr d .W32) addr)
  | _, .w32 => armIselInsI (w := .W32) (.LDR (zr d .W32) (.addr addr))
  | _, .w64 => armIselInsI (w := .W64) (.LDR (zr d .W64) (.addr addr))

/-- Full `.load w ext rd addr` lowering to AArch64 `Instr` list. -/
@[expose] def asmLoadIns (w : Width) (ext : LoadExt) (rd : Arm64.Reg) (a : AddrArg Arm64.Reg) :
    List _root_.Instr :=
  let (setup, addr) := armSetupAddrTotalIns w.bytes a
  match rd with
  | .reg d => setup ++ [asmLoadDirI w ext d addr]
  | .SP => setup ++ [asmLoadDirI w ext .X16 addr, armIselMovToSpI .X16]

/-- Single store `Instr` for width `w` from `rx : XReg` to effective address `addr`. -/
@[expose] def asmStoreDirI (w : Width) (rx : XReg) (addr : AddrExpr) : _root_.Instr :=
  match w with
  | .w8 => armIselInsI (.STRB (zr rx .W32) addr)
  | .w16 => armIselInsI (.STRH (zr rx .W32) addr)
  | .w32 => armIselInsI (w := .W32) (.STR (zr rx .W32) addr)
  | .w64 => armIselInsI (w := .W64) (.STR (zr rx .W64) addr)

/-- Full `.store w rs addr` lowering to AArch64 `Instr` list. -/
@[expose] def asmStoreIns (w : Width) (rs : Arm64.Reg) (a : AddrArg Arm64.Reg) :
    List _root_.Instr :=
  let (setup, addr) := armSetupAddrTotalIns w.bytes a
  match rs with
  | .reg x => setup ++ [asmStoreDirI w x addr]
  | .SP => setup ++ [armIselMovToXI .X17 .SP, asmStoreDirI w .X17 addr]

/-- Flag-preserving low-byte non-zero branch (`uxtb w16, wr; cbnz w16, l`), matching VLL's
exact `(s.gpr r).setWidth 8 != 0#8` semantics without assuming `0/1` boolean normalization. -/
@[expose] def asmJnzGprIns (r : Arm64.Reg) (l : Sym) : List _root_.Instr :=
  match r with
  | .reg x =>
    [armIselInsI (.UBFM (zr .X16 .W32) (zr x .W32) 0 7),
     armIselInsI (.CBNZ (zr .X16 .W32) (.label l))]
  | .SP =>
    [armIselMovToXI .X16 .SP,
     armIselInsI (.UBFM (zr .X16 .W32) (zr .X16 .W32) 0 7),
     armIselInsI (.CBNZ (zr .X16 .W32) (.label l))]

/-! ## 4. Top-Level Context-Free Assembler `asmArm64` & Label-Offset Map `ρ` -/

/-- Context-free 1:1 AArch64 assembler lowering `Instr arm64Arch` to Kraken AArch64 directives. -/
@[expose] def asmArm64 : Instr arm64Arch → List _root_.Directive
  | .label s => [.label s]
  | .mov w rd rs => emitClean (asmMovIns w rd rs)
  | .movi rd imm => armMovi rd imm
  | .alu op w rd lhs rhs sf => emitClean (asmAluIns op w rd lhs rhs sf)
  | .cmp w lhs rhs => emitClean (asmCmpIns w lhs rhs)
  | .test w lhs rhs => emitClean (asmTestIns w lhs rhs)
  | .clearFlags => armClearFlags
  | .setcc rd c => armSetcc rd c
  | .load w ext rd addr => emitClean (asmLoadIns w ext rd addr)
  | .store w rs addr => emitClean (asmStoreIns w rs addr)
  | .slotSt i rs => armSlotSt i rs
  | .slotLd rd i => armSlotLd rd i
  | .prologue ns => (armPrologue ns).1
  | .epilogue ns => (armEpilogue ns).1
  | .canonAbi t r => (armCanonAbi t r).1
  | .jmp l => armJmp l
  | .jcc c l => armJcc c l
  | .jnzGpr r l => emitClean (asmJnzGprIns r l)
  | .call sym => armFrame.call sym
  | .icall r =>
    match r with
    | .reg x => armCallReg (.reg x)
    | .SP => [armMovToX .X16 .SP, .blr (.reg .X16)]
  | .ret => armFrame.ret
  | .exitJmp sym => armFrame.exitJmp sym
  | .tailJmpR r =>
    match r with
    | .reg x => armJmpReg (.reg x)
    | .SP => [armMovToX .X16 .SP, .br (.reg .X16)]
  | .symAddr sym rd =>
    match rd with
    | .reg x => armSymAddrReg sym (.reg x)
    | .SP => armSymAddr .X16 sym ++ [armMovToSp .X16]
  | .ijmp r =>
    match r with
    | .reg x => armJmpReg (.reg x)
    | .SP => [armMovToX .X16 .SP, .br (.reg .X16)]
  | .pad _ => [ins (w := .W64) .NOP]
  | .native d => [d]

/-- Assemble a flat `List (Instr arm64Arch)` into Kraken AArch64 directives. -/
@[expose] def asmArm64List (is : List (Instr arm64Arch)) : List _root_.Directive :=
  is.flatMap asmArm64

/-- Flatten and assemble a `VllCodeMap arm64Arch` into Kraken AArch64 directives. -/
@[expose] def asmArm64CodeMap (cm : VllCodeMap arm64Arch) : List _root_.Directive :=
  asmArm64List cm.flatten

/-- Label-index translation map `ρ(k)` giving the starting directive index in `asmArm64List prog`
corresponding to VLL instruction index `k`. -/
@[expose] def asmArm64Offset (prog : List (Instr arm64Arch)) (k : Nat) : Nat :=
  (asmArm64List (prog.take k)).length

/-! ## 5. Assembly-Simulation Side Conditions (`arm64InstrOk`) -/

/-- State-independent well-formedness side condition for assembling `i`: no scratch registers
(`x16`, `x17`) read, and legal AArch64 scalar widths (`8`/`16`/`32`/`64`) for `canonAbi`. -/
@[expose] def arm64InstrStaticOk (i : Instr arm64Arch) : Prop :=
  (∀ r ∈ i.uses, r ∉ armScratch) ∧
  (match i with
   | .canonAbi (.bits n) _ => n ∈ [8, 16, 32, 64]
   | _ => True)

/-- Dynamic side condition for assembling `i` at state `s`: 16-byte `sp` alignment on stack
slot/frame instructions (`slotSt`, `slotLd`, `prologue`, `epilogue`). -/
@[expose] def arm64InstrDynOk (i : Instr arm64Arch) (s : MachData Arm64.Reg Empty StatusFlags) :
    Prop :=
  match i with
  | .slotSt _ _ | .slotLd _ _ | .prologue _ | .epilogue _ => arm64Arch.abi.spOk (s.gpr .SP)
  | _ => True

/-- Combined per-instruction assembly-simulation side condition for `asmArm64`. -/
@[expose] def arm64InstrOk (i : Instr arm64Arch) (s : MachData Arm64.Reg Empty StatusFlags) :
    Prop :=
  arm64InstrStaticOk i ∧ arm64InstrDynOk i s

end LeanQbe.T.Vll
