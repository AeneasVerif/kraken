module

public import Kraken.X64.Syntax
public import LeanQbe.T.LeanLCNF.Basic
meta import LeanQbe.T.LeanLCNF.Basic

/-!
# Stage B Minimal AT&T x86-64 Assembly Printer (`PrintAsm0`)

Pure, first-order, closure-free, zero-global, acyclic AT&T x86-64 assembly emitter covering every
directive, instruction, and operand emitted by `leanqbe0` Stage A (`Isel0`/`Rega0`) and the full
scalar `x64ScalarTarget` (`x64Gpr` + `x64Frame`) envelope:

* **Zero closures / HOFs / `ToString` dicts:** direct tail-recursive list loops and monomorphic
  pattern matches (`papTargets = []`, `maxAp = 0`).
* **Zero string literals / closed constants / big `Nat` globals:** builds output directly into a
  `ByteArray` using raw ASCII `UInt8` scalar pushes and tail-recursive `UInt64`/`Int64` decimal
  formatting (`totalGlobalsCount = 0`).
* **Small acyclic functions:** splits instruction formatting across small `@[noinline]` helpers so
  every lowered function stays well below `250` x64 directives.
* **Out of the TCB:** `LeanQbe.T.Amd64.PrintAsm0Lemmas` proves bit-for-bit byte and string
  equivalence against `Kraken.X64.toATT` and `LeanQbe.T.Driver.emitAsm`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Amd64

namespace PrintAsm0

/-! ## 1. Low-level ASCII byte and decimal emitters -/

@[expose] def e2 (ba : ByteArray) (a b : UInt8) : ByteArray :=
  (ba.push a).push b

@[expose] def e3 (ba : ByteArray) (a b c : UInt8) : ByteArray :=
  ((ba.push a).push b).push c

@[expose] def e4 (ba : ByteArray) (a b c d : UInt8) : ByteArray :=
  (((ba.push a).push b).push c).push d

@[expose] def eCommaSp (ba : ByteArray) : ByteArray :=
  e2 ba 0x2c 0x20

@[expose] def eWidth (ba : ByteArray) : Width → ByteArray
  | .W8 => ba.push 0x62
  | .W16 => ba.push 0x77
  | .W32 => ba.push 0x6c
  | .W64 => ba.push 0x71

@[expose] def emitStrLoop (ba : ByteArray) (s : String) (i : Nat) : ByteArray :=
  if h : i < s.utf8ByteSize then
    emitStrLoop (ba.push (s.getUTF8Byte ⟨i⟩ h)) s (Nat.add i 1)
  else ba
termination_by s.utf8ByteSize - i

@[expose] def emitStr (ba : ByteArray) (s : String) : ByteArray :=
  emitStrLoop ba s 0

@[expose] def pow10Up (fuel : Nat) (q p : UInt64) : UInt64 :=
  match fuel with
  | 0 => p
  | fuel' + 1 => if p <= q then pow10Up fuel' q (p * 10) else p

@[expose] def emitPowDown (fuel : Nat) (ba : ByteArray) (n p : UInt64) : ByteArray :=
  let d : UInt8 := 48 + (n / p).toUInt8
  let ba' := ba.push d
  match fuel with
  | 0 => ba'
  | fuel' + 1 => if p == 1 then ba' else emitPowDown fuel' ba' (n % p) (p / 10)

@[expose, noinline] def emitU64Dec (ba : ByteArray) (n : UInt64) : ByteArray :=
  emitPowDown 20 ba n (pow10Up 20 (n / 10) 1)

@[expose, noinline] def emitI64Dec (ba : ByteArray) (bits : UInt64) : ByteArray :=
  if (bits >>> 63) == 1 then emitU64Dec (ba.push 0x2d) (0 - bits)
  else emitU64Dec ba bits

/-! ## 2. Registers, condition codes, constants, addresses, and operands -/

@[expose, noinline] def regPairBytes (ba : ByteArray) : Reg64 → ByteArray
  | .rax => e2 ba 0x61 0x78
  | .rbx => e2 ba 0x62 0x78
  | .rcx => e2 ba 0x63 0x78
  | .rdx => e2 ba 0x64 0x78
  | .rsi => e2 ba 0x73 0x69
  | .rdi => e2 ba 0x64 0x69
  | .rsp => e2 ba 0x73 0x70
  | .rbp => e2 ba 0x62 0x70
  | _ => ba

@[expose, noinline] def regLow8Bytes (ba : ByteArray) : Reg64 → ByteArray
  | .rax => e2 ba 0x61 0x6c
  | .rbx => e2 ba 0x62 0x6c
  | .rcx => e2 ba 0x63 0x6c
  | .rdx => e2 ba 0x64 0x6c
  | .rsi => e3 ba 0x73 0x69 0x6c
  | .rdi => e3 ba 0x64 0x69 0x6c
  | .rsp => e3 ba 0x73 0x70 0x6c
  | .rbp => e3 ba 0x62 0x70 0x6c
  | _ => ba

@[expose, noinline] def regExtNum : Reg64 → UInt64
  | .r8 => 8
  | .r9 => 9
  | .r10 => 10
  | .r11 => 11
  | .r12 => 12
  | .r13 => 13
  | .r14 => 14
  | .r15 => 15
  | _ => 0

@[expose, noinline] def emitReg64 (ba : ByteArray) (w : Width) (r : Reg64) : ByteArray :=
  let ba := ba.push 0x25
  let idx := regExtNum r
  if idx >= 8 then
    let ba := emitU64Dec (ba.push 0x72) idx
    match w with
    | .W64 => ba
    | .W32 => ba.push 0x64
    | .W16 => ba.push 0x77
    | .W8 => ba.push 0x62
  else
    match w with
    | .W64 => regPairBytes (ba.push 0x72) r
    | .W32 => regPairBytes (ba.push 0x65) r
    | .W16 => regPairBytes ba r
    | .W8 => regLow8Bytes ba r

@[expose, noinline] def emitReg (ba : ByteArray) (w : Width) : Reg w → ByteArray
  | .low r _ => emitReg64 ba w r
  | .ah => e3 ba 0x25 0x61 0x68
  | .bh => e3 ba 0x25 0x62 0x68
  | .ch => e3 ba 0x25 0x63 0x68
  | .dh => e3 ba 0x25 0x64 0x68

@[expose, noinline] def emitCcHi (ba : ByteArray) : CondCode → ByteArray
  | .s => ba.push 0x73
  | .ns => e2 ba 0x6e 0x73
  | .p => ba.push 0x70
  | .np => e2 ba 0x6e 0x70
  | .l => ba.push 0x6c
  | .ge => e2 ba 0x67 0x65
  | .le => e2 ba 0x6c 0x65
  | .g => ba.push 0x67
  | _ => ba

@[expose, noinline] def emitCc (ba : ByteArray) : CondCode → ByteArray
  | .o => ba.push 0x6f
  | .no => e2 ba 0x6e 0x6f
  | .c => ba.push 0x62
  | .nc => e2 ba 0x61 0x65
  | .z => ba.push 0x65
  | .nz => e2 ba 0x6e 0x65
  | .be => e2 ba 0x62 0x65
  | .a => ba.push 0x61
  | cc => emitCcHi ba cc

@[expose, noinline] def emitConst (ba : ByteArray) : ConstExpr → ByteArray
  | .label l => emitStr ba l
  | .int64 i => emitI64Dec ba i.toUInt64
  | _ => ba

@[expose] def emitAddrDisp (ba : ByteArray) (base : Option RegOrRip) (disp : ConstExpr) :
    ByteArray :=
  match base, disp with
  | some .rip, .sub e .after_current_instruction => emitConst ba e
  | _, .int64 i => if i.toUInt64 == 0 then ba else emitI64Dec ba i.toUInt64
  | _, d => emitConst ba d

@[expose] def emitScaleByte (ba : ByteArray) : Width → ByteArray
  | .W8 => ba.push 0x31
  | .W16 => ba.push 0x32
  | .W32 => ba.push 0x34
  | .W64 => ba.push 0x38

@[expose, noinline] def emitAddr (ba : ByteArray) (a : AddrExpr) : ByteArray :=
  match a.base, a.idx with
  | none, none => emitConst ba a.disp
  | base, idx =>
    let ba := (emitAddrDisp ba base a.disp).push 0x28
    let ba := match base with
      | some (.reg r) => emitReg64 ba .W64 r
      | some .rip => e4 ba 0x25 0x72 0x69 0x70
      | none => ba
    let ba := match idx with
      | some idx' =>
        let ba := emitReg64 (ba.push 0x2c) .W64 idx'.reg
        emitScaleByte (ba.push 0x2c) idx'.scale
      | none => ba
    ba.push 0x29

@[expose, noinline] def emitRm (ba : ByteArray) (w : Width) : RegOrMem w → ByteArray
  | .reg r => emitReg ba w r
  | .mem a => emitAddr ba a

@[expose, noinline] def emitOpd (ba : ByteArray) (w : Width) : Operand w → ByteArray
  | .regOrMem x => emitRm ba w x
  | .imm e => emitConst (ba.push 0x24) e

@[expose, noinline] def emitCount (ba : ByteArray) : ShiftCountExpr → ByteArray
  | .cl => e3 ba 0x25 0x63 0x6c
  | .imm8 e => emitConst (ba.push 0x24) e

@[expose, noinline] def emitTarget (ba : ByteArray) : RelRegOrMem → ByteArray
  | .rel (.sub e .after_current_instruction) => emitConst ba e
  | .rel e => emitConst ba e
  | .reg r => emitReg ba .W64 r
  | .mem a => emitAddr ba a

/-! ## 3. Factored instruction emitters (`< 250` directives per lowered function) -/

@[expose, noinline] def eOp1W (ba : ByteArray) (w : Width) (d : RegOrMem w) : ByteArray :=
  emitRm ((eWidth ba w).push 0x20) w d

@[expose, noinline] def eOp2W (ba : ByteArray) (w : Width) (d : RegOrMem w) (x : Operand w) :
    ByteArray :=
  let ba := emitOpd ((eWidth ba w).push 0x20) w x
  emitRm (eCommaSp ba) w d

@[expose, noinline] def eShW (ba : ByteArray) (w : Width) (d : RegOrMem w) (c : ShiftCountExpr) :
    ByteArray :=
  let ba := emitCount ((eWidth ba w).push 0x20) c
  emitRm (eCommaSp ba) w d

@[expose, noinline] def eRmReg (ba : ByteArray) (w : Width) (d : Reg w) (x : RegOrMem w) :
    ByteArray :=
  let ba := emitRm (ba.push 0x20) w x
  emitReg (eCommaSp ba) w d

@[expose, noinline] def eBmi2Shift (ba : ByteArray) (w : Width) (d : Reg w) (x : RegOrMem w)
    (c : Reg w) : ByteArray :=
  let ba := emitReg (ba.push 0x20) w c
  let ba := emitRm (eCommaSp ba) w x
  emitReg (eCommaSp ba) w d

@[expose, noinline] def emitMovExt (ba : ByteArray) (w w' : Width) (isSign : Bool)
    (d : RegOrMem w) (x : RegOrMem w') : ByteArray :=
  let tagByte : UInt8 := if isSign then 0x73 else 0x7a
  let ba := e4 ba 0x6d 0x6f 0x76 tagByte
  match x with
  | .mem a =>
    let ba := eWidth (eWidth ba w') w
    let ba := emitAddr (ba.push 0x20) a
    emitRm (eCommaSp ba) w d
  | .reg r =>
    let ba := emitReg (e2 ba 0x78 0x20) w' r
    emitRm (eCommaSp ba) w d

@[expose, noinline] def emitOpCtrl (ba : ByteArray) (w : Width) (op : Operation w) : ByteArray :=
  match op with
  | .jcc cc l => emitStr ((emitCc (ba.push 0x6a) cc).push 0x20) l
  | .jmp t => emitTarget (e4 ba 0x6a 0x6d 0x70 0x20) t
  | .call t => emitTarget ((e4 ba 0x63 0x61 0x6c 0x6c).push 0x20) t
  | .ret => e3 ba 0x72 0x65 0x74
  | _ => ba

@[expose, noinline] def emitOpBmi2 (ba : ByteArray) (w : Width) (op : Operation w) : ByteArray :=
  match op with
  | .shlx d x c => eBmi2Shift (e4 ba 0x73 0x68 0x6c 0x78) w d x c
  | .shrx d x c => eBmi2Shift (e4 ba 0x73 0x68 0x72 0x78) w d x c
  | .sarx d x c => eBmi2Shift (e4 ba 0x73 0x61 0x72 0x78) w d x c
  | .rorx d x i =>
    let ba := emitConst (e2 (e4 ba 0x72 0x6f 0x72 0x78) 0x20 0x24) i
    let ba := emitRm (eCommaSp ba) w x
    emitReg (eCommaSp ba) w d
  | _ => emitOpCtrl ba w op

@[expose, noinline] def emitOpBitcnt (ba : ByteArray) (w : Width) (op : Operation w) :
    ByteArray :=
  match op with
  | .bswap d => emitReg ((e4 ba 0x62 0x73 0x77 0x61).push 0x70 |>.push 0x20) w d
  | .lzcnt d x => eRmReg ((e4 ba 0x6c 0x7a 0x63 0x6e).push 0x74) w d x
  | .tzcnt d x => eRmReg ((e4 ba 0x74 0x7a 0x63 0x6e).push 0x74) w d x
  | .popcnt d x => eRmReg (e3 (e3 ba 0x70 0x6f 0x70) 0x63 0x6e 0x74) w d x
  | _ => emitOpBmi2 ba w op

@[expose, noinline] def emitOpShift2 (ba : ByteArray) (w : Width) (op : Operation w) :
    ByteArray :=
  match op with
  | .rol d c => eShW (e3 ba 0x72 0x6f 0x6c) w d c
  | .ror d c => eShW (e3 ba 0x72 0x6f 0x72) w d c
  | .shld d x c =>
    let ba := emitCount ((e4 ba 0x73 0x68 0x6c 0x64).push 0x20) c
    let ba := emitReg (eCommaSp ba) w x
    emitRm (eCommaSp ba) w d
  | .shrd d x c =>
    let ba := emitCount ((e4 ba 0x73 0x68 0x72 0x64).push 0x20) c
    let ba := emitReg (eCommaSp ba) w x
    emitRm (eCommaSp ba) w d
  | _ => emitOpBitcnt ba w op

@[expose, noinline] def emitOpShift1 (ba : ByteArray) (w : Width) (op : Operation w) :
    ByteArray :=
  match op with
  | .shl d c => eShW (e3 ba 0x73 0x68 0x6c) w d c
  | .shr d c => eShW (e3 ba 0x73 0x68 0x72) w d c
  | .sar d c => eShW (e3 ba 0x73 0x61 0x72) w d c
  | _ => emitOpShift2 ba w op

@[expose, noinline] def emitOpCarry (ba : ByteArray) (w : Width) (op : Operation w) : ByteArray :=
  match op with
  | .adc d x => eOp2W (e3 ba 0x61 0x64 0x63) w d x
  | .sbb d x => eOp2W (e3 ba 0x73 0x62 0x62) w d x
  | .adcx d x => eRmReg (e4 ba 0x61 0x64 0x63 0x78) w d x
  | .adox d x => eRmReg (e4 ba 0x61 0x64 0x6f 0x78) w d x
  | .inc d => eOp1W (e3 ba 0x69 0x6e 0x63) w d
  | .dec d => eOp1W (e3 ba 0x64 0x65 0x63) w d
  | _ => emitOpShift1 ba w op

@[expose, noinline] def emitOpMulDiv (ba : ByteArray) (w : Width) (op : Operation w) :
    ByteArray :=
  match op with
  | .mul x => eOp1W (e3 ba 0x6d 0x75 0x6c) w x
  | .div x => eOp1W (e3 ba 0x64 0x69 0x76) w x
  | .idiv x => eOp1W (e4 ba 0x69 0x64 0x69 0x76) w x
  | .imul1 x => eOp1W (e4 ba 0x69 0x6d 0x75 0x6c) w x
  | .imul none a b => eOp2W (e4 ba 0x69 0x6d 0x75 0x6c) w a b
  | .mulx hi lo x =>
    let ba := emitRm ((e4 ba 0x6d 0x75 0x6c 0x78).push 0x20) w x
    let ba := emitReg (eCommaSp ba) w lo
    emitReg (eCommaSp ba) w hi
  | _ => emitOpCarry ba w op

@[expose, noinline] def emitOpAlu2 (ba : ByteArray) (w : Width) (op : Operation w) : ByteArray :=
  match op with
  | .cmp a b => eOp2W (e3 ba 0x63 0x6d 0x70) w a b
  | .test a b => eOp2W (e4 ba 0x74 0x65 0x73 0x74) w a b
  | .neg d => eOp1W (e3 ba 0x6e 0x65 0x67) w d
  | .not d => eOp1W (e3 ba 0x6e 0x6f 0x74) w d
  | _ => emitOpMulDiv ba w op

@[expose, noinline] def emitOpAlu1 (ba : ByteArray) (w : Width) (op : Operation w) : ByteArray :=
  match op with
  | .add d x => eOp2W (e3 ba 0x61 0x64 0x64) w d x
  | .sub d x => eOp2W (e3 ba 0x73 0x75 0x62) w d x
  | .and d x => eOp2W (e3 ba 0x61 0x6e 0x64) w d x
  | .or d x => eOp2W (e2 ba 0x6f 0x72) w d x
  | .xor d x => eOp2W (e3 ba 0x78 0x6f 0x72) w d x
  | _ => emitOpAlu2 ba w op

@[expose, noinline] def emitOpData (ba : ByteArray) (w : Width) (op : Operation w) : ByteArray :=
  match op with
  | .mov d x => eOp2W (e3 ba 0x6d 0x6f 0x76) w d x
  | .movsx (w' := w') d x => emitMovExt ba w w' true d x
  | .movzx (w' := w') d x => emitMovExt ba w w' false d x
  | .setcc cc d => emitRm ((emitCc (e3 ba 0x73 0x65 0x74) cc).push 0x20) w d
  | .cmovcc cc d x => eRmReg (emitCc (e4 ba 0x63 0x6d 0x6f 0x76) cc) w d x
  | .lea d a =>
    let ba := emitAddr (e4 ba 0x6c 0x65 0x61 0x20) a
    emitReg (eCommaSp ba) w d
  | _ => emitOpAlu1 ba w op

end PrintAsm0

/-! ## 4. Public directive and module entrypoints -/

/-- Append a single AT&T assembly directive (without trailing newline) into `ba`. -/
@[expose, noinline] def emitDir0 (ba : ByteArray) : Directive → ByteArray
  | .label l => (PrintAsm0.emitStr ba l).push 0x3a
  | .instr (.regular .W64 w op) => PrintAsm0.emitOpData ba w op
  | _ => ba

namespace PrintAsm0

@[expose] def emitDirsLineLoop (ba : ByteArray) : List Directive → ByteArray
  | [] => ba
  | d :: ds => emitDirsLineLoop ((emitDir0 ba d).push 0x0a) ds

@[expose] def emitDirsNoTrailLoop (ba : ByteArray) : List Directive → ByteArray
  | [] => ba
  | [d] => emitDir0 ba d
  | d :: ds => emitDirsNoTrailLoop ((emitDir0 ba d).push 0x0a) ds

@[expose] def emitGloblLoop (ba : ByteArray) : List String → ByteArray
  | [] => ba
  | fn :: rest =>
    let ba := e4 (e3 ba 0x2e 0x67 0x6c) 0x6f 0x62 0x6c 0x20
    emitGloblLoop ((emitStr ba fn).push 0x0a) rest

end PrintAsm0

/-- Emit a list of directives as UTF-8 AT&T assembly bytes, one `'\n'`-terminated line per
directive (`ByteArray.empty` on `[]`). -/
@[expose] def printAmd64Asm0 (p : List Directive) : ByteArray :=
  let cap : Nat := match p with | [] => 0 | _ :: _ => 64
  PrintAsm0.emitDirsLineLoop (ByteArray.emptyWithCapacity cap) p

/-- Emit a list of directives as UTF-8 AT&T assembly bytes separated by `'\n'` (matching
`Kraken.X64.toATT p` verbatim without a trailing newline). -/
@[expose] def printAmd64Asm0NoTrail (p : List Directive) : ByteArray :=
  let cap : Nat := match p with | [] => 0 | _ :: _ => 64
  PrintAsm0.emitDirsNoTrailLoop (ByteArray.emptyWithCapacity cap) p

/-- Emit a full module (`.text\n`, `.globl <fn>\n`, and `'\n'`-terminated AT&T directive lines)
into a `ByteArray` without any `String` literals or closures. -/
@[expose] def printDir0Asm0 (fnNames : List String) (p : List Directive) : ByteArray :=
  let cap : Nat := match fnNames, p with | [], [] => 8 | _, _ => 64
  let ba := ByteArray.emptyWithCapacity cap
  let ba := PrintAsm0.e4 (PrintAsm0.e2 ba 0x2e 0x74) 0x65 0x78 0x74 0x0a
  PrintAsm0.emitDirsLineLoop (PrintAsm0.emitGloblLoop ba fnNames) p

/-- Emit a list of `Directive`s as an AT&T assembly `String` (matching `Kraken.X64.toATT`). -/
@[expose] def printAsm0 (p : List Directive) : String :=
  String.fromUTF8! (printAmd64Asm0NoTrail p)

/-- Emit a full module (`.text\n`, `.globl` lines, and AT&T directives) as a `String`. -/
@[expose] def printModule0 (fnNames : List String) (p : List Directive) : String :=
  String.fromUTF8! (printDir0Asm0 fnNames p)

/-! ## 5. Extracted Impure LCNF Module for `CheckLeanQbe0Clean` Verification -/

lcnf_of_lean! printAsm0LcMod [printDir0Asm0, printAmd64Asm0, printAmd64Asm0NoTrail]

end LeanQbe.T.Amd64
