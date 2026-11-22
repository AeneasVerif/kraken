module

public import LeanQbe.T.Bootstrap0.Types0
public import LeanQbe.T.LeanLCNF.Basic
meta import LeanQbe.T.LeanLCNF.Basic

/-!
# Bootstrap Stage A (`leanqbe0`) Closure-Free `Dir0 → ByteArray` AT&T Printer (`PrintDir0`)

Strictly first-order, monomorphic, closure-free, zero-global, zero-`String`-literal, `≤ 5`-arg
AT&T x86-64 assembly emitter directly from `Dir0` + a flat byte symbol table (`symBytes :
ByteArray`, `symOffs : Array Nat` storing `(off, len)` slices at `2 * sym`, `2 * sym + 1`):

* `printDir0Bytes`: appends the exact AT&T assembly bytes for one `Dir0` (matching
  `Kraken.X64.toATT (Bridge0.dir0ToAmd64 symName d)` without trailing newline).
* `printDirs0Bytes`: appends `'\n'`-separated AT&T bytes for `List Dir0` (matching
  `Kraken.X64.toATT (Bridge0.toAmd64Program symName ds)` without trailing newline).
* `printDirs0LinesBytes`: appends `'\n'`-terminated AT&T lines for `List Dir0`.
* `printGlobl0Bytes` / `printModule0Bytes`: emits `.text\n`, `.globl <sym>\n`, and directive lines.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Bootstrap0

namespace PrintDir0

private theorem u32Sub1Lt (n : UInt32) (h : n ≠ 0) : (n - 1).toNat < n.toNat := by
  have hn : n.toNat ≠ 0 := by
    intro hz
    apply h
    calc n = UInt32.ofNat n.toNat := UInt32.ofNat_toNat.symm
      _ = UInt32.ofNat 0 := by rw [hz]
      _ = 0 := rfl
  have h1 : (1 : UInt32) ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn)
  rw [UInt32.toNat_sub_of_le n 1 h1]
  exact Nat.sub_lt (Nat.pos_of_ne_zero hn) Nat.zero_lt_one

private theorem u64Add1SubLt (i endOff : UInt64) (h : i < endOff) :
    endOff.toNat - (i + 1).toNat < endOff.toNat - i.toNat := by
  have hi : i.toNat < endOff.toNat := h
  have hsz : endOff.toNat < 2 ^ 64 := endOff.toNat_lt_size
  have hadd : (i + 1).toNat = i.toNat + 1 := by
    rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
    exact Nat.mod_eq_of_lt (by omega)
  rw [hadd]
  omega

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

@[expose] def pow10Up (fuel : UInt32) (q p : UInt64) : UInt64 :=
  if h : fuel = 0 then p
  else if p <= q then pow10Up (fuel - 1) q (p * 10) else p
termination_by fuel.toNat
decreasing_by exact u32Sub1Lt fuel h

@[expose] def emitPowDown (fuel : UInt32) (ba : ByteArray) (n p : UInt64) : ByteArray :=
  let d : UInt8 := 48 + (n / p).toUInt8
  let ba' := ba.push d
  if h : fuel = 0 then ba'
  else if p == 1 then ba' else emitPowDown (fuel - 1) ba' (n % p) (p / 10)
termination_by fuel.toNat
decreasing_by exact u32Sub1Lt fuel h

@[expose, noinline] def emitU64Dec (ba : ByteArray) (n : UInt64) : ByteArray :=
  emitPowDown 20 ba n (pow10Up 20 (n / 10) 1)

@[expose, noinline] def emitI64Dec (ba : ByteArray) (bits : UInt64) : ByteArray :=
  if (bits >>> 63) == 1 then emitU64Dec (ba.push 0x2d) (0 - bits)
  else emitU64Dec ba bits

/-! ## 2. Flat byte symbol table and `Label0` emitters -/

@[expose, noinline] def arrGetU64 (arr : Array Nat) (i : UInt64) : UInt64 :=
  UInt64.ofNat (arr[i.toNat]!)

@[expose, noinline] def arrSizeU64 (arr : Array Nat) : UInt64 :=
  UInt64.ofNat arr.size

@[expose, noinline] def baSizeU64 (ba : ByteArray) : UInt64 :=
  UInt64.ofNat ba.size

@[expose, noinline] def baGetU8 (ba : ByteArray) (i : UInt64) : UInt8 :=
  ba.get! i.toNat

@[expose] def emitSymLoop (symBytes : ByteArray) (i endOff : UInt64) (out : ByteArray) :
    ByteArray :=
  if h : i < endOff then
    emitSymLoop symBytes (i + 1) endOff (out.push (baGetU8 symBytes i))
  else out
termination_by endOff.toNat - i.toNat
decreasing_by exact u64Add1SubLt i endOff h

@[expose, noinline] def emitSym (symBytes : ByteArray) (symOffs : Array Nat) (sym : Sym0)
    (out : ByteArray) : ByteArray :=
  let idx := sym.toUInt64 * 2
  let arrSz := arrSizeU64 symOffs
  if idx < arrSz && 1 < arrSz - idx then
    let off := arrGetU64 symOffs idx
    let len := arrGetU64 symOffs (idx + 1)
    let baSz := baSizeU64 symBytes
    if off <= baSz && len <= baSz - off then
      emitSymLoop symBytes off (off + len) out
    else out
  else out

@[expose, noinline] def emitLabel0 (symBytes : ByteArray) (symOffs : Array Nat) (l : Label0)
    (out : ByteArray) : ByteArray :=
  match l with
  | .sym id => emitSym symBytes symOffs id out
  | .loc fnId lblId =>
    let out := e3 out 0x2e 0x4c 0x5f
    let out := emitU64Dec out fnId.toUInt64
    emitU64Dec (out.push 0x5f) lblId.toUInt64

/-! ## 3. Registers, condition codes, and mnemonics -/

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

@[expose, noinline] def emitAluMn (ba : ByteArray) : AluKind0 → ByteArray
  | .add => e3 ba 0x61 0x64 0x64
  | .sub => e3 ba 0x73 0x75 0x62
  | .mul => e4 ba 0x69 0x6d 0x75 0x6c
  | .and => e3 ba 0x61 0x6e 0x64
  | .or => e2 ba 0x6f 0x72
  | .xor => e3 ba 0x78 0x6f 0x72

@[expose, noinline] def emitShiftMn (ba : ByteArray) : ShiftKind0 → ByteArray
  | .shl => e3 ba 0x73 0x68 0x6c
  | .lshr => e3 ba 0x73 0x68 0x72
  | .ashr => e3 ba 0x73 0x61 0x72
  | .rotl => e3 ba 0x72 0x6f 0x6c
  | .rotr => e3 ba 0x72 0x6f 0x72

/-! ## 4. Shared instruction-formatting helpers (`≤ 5` args, small LCNF) -/

@[expose, noinline] def eRegRegW (ba : ByteArray) (w : Width) (rd rs : Reg64) : ByteArray :=
  let ba := emitReg64 ((eWidth ba w).push 0x20) w rs
  emitReg64 (eCommaSp ba) w rd

@[expose, noinline] def eMovReg (ba : ByteArray) (wDst : Width) (rd : Reg64) (wSrc : Width)
    (rs : Reg64) : ByteArray :=
  let ba := emitReg64 (ba.push 0x20) wSrc rs
  emitReg64 (eCommaSp ba) wDst rd

@[expose, noinline] def eImmReg (ba : ByteArray) (w : Width) (rd : Reg64) (imm : UInt64) :
    ByteArray :=
  let ba := emitI64Dec (e2 (eWidth ba w) 0x20 0x24) imm
  emitReg64 (eCommaSp ba) w rd

@[expose, noinline] def eSpSuffix (ba : ByteArray) : ByteArray :=
  e4 (e2 ba 0x28 0x25) 0x72 0x73 0x70 0x29

@[expose, noinline] def eSlotMem (ba : ByteArray) (disp : UInt64) : ByteArray :=
  let ba := if disp == 0 then ba else emitI64Dec ba disp
  eSpSuffix ba

@[expose, noinline] def eSlotIdxMem (ba : ByteArray) (idx : Reg64) : ByteArray :=
  let ba := emitReg64 (e2 (e4 ba 0x28 0x25 0x72 0x73) 0x70 0x2c) .W64 idx
  e3 ba 0x2c 0x31 0x29

@[expose, noinline] def eRegMemAt (ba : ByteArray) (r : Reg64) : ByteArray :=
  (emitReg64 (ba.push 0x28) .W64 r).push 0x29

@[expose, noinline] def eMovzx32 (ba : ByteArray) (wSrc : Width) (rd rs : Reg64) : ByteArray :=
  match wSrc with
  | .W8 => eMovReg (e4 ba 0x6d 0x6f 0x76 0x7a |>.push 0x78) .W32 rd .W8 rs
  | .W16 => eMovReg (e4 ba 0x6d 0x6f 0x76 0x7a |>.push 0x78) .W32 rd .W16 rs
  | .W32 => eRegRegW (e3 ba 0x6d 0x6f 0x76) .W32 rd rs
  | .W64 => eRegRegW (e3 ba 0x6d 0x6f 0x76) .W64 rd rs

@[expose, noinline] def eMovsx (ba : ByteArray) (wDst : Width) (rd : Reg64) (wSrc : Width)
    (rs : Reg64) : ByteArray :=
  let isExt :=
    match wDst, wSrc with
    | .W64, .W8 | .W64, .W16 | .W64, .W32 => true
    | .W32, .W8 | .W32, .W16 => true
    | _, _ => false
  if isExt then eMovReg (e4 ba 0x6d 0x6f 0x76 0x73 |>.push 0x78) wDst rd wSrc rs
  else eRegRegW (e3 ba 0x6d 0x6f 0x76) wDst rd rs

@[expose, noinline] def eLdMem (ba : ByteArray) (w : Width) (rd base : Reg64) : ByteArray :=
  match w with
  | .W8 =>
    let ba := eRegMemAt (e3 (e4 ba 0x6d 0x6f 0x76 0x7a) 0x62 0x6c 0x20) base
    emitReg64 (eCommaSp ba) .W32 rd
  | .W16 =>
    let ba := eRegMemAt (e3 (e4 ba 0x6d 0x6f 0x76 0x7a) 0x77 0x6c 0x20) base
    emitReg64 (eCommaSp ba) .W32 rd
  | .W32 =>
    let ba := eRegMemAt (e2 (e3 ba 0x6d 0x6f 0x76) 0x6c 0x20) base
    emitReg64 (eCommaSp ba) .W32 rd
  | .W64 =>
    let ba := eRegMemAt (e2 (e3 ba 0x6d 0x6f 0x76) 0x71 0x20) base
    emitReg64 (eCommaSp ba) .W64 rd

@[expose, noinline] def eSarRdx (ba : ByteArray) (is64 : Bool) (imm : UInt64) : ByteArray :=
  let ba := e4 ba 0x73 0x61 0x72 (if is64 then 0x71 else 0x6c)
  let ba := emitU64Dec (e2 ba 0x20 0x24) imm
  let ba := e2 ba 0x2c 0x20
  emitReg64 ba (if is64 then .W64 else .W32) .rdx

@[expose, noinline] def eDivSignedPfx (ba : ByteArray) (is64 : Bool) : ByteArray :=
  let w := if is64 then Width.W64 else Width.W32
  let ba := eRegRegW (e3 ba 0x6d 0x6f 0x76) w .rdx .rax
  let ba := eSarRdx (ba.push 0x0a) is64 (if is64 then 63 else 31)
  e4 (ba.push 0x0a) 0x69 0x64 0x69 0x76

@[expose, noinline] def eDivUnsignedPfx (ba : ByteArray) : ByteArray :=
  let ba := eImmReg (e3 ba 0x6d 0x6f 0x76) .W32 .rdx 0
  e3 (ba.push 0x0a) 0x64 0x69 0x76

@[expose, noinline] def eDivCore (ba : ByteArray) (w : Width) (isSigned : Bool) (rhs : Reg64) :
    ByteArray :=
  if isSigned then
    match w with
    | .W64 => emitReg64 (e2 (eDivSignedPfx ba true) 0x71 0x20) .W64 rhs
    | _ => emitReg64 ((eWidth (eDivSignedPfx ba false) w).push 0x20) w rhs
  else
    emitReg64 ((eWidth (eDivUnsignedPfx ba) w).push 0x20) w rhs

/-! ## 5. Factored `Dir0` dispatchers (`≤ 260` directives per lowered function) -/

@[expose, noinline] def printDir0DivMulRet (d : Dir0) (out : ByteArray) : ByteArray :=
  match d with
  | .divCore w isSigned rhs => eDivCore out w isSigned rhs
  | .mulq rhs => emitReg64 (e3 (e2 out 0x6d 0x75) 0x6c 0x71 0x20) .W64 rhs
  | .ret => e3 out 0x72 0x65 0x74
  | _ => out

@[expose, noinline] def printDir0Cond (d : Dir0) (out : ByteArray) : ByteArray :=
  match d with
  | .setcc cc rd => emitReg64 ((emitCc (e3 out 0x73 0x65 0x74) cc).push 0x20) .W8 rd
  | .cmovcc w cc rd rs => eMovReg (emitCc (e4 out 0x63 0x6d 0x6f 0x76) cc) w rd w rs
  | _ => printDir0DivMulRet d out

@[expose, noinline] def printDir0CmpTest (d : Dir0) (out : ByteArray) : ByteArray :=
  match d with
  | .cmpRR w ra rb => eRegRegW (e3 out 0x63 0x6d 0x70) w ra rb
  | .testbRR ra rb => eRegRegW (e4 out 0x74 0x65 0x73 0x74) .W8 ra rb
  | _ => printDir0Cond d out

@[expose, noinline] def printDir0Shift (d : Dir0) (out : ByteArray) : ByteArray :=
  match d with
  | .shiftCl w k rd =>
    let out := e4 (eWidth (emitShiftMn out k) w) 0x20 0x25 0x63 0x6c
    emitReg64 (eCommaSp out) w rd
  | .shMaskCl imm => eImmReg (e3 out 0x61 0x6e 0x64) .W32 .rcx imm
  | _ => printDir0CmpTest d out

@[expose, noinline] def printDir0Alu (d : Dir0) (out : ByteArray) : ByteArray :=
  match d with
  | .aluRR w k rd rs => eRegRegW (emitAluMn out k) w rd rs
  | .unary w isNeg rd =>
    let out := if isNeg then e3 out 0x6e 0x65 0x67 else e3 out 0x6e 0x6f 0x74
    emitReg64 ((eWidth out w).push 0x20) w rd
  | _ => printDir0Shift d out

@[expose, noinline] def printDir0Sp (d : Dir0) (out : ByteArray) : ByteArray :=
  match d with
  | .spAdd isSub imm32 =>
    let out := if isSub then e3 out 0x73 0x75 0x62 else e3 out 0x61 0x64 0x64
    eImmReg out .W64 .rsp imm32
  | .spAddReg isSub r =>
    let out := if isSub then e3 out 0x73 0x75 0x62 else e3 out 0x61 0x64 0x64
    eRegRegW out .W64 .rsp r
  | _ => printDir0Alu d out

@[expose, noinline] def printDir0SlotIdx (d : Dir0) (out : ByteArray) : ByteArray :=
  match d with
  | .ldSlotIdx rd idx =>
    let out := eSlotIdxMem (e2 (e3 out 0x6d 0x6f 0x76) 0x71 0x20) idx
    emitReg64 (eCommaSp out) .W64 rd
  | .stSlotIdx idx rs =>
    let out := emitReg64 (e2 (e3 out 0x6d 0x6f 0x76) 0x71 0x20) .W64 rs
    eSlotIdxMem (eCommaSp out) idx
  | _ => printDir0Sp d out

@[expose, noinline] def printDir0Slot (d : Dir0) (out : ByteArray) : ByteArray :=
  match d with
  | .ldSlot rd disp =>
    let out := eSlotMem (e2 (e3 out 0x6d 0x6f 0x76) 0x71 0x20) disp
    emitReg64 (eCommaSp out) .W64 rd
  | .stSlot disp rs =>
    let out := emitReg64 (e2 (e3 out 0x6d 0x6f 0x76) 0x71 0x20) .W64 rs
    eSlotMem (eCommaSp out) disp
  | _ => printDir0SlotIdx d out

@[expose, noinline] def printDir0LdSt (d : Dir0) (out : ByteArray) : ByteArray :=
  match d with
  | .ldMem w rd base => eLdMem out w rd base
  | .stMem w base val =>
    let out := emitReg64 ((eWidth (e3 out 0x6d 0x6f 0x76) w).push 0x20) w val
    eRegMemAt (eCommaSp out) base
  | _ => printDir0Slot d out

@[expose, noinline] def printDir0Ext (d : Dir0) (out : ByteArray) : ByteArray :=
  match d with
  | .movzx32 wSrc rd rs => eMovzx32 out wSrc rd rs
  | .movsx wDst rd wSrc rs => eMovsx out wDst rd wSrc rs
  | _ => printDir0LdSt d out

@[expose, noinline] def printDir0Mem (d : Dir0) (out : ByteArray) : ByteArray :=
  match d with
  | .movRR w rd rs => eRegRegW (e3 out 0x6d 0x6f 0x76) w rd rs
  | .movRI rd imm =>
    let w := if (imm >>> 32) == 0 then Width.W32 else Width.W64
    eImmReg (e3 out 0x6d 0x6f 0x76) w rd imm
  | _ => printDir0Ext d out

end PrintDir0

/-! ## 6. Public entrypoints -/

/-- Append the AT&T x86-64 assembly bytes for a single `Dir0` (matching `Kraken.X64.toATT
(Bridge0.dir0ToAmd64 symName d)` without trailing newline) onto `out`. -/
@[expose, noinline] def printDir0Bytes (symBytes : ByteArray) (symOffs : Array Nat)
    (d : Dir0) (out : ByteArray) : ByteArray :=
  match d with
  | .label l => (PrintDir0.emitLabel0 symBytes symOffs l out).push 0x3a
  | .jmp l => PrintDir0.emitLabel0 symBytes symOffs l (PrintDir0.e4 out 0x6a 0x6d 0x70 0x20)
  | .jcc cc l =>
    let out := (PrintDir0.emitCc (out.push 0x6a) cc).push 0x20
    PrintDir0.emitLabel0 symBytes symOffs l out
  | .callSym sym =>
    let out := (PrintDir0.e4 out 0x63 0x61 0x6c 0x6c).push 0x20
    PrintDir0.emitSym symBytes symOffs sym out
  | _ => PrintDir0.printDir0Mem d out

/-- Append `'\n'`-separated AT&T x86-64 assembly bytes for `ds : List Dir0` (matching
`Kraken.X64.toATT (Bridge0.toAmd64Program symName ds)` without trailing newline) onto `out`. -/
@[expose] def printDirs0Bytes (symBytes : ByteArray) (symOffs : Array Nat)
    (ds : List Dir0) (out : ByteArray) : ByteArray :=
  match ds with
  | [] => out
  | [d] => printDir0Bytes symBytes symOffs d out
  | d :: ds' =>
    printDirs0Bytes symBytes symOffs ds' ((printDir0Bytes symBytes symOffs d out).push 0x0a)

/-- Append `'\n'`-terminated AT&T x86-64 assembly lines for `ds : List Dir0` onto `out`. -/
@[expose] def printDirs0LinesBytes (symBytes : ByteArray) (symOffs : Array Nat)
    (ds : List Dir0) (out : ByteArray) : ByteArray :=
  match ds with
  | [] => out
  | d :: ds' =>
    printDirs0LinesBytes symBytes symOffs ds' ((printDir0Bytes symBytes symOffs d out).push 0x0a)

/-- Append `.globl <sym>\n` lines for `fnSyms : List Sym0` onto `out`. -/
@[expose] def printGlobl0Bytes (symBytes : ByteArray) (symOffs : Array Nat)
    (fnSyms : List Sym0) (out : ByteArray) : ByteArray :=
  match fnSyms with
  | [] => out
  | s :: rest =>
    let out := PrintDir0.e4 (PrintDir0.e3 out 0x2e 0x67 0x6c) 0x6f 0x62 0x6c 0x20
    let out := (PrintDir0.emitSym symBytes symOffs s out).push 0x0a
    printGlobl0Bytes symBytes symOffs rest out

/-- Emit a full module (`.text\n`, `.globl <fn>\n`, and `'\n'`-terminated directive lines)
into a `ByteArray` without any `String` literals, closures, or globals. -/
@[expose] def printModule0Bytes (symBytes : ByteArray) (symOffs : Array Nat)
    (fnSyms : List Sym0) (ds : List Dir0) : ByteArray :=
  let cap : Nat := match fnSyms, ds with | [], [] => 8 | _, _ => 64
  let out := ByteArray.emptyWithCapacity cap
  let out := PrintDir0.e4 (PrintDir0.e2 out 0x2e 0x74) 0x65 0x78 0x74 0x0a
  printDirs0LinesBytes symBytes symOffs ds (printGlobl0Bytes symBytes symOffs fnSyms out)

/-! ## 7. Extracted Impure LCNF Module for `leanqbe0` Gate Verification -/

lcnf_of_lean! printDir0LcMod
  [printDir0Bytes, printDirs0Bytes, printDirs0LinesBytes, printGlobl0Bytes, printModule0Bytes]

end LeanQbe.T.Bootstrap0
