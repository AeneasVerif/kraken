module

public import LeanQbe.T.Amd64.Frame

/-!
# SysV x64 Vector Instruction Selection

Target-level `VecIsa` instantiation for System V AMD64 (`x64Vec`):
* Vector registers restricted to `mm0..mm15` so both legacy 128-bit SSE instructions (`pshufd`,
  `pshufb`, `palignr`, `pblendw`, `addps`, `subps`) and 128/256/512-bit VEX/EVEX instructions
  (`vmovdqu32`, `vpaddd`, `vprord`, `vpsrld`, `vpternlogd`) operate uniformly on the bank.
* `vecScratch := [.mm14, .mm15]`, `vecAllocatable := [.mm0 .. .mm13]`,
  `vecArgRegs := [.mm0 .. .mm7]`, `vecRetRegs := [.mm0, .mm1]`.
* `isAbiVec`: `128`-bit `i32`/`f32` vectors (`v4i32`, `v4f32`).
* `vecSlotWidth`: `some .w64` for `v2i32`/`v2f32` (`mkpair`/`unpair` bridges), `some .w128`/`.w256`/
  `.w512` for `128`/`256`/`512`-bit `i32`/`f32` vectors.
* Unaligned stack slots and memory accesses (`vmovdqu32` with `checkAlign = false`, `vmovIn`/`vmovOut`
  at `.W64`), with `movabs`/`lea` fallbacks for `≥ 2^31` slot offsets and non-imm32 displacements.
* Kernel-`rfl`-safe `supportsVecOp` matching `LegalTarget.x64` (`i32`/`f32` SIMD + `mkpair`/`unpair`
  bridges, no SHA-NI).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Amd64

/-! ## 1. Vector register bank, type predicates, and Kraken AVX wrappers -/

/-- Scratch vector registers reserved for lowering (`%xmm14`/`%ymm14`/`%zmm14`, `15`). -/
@[reducible] def x64VecScratch : List RegMm := [.mm14, .mm15]

/-- Allocatable vector registers (`mm0..mm13`). -/
@[reducible] def x64VecAllocatable : List RegMm :=
  [.mm0, .mm1, .mm2, .mm3, .mm4, .mm5, .mm6, .mm7,
   .mm8, .mm9, .mm10, .mm11, .mm12, .mm13]

/-- SysV AMD64 vector argument registers (`xmm0..xmm7`). -/
@[reducible] def x64VecArgRegs : List RegMm :=
  [.mm0, .mm1, .mm2, .mm3, .mm4, .mm5, .mm6, .mm7]

/-- SysV AMD64 vector return registers (`xmm0`, `xmm1`). -/
@[reducible] def x64VecRetRegs : List RegMm := [.mm0, .mm1]

/-- True iff `t` is a balanced tree of `i32` lanes. -/
def x64IsI32Vec : Ty → Bool
  | .bits 32 => true
  | .pair a b => a == b && x64IsI32Vec a
  | _ => false

/-- True iff `t` is a balanced tree of `f32` lanes. -/
def x64IsF32Vec : Ty → Bool
  | .float .s => true
  | .pair a b => a == b && x64IsF32Vec a
  | _ => false

/-- True iff `t` is a balanced `i32` or `f32` vector/leaf type. -/
@[reducible] def x64IsVecBits (t : Ty) : Bool :=
  x64IsI32Vec t || x64IsF32Vec t

/-- SysV `__m128i`/`__m128` ABI vector types (`v4i32`, `v4f32`). -/
def x64IsAbiVec (t : Ty) : Bool :=
  x64IsVecBits t && t.size == 128

/-- Stack-slot width for packed SIMD vectors and 64-bit `v2i32`/`v2f32` bridges. -/
def x64VecSlotWidth (t : Ty) : Option SlotWidth :=
  if x64IsVecBits t then
    match t.size with
    | 64 => some .w64
    | 128 => some .w128
    | 256 => some .w256
    | 512 => some .w512
    | _ => none
  else none

/-- Kraken `AvxWidth` used for moves and EVEX instructions at `SlotWidth`. -/
@[reducible] def x64AwOf : SlotWidth → AvxWidth
  | .w64 | .w128 => .W128
  | .w256 => .W256
  | .w512 => .W512

/-- Kraken `AvxReg` view of `r` at `x64AwOf w`. -/
@[reducible] def x64AvxRegOf (w : SlotWidth) (r : RegMm) : AvxReg (x64AwOf w) :=
  match w with
  | .w64 | .w128 => .xmm r
  | .w256 => .ymm r
  | .w512 => .zmm r

/-- 64-bit-address AVX instruction constructor at width `x64AwOf w`. -/
abbrev x64AvxI (w : SlotWidth) (op : AvxOperation (x64AwOf w)) : Instr :=
  .avx .W64 (x64AwOf w) op

/-- 64-bit-address AVX directive wrapper at width `x64AwOf w`. -/
abbrev x64Avx (w : SlotWidth) (op : AvxOperation (x64AwOf w)) : Directive :=
  .instr (x64AvxI w op)

/-- 64-bit-address 128-bit AVX/SSE instruction constructor. -/
abbrev x64Avx128I (op : AvxOperation .W128) : Instr :=
  .avx .W64 .W128 op

/-- 64-bit-address 128-bit AVX/SSE directive wrapper. -/
abbrev x64Avx128 (op : AvxOperation .W128) : Directive :=
  .instr (x64Avx128I op)

/-- True iff `d` fits in a signed 32-bit x64 displacement (`-2^31 ≤ d < 2^31`). -/
def x64FitsDisp32 (d : Int64) : Bool :=
  (d.toBitVec.setWidth 32).signExtend 64 == d.toBitVec

/-- `[rb + r10]` indexed memory operand. -/
abbrev x64AtBaseR10 (rb : Reg64) : AddrExpr :=
  { base := some (.reg rb), idx := some ⟨.r10, .W8⟩ }

/-! ## 2. Vector moves, immediates, stack slots, and memory access -/

/-- Internal instruction stream for `x64Vmov`. -/
def x64VmovIns (w : SlotWidth) (vd vs : RegMm) : List Instr :=
  [x64AvxI w (.vmovdqu32 (.avx (x64AvxRegOf w vd)) (.avx (x64AvxRegOf w vs)))]

/-- Vector register move (`vmovdqu32`), clearing upper bits above `(x64AwOf w).bits`. -/
def x64Vmov (w : SlotWidth) (vd vs : RegMm) : List Directive :=
  emitClean (x64VmovIns w vd vs)

/-- Internal instruction stream for `x64Movi64`. -/
def x64Movi64Ins (vd : RegMm) (lo : BitVec 64) : List Instr :=
  [x64MoviI .r10 lo, x64Avx128I (.vmovIn .W64 (.xmm vd) (.reg (q .r10)))]

/-- Materialize 64-bit immediate `lo` into low 64 bits of `vd` (`movabs` + `vmovq`). -/
def x64Movi64 (vd : RegMm) (lo : BitVec 64) : List Directive :=
  emitClean (x64Movi64Ins vd lo)

/-- Internal instruction stream for `x64Movi128`. -/
def x64Movi128Ins (vd tmp : RegMm) (c : BitVec 512) : List Instr :=
  [ x64MoviI .r10 (c.extractLsb' 64 64)
  , x64Avx128I (.vmovIn .W64 (.xmm vd) (.reg (q .r10)))
  , x64Avx128I (.pshufd (.avx (.xmm vd)) (.avx (.xmm vd)) (.int64 0x4e))
  , x64MoviI .r10 (c.extractLsb' 0 64)
  , x64Avx128I (.vmovIn .W64 (.xmm tmp) (.reg (q .r10)))
  , x64Avx128I (.vpternlogd (.avx (.xmm vd)) (.avx (.xmm tmp)) (.avx (.xmm tmp)) (.int64 0xFE))
  ]

/-- Materialize low 128 bits of `c` into `vd` using `tmp` (`tmp ≠ vd`), zeroing bits `128..511`. -/
def x64Movi128 (vd tmp : RegMm) (c : BitVec 512) : List Directive :=
  emitClean (x64Movi128Ins vd tmp c)

/-- Internal instruction stream for `x64VmoviWith`. -/
def x64VmoviWithIns (tmp : RegMm) (w : SlotWidth) (vd : RegMm) (c : BitVec 512) :
    Option (List Instr) :=
  match w with
  | .w64 => some (x64Movi64Ins vd (c.extractLsb' 0 64))
  | .w128 => some (x64Movi128Ins vd tmp c)
  | .w256 | .w512 =>
    let lo := c.setWidth w.bits
    let r : AvxRegOrMem (x64AwOf w) := .avx (x64AvxRegOf w vd)
    if lo == 0#(w.bits) then
      some [x64AvxI w (.vpternlogd r r r (.int64 0x00))]
    else if lo == BitVec.allOnes w.bits then
      some [x64AvxI w (.vpternlogd r r r (.int64 0xFF))]
    else none

/-- Materialize a `w`-bit immediate into `vd`, using `tmp` (`tmp ≠ vd`) at `.w128`. -/
def x64VmoviWith (tmp : RegMm) (w : SlotWidth) (vd : RegMm) (c : BitVec 512) :
    Option (List Directive) :=
  emitCleanOpt (x64VmoviWithIns tmp w vd c)

/-- Internal instruction stream for `x64Vmovi`. -/
def x64VmoviIns (w : SlotWidth) (vd : RegMm) (c : BitVec 512) : Option (List Instr) :=
  x64VmoviWithIns .mm14 w vd c

/-- Standard vector immediate materialization using `.mm14` as helper scratch. -/
def x64Vmovi (w : SlotWidth) (vd : RegMm) (c : BitVec 512) : Option (List Directive) :=
  emitCleanOpt (x64VmoviIns w vd c)

/-- Internal instruction stream for `x64SlotAddr`. -/
def x64SlotAddrIns (i : Nat) : List Instr × AddrExpr :=
  let off := 8 * i
  if x64FitsImm31 off then ([], x64AtSp (Int64.ofNat off))
  else ([x64MoviI .r10 (BitVec.ofNat 64 off)], x64AtSpR10)

/-- Address setup for stack slot `i` (`[rsp + 8*i]`), falling back to `%r10` if `8 * i ≥ 2^31`. -/
def x64SlotAddr (i : Nat) : List Directive × AddrExpr :=
  (emitClean (x64SlotAddrIns i).1, (x64SlotAddrIns i).2)

/-- Unaligned vector memory `Instr` (`vmovIn`/`vmovOut` at `.w64`, `vmovdqu32` otherwise). -/
@[reducible]
def x64VmemI (isLoad : Bool) (w : SlotWidth) (v : RegMm) (addr : AddrExpr) : Instr :=
  match w with
  | .w64 =>
    if isLoad then x64Avx128I (.vmovIn .W64 (.xmm v) (.mem addr))
    else x64Avx128I (.vmovOut .W64 (.mem addr) (.xmm v))
  | _ =>
    if isLoad then x64AvxI w (.vmovdqu32 (.avx (x64AvxRegOf w v)) (.mem addr))
    else x64AvxI w (.vmovdqu32 (.mem addr) (.avx (x64AvxRegOf w v)))

/-- Unaligned vector memory directive (`vmovIn`/`vmovOut` at `.w64`, `vmovdqu32` otherwise). -/
@[reducible]
def x64VmemDir (isLoad : Bool) (w : SlotWidth) (v : RegMm) (addr : AddrExpr) : Directive :=
  .instr (x64VmemI isLoad w v addr)

/-- Internal instruction stream for `x64VslotSt`. -/
def x64VslotStIns (w : SlotWidth) (i : Nat) (vs : RegMm) : List Instr :=
  let (pre, addr) := x64SlotAddrIns i
  pre ++ [x64VmemI false w vs addr]

/-- Store `w`-bit vector `vs` into stack slot `i` (unaligned safe, preserving flags). -/
def x64VslotSt (w : SlotWidth) (i : Nat) (vs : RegMm) : List Directive :=
  emitClean (x64VslotStIns w i vs)

/-- Internal instruction stream for `x64VslotLd`. -/
def x64VslotLdIns (w : SlotWidth) (vd : RegMm) (i : Nat) : List Instr :=
  let (pre, addr) := x64SlotAddrIns i
  pre ++ [x64VmemI true w vd addr]

/-- Load stack slot `i` into `w`-bit vector `vd` (unaligned safe, preserving flags). -/
def x64VslotLd (w : SlotWidth) (vd : RegMm) (i : Nat) : List Directive :=
  emitClean (x64VslotLdIns w vd i)

/-- Internal instruction stream for `x64AddrPrep`. -/
def x64AddrPrepIns : AddrArg Reg64 → List Instr × AddrExpr
  | .baseDisp rb disp =>
    if x64FitsDisp32 disp then ([], atDisp rb disp)
    else
      ([x64MoviI .r10 disp.toBitVec, insI (.lea (q .r10) (x64AtBaseR10 rb))], atReg .r10)
  | .baseIdxDisp rb ri sc disp =>
    if x64FitsDisp32 disp then ([], atSIB rb ri sc disp)
    else
      ([x64MoviI .r10 disp.toBitVec, insI (.lea (q .r10) (x64AtBaseR10 rb))],
        atSIB .r10 ri sc 0)
  | .imm c => ([x64MoviI .r10 c], atReg .r10)

/-- Address preparation for `AddrArg Reg64`, using `%r10` if `imm`/disp exceeds int32. -/
def x64AddrPrep (a : AddrArg Reg64) : List Directive × AddrExpr :=
  (emitClean (x64AddrPrepIns a).1, (x64AddrPrepIns a).2)

/-- Internal instruction stream for `x64Vload`. -/
def x64VloadIns (t : Ty) (vd : RegMm) (a : AddrArg Reg64) : Option (List Instr × FlagMask) :=
  if !x64AddrValid a then none
  else (x64VecSlotWidth t).map fun w =>
    let (pre, addr) := x64AddrPrepIns a
    (pre ++ [x64VmemI true w vd addr], maskNone)

/-- Unaligned memory load into `vd` (`vmovIn .W64` for 64-bit, `vmovdqu32` for 128/256/512). -/
def x64Vload (t : Ty) (vd : RegMm) (a : AddrArg Reg64) : Option (List Directive × FlagMask) :=
  emitCleanPair (x64VloadIns t vd a)

/-- Internal instruction stream for `x64Vstore`. -/
def x64VstoreIns (t : Ty) (vs : RegMm) (a : AddrArg Reg64) : Option (List Instr × FlagMask) :=
  if !x64AddrValid a then none
  else (x64VecSlotWidth t).map fun w =>
    let (pre, addr) := x64AddrPrepIns a
    (pre ++ [x64VmemI false w vs addr], maskNone)

/-- Unaligned memory store from `vs` (`vmovOut .W64` for 64-bit, `vmovdqu32` for 128/256/512). -/
def x64Vstore (t : Ty) (vs : RegMm) (a : AddrArg Reg64) : Option (List Directive × FlagMask) :=
  emitCleanPair (x64VstoreIns t vs a)

/-! ## 3. Vector opcode selection (`x64Vop` and `x64SupportsVecOp`) -/

/-- If `t` is an `i32` leaf/vector tree whose leaves all have the same `val.toNat % 32`, return it. -/
def x64UniformI32Splat? : (t : Ty) → Val t → Option Nat
  | .bits 32, x => some (x.toNat % 32)
  | .pair a b, (x, y) => do
    let cx ← x64UniformI32Splat? a x
    let cy ← x64UniformI32Splat? b y
    if cx == cy then some cx else none
  | _, _ => none

@[reducible] def x64IsPackedWidth (t : Ty) : Bool :=
  x64IsVecBits t && (t.size == 128 || t.size == 256 || t.size == 512)

@[reducible] def x64Is128Vec (t : Ty) : Bool :=
  x64IsVecBits t && t.size == 128

@[reducible] def x64IsBridgeSubVec (t : Ty) : Bool :=
  x64IsVecBits t && t.size == 64

/-- Kernel-`rfl`-safe predicate deciding supported SysV x64 SIMD operations (no SHA-NI). -/
def x64SupportsVecOp {sig rs : List Ty} (code : OpCode sig rs)
    (args : Tup (Arg (fun _ => Unit)) sig) : Bool :=
  match code, args with
  | .copy t, _ => x64IsPackedWidth t
  | .add t, _ => x64IsI32Vec t && (t.size == 128 || t.size == 256 || t.size == 512)
  | .and t, _ | .or t, _ | .xor t, _ | .not t, _ | .ternlog t _, _ => x64IsPackedWidth t
  | .rotr t, (_, .imm c, ()) | .lshr t, (_, .imm c, ()) =>
    x64IsI32Vec t && (t.size == 128 || t.size == 256 || t.size == 512) &&
      (x64UniformI32Splat? t c).isSome
  | .shufd t _, _ | .shufb t, _ | .alignr t _, _ | .blendw t _, _ => x64Is128Vec t
  | .fadd t, _ | .fsub t, _ => x64IsF32Vec t && t.size == 128
  | .mkpair (.bits 32) (.bits 32), _ => true
  | .unpair (.bits 32) (.bits 32), _ => true
  | .mkpair a b, _ => a == b && x64IsBridgeSubVec a
  | .unpair a b, _ => a == b && x64IsBridgeSubVec a
  | _, _ => false

/-- Emit unary instruction reading `src` (register) and writing `vd` (preserving flags). -/
def x64EmitUnaryIns (w : SlotWidth) (t : Ty) (vd : RegMm)
    (pa : PArg Reg64 RegMm CondCode t) (emit : RegMm → RegMm → Instr) : Option (List Instr) :=
  match pa with
  | .vec va => some [emit vd va]
  | .imm ca => (x64VmoviIns w vd ((toBits t ca).setWidth 512)).map (· ++ [emit vd vd])
  | _ => none

/-- Emit 3-operand `vpaddd` (`dst, src1, src2`) handling any `.vec`/`.imm` combination cleanly. -/
def x64EmitVpadddIns (w : SlotWidth) (t : Ty) (vd : RegMm)
    (pa pb : PArg Reg64 RegMm CondCode t) : Option (List Instr) :=
  let mk (s1 s2 : RegMm) :=
    x64AvxI w
      (.vpaddd (.avx (x64AvxRegOf w vd)) (.avx (x64AvxRegOf w s1)) (.avx (x64AvxRegOf w s2)))
  match pa, pb with
  | .vec va, .vec vb => some [mk va vb]
  | .vec va, .imm cb => (x64VmoviIns w .mm15 ((toBits t cb).setWidth 512)).map (· ++ [mk va .mm15])
  | .imm ca, .vec vb => (x64VmoviIns w .mm15 ((toBits t ca).setWidth 512)).map (· ++ [mk .mm15 vb])
  | .imm ca, .imm cb => do
    let p1 ← x64VmoviIns w vd ((toBits t ca).setWidth 512)
    let p2 ← x64VmoviIns w .mm15 ((toBits t cb).setWidth 512)
    some (p1 ++ p2 ++ [mk vd .mm15])
  | _, _ => none

/-- Emit a 2-operand in-place instruction (`dst ← op dst src`), staging inputs to prevent
clobbering when `pb = .vec vd` and handling `.imm` operands uniformly. -/
def x64EmitBinInPlaceIns (w : SlotWidth) (t : Ty) (vd : RegMm)
    (pa pb : PArg Reg64 RegMm CondCode t) (emit : RegMm → RegMm → Instr) : Option (List Instr) :=
  match pa, pb with
  | .vec va, .vec vb =>
    some (if va == vd then [emit vd vb]
      else if vb == vd then x64VmovIns w .mm15 vb ++ x64VmovIns w vd va ++ [emit vd .mm15]
      else x64VmovIns w vd va ++ [emit vd vb])
  | .vec va, .imm cb =>
    (x64VmoviIns w .mm15 ((toBits t cb).setWidth 512)).map fun p =>
      p ++ (if va == vd then [] else x64VmovIns w vd va) ++ [emit vd .mm15]
  | .imm ca, .vec vb =>
    (x64VmoviIns w vd ((toBits t ca).setWidth 512)).map fun p =>
      if vb == vd then x64VmovIns w .mm15 vb ++ p ++ [emit vd .mm15]
      else p ++ [emit vd vb]
  | .imm ca, .imm cb => do
    let p1 ← x64VmoviIns w vd ((toBits t ca).setWidth 512)
    let p2 ← x64VmoviIns w .mm15 ((toBits t cb).setWidth 512)
    some (p1 ++ p2 ++ [emit vd .mm15])
  | _, _ => none

/-- Helper: `vpternlogd` `Instr` at width `w` with immediate byte `imm`. -/
abbrev x64TernlogI (w : SlotWidth) (dst s2 s3 : RegMm) (imm : BitVec 8) : Instr :=
  x64AvxI w (.vpternlogd (.avx (x64AvxRegOf w dst)) (.avx (x64AvxRegOf w s2))
    (.avx (x64AvxRegOf w s3)) (.int64 (Int64.ofNat imm.toNat)))

/-- Helper: `vpternlogd` directive at width `w` with immediate byte `imm`. -/
def x64TernlogD (w : SlotWidth) (dst s2 s3 : RegMm) (imm : BitVec 8) : Directive :=
  .instr (x64TernlogI w dst s2 s3 imm)

/-- Reduce a 3-input `ternlog` with one `.vec` and two fixed 512-bit constant operands into
`(x &&& keep) ^^^ flip` so only one scratch vector is ever needed. -/
def x64EmitTernlog1VecIns (w : SlotWidth) (vd rx : RegMm) (f0 f1 : BitVec 512) :
    Option (List Instr) := do
  let keep := f1 ^^^ f0
  let flip := f0
  let pk ← x64VmoviIns w .mm15 keep
  let pf ← x64VmoviIns w .mm15 flip
  let prep := if rx == vd then [] else x64VmovIns w vd rx
  some (prep ++ pk ++ [x64TernlogI w vd .mm15 .mm15 0xC0] ++ pf ++
    [x64TernlogI w vd .mm15 .mm15 0x3C])

/-- Emit 3-input `vpternlogd` for arbitrary `.vec`/`.imm` operands and aliasing. -/
def x64EmitTernlogIns (w : SlotWidth) (t : Ty) (vd : RegMm) (imm : BitVec 8)
    (pa pb pc : PArg Reg64 RegMm CondCode t) : Option (List Instr) :=
  let stageOneVec (va vb : RegMm) (pimm : List Instr) : List Instr :=
    if va == vd then pimm ++ [x64TernlogI w vd vb .mm14 imm]
    else if vb != vd then pimm ++ x64VmovIns w vd va ++ [x64TernlogI w vd vb .mm14 imm]
    else pimm ++ x64VmovIns w .mm15 vd ++ x64VmovIns w vd va ++
      [x64TernlogI w vd .mm15 .mm14 imm]
  match pa, pb, pc with
  | .vec va, .vec vb, .vec vc =>
    some (if va == vd then [x64TernlogI w vd vb vc imm]
      else if vb != vd && vc != vd then x64VmovIns w vd va ++ [x64TernlogI w vd vb vc imm]
      else x64VmovIns w .mm15 vd ++ x64VmovIns w vd va ++
        [x64TernlogI w vd (if vb == vd then .mm15 else vb)
          (if vc == vd then .mm15 else vc) imm])
  | .vec va, .vec vb, .imm cc =>
    (x64VmoviWithIns .mm15 w .mm14 ((toBits t cc).setWidth 512)).map (stageOneVec va vb)
  | .vec va, .imm cb, .vec vc =>
    (x64VmoviWithIns .mm15 w .mm14 ((toBits t cb).setWidth 512)).map fun p =>
      if va == vd then p ++ [x64TernlogI w vd .mm14 vc imm]
      else if vc != vd then p ++ x64VmovIns w vd va ++ [x64TernlogI w vd .mm14 vc imm]
      else p ++ x64VmovIns w .mm15 vd ++ x64VmovIns w vd va ++
        [x64TernlogI w vd .mm14 .mm15 imm]
  | .imm ca, .vec vb, .vec vc =>
    (x64VmoviIns w vd ((toBits t ca).setWidth 512)).map fun p =>
      if vb != vd && vc != vd then p ++ [x64TernlogI w vd vb vc imm]
      else x64VmovIns w .mm15 vd ++ p ++
        [x64TernlogI w vd (if vb == vd then .mm15 else vb)
          (if vc == vd then .mm15 else vc) imm]
  | .vec va, .imm cb, .imm cc =>
    let bvB := (toBits t cb).setWidth 512
    let bvC := (toBits t cc).setWidth 512
    x64EmitTernlog1VecIns w vd va (ternaryLogic 0#512 bvB bvC imm)
      (ternaryLogic (BitVec.allOnes 512) bvB bvC imm)
  | .imm ca, .vec vb, .imm cc =>
    let bvA := (toBits t ca).setWidth 512
    let bvC := (toBits t cc).setWidth 512
    x64EmitTernlog1VecIns w vd vb (ternaryLogic bvA 0#512 bvC imm)
      (ternaryLogic bvA (BitVec.allOnes 512) bvC imm)
  | .imm ca, .imm cb, .vec vc =>
    let bvA := (toBits t ca).setWidth 512
    let bvB := (toBits t cb).setWidth 512
    x64EmitTernlog1VecIns w vd vc (ternaryLogic bvA bvB 0#512 imm)
      (ternaryLogic bvA bvB (BitVec.allOnes 512) imm)
  | .imm ca, .imm cb, .imm cc =>
    let res := ternaryLogic (toBits t ca) (toBits t cb) (toBits t cc) imm
    x64VmoviIns w vd (res.setWidth 512)
  | _, _, _ => none

/-- Lower `i32` operand into 64-bit GPR `rd` zero-extended (`movl` / `movabs`). -/
def x64LoadI32ToGprIns (rd : Reg64) : PArg Reg64 RegMm CondCode i32 → Option (List Instr)
  | .gpr r => some [ins32I (.mov (.reg (d rd)) (.reg (d r)))]
  | .imm c => some [x64MoviI rd (c.setWidth 64)]
  | _ => none

/-- Lower 64-bit vector operand into `vd` via `vmovq`/`x64Movi64Ins`. -/
def x64LoadSubVec64Ins {t : Ty} (ht : t.size = 64) (vd : RegMm) :
    PArg Reg64 RegMm CondCode t → Option (List Instr)
  | .vec r => some [x64Avx128I (.vmovq (.xmm vd) (.xmm r))]
  | .imm c => some (x64Movi64Ins vd (BitVec.cast (by omega) (toBits t c)))
  | _ => none

/-- Emit `mkpair` bridge (`i32 × i32 → v2i32` or `v2 × v2 → v4`). -/
def x64EmitMkpairIns {a b : Ty} (pas : Tup (PArg Reg64 RegMm CondCode) [a, b])
    (dsts : Tup (PDst Reg64 RegMm CondCode) [.pair a b]) : Option (List Instr × FlagMask) :=
  match a, b, pas, dsts with
  | .bits 32, .bits 32, (pa, pb, ()), (.vec vd, ()) => do
    let la ← x64LoadI32ToGprIns .r10 pa
    let lb ← x64LoadI32ToGprIns .r11 pb
    some (la ++ lb ++
      [ insI (.shl (.reg (q .r11)) (.imm8 (.int64 32)))
      , insI (.or (.reg (q .r10)) (.reg (q .r11)))
      , x64Avx128I (.vmovIn .W64 (.xmm vd) (.reg (q .r10)))
      ], maskAll)
  | a, b, (pa, pb, ()), (.vec vd, ()) =>
    if h : a = b ∧ x64IsBridgeSubVec a ∧ a.size = 64 then do
      let hb : b.size = 64 := h.1 ▸ h.2.2
      let la ← x64LoadSubVec64Ins h.2.2 .mm14 pa
      let lb ← x64LoadSubVec64Ins hb vd pb
      some (la ++ lb ++
        [ x64Avx128I (.pshufd (.avx (.xmm vd)) (.avx (.xmm vd)) (.int64 0x4e))
        , x64TernlogI .w128 vd .mm14 .mm14 0xFE
        ], maskNone)
    else none
  | _, _, _, _ => none

/-- Emit `unpair` bridge (`v2i32 → i32 × i32` or `v4 → v2 × v2`), requiring distinct outputs. -/
def x64EmitUnpairIns {a b : Ty} (pas : Tup (PArg Reg64 RegMm CondCode) [.pair a b])
    (dsts : Tup (PDst Reg64 RegMm CondCode) [a, b]) : Option (List Instr × FlagMask) :=
  match a, b, pas, dsts with
  | .bits 32, .bits 32, (pa, ()), (.gpr d0, .gpr d1, ()) =>
    if d0 == d1 then none
    else
      let prep := match pa with
        | .vec vs => some [x64Avx128I (.vmovOut .W64 (.reg (q .r10)) (.xmm vs))]
        | .imm c => some [x64MoviI .r10 (toBits (.pair i32 i32) c)]
        | _ => none
      prep.map fun lp =>
        (lp ++
          [ ins32I (.mov (.reg (d d0)) (.reg (d .r10)))
          , insI (.shr (.reg (q .r10)) (.imm8 (.int64 32)))
          , ins32I (.mov (.reg (d d1)) (.reg (d .r10)))
          ], maskAll)
  | a, b, (pa, ()), (.vec v0, .vec v1, ()) =>
    if v0 == v1 then none
    else if h : a = b ∧ x64IsBridgeSubVec a ∧ a.size = 64 then
      match pa with
      | .vec vs =>
        some ([ x64Avx128I (.pshufd (.avx (.xmm .mm14)) (.avx (.xmm vs)) (.int64 0x4e))
              , x64Avx128I (.vmovq (.xmm v0) (.xmm vs))
              , x64Avx128I (.vmovq (.xmm v1) (.xmm .mm14))
              ], maskNone)
      | .imm c =>
        let hb : b.size = 64 := h.1 ▸ h.2.2
        some (x64Movi64Ins v0 (BitVec.cast h.2.2 (toBits a c.1)) ++
          x64Movi64Ins v1 (BitVec.cast hb (toBits b c.2)), maskNone)
      | _ => none
    else none
  | _, _, _, _ => none

/-- Shared dispatcher for wide (`≥ 128`-bit) binary `vpternlogd` ops (`and`/`or`/`xor`). -/
def x64WideTernlogBinIns {t : Ty} (imm : BitVec 8)
    (pas : Tup (PArg Reg64 RegMm CondCode) [t, t])
    (dsts : Tup (PDst Reg64 RegMm CondCode) [t]) : Option (List Instr × FlagMask) :=
  match x64VecSlotWidth t, pas, dsts with
  | some w, (pa, pb, ()), (.vec vd, ()) =>
    if w == .w64 then none
    else (x64EmitBinInPlaceIns w t vd pa pb (fun d s => x64TernlogI w d s s imm)).map (·, maskNone)
  | _, _, _ => none

/-- Shared dispatcher for wide uniform-splat `i32` shift/rotate ops (`rotr`/`lshr`). -/
def x64UniformShiftI32Ins {t : Ty} (pas : Tup (PArg Reg64 RegMm CondCode) [t, t])
    (dsts : Tup (PDst Reg64 RegMm CondCode) [t])
    (mk : SlotWidth → Nat → RegMm → RegMm → Instr) : Option (List Instr × FlagMask) :=
  if !x64IsI32Vec t then none
  else match x64VecSlotWidth t, pas, dsts with
    | some w, (pa, .imm cb, ()), (.vec vd, ()) =>
      if w == .w64 then none
      else (x64UniformI32Splat? t cb).bind fun cnt =>
        (x64EmitUnaryIns w t vd pa (mk w cnt)).map (·, maskNone)
    | _, _, _ => none

/-- Shared dispatcher for 128-bit in-place binary ops (`shufb`/`alignr`/`blendw`/`fadd`/`fsub`). -/
def x64BinInPlace128Ins {t : Ty} (ok : Bool)
    (pas : Tup (PArg Reg64 RegMm CondCode) [t, t])
    (dsts : Tup (PDst Reg64 RegMm CondCode) [t])
    (emit : RegMm → RegMm → Instr) : Option (List Instr × FlagMask) :=
  if !ok then none
  else match pas, dsts with
    | (pa, pb, ()), (.vec vd, ()) => (x64EmitBinInPlaceIns .w128 t vd pa pb emit).map (·, maskNone)
    | _, _ => none

/-- Internal instruction stream for `x64Vop`. -/
def x64VopIns {sig rs : List Ty} (code : OpCode sig rs)
    (pas : Tup (PArg Reg64 RegMm CondCode) sig)
    (dsts : Tup (PDst Reg64 RegMm CondCode) rs) : Option (List Instr × FlagMask) :=
  let withWide (t : Ty) (dsts : Tup (PDst Reg64 RegMm CondCode) [t])
      (f : SlotWidth → RegMm → Option (List Instr)) : Option (List Instr × FlagMask) :=
    match x64VecSlotWidth t, dsts with
    | some w, (.vec vd, ()) => if w == .w64 then none else (f w vd).map (·, maskNone)
    | _, _ => none
  match code with
  | .copy t =>
    match x64VecSlotWidth t, pas, dsts with
    | some w, (pa, ()), (.vec vd, ()) =>
      match pa with
      | .vec vs => some (x64VmovIns w vd vs, maskNone)
      | .imm c => (x64VmoviIns w vd ((toBits t c).setWidth 512)).map (·, maskNone)
      | _ => none
    | _, _, _ => none
  | .add t =>
    if !x64IsI32Vec t then none
    else match pas with
      | (pa, pb, ()) => withWide t dsts fun w vd => x64EmitVpadddIns w t vd pa pb
  | .and _ => x64WideTernlogBinIns 0xC0 pas dsts
  | .or _ => x64WideTernlogBinIns 0xFC pas dsts
  | .xor _ => x64WideTernlogBinIns 0x3C pas dsts
  | .not t =>
    match pas with
    | (pa, ()) => withWide t dsts fun w vd =>
      x64EmitUnaryIns w t vd pa (fun d s => x64TernlogI w d s s 0x33)
  | .ternlog t imm =>
    match pas with
    | (pa, pb, pc, ()) => withWide t dsts fun w vd => x64EmitTernlogIns w t vd imm pa pb pc
  | .rotr _ =>
    x64UniformShiftI32Ins pas dsts fun w cnt d s =>
      x64AvxI w
        (.vprord (.avx (x64AvxRegOf w d)) (.avx (x64AvxRegOf w s)) (.int64 (Int64.ofNat cnt)))
  | .lshr _ =>
    x64UniformShiftI32Ins pas dsts fun w cnt d s =>
      x64AvxI w
        (.vpsrld (.avx (x64AvxRegOf w d)) (.avx (x64AvxRegOf w s)) (.int64 (Int64.ofNat cnt)))
  | .shufd t imm =>
    if !x64Is128Vec t then none
    else match pas, dsts with
      | (pa, ()), (.vec vd, ()) =>
        let emit d s :=
          x64Avx128I (.pshufd (.avx (.xmm d)) (.avx (.xmm s)) (.int64 (Int64.ofNat imm.toNat)))
        (x64EmitUnaryIns .w128 t vd pa emit).map (·, maskNone)
      | _, _ => none
  | .shufb t =>
    x64BinInPlace128Ins (x64Is128Vec t) pas dsts fun d s =>
      x64Avx128I (.pshufb (.avx (.xmm d)) (.avx (.xmm s)))
  | .alignr t imm =>
    x64BinInPlace128Ins (x64Is128Vec t) pas dsts fun d s =>
      x64Avx128I (.palignr (.avx (.xmm d)) (.avx (.xmm s)) (.int64 (Int64.ofNat imm.toNat)))
  | .blendw t imm =>
    x64BinInPlace128Ins (x64Is128Vec t) pas dsts fun d s =>
      x64Avx128I (.pblendw (.avx (.xmm d)) (.avx (.xmm s)) (.int64 (Int64.ofNat imm.toNat)))
  | .fadd t =>
    x64BinInPlace128Ins (x64IsF32Vec t && t.size == 128) pas dsts fun d s =>
      x64Avx128I (.addps (.avx (.xmm d)) (.avx (.xmm s)))
  | .fsub t =>
    x64BinInPlace128Ins (x64IsF32Vec t && t.size == 128) pas dsts fun d s =>
      x64Avx128I (.subps (.avx (.xmm d)) (.avx (.xmm s)))
  | .mkpair _ _ => x64EmitMkpairIns pas dsts
  | .unpair _ _ => x64EmitUnpairIns pas dsts
  | _ => none

/-- SysV x64 SIMD instruction selection for `OpCode`. -/
def x64Vop {sig rs : List Ty} (code : OpCode sig rs)
    (pas : Tup (PArg Reg64 RegMm CondCode) sig)
    (dsts : Tup (PDst Reg64 RegMm CondCode) rs) (_vh : VariantHint) :
    Option (List Directive × FlagMask) :=
  emitCleanPair (x64VopIns code pas dsts)

/-- SysV x64 `VecIsa` instance. -/
@[reducible] def x64Vec : VecIsa Reg64 RegMm CondCode Directive where
  vecScratch := x64VecScratch
  vecAllocatable := x64VecAllocatable
  vecArgRegs := x64VecArgRegs
  vecRetRegs := x64VecRetRegs
  isAbiVec := x64IsAbiVec
  vecSlotWidth := x64VecSlotWidth
  vmov := x64Vmov
  vmovi := x64Vmovi
  vslotSt := x64VslotSt
  vslotLd := x64VslotLd
  vop := x64Vop
  vload := x64Vload
  vstore := x64Vstore
  supportsVecOp := x64SupportsVecOp

end LeanQbe.T.Amd64
