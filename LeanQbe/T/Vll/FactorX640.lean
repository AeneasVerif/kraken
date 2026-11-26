module

public import LeanQbe.T.Vll.RegaInst
public import LeanQbe.T.Vll.X64
public import LeanQbe.T.Amd64.Targ
import LeanQbe.T.Amd64.TargLemmas
import Kraken.X64.Regs

/-!
# BedrockMach SysV x86-64 Hooks and Native Semantic Lifting (`Vll.FactorX640`)

Provides the pure data configuration and low-level lifting bridges for `LeanQbe.T.Vll.FactorX64`:
* `vllX64Vec` & `vllX64NativeHooks : VllNativeHooks x64Arch` emitting first-class `Instr x64Arch`
  wherever 1:1 parity with `x64Isa` holds and `.native` for x86-64 fused/exotic/SIMD callbacks.
* `vllX64Hooks_noLab : VllHooksNoLab x64Arch vllX64NativeHooks`.
* Straight-line and conditional-branch lifting theorems (`x64Mach_fallsTo_to_vll`,
  `x64Mach_splitJcc_to_vll`) translating `x64Mach.FallsTo` / `x64Mach.Run` obligations into
  `(vllMach x64Arch).FallsTo` / `(vllMach x64Arch).Run` via `KrakenSim` & `EffectsLockstep`.
* Clean-directive and bounded-length lemmas for all `Amd64` scalar & vector instruction builders.

Zero `Arm64` / `Kraken.AArch64` imports, zero `@[expose]` on proof theorems/lemmas.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Vll

open LeanQbe.T
open LeanQbe.T.Amd64

/-! ## 1. Pure Hooks `vllX64NativeHooks` and `VllHooksNoLab` -/

/-- Native-wrapped SysV x64 `VecIsa` over `Instr x64Arch`. -/
@[expose] def vllX64Vec : VecIsa Reg64 RegMm CondCode (Instr x64Arch) where
  vecScratch := x64Vec.vecScratch
  vecAllocatable := x64Vec.vecAllocatable
  vecArgRegs := x64Vec.vecArgRegs
  vecRetRegs := x64Vec.vecRetRegs
  isAbiVec := x64Vec.isAbiVec
  vecSlotWidth := x64Vec.vecSlotWidth
  vmov w vd vs := (x64Vec.vmov w vd vs).map .native
  vmovi w vd c := (x64Vec.vmovi w vd c).map (List.map .native)
  vslotSt w i vs := (x64Vec.vslotSt w i vs).map .native
  vslotLd w vd i := (x64Vec.vslotLd w vd i).map .native
  vop code pas dsts vh :=
    (x64Vec.vop code pas dsts vh).map fun (ds, cl) => (ds.map .native, cl)
  vload t vd a := (x64Vec.vload t vd a).map fun (ds, cl) => (ds.map .native, cl)
  vstore t vs a := (x64Vec.vstore t vs a).map fun (ds, cl) => (ds.map .native, cl)
  supportsVecOp := x64Vec.supportsVecOp

@[expose] def x64NativePair (res : Option (List _root_.Directive × FlagMask)) :
    Option (List (Instr x64Arch) × FlagMask) :=
  res.map fun (ds, cl) => (ds.map .native, cl)

@[expose] def vllX64WidthOfBits? : Nat → Option Width
  | 8 => some .w8 | 16 => some .w16 | 32 => some .w32 | 64 => some .w64 | _ => none

@[expose] def vllX64CoreAluOf? {sig rs : List Ty} : OpCode sig rs → Option (CoreAlu × Nat)
  | .add (.bits n) => some (.add, n)
  | .sub (.bits n) => some (.sub, n)
  | .and (.bits n) => some (.and, n)
  | .or  (.bits n) => some (.or, n)
  | .xor (.bits n) => some (.xor, n)
  | _ => none

/-- Hybrid `opHook`: uses first-class `Instr x64Arch` (including `sf := true` for binary ALUs
matching `x64Op` and `aluZeroOut?`) wherever exact 1:1 parity with `x64Op` holds, and wraps all
other `x64Op` sequences in `.native`. -/
@[expose] def vllX64OpHook {sig rs : List Ty} (code : OpCode sig rs)
    (pas : Tup (PArg Reg64 RegMm CondCode) sig) (dsts : Tup (PDst Reg64 RegMm CondCode) rs)
    (vh : VariantHint) : Option (List (Instr x64Arch) × FlagMask) :=
  let fb := x64NativePair (x64Op code pas dsts vh)
  match code, pas, dsts with
  | .copy .bool, (pa, ()), (.gpr _, ()) =>
    match pa with | .imm _ | .flag _ => none | _ => fb
  | .copy (.bits n), (pa, ()), (.gpr rd, ()) =>
    if x64BitWidths.contains n then
      match pa with
      | .imm _ => none
      | .gpr rs => if (n == 32 || n == 64) && rs != rd then none else fb
      | _ => fb
    else fb
  | .bitcast (.bits m) (.bits n) _, (pa, ()), (.gpr rd, ()) =>
    if x64BitWidths.contains m && x64BitWidths.contains n then
      match pa with
      | .imm _ => none
      | .gpr rs => if (m == 32 || m == 64) && rs != rd then none else fb
      | _ => fb
    else fb
  | .trunc m n, (pa, ()), (.gpr rd, ()) =>
    if m == 64 && n == 32 then
      match pa with
      | .imm _ => none
      | .gpr rs => if rs != rd then none else fb
      | _ => fb
    else fb
  | .mul (.bits n), (pa, pb, ()), (.gpr rd, ()) =>
    if n == 16 || n == 32 || n == 64 then
      match pa, pb with
      | .gpr ra, .gpr _ | .gpr ra, .imm _ => if ra == rd then none else fb
      | _, _ => fb
    else fb
  | .add (.bits n), (pa, pb, ()), (.gpr rd, ()) =>
    match vllX64WidthOfBits? n, vh, pa with
    | some w, .default, .gpr ra =>
      if ra == rd then
        match pb with
        | .gpr rb => some ([.alu .add w rd rd (.reg rb) true], maskAll)
        | .imm cb => some ([.alu .add w rd rd (.imm (cb.setWidth 64)) true], maskAll)
        | .vec _ => fb
      else fb
    | _, _, _ => fb
  | .sub (.bits n), (pa, pb, ()), (.gpr rd, ()) =>
    match vllX64WidthOfBits? n, vh, pa with
    | some w, .default, .gpr ra =>
      if ra == rd then
        match pb with
        | .gpr rb => some ([.alu .sub w rd rd (.reg rb) true], maskAll)
        | .imm cb => some ([.alu .sub w rd rd (.imm (cb.setWidth 64)) true], maskAll)
        | .vec _ => fb
      else fb
    | _, _, _ => fb
  | .and (.bits n), (pa, pb, ()), (.gpr rd, ()) =>
    match vllX64WidthOfBits? n, vh, pa with
    | some w, .default, .gpr ra =>
      if ra == rd || n == 32 || n == 64 then
        match pb with
        | .gpr rb => some ([.alu .and w rd ra (.reg rb) true], maskAll)
        | .imm cb => some ([.alu .and w rd ra (.imm (cb.setWidth 64)) true], maskAll)
        | .vec _ => fb
      else fb
    | _, _, _ => fb
  | .or (.bits n), (pa, pb, ()), (.gpr rd, ()) =>
    match vllX64WidthOfBits? n, vh, pa with
    | some w, .default, .gpr ra =>
      if ra == rd || n == 32 || n == 64 then
        match pb with
        | .gpr rb => some ([.alu .or w rd ra (.reg rb) true], maskAll)
        | .imm cb => some ([.alu .or w rd ra (.imm (cb.setWidth 64)) true], maskAll)
        | .vec _ => fb
      else fb
    | _, _, _ => fb
  | .xor (.bits n), (pa, pb, ()), (.gpr rd, ()) =>
    match vllX64WidthOfBits? n, vh, pa with
    | some w, .default, .gpr ra =>
      if ra == rd || n == 32 || n == 64 then
        match pb with
        | .gpr rb => some ([.alu .xor w rd ra (.reg rb) true], maskAll)
        | .imm cb => some ([.alu .xor w rd ra (.imm (cb.setWidth 64)) true], maskAll)
        | .vec _ => fb
      else fb
    | _, _, _ => fb
  | .cmp co (.bits n) .bool _, (pa, pb, ()), (pd, ()) =>
    if x64BitWidths.contains n then
      match pa, pb, pd with
      | .gpr _, .gpr _, .gpr _ | .gpr _, .imm _, .gpr _ => none
      | .gpr _, .gpr _, .flag cf | .gpr _, .imm _, .flag cf =>
        if cf == condOf co then none else fb
      | _, _, _ => fb
    else fb
  | _, _, _ => fb

/-- First-class `.store` for `.gpr` on valid x64 addresses, else `.native` via `x64Store`. -/
@[expose] def vllX64StoreHook (t : Ty) (pa : PArg Reg64 RegMm CondCode t) (a : AddrArg Reg64) :
    Option (List (Instr x64Arch) × FlagMask) :=
  let okTy := match t with | .bool => true | .bits n => x64BitWidths.contains n | _ => false
  if x64AddrValid a && okTy then
    match pa with | .gpr _ => none | _ => x64NativePair (x64Store t pa a)
  else x64NativePair (x64Store t pa a)

/-- First-class `loadSext` using `.load w .sx rd a` for 8/16/32-bit sign-extending loads. -/
@[expose] def vllX64LoadSext (m n : Nat) (rd : Reg64) (a : AddrArg Reg64) :
    Option (List (Instr x64Arch) × FlagMask) :=
  if !(x64AddrValid a && Nat.blt m n && Nat.ble n 64) then none else
  match m with
  | 8 => some ([.load .w8 .sx rd a], maskNone)
  | 16 => some ([.load .w16 .sx rd a], maskNone)
  | 32 => some ([.load .w32 .sx rd a], maskNone)
  | _ => none

/-- Polarity-aware `jnzGprInv?`: first-class `.jnzGpr` when `inv = false`, `.native` when `true`. -/
@[expose] def vllX64JnzGprInv (r : Reg64) (inv : Bool) (l : Sym) :
    List (Instr x64Arch) × FlagMask :=
  if inv then
    let (ds, cl) := x64JnzGpr r true l
    (ds.map .native, cl)
  else ([.jnzGpr r l], maskAll)

/-- Hybrid `VllNativeHooks x64Arch` achieving exact 1:1 `x64Isa` parity across SysV x86-64. -/
@[expose] def vllX64NativeHooks : VllNativeHooks x64Arch where
  regName := toString ∘ repr
  vregName := toString ∘ repr
  loadExt := .zx
  condOfCmp? := some ∘ condOf
  cmpFlags := x64Gpr.cmpFlags
  opHook := @vllX64OpHook
  storeHook := vllX64StoreHook
  supportsScalarOpOverride? := some @x64SupportsScalarOp
  zeroUpper32Load := true
  zeroExtLoad := true
  zeroUpper32Op := @x64ZeroUpper32Op
  elideZext32 := true
  testOp := fun w neg pa pb pd => x64NativePair (x64TestOp w neg pa pb pd)
  cmpMem := fun co w a pb pd => x64NativePair (x64CmpMem co w a pb pd)
  testMem := fun w neg a pb pd => x64NativePair (x64TestMem w neg a pb pd)
  loadSext := vllX64LoadSext
  aluMem := fun w code memRhs a pb rd => x64NativePair (x64AluMem w code memRhs a pb rd)
  zeroUpper32AluMem := true
  jnzMem := fun a inv l => x64NativePair (x64JnzMem a inv l)
  rmwMem := fun w code a pb => x64NativePair (x64RmwMem w code a pb)
  leaArith := fun w base? idx sc disp rd => x64NativePair (x64LeaArith w base? idx sc disp rd)
  zeroUpper32LeaArith := true
  jnzGprInv? := some vllX64JnzGprInv
  boolFlagOut? := @x64BoolFlagOut
  cmpFlagsOut? := x64CmpFlagsOut
  aluZeroOut? := @x64AluZeroOut
  hasTestFlags := true
  cmpMemFlagsOut? := x64CmpMemFlagsOut
  supportsAddrDisp := x64SupportsAddrDisp
  supportsAddrIdx := x64SupportsAddrIdx
  supportsTestFuse := true
  supportsCmpMem := x64SupportsCmpMem
  supportsTestMem := x64SupportsCmpMem
  vec := vllX64Vec
  legalTarget? := some x64LegalTarget

private theorem noVllLab_map_native {A : Arch} (ds : List A.Native) :
    NoVllLab (ds.map (Instr.native (A := A))) := by
  intro l hm
  obtain ⟨d, _, hd⟩ := List.mem_map.mp hm
  cases hd

private theorem noVllLab_nativePair {r : Option (List _root_.Directive × FlagMask)}
    {c : List (Instr x64Arch)} {cl : FlagMask} (h : x64NativePair r = some (c, cl)) :
    NoVllLab c := by
  cases r with
  | none => cases h
  | some p =>
    cases h
    exact noVllLab_map_native (A := x64Arch) p.1

private theorem vllX64OpHook_noLab {sig rs : List Ty} {code : OpCode sig rs}
    {pas : Tup (PArg Reg64 RegMm CondCode) sig} {dsts : Tup (PDst Reg64 RegMm CondCode) rs}
    {vh : VariantHint} {c : List (Instr x64Arch)} {cl : FlagMask}
    (h : vllX64OpHook code pas dsts vh = some (c, cl)) : NoVllLab c := by
  unfold vllX64OpHook at h
  dsimp only at h
  repeat
    first
    | contradiction
    | exact noVllLab_nativePair h
    | (cases h; exact noVllLab_one (fun _ e => by cases e))
    | split at h

/-- Structural `VllHooksNoLab` proof for `vllX64NativeHooks`. -/
theorem vllX64Hooks_noLab : VllHooksNoLab x64Arch vllX64NativeHooks where
  jnzGprInv {_ r inv l} h := by
    cases h
    dsimp only [vllX64JnzGprInv]
    cases inv <;> simp only [↓reduceIte, Bool.false_eq_true]
    · exact noVllLab_one (fun _ e => by cases e)
    · exact noVllLab_map_native (A := x64Arch) _
  opHook {_ _ _ _ _ _ _ _} h := vllX64OpHook_noLab h
  storeHook {_ _ a c cl} h := by
    dsimp only [vllX64NativeHooks, vllX64StoreHook] at h
    repeat
      first
      | contradiction
      | exact noVllLab_nativePair h
      | split at h
  testOp {_ _ _ _ _ _ _} h := noVllLab_nativePair h
  cmpMem {_ _ _ _ _ _ _} h := noVllLab_nativePair h
  testMem {_ _ _ _ _ _ _} h := noVllLab_nativePair h
  loadSext {m n r a c cl} h := by
    dsimp only [vllX64NativeHooks, vllX64LoadSext] at h
    split at h
    · cases h
    · split at h <;> cases h <;> exact noVllLab_one (fun _ e => by cases e)
  aluMem {_ _ _ _ _ _ _ _} h := noVllLab_nativePair h
  jnzMem {_ _ _ _ _} h := noVllLab_nativePair h
  rmwMem {_ _ _ _ _ _} h := noVllLab_nativePair h
  leaArith {_ _ _ _ _ _ _ _} h := noVllLab_nativePair h
  vmov _ _ _ := noVllLab_map_native (A := x64Arch) _
  vmovi w d c code h := by
    dsimp only [vllX64NativeHooks, vllX64Vec] at h
    rcases Option.map_eq_some_iff.mp h with ⟨ds, _, rfl⟩
    exact noVllLab_map_native (A := x64Arch) ds
  vslotSt _ _ _ := noVllLab_map_native (A := x64Arch) _
  vslotLd _ _ _ := noVllLab_map_native (A := x64Arch) _
  vop code pas dsts vh c cl h := by
    dsimp only [vllX64NativeHooks, vllX64Vec] at h
    rcases Option.map_eq_some_iff.mp h with ⟨⟨ds, _⟩, _, hp⟩
    cases hp; exact noVllLab_map_native (A := x64Arch) ds
  vload t d a c cl h := by
    dsimp only [vllX64NativeHooks, vllX64Vec] at h
    rcases Option.map_eq_some_iff.mp h with ⟨⟨ds, _⟩, _, hp⟩
    cases hp; exact noVllLab_map_native (A := x64Arch) ds
  vstore t s a c cl h := by
    dsimp only [vllX64NativeHooks, vllX64Vec] at h
    rcases Option.map_eq_some_iff.mp h with ⟨⟨ds, _⟩, _, hp⟩
    cases hp; exact noVllLab_map_native (A := x64Arch) ds

/-! ## 2. Clean Directives, `KrakenSim`, `EffectsLockstep`, and `x64Mach → vllMach` Lifting -/

@[expose] def constNoLab : ConstExpr → Bool
  | .int64 _ => true
  | _ => false

@[expose] def addrNoRip (a : AddrExpr) : Bool :=
  (a.base != some .rip) && constNoLab a.disp

@[expose] def rmNoRip {w : _root_.Width} : RegOrMem w → Bool
  | .reg _ => true
  | .mem a => addrNoRip a

@[expose] def opndNoRip {w : _root_.Width} : Operand w → Bool
  | .regOrMem rm => rmNoRip rm
  | .imm c => constNoLab c

@[expose] def dstNoRip {w : _root_.Width} : Dst w → Bool
  | .reg _ => true
  | .mem a => addrNoRip a

@[expose] def avxRmNoRip {aw : AvxWidth} : AvxRegOrMem aw → Bool
  | .avx _ => true
  | .mem a => addrNoRip a

@[expose] def avxDstNoRip {aw : AvxWidth} : AvxDst aw → Bool
  | .avx _ => true
  | .mem a => addrNoRip a

@[expose] def scNoLab : ShiftCountExpr → Bool
  | .cl => true
  | .imm8 c => constNoLab c

/-- Predicate identifying straight-line Kraken scalar operations independent of
`p`/`df`/`Labels`. -/
@[expose] def opStraightClean {w : _root_.Width} : Operation w → Bool
  | .nop _ => true
  | .lea _ a => addrNoRip a
  | .setcc _ d => dstNoRip d
  | .cmovcc _ _ src => rmNoRip src
  | .mulx _ _ src => rmNoRip src
  | .adcx _ src | .adox _ src => rmNoRip src
  | .cmp d s => rmNoRip d && opndNoRip s
  | .test d s => rmNoRip d && opndNoRip s
  | .mov d s => dstNoRip d && opndNoRip s
  | .movsx d s | .movzx d s => dstNoRip d && rmNoRip s
  | .not d | .inc d | .dec d | .neg d => dstNoRip d
  | .add d s | .adc d s | .sub d s | .sbb d s | .and d s | .or d s | .xor d s =>
    dstNoRip d && opndNoRip s
  | .mul s | .imul1 s | .div s | .idiv s => rmNoRip s
  | .imul d? d s =>
    (match d? with | some dst => dstNoRip dst | none => true) && rmNoRip d && opndNoRip s
  | .shl d c | .shr d c | .sar d c | .rol d c | .ror d c => dstNoRip d && scNoLab c
  | .shld d _ c | .shrd d _ c => dstNoRip d && scNoLab c
  | .bswap _ => true
  | .lzcnt _ s | .tzcnt _ s | .popcnt _ s => rmNoRip s
  | .rorx _ s c => rmNoRip s && constNoLab c
  | .shlx _ s _ | .shrx _ s _ | .sarx _ s _ => rmNoRip s
  | _ => false

/-- Predicate identifying AVX/SSE operations independent of `p`/`df`/`Labels`. -/
@[expose] def avxStraightClean {aw : AvxWidth} : AvxOperation aw → Bool
  | .vmovIn _ _ s => rmNoRip s
  | .vmovOut _ d _ => dstNoRip d
  | .vmovq _ _ | .vzeroupper => true
  | .movups d s | .vmovups d s | .movaps d s | .movdqu d s | .movdqa d s
  | .vmovdqu d s | .vmovdqu32 d s | .vmovdqa32 d s => avxDstNoRip d && avxRmNoRip s
  | .subps d s | .addps d s | .paddd d s | .pshufb d s
  | .sha256rnds2 d s | .sha256msg1 d s | .sha256msg2 d s => avxDstNoRip d && avxRmNoRip s
  | .pshufd d s c | .palignr d s c | .pblendw d s c
  | .vprord d s c | .vpsrld d s c => avxDstNoRip d && avxRmNoRip s && constNoLab c
  | .vpaddd d s1 s2 => avxDstNoRip d && avxRmNoRip s1 && avxRmNoRip s2
  | .vpternlogd d s2 s3 c => avxDstNoRip d && avxRmNoRip s2 && avxRmNoRip s3 && constNoLab c

/-- Clean straight-line Kraken `Instr` (`64`-bit address size for deterministic encoding). -/
@[expose] def instrStraightClean : _root_.Instr → Bool
  | .regular .W64 _ op => opStraightClean op
  | .avx .W64 _ aop => avxStraightClean aop
  | _ => false

/-- Clean straight-line `_root_.Directive` (every directive is an `.instr` of size `4`). -/
@[expose] def dirStraightClean : _root_.Directive → Bool
  | .instr i => instrStraightClean i
  | _ => false

/-- Construct a concrete `Reg64s` from `g : Reg64 → BitVec 64`. -/
@[expose] def regsOfFn (g : Reg64 → BitVec 64) : Reg64s where
  rax := UInt64.ofBitVec (g .rax); rbx := UInt64.ofBitVec (g .rbx)
  rcx := UInt64.ofBitVec (g .rcx); rdx := UInt64.ofBitVec (g .rdx)
  rsi := UInt64.ofBitVec (g .rsi); rdi := UInt64.ofBitVec (g .rdi)
  rsp := UInt64.ofBitVec (g .rsp); rbp := UInt64.ofBitVec (g .rbp)
  r8  := UInt64.ofBitVec (g .r8);  r9  := UInt64.ofBitVec (g .r9)
  r10 := UInt64.ofBitVec (g .r10); r11 := UInt64.ofBitVec (g .r11)
  r12 := UInt64.ofBitVec (g .r12); r13 := UInt64.ofBitVec (g .r13)
  r14 := UInt64.ofBitVec (g .r14); r15 := UInt64.ofBitVec (g .r15)

/-- Construct a concrete `RegZmms` from `v : RegMm → BitVec 512`. -/
@[expose] def zmmsOfFn (v : RegMm → BitVec 512) : RegZmms where
  zmm0  := v .mm0;  zmm1  := v .mm1;  zmm2  := v .mm2;  zmm3  := v .mm3
  zmm4  := v .mm4;  zmm5  := v .mm5;  zmm6  := v .mm6;  zmm7  := v .mm7
  zmm8  := v .mm8;  zmm9  := v .mm9;  zmm10 := v .mm10; zmm11 := v .mm11
  zmm12 := v .mm12; zmm13 := v .mm13; zmm14 := v .mm14; zmm15 := v .mm15
  zmm16 := v .mm16; zmm17 := v .mm17; zmm18 := v .mm18; zmm19 := v .mm19
  zmm20 := v .mm20; zmm21 := v .mm21; zmm22 := v .mm22; zmm23 := v .mm23
  zmm24 := v .mm24; zmm25 := v .mm25; zmm26 := v .mm26; zmm27 := v .mm27
  zmm28 := v .mm28; zmm29 := v .mm29; zmm30 := v .mm30; zmm31 := v .mm31

theorem regsOfFn_get64 (g : Reg64 → BitVec 64) (r : Reg64) : (regsOfFn g).get64 r = g r := by
  cases r <;> rfl

theorem zmmsOfFn_get512 (v : RegMm → BitVec 512) (vr : RegMm) :
    (zmmsOfFn v).get512 vr = v vr := by
  cases vr <;> rfl

/-- Embed `MachSt x64Arch` into Kraken `MachineData`. -/
@[expose] def machToKraken (sv : MachSt x64Arch) : MachineData where
  regs := regsOfFn sv.gpr
  zmms := zmmsOfFn sv.vreg
  status := sv.flags
  df := false
  dmem := sv.mem

/-- Agreement between two `MachineData` states on GPRs, ZMMs, memory, and architectural flags
(ignoring `.af`, `.df`, code position, and label tables). -/
@[expose] def KrakenSim (s₁ s₂ : MachineData) : Prop :=
  (∀ r, s₁.regs.get64 r = s₂.regs.get64 r) ∧
  (∀ vr, s₁.zmms.get512 vr = s₂.zmms.get512 vr) ∧
  s₁.dmem = s₂.dmem ∧
  s₁.status.cf = s₂.status.cf ∧ s₁.status.pf = s₂.status.pf ∧
  s₁.status.zf = s₂.status.zf ∧ s₁.status.sf = s₂.status.sf ∧
  s₁.status.of = s₂.status.of

private theorem krakenSim_refl (s : MachineData) : KrakenSim s s :=
  ⟨fun _ => rfl, fun _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem krakenSim_symm {s₁ s₂ : MachineData} (h : KrakenSim s₁ s₂) : KrakenSim s₂ s₁ :=
  ⟨fun r => (h.1 r).symm, fun vr => (h.2.1 vr).symm, h.2.2.1.symm,
    h.2.2.2.1.symm, h.2.2.2.2.1.symm, h.2.2.2.2.2.1.symm, h.2.2.2.2.2.2.1.symm,
    h.2.2.2.2.2.2.2.symm⟩

private theorem krakenSim_trans {s₁ s₂ s₃ : MachineData} (h₁ : KrakenSim s₁ s₂)
    (h₂ : KrakenSim s₂ s₃) : KrakenSim s₁ s₃ :=
  ⟨fun r => (h₁.1 r).trans (h₂.1 r), fun vr => (h₁.2.1 vr).trans (h₂.2.1 vr),
    h₁.2.2.1.trans h₂.2.2.1, h₁.2.2.2.1.trans h₂.2.2.2.1, h₁.2.2.2.2.1.trans h₂.2.2.2.2.1,
    h₁.2.2.2.2.2.1.trans h₂.2.2.2.2.2.1, h₁.2.2.2.2.2.2.1.trans h₂.2.2.2.2.2.2.1,
    h₁.2.2.2.2.2.2.2.trans h₂.2.2.2.2.2.2.2⟩

private theorem krakenSim_cond {s₁ s₂ : MachineData} (h : KrakenSim s₁ s₂) (cc : CondCode) :
    cc.interp s₁.status = cc.interp s₂.status := by
  cases cc <;> simp [CondCode.interp, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
    h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2]

private theorem krakenSim_of_archEq {sv : MachSt x64Arch} {sk : MachineData}
    (hr : ∀ r, sk.regs.get64 r = sv.gpr r) (hv : ∀ vr, sk.zmms.get512 vr = sv.vreg vr)
    (hm : sk.dmem = sv.mem) (hf : ∀ cc : CondCode, cc.interp sk.status = cc.interp sv.flags) :
    KrakenSim (machToKraken sv) sk := by
  refine ⟨fun r => (regsOfFn_get64 sv.gpr r).trans (hr r).symm,
    fun vr => (zmmsOfFn_get512 sv.vreg vr).trans (hv vr).symm, hm.symm, ?_⟩
  have hcf := hf .c
  have hpf := hf .p
  have hzf := hf .z
  have hsf := hf .s
  have hof := hf .o
  simp only [CondCode.interp] at hcf hpf hzf hsf hof
  exact ⟨hcf.symm, hpf.symm, hzf.symm, hsf.symm, hof.symm⟩

private theorem krakenSim_to_mach (sv : MachSt x64Arch) {sk : MachineData}
    (h : KrakenSim (machToKraken sv) sk) :
    (∀ r, sk.regs.get64 r = sv.gpr r) ∧ (∀ vr, sk.zmms.get512 vr = sv.vreg vr) ∧
    sk.dmem = sv.mem ∧ (∀ cc : CondCode, cc.interp sk.status = cc.interp sv.flags) := by
  refine ⟨fun r => (h.1 r).symm.trans (regsOfFn_get64 sv.gpr r),
    fun vr => (h.2.1 vr).symm.trans (zmmsOfFn_get512 sv.vreg vr), h.2.2.1.symm, fun cc => ?_⟩
  exact (krakenSim_cond h cc).symm

private theorem krakenSim_krakenToMachData (sk : MachineData) :
    KrakenSim (machToKraken (krakenToMachData sk)) sk :=
  krakenSim_of_archEq (fun _ => rfl) (fun _ => rfl) rfl (fun _ => rfl)

private theorem reg64s_eq_of_get64 {r₁ r₂ : Reg64s} (h : ∀ r, r₁.get64 r = r₂.get64 r) :
    r₁ = r₂ :=
  Reg64s.ext_get64 h

private theorem regZmms_eq_of_get512 {z₁ z₂ : RegZmms} (h : ∀ vr, z₁.get512 vr = z₂.get512 vr) :
    z₁ = z₂ := by
  cases z₁; cases z₂
  have hz : ∀ vr, _ = _ := h
  simp only [RegZmms.get512] at hz
  congr 1 <;> first
    | exact hz .mm0  | exact hz .mm1  | exact hz .mm2  | exact hz .mm3
    | exact hz .mm4  | exact hz .mm5  | exact hz .mm6  | exact hz .mm7
    | exact hz .mm8  | exact hz .mm9  | exact hz .mm10 | exact hz .mm11
    | exact hz .mm12 | exact hz .mm13 | exact hz .mm14 | exact hz .mm15
    | exact hz .mm16 | exact hz .mm17 | exact hz .mm18 | exact hz .mm19
    | exact hz .mm20 | exact hz .mm21 | exact hz .mm22 | exact hz .mm23
    | exact hz .mm24 | exact hz .mm25 | exact hz .mm26 | exact hz .mm27
    | exact hz .mm28 | exact hz .mm29 | exact hz .mm30 | exact hz .mm31

private theorem krakenSim_setReg {s₁ s₂ : MachineData} (h : KrakenSim s₁ s₂)
    {w : _root_.Width} (r : Reg w) (v : w.type) :
    KrakenSim (s₁.setReg r v) (s₂.setReg r v) := by
  have hregs : s₁.regs = s₂.regs := reg64s_eq_of_get64 h.1
  refine ⟨fun q => by simp [MachineData.setReg, hregs], h.2.1, h.2.2.1, h.2.2.2⟩

private theorem krakenSim_setAvxReg {s₁ s₂ : MachineData} (h : KrakenSim s₁ s₂)
    {aw : AvxWidth} (r : AvxReg aw) (v : aw.type) :
    KrakenSim (s₁.setAvxReg r v) (s₂.setAvxReg r v) := by
  have hzmms : s₁.zmms = s₂.zmms := regZmms_eq_of_get512 h.2.1
  refine ⟨h.1, fun vr => by simp [MachineData.setAvxReg, hzmms], h.2.2.1, h.2.2.2⟩

private theorem krakenSim_setAvxLegacyReg {s₁ s₂ : MachineData} (h : KrakenSim s₁ s₂)
    {aw : AvxWidth} (r : AvxReg aw) (v : aw.type) :
    KrakenSim (s₁.setAvxLegacyReg r v) (s₂.setAvxLegacyReg r v) := by
  have hzmms : s₁.zmms = s₂.zmms := regZmms_eq_of_get512 h.2.1
  refine ⟨h.1, fun vr => by simp [MachineData.setAvxLegacyReg, hzmms], h.2.2.1, h.2.2.2⟩

private theorem krakenSim_setDmem {s₁ s₂ : MachineData} (h : KrakenSim s₁ s₂) (m' : DataMem) :
    KrakenSim { s₁ with dmem := m' } { s₂ with dmem := m' } :=
  ⟨h.1, h.2.1, rfl, h.2.2.2⟩

private theorem krakenSim_withStatus {s₁ s₂ : MachineData} (h : KrakenSim s₁ s₂)
    {st₁ st₂ : StatusFlags} (hcf : st₁.cf = st₂.cf) (hpf : st₁.pf = st₂.pf)
    (hzf : st₁.zf = st₂.zf) (hsf : st₁.sf = st₂.sf) (hof : st₁.of = st₂.of) :
    KrakenSim { s₁ with status := st₁ } { s₂ with status := st₂ } :=
  ⟨h.1, h.2.1, h.2.2.1, hcf, hpf, hzf, hsf, hof⟩

private theorem krakenSim_withStatus_same {s₁ s₂ : MachineData} (h : KrakenSim s₁ s₂)
    (st : StatusFlags) : KrakenSim { s₁ with status := st } { s₂ with status := st } :=
  ⟨h.1, h.2.1, h.2.2.1, rfl, rfl, rfl, rfl, rfl⟩

private theorem krakenSim_from_result {s₁ s₂ : MachineData} (h : KrakenSim s₁ s₂)
    {w : Nat} (v : BitVec w) {c₁ c₂ a₁ a₂ o₁ o₂ : Bool} (hc : c₁ = c₂) (ho : o₁ = o₂) :
    KrakenSim { s₁ with status := StatusFlags.from_result v { cf := c₁, af := a₁, of := o₁ } }
      { s₂ with status := StatusFlags.from_result v { cf := c₂, af := a₂, of := o₂ } } :=
  krakenSim_withStatus h hc rfl rfl rfl ho

/-- Lockstep bisimulation over `Effects` trees differing only by `KrakenSim` (`.af`/`.df`),
program ranges `p`, and symbol tables `Labels`, excluding jumps and faults. -/
private inductive EffectsLockstep (n₁ : MachineData → Effects) (n₂ : MachineData → Effects) :
    Effects → Effects → Prop where
  | fall {s₁ s₂} : KrakenSim s₁ s₂ → EffectsLockstep n₁ n₂ (n₁ s₁) (n₂ s₂)
  | fail {e₁ e₂} : (∀ P, ¬e₁.All P) → EffectsLockstep n₁ n₂ e₁ e₂
  | undef {α} [inst : NondetSupportingType α] {c₁ c₂ : α → Effects} :
      (∀ v, EffectsLockstep n₁ n₂ (c₁ v) (c₂ v)) →
      EffectsLockstep n₁ n₂ (@Effects.undefined α inst c₁) (@Effects.undefined α inst c₂)
  | rread {sp₁ sp₂} {k₁ k₂ : Unit → Effects} :
      EffectsLockstep n₁ n₂ (k₁ ()) (k₂ ()) →
      EffectsLockstep n₁ n₂ (.require_read_access sp₁ k₁) (.require_read_access sp₂ k₂)
  | rwrite {sp₁ sp₂} {k₁ k₂ : Unit → Effects} :
      EffectsLockstep n₁ n₂ (k₁ ()) (k₂ ()) →
      EffectsLockstep n₁ n₂ (.require_write_access sp₁ k₁) (.require_write_access sp₂ k₂)
  | rexec {p₁ p₂} {k₁ k₂ : Unit → Effects} :
      EffectsLockstep n₁ n₂ (k₁ ()) (k₂ ()) →
      EffectsLockstep n₁ n₂ (.require_exec_access p₁ k₁) (.require_exec_access p₂ k₂)

private theorem effectsLockstep_exists_reaches {n₁ n₂ : MachineData → Effects} {e₁ e₂ : Effects}
    (hls : EffectsLockstep n₁ n₂ e₁ e₂) {P₁ : MachineState → Prop} (hall : e₁.All P₁)
    (hn₂ : ∀ s₂, ∃ s₂', EffectsReaches (n₂ s₂) ⟨s₂', 0⟩) :
    ∃ s₂', EffectsReaches e₂ ⟨s₂', 0⟩ := by
  induction hls with
  | fall _ => exact hn₂ _
  | fail h => exact absurd hall (h P₁)
  | @undef α inst _ _ _ ih =>
    let v : α := inst.from_hash 0
    obtain ⟨s₂', hr⟩ := ih v (hall v)
    exact ⟨s₂', .undefined hr⟩
  | rread _ ih =>
    obtain ⟨s₂', hr⟩ := ih hall
    exact ⟨s₂', .require_read hr⟩
  | rwrite _ ih =>
    obtain ⟨s₂', hr⟩ := ih hall
    exact ⟨s₂', .require_write hr⟩
  | rexec _ ih =>
    obtain ⟨s₂', hr⟩ := ih hall
    exact ⟨s₂', .require_exec hr⟩

private theorem effectsLockstep_preserves {n₁ n₂ : MachineData → Effects} {e₁ e₂ : Effects}
    (hls : EffectsLockstep n₁ n₂ e₁ e₂) {P₁ Q₁ : MachineState → Prop}
    (hall : e₁.All P₁) {s₂' : MachineData} (hr : EffectsReaches e₂ ⟨s₂', 0⟩)
    (hn : ∀ s₁ s₂, KrakenSim s₁ s₂ → (n₁ s₁).All P₁ →
      EffectsReaches (n₂ s₂) ⟨s₂', 0⟩ → ∃ st₁, P₁ st₁ ∧ Q₁ st₁ ∧ KrakenSim st₁.data s₂') :
    ∃ st₁, P₁ st₁ ∧ Q₁ st₁ ∧ KrakenSim st₁.data s₂' := by
  induction hls with
  | fall hsim => exact hn _ _ hsim hall hr
  | fail h => exact absurd hall (h P₁)
  | undef _ ih =>
    cases hr with | undefined hr' => exact ih _ (hall _) hr'
  | rread _ ih =>
    cases hr with | require_read hr' => exact ih hall hr'
  | rwrite _ ih =>
    cases hr with | require_write hr' => exact ih hall hr'
  | rexec _ ih =>
    cases hr with | require_exec hr' => exact ih hall hr'

private theorem constNoLab_interp (L : Labels) (c : ConstExpr) (hc : constNoLab c = true)
    (p : Std.Rco Int64) : ∃ i, c = .int64 i ∧ @ConstExpr.interp L c p = i := by
  cases c <;> simp only [constNoLab, Bool.false_eq_true] at hc
  · exact ⟨_, rfl, rfl⟩

private theorem constNoLab_interp_eq (L₁ L₂ : Labels) (c : ConstExpr)
    (hc : constNoLab c = true) (p₁ p₂ : Std.Rco Int64) :
    @ConstExpr.interp L₁ c p₁ = @ConstExpr.interp L₂ c p₂ := by
  obtain ⟨_, rfl, _⟩ := constNoLab_interp L₁ c hc p₁; rfl

private theorem addrNoRip_interp_eq (L₁ L₂ : Labels) (as : AddressSize)
    (a : AddrExpr) (ha : addrNoRip a = true) {s₁ s₂ : MachineData} (hs : KrakenSim s₁ s₂)
    (p₁ p₂ : Std.Rco Int64) :
    @AddrExpr.interp L₁ as a s₁.regs p₁ = @AddrExpr.interp L₂ as a s₂.regs p₂ := by
  simp only [addrNoRip, Bool.and_eq_true] at ha
  have hregs : s₁.regs = s₂.regs := reg64s_eq_of_get64 hs.1
  have hdisp := constNoLab_interp_eq L₁ L₂ a.disp ha.2 p₁ p₂
  cases hb : a.base with
  | none => dsimp only [AddrExpr.interp]; rw [hregs, hdisp, hb]
  | some b =>
    cases b with
    | reg _ => dsimp only [AddrExpr.interp]; rw [hregs, hdisp, hb]
    | rip => rw [hb] at ha; cases ha.1

private theorem lockstep_rread {n₁ n₂} (addr : BitVec 64) (bytes : UInt64)
    {k₁ k₂ : Unit → Effects} (h : EffectsLockstep n₁ n₂ (k₁ ()) (k₂ ())) :
    EffectsLockstep n₁ n₂
      (require_access require_read_access addr bytes k₁)
      (require_access require_read_access addr bytes k₂) := by
  dsimp only [require_access]; split
  · exact .rread h
  · exact .rread (.rread h)

private theorem lockstep_rwrite {n₁ n₂} (addr : BitVec 64) (bytes : UInt64)
    {k₁ k₂ : Unit → Effects} (h : EffectsLockstep n₁ n₂ (k₁ ()) (k₂ ())) :
    EffectsLockstep n₁ n₂
      (require_access require_write_access addr bytes k₁)
      (require_access require_write_access addr bytes k₂) := by
  dsimp only [require_access]; split
  · exact .rwrite h
  · exact .rwrite (.rwrite h)

private theorem lockstep_load {n₁ n₂} {s₁ s₂ : MachineData} (hs : KrakenSim s₁ s₂)
    (a : BitVec 64) (w : _root_.Width) {r₁ r₂ : w.type → MachineData → Effects}
    (h : ∀ v s₁' s₂', KrakenSim s₁' s₂' → EffectsLockstep n₁ n₂ (r₁ v s₁') (r₂ v s₂')) :
    EffectsLockstep n₁ n₂ (s₁.load a w r₁) (s₂.load a w r₂) := by
  dsimp only [MachineData.load]
  refine lockstep_rread a (UInt64.ofNat w.bytes) ?_
  rw [← hs.2.2.1]
  cases Mem.loadInt s₁.dmem a w.bytes
  · exact .fail fun _ hp => hp
  · exact h _ s₁ s₂ hs

private theorem lockstep_store {n₁ n₂} {s₁ s₂ : MachineData} (hs : KrakenSim s₁ s₂)
    (a : BitVec 64) {w : _root_.Width} (v : w.type) {r₁ r₂ : MachineData → Effects}
    (h : ∀ s₁' s₂', KrakenSim s₁' s₂' → EffectsLockstep n₁ n₂ (r₁ s₁') (r₂ s₂')) :
    EffectsLockstep n₁ n₂ (s₁.store a v r₁) (s₂.store a v r₂) := by
  dsimp only [MachineData.store]
  refine lockstep_rwrite a (UInt64.ofNat w.bytes) ?_
  rw [← hs.2.2.1]
  cases Mem.loadInt s₁.dmem a w.bytes
  · exact .fail fun _ hp => hp
  · exact h _ _ (krakenSim_setDmem hs _)

private theorem lockstep_rm (L₁ L₂ : Labels) (as : AddressSize) {n₁ n₂}
    {w : _root_.Width} (rm : RegOrMem w) (hrm : rmNoRip rm = true)
    {s₁ s₂ : MachineData} (hs : KrakenSim s₁ s₂) (p₁ p₂ : Std.Rco Int64)
    {r₁ r₂ : w.type → MachineData → Effects}
    (h : ∀ v s₁' s₂', KrakenSim s₁' s₂' → EffectsLockstep n₁ n₂ (r₁ v s₁') (r₂ v s₂')) :
    EffectsLockstep n₁ n₂
      (@RegOrMem.interp w L₁ as rm s₁ p₁ r₁) (@RegOrMem.interp w L₂ as rm s₂ p₂ r₂) := by
  cases rm with
  | reg r =>
    have hregs : s₁.regs = s₂.regs := reg64s_eq_of_get64 hs.1
    dsimp only [RegOrMem.interp]; rw [hregs]; exact h _ s₁ s₂ hs
  | mem a =>
    dsimp only [RegOrMem.interp]
    rw [addrNoRip_interp_eq L₁ L₂ as a hrm hs p₁ p₂]
    exact lockstep_load hs _ w h

private theorem lockstep_opnd (L₁ L₂ : Labels) (as : AddressSize) {n₁ n₂}
    {w : _root_.Width} (o : Operand w) (ho : opndNoRip o = true)
    {s₁ s₂ : MachineData} (hs : KrakenSim s₁ s₂) (p₁ p₂ : Std.Rco Int64)
    {r₁ r₂ : w.type → MachineData → Effects}
    (h : ∀ v s₁' s₂', KrakenSim s₁' s₂' → EffectsLockstep n₁ n₂ (r₁ v s₁') (r₂ v s₂')) :
    EffectsLockstep n₁ n₂
      (@Operand.interp w L₁ as o s₁ p₁ r₁) (@Operand.interp w L₂ as o s₂ p₂ r₂) := by
  cases o with
  | regOrMem rm => dsimp only [Operand.interp]; exact lockstep_rm L₁ L₂ as rm ho hs p₁ p₂ h
  | imm c =>
    dsimp only [Operand.interp]
    rw [constNoLab_interp_eq L₁ L₂ c ho p₁ p₂]
    exact h _ s₁ s₂ hs

private theorem lockstep_set (L₁ L₂ : Labels) (as : AddressSize) {n₁ n₂}
    {w : _root_.Width} (d : Dst w) (hd : dstNoRip d = true) (v : w.type)
    {s₁ s₂ : MachineData} (hs : KrakenSim s₁ s₂) (p₁ p₂ : Std.Rco Int64)
    {r₁ r₂ : MachineData → Effects}
    (h : ∀ s₁' s₂', KrakenSim s₁' s₂' → EffectsLockstep n₁ n₂ (r₁ s₁') (r₂ s₂')) :
    EffectsLockstep n₁ n₂
      (@MachineData.set w L₁ as s₁ d v p₁ r₁) (@MachineData.set w L₂ as s₂ d v p₂ r₂) := by
  cases d with
  | reg r => exact h _ _ (krakenSim_setReg hs r v)
  | mem a =>
    dsimp only [MachineData.set]
    rw [addrNoRip_interp_eq L₁ L₂ as a hd hs p₁ p₂]
    exact lockstep_store hs _ v h

private theorem lockstep_avxRm (L₁ L₂ : Labels) (as : AddressSize) {n₁ n₂}
    {aw : AvxWidth} (rm : AvxRegOrMem aw) (hrm : avxRmNoRip rm = true)
    {s₁ s₂ : MachineData} (hs : KrakenSim s₁ s₂) (p₁ p₂ : Std.Rco Int64) (chk : Bool)
    {r₁ r₂ : aw.type → MachineData → Effects}
    (h : ∀ v s₁' s₂', KrakenSim s₁' s₂' → EffectsLockstep n₁ n₂ (r₁ v s₁') (r₂ v s₂')) :
    EffectsLockstep n₁ n₂
      (@AvxRegOrMem.interp aw L₁ as rm s₁ p₁ r₁ chk)
      (@AvxRegOrMem.interp aw L₂ as rm s₂ p₂ r₂ chk) := by
  cases rm with
  | avx ar =>
    have hz : s₁.zmms = s₂.zmms := regZmms_eq_of_get512 hs.2.1
    dsimp only [AvxRegOrMem.interp]; rw [hz]; exact h _ s₁ s₂ hs
  | mem a =>
    dsimp only [AvxRegOrMem.interp, MachineData.loadAvx]
    rw [addrNoRip_interp_eq L₁ L₂ as a hrm hs p₁ p₂]
    split
    · exact .fail fun _ hp => hp
    · refine lockstep_rread _ _ ?_
      rw [← hs.2.2.1]
      cases Mem.loadInt s₁.dmem _ aw.bytes
      · exact .fail fun _ hp => hp
      · exact h _ s₁ s₂ hs

private theorem lockstep_setAvxCore (L₁ L₂ : Labels) (as : AddressSize) {n₁ n₂}
    {aw : AvxWidth} (leg : Bool) (d : AvxDst aw) (hd : avxDstNoRip d = true) (v : aw.type)
    {s₁ s₂ : MachineData} (hs : KrakenSim s₁ s₂) (p₁ p₂ : Std.Rco Int64) (chk : Bool)
    {r₁ r₂ : MachineData → Effects}
    (h : ∀ s₁' s₂', KrakenSim s₁' s₂' → EffectsLockstep n₁ n₂ (r₁ s₁') (r₂ s₂')) :
    EffectsLockstep n₁ n₂
      (if leg then @MachineData.setAvxLegacy aw L₁ as s₁ d v p₁ r₁ chk
        else @MachineData.setAvx aw L₁ as s₁ d v p₁ r₁ chk)
      (if leg then @MachineData.setAvxLegacy aw L₂ as s₂ d v p₂ r₂ chk
        else @MachineData.setAvx aw L₂ as s₂ d v p₂ r₂ chk) := by
  cases d with
  | avx ar =>
    cases leg
    · exact h _ _ (krakenSim_setAvxReg hs ar v)
    · exact h _ _ (krakenSim_setAvxLegacyReg hs ar v)
  | mem a =>
    have ha := addrNoRip_interp_eq L₁ L₂ as a hd hs p₁ p₂
    cases leg <;> simp only [MachineData.setAvxLegacy, MachineData.setAvx, MachineData.storeAvx,
        Bool.false_eq_true, ↓reduceIte, ha] <;> split
    · exact .fail fun _ hp => hp
    · refine lockstep_rwrite _ _ ?_
      rw [← hs.2.2.1]
      cases Mem.loadInt s₁.dmem _ aw.bytes
      · exact .fail fun _ hp => hp
      · exact h _ _ (krakenSim_setDmem hs _)
    · exact .fail fun _ hp => hp
    · refine lockstep_rwrite _ _ ?_
      rw [← hs.2.2.1]
      cases Mem.loadInt s₁.dmem _ aw.bytes
      · exact .fail fun _ hp => hp
      · exact h _ _ (krakenSim_setDmem hs _)

private theorem lockstep_avx (L₁ L₂ : Labels) (as : AddressSize) {n₁ n₂}
    {aw : AvxWidth} (aop : AvxOperation aw) (ha : avxStraightClean aop = true)
    {s₁ s₂ : MachineData} (hs : KrakenSim s₁ s₂) (p₁ p₂ : Std.Rco Int64) :
    EffectsLockstep n₁ n₂
      (@AvxOperation.interp L₁ as aw aop p₁ s₁ n₁)
      (@AvxOperation.interp L₂ as aw aop p₂ s₂ n₂) := by
  have hz : s₁.zmms = s₂.zmms := regZmms_eq_of_get512 hs.2.1
  cases aop with
  | vmovIn _ dst src =>
    dsimp only [avxStraightClean] at ha
    dsimp only [AvxOperation.interp]
    exact lockstep_rm L₁ L₂ as src ha hs p₁ p₂ fun v s₁' s₂' hs' =>
      .fall (krakenSim_setAvxReg hs' dst (v.zeroExtend _))
  | vmovOut n dst src =>
    dsimp only [avxStraightClean] at ha
    dsimp only [AvxOperation.interp]
    rw [hz]
    exact lockstep_set L₁ L₂ as dst ha ((s₂.zmms.get src).take n.bits) hs p₁ p₂ fun _ _ hs' =>
      .fall hs'
  | vmovq dst src =>
    dsimp only [AvxOperation.interp]; rw [hz]; exact .fall (krakenSim_setAvxReg hs _ _)
  | vzeroupper =>
    dsimp only [AvxOperation.interp]
    exact .fall ⟨hs.1, fun vr => by simp [hz], hs.2.2.1, hs.2.2.2⟩
  | vmovups d s | vmovdqu d s | vmovdqu32 d s =>
    simp only [avxStraightClean, Bool.and_eq_true] at ha
    dsimp only [AvxOperation.interp]
    exact lockstep_avxRm L₁ L₂ as s ha.2 hs p₁ p₂ false fun v s₁' s₂' hs' => by
      simpa only [Bool.false_eq_true, ↓reduceIte] using
        lockstep_setAvxCore L₁ L₂ as false d ha.1 v hs' p₁ p₂ false fun _ _ hs'' => .fall hs''
  | vmovdqa32 d s =>
    simp only [avxStraightClean, Bool.and_eq_true] at ha
    dsimp only [AvxOperation.interp]
    exact lockstep_avxRm L₁ L₂ as s ha.2 hs p₁ p₂ true fun v s₁' s₂' hs' => by
      simpa only [Bool.false_eq_true, ↓reduceIte] using
        lockstep_setAvxCore L₁ L₂ as false d ha.1 v hs' p₁ p₂ true fun _ _ hs'' => .fall hs''
  | vprord d s c | vpsrld d s c =>
    simp only [avxStraightClean, Bool.and_eq_true] at ha
    dsimp only [AvxOperation.interp]
    rw [constNoLab_interp_eq L₁ L₂ c ha.2 p₁ p₂]
    exact lockstep_avxRm L₁ L₂ as s ha.1.2 hs p₁ p₂ false fun v s₁' s₂' hs' => by
      simpa only [Bool.false_eq_true, ↓reduceIte] using
        lockstep_setAvxCore L₁ L₂ as false d ha.1.1 _ hs' p₁ p₂ false fun _ _ hs'' => .fall hs''
  | vpaddd d s1 s2 =>
    simp only [avxStraightClean, Bool.and_eq_true] at ha
    dsimp only [AvxOperation.interp]
    exact lockstep_avxRm L₁ L₂ as s2 ha.2 hs p₁ p₂ false fun v2 s₁' s₂' hs' =>
      lockstep_avxRm L₁ L₂ as s1 ha.1.2 hs' p₁ p₂ false fun v1 s₁'' s₂'' hs'' => by
        simpa only [Bool.false_eq_true, ↓reduceIte] using
          lockstep_setAvxCore L₁ L₂ as false d ha.1.1 (BitVec.packedBinOp 32 (· + ·) v1 v2)
            hs'' p₁ p₂ false fun _ _ hs''' => .fall hs'''
  | vpternlogd d s2 s3 c =>
    simp only [avxStraightClean, Bool.and_eq_true] at ha
    dsimp only [AvxOperation.interp]
    rw [constNoLab_interp_eq L₁ L₂ c ha.2 p₁ p₂]
    exact lockstep_avxRm L₁ L₂ as s3 ha.1.2 hs p₁ p₂ false fun v3 s₁' s₂' hs' =>
      lockstep_avxRm L₁ L₂ as s2 ha.1.1.2 hs' p₁ p₂ false fun v2 s₁'' s₂'' hs'' =>
        lockstep_avxRm L₁ L₂ as d (by cases d <;> exact ha.1.1.1) hs'' p₁ p₂ false
          fun v1 s₁''' s₂''' hs''' => by
            simpa only [Bool.false_eq_true, ↓reduceIte] using
              lockstep_setAvxCore L₁ L₂ as false d ha.1.1.1
                (BitVec.ternaryLogic v1 v2 v3 ((@ConstExpr.interp L₂ c p₂).toBitVec.take 8))
                hs''' p₁ p₂ false fun _ _ hs4 => .fall hs4
  | movups d s | movdqu d s =>
    simp only [avxStraightClean, Bool.and_eq_true] at ha
    dsimp only [AvxOperation.interp]
    exact lockstep_avxRm L₁ L₂ as s ha.2 hs p₁ p₂ false fun v s₁' s₂' hs' => by
      simpa only [↓reduceIte] using
        lockstep_setAvxCore L₁ L₂ as true d ha.1 v hs' p₁ p₂ false fun _ _ hs'' => .fall hs''
  | movaps d s | movdqa d s =>
    simp only [avxStraightClean, Bool.and_eq_true] at ha
    dsimp only [AvxOperation.interp]
    exact lockstep_avxRm L₁ L₂ as s ha.2 hs p₁ p₂ true fun v s₁' s₂' hs' => by
      simpa only [↓reduceIte] using
        lockstep_setAvxCore L₁ L₂ as true d ha.1 v hs' p₁ p₂ true fun _ _ hs'' => .fall hs''
  | pshufd d s c =>
    simp only [avxStraightClean, Bool.and_eq_true] at ha
    dsimp only [AvxOperation.interp]
    rw [constNoLab_interp_eq L₁ L₂ c ha.2 p₁ p₂]
    exact lockstep_avxRm L₁ L₂ as s ha.1.2 hs p₁ p₂ true fun v s₁' s₂' hs' => by
      simpa only [↓reduceIte] using
        lockstep_setAvxCore L₁ L₂ as true d ha.1.1
          (BitVec.shuffleDwords v ((@ConstExpr.interp L₂ c p₂).toBitVec.take 8))
          hs' p₁ p₂ false fun _ _ hs'' => .fall hs''
  | subps d s | addps d s | paddd d s | pshufb d s =>
    simp only [avxStraightClean, Bool.and_eq_true] at ha
    dsimp only [AvxOperation.interp]
    exact lockstep_avxRm L₁ L₂ as s ha.2 hs p₁ p₂ true fun v s₁' s₂' hs' =>
      lockstep_avxRm L₁ L₂ as d (by cases d <;> exact ha.1) hs' p₁ p₂ false
        fun v2 s₁'' s₂'' hs'' => by
          simpa only [↓reduceIte] using
            lockstep_setAvxCore L₁ L₂ as true d ha.1 _ hs'' p₁ p₂ false fun _ _ hs''' => .fall hs'''
  | sha256rnds2 d s =>
    simp only [avxStraightClean, Bool.and_eq_true] at ha
    dsimp only [AvxOperation.interp]
    exact lockstep_avxRm L₁ L₂ as s ha.2 hs p₁ p₂ true fun v s₁' s₂' hs' =>
      lockstep_avxRm L₁ L₂ as d (by cases d <;> exact ha.1) hs' p₁ p₂ false
        fun v2 s₁'' s₂'' hs'' => by
          have hz'' : s₁''.zmms = s₂''.zmms := regZmms_eq_of_get512 hs''.2.1
          rw [hz'']
          simpa only [↓reduceIte] using
            lockstep_setAvxCore L₁ L₂ as true d ha.1 _ hs'' p₁ p₂ false fun _ _ hs''' => .fall hs'''
  | sha256msg1 d s | sha256msg2 d s =>
    simp only [avxStraightClean, Bool.and_eq_true] at ha
    dsimp only [AvxOperation.interp]
    exact lockstep_avxRm L₁ L₂ as s ha.2 hs p₁ p₂ true fun v s₁' s₂' hs' =>
      lockstep_avxRm L₁ L₂ as d (by cases d <;> exact ha.1) hs' p₁ p₂ false
        fun v2 s₁'' s₂'' hs'' => by
          simpa only [↓reduceIte] using
            lockstep_setAvxCore L₁ L₂ as true d ha.1 _ hs'' p₁ p₂ false fun _ _ hs''' => .fall hs'''
  | palignr d s c | pblendw d s c =>
    simp only [avxStraightClean, Bool.and_eq_true] at ha
    dsimp only [AvxOperation.interp]
    rw [constNoLab_interp_eq L₁ L₂ c ha.2 p₁ p₂]
    exact lockstep_avxRm L₁ L₂ as s ha.1.2 hs p₁ p₂ true fun v s₁' s₂' hs' =>
      lockstep_avxRm L₁ L₂ as d (by cases d <;> exact ha.1.1) hs' p₁ p₂ false
        fun v2 s₁'' s₂'' hs'' => by
          simpa only [↓reduceIte] using
            lockstep_setAvxCore L₁ L₂ as true d ha.1.1 _ hs'' p₁ p₂ false fun _ _ hs''' =>
              .fall hs'''

private theorem scNoLab_interp (L₁ L₂ : Labels) (c : ShiftCountExpr)
    (hc : scNoLab c = true) {s₁ s₂ : MachineData} (hs : KrakenSim s₁ s₂)
    (p₁ p₂ : Std.Rco Int64) (w : _root_.Width) :
    @ShiftCountExpr.interp L₁ c s₁ p₁ = @ShiftCountExpr.interp L₂ c s₂ p₂ ∧
    @ShiftCountExpr.interpMasked L₁ c s₁ p₁ w = @ShiftCountExpr.interpMasked L₂ c s₂ p₂ w := by
  have hregs : s₁.regs = s₂.regs := reg64s_eq_of_get64 hs.1
  cases c with
  | cl => simp [ShiftCountExpr.interp, ShiftCountExpr.interpMasked, hregs]
  | imm8 ce =>
    have hce := constNoLab_interp_eq L₁ L₂ ce hc p₁ p₂
    simp [ShiftCountExpr.interp, ShiftCountExpr.interpMasked, hce]

private theorem lockstep_op_hi (L₁ L₂ : Labels) (as : AddressSize) {n₁ n₂ j₁ j₂}
    {w : _root_.Width} (op : Operation w) (hop : opStraightClean op = true)
    {s₁ s₂ : MachineData} (hs : KrakenSim s₁ s₂) (p₁ p₂ : Std.Rco Int64) :
    EffectsLockstep n₁ n₂
      (@Operation.interp L₁ as w op p₁ s₁ n₁ j₁)
      (@Operation.interp L₂ as w op p₂ s₂ n₂ j₂) := by
  have hregs : s₁.regs = s₂.regs := reg64s_eq_of_get64 hs.1
  have hcond : ∀ cc : CondCode, cc.interp s₁.status = cc.interp s₂.status := krakenSim_cond hs
  cases op with
  | nop _ => exact .fall hs
  | lea d a =>
    dsimp only [opStraightClean] at hop
    dsimp only [Operation.interp]
    rw [addrNoRip_interp_eq L₁ L₂ as a hop hs p₁ p₂]
    exact .fall (krakenSim_setReg hs d _)
  | setcc cc d =>
    dsimp only [opStraightClean] at hop
    dsimp only [Operation.interp]; rw [hcond cc]
    exact lockstep_set L₁ L₂ as d hop (BitVec.ofNat w.bits (cc.interp s₂.status).toNat)
      hs p₁ p₂ fun _ _ hs' => .fall hs'
  | cmovcc cc d s =>
    dsimp only [opStraightClean] at hop
    dsimp only [Operation.interp]
    exact lockstep_rm L₁ L₂ as s hop hs p₁ p₂ fun v s₁' s₂' hs' => by
      have hr' : s₁'.regs = s₂'.regs := reg64s_eq_of_get64 hs'.1
      rw [krakenSim_cond hs' cc, hr']
      exact .fall (krakenSim_setReg hs' d _)
  | mulx hi lo src =>
    dsimp only [opStraightClean] at hop
    dsimp only [Operation.interp]
    exact lockstep_rm L₁ L₂ as src hop hs p₁ p₂ fun v s₁' s₂' hs' => by
      have hr' : s₁'.regs = s₂'.regs := reg64s_eq_of_get64 hs'.1
      rw [hr']
      exact .fall (krakenSim_setReg (krakenSim_setReg hs' lo _) hi _)
  | adcx d src =>
    dsimp only [opStraightClean] at hop
    dsimp only [Operation.interp]
    exact lockstep_rm L₁ L₂ as src hop hs p₁ p₂ fun v s₁' s₂' hs' => by
      have hr' : s₁'.regs = s₂'.regs := reg64s_eq_of_get64 hs'.1
      dsimp only [Reg.interp]
      rw [hr', hs'.2.2.2.1]
      exact .fall ⟨fun _ => rfl, hs'.2.1, hs'.2.2.1,
        rfl, hs'.2.2.2.2.1, hs'.2.2.2.2.2.1, hs'.2.2.2.2.2.2.1, hs'.2.2.2.2.2.2.2⟩
  | adox d src =>
    dsimp only [opStraightClean] at hop
    dsimp only [Operation.interp]
    exact lockstep_rm L₁ L₂ as src hop hs p₁ p₂ fun v s₁' s₂' hs' => by
      have hr' : s₁'.regs = s₂'.regs := reg64s_eq_of_get64 hs'.1
      dsimp only [Reg.interp]
      rw [hr', hs'.2.2.2.2.2.2.2]
      exact .fall ⟨fun _ => rfl, hs'.2.1, hs'.2.2.1,
        hs'.2.2.2.1, hs'.2.2.2.2.1, hs'.2.2.2.2.2.1, hs'.2.2.2.2.2.2.1, rfl⟩
  | cmp a b =>
    simp only [opStraightClean, Bool.and_eq_true] at hop
    dsimp only [Operation.interp]
    exact lockstep_rm L₁ L₂ as a hop.1 hs p₁ p₂ fun va s₁' s₂' hs' =>
      lockstep_opnd L₁ L₂ as b hop.2 hs' p₁ p₂ fun vb s₁'' s₂'' hs'' =>
        .fall (krakenSim_from_result hs'' (va - vb) rfl rfl)
  | test a b =>
    simp only [opStraightClean, Bool.and_eq_true] at hop
    dsimp only [Operation.interp]
    exact lockstep_rm L₁ L₂ as a hop.1 hs p₁ p₂ fun va s₁' s₂' hs' =>
      lockstep_opnd L₁ L₂ as b hop.2 hs' p₁ p₂ fun vb s₁'' s₂'' hs'' =>
        .undef fun af => .fall (krakenSim_from_result hs'' (va &&& vb) rfl rfl)
  | mov d s =>
    simp only [opStraightClean, Bool.and_eq_true] at hop
    dsimp only [Operation.interp]
    exact lockstep_opnd L₁ L₂ as s hop.2 hs p₁ p₂ fun v s₁' s₂' hs' =>
      lockstep_set L₁ L₂ as d hop.1 v hs' p₁ p₂ fun _ _ hs'' => .fall hs''
  | movsx d s =>
    simp only [opStraightClean, Bool.and_eq_true] at hop
    dsimp only [Operation.interp]
    exact lockstep_rm L₁ L₂ as s hop.2 hs p₁ p₂ fun v s₁' s₂' hs' =>
      lockstep_set L₁ L₂ as d hop.1 (v.signExtend w.bits) hs' p₁ p₂ fun _ _ hs'' => .fall hs''
  | movzx d s =>
    simp only [opStraightClean, Bool.and_eq_true] at hop
    dsimp only [Operation.interp]
    exact lockstep_rm L₁ L₂ as s hop.2 hs p₁ p₂ fun v s₁' s₂' hs' =>
      lockstep_set L₁ L₂ as d hop.1 (v.zeroExtend w.bits) hs' p₁ p₂ fun _ _ hs'' => .fall hs''
  | not d =>
    dsimp only [opStraightClean] at hop
    dsimp only [Operation.interp]
    exact lockstep_rm L₁ L₂ as d hop hs p₁ p₂ fun v s₁' s₂' hs' =>
      lockstep_set L₁ L₂ as d hop (~~~v) hs' p₁ p₂ fun _ _ hs'' => .fall hs''
  | inc d =>
    dsimp only [opStraightClean] at hop
    dsimp only [Operation.interp]
    exact lockstep_rm L₁ L₂ as d hop hs p₁ p₂ fun v s₁' s₂' hs' =>
      lockstep_set L₁ L₂ as d hop (v + 1) (krakenSim_from_result hs' (v + 1) hs'.2.2.2.1 rfl)
        p₁ p₂ fun _ _ hs'' => .fall hs''
  | dec d =>
    dsimp only [opStraightClean] at hop
    dsimp only [Operation.interp]
    exact lockstep_rm L₁ L₂ as d hop hs p₁ p₂ fun v s₁' s₂' hs' =>
      lockstep_set L₁ L₂ as d hop (v - 1) (krakenSim_from_result hs' (v - 1) hs'.2.2.2.1 rfl)
        p₁ p₂ fun _ _ hs'' => .fall hs''
  | neg d =>
    dsimp only [opStraightClean] at hop
    dsimp only [Operation.interp]
    exact lockstep_rm L₁ L₂ as d hop hs p₁ p₂ fun v s₁' s₂' hs' =>
      lockstep_set L₁ L₂ as d hop (-v) (krakenSim_from_result hs' (-v) rfl rfl) p₁ p₂
        fun _ _ hs'' => .fall hs''
  | add d s | sub d s =>
    simp only [opStraightClean, Bool.and_eq_true] at hop
    dsimp only [Operation.interp]
    exact lockstep_opnd L₁ L₂ as s hop.2 hs p₁ p₂ fun a s₁' s₂' hs' =>
      lockstep_rm L₁ L₂ as d hop.1 hs' p₁ p₂ fun b s₁'' s₂'' hs'' =>
        lockstep_set L₁ L₂ as d hop.1 _ (krakenSim_from_result hs'' _ rfl rfl) p₁ p₂
          fun _ _ hs''' => .fall hs'''
  | adc d s | sbb d s =>
    simp only [opStraightClean, Bool.and_eq_true] at hop
    dsimp only [Operation.interp]
    exact lockstep_opnd L₁ L₂ as s hop.2 hs p₁ p₂ fun a s₁' s₂' hs' =>
      lockstep_rm L₁ L₂ as d hop.1 hs' p₁ p₂ fun b s₁'' s₂'' hs'' => by
        rw [hs''.2.2.2.1]
        exact lockstep_set L₁ L₂ as d hop.1 _ (krakenSim_from_result hs'' _ rfl rfl) p₁ p₂
          fun _ _ hs''' => .fall hs'''
  | and d s | or d s | xor d s =>
    simp only [opStraightClean, Bool.and_eq_true] at hop
    dsimp only [Operation.interp]
    exact lockstep_rm L₁ L₂ as d hop.1 hs p₁ p₂ fun a s₁' s₂' hs' =>
      lockstep_opnd L₁ L₂ as s hop.2 hs' p₁ p₂ fun b s₁'' s₂'' hs'' =>
        .undef fun af =>
          lockstep_set L₁ L₂ as d hop.1 _ (krakenSim_from_result hs'' _ rfl rfl) p₁ p₂
            fun _ _ hs''' => .fall hs'''
  | mul s | imul1 s =>
    dsimp only [opStraightClean] at hop
    cases w <;>
      simp only [Operation.interp, show (Width.W8 == .W8) = true from rfl,
        show (Width.W16 == .W8) = false from rfl, show (Width.W32 == .W8) = false from rfl,
        show (Width.W64 == .W8) = false from rfl, Bool.false_eq_true, ↓reduceIte] <;>
      (rw [hregs]; exact lockstep_rm L₁ L₂ as s hop hs p₁ p₂ fun b s₁' s₂' hs' =>
        .undef fun sf => .undef fun zf => .undef fun af => .undef fun pf =>
          .fall (krakenSim_withStatus (by first
            | exact krakenSim_setReg hs' _ _
            | exact krakenSim_setReg (krakenSim_setReg hs' _ _) _ _) rfl rfl rfl rfl rfl))
  | imul d? d s =>
    simp only [opStraightClean, Bool.and_eq_true] at hop
    dsimp only [Operation.interp]
    exact lockstep_rm L₁ L₂ as d hop.1.2 hs p₁ p₂ fun a s₁' s₂' hs' =>
      lockstep_opnd L₁ L₂ as s hop.2 hs' p₁ p₂ fun b s₁'' s₂'' hs'' => by
        cases d? with
        | none =>
          exact lockstep_set L₁ L₂ as d hop.1.2 (a * b) hs'' p₁ p₂ fun _ _ hs''' =>
            .undef fun sf => .undef fun zf => .undef fun af => .undef fun pf =>
              .fall (krakenSim_withStatus hs''' rfl rfl rfl rfl rfl)
        | some dst =>
          exact lockstep_set L₁ L₂ as dst hop.1.1 (a * b) hs'' p₁ p₂ fun _ _ hs''' =>
            .undef fun sf => .undef fun zf => .undef fun af => .undef fun pf =>
              .fall (krakenSim_withStatus hs''' rfl rfl rfl rfl rfl)
  | div s | idiv s =>
    dsimp only [opStraightClean] at hop
    cases w <;>
      simp only [Operation.interp, show (Width.W8 == .W8) = true from rfl,
        show (Width.W16 == .W8) = false from rfl, show (Width.W32 == .W8) = false from rfl,
        show (Width.W64 == .W8) = false from rfl, Bool.false_eq_true, ↓reduceIte] <;>
      exact lockstep_rm L₁ L₂ as s hop hs p₁ p₂ fun v s₁' s₂' hs' => by
        have hr' : s₁'.regs = s₂'.regs := reg64s_eq_of_get64 hs'.1
        rw [hr']
        split
        · exact .fail fun _ hp => hp
        · exact .undef fun st => .fall (krakenSim_withStatus_same (by first
            | exact krakenSim_setReg hs' _ _
            | exact krakenSim_setReg (krakenSim_setReg hs' _ _) _ _) st)
  | shl d c | shr d c =>
    simp only [opStraightClean, Bool.and_eq_true] at hop
    dsimp only [Operation.interp]
    exact lockstep_rm L₁ L₂ as d hop.1 hs p₁ p₂ fun a s₁' s₂' hs' => by
      rw [(scNoLab_interp L₁ L₂ c hop.2 hs' p₁ p₂ w).2]
      split
      · exact lockstep_set L₁ L₂ as d hop.1 a hs' p₁ p₂ fun _ _ hs'' => .fall hs''
      · exact .undef fun af => by
          split
          · split
            · exact lockstep_set L₁ L₂ as d hop.1 _ (krakenSim_from_result hs' _ rfl rfl) p₁ p₂
                fun _ _ hs'' => .fall hs''
            · exact .undef fun of =>
                lockstep_set L₁ L₂ as d hop.1 _ (krakenSim_from_result hs' _ rfl rfl) p₁ p₂
                  fun _ _ hs'' => .fall hs''
          · exact .undef fun cf => by
              split
              · exact lockstep_set L₁ L₂ as d hop.1 _ (krakenSim_from_result hs' _ rfl rfl) p₁ p₂
                  fun _ _ hs'' => .fall hs''
              · exact .undef fun of =>
                  lockstep_set L₁ L₂ as d hop.1 _ (krakenSim_from_result hs' _ rfl rfl) p₁ p₂
                    fun _ _ hs'' => .fall hs''
  | sar d c =>
    simp only [opStraightClean, Bool.and_eq_true] at hop
    dsimp only [Operation.interp]
    exact lockstep_rm L₁ L₂ as d hop.1 hs p₁ p₂ fun a s₁' s₂' hs' => by
      rw [(scNoLab_interp L₁ L₂ c hop.2 hs' p₁ p₂ w).2]
      split
      · exact lockstep_set L₁ L₂ as d hop.1 a hs' p₁ p₂ fun _ _ hs'' => .fall hs''
      · exact .undef fun af => by
          split
          · exact lockstep_set L₁ L₂ as d hop.1 _ (krakenSim_from_result hs' _ rfl rfl) p₁ p₂
              fun _ _ hs'' => .fall hs''
          · exact .undef fun of =>
              lockstep_set L₁ L₂ as d hop.1 _ (krakenSim_from_result hs' _ rfl rfl) p₁ p₂
                fun _ _ hs'' => .fall hs''
  | rol d c | ror d c =>
    simp only [opStraightClean, Bool.and_eq_true] at hop
    dsimp only [Operation.interp]
    refine lockstep_rm L₁ L₂ as d hop.1 hs p₁ p₂ fun a s₁' s₂' hs' => ?_
    rw [(scNoLab_interp L₁ L₂ c hop.2 hs' p₁ p₂ w).2]
    split
    · exact lockstep_set L₁ L₂ as d hop.1 a hs' p₁ p₂ fun _ _ hs'' => .fall hs''
    · split
      · refine lockstep_set L₁ L₂ as d hop.1 _ ?_ p₁ p₂ fun _ _ hs'' => .fall hs''
        exact krakenSim_withStatus hs' rfl hs'.2.2.2.2.1 hs'.2.2.2.2.2.1 hs'.2.2.2.2.2.2.1 rfl
      · refine .undef fun of => ?_
        refine lockstep_set L₁ L₂ as d hop.1 _ ?_ p₁ p₂ fun _ _ hs'' => .fall hs''
        exact krakenSim_withStatus hs' rfl hs'.2.2.2.2.1 hs'.2.2.2.2.2.1 hs'.2.2.2.2.2.2.1 rfl
  | shld d src c | shrd d src c =>
    simp only [opStraightClean, Bool.and_eq_true] at hop
    dsimp only [Operation.interp, Reg.interp]
    refine lockstep_rm L₁ L₂ as d hop.1 hs p₁ p₂ fun a s₁' s₂' hs' => ?_
    have hregs' : s₁'.regs = s₂'.regs := reg64s_eq_of_get64 hs'.1
    rw [(scNoLab_interp L₁ L₂ c hop.2 hs' p₁ p₂ w).2]
    split
    · exact lockstep_set L₁ L₂ as d hop.1 _ hs' p₁ p₂ fun _ _ hs'' => .fall hs''
    · by_cases hgt : c.interpMasked s₂' p₂ w > w.bits
      · simp only [hgt, ↓reduceIte]
        exact .undef fun st => .undef fun v =>
          lockstep_set L₁ L₂ as d hop.1 v (krakenSim_withStatus_same hs' st) p₁ p₂
            fun _ _ hs'' => .fall hs''
      · have hsrc : s₁'.regs.get src = s₂'.regs.get src := by rw [hregs']
        simp only [hgt, ↓reduceIte]
        refine .undef fun af => ?_
        split
        · rw [hsrc]
          refine lockstep_set L₁ L₂ as d hop.1 _ ?_ p₁ p₂ fun _ _ hs'' => .fall hs''
          exact krakenSim_from_result hs' _ rfl rfl
        · refine .undef fun of => ?_
          rw [hsrc]
          refine lockstep_set L₁ L₂ as d hop.1 _ ?_ p₁ p₂ fun _ _ hs'' => .fall hs''
          exact krakenSim_from_result hs' _ rfl rfl
  | bswap r =>
    cases w <;> dsimp only [Operation.interp]
    · exact @EffectsLockstep.undef _ _ _ (.bitvec .W8) _ _ fun v => .fall (krakenSim_setReg hs _ v)
    · exact @EffectsLockstep.undef _ _ _ (.bitvec .W16) _ _ fun v =>
        .fall (krakenSim_setReg hs _ v)
    · rw [hregs]; exact .fall (krakenSim_setReg hs _ _)
    · rw [hregs]; exact .fall (krakenSim_setReg hs _ _)
  | lzcnt dst s | tzcnt dst s =>
    dsimp only [opStraightClean] at hop
    cases w <;> dsimp only [Operation.interp]
    · exact @EffectsLockstep.undef _ _ _ (.bitvec .W8) _ _ fun v =>
        .undef fun st => .fall (krakenSim_withStatus_same (krakenSim_setReg hs dst v) st)
    · exact lockstep_rm L₁ L₂ as s hop hs p₁ p₂ fun _ s₁' s₂' hs' =>
        .undef fun pf => .undef fun af => .undef fun sf => .undef fun of =>
          .fall (krakenSim_withStatus (krakenSim_setReg hs' dst _) rfl rfl rfl rfl rfl)
    · exact lockstep_rm L₁ L₂ as s hop hs p₁ p₂ fun _ s₁' s₂' hs' =>
        .undef fun pf => .undef fun af => .undef fun sf => .undef fun of =>
          .fall (krakenSim_withStatus (krakenSim_setReg hs' dst _) rfl rfl rfl rfl rfl)
    · exact lockstep_rm L₁ L₂ as s hop hs p₁ p₂ fun _ s₁' s₂' hs' =>
        .undef fun pf => .undef fun af => .undef fun sf => .undef fun of =>
          .fall (krakenSim_withStatus (krakenSim_setReg hs' dst _) rfl rfl rfl rfl rfl)
  | popcnt dst s =>
    dsimp only [opStraightClean] at hop
    cases w <;> dsimp only [Operation.interp]
    · exact @EffectsLockstep.undef _ _ _ (.bitvec .W8) _ _ fun v =>
        .undef fun st => .fall (krakenSim_withStatus_same (krakenSim_setReg hs dst v) st)
    · exact lockstep_rm L₁ L₂ as s hop hs p₁ p₂ fun _ s₁' s₂' hs' =>
        .fall (krakenSim_withStatus (krakenSim_setReg hs' dst _) rfl rfl rfl rfl rfl)
    · exact lockstep_rm L₁ L₂ as s hop hs p₁ p₂ fun _ s₁' s₂' hs' =>
        .fall (krakenSim_withStatus (krakenSim_setReg hs' dst _) rfl rfl rfl rfl rfl)
    · exact lockstep_rm L₁ L₂ as s hop hs p₁ p₂ fun _ s₁' s₂' hs' =>
        .fall (krakenSim_withStatus (krakenSim_setReg hs' dst _) rfl rfl rfl rfl rfl)
  | rorx dst s c =>
    simp only [opStraightClean, Bool.and_eq_true] at hop
    cases w <;> dsimp only [Operation.interp]
    · exact @EffectsLockstep.undef _ _ _ (.bitvec .W8) _ _ fun v => .fall (krakenSim_setReg hs _ v)
    · exact @EffectsLockstep.undef _ _ _ (.bitvec .W16) _ _ fun v =>
        .fall (krakenSim_setReg hs _ v)
    · rw [constNoLab_interp_eq L₁ L₂ c hop.2 p₁ p₂]
      exact lockstep_rm L₁ L₂ as s hop.1 hs p₁ p₂ fun _ s₁' s₂' hs' =>
        .fall (krakenSim_setReg hs' dst _)
    · rw [constNoLab_interp_eq L₁ L₂ c hop.2 p₁ p₂]
      exact lockstep_rm L₁ L₂ as s hop.1 hs p₁ p₂ fun _ s₁' s₂' hs' =>
        .fall (krakenSim_setReg hs' dst _)
  | shlx dst s1 s2 | shrx dst s1 s2 | sarx dst s1 s2 =>
    dsimp only [opStraightClean] at hop
    cases w <;> dsimp only [Operation.interp]
    · exact @EffectsLockstep.undef _ _ _ (.bitvec .W8) _ _ fun v => .fall (krakenSim_setReg hs _ v)
    · exact @EffectsLockstep.undef _ _ _ (.bitvec .W16) _ _ fun v =>
        .fall (krakenSim_setReg hs _ v)
    · exact lockstep_rm L₁ L₂ as s1 hop hs p₁ p₂ fun _ s₁' s₂' hs' => by
        rw [reg64s_eq_of_get64 hs'.1]; exact .fall (krakenSim_setReg hs' dst _)
    · exact lockstep_rm L₁ L₂ as s1 hop hs p₁ p₂ fun _ s₁' s₂' hs' => by
        rw [reg64s_eq_of_get64 hs'.1]; exact .fall (krakenSim_setReg hs' dst _)
  | movs _ | stos _ | push _ | pop _ | cld | std | nopalign _ _
  | rcl _ _ | rcr _ _ | jcc _ _ | jmp _ | call _ | ret =>
    cases hop

private theorem dir_interp_lockstep (L₁ L₂ : Labels) {n₁ n₂ j₁ j₂}
    (d : _root_.Directive) (hd : dirStraightClean d = true)
    {s₁ s₂ : MachineData} (hs : KrakenSim s₁ s₂) (p₁ p₂ : Std.Rco Int64) :
    EffectsLockstep n₁ n₂ (@_root_.Directive.interp L₁ d s₁ p₁ n₁ j₁)
      (@_root_.Directive.interp L₂ d s₂ p₂ n₂ j₂) := by
  cases d with
  | label _ | byteArray _ | word _ _ => cases hd
  | instr i =>
    cases i with
    | regular asz w op =>
      cases asz <;> try cases hd
      exact .rexec (@lockstep_op_hi L₁ L₂ ⟨.W64⟩ n₁ n₂ j₁ j₂ w op hd s₁ s₂ hs p₁ p₂)
    | avx asz aw aop =>
      cases asz <;> try cases hd
      exact .rexec (@lockstep_avx L₁ L₂ ⟨.W64⟩ n₁ n₂ aw aop hd s₁ s₂ hs p₁ p₂)

private theorem clean_dirSize (d : _root_.Directive) (hd : dirStraightClean d = true) :
    x64DirSize d = 4 := by
  cases d <;> simp [dirStraightClean] at hd; rfl

private theorem clean_sum_dirSize :
    ∀ ds : List _root_.Directive, (∀ d ∈ ds, dirStraightClean d = true) →
      (ds.map x64DirSize).sum = 4 * ds.length
  | [], _ => rfl
  | d :: ds, h => by
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    rw [clean_dirSize d (h d List.mem_cons_self),
      clean_sum_dirSize ds (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    omega

private def dirInstrOnly : _root_.Directive → Bool
  | .instr _ => true
  | _ => false

private theorem dirInstrOnly_of_clean {d : _root_.Directive} (h : dirStraightClean d = true) :
    dirInstrOnly d = true := by
  cases d <;> simp_all [dirStraightClean, dirInstrOnly]

private theorem sizeBefore_instrOnly (kh : Host) (ds rest : List _root_.Directive)
    (hprog : kh.prog = ds ++ rest) (hins : ∀ d ∈ ds, dirInstrOnly d = true)
    (hl : (@Host.layout kh) = x64UniformLayout) :
    ∀ m ≤ ds.length, (@Host.exe kh).sizeBefore m = 4 * m := by
  intro m hm
  induction m with
  | zero => simp [Kraken.Executable.sizeBefore]
  | succ m ih =>
    have hlt : m < ds.length := by omega
    have hpi : kh.prog[m]? = some ds[m] := by
      rw [hprog, List.getElem?_append_left hlt, List.getElem?_eq_getElem hlt]
    have hsz : (@Host.layout kh).size ds[m] m = 4 := by
      have hc := hins ds[m] (List.getElem_mem hlt)
      cases hdm : ds[m] <;> simp [hdm, dirInstrOnly] at hc
      rw [hl]; rfl
    have hei : (@Host.exe kh).program[m]? = some { directive := ds[m], size := 4 } := by
      rw [@Host.exe_getElem? kh m, hpi]; dsimp only [Option.map]; rw [hsz]
    rw [Kraken.Executable.sizeBefore_succ (@Host.exe kh) hei, ih (by omega)]
    dsimp only
    omega

private theorem host_addrOf_inj_clean (kh : Host) (ds : List _root_.Directive)
    (hprog : kh.prog = ds) (hlen : 4 * ds.length < 2 ^ 64)
    (hclean : ∀ d ∈ ds, dirStraightClean d = true)
    (hl : (@Host.layout kh) = x64UniformLayout)
    {i j : Nat} (hi : i ≤ ds.length) (hj : j ≤ ds.length)
    (heq : @Host.addrOf kh i = @Host.addrOf kh j) : i = j := by
  have _ := hlen
  have h1 := @Host.sizeBefore_eq_of_addrOf_eq kh i j heq
  have hins : ∀ d ∈ ds, dirInstrOnly d = true := fun d hd => dirInstrOnly_of_clean (hclean d hd)
  have hprog' : kh.prog = ds ++ [] := by rw [List.append_nil]; exact hprog
  have hsi := sizeBefore_instrOnly kh ds [] hprog' hins hl i hi
  have hsj := sizeBefore_instrOnly kh ds [] hprog' hins hl j hj
  rw [hsi, hsj] at h1
  omega

private theorem takeWhile_prop {α : Type _} {p : α → Bool} {l : List α} {x : α}
    (hx : x ∈ l.takeWhile p) : p x = true := by
  induction l with
  | nil => simp at hx
  | cons y ys ih =>
    simp only [List.takeWhile_cons] at hx
    split at hx
    · rcases List.mem_cons.mp hx with rfl | hx'
      · assumption
      · exact ih hx'
    · cases hx

private theorem mem_directivesAtAddress_exists {Instr Const : Type}
    (e : Kraken.Executable Instr Const) {a : Int64}
    {c : Kraken.Sized (Kraken.Directive Instr Const)} (h : c ∈ e.directivesAtAddress a) :
    ∃ m, e.program[m]? = some c ∧ e.addrOf m = a := by
  dsimp [Kraken.Executable.directivesAtAddress] at h
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h
  have ha : x.addr = a := by simpa using takeWhile_prop hx
  have hmem : x ∈ e.withAddresses :=
    (List.dropWhile_sublist _).subset ((List.takeWhile_sublist _).subset hx)
  obtain ⟨m, hm⟩ := List.mem_iff_getElem?.mp hmem
  rw [Kraken.Executable.getElem?_withAddresses_eq] at hm
  obtain ⟨c0, hc0, hxe⟩ := Option.map_eq_some_iff.mp hm
  refine ⟨m, ?_, ?_⟩
  · subst hxe; exact hc0
  · rw [← hxe] at ha; simpa using ha

private theorem host_directives_past_nil (kh : Host) (ds : List _root_.Directive)
    (hprog : kh.prog = ds) (hclean : ∀ d ∈ ds, dirStraightClean d = true)
    (hl : (@Host.layout kh) = x64UniformLayout) :
    (@Host.exe kh).directivesAtAddress (@Host.addrOf kh ds.length) = [] := by
  have hpos : ∀ s ∈ (@Host.exe kh).program, 0 < s.size := by
    intro s hs
    obtain ⟨m, hm⟩ := List.mem_iff_getElem?.mp hs
    rw [@Host.exe_getElem? kh m, hprog] at hm
    cases hdm : ds[m]? with
    | none => simp [hdm] at hm
    | some dm =>
      simp only [hdm, Option.map_some, Option.some.injEq] at hm
      have hs_sz : s.size = (@Host.layout kh).size dm m := (congrArg Kraken.Sized.size hm).symm
      have hcm := hclean dm (List.mem_of_getElem? hdm)
      cases dm <;> simp [dirStraightClean] at hcm
      rw [hs_sz, hl]; exact Nat.zero_lt_succ 3
  cases hd : (@Host.exe kh).directivesAtAddress (@Host.addrOf kh ds.length) with
  | nil => rfl
  | cons x _ =>
    exfalso
    have hx := List.mem_of_mem_head? (hd ▸ rfl :
      ((@Host.exe kh).directivesAtAddress (@Host.addrOf kh ds.length)).head? = some x)
    obtain ⟨m, hm, haddr⟩ := mem_directivesAtAddress_exists (@Host.exe kh) hx
    have hmlt : m < ds.length := by
      rw [@Host.exe_getElem? kh m, hprog] at hm
      cases hdm : ds[m]? with
      | none => simp [hdm] at hm
      | some _ => exact (List.getElem?_eq_some_iff.mp hdm).1
    have hsb := @Host.sizeBefore_eq_of_addrOf_eq kh ds.length m haddr.symm
    have hposm : (@Host.exe kh).sizeBefore m < (@Host.exe kh).sizeBefore ds.length := by
      have hle := Kraken.Executable.sizeBefore_mono (@Host.exe kh) (show m + 1 ≤ ds.length by omega)
      have hs1 := Kraken.Executable.sizeBefore_succ (@Host.exe kh) hm
      have hpx := hpos _ (List.mem_of_getElem? hm)
      omega
    omega

private theorem host_directives_at_clean (kh : Host) (ds : List _root_.Directive)
    (hprog : kh.prog = ds) (hclean : ∀ d ∈ ds, dirStraightClean d = true)
    (hl : (@Host.layout kh) = x64UniformLayout) {i : Nat} (hi : i < ds.length) :
    (@Host.exe kh).directivesAtAddress (@Host.addrOf kh i) =
      [{ directive := ds[i], size := 4 }] := by
  have hpi : (@Host.prog kh)[i]? = some ds[i] := by rw [hprog]; exact List.getElem?_eq_getElem hi
  have hs4 : (@Host.layout kh).size ds[i] i = 4 := by
    have hc := hclean ds[i] (List.getElem_mem hi)
    cases hdm : ds[i] <;> simp [hdm, dirStraightClean] at hc
    rw [hl]; rfl
  have hei : (@Host.exe kh).program[i]? = some { directive := ds[i], size := 4 } := by
    rw [@Host.exe_getElem? kh i, hpi]; dsimp only [Option.map]; rw [hs4]
  obtain ⟨pre, hat, hpre⟩ := @Host.directivesAtAddress_addrOf kh i _ hei (Nat.zero_lt_succ 3)
  have hnil : pre = [] := by
    cases pre with
    | nil => rfl
    | cons y _ =>
      exfalso
      have hy0 := hpre y List.mem_cons_self
      obtain ⟨m, hm, _⟩ := mem_directivesAtAddress_exists (@Host.exe kh)
        (hat ▸ List.mem_append_left _ List.mem_cons_self)
      rw [@Host.exe_getElem? kh m, hprog] at hm
      cases hdm : ds[m]? with
      | none => simp [hdm] at hm
      | some dm =>
        simp only [hdm, Option.map_some, Option.some.injEq] at hm
        have hy_sz : y.size = (@Host.layout kh).size dm m := (congrArg Kraken.Sized.size hm).symm
        have hcm := hclean dm (List.mem_of_getElem? hdm)
        cases dm <;> simp [dirStraightClean] at hcm
        rw [hy_sz, hl] at hy0
        simp [Kraken.Layout.size] at hy0
  rw [hnil, List.nil_append] at hat
  exact hat

private theorem x64_frame_to_vll {gClob : List Reg64} {vClob : List RegMm} {fClob : FlagMask}
    {sv sv' : MachSt x64Arch} {sk' : MachineData}
    (hsim : KrakenSim (machToKraken sv') sk')
    (hfr : x64Mach.Frame x64CondReads (machToKraken sv) sk' gClob vClob fClob) :
    (vllMach x64Arch).Frame x64CondReads sv sv' gClob vClob fClob := by
  refine ⟨fun r hr => ?_, fun vr hvr => ?_, fun cc hc => ?_⟩
  · exact (regsOfFn_get64 sv'.gpr r).symm.trans ((hsim.1 r).trans
      ((hfr.1 r hr).trans (regsOfFn_get64 sv.gpr r)))
  · exact (zmmsOfFn_get512 sv'.vreg vr).symm.trans ((hsim.2.1 vr).trans
      ((hfr.2.1 vr hvr).trans (zmmsOfFn_get512 sv.vreg vr)))
  · exact (krakenSim_cond hsim cc).trans (hfr.2.2 cc hc)

private theorem vllMach_step_at' {A : Arch} {h : VllHost A} {k : Nat} {instr : Instr A}
    {s : MachSt A} {post : Config A → Prop}
    (hk : h.prog[k]? = some instr)
    (hex : ∃ o, instrRel A h.labelAddr (h.addrOf (k + 1)) instr s o)
    (hfall : ∀ s', instrRel A h.labelAddr (h.addrOf (k + 1)) instr s (.fall s') →
      (vllMach A).Run h (k + 1) s' post)
    (hjump : ∀ pc' s', instrRel A h.labelAddr (h.addrOf (k + 1)) instr s (.jump pc' s') →
      Eventually (vllStep h) post ⟨s', pc'⟩)
    (hhalt : ∀ c s', instrRel A h.labelAddr (h.addrOf (k + 1)) instr s (.halt c s') → False) :
    (vllMach A).Run h k s post :=
  step_cps (vllStep h) post ⟨s, h.addrOf k⟩ ⟨k, instr, hk, rfl, hex, hfall, hjump, hhalt⟩

private theorem vllMach_native_clean_step (kh : Host) (vh : VllHost x64Arch)
    {i k_vh : Nat} {d : _root_.Directive} {st : MachineState} {sv_i : MachSt x64Arch}
    {mid_p : MachineState → Prop} {post : Config x64Arch → Prop}
    (hc_d : dirStraightClean d = true)
    (hk_vh : vh.prog[k_vh]? = some (.native d))
    (hstep' : ((@_root_.Directive.interp (@Host.exe kh).labels d st.data
        ⟨@Host.addrOf kh i, @Host.addrOf kh (i + 1)⟩
        (fun s => .done ⟨s, @Host.addrOf kh (i + 1)⟩)
        (fun pc s => .done ⟨s, pc⟩))).All mid_p)
    (hsim : KrakenSim (machToKraken sv_i) st.data)
    (hnext : ∀ st1 : MachineState, ∀ sv' : MachSt x64Arch,
      mid_p st1 → st1.pc = @Host.addrOf kh (i + 1) →
      KrakenSim (machToKraken sv') st1.data →
      (vllMach x64Arch).Run vh (k_vh + 1) sv' post) :
    (vllMach x64Arch).Run vh k_vh sv_i post := by
  let L_vh : Labels := { label := fun l => Int64.ofBitVec (vh.labelAddr l) }
  let p0 : Std.Rco Int64 := ⟨0, 4⟩
  have hls : ∀ (sk0 : MachineData) (p_v : Std.Rco Int64),
      KrakenSim (machToKraken sv_i) sk0 →
      EffectsLockstep
        (fun s => .done ⟨s, @Host.addrOf kh (i + 1)⟩) (fun s => .done ⟨s, 0⟩)
        (@_root_.Directive.interp (@Host.exe kh).labels d st.data
          ⟨@Host.addrOf kh i, @Host.addrOf kh (i + 1)⟩
          (fun s => .done ⟨s, @Host.addrOf kh (i + 1)⟩) (fun pc s => .done ⟨s, pc⟩))
        (@_root_.Directive.interp L_vh d sk0 p_v
          (fun s => .done ⟨s, 0⟩) (fun _ _ => .unimplemented "jmp")) :=
    fun sk0 p_v hk0 =>
      dir_interp_lockstep (@Host.exe kh).labels L_vh d hc_d
        (krakenSim_trans (krakenSim_symm hsim) hk0) _ p_v
  have hex : ∃ o, instrRel x64Arch vh.labelAddr (vh.addrOf (k_vh + 1)) (.native d) sv_i o := by
    obtain ⟨sk', hre⟩ := effectsLockstep_exists_reaches (hls (machToKraken sv_i) p0
      (krakenSim_refl _)) hstep' fun s₂ => ⟨s₂, .done⟩
    exact ⟨.fall (krakenToMachData sk'), .fall (krakenToMachData sk'),
      ⟨machToKraken sv_i, p0, regsOfFn_get64 sv_i.gpr, zmmsOfFn_get512 sv_i.vreg,
        fun _ => rfl, rfl, sk', hre, rfl⟩, rfl⟩
  refine vllMach_step_at' hk_vh hex ?_ ?_ ?_
  · rintro sv' ⟨no, hns, ho⟩
    cases no with
    | jump _ _ | halt _ _ => cases ho
    | fall s_out =>
      cases ho
      obtain ⟨sk0, pv, hr0, hv0, hf0, hm0, sk', hre, hs_out⟩ := hns
      subst hs_out
      have hk0 := krakenSim_of_archEq hr0 hv0 hm0 hf0
      obtain ⟨st1, hmid1, hpc1, hd1sim⟩ := effectsLockstep_preserves (hls sk0 pv hk0)
        (Q₁ := fun s => s.pc = @Host.addrOf kh (i + 1)) hstep' hre
        fun s₁ _ hsim12 hall1 hre2 => by cases hre2; exact ⟨_, hall1, rfl, hsim12⟩
      exact hnext st1 (krakenToMachData sk') hmid1 hpc1
        (krakenSim_trans (krakenSim_krakenToMachData sk') (krakenSim_symm hd1sim))
  · rintro pc' sv' ⟨no, hns, ho⟩
    cases no with
    | fall _ | halt _ _ => cases ho
    | jump _ s_out =>
      cases ho
      obtain ⟨sk0, pv, hr0, hv0, hf0, hm0, sk', hre, _⟩ := hns
      have hk0 := krakenSim_of_archEq hr0 hv0 hm0 hf0
      exfalso
      have hno : EffectsLockstep
          (fun s => .done ⟨s, @Host.addrOf kh (i + 1)⟩) (fun _ => .unimplemented "fall")
          (@_root_.Directive.interp (@Host.exe kh).labels d st.data
            ⟨@Host.addrOf kh i, @Host.addrOf kh (i + 1)⟩
            (fun s => .done ⟨s, @Host.addrOf kh (i + 1)⟩) (fun pc s => .done ⟨s, pc⟩))
          (@_root_.Directive.interp L_vh d sk0 pv
            (fun _ => .unimplemented "fall") (fun a s => .done ⟨s, a⟩)) :=
        @dir_interp_lockstep (@Host.exe kh).labels L_vh
          (fun s => .done ⟨s, @Host.addrOf kh (i + 1)⟩) (fun _ => .unimplemented "fall")
          (fun pc s => .done ⟨s, pc⟩) (fun a s => .done ⟨s, a⟩) d hc_d st.data sk0
          (krakenSim_trans (krakenSim_symm hsim) hk0)
          ⟨@Host.addrOf kh i, @Host.addrOf kh (i + 1)⟩ pv
      clear hls hex
      suffices ∀ {e₁ e₂} (hl : EffectsLockstep
          (fun s => .done ⟨s, @Host.addrOf kh (i + 1)⟩) (fun _ => .unimplemented "fall") e₁ e₂),
          e₁.All mid_p → ∀ {a}, EffectsReaches e₂ ⟨sk', a⟩ → False from
        this hno hstep' hre
      intro e₁ e₂ hl hall1 a hre2
      induction hl with
      | fall _ => cases hre2
      | fail hn => exact hn mid_p hall1
      | undef _ ih2 => cases hre2 with | undefined hr2 => exact ih2 _ (hall1 _) hr2
      | rread _ ih2 => cases hre2 with | require_read hr2 => exact ih2 hall1 hr2
      | rwrite _ ih2 => cases hre2 with | require_write hr2 => exact ih2 hall1 hr2
      | rexec _ ih2 => cases hre2 with | require_exec hr2 => exact ih2 hall1 hr2
  · rintro c sv' ⟨no, hns, ho⟩
    cases no with
    | fall _ | jump _ _ => cases ho
    | halt _ _ => obtain ⟨_, _, _, _, _, _, hbad⟩ := hns; exact hbad

/-- Master lifting theorem translating any straight-line `x64Mach.FallsTo` proof over `ds`
into `(vllMach x64Arch).FallsTo` over `ds.map .native`. -/
theorem x64Mach_fallsTo_to_vll {vh : VllHost x64Arch} {k : Nat}
    {ds : List _root_.Directive} {gClob : List Reg64} {vClob : List RegMm} {fClob : FlagMask}
    {sv : MachSt x64Arch} {Q : MachSt x64Arch → Prop} {Qk : MachineData → Prop}
    {post : Config x64Arch → Prop}
    (hclean : ∀ d ∈ ds, dirStraightClean d = true)
    (hlen : ds.length < 2 ^ 61)
    (hx : ∀ (kh : Host),
      x64Mach.FallsTo x64CondReads kh 0 ds gClob vClob fClob (machToKraken sv) Qk
        (fun st => st.pc = @Host.addrOf kh ds.length ∧ Qk st.data ∧
          x64Mach.Frame x64CondReads (machToKraken sv) st.data gClob vClob fClob))
    (hQ : ∀ sv' sk', KrakenSim (machToKraken sv') sk' → Qk sk' → Q sv') :
    (vllMach x64Arch).FallsTo x64CondReads vh k (ds.map .native) gClob vClob fClob sv Q post := by
  intro hc cont
  have hps : x64ProgSmall ds = true := by
    dsimp only [x64ProgSmall]; rw [clean_sum_dirSize ds hclean]; exact decide_eq_true (by omega)
  let kh : Host := .ofLayout ds x64UniformLayout (x64UniformLayout_small ds hps)
  have he : Eventually (@hostStep kh)
      (fun st => st.pc = @Host.addrOf kh ds.length ∧ Qk st.data ∧
        x64Mach.Frame x64CondReads (machToKraken sv) st.data gClob vClob fClob)
      ⟨machToKraken sv, @Host.addrOf kh 0⟩ :=
    hx kh ⟨[], List.append_nil ds⟩ fun sk' hqk hfr => Eventually.done _ ⟨by simp, hqk, hfr⟩
  suffices hloop : ∀ (st : MachineState) (i k_vh : Nat) (sv_i : MachSt x64Arch),
      Eventually (@hostStep kh)
        (fun s => s.pc = @Host.addrOf kh ds.length ∧ Qk s.data ∧
          x64Mach.Frame x64CondReads (machToKraken sv) s.data gClob vClob fClob) st →
      i ≤ ds.length → st.pc = @Host.addrOf kh i → KrakenSim (machToKraken sv_i) st.data →
      ((ds.drop i).map (.native (A := x64Arch))).IsInfixAt vh.prog k_vh →
      (∀ sk_fin sv_fin, KrakenSim (machToKraken sv_fin) sk_fin →
        Qk sk_fin → x64Mach.Frame x64CondReads (machToKraken sv) sk_fin gClob vClob fClob →
        (vllMach x64Arch).Run vh (k_vh + (ds.drop i).length) sv_fin post) →
      (vllMach x64Arch).Run vh k_vh sv_i post by
    exact hloop ⟨machToKraken sv, @Host.addrOf kh 0⟩ 0 k sv he (Nat.zero_le _) rfl
      (krakenSim_refl _) hc fun sk_fin sv_fin hsim hqk hfr => by
      simpa using cont sv_fin (hQ sv_fin sk_fin hsim hqk) (x64_frame_to_vll hsim hfr)
  intro st i k_vh sv_i he0 hi hpc hsim hdrop hvcont
  induction he0 generalizing i k_vh sv_i with
  | done st hp =>
    have hieq : i = ds.length :=
      host_addrOf_inj_clean kh ds rfl (by omega) hclean rfl hi (Nat.le_refl _) (hpc.symm.trans hp.1)
    subst hieq
    simpa [List.drop_length] using hvcont st.data sv_i hsim hp.2.1 hp.2.2
  | step st mid_p hstep _ ih =>
    by_cases hilt : i < ds.length
    · have hk_vh : vh.prog[k_vh]? = some (.native ds[i]) := by
        rw [List.drop_eq_getElem_cons hilt, List.map_cons] at hdrop
        exact hdrop.cons.1
      have hdir := host_directives_at_clean kh ds rfl hclean rfl hilt
      have hstep' : ((@_root_.Directive.interp (@Host.exe kh).labels ds[i] st.data
          ⟨@Host.addrOf kh i, @Host.addrOf kh (i + 1)⟩
          (fun s => .done ⟨s, @Host.addrOf kh (i + 1)⟩)
          (fun pc s => .done ⟨s, pc⟩))).All mid_p := by
        have hs0 : ((@Directives.interp (@Host.exe kh).labels
            [{ directive := ds[i], size := 4 }] st.data (@Host.addrOf kh i)
            fun pc s => .done ⟨s, pc⟩)).All mid_p := by
          simpa [hostStep, step1, Executable.step, hpc, hdir] using hstep
        have ha1 : @Host.addrOf kh (i + 1) = @Host.addrOf kh i + 4 := by
          have ha := @Host.addrOf_succ kh i ds[i] (List.getElem?_eq_getElem hilt)
          have hsz : (@Host.layout kh).size ds[i] i = 4 := by
            have hcd := hclean ds[i] (List.getElem_mem hilt)
            cases hdm : ds[i] <;> simp [hdm, dirStraightClean] at hcd; rfl
          simpa [hsz] using ha
        simpa [Directives.interp, ha1] using hs0
      refine vllMach_native_clean_step kh vh (hclean ds[i] (List.getElem_mem hilt))
        hk_vh hstep' hsim fun st1 sv' hmid1 hpc1 hsim1 => ?_
      have hdrop1 : ((ds.drop (i + 1)).map (.native (A := x64Arch))).IsInfixAt
          vh.prog (k_vh + 1) := by
        rw [List.drop_eq_getElem_cons hilt, List.map_cons] at hdrop
        exact hdrop.cons.2
      have hvcont1 :
          ∀ sk_fin sv_fin, KrakenSim (machToKraken sv_fin) sk_fin →
            Qk sk_fin → x64Mach.Frame x64CondReads (machToKraken sv) sk_fin gClob vClob fClob →
            (vllMach x64Arch).Run vh (k_vh + 1 + (ds.drop (i + 1)).length) sv_fin post := by
        intro sk_fin sv_fin hsim_fin hqk hfr
        have hlen_eq : k_vh + 1 + (ds.drop (i + 1)).length = k_vh + (ds.drop i).length := by
          simp only [List.length_drop]; omega
        rw [hlen_eq]; exact hvcont sk_fin sv_fin hsim_fin hqk hfr
      exact ih st1 hmid1 (i + 1) (k_vh + 1) sv' (by omega) hpc1 hsim1 hdrop1 hvcont1
    · have hieq : i = ds.length := Nat.le_antisymm hi (Nat.le_of_not_lt hilt)
      subst hieq
      have hnil := host_directives_past_nil kh ds rfl hclean rfl
      obtain ⟨sdata, spc⟩ := st
      dsimp only at hpc hsim
      have hmid : mid_p ⟨sdata, spc⟩ := by
        rw [hpc]
        dsimp only [hostStep, step1, Executable.step] at hstep
        rw [hpc, hnil] at hstep
        simpa [Directives.interp, Effects.All] using hstep
      exact ih _ hmid ds.length k_vh sv_i hi hpc hsim hdrop hvcont

/-! ## 3. Conditional Branch Lifting (`x64Mach_splitJcc_to_vll`) and Clean/Small Lemmas -/

private theorem jccTail_progSmall (ds_pre : List _root_.Directive) (cc : CondCode) (l : Sym)
    (hclean : ∀ d ∈ ds_pre, dirStraightClean d = true) (hlen : ds_pre.length < 2 ^ 60) :
    x64ProgSmall (ds_pre ++ [ins (.jcc cc l), .byteArray ⟨#[0]⟩, .label l, .byteArray ⟨#[1]⟩]) =
      true := by
  dsimp only [x64ProgSmall]
  rw [List.map_append, List.sum_append, clean_sum_dirSize ds_pre hclean]
  have h0 : (⟨#[0]⟩ : ByteArray).size = 1 := rfl
  have h1 : (⟨#[1]⟩ : ByteArray).size = 1 := rfl
  simp [x64DirSize, h0, h1]
  omega

private theorem directives_interp_pre_byteArray (kh : Host) (b : UInt8) :
    ∀ (pre : List (Kraken.Sized _root_.Directive)) (s : MachineData) (pc : Int64)
      (ret : Int64 → MachineData → Effects) (mid_p : MachineState → Prop),
      (∀ c ∈ pre, c ∈ (@Host.exe kh).program ∧ c.size = 0) →
      (@Directives.interp (@Host.exe kh).labels
        (pre ++ [{ directive := .byteArray ⟨#[b]⟩, size := 1 }]) s pc ret).All
        mid_p → False := by
  intro pre
  induction pre with
  | nil =>
    intro s pc ret mid_p _ hall
    have hb : (⟨#[b]⟩ : ByteArray).isEmpty = false := rfl
    simp only [List.nil_append, Directives.interp, _root_.Directive.interp, hb,
      Bool.false_eq_true, ↓reduceIte] at hall
    exact hall
  | cons c cs ih =>
    intro s pc ret mid_p hpre hall
    obtain ⟨hmem, hc0⟩ := hpre c List.mem_cons_self
    obtain ⟨m, hm⟩ := List.mem_iff_getElem?.mp hmem
    rw [@Host.exe_getElem? kh m] at hm
    cases hpm : kh.prog[m]? with
    | none => simp [hpm] at hm
    | some dm =>
      simp only [hpm, Option.map_some, Option.some.injEq] at hm
      have hcd_eq : c.directive = dm := by subst hm; rfl
      have hsz_eq : (@Host.layout kh).size c.directive m = 0 := by
        rw [hcd_eq]; exact (congrArg Kraken.Sized.size hm).trans hc0
      have hcd := @inert_of_size_zero (@Host.layout kh) (@Host.exe kh).labels m c.directive
        hsz_eq s ⟨pc, pc + .ofNat c.size⟩
        (fun s' => @Directives.interp (@Host.exe kh).labels
          (cs ++ [{ directive := .byteArray ⟨#[b]⟩, size := 1 }]) s' (pc + .ofNat c.size) ret) ret
      simp only [List.cons_append, Directives.interp] at hall
      rw [hcd] at hall
      exact ih s (pc + .ofNat c.size) ret mid_p
        (fun x hx => hpre x (List.mem_cons_of_mem _ hx)) hall

private theorem splitJcc_directives_at_pref (kh : Host)
    (ds_pre : List _root_.Directive) (cc : CondCode) (l : Sym)
    (hprog : kh.prog = ds_pre ++ [ins (.jcc cc l), .byteArray ⟨#[0]⟩, .label l, .byteArray ⟨#[1]⟩])
    (hclean : ∀ d ∈ ds_pre, dirStraightClean d = true)
    (hl : (@Host.layout kh) = x64UniformLayout) {i : Nat} (hi : i ≤ ds_pre.length) :
    (@Host.exe kh).directivesAtAddress (@Host.addrOf kh i) =
      [{ directive := (@Host.prog kh)[i]?.getD (.label ""), size := 4 }] := by
  let ds0 := ds_pre ++ [ins (.jcc cc l)]
  have hprog' : kh.prog = ds0 ++ [.byteArray ⟨#[0]⟩, .label l, .byteArray ⟨#[1]⟩] := by
    rw [hprog]; simp [ds0]
  have hins0 : ∀ d ∈ ds0, dirInstrOnly d = true := fun d hd => by
    rcases List.mem_append.mp hd with h1 | h2
    · exact dirInstrOnly_of_clean (hclean d h1)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h2; subst h2; rfl
  have hilt : i < ds0.length := by simp [ds0]; omega
  have hpi : (@Host.prog kh)[i]? = some ds0[i] := by
    rw [hprog']; exact (List.getElem?_append_left hilt).trans (List.getElem?_eq_getElem hilt)
  have hs4 : (@Host.layout kh).size ds0[i] i = 4 := by
    have hc := hins0 ds0[i] (List.getElem_mem hilt)
    cases hdm : ds0[i] <;> simp [hdm, dirInstrOnly] at hc; rw [hl]; rfl
  have hei : (@Host.exe kh).program[i]? = some { directive := ds0[i], size := 4 } := by
    rw [@Host.exe_getElem? kh i, hpi]; dsimp only [Option.map]; rw [hs4]
  obtain ⟨pre, hat, hpre⟩ := @Host.directivesAtAddress_addrOf kh i _ hei (Nat.zero_lt_succ 3)
  have hnil : pre = [] := by
    cases pre with
    | nil => rfl
    | cons y _ =>
      exfalso
      have hy0 := hpre y List.mem_cons_self
      obtain ⟨m, hm, haddr⟩ := mem_directivesAtAddress_exists (@Host.exe kh)
        (hat ▸ List.mem_append_left _ List.mem_cons_self)
      have hsb := @Host.sizeBefore_eq_of_addrOf_eq kh m i haddr
      have hsi : (@Host.exe kh).sizeBefore i = 4 * i :=
        sizeBefore_instrOnly kh ds0 _ hprog' hins0 hl i (by omega)
      have hsd : (@Host.exe kh).sizeBefore ds0.length = 4 * ds0.length :=
        sizeBefore_instrOnly kh ds0 _ hprog' hins0 hl ds0.length (Nat.le_refl _)
      by_cases hm0 : m < ds0.length
      · rw [@Host.exe_getElem? kh m, hprog', List.getElem?_append_left hm0,
          List.getElem?_eq_getElem hm0] at hm
        simp only [Option.map_some, Option.some.injEq] at hm
        have hy_sz : y.size = (@Host.layout kh).size ds0[m] m :=
          (congrArg Kraken.Sized.size hm).symm
        have hcm := hins0 ds0[m] (List.getElem_mem hm0)
        cases hdm : ds0[m] <;> simp [hdm, dirInstrOnly] at hcm
        rw [hdm, hl] at hy_sz
        rw [hy_sz] at hy0
        simp [Kraken.Layout.size] at hy0
      · have hmono := Kraken.Executable.sizeBefore_mono (@Host.exe kh) (Nat.le_of_not_lt hm0)
        rw [hsb, hsi, hsd] at hmono
        have : ds0.length = ds_pre.length + 1 := by simp [ds0]
        omega
  rw [hnil, List.nil_append] at hat
  rw [hpi]; simpa using hat

private theorem krakenToMachData_machToKraken (sv : MachSt x64Arch) :
    krakenToMachData (machToKraken sv) = sv := by
  cases sv; dsimp only [krakenToMachData, machToKraken]; congr 1
  · funext r; exact regsOfFn_get64 _ r
  · funext vr; exact zmmsOfFn_get512 _ vr

private theorem vllMach_native_jcc_step {vh : VllHost x64Arch} {k j : Nat}
    {cc : CondCode} {l : Sym} {sv : MachSt x64Arch} {post : Config x64Arch → Prop}
    (hk : vh.prog[k]? = some (.native (ins (.jcc cc l))))
    (hl : vh.labelAddr l = vh.addrOf j)
    (ht : cc.interp sv.flags = true →
      ∀ s' : MachSt x64Arch,
        (∀ r, s'.gpr r = sv.gpr r) → (∀ vr, s'.vreg vr = sv.vreg vr) →
        (∀ cd : CondCode, cd.interp s'.flags = cd.interp sv.flags) → s'.mem = sv.mem →
        (vllMach x64Arch).Run vh j s' post)
    (hf : cc.interp sv.flags = false →
      ∀ s' : MachSt x64Arch,
        (∀ r, s'.gpr r = sv.gpr r) → (∀ vr, s'.vreg vr = sv.vreg vr) →
        (∀ cd : CondCode, cd.interp s'.flags = cd.interp sv.flags) → s'.mem = sv.mem →
        (vllMach x64Arch).Run vh (k + 1) s' post) :
    (vllMach x64Arch).Run vh k sv post := by
  have hrkm : ∀ (sk0 : MachineData),
      (∀ r, sk0.regs.get64 r = sv.gpr r) → (∀ vr, sk0.zmms.get512 vr = sv.vreg vr) →
      (∀ cd : CondCode, cd.interp sk0.status = cd.interp sv.flags) → sk0.dmem = sv.mem →
      (∀ r, (krakenToMachData sk0).gpr r = sv.gpr r) ∧
      (∀ vr, (krakenToMachData sk0).vreg vr = sv.vreg vr) ∧
      (∀ cd : CondCode, cd.interp (krakenToMachData sk0).flags = cd.interp sv.flags) ∧
      (krakenToMachData sk0).mem = sv.mem := fun sk0 h1 h2 h3 h4 => ⟨h1, h2, h3, h4⟩
  cases hcond : cc.interp sv.flags with
  | true =>
    refine vllMach_step_at' hk ?_ ?_ ?_ ?_
    · refine ⟨.jump (vh.addrOf j) sv, ⟨.jump (vh.addrOf j) sv, ?_, rfl⟩⟩
      refine ⟨machToKraken sv, ⟨0, 0⟩, regsOfFn_get64 sv.gpr, zmmsOfFn_get512 sv.vreg,
        fun _ => rfl, rfl, ⟨machToKraken sv, ?_, (krakenToMachData_machToKraken sv).symm⟩⟩
      exact .require_exec (by simp [Operation.interp, machToKraken, hcond, hl]; exact .done)
    · rintro s' ⟨no, ⟨sk0, p, _, _, h3, _, hst⟩, ho⟩
      cases no with
      | jump _ _ | halt _ _ => cases ho
      | fall _ =>
        obtain ⟨sk', hr, _⟩ := hst
        simp only [_root_.Directive.interp, Instr.interp, Operation.interp, h3 cc, hcond,
          ↓reduceIte] at hr
        cases hr with | require_exec hr => cases hr
    · rintro pc' s' ⟨no, ⟨sk0, p, h1, h2, h3, h4, hst⟩, ho⟩
      cases no with
      | fall _ | halt _ _ => cases ho
      | jump pc0 s0 =>
        cases ho
        obtain ⟨sk', hr, rfl⟩ := hst
        simp only [_root_.Directive.interp, Instr.interp, Operation.interp, h3 cc, hcond,
          ↓reduceIte] at hr
        cases hr with
        | require_exec hr =>
          cases hr
          obtain ⟨g1, g2, g3, g4⟩ := hrkm sk0 h1 h2 h3 h4
          exact hl ▸ ht hcond (krakenToMachData sk0) g1 g2 g3 g4
    · rintro c0 sv' ⟨no, hns, ho⟩
      cases no with
      | fall _ | jump _ _ => cases ho
      | halt _ _ => obtain ⟨_, _, _, _, _, _, hbad⟩ := hns; exact hbad
  | false =>
    refine vllMach_step_at' hk ?_ ?_ ?_ ?_
    · refine ⟨.fall sv, ⟨.fall sv, ?_, rfl⟩⟩
      refine ⟨machToKraken sv, ⟨0, 0⟩, regsOfFn_get64 sv.gpr, zmmsOfFn_get512 sv.vreg,
        fun _ => rfl, rfl, ⟨machToKraken sv, ?_, (krakenToMachData_machToKraken sv).symm⟩⟩
      exact .require_exec (by simp [Operation.interp, machToKraken, hcond]; exact .done)
    · rintro s' ⟨no, ⟨sk0, p, h1, h2, h3, h4, hst⟩, ho⟩
      cases no with
      | jump _ _ | halt _ _ => cases ho
      | fall s0 =>
        cases ho
        obtain ⟨sk', hr, rfl⟩ := hst
        simp only [_root_.Directive.interp, Instr.interp, Operation.interp, h3 cc, hcond,
          Bool.false_eq_true, ↓reduceIte] at hr
        cases hr with
        | require_exec hr =>
          cases hr
          obtain ⟨g1, g2, g3, g4⟩ := hrkm sk0 h1 h2 h3 h4
          exact hf hcond (krakenToMachData sk0) g1 g2 g3 g4
    · rintro pc' s' ⟨no, ⟨sk0, p, _, _, h3, _, hst⟩, ho⟩
      cases no with
      | fall _ | halt _ _ => cases ho
      | jump _ _ =>
        obtain ⟨sk', hr, _⟩ := hst
        simp only [_root_.Directive.interp, Instr.interp, Operation.interp, h3 cc, hcond,
          Bool.false_eq_true, ↓reduceIte] at hr
        cases hr with | require_exec hr => cases hr
    · rintro c0 sv' ⟨no, hns, ho⟩
      cases no with
      | fall _ | jump _ _ => cases ho
      | halt _ _ => obtain ⟨_, _, _, _, _, _, hbad⟩ := hns; exact hbad

/-- Lift a straight-line prefix followed by `.jcc cc l` from `x64Mach.Run` into
`(vllMach x64Arch).Run`, using a minimal synthetic `[ins (.jcc cc l), .byteArray #[0],
.label l, .byteArray #[1]]` host tail so taken and fallthrough outcomes remain separated. -/
theorem x64Mach_splitJcc_to_vll {vh : VllHost x64Arch} {k j : Nat}
    {ds_pre : List _root_.Directive} {cc : CondCode} {l : Sym} {fClob : FlagMask}
    {sv : MachSt x64Arch} {cond : Bool} {post : Config x64Arch → Prop}
    (hclean : ∀ d ∈ ds_pre, dirStraightClean d = true)
    (hlen : ds_pre.length < 2 ^ 60)
    (hc : ((ds_pre ++ [ins (.jcc cc l)]).map (.native (A := x64Arch))).IsInfixAt vh.prog k)
    (hl : vh.labelAddr l = vh.addrOf j)
    (hx : ∀ (kh : Host),
      (ds_pre ++ [ins (.jcc cc l)]).IsInfixAt (x64Mach.prog kh) 0 →
      ∀ j_k : Nat, x64Mach.labelAddr kh l = x64Mach.addrOf kh j_k →
      let post_k : MachineState → Prop := fun st =>
        st.pc = @Host.addrOf kh (if cond then j_k else ds_pre.length + 1) ∧
        st.data.dmem = sv.mem ∧
        x64Mach.Frame x64CondReads (machToKraken sv) st.data x64Scratch [] fClob
      (∀ s', x64Mach.Frame x64CondReads (machToKraken sv) s' x64Scratch [] fClob →
        s'.dmem = sv.mem →
        (cond = true → x64Mach.Run kh j_k s' post_k) ∧
        (cond = false → x64Mach.Run kh (ds_pre.length + 1) s' post_k)) →
      x64Mach.Run kh 0 (machToKraken sv) post_k)
    (hcont : ∀ s', (vllMach x64Arch).Frame x64CondReads sv s' x64Scratch [] fClob →
      s'.mem = sv.mem →
      (cond = true → (vllMach x64Arch).Run vh j s' post) ∧
      (cond = false →
        (vllMach x64Arch).Run vh (k + (ds_pre ++ [ins (.jcc cc l)]).length) s' post)) :
    (vllMach x64Arch).Run vh k sv post := by
  let tail : List _root_.Directive := [.byteArray ⟨#[0]⟩, .label l, .byteArray ⟨#[1]⟩]
  let prog_kh : List _root_.Directive :=
    ds_pre ++ [ins (.jcc cc l), .byteArray ⟨#[0]⟩, .label l, .byteArray ⟨#[1]⟩]
  have hps : x64ProgSmall prog_kh = true := jccTail_progSmall ds_pre cc l hclean hlen
  let kh : Host := .ofLayout prog_kh x64UniformLayout (x64UniformLayout_small _ hps)
  let j_k : Nat := ds_pre.length + 2
  have hprog_kh : kh.prog = prog_kh := rfl
  have hprog_kh' : kh.prog = (ds_pre ++ [ins (.jcc cc l)]) ++ tail := by
    rw [hprog_kh]; simp [prog_kh, tail]
  have hj_k_elem : kh.prog[j_k]? = some (.label l) := by
    rw [hprog_kh, List.getElem?_append_right (show ds_pre.length ≤ j_k by omega)]
    simp [j_k, show ds_pre.length + 2 - ds_pre.length = 2 by omega]
  have hfirst : ∀ idx, idx < j_k → kh.prog[idx]? ≠ some (.label l) := by
    intro idx hidx hbad
    rw [hprog_kh] at hbad
    by_cases hlt : idx < ds_pre.length
    · rw [List.getElem?_append_left hlt, List.getElem?_eq_getElem hlt] at hbad
      have hbad' : ds_pre[idx] = .label l := Option.some.inj hbad
      have hc0 := hclean ds_pre[idx] (List.getElem_mem hlt)
      rw [hbad'] at hc0; cases hc0
    · rw [List.getElem?_append_right (Nat.le_of_not_lt hlt)] at hbad
      have hidx_eq : idx = ds_pre.length ∨ idx = ds_pre.length + 1 := by simp [j_k] at hidx; omega
      rcases hidx_eq with rfl | rfl <;> simp_all
  have hlab_k : x64Mach.labelAddr kh l = x64Mach.addrOf kh j_k :=
    @Host.label_eq_addrOf kh l j_k hj_k_elem hfirst
  have hinf_k : (ds_pre ++ [ins (.jcc cc l)]).IsInfixAt (x64Mach.prog kh) 0 :=
    ⟨tail, by simpa [x64Mach] using hprog_kh'.symm⟩
  let post_k : MachineState → Prop := fun st =>
    st.pc = @Host.addrOf kh (if cond then j_k else ds_pre.length + 1) ∧
    st.data.dmem = sv.mem ∧
    x64Mach.Frame x64CondReads (machToKraken sv) st.data x64Scratch [] fClob
  have he : Eventually (@hostStep kh) post_k ⟨machToKraken sv, @Host.addrOf kh 0⟩ :=
    hx kh hinf_k j_k hlab_k fun s' hfr hmem =>
      ⟨fun hcnd => Eventually.done _ ⟨by simp [hcnd], hmem, hfr⟩,
       fun hcnd => Eventually.done _ ⟨by simp [hcnd], hmem, hfr⟩⟩
  have hins0 : ∀ d ∈ ds_pre ++ [ins (.jcc cc l)], dirInstrOnly d = true := fun d hd => by
    rcases List.mem_append.mp hd with h1 | h2
    · exact dirInstrOnly_of_clean (hclean d h1)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h2; subst h2; rfl
  have hsb_done0 := sizeBefore_instrOnly kh (ds_pre ++ [ins (.jcc cc l)]) tail hprog_kh' hins0 rfl
  have hsb_done : ∀ m ≤ ds_pre.length + 1, (@Host.exe kh).sizeBefore m = 4 * m :=
    fun m hm => hsb_done0 m (by simp; omega)
  have hsz_b0 : (@Host.exe kh).program[ds_pre.length + 1]? =
      some { directive := .byteArray ⟨#[0]⟩, size := 1 } := by
    rw [@Host.exe_getElem? kh, hprog_kh,
      List.getElem?_append_right (show ds_pre.length ≤ ds_pre.length + 1 by omega)]
    have h1 : ds_pre.length + 1 - ds_pre.length = 1 := by omega
    rw [h1]; rfl
  have hsz_b1 : (@Host.exe kh).program[ds_pre.length + 3]? =
      some { directive := .byteArray ⟨#[1]⟩, size := 1 } := by
    rw [@Host.exe_getElem? kh, hprog_kh,
      List.getElem?_append_right (show ds_pre.length ≤ ds_pre.length + 3 by omega)]
    have h3 : ds_pre.length + 3 - ds_pre.length = 3 := by omega
    rw [h3]; rfl
  have haddr_lbl : @Host.addrOf kh j_k = @Host.addrOf kh (ds_pre.length + 3) := by
    have hsucc := @Host.addrOf_succ kh j_k (.label l) hj_k_elem
    simpa [j_k, kh, x64UniformLayout, Kraken.Layout.size] using hsucc.symm
  have haddr_ne : @Host.addrOf kh j_k ≠ @Host.addrOf kh (ds_pre.length + 1) := by
    intro heq
    have h1 := @Host.sizeBefore_eq_of_addrOf_eq kh j_k (ds_pre.length + 1) heq
    have h2 : (@Host.exe kh).sizeBefore j_k = 4 * (ds_pre.length + 1) + 1 := by
      have hs := Kraken.Executable.sizeBefore_succ (@Host.exe kh) hsz_b0
      rw [hsb_done (ds_pre.length + 1) (Nat.le_refl _)] at hs
      simpa [j_k] using hs
    have h3 := hsb_done (ds_pre.length + 1) (Nat.le_refl _)
    omega
  have ha_done_j : ∀ s0 : MachineData,
      Eventually (@hostStep kh) post_k ⟨s0, @Host.addrOf kh j_k⟩ →
      post_k ⟨s0, @Host.addrOf kh j_k⟩ := by
    intro s0 hej
    cases hej with
    | done _ hp => exact hp
    | step _ mid_p hs0 _ =>
      exfalso
      obtain ⟨pre, hat, hpre⟩ := @Host.directivesAtAddress_addrOf kh (ds_pre.length + 3) _
        hsz_b1 (Nat.zero_lt_succ 0)
      rw [← haddr_lbl] at hat
      have hall : (@Directives.interp (@Host.exe kh).labels
          (pre ++ [{ directive := .byteArray ⟨#[1]⟩, size := 1 }]) s0 (@Host.addrOf kh j_k)
          (fun pc s => .done ⟨s, pc⟩)).All mid_p := by
        simpa [hostStep, step1, Executable.step, ← hat] using hs0
      exact directives_interp_pre_byteArray kh 1 pre s0 _ _ mid_p
        (fun x hx => ⟨Kraken.Executable.mem_of_mem_directivesAtAddress
          (hat ▸ List.mem_append_left _ hx), hpre x hx⟩) hall
  have ha_done_fall : ∀ s0 : MachineData,
      Eventually (@hostStep kh) post_k ⟨s0, @Host.addrOf kh (ds_pre.length + 1)⟩ →
      post_k ⟨s0, @Host.addrOf kh (ds_pre.length + 1)⟩ := by
    intro s0 hej
    cases hej with
    | done _ hp => exact hp
    | step _ mid_p hs0 _ =>
      exfalso
      obtain ⟨pre, hat, hpre⟩ := @Host.directivesAtAddress_addrOf kh (ds_pre.length + 1) _
        hsz_b0 (Nat.zero_lt_succ 0)
      have hall : (@Directives.interp (@Host.exe kh).labels
          (pre ++ [{ directive := .byteArray ⟨#[0]⟩, size := 1 }]) s0
          (@Host.addrOf kh (ds_pre.length + 1))
          (fun pc s => .done ⟨s, pc⟩)).All mid_p := by
        simpa [hostStep, step1, Executable.step, ← hat] using hs0
      exact directives_interp_pre_byteArray kh 0 pre s0 _ _ mid_p
        (fun x hx => ⟨Kraken.Executable.mem_of_mem_directivesAtAddress
          (hat ▸ List.mem_append_left _ hx), hpre x hx⟩) hall
  suffices hloop : ∀ (st : MachineState) (i k_vh : Nat) (sv_i : MachSt x64Arch),
      Eventually (@hostStep kh) post_k st →
      i ≤ ds_pre.length →
      st.pc = @Host.addrOf kh i →
      KrakenSim (machToKraken sv_i) st.data →
      (((ds_pre ++ [ins (.jcc cc l)]).drop i).map (.native (A := x64Arch))).IsInfixAt vh.prog k_vh →
      k + ds_pre.length = k_vh + (ds_pre.length - i) →
      (vllMach x64Arch).Run vh k_vh sv_i post by
    exact hloop ⟨machToKraken sv, @Host.addrOf kh 0⟩ 0 k sv he (Nat.zero_le _) rfl
      (krakenSim_refl _) (by simpa using hc) (by omega)
  intro st i k_vh sv_i he0 hi hpc hsim hdrop hidx_eq
  induction he0 generalizing i k_vh sv_i with
  | done st hp =>
    exfalso
    have heq_addr : @Host.addrOf kh i =
        @Host.addrOf kh (if cond then j_k else ds_pre.length + 1) := hpc.symm.trans hp.1
    have hsb_i := hsb_done i (by omega)
    cases cond with
    | true =>
      have h1 := @Host.sizeBefore_eq_of_addrOf_eq kh i j_k heq_addr
      have h2 : (@Host.exe kh).sizeBefore j_k = 4 * (ds_pre.length + 1) + 1 := by
        have hs := Kraken.Executable.sizeBefore_succ (@Host.exe kh) hsz_b0
        rw [hsb_done (ds_pre.length + 1) (Nat.le_refl _)] at hs
        simpa [j_k] using hs
      omega
    | false =>
      have h1 := @Host.sizeBefore_eq_of_addrOf_eq kh i (ds_pre.length + 1) heq_addr
      have h2 := hsb_done (ds_pre.length + 1) (Nat.le_refl _)
      omega
  | step st mid_p hstep he_next ih =>
    have hdir := splitJcc_directives_at_pref kh ds_pre cc l hprog_kh hclean rfl hi
    by_cases hilt : i < ds_pre.length
    · have hds_drop : (ds_pre ++ [ins (.jcc cc l)]).drop i =
          ds_pre[i] :: (ds_pre ++ [ins (.jcc cc l)]).drop (i + 1) := by
        have hilt' : i < (ds_pre ++ [ins (.jcc cc l)]).length := by simp; omega
        rw [List.drop_eq_getElem_cons hilt', List.getElem_append_left hilt]
      have hk_vh : vh.prog[k_vh]? = some (.native ds_pre[i]) := by
        rw [hds_drop, List.map_cons] at hdrop
        exact hdrop.cons.1
      have hpi : (@Host.prog kh)[i]? = some ds_pre[i] := by
        rw [hprog_kh, List.getElem?_append_left hilt, List.getElem?_eq_getElem hilt]
      have hd_sz : (@Host.layout kh).size ds_pre[i] i = 4 := by
        have hcm := hclean ds_pre[i] (List.getElem_mem hilt)
        cases hdm : ds_pre[i] <;> simp [hdm, dirStraightClean] at hcm; rfl
      have hstep' : ((@_root_.Directive.interp (@Host.exe kh).labels ds_pre[i] st.data
          ⟨@Host.addrOf kh i, @Host.addrOf kh (i + 1)⟩
          (fun s => .done ⟨s, @Host.addrOf kh (i + 1)⟩)
          (fun pc s => .done ⟨s, pc⟩))).All mid_p := by
        have haddr_s : @Host.addrOf kh (i + 1) = @Host.addrOf kh i + 4 := by
          have h := @Host.addrOf_succ kh i _ hpi
          rw [hd_sz] at h; exact h
        have hs0 : ((@Directives.interp (@Host.exe kh).labels
            [{ directive := ds_pre[i], size := 4 }] st.data (@Host.addrOf kh i)
            (fun pc s => .done ⟨s, pc⟩))).All mid_p := by
          simpa [hostStep, step1, Executable.step, hpc, hdir, hpi] using hstep
        simpa [Directives.interp, ← haddr_s] using hs0
      refine vllMach_native_clean_step kh vh (hclean ds_pre[i] (List.getElem_mem hilt))
        hk_vh hstep' hsim fun st1 sv' hmid1 hpc1 hsim1 => ?_
      have hdrop' : (((ds_pre ++ [ins (.jcc cc l)]).drop (i + 1)).map
          (.native (A := x64Arch))).IsInfixAt vh.prog (k_vh + 1) := by
        rw [hds_drop, List.map_cons] at hdrop
        exact hdrop.cons.2
      exact ih st1 hmid1 (i + 1) (k_vh + 1) sv' (by omega) hpc1 hsim1 hdrop' (by omega)
    · have hieq : i = ds_pre.length := Nat.le_antisymm hi (Nat.le_of_not_lt hilt)
      subst hieq
      have hds_drop : (ds_pre ++ [ins (.jcc cc l)]).drop ds_pre.length = [ins (.jcc cc l)] := by
        simp
      have hk_vh : vh.prog[k_vh]? = some (.native (ins (.jcc cc l))) := by
        rw [hds_drop, List.map_singleton] at hdrop
        exact List.isInfixAt_singleton.mp hdrop
      have hpi : (@Host.prog kh)[ds_pre.length]? = some (ins (.jcc cc l)) := by
        rw [hprog_kh, List.getElem?_append_right (Nat.le_refl _)]; simp
      have hs0 : ((@Directives.interp (@Host.exe kh).labels
          [{ directive := ins (.jcc cc l), size := 4 }] st.data (@Host.addrOf kh ds_pre.length)
          (fun pc s => .done ⟨s, pc⟩))).All mid_p := by
        simpa [hostStep, step1, Executable.step, hpc, hdir, hpi] using hstep
      have haddr_succ : @Host.addrOf kh (ds_pre.length + 1) =
          @Host.addrOf kh ds_pre.length + 4 := by
        have h := @Host.addrOf_succ kh ds_pre.length _ hpi
        have hsz : @Kraken.Layout.size _ _ (@Host.layout kh)
            (ins (.jcc cc l)) ds_pre.length = 4 := rfl
        simpa [hsz] using h
      have hlab_k' : (@Host.exe kh).labels.label l = @Host.addrOf kh j_k := hlab_k
      have hcond_sim : cc.interp st.data.status = cc.interp sv_i.flags :=
        (krakenSim_cond hsim cc).symm
      have finishFrame : ∀ s' : MachSt x64Arch,
          (∀ r, s'.gpr r = sv_i.gpr r) → (∀ vr, s'.vreg vr = sv_i.vreg vr) →
          (∀ cd : CondCode, cd.interp s'.flags = cd.interp sv_i.flags) → s'.mem = sv_i.mem →
          st.data.dmem = sv.mem →
          x64Mach.Frame x64CondReads (machToKraken sv) st.data x64Scratch [] fClob →
          (vllMach x64Arch).Frame x64CondReads sv s' x64Scratch [] fClob ∧ s'.mem = sv.mem := by
        intro s' hg hv hcnd hm hm_st hfr_st
        have hsim_s' : KrakenSim (machToKraken s') st.data :=
          ⟨fun r => (regsOfFn_get64 s'.gpr r).trans
              ((hg r).trans ((regsOfFn_get64 sv_i.gpr r).symm.trans (hsim.1 r))),
           fun vr => (zmmsOfFn_get512 s'.vreg vr).trans
              ((hv vr).trans ((zmmsOfFn_get512 sv_i.vreg vr).symm.trans (hsim.2.1 vr))),
           hm.trans hsim.2.2.1,
           (hcnd .c).trans hsim.2.2.2.1, (hcnd .p).trans hsim.2.2.2.2.1,
           (hcnd .z).trans hsim.2.2.2.2.2.1, (hcnd .s).trans hsim.2.2.2.2.2.2.1,
           (hcnd .o).trans hsim.2.2.2.2.2.2.2⟩
        exact ⟨x64_frame_to_vll hsim_s' hfr_st, hm.trans (hsim.2.2.1.trans hm_st)⟩
      refine vllMach_native_jcc_step hk_vh hl ?_ ?_
      · intro hct
        have hct' : cc.interp st.data.status = true := hcond_sim.trans hct
        have hmid : mid_p ⟨st.data, @Host.addrOf kh j_k⟩ := by
          simpa [Directives.interp, _root_.Directive.interp, Instr.interp, Operation.interp,
            hct', hlab_k', Effects.All] using hs0
        have hp_fin := ha_done_j st.data (he_next ⟨st.data, @Host.addrOf kh j_k⟩ hmid)
        rcases hp_fin with ⟨hpc_fin, hm_st, hfr_st⟩
        have hcnd_true : cond = true := by
          cases hcnd : cond with
          | true => rfl
          | false => rw [hcnd] at hpc_fin; exact absurd hpc_fin haddr_ne
        intro s' hg hv hcnd hm
        obtain ⟨hfr_vll, hmem_vll⟩ := finishFrame s' hg hv hcnd hm hm_st hfr_st
        exact (hcont s' hfr_vll hmem_vll).1 hcnd_true
      · intro hcf
        have hcf' : cc.interp st.data.status = false := hcond_sim.trans hcf
        have hmid : mid_p ⟨st.data, @Host.addrOf kh (ds_pre.length + 1)⟩ := by
          simpa [Directives.interp, _root_.Directive.interp, Instr.interp, Operation.interp,
            hcf', haddr_succ, Effects.All] using hs0
        have hp_fin := ha_done_fall st.data
          (he_next ⟨st.data, @Host.addrOf kh (ds_pre.length + 1)⟩ hmid)
        rcases hp_fin with ⟨hpc_fin, hm_st, hfr_st⟩
        have hcnd_false : cond = false := by
          cases hcnd : cond with
          | false => rfl
          | true => rw [hcnd] at hpc_fin; exact absurd hpc_fin.symm haddr_ne
        intro s' hg hv hcnd hm
        obtain ⟨hfr_vll, hmem_vll⟩ := finishFrame s' hg hv hcnd hm hm_st hfr_st
        have hlen_eq : k_vh + 1 = k + (ds_pre ++ [ins (.jcc cc l)]).length := by simp; omega
        exact hlen_eq ▸ (hcont s' hfr_vll hmem_vll).2 hcnd_false

/-! ## 4. Cleanliness and Bounded-Length Lemmas for `Amd64` Builders -/

theorem dirStraightClean_emitClean {is : List _root_.Instr}
    (h : is.all instrStraightClean = true) :
    ∀ d ∈ emitClean is, dirStraightClean d = true := by
  intro d hd
  rcases List.mem_map.mp hd with ⟨i, hi, rfl⟩
  exact List.all_eq_true.mp h i hi

abbrev cleanBound (n : Nat) (is : List _root_.Instr) : Prop :=
  is.all instrStraightClean = true ∧ is.length ≤ n

theorem cleanBound_mono {m n : Nat} {is : List _root_.Instr} (hmn : m ≤ n)
    (h : cleanBound m is) : cleanBound n is :=
  ⟨h.1, Nat.le_trans h.2 hmn⟩

theorem cleanBound_append {m n : Nat} {a b : List _root_.Instr}
    (ha : cleanBound m a) (hb : cleanBound n b) : cleanBound (m + n) (a ++ b) :=
  ⟨by rw [List.all_append, ha.1, hb.1]; rfl, by simp [ha.2, hb.2, Nat.add_le_add]⟩

theorem cleanBound_cons {n : Nat} {i : _root_.Instr} {is : List _root_.Instr}
    (hi : instrStraightClean i = true) (his : cleanBound n is) : cleanBound (n + 1) (i :: is) :=
  ⟨by simp [hi, his.1], by simp [his.2]⟩

theorem clean_small_of_cleanBound {n : Nat} {is : List _root_.Instr}
    (h : cleanBound n is) (hn : n < 2 ^ 61) :
    (∀ d ∈ emitClean (D := ConstExpr) is, dirStraightClean d = true) ∧
      (emitClean (D := ConstExpr) is).length < 2 ^ 61 :=
  ⟨dirStraightClean_emitClean h.1, by simp only [emitClean, List.length_map]; omega⟩

theorem clean_small_emitCleanPair {α : Type} {n : Nat} {x : Option (List _root_.Instr × α)}
    {ds : List _root_.Directive} {a : α} (hpair : emitCleanPair x = some (ds, a))
    (hx : ∀ is b, x = some (is, b) → cleanBound n is) (hn : n < 2 ^ 61) :
    (∀ d ∈ ds, dirStraightClean d = true) ∧ ds.length < 2 ^ 61 := by
  obtain ⟨is, h0, rfl⟩ := emitCleanPair_eq_some.mp hpair
  exact clean_small_of_cleanBound (hx is a h0) hn

theorem instr_moviI (rd : Reg64) (c : BitVec 64) :
    instrStraightClean (moviI rd c) = true := by
  unfold moviI; split <;> rfl

theorem instr_movWI (w : _root_.Width) (rd rs : Reg64) :
    instrStraightClean (movWI w rd rs) = true := by
  cases w <;> rfl

theorem instr_aluBinI (w : _root_.Width) (k : AluBinKind) (rd : Reg64)
    {src : Operand w} (hsrc : opndNoRip src = true) :
    instrStraightClean (aluBinI w k rd src) = true := by
  cases k <;> cases w <;> cases src with
  | regOrMem rm =>
    cases rm <;>
      (dsimp only [opndNoRip, rmNoRip] at hsrc
       simp [instrStraightClean, opStraightClean, dstNoRip, rmNoRip, opndNoRip, hsrc])
  | imm c =>
    dsimp only [opndNoRip] at hsrc
    simp [instrStraightClean, opStraightClean, dstNoRip, rmNoRip, opndNoRip, hsrc]

private theorem reg_ne_rip (r : Reg64) :
    (some (RegOrRip.reg r) != some RegOrRip.rip) = true := by
  cases r <;> rfl

theorem clean_addrToExprIns (a : AddrArg Reg64) :
    cleanBound 2 (addrToExprIns a).1 ∧ addrNoRip (addrToExprIns a).2.1 = true := by
  cases a with
  | baseDisp r off =>
    dsimp only [addrToExprIns]; split
    · exact ⟨⟨rfl, by simp⟩, rfl⟩
    · split
      · exact ⟨⟨rfl, by simp⟩, rfl⟩
      · exact ⟨cleanBound_cons (instr_moviI _ _)
          ⟨by simp [instrStraightClean, opStraightClean, addrNoRip, atSIB, constNoLab,
            reg_ne_rip r], by simp⟩, rfl⟩
  | baseIdxDisp rb ri sc off =>
    dsimp only [addrToExprIns]; split
    · exact ⟨⟨rfl, by simp⟩, by simp [addrNoRip, constNoLab, reg_ne_rip rb]⟩
    · exact ⟨cleanBound_cons (instr_moviI _ _)
        ⟨by simp [instrStraightClean, opStraightClean, addrNoRip, atSIB, constNoLab,
          reg_ne_rip rb], by simp⟩, by simp [addrNoRip, constNoLab, reg_ne_rip .r10]⟩
  | imm addr => exact ⟨cleanBound_cons (instr_moviI _ _) ⟨rfl, by simp⟩, rfl⟩

end LeanQbe.T.Vll
