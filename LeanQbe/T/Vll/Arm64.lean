module

public import LeanQbe.T.Vll.Arch
public import LeanQbe.T.Arm64.Frame
public import LeanQbe.T.Arm64.Isel
import LeanQbe.T.AbiLemmas

/-!
# AArch64 `BedrockMach` L1 Architecture (`Vll.Arm64`)

Instantiates `LeanQbe.T.Vll.Arch` for AAPCS64 AArch64 (`arm64Arch`) with zero `Amd64` or
`Kraken.X64` imports and zero public `*Lemmas*` imports:

* Exact state conversion between `MachData Arm64.Reg Empty StatusFlags` and Kraken's
  `MachineData`, plus scratch-modulo agreement `arm64StateRel`.
* Precise static effect summary `arm64NativeEffect : Directive → NativeEffect Arm64.Reg Empty`
  covering every Kraken AArch64 `Operation` and `Directive` constructor.
* Relational escape-hatch semantics `arm64NativeStep` backed directly by Kraken's
  `Directive.interp`.
* `arm64Arch : Arch` matching `Arm64/Frame.lean` + AAPCS64 (`writeSubZeroExtend`, `.linkReg .X30`,
  16-byte SP alignment, 4-byte PC alignment, NZCV flag model).
* `arm64Arch_wf : arm64Arch.Wf` and `arm64Arch_nativeEffectSound : arm64Arch.NativeEffectSound`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Vll

open LeanQbe.T
open LeanQbe.T.Arm64

/-! ## 1. VLL ↔ Kraken `MachineData` Conversion & Labels Environment -/

/-- Pack a VLL GPR function `Arm64.Reg → BitVec 64` into Kraken's `Reg64s` record. -/
@[expose] def vllToReg64s (g : Arm64.Reg → BitVec 64) : Reg64s where
  X0  := .ofBitVec (g (.reg .X0));  X1  := .ofBitVec (g (.reg .X1))
  X2  := .ofBitVec (g (.reg .X2));  X3  := .ofBitVec (g (.reg .X3))
  X4  := .ofBitVec (g (.reg .X4));  X5  := .ofBitVec (g (.reg .X5))
  X6  := .ofBitVec (g (.reg .X6));  X7  := .ofBitVec (g (.reg .X7))
  X8  := .ofBitVec (g (.reg .X8));  X9  := .ofBitVec (g (.reg .X9))
  X10 := .ofBitVec (g (.reg .X10)); X11 := .ofBitVec (g (.reg .X11))
  X12 := .ofBitVec (g (.reg .X12)); X13 := .ofBitVec (g (.reg .X13))
  X14 := .ofBitVec (g (.reg .X14)); X15 := .ofBitVec (g (.reg .X15))
  X16 := .ofBitVec (g (.reg .X16)); X17 := .ofBitVec (g (.reg .X17))
  X18 := .ofBitVec (g (.reg .X18)); X19 := .ofBitVec (g (.reg .X19))
  X20 := .ofBitVec (g (.reg .X20)); X21 := .ofBitVec (g (.reg .X21))
  X22 := .ofBitVec (g (.reg .X22)); X23 := .ofBitVec (g (.reg .X23))
  X24 := .ofBitVec (g (.reg .X24)); X25 := .ofBitVec (g (.reg .X25))
  X26 := .ofBitVec (g (.reg .X26)); X27 := .ofBitVec (g (.reg .X27))
  X28 := .ofBitVec (g (.reg .X28)); X29 := .ofBitVec (g (.reg .X29))
  X30 := .ofBitVec (g (.reg .X30)); SP  := .ofBitVec (g .SP)

/-- Convert VLL `MachData Arm64.Reg Empty StatusFlags` to Kraken AArch64 `MachineData`. -/
@[expose] def vllToMachData (s : MachData Arm64.Reg Empty StatusFlags) : MachineData where
  regs := vllToReg64s s.gpr
  status := s.flags
  dmem := s.mem

/-- Convert Kraken AArch64 `MachineData` to VLL `MachData Arm64.Reg Empty StatusFlags`. -/
@[expose] def machDataToVll (s : MachineData) : MachData Arm64.Reg Empty StatusFlags where
  gpr := Arm64.get s
  vreg := Empty.elim
  flags := s.status
  mem := s.dmem

/-- Kraken `Labels` environment induced by a VLL symbol-to-address map `symAddr`. -/
@[expose, instance_reducible] def labelsOfSymAddr (symAddr : Sym → BitVec 64) : Labels where
  label l := Int64.ofBitVec (symAddr l)

/-- Agreement between a VLL `MachData` and Kraken `MachineData` on all non-scratch GPRs
(including `sp`, `x0..x15`, `x18..x30`), all NZCV status flags, and data memory. -/
@[expose] def arm64StateRel (sv : MachData Arm64.Reg Empty StatusFlags) (sm : MachineData) :
    Prop :=
  (∀ r : Arm64.Reg, r ∉ armScratch → Arm64.get sm r = sv.gpr r) ∧
  sm.status = sv.flags ∧
  sm.dmem = sv.mem

theorem get_vllToMachData (s : MachData Arm64.Reg Empty StatusFlags) (r : Arm64.Reg) :
    Arm64.get (vllToMachData s) r = s.gpr r := by
  cases r with
  | SP => rfl
  | reg x => cases x <;> rfl

theorem vllToMachData_machDataToVll (sm : MachineData) :
    vllToMachData (machDataToVll sm) = sm := by
  rcases sm with ⟨⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15,
    x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, sp⟩, st, dm⟩
  rfl

theorem machDataToVll_vllToMachData (s : MachData Arm64.Reg Empty StatusFlags) :
    machDataToVll (vllToMachData s) = s := by
  cases s with
  | mk gpr vreg flags mem =>
    dsimp only [machDataToVll]
    congr 1
    · funext r; exact get_vllToMachData ⟨gpr, vreg, flags, mem⟩ r
    · funext v; exact v.elim

theorem arm64StateRel_machDataToVll (sm : MachineData) :
    arm64StateRel (machDataToVll sm) sm :=
  ⟨fun _ _ => rfl, rfl, rfl⟩

theorem arm64StateRel_vllToMachData (sv : MachData Arm64.Reg Empty StatusFlags) :
    arm64StateRel sv (vllToMachData sv) :=
  ⟨fun r _ => get_vllToMachData sv r, rfl, rfl⟩

/-! ## 2. Precise Static `arm64NativeEffect` & Relational `arm64NativeStep` -/

/-- Register list extracted from `XRegOrXzr` (`[]` for `XZR`). -/
@[expose] def regOfXzr : XRegOrXzr → List Arm64.Reg
  | .reg x => [.reg x]
  | .XZR => []

/-- Register list extracted from `RegOrZr w` / `RegOrSp w`. -/
@[expose] def regOfZr {w : RegWidth} (r : RegOrZr w) : List Arm64.Reg := regOfXzr r.base
@[expose] def regOfSp {w : RegWidth} (r : RegOrSp w) : List Arm64.Reg := [r.base]

/-- GPRs read / clobbered by `AddrExpr`, `AddrOrLit`, `UnscaledAddrExpr`, `ExtOrImmReg`,
and `ShiftRegExpr`. -/
@[expose] def addrExprUses (a : AddrExpr) : List Arm64.Reg :=
  a.base.base :: match a.off with | .imm _ => [] | .reg er => regOfXzr er.reg.reg.base

@[expose] def addrExprClob (a : AddrExpr) : List Arm64.Reg :=
  match a.off with | .imm i => if i.index.isSome then [a.base.base] else [] | .reg _ => []

@[expose] def addrOrLitUses : AddrOrLit → List Arm64.Reg
  | .addr a => addrExprUses a | .lit _ => []

@[expose] def addrOrLitClob : AddrOrLit → List Arm64.Reg
  | .addr a => addrExprClob a | .lit _ => []

@[expose] def unscaledAddrUses (a : UnscaledAddrExpr) : List Arm64.Reg := [a.base.base]

@[expose] def extOrImmUses : ExtOrImmReg → List Arm64.Reg
  | .ext e => regOfXzr e.reg.reg.base | .imm _ => []

@[expose] def shiftRegUses {w : RegWidth} (sr : ShiftRegExpr w) : List Arm64.Reg := regOfZr sr.reg

/-- Concise `NativeEffect` constructor for AArch64 instructions (empty vector bank). -/
@[expose, reducible] def mkArmEff (gUses gClob : List Arm64.Reg)
    (fClob : FlagMask := maskNone) (readsMem writesMem isControl : Bool := false) :
    NativeEffect Arm64.Reg Empty :=
  { gUses, gClob, vUses := [], vClob := [], fClob, readsMem, writesMem, isControl }

/-- Exact static read/write/clobber summary of a Kraken AArch64 `Operation w`. -/
@[expose] def opNativeEffect {w : RegWidth} : Operation w → NativeEffect Arm64.Reg Empty
  | .LDR dst src | .LDRSW dst src =>
    mkArmEff (addrOrLitUses src) (regOfZr dst ++ addrOrLitClob src) (readsMem := true)
  | .LDRB dst src | .LDRSB dst src | .LDRH dst src | .LDRSH dst src =>
    mkArmEff (addrExprUses src) (regOfZr dst ++ addrExprClob src) (readsMem := true)
  | .LDP d1 d2 src | .LDPSW d1 d2 src =>
    mkArmEff (addrExprUses src) (regOfZr d1 ++ regOfZr d2 ++ addrExprClob src) (readsMem := true)
  | .LDUR dst src | .LDURB dst src | .LDURSB dst src
  | .LDURH dst src | .LDURSH dst src | .LDURSW dst src =>
    mkArmEff (unscaledAddrUses src) (regOfZr dst) (readsMem := true)
  | .STR src dst | .STRB src dst | .STRH src dst =>
    mkArmEff (regOfZr src ++ addrExprUses dst) (addrExprClob dst) (writesMem := true)
  | .STP s1 s2 dst =>
    mkArmEff (regOfZr s1 ++ regOfZr s2 ++ addrExprUses dst) (addrExprClob dst) (writesMem := true)
  | .STUR src dst | .STURB src dst | .STURH src dst =>
    mkArmEff (regOfZr src ++ unscaledAddrUses dst) [] (writesMem := true)
  | .ADD_e dst s1 s2 | .SUB_e dst s1 s2 =>
    mkArmEff (regOfSp s1 ++ extOrImmUses s2) (regOfSp dst)
  | .ADDS_e dst s1 s2 | .SUBS_e dst s1 s2 =>
    mkArmEff (regOfSp s1 ++ extOrImmUses s2) (regOfZr dst) (fClob := maskNZCV)
  | .ADD_s dst s1 s2 | .SUB_s dst s1 s2 | .AND_s dst s1 s2 | .ORR_s dst s1 s2
  | .ORN_s dst s1 s2 | .EOR_s dst s1 s2 | .EON_s dst s1 s2 | .BIC_s dst s1 s2 =>
    mkArmEff (regOfZr s1 ++ shiftRegUses s2) (regOfZr dst)
  | .ADDS_s dst s1 s2 | .SUBS_s dst s1 s2 | .ANDS_s dst s1 s2 | .BICS_s dst s1 s2 =>
    mkArmEff (regOfZr s1 ++ shiftRegUses s2) (regOfZr dst) (fClob := maskNZCV)
  | .AND_i dst s1 _ | .ORR_i dst s1 _ | .EOR_i dst s1 _ =>
    mkArmEff (regOfZr s1) (regOfSp dst)
  | .ANDS_i dst s1 _ =>
    mkArmEff (regOfZr s1) (regOfZr dst) (fClob := maskNZCV)
  | .ADC dst s1 s2 | .SBC dst s1 s2 | .SDIV dst s1 s2 | .UDIV dst s1 s2
  | .SMULH dst s1 s2 | .UMULH dst s1 s2 | .EXTR dst s1 s2 _
  | .LSLV dst s1 s2 | .LSRV dst s1 s2 | .ASRV dst s1 s2 | .RORV dst s1 s2
  | .CSEL dst s1 s2 _ | .CSINC dst s1 s2 _ | .CSINV dst s1 s2 _ | .CSNEG dst s1 s2 _ =>
    mkArmEff (regOfZr s1 ++ regOfZr s2) (regOfZr dst)
  | .ADCS dst s1 s2 | .SBCS dst s1 s2 =>
    mkArmEff (regOfZr s1 ++ regOfZr s2) (regOfZr dst) (fClob := maskNZCV)
  | .MADD dst s1 s2 s3 | .MSUB dst s1 s2 s3
  | .SMADDL dst s1 s2 s3 | .UMADDL dst s1 s2 s3
  | .SMSUBL dst s1 s2 s3 | .UMSUBL dst s1 s2 s3 =>
    mkArmEff (regOfZr s1 ++ regOfZr s2 ++ regOfZr s3) (regOfZr dst)
  | .SBFM dst src _ _ | .UBFM dst src _ _
  | .CLZ dst src | .CLS dst src | .RBIT dst src
  | .REV dst src | .REV16 dst src | .REV32 dst src =>
    mkArmEff (regOfZr src) (regOfZr dst)
  | .BFM dst src _ _ => mkArmEff (regOfZr dst ++ regOfZr src) (regOfZr dst)
  | .MOVZ dst _ _ | .MOVN dst _ _ | .ADR dst _ | .ADRP dst _ => mkArmEff [] (regOfZr dst)
  | .MOVK dst _ _ => mkArmEff (regOfZr dst) (regOfZr dst)
  | .CCMP_reg s1 s2 _ _ | .CCMN_reg s1 s2 _ _ =>
    mkArmEff (regOfZr s1 ++ regOfZr s2) [] (fClob := maskNZCV)
  | .CCMP_imm s1 _ _ _ | .CCMN_imm s1 _ _ _ =>
    mkArmEff (regOfZr s1) [] (fClob := maskNZCV)
  | .B _ | .B_cond _ _ => mkArmEff [] [] (isControl := true)
  | .BL _ => mkArmEff [] [.reg .X30] (isControl := true)
  | .BLR tgt => mkArmEff (regOfZr tgt) [.reg .X30] (isControl := true)
  | .BR tgt | .RET tgt | .CBZ tgt _ | .CBNZ tgt _ | .TBZ tgt _ _ | .TBNZ tgt _ _ =>
    mkArmEff (regOfZr tgt) [] (isControl := true)
  | .NOP => mkArmEff [] []

/-- Static effect summary for a Kraken AArch64 `Directive`. -/
@[expose] def arm64NativeEffect : _root_.Directive → NativeEffect Arm64.Reg Empty
  | .instr i => opNativeEffect i.operation
  | .label _ | .byteArray _ | .word _ _ => mkArmEff [] []

/-- Relational operational semantics of `.native d` (`d : Directive`), defined directly via
Kraken AArch64 `Directive.interp` across all PC intervals `p`. -/
@[expose] def arm64NativeStep (d : _root_.Directive) (symAddr : Sym → BitVec 64)
    (s : MachData Arm64.Reg Empty StatusFlags)
    (out : NativeOutcome Arm64.Reg Empty StatusFlags) : Prop :=
  letI : Labels := labelsOfSymAddr symAddr
  let sm := vllToMachData s
  match out with
  | .fall s' =>
    ∀ p : Std.Rco Int64,
      (d.interp sm p (fun sm' => .done ⟨sm', 0⟩) (fun _ _ => .unimplemented "jmp")).All
        (fun st => machDataToVll st.data = s')
  | .jump pc' s' =>
    ∀ p : Std.Rco Int64,
      (d.interp sm p (fun _ => .unimplemented "fall") (fun a sm' => .done ⟨sm', a⟩)).All
        (fun st => st.pc.toBitVec = pc' ∧ machDataToVll st.data = s')
  | .halt _ _ => False

/-! ## 3. AArch64 Flag Semantics, `arm64Abi`, and `arm64Arch : Arch` -/

/-- Flag clobber mask for `alu op w rd lhs rhs setFlags` on AArch64. -/
@[expose] def arm64AluClob (_ : CoreAlu) (sf : Bool) : FlagMask :=
  if sf then maskNZCV else maskNone

/-- Exact NZCV flag update for `alu op w rd lhs rhs setFlags` on AArch64. -/
@[expose] def arm64AluFlags (op : CoreAlu) (w : Width) (sf : Bool)
    (a b : BitVec w.bits) (f : StatusFlags) : StatusFlags :=
  if !sf then f
  else match op with
    | .add => StatusFlags.adds (a + b) a b
    | .sub => StatusFlags.subs (a - b) a b
    | _ => StatusFlags.from_result (op.eval w a b) { c := false, v := false }

/-- Exact NZCV flag update for `cmp w lhs rhs` (`SUBS`). -/
@[expose] def arm64CmpFlags (w : Width) (a b : BitVec w.bits) (_ : StatusFlags) : StatusFlags :=
  StatusFlags.subs (a - b) a b

/-- Exact NZCV flag update for `test w lhs rhs` (`ANDS`). -/
@[expose] def arm64TestFlags (w : Width) (a b : BitVec w.bits) (_ : StatusFlags) : StatusFlags :=
  StatusFlags.from_result (a &&& b) { c := false, v := false }

/-- Architectural status flags produced by `armClearFlags` (`adds xzr, xzr, xzr`). -/
@[expose] def arm64ClearFlagsVal : StatusFlags :=
  StatusFlags.adds 0#64 0#64 0#64

/-- AAPCS64 AArch64 ABI record matching `LeanQbe.T.Arm64.armFrame`. -/
@[expose, reducible] def arm64Abi : Abi Arm64.Reg Empty where
  sp := .SP
  raKind := .linkReg (.reg .X30)
  scratch := armScratch
  allocatable := armFrame.allocatable
  callerSaved := armFrame.allocatable ++ armScratch ++ [.reg .X18, .reg .X30]
  calleeSaved := armFrame.calleeSaved
  argRegs := armFrame.argRegs
  retRegs := armFrame.retRegs
  vecScratch := []
  vecAllocatable := []
  vecArgRegs := []
  vecRetRegs := []
  bitWidths := [8, 16, 32, 64]
  stackAlign := 16
  pcAlign := 4
  pcName := "pc"
  frameSize := armFrameSize
  spEntry := fun sp => sp.toNat % 16 = 0
  spOk := fun sp => sp.toNat % 16 = 0
  prologueClob := maskNone
  epilogueClob := maskNone
  canonAbiClob := fun _ => maskNone
  leafZeroFrame := true

/-- `BedrockMach` L1 AArch64 architecture description (`arm64Arch`). -/
@[expose, reducible] def arm64Arch : Arch where
  Reg := Arm64.Reg
  VReg := Empty
  Cond := ArmCond
  Flags := StatusFlags
  Native := _root_.Directive
  abi := arm64Abi
  writeSub := writeSubZeroExtend
  condReads := armCondReads
  negCond := armNegCond
  evalCond := fun f c => c.interp f
  zeroFlags := armZeroFlags
  clearFlagsVal := arm64ClearFlagsVal
  aluClob := arm64AluClob
  aluFlags := arm64AluFlags
  cmpClob := maskNZCV
  cmpFlags := arm64CmpFlags
  testClob := maskNZCV
  testFlags := arm64TestFlags
  jnzGprClob := maskNone
  jnzGprFlags := fun _ f => f
  prologueFlags := fun _ f => f
  epilogueFlags := fun _ f => f
  canonAbiFlags := fun _ f => f
  nativeStep := arm64NativeStep
  nativeEffect := arm64NativeEffect
  zeroUpper32Write := true

/-! ## 4. Well-Formedness (`arm64Arch_wf`) & Native Effect Soundness -/

/-- Any two `StatusFlags` trivially agree outside `maskNZCV`, since every `ArmCond` reads at
least one of `N`, `Z`, `C`, `V`. -/
theorem arm64Arch_flagsAgree_nzcv (f f' : StatusFlags) :
    arm64Arch.FlagsAgree f f' maskNZCV := by
  intro c hc
  cases c <;>
    simp [FlagMask.disjoint, armCondReads, maskNZCV, maskN, maskZ, maskC, maskV] at hc

/-- Proof that `arm64Arch` satisfies every `Arch.Wf` architectural invariant. -/
theorem arm64Arch_wf : arm64Arch.Wf where
  sp_disj := by simp [Abi.raRegs, RaKind.raRegs]
  scratch_disj := by simp
  cs_disj := by simp
  ra_disj := by simp [Abi.raRegs, RaKind.raRegs]
  argRegs_nodup := by decide
  retRegs_nodup := by decide
  callerSaved_sub := fun _ hr => List.mem_append_left _ (List.mem_append_left _ hr)
  align_pos := by decide
  slots_le_frameSize := fun ns => by dsimp only [arm64Arch, arm64Abi, armFrameSize]; omega
  linkReg_frameSize := fun _ _ ns => by dsimp only [armFrameSize]; omega
  spOk_frame := fun _ ns hsp => aligned16_sub hsp (by dsimp only [armFrameSize]; omega)
  spEntry_call := fun _ ns hsp => by
    simpa [BitVec.sub_zero, Abi.raBytes, RaKind.raBytes] using
      aligned16_sub hsp (by dsimp only [armFrameSize]; omega)
  writeSub_setWidth := writeSubZeroExtend_setWidth
  writeSub_w64 := writeSubZeroExtend_w64
  negCond_reads := armNegCond_reads
  negCond_eval := fun f c => armNegCond_interp c f
  clearFlags_zero := by
    intro c hc
    simp only [armZeroFlags, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> decide
  aluFlags_frame := fun _ _ sf _ _ f => by
    cases sf
    · intro _ _; simp [arm64AluFlags]
    · exact arm64Arch_flagsAgree_nzcv f _
  cmpFlags_frame := fun _ _ _ f => arm64Arch_flagsAgree_nzcv f _
  testFlags_frame := fun _ _ _ f => arm64Arch_flagsAgree_nzcv f _
  jnzGprFlags_frame := fun _ _ _ _ => rfl
  prologueFlags_frame := fun _ _ _ _ => rfl
  epilogueFlags_frame := fun _ _ _ _ => rfl
  canonAbiFlags_frame := fun _ _ _ _ => rfl

private def EffOk (eff : NativeEffect Arm64.Reg Empty) (s s' : MachineData) : Prop :=
  (∀ r : Arm64.Reg, r ∉ eff.gClob → Arm64.get s' r = Arm64.get s r) ∧
  arm64Arch.FlagsAgree s.status s'.status eff.fClob ∧
  (eff.writesMem = false → s'.dmem = s.dmem)

private theorem effOk_refl (eff : NativeEffect Arm64.Reg Empty) (s : MachineData) :
    EffOk eff s s := ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl⟩

private theorem effOk_trans {eff : NativeEffect Arm64.Reg Empty} {s₁ s₂ s₃ : MachineData}
    (h1 : EffOk eff s₁ s₂) (h2 : EffOk eff s₂ s₃) : EffOk eff s₁ s₃ :=
  ⟨fun r hr => (h2.1 r hr).trans (h1.1 r hr),
   fun c hc => (h2.2.1 c hc).trans (h1.2.1 c hc),
   fun hw => (h2.2.2 hw).trans (h1.2.2 hw)⟩

private theorem get_setRegOrZr_ne {w : RegWidth} (regs : Reg64s) (dst : RegOrZr w)
    (v : w.type) {r : Arm64.Reg} (hr : r ∉ regOfZr dst) :
    (regs.setRegOrZr dst v).getRegOrSp64 r = regs.getRegOrSp64 r := by
  cases dst with
  | low xr w =>
    cases xr with
    | XZR => cases w <;> rfl
    | reg xd =>
      have hne : r ≠ .reg xd := fun e => hr (e ▸ List.mem_cons_self)
      cases w with
      | W64 => exact get_wr_of_ne ⟨regs, ⟨false, false, false, false⟩, ∅⟩ xd v r hne
      | W32 => exact get_wr_of_ne ⟨regs, ⟨false, false, false, false⟩, ∅⟩ xd (v.zeroExtend 64) r hne

private theorem get_setRegOrSp_ne {w : RegWidth} (regs : Reg64s) (dst : RegOrSp w)
    (v : w.type) {r : Arm64.Reg} (hr : r ∉ regOfSp dst) :
    (regs.setRegOrSp dst v).getRegOrSp64 r = regs.getRegOrSp64 r := by
  cases dst with
  | low xs w =>
    have hne : r ≠ xs := fun e => hr (e ▸ List.mem_cons_self)
    cases xs with
    | SP => cases r with | SP => exact absurd rfl hne | reg xr => cases w <;> cases xr <;> rfl
    | reg xd =>
      cases w with
      | W64 => exact get_wr_of_ne ⟨regs, ⟨false, false, false, false⟩, ∅⟩ xd v r hne
      | W32 => exact get_wr_of_ne ⟨regs, ⟨false, false, false, false⟩, ∅⟩ xd (v.zeroExtend 64) r hne

private theorem effOk_setZr {eff : NativeEffect Arm64.Reg Empty} {w : RegWidth}
    {s : MachineData} (dst : RegOrZr w) (v : w.type)
    (hsub : ∀ r ∈ regOfZr dst, r ∈ eff.gClob) :
    EffOk eff s { s with regs := s.regs.setRegOrZr dst v } :=
  ⟨fun r hr => get_setRegOrZr_ne s.regs dst v (fun hm => hr (hsub r hm)),
   fun _ _ => rfl, fun _ => rfl⟩

private theorem effOk_setSp {eff : NativeEffect Arm64.Reg Empty} {w : RegWidth}
    {s : MachineData} (dst : RegOrSp w) (v : w.type)
    (hsub : ∀ r ∈ regOfSp dst, r ∈ eff.gClob) :
    EffOk eff s { s with regs := s.regs.setRegOrSp dst v } :=
  ⟨fun r hr => get_setRegOrSp_ne s.regs dst v (fun hm => hr (hsub r hm)),
   fun _ _ => rfl, fun _ => rfl⟩

private theorem effOk_setStatus {eff : NativeEffect Arm64.Reg Empty} {s : MachineData}
    (st : StatusFlags) (hf : eff.fClob = maskNZCV) : EffOk eff s { s with status := st } :=
  ⟨fun _ _ => rfl, hf ▸ arm64Arch_flagsAgree_nzcv s.status st, fun _ => rfl⟩

private theorem effOk_setMem {eff : NativeEffect Arm64.Reg Empty} {s : MachineData}
    (m' : DataMem) (hw : eff.writesMem = true) : EffOk eff s { s with dmem := m' } :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun h => by rw [hw] at h; cases h⟩

private theorem effOk_addrEval [Labels] {eff : NativeEffect Arm64.Reg Empty}
    (a : AddrExpr) (s : MachineData) (p : Std.Rco Int64)
    (hsub : ∀ r ∈ addrExprClob a, r ∈ eff.gClob) : EffOk eff s (a.eval s p).2 := by
  cases a with
  | mk base off =>
    cases off with
    | reg _ => exact effOk_refl eff s
    | imm i =>
      cases hi : i.index with
      | none => simp [AddrExpr.eval, hi]; exact effOk_refl eff s
      | some idx =>
        simp only [AddrExpr.eval, hi]
        refine effOk_setSp base _ (fun r hr => hsub r ?_)
        simp only [addrExprClob, hi, Option.isSome_some, ↓reduceIte, regOfSp] at hr ⊢
        exact hr

private theorem all_checkSP {a : AddrExpr} {s : MachineData} {ok : Unit → Effects}
    {P : MachineState → Prop} (h : (a.checkSPAlignment s ok).All P) : (ok ()).All P := by
  dsimp only [AddrExpr.checkSPAlignment] at h
  split at h <;> first | exact h | (split at h <;> first | cases h | exact h)

private theorem all_uCheckSP {a : UnscaledAddrExpr} {s : MachineData} {ok : Unit → Effects}
    {P : MachineState → Prop} (h : (a.checkSPAlignment s ok).All P) : (ok ()).All P := by
  dsimp only [UnscaledAddrExpr.checkSPAlignment] at h
  split at h <;> first | exact h | (split at h <;> first | cases h | exact h)

private theorem all_load {s : MachineData} {addr : BitVec 64} {w : MemWidth}
    {ret : w.type → MachineData → Effects} {P : MachineState → Prop}
    (h : (s.load addr w ret).All P) : ∃ v, (ret v s).All P := by
  dsimp only [MachineData.load, Effects.All] at h
  split at h <;> first | exact ⟨_, h⟩ | cases h

private theorem all_store {s : MachineData} {addr : BitVec 64} {w : MemWidth}
    {v : w.type} {ret : MachineData → Effects} {P : MachineState → Prop}
    (h : (s.store addr v ret).All P) : ∃ m', (ret { s with dmem := m' }).All P := by
  dsimp only [MachineData.store, Effects.All] at h
  split at h <;> first | exact ⟨_, h⟩ | cases h

private theorem all_addrLoad [Labels] (eff : NativeEffect Arm64.Reg Empty)
    {a : AddrExpr} {w : MemWidth} {s : MachineData} {p : Std.Rco Int64}
    {ret : w.type → MachineData → Effects} {P : MachineState → Prop}
    (hsub : ∀ r ∈ addrExprClob a, r ∈ eff.gClob) (h : (a.interpLoad (w := w) s p ret).All P) :
    ∃ v s', EffOk eff s s' ∧ (ret v s').All P := by
  obtain ⟨v, hv⟩ := all_load (all_checkSP h)
  exact ⟨v, (a.eval s p).2, effOk_addrEval a s p hsub, hv⟩

private theorem all_aolLoad [Labels] (eff : NativeEffect Arm64.Reg Empty)
    {a : AddrOrLit} {w : MemWidth} {s : MachineData} {p : Std.Rco Int64}
    {ret : w.type → MachineData → Effects} {P : MachineState → Prop}
    (hsub : ∀ r ∈ addrOrLitClob a, r ∈ eff.gClob) (h : (a.interpLoad (w := w) s p ret).All P) :
    ∃ v s', EffOk eff s s' ∧ (ret v s').All P := by
  cases a with
  | addr ae => exact all_addrLoad eff hsub h
  | lit lit =>
    cases lit with
    | addr _ => obtain ⟨v, hv⟩ := all_load h; exact ⟨v, s, effOk_refl eff s, hv⟩
    | pool _ => exact ⟨_, s, effOk_refl eff s, h⟩

private theorem op_interp_eff [Labels] {w : RegWidth} (op : Operation w) (s : MachineData)
    (p : Std.Rco Int64) (next : MachineData → Effects) (jmp : Int64 → MachineData → Effects)
    (P : MachineState → Prop) (R : Prop)
    (hnext : ∀ s', EffOk (opNativeEffect op) s s' → (next s').All P → R)
    (hjmp : ∀ a s', EffOk (opNativeEffect op) s s' → (jmp a s').All P → R)
    (h : (op.interp p s next jmp).All P) : R := by
  cases op with
  | LDR dst src | LDRSW dst src =>
    dsimp only [Operation.interp, opNativeEffect] at h hnext
    obtain ⟨v, s₁, h1, h2⟩ := all_aolLoad
      (mkArmEff (addrOrLitUses src) (regOfZr dst ++ addrOrLitClob src) (readsMem := true))
      (fun _ hr => List.mem_append_right _ hr) h
    exact hnext _ (effOk_trans h1 (effOk_setZr dst _ (fun _ hr => List.mem_append_left _ hr))) h2
  | LDRB dst src | LDRSB dst src | LDRH dst src | LDRSH dst src =>
    dsimp only [Operation.interp, opNativeEffect] at h hnext
    obtain ⟨v, s₁, h1, h2⟩ := all_addrLoad
      (mkArmEff (addrExprUses src) (regOfZr dst ++ addrExprClob src) (readsMem := true))
      (fun _ hr => List.mem_append_right _ hr) h
    exact hnext _ (effOk_trans h1 (effOk_setZr dst _ (fun _ hr => List.mem_append_left _ hr))) h2
  | LDP d1 d2 src | LDPSW d1 d2 src =>
    dsimp only [Operation.interp, opNativeEffect] at h hnext
    obtain ⟨v1, h2⟩ := all_load (all_checkSP h)
    obtain ⟨v2, h3⟩ := all_load h2
    refine hnext _ (effOk_trans (effOk_addrEval src s p ?_)
      (effOk_trans (effOk_setZr d1 _ ?_) (effOk_setZr d2 _ ?_))) h3 <;>
      intro _ hr <;> simp [hr]
  | LDUR dst src | LDURB dst src | LDURSB dst src
  | LDURH dst src | LDURSH dst src | LDURSW dst src =>
    dsimp only [Operation.interp, opNativeEffect] at h hnext
    obtain ⟨v, hv⟩ := all_load (all_uCheckSP h)
    exact hnext _ (effOk_setZr dst _ (fun _ hr => hr)) hv
  | STR src dst | STRB src dst | STRH src dst =>
    dsimp only [Operation.interp, opNativeEffect] at h hnext
    obtain ⟨m', hm'⟩ := all_store (all_checkSP h)
    exact hnext _ (effOk_trans (effOk_addrEval dst s p (fun _ hr => hr)) (effOk_setMem m' rfl)) hm'
  | STP s1 s2 dst =>
    dsimp only [Operation.interp, opNativeEffect] at h hnext
    obtain ⟨m1, h2⟩ := all_store (all_checkSP h)
    obtain ⟨m2, h3⟩ := all_store h2
    exact hnext _ (effOk_trans (effOk_addrEval dst s p (fun _ hr => hr))
      (effOk_trans (effOk_setMem m1 rfl) (effOk_setMem m2 rfl))) h3
  | STUR src dst | STURB src dst | STURH src dst =>
    dsimp only [Operation.interp, opNativeEffect] at h hnext
    obtain ⟨m', hm'⟩ := all_store (all_uCheckSP h)
    exact hnext _ (effOk_setMem m' rfl) hm'
  | ADD_e dst _ _ | SUB_e dst _ _ | AND_i dst _ _ | ORR_i dst _ _ | EOR_i dst _ _ =>
    exact hnext _ (effOk_setSp dst _ (fun _ hr => hr)) h
  | ADDS_e dst _ _ | SUBS_e dst _ _ | ADDS_s dst _ _ | SUBS_s dst _ _
  | ADCS dst _ _ | SBCS dst _ _ | ANDS_i dst _ _ | ANDS_s dst _ _ | BICS_s dst _ _ =>
    exact hnext _ (effOk_trans (effOk_setStatus _ rfl) (effOk_setZr dst _ (fun _ hr => hr))) h
  | ADD_s dst _ _ | SUB_s dst _ _ | ADC dst _ _ | SBC dst _ _
  | SDIV dst _ _ | UDIV dst _ _ | MADD dst _ _ _ | MSUB dst _ _ _
  | SMULH dst _ _ | UMULH dst _ _ | SMADDL dst _ _ _ | UMADDL dst _ _ _
  | SMSUBL dst _ _ _ | UMSUBL dst _ _ _
  | AND_s dst _ _ | ORR_s dst _ _ | ORN_s dst _ _ | EOR_s dst _ _ | EON_s dst _ _
  | BIC_s dst _ _ | BFM dst _ _ _ | SBFM dst _ _ _ | UBFM dst _ _ _
  | CLZ dst _ | CLS dst _ | RBIT dst _ | REV dst _ | REV16 dst _ | REV32 dst _
  | EXTR dst _ _ _ | MOVZ dst _ _ | MOVK dst _ _ | MOVN dst _ _
  | LSLV dst _ _ | LSRV dst _ _ | ASRV dst _ _ | RORV dst _ _
  | CSEL dst _ _ _ | CSINC dst _ _ _ | CSINV dst _ _ _ | CSNEG dst _ _ _
  | ADR dst _ | ADRP dst _ =>
    exact hnext _ (effOk_setZr dst _ (fun _ hr => hr)) h
  | CCMP_reg _ _ _ _ | CCMP_imm _ _ _ _ | CCMN_reg _ _ _ _ | CCMN_imm _ _ _ _ =>
    exact hnext _ (effOk_setStatus _ rfl) h
  | B _ | BR _ | RET _ => exact hjmp _ _ (effOk_refl _ s) h
  | BL _ | BLR _ => exact hjmp _ _ (effOk_setZr RegOrZr.X30 _ (fun _ hr => hr)) h
  | B_cond _ _ | CBZ _ _ | CBNZ _ _ | TBZ _ _ _ | TBNZ _ _ _ =>
    dsimp only [Operation.interp] at h
    split at h
    · exact hjmp _ _ (effOk_refl _ s) h
    · exact hnext _ (effOk_refl _ s) h
  | NOP => exact hnext _ (effOk_refl _ s) h

private theorem directive_interp_eff [Labels] (d : _root_.Directive) (s : MachineData)
    (p : Std.Rco Int64) (next : MachineData → Effects) (jmp : Int64 → MachineData → Effects)
    (P : MachineState → Prop) (R : Prop)
    (hnext : ∀ s', EffOk (arm64NativeEffect d) s s' → (next s').All P → R)
    (hjmp : ∀ a s', EffOk (arm64NativeEffect d) s s' → (jmp a s').All P → R)
    (h : (d.interp s p next jmp).All P) : R := by
  cases d with
  | label _ => exact hnext s (effOk_refl _ s) h
  | instr i => exact op_interp_eff i.operation s p next jmp P R hnext hjmp h
  | byteArray bs =>
    dsimp only [Directive.interp] at h
    split at h <;> first | exact hnext s (effOk_refl _ s) h | cases h
  | word bytes _ =>
    cases bytes with | zero => exact hnext s (effOk_refl _ s) h | succ _ => cases h

/-- Proof that `arm64NativeStep` respects `arm64NativeEffect`'s GPR, vector, flag, and memory
frame summary for every Kraken AArch64 directive. -/
theorem arm64Arch_nativeEffectSound : arm64Arch.NativeEffectSound := by
  intro d symAddr s out hstep
  letI : Labels := labelsOfSymAddr symAddr
  cases out with
  | halt _ _ => exact False.elim hstep
  | fall s' =>
    refine directive_interp_eff d (vllToMachData s) ⟨0, 4⟩ _ _ _ _ ?_ (fun _ _ _ hf => by cases hf)
      (hstep ⟨0, 4⟩)
    intro sm' heff hEq
    have hs' : machDataToVll sm' = s' := hEq
    subst hs'
    exact ⟨fun r hr => (heff.1 r hr).trans (get_vllToMachData s r),
      fun vr => vr.elim, heff.2.1, heff.2.2⟩
  | jump pc' s' =>
    refine directive_interp_eff d (vllToMachData s) ⟨0, 4⟩ _ _ _ _ (fun _ _ hf => by cases hf) ?_
      (hstep ⟨0, 4⟩)
    intro _ sm' heff hEq
    have hs' : machDataToVll sm' = s' := hEq.2
    subst hs'
    exact ⟨fun r hr => (heff.1 r hr).trans (get_vllToMachData s r),
      fun vr => vr.elim, heff.2.1, heff.2.2⟩

end LeanQbe.T.Vll
