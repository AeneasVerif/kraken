module

public import LeanQbe.T.Vll.Arch
public import LeanQbe.T.Amd64.IselVec
import LeanQbe.T.AbiLemmas

/-!
# Target Architecture Instance for SysV x86-64 (`Amd64.VllX64`)

Defines `x64Arch : Arch`, `x64Arch_wf : x64Arch.Wf`, and
`x64Arch_nativeEffectSound : x64Arch.NativeEffectSound` for `BedrockMach` L1 VLLIR on x86-64
(`Reg := Reg64`, `VReg := RegMm`, `Cond := CondCode`, `Flags := StatusFlags`,
`Native := _root_.Directive`, `writeSub := writeSubX64`), with zero Arm64/AArch64 or public
`*Lemmas*` imports.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Vll

/-- Convert a `BedrockMach` scalar `Vll.Width` to Kraken `Width`. -/
@[expose, reducible] def Width.toX64 : Width → _root_.Width
  | .w8 => .W8 | .w16 => .W16 | .w32 => .W32 | .w64 => .W64

end LeanQbe.T.Vll

namespace LeanQbe.T.Amd64

open LeanQbe.T
open LeanQbe.T.Vll

/-! ## 1. Width Mapping, Registers, and Flag Helpers -/

/-- All 16 general-purpose registers in Kraken `Reg64`. -/
@[expose] def x64AllGprs : List Reg64 :=
  [.rax, .rbx, .rcx, .rdx, .rsi, .rdi, .rsp, .rbp, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

/-- First 16 vector registers (`mm0..mm15`) zero-uppered by `vzeroupper`. -/
@[expose] def x64Vec16Regs : List RegMm :=
  [.mm0, .mm1, .mm2, .mm3, .mm4, .mm5, .mm6, .mm7,
   .mm8, .mm9, .mm10, .mm11, .mm12, .mm13, .mm14, .mm15]

/-- Flag state produced by `clearFlags` (`xorl %r10d, %r10d`). -/
@[expose] def x64ClearFlagsVal : StatusFlags :=
  { cf := false, pf := true, af := false, zf := true, sf := false, of := false }

/-- Flag state produced by `cmp a b` at width `w` (`sub` flags). -/
@[expose] def x64CmpFlags (w : Vll.Width) (a b : BitVec w.bits) (_ : StatusFlags) : StatusFlags :=
  let v := a - b
  StatusFlags.from_result v {
    cf := v.unsigned != a.unsigned - b.unsigned
    af := (v.take 4).unsigned != (a.take 4).unsigned - (b.take 4).unsigned
    of := v.signed != a.signed - b.signed }

/-- Flag state produced by `test a b` at width `w`. -/
@[expose] def x64TestFlags (w : Vll.Width) (a b : BitVec w.bits) (_ : StatusFlags) : StatusFlags :=
  StatusFlags.from_result (a &&& b) { cf := false, af := false, of := false }

/-- Flag state produced by `jnzGpr r l` (`testb %rb, %rb`). -/
@[expose] def x64JnzGprFlags (v : BitVec 64) (_ : StatusFlags) : StatusFlags :=
  StatusFlags.from_result (v.setWidth 8) { cf := false, af := false, of := false }

/-- Flag state update for `alu op w _ _ _ setFlags` on x86-64. -/
@[expose] def x64AluFlags (op : CoreAlu) (w : Vll.Width) (sf : Bool)
    (a b : BitVec w.bits) (f : StatusFlags) : StatusFlags :=
  if !sf then f
  else match op with
    | .add =>
      let v := a + b
      StatusFlags.from_result v {
        cf := v.unsigned != a.unsigned + b.unsigned
        af := (v.take 4).unsigned != (a.take 4).unsigned + (b.take 4).unsigned
        of := v.signed != a.signed + b.signed }
    | .sub => x64CmpFlags w a b f
    | .and => x64TestFlags w a b f
    | .or  => StatusFlags.from_result (a ||| b) { cf := false, af := false, of := false }
    | .xor => StatusFlags.from_result (a ^^^ b) { cf := false, af := false, of := false }
    | .shl | .lshr | .ashr | .mul =>
      StatusFlags.from_result (op.eval w a b) { cf := false, af := false, of := false }

/-! ## 2. Native `.native` Escape-Hatch Semantics and Effects -/

/-- Reachability of a `MachineState` along non-faulting branches of a Kraken `Effects` tree. -/
inductive EffectsReaches : Effects → MachineState → Prop where
  | done {st} : EffectsReaches (.done st) st
  | undefined {α : Type} [NondetSupportingType α] {cont : α → Effects} {v : α} {st} :
      EffectsReaches (cont v) st → EffectsReaches (.undefined cont) st
  | require_read {span} {ok : Unit → Effects} {st} :
      EffectsReaches (ok ()) st → EffectsReaches (.require_read_access span ok) st
  | require_write {span} {ok : Unit → Effects} {st} :
      EffectsReaches (ok ()) st → EffectsReaches (.require_write_access span ok) st
  | require_exec {p} {ok : Unit → Effects} {st} :
      EffectsReaches (ok ()) st → EffectsReaches (.require_exec_access p ok) st

/-- Convert Kraken `MachineData` into `MachData Reg64 RegMm StatusFlags`. -/
@[expose] def krakenToMachData (sk : MachineData) : MachData Reg64 RegMm StatusFlags :=
  { gpr := sk.regs.get64, vreg := sk.zmms.get512, flags := sk.status, mem := sk.dmem }

/-- Extract vector register modified by an `AvxDst`, if it targets a register. -/
@[expose] def avxDstVecClob {aw : AvxWidth} : AvxDst aw → List RegMm
  | .avx r => [r.base]
  | .mem _ => []

/-- True iff an `AvxDst` targets memory. -/
@[expose] def avxDstWritesMem {aw : AvxWidth} : AvxDst aw → Bool
  | .avx _ => false
  | .mem _ => true

/-- Static effect summary of an `AvxOperation`. -/
@[expose] def x64AvxNativeEffect {aw : AvxWidth} : AvxOperation aw → NativeEffect Reg64 RegMm
  | .vmovIn _ dst _ | .vmovq dst _ =>
    { gClob := [], vClob := [dst.base], fClob := maskNone, writesMem := false, isControl := false }
  | .vmovOut _ (.reg r) _ =>
    { gClob := [r.base], vClob := [], fClob := maskNone, writesMem := false, isControl := false }
  | .vmovOut _ (.mem _) _ =>
    { gClob := [], vClob := [], fClob := maskNone, writesMem := true, isControl := false }
  | .vzeroupper =>
    { gClob := [], vClob := x64Vec16Regs, fClob := maskNone, writesMem := false,
      isControl := false }
  | .movups d _ | .vmovups d _ | .movaps d _ | .subps d _ | .addps d _
  | .movdqu d _ | .movdqa d _ | .paddd d _ | .pshufb d _ | .pshufd d _ _
  | .palignr d _ _ | .pblendw d _ _ | .vmovdqu d _ | .sha256rnds2 d _
  | .sha256msg1 d _ | .sha256msg2 d _ | .vmovdqu32 d _ | .vmovdqa32 d _
  | .vpaddd d _ _ | .vprord d _ _ | .vpsrld d _ _ | .vpternlogd d _ _ _ =>
    { gClob := [], vClob := avxDstVecClob d, fClob := maskNone,
      writesMem := avxDstWritesMem d, isControl := false }
/-- Static effect summary of a scalar `Operation`. -/
@[expose] def x64OpNativeEffect {w : _root_.Width} : Operation w → NativeEffect Reg64 RegMm
  | .nop _ | .nopalign _ _ =>
    { gClob := [], vClob := [], fClob := maskNone, readsMem := false,
      writesMem := false, isControl := false }
  | .lea dst _ =>
    { gClob := [dst.base], vClob := [], fClob := maskNone, readsMem := false,
      writesMem := false, isControl := false }
  | .mov (.reg dst) _ =>
    { gClob := [dst.base], vClob := [], fClob := maskNone, writesMem := false, isControl := false }
  | .jcc _ _ | .jmp _ =>
    { gClob := [], vClob := [], fClob := maskNone, writesMem := false, isControl := true }
  | .call _ | .ret =>
    { gClob := x64AllGprs, vClob := [], fClob := maskAll, readsMem := true,
      writesMem := true, isControl := true }
  | _ =>
    { gClob := x64AllGprs, vClob := [], fClob := maskAll, readsMem := true,
      writesMem := true, isControl := false }

/-- Sound static effect summary `nativeEffect` for `_root_.Directive` on x86-64. -/
@[expose] def x64NativeEffect : _root_.Directive → NativeEffect Reg64 RegMm
  | .label _ | .byteArray _ | .word _ _ =>
    { gClob := [], vClob := [], fClob := maskNone, readsMem := false,
      writesMem := false, isControl := false }
  | .instr (.regular _ _ op) => x64OpNativeEffect op
  | .instr (.avx _ _ aop) => x64AvxNativeEffect aop

/-- Operational semantics `nativeStep` of `.native d` grounded in Kraken's `Directive.interp`. -/
@[expose] def x64NativeStep (d : _root_.Directive) (symAddr : Sym → BitVec 64)
    (s : MachData Reg64 RegMm StatusFlags)
    (out : NativeOutcome Reg64 RegMm StatusFlags) : Prop :=
  letI : Labels := { label := fun l => Int64.ofBitVec (symAddr l) }
  ∃ (sk0 : MachineData) (p : Std.Rco Int64),
    (∀ r, sk0.regs.get64 r = s.gpr r) ∧ (∀ vr, sk0.zmms.get512 vr = s.vreg vr) ∧
    (∀ cc : CondCode, cc.interp sk0.status = cc.interp s.flags) ∧ sk0.dmem = s.mem ∧
    match out with
    | .fall s' => ∃ sk', EffectsReaches
        (d.interp sk0 p (fun s1 => .done ⟨s1, 0⟩) (fun _ _ => .unimplemented "jmp")) ⟨sk', 0⟩ ∧
        s' = krakenToMachData sk'
    | .jump pc' s' => ∃ sk', EffectsReaches
        (d.interp sk0 p (fun _ => .unimplemented "fall") (fun a s1 => .done ⟨s1, a⟩))
        ⟨sk', Int64.ofBitVec pc'⟩ ∧ s' = krakenToMachData sk'
    | .halt _ _ => False

/-! ## 3. `x64Arch : Arch` and `x64Arch_wf : x64Arch.Wf` -/

/-- Target architecture description `x64Arch : Arch` for SysV x86-64 `BedrockMach` L1 VLLIR. -/
@[expose, reducible] def x64Arch : Arch where
  Reg := Reg64
  VReg := RegMm
  Cond := CondCode
  Flags := StatusFlags
  Native := _root_.Directive
  abi := {
    sp := .rsp, raKind := .stack, scratch := x64Scratch, allocatable := x64Frame.allocatable,
    callerSaved := x64Scratch ++ x64Frame.allocatable, calleeSaved := x64Frame.calleeSaved,
    argRegs := x64Frame.argRegs, retRegs := x64Frame.retRegs, vecScratch := x64VecScratch,
    vecAllocatable := x64VecAllocatable, vecArgRegs := x64VecArgRegs, vecRetRegs := x64VecRetRegs,
    bitWidths := x64Frame.bitWidths, stackAlign := 16, pcAlign := 1, pcName := "rip",
    frameSize := x64FrameSize, spEntry := fun sp => (sp + 8#64).toNat % 16 = 0,
    spOk := fun _ => True, prologueClob := maskAll, epilogueClob := maskAll,
    canonAbiClob := fun _ => maskNone, leafZeroFrame := true }
  writeSub := writeSubX64
  condReads := x64CondReads
  negCond := x64NegCond
  evalCond := fun f cc => cc.interp f
  zeroFlags := [.c, .o]
  clearFlagsVal := x64ClearFlagsVal
  aluClob := fun _ _ => maskAll
  aluFlags := x64AluFlags
  cmpClob := maskAll
  cmpFlags := x64CmpFlags
  testClob := maskAll
  testFlags := x64TestFlags
  jnzGprClob := maskAll
  jnzGprFlags := x64JnzGprFlags
  nativeStep := x64NativeStep
  nativeEffect := x64NativeEffect
  zeroUpper32Write := true
  xor32ZeroClearFlags := true

private theorem x64_flagsAgree_maskAll (f f' : StatusFlags) :
    x64Arch.FlagsAgree f f' maskAll := by
  intro cc h
  cases cc <;> simp [x64CondReads, FlagMask.disjoint,
    maskAll, maskOF, maskCF, maskZF, maskSF, maskPF] at h

/-- Proof that `x64Arch` satisfies every `Arch.Wf` architectural invariant. -/
theorem x64Arch_wf : x64Arch.Wf where
  sp_disj := by dsimp only [x64Arch, x64Frame, Abi.raRegs, RaKind.raRegs]; simp [x64Scratch]
  scratch_disj := by
    intro r hr; dsimp only [x64Arch] at hr ⊢
    simp only [x64Scratch, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp
  cs_disj := by
    intro r hr; dsimp only [x64Arch, x64Frame] at hr ⊢
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  ra_disj := fun _ hr => by simp only [x64Arch, Abi.raRegs, RaKind.raRegs, List.not_mem_nil] at hr
  argRegs_nodup := by decide
  retRegs_nodup := by decide
  callerSaved_sub _ hr := List.mem_append_right _ hr
  align_pos := by decide
  slots_le_frameSize ns := by dsimp only [x64Arch, x64FrameSize]; split <;> omega
  linkReg_frameSize _ h := by simp [x64Arch] at h
  spOk_frame _ _ _ := trivial
  spEntry_call sp ns hsp := by
    dsimp only [x64Arch, Abi.raBytes, RaKind.raBytes] at hsp ⊢
    have hmod : x64FrameSize ns % 16 = 8 := by
      dsimp only [x64FrameSize]
      rcases Nat.mod_two_eq_zero_or_one ns with h | h <;> simp [h] <;> omega
    exact aligned16_add8_sub_call hsp hmod
  writeSub_setWidth := writeSubX64_setWidth
  writeSub_w64 := writeSubX64_w64
  negCond_reads := x64NegCond_reads
  negCond_eval f cc := x64NegCond_interp cc f
  clearFlags_zero cc hc := by
    simp only [x64Arch, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> rfl
  aluFlags_frame _ _ _ _ _ f' := x64_flagsAgree_maskAll f' _
  cmpFlags_frame _ _ _ f' := x64_flagsAgree_maskAll f' _
  testFlags_frame _ _ _ f' := x64_flagsAgree_maskAll f' _
  jnzGprFlags_frame _ f' := x64_flagsAgree_maskAll f' _
  prologueFlags_frame _ f' := x64_flagsAgree_maskAll f' _
  epilogueFlags_frame _ f' := x64_flagsAgree_maskAll f' _
  canonAbiFlags_frame _ _ _ _ := rfl

/-! ## 4. `x64Arch_nativeEffectSound : x64Arch.NativeEffectSound` -/

/-- Soundness of `Effects.All` along `EffectsReaches`. -/
theorem EffectsReaches.all_sound {e : Effects} {Q : MachineState → Prop}
    (hall : e.All Q) {st : MachineState} (h : EffectsReaches e st) : Q st := by
  induction h with
  | done => exact hall
  | @undefined _ _ _ v _ _ ih => exact ih (hall v)
  | require_read _ ih | require_write _ ih | require_exec _ ih => exact ih hall

private def EffectsPreserves (Q : MachineState → Prop) : Effects → Prop
  | .done a => Q a
  | .unimplemented _ | .gp_unaligned _ _ | .divide_error
  | .nonmem_load _ _ _ _ | .nonmem_store _ _ _ _ => True
  | @Effects.undefined _ _ cont => ∀ v, EffectsPreserves Q (cont v)
  | .require_read_access _ ok | .require_write_access _ ok | .require_exec_access _ ok =>
    EffectsPreserves Q (ok ())

private theorem EffectsPreserves.reaches_sound {e : Effects} {Q : MachineState → Prop}
    (hp : EffectsPreserves Q e) {st : MachineState} (h : EffectsReaches e st) : Q st := by
  induction h with
  | done => exact hp
  | @undefined _ _ _ v _ _ ih => exact ih (hp v)
  | require_read _ ih | require_write _ ih | require_exec _ ih => exact ih hp

private theorem mem_x64AllGprs (r : Reg64) : r ∈ x64AllGprs := by cases r <;> simp [x64AllGprs]

private theorem reg64s_get64_set_ne {w : _root_.Width} (regs : Reg64s) (d : Reg w)
    (v : w.type) (r : Reg64) (hne : r ≠ d.base) : (regs.set d v).get64 r = regs.get64 r := by
  cases d with
  | low db => cases w <;> simp only [Reg.base] at hne <;>
    simpa only [Reg64s.set] using Reg64s.get64_set64_of_ne regs db r _ hne.symm
  | ah => simp only [Reg.base] at hne; exact Reg64s.get64_set64_of_ne regs .rax r _ hne.symm
  | bh => simp only [Reg.base] at hne; exact Reg64s.get64_set64_of_ne regs .rbx r _ hne.symm
  | ch => simp only [Reg.base] at hne; exact Reg64s.get64_set64_of_ne regs .rcx r _ hne.symm
  | dh => simp only [Reg.base] at hne; exact Reg64s.get64_set64_of_ne regs .rdx r _ hne.symm

private theorem regZmms_set512_ne (zmms : RegZmms) {r r' : RegMm} (h : r' ≠ r) (v : BitVec 512) :
    (zmms.set512 r v).get512 r' = zmms.get512 r' := by
  cases r <;> cases r' <;> first | rfl | exact absurd rfl h

private theorem mem_x64Vec16_zeroUpper (zmms : RegZmms) (vr : RegMm)
    (hn : vr ∉ x64Vec16Regs) : zmms.zeroUpper.get512 vr = zmms.get512 vr := by
  have hfold : ∀ (rs : List RegMm) (s0 : RegZmms), (∀ r ∈ rs, vr ≠ r) →
      (rs.foldl (fun s r => s.set512 r (((s.get512 r).take 128).zeroExtend 512)) s0).get512 vr =
        s0.get512 vr := by
    intro rs; induction rs with
    | nil => intro _ _; rfl
    | cons r _ ih =>
      intro s0 hrs
      rw [List.foldl_cons, ih _ (fun x hx => hrs x (List.mem_cons_of_mem _ hx)),
        regZmms_set512_ne s0 (hrs r List.mem_cons_self)]
  exact hfold x64Vec16Regs zmms fun r hr he => hn (he ▸ hr)

private theorem load_p {s : MachineData} {a : BitVec 64} {w : _root_.Width}
    {ret : w.type → MachineData → Effects} {Q : MachineState → Prop}
    (h : ∀ v, EffectsPreserves Q (ret v s)) : EffectsPreserves Q (s.load a w ret) := by
  dsimp only [MachineData.load, require_access]; split <;> dsimp only [EffectsPreserves] <;>
    cases Mem.loadInt s.dmem a w.bytes <;> first | exact h _ | exact trivial

private theorem store_p {s : MachineData} {a : BitVec 64} {w : _root_.Width} {v : w.type}
    {ret : MachineData → Effects} {Q : MachineState → Prop}
    (h : ∀ dm', EffectsPreserves Q (ret { s with dmem := dm' })) :
    EffectsPreserves Q (s.store a v ret) := by
  dsimp only [MachineData.store, require_access]; split <;> dsimp only [EffectsPreserves] <;>
    cases Mem.loadInt s.dmem a w.bytes <;> first | exact h _ | exact trivial

private theorem rm_p [Labels] [AddressSize] {w : _root_.Width} {rm : RegOrMem w} {s : MachineData}
    {p : Std.Rco Int64} {ret : w.type → MachineData → Effects} {Q : MachineState → Prop}
    (h : ∀ v, EffectsPreserves Q (ret v s)) : EffectsPreserves Q (rm.interp s p ret) := by
  cases rm with | reg _ => exact h _ | mem _ => exact load_p h

private theorem opnd_p [Labels] [AddressSize] {w : _root_.Width} {o : Operand w} {s : MachineData}
    {p : Std.Rco Int64} {ret : w.type → MachineData → Effects} {Q : MachineState → Prop}
    (h : ∀ v, EffectsPreserves Q (ret v s)) : EffectsPreserves Q (o.interp s p ret) := by
  cases o with | regOrMem _ => exact rm_p h | imm _ => exact h _

private theorem rrm_p [Labels] [AddressSize] {rm : RelRegOrMem} {s : MachineData}
    {p : Std.Rco Int64} {ret : BitVec 64 → MachineData → Effects} {Q : MachineState → Prop}
    (h : ∀ v, EffectsPreserves Q (ret v s)) : EffectsPreserves Q (rm.interp s p ret) := by
  cases rm with | rel _ | reg _ => exact h _ | mem _ => exact load_p h

private theorem set_p_zmms [Labels] [AddressSize] {w : _root_.Width} (s : MachineData) (d : Dst w)
    (v : w.type) (p : Std.Rco Int64) (ret : MachineData → Effects) (Q : MachineState → Prop)
    (h : ∀ s', s'.zmms = s.zmms → EffectsPreserves Q (ret s')) :
    EffectsPreserves Q (s.set d v p ret) := by
  cases d with | reg _ => exact h _ rfl | mem _ => exact store_p fun _ => h _ rfl

private theorem foldl_stepString_zmms [AddressSize] (rs : List Reg64) (s : MachineData) :
    (rs.foldl (fun acc r => acc.stepString r 0) s).zmms = s.zmms := by
  induction rs generalizing s with | nil => rfl | cons r _ ih => exact ih (s.stepString r 0)

private theorem rep_p_zmms [AddressSize] {step : MachineData → (MachineData → Effects) → Effects}
    (hs : ∀ s1 n1 Q1, (∀ s2, s2.zmms = s1.zmms → EffectsPreserves Q1 (n1 s2)) →
      EffectsPreserves Q1 (step s1 n1))
    {rs : List Reg64} {s : MachineData} {next : MachineData → Effects} {Q : MachineState → Prop}
    (hn : ∀ s', s'.zmms = s.zmms → EffectsPreserves Q (next s')) :
    EffectsPreserves Q (MachineData.repString step rs s next) := by
  dsimp only [MachineData.repString]; split
  · exact fun b => by cases b; exact hn _ rfl; exact hn _ (foldl_stepString_zmms _ _)
  · suffices ∀ c s0, (∀ s', s'.zmms = s0.zmms → EffectsPreserves Q (next s')) →
        EffectsPreserves Q (MachineData.repeatString step c s0 next) from this _ s hn
    intro c; induction c with
    | zero => intro _ h0; exact h0 _ rfl
    | succ _ ih => intro _ h0; exact hs _ _ Q fun _ h1 => ih _ fun _ h2 => h0 _ (h2.trans h1)

private theorem avxRm_p [Labels] [AddressSize] {w : AvxWidth} {rm : AvxRegOrMem w}
    {s : MachineData} {p : Std.Rco Int64} {ret : w.type → MachineData → Effects} {chk : Bool}
    {Q : MachineState → Prop} (h : ∀ v, EffectsPreserves Q (ret v s)) :
    EffectsPreserves Q (rm.interp s p ret chk) := by
  cases rm with
  | avx _ => exact h _
  | mem _ =>
    dsimp only [AvxRegOrMem.interp, MachineData.loadAvx, require_access]; split
    · exact trivial
    · split <;> dsimp only [EffectsPreserves] <;> cases Mem.loadInt s.dmem _ _ <;>
        first | exact h _ | exact trivial

private theorem storeAvx_p {aw : AvxWidth} {s : MachineData} {a : BitVec 64} {v : aw.type}
    {ret : MachineData → Effects} {chk : Bool} {Q : MachineState → Prop}
    (h : ∀ dm', EffectsPreserves Q (ret { s with dmem := dm' })) :
    EffectsPreserves Q (s.storeAvx a v ret chk) := by
  dsimp only [MachineData.storeAvx, require_access]; split
  · exact trivial
  · split <;> dsimp only [EffectsPreserves] <;> cases Mem.loadInt s.dmem a aw.bytes <;>
      first | exact h _ | exact trivial

private theorem regZmms_set_ne (leg : Bool) {aw : AvxWidth} (zmms : RegZmms) (d : AvxReg aw)
    (v : aw.type) (vr : RegMm) (h : vr ≠ d.base) :
    (if leg then zmms.setLegacy d v else zmms.set d v).get512 vr = zmms.get512 vr := by
  cases leg <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> cases d <;>
    simp only [AvxReg.base] at h <;>
    simpa only [RegZmms.set, RegZmms.setLegacy] using regZmms_set512_ne zmms h _

private theorem setAvx_p [Labels] [AddressSize] {aw : AvxWidth} (leg : Bool) (s : MachineData)
    (d : AvxDst aw) (v : aw.type) (p : Std.Rco Int64) (ret : MachineData → Effects) (chk : Bool)
    (Q : MachineState → Prop)
    (h : ∀ s', s'.regs = s.regs → s'.status = s.status →
      (∀ vr, vr ∉ avxDstVecClob d → s'.zmms.get512 vr = s.zmms.get512 vr) →
      (avxDstWritesMem d = false → s'.dmem = s.dmem) → EffectsPreserves Q (ret s')) :
    EffectsPreserves Q (if leg then s.setAvxLegacy d v p ret chk else s.setAvx d v p ret chk) := by
  cases d with
  | avx r =>
    have hv : ∀ vr, vr ∉ avxDstVecClob (.avx r) →
        (if leg then s.zmms.setLegacy r v else s.zmms.set r v).get512 vr = s.zmms.get512 vr :=
      fun vr hvr => regZmms_set_ne leg s.zmms r v vr fun e => hvr (e ▸ List.mem_cons_self)
    cases leg
    · exact h _ rfl rfl (by simpa only [Bool.false_eq_true, ↓reduceIte, MachineData.setAvx,
        MachineData.setAvxReg] using hv) (fun _ => rfl)
    · exact h _ rfl rfl (by simpa only [↓reduceIte, MachineData.setAvxLegacy,
        MachineData.setAvxLegacyReg] using hv) (fun _ => rfl)
  | mem _ =>
    cases leg <;> exact storeAvx_p fun _ => h _ rfl rfl (fun _ _ => rfl) (fun hf => by cases hf)

private theorem avxOp_p_eff [Labels] [AddressSize] {w : AvxWidth}
    (aop : AvxOperation w) (p : Std.Rco Int64) (s0 : MachineData)
    (next : MachineData → Effects) (Q : MachineState → Prop)
    (hn : ∀ s', (∀ r, r ∉ (x64AvxNativeEffect aop).gClob → s'.regs.get64 r = s0.regs.get64 r) →
      (∀ vr, vr ∉ (x64AvxNativeEffect aop).vClob → s'.zmms.get512 vr = s0.zmms.get512 vr) →
      s'.status = s0.status →
      ((x64AvxNativeEffect aop).writesMem = false → s'.dmem = s0.dmem) →
      EffectsPreserves Q (next s')) :
    EffectsPreserves Q (aop.interp p s0 next) := by
  cases aop with
  | vmovIn _ dst src =>
    refine @rm_p _ _ _ src s0 p (fun v s => next (s.setAvxReg dst (v.zeroExtend _))) Q fun v => ?_
    refine hn _ (fun _ _ => rfl) (fun vr hvr => ?_) rfl (fun _ => rfl)
    cases dst <;> simpa [MachineData.setAvxReg, RegZmms.set] using
      regZmms_set512_ne s0.zmms (fun e => hvr (by simp [x64AvxNativeEffect, AvxReg.base, e])) _
  | vmovOut _ dst _ =>
    cases dst with
    | reg r =>
      refine hn _ (fun x hx => ?_) (fun _ _ => rfl) rfl (fun _ => rfl)
      exact reg64s_get64_set_ne s0.regs r _ x fun e => hx (e ▸ List.mem_cons_self)
    | mem _ =>
      exact store_p fun _ => hn _ (fun _ _ => rfl) (fun _ _ => rfl) rfl (fun h => by cases h)
  | vmovq dst _ =>
    refine hn _ (fun _ _ => rfl) (fun vr hvr => ?_) rfl (fun _ => rfl)
    cases dst <;> simpa [MachineData.setAvxReg, RegZmms.set] using
      regZmms_set512_ne s0.zmms (fun e => hvr (by simp [x64AvxNativeEffect, AvxReg.base, e])) _
  | vzeroupper =>
    exact hn _ (fun _ _ => rfl) (fun vr hvr => mem_x64Vec16_zeroUpper s0.zmms vr hvr)
      rfl (fun _ => rfl)
  | vmovups d _ | vmovdqu d _ | vmovdqu32 d _ | vmovdqa32 d _
  | vpaddd d _ _ | vprord d _ _ | vpsrld d _ _ | vpternlogd d _ _ _ =>
    dsimp only [AvxOperation.interp]; repeat (refine avxRm_p fun _ => ?_)
    exact setAvx_p false s0 d _ p next _ Q fun s' hr hs hv hm =>
      hn s' (fun _ _ => hr ▸ rfl) hv hs hm
  | movups d _ | movaps d _ | movdqu d _ | movdqa d _ | pshufd d _ _ | subps d _ | addps d _
  | paddd d _ | pshufb d _ | palignr d _ _ | pblendw d _ _
  | sha256rnds2 d _ | sha256msg1 d _ | sha256msg2 d _ =>
    dsimp only [AvxOperation.interp]; repeat (refine avxRm_p fun _ => ?_)
    exact setAvx_p true s0 d _ p next _ Q fun s' hr hs hv hm =>
      hn s' (fun _ _ => hr ▸ rfl) hv hs hm

private theorem op_p_zmms [Labels] [AddressSize] {w : _root_.Width}
    (op : Operation w) (p : Std.Rco Int64) (s0 : MachineData) (next : MachineData → Effects)
    (jmp : Int64 → MachineData → Effects) (Q : MachineState → Prop)
    (hn : ∀ s', s'.zmms = s0.zmms → EffectsPreserves Q (next s'))
    (hj : ∀ a s', s'.zmms = s0.zmms → EffectsPreserves Q (jmp a s')) :
    EffectsPreserves Q (op.interp p s0 next jmp) := by
  cases op with
  | jcc _ _ => dsimp only [Operation.interp]; split; exact hj _ _ rfl; exact hn _ rfl
  | jmp _ | call _ | ret =>
    dsimp only [Operation.interp]
    repeat first | apply rrm_p; intro _ | apply load_p; intro _ | apply store_p; intro _
    exact hj _ _ rfl
  | movs _ =>
    dsimp only [Operation.interp]; split
    · refine rep_p_zmms (fun _ _ _ h1 => ?_) hn
      apply load_p; intro _; apply store_p; intro _; exact h1 _ rfl
    · apply load_p; intro _; apply store_p; intro _; exact hn _ rfl
  | stos _ =>
    dsimp only [Operation.interp]; split
    · refine rep_p_zmms (fun _ _ _ h1 => ?_) hn; apply store_p; intro _; exact h1 _ rfl
    · apply store_p; intro _; exact hn _ rfl
  | div _ | idiv _ =>
    dsimp only [Operation.interp]; apply rm_p; intro _
    repeat (first | exact trivial | (intro _; dsimp only; exact hn _ rfl) | split)
  | mul _ | imul1 _ =>
    dsimp only [Operation.interp]; apply rm_p; intro _; intro _ _ _ _; dsimp only
    apply hn; split <;> rfl
  | imul _ _ _ =>
    dsimp only [Operation.interp]; apply rm_p; intro _; apply opnd_p; intro _
    apply set_p_zmms; intro _ h1; intro _ _ _ _; dsimp only; exact hn _ (by rw [← h1])
  | shl _ _ | shr _ _ | sar _ _ | shld _ _ _ | shrd _ _ _
  | rol _ _ | ror _ _ | rcr _ _ | rcl _ _ =>
    dsimp only [Operation.interp, Reg.interp]
    repeat (first
      | apply rm_p; intro _
      | exact set_p_zmms _ _ _ p next Q hn
      | dsimp only
      | split
      | intro _)
  | bswap _ | lzcnt _ _ | tzcnt _ _ | popcnt _ _ | rorx _ _ _
  | shlx _ _ _ | shrx _ _ _ | sarx _ _ _ =>
    cases w <;> dsimp only [Operation.interp] <;>
      repeat (first | apply rm_p; intro _ | dsimp only | intro _ | exact hn _ rfl)
  | _ =>
    dsimp only [Operation.interp, Reg.interp]
    repeat (first
      | apply opnd_p; intro _
      | apply rm_p; intro _
      | apply load_p; intro _
      | apply store_p; intro _
      | exact set_p_zmms _ _ _ p next Q hn
      | dsimp only
      | intro _
      | exact hn _ rfl)

private def EffPres (ef : NativeEffect Reg64 RegMm) (s0 s' : MachineData) : Prop :=
  (∀ r, r ∉ ef.gClob → s'.regs.get64 r = s0.regs.get64 r) ∧
  (∀ vr, vr ∉ ef.vClob → s'.zmms.get512 vr = s0.zmms.get512 vr) ∧
  x64Arch.FlagsAgree s0.status s'.status ef.fClob ∧
  (ef.writesMem = false → s'.dmem = s0.dmem)

private theorem effPres_refl (ef : NativeEffect Reg64 RegMm) (s0 : MachineData) :
    EffPres ef s0 s0 :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl⟩

private theorem op_p_eff [Labels] [AddressSize] {w : _root_.Width} (op : Operation w)
    (p : Std.Rco Int64) (s0 : MachineData) (next : MachineData → Effects)
    (jmp : Int64 → MachineData → Effects) (Q : MachineState → Prop)
    (hn : ∀ s', EffPres (x64OpNativeEffect op) s0 s' → EffectsPreserves Q (next s'))
    (hj : ∀ a s', EffPres (x64OpNativeEffect op) s0 s' → EffectsPreserves Q (jmp a s')) :
    EffectsPreserves Q (op.interp p s0 next jmp) := by
  have fbn : ∀ s', s'.zmms = s0.zmms → (x64OpNativeEffect op).gClob = x64AllGprs →
      (x64OpNativeEffect op).fClob = maskAll →
      (x64OpNativeEffect op).writesMem = true → EffectsPreserves Q (next s') := fun _ hz hg hf hm =>
    hn _ ⟨fun r hr => absurd (mem_x64AllGprs r) (hg ▸ hr), fun _ _ => by simp [hz],
      hf ▸ x64_flagsAgree_maskAll _ _, fun h => by cases hm ▸ h⟩
  have fbj : ∀ a s', s'.zmms = s0.zmms → (x64OpNativeEffect op).gClob = x64AllGprs →
      (x64OpNativeEffect op).fClob = maskAll → (x64OpNativeEffect op).writesMem = true →
      EffectsPreserves Q (jmp a s') := fun _ _ hzm hg hf hm => hj _ _
    ⟨fun r hr => absurd (mem_x64AllGprs r) (hg ▸ hr), fun _ _ => by simp [hzm],
     hf ▸ x64_flagsAgree_maskAll _ _, fun h => by cases hm ▸ h⟩
  cases op with
  | nop _ | nopalign _ _ => exact hn _ (effPres_refl _ _)
  | lea dst _ =>
    refine hn _ ⟨fun r hr => reg64s_get64_set_ne s0.regs dst _ r
      fun e => hr (e ▸ List.mem_cons_self), fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl⟩
  | mov d _ =>
    cases d with
    | reg dst =>
      dsimp only [Operation.interp]; apply opnd_p; intro _
      refine hn _ ⟨fun r hr => reg64s_get64_set_ne s0.regs dst _ r
        fun e => hr (e ▸ List.mem_cons_self), fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl⟩
    | mem _ =>
      exact op_p_zmms _ p s0 next jmp Q (fun _ h => fbn _ h rfl rfl rfl)
        (fun _ _ h => fbj _ _ h rfl rfl rfl)
  | jcc _ _ =>
    dsimp only [Operation.interp]; split
    · exact hj _ _ (effPres_refl _ _)
    · exact hn _ (effPres_refl _ _)
  | jmp _ =>
    dsimp only [Operation.interp]; apply rrm_p; intro _; exact hj _ _ (effPres_refl _ _)
  | _ =>
    exact op_p_zmms _ p s0 next jmp Q (fun _ h => fbn _ h rfl rfl rfl)
      (fun _ _ h => fbj _ _ h rfl rfl rfl)

private theorem dir_p_eff [Labels] (d : _root_.Directive) (p : Std.Rco Int64) (s0 : MachineData)
    (next : MachineData → Effects) (jmp : Int64 → MachineData → Effects) (Q : MachineState → Prop)
    (hn : ∀ s', EffPres (x64NativeEffect d) s0 s' → EffectsPreserves Q (next s'))
    (hj : ∀ a s', EffPres (x64NativeEffect d) s0 s' → EffectsPreserves Q (jmp a s')) :
    EffectsPreserves Q (d.interp s0 p next jmp) := by
  cases d with
  | label _ => exact hn _ (effPres_refl _ _)
  | byteArray _ =>
    dsimp only [Directive.interp]; split; exact hn _ (effPres_refl _ _); exact trivial
  | word bytes _ =>
    dsimp only [Directive.interp]; cases bytes; exact hn _ (effPres_refl _ _); exact trivial
  | instr i =>
    cases i with
    | regular asz _ op =>
      letI : AddressSize := ⟨asz⟩
      exact op_p_eff op p s0 next jmp Q (fun _ h => hn _ h) (fun _ _ h => hj _ _ h)
    | avx asz _ aop =>
      letI : AddressSize := ⟨asz⟩
      exact avxOp_p_eff aop p s0 next Q fun _ hr hv hs hm =>
        hn _ ⟨hr, hv, (fun _ _ => by simp [hs]), hm⟩

/-- Proof that `x64Arch.nativeStep` respects `x64Arch.nativeEffect`. -/
theorem x64Arch_nativeEffectSound : x64Arch.NativeEffectSound := by
  intro d symAddr s out hstep
  dsimp only [x64Arch, x64NativeStep] at hstep
  obtain ⟨sk0, p, hrg, hvr0, hfl, hmem, hbody⟩ := hstep
  letI : Labels := { label := fun l => Int64.ofBitVec (symAddr l) }
  let Q : MachineState → Prop := fun st => EffPres (x64NativeEffect d) sk0 st.data
  have finish {st : MachineState} (hq : Q st) :
      (∀ r, r ∉ (x64NativeEffect d).gClob → (krakenToMachData st.data).gpr r = s.gpr r) ∧
      (∀ vr, vr ∉ (x64NativeEffect d).vClob → (krakenToMachData st.data).vreg vr = s.vreg vr) ∧
      x64Arch.FlagsAgree s.flags (krakenToMachData st.data).flags (x64NativeEffect d).fClob ∧
      ((x64NativeEffect d).writesMem = false → (krakenToMachData st.data).mem = s.mem) :=
    ⟨fun r hr => (hq.1 r hr).trans (hrg r), fun vr hvr => (hq.2.1 vr hvr).trans (hvr0 vr),
     fun cc hc => (hq.2.2.1 cc hc).trans (hfl cc), fun hm => (hq.2.2.2 hm).trans hmem⟩
  cases out with
  | fall _ =>
    obtain ⟨_, hr, rfl⟩ := hbody
    have hp := dir_p_eff d p sk0 (fun s1 => .done ⟨s1, 0⟩) (fun _ _ => .unimplemented "jmp") Q
      (fun _ h => h) (fun _ _ _ => trivial)
    exact finish (EffectsPreserves.reaches_sound hp hr)
  | jump _ _ =>
    obtain ⟨_, hr, rfl⟩ := hbody
    have hp := dir_p_eff d p sk0 (fun _ => .unimplemented "fall") (fun a s1 => .done ⟨s1, a⟩) Q
      (fun _ _ => trivial) (fun _ _ h => h)
    exact finish (EffectsPreserves.reaches_sound hp hr)
  | halt _ _ => exact hbody.elim

end LeanQbe.T.Amd64
