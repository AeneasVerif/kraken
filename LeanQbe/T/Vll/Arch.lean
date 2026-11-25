module

public import LeanQbe.T.Target

/-!
# Target-Neutral Machine Architecture Description (`Vll.Arch`)

Defines the architecture abstraction `Arch` for `BedrockMach` L1 VLLIR, shared across x86-64,
AArch64, and concrete test machines with zero `Kraken.X64`, `Kraken.AArch64`, `Amd64`, `Arm64`,
or `*Lemmas*` imports:

* Core scalar types: `Width`, `CoreAlu`, `LoadExt`, `PadKind`, `RaKind`.
* Polymorphic machine data `MachData Reg VReg Flags`, escape-hatch outcome `NativeOutcome`,
  and opaque effect summary `NativeEffect`.
* `Abi` capturing calling-convention registers (`callerSaved`, `calleeSaved`, `allocatable`,
  `scratch`, `argRegs`, `retRegs`, `sp`, `raKind`, vector banks, stack/PC alignment, frame
  sizing, and flag clobbers).
* `Arch` abstracting `Reg`, `VReg`, `Cond`, `Flags`, `Native`, `abi`, `writeSub`, `evalCond`,
  flag update callbacks, and the `.native` escape-hatch relation `nativeStep`.
* `Arch.Wf` (`arch_wf`) bundling register disjointness, stack/frame alignment, sub-word write
  soundness, condition negation, and flag-framing invariants.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Vll

open LeanQbe.T

/-! ## 1. Scalar Widths, Core ALU Ops, Load Extensions, Landing Pads, Return Convention -/

/-- Architectural scalar operand width (`8`, `16`, `32`, or `64` bits). -/
inductive Width where
  | w8 | w16 | w32 | w64
  deriving DecidableEq, Repr, Inhabited, Hashable

/-- Bit width of a `Width`. -/
@[expose, reducible] def Width.bits : Width → Nat
  | .w8 => 8
  | .w16 => 16
  | .w32 => 32
  | .w64 => 64

/-- Byte size of a `Width`. -/
@[expose, reducible] def Width.bytes : Width → Nat
  | .w8 => 1
  | .w16 => 2
  | .w32 => 4
  | .w64 => 8

/-- Corresponding `LeanQbe.T.Ty` bitvector type for `w`. -/
@[expose, reducible] def Width.toTy (w : Width) : Ty :=
  .bits w.bits

/-- Convert a bit count (`8`, `16`, `32`, `64`) to a `Width`. -/
@[expose] def Width.ofBits? : Nat → Option Width
  | 8 => some .w8
  | 16 => some .w16
  | 32 => some .w32
  | 64 => some .w64
  | _ => none

/-- Low-bit mask in 64 bits covering `w.bits`. -/
@[expose] def Width.mask64 : Width → BitVec 64
  | .w8 => 0x00000000000000FF#64
  | .w16 => 0x000000000000FFFF#64
  | .w32 => 0x00000000FFFFFFFF#64
  | .w64 => 0xFFFFFFFFFFFFFFFF#64

theorem Width.bits_le_64 (w : Width) : w.bits ≤ 64 := by
  cases w <;> decide

theorem Width.bits_pos (w : Width) : 0 < w.bits := by
  cases w <;> decide

theorem Width.toTy_bytes (w : Width) : w.toTy.bytes = w.bytes := by
  cases w <;> rfl

theorem Width.bits_eq_8_mul_bytes (w : Width) : w.bits = 8 * w.bytes := by
  cases w <;> rfl

theorem Width.ofBits?_bits (w : Width) : Width.ofBits? w.bits = some w := by
  cases w <;> rfl

/-- Target-neutral core integer ALU opcodes shared across x86-64 and AArch64. -/
inductive CoreAlu where
  | add | sub | and | or | xor | shl | lshr | ashr | mul
  deriving DecidableEq, Repr, Inhabited, Hashable

/-- Exact bitvector semantics of `CoreAlu` at width `w` (shift counts masked mod `w.bits`). -/
@[expose] def CoreAlu.eval (op : CoreAlu) (w : Width) (a b : BitVec w.bits) : BitVec w.bits :=
  match op with
  | .add  => a + b
  | .sub  => a - b
  | .and  => a &&& b
  | .or   => a ||| b
  | .xor  => a ^^^ b
  | .shl  => a <<< (b.toNat % w.bits)
  | .lshr => a >>> (b.toNat % w.bits)
  | .ashr => a.sshiftRight (b.toNat % w.bits)
  | .mul  => a * b

/-- Extension policy when writing a loaded sub-word into a 64-bit destination register. -/
inductive LoadExt where
  /-- Zero-extend low `w.bits` bits to 64 bits. -/
  | zx
  /-- Sign-extend low `w.bits` bits to 64 bits. -/
  | sx
  /-- Apply architectural partial-register write (`A.writeSub`). -/
  | sub
  deriving DecidableEq, Repr, Inhabited, Hashable

/-- Hardware indirect-branch landing pad kind (`endbr64` on x86-64; `bti` on AArch64). -/
inductive PadKind where
  | endbr
  | btiC
  | btiJ
  | btiJC
  deriving DecidableEq, Repr, Inhabited, Hashable

/-- Hardware return-address calling convention. -/
inductive RaKind (Reg : Type) : Type where
  /-- Stack-pushed return address at `[sp]` (e.g. x86-64: `raBytes = 8`, `raRegs = []`). -/
  | stack
  /-- Link-register return address held in `lr` and spilled by prologue/epilogue at
  `[sp + 8 * ns]` (e.g. AArch64: `raBytes = 0`, `raRegs = [lr]`). -/
  | linkReg (lr : Reg)
  deriving DecidableEq, Repr

/-- Number of stack bytes pushed by hardware `call` (`8` for `.stack`, `0` for `.linkReg`). -/
@[expose, reducible] def RaKind.raBytes {Reg : Type} : RaKind Reg → Nat
  | .stack => 8
  | .linkReg _ => 0

/-- Link registers clobbered by hardware `call` (`[]` for `.stack`, `[lr]` for `.linkReg lr`). -/
@[expose, reducible] def RaKind.raRegs {Reg : Type} : RaKind Reg → List Reg
  | .stack => []
  | .linkReg lr => [lr]

/-! ## 2. Standard Sub-Word Register Write Policies -/

/-- Zero-extending sub-word write policy (used by AArch64 and simple RISC architectures). -/
@[expose] def writeSubZeroExtend (w : Width) (_old : BitVec 64) (v : BitVec w.bits) : BitVec 64 :=
  v.setWidth 64

/-- x86-64 sub-word write policy: `w8`/`w16` merge low bits into `old`, while `w32`/`w64`
zero-extend to 64 bits. -/
@[expose] def writeSubX64 (w : Width) (old : BitVec 64) (v : BitVec w.bits) : BitVec 64 :=
  match w with
  | .w8  => (old &&& ~~~0xFF#64) ||| v.setWidth 64
  | .w16 => (old &&& ~~~0xFFFF#64) ||| v.setWidth 64
  | .w32 => v.setWidth 64
  | .w64 => v

theorem writeSubZeroExtend_setWidth (w : Width) (old : BitVec 64) (v : BitVec w.bits) :
    (writeSubZeroExtend w old v).setWidth w.bits = v := by
  dsimp only [writeSubZeroExtend]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have h64 : i < 64 := Nat.lt_of_lt_of_le hi w.bits_le_64
  simp [hi, h64]

theorem writeSubZeroExtend_w64 (old v : BitVec 64) :
    writeSubZeroExtend .w64 old v = v := by
  simp [writeSubZeroExtend]

private theorem not_mask_getElem_false {k i : Nat} (hk : k ≤ 64) (hi : i < k) :
    (~~~BitVec.ofNat 64 (2 ^ k - 1))[i]'(Nat.lt_of_lt_of_le hi hk) = false := by
  rw [BitVec.getElem_not, BitVec.getElem_eq_testBit_toNat, BitVec.toNat_ofNat]
  have hlt : 2 ^ k - 1 < 2 ^ 64 :=
    Nat.lt_of_lt_of_le (Nat.sub_lt (Nat.two_pow_pos k) (by decide))
      (Nat.pow_le_pow_right (by decide) hk)
  rw [Nat.mod_eq_of_lt hlt, Nat.testBit_two_pow_sub_one, decide_eq_true hi]
  rfl

theorem writeSubX64_setWidth (w : Width) (old : BitVec 64) (v : BitVec w.bits) :
    (writeSubX64 w old v).setWidth w.bits = v := by
  cases w <;> dsimp only [writeSubX64]
  · apply BitVec.eq_of_getElem_eq
    intro i hi
    dsimp only [Width.bits] at hi
    have h64 : i < 64 := by omega
    have hnot : (~~~0xFF#64 : BitVec 64).getLsbD i = false := by
      rw [BitVec.getLsbD_eq_getElem h64]
      exact not_mask_getElem_false (k := 8) (by decide) hi
    rw [BitVec.getElem_setWidth, BitVec.getLsbD_or, BitVec.getLsbD_and, hnot]
    simp [hi, h64]
  · apply BitVec.eq_of_getElem_eq
    intro i hi
    dsimp only [Width.bits] at hi
    have h64 : i < 64 := by omega
    have hnot : (~~~0xFFFF#64 : BitVec 64).getLsbD i = false := by
      rw [BitVec.getLsbD_eq_getElem h64]
      exact not_mask_getElem_false (k := 16) (by decide) hi
    rw [BitVec.getElem_setWidth, BitVec.getLsbD_or, BitVec.getLsbD_and, hnot]
    simp [hi, h64]
  · apply BitVec.eq_of_getElem_eq
    intro i hi
    dsimp only [Width.bits] at hi
    have h64 : i < 64 := by omega
    simp [BitVec.getElem_setWidth, hi, h64]
  · exact BitVec.setWidth_eq v

theorem writeSubX64_w64 (old v : BitVec 64) :
    writeSubX64 .w64 old v = v := rfl

/-! ## 3. Machine State Data & `.native` Escape-Hatch Interface -/

/-- Architectural register, vector, flag, and memory state (excluding `pc`). -/
structure MachData (Reg VReg Flags : Type) : Type where
  gpr : Reg → BitVec 64
  vreg : VReg → BitVec 512
  flags : Flags
  mem : Mem 64

/-- Outcome of executing a `.native` escape-hatch directive. -/
inductive NativeOutcome (Reg VReg Flags : Type) : Type where
  /-- Fall through to the next instruction with updated state. -/
  | fall (s' : MachData Reg VReg Flags)
  /-- Transfer control to an explicit 64-bit code address. -/
  | jump (pc' : BitVec 64) (s' : MachData Reg VReg Flags)
  /-- Halt execution with an exit code word and final state. -/
  | halt (code : BitVec 64) (s' : MachData Reg VReg Flags)

/-- Static read/write/clobber summary for opaque `.native` directives (used by future machine
passes such as shared epilogue, LDP/STP pairing, and `jcc` peepholes). -/
structure NativeEffect (Reg VReg : Type) : Type where
  gUses : List Reg := []
  gClob : List Reg := []
  vUses : List VReg := []
  vClob : List VReg := []
  fClob : FlagMask := FlagMask.all
  readsMem : Bool := true
  writesMem : Bool := true
  isControl : Bool := false
  deriving DecidableEq, Repr

/-! ## 4. Target ABI Record -/

/-- Calling-convention and layout specification for an `Arch`. -/
structure Abi (Reg VReg : Type) : Type where
  /-- Architectural stack pointer register (`rsp` / `sp`). -/
  sp : Reg
  /-- Return-address convention (`.stack` for x86-64, `.linkReg .X30` for AArch64). -/
  raKind : RaKind Reg
  /-- Caller-saved scratch GPRs reserved for lowering (`r10, r11` / `x16, x17`). -/
  scratch : List Reg
  /-- Caller-saved allocatable GPRs (disjoint from `sp`, `scratch`, `calleeSaved`, `raRegs`). -/
  allocatable : List Reg
  /-- Full caller-saved GPR set (superset of `allocatable`). -/
  callerSaved : List Reg
  /-- Callee-saved GPRs preserved across calls. -/
  calleeSaved : List Reg
  /-- Argument passing GPRs in ABI order. -/
  argRegs : List Reg
  /-- Return value GPRs in ABI order. -/
  retRegs : List Reg
  /-- Vector scratch, allocatable, argument, and return banks. -/
  vecScratch : List VReg := []
  vecAllocatable : List VReg := []
  vecArgRegs : List VReg := []
  vecRetRegs : List VReg := []
  /-- Supported scalar integer bit widths (`[8, 16, 32, 64]`). -/
  bitWidths : List Nat := [8, 16, 32, 64]
  /-- Required stack alignment in bytes (e.g. `16`). -/
  stackAlign : Nat := 16
  /-- Instruction/PC alignment stride in bytes (e.g. `1` on x86-64, `4` on AArch64). -/
  pcAlign : Nat := 1
  /-- Human-readable architectural PC register name (e.g. `"rip"` / `"pc"`). -/
  pcName : String := "pc"
  /-- Frame byte size allocated by `prologue ns` for `ns` 8-byte slots. -/
  frameSize : Nat → Nat
  /-- Stack-pointer entry invariant (e.g. `(sp + 8) % 16 = 0` on x64, `sp % 16 = 0` on Arm64). -/
  spEntry : BitVec 64 → Prop
  /-- Stack-pointer body invariant after `prologue ns`. -/
  spOk : BitVec 64 → Prop
  /-- Flag clobber mask of `prologue ns` (`FlagMask.all` on x64, `FlagMask.none` on Arm64). -/
  prologueClob : FlagMask := FlagMask.all
  /-- Flag clobber mask of `epilogue ns` (`FlagMask.all` on x64, `FlagMask.none` on Arm64). -/
  epilogueClob : FlagMask := FlagMask.all
  /-- Flag clobber mask of `canonAbi t r` (`FlagMask.none` on both x64 and Arm64). -/
  canonAbiClob : Ty → FlagMask := fun _ => FlagMask.none
  /-- Whether 0-slot leaf functions may omit prologue/epilogue completely. -/
  leafZeroFrame : Bool := true

/-- Return-address stack byte count derived from `abi.raKind`. -/
@[expose, reducible] def Abi.raBytes {Reg VReg : Type} (abi : Abi Reg VReg) : Nat :=
  abi.raKind.raBytes

/-- Link registers derived from `abi.raKind`. -/
@[expose, reducible] def Abi.raRegs {Reg VReg : Type} (abi : Abi Reg VReg) : List Reg :=
  abi.raKind.raRegs

/-! ## 5. Architecture Description `Arch` and Well-Formedness `Arch.Wf` -/

/-- Target-neutral architecture description for `BedrockMach` L1 VLLIR.
Each concrete backend (`x64Arch`, `arm64Arch`, or a toy machine) supplies its register/condition/
flag/native types, ABI, sub-word write policy, condition evaluator, flag updates, and the
`.native` escape-hatch step relation `nativeStep`. -/
structure Arch : Type 1 where
  Reg : Type
  VReg : Type
  Cond : Type
  Flags : Type
  Native : Type
  [decEqReg : DecidableEq Reg]
  [decEqVReg : DecidableEq VReg]
  [decEqCond : DecidableEq Cond]
  /-- Calling convention, register banks, alignment, and frame sizing. -/
  abi : Abi Reg VReg
  /-- Sub-word register write policy (`writeSubX64` / `writeSubZeroExtend`). -/
  writeSub : (w : Width) → BitVec 64 → BitVec w.bits → BitVec 64
  /-- Status flags read by each condition code. -/
  condReads : Cond → FlagMask
  /-- Logical negation of a condition code. -/
  negCond : Cond → Cond
  /-- Evaluate a condition code against architectural status flags. -/
  evalCond : Flags → Cond → Bool
  /-- Conditions guaranteed to evaluate to `false` after `clearFlags`. -/
  zeroFlags : List Cond
  /-- Flag state produced by `clearFlags`. -/
  clearFlagsVal : Flags
  /-- Flag clobber mask for `alu op w _ _ _ setFlags`. -/
  aluClob : CoreAlu → Bool → FlagMask := fun _ sf => if sf then FlagMask.all else FlagMask.none
  /-- Flag state update for `alu op w _ _ _ setFlags`. -/
  aluFlags : CoreAlu → (w : Width) → Bool → BitVec w.bits → BitVec w.bits → Flags → Flags :=
    fun _ _ _ _ _ f => f
  /-- Flag clobber mask for `cmp`. -/
  cmpClob : FlagMask := FlagMask.all
  /-- Flag state update for `cmp w lhs rhs`. -/
  cmpFlags : (w : Width) → BitVec w.bits → BitVec w.bits → Flags → Flags
  /-- Flag clobber mask for `test`. -/
  testClob : FlagMask := FlagMask.all
  /-- Flag state update for `test w lhs rhs`. -/
  testFlags : (w : Width) → BitVec w.bits → BitVec w.bits → Flags → Flags
  /-- Flag clobber mask for `jnzGpr` (`FlagMask.all` on x64 `testb`, `FlagMask.none` on Arm64). -/
  jnzGprClob : FlagMask := FlagMask.none
  /-- Flag state update for `jnzGpr`. -/
  jnzGprFlags : BitVec 64 → Flags → Flags := fun _ f => f
  /-- Flag state update for `prologue ns`. -/
  prologueFlags : Nat → Flags → Flags := fun _ f => f
  /-- Flag state update for `epilogue ns`. -/
  epilogueFlags : Nat → Flags → Flags := fun _ f => f
  /-- Flag state update for `canonAbi t r`. -/
  canonAbiFlags : Ty → Flags → Flags := fun _ f => f
  /-- Relational operational semantics of `.native d` escape-hatch directives, parameterized by
  the symbol-to-address environment `symAddr`. -/
  nativeStep : Native → (Sym → BitVec 64) → MachData Reg VReg Flags →
    NativeOutcome Reg VReg Flags → Prop
  /-- Conservative static effect summary of `.native d`. -/
  nativeEffect : Native → NativeEffect Reg VReg := fun _ => {}
  /-- Whether `load (.bits 32)` with `.sub` zeroes bits `32..63`. -/
  zeroUpper32Write : Bool := true

attribute [instance] Arch.decEqReg Arch.decEqVReg Arch.decEqCond

/-- Apply a `LoadExt` extension policy under architecture `A`. -/
@[expose] def LoadExt.apply (A : Arch) (ext : LoadExt) (w : Width) (old : BitVec 64)
    (v : BitVec w.bits) : BitVec 64 :=
  match ext with
  | .zx  => v.setWidth 64
  | .sx  => v.signExtend 64
  | .sub => A.writeSub w old v

/-- Flag-agreement predicate between `f` and `f'` outside clobber mask `clob`. -/
@[expose] def Arch.FlagsAgree (A : Arch) (f f' : A.Flags) (clob : FlagMask) : Prop :=
  ∀ c, FlagMask.disjoint (A.condReads c) clob = true → A.evalCond f' c = A.evalCond f c

/-- Well-formedness invariants (`arch_wf`) required of every valid `Arch` instance. -/
structure Arch.Wf (A : Arch) : Prop where
  sp_disj :
    A.abi.sp ∉ A.abi.scratch ∧ A.abi.sp ∉ A.abi.allocatable ∧ A.abi.sp ∉ A.abi.calleeSaved ∧
    A.abi.sp ∉ A.abi.argRegs ∧ A.abi.sp ∉ A.abi.retRegs ∧ A.abi.sp ∉ A.abi.raRegs
  scratch_disj : ∀ r ∈ A.abi.scratch,
    r ∉ A.abi.allocatable ∧ r ∉ A.abi.calleeSaved ∧ r ∉ A.abi.argRegs ∧ r ∉ A.abi.retRegs
  cs_disj : ∀ r ∈ A.abi.calleeSaved,
    r ∉ A.abi.allocatable ∧ r ∉ A.abi.argRegs ∧ r ∉ A.abi.retRegs
  ra_disj : ∀ r ∈ A.abi.raRegs,
    r ∉ A.abi.allocatable ∧ r ∉ A.abi.scratch ∧ r ∉ A.abi.calleeSaved ∧
    r ∉ A.abi.argRegs ∧ r ∉ A.abi.retRegs
  argRegs_nodup : A.abi.argRegs.Nodup
  retRegs_nodup : A.abi.retRegs.Nodup
  callerSaved_sub : ∀ r ∈ A.abi.allocatable, r ∈ A.abi.callerSaved
  align_pos : 0 < A.abi.stackAlign ∧ 0 < A.abi.pcAlign
  slots_le_frameSize : ∀ ns, 8 * ns ≤ A.abi.frameSize ns
  linkReg_frameSize : ∀ lr, A.abi.raKind = .linkReg lr → ∀ ns, 8 * ns + 8 ≤ A.abi.frameSize ns
  spOk_frame : ∀ sp ns, A.abi.spEntry sp →
    A.abi.spOk (sp - BitVec.ofNat 64 (A.abi.frameSize ns))
  spEntry_call : ∀ sp ns, A.abi.spEntry sp →
    A.abi.spEntry
      (sp - BitVec.ofNat 64 (A.abi.frameSize ns) - BitVec.ofNat 64 A.abi.raBytes)
  writeSub_setWidth : ∀ (w : Width) (old : BitVec 64) (v : BitVec w.bits),
    (A.writeSub w old v).setWidth w.bits = v
  writeSub_w64 : ∀ (old v : BitVec 64), A.writeSub .w64 old v = v
  negCond_reads : ∀ c, A.condReads (A.negCond c) = A.condReads c
  negCond_eval : ∀ f c, A.evalCond f (A.negCond c) = !A.evalCond f c
  clearFlags_zero : ∀ c ∈ A.zeroFlags, A.evalCond A.clearFlagsVal c = false
  aluFlags_frame : ∀ op w sf a b f, A.FlagsAgree f (A.aluFlags op w sf a b f) (A.aluClob op sf)
  cmpFlags_frame : ∀ w a b f, A.FlagsAgree f (A.cmpFlags w a b f) A.cmpClob
  testFlags_frame : ∀ w a b f, A.FlagsAgree f (A.testFlags w a b f) A.testClob
  jnzGprFlags_frame : ∀ v f, A.FlagsAgree f (A.jnzGprFlags v f) A.jnzGprClob
  prologueFlags_frame : ∀ ns f, A.FlagsAgree f (A.prologueFlags ns f) A.abi.prologueClob
  epilogueFlags_frame : ∀ ns f, A.FlagsAgree f (A.epilogueFlags ns f) A.abi.epilogueClob
  canonAbiFlags_frame : ∀ t f, A.FlagsAgree f (A.canonAbiFlags t f) (A.abi.canonAbiClob t)

/-- Alias for `Arch.Wf`. -/
abbrev arch_wf (A : Arch) : Prop := A.Wf

/-- Optional soundness predicate asserting that `A.nativeStep` respects `A.nativeEffect`'s
register/vector/flag/memory frame summary (used by future VLLIR machine passes). -/
@[expose] def Arch.NativeEffectSound (A : Arch) : Prop :=
  ∀ d symAddr s out, A.nativeStep d symAddr s out →
    let eff := A.nativeEffect d
    let s' := match out with | .fall s' => s' | .jump _ s' => s' | .halt _ s' => s'
    (∀ r, r ∉ eff.gClob → s'.gpr r = s.gpr r) ∧
    (∀ vr, vr ∉ eff.vClob → s'.vreg vr = s.vreg vr) ∧
    A.FlagsAgree s.flags s'.flags eff.fClob ∧
    (eff.writesMem = false → s'.mem = s.mem)

/-! ## 6. Basic `LoadExt` and `Arch.Wf` Lemmas -/

theorem LoadExt.apply_setWidth {A : Arch} (hwf : A.Wf) (ext : LoadExt) (w : Width)
    (old : BitVec 64) (v : BitVec w.bits) :
    (ext.apply A w old v).setWidth w.bits = v := by
  cases ext with
  | zx =>
    dsimp only [LoadExt.apply]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have h64 : i < 64 := Nat.lt_of_lt_of_le hi w.bits_le_64
    simp [hi, h64]
  | sx =>
    dsimp only [LoadExt.apply]
    apply BitVec.eq_of_getElem_eq
    intro i hi
    have h64 : i < 64 := Nat.lt_of_lt_of_le hi w.bits_le_64
    simp [BitVec.getElem_setWidth, BitVec.getElem_signExtend, hi, h64]
  | sub =>
    exact hwf.writeSub_setWidth w old v

theorem LoadExt.apply_gprHolds {A : Arch} (hwf : A.Wf) (ext : LoadExt) (w : Width)
    (old : BitVec 64) (v : BitVec w.bits) :
    GprHolds (ext.apply A w old v) w.toTy v := by
  cases w with
  | w8 | w16 | w32 | w64 =>
    exact ⟨by decide, ext.apply_setWidth hwf _ old v⟩

theorem LoadExt.apply_zx_abiGprHolds (A : Arch) (w : Width) (old : BitVec 64) (v : BitVec w.bits) :
    AbiGprHolds (LoadExt.zx.apply A w old v) w.toTy v := by
  cases w <;> exact ⟨by decide, rfl⟩

theorem Arch.Wf.writeSub_gprHolds {A : Arch} (hwf : A.Wf) (w : Width) (old : BitVec 64)
    (v : BitVec w.bits) :
    GprHolds (A.writeSub w old v) w.toTy v :=
  LoadExt.apply_gprHolds hwf .sub w old v

theorem Arch.FlagsAgree.refl (A : Arch) (f : A.Flags) (clob : FlagMask) :
    A.FlagsAgree f f clob :=
  fun _ _ => rfl

end LeanQbe.T.Vll
