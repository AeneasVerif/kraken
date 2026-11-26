module

public import LeanQbe.T.Target
public import LeanQbe.T.Wf
public import LeanQbe.T.Rega
public import LeanQbe.T.LegalBase
public import LeanQbe.T.Vll.Arch
public import LeanQbe.T.Vll.Syntax
public import LeanQbe.T.Vll.Sem
public import LeanQbe.T.Vll.RegaInst0
import LeanQbe.T.AbiLemmas
import LeanQbe.T.RegaLemmas
import LeanQbe.T.TargetLemmas

/-!
# Target-Neutral `Rega` Backend Instantiation on `BedrockMach` L1 (`Vll.RegaInst`)

Instantiates `LeanQbe.T.GprIsa`, `LeanQbe.T.FrameIsa`, `LeanQbe.T.Isa`, `LeanQbe.T.LegalTarget`,
and `LeanQbe.T.Target` directly over `vllMach A` and `Instr A` for any well-formed `A : Arch`,
inheriting `Rega.lowerFn` and `Rega.lowerFn_correct` with zero edits to `Rega*` and zero
architecture-specific (`Amd64`, `Arm64`, `Kraken.X64`, `Kraken.AArch64`) imports:

* **Extensible native-hook policy** (`VllNativeHooks`, `VllPolicySpec`, `VllPolicy`,
  `VllPolicy.core`): separates pure data callbacks (`VllNativeHooks A : Type`, covering all 14
  core + 28 Wave-3/Gate-2 `GprIsa` hooks, optional `FrameIsa` `saveRegs?`/`restoreRegs?`,
  `VecIsa`, `Isa` hint gates, `regName`/`vregName`, `LegalTarget`) from soundness proofs
  (`VllPolicySpec A H : Prop`); `VllPolicy.core` defaults every optional hook to
  `none`/`false`/`[]` with empty vector banks.
* **Target assembly & lowering** (`vllGprIsa`, `vllGprTarget`, `vllFrameIsaWith`,
  `vllFrameTargetWith`, `vllIsa`, `vllLegalTarget`, `vllTarget`, `vllLabelClean`, `vllLowerFn`,
  `vllLowerFn_correct`): discharges every `Target` proof obligation against `vllMach_*_spec`
  and `Vll.RegaInst0` using only standard Lean axioms (`std3`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Vll

open LeanQbe.T

/-! ## 1. Empty Vector Bank, Default `LegalTarget`, & `VllNativeHooks` -/

/-- Empty `VecIsa` for any `Arch` whose `VReg` bank is uninhabited (`A.VReg → Empty`). -/
@[expose] def vllEmptyVecIsa (A : Arch) (emptyVReg : A.VReg → Empty) :
    VecIsa A.Reg A.VReg A.Cond (Instr A) where
  vecScratch := []
  vecAllocatable := []
  vecArgRegs := []
  vecRetRegs := []
  isAbiVec _ := false
  vecSlotWidth _ := none
  vmov _ v _ := (emptyVReg v).elim
  vmovi _ v _ := (emptyVReg v).elim
  vslotSt _ _ v := (emptyVReg v).elim
  vslotLd _ v _ := (emptyVReg v).elim
  vop _ _ _ _ := none
  vload _ v _ := (emptyVReg v).elim
  vstore _ v _ := (emptyVReg v).elim
  supportsVecOp _ _ := false

/-- Trivial `VecTarget` proof for `vllEmptyVecIsa`. -/
theorem vllEmptyVecTarget (A : Arch) (emptyVReg : A.VReg → Empty) :
    VecTarget (vllMach A) (vllEmptyVecIsa A emptyVReg) A.condReads
      A.abi.sp A.abi.scratch A.abi.spOk where
  vecScratch_disj _ h := nomatch h
  vecArgRegs_nodup := List.nodup_nil
  vecRetRegs_nodup := List.nodup_nil
  abiVec_slot _ h := nomatch h
  vmov_spec {_ _ _ vd} := (emptyVReg vd).elim
  vmovi_spec {_ _ _ vd} := (emptyVReg vd).elim
  vslotSt_spec {_ _ _ _ vr} := (emptyVReg vr).elim
  vslotLd_spec {_ _ _ _ vd} := (emptyVReg vd).elim
  vop_spec h := nomatch h
  vload_spec {_ _ _ vd} := (emptyVReg vd).elim
  vstore_spec {_ _ _ vs} := (emptyVReg vs).elim

/-- Default scalar-only `LegalTarget` derived from `A.abi.bitWidths`. -/
@[expose] def vllDefaultLegalTarget (A : Arch) : LegalTarget where
  oracle := .none
  allowPackBridge := false
  bitWidths := A.abi.bitWidths
  floatFmts := []
  vecIntOpSupported _ _ _ := false
  vecFloatOpSupported _ _ := false

/-- Target-specific configuration and optional `.native`-emitting callbacks for instantiating
`Rega` on `BedrockMach` L1 (`Instr A`). Every optional Wave-3/Gate-2 hook defaults to
`none`/`false`/`[]`, so `VllNativeHooks.core` lowers purely into first-class `Instr A`, while
`FactorX64`/`FactorArm64` can populate any subset of `.native` callbacks for exact byte parity. -/
structure VllNativeHooks (A : Arch) : Type where
  regName : A.Reg → String := fun _ => "<reg>"
  vregName : A.VReg → String := fun _ => "<vreg>"
  loadExt : LoadExt := .zx
  condOfCmp? : CmpOp → Option A.Cond := fun _ => none
  cmpFlags : List A.Cond := []
  clearFlags? : Option (List (Instr A)) := none
  mov? : Option (A.Reg → A.Reg → List (Instr A)) := none
  movi? : Option (A.Reg → BitVec 64 → List (Instr A)) := none
  setcc? : Option (A.Reg → A.Cond → List (Instr A)) := none
  jmp? : Option (Sym → List (Instr A)) := none
  jcc? : Option (A.Cond → Sym → List (Instr A)) := none
  jnzGpr? : Option (A.Reg → Sym → List (Instr A) × FlagMask) := none
  opHook : {sig rs : List Ty} → OpCode sig rs → Tup (PArg A.Reg A.VReg A.Cond) sig →
    Tup (PDst A.Reg A.VReg A.Cond) rs → VariantHint → Option (List (Instr A) × FlagMask) :=
    fun _ _ _ _ => none
  loadHook : Ty → A.Reg → AddrArg A.Reg → Option (List (Instr A) × FlagMask) :=
    fun _ _ _ => none
  storeHook : (t : Ty) → PArg A.Reg A.VReg A.Cond t → AddrArg A.Reg →
    Option (List (Instr A) × FlagMask) := fun _ _ _ => none
  supportsExtraScalarOp : {sig rs : List Ty} → OpCode sig rs →
    Tup (Arg (fun _ => Unit)) sig → Bool := fun _ _ => false
  supportsScalarOpOverride? : Option ({sig rs : List Ty} → OpCode sig rs →
    Tup (Arg (fun _ => Unit)) sig → Bool) := none
  zeroUpper32Load : Bool := false
  zeroExtLoad : Bool := false
  zeroUpper32Op : {sig rs : List Ty} → OpCode sig rs → Tup (PArg A.Reg A.VReg A.Cond) sig →
    Tup (PDst A.Reg A.VReg A.Cond) rs → Bool := fun _ _ _ => false
  elideZext32 : Bool := false
  testOp : (w : Nat) → (neg : Bool) → PArg A.Reg A.VReg A.Cond (.bits w) →
    PArg A.Reg A.VReg A.Cond (.bits w) → PDst A.Reg A.VReg A.Cond .bool →
    Option (List (Instr A) × FlagMask) := fun _ _ _ _ _ => none
  cmpMem : (co : CmpOp) → (w : Nat) → AddrArg A.Reg → PArg A.Reg A.VReg A.Cond (.bits w) →
    PDst A.Reg A.VReg A.Cond .bool → Option (List (Instr A) × FlagMask) := fun _ _ _ _ _ => none
  testMem : (w : Nat) → (neg : Bool) → AddrArg A.Reg → PArg A.Reg A.VReg A.Cond (.bits w) →
    PDst A.Reg A.VReg A.Cond .bool → Option (List (Instr A) × FlagMask) := fun _ _ _ _ _ => none
  loadSext : (m n : Nat) → A.Reg → AddrArg A.Reg → Option (List (Instr A) × FlagMask) :=
    fun _ _ _ _ => none
  cmpZeroJcc : (co : CmpOp) → (w : Nat) → A.Reg → Sym → Option (List (Instr A) × FlagMask) :=
    fun _ _ _ _ => none
  testJcc : (neg : Bool) → (w : Nat) → A.Reg → BitVec w → Sym →
    Option (List (Instr A) × FlagMask) := fun _ _ _ _ _ => none
  aluMem : (w : Nat) → OpCode [.bits w, .bits w] [.bits w] → (memRhs : Bool) →
    AddrArg A.Reg → PArg A.Reg A.VReg A.Cond (.bits w) → A.Reg →
    Option (List (Instr A) × FlagMask) := fun _ _ _ _ _ _ => none
  zeroUpper32AluMem : Bool := false
  jnzMem : AddrArg A.Reg → (inv : Bool) → Sym → Option (List (Instr A) × FlagMask) :=
    fun _ _ _ => none
  rmwMem : (w : Nat) → OpCode [.bits w, .bits w] [.bits w] → AddrArg A.Reg →
    PArg A.Reg A.VReg A.Cond (.bits w) → Option (List (Instr A) × FlagMask) :=
    fun _ _ _ _ => none
  leaArith : (w : Nat) → Option A.Reg → A.Reg → AddrScale → Int64 → A.Reg →
    Option (List (Instr A) × FlagMask) := fun _ _ _ _ _ _ => none
  zeroUpper32LeaArith : Bool := false
  jnzGprInv? : Option (A.Reg → Bool → Sym → List (Instr A) × FlagMask) := none
  boolFlagOut? : {sig : List Ty} → OpCode sig [.bool] → Tup (PArg A.Reg A.VReg A.Cond) sig →
    PDst A.Reg A.VReg A.Cond .bool → Option A.Cond := fun _ _ _ => none
  cmpFlagsOut? : (co : CmpOp) → (w : Nat) → PArg A.Reg A.VReg A.Cond (.bits w) →
    PArg A.Reg A.VReg A.Cond (.bits w) → PDst A.Reg A.VReg A.Cond .bool → Option Bool :=
    fun _ _ _ _ _ => none
  aluZeroOut? : {sig : List Ty} → (w : Nat) → OpCode sig [.bits w] →
    PDst A.Reg A.VReg A.Cond (.bits w) → Option Bool := fun _ _ _ => none
  hasTestFlags : Bool := false
  cmpMemFlagsOut? : CmpOp → PDst A.Reg A.VReg A.Cond .bool → Option Bool := fun _ _ => none
  loadZextIdx : Ty → A.Reg → A.Reg → A.Reg → AddrScale → Int64 →
    Option (List (Instr A) × FlagMask) := fun _ _ _ _ _ _ => none
  loadSextZextIdx : (m n : Nat) → A.Reg → A.Reg → A.Reg → AddrScale → Int64 →
    Option (List (Instr A) × FlagMask) := fun _ _ _ _ _ _ _ => none
  storeZextIdx : (t : Ty) → PArg A.Reg A.VReg A.Cond t → A.Reg → A.Reg → AddrScale → Int64 →
    Option (List (Instr A) × FlagMask) := fun _ _ _ _ _ _ => none
  leaArithZext : Option A.Reg → A.Reg → Nat → Int64 → A.Reg →
    Option (List (Instr A) × FlagMask) := fun _ _ _ _ _ => none
  moviDeadFlags? : Option (A.Reg → BitVec 64 → List (Instr A) × FlagMask) := none
  saveRegs? : Option (Nat → List A.Reg → List (Instr A)) := none
  restoreRegs? : Option (Nat → List A.Reg → List (Instr A)) := none
  supportsAddrDisp : Ty → BitVec 64 → Bool := fun _ _ => false
  supportsAddrIdx : Ty → AddrScale → BitVec 64 → Bool := fun _ _ _ => false
  supportsTestFuse : Bool := false
  supportsCmpMem : Ty → Bool := fun _ => false
  supportsTestMem : Ty → Bool := fun _ => false
  supportsAddrZextIdx : Ty → AddrScale → BitVec 64 → Bool := fun _ _ _ => false
  vec : VecIsa A.Reg A.VReg A.Cond (Instr A)
  legalTarget? : Option LegalTarget := none

/-- Default pure-core `VllNativeHooks A` with all optional hooks disabled and empty vector bank. -/
@[expose] def VllNativeHooks.core (A : Arch) (emptyVReg : A.VReg → Empty)
    (condOfCmp? : CmpOp → Option A.Cond := fun _ => none)
    (cmpFlags : List A.Cond := []) : VllNativeHooks A where
  condOfCmp? := condOfCmp?
  cmpFlags := cmpFlags
  vec := vllEmptyVecIsa A emptyVReg

/-- Construct `GprIsa` over `Instr A` from `VllNativeHooks A`. -/
@[expose] def vllGprIsaOfHooks (A : Arch) (H : VllNativeHooks A) :
    GprIsa A.Reg A.VReg A.Cond (Instr A) where
  condReads := A.condReads
  negCond := A.negCond
  zeroFlags := A.zeroFlags
  clearFlags := H.clearFlags?.getD [.clearFlags]
  mov := H.mov?.getD fun rd rs => [.mov .w64 rd rs]
  movi := H.movi?.getD fun rd c => [.movi rd c]
  setcc := H.setcc?.getD fun rd c => [.setcc rd c]
  jmp := H.jmp?.getD fun l => [.jmp l]
  jcc := H.jcc?.getD fun c l => [.jcc c l]
  jnzGpr := H.jnzGpr?.getD fun r l => ([.jnzGpr r l], A.jnzGprClob)
  op code pas dsts vh :=
    match H.opHook code pas dsts vh with
    | some res => some res
    | none => vllCoreOp A H.condOfCmp? code pas dsts vh
  load t rd a :=
    match H.loadHook t rd a with
    | some res => some res
    | none => vllCoreLoad A H.loadExt t rd a
  store t pa a :=
    match H.storeHook t pa a with
    | some res => some res
    | none => vllCoreStore A t pa a
  supportsScalarOp code args :=
    match H.supportsScalarOpOverride? with
    | some f => f code args
    | none => H.supportsExtraScalarOp code args || vllCoreSupportsScalarOp A H.condOfCmp? code args
  cmpFlags := H.cmpFlags
  zeroUpper32Load := H.zeroUpper32Load
  zeroExtLoad := H.zeroExtLoad
  zeroUpper32Op := H.zeroUpper32Op
  elideZext32 := H.elideZext32
  testOp := H.testOp
  cmpMem := H.cmpMem
  testMem := H.testMem
  loadSext := H.loadSext
  cmpZeroJcc := H.cmpZeroJcc
  testJcc := H.testJcc
  aluMem := H.aluMem
  zeroUpper32AluMem := H.zeroUpper32AluMem
  jnzMem := H.jnzMem
  rmwMem := H.rmwMem
  leaArith := H.leaArith
  zeroUpper32LeaArith := H.zeroUpper32LeaArith
  jnzGprInv? := H.jnzGprInv?
  condOfCmp? := H.condOfCmp?
  boolFlagOut? := H.boolFlagOut?
  cmpFlagsOut? := H.cmpFlagsOut?
  aluZeroOut? := H.aluZeroOut?
  hasTestFlags := H.hasTestFlags
  cmpMemFlagsOut? := H.cmpMemFlagsOut?
  loadZextIdx := H.loadZextIdx
  loadSextZextIdx := H.loadSextZextIdx
  storeZextIdx := H.storeZextIdx
  leaArithZext := H.leaArithZext
  moviDeadFlags? := H.moviDeadFlags?

/-- Extend `vllFrameIsa A` with optional bulk callee-saved save/restore overrides from `H`. -/
@[expose] def vllFrameIsaOfHooks (A : Arch) (H : VllNativeHooks A) : FrameIsa A.Reg (Instr A) :=
  { vllFrameIsa A with
    saveRegs? := H.saveRegs?
    restoreRegs? := H.restoreRegs? }

/-- Construct `Isa` over `Instr A` from `VllNativeHooks A`. -/
@[expose] def vllIsaOfHooks (A : Arch) (H : VllNativeHooks A) : Isa where
  Reg := A.Reg
  VReg := A.VReg
  Cond := A.Cond
  Directive := Instr A
  gpr := vllGprIsaOfHooks A H
  vec := H.vec
  frame := vllFrameIsaOfHooks A H
  supportsAddrDisp := H.supportsAddrDisp
  supportsAddrIdx := H.supportsAddrIdx
  supportsTestFuse := H.supportsTestFuse
  supportsCmpMem := H.supportsCmpMem
  supportsTestMem := H.supportsTestMem
  supportsAddrZextIdx := H.supportsAddrZextIdx

/-- Construct `LegalTarget` from `VllNativeHooks A`. -/
@[expose] def vllLegalTargetOfHooks (A : Arch) (H : VllNativeHooks A) : LegalTarget :=
  H.legalTarget?.getD (vllDefaultLegalTarget A)

/-! ## 2. Verified Policy Spec (`VllPolicySpec`), `VllPolicy`, `vllTarget`, & `vllLowerFn` -/

/-- Helper discharging `clearFlags_frame` whenever every condition code reads at least one flag
bit (`A.condReads c ≠ 0#8`). -/
theorem clearFlags_frame_of_nonzero {A : Arch} (h : ∀ c : A.Cond, A.condReads c ≠ 0#8) :
    ∀ (f : A.Flags) (c : A.Cond),
      FlagMask.disjoint (A.condReads c) FlagMask.all = true →
      A.evalCond A.clearFlagsVal c = A.evalCond f c := by
  intro f c hd
  have hz : A.condReads c = 0#8 := by
    simp only [FlagMask.disjoint, FlagMask.all, beq_iff_eq] at hd
    have hall : A.condReads c &&& (0xFF#8 : BitVec 8) = A.condReads c := by
      change A.condReads c &&& BitVec.allOnes 8 = A.condReads c
      exact BitVec.and_allOnes
    rwa [hall] at hd
  exact absurd hz (h c)

/-- Soundness obligations for all hooks in `H : VllNativeHooks A`. Kept in `Prop` (analogous to
`GprTarget`/`FrameSpec`) so pure data hooks stay L4-firewall separate from proof modules and
unused optional hooks discharge in 1 step via `intro h; cases h`. -/
structure VllPolicySpec (A : Arch) (H : VllNativeHooks A) : Prop where
  clearFlags_frame : ∀ (f : A.Flags) (c : A.Cond),
    FlagMask.disjoint (A.condReads c) FlagMask.all = true →
    A.evalCond A.clearFlagsVal c = A.evalCond f c
  cmpFlags_spec : ∀ co cc (w : Width) (a b : BitVec w.bits) f,
    H.condOfCmp? co = some cc → A.evalCond (A.cmpFlags w a b f) cc = co.evalBits a b
  clearFlags_override_spec : ∀ {c h k s post}, H.clearFlags? = some c →
    (vllMach A).FallsTo A.condReads h k c A.abi.scratch [] FlagMask.all s
      (fun s' => (∀ cc ∈ A.zeroFlags, (vllMach A).evalCond s' cc = false) ∧
        s'.mem = s.mem) post := by intros; contradiction
  mov_override_spec : ∀ {f h k rd rs s post}, H.mov? = some f →
    (vllMach A).FallsTo A.condReads h k (f rd rs) [rd] [] FlagMask.none s
      (fun s' => s'.gpr rd = s.gpr rs ∧ s'.mem = s.mem) post := by intros; contradiction
  movi_override_spec : ∀ {f h k rd cv s post}, H.movi? = some f →
    (vllMach A).FallsTo A.condReads h k (f rd cv) (rd :: A.abi.scratch) [] FlagMask.none s
      (fun s' => s'.gpr rd = cv ∧ s'.mem = s.mem) post := by intros; contradiction
  setcc_override_spec : ∀ {f h k rd cc s post}, H.setcc? = some f → rd ∉ A.abi.scratch →
    (vllMach A).FallsTo A.condReads h k (f rd cc) (rd :: A.abi.scratch) [] FlagMask.none s
      (fun s' => GprHolds (s'.gpr rd) .bool ((vllMach A).evalCond s cc) ∧
        s'.mem = s.mem) post := by intros; contradiction
  jmp_override_spec : ∀ {f h k j l s post}, H.jmp? = some f →
    (f l).IsInfixAt h.prog k → h.labelAddr l = h.addrOf j →
    (∀ s', (vllMach A).Frame A.condReads s s' A.abi.scratch [] FlagMask.none →
      s'.mem = s.mem → (vllMach A).Run h j s' post) →
    (vllMach A).Run h k s post := by intros; contradiction
  jcc_override_spec : ∀ {f h k j cc l s post}, H.jcc? = some f →
    (f cc l).IsInfixAt h.prog k → h.labelAddr l = h.addrOf j →
    (∀ s', (vllMach A).Frame A.condReads s s' A.abi.scratch [] FlagMask.none → s'.mem = s.mem →
      ((vllMach A).evalCond s cc = true → (vllMach A).Run h j s' post) ∧
      ((vllMach A).evalCond s cc = false → (vllMach A).Run h (k + (f cc l).length) s' post)) →
    (vllMach A).Run h k s post := by intros; contradiction
  jnzGpr_override_spec : ∀ {f h k j r l b s post}, H.jnzGpr? = some f →
    (f r l).1.IsInfixAt h.prog k → h.labelAddr l = h.addrOf j →
    r ∉ A.abi.scratch → GprHolds (s.gpr r) .bool b →
    (∀ s', (vllMach A).Frame A.condReads s s' A.abi.scratch [] (f r l).2 → s'.mem = s.mem →
      (b = true → (vllMach A).Run h j s' post) ∧
      (b = false → (vllMach A).Run h (k + (f r l).1.length) s' post)) →
    (vllMach A).Run h k s post := by intros; contradiction
  opHook_spec : ∀ {h k sig rs} {code : OpCode sig rs} {pas dsts vh c clob vs P s post},
    H.opHook code pas dsts vh = some (c, clob) →
    (∀ r ∈ tupArgGprs pas, r ∉ A.abi.scratch) → (∀ r ∈ tupDstGprs dsts, r ∉ A.abi.scratch) →
    TRel ((vllMach A).PArgHolds s) pas vs → code.wp vs P →
    (vllMach A).FallsTo A.condReads h k c (tupDstGprs dsts ++ A.abi.scratch) [] clob s
      (fun s' => (∃ rvs, P rvs ∧ TRel ((vllMach A).PDstHolds s') dsts rvs) ∧
        s'.mem = s.mem) post := by intros; contradiction
  loadHook_spec : ∀ {h k t rd a c clob v s post},
    H.loadHook t rd a = some (c, clob) → rd ∉ A.abi.scratch → (∀ r ∈ a.regs, r ∉ A.abi.scratch) →
    loadVal s.mem t (a.eval s.gpr) = some v →
    (vllMach A).FallsTo A.condReads h k c (rd :: A.abi.scratch) [] clob s
      (fun s' => GprHolds (s'.gpr rd) t v ∧ s'.mem = s.mem) post := by intros; contradiction
  storeHook_spec : ∀ {h k t pa a c clob v s post},
    H.storeHook t pa a = some (c, clob) → (∀ r ∈ pa.gprs ++ a.regs, r ∉ A.abi.scratch) →
    (vllMach A).PArgHolds s t pa v → storeOk s.mem t (a.eval s.gpr) →
    (vllMach A).FallsTo A.condReads h k c A.abi.scratch [] clob s
      (fun s' => s'.mem = storeMem s.mem t (a.eval s.gpr) v) post := by intros; contradiction
  load_zero32 : H.zeroUpper32Load = true →
    ∀ {h k rd a c clob s post} {v : BitVec 32},
    (vllGprIsaOfHooks A H).load (.bits 32) rd a = some (c, clob) →
    rd ∉ A.abi.scratch → (∀ r ∈ a.regs, r ∉ A.abi.scratch) →
    loadVal s.mem (.bits 32) (a.eval s.gpr) = some v →
    (vllMach A).FallsTo A.condReads h k c (rd :: A.abi.scratch) [] clob s
      (fun s' => s'.gpr rd = v.setWidth 64 ∧ s'.mem = s.mem) post := by intros; contradiction
  load_zext : H.zeroExtLoad = true →
    ∀ {h k t rd a c clob v s post},
    (vllGprIsaOfHooks A H).load t rd a = some (c, clob) →
    rd ∉ A.abi.scratch → (∀ r ∈ a.regs, r ∉ A.abi.scratch) →
    loadVal s.mem t (a.eval s.gpr) = some v →
    (vllMach A).FallsTo A.condReads h k c (rd :: A.abi.scratch) [] clob s
      (fun s' => AbiGprHolds (s'.gpr rd) t v ∧ s'.mem = s.mem) post := by intros; contradiction
  op_zero32 : ∀ {h k sig} {code : OpCode sig [.bits 32]} {pas dsts rd vh c clob vs P s post},
    H.zeroUpper32Op code pas dsts = true →
    (vllGprIsaOfHooks A H).op code pas dsts vh = some (c, clob) →
    dsts = (.gpr rd, ()) →
    (∀ r ∈ tupArgGprs pas, r ∉ A.abi.scratch) → rd ∉ A.abi.scratch →
    TRel ((vllMach A).PArgHolds s) pas vs → code.wp vs P →
    (vllMach A).FallsTo A.condReads h k c (rd :: A.abi.scratch) [] clob s
      (fun s' => (∃ rv : BitVec 32, P (rv, ()) ∧ s'.gpr rd = rv.setWidth 64) ∧
        s'.mem = s.mem) post := by intros; contradiction
  testOp_spec : ∀ {h k w neg pa pb pd c clob va vb s post},
    H.testOp w neg pa pb pd = some (c, clob) →
    (∀ r ∈ pa.gprs ++ pb.gprs, r ∉ A.abi.scratch) → (∀ r ∈ pd.gprs, r ∉ A.abi.scratch) →
    (vllMach A).PArgHolds s (.bits w) pa va → (vllMach A).PArgHolds s (.bits w) pb vb →
    (vllMach A).FallsTo A.condReads h k c (pd.gprs ++ A.abi.scratch) [] clob s
      (fun s' =>
        (vllMach A).PDstHolds s' .bool pd
          ((if neg then CmpOp.ne else CmpOp.eq).evalBits (va &&& vb) 0#w) ∧
        s'.mem = s.mem) post := by intros; contradiction
  cmpMem_spec : ∀ {h k co w a pb pd c clob va vb s post},
    H.cmpMem co w a pb pd = some (c, clob) →
    (∀ r ∈ a.regs ++ pb.gprs, r ∉ A.abi.scratch) → (∀ r ∈ pd.gprs, r ∉ A.abi.scratch) →
    loadVal s.mem (.bits w) (a.eval s.gpr) = some va →
    (vllMach A).PArgHolds s (.bits w) pb vb →
    (vllMach A).FallsTo A.condReads h k c (pd.gprs ++ A.abi.scratch) [] clob s
      (fun s' => (vllMach A).PDstHolds s' .bool pd (co.evalBits va vb) ∧
        s'.mem = s.mem) post := by intros; contradiction
  testMem_spec : ∀ {h k w neg a pb pd c clob va vb s post},
    H.testMem w neg a pb pd = some (c, clob) →
    (∀ r ∈ a.regs ++ pb.gprs, r ∉ A.abi.scratch) → (∀ r ∈ pd.gprs, r ∉ A.abi.scratch) →
    loadVal s.mem (.bits w) (a.eval s.gpr) = some va →
    (vllMach A).PArgHolds s (.bits w) pb vb →
    (vllMach A).FallsTo A.condReads h k c (pd.gprs ++ A.abi.scratch) [] clob s
      (fun s' =>
        (vllMach A).PDstHolds s' .bool pd
          ((if neg then CmpOp.ne else CmpOp.eq).evalBits (va &&& vb) 0#w) ∧
        s'.mem = s.mem) post := by intros; contradiction
  loadSext_spec : ∀ {h k m n rd a c clob v s post},
    H.loadSext m n rd a = some (c, clob) → rd ∉ A.abi.scratch → (∀ r ∈ a.regs, r ∉ A.abi.scratch) →
    loadVal s.mem (.bits m) (a.eval s.gpr) = some v →
    (vllMach A).FallsTo A.condReads h k c (rd :: A.abi.scratch) [] clob s
      (fun s' => s'.gpr rd = v.signExtend 64 ∧ s'.mem = s.mem) post := by intros; contradiction
  cmpZeroJcc_spec : ∀ {h k j co w r l c clob} {v : BitVec w} {s post},
    H.cmpZeroJcc co w r l = some (c, clob) →
    c.IsInfixAt h.prog k → h.labelAddr l = h.addrOf j →
    r ∉ A.abi.scratch → GprHolds (s.gpr r) (.bits w) v →
    (∀ s', (vllMach A).Frame A.condReads s s' A.abi.scratch [] clob → s'.mem = s.mem →
      (co.evalBits v 0#w = true → (vllMach A).Run h j s' post) ∧
      (co.evalBits v 0#w = false → (vllMach A).Run h (k + c.length) s' post)) →
    (vllMach A).Run h k s post := by intros; contradiction
  testJcc_spec : ∀ {h k j neg w r mask l c clob} {v : BitVec w} {s post},
    H.testJcc neg w r mask l = some (c, clob) →
    c.IsInfixAt h.prog k → h.labelAddr l = h.addrOf j →
    r ∉ A.abi.scratch → GprHolds (s.gpr r) (.bits w) v →
    (∀ s', (vllMach A).Frame A.condReads s s' A.abi.scratch [] clob → s'.mem = s.mem →
      ((if neg then CmpOp.ne else CmpOp.eq).evalBits (v &&& mask) 0#w = true →
        (vllMach A).Run h j s' post) ∧
      ((if neg then CmpOp.ne else CmpOp.eq).evalBits (v &&& mask) 0#w = false →
        (vllMach A).Run h (k + c.length) s' post)) →
    (vllMach A).Run h k s post := by intros; contradiction
  aluMem_spec : ∀ {h k w memRhs} {code : OpCode [.bits w, .bits w] [.bits w]}
      {a : AddrArg A.Reg} {pb : PArg A.Reg A.VReg A.Cond (.bits w)} {rd : A.Reg}
      {c : List (Instr A)} {clob : FlagMask} {va vb : BitVec w}
      {P : Tup Val [.bits w] → Prop} {s : MachSt A} {post : Config A → Prop},
    H.aluMem w code memRhs a pb rd = some (c, clob) →
    (∀ r ∈ a.regs ++ pb.gprs, r ∉ A.abi.scratch) → rd ∉ A.abi.scratch →
    loadVal s.mem (.bits w) (a.eval s.gpr) = some va →
    (vllMach A).PArgHolds s (.bits w) pb vb →
    code.wp (if memRhs then (vb, va, ()) else (va, vb, ())) P →
    (vllMach A).FallsTo A.condReads h k c (rd :: A.abi.scratch) [] clob s
      (fun s' => (∃ rv : BitVec w, P (rv, ()) ∧ GprHolds (s'.gpr rd) (.bits w) rv) ∧
        s'.mem = s.mem) post := by intros; contradiction
  aluMem_zero32 : H.zeroUpper32AluMem = true →
    ∀ {h k memRhs} {code : OpCode [.bits 32, .bits 32] [.bits 32]}
      {a : AddrArg A.Reg} {pb : PArg A.Reg A.VReg A.Cond (.bits 32)} {rd : A.Reg}
      {c : List (Instr A)} {clob : FlagMask} {va vb : BitVec 32}
      {P : Tup Val [.bits 32] → Prop} {s : MachSt A} {post : Config A → Prop},
    H.aluMem 32 code memRhs a pb rd = some (c, clob) →
    (∀ r ∈ a.regs ++ pb.gprs, r ∉ A.abi.scratch) → rd ∉ A.abi.scratch →
    loadVal s.mem (.bits 32) (a.eval s.gpr) = some va →
    (vllMach A).PArgHolds s (.bits 32) pb vb →
    code.wp (if memRhs then (vb, va, ()) else (va, vb, ())) P →
    (vllMach A).FallsTo A.condReads h k c (rd :: A.abi.scratch) [] clob s
      (fun s' => (∃ rv : BitVec 32, P (rv, ()) ∧ s'.gpr rd = rv.setWidth 64) ∧
        s'.mem = s.mem) post := by intros; contradiction
  jnzMem_spec : ∀ {h k j a inv l c clob} {v8 : BitVec 8} {b : Bool}
      {s : MachSt A} {post : Config A → Prop},
    H.jnzMem a inv l = some (c, clob) →
    c.IsInfixAt h.prog k → h.labelAddr l = h.addrOf j →
    (∀ r ∈ a.regs, r ∉ A.abi.scratch) →
    loadVal s.mem (.bits 8) (a.eval s.gpr) = some v8 →
    v8 = BitVec.ofNat 8 b.toNat →
    (∀ s', (vllMach A).Frame A.condReads s s' A.abi.scratch [] clob → s'.mem = s.mem →
      ((if inv then !b else b) = true → (vllMach A).Run h j s' post) ∧
      ((if inv then !b else b) = false → (vllMach A).Run h (k + c.length) s' post)) →
    (vllMach A).Run h k s post := by intros; contradiction
  rmwMem_spec : ∀ {h k w} {code : OpCode [.bits w, .bits w] [.bits w]}
      {a : AddrArg A.Reg} {pb : PArg A.Reg A.VReg A.Cond (.bits w)}
      {c : List (Instr A)} {clob : FlagMask} {va vb : BitVec w}
      {P : Tup Val [.bits w] → Prop} {s : MachSt A} {post : Config A → Prop},
    H.rmwMem w code a pb = some (c, clob) →
    (∀ r ∈ a.regs ++ pb.gprs, r ∉ A.abi.scratch) →
    loadVal s.mem (.bits w) (a.eval s.gpr) = some va →
    storeOk s.mem (.bits w) (a.eval s.gpr) →
    (vllMach A).PArgHolds s (.bits w) pb vb →
    code.wp (va, vb, ()) P →
    (vllMach A).FallsTo A.condReads h k c A.abi.scratch [] clob s
      (fun s' => ∃ rv : BitVec w, P (rv, ()) ∧
        s'.mem = storeMem s.mem (.bits w) (a.eval s.gpr) rv) post := by intros; contradiction
  leaArith_spec : ∀ {h k w base? idx sc disp rd c clob vb vi s post},
    H.leaArith w base? idx sc disp rd = some (c, clob) →
    (∀ r, base? = some r → r ∉ A.abi.scratch) → idx ∉ A.abi.scratch → rd ∉ A.abi.scratch →
    (∀ r, base? = some r → GprHolds (s.gpr r) (.bits w) vb) →
    GprHolds (s.gpr idx) (.bits w) vi →
    let res : BitVec w :=
      (if base?.isSome then vb else 0#w) + (vi <<< sc.shift) + disp.toBitVec.setWidth w
    (vllMach A).FallsTo A.condReads h k c (rd :: A.abi.scratch) [] clob s
      (fun s' => GprHolds (s'.gpr rd) (.bits w) res ∧ s'.mem = s.mem) post :=
    by intros; contradiction
  leaArith_zero32 : H.zeroUpper32LeaArith = true →
    ∀ {h k base? idx sc disp rd c clob vb vi s post},
    H.leaArith 32 base? idx sc disp rd = some (c, clob) →
    (∀ r, base? = some r → r ∉ A.abi.scratch) → idx ∉ A.abi.scratch → rd ∉ A.abi.scratch →
    (∀ r, base? = some r → GprHolds (s.gpr r) (.bits 32) vb) →
    GprHolds (s.gpr idx) (.bits 32) vi →
    let res : BitVec 32 :=
      (if base?.isSome then vb else 0#32) + (vi <<< sc.shift) + disp.toBitVec.setWidth 32
    (vllMach A).FallsTo A.condReads h k c (rd :: A.abi.scratch) [] clob s
      (fun s' => s'.gpr rd = res.setWidth 64 ∧ s'.mem = s.mem) post := by intros; contradiction
  jnzGprInv_spec : ∀ {fn h k j r inv l b s post},
    H.jnzGprInv? = some fn →
    (fn r inv l).1.IsInfixAt h.prog k → h.labelAddr l = h.addrOf j →
    r ∉ A.abi.scratch → GprHolds (s.gpr r) .bool b →
    (∀ s', (vllMach A).Frame A.condReads s s' A.abi.scratch [] (fn r inv l).2 → s'.mem = s.mem →
      ((if inv then !b else b) = true → (vllMach A).Run h j s' post) ∧
      ((if inv then !b else b) = false → (vllMach A).Run h (k + (fn r inv l).1.length) s' post)) →
    (vllMach A).Run h k s post := by intros; contradiction
  op_boolFlag_spec : ∀ {h k sig} {code : OpCode sig [.bool]} {pas pd cc vh c clob vs P s post},
    H.boolFlagOut? code pas pd = some cc →
    (vllGprIsaOfHooks A H).op code pas (pd, ()) vh = some (c, clob) →
    (∀ r ∈ tupArgGprs pas, r ∉ A.abi.scratch) → (∀ r ∈ pd.gprs, r ∉ A.abi.scratch) →
    TRel ((vllMach A).PArgHolds s) pas vs → code.wp vs P →
    (vllMach A).FallsTo A.condReads h k c (pd.gprs ++ A.abi.scratch) [] clob s
      (fun s' => (∃ b : Bool, P (b, ()) ∧ (vllMach A).PDstHolds s' .bool pd b ∧
          (vllMach A).evalCond s' cc = b) ∧
        s'.mem = s.mem) post := by intros; contradiction
  op_cmpFlags_spec : ∀ {h k co w pa pb pd lhsFirst vh c clob va vb s post},
    H.cmpFlagsOut? co w pa pb pd = some lhsFirst →
    (vllGprIsaOfHooks A H).op
      (.cmp co (.bits w) .bool rfl) (pa, pb, ()) (pd, ()) vh = some (c, clob) →
    (∀ r ∈ pa.gprs ++ pb.gprs, r ∉ A.abi.scratch) → (∀ r ∈ pd.gprs, r ∉ A.abi.scratch) →
    (vllMach A).PArgHolds s (.bits w) pa va → (vllMach A).PArgHolds s (.bits w) pb vb →
    (vllMach A).FallsTo A.condReads h k c (pd.gprs ++ A.abi.scratch) [] clob s
      (fun s' => (vllMach A).PDstHolds s' .bool pd (co.evalBits va vb) ∧
        FlagCmpOk (vllMach A) (vllGprIsaOfHooks A H) s'
          (if lhsFirst then va else vb) (if lhsFirst then vb else va) false ∧
        s'.mem = s.mem) post := by intros; contradiction
  op_aluZero_spec : ∀ {h k sig w} {code : OpCode sig [.bits w]}
      {pas pd eqNe vh c clob vs P s post},
    H.aluZeroOut? w code pd = some eqNe → clob ≠ FlagMask.none →
    (vllGprIsaOfHooks A H).op code pas (pd, ()) vh = some (c, clob) →
    (∀ r ∈ tupArgGprs pas, r ∉ A.abi.scratch) → (∀ r ∈ pd.gprs, r ∉ A.abi.scratch) →
    TRel ((vllMach A).PArgHolds s) pas vs → code.wp vs P →
    (vllMach A).FallsTo A.condReads h k c (pd.gprs ++ A.abi.scratch) [] clob s
      (fun s' => (∃ rv : BitVec w, P (rv, ()) ∧ (vllMach A).PDstHolds s' (.bits w) pd rv ∧
          (∀ rd, w = 32 → pd = .gpr rd → H.zeroUpper32Op code pas (.gpr rd, ()) = true →
            s'.gpr rd = rv.setWidth 64) ∧
          FlagCmpOk (vllMach A) (vllGprIsaOfHooks A H) s' rv 0#w eqNe) ∧
        s'.mem = s.mem) post := by intros; contradiction
  testOp_boolFlag_spec : H.hasTestFlags = true →
    ∀ {h k w neg pa pb pd c clob va vb cc s post},
    clob ≠ FlagMask.none → H.condOfCmp? (if neg then .ne else .eq) = some cc →
    H.testOp w neg pa pb pd = some (c, clob) →
    (∀ r ∈ pa.gprs ++ pb.gprs, r ∉ A.abi.scratch) → (∀ r ∈ pd.gprs, r ∉ A.abi.scratch) →
    (vllMach A).PArgHolds s (.bits w) pa va → (vllMach A).PArgHolds s (.bits w) pb vb →
    (vllMach A).FallsTo A.condReads h k c (pd.gprs ++ A.abi.scratch) [] clob s
      (fun s' =>
        let res := (if neg then CmpOp.ne else CmpOp.eq).evalBits (va &&& vb) 0#w
        (vllMach A).PDstHolds s' .bool pd res ∧ (vllMach A).evalCond s' cc = res ∧
        s'.mem = s.mem) post := by intros; contradiction
  testMem_boolFlag_spec : H.hasTestFlags = true →
    ∀ {h k w neg a pb pd c clob va vb cc s post},
    clob ≠ FlagMask.none → H.condOfCmp? (if neg then .ne else .eq) = some cc →
    H.testMem w neg a pb pd = some (c, clob) →
    (∀ r ∈ a.regs ++ pb.gprs, r ∉ A.abi.scratch) → (∀ r ∈ pd.gprs, r ∉ A.abi.scratch) →
    loadVal s.mem (.bits w) (a.eval s.gpr) = some va →
    (vllMach A).PArgHolds s (.bits w) pb vb →
    (vllMach A).FallsTo A.condReads h k c (pd.gprs ++ A.abi.scratch) [] clob s
      (fun s' =>
        let res := (if neg then CmpOp.ne else CmpOp.eq).evalBits (va &&& vb) 0#w
        (vllMach A).PDstHolds s' .bool pd res ∧ (vllMach A).evalCond s' cc = res ∧
        s'.mem = s.mem) post := by intros; contradiction
  cmpMem_flags_spec : ∀ {h k co w a pb pd lhsFirst c clob va vb s post},
    H.cmpMemFlagsOut? co pd = some lhsFirst →
    H.cmpMem co w a pb pd = some (c, clob) →
    (∀ r ∈ a.regs ++ pb.gprs, r ∉ A.abi.scratch) → (∀ r ∈ pd.gprs, r ∉ A.abi.scratch) →
    loadVal s.mem (.bits w) (a.eval s.gpr) = some va →
    (vllMach A).PArgHolds s (.bits w) pb vb →
    (vllMach A).FallsTo A.condReads h k c (pd.gprs ++ A.abi.scratch) [] clob s
      (fun s' => (vllMach A).PDstHolds s' .bool pd (co.evalBits va vb) ∧
        FlagCmpOk (vllMach A) (vllGprIsaOfHooks A H) s'
          (if lhsFirst then va else vb) (if lhsFirst then vb else va) false ∧
        s'.mem = s.mem) post := by intros; contradiction
  loadZextIdx_spec : ∀ {h k t rd base idx sc disp c clob v vb vi s post},
    H.loadZextIdx t rd base idx sc disp = some (c, clob) →
    rd ∉ A.abi.scratch → base ∉ A.abi.scratch → idx ∉ A.abi.scratch →
    GprHolds (s.gpr base) (.bits 64) vb → GprHolds (s.gpr idx) (.bits 32) vi →
    loadVal s.mem t (vb + (vi.setWidth 64 <<< sc.shift) + disp.toBitVec) = some v →
    (vllMach A).FallsTo A.condReads h k c (rd :: A.abi.scratch) [] clob s
      (fun s' => GprHolds (s'.gpr rd) t v ∧ s'.mem = s.mem) post := by intros; contradiction
  loadZextIdx_zero32 : H.zeroUpper32Load = true →
    ∀ {h k rd base idx sc disp c clob} {v : BitVec 32} {vb : BitVec 64} {vi : BitVec 32}
      {s post},
    H.loadZextIdx (.bits 32) rd base idx sc disp = some (c, clob) →
    rd ∉ A.abi.scratch → base ∉ A.abi.scratch → idx ∉ A.abi.scratch →
    GprHolds (s.gpr base) (.bits 64) vb → GprHolds (s.gpr idx) (.bits 32) vi →
    loadVal s.mem (.bits 32) (vb + (vi.setWidth 64 <<< sc.shift) + disp.toBitVec) = some v →
    (vllMach A).FallsTo A.condReads h k c (rd :: A.abi.scratch) [] clob s
      (fun s' => s'.gpr rd = v.setWidth 64 ∧ s'.mem = s.mem) post := by intros; contradiction
  loadZextIdx_zext : H.zeroExtLoad = true →
    ∀ {h k t rd base idx sc disp c clob v vb vi s post},
    H.loadZextIdx t rd base idx sc disp = some (c, clob) →
    rd ∉ A.abi.scratch → base ∉ A.abi.scratch → idx ∉ A.abi.scratch →
    GprHolds (s.gpr base) (.bits 64) vb → GprHolds (s.gpr idx) (.bits 32) vi →
    loadVal s.mem t (vb + (vi.setWidth 64 <<< sc.shift) + disp.toBitVec) = some v →
    (vllMach A).FallsTo A.condReads h k c (rd :: A.abi.scratch) [] clob s
      (fun s' => AbiGprHolds (s'.gpr rd) t v ∧ s'.mem = s.mem) post := by intros; contradiction
  loadSextZextIdx_spec : ∀ {h k m n rd base idx sc disp c clob v vb vi s post},
    H.loadSextZextIdx m n rd base idx sc disp = some (c, clob) →
    rd ∉ A.abi.scratch → base ∉ A.abi.scratch → idx ∉ A.abi.scratch →
    GprHolds (s.gpr base) (.bits 64) vb → GprHolds (s.gpr idx) (.bits 32) vi →
    loadVal s.mem (.bits m) (vb + (vi.setWidth 64 <<< sc.shift) + disp.toBitVec) = some v →
    (vllMach A).FallsTo A.condReads h k c (rd :: A.abi.scratch) [] clob s
      (fun s' => s'.gpr rd = v.signExtend 64 ∧ s'.mem = s.mem) post := by intros; contradiction
  storeZextIdx_spec : ∀ {h k t pa base idx sc disp c clob v vb vi s post},
    H.storeZextIdx t pa base idx sc disp = some (c, clob) →
    (∀ r ∈ pa.gprs, r ∉ A.abi.scratch) → base ∉ A.abi.scratch → idx ∉ A.abi.scratch →
    (vllMach A).PArgHolds s t pa v →
    GprHolds (s.gpr base) (.bits 64) vb → GprHolds (s.gpr idx) (.bits 32) vi →
    storeOk s.mem t (vb + (vi.setWidth 64 <<< sc.shift) + disp.toBitVec) →
    (vllMach A).FallsTo A.condReads h k c A.abi.scratch [] clob s
      (fun s' => s'.mem =
        storeMem s.mem t (vb + (vi.setWidth 64 <<< sc.shift) + disp.toBitVec) v) post :=
    by intros; contradiction
  leaArithZext_spec : ∀ {h k base? idx shift disp rd c clob vb vi s post},
    H.leaArithZext base? idx shift disp rd = some (c, clob) →
    (∀ r, base? = some r → r ∉ A.abi.scratch) → idx ∉ A.abi.scratch → rd ∉ A.abi.scratch →
    (∀ r, base? = some r → GprHolds (s.gpr r) (.bits 64) vb) →
    GprHolds (s.gpr idx) (.bits 32) vi →
    let res : BitVec 64 :=
      (if base?.isSome then vb else 0#64) + (vi.setWidth 64 <<< shift) + disp.toBitVec
    (vllMach A).FallsTo A.condReads h k c (rd :: A.abi.scratch) [] clob s
      (fun s' => GprHolds (s'.gpr rd) (.bits 64) res ∧ s'.mem = s.mem) post :=
    by intros; contradiction
  moviDeadFlags?_spec : ∀ {fn h k rd c s post},
    H.moviDeadFlags? = some fn →
    (vllMach A).FallsTo A.condReads h k (fn rd c).1 (rd :: A.abi.scratch) [] (fn rd c).2 s
      (fun s' => s'.gpr rd = c ∧ s'.mem = s.mem) post :=
    by intros; contradiction
  saveRegs_spec : ∀ {fn h k i rs s G post},
    H.saveRegs? = some fn → 8 * i + 8 * rs.length ≤ 2 ^ 64 →
    (∀ r ∈ rs, r ∉ A.abi.scratch) → A.abi.spOk (s.gpr A.abi.sp) →
    (s.mem =⋆ region (s.gpr A.abi.sp + BitVec.ofNat 64 (8 * i)) (8 * rs.length) ⋆ G) →
    (vllMach A).FallsTo A.condReads h k (fn i rs) A.abi.scratch [] FlagMask.none s
      (fun s' => s'.mem =⋆
        array64 (s.gpr A.abi.sp + BitVec.ofNat 64 (8 * i)) (rs.map s.gpr) ⋆ G) post :=
    by intros; contradiction
  restoreRegs_spec : ∀ {fn h k i rs} {s₀ : MachSt A} {s G post},
    H.restoreRegs? = some fn →
    rs.Nodup → (∀ r ∈ rs, r ∈ A.abi.calleeSaved) → A.abi.spOk (s.gpr A.abi.sp) →
    (s.mem =⋆ array64 (s.gpr A.abi.sp + BitVec.ofNat 64 (8 * i)) (rs.map s₀.gpr) ⋆ G) →
    (vllMach A).FallsTo A.condReads h k (fn i rs) (rs ++ A.abi.scratch) [] FlagMask.none s
      (fun s' => (∀ r ∈ rs, s'.gpr r = s₀.gpr r) ∧ s'.mem = s.mem) post := by intros; contradiction
  vecSpec : VecTarget (vllMach A) H.vec A.condReads A.abi.sp A.abi.scratch A.abi.spOk

/-- Verified lowering policy bundling pure hooks `hooks` with their `VllPolicySpec` proof. -/
structure VllPolicy (A : Arch) : Type where
  hooks : VllNativeHooks A
  spec : VllPolicySpec A hooks

/-- Minimal scalar-only core policy: every optional Wave-3/Gate-2 hook defaults to
`none`/`false`/`[]`, `vec` is empty (`vllEmptyVecIsa`/`vllEmptyVecTarget`), and all lowering
emits pure first-class `Instr A` instructions. -/
@[expose] def VllPolicy.core (A : Arch) (emptyVReg : A.VReg → Empty)
    (hclear : ∀ (f : A.Flags) (c : A.Cond),
      FlagMask.disjoint (A.condReads c) FlagMask.all = true →
      A.evalCond A.clearFlagsVal c = A.evalCond f c)
    (condOfCmp? : CmpOp → Option A.Cond)
    (cmpFlags : List A.Cond)
    (hcmp : ∀ co cc (w : Width) (a b : BitVec w.bits) f,
      condOfCmp? co = some cc → A.evalCond (A.cmpFlags w a b f) cc = co.evalBits a b) :
    VllPolicy A where
  hooks := VllNativeHooks.core A emptyVReg condOfCmp? cmpFlags
  spec := {
    clearFlags_frame := hclear
    cmpFlags_spec := hcmp
    vecSpec := vllEmptyVecTarget A emptyVReg
  }

/-- Minimal `VllPolicy.core` specialization with no compare-flag condition mapping (`none`). -/
@[expose] def VllPolicy.coreNoCmp (A : Arch) (emptyVReg : A.VReg → Empty)
    (hclear : ∀ (f : A.Flags) (c : A.Cond),
      FlagMask.disjoint (A.condReads c) FlagMask.all = true →
      A.evalCond A.clearFlagsVal c = A.evalCond f c) : VllPolicy A :=
  VllPolicy.core A emptyVReg hclear (fun _ => none) [] (fun _ _ _ _ _ _ h => nomatch h)

/-- `GprIsa` instantiated on `Instr A` from policy `P`. -/
@[expose] def vllGprIsa (A : Arch) (P : VllPolicy A) : GprIsa A.Reg A.VReg A.Cond (Instr A) :=
  vllGprIsaOfHooks A P.hooks

/-- `FrameIsa` instantiated on `Instr A` extending `vllFrameIsa A` with policy `P`. -/
@[expose] def vllFrameIsaWith (A : Arch) (P : VllPolicy A) : FrameIsa A.Reg (Instr A) :=
  vllFrameIsaOfHooks A P.hooks

/-- Full `Isa` over `Instr A` assembled from `(A, P)`. -/
@[expose] def vllIsa (A : Arch) (P : VllPolicy A) : Isa :=
  vllIsaOfHooks A P.hooks

/-- `LegalTarget` associated with `(A, P)`. -/
@[expose] def vllLegalTarget (A : Arch) (P : VllPolicy A) : LegalTarget :=
  vllLegalTargetOfHooks A P.hooks

/-- Generic `GprTarget` soundness proof for `vllGprIsa A P` over `vllMach A`. -/
theorem vllGprTarget (A : Arch) (hwf : A.Wf) (P : VllPolicy A) :
    GprTarget (vllMach A) (vllGprIsa A P) A.abi.scratch where
  negCond_reads := hwf.negCond_reads
  negCond_eval s c := hwf.negCond_eval s.flags c
  clearFlags_spec := by
    intro h k s post; dsimp only [vllGprIsa, vllGprIsaOfHooks]
    cases hcf : P.hooks.clearFlags? with
    | none =>
      exact Machine.FallsTo.weaken (vllMach_clearFlags_spec hwf (P.spec.clearFlags_frame s.flags))
        (fun _ h => nomatch h) (fun _ h => nomatch h) (flagMask_sub_refl _)
    | some c => exact P.spec.clearFlags_override_spec hcf
  mov_spec := by
    intro h k rd rs s post; dsimp only [vllGprIsa, vllGprIsaOfHooks]
    cases hmv : P.hooks.mov? with
    | none => exact vllMach_mov_spec hwf
    | some f => exact P.spec.mov_override_spec hmv
  movi_spec := by
    intro h k rd c s post; dsimp only [vllGprIsa, vllGprIsaOfHooks]
    cases hmvi : P.hooks.movi? with
    | none => exact fallsTo_weaken_rd (vllMach_movi_spec (A := A) (rd := rd) (imm := c))
    | some f => exact P.spec.movi_override_spec hmvi
  setcc_spec := by
    intro h k rd c s post hrd; dsimp only [vllGprIsa, vllGprIsaOfHooks]
    cases hsc : P.hooks.setcc? with
    | none => exact fallsTo_weaken_rd (vllMach_setcc_spec hwf (rd := rd) (c := c))
    | some f => exact P.spec.setcc_override_spec hsc hrd
  jmp_spec := by
    intro h k j l s post hc hl hcont; dsimp only [vllGprIsa, vllGprIsaOfHooks] at hc ⊢
    cases hjm : P.hooks.jmp? with
    | none =>
      simp only [hjm, Option.getD_none] at hc
      exact vllMach_jmp_spec hc hl (hcont s (Machine.Frame.refl _ _ _ _ _) rfl)
    | some f =>
      simp only [hjm, Option.getD_some] at hc; exact P.spec.jmp_override_spec hjm hc hl hcont
  jcc_spec := by
    intro h k j c l s post hc hl hcont; dsimp only [vllGprIsa, vllGprIsaOfHooks] at hc hcont ⊢
    cases hjc : P.hooks.jcc? with
    | none =>
      simp only [hjc, Option.getD_none, List.length_singleton] at hc hcont
      have h0 := hcont s (Machine.Frame.refl _ _ _ _ _) rfl
      exact vllMach_jcc_spec hc hl h0.1 h0.2
    | some f =>
      simp only [hjc, Option.getD_some] at hc hcont; exact P.spec.jcc_override_spec hjc hc hl hcont
  jnzGpr_spec := by
    intro h k j r l b s post hc hl hr hb hcont
    dsimp only [vllGprIsa, vllGprIsaOfHooks] at hc hcont ⊢
    cases hjz : P.hooks.jnzGpr? with
    | none =>
      simp only [hjz, Option.getD_none, List.length_singleton] at hc hcont
      exact vllMach_jnzGpr_spec hwf hc hl hb hcont
    | some f =>
      simp only [hjz, Option.getD_some] at hc hcont
      exact P.spec.jnzGpr_override_spec hjz hc hl hr hb hcont
  op_spec := by
    intro h k sig rs code pas dsts vh c clob vs Q s post hop ha hd hrel hwp
    dsimp only [vllGprIsa, vllGprIsaOfHooks] at hop
    cases hhk : P.hooks.opHook code pas dsts vh with
    | some res => rw [hhk] at hop; cases hop; exact P.spec.opHook_spec hhk ha hd hrel hwp
    | none =>
      rw [hhk] at hop
      exact vllCoreOp_spec A hwf P.hooks.condOfCmp? P.spec.cmpFlags_spec hop ha hd hrel hwp
  load_spec := by
    intro h k t rd a c clob v s post hld hrd ha hval
    dsimp only [vllGprIsa, vllGprIsaOfHooks] at hld
    cases hhk : P.hooks.loadHook t rd a with
    | some res => rw [hhk] at hld; cases hld; exact P.spec.loadHook_spec hhk hrd ha hval
    | none => rw [hhk] at hld; exact vllCoreLoad_spec A hwf P.hooks.loadExt hld hval
  store_spec := by
    intro h k t pa a c clob v s post hst hns hh hok
    dsimp only [vllGprIsa, vllGprIsaOfHooks] at hst
    cases hhk : P.hooks.storeHook t pa a with
    | some res => rw [hhk] at hst; cases hst; exact P.spec.storeHook_spec hhk hns hh hok
    | none => rw [hhk] at hst; exact vllCoreStore_spec A hwf hst hns hh hok
  load_zero32 := P.spec.load_zero32
  load_zext := P.spec.load_zext
  op_zero32 := P.spec.op_zero32
  testOp_spec := P.spec.testOp_spec
  cmpMem_spec := P.spec.cmpMem_spec
  testMem_spec := P.spec.testMem_spec
  loadSext_spec := P.spec.loadSext_spec
  cmpZeroJcc_spec := P.spec.cmpZeroJcc_spec
  testJcc_spec := P.spec.testJcc_spec
  aluMem_spec := P.spec.aluMem_spec
  aluMem_zero32 := P.spec.aluMem_zero32
  jnzMem_spec := P.spec.jnzMem_spec
  rmwMem_spec := P.spec.rmwMem_spec
  leaArith_spec := P.spec.leaArith_spec
  leaArith_zero32 := P.spec.leaArith_zero32
  jnzGprInv_spec := P.spec.jnzGprInv_spec
  op_boolFlag_spec := P.spec.op_boolFlag_spec
  op_cmpFlags_spec := P.spec.op_cmpFlags_spec
  op_aluZero_spec := P.spec.op_aluZero_spec
  testOp_boolFlag_spec := P.spec.testOp_boolFlag_spec
  testMem_boolFlag_spec := P.spec.testMem_boolFlag_spec
  cmpMem_flags_spec := P.spec.cmpMem_flags_spec
  loadZextIdx_spec := P.spec.loadZextIdx_spec
  loadZextIdx_zero32 := P.spec.loadZextIdx_zero32
  loadZextIdx_zext := P.spec.loadZextIdx_zext
  loadSextZextIdx_spec := P.spec.loadSextZextIdx_spec
  storeZextIdx_spec := P.spec.storeZextIdx_spec
  leaArithZext_spec := P.spec.leaArithZext_spec
  moviDeadFlags?_spec := P.spec.moviDeadFlags?_spec

/-- Extend `vllFrameTarget A hwf` with optional bulk save/restore specs from `P`. -/
theorem vllFrameSpecWith (A : Arch) (hwf : A.Wf) (P : VllPolicy A) :
    FrameSpec (vllMach A) (vllFrameIsaWith A P) A.condReads (vllFramePreds A) where
  sp_disj := hwf.sp_disj
  scratch_disj := hwf.scratch_disj
  cs_disj := hwf.cs_disj
  ra_disj := hwf.ra_disj
  argRegs_nodup := hwf.argRegs_nodup
  retRegs_nodup := hwf.retRegs_nodup
  retAddr_region := by
    intro a ra m h
    cases hkind : A.abi.raKind with
    | stack =>
      simp only [vllFramePreds, hkind] at h
      simpa only [vllFrameIsaWith, vllFrameIsaOfHooks, vllFrameIsa, Abi.raBytes, hkind,
        RaKind.raBytes] using cell64_region h
    | linkReg lr =>
      simp only [vllFramePreds, hkind] at h
      simpa only [vllFrameIsaWith, vllFrameIsaOfHooks, vllFrameIsa, Abi.raBytes, hkind,
        RaKind.raBytes] using h
  raReg_of_raRegs := by
    intro s s' ra hkeep hra
    cases hkind : A.abi.raKind with
    | stack => simp [vllFramePreds, hkind]
    | linkReg lr =>
      simp only [vllFramePreds, hkind] at hra ⊢
      have hlr := hkeep lr (by
        simp [vllFrameIsaWith, vllFrameIsaOfHooks, vllFrameIsa, Abi.raRegs, hkind, RaKind.raRegs])
      exact hlr.trans hra
  slots_le_frameSize := hwf.slots_le_frameSize
  spOk_frame := hwf.spOk_frame
  spEntry_call := hwf.spEntry_call
  labelAddr_eq := fun hk hfirst => VllHost.labelAddr_wf _ hk hfirst
  label_spec := fun hk hnext => vllMach_label_spec hk hnext
  prologue_spec := fun hra _ hbound hm => vllMach_prologue_spec hwf hra hbound hm
  epilogue_spec := fun _ hbound hm => vllMach_epilogue_spec hwf hbound hm
  slotSt_spec := fun _ _ hm => vllMach_slotSt_spec hm
  slotLd_spec := fun _ _ hm => vllMach_slotLd_spec hm
  canonAbi_spec := fun ht _ hholds => vllMach_canonAbi_spec hwf ht hholds
  call_spec := fun hc hm hcont => vllMach_call_spec hwf hc hm hcont
  exitJmp_spec := fun hc hcont =>
    vllMach_exitJmp_spec hc (hcont _ (Machine.Frame.refl _ _ _ _ _) rfl)
  ret_spec := fun hc hra hm hcont => vllMach_ret_spec hc hra hm hcont
  saveRegs_spec := P.spec.saveRegs_spec
  restoreRegs_spec := P.spec.restoreRegs_spec

/-- `FrameTarget` extending `vllFrameTarget A hwf` with optional bulk callee-saved overrides. -/
@[expose] def vllFrameTargetWith (A : Arch) (hwf : A.Wf) (P : VllPolicy A) :
    FrameTarget (vllMach A) (vllFrameIsaWith A P) A.condReads where
  toFramePreds := vllFramePreds A
  spec := vllFrameSpecWith A hwf P

/-- Verified `LeanQbe.T.Target` instantiated directly over `BedrockMach` L1 (`vllMach A` /
`Instr A`), inheriting `Rega.lowerFn` and `Rega.lowerFn_correct` for any `(A, hwf, P)`. -/
@[expose] def vllTarget (A : Arch) (hwf : A.Wf) (P : VllPolicy A) : Target where
  toIsa := vllIsa A P
  mach := vllMach A
  gprSpec := vllGprTarget A hwf P
  frameSpec := vllFrameTargetWith A hwf P
  vecSpec := P.spec.vecSpec

theorem vllTarget_toIsa (A : Arch) (hwf : A.Wf) (P : VllPolicy A) :
    (vllTarget A hwf P).toIsa = vllIsa A P := rfl

theorem vllFrameIsaWith_eq_base (A : Arch) (P : VllPolicy A)
    (hs : P.hooks.saveRegs? = none) (hr : P.hooks.restoreRegs? = none) :
    vllFrameIsaWith A P = vllFrameIsa A := by
  dsimp only [vllFrameIsaWith, vllFrameIsaOfHooks]; rw [hs, hr]; rfl

/-- Lower a typed `Fn` directly to `BedrockMach` L1 `List (Instr A)` via `Rega.lowerFn`. -/
@[expose] def vllLowerFn (A : Arch) (P : VllPolicy A) (hints : (vllIsa A P).Hints)
    (E : Rega.Ext) (f : Fn) : Except String (List (Instr A)) :=
  Rega.lowerFn (vllIsa A P) hints E f

/-- End-to-end soundness of `vllLowerFn`, specializing `Rega.lowerFn_correct` to
`vllTarget A hwf P`. -/
theorem vllLowerFn_correct (A : Arch) (hwf : A.Wf) (P : VllPolicy A)
    (host : VllHost A) (hints : (vllIsa A P).Hints) (E : Rega.Ext) (f : Fn)
    (Γ : Env) (n nX : Nat) (bound : Sym → Nat) {code : List (Instr A)} {k₀ : Nat}
    (hf : f.Wf) (hl : vllLowerFn A P hints E f = .ok code)
    (hc : code.IsInfixAt host.prog k₀) (hu : (vllTarget A hwf P).LabelsUnique host)
    (hfr : Rega.effFrame (vllIsa A P) hints E ≤ n)
    (hn : n + A.abi.raBytes ≤ 2 ^ 64)
    (hcal : ∀ g as bs, (g, as, bs) ∈ E.callees →
      (vllTarget A hwf P).FnSpec host g (Γ g as bs) (bound g) nX ∧
      Rega.effFrame (vllIsa A P) hints E + A.abi.raBytes + bound g ≤ n)
    (hex : ∀ g, g ∈ E.exits → (vllTarget A hwf P).Defined host g ∧ nX ≤ n) :
    (vllTarget A hwf P).FnSpec host f.name (Func.spec Γ f.body) n nX :=
  Rega.lowerFn_correct (vllTarget A hwf P) host hints E f Γ n nX bound
    hf hl hc hu hfr hn hcal hex

/-! ## 3. Structural `Rega.LabelClean` for `vllIsa` -/

/-- Label-cleanliness obligation on custom hooks in `VllNativeHooks A` (unused hooks default via
fast 1-step `intro h; cases h`). -/
structure VllHooksNoLab (A : Arch) (H : VllNativeHooks A) : Prop where
  clearFlags : ∀ {c}, H.clearFlags? = some c → NoVllLab c := by intros; contradiction
  mov : ∀ {f d s}, H.mov? = some f → NoVllLab (f d s) := by intros; contradiction
  movi : ∀ {f d c}, H.movi? = some f → NoVllLab (f d c) := by intros; contradiction
  setcc : ∀ {f d c}, H.setcc? = some f → NoVllLab (f d c) := by intros; contradiction
  jmp : ∀ {f l}, H.jmp? = some f → NoVllLab (f l) := by intros; contradiction
  jcc : ∀ {f c l}, H.jcc? = some f → NoVllLab (f c l) := by intros; contradiction
  jnzGpr : ∀ {f r l}, H.jnzGpr? = some f → NoVllLab (f r l).1 := by intros; contradiction
  jnzGprInv : ∀ {f r inv l}, H.jnzGprInv? = some f → NoVllLab (f r inv l).1 :=
    by intros; contradiction
  opHook : ∀ {sig rs : List Ty} {code : OpCode sig rs} {pas dsts vh c cl},
    H.opHook code pas dsts vh = some (c, cl) → NoVllLab c := by intros; contradiction
  loadHook : ∀ {t r a c cl}, H.loadHook t r a = some (c, cl) → NoVllLab c :=
    by intros; contradiction
  storeHook : ∀ {t pa a c cl}, H.storeHook t pa a = some (c, cl) → NoVllLab c :=
    by intros; contradiction
  testOp : ∀ {w neg pa pb pd c cl}, H.testOp w neg pa pb pd = some (c, cl) → NoVllLab c :=
    by intros; contradiction
  cmpMem : ∀ {co w a pb pd c cl}, H.cmpMem co w a pb pd = some (c, cl) → NoVllLab c :=
    by intros; contradiction
  testMem : ∀ {w neg a pb pd c cl}, H.testMem w neg a pb pd = some (c, cl) → NoVllLab c :=
    by intros; contradiction
  loadSext : ∀ {m n r a c cl}, H.loadSext m n r a = some (c, cl) → NoVllLab c :=
    by intros; contradiction
  cmpZeroJcc : ∀ {co w r l c cl}, H.cmpZeroJcc co w r l = some (c, cl) → NoVllLab c :=
    by intros; contradiction
  testJcc : ∀ {neg w r mask l c cl}, H.testJcc neg w r mask l = some (c, cl) → NoVllLab c :=
    by intros; contradiction
  aluMem : ∀ {w code memRhs a pb rd c cl},
    H.aluMem w code memRhs a pb rd = some (c, cl) → NoVllLab c := by intros; contradiction
  jnzMem : ∀ {a inv l c cl}, H.jnzMem a inv l = some (c, cl) → NoVllLab c :=
    by intros; contradiction
  rmwMem : ∀ {w code a pb c cl}, H.rmwMem w code a pb = some (c, cl) → NoVllLab c :=
    by intros; contradiction
  leaArith : ∀ {w base? idx sc disp rd c cl},
    H.leaArith w base? idx sc disp rd = some (c, cl) → NoVllLab c := by intros; contradiction
  loadZextIdx : ∀ {t rd base idx sc disp c cl},
    H.loadZextIdx t rd base idx sc disp = some (c, cl) → NoVllLab c := by intros; contradiction
  loadSextZextIdx : ∀ {m n rd base idx sc disp c cl},
    H.loadSextZextIdx m n rd base idx sc disp = some (c, cl) → NoVllLab c :=
    by intros; contradiction
  storeZextIdx : ∀ {t pa base idx sc disp c cl},
    H.storeZextIdx t pa base idx sc disp = some (c, cl) → NoVllLab c := by intros; contradiction
  leaArithZext : ∀ {base? idx sh disp rd c cl},
    H.leaArithZext base? idx sh disp rd = some (c, cl) → NoVllLab c := by intros; contradiction
  moviDeadFlags : ∀ {f d c}, H.moviDeadFlags? = some f → NoVllLab (f d c).1 :=
    by intros; contradiction
  saveRegs : ∀ {f base rs}, H.saveRegs? = some f → NoVllLab (f base rs) := by intros; contradiction
  restoreRegs : ∀ {f base rs}, H.restoreRegs? = some f → NoVllLab (f base rs) :=
    by intros; contradiction
  vmov : ∀ w d s, NoVllLab (H.vec.vmov w d s)
  vmovi : ∀ w d c code, H.vec.vmovi w d c = some code → NoVllLab code
  vslotSt : ∀ w i s, NoVllLab (H.vec.vslotSt w i s)
  vslotLd : ∀ w d i, NoVllLab (H.vec.vslotLd w d i)
  vop : ∀ {sig rs : List Ty} (code : OpCode sig rs) pas dsts vh c cl,
    H.vec.vop code pas dsts vh = some (c, cl) → NoVllLab c
  vload : ∀ t d a c cl, H.vec.vload t d a = some (c, cl) → NoVllLab c
  vstore : ∀ t s a c cl, H.vec.vstore t s a = some (c, cl) → NoVllLab c

/-- Structural `Rega.LabelClean` proof for `vllIsa A P` given `VllHooksNoLab`. -/
theorem vllLabelClean (A : Arch) (P : VllPolicy A) (hnl : VllHooksNoLab A P.hooks) :
    Rega.LabelClean (vllIsa A P) where
  label_inj _ _ h := Instr.label.inj h
  mov d s := by
    dsimp only [vllIsa, vllIsaOfHooks, vllGprIsaOfHooks]
    cases h : P.hooks.mov? with
    | none => exact noVllLab_one (fun _ e => by cases e)
    | some _ => exact hnl.mov h
  movi d c := by
    dsimp only [vllIsa, vllIsaOfHooks, vllGprIsaOfHooks]
    cases h : P.hooks.movi? with
    | none => exact noVllLab_one (fun _ e => by cases e)
    | some _ => exact hnl.movi h
  setcc d c := by
    dsimp only [vllIsa, vllIsaOfHooks, vllGprIsaOfHooks]
    cases h : P.hooks.setcc? with
    | none => exact noVllLab_one (fun _ e => by cases e)
    | some _ => exact hnl.setcc h
  jmp l := by
    dsimp only [vllIsa, vllIsaOfHooks, vllGprIsaOfHooks]
    cases h : P.hooks.jmp? with
    | none => exact noVllLab_one (fun _ e => by cases e)
    | some _ => exact hnl.jmp h
  jcc c l := by
    dsimp only [vllIsa, vllIsaOfHooks, vllGprIsaOfHooks]
    cases h : P.hooks.jcc? with
    | none => exact noVllLab_one (fun _ e => by cases e)
    | some _ => exact hnl.jcc h
  jnzGpr r l := by
    dsimp only [vllIsa, vllIsaOfHooks, vllGprIsaOfHooks]
    cases h : P.hooks.jnzGpr? with
    | none => exact noVllLab_one (fun _ e => by cases e)
    | some _ => exact hnl.jnzGpr h
  jnzGprInv _ _ _ _ h := hnl.jnzGprInv h
  op code pas dsts vh c cl h := by
    dsimp only [vllIsa, vllIsaOfHooks, vllGprIsaOfHooks] at h
    cases hhk : P.hooks.opHook code pas dsts vh with
    | some _ => rw [hhk] at h; cases h; exact hnl.opHook hhk
    | none => rw [hhk] at h; exact vllCoreOp_noLab h
  testOp _ _ _ _ _ _ _ h := hnl.testOp h
  cmpMem _ _ _ _ _ _ _ h := hnl.cmpMem h
  testMem _ _ _ _ _ _ _ h := hnl.testMem h
  loadSext _ _ _ _ _ _ h := hnl.loadSext h
  cmpZeroJcc _ _ _ _ _ _ h := hnl.cmpZeroJcc h
  testJcc _ _ _ _ _ _ _ h := hnl.testJcc h
  aluMem _ _ _ _ _ _ _ _ h := hnl.aluMem h
  jnzMem _ _ _ _ _ h := hnl.jnzMem h
  rmwMem _ _ _ _ _ _ h := hnl.rmwMem h
  leaArith _ _ _ _ _ _ _ _ h := hnl.leaArith h
  loadZextIdx _ _ _ _ _ _ _ _ h := hnl.loadZextIdx h
  loadSextZextIdx _ _ _ _ _ _ _ _ _ h := hnl.loadSextZextIdx h
  storeZextIdx _ _ _ _ _ _ _ _ h := hnl.storeZextIdx h
  leaArithZext _ _ _ _ _ _ _ h := hnl.leaArithZext h
  moviDeadFlags _ _ _ h := hnl.moviDeadFlags h
  load t r a c cl h := by
    dsimp only [vllIsa, vllIsaOfHooks, vllGprIsaOfHooks] at h
    cases hhk : P.hooks.loadHook t r a with
    | some _ => rw [hhk] at h; cases h; exact hnl.loadHook hhk
    | none => rw [hhk] at h; exact vllCoreLoad_noLab h
  store t pa a c cl h := by
    dsimp only [vllIsa, vllIsaOfHooks, vllGprIsaOfHooks] at h
    cases hhk : P.hooks.storeHook t pa a with
    | some _ => rw [hhk] at h; cases h; exact hnl.storeHook hhk
    | none => rw [hhk] at h; exact vllCoreStore_noLab h
  clearFlags := by
    dsimp only [vllIsa, vllIsaOfHooks, vllGprIsaOfHooks]
    cases h : P.hooks.clearFlags? with
    | none => exact noVllLab_one (fun _ e => by cases e)
    | some _ => exact hnl.clearFlags h
  vmov := hnl.vmov
  vmovi := hnl.vmovi
  vslotSt := hnl.vslotSt
  vslotLd := hnl.vslotLd
  vop := hnl.vop
  vload := hnl.vload
  vstore := hnl.vstore
  prologue _ := noVllLab_one (fun _ e => by cases e)
  epilogue _ := noVllLab_one (fun _ e => by cases e)
  slotSt _ _ := noVllLab_one (fun _ e => by cases e)
  slotLd _ _ := noVllLab_one (fun _ e => by cases e)
  saveRegs _ _ _ h := hnl.saveRegs h
  restoreRegs _ _ _ h := hnl.restoreRegs h
  canonAbi _ _ := noVllLab_one (fun _ e => by cases e)
  call _ := noVllLab_one (fun _ e => by cases e)
  exitJmp _ := noVllLab_one (fun _ e => by cases e)
  ret := noVllLab_one (fun _ e => by cases e)

/-- Automatic `Rega.LabelClean` proof for every `VllPolicy.core` instance. -/
theorem vllLabelClean_core (A : Arch) (emptyVReg : A.VReg → Empty)
    (hclear : ∀ (f : A.Flags) (c : A.Cond),
      FlagMask.disjoint (A.condReads c) FlagMask.all = true →
      A.evalCond A.clearFlagsVal c = A.evalCond f c)
    (condOfCmp? : CmpOp → Option A.Cond)
    (cmpFlags : List A.Cond)
    (hcmp : ∀ co cc (w : Width) (a b : BitVec w.bits) f,
      condOfCmp? co = some cc → A.evalCond (A.cmpFlags w a b f) cc = co.evalBits a b) :
    Rega.LabelClean (vllIsa A (VllPolicy.core A emptyVReg hclear condOfCmp? cmpFlags hcmp)) :=
  vllLabelClean A _ {
    vmov := fun _ d _ => (emptyVReg d).elim
    vmovi := fun _ d _ _ _ => (emptyVReg d).elim
    vslotSt := fun _ _ s => (emptyVReg s).elim
    vslotLd := fun _ d _ => (emptyVReg d).elim
    vop := fun _ _ _ _ _ _ h => nomatch h
    vload := fun _ d _ _ _ _ => (emptyVReg d).elim
    vstore := fun _ s _ _ _ _ => (emptyVReg s).elim
  }

/-! ## 4. Generic `VllHost` Builder & Structural `LabelsUnique` -/

/-- Index of the first `.label l` occurrence in `prog` (or `prog.length` when absent). -/
@[expose] def firstLabelIdx {A : Arch} : List (Instr A) → Sym → Nat
  | [], _ => 0
  | .label l' :: rest, l => if l' == l then 0 else 1 + firstLabelIdx rest l
  | _ :: rest, l => 1 + firstLabelIdx rest l

theorem firstLabelIdx_eq {A : Arch} : ∀ (prog : List (Instr A)) (k : Nat) (l : Sym),
    prog[k]? = some (.label l) → (∀ j < k, prog[j]? ≠ some (.label l)) →
    firstLabelIdx prog l = k
  | [], k, _, hk, _ => by simp at hk
  | i :: rest, 0, l, hk, _ => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
    subst hk
    simp [firstLabelIdx]
  | i :: rest, k + 1, l, hk, hfirst => by
    have h0 : i ≠ .label l := by
      intro heq
      exact hfirst 0 (Nat.zero_lt_succ k) (by simp [heq])
    have hk' : rest[k]? = some (.label l) := by simpa using hk
    have hf' : ∀ j < k, rest[j]? ≠ some (.label l) := fun j hj =>
      hfirst (j + 1) (Nat.succ_lt_succ hj)
    have ih := firstLabelIdx_eq rest k l hk' hf'
    cases i with
    | label l' =>
      have hne : (l' == l) = false := beq_false_of_ne (fun h => h0 (h ▸ rfl))
      simp only [firstLabelIdx, hne, Bool.false_eq_true, ↓reduceIte, ih]
      omega
    | _ => simp only [firstLabelIdx, ih]; omega

/-- Construct a well-formed `VllHost A` from any instruction sequence `prog` with
`4 * prog.length < 2 ^ 64`, assigning address `4 * k` to instruction index `k`. -/
@[expose] def mkVllHost (A : Arch) (prog : List (Instr A))
    (hlen : 4 * prog.length < 2 ^ 64) : VllHost A where
  prog := prog
  addrOf k := BitVec.ofNat 64 (4 * k)
  labelAddr l := BitVec.ofNat 64 (4 * firstLabelIdx prog l)
  addrOf_inj := by
    intro i j hi hj heq
    have hnat := congrArg BitVec.toNat heq
    simp only [BitVec.toNat_ofNat] at hnat
    have hi' : 4 * i < 2 ^ 64 := by omega
    have hj' : 4 * j < 2 ^ 64 := by omega
    rw [Nat.mod_eq_of_lt hi', Nat.mod_eq_of_lt hj'] at hnat
    omega
  labelAddr_wf := fun hk hfirst => congrArg (fun n => BitVec.ofNat 64 (4 * n))
    (firstLabelIdx_eq prog _ _ hk hfirst)

/-- Structural `Target.LabelsUnique` for a single-function `mkVllHost` lowered by `vllLowerFn`. -/
theorem vllLowerFn_labelsUnique (A : Arch) (hwf : A.Wf) (P : VllPolicy A)
    (hnl : VllHooksNoLab A P.hooks) {hints : (vllIsa A P).Hints} {E : Rega.Ext} {f : Fn}
    {code : List (Instr A)} (hl : vllLowerFn A P hints E f = .ok code)
    (hlen : 4 * code.length < 2 ^ 64) :
    (vllTarget A hwf P).LabelsUnique (mkVllHost A code hlen) :=
  fun i j l hi hj => Rega.lowerFn_labelsUnique (vllLabelClean A P hnl) hl i j l hi hj

/-- Every label emitted by `vllLowerFn` is either `f.name` or `Rega.lname f.name idx`. -/
theorem vllLowerFn_label_mem (A : Arch) (P : VllPolicy A) (hnl : VllHooksNoLab A P.hooks)
    {hints : (vllIsa A P).Hints} {E : Rega.Ext} {f : Fn} {code : List (Instr A)}
    (hl : vllLowerFn A P hints E f = .ok code) {i : Nat} {l : Sym}
    (hi : code[i]? = some (.label l)) :
    l = f.name ∨ ∃ j, l = Rega.lname f.name j :=
  Rega.lowerFn_label_mem (vllLabelClean A P hnl) hl hi

end LeanQbe.T.Vll
