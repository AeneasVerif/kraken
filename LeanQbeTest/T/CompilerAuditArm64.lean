module

public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.Arm64.IselLemmas4
public import LeanQbe.T.Arm64.FrameLemmas
public import LeanQbe.T.Arm64.IselStepRules
public import LeanQbe.T.Arm64.LinkRec
public import LeanQbe.T.Arm64.Litmus
public import LeanQbeTest.T.MainLinkArm64Test
import all Kraken.Mem
import all Kraken.Separation

/-!
# AAPCS64 AArch64 Backend, Multi-Chunk Linker, Cyclic Recursion, & Litmus Audit

Self-contained machine-level audit for the AAPCS64 AArch64 (`Kraken.AArch64`) backend of
`lean-qbe`. This module imports only `Kraken.AArch64` (`LeanQbe.T.Arm64.*`), never `Kraken.X64`.

## What This Workstream Proves
1. **Verified AArch64 backend contracts (`Arm64.Targ`, `Arm64.TargLemmas`)**:
   * `armGprSpec` (`GprTarget`), `armFrameSpec` (`FrameTarget`, AAPCS64 `X30`/`SP` frame), and
     `armLabelClean` (`Rega.LabelClean`).
   * Capability parity `armSupportsOp_parity` aligning `armLegalTarget` with `armTarget.toIsa`.
2. **Compositional multi-chunk linking (`MainLinkArm64Test`)**:
   * 2-chunk (`bump` + `doubleBump`) and 3-chunk (`bump` + `doubleBump` + `top`) literal-backed
     metadata-only linking (`checkLink` / `checkLinkList` / `*WithLabels`) with closed
     `Eventually` machine runs and negative rejections (duplicate names, `.L` label hygiene,
     mismatched callee bounds).
3. **Cyclic and mutual recursion (`Arm64.LinkRec`)**:
   * Closed Kraken AArch64 `Eventually (step1 Host.exe)` correctness for mutually recursive
     `isEven` / `isOdd` and fuel-guarded `recSum` (normal return and `"out_of_fuel"` exit),
     negative checks, plus concrete non-vacuous witnesses.
4. **Scalar litmus suite (`Arm64.Litmus`)**:
   * Closed Kraken AArch64 correctness for memory mutation (`tracer`), loops (`sumto`), calls
     (`callinc`, `sumcall`), spilling (`spill10`), and abnormal exits (`twice` -> `"fail"`),
     plus concrete execution witnesses.

## Inputs / Assumptions
* Arbitrary Kraken `Host` containing the compiled directive sequence as an infix with unique
  labels (`Host.LabelsUnique`), AAPCS64 16-byte stack alignment (`SP % 16 = 0`), return address
  in `X30`, and disjoint caller-owned memory.
* Concrete `*_nv` witnesses discharge every host/state precondition on `*.host` via `armInit`.

## Trusted Computing Base (TCB)
* Lean 4 kernel (`propext`, `Classical.choice`, `Quot.sound`).
* Kraken AArch64 operational semantics (`Kraken.AArch64.step1`, `Host.exe`, `MachineData`,
  `Mem 64`).
* External assembly/linking outside Kraken is outside scope; every AArch64 directive sequence is
  verified directly against Kraken's AST and step relation.
-/

set_option autoImplicit false

@[expose] public section

namespace CompilerAuditArm64

open Std Std.ExtHashMap
open LeanQbe.T LeanQbe.T.Arm64 LeanQbeTest.T Kraken

/-! ## 1. Verified AAPCS64 AArch64 Backend Contracts -/

theorem audit_gpr : GprTarget armMach armGpr armScratch :=
  armGprSpec

theorem audit_frame : Nonempty (FrameTarget armMach armFrame armCondReads) :=
  ⟨armFrameSpec⟩

theorem audit_label_clean : Rega.LabelClean armTarget.toIsa :=
  armLabelClean

theorem audit_arm_to_isa :
    armTarget.toIsa =
      { Reg := Reg, VReg := Empty, Cond := ArmCond, Directive := Directive,
        gpr := armGpr, vec := VecIsa.empty Reg ArmCond Directive, frame := armFrame,
        supportsAddrDisp := armSupportsAddrDisp,
        supportsAddrIdx := armSupportsAddrIdx,
        supportsTestFuse := true,
        supportsCmpMem := armSupportsCmpMem,
        supportsAddrZextIdx := armSupportsAddrIdx } :=
  armTarget_toIsa

theorem audit_leaf_zero_frame : armFrame.leafZeroFrame = true := rfl

theorem audit_parity (t : Ty) (f : Fmt) (n : Nat)
    (u1n : Tup (Arg (fun _ => Unit)) [.bits n])
    (u2n : Tup (Arg (fun _ => Unit)) [.bits n, .bits n])
    (uc3 : Tup (Arg (fun _ => Unit)) [.bits n, .bits n, .bool])
    (uf3 : Tup (Arg (fun _ => Unit)) [.bits n, .bits n, .bits n])
    (u164 : Tup (Arg (fun _ => Unit)) [i64])
    (u264 : Tup (Arg (fun _ => Unit)) [i64, i64])
    (u216 : Tup (Arg (fun _ => Unit)) [i16, i16])
    {sig rs : List Ty} (vcode : OpCode sig rs) (vargs : Tup (Arg (fun _ => Unit)) sig) :
    (armLegalTarget.keepsPacked t = false ∧
      armLegalTarget.supportsTy (.float f) = false ∧
      armTarget.toIsa.hasBank (.float f) = false ∧
      armTarget.toIsa.vec.supportsVecOp vcode vargs = false) ∧
    (armTarget.toIsa.supportsOp (.popcnt n) u1n = false) ∧
    (armTarget.toIsa.supportsOp (.clz n) u1n = ([32, 64].contains n) ∧
      armTarget.toIsa.supportsOp (.cls n) u1n = ([32, 64].contains n) ∧
      armTarget.toIsa.supportsOp (.rbit n) u1n = ([32, 64].contains n) ∧
      armTarget.toIsa.supportsOp (.ctz n) u1n = ([32, 64].contains n)) ∧
    (armTarget.toIsa.supportsOp (.fshl n) uf3 = ([32, 64].contains n) ∧
      armTarget.toIsa.supportsOp (.fshr n) uf3 = ([32, 64].contains n) ∧
      armTarget.toIsa.supportsOp (.addc n) uc3 = ([32, 64].contains n) ∧
      armTarget.toIsa.supportsOp (.subb n) uc3 = ([32, 64].contains n) ∧
      armTarget.toIsa.supportsOp (.umulw n) u2n = ([32, 64].contains n) ∧
      armTarget.toIsa.supportsOp (.smulw n) u2n = ([32, 64].contains n)) ∧
    (armTarget.toIsa.supportsOp (.bswap (.bits n)) u1n = ([16, 32, 64].contains n)) ∧
    (armTarget.toIsa.supportsOp (.add (.bits n)) u2n = ([8, 16, 32, 64].contains n) ∧
      armTarget.toIsa.supportsOp (.udiv0 n) u2n = ([8, 16, 32, 64].contains n) ∧
      armTarget.toIsa.supportsOp (.sdiv0 n) u2n = ([8, 16, 32, 64].contains n)) ∧
    (armLegalTarget.isLegalOp (.clz 64) false = true ∧
      armTarget.toIsa.supportsOp (.clz 64) u164 = true ∧
      armLegalTarget.isLegalOp (.udiv0 64) false = true ∧
      armTarget.toIsa.supportsOp (.udiv0 64) u264 = true ∧
      armLegalTarget.isLegalOp (.add i16) false = true ∧
      armTarget.toIsa.supportsOp (.add i16) u216 = true) :=
  armSupportsOp_parity t f n u1n u2n uc3 uf3 u164 u264 u216 vcode vargs

/-! ## 2. Compositional Multi-Chunk Linking on AArch64 -/

theorem audit_link2_run :
    Eventually (armTarget.mach.step MainLinkArm64Test.twoChunkLinked.host)
      (fun st => armTarget.mach.pc st = armInit.ra0 ∧
        armTarget.RetsIn (bs := [i64]) (36#64, ()) (armTarget.mach.data st) ∧
        (armTarget.mach.mem (armTarget.mach.data st) =⋆
          (cell64 0x1000#64 21#64 ⋆ emp) ⋆
          armTarget.Exit armInit.sp0 (MainLinkArm64Test.twoChunkLinked.bound "doubleBump") ⋆ emp))
      (armTarget.mach.mkState
        (armInit.initState (as := [i64, i64])
          (MainLinkArm64Test.twoChunkLinked.bound "doubleBump")
          MainLinkArm64Test.initMemBytes (0x1000#64, 5#64, ()))
        (armTarget.mach.labelAddr MainLinkArm64Test.twoChunkLinked.host "doubleBump")) :=
  MainLinkArm64Test.twoChunk_run_ret1_sep

theorem audit_link3_run :
    Eventually (armTarget.mach.step MainLinkArm64Test.threeChunkLinked.host)
      (fun st => armTarget.mach.pc st = armInit.ra0 ∧
        armTarget.RetsIn (bs := [i64]) (37#64, ()) (armTarget.mach.data st) ∧
        (armTarget.mach.mem (armTarget.mach.data st) =⋆
          (cell64 0x1000#64 21#64 ⋆ emp) ⋆
          armTarget.Exit armInit.sp0 (MainLinkArm64Test.threeChunkLinked.bound "top") ⋆ emp))
      (armTarget.mach.mkState
        (armInit.initState (as := [i64, i64])
          (MainLinkArm64Test.threeChunkLinked.bound "top")
          MainLinkArm64Test.initMemBytes (0x1000#64, 5#64, ()))
        (armTarget.mach.labelAddr MainLinkArm64Test.threeChunkLinked.host "top")) :=
  MainLinkArm64Test.threeChunk_run_ret1_sep

theorem audit_link_neg :
    checkLink armLayout MainLinkArm64Test.chunk1Compiled MainLinkArm64Test.dupChunkCompiled =
      false ∧
    checkLink armLayout MainLinkArm64Test.chunk1Compiled MainLinkArm64Test.dotLChunkCompiled =
      false :=
  ⟨MainLinkArm64Test.link_dup_name_rejected, MainLinkArm64Test.link_dotL_name_rejected⟩

/-! ## 3. Cyclic & Mutual Recursion on AArch64 -/

theorem audit_rec_neg :
    LeanQbe.T.LinkRec.checkCompileRec armTarget armLayout armLegalTarget [] [] 16 16
      LeanQbe.T.LinkRec.recSumMod.fns Arm64.LinkRec.recSumHints 2048 = false ∧
    LeanQbe.T.LinkRec.checkCompileRec armTarget armLayout armLegalTarget [] [] 0 1000
      LeanQbe.T.LinkRec.evenOddRecMod.fns Arm64.LinkRec.evenOddHints 2048 = false :=
  ⟨Arm64.LinkRec.recSum_missing_exit_rejected, Arm64.LinkRec.evenOdd_stack_overflow_rejected⟩

theorem audit_is_even {hh : Host} (k₀ : Nat)
    (hc : Arm64.LinkRec.evenOddCompiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {k : Nat} (hk : k ≤ 32) (n : BitVec 64) (hn : n.toNat ≤ k)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hx0 : (s.regs.getXReg .X0).toBitVec = n)
    (hra : s.regs.X30 = ra.toUInt64) (hsp : s.regs.SP.toNat % 16 = 0)
    (hmem : s.dmem =⋆
      region (s.regs.SP.toBitVec - BitVec.ofNat 64 (Arm64.LinkRec.evenOddCompiled.boundAt k))
        (Arm64.LinkRec.evenOddCompiled.boundAt k) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧ (st.data.regs.getXReg .X0).toBitVec = LeanQbe.T.LinkRec.isEvenVal n ∧
        (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
          st.data.regs.getXReg r = s.regs.getXReg r) ∧
        st.data.regs.SP = s.regs.SP ∧
        (st.data.dmem =⋆
          region (s.regs.SP.toBitVec - BitVec.ofNat 64 (Arm64.LinkRec.evenOddCompiled.boundAt k))
            (Arm64.LinkRec.evenOddCompiled.boundAt k) ⋆ R))
      ⟨s, Labels.label "isEven"⟩ :=
  Arm64.LinkRec.isEven_arm64_correct (hh := hh) k₀ hc hu hk n hn s ra R hx0 hra hsp hmem

theorem audit_rec_sum {hh : Host} (k₀ : Nat)
    (hc : Arm64.LinkRec.recSumCompiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (hexit : armTarget.Defined hh "out_of_fuel")
    {k : Nat} (hk : k ≤ 16) (n f : BitVec 64) (hf : f.toNat ≤ k)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hx0 : (s.regs.getXReg .X0).toBitVec = n) (hx1 : (s.regs.getXReg .X1).toBitVec = f)
    (hra : s.regs.X30 = ra.toUInt64) (hsp : s.regs.SP.toNat % 16 = 0)
    (hmem : s.dmem =⋆
      region (s.regs.SP.toBitVec - BitVec.ofNat 64 (Arm64.LinkRec.recSumCompiled.boundAt k))
        (Arm64.LinkRec.recSumCompiled.boundAt k) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st =>
        (∃ sum, LeanQbe.T.LinkRec.recSumOutcome n f.toNat = .inl sum ∧
          st.pc = ra ∧ (st.data.regs.getXReg .X0).toBitVec = sum ∧
          (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
            st.data.regs.getXReg r = s.regs.getXReg r) ∧
          st.data.regs.SP = s.regs.SP) ∨
        (∃ rem, LeanQbe.T.LinkRec.recSumOutcome n f.toNat = .inr rem ∧
          st.pc = Labels.label "out_of_fuel" ∧ (st.data.regs.getXReg .X0).toBitVec = rem ∧
          st.data.regs.SP.toNat % 16 = 0))
      ⟨s, Labels.label "recSum"⟩ :=
  Arm64.LinkRec.recSum_arm64_correct (hh := hh) k₀ hc hu hexit hk n f hf s ra R hx0 hx1 hra hsp hmem

attribute [local instance] Arm64.LinkRec.evenOddHost in
theorem audit_is_even_nv :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧ (st.data.regs.getXReg .X0).toBitVec = 1#64)
      ⟨Arm64.LinkRec.evenOddState 4 4#64, Labels.label "isEven"⟩ :=
  Arm64.LinkRec.isEven_4_arm64_nonvacuous

attribute [local instance] Arm64.LinkRec.recSumHost in
theorem audit_rec_sum_nv :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧ (st.data.regs.getXReg .X0).toBitVec = 6#64)
      ⟨Arm64.LinkRec.recSumState 5 3#64 5#64, Labels.label "recSum"⟩ ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = Labels.label "out_of_fuel" ∧
        (st.data.regs.getXReg .X0).toBitVec = 3#64)
      ⟨Arm64.LinkRec.recSumState 2 5#64 2#64, Labels.label "recSum"⟩ :=
  ⟨Arm64.LinkRec.recSum_normal_arm64_nonvacuous,
   Arm64.LinkRec.recSum_out_of_fuel_arm64_nonvacuous⟩

/-! ## 4. Scalar Litmus Suite on AArch64 -/

theorem audit_tracer [hh : Host] (k₀ : Nat)
    (hc : Arm64.Litmus.tracerCompiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (a b p v0 : BitVec 64) (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (ha : (s.regs.getXReg .X0).toBitVec = a) (hb : (s.regs.getXReg .X1).toBitVec = b)
    (hpp : (s.regs.getXReg .X2).toBitVec = p)
    (hra : s.regs.X30 = ra.toUInt64) (hsp : s.regs.SP.toNat % 16 = 0)
    (hmem : s.dmem =⋆ cell64 p v0 ⋆
      region (s.regs.SP.toBitVec - BitVec.ofNat 64 (Arm64.Litmus.tracerCompiled.bound "tracer"))
        (Arm64.Litmus.tracerCompiled.bound "tracer") ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧ (st.data.regs.getXReg .X0).toBitVec = a + b ∧
        (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
          st.data.regs.getXReg r = s.regs.getXReg r) ∧
        st.data.regs.SP = s.regs.SP ∧
        (st.data.dmem =⋆ cell64 p (a + b) ⋆
          region (s.regs.SP.toBitVec - BitVec.ofNat 64 (Arm64.Litmus.tracerCompiled.bound "tracer"))
            (Arm64.Litmus.tracerCompiled.bound "tracer") ⋆ R))
      ⟨s, Labels.label "tracer"⟩ :=
  Arm64.Litmus.tracer_arm64_correct (hh := hh) k₀ hc hu a b p v0 s ra R ha hb hpp hra hsp hmem

theorem audit_twice [hh : Host] (k₀ : Nat)
    (hc : Arm64.Litmus.twiceCompiled.code.IsInfixAt Host.prog k₀)
    (hfail : armTarget.Defined hh "fail") (hu : Host.LabelsUnique)
    (a b : BitVec 64) (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (ha : (s.regs.getXReg .X0).toBitVec = a) (hb : (s.regs.getXReg .X1).toBitVec = b)
    (hra : s.regs.X30 = ra.toUInt64) (hsp : s.regs.SP.toNat % 16 = 0)
    (hmem : s.dmem =⋆
      region (s.regs.SP.toBitVec - BitVec.ofNat 64 (Arm64.Litmus.twiceCompiled.bound "twice"))
        (Arm64.Litmus.twiceCompiled.bound "twice") ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st =>
        (Examples.Litmus.Truthy a ∧ Examples.Litmus.Truthy b ∧
          st.pc = ra ∧ (st.data.regs.getXReg .X0).toBitVec = a + b ∧
          (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
            st.data.regs.getXReg r = s.regs.getXReg r) ∧
          st.data.regs.SP = s.regs.SP) ∨
        ((¬Examples.Litmus.Truthy a ∧ st.pc = Labels.label "fail" ∧
          (st.data.regs.getXReg .X0).toBitVec = a ∧ st.data.regs.SP.toNat % 16 = 0) ∨
         (Examples.Litmus.Truthy a ∧ ¬Examples.Litmus.Truthy b ∧
          st.pc = Labels.label "fail" ∧ (st.data.regs.getXReg .X0).toBitVec = b ∧
          st.data.regs.SP.toNat % 16 = 0)))
      ⟨s, Labels.label "twice"⟩ :=
  Arm64.Litmus.twice_arm64_correct (hh := hh) k₀ hc hfail hu a b s ra R ha hb hra hsp hmem

theorem audit_spill10 [hh : Host] (k₀ : Nat)
    (hc : Arm64.Litmus.spill10Compiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (a b : BitVec 64) (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (ha : (s.regs.getXReg .X0).toBitVec = a) (hb : (s.regs.getXReg .X1).toBitVec = b)
    (hra : s.regs.X30 = ra.toUInt64) (hsp : s.regs.SP.toNat % 16 = 0)
    (hmem : s.dmem =⋆
      region (s.regs.SP.toBitVec - BitVec.ofNat 64 (Arm64.Litmus.spill10Compiled.bound "spill10"))
        (Arm64.Litmus.spill10Compiled.bound "spill10") ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧ (st.data.regs.getXReg .X0).toBitVec = Examples.Litmus.spill10Val a b ∧
        (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
          st.data.regs.getXReg r = s.regs.getXReg r) ∧
        st.data.regs.SP = s.regs.SP ∧
        (st.data.dmem =⋆
          region (s.regs.SP.toBitVec -
              BitVec.ofNat 64 (Arm64.Litmus.spill10Compiled.bound "spill10"))
            (Arm64.Litmus.spill10Compiled.bound "spill10") ⋆ R))
      ⟨s, Labels.label "spill10"⟩ :=
  Arm64.Litmus.spill10_arm64_correct (hh := hh) k₀ hc hu a b s ra R ha hb hra hsp hmem

theorem audit_sumcall [hh : Host] (k₀ : Nat)
    (hc : Arm64.Litmus.sumcallCompiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (n b : BitVec 64) (hn : n.toNat < 2 ^ 32)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hx0 : (s.regs.getXReg .X0).toBitVec = n) (hx1 : (s.regs.getXReg .X1).toBitVec = b)
    (hra : s.regs.X30 = ra.toUInt64) (hsp : s.regs.SP.toNat % 16 = 0)
    (hmem : s.dmem =⋆
      region (s.regs.SP.toBitVec - BitVec.ofNat 64 (Arm64.Litmus.sumcallCompiled.bound "sumcall"))
        (Arm64.Litmus.sumcallCompiled.bound "sumcall") ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧
        (st.data.regs.getXReg .X0).toBitVec = Examples.Litmus.tri n.toNat + n + b ∧
        (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
          st.data.regs.getXReg r = s.regs.getXReg r) ∧
        st.data.regs.SP = s.regs.SP ∧
        (st.data.dmem =⋆
          region (s.regs.SP.toBitVec -
              BitVec.ofNat 64 (Arm64.Litmus.sumcallCompiled.bound "sumcall"))
            (Arm64.Litmus.sumcallCompiled.bound "sumcall") ⋆ R))
      ⟨s, Labels.label "sumcall"⟩ :=
  Arm64.Litmus.sumcall_arm64_correct (hh := hh) k₀ hc hu n b hn s ra R hx0 hx1 hra hsp hmem

attribute [local instance] Arm64.Litmus.tracerHost in
theorem audit_tracer_nv :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧ (st.data.regs.getXReg .X0).toBitVec = 42#64 ∧
        (st.data.dmem =⋆ cell64 0x1000#64 42#64 ⋆
          region (0x1000#64 - BitVec.ofNat 64 (Arm64.Litmus.tracerCompiled.bound "tracer"))
            (Arm64.Litmus.tracerCompiled.bound "tracer") ⋆ emp))
      ⟨Arm64.Litmus.tracerState0, Labels.label "tracer"⟩ :=
  Arm64.Litmus.tracer_arm64_nonvacuous

attribute [local instance] Arm64.Litmus.twiceHost in
theorem audit_twice_exit :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Labels.label "fail" ∧ (st.data.regs.getXReg .X0).toBitVec = 0#64)
      ⟨Arm64.Litmus.twiceState 20#64 0#64, Labels.label "twice"⟩ :=
  Arm64.Litmus.twice_arm64_nonvacuous_exit

/-! ## 5. `Arm64.IselStepRules` Frame & `@[scoped isel_step]` Rules -/

section IselStepArmAudit

theorem audit_arm_upd_regs {s s' : MachineData} {gClob : List Reg} {fClob : FlagMask}
    (hkeep : ∀ r, r ∉ gClob → get s' r = get s r)
    (hflg : fClob = maskAll ∨ fClob = maskNZCV ∧
      (∀ c, FlagMask.disjoint (armCondReads c) maskNZCV = true →
        c.interp s'.status = c.interp s.status) ∨
      s'.status = s.status) :
    armMach.Frame armCondReads s s' gClob [] fClob :=
  armFrame_upd_regs hkeep hflg

theorem audit_arm_nzcv {s s' : MachineData} {gClob : List Reg}
    (hkeep : ∀ r, r ∉ gClob → get s' r = get s r) :
    armMach.Frame armCondReads s s' gClob [] maskNZCV :=
  armFrame_nzcv hkeep

theorem audit_arm_st_eq {s s' : MachineData} {gClob : List Reg} {fClob : FlagMask}
    (hkeep : ∀ r, r ∉ gClob → get s' r = get s r) (hst : s'.status = s.status) :
    armMach.Frame armCondReads s s' gClob [] fClob :=
  armFrame_status_eq hkeep hst

theorem audit_arm_ldr_cons [Host] {d : XReg} {c : BitVec 64} {rest : List Directive}
    {s : MachineData} {Q : MachineData → Prop}
    (hk : _root_.Program.wp rest Q (fun _ _ => False) (wr s d c)) :
    _root_.Program.wp (armLdrPoolBv d c :: rest) Q (fun _ _ => False) s :=
  IselStep.arm_step_ldrPool_cons hk

theorem audit_arm_ldr_last [Host] {d : XReg} {c : BitVec 64}
    {s : MachineData} {Q : MachineData → Prop}
    (hk : Q (wr s d c)) :
    _root_.Program.wp [armLdrPoolBv d c] Q (fun _ _ => False) s :=
  IselStep.arm_step_ldrPool_last hk

end IselStepArmAudit

/-! ## 6. Logical Foundations Audit (`#print axioms`) -/

#print axioms audit_gpr
#print axioms audit_frame
#print axioms audit_label_clean
#print axioms audit_arm_to_isa
#print axioms audit_leaf_zero_frame
#print axioms audit_parity
#print axioms audit_link2_run
#print axioms audit_link3_run
#print axioms audit_link_neg
#print axioms audit_rec_neg
#print axioms audit_is_even
#print axioms audit_rec_sum
#print axioms audit_is_even_nv
#print axioms audit_rec_sum_nv
#print axioms audit_tracer
#print axioms audit_twice
#print axioms audit_spill10
#print axioms audit_sumcall
#print axioms audit_tracer_nv
#print axioms audit_twice_exit
#print axioms audit_arm_upd_regs
#print axioms audit_arm_nzcv
#print axioms audit_arm_st_eq
#print axioms audit_arm_ldr_cons
#print axioms audit_arm_ldr_last

end CompilerAuditArm64
