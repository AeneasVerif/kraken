module

public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.Amd64.IselLemmas5
public import LeanQbe.T.Amd64.IselVecLemmas3
public import LeanQbe.T.Amd64.FrameLemmas
public import LeanQbe.T.Amd64.IselStepRules
public import LeanQbe.T.Amd64.LinkRec
public import LeanQbe.T.Amd64.Litmus
public import LeanQbeTest.T.MainLinkAmd64Test
import LeanQbe.T.Logic.MemLemmas

/-!
# SysV x86-64 Backend, Multi-Chunk Linker, Cyclic Recursion, & Litmus Audit

Self-contained machine-level audit for the SysV x86-64 (`Kraken.X64`) backend of `lean-qbe`.
This module imports only `Kraken.X64` (`LeanQbe.T.Amd64.*`), never `Kraken.AArch64`.

## What This Workstream Proves
1. **Verified x86-64 backend contracts (`Amd64.Targ`, `Amd64.TargLemmas`)**:
   * `x64GprSpec` (`GprTarget`), `x64VecSpec` (`VecTarget`, AVX2/AVX-512/SSE), `x64FrameSpec`
     (`FrameTarget`, SysV call/return/stack frame), and `x64LabelClean` (`Rega.LabelClean`).
   * Capability parity `x64SupportsOp_parity` aligning `x64LegalTarget` with `x64Target.toIsa`.
2. **Compositional multi-chunk linking (`MainLinkAmd64Test`)**:
   * 2-chunk (`bump` + `doubleBump`) and 3-chunk (`bump` + `doubleBump` + `top`) literal-backed
     metadata-only linking (`checkLink` / `checkLinkList`) with closed `Eventually` machine runs
     and negative rejections (duplicate names, exit collisions, mismatched callee bounds).
3. **Cyclic and mutual recursion (`Amd64.LinkRec`)**:
   * Closed Kraken x64 `Eventually (step1 Host.exe)` correctness for mutually recursive `isEven` /
     `isOdd` and fuel-guarded `recSum` (normal return and `"out_of_fuel"` exit), negative checks
     for undeclared exits and stack-budget overflow, plus concrete non-vacuous witnesses.
4. **Scalar litmus suite (`Amd64.Litmus`)**:
   * Closed Kraken x64 correctness for memory mutation (`tracer`), loops (`sumto`), calls
     (`callinc`, `sumcall`), spilling (`spill10`), and abnormal exits (`twice` -> `"fail"`),
     plus concrete execution witnesses.

## Inputs / Assumptions
* Arbitrary Kraken `Host` containing the compiled directive sequence as an infix with unique
  labels (`Host.LabelsUnique`), SysV 16-byte stack alignment at call sites
  (`(rsp + 8) % 16 = 0`), return address `ra` stored at `rsp`, and disjoint caller-owned memory.
* Concrete `*_nv` witnesses discharge every host/state precondition on `*.host` via `x64Init`.

## Trusted Computing Base (TCB)
* Lean 4 kernel (`propext`, `Classical.choice`, `Quot.sound`).
* Kraken x86-64 operational semantics (`Kraken.X64.step1`, `Host.exe`, `MachineData`, `Mem 64`).
* External assembly/linking outside Kraken is outside scope; every x86-64 directive sequence is
  verified directly against Kraken's AST and step relation.
-/

set_option autoImplicit false

public section

namespace CompilerAuditX64

open Std Std.ExtHashMap
open LeanQbe.T LeanQbe.T.Amd64 LeanQbeTest.T Kraken

/-! ## 1. Verified SysV x86-64 Backend Contracts -/

theorem audit_gpr : GprTarget x64Mach x64Gpr x64Scratch :=
  x64GprSpec

theorem audit_vec :
    VecTarget x64Mach x64Vec x64CondReads x64Frame.sp x64Scratch x64FrameSpec.spOk :=
  x64VecSpec

theorem audit_frame : Nonempty (FrameTarget x64Mach x64Frame x64CondReads) :=
  ⟨x64FrameSpec⟩

theorem audit_label_clean : Rega.LabelClean x64Target.toIsa :=
  x64LabelClean

theorem audit_x64_to_isa :
    x64Target.toIsa =
      { Reg := Reg64, VReg := RegMm, Cond := CondCode, Directive := Directive,
        gpr := x64Gpr, vec := x64Vec, frame := x64Frame,
        supportsAddrDisp := x64SupportsAddrDisp,
        supportsAddrIdx := x64SupportsAddrIdx,
        supportsTestFuse := true,
        supportsCmpMem := x64SupportsCmpMem,
        supportsTestMem := x64SupportsCmpMem } :=
  x64Target_toIsa

theorem audit_parity (t : Ty) (hp : x64LegalTarget.keepsPacked t = true) (imm : BitVec 8)
    (u1 : Tup (Arg (fun _ => Unit)) [t])
    (u2 : Tup (Arg (fun _ => Unit)) [t, t])
    (u3 : Tup (Arg (fun _ => Unit)) [t, t, t])
    (uSha1 : Tup (Arg (fun _ => Unit)) [v4i32, v4i32, v4i32])
    (uSha2 : Tup (Arg (fun _ => Unit)) [v4i32, v4i32]) :
    (x64Target.toIsa.supportsOp (.copy t) u1 = true ↔
      x64LegalTarget.isLegalOp (.copy t) false = true) ∧
    (x64Target.toIsa.supportsOp (.add t) u2 = true ↔
      x64LegalTarget.isLegalOp (.add t) false = true) ∧
    (x64Target.toIsa.supportsOp (.and t) u2 = true ↔
      x64LegalTarget.isLegalOp (.and t) false = true) ∧
    (x64Target.toIsa.supportsOp (.or t) u2 = true ↔
      x64LegalTarget.isLegalOp (.or t) false = true) ∧
    (x64Target.toIsa.supportsOp (.xor t) u2 = true ↔
      x64LegalTarget.isLegalOp (.xor t) false = true) ∧
    (x64Target.toIsa.supportsOp (.not t) u1 = true ↔
      x64LegalTarget.isLegalOp (.not t) false = true) ∧
    (x64Target.toIsa.supportsOp (.ternlog t imm) u3 = true ↔
      x64LegalTarget.isLegalOp (.ternlog t imm) false = true) ∧
    (x64Target.toIsa.supportsOp (.shufd t imm) u1 = true ↔
      x64LegalTarget.isLegalOp (.shufd t imm) false = true) ∧
    (x64Target.toIsa.supportsOp (.shufb t) u2 = true ↔
      x64LegalTarget.isLegalOp (.shufb t) false = true) ∧
    (x64Target.toIsa.supportsOp (.alignr t imm) u2 = true ↔
      x64LegalTarget.isLegalOp (.alignr t imm) false = true) ∧
    (x64Target.toIsa.supportsOp (.blendw t imm) u2 = true ↔
      x64LegalTarget.isLegalOp (.blendw t imm) false = true) ∧
    (x64Target.toIsa.supportsOp (.fadd t) u2 = true ↔
      x64LegalTarget.isLegalOp (.fadd t) false = true) ∧
    (x64Target.toIsa.supportsOp (.fsub t) u2 = true ↔
      x64LegalTarget.isLegalOp (.fsub t) false = true) ∧
    (x64Target.toIsa.supportsOp .sha256rnds2 uSha1 = false ∧
      x64LegalTarget.isLegalOp .sha256rnds2 false = false) ∧
    (x64Target.toIsa.supportsOp .sha256msg1 uSha2 = false ∧
      x64LegalTarget.isLegalOp .sha256msg1 false = false) ∧
    (x64Target.toIsa.supportsOp .sha256msg2 uSha2 = false ∧
      x64LegalTarget.isLegalOp .sha256msg2 false = false) :=
  x64SupportsOp_parity t hp imm u1 u2 u3 uSha1 uSha2

/-! ## 2. Compositional Multi-Chunk Linking on x86-64 -/

theorem audit_link2_run :
    Eventually (x64Target.mach.step MainLinkAmd64Test.twoChunkLinked.host)
      (fun st => x64Target.mach.pc st = x64Init.ra0 ∧
        x64Target.RetsIn (bs := [i64]) (36#64, ()) (x64Target.mach.data st) ∧
        (x64Target.mach.mem (x64Target.mach.data st) =⋆
          (cell64 0x1000#64 21#64 ⋆ emp) ⋆
          x64Target.Exit x64Init.sp0 (MainLinkAmd64Test.twoChunkLinked.bound "doubleBump") ⋆ emp))
      (x64Target.mach.mkState
        (x64Init.initState (as := [i64, i64])
          (MainLinkAmd64Test.twoChunkLinked.bound "doubleBump")
          MainLinkAmd64Test.initMemBytes (0x1000#64, 5#64, ()))
        (x64Target.mach.labelAddr MainLinkAmd64Test.twoChunkLinked.host "doubleBump")) :=
  MainLinkAmd64Test.twoChunk_run_ret1_sep

theorem audit_link3_run :
    Eventually (x64Target.mach.step MainLinkAmd64Test.threeChunkLinked.host)
      (fun st => x64Target.mach.pc st = x64Init.ra0 ∧
        x64Target.RetsIn (bs := [i64]) (37#64, ()) (x64Target.mach.data st) ∧
        (x64Target.mach.mem (x64Target.mach.data st) =⋆
          (cell64 0x1000#64 21#64 ⋆ emp) ⋆
          x64Target.Exit x64Init.sp0 (MainLinkAmd64Test.threeChunkLinked.bound "top") ⋆ emp))
      (x64Target.mach.mkState
        (x64Init.initState (as := [i64, i64])
          (MainLinkAmd64Test.threeChunkLinked.bound "top")
          MainLinkAmd64Test.initMemBytes (0x1000#64, 5#64, ()))
        (x64Target.mach.labelAddr MainLinkAmd64Test.threeChunkLinked.host "top")) :=
  MainLinkAmd64Test.threeChunk_run_ret1_sep

theorem audit_link_neg :
    checkLink x64Layout MainLinkAmd64Test.chunk1Compiled MainLinkAmd64Test.dupChunkCompiled =
      false ∧
    checkCompileLit x64Target.frame.label x64Layout.progSmall
      MainLinkAmd64Test.chunk1Code MainLinkAmd64Test.chunk1Bounds
      (MainLinkAmd64Test.chunk1Fns.map Fn.name) ["bump"] 2048 = false :=
  ⟨MainLinkAmd64Test.link_dup_name_rejected, MainLinkAmd64Test.exit_collision_rejected⟩

/-! ## 3. Cyclic & Mutual Recursion on x86-64 -/

theorem audit_rec_neg :
    LeanQbe.T.LinkRec.checkCompileRec x64Target x64Layout x64LegalTarget [] [] 16 16
      LeanQbe.T.LinkRec.recSumMod.fns Amd64.LinkRec.recSumHints 2048 = false ∧
    LeanQbe.T.LinkRec.checkCompileRec x64Target x64Layout x64LegalTarget [] [] 0 1000
      LeanQbe.T.LinkRec.evenOddRecMod.fns Amd64.LinkRec.evenOddHints 2048 = false :=
  ⟨Amd64.LinkRec.recSum_missing_exit_rejected, Amd64.LinkRec.evenOdd_stack_overflow_rejected⟩

theorem audit_is_even {hh : Host} (k₀ : Nat)
    (hc : Amd64.LinkRec.evenOddCompiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {k : Nat} (hk : k ≤ 32) (n : BitVec 64) (hn : n.toNat ≤ k)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hrdi : s.regs.get64 .rdi = n)
    (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hmem : s.dmem =⋆
      (region (s.regs.get64 .rsp - BitVec.ofNat 64 (Amd64.LinkRec.evenOddCompiled.boundAt k))
          (Amd64.LinkRec.evenOddCompiled.boundAt k) ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧ st.data.regs.get64 .rax = LeanQbe.T.LinkRec.isEvenVal n ∧
        (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15],
          st.data.regs.get64 r = s.regs.get64 r) ∧
        st.data.regs.get64 .rsp = s.regs.get64 .rsp + 8#64 ∧
        (st.data.dmem =⋆
          region (s.regs.get64 .rsp - BitVec.ofNat 64 (Amd64.LinkRec.evenOddCompiled.boundAt k))
            (Amd64.LinkRec.evenOddCompiled.boundAt k + 8) ⋆ R))
      ⟨s, Labels.label "isEven"⟩ :=
  Amd64.LinkRec.isEven_x64_correct (hh := hh) k₀ hc hu hk n hn s ra R hrdi hsp hmem

theorem audit_rec_sum {hh : Host} (k₀ : Nat)
    (hc : Amd64.LinkRec.recSumCompiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (hexit : x64Target.Defined hh "out_of_fuel")
    {k : Nat} (hk : k ≤ 16) (n f : BitVec 64) (hf : f.toNat ≤ k)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hrdi : s.regs.get64 .rdi = n) (hrsi : s.regs.get64 .rsi = f)
    (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hmem : s.dmem =⋆
      (region (s.regs.get64 .rsp - BitVec.ofNat 64 (Amd64.LinkRec.recSumCompiled.boundAt k))
          (Amd64.LinkRec.recSumCompiled.boundAt k) ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st =>
        (∃ sum, LeanQbe.T.LinkRec.recSumOutcome n f.toNat = .inl sum ∧
          st.pc = ra ∧ st.data.regs.get64 .rax = sum ∧
          (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15],
            st.data.regs.get64 r = s.regs.get64 r) ∧
          st.data.regs.get64 .rsp = s.regs.get64 .rsp + 8#64) ∨
        (∃ rem, LeanQbe.T.LinkRec.recSumOutcome n f.toNat = .inr rem ∧
          st.pc = Labels.label "out_of_fuel" ∧ st.data.regs.get64 .rdi = rem ∧
          (st.data.regs.get64 .rsp + 8#64).toNat % 16 = 0))
      ⟨s, Labels.label "recSum"⟩ :=
  Amd64.LinkRec.recSum_x64_correct (hh := hh) k₀ hc hu hexit hk n f hf s ra R hrdi hrsi hsp hmem

attribute [local instance] Amd64.LinkRec.evenOddHost in
theorem audit_is_even_nv :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧ st.data.regs.get64 .rax = 1#64)
      ⟨Amd64.LinkRec.evenOddState 4 4#64, Labels.label "isEven"⟩ :=
  Amd64.LinkRec.isEven_4_x64_nonvacuous

attribute [local instance] Amd64.LinkRec.recSumHost in
theorem audit_rec_sum_nv :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧ st.data.regs.get64 .rax = 6#64)
      ⟨Amd64.LinkRec.recSumState 5 3#64 5#64, Labels.label "recSum"⟩ ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = Labels.label "out_of_fuel" ∧ st.data.regs.get64 .rdi = 3#64)
      ⟨Amd64.LinkRec.recSumState 2 5#64 2#64, Labels.label "recSum"⟩ :=
  ⟨Amd64.LinkRec.recSum_normal_x64_nonvacuous, Amd64.LinkRec.recSum_out_of_fuel_x64_nonvacuous⟩

/-! ## 4. Scalar Litmus Suite on x86-64 -/

theorem audit_tracer [hh : Host] (k₀ : Nat)
    (hc : Amd64.Litmus.tracerCompiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (a b p v0 : BitVec 64) (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (ha : s.regs.get64 .rdi = a) (hb : s.regs.get64 .rsi = b) (hpp : s.regs.get64 .rdx = p)
    (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hmem : s.dmem =⋆ cell64 p v0 ⋆
      (region (s.regs.get64 .rsp - BitVec.ofNat 64 (Amd64.Litmus.tracerCompiled.bound "tracer"))
          (Amd64.Litmus.tracerCompiled.bound "tracer") ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧ st.data.regs.get64 .rax = a + b ∧
        (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15],
          st.data.regs.get64 r = s.regs.get64 r) ∧
        st.data.regs.get64 .rsp = s.regs.get64 .rsp + 8#64 ∧
        (st.data.dmem =⋆ cell64 p (a + b) ⋆
          region (s.regs.get64 .rsp - BitVec.ofNat 64 (Amd64.Litmus.tracerCompiled.bound "tracer"))
            (Amd64.Litmus.tracerCompiled.bound "tracer" + 8) ⋆ R))
      ⟨s, Labels.label "tracer"⟩ :=
  Amd64.Litmus.tracer_x64_correct (hh := hh) k₀ hc hu a b p v0 s ra R ha hb hpp hsp hmem

theorem audit_twice [hh : Host] (k₀ : Nat)
    (hc : Amd64.Litmus.twiceCompiled.code.IsInfixAt Host.prog k₀)
    (hfail : x64Target.Defined hh "fail") (hu : Host.LabelsUnique)
    (a b : BitVec 64) (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (ha : s.regs.get64 .rdi = a) (hb : s.regs.get64 .rsi = b)
    (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hmem : s.dmem =⋆
      (region (s.regs.get64 .rsp - BitVec.ofNat 64 (Amd64.Litmus.twiceCompiled.bound "twice"))
          (Amd64.Litmus.twiceCompiled.bound "twice") ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st =>
        (Examples.Litmus.Truthy a ∧ Examples.Litmus.Truthy b ∧
          st.pc = ra ∧ st.data.regs.get64 .rax = a + b ∧
          (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15],
            st.data.regs.get64 r = s.regs.get64 r) ∧
          st.data.regs.get64 .rsp = s.regs.get64 .rsp + 8#64) ∨
        ((¬Examples.Litmus.Truthy a ∧ st.pc = Labels.label "fail" ∧
          st.data.regs.get64 .rdi = a ∧ (st.data.regs.get64 .rsp + 8#64).toNat % 16 = 0) ∨
         (Examples.Litmus.Truthy a ∧ ¬Examples.Litmus.Truthy b ∧
          st.pc = Labels.label "fail" ∧ st.data.regs.get64 .rdi = b ∧
          (st.data.regs.get64 .rsp + 8#64).toNat % 16 = 0)))
      ⟨s, Labels.label "twice"⟩ :=
  Amd64.Litmus.twice_x64_correct (hh := hh) k₀ hc hfail hu a b s ra R ha hb hsp hmem

theorem audit_spill10 [hh : Host] (k₀ : Nat)
    (hc : Amd64.Litmus.spill10Compiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (a b : BitVec 64) (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (ha : s.regs.get64 .rdi = a) (hb : s.regs.get64 .rsi = b)
    (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hmem : s.dmem =⋆
      (region (s.regs.get64 .rsp - BitVec.ofNat 64 (Amd64.Litmus.spill10Compiled.bound "spill10"))
          (Amd64.Litmus.spill10Compiled.bound "spill10") ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧ st.data.regs.get64 .rax = Examples.Litmus.spill10Val a b ∧
        (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15],
          st.data.regs.get64 r = s.regs.get64 r) ∧
        st.data.regs.get64 .rsp = s.regs.get64 .rsp + 8#64 ∧
        (st.data.dmem =⋆
          region (s.regs.get64 .rsp -
              BitVec.ofNat 64 (Amd64.Litmus.spill10Compiled.bound "spill10"))
            (Amd64.Litmus.spill10Compiled.bound "spill10" + 8) ⋆ R))
      ⟨s, Labels.label "spill10"⟩ :=
  Amd64.Litmus.spill10_x64_correct (hh := hh) k₀ hc hu a b s ra R ha hb hsp hmem

theorem audit_sumcall [hh : Host] (k₀ : Nat)
    (hc : Amd64.Litmus.sumcallCompiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (n b : BitVec 64) (hn : n.toNat < 2 ^ 32)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hrdi : s.regs.get64 .rdi = n) (hrsi : s.regs.get64 .rsi = b)
    (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hmem : s.dmem =⋆
      (region (s.regs.get64 .rsp - BitVec.ofNat 64 (Amd64.Litmus.sumcallCompiled.bound "sumcall"))
          (Amd64.Litmus.sumcallCompiled.bound "sumcall") ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧ st.data.regs.get64 .rax = Examples.Litmus.tri n.toNat + n + b ∧
        (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15],
          st.data.regs.get64 r = s.regs.get64 r) ∧
        st.data.regs.get64 .rsp = s.regs.get64 .rsp + 8#64 ∧
        (st.data.dmem =⋆
          region (s.regs.get64 .rsp -
              BitVec.ofNat 64 (Amd64.Litmus.sumcallCompiled.bound "sumcall"))
            (Amd64.Litmus.sumcallCompiled.bound "sumcall" + 8) ⋆ R))
      ⟨s, Labels.label "sumcall"⟩ :=
  Amd64.Litmus.sumcall_x64_correct (hh := hh) k₀ hc hu n b hn s ra R hrdi hrsi hsp hmem

attribute [local instance] Amd64.Litmus.tracerHost in
theorem audit_tracer_nv :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧ st.data.regs.get64 .rax = 42#64 ∧
        (st.data.dmem =⋆ cell64 0x1000#64 42#64 ⋆
          region (0x0ff8#64 - BitVec.ofNat 64 (Amd64.Litmus.tracerCompiled.bound "tracer"))
            (Amd64.Litmus.tracerCompiled.bound "tracer" + 8) ⋆ emp))
      ⟨Amd64.Litmus.tracerState0, Labels.label "tracer"⟩ :=
  Amd64.Litmus.tracer_x64_nonvacuous

attribute [local instance] Amd64.Litmus.twiceHost in
theorem audit_twice_exit :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Labels.label "fail" ∧ st.data.regs.get64 .rdi = 0#64)
      ⟨Amd64.Litmus.twiceState 20#64 0#64, Labels.label "twice"⟩ :=
  Amd64.Litmus.twice_x64_nonvacuous_exit

/-! ## 5. `Amd64.IselStepRules` Frame & `@[scoped isel_step]` Rules -/

section IselStepX64Audit

theorem audit_x64_frame_eq {s s' : MachineData} {g : List Reg64} {f : FlagMask}
    (hregs : ∀ r, r ∉ g → s'.regs.get64 r = s.regs.get64 r)
    (hzmms : s'.zmms = s.zmms)
    (hflags : x64Mach.UpdFlags x64CondReads s s' f) :
    x64Mach.Frame x64CondReads s s' g [] f :=
  x64_frame_of_eq hregs hzmms hflags

theorem audit_x64_upd_all (s s' : MachineData) :
    x64Mach.UpdFlags x64CondReads s s' maskAll :=
  updFlags_maskAll s s'

theorem audit_x64_wp_dir [Host] {E : Int64 → MachineData → Prop}
    {dir : Directive} {rest : List Directive} {s : MachineData} {P Q : MachineData → Prop}
    (hd : Directive.FallsTo dir s P)
    (hk : ∀ s', P s' → _root_.Program.wp rest Q E s') :
    _root_.Program.wp (dir :: rest) Q E s :=
  x64_wp_step_dir hd hk

theorem audit_x64_mov_cons [Host] {E : Int64 → MachineData → Prop}
    {rd rs : Reg64} {rest : List Directive} {s : MachineData} {Q : MachineData → Prop}
    (hk : _root_.Program.wp rest Q E { s with regs := s.regs.set64 rd (s.regs.get64 rs) }) :
    _root_.Program.wp (ins (.mov (.reg (q rd)) (.reg (q rs))) :: rest) Q E s :=
  IselStep.x64_step_mov_cons hk

theorem audit_x64_mov_last [Host] {E : Int64 → MachineData → Prop}
    {rd rs : Reg64} {s : MachineData} {Q : MachineData → Prop}
    (hk : Q { s with regs := s.regs.set64 rd (s.regs.get64 rs) }) :
    _root_.Program.wp [ins (.mov (.reg (q rd)) (.reg (q rs)))] Q E s :=
  IselStep.x64_step_mov_last hk

end IselStepX64Audit

/-! ## 6. Logical Foundations Audit (`#print axioms`) -/

#print axioms audit_gpr
#print axioms audit_vec
#print axioms audit_frame
#print axioms audit_label_clean
#print axioms audit_x64_to_isa
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
#print axioms audit_x64_frame_eq
#print axioms audit_x64_upd_all
#print axioms audit_x64_wp_dir
#print axioms audit_x64_mov_cons
#print axioms audit_x64_mov_last

end CompilerAuditX64
