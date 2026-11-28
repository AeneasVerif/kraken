module

public import LeanQbe.T.MainCertSlices
public import LeanQbe.T.MainCertInline
public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.Amd64.KissatAbi
public import LeanQbe.T.Examples.Kissat.KissatCertCommon
public import LeanQbe.T.Logic.MemLemmas
public import LeanQbeTest.T.Common.Fixtures
public import Std.Sat.CNF
import LeanQbe.T.FlatLemmas
import Kraken.Mem
import Kraken.Separation
public meta import Lean
public meta import LeanQbe.T.MainCertElab
public meta import LeanQbe.T.MainCertInline
public meta import LeanQbe.T.Amd64.Targ
public meta import LeanQbeTest.T.Common.Fixtures

/-!
# Additive Slice-List Certificate & Kissat ABI Common Tests (`MainCertSlicesTest`)

Tests all additive M8+ certificate infrastructure (`0` dual-arch co-imports, `std3` axioms only,
`0` `sorry`):
1. `LeanQbe.T.MainCertSlices`:
   - 3-slice uninlined `certMod` assembled via `ChunkSlice.ofCert` / `ChunkSlice.ofDrop` +
     `LinkedCert.ofChunkSlices` + `LinkedCert.toCompiled`, with arbitrary-`Host` `FnSpec` and
     closed `x64Init` execution (`rax = 75#64`, `cell64 0x1000#64 21#64`).
   - 2-slice materialized `inline_mod!` (`inlSrcMod`, `InlinePolicy.b5`) assembled via
     `LinkedCert.ofChunkSlices` + `LinkedCert.castModule` + `LinkedCert.toCompiled`, reaching
     `rax = 85#64`.
2. `LeanQbe.T.Examples.Kissat.KissatCertCommon` & `LeanQbe.T.Amd64.KissatAbi`:
   - Shared `m6NvWorkLen`, `m6NvPayload*`, `m6Nv_unsat_bound`, `sep_exists_eq`.
   - `x64KissatAbi` + `solve_of_abi_fnspec` lifting a compiled 5-arg `i64` entry to concrete
     SysV x64 `step1 Host.exe` `Eventually` and executing concretely on `x64Init`.
   - End-to-end definitional compatibility of `KissatUnsatPkg` + `x64KissatAbi` combinators
     (`module_fnspec_of_abi`, `solve_bytes_unsat_of_abi`, `unsat_correct_of_abi`,
     `unsat_nonvacuous_of_abi`, `run_unsat_of_abi`) against concrete SysV x64 signatures.
3. Single-line `< 115c` `#print axioms` audits (`std3` only).
-/

set_option autoImplicit false

section

namespace LeanQbeTest.T.MainCertSlicesTest

open Std Std.ExtHashMap Std.Sat
open LeanQbe.T LeanQbe.T.Amd64 Kraken
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec hiding sep_exists_eq
open LeanQbe.T.Examples.Kissat.KissatCertCommon
open LeanQbeTest.T.Common.Fixtures

theorem certMod_legalSig : LegalSigAll x64LegalTarget certMod.fns :=
  legalSigAll_of_check (by t_kernel_rfl)

theorem certMod_fns_len : certMod.fns.length = 6 := rfl

/-! ## 1. 3-Slice `LinkedCert.ofChunkSlices` & `LinkedCert.toCompiled` on `certMod` -/

compile_linked_chunks! certS1
  x64Target x64Layout x64LegalTarget x64LabelClean slice1Mod 2

eval_prefix_ext! extS1 x64Target x64LegalTarget (autoFns.take 2)

compile_linked_chunks! certS2
  x64Target x64Layout x64LegalTarget x64LabelClean slice2Mod 2 (ext := extS1)

eval_prefix_ext! extS2 x64Target x64LegalTarget (autoFns.take 4)

compile_linked_chunks! certS3
  x64Target x64Layout x64LegalTarget x64LabelClean slice3Mod 2 (ext := extS2)

noncomputable def sl1 :
    ChunkSlice x64Target x64LegalTarget [] 0 2048 certMod.fns :=
  ChunkSlice.ofCert 0 2 certS1 rfl

noncomputable def sl2 :
    ChunkSlice x64Target x64LegalTarget [] 0 2048 certMod.fns :=
  ChunkSlice.ofCert 2 2 certS2 rfl

noncomputable def sl3 :
    ChunkSlice x64Target x64LegalTarget [] 0 2048 certMod.fns :=
  ChunkSlice.ofDrop 4 2 certS3 certMod_fns_len (by decide) rfl

noncomputable def certModSlices :
    List (ChunkSlice x64Target x64LegalTarget [] 0 2048 certMod.fns) :=
  [sl1, sl2, sl3]

theorem certModSlices_link :
    checkLinkList x64Layout [] (ChunkSlice.allChunks certModSlices) = true := by
  t_kernel_rfl

noncomputable def certSlices :
    LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean certMod [] [] 0 2048 :=
  LinkedCert.ofChunkSlices certModSlices certMod_fns_len (by decide) certModSlices_link

noncomputable def certCompiled := certSlices.toCompiled

theorem certSlices_chunks : certSlices.numChunks = 3 := rfl

theorem certSlices_fnspec [hh : Host] (k₀ : Nat)
    (hc : certSlices.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {f : Fn} (hf : f ∈ certMod.fns) :
    x64Target.Defined hh f.name ∧
      x64Target.FnSpec hh f.name (certΓ f.name f.as f.rs) (certSlices.bound f.name) 0 :=
  certSlices.fnSpec_noExit_of_legalSigAll hh certΓ k₀ hc hu
    certMod_acyclic certMod_wf certMod_legalSig certMod_wp hf (certΓ_noExit f.name f.as f.rs)

def mainMemBytes : List UInt8 := bytes64 [10#64]

private theorem mainMemBytes_len : mainMemBytes.length ≤ 8192 := by
  simp [mainMemBytes, bytes64_length]

private theorem mainMemBytes_cell :
    (cell64 0x1000#64 10#64 ⋆ emp) (mainMemBytes.At 0x1000#64) := by
  have h := array64_bytes 0x1000#64 [10#64] (by decide)
  simpa [mainMemBytes] using h

theorem x64_run_main_slices :
    Eventually (x64Target.mach.step certSlices.host)
      (fun st => x64Target.mach.pc st = x64Init.ra0 ∧
        x64Target.mach.getGpr (x64Target.mach.data st) x64Init.ret0 = mainVal 10#64 5#64 ∧
        (x64Target.mach.mem (x64Target.mach.data st) =⋆
          (cell64 0x1000#64 (pairMem 10#64 5#64) ⋆ emp) ⋆
          x64Target.Exit x64Init.sp0 (certSlices.bound "main_entry") ⋆ emp))
      (x64Target.mach.mkState
        (x64Init.initState (as := [i64, i64]) (certSlices.bound "main_entry") mainMemBytes
          (0x1000#64, 5#64, ()))
        (x64Target.mach.labelAddr certSlices.host "main_entry")) := by
  refine certSlices.eventually_ret1_sep_i64 x64Init certΓ
    certMod_acyclic certMod_wf certMod_wp (f := fnMain) fnMain_mem_certMod rfl rfl rfl
    (certΓ_noExit "main_entry" [i64, i64] [i64])
    mainMemBytes (0x1000#64, 5#64, ()) (mainVal 10#64 5#64)
    (cell64 0x1000#64 (pairMem 10#64 5#64) ⋆ emp) mainMemBytes_len rfl
    (Q := fun rets m' => rets = (mainVal 10#64 5#64, ()) ∧
      (cell64 0x1000#64 (pairMem 10#64 5#64) ⋆ emp) m') ?_
    (fun _ _ h => h) (by decide)
  refine ⟨10#64, emp, mainMemBytes_cell, fun m' hm' => ⟨rfl, ?_⟩⟩
  simpa using hm'

/-! ## 2. 2-Slice Inlined `inline_mod!` + `ofChunkSlices` + `castModule` -/

inline_mod! inlModS inlSrcMod InlinePolicy.b5

theorem inlSrcMod_legalSig : LegalSigAll x64LegalTarget inlSrcMod.fns :=
  legalSigAll_of_check (by t_kernel_rfl)

theorem inlModS_fns_len : inlModS.fns.length = 4 := rfl

noncomputable abbrev inlSlice1Mod : Module := { fns := inlModS.fns.take 2 }
noncomputable abbrev inlSlice2Mod : Module := { fns := inlModS.fns.drop 2 }

compile_linked_chunks! inlC1
  x64Target x64Layout x64LegalTarget x64LabelClean inlSlice1Mod 1

eval_prefix_ext! extInlS1 x64Target x64LegalTarget (inlModS.fns.take 2)

compile_linked_chunks! inlC2
  x64Target x64Layout x64LegalTarget x64LabelClean inlSlice2Mod 1 (ext := extInlS1)

noncomputable def iSl1 :
    ChunkSlice x64Target x64LegalTarget [] 0 2048 inlModS.fns :=
  ChunkSlice.ofCert 0 2 inlC1 rfl

noncomputable def iSl2 :
    ChunkSlice x64Target x64LegalTarget [] 0 2048 inlModS.fns :=
  ChunkSlice.ofDrop 2 2 inlC2 inlModS_fns_len (by decide) rfl

noncomputable def inlSlices :
    List (ChunkSlice x64Target x64LegalTarget [] 0 2048 inlModS.fns) :=
  [iSl1, iSl2]

theorem inlSlices_link :
    checkLinkList x64Layout [] (ChunkSlice.allChunks inlSlices) = true := by
  t_kernel_rfl

noncomputable def certInlMat :
    LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean inlModS [] [] 0 2048 :=
  LinkedCert.ofChunkSlices inlSlices inlModS_fns_len (by decide) inlSlices_link

noncomputable def certInl :
    LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean
      (inlSrcMod.optInlinePolicy InlinePolicy.b5) [] [] 0 2048 :=
  certInlMat.castModule inlModS.eq

noncomputable def certInlCompiled := certInl.toCompiled

def inlMemBytes : List UInt8 := bytes64 [20#64]

private theorem inlMemBytes_len : inlMemBytes.length ≤ 8192 := by
  simp [inlMemBytes, bytes64_length]

private theorem inlMemBytes_cell :
    (cell64 0x1000#64 20#64 ⋆ emp) (inlMemBytes.At 0x1000#64) := by
  have h := array64_bytes 0x1000#64 [20#64] (by decide)
  simpa [inlMemBytes] using h

theorem x64_run_inl_slices :
    Eventually (x64Target.mach.step certInl.host)
      (fun st => x64Target.mach.pc st = x64Init.ra0 ∧
        x64Target.mach.getGpr (x64Target.mach.data st) x64Init.ret0 = 85#64 ∧
        (x64Target.mach.mem (x64Target.mach.data st) =⋆
          (cell64 0x1000#64 25#64 ⋆ emp) ⋆
          x64Target.Exit x64Init.sp0 (certInl.bound "entry") ⋆ emp))
      (x64Target.mach.mkState
        (x64Init.initState (as := [i64, i64]) (certInl.bound "entry") inlMemBytes
          (0x1000#64, 5#64, ()))
        (x64Target.mach.labelAddr certInl.host "entry")) := by
  refine certInl.eventually_ret1_sep_i64_of_legalSigAll_optInlinePolicy x64Init inlΓ
    inlSrcMod_modOk inlSrcMod_legalSig (f := fnEntryInl) (by simp [inlSrcMod]) rfl
    (inlΓ_noExit "entry" [i64, i64] [i64]) inlMemBytes (0x1000#64, 5#64, ()) 85#64
    (cell64 0x1000#64 25#64 ⋆ emp) inlMemBytes_len rfl
    (Q := fun rets m' => rets = (85#64, ()) ∧ (cell64 0x1000#64 25#64 ⋆ emp) m') ?_
    (fun _ _ h => h) (by decide)
  refine ⟨20#64, emp, inlMemBytes_cell, fun m' hm' => ⟨rfl, ?_⟩⟩
  simpa using hm'

/-! ## 3. `KissatCertCommon` & `x64KissatAbi` End-to-End Integration -/

theorem m6NvWorkLen_val : m6NvWorkLen = 6144 := rfl

def fnArg5 : Fn :=
  ⟨"solve5_test", [i64, i64, i64, i64, i64], [i64], fun _ _ (a, b, c, d, e, ()) =>
    .let_ ⟨.add i64, (.var a, .var b, ())⟩ fun (s1, ()) =>
    .let_ ⟨.add i64, (.var s1, .var c, ())⟩ fun (s2, ()) =>
    .let_ ⟨.add i64, (.var s2, .var d, ())⟩ fun (s3, ()) =>
    .let_ ⟨.add i64, (.var s3, .var e, ())⟩ fun (s4, ()) =>
    .ret (.var s4, ())⟩

def modArg5 : Module := { fns := [fnArg5] }

theorem modArg5_acyclic : modArg5.checkAcyclic = true := by t_kernel_rfl

theorem fnArg5_wf : fnArg5.Wf := by t_wf_reify

theorem modArg5_wf : ∀ f ∈ modArg5.fns, f.Wf := by
  intro f hf
  cases hf with
  | head => exact fnArg5_wf
  | tail _ h => cases h

theorem modArg5_legalSig : LegalSigAll x64LegalTarget modArg5.fns :=
  legalSigAll_of_check (by t_kernel_rfl)

def specArg5 : Spec [i64, i64, i64, i64, i64] [i64] :=
  fun (a, b, c, d, e, ()) m Q _ => Q (a + b + c + d + e, ()) m

def envArg5 : Env := fun nm as bs xs m Q _ =>
  match nm, as, bs with
  | "solve5_test", [.bits 64, .bits 64, .bits 64, .bits 64, .bits 64], [.bits 64] =>
    specArg5 xs m Q (fun _ _ _ _ => False)
  | _, _, _ => False

theorem modArg5_wp : ∀ f ∈ modArg5.fns, ∀ xs m Q X,
    envArg5 f.name f.as f.rs xs m Q X → Func.wp envArg5 f.body xs m Q X := by
  intro f hf xs m Q X h
  cases hf with
  | head =>
    rcases xs with ⟨a, b, c, d, e, ⟨⟩⟩
    dsimp only [envArg5] at h
    dsimp only [fnArg5, Func.wp, wp, Op.wp, op2, OpCode.wp, lift2, Ty.hasFloat, Arg.val, vals]
    exact h
  | tail _ h' => cases h'

compile_linked_chunks! certArg5Raw
  x64Target x64Layout x64LegalTarget x64LabelClean modArg5 1

theorem modArg5_len : modArg5.fns.length = 1 := rfl

noncomputable def arg5Slices :
    List (ChunkSlice x64Target x64LegalTarget [] 0 2048 modArg5.fns) :=
  [ChunkSlice.ofDrop 0 1 certArg5Raw modArg5_len (by decide) rfl]

theorem arg5Slices_link :
    checkLinkList x64Layout [] (ChunkSlice.allChunks arg5Slices) = true := by
  t_kernel_rfl

noncomputable def certArg5 :
    LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean modArg5 [] [] 0 2048 :=
  LinkedCert.ofChunkSlices arg5Slices modArg5_len (by decide) arg5Slices_link

theorem solve5_x64_of_abi [hh : Host] {b : Nat}
    {spec : Spec [i64, i64, i64, i64, i64] [i64]}
    (hfnspec : x64Target.FnSpec hh "solve5_test" spec b 0)
    (cnf_ptr cnf_len work_ptr work_len fuel : BitVec 64)
    {m : Mem 64} {Q : Post [i64]}
    (hspec : spec (cnf_ptr, cnf_len, work_ptr, work_len, fuel, ()) m Q
      (fun _ _ _ _ => False))
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hrdi : s.regs.get64 .rdi = cnf_ptr)
    (hrsi : s.regs.get64 .rsi = cnf_len)
    (hrdx : s.regs.get64 .rdx = work_ptr)
    (hrcx : s.regs.get64 .rcx = work_len)
    (hr8 : s.regs.get64 .r8 = fuel)
    (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hmem : s.dmem =⋆ Eq m ⋆
      (region (s.regs.get64 .rsp - BitVec.ofNat 64 b) b ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15],
          st.data.regs.get64 r = s.regs.get64 r) ∧
        st.data.regs.get64 .rsp = s.regs.get64 .rsp + 8#64 ∧
        ∃ m', Q (st.data.regs.get64 .rax, ()) m' ∧
          (st.data.dmem =⋆ Eq m' ⋆
            region (s.regs.get64 .rsp - BitVec.ofNat 64 b) (b + 8) ⋆ R))
      ⟨s, Labels.label "solve5_test"⟩ := by
  refine eventually_weaken _ _ _ _
    (fun _ ⟨hpc, ⟨hcal, hsp'⟩, m', hQ, hm'⟩ => ⟨hpc, hcal, hsp', m', hQ, hm'⟩)
    (solve_of_abi_fnspec x64KissatAbi hh "solve5_test" hfnspec
      cnf_ptr cnf_len work_ptr work_len fuel hspec s ra R
      ⟨hrdi, hrsi, hrdx, hrcx, hr8⟩ hsp hmem)

theorem abi_solve5_x64 [hh : Host] (k₀ : Nat)
    (hc : certArg5.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (a0 a1 a2 a3 a4 : BitVec 64)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hrdi : s.regs.get64 .rdi = a0)
    (hrsi : s.regs.get64 .rsi = a1)
    (hrdx : s.regs.get64 .rdx = a2)
    (hrcx : s.regs.get64 .rcx = a3)
    (hr8 : s.regs.get64 .r8 = a4)
    (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hmem : s.dmem =⋆ emp ⋆
      (region (s.regs.get64 .rsp - BitVec.ofNat 64 (certArg5.bound "solve5_test"))
          (certArg5.bound "solve5_test") ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        st.data.regs.get64 .rax = a0 + a1 + a2 + a3 + a4 ∧
        (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15],
          st.data.regs.get64 r = s.regs.get64 r) ∧
        st.data.regs.get64 .rsp = s.regs.get64 .rsp + 8#64)
      ⟨s, Labels.label "solve5_test"⟩ := by
  have hfn := (certArg5.fnSpec_noExit_of_legalSigAll hh envArg5 k₀ hc hu
    modArg5_acyclic modArg5_wf modArg5_legalSig modArg5_wp List.mem_cons_self
    (fun _ _ _ _ _ h => h)).2
  have hspec : envArg5 "solve5_test" [i64, i64, i64, i64, i64] [i64]
      (a0, a1, a2, a3, a4, ()) ∅
      (fun r m' => r.fst = a0 + a1 + a2 + a3 + a4 ∧ m' = ∅)
      (fun _ _ _ _ => False) :=
    ⟨rfl, rfl⟩
  have hmem' : s.dmem =⋆ Eq (∅ : Mem 64) ⋆
      (region (s.regs.get64 .rsp - BitVec.ofNat 64 (certArg5.bound "solve5_test"))
          (certArg5.bound "solve5_test") ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R := by
    rw [eq_empty_eq_emp]; exact hmem
  refine eventually_weaken _ _ _ _
    (fun _ ⟨hpc, hcal, hsp', m', ⟨hr, _⟩, _⟩ => ⟨hpc, hr, hcal, hsp'⟩)
    (solve5_x64_of_abi hfn a0 a1 a2 a3 a4 hspec s ra R hrdi hrsi hrdx hrcx hr8 hsp hmem')

/-! ## 4. Parametric `KissatUnsatPkg` Compatibility on `x64KissatAbi` -/

theorem pkg_module_fnspec (P : KissatUnsatPkg)
    (cert : LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean
      (P.mod.optInlinePolicy P.inlPolicy))
    (hleg : LegalSigAll x64LegalTarget P.mod.fns)
    [hh : Host] (k₀ : Nat)
    (hc : cert.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {f : Fn} (hf : f ∈ P.mod.fns) :
    x64Target.Defined hh f.name ∧
      x64Target.FnSpec hh f.name (P.env f.name f.as f.rs) (cert.bound f.name) 0 :=
  module_fnspec_of_abi x64KissatAbi P cert hleg hh k₀ hc hu hf

theorem pkg_solve_bytes_unsat_x64 (P : KissatUnsatPkg)
    (cert : LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean
      (P.mod.optInlinePolicy P.inlPolicy))
    (hleg : LegalSigAll x64LegalTarget P.mod.fns)
    [hh : Host] (k₀ : Nat)
    (hc : cert.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (cnf_ptr work_ptr fuel : BitVec 64) (cnfBytes : List UInt8) (wlen : Nat)
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hrdi : s.regs.get64 .rdi = cnf_ptr)
    (hrsi : s.regs.get64 .rsi = BitVec.ofNat 64 cnfBytes.length)
    (hrdx : s.regs.get64 .rdx = work_ptr)
    (hrcx : s.regs.get64 .rcx = BitVec.ofNat 64 wlen)
    (hr8 : s.regs.get64 .r8 = fuel)
    (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hmem : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
      (region (s.regs.get64 .rsp - BitVec.ofNat 64 (cert.bound P.entryFn))
          (cert.bound P.entryFn) ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) s.dmem) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        (st.data.regs.get64 .rax = 0#64 ∨
          st.data.regs.get64 .rax = 10#64 ∨
          st.data.regs.get64 .rax = 20#64) ∧
        (st.data.regs.get64 .rax = 20#64 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15],
          st.data.regs.get64 r = s.regs.get64 r) ∧
        st.data.regs.get64 .rsp = s.regs.get64 .rsp + 8#64 ∧
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
          region (s.regs.get64 .rsp - BitVec.ofNat 64 (cert.bound P.entryFn))
            ((cert.bound P.entryFn) + 8) ⋆ R) st.data.dmem)
      ⟨s, Labels.label P.entryFn⟩ := by
  refine eventually_weaken _ _ _ _
    (fun _ ⟨hpc, hdom, hu', ⟨hcal, hrsp⟩, hst⟩ => ⟨hpc, hdom, hu', hcal, hrsp, hst⟩)
    (solve_bytes_unsat_of_abi x64KissatAbi P cert hleg hh k₀ hc hu
      cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit s ra R
      ⟨hrdi, hrsi, hrdx, hrcx, hr8⟩ hsp hmem)

theorem pkg_unsat_correct_x64 (P : KissatUnsatPkg)
    (cert : LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean
      (P.mod.optInlinePolicy P.inlPolicy))
    (hleg : LegalSigAll x64LegalTarget P.mod.fns)
    [hh : Host] (k₀ : Nat)
    (hc : cert.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (cnf_ptr work_ptr fuel : BitVec 64) (cnfBytes : List UInt8) (wlen : Nat)
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hrdi : s.regs.get64 .rdi = cnf_ptr)
    (hrsi : s.regs.get64 .rsi = BitVec.ofNat 64 cnfBytes.length)
    (hrdx : s.regs.get64 .rdx = work_ptr)
    (hrcx : s.regs.get64 .rcx = BitVec.ofNat 64 wlen)
    (hr8 : s.regs.get64 .r8 = fuel)
    (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hmem : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
      (region (s.regs.get64 .rsp - BitVec.ofNat 64 (cert.bound P.entryFn))
          (cert.bound P.entryFn) ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) s.dmem) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        (st.data.regs.get64 .rax = 0#64 ∨
          st.data.regs.get64 .rax = 10#64 ∨
          st.data.regs.get64 .rax = 20#64) ∧
        (st.data.regs.get64 .rax = 20#64 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat))
      ⟨s, Labels.label P.entryFn⟩ :=
  unsat_correct_of_abi x64KissatAbi P cert hleg hh k₀ hc hu
    cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit s ra R
    ⟨hrdi, hrsi, hrdx, hrcx, hr8⟩ hsp hmem

theorem pkg_unsat_nv_x64 (P : KissatUnsatPkg)
    (cert : LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean
      (P.mod.optInlinePolicy P.inlPolicy))
    (hleg : LegalSigAll x64LegalTarget P.mod.fns)
    [hh : Host] (k₀ : Nat)
    (hc : cert.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique) :
    ∃ (cnf_ptr work_ptr fuel : BitVec 64) (cnfBytes : List UInt8) (wlen : Nat)
      (s : MachineData) (ra : Int64) (R : Mem 64 → Prop),
      cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧
      work_ptr.toNat + wlen < 2 ^ 64 ∧
      s.regs.get64 .rdi = cnf_ptr ∧
      s.regs.get64 .rsi = BitVec.ofNat 64 cnfBytes.length ∧
      s.regs.get64 .rdx = work_ptr ∧
      s.regs.get64 .rcx = BitVec.ofNat 64 wlen ∧
      s.regs.get64 .r8 = fuel ∧
      (s.regs.get64 .rsp + 8#64).toNat % 16 = 0 ∧
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
        (region (s.regs.get64 .rsp - BitVec.ofNat 64 (cert.bound P.entryFn))
            (cert.bound P.entryFn) ⋆
          cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) s.dmem ∧
      Eventually (step1 Host.exe)
        (fun st => st.pc = ra ∧ st.data.regs.get64 .rax = 20#64 ∧
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat)
        ⟨s, Labels.label P.entryFn⟩ := by
  obtain ⟨cp, wp, fu, cb, wl, s, ra, R, hcf, hwf,
    ⟨h0, h1, h2, h3, h4⟩, hsp, hdm, hev⟩ :=
    unsat_nonvacuous_of_abi x64KissatAbi P cert hleg hh k₀ hc hu
  exact ⟨cp, wp, fu, cb, wl, s, ra, R, hcf, hwf, h0, h1, h2, h3, h4, hsp, hdm, hev⟩

theorem pkg_run_unsat_x64 (P : KissatUnsatPkg)
    (cert : LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean
      (P.mod.optInlinePolicy P.inlPolicy))
    (hleg : LegalSigAll x64LegalTarget P.mod.fns) :
    Eventually (x64Target.mach.step cert.host)
      (fun st =>
        x64Target.mach.pc st = x64Init.ra0 ∧
        x64Target.mach.getGpr (x64Target.mach.data st) x64Init.ret0 = 20#64 ∧
        (x64Target.mach.mem (x64Target.mach.data st) =⋆
          (fun m' => nvM6UnsatCnf.Unsat ∧
            (bytes nvM6CnfPtr nvM6UnsatBytes ⋆
              region nvM6UnsatWorkPtr m6NvWorkLen ⋆ emp) m') ⋆
          x64Target.Exit x64Init.sp0 (cert.bound P.entryFn) ⋆ emp))
      (x64Target.mach.mkState
        (x64Init.initState (as := [i64, i64, i64, i64, i64])
          (cert.bound P.entryFn)
          (m6NvPayload nvM6UnsatBytes)
          (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
            nvM6UnsatWorkPtr, BitVec.ofNat 64 m6NvWorkLen, 16#64, ()))
        (x64Target.mach.labelAddr cert.host P.entryFn)) :=
  run_unsat_of_abi x64KissatAbi P cert hleg

/-! ## 5. Single-Line `< 115c` Standard-Axiom Audit -/

noncomputable abbrev ax_slices := certSlices
noncomputable abbrev ax_compiled := certCompiled
noncomputable abbrev ax_inl := certInl
noncomputable abbrev ax_inl_comp := certInlCompiled
abbrev ax_main_run := @x64_run_main_slices
abbrev ax_inl_run := @x64_run_inl_slices
abbrev ax_abi_solve5 := @abi_solve5_x64
abbrev ax_pkg_fnspec := @pkg_module_fnspec
abbrev ax_pkg_unsat := @pkg_solve_bytes_unsat_x64
abbrev ax_pkg_correct := @pkg_unsat_correct_x64
abbrev ax_pkg_nv := @pkg_unsat_nv_x64
abbrev ax_pkg_run := @pkg_run_unsat_x64
abbrev ax_m6nv_sep := @m6NvPayload_sep
abbrev ax_m6nv_bound := @m6Nv_unsat_bound
abbrev ax_sep_eq := @sep_exists_eq

#print axioms ax_slices
#print axioms ax_compiled
#print axioms ax_inl
#print axioms ax_inl_comp
#print axioms ax_main_run
#print axioms ax_inl_run
#print axioms ax_abi_solve5
#print axioms ax_pkg_fnspec
#print axioms ax_pkg_unsat
#print axioms ax_pkg_correct
#print axioms ax_pkg_nv
#print axioms ax_pkg_run
#print axioms ax_m6nv_sep
#print axioms ax_m6nv_bound
#print axioms ax_sep_eq

end LeanQbeTest.T.MainCertSlicesTest
