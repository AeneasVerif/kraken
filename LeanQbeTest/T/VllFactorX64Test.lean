module

public import LeanQbe.T.Vll.FactorX64
public import LeanQbe.T.MainSplice
public import LeanQbe.T.Examples.Kissat.FullM7FidelityAssembly
public import LeanQbe.T.Examples.ChaCha
public import LeanQbeTest.T.Common.Fixtures
import LeanQbe.T.FlatLemmas
import LeanQbe.T.Examples.ChaChaProg
public meta import Lean
public meta import LeanQbe.T.MainSplice
public meta import LeanQbe.T.Main
public meta import LeanQbe.T.RegaDefs
public meta import LeanQbe.T.Rega
public meta import LeanQbe.T.Spill
public meta import LeanQbe.T.Amd64.Isel
public meta import LeanQbe.T.Amd64.IselVec
public meta import LeanQbe.T.Amd64.Frame
public meta import LeanQbe.T.Amd64.Isa
public meta import LeanQbe.T.Amd64.Targ
public meta import LeanQbe.T.Vll.X64
public meta import LeanQbe.T.Vll.AsmX64
public meta import LeanQbe.T.Vll.RegaInst0
public meta import LeanQbe.T.Vll.RegaInst
public meta import LeanQbe.T.Vll.FactorX640
public meta import LeanQbe.T.Vll.FactorX641
public meta import LeanQbe.T.Vll.FactorX642
public meta import LeanQbe.T.Vll.FactorX643
public meta import LeanQbe.T.Vll.FactorX644
public meta import LeanQbe.T.Vll.FactorX645
public meta import LeanQbe.T.Vll.FactorX646
public meta import LeanQbe.T.Vll.FactorX647
public meta import LeanQbe.T.Vll.FactorX64
public meta import LeanQbe.T.Examples.ChaCha
public meta import LeanQbe.T.Examples.ChaChaProg
public meta import LeanQbe.T.Examples.Kissat.FullM7FidelityAssembly
public meta import LeanQbeTest.T.Common.Fixtures

/-!
# Verification & `413`-Fn Parity Suite for `Vll.FactorX64` (`VllFactorX64Test`)

Tests:
1. `Unified.Factoring` (`FlatFn`, `x64FactoringOn`, `x64Factoring`), `sanitizeHints`, core
   `Instr x64Arch` vs `.native` emission on branching/fused/bitcount/`aluMem`/`cmpMem` IR and
   128-bit SIMD `ChaCha.chacha20Fn`.
2. Multi-function `certMod` (`6` functions: `inc`, `scale`, `step`, `pair`, `wrap`, `main_entry`):
   `vllX64_compileChecked_pair`, bidirectional `vllX64_compiled_to_x64` /
   `x64_compiled_to_vllX64`, state simulation (`vllX64_{argsIn,retsIn,restored}_iff`), dual-target
   `FnSpec` bridges (`vllX64_compiled_fnSpec_src`, `x64_compiled_fnSpec_to_vllX64`), and concrete
   `BedrockMach` `vllStep` / Kraken `step1 Host.exe` execution lifting (`vllX64_of_call`,
   `x64_of_returns`).
3. Full `413`-function parity across `FullM7FidelityAssembly.m7FidelityModule.fns`: verifies
   `hintsNoRsp`, `Rega.lowerFn`, and `compileFn` (`asmX64List ∘ vllX64Target = x64Target`),
   confirming `413/413` `0`-directive / `0`-byte diff.
4. `#print axioms` audit (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.VllFactorX64Test

open Std Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.Unified
open LeanQbe.T.Amd64
open LeanQbe.T.Vll
open LeanQbe.T.Examples.ChaCha
open LeanQbe.T.Examples.Kissat.FullM7Fidelity
open LeanQbeTest.T.Common.Fixtures
open Kraken

/-! ## 1. `FlatFn`, `Unified.Factoring`, Core vs `.native`, & ChaCha SIMD Parity -/

@[expose] def isNativeInstr : Instr x64Arch → Bool
  | .native _ => true
  | _ => false

@[expose] def hasCoreInstr (xs : List (Instr x64Arch)) : Bool :=
  xs.any (fun i => !isNativeInstr i)

@[expose] def hasNativeInstr (xs : List (Instr x64Arch)) : Bool :=
  xs.any isNativeInstr

@[expose] def compilePairOk (f : Fn) : Bool :=
  let h := sanitizeHints (Fn.computeHints x64Isa x64LegalTarget f)
  match compileFn vllX64Target.toIsa x64LegalTarget h f,
        compileFn x64Target.toIsa x64LegalTarget h f with
  | .ok v, .ok x => asmX64List v == x && hasCoreInstr v
  | _, _ => false

@[expose] def flatBranchBody : TFlat [i64] :=
  .let_ (op2 (.cmp .slt i64) (.var 0) (.var 1))
    (.jnz (.var 0)
      (.let_ (op2 (.add i64) (.var 2) (.var 1)) (.ret (.var 0, ())))
      (.let_ (op2 (.sub i64) (.var 1) (.var 2)) (.ret (.var 0, ()))))

@[expose] def flatBranch : FlatFn := ⟨"flat_branch", [i64, i64], [i64], flatBranchBody⟩

@[expose] def fusedMixFn : Fn :=
  ⟨"fused_mix", [i64, i32], [i64], fun _ _ (p, x, ()) =>
    .load i64 (.var p) fun v =>
    .let_ (op1 (.sext 32 64) (.var x)) fun (sx, ()) =>
    .let_ (op2 (.add i64) (.var v) (.var sx)) fun (sum, ()) =>
    .let_ (op2 (.mul i64) (.var sum) (.imm 3#64)) fun (prod, ()) =>
    .let_ (op1 (.ctz 64) (.var prod)) fun (tz, ()) =>
    .let_ (op2 (.xor i64) (.var prod) (.var tz)) fun (out, ()) =>
    .let_ (op2 (.cmp .ult i64) (.var out) (.var v)) fun (cond, ()) =>
    .jnz (.var cond) (.ret (.var out, ())) (.ret (.var sum, ()))⟩

#guard ((x64Factoring x64LegalTarget).vll flatBranch).isOk
#guard compilePairOk flatBranch.toFn
#guard compilePairOk fusedMixFn
#guard compilePairOk chacha20Fn
#guard match compileFn vllX64Target.toIsa x64LegalTarget
    (sanitizeHints (Fn.computeHints x64Isa x64LegalTarget chacha20Fn)) chacha20Fn with
  | .ok v => hasCoreInstr v && hasNativeInstr v
  | .error _ => false
#guard match compileFn vllX64Target.toIsa x64LegalTarget
    (sanitizeHints (Fn.computeHints x64Isa x64LegalTarget fusedMixFn)) fusedMixFn with
  | .ok v => hasCoreInstr v && hasNativeInstr v
  | .error _ => false

splice_module_hints flatBranchHintsLit x64Target.toIsa x64LegalTarget [flatBranch.toFn]
splice_module_hints chacha20HintsLit x64Target.toIsa x64LegalTarget [chacha20Fn]

@[expose] def flatBranchHint : x64Isa.Hints :=
  sanitizeHints (flatBranchHintsLit.headD {})

@[expose] def chacha20Hint : x64Isa.Hints :=
  sanitizeHints (chacha20HintsLit.headD {})

theorem flatBranch_factor_eq :
    ((x64Factoring x64LegalTarget).vll flatBranch).map
        (·.flatMap (x64Factoring x64LegalTarget).asm) =
      (x64Factoring x64LegalTarget).direct flatBranch :=
  (x64Factoring x64LegalTarget).factor flatBranch

theorem flatBranch_noRsp : hintsNoRsp flatBranchHint = true :=
  sanitizeHints_noRsp _

theorem flatBranch_direct_eq :
    (x64Factoring x64LegalTarget (fun _ => flatBranchHint)).direct flatBranch =
      compileFn x64Target.toIsa x64LegalTarget flatBranchHint flatBranch.toFn :=
  x64Factoring_eq_direct x64LegalTarget (fun _ => flatBranchHint)
    flatBranch flatBranch_noRsp

theorem flatBranch_same_bytes (is : List (Instr x64Arch))
    (hv : compileFn vllX64Target.toIsa x64LegalTarget flatBranchHint flatBranch.toFn = .ok is) :
    compileFn x64Target.toIsa x64LegalTarget flatBranchHint flatBranch.toFn =
      .ok (asmX64List is) :=
  x64Factoring_same_bytes x64LegalTarget flatBranchHint flatBranch_noRsp flatBranch.toFn hv

theorem chacha20_noRsp : hintsNoRsp chacha20Hint = true :=
  sanitizeHints_noRsp _

theorem chacha20_factor_eq :
    (compileFn vllX64Target.toIsa x64LegalTarget chacha20Hint chacha20Fn).map asmX64List =
      compileFn x64Target.toIsa x64LegalTarget chacha20Hint chacha20Fn :=
  vllX64_compileFn_eq x64LegalTarget chacha20Hint chacha20_noRsp chacha20Fn

/-! ## 2. Multi-Function `certMod` (`Compiled`, `FnSpec`, & Concrete Lifting) -/

splice_module_hints certModRawHints x64Target.toIsa x64LegalTarget certMod.fns

@[expose] def certModHints : List x64Isa.Hints :=
  certModRawHints.map sanitizeHints

theorem certModHints_noRsp : certModHints.all hintsNoRsp = true := by
  t_kernel_rfl

theorem certMod_vll_check :
    checkCompile vllX64Target vllX64Layout x64LegalTarget [] [] 0
      certMod.fns certModHints 2048 = true := by
  t_kernel_rfl

theorem certMod_x64_small :
    x64ProgSmall
      (asmX64List (extractCode (compileModule vllX64Isa x64LegalTarget 8 [] [] 0
        certMod.fns certModHints)) ++ [].map x64Target.frame.label) = true := by
  t_kernel_rfl

theorem certMod_vll_small :
    vllX64ProgSmall
      (extractCode (compileModule vllX64Isa x64LegalTarget 8 [] [] 0
        certMod.fns certModHints) ++ [].map vllX64Isa.frame.label) = true := by
  t_kernel_rfl

@[expose] def certPair :=
  vllX64_compileChecked_pair (maxBound := 2048) certModHints_noRsp certMod_vll_check
    certMod_x64_small

theorem certPair_code_eq : certPair.2.1.code = asmX64List certPair.1.code :=
  certPair.2.2.1

theorem certMod_x64_labelsNodup :
    x64Layout.labelsNodup
      (asmX64List certPair.1.code ++ [].map x64Target.frame.label) = true := by
  t_kernel_rfl

theorem certPair_x64_small :
    x64ProgSmall (asmX64List certPair.1.code ++ [].map x64Target.frame.label) = true :=
  certMod_x64_small

@[expose] def certMxUpgraded :=
  vllX64_compiled_to_x64 certPair.1 certModHints_noRsp certMod_x64_labelsNodup certPair_x64_small

@[expose] def certMvFromX64 :=
  x64_compiled_to_vllX64 certPair.2.1 certModHints_noRsp certMod_vll_small

theorem certMod_supp :
    ∀ f ∈ certMod.fns, (f.earlyOpt).body.supportsSource x64LegalTarget = true :=
  supportsAll_to_forall (by t_kernel_rfl)

theorem certMod_compile_eq :
    (compile vllX64Target.toIsa x64LegalTarget certMod.fns certModHints).map asmX64List =
      compile x64Target.toIsa x64LegalTarget certMod.fns certModHints :=
  vllX64_compile_eq x64LegalTarget certMod.fns certModHints certModHints_noRsp

theorem certMod_dual_fnSpec :
    certPair.2.1.code = asmX64List certPair.1.code ∧
    (vllX64Target.Defined certPair.1.host fnMain.name ∧
      vllX64Target.FnSpec certPair.1.host fnMain.name
        (certΓ fnMain.name fnMain.as fnMain.rs) (certPair.1.bound fnMain.name) 0) ∧
    (x64Target.Defined certPair.2.1.host fnMain.name ∧
      x64Target.FnSpec certPair.2.1.host fnMain.name
        (certΓ fnMain.name fnMain.as fnMain.rs) (certPair.1.bound fnMain.name) 0) :=
  vllX64_compiled_fnSpec_src certModHints_noRsp certMod_vll_check certMod_x64_small
    certMod rfl certΓ certMod_acyclic certMod_wf certMod_supp certMod_wp
    fnMain_mem_certMod rfl rfl (certΓ_noExit fnMain.name fnMain.as fnMain.rs)

theorem certMod_x64_to_vll_fnSpec :
    asmX64List certMvFromX64.1.code = certPair.2.1.code ∧
    (vllX64Target.Defined certMvFromX64.1.host fnMain.name ∧
      vllX64Target.FnSpec certMvFromX64.1.host fnMain.name
        (certΓ fnMain.name fnMain.as fnMain.rs) (certMvFromX64.1.bound fnMain.name) 0) ∧
    (x64Target.Defined certPair.2.1.host fnMain.name ∧
      x64Target.FnSpec certPair.2.1.host fnMain.name
        (certΓ fnMain.name fnMain.as fnMain.rs) (certMvFromX64.1.bound fnMain.name) 0) :=
  x64_compiled_fnSpec_to_vllX64 certPair.2.1 certModHints_noRsp certMod_vll_small
    certMod rfl certΓ certMod_acyclic certMod_wf certMod_supp certMod_wp
    fnMain_mem_certMod rfl rfl (certΓ_noExit fnMain.name fnMain.as fnMain.rs)

theorem certMod_vll_main_eventually
    (p v d : BitVec 64) (m : Mem 64) (s : MachSt x64Arch) (ra : BitVec 64) (R : Mem 64 → Prop)
    (hm : (cell64 p v ⋆ emp) m) (hrdi : s.gpr .rdi = p) (hrsi : s.gpr .rsi = d)
    (hsp : (s.gpr .rsp + 8#64).toNat % 16 = 0)
    (hmem : s.mem =⋆ Eq m ⋆
      (region (s.gpr .rsp - BitVec.ofNat 64 (certPair.1.bound "main_entry"))
          (certPair.1.bound "main_entry") ⋆
        cell64 (s.gpr .rsp) ra) ⋆ R) :
    Eventually (vllStep certPair.1.host)
      (fun st =>
        st.pc = ra ∧
        st.data.gpr .rax = mainVal v d ∧
        (st.data.mem =⋆ cell64 p (pairMem v d) ⋆
          region (s.gpr .rsp - BitVec.ofNat 64 (certPair.1.bound "main_entry"))
            (certPair.1.bound "main_entry" + 8) ⋆ R))
      ⟨s, certPair.1.host.labelAddr "main_entry"⟩ := by
  have hfn : vllX64Target.FnSpec certPair.1.host "main_entry" mainSpec
      (certPair.1.bound "main_entry") 0 := certMod_dual_fnSpec.2.1.2
  have hargsV : x64Target.ArgsIn (as := [i64, i64]) (p, d, ()) (machToKraken s) :=
    ⟨_, rfl, .cons ⟨by decide, show (machToKraken s).regs.get64 .rdi = BitVec.setWidth 64 p from
        (regsOfFn_get64 s.gpr .rdi).trans hrdi⟩
      (.cons ⟨by decide, show (machToKraken s).regs.get64 .rsi = BitVec.setWidth 64 d from
        (regsOfFn_get64 s.gpr .rsi).trans hrsi⟩ .nil)⟩
  have hargs := (vllX64_argsIn_iff s (as := [i64, i64]) (p, d, ())).mpr hargsV
  have hspec : mainSpec (p, d, ()) m
      (fun (r, ()) m' => r = mainVal v d ∧ (cell64 p (pairMem v d) ⋆ emp) m')
      (fun _ _ _ _ => False) :=
    ⟨v, emp, hm, fun _ hm' => ⟨rfl, hm'⟩⟩
  refine eventually_weaken _ _ _ _ ?_
    (vllX64_of_call certPair.1.host hfn hspec s ra R hargs hsp hmem)
  rintro st (⟨hpc, _, _, ⟨r, ⟨⟩⟩, m', ⟨rfl, hm'⟩, hrets, hmem'⟩ | ⟨_, _, _, _, hX, _⟩)
  · have hretsX :=
      (vllX64_retsIn_iff st.data (bs := [i64]) (mainVal v d, ())).mp hrets
    have hrax := x64Init.retsIn_singleton (mainVal v d) (machToKraken st.data) hretsX
    have hrax' : st.data.gpr .rax = mainVal v d :=
      (regsOfFn_get64 st.data.gpr .rax).symm.trans hrax
    have hm'' : (cell64 p (pairMem v d) : Mem 64 → Prop) m' := by
      rwa [sep_emp] at hm'
    exact ⟨hpc, hrax', sep_mono (fun _ => sep_mono (fun _ e => by cases e; exact hm'')) hmem'⟩
  · exact hX.elim

theorem certMod_x64_main_eventually
    (p v d : BitVec 64) (m : Mem 64) (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hm : (cell64 p v ⋆ emp) m) (hrdi : s.regs.get64 .rdi = p) (hrsi : s.regs.get64 .rsi = d)
    (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hmem : s.dmem =⋆ Eq m ⋆
      (region (s.regs.get64 .rsp - BitVec.ofNat 64 (certPair.1.bound "main_entry"))
          (certPair.1.bound "main_entry") ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) :
    Eventually (x64Target.mach.step certPair.2.1.host)
      (fun st =>
        x64Target.mach.pc st = ra ∧
        (x64Target.mach.data st).regs.get64 .rax = mainVal v d ∧
        ((x64Target.mach.data st).dmem =⋆ cell64 p (pairMem v d) ⋆
          region (s.regs.get64 .rsp - BitVec.ofNat 64 (certPair.1.bound "main_entry"))
            (certPair.1.bound "main_entry" + 8) ⋆ R))
      (x64Target.mach.mkState s (x64Target.mach.labelAddr certPair.2.1.host "main_entry")) := by
  letI : Host := certPair.2.1.host
  have hfn : x64Target.FnSpec certPair.2.1.host "main_entry" mainSpec
      (certPair.1.bound "main_entry") 0 := certMod_dual_fnSpec.2.2.2
  have hargs : x64Target.ArgsIn (as := [i64, i64]) (p, d, ()) s :=
    ⟨_, rfl, .cons ⟨by decide, show s.regs.get64 .rdi = BitVec.setWidth 64 p from hrdi⟩
      (.cons ⟨by decide, show s.regs.get64 .rsi = BitVec.setWidth 64 d from hrsi⟩ .nil)⟩
  have hspec : mainSpec (p, d, ()) m
      (fun (r, ()) m' => r = mainVal v d ∧ (cell64 p (pairMem v d) ⋆ emp) m')
      (fun _ _ _ _ => False) :=
    ⟨v, emp, hm, fun _ hm' => ⟨rfl, hm'⟩⟩
  refine eventually_weaken _ _ _ _ ?_
    (x64_of_returns (hh := certPair.2.1.host) hfn hspec s ra R hargs hsp hmem)
  rintro st ⟨hpc, _, _, ⟨r, ⟨⟩⟩, m', ⟨rfl, hm'⟩, hrets, hmem'⟩
  have hm'' : (cell64 p (pairMem v d) : Mem 64 → Prop) m' := by
    rwa [sep_emp] at hm'
  exact ⟨hpc, x64Init.retsIn_singleton (mainVal v d) st.data hrets,
    sep_mono (fun _ => sep_mono (fun _ e => by cases e; exact hm'')) hmem'⟩

/-! ## 3. Full `413`-Function Kissat `m7FidelityModule` Byte-Exact Parity (`#guard` / `#eval`) -/

#guard m7FidelityModule.fns.length == 413

private def verifyM7Fidelity413 : IO Unit := do
  let fns := m7FidelityModule.fns
  if fns.length != 413 then
    throw <| IO.userError s!"expected 413 m7FidelityModule fns, got {fns.length}"
  let mut ok := 0
  let mut rawNoRsp := 0
  let mut lowerOk := 0
  let mut totalVll := 0
  let mut totalCore := 0
  let mut totalNative := 0
  let mut totalDirs := 0
  for f in fns do
    let hRaw := Fn.computeHints x64Isa x64LegalTarget f
    if hintsNoRsp hRaw then rawNoRsp := rawNoRsp + 1
    let h := sanitizeHints hRaw
    let mf := f.mid x64LegalTarget
    match Rega.lowerFn vllX64Target.toIsa h mf.ext mf,
          Rega.lowerFn x64Target.toIsa h mf.ext mf with
    | .ok lv, .ok lx =>
      if asmX64List lv == lx then lowerOk := lowerOk + 1
      else throw <| IO.userError s!"Rega.lowerFn diff on {f.name}"
    | _, _ => throw <| IO.userError s!"Rega.lowerFn error/mismatch on {f.name}"
    match compileFn vllX64Target.toIsa x64LegalTarget h f,
          compileFn x64Target.toIsa x64LegalTarget h f with
    | .ok cv, .ok cx =>
      let acv := asmX64List cv
      if acv == cx then
        ok := ok + 1
        let nNat := (cv.filter isNativeInstr).length
        totalVll := totalVll + cv.length
        totalCore := totalCore + (cv.length - nNat)
        totalNative := totalNative + nNat
        totalDirs := totalDirs + cx.length
      else
        throw <| IO.userError s!"compileFn directive/byte diff on {f.name}"
    | _, _ => throw <| IO.userError s!"compileFn error/mismatch on {f.name}"
  if ok != 413 || lowerOk != 413 || rawNoRsp != 413 then
    throw <| IO.userError
      s!"413-fn parity failed: compileFn={ok}, lowerFn={lowerOk}, rawNoRsp={rawNoRsp}"
  IO.println s!"OK (m7FidelityModule 413/413): compileFn=413/413, Rega.lowerFn=413/413, "
  IO.println s!"rawNoRsp=413/413, 0 directive/byte diff (vll={totalVll} "
  IO.println s!"[core={totalCore}, native={totalNative}], x64Dirs={totalDirs})"

#eval verifyM7Fidelity413

end LeanQbeTest.T.VllFactorX64Test

/-! ## 4. Standard-Axiom Audit (`⊆ [propext, Classical.choice, Quot.sound]`) -/

#print axioms LeanQbe.T.Vll.vllX64Policy
#print axioms LeanQbe.T.Vll.vllX64Target
#print axioms LeanQbe.T.Vll.x64FactoringOn
#print axioms LeanQbe.T.Vll.x64Factoring
#print axioms LeanQbe.T.Vll.x64Factoring_eq_direct
#print axioms LeanQbe.T.Vll.x64Factoring_flat_same_bytes
#print axioms LeanQbe.T.Vll.x64Factoring_flat_transport
#print axioms LeanQbe.T.Vll.x64Factoring_lowerFn
#print axioms LeanQbe.T.Vll.x64Factoring_same_bytes
#print axioms LeanQbe.T.Vll.x64Factoring_transport
#print axioms LeanQbe.T.Vll.x64Factoring_compile_ok
#print axioms LeanQbe.T.Vll.x64Factoring_compileModule_ok
#print axioms LeanQbe.T.Vll.fnNoSameExt_mid
#print axioms LeanQbe.T.Vll.vllX64_lowerFn_eq
#print axioms LeanQbe.T.Vll.vllX64_compileFn_eq
#print axioms LeanQbe.T.Vll.vllX64_compile_eq
#print axioms LeanQbe.T.Vll.vllX64_compileModule_eq
#print axioms LeanQbe.T.Vll.vllX64_compiled_to_x64
#print axioms LeanQbe.T.Vll.x64_compiled_to_vllX64
#print axioms LeanQbe.T.Vll.vllX64_compileChecked_pair
#print axioms LeanQbe.T.Vll.vllX64_compiled_fnSpec_pair
#print axioms LeanQbe.T.Vll.x64_compiled_fnSpec_to_vllX64
#print axioms LeanQbe.T.Vll.vllX64_compiled_fnSpec_src
#print axioms LeanQbe.T.Vll.vllX64_of_call
#print axioms LeanQbe.T.Vll.vllX64_argsIn_iff
#print axioms LeanQbe.T.Vll.vllX64_retsIn_iff
#print axioms LeanQbe.T.Vll.vllX64_restored_iff
#print axioms LeanQbeTest.T.VllFactorX64Test.flatBranch_factor_eq
#print axioms LeanQbeTest.T.VllFactorX64Test.chacha20_factor_eq
#print axioms LeanQbeTest.T.VllFactorX64Test.certMod_dual_fnSpec
#print axioms LeanQbeTest.T.VllFactorX64Test.certMod_x64_to_vll_fnSpec
#print axioms LeanQbeTest.T.VllFactorX64Test.certMod_vll_main_eventually
#print axioms LeanQbeTest.T.VllFactorX64Test.certMod_x64_main_eventually
