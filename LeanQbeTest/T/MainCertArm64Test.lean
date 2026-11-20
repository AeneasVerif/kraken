module

public import LeanQbe.T.MainCert
public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.Logic.MemLemmas
import all Kraken.Mem
import all Kraken.Separation
public meta import Lean
public meta import LeanQbe.T.MainCert
public meta import LeanQbe.T.Arm64.Targ

/-!
# Chunked Native Compilation Certificate Test on AAPCS64 Arm64 (`MainCert`)

Tests `LeanQbe.T.MainCert` (`LinkedCert` + `compile_linked_chunks!`) end-to-end on `armTarget`
(`armLegalTarget`, `armLayout`, `armLabelClean`, `armInit`):
1. Compiles a 6-function callee-first module (`certMod`) across 3 chunks (`K = 2`) and 2 chunks
   (`K = 4`), exercising cross-chunk calls (chunk 2 → chunk 1 and chunk 2 → chunk 0), intra-chunk
   calls, and memory-mutating (`cell64`) + pure functions.
2. Tests optional clauses (`maxBound := 1024`, `exits := ["bail"]`, `nX := 32`) and empty-module
   compilation.
3. Proves whole-module arbitrary-`Host` `FnSpec` via `cert.fnSpec_noExit_of_legalSigAll`,
   linked-host `FnSpec` via `cert.fnSpec_host_of_legalSigAll` (`linkCompiledList_fnSpec`),
   concrete Kraken Arm64 `Eventually (step1 Host.exe)` via `arm64_of_returns`, and closed execution
   witnesses via `cert.eventually_ret1_sep_i64` (`X0 = 75`, `cell64 0x1000 21`).
4. Audits single-line `#print axioms` (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbeTest.T.MainCertArm64Test

open Std Std.ExtHashMap
open LeanQbe.T LeanQbe.T.Arm64 Kraken

/-! ## 1. Six-function acyclic module and source specifications -/

def fnInc : Fn :=
  ⟨"inc", [i64, i64], [i64], fun _ _ (p, d, ()) =>
    .load i64 (.var p) fun v =>
    .let_ ⟨.add i64, (.var v, .var d, ())⟩ fun (s, ()) =>
    .store (.var s) (.var p) (.ret (.var s, ()))⟩

def fnScale : Fn :=
  ⟨"scale", [i64], [i64], fun _ _ (x, ()) =>
    .let_ ⟨.add i64, (.var x, .var x, ())⟩ fun (s, ()) =>
    .ret (.var s, ())⟩

def fnStep : Fn :=
  ⟨"step", [i64, i64], [i64], fun _ _ (p, d, ()) =>
    .call "inc" (as := [i64, i64]) (bs := [i64]) (.var p, .var d, ()) fun (r1, ()) =>
    .call "scale" (as := [i64]) (bs := [i64]) (.var d, ()) fun (r2, ()) =>
    .let_ ⟨.add i64, (.var r1, .var r2, ())⟩ fun (s, ()) =>
    .ret (.var s, ())⟩

def fnPair : Fn :=
  ⟨"pair", [i64, i64], [i64], fun _ _ (p, d, ()) =>
    .call "step" (as := [i64, i64]) (bs := [i64]) (.var p, .var d, ()) fun (r1, ()) =>
    .let_ ⟨.add i64, (.var d, .imm 1#64, ())⟩ fun (d1, ()) =>
    .call "step" (as := [i64, i64]) (bs := [i64]) (.var p, .var d1, ()) fun (r2, ()) =>
    .let_ ⟨.add i64, (.var r1, .var r2, ())⟩ fun (s, ()) =>
    .ret (.var s, ())⟩

def fnWrap : Fn :=
  ⟨"wrap", [i64, i64], [i64], fun _ _ (p, d, ()) =>
    .call "pair" (as := [i64, i64]) (bs := [i64]) (.var p, .var d, ()) fun (r, ()) =>
    .let_ ⟨.add i64, (.var r, .imm 7#64, ())⟩ fun (s, ()) =>
    .ret (.var s, ())⟩

def fnMain : Fn :=
  ⟨"main_entry", [i64, i64], [i64], fun _ _ (p, d, ()) =>
    .call "wrap" (as := [i64, i64]) (bs := [i64]) (.var p, .var d, ()) fun (r1, ()) =>
    .call "scale" (as := [i64]) (bs := [i64]) (.var d, ()) fun (r2, ()) =>
    .let_ ⟨.add i64, (.var r1, .var r2, ())⟩ fun (s, ()) =>
    .ret (.var s, ())⟩

def fnExit : Fn :=
  ⟨"guard_exit", [.bool, i64], [i64], fun _ _ (b, x, ()) =>
    .jnz (.var b) (.exit (as := [i64]) "bail" (.var x, ())) (.ret (.var x, ()))⟩

def certMod : Module :=
  { fns := [fnInc, fnScale, fnStep, fnPair, fnWrap, fnMain] }

def exitMod : Module :=
  { fns := [fnScale, fnExit], exits := ["bail"] }

def emptyMod : Module :=
  { fns := [] }

def extSubMod : Module :=
  { fns := [fnStep, fnPair] }

def extCalleesSample : List (SigEntry × Nat) :=
  [(("inc", [i64, i64], [i64]), 16), (("scale", [i64], [i64]), 16)]

def part1Mod : Module :=
  { fns := [fnInc, fnScale, fnStep] }

def part2Mod : Module :=
  { fns := [fnPair, fnWrap, fnMain] }

theorem certMod_acyclic : certMod.checkAcyclic = true := by t_kernel_rfl

theorem fnInc_wf : fnInc.Wf := by t_wf_reify
theorem fnScale_wf : fnScale.Wf := by t_wf_reify
theorem fnStep_wf : fnStep.Wf := by t_wf_reify
theorem fnPair_wf : fnPair.Wf := by t_wf_reify
theorem fnWrap_wf : fnWrap.Wf := by t_wf_reify
theorem fnMain_wf : fnMain.Wf := by t_wf_reify

theorem certMod_wf : ∀ f ∈ certMod.fns, f.Wf := by
  intro f hf
  simp only [certMod, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact fnInc_wf
  · exact fnScale_wf
  · exact fnStep_wf
  · exact fnPair_wf
  · exact fnWrap_wf
  · exact fnMain_wf

theorem certMod_legalSig : LegalSigAll armLegalTarget certMod.fns :=
  legalSigAll_of_check (by t_kernel_rfl)

def stepVal (v d : BitVec 64) : BitVec 64 := (v + d) + (d + d)
def pairMem (v d : BitVec 64) : BitVec 64 := (v + d) + (d + 1#64)
def pairVal (v d : BitVec 64) : BitVec 64 := stepVal v d + stepVal (v + d) (d + 1#64)
def wrapVal (v d : BitVec 64) : BitVec 64 := pairVal v d + 7#64
def mainVal (v d : BitVec 64) : BitVec 64 := wrapVal v d + (d + d)

def incSpec : Spec [i64, i64] [i64] := fun (p, d, ()) m Q _ =>
  ∃ v R, (m =⋆ cell64 p v ⋆ R) ∧ (∀ m', (m' =⋆ cell64 p (v + d) ⋆ R) → Q (v + d, ()) m')

def scaleSpec : Spec [i64] [i64] := fun (x, ()) m Q _ => Q (x + x, ()) m

def stepSpec : Spec [i64, i64] [i64] := fun (p, d, ()) m Q _ =>
  ∃ v R, (m =⋆ cell64 p v ⋆ R) ∧
    (∀ m', (m' =⋆ cell64 p (v + d) ⋆ R) → Q (stepVal v d, ()) m')

def pairSpec : Spec [i64, i64] [i64] := fun (p, d, ()) m Q _ =>
  ∃ v R, (m =⋆ cell64 p v ⋆ R) ∧
    (∀ m', (m' =⋆ cell64 p (pairMem v d) ⋆ R) → Q (pairVal v d, ()) m')

def wrapSpec : Spec [i64, i64] [i64] := fun (p, d, ()) m Q _ =>
  ∃ v R, (m =⋆ cell64 p v ⋆ R) ∧
    (∀ m', (m' =⋆ cell64 p (pairMem v d) ⋆ R) → Q (wrapVal v d, ()) m')

def mainSpec : Spec [i64, i64] [i64] := fun (p, d, ()) m Q _ =>
  ∃ v R, (m =⋆ cell64 p v ⋆ R) ∧
    (∀ m', (m' =⋆ cell64 p (pairMem v d) ⋆ R) → Q (mainVal v d, ()) m')

def certΓ : Env
  | "inc", [.bits 64, .bits 64], [.bits 64], xs, m, Q, X => incSpec xs m Q X
  | "scale", [.bits 64], [.bits 64], xs, m, Q, X => scaleSpec xs m Q X
  | "step", [.bits 64, .bits 64], [.bits 64], xs, m, Q, X => stepSpec xs m Q X
  | "pair", [.bits 64, .bits 64], [.bits 64], xs, m, Q, X => pairSpec xs m Q X
  | "wrap", [.bits 64, .bits 64], [.bits 64], xs, m, Q, X => wrapSpec xs m Q X
  | "main_entry", [.bits 64, .bits 64], [.bits 64], xs, m, Q, X => mainSpec xs m Q X
  | _, _, _, _, _, _, _ => False

theorem certΓ_noExit : ∀ f as bs xs m Q X X',
    certΓ f as bs xs m Q X → certΓ f as bs xs m Q X' := by
  intro f as bs xs m Q X X' h
  unfold certΓ at h ⊢
  split at h <;> exact h

private theorem inc_wp {xs : Tup Val [i64, i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (h : incSpec xs m Q X) : Func.wp certΓ fnInc.body xs m Q X := by
  rcases xs with ⟨p, d, ⟨⟩⟩
  rcases h with ⟨v, R, hm, hQ⟩
  dsimp only [Func.wp, fnInc, wp, Op.wp, op2, OpCode.wp, lift2, Ty.hasFloat, Arg.val, vals]
  refine ⟨v, loadVal_cell64 hm, ?_⟩
  obtain ⟨hok, hst⟩ := store_cell64 (v + d) hm
  exact ⟨hok, hQ _ hst⟩

private theorem scale_wp {xs : Tup Val [i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (h : scaleSpec xs m Q X) : Func.wp certΓ fnScale.body xs m Q X := by
  rcases xs with ⟨x, ⟨⟩⟩
  dsimp only [Func.wp, fnScale, wp, Op.wp, op2, OpCode.wp, lift2, Ty.hasFloat, Arg.val, vals]
  exact h

private theorem step_wp {xs : Tup Val [i64, i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (h : stepSpec xs m Q X) : Func.wp certΓ fnStep.body xs m Q X := by
  rcases xs with ⟨p, d, ⟨⟩⟩
  rcases h with ⟨v, R, hm, hQ⟩
  dsimp only [Func.wp, fnStep, wp, Op.wp, op2, OpCode.wp, lift2, Ty.hasFloat, Arg.val, vals]
  refine ⟨fun (r, _) m₁ => r = v + d ∧ (m₁ =⋆ cell64 p (v + d) ⋆ R), X,
    ⟨v, R, hm, fun m' hm' => ⟨rfl, hm'⟩⟩, ?_, fun _ _ _ _ hx => hx⟩
  rintro ⟨r₁, ⟨⟩⟩ m₁ ⟨rfl, hm₁⟩
  refine ⟨fun (r, _) m₂ => r = d + d ∧ m₂ = m₁, X, ⟨rfl, rfl⟩, ?_, fun _ _ _ _ hx => hx⟩
  rintro ⟨r₂, ⟨⟩⟩ m₂ ⟨rfl, rfl⟩
  exact hQ m₂ hm₁

private theorem pair_wp {xs : Tup Val [i64, i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (h : pairSpec xs m Q X) : Func.wp certΓ fnPair.body xs m Q X := by
  rcases xs with ⟨p, d, ⟨⟩⟩
  rcases h with ⟨v, R, hm, hQ⟩
  dsimp only [Func.wp, fnPair, wp, Op.wp, op2, OpCode.wp, lift2, Ty.hasFloat, Arg.val, vals]
  refine ⟨fun (r, _) m₁ => r = stepVal v d ∧ (m₁ =⋆ cell64 p (v + d) ⋆ R), X,
    ⟨v, R, hm, fun m' hm' => ⟨rfl, hm'⟩⟩, ?_, fun _ _ _ _ hx => hx⟩
  rintro ⟨r₁, ⟨⟩⟩ m₁ ⟨rfl, hm₁⟩
  refine ⟨fun (r, _) m₂ => r = stepVal (v + d) (d + 1#64) ∧ (m₂ =⋆ cell64 p (pairMem v d) ⋆ R),
    X, ⟨v + d, R, hm₁, fun m' hm' => ⟨rfl, hm'⟩⟩, ?_, fun _ _ _ _ hx => hx⟩
  rintro ⟨r₂, ⟨⟩⟩ m₂ ⟨rfl, hm₂⟩
  exact hQ m₂ hm₂

private theorem wrap_wp {xs : Tup Val [i64, i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (h : wrapSpec xs m Q X) : Func.wp certΓ fnWrap.body xs m Q X := by
  rcases xs with ⟨p, d, ⟨⟩⟩
  rcases h with ⟨v, R, hm, hQ⟩
  dsimp only [Func.wp, fnWrap, wp, Op.wp, op2, OpCode.wp, lift2, Ty.hasFloat, Arg.val, vals]
  refine ⟨fun (r, _) m₁ => r = pairVal v d ∧ (m₁ =⋆ cell64 p (pairMem v d) ⋆ R), X,
    ⟨v, R, hm, fun m' hm' => ⟨rfl, hm'⟩⟩, ?_, fun _ _ _ _ hx => hx⟩
  rintro ⟨r, ⟨⟩⟩ m₁ ⟨rfl, hm₁⟩
  exact hQ m₁ hm₁

private theorem main_wp {xs : Tup Val [i64, i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (h : mainSpec xs m Q X) : Func.wp certΓ fnMain.body xs m Q X := by
  rcases xs with ⟨p, d, ⟨⟩⟩
  rcases h with ⟨v, R, hm, hQ⟩
  dsimp only [Func.wp, fnMain, wp, Op.wp, op2, OpCode.wp, lift2, Ty.hasFloat, Arg.val, vals]
  refine ⟨fun (r, _) m₁ => r = wrapVal v d ∧ (m₁ =⋆ cell64 p (pairMem v d) ⋆ R), X,
    ⟨v, R, hm, fun m' hm' => ⟨rfl, hm'⟩⟩, ?_, fun _ _ _ _ hx => hx⟩
  rintro ⟨r₁, ⟨⟩⟩ m₁ ⟨rfl, hm₁⟩
  refine ⟨fun (r, _) m₂ => r = d + d ∧ m₂ = m₁, X, ⟨rfl, rfl⟩, ?_, fun _ _ _ _ hx => hx⟩
  rintro ⟨r₂, ⟨⟩⟩ m₂ ⟨rfl, rfl⟩
  exact hQ m₂ hm₁

theorem certMod_wp : ∀ f ∈ certMod.fns, ∀ xs m Q X,
    certΓ f.name f.as f.rs xs m Q X → Func.wp certΓ f.body xs m Q X := by
  intro f hf xs m Q X hΓ
  simp only [certMod, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact inc_wp hΓ
  · exact scale_wp hΓ
  · exact step_wp hΓ
  · exact pair_wp hΓ
  · exact wrap_wp hΓ
  · exact main_wp hΓ

/-! ## 2. Chunked native certificates via `compile_linked_chunks!` -/

compile_linked_chunks! armCert3
  armTarget armLayout armLegalTarget armLabelClean certMod 2

compile_linked_chunks! armCert2
  armTarget armLayout armLegalTarget armLabelClean certMod 4

compile_linked_chunks! armExitCert
  armTarget armLayout armLegalTarget armLabelClean exitMod 1
  (maxBound := 1024) (exits := ["bail"]) (nX := 32)

compile_linked_chunks! armEmptyCert
  armTarget armLayout armLegalTarget armLabelClean emptyMod 4

compile_linked_chunks! armExtCert
  armTarget armLayout armLegalTarget armLabelClean extSubMod 1
  (ext := extCalleesSample)

compile_linked_chunks! armAdaptiveCert
  armTarget armLayout armLegalTarget armLabelClean certMod 6 (maxDirs := 20)

compile_linked_chunks! armPart1
  armTarget armLayout armLegalTarget armLabelClean part1Mod 2

compile_linked_chunks! armPart2
  armTarget armLayout armLegalTarget armLabelClean part2Mod 2
  (ext := armPart1.exportedExt)

def armAppendedCert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean certMod [] [] 0
      (Nat.max 2048 2048) :=
  armPart1.append armPart2 rfl (by t_kernel_rfl)

theorem armCert3_chunks : armCert3.numChunks = 3 := rfl
theorem armCert2_chunks : armCert2.numChunks = 2 := rfl
theorem armExitCert_chunks : armExitCert.numChunks = 2 := rfl
theorem armEmptyCert_chunks : armEmptyCert.numChunks = 1 := rfl
theorem armExtCert_chunks : armExtCert.numChunks = 2 := rfl
theorem armAppended_chunks : armAppendedCert.numChunks = 4 := rfl
theorem armAdaptive_ge : 2 ≤ armAdaptiveCert.numChunks := by decide

theorem armCert3_bound_le : armCert3.bound "main_entry" ≤ 2048 :=
  armCert3.bound_le_max "main_entry"

/-! ## 3. Whole-module `FnSpec` & concrete Kraken Arm64 `Eventually` theorems -/

/-- Arbitrary-`Host` whole-module `FnSpec` via `LinkedCert.fnSpec_noExit_of_legalSigAll`. -/
theorem arm_module_fnspec [hh : Host] (k₀ : Nat)
    (hc : armCert3.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {f : Fn} (hf : f ∈ certMod.fns) :
    armTarget.Defined hh f.name ∧
      armTarget.FnSpec hh f.name (certΓ f.name f.as f.rs) (armCert3.bound f.name) 0 :=
  armCert3.fnSpec_noExit_of_legalSigAll hh certΓ k₀ hc hu
    certMod_acyclic certMod_wf certMod_legalSig certMod_wp hf (certΓ_noExit f.name f.as f.rs)

/-- Linked-host `FnSpec` for `main_entry` via `linkCompiledList_fnSpec`. -/
theorem arm_main_fnSpec :
    armTarget.Defined armCert3.host "main_entry" ∧
      armTarget.FnSpec armCert3.host "main_entry" mainSpec
        (armCert3.bound "main_entry") 0 :=
  armCert3.fnSpec_host_of_legalSigAll certΓ certMod_acyclic certMod_wf certMod_legalSig
    certMod_wp (f := fnMain) (by simp [certMod]) (certΓ_noExit "main_entry" [i64, i64] [i64])

/-- Arbitrary-`Host` concrete Kraken Arm64 `Eventually (step1 Host.exe)` theorem. -/
theorem arm_main_eventually [hh : Host] (k₀ : Nat)
    (hc : armCert3.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (p v d : BitVec 64) (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hx0 : (s.regs.getXReg .X0).toBitVec = p) (hx1 : (s.regs.getXReg .X1).toBitVec = d)
    (hra : s.regs.X30 = ra.toUInt64) (hsp : s.regs.SP.toNat % 16 = 0)
    (hmem : s.dmem =⋆ cell64 p v ⋆
      region (s.regs.SP.toBitVec - BitVec.ofNat 64 (armCert3.bound "main_entry"))
        (armCert3.bound "main_entry") ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        (st.data.regs.getXReg .X0).toBitVec = mainVal v d ∧
        (st.data.dmem =⋆ cell64 p (pairMem v d) ⋆
          region (s.regs.SP.toBitVec - BitVec.ofNat 64 (armCert3.bound "main_entry"))
            (armCert3.bound "main_entry") ⋆ R))
      ⟨s, Labels.label "main_entry"⟩ := by
  obtain ⟨mf, mR, hu1, hd1, ⟨m, f, hu2, hd2, hm, hf⟩, hmR⟩ := hmem
  have hmEq : s.dmem =⋆ Eq m ⋆
      region (s.regs.SP.toBitVec - BitVec.ofNat 64 (armCert3.bound "main_entry"))
        (armCert3.bound "main_entry") ⋆ R :=
    ⟨mf, mR, hu1, hd1, ⟨m, f, hu2, hd2, rfl, hf⟩, hmR⟩
  have hfn : armTarget.FnSpec hh "main_entry" mainSpec (armCert3.bound "main_entry") 0 :=
    (arm_module_fnspec k₀ hc hu (f := fnMain) (by simp [certMod])).2
  have hargs : armTarget.ArgsIn (as := [i64, i64]) (p, d, ()) s :=
    ⟨_, rfl,
      .cons ⟨by decide, by simpa [get_reg] using hx0⟩
        (.cons ⟨by decide, by simpa [get_reg] using hx1⟩ .nil)⟩
  have hspec : mainSpec (p, d, ()) m
      (fun (r, ()) m' => r = mainVal v d ∧ cell64 p (pairMem v d) m') (fun _ _ _ _ => False) :=
    ⟨v, emp, by rwa [sep_emp], fun _ hm' => ⟨rfl, by rwa [sep_emp] at hm'⟩⟩
  refine eventually_weaken _ _ _ _ ?_ (arm64_of_returns hfn hspec s ra R hargs hra hsp hmEq)
  rintro st ⟨hpc, _, _, ⟨r, ⟨⟩⟩, m', ⟨rfl, hm'⟩, hrets, hmem'⟩
  have hx0' : (st.data.regs.getXReg .X0).toBitVec = mainVal v d := by
    simpa [armInit, get_reg] using armInit.retsIn_singleton (mainVal v d) st.data hrets
  exact ⟨hpc, hx0', sep_mono (fun _ => sep_mono (fun _ e => e ▸ hm')) hmem'⟩

def initMemBytes : List UInt8 := bytes64 [10#64]

private theorem initMemBytes_len : initMemBytes.length ≤ 8192 := by
  simp [initMemBytes, bytes64_length]

private theorem initMemBytes_cell : (cell64 0x1000#64 10#64 ⋆ emp) (initMemBytes.At 0x1000#64) := by
  have h := array64_bytes 0x1000#64 [10#64] (by decide)
  simpa [initMemBytes, array64, array] using h

/-- Concrete end-to-end Arm64 execution witness on `armCert3.host` via `eventually_ret1_sep_i64`
(`main_entry(0x1000, 5) = 75`, updating `cell64 0x1000 21`). -/
theorem arm_run_main_sep :
    Eventually (armTarget.mach.step armCert3.host)
      (fun st => armTarget.mach.pc st = armInit.ra0 ∧
        armTarget.mach.getGpr (armTarget.mach.data st) armInit.ret0 = 75#64 ∧
        (armTarget.mach.mem (armTarget.mach.data st) =⋆
          (cell64 0x1000#64 21#64 ⋆ emp) ⋆
          armTarget.Exit armInit.sp0 (armCert3.bound "main_entry") ⋆ emp))
      (armTarget.mach.mkState
        (armInit.initState (as := [i64, i64]) (armCert3.bound "main_entry") initMemBytes
          (0x1000#64, 5#64, ()))
        (armTarget.mach.labelAddr armCert3.host "main_entry")) := by
  refine armCert3.eventually_ret1_sep_i64 armInit certΓ certMod_acyclic certMod_wf certMod_wp
    (f := fnMain) (by simp [certMod]) rfl rfl rfl (certΓ_noExit "main_entry" [i64, i64] [i64])
    initMemBytes (0x1000#64, 5#64, ()) 75#64 (cell64 0x1000#64 21#64 ⋆ emp) initMemBytes_len rfl
    (Q := fun rets m' => rets = (75#64, ()) ∧ (cell64 0x1000#64 21#64 ⋆ emp) m') ?_
    (fun _ _ h => h) (by decide)
  refine ⟨10#64, emp, initMemBytes_cell, fun m' hm' => ⟨rfl, ?_⟩⟩
  simpa [pairMem] using hm'

/-- Concrete 2-chunk (`K = 4`) Arm64 execution witness on `armCert2.host`. -/
theorem arm_cert2_run_sep :
    Eventually (armTarget.mach.step armCert2.host)
      (fun st => armTarget.mach.pc st = armInit.ra0 ∧
        armTarget.mach.getGpr (armTarget.mach.data st) armInit.ret0 = 75#64 ∧
        (armTarget.mach.mem (armTarget.mach.data st) =⋆
          (cell64 0x1000#64 21#64 ⋆ emp) ⋆
          armTarget.Exit armInit.sp0 (armCert2.bound "main_entry") ⋆ emp))
      (armTarget.mach.mkState
        (armInit.initState (as := [i64, i64]) (armCert2.bound "main_entry") initMemBytes
          (0x1000#64, 5#64, ()))
        (armTarget.mach.labelAddr armCert2.host "main_entry")) := by
  refine armCert2.eventually_ret1_sep_i64 armInit certΓ certMod_acyclic certMod_wf certMod_wp
    (f := fnMain) (by simp [certMod]) rfl rfl rfl (certΓ_noExit "main_entry" [i64, i64] [i64])
    initMemBytes (0x1000#64, 5#64, ()) 75#64 (cell64 0x1000#64 21#64 ⋆ emp) initMemBytes_len rfl
    (Q := fun rets m' => rets = (75#64, ()) ∧ (cell64 0x1000#64 21#64 ⋆ emp) m') ?_
    (fun _ _ h => h) (by decide)
  refine ⟨10#64, emp, initMemBytes_cell, fun m' hm' => ⟨rfl, ?_⟩⟩
  simpa [pairMem] using hm'

/-- Concrete appended-cert (`LinkedCert.append`) Arm64 execution witness on `armAppendedCert`. -/
theorem arm_appended_run_sep :
    Eventually (armTarget.mach.step armAppendedCert.host)
      (fun st => armTarget.mach.pc st = armInit.ra0 ∧
        armTarget.mach.getGpr (armTarget.mach.data st) armInit.ret0 = 75#64 ∧
        (armTarget.mach.mem (armTarget.mach.data st) =⋆
          (cell64 0x1000#64 21#64 ⋆ emp) ⋆
          armTarget.Exit armInit.sp0 (armAppendedCert.bound "main_entry") ⋆ emp))
      (armTarget.mach.mkState
        (armInit.initState (as := [i64, i64]) (armAppendedCert.bound "main_entry") initMemBytes
          (0x1000#64, 5#64, ()))
        (armTarget.mach.labelAddr armAppendedCert.host "main_entry")) := by
  refine armAppendedCert.eventually_ret1_sep_i64_of_legalSigAll armInit certΓ certMod_acyclic
    certMod_wf certMod_legalSig certMod_wp (f := fnMain) (by simp [certMod]) rfl
    (certΓ_noExit "main_entry" [i64, i64] [i64]) initMemBytes (0x1000#64, 5#64, ()) 75#64
    (cell64 0x1000#64 21#64 ⋆ emp) initMemBytes_len rfl
    (Q := fun rets m' => rets = (75#64, ()) ∧ (cell64 0x1000#64 21#64 ⋆ emp) m') ?_
    (fun _ _ h => h) (by decide)
  refine ⟨10#64, emp, initMemBytes_cell, fun m' hm' => ⟨rfl, ?_⟩⟩
  simpa [pairMem] using hm'

/-! ## 4. Axiom Audit -/

#print axioms armCert3
#print axioms armCert2
#print axioms armExitCert
#print axioms armEmptyCert
#print axioms armExtCert
#print axioms armAdaptiveCert
#print axioms armAppendedCert
#print axioms arm_module_fnspec
#print axioms arm_main_fnSpec
#print axioms arm_main_eventually
#print axioms arm_run_main_sep
#print axioms arm_cert2_run_sep
#print axioms arm_appended_run_sep

end LeanQbeTest.T.MainCertArm64Test
