module

public import LeanQbe.T.MainCert
public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.FlatLemmas
import all Kraken.Mem
import all Kraken.Separation
public meta import Lean
public meta import LeanQbe.T.MainCert
public meta import LeanQbe.T.Amd64.Targ

/-!
# Chunked Native Compilation Certificate Test on SysV x64 (`MainCert`)

Tests `LeanQbe.T.MainCert` (`LinkedCert` + `compile_linked_chunks!`) end-to-end on `x64Target`
(`x64LegalTarget`, `x64Layout`, `x64LabelClean`, `x64Init`):
1. Compiles a 6-function callee-first module (`certMod`) across 3 chunks (`K = 2`) and 2 chunks
   (`K = 4`), exercising cross-chunk calls (chunk 2 → chunk 1 and chunk 2 → chunk 0), intra-chunk
   calls, and memory-mutating (`cell64`) + pure functions.
2. Tests optional clauses (`maxBound := 1024`, `exits := ["bail"]`, `nX := 32`), non-empty
   `ext := ...`, and empty-module compilation.
3. Proves whole-module arbitrary-`Host` `FnSpec` via `cert.fnSpec_noExit_of_legalSigAll`,
   linked-host `FnSpec` via `cert.fnSpec_host_of_legalSigAll` (`linkCompiledList_fnSpec`),
   concrete Kraken x64 `Eventually (step1 Host.exe)` via `x64_of_returns`, and closed execution
   witnesses via `cert.eventually_ret1_sep_i64` (`rax = 75`, `cell64 0x1000 21`).
4. Audits single-line `#print axioms` (`⊆ [propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbeTest.T.MainCertTest

open Std Std.ExtHashMap
open LeanQbe.T LeanQbe.T.Amd64 Kraken

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
  [(("inc", [i64, i64], [i64]), 8), (("scale", [i64], [i64]), 8)]

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

theorem certMod_legalSig : LegalSigAll x64LegalTarget certMod.fns :=
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

compile_linked_chunks! x64Cert3
  x64Target x64Layout x64LegalTarget x64LabelClean certMod 2

compile_linked_chunks! x64Cert2
  x64Target x64Layout x64LegalTarget x64LabelClean certMod 4

compile_linked_chunks! x64ExitCert
  x64Target x64Layout x64LegalTarget x64LabelClean exitMod 1
  (maxBound := 1024) (exits := ["bail"]) (nX := 32)

compile_linked_chunks! x64EmptyCert
  x64Target x64Layout x64LegalTarget x64LabelClean emptyMod 4

compile_linked_chunks! x64ExtCert
  x64Target x64Layout x64LegalTarget x64LabelClean extSubMod 1
  (ext := extCalleesSample)

compile_linked_chunks! x64AdaptiveCert
  x64Target x64Layout x64LegalTarget x64LabelClean certMod 6 (maxDirs := 20)

compile_linked_chunks! x64Part1
  x64Target x64Layout x64LegalTarget x64LabelClean part1Mod 2

compile_linked_chunks! x64Part2
  x64Target x64Layout x64LegalTarget x64LabelClean part2Mod 2
  (ext := x64Part1.exportedExt)

def x64AppendedCert :
    LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean certMod [] [] 0
      (Nat.max 2048 2048) :=
  x64Part1.append x64Part2 rfl (by t_kernel_rfl)

theorem x64Cert3_chunks : x64Cert3.numChunks = 3 := rfl
theorem x64Cert2_chunks : x64Cert2.numChunks = 2 := rfl
theorem x64ExitCert_chunks : x64ExitCert.numChunks = 2 := rfl
theorem x64EmptyCert_chunks : x64EmptyCert.numChunks = 1 := rfl
theorem x64ExtCert_chunks : x64ExtCert.numChunks = 2 := rfl
theorem x64Appended_chunks : x64AppendedCert.numChunks = 4 := rfl
theorem x64Adaptive_ge : 2 ≤ x64AdaptiveCert.numChunks := by decide

theorem x64Cert3_bound_le : x64Cert3.bound "main_entry" ≤ 2048 :=
  x64Cert3.bound_le_max "main_entry"

/-! ## 3. Whole-module `FnSpec` & concrete Kraken x64 `Eventually` theorems -/

/-- Arbitrary-`Host` whole-module `FnSpec` via `LinkedCert.fnSpec_noExit_of_legalSigAll`. -/
theorem x64_module_fnspec [hh : Host] (k₀ : Nat)
    (hc : x64Cert3.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {f : Fn} (hf : f ∈ certMod.fns) :
    x64Target.Defined hh f.name ∧
      x64Target.FnSpec hh f.name (certΓ f.name f.as f.rs) (x64Cert3.bound f.name) 0 :=
  x64Cert3.fnSpec_noExit_of_legalSigAll hh certΓ k₀ hc hu
    certMod_acyclic certMod_wf certMod_legalSig certMod_wp hf (certΓ_noExit f.name f.as f.rs)

/-- Linked-host `FnSpec` for `main_entry` via `linkCompiledList_fnSpec`. -/
theorem x64_main_fnSpec :
    x64Target.Defined x64Cert3.host "main_entry" ∧
      x64Target.FnSpec x64Cert3.host "main_entry" mainSpec
        (x64Cert3.bound "main_entry") 0 :=
  x64Cert3.fnSpec_host_of_legalSigAll certΓ certMod_acyclic certMod_wf certMod_legalSig
    certMod_wp (f := fnMain) (by simp [certMod]) (certΓ_noExit "main_entry" [i64, i64] [i64])

/-- Arbitrary-`Host` concrete Kraken x64 `Eventually (step1 Host.exe)` theorem for `main_entry`. -/
theorem x64_main_eventually [hh : Host] (k₀ : Nat)
    (hc : x64Cert3.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (p v d : BitVec 64) (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hrdi : s.regs.get64 .rdi = p) (hrsi : s.regs.get64 .rsi = d)
    (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hmem : s.dmem =⋆ cell64 p v ⋆
      (region (s.regs.get64 .rsp - BitVec.ofNat 64 (x64Cert3.bound "main_entry"))
          (x64Cert3.bound "main_entry") ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st =>
        st.pc = ra ∧
        st.data.regs.get64 .rax = mainVal v d ∧
        (st.data.dmem =⋆ cell64 p (pairMem v d) ⋆
          region (s.regs.get64 .rsp - BitVec.ofNat 64 (x64Cert3.bound "main_entry"))
            (x64Cert3.bound "main_entry" + 8) ⋆ R))
      ⟨s, Labels.label "main_entry"⟩ := by
  obtain ⟨mf, mR, hu1, hd1, ⟨m, f, hu2, hd2, hm, hf⟩, hmR⟩ := hmem
  have hmEq : s.dmem =⋆ Eq m ⋆
      (region (s.regs.get64 .rsp - BitVec.ofNat 64 (x64Cert3.bound "main_entry"))
          (x64Cert3.bound "main_entry") ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R :=
    ⟨mf, mR, hu1, hd1, ⟨m, f, hu2, hd2, rfl, hf⟩, hmR⟩
  have hfn : x64Target.FnSpec hh "main_entry" mainSpec (x64Cert3.bound "main_entry") 0 :=
    (x64_module_fnspec k₀ hc hu (f := fnMain) (by simp [certMod])).2
  have hargs : x64Target.ArgsIn (as := [i64, i64]) (p, d, ()) s :=
    ⟨_, rfl, .cons ⟨by decide, by simpa using hrdi⟩ (.cons ⟨by decide, by simpa using hrsi⟩ .nil)⟩
  have hspec : mainSpec (p, d, ()) m
      (fun (r, ()) m' => r = mainVal v d ∧ cell64 p (pairMem v d) m') (fun _ _ _ _ => False) :=
    ⟨v, emp, by rwa [sep_emp], fun _ hm' => ⟨rfl, by rwa [sep_emp] at hm'⟩⟩
  refine eventually_weaken _ _ _ _ ?_ (x64_of_returns hfn hspec s ra R hargs hsp hmEq)
  rintro st ⟨hpc, _, _, ⟨r, ⟨⟩⟩, m', ⟨rfl, hm'⟩, hrets, hmem'⟩
  exact ⟨hpc, x64Init.retsIn_singleton (mainVal v d) st.data hrets,
    sep_mono (fun _ => sep_mono (fun _ e => e ▸ hm')) hmem'⟩

def initMemBytes : List UInt8 := bytes64 [10#64]

private theorem initMemBytes_len : initMemBytes.length ≤ 8192 := by
  simp [initMemBytes, bytes64_length]

private theorem initMemBytes_cell : (cell64 0x1000#64 10#64 ⋆ emp) (initMemBytes.At 0x1000#64) := by
  have h := array64_bytes 0x1000#64 [10#64] (by decide)
  simpa [initMemBytes, array64, array] using h

/-- Concrete end-to-end x64 execution witness on `x64Cert3.host` via `eventually_ret1_sep_i64`
(`main_entry(0x1000, 5) = 75`, updating `cell64 0x1000 21`). -/
theorem x64_run_main_sep :
    Eventually (x64Target.mach.step x64Cert3.host)
      (fun st => x64Target.mach.pc st = x64Init.ra0 ∧
        x64Target.mach.getGpr (x64Target.mach.data st) x64Init.ret0 = 75#64 ∧
        (x64Target.mach.mem (x64Target.mach.data st) =⋆
          (cell64 0x1000#64 21#64 ⋆ emp) ⋆
          x64Target.Exit x64Init.sp0 (x64Cert3.bound "main_entry") ⋆ emp))
      (x64Target.mach.mkState
        (x64Init.initState (as := [i64, i64]) (x64Cert3.bound "main_entry") initMemBytes
          (0x1000#64, 5#64, ()))
        (x64Target.mach.labelAddr x64Cert3.host "main_entry")) := by
  refine x64Cert3.eventually_ret1_sep_i64 x64Init certΓ certMod_acyclic certMod_wf certMod_wp
    (f := fnMain) (by simp [certMod]) rfl rfl rfl (certΓ_noExit "main_entry" [i64, i64] [i64])
    initMemBytes (0x1000#64, 5#64, ()) 75#64 (cell64 0x1000#64 21#64 ⋆ emp) initMemBytes_len rfl
    (Q := fun rets m' => rets = (75#64, ()) ∧ (cell64 0x1000#64 21#64 ⋆ emp) m') ?_
    (fun _ _ h => h) (by decide)
  refine ⟨10#64, emp, initMemBytes_cell, fun m' hm' => ⟨rfl, ?_⟩⟩
  simpa [pairMem] using hm'

/-- Concrete 2-chunk (`K = 4`) x64 execution witness on `x64Cert2.host`. -/
theorem x64_cert2_run_sep :
    Eventually (x64Target.mach.step x64Cert2.host)
      (fun st => x64Target.mach.pc st = x64Init.ra0 ∧
        x64Target.mach.getGpr (x64Target.mach.data st) x64Init.ret0 = 75#64 ∧
        (x64Target.mach.mem (x64Target.mach.data st) =⋆
          (cell64 0x1000#64 21#64 ⋆ emp) ⋆
          x64Target.Exit x64Init.sp0 (x64Cert2.bound "main_entry") ⋆ emp))
      (x64Target.mach.mkState
        (x64Init.initState (as := [i64, i64]) (x64Cert2.bound "main_entry") initMemBytes
          (0x1000#64, 5#64, ()))
        (x64Target.mach.labelAddr x64Cert2.host "main_entry")) := by
  refine x64Cert2.eventually_ret1_sep_i64 x64Init certΓ certMod_acyclic certMod_wf certMod_wp
    (f := fnMain) (by simp [certMod]) rfl rfl rfl (certΓ_noExit "main_entry" [i64, i64] [i64])
    initMemBytes (0x1000#64, 5#64, ()) 75#64 (cell64 0x1000#64 21#64 ⋆ emp) initMemBytes_len rfl
    (Q := fun rets m' => rets = (75#64, ()) ∧ (cell64 0x1000#64 21#64 ⋆ emp) m') ?_
    (fun _ _ h => h) (by decide)
  refine ⟨10#64, emp, initMemBytes_cell, fun m' hm' => ⟨rfl, ?_⟩⟩
  simpa [pairMem] using hm'

/-- Concrete appended-cert (`LinkedCert.append`) x64 execution witness on `x64AppendedCert.host`. -/
theorem x64_appended_run_sep :
    Eventually (x64Target.mach.step x64AppendedCert.host)
      (fun st => x64Target.mach.pc st = x64Init.ra0 ∧
        x64Target.mach.getGpr (x64Target.mach.data st) x64Init.ret0 = 75#64 ∧
        (x64Target.mach.mem (x64Target.mach.data st) =⋆
          (cell64 0x1000#64 21#64 ⋆ emp) ⋆
          x64Target.Exit x64Init.sp0 (x64AppendedCert.bound "main_entry") ⋆ emp))
      (x64Target.mach.mkState
        (x64Init.initState (as := [i64, i64]) (x64AppendedCert.bound "main_entry") initMemBytes
          (0x1000#64, 5#64, ()))
        (x64Target.mach.labelAddr x64AppendedCert.host "main_entry")) := by
  refine x64AppendedCert.eventually_ret1_sep_i64_of_legalSigAll x64Init certΓ certMod_acyclic
    certMod_wf certMod_legalSig certMod_wp (f := fnMain) (by simp [certMod]) rfl
    (certΓ_noExit "main_entry" [i64, i64] [i64]) initMemBytes (0x1000#64, 5#64, ()) 75#64
    (cell64 0x1000#64 21#64 ⋆ emp) initMemBytes_len rfl
    (Q := fun rets m' => rets = (75#64, ()) ∧ (cell64 0x1000#64 21#64 ⋆ emp) m') ?_
    (fun _ _ h => h) (by decide)
  refine ⟨10#64, emp, initMemBytes_cell, fun m' hm' => ⟨rfl, ?_⟩⟩
  simpa [pairMem] using hm'

/-! ## 4. Axiom Audit -/

#print axioms LeanQbe.T.LinkedCert.fnSpec
#print axioms LeanQbe.T.LinkedCert.fnSpec_linked
#print axioms LeanQbe.T.LinkedCert.fnSpec_host
#print axioms LeanQbe.T.LinkedCert.fnSpec_host_src
#print axioms LeanQbe.T.LinkedCert.fnSpec_noExit_id
#print axioms LeanQbe.T.LinkedCert.eventually_fnSpec
#print axioms LeanQbe.T.LinkedCert.eventually_ret1_sep_i64
#print axioms LeanQbe.T.LinkedCert.append
#print axioms x64Cert3
#print axioms x64Cert2
#print axioms x64ExitCert
#print axioms x64EmptyCert
#print axioms x64ExtCert
#print axioms x64AdaptiveCert
#print axioms x64AppendedCert
#print axioms x64_module_fnspec
#print axioms x64_main_fnSpec
#print axioms x64_main_eventually
#print axioms x64_run_main_sep
#print axioms x64_cert2_run_sep
#print axioms x64_appended_run_sep

end LeanQbeTest.T.MainCertTest
