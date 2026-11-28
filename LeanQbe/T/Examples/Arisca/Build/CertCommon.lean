/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.BenchmarkCertKit
public import LeanQbe.T.MainCertInlineProof
public import LeanQbe.T.Examples.Arisca.Src.Module
public import LeanQbe.T.Examples.Arisca.Build.Flat
import Kraken.Mem
import Kraken.Separation

/-!
# Arch-Free `LinkedCert` & `ModuleOk`-Parameterized Bridge for ARiSCA (`Arisca.Build.CertCommon`)

Centralizes architecture-independent slice assembly (`mkAriscaCertTree`, 5 slices covering all
`45` functions of `ariscaModule`), entry-function metadata (`arisca_check_bytes`), and
`BenchAbi` + `ModuleOk`-parameterized `FnSpec` / `Eventually` lifts ready for direct composition
once `M1-C` (`ModuleOk ariscaEnv ariscaModule`) lands.

Strictly arch-free (`0` `Amd64`/`Arm64`/`Kraken.X64`/`Kraken.AArch64`/`Kissat` imports, `<= std3`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Arisca.Build.CertCommon

open Std Std.ExtHashMap
open LeanQbe.T LeanQbe.T.BenchmarkCertKit Kraken
open LeanQbe.T.Examples.Arisca.Src
open LeanQbe.T.Examples.Arisca.Src.Module
open LeanQbe.T.Examples.Arisca.Build

/-! ## 1. Module & Entry Metadata (`arisca_check_bytes` at index 44) -/

theorem ariscaModule_fns_len : ariscaModule.fns.length = 45 := rfl

theorem ariscaModule_namesNodup : (ariscaModule.fns.map Fn.name).Nodup := by
  have h := ariscaModule_checkAcyclic
  simp only [Module.checkAcyclic, Bool.and_eq_true] at h
  have hnd := Module.namesNodup_of_checkNamesNodup h.1
  simpa [Module.namesNodup, Module.names, ariscaModule] using hnd

/-- Top-level C0 entry function `arisca_check_bytes` (`[i64 × 6] → [i64]`). -/
abbrev ariscaCheckBytesFn : Fn := Driver.arisca_check_bytes

theorem ariscaCheckBytesFn_at_44 :
    ariscaModule.fns[44]? = some ariscaCheckBytesFn := rfl

theorem ariscaCheckBytesFn_mem : ariscaCheckBytesFn ∈ ariscaModule.fns :=
  List.mem_of_getElem? ariscaCheckBytesFn_at_44

theorem ariscaCheckBytesFn_name : ariscaCheckBytesFn.name = "arisca_check_bytes" := rfl

theorem ariscaCheckBytesFn_as :
    ariscaCheckBytesFn.as = [i64, i64, i64, i64, i64, i64] := rfl

theorem ariscaCheckBytesFn_rs : ariscaCheckBytesFn.rs = [i64] := rfl

/-! ## 2. Balanced 5-Slice `LinkedCert.append` Assembly -/

/-- Pair module for slices 0–1 (`[0, 25)`). -/
@[expose] noncomputable def ariscaMod01 : Module :=
  { fns := ariscaFlatMod.fns.take 25 }

/-- Pair module for slices 2–3 (`[25, 39)`). -/
@[expose] noncomputable def ariscaMod23 : Module :=
  { fns := (ariscaFlatMod.fns.drop 25).take 14 }

/-- Prefix module for slices 0–3 (`[0, 39)`). -/
@[expose] noncomputable def ariscaMod03 : Module :=
  { fns := ariscaFlatMod.fns.take 39 }

theorem arisca_drop_take_add {α : Type _} (l : List α) (s i j : Nat) :
    (l.drop s).take (i + j) = (l.drop s).take i ++ (l.drop (s + i)).take j := by
  rw [List.take_add, List.drop_drop]

/-- Combine the 5 parallel `ariscaFlatMod` slice certificates (`[0,15)`, `[15,25)`, `[25,31)`,
`[31,39)`, `[39,45)`) into a whole-module `LinkedCert` over `ariscaModule` via a balanced tree:
`((c0 ++ c1) ++ (c2 ++ c3)) ++ c4`. -/
@[expose] noncomputable def mkAriscaCertTree {T : Target} {L : TargetLayout T}
    {lt : LegalTarget} {hcl : Rega.LabelClean T.toIsa}
    {ext1 ext2 ext3 ext4 : List (SigEntry × Nat)}
    {m0 m1 m2 m3 m4 : Module}
    (hm0 : m0.fns = ariscaFlatMod.fns.take 15)
    (hm1 : m1.fns = (ariscaFlatMod.fns.drop 15).take 10)
    (hm2 : m2.fns = (ariscaFlatMod.fns.drop 25).take 6)
    (hm3 : m3.fns = (ariscaFlatMod.fns.drop 31).take 8)
    (hm4 : m4.fns = ariscaFlatMod.fns.drop 39)
    (c0 : LinkedCert T L lt hcl m0 [] [] 0 2048)
    (c1 : LinkedCert T L lt hcl m1 ext1 [] 0 2048)
    (c2 : LinkedCert T L lt hcl m2 ext2 [] 0 2048)
    (c3 : LinkedCert T L lt hcl m3 ext3 [] 0 2048)
    (c4 : LinkedCert T L lt hcl m4 ext4 [] 0 2048)
    (hlink01 : checkLinkList L [] (c0.chunks ++ c1.chunks) = true)
    (hlink23 : checkLinkList L ext2 (c2.chunks ++ c3.chunks) = true)
    (hlink03 : checkLinkList L [] ((c0.chunks ++ c1.chunks) ++ (c2.chunks ++ c3.chunks)) = true)
    (hlink04 : checkLinkList L []
      (((c0.chunks ++ c1.chunks) ++ (c2.chunks ++ c3.chunks)) ++ c4.chunks) = true) :
    LinkedCert T L lt hcl ariscaModule [] [] 0 2048 :=
  let c01 := c0.append c1 (mod := ariscaMod01)
    (by
      simp only [ariscaMod01, hm0, hm1]
      exact List.take_add (l := ariscaFlatMod.fns) (i := 15) (j := 10))
    hlink01
  let c23 := c2.append c3 (mod := ariscaMod23)
    (by
      simp only [ariscaMod23, hm2, hm3]
      exact arisca_drop_take_add ariscaFlatMod.fns 25 6 8)
    hlink23
  let c03 := c01.append c23 (mod := ariscaMod03)
    (by
      simp only [ariscaMod03, ariscaMod01, ariscaMod23]
      exact List.take_add (l := ariscaFlatMod.fns) (i := 25) (j := 14))
    hlink03
  c03.append c4 (mod := ariscaModule)
    (by
      simp only [ariscaMod03, hm4]
      exact ariscaFlatMod_fns_eq.symm.trans (List.take_append_drop 39 ariscaFlatMod.fns).symm)
    hlink04

/-! ## 3. Compiler-Certificate & `ModuleOk`-Parameterized `BenchAbi` Theorems -/

section AbiCert

variable (A : BenchAbi)

/-- Standalone `compileModule` theorem extracted from any `ariscaModule` `LinkedCert`. -/
theorem arisca_compileModule_abi
    (cert : LinkedCert A.T A.L A.lt A.hcl ariscaModule [] [] 0 2048) :
    compileModule A.T.toIsa A.lt A.T.frame.raBytes [] [] 0
      ariscaFns (chunksHints cert.chunks) = .ok (cert.code, cert.bounds) :=
  linkedCert_compileModule cert

/-- Standalone `checkCompileLit` theorem for any `ariscaModule` `LinkedCert`. -/
theorem arisca_checkLit_abi
    (cert : LinkedCert A.T A.L A.lt A.hcl ariscaModule [] [] 0 2048) :
    checkCompileLit A.T.frame.label A.L.progSmall cert.code cert.bounds
      (ariscaFns.map Fn.name) [] 2048 = true :=
  linkedCert_checkLit cert

/-- Standalone `checkCompile` theorem for any `ariscaModule` `LinkedCert`. -/
theorem arisca_checkCompile_abi
    (cert : LinkedCert A.T A.L A.lt A.hcl ariscaModule [] [] 0 2048) :
    checkCompile A.T A.L A.lt [] [] 0 ariscaFns (chunksHints cert.chunks) 2048 = true :=
  linkedCert_checkCompile cert

/-- Exact entry-function stack bound from `cert.bounds[44]`. -/
theorem arisca_entry_bound_of_getElem
    (cert : LinkedCert A.T A.L A.lt A.hcl ariscaModule [] [] 0 2048)
    {b : Nat}
    (hb : (cert.bounds[44]'(by rw [cert.bounds_length, ariscaModule_fns_len]; decide)).2 = b) :
    cert.bound "arisca_check_bytes" = b := by
  have h44 : 44 < ariscaModule.fns.length := by rw [ariscaModule_fns_len]; decide
  have h := cert.bound_at_fn_idx ariscaModule_namesNodup h44
  have hnm : (ariscaModule.fns[44]'h44).name = "arisca_check_bytes" := rfl
  rw [hnm] at h
  exact h.trans hb

/-- Whole-module `Defined` + `FnSpec` over any host embedding `cert.code`, parameterized over any
`ModuleOk Γ ariscaModule`. -/
theorem arisca_module_fnSpec_of_moduleOk_abi
    (cert : LinkedCert A.T A.L A.lt A.hcl ariscaModule [] [] 0 2048)
    (hleg : LegalSigAll A.lt ariscaModule.fns)
    (hh : A.T.mach.Host) (Γ : Env) (hM : ModuleOk Γ ariscaModule)
    (hnoex : ∀ g ∈ ariscaModule.fns, InlNoExit Γ g)
    (k₀ : Nat) (hc : cert.code.IsInfixAt (A.T.mach.prog hh) k₀) (hu : A.T.LabelsUnique hh)
    {f : Fn} (hf : f ∈ ariscaModule.fns) :
    A.T.Defined hh f.name ∧ A.T.FnSpec hh f.name (Γ f.name f.as f.rs) (cert.bound f.name) 0 := by
  have ⟨hacyc, hwf, hwp⟩ := moduleOk_parts hM
  exact cert.fnSpec_noExit_of_legalSigAll hh Γ k₀ hc hu hacyc hwf hleg hwp hf (hnoex f hf)

/-- Self-contained `Defined` + `FnSpec` on `cert.host`, parameterized over any
`ModuleOk Γ ariscaModule`. -/
theorem arisca_host_module_fnSpec_of_moduleOk_abi
    (cert : LinkedCert A.T A.L A.lt A.hcl ariscaModule [] [] 0 2048)
    (hleg : LegalSigAll A.lt ariscaModule.fns)
    (Γ : Env) (hM : ModuleOk Γ ariscaModule)
    (hnoex : ∀ g ∈ ariscaModule.fns, InlNoExit Γ g)
    {f : Fn} (hf : f ∈ ariscaModule.fns) :
    A.T.Defined cert.host f.name ∧
      A.T.FnSpec cert.host f.name (Γ f.name f.as f.rs) (cert.bound f.name) 0 :=
  arisca_module_fnSpec_of_moduleOk_abi A cert hleg cert.host Γ hM hnoex 0
    cert.code_infix_host cert.labelsUnique hf

/-- Entry-point `Defined` + `FnSpec` for `"arisca_check_bytes"` (`[i64 × 6] → [i64]`),
parameterized over any `ModuleOk Γ ariscaModule`. -/
theorem arisca_entry_fnSpec_of_moduleOk_abi
    (cert : LinkedCert A.T A.L A.lt A.hcl ariscaModule [] [] 0 2048)
    (hleg : LegalSigAll A.lt ariscaModule.fns)
    (hh : A.T.mach.Host) (Γ : Env) (hM : ModuleOk Γ ariscaModule)
    (hnoex : ∀ g ∈ ariscaModule.fns, InlNoExit Γ g)
    (k₀ : Nat) (hc : cert.code.IsInfixAt (A.T.mach.prog hh) k₀) (hu : A.T.LabelsUnique hh) :
    A.T.Defined hh "arisca_check_bytes" ∧
      A.T.FnSpec hh "arisca_check_bytes"
        (Γ "arisca_check_bytes" [i64, i64, i64, i64, i64, i64] [i64])
        (cert.bound "arisca_check_bytes") 0 :=
  arisca_module_fnSpec_of_moduleOk_abi A cert hleg hh Γ hM hnoex k₀ hc hu ariscaCheckBytesFn_mem

/-- Closed 6-argument ABI `Eventually` lift for `"arisca_check_bytes"` over any host embedding
`cert.code`, parameterized over any `ModuleOk Γ ariscaModule` and postcondition `Q`. -/
theorem arisca_entry_eventually_of_moduleOk_abi
    (cert : LinkedCert A.T A.L A.lt A.hcl ariscaModule [] [] 0 2048)
    (hleg : LegalSigAll A.lt ariscaModule.fns)
    (hh : A.T.mach.Host) (Γ : Env) (hM : ModuleOk Γ ariscaModule)
    (hnoex : ∀ g ∈ ariscaModule.fns, InlNoExit Γ g)
    (k₀ : Nat) (hc : cert.code.IsInfixAt (A.T.mach.prog hh) k₀) (hu : A.T.LabelsUnique hh)
    (aig_ptr aig_len art_ptr art_len work_ptr work_len : BitVec 64)
    {m : Mem 64} {Q : Post [i64]}
    (hspec : Γ "arisca_check_bytes" [i64, i64, i64, i64, i64, i64] [i64]
      (aig_ptr, aig_len, art_ptr, art_len, work_ptr, work_len, ()) m Q
      (fun _ _ _ _ => False))
    (s : A.T.mach.MData) (ra : A.T.mach.Addr) (R : Mem 64 → Prop)
    (h0 : A.argAt 0 s = aig_ptr) (h1 : A.argAt 1 s = aig_len)
    (h2 : A.argAt 2 s = art_ptr) (h3 : A.argAt 3 s = art_len)
    (h4 : A.argAt 4 s = work_ptr) (h5 : A.argAt 5 s = work_len)
    (hsp : A.stackPre s ra)
    (hmem : (A.T.mach.mem s =⋆ Eq m ⋆ A.entryFrame s ra (cert.bound "arisca_check_bytes") ⋆ R)) :
    Eventually (A.T.mach.step hh)
      (fun st =>
        A.T.mach.pc st = ra ∧
        A.calleeSavedOk s (A.T.mach.data st) ∧
        A.spRestored s (A.T.mach.data st) ∧
        ∃ m', Q (A.retGpr (A.T.mach.data st), ()) m' ∧
          (A.T.mach.mem (A.T.mach.data st) =⋆
            Eq m' ⋆ A.exitFrame s (cert.bound "arisca_check_bytes") ⋆ R))
      (A.T.mach.mkState s (A.T.mach.labelAddr hh "arisca_check_bytes")) :=
  abi_of_returns_ret1_q A hh
    (arisca_entry_fnSpec_of_moduleOk_abi A cert hleg hh Γ hM hnoex k₀ hc hu).2
    hspec s ra R (A.argsIn_6 h0 h1 h2 h3 h4 h5) hsp hmem

/-- Concrete `TargetInit` execution runner for `"arisca_check_bytes"` on `cert.host`, ready for
5-line M1-C non-vacuity composition (`r = 20#64` / `r = 0#64`). -/
theorem arisca_entry_run_ret1_of_moduleOk_abi
    (cert : LinkedCert A.T A.L A.lt A.hcl ariscaModule [] [] 0 2048)
    (hleg : LegalSigAll A.lt ariscaModule.fns)
    (Γ : Env) (hM : ModuleOk Γ ariscaModule)
    (hnoex : ∀ g ∈ ariscaModule.fns, InlNoExit Γ g)
    (bsMem : List UInt8) (args : Tup Val [i64, i64, i64, i64, i64, i64])
    (v : BitVec 64) (hlen : bsMem.length ≤ 8192)
    {Q : Post [i64]}
    (hspec : Γ "arisca_check_bytes" [i64, i64, i64, i64, i64, i64] [i64]
      args (bsMem.At 0x1000#64) Q (fun _ _ _ _ => False))
    (hQ : ∀ rets m', Q rets m' → rets = (v, ())) :
    Eventually (A.T.mach.step cert.host)
      (fun st => A.T.mach.pc st = A.init.ra0 ∧ A.retGpr (A.T.mach.data st) = v)
      (A.T.mach.mkState (A.init.initState (cert.bound "arisca_check_bytes") bsMem args)
        (A.T.mach.labelAddr cert.host "arisca_check_bytes")) := by
  have hfn := (arisca_entry_fnSpec_of_moduleOk_abi A cert hleg cert.host Γ hM hnoex 0
    cert.code_infix_host cert.labelsUnique).2
  have hassign : (A.T.toIsa.assignArgs [i64, i64, i64, i64, i64, i64]).isSome = true :=
    A.assignArgs_i64 6 (by decide)
  refine eventually_weaken _ _ _ _ (fun _ ⟨hpc, hrets⟩ => ⟨hpc, A.retGpr_eq_of_retsIn hrets⟩)
    (cert.run_ret1 A.init hfn bsMem args v (Nat.le_trans hlen A.maxMem_ge)
      hassign hspec hQ A.maxStack_ge)

end AbiCert

end LeanQbe.T.Examples.Arisca.Build.CertCommon
