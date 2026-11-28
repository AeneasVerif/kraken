/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Arisca.Build.CertCommon
public import LeanQbe.T.Examples.Arisca.Proof.Full
import LeanQbe.T.Logic.Bytes
import Kraken.Separation

/-!
# Arch-Free End-to-End Composition Bridge for ARiSCA (`Arisca.Proof.CertBridge`)

Composes `M1-C` (`ariscaModule_ok : ModuleOk ariscaEnv ariscaModule`) with any `M1-D`
`LinkedCert` over `BenchAbi` (`0` `Amd64`/`Arm64`/`Kraken.X64`/`Kraken.AArch64`/`Kissat` imports,
`0` `import all`, `<= std3`):
* `arisca_module_fnspec_abi` (44-fn whole-module `Defined` + `FnSpec`);
* `arisca_check_bytes_correct_abi` (machine-code soundness + callee-saved/SP/heap framing);
* `arisca_check_bytes_sound_abi` (concise soundness corollary: `ret = 20#64` (`AR_ACCEPT`)
  implies `ArtSound.checkArt_sound` modular polynomial/circuit multiplier equivalence);
* `arisca_check_bytes_nv_abi` (concrete closed-host `0x1000#64` `Mem 64` non-vacuity witness).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Arisca.Proof.CertBridge

open Std Std.ExtHashMap
open LeanQbe.T LeanQbe.T.BenchmarkCertKit LeanQbe.T.ProofUtil Kraken
open LeanQbe.T.Examples.Arisca
open LeanQbe.T.Examples.Arisca.Src.Module
open LeanQbe.T.Examples.Arisca.Build.CertCommon
open LeanQbe.T.Examples.Arisca.Proof

public section

/-! ## 1. `ariscaEnv` Entry & `InlNoExit` Bridges -/

/-- Every function in `ariscaModule.fns` (`45` fns) ignores exit continuations in `ariscaEnv`. -/
theorem ariscaEnv_inlNoExit : ∀ g ∈ ariscaModule.fns, InlNoExit ariscaEnv g :=
  fun g _ => ariscaEnv_noExit g.name g.as g.rs

/-- Row `44` lookup in `ariscaEnv` for top-level `"arisca_check_bytes"`. -/
theorem ariscaEnv_check_bytes :
    ∀ xs m Q X, ariscaCheckBytesSpec xs m Q X →
      ariscaEnv "arisca_check_bytes" [i64, i64, i64, i64, i64, i64] [i64] xs m Q X :=
  ariscaEnv_row_at 44
    ⟨"arisca_check_bytes", [i64, i64, i64, i64, i64, i64], [i64],
      ariscaCheckBytesSpec, true⟩
    (by rfl) (by intro _ _ _ _ h; exact h)

/-! ## 2. Concrete `0x1000#64` Non-Vacuity Payload (`TargetInit`-Compatible) -/

/-- Concrete `TargetInit` base pointer for `nvAigBytes` (`18` bytes at `0x1000#64`). -/
@[expose] def ariscaNvAigPtr : BitVec 64 := 0x1000#64

/-- Concrete `TargetInit` pointer for `nvArtBytes` (`4` bytes at `0x1012#64`). -/
@[expose] def ariscaNvArtPtr : BitVec 64 := 0x1012#64

/-- Concrete `TargetInit` pointer for `0x1000`-byte scratch workspace (`0x1016#64`). -/
@[expose] def ariscaNvWorkPtr : BitVec 64 := 0x1016#64

/-- Concrete scratch workspace capacity (`4096` bytes). -/
@[expose] def ariscaNvWorkCap : BitVec 64 := 0x1000#64

/-- Concrete `4118`-byte `TargetInit` payload (`nvAigBytes ++ nvArtBytes ++ 4096 zeros`). -/
@[expose] def ariscaNvPayload : List UInt8 :=
  nvAigBytes ++ nvArtBytes ++ List.replicate 0x1000 (0 : UInt8)

/-- Concrete 6-argument `i64` tuple for `arisca_check_bytes` over `ariscaNvPayload`. -/
@[expose] def ariscaNvArgs : Tup Val [i64, i64, i64, i64, i64, i64] :=
  (ariscaNvAigPtr, nvAigLen, ariscaNvArtPtr, nvArtLen, ariscaNvWorkPtr, ariscaNvWorkCap, ())

theorem ariscaNvPayload_length : ariscaNvPayload.length ≤ 8192 := by
  have hl_aig : nvAigBytes.length = 18 := rfl
  have hl_art : nvArtBytes.length = 4 := rfl
  have hl_rep : (List.replicate 0x1000 (0 : UInt8)).length = 0x1000 := List.length_replicate
  dsimp only [ariscaNvPayload]
  rw [List.length_append, List.length_append, hl_aig, hl_art, hl_rep]
  decide

/-- Separation-logic decomposition of `ariscaNvPayload.At 0x1000#64`. -/
theorem ariscaNvPayload_sep :
    (bytes ariscaNvAigPtr nvAigBytes ⋆ bytes ariscaNvArtPtr nvArtBytes ⋆
      region ariscaNvWorkPtr ariscaNvWorkCap.toNat ⋆ (emp : Mem 64 → Prop))
      (ariscaNvPayload.At 0x1000#64) := by
  have hl_aig : nvAigBytes.length = 18 := rfl
  have hl_art : nvArtBytes.length = 4 := rfl
  have hl_rep : (List.replicate 0x1000 (0 : UInt8)).length = 0x1000 := List.length_replicate
  have hlen1 : nvAigBytes.length + (nvArtBytes ++ List.replicate 0x1000 (0 : UInt8)).length ≤
      2 ^ 64 := by
    rw [List.length_append, hl_aig, hl_art, hl_rep]; decide
  have hlen2 : nvArtBytes.length + (List.replicate 0x1000 (0 : UInt8)).length ≤ 2 ^ 64 := by
    rw [hl_art, hl_rep]; decide
  have hsep1 := Mem.At_append_sep nvAigBytes
    (nvArtBytes ++ List.replicate 0x1000 (0 : UInt8)) ariscaNvAigPtr hlen1
  have hsep2 := Mem.At_append_sep nvArtBytes
    (List.replicate 0x1000 (0 : UInt8)) ariscaNvArtPtr hlen2
  have hadr1 : ariscaNvAigPtr + BitVec.ofNat 64 nvAigBytes.length = ariscaNvArtPtr := by
    rw [hl_aig]; rfl
  have hadr2 : ariscaNvArtPtr + BitVec.ofNat 64 nvArtBytes.length = ariscaNvWorkPtr := by
    rw [hl_art]; rfl
  have hself : Eq ((nvAigBytes ++ nvArtBytes ++ List.replicate 0x1000 (0 : UInt8)).At
      ariscaNvAigPtr) (ariscaNvPayload.At 0x1000#64) := rfl
  rw [List.append_assoc, hsep1, hadr1, hsep2, hadr2] at hself
  have h0 : (Eq ((List.replicate 0x1000 (0 : UInt8)).At ariscaNvWorkPtr) ⋆
      (Eq (nvAigBytes.At ariscaNvAigPtr) ⋆ Eq (nvArtBytes.At ariscaNvArtPtr)))
      (ariscaNvPayload.At 0x1000#64) :=
    sep_cast hself (by ac_rfl)
  have h1 := sep_mono (P := Eq ((List.replicate 0x1000 (0 : UInt8)).At ariscaNvWorkPtr))
    (P' := region ariscaNvWorkPtr ariscaNvWorkCap.toNat)
    (fun _ h => ⟨List.replicate 0x1000 (0 : UInt8), hl_rep, h.symm⟩) h0
  have h2 : (bytes ariscaNvAigPtr nvAigBytes ⋆ bytes ariscaNvArtPtr nvArtBytes ⋆
      region ariscaNvWorkPtr ariscaNvWorkCap.toNat) (ariscaNvPayload.At 0x1000#64) :=
    sep_cast h1 (by ac_rfl)
  simpa [sep_emp] using h2

/-! ## 3. Arch-Agnostic End-to-End `BenchAbi` Soundness & Non-Vacuity Combinators -/

section AbiCompose

variable (A : BenchAbi)

/-- Closed 45-function `Defined` + `FnSpec` under `ariscaEnv` over any host embedding
`cert.code`. -/
theorem arisca_module_fnspec_abi
    (cert : LinkedCert A.T A.L A.lt A.hcl ariscaModule [] [] 0 2048)
    (hleg : LegalSigAll A.lt ariscaModule.fns)
    (hh : A.T.mach.Host) (k₀ : Nat)
    (hc : cert.code.IsInfixAt (A.T.mach.prog hh) k₀) (hu : A.T.LabelsUnique hh)
    {f : Fn} (hf : f ∈ ariscaModule.fns) :
    A.T.Defined hh f.name ∧
      A.T.FnSpec hh f.name (ariscaEnv f.name f.as f.rs) (cert.bound f.name) 0 :=
  arisca_module_fnSpec_of_moduleOk_abi A cert hleg hh ariscaEnv ariscaModule_ok
    ariscaEnv_inlNoExit k₀ hc hu hf

/-- Closed end-to-end machine-code soundness and ABI/heap framing for `"arisca_check_bytes"`
(`XPost := False`, `ret = 20#64` (`AR_ACCEPT`) implies multiplier or `SPEC_MITER` equivalence). -/
theorem arisca_check_bytes_correct_abi
    (cert : LinkedCert A.T A.L A.lt A.hcl ariscaModule [] [] 0 2048)
    (hleg : LegalSigAll A.lt ariscaModule.fns)
    (hh : A.T.mach.Host) (k₀ : Nat)
    (hc : cert.code.IsInfixAt (A.T.mach.prog hh) k₀) (hu : A.T.LabelsUnique hh)
    (aig_ptr aig_len art_ptr art_len work_ptr work_len : BitVec 64)
    (aigBytes artBytes : List UInt8)
    (haig : aig_len.toNat = aigBytes.length)
    (hart : art_len.toNat = artBytes.length)
    (s : A.T.mach.MData) (ra : A.T.mach.Addr) (R : Mem 64 → Prop)
    (h0 : A.argAt 0 s = aig_ptr) (h1 : A.argAt 1 s = aig_len)
    (h2 : A.argAt 2 s = art_ptr) (h3 : A.argAt 3 s = art_len)
    (h4 : A.argAt 4 s = work_ptr) (h5 : A.argAt 5 s = work_len)
    (hsp : A.stackPre s ra)
    (hmem : (A.T.mach.mem s =⋆
      (bytes aig_ptr aigBytes ⋆ bytes art_ptr artBytes ⋆ region work_ptr work_len.toNat) ⋆
      A.entryFrame s ra (cert.bound "arisca_check_bytes") ⋆ R)) :
    Eventually (A.T.mach.step hh)
      (fun st =>
        A.T.mach.pc st = ra ∧
        (A.retGpr (A.T.mach.data st) = 20#64 →
          ∃ g : Aig,
            parseAig (toNatBytes aigBytes) = some g ∧
            ariscaCircuitProp (BitVec.ofNat 32 (wordAt artBytes 2)) g) ∧
        A.calleeSavedOk s (A.T.mach.data st) ∧
        A.spRestored s (A.T.mach.data st) ∧
        (A.T.mach.mem (A.T.mach.data st) =⋆
          (bytes aig_ptr aigBytes ⋆ bytes art_ptr artBytes ⋆ region work_ptr work_len.toNat) ⋆
          A.exitFrame s (cert.bound "arisca_check_bytes") ⋆ R))
      (A.T.mach.mkState s (A.T.mach.labelAddr hh "arisca_check_bytes")) := by
  obtain ⟨m, hm, hmEq⟩ := sep_extract_eq hmem
  have hspec : ariscaEnv "arisca_check_bytes" [i64, i64, i64, i64, i64, i64] [i64]
      (aig_ptr, aig_len, art_ptr, art_len, work_ptr, work_len, ()) m
      (fun r m' =>
        (r.1 = 20#64 →
          ∃ g : Aig,
            parseAig (toNatBytes aigBytes) = some g ∧
            ariscaCircuitProp (BitVec.ofNat 32 (wordAt artBytes 2)) g) ∧
        (bytes aig_ptr aigBytes ⋆ bytes art_ptr artBytes ⋆
          region work_ptr work_len.toNat) m')
      (fun _ _ _ _ => False) :=
    ariscaEnv_check_bytes _ _ _ _
      ⟨aigBytes, artBytes, emp, haig, hart, by rwa [sep_emp],
        fun _ _ h20 hm' => ⟨h20, by rwa [sep_emp] at hm'⟩⟩
  refine eventually_weaken _ _ _ _ ?_
    (arisca_entry_eventually_of_moduleOk_abi A cert hleg hh ariscaEnv ariscaModule_ok
      ariscaEnv_inlNoExit k₀ hc hu aig_ptr aig_len art_ptr art_len work_ptr work_len
      hspec s ra R h0 h1 h2 h3 h4 h5 hsp hmEq)
  rintro st ⟨hpc, hcs, hsp', m', ⟨h20, hm'⟩, hdmem⟩
  exact ⟨hpc, h20, hcs, hsp', sep_mono (fun _ => sep_mono (fun _ e => e ▸ hm')) hdmem⟩

/-- Concise soundness corollary of `arisca_check_bytes_correct_abi`. -/
theorem arisca_check_bytes_sound_abi
    (cert : LinkedCert A.T A.L A.lt A.hcl ariscaModule [] [] 0 2048)
    (hleg : LegalSigAll A.lt ariscaModule.fns)
    (hh : A.T.mach.Host) (k₀ : Nat)
    (hc : cert.code.IsInfixAt (A.T.mach.prog hh) k₀) (hu : A.T.LabelsUnique hh)
    (aig_ptr aig_len art_ptr art_len work_ptr work_len : BitVec 64)
    (aigBytes artBytes : List UInt8)
    (haig : aig_len.toNat = aigBytes.length)
    (hart : art_len.toNat = artBytes.length)
    (s : A.T.mach.MData) (ra : A.T.mach.Addr) (R : Mem 64 → Prop)
    (h0 : A.argAt 0 s = aig_ptr) (h1 : A.argAt 1 s = aig_len)
    (h2 : A.argAt 2 s = art_ptr) (h3 : A.argAt 3 s = art_len)
    (h4 : A.argAt 4 s = work_ptr) (h5 : A.argAt 5 s = work_len)
    (hsp : A.stackPre s ra)
    (hmem : (A.T.mach.mem s =⋆
      (bytes aig_ptr aigBytes ⋆ bytes art_ptr artBytes ⋆ region work_ptr work_len.toNat) ⋆
      A.entryFrame s ra (cert.bound "arisca_check_bytes") ⋆ R)) :
    Eventually (A.T.mach.step hh)
      (fun st =>
        A.T.mach.pc st = ra ∧
        (A.retGpr (A.T.mach.data st) = 20#64 →
          ∃ g : Aig,
            parseAig (toNatBytes aigBytes) = some g ∧
            ariscaCircuitProp (BitVec.ofNat 32 (wordAt artBytes 2)) g))
      (A.T.mach.mkState s (A.T.mach.labelAddr hh "arisca_check_bytes")) :=
  eventually_weaken _ _ _ _ (fun _ ⟨hpc, h20, _⟩ => ⟨hpc, h20⟩)
    (arisca_check_bytes_correct_abi A cert hleg hh k₀ hc hu
      aig_ptr aig_len art_ptr art_len work_ptr work_len aigBytes artBytes haig hart
      s ra R h0 h1 h2 h3 h4 h5 hsp hmem)

/-- Concrete closed-host `Mem 64` non-vacuity execution witness for compiled
`"arisca_check_bytes"` on `cert.host`. -/
theorem arisca_check_bytes_nv_abi
    (cert : LinkedCert A.T A.L A.lt A.hcl ariscaModule [] [] 0 2048)
    (hleg : LegalSigAll A.lt ariscaModule.fns) :
    Eventually (A.T.mach.step cert.host)
      (fun st =>
        A.T.mach.pc st = A.init.ra0 ∧
        (A.retGpr (A.T.mach.data st) = 20#64 →
          ∃ g : Aig,
            parseAig (toNatBytes nvAigBytes) = some g ∧
            ariscaCircuitProp (BitVec.ofNat 32 (wordAt nvArtBytes 2)) g) ∧
        (A.T.mach.mem (A.T.mach.data st) =⋆
          (bytes ariscaNvAigPtr nvAigBytes ⋆ bytes ariscaNvArtPtr nvArtBytes ⋆
            region ariscaNvWorkPtr ariscaNvWorkCap.toNat) ⋆
          A.initExitFrame (cert.bound "arisca_check_bytes") ⋆ emp))
      (A.T.mach.mkState
        (A.init.initState (as := [i64, i64, i64, i64, i64, i64])
          (cert.bound "arisca_check_bytes") ariscaNvPayload ariscaNvArgs)
        (A.T.mach.labelAddr cert.host "arisca_check_bytes")) := by
  have hfn := (arisca_entry_fnSpec_of_moduleOk_abi A cert hleg cert.host ariscaEnv
    ariscaModule_ok ariscaEnv_inlNoExit 0 cert.code_infix_host cert.labelsUnique).2
  have hspec : ariscaEnv "arisca_check_bytes" [i64, i64, i64, i64, i64, i64] [i64]
      ariscaNvArgs (ariscaNvPayload.At 0x1000#64)
      (fun r m' =>
        (r.1 = 20#64 →
          ∃ g : Aig,
            parseAig (toNatBytes nvAigBytes) = some g ∧
            ariscaCircuitProp (BitVec.ofNat 32 (wordAt nvArtBytes 2)) g) ∧
        (bytes ariscaNvAigPtr nvAigBytes ⋆ bytes ariscaNvArtPtr nvArtBytes ⋆
          region ariscaNvWorkPtr ariscaNvWorkCap.toNat) m')
      (fun _ _ _ _ => False) :=
    ariscaEnv_check_bytes _ _ _ _
      ⟨nvAigBytes, nvArtBytes, emp, rfl, rfl, ariscaNvPayload_sep,
        fun _ _ h20 hm' => ⟨h20, by rwa [sep_emp] at hm'⟩⟩
  refine cert.run_fnSpec A.init hfn ariscaNvPayload ariscaNvArgs
    (Nat.le_trans ariscaNvPayload_length A.maxMem_ge)
    (A.assignArgs_i64 6 (by decide)) hspec ?_ A.maxStack_ge
  rintro st (⟨hpc, ⟨r, ⟨⟩⟩, m', ⟨h20, hm'⟩, hrets, hdmem⟩ | ⟨_, _, _, _, hx, _⟩)
  · rw [← A.retGpr_eq_of_retsIn hrets] at h20
    exact ⟨hpc, h20,
      sep_mono_mid (fun _ hex => A.initExitFrame_of_exit hex)
        (sep_mono (fun _ => sep_mono (fun _ e => e ▸ hm')) hdmem)⟩
  · exact hx.elim

end AbiCompose

end

end LeanQbe.T.Examples.Arisca.Proof.CertBridge
