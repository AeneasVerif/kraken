module

public import LeanQbe.T.Examples.Kissat.KissatAbiCommon
public import LeanQbe.T.Examples.Kissat.PlainLemmas
import LeanQbe.T.AbiLemmas
import Kraken.Mem
import Kraken.Separation

/-!
# Arch-Free Kissat `D-Plain` Compilation & Proof Bridge (`KissatPlainCertCommon`)

Centralizes architecture-independent slice composition (depth-3 balanced binary tree via
`LinkedCert.append`), generic `FnSpec` linking, and end-to-end SAT/UNSAT correctness and
non-vacuity proofs over `ArchKissatAbi` for `LeanQbe.T.{Amd64,Arm64}.KissatPlain*`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.KissatPlainCertCommon

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Plain LeanQbe.T.Examples.Kissat.KissatCertCommon
open Kraken

/-! ## 1. Balanced Binary-Tree Slice Composition & Generic `FnSpec` -/

/-- Pair module for slices 1–2 (`[0, 29)`). -/
@[expose] def plainMod12 : Module := { fns := plainFns.take 29 }

/-- Pair module for slices 3–4 (`[29, 47)`). -/
@[expose] def plainMod34 : Module := { fns := (plainFns.drop 29).take 18 }

/-- Pair module for slices 5–6 (`[47, 59)`). -/
@[expose] def plainMod56 : Module := { fns := plainFns.drop 47 }

/-- Quad module for slices 1–4 (`[0, 47)`). -/
@[expose] def plainMod14 : Module := { fns := plainFns.take 47 }

theorem plain_drop_take_add {α : Type _} (l : List α) (s i j : Nat) :
    (l.drop s).take (i + j) = (l.drop s).take i ++ (l.drop (s + i)).take j := by
  rw [List.take_add, List.drop_drop]

theorem plain_drop_take_drop {α : Type _} (l : List α) (s i : Nat) :
    l.drop s = (l.drop s).take i ++ l.drop (s + i) := by
  have h := (List.take_append_drop i (l.drop s)).symm
  rwa [List.drop_drop] at h

/-- Combine the 6 parallel `plainFns` slice certificates into a whole-module `LinkedCert` via a
balanced depth-3 binary tree: `((c1 ++ c2) ++ (c3 ++ c4)) ++ (c5 ++ c6)`. -/
@[expose] noncomputable def mkPlainCertTree {T : Target} {L : TargetLayout T} {lt : LegalTarget}
    {hcl : Rega.LabelClean T.toIsa}
    {ext2 ext3 ext4 ext5 ext6 : List (SigEntry × Nat)}
    {m1 m2 m3 m4 m5 m6 : Module}
    (hm1 : m1.fns = plainFns.take 15)
    (hm2 : m2.fns = (plainFns.drop 15).take 14)
    (hm3 : m3.fns = (plainFns.drop 29).take 11)
    (hm4 : m4.fns = (plainFns.drop 40).take 7)
    (hm5 : m5.fns = (plainFns.drop 47).take 5)
    (hm6 : m6.fns = plainFns.drop 52)
    (c1 : LinkedCert T L lt hcl m1 [] [] 0 2048)
    (c2 : LinkedCert T L lt hcl m2 ext2 [] 0 2048)
    (c3 : LinkedCert T L lt hcl m3 ext3 [] 0 2048)
    (c4 : LinkedCert T L lt hcl m4 ext4 [] 0 2048)
    (c5 : LinkedCert T L lt hcl m5 ext5 [] 0 2048)
    (c6 : LinkedCert T L lt hcl m6 ext6 [] 0 2048)
    (hlink12 : checkLinkList L [] (c1.chunks ++ c2.chunks) = true)
    (hlink34 : checkLinkList L ext3 (c3.chunks ++ c4.chunks) = true)
    (hlink56 : checkLinkList L ext5 (c5.chunks ++ c6.chunks) = true)
    (hlink14 : checkLinkList L [] ((c1.chunks ++ c2.chunks) ++ (c3.chunks ++ c4.chunks)) = true)
    (hlink16 : checkLinkList L []
      (((c1.chunks ++ c2.chunks) ++ (c3.chunks ++ c4.chunks)) ++
        (c5.chunks ++ c6.chunks)) = true) :
    LinkedCert T L lt hcl plainModule [] [] 0 2048 :=
  let c12 := c1.append c2 (mod := plainMod12)
    (by simp only [plainMod12, hm1, hm2]; exact List.take_add (l := plainFns) (i := 15) (j := 14))
    hlink12
  let c34 := c3.append c4 (mod := plainMod34)
    (by simp only [plainMod34, hm3, hm4]; exact plain_drop_take_add plainFns 29 11 7)
    hlink34
  let c56 := c5.append c6 (mod := plainMod56)
    (by simp only [plainMod56, hm5, hm6]; exact plain_drop_take_drop plainFns 47 5)
    hlink56
  let c14 := c12.append c34 (mod := plainMod14)
    (by simp only [plainMod14, plainMod12, plainMod34]
        exact List.take_add (l := plainFns) (i := 29) (j := 18))
    hlink14
  c14.append c56 (mod := plainModule)
    (by simp only [plainModule, plainMod14, plainMod56]
        exact (List.take_append_drop 47 plainFns).symm)
    hlink16

theorem plain_mk_module_fnspec {T : Target} {L : TargetLayout T} {lt : LegalTarget}
    {hcl : Rega.LabelClean T.toIsa}
    (cert : LinkedCert T L lt hcl plainModule [] [] 0 2048)
    (hleg : LegalSigAll lt plainModule.fns)
    (hh : T.mach.Host) (Γ : Env)
    (hsound : ∀ f ∈ plainFns, ∀ args m Q X,
      Γ f.name f.as f.rs args m Q X → Func.wp Γ f.body args m Q X)
    (hnoex : ∀ g ∈ plainFns, ∀ args m Q X X',
      Γ g.name g.as g.rs args m Q X → Γ g.name g.as g.rs args m Q X')
    (k₀ : Nat) (hc : cert.code.IsInfixAt (T.mach.prog hh) k₀) (hu : T.LabelsUnique hh)
    {f : Fn} (hf : f ∈ plainModule.fns) :
    T.Defined hh f.name ∧ T.FnSpec hh f.name (Γ f.name f.as f.rs) (cert.bound f.name) 0 :=
  cert.fnSpec_noExit_of_legalSigAll hh Γ k₀ hc hu
    plain_acyclic plainFns_wf hleg hsound hf (hnoex f hf)

/-! ## 2. End-to-End Top-Level `KissatPlain` Theorems over `ArchKissatAbi` -/

theorem plain_module_fnspec_abi (A : ArchKissatAbi)
    (cert : LinkedCert A.T A.L A.lt A.hcl plainModule [] [] 0 2048)
    (hleg : LegalSigAll A.lt plainModule.fns)
    (hh : A.T.mach.Host) (k₀ : Nat)
    (hc : cert.code.IsInfixAt (A.T.mach.prog hh) k₀) (hu : A.T.LabelsUnique hh)
    {f : Fn} (hf : f ∈ plainModule.fns) :
    A.T.Defined hh f.name ∧
      A.T.FnSpec hh f.name (plainEnv f.name f.as f.rs) (cert.bound f.name) 0 :=
  plain_mk_module_fnspec cert hleg hh plainEnv plainEnv_sound
    (fun _ _ => plainEnv_noExit _ _ _) k₀ hc hu hf

private theorem plain_mk_entry_fnspec_abi (A : ArchKissatAbi)
    (cert : LinkedCert A.T A.L A.lt A.hcl plainModule [] [] 0 2048)
    (hleg : LegalSigAll A.lt plainModule.fns)
    (hh : A.T.mach.Host)
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hsound : ∀ f ∈ plainFns, ∀ args m Q X,
      mkPlainEnv mainSpec f.name f.as f.rs args m Q X →
      Func.wp (mkPlainEnv mainSpec) f.body args m Q X)
    (hno : ∀ xs m Q X, mainSpec xs m Q X → mainSpec xs m Q (fun _ _ _ _ => False))
    (k₀ : Nat) (hc : cert.code.IsInfixAt (A.T.mach.prog hh) k₀) (hu : A.T.LabelsUnique hh) :
    A.T.FnSpec hh "kissat_solve_bytes" mainSpec (cert.bound "kissat_solve_bytes") 0 :=
  Target.FnSpec.of_spec A.T
    (plain_mk_module_fnspec cert hleg hh (mkPlainEnv mainSpec) hsound
      (fun g _ => mkPlainEnv_noExit mainSpec g.name g.as g.rs) k₀ hc hu
      (f := Plain.kissat_solve_bytes) (by simp [plainModule, plainFns, plain2_fns])).2
    (mkPlainEnv_solve_bytes mainSpec hno)

theorem plain_solve_correct_abi (A : ArchKissatAbi)
    (cert : LinkedCert A.T A.L A.lt A.hcl plainModule [] [] 0 2048)
    (hleg : LegalSigAll A.lt plainModule.fns)
    (hh : A.T.mach.Host) (k₀ : Nat)
    (hc : cert.code.IsInfixAt (A.T.mach.prog hh) k₀) (hu : A.T.LabelsUnique hh)
    (cnf_ptr work_ptr fuel : BitVec 64) (cnfBytes : List UInt8) (wlen : Nat)
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (s : A.T.mach.MData) (ra : A.T.mach.Addr) (R : Mem 64 → Prop)
    (hargs : A.args5Ok s cnf_ptr (BitVec.ofNat 64 cnfBytes.length) work_ptr
      (BitVec.ofNat 64 wlen) fuel)
    (hsp : A.stackPre s ra)
    (hmem : (A.T.mach.mem s =⋆
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen) ⋆
      A.entryFrame s ra (cert.bound "kissat_solve_bytes") ⋆ R)) :
    Eventually (A.T.mach.step hh)
      (fun st =>
        A.T.mach.pc st = ra ∧
        (A.retGpr (A.T.mach.data st) = 0#64 ∨
          A.retGpr (A.T.mach.data st) = 10#64 ∨
          A.retGpr (A.T.mach.data st) = 20#64) ∧
        (A.retGpr (A.T.mach.data st) = 20#64 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (A.retGpr (A.T.mach.data st) = 10#64 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ ¬ cnf.Unsat ∧ ∃ α, cnf.Sat α) ∧
        A.calleeSpOk s (A.T.mach.data st) ∧
        (A.T.mach.mem (A.T.mach.data st) =⋆
          (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen) ⋆
          A.exitFrame s (cert.bound "kissat_solve_bytes") ⋆ R))
      (A.T.mach.mkState s (A.T.mach.labelAddr hh "kissat_solve_bytes")) := by
  have hm0 : ((bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen) ⋆
      (A.entryFrame s ra (cert.bound "kissat_solve_bytes") ⋆ R)) (A.T.mach.mem s) := by
    rw [← sep_assoc]; exact hmem
  obtain ⟨m, hm, hmEq0⟩ := sep_exists_eq hm0
  have hmEq : (Eq m ⋆ A.entryFrame s ra (cert.bound "kissat_solve_bytes") ⋆ R)
      (A.T.mach.mem s) := by
    rw [sep_assoc]; exact hmEq0
  have hfn := plain_mk_entry_fnspec_abi A cert hleg hh plainSolveBytesSpec plainEnv_sound
    (fun _ _ _ _ h => h) k₀ hc hu
  have hspec : plainSolveBytesSpec
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ()) m
      (fun (r, ()) m' =>
        (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) ∧
        (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (r = 10#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ ¬ cnf.Unsat ∧ ∃ α, cnf.Sat α) ∧
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen) m')
      (fun _ _ _ _ => False) :=
    ⟨cnfBytes, wlen, emp, rfl, rfl, hcfit, hwfit, by rw [sep_emp]; exact hm,
      fun _ _ hdom hu' hs hm' => by rw [sep_emp] at hm'; exact ⟨hdom, hu', hs, hm'⟩⟩
  refine eventually_weaken _ _ _ _ ?_
    (solve_of_abi_fnspec A hh "kissat_solve_bytes" hfn cnf_ptr (BitVec.ofNat 64 cnfBytes.length)
      work_ptr (BitVec.ofNat 64 wlen) fuel hspec s ra R hargs hsp hmEq)
  rintro st ⟨hpc, hcal, m', ⟨hdom, hu', hs, hm'⟩, hm_dmem⟩
  rw [sep_assoc] at hm_dmem
  have hm_dmem' := sep_mono (fun _ e => e ▸ hm') hm_dmem
  rw [← sep_assoc] at hm_dmem'
  exact ⟨hpc, hdom, hu', hs, hcal, hm_dmem'⟩

theorem plain_solve_sound_abi (A : ArchKissatAbi)
    (cert : LinkedCert A.T A.L A.lt A.hcl plainModule [] [] 0 2048)
    (hleg : LegalSigAll A.lt plainModule.fns)
    (hh : A.T.mach.Host) (k₀ : Nat)
    (hc : cert.code.IsInfixAt (A.T.mach.prog hh) k₀) (hu : A.T.LabelsUnique hh)
    (cnf_ptr work_ptr fuel : BitVec 64) (cnfBytes : List UInt8) (wlen : Nat)
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (s : A.T.mach.MData) (ra : A.T.mach.Addr) (R : Mem 64 → Prop)
    (hargs : A.args5Ok s cnf_ptr (BitVec.ofNat 64 cnfBytes.length) work_ptr
      (BitVec.ofNat 64 wlen) fuel)
    (hsp : A.stackPre s ra)
    (hmem : (A.T.mach.mem s =⋆
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen) ⋆
      A.entryFrame s ra (cert.bound "kissat_solve_bytes") ⋆ R)) :
    Eventually (A.T.mach.step hh)
      (fun st =>
        A.T.mach.pc st = ra ∧
        (A.retGpr (A.T.mach.data st) = 0#64 ∨
          A.retGpr (A.T.mach.data st) = 10#64 ∨
          A.retGpr (A.T.mach.data st) = 20#64) ∧
        (A.retGpr (A.T.mach.data st) = 20#64 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (A.retGpr (A.T.mach.data st) = 10#64 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ ¬ cnf.Unsat ∧ ∃ α, cnf.Sat α))
      (A.T.mach.mkState s (A.T.mach.labelAddr hh "kissat_solve_bytes")) :=
  eventually_weaken _ _ _ _ (fun _ ⟨hpc, hdom, hu', hs, _⟩ => ⟨hpc, hdom, hu', hs⟩)
    (plain_solve_correct_abi A cert hleg hh k₀ hc hu cnf_ptr work_ptr fuel cnfBytes wlen
      hcfit hwfit s ra R hargs hsp hmem)

@[expose] def plainArgs (cnfBytes : List UInt8) : Tup Val [i64, i64, i64, i64, i64] :=
  (plainNvCnfPtr, BitVec.ofNat 64 cnfBytes.length,
    plainNvWorkPtr cnfBytes, 2048#64, 16#64, ())

private theorem plain_nv_run_ret1 (A : ArchKissatAbi)
    (cert : LinkedCert A.T A.L A.lt A.hcl plainModule [] [] 0 2048)
    (hleg : LegalSigAll A.lt plainModule.fns)
    (mainSpec : Spec [i64, i64, i64, i64, i64] [i64])
    (hsound : ∀ f ∈ plainFns, ∀ args m Q X,
      mkPlainEnv mainSpec f.name f.as f.rs args m Q X →
      Func.wp (mkPlainEnv mainSpec) f.body args m Q X)
    (hno : ∀ xs m Q X, mainSpec xs m Q X → mainSpec xs m Q (fun _ _ _ _ => False))
    (cnfBytes : List UInt8) (hlen : (plainPayload cnfBytes).length ≤ 8192)
    {P : Prop} {ret : BitVec 64}
    (hspec : mainSpec (plainArgs cnfBytes) ((plainPayload cnfBytes).At 0x1000#64)
      (fun rs _ => rs = (ret, ()) ∧ P) (fun _ _ _ _ => False)) :
    Eventually (A.T.mach.step cert.host)
      (fun st => A.T.mach.pc st = A.init.ra0 ∧ A.retGpr (A.T.mach.data st) = ret ∧ P)
      (A.T.mach.mkState
        (A.init.initState (as := [i64, i64, i64, i64, i64])
          (cert.bound "kissat_solve_bytes") (plainPayload cnfBytes) (plainArgs cnfBytes))
        (A.T.mach.labelAddr cert.host "kissat_solve_bytes")) := by
  have hfn := plain_mk_entry_fnspec_abi A cert hleg cert.host mainSpec hsound hno
    0 cert.code_infix_host cert.labelsUnique
  have ⟨locs, hlocs, _⟩ := A.argsIn_of_args5 (A.init_args5 0 [] 0#64 0#64 0#64 0#64 0#64)
  have hassign : (A.T.toIsa.assignArgs [i64, i64, i64, i64, i64]).isSome = true :=
    Option.isSome_iff_exists.mpr ⟨locs, hlocs⟩
  refine cert.run_fnSpec A.init hfn (plainPayload cnfBytes) (plainArgs cnfBytes)
    (Nat.le_trans hlen A.maxMem_ge) hassign hspec ?_ A.maxStack_ge
  rintro st (⟨hpc, _, _, ⟨rfl, hP⟩, hrets, _⟩ | ⟨_, _, _, _, hx, _⟩)
  · exact ⟨hpc, A.retGpr_eq_of_retsIn hrets, hP⟩
  · exact hx.elim

theorem plain_unsat_nv_abi (A : ArchKissatAbi)
    (cert : LinkedCert A.T A.L A.lt A.hcl plainModule [] [] 0 2048)
    (hleg : LegalSigAll A.lt plainModule.fns) :
    Eventually (A.T.mach.step cert.host)
      (fun st => A.T.mach.pc st = A.init.ra0 ∧
        A.retGpr (A.T.mach.data st) = 20#64 ∧ plainNvUnsatCnf.Unsat)
      (A.T.mach.mkState
        (A.init.initState (as := [i64, i64, i64, i64, i64])
          (cert.bound "kissat_solve_bytes")
          (plainPayload plainNvUnsatBytes) (plainArgs plainNvUnsatBytes))
        (A.T.mach.labelAddr cert.host "kissat_solve_bytes")) :=
  plain_nv_run_ret1 A cert hleg plainUnsatWitnessSpec plainUnsatEnv_sound
    (fun _ _ _ _ h => h) plainNvUnsatBytes
    (by simp [plainPayload_length, plainNvUnsatBytes])
    ⟨emp, rfl, rfl, rfl, by decide, by decide,
      by rw [sep_emp]; exact plainPayload_sep plainNvUnsatBytes (by decide),
      fun _ hu _ => ⟨rfl, hu⟩⟩

theorem plain_sat_nv_abi (A : ArchKissatAbi)
    (cert : LinkedCert A.T A.L A.lt A.hcl plainModule [] [] 0 2048)
    (hleg : LegalSigAll A.lt plainModule.fns) :
    Eventually (A.T.mach.step cert.host)
      (fun st => A.T.mach.pc st = A.init.ra0 ∧
        A.retGpr (A.T.mach.data st) = 10#64 ∧
        ¬ plainNvSatCnf.Unsat ∧ ∃ α, plainNvSatCnf.Sat α)
      (A.T.mach.mkState
        (A.init.initState (as := [i64, i64, i64, i64, i64])
          (cert.bound "kissat_solve_bytes")
          (plainPayload plainNvSatBytes) (plainArgs plainNvSatBytes))
        (A.T.mach.labelAddr cert.host "kissat_solve_bytes")) :=
  plain_nv_run_ret1 A cert hleg plainSatWitnessSpec plainSatEnv_sound
    (fun _ _ _ _ h => h) plainNvSatBytes
    (by simp [plainPayload_length, plainNvSatBytes])
    ⟨emp, rfl, rfl, rfl, by decide, by decide,
      by rw [sep_emp]; exact plainPayload_sep plainNvSatBytes (by decide),
      fun _ hnu hsat _ => ⟨rfl, hnu, hsat⟩⟩

end LeanQbe.T.Examples.Kissat.KissatPlainCertCommon
