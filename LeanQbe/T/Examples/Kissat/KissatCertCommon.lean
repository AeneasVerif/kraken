module

public import LeanQbe.T.MainCertInline
public import LeanQbe.T.Examples.Kissat.FullM6SatNv
public import LeanQbe.T.Examples.Kissat.FullM6SatSound
public import LeanQbe.T.Logic.MemLemmas
public import Std.Sat.CNF.Basic
public import Kraken.Mem
public import Kraken.Separation

/-!
# Arch-Free Kissat Certificate & ABI Deduplication Infrastructure (`KissatCertCommon`)

Centralizes architecture-independent helpers and generic UNSAT linking/top-level proof combinators
used by M8+ generated certificates (`Amd64.KissatAbi` / `Arm64.KissatAbi`, `0` dual-arch co-imports):
1. Deduplicated `m6Nv*` payload/bound helpers and `sep_exists_eq`.
2. `ArchKissatAbi`: ISA-agnostic ABI bridge over `Target` and `TargetInit`.
3. `solve_of_abi_fnspec`: generic `FnSpec` -> `Eventually (A.T.mach.step hh)` lift.
4. `KissatUnsatPkg` and generic `module_fnspec_of_abi`, `solve_bytes_unsat_of_abi`,
   `unsat_correct_of_abi`, `unsat_nonvacuous_of_abi`, `run_unsat_of_abi`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.KissatCertCommon

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open Kraken

/-! ## 1. Deduplicated `Mem` & `M6Nv` Payload Helpers -/

theorem sep_exists_eq {P Q : Mem 64 → Prop} {M : Mem 64}
    (h : (P ⋆ Q) M) : ∃ m : Mem 64, P m ∧ (Eq m ⋆ Q) M := by
  have hm := sep_mono (Q := Q)
    (fun x hx => (⟨x, ⟨hx, rfl⟩⟩ : ∃ m : Mem 64, P m ∧ Eq m x)) h
  rw [sep_ex_l] at hm
  obtain ⟨m, hm'⟩ := hm
  exact ⟨m, sep_pure_l (φ := P m) (P := Eq m) (R := Q).mp hm'⟩

@[expose] def m6NvWorkLen : Nat := 6144

theorem m6NvWorkLen_eq : m6NvWorkLen = 6144 := rfl

@[expose] def m6NvPayload (cnfBytes : List UInt8) : List UInt8 :=
  cnfBytes ++ List.replicate m6NvWorkLen 0

theorem m6NvPayload_eq (cnfBytes : List UInt8) :
    m6NvPayload cnfBytes = cnfBytes ++ List.replicate 6144 0 := rfl

theorem m6NvPayload_length (cnfBytes : List UInt8) :
    (m6NvPayload cnfBytes).length = cnfBytes.length + m6NvWorkLen := by
  simp only [m6NvPayload, List.length_append, List.length_replicate]

theorem m6NvPayload_sep (cnfBytes : List UInt8) (hcb : cnfBytes.length ≤ 2048) :
    (bytes nvM6CnfPtr cnfBytes ⋆ region (fullNvWorkPtr cnfBytes) m6NvWorkLen)
      ((m6NvPayload cnfBytes).At nvM6CnfPtr) :=
  nv_sep_append rfl
    (by unfold m6NvWorkLen; rw [List.length_replicate]; omega)
    rfl ⟨List.replicate m6NvWorkLen 0, List.length_replicate, rfl⟩

theorem m6Nv_unsat_bound :
    fullM6ExtBytes + fullFixedBytes 1 + 2 * 40 + 136 + 8 ≤ m6NvWorkLen := by
  unfold m6NvWorkLen fullM6ExtBytes fullFixedBytes valsBytes markBytes
    u32FullBytes fullMinDepthOf
  decide

/-! ## 2. `ArchKissatAbi` Structure & Generic `FnSpec` Lift -/

/-- Architecture-agnostic ABI bridge connecting `Target`/`TargetInit` semantics to
architecture-specific Kraken entry/exit predicates (`rdi..r8`/SysV x64 vs `X0..X4,X30`/AAPCS64). -/
structure ArchKissatAbi where
  T : Target
  L : TargetLayout T
  lt : LegalTarget
  hcl : Rega.LabelClean T.toIsa
  maxStack : Nat := 2048
  maxMem : Nat := 8192
  init : TargetInit T maxStack maxMem
  maxStack_ge : 2048 ≤ maxStack := by omega
  maxMem_ge : 8192 ≤ maxMem := by omega
  /-- Five-argument `i64` register ABI predicate `args5Ok s a0 a1 a2 a3 a4`. -/
  args5Ok : T.mach.MData → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Prop
  /-- Entry stack / link-register alignment predicate (`stackPre s ra`). -/
  stackPre : T.mach.MData → T.mach.Addr → Prop
  /-- Caller-side entry stack frame separation predicate (`entryFrame s ra b`). -/
  entryFrame : T.mach.MData → T.mach.Addr → Nat → Mem 64 → Prop
  /-- Return-side stack frame separation predicate (`exitFrame s b`). -/
  exitFrame : T.mach.MData → Nat → Mem 64 → Prop
  /-- Callee-saved registers & caller stack-pointer preservation (`calleeSpOk s_in s_out`). -/
  calleeSpOk : T.mach.MData → T.mach.MData → Prop
  /-- Primary `i64` GPR return value (`rax` on x64, `X0.toBitVec` on Arm64). -/
  retGpr : T.mach.MData → BitVec 64
  argsIn_of_args5 : ∀ {s a0 a1 a2 a3 a4},
    args5Ok s a0 a1 a2 a3 a4 →
    T.ArgsIn (as := [i64, i64, i64, i64, i64]) (a0, a1, a2, a3, a4, ()) s
  raReg_spEntry_of_stackPre : ∀ {s ra},
    stackPre s ra →
    T.frameSpec.raReg s ra ∧ T.frameSpec.spEntry (T.mach.getGpr s T.frame.sp)
  entry_of_entryFrame : ∀ {s ra b m},
    entryFrame s ra b m → T.Entry (T.mach.getGpr s T.frame.sp) ra b m
  entryFrame_of_entry : ∀ {s ra b m},
    T.Entry (T.mach.getGpr s T.frame.sp) ra b m → entryFrame s ra b m
  exitFrame_of_exit : ∀ {s b m},
    T.Exit (T.mach.getGpr s T.frame.sp) b m → exitFrame s b m
  calleeSpOk_of_restored : ∀ {s s'},
    T.Restored s s' → calleeSpOk s s'
  retGpr_eq_of_retsIn : ∀ {r : Val i64} {st},
    T.RetsIn (bs := [i64]) (r, ()) st → retGpr st = r
  init_args5 : ∀ b bs (a0 a1 a2 a3 a4 : BitVec 64),
    args5Ok (init.initState (as := [i64, i64, i64, i64, i64]) b bs (a0, a1, a2, a3, a4, ()))
      a0 a1 a2 a3 a4
  init_stackPre : ∀ b bs {as : List Ty} (args : Tup Val as),
    stackPre (init.initState b bs args) init.ra0

/-- Generic ABI-neutral `FnSpec` -> `Eventually` lift for non-exiting 5-arg `i64` solver entries. -/
theorem solve_of_abi_fnspec (A : ArchKissatAbi) (hh : A.T.mach.Host)
    (entryFn : Sym) {b : Nat} {spec : Spec [i64, i64, i64, i64, i64] [i64]}
    (hfnspec : A.T.FnSpec hh entryFn spec b 0)
    (cnf_ptr cnf_len work_ptr work_len fuel : BitVec 64)
    {m : Mem 64} {Q : Post [i64]}
    (hspec : spec (cnf_ptr, cnf_len, work_ptr, work_len, fuel, ()) m Q
      (fun _ _ _ _ => False))
    (s : A.T.mach.MData) (ra : A.T.mach.Addr) (R : Mem 64 → Prop)
    (hargs : A.args5Ok s cnf_ptr cnf_len work_ptr work_len fuel)
    (hsp : A.stackPre s ra)
    (hmem : (A.T.mach.mem s =⋆ Eq m ⋆ A.entryFrame s ra b ⋆ R)) :
    Eventually (A.T.mach.step hh)
      (fun st =>
        A.T.mach.pc st = ra ∧
        A.calleeSpOk s (A.T.mach.data st) ∧
        ∃ m', Q (A.retGpr (A.T.mach.data st), ()) m' ∧
          (A.T.mach.mem (A.T.mach.data st) =⋆
            Eq m' ⋆ A.exitFrame s b ⋆ R))
      (A.T.mach.mkState s (A.T.mach.labelAddr hh entryFn)) := by
  have ⟨hra, hspE⟩ := A.raReg_spEntry_of_stackPre hsp
  have hmem' : (A.T.mach.mem s =⋆ Eq m ⋆ A.T.Entry (A.T.mach.getGpr s A.T.frame.sp) ra b ⋆ R) :=
    sep_mono_mid (fun _ he => A.entry_of_entryFrame he) hmem
  refine eventually_weaken _ _ _ _ ?_
    (hfnspec (cnf_ptr, cnf_len, work_ptr, work_len, fuel, ()) m Q (fun _ _ _ _ => False)
      hspec s ra R (A.argsIn_of_args5 hargs) hra hspE hmem')
  rintro st (⟨hpc, rets, m', hQ, hrets, hrest, hm'⟩ | ⟨_, _, _, _, hx, _⟩)
  · rcases rets with ⟨r, ⟨⟩⟩
    have hret : A.retGpr (A.T.mach.data st) = r := A.retGpr_eq_of_retsIn hrets
    rw [hret]
    exact ⟨hpc, A.calleeSpOk_of_restored hrest, m', hQ,
      sep_mono_mid (fun _ hex => A.exitFrame_of_exit hex) hm'⟩
  · exact hx.elim

/-! ## 3. Generic Arch-Free `KissatUnsatPkg` & Top-Level UNSAT Theorems -/

/-- Canonical UNSAT + deterministic `UnitUnsatTrace` demand for `kissat_solve_bytes`. -/
@[expose] def CommonUnsatSolveReq
    (cnfBytes : List UInt8) (cnf_ptr work_ptr fuel : BitVec 64) (wlen : Nat)
    (R : Mem 64 → Prop) (Q : Post [i64]) : Prop :=
  ∀ r m',
    (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) →
    (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) →
    (∀ mv nc i0,
      cnf_ptr ≠ 0#64 → work_ptr ≠ 0#64 → 0 < fuel.toNat →
      fullM6ExtBytes + fullFixedBytes mv + nc * 40 + 136 + 8 ≤ wlen →
      i0 ≤ cnfBytes.length →
      parseHeader cnfBytes = some (mv, nc, cnfBytes.drop i0) →
      UnitUnsatTrace mv (List.replicate (2 * mv) 0#8) (cnfBytes.drop i0) nc →
      r = 20#64) →
    (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m' →
    Q (r, ()) m'

/-- Milestone-level arch-free UNSAT solver witness package (provided once per M8+ milestone). -/
structure KissatUnsatPkg where
  mod : Module
  inlPolicy : InlinePolicy
  entryFn : Sym := "kissat_solve_bytes"
  entryFn_fn : Fn
  entryFn_sig : entryFn_fn.name = entryFn ∧ entryFn_fn.as = [i64, i64, i64, i64, i64] ∧
    entryFn_fn.rs = [i64]
  entry_mem : entryFn_fn ∈ mod.fns
  env : Env
  moduleOk : ModuleOk env mod
  noExit : ∀ f ∈ mod.fns, ∀ args m Q X X',
    env f.name f.as f.rs args m Q X → env f.name f.as f.rs args m Q X'
  solve_intro : ∀ {cnf_ptr work_ptr fuel : BitVec 64} {cnfBytes : List UInt8}
    {wlen : Nat} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [i64]} {X : XPost},
    cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 →
    work_ptr.toNat + wlen < 2 ^ 64 →
    (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆ R) m →
    CommonUnsatSolveReq cnfBytes cnf_ptr work_ptr fuel wlen R Q →
    env entryFn [i64, i64, i64, i64, i64] [i64]
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr, BitVec.ofNat 64 wlen, fuel, ())
      m Q X

theorem module_fnspec_of_abi (A : ArchKissatAbi) (P : KissatUnsatPkg)
    (cert : LinkedCert A.T A.L A.lt A.hcl (P.mod.optInlinePolicy P.inlPolicy))
    (hleg : LegalSigAll A.lt P.mod.fns)
    (hh : A.T.mach.Host) (k₀ : Nat)
    (hc : cert.code.IsInfixAt (A.T.mach.prog hh) k₀) (hu : A.T.LabelsUnique hh)
    {f : Fn} (hf : f ∈ P.mod.fns) :
    A.T.Defined hh f.name ∧
      A.T.FnSpec hh f.name (P.env f.name f.as f.rs) (cert.bound f.name) 0 :=
  cert.fnSpec_noExit_of_legalSigAll_optInlinePolicy hh P.env k₀ hc hu
    P.moduleOk hleg hf (P.noExit f hf)

private theorem entryFn_spec_of_abi (A : ArchKissatAbi) (P : KissatUnsatPkg)
    (cert : LinkedCert A.T A.L A.lt A.hcl (P.mod.optInlinePolicy P.inlPolicy))
    (hleg : LegalSigAll A.lt P.mod.fns)
    (hh : A.T.mach.Host) (k₀ : Nat)
    (hc : cert.code.IsInfixAt (A.T.mach.prog hh) k₀) (hu : A.T.LabelsUnique hh) :
    A.T.FnSpec hh P.entryFn (P.env P.entryFn [i64, i64, i64, i64, i64] [i64])
      (cert.bound P.entryFn) 0 := by
  have hmem : ∀ f ∈ P.mod.fns,
      f.name = P.entryFn ∧ f.as = [i64, i64, i64, i64, i64] ∧ f.rs = [i64] →
      A.T.FnSpec hh P.entryFn (P.env P.entryFn [i64, i64, i64, i64, i64] [i64])
        (cert.bound P.entryFn) 0 := by
    rintro ⟨nm, as, rs, body⟩ hf ⟨rfl, rfl, rfl⟩
    exact (module_fnspec_of_abi A P cert hleg hh k₀ hc hu hf).2
  exact hmem P.entryFn_fn P.entry_mem P.entryFn_sig

theorem solve_bytes_unsat_of_abi (A : ArchKissatAbi) (P : KissatUnsatPkg)
    (cert : LinkedCert A.T A.L A.lt A.hcl (P.mod.optInlinePolicy P.inlPolicy))
    (hleg : LegalSigAll A.lt P.mod.fns)
    (hh : A.T.mach.Host) (k₀ : Nat)
    (hc : cert.code.IsInfixAt (A.T.mach.prog hh) k₀) (hu : A.T.LabelsUnique hh)
    (cnf_ptr work_ptr fuel : BitVec 64) (cnfBytes : List UInt8) (wlen : Nat)
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (s : A.T.mach.MData) (ra : A.T.mach.Addr) (R : Mem 64 → Prop)
    (hargs : A.args5Ok s cnf_ptr (BitVec.ofNat 64 cnfBytes.length) work_ptr
      (BitVec.ofNat 64 wlen) fuel)
    (hsp : A.stackPre s ra)
    (hmem : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
      A.entryFrame s ra (cert.bound P.entryFn) ⋆ R) (A.T.mach.mem s)) :
    Eventually (A.T.mach.step hh)
      (fun st =>
        A.T.mach.pc st = ra ∧
        (A.retGpr (A.T.mach.data st) = 0#64 ∨
          A.retGpr (A.T.mach.data st) = 10#64 ∨
          A.retGpr (A.T.mach.data st) = 20#64) ∧
        (A.retGpr (A.T.mach.data st) = 20#64 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        A.calleeSpOk s (A.T.mach.data st) ∧
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
          A.exitFrame s (cert.bound P.entryFn) ⋆ R) (A.T.mach.mem (A.T.mach.data st)))
      (A.T.mach.mkState s (A.T.mach.labelAddr hh P.entryFn)) := by
  have hfn := entryFn_spec_of_abi A P cert hleg hh k₀ hc hu
  have hm0 : ((bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen) ⋆
      (A.entryFrame s ra (cert.bound P.entryFn) ⋆ R)) (A.T.mach.mem s) := by
    rw [← sep_assoc]; exact hmem
  obtain ⟨m, hm_in, hm_dmem⟩ := sep_exists_eq hm0
  have hm_dmem' : (Eq m ⋆ A.entryFrame s ra (cert.bound P.entryFn) ⋆ R) (A.T.mach.mem s) := by
    rw [sep_assoc]; exact hm_dmem
  have hspec : P.env P.entryFn [i64, i64, i64, i64, i64] [i64]
      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr,
        BitVec.ofNat 64 wlen, fuel, ()) m
      (fun r m' =>
        (r.fst = 0#64 ∨ r.fst = 10#64 ∨ r.fst = 20#64) ∧
        (r.fst = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧
        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen) m')
      (fun _ _ _ _ => False) := by
    refine P.solve_intro (R := emp) hcfit hwfit (by rw [sep_emp]; exact hm_in) ?_
    intro r m' hdom hu _ hm'
    rw [sep_emp] at hm'
    exact ⟨hdom, hu, hm'⟩
  refine eventually_weaken _ _ _ _ ?_
    (solve_of_abi_fnspec A hh P.entryFn hfn cnf_ptr _ work_ptr _ fuel hspec s ra R
      hargs hsp hm_dmem')
  rintro st ⟨hpc, hcal, m', ⟨hdom, hu', hm'⟩, hst⟩
  rw [sep_assoc] at hst
  have hst' := sep_mono (fun _ heq => heq ▸ hm') hst
  rw [← sep_assoc] at hst'
  exact ⟨hpc, hdom, hu', hcal, hst'⟩

theorem unsat_correct_of_abi (A : ArchKissatAbi) (P : KissatUnsatPkg)
    (cert : LinkedCert A.T A.L A.lt A.hcl (P.mod.optInlinePolicy P.inlPolicy))
    (hleg : LegalSigAll A.lt P.mod.fns)
    (hh : A.T.mach.Host) (k₀ : Nat)
    (hc : cert.code.IsInfixAt (A.T.mach.prog hh) k₀) (hu : A.T.LabelsUnique hh)
    (cnf_ptr work_ptr fuel : BitVec 64) (cnfBytes : List UInt8) (wlen : Nat)
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_ptr.toNat + wlen < 2 ^ 64)
    (s : A.T.mach.MData) (ra : A.T.mach.Addr) (R : Mem 64 → Prop)
    (hargs : A.args5Ok s cnf_ptr (BitVec.ofNat 64 cnfBytes.length) work_ptr
      (BitVec.ofNat 64 wlen) fuel)
    (hsp : A.stackPre s ra)
    (hmem : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
      A.entryFrame s ra (cert.bound P.entryFn) ⋆ R) (A.T.mach.mem s)) :
    Eventually (A.T.mach.step hh)
      (fun st =>
        A.T.mach.pc st = ra ∧
        (A.retGpr (A.T.mach.data st) = 0#64 ∨
          A.retGpr (A.T.mach.data st) = 10#64 ∨
          A.retGpr (A.T.mach.data st) = 20#64) ∧
        (A.retGpr (A.T.mach.data st) = 20#64 →
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat))
      (A.T.mach.mkState s (A.T.mach.labelAddr hh P.entryFn)) :=
  eventually_weaken _ _ _ _ (fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (solve_bytes_unsat_of_abi A P cert hleg hh k₀ hc hu cnf_ptr work_ptr fuel cnfBytes wlen
      hcfit hwfit s ra R hargs hsp hmem)

theorem unsat_nonvacuous_of_abi (A : ArchKissatAbi) (P : KissatUnsatPkg)
    (cert : LinkedCert A.T A.L A.lt A.hcl (P.mod.optInlinePolicy P.inlPolicy))
    (hleg : LegalSigAll A.lt P.mod.fns)
    (hh : A.T.mach.Host) (k₀ : Nat)
    (hc : cert.code.IsInfixAt (A.T.mach.prog hh) k₀) (hu : A.T.LabelsUnique hh) :
    ∃ (cnf_ptr work_ptr fuel : BitVec 64) (cnfBytes : List UInt8) (wlen : Nat)
      (s : A.T.mach.MData) (ra : A.T.mach.Addr) (R : Mem 64 → Prop),
      cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧
      work_ptr.toNat + wlen < 2 ^ 64 ∧
      A.args5Ok s cnf_ptr (BitVec.ofNat 64 cnfBytes.length) work_ptr
        (BitVec.ofNat 64 wlen) fuel ∧
      A.stackPre s ra ∧
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
        A.entryFrame s ra (cert.bound P.entryFn) ⋆ R) (A.T.mach.mem s) ∧
      Eventually (A.T.mach.step hh)
        (fun st => A.T.mach.pc st = ra ∧ A.retGpr (A.T.mach.data st) = 20#64 ∧
          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat)
        (A.T.mach.mkState s (A.T.mach.labelAddr hh P.entryFn)) := by
  have hfn := entryFn_spec_of_abi A P cert hleg hh k₀ hc hu
  let b := cert.bound P.entryFn
  let bs := m6NvPayload nvM6UnsatBytes
  let args : Tup Val [i64, i64, i64, i64, i64] :=
    (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
      nvM6UnsatWorkPtr, BitVec.ofNat 64 m6NvWorkLen, 16#64, ())
  let s := A.init.initState (as := [i64, i64, i64, i64, i64]) b bs args
  have hcb_len : nvM6UnsatBytes.length ≤ 2048 := by decide
  have hbs_len : bs.length ≤ 8192 := by
    rw [m6NvPayload_length, m6NvWorkLen_eq]
    exact Nat.add_le_add_right hcb_len 6144
  have h1 := A.init.mem_entry b bs args
    (Nat.le_trans (cert.bound_le_max _) A.maxStack_ge)
    (Nat.le_trans hbs_len A.maxMem_ge)
  rw [← A.init.get_sp b bs args] at h1
  have h1' : (Eq (bs.At 0x1000#64) ⋆ A.entryFrame s A.init.ra0 b ⋆ emp) (A.T.mach.mem s) :=
    sep_mono_mid (fun _ he => A.entryFrame_of_entry he) h1
  have hdm : (bytes nvM6CnfPtr nvM6UnsatBytes ⋆
      region nvM6UnsatWorkPtr m6NvWorkLen ⋆
      A.entryFrame s A.init.ra0 b ⋆ emp) (A.T.mach.mem s) := by
    refine sep_mono (fun _ => sep_mono (fun _ heq => ?_)) h1'
    rw [← heq, nvM6UnsatWorkPtr_eq_fullNvWorkPtr]
    exact m6NvPayload_sep nvM6UnsatBytes hcb_len
  have hargs := A.init_args5 b bs nvM6CnfPtr (BitVec.ofNat 64 nvM6UnsatBytes.length)
    nvM6UnsatWorkPtr (BitVec.ofNat 64 m6NvWorkLen) 16#64
  have hsp := A.init_stackPre b bs args
  refine ⟨nvM6CnfPtr, nvM6UnsatWorkPtr, 16#64, nvM6UnsatBytes, m6NvWorkLen,
    s, A.init.ra0, emp, by decide, by decide, hargs, hsp, hdm, ?_⟩
  have hspec : P.env P.entryFn [i64, i64, i64, i64, i64] [i64]
      args (bs.At 0x1000#64) (fun r _ => r.fst = 20#64 ∧ nvM6UnsatCnf.Unsat)
      (fun _ _ _ _ => False) := by
    refine P.solve_intro (R := emp) (by decide) (by decide) ?_ ?_
    · rw [sep_emp, nvM6UnsatWorkPtr_eq_fullNvWorkPtr]
      exact m6NvPayload_sep nvM6UnsatBytes (by decide)
    · intro r _ _ _ htr _
      exact ⟨htr 1 2 9 (by decide) (by decide) (by decide) m6Nv_unsat_bound
        (by decide) nvM6Unsat_header nvM6Unsat_unitTrace, nvM6UnsatCnf_unsat⟩
  have hev := solve_of_abi_fnspec A hh P.entryFn hfn nvM6CnfPtr _
    nvM6UnsatWorkPtr _ 16#64 hspec s A.init.ra0 emp hargs hsp h1'
  exact eventually_weaken _ _ _ _
    (fun _ ⟨hpc, _, _, ⟨h20, huns⟩, _⟩ =>
      ⟨hpc, h20, nvM6UnsatCnf, parseDimacs_nvM6UnsatBytes, huns⟩)
    hev

theorem run_unsat_of_abi (A : ArchKissatAbi) (P : KissatUnsatPkg)
    (cert : LinkedCert A.T A.L A.lt A.hcl (P.mod.optInlinePolicy P.inlPolicy))
    (hleg : LegalSigAll A.lt P.mod.fns) :
    Eventually (A.T.mach.step cert.host)
      (fun st =>
        A.T.mach.pc st = A.init.ra0 ∧
        A.T.mach.getGpr (A.T.mach.data st) A.init.ret0 = 20#64 ∧
        (A.T.mach.mem (A.T.mach.data st) =⋆
          (fun m' => nvM6UnsatCnf.Unsat ∧
            (bytes nvM6CnfPtr nvM6UnsatBytes ⋆
              region nvM6UnsatWorkPtr m6NvWorkLen ⋆ emp) m') ⋆
          A.T.Exit A.init.sp0 (cert.bound P.entryFn) ⋆ emp))
      (A.T.mach.mkState
        (A.init.initState (as := [i64, i64, i64, i64, i64])
          (cert.bound P.entryFn)
          (m6NvPayload nvM6UnsatBytes)
          (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
            nvM6UnsatWorkPtr, BitVec.ofNat 64 m6NvWorkLen, 16#64, ()))
        (A.T.mach.labelAddr cert.host P.entryFn)) := by
  have ⟨locs, hlocs, _⟩ := A.argsIn_of_args5 (A.init_args5 0 [] 0#64 0#64 0#64 0#64 0#64)
  have hassign : (A.T.toIsa.assignArgs [i64, i64, i64, i64, i64]).isSome = true :=
    Option.isSome_iff_exists.mpr ⟨locs, hlocs⟩
  have hcb_len : nvM6UnsatBytes.length ≤ 2048 := by decide
  have hbs_len : (m6NvPayload nvM6UnsatBytes).length ≤ 8192 := by
    rw [m6NvPayload_length, m6NvWorkLen_eq]
    exact Nat.add_le_add_right hcb_len 6144
  have hrun : ∀ f ∈ P.mod.fns,
      f.name = P.entryFn ∧ f.as = [i64, i64, i64, i64, i64] ∧ f.rs = [i64] →
      Eventually (A.T.mach.step cert.host)
        (fun st =>
          A.T.mach.pc st = A.init.ra0 ∧
          A.T.mach.getGpr (A.T.mach.data st) A.init.ret0 = 20#64 ∧
          (A.T.mach.mem (A.T.mach.data st) =⋆
            (fun m' => nvM6UnsatCnf.Unsat ∧
              (bytes nvM6CnfPtr nvM6UnsatBytes ⋆
                region nvM6UnsatWorkPtr m6NvWorkLen ⋆ emp) m') ⋆
            A.T.Exit A.init.sp0 (cert.bound P.entryFn) ⋆ emp))
        (A.T.mach.mkState
          (A.init.initState (as := [i64, i64, i64, i64, i64])
            (cert.bound P.entryFn)
            (m6NvPayload nvM6UnsatBytes)
            (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
              nvM6UnsatWorkPtr, BitVec.ofNat 64 m6NvWorkLen, 16#64, ()))
          (A.T.mach.labelAddr cert.host P.entryFn)) := by
    rintro ⟨nm, as, rs, body⟩ hfn_mem ⟨rfl, rfl, rfl⟩
    refine cert.eventually_ret1_sep_i64_of_legalSigAll_optInlinePolicy
      A.init
      P.env P.moduleOk hleg hfn_mem rfl
      (P.noExit ⟨P.entryFn, [i64, i64, i64, i64, i64], [i64], body⟩ hfn_mem)
      (m6NvPayload nvM6UnsatBytes)
      (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,
        nvM6UnsatWorkPtr, BitVec.ofNat 64 m6NvWorkLen, 16#64, ())
      20#64
      (fun m' => nvM6UnsatCnf.Unsat ∧
        (bytes nvM6CnfPtr nvM6UnsatBytes ⋆
          region nvM6UnsatWorkPtr m6NvWorkLen ⋆ emp) m')
      (Nat.le_trans hbs_len A.maxMem_ge)
      hassign
      (Q := fun r m' => r = (20#64, ()) ∧ nvM6UnsatCnf.Unsat ∧
        (bytes nvM6CnfPtr nvM6UnsatBytes ⋆
          region nvM6UnsatWorkPtr m6NvWorkLen ⋆ emp) m')
      ?_ (fun _ _ h => h) A.maxStack_ge
    refine P.solve_intro (R := emp) (by decide) (by decide) ?_ ?_
    · rw [sep_emp, nvM6UnsatWorkPtr_eq_fullNvWorkPtr]
      exact m6NvPayload_sep nvM6UnsatBytes hcb_len
    · intro _ m' _ _ htr hm'
      exact ⟨congrArg (·, ()) (htr 1 2 9 (by decide) (by decide) (by decide) m6Nv_unsat_bound
        (by decide) nvM6Unsat_header nvM6Unsat_unitTrace), nvM6UnsatCnf_unsat, hm'⟩
  exact hrun P.entryFn_fn P.entry_mem P.entryFn_sig

end LeanQbe.T.Examples.Kissat.KissatCertCommon
