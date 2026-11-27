module

public import LeanQbe.T.MainLemmas
public import LeanQbe.T.LinkRecLemmas
public import LeanQbe.T.MainCertProof
import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.FlatLemmas
import all Kraken.Mem
import all Kraken.Separation

/-!
# Target-Generic Verification Kit (`BenchmarkCertKit`)

Arch-neutral separation-logic extraction, `LegalTarget.legalSig` helpers for `i64` signatures,
`LinkedCert` -> `Compiled` bridges, `BenchAbi` abstraction, and generic `FnSpec`/`TargetInit`
combinators shared across `Amd64` and `Arm64` certified modules (`0` `Amd64`/`Arm64`/`Kraken.X64`/
`Kraken.AArch64` imports).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.BenchmarkCertKit

open Std Std.ExtHashMap
open LeanQbe.T LeanQbe.T.LinkRec Kraken

/-! ## 1. Separation-Logic, Signature, & Single-Function Helpers -/

/-- Extract the concrete heap chunk `m` satisfying `P m` from `dmem =⋆ P ⋆ F ⋆ R`. -/
theorem sep_extract_eq {dmem : Mem 64} {P F R : Mem 64 → Prop}
    (hmem : dmem =⋆ P ⋆ F ⋆ R) :
    ∃ m : Mem 64, P m ∧ (dmem =⋆ Eq m ⋆ F ⋆ R) := by
  obtain ⟨mf, mR, hu1, hd1, ⟨m, f, hu2, hd2, hm, hf⟩, hmR⟩ := hmem
  exact ⟨m, hm, ⟨mf, mR, hu1, hd1, ⟨m, f, hu2, hd2, rfl, hf⟩, hmR⟩⟩

theorem legalSig_singleton_i64_tys {lt : LegalTarget} (hi64 : lt.legalSig [i64] = [i64]) :
    lt.legalTys i64 = [i64] := by
  simpa only [LegalTarget.legalSig, List.append_nil] using hi64

theorem legalSig_two_i64 {lt : LegalTarget} (hi64 : lt.legalSig [i64] = [i64]) :
    lt.legalSig [i64, i64] = [i64, i64] := by
  simp only [LegalTarget.legalSig, legalSig_singleton_i64_tys hi64, List.cons_append,
    List.nil_append]

theorem legalSig_three_i64 {lt : LegalTarget} (hi64 : lt.legalSig [i64] = [i64]) :
    lt.legalSig [i64, i64, i64] = [i64, i64, i64] := by
  simp only [LegalTarget.legalSig, legalSig_singleton_i64_tys hi64, List.cons_append,
    List.nil_append]

theorem legalSig_five_i64 {lt : LegalTarget} (hi64 : lt.legalSig [i64] = [i64]) :
    lt.legalSig [i64, i64, i64, i64, i64] = [i64, i64, i64, i64, i64] := by
  simp only [LegalTarget.legalSig, legalSig_singleton_i64_tys hi64, List.cons_append,
    List.nil_append]

theorem legalSig_six_i64 {lt : LegalTarget} (hi64 : lt.legalSig [i64] = [i64]) :
    lt.legalSig [i64, i64, i64, i64, i64, i64] = [i64, i64, i64, i64, i64, i64] := by
  simp only [LegalTarget.legalSig, legalSig_singleton_i64_tys hi64, List.cons_append,
    List.nil_append]

/-- Generic closed `FnSpec` wrapper for single-function modules `{ fns := [f] }`. -/
theorem single_fnspec_gen {T : Target} {lt : LegalTarget} {maxBound : Nat}
    {f : Fn} {hints : List T.toIsa.Hints}
    (M : Compiled T lt [] [] 0 [f] hints maxBound)
    (hh : T.mach.Host) (Γ : Env)
    (hacyc : ({ fns := [f], externs := [], exits := [] } : Module).checkAcyclic = true)
    (hwf : f.Wf)
    (hsupp : (f.earlyOpt).body.supportsSource lt = true)
    (hwp : ∀ xs m Q X, Γ f.name f.as f.rs xs m Q X → Func.wp Γ f.body xs m Q X)
    (k₀ : Nat) (hc : M.code.IsInfixAt (T.mach.prog hh) k₀) (hu : T.LabelsUnique hh)
    (has : lt.legalSig f.as = f.as) (hrs : lt.legalSig f.rs = f.rs)
    (hnoex : ∀ args m Q X X',
      Γ f.name f.as f.rs args m Q X → Γ f.name f.as f.rs args m Q X') :
    T.Defined hh f.name ∧ T.FnSpec hh f.name (Γ f.name f.as f.rs) (M.bound f.name) 0 :=
  M.fnSpec_noExit_id ⟨[f], [], []⟩ rfl hh Γ k₀ hc hu hacyc
    (fun g hg => by simp only [List.mem_singleton] at hg; subst hg; exact hwf)
    (fun g hg => by simp only [List.mem_singleton] at hg; subst hg; exact hsupp)
    (fun g hg => by simp only [List.mem_singleton] at hg; subst hg; exact hwp)
    List.mem_cons_self has hrs hnoex

/-- Target-generic concrete heap non-vacuous execution witness over `TargetInit.run_fnSpec`. -/
theorem run_sep_nonvacuous {T : Target} (I : TargetInit T 2048 8192)
    {lt : LegalTarget} {as : List Ty} {hints : List T.toIsa.Hints} {fns : List Fn}
    (M : Compiled T lt [] [] 0 fns hints 2048) {sym : Sym} {spec : Spec as []}
    (hfn : T.FnSpec M.host sym spec (M.bound sym) 0)
    (bytes : List UInt8) (xs : Tup Val as) (hlen : bytes.length ≤ 8192)
    (hargs : (T.toIsa.assignArgs as).isSome = true)
    {P : Mem 64 → Prop}
    (hspec : spec xs (bytes.At 0x1000#64) (fun _ m' => P m') (fun _ _ _ _ => False)) :
    Eventually (T.mach.step M.host)
      (fun st => T.mach.pc st = I.ra0 ∧
        (T.mach.mem (T.mach.data st) =⋆ P ⋆ T.Exit I.sp0 (M.bound sym) ⋆ emp))
      (T.mach.mkState (I.initState (M.bound sym) bytes xs) (T.mach.labelAddr M.host sym)) := by
  refine I.run_fnSpec M hfn bytes xs hlen hargs hspec ?_
  rintro st (⟨hpc, _, m', hP, _, hm'⟩ | ⟨_, _, _, _, hx, _⟩)
  · exact ⟨hpc, sep_mono (fun _ => sep_mono (fun _ e => e ▸ hP)) hm'⟩
  · exact hx.elim

/-! ## 2. `LinkedCert` to Literal-Backed `Compiled` Bridge -/

theorem linkedCert_compileModule {T : Target} {L : TargetLayout T} {lt : LegalTarget}
    {hcl : Rega.LabelClean T.toIsa} {mod : Module} {ext₀ : List (SigEntry × Nat)}
    {exits : List Sym} {nX maxB : Nat}
    (cert : LinkedCert T L lt hcl mod ext₀ exits nX maxB) :
    compileModule T.toIsa lt T.frame.raBytes ext₀ exits nX mod.fns (chunksHints cert.chunks) =
      .ok (cert.code, cert.bounds) := by
  rw [show mod.fns = chunksFns cert.chunks from cert.fns_eq]
  exact cert.compiled.compileModule_eq

theorem linkedCert_checkLit {T : Target} {L : TargetLayout T} {lt : LegalTarget}
    {hcl : Rega.LabelClean T.toIsa} {mod : Module} {exits : List Sym} {nX maxB : Nat}
    (cert : LinkedCert T L lt hcl mod [] exits nX maxB) :
    checkCompileLit T.frame.label L.progSmall cert.code cert.bounds
      (mod.fns.map Fn.name) exits maxB = true := by
  have hlink := cert.linkCheck
  simp only [checkLinkList, Bool.and_eq_true] at hlink
  have hfns : mod.fns = chunksFns cert.chunks := cert.fns_eq
  have hnd : (cert.compiled.bounds.map Prod.fst).Nodup := by
    rw [compileModule_bounds_names cert.compiled.compileModule_eq]
    exact (List.nodup_append.mp (checkLinkList_parts cert.linkCheck).2.2.2.1).1
  simp only [checkCompileLit, checkCompileResult, Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [hfns]; exact hlink.1.1.1.2
  · exact hlink.1.1.2
  · rw [hfns]; exact hlink.1.2
  · exact hlink.2
  · refine List.all_eq_true.mpr fun p hp => Nat.ble_eq.mpr ?_
    have hlk := lookupFnBound_of_mem_nodup hnd hp
    have hle := cert.bound_le_max p.1
    simpa [LinkedCert.bound, Compiled.bound, hlk] using hle
  · rw [hfns]
    refine List.all_eq_true.mpr fun nm hnm => ?_
    cases hlk : lookupFnBound cert.bounds nm with
    | some _ => rfl
    | none =>
      simp only [lookupFnBound, Option.map_eq_none_iff, List.find?_eq_none] at hlk
      exact absurd (beq_self_eq_true nm) (hlk _ (cert.compiled.bound_mem hnm))

theorem linkedCert_checkCompile {T : Target} {L : TargetLayout T} {lt : LegalTarget}
    {hcl : Rega.LabelClean T.toIsa} {mod : Module} {exits : List Sym} {nX maxB : Nat}
    (cert : LinkedCert T L lt hcl mod [] exits nX maxB) :
    checkCompile T L lt [] exits nX mod.fns (chunksHints cert.chunks) maxB = true := by
  unfold checkCompile
  rw [linkedCert_compileModule cert]
  exact linkedCert_checkLit cert

/-- Convert a zero-extern `LinkedCert` to a literal-backed `Compiled` bundle with zero
recompilation. -/
@[expose] noncomputable def linkedCert_to_compiled {T : Target} {L : TargetLayout T}
    {lt : LegalTarget} {hcl : Rega.LabelClean T.toIsa} {mod : Module}
    {exits : List Sym} {nX maxB : Nat}
    (cert : LinkedCert T L lt hcl mod [] exits nX maxB) :
    Compiled T lt [] exits nX mod.fns (chunksHints cert.chunks) maxB :=
  compileCheckedLit T L lt hcl [] exits nX mod.fns (chunksHints cert.chunks) maxB
    cert.code cert.bounds (linkedCert_compileModule cert) (linkedCert_checkLit cert)

/-! ## 3. Architecture-Neutral `BenchAbi` & Generic `Eventually` Lifts -/

/-- Architecture-agnostic ABI bridge connecting `Target`/`TargetInit` semantics to
ISA-specific Kraken machine-state predicates (`rdi..r9`/`rsp`/`rax` on x64 vs
`X0..X5`/`SP`/`X30` on Arm64) with separate `calleeSavedOk` and `spRestored` fields so
right-associated conjunctions unify definitionally with concrete ISA theorem statements. -/
structure BenchAbi where
  T : Target
  L : TargetLayout T
  lt : LegalTarget
  hcl : Rega.LabelClean T.toIsa
  maxStack : Nat := 2048
  maxMem : Nat := 8192
  init : TargetInit T maxStack maxMem
  maxStack_ge : 2048 ≤ maxStack := by omega
  maxMem_ge : 8192 ≤ maxMem := by omega
  legalSig_i64 : lt.legalSig [i64] = [i64]
  assignArgs_i64 : ∀ n ≤ 6, (T.toIsa.assignArgs (List.replicate n i64)).isSome = true
  /-- Read the `i`-th `i64` argument register (`i < 6`) from machine data. -/
  argAt : Fin 6 → T.mach.MData → BitVec 64
  /-- Entry stack / link-register alignment predicate (`stackPre s ra`). -/
  stackPre : T.mach.MData → T.mach.Addr → Prop
  /-- Exit-site stack alignment predicate (`exitSpOk stData`). -/
  exitSpOk : T.mach.MData → Prop
  /-- Caller-side entry stack frame separation predicate (`entryFrame s ra b`). -/
  entryFrame : T.mach.MData → T.mach.Addr → Nat → Mem 64 → Prop
  /-- Return-side stack frame separation predicate (`exitFrame s b`). -/
  exitFrame : T.mach.MData → Nat → Mem 64 → Prop
  /-- Initial-state exit stack frame predicate (`initExitFrame b`). -/
  initExitFrame : Nat → Mem 64 → Prop
  /-- Callee-saved register preservation (`calleeSavedOk s_in s_out`). -/
  calleeSavedOk : T.mach.MData → T.mach.MData → Prop
  /-- Stack pointer restoration (`spRestored s_in s_out`). -/
  spRestored : T.mach.MData → T.mach.MData → Prop
  /-- Primary `i64` GPR return value (`rax` on x64, `X0.toBitVec` on Arm64). -/
  retGpr : T.mach.MData → BitVec 64
  argsIn_1 : ∀ {s a0}, argAt 0 s = a0 → T.ArgsIn (as := [i64]) (a0, ()) s
  argsIn_2 : ∀ {s a0 a1}, argAt 0 s = a0 → argAt 1 s = a1 →
    T.ArgsIn (as := [i64, i64]) (a0, a1, ()) s
  argsIn_3 : ∀ {s a0 a1 a2}, argAt 0 s = a0 → argAt 1 s = a1 → argAt 2 s = a2 →
    T.ArgsIn (as := [i64, i64, i64]) (a0, a1, a2, ()) s
  argsIn_5 : ∀ {s a0 a1 a2 a3 a4}, argAt 0 s = a0 → argAt 1 s = a1 → argAt 2 s = a2 →
    argAt 3 s = a3 → argAt 4 s = a4 →
    T.ArgsIn (as := [i64, i64, i64, i64, i64]) (a0, a1, a2, a3, a4, ()) s
  argsIn_6 : ∀ {s a0 a1 a2 a3 a4 a5}, argAt 0 s = a0 → argAt 1 s = a1 → argAt 2 s = a2 →
    argAt 3 s = a3 → argAt 4 s = a4 → argAt 5 s = a5 →
    T.ArgsIn (as := [i64, i64, i64, i64, i64, i64]) (a0, a1, a2, a3, a4, a5, ()) s
  raReg_spEntry_of_stackPre : ∀ {s ra},
    stackPre s ra →
    T.frameSpec.raReg s ra ∧ T.frameSpec.spEntry (T.mach.getGpr s T.frame.sp)
  entry_of_entryFrame : ∀ {s ra b m},
    entryFrame s ra b m → T.Entry (T.mach.getGpr s T.frame.sp) ra b m
  exitFrame_of_exit : ∀ {s b m},
    T.Exit (T.mach.getGpr s T.frame.sp) b m → exitFrame s b m
  initExitFrame_of_exit : ∀ {b m},
    T.Exit init.sp0 b m → initExitFrame b m
  calleeSavedOk_of_restored : ∀ {s s'}, T.Restored s s' → calleeSavedOk s s'
  spRestored_of_restored : ∀ {s s'}, T.Restored s s' → spRestored s s'
  retGpr_eq_of_retsIn : ∀ {r : Val i64} {st},
    T.RetsIn (bs := [i64]) (r, ()) st → retGpr st = r
  arg0_eq_of_argsIn : ∀ {v : Val i64} {st},
    T.ArgsIn (as := [i64]) (v, ()) st → argAt 0 st = v
  exitSpOk_of_spEntry : ∀ {st},
    T.frameSpec.spEntry (T.mach.getGpr st T.frame.sp) → exitSpOk st

section AbiLifts

variable (A : BenchAbi)

/-- Generic `FnSpec` -> `Eventually` lift for potentially-exiting empty-heap calls. -/
theorem abi_of_call_emp (hh : A.T.mach.Host) {sym : Sym} {b nX : Nat} {as bs : List Ty}
    {spec : Spec as bs} (hfn : A.T.FnSpec hh sym spec b nX)
    {args : Tup Val as} {Q : Post bs} {X : XPost} (hspec : spec args ∅ Q X)
    (s : A.T.mach.MData) (ra : A.T.mach.Addr) (R : Mem 64 → Prop)
    (hargs : A.T.ArgsIn args s) (hsp : A.stackPre s ra)
    (hmem : (A.entryFrame s ra b ⋆ R) (A.T.mach.mem s)) :
    Eventually (A.T.mach.step hh)
      (fun st =>
        (A.T.mach.pc st = ra ∧
          A.calleeSavedOk s (A.T.mach.data st) ∧
          A.spRestored s (A.T.mach.data st) ∧
          ∃ rets m', Q rets m' ∧ A.T.RetsIn rets (A.T.mach.data st) ∧
            (A.T.mach.mem (A.T.mach.data st) =⋆ Eq m' ⋆ A.exitFrame s b ⋆ R)) ∨
        (∃ (sym' : Sym) (cs : List Ty) (xs : Tup Val cs) (m' : Mem 64),
          X sym' cs xs m' ∧ A.T.Defined hh sym' ∧
          A.T.mach.pc st = A.T.mach.labelAddr hh sym' ∧
          A.T.ArgsIn xs (A.T.mach.data st) ∧ A.exitSpOk (A.T.mach.data st)))
      (A.T.mach.mkState s (A.T.mach.labelAddr hh sym)) := by
  have ⟨hra, hspE⟩ := A.raReg_spEntry_of_stackPre hsp
  have hmem' : (A.T.mach.mem s =⋆ Eq (∅ : Mem 64) ⋆
      A.T.Entry (A.T.mach.getGpr s A.T.frame.sp) ra b ⋆ R) := by
    rw [eq_empty_eq_emp, emp_sep]
    exact sep_mono (fun _ he => A.entry_of_entryFrame he) hmem
  refine eventually_weaken _ _ _ _ ?_
    (hfn args ∅ Q X hspec s ra R hargs hra hspE hmem')
  rintro st (⟨hpc, rets, m', hQ, hrets, hrest, hm'⟩ |
    ⟨sym', cs, xs, m', hX, hdef, hpc, has, hsp', _⟩)
  · exact Or.inl ⟨hpc, A.calleeSavedOk_of_restored hrest, A.spRestored_of_restored hrest,
      rets, m', hQ, hrets, sep_mono_mid (fun _ hex => A.exitFrame_of_exit hex) hm'⟩
  · exact Or.inr ⟨sym', cs, xs, m', hX, hdef, hpc, has, A.exitSpOk_of_spEntry hsp'⟩

/-- Generic non-exiting `FnSpec` -> `Eventually` lift over `Eq m ⋆ entryFrame`. -/
theorem abi_of_returns (hh : A.T.mach.Host) {sym : Sym} {b nX : Nat} {as bs : List Ty}
    {spec : Spec as bs} (hfn : A.T.FnSpec hh sym spec b nX)
    {args : Tup Val as} {m : Mem 64} {Q : Post bs}
    (hspec : spec args m Q (fun _ _ _ _ => False))
    (s : A.T.mach.MData) (ra : A.T.mach.Addr) (R : Mem 64 → Prop)
    (hargs : A.T.ArgsIn args s) (hsp : A.stackPre s ra)
    (hmem : (A.T.mach.mem s =⋆ Eq m ⋆ A.entryFrame s ra b ⋆ R)) :
    Eventually (A.T.mach.step hh)
      (fun st =>
        A.T.mach.pc st = ra ∧
        A.calleeSavedOk s (A.T.mach.data st) ∧
        A.spRestored s (A.T.mach.data st) ∧
        ∃ rets m', Q rets m' ∧ A.T.RetsIn rets (A.T.mach.data st) ∧
          (A.T.mach.mem (A.T.mach.data st) =⋆ Eq m' ⋆ A.exitFrame s b ⋆ R))
      (A.T.mach.mkState s (A.T.mach.labelAddr hh sym)) := by
  have ⟨hra, hspE⟩ := A.raReg_spEntry_of_stackPre hsp
  have hmem' : (A.T.mach.mem s =⋆ Eq m ⋆
      A.T.Entry (A.T.mach.getGpr s A.T.frame.sp) ra b ⋆ R) :=
    sep_mono_mid (fun _ he => A.entry_of_entryFrame he) hmem
  refine eventually_weaken _ _ _ _ ?_
    (hfn args m Q (fun _ _ _ _ => False) hspec s ra R hargs hra hspE hmem')
  rintro st (⟨hpc, rets, m', hQ, hrets, hrest, hm'⟩ | ⟨_, _, _, _, hx, _⟩)
  · exact ⟨hpc, A.calleeSavedOk_of_restored hrest, A.spRestored_of_restored hrest,
      rets, m', hQ, hrets, sep_mono_mid (fun _ hex => A.exitFrame_of_exit hex) hm'⟩
  · exact hx.elim

/-- Specialization of `abi_of_returns` for `rs = []` transforming heap `P` into `P'`. -/
theorem abi_of_returns_sep0 (hh : A.T.mach.Host) {sym : Sym} {b nX : Nat} {as : List Ty}
    {spec : Spec as []} (hfn : A.T.FnSpec hh sym spec b nX)
    {args : Tup Val as} {P P' : Mem 64 → Prop}
    (s : A.T.mach.MData) (ra : A.T.mach.Addr) (R : Mem 64 → Prop)
    (hargs : A.T.ArgsIn args s) (hsp : A.stackPre s ra)
    (hmem : (A.T.mach.mem s =⋆ P ⋆ A.entryFrame s ra b ⋆ R))
    (hspec : ∀ m, P m → spec args m (fun _ m' => P' m') (fun _ _ _ _ => False)) :
    Eventually (A.T.mach.step hh)
      (fun st =>
        A.T.mach.pc st = ra ∧
        A.calleeSavedOk s (A.T.mach.data st) ∧
        A.spRestored s (A.T.mach.data st) ∧
        (A.T.mach.mem (A.T.mach.data st) =⋆ P' ⋆ A.exitFrame s b ⋆ R))
      (A.T.mach.mkState s (A.T.mach.labelAddr hh sym)) := by
  obtain ⟨m, hm, hmEq⟩ := sep_extract_eq hmem
  refine eventually_weaken _ _ _ _ ?_
    (abi_of_returns A hh hfn (hspec m hm) s ra R hargs hsp hmEq)
  rintro st ⟨hpc, hcs, hsp', _, m', hP', _, hm'⟩
  exact ⟨hpc, hcs, hsp', sep_mono (fun _ => sep_mono (fun _ e => e ▸ hP')) hm'⟩

/-- Specialization of `abi_of_returns` for `rs = [i64]` returning `v` and establishing `P'`. -/
theorem abi_of_returns_ret1_sep (hh : A.T.mach.Host) {sym : Sym} {b nX : Nat} {as : List Ty}
    {spec : Spec as [i64]} (hfn : A.T.FnSpec hh sym spec b nX)
    {args : Tup Val as} {v : BitVec 64} {P P' : Mem 64 → Prop}
    (s : A.T.mach.MData) (ra : A.T.mach.Addr) (R : Mem 64 → Prop)
    (hargs : A.T.ArgsIn args s) (hsp : A.stackPre s ra)
    (hmem : (A.T.mach.mem s =⋆ P ⋆ A.entryFrame s ra b ⋆ R))
    (hspec : ∀ m, P m →
      spec args m (fun r m' => r = (v, ()) ∧ P' m') (fun _ _ _ _ => False)) :
    Eventually (A.T.mach.step hh)
      (fun st =>
        A.T.mach.pc st = ra ∧
        A.retGpr (A.T.mach.data st) = v ∧
        A.calleeSavedOk s (A.T.mach.data st) ∧
        A.spRestored s (A.T.mach.data st) ∧
        (A.T.mach.mem (A.T.mach.data st) =⋆ P' ⋆ A.exitFrame s b ⋆ R))
      (A.T.mach.mkState s (A.T.mach.labelAddr hh sym)) := by
  obtain ⟨m, hm, hmEq⟩ := sep_extract_eq hmem
  refine eventually_weaken _ _ _ _ ?_
    (abi_of_returns A hh hfn (hspec m hm) s ra R hargs hsp hmEq)
  rintro st ⟨hpc, hcs, hsp', _, m', ⟨rfl, hP'⟩, hrets, hm'⟩
  exact ⟨hpc, A.retGpr_eq_of_retsIn hrets, hcs, hsp',
    sep_mono (fun _ => sep_mono (fun _ e => e ▸ hP')) hm'⟩

/-- Specialization of `abi_of_call_emp` for non-exiting empty-heap `rs = [i64]` returning `v`. -/
theorem abi_of_returns_ret1_emp (hh : A.T.mach.Host) {sym : Sym} {b nX : Nat} {as : List Ty}
    {spec : Spec as [i64]} (hfn : A.T.FnSpec hh sym spec b nX)
    {args : Tup Val as} {v : BitVec 64}
    (hspec : spec args ∅ (fun r m' => r = (v, ()) ∧ emp m') (fun _ _ _ _ => False))
    (s : A.T.mach.MData) (ra : A.T.mach.Addr) (R : Mem 64 → Prop)
    (hargs : A.T.ArgsIn args s) (hsp : A.stackPre s ra)
    (hmem : (A.entryFrame s ra b ⋆ R) (A.T.mach.mem s)) :
    Eventually (A.T.mach.step hh)
      (fun st =>
        A.T.mach.pc st = ra ∧
        A.retGpr (A.T.mach.data st) = v ∧
        A.calleeSavedOk s (A.T.mach.data st) ∧
        A.spRestored s (A.T.mach.data st) ∧
        (A.T.mach.mem (A.T.mach.data st) =⋆ A.exitFrame s b ⋆ R))
      (A.T.mach.mkState s (A.T.mach.labelAddr hh sym)) := by
  refine eventually_weaken _ _ _ _ ?_
    (abi_of_call_emp A hh hfn hspec s ra R hargs hsp hmem)
  rintro st (⟨hpc, hcs, hsp', _, m', ⟨rfl, hm0⟩, hrets, hm'⟩ | ⟨_, _, _, _, hx, _⟩)
  · rw [← eq_empty_eq_emp] at hm0; subst hm0
    rw [eq_empty_eq_emp, emp_sep] at hm'
    exact ⟨hpc, A.retGpr_eq_of_retsIn hrets, hcs, hsp', hm'⟩
  · exact hx.elim

/-- Specialization of `abi_of_returns` for `rs = [i64]` with an arbitrary `Q : Post [i64]`. -/
theorem abi_of_returns_ret1_q (hh : A.T.mach.Host) {sym : Sym} {b nX : Nat} {as : List Ty}
    {spec : Spec as [i64]} (hfn : A.T.FnSpec hh sym spec b nX)
    {args : Tup Val as} {m : Mem 64} {Q : Post [i64]}
    (hspec : spec args m Q (fun _ _ _ _ => False))
    (s : A.T.mach.MData) (ra : A.T.mach.Addr) (R : Mem 64 → Prop)
    (hargs : A.T.ArgsIn args s) (hsp : A.stackPre s ra)
    (hmem : (A.T.mach.mem s =⋆ Eq m ⋆ A.entryFrame s ra b ⋆ R)) :
    Eventually (A.T.mach.step hh)
      (fun st =>
        A.T.mach.pc st = ra ∧
        A.calleeSavedOk s (A.T.mach.data st) ∧
        A.spRestored s (A.T.mach.data st) ∧
        ∃ m', Q (A.retGpr (A.T.mach.data st), ()) m' ∧
          (A.T.mach.mem (A.T.mach.data st) =⋆ Eq m' ⋆ A.exitFrame s b ⋆ R))
      (A.T.mach.mkState s (A.T.mach.labelAddr hh sym)) := by
  refine eventually_weaken _ _ _ _ ?_ (abi_of_returns A hh hfn hspec s ra R hargs hsp hmem)
  rintro st ⟨hpc, hcs, hsp', ⟨r, ⟨⟩⟩, m', hQ, hrets, hm'⟩
  rw [← A.retGpr_eq_of_retsIn hrets] at hQ
  exact ⟨hpc, hcs, hsp', m', hQ, hm'⟩

/-! ## 4. Generic `TargetInit` Concrete Execution Runners over `BenchAbi` -/

/-- Run a non-exiting `rs = []` function establishing heap predicate `P` on `M.host`. -/
theorem abi_run_sep0 {fns : List Fn} {hints : List A.T.toIsa.Hints} {as : List Ty}
    (M : Compiled A.T A.lt [] [] 0 fns hints 2048) {sym : Sym} {spec : Spec as []}
    (hfn : A.T.FnSpec M.host sym spec (M.bound sym) 0)
    (bytes : List UInt8) (xs : Tup Val as) (hlen : bytes.length ≤ 8192)
    (hargs : (A.T.toIsa.assignArgs as).isSome = true) {P : Mem 64 → Prop}
    (hspec : spec xs (bytes.At 0x1000#64) (fun _ m' => P m') (fun _ _ _ _ => False)) :
    Eventually (A.T.mach.step M.host)
      (fun st => A.T.mach.pc st = A.init.ra0 ∧
        (A.T.mach.mem (A.T.mach.data st) =⋆ P ⋆ A.initExitFrame (M.bound sym) ⋆ emp))
      (A.T.mach.mkState (A.init.initState (M.bound sym) bytes xs)
        (A.T.mach.labelAddr M.host sym)) := by
  refine A.init.run_fnSpec M hfn bytes xs (Nat.le_trans hlen A.maxMem_ge) hargs hspec ?_
    A.maxStack_ge
  rintro st (⟨hpc, _, m', hP, _, hm'⟩ | ⟨_, _, _, _, hx, _⟩)
  · exact ⟨hpc, sep_mono_mid (fun _ hex => A.initExitFrame_of_exit hex)
      (sep_mono (fun _ => sep_mono (fun _ e => e ▸ hP)) hm')⟩
  · exact hx.elim

/-- Run a non-exiting `rs = [i64]` function returning `v` and establishing `P` on `M.host`. -/
theorem abi_run_ret1_sep_i64 {fns : List Fn} {hints : List A.T.toIsa.Hints} {as : List Ty}
    (M : Compiled A.T A.lt [] [] 0 fns hints 2048) {sym : Sym} {spec : Spec as [i64]}
    (hfn : A.T.FnSpec M.host sym spec (M.bound sym) 0)
    (bytes : List UInt8) (xs : Tup Val as) (v : BitVec 64) (P : Mem 64 → Prop)
    (hlen : bytes.length ≤ 8192) (hargs : (A.T.toIsa.assignArgs as).isSome = true)
    {Q : Post [i64]} (hspec : spec xs (bytes.At 0x1000#64) Q (fun _ _ _ _ => False))
    (hQ : ∀ rets m', Q rets m' → rets = (v, ()) ∧ P m') :
    Eventually (A.T.mach.step M.host)
      (fun st => A.T.mach.pc st = A.init.ra0 ∧
        A.retGpr (A.T.mach.data st) = v ∧
        (A.T.mach.mem (A.T.mach.data st) =⋆ P ⋆ A.initExitFrame (M.bound sym) ⋆ emp))
      (A.T.mach.mkState (A.init.initState (M.bound sym) bytes xs)
        (A.T.mach.labelAddr M.host sym)) := by
  refine eventually_weaken _ _ _ _ ?_
    (A.init.run_ret1_sep M hfn bytes xs v P
      (Nat.le_trans hlen A.maxMem_ge) hargs hspec hQ A.maxStack_ge)
  rintro st ⟨hpc, hrets, hm⟩
  exact ⟨hpc, A.retGpr_eq_of_retsIn hrets,
    sep_mono_mid (fun _ hex => A.initExitFrame_of_exit hex) hm⟩

/-- Run a non-exiting `rs = [i64]` function returning `v` on `M.host`. -/
theorem abi_run_ret1_i64 {fns : List Fn} {hints : List A.T.toIsa.Hints} {as : List Ty}
    (M : Compiled A.T A.lt [] [] 0 fns hints 2048) {sym : Sym} {spec : Spec as [i64]}
    (hfn : A.T.FnSpec M.host sym spec (M.bound sym) 0)
    (bytes : List UInt8) (xs : Tup Val as) (v : BitVec 64)
    (hlen : bytes.length ≤ 8192) (hargs : (A.T.toIsa.assignArgs as).isSome = true)
    {Q : Post [i64]} (hspec : spec xs (bytes.At 0x1000#64) Q (fun _ _ _ _ => False))
    (hQ : ∀ rets m', Q rets m' → rets = (v, ())) :
    Eventually (A.T.mach.step M.host)
      (fun st => A.T.mach.pc st = A.init.ra0 ∧ A.retGpr (A.T.mach.data st) = v)
      (A.T.mach.mkState (A.init.initState (M.bound sym) bytes xs)
        (A.T.mach.labelAddr M.host sym)) := by
  refine eventually_weaken _ _ _ _ ?_
    (A.init.run_ret1 M hfn bytes xs v
      (Nat.le_trans hlen A.maxMem_ge) hargs hspec hQ A.maxStack_ge)
  rintro st ⟨hpc, hrets⟩
  exact ⟨hpc, A.retGpr_eq_of_retsIn hrets⟩

/-- Run an exiting `Compiled` function reaching abnormal exit label `g` with `[i64]` arg `v`. -/
theorem abi_run_exit1_i64 {exits : List Sym} {nX : Nat} {fns : List Fn}
    {hints : List A.T.toIsa.Hints} {as bs : List Ty}
    (M : Compiled A.T A.lt [] exits nX fns hints 2048) {sym : Sym} {spec : Spec as bs}
    (hfn : A.T.FnSpec M.host sym spec (M.bound sym) nX)
    (bytes : List UInt8) (xs : Tup Val as) (g : Sym) (v : BitVec 64)
    (hlen : bytes.length ≤ 8192) (hargs : (A.T.toIsa.assignArgs as).isSome = true)
    {X : XPost} (hspec : spec xs (bytes.At 0x1000#64) (fun _ _ => False) X)
    (hX : ∀ sym' cs xs' m', X sym' cs xs' m' →
      ∃ h : cs = [i64], sym' = g ∧ xs' = h ▸ (v, ())) :
    Eventually (A.T.mach.step M.host)
      (fun st => A.T.mach.pc st = A.T.mach.labelAddr M.host g ∧
        A.argAt 0 (A.T.mach.data st) = v)
      (A.T.mach.mkState (A.init.initState (M.bound sym) bytes xs)
        (A.T.mach.labelAddr M.host sym)) := by
  refine A.init.run_fnSpec M hfn bytes xs
    (Nat.le_trans hlen A.maxMem_ge) hargs hspec ?_ A.maxStack_ge
  rintro st (⟨_, _, _, hq, _⟩ | ⟨sym', cs, xs', m', hx, hpc, has⟩)
  · exact hq.elim
  · obtain ⟨rfl, rfl, rfl⟩ := hX sym' cs xs' m' hx
    exact ⟨hpc, A.arg0_eq_of_argsIn has⟩

/-- Run a non-exiting `CompiledRec` function at fuel `k ≤ fuel` returning `v` in `retGpr`. -/
theorem abi_run_rec_ret1_i64 {exits : List Sym} {nX fuel : Nat} {fns : List Fn}
    {hints : List A.T.toIsa.Hints}
    (M : CompiledRec A.T A.lt [] exits nX fuel fns hints 2048) {k : Nat} (hk : k ≤ fuel)
    {sym : Sym} {as : List Ty} {spec : Spec as [i64]}
    (hfn : A.T.FnSpec M.host sym spec (M.boundAt k) nX)
    (bytes : List UInt8) (xs : Tup Val as) (v : BitVec 64)
    (hlen : bytes.length ≤ 8192) (hargs : (A.T.toIsa.assignArgs as).isSome = true)
    {Q : Post [i64]} (hspec : spec xs (bytes.At 0x1000#64) Q (fun _ _ _ _ => False))
    (hQ : ∀ rets m', Q rets m' → rets = (v, ())) :
    Eventually (A.T.mach.step M.host)
      (fun st => A.T.mach.pc st = A.init.ra0 ∧ A.retGpr (A.T.mach.data st) = v)
      (A.T.mach.mkState (A.init.initState (M.boundAt k) bytes xs)
        (A.T.mach.labelAddr M.host sym)) := by
  refine eventually_weaken _ _ _ _ ?_
    (run_rec_ret1 A.init M hk hfn bytes xs v
      (Nat.le_trans hlen A.maxMem_ge) hargs hspec hQ A.maxStack_ge)
  rintro st ⟨hpc, hrets⟩
  exact ⟨hpc, A.retGpr_eq_of_retsIn hrets⟩

/-- Run an exiting `CompiledRec` function reaching exit `g` with `[i64]` arg `v`. -/
theorem abi_run_rec_exit1_i64 {exits : List Sym} {nX fuel : Nat} {fns : List Fn}
    {hints : List A.T.toIsa.Hints}
    (M : CompiledRec A.T A.lt [] exits nX fuel fns hints 2048) {k : Nat} (hk : k ≤ fuel)
    {sym : Sym} {as bs : List Ty} {spec : Spec as bs}
    (hfn : A.T.FnSpec M.host sym spec (M.boundAt k) nX)
    (bytes : List UInt8) (xs : Tup Val as) (g : Sym) (v : BitVec 64)
    (hlen : bytes.length ≤ 8192) (hargs : (A.T.toIsa.assignArgs as).isSome = true)
    {X : XPost} (hspec : spec xs (bytes.At 0x1000#64) (fun _ _ => False) X)
    (hX : ∀ sym' cs xs' m', X sym' cs xs' m' →
      sym' = g ∧ cs = [i64] ∧ HEq xs' ((v, ()) : Tup Val [i64])) :
    Eventually (A.T.mach.step M.host)
      (fun st => A.T.mach.pc st = A.T.mach.labelAddr M.host g ∧
        A.argAt 0 (A.T.mach.data st) = v)
      (A.T.mach.mkState (A.init.initState (M.boundAt k) bytes xs)
        (A.T.mach.labelAddr M.host sym)) := by
  refine run_rec_fnSpec A.init M hk hfn bytes xs
    (Nat.le_trans hlen A.maxMem_ge) hargs hspec ?_ A.maxStack_ge
  rintro st (⟨_, _, _, hq, _⟩ | ⟨sym', cs, xs', m', hx, hpc, has⟩)
  · exact hq.elim
  · obtain ⟨rfl, rfl, hheq⟩ := hX sym' cs xs' m' hx
    obtain rfl := eq_of_heq hheq
    exact ⟨hpc, A.arg0_eq_of_argsIn has⟩

end AbiLifts

end LeanQbe.T.BenchmarkCertKit
