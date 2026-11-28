/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.MainCertProof
public import LeanQbe.T.Logic.MemLemmas
public import Kraken.Mem
public import Kraken.Separation

/-!
# Legacy-Free Arch-Agnostic Kissat ABI Bridge (`KissatAbiCommon`)

Provides the lightweight ISA-neutral ABI interface and separation helpers with zero legacy
`Kissat.Full*`, `MainCertInline`, or `Elab` imports:
1. `sep_exists_eq`: separation-logic existential frame extraction helper.
2. `ArchKissatAbi`: ISA-agnostic ABI bridge over `Target` and `TargetInit`.
3. `solve_of_abi_fnspec`: generic `FnSpec` -> `Eventually (A.T.mach.step hh)` lift for
   non-exiting 5-argument `i64` solver entries.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.KissatCertCommon

open Std Std.ExtHashMap
open LeanQbe.T

/-! ## 1. Separation Frame Helper -/

theorem sep_exists_eq {P Q : Mem 64 → Prop} {M : Mem 64}
    (h : (P ⋆ Q) M) : ∃ m : Mem 64, P m ∧ (Eq m ⋆ Q) M := by
  have hm := sep_mono (Q := Q)
    (fun x hx => (⟨x, ⟨hx, rfl⟩⟩ : ∃ m : Mem 64, P m ∧ Eq m x)) h
  rw [sep_ex_l] at hm
  obtain ⟨m, hm'⟩ := hm
  exact ⟨m, sep_pure_l (φ := P m) (P := Eq m) (R := Q).mp hm'⟩

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

/-- Generic ABI-neutral `FnSpec` -> `Eventually` lift for non-exiting 5-arg `i64` entries. -/
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

end LeanQbe.T.Examples.Kissat.KissatCertCommon
