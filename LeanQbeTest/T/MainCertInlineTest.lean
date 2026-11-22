module

public import LeanQbe.T.MainCertInline
public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.Logic.MemLemmas
public import Std.Sat.CNF
import LeanQbe.T.FlatLemmas
import all Kraken.Mem
import all Kraken.Separation
public meta import Lean
public meta import LeanQbe.T.MainCertInline
public meta import LeanQbe.T.Amd64.Targ

/-!
# Certified Inlined Compilation Bridge Tests on SysV x64 (`MainCertInline`)

Tests `LeanQbe.T.MainCertInline` (`inline_mod!`, `LinkedCert.castModule`,
`LinkedCert.fnSpec_*_optInlinePolicy`, `LinkedCert.eventually_ret1_sep_i64_*_optInlinePolicy`,
and `optInline` corollaries) end-to-end on `x64Target`:
1. 4-function module `inlSrcMod` with `fnAdd45` (`size = 46 ∈ (40, 106]`) called in a loop:
   `inline_mod! inlMod40` keeps `add45` out-of-line while `inline_mod! inlModB5` (`InlinePolicy.b5`)
   inlines `inc`, `step`, and `add45` (`#guard` checks zero remaining `.call`s in `entry`).
2. 2-slice `compile_linked_chunks!` + `eval_prefix_ext!` + `LinkedCert.append` +
   `LinkedCert.castModule inlModB5.eq` (plus single-call `inlMod40` cert), proving arbitrary-`Host`
   `FnSpec`, `Kraken.X64` `x64_of_returns`, and closed `x64Init` `Eventually` (`rax = 85`,
   `cell64 0x1000 25`).
3. Kissat-shaped mini-module witness linking `rax = 20` (`entryVal`) to `cnf.Unsat` on the
   inlined machine code (`miniSatCnf.Unsat`).
4. Audits single-line `<115c` `std3` `#print axioms`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbeTest.T.MainCertInlineTest

open Std Std.ExtHashMap Std.Sat
open LeanQbe.T LeanQbe.T.Amd64 Kraken

/-! ## 1. Four-function acyclic module (`fnAdd45` triggers `b5` `leafMax`) -/

def addChain : (n : Nat) → {V : Ty → Type} → {L : List Ty → Type} →
    Arg V i64 → Expr V L [i64]
  | 0, _, _, a => .ret (a, ())
  | n + 1, _, _, a =>
      .let_ ⟨.add i64, (a, .imm 1#64, ())⟩ fun (y, ()) =>
      addChain n (.var y)

def fnInc : Fn :=
  ⟨"inc", [i64, i64], [i64], fun _ _ (p, d, ()) =>
    .load i64 (.var p) fun v =>
    .let_ ⟨.add i64, (.var v, .var d, ())⟩ fun (s, ()) =>
    .store (.var s) (.var p) (.ret (.var s, ()))⟩

def fnAdd45 : Fn :=
  ⟨"add45", [i64], [i64], fun _ _ (x, ()) => addChain 45 (.var x)⟩

def fnStep : Fn :=
  ⟨"step", [i64, i64], [i64], fun _ _ (p, d, ()) =>
    .call "inc" (as := [i64, i64]) (bs := [i64]) (.var p, .var d, ()) fun (r1, ()) =>
    .let_ ⟨.add i64, (.var r1, .imm 10#64, ())⟩ fun (s, ()) =>
    .ret (.var s, ())⟩

def fnEntry : Fn :=
  ⟨"entry", [i64, i64], [i64], fun _ _ (p, d, ()) =>
    .group (sig := [[i64]])
      (fun (lp, ()) => .cons (fun (acc, ()) =>
        .call "step" (as := [i64, i64]) (bs := [i64]) (.var p, .var d, ()) fun (r1, ()) =>
        .call "add45" (as := [i64]) (bs := [i64]) (.var r1, ()) fun (r2, ()) =>
        .let_ ⟨.add i64, (.var acc, .var r2, ())⟩ fun (s, ()) =>
        .jnz (.imm false) (.jump lp (.var s, ())) (.ret (.var s, ()))) .nil)
      (fun (lp, ()) => .jump lp (.imm 5#64, ()))⟩

def inlSrcMod : Module :=
  { fns := [fnInc, fnAdd45, fnStep, fnEntry] }

/-! ## 2. Materialized inlined modules via `inline_mod!` + `#guard` inlining assertions -/

inline_mod! inlModB5 inlSrcMod InlinePolicy.b5

inline_mod! inlMod40 inlSrcMod (InlinePolicy.const 40)

def dummyFn : Fn := ⟨"", [], [], fun _ _ _ => .hlt⟩

#guard fnAdd45.size == 46
#guard !(inlSrcMod.fns.getD 3 dummyFn).checkCallsOk [] []
#guard (inlMod40.fns.getD 3 dummyFn).checkCallsOk [("add45", [i64], [i64])] []
#guard !(inlMod40.fns.getD 3 dummyFn).checkCallsOk [] []
#guard (inlModB5.fns.getD 3 dummyFn).checkCallsOk [] []

/-! ## 3. Source `ModuleOk` and `LegalSigAll` -/

theorem inlSrcMod_acyclic : inlSrcMod.checkAcyclic = true := by t_kernel_rfl

theorem fnInc_wf : fnInc.Wf := by t_wf_reify
theorem fnAdd45_wf : fnAdd45.Wf := by t_wf_reify
theorem fnStep_wf : fnStep.Wf := by t_wf_reify
theorem fnEntry_wf : fnEntry.Wf := by t_wf_reify

theorem inlSrcMod_wf : ∀ f ∈ inlSrcMod.fns, f.Wf := by
  intro f hf
  simp only [inlSrcMod, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact fnInc_wf
  · exact fnAdd45_wf
  · exact fnStep_wf
  · exact fnEntry_wf

theorem inlSrcMod_legalSig : LegalSigAll x64LegalTarget inlSrcMod.fns :=
  legalSigAll_of_check (by t_kernel_rfl)

def entryVal (v d : BitVec 64) : BitVec 64 := 5#64 + ((v + d + 10#64) + 45#64)

def incSpec : Spec [i64, i64] [i64] := fun (p, d, ()) m Q _ =>
  ∃ v R, (m =⋆ cell64 p v ⋆ R) ∧ (∀ m', (m' =⋆ cell64 p (v + d) ⋆ R) → Q (v + d, ()) m')

def add45Spec : Spec [i64] [i64] := fun (x, ()) m Q _ =>
  Q (x + 45#64, ()) m

def stepSpec : Spec [i64, i64] [i64] := fun (p, d, ()) m Q _ =>
  ∃ v R, (m =⋆ cell64 p v ⋆ R) ∧
    (∀ m', (m' =⋆ cell64 p (v + d) ⋆ R) → Q (v + d + 10#64, ()) m')

def entrySpec : Spec [i64, i64] [i64] := fun (p, d, ()) m Q _ =>
  ∃ v R, (m =⋆ cell64 p v ⋆ R) ∧
    (∀ m', (m' =⋆ cell64 p (v + d) ⋆ R) → Q (entryVal v d, ()) m')

def inlΓ : Env
  | "inc", [.bits 64, .bits 64], [.bits 64], xs, m, Q, X => incSpec xs m Q X
  | "add45", [.bits 64], [.bits 64], xs, m, Q, X => add45Spec xs m Q X
  | "step", [.bits 64, .bits 64], [.bits 64], xs, m, Q, X => stepSpec xs m Q X
  | "entry", [.bits 64, .bits 64], [.bits 64], xs, m, Q, X => entrySpec xs m Q X
  | _, _, _, _, _, _, _ => False

theorem inlΓ_noExit : ∀ f as bs xs m Q X X',
    inlΓ f as bs xs m Q X → inlΓ f as bs xs m Q X' := by
  intro f as bs xs m Q X X' h
  unfold inlΓ at h ⊢
  split at h <;> exact h

private theorem addChain_wp (Γ : Env) :
    ∀ (n : Nat) (x : BitVec 64) (m : Mem 64) (Q : Post [i64]) (X : XPost),
      Q (x + BitVec.ofNat 64 n, ()) m →
      wp Γ Q X (addChain n (.var x)) m
  | 0, x, m, Q, _, h => by
      dsimp only [addChain, wp, vals]
      rw [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] at h
      exact h
  | n + 1, x, m, Q, X, h => by
      dsimp only [addChain, wp, Op.wp, OpCode.wp, lift2, Ty.hasFloat, Arg.val, vals]
      refine addChain_wp Γ n (x + 1#64) m Q X ?_
      have hn : BitVec.ofNat 64 (n + 1) = 1#64 + BitVec.ofNat 64 n := by
        rw [Nat.add_comm n 1, BitVec.ofNat_add]
      simpa [BitVec.add_assoc, hn] using h

private theorem inc_wp {xs : Tup Val [i64, i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (h : incSpec xs m Q X) : Func.wp inlΓ fnInc.body xs m Q X := by
  rcases xs with ⟨p, d, ⟨⟩⟩
  rcases h with ⟨v, R, hm, hQ⟩
  dsimp only [Func.wp, fnInc, wp, Op.wp, op2, OpCode.wp, lift2, Ty.hasFloat, Arg.val, vals]
  refine ⟨v, loadVal_cell64 hm, ?_⟩
  obtain ⟨hok, hst⟩ := store_cell64 (v + d) hm
  exact ⟨hok, hQ _ hst⟩

private theorem add45_wp {xs : Tup Val [i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (h : add45Spec xs m Q X) : Func.wp inlΓ fnAdd45.body xs m Q X := by
  rcases xs with ⟨x, ⟨⟩⟩
  exact addChain_wp inlΓ 45 x m Q X h

private theorem step_wp {xs : Tup Val [i64, i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (h : stepSpec xs m Q X) : Func.wp inlΓ fnStep.body xs m Q X := by
  rcases xs with ⟨p, d, ⟨⟩⟩
  rcases h with ⟨v, R, hm, hQ⟩
  dsimp only [Func.wp, fnStep, wp, Op.wp, op2, OpCode.wp, lift2, Ty.hasFloat, Arg.val, vals]
  refine ⟨fun (r, _) m₁ => r = v + d ∧ (m₁ =⋆ cell64 p (v + d) ⋆ R), X,
    ⟨v, R, hm, fun m' hm' => ⟨rfl, hm'⟩⟩, ?_, fun _ _ _ _ hx => hx⟩
  rintro ⟨r₁, ⟨⟩⟩ m₁ ⟨rfl, hm₁⟩
  exact hQ m₁ hm₁

private theorem entry_wp {xs : Tup Val [i64, i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (h : entrySpec xs m Q X) : Func.wp inlΓ fnEntry.body xs m Q X := by
  rcases xs with ⟨p, d, ⟨⟩⟩
  rcases h with ⟨v, R, hm, hQ⟩
  dsimp only [Func.wp, fnEntry, wp, vals]
  intro Js hClosed
  refine hClosed.1 (5#64, ()) m ?_
  dsimp only [wp, Op.wp, OpCode.wp, lift2, Ty.hasFloat, Arg.val, vals]
  refine ⟨fun (r, _) m₁ => r = v + d + 10#64 ∧ (m₁ =⋆ cell64 p (v + d) ⋆ R), X,
    ⟨v, R, hm, fun m' hm' => ⟨rfl, hm'⟩⟩, ?_, fun _ _ _ _ hx => hx⟩
  rintro ⟨r₁, ⟨⟩⟩ m₁ ⟨rfl, hm₁⟩
  refine ⟨fun (r, _) m₂ => r = (v + d + 10#64) + 45#64 ∧ m₂ = m₁, X, ⟨rfl, rfl⟩, ?_,
    fun _ _ _ _ hx => hx⟩
  rintro ⟨r₂, ⟨⟩⟩ m₂ ⟨rfl, hm₂⟩
  subst hm₂
  constructor
  · intro hc; cases hc
  · intro _; exact hQ m₂ hm₁

theorem inlSrcMod_modOk : ModuleOk inlΓ inlSrcMod := by
  refine Module.moduleOk_of_checkAcyclic inlSrcMod_acyclic inlSrcMod_wf ?_
  intro f hf xs m Q X hΓ
  simp only [inlSrcMod, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact inc_wp hΓ
  · exact add45_wp hΓ
  · exact step_wp hΓ
  · exact entry_wp hΓ

/-! ## 4. Multi-slice `compile_linked_chunks!` + `castModule` certificates -/

def slice1Mod : Module := { fns := inlModB5.fns.take 2 }
def slice2Mod : Module := { fns := inlModB5.fns.drop 2 }

compile_linked_chunks! certB5Slice1
  x64Target x64Layout x64LegalTarget x64LabelClean slice1Mod 1

eval_prefix_ext! extB5Slice1 x64Target x64LegalTarget (inlModB5.fns.take 2)

compile_linked_chunks! certB5Slice2
  x64Target x64Layout x64LegalTarget x64LabelClean slice2Mod 1 (ext := extB5Slice1)

noncomputable def certB5Mat :
    LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean inlModB5 [] [] 0 2048 :=
  certB5Slice1.append certB5Slice2
    (by exact (List.take_append_drop 2 inlModB5.fns).symm)
    (by t_kernel_rfl)

noncomputable def certB5 :
    LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean
      (inlSrcMod.optInlinePolicy InlinePolicy.b5) [] [] 0 2048 :=
  certB5Mat.castModule inlModB5.eq

compile_linked_chunks! cert40Mat
  x64Target x64Layout x64LegalTarget x64LabelClean inlMod40 2

noncomputable def cert40 :
    LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean
      (inlSrcMod.optInline 40) [] [] 0 2048 :=
  cert40Mat.castModule inlMod40.eq

/-! ## 5. Arbitrary-`Host` `FnSpec`, `x64_of_returns`, and closed `x64Init` `Eventually` -/

theorem certB5_fnspec [hh : Host] (k₀ : Nat)
    (hc : certB5.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {f : Fn} (hf : f ∈ inlSrcMod.fns) :
    x64Target.Defined hh f.name ∧
      x64Target.FnSpec hh f.name (inlΓ f.name f.as f.rs) (certB5.bound f.name) 0 :=
  certB5.fnSpec_noExit_of_legalSigAll_optInlinePolicy hh inlΓ k₀ hc hu
    inlSrcMod_modOk inlSrcMod_legalSig hf (inlΓ_noExit f.name f.as f.rs)

theorem cert40_fnspec [hh : Host] (k₀ : Nat)
    (hc : cert40.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    {f : Fn} (hf : f ∈ inlSrcMod.fns) :
    x64Target.Defined hh f.name ∧
      x64Target.FnSpec hh f.name (inlΓ f.name f.as f.rs) (cert40.bound f.name) 0 :=
  cert40.fnSpec_noExit_of_legalSigAll_optInline hh inlΓ k₀ hc hu
    inlSrcMod_modOk inlSrcMod_legalSig hf (inlΓ_noExit f.name f.as f.rs)

theorem entry_x64_ev [hh : Host] (k₀ : Nat)
    (hc : certB5.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (p d v₀ : BitVec 64) (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hrdi : s.regs.get64 .rdi = p) (hrsi : s.regs.get64 .rsi = d)
    (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hmem : s.dmem =⋆ cell64 p v₀ ⋆
      (region (s.regs.get64 .rsp - BitVec.ofNat 64 (certB5.bound "entry"))
          (certB5.bound "entry") ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧ st.data.regs.get64 .rax = entryVal v₀ d)
      ⟨s, Labels.label "entry"⟩ := by
  have hfn : x64Target.FnSpec hh "entry" entrySpec (certB5.bound "entry") 0 :=
    (certB5_fnspec k₀ hc hu (f := fnEntry) (by simp [inlSrcMod])).2
  have hargs : x64Target.ArgsIn (as := [i64, i64]) (p, d, ()) s :=
    ⟨_, rfl, .cons ⟨by decide, by simpa using hrdi⟩
      (.cons ⟨by decide, by simpa using hrsi⟩ .nil)⟩
  obtain ⟨mf, mR, hu1, hd1, ⟨mCell, f, hu2, hd2, hmCell, hf⟩, hmRest⟩ := hmem
  have hmEq : s.dmem =⋆ Eq mCell ⋆
      (region (s.regs.get64 .rsp - BitVec.ofNat 64 (certB5.bound "entry"))
          (certB5.bound "entry") ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R :=
    ⟨mf, mR, hu1, hd1, ⟨mCell, f, hu2, hd2, rfl, hf⟩, hmRest⟩
  have hspec : entrySpec (p, d, ()) mCell (fun r m' => r = (entryVal v₀ d, ()) ∧ True)
      (fun _ _ _ _ => False) :=
    ⟨v₀, emp, by rwa [sep_emp], fun _ _ => ⟨rfl, trivial⟩⟩
  refine eventually_weaken _ _ _ _ ?_ (x64_of_returns hfn hspec s ra R hargs hsp hmEq)
  rintro st ⟨hpc, _, _, _, _, ⟨rfl, _⟩, hrets, _⟩
  exact ⟨hpc, x64Init.retsIn_singleton (entryVal v₀ d) st.data hrets⟩

def initMemBytes : List UInt8 := bytes64 [20#64]

private theorem initMemBytes_len : initMemBytes.length ≤ 8192 := by
  simp [initMemBytes, bytes64_length]

private theorem initMemBytes_cell :
    (cell64 0x1000#64 20#64 ⋆ emp) (initMemBytes.At 0x1000#64) := by
  have h := array64_bytes 0x1000#64 [20#64] (by decide)
  simpa [initMemBytes] using h

theorem x64_run_b5_sep :
    Eventually (x64Target.mach.step certB5.host)
      (fun st => x64Target.mach.pc st = x64Init.ra0 ∧
        x64Target.mach.getGpr (x64Target.mach.data st) x64Init.ret0 = 85#64 ∧
        (x64Target.mach.mem (x64Target.mach.data st) =⋆
          (cell64 0x1000#64 25#64 ⋆ emp) ⋆
          x64Target.Exit x64Init.sp0 (certB5.bound "entry") ⋆ emp))
      (x64Target.mach.mkState
        (x64Init.initState (as := [i64, i64]) (certB5.bound "entry") initMemBytes
          (0x1000#64, 5#64, ()))
        (x64Target.mach.labelAddr certB5.host "entry")) := by
  refine certB5.eventually_ret1_sep_i64_of_legalSigAll_optInlinePolicy x64Init inlΓ
    inlSrcMod_modOk inlSrcMod_legalSig (f := fnEntry) (by simp [inlSrcMod]) rfl
    (inlΓ_noExit "entry" [i64, i64] [i64]) initMemBytes (0x1000#64, 5#64, ()) 85#64
    (cell64 0x1000#64 25#64 ⋆ emp) initMemBytes_len rfl
    (Q := fun rets m' => rets = (85#64, ()) ∧ (cell64 0x1000#64 25#64 ⋆ emp) m') ?_
    (fun _ _ h => h) (by decide)
  refine ⟨20#64, emp, initMemBytes_cell, fun m' hm' => ⟨rfl, ?_⟩⟩
  simpa using hm'

/-! ## 6. Mini UNSAT Witness (`cnf.Unsat` from Inlined Machine Code) -/

def miniUnsatCnf : CNF Nat :=
  (CNF.empty.add (CNF.Clause.empty.add 1 true)).add
    (CNF.Clause.empty.add 1 false)

theorem miniUnsatCnf_unsat : miniUnsatCnf.Unsat := by
  intro a
  simp only [miniUnsatCnf, CNF.eval_add, CNF.eval_empty, CNF.Clause.eval_add,
    CNF.Clause.eval_empty, Bool.or_false, Bool.and_true]
  cases a 1 <;> simp

theorem x64_run_b5_unsat :
    Eventually (x64Target.mach.step certB5.host)
      (fun st => x64Target.mach.pc st = x64Init.ra0 ∧
        x64Target.mach.getGpr (x64Target.mach.data st) x64Init.ret0 = 85#64 ∧
        miniUnsatCnf.Unsat)
      (x64Target.mach.mkState
        (x64Init.initState (as := [i64, i64]) (certB5.bound "entry") initMemBytes
          (0x1000#64, 5#64, ()))
        (x64Target.mach.labelAddr certB5.host "entry")) :=
  eventually_weaken _ _ _ _
    (fun _ h => ⟨h.1, h.2.1, miniUnsatCnf_unsat⟩) x64_run_b5_sep

/-! ## 7. Axiom Audit -/

#print axioms LeanQbe.T.LinkedCert.castFns
#print axioms LeanQbe.T.LinkedCert.castModule
#print axioms LeanQbe.T.LinkedCert.fnSpec_optInlinePolicy
#print axioms LeanQbe.T.LinkedCert.fnSpec_host_optInlinePolicy
#print axioms LeanQbe.T.LinkedCert.fnSpec_noExit_id_optInlinePolicy
#print axioms inlModB5
#print axioms inlModB5.eq
#print axioms certB5
#print axioms cert40
#print axioms certB5_fnspec
#print axioms cert40_fnspec
#print axioms entry_x64_ev
#print axioms x64_run_b5_sep
#print axioms x64_run_b5_unsat

end LeanQbeTest.T.MainCertInlineTest
