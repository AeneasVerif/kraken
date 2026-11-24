module

public import LeanQbe.T.Main
public import LeanQbe.T.MainLemmas
public import LeanQbe.T.WP
public import LeanQbe.T.MainCertProof
public import LeanQbe.T.MainCertInline
public import LeanQbe.T.Logic.MemLemmas
public import Std.Sat.CNF
public import Kraken.Layout
import LeanQbe.T.FlatLemmas
import all Kraken.Mem
import all Kraken.Separation

/-!
# Shared Test Fixtures, Specifications, and Acyclic Modules (`Common.Fixtures`)

Target-neutral IR functions, modules, and semantic specifications shared across
architecture-mirrored test suites (`CertAutoExt{,Arm64}Test`, `MainCert{,Arm64}Test`,
`MainCertInline{,Arm64}Test`, and litmus tests).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbeTest.T.Common.Fixtures

open Std Std.ExtHashMap Std.Sat
open LeanQbe.T Kraken

/-! ## 1. Six-function acyclic test module (`autoFns` / `certMod`) -/

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

def autoFns : List Fn := [fnInc, fnScale, fnStep, fnPair, fnWrap, fnMain]

def certMod : Module := { fns := autoFns }
def exitMod : Module := { fns := [fnScale, fnExit], exits := ["bail"] }
def emptyMod : Module := { fns := [] }
def extSubMod : Module := { fns := [fnStep, fnPair] }
def extCalleesSample : List (SigEntry × Nat) :=
  [(("inc", [i64, i64], [i64]), 8), (("scale", [i64], [i64]), 8)]
def extCalleesSampleArm : List (SigEntry × Nat) :=
  [(("inc", [i64, i64], [i64]), 16), (("scale", [i64], [i64]), 16)]
def part1Mod : Module := { fns := [fnInc, fnScale, fnStep] }
def part2Mod : Module := { fns := [fnPair, fnWrap, fnMain] }

def slice1Mod : Module := { fns := autoFns.take 2 }
def slice2Mod : Module := { fns := (autoFns.drop 2).take 2 }
def slice3Mod : Module := { fns := autoFns.drop 4 }
def pref2Mod : Module := { fns := autoFns.take 4 }
def fullMod : Module := { fns := autoFns }

theorem certMod_acyclic : certMod.checkAcyclic = true := by t_kernel_rfl

theorem fnInc_wf : fnInc.Wf := by t_wf_reify
theorem fnScale_wf : fnScale.Wf := by t_wf_reify
theorem fnStep_wf : fnStep.Wf := by t_wf_reify
theorem fnPair_wf : fnPair.Wf := by t_wf_reify
theorem fnWrap_wf : fnWrap.Wf := by t_wf_reify
theorem fnMain_wf : fnMain.Wf := by t_wf_reify

theorem certMod_wf : ∀ f ∈ certMod.fns, f.Wf := by
  intro f hf
  cases hf with
  | head => exact fnInc_wf
  | tail _ hf =>
    cases hf with
    | head => exact fnScale_wf
    | tail _ hf =>
      cases hf with
      | head => exact fnStep_wf
      | tail _ hf =>
        cases hf with
        | head => exact fnPair_wf
        | tail _ hf =>
          cases hf with
          | head => exact fnWrap_wf
          | tail _ hf =>
            cases hf with
            | head => exact fnMain_wf
            | tail _ hf => cases hf

theorem fnMain_mem_certMod : fnMain ∈ certMod.fns :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
    (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

/-! ## 2. Source Semantics & Pure Functional Specifications -/

def stepVal (v d : BitVec 64) : BitVec 64 := (v + d) + (d + d)
def pairMem (v d : BitVec 64) : BitVec 64 := (v + d) + (d + 1#64)
def pairVal (v d : BitVec 64) : BitVec 64 := stepVal v d + stepVal (v + d) (d + 1#64)
def wrapVal (v d : BitVec 64) : BitVec 64 := pairVal v d + 7#64
def mainVal (v d : BitVec 64) : BitVec 64 := wrapVal v d + (d + d)

abbrev PureSpec (as bs : List Ty) := Tup Val as → Mem 64 → Post bs → Prop

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

def pureIncSpec : PureSpec [i64, i64] [i64] := fun (p, d, ()) m Q =>
  ∃ v R, (m =⋆ cell64 p v ⋆ R) ∧ (∀ m', (m' =⋆ cell64 p (v + d) ⋆ R) → Q (v + d, ()) m')

def pureScaleSpec : PureSpec [i64] [i64] := fun (x, ()) m Q => Q (x + x, ()) m

def pureStepSpec : PureSpec [i64, i64] [i64] := fun (p, d, ()) m Q =>
  ∃ v R, (m =⋆ cell64 p v ⋆ R) ∧
    (∀ m', (m' =⋆ cell64 p (v + d) ⋆ R) → Q (stepVal v d, ()) m')

def purePairSpec : PureSpec [i64, i64] [i64] := fun (p, d, ()) m Q =>
  ∃ v R, (m =⋆ cell64 p v ⋆ R) ∧
    (∀ m', (m' =⋆ cell64 p (pairMem v d) ⋆ R) → Q (pairVal v d, ()) m')

def pureWrapSpec : PureSpec [i64, i64] [i64] := fun (p, d, ()) m Q =>
  ∃ v R, (m =⋆ cell64 p v ⋆ R) ∧
    (∀ m', (m' =⋆ cell64 p (pairMem v d) ⋆ R) → Q (wrapVal v d, ()) m')

def pureMainSpec : PureSpec [i64, i64] [i64] := fun (p, d, ()) m Q =>
  ∃ v R, (m =⋆ cell64 p v ⋆ R) ∧
    (∀ m', (m' =⋆ cell64 p (pairMem v d) ⋆ R) → Q (mainVal v d, ()) m')

def certSpec (f : Sym) (as bs : List Ty) : Option (PureSpec as bs) :=
  match f, as, bs with
  | "inc", [.bits 64, .bits 64], [.bits 64] => some pureIncSpec
  | "scale", [.bits 64], [.bits 64] => some pureScaleSpec
  | "step", [.bits 64, .bits 64], [.bits 64] => some pureStepSpec
  | "pair", [.bits 64, .bits 64], [.bits 64] => some purePairSpec
  | "wrap", [.bits 64, .bits 64], [.bits 64] => some pureWrapSpec
  | "main_entry", [.bits 64, .bits 64], [.bits 64] => some pureMainSpec
  | _, _, _ => none

def certΓ : Env := fun f as bs xs m Q _ =>
  match certSpec f as bs with
  | some spec => spec xs m Q
  | none => False

theorem certΓ_noExit : ∀ f as bs xs m Q X X',
    certΓ f as bs xs m Q X → certΓ f as bs xs m Q X' :=
  fun _ _ _ _ _ _ _ _ h => h

theorem inc_wp {xs : Tup Val [i64, i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (h : incSpec xs m Q X) : Func.wp certΓ fnInc.body xs m Q X := by
  rcases xs with ⟨p, d, ⟨⟩⟩
  rcases h with ⟨v, R, hm, hQ⟩
  dsimp only [Func.wp, fnInc, wp, Op.wp, op2, OpCode.wp, lift2, Ty.hasFloat, Arg.val, vals]
  refine ⟨v, loadVal_cell64 hm, ?_⟩
  obtain ⟨hok, hst⟩ := store_cell64 (v + d) hm
  exact ⟨hok, hQ _ hst⟩

theorem scale_wp {xs : Tup Val [i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (h : scaleSpec xs m Q X) : Func.wp certΓ fnScale.body xs m Q X := by
  rcases xs with ⟨x, ⟨⟩⟩
  dsimp only [Func.wp, fnScale, wp, Op.wp, op2, OpCode.wp, lift2, Ty.hasFloat, Arg.val, vals]
  exact h

theorem step_wp {xs : Tup Val [i64, i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost}
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

theorem pair_wp {xs : Tup Val [i64, i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost}
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

theorem wrap_wp {xs : Tup Val [i64, i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (h : wrapSpec xs m Q X) : Func.wp certΓ fnWrap.body xs m Q X := by
  rcases xs with ⟨p, d, ⟨⟩⟩
  rcases h with ⟨v, R, hm, hQ⟩
  dsimp only [Func.wp, fnWrap, wp, Op.wp, op2, OpCode.wp, lift2, Ty.hasFloat, Arg.val, vals]
  refine ⟨fun (r, _) m₁ => r = pairVal v d ∧ (m₁ =⋆ cell64 p (pairMem v d) ⋆ R), X,
    ⟨v, R, hm, fun m' hm' => ⟨rfl, hm'⟩⟩, ?_, fun _ _ _ _ hx => hx⟩
  rintro ⟨r, ⟨⟩⟩ m₁ ⟨rfl, hm₁⟩
  exact hQ m₁ hm₁

theorem main_wp {xs : Tup Val [i64, i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost}
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
  cases hf with
  | head => exact inc_wp hΓ
  | tail _ hf =>
    cases hf with
    | head => exact scale_wp hΓ
    | tail _ hf =>
      cases hf with
      | head => exact step_wp hΓ
      | tail _ hf =>
        cases hf with
        | head => exact pair_wp hΓ
        | tail _ hf =>
          cases hf with
          | head => exact wrap_wp hΓ
          | tail _ hf =>
            cases hf with
            | head => exact main_wp hΓ
            | tail _ hf => cases hf

/-! ## 3. Inlining Fixtures & Proofs (`MainCertInline`) -/

def addChain : (n : Nat) → {V : Ty → Type} → {L : List Ty → Type} →
    Arg V i64 → Expr V L [i64]
  | 0, _, _, a => .ret (a, ())
  | n + 1, _, _, a =>
      .let_ ⟨.add i64, (a, .imm 1#64, ())⟩ fun (y, ()) =>
      addChain n (.var y)

def fnAdd45 : Fn :=
  ⟨"add45", [i64], [i64], fun _ _ (x, ()) => addChain 45 (.var x)⟩

def fnStepInl : Fn :=
  ⟨"step", [i64, i64], [i64], fun _ _ (p, d, ()) =>
    .call "inc" (as := [i64, i64]) (bs := [i64]) (.var p, .var d, ()) fun (r1, ()) =>
    .let_ ⟨.add i64, (.var r1, .imm 10#64, ())⟩ fun (s, ()) =>
    .ret (.var s, ())⟩

def fnEntryInl : Fn :=
  ⟨"entry", [i64, i64], [i64], fun _ _ (p, d, ()) =>
    .group (sig := [[i64]])
      (fun (lp, ()) => .cons (fun (acc, ()) =>
        .call "step" (as := [i64, i64]) (bs := [i64]) (.var p, .var d, ()) fun (r1, ()) =>
        .call "add45" (as := [i64]) (bs := [i64]) (.var r1, ()) fun (r2, ()) =>
        .let_ ⟨.add i64, (.var acc, .var r2, ())⟩ fun (s, ()) =>
        .jnz (.imm false) (.jump lp (.var s, ())) (.ret (.var s, ()))) .nil)
      (fun (lp, ()) => .jump lp (.imm 5#64, ()))⟩

def inlSrcMod : Module :=
  { fns := [fnInc, fnAdd45, fnStepInl, fnEntryInl] }

theorem inlSrcMod_acyclic : inlSrcMod.checkAcyclic = true := by t_kernel_rfl

theorem fnAdd45_wf : fnAdd45.Wf := by t_wf_reify
theorem fnStepInl_wf : fnStepInl.Wf := by t_wf_reify
theorem fnEntryInl_wf : fnEntryInl.Wf := by t_wf_reify

theorem inlSrcMod_wf : ∀ f ∈ inlSrcMod.fns, f.Wf := by
  intro f hf
  simp only [inlSrcMod, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · exact fnInc_wf
  · exact fnAdd45_wf
  · exact fnStepInl_wf
  · exact fnEntryInl_wf

def entryVal (v d : BitVec 64) : BitVec 64 := 5#64 + ((v + d + 10#64) + 45#64)

def add45Spec : Spec [i64] [i64] := fun (x, ()) m Q _ =>
  Q (x + 45#64, ()) m

def inlStepSpec : Spec [i64, i64] [i64] := fun (p, d, ()) m Q _ =>
  ∃ v R, (m =⋆ cell64 p v ⋆ R) ∧
    (∀ m', (m' =⋆ cell64 p (v + d) ⋆ R) → Q (v + d + 10#64, ()) m')

def entrySpec : Spec [i64, i64] [i64] := fun (p, d, ()) m Q _ =>
  ∃ v R, (m =⋆ cell64 p v ⋆ R) ∧
    (∀ m', (m' =⋆ cell64 p (v + d) ⋆ R) → Q (entryVal v d, ()) m')

def inlΓ : Env
  | "inc", [.bits 64, .bits 64], [.bits 64], xs, m, Q, X => incSpec xs m Q X
  | "add45", [.bits 64], [.bits 64], xs, m, Q, X => add45Spec xs m Q X
  | "step", [.bits 64, .bits 64], [.bits 64], xs, m, Q, X => inlStepSpec xs m Q X
  | "entry", [.bits 64, .bits 64], [.bits 64], xs, m, Q, X => entrySpec xs m Q X
  | _, _, _, _, _, _, _ => False

theorem inlΓ_noExit : ∀ f as bs xs m Q X X',
    inlΓ f as bs xs m Q X → inlΓ f as bs xs m Q X' := by
  intro f as bs xs m Q X X' h
  unfold inlΓ at h ⊢
  split at h <;> exact h

theorem addChain_wp (Γ : Env) :
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

theorem inlInc_wp {xs : Tup Val [i64, i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (h : incSpec xs m Q X) : Func.wp inlΓ fnInc.body xs m Q X := by
  rcases xs with ⟨p, d, ⟨⟩⟩
  rcases h with ⟨v, R, hm, hQ⟩
  dsimp only [Func.wp, fnInc, wp, Op.wp, op2, OpCode.wp, lift2, Ty.hasFloat, Arg.val, vals]
  refine ⟨v, loadVal_cell64 hm, ?_⟩
  obtain ⟨hok, hst⟩ := store_cell64 (v + d) hm
  exact ⟨hok, hQ _ hst⟩

theorem add45_wp {xs : Tup Val [i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (h : add45Spec xs m Q X) : Func.wp inlΓ fnAdd45.body xs m Q X := by
  rcases xs with ⟨x, ⟨⟩⟩
  exact addChain_wp inlΓ 45 x m Q X h

theorem inlStep_wp {xs : Tup Val [i64, i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (h : inlStepSpec xs m Q X) : Func.wp inlΓ fnStepInl.body xs m Q X := by
  rcases xs with ⟨p, d, ⟨⟩⟩
  rcases h with ⟨v, R, hm, hQ⟩
  dsimp only [Func.wp, fnStepInl, wp, Op.wp, op2, OpCode.wp, lift2, Ty.hasFloat, Arg.val, vals]
  refine ⟨fun (r, _) m₁ => r = v + d ∧ (m₁ =⋆ cell64 p (v + d) ⋆ R), X,
    ⟨v, R, hm, fun m' hm' => ⟨rfl, hm'⟩⟩, ?_, fun _ _ _ _ hx => hx⟩
  rintro ⟨r₁, ⟨⟩⟩ m₁ ⟨rfl, hm₁⟩
  exact hQ m₁ hm₁

theorem entry_wp {xs : Tup Val [i64, i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (h : entrySpec xs m Q X) : Func.wp inlΓ fnEntryInl.body xs m Q X := by
  rcases xs with ⟨p, d, ⟨⟩⟩
  rcases h with ⟨v, R, hm, hQ⟩
  dsimp only [Func.wp, fnEntryInl, wp, vals]
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
  · exact inlInc_wp hΓ
  · exact add45_wp hΓ
  · exact inlStep_wp hΓ
  · exact entry_wp hΓ

/-! ## 4. CNF Sat/Unsat Instances (`MainCertInline`) -/

def miniUnsatCnf : CNF Nat :=
  (CNF.empty.add (CNF.Clause.empty.add 1 true)).add
    (CNF.Clause.empty.add 1 false)

theorem miniUnsatCnf_unsat : miniUnsatCnf.Unsat := by
  intro a
  simp only [miniUnsatCnf, CNF.eval_add, CNF.eval_empty, CNF.Clause.eval_add,
    CNF.Clause.eval_empty, Bool.or_false, Bool.and_true]
  cases a 1 <;> simp

end LeanQbeTest.T.Common.Fixtures
