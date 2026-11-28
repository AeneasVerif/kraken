module

import LeanQbe.T.MainInline
import LeanQbe.T.FlatLemmas

/-!
# `InlinePolicy` Threshold, Exclusion, and Soundness Tests

Covers:
1. `leafMax`: leaf callee (`size ∈ (40, leafMax]`) with `≥ 2` sites inlines while a same-size
   non-leaf callee with `≥ 2` sites stays out-of-line.
2. `singleSiteMax`: single-site callee (`size ∈ (leafMax, singleSiteMax]`) inlines while a
   multi-site callee of identical size stays `.call`.
3. `maxCallerSize` cap: callers exceeding `maxCallerSize` receive zero inlining, and callers within
   `maxCallerSize` greedily inline smallest eligible callees up to the cap and stop before
   exceeding it.
4. `keepOutOfLine` exclusion: small leaf / single-site callees listed in `keepOutOfLine` never
   inline regardless of budget/leaf/single-site thresholds.
5. `InlinePolicy.b5` preset check and verified soundness (`optInlinePolicy_wf`,
   `optInlinePolicy_spec`, `optInlinePolicy_callsOk`, `optInlinePolicy_acyclic`,
   `optInlinePolicy_supportsSource`) with single-line standard-axiom `#print axioms`.
-/

set_option autoImplicit false

section

namespace LeanQbeTest.T.InlinePolicyB5Test

open LeanQbe.T

def addChain : (n : Nat) → {V : Ty → Type} → {L : List Ty → Type} →
    Arg V i64 → Expr V L [i64]
  | 0, _, _, a => .ret (a, ())
  | n + 1, _, _, a =>
      .let_ (op2 (.add i64) a (.imm 1)) fun (y, ()) =>
      addChain n (.var y)

theorem addChain_wp (Γ : Env) :
    ∀ (n : Nat) (x : BitVec 64) (m : Mem 64) (Q : Post [i64]) (X : XPost),
      Q (x + BitVec.ofNat 64 n, ()) m →
      wp Γ (fun r m' => Q r m') X (addChain n (.var x)) m
  | 0, x, m, Q, _, h => by
      dsimp only [addChain, wp, vals]
      rw [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] at h
      exact h
  | n + 1, x, m, Q, X, h => by
      dsimp only [addChain, wp, Op.wp, OpCode.wp, vals]
      refine addChain_wp Γ n (x + 1#64) m Q X ?_
      have hn : BitVec.ofNat 64 (n + 1) = 1#64 + BitVec.ofNat 64 n := by
        rw [Nat.add_comm n 1, BitVec.ofNat_add]
      simpa [BitVec.add_assoc, hn] using h

def dummyFn : Fn := ⟨"", [], [], fun _ _ _ => .hlt⟩

/-! ## 1. `leafMax` vs non-leaf multi-site -/

def leafMid : Fn := ⟨"leafMid", [i64], [i64], fun _ _ (x, ()) => addChain 7 (.var x)⟩

def bigHelper : Fn := ⟨"bigHelper", [i64], [i64], fun _ _ (x, ()) => addChain 12 (.var x)⟩

def tinyCallee : Fn := ⟨"tinyCallee", [i64], [i64], fun _ _ (x, ()) =>
  .let_ (op2 (.add i64) (.var x) (.imm 1)) fun (y, ()) => .ret (.var y, ())⟩

def nonLeafMid : Fn := ⟨"nonLeafMid", [i64], [i64], fun _ _ (x, ()) =>
  .call "bigHelper" (as := [i64]) (bs := [i64]) (.var x, ()) fun (a, ()) =>
  addChain 6 (.var a)⟩

def leafCaller1 : Fn := ⟨"lcaller1", [i64], [i64], fun _ _ (x, ()) =>
  .call "leafMid" (as := [i64]) (bs := [i64]) (.var x, ()) fun (a, ()) =>
  .call "nonLeafMid" (as := [i64]) (bs := [i64]) (.var a, ()) fun (b, ()) =>
  .ret (.var b, ())⟩

def leafCaller2 : Fn := ⟨"lcaller2", [i64], [i64], fun _ _ (x, ()) =>
  .call "leafMid" (as := [i64]) (bs := [i64]) (.var x, ()) fun (a, ()) =>
  .call "nonLeafMid" (as := [i64]) (bs := [i64]) (.var a, ()) fun (b, ()) =>
  .ret (.var b, ())⟩

def leafMod : Module where
  fns := [bigHelper, leafMid, nonLeafMid, leafCaller1, leafCaller2]

def leafPol : InlinePolicy :=
  { budget := fun _ => 5, leafMax := 10, singleSiteMax := 0 }

theorem leafPol_leaf_only :
    let body :=
      ((leafMod.inlinePolicy leafPol).fns.getD 3 dummyFn).body
        (fun _ => Unit) (fun _ => Unit) (Tup.units [i64])
    leafMid.isLeaf = true ∧ nonLeafMid.isLeaf = false ∧
      Expr.checkCallsOk [⟨"nonLeafMid", [i64], [i64]⟩] [] body = true ∧
      Expr.checkCallsOk [] [] body = false := by
  decide

/-! ## 2. `singleSiteMax` vs multi-site -/

def ssSingle : Fn := ⟨"ssSingle", [i64], [i64], fun _ _ (x, ()) =>
  .call "tinyCallee" (as := [i64]) (bs := [i64]) (.var x, ()) fun (a, ()) =>
  addChain 10 (.var a)⟩

def ssMulti : Fn := ⟨"ssMulti", [i64], [i64], fun _ _ (x, ()) =>
  .call "tinyCallee" (as := [i64]) (bs := [i64]) (.var x, ()) fun (a, ()) =>
  addChain 10 (.var a)⟩

def ssCaller1 : Fn := ⟨"scaller1", [i64], [i64], fun _ _ (x, ()) =>
  .call "ssSingle" (as := [i64]) (bs := [i64]) (.var x, ()) fun (a, ()) =>
  .call "ssMulti" (as := [i64]) (bs := [i64]) (.var a, ()) fun (b, ()) =>
  .ret (.var b, ())⟩

def ssCaller2 : Fn := ⟨"scaller2", [i64], [i64], fun _ _ (x, ()) =>
  .call "ssMulti" (as := [i64]) (bs := [i64]) (.var x, ()) fun (b, ()) =>
  .ret (.var b, ())⟩

def ssMod : Module where
  fns := [tinyCallee, ssSingle, ssMulti, ssCaller1, ssCaller2]

def ssPol : InlinePolicy :=
  { budget := fun _ => 5, leafMax := 6, singleSiteMax := 15 }

theorem ssPol_single_only :
    let body :=
      ((ssMod.inlinePolicy ssPol).fns.getD 3 dummyFn).body
        (fun _ => Unit) (fun _ => Unit) (Tup.units [i64])
    Expr.checkCallsOk [⟨"ssMulti", [i64], [i64]⟩] [] body = true ∧
      Expr.checkCallsOk [] [] body = false := by
  decide

/-! ## 3. `maxCallerSize` cap (pre-cap + greedy size cap) -/

def capSmall : Fn := ⟨"capSmall", [i64], [i64], fun _ _ (x, ()) => addChain 4 (.var x)⟩

def capMed : Fn := ⟨"capMed", [i64], [i64], fun _ _ (x, ()) => addChain 10 (.var x)⟩

/-- Pre-inline size is `7`, so with `maxCallerSize = 15`: `capSmall` (`5`, `7+5=12 ≤ 15`)
inlines while `capMed` (`11`, `12+11=23 > 15`) stays out-of-line. -/
def capBoundedCaller : Fn := ⟨"capBounded", [i64], [i64], fun _ _ (x, ()) =>
  .call "capSmall" (as := [i64]) (bs := [i64]) (.var x, ()) fun (a, ()) =>
  .call "capMed" (as := [i64]) (bs := [i64]) (.var a, ()) fun (b, ()) =>
  addChain 4 (.var b)⟩

/-- Pre-inline size is `17 > maxCallerSize (15)`, so zero calls are inlined. -/
def capOverCaller : Fn := ⟨"capOver", [i64], [i64], fun _ _ (x, ()) =>
  .call "capSmall" (as := [i64]) (bs := [i64]) (.var x, ()) fun (a, ()) =>
  addChain 15 (.var a)⟩

def capMod : Module where
  fns := [capSmall, capMed, capBoundedCaller, capOverCaller]

def capPol : InlinePolicy :=
  { budget := fun _ => 20, leafMax := 20, singleSiteMax := 20, maxCallerSize := 15 }

theorem capPol_caller_cap :
    let fns := (capMod.inlinePolicy capPol).fns
    let b1 := (fns.getD 2 dummyFn).body (fun _ => Unit) (fun _ => Unit) (Tup.units [i64])
    let b2 := (fns.getD 3 dummyFn).body (fun _ => Unit) (fun _ => Unit) (Tup.units [i64])
    capBoundedCaller.size = 7 ∧ capOverCaller.size = 17 ∧
      (fns.getD 2 dummyFn).size ≤ 15 ∧
      Expr.checkCallsOk [⟨"capMed", [i64], [i64]⟩] [] b1 = true ∧
      Expr.checkCallsOk [] [] b1 = false ∧
      Expr.checkCallsOk [⟨"capSmall", [i64], [i64]⟩] [] b2 = true := by
  decide

/-! ## 4. `keepOutOfLine` exclusion -/

def oolLeaf : Fn := ⟨"oolLeaf", [i64], [i64], fun _ _ (x, ()) =>
  .let_ (op2 (.add i64) (.var x) (.imm 1)) fun (y, ()) => .ret (.var y, ())⟩

def oolCaller : Fn := ⟨"oolCaller", [i64], [i64], fun _ _ (x, ()) =>
  .call "oolLeaf" (as := [i64]) (bs := [i64]) (.var x, ()) fun (a, ()) =>
  .ret (.var a, ())⟩

def oolMod : Module where
  fns := [oolLeaf, oolCaller]

def oolPol : InlinePolicy :=
  { budget := fun _ => 100, leafMax := 100, singleSiteMax := 100, keepOutOfLine := ["oolLeaf"] }

theorem oolPol_excludes_ool :
    let body :=
      ((oolMod.inlinePolicy oolPol).fns.getD 1 dummyFn).body
        (fun _ => Unit) (fun _ => Unit) (Tup.units [i64])
    Expr.checkCallsOk [⟨"oolLeaf", [i64], [i64]⟩] [] body = true ∧
      Expr.checkCallsOk [] [] body = false := by
  decide

/-! ## 5. Structural gates (`requireLoopSite`, `maxTotalDup`, `maxCalleeLoops`, `maxCallerCalls`) -/

def loopCallee : Fn := ⟨"loopCallee", [i64], [i64], fun _ _ (x, ()) => addChain 7 (.var x)⟩

def flatCallee : Fn := ⟨"flatCallee", [i64], [i64], fun _ _ (x, ()) => addChain 7 (.var x)⟩

def loopCaller : Fn := ⟨"loopCaller", [i64], [i64], fun _ _ (x, ()) =>
  .group (sig := [[i64]])
    (fun (lp, ()) => .cons (fun (v, ()) =>
      .call "loopCallee" (as := [i64]) (bs := [i64]) (.var v, ()) fun (r, ()) =>
      .jnz (.imm false) (.jump lp (.var r, ())) (.ret (.var r, ()))) .nil)
    (fun (lp, ()) =>
      .call "flatCallee" (as := [i64]) (bs := [i64]) (.var x, ()) fun (y, ()) =>
      .jump lp (.var y, ()))⟩

def loopMod : Module where
  fns := [loopCallee, flatCallee, loopCaller]

def loopPol : InlinePolicy :=
  { budget := fun _ => 5, leafMax := 20, requireLoopSite := true }

theorem loopSitePol_filters :
    let body :=
      ((loopMod.inlinePolicy loopPol).fns.getD 2 dummyFn).body
        (fun _ => Unit) (fun _ => Unit) (Tup.units [i64])
    Expr.checkCallsOk [⟨"flatCallee", [i64], [i64]⟩] [] body = true ∧
      Expr.checkCallsOk [] [] body = false := by
  decide

def dupCallee1 : Fn := ⟨"dupCallee1", [i64], [i64], fun _ _ (x, ()) => addChain 7 (.var x)⟩

def dupCallee2 : Fn := ⟨"dupCallee2", [i64], [i64], fun _ _ (x, ()) => addChain 7 (.var x)⟩

def dupCaller : Fn := ⟨"dupCaller", [i64], [i64], fun _ _ (x, ()) =>
  .call "dupCallee1" (as := [i64]) (bs := [i64]) (.var x, ()) fun (a, ()) =>
  .call "dupCallee2" (as := [i64]) (bs := [i64]) (.var a, ()) fun (b, ()) =>
  .call "dupCallee2" (as := [i64]) (bs := [i64]) (.var b, ()) fun (c, ()) =>
  .ret (.var c, ())⟩

def dupMod : Module where
  fns := [dupCallee1, dupCallee2, dupCaller]

def dupPol : InlinePolicy :=
  { budget := fun _ => 5, leafMax := 20, maxTotalDup := 10 }

theorem dupPol_filters :
    let body :=
      ((dupMod.inlinePolicy dupPol).fns.getD 2 dummyFn).body
        (fun _ => Unit) (fun _ => Unit) (Tup.units [i64])
    Expr.checkCallsOk [⟨"dupCallee2", [i64], [i64]⟩] [] body = true ∧
      Expr.checkCallsOk [] [] body = false := by
  decide

/-! ## 6. `InlinePolicy.b5` & full soundness (`optInlinePolicy_*`) -/

theorem b5_params :
    InlinePolicy.b5.leafMax = 115 ∧
      InlinePolicy.b5.singleSiteMax = 190 ∧
      InlinePolicy.b5.maxCallerSize = 660 ∧
      InlinePolicy.b5.maxCalleeCalls = 2 ∧
      InlinePolicy.b5.maxCalleeLoops = some 2 ∧
      InlinePolicy.b5.maxTotalDup = 450 ∧
      InlinePolicy.b5.leafNoLoopMaxDup = 800 ∧
      InlinePolicy.b5.requireLoopSite = true ∧
      InlinePolicy.b5.maxCallerCalls = 6 ∧
      InlinePolicy.b5.exemptNoLoopMax = 190 ∧
      InlinePolicy.b5.maxCallerLoopDup = 4 ∧
      InlinePolicy.b5.coldLoopGuardMax = 50 ∧
      InlinePolicy.b5.keepOutOfLine = [] := by
  decide

theorem capMod_checkAcyclic : capMod.checkAcyclic = true := by rfl

theorem capMod_wf : ∀ fn ∈ capMod.fns, fn.Wf := by
  intro fn hfn
  simp only [capMod, List.mem_cons, List.not_mem_nil, or_false] at hfn
  rcases hfn with rfl | rfl | rfl | rfl <;> (unfold Fn.Wf; t_wf_reify)

theorem capMod_supp : ∀ fn ∈ capMod.fns, fn.body.supportsSource LegalTarget.x64AVX512 = true := by
  decide

def capΓ : Env
  | "capSmall", [.bits 64], [.bits 64], (x, ()), m, Q, _ => Q (x + 4#64, ()) m
  | "capMed", [.bits 64], [.bits 64], (x, ()), m, Q, _ => Q (x + 10#64, ()) m
  | "capBounded", [.bits 64], [.bits 64], (x, ()), m, Q, _ => Q (x + 18#64, ()) m
  | "capOver", [.bits 64], [.bits 64], (x, ()), m, Q, _ => Q (x + 19#64, ()) m
  | _, _, _, _, _, _, _ => False

theorem capMod_modOk : ModuleOk capΓ capMod := by
  refine Module.moduleOk_of_checkAcyclic capMod_checkAcyclic capMod_wf ?_
  intro fn hfn xs m Q X hΓ
  simp only [capMod, List.mem_cons, List.not_mem_nil, or_false] at hfn
  rcases hfn with rfl | rfl | rfl | rfl
  · rcases xs with ⟨x, ⟨⟩⟩
    refine addChain_wp capΓ 4 x m Q X ?_
    rw [show BitVec.ofNat 64 4 = 4#64 from rfl]; exact hΓ
  · rcases xs with ⟨x, ⟨⟩⟩
    refine addChain_wp capΓ 10 x m Q X ?_
    rw [show BitVec.ofNat 64 10 = 10#64 from rfl]; exact hΓ
  · rcases xs with ⟨x, ⟨⟩⟩
    refine ⟨fun r m' => r = (x + 4#64, ()) ∧ m' = m, fun _ _ _ _ => False,
      ⟨rfl, rfl⟩, ?_, fun _ _ _ _ h => h.elim⟩
    rintro ⟨a, ⟨⟩⟩ m1 ⟨ha, hm1⟩; subst hm1
    have ha' : a = x + 4#64 := (Prod.ext_iff.mp ha).1; subst ha'
    refine ⟨fun r m' => r = ((x + 4#64) + 10#64, ()) ∧ m' = m1, fun _ _ _ _ => False,
      ⟨rfl, rfl⟩, ?_, fun _ _ _ _ h => h.elim⟩
    rintro ⟨b, ⟨⟩⟩ m2 ⟨hb, hm2⟩; subst hm2
    have hb' : b = (x + 4#64) + 10#64 := (Prod.ext_iff.mp hb).1; subst hb'
    refine addChain_wp capΓ 4 ((x + 4#64) + 10#64) m2 Q X ?_
    have h18 : (x + 4#64) + 10#64 + BitVec.ofNat 64 4 = x + 18#64 := by
      rw [BitVec.add_assoc, BitVec.add_assoc]; rfl
    rwa [h18]
  · rcases xs with ⟨x, ⟨⟩⟩
    refine ⟨fun r m' => r = (x + 4#64, ()) ∧ m' = m, fun _ _ _ _ => False,
      ⟨rfl, rfl⟩, ?_, fun _ _ _ _ h => h.elim⟩
    rintro ⟨a, ⟨⟩⟩ m1 ⟨ha, hm1⟩; subst hm1
    have ha' : a = x + 4#64 := (Prod.ext_iff.mp ha).1; subst ha'
    refine addChain_wp capΓ 15 (x + 4#64) m1 Q X ?_
    have h19 : (x + 4#64) + BitVec.ofNat 64 15 = x + 19#64 := by
      rw [BitVec.add_assoc]; rfl
    rwa [h19]

theorem cap_wf : ∀ f ∈ (capMod.optInlinePolicy capPol).fns, f.Wf :=
  Module.optInlinePolicy_wf capPol capMod_checkAcyclic capMod_wf

theorem cap_spec :
    ∀ f ∈ (capMod.optInlinePolicy capPol).fns, ∀ xs m Q X,
      capΓ f.name f.as f.rs xs m Q X → Func.wp capΓ f.body xs m Q X :=
  Module.optInlinePolicy_spec capPol capMod_modOk

theorem cap_calls :
    ∀ pre fn post, (capMod.optInlinePolicy capPol).fns = pre ++ fn :: post →
      fn.callsOk (pre.map Fn.sig ++ capMod.externs.map Extern.sig) capMod.exits :=
  Module.optInlinePolicy_callsOk capPol capMod_checkAcyclic capMod_wf

theorem cap_acyc : (capMod.optInlinePolicy capPol).checkAcyclic = true :=
  Module.optInlinePolicy_acyclic capPol capMod_checkAcyclic capMod_wf

theorem cap_supp :
    ∀ f ∈ (capMod.optInlinePolicy capPol).fns,
      f.body.supportsSource LegalTarget.x64AVX512 = true :=
  Module.optInlinePolicy_supportsSource LegalTarget.x64AVX512 capPol capMod_wf capMod_supp

theorem cap_b5_wf : ∀ f ∈ (capMod.optInlinePolicy InlinePolicy.b5).fns, f.Wf :=
  Module.optInlinePolicy_wf InlinePolicy.b5 capMod_checkAcyclic capMod_wf

theorem cap_b5_supp :
    ∀ f ∈ (capMod.optInlinePolicy InlinePolicy.b5).fns,
      f.body.supportsSource LegalTarget.x64AVX512 = true :=
  Module.optInlinePolicy_supportsSource LegalTarget.x64AVX512 InlinePolicy.b5 capMod_wf capMod_supp

/-! ## 7. Axiom Audit -/

#print axioms LeanQbe.T.Module.optInlinePolicy_wf
#print axioms LeanQbe.T.Module.optInlinePolicy_spec
#print axioms LeanQbe.T.Module.optInlinePolicy_callsOk
#print axioms LeanQbe.T.Module.optInlinePolicy_acyclic
#print axioms LeanQbe.T.Module.optInlinePolicy_supportsSource
#print axioms leafPol_leaf_only
#print axioms ssPol_single_only
#print axioms capPol_caller_cap
#print axioms oolPol_excludes_ool
#print axioms loopSitePol_filters
#print axioms dupPol_filters
#print axioms b5_params
#print axioms cap_wf
#print axioms cap_spec
#print axioms cap_calls
#print axioms cap_acyc
#print axioms cap_supp
#print axioms cap_b5_wf
#print axioms cap_b5_supp

end LeanQbeTest.T.InlinePolicyB5Test
