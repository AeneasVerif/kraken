module

public import LeanQbe.T.IL
public import LeanQbe.T.Inline
public import LeanQbe.T.InlineLemmas
public import LeanQbe.T.Main
public import LeanQbe.T.MainInline
meta import LeanQbe.T.IL
meta import LeanQbe.T.Inline

/-!
# Tests for tuned `InlinePolicy.b5` heuristics (`LeanQbe.T.Inline`)

Covers:
1. `coldLoopGuardMax` (`[coldLoopGuardMin, coldLoopGuardMax]`): blocks small-to-medium
   loop-containing slow-path callees inside loop-free callers when all sites sit behind
   trivial `.jump`/`.ret` `.jnz` guards, while preserving loop callers, non-trivial guards,
   and loop-free helpers.
2. `maxCallerLoopDup`: blocks repeated inlining of loop callees when
   `callsInCaller * callee.numLoops > maxCallerLoopDup` (`5 > 4`), while allowing `<= 4`.
3. `exemptNoLoopMax`: allows loop-free approved callees inside high-call callers
   (`numCalls > maxCallerCalls`) while keeping loop-containing callees out-of-line.
4. `leafNoLoopMaxDup`: allows higher total duplication (`<= 800`) for loop-free leaf callees
   under `Module.inlinePolicy` (`maxTotalDup := 450`), while keeping loop callees capped.
5. `InlinePolicy.b5` invariants and kernel-checked `Module.inlinePolicy_ok` /
   `Module.optInlinePolicy_*` soundness preservation (standard-axiom `#print axioms`).
-/

set_option autoImplicit false

namespace LeanQbeTest.T.InlineB5

open LeanQbe.T

public section

private def dummyFn : Fn := ⟨"", [], [], fun _ _ _ => .hlt⟩

private def hasCall (sym : Sym) (fn : Fn) : Bool :=
  lookupCallSite
    (exprCallSites [] (fn.body (fun _ => Unit) (fun _ => Unit) (Tup.units fn.as))) sym > 0

private def addChain : (n : Nat) → {V : Ty → Type} → {L : List Ty → Type} →
    Arg V i64 → Expr V L [i64]
  | 0, _, _, a => .ret (a, ())
  | n + 1, _, _, a =>
      .let_ (op2 (.add i64) a (.imm 1)) fun (y, ()) =>
      addChain n (.var y)

/-- Build a loop-containing leaf function (`numLoops = 1`, `numCalls = 0`) with `n` leading
adds so total `Fn.size` falls cleanly inside `[20, 50]`. -/
private def mkLoopLeaf (nm : Sym) (n : Nat) : Fn :=
  ⟨nm, [i64], [i64], fun _ _ (x, ()) =>
    .group (sig := [[i64]])
      (fun (lp, ()) => .cons (fun (i, ()) =>
        .let_ (op2 (.add i64) (.var i) (.imm 1)) fun (i', ()) =>
        .jnz (.imm false) (.jump lp (.var i', ())) (addChain n (.var i'))) .nil)
      (fun (lp, ()) => .jump lp (.var x, ()))⟩

/-- Build a loop-free leaf helper (`numLoops = 0`, `numCalls = 0`). -/
private def mkPureLeaf (nm : Sym) (n : Nat) : Fn :=
  ⟨nm, [i64], [i64], fun _ _ (x, ()) => addChain n (.var x)⟩

/-! ## 1. `coldLoopGuardMax` (cold single-sided trivial `.jnz` slow-path guard) -/

private def coldLp : Fn := mkLoopLeaf "cold_lp" 18
private def noLpCallee : Fn := mkPureLeaf "noloop_leaf" 24

private def tinyId : Fn :=
  ⟨"tiny_id", [i64], [i64], fun _ _ (x, ()) => .ret (.var x, ())⟩

private def hotCaller : Fn :=
  ⟨"hot_caller", [i64], [i64], fun _ _ (x, ()) =>
    .group (sig := [[i64]])
      (fun (lp, ()) => .cons (fun (i, ()) =>
        .call "cold_lp" (as := [i64]) (bs := [i64]) (.var i, ()) fun (r, ()) =>
        .call "noloop_leaf" (as := [i64]) (bs := [i64]) (.var r, ()) fun (r2, ()) =>
        .jnz (.imm false) (.jump lp (.var r2, ())) (.ret (.var r2, ()))) .nil)
      (fun (lp, ()) => .jump lp (.var x, ()))⟩

private def coldGuardCaller : Fn :=
  ⟨"cold_guard_caller", [i64], [i64], fun _ _ (x, ()) =>
    .jnz (.imm true)
      (.call "cold_lp" (as := [i64]) (bs := [i64]) (.var x, ()) fun (r, ()) => .ret (.var r, ()))
      (.ret (.var x, ()))⟩

private def twoWayCaller : Fn :=
  ⟨"two_way_caller", [i64], [i64], fun _ _ (x, ()) =>
    .jnz (.imm true)
      (.call "cold_lp" (as := [i64]) (bs := [i64]) (.var x, ()) fun (r, ()) => .ret (.var r, ()))
      (.call "tiny_id" (as := [i64]) (bs := [i64]) (.var x, ()) fun (r, ()) => .ret (.var r, ()))⟩

private def noLpGuardCaller : Fn :=
  ⟨"nolp_guard_caller", [i64], [i64], fun _ _ (x, ()) =>
    .jnz (.imm true)
      (.call "noloop_leaf" (as := [i64]) (bs := [i64]) (.var x, ()) fun (r, ()) =>
        .ret (.var r, ()))
      (.ret (.var x, ()))⟩

private def coldGuardMod : Module where
  fns := [tinyId, coldLp, noLpCallee, hotCaller, coldGuardCaller, twoWayCaller, noLpGuardCaller]

private def coldGuardPol : InlinePolicy :=
  { budget := fun _ => 40
    leafMax := 115
    maxCallerSize := 660
    maxCalleeLoops := some 2
    maxTotalDup := 450
    requireLoopSite := true
    maxCallerCalls := 6
    coldLoopGuardMin := 20
    coldLoopGuardMax := 50 }

#guard coldLp.size ≥ 20 && coldLp.size ≤ 50 && coldLp.numLoops == 1
#guard noLpCallee.size == 25 && noLpCallee.numLoops == 0
#guard hasCall "cold_lp"
    (((coldGuardMod.inlinePolicy coldGuardPol).fns.getD 4 dummyFn)) == true
#guard hasCall "cold_lp"
    (((coldGuardMod.inlinePolicy { coldGuardPol with coldLoopGuardMax := 0 }).fns.getD 4 dummyFn))
      == false
#guard hasCall "cold_lp"
    (((coldGuardMod.inlinePolicy coldGuardPol).fns.getD 3 dummyFn)) == false
#guard hasCall "cold_lp"
    (((coldGuardMod.inlinePolicy coldGuardPol).fns.getD 5 dummyFn)) == false
#guard hasCall "noloop_leaf"
    (((coldGuardMod.inlinePolicy coldGuardPol).fns.getD 6 dummyFn)) == false

/-! ## 2. `maxCallerLoopDup` (per-`(caller, callee)` loop-copy cap) -/

private def smallLp : Fn := mkLoopLeaf "small_lp" 12

private def callN (sym : Sym) : Nat → {V : Ty → Type} → {L : List Ty → Type} →
    Arg V i64 → Expr V L [i64]
  | 0, _, _, a => .ret (a, ())
  | n + 1, _, _, a =>
      .call sym (as := [i64]) (bs := [i64]) (a, ()) fun (r, ()) =>
      callN sym n (.var r)

private def smallLpHot : Fn :=
  ⟨"small_lp_hot", [i64], [i64], fun _ _ (x, ()) =>
    .group (sig := [[i64]])
      (fun (lp, ()) => .cons (fun (i, ()) =>
        .call "small_lp" (as := [i64]) (bs := [i64]) (.var i, ()) fun (r, ()) =>
        .jnz (.imm false) (.jump lp (.var r, ())) (.ret (.var r, ()))) .nil)
      (fun (lp, ()) => .jump lp (.var x, ()))⟩

private def caller4Lp : Fn := ⟨"caller_4lp", [i64], [i64], fun _ _ (x, ()) =>
  callN "small_lp" 4 (.var x)⟩

private def caller5Lp : Fn := ⟨"caller_5lp", [i64], [i64], fun _ _ (x, ()) =>
  callN "small_lp" 5 (.var x)⟩

private def lpDupMod : Module where
  fns := [smallLp, smallLpHot, caller4Lp, caller5Lp]

private def lpDupPol : InlinePolicy :=
  { budget := fun _ => 40
    maxCallerSize := 660
    maxCalleeLoops := some 2
    maxTotalDup := 450
    requireLoopSite := true
    maxCallerCalls := 6
    maxCallerLoopDup := 4 }

#guard smallLp.size ≤ 40 && smallLp.numLoops == 1
#guard hasCall "small_lp" (((lpDupMod.inlinePolicy lpDupPol).fns.getD 2 dummyFn)) == false
#guard hasCall "small_lp" (((lpDupMod.inlinePolicy lpDupPol).fns.getD 3 dummyFn)) == true
#guard hasCall "small_lp"
    (((lpDupMod.inlinePolicy { lpDupPol with maxCallerLoopDup := 0 }).fns.getD 3 dummyFn))
      == false

/-! ## 3. `exemptNoLoopMax` (loop-free helpers inside busy callers) -/

private def noLpMid : Fn := mkPureLeaf "noloop_mid" 44
private def lpMid : Fn := mkLoopLeaf "loop_mid" 42

private def busyHotAnchor : Fn :=
  ⟨"busy_anchor", [i64], [i64], fun _ _ (x, ()) =>
    .group (sig := [[i64]])
      (fun (lp, ()) => .cons (fun (i, ()) =>
        .call "noloop_mid" (as := [i64]) (bs := [i64]) (.var i, ()) fun (a, ()) =>
        .call "loop_mid" (as := [i64]) (bs := [i64]) (.var a, ()) fun (b, ()) =>
        .jnz (.imm false) (.jump lp (.var b, ())) (.ret (.var b, ()))) .nil)
      (fun (lp, ()) => .jump lp (.var x, ()))⟩

private def busyCaller : Fn :=
  ⟨"busy_caller", [i64], [i64], fun _ _ (x, ()) =>
    .call "tiny_id" (as := [i64]) (bs := [i64]) (.var x, ()) fun (r0, ()) =>
    .call "tiny_id" (as := [i64]) (bs := [i64]) (.var r0, ()) fun (r1, ()) =>
    .call "tiny_id" (as := [i64]) (bs := [i64]) (.var r1, ()) fun (r2, ()) =>
    .call "tiny_id" (as := [i64]) (bs := [i64]) (.var r2, ()) fun (r3, ()) =>
    .call "tiny_id" (as := [i64]) (bs := [i64]) (.var r3, ()) fun (r4, ()) =>
    .call "noloop_mid" (as := [i64]) (bs := [i64]) (.var r4, ()) fun (r5, ()) =>
    .call "loop_mid" (as := [i64]) (bs := [i64]) (.var r5, ()) fun (r6, ()) =>
    .ret (.var r6, ())⟩

private def exemptMod : Module where
  fns := [tinyId, noLpMid, lpMid, busyHotAnchor, busyCaller]

private def exemptPol : InlinePolicy :=
  { budget := fun _ => 40
    leafMax := 115
    maxCallerSize := 660
    maxCalleeLoops := some 2
    maxTotalDup := 450
    requireLoopSite := true
    maxCallerCalls := 6
    exemptNoLoopMax := 190 }

#guard noLpMid.size == 45 && noLpMid.numLoops == 0
#guard lpMid.size > 40 && lpMid.size ≤ 190 && lpMid.numLoops == 1
#guard hasCall "noloop_mid" (((exemptMod.inlinePolicy exemptPol).fns.getD 4 dummyFn)) == false
#guard hasCall "loop_mid" (((exemptMod.inlinePolicy exemptPol).fns.getD 4 dummyFn)) == true
#guard hasCall "noloop_mid"
    (((exemptMod.inlinePolicy { exemptPol with exemptNoLoopMax := 0 }).fns.getD 4 dummyFn)) == true

/-! ## 4. `leafNoLoopMaxDup` (elevated duplication cap for loop-free leaves) -/

private def wideLeaf : Fn := mkPureLeaf "wide_leaf" 8

private def wideHot : Fn :=
  ⟨"wide_hot", [i64], [i64], fun _ _ (x, ()) =>
    .group (sig := [[i64]])
      (fun (lp, ()) => .cons (fun (i, ()) =>
        .call "wide_leaf" (as := [i64]) (bs := [i64]) (.var i, ()) fun (r, ()) =>
        .jnz (.imm false) (.jump lp (.var r, ())) (.ret (.var r, ()))) .nil)
      (fun (lp, ()) => .jump lp (.var x, ()))⟩

private def wideUsers : List Fn :=
  ["u1", "u2", "u3", "u4", "u5"].map fun nm =>
    ⟨nm, [i64], [i64], fun _ _ (x, ()) =>
      .call "wide_leaf" (as := [i64]) (bs := [i64]) (.var x, ()) fun (r, ()) =>
      .ret (.var r, ())⟩

private def dupMod : Module where
  fns := [wideLeaf, wideHot] ++ wideUsers

private def dupPol : InlinePolicy :=
  { budget := fun _ => 5
    leafMax := 12
    maxCallerSize := 660
    maxCalleeLoops := some 2
    maxTotalDup := 45
    leafNoLoopMaxDup := 80
    requireLoopSite := true
    maxCallerCalls := 6 }

#guard wideLeaf.size == 9 && wideLeaf.isLeaf && wideLeaf.numLoops == 0
#guard hasCall "wide_leaf" (((dupMod.inlinePolicy dupPol).fns.getD 1 dummyFn)) == false
#guard hasCall "wide_leaf"
    (((dupMod.inlinePolicy { dupPol with leafNoLoopMaxDup := 0 }).fns.getD 1 dummyFn)) == true

/-! ## 5. Kernel-checked soundness & `InlinePolicy.b5` defaults (standard axioms) -/

theorem b5_defaults :
    InlinePolicy.b5.leafMax = 115 ∧
      InlinePolicy.b5.leafNoLoopMaxDup = 800 ∧
      InlinePolicy.b5.maxCallerCalls = 6 ∧
      InlinePolicy.b5.exemptNoLoopMax = 190 ∧
      InlinePolicy.b5.maxCallerLoopDup = 4 ∧
      InlinePolicy.b5.coldLoopGuardMin = 20 ∧
      InlinePolicy.b5.coldLoopGuardMax = 50 := by
  decide

theorem b5_inlines_ok {Γ : Env} {M : Module} (hM : ModuleOk Γ M) :
    ModuleOk Γ (M.inlinePolicy InlinePolicy.b5) :=
  Module.inlinePolicy_ok InlinePolicy.b5 hM

theorem b5_opt_wf {M : Module} (hchk : M.checkAcyclic = true)
    (hwf : ∀ f ∈ M.fns, f.Wf) :
    ∀ f ∈ (M.optInlinePolicy InlinePolicy.b5).fns, f.Wf :=
  Module.optInlinePolicy_wf InlinePolicy.b5 hchk hwf

theorem b5_opt_supp {M : Module} (target : LegalTarget) (hwf : ∀ f ∈ M.fns, f.Wf)
    (hsupp : ∀ f ∈ M.fns, f.body.supportsSource target = true) :
    ∀ f ∈ (M.optInlinePolicy InlinePolicy.b5).fns,
      f.body.supportsSource target = true :=
  Module.optInlinePolicy_supportsSource target InlinePolicy.b5 hwf hsupp

theorem b5_opt_acyc {M : Module} (hchk : M.checkAcyclic = true)
    (hwf : ∀ f ∈ M.fns, f.Wf) :
    (M.optInlinePolicy InlinePolicy.b5).checkAcyclic = true :=
  Module.optInlinePolicy_checkAcyclic InlinePolicy.b5 hchk hwf

theorem b5_opt_calls {M : Module} (hchk : M.checkAcyclic = true)
    (hwf : ∀ f ∈ M.fns, f.Wf) :
    ∀ pre fn post, (M.optInlinePolicy InlinePolicy.b5).fns = pre ++ fn :: post →
      fn.callsOk (pre.map Fn.sig ++ M.externs.map Extern.sig) M.exits :=
  Module.optInlinePolicy_callsOk InlinePolicy.b5 hchk hwf

#guard coldGuardMod.checkAcyclic == true
#guard lpDupMod.checkAcyclic == true
#guard exemptMod.checkAcyclic == true
#guard dupMod.checkAcyclic == true

#print axioms b5_defaults
#print axioms b5_inlines_ok
#print axioms b5_opt_wf
#print axioms b5_opt_supp
#print axioms b5_opt_acyc
#print axioms b5_opt_calls

end

end LeanQbeTest.T.InlineB5
