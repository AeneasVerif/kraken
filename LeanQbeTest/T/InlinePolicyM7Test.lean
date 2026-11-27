module

public import LeanQbe.T.Examples.Kissat.FullM7InlPolicy
public import LeanQbe.T.InlineLemmas
public import LeanQbe.T.WfLemmas
public import LeanQbe.T.FlatLemmas
public import LeanQbe.T.MainInline
meta import LeanQbe.T.Inline
meta import LeanQbe.T.MainInline
meta import LeanQbe.T.Examples.Kissat.FullM7InlPolicy

/-!
# Tests for `FullM7InlPolicy` (`m7PgoBudget` and `m7InlPolicy`)

Verifies:
1. `m7InlPolicy` structural caps (`leafMax = 0`, `singleSiteMax = 0`, `maxCallerSize = 1020`,
   `maxCalleeCalls = 2`, `maxCalleeLoops = some 2`, `maxTotalDup = 0`, `requireLoopSite = false`,
   `maxCallerCalls = 4`, `keepOutOfLine = []`).
2. `m7PgoBudget` spot values across M7-specific helpers, Phase-2 Kissat callees, delegated
   `m6PgoBudget` entries, and the `15`-node cold fallback floor.
3. Selective inlining on `m7TestMod` (`"full_arena_next"` at `20 ≤ 55` inlined; unflagged
   `"cold_unflagged_m7"` at `20 > 15` kept out-of-line).
4. Kernel soundness theorems (`Module.inlinePolicy_ok`, `optInlinePolicy_*`) and single-line
   `std3` `#print axioms` checks.
-/

set_option autoImplicit false

section

namespace LeanQbeTest.T.InlinePolicyM7Test

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.FullM7InlPolicy

/-! ## 1. Policy parameters & PGO spot checks -/

theorem m7_params :
    m7InlPolicy.leafMax = 0 ∧
      m7InlPolicy.singleSiteMax = 0 ∧
      m7InlPolicy.maxCallerSize = 1020 ∧
      m7InlPolicy.maxCalleeCalls = 2 ∧
      m7InlPolicy.maxCalleeLoops = some 2 ∧
      m7InlPolicy.maxTotalDup = 0 ∧
      m7InlPolicy.requireLoopSite = false ∧
      m7InlPolicy.maxCallerCalls = 4 ∧
      m7InlPolicy.keepOutOfLine = [] := by
  decide

theorem m7_pgo_spot :
    m7PgoBudget "full_log10_q16_m7" = 60 ∧
      m7PgoBudget "full_sort_tmp_sift_m7" = 106 ∧
      m7PgoBudget "full_cong_u64_sort_m7" = 146 ∧
      m7PgoBudget "full_bve_var_key_m7" = 68 ∧
      m7PgoBudget "full_walk_save_min_m7" = 108 ∧
      m7PgoBudget "full_bump_sift_m7" = 110 ∧
      m7PgoBudget "full_k6_assign_m7" = 84 ∧
      m7PgoBudget "full_bve_heap_up_m7" = 71 ∧
      m7PgoBudget "full_k512_assign" = 78 ∧
      m7PgoBudget "full_k512_backtrack" = 120 ∧
      m7PgoBudget "full_k512_ana_clause" = 131 ∧
      m7PgoBudget "full_heap_down" = 113 ∧
      m7PgoBudget "full_heap_pop" = 181 ∧
      m7PgoBudget "full_restore_bump_ana_m5" = 90 ∧
      m7PgoBudget "kissat_next_lit" = 235 ∧
      m7PgoBudget "full_arena_next" = 55 ∧
      m7PgoBudget "full_bve_mark_and_m6" = 172 ∧
      m7PgoBudget "full_viv_keys_m6" = 89 ∧
      m7PgoBudget "full_m4_sweep_refine_sig" = 53 ∧
      m7PgoBudget "cold_unflagged_m7" = 15 := by
  decide

/-! ## 2. Selective PGO vs cold floor behavior -/

def chainAddExpr (V : Ty → Type) (L : List Ty → Type) :
    Nat → V i64 → Expr V L [i64]
  | 0, x => .ret (.var x, ())
  | n + 1, x =>
      .let_ (op2 (.add i64) (.var x) (.imm 1)) fun (y, ()) =>
      chainAddExpr V L n y

def fnArenaMock : Fn := ⟨"full_arena_next", [i64], [i64], fun V L (x, ()) =>
  chainAddExpr V L 19 x⟩

def fnColdMock : Fn := ⟨"cold_unflagged_m7", [i64], [i64], fun V L (x, ()) =>
  chainAddExpr V L 19 x⟩

def fnM7Caller : Fn := ⟨"m7_caller", [i64], [i64], fun _ _ (a, ()) =>
  .call "full_arena_next" (as := [i64]) (bs := [i64]) (.var a, ()) fun (r1, ()) =>
  .call "cold_unflagged_m7" (as := [i64]) (bs := [i64]) (.var r1, ()) fun (r2, ()) =>
  .ret (.var r2, ())⟩

def m7TestMod : Module where
  fns := [fnArenaMock, fnColdMock, fnM7Caller]

def m7CallerCalls : List (Sym × Nat) :=
  match (m7TestMod.optInlinePolicy m7InlPolicy).fns.find? (·.name == "m7_caller") with
  | some fn => exprCallSites [] (fn.body (fun _ => Unit) (fun _ => Unit) (Tup.units fn.as))
  | none => []

#guard fnArenaMock.size == 20
#guard fnColdMock.size == 20
#guard lookupCallSite m7CallerCalls "full_arena_next" == 0
#guard lookupCallSite m7CallerCalls "cold_unflagged_m7" == 1

theorem m7TestMod_checkAcyclic : m7TestMod.checkAcyclic = true := by
  rfl

theorem m7TestMod_wf : ∀ f ∈ m7TestMod.fns, f.Wf := by
  intro f hf
  simp only [m7TestMod, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · unfold Fn.Wf; dsimp only [fnArenaMock, chainAddExpr]; t_wf_reify
  · unfold Fn.Wf; dsimp only [fnColdMock, chainAddExpr]; t_wf_reify
  · unfold Fn.Wf; dsimp only [fnM7Caller]; t_wf_reify

/-! ## 3. Kernel soundness theorems under `m7InlPolicy` (`std3`, `<115c`) -/

theorem m7_inline_ok {Γ : Env} {M : Module} (hM : ModuleOk Γ M) :
    ModuleOk Γ (M.inlinePolicy m7InlPolicy) :=
  Module.inlinePolicy_ok m7InlPolicy hM

theorem m7_opt_ok {Γ : Env} {M : Module} (hM : ModuleOk Γ M) :
    ModuleOk Γ (M.optInlinePolicy m7InlPolicy) :=
  Module.optInlinePolicy_ok m7InlPolicy hM

theorem m7_opt_wf {M : Module}
    (hchk : M.checkAcyclic = true) (hwf : ∀ f ∈ M.fns, f.Wf) :
    ∀ f ∈ (M.optInlinePolicy m7InlPolicy).fns, f.Wf :=
  Module.optInlinePolicy_wf m7InlPolicy hchk hwf

theorem m7_opt_spec {Γ : Env} {M : Module} (hM : ModuleOk Γ M) :
    ∀ f ∈ (M.optInlinePolicy m7InlPolicy).fns, ∀ xs m Q X,
      Γ f.name f.as f.rs xs m Q X → Func.wp Γ f.body xs m Q X :=
  Module.optInlinePolicy_spec m7InlPolicy hM

theorem m7_opt_calls {M : Module}
    (hchk : M.checkAcyclic = true) (hwf : ∀ f ∈ M.fns, f.Wf) :
    ∀ pre fn post, (M.optInlinePolicy m7InlPolicy).fns = pre ++ fn :: post →
      fn.callsOk (pre.map Fn.sig ++ M.externs.map Extern.sig) M.exits :=
  Module.optInlinePolicy_callsOk m7InlPolicy hchk hwf

theorem m7_opt_acyc {M : Module}
    (hchk : M.checkAcyclic = true) (hwf : ∀ f ∈ M.fns, f.Wf) :
    (M.optInlinePolicy m7InlPolicy).checkAcyclic = true :=
  Module.optInlinePolicy_checkAcyclic m7InlPolicy hchk hwf

theorem m7_opt_supp (target : LegalTarget) {M : Module}
    (hwf : ∀ f ∈ M.fns, f.Wf) (hsupp : ∀ f ∈ M.fns, f.body.supportsSource target = true) :
    ∀ f ∈ (M.optInlinePolicy m7InlPolicy).fns, f.body.supportsSource target = true :=
  Module.optInlinePolicy_supportsSource target m7InlPolicy hwf hsupp

theorem m7Test_wf :
    ∀ f ∈ (m7TestMod.optInlinePolicy m7InlPolicy).fns, f.Wf :=
  m7_opt_wf m7TestMod_checkAcyclic m7TestMod_wf

theorem m7Test_acyc :
    (m7TestMod.optInlinePolicy m7InlPolicy).checkAcyclic = true :=
  m7_opt_acyc m7TestMod_checkAcyclic m7TestMod_wf

#print axioms m7_params
#print axioms m7_pgo_spot
#print axioms m7_inline_ok
#print axioms m7_opt_ok
#print axioms m7_opt_wf
#print axioms m7_opt_spec
#print axioms m7_opt_calls
#print axioms m7_opt_acyc
#print axioms m7_opt_supp
#print axioms m7Test_wf
#print axioms m7Test_acyc

end LeanQbeTest.T.InlinePolicyM7Test
