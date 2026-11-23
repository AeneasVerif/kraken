/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM7
public import LeanQbe.T.Examples.Kissat.FullM7BvaGuFix
public import LeanQbe.T.Examples.Kissat.FullM7CompactFix
public import LeanQbe.T.Examples.Kissat.FullM7BvaV5Fix
public import LeanQbe.T.Examples.Kissat.FullM7ParityVivTiers
public import LeanQbe.T.Examples.Kissat.FullM7ParityBvaTie
public import LeanQbe.T.Examples.Kissat.FullM7Splice
meta import LeanQbe.T.Examples.Kissat.FullM7
meta import LeanQbe.T.Examples.Kissat.FullM7BvaGuFix
meta import LeanQbe.T.Examples.Kissat.FullM7CompactFix
meta import LeanQbe.T.Examples.Kissat.FullM7BvaV5Fix
meta import LeanQbe.T.Examples.Kissat.FullM7ParityVivTiers
meta import LeanQbe.T.Examples.Kissat.FullM7ParityBvaTie
meta import LeanQbe.T.Examples.Kissat.FullM7Splice
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal

/-!
# Kissat Unified `M7Plus` (`FullM7Plus` / `PLUS_T8_tie1_bb20`) Assembly (`410` Fns)

Assembles Target B (`m7PlusModule`, `410` functions, `0` externs, `0` exits) over unchanged
`FullM7.m7Module` via purely additive `spliceFns` with `17` disjoint canonical replacements:
1. `FullM7BvaGuFix` (`2` fns): `full_bva_commit`, `full_analyze_rsn`.
2. `FullM7CompactFix` (`4` fns): `full_compact_needed`, `full_compact_mark_live`,
   `full_compact_vars`, `full_sweep_copy`.
3. `FullM7BvaV5Fix` (`3` fns): `full_calc_max_v` (`cand = 4096ULL`), `full_forward_sub`,
   and `m7PlusEliminateFn` (`full_eliminate_m6`, adapting `full_eliminate_m7v5` via
   `renameFuncCalls` so `full_forward_sub_m7v5` resolves directly to `full_forward_sub`).
4. `FullM7ParityVivTiers` (`5` fns): `m6_hdr_sync_legacy_tiers`, `full_propagate_ignore_hot`,
   `full_propagate_ignore`, `full_vivify_tier_m6_hdr`, `full_vivify_m6_hdr`.
5. `FullM7ParityBvaTie` (`3` fns): `full_bva_pick_cand`, `full_probe_tail_m6`, `full_probe_m6`.

Certifies `m7PlusFns_length` (`410`), `m7PlusFns_wf`, fast `O(17)` `m7Plus_acyclic`,
`m7Plus_noExit`, and compile-time `#guard` checks across PrintCpp, PrintQbe, and all 4 ISAs.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM7Plus

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.FullM7
open LeanQbe.T.Examples.Kissat.FullM7BvaGuFix
open LeanQbe.T.Examples.Kissat.FullM7CompactFix
open LeanQbe.T.Examples.Kissat.FullM7BvaV5Fix
open LeanQbe.T.Examples.Kissat.FullM7ParityVivTiers
open LeanQbe.T.Examples.Kissat.FullM7ParityBvaTie
open LeanQbe.T.Examples.Kissat.FullM7Splice

/-! ## 1. Pure Callee-Renaming Combinator & `m7PlusEliminateFn` -/

mutual
  /-- Pointwise rewrite of direct callee symbols across a PHOAS expression. -/
  def renameExprCalls (σ : Sym → Sym) {V : Ty → Type} {C : List Ty → Type} {rs : List Ty} :
      Expr V C rs → Expr V C rs
    | .let_ op k => .let_ op fun r => renameExprCalls σ (k r)
    | .load t a k => .load t a fun v => renameExprCalls σ (k v)
    | .store v a k => .store v a (renameExprCalls σ k)
    | .call f args k => .call (σ f) args fun r => renameExprCalls σ (k r)
    | .jnz c t e => .jnz c (renameExprCalls σ t) (renameExprCalls σ e)
    | .jump j args => .jump j args
    | .ret vs => .ret vs
    | .exit f args => .exit f args
    | .hlt => .hlt
    | .group bodies k =>
        .group (fun Js => renameBlocksCalls σ (bodies Js)) (fun Js => renameExprCalls σ (k Js))

  /-- Pointwise rewrite of direct callee symbols across a PHOAS block list. -/
  def renameBlocksCalls (σ : Sym → Sym) {V : Ty → Type} {C : List Ty → Type} {rs : List Ty} :
      {sig : List (List Ty)} → Blocks V C rs sig → Blocks V C rs sig
    | [], .nil => .nil
    | _ :: _, .cons b bs =>
        .cons (fun xs => renameExprCalls σ (b xs)) (renameBlocksCalls σ bs)
end

/-- Pointwise rewrite of direct callee symbols across a closed PHOAS `Func`. -/
def renameFuncCalls (σ : Sym → Sym) {as rs : List Ty} (f : Func as rs) : Func as rs :=
  fun V C xs => renameExprCalls σ (f V C xs)

mutual
  /-- Callee renaming preserves relational `LeanQbe.T.Wf`. -/
  theorem wf_renameExprCalls {σ : Sym → Sym} {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type}
      {rs : List Ty} {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
      {e₁ : Expr V₁ L₁ rs} {e₂ : Expr V₂ L₂ rs} (hw : LeanQbe.T.Wf G D e₁ e₂) :
      LeanQbe.T.Wf G D (renameExprCalls σ e₁) (renameExprCalls σ e₂) := by
    cases hw with
    | let_ hop hk => exact .let_ hop fun xs₁ xs₂ => wf_renameExprCalls (hk xs₁ xs₂)
    | load t harg hk => exact .load t harg fun v₁ v₂ => wf_renameExprCalls (hk v₁ v₂)
    | store hv ha hk => exact .store hv ha (wf_renameExprCalls hk)
    | call f hargs hk =>
        exact .call (σ f) hargs fun xs₁ xs₂ => wf_renameExprCalls (hk xs₁ xs₂)
    | jnz hc ht he => exact .jnz hc (wf_renameExprCalls ht) (wf_renameExprCalls he)
    | jump hj hargs => exact .jump hj hargs
    | ret hvs => exact .ret hvs
    | exit f hargs => exact .exit f hargs
    | hlt => exact .hlt
    | group hb hk =>
        exact .group (fun Js₁ Js₂ => wfB_renameBlocksCalls (hb Js₁ Js₂))
          (fun Js₁ Js₂ => wf_renameExprCalls (hk Js₁ Js₂))

  /-- Callee renaming preserves relational `LeanQbe.T.WfB`. -/
  theorem wfB_renameBlocksCalls {σ : Sym → Sym} {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type}
      {rs : List Ty} {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {sig : List (List Ty)}
      {bs₁ : Blocks V₁ L₁ rs sig} {bs₂ : Blocks V₂ L₂ rs sig}
      (hw : LeanQbe.T.WfB G D bs₁ bs₂) :
      LeanQbe.T.WfB G D (renameBlocksCalls σ bs₁) (renameBlocksCalls σ bs₂) := by
    cases hw with
    | nil => exact .nil
    | cons hb hbs =>
        exact .cons (fun xs₁ xs₂ => wf_renameExprCalls (hb xs₁ xs₂)) (wfB_renameBlocksCalls hbs)
end

/-- Symbol map routing `full_forward_sub_m7v5` to canonical `full_forward_sub`. -/
def elimFwdSubRename : Sym → Sym
  | "full_forward_sub_m7v5" => "full_forward_sub"
  | s => s

/-- `Func` body for canonical `full_eliminate_m6` adapting `full_eliminate_m7v5_body` cleanly. -/
def m7PlusEliminateBody : Func [i64, .bool] [i64] :=
  renameFuncCalls elimFwdSubRename full_eliminate_m7v5_body

/-- Drop-in `Fn` handle replacing `full_eliminate_m6` in `FullM7Plus`. -/
def m7PlusEliminateFn : Fn :=
  ⟨"full_eliminate_m6", [i64, .bool], [i64], m7PlusEliminateBody⟩

theorem m7PlusEliminate_wf : Func.Wf m7PlusEliminateBody := fun _ _ _ _ xs₁ xs₂ =>
  wf_renameExprCalls (full_eliminate_m7v5_wf _ _ _ _ xs₁ xs₂)

/-! ## 2. `17` Disjoint Canonical Replacements & `410`-Fn `m7PlusModule` -/

/-- `12` Target B replacements applied on top of `FullM7ParityVivTiers` (`5` fns). -/
def m7PlusTailRepls : List Fn :=
  [ m7BvaCommitFn
  , m7AnalyzeRsnFn
  , m7fixCompactNeededFn
  , m7fixCompactMarkLiveFn
  , m7fixCompactVarsFn
  , m7fixSweepCopyFn
  , m7v5CalcMaxVFn
  , m7v5ForwardSubFn
  , m7PlusEliminateFn ] ++ m7ParityBvaTiePatchFns

/-- Complete list of `17` disjoint canonical replacement functions for `FullM7Plus`. -/
def m7PlusRepls : List Fn :=
  m7ParityVivTiersPatchFns ++ m7PlusTailRepls

/-- Transparent exposed splice helper so `m7PlusModule.fns` reduces in kernel/chunk inlining. -/
def mpSpliceFns (repls fs : List Fn) : List Fn :=
  fs.map fun f => (repls.find? (·.name == f.name)).getD f

private theorem mp_find_name_eq {repls : List Fn} {f r : Fn}
    (h : repls.find? (fun x => x.name == f.name) = some r) : r.name = f.name :=
  beq_iff_eq.mp (List.find?_some (p := fun x : Fn => x.name == f.name) h)

theorem mpSpliceFns_mem_of_ne {repls fs : List Fn} {g : Fn} (hg : g ∈ fs)
    (hne : ∀ r ∈ repls, r.name ≠ g.name) : g ∈ mpSpliceFns repls fs := by
  refine List.mem_map.mpr ⟨g, hg, ?_⟩
  cases h : repls.find? (fun x => x.name == g.name) with
  | none => rfl
  | some r => exact absurd (mp_find_name_eq h) (hne r (List.mem_of_find?_eq_some h))

theorem mpSpliceFns_length (repls fs : List Fn) :
    (mpSpliceFns repls fs).length = fs.length := by
  unfold mpSpliceFns; simp only [List.length_map]

theorem mpSpliceFns_sigs {repls fs : List Fn}
    (hsig : ∀ r ∈ repls, ∀ f ∈ fs, r.name = f.name → r.sig = f.sig) :
    (mpSpliceFns repls fs).map Fn.sig = fs.map Fn.sig := by
  unfold mpSpliceFns; rw [List.map_map]; apply List.map_congr_left
  intro f hf; dsimp only [Function.comp_def]
  cases h : repls.find? (fun x => x.name == f.name) with
  | none => rfl
  | some r => exact hsig r (List.mem_of_find?_eq_some h) f hf (mp_find_name_eq h)

theorem mpSpliceFns_wf {repls fs : List Fn}
    (hfs : ∀ f ∈ fs, f.Wf) (hr : ∀ r ∈ repls, r.Wf) :
    ∀ f ∈ mpSpliceFns repls fs, f.Wf := by
  intro f hf; rcases List.mem_map.mp hf with ⟨g, hg, rfl⟩
  cases h : repls.find? (fun x => x.name == g.name) with
  | none => exact hfs g hg
  | some r => exact hr r (List.mem_of_find?_eq_some h)

private theorem mpCheckFnsCallsOk_splice (exits : List Sym) (extSigs : List SigEntry) :
    ∀ (seen fs repls : List Fn),
    LeanQbe.T.Module.checkFnsCallsOk exits extSigs (seen.map Fn.sig) fs = true →
    (∀ r ∈ repls, ∀ f ∈ fs, r.name = f.name → r.sig = f.sig) →
    (∀ pre f post r, fs = pre ++ f :: post → r ∈ repls → r.name = f.name →
      r.checkCallsOk ((seen ++ pre).map Fn.sig ++ extSigs) exits = true) →
    LeanQbe.T.Module.checkFnsCallsOk exits extSigs (seen.map Fn.sig)
      (mpSpliceFns repls fs) = true
  | _, [], _, _, _, _ => rfl
  | seen, f :: rest, repls, hchk, hsig, hrepl => by
    simp only [LeanQbe.T.Module.checkFnsCallsOk, Bool.and_eq_true] at hchk
    unfold mpSpliceFns
    simp only [List.map_cons, LeanQbe.T.Module.checkFnsCallsOk, Bool.and_eq_true]
    have hhead_sig : ((repls.find? (fun x => x.name == f.name)).getD f).sig = f.sig := by
      cases h : repls.find? (fun x => x.name == f.name) with
      | none => rfl
      | some r =>
        exact hsig r (List.mem_of_find?_eq_some h) f List.mem_cons_self (mp_find_name_eq h)
    have hhead_ok : ((repls.find? (fun x => x.name == f.name)).getD f).checkCallsOk
        (seen.map Fn.sig ++ extSigs) exits = true := by
      cases h : repls.find? (fun x => x.name == f.name) with
      | none => exact hchk.1
      | some r =>
        simpa using hrepl [] f rest r rfl (List.mem_of_find?_eq_some h) (mp_find_name_eq h)
    refine ⟨hhead_ok, ?_⟩
    have hchk2 : LeanQbe.T.Module.checkFnsCallsOk exits extSigs
        ((seen ++ [f]).map Fn.sig) rest = true := by
      simpa only [List.map_append, List.map_singleton] using hchk.2
    rw [hhead_sig, show seen.map Fn.sig ++ [f.sig] = (seen ++ [f]).map Fn.sig by simp]
    exact mpCheckFnsCallsOk_splice exits extSigs (seen ++ [f]) rest repls hchk2
      (fun r hr g hg => hsig r hr g (List.mem_cons_of_mem f hg))
      (fun pre g post r hsp hr hnm => by
        rw [List.append_assoc]
        exact hrepl (f :: pre) g post r (by rw [hsp]; rfl) hr hnm)

private theorem mpSpliceModule_checkAcyclic {M : LeanQbe.T.Module} {repls : List Fn}
    (hM : M.checkAcyclic = true)
    (hsig : ∀ r ∈ repls, ∀ f ∈ M.fns, r.name = f.name → r.sig = f.sig)
    (hrepl : ∀ pre f post r, M.fns = pre ++ f :: post → r ∈ repls → r.name = f.name →
      r.checkCallsOk (pre.map Fn.sig ++ M.externs.map Extern.sig) M.exits = true) :
    ({ M with fns := mpSpliceFns repls M.fns } : LeanQbe.T.Module).checkAcyclic = true := by
  simp only [LeanQbe.T.Module.checkAcyclic, Bool.and_eq_true] at hM ⊢
  refine ⟨?_, mpCheckFnsCallsOk_splice M.exits (M.externs.map Extern.sig) [] M.fns repls
      hM.2 hsig hrepl⟩
  have hnames : ({ M with fns := mpSpliceFns repls M.fns } : LeanQbe.T.Module).names =
      M.names := by
    simp only [LeanQbe.T.Module.names]
    have hm := congrArg (List.map Prod.fst) (mpSpliceFns_sigs hsig)
    simp only [List.map_map, Function.comp_def, Fn.sig] at hm
    rw [hm]
  unfold LeanQbe.T.Module.checkNamesNodup
  rw [hnames]; exact hM.1

/-- Ordered `410`-function list of `FullM7Plus` (`PLUS_T8_tie1_bb20`). -/
def m7PlusFns : List Fn :=
  mpSpliceFns m7PlusRepls m7Fns

/-- Closed `410`-function `FullM7Plus` (`KissatM7Plus`) module (`0` externs, `0` exits). -/
def m7PlusModule : LeanQbe.T.Module :=
  { fns := m7PlusFns, externs := [], exits := [] }

theorem m7PlusRepls_length : m7PlusRepls.length = 17 := by rfl

theorem m7PlusRepls_names_nodup : (m7PlusRepls.map Fn.name).Nodup := by decide

theorem m7PlusFns_length : m7PlusFns.length = 410 := by
  unfold m7PlusFns
  rw [mpSpliceFns_length, FullM7Proof.m7Fns_length]

theorem m7PlusTailRepls_wf : ∀ r ∈ m7PlusTailRepls, r.Wf := by
  intro r hr
  simp only [m7PlusTailRepls, m7ParityBvaTiePatchFns, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hr
  rcases hr with
    (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl)
  · exact full_bva_commit_m7_wf
  · exact full_analyze_rsn_m7_wf
  · exact full_compact_needed_m7fix_wf
  · exact full_compact_mark_live_m7fix_wf
  · exact full_compact_vars_m7fix_wf
  · exact full_sweep_copy_m7fix_wf
  · exact full_calc_max_v_m7v5_wf
  · exact full_forward_sub_m7v5_wf
  · exact m7PlusEliminate_wf
  · exact full_bva_pick_cand_bt_wf
  · exact full_probe_tail_bt_wf
  · exact full_probe_bt_wf

theorem m7PlusRepls_wf : ∀ r ∈ m7PlusRepls, r.Wf := by
  intro r hr
  rcases List.mem_append.mp hr with h1 | h2
  · exact m7ParityVivTiersPatchFns_wf r h1
  · exact m7PlusTailRepls_wf r h2

theorem m7PlusFns_wf : ∀ f ∈ m7PlusFns, f.Wf :=
  mpSpliceFns_wf m7Fns_wf m7PlusRepls_wf

theorem m7Plus_noExit : m7PlusModule.exits = [] := rfl

/-! ## 3. Fast `O(17)` Acyclicity Proof (`m7Plus_acyclic`) -/

private theorem mp_p1 {k : Nat} (hk : k < 112) {s : SigEntry}
    (h : m7FnsPart1[k]?.map Fn.sig = some s) : m7Fns[k]?.map Fn.sig = some s := by
  rw [m7_get_p1 hk]; exact h

private theorem mp_p2 {k : Nat} (hk : k < 164) {s : SigEntry}
    (h : m7FnsPart2[k]?.map Fn.sig = some s) : m7Fns[112 + k]?.map Fn.sig = some s := by
  rw [m7_get_p2 hk]; exact h

private theorem mp_p3 {k : Nat} {s : SigEntry}
    (h : m7FnsPart3[k]?.map Fn.sig = some s) : m7Fns[276 + k]?.map Fn.sig = some s := by
  rw [m7_get_p3]; exact h

-- Replaced slot indices (17 total) and callee indices in `m7Fns`.
private theorem mp_idx_9 : m7Fns[9]?.map Fn.sig =
    some ("full_ilog10", [i64], [i64]) := mp_p1 (by decide) (by t_kernel_rfl)
private theorem mp_idx_11 : m7Fns[11]?.map Fn.sig =
    some ("full_arena_next", [i64, i32], [i32]) := mp_p1 (by decide) (by t_kernel_rfl)
private theorem mp_idx_12 : m7Fns[12]?.map Fn.sig =
    some ("full_alloc_cl", [i64, i32, i32, .bool], [i64]) := mp_p1 (by decide) (by t_kernel_rfl)
private theorem mp_idx_17 : m7Fns[17]?.map Fn.sig =
    some ("full_wstack_defrag", [i64], []) := mp_p1 (by decide) (by t_kernel_rfl)
private theorem mp_idx_18 : m7Fns[18]?.map Fn.sig =
    some ("full_watch_push", [i64, i32, i32, i32, i32], [.bool]) :=
  mp_p1 (by decide) (by t_kernel_rfl)
private theorem mp_idx_32 : m7Fns[32]?.map Fn.sig =
    some ("full_scale_delta_m5", [i64, i64], [i64]) := mp_p1 (by decide) (by t_kernel_rfl)
private theorem mp_idx_34 : m7Fns[34]?.map Fn.sig =
    some ("full_scale_delta", [i64, i64], [i64]) := mp_p1 (by decide) (by t_kernel_rfl)
private theorem mp_idx_35 : m7Fns[35]?.map Fn.sig =
    some ("full_assign_lvl", [i64, i32, i32, i32], []) := mp_p1 (by decide) (by t_kernel_rfl)
private theorem mp_idx_39 : m7Fns[39]?.map Fn.sig =
    some ("full_backtrack", [i64, i64], []) := mp_p1 (by decide) (by t_kernel_rfl)
private theorem mp_idx_43 : m7Fns[43]?.map Fn.sig =
    some ("full_fixed_bytes", [i64], [i64]) := mp_p1 (by decide) (by t_kernel_rfl)
private theorem mp_idx_46 : m7Fns[46]?.map Fn.sig =
    some ("full_calc_max_v", [i64, i64, i64, i64], [i64]) := mp_p1 (by decide) (by t_kernel_rfl)
private theorem mp_idx_56 : m7Fns[56]?.map Fn.sig =
    some ("m6_ext_ensure_init", [i64], []) := mp_p1 (by decide) (by t_kernel_rfl)
private theorem mp_idx_59 : m7Fns[59]?.map Fn.sig =
    some ("m6_hdr_sync_legacy_tiers", [i64], []) := mp_p1 (by decide) (by t_kernel_rfl)
private theorem mp_idx_66 : m7Fns[66]?.map Fn.sig =
    some ("m6_hdr_delaying", [i64, i64], [.bool]) := mp_p1 (by decide) (by t_kernel_rfl)
private theorem mp_idx_67 : m7Fns[67]?.map Fn.sig =
    some ("m6_hdr_bump_delay", [i64, i64], []) := mp_p1 (by decide) (by t_kernel_rfl)
private theorem mp_idx_68 : m7Fns[68]?.map Fn.sig =
    some ("m6_hdr_reduce_delay", [i64, i64], []) := mp_p1 (by decide) (by t_kernel_rfl)
private theorem mp_idx_70 : m7Fns[70]?.map Fn.sig =
    some ("m6_hdr_get_watermark", [i64, i64], [i64]) := mp_p1 (by decide) (by t_kernel_rfl)
private theorem mp_idx_71 : m7Fns[71]?.map Fn.sig =
    some ("m6_hdr_set_watermark", [i64, i64, i64], []) := mp_p1 (by decide) (by t_kernel_rfl)
private theorem mp_idx_80 : m7Fns[80]?.map Fn.sig =
    some ("full_unwatch_large", [i64, i32, i32], []) := mp_p1 (by decide) (by t_kernel_rfl)
private theorem mp_idx_81 : m7Fns[81]?.map Fn.sig =
    some ("full_prop_lit_ovf_hot", [i64, i32, i32, i32], [.bool]) :=
  mp_p1 (by decide) (by t_kernel_rfl)
private theorem mp_idx_82 : m7Fns[82]?.map Fn.sig =
    some ("full_prop_chrono_hot", [i64, i64], [.bool]) := mp_p1 (by decide) (by t_kernel_rfl)
private theorem mp_idx_83 : m7Fns[83]?.map Fn.sig =
    some ("full_propagate_ignore_hot", [i64, i64], [i64]) := mp_p1 (by decide) (by t_kernel_rfl)
private theorem mp_idx_85 : m7Fns[85]?.map Fn.sig =
    some ("full_propagate_ignore", [i64, i64], [i64]) := mp_p1 (by decide) (by t_kernel_rfl)
private theorem mp_idx_86 : m7Fns[86]?.map Fn.sig =
    some ("full_propagate", [i64], [i64]) := mp_p1 (by decide) (by t_kernel_rfl)
private theorem mp_idx_97 : m7Fns[97]?.map Fn.sig =
    some ("full_sweep_copy", [i64, i64, i64, i32, .bool], [i64]) :=
  mp_p1 (by decide) (by t_kernel_rfl)
private theorem mp_idx_112 : m7Fns[112]?.map Fn.sig =
    some ("full_analyze_lit", [i64, i32, i32], [.bool]) :=
  mp_p2 (k := 0) (by decide) (by t_kernel_rfl)
private theorem mp_idx_113 : m7Fns[113]?.map Fn.sig =
    some ("full_analyze_rsn", [i64, i32, i32], [.bool]) :=
  mp_p2 (k := 1) (by decide) (by t_kernel_rfl)
private theorem mp_idx_178 : m7Fns[178]?.map Fn.sig =
    some ("full_add_bin", [i64, i32, i32], [i64]) := mp_p2 (k := 66) (by decide) (by t_kernel_rfl)
private theorem mp_idx_179 : m7Fns[179]?.map Fn.sig =
    some ("full_delete_binary", [i64, i32, i32], []) :=
  mp_p2 (k := 67) (by decide) (by t_kernel_rfl)
private theorem mp_idx_190 : m7Fns[190]?.map Fn.sig =
    some ("full_probe_run", [i64, i64], [i64]) := mp_p2 (k := 78) (by decide) (by t_kernel_rfl)
private theorem mp_idx_209 : m7Fns[209]?.map Fn.sig =
    some ("full_viv_clause_m6", [i64, i32], [i64]) := mp_p2 (k := 97) (by decide) (by t_kernel_rfl)
private theorem mp_idx_211 : m7Fns[211]?.map Fn.sig =
    some ("full_viv_collect_m6", [i64, i64], [i64]) := mp_p2 (k := 99) (by decide) (by t_kernel_rfl)
private theorem mp_idx_212 : m7Fns[212]?.map Fn.sig =
    some ("full_viv_count_m6", [i64, i64], []) := mp_p2 (k := 100) (by decide) (by t_kernel_rfl)
private theorem mp_idx_213 : m7Fns[213]?.map Fn.sig =
    some ("full_viv_keys_m6", [i64, i64], []) := mp_p2 (k := 101) (by decide) (by t_kernel_rfl)
private theorem mp_idx_214 : m7Fns[214]?.map Fn.sig =
    some ("full_viv_sort_sched_m6", [i64, i64], []) :=
  mp_p2 (k := 102) (by decide) (by t_kernel_rfl)
private theorem mp_idx_215 : m7Fns[215]?.map Fn.sig =
    some ("full_viv_clear_tier_m6", [i64, i64], []) :=
  mp_p2 (k := 103) (by decide) (by t_kernel_rfl)
private theorem mp_idx_217 : m7Fns[217]?.map Fn.sig =
    some ("full_vivify_tier_m6_hdr", [i64, i64, i64, i64], [i64]) :=
  mp_p2 (k := 105) (by decide) (by t_kernel_rfl)
private theorem mp_idx_218 : m7Fns[218]?.map Fn.sig =
    some ("full_vivify_m6_hdr", [i64], [i64]) := mp_p2 (k := 106) (by decide) (by t_kernel_rfl)
private theorem mp_idx_226 : m7Fns[226]?.map Fn.sig =
    some ("full_backbone_m6", [i64, i64], [i64]) := mp_p2 (k := 114) (by decide) (by t_kernel_rfl)
private theorem mp_idx_229 : m7Fns[229]?.map Fn.sig =
    some ("full_transitive_m6", [i64, i64], [i64]) := mp_p2 (k := 117) (by decide) (by t_kernel_rfl)
private theorem mp_idx_235 : m7Fns[235]?.map Fn.sig =
    some ("full_substitute", [i64], [i64]) := mp_p2 (k := 123) (by decide) (by t_kernel_rfl)
private theorem mp_idx_236 : m7Fns[236]?.map Fn.sig =
    some ("full_enter_dense", [i64], [.bool]) := mp_p2 (k := 124) (by decide) (by t_kernel_rfl)
private theorem mp_idx_237 : m7Fns[237]?.map Fn.sig =
    some ("full_rebuild_watches", [i64], [i64]) := mp_p2 (k := 125) (by decide) (by t_kernel_rfl)
private theorem mp_idx_275 : m7Fns[275]?.map Fn.sig =
    some ("full_congruence_dense", [i64, i64], [i64]) :=
  mp_p2 (k := 163) (by decide) (by t_kernel_rfl)
private theorem mp_idx_299 : m7Fns[299]?.map Fn.sig =
    some ("full_sweep_dense_m6", [i64, i64, i64], [i64]) := mp_p3 (k := 23) (by t_kernel_rfl)
private theorem mp_idx_300 : m7Fns[300]?.map Fn.sig =
    some ("full_fwd_dedup_bins", [i64], [.bool]) := mp_p3 (k := 24) (by t_kernel_rfl)
private theorem mp_idx_302 : m7Fns[302]?.map Fn.sig =
    some ("full_dense_flush_units_m7", [i64], [.bool]) := mp_p3 (k := 26) (by t_kernel_rfl)
private theorem mp_idx_303 : m7Fns[303]?.map Fn.sig =
    some ("full_fwd_flush_large_m7", [i64], []) := mp_p3 (k := 27) (by t_kernel_rfl)
private theorem mp_idx_304 : m7Fns[304]?.map Fn.sig =
    some ("full_fwd_reconnect_irred_m7", [i64], []) := mp_p3 (k := 28) (by t_kernel_rfl)
private theorem mp_idx_306 : m7Fns[306]?.map Fn.sig =
    some ("full_fwd_check_cl_m7", [i64, i32], [.bool]) := mp_p3 (k := 30) (by t_kernel_rfl)
private theorem mp_idx_307 : m7Fns[307]?.map Fn.sig =
    some ("full_fwd_connect_subsumer_m7", [i64, i32], []) := mp_p3 (k := 31) (by t_kernel_rfl)
private theorem mp_idx_308 : m7Fns[308]?.map Fn.sig =
    some ("full_fwd_collect_sort_m7", [i64], [i64]) := mp_p3 (k := 32) (by t_kernel_rfl)
private theorem mp_idx_311 : m7Fns[311]?.map Fn.sig =
    some ("full_forward_sub", [i64, i64], [i64]) := mp_p3 (k := 35) (by t_kernel_rfl)
private theorem mp_idx_340 : m7Fns[340]?.map Fn.sig =
    some ("full_init_fresh_var", [i64, i32], []) := mp_p3 (k := 64) (by t_kernel_rfl)
private theorem mp_idx_346 : m7Fns[346]?.map Fn.sig =
    some ("full_bva_pick_cand", [i64, i32, i32], [i32]) := mp_p3 (k := 70) (by t_kernel_rfl)
private theorem mp_idx_348 : m7Fns[348]?.map Fn.sig =
    some ("full_bva_commit", [i64, i32], [.bool]) := mp_p3 (k := 72) (by t_kernel_rfl)
private theorem mp_idx_352 : m7Fns[352]?.map Fn.sig =
    some ("full_factor", [i64, i64], [i64]) := mp_p3 (k := 76) (by t_kernel_rfl)
private theorem mp_idx_353 : m7Fns[353]?.map Fn.sig =
    some ("full_compact_needed", [i64], [.bool]) := mp_p3 (k := 77) (by t_kernel_rfl)
private theorem mp_idx_355 : m7Fns[355]?.map Fn.sig =
    some ("full_compact_mark_live", [i64], []) := mp_p3 (k := 79) (by t_kernel_rfl)
private theorem mp_idx_360 : m7Fns[360]?.map Fn.sig =
    some ("full_compact_vars", [i64, i64, i64], []) := mp_p3 (k := 84) (by t_kernel_rfl)
private theorem mp_idx_374 : m7Fns[374]?.map Fn.sig =
    some ("full_min_u64", [i64, i64], [i64]) := mp_p3 (k := 98) (by t_kernel_rfl)
private theorem mp_idx_376 : m7Fns[376]?.map Fn.sig =
    some ("full_elim_dticks", [i64, .bool], [i64]) := mp_p3 (k := 100) (by t_kernel_rfl)
private theorem mp_idx_383 : m7Fns[383]?.map Fn.sig =
    some ("full_elim_bve_m7", [i64, i64], [i64]) := mp_p3 (k := 107) (by t_kernel_rfl)
private theorem mp_idx_385 : m7Fns[385]?.map Fn.sig =
    some ("full_eliminate_m6", [i64, .bool], [i64]) := mp_p3 (k := 109) (by t_kernel_rfl)
private theorem mp_idx_400 : m7Fns[400]?.map Fn.sig =
    some ("full_probe_dticks_m6_hdr", [i64, .bool], [i64]) := mp_p3 (k := 124) (by t_kernel_rfl)
private theorem mp_idx_401 : m7Fns[401]?.map Fn.sig =
    some ("full_probe_tail_m6", [i64, i64], [i64]) := mp_p3 (k := 125) (by t_kernel_rfl)
private theorem mp_idx_402 : m7Fns[402]?.map Fn.sig =
    some ("full_probe_m6", [i64, .bool], [i64]) := mp_p3 (k := 126) (by t_kernel_rfl)

/-- Fast `O(17)` preservation of `Module.checkAcyclic = true` across all `410` functions of
`m7PlusModule`. -/
theorem m7Plus_acyclic : m7PlusModule.checkAcyclic = true := by
  obtain ⟨f46, hf46, hs46⟩ := sig_of_map_idx mp_idx_46
  obtain ⟨f59, hf59, hs59⟩ := sig_of_map_idx mp_idx_59
  obtain ⟨f83, hf83, hs83⟩ := sig_of_map_idx mp_idx_83
  obtain ⟨f85, hf85, hs85⟩ := sig_of_map_idx mp_idx_85
  obtain ⟨f97, hf97, hs97⟩ := sig_of_map_idx mp_idx_97
  obtain ⟨f113, hf113, hs113⟩ := sig_of_map_idx mp_idx_113
  obtain ⟨f217, hf217, hs217⟩ := sig_of_map_idx mp_idx_217
  obtain ⟨f218, hf218, hs218⟩ := sig_of_map_idx mp_idx_218
  obtain ⟨f311, hf311, hs311⟩ := sig_of_map_idx mp_idx_311
  obtain ⟨f346, hf346, hs346⟩ := sig_of_map_idx mp_idx_346
  obtain ⟨f348, hf348, hs348⟩ := sig_of_map_idx mp_idx_348
  obtain ⟨f353, hf353, hs353⟩ := sig_of_map_idx mp_idx_353
  obtain ⟨f355, hf355, hs355⟩ := sig_of_map_idx mp_idx_355
  obtain ⟨f360, hf360, hs360⟩ := sig_of_map_idx mp_idx_360
  obtain ⟨f385, hf385, hs385⟩ := sig_of_map_idx mp_idx_385
  obtain ⟨f401, hf401, hs401⟩ := sig_of_map_idx mp_idx_401
  obtain ⟨f402, hf402, hs402⟩ := sig_of_map_idx mp_idx_402
  obtain ⟨g9, hg9, hsg9⟩ := sig_of_map_idx mp_idx_9
  obtain ⟨g11, hg11, hsg11⟩ := sig_of_map_idx mp_idx_11
  obtain ⟨g12, hg12, hsg12⟩ := sig_of_map_idx mp_idx_12
  obtain ⟨g17, hg17, hsg17⟩ := sig_of_map_idx mp_idx_17
  obtain ⟨g18, hg18, hsg18⟩ := sig_of_map_idx mp_idx_18
  obtain ⟨g32, hg32, hsg32⟩ := sig_of_map_idx mp_idx_32
  obtain ⟨g34, hg34, hsg34⟩ := sig_of_map_idx mp_idx_34
  obtain ⟨g35, hg35, hsg35⟩ := sig_of_map_idx mp_idx_35
  obtain ⟨g39, hg39, hsg39⟩ := sig_of_map_idx mp_idx_39
  obtain ⟨g43, hg43, hsg43⟩ := sig_of_map_idx mp_idx_43
  obtain ⟨g56, hg56, hsg56⟩ := sig_of_map_idx mp_idx_56
  obtain ⟨g66, hg66, hsg66⟩ := sig_of_map_idx mp_idx_66
  obtain ⟨g67, hg67, hsg67⟩ := sig_of_map_idx mp_idx_67
  obtain ⟨g68, hg68, hsg68⟩ := sig_of_map_idx mp_idx_68
  obtain ⟨g70, hg70, hsg70⟩ := sig_of_map_idx mp_idx_70
  obtain ⟨g71, hg71, hsg71⟩ := sig_of_map_idx mp_idx_71
  obtain ⟨g80, hg80, hsg80⟩ := sig_of_map_idx mp_idx_80
  obtain ⟨g81, hg81, hsg81⟩ := sig_of_map_idx mp_idx_81
  obtain ⟨g82, hg82, hsg82⟩ := sig_of_map_idx mp_idx_82
  obtain ⟨g86, hg86, hsg86⟩ := sig_of_map_idx mp_idx_86
  obtain ⟨g112, hg112, hsg112⟩ := sig_of_map_idx mp_idx_112
  obtain ⟨g178, hg178, hsg178⟩ := sig_of_map_idx mp_idx_178
  obtain ⟨g179, hg179, hsg179⟩ := sig_of_map_idx mp_idx_179
  obtain ⟨g190, hg190, hsg190⟩ := sig_of_map_idx mp_idx_190
  obtain ⟨g209, hg209, hsg209⟩ := sig_of_map_idx mp_idx_209
  obtain ⟨g211, hg211, hsg211⟩ := sig_of_map_idx mp_idx_211
  obtain ⟨g212, hg212, hsg212⟩ := sig_of_map_idx mp_idx_212
  obtain ⟨g213, hg213, hsg213⟩ := sig_of_map_idx mp_idx_213
  obtain ⟨g214, hg214, hsg214⟩ := sig_of_map_idx mp_idx_214
  obtain ⟨g215, hg215, hsg215⟩ := sig_of_map_idx mp_idx_215
  obtain ⟨g226, hg226, hsg226⟩ := sig_of_map_idx mp_idx_226
  obtain ⟨g229, hg229, hsg229⟩ := sig_of_map_idx mp_idx_229
  obtain ⟨g235, hg235, hsg235⟩ := sig_of_map_idx mp_idx_235
  obtain ⟨g236, hg236, hsg236⟩ := sig_of_map_idx mp_idx_236
  obtain ⟨g237, hg237, hsg237⟩ := sig_of_map_idx mp_idx_237
  obtain ⟨g275, hg275, hsg275⟩ := sig_of_map_idx mp_idx_275
  obtain ⟨g299, hg299, hsg299⟩ := sig_of_map_idx mp_idx_299
  obtain ⟨g300, hg300, hsg300⟩ := sig_of_map_idx mp_idx_300
  obtain ⟨g302, hg302, hsg302⟩ := sig_of_map_idx mp_idx_302
  obtain ⟨g303, hg303, hsg303⟩ := sig_of_map_idx mp_idx_303
  obtain ⟨g304, hg304, hsg304⟩ := sig_of_map_idx mp_idx_304
  obtain ⟨g306, hg306, hsg306⟩ := sig_of_map_idx mp_idx_306
  obtain ⟨g307, hg307, hsg307⟩ := sig_of_map_idx mp_idx_307
  obtain ⟨g308, hg308, hsg308⟩ := sig_of_map_idx mp_idx_308
  obtain ⟨g340, hg340, hsg340⟩ := sig_of_map_idx mp_idx_340
  obtain ⟨g352, hg352, hsg352⟩ := sig_of_map_idx mp_idx_352
  obtain ⟨g374, hg374, hsg374⟩ := sig_of_map_idx mp_idx_374
  obtain ⟨g376, hg376, hsg376⟩ := sig_of_map_idx mp_idx_376
  obtain ⟨g383, hg383, hsg383⟩ := sig_of_map_idx mp_idx_383
  obtain ⟨g400, hg400, hsg400⟩ := sig_of_map_idx mp_idx_400
  change ({ m7Module with fns := mpSpliceFns m7PlusRepls m7Module.fns } :
    LeanQbe.T.Module).checkAcyclic = true
  refine mpSpliceModule_checkAcyclic (M := m7Module) m7_acyclic ?_ ?_
  · intro r hr f hf hnm
    simp only [m7PlusRepls, m7ParityVivTiersPatchFns, m7PlusTailRepls, m7ParityBvaTiePatchFns,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with
      (rfl | rfl | rfl | rfl | rfl) |
      (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl)
    · exact (fn_eq_of_mem_idx m7_names_nodup hf hf59
        (hnm.symm.trans (congrArg Prod.fst hs59.symm))) ▸ hs59.symm
    · exact (fn_eq_of_mem_idx m7_names_nodup hf hf83
        (hnm.symm.trans (congrArg Prod.fst hs83.symm))) ▸ hs83.symm
    · exact (fn_eq_of_mem_idx m7_names_nodup hf hf85
        (hnm.symm.trans (congrArg Prod.fst hs85.symm))) ▸ hs85.symm
    · exact (fn_eq_of_mem_idx m7_names_nodup hf hf217
        (hnm.symm.trans (congrArg Prod.fst hs217.symm))) ▸ hs217.symm
    · exact (fn_eq_of_mem_idx m7_names_nodup hf hf218
        (hnm.symm.trans (congrArg Prod.fst hs218.symm))) ▸ hs218.symm
    · exact (fn_eq_of_mem_idx m7_names_nodup hf hf348
        (hnm.symm.trans (congrArg Prod.fst hs348.symm))) ▸ hs348.symm
    · exact (fn_eq_of_mem_idx m7_names_nodup hf hf113
        (hnm.symm.trans (congrArg Prod.fst hs113.symm))) ▸ hs113.symm
    · exact (fn_eq_of_mem_idx m7_names_nodup hf hf353
        (hnm.symm.trans (congrArg Prod.fst hs353.symm))) ▸ hs353.symm
    · exact (fn_eq_of_mem_idx m7_names_nodup hf hf355
        (hnm.symm.trans (congrArg Prod.fst hs355.symm))) ▸ hs355.symm
    · exact (fn_eq_of_mem_idx m7_names_nodup hf hf360
        (hnm.symm.trans (congrArg Prod.fst hs360.symm))) ▸ hs360.symm
    · exact (fn_eq_of_mem_idx m7_names_nodup hf hf97
        (hnm.symm.trans (congrArg Prod.fst hs97.symm))) ▸ hs97.symm
    · exact (fn_eq_of_mem_idx m7_names_nodup hf hf46
        (hnm.symm.trans (congrArg Prod.fst hs46.symm))) ▸ hs46.symm
    · exact (fn_eq_of_mem_idx m7_names_nodup hf hf311
        (hnm.symm.trans (congrArg Prod.fst hs311.symm))) ▸ hs311.symm
    · exact (fn_eq_of_mem_idx m7_names_nodup hf hf385
        (hnm.symm.trans (congrArg Prod.fst hs385.symm))) ▸ hs385.symm
    · exact (fn_eq_of_mem_idx m7_names_nodup hf hf346
        (hnm.symm.trans (congrArg Prod.fst hs346.symm))) ▸ hs346.symm
    · exact (fn_eq_of_mem_idx m7_names_nodup hf hf401
        (hnm.symm.trans (congrArg Prod.fst hs401.symm))) ▸ hs401.symm
    · exact (fn_eq_of_mem_idx m7_names_nodup hf hf402
        (hnm.symm.trans (congrArg Prod.fst hs402.symm))) ▸ hs402.symm
  · intro pre f post r hsplit hr hnm
    simp only [m7Module, List.map_nil, List.append_nil] at hsplit ⊢
    simp only [m7PlusRepls, m7ParityVivTiersPatchFns, m7PlusTailRepls, m7ParityBvaTiePatchFns,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with
      (rfl | rfl | rfl | rfl | rfl) |
      (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl)
    · have hn0 : f.name = f59.name := hnm.symm.trans (congrArg Prod.fst hs59.symm)
      have hc : m7pSyncLegacyTiersFn.checkCallsOk
          [("m6_ext_ensure_init", [i64], [])] [] = true := by rfl
      refine fn_checkCallsOk_mono (fun s hs => ?_) hc
      rcases List.mem_singleton.mp hs with rfl
      exact hsg56 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf59 hn0 hg56 (by decide)
    · have hn0 : f.name = f83.name := hnm.symm.trans (congrArg Prod.fst hs83.symm)
      have hc : m7pPropIgnoreHotFn.checkCallsOk
          [ ("full_prop_lit_ovf_hot", [i64, i32, i32, i32], [.bool])
          , ("full_prop_chrono_hot", [i64, i64], [.bool]) ] [] = true := by rfl
      refine fn_checkCallsOk_mono (fun s hs => ?_) hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl
      · exact hsg81 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf83 hn0 hg81 (by decide)
      · exact hsg82 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf83 hn0 hg82 (by decide)
    · have hn0 : f.name = f85.name := hnm.symm.trans (congrArg Prod.fst hs85.symm)
      have hc : m7pPropIgnoreFn.checkCallsOk
          [ ("full_prop_lit_ovf_hot", [i64, i32, i32, i32], [.bool])
          , ("full_prop_chrono_hot", [i64, i64], [.bool]) ] [] = true := by rfl
      refine fn_checkCallsOk_mono (fun s hs => ?_) hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl
      · exact hsg81 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf85 hn0 hg81 (by decide)
      · exact hsg82 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf85 hn0 hg82 (by decide)
    · have hn0 : f.name = f217.name := hnm.symm.trans (congrArg Prod.fst hs217.symm)
      have hc : m7pVivifyTierFn.checkCallsOk
          [ ("full_backtrack", [i64, i64], [])
          , ("full_viv_collect_m6", [i64, i64], [i64])
          , ("full_viv_count_m6", [i64, i64], [])
          , ("full_viv_keys_m6", [i64, i64], [])
          , ("full_viv_sort_sched_m6", [i64, i64], [])
          , ("full_viv_clause_m6", [i64, i32], [i64])
          , ("full_propagate", [i64], [i64])
          , ("full_viv_clear_tier_m6", [i64, i64], []) ] [] = true := by rfl
      refine fn_checkCallsOk_mono (fun s hs => ?_) hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hsg39 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf217 hn0 hg39 (by decide)
      · exact hsg211 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf217 hn0 hg211 (by decide)
      · exact hsg212 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf217 hn0 hg212 (by decide)
      · exact hsg213 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf217 hn0 hg213 (by decide)
      · exact hsg214 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf217 hn0 hg214 (by decide)
      · exact hsg209 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf217 hn0 hg209 (by decide)
      · exact hsg86 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf217 hn0 hg86 (by decide)
      · exact hsg215 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf217 hn0 hg215 (by decide)
    · have hn0 : f.name = f218.name := hnm.symm.trans (congrArg Prod.fst hs218.symm)
      have hc : m7pVivifyFn.checkCallsOk
          [ ("full_backtrack", [i64, i64], [])
          , ("m6_hdr_sync_legacy_tiers", [i64], [])
          , ("m6_hdr_get_watermark", [i64, i64], [i64])
          , ("full_vivify_tier_m6_hdr", [i64, i64, i64, i64], [i64]) ] [] = true := by rfl
      refine fn_checkCallsOk_mono (fun s hs => ?_) hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl
      · exact hsg39 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf218 hn0 hg39 (by decide)
      · exact hs59 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf218 hn0 hf59 (by decide)
      · exact hsg70 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf218 hn0 hg70 (by decide)
      · exact hs217 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf218 hn0 hf217 (by decide)
    · have hn0 : f.name = f348.name := hnm.symm.trans (congrArg Prod.fst hs348.symm)
      have hc : m7BvaCommitFn.checkCallsOk
          [ ("full_alloc_cl", [i64, i32, i32, .bool], [i64])
          , ("full_wstack_defrag", [i64], [])
          , ("full_watch_push", [i64, i32, i32, i32, i32], [.bool])
          , ("full_unwatch_large", [i64, i32, i32], [])
          , ("full_add_bin", [i64, i32, i32], [i64])
          , ("full_delete_binary", [i64, i32, i32], [])
          , ("full_init_fresh_var", [i64, i32], []) ] [] = true := by rfl
      refine fn_checkCallsOk_mono (fun s hs => ?_) hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hsg12 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf348 hn0 hg12 (by decide)
      · exact hsg17 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf348 hn0 hg17 (by decide)
      · exact hsg18 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf348 hn0 hg18 (by decide)
      · exact hsg80 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf348 hn0 hg80 (by decide)
      · exact hsg178 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf348 hn0 hg178 (by decide)
      · exact hsg179 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf348 hn0 hg179 (by decide)
      · exact hsg340 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf348 hn0 hg340 (by decide)
    · have hn0 : f.name = f113.name := hnm.symm.trans (congrArg Prod.fst hs113.symm)
      have hc : m7AnalyzeRsnFn.checkCallsOk
          [("full_analyze_lit", [i64, i32, i32], [.bool])] [] = true := by rfl
      refine fn_checkCallsOk_mono (fun s hs => ?_) hc
      rcases List.mem_singleton.mp hs with rfl
      exact hsg112 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf113 hn0 hg112 (by decide)
    · exact (by rfl : m7fixCompactNeededFn.checkCallsOk [] [] = true)
    · have hn0 : f.name = f355.name := hnm.symm.trans (congrArg Prod.fst hs355.symm)
      have hc : m7fixCompactMarkLiveFn.checkCallsOk
          [("full_arena_next", [i64, i32], [i32])] [] = true := by rfl
      refine fn_checkCallsOk_mono (fun s hs => ?_) hc
      rcases List.mem_singleton.mp hs with rfl
      exact hsg11 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf355 hn0 hg11 (by decide)
    · exact (by rfl : m7fixCompactVarsFn.checkCallsOk [] [] = true)
    · have hn0 : f.name = f97.name := hnm.symm.trans (congrArg Prod.fst hs97.symm)
      have hc : m7fixSweepCopyFn.checkCallsOk
          [ ("full_assign_lvl", [i64, i32, i32, i32], [])
          , ("full_watch_push", [i64, i32, i32, i32, i32], [.bool]) ] [] = true := by rfl
      refine fn_checkCallsOk_mono (fun s hs => ?_) hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl
      · exact hsg35 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf97 hn0 hg35 (by decide)
      · exact hsg18 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf97 hn0 hg18 (by decide)
    · have hn0 : f.name = f46.name := hnm.symm.trans (congrArg Prod.fst hs46.symm)
      have hc : m7v5CalcMaxVFn.checkCallsOk
          [("full_fixed_bytes", [i64], [i64])] [] = true := by rfl
      refine fn_checkCallsOk_mono (fun s hs => ?_) hc
      rcases List.mem_singleton.mp hs with rfl
      exact hsg43 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf46 hn0 hg43 (by decide)
    · have hn0 : f.name = f311.name := hnm.symm.trans (congrArg Prod.fst hs311.symm)
      have hc : m7v5ForwardSubFn.checkCallsOk
          [ ("full_fwd_dedup_bins", [i64], [.bool])
          , ("full_dense_flush_units_m7", [i64], [.bool])
          , ("full_fwd_collect_sort_m7", [i64], [i64])
          , ("full_fwd_flush_large_m7", [i64], [])
          , ("full_fwd_check_cl_m7", [i64, i32], [.bool])
          , ("full_fwd_connect_subsumer_m7", [i64, i32], [])
          , ("full_arena_next", [i64, i32], [i32])
          , ("full_fwd_reconnect_irred_m7", [i64], []) ] [] = true := by rfl
      refine fn_checkCallsOk_mono (fun s hs => ?_) hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hsg300 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf311 hn0 hg300 (by decide)
      · exact hsg302 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf311 hn0 hg302 (by decide)
      · exact hsg308 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf311 hn0 hg308 (by decide)
      · exact hsg303 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf311 hn0 hg303 (by decide)
      · exact hsg306 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf311 hn0 hg306 (by decide)
      · exact hsg307 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf311 hn0 hg307 (by decide)
      · exact hsg11 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf311 hn0 hg11 (by decide)
      · exact hsg304 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf311 hn0 hg304 (by decide)
    · have hn0 : f.name = f385.name := hnm.symm.trans (congrArg Prod.fst hs385.symm)
      have hc : m7PlusEliminateFn.checkCallsOk
          [ ("full_elim_dticks", [i64, .bool], [i64])
          , ("full_ilog10", [i64], [i64])
          , ("full_scale_delta", [i64, i64], [i64])
          , ("full_enter_dense", [i64], [.bool])
          , ("full_min_u64", [i64, i64], [i64])
          , ("full_forward_sub", [i64, i64], [i64])
          , ("full_elim_bve_m7", [i64, i64], [i64])
          , ("full_factor", [i64, i64], [i64])
          , ("full_rebuild_watches", [i64], [i64]) ] [] = true := by rfl
      refine fn_checkCallsOk_mono (fun s hs => ?_) hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hsg376 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf385 hn0 hg376 (by decide)
      · exact hsg9 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf385 hn0 hg9 (by decide)
      · exact hsg34 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf385 hn0 hg34 (by decide)
      · exact hsg236 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf385 hn0 hg236 (by decide)
      · exact hsg374 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf385 hn0 hg374 (by decide)
      · exact hs311 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf385 hn0 hf311 (by decide)
      · exact hsg383 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf385 hn0 hg383 (by decide)
      · exact hsg352 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf385 hn0 hg352 (by decide)
      · exact hsg237 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf385 hn0 hg237 (by decide)
    · exact (by rfl : m7btBvaPickCandFn.checkCallsOk [] [] = true)
    · have hn0 : f.name = f401.name := hnm.symm.trans (congrArg Prod.fst hs401.symm)
      have hc : m7btProbeTailFn.checkCallsOk
          [ ("full_backbone_m6", [i64, i64], [i64])
          , ("full_transitive_m6", [i64, i64], [i64])
          , ("full_min_u64", [i64, i64], [i64])
          , ("full_probe_run", [i64, i64], [i64])
          , ("full_vivify_m6_hdr", [i64], [i64]) ] [] = true := by rfl
      refine fn_checkCallsOk_mono (fun s hs => ?_) hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl
      · exact hsg226 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf401 hn0 hg226 (by decide)
      · exact hsg229 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf401 hn0 hg229 (by decide)
      · exact hsg374 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf401 hn0 hg374 (by decide)
      · exact hsg190 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf401 hn0 hg190 (by decide)
      · exact hs218 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf401 hn0 hf218 (by decide)
    · have hn0 : f.name = f402.name := hnm.symm.trans (congrArg Prod.fst hs402.symm)
      have hc : m7btProbeFn.checkCallsOk
          [ ("full_probe_dticks_m6_hdr", [i64, .bool], [i64])
          , ("full_ilog10", [i64], [i64])
          , ("full_scale_delta_m5", [i64, i64], [i64])
          , ("full_enter_dense", [i64], [.bool])
          , ("m6_hdr_delaying", [i64, i64], [.bool])
          , ("full_congruence_dense", [i64, i64], [i64])
          , ("full_rebuild_watches", [i64], [i64])
          , ("m6_hdr_set_watermark", [i64, i64, i64], [])
          , ("m6_hdr_reduce_delay", [i64, i64], [])
          , ("m6_hdr_bump_delay", [i64, i64], [])
          , ("full_sweep_dense_m6", [i64, i64, i64], [i64])
          , ("full_substitute", [i64], [i64])
          , ("full_probe_tail_m6", [i64, i64], [i64])
          , ("full_backbone_m6", [i64, i64], [i64])
          , ("full_min_u64", [i64, i64], [i64])
          , ("full_factor", [i64, i64], [i64]) ] [] = true := by rfl
      refine fn_checkCallsOk_mono (fun s hs => ?_) hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl
      · exact hsg400 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf402 hn0 hg400 (by decide)
      · exact hsg9 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf402 hn0 hg9 (by decide)
      · exact hsg32 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf402 hn0 hg32 (by decide)
      · exact hsg236 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf402 hn0 hg236 (by decide)
      · exact hsg66 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf402 hn0 hg66 (by decide)
      · exact hsg275 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf402 hn0 hg275 (by decide)
      · exact hsg237 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf402 hn0 hg237 (by decide)
      · exact hsg71 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf402 hn0 hg71 (by decide)
      · exact hsg68 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf402 hn0 hg68 (by decide)
      · exact hsg67 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf402 hn0 hg67 (by decide)
      · exact hsg299 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf402 hn0 hg299 (by decide)
      · exact hsg235 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf402 hn0 hg235 (by decide)
      · exact hs401 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf402 hn0 hf401 (by decide)
      · exact hsg226 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf402 hn0 hg226 (by decide)
      · exact hsg374 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf402 hn0 hg374 (by decide)
      · exact hsg352 ▸ sig_mem_pre_of_lt_idx m7_names_nodup hsplit hf402 hn0 hg352 (by decide)

/-! ## 4. Compile-Time `#guard` Verification (`PrintCpp`, `PrintQbe`, 4-ISA Legal) -/

section Guards

open LeanQbe.T.PrintCpp

#guard m7PlusRepls.length == 17
#guard (m7PlusRepls.map Fn.name).eraseDups.length == 17
#guard m7PlusRepls.all fun r => m7Fns.any fun f => f.sig == r.sig
#guard m7PlusFns.length == 410
#guard (m7PlusFns.map Fn.name).eraseDups.length == 410
#guard m7PlusFns.map Fn.sig == m7Fns.map Fn.sig
#guard m7PlusModule.checkAcyclic
#guard m7PlusModule.exits.isEmpty && m7PlusModule.externs.isEmpty
#guard (ppTModule m7PlusModule).isOk
#guard (PrintQbe.module m7PlusModule).isOk
#guard (ppModule (m7PlusFns.map (Fn.legal .aarch64))).isOk
#guard (ppModule (m7PlusFns.map (Fn.legal .scalar64))).isOk
#guard (ppModule (m7PlusFns.map (Fn.legal .x64AVX512))).isOk
#guard (ppModule (m7PlusFns.map (Fn.legal .x64AVX2))).isOk
#guard m7PlusFns.all fun fn => (Fn.legal .aarch64 fn).body.isLegal .aarch64
#guard m7PlusFns.all fun fn => (Fn.legal .scalar64 fn).body.isLegal .scalar64
#guard m7PlusFns.all fun fn => (Fn.legal .x64AVX512 fn).body.isLegal .x64AVX512
#guard m7PlusFns.all fun fn => (Fn.legal .x64AVX2 fn).body.isLegal .x64AVX2

end Guards

end LeanQbe.T.Examples.Kissat.FullM7Plus
