module

public import LeanQbe.T.Examples.Kissat.FullM7BveGates
public import LeanQbe.T.Examples.Kissat.FullM6BveFwdProof
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullBvaFwdSpec
import LeanQbe.T.Examples.Kissat.FullDenseWatchLemmas1
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Wave-4E (`FullM7BveGates`) Proofs — Part 1 (Callee-Rename Transport)

M1-clean proof module (`public section`, `0` `@[expose]`, `0` `import all`, `private` helpers):
1. `ExprRename` / `wp_iff_of_exprRename`: zero-axiom syntactic callee-renaming transport for
   `Func.wp`, proving the `17` logic-identical `_m7` functions directly from `FullM6BveFwdProof`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM7BveGates

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullBvaFwdHelpers
open LeanQbe.T.Examples.Kissat.Full.FullDenseWatchHelpers
open LeanQbe.T.Examples.Kissat.FullFastBveBudgets
open LeanQbe.T.Examples.Kissat.FullFastSched
open LeanQbe.T.Examples.Kissat.FullM3CongBva
open LeanQbe.T.Examples.Kissat.FullM6BveFwd
open Kraken.Bedrock2.Test

open scoped FullArenaTactics

/-! ## 1. Callee-Renaming Transport (`_m6` -> `_m7`) -/

def m6ToM7Sym : Sym → Sym
  | "full_dense_prop_unit_m6" => "full_dense_prop_unit_m7"
  | "full_dense_flush_units_m6" => "full_dense_flush_units_m7"
  | "full_fwd_flush_large_m6" => "full_fwd_flush_large_m7"
  | "full_fwd_reconnect_irred_m6" => "full_fwd_reconnect_irred_m7"
  | "full_fwd_scan_lit_m6" => "full_fwd_scan_lit_m7"
  | "full_fwd_check_cl_m6" => "full_fwd_check_cl_m7"
  | "full_fwd_connect_subsumer_m6" => "full_fwd_connect_subsumer_m7"
  | "full_fwd_collect_sort_m6" => "full_fwd_collect_sort_m7"
  | "full_forward_sub_m6" => "full_forward_sub_m7"
  | "full_bve_collect_m6" => "full_bve_collect_m7"
  | "full_bve_mark_and_m6" => "full_bve_mark_and_m7"
  | "full_bve_get_tern_m6" => "full_bve_get_tern_m7"
  | "full_bve_match_tern_m6" => "full_bve_match_tern_m7"
  | "full_bve_find_ite_m6" => "full_bve_find_ite_m7"
  | "full_bve_gates_m6" => "full_bve_gates_m7"
  | "full_bve_var_m6" => "full_bve_var_m7"
  | "full_bve_var_key_m6" => "full_bve_var_key_m7"
  | "full_bve_heap_up_m6" => "full_bve_heap_up_m7"
  | "full_bve_heap_down_m6" => "full_bve_heap_down_m7"
  | "full_bve_heap_push_m6" => "full_bve_heap_push_m7"
  | "full_bve_heap_pop_m6" => "full_bve_heap_pop_m7"
  | "full_bve_collect_nbrs_m6" => "full_bve_collect_nbrs_m7"
  | "full_elim_bve_m6" => "full_elim_bve_m7"
  | "full_eliminate_m6" => "full_eliminate_m7"
  | x => x

mutual
inductive ExprRename (σ : Sym → Sym) :
    {rs : List Ty} → Expr Val Cont rs → Expr Val Cont rs → Prop
  | let_ {rs ts : List Ty} {op : Op Val ts} {k₁ k₂ : Tup Val ts → Expr Val Cont rs} :
      (∀ r, ExprRename σ (k₁ r) (k₂ r)) → ExprRename σ (.let_ op k₁) (.let_ op k₂)
  | load {rs : List Ty} {t : Ty} {a : Arg Val i64} {k₁ k₂ : Val t → Expr Val Cont rs} :
      (∀ v, ExprRename σ (k₁ v) (k₂ v)) → ExprRename σ (.load t a k₁) (.load t a k₂)
  | store {rs : List Ty} {t : Ty} {v : Arg Val t} {a : Arg Val i64}
      {k₁ k₂ : Expr Val Cont rs} :
      ExprRename σ k₁ k₂ → ExprRename σ (.store v a k₁) (.store v a k₂)
  | call {rs : List Ty} (f₁ f₂ : Sym) {as bs : List Ty}
      {args : Tup (Arg Val) as} {k₁ k₂ : Tup Val bs → Expr Val Cont rs} :
      σ f₁ = f₂ → (∀ r, ExprRename σ (k₁ r) (k₂ r)) →
      ExprRename σ (.call f₁ args k₁) (.call f₂ args k₂)
  | jnz {rs : List Ty} {c : Arg Val .bool} {t₁ t₂ e₁ e₂ : Expr Val Cont rs} :
      ExprRename σ t₁ t₂ → ExprRename σ e₁ e₂ → ExprRename σ (.jnz c t₁ e₁) (.jnz c t₂ e₂)
  | jump {rs ts : List Ty} {j : Cont ts} {args : Tup (Arg Val) ts} :
      ExprRename σ (.jump j args) (.jump (rs := rs) j args)
  | ret {rs : List Ty} {vs : Tup (Arg Val) rs} :
      ExprRename σ (.ret vs) (.ret vs)
  | hlt {rs : List Ty} : ExprRename σ (.hlt (rs := rs)) .hlt
  | group {rs : List Ty} {sig : List (List Ty)}
      {b₁ b₂ : Tup Cont sig → Blocks Val Cont rs sig}
      {k₁ k₂ : Tup Cont sig → Expr Val Cont rs} :
      (∀ Js, BlocksRename σ (b₁ Js) (b₂ Js)) → (∀ Js, ExprRename σ (k₁ Js) (k₂ Js)) →
      ExprRename σ (.group b₁ k₁) (.group b₂ k₂)

inductive BlocksRename (σ : Sym → Sym) :
    {rs : List Ty} → {sig : List (List Ty)} →
    Blocks Val Cont rs sig → Blocks Val Cont rs sig → Prop
  | nil {rs : List Ty} : BlocksRename σ (.nil (rs := rs)) .nil
  | cons {rs ts : List Ty} {sig : List (List Ty)}
      {b₁ b₂ : Tup Val ts → Expr Val Cont rs} {bs₁ bs₂ : Blocks Val Cont rs sig} :
      (∀ xs, ExprRename σ (b₁ xs) (b₂ xs)) → BlocksRename σ bs₁ bs₂ →
      BlocksRename σ (.cons b₁ bs₁) (.cons b₂ bs₂)
end

private theorem BlocksRename.get {σ : Sym → Sym} {rs : List Ty} {sig : List (List Ty)}
    {bs₁ bs₂ : Blocks Val Cont rs sig} (h : BlocksRename σ bs₁ bs₂)
    {ts : List Ty} (i : Member ts sig) (xs : Tup Val ts) :
    ExprRename σ (bs₁.get i xs) (bs₂.get i xs) := by
  induction i with
  | here => cases h with | cons hb _ => exact hb xs
  | there i ih => cases h with | cons _ hbs => exact ih hbs

private theorem op_wp_iff {ts : List Ty} (op : Op Val ts) {P₁ P₂ : Tup Val ts → Prop}
    (h : ∀ r, P₁ r ↔ P₂ r) : op.wp P₁ ↔ op.wp P₂ :=
  ⟨fun h1 => Op.wp_mono (fun r hr => (h r).mp hr) h1,
   fun h2 => Op.wp_mono (fun r hr => (h r).mpr hr) h2⟩

theorem wp_iff_of_exprRename (σ : Sym → Sym) (Γ₂ : Env) {rs : List Ty}
    {Q : Post rs} {X : XPost} {e₁ e₂ : Expr Val Cont rs}
    (hrel : ExprRename σ e₁ e₂) :
    ∀ m, wp (fun f as bs => Γ₂ (σ f) as bs) Q X e₁ m ↔ wp Γ₂ Q X e₂ m := by
  let Γ₁ : Env := fun f as bs => Γ₂ (σ f) as bs
  induction e₁ using Expr.induct generalizing e₂ with
  | let_ op k ih =>
    cases hrel with | let_ hk => intro m; exact op_wp_iff op fun r => ih r (hk r) m
  | load t a k ih =>
    cases hrel with | load hk =>
      intro m; dsimp only [wp]
      exact exists_congr fun v => and_congr_right fun _ => ih v (hk v) m
  | store v a k ih =>
    cases hrel with | store hk => intro m; exact and_congr_right fun _ => ih hk _
  | call f args k ih =>
    cases hrel with | call _ _ hf hk =>
      subst hf; intro m; dsimp only [wp, Γ₁]
      exact exists_congr fun P => exists_congr fun E =>
        and_congr_right fun _ => and_congr_left fun _ =>
          forall_congr' fun r => forall_congr' fun m' => imp_congr_right fun _ => ih r (hk r) m'
  | jnz c t e iht ihe =>
    cases hrel with | jnz ht he =>
      intro m; exact and_congr (imp_congr_right fun _ => iht ht m)
        (imp_congr_right fun _ => ihe he m)
  | jump j args => cases hrel; intro _; exact Iff.rfl
  | ret vs => cases hrel; intro _; exact Iff.rfl
  | exit f args => cases hrel
  | hlt => cases hrel; intro _; exact Iff.rfl
  | group bodies k ihb ihk =>
    cases hrel with | group hbr hkr =>
      intro m; dsimp only [wp]
      refine forall_congr' fun Js => ?_
      rw [closed_iff, closed_iff]
      refine imp_congr ?_ (ihk Js (hkr Js) m)
      refine forall_congr' fun ts => forall_congr' fun i => forall_congr' fun xs =>
        forall_congr' fun m' => imp_congr_left ?_
      exact ihb Js i xs ((hbr Js).get i xs) m'

theorem func_wp_of_rename {as rs : List Ty} (σ : Sym → Sym) (f₆ f₇ : Func as rs)
    (hrel : ∀ xs, ExprRename σ (f₆ Val Cont xs) (f₇ Val Cont xs))
    (Γ : Env) {spec : Spec as rs}
    (hwp : ∀ a m Q X, spec a m Q X → Func.wp (fun f as' bs' => Γ (σ f) as' bs') f₆ a m Q X) :
    ∀ a m Q X, spec a m Q X → Func.wp Γ f₇ a m Q X :=
  fun a m Q X hs => (wp_iff_of_exprRename σ Γ (hrel a) m).mp (hwp a m Q X hs)

local macro "rename_step" : tactic =>
  `(tactic| (first
    | exact ExprRename.jump
    | exact ExprRename.ret
    | exact ExprRename.hlt
    | exact BlocksRename.nil
    | (apply ExprRename.let_; intro _)
    | (apply ExprRename.load; intro _)
    | apply ExprRename.store
    | (apply ExprRename.call _ _ rfl; intro _)
    | apply ExprRename.jnz
    | (apply ExprRename.group <;> intro _)
    | (apply BlocksRename.cons; intro _)))

/-! ## 2. Transported `_m7` Function Proofs (`20` Logic-Identical Functions) -/

theorem full_dense_prop_unit_m7_wp (Γ : Env)
    (hAddUnit : ∀ a m Q X, fullAddUnitSpec a m Q X →
      Γ "full_add_unit" [i64, i32] [.bool] a m Q X) :
    ∀ a m Q X, fullDensePropUnitM6Spec a m Q X →
      Func.wp Γ full_dense_prop_unit_m7_body a m Q X := by
  refine func_wp_of_rename m6ToM7Sym full_dense_prop_unit_m6_body full_dense_prop_unit_m7_body
    ?_ Γ (full_dense_prop_unit_m6_wp _ hAddUnit)
  intro _; unfold full_dense_prop_unit_m6_body full_dense_prop_unit_m7_body; repeat rename_step

theorem full_dense_flush_units_m7_wp (Γ : Env)
    (hPropUnit : ∀ a m Q X, fullDensePropUnitM6Spec a m Q X →
      Γ "full_dense_prop_unit_m7" [i64, i32] [.bool] a m Q X) :
    ∀ a m Q X, fullDenseFlushUnitsM6Spec a m Q X →
      Func.wp Γ full_dense_flush_units_m7_body a m Q X := by
  refine func_wp_of_rename m6ToM7Sym full_dense_flush_units_m6_body
    full_dense_flush_units_m7_body ?_ Γ (full_dense_flush_units_m6_wp _ hPropUnit)
  intro _; unfold full_dense_flush_units_m6_body full_dense_flush_units_m7_body; repeat rename_step

theorem full_fwd_flush_large_m7_wp (Γ : Env)
    (hDefrag : ∀ a m Q X, fullWstackDefragSpec a m Q X → Γ "full_wstack_defrag" [i64] [] a m Q X) :
    ∀ a m Q X, fullFwdFlushLargeM6Spec a m Q X →
      Func.wp Γ full_fwd_flush_large_m7_body a m Q X := by
  refine func_wp_of_rename m6ToM7Sym full_fwd_flush_large_m6_body full_fwd_flush_large_m7_body
    ?_ Γ (full_fwd_flush_large_m6_wp _ hDefrag)
  intro _; unfold full_fwd_flush_large_m6_body full_fwd_flush_large_m7_body; repeat rename_step

theorem full_fwd_reconnect_irred_m7_wp (Γ : Env)
    (hFlush : ∀ a m Q X, fullFwdFlushLargeM6Spec a m Q X →
      Γ "full_fwd_flush_large_m7" [i64] [] a m Q X)
    (hNext : ∀ a m Q X, fullArenaNextSpec a m Q X → Γ "full_arena_next" [i64, i32] [i32] a m Q X)
    (hPush : ∀ a m Q X, fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, fullFwdReconnectIrredM6Spec a m Q X →
      Func.wp Γ full_fwd_reconnect_irred_m7_body a m Q X := by
  refine func_wp_of_rename m6ToM7Sym full_fwd_reconnect_irred_m6_body
    full_fwd_reconnect_irred_m7_body ?_ Γ (full_fwd_reconnect_irred_m6_wp _ hFlush hNext hPush)
  intro _; unfold full_fwd_reconnect_irred_m6_body full_fwd_reconnect_irred_m7_body
  repeat rename_step

theorem full_fwd_connect_subsumer_m7_wp (Γ : Env)
    (hPush : ∀ a m Q X, fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, fullFwdConnectSubsumerM6Spec a m Q X →
      Func.wp Γ full_fwd_connect_subsumer_m7_body a m Q X := by
  refine func_wp_of_rename m6ToM7Sym full_fwd_connect_subsumer_m6_body
    full_fwd_connect_subsumer_m7_body ?_ Γ (full_fwd_connect_subsumer_m6_wp _ hPush)
  intro _; unfold full_fwd_connect_subsumer_m6_body full_fwd_connect_subsumer_m7_body
  repeat rename_step

theorem full_fwd_collect_sort_m7_wp (Γ : Env)
    (hNext : ∀ a m Q X, fullArenaNextSpec a m Q X → Γ "full_arena_next" [i64, i32] [i32] a m Q X) :
    ∀ a m Q X, fullFwdCollectSortM6Spec a m Q X →
      Func.wp Γ full_fwd_collect_sort_m7_body a m Q X := by
  refine func_wp_of_rename m6ToM7Sym full_fwd_collect_sort_m6_body full_fwd_collect_sort_m7_body
    ?_ Γ (full_fwd_collect_sort_m6_wp _ hNext)
  intro _; unfold full_fwd_collect_sort_m6_body full_fwd_collect_sort_m7_body; repeat rename_step

theorem full_bve_collect_m7_wp (Γ : Env) :
    ∀ a m Q X, fullBveCollectSpec a m Q X → Func.wp Γ full_bve_collect_m7_body a m Q X := by
  refine func_wp_of_rename m6ToM7Sym full_bve_collect_m6_body full_bve_collect_m7_body
    ?_ Γ (full_bve_collect_m6_wp _)
  intro _; unfold full_bve_collect_m6_body full_bve_collect_m7_body; repeat rename_step

theorem full_bve_mark_and_m7_wp (Γ : Env) :
    ∀ a m Q X, fullBveMarkAndM6Spec a m Q X → Func.wp Γ full_bve_mark_and_m7_body a m Q X := by
  refine func_wp_of_rename m6ToM7Sym full_bve_mark_and_m6_body full_bve_mark_and_m7_body
    ?_ Γ (full_bve_mark_and_m6_wp _)
  intro _; unfold full_bve_mark_and_m6_body full_bve_mark_and_m7_body; repeat rename_step

theorem full_bve_var_key_m7_wp (Γ : Env) :
    ∀ a m Q X, fullBveVarKeyM6Spec a m Q X → Func.wp Γ full_bve_var_key_m7_body a m Q X := by
  refine func_wp_of_rename m6ToM7Sym full_bve_var_key_m6_body full_bve_var_key_m7_body
    ?_ Γ (full_bve_var_key_m6_wp _)
  intro _; unfold full_bve_var_key_m6_body full_bve_var_key_m7_body; repeat rename_step

theorem full_bve_heap_up_m7_wp (Γ : Env) :
    ∀ a m Q X, fullBveHeapUpM6Spec a m Q X → Func.wp Γ full_bve_heap_up_m7_body a m Q X := by
  refine func_wp_of_rename m6ToM7Sym full_bve_heap_up_m6_body full_bve_heap_up_m7_body
    ?_ Γ (full_bve_heap_up_m6_wp _)
  intro _; unfold full_bve_heap_up_m6_body full_bve_heap_up_m7_body; repeat rename_step

theorem full_bve_heap_down_m7_wp (Γ : Env) :
    ∀ a m Q X, fullBveHeapDownM6Spec a m Q X → Func.wp Γ full_bve_heap_down_m7_body a m Q X := by
  refine func_wp_of_rename m6ToM7Sym full_bve_heap_down_m6_body full_bve_heap_down_m7_body
    ?_ Γ (full_bve_heap_down_m6_wp _)
  intro _; unfold full_bve_heap_down_m6_body full_bve_heap_down_m7_body; repeat rename_step

theorem full_bve_heap_push_m7_wp (Γ : Env)
    (hKey : ∀ a m Q X, fullBveVarKeyM6Spec a m Q X →
      Γ "full_bve_var_key_m7" [i64, i32] [i64] a m Q X)
    (hUp : ∀ a m Q X, fullBveHeapUpM6Spec a m Q X →
      Γ "full_bve_heap_up_m7" [i64, i64, i32] [] a m Q X)
    (hDown : ∀ a m Q X, fullBveHeapDownM6Spec a m Q X →
      Γ "full_bve_heap_down_m7" [i64, i64, i32] [] a m Q X) :
    ∀ a m Q X, fullBveHeapPushM6Spec a m Q X → Func.wp Γ full_bve_heap_push_m7_body a m Q X := by
  refine func_wp_of_rename m6ToM7Sym full_bve_heap_push_m6_body full_bve_heap_push_m7_body
    ?_ Γ (full_bve_heap_push_m6_wp _ hKey hUp hDown)
  intro _; unfold full_bve_heap_push_m6_body full_bve_heap_push_m7_body; repeat rename_step

theorem full_bve_heap_pop_m7_wp (Γ : Env)
    (hDown : ∀ a m Q X, fullBveHeapDownM6Spec a m Q X →
      Γ "full_bve_heap_down_m7" [i64, i64, i32] [] a m Q X) :
    ∀ a m Q X, fullBveHeapPopM6Spec a m Q X → Func.wp Γ full_bve_heap_pop_m7_body a m Q X := by
  refine func_wp_of_rename m6ToM7Sym full_bve_heap_pop_m6_body full_bve_heap_pop_m7_body
    ?_ Γ (full_bve_heap_pop_m6_wp _ hDown)
  intro _; unfold full_bve_heap_pop_m6_body full_bve_heap_pop_m7_body; repeat rename_step

theorem full_bve_collect_nbrs_m7_wp (Γ : Env) :
    ∀ a m Q X, m3ElimCollectNbrsSpec a m Q X →
      Func.wp Γ full_bve_collect_nbrs_m7_body a m Q X := by
  refine func_wp_of_rename m6ToM7Sym full_bve_collect_nbrs_m6_body full_bve_collect_nbrs_m7_body
    ?_ Γ (full_bve_collect_nbrs_m6_wp _)
  intro _; unfold full_bve_collect_nbrs_m6_body full_bve_collect_nbrs_m7_body; repeat rename_step

theorem full_elim_bve_m7_wp (Γ : Env)
    (hFlush : ∀ a m Q X, fullDenseFlushUnitsM6Spec a m Q X →
      Γ "full_dense_flush_units_m7" [i64] [.bool] a m Q X)
    (hPush : ∀ a m Q X, fullBveHeapPushM6Spec a m Q X →
      Γ "full_bve_heap_push_m7" [i64, i64, i32] [i64] a m Q X)
    (hPop : ∀ a m Q X, fullBveHeapPopM6Spec a m Q X →
      Γ "full_bve_heap_pop_m7" [i64, i64] [i32] a m Q X)
    (hNbrs : ∀ a m Q X, m3ElimCollectNbrsSpec a m Q X →
      Γ "full_bve_collect_nbrs_m7" [i64, i32] [i64] a m Q X)
    (hVar : ∀ a m Q X, fullBveVarDefSpec a m Q X →
      Γ "full_bve_var_m7" [i64, i32] [i64] a m Q X) :
    ∀ a m Q X, m3ElimBveSpec a m Q X → Func.wp Γ full_elim_bve_m7_body a m Q X := by
  refine func_wp_of_rename m6ToM7Sym full_elim_bve_m6_body full_elim_bve_m7_body ?_ Γ
    (full_elim_bve_m6_wp _ hFlush hPush hPop hNbrs hVar)
  intro _; unfold full_elim_bve_m6_body full_elim_bve_m7_body; repeat rename_step

theorem full_eliminate_m7_wp (Γ : Env)
    (hDticks : ∀ a m Q X, schedElimDticksSpec a m Q X →
      Γ "full_elim_dticks" [i64, .bool] [i64] a m Q X)
    (hIlog10 : ∀ a m Q X, fullIlog10Spec a m Q X → Γ "full_ilog10" [i64] [i64] a m Q X)
    (hScale : ∀ a m Q X, schedScaleDeltaSpec a m Q X →
      Γ "full_scale_delta" [i64, i64] [i64] a m Q X)
    (hEnter : ∀ a m Q X, schedEnterDenseSpec a m Q X → Γ "full_enter_dense" [i64] [.bool] a m Q X)
    (hMin : ∀ a m Q X, schedMinU64Spec a m Q X → Γ "full_min_u64" [i64, i64] [i64] a m Q X)
    (hFwdSub : ∀ a m Q X, fullForwardSubFastSpec a m Q X →
      Γ "full_forward_sub_m7" [i64, i64] [i64] a m Q X)
    (hElimBve : ∀ a m Q X, m3ElimBveSpec a m Q X → Γ "full_elim_bve_m7" [i64, i64] [i64] a m Q X)
    (hFactor : ∀ a m Q X, fullFactorHeapSpec a m Q X → Γ "full_factor" [i64, i64] [i64] a m Q X)
    (hRebuild : ∀ a m Q X, fullRebuildWatchesSpec a m Q X →
      Γ "full_rebuild_watches" [i64] [i64] a m Q X) :
    ∀ a m Q X, schedEliminateSpec a m Q X → Func.wp Γ full_eliminate_m7_body a m Q X := by
  refine func_wp_of_rename m6ToM7Sym full_eliminate_m6_body full_eliminate_m7_body ?_ Γ
    (full_eliminate_m6_wp _ hDticks hIlog10 hScale hEnter hMin hFwdSub hElimBve hFactor hRebuild)
  intro _; unfold full_eliminate_m6_body full_eliminate_m7_body; repeat rename_step


end LeanQbe.T.Examples.Kissat.FullM7BveGates
