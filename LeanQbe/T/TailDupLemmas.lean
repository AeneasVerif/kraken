module

public import LeanQbe.T.TailDup
public import LeanQbe.T.Wf
public import LeanQbe.T.WP
public import LeanQbe.T.Module
import LeanQbe.T.OptUtilLemmas
import LeanQbe.T.OpsLemmas
import LeanQbe.T.WPLemmas
import LeanQbe.T.WfLemmas
public import LeanQbe.T.FlatLemmas

/-!
# Soundness Proofs for `LeanQbe.T.TailDup`

Proves relational well-formedness (`*_wf`), weakest-precondition semantics preservation (`*_spec`
and `tailDup_wp`), and call/exit well-scopedness (`*_callsOk`) for:

* `Func.tailDupWithPlan`: verified linear PHOAS validator (`validatePlan`) + single-pass
  duplication rewriter (`rewriteExpr`).
* `Func.tailDupOnce` / `Func.tailDupLoop` / `Func.tailDup` / `Fn.tailDup`: bounded-iteration
  small join/tail block duplication on closed `Func` and `Fn`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T

namespace TailDupImpl

open TailDup

/-! ## Relational well-formedness (`DupLRel`, `DupDRel`, `rewriteExpr_wf`) -/

/-- Relational invariant pairing two `DupL` labels across target contexts `(G', D')`. -/
inductive DupLRel {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    (G' : Ctx V₁ V₂) (D' : Ctx L₁ L₂) :
    {ts : List Ty} → DupL V₁ L₁ rs ts → DupL V₂ L₂ rs ts → Prop
  | keep {ts : List Ty} {l₁ : L₁ ts} {l₂ : L₂ ts} :
      ⟨ts, l₁, l₂⟩ ∈ D' → DupLRel G' D' (.keep l₁) (.keep l₂)
  | dead {ts : List Ty} :
      DupLRel G' D' (ts := ts) .dead .dead
  | dup {ts : List Ty}
      {b₁ : Tup (Arg V₁) ts → Expr V₁ L₁ rs}
      {b₂ : Tup (Arg V₂) ts → Expr V₂ L₂ rs} :
      (∀ {G'' D''}, (∀ p ∈ G', p ∈ G'') → (∀ p ∈ D', p ∈ D'') →
        ∀ (a₁ : Tup (Arg V₁) ts) (a₂ : Tup (Arg V₂) ts),
          TRel (ArgRel G'') a₁ a₂ → Wf G'' D'' (b₁ a₁) (b₂ a₂)) →
      DupLRel G' D' (.dup b₁) (.dup b₂)

theorem DupLRel.weaken {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G₁ G₂ : Ctx V₁ V₂} {D₁ D₂ : Ctx L₁ L₂}
    (hG : ∀ p ∈ G₁, p ∈ G₂) (hD : ∀ p ∈ D₁, p ∈ D₂)
    {ts : List Ty} {l₁ : DupL V₁ L₁ rs ts} {l₂ : DupL V₂ L₂ rs ts} :
    DupLRel G₁ D₁ l₁ l₂ → DupLRel G₂ D₂ l₁ l₂
  | .keep h => .keep (hD _ h)
  | .dead => .dead
  | .dup hb =>
    .dup fun hG' hD' => hb (fun _ hp => hG' _ (hG _ hp)) (fun _ hp => hD' _ (hD _ hp))

def DupDRel {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    (G' : Ctx V₁ V₂) (D' : Ctx L₁ L₂)
    (D : Ctx (DupL V₁ L₁ rs) (DupL V₂ L₂ rs)) : Prop :=
  ∀ p ∈ D, DupLRel G' D' p.2.1 p.2.2

theorem DupDRel.weaken {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G₁ G₂ : Ctx V₁ V₂} {D₁ D₂ : Ctx L₁ L₂}
    {D : Ctx (DupL V₁ L₁ rs) (DupL V₂ L₂ rs)}
    (hG : ∀ p ∈ G₁, p ∈ G₂) (hD : ∀ p ∈ D₁, p ∈ D₂)
    (h : DupDRel G₁ D₁ D) : DupDRel G₂ D₂ D :=
  fun p hp => (h p hp).weaken hG hD

theorem DupDRel.append {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G' : Ctx V₁ V₂} {D' : Ctx L₁ L₂}
    {H D : Ctx (DupL V₁ L₁ rs) (DupL V₂ L₂ rs)}
    (hH : DupDRel G' D' H) (hD : DupDRel G' D' D) : DupDRel G' D' (H ++ D) := fun p hp =>
  (List.mem_append.1 hp).elim (hH p) (hD p)

theorem deadTup_rel {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G' : Ctx V₁ V₂} {D' : Ctx L₁ L₂} :
    (sig : List (List Ty)) →
    DupDRel G' D' (Tup.zip (deadTup (V := V₁) (L := L₁) (rs := rs) sig)
      (deadTup (V := V₂) (L := L₂) (rs := rs) sig))
  | [], _, hp => nomatch hp
  | _ :: sig, _, .head _ => .dead
  | _ :: sig, p, .tail _ hp => deadTup_rel sig p hp

theorem expandKeepLabels_rel {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G' : Ctx V₁ V₂} {D' : Ctx L₁ L₂} :
    (acts : List DupAct) → (sig : List (List Ty)) →
    (Js₁ : Tup L₁ (filterActsSig acts sig)) → (Js₂ : Tup L₂ (filterActsSig acts sig)) →
    DupDRel G' (Tup.zip Js₁ Js₂ ++ D')
      (Tup.zip (expandKeepLabels (V := V₁) (rs := rs) acts sig Js₁)
        (expandKeepLabels (V := V₂) (rs := rs) acts sig Js₂))
  | _, [], (), (), _, hp => nomatch hp
  | [], _ :: sig, (), (), p, hp => by
    dsimp only [expandKeepLabels, Tup.zip] at hp
    cases hp with
    | head => exact .dead
    | tail _ hp => exact deadTup_rel sig p hp
  | .keep :: acts, _ :: sig, (j₁, js₁), (j₂, js₂), p, hp => by
    dsimp only [expandKeepLabels, Tup.zip] at hp ⊢
    cases hp with
    | head => exact .keep List.mem_cons_self
    | tail _ hp =>
      exact (expandKeepLabels_rel acts sig js₁ js₂ p hp).weaken (fun _ h => h)
        (fun _ h => List.mem_cons_of_mem _ h)
  | .dup :: acts, _ :: sig, js₁, js₂, p, hp => by
    dsimp only [expandKeepLabels, Tup.zip] at hp
    cases hp with
    | head => exact .dead
    | tail _ hp => exact expandKeepLabels_rel acts sig js₁ js₂ p hp
  | .drop :: acts, _ :: sig, js₁, js₂, p, hp => by
    dsimp only [expandKeepLabels, Tup.zip] at hp
    cases hp with
    | head => exact .dead
    | tail _ hp => exact expandKeepLabels_rel acts sig js₁ js₂ p hp

theorem buildDupLabels_rel {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G' : Ctx V₁ V₂} {D' : Ctx L₁ L₂} :
    (acts : List DupAct) → (pbs : DupPlanB) → {sig : List (List Ty)} →
    {bs₁ : Blocks (Arg V₁) (DupL V₁ L₁ rs) rs sig} →
    {bs₂ : Blocks (Arg V₂) (DupL V₂ L₂ rs) rs sig} →
    {ls₁ : Tup (DupL V₁ L₁ rs) sig} → {ls₂ : Tup (DupL V₂ L₂ rs) sig} →
    DupDRel G' D' (Tup.zip ls₁ ls₂) →
    (∀ {ts} (i : Member ts sig) (pb : DupPlan) {G'' D''}
      (a₁ : Tup (Arg V₁) ts) (a₂ : Tup (Arg V₂) ts),
      (∀ p ∈ G', p ∈ G'') → (∀ p ∈ D', p ∈ D'') → TRel (ArgRel G'') a₁ a₂ →
      Wf G'' D'' (rewriteExpr pb (bs₁.get i a₁)) (rewriteExpr pb (bs₂.get i a₂))) →
    DupDRel G' D'
      (Tup.zip (buildDupLabels acts pbs bs₁ ls₁) (buildDupLabels acts pbs bs₂ ls₂))
  | _, _, [], .nil, .nil, (), (), _, _, _, hp => nomatch hp
  | [], _, _ :: sig, .cons _ _, .cons _ _, (_, _), (_, _), _, _, p, hp => by
    dsimp only [buildDupLabels, Tup.zip] at hp
    cases hp with
    | head => exact .dead
    | tail _ hp => exact deadTup_rel sig p hp
  | a :: _, .nil, _ :: sig, .cons _ _, .cons _ _, (_, _), (_, _), _, _, p, hp => by
    cases a <;> (
      dsimp only [buildDupLabels, Tup.zip] at hp
      cases hp with
      | head => exact .dead
      | tail _ hp => exact deadTup_rel sig p hp)
  | .dup :: acts, .cons pb pbs, _ :: _, .cons _ _, .cons _ _, (_, ls₁), (_, ls₂),
      hls, hb, p, hp => by
    dsimp only [buildDupLabels, Tup.zip] at hp
    cases hp with
    | head => exact .dup fun hG hD a₁ a₂ ha => hb .here pb a₁ a₂ hG hD ha
    | tail _ hp =>
      exact buildDupLabels_rel acts pbs (fun _ hq => hls _ (List.mem_cons_of_mem _ hq))
        (fun i => hb (.there i)) p hp
  | .keep :: acts, .cons _ pbs, _ :: _, .cons _ _, .cons _ _, (_, ls₁), (_, ls₂),
      hls, hb, p, hp => by
    dsimp only [buildDupLabels, Tup.zip] at hp
    cases hp with
    | head => exact hls _ List.mem_cons_self
    | tail _ hp =>
      exact buildDupLabels_rel acts pbs (fun _ hq => hls _ (List.mem_cons_of_mem _ hq))
        (fun i => hb (.there i)) p hp
  | .drop :: acts, .cons _ pbs, _ :: _, .cons _ _, .cons _ _, (_, ls₁), (_, ls₂),
      hls, hb, p, hp => by
    dsimp only [buildDupLabels, Tup.zip] at hp
    cases hp with
    | head => exact .dead
    | tail _ hp =>
      exact buildDupLabels_rel acts pbs (fun _ hq => hls _ (List.mem_cons_of_mem _ hq))
        (fun i => hb (.there i)) p hp

theorem rewriteKeptBlocks_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G' : Ctx V₁ V₂} {D' : Ctx L₁ L₂} :
    (acts : List DupAct) → (pbs : DupPlanB) → {sig : List (List Ty)} →
    {bs₁ : Blocks (Arg V₁) (DupL V₁ L₁ rs) rs sig} →
    {bs₂ : Blocks (Arg V₂) (DupL V₂ L₂ rs) rs sig} →
    (∀ {ts} (i : Member ts sig) (pb : DupPlan) (xs₁ : Tup V₁ ts) (xs₂ : Tup V₂ ts),
      Wf (Tup.zip xs₁ xs₂ ++ G') D'
        (rewriteExpr pb (bs₁.get i (toArgTup xs₁)))
        (rewriteExpr pb (bs₂.get i (toArgTup xs₂)))) →
    WfB G' D' (rewriteKeptBlocks acts pbs bs₁) (rewriteKeptBlocks acts pbs bs₂)
  | [], _, [], .nil, .nil, _ => .nil
  | _ :: _, _, [], .nil, .nil, _ => .nil
  | [], _, _ :: _, .cons _ _, .cons _ _, _ => .nil
  | .keep :: acts, .cons pb pbs, _ :: _, .cons _ _, .cons _ _, hb =>
    .cons (fun xs₁ xs₂ => hb .here pb xs₁ xs₂)
      (rewriteKeptBlocks_wf acts pbs fun i => hb (.there i))
  | .dup :: acts, .cons _ pbs, _ :: _, .cons _ _, .cons _ _, hb =>
    rewriteKeptBlocks_wf acts pbs fun i => hb (.there i)
  | .drop :: acts, .cons _ pbs, _ :: _, .cons _ _, .cons _ _, hb =>
    rewriteKeptBlocks_wf acts pbs fun i => hb (.there i)
  | .keep :: acts, .nil, _ :: _, .cons _ _, .cons _ _, hb =>
    .cons (fun _ _ => .hlt) (rewriteKeptBlocks_wf acts .nil fun i => hb (.there i))
  | .dup :: acts, .nil, _ :: _, .cons _ _, .cons _ _, hb =>
    rewriteKeptBlocks_wf acts .nil fun i => hb (.there i)
  | .drop :: acts, .nil, _ :: _, .cons _ _, .cons _ _, hb =>
    rewriteKeptBlocks_wf acts .nil fun i => hb (.there i)

/-- `rewriteExpr` preserves `Wf` for every `DupPlan`. -/
theorem rewriteExpr_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx (Arg V₁) (Arg V₂)} {D : Ctx (DupL V₁ L₁ rs) (DupL V₂ L₂ rs)}
    {e₁ : Expr (Arg V₁) (DupL V₁ L₁ rs) rs} {e₂ : Expr (Arg V₂) (DupL V₂ L₂ rs) rs}
    (hwf : Wf G D e₁ e₂) :
    ∀ {G' : Ctx V₁ V₂} {D' : Ctx L₁ L₂} (plan : DupPlan),
      (∀ p ∈ G, ArgRel G' p.1 p.2.1 p.2.2) → DupDRel G' D' D →
      Wf G' D' (rewriteExpr plan e₁) (rewriteExpr plan e₂) := by
  induction hwf using Wf.induct with
  | let_ hop _ ih =>
    intro G' D' plan hG hD
    cases plan with
    | node1 pk =>
      exact .let_ (hop.flattenOp hG) fun xs₁ xs₂ =>
        ih (toArgTup xs₁) (toArgTup xs₂) pk
          (ctx_argRel_append (mem_zip_toArgTup xs₁ xs₂) hG)
          (hD.weaken (fun _ h => List.mem_append_right _ h) (fun _ h => h))
    | _ => exact .hlt
  | load t ha _ ih =>
    intro G' D' plan hG hD
    cases plan with
    | node1 pk =>
      exact .load t (ha.flattenArg hG) fun v₁ v₂ =>
        ih (.var v₁) (.var v₂) pk
          (ctx_argRel_cons_var hG v₁ v₂)
          (hD.weaken (fun _ h => List.mem_cons_of_mem _ h) (fun _ h => h))
    | _ => exact .hlt
  | store hv ha _ ih =>
    intro G' D' plan hG hD
    cases plan with
    | node1 pk => exact .store (hv.flattenArg hG) (ha.flattenArg hG) (ih pk hG hD)
    | _ => exact .hlt
  | call f hargs _ ih =>
    intro G' D' plan hG hD
    cases plan with
    | node1 pk =>
      exact .call f (TRel.flattenArgs hG hargs) fun xs₁ xs₂ =>
        ih (toArgTup xs₁) (toArgTup xs₂) pk
          (ctx_argRel_append (mem_zip_toArgTup xs₁ xs₂) hG)
          (hD.weaken (fun _ h => List.mem_append_right _ h) (fun _ h => h))
    | _ => exact .hlt
  | jnz hc _ _ iht ihe =>
    intro G' D' plan hG hD
    cases plan with
    | node2 pt pe => exact .jnz (hc.flattenArg hG) (iht pt hG hD) (ihe pe hG hD)
    | _ => exact .hlt
  | jump hj hargs =>
    intro G' D' plan hG hD
    cases plan with
    | leaf =>
      have hdj := hD _ hj
      dsimp only at hdj
      cases hdj with
      | keep hj' => exact .jump hj' (TRel.flattenArgs hG hargs)
      | dead => exact .hlt
      | dup hb => exact hb (fun _ h => h) (fun _ h => h) _ _ (TRel.flattenArgs hG hargs)
    | _ => exact .hlt
  | ret hvs =>
    intro G' D' plan hG _
    cases plan with
    | leaf => exact .ret (TRel.flattenArgs hG hvs)
    | _ => exact .hlt
  | exit f hargs =>
    intro G' D' plan hG _
    cases plan with
    | leaf => exact .exit f (TRel.flattenArgs hG hargs)
    | _ => exact .hlt
  | hlt =>
    intro _ _ plan _ _
    cases plan <;> exact .hlt
  | @group G D sig b₁ b₂ k₁ k₂ _ _ ihb ihk =>
    intro G' D' plan hG hD
    cases plan with
    | group acts pbs pk =>
      dsimp only [rewriteExpr]
      by_cases hkeep : acts.any (· == .keep) = true
      · simp only [hkeep, ↓reduceIte]
        refine .group (fun Js₁ Js₂ => ?_) (fun Js₁ Js₂ => ?_)
        · let lsNo₁ := expandKeepLabels (V := V₁) (rs := rs) acts sig Js₁
          let lsNo₂ := expandKeepLabels (V := V₂) (rs := rs) acts sig Js₂
          have hNo : DupDRel G' (Tup.zip Js₁ Js₂ ++ D') (Tup.zip lsNo₁ lsNo₂) :=
            expandKeepLabels_rel acts sig Js₁ Js₂
          have hDup : DupDRel G' (Tup.zip Js₁ Js₂ ++ D')
              (Tup.zip (buildDupLabels acts pbs (b₁ lsNo₁) lsNo₁)
                (buildDupLabels acts pbs (b₂ lsNo₂) lsNo₂)) :=
            buildDupLabels_rel acts pbs hNo fun {_} i pb {G'' D''} a₁ a₂ hsubG hsubD ha =>
              ihb lsNo₁ lsNo₂ i a₁ a₂ pb
                (ctx_argRel_append_same (mem_zip_argRel ha) fun p hp => (hG p hp).weaken hsubG)
                ((hNo.weaken hsubG hsubD).append
                  (hD.weaken hsubG (fun _ h => hsubD _ (List.mem_append_right _ h))))
          have hD_dup := hDup.append
            (hD.weaken (fun _ h => h) (fun _ h => List.mem_append_right _ h))
          exact rewriteKeptBlocks_wf acts pbs fun i pb xs₁ xs₂ =>
            ihb _ _ i (toArgTup xs₁) (toArgTup xs₂) pb
              (ctx_argRel_append (mem_zip_toArgTup xs₁ xs₂) hG)
              (hD_dup.weaken (fun _ h => List.mem_append_right _ h) (fun _ h => h))
        · let lsNo₁ := expandKeepLabels (V := V₁) (rs := rs) acts sig Js₁
          let lsNo₂ := expandKeepLabels (V := V₂) (rs := rs) acts sig Js₂
          have hNo : DupDRel G' (Tup.zip Js₁ Js₂ ++ D') (Tup.zip lsNo₁ lsNo₂) :=
            expandKeepLabels_rel acts sig Js₁ Js₂
          have hDup : DupDRel G' (Tup.zip Js₁ Js₂ ++ D')
              (Tup.zip (buildDupLabels acts pbs (b₁ lsNo₁) lsNo₁)
                (buildDupLabels acts pbs (b₂ lsNo₂) lsNo₂)) :=
            buildDupLabels_rel acts pbs hNo fun {_} i pb {G'' D''} a₁ a₂ hsubG hsubD ha =>
              ihb lsNo₁ lsNo₂ i a₁ a₂ pb
                (ctx_argRel_append_same (mem_zip_argRel ha) fun p hp => (hG p hp).weaken hsubG)
                ((hNo.weaken hsubG hsubD).append
                  (hD.weaken hsubG (fun _ h => hsubD _ (List.mem_append_right _ h))))
          exact ihk _ _ pk hG
            (hDup.append (hD.weaken (fun _ h => h) (fun _ h => List.mem_append_right _ h)))
      · have hno : acts.any (· == .keep) = false := Bool.eq_false_iff.mpr hkeep
        simp only [hno, Bool.false_eq_true, ↓reduceIte]
        have hNo : DupDRel G' D'
            (Tup.zip (deadTup (V := V₁) (L := L₁) (rs := rs) sig)
              (deadTup (V := V₂) (L := L₂) (rs := rs) sig)) := deadTup_rel sig
        have hDup : DupDRel G' D'
            (Tup.zip (buildDupLabels acts pbs (b₁ (deadTup sig)) (deadTup sig))
              (buildDupLabels acts pbs (b₂ (deadTup sig)) (deadTup sig))) :=
          buildDupLabels_rel acts pbs hNo fun {_} i pb {G'' D''} a₁ a₂ hsubG hsubD ha =>
            ihb (deadTup sig) (deadTup sig) i a₁ a₂ pb
              (ctx_argRel_append_same (mem_zip_argRel ha) fun p hp => (hG p hp).weaken hsubG)
              ((hNo.weaken hsubG hsubD).append (hD.weaken hsubG hsubD))
        exact ihk _ _ pk hG (hDup.append hD)
    | _ => exact .hlt

/-! ## Weakest-precondition refinement (`ValidDk`, `DupWpD`, `rewriteExpr_wp`) -/

/-- Whether a `DupL` label is live (not `.dead`). -/
def isLiveDupL {V : Ty → Type} {L : List Ty → Type} {rs ts : List Ty} :
    DupL V L rs ts → Bool
  | .keep _ => true
  | .dup _ => true
  | .dead => false

/-- Every `true` label in `Dk` corresponds to a live (non-`.dead`) `DupL` label. -/
def ValidDk {rs : List Ty} (Dk : Ctx BoolL (DupL Val Cont rs)) : Prop :=
  ∀ p ∈ Dk, p.2.1 = true → isLiveDupL p.2.2 = true

theorem ValidDk.append {rs : List Ty} {H Dk : Ctx BoolL (DupL Val Cont rs)}
    (hH : ValidDk H) (hD : ValidDk Dk) : ValidDk (H ++ Dk) := fun p hp =>
  (List.mem_append.1 hp).elim (hH p) (hD p)

/-- Weakest-precondition invariant relating `DupL Val Cont rs` labels to source `Cont`s. -/
def DupWpD (Γ : Env) {rs : List Ty} (Q : Post rs) (X : XPost)
    (D : Ctx (DupL Val Cont rs) Cont) : Prop :=
  ∀ p ∈ D, match p.2.1 with
    | .keep J => J = p.2.2
    | .dead => True
    | .dup b => ∀ (args : Tup (Arg Val) p.1) (m : Mem 64),
        p.2.2 (vals args) m → wp Γ Q X (b args) m

theorem DupWpD.append {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {H D : Ctx (DupL Val Cont rs) Cont}
    (hH : DupWpD Γ Q X H) (hD : DupWpD Γ Q X D) : DupWpD Γ Q X (H ++ D) := fun p hp =>
  (List.mem_append.1 hp).elim (hH p) (hD p)

private def tupTrue : (sig : List (List Ty)) → Tup Cont sig
  | [] => ()
  | _ :: sig => (fun _ _ => True, tupTrue sig)

private theorem validDk_allFalse_dead {rs : List Ty} :
    (sig : List (List Ty)) →
    ValidDk (Tup.zip (allFalse sig) (deadTup (V := Val) (L := Cont) (rs := rs) sig))
  | [], _, hp, _ => nomatch hp
  | _ :: _, _, .head _, h => by cases h
  | _ :: sig, p, .tail _ hp, h => validDk_allFalse_dead sig p hp h

private theorem dupWpD_dead (Γ : Env) {rs : List Ty} (Q : Post rs) (X : XPost) :
    (sig : List (List Ty)) → (Js : Tup Cont sig) →
    DupWpD Γ Q X (Tup.zip (deadTup (V := Val) (L := Cont) (rs := rs) sig) Js)
  | [], (), _, hp => nomatch hp
  | _ :: _, (_, _), _, .head _ => trivial
  | _ :: sig, (_, Js), p, .tail _ hp => dupWpD_dead Γ Q X sig Js p hp

private theorem filterActsSig_eq_nil_of_noKeep :
    (acts : List DupAct) → (sig : List (List Ty)) →
    acts.any (· == .keep) = false → filterActsSig acts sig = []
  | _, [], _ => rfl
  | [], _ :: _, _ => rfl
  | .keep :: _, _ :: _, h => by simp [List.any] at h
  | .dup :: acts, _ :: sig, h => by
    have h' : acts.any (· == .keep) = false := by simpa [List.any] using h
    exact filterActsSig_eq_nil_of_noKeep acts sig h'
  | .drop :: acts, _ :: sig, h => by
    have h' : acts.any (· == .keep) = false := by simpa [List.any] using h
    exact filterActsSig_eq_nil_of_noKeep acts sig h'

private theorem expandKeepLabels_eq_deadTup_of_noKeep {V : Ty → Type} {L : List Ty → Type}
    {rs : List Ty} :
    (acts : List DupAct) → (sig : List (List Ty)) →
    acts.any (· == .keep) = false →
    (Js : Tup L (filterActsSig acts sig)) →
    expandKeepLabels (V := V) (rs := rs) acts sig Js = deadTup sig
  | _, [], _, () => rfl
  | [], _ :: _, _, () => rfl
  | .keep :: _, _ :: _, h, _ => by simp [List.any] at h
  | .dup :: acts, _ :: sig, h, js => by
    have h' : acts.any (· == .keep) = false := by simpa [List.any] using h
    exact congrArg (_, ·) (expandKeepLabels_eq_deadTup_of_noKeep acts sig h' js)
  | .drop :: acts, _ :: sig, h, js => by
    have h' : acts.any (· == .keep) = false := by simpa [List.any] using h
    exact congrArg (_, ·) (expandKeepLabels_eq_deadTup_of_noKeep acts sig h' js)

private theorem closed_rewriteKeptBlocks_of_noKeep (Γ : Env) {rs : List Ty} (Q : Post rs)
    (X : XPost) :
    (acts : List DupAct) → (pbs : DupPlanB) → {sig : List (List Ty)} →
    (bs : Blocks (Arg Val) (DupL Val Cont rs) rs sig) →
    (hno : acts.any (· == .keep) = false) →
    (Js : Tup Cont (filterActsSig acts sig)) →
    Closed Γ Q X (rewriteKeptBlocks acts pbs bs) Js
  | _, _, [], .nil, _, _ => trivial
  | [], _, _ :: _, .cons _ _, _, _ => trivial
  | .keep :: _, _, _ :: _, .cons _ _, hno, _ => by simp [List.any] at hno
  | .dup :: acts, .cons _ pbs, _ :: _, .cons _ bs, hno, Js => by
    have h' : acts.any (· == .keep) = false := by simpa [List.any] using hno
    exact closed_rewriteKeptBlocks_of_noKeep Γ Q X acts pbs bs h' Js
  | .drop :: acts, .cons _ pbs, _ :: _, .cons _ bs, hno, Js => by
    have h' : acts.any (· == .keep) = false := by simpa [List.any] using hno
    exact closed_rewriteKeptBlocks_of_noKeep Γ Q X acts pbs bs h' Js
  | .dup :: acts, .nil, _ :: _, .cons _ bs, hno, Js => by
    have h' : acts.any (· == .keep) = false := by simpa [List.any] using hno
    exact closed_rewriteKeptBlocks_of_noKeep Γ Q X acts .nil bs h' Js
  | .drop :: acts, .nil, _ :: _, .cons _ bs, hno, Js => by
    have h' : acts.any (· == .keep) = false := by simpa [List.any] using hno
    exact closed_rewriteKeptBlocks_of_noKeep Γ Q X acts .nil bs h' Js

/-- Source continuation tuple used for `Closed` in the `.group` case of `rewriteExpr_wp`. -/
private def dupSrcConts (Γ : Env) {rs : List Ty} (Q : Post rs) (X : XPost) :
    (acts : List DupAct) → (pbs : DupPlanB) → {sig : List (List Ty)} →
    Blocks (Arg Val) (DupL Val Cont rs) rs sig →
    Tup Cont (filterActsSig acts sig) → Tup Cont sig
  | _, _, [], .nil, () => ()
  | [], _, _ :: sig, .cons _ _, () => (fun _ _ => True, tupTrue sig)
  | .keep :: acts, .nil, _ :: _, .cons _ bs, (J, Js) =>
    (J, dupSrcConts Γ Q X acts .nil bs Js)
  | .dup :: acts, .nil, _ :: _, .cons _ bs, Js =>
    (fun _ _ => True, dupSrcConts Γ Q X acts .nil bs Js)
  | .drop :: acts, .nil, _ :: _, .cons _ bs, Js =>
    (fun _ _ => True, dupSrcConts Γ Q X acts .nil bs Js)
  | .keep :: acts, .cons _ pbs, _ :: _, .cons _ bs, (J, Js) =>
    (J, dupSrcConts Γ Q X acts pbs bs Js)
  | .dup :: acts, .cons pb pbs, ts :: _, .cons b bs, Js =>
    (fun xs m => ∀ (args : Tup (Arg Val) ts), vals args = xs →
      wp Γ Q X (rewriteExpr pb (b args)) m,
     dupSrcConts Γ Q X acts pbs bs Js)
  | .drop :: acts, .cons _ pbs, _ :: _, .cons _ bs, Js =>
    (fun _ _ => True, dupSrcConts Γ Q X acts pbs bs Js)

private theorem validDk_noDup {rs : List Ty} :
    (acts : List DupAct) → (sig : List (List Ty)) → (Js : Tup Cont (filterActsSig acts sig)) →
    ValidDk (Tup.zip (noDupBoolTup acts sig) (expandKeepLabels (V := Val) (rs := rs) acts sig Js))
  | _, [], (), _, hp, _ => nomatch hp
  | [], _ :: sig, (), p, hp, h => by
    dsimp only [noDupBoolTup, expandKeepLabels, Tup.zip] at hp
    cases hp with
    | head => cases h
    | tail _ hp => exact validDk_allFalse_dead sig p hp h
  | .keep :: acts, _ :: sig, (J, Js), p, hp, h => by
    dsimp only [noDupBoolTup, expandKeepLabels, Tup.zip] at hp
    cases hp with
    | head => rfl
    | tail _ hp => exact validDk_noDup acts sig Js p hp h
  | .dup :: acts, _ :: sig, Js, p, hp, h => by
    dsimp only [noDupBoolTup, expandKeepLabels, Tup.zip] at hp
    cases hp with
    | head => cases h
    | tail _ hp => exact validDk_noDup acts sig Js p hp h
  | .drop :: acts, _ :: sig, Js, p, hp, h => by
    dsimp only [noDupBoolTup, expandKeepLabels, Tup.zip] at hp
    cases hp with
    | head => cases h
    | tail _ hp => exact validDk_noDup acts sig Js p hp h

private theorem dupWpD_noDup (Γ : Env) {rs : List Ty} (Q : Post rs) (X : XPost) :
    (acts : List DupAct) → (pbs : DupPlanB) → {sig : List (List Ty)} →
    (bs : Blocks (Arg Val) (DupL Val Cont rs) rs sig) →
    (Js : Tup Cont (filterActsSig acts sig)) →
    DupWpD Γ Q X
      (Tup.zip (expandKeepLabels (V := Val) (rs := rs) acts sig Js)
        (dupSrcConts Γ Q X acts pbs bs Js))
  | _, _, [], .nil, (), _, hp => nomatch hp
  | [], _, _ :: sig, .cons _ _, (), p, hp => by
    dsimp only [expandKeepLabels, dupSrcConts, Tup.zip] at hp
    cases hp with
    | head => trivial
    | tail _ hp => exact dupWpD_dead Γ Q X sig (tupTrue sig) p hp
  | .keep :: acts, .nil, _ :: _, .cons _ bs, (_, Js), p, hp => by
    dsimp only [expandKeepLabels, dupSrcConts, Tup.zip] at hp
    cases hp with
    | head => rfl
    | tail _ hp => exact dupWpD_noDup Γ Q X acts .nil bs Js p hp
  | .dup :: acts, .nil, _ :: _, .cons _ bs, Js, p, hp => by
    dsimp only [expandKeepLabels, dupSrcConts, Tup.zip] at hp
    cases hp with
    | head => trivial
    | tail _ hp => exact dupWpD_noDup Γ Q X acts .nil bs Js p hp
  | .drop :: acts, .nil, _ :: _, .cons _ bs, Js, p, hp => by
    dsimp only [expandKeepLabels, dupSrcConts, Tup.zip] at hp
    cases hp with
    | head => trivial
    | tail _ hp => exact dupWpD_noDup Γ Q X acts .nil bs Js p hp
  | .keep :: acts, .cons _ pbs, _ :: _, .cons _ bs, (_, Js), p, hp => by
    dsimp only [expandKeepLabels, dupSrcConts, Tup.zip] at hp
    cases hp with
    | head => rfl
    | tail _ hp => exact dupWpD_noDup Γ Q X acts pbs bs Js p hp
  | .dup :: acts, .cons _ pbs, _ :: _, .cons _ bs, Js, p, hp => by
    dsimp only [expandKeepLabels, dupSrcConts, Tup.zip] at hp
    cases hp with
    | head => trivial
    | tail _ hp => exact dupWpD_noDup Γ Q X acts pbs bs Js p hp
  | .drop :: acts, .cons _ pbs, _ :: _, .cons _ bs, Js, p, hp => by
    dsimp only [expandKeepLabels, dupSrcConts, Tup.zip] at hp
    cases hp with
    | head => trivial
    | tail _ hp => exact dupWpD_noDup Γ Q X acts pbs bs Js p hp

private theorem validDk_dup {rs : List Ty} :
    (acts : List DupAct) → (pbs : DupPlanB) → {sig : List (List Ty)} →
    (bsk : Blocks UnitV BoolL rs sig) →
    (bs₁ : Blocks (Arg Val) (DupL Val Cont rs) rs sig) →
    (ls : Tup (DupL Val Cont rs) sig) →
    validateDupBlocks acts pbs bsk = true →
    ValidDk (Tup.zip (noDupBoolTup acts sig) ls) →
    ValidDk (Tup.zip (dupBoolTup acts sig) (buildDupLabels acts pbs bs₁ ls))
  | [], .nil, [], .nil, .nil, (), _, _, _, hp, _ => nomatch hp
  | .keep :: acts, .cons _ pbs, _ :: _, .cons _ bsk, .cons _ bs₁, (_, ls), hval, hls, p, hp, h => by
    change validateDupBlocks acts pbs bsk = true at hval
    dsimp only [dupBoolTup, buildDupLabels, Tup.zip] at hp
    cases hp with
    | head => exact hls _ List.mem_cons_self h
    | tail _ hp =>
      exact validDk_dup acts pbs bsk bs₁ ls hval
        (fun _ hq => hls _ (List.mem_cons_of_mem _ hq)) p hp h
  | .dup :: acts, .cons pb pbs, _ :: _, .cons _ bsk, .cons _ bs₁, (_, ls), hval, hls, p, hp, h => by
    change (validatePlan pb _ && validateDupBlocks acts pbs bsk) = true at hval
    simp only [Bool.and_eq_true] at hval
    dsimp only [dupBoolTup, buildDupLabels, Tup.zip] at hp
    cases hp with
    | head => rfl
    | tail _ hp =>
      exact validDk_dup acts pbs bsk bs₁ ls hval.2
        (fun _ hq => hls _ (List.mem_cons_of_mem _ hq)) p hp h
  | .drop :: acts, .cons _ pbs, _ :: _, .cons _ bsk, .cons _ bs₁, (_, ls), hval, hls, p, hp, h => by
    change validateDupBlocks acts pbs bsk = true at hval
    dsimp only [dupBoolTup, buildDupLabels, Tup.zip] at hp
    cases hp with
    | head => cases h
    | tail _ hp =>
      exact validDk_dup acts pbs bsk bs₁ ls hval
        (fun _ hq => hls _ (List.mem_cons_of_mem _ hq)) p hp h
  | [], .cons _ _, [], .nil, .nil, (), hval, _, _, _, _ => by cases hval
  | _ :: _, pbs, [], .nil, .nil, (), hval, _, _, _, _ => by cases pbs <;> cases hval
  | [], pbs, _ :: _, .cons _ _, .cons _ _, _, hval, _, _, _, _ => by cases pbs <;> cases hval
  | a :: _, .nil, _ :: _, .cons _ _, .cons _ _, _, hval, _, _, _, _ => by cases a <;> cases hval

private theorem dupWpD_dup (Γ : Env) {rs : List Ty} (Q : Post rs) (X : XPost) :
    (acts : List DupAct) → (pbs : DupPlanB) → {sig : List (List Ty)} →
    (bsk : Blocks UnitV BoolL rs sig) →
    (bs₁ : Blocks (Arg Val) (DupL Val Cont rs) rs sig) →
    (ls : Tup (DupL Val Cont rs) sig) →
    (Js : Tup Cont (filterActsSig acts sig)) →
    validateDupBlocks acts pbs bsk = true →
    DupWpD Γ Q X (Tup.zip ls (dupSrcConts Γ Q X acts pbs bs₁ Js)) →
    DupWpD Γ Q X
      (Tup.zip (buildDupLabels acts pbs bs₁ ls) (dupSrcConts Γ Q X acts pbs bs₁ Js))
  | [], .nil, [], .nil, .nil, (), (), _, _, _, hp => nomatch hp
  | .keep :: acts, .cons _ pbs, _ :: _, .cons _ bsk, .cons _ bs₁, (_, ls), (_, Js),
      hval, hls, p, hp => by
    change validateDupBlocks acts pbs bsk = true at hval
    dsimp only [buildDupLabels, dupSrcConts, Tup.zip] at hp
    cases hp with
    | head => exact hls _ List.mem_cons_self
    | tail _ hp =>
      exact dupWpD_dup Γ Q X acts pbs bsk bs₁ ls Js hval
        (fun _ hq => hls _ (List.mem_cons_of_mem _ hq)) p hp
  | .dup :: acts, .cons pb pbs, _ :: _, .cons _ bsk, .cons _ bs₁, (_, ls), Js,
      hval, hls, p, hp => by
    change (validatePlan pb _ && validateDupBlocks acts pbs bsk) = true at hval
    simp only [Bool.and_eq_true] at hval
    dsimp only [buildDupLabels, dupSrcConts, Tup.zip] at hp
    cases hp with
    | head => exact fun args m h => h args rfl
    | tail _ hp =>
      exact dupWpD_dup Γ Q X acts pbs bsk bs₁ ls Js hval.2
        (fun _ hq => hls _ (List.mem_cons_of_mem _ hq)) p hp
  | .drop :: acts, .cons _ pbs, _ :: _, .cons _ bsk, .cons _ bs₁, (_, ls), Js,
      hval, hls, p, hp => by
    change validateDupBlocks acts pbs bsk = true at hval
    dsimp only [buildDupLabels, dupSrcConts, Tup.zip] at hp
    cases hp with
    | head => trivial
    | tail _ hp =>
      exact dupWpD_dup Γ Q X acts pbs bsk bs₁ ls Js hval
        (fun _ hq => hls _ (List.mem_cons_of_mem _ hq)) p hp
  | [], .cons _ _, [], .nil, .nil, (), (), hval, _, _, _ => by cases hval
  | _ :: _, pbs, [], .nil, .nil, (), _, hval, _, _, _ => by cases pbs <;> cases hval
  | [], pbs, _ :: _, .cons _ _, .cons _ _, _, (), hval, _, _, _ => by cases pbs <;> cases hval
  | a :: _, .nil, _ :: _, .cons _ _, .cons _ _, _, _, hval, _, _, _ => by cases a <;> cases hval

private theorem dupSrcConts_closed (Γ : Env) {rs : List Ty} (Q : Post rs) (X : XPost) :
    (acts : List DupAct) → (pbs : DupPlanB) → {sig : List (List Ty)} →
    (bskNo bskYes : Blocks UnitV BoolL rs sig) →
    (bsNo bsYes : Blocks (Arg Val) (DupL Val Cont rs) rs sig) →
    (bs₂ : Blocks Val Cont rs sig) →
    (Js : Tup Cont (filterActsSig acts sig)) →
    validateDupBlocks acts pbs bskNo = true →
    validateKeptBlocks acts pbs bskYes = true →
    Closed Γ Q X (rewriteKeptBlocks acts pbs bsYes) Js →
    (∀ {ts} (i : Member ts sig) (pb : DupPlan) (args : Tup (Arg Val) ts) (xs : Tup Val ts),
      validatePlan pb (bskNo.get i (Tup.units ts)) = true → vals args = xs →
      ∀ m, wp Γ Q X (bs₂.get i xs) m → wp Γ Q X (rewriteExpr pb (bsNo.get i args)) m) →
    (∀ {ts} (i : Member ts sig) (pb : DupPlan) (xs : Tup Val ts),
      validatePlan pb (bskYes.get i (Tup.units ts)) = true →
      ∀ m, wp Γ Q X (bs₂.get i xs) m →
        wp Γ Q X (rewriteExpr pb (bsYes.get i (toArgTup xs))) m) →
    Closed Γ Q X bs₂ (dupSrcConts Γ Q X acts pbs bsNo Js)
  | [], .nil, [], .nil, .nil, .nil, .nil, .nil, (), _, _, _, _, _ => trivial
  | .keep :: acts, .cons pb pbs, _ :: _, .cons _ bskNo, .cons _ bskYes,
      .cons _ bsNo, .cons _ bsYes, .cons _ bs₂, (J, Js), hvNo, hvYes, hcl, hDup, hKeep => by
    change validateDupBlocks acts pbs bskNo = true at hvNo
    change (validatePlan pb _ && validateKeptBlocks acts pbs bskYes) = true at hvYes
    simp only [Bool.and_eq_true] at hvYes
    simp only [rewriteKeptBlocks] at hcl
    simp only [Closed]
    exact ⟨fun xs m hw => hcl.1 xs m (hKeep .here pb xs hvYes.1 m hw),
      dupSrcConts_closed Γ Q X acts pbs bskNo bskYes bsNo bsYes bs₂ Js hvNo hvYes.2 hcl.2
        (fun i => hDup (.there i)) (fun i => hKeep (.there i))⟩
  | .dup :: acts, .cons pb pbs, _ :: _, .cons _ bskNo, .cons _ bskYes,
      .cons _ bsNo, .cons _ bsYes, .cons _ bs₂, Js, hvNo, hvYes, hcl, hDup, hKeep => by
    change (validatePlan pb _ && validateDupBlocks acts pbs bskNo) = true at hvNo
    change validateKeptBlocks acts pbs bskYes = true at hvYes
    simp only [Bool.and_eq_true] at hvNo
    simp only [rewriteKeptBlocks] at hcl
    simp only [Closed]
    exact ⟨fun xs m hw args hargs => hDup .here pb args xs hvNo.1 hargs m hw,
      dupSrcConts_closed Γ Q X acts pbs bskNo bskYes bsNo bsYes bs₂ Js hvNo.2 hvYes hcl
        (fun i => hDup (.there i)) (fun i => hKeep (.there i))⟩
  | .drop :: acts, .cons _ pbs, _ :: _, .cons _ bskNo, .cons _ bskYes,
      .cons _ bsNo, .cons _ bsYes, .cons _ bs₂, Js, hvNo, hvYes, hcl, hDup, hKeep => by
    change validateDupBlocks acts pbs bskNo = true at hvNo
    change validateKeptBlocks acts pbs bskYes = true at hvYes
    simp only [rewriteKeptBlocks] at hcl
    simp only [Closed]
    exact ⟨fun _ _ _ => trivial,
      dupSrcConts_closed Γ Q X acts pbs bskNo bskYes bsNo bsYes bs₂ Js hvNo hvYes hcl
        (fun i => hDup (.there i)) (fun i => hKeep (.there i))⟩
  | [], .cons _ _, [], .nil, .nil, .nil, .nil, .nil, (), hvNo, _, _, _, _ => by cases hvNo
  | _ :: _, pbs, [], .nil, .nil, .nil, .nil, .nil, (), hvNo, _, _, _, _ => by
    cases pbs <;> cases hvNo
  | [], pbs, _ :: _, .cons _ _, .cons _ _, .cons _ _, .cons _ _, .cons _ _, (),
      hvNo, _, _, _, _ => by cases pbs <;> cases hvNo
  | a :: _, .nil, _ :: _, .cons _ _, .cons _ _, .cons _ _, .cons _ _, .cons _ _, _,
      hvNo, _, _, _, _ => by cases a <;> cases hvNo

/-- `rewriteExpr` refines `wp` whenever `validatePlan` accepts the plan. -/
theorem rewriteExpr_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {G : Ctx (Arg Val) Val} {D : Ctx (DupL Val Cont rs) Cont}
    {e₁ : Expr (Arg Val) (DupL Val Cont rs) rs} {e₂ : Expr Val Cont rs}
    (hwf : Wf G D e₁ e₂) :
    ∀ {Gk : Ctx UnitV (Arg Val)} {Dk : Ctx BoolL (DupL Val Cont rs)}
      {ek : Expr UnitV BoolL rs} (_hwk : Wf Gk Dk ek e₁)
      (plan : DupPlan) (_hval : validatePlan plan ek = true),
      (∀ p ∈ G, p.2.1.val = p.2.2) →
      ValidDk Dk → DupWpD Γ Q X D →
      ∀ m, wp Γ Q X e₂ m → wp Γ Q X (rewriteExpr plan e₁) m := by
  induction hwf using Wf.induct with
  | let_ hop _ ih =>
    intro Gk Dk ek hwk plan hval hG hDk hD m hw2
    rcases hwk.rhs_let with ⟨_, kk, rfl, _, hkk⟩
    cases plan with
    | node1 pk =>
      cases hop with
      | mk code hargs =>
        dsimp only [validatePlan] at hval
        dsimp only [rewriteExpr, flattenOp, wp, Op.wp] at hw2 ⊢
        rw [flattenArgs_vals hG hargs]
        exact OpCode.wp_mono code _ (fun r =>
          ih (toArgTup r) r (hkk (Tup.units _) (toArgTup r)) pk hval
            (ctx_val_append (toArgTup_zip_val r) hG) hDk hD m) hw2
    | _ => dsimp only [validatePlan] at hval; cases hval
  | load t ha _ ih =>
    intro Gk Dk ek hwk plan hval hG hDk hD m ⟨v, hv, hw2⟩
    rcases hwk.rhs_load with ⟨_, kk, rfl, _, hkk⟩
    cases plan with
    | node1 pk =>
      dsimp only [validatePlan] at hval
      dsimp only [rewriteExpr, wp]
      rw [flattenArg_val hG ha]
      exact ⟨v, hv, ih (.var v) v (hkk () (.var v)) pk hval
        (ctx_val_cons_var hG v) hDk hD m hw2⟩
    | _ => dsimp only [validatePlan] at hval; cases hval
  | store hv ha _ ih =>
    intro Gk Dk ek hwk plan hval hG hDk hD m ⟨hok, hw2⟩
    rcases hwk.rhs_store with ⟨_, _, kk, rfl, _, _, hkk⟩
    cases plan with
    | node1 pk =>
      dsimp only [validatePlan] at hval
      dsimp only [rewriteExpr, wp]
      rw [flattenArg_val hG hv, flattenArg_val hG ha]
      exact ⟨hok, ih hkk pk hval hG hDk hD _ hw2⟩
    | _ => dsimp only [validatePlan] at hval; cases hval
  | call f hargs _ ih =>
    intro Gk Dk ek hwk plan hval hG hDk hD m ⟨P, E, hΓ, hP, hE⟩
    rcases hwk.rhs_call with ⟨_, kk, rfl, _, hkk⟩
    cases plan with
    | node1 pk =>
      dsimp only [validatePlan] at hval
      dsimp only [rewriteExpr, wp]
      rw [flattenArgs_vals hG hargs]
      exact ⟨P, E, hΓ, fun r m' hp =>
        ih (toArgTup r) r (hkk (Tup.units _) (toArgTup r)) pk hval
          (ctx_val_append (toArgTup_zip_val r) hG) hDk hD m' (hP r m' hp), hE⟩
    | _ => dsimp only [validatePlan] at hval; cases hval
  | jnz hc _ _ iht ihe =>
    intro Gk Dk ek hwk plan hval hG hDk hD m hw2
    rcases hwk.rhs_jnz with ⟨_, tk, ek', rfl, _, htk, hek⟩
    cases plan with
    | node2 pt pe =>
      dsimp only [validatePlan] at hval; simp only [Bool.and_eq_true] at hval
      dsimp only [rewriteExpr, wp] at hw2 ⊢
      rw [flattenArg_val hG hc]
      exact ⟨fun h => iht htk pt hval.1 hG hDk hD m (hw2.1 h),
             fun h => ihe hek pe hval.2 hG hDk hD m (hw2.2 h)⟩
    | _ => dsimp only [validatePlan] at hval; cases hval
  | @jump _ _ _ j₁ _ _ _ hj hargs =>
    intro Gk Dk ek hwk plan hval hG hDk hD m hw2
    rcases hwk.rhs_jump with ⟨ok, _, rfl, hjk, _⟩
    cases plan with
    | leaf =>
      dsimp only [validatePlan] at hval
      have hlive : isLiveDupL j₁ = true := hDk _ hjk hval
      have hd := hD _ hj
      cases j₁ with
      | keep J =>
        dsimp only [rewriteExpr, wp] at hw2 ⊢
        dsimp only at hd
        rw [flattenArgs_vals hG hargs, hd]
        exact hw2
      | dead => dsimp only [isLiveDupL] at hlive; cases hlive
      | dup body =>
        dsimp only [rewriteExpr, wp] at hw2 ⊢
        exact hd _ m (by rw [flattenArgs_vals hG hargs]; exact hw2)
    | _ => dsimp only [validatePlan] at hval; cases hval
  | ret hvs =>
    intro Gk Dk ek hwk plan hval hG _ _ m hw2
    rcases hwk.rhs_ret with ⟨_, rfl, _⟩
    cases plan with
    | leaf =>
      dsimp only [rewriteExpr, wp] at hw2 ⊢
      rwa [flattenArgs_vals hG hvs]
    | _ => dsimp only [validatePlan] at hval; cases hval
  | exit f hargs =>
    intro Gk Dk ek hwk plan hval hG _ _ m hw2
    rcases hwk.rhs_exit with ⟨_, rfl, _⟩
    cases plan with
    | leaf =>
      dsimp only [rewriteExpr, wp] at hw2 ⊢
      rwa [flattenArgs_vals hG hargs]
    | _ => dsimp only [validatePlan] at hval; cases hval
  | hlt =>
    intro Gk Dk ek hwk plan hval _ _ _ _ hw2
    rcases hwk.rhs_hlt with rfl
    cases plan with
    | leaf => exact hw2
    | _ => dsimp only [validatePlan] at hval; cases hval
  | @group G D sig b₁ b₂ k₁ k₂ _ _ ihb ihk =>
    intro Gk Dk ek hwk plan hval hG hDk hD m hw2
    rcases hwk.rhs_group with ⟨bk, kk, rfl, hbk, hkk⟩
    cases plan with
    | group acts pbs pk =>
      dsimp only [validatePlan] at hval
      simp only [Bool.and_eq_true] at hval
      rcases hval with ⟨⟨hvNo, hvYes⟩, hvk⟩
      dsimp only [rewriteExpr]
      have runStep : ∀ (Js_out : Tup Cont (filterActsSig acts sig)),
          Closed Γ Q X (rewriteKeptBlocks acts pbs
            (b₁ (buildDupLabels acts pbs (b₁ (expandKeepLabels acts sig Js_out))
              (expandKeepLabels acts sig Js_out)))) Js_out →
          wp Γ Q X (rewriteExpr pk
            (k₁ (buildDupLabels acts pbs (b₁ (expandKeepLabels acts sig Js_out))
              (expandKeepLabels acts sig Js_out)))) m := by
        intro Js_out hcl_out
        let lsNo := expandKeepLabels (V := Val) (rs := rs) acts sig Js_out
        let lsDup := buildDupLabels acts pbs (b₁ lsNo) lsNo
        let Js₂ := dupSrcConts Γ Q X acts pbs (b₁ lsNo) Js_out
        have hDkNo : ValidDk (Tup.zip (noDupBoolTup acts sig) lsNo ++ Dk) :=
          (validDk_noDup acts sig Js_out).append hDk
        have hDNo : DupWpD Γ Q X (Tup.zip lsNo Js₂ ++ D) :=
          (dupWpD_noDup Γ Q X acts pbs (b₁ lsNo) Js_out).append hD
        have hDkYes : ValidDk (Tup.zip (dupBoolTup acts sig) lsDup ++ Dk) :=
          (validDk_dup acts pbs (bk (noDupBoolTup acts sig)) (b₁ lsNo) lsNo hvNo
            (validDk_noDup acts sig Js_out)).append hDk
        have hDYes : DupWpD Γ Q X (Tup.zip lsDup Js₂ ++ D) :=
          (dupWpD_dup Γ Q X acts pbs (bk (noDupBoolTup acts sig)) (b₁ lsNo) lsNo Js_out hvNo
            (dupWpD_noDup Γ Q X acts pbs (b₁ lsNo) Js_out)).append hD
        have hcl₂ : Closed Γ Q X (b₂ Js₂) Js₂ :=
          dupSrcConts_closed Γ Q X acts pbs
            (bk (noDupBoolTup acts sig)) (bk (dupBoolTup acts sig))
            (b₁ lsNo) (b₁ lsDup) (b₂ Js₂) Js_out hvNo hvYes hcl_out
            (fun i pb args xs hvb hargs m' hw =>
              ihb lsNo Js₂ i args xs
                ((hbk (noDupBoolTup acts sig) lsNo).get i (Tup.units _) args) pb hvb
                (ctx_val_append (tup_zip_vals_val args xs hargs) hG) hDkNo hDNo m' hw)
            (fun i pb xs hvb m' hw =>
              ihb lsDup Js₂ i (toArgTup xs) xs
                ((hbk (dupBoolTup acts sig) lsDup).get i (Tup.units _) (toArgTup xs)) pb hvb
                (ctx_val_append (toArgTup_zip_val xs) hG) hDkYes hDYes m' hw)
        exact ihk lsDup Js₂ (hkk (dupBoolTup acts sig) lsDup) pk hvk hG hDkYes hDYes m
          (hw2 Js₂ hcl₂)
      by_cases hkeep : acts.any (· == .keep) = true
      · simp only [hkeep, ↓reduceIte, wp]
        exact runStep
      · have hno : acts.any (· == .keep) = false := Bool.eq_false_iff.mpr hkeep
        simp only [hno, Bool.false_eq_true, ↓reduceIte]
        let Js_out : Tup Cont (filterActsSig acts sig) :=
          (filterActsSig_eq_nil_of_noKeep acts sig hno) ▸ ()
        have hexp : expandKeepLabels (V := Val) (rs := rs) acts sig Js_out = deadTup sig :=
          expandKeepLabels_eq_deadTup_of_noKeep acts sig hno Js_out
        have hstep := runStep Js_out
          (closed_rewriteKeptBlocks_of_noKeep Γ Q X acts pbs _ hno Js_out)
        simpa [hexp] using hstep
    | _ => dsimp only [validatePlan] at hval; cases hval

/-! ## Call/exit well-scopedness (`rewriteExpr_callsOk`, `denote_toTFlat_callsOk`) -/

private def DupCallsOkD (allowed : List SigEntry) (exits : List Sym) {rs : List Ty}
    (D : Ctx (DupL UnitV (fun _ => Unit) rs) (fun _ => Unit)) : Prop :=
  ∀ p ∈ D, match p.2.1 with
    | .keep _ => True
    | .dead => True
    | .dup body => ∀ args, (body args).callsOk allowed exits

private theorem DupCallsOkD.append {allowed : List SigEntry} {exits : List Sym} {rs : List Ty}
    {H D : Ctx (DupL UnitV (fun _ => Unit) rs) (fun _ => Unit)}
    (hH : DupCallsOkD allowed exits H) (hD : DupCallsOkD allowed exits D) :
    DupCallsOkD allowed exits (H ++ D) := fun p hp =>
  (List.mem_append.1 hp).elim (hH p) (hD p)

private theorem deadTup_callsOkD {allowed : List SigEntry} {exits : List Sym} {rs : List Ty} :
    (sig : List (List Ty)) →
    DupCallsOkD allowed exits
      (Tup.zip (deadTup (V := UnitV) (L := fun _ => Unit) (rs := rs) sig) (Tup.units sig))
  | [], _, hp => nomatch hp
  | _ :: sig, _, .head _ => trivial
  | _ :: sig, p, .tail _ hp => deadTup_callsOkD sig p hp

private theorem expandKeepLabels_callsOkD {allowed : List SigEntry} {exits : List Sym}
    {rs : List Ty} :
    (acts : List DupAct) → (sig : List (List Ty)) →
    (Js : Tup (fun _ => Unit) (filterActsSig acts sig)) →
    DupCallsOkD allowed exits
      (Tup.zip (expandKeepLabels (V := UnitV) (rs := rs) acts sig Js) (Tup.units sig))
  | _, [], (), _, hp => nomatch hp
  | [], _ :: sig, (), p, hp => by
    dsimp only [expandKeepLabels, Tup.units, Tup.zip] at hp
    cases hp with
    | head => trivial
    | tail _ hp => exact deadTup_callsOkD sig p hp
  | .keep :: acts, _ :: sig, (_, js), p, hp => by
    dsimp only [expandKeepLabels, Tup.units, Tup.zip] at hp
    cases hp with
    | head => trivial
    | tail _ hp => exact expandKeepLabels_callsOkD acts sig js p hp
  | .dup :: acts, _ :: sig, js, p, hp => by
    dsimp only [expandKeepLabels, Tup.units, Tup.zip] at hp
    cases hp with
    | head => trivial
    | tail _ hp => exact expandKeepLabels_callsOkD acts sig js p hp
  | .drop :: acts, _ :: sig, js, p, hp => by
    dsimp only [expandKeepLabels, Tup.units, Tup.zip] at hp
    cases hp with
    | head => trivial
    | tail _ hp => exact expandKeepLabels_callsOkD acts sig js p hp

private theorem buildDupLabels_callsOkD {allowed : List SigEntry} {exits : List Sym}
    {rs : List Ty} :
    (acts : List DupAct) → (pbs : DupPlanB) → {sig : List (List Ty)} →
    (bs : Blocks (Arg UnitV) (DupL UnitV (fun _ => Unit) rs) rs sig) →
    (ls : Tup (DupL UnitV (fun _ => Unit) rs) sig) →
    DupCallsOkD allowed exits (Tup.zip ls (Tup.units sig)) →
    (∀ {ts} (i : Member ts sig) pb (a : Tup (Arg UnitV) ts),
      (rewriteExpr pb (bs.get i a)).callsOk allowed exits) →
    DupCallsOkD allowed exits (Tup.zip (buildDupLabels acts pbs bs ls) (Tup.units sig))
  | _, _, [], .nil, (), _, _, _, hp => nomatch hp
  | [], _, _ :: sig, .cons _ _, (_, _), _, _, p, hp => by
    dsimp only [buildDupLabels, Tup.units, Tup.zip] at hp
    cases hp with
    | head => trivial
    | tail _ hp => exact deadTup_callsOkD sig p hp
  | a :: _, .nil, _ :: sig, .cons _ _, (_, _), _, _, p, hp => by
    cases a <;> (
      dsimp only [buildDupLabels, Tup.units, Tup.zip] at hp
      cases hp with
      | head => trivial
      | tail _ hp => exact deadTup_callsOkD sig p hp)
  | .dup :: acts, .cons pb pbs, _ :: _, .cons _ bs, (_, ls), hls, hb, p, hp => by
    dsimp only [buildDupLabels, Tup.units, Tup.zip] at hp
    cases hp with
    | head => exact fun args => hb .here pb args
    | tail _ hp =>
      exact buildDupLabels_callsOkD acts pbs bs ls
        (fun _ hq => hls _ (List.mem_cons_of_mem _ hq)) (fun i => hb (.there i)) p hp
  | .keep :: acts, .cons _ pbs, _ :: _, .cons _ bs, (_, ls), hls, hb, p, hp => by
    dsimp only [buildDupLabels, Tup.units, Tup.zip] at hp
    cases hp with
    | head => exact hls _ List.mem_cons_self
    | tail _ hp =>
      exact buildDupLabels_callsOkD acts pbs bs ls
        (fun _ hq => hls _ (List.mem_cons_of_mem _ hq)) (fun i => hb (.there i)) p hp
  | .drop :: acts, .cons _ pbs, _ :: _, .cons _ bs, (_, ls), hls, hb, p, hp => by
    dsimp only [buildDupLabels, Tup.units, Tup.zip] at hp
    cases hp with
    | head => trivial
    | tail _ hp =>
      exact buildDupLabels_callsOkD acts pbs bs ls
        (fun _ hq => hls _ (List.mem_cons_of_mem _ hq)) (fun i => hb (.there i)) p hp

private theorem rewriteKeptBlocks_callsOk {allowed : List SigEntry} {exits : List Sym}
    {rs : List Ty} :
    (acts : List DupAct) → (pbs : DupPlanB) → {sig : List (List Ty)} →
    (bs : Blocks (Arg UnitV) (DupL UnitV (fun _ => Unit) rs) rs sig) →
    (∀ {ts} (i : Member ts sig) pb (a : Tup (Arg UnitV) ts),
      (rewriteExpr pb (bs.get i a)).callsOk allowed exits) →
    (rewriteKeptBlocks acts pbs bs).callsOk allowed exits
  | [], _, [], .nil, _ => trivial
  | _ :: _, _, [], .nil, _ => trivial
  | [], _, _ :: _, .cons _ _, _ => trivial
  | .keep :: acts, .cons pb pbs, _ :: _, .cons _ bs, hb =>
    ⟨hb .here pb _, rewriteKeptBlocks_callsOk acts pbs bs fun i => hb (.there i)⟩
  | .dup :: acts, .cons _ pbs, _ :: _, .cons _ bs, hb =>
    rewriteKeptBlocks_callsOk acts pbs bs fun i => hb (.there i)
  | .drop :: acts, .cons _ pbs, _ :: _, .cons _ bs, hb =>
    rewriteKeptBlocks_callsOk acts pbs bs fun i => hb (.there i)
  | .keep :: acts, .nil, _ :: _, .cons _ bs, hb =>
    ⟨trivial, rewriteKeptBlocks_callsOk acts .nil bs fun i => hb (.there i)⟩
  | .dup :: acts, .nil, _ :: _, .cons _ bs, hb =>
    rewriteKeptBlocks_callsOk acts .nil bs fun i => hb (.there i)
  | .drop :: acts, .nil, _ :: _, .cons _ bs, hb =>
    rewriteKeptBlocks_callsOk acts .nil bs fun i => hb (.there i)

private theorem rewriteExpr_callsOk {allowed : List SigEntry} {exits : List Sym} {rs : List Ty}
    {G : Ctx (Arg UnitV) UnitV} {D : Ctx (DupL UnitV (fun _ => Unit) rs) (fun _ => Unit)}
    {e₁ : Expr (Arg UnitV) (DupL UnitV (fun _ => Unit) rs) rs}
    {e₂ : Expr UnitV (fun _ => Unit) rs}
    (hwf : Wf G D e₁ e₂) :
    ∀ (p : DupPlan), DupCallsOkD allowed exits D → e₂.callsOk allowed exits →
      (rewriteExpr p e₁).callsOk allowed exits := by
  induction hwf using Wf.induct with
  | let_ _ _ ih =>
    intro p hD hc
    cases p with
    | node1 pk => exact ih (toArgTup (Tup.units _)) (Tup.units _) pk hD hc
    | _ => trivial
  | load _ _ _ ih =>
    intro p hD hc
    cases p with
    | node1 pk => exact ih (.var ()) () pk hD hc
    | _ => trivial
  | store _ _ _ ih =>
    intro p hD hc
    cases p with
    | node1 pk => exact ih pk hD hc
    | _ => trivial
  | call _ _ _ ih =>
    intro p hD ⟨hf, hc⟩
    cases p with
    | node1 pk => exact ⟨hf, ih (toArgTup (Tup.units _)) (Tup.units _) pk hD hc⟩
    | _ => trivial
  | jnz _ _ _ iht ihe =>
    intro p hD ⟨ht, he⟩
    cases p with
    | node2 pt pe => exact ⟨iht pt hD ht, ihe pe hD he⟩
    | _ => trivial
  | @jump _ _ _ j₁ _ _ _ hj _ =>
    intro p hD _
    cases p with
    | leaf =>
      have hd := hD _ hj
      cases j₁ with
      | keep _ => trivial
      | dead => trivial
      | dup body => exact hd _
    | _ => trivial
  | ret _ => intro p _ _; cases p <;> trivial
  | exit _ _ => intro p _ hc; cases p <;> first | trivial | exact hc
  | hlt => intro p _ _; cases p <;> trivial
  | @group _ D sig b₁ b₂ _ _ _ _ ihb ihk =>
    intro p hD ⟨hcb, hck⟩
    cases p with
    | group acts pbs pk =>
      dsimp only [rewriteExpr]
      by_cases hkeep : acts.any (· == .keep) = true
      · simp only [hkeep, ↓reduceIte, Expr.callsOk]
        let lsNo := expandKeepLabels (V := UnitV) (rs := rs) acts sig (Tup.units _)
        have hD_no : DupCallsOkD allowed exits (Tup.zip lsNo (Tup.units sig) ++ D) :=
          (expandKeepLabels_callsOkD acts sig (Tup.units _)).append hD
        have hDup : DupCallsOkD allowed exits
            (Tup.zip (buildDupLabels acts pbs (b₁ lsNo) lsNo) (Tup.units sig)) :=
          buildDupLabels_callsOkD acts pbs (b₁ lsNo) lsNo
            (expandKeepLabels_callsOkD acts sig (Tup.units _)) fun i pb a =>
              ihb lsNo (Tup.units sig) i a (Tup.units _) pb hD_no (Blocks.callsOk_get hcb i)
        have hD_dup := hDup.append hD
        let lsDup := buildDupLabels acts pbs (b₁ lsNo) lsNo
        exact ⟨rewriteKeptBlocks_callsOk acts pbs (b₁ lsDup) fun i pb a =>
            ihb lsDup (Tup.units sig) i a (Tup.units _) pb hD_dup (Blocks.callsOk_get hcb i),
          ihk lsDup (Tup.units sig) pk hD_dup hck⟩
      · have hno : acts.any (· == .keep) = false := Bool.eq_false_iff.mpr hkeep
        simp only [hno, Bool.false_eq_true, ↓reduceIte]
        let lsNo := deadTup (V := UnitV) (L := fun _ => Unit) (rs := rs) sig
        have hD_no : DupCallsOkD allowed exits (Tup.zip lsNo (Tup.units sig) ++ D) :=
          (deadTup_callsOkD sig).append hD
        have hDup : DupCallsOkD allowed exits
            (Tup.zip (buildDupLabels acts pbs (b₁ lsNo) lsNo) (Tup.units sig)) :=
          buildDupLabels_callsOkD acts pbs (b₁ lsNo) lsNo (deadTup_callsOkD sig) fun i pb a =>
            ihb lsNo (Tup.units sig) i a (Tup.units _) pb hD_no (Blocks.callsOk_get hcb i)
        exact ihk _ (Tup.units sig) pk (hDup.append hD) hck
    | _ => trivial

private theorem denoteB_toTBlocks_callsOk {allowed : List SigEntry} {exits : List Sym}
    {rs : List Ty} :
    {sig : List (List Ty)} → {bs₁ : Blocks K KL rs sig} →
    {bs₂ : Blocks UnitV (fun _ => Unit) rs sig} →
    (nv nl : Nat) → (vs : List ((_t : Ty) × Unit)) → (ls : List ((_ts : List Ty) × Unit)) →
    (∀ {ts} (i : Member ts sig), (bs₂.get i (Tup.units ts)).callsOk allowed exits →
      (denote UnitV (fun _ => Unit)
        (toTFlat (bs₁.get i (Tup.levels ts nv)) (nv + ts.length) nl)
        (pushTup (Tup.units ts) vs) ls).callsOk allowed exits) →
    bs₂.callsOk allowed exits →
    (denoteB UnitV (fun _ => Unit) (toTBlocks bs₁ nv nl) vs ls).callsOk allowed exits
  | [], .nil, .nil, _, _, _, _, _, _ => trivial
  | _ :: _, .cons _ _, .cons _ _, nv, nl, vs, ls, h, hc =>
    ⟨h .here hc.1, denoteB_toTBlocks_callsOk nv nl vs ls (fun i => h (.there i)) hc.2⟩

private theorem denote_toTFlat_callsOk {allowed : List SigEntry} {exits : List Sym} {rs : List Ty}
    {G : Ctx K UnitV} {D : Ctx KL (fun _ => Unit)}
    {e₁ : Expr K KL rs} {e₂ : Expr UnitV (fun _ => Unit) rs}
    (hwf : Wf G D e₁ e₂) :
    ∀ (nv nl : Nat) (vs : List ((_t : Ty) × Unit)) (ls : List ((_ts : List Ty) × Unit)),
      e₂.callsOk allowed exits →
      (denote UnitV (fun _ => Unit) (toTFlat e₁ nv nl) vs ls).callsOk allowed exits := by
  induction hwf using Wf.induct with
  | @let_ G D ts op₁ op₂ k₁ k₂ _ _ ih =>
    intro nv nl vs ls hc
    dsimp only [toTFlat, denote]
    cases denoteArgs vs (idxArgs nv op₁.args) with
    | none => trivial
    | some _ => exact ih (Tup.levels ts nv) (Tup.units ts) (nv + ts.length) nl _ ls hc
  | load _ _ _ ih =>
    intro nv nl vs ls hc
    dsimp only [toTFlat, denote]
    cases denoteArg vs (idxArg nv _) with
    | none => trivial
    | some _ => exact ih nv () (nv + 1) nl _ ls hc
  | store _ _ _ ih =>
    intro nv nl vs ls hc
    dsimp only [toTFlat, denote]
    cases denoteArg vs _ <;> cases denoteArg vs _ <;> first | trivial | exact ih nv nl vs ls hc
  | call _ _ _ ih =>
    intro nv nl vs ls ⟨hf, hc⟩
    dsimp only [toTFlat, denote]
    cases denoteArgs vs _ with
    | none => trivial
    | some _ => exact ⟨hf, ih (Tup.levels _ nv) (Tup.units _) (nv + _) nl _ ls hc⟩
  | jnz _ _ _ iht ihe =>
    intro nv nl vs ls ⟨ht, he⟩
    dsimp only [toTFlat, denote]
    cases denoteArg vs _ with
    | none => trivial
    | some _ => exact ⟨iht nv nl vs ls ht, ihe nv nl vs ls he⟩
  | jump _ _ =>
    intro nv nl vs ls _
    dsimp only [toTFlat, denote]
    cases lookupL ls _ _ <;> cases denoteArgs vs _ <;> trivial
  | ret _ =>
    intro nv nl vs _ _
    dsimp only [toTFlat, denote]; cases denoteArgs vs _ <;> trivial
  | exit _ _ =>
    intro nv nl vs _ _
    dsimp only [toTFlat, denote]; cases denoteArgs vs _ <;> trivial
  | hlt => intro _ _ _ _ _; trivial
  | @group _ _ sig b₁ b₂ k₁ k₂ _ _ ihb ihk =>
    intro nv nl vs ls ⟨hb, hk⟩
    dsimp only [toTFlat, denote, Expr.callsOk]
    exact ⟨denoteB_toTBlocks_callsOk nv (nl + sig.length) vs _
        (fun i hci => ihb (Tup.levels sig nl) (Tup.units sig) i (Tup.levels _ nv) (Tup.units _)
          (nv + _) (nl + sig.length) _ _ hci) hb,
      ihk (Tup.levels sig nl) (Tup.units sig) nv (nl + sig.length) vs _ hk⟩

end TailDupImpl

/-! ## Top-level soundness theorems (`Func.tailDup_*`, `tailDup_wp`, `Fn.tailDup_*`) -/

open TailDup TailDupImpl

/-- `Func.tailDupWithPlan` preserves relational well-formedness `Func.Wf`. -/
theorem Func.tailDupWithPlan_wf {as rs : List Ty} (plan : DupPlan) {f : Func as rs}
    (hf : f.Wf) : (Func.tailDupWithPlan plan f).Wf := by
  dsimp only [Func.tailDupWithPlan]
  split
  · intro V₁ V₂ L₁ L₂ xs₁ xs₂
    exact rewriteExpr_wf
      (hf (Arg V₁) (Arg V₂) (DupL V₁ L₁ rs) (DupL V₂ L₂ rs) (toArgTup xs₁) (toArgTup xs₂))
      plan (mem_zip_toArgTup xs₁ xs₂) (fun _ hp => nomatch hp)
  · exact hf

/-- `Func.tailDupWithPlan` refines `Func.wp` / `Func.spec` for any well-formed `f`. -/
theorem Func.tailDupWithPlan_spec {as rs : List Ty} (plan : DupPlan) {f : Func as rs}
    (hf : f.Wf) {Γ : Env} {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Func.spec Γ f xs m Q X) : Func.spec Γ (Func.tailDupWithPlan plan f) xs m Q X := by
  dsimp only [Func.tailDupWithPlan]
  split
  · rename_i hval
    have hwf := hf (Arg Val) Val (DupL Val Cont rs) Cont (toArgTup xs) xs
    have hwk := hf UnitV (Arg Val) BoolL (DupL Val Cont rs) (Tup.units as) (toArgTup xs)
    exact rewriteExpr_wp hwf hwk plan hval (toArgTup_zip_val xs)
      (fun _ hp => nomatch hp) (fun _ hp => nomatch hp) m h
  · exact h

/-- `Func.tailDupWithPlan` preserves `Expr.callsOk`. -/
theorem Func.tailDupWithPlan_callsOk {allowed : List SigEntry} {exits : List Sym}
    {as rs : List Ty} (plan : DupPlan) {f : Func as rs} (hf : f.Wf)
    (hc : (f UnitV (fun _ => Unit) (Tup.units as)).callsOk allowed exits) :
    ((Func.tailDupWithPlan plan f) UnitV (fun _ => Unit) (Tup.units as)).callsOk
      allowed exits := by
  dsimp only [Func.tailDupWithPlan]
  split
  · exact rewriteExpr_callsOk
      (hf (Arg UnitV) UnitV (DupL UnitV (fun _ => Unit) rs) (fun _ => Unit)
        (toArgTup (Tup.units as)) (Tup.units as))
      plan (fun _ hp => nomatch hp) hc
  · exact hc

/-- `Func.tailDupOnce` produces a well-formed function. -/
theorem Func.tailDupOnce_wf {as rs : List Ty} {f : Func as rs} (cfg : TailDupConfig) :
    (Func.tailDupOnce f cfg).1.Wf := by
  dsimp only [Func.tailDupOnce]
  split
  · exact Func.tailDupWithPlan_wf _ (Func.wf_of_denote (reifyFunc f) rfl)
  · exact Func.wf_of_denote (reifyFunc f) rfl

/-- `Func.tailDupOnce` refines `Func.wp` / `Func.spec` for any well-formed `f`. -/
theorem Func.tailDupOnce_spec {as rs : List Ty} {f : Func as rs} (hf : f.Wf)
    (cfg : TailDupConfig) {Γ : Env} {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Func.spec Γ f xs m Q X) : Func.spec Γ (Func.tailDupOnce f cfg).1 xs m Q X := by
  dsimp only [Func.tailDupOnce]
  split
  · exact Func.tailDupWithPlan_spec _ (Func.wf_of_denote (reifyFunc f) rfl) (Func.renorm_spec hf h)
  · exact Func.renorm_spec hf h

/-- `Func.tailDupOnce` preserves `Expr.callsOk` for any well-formed `f`. -/
theorem Func.tailDupOnce_callsOk {allowed : List SigEntry} {exits : List Sym}
    {as rs : List Ty} {f : Func as rs} (hf : f.Wf) (cfg : TailDupConfig)
    (hc : (f UnitV (fun _ => Unit) (Tup.units as)).callsOk allowed exits) :
    ((Func.tailDupOnce f cfg).1 UnitV (fun _ => Unit) (Tup.units as)).callsOk
      allowed exits := by
  have hr : ((denoteFunc (as := as) (reifyFunc f)) UnitV (fun _ => Unit)
      (Tup.units as)).callsOk allowed exits := by
    simpa [denoteFunc, reifyFunc] using
      denote_toTFlat_callsOk
        (hf K UnitV KL (fun _ => Unit) (Tup.levels as 0) (Tup.units as))
        as.length 0 (pushTup (Tup.units as) []) [] hc
  dsimp only [Func.tailDupOnce]
  split
  · exact Func.tailDupWithPlan_callsOk _ (Func.wf_of_denote (reifyFunc f) rfl) hr
  · exact hr

/-- `Func.tailDupLoop` preserves `Func.Wf`. -/
theorem Func.tailDupLoop_wf {as rs : List Ty} (cfg : TailDupConfig) :
    (fuel : Nat) → {f : Func as rs} → f.Wf → (Func.tailDupLoop cfg fuel f).Wf
  | 0, _, hf => hf
  | fuel + 1, f, _ => by
    dsimp only [Func.tailDupLoop]
    split
    · exact Func.tailDupLoop_wf cfg fuel (Func.tailDupOnce_wf cfg)
    · exact Func.tailDupOnce_wf cfg

/-- `Func.tailDupLoop` refines `Func.wp` / `Func.spec` for any well-formed `f`. -/
theorem Func.tailDupLoop_spec {as rs : List Ty} (cfg : TailDupConfig) :
    (fuel : Nat) → {f : Func as rs} → f.Wf →
    {Γ : Env} → {xs : Tup Val as} → {m : Mem 64} → {Q : Post rs} → {X : XPost} →
    Func.spec Γ f xs m Q X → Func.spec Γ (Func.tailDupLoop cfg fuel f) xs m Q X
  | 0, _, _, _, _, _, _, _, h => h
  | fuel + 1, f, hf, _, _, _, _, _, h => by
    dsimp only [Func.tailDupLoop]
    split
    · exact Func.tailDupLoop_spec cfg fuel (Func.tailDupOnce_wf cfg)
        (Func.tailDupOnce_spec hf cfg h)
    · exact Func.tailDupOnce_spec hf cfg h

/-- `Func.tailDupLoop` preserves `Expr.callsOk` for any well-formed `f`. -/
theorem Func.tailDupLoop_callsOk {allowed : List SigEntry} {exits : List Sym}
    {as rs : List Ty} (cfg : TailDupConfig) :
    (fuel : Nat) → {f : Func as rs} → f.Wf →
    (f UnitV (fun _ => Unit) (Tup.units as)).callsOk allowed exits →
    ((Func.tailDupLoop cfg fuel f) UnitV (fun _ => Unit) (Tup.units as)).callsOk allowed exits
  | 0, _, _, hc => hc
  | fuel + 1, f, hf, hc => by
    dsimp only [Func.tailDupLoop]
    split
    · exact Func.tailDupLoop_callsOk cfg fuel (Func.tailDupOnce_wf cfg)
        (Func.tailDupOnce_callsOk hf cfg hc)
    · exact Func.tailDupOnce_callsOk hf cfg hc

/-- `Func.tailDup` preserves relational well-formedness `Func.Wf`. -/
theorem Func.tailDup_wf {as rs : List Ty} {f : Func as rs} (hf : f.Wf)
    (cfg : TailDupConfig := {}) : (Func.tailDup f cfg).Wf :=
  Func.tailDupLoop_wf cfg cfg.maxIters hf

/-- `Func.tailDup` refines `Func.wp` / `Func.spec` for any well-formed `f`. -/
theorem Func.tailDup_spec {as rs : List Ty} {f : Func as rs} (hf : f.Wf)
    (cfg : TailDupConfig := {}) {Γ : Env} {xs : Tup Val as} {m : Mem 64}
    {Q : Post rs} {X : XPost} (h : Func.spec Γ f xs m Q X) :
    Func.spec Γ (Func.tailDup f cfg) xs m Q X :=
  Func.tailDupLoop_spec cfg cfg.maxIters hf h

/-- Semantic `Func.wp` preservation alias for `Func.tailDup`. -/
theorem tailDup_wp {as rs : List Ty} {f : Func as rs} (hf : f.Wf)
    (cfg : TailDupConfig := {}) {Γ : Env} {xs : Tup Val as} {m : Mem 64}
    {Q : Post rs} {X : XPost} (h : Func.wp Γ f xs m Q X) :
    Func.wp Γ (Func.tailDup f cfg) xs m Q X :=
  Func.tailDup_spec hf cfg h

/-- `Func.tailDup` preserves `Expr.callsOk` for any well-formed `f`. -/
theorem Func.tailDup_callsOk {allowed : List SigEntry} {exits : List Sym}
    {as rs : List Ty} {f : Func as rs} (hf : f.Wf) (cfg : TailDupConfig := {})
    (hc : (f UnitV (fun _ => Unit) (Tup.units as)).callsOk allowed exits) :
    ((Func.tailDup f cfg) UnitV (fun _ => Unit) (Tup.units as)).callsOk allowed exits :=
  Func.tailDupLoop_callsOk cfg cfg.maxIters hf hc

/-- `Fn.tailDup` preserves `Fn.Wf`. -/
theorem Fn.tailDup_wf {fn : Fn} (hf : fn.Wf) (cfg : TailDupConfig := {}) :
    (fn.tailDup cfg).Wf :=
  Func.tailDup_wf hf cfg

/-- `Fn.tailDup` refines `Func.spec`. -/
theorem Fn.tailDup_spec {fn : Fn} (hf : fn.Wf) (cfg : TailDupConfig := {})
    {Γ : Env} {xs : Tup Val fn.as} {m : Mem 64} {Q : Post fn.rs} {X : XPost}
    (h : Func.spec Γ fn.body xs m Q X) :
    Func.spec Γ (fn.tailDup cfg).body xs m Q X :=
  Func.tailDup_spec hf cfg h

/-- `Fn.tailDup` preserves `Fn.callsOk`. -/
theorem Fn.tailDup_callsOk {allowed : List SigEntry} {exits : List Sym}
    {fn : Fn} (hf : fn.Wf) (cfg : TailDupConfig := {})
    (hc : fn.callsOk allowed exits) :
    (fn.tailDup cfg).callsOk allowed exits :=
  Func.tailDup_callsOk hf cfg hc

end LeanQbe.T
