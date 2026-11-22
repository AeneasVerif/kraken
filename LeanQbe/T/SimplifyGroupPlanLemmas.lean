module

public import LeanQbe.T.SimplifyGroupPlan
public import LeanQbe.T.Wf
public import LeanQbe.T.WP
import LeanQbe.T.OptUtilLemmas
import LeanQbe.T.FlatLemmas

/-!
# Correctness Proofs for `SimplifyGroupPlan`

Proves relational well-formedness preservation and weakest-precondition refinement for the linear
plan-guided PHOAS join-group simplifier:

* `rewriteExpr_wf`, `Func.simplifyGroupWithPlan_wf`, `Func.simplifyGroupPlan_wf`
* `rewriteExpr_wp`, `Func.simplifyGroupWithPlan_spec`, `Func.simplifyGroupPlan_spec`

Zero `OuterWf`, zero `OptV`, and zero oracle correctness obligations: `validatePlan` alone ensures
no reachable `.jump` ever reaches `.dead`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T

namespace SgpImpl

/-! ## Relational well-formedness (`PlanLRel`, `rewriteExpr_wf`) -/

/-- Relational invariant pairing two `PlanL` labels across target contexts `(G', D')`. -/
inductive PlanLRel {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    (G' : Ctx V₁ V₂) (D' : Ctx L₁ L₂) :
    {ts : List Ty} → PlanL V₁ L₁ rs ts → PlanL V₂ L₂ rs ts → Prop
  | keep {ts : List Ty} {l₁ : L₁ ts} {l₂ : L₂ ts} :
      ⟨ts, l₁, l₂⟩ ∈ D' → PlanLRel G' D' (.keep l₁) (.keep l₂)
  | dead {ts : List Ty} :
      PlanLRel G' D' (ts := ts) .dead .dead
  | splice {ts : List Ty}
      {b₁ : Tup (Arg V₁) ts → Expr V₁ L₁ rs}
      {b₂ : Tup (Arg V₂) ts → Expr V₂ L₂ rs} :
      (∀ {G'' D''}, (∀ p ∈ G', p ∈ G'') → (∀ p ∈ D', p ∈ D'') →
        ∀ (a₁ : Tup (Arg V₁) ts) (a₂ : Tup (Arg V₂) ts),
          TRel (ArgRel G'') a₁ a₂ → Wf G'' D'' (b₁ a₁) (b₂ a₂)) →
      PlanLRel G' D' (.splice b₁) (.splice b₂)

theorem PlanLRel.weaken {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G₁ G₂ : Ctx V₁ V₂} {D₁ D₂ : Ctx L₁ L₂}
    (hG : ∀ p ∈ G₁, p ∈ G₂) (hD : ∀ p ∈ D₁, p ∈ D₂)
    {ts : List Ty} {l₁ : PlanL V₁ L₁ rs ts} {l₂ : PlanL V₂ L₂ rs ts} :
    PlanLRel G₁ D₁ l₁ l₂ → PlanLRel G₂ D₂ l₁ l₂
  | .keep h => .keep (hD _ h)
  | .dead => .dead
  | .splice hb =>
    .splice fun hG' hD' => hb (fun _ hp => hG' _ (hG _ hp)) (fun _ hp => hD' _ (hD _ hp))

def PlanDRel {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    (G' : Ctx V₁ V₂) (D' : Ctx L₁ L₂)
    (D : Ctx (PlanL V₁ L₁ rs) (PlanL V₂ L₂ rs)) : Prop :=
  ∀ p ∈ D, PlanLRel G' D' p.2.1 p.2.2

theorem PlanDRel.weaken {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G₁ G₂ : Ctx V₁ V₂} {D₁ D₂ : Ctx L₁ L₂}
    {D : Ctx (PlanL V₁ L₁ rs) (PlanL V₂ L₂ rs)}
    (hG : ∀ p ∈ G₁, p ∈ G₂) (hD : ∀ p ∈ D₁, p ∈ D₂)
    (h : PlanDRel G₁ D₁ D) : PlanDRel G₂ D₂ D :=
  fun p hp => (h p hp).weaken hG hD

theorem PlanDRel.append {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G' : Ctx V₁ V₂} {D' : Ctx L₁ L₂}
    {H D : Ctx (PlanL V₁ L₁ rs) (PlanL V₂ L₂ rs)}
    (hH : PlanDRel G' D' H) (hD : PlanDRel G' D' D) : PlanDRel G' D' (H ++ D) := fun p hp =>
  (List.mem_append.1 hp).elim (hH p) (hD p)

theorem deadTup_rel {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G' : Ctx V₁ V₂} {D' : Ctx L₁ L₂} :
    (sig : List (List Ty)) →
    PlanDRel G' D' (Tup.zip (deadTup (V := V₁) (L := L₁) (rs := rs) sig)
      (deadTup (V := V₂) (L := L₂) (rs := rs) sig))
  | [], _, hp => nomatch hp
  | _ :: sig, _, .head _ => .dead
  | _ :: sig, p, .tail _ hp => deadTup_rel sig p hp

theorem expandKeepLabels_rel {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G' : Ctx V₁ V₂} {D' : Ctx L₁ L₂} :
    (ks : List Bool) → (sig : List (List Ty)) →
    (Js₁ : Tup L₁ (filterSig ks sig)) → (Js₂ : Tup L₂ (filterSig ks sig)) →
    PlanDRel G' (Tup.zip Js₁ Js₂ ++ D')
      (Tup.zip (expandKeepLabels (V := V₁) (rs := rs) ks sig Js₁)
        (expandKeepLabels (V := V₂) (rs := rs) ks sig Js₂))
  | _, [], (), (), _, hp => nomatch hp
  | [], _ :: sig, (), (), p, hp => by
    dsimp only [expandKeepLabels, Tup.zip] at hp
    cases hp with
    | head => exact .dead
    | tail _ hp => exact deadTup_rel sig p hp
  | true :: ks, _ :: sig, (j₁, js₁), (j₂, js₂), p, hp => by
    dsimp only [expandKeepLabels, Tup.zip] at hp ⊢
    cases hp with
    | head => exact .keep List.mem_cons_self
    | tail _ hp =>
      exact (expandKeepLabels_rel ks sig js₁ js₂ p hp).weaken (fun _ h => h)
        (fun _ h => List.mem_cons_of_mem _ h)
  | false :: ks, _ :: sig, js₁, js₂, p, hp => by
    dsimp only [expandKeepLabels, Tup.zip] at hp
    cases hp with
    | head => exact .dead
    | tail _ hp => exact expandKeepLabels_rel ks sig js₁ js₂ p hp

theorem rewriteSpliceLabels_rel {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G' : Ctx V₁ V₂} {D' : Ctx L₁ L₂} :
    (idx : Nat) → (pbs : SimpPlanB) → {sig : List (List Ty)} →
    {bs₁ : Blocks (Arg V₁) (PlanL V₁ L₁ rs) rs sig} →
    {bs₂ : Blocks (Arg V₂) (PlanL V₂ L₂ rs) rs sig} →
    (∀ {ts} (i : Member ts sig) (pb : SimpPlan) {G'' D''}
      (a₁ : Tup (Arg V₁) ts) (a₂ : Tup (Arg V₂) ts),
      (∀ p ∈ G', p ∈ G'') → (∀ p ∈ D', p ∈ D'') → TRel (ArgRel G'') a₁ a₂ →
      Wf G'' D'' (rewriteExpr pb (bs₁.get i a₁)) (rewriteExpr pb (bs₂.get i a₂))) →
    PlanDRel G' D'
      (Tup.zip (rewriteSpliceLabels idx pbs bs₁) (rewriteSpliceLabels idx pbs bs₂))
  | _, _, [], .nil, .nil, _, _, hp => nomatch hp
  | 0, .cons pb _, _ :: sig, .cons _ _, .cons _ _, hb, p, hp => by
    dsimp only [rewriteSpliceLabels, Tup.zip] at hp
    cases hp with
    | head => exact .splice fun hG hD a₁ a₂ ha => hb .here pb a₁ a₂ hG hD ha
    | tail _ hp => exact deadTup_rel sig p hp
  | idx + 1, .cons _ pbs, _ :: _, .cons _ bs₁, .cons _ bs₂, hb, p, hp => by
    dsimp only [rewriteSpliceLabels, Tup.zip] at hp
    cases hp with
    | head => exact .dead
    | tail _ hp => exact rewriteSpliceLabels_rel idx pbs (fun i => hb (.there i)) p hp
  | idx, .nil, _ :: sig, .cons _ _, .cons _ _, _, p, hp => by
    cases idx <;> (dsimp only [rewriteSpliceLabels, Tup.zip] at hp; cases hp with
      | head => exact .dead | tail _ hp => exact deadTup_rel sig p hp)

theorem rewriteFilteredBlocks_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G' : Ctx V₁ V₂} {D' : Ctx L₁ L₂} :
    (ks : List Bool) → (pbs : SimpPlanB) → {sig : List (List Ty)} →
    {bs₁ : Blocks (Arg V₁) (PlanL V₁ L₁ rs) rs sig} →
    {bs₂ : Blocks (Arg V₂) (PlanL V₂ L₂ rs) rs sig} →
    (∀ {ts} (i : Member ts sig) (pb : SimpPlan) (xs₁ : Tup V₁ ts) (xs₂ : Tup V₂ ts),
      Wf (Tup.zip xs₁ xs₂ ++ G') D'
        (rewriteExpr pb (bs₁.get i (toArgTup xs₁)))
        (rewriteExpr pb (bs₂.get i (toArgTup xs₂)))) →
    WfB G' D' (rewriteFilteredBlocks ks pbs bs₁) (rewriteFilteredBlocks ks pbs bs₂)
  | [], _, [], .nil, .nil, _ => .nil
  | _ :: _, _, [], .nil, .nil, _ => .nil
  | [], _, _ :: _, .cons _ _, .cons _ _, _ => .nil
  | true :: ks, .cons pb pbs, _ :: _, .cons _ _, .cons _ _, hb =>
    .cons (fun xs₁ xs₂ => hb .here pb xs₁ xs₂)
      (rewriteFilteredBlocks_wf ks pbs fun i => hb (.there i))
  | false :: ks, .cons _ pbs, _ :: _, .cons _ _, .cons _ _, hb =>
    rewriteFilteredBlocks_wf ks pbs fun i => hb (.there i)
  | true :: ks, .nil, _ :: _, .cons _ _, .cons _ _, hb =>
    .cons (fun _ _ => .hlt) (rewriteFilteredBlocks_wf ks .nil fun i => hb (.there i))
  | false :: ks, .nil, _ :: _, .cons _ _, .cons _ _, hb =>
    rewriteFilteredBlocks_wf ks .nil fun i => hb (.there i)

/-- `rewriteExpr` preserves `Wf` for every `SimpPlan`. -/
theorem rewriteExpr_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx (Arg V₁) (Arg V₂)} {D : Ctx (PlanL V₁ L₁ rs) (PlanL V₂ L₂ rs)}
    {e₁ : Expr (Arg V₁) (PlanL V₁ L₁ rs) rs} {e₂ : Expr (Arg V₂) (PlanL V₂ L₂ rs) rs}
    (hwf : Wf G D e₁ e₂) :
    ∀ {G' : Ctx V₁ V₂} {D' : Ctx L₁ L₂} (plan : SimpPlan),
      (∀ p ∈ G, ArgRel G' p.1 p.2.1 p.2.2) → PlanDRel G' D' D →
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
      | splice hb =>
        exact hb (fun _ h => h) (fun _ h => h) _ _ (TRel.flattenArgs hG hargs)
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
    | group act pbs pk =>
      cases act with
      | unwrap =>
        exact ihk (deadTup sig) (deadTup sig) pk hG ((deadTup_rel sig).append hD)
      | splice idx =>
        have hrel := rewriteSpliceLabels_rel (G' := G') (D' := D') idx pbs
          (bs₁ := b₁ (deadTup sig)) (bs₂ := b₂ (deadTup sig))
          fun {_} i pb {G'' D''} a₁ a₂ hsubG hsubD ha =>
            ihb (deadTup sig) (deadTup sig) i a₁ a₂ pb
              (ctx_argRel_append_same (mem_zip_argRel ha) fun p hp => (hG p hp).weaken hsubG)
              ((deadTup_rel sig).append (hD.weaken hsubG hsubD))
        exact ihk _ _ pk hG (hrel.append hD)
      | filter keep =>
        refine .group (fun Js₁ Js₂ => ?_) (fun Js₁ Js₂ => ?_)
        · have hD'' : PlanDRel G' (Tup.zip Js₁ Js₂ ++ D')
              (Tup.zip (expandKeepLabels keep sig Js₁) (expandKeepLabels keep sig Js₂) ++ D) :=
            (expandKeepLabels_rel keep sig Js₁ Js₂).append
              (hD.weaken (fun _ h => h) (fun _ h => List.mem_append_right _ h))
          exact rewriteFilteredBlocks_wf keep pbs fun i pb xs₁ xs₂ =>
            ihb _ _ i (toArgTup xs₁) (toArgTup xs₂) pb
              (ctx_argRel_append (mem_zip_toArgTup xs₁ xs₂) hG)
              (hD''.weaken (fun _ h => List.mem_append_right _ h) (fun _ h => h))
        · exact ihk _ _ pk hG
            ((expandKeepLabels_rel keep sig Js₁ Js₂).append
              (hD.weaken (fun _ h => h) (fun _ h => List.mem_append_right _ h)))
    | _ => exact .hlt

/-! ## Weakest-precondition refinement (`ValidDk`, `PlanWpD`, `rewriteExpr_wp`) -/

/-- Whether a `PlanL` label is live (not `.dead`). -/
def PlanL.isLive {V : Ty → Type} {L : List Ty → Type} {rs ts : List Ty} :
    PlanL V L rs ts → Bool
  | .keep _ => true
  | .splice _ => true
  | .dead => false

/-- Every `true` label in `Dk` corresponds to a live (non-`.dead`) `PlanL` label. -/
def ValidDk {rs : List Ty} (Dk : Ctx BoolL (PlanL Val Cont rs)) : Prop :=
  ∀ p ∈ Dk, p.2.1 = true → p.2.2.isLive = true

theorem ValidDk.append {rs : List Ty} {H Dk : Ctx BoolL (PlanL Val Cont rs)}
    (hH : ValidDk H) (hD : ValidDk Dk) : ValidDk (H ++ Dk) := fun p hp =>
  (List.mem_append.1 hp).elim (hH p) (hD p)

/-- Weakest-precondition invariant relating `PlanL Val Cont rs` labels to source `Cont`s. -/
def PlanWpD (Γ : Env) {rs : List Ty} (Q : Post rs) (X : XPost)
    (D : Ctx (PlanL Val Cont rs) Cont) : Prop :=
  ∀ p ∈ D, match p.2.1 with
    | .keep J => J = p.2.2
    | .dead => True
    | .splice b => ∀ (args : Tup (Arg Val) p.1) (m : Mem 64),
        p.2.2 (vals args) m → wp Γ Q X (b args) m

theorem PlanWpD.append {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {H D : Ctx (PlanL Val Cont rs) Cont}
    (hH : PlanWpD Γ Q X H) (hD : PlanWpD Γ Q X D) : PlanWpD Γ Q X (H ++ D) := fun p hp =>
  (List.mem_append.1 hp).elim (hH p) (hD p)

def tupTrue : (sig : List (List Ty)) → Tup Cont sig
  | [] => ()
  | _ :: sig => (fun _ _ => True, tupTrue sig)

theorem pureTrue_closed (Γ : Env) {rs : List Ty} (Q : Post rs) (X : XPost) :
    {sig : List (List Ty)} → (bs : Blocks Val Cont rs sig) → Closed Γ Q X bs (tupTrue sig)
  | [], .nil => trivial
  | _ :: _, .cons _ bs => ⟨fun _ _ _ => trivial, pureTrue_closed Γ Q X bs⟩

theorem validDk_allFalse_dead {rs : List Ty} :
    (sig : List (List Ty)) →
    ValidDk (Tup.zip (allFalse sig) (deadTup (V := Val) (L := Cont) (rs := rs) sig))
  | [], _, hp, _ => nomatch hp
  | _ :: _, _, .head _, h => by cases h
  | _ :: sig, p, .tail _ hp, h => validDk_allFalse_dead sig p hp h

theorem planWpD_dead (Γ : Env) {rs : List Ty} (Q : Post rs) (X : XPost) :
    (sig : List (List Ty)) → (Js : Tup Cont sig) →
    PlanWpD Γ Q X (Tup.zip (deadTup (V := Val) (L := Cont) (rs := rs) sig) Js)
  | [], (), _, hp => nomatch hp
  | _ :: _, (_, _), _, .head _ => trivial
  | _ :: sig, (_, Js), p, .tail _ hp => planWpD_dead Γ Q X sig Js p hp

/-- Source continuation tuple used for `Closed` in the `.splice idx` case. -/
def spliceSrcTup (Γ : Env) {rs : List Ty} (Q : Post rs) (X : XPost)
    (idx : Nat) (pbs : SimpPlanB) :
    {sig : List (List Ty)} → Blocks (Arg Val) (PlanL Val Cont rs) rs sig → Tup Cont sig
  | [], .nil => ()
  | ts :: sig, .cons b bs =>
    match idx, pbs with
    | 0, .cons pb _ =>
      (fun vs m => ∀ (args : Tup (Arg Val) ts), vals args = vs →
        wp Γ Q X (rewriteExpr pb (b args)) m,
       tupTrue sig)
    | idx' + 1, .cons _ pbs' =>
      (fun _ _ => True, spliceSrcTup Γ Q X idx' pbs' bs)
    | _, .nil => (fun _ _ => True, tupTrue sig)

theorem validDk_oneTrue_splice {rs : List Ty} :
    (idx : Nat) → (pbs : SimpPlanB) → {sig : List (List Ty)} →
    {bsk : Blocks UnitV BoolL rs sig} → {bs₁ : Blocks (Arg Val) (PlanL Val Cont rs) rs sig} →
    validateSpliceBlock idx pbs bsk = true →
    ValidDk (Tup.zip (oneTrue idx sig) (rewriteSpliceLabels idx pbs bs₁))
  | _, _, [], .nil, .nil, hval, _, _, _ => by simp [validateSpliceBlock] at hval
  | 0, .cons pb _, _ :: sig, .cons _ _, .cons _ _, _, p, hp, h => by
    dsimp only [oneTrue, rewriteSpliceLabels, Tup.zip] at hp
    cases hp with
    | head => rfl
    | tail _ hp => exact validDk_allFalse_dead sig p hp h
  | idx + 1, .cons _ pbs, _ :: _, .cons _ bsk, .cons _ bs₁, hval, p, hp, h => by
    change validateSpliceBlock idx pbs bsk = true at hval
    dsimp only [oneTrue, rewriteSpliceLabels, Tup.zip] at hp
    cases hp with
    | head => cases h
    | tail _ hp => exact validDk_oneTrue_splice idx pbs (bsk := bsk) (bs₁ := bs₁) hval p hp h
  | idx, .nil, _ :: _, .cons _ _, .cons _ _, hval, _, _, _ => by cases idx <;> cases hval

theorem planWpD_splice (Γ : Env) {rs : List Ty} (Q : Post rs) (X : XPost) :
    (idx : Nat) → (pbs : SimpPlanB) → {sig : List (List Ty)} →
    (bs₁ : Blocks (Arg Val) (PlanL Val Cont rs) rs sig) →
    PlanWpD Γ Q X
      (Tup.zip (rewriteSpliceLabels idx pbs bs₁) (spliceSrcTup Γ Q X idx pbs bs₁))
  | _, _, [], .nil, _, hp => nomatch hp
  | 0, .cons pb _, _ :: sig, .cons b _, p, hp => by
    dsimp only [rewriteSpliceLabels, spliceSrcTup, Tup.zip] at hp
    cases hp with
    | head => exact fun args m h => h args rfl
    | tail _ hp => exact planWpD_dead Γ Q X sig (tupTrue sig) p hp
  | idx + 1, .cons _ pbs, _ :: _, .cons _ bs₁, p, hp => by
    dsimp only [rewriteSpliceLabels, spliceSrcTup, Tup.zip] at hp
    cases hp with
    | head => trivial
    | tail _ hp => exact planWpD_splice Γ Q X idx pbs bs₁ p hp
  | idx, .nil, _ :: sig, .cons _ _, p, hp => by
    cases idx <;> (dsimp only [rewriteSpliceLabels, spliceSrcTup, Tup.zip] at hp; cases hp with
      | head => trivial | tail _ hp => exact planWpD_dead Γ Q X sig (tupTrue sig) p hp)

theorem spliceSrcTup_closed (Γ : Env) {rs : List Ty} (Q : Post rs) (X : XPost) :
    (idx : Nat) → (pbs : SimpPlanB) → {sig : List (List Ty)} →
    (bsk : Blocks UnitV BoolL rs sig) →
    (bs₁ : Blocks (Arg Val) (PlanL Val Cont rs) rs sig) →
    (bs₂ : Blocks Val Cont rs sig) →
    validateSpliceBlock idx pbs bsk = true →
    (∀ {ts} (i : Member ts sig) (pb : SimpPlan) (args : Tup (Arg Val) ts) (xs : Tup Val ts),
      validatePlan pb (bsk.get i (Tup.units ts)) = true → vals args = xs →
      ∀ m, wp Γ Q X (bs₂.get i xs) m → wp Γ Q X (rewriteExpr pb (bs₁.get i args)) m) →
    Closed Γ Q X bs₂ (spliceSrcTup Γ Q X idx pbs bs₁)
  | _, _, [], .nil, .nil, .nil, _, _ => trivial
  | 0, .cons pb _, _ :: _, .cons _ _, .cons _ _, .cons _ bs₂, hval, hb => by
    change validatePlan pb _ = true at hval
    simp only [spliceSrcTup, Closed]
    exact ⟨fun xs m hw args hargs => hb .here pb args xs hval hargs m hw,
      pureTrue_closed Γ Q X bs₂⟩
  | idx + 1, .cons _ pbs, _ :: _, .cons _ bsk, .cons _ bs₁, .cons _ bs₂, hval, hb => by
    change validateSpliceBlock idx pbs bsk = true at hval
    simp only [spliceSrcTup, Closed]
    exact ⟨fun _ _ _ => trivial,
      spliceSrcTup_closed Γ Q X idx pbs bsk bs₁ bs₂ hval fun i => hb (.there i)⟩
  | idx, .nil, _ :: _, .cons _ _, .cons _ _, .cons _ _, hval, _ => by
    cases idx <;> cases hval

/-- Expand target `Js : Tup Cont (filterSig ks sig)` to source `Tup Cont sig`. -/
def expandSrcConts : (ks : List Bool) → (sig : List (List Ty)) →
    Tup Cont (filterSig ks sig) → Tup Cont sig
  | _, [], () => ()
  | [], _ :: sig, () => (fun _ _ => True, tupTrue sig)
  | true :: ks, _ :: sig, (J, Js) => (J, expandSrcConts ks sig Js)
  | false :: ks, _ :: sig, Js => (fun _ _ => True, expandSrcConts ks sig Js)

theorem validDk_filter {rs : List Ty} :
    (ks : List Bool) → (sig : List (List Ty)) → (Js : Tup Cont (filterSig ks sig)) →
    ValidDk (Tup.zip (boolTup ks sig) (expandKeepLabels (V := Val) (rs := rs) ks sig Js))
  | _, [], (), _, hp, _ => nomatch hp
  | [], _ :: sig, (), p, hp, h => by
    dsimp only [boolTup, expandKeepLabels, Tup.zip] at hp
    cases hp with
    | head => cases h
    | tail _ hp => exact validDk_allFalse_dead sig p hp h
  | true :: ks, _ :: sig, (J, Js), p, hp, h => by
    dsimp only [boolTup, expandKeepLabels, Tup.zip] at hp
    cases hp with
    | head => rfl
    | tail _ hp => exact validDk_filter ks sig Js p hp h
  | false :: ks, _ :: sig, Js, p, hp, h => by
    dsimp only [boolTup, expandKeepLabels, Tup.zip] at hp
    cases hp with
    | head => cases h
    | tail _ hp => exact validDk_filter ks sig Js p hp h

theorem planWpD_filter (Γ : Env) {rs : List Ty} (Q : Post rs) (X : XPost) :
    (ks : List Bool) → (sig : List (List Ty)) → (Js : Tup Cont (filterSig ks sig)) →
    PlanWpD Γ Q X
      (Tup.zip (expandKeepLabels (V := Val) (rs := rs) ks sig Js) (expandSrcConts ks sig Js))
  | _, [], (), _, hp => nomatch hp
  | [], _ :: sig, (), p, hp => by
    dsimp only [expandKeepLabels, expandSrcConts, Tup.zip] at hp
    cases hp with
    | head => trivial
    | tail _ hp => exact planWpD_dead Γ Q X sig (tupTrue sig) p hp
  | true :: ks, _ :: sig, (_, Js), p, hp => by
    dsimp only [expandKeepLabels, expandSrcConts, Tup.zip] at hp
    cases hp with
    | head => rfl
    | tail _ hp => exact planWpD_filter Γ Q X ks sig Js p hp
  | false :: ks, _ :: sig, Js, p, hp => by
    dsimp only [expandKeepLabels, expandSrcConts, Tup.zip] at hp
    cases hp with
    | head => trivial
    | tail _ hp => exact planWpD_filter Γ Q X ks sig Js p hp

theorem expandSrcConts_closed (Γ : Env) {rs : List Ty} (Q : Post rs) (X : XPost) :
    (ks : List Bool) → (pbs : SimpPlanB) → {sig : List (List Ty)} →
    (bsk : Blocks UnitV BoolL rs sig) →
    (bs₁ : Blocks (Arg Val) (PlanL Val Cont rs) rs sig) →
    (bs₂ : Blocks Val Cont rs sig) →
    (Js : Tup Cont (filterSig ks sig)) →
    validateFilteredBlocks ks pbs bsk = true →
    Closed Γ Q X (rewriteFilteredBlocks ks pbs bs₁) Js →
    (∀ {ts} (i : Member ts sig) (pb : SimpPlan) (xs : Tup Val ts),
      validatePlan pb (bsk.get i (Tup.units ts)) = true →
      ∀ m, wp Γ Q X (bs₂.get i xs) m →
        wp Γ Q X (rewriteExpr pb (bs₁.get i (toArgTup xs))) m) →
    Closed Γ Q X bs₂ (expandSrcConts ks sig Js)
  | [], .nil, [], .nil, .nil, .nil, (), _, _, _ => trivial
  | true :: ks, .cons pb pbs, _ :: _, .cons _ bsk, .cons _ bs₁, .cons _ bs₂, (J, Js),
      hval, hcl, hb => by
    change (validatePlan pb _ && validateFilteredBlocks ks pbs bsk) = true at hval
    simp only [Bool.and_eq_true] at hval
    simp only [rewriteFilteredBlocks] at hcl
    simp only [expandSrcConts, Closed]
    exact ⟨fun xs m hw => hcl.1 xs m (hb .here pb xs hval.1 m hw),
      expandSrcConts_closed Γ Q X ks pbs bsk bs₁ bs₂ Js hval.2 hcl.2 fun i => hb (.there i)⟩
  | false :: ks, .cons _ pbs, _ :: _, .cons _ bsk, .cons _ bs₁, .cons _ bs₂, Js,
      hval, hcl, hb => by
    change validateFilteredBlocks ks pbs bsk = true at hval
    simp only [rewriteFilteredBlocks] at hcl
    simp only [expandSrcConts, Closed]
    exact ⟨fun _ _ _ => trivial,
      expandSrcConts_closed Γ Q X ks pbs bsk bs₁ bs₂ Js hval hcl fun i => hb (.there i)⟩
  | [], .cons _ _, [], .nil, .nil, .nil, (), hval, _, _ => by cases hval
  | _ :: _, pbs, [], .nil, .nil, .nil, (), hval, _, _ => by cases pbs <;> cases hval
  | [], pbs, _ :: _, .cons _ _, .cons _ _, .cons _ _, (), hval, _, _ => by cases pbs <;> cases hval
  | k :: _, .nil, _ :: _, .cons _ _, .cons _ _, .cons _ _, _, hval, _, _ => by
      cases k <;> cases hval

/-- `rewriteExpr` refines `wp` whenever `validatePlan` accepts the plan. -/
theorem rewriteExpr_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {G : Ctx (Arg Val) Val} {D : Ctx (PlanL Val Cont rs) Cont}
    {e₁ : Expr (Arg Val) (PlanL Val Cont rs) rs} {e₂ : Expr Val Cont rs}
    (hwf : Wf G D e₁ e₂) :
    ∀ {Gk : Ctx UnitV (Arg Val)} {Dk : Ctx BoolL (PlanL Val Cont rs)}
      {ek : Expr UnitV BoolL rs} (_hwk : Wf Gk Dk ek e₁)
      (plan : SimpPlan) (_hval : validatePlan plan ek = true),
      (∀ p ∈ G, p.2.1.val = p.2.2) →
      ValidDk Dk → PlanWpD Γ Q X D →
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
      have hlive : j₁.isLive = true := hDk _ hjk hval
      have hd := hD _ hj
      cases j₁ with
      | keep J =>
        dsimp only [rewriteExpr, wp] at hw2 ⊢
        dsimp only at hd
        rw [flattenArgs_vals hG hargs, hd]
        exact hw2
      | dead => dsimp only [PlanL.isLive] at hlive; cases hlive
      | splice body =>
        dsimp only [rewriteExpr, wp] at hw2 ⊢
        dsimp only at hd
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
    | group act pbs pk =>
      cases act with
      | unwrap =>
        dsimp only [validatePlan] at hval
        dsimp only [rewriteExpr]
        let Js₂ := tupTrue sig
        exact ihk (deadTup sig) Js₂ (hkk (allFalse sig) (deadTup sig)) pk hval hG
          ((validDk_allFalse_dead sig).append hDk)
          ((planWpD_dead Γ Q X sig Js₂).append hD)
          m (hw2 Js₂ (pureTrue_closed Γ Q X (b₂ Js₂)))
      | splice idx =>
        dsimp only [validatePlan] at hval; simp only [Bool.and_eq_true] at hval
        dsimp only [rewriteExpr]
        let Js₂ := spliceSrcTup Γ Q X idx pbs (b₁ (deadTup sig))
        have hcl₂ : Closed Γ Q X (b₂ Js₂) Js₂ :=
          spliceSrcTup_closed Γ Q X idx pbs (bk (allFalse sig)) (b₁ (deadTup sig)) (b₂ Js₂)
            hval.1 fun i pb args xs hvb hargs m' hw =>
              ihb (deadTup sig) Js₂ i args xs
                ((hbk (allFalse sig) (deadTup sig)).get i (Tup.units _) args) pb hvb
                (ctx_val_append (tup_zip_vals_val args xs hargs) hG)
                ((validDk_allFalse_dead sig).append hDk)
                ((planWpD_dead Γ Q X sig Js₂).append hD)
                m' hw
        exact ihk (rewriteSpliceLabels idx pbs (b₁ (deadTup sig))) Js₂
          (hkk (oneTrue idx sig) (rewriteSpliceLabels idx pbs (b₁ (deadTup sig)))) pk hval.2 hG
          ((validDk_oneTrue_splice idx pbs hval.1).append hDk)
          ((planWpD_splice Γ Q X idx pbs (b₁ (deadTup sig))).append hD)
          m (hw2 Js₂ hcl₂)
      | filter keep =>
        dsimp only [validatePlan] at hval; simp only [Bool.and_eq_true] at hval
        dsimp only [rewriteExpr, wp]
        intro Js_out hcl_out
        let ls := expandKeepLabels (V := Val) (rs := rs) keep sig Js_out
        let Js₂ := expandSrcConts keep sig Js_out
        have hDk' := (validDk_filter keep sig Js_out).append hDk
        have hD' := (planWpD_filter Γ Q X keep sig Js_out).append hD
        have hcl₂ : Closed Γ Q X (b₂ Js₂) Js₂ :=
          expandSrcConts_closed Γ Q X keep pbs (bk (boolTup keep sig)) (b₁ ls) (b₂ Js₂) Js_out
            hval.1 hcl_out fun i pb xs hvb m' hw =>
              ihb ls Js₂ i (toArgTup xs) xs
                ((hbk (boolTup keep sig) ls).get i (Tup.units _) (toArgTup xs)) pb hvb
                (ctx_val_append (toArgTup_zip_val xs) hG) hDk' hD' m' hw
        exact ihk ls Js₂ (hkk (boolTup keep sig) ls) pk hval.2 hG hDk' hD' m (hw2 Js₂ hcl₂)
    | _ => dsimp only [validatePlan] at hval; cases hval

end SgpImpl

open SgpImpl

/-! ## Top-level `Func` well-formedness and specification theorems -/

/-- `Func.simplifyGroupWithPlan` preserves relational well-formedness `Func.Wf`. -/
theorem Func.simplifyGroupWithPlan_wf {as rs : List Ty} (plan : SimpPlan) {f : Func as rs}
    (hf : f.Wf) : (Func.simplifyGroupWithPlan plan f).Wf := by
  dsimp only [Func.simplifyGroupWithPlan]
  split
  · intro V₁ V₂ L₁ L₂ xs₁ xs₂
    exact rewriteExpr_wf
      (hf (Arg V₁) (Arg V₂) (PlanL V₁ L₁ rs) (PlanL V₂ L₂ rs) (toArgTup xs₁) (toArgTup xs₂))
      plan (mem_zip_toArgTup xs₁ xs₂) (fun _ hp => nomatch hp)
  · exact hf

/-- `Func.simplifyGroupWithPlan` refines function contracts for any well-formed `f`. -/
theorem Func.simplifyGroupWithPlan_spec {as rs : List Ty} (plan : SimpPlan) {f : Func as rs}
    (hf : f.Wf) {Γ : Env} {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Func.spec Γ f xs m Q X) : Func.spec Γ (Func.simplifyGroupWithPlan plan f) xs m Q X := by
  dsimp only [Func.simplifyGroupWithPlan]
  split
  · rename_i hval
    have hwf := hf (Arg Val) Val (PlanL Val Cont rs) Cont (toArgTup xs) xs
    have hwk := hf UnitV (Arg Val) BoolL (PlanL Val Cont rs) (Tup.units as) (toArgTup xs)
    exact rewriteExpr_wp hwf hwk plan hval (toArgTup_zip_val xs)
      (fun _ hp => nomatch hp) (fun _ hp => nomatch hp) m h
  · exact h

/-- `Func.simplifyGroupPlan` preserves relational well-formedness `Func.Wf`. -/
theorem Func.simplifyGroupPlan_wf {as rs : List Ty} {f : Func as rs} (_hf : f.Wf) :
    (Func.simplifyGroupPlan f).Wf := by
  dsimp only [Func.simplifyGroupPlan]
  split
  · exact Func.simplifyGroupWithPlan_wf _ (Func.renorm_wf f)
  · exact Func.renorm_wf f

/-- `Func.simplifyGroupPlan` refines function contracts for any well-formed `f`. -/
theorem Func.simplifyGroupPlan_spec {as rs : List Ty} {f : Func as rs} (hf : f.Wf) {Γ : Env}
    {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Func.spec Γ f xs m Q X) : Func.spec Γ (Func.simplifyGroupPlan f) xs m Q X := by
  dsimp only [Func.simplifyGroupPlan]
  split
  · exact Func.simplifyGroupWithPlan_spec _ (Func.renorm_wf f) (Func.renorm_spec hf h)
  · exact Func.renorm_spec hf h

end LeanQbe.T
