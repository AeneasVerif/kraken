module

public import LeanQbe.T.IfOptLemmas0
import LeanQbe.T.OpsLemmas
import LeanQbe.T.PassEnvKit

/-!
# Correctness of `ifOpt` — Part 1 (Hoist `Wf`, `TagD`, and Diamond `WP`)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T

open IfOptImpl

namespace IfOptImpl

section WfSelect
variable {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type}

theorem hoistArm_jump_eq {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (ts : List Ty) (next : Nat) (j : JLabel L ts) (args : Tup (Arg (IVal V)) ts)
    (cont : Nat → Tup (Arg (IVal V)) ts → Expr V L rs) :
    hoistArm ts .jump next (.jump j args) cont = cont next args := by
  dsimp only [hoistArm]
  cases listTyDecEq ts ts with
  | isFalse hne => exact absurd rfl hne
  | isTrue _ => rfl

theorem hoistArm_ret_eq {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (next : Nat) (vs : Tup (Arg (IVal V)) rs)
    (cont : Nat → Tup (Arg (IVal V)) rs → Expr V L rs) :
    hoistArm rs .ret next (.ret vs) cont = cont next vs := by
  dsimp only [hoistArm]
  cases listTyDecEq rs rs with
  | isFalse hne => exact absurd rfl hne
  | isTrue _ => rfl

theorem hoistArm_wf {rs : List Ty} (jTs : List Ty) {D' : Ctx L₁ L₂} :
    ∀ (p : ArmPlan) (next : Nat) {G : Ctx (IVal V₁) (IVal V₂)} {G' : Ctx V₁ V₂}
      {D : Ctx (JLabel L₁) (JLabel L₂)}
      {e₁ : Expr (IVal V₁) (JLabel L₁) rs} {e₂ : Expr (IVal V₂) (JLabel L₂) rs},
    Wf G D e₁ e₂ → HasArmShape jTs p e₁ → IRelG G' G →
    {cont₁ : Nat → Tup (Arg (IVal V₁)) jTs → Expr V₁ L₁ rs} →
    {cont₂ : Nat → Tup (Arg (IVal V₂)) jTs → Expr V₂ L₂ rs} →
    (∀ G'' next' args₁ args₂, (∀ q ∈ G', q ∈ G'') → IRelG G'' G →
      TRel (fun _ => IArgRel G'') args₁ args₂ →
      Wf G'' D' (cont₁ next' args₁) (cont₂ next' args₂)) →
    Wf G' D' (hoistArm jTs p next e₁ cont₁) (hoistArm jTs p next e₂ cont₂)
  | .jump, next, G, G', D, _, _, hwf, hsh, hG, cont₁, cont₂, hcont => by
    cases hwf with
    | @jump _ _ ts j₁ j₂ args₁ args₂ _ hargs =>
      dsimp only [HasArmShape] at hsh
      subst hsh
      rw [hoistArm_jump_eq, hoistArm_jump_eq]
      exact hcont G' next args₁ args₂ (fun _ h => h) hG (trel_iargRel hG hargs)
    | let_ _ _ | load _ _ _ | store _ _ _ | call _ _ _ | jnz _ _ _ | ret _ | exit _ _ | hlt
    | group _ _ => exact False.elim hsh
  | .ret, next, G, G', D, _, _, hwf, hsh, hG, cont₁, cont₂, hcont => by
    cases hwf with
    | ret hvs =>
      dsimp only [HasArmShape] at hsh
      subst hsh
      rw [hoistArm_ret_eq, hoistArm_ret_eq]
      exact hcont G' next _ _ (fun _ h => h) hG (trel_iargRel hG hvs)
    | let_ _ _ | load _ _ _ | store _ _ _ | call _ _ _ | jnz _ _ _ | jump _ _ | exit _ _ | hlt
    | group _ _ => exact False.elim hsh
  | .let_ rest, next, G, G', D, e₁, e₂, hwf, hsh, hG, cont₁, cont₂, hcont => by
    cases hwf with
    | let_ hop hk =>
      cases hop with
      | mk code hargs =>
        dsimp only [hoistArm]
        refine .let_ (.mk code (trel_iout hG hargs)) fun xs₁ xs₂ => ?_
        have hG'' : IRelG (Tup.zip xs₁ xs₂ ++ G')
            (Tup.zip (freshIVals _ xs₁ next) (freshIVals _ xs₂ next) ++ G) :=
          IRelG.freshIVals hG xs₁ xs₂ next
        refine hoistArm_wf jTs rest (next + _) (hk (freshIVals _ xs₁ next) (freshIVals _ xs₂ next))
          (hsh (freshIVals _ xs₁ next)) hG'' fun G₃ next' a₁ a₂ hsub hrel3 ha => ?_
        refine hcont G₃ next' a₁ a₂ (fun p hp => hsub p (List.mem_append_right _ hp)) ?_ ha
        exact fun p hp => hrel3 p (List.mem_append_right _ hp)
    | load _ _ _ | store _ _ _ | call _ _ _ | jnz _ _ _ | jump _ _ | ret _ | exit _ _ | hlt
    | group _ _ => exact False.elim hsh
  | .jnz pT pE, next, G, G', D, _, _, hwf, hsh, hG, cont₁, cont₂, hcont => by
    cases hwf with
    | jnz hc ht he =>
      rcases hsh with ⟨hshT, hshE⟩
      dsimp only [hoistArm]
      refine hoistArm_wf jTs pT next ht hshT hG fun G₁ next₁ argsT₁ argsT₂ hsub₁ hG₁ hargsT => ?_
      refine hoistArm_wf jTs pE next₁ he hshE hG₁ fun G₂ next₂ argsE₁ argsE₂ hsub₂ hG₂ hargsE => ?_
      have hc₂ := (argRel_iout hG hc).weaken (fun p hp => hsub₂ p (hsub₁ p hp))
      have hargsT₂ := TRel.mono (fun _ _ _ h => iargRel_weaken hsub₂ h) hargsT
      refine emitSelectTupIVal_wf hc₂ jTs next₂ hargsT₂ hargsE
        fun G₃ next₃ sel₁ sel₂ hsub₃ hsel => ?_
      refine hcont G₃ next₃ sel₁ sel₂ ?_ (hG₂.weaken hsub₃) hsel
      exact fun p hp => hsub₃ p (hsub₂ p (hsub₁ p hp))
    | let_ _ _ | load _ _ _ | store _ _ _ | call _ _ _ | jump _ _ | ret _ | exit _ _ | hlt
    | group _ _ => exact False.elim hsh

theorem hoistJnzArms_wf {rs : List Ty} (jTs : List Ty) {D' : Ctx L₁ L₂}
    (pT pE : ArmPlan) (next : Nat) {G : Ctx (IVal V₁) (IVal V₂)} {G' : Ctx V₁ V₂}
    {D : Ctx (JLabel L₁) (JLabel L₂)}
    {c₁ : Arg (IVal V₁) .bool} {c₂ : Arg (IVal V₂) .bool}
    {t₁ e₁ : Expr (IVal V₁) (JLabel L₁) rs} {t₂ e₂ : Expr (IVal V₂) (JLabel L₂) rs}
    (hc : ArgRel G .bool c₁ c₂) (ht : Wf G D t₁ t₂) (he : Wf G D e₁ e₂)
    (hshT : HasArmShape jTs pT t₁) (hshE : HasArmShape jTs pE e₁) (hG : IRelG G' G)
    {fin₁ : Tup (Arg V₁) jTs → Expr V₁ L₁ rs} {fin₂ : Tup (Arg V₂) jTs → Expr V₂ L₂ rs}
    (hfin : ∀ G'' sel₁ sel₂, (∀ q ∈ G', q ∈ G'') → TRel (ArgRel G'') sel₁ sel₂ →
      Wf G'' D' (fin₁ sel₁) (fin₂ sel₂)) :
    Wf G' D' (hoistJnzArms jTs pT pE next c₁ t₁ e₁ fin₁)
             (hoistJnzArms jTs pT pE next c₂ t₂ e₂ fin₂) := by
  dsimp only [hoistJnzArms]
  refine hoistArm_wf jTs pT next ht hshT hG fun G₁ next₁ argsT₁ argsT₂ hsub₁ hG₁ hargsT => ?_
  refine hoistArm_wf jTs pE next₁ he hshE hG₁ fun G₂ next₂ argsE₁ argsE₂ hsub₂ hG₂ hargsE => ?_
  have hc₂ := (argRel_iout hG hc).weaken (fun p hp => hsub₂ p (hsub₁ p hp))
  have hargsT₂ := TRel.mono (fun _ _ _ h => iargRel_weaken hsub₂ h) hargsT
  refine emitSelectTup_wf hc₂ jTs next₂ hargsT₂ hargsE fun G₃ sel₁ sel₂ hsub₃ hsel => ?_
  exact hfin G₃ sel₁ sel₂ (fun p hp => hsub₃ p (hsub₂ p (hsub₁ p hp))) hsel

theorem hoistStoreTail_jump_eq {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (ts : List Ty) (next : Nat) (j : JLabel L ts) (args : Tup (Arg (IVal V)) ts)
    (cont : Nat → Tup (Arg (IVal V)) ts → Expr V L rs) :
    hoistStoreTail ts .jump next (.jump j args) cont = cont next args := by
  dsimp only [hoistStoreTail]
  cases h : listTyDecEq ts ts with
  | isTrue _ => rfl
  | isFalse hne => exact absurd rfl hne

theorem hoistStoreTail_ret_eq {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (next : Nat) (vs : Tup (Arg (IVal V)) rs)
    (cont : Nat → Tup (Arg (IVal V)) rs → Expr V L rs) :
    hoistStoreTail rs .ret next (.ret vs) cont = cont next vs := by
  dsimp only [hoistStoreTail]
  cases h : listTyDecEq rs rs with
  | isTrue _ => rfl
  | isFalse hne => exact absurd rfl hne

theorem hoistStoreTail_wf {rs : List Ty} (jTs : List Ty) {D' : Ctx L₁ L₂} :
    ∀ (p : StoreTail) (next : Nat) {G : Ctx (IVal V₁) (IVal V₂)} {G' : Ctx V₁ V₂}
      {D : Ctx (JLabel L₁) (JLabel L₂)}
      {e₁ : Expr (IVal V₁) (JLabel L₁) rs} {e₂ : Expr (IVal V₂) (JLabel L₂) rs},
    Wf G D e₁ e₂ → HasStoreTailShape jTs p e₁ → IRelG G' G →
    {cont₁ : Nat → Tup (Arg (IVal V₁)) jTs → Expr V₁ L₁ rs} →
    {cont₂ : Nat → Tup (Arg (IVal V₂)) jTs → Expr V₂ L₂ rs} →
    (∀ G'' next' args₁ args₂, (∀ p ∈ G', p ∈ G'') → IRelG G'' G →
      TRel (fun _ => IArgRel G'') args₁ args₂ →
      Wf G'' D' (cont₁ next' args₁) (cont₂ next' args₂)) →
    Wf G' D' (hoistStoreTail jTs p next e₁ cont₁) (hoistStoreTail jTs p next e₂ cont₂)
  | .jump, next, _, G', _, _, _, hwf, hsh, hG, cont₁, cont₂, hcont => by
    cases hwf with
    | @jump _ _ ts _ _ args₁ args₂ _ hargs =>
      cases hsh
      rw [hoistStoreTail_jump_eq, hoistStoreTail_jump_eq]
      exact hcont G' next args₁ args₂ (fun _ h => h) hG (trel_iargRel hG hargs)
    | let_ _ _ | load _ _ _ | store _ _ _ | call _ _ _ | jnz _ _ _ | ret _ | exit _ _ | hlt
    | group _ _ => exact False.elim hsh
  | .ret, next, _, G', _, _, _, hwf, hsh, hG, cont₁, cont₂, hcont => by
    cases hwf with
    | ret hvs =>
      cases hsh
      rw [hoistStoreTail_ret_eq, hoistStoreTail_ret_eq]
      exact hcont G' next _ _ (fun _ h => h) hG (trel_iargRel hG hvs)
    | let_ _ _ | load _ _ _ | store _ _ _ | call _ _ _ | jnz _ _ _ | jump _ _ | exit _ _ | hlt
    | group _ _ => exact False.elim hsh
  | .let_ rest, next, _, G', _, _, _, hwf, hsh, hG, cont₁, cont₂, hcont => by
    cases hwf with
    | let_ hop hk =>
      cases hop with
      | mk code hargs =>
        dsimp only [hoistStoreTail]
        refine .let_ (.mk code (trel_iout hG hargs)) fun xs₁ xs₂ => ?_
        refine hoistStoreTail_wf jTs rest (next + _)
          (hk (freshIVals _ xs₁ next) (freshIVals _ xs₂ next))
          (hsh (freshIVals _ xs₁ next)) (hG.freshIVals xs₁ xs₂ next)
          fun G'' next' a₁ a₂ hsub hG'' ha => ?_
        have hsub' : ∀ p ∈ G', p ∈ G'' := fun p hp =>
          hsub p (List.mem_append_right _ hp)
        have hG' : IRelG G'' _ := fun p hp => hG'' p (List.mem_append_right _ hp)
        exact hcont G'' next' a₁ a₂ hsub' hG' ha
    | load _ _ _ | store _ _ _ | call _ _ _ | jnz _ _ _ | jump _ _ | ret _ | exit _ _ | hlt
    | group _ _ => exact False.elim hsh

theorem hoistStoreStep_wf {rs : List Ty} (jTs : List Ty) (st : Ty) {D' : Ctx L₁ L₂} :
    ∀ (p : StoreStep) (next : Nat) {l₁ : List ((t : Ty) × IVal V₁ t)}
      {l₂ : List ((t : Ty) × IVal V₂ t)}
      {G : Ctx (IVal V₁) (IVal V₂)} {G' : Ctx V₁ V₂} {D : Ctx (JLabel L₁) (JLabel L₂)}
      {e₁ : Expr (IVal V₁) (JLabel L₁) rs} {e₂ : Expr (IVal V₂) (JLabel L₂) rs},
    Wf G D e₁ e₂ → HasStoreStepShape jTs st p e₁ → IRelG G' G → SLoadsRel G' l₁ l₂ →
    {cont₁ : Nat → List ((t : Ty) × IVal V₁ t) → Arg (IVal V₁) st → Arg (IVal V₁) i64 →
      Tup (Arg (IVal V₁)) jTs → Expr V₁ L₁ rs} →
    {cont₂ : Nat → List ((t : Ty) × IVal V₂ t) → Arg (IVal V₂) st → Arg (IVal V₂) i64 →
      Tup (Arg (IVal V₂)) jTs → Expr V₂ L₂ rs} →
    (∀ G'' next' l₁' l₂' v₁ v₂ a₁ a₂ args₁ args₂,
      (∀ p ∈ G', p ∈ G'') → IRelG G'' G → SLoadsRel G'' l₁' l₂' →
      IArgRel G'' v₁ v₂ → IArgRel G'' a₁ a₂ → TRel (fun _ => IArgRel G'') args₁ args₂ →
      Wf G'' D' (cont₁ next' l₁' v₁ a₁ args₁) (cont₂ next' l₂' v₂ a₂ args₂)) →
    Wf G' D' (hoistStoreStep jTs st p next l₁ e₁ cont₁)
             (hoistStoreStep jTs st p next l₂ e₂ cont₂)
  | .let_ rest, next, l₁, l₂, _, G', _, _, _, hwf, hsh, hG, hL, cont₁, cont₂, hcont => by
    cases hwf with
    | let_ hop hk =>
      cases hop with
      | mk code hargs =>
        dsimp only [hoistStoreStep]
        refine .let_ (.mk code (trel_iout hG hargs)) fun xs₁ xs₂ => ?_
        have hsub0 : ∀ p ∈ G', p ∈ Tup.zip xs₁ xs₂ ++ G' :=
          fun _ hp => List.mem_append_right _ hp
        refine hoistStoreStep_wf jTs st rest (next + _)
          (hk (freshIVals _ xs₁ next) (freshIVals _ xs₂ next))
          (hsh (freshIVals _ xs₁ next)) (hG.freshIVals xs₁ xs₂ next) (hL.weaken hsub0)
          fun G'' next' l₁' l₂' v₁ v₂ a₁ a₂ args₁ args₂ hsub hG'' hL' hv ha hargs' => ?_
        exact hcont G'' next' l₁' l₂' v₁ v₂ a₁ a₂ args₁ args₂
          (fun p hp => hsub p (hsub0 p hp))
          (fun p hp => hG'' p (List.mem_append_right _ hp)) hL' hv ha hargs'
    | load _ _ _ | store _ _ _ | call _ _ _ | jnz _ _ _ | jump _ _ | ret _ | exit _ _ | hlt
    | group _ _ => exact False.elim hsh
  | .loadEmit rest, next, l₁, l₂, _, G', _, _, _, hwf, hsh, hG, hL, cont₁, cont₂, hcont => by
    cases hwf with
    | load t ha hk =>
      dsimp only [hoistStoreStep]
      refine .load t (argRel_iout hG ha) fun v₁ v₂ => ?_
      have hsub0 : ∀ p ∈ G', p ∈ ⟨t, v₁, v₂⟩ :: G' := fun _ hp => List.mem_cons_of_mem _ hp
      have hiv : IValRel (⟨t, v₁, v₂⟩ :: G') (.var v₁, .var next) (.var v₂, .var next) :=
        ⟨.var List.mem_cons_self, rfl⟩
      have hL1 := (hL.weaken hsub0).append hiv
      refine hoistStoreStep_wf jTs st rest (next + 1)
        (hk (.var v₁, .var next) (.var v₂, .var next))
        (hsh (.var v₁, .var next)) (hG.freshOne v₁ v₂ next) hL1
        fun G'' next' l₁' l₂' rv₁ rv₂ ra₁ ra₂ args₁ args₂ hsub hG'' hL' hv' ha' hargs' => ?_
      exact hcont G'' next' l₁' l₂' rv₁ rv₂ ra₁ ra₂ args₁ args₂
        (fun p hp => hsub p (hsub0 p hp))
        (fun p hp => hG'' p (List.mem_cons_of_mem _ hp)) hL' hv' ha' hargs'
    | let_ _ _ | store _ _ _ | call _ _ _ | jnz _ _ _ | jump _ _ | ret _ | exit _ _ | hlt
    | group _ _ => exact False.elim hsh
  | .loadReuse slot rest, next, l₁, l₂, _, G', _, _, _, hwf, hsh, hG, hL, cont₁, cont₂, hcont => by
    cases hwf with
    | load t _ hk =>
      dsimp only [hoistStoreStep]
      rcases sLoadsRel_lookup hL slot with ⟨hn₁, hn₂⟩ | ⟨lt, iv₁, iv₂, hs₁, hs₂, hiv⟩
      · rw [hn₁, hn₂]; exact .hlt
      · rw [hs₁, hs₂]; dsimp only
        cases hdec : tyDecEq lt t with
        | isFalse _ => exact .hlt
        | isTrue heq =>
          subst heq
          refine hoistStoreStep_wf jTs st rest next
            (hk iv₁ iv₂) (hsh iv₁) (hG.cons hiv) hL
            fun G'' next' l₁' l₂' rv₁ rv₂ ra₁ ra₂ args₁ args₂ hsub hG'' hL' hv' ha' hargs' => ?_
          exact hcont G'' next' l₁' l₂' rv₁ rv₂ ra₁ ra₂ args₁ args₂ hsub
            (fun p hp => hG'' p (List.mem_cons_of_mem _ hp)) hL' hv' ha' hargs'
    | let_ _ _ | store _ _ _ | call _ _ _ | jnz _ _ _ | jump _ _ | ret _ | exit _ _ | hlt
    | group _ _ => exact False.elim hsh
  | .store tail, next, l₁, l₂, _, G', _, _, _, hwf, hsh, hG, hL, cont₁, cont₂, hcont => by
    cases hwf with
    | store hv ha hk =>
      dsimp only [hoistStoreStep]
      cases hdec : tyDecEq _ st with
      | isFalse hne => exact absurd hsh.1 hne
      | isTrue heq =>
        subst heq
        refine hoistStoreTail_wf jTs tail next hk hsh.2 hG
          fun G'' next' args₁ args₂ hsub hG'' hargs => ?_
        exact hcont G'' next' l₁ l₂ _ _ _ _ args₁ args₂ hsub hG''
          (hL.weaken hsub) (argRel_iargRel hG'' hv) (argRel_iargRel hG'' ha) hargs
    | let_ _ _ | load _ _ _ | call _ _ _ | jnz _ _ _ | jump _ _ | ret _ | exit _ _ | hlt
    | group _ _ => exact False.elim hsh

theorem hoistStoreArms_wf {rs : List Ty} (jTs : List Ty) {D' : Ctx L₁ L₂}
    (sp : StoreDiamondPlan) (next : Nat)
    {G : Ctx (IVal V₁) (IVal V₂)} {G' : Ctx V₁ V₂} {D : Ctx (JLabel L₁) (JLabel L₂)}
    {c₁ : Arg (IVal V₁) .bool} {c₂ : Arg (IVal V₂) .bool}
    {t₁ e₁ : Expr (IVal V₁) (JLabel L₁) rs} {t₂ e₂ : Expr (IVal V₂) (JLabel L₂) rs}
    {fin₁ : Tup (Arg V₁) jTs → Expr V₁ L₁ rs} {fin₂ : Tup (Arg V₂) jTs → Expr V₂ L₂ rs}
    (hc : ArgRel G .bool c₁ c₂) (ht : Wf G D t₁ t₂) (he : Wf G D e₁ e₂)
    (hshT : HasStoreStepShape jTs sp.storeTy sp.armT t₁)
    (hshE : HasStoreStepShape jTs sp.storeTy sp.armE e₁)
    (hG : IRelG G' G)
    (hfin : ∀ G'' sel₁ sel₂, (∀ p ∈ G', p ∈ G'') → TRel (ArgRel G'') sel₁ sel₂ →
      Wf G'' D' (fin₁ sel₁) (fin₂ sel₂)) :
    Wf G' D' (hoistStoreArms jTs sp next c₁ t₁ e₁ fin₁)
             (hoistStoreArms jTs sp next c₂ t₂ e₂ fin₂) := by
  dsimp only [hoistStoreArms]
  have hL0 : SLoadsRel G' ([] : List ((t : Ty) × IVal V₁ t)) [] :=
    ⟨rfl, fun i {_} {_} {_} {_} h1 => by cases h1⟩
  refine hoistStoreStep_wf jTs sp.storeTy sp.armT next ht hshT hG hL0
    fun G₁ next₁ l₁ l₂ vT₁ vT₂ aT₁ aT₂ argsT₁ argsT₂ hsub₁ hG₁ hL₁ hvT haT hargsT => ?_
  refine hoistStoreStep_wf jTs sp.storeTy sp.armE next₁ he hshE hG₁ hL₁
    fun G₂ next₂ _ _ vE₁ vE₂ _ _ argsE₁ argsE₂ hsub₂ hG₂ _ hvE _ hargsE => ?_
  have hc₂ := (argRel_iout hG hc).weaken (fun p hp => hsub₂ p (hsub₁ p hp))
  have hvT₂ := iargRel_weaken hsub₂ hvT
  have haT₂ := haT.1.weaken hsub₂
  have hargsT₂ := TRel.mono (fun _ _ _ h => iargRel_weaken hsub₂ h) hargsT
  refine emitSelectTy_wf hc₂ sp.storeTy next₂ hvT₂ hvE fun G₃ next₃ selV₁ selV₂ hsub₃ hselV => ?_
  have hc₃ := hc₂.weaken hsub₃
  have haT₃ := haT₂.weaken hsub₃
  have hargsT₃ := TRel.mono (fun _ _ _ h => iargRel_weaken hsub₃ h) hargsT₂
  have hargsE₃ := TRel.mono (fun _ _ _ h => iargRel_weaken hsub₃ h) hargsE
  refine .store hselV haT₃
    (emitSelectTup_wf hc₃ jTs next₃ hargsT₃ hargsE₃ fun G₄ sel₁ sel₂ hsub₄ hsel => ?_)
  exact hfin G₄ sel₁ sel₂
    (fun p hp => hsub₄ p (hsub₃ p (hsub₂ p (hsub₁ p hp)))) hsel

theorem hoistDiamond_wf {rs : List Ty} {jTs : List Ty} {D' : Ctx L₁ L₂}
    {j₁ : L₁ jTs} {j₂ : L₂ jTs} (hj : ⟨jTs, j₁, j₂⟩ ∈ D') :
    ∀ (plan : DiamondPlan) (next : Nat) {G : Ctx (IVal V₁) (IVal V₂)} {G' : Ctx V₁ V₂}
      {D : Ctx (JLabel L₁) (JLabel L₂)}
      {e₁ : Expr (IVal V₁) (JLabel L₁) rs} {e₂ : Expr (IVal V₂) (JLabel L₂) rs},
    Wf G D e₁ e₂ → HasDiamondShape jTs plan e₁ → IRelG G' G →
    Wf G' D' (hoistDiamond j₁ plan next e₁) (hoistDiamond j₂ plan next e₂)
  | .jnz pT pE, next, _, G', _, _, _, hwf, hsh, hG => by
    cases hwf with
    | jnz hc ht he =>
      rcases hsh with ⟨hshT, hshE⟩
      dsimp only [hoistDiamond]
      exact hoistJnzArms_wf jTs pT pE next hc ht he hshT hshE hG fun _ _ _ _ hsel => .jump hj hsel
    | let_ _ _ | load _ _ _ | store _ _ _ | call _ _ _ | jump _ _ | ret _ | exit _ _ | hlt
    | group _ _ => exact False.elim hsh
  | .jnzStore sp, next, _, G', _, _, _, hwf, hsh, hG => by
    cases hwf with
    | jnz hc ht he =>
      rcases hsh with ⟨hshT, hshE⟩
      dsimp only [hoistDiamond]
      exact hoistStoreArms_wf jTs sp next hc ht he hshT hshE hG fun _ _ _ _ hsel => .jump hj hsel
    | let_ _ _ | load _ _ _ | store _ _ _ | call _ _ _ | jump _ _ | ret _ | exit _ _ | hlt
    | group _ _ => exact False.elim hsh
  | .let_ rest, next, _, G', _, _, _, hwf, hsh, hG => by
    cases hwf with
    | let_ hop hk =>
      cases hop with
      | mk code hargs =>
        dsimp only [hoistDiamond]
        refine .let_ (.mk code (trel_iout hG hargs)) fun xs₁ xs₂ => ?_
        exact hoistDiamond_wf hj rest (next + _)
          (hk (freshIVals _ xs₁ next) (freshIVals _ xs₂ next))
          (hsh (freshIVals _ xs₁ next)) (hG.freshIVals xs₁ xs₂ next)
    | load _ _ _ | store _ _ _ | call _ _ _ | jnz _ _ _ | jump _ _ | ret _ | exit _ _ | hlt
    | group _ _ => exact False.elim hsh
  | .load rest, next, _, G', _, _, _, hwf, hsh, hG => by
    cases hwf with
    | load t ha hk =>
      dsimp only [hoistDiamond]
      refine .load t (argRel_iout hG ha) fun v₁ v₂ => ?_
      exact hoistDiamond_wf hj rest (next + 1) (hk (.var v₁, .var next) (.var v₂, .var next))
        (hsh (.var v₁, .var next)) (hG.freshOne v₁ v₂ next)
    | let_ _ _ | store _ _ _ | call _ _ _ | jnz _ _ _ | jump _ _ | ret _ | exit _ _ | hlt
    | group _ _ => exact False.elim hsh
  | .store rest, next, _, G', _, _, _, hwf, hsh, hG => by
    cases hwf with
    | store hv ha hk =>
      dsimp only [hoistDiamond]
      exact .store (argRel_iout hG hv) (argRel_iout hG ha) (hoistDiamond_wf hj rest next hk hsh hG)
    | let_ _ _ | load _ _ _ | call _ _ _ | jnz _ _ _ | jump _ _ | ret _ | exit _ _ | hlt
    | group _ _ => exact False.elim hsh
  | .call rest, next, _, G', _, _, _, hwf, hsh, hG => by
    cases hwf with
    | call f hargs hk =>
      dsimp only [hoistDiamond]
      refine .call f (trel_iout hG hargs) fun xs₁ xs₂ => ?_
      exact hoistDiamond_wf hj rest (next + _)
        (hk (freshIVals _ xs₁ next) (freshIVals _ xs₂ next))
        (hsh (freshIVals _ xs₁ next)) (hG.freshIVals xs₁ xs₂ next)
    | let_ _ _ | load _ _ _ | store _ _ _ | jnz _ _ _ | jump _ _ | ret _ | exit _ _ | hlt
    | group _ _ => exact False.elim hsh

end WfSelect

/-! ## `ifOpt_wf` via `Wf.induct` -/

theorem ifOptB_get {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (bitsOnly : Bool) (depth next : Nat) :
    {sig : List (List Ty)} → {ts : List Ty} → (bs : Blocks (IVal V) (JLabel L) rs sig) →
    (i : Member ts sig) → (xs : Tup V ts) →
    (ifOptBWith bitsOnly depth next bs).get i xs =
      ifOptWith bitsOnly depth (next + ts.length) (bs.get i (freshIVals ts xs next))
  | _, _, .cons _ _, .here, _ => rfl
  | _, _, .cons _ bs, .there i, xs => ifOptB_get bitsOnly depth next bs i xs

@[expose] def OuterD {L₁ L₂ : List Ty → Type} (D : Ctx (JLabel L₁) (JLabel L₂))
    (D' : Ctx L₁ L₂) : Prop :=
  ∀ p ∈ D, match p.2.1, p.2.2 with
    | .outer l₁, .outer l₂ => ⟨p.1, l₁, l₂⟩ ∈ D'
    | _, _ => False

@[expose] def TagD {L₁ L₂ : List Ty → Type} (D : Ctx (JLabel L₁) (JLabel L₂))
    (D' : Ctx L₁ L₂) : Prop :=
  ∀ p ∈ D, match p.2.1, p.2.2 with
    | .outer l₁, .outer l₂ => ⟨p.1, l₁, l₂⟩ ∈ D'
    | .tag id₁ l₁, .tag id₂ l₂ => id₁ = id₂ ∧ ⟨p.1, l₁, l₂⟩ ∈ D'
    | _, _ => False

theorem OuterD.to_tagD {L₁ L₂ : List Ty → Type}
    {D : Ctx (JLabel L₁) (JLabel L₂)} {D' : Ctx L₁ L₂} (hD : OuterD D D') : TagD D D' := by
  intro ⟨ts, j₁, j₂⟩ hp
  have hd := hD _ hp
  cases j₁ <;> cases j₂ <;> simp_all

theorem TagD.checkArm_compat {L₁ L₂ : List Ty → Type}
    {D : Ctx (JLabel L₁) (JLabel L₂)} {D' : Ctx L₁ L₂} (hD : TagD D D') :
    ∀ p ∈ D, match p.2.1, p.2.2 with
      | .loc d₁, .loc d₂ => d₁ = d₂
      | .tag id₁ _, .tag id₂ _ => id₁ = id₂
      | .outer _, .outer _ => True
      | _, _ => False := by
  intro ⟨ts, j₁, j₂⟩ hp
  have hd := hD _ hp
  cases j₁ <;> cases j₂ <;> simp_all

theorem TagD.head_compat {L₁ L₂ : List Ty → Type}
    {D : Ctx (JLabel L₁) (JLabel L₂)} {D' : Ctx L₁ L₂} (hD : TagD D D')
    (jId : Nat) {ts : List Ty} :
    ∀ p ∈ (⟨ts, JLabel.loc jId, JLabel.loc jId⟩ :: D),
      match p.2.1, p.2.2 with
      | .loc d₁, .loc d₂ => d₁ = d₂
      | .tag id₁ _, .tag id₂ _ => id₁ = id₂
      | .outer _, .outer _ => True
      | _, _ => False := by
  intro ⟨pts, j₁, j₂⟩ hp
  cases hp with
  | head => rfl
  | tail _ hp => exact TagD.checkArm_compat hD _ hp

theorem TagD.append_outer {L₁ L₂ : List Ty → Type}
    {D : Ctx (JLabel L₁) (JLabel L₂)} {D' : Ctx L₁ L₂} (hD : TagD D D') :
    {sig : List (List Ty)} → (Js₁ : Tup L₁ sig) → (Js₂ : Tup L₂ sig) →
    TagD (Tup.zip (Js₁.map fun _ l => .outer l) (Js₂.map fun _ l => .outer l) ++ D)
      (Tup.zip Js₁ Js₂ ++ D')
  | [], (), (), p, hp => by
    have := hD p hp
    cases h1 : p.2.1 <;> cases h2 : p.2.2 <;> simp_all
  | _ :: _, (j₁, Js₁), (j₂, Js₂), p, hp => by
    simp only [Tup.map, Tup.zip, List.cons_append] at hp ⊢
    cases hp with
    | head => exact List.mem_cons_self
    | tail _ hp =>
      have ih := TagD.append_outer hD Js₁ Js₂ p hp
      cases h1 : p.2.1 <;> cases h2 : p.2.2 <;> simp_all

theorem TagD.append_tag {L₁ L₂ : List Ty → Type}
    {D : Ctx (JLabel L₁) (JLabel L₂)} {D' : Ctx L₁ L₂} (hD : TagD D D') :
    (depth : Nat) → {sig : List (List Ty)} → (Js₁ : Tup L₁ sig) → (Js₂ : Tup L₂ sig) →
    TagD (Tup.zip (tagLabels depth Js₁) (tagLabels depth Js₂) ++ D) (Tup.zip Js₁ Js₂ ++ D')
  | _, [], (), (), p, hp => by
    have := hD p hp
    cases h1 : p.2.1 <;> cases h2 : p.2.2 <;> simp_all
  | depth, _ :: _, (j₁, Js₁), (j₂, Js₂), p, hp => by
    simp only [tagLabels, Tup.zip, List.cons_append] at hp ⊢
    cases hp with
    | head => exact ⟨rfl, List.mem_cons_self⟩
    | tail _ hp =>
      have ih := TagD.append_tag hD (depth + 1) Js₁ Js₂ p hp
      cases h1 : p.2.1 <;> cases h2 : p.2.2 <;> simp_all

theorem findFirstJump_eq_of_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type}
    {G : Ctx (IVal V₁) (IVal V₂)} {D : Ctx (JLabel L₁) (JLabel L₂)} {D' : Ctx L₁ L₂}
    {rs : List Ty} (hD : TagD D D') :
    ∀ (fuel : Nat) {e₁ : Expr (IVal V₁) (JLabel L₁) rs} {e₂ : Expr (IVal V₂) (JLabel L₂) rs},
    Wf G D e₁ e₂ →
    (findFirstJump fuel e₁ = none ∧ findFirstJump fuel e₂ = none) ∨
    (∃ ts id l₁ l₂, findFirstJump fuel e₁ = some ⟨ts, id, l₁⟩ ∧
      findFirstJump fuel e₂ = some ⟨ts, id, l₂⟩ ∧ ⟨ts, l₁, l₂⟩ ∈ D')
  | 0, _, _, _ => Or.inl ⟨rfl, rfl⟩
  | fuel + 1, _, _, .let_ _ hk =>
    findFirstJump_eq_of_wf hD fuel (hk (dummyIVals _ 0) (dummyIVals _ 0))
  | fuel + 1, _, _, .jnz _ ht _ =>
    findFirstJump_eq_of_wf hD fuel ht
  | _ + 1, _, _, .jump (ts := ts) (j₁ := j₁) (j₂ := j₂) hj _ => by
    have hjl := hD _ hj
    cases j₁ <;> cases j₂ <;> dsimp only at hjl
    all_goals first
      | exact Or.inl ⟨rfl, rfl⟩
      | exact False.elim hjl
      | (rcases hjl with ⟨rfl, hl⟩; exact Or.inr ⟨ts, _, _, _, rfl, rfl, hl⟩)
  | _ + 1, _, _, .load _ _ _ | _ + 1, _, _, .store _ _ _ | _ + 1, _, _, .call _ _ _
  | _ + 1, _, _, .ret _ | _ + 1, _, _, .exit _ _ | _ + 1, _, _, .hlt
  | _ + 1, _, _, .group _ _ => Or.inl ⟨rfl, rfl⟩

theorem findFirstJumpStore_eq_of_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type}
    {G : Ctx (IVal V₁) (IVal V₂)} {D : Ctx (JLabel L₁) (JLabel L₂)} {D' : Ctx L₁ L₂}
    {rs : List Ty} (hD : TagD D D') :
    ∀ (fuel : Nat) {e₁ : Expr (IVal V₁) (JLabel L₁) rs} {e₂ : Expr (IVal V₂) (JLabel L₂) rs},
    Wf G D e₁ e₂ →
    (findFirstJumpStore fuel e₁ = none ∧ findFirstJumpStore fuel e₂ = none) ∨
    (∃ ts id l₁ l₂, findFirstJumpStore fuel e₁ = some ⟨ts, id, l₁⟩ ∧
      findFirstJumpStore fuel e₂ = some ⟨ts, id, l₂⟩ ∧ ⟨ts, l₁, l₂⟩ ∈ D')
  | 0, _, _, _ => Or.inl ⟨rfl, rfl⟩
  | fuel + 1, _, _, .let_ _ hk =>
    findFirstJumpStore_eq_of_wf hD fuel (hk (dummyIVals _ 0) (dummyIVals _ 0))
  | fuel + 1, _, _, .load _ _ hk =>
    findFirstJumpStore_eq_of_wf hD fuel (hk (.imm default, .var 0) (.imm default, .var 0))
  | fuel + 1, _, _, .store _ _ hk =>
    findFirstJumpStore_eq_of_wf hD fuel hk
  | _ + 1, _, _, .jump (ts := ts) (j₁ := j₁) (j₂ := j₂) hj _ => by
    have hjl := hD _ hj
    cases j₁ <;> cases j₂ <;> dsimp only at hjl
    all_goals first
      | exact Or.inl ⟨rfl, rfl⟩
      | exact False.elim hjl
      | (rcases hjl with ⟨rfl, hl⟩; exact Or.inr ⟨ts, _, _, _, rfl, rfl, hl⟩)
  | _ + 1, _, _, .jnz _ _ _ | _ + 1, _, _, .call _ _ _
  | _ + 1, _, _, .ret _ | _ + 1, _, _, .exit _ _ | _ + 1, _, _, .hlt
  | _ + 1, _, _, .group _ _ => Or.inl ⟨rfl, rfl⟩



inductive TermTarget (rs : List Ty) : List Ty → Type
  | jump {jTs : List Ty} (j : Cont jTs) : TermTarget rs jTs
  | ret : TermTarget rs rs

@[expose] def TermTarget.wp {rs : List Ty} (Q : Post rs) :
    {jTs : List Ty} → TermTarget rs jTs → Tup Val jTs → Mem 64 → Prop
  | _, .jump j, vs, m => j vs m
  | _, .ret, vs, m => Q vs m

@[expose] def ArmSpec {rs : List Ty} {jTs : List Ty} (tgt : TermTarget rs jTs)
    (p : ArmPlan) (e : Expr Val Cont rs) : Prop :=
  match p, e, tgt with
  | .jump, .jump (ts := ts) l _, .jump j => ∃ h : ts = jTs, l = h ▸ j
  | .ret, .ret _, .ret => True
  | .let_ rest, .let_ op k, tgt => isSafeOp op.code = true ∧ ∀ xs, ArmSpec tgt rest (k xs)
  | .jnz pT pE, .jnz _ t e, tgt => ArmSpec tgt pT t ∧ ArmSpec tgt pE e
  | _, _, _ => False

@[expose] def StoreTailSpec {rs : List Ty} {jTs : List Ty} (tgt : TermTarget rs jTs)
    (p : StoreTail) (e : Expr Val Cont rs) : Prop :=
  match p, e, tgt with
  | .jump, .jump (ts := ts) l _, .jump j => ∃ h : ts = jTs, l = h ▸ j
  | .ret, .ret _, .ret => True
  | .let_ rest, .let_ op k, tgt => isSafeOp op.code = true ∧ ∀ xs, StoreTailSpec tgt rest (k xs)
  | _, _, _ => False

theorem isSafeOp_ts_pos {sig ts : List Ty} (code : OpCode sig ts)
    (hs : isSafeOp code = true) : 0 < ts.length := by
  cases code <;> first | exact Nat.succ_pos _ | (dsimp [isSafeOp] at hs; cases hs)

@[expose] def SymTblWf (base : Nat) (tbl : SymTbl) : Prop :=
  base ≤ tbl.vnNext ∧
  (∀ e ∈ tbl.ops, ∃ s, e.res = freshFKeys e.ts s ∧ base ≤ s ∧ s + e.ts.length ≤ tbl.vnNext ∧
    isSafeOp e.code = true ∧ fKeysLt s e.args) ∧
  (∀ i (l : SymLoadEntry), tbl.loads[i]? = some l →
    l.slot = i ∧ base ≤ l.vn ∧ l.vn < tbl.vnNext ∧ l.addr.FLt l.vn) ∧
  (∀ (i₁ i₂ : Nat) (e₁ e₂ : SymOpEntry),
    i₁ < i₂ → tbl.ops[i₁]? = some e₁ → tbl.ops[i₂]? = some e₂ →
    ∀ s₁ s₂, e₁.res = freshFKeys e₁.ts s₁ → e₂.res = freshFKeys e₂.ts s₂ →
    s₂ + e₂.ts.length ≤ s₁) ∧
  (∀ e ∈ tbl.ops, ∀ l ∈ tbl.loads, ∀ s, e.res = freshFKeys e.ts s →
    l.vn < s ∨ s + e.ts.length ≤ l.vn) ∧
  (∀ (j₁ j₂ : Nat) (l₁ l₂ : SymLoadEntry), j₁ ≠ j₂ →
    tbl.loads[j₁]? = some l₁ → tbl.loads[j₂]? = some l₂ → l₁.vn ≠ l₂.vn)

@[expose] def KeyIn (D : Nat → Bool) : {t : Ty} → FKey t → Prop
  | _, .var i => D i = true
  | _, .imm _ => True

@[expose] def fKeysIn (D : Nat → Bool) : {ts : List Ty} → Tup FKey ts → Prop
  | [], () => True
  | _ :: _, (k, ks) => KeyIn D k ∧ fKeysIn D ks

@[expose] def addVN (D : Nat → Bool) (v : Nat) : Nat → Bool :=
  fun i => D i || i == v

@[expose] def addKey {t : Ty} (D : Nat → Bool) : FKey t → Nat → Bool
  | .var v => addVN D v
  | .imm _ => D

@[expose] def addKeys : {ts : List Ty} → (Nat → Bool) → Tup FKey ts → Nat → Bool
  | [], D, () => D
  | _ :: _, D, (k, ks) => addKeys (addKey D k) ks

@[expose] def StoreStepSpec {rs : List Ty} {jTs : List Ty} (tgt : TermTarget rs jTs)
    (st : Ty) (allowNew : Bool) (Qend : List Nat → SymTbl → Prop) :
    StoreStep → SymTbl → (Nat → Bool) → List Nat → FKey i64 → FEnv → Expr Val Cont rs → Prop
  | .let_ rest, tbl, D, hits, aGoal, ρ, .let_ (ts := ts) op k =>
    isSafeOp op.code = true ∧
    ∃ (kArgs : Tup FKey op.sig),
      fKeysEval ρ kArgs = vals op.args ∧ fKeysIn D kArgs ∧ fKeysLt tbl.vnNext kArgs ∧
      let (resKeys, tbl1) := tbl.internOp op.code kArgs
      ∀ (r : Tup Val ts) (ρ' : FEnv),
        (∀ {u} (fk : FKey u), KeyIn D fk → fk.fev ρ' = fk.fev ρ) →
        fKeysEval ρ' resKeys = r →
        StoreStepSpec tgt st allowNew Qend rest tbl1 (addKeys D resKeys) hits aGoal ρ' (k r)
  | .loadEmit rest, tbl, D, hits, aGoal, ρ, .load t a k =>
    allowNew = true ∧
    ∃ (aKey : FKey i64),
      aKey.fev ρ = a.val ∧ KeyIn D aKey ∧ aKey.FLt tbl.vnNext ∧
      findSymLoad tbl.loads t aKey = none ∧
      let entry : SymLoadEntry := ⟨tbl.loads.length, t, aKey, tbl.vnNext⟩
      let tbl1 : SymTbl := { tbl with vnNext := tbl.vnNext + 1, loads := tbl.loads ++ [entry] }
      ∀ (v : Val t) (ρ' : FEnv),
        (∀ {u} (fk : FKey u), KeyIn D fk → fk.fev ρ' = fk.fev ρ) →
        ρ' t tbl.vnNext = v →
        StoreStepSpec tgt st allowNew Qend rest tbl1 (addVN D tbl.vnNext)
          (entry.slot :: hits) aGoal ρ' (k v)
  | .loadReuse slot rest, tbl, D, hits, aGoal, ρ, .load t a k =>
    ∃ (aKey : FKey i64) (entry : SymLoadEntry),
      aKey.fev ρ = a.val ∧ KeyIn D aKey ∧ aKey.FLt tbl.vnNext ∧
      findSymLoad tbl.loads t aKey = some entry ∧ entry.slot = slot ∧
      let hits' := if hits.contains slot then hits else slot :: hits
      ∀ (v : Val t) (ρ' : FEnv),
        (∀ {u} (fk : FKey u), KeyIn D fk → fk.fev ρ' = fk.fev ρ) →
        ρ' t entry.vn = v →
        StoreStepSpec tgt st allowNew Qend rest tbl (addVN D entry.vn) hits' aGoal ρ' (k v)
  | .store tail, tbl, D, hits, aGoal, ρ, .store (t := st') _ a k =>
    st' = st ∧ aGoal.fev ρ = a.val ∧ KeyIn D aGoal ∧ Qend hits tbl ∧ StoreTailSpec tgt tail k
  | _, _, _, _, _, _, _ => False

@[expose] def StoreDiamondSpec {rs : List Ty} {jTs : List Ty} (tgt : TermTarget rs jTs)
    (sp : StoreDiamondPlan) (next : Nat) (ρ : FEnv)
    (t₂ e₂ : Expr Val Cont rs) : Prop :=
  let D₀ : Nat → Bool := fun i => decide (i < next)
  isSelectTy sp.storeTy = true ∧
  ∃ (tbl₁ : SymTbl) (aGoal : FKey i64),
    SymTblWf next tbl₁ ∧ tbl₁.loads.length = sp.numLoads ∧ aGoal.FLt tbl₁.vnNext ∧
    (∀ ρT, (∀ {u} (fk : FKey u), fk.FLt next → fk.fev ρT = fk.fev ρ) →
      StoreStepSpec tgt sp.storeTy true (fun _ tbl => tbl = tbl₁) sp.armT
        ⟨next, [], []⟩ D₀ [] aGoal ρT t₂) ∧
    (∀ ρE, (∀ {u} (fk : FKey u), fk.FLt next → fk.fev ρE = fk.fev ρ) →
      StoreStepSpec tgt sp.storeTy false
        (fun hits tbl => tbl.loads = tbl₁.loads ∧ ∀ s, s < tbl₁.loads.length → s ∈ hits)
        sp.armE tbl₁ D₀ [] aGoal ρE e₂)

@[expose] def DiamondSpec {rs : List Ty} {jTs : List Ty} (j : Cont jTs) (next : Nat) (ρ : FEnv) :
    DiamondPlan → Expr Val Cont rs → Prop
  | .jnz pT pE, .jnz _ t e =>
    isSelectSig jTs = true ∧ ArmSpec (.jump j) pT t ∧ ArmSpec (.jump j) pE e
  | .jnzStore sp, .jnz _ t e =>
    isSelectSig jTs = true ∧ StoreDiamondSpec (.jump j) sp next ρ t e
  | .let_ rest, .let_ (ts := ts) _ k =>
    ∀ xs, DiamondSpec j (next + ts.length) (fupdTup ρ next xs) rest (k xs)
  | .load rest, .load _ _ k =>
    ∀ v, DiamondSpec j (next + 1) (fupd ρ next v) rest (k v)
  | .store rest, .store _ _ k => DiamondSpec j next ρ rest k
  | .call rest, .call _ (bs := bs) _ k =>
    ∀ xs, DiamondSpec j (next + bs.length) (fupdTup ρ next xs) rest (k xs)
  | _, _ => False

@[expose] def OuterContD (D : Ctx (JLabel Cont) Cont) : Prop :=
  ∀ p ∈ D, match p.2.1 with | .outer l => l = p.2.2 | .loc _ => False | .tag _ _ => False

@[expose] def TagContD (depth : Nat) (D : Ctx (JLabel Cont) Cont) : Prop :=
  (∀ p ∈ D, match p.2.1 with
    | .outer l => l = p.2.2
    | .tag id l => id < depth ∧ l = p.2.2
    | .loc _ => False) ∧
  (∀ {ts₁ ts₂ : List Ty} {id : Nat} {l₁ : Cont ts₁} {l₂ : Cont ts₂}
    {c₁ : Cont ts₁} {c₂ : Cont ts₂},
    ⟨ts₁, .tag id l₁, c₁⟩ ∈ D → ⟨ts₂, .tag id l₂, c₂⟩ ∈ D →
    ∃ h : ts₁ = ts₂, h ▸ c₁ = c₂)

theorem OuterContD.to_tagContD {D : Ctx (JLabel Cont) Cont} (hD : OuterContD D)
    (depth : Nat) : TagContD depth D := by
  refine ⟨fun ⟨ts, j, c⟩ hp => ?_, fun {ts₁ ts₂ id l₁ l₂ c₁ c₂} h1 _ => ?_⟩
  · have hd := hD _ hp
    cases j with
    | outer _ => exact hd
    | loc _ | tag _ _ => exact False.elim hd
  · exact False.elim (hD _ h1)

theorem TagContD.append_outer {depth : Nat} {D : Ctx (JLabel Cont) Cont}
    (hD : TagContD depth D) :
    {sig : List (List Ty)} → (Js : Tup Cont sig) →
    TagContD depth (Tup.zip (Js.map fun _ l => .outer l) Js ++ D)
  | [], () => hD
  | _ :: _, (_, Js) => by
    have ih := TagContD.append_outer hD Js
    refine ⟨fun p hp => ?_, fun h1 h2 => ?_⟩
    · simp only [Tup.map, Tup.zip, List.cons_append] at hp
      cases hp with
      | head => rfl
      | tail _ hp => exact ih.1 p hp
    · simp only [Tup.map, Tup.zip, List.cons_append] at h1 h2
      cases h1 with
      | tail _ h1 =>
        cases h2 with
        | tail _ h2 => exact ih.2 h1 h2

theorem TagContD.mono {d₁ d₂ : Nat} {D : Ctx (JLabel Cont) Cont}
    (hle : d₁ ≤ d₂) (hD : TagContD d₁ D) : TagContD d₂ D := by
  refine ⟨fun p hp => ?_, fun h1 h2 => hD.2 h1 h2⟩
  have h := hD.1 p hp
  cases hj : p.2.1 with
  | outer _ => simpa [hj] using h
  | loc _ => simp [hj] at h
  | tag _ _ =>
    simp only [hj] at h ⊢
    exact ⟨Nat.lt_of_lt_of_le h.1 hle, h.2⟩

private theorem mem_zip_tagLabels :
    {sig : List (List Ty)} → {depth : Nat} → (Js : Tup Cont sig) →
    {ts : List Ty} → {id : Nat} → {l c : Cont ts} →
    ⟨ts, .tag id l, c⟩ ∈ Tup.zip (tagLabels depth Js) Js →
    depth ≤ id ∧ id < depth + sig.length ∧ l = c
  | _ :: _, depth, (_, Js), _, _, _, _, hm => by
    simp only [tagLabels, Tup.zip, List.length_cons] at hm ⊢
    cases hm with
    | head => exact ⟨Nat.le_refl _, Nat.lt_add_of_pos_right (Nat.succ_pos _), rfl⟩
    | tail _ hm =>
      have ⟨h1, h2, h3⟩ := mem_zip_tagLabels Js hm
      exact ⟨by omega, by omega, h3⟩

private theorem mem_zip_tagLabels_inj :
    {sig : List (List Ty)} → {depth : Nat} → (Js : Tup Cont sig) →
    {ts₁ ts₂ : List Ty} → {id : Nat} → {l₁ c₁ : Cont ts₁} → {l₂ c₂ : Cont ts₂} →
    ⟨ts₁, .tag id l₁, c₁⟩ ∈ Tup.zip (tagLabels depth Js) Js →
    ⟨ts₂, .tag id l₂, c₂⟩ ∈ Tup.zip (tagLabels depth Js) Js →
    ∃ h : ts₁ = ts₂, h ▸ c₁ = c₂
  | _ :: _, depth, (_, Js), _, _, _, _, _, _, _, h1, h2 => by
    simp only [tagLabels, Tup.zip] at h1 h2
    cases h1 with
    | head =>
      cases h2 with
      | head => exact ⟨rfl, rfl⟩
      | tail _ h2 =>
        have ⟨hle, _⟩ := mem_zip_tagLabels Js h2
        omega
    | tail _ h1 =>
      cases h2 with
      | head =>
        have ⟨hle, _⟩ := mem_zip_tagLabels Js h1
        omega
      | tail _ h2 => exact mem_zip_tagLabels_inj Js h1 h2

private theorem mem_zip_tagLabels_eq_tag :
    {sig : List (List Ty)} → {depth : Nat} → (Js : Tup Cont sig) →
    ∀ p ∈ Tup.zip (tagLabels depth Js) Js,
      ∃ id l, p.2.1 = .tag id l ∧ id < depth + sig.length ∧ l = p.2.2
  | [], _, (), p, hp => by cases hp
  | _ :: sig, depth, (j, Js), p, hp => by
    simp only [tagLabels, Tup.zip, List.length_cons] at hp ⊢
    cases hp with
    | head => exact ⟨depth, j, rfl, Nat.lt_add_of_pos_right (Nat.succ_pos _), rfl⟩
    | tail _ hp =>
      rcases mem_zip_tagLabels_eq_tag Js p hp with ⟨id, l, h1, h2, h3⟩
      exact ⟨id, l, h1, by omega, h3⟩

theorem TagContD.append_tag {depth : Nat} {D : Ctx (JLabel Cont) Cont}
    (hD : TagContD depth D) {sig : List (List Ty)} (Js : Tup Cont sig) :
    TagContD (depth + sig.length) (Tup.zip (tagLabels depth Js) Js ++ D) := by
  refine ⟨fun p hp => ?_, fun h1 h2 => ?_⟩
  · rcases List.mem_append.1 hp with hp | hp
    · rcases mem_zip_tagLabels_eq_tag Js p hp with ⟨id, l, h1, h2, h3⟩
      rw [h1]; exact ⟨h2, h3⟩
    · exact (hD.mono (Nat.le_add_right _ _)).1 p hp
  · rcases List.mem_append.1 h1 with h1 | h1 <;> rcases List.mem_append.1 h2 with h2 | h2
    · exact mem_zip_tagLabels_inj Js h1 h2
    · have := (mem_zip_tagLabels Js h1).1; have := (hD.1 _ h2).1; omega
    · have := (hD.1 _ h1).1; have := (mem_zip_tagLabels Js h2).1; omega
    · exact hD.2 h1 h2

private def dummyVals : (ts : List Ty) → Tup Val ts
  | [] => ()
  | _ :: ts => (default, dummyVals ts)

theorem findFirstJump_mem_of_wf {G : Ctx (IVal Val) Val}
    {D : Ctx (JLabel Cont) Cont} {rs : List Ty} (depth : Nat) (hD : TagContD depth D) :
    ∀ (fuel : Nat) {e₁ : Expr (IVal Val) (JLabel Cont) rs} {e₂ : Expr Val Cont rs},
    Wf G D e₁ e₂ →
    ∀ {jTs jId jLbl}, findFirstJump fuel e₁ = some ⟨jTs, jId, jLbl⟩ →
      ⟨jTs, .tag jId jLbl, jLbl⟩ ∈ D
  | 0, _, _, _, _, _, _, h => by cases h
  | fuel + 1, _, _, .let_ _ hk, _, _, _, h =>
    findFirstJump_mem_of_wf depth hD fuel (hk (dummyIVals _ 0) (dummyVals _)) h
  | fuel + 1, _, _, .jnz _ ht _, _, _, _, h =>
    findFirstJump_mem_of_wf depth hD fuel ht h
  | _ + 1, _, _, .jump (j₁ := j₁) hj _, _, _, _, h => by
    cases j₁ with
    | outer _ | loc _ => cases h
    | tag id l =>
      simp only [findFirstJump, Option.some.injEq, TaggedTarget.mk.injEq] at h
      rcases h with ⟨rfl, rfl, hlbl⟩
      cases hlbl
      have h2 := (hD.1 _ hj).2
      dsimp only at h2
      subst h2
      exact hj
  | _ + 1, _, _, .load _ _ _, _, _, _, h | _ + 1, _, _, .store _ _ _, _, _, _, h
  | _ + 1, _, _, .call _ _ _, _, _, _, h | _ + 1, _, _, .ret _, _, _, _, h
  | _ + 1, _, _, .exit _ _, _, _, _, h | _ + 1, _, _, .hlt, _, _, _, h
  | _ + 1, _, _, .group _ _, _, _, _, h => by cases h

theorem findFirstJumpStore_mem_of_wf {G : Ctx (IVal Val) Val}
    {D : Ctx (JLabel Cont) Cont} {rs : List Ty} (depth : Nat) (hD : TagContD depth D) :
    ∀ (fuel : Nat) {e₁ : Expr (IVal Val) (JLabel Cont) rs} {e₂ : Expr Val Cont rs},
    Wf G D e₁ e₂ →
    ∀ {jTs jId jLbl}, findFirstJumpStore fuel e₁ = some ⟨jTs, jId, jLbl⟩ →
      ⟨jTs, .tag jId jLbl, jLbl⟩ ∈ D
  | 0, _, _, _, _, _, _, h => by cases h
  | fuel + 1, _, _, .let_ _ hk, _, _, _, h =>
    findFirstJumpStore_mem_of_wf depth hD fuel (hk (dummyIVals _ 0) (dummyVals _)) h
  | fuel + 1, _, _, .load _ _ hk, _, _, _, h =>
    findFirstJumpStore_mem_of_wf depth hD fuel (hk (.imm default, .var 0) default) h
  | fuel + 1, _, _, .store _ _ hk, _, _, _, h =>
    findFirstJumpStore_mem_of_wf depth hD fuel hk h
  | _ + 1, _, _, .jump (j₁ := j₁) hj _, _, _, _, h => by
    cases j₁ with
    | outer _ | loc _ => cases h
    | tag id l =>
      simp only [findFirstJumpStore, Option.some.injEq, TaggedTarget.mk.injEq] at h
      rcases h with ⟨rfl, rfl, hlbl⟩
      cases hlbl
      have h2 := (hD.1 _ hj).2
      dsimp only at h2
      subst h2
      exact hj
  | _ + 1, _, _, .jnz _ _ _, _, _, _, h | _ + 1, _, _, .call _ _ _, _, _, _, h
  | _ + 1, _, _, .ret _, _, _, _, h | _ + 1, _, _, .exit _ _, _, _, _, h
  | _ + 1, _, _, .hlt, _, _, _, h | _ + 1, _, _, .group _ _, _, _, _, h => by cases h

theorem freshFKeys_start_eq :
    {ts : List Ty} → ∀ {s₁ s₂ : Nat},
    freshFKeys ts s₁ = freshFKeys ts s₂ → ts = [] ∨ s₁ = s₂
  | [], _, _, _ => Or.inl rfl
  | _ :: _, _, _, h => by
    simp only [freshFKeys, Prod.mk.injEq, Arg.var.injEq] at h
    exact Or.inr h.1

theorem symTblWf_empty (base : Nat) : SymTblWf base ⟨base, [], []⟩ := by
  refine ⟨Nat.le_refl _, ?_, ?_, ?_, ?_, ?_⟩
  · intro _ h; cases h
  · intro _ _ h; simp at h
  · intro _ _ _ _ _ h; simp at h
  · intro _ h; cases h
  · intro _ _ _ _ _ h; simp at h

theorem symTblWf_internOp {base : Nat} {tbl : SymTbl} (hwf : SymTblWf base tbl)
    {sig ts : List Ty} (code : OpCode sig ts) (hs : isSafeOp code = true)
    (args : Tup FKey sig) (hargs : fKeysLt tbl.vnNext args) :
    SymTblWf base (tbl.internOp code args).2 ∧
    tbl.vnNext ≤ (tbl.internOp code args).2.vnNext ∧
    fKeysLt (tbl.internOp code args).2.vnNext (tbl.internOp code args).1 ∧
    (∀ e ∈ tbl.ops, e ∈ (tbl.internOp code args).2.ops) ∧
    (tbl.internOp code args).2.loads = tbl.loads := by
  unfold SymTbl.internOp
  split
  · exact ⟨hwf, Nat.le_refl _, hargs, fun _ h => h, rfl⟩
  · rcases hwf with ⟨h1, h2, h3, h4, h5, h6⟩
    cases hf : findSymOp tbl.ops sig ts code args with
    | some res =>
      have hmem := findSymOp_mem tbl.ops sig ts code args res hf
      rcases h2 _ hmem with ⟨s, hrs, _, hsle, _, _⟩
      dsimp only at hrs
      exact ⟨⟨h1, h2, h3, h4, h5, h6⟩, Nat.le_refl _,
        hrs ▸ (fKeysLt_freshFKeys ts s).le hsle, fun _ h => h, rfl⟩
    | none =>
      refine ⟨⟨Nat.le_trans h1 (Nat.le_add_right _ _), ?_, ?_, ?_, ?_, ?_⟩,
        Nat.le_add_right _ _, fKeysLt_freshFKeys _ _, fun _ h => List.mem_cons_of_mem _ h, rfl⟩
      · intro e he
        cases he with
        | head => exact ⟨tbl.vnNext, rfl, h1, Nat.le_refl _, hs, hargs⟩
        | tail _ he =>
          rcases h2 _ he with ⟨s, hrs, hbs, hsle, hsafe, hka⟩
          exact ⟨s, hrs, hbs, Nat.le_trans hsle (Nat.le_add_right _ _), hsafe, hka⟩
      · intro i l hl
        rcases h3 i l hl with ⟨hsl, hbl, hlv, hla⟩
        exact ⟨hsl, hbl, Nat.lt_of_lt_of_le hlv (Nat.le_add_right _ _), hla⟩
      · intro i₁ i₂ e₁ e₂ hlt he₁ he₂ s₁ s₂ hrs₁ hrs₂
        cases i₁ <;> cases i₂
        · omega
        · simp only [List.getElem?_cons_zero, Option.some.injEq] at he₁
          simp only [List.getElem?_cons_succ] at he₂
          subst he₁
          rcases h2 _ (List.mem_of_getElem? he₂) with ⟨s₂', hrs₂', _, hsle₂, hsafe₂, _⟩
          have hpos := isSafeOp_ts_pos code hs
          have hpos₂ := isSafeOp_ts_pos _ hsafe₂
          rcases freshFKeys_start_eq hrs₁ with hnil | rfl
          · have : ts.length = 0 := by simp [hnil]
            omega
          · rcases freshFKeys_start_eq (hrs₂.symm.trans hrs₂') with hnil2 | rfl
            · have : e₂.ts.length = 0 := by simp [hnil2]
              omega
            · exact hsle₂
        · omega
        · simp only [List.getElem?_cons_succ] at he₁ he₂
          exact h4 _ _ _ _ (by omega) he₁ he₂ _ _ hrs₁ hrs₂
      · intro e he l hl s hrs
        cases he with
        | head =>
          obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hl
          rcases h3 j l hj with ⟨_, _, hlv, _⟩
          rcases freshFKeys_start_eq hrs with hnil | rfl
          · simp [hnil]; omega
          · exact Or.inl hlv
        | tail _ he => exact h5 _ he l hl s hrs
      · exact h6

theorem symTblWf_loadEmit {base : Nat} {tbl : SymTbl} (hwf : SymTblWf base tbl)
    (t : Ty) (aKey : FKey i64) (ha : aKey.FLt tbl.vnNext) :
    let entry : SymLoadEntry := ⟨tbl.loads.length, t, aKey, tbl.vnNext⟩
    let tbl' : SymTbl := { tbl with vnNext := tbl.vnNext + 1, loads := tbl.loads ++ [entry] }
    SymTblWf base tbl' := by
  intro entry tbl'
  rcases hwf with ⟨h1, h2, h3, h4, h5, h6⟩
  refine ⟨Nat.le_trans h1 (Nat.le_succ _), ?_, ?_, h4, ?_, ?_⟩
  · intro e he
    rcases h2 e he with ⟨s, hrs, hbs, hsle, hsafe, hka⟩
    exact ⟨s, hrs, hbs, Nat.le_trans hsle (Nat.le_succ _), hsafe, hka⟩
  · intro i l hl
    by_cases hi : i < tbl.loads.length
    · rw [List.getElem?_append_left hi] at hl
      rcases h3 i l hl with ⟨hsl, hbl, hlv, hla⟩
      exact ⟨hsl, hbl, Nat.lt_succ_of_lt hlv, hla⟩
    · have hle : tbl.loads.length ≤ i := Nat.le_of_not_lt hi
      rw [List.getElem?_append_right hle] at hl
      cases hidx : i - tbl.loads.length with
      | zero =>
        simp only [hidx, List.getElem?_cons_zero, Option.some.injEq] at hl
        subst hl
        exact ⟨by dsimp only [entry]; omega, h1, Nat.lt_succ_self _, ha⟩
      | succ k => simp [hidx] at hl
  · intro e he l hl s hrs
    rcases List.mem_append.1 hl with hl | hl
    · exact h5 e he l hl s hrs
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      subst hl
      rcases h2 e he with ⟨s', hrs', _, hsle, _, _⟩
      rcases freshFKeys_start_eq (hrs.symm.trans hrs') with hnil | rfl
      · simp [hnil]; omega
      · exact Or.inr hsle
  · intro j₁ j₂ l₁ l₂ hne hj₁ hj₂
    by_cases h1lt : j₁ < tbl.loads.length <;> by_cases h2lt : j₂ < tbl.loads.length
    · rw [List.getElem?_append_left h1lt] at hj₁
      rw [List.getElem?_append_left h2lt] at hj₂
      exact h6 j₁ j₂ l₁ l₂ hne hj₁ hj₂
    · rw [List.getElem?_append_left h1lt] at hj₁
      rw [List.getElem?_append_right (Nat.le_of_not_lt h2lt)] at hj₂
      cases hidx : j₂ - tbl.loads.length with
      | zero =>
        simp only [hidx, List.getElem?_cons_zero, Option.some.injEq] at hj₂
        subst hj₂; have := (h3 j₁ l₁ hj₁).2.2.1; dsimp only [entry]; omega
      | succ k => simp [hidx] at hj₂
    · rw [List.getElem?_append_right (Nat.le_of_not_lt h1lt)] at hj₁
      rw [List.getElem?_append_left h2lt] at hj₂
      cases hidx : j₁ - tbl.loads.length with
      | zero =>
        simp only [hidx, List.getElem?_cons_zero, Option.some.injEq] at hj₁
        subst hj₁; have := (h3 j₂ l₂ hj₂).2.2.1; dsimp only [entry]; omega
      | succ k => simp [hidx] at hj₁
    · exfalso
      rw [List.getElem?_append_right (Nat.le_of_not_lt h1lt)] at hj₁
      rw [List.getElem?_append_right (Nat.le_of_not_lt h2lt)] at hj₂
      cases hidx1 : j₁ - tbl.loads.length <;> cases hidx2 : j₂ - tbl.loads.length <;>
        simp [hidx1, hidx2] at hj₁ hj₂
      omega

private theorem armSpec_of_checkArm_loc {rs : List Ty} (jId : Nat) {jTs : List Ty} (j : Cont jTs)
    (depth : Nat) {G : Ctx (IVal Val) Val} {D : Ctx (JLabel Cont) Cont}
    {e₁ : Expr (IVal Val) (JLabel Cont) rs} {e₂ : Expr Val Cont rs}
    (hD : TagContD depth D) (hwf : Wf G (⟨jTs, .loc jId, j⟩ :: D) e₁ e₂) :
    ∀ {jnzFuel letFuel next rem : Nat} {p : ArmPlan},
      checkArm (.loc jId jTs) jnzFuel letFuel next e₁ = some (p, rem) →
      ArmSpec (.jump j) p e₂ :=
  checkArm_peel (.loc jId jTs) (ArmSpec (.jump j))
    (fun hs h => ⟨hs, h⟩) (fun ht he => ⟨ht, he⟩)
    (fun {_ j₁ _ _} hj hcond => by
      cases hj with
      | head => exact ⟨rfl, rfl⟩
      | tail _ hm =>
        have hbad := hD.1 _ hm
        cases j₁ <;> simp_all)
    (fun h => by cases h)
    hwf

theorem armSpec_of_checkArm_tag {rs : List Ty} (jId : Nat) {jTs : List Ty} (l₀ j : Cont jTs)
    (depth : Nat) {G : Ctx (IVal Val) Val} {D : Ctx (JLabel Cont) Cont}
    {e₁ : Expr (IVal Val) (JLabel Cont) rs} {e₂ : Expr Val Cont rs}
    (hwf : Wf G D e₁ e₂) (hD : TagContD depth D) (hj₀ : ⟨jTs, .tag jId l₀, j⟩ ∈ D) :
    ∀ {jnzFuel letFuel next rem : Nat} {p : ArmPlan},
      checkArm (.tag jId jTs) jnzFuel letFuel next e₁ = some (p, rem) →
      ArmSpec (.jump j) p e₂ :=
  checkArm_peel (.tag jId jTs) (ArmSpec (.jump j))
    (fun hs h => ⟨hs, h⟩) (fun ht he => ⟨ht, he⟩)
    (fun {_ j₁ _ _} hj hcond => by
      cases j₁ with
      | outer _ | loc _ => exact False.elim hcond
      | tag id l =>
        rcases hcond with ⟨rfl, rfl⟩
        rcases hD.2 hj hj₀ with ⟨h, heq⟩
        exact ⟨rfl, by simpa using heq⟩)
    (fun h => by cases h)
    hwf

theorem armSpec_of_checkArm_ret {rs : List Ty}
    {G : Ctx (IVal Val) Val} {D : Ctx (JLabel Cont) Cont}
    {e₁ : Expr (IVal Val) (JLabel Cont) rs} {e₂ : Expr Val Cont rs}
    (hwf : Wf G D e₁ e₂) :
    ∀ {jnzFuel letFuel next rem : Nat} {p : ArmPlan},
      checkArm .ret jnzFuel letFuel next e₁ = some (p, rem) →
      ArmSpec (rs := rs) .ret p e₂ :=
  checkArm_peel .ret (ArmSpec (rs := rs) .ret)
    (fun hs h => ⟨hs, h⟩) (fun ht he => ⟨ht, he⟩)
    (fun {_ j₁ _ _} _ hcond => by cases j₁ <;> exact False.elim hcond)
    (fun _ => trivial)
    hwf

private theorem storeTailSpec_of_checkStoreTail_loc {rs : List Ty} (jId : Nat)
    {jTs : List Ty} (j : Cont jTs) (depth : Nat)
    {G : Ctx (IVal Val) Val} {D : Ctx (JLabel Cont) Cont}
    {e₁ : Expr (IVal Val) (JLabel Cont) rs} {e₂ : Expr Val Cont rs}
    (hD : TagContD depth D) (hwf : Wf G (⟨jTs, .loc jId, j⟩ :: D) e₁ e₂) :
    ∀ {letFuel : Nat} {p : StoreTail},
      checkStoreTail (.loc jId jTs) letFuel e₁ = some p → StoreTailSpec (.jump j) p e₂ :=
  checkStoreTail_peel (.loc jId jTs) (StoreTailSpec (.jump j))
    (fun hs h => ⟨hs, h⟩)
    (fun {_ j₁ _ _} hj hcond => by
      cases hj with
      | head => exact ⟨rfl, rfl⟩
      | tail _ hm => have hbad := hD.1 _ hm; cases j₁ <;> simp_all)
    (fun h => by cases h)
    hwf

private theorem storeTailSpec_of_checkStoreTail_tag {rs : List Ty} (jId : Nat)
    {jTs : List Ty} (l₀ j : Cont jTs) (depth : Nat)
    {G : Ctx (IVal Val) Val} {D : Ctx (JLabel Cont) Cont}
    {e₁ : Expr (IVal Val) (JLabel Cont) rs} {e₂ : Expr Val Cont rs}
    (hwf : Wf G D e₁ e₂) (hD : TagContD depth D) (hj₀ : ⟨jTs, .tag jId l₀, j⟩ ∈ D) :
    ∀ {letFuel : Nat} {p : StoreTail},
      checkStoreTail (.tag jId jTs) letFuel e₁ = some p → StoreTailSpec (.jump j) p e₂ :=
  checkStoreTail_peel (.tag jId jTs) (StoreTailSpec (.jump j))
    (fun hs h => ⟨hs, h⟩)
    (fun {_ j₁ _ _} hj hcond => by
      cases j₁ with
      | outer _ | loc _ => exact False.elim hcond
      | tag id l =>
        rcases hcond with ⟨rfl, rfl⟩
        rcases hD.2 hj hj₀ with ⟨h, heq⟩
        exact ⟨rfl, by simpa using heq⟩)
    (fun h => by cases h)
    hwf

private theorem storeTailSpec_of_checkStoreTail_ret {rs : List Ty}
    {G : Ctx (IVal Val) Val} {D : Ctx (JLabel Cont) Cont}
    {e₁ : Expr (IVal Val) (JLabel Cont) rs} {e₂ : Expr Val Cont rs}
    (hwf : Wf G D e₁ e₂) :
    ∀ {letFuel : Nat} {p : StoreTail},
      checkStoreTail .ret letFuel e₁ = some p → StoreTailSpec (rs := rs) .ret p e₂ :=
  checkStoreTail_peel .ret (StoreTailSpec (rs := rs) .ret)
    (fun hs h => ⟨hs, h⟩)
    (fun {_ j₁ _ _} _ hcond => by cases j₁ <;> exact False.elim hcond)
    (fun _ => trivial)
    hwf

@[expose] def SymGIn (ρ : FEnv) (b : Nat) (D : Nat → Bool) (G : Ctx (IVal Val) Val) : Prop :=
  ∀ p ∈ G, p.2.1.2.fev ρ = p.2.2 ∧ KeyIn D p.2.1.2 ∧ p.2.1.2.FLt b

theorem keyIn_mono {D₁ D₂ : Nat → Bool} (hsub : ∀ i, D₁ i = true → D₂ i = true) :
    {t : Ty} → {k : FKey t} → KeyIn D₁ k → KeyIn D₂ k
  | _, .var _, h => hsub _ h
  | _, .imm _, _ => trivial

theorem fKeysIn_mono {D₁ D₂ : Nat → Bool} (hsub : ∀ i, D₁ i = true → D₂ i = true) :
    {ts : List Ty} → {ks : Tup FKey ts} → fKeysIn D₁ ks → fKeysIn D₂ ks
  | [], (), _ => trivial
  | _ :: _, (_, _), ⟨h1, h2⟩ => ⟨keyIn_mono hsub h1, fKeysIn_mono hsub h2⟩

theorem addVN_sub (D : Nat → Bool) (v : Nat) : ∀ i, D i = true → addVN D v i = true := by
  intro i hi; simp [addVN, hi]

theorem addKeys_sub : {ts : List Ty} → (D : Nat → Bool) → (ks : Tup FKey ts) →
    ∀ i, D i = true → addKeys D ks i = true
  | [], D, (), _ => fun hi => hi
  | _ :: _, D, (k, ks), i => fun hi => by
    refine addKeys_sub _ ks i ?_
    cases k with
    | var v => exact addVN_sub D v i hi
    | imm _ => exact hi

theorem fKeysIn_addKeys : {ts : List Ty} → (D : Nat → Bool) → (ks : Tup FKey ts) →
    fKeysIn (addKeys D ks) ks
  | [], _, () => trivial
  | _ :: _, D, (k, ks) => by
    refine ⟨?_, fKeysIn_addKeys _ ks⟩
    cases k with
    | var v => exact addKeys_sub (addVN D v) ks v (by simp [addVN])
    | imm _ => trivial

theorem symGIn_of_iGood {ρ : FEnv} {b : Nat} {G : Ctx (IVal Val) Val} (h : IGood ρ b G) :
    SymGIn ρ b (fun i => decide (i < b)) G := by
  intro p hp
  rcases h p hp with ⟨_, h1, h2⟩
  refine ⟨h1, ?_, h2⟩
  cases hk : p.2.1.2 with
  | var i =>
    have hlt : i < b := by rw [hk] at h2; exact h2
    exact decide_eq_true hlt
  | imm _ => trivial

private theorem symGIn_dummyKeyIVals_mem {ρ' : FEnv} {b' : Nat} :
    {ts : List Ty} → (D : Nat → Bool) → (ks : Tup FKey ts) → (r : Tup Val ts) →
    fKeysIn (addKeys D ks) ks → fKeysLt b' ks → fKeysEval ρ' ks = r →
    ∀ p ∈ Tup.zip (dummyKeyIVals (V := Val) ts ks) r,
      p.2.1.2.fev ρ' = p.2.2 ∧ KeyIn (addKeys D ks) p.2.1.2 ∧ p.2.1.2.FLt b'
  | [], _, (), (), _, _, _, _, hp => by cases hp
  | _ :: _, D, (k, ks), (v, r), hIn, hklt, hkev, p, hp => by
    simp only [dummyKeyIVals, Tup.zip, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact ⟨(congrArg Prod.fst hkev : k.fev ρ' = v), hIn.1, hklt.1⟩
    · exact symGIn_dummyKeyIVals_mem (addKey D k) ks r hIn.2 hklt.2
        (congrArg Prod.snd hkev) p hp

theorem symGIn_dummyKeyIVals {ρ ρ' : FEnv} {b b' : Nat} {D : Nat → Bool}
    {G : Ctx (IVal Val) Val} (hG : SymGIn ρ b D G) (hb : b ≤ b')
    {ts : List Ty} {ks : Tup FKey ts} {r : Tup Val ts}
    (heq : ∀ {u} (fk : FKey u), KeyIn D fk → fk.fev ρ' = fk.fev ρ)
    (hklt : fKeysLt b' ks) (hkev : fKeysEval ρ' ks = r) :
    SymGIn ρ' b' (addKeys D ks) (Tup.zip (dummyKeyIVals ts ks) r ++ G) := by
  intro p hp
  rcases List.mem_append.1 hp with hp | hp
  · exact symGIn_dummyKeyIVals_mem D ks r (fKeysIn_addKeys D ks) hklt hkev p hp
  · rcases hG p hp with ⟨h1, h2, h3⟩
    exact ⟨(heq _ h2).trans h1, keyIn_mono (addKeys_sub D ks) h2, h3.le hb⟩

theorem symGIn_oneKey {ρ ρ' : FEnv} {b b' : Nat} {D : Nat → Bool} {G : Ctx (IVal Val) Val}
    (hG : SymGIn ρ b D G) (hb : b ≤ b')
    (heq : ∀ {u} (fk : FKey u), KeyIn D fk → fk.fev ρ' = fk.fev ρ)
    {t : Ty} {v : Val t} {vn : Nat} (hkl : vn < b') (hke : ρ' t vn = v) :
    SymGIn ρ' b' (addVN D vn) (⟨t, (.imm default, .var vn), v⟩ :: G) := by
  intro p hp
  cases hp with
  | head => exact ⟨hke, by simp [KeyIn, addVN], hkl⟩
  | tail _ hm =>
    rcases hG p hm with ⟨h1, h2, h3⟩
    exact ⟨(heq _ h2).trans h1, keyIn_mono (addVN_sub D vn) h2, h3.le hb⟩

private theorem tupZip_dummyIVals_eq :
    (ts : List Ty) → (b : Nat) → (r : Tup Val ts) →
    Tup.zip (dummyIVals (V := Val) ts b) r =
      Tup.zip (dummyKeyIVals (V := Val) ts (freshFKeys ts b)) r
  | [], _, () => rfl
  | _ :: ts, b, (v, r) => by
    simp only [dummyIVals, freshFKeys, dummyKeyIVals, Tup.zip, tupZip_dummyIVals_eq ts (b + 1) r]

theorem symGIn_dummyIVals {ρ : FEnv} {b : Nat} {D : Nat → Bool} {G : Ctx (IVal Val) Val}
    (hG : SymGIn ρ b D G) (hD : ∀ {u} (fk : FKey u), KeyIn D fk → fk.FLt b)
    {ts : List Ty} (r : Tup Val ts) :
    SymGIn (fupdTup ρ b r) (b + ts.length) (addKeys D (freshFKeys ts b))
      (Tup.zip (dummyIVals (V := Val) ts b) r ++ G) := by
  rw [tupZip_dummyIVals_eq ts b r]
  exact symGIn_dummyKeyIVals hG (Nat.le_add_right _ _)
    (fun fk hk => FKey.fev_fupdTup r (hD fk hk))
    (fKeysLt_freshFKeys ts b) (fKeysEval_freshFKeys ρ ts b r)

theorem argRel_keys_lt {V₁ V₂ : Ty → Type} {G : Ctx (IVal V₁) V₂} {b : Nat}
    (hG : ∀ p ∈ G, p.2.1.2.FLt b) {ts : List Ty} {as₁ : Tup (Arg (IVal V₁)) ts}
    {as₂ : Tup (Arg V₂) ts} (h : TRel (ArgRel G) as₁ as₂) :
    fKeysLt b (tupIKeys as₁) := by
  induction h with
  | nil => trivial
  | cons ha _ ih =>
    rcases ha with ⟨hm⟩ | ⟨_⟩
    · exact ⟨hG _ hm, ih⟩
    · exact ⟨trivial, ih⟩

private theorem keysLt_dummyKeyIVals_mem {V₁ V₂ : Ty → Type} {b : Nat} :
    {ts : List Ty} → (ks : Tup FKey ts) → (vs : Tup V₂ ts) →
    fKeysLt b ks → ∀ p ∈ Tup.zip (dummyKeyIVals (V := V₁) ts ks) vs, p.2.1.2.FLt b
  | [], (), (), _, _, hp => by cases hp
  | _ :: _, (_, ks), (_, vs), hk, p, hp => by
    simp only [dummyKeyIVals, Tup.zip, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact hk.1
    · exact keysLt_dummyKeyIVals_mem ks vs hk.2 p hp

private theorem keysLt_append_dummyKeyIVals {V₁ V₂ : Ty → Type}
    {ts : List Ty} (ks : Tup FKey ts) (vs : Tup V₂ ts)
    {G : Ctx (IVal V₁) V₂} {b : Nat}
    (hk : fKeysLt b ks) (hG : ∀ p ∈ G, p.2.1.2.FLt b) :
    ∀ p ∈ Tup.zip (dummyKeyIVals (V := V₁) ts ks) vs ++ G, p.2.1.2.FLt b := fun p hp =>
  match List.mem_append.1 hp with
  | .inl hp => keysLt_dummyKeyIVals_mem ks vs hk p hp
  | .inr hp => hG p hp

private theorem argRel_ikey_flt {V₁ V₂ : Ty → Type} {G : Ctx (IVal V₁) V₂} {b : Nat}
    (hG : ∀ p ∈ G, p.2.1.2.FLt b) {t : Ty} {a₁ : Arg (IVal V₁) t} {a₂ : Arg V₂ t} :
    ArgRel G t a₁ a₂ → (ikey a₁).FLt b
  | .var hm => hG _ hm
  | .imm _ => trivial

private theorem tupIKeys_spec_of_symGIn {ρ : FEnv} {b : Nat} {D : Nat → Bool}
    {G : Ctx (IVal Val) Val} (hG : SymGIn ρ b D G) :
    {ts : List Ty} → {as₁ : Tup (Arg (IVal Val)) ts} → {as₂ : Tup (Arg Val) ts} →
    TRel (ArgRel G) as₁ as₂ →
    fKeysEval ρ (tupIKeys as₁) = vals as₂ ∧
    fKeysIn D (tupIKeys as₁) ∧
    fKeysLt b (tupIKeys as₁)
  | [], (), (), .nil => ⟨rfl, trivial, trivial⟩
  | _ :: _, (_, _), (_, _), .cons ha has => by
    rcases tupIKeys_spec_of_symGIn hG has with ⟨h1, h2, h3⟩
    cases ha with
    | var hm =>
      rcases hG _ hm with ⟨ha1, ha2, ha3⟩
      exact ⟨Prod.ext ha1 h1, ⟨ha2, h2⟩, ⟨ha3, h3⟩⟩
    | imm _ =>
      exact ⟨Prod.ext rfl h1, ⟨trivial, h2⟩, ⟨trivial, h3⟩⟩

private theorem ikey_spec_of_symGIn {ρ : FEnv} {b : Nat} {D : Nat → Bool}
    {G : Ctx (IVal Val) Val} (hG : SymGIn ρ b D G) {t : Ty}
    {a₁ : Arg (IVal Val) t} {a₂ : Arg Val t} (ha : ArgRel G t a₁ a₂) :
    (ikey a₁).fev ρ = a₂.val ∧ KeyIn D (ikey a₁) ∧ (ikey a₁).FLt b := by
  cases ha with
  | var hm => exact hG _ hm
  | imm _ => exact ⟨rfl, trivial, trivial⟩

private theorem SymGIn.congr {ρ₁ ρ₂ : FEnv} {b : Nat} {D : Nat → Bool} {G : Ctx (IVal Val) Val}
    (hG : SymGIn ρ₁ b D G) (heq : ∀ {u} (fk : FKey u), fk.FLt b → fk.fev ρ₂ = fk.fev ρ₁) :
    SymGIn ρ₂ b D G := fun p hp =>
  ⟨(heq _ (hG p hp).2.2).trans (hG p hp).1, (hG p hp).2.1, (hG p hp).2.2⟩

private theorem SymGIn.mono_b {ρ : FEnv} {b₁ b₂ : Nat} {D : Nat → Bool} {G : Ctx (IVal Val) Val}
    (hle : b₁ ≤ b₂) (hG : SymGIn ρ b₁ D G) : SymGIn ρ b₂ D G := fun p hp =>
  ⟨(hG p hp).1, (hG p hp).2.1, (hG p hp).2.2.le hle⟩

private theorem symGIn_dummyIVals_mem (ρ : FEnv) :
    (ts : List Ty) → (b : Nat) → (r : Tup Val ts) →
    ∀ p ∈ Tup.zip (dummyIVals (V := Val) ts b) r,
      p.2.1.2.fev (fupdTup ρ b r) = p.2.2 ∧
      KeyIn (fun i => decide (i < b + ts.length)) p.2.1.2 ∧
      p.2.1.2.FLt (b + ts.length)
  | [], _, (), _, hp => by cases hp
  | _ :: ts, b, (v, r), p, hp => by
    simp only [dummyIVals, Tup.zip, List.mem_cons] at hp
    rcases hp with rfl | hp
    · refine ⟨?_, ?_, ?_⟩
      · dsimp only [FKey.fev, fupdTup]
        rw [fupdTup_lt _ _ (Nat.lt_succ_self b), fupd_eq]
      · simp only [KeyIn, decide_eq_true_eq, List.length_cons]; omega
      · show b < b + (ts.length + 1); omega
    · rcases symGIn_dummyIVals_mem (fupd ρ b v) ts (b + 1) r p hp with ⟨h1, h2, h3⟩
      simp only [fupdTup, List.length_cons]
      refine ⟨h1, ?_, h3.le (by omega)⟩
      cases hk : p.2.1.2 with
      | var _ => simp only [KeyIn, hk, decide_eq_true_eq] at h2 ⊢; omega
      | imm _ => trivial

private theorem symGIn_dummyIVals_lt {ρ : FEnv} {b : Nat} {G : Ctx (IVal Val) Val}
    (hG : SymGIn ρ b (fun i => decide (i < b)) G)
    {ts : List Ty} (r : Tup Val ts) :
    SymGIn (fupdTup ρ b r) (b + ts.length) (fun i => decide (i < b + ts.length))
      (Tup.zip (dummyIVals (V := Val) ts b) r ++ G) := by
  intro p hp
  rcases List.mem_append.1 hp with hp | hp
  · exact symGIn_dummyIVals_mem ρ ts b r p hp
  · rcases hG p hp with ⟨h1, h2, h3⟩
    have hlt : b ≤ b + ts.length := Nat.le_add_right _ _
    refine ⟨(FKey.fev_fupdTup r h3).trans h1, ?_, h3.le hlt⟩
    cases hk : p.2.1.2 with
    | var _ => simp only [KeyIn, hk, decide_eq_true_eq] at h2 ⊢; omega
    | imm _ => trivial

private theorem symGIn_freshOne_lt {ρ : FEnv} {b : Nat} {G : Ctx (IVal Val) Val}
    (hG : SymGIn ρ b (fun i => decide (i < b)) G) {t : Ty} (v : Val t) :
    SymGIn (fupd ρ b v) (b + 1) (fun i => decide (i < b + 1))
      (⟨t, (.imm default, .var b), v⟩ :: G) := by
  intro p hp
  cases hp with
  | head => exact ⟨fupd_eq (ρ := ρ) (t := t) (b := b) (v := v), by simp [KeyIn], Nat.lt_succ_self _⟩
  | tail _ hm =>
    rcases hG p hm with ⟨h1, h2, h3⟩
    refine ⟨(FKey.fev_fupd v h3).trans h1, ?_, h3.le (Nat.le_succ _)⟩
    cases hk : p.2.1.2 with
    | var _ => simp only [KeyIn, hk, decide_eq_true_eq] at h2 ⊢; omega
    | imm _ => trivial

theorem checkStoreArm_tblWf {rs : List Ty} (tgt : ArmTarget) (allowNew : Bool) (base : Nat)
    {G : Ctx (IVal Val) Val} {D : Ctx (JLabel Cont) Cont}
    {e₁ : Expr (IVal Val) (JLabel Cont) rs} {e₂ : Expr Val Cont rs}
    (hwf : Wf G D e₁ e₂) :
    ∀ {letFuel loadFuel : Nat} {tbl tbl' : SymTbl} {hits : List Nat} {ap : StoreArmPlan},
    SymTblWf base tbl → (∀ p ∈ G, p.2.1.2.FLt tbl.vnNext) →
    checkStoreArm tgt allowNew letFuel loadFuel tbl hits e₁ = some (ap, tbl') →
    SymTblWf base tbl' ∧ tbl.vnNext ≤ tbl'.vnNext ∧ ap.storeAddr.FLt tbl'.vnNext ∧
      (allowNew = false → tbl'.loads = tbl.loads) := by
  induction hwf using Wf.induct with
  | let_ hop _ ih =>
    intro letFuel loadFuel tbl tbl' hits ap hTwf hLt hc
    cases hop with | mk code hargs =>
    unfold checkStoreArm at hc
    cases hs : isSafeOp code <;> rw [hs] at hc
    · simp at hc
    · cases letFuel with
      | zero => simp at hc
      | succ letFuel' =>
        simp only [↓reduceIte, Option.map_eq_some_iff] at hc
        rcases hc with ⟨⟨ap', tbl''⟩, hq, heq⟩
        cases heq
        have hka := argRel_keys_lt hLt hargs
        have hInt := symTblWf_internOp hTwf code hs (tupIKeys _) hka
        rcases ih _ (dummyVals _) hInt.1
          (keysLt_append_dummyKeyIVals _ _ hInt.2.2.1 (fun p hp => (hLt p hp).le hInt.2.1))
          hq with ⟨hTwf', hle', haLt, hloads⟩
        exact ⟨hTwf', Nat.le_trans hInt.2.1 hle', haLt, fun ha => (hloads ha).trans hInt.2.2.2.2⟩
  | load t ha _ ih =>
    intro letFuel loadFuel tbl tbl' hits ap hTwf hLt hc
    unfold checkStoreArm at hc; dsimp only at hc
    have haLt := argRel_ikey_flt hLt ha
    cases hf : findSymLoad tbl.loads t (ikey _)
    · rw [hf] at hc
      cases allowNew
      · simp at hc
      · cases loadFuel with
        | zero => simp at hc
        | succ loadFuel' =>
          simp only [↓reduceIte, Option.map_eq_some_iff] at hc
          rcases hc with ⟨⟨ap', tbl''⟩, hq, heq⟩
          cases heq
          have hTwf1 := symTblWf_loadEmit hTwf t _ haLt
          rcases ih (.imm default, .var tbl.vnNext) default hTwf1
            (fun p hp => by
              cases hp with
              | head => exact Nat.lt_succ_self _
              | tail _ hm => exact (hLt p hm).le (Nat.le_succ _)) hq with
            ⟨hTwf', hle', hst, _⟩
          exact ⟨hTwf', Nat.le_trans (Nat.le_succ _) hle', hst, fun h => by cases h⟩
    · next entry =>
      rw [hf] at hc
      simp only [Option.map_eq_some_iff] at hc
      rcases hc with ⟨⟨ap', tbl''⟩, hq, heq⟩
      cases heq
      have hmem := findSymLoad_mem tbl.loads t _ entry hf
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hmem.1
      have hvn := (hTwf.2.2.1 j entry hj).2.2.1
      rcases ih (.imm default, .var entry.vn) default hTwf
        (fun p hp => by
          cases hp with
          | head => exact hvn
          | tail _ hm => exact hLt p hm) hq with ⟨hTwf', hle', haLt, hloads⟩
      exact ⟨hTwf', hle', haLt, hloads⟩
  | store _ ha _ =>
    intro _ _ tbl tbl' _ ap hTwf hLt hc
    unfold checkStoreArm at hc
    simp only [Option.map_eq_some_iff] at hc
    rcases hc with ⟨_, _, heq⟩
    cases heq
    exact ⟨hTwf, Nat.le_refl _, argRel_ikey_flt hLt ha, fun _ => rfl⟩
  | call _ _ _ | jnz _ _ _ | jump _ _ | ret _ | exit _ _ | hlt | group _ _ =>
    intro _ _ _ _ _ _ _ _ hc
    simp [checkStoreArm] at hc

private theorem storeStepSpec_of_checkStoreArm {rs jTs : List Ty}
    (tgt : ArmTarget) (tgt2 : TermTarget rs jTs) (allowNew : Bool) (base : Nat)
    {D : Ctx (JLabel Cont) Cont}
    (htail : ∀ {G : Ctx (IVal Val) Val}
      {e₁ : Expr (IVal Val) (JLabel Cont) rs} {e₂ : Expr Val Cont rs}
      {letFuel : Nat} {p : StoreTail},
      Wf G D e₁ e₂ → checkStoreTail tgt letFuel e₁ = some p → StoreTailSpec tgt2 p e₂)
    {G : Ctx (IVal Val) Val}
    {e₁ : Expr (IVal Val) (JLabel Cont) rs} {e₂ : Expr Val Cont rs}
    (hwf : Wf G D e₁ e₂) :
    ∀ {letFuel loadFuel : Nat} {tbl tbl' : SymTbl} {Dvn : Nat → Bool} {hits : List Nat}
      {ap : StoreArmPlan} {ρ : FEnv} {Qend : List Nat → SymTbl → Prop},
    SymTblWf base tbl → SymGIn ρ tbl.vnNext Dvn G →
    checkStoreArm tgt allowNew letFuel loadFuel tbl hits e₁ = some (ap, tbl') →
    Qend ap.hitSlots tbl' →
    StoreStepSpec tgt2 ap.storeTy allowNew Qend ap.step tbl Dvn hits ap.storeAddr ρ e₂ := by
  induction hwf using Wf.induct with
  | let_ hop _ ih =>
    intro letFuel loadFuel tbl tbl' Dvn hits ap ρ Qend hTwf hSym hc hQend
    cases hop with | mk code hargs =>
    unfold checkStoreArm at hc
    cases hs : isSafeOp code <;> rw [hs] at hc
    · simp at hc
    · cases letFuel with
      | zero => simp at hc
      | succ letFuel' =>
        simp only [↓reduceIte, Option.map_eq_some_iff] at hc
        rcases hc with ⟨⟨ap', tbl''⟩, hq, heq⟩
        cases heq
        have hks := tupIKeys_spec_of_symGIn hSym hargs
        have hInt := symTblWf_internOp hTwf code hs (tupIKeys _) hks.2.2
        refine ⟨hs, tupIKeys _, hks.1, hks.2.1, hks.2.2, fun r ρ' heq hkev => ?_⟩
        exact ih _ r htail hInt.1
          (symGIn_dummyKeyIVals hSym hInt.2.1 heq hInt.2.2.1 hkev) hq hQend
  | load t ha _ ih =>
    intro letFuel loadFuel tbl tbl' Dvn hits ap ρ Qend hTwf hSym hc hQend
    unfold checkStoreArm at hc; dsimp only at hc
    have hsp := ikey_spec_of_symGIn hSym ha
    cases hf : findSymLoad tbl.loads t (ikey _)
    · rw [hf] at hc
      cases allowNew
      · simp at hc
      · cases loadFuel with
        | zero => simp at hc
        | succ loadFuel' =>
          simp only [↓reduceIte, Option.map_eq_some_iff] at hc
          rcases hc with ⟨⟨ap', tbl''⟩, hq, heq⟩
          cases heq
          have hTwf1 := symTblWf_loadEmit hTwf t _ hsp.2.2
          refine ⟨rfl, _, hsp.1, hsp.2.1, hsp.2.2, hf, fun v ρ' heq hrv => ?_⟩
          exact ih (.imm default, .var tbl.vnNext) v htail hTwf1
            (symGIn_oneKey hSym (Nat.le_succ _) heq (Nat.lt_succ_self _) hrv) hq hQend
    · next entry =>
      rw [hf] at hc
      simp only [Option.map_eq_some_iff] at hc
      rcases hc with ⟨⟨ap', tbl''⟩, hq, heq⟩
      cases heq
      have hmem := findSymLoad_mem tbl.loads t _ entry hf
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hmem.1
      have hvn := (hTwf.2.2.1 j entry hj).2.2.1
      refine ⟨_, entry, hsp.1, hsp.2.1, hsp.2.2, hf, rfl, fun v ρ' heq hrv => ?_⟩
      exact ih (.imm default, .var entry.vn) v htail hTwf
        (symGIn_oneKey hSym (Nat.le_refl _) heq hvn hrv) hq hQend
  | store _ ha hk =>
    intro _ _ tbl tbl' Dvn hits ap ρ Qend _ hSym hc hQend
    unfold checkStoreArm at hc
    simp only [Option.map_eq_some_iff] at hc
    rcases hc with ⟨tp, htp, heq⟩
    cases heq
    have hsp := ikey_spec_of_symGIn hSym ha
    exact ⟨rfl, hsp.1, hsp.2.1, hQend, htail hk htp⟩
  | call _ _ _ | jnz _ _ _ | jump _ _ | ret _ | exit _ _ | hlt | group _ _ =>
    intro _ _ _ _ _ _ _ _ _ _ _ hc _
    simp [checkStoreArm] at hc

private theorem storeDiamondSpec_of_checkStoreArms {rs jTs : List Ty}
    (bitsOnly : Bool) (tgt : ArmTarget) (tgt2 : TermTarget rs jTs) (next : Nat) (ρ : FEnv)
    {G : Ctx (IVal Val) Val} {D : Ctx (JLabel Cont) Cont}
    (htail : ∀ {G' : Ctx (IVal Val) Val}
      {e₁ : Expr (IVal Val) (JLabel Cont) rs} {e₂ : Expr Val Cont rs}
      {letFuel : Nat} {p : StoreTail},
      Wf G' D e₁ e₂ → checkStoreTail tgt letFuel e₁ = some p → StoreTailSpec tgt2 p e₂)
    {t₁ e₁ : Expr (IVal Val) (JLabel Cont) rs} {t₂ e₂ : Expr Val Cont rs}
    {sp : StoreDiamondPlan}
    (ht : Wf G D t₁ t₂) (he : Wf G D e₁ e₂)
    (hSym : SymGIn ρ next (fun i => decide (i < next)) G)
    (hsp : checkStoreArms bitsOnly tgt next t₁ e₁ = some sp) :
    StoreDiamondSpec tgt2 sp next ρ t₂ e₂ := by
  dsimp only [checkStoreArms, bind, Option.bind] at hsp
  cases h1 : checkStoreArm tgt true 12 2 ⟨next, [], []⟩ [] t₁ with
  | none => rw [h1] at hsp; simp at hsp
  | some r1 =>
    rw [h1] at hsp; dsimp only at hsp
    cases hsel : isSelectTyWith bitsOnly r1.1.storeTy with
    | false => rw [hsel] at hsp; simp [guard] at hsp
    | true =>
      rw [hsel] at hsp; simp only [guard, ↓reduceIte, Option.pure_def] at hsp
      cases h2 : checkStoreArm tgt false 12 0 r1.2 [] e₁ with
      | none => rw [h2] at hsp; simp at hsp
      | some r2 =>
        rw [h2] at hsp; dsimp only at hsp
        cases hty : tyDecEq r1.1.storeTy r2.1.storeTy with
        | isFalse _ => rw [hty] at hsp; simp at hsp
        | isTrue heqTy =>
          rw [hty] at hsp; dsimp only at hsp
          cases hfk : fKeyBeq r1.1.storeAddr r2.1.storeAddr with
          | false => rw [hfk] at hsp; simp at hsp
          | true =>
            rw [hfk] at hsp; simp only [↓reduceIte] at hsp
            cases hhit : (List.range r1.2.loads.length).all fun s => r2.1.hitSlots.contains s with
            | false => rw [hhit] at hsp; simp at hsp
            | true =>
              rw [hhit] at hsp; simp only [↓reduceIte, Option.some.injEq] at hsp
              subst hsp
              have hwf1 := checkStoreArm_tblWf tgt true next ht (symTblWf_empty next)
                (fun p hp => (hSym p hp).2.2) h1
              have hwf2 := checkStoreArm_tblWf tgt false next he hwf1.1
                (fun p hp => (hSym p hp).2.2.le hwf1.2.1) h2
              have heqAddr := fKeyBeq_iff_eq.1 hfk
              have hhits : ∀ s, s < r1.2.loads.length → s ∈ r2.1.hitSlots := by
                intro s hs
                exact List.contains_iff_mem.1 (List.all_eq_true.1 hhit s (List.mem_range.2 hs))
              refine ⟨isSelectTyWith_imp bitsOnly _ hsel, r1.2, r1.1.storeAddr,
                hwf1.1, rfl, hwf1.2.2.1, fun ρT hEq => ?_, fun ρE hEq => ?_⟩
              · exact storeStepSpec_of_checkStoreArm tgt tgt2 true next htail ht
                  (symTblWf_empty next) (hSym.congr hEq) h1 rfl
              · have hsE := storeStepSpec_of_checkStoreArm tgt tgt2 false next htail he
                  hwf1.1 ((hSym.congr hEq).mono_b hwf1.2.1) h2
                  (Qend := fun hits tbl => tbl.loads = r1.2.loads ∧
                    ∀ s, s < r1.2.loads.length → s ∈ hits) ⟨hwf2.2.2.2 rfl, hhits⟩
                rw [← heqTy, ← heqAddr] at hsE
                exact hsE

theorem storeDiamondSpec_of_checkStoreArms_tag {rs : List Ty} (bitsOnly : Bool)
    (jId : Nat) {jTs : List Ty} (l₀ j : Cont jTs) (depth : Nat) (next : Nat) (ρ : FEnv)
    {G : Ctx (IVal Val) Val} {D : Ctx (JLabel Cont) Cont}
    {t₁ e₁ : Expr (IVal Val) (JLabel Cont) rs} {t₂ e₂ : Expr Val Cont rs}
    {sp : StoreDiamondPlan}
    (ht : Wf G D t₁ t₂) (he : Wf G D e₁ e₂)
    (hD : TagContD depth D) (hj₀ : ⟨jTs, .tag jId l₀, j⟩ ∈ D)
    (hSym : SymGIn ρ next (fun i => decide (i < next)) G)
    (hsp : checkStoreArms bitsOnly (.tag jId jTs) next t₁ e₁ = some sp) :
    StoreDiamondSpec (.jump j) sp next ρ t₂ e₂ :=
  storeDiamondSpec_of_checkStoreArms bitsOnly (.tag jId jTs) (.jump j) next ρ
    (fun hwf => storeTailSpec_of_checkStoreTail_tag jId l₀ j depth hwf hD hj₀) ht he hSym hsp

theorem storeDiamondSpec_of_checkStoreArms_ret {rs : List Ty} (bitsOnly : Bool)
    (next : Nat) (ρ : FEnv) {G : Ctx (IVal Val) Val} {D : Ctx (JLabel Cont) Cont}
    {t₁ e₁ : Expr (IVal Val) (JLabel Cont) rs} {t₂ e₂ : Expr Val Cont rs}
    {sp : StoreDiamondPlan}
    (ht : Wf G D t₁ t₂) (he : Wf G D e₁ e₂)
    (hSym : SymGIn ρ next (fun i => decide (i < next)) G)
    (hsp : checkStoreArms bitsOnly .ret next t₁ e₁ = some sp) :
    StoreDiamondSpec (rs := rs) .ret sp next ρ t₂ e₂ :=
  storeDiamondSpec_of_checkStoreArms bitsOnly .ret .ret next ρ
    (fun hwf => storeTailSpec_of_checkStoreTail_ret hwf) ht he hSym hsp

theorem diamondSpec_of_checkDiamond {rs : List Ty} (bitsOnly : Bool)
    (jId : Nat) {jTs : List Ty} (j : Cont jTs) (depth : Nat)
    (next : Nat) (ρ : FEnv) (plan : DiamondPlan) {G : Ctx (IVal Val) Val}
    {D : Ctx (JLabel Cont) Cont}
    {e₁ : Expr (IVal Val) (JLabel Cont) rs} {e₂ : Expr Val Cont rs}
    (hD : TagContD depth D) (hwf : Wf G (⟨jTs, .loc jId, j⟩ :: D) e₁ e₂)
    (hSym : SymGIn ρ next (fun i => decide (i < next)) G)
    (hc : checkDiamondWith bitsOnly jId jTs next e₁ = some plan) :
    DiamondSpec j next ρ plan e₂ := by
  refine checkDiamond_peel_of_wf bitsOnly jId jTs
    (fun next' G' plan' e₂' =>
      ∀ ρ', SymGIn ρ' next' (fun i => decide (i < next')) G' → DiamondSpec j next' ρ' plan' e₂')
    (fun ih ρ' hSym' xs => ih xs _ (symGIn_dummyIVals_lt hSym' xs))
    (fun ih ρ' hSym' v => ih v _ (symGIn_freshOne_lt hSym' v))
    (fun ih ρ' hSym' => ih ρ' hSym')
    (fun ih ρ' hSym' xs => ih xs _ (symGIn_dummyIVals_lt hSym' xs))
    (fun ht he hsel ⟨_, _, h1, h2⟩ _ _ =>
      ⟨isSelectSigWith_imp bitsOnly jTs hsel,
        armSpec_of_checkArm_loc jId j depth hD ht h1,
        armSpec_of_checkArm_loc jId j depth hD he h2⟩)
    (fun ht he hsel hsp ρ' hSym' =>
      ⟨isSelectSigWith_imp bitsOnly jTs hsel,
        storeDiamondSpec_of_checkStoreArms bitsOnly (.loc jId jTs) (.jump j) _ ρ'
          (fun hwf => storeTailSpec_of_checkStoreTail_loc jId j depth hD hwf) ht he hSym' hsp⟩)
    next plan hwf hc ρ hSym

theorem bool_val_cases {c₁ : Arg (IVal Val) .bool} {c₂ : Arg Val .bool}
    (hce : (iout c₁).val = c₂.val) {P : Prop}
    (ht : c₂.val = true → (iout c₁).val = true → P)
    (hf : c₂.val = false → (iout c₁).val = false → P) : P := by
  cases h : c₂.val
  · exact hf h (hce.trans h)
  · exact ht h (hce.trans h)

private theorem hoistArm_untaken_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {jTs : List Ty} (tgt : TermTarget rs jTs) (hsel : isSelectSig jTs = true) :
    ∀ (p : ArmPlan) (next : Nat) {ρ : FEnv} {G : Ctx (IVal Val) Val} {D : Ctx (JLabel Cont) Cont}
      {e₁ : Expr (IVal Val) (JLabel Cont) rs} {e₂ : Expr Val Cont rs},
    Wf G D e₁ e₂ → ArmSpec tgt p e₂ → IGood ρ next G →
    {cont : Nat → Tup (Arg (IVal Val)) jTs → Expr Val Cont rs} →
    (∀ next' ρ' args₁ vs₂, next ≤ next' →
      (∀ {u} (k : FKey u), k.FLt next → k.fev ρ' = k.fev ρ) →
      IArgsGood ρ' next' args₁ vs₂ → wp Γ Q X (cont next' args₁) m) →
    wp Γ Q X (hoistArm jTs p next e₁ cont) m
  | .jump, next, ρ, G, D, e₁, e₂, hwf, hsp, hG, cont, hcont => by
    cases hwf with
    | @jump _ _ ts _ _ args₁ args₂ _ hargs =>
      cases tgt with
      | ret => exact False.elim hsp
      | jump j =>
        rcases hsp with ⟨rfl, rfl⟩
        rw [hoistArm_jump_eq]
        exact hcont next ρ args₁ (vals args₂) (Nat.le_refl _) (fun _ _ => rfl)
          (IArgsGood.of_trel hG hargs)
    | let_ _ _ | load _ _ _ | store _ _ _ | call _ _ _ | jnz _ _ _ | ret _ | exit _ _ | hlt
    | group _ _ => exact False.elim (by cases tgt <;> exact hsp)
  | .ret, next, ρ, G, D, e₁, e₂, hwf, hsp, hG, cont, hcont => by
    cases hwf with
    | ret hvs =>
      cases tgt with
      | jump _ => exact False.elim hsp
      | ret =>
        rw [hoistArm_ret_eq]
        exact hcont next ρ _ _ (Nat.le_refl _) (fun _ _ => rfl) (IArgsGood.of_trel hG hvs)
    | let_ _ _ | load _ _ _ | store _ _ _ | call _ _ _ | jnz _ _ _ | jump _ _ | exit _ _ | hlt
    | group _ _ => exact False.elim (by cases tgt <;> exact hsp)
  | .let_ rest, next, ρ, G, D, e₁, e₂, hwf, hsp, hG, cont, hcont => by
    cases hwf with
    | let_ hop hk =>
      cases hop with
      | @mk _ _ code args₁ args₂ hargs =>
        rcases hsp with ⟨hsafe, hsp'⟩
        dsimp only [hoistArm, wp, Op.wp]
        refine OpCode.wp_of_isSafeOp code hsafe (vals (tupIOut args₁)) fun r => ?_
        refine hoistArm_untaken_wp tgt hsel rest (next + _) (hk (freshIVals _ r next) r)
          (hsp' r) (hG.freshIVals r) fun next' ρ' args₁ vs₂ hle hev hargs' => ?_
        refine hcont next' ρ' args₁ vs₂ (Nat.le_trans (Nat.le_add_right _ _) hle)
          (fun {u} k hk => ?_) hargs'
        exact (hev k (hk.le (Nat.le_add_right _ _))).trans (FKey.fev_fupdTup r hk)
    | load _ _ _ | store _ _ _ | call _ _ _ | jnz _ _ _ | jump _ _ | ret _ | exit _ _ | hlt
    | group _ _ => exact False.elim hsp
  | .jnz pT pE, next, ρ, G, D, e₁, e₂, hwf, hsp, hG, cont, hcont => by
    cases hwf with
    | @jnz _ _ c₁ c₂ t₁ t₂ e₁' e₂' hc ht he =>
      rcases hsp with ⟨hspT, hspE⟩
      dsimp only [hoistArm]
      refine hoistArm_untaken_wp tgt hsel pT next ht hspT hG
        fun next₁ ρ₁ argsT vsT hle₁ hev₁ hargsT => ?_
      refine hoistArm_untaken_wp tgt hsel pE next₁ he hspE (hG.mono hle₁ hev₁)
        fun next₂ ρ₂ argsE vsE hle₂ hev₂ hargsE => ?_
      have hargsT₂ := iargsGood_mono hle₂ hev₂ hargsT
      refine emitSelectTupIVal_wp (iout c₁) jTs hsel ρ₂ next₂ hargsT₂ hargsE
        fun ρ₃ next₃ sel hle₃ hev₃ hsel_g => ?_
      have hle_all : next ≤ next₃ := Nat.le_trans hle₁ (Nat.le_trans hle₂ hle₃)
      have hev_all : ∀ {u} (k : FKey u), k.FLt next → k.fev ρ₃ = k.fev ρ := fun k hk =>
        (hev₃ k (hk.le (Nat.le_trans hle₁ hle₂))).trans
        ((hev₂ k (hk.le hle₁)).trans (hev₁ k hk))
      exact hcont next₃ ρ₃ sel _ hle_all hev_all hsel_g
    | let_ _ _ | load _ _ _ | store _ _ _ | call _ _ _ | jump _ _ | ret _ | exit _ _ | hlt
    | group _ _ => exact False.elim hsp

private theorem hoistArm_taken_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {jTs : List Ty} (tgt : TermTarget rs jTs) (hsel : isSelectSig jTs = true) :
    ∀ (p : ArmPlan) (next : Nat) {ρ : FEnv} {G : Ctx (IVal Val) Val} {D : Ctx (JLabel Cont) Cont}
      {e₁ : Expr (IVal Val) (JLabel Cont) rs} {e₂ : Expr Val Cont rs},
    Wf G D e₁ e₂ → ArmSpec tgt p e₂ → IGood ρ next G → wp Γ Q X e₂ m →
    {cont : Nat → Tup (Arg (IVal Val)) jTs → Expr Val Cont rs} →
    (∀ next' ρ' args₁ vs₂, next ≤ next' →
      (∀ {u} (k : FKey u), k.FLt next → k.fev ρ' = k.fev ρ) →
      IArgsGood ρ' next' args₁ vs₂ → tgt.wp Q vs₂ m → wp Γ Q X (cont next' args₁) m) →
    wp Γ Q X (hoistArm jTs p next e₁ cont) m
  | .jump, next, ρ, G, D, e₁, e₂, hwf, hsp, hG, hwp, cont, hcont => by
    cases hwf with
    | @jump _ _ ts _ _ args₁ args₂ _ hargs =>
      cases tgt with
      | ret => exact False.elim hsp
      | jump j =>
        rcases hsp with ⟨rfl, rfl⟩
        rw [hoistArm_jump_eq]
        dsimp only [wp] at hwp
        exact hcont next ρ args₁ (vals args₂) (Nat.le_refl _) (fun _ _ => rfl)
          (IArgsGood.of_trel hG hargs) hwp
    | let_ _ _ | load _ _ _ | store _ _ _ | call _ _ _ | jnz _ _ _ | ret _ | exit _ _ | hlt
    | group _ _ => exact False.elim (by cases tgt <;> exact hsp)
  | .ret, next, ρ, G, D, e₁, e₂, hwf, hsp, hG, hwp, cont, hcont => by
    cases hwf with
    | ret hvs =>
      cases tgt with
      | jump _ => exact False.elim hsp
      | ret =>
        rw [hoistArm_ret_eq]
        dsimp only [wp] at hwp
        exact hcont next ρ _ _ (Nat.le_refl _) (fun _ _ => rfl) (IArgsGood.of_trel hG hvs) hwp
    | let_ _ _ | load _ _ _ | store _ _ _ | call _ _ _ | jnz _ _ _ | jump _ _ | exit _ _ | hlt
    | group _ _ => exact False.elim (by cases tgt <;> exact hsp)
  | .let_ rest, next, ρ, G, D, e₁, e₂, hwf, hsp, hG, hwp, cont, hcont => by
    cases hwf with
    | let_ hop hk =>
      cases hop with
      | @mk _ _ code args₁ args₂ hargs =>
        rcases hsp with ⟨_, hsp'⟩
        dsimp only [hoistArm, wp, Op.wp] at hwp ⊢
        rw [TRel.iout_vals hG hargs]
        refine OpCode.wp_mono code (vals args₂) (fun r hr => ?_) hwp
        refine hoistArm_taken_wp tgt hsel rest (next + _) (hk (freshIVals _ r next) r)
          (hsp' r) (hG.freshIVals r) hr fun next' ρ' args₁ vs₂ hle hev hargs' hj => ?_
        refine hcont next' ρ' args₁ vs₂ (Nat.le_trans (Nat.le_add_right _ _) hle)
          (fun {u} k hk => ?_) hargs' hj
        exact (hev k (hk.le (Nat.le_add_right _ _))).trans (FKey.fev_fupdTup r hk)
    | load _ _ _ | store _ _ _ | call _ _ _ | jnz _ _ _ | jump _ _ | ret _ | exit _ _ | hlt
    | group _ _ => exact False.elim hsp
  | .jnz pT pE, next, ρ, G, D, e₁, e₂, hwf, hsp, hG, hwp, cont, hcont => by
    cases hwf with
    | @jnz _ _ c₁ c₂ t₁ t₂ e₁' e₂' hc ht he =>
      rcases hsp with ⟨hspT, hspE⟩
      dsimp only [hoistArm, wp] at hwp ⊢
      have hce := argRel_iout_val hG hc
      refine bool_val_cases hce (fun hcv hcv1 => ?_) (fun hcv hcv1 => ?_)
      · refine hoistArm_taken_wp tgt hsel pT next ht hspT hG (hwp.1 hcv)
          fun next₁ ρ₁ argsT vsT hle₁ hev₁ hargsT hjT => ?_
        refine hoistArm_untaken_wp tgt hsel pE next₁ he hspE (hG.mono hle₁ hev₁)
          fun next₂ ρ₂ argsE vsE hle₂ hev₂ hargsE => ?_
        have hargsT₂ := iargsGood_mono hle₂ hev₂ hargsT
        refine emitSelectTupIVal_wp (iout c₁) jTs hsel ρ₂ next₂ hargsT₂ hargsE
          fun ρ₃ next₃ sel hle₃ hev₃ hsel_g => ?_
        have hle_all : next ≤ next₃ := Nat.le_trans hle₁ (Nat.le_trans hle₂ hle₃)
        have hev_all : ∀ {u} (k : FKey u), k.FLt next → k.fev ρ₃ = k.fev ρ := fun k hk =>
          (hev₃ k (hk.le (Nat.le_trans hle₁ hle₂))).trans
          ((hev₂ k (hk.le hle₁)).trans (hev₁ k hk))
        simp only [hcv1, ↓reduceIte] at hsel_g
        exact hcont next₃ ρ₃ sel vsT hle_all hev_all hsel_g hjT
      · refine hoistArm_untaken_wp tgt hsel pT next ht hspT hG
          fun next₁ ρ₁ argsT vsT hle₁ hev₁ hargsT => ?_
        refine hoistArm_taken_wp tgt hsel pE next₁ he hspE (hG.mono hle₁ hev₁) (hwp.2 hcv)
          fun next₂ ρ₂ argsE vsE hle₂ hev₂ hargsE hjE => ?_
        have hargsT₂ := iargsGood_mono hle₂ hev₂ hargsT
        refine emitSelectTupIVal_wp (iout c₁) jTs hsel ρ₂ next₂ hargsT₂ hargsE
          fun ρ₃ next₃ sel hle₃ hev₃ hsel_g => ?_
        have hle_all : next ≤ next₃ := Nat.le_trans hle₁ (Nat.le_trans hle₂ hle₃)
        have hev_all : ∀ {u} (k : FKey u), k.FLt next → k.fev ρ₃ = k.fev ρ := fun k hk =>
          (hev₃ k (hk.le (Nat.le_trans hle₁ hle₂))).trans
          ((hev₂ k (hk.le hle₁)).trans (hev₁ k hk))
        simp only [hcv1, Bool.false_eq_true, ↓reduceIte] at hsel_g
        exact hcont next₃ ρ₃ sel vsE hle_all hev_all hsel_g hjE
    | let_ _ _ | load _ _ _ | store _ _ _ | call _ _ _ | jump _ _ | ret _ | exit _ _ | hlt
    | group _ _ => exact False.elim hsp

theorem hoistJnzArms_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {jTs : List Ty} (tgt : TermTarget rs jTs) (hsel : isSelectSig jTs = true)
    (pT pE : ArmPlan) (next : Nat) {ρ : FEnv} {G : Ctx (IVal Val) Val}
    {D : Ctx (JLabel Cont) Cont}
    {c₁ : Arg (IVal Val) .bool} {c₂ : Arg Val .bool}
    {t₁ e₁ : Expr (IVal Val) (JLabel Cont) rs} {t₂ e₂ : Expr Val Cont rs}
    (hc : ArgRel G .bool c₁ c₂) (ht : Wf G D t₁ t₂) (he : Wf G D e₁ e₂)
    (hspT : ArmSpec tgt pT t₂) (hspE : ArmSpec tgt pE e₂) (hG : IGood ρ next G)
    (hwp : wp Γ Q X (.jnz c₂ t₂ e₂) m)
    {fin : Tup (Arg Val) jTs → Expr Val Cont rs}
    (hfin : ∀ (sel : Tup (Arg Val) jTs), tgt.wp Q (vals sel) m → wp Γ Q X (fin sel) m) :
    wp Γ Q X (hoistJnzArms jTs pT pE next c₁ t₁ e₁ fin) m := by
  dsimp only [hoistJnzArms]
  dsimp only [wp] at hwp
  have hce := argRel_iout_val hG hc
  refine bool_val_cases hce (fun hcv hcv1 => ?_) (fun hcv hcv1 => ?_)
  · refine hoistArm_taken_wp tgt hsel pT next ht hspT hG (hwp.1 hcv)
      fun next₁ ρ₁ argsT vsT hle₁ hev₁ hargsT hjT => ?_
    refine hoistArm_untaken_wp tgt hsel pE next₁ he hspE (hG.mono hle₁ hev₁)
      fun next₂ ρ₂ argsE vsE hle₂ hev₂ hargsE => ?_
    have hargsT₂ := iargsGood_mono hle₂ hev₂ hargsT
    refine emitSelectTup_wp (iout c₁) jTs hsel ρ₂ next₂ hargsT₂ hargsE fun sel hsel_eq => ?_
    refine hfin sel ?_
    simpa [hsel_eq, hcv1] using hjT
  · refine hoistArm_untaken_wp tgt hsel pT next ht hspT hG
      fun next₁ ρ₁ argsT vsT hle₁ hev₁ hargsT => ?_
    refine hoistArm_taken_wp tgt hsel pE next₁ he hspE (hG.mono hle₁ hev₁) (hwp.2 hcv)
      fun next₂ ρ₂ argsE vsE hle₂ hev₂ hargsE hjE => ?_
    have hargsT₂ := iargsGood_mono hle₂ hev₂ hargsT
    refine emitSelectTup_wp (iout c₁) jTs hsel ρ₂ next₂ hargsT₂ hargsE fun sel hsel_eq => ?_
    refine hfin sel ?_
    simpa [hsel_eq, hcv1] using hjE

end IfOptImpl

end LeanQbe.T
