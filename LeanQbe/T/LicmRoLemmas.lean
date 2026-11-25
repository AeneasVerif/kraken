module

public import LeanQbe.T.Licm
public import LeanQbe.T.GvnLemmas
public import LeanQbe.T.FlatLemmas
public import LeanQbe.T.Legal
import LeanQbe.T.PassFlatKit
import LeanQbe.T.LegalPassKit

/-!
# Soundness of Read-Only Load Hoisting & Forwarding (`roSweepFunc_*`)

Proves relational `Wf`, `supportsSource`, and WP soundness (`roSweep_wf`,
`roSweep_supportsSource`, `roSweep_denote_wp`, `roSweepFunc_wf`, `roSweepFunc_spec`,
`roSweepFunc_supportsSource`) for `Licm.buildRoPlan` + `roSweep`, separated from
`LeanQbe/T/LicmLemmas.lean` to keep both proof modules concise and modular.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T

theorem castTy_some_eq {V : Ty → Type} :
    {t' t : Ty} → {v : V t'} → {v' : V t} →
    castTy t' t v = some v' → ∃ h : t' = t, h ▸ v = v' :=
  PassFlatKit.castTy_some_eq

section
variable {V₁ V₂ : Ty → Type}

/-- Pointwise relational correspondence between two lexical `VEnv` tries under `G'`. -/
def EnvRel (G' : Ctx V₁ V₂) (env₁ : VEnv V₁) (env₂ : VEnv V₂) : Prop :=
  ∀ lvl : Nat, ORel (fun p q => ∃ t v₁ v₂, p = ⟨t, v₁⟩ ∧ q = ⟨t, v₂⟩ ∧ ⟨t, v₁, v₂⟩ ∈ G')
    (env₁.find? lvl) (env₂.find? lvl)

theorem EnvRel.empty {G' : Ctx V₁ V₂} : EnvRel G' .empty .empty := fun _ => trivial

theorem EnvRel.weaken {G₁ G₂ : Ctx V₁ V₂} (hsub : ∀ p ∈ G₁, p ∈ G₂)
    {env₁ : VEnv V₁} {env₂ : VEnv V₂} (hE : EnvRel G₁ env₁ env₂) : EnvRel G₂ env₁ env₂ := by
  intro lvl
  have hl := hE lvl
  cases h1 : env₁.find? lvl <;> cases h2 : env₂.find? lvl <;> rw [h1, h2] at hl <;>
    simp only [ORel] at hl ⊢
  rcases hl with ⟨t, v₁, v₂, rfl, rfl, hm⟩
  exact ⟨t, v₁, v₂, rfl, rfl, hsub _ hm⟩

theorem EnvRel.insert {G' : Ctx V₁ V₂} {env₁ : VEnv V₁} {env₂ : VEnv V₂}
    (hE : EnvRel G' env₁ env₂) (b : Nat) {t : Ty} {v₁ : V₁ t} {v₂ : V₂ t}
    (hm : ⟨t, v₁, v₂⟩ ∈ G') : EnvRel G' (env₁.insert b ⟨t, v₁⟩) (env₂.insert b ⟨t, v₂⟩) := by
  intro lvl
  rw [Trie.find?_insert, Trie.find?_insert]
  split
  · exact ⟨t, v₁, v₂, rfl, rfl, hm⟩
  · exact hE lvl

private theorem envRel_insertTup_aux {G' : Ctx V₁ V₂} :
    {ts : List Ty} → {xs₁ : Tup V₁ ts} → {xs₂ : Tup V₂ ts} →
    {env₁ : VEnv V₁} → {env₂ : VEnv V₂} → (b : Nat) →
    (∀ p ∈ Tup.zip xs₁ xs₂, p ∈ G') →
    EnvRel G' env₁ env₂ → EnvRel G' (envInsertTup env₁ b xs₁) (envInsertTup env₂ b xs₂)
  | [], (), (), _, _, _, _, hE => hE
  | _ :: _, (_, _), (_, _), _, _, b, hsub, hE =>
    envRel_insertTup_aux (b + 1) (fun _ hp => hsub _ (List.mem_cons_of_mem _ hp))
      (hE.insert b (hsub _ List.mem_cons_self))

theorem EnvRel.insertTup {G' : Ctx V₁ V₂} {env₁ : VEnv V₁} {env₂ : VEnv V₂}
    (hE : EnvRel G' env₁ env₂) {ts : List Ty} (xs₁ : Tup V₁ ts) (xs₂ : Tup V₂ ts) (b : Nat) :
    EnvRel (Tup.zip xs₁ xs₂ ++ G') (envInsertTup env₁ b xs₁) (envInsertTup env₂ b xs₂) :=
  envRel_insertTup_aux b (fun _ hp => List.mem_append_left G' hp)
    (hE.weaken fun _ hp => List.mem_append_right _ hp)

theorem resolveArg_rel {G' : Ctx V₁ V₂} {env₁ : VEnv V₁} {env₂ : VEnv V₂}
    (hE : EnvRel G' env₁ env₂) {t : Ty} (a : Arg K t) :
    ORel (ArgRel G' t) (resolveArg env₁ a) (resolveArg env₂ a) := by
  cases a with
  | imm c => exact .imm c
  | var lvl =>
    have hl := hE lvl
    dsimp only [resolveArg]
    cases e₁ : env₁.find? lvl <;> cases e₂ : env₂.find? lvl <;> rw [e₁, e₂] at hl <;>
      simp only [ORel] at hl ⊢
    rcases hl with ⟨t', v₁, v₂, rfl, rfl, hm⟩
    have hc := castTy_rel (t := t) hm
    cases c₁ : castTy t' t v₁ <;> cases c₂ : castTy t' t v₂ <;> rw [c₁, c₂] at hc <;>
      simp only [ORel] at hc ⊢
    exact .var hc

theorem resolveArgs_rel {G' : Ctx V₁ V₂} {env₁ : VEnv V₁} {env₂ : VEnv V₂}
    (hE : EnvRel G' env₁ env₂) :
    {ts : List Ty} → (args : Tup (Arg K) ts) →
    ORel (TRel (ArgRel G')) (resolveArgs env₁ args) (resolveArgs env₂ args)
  | [], () => .nil
  | _ :: _, (a, as) => by
    have ha := resolveArg_rel hE a
    have has := resolveArgs_rel hE as
    dsimp only [resolveArgs]
    cases e₁ : resolveArg env₁ a <;> cases e₂ : resolveArg env₂ a <;> rw [e₁, e₂] at ha <;>
      simp only [ORel] at ha ⊢ <;>
      cases f₁ : resolveArgs env₁ as <;> cases f₂ : resolveArgs env₂ as <;> rw [f₁, f₂] at has <;>
      simp only [ORel] at has ⊢
    exact .cons ha has

end

theorem toTBlocks_supportsSource_get (target : LegalTarget) {rs : List Ty} (nv nl : Nat)
    {sig : List (List Ty)} (bs : Blocks K KL rs sig)
    (hs : (toTBlocks bs nv nl).supportsSource target = true)
    {ts : List Ty} (i : Member ts sig) :
    (toTFlat (bs.get i (Tup.levels ts nv)) (nv + ts.length) nl).supportsSource target = true :=
  LegalPassKit.toTBlocks_supportsSource_get target nv nl bs hs i

theorem toTBlocks_supportsSource_of_get (target : LegalTarget) {rs : List Ty} (nv nl : Nat)
    {sig : List (List Ty)} (bs : Blocks K KL rs sig)
    (hsig : sig.all (·.all target.supportsTy) = true)
    (hget : ∀ {ts : List Ty} (i : Member ts sig),
      (toTFlat (bs.get i (Tup.levels ts nv)) (nv + ts.length) nl).supportsSource target = true) :
    (toTBlocks bs nv nl).supportsSource target = true :=
  LegalPassKit.toTBlocks_supportsSource_of_get target nv nl bs hsig hget

/-! ## `roSweep` relational well-formedness (`roSweep_wf`) -/

/-- Positional projection of `RoBlocks` at block index `i`. -/
private def RoBlocks.get {sig : List (List Ty)} {ts : List Ty} :
    RoBlocks → Member ts sig → RoPlan
  | .nil, _ => .leaf
  | .cons ph _, .here => ph
  | .cons _ pt, .there i => pt.get i

private theorem roSweepB_get_eq {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (b : Nat) (env : VEnv V) :
    {sig : List (List Ty)} → (bsPlan : RoBlocks) → (bs : Blocks V L rs sig) →
    ∀ {ts : List Ty} (i : Member ts sig) (xs : Tup V ts),
      (roSweepB b env bsPlan bs).get i xs =
        roSweep (b + ts.length) (envInsertTup env b xs) (bsPlan.get i) (bs.get i xs)
  | _ :: _, .nil, .cons _ _, _, .here, _ => rfl
  | _ :: _, .cons _ _, .cons _ _, _, .here, _ => rfl
  | _ :: _, .nil, .cons _ bs, _, .there i, xs => roSweepB_get_eq b env .nil bs i xs
  | _ :: _, .cons _ pt, .cons _ bs, _, .there i, xs => roSweepB_get_eq b env pt bs i xs

private theorem roSweep_load {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (next : Nat) (env : VEnv V) (plan : RoPlan) (t : Ty) (a : Arg V i64)
    (k : V t → Expr V L rs) :
    roSweep next env plan (.load t a k) =
      match plan with
      | .fwdLoad lvl kPlan =>
        match env.find? lvl with
        | some ⟨t', v⟩ =>
          if h : t' = t then roSweep next env kPlan (k (h ▸ v))
          else .load t a fun v => roSweep (next + 1) (env.insert next ⟨t, v⟩) kPlan (k v)
        | none => .load t a fun v => roSweep (next + 1) (env.insert next ⟨t, v⟩) kPlan (k v)
      | _ =>
        let kPlan := match plan with | .node1 p => p | _ => .leaf
        .load t a fun v => roSweep (next + 1) (env.insert next ⟨t, v⟩) kPlan (k v) := by
  delta roSweep; dsimp only [Expr.brecOn, Expr.rec, roSweep._f]; cases plan <;> rfl

private theorem emitRoHoists_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {D : Ctx L₁ L₂}
    (cont₁ : Nat → VEnv V₁ → Expr V₁ L₁ rs)
    (cont₂ : Nat → VEnv V₂ → Expr V₂ L₂ rs) :
    ∀ (hoists : List HoistLoad) (b : Nat) {G' : Ctx V₁ V₂}
      (env₁ : VEnv V₁) (env₂ : VEnv V₂),
      EnvRel G' env₁ env₂ →
      (∀ b' {G'' : Ctx V₁ V₂} env₁' env₂',
        (∀ p ∈ G', p ∈ G'') → EnvRel G'' env₁' env₂' →
        Wf G'' D (cont₁ b' env₁') (cont₂ b' env₂')) →
      Wf G' D (emitRoHoists hoists b env₁ cont₁) (emitRoHoists hoists b env₂ cont₂)
  | [], b, _, env₁, env₂, hE, hcont => hcont b env₁ env₂ (fun _ hp => hp) hE
  | h :: rest, b, G', env₁, env₂, hE, hcont => by
    dsimp only [emitRoHoists]
    have hres := resolveArg_rel hE h.addr
    cases e₁ : resolveArg env₁ h.addr <;> cases e₂ : resolveArg env₂ h.addr <;>
      rw [e₁, e₂] at hres <;> simp only [ORel] at hres ⊢
    · exact emitRoHoists_wf cont₁ cont₂ rest b env₁ env₂ hE hcont
    · refine .load h.ty hres fun v₁ v₂ => ?_
      have hsub : ∀ p ∈ G', p ∈ (⟨h.ty, v₁, v₂⟩ :: G') :=
        fun _ hq => List.mem_cons_of_mem _ hq
      exact emitRoHoists_wf cont₁ cont₂ rest (b + 1)
        (env₁.insert b ⟨h.ty, v₁⟩) (env₂.insert b ⟨h.ty, v₂⟩)
        ((hE.weaken hsub).insert b List.mem_cons_self)
        fun b' G'' env₁' env₂' hsub2 hE'' =>
          hcont b' env₁' env₂' (fun p hp => hsub2 p (hsub p hp)) hE''

/-- Relational well-formedness preservation for `roSweep` under any `RoPlan`. -/
private theorem roSweep_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
    {e₁ : Expr V₁ L₁ rs} {e₂ : Expr V₂ L₂ rs}
    (hwf : Wf G D e₁ e₂) :
    ∀ {G' : Ctx V₁ V₂}, (∀ p ∈ G, p ∈ G') →
      ∀ b env₁ env₂ plan, EnvRel G' env₁ env₂ →
        Wf G' D (roSweep b env₁ plan e₁) (roSweep b env₂ plan e₂) := by
  induction hwf using Wf.induct with
  | @let_ G D ts op₁ op₂ k₁ k₂ hop _ ih =>
    intro G' hsub b env₁ env₂ plan hE
    dsimp only [roSweep]
    refine .let_ (hop.weaken hsub) fun xs₁ xs₂ => ?_
    exact ih xs₁ xs₂ (append_sub_left (Tup.zip xs₁ xs₂) hsub)
      (b + ts.length) (envInsertTup env₁ b xs₁) (envInsertTup env₂ b xs₂) _
      (hE.insertTup xs₁ xs₂ b)
  | @load G D t a₁ a₂ k₁ k₂ ha _ ih =>
    intro G' hsub b env₁ env₂ plan hE
    rw [roSweep_load, roSweep_load]
    have stepLoad : ∀ kPlan, Wf G' D
        (.load t a₁ fun v => roSweep (b + 1) (env₁.insert b ⟨t, v⟩) kPlan (k₁ v))
        (.load t a₂ fun v => roSweep (b + 1) (env₂.insert b ⟨t, v⟩) kPlan (k₂ v)) := by
      intro kPlan
      refine .load t (ha.weaken hsub) fun v₁ v₂ => ?_
      have hsub' : ∀ p ∈ G', p ∈ (⟨t, v₁, v₂⟩ :: G') :=
        fun _ hq => List.mem_cons_of_mem _ hq
      exact ih v₁ v₂ (cons_sub hsub) (b + 1)
        (env₁.insert b ⟨t, v₁⟩) (env₂.insert b ⟨t, v₂⟩) kPlan
        ((hE.weaken hsub').insert b List.mem_cons_self)
    cases plan with
    | fwdLoad lvl kPlan =>
      dsimp only
      have hl := hE lvl
      cases e₁ : env₁.find? lvl <;> cases e₂ : env₂.find? lvl <;>
        rw [e₁, e₂] at hl <;> simp only [ORel] at hl ⊢
      · exact stepLoad kPlan
      · rcases hl with ⟨t', v₁, v₂, rfl, rfl, hm⟩
        dsimp only
        split
        · next heq =>
          subst heq
          refine ih v₁ v₂ ?_ b env₁ env₂ kPlan hE
          intro p hp
          rcases List.mem_cons.1 hp with rfl | hp
          · exact hm
          · exact hsub p hp
        · exact stepLoad kPlan
    | _ => exact stepLoad _
  | store hv ha _ ih =>
    intro G' hsub b env₁ env₂ plan hE
    exact .store (hv.weaken hsub) (ha.weaken hsub) (ih hsub b env₁ env₂ _ hE)
  | call f hargs _ ih =>
    intro G' hsub b env₁ env₂ plan hE
    dsimp only [roSweep]
    refine .call f (TRel.argRel_weaken hsub hargs) fun xs₁ xs₂ => ?_
    exact ih xs₁ xs₂ (append_sub_left (Tup.zip xs₁ xs₂) hsub)
      (b + _) (envInsertTup env₁ b xs₁) (envInsertTup env₂ b xs₂) _
      (hE.insertTup xs₁ xs₂ b)
  | jnz hc _ _ iht ihe =>
    intro G' hsub b env₁ env₂ plan hE
    exact .jnz (hc.weaken hsub) (iht hsub b env₁ env₂ _ hE) (ihe hsub b env₁ env₂ _ hE)
  | jump hj hargs =>
    intro G' hsub _ _ _ _ _
    exact .jump hj (TRel.argRel_weaken hsub hargs)
  | ret hvs =>
    intro G' hsub _ _ _ _ _
    exact .ret (TRel.argRel_weaken hsub hvs)
  | exit f hargs =>
    intro G' hsub _ _ _ _ _
    exact .exit f (TRel.argRel_weaken hsub hargs)
  | hlt =>
    intro _ _ _ _ _ _ _
    exact .hlt
  | @group G D sig b₁ b₂ k₁ k₂ _ _ ihb ihk =>
    intro G' hsub b env₁ env₂ plan hE
    dsimp only [roSweep]
    refine emitRoHoists_wf _ _ _ b env₁ env₂ hE
      fun b' G'' env₁' env₂' hsub2 hE' => ?_
    have hsubAll : ∀ p ∈ G, p ∈ G'' := fun p hp => hsub2 p (hsub p hp)
    refine .group (fun Js₁ Js₂ => WfB.of_get fun i xs₁ xs₂ => ?_)
      (fun Js₁ Js₂ => ihk Js₁ Js₂ hsubAll b' env₁' env₂' _ hE')
    rw [roSweepB_get_eq, roSweepB_get_eq]
    exact ihb Js₁ Js₂ i xs₁ xs₂ (append_sub_left (Tup.zip xs₁ xs₂) hsubAll)
      (b' + _) (envInsertTup env₁' b' xs₁) (envInsertTup env₂' b' xs₂) _
      (hE'.insertTup xs₁ xs₂ b')

/-! ## `roSweep` `supportsSource` preservation -/

/-- Check that a hoisted load's type is supported by `target` and fits within 2^64 bytes. -/
private def HoistLoad.supports (target : LegalTarget) (h : HoistLoad) : Bool :=
  target.supportsTy h.ty && h.ty.bytes ≤ 2 ^ 64

mutual
/-- Check that every hoisted load in `RoPlan` is supported by `target`. -/
private def RoPlan.supports (target : LegalTarget) : RoPlan → Bool
  | .leaf => true
  | .node1 k | .fwdLoad _ k => k.supports target
  | .node2 t e => t.supports target && e.supports target
  | .groupNode hs bs k =>
    hs.all (HoistLoad.supports target) && bs.supports target && k.supports target

/-- Block-list companion of `RoPlan.supports`. -/
private def RoBlocks.supports (target : LegalTarget) : RoBlocks → Bool
  | .nil => true
  | .cons h t => h.supports target && t.supports target
end

private theorem RoBlocks.supports_get {target : LegalTarget} :
    {sig : List (List Ty)} → {ts : List Ty} → (bs : RoBlocks) → (i : Member ts sig) →
    bs.supports target = true → (bs.get i).supports target = true
  | _ :: _, _, .nil, _, _ => rfl
  | _ :: _, _, .cons _ _, .here, h => (Bool.and_eq_true _ _ ▸ h).1
  | _ :: _, _, .cons _ pt, .there i, h =>
    RoBlocks.supports_get pt i (Bool.and_eq_true _ _ ▸ h).2

private theorem RoPlan.supports_node1 {target : LegalTarget} {plan : RoPlan}
    (hplan : plan.supports target = true) :
    (match plan with | .node1 p => p | _ => .leaf).supports target = true := by
  cases plan <;> simp [RoPlan.supports] at hplan ⊢; exact hplan

private theorem scanPrefixLoads_supports (target : LegalTarget) {rs : List Ty} :
    (tf : TFlat rs) → (cap next : Nat) → (senv : List (Option Nat)) →
    (ldTbl : List (Ty × Nat × Nat)) →
    tf.supportsSource target = true →
    (Licm.scanPrefixLoads cap next senv ldTbl tf).1.all (HoistLoad.supports target) = true
  | .let_ op k, cap, next, senv, ldTbl, hsupp => by
    simp only [TFlat.supportsSource, Bool.and_eq_true] at hsupp
    dsimp only [Licm.scanPrefixLoads]
    split
    · exact scanPrefixLoads_supports target k cap next _ ldTbl hsupp.2
    · rfl
  | .load t a k, cap, next, senv, ldTbl, hsupp => by
    simp only [TFlat.supportsSource, Bool.and_eq_true] at hsupp
    dsimp only [Licm.scanPrefixLoads]
    cases Licm.mapRoAddr senv a with
    | none => rfl
    | some ka =>
      dsimp only
      split
      · exact scanPrefixLoads_supports target k cap next _ ldTbl hsupp.2
      · split
        · rfl
        · simp only [List.all, HoistLoad.supports, Bool.and_eq_true]
          exact ⟨hsupp.1, scanPrefixLoads_supports target k _ _ _ _ hsupp.2⟩
  | .store _ _ _, _, _, _, _, _ | .call _ _ _ _, _, _, _, _, _ | .jnz _ _ _, _, _, _, _, _
  | .jump _ _, _, _, _, _, _ | .ret _, _, _, _, _, _ | .exit _ _, _, _, _, _, _
  | .hlt, _, _, _, _, _ | .group _ _, _, _, _, _, _ => rfl

private theorem getBlock?_supportsSource (target : LegalTarget) {rs : List Ty} :
    {sig : List (List Ty)} → (tb : TBlocks rs sig) → (idx : Nat) → {nPars : Nat} →
    {b : TFlat rs} → tb.supportsSource target = true →
    Licm.getBlock? tb idx = some (nPars, b) → b.supportsSource target = true
  | _, .nil, _, _, _, _, hget => nomatch hget
  | _ :: _, .cons b _, 0, _, _, hsupp, hget => by
    simp only [TBlocks.supportsSource, Bool.and_eq_true] at hsupp
    cases hget; exact hsupp.1.2
  | _ :: _, .cons _ bs, idx + 1, _, _, hsupp, hget => by
    simp only [TBlocks.supportsSource, Bool.and_eq_true] at hsupp
    exact getBlock?_supportsSource target bs idx hsupp.2 hget

private theorem groupHoist_supports (target : LegalTarget) {rs : List Ty} {sig : List (List Ty)}
    (lowPress : Bool) (budget next : Nat) (env : List Nat) (ldTbl : List (Ty × Nat × Nat))
    (bodies : TBlocks rs sig) (k : TFlat rs)
    (hb : bodies.supportsSource target = true) (hk : k.supportsSource target = true) :
    let resE := if lowPress then Licm.scanPrefixLoads budget next (env.map some) ldTbl k
      else ([], ldTbl, none)
    let rem := budget - resE.1.length
    let getBlk : Nat → Option (Nat × TFlat rs) := fun j =>
      if Nat.blt j sig.length then Licm.getBlock? bodies (sig.length - 1 - j) else none
    let resB := if Nat.blt 0 rem then
        match resE.2.2.bind getBlk with
        | some (nPars, b) =>
          let p := Licm.scanPrefixLoads rem (next + resE.1.length)
            (Licm.pushNones nPars (env.map some)) resE.2.1 b
          (p.1, p.2.1)
        | none => ([], resE.2.1)
      else ([], resE.2.1)
    resE.1.all (HoistLoad.supports target) = true ∧
    resB.1.all (HoistLoad.supports target) = true := by
  dsimp only
  cases lowPress with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, Option.bind_none]
    exact ⟨rfl, by split <;> rfl⟩
  | true =>
    simp only [↓reduceIte]
    refine ⟨scanPrefixLoads_supports target k budget next (env.map some) ldTbl hk, ?_⟩
    split
    · cases hbind : (Licm.scanPrefixLoads budget next (env.map some) ldTbl k).2.2.bind
          (fun j => if Nat.blt j sig.length then
            Licm.getBlock? bodies (sig.length - 1 - j) else none) with
      | none => rfl
      | some pb =>
        rcases pb with ⟨nPars, b⟩
        cases hj : (Licm.scanPrefixLoads budget next (env.map some) ldTbl k).2.2 with
        | none => rw [hj] at hbind; cases hbind
        | some j =>
          rw [hj, Option.bind_some] at hbind
          split at hbind
          · exact scanPrefixLoads_supports target b _ _ _ _
              (getBlock?_supportsSource target bodies _ hb hbind)
          · cases hbind
    · rfl

mutual
private theorem analyzeRoTFlat_supports (target : LegalTarget) {rs : List Ty} :
    (tf : TFlat rs) → (next : Nat) → (env : List Nat) →
    (ldTbl : List (Ty × Nat × Nat)) → (inLoop : Option Licm.ReachTree) →
    tf.supportsSource target = true →
    (Licm.analyzeRoTFlat next env ldTbl inLoop tf).supports target = true
  | .let_ _ k, next, env, ldTbl, inLoop, hsupp => by
    simp only [TFlat.supportsSource, Bool.and_eq_true] at hsupp
    exact analyzeRoTFlat_supports target k _ _ ldTbl _ hsupp.2
  | .load t a k, next, env, ldTbl, inLoop, hsupp => by
    simp only [TFlat.supportsSource, Bool.and_eq_true] at hsupp
    dsimp only [Licm.analyzeRoTFlat]
    split <;> exact analyzeRoTFlat_supports target k _ _ _ _ hsupp.2
  | .store _ _ k, next, env, ldTbl, inLoop, hsupp => by
    simp only [TFlat.supportsSource, Bool.and_eq_true] at hsupp
    exact analyzeRoTFlat_supports target k next env [] _ hsupp.2
  | .call _ _ _ k, next, env, ldTbl, inLoop, hsupp => by
    simp only [TFlat.supportsSource, Bool.and_eq_true] at hsupp
    exact analyzeRoTFlat_supports target k _ _ [] _ hsupp.2
  | .jnz _ t e, next, env, ldTbl, inLoop, hsupp => by
    simp only [TFlat.supportsSource, Bool.and_eq_true] at hsupp
    simp only [Licm.analyzeRoTFlat, RoPlan.supports, Bool.and_eq_true]
    exact ⟨analyzeRoTFlat_supports target t next env ldTbl _ hsupp.1,
           analyzeRoTFlat_supports target e next env ldTbl _ hsupp.2⟩
  | .jump _ _, _, _, _, _, _ | .ret _, _, _, _, _, _
  | .exit _ _, _, _, _, _, _ | .hlt, _, _, _, _, _ => rfl
  | .group bodies k, next, env, ldTbl, inLoop, hsupp => by
    simp only [TFlat.supportsSource, Bool.and_eq_true] at hsupp
    dsimp only [Licm.analyzeRoTFlat]
    split
    · simp only [RoPlan.supports, List.all_nil, Bool.true_and, Bool.and_eq_true]
      exact ⟨analyzeRoTBlocks_supports target bodies next env [] _ false hsupp.1.2,
             analyzeRoTFlat_supports target k next env ldTbl _ hsupp.2⟩
    · split
      · simp only [RoPlan.supports, List.all_nil, Bool.true_and, Bool.and_eq_true]
        exact ⟨analyzeRoTBlocks_supports target bodies next env ldTbl _ inLoop.isSome hsupp.1.2,
               analyzeRoTFlat_supports target k next env ldTbl _ hsupp.2⟩
      · simp only [RoPlan.supports, List.all_append, Bool.and_eq_true]
        have hhs := groupHoist_supports target
          (Nat.blt (Licm.trieCard (Licm.collectOuterB 0 bodies .empty)) Licm.roLoadPressCap)
          (if Nat.blt (Licm.trieCard (Licm.collectOuterB 0 bodies .empty)) Licm.roLoadPressCap
            then Licm.roLoadPressCap - Licm.trieCard (Licm.collectOuterB 0 bodies .empty) else 0)
          next env ldTbl bodies k hsupp.1.2 hsupp.2
        exact ⟨⟨hhs, analyzeRoTBlocks_supports target bodies _ env _ _ true hsupp.1.2⟩,
               analyzeRoTFlat_supports target k _ env _ _ hsupp.2⟩

private theorem analyzeRoTBlocks_supports (target : LegalTarget) {rs : List Ty} :
    {sig : List (List Ty)} → (tb : TBlocks rs sig) → (next : Nat) → (env : List Nat) →
    (ldTbl : List (Ty × Nat × Nat)) → (rbs : Licm.ReachBlocks) → (gateReach : Bool) →
    tb.supportsSource target = true →
    (Licm.analyzeRoTBlocks next env ldTbl rbs gateReach tb).supports target = true
  | _, .nil, _, _, _, _, _, _ => rfl
  | _, .cons b bs, next, env, ldTbl, rbs, gateReach, hsupp => by
    simp only [TBlocks.supportsSource, Bool.and_eq_true] at hsupp
    simp only [Licm.analyzeRoTBlocks, RoBlocks.supports, Bool.and_eq_true]
    exact ⟨analyzeRoTFlat_supports target b _ _ ldTbl _ hsupp.1.2,
           analyzeRoTBlocks_supports target bs next env ldTbl _ gateReach hsupp.2⟩
end

private theorem emitRoHoists_supportsSource (target : LegalTarget) {rs : List Ty}
    (cont : Nat → VEnv K → Expr K KL rs) :
    ∀ (hoists : List HoistLoad) (b nv nl : Nat) (env : VEnv K),
      hoists.all (HoistLoad.supports target) = true →
      (∀ b' nv' env', (toTFlat (cont b' env') nv' nl).supportsSource target = true) →
      (toTFlat (emitRoHoists hoists b env cont) nv nl).supportsSource target = true
  | [], b, nv, _, env, _, hcont => hcont b nv env
  | h :: rest, b, nv, nl, env, hhs, hcont => by
    simp only [List.all_cons, Bool.and_eq_true] at hhs
    have hload := hhs.1
    dsimp only [HoistLoad.supports] at hload
    rw [Bool.and_eq_true] at hload
    dsimp only [emitRoHoists]
    cases resolveArg env h.addr with
    | none => exact emitRoHoists_supportsSource target cont rest b nv nl env hhs.2 hcont
    | some _ =>
      dsimp only [toTFlat, TFlat.supportsSource]; simp only [Bool.and_eq_true]
      exact ⟨hload,
        emitRoHoists_supportsSource target cont rest (b + 1) (nv + 1) nl _ hhs.2 hcont⟩

private theorem roSweep_supportsSource (target : LegalTarget) {rs : List Ty}
    {G : Ctx K K} {D : Ctx KL KL}
    {e₁ e₂ : Expr K KL rs} (hwf : Wf G D e₁ e₂) :
    ∀ b env plan nv₁ nl₁ nv₂ nl₂,
      (toTFlat e₁ nv₁ nl₁).supportsSource target = true →
      plan.supports target = true →
      (toTFlat (roSweep b env plan e₂) nv₂ nl₂).supportsSource target = true := by
  induction hwf using Wf.induct with
  | @let_ _ _ ts _ _ _ _ hop _ ih =>
    intro b env plan nv₁ nl₁ nv₂ nl₂ hsupp hplan
    cases hop with
    | mk code _ =>
      dsimp only [toTFlat, TFlat.supportsSource] at hsupp; simp only [Bool.and_eq_true] at hsupp
      dsimp only [roSweep, toTFlat, TFlat.supportsSource]; simp only [Bool.and_eq_true]
      exact ⟨hsupp.1,
        ih (Tup.levels ts nv₁) (Tup.levels ts nv₂) (b + ts.length) _ _
          (nv₁ + ts.length) nl₁ (nv₂ + ts.length) nl₂ hsupp.2 (RoPlan.supports_node1 hplan)⟩
  | @load _ _ t _ _ k₁ k₂ _ _ ih =>
    intro b env plan nv₁ nl₁ nv₂ nl₂ hsupp hplan
    dsimp only [toTFlat, TFlat.supportsSource] at hsupp; simp only [Bool.and_eq_true] at hsupp
    rw [roSweep_load]
    cases plan with
    | fwdLoad lvl kPlan =>
      simp only [RoPlan.supports] at hplan
      dsimp only
      cases env.find? lvl with
      | none =>
        dsimp only [toTFlat, TFlat.supportsSource]; simp only [Bool.and_eq_true]
        exact ⟨hsupp.1, ih nv₁ nv₂ (b + 1) _ kPlan (nv₁ + 1) nl₁ (nv₂ + 1) nl₂ hsupp.2 hplan⟩
      | some p =>
        rcases p with ⟨t', v⟩
        dsimp only
        split
        · next heq =>
          subst heq
          exact ih nv₁ v b env kPlan (nv₁ + 1) nl₁ nv₂ nl₂ hsupp.2 hplan
        · dsimp only [toTFlat, TFlat.supportsSource]; simp only [Bool.and_eq_true]
          exact ⟨hsupp.1, ih nv₁ nv₂ (b + 1) _ kPlan (nv₁ + 1) nl₁ (nv₂ + 1) nl₂ hsupp.2 hplan⟩
    | _ =>
      dsimp only [toTFlat, TFlat.supportsSource]; simp only [Bool.and_eq_true]
      exact ⟨hsupp.1,
        ih nv₁ nv₂ (b + 1) _ _ (nv₁ + 1) nl₁ (nv₂ + 1) nl₂ hsupp.2 (RoPlan.supports_node1 hplan)⟩
  | store _ _ _ ih =>
    intro b env plan nv₁ nl₁ nv₂ nl₂ hsupp hplan
    dsimp only [toTFlat, TFlat.supportsSource] at hsupp; simp only [Bool.and_eq_true] at hsupp
    dsimp only [roSweep, toTFlat, TFlat.supportsSource]; simp only [Bool.and_eq_true]
    exact ⟨hsupp.1, ih b env _ nv₁ nl₁ nv₂ nl₂ hsupp.2 (RoPlan.supports_node1 hplan)⟩
  | call f _ _ ih =>
    intro b env plan nv₁ nl₁ nv₂ nl₂ hsupp hplan
    dsimp only [toTFlat, TFlat.supportsSource] at hsupp; simp only [Bool.and_eq_true] at hsupp
    dsimp only [roSweep, toTFlat, TFlat.supportsSource]; simp only [Bool.and_eq_true]
    exact ⟨hsupp.1,
      ih (Tup.levels _ nv₁) (Tup.levels _ nv₂) (b + _) _ _
        (nv₁ + _) nl₁ (nv₂ + _) nl₂ hsupp.2 (RoPlan.supports_node1 hplan)⟩
  | jnz _ _ _ iht ihe =>
    intro b env plan nv₁ nl₁ nv₂ nl₂ hsupp hplan
    dsimp only [toTFlat, TFlat.supportsSource] at hsupp; simp only [Bool.and_eq_true] at hsupp
    have hp2 :
        let p := match plan with | .node2 pt pe => (pt, pe) | _ => (.leaf, .leaf)
        p.1.supports target = true ∧ p.2.supports target = true := by
      cases plan <;> simp only [RoPlan.supports, Bool.and_eq_true] at hplan ⊢
      · exact ⟨trivial, trivial⟩
      · exact ⟨trivial, trivial⟩
      · exact ⟨trivial, trivial⟩
      · exact hplan
      · exact ⟨trivial, trivial⟩
    dsimp only [roSweep, toTFlat, TFlat.supportsSource]
    rw [Bool.and_eq_true]
    exact ⟨iht b env _ nv₁ nl₁ nv₂ nl₂ hsupp.1 hp2.1,
           ihe b env _ nv₁ nl₁ nv₂ nl₂ hsupp.2 hp2.2⟩
  | jump _ _ => intro _ _ _ _ _ _ _ hsupp _; exact hsupp
  | ret _ => intro _ _ _ _ _ _ _ hsupp _; exact hsupp
  | exit _ _ => intro _ _ _ _ _ _ _ hsupp _; exact hsupp
  | hlt => intro _ _ _ _ _ _ _ _ _; rfl
  | @group _ _ sig b₁ _ _ _ _ _ ihb ihk =>
    intro b env plan nv₁ nl₁ nv₂ nl₂ hsupp hplan
    dsimp only [toTFlat, TFlat.supportsSource] at hsupp; simp only [Bool.and_eq_true] at hsupp
    cases plan with
    | groupNode hs bsP kP =>
      simp only [RoPlan.supports, Bool.and_eq_true] at hplan
      dsimp only [roSweep]
      refine emitRoHoists_supportsSource target _ hs b nv₂ nl₂ env hplan.1.1 fun b' nv' env' => ?_
      dsimp only [toTFlat, TFlat.supportsSource]; simp only [Bool.and_eq_true]
      refine ⟨⟨hsupp.1.1, toTBlocks_supportsSource_of_get target nv' (nl₂ + sig.length) _ hsupp.1.1
        fun {ts} i => ?_⟩,
        ihk (Tup.levels sig nl₁) (Tup.levels sig nl₂) b' env' kP nv₁ (nl₁ + sig.length)
          nv' (nl₂ + sig.length) hsupp.2 hplan.2⟩
      rw [roSweepB_get_eq]
      exact ihb (Tup.levels sig nl₁) (Tup.levels sig nl₂) i
        (Tup.levels ts nv₁) (Tup.levels ts nv') (b' + ts.length)
        (envInsertTup env' b' (Tup.levels ts nv')) (bsP.get i)
        (nv₁ + ts.length) (nl₁ + sig.length) (nv' + ts.length) (nl₂ + sig.length)
        (toTBlocks_supportsSource_get target nv₁ (nl₁ + sig.length) (b₁ (Tup.levels sig nl₁))
          hsupp.1.2 i)
        (RoBlocks.supports_get bsP i hplan.1.2)
    | _ =>
      dsimp only [roSweep, emitRoHoists, toTFlat, TFlat.supportsSource]
      simp only [Bool.and_eq_true]
      refine ⟨⟨hsupp.1.1, toTBlocks_supportsSource_of_get target nv₂ (nl₂ + sig.length) _ hsupp.1.1
        fun {ts} i => ?_⟩,
        ihk (Tup.levels sig nl₁) (Tup.levels sig nl₂) b env .leaf nv₁ (nl₁ + sig.length)
          nv₂ (nl₂ + sig.length) hsupp.2 rfl⟩
      rw [roSweepB_get_eq]
      exact ihb (Tup.levels sig nl₁) (Tup.levels sig nl₂) i
        (Tup.levels ts nv₁) (Tup.levels ts nv₂) (b + ts.length)
        (envInsertTup env b (Tup.levels ts nv₂)) (RoBlocks.nil.get i)
        (nv₁ + ts.length) (nl₁ + sig.length) (nv₂ + ts.length) (nl₂ + sig.length)
        (toTBlocks_supportsSource_get target nv₁ (nl₁ + sig.length) (b₁ (Tup.levels sig nl₁))
          hsupp.1.2 i)
        rfl

/-! ## `roSweep` weakest-precondition soundness (`roSweep_denote_wp`) -/

private def EnvBound (next : Nat) (env : VEnv Val) : Prop :=
  ∀ lvl p, env.find? lvl = some p → lvl < next

private theorem EnvBound.empty (next : Nat) : EnvBound next .empty :=
  fun _ _ h => nomatch h

private theorem EnvBound.insert_fresh {next : Nat} {env : VEnv Val}
    (hb : EnvBound next env) {t : Ty} (v : Val t) :
    EnvBound (next + 1) (env.insert next ⟨t, v⟩) := by
  intro lvl p hf
  rw [Trie.find?_insert] at hf
  split at hf
  · subst_vars; omega
  · exact Nat.lt_succ_of_lt (hb lvl p hf)

private theorem EnvBound.insertTup {next : Nat} {env : VEnv Val} (hb : EnvBound next env) :
    {ts : List Ty} → (xs : Tup Val ts) → EnvBound (next + ts.length) (envInsertTup env next xs)
  | [], () => hb
  | _ :: ts, (x, xs) => by
    dsimp only [envInsertTup]; simp only [List.length_cons]
    have h1 := (hb.insert_fresh x).insertTup xs
    rwa [show next + 1 + ts.length = next + (ts.length + 1) by omega] at h1

private theorem find?_insert_lt {α : Type} {env : Trie α} {lvl next : Nat} {v : α}
    (hlt : lvl < next) : (env.insert next v).find? lvl = env.find? lvl := by
  rw [Trie.find?_insert]
  split
  · next heq => omega
  · rfl

private theorem find?_insertTup_lt {env : VEnv Val} :
    {ts : List Ty} → (xs : Tup Val ts) → (next lvl : Nat) → lvl < next →
    (envInsertTup env next xs).find? lvl = env.find? lvl
  | [], (), _, _, _ => rfl
  | _ :: _, (x, xs), next, lvl, hlt => by
    dsimp only [envInsertTup]
    rw [find?_insertTup_lt xs (next + 1) lvl (by omega), find?_insert_lt hlt]

private def EnvVsMatch (next : Nat) (vs : List ((t : Ty) × Val t))
    (envK : List Nat) (envV : VEnv Val) : Prop :=
  envK.length = vs.length ∧
  ∀ idx t v, listGet? vs idx = some ⟨t, v⟩ →
    ∃ lvl, listGet? envK idx = some lvl ∧ lvl < next ∧ envV.find? lvl = some ⟨t, v⟩

private theorem EnvVsMatch.empty (next : Nat) : EnvVsMatch next [] [] .empty :=
  ⟨rfl, fun idx _ _ h => by cases idx <;> simp [listGet?] at h⟩

private theorem EnvVsMatch.mono {next next' : Nat} {vs : List ((t : Ty) × Val t)}
    {envK : List Nat} {envV envV' : VEnv Val}
    (hle : next ≤ next') (hkeep : ∀ lvl < next, envV'.find? lvl = envV.find? lvl)
    (hm : EnvVsMatch next vs envK envV) : EnvVsMatch next' vs envK envV' := by
  refine ⟨hm.1, fun idx t v hg => ?_⟩
  obtain ⟨lvl, hk, hlt, hf⟩ := hm.2 idx t v hg
  exact ⟨lvl, hk, Nat.lt_of_lt_of_le hlt hle, (hkeep lvl hlt).trans hf⟩

private theorem EnvVsMatch.cons_existing {next : Nat} {vs : List ((t : Ty) × Val t)}
    {envK : List Nat} {envV : VEnv Val}
    (hm : EnvVsMatch next vs envK envV) {t : Ty} {v : Val t} {lvl : Nat}
    (hlt : lvl < next) (hf : envV.find? lvl = some ⟨t, v⟩) :
    EnvVsMatch next (⟨t, v⟩ :: vs) (lvl :: envK) envV := by
  refine ⟨by simp [hm.1], fun idx u w hg => ?_⟩
  cases idx with
  | zero => cases hg; exact ⟨lvl, rfl, hlt, hf⟩
  | succ idx' => exact hm.2 idx' u w hg

private theorem EnvVsMatch.cons_fresh {next : Nat} {vs : List ((t : Ty) × Val t)}
    {envK : List Nat} {envV : VEnv Val} (hm : EnvVsMatch next vs envK envV)
    {t : Ty} (v : Val t) :
    EnvVsMatch (next + 1) (⟨t, v⟩ :: vs) (next :: envK) (envV.insert next ⟨t, v⟩) := by
  have hm' := hm.mono (Nat.le_succ next) fun l hlt =>
    find?_insert_lt (v := (⟨t, v⟩ : (u : Ty) × Val u)) hlt
  refine hm'.cons_existing (Nat.lt_succ_self next) ?_
  rw [Trie.find?_insert]; simp

private theorem EnvVsMatch.push {next : Nat} {vs : List ((t : Ty) × Val t)}
    {envK : List Nat} {envV : VEnv Val} :
    {ts : List Ty} → (xs : Tup Val ts) → EnvVsMatch next vs envK envV →
    EnvVsMatch (next + ts.length) (pushTup xs vs)
      (Licm.pushLevels ts.length next envK) (envInsertTup envV next xs)
  | [], (), hm => hm
  | _ :: ts, (x, xs), hm => by
    dsimp only [pushTup, Licm.pushLevels, envInsertTup]
    simp only [List.length_cons]
    have h1 := EnvVsMatch.push (next := next + 1) xs (hm.cons_fresh x)
    rwa [show next + 1 + ts.length = next + (ts.length + 1) by omega] at h1

private theorem listGet?_map {α β : Type} (f : α → β) :
    (xs : List α) → (idx : Nat) → listGet? (xs.map f) idx = (listGet? xs idx).map f
  | [], idx => by cases idx <;> rfl
  | _ :: _, 0 => rfl
  | _ :: xs, idx + 1 => listGet?_map f xs idx

private theorem castTy_self {V : Ty → Type} : (t : Ty) → (v : V t) → castTy t t v = some v :=
  PassFlatKit.castTy_self

private theorem castListTy_self {L : List Ty → Type} (ts : List Ty) (l : L ts) :
    castListTy ts ts l = some l :=
  PassFlatKit.castListTy_self ts l

private def ScanRel (next : Nat) (vs : List ((t : Ty) × Val t))
    (senv : List (Option Nat)) (envV : VEnv Val) : Prop :=
  senv.length = vs.length ∧
  ∀ idx lvl t v, listGet? senv idx = some (some lvl) → listGet? vs idx = some ⟨t, v⟩ →
    lvl < next ∧ envV.find? lvl = some ⟨t, v⟩

private theorem ScanRel.of_envVsMatch {next : Nat} {vs : List ((t : Ty) × Val t)}
    {envK : List Nat} {envV : VEnv Val} (hm : EnvVsMatch next vs envK envV) :
    ScanRel next vs (envK.map some) envV := by
  refine ⟨by simp [hm.1], fun idx lvl t v hs hv => ?_⟩
  obtain ⟨lvl', hk, hlt, hf⟩ := hm.2 idx t v hv
  rw [listGet?_map, hk] at hs
  cases hs; exact ⟨hlt, hf⟩

private theorem ScanRel.mono {next next' : Nat} {vs : List ((t : Ty) × Val t)}
    {senv : List (Option Nat)} {envV envV' : VEnv Val}
    (hle : next ≤ next') (hkeep : ∀ lvl < next, envV'.find? lvl = envV.find? lvl)
    (hs : ScanRel next vs senv envV) : ScanRel next' vs senv envV' := by
  refine ⟨hs.1, fun idx lvl t v hse hv => ?_⟩
  obtain ⟨hlt, hf⟩ := hs.2 idx lvl t v hse hv
  exact ⟨Nat.lt_of_lt_of_le hlt hle, (hkeep lvl hlt).trans hf⟩

private theorem ScanRel.cons_some {next : Nat} {vs : List ((t : Ty) × Val t)}
    {senv : List (Option Nat)} {envV : VEnv Val} (hs : ScanRel next vs senv envV)
    {t : Ty} {v : Val t} {lvl : Nat} (hlt : lvl < next) (hf : envV.find? lvl = some ⟨t, v⟩) :
    ScanRel next (⟨t, v⟩ :: vs) (some lvl :: senv) envV := by
  refine ⟨by simp [hs.1], fun idx lvl' u w hse hv => ?_⟩
  cases idx with
  | zero => cases hse; cases hv; exact ⟨hlt, hf⟩
  | succ idx' => exact hs.2 idx' lvl' u w hse hv

private theorem ScanRel.cons_none {next : Nat} {vs : List ((t : Ty) × Val t)}
    {senv : List (Option Nat)} {envV : VEnv Val} (hs : ScanRel next vs senv envV)
    {t : Ty} (v : Val t) :
    ScanRel next (⟨t, v⟩ :: vs) (none :: senv) envV := by
  refine ⟨by simp [hs.1], fun idx lvl u w hse hv => ?_⟩
  cases idx with
  | zero => cases hse
  | succ idx' => exact hs.2 idx' lvl u w hse hv

private theorem ScanRel.pushNones_pushTup {next : Nat} {vs : List ((t : Ty) × Val t)}
    {senv : List (Option Nat)} {envV : VEnv Val} :
    {ts : List Ty} → (xs : Tup Val ts) → ScanRel next vs senv envV →
    ScanRel next (pushTup xs vs) (Licm.pushNones ts.length senv) envV
  | [], (), hs => hs
  | _ :: _, (x, xs), hs => ScanRel.pushNones_pushTup xs (hs.cons_none x)

private def LdTableOk (m : Mem 64) (envV : VEnv Val) (next : Nat)
    (ldTbl : List (Ty × Nat × Nat)) : Prop :=
  ∀ t alvl vlvl, (t, alvl, vlvl) ∈ ldTbl →
    alvl < next ∧ vlvl < next ∧
    ∃ (va : Val i64) (vv : Val t),
      envV.find? alvl = some ⟨i64, va⟩ ∧ envV.find? vlvl = some ⟨t, vv⟩ ∧ loadVal m t va = some vv

private theorem LdTableOk.mono {m : Mem 64} {envV envV' : VEnv Val} {next next' : Nat}
    {ldTbl : List (Ty × Nat × Nat)}
    (hle : next ≤ next') (hkeep : ∀ lvl < next, envV'.find? lvl = envV.find? lvl)
    (hld : LdTableOk m envV next ldTbl) : LdTableOk m envV' next' ldTbl := by
  intro t a v hm
  obtain ⟨ha, hv, va, vv, hfa, hfv, hl⟩ := hld t a v hm
  exact ⟨Nat.lt_of_lt_of_le ha hle, Nat.lt_of_lt_of_le hv hle, va, vv,
    (hkeep a ha).trans hfa, (hkeep v hv).trans hfv, hl⟩

private theorem LdTableOk.cons {m : Mem 64} {envV : VEnv Val} {next : Nat}
    {ldTbl : List (Ty × Nat × Nat)} (hld : LdTableOk m envV next ldTbl)
    {t : Ty} {alvl vlvl : Nat} {va : Val i64} {vv : Val t}
    (ha : alvl < next) (hv : vlvl < next)
    (hfa : envV.find? alvl = some ⟨i64, va⟩) (hfv : envV.find? vlvl = some ⟨t, vv⟩)
    (hl : loadVal m t va = some vv) :
    LdTableOk m envV next ((t, alvl, vlvl) :: ldTbl) := by
  intro t' a' v' hm
  rcases List.mem_cons.1 hm with ⟨rfl, rfl, rfl⟩ | hm
  · exact ⟨ha, hv, va, vv, hfa, hfv, hl⟩
  · exact hld t' a' v' hm

private theorem lookupLd_mem :
    {ldTbl : List (Ty × Nat × Nat)} → {t : Ty} → {alvl vlvl : Nat} →
    Licm.lookupLd t alvl ldTbl = some vlvl → (t, alvl, vlvl) ∈ ldTbl
  | [], _, _, _, h => nomatch h
  | (t', a', v') :: rest, t, alvl, vlvl, h => by
    dsimp only [Licm.lookupLd] at h
    split at h
    · next heq =>
      simp only [Bool.and_eq_true, beq_iff_eq] at heq
      rcases heq with ⟨rfl, rfl⟩
      cases h
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (lookupLd_mem h)

private theorem scanRel_mapRoAddr {next : Nat} {vs : List ((t : Ty) × Val t)}
    {senv : List (Option Nat)} {envV : VEnv Val} (hs : ScanRel next vs senv envV)
    {a : Arg K i64} {ka : Arg K i64} {va : Arg Val i64}
    (hmap : Licm.mapRoAddr senv a = some ka) (hda : denoteArg vs a = some va) :
    resolveArg envV ka = some va ∧
    (∀ alvl, ka = .var alvl → alvl < next ∧ envV.find? alvl = some ⟨i64, va.val⟩) := by
  cases a with
  | imm c =>
    cases hmap; cases hda
    exact ⟨rfl, fun _ hc => nomatch hc⟩
  | var idx =>
    dsimp only [Licm.mapRoAddr] at hmap
    dsimp only [denoteArg, lookupV] at hda
    cases hv : listGet? vs idx with
    | none => simp [hv] at hda
    | some pv =>
      rcases pv with ⟨t', v'⟩
      simp only [hv] at hda
      cases hcast : castTy t' i64 v' with
      | none => simp [hcast] at hda
      | some v'' =>
        simp only [hcast, Option.some.injEq] at hda
        subst hda
        obtain ⟨rfl, rfl⟩ := castTy_some_eq hcast
        cases hse : listGet? senv idx with
        | none => simp [hse] at hmap
        | some opt =>
          cases opt with
          | none => simp [hse] at hmap
          | some lvl =>
            simp only [hse, Option.some.injEq] at hmap
            subst hmap
            obtain ⟨hlt, hf⟩ := hs.2 idx lvl i64 v' hse hv
            have hres : resolveArg envV (.var lvl) = some (.var v') := by
              dsimp only [resolveArg]; rw [hf]; dsimp only
              rw [castTy_self i64 v']
            refine ⟨hres, fun alvl hc => by cases hc; exact ⟨hlt, hf⟩⟩

private inductive EvalHoists (m : Mem 64) :
    List HoistLoad → Nat → VEnv Val → Nat → VEnv Val → Prop
  | nil {next env} : EvalHoists m [] next env next env
  | cons {h rest next env next' env' va v} :
      resolveArg env h.addr = some va →
      loadVal m h.ty va.val = some v →
      EvalHoists m rest (next + 1) (env.insert next ⟨h.ty, v⟩) next' env' →
      EvalHoists m (h :: rest) next env next' env'

private theorem EvalHoists.append {m : Mem 64} :
    {hs₁ hs₂ : List HoistLoad} → {n0 n1 n2 : Nat} → {e0 e1 e2 : VEnv Val} →
    EvalHoists m hs₁ n0 e0 n1 e1 → EvalHoists m hs₂ n1 e1 n2 e2 →
    EvalHoists m (hs₁ ++ hs₂) n0 e0 n2 e2
  | [], _, _, _, _, _, _, _, .nil, h2 => h2
  | _ :: _, _, _, _, _, _, _, _, .cons hr hl h1, h2 => .cons hr hl (h1.append h2)

private theorem EvalHoists.det {m : Mem 64} :
    {hs : List HoistLoad} → {n0 n1 n2 : Nat} → {e0 e1 e2 : VEnv Val} →
    EvalHoists m hs n0 e0 n1 e1 → EvalHoists m hs n0 e0 n2 e2 → n1 = n2 ∧ e1 = e2
  | [], _, _, _, _, _, _, .nil, .nil => ⟨rfl, rfl⟩
  | _ :: _, _, _, _, _, _, _, .cons hr1 hl1 h1, .cons hr2 hl2 h2 => by
    rw [hr1] at hr2; cases hr2
    rw [hl1] at hl2; cases hl2
    exact EvalHoists.det h1 h2

private theorem EvalHoists.le_next {m : Mem 64} :
    {hs : List HoistLoad} → {n0 n1 : Nat} → {e0 e1 : VEnv Val} →
    EvalHoists m hs n0 e0 n1 e1 → n0 ≤ n1
  | [], _, _, _, _, .nil => Nat.le_refl _
  | _ :: _, _, _, _, _, .cons _ _ h => Nat.le_trans (Nat.le_succ _) (EvalHoists.le_next h)

private theorem EvalHoists.find?_lt {m : Mem 64} :
    {hs : List HoistLoad} → {n0 n1 : Nat} → {e0 e1 : VEnv Val} →
    EvalHoists m hs n0 e0 n1 e1 → ∀ lvl < n0, e1.find? lvl = e0.find? lvl
  | [], _, _, _, _, .nil, _, _ => rfl
  | _ :: _, _, _, _, _, .cons _ _ h, lvl, hlt => by
    rw [EvalHoists.find?_lt h lvl (Nat.lt_succ_of_lt hlt), find?_insert_lt hlt]

private theorem EvalHoists.wp_emitRoHoists {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} (cont : Nat → VEnv Val → Expr Val Cont rs) :
    {hs : List HoistLoad} → {n0 n1 : Nat} → {e0 e1 : VEnv Val} →
    EvalHoists m hs n0 e0 n1 e1 →
    wp Γ Q X (cont n1 e1) m →
    wp Γ Q X (emitRoHoists hs n0 e0 cont) m
  | [], _, _, _, _, .nil, hw => hw
  | _ :: _, _, _, _, _, .cons hr hl hrest, hw => by
    dsimp only [emitRoHoists]; rw [hr]; dsimp only [wp]
    exact ⟨_, hl, EvalHoists.wp_emitRoHoists cont hrest hw⟩

private theorem scanPrefixLoads_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64}
    (hPure : ∀ {as rs : List Ty} (c : OpCode as rs),
      c.isLicmPure = true → ∀ args, ∃ r, ∀ post, c.wp args post ↔ post r) :
    (tf : TFlat rs) → (cap next : Nat) → (vs : List ((t : Ty) × Val t)) →
    (senv : List (Option Nat)) → (envV : VEnv Val) → (ldTbl : List (Ty × Nat × Nat)) →
    (ls : List ((ts : List Ty) × Cont ts)) →
    ScanRel next vs senv envV → EnvBound next envV → LdTableOk m envV next ldTbl →
    wp Γ Q X (denote Val Cont tf vs ls) m →
    let res := Licm.scanPrefixLoads cap next senv ldTbl tf
    ∃ next' envV', EvalHoists m res.1 next envV next' envV' ∧
      EnvBound next' envV' ∧ LdTableOk m envV' next' res.2.1 ∧
      ∀ j, res.2.2 = some j →
        ∃ (ts : List Ty) (args : Tup Val ts) (J : Cont ts), lookupL ls ts j = some J ∧ J args m
  | .let_ (ts := ts) op k, cap, next, vs, senv, envV, ldTbl, ls, hsc, heb, hld, hw => by
    dsimp only [Licm.scanPrefixLoads]
    split
    · next hp =>
      dsimp only [denote] at hw
      cases hda : denoteArgs vs op.args with
      | none => rw [hda] at hw; exact False.elim hw
      | some vArgs =>
        rw [hda] at hw
        dsimp only [wp, Op.wp] at hw
        obtain ⟨r, hr⟩ := hPure op.code hp (vals vArgs)
        have hwk := (hr _).1 hw
        exact scanPrefixLoads_wp hPure k cap next (pushTup r vs) (Licm.pushNones ts.length senv)
          envV ldTbl ls (hsc.pushNones_pushTup r) heb hld hwk
    · exact ⟨next, envV, .nil, heb, hld, fun _ hj => nomatch hj⟩
  | .load t a k, cap, next, vs, senv, envV, ldTbl, ls, hsc, heb, hld, hw => by
    dsimp only [Licm.scanPrefixLoads]
    cases hmap : Licm.mapRoAddr senv a with
    | none => exact ⟨next, envV, .nil, heb, hld, fun _ hj => nomatch hj⟩
    | some ka =>
      dsimp only [denote] at hw
      cases hda : denoteArg vs a with
      | none => rw [hda] at hw; exact False.elim hw
      | some va =>
        rw [hda] at hw
        dsimp only [wp] at hw
        rcases hw with ⟨v, hv, hwk⟩
        obtain ⟨hres, hka⟩ := scanRel_mapRoAddr hsc hmap hda
        dsimp only
        have hand : ∀ alvl vlvl, ka = .var alvl → Licm.lookupLd t alvl ldTbl = some vlvl →
            ∃ next' envV',
              EvalHoists m
                (Licm.scanPrefixLoads cap next (some vlvl :: senv) ldTbl k).1
                next envV next' envV' ∧
              EnvBound next' envV' ∧
              LdTableOk m envV' next'
                (Licm.scanPrefixLoads cap next (some vlvl :: senv) ldTbl k).2.1 ∧
              ∀ j, (Licm.scanPrefixLoads cap next (some vlvl :: senv) ldTbl k).2.2 = some j →
                ∃ ts args J, lookupL ls ts j = some J ∧ J args m := by
          intro alvl vlvl hkav hlkp
          obtain ⟨_, hvv, _, vv, hfa, hfv, hlv⟩ := hld t alvl vlvl (lookupLd_mem hlkp)
          obtain ⟨_, hfva⟩ := hka alvl hkav
          rw [hfa] at hfva; cases hfva
          rw [hlv] at hv; cases hv
          exact scanPrefixLoads_wp hPure k cap next (⟨t, v⟩ :: vs) (some vlvl :: senv) envV ldTbl ls
            (hsc.cons_some hvv hfv) heb hld hwk
        cases ka with
        | imm _ =>
          dsimp only
          split
          · exact ⟨next, envV, .nil, heb, hld, fun _ hj => nomatch hj⟩
          · have hsc' : ScanRel (next + 1) (⟨t, v⟩ :: vs) (some next :: senv)
                (envV.insert next ⟨t, v⟩) :=
              (hsc.mono (Nat.le_succ next)
                fun l hl => find?_insert_lt (v := (⟨t, v⟩ : (u : Ty) × Val u)) hl).cons_some
                (Nat.lt_succ_self next) (by rw [Trie.find?_insert]; simp)
            have heb' := heb.insert_fresh v
            have hld' := hld.mono (Nat.le_succ next)
              fun l hl => find?_insert_lt (v := (⟨t, v⟩ : (u : Ty) × Val u)) hl
            obtain ⟨n', e', hev, heb'', hld'', hj⟩ := scanPrefixLoads_wp hPure k (cap - 1)
              (next + 1) (⟨t, v⟩ :: vs) (some next :: senv) (envV.insert next ⟨t, v⟩) ldTbl ls
              hsc' heb' hld' hwk
            exact ⟨n', e', .cons hres hv hev, heb'', hld'', hj⟩
        | var alvl =>
          dsimp only
          cases hlkp : Licm.lookupLd t alvl ldTbl with
          | some vlvl => exact hand alvl vlvl rfl hlkp
          | none =>
            dsimp only
            split
            · exact ⟨next, envV, .nil, heb, hld, fun _ hj => nomatch hj⟩
            · obtain ⟨hal, hfa⟩ := hka alvl rfl
              have hkeep : ∀ l < next, (envV.insert next ⟨t, v⟩).find? l = envV.find? l :=
                fun l hl => find?_insert_lt hl
              have hsc' : ScanRel (next + 1) (⟨t, v⟩ :: vs) (some next :: senv)
                  (envV.insert next ⟨t, v⟩) :=
                (hsc.mono (Nat.le_succ next) hkeep).cons_some
                  (Nat.lt_succ_self next) (by rw [Trie.find?_insert]; simp)
              have heb' := heb.insert_fresh v
              have hld' := (hld.mono (Nat.le_succ next) hkeep).cons
                (Nat.lt_succ_of_lt hal) (Nat.lt_succ_self next)
                ((hkeep alvl hal).trans hfa) (by rw [Trie.find?_insert]; simp) hv
              obtain ⟨n', e', hev, heb'', hld'', hj⟩ := scanPrefixLoads_wp hPure k (cap - 1)
                (next + 1) (⟨t, v⟩ :: vs) (some next :: senv) (envV.insert next ⟨t, v⟩)
                ((t, alvl, next) :: ldTbl) ls hsc' heb' hld' hwk
              exact ⟨n', e', .cons hres hv hev, heb'', hld'', hj⟩
  | .jump (ts := ts) j args, _, next, vs, _, envV, ldTbl, ls, _, heb, hld, hw => by
    dsimp only [Licm.scanPrefixLoads]
    dsimp only [denote] at hw
    cases hJ : lookupL ls ts j with
    | none => rw [hJ] at hw; exact False.elim hw
    | some J =>
      rw [hJ] at hw
      cases hda : denoteArgs vs args with
      | none => rw [hda] at hw; exact False.elim hw
      | some vArgs =>
        rw [hda] at hw
        exact ⟨next, envV, .nil, heb, hld, fun j' hj' => by
          cases hj'; exact ⟨ts, vals vArgs, J, hJ, hw⟩⟩
  | .store _ _ _, _, next, _, _, envV, ldTbl, _, _, heb, hld, _
  | .call _ _ _ _, _, next, _, _, envV, ldTbl, _, _, heb, hld, _
  | .jnz _ _ _, _, next, _, _, envV, ldTbl, _, _, heb, hld, _
  | .ret _, _, next, _, _, envV, ldTbl, _, _, heb, hld, _
  | .exit _ _, _, next, _, _, envV, ldTbl, _, _, heb, hld, _
  | .hlt, _, next, _, _, envV, ldTbl, _, _, heb, hld, _
  | .group _ _, _, next, _, _, envV, ldTbl, _, _, heb, hld, _ =>
    ⟨next, envV, .nil, heb, hld, fun _ hj => nomatch hj⟩

private theorem not_range_bool {lo j hi : Nat} :
    ((!(Nat.ble lo j && Nat.blt j hi)) = true) ↔ ¬(lo ≤ j ∧ j < hi) := by
  have h : (Nat.ble lo j && Nat.blt j hi) = true ↔ (lo ≤ j ∧ j < hi) := by
    rw [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq]
  cases hc : (Nat.ble lo j && Nat.blt j hi) <;> rw [hc] at h
  · exact ⟨fun _ hx => Bool.false_ne_true (h.2 hx), fun _ => rfl⟩
  · exact ⟨fun hf => False.elim (Bool.false_ne_true hf), fun hn => False.elim (hn (h.1 rfl))⟩

mutual
private theorem noJumpInRange_mono (lo₁ hi₁ lo₂ hi₂ : Nat) (hlo : lo₁ ≤ lo₂) (hhi : hi₂ ≤ hi₁)
    {rs : List Ty} : (tf : TFlat rs) →
    Licm.noJumpInRange lo₁ hi₁ tf = true → Licm.noJumpInRange lo₂ hi₂ tf = true
  | .let_ _ k, h | .load _ _ k, h | .store _ _ k, h | .call _ _ _ k, h =>
    noJumpInRange_mono lo₁ hi₁ lo₂ hi₂ hlo hhi k h
  | .jnz _ t e, h => by
    simp only [Licm.noJumpInRange, Bool.and_eq_true] at h ⊢
    exact ⟨noJumpInRange_mono lo₁ hi₁ lo₂ hi₂ hlo hhi t h.1,
           noJumpInRange_mono lo₁ hi₁ lo₂ hi₂ hlo hhi e h.2⟩
  | .jump j _, h => by
    dsimp only [Licm.noJumpInRange] at h ⊢
    rw [not_range_bool] at h ⊢; omega
  | .ret _, _ | .exit _ _, _ | .hlt, _ => rfl
  | .group (sig := sig) bodies k, h => by
    simp only [Licm.noJumpInRange, Bool.and_eq_true] at h ⊢
    exact ⟨noJumpInRangeB_mono _ _ _ _ (by omega) (by omega) bodies h.1,
           noJumpInRange_mono _ _ _ _ (by omega) (by omega) k h.2⟩

private theorem noJumpInRangeB_mono (lo₁ hi₁ lo₂ hi₂ : Nat) (hlo : lo₁ ≤ lo₂) (hhi : hi₂ ≤ hi₁)
    {rs : List Ty} : {sig : List (List Ty)} → (tb : TBlocks rs sig) →
    Licm.noJumpInRangeB lo₁ hi₁ tb = true → Licm.noJumpInRangeB lo₂ hi₂ tb = true
  | _, .nil, _ => rfl
  | _, .cons b bs, h => by
    simp only [Licm.noJumpInRangeB, Bool.and_eq_true] at h ⊢
    exact ⟨noJumpInRange_mono lo₁ hi₁ lo₂ hi₂ hlo hhi b h.1,
           noJumpInRangeB_mono lo₁ hi₁ lo₂ hi₂ hlo hhi bs h.2⟩
end

mutual
private theorem memCleanReaches_mono (lo₁ hi₁ lo₂ hi₂ : Nat) (hlo : lo₁ ≤ lo₂) (hhi : hi₂ ≤ hi₁)
    {rs : List Ty} : (tf : TFlat rs) →
    Licm.memCleanReaches lo₁ hi₁ tf = true → Licm.memCleanReaches lo₂ hi₂ tf = true
  | .let_ _ k, h | .load _ _ k, h => memCleanReaches_mono lo₁ hi₁ lo₂ hi₂ hlo hhi k h
  | .store _ _ k, h | .call _ _ _ k, h => noJumpInRange_mono lo₁ hi₁ lo₂ hi₂ hlo hhi k h
  | .jnz _ t e, h => by
    simp only [Licm.memCleanReaches, Bool.and_eq_true] at h ⊢
    exact ⟨memCleanReaches_mono lo₁ hi₁ lo₂ hi₂ hlo hhi t h.1,
           memCleanReaches_mono lo₁ hi₁ lo₂ hi₂ hlo hhi e h.2⟩
  | .jump _ _, _ | .ret _, _ | .exit _ _, _ | .hlt, _ => rfl
  | .group (sig := sig) bodies k, h => by
    dsimp only [Licm.memCleanReaches] at h ⊢
    split at h
    · next hnj =>
      rw [Bool.and_eq_true] at hnj
      have hnj' : (Licm.noJumpInRangeB (lo₂ + sig.length) (hi₂ + sig.length) bodies &&
          Licm.noJumpInRange (lo₂ + sig.length) (hi₂ + sig.length) k) = true := by
        rw [Bool.and_eq_true]
        exact ⟨noJumpInRangeB_mono _ _ _ _ (by omega) (by omega) bodies hnj.1,
               noJumpInRange_mono _ _ _ _ (by omega) (by omega) k hnj.2⟩
      simp only [hnj', ↓reduceIte]
    · simp only [Bool.and_eq_true] at h
      split
      · rfl
      · rw [Bool.and_eq_true]
        exact ⟨memCleanReachesB_mono 0 _ 0 _ (Nat.le_refl 0) (by omega) bodies h.1,
               memCleanReaches_mono 0 _ 0 _ (Nat.le_refl 0) (by omega) k h.2⟩

private theorem memCleanReachesB_mono (lo₁ hi₁ lo₂ hi₂ : Nat) (hlo : lo₁ ≤ lo₂) (hhi : hi₂ ≤ hi₁)
    {rs : List Ty} : {sig : List (List Ty)} → (tb : TBlocks rs sig) →
    Licm.memCleanReachesB lo₁ hi₁ tb = true → Licm.memCleanReachesB lo₂ hi₂ tb = true
  | _, .nil, _ => rfl
  | _, .cons b bs, h => by
    simp only [Licm.memCleanReachesB, Bool.and_eq_true] at h ⊢
    exact ⟨memCleanReaches_mono lo₁ hi₁ lo₂ hi₂ hlo hhi b h.1,
           memCleanReachesB_mono lo₁ hi₁ lo₂ hi₂ hlo hhi bs h.2⟩
end

private def LsSafe {rs : List Ty} (ls_src ls_out : List ((ts : List Ty) × Cont ts))
    (tf : TFlat rs) (m : Mem 64) : Prop :=
  ls_src.length = ls_out.length ∧
  ∀ idx, match listGet? ls_src idx, listGet? ls_out idx with
    | some ⟨ts₁, j₁⟩, some ⟨ts₂, j₂⟩ =>
      ∃ h : ts₁ = ts₂,
        (∀ xs m', j₁ xs m' → (h ▸ j₂) xs m') ∨
        ((∀ xs, j₁ xs m → (h ▸ j₂) xs m) ∧ Licm.memCleanReaches idx (idx + 1) tf = true) ∨
        Licm.noJumpInRange idx (idx + 1) tf = true
    | _, _ => True

private theorem LsSafe.map_ctrl {rs₁ rs₂ : List Ty}
    {ls_src ls_out : List ((ts : List Ty) × Cont ts)}
    {tf₁ : TFlat rs₁} {tf₂ : TFlat rs₂} {m m' : Mem 64}
    (hSafe : LsSafe ls_src ls_out tf₁ m)
    (hMc : ∀ idx, Licm.memCleanReaches idx (idx + 1) tf₁ = true →
      (m' = m ∧ Licm.memCleanReaches idx (idx + 1) tf₂ = true) ∨
      Licm.noJumpInRange idx (idx + 1) tf₂ = true)
    (hNj : ∀ idx, Licm.noJumpInRange idx (idx + 1) tf₁ = true →
      Licm.noJumpInRange idx (idx + 1) tf₂ = true) :
    LsSafe ls_src ls_out tf₂ m' := by
  refine ⟨hSafe.1, fun idx => ?_⟩
  have h := hSafe.2 idx
  cases h1 : listGet? ls_src idx with
  | none => rw [h1] at h; dsimp only
  | some p1 =>
    rcases p1 with ⟨ts₁, j₁⟩
    cases h2 : listGet? ls_out idx with
    | none => rw [h1, h2] at h; dsimp only
    | some p2 =>
      rcases p2 with ⟨ts₂, j₂⟩
      rw [h1, h2] at h; dsimp only at h ⊢
      rcases h with ⟨eqt, h1' | ⟨h2a, h2b⟩ | h3⟩
      · exact ⟨eqt, Or.inl h1'⟩
      · rcases hMc idx h2b with ⟨rfl, hm⟩ | hn
        · exact ⟨eqt, Or.inr (Or.inl ⟨h2a, hm⟩)⟩
        · exact ⟨eqt, Or.inr (Or.inr hn)⟩
      · exact ⟨eqt, Or.inr (Or.inr (hNj idx h3))⟩

private theorem LsSafe.mono_ctrl {rs₁ rs₂ : List Ty}
    {ls_src ls_out : List ((ts : List Ty) × Cont ts)}
    {tf₁ : TFlat rs₁} {tf₂ : TFlat rs₂} {m : Mem 64}
    (hSafe : LsSafe ls_src ls_out tf₁ m)
    (hMc : ∀ idx, Licm.memCleanReaches idx (idx + 1) tf₁ = true →
      Licm.memCleanReaches idx (idx + 1) tf₂ = true)
    (hNj : ∀ idx, Licm.noJumpInRange idx (idx + 1) tf₁ = true →
      Licm.noJumpInRange idx (idx + 1) tf₂ = true) :
    LsSafe ls_src ls_out tf₂ m :=
  hSafe.map_ctrl (fun idx h => Or.inl ⟨rfl, hMc idx h⟩) hNj

private theorem LsSafe.to_unreach {rs₁ rs₂ : List Ty}
    {ls_src ls_out : List ((ts : List Ty) × Cont ts)}
    {tf₁ : TFlat rs₁} {tf₂ : TFlat rs₂} {m m' : Mem 64}
    (hSafe : LsSafe ls_src ls_out tf₁ m)
    (hMcNj : ∀ idx, Licm.memCleanReaches idx (idx + 1) tf₁ = true →
      Licm.noJumpInRange idx (idx + 1) tf₂ = true)
    (hNj : ∀ idx, Licm.noJumpInRange idx (idx + 1) tf₁ = true →
      Licm.noJumpInRange idx (idx + 1) tf₂ = true) :
    LsSafe ls_src ls_out tf₂ m' :=
  hSafe.map_ctrl (fun idx h => Or.inr (hMcNj idx h)) hNj

private def makeCleanJs (clean : Bool) (m₀ : Mem 64) :
    {sig : List (List Ty)} → Tup Cont sig → Tup Cont sig
  | [], () => ()
  | _ :: _, (J, Js) =>
    (fun xs m' => (clean = true → m' = m₀) → J xs m', makeCleanJs clean m₀ Js)

private def makePrefJs (P : Mem 64 → Prop) : (sig : List (List Ty)) → Nat → Tup Cont sig
  | [], _ => ()
  | _ :: sig', 0 => (fun _ m' => P m', makePrefJs (fun _ => True) sig' 0)
  | _ :: sig', n + 1 => (fun _ _ => True, makePrefJs P sig' n)

private theorem listGet?_pushTup_tail {α : Type} {f : α → Type} :
    {sig : List α} → (xs : Tup f sig) → (acc : List ((a : α) × f a)) → (idx : Nat) →
    listGet? (pushTup xs acc) (sig.length + idx) = listGet? acc idx
  | [], (), acc, idx => by simp [pushTup]
  | a :: sig', (x, xs), acc, idx => by
    dsimp only [pushTup]
    rw [show (a :: sig').length + idx = sig'.length + (idx + 1) by simp [Nat.add_assoc]; omega]
    exact listGet?_pushTup_tail xs (⟨a, x⟩ :: acc) (idx + 1)

private theorem pushTup_cleanJs_get {clean : Bool} {m₀ : Mem 64} :
    {sig : List (List Ty)} → (Js : Tup Cont sig) →
    (ls₁ ls₂ : List ((ts : List Ty) × Cont ts)) →
    (idx : Nat) → idx < sig.length →
    ∃ ts J₁ J₂,
      listGet? (pushTup (makeCleanJs clean m₀ Js) ls₁) idx = some ⟨ts, J₁⟩ ∧
      listGet? (pushTup Js ls₂) idx = some ⟨ts, J₂⟩ ∧
      (∀ xs m', J₁ xs m' = ((clean = true → m' = m₀) → J₂ xs m'))
  | [], (), _, _, idx, hlt => by simp only [List.length_nil] at hlt; omega
  | ts :: sig', (J, Js), ls₁, ls₂, idx, hlt => by
    dsimp only [makeCleanJs, pushTup]
    simp only [List.length_cons] at hlt
    by_cases hlt' : idx < sig'.length
    · exact pushTup_cleanJs_get Js (⟨ts, _⟩ :: ls₁) (⟨ts, J⟩ :: ls₂) idx hlt'
    · have heq : idx = sig'.length := by omega
      subst heq
      have h1 := listGet?_pushTup_tail (makeCleanJs clean m₀ Js)
        (⟨ts, fun xs m' => (clean = true → m' = m₀) → J xs m'⟩ :: ls₁) 0
      have h2 := listGet?_pushTup_tail Js (⟨ts, J⟩ :: ls₂) 0
      simp only [Nat.add_zero] at h1 h2
      exact ⟨ts, _, J, h1, h2, fun _ _ => rfl⟩

private theorem lookupL_pushTup_makePrefJs (P : Mem 64 → Prop) :
    {sig : List (List Ty)} → (ls : List ((ts : List Ty) × Cont ts)) →
    (j : Nat) → j < sig.length →
    {ts : List Ty} → {J : Cont ts} →
    lookupL (pushTup (makePrefJs P sig (sig.length - 1 - j)) ls) ts j = some J →
    ∀ args m', J args m' → P m'
  | [], _, j, hlt, _, _, _ => by simp only [List.length_nil] at hlt; omega
  | ts₀ :: sig', ls, j, hlt, ts, J, hl => by
    simp only [List.length_cons] at hlt hl ⊢
    by_cases hlt' : j < sig'.length
    · have hpos : sig'.length + 1 - 1 - j = (sig'.length - 1 - j) + 1 := by omega
      rw [hpos] at hl
      dsimp only [makePrefJs, pushTup] at hl
      exact lookupL_pushTup_makePrefJs P (⟨ts₀, fun _ _ => True⟩ :: ls) j hlt' hl
    · have heq : j = sig'.length := by omega
      subst heq
      have hpos : sig'.length + 1 - 1 - sig'.length = 0 := by omega
      rw [hpos] at hl
      dsimp only [makePrefJs, pushTup] at hl
      have hg := listGet?_pushTup_tail (makePrefJs (fun _ => True) sig' 0)
        (⟨ts₀, fun _ m' => P m'⟩ :: ls) 0
      simp only [Nat.add_zero] at hg
      dsimp only [lookupL] at hl
      rw [hg] at hl
      dsimp only [listGet?, castListTy] at hl
      cases hdec : listTyDecEq ts₀ ts with
      | isFalse _ => simp [hdec] at hl
      | isTrue heqt =>
        subst heqt; rw [hdec] at hl; cases hl
        exact fun _ _ hp => hp

private theorem closed_makePrefJs_true {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {vs : List ((t : Ty) × Val t)} :
    {sig : List (List Ty)} → (tb : TBlocks rs sig) →
    (ls : List ((ts : List Ty) × Cont ts)) → (pos : Nat) →
    Closed Γ Q X (denoteB Val Cont tb vs ls) (makePrefJs (fun _ => True) sig pos)
  | [], .nil, _, _ => trivial
  | _ :: _, .cons _ bs, ls, 0 => ⟨fun _ _ _ => trivial, closed_makePrefJs_true bs ls 0⟩
  | _ :: _, .cons _ bs, ls, n + 1 => ⟨fun _ _ _ => trivial, closed_makePrefJs_true bs ls n⟩

private theorem closed_makePrefJs_at {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (hPure : ∀ {as rs : List Ty} (c : OpCode as rs),
      c.isLicmPure = true → ∀ args, ∃ r, ∀ post, c.wp args post ↔ post r)
    (cap next : Nat) (senv : List (Option Nat)) (envV : VEnv Val)
    (ldTbl : List (Ty × Nat × Nat)) (m₀ : Mem 64)
    (vs : List ((t : Ty) × Val t))
    (hsc : ScanRel next vs senv envV) (heb : EnvBound next envV)
    (hld : LdTableOk m₀ envV next ldTbl) :
    {sig : List (List Ty)} → (tb : TBlocks rs sig) → (pos : Nat) →
    (ls : List ((ts : List Ty) × Cont ts)) →
    let P := fun m' => m' = m₀ →
      match Licm.getBlock? tb pos with
      | some (nPars, b) =>
        let res := Licm.scanPrefixLoads cap next (Licm.pushNones nPars senv) ldTbl b
        ∃ next' envV', EvalHoists m₀ res.1 next envV next' envV' ∧
          EnvBound next' envV' ∧ LdTableOk m₀ envV' next' res.2.1
      | none => True
    Closed Γ Q X (denoteB Val Cont tb vs ls) (makePrefJs P sig pos)
  | [], .nil, _, _ => trivial
  | ts :: _, .cons b bs, 0, ls => by
    refine ⟨fun xs m' hwb hm' => ?_, closed_makePrefJs_true bs ls 0⟩
    subst hm'
    dsimp only [Licm.getBlock?]
    obtain ⟨n', e', hev, heb', hld', _⟩ := scanPrefixLoads_wp hPure b cap next
      (pushTup xs vs) (Licm.pushNones ts.length senv) envV ldTbl ls
      (hsc.pushNones_pushTup xs) heb hld hwb
    exact ⟨n', e', hev, heb', hld'⟩
  | _ :: _, .cons _ bs, pos + 1, ls => by
    refine ⟨fun _ _ _ => trivial, ?_⟩
    exact closed_makePrefJs_at hPure cap next senv envV ldTbl m₀ vs hsc heb hld bs pos ls

private theorem LsSafe.push_group_arm {rs : List Ty} {sig : List (List Ty)}
    {bodies : TBlocks rs sig} {k : TFlat rs} {tf' : TFlat rs}
    {ls_src ls_out : List ((ts : List Ty) × Cont ts)} {m₀ m' : Mem 64}
    (cleanGroup : Bool) (Js_out : Tup Cont sig)
    (hSafe : LsSafe ls_src ls_out (.group bodies k) m₀)
    (hhead : cleanGroup = true →
      m' = m₀ ∧ ∀ idx, idx < sig.length → Licm.memCleanReaches idx (idx + 1) tf' = true)
    (htail_nj : ∀ idx,
      Licm.noJumpInRangeB (idx + sig.length) (idx + 1 + sig.length) bodies = true →
      Licm.noJumpInRange (idx + sig.length) (idx + 1 + sig.length) k = true →
      Licm.noJumpInRange (sig.length + idx) (sig.length + idx + 1) tf' = true)
    (htail_mc : ∀ idx,
      Licm.memCleanReachesB 0 (idx + 1 + sig.length) bodies = true →
      Licm.memCleanReaches 0 (idx + 1 + sig.length) k = true →
      m' = m₀ ∧ Licm.memCleanReaches (sig.length + idx) (sig.length + idx + 1) tf' = true) :
    LsSafe (pushTup (makeCleanJs cleanGroup m₀ Js_out) ls_src)
      (pushTup Js_out ls_out) tf' m' := by
  refine ⟨by rw [pushTup_length, pushTup_length, hSafe.1], fun idx' => ?_⟩
  by_cases hlt : idx' < sig.length
  · obtain ⟨ts, J₁, J₂, hg1, hg2, heqJ⟩ := pushTup_cleanJs_get Js_out ls_src ls_out idx' hlt
    rw [hg1, hg2]; dsimp only
    refine ⟨rfl, ?_⟩
    by_cases hcg : cleanGroup = true
    · obtain ⟨hm_eq, hmc⟩ := hhead hcg
      refine Or.inr (Or.inl ⟨fun xs hj => ?_, hmc idx' hlt⟩)
      rw [heqJ xs m'] at hj; exact hj fun _ => hm_eq
    · refine Or.inl fun xs m'' hj => ?_
      rw [heqJ xs m''] at hj; exact hj fun hc => False.elim (hcg hc)
  · have hidx : idx' = sig.length + (idx' - sig.length) := by omega
    rw [hidx, listGet?_pushTup_tail, listGet?_pushTup_tail]
    have h := hSafe.2 (idx' - sig.length)
    cases h1 : listGet? ls_src (idx' - sig.length) with
    | none => rw [h1] at h; dsimp only
    | some p1 =>
      rcases p1 with ⟨ts₁, j₁⟩
      cases h2 : listGet? ls_out (idx' - sig.length) with
      | none => rw [h1, h2] at h; dsimp only
      | some p2 =>
        rcases p2 with ⟨ts₂, j₂⟩
        rw [h1, h2] at h; dsimp only at h ⊢
        rcases h with ⟨eqt, h1' | ⟨h2a, h2b⟩ | h3⟩
        · exact ⟨eqt, Or.inl h1'⟩
        · dsimp only [Licm.memCleanReaches] at h2b
          split at h2b
          · next hnj =>
            rw [Bool.and_eq_true] at hnj
            exact ⟨eqt, Or.inr (Or.inr (htail_nj _ hnj.1 hnj.2))⟩
          · rw [Bool.and_eq_true] at h2b
            obtain ⟨hm_eq, hmc'⟩ := htail_mc _ h2b.1 h2b.2
            exact ⟨eqt, Or.inr (Or.inl ⟨fun xs => hm_eq ▸ h2a xs, hmc'⟩)⟩
        · simp only [Licm.noJumpInRange, Bool.and_eq_true] at h3
          exact ⟨eqt, Or.inr (Or.inr (htail_nj _ h3.1 h3.2))⟩

private theorem LsSafe.push_group_blk {rs : List Ty} {sig : List (List Ty)}
    {bodies : TBlocks rs sig} {k : TFlat rs}
    {ls_src ls_out : List ((ts : List Ty) × Cont ts)} {m₀ m' : Mem 64}
    (cleanGroup : Bool) (Js_out : Tup Cont sig)
    (hSafe : LsSafe ls_src ls_out (.group bodies k) m₀)
    (hm_clean : cleanGroup = true → m' = m₀)
    {b_tf : TFlat rs}
    (hb_nj : ∀ lo hi, Licm.noJumpInRangeB lo hi bodies = true →
      Licm.noJumpInRange lo hi b_tf = true)
    (hb_mc : ∀ lo hi, Licm.memCleanReachesB lo hi bodies = true →
      Licm.memCleanReaches lo hi b_tf = true)
    (hCleanB : cleanGroup = true → Licm.memCleanReachesB 0 sig.length bodies = true)
    (hCleanDef : Licm.memCleanReachesB 0 sig.length bodies = true →
      Licm.memCleanReaches 0 sig.length k = true → cleanGroup = true) :
    LsSafe (pushTup (makeCleanJs cleanGroup m₀ Js_out) ls_src)
      (pushTup Js_out ls_out) b_tf m' :=
  LsSafe.push_group_arm cleanGroup Js_out hSafe
    (fun hcg => ⟨hm_clean hcg, fun idx hlt => hb_mc _ _
      (memCleanReachesB_mono 0 sig.length idx (idx + 1) (Nat.zero_le idx) hlt bodies
        (hCleanB hcg))⟩)
    (fun idx hb _ => hb_nj _ _ (noJumpInRangeB_mono _ _ _ _ (by omega) (by omega) bodies hb))
    (fun idx hb hk => ⟨hm_clean (hCleanDef
        (memCleanReachesB_mono 0 _ 0 sig.length (Nat.le_refl 0) (by omega) bodies hb)
        (memCleanReaches_mono 0 _ 0 sig.length (Nat.le_refl 0) (by omega) k hk)),
      hb_mc _ _ (memCleanReachesB_mono 0 _ (sig.length + idx) (sig.length + idx + 1)
        (by omega) (by omega) bodies hb)⟩)

private theorem LsSafe.push_group_k {rs : List Ty} {sig : List (List Ty)}
    {bodies : TBlocks rs sig} {k : TFlat rs}
    {ls_src ls_out : List ((ts : List Ty) × Cont ts)} {m₀ : Mem 64}
    (cleanGroup : Bool) (Js_out : Tup Cont sig)
    (hSafe : LsSafe ls_src ls_out (.group bodies k) m₀)
    (hCleanK : cleanGroup = true → Licm.memCleanReaches 0 sig.length k = true) :
    LsSafe (pushTup (makeCleanJs cleanGroup m₀ Js_out) ls_src) (pushTup Js_out ls_out) k m₀ :=
  LsSafe.push_group_arm cleanGroup Js_out hSafe
    (fun hcg => ⟨rfl, fun idx hlt =>
      memCleanReaches_mono 0 sig.length idx (idx + 1) (Nat.zero_le idx) hlt k (hCleanK hcg)⟩)
    (fun idx _ hk => noJumpInRange_mono _ _ _ _ (by omega) (by omega) k hk)
    (fun idx _ hk => ⟨rfl,
      memCleanReaches_mono 0 _ (sig.length + idx) (sig.length + idx + 1)
        (by omega) (by omega) k hk⟩)

private def LsSafeB {rs : List Ty} (ls_src ls_out : List ((ts : List Ty) × Cont ts)) :
    {sig : List (List Ty)} → TBlocks rs sig → Mem 64 → Prop
  | _, .nil, _ => True
  | _, .cons b bs, m => LsSafe ls_src ls_out b m ∧ LsSafeB ls_src ls_out bs m

private theorem lsSafeB_push_group_aux {rs : List Ty} {sig₀ : List (List Ty)}
    {bodies : TBlocks rs sig₀} {k : TFlat rs}
    {ls_src ls_out : List ((ts : List Ty) × Cont ts)} {m₀ m' : Mem 64}
    (cleanGroup : Bool) (Js_out : Tup Cont sig₀)
    (hSafe : LsSafe ls_src ls_out (.group bodies k) m₀)
    (hm_clean : cleanGroup = true → m' = m₀)
    (hCleanB : cleanGroup = true → Licm.memCleanReachesB 0 sig₀.length bodies = true)
    (hCleanDef : Licm.memCleanReachesB 0 sig₀.length bodies = true →
      Licm.memCleanReaches 0 sig₀.length k = true → cleanGroup = true) :
    {sig : List (List Ty)} → (tb : TBlocks rs sig) →
    (∀ lo hi, Licm.noJumpInRangeB lo hi bodies = true → Licm.noJumpInRangeB lo hi tb = true) →
    (∀ lo hi, Licm.memCleanReachesB lo hi bodies = true → Licm.memCleanReachesB lo hi tb = true) →
    LsSafeB (pushTup (makeCleanJs cleanGroup m₀ Js_out) ls_src)
      (pushTup Js_out ls_out) tb m'
  | _, .nil, _, _ => trivial
  | _, .cons b bs, hnj, hmc => by
    have hnj_b : ∀ lo hi, Licm.noJumpInRangeB lo hi bodies = true →
        Licm.noJumpInRange lo hi b = true := by
      intro lo hi h; exact (Bool.and_eq_true _ _ ▸ hnj lo hi h).1
    have hmc_b : ∀ lo hi, Licm.memCleanReachesB lo hi bodies = true →
        Licm.memCleanReaches lo hi b = true := by
      intro lo hi h; exact (Bool.and_eq_true _ _ ▸ hmc lo hi h).1
    have hnj_bs : ∀ lo hi, Licm.noJumpInRangeB lo hi bodies = true →
        Licm.noJumpInRangeB lo hi bs = true := by
      intro lo hi h; exact (Bool.and_eq_true _ _ ▸ hnj lo hi h).2
    have hmc_bs : ∀ lo hi, Licm.memCleanReachesB lo hi bodies = true →
        Licm.memCleanReachesB lo hi bs = true := by
      intro lo hi h; exact (Bool.and_eq_true _ _ ▸ hmc lo hi h).2
    exact ⟨LsSafe.push_group_blk cleanGroup Js_out hSafe hm_clean hnj_b hmc_b hCleanB hCleanDef,
      lsSafeB_push_group_aux cleanGroup Js_out hSafe hm_clean hCleanB hCleanDef bs hnj_bs hmc_bs⟩

private theorem listGet?_some_of_lt {α : Type} :
    {xs : List α} → {idx : Nat} → idx < xs.length → ∃ x, listGet? xs idx = some x
  | [], idx, hlt => by simp only [List.length_nil] at hlt; omega
  | x :: _, 0, _ => ⟨x, rfl⟩
  | _ :: xs, idx + 1, hlt => by
    simp only [List.length_cons] at hlt
    exact listGet?_some_of_lt (xs := xs) (idx := idx) (by omega)

private theorem listGet?_lt_length {α : Type} :
    {xs : List α} → {idx : Nat} → {x : α} → listGet? xs idx = some x → idx < xs.length
  | [], idx, _, h => by cases idx <;> cases h
  | _ :: _, 0, _, _ => Nat.zero_lt_succ _
  | _ :: xs, idx + 1, _, h => Nat.succ_lt_succ (listGet?_lt_length h)

private theorem EvalHoists.len {m : Mem 64} :
    {hs : List HoistLoad} → {n0 n1 : Nat} → {e0 e1 : VEnv Val} →
    EvalHoists m hs n0 e0 n1 e1 → n1 = n0 + hs.length
  | [], _, _, _, _, .nil => rfl
  | _ :: rest, _, _, _, _, .cons _ _ h => by
    have ih := EvalHoists.len h
    simp only [List.length_cons]; omega

private theorem groupHoist_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    (hPure : ∀ {as rs : List Ty} (c : OpCode as rs),
      c.isLicmPure = true → ∀ args, ∃ r, ∀ post, c.wp args post ↔ post r)
    {sig : List (List Ty)} (lowPress : Bool) (budget next : Nat)
    (vs : List ((t : Ty) × Val t)) (envK : List Nat) (envV : VEnv Val)
    (ldTbl : List (Ty × Nat × Nat)) (bodies : TBlocks rs sig) (k : TFlat rs)
    (ls_src : List ((ts : List Ty) × Cont ts))
    (hm : EnvVsMatch next vs envK envV) (heb : EnvBound next envV)
    (hld : LdTableOk m envV next ldTbl)
    (hw : ∀ Js, Closed Γ Q X (denoteB Val Cont bodies vs (pushTup Js ls_src)) Js →
      wp Γ Q X (denote Val Cont k vs (pushTup Js ls_src)) m) :
    let resE := if lowPress then Licm.scanPrefixLoads budget next (envK.map some) ldTbl k
      else ([], ldTbl, none)
    let rem := budget - resE.1.length
    let getBlk : Nat → Option (Nat × TFlat rs) := fun j =>
      if Nat.blt j sig.length then Licm.getBlock? bodies (sig.length - 1 - j) else none
    let resB := if Nat.blt 0 rem then
        match resE.2.2.bind getBlk with
        | some (nPars, b) =>
          let p := Licm.scanPrefixLoads rem (next + resE.1.length)
            (Licm.pushNones nPars (envK.map some)) resE.2.1 b
          (p.1, p.2.1)
        | none => ([], resE.2.1)
      else ([], resE.2.1)
    ∃ nextB envV_B, EvalHoists m (resE.1 ++ resB.1) next envV nextB envV_B ∧
      EnvBound nextB envV_B ∧ LdTableOk m envV_B nextB resB.2 := by
  dsimp only
  cases hlp : lowPress with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, Option.bind_none, List.nil_append]
    split <;> exact ⟨next, envV, .nil, heb, hld⟩
  | true =>
    simp only [↓reduceIte]
    let senv := envK.map some
    have hw0 := hw (makePrefJs (fun _ => True) sig 0)
      (closed_makePrefJs_true bodies (pushTup (makePrefJs (fun _ => True) sig 0) ls_src) 0)
    obtain ⟨nextE, envV_E, hevE, hebE, hldE, _⟩ := scanPrefixLoads_wp hPure k budget next vs senv
      envV ldTbl (pushTup (makePrefJs (fun _ => True) sig 0) ls_src)
      (ScanRel.of_envVsMatch hm) heb hld hw0
    have heqNE : nextE = next + (Licm.scanPrefixLoads budget next senv ldTbl k).1.length :=
      hevE.len
    let getBlk : Nat → Option (Nat × TFlat rs) := fun j =>
      if Nat.blt j sig.length then Licm.getBlock? bodies (sig.length - 1 - j) else none
    by_cases hrem : Nat.blt 0
        (budget - (Licm.scanPrefixLoads budget next (envK.map some) ldTbl k).1.length) = true
    · simp only [hrem, ↓reduceIte]
      cases hbind : (Licm.scanPrefixLoads budget next senv ldTbl k).2.2.bind getBlk with
      | none =>
        simp only [List.append_nil]
        exact ⟨nextE, envV_E, hevE, hebE, hldE⟩
      | some pb =>
        rcases pb with ⟨nPars, b⟩
        cases hjmp : (Licm.scanPrefixLoads budget next senv ldTbl k).2.2 with
        | none => simp [hjmp] at hbind
        | some j =>
          rw [hjmp, Option.bind_some] at hbind
          dsimp only [getBlk] at hbind
          by_cases hjlt : Nat.blt j sig.length = true
          · simp only [hjlt, ↓reduceIte] at hbind
            have hjlt' : j < sig.length := Nat.blt_eq ▸ hjlt
            let pos := sig.length - 1 - j
            let rem := budget - (Licm.scanPrefixLoads budget next senv ldTbl k).1.length
            let P : Mem 64 → Prop := fun m' => m' = m →
              match Licm.getBlock? bodies pos with
              | some (np, bk) =>
                let r := Licm.scanPrefixLoads rem nextE (Licm.pushNones np senv)
                  (Licm.scanPrefixLoads budget next senv ldTbl k).2.1 bk
                ∃ next' envV', EvalHoists m r.1 nextE envV_E next' envV' ∧
                  EnvBound next' envV' ∧ LdTableOk m envV' next' r.2.1
              | none => True
            let Js_pref := makePrefJs P sig pos
            have hscE : ScanRel nextE vs senv envV_E :=
              (ScanRel.of_envVsMatch hm).mono hevE.le_next fun l hl => hevE.find?_lt l hl
            have hclP := closed_makePrefJs_at (Γ := Γ) (Q := Q) (X := X) hPure rem nextE senv
              envV_E (Licm.scanPrefixLoads budget next senv ldTbl k).2.1 m vs
              hscE hebE hldE bodies pos (pushTup Js_pref ls_src)
            have hwkP := hw Js_pref hclP
            obtain ⟨_, _, _, _, _, hj2⟩ := scanPrefixLoads_wp hPure k budget next vs senv envV ldTbl
              (pushTup Js_pref ls_src) (ScanRel.of_envVsMatch hm) heb hld hwkP
            obtain ⟨_, args_j, J_j, hJ_j, hP_j⟩ := hj2 j hjmp
            have hp_m : P m := lookupL_pushTup_makePrefJs P ls_src j hjlt' hJ_j args_j m hP_j
            have hp_res := hp_m rfl
            rw [hbind] at hp_res
            dsimp only at hp_res
            obtain ⟨nB, eB, hevB, hebB, hldB⟩ := hp_res
            have hsub := hevE.append hevB
            dsimp only [senv, getBlk, rem] at *
            rw [← heqNE]
            exact ⟨nB, eB, hsub, hebB, hldB⟩
          · simp only [hjlt, Bool.false_eq_true, ↓reduceIte] at hbind; cases hbind
    · simp only [hrem, Bool.false_eq_true, ↓reduceIte, List.append_nil]
      exact ⟨nextE, envV_E, hevE, hebE, hldE⟩

mutual
private theorem roSweep_denote_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (hPure : ∀ {as rs : List Ty} (c : OpCode as rs),
      c.isLicmPure = true → ∀ args, ∃ r, ∀ post, c.wp args post ↔ post r) :
    (tf : TFlat rs) → (next : Nat) → (vs : List ((t : Ty) × Val t)) →
    (envK : List Nat) → (envV : VEnv Val) → (ldTbl : List (Ty × Nat × Nat)) →
    (inLoop : Option Licm.ReachTree) →
    (ls_src ls_out : List ((ts : List Ty) × Cont ts)) → (m : Mem 64) →
    EnvVsMatch next vs envK envV → EnvBound next envV → LdTableOk m envV next ldTbl →
    LsSafe ls_src ls_out tf m →
    wp Γ Q X (denote Val Cont tf vs ls_src) m →
    wp Γ Q X (roSweep next envV (Licm.analyzeRoTFlat next envK ldTbl inLoop tf)
      (denote Val Cont tf vs ls_out)) m
  | .let_ (ts := ts) op k, next, vs, envK, envV, ldTbl, inLoop, ls_src, ls_out, m,
      hm, heb, hld, hSafe, hw => by
    dsimp only [denote] at hw ⊢
    cases hda : denoteArgs vs op.args with
    | none => rw [hda] at hw; exact False.elim hw
    | some vArgs =>
      rw [hda] at hw
      dsimp only [Licm.analyzeRoTFlat, roSweep, wp, Op.wp] at hw ⊢
      refine OpCode.wp_mono op.code (vals vArgs) (fun xs hxs => ?_) hw
      have hkeep : ∀ l < next, (envInsertTup envV next xs).find? l = envV.find? l :=
        fun l hl => find?_insertTup_lt xs next l hl
      exact roSweep_denote_wp hPure k (next + ts.length) (pushTup xs vs)
        (Licm.pushLevels ts.length next envK) (envInsertTup envV next xs) ldTbl
        (inLoop.map (fun rt => (Licm.roRtStep1 rt).2)) ls_src ls_out m
        (hm.push xs) (heb.insertTup xs) (hld.mono (Nat.le_add_right _ _) hkeep)
        (hSafe.mono_ctrl (fun _ h => h) (fun _ h => h)) hxs
  | .load t a k, next, vs, envK, envV, ldTbl, inLoop, ls_src, ls_out, m,
      hm, heb, hld, hSafe, hw => by
    dsimp only [denote] at hw ⊢
    cases hda : denoteArg vs a with
    | none => rw [hda] at hw; exact False.elim hw
    | some va =>
      rw [hda] at hw; dsimp only
      dsimp only [wp] at hw
      rcases hw with ⟨v, hv, hwk⟩
      have alvlStep : ∀ idx alvl, a = .var idx → listGet? envK idx = some alvl →
          alvl < next ∧ envV.find? alvl = some ⟨i64, va.val⟩ := by
        intro idx alvl haeq hk; subst haeq
        dsimp only [denoteArg, lookupV] at hda
        cases hvx : listGet? vs idx with
        | none => simp [hvx] at hda
        | some pv =>
          rcases pv with ⟨t', v'⟩
          simp only [hvx] at hda
          cases hcast : castTy t' i64 v' with
          | none => simp [hcast] at hda
          | some v'' =>
            simp only [hcast, Option.some.injEq] at hda; subst hda
            obtain ⟨rfl, rfl⟩ := castTy_some_eq hcast
            obtain ⟨lvl, hk', hlt, hf⟩ := hm.2 idx i64 v' hvx
            rw [hk] at hk'; cases hk'; exact ⟨hlt, hf⟩
      let allowFwd := match inLoop with | none => true | some rt => (Licm.roRtStep1 rt).1
      let inL' := match inLoop with | none => none | some rt => some (Licm.roRtStep1 rt).2
      let alvl? := match a with | .var idx => listGet? envK idx | .imm _ => none
      let fwd? := if allowFwd then alvl?.bind (fun alvl => Licm.lookupLd t alvl ldTbl) else none
      have stepNode1 : ∀ ldTbl', LdTableOk m (envV.insert next ⟨t, v⟩) (next + 1) ldTbl' →
          wp Γ Q X (roSweep next envV
            (.node1 (Licm.analyzeRoTFlat (next + 1) (next :: envK) ldTbl' inL' k))
            (.load t va fun w => denote Val Cont k (⟨t, w⟩ :: vs) ls_out)) m := by
        intro ldTbl' hld'
        rw [roSweep_load]; dsimp only [wp]; refine ⟨v, hv, ?_⟩
        exact roSweep_denote_wp hPure k (next + 1) (⟨t, v⟩ :: vs) (next :: envK)
          (envV.insert next ⟨t, v⟩) ldTbl' inL' ls_src ls_out m
          (hm.cons_fresh v) (heb.insert_fresh v) hld'
          (hSafe.mono_ctrl (fun _ h => h) (fun _ h => h)) hwk
      cases hfwd : fwd? with
      | some vlvl =>
        have hf1 : allowFwd = true ∧ ∃ alvl, alvl? = some alvl ∧
            Licm.lookupLd t alvl ldTbl = some vlvl := by
          dsimp only [fwd?] at hfwd
          cases hallow : allowFwd with
          | false => simp [hallow] at hfwd
          | true =>
            simp only [hallow, ↓reduceIte] at hfwd
            cases hal : alvl? with
            | none => simp [hal] at hfwd
            | some alvl =>
              simp only [hal, Option.bind_some] at hfwd; exact ⟨rfl, alvl, rfl, hfwd⟩
        rcases hf1 with ⟨_, alvl, halEq, hlkp⟩
        cases a with
        | imm _ => simp [alvl?] at halEq
        | var idx =>
          obtain ⟨halLt, hfa⟩ := alvlStep idx alvl rfl halEq
          obtain ⟨_, hvvLt, va', vv, hfa', hfv, hlv⟩ := hld t alvl vlvl (lookupLd_mem hlkp)
          rw [hfa] at hfa'; cases hfa'; rw [hlv] at hv; cases hv
          have heq_plan : Licm.analyzeRoTFlat next envK ldTbl inLoop (.load t (.var idx) k) =
              .fwdLoad vlvl (Licm.analyzeRoTFlat next (vlvl :: envK) ldTbl inL' k) := by
            dsimp only [Licm.analyzeRoTFlat]
            dsimp only [fwd?, allowFwd, inL', alvl?] at hfwd ⊢
            cases inLoop <;> dsimp only at hfwd ⊢ <;> rw [hfwd]
          rw [heq_plan, roSweep_load]; dsimp only; rw [hfv]; dsimp only
          split
          · exact roSweep_denote_wp hPure k next (⟨t, v⟩ :: vs) (vlvl :: envK) envV ldTbl inL'
              ls_src ls_out m (hm.cons_existing hvvLt hfv) heb hld
              (hSafe.mono_ctrl (fun _ h => h) (fun _ h => h)) hwk
          · contradiction
      | none =>
        have heq_plan : Licm.analyzeRoTFlat next envK ldTbl inLoop (.load t a k) =
            .node1 (Licm.analyzeRoTFlat (next + 1) (next :: envK)
              (match alvl? with | some alvl => (t, alvl, next) :: ldTbl | none => ldTbl)
              inL' k) := by
          dsimp only [Licm.analyzeRoTFlat]
          dsimp only [fwd?, allowFwd, inL', alvl?] at hfwd ⊢
          cases inLoop <;> cases a <;> dsimp only at hfwd ⊢ <;> rw [hfwd] <;> rfl
        rw [heq_plan]
        have hkeep : ∀ l < next, (envV.insert next ⟨t, v⟩).find? l = envV.find? l :=
          fun l hl => find?_insert_lt hl
        have hld_base := hld.mono (Nat.le_succ next) hkeep
        cases hal : alvl? with
        | none => exact stepNode1 ldTbl hld_base
        | some alvl =>
          cases a with
          | imm _ => simp [alvl?] at hal
          | var idx =>
            obtain ⟨halLt, hfa⟩ := alvlStep idx alvl rfl hal
            exact stepNode1 ((t, alvl, next) :: ldTbl)
              (hld_base.cons (Nat.lt_succ_of_lt halLt) (Nat.lt_succ_self next)
                ((hkeep alvl halLt).trans hfa) (by rw [Trie.find?_insert]; simp) hv)
  | .store v a k, next, vs, envK, envV, ldTbl, inLoop, ls_src, ls_out, m,
      hm, heb, _, hSafe, hw => by
    dsimp only [denote] at hw ⊢
    cases hdv : denoteArg vs v with
    | none => rw [hdv] at hw; exact False.elim hw
    | some vv =>
      cases hda : denoteArg vs a with
      | none => rw [hdv, hda] at hw; exact False.elim hw
      | some va =>
        rw [hdv, hda] at hw
        dsimp only [Licm.analyzeRoTFlat, roSweep, wp] at hw ⊢
        refine ⟨hw.1, roSweep_denote_wp hPure k next vs envK envV []
          (inLoop.map (fun rt => (Licm.roRtStep1 rt).2)) ls_src ls_out _
          hm heb (fun _ _ _ h => nomatch h)
          (hSafe.to_unreach (fun _ h => h) (fun _ h => h)) hw.2⟩
  | .call f (bs := bs) args k, next, vs, envK, envV, ldTbl, inLoop, ls_src, ls_out, m,
      hm, heb, _, hSafe, hw => by
    dsimp only [denote] at hw ⊢
    cases hda : denoteArgs vs args with
    | none => rw [hda] at hw; exact False.elim hw
    | some vArgs =>
      rw [hda] at hw
      dsimp only [Licm.analyzeRoTFlat, roSweep, wp] at hw ⊢
      rcases hw with ⟨P, E, hΓ, hP, hE⟩
      refine ⟨P, E, hΓ, fun r m' hp => ?_, hE⟩
      exact roSweep_denote_wp hPure k (next + bs.length) (pushTup r vs)
        (Licm.pushLevels bs.length next envK) (envInsertTup envV next r) []
        (inLoop.map (fun rt => (Licm.roRtStep1 rt).2)) ls_src ls_out m'
        (hm.push r) (heb.insertTup r) (fun _ _ _ h => nomatch h)
        (hSafe.to_unreach (fun _ h => h) (fun _ h => h)) (hP r m' hp)
  | .jnz c t e, next, vs, envK, envV, ldTbl, inLoop, ls_src, ls_out, m,
      hm, heb, hld, hSafe, hw => by
    dsimp only [denote] at hw ⊢
    cases hdc : denoteArg vs c with
    | none => rw [hdc] at hw; exact False.elim hw
    | some vc =>
      rw [hdc] at hw
      dsimp only [Licm.analyzeRoTFlat, roSweep, wp] at hw ⊢
      exact ⟨
        fun h => roSweep_denote_wp hPure t next vs envK envV ldTbl _ ls_src ls_out m hm heb hld
          (hSafe.mono_ctrl
            (fun _ hm' => (Bool.and_eq_true _ _ ▸ hm').1)
            (fun _ hn' => (Bool.and_eq_true _ _ ▸ hn').1))
          (hw.1 h),
        fun h => roSweep_denote_wp hPure e next vs envK envV ldTbl _ ls_src ls_out m hm heb hld
          (hSafe.mono_ctrl
            (fun _ hm' => (Bool.and_eq_true _ _ ▸ hm').2)
            (fun _ hn' => (Bool.and_eq_true _ _ ▸ hn').2))
          (hw.2 h)⟩
  | .jump (ts := ts) j args, next, vs, envK, envV, _, _, ls_src, ls_out, m,
      _, _, _, hSafe, hw => by
    dsimp only [denote] at hw ⊢
    cases hJ : lookupL ls_src ts j with
    | none => rw [hJ] at hw; exact False.elim hw
    | some J₁ =>
      cases hda : denoteArgs vs args with
      | none => rw [hJ, hda] at hw; exact False.elim hw
      | some vArgs =>
        rw [hJ, hda] at hw
        dsimp only [lookupL] at hJ
        cases hg1 : listGet? ls_src j with
        | none => simp [hg1] at hJ
        | some p1 =>
          rcases p1 with ⟨ts1, J1'⟩
          simp only [hg1] at hJ
          cases hct : castListTy ts1 ts J1' with
          | none => simp [hct] at hJ
          | some J1'' =>
            simp only [hct, Option.some.injEq] at hJ
            subst hJ
            dsimp only [castListTy] at hct
            cases hdec : listTyDecEq ts1 ts with
            | isFalse _ => simp [hdec] at hct
            | isTrue heqt =>
              subst heqt
              simp only [hdec, Option.some.injEq] at hct
              subst hct
              have hlt : j < ls_out.length := by rw [← hSafe.1]; exact listGet?_lt_length hg1
              obtain ⟨p2, hg2⟩ := listGet?_some_of_lt hlt
              rcases p2 with ⟨ts2, J2⟩
              have hidx := hSafe.2 j
              rw [hg1, hg2] at hidx
              dsimp only at hidx
              rcases hidx with ⟨eqt, himpl | ⟨himpl, _⟩ | hnj⟩
              · subst eqt
                have hJ2 : lookupL ls_out ts1 j = some J2 := by
                  dsimp only [lookupL]; rw [hg2]; exact castListTy_self ts1 J2
                rw [hJ2]; dsimp only [Licm.analyzeRoTFlat, roSweep, wp] at hw ⊢
                exact himpl (vals vArgs) m hw
              · subst eqt
                have hJ2 : lookupL ls_out ts1 j = some J2 := by
                  dsimp only [lookupL]; rw [hg2]; exact castListTy_self ts1 J2
                rw [hJ2]; dsimp only [Licm.analyzeRoTFlat, roSweep, wp] at hw ⊢
                exact himpl (vals vArgs) hw
              · dsimp only [Licm.noJumpInRange] at hnj
                rw [not_range_bool] at hnj; omega
  | .ret vs', _, vs, _, _, _, _, _, _, _, _, _, _, _, hw => by
    dsimp only [denote] at hw ⊢
    cases hda : denoteArgs vs vs' with
    | none => rw [hda] at hw; exact False.elim hw
    | some _ => rw [hda] at hw; exact hw
  | .exit _ args, _, vs, _, _, _, _, _, _, _, _, _, _, _, hw => by
    dsimp only [denote] at hw ⊢
    cases hda : denoteArgs vs args with
    | none => rw [hda] at hw; exact False.elim hw
    | some _ => rw [hda] at hw; exact hw
  | .hlt, _, _, _, _, _, _, _, _, _, _, _, _, _, hw => hw
  | .group (sig := sig) bodies k, next, vs, envK, envV, ldTbl, inLoop,
      ls_src, ls_out, m, hm, heb, hld, hSafe, hw => by
    dsimp only [denote, wp] at hw ⊢
    dsimp only [Licm.analyzeRoTFlat]
    let cleanGroup := Nat.blt 0 sig.length &&
      Licm.memCleanReachesB 0 sig.length bodies &&
      Licm.memCleanReaches 0 sig.length k
    have hCleanB : cleanGroup = true → Licm.memCleanReachesB 0 sig.length bodies = true := by
      intro h; simp only [cleanGroup, Bool.and_eq_true] at h; exact h.1.2
    have hCleanK : cleanGroup = true → Licm.memCleanReaches 0 sig.length k = true := by
      intro h; simp only [cleanGroup, Bool.and_eq_true] at h; exact h.2
    have hCleanDef : Licm.memCleanReachesB 0 sig.length bodies = true →
        Licm.memCleanReaches 0 sig.length k = true → 0 < sig.length → cleanGroup = true := by
      intro h1 h2 hne
      simp only [cleanGroup, Bool.and_eq_true, Nat.blt_eq]
      exact ⟨⟨hne, h1⟩, h2⟩
    let runGroup : ∀ (hoists : List HoistLoad) (bsLd kLd : List (Ty × Nat × Nat))
        (rbs : Licm.ReachBlocks) (gateReach : Bool) (inK : Option Licm.ReachTree)
        (next' : Nat) (envV' : VEnv Val),
        EvalHoists m hoists next envV next' envV' →
        EnvBound next' envV' →
        (bsLd = [] ∨ (cleanGroup = true ∧ LdTableOk m envV' next' bsLd)) →
        LdTableOk m envV' next' kLd →
        next' = next + hoists.length →
        wp Γ Q X (roSweep next envV
          (.groupNode hoists
            (Licm.analyzeRoTBlocks (next + hoists.length) envK bsLd rbs gateReach bodies)
            (Licm.analyzeRoTFlat (next + hoists.length) envK kLd inK k))
          (.group (fun Js => denoteB Val Cont bodies vs (pushTup Js ls_out))
            (fun Js => denote Val Cont k vs (pushTup Js ls_out)))) m := by
      intro hoists bsLd kLd rbs gateReach inK next' envV' hev heb' hbsLd hkLd hnxt
      subst hnxt
      dsimp only [roSweep]
      refine hev.wp_emitRoHoists _ ?_
      dsimp only [wp]
      intro Js_out hclosed_dst
      let Js_src := makeCleanJs cleanGroup m Js_out
      have hm' : EnvVsMatch (next + hoists.length) vs envK envV' :=
        hm.mono hev.le_next fun l hl => hev.find?_lt l hl
      have hSafeB : ∀ m', (cleanGroup = true → m' = m) →
          LsSafeB (pushTup Js_src ls_src) (pushTup Js_out ls_out) bodies m' := by
        intro m' hm_c
        cases bodies with
        | nil => exact trivial
        | @cons ts0 sig0 b0 bs0 =>
          exact lsSafeB_push_group_aux cleanGroup Js_out hSafe hm_c hCleanB
            (fun h1 h2 => hCleanDef h1 h2 (Nat.zero_lt_succ _)) (.cons b0 bs0)
            (fun _ _ h => h) (fun _ _ h => h)
      have hSafeK : LsSafe (pushTup Js_src ls_src) (pushTup Js_out ls_out) k m :=
        LsSafe.push_group_k cleanGroup Js_out hSafe hCleanK
      have hclosed_src : Closed Γ Q X
          (denoteB Val Cont bodies vs (pushTup Js_src ls_src)) Js_src :=
        roSweepB_denote_wp hPure bodies (next + hoists.length) vs envK envV' bsLd rbs gateReach
          (pushTup Js_src ls_src) (pushTup Js_out ls_out) cleanGroup m hm' heb' hbsLd
          hSafeB Js_out hclosed_dst
      have hwk := hw Js_src hclosed_src
      exact roSweep_denote_wp hPure k (next + hoists.length) vs envK envV' kLd inK
        (pushTup Js_src ls_src) (pushTup Js_out ls_out) m hm' heb' hkLd hSafeK hwk
    by_cases hcg : cleanGroup = true
    · have hncg : (!cleanGroup) = false := by simp [hcg]
      change wp Γ Q X (roSweep next envV (if !cleanGroup then _ else _)
          (.group (fun Js => denoteB Val Cont bodies vs (pushTup Js ls_out))
            (fun Js => denote Val Cont k vs (pushTup Js ls_out)))) m
      simp only [hncg, Bool.false_eq_true, ↓reduceIte]
      split
      · exact runGroup [] ldTbl ldTbl _ inLoop.isSome _ next envV .nil heb
          (Or.inr ⟨hcg, hld⟩) hld rfl
      · let outerCard := Licm.trieCard (Licm.collectOuterB 0 bodies .empty)
        let lowPress := Nat.blt outerCard Licm.roLoadPressCap
        let budget := if lowPress then Licm.roLoadPressCap - outerCard else 0
        obtain ⟨nextB, envV_B, hevAll, hebB, hldB⟩ := groupHoist_wp hPure lowPress budget next
          vs envK envV ldTbl bodies k ls_src hm heb hld hw
        refine runGroup _ _ _ _ true _ nextB envV_B hevAll hebB ?_ hldB hevAll.len
        dsimp only [lowPress, outerCard, budget] at hldB ⊢
        split
        · next hlp =>
          simp only [hlp, ↓reduceIte] at hldB ⊢
          exact Or.inr ⟨hcg, hldB⟩
        · exact Or.inl rfl
    · have hncg : (!cleanGroup) = true := by simp [hcg]
      change wp Γ Q X (roSweep next envV (if !cleanGroup then _ else _)
          (.group (fun Js => denoteB Val Cont bodies vs (pushTup Js ls_out))
            (fun Js => denote Val Cont k vs (pushTup Js ls_out)))) m
      rw [hncg]
      exact runGroup [] [] ldTbl .nil false _ next envV .nil heb (Or.inl rfl) hld rfl

private theorem roSweepB_denote_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (hPure : ∀ {as rs : List Ty} (c : OpCode as rs),
      c.isLicmPure = true → ∀ args, ∃ r, ∀ post, c.wp args post ↔ post r) :
    {sig : List (List Ty)} → (tb : TBlocks rs sig) →
    (next : Nat) → (vs : List ((t : Ty) × Val t)) →
    (envK : List Nat) → (envV : VEnv Val) → (ldTbl : List (Ty × Nat × Nat)) →
    (rbs : Licm.ReachBlocks) → (gateReach : Bool) →
    (ls_src ls_out : List ((ts : List Ty) × Cont ts)) →
    (cleanGroup : Bool) → (m₀ : Mem 64) →
    EnvVsMatch next vs envK envV → EnvBound next envV →
    (ldTbl = [] ∨ (cleanGroup = true ∧ LdTableOk m₀ envV next ldTbl)) →
    (∀ m', (cleanGroup = true → m' = m₀) → LsSafeB ls_src ls_out tb m') →
    (Js_out : Tup Cont sig) →
    Closed Γ Q X
      (roSweepB next envV (Licm.analyzeRoTBlocks next envK ldTbl rbs gateReach tb)
        (denoteB Val Cont tb vs ls_out)) Js_out →
    Closed Γ Q X (denoteB Val Cont tb vs ls_src) (makeCleanJs cleanGroup m₀ Js_out)
  | _, .nil, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, (), _ => trivial
  | ts :: _, .cons b bs, next, vs, envK, envV, ldTbl, rbs, gateReach, ls_src, ls_out,
      cleanGroup, m₀, hm, heb, hldOpt, hSafeB, (J_out, Js_out), hclosed => by
    dsimp only [denoteB, roSweepB, Licm.analyzeRoTBlocks, Closed] at hclosed ⊢
    refine ⟨fun xs m' hwb hcm => ?_, ?_⟩
    · have hkeep : ∀ l < next, (envInsertTup envV next xs).find? l = envV.find? l :=
        fun l hl => find?_insertTup_lt xs next l hl
      have hld' : LdTableOk m' (envInsertTup envV next xs) (next + ts.length) ldTbl := by
        rcases hldOpt with rfl | ⟨hcg_t, hld0⟩
        · exact fun _ _ _ h => nomatch h
        · have hm' := hcm hcg_t; subst hm'
          exact hld0.mono (Nat.le_add_right _ _) hkeep
      let inB : Option Licm.ReachTree :=
        if gateReach then some (match rbs with
          | .cons rh rtl => (rh, rtl)
          | _ => (.leaf false, .nil)).1
        else none
      have hb_dst := roSweep_denote_wp hPure b (next + ts.length) (pushTup xs vs)
        (Licm.pushLevels ts.length next envK) (envInsertTup envV next xs) ldTbl inB
        ls_src ls_out m' (hm.push xs) (heb.insertTup xs) hld'
        (hSafeB m' hcm).1 hwb
      exact hclosed.1 xs m' hb_dst
    · exact roSweepB_denote_wp hPure bs next vs envK envV ldTbl _ gateReach ls_src ls_out
        cleanGroup m₀ hm heb hldOpt (fun m' hm_c => (hSafeB m' hm_c).2) Js_out hclosed.2
end

/-! ## Closed-function theorems (`roSweep`, `Func.licm_*`, `Fn.licm_*`) -/

theorem roSweepFunc_wf {as rs : List Ty} {f : Func as rs} (hf : f.Wf) :
    Func.Wf (fun V L xs => roSweep as.length (envInsertTup .empty 0 xs)
      (Licm.buildRoPlan as.length (reifyFunc f)) (f V L xs)) := by
  intro V₁ V₂ L₁ L₂ xs₁ xs₂
  have hwf := hf V₁ V₂ L₁ L₂ xs₁ xs₂
  have hE : EnvRel (Tup.zip xs₁ xs₂) (envInsertTup .empty 0 xs₁) (envInsertTup .empty 0 xs₂) := by
    simpa using EnvRel.insertTup (G' := []) EnvRel.empty xs₁ xs₂ 0
  exact roSweep_wf hwf (fun _ hp => hp) as.length _ _ _ hE

theorem roSweepFunc_spec {as rs : List Ty} {f : Func as rs} (hf : f.Wf)
    (hPure : ∀ {as rs : List Ty} (c : OpCode as rs),
      c.isLicmPure = true → ∀ args, ∃ r, ∀ post, c.wp args post ↔ post r)
    {Γ : Env} {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Func.spec Γ f xs m Q X) :
    Func.spec Γ (fun V L xs => roSweep as.length (envInsertTup .empty 0 xs)
      (Licm.buildRoPlan as.length (reifyFunc f)) (f V L xs)) xs m Q X := by
  have hren := Func.renorm_spec hf h
  dsimp only [Func.wp, Func.renorm, denoteFunc, reifyFunc] at hren
  have hm0 : EnvVsMatch as.length (pushTup xs []) (Licm.pushLevels as.length 0 [])
      (envInsertTup .empty 0 xs) := by
    simpa using (EnvVsMatch.empty 0).push xs
  have heb0 : EnvBound as.length (envInsertTup .empty 0 xs) := by
    simpa using (EnvBound.empty 0).insertTup xs
  have hld0 : LdTableOk m (envInsertTup .empty 0 xs) as.length [] := fun _ _ _ hp => nomatch hp
  have hsafe0 : LsSafe [] [] (toTFlat (f K KL (Tup.levels as 0)) as.length 0) m :=
    ⟨rfl, fun _ => trivial⟩
  have hrw := roSweep_denote_wp hPure (toTFlat (f K KL (Tup.levels as 0)) as.length 0)
    as.length (pushTup xs []) (Licm.pushLevels as.length 0 []) (envInsertTup .empty 0 xs)
    [] none [] [] m hm0 heb0 hld0 hsafe0 hren
  have hwf := hf Val K Cont KL xs (Tup.levels as 0)
  have h0 : PassFlatKit.RelCtxMatch 0 ([] : Ctx Val K) ([] : Ctx Val Val)
      ([] : List ((t : Ty) × Val t)) := fun hm => nomatch hm
  have hvs : PassFlatKit.RelCtxMatch (0 + as.length) (Tup.zip xs (Tup.levels as 0) ++ [])
      (Tup.zip xs xs ++ []) (pushTup xs []) := PassFlatKit.RelCtxMatch.pushTup xs xs h0
  simp only [Nat.zero_add, List.append_nil] at hvs
  have hD0 : PassFlatKit.RelCtxMatch 0 ([] : Ctx Cont KL) ([] : Ctx Cont Cont)
      ([] : List ((ts : List Ty) × Cont ts)) := fun hm => nomatch hm
  have hdwf := PassFlatKit.denote_wf_src hwf hvs hD0
  have hE : EnvRel (Tup.zip xs xs) (envInsertTup .empty 0 xs) (envInsertTup .empty 0 xs) := by
    simpa using EnvRel.insertTup (G' := []) EnvRel.empty xs xs 0
  have hswf := roSweep_wf hdwf (fun _ hp => hp) as.length _ _
    (Licm.buildRoPlan as.length (reifyFunc f)) hE
  have hweq := PassFlatKit.wp_iff_of_diag_eq (Γ := Γ) (Q := Q) (X := X) hswf
    (fun p hp => (tup_zip_self_eq (D := ([] : Ctx Val Val)) (fun _ hq => nomatch hq) xs)
      p (List.mem_append_left [] hp))
    (fun _ hp => nomatch hp) (m := m)
  exact hweq.2 hrw

theorem roSweepFunc_supportsSource (target : LegalTarget) {as rs : List Ty} {f : Func as rs}
    (hf : f.Wf) (hsupp : f.supportsSource target = true) :
    Func.supportsSource target (fun V L xs => roSweep as.length (envInsertTup .empty 0 xs)
      (Licm.buildRoPlan as.length (reifyFunc f)) (f V L xs)) = true := by
  simp only [Func.supportsSource, Bool.and_eq_true] at hsupp ⊢
  refine ⟨hsupp.1, ?_⟩
  have hplan : (Licm.buildRoPlan as.length (reifyFunc f)).supports target = true :=
    analyzeRoTFlat_supports target (reifyFunc f) as.length (Licm.pushLevels as.length 0 [])
      [] none hsupp.2
  exact roSweep_supportsSource target
    (hf K K KL KL (Tup.levels as 0) (Tup.levels as 0))
    as.length (envInsertTup .empty 0 (Tup.levels as 0)) _ as.length 0 as.length 0
    hsupp.2 hplan

end LeanQbe.T
