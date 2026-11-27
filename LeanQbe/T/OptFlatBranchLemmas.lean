module

public import LeanQbe.T.OptFlatBranchLemmas0
import LeanQbe.T.FlatDirectLemmas
import LeanQbe.T.PassFlatKit
import LeanQbe.T.OptFlatSimKit
import LeanQbe.T.CondThreadOptLemmas2

/-!
# Conditional Branch Threading Equivalence Proofs (`OptFlatBranchLemmas`)

Proves exact `=` correspondence (`std3` axioms only) between the native `TFlat` pass
`OptFlatBranch.condThreadPassFlat` and `Func.condThreadPass` (and re-exports
`OptFlatBranchLemmas0` for `tailDupFlat`):

* `OptFlatBranch.condThreadWithPlanFlat_eq`
* `OptFlatBranch.condThreadPassFlat_eq`
* `OptFlatBranch.denoteFunc_condThreadPassFlat`
* `OptFlatBranch.condThreadPassFlat_wfCheck`
* `OptFlatBranch.condThreadPassFlatFn_toFn` / `OptFlatBranch.condThreadPassFlatFn_wfCheck`
-/

set_option autoImplicit false

public section

namespace LeanQbe.T
namespace OptFlatBranch

open OptFlatPlanKit
open OptFlatSimKit
open CondThreadOpt

/-! ## 1. `CTTarget`, `ValidLFlat`, and `CTLabelFlat` Relations -/

private theorem orel_isSome {α β : Type} {R : α → β → Prop} :
    {o₁ : Option α} → {o₂ : Option β} → ORel R o₁ o₂ → o₁.isSome = o₂.isSome
  | none, none, _ => rfl
  | some _, some _, _ => rfl

private theorem emitCTTargetFlat_eq {rs ts : List Ty} (ovd old : Nat)
    (args : Tup (Arg (CTOptV K)) ts) :
    (tgt : CTTarget K KL ts) →
    toTFlat (CTTarget.emit (rs := rs) args tgt) ovd old = emitCTTargetFlat ovd old args tgt
  | .keep l => by
    dsimp only [CTTarget.emit, emitCTTargetFlat]; cases toRealArgs? args <;> rfl
  | .dead => rfl
  | .split m lT? lF? lD? => by
    dsimp only [CTTarget.emit, emitCTTargetFlat]
    cases getTupMem m args with
    | imm b =>
      cases b with
      | true =>
        cases lT? with
        | none => rfl
        | some _ => cases toRealArgs? (dropTupMem m args) <;> rfl
      | false =>
        cases lF? with
        | none => rfl
        | some _ => cases toRealArgs? (dropTupMem m args) <;> rfl
    | var v? =>
      cases v? with
      | none => rfl
      | some _ =>
        cases lD? with
        | some _ => cases toRealArgs? args <;> rfl
        | none =>
          cases lT? with
          | none => rfl
          | some _ =>
            cases lF? with
            | none => rfl
            | some _ => cases toRealArgs? (dropTupMem m args) <;> rfl

/-- Validation-time simulation relation between `ValidLFlat` and `CondThreadOpt.ValidL`. -/
private def ValidLFlatMatch {rs ts : List Ty} (jl : ValidLFlat rs ts) (j : ValidL rs ts) : Prop :=
  jl.target = j.target ∧ ∀ args, jl.inlineOk? args = (j.inline? args).isSome

/-- Rewriter-time simulation relation between `CTLabelFlat` and `CTLabel K KL`. -/
private def CTLabelFlatMatch {rs ts : List Ty}
    (jl : CTLabelFlat rs ts) (j : CTLabel K KL rs ts) : Prop :=
  jl.target = j.target ∧
    ∀ ovd old args,
      ORel (fun tf e => tf = toTFlat e ovd old) (jl.inline? ovd old args) (j.inline? args)

private theorem CTLabelFlat_emitJump_eq {rs ts : List Ty} (tryInl : Bool)
    {jl : CTLabelFlat rs ts} {j : CTLabel K KL rs ts}
    (hm : CTLabelFlatMatch jl j) (ovd old : Nat) (args : Tup (Arg (CTOptV K)) ts) :
    toTFlat (j.emitJump tryInl args) ovd old = jl.emitJump tryInl ovd old args := by
  dsimp only [CTLabel.emitJump, CTLabelFlat.emitJump]
  by_cases htry : tryInl = true
  · simp only [htry, ↓reduceIte]
    have hi := hm.2 ovd old args
    cases h1 : jl.inline? ovd old args <;> cases h2 : j.inline? args <;>
      simp only [h1, h2, ORel] at hi
    · rw [hm.1]; exact emitCTTargetFlat_eq ovd old args j.target
    · exact hi.symm
  · simp only [htry, Bool.false_eq_true, ↓reduceIte]
    rw [hm.1]; exact emitCTTargetFlat_eq ovd old args j.target

private theorem mkFreshOptArg_eq_toOptArgTup :
    (ts : List Ty) → (inVD outVD : Nat) →
    mkFreshTup (fun _ _ od => Arg.var (some od)) ts inVD outVD =
      toOptArgTup (Tup.levels ts outVD)
  | [], _, _ => rfl
  | _ :: ts, inVD, outVD => by
    dsimp only [mkFreshTup, Tup.levels, toOptArgTup]
    rw [mkFreshOptArg_eq_toOptArgTup ts (inVD + 1) (outVD + 1)]

private theorem tupFreshSomeOpt_eq :
    (ts : List Ty) → (xs : Tup K ts) → (n : Nat) →
    tupFreshWith (fun x _ => Arg.var (some x)) ts xs n = toOptArgTup xs
  | [], (), _ => rfl
  | _ :: ts, (_, xs), n => by
    dsimp only [tupFreshWith, toOptArgTup]; rw [tupFreshSomeOpt_eq ts xs (n + 1)]

private theorem tupFreshUnitOpt_eq :
    (ts : List Ty) → (xs : Tup K ts) → (n : Nat) →
    tupFreshWith (fun _ _ => Arg.var (some ())) ts xs n = toOptArgTup (Tup.units ts)
  | [], (), _ => rfl
  | _ :: ts, (_, xs), n => by
    dsimp only [tupFreshWith, Tup.units, toOptArgTup]; rw [tupFreshUnitOpt_eq ts xs (n + 1)]

/-! ## 2. `peelThreadHeadFlat`, `validateInlineFlat`, and `rewriteCTInlineFlat` Equivalence -/

private theorem peelThreadHead_other {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (fuel : Nat) (res : Bool) (p : CTPlan) (e : Expr (Arg (CTOptV V)) (CTLabel V L rs) rs)
    (h1 : ∀ pk, p ≠ .node1 pk) (h2 : ∀ pt pe, p ≠ .node2 pt pe) :
    peelThreadHead fuel res p e = (res, p, e) := by
  cases fuel with
  | zero => rfl
  | succ _ =>
    cases p with
    | node1 pk => exact absurd rfl (h1 pk)
    | node2 pt pe => exact absurd rfl (h2 pt pe)
    | leaf | jump _ | group _ _ _ => rfl

local macro "pth_miss" eqP:Lean.Parser.Tactic.rwRule "," hΓ:ident "," hmV:ident "," hwf0:ident ","
    hrw:Lean.Parser.Tactic.rwRule "," heq:Lean.Parser.Tactic.rwRule : tactic => `(tactic| (
  simp only; refine ⟨_, _, $hΓ, $hmV, $hwf0, ?_⟩
  dsimp only [denote]; rw [$hrw]; dsimp only; rw [$eqP]; dsimp only; rw [$heq]))

private theorem peelThreadHeadFlat_eq {W : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    (fuel : Nat) → (res : Bool) → (p : CTPlan) → (tf : TFlat rs) →
    {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × Arg (CTOptV W) t)} →
    {ls : List ((ts : List Ty) × CTLabel W L rs ts)} →
    {inVD : Nat} → {inVE : Trie ((t : Ty) × Arg (CTOptV W) t)} →
    CtxTypes Γ vs → CtxTypes Δ ls → TrieCtxMatch inVD inVE vs → tf.wfCheck Γ Δ = true →
    ∃ Γ' vs',
      let r := peelThreadHeadFlat fuel res p inVD inVE tf
      CtxTypes Γ' vs' ∧ TrieCtxMatch r.2.2.1 r.2.2.2.1 vs' ∧
        r.2.2.2.2.wfCheck Γ' Δ = true ∧
        peelThreadHead fuel res p (denote (Arg (CTOptV W)) (CTLabel W L rs) tf vs ls) =
          (r.1, r.2.1, denote (Arg (CTOptV W)) (CTLabel W L rs) r.2.2.2.2 vs' ls)
  | 0, _, _, _, Γ, _, vs, _, _, _, hΓ, _, hmV, hwf => ⟨Γ, vs, hΓ, hmV, hwf, rfl⟩
  | fuel + 1, res, p, tf, Γ, Δ, vs, ls, inVD, inVE, hΓ, hΔ, hmV, hwf => by
    cases p with
    | node1 pk =>
      cases tf with
      | let_ op k =>
        have hwf0 := hwf
        obtain ⟨ha, hk⟩ := wf_let hwf
        have hargs := denoteArgs_eq_some_resolveEnvArgs hΓ hmV op.args ha ctDflt
        rw [peelThreadHeadFlat.eq_def]; simp only
        let args' := flattenArgs (resolveEnvArgs inVD inVE op.args ctDflt)
        cases hev : evalThreadLet? op.code args' with
        | some out =>
          simp only; dsimp only [denote]; rw [hargs]; dsimp only [peelThreadHead]; rw [hev]
          exact peelThreadHeadFlat_eq fuel res pk k
            (ctxTypes_pushTup_rev out hΓ) hΔ (trieCtxMatch_insertTupEnv hmV out) hk
        | none => pth_miss peelThreadHead.eq_def, hΓ, hmV, hwf0, hargs, hev
      | _ =>
        rw [peelThreadHeadFlat.eq_def]; simp only; refine ⟨Γ, vs, hΓ, hmV, hwf, ?_⟩
        cases hne : denote (Arg (CTOptV W)) (CTLabel W L rs) _ vs ls with
        | let_ _ _ => dsimp only [denote] at hne; repeat (first | cases hne | split at hne)
        | _ => rfl
    | node2 pt pe =>
      cases tf with
      | jnz c t e =>
        have hwf0 := hwf
        obtain ⟨hc, ht, he⟩ := wf_jnz hwf
        have hca := denoteArg_eq_some_resolveEnvArg hΓ hmV c hc ctDflt
        rw [peelThreadHeadFlat.eq_def]; simp only
        cases hc' : flattenArg (resolveEnvArg inVD inVE c ctDflt) with
        | imm b =>
          dsimp only [denote]; rw [hca]; dsimp only [peelThreadHead]; rw [hc']
          cases b with
          | true => exact peelThreadHeadFlat_eq fuel true pt t hΓ hΔ hmV ht
          | false => exact peelThreadHeadFlat_eq fuel true pe e hΓ hΔ hmV he
        | var _ => pth_miss peelThreadHead.eq_def, hΓ, hmV, hwf0, hca, hc'
      | _ =>
        rw [peelThreadHeadFlat.eq_def]; simp only; refine ⟨Γ, vs, hΓ, hmV, hwf, ?_⟩
        cases hne : denote (Arg (CTOptV W)) (CTLabel W L rs) _ vs ls with
        | jnz _ _ _ => dsimp only [denote] at hne; repeat (first | cases hne | split at hne)
        | _ => rfl
    | leaf | jump _ | group _ _ _ =>
      rw [peelThreadHeadFlat.eq_def]; simp only
      exact ⟨Γ, vs, hΓ, hmV, hwf, peelThreadHead_other _ _ _ _ (by simp) (by simp)⟩

local macro "vi_succ" eqF:Lean.Parser.Tactic.rwRule "," eqP:Lean.Parser.Tactic.rwRule ","
    b_t:Lean.Parser.Tactic.elimTarget "," b:ident "," body:tacticSeq : tactic => `(tactic|
  cases $b_t with
  | zero => rw [$eqF, $eqP]
  | succ $b => $body)

local macro "vi_node1" eqF:Lean.Parser.Tactic.rwRule "," eqP:Lean.Parser.Tactic.rwRule ","
    b_t:Lean.Parser.Tactic.elimTarget "," b:ident ","
    plan:Lean.Parser.Tactic.elimTarget "," pk:ident ","
    pre:tacticSeq "," body:tacticSeq : tactic => `(tactic|
  cases $b_t with
  | zero => rw [$eqF, $eqP]
  | succ $b =>
    ($pre)
    cases $plan with
    | node1 $pk => rw [$eqF, $eqP]; simp only; ($body)
    | _ => rw [$eqF, $eqP])

local macro "vi_term" eqF:Lean.Parser.Tactic.rwRule "," eqP:Lean.Parser.Tactic.rwRule ","
    b:Lean.Parser.Tactic.elimTarget "," plan:Lean.Parser.Tactic.elimTarget ","
    pre:tacticSeq : tactic => `(tactic|
  cases $b with
  | zero => rw [$eqF, $eqP]
  | succ _ =>
    ($pre)
    cases $plan <;> rw [$eqF, $eqP] <;> simp only)

private theorem validateInlineFlat_eq {W : Ty → Type} {LFlat L : List Ty → Type} {rs : List Ty}
    (R : (ts : List Ty) → LFlat ts → CTLabel W L rs ts → Prop)
    (checkJ : ∀ {ts : List Ty}, LFlat ts → Tup (Arg (CTOptV W)) ts → Bool)
    (hJ : ∀ {ts jl j a}, R ts jl j → checkJ jl a = (j.target.canEmit a || (j.inline? a).isSome)) :
    (budget : Nat) → (plan : CTPlan) → (tf : TFlat rs) →
    {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × Arg (CTOptV W) t)} →
    {ls : List ((ts : List Ty) × CTLabel W L rs ts)} →
    {inVD inLD : Nat} →
    {inVE : Trie ((t : Ty) × Arg (CTOptV W) t)} →
    {inLE : Trie ((ts : List Ty) × LFlat ts)} →
    CtxTypes Γ vs → CtxTypes Δ ls → TrieCtxMatch inVD inVE vs →
    TrieRelMatch R inLD inLE ls → tf.wfCheck Γ Δ = true →
    validateInlineFlat checkJ inLD inLE budget plan inVD inVE tf =
      validateInline budget plan (denote (Arg (CTOptV W)) (CTLabel W L rs) tf vs ls) := by
  intro budget plan tf Γ Δ vs ls inVD inLD inVE inLE hΓ hΔ hmV hmL hwf
  refine (relSim_mutual (rs := rs)
    (W := Arg (CTOptV W)) (L₁ := LFlat) (L₂ := CTLabel W L rs) (S := Nat × CTPlan) (SB := Unit)
    (LR := fun Δ inLD inLE ls => CtxTypes Δ ls ∧ TrieRelMatch R inLD inLE ls)
    (P := fun s tf _ _ vs ls inVD inVE inLD inLE _ _ =>
      validateInlineFlat checkJ inLD inLE s.1 s.2 inVD inVE tf =
        validateInline s.1 s.2 (denote (Arg (CTOptV W)) (CTLabel W L rs) tf vs ls))
    (PB := fun _ _ _ _ _ _ _ _ _ _ _ _ => True) ⟨
    @fun ts _ _ _ _ inVD _ _ _ inVE _ ⟨b, plan⟩ op k hΓ _ hmV hlr hwf ih => by
      vi_node1 validateInlineFlat.eq_def, validateInline.eq_def, b, b, plan, pk,
        (obtain ⟨ha, hk⟩ := wf_let hwf; dsimp only [denote];
         rw [denoteArgs_eq_some_resolveEnvArgs hΓ hmV op.args ha ctDflt]; dsimp only),
        (cases evalThreadLet? op.code (flattenArgs (resolveEnvArgs inVD inVE op.args ctDflt)) with
         | some out =>
           exact ih (outVD' := 0) (outLD' := 0) (b + 1, pk) (ctxTypes_pushTup_rev out hΓ)
             (trieCtxMatch_insertTupEnv hmV out) hlr hk
         | none =>
           rw [ih (outVD' := 0) (outLD' := 0) (b, pk) (ctxTypes_pushTup_rev (noneArgTup ts) hΓ)
             (trieCtxMatch_insertTupEnv hmV (noneArgTup ts)) hlr hk]),
    fun ⟨b, plan⟩ t a k hΓ _ hmV hlr hwf ih => by
      vi_node1 validateInlineFlat.eq_def, validateInline.eq_def, b, b, plan, pk,
        (obtain ⟨ha, hk⟩ := wf_load hwf; dsimp only [denote];
         rw [denoteArg_eq_some_resolveEnvArg hΓ hmV a ha ctDflt]; dsimp only),
        rw [ih (outVD' := 0) (outLD' := 0) (b, pk) (.cons hΓ)
          (hmV.cons t (Arg.var none)) hlr hk],
    fun ⟨b, plan⟩ v a k hΓ _ hmV hlr hwf ih => by
      vi_node1 validateInlineFlat.eq_def, validateInline.eq_def, b, b, plan, pk,
        (obtain ⟨hv, ha, hk⟩ := wf_store hwf; dsimp only [denote];
         rw [denoteArg_eq_some_resolveEnvArg hΓ hmV v hv ctDflt,
           denoteArg_eq_some_resolveEnvArg hΓ hmV a ha ctDflt]; dsimp only),
        rw [ih (outVD' := 0) (outLD' := 0) (b, pk) hΓ hmV hlr hk],
    fun ⟨b, plan⟩ _ bs args k hΓ _ hmV hlr hwf ih => by
      vi_node1 validateInlineFlat.eq_def, validateInline.eq_def, b, b, plan, pk,
        (obtain ⟨ha, hk⟩ := wf_call hwf; dsimp only [denote];
         rw [denoteArgs_eq_some_resolveEnvArgs hΓ hmV args ha ctDflt]; dsimp only),
        rw [ih (outVD' := 0) (outLD' := 0) (b, pk) (ctxTypes_pushTup_rev (noneArgTup bs) hΓ)
          (trieCtxMatch_insertTupEnv hmV (noneArgTup bs)) hlr hk],
    @fun _ _ vs ls inVD _ _ _ inVE _ ⟨b, plan⟩ c t e hΓ _ hmV _ hwf iht ihe => by
      vi_succ validateInlineFlat.eq_def, validateInline.eq_def, b, b,
        (obtain ⟨hc, ht, he⟩ := wf_jnz hwf; dsimp only [denote];
         rw [denoteArg_eq_some_resolveEnvArg hΓ hmV c hc ctDflt]; dsimp only
         cases plan with
         | node2 pt pe =>
           rw [validateInlineFlat.eq_def, validateInline.eq_def]; simp only
           cases flattenArg (resolveEnvArg inVD inVE c ctDflt) with
           | imm bVal =>
             cases bVal with
             | true => exact iht (b + 1, pt) ht
             | false => exact ihe (b + 1, pe) he
           | var _ =>
             dsimp only; rw [iht (b, pt) ht]
             cases hst : validateInline b pt
                 (denote (Arg (CTOptV W)) (CTLabel W L rs) t vs ls) with
             | none => rfl
             | some st => dsimp only [Bind.bind, Option.bind]; rw [ihe (b - st, pe) he]
         | _ => rw [validateInlineFlat.eq_def, validateInline.eq_def]),
    fun ⟨b, plan⟩ j args hΓ _ hmV hlr hwf => by
      vi_succ validateInlineFlat.eq_def, validateInline.eq_def, b, b,
        (obtain ⟨hj, ha⟩ := wf_jump hwf
         obtain ⟨w₁, w₂, hres, hlk, hm⟩ := TrieRelMatch.resolveLabel_rel hlr.1 hlr.2 hj
         dsimp only [denote]
         rw [hlk, denoteArgs_eq_some_resolveEnvArgs hΓ hmV args ha ctDflt]; dsimp only
         cases plan with
         | jump _ =>
           rw [validateInlineFlat.eq_def, validateInline.eq_def]; simp only
           rw [hres]; simp only [hJ hm]
         | _ => rw [validateInlineFlat.eq_def, validateInline.eq_def]),
    fun ⟨b, plan⟩ vs' hΓ _ hmV _ hwf => by
      vi_term validateInlineFlat.eq_def, validateInline.eq_def, b, plan,
        (dsimp only [denote];
         rw [denoteArgs_eq_some_resolveEnvArgs hΓ hmV vs' hwf ctDflt]; dsimp only),
    fun ⟨b, plan⟩ _ args hΓ _ hmV _ hwf => by
      vi_term validateInlineFlat.eq_def, validateInline.eq_def, b, plan,
        (dsimp only [denote];
         rw [denoteArgs_eq_some_resolveEnvArgs hΓ hmV args hwf ctDflt]; dsimp only),
    fun ⟨b, plan⟩ _ _ _ _ _ => by
      vi_term validateInlineFlat.eq_def, validateInline.eq_def, b, plan, dsimp only [denote],
    fun ⟨b, plan⟩ _ _ _ _ _ _ _ _ _ => by
      vi_term validateInlineFlat.eq_def, validateInline.eq_def, b, plan, dsimp only [denote],
    fun _ _ _ _ _ _ => trivial,
    fun _ _ _ _ _ _ _ _ _ _ => trivial⟩).1 tf (budget, plan) hΓ hΔ hmV ⟨hΔ, hmL⟩ hwf
      (outVD := 0) (outLD := 0)

local macro "ct_rw_rel" eqP:Lean.Parser.Tactic.rwRule "," eqF:Lean.Parser.Tactic.rwRule ","
    onJump:term "," onGroup:term "," onNil:term "," onCons:term : term => `(⟨
  @fun ts _ _ _ _ inVD outVD _ _ inVE _ plan op k hΓ _ hmV hlr hwf ih => by
    obtain ⟨ha, hk⟩ := wf_let hwf; dsimp only [denote]
    rw [denoteArgs_eq_some_resolveEnvArgs hΓ hmV op.args ha ctDflt]; dsimp only
    cases plan with
    | node1 pk =>
      rw [$eqP, $eqF]; simp only
      cases evalThreadLet? op.code (flattenArgs (resolveEnvArgs inVD inVE op.args ctDflt)) with
      | some out =>
        exact ih pk (ctxTypes_pushTup_rev out hΓ) (trieCtxMatch_insertTupEnv hmV out) hlr hk
      | none =>
        cases toRealArgs? (flattenArgs (resolveEnvArgs inVD inVE op.args ctDflt)) with
        | none => rfl
        | some _ =>
          dsimp only [toTFlat]
          have hfresh := trieCtxMatch_insertFreshWith
            (fun _ _ od => Arg.var (some od)) hmV ts outVD
          rw [mkFreshOptArg_eq_toOptArgTup] at hfresh
          exact congrArg (TFlat.let_ _) (ih pk (ctxTypes_pushTup_rev _ hΓ) hfresh hlr hk)
    | _ => rw [$eqP, $eqF]; simp only; rfl,
  @fun _ _ _ _ inVD outVD _ _ inVE _ plan t a k hΓ _ hmV hlr hwf ih => by
    obtain ⟨ha, hk⟩ := wf_load hwf
    dsimp only [denote]; rw [denoteArg_eq_some_resolveEnvArg hΓ hmV a ha ctDflt]; dsimp only
    cases plan with
    | node1 pk =>
      rw [$eqP, $eqF]; simp only
      cases toRealArg? (flattenArg (resolveEnvArg inVD inVE a ctDflt)) with
      | none => rfl
      | some _ =>
        dsimp only [toTFlat]
        exact congrArg (TFlat.load t _)
          (ih pk (.cons hΓ) (hmV.cons t (Arg.var (some outVD))) hlr hk)
    | _ => rw [$eqP, $eqF]; simp only; rfl,
  @fun _ _ _ _ _ inVD _ _ _ inVE _ plan v a k hΓ _ hmV hlr hwf ih => by
    obtain ⟨hv, ha, hk⟩ := wf_store hwf; dsimp only [denote]
    rw [denoteArg_eq_some_resolveEnvArg hΓ hmV v hv ctDflt,
      denoteArg_eq_some_resolveEnvArg hΓ hmV a ha ctDflt]; dsimp only
    cases plan with
    | node1 pk =>
      rw [$eqP, $eqF]; simp only
      cases toRealArg? (flattenArg (resolveEnvArg inVD inVE v ctDflt)) with
      | none => rfl
      | some _ =>
        cases toRealArg? (flattenArg (resolveEnvArg inVD inVE a ctDflt)) with
        | none => rfl
        | some _ => dsimp only [toTFlat]; exact congrArg (TFlat.store _ _) (ih pk hΓ hmV hlr hk)
    | _ => rw [$eqP, $eqF]; simp only; rfl,
  @fun _ _ _ _ _ inVD outVD _ _ inVE _ plan f bs args k hΓ _ hmV hlr hwf ih => by
    obtain ⟨ha, hk⟩ := wf_call hwf; dsimp only [denote]
    rw [denoteArgs_eq_some_resolveEnvArgs hΓ hmV args ha ctDflt]; dsimp only
    cases plan with
    | node1 pk =>
      rw [$eqP, $eqF]; simp only
      cases toRealArgs? (flattenArgs (resolveEnvArgs inVD inVE args ctDflt)) with
      | none => rfl
      | some _ =>
        dsimp only [toTFlat]
        have hfresh := trieCtxMatch_insertFreshWith
          (fun _ _ od => Arg.var (some od)) hmV bs outVD
        rw [mkFreshOptArg_eq_toOptArgTup] at hfresh
        exact congrArg (TFlat.call f bs _) (ih pk (ctxTypes_pushTup_rev _ hΓ) hfresh hlr hk)
    | _ => rw [$eqP, $eqF]; simp only; rfl,
  @fun _ _ _ _ inVD _ _ _ inVE _ plan c t e hΓ _ hmV _ hwf iht ihe => by
    obtain ⟨hc, ht, he⟩ := wf_jnz hwf
    dsimp only [denote]; rw [denoteArg_eq_some_resolveEnvArg hΓ hmV c hc ctDflt]; dsimp only
    cases plan with
    | node2 pt pe =>
      rw [$eqP, $eqF]; simp only
      cases flattenArg (resolveEnvArg inVD inVE c ctDflt) with
      | imm b => cases b with | true => exact iht pt ht | false => exact ihe pe he
      | var v? =>
        cases v? with
        | none => rfl
        | some _ => dsimp only [toTFlat]; rw [iht pt ht, ihe pe he]
    | _ => rw [$eqP, $eqF]; simp only; rfl,
  $onJump,
  @fun _ _ _ _ inVD _ _ _ inVE _ plan vs' hΓ _ hmV _ hwf => by
    dsimp only [denote]; rw [denoteArgs_eq_some_resolveEnvArgs hΓ hmV vs' hwf ctDflt]; dsimp only
    cases plan with
    | leaf =>
      rw [$eqP, $eqF]; simp only
      cases toRealArgs? (flattenArgs (resolveEnvArgs inVD inVE vs' ctDflt)) <;> rfl
    | _ => rw [$eqP, $eqF]; simp only; rfl,
  @fun _ _ _ _ _ inVD _ _ _ inVE _ plan _ args hΓ _ hmV _ hwf => by
    dsimp only [denote]; rw [denoteArgs_eq_some_resolveEnvArgs hΓ hmV args hwf ctDflt]; dsimp only
    cases plan with
    | leaf =>
      rw [$eqP, $eqF]; simp only
      cases toRealArgs? (flattenArgs (resolveEnvArgs inVD inVE args ctDflt)) <;> rfl
    | _ => rw [$eqP, $eqF]; simp only; rfl,
  fun plan _ _ _ _ _ => by
    dsimp only [denote]; cases plan <;> rw [$eqP, $eqF] <;> simp only <;> rfl,
  $onGroup, $onNil, $onCons⟩)

private theorem rewriteCTInlineFlat_eq {rs : List Ty} :
    (plan : CTPlan) → (tf : TFlat rs) → {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × Arg (CTOptV K) t)} →
    {ls : List ((ts : List Ty) × CTLabel K KL rs ts)} →
    {inVD inLD outVD outLD : Nat} →
    {inVE : Trie ((t : Ty) × Arg (CTOptV K) t)} →
    {inLE : Trie ((ts : List Ty) × CTLabelFlat rs ts)} →
    CtxTypes Γ vs → CtxTypes Δ ls → TrieCtxMatch inVD inVE vs →
    TrieRelMatch (fun _ => CTLabelFlatMatch (rs := rs)) inLD inLE ls → tf.wfCheck Γ Δ = true →
    toTFlat (rewriteCTInline plan (denote (Arg (CTOptV K)) (CTLabel K KL rs) tf vs ls))
        outVD outLD =
      rewriteCTInlineFlat inLD inLE plan inVD inVE outVD outLD tf := by
  intro plan tf Γ Δ vs ls inVD inLD outVD outLD inVE inLE hΓ hΔ hmV hmL hwf
  refine (relSim_mutual (rs := rs)
    (W := Arg (CTOptV K)) (L₁ := CTLabelFlat rs) (L₂ := CTLabel K KL rs)
    (S := CTPlan) (SB := Unit)
    (LR := fun Δ inLD inLE ls =>
      CtxTypes Δ ls ∧ TrieRelMatch (fun _ => CTLabelFlatMatch (rs := rs)) inLD inLE ls)
    (P := fun plan tf _ _ vs ls inVD inVE inLD inLE outVD outLD =>
      toTFlat (rewriteCTInline plan (denote (Arg (CTOptV K)) (CTLabel K KL rs) tf vs ls))
          outVD outLD =
        rewriteCTInlineFlat inLD inLE plan inVD inVE outVD outLD tf)
    (PB := fun _ _ _ _ _ _ _ _ _ _ _ _ => True)
    (ct_rw_rel rewriteCTInline.eq_def, rewriteCTInlineFlat.eq_def,
      @fun _ _ _ _ _ inVD outVD _ outLD inVE _ plan j args hΓ _ hmV hlr hwf => by
        obtain ⟨hj, ha⟩ := wf_jump hwf
        obtain ⟨w₁, w₂, hres, hlk, hm⟩ := TrieRelMatch.resolveLabel_rel hlr.1 hlr.2 hj
        dsimp only [denote]
        rw [hlk, denoteArgs_eq_some_resolveEnvArgs hΓ hmV args ha ctDflt]; dsimp only
        cases plan with
        | jump _ =>
          rw [rewriteCTInline.eq_def, rewriteCTInlineFlat.eq_def]; simp only; rw [hres]; simp only
          by_cases hcan :
              w₂.target.canEmit (flattenArgs (resolveEnvArgs inVD inVE args ctDflt)) = true
          · rw [hm.1]; simp only [hcan, ↓reduceIte]
            exact emitCTTargetFlat_eq outVD outLD _ w₂.target
          · rw [hm.1]; simp only [hcan, Bool.false_eq_true, ↓reduceIte]
            have hi := hm.2 outVD outLD (flattenArgs (resolveEnvArgs inVD inVE args ctDflt))
            cases h1 : w₁.inline? outVD outLD _ <;> cases h2 : w₂.inline? _ <;>
              simp only [h1, h2, ORel] at hi
            · rfl
            · exact hi.symm
        | _ => rw [rewriteCTInline.eq_def, rewriteCTInlineFlat.eq_def]; simp only; rfl,
      fun plan _ _ _ _ _ _ _ _ _ => by
        dsimp only [denote]
        cases plan <;> rw [rewriteCTInline.eq_def, rewriteCTInlineFlat.eq_def] <;>
          simp only <;> rfl,
      fun _ _ _ _ _ _ => trivial,
      fun _ _ _ _ _ _ _ _ _ _ => trivial)).1 tf plan hΓ hΔ hmV ⟨hΔ, hmL⟩ hwf

/-! ## 3. Shared Head-Inline Helper & `validateCTPlanFlat` Equivalence -/

private theorem peelValidate_eq {W : Ty → Type} {LFlat L : List Ty → Type} {rs ts : List Ty}
    (R : (ts' : List Ty) → LFlat ts' → CTLabel W L rs ts' → Prop)
    (checkJ : ∀ {ts' : List Ty}, LFlat ts' → Tup (Arg (CTOptV W)) ts' → Bool)
    (hJ : ∀ {ts' jl j a}, R ts' jl j → checkJ jl a = (j.target.canEmit a || (j.inline? a).isSome))
    {Γ : List Ty} {Δ : List (List Ty)}
    {vs : List ((t : Ty) × Arg (CTOptV W) t)} {ls : List ((ts' : List Ty) × CTLabel W L rs ts')}
    {inVD inLD : Nat} {inVE : Trie ((t : Ty) × Arg (CTOptV W) t)}
    {inLE : Trie ((ts' : List Ty) × LFlat ts')}
    (hΓ : CtxTypes Γ vs) (hΔ : CtxTypes Δ ls) (hmV : TrieCtxMatch inVD inVE vs)
    (hmL : TrieRelMatch R inLD inLE ls) (pb : CTPlan) (b : TFlat rs)
    (hb : b.wfCheck (pushTypes ts Γ) Δ = true) (args : Tup (Arg (CTOptV W)) ts)
    (budgetFn : Bool → Nat) :
    let r := peelThreadHeadFlat 4 false pb (inVD + ts.length) (insertTupEnv inVD inVE args) b
    let resP := peelThreadHead 4 false pb
      (denote (Arg (CTOptV W)) (CTLabel W L rs) b (pushTup args vs) ls)
    ∃ Γ' vs', CtxTypes Γ' vs' ∧ TrieCtxMatch r.2.2.1 r.2.2.2.1 vs' ∧
      r.2.2.2.2.wfCheck Γ' Δ = true ∧
      resP = (r.1, r.2.1, denote (Arg (CTOptV W)) (CTLabel W L rs) r.2.2.2.2 vs' ls) ∧
      validateInlineFlat checkJ inLD inLE (budgetFn r.1) r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2 =
        validateInline (budgetFn resP.1) resP.2.1 resP.2.2 := by
  have hp := peelThreadHeadFlat_eq 4 false pb b (ctxTypes_pushTup_rev args hΓ) hΔ
    (trieCtxMatch_insertTupEnv hmV args) hb
  obtain ⟨Γ', vs', hΓ', hmV', hwf', hpeel⟩ := hp
  refine ⟨Γ', vs', hΓ', hmV', hwf', hpeel, ?_⟩
  rw [hpeel]
  exact validateInlineFlat_eq R checkJ hJ _ _ _ hΓ' hΔ hmV' hmL hwf'

private theorem validTargetsFlat_match {rs : List Ty} :
    (acts : List BlockAct) → (sig : List (List Ty)) →
    TRel (fun _ => ValidLFlatMatch (rs := rs)) (validTargetsFlat acts sig) (validTargets acts sig)
  | _, [] => .nil
  | [], _ :: sig => .cons ⟨rfl, fun _ => rfl⟩ (validTargetsFlat_match [] sig)
  | _ :: acts, _ :: sig => .cons ⟨rfl, fun _ => rfl⟩ (validTargetsFlat_match acts sig)

private theorem tryMakeValidInlineFlat_match {rs ts : List Ty}
    {Γ : List Ty} {Δ : List (List Ty)}
    {vs : List ((t : Ty) × Arg (CTOptV UnitV) t)}
    {ls : List ((ts' : List Ty) × ValidL rs ts')}
    {inVD inLD : Nat}
    {inVE : Trie ((t : Ty) × Arg (CTOptV UnitV) t)}
    {inLE : Trie ((ts' : List Ty) × ValidLFlat rs ts')}
    (hΓ : CtxTypes Γ vs) (hΔ : CtxTypes Δ ls) (hmV : TrieCtxMatch inVD inVE vs)
    (hmL : TrieRelMatch (fun _ => ValidLFlatMatch (rs := rs)) inLD inLE ls)
    (act : BlockAct) (pb : CTPlan) (b : TFlat rs) (hb : b.wfCheck (pushTypes ts Γ) Δ = true)
    {lF : ValidLFlat rs ts} {lP : ValidL rs ts} (hl : ValidLFlatMatch lF lP) :
    ValidLFlatMatch (tryMakeValidInlineFlat inVD inVE inLD inLE act pb b lF)
      (tryMakeInlineLabel act pb (fun args => denote (Arg (CTOptV UnitV)) (ValidL rs) b
        (pushTup args vs) ls) lP) := by
  have hJ : ∀ {ts' : List Ty} {jl : ValidLFlat rs ts'} {j : ValidL rs ts'}
      {a : Tup (Arg (CTOptV UnitV)) ts'},
      ValidLFlatMatch jl j → (jl.target.canEmit a || jl.inlineOk? a) =
        (j.target.canEmit a || (j.inline? a).isSome) := fun hm => by rw [hm.1, hm.2 _]
  cases act with
  | keep _ bInl =>
    cases bInl with
    | false => exact hl
    | true =>
      refine ⟨hl.1, fun args => ?_⟩
      dsimp only [tryMakeValidInlineFlat, tryMakeInlineLabel]
      obtain ⟨_, _, _, _, _, _, hval⟩ := peelValidate_eq
        (fun _ => ValidLFlatMatch (rs := rs)) _ hJ hΓ hΔ hmV hmL pb b hb args
        (fun res => if res then 8 else 3)
      rw [hval]
      cases (validateInline _ _ _).isSome <;> rfl
  | splitBool _ _ _ _ inlT inlF =>
    by_cases hInl : (inlT || inlF) = true
    · dsimp only [tryMakeValidInlineFlat, tryMakeInlineLabel]
      simp only [hInl, ↓reduceIte]
      refine ⟨hl.1, fun args => ?_⟩
      dsimp only
      obtain ⟨_, _, _, _, _, hpeel, hval⟩ := peelValidate_eq
        (fun _ => ValidLFlatMatch (rs := rs)) _ hJ hΓ hΔ hmV hmL pb b hb args (fun _ => 8)
      rw [hval, hpeel]; dsimp only
      cases (_ && (validateInline 8 _ _).isSome) <;> rfl
    · dsimp only [tryMakeValidInlineFlat, tryMakeInlineLabel]
      simp only [hInl, Bool.false_eq_true, ↓reduceIte]; exact hl

private theorem attachInlinesGen_match {W : Ty → Type} {LFlat L : List Ty → Type} {rs : List Ty}
    {Γ : List Ty} {Δ : List (List Ty)}
    {vs : List ((t : Ty) × Arg (CTOptV W) t)}
    {ls : List ((ts : List Ty) × CTLabel W L rs ts)}
    (R : (ts : List Ty) → LFlat ts → CTLabel W L rs ts → Prop)
    (tryF : ∀ {ts : List Ty}, BlockAct → CTPlan → TFlat rs → LFlat ts → LFlat ts)
    (attachF : List BlockAct → CTPlanB → ∀ {sig : List (List Ty)},
      TBlocks rs sig → Tup LFlat sig → Tup LFlat sig)
    (hNilActs : ∀ {ts : List Ty} {sig : List (List Ty)} (pbs : CTPlanB)
      (b : TFlat rs) (bs : TBlocks rs sig) (l : LFlat ts) (ls : Tup LFlat sig),
      attachF [] pbs (.cons b bs) (l, ls) = (l, attachF [] .nil bs ls))
    (hNilPbs : ∀ {ts : List Ty} {sig : List (List Ty)} (acts : List BlockAct)
      (b : TFlat rs) (bs : TBlocks rs sig) (l : LFlat ts) (ls : Tup LFlat sig),
      attachF acts .nil (.cons b bs) (l, ls) = (l, attachF [] .nil bs ls))
    (hCons : ∀ {ts : List Ty} {sig : List (List Ty)}
      (a : BlockAct) (acts : List BlockAct) (pb : CTPlan) (pbs : CTPlanB)
      (b : TFlat rs) (bs : TBlocks rs sig) (l : LFlat ts) (ls : Tup LFlat sig),
      attachF (a :: acts) (.cons pb pbs) (.cons b bs) (l, ls) =
        (tryF a pb b l, attachF acts pbs bs ls))
    (htry : ∀ {ts : List Ty} (a : BlockAct) (pb : CTPlan) (b : TFlat rs),
      b.wfCheck (pushTypes ts Γ) Δ = true → ∀ {lF : LFlat ts} {lP : CTLabel W L rs ts},
      R ts lF lP → R ts (tryF a pb b lF) (tryMakeInlineLabel a pb
        (fun args => denote (Arg (CTOptV W)) (CTLabel W L rs) b (pushTup args vs) ls) lP)) :
    (acts : List BlockAct) → (pbs : CTPlanB) → {sig : List (List Ty)} → (tb : TBlocks rs sig) →
    {lsF : Tup LFlat sig} → {lsP : Tup (CTLabel W L rs) sig} →
    TRel R lsF lsP → tb.wfCheck Γ Δ = true →
    TRel R (attachF acts pbs tb lsF)
      (attachInlines acts pbs (denoteB (Arg (CTOptV W)) (CTLabel W L rs) tb vs ls) lsP)
  | _, _, [], .nil, (), (), .nil, _ => .nil
  | [], _, _ :: _, .cons _ bs, (_, _), (_, _), .cons hl hls, hwf => by
    rw [hNilActs]; obtain ⟨_, hbs⟩ := wf_cons hwf
    exact .cons hl (attachInlinesGen_match R tryF attachF hNilActs hNilPbs hCons htry
      [] .nil bs hls hbs)
  | _ :: _, .nil, _ :: _, .cons _ bs, (_, _), (_, _), .cons hl hls, hwf => by
    rw [hNilPbs]; obtain ⟨_, hbs⟩ := wf_cons hwf
    exact .cons hl (attachInlinesGen_match R tryF attachF hNilActs hNilPbs hCons htry
      [] .nil bs hls hbs)
  | a :: acts', .cons pb pbs', _ :: _, .cons b bs, (_, _), (_, _), .cons hl hls, hwf => by
    obtain ⟨hb, hbs⟩ := wf_cons hwf
    rw [hCons]; dsimp only [denoteB, attachInlines]
    exact .cons (htry a pb b hb hl)
      (attachInlinesGen_match R tryF attachF hNilActs hNilPbs hCons htry
        acts' pbs' bs hls hbs)

local macro "vct_node1" eqF:Lean.Parser.Tactic.rwRule "," eqP:Lean.Parser.Tactic.rwRule ","
    plan:Lean.Parser.Tactic.elimTarget "," pk:ident ","
    pre:tacticSeq "," body:tacticSeq : tactic => `(tactic| (
  ($pre); dsimp only
  cases $plan with
  | node1 $pk => rw [$eqF, $eqP]; simp only; ($body)
  | _ => rw [$eqF, $eqP]))

private theorem validateCTPlanFlat_both {rs : List Ty} :
    (∀ (tf : TFlat rs) {Γ Δ vs ls inVD} {_outVD : Nat} {inLD} {_outLD : Nat} {inVE inLE}
      (plan : CTPlan),
      CtxTypes Γ vs → CtxTypes Δ ls → TrieCtxMatch inVD inVE vs →
      (CtxTypes Δ ls ∧
        TrieRelMatch (fun _ => ValidLFlatMatch (rs := rs)) inLD inLE ls) →
      tf.wfCheck Γ Δ = true →
      validateCTPlanFlat plan inVD inVE inLD inLE tf =
        validateCTPlan plan (denote (Arg (CTOptV UnitV)) (ValidL rs) tf vs ls)) ∧
    (∀ {sig : List (List Ty)} (tb : TBlocks rs sig)
      {Γ Δ vs ls inVD} {_outVD : Nat} {inLD} {_outLD : Nat} {inVE inLE}
      (sp : List BlockAct × CTPlanB),
      CtxTypes Γ vs → CtxTypes Δ ls → TrieCtxMatch inVD inVE vs →
      (CtxTypes Δ ls ∧
        TrieRelMatch (fun _ => ValidLFlatMatch (rs := rs)) inLD inLE ls) →
      tb.wfCheck Γ Δ = true →
      validateCTBlocksFlat sp.1 sp.2 inVD inVE inLD inLE tb =
        validateCTBlocks sp.1 sp.2 (denoteB (Arg (CTOptV UnitV)) (ValidL rs) tb vs ls)) := by
  refine relSim_mutual
    (LR := fun Δ inLD inLE ls =>
      CtxTypes Δ ls ∧ TrieRelMatch (fun _ => ValidLFlatMatch (rs := rs)) inLD inLE ls) ⟨
    @fun ts _ _ _ _ inVD _ _ _ inVE _ plan op k hΓ _ hmV hlr hwf ih => by
      vct_node1 validateCTPlanFlat.eq_def, validateCTPlan.eq_def, plan, pk,
        (obtain ⟨ha, hk⟩ := wf_let hwf; dsimp only [denote];
         rw [denoteArgs_eq_some_resolveEnvArgs hΓ hmV op.args ha ctDflt]),
        (cases evalThreadLet? op.code (flattenArgs (resolveEnvArgs inVD inVE op.args ctDflt)) with
         | some out =>
           exact ih (outVD' := 0) (outLD' := 0) pk (ctxTypes_pushTup_rev out hΓ)
             (trieCtxMatch_insertTupEnv hmV out) hlr hk
         | none =>
           exact ih (outVD' := 0) (outLD' := 0) pk (ctxTypes_pushTup_rev _ hΓ)
             (trieCtxMatch_insertTupEnv hmV _) hlr hk),
    fun plan t a k hΓ _ hmV hlr hwf ih => by
      vct_node1 validateCTPlanFlat.eq_def, validateCTPlan.eq_def, plan, pk,
        (obtain ⟨ha, hk⟩ := wf_load hwf; dsimp only [denote];
         rw [denoteArg_eq_some_resolveEnvArg hΓ hmV a ha ctDflt]),
        exact ih (outVD' := 0) (outLD' := 0) pk (.cons hΓ) (hmV.cons t (Arg.var (some ()))) hlr hk,
    fun plan v a k hΓ _ hmV hlr hwf ih => by
      vct_node1 validateCTPlanFlat.eq_def, validateCTPlan.eq_def, plan, pk,
        (obtain ⟨hv, ha, hk⟩ := wf_store hwf; dsimp only [denote];
         rw [denoteArg_eq_some_resolveEnvArg hΓ hmV v hv ctDflt,
           denoteArg_eq_some_resolveEnvArg hΓ hmV a ha ctDflt]),
        exact ih (outVD' := 0) (outLD' := 0) pk hΓ hmV hlr hk,
    fun plan _ bs args k hΓ _ hmV hlr hwf ih => by
      vct_node1 validateCTPlanFlat.eq_def, validateCTPlan.eq_def, plan, pk,
        (obtain ⟨ha, hk⟩ := wf_call hwf; dsimp only [denote];
         rw [denoteArgs_eq_some_resolveEnvArgs hΓ hmV args ha ctDflt]),
        exact ih (outVD' := 0) (outLD' := 0) pk (ctxTypes_pushTup_rev _ hΓ)
          (trieCtxMatch_insertTupEnv hmV _) hlr hk,
    @fun _ _ _ _ inVD _ _ _ inVE _ plan c t e hΓ _ hmV _ hwf iht ihe => by
      obtain ⟨hc, ht, he⟩ := wf_jnz hwf
      dsimp only [denote]; rw [denoteArg_eq_some_resolveEnvArg hΓ hmV c hc ctDflt]; dsimp only
      cases plan with
      | node2 pt pe =>
        rw [validateCTPlanFlat.eq_def, validateCTPlan.eq_def]; simp only
        cases flattenArg (resolveEnvArg inVD inVE c ctDflt) with
        | imm b => cases b with | true => exact iht pt ht | false => exact ihe pe he
        | var _ => dsimp only; rw [iht pt ht, ihe pe he]
      | _ => rw [validateCTPlanFlat.eq_def, validateCTPlan.eq_def],
    @fun _ _ _ _ _ inVD _ _ _ inVE _ plan j args hΓ _ hmV hlr hwf => by
      obtain ⟨hj, ha⟩ := wf_jump hwf
      obtain ⟨w₁, w₂, hres, hlk, hm⟩ := TrieRelMatch.resolveLabel_rel hlr.1 hlr.2 hj
      dsimp only [denote]
      rw [hlk, denoteArgs_eq_some_resolveEnvArgs hΓ hmV args ha ctDflt]; dsimp only
      cases plan with
      | jump tryInl =>
        rw [validateCTPlanFlat.eq_def, validateCTPlan.eq_def]; simp only
        rw [hres]; simp only [hm.1]
        cases tryInl with
        | false => rfl
        | true =>
          rw [hm.2 (flattenArgs (resolveEnvArgs inVD inVE args ctDflt))]
          cases w₂.inline? (flattenArgs (resolveEnvArgs inVD inVE args ctDflt)) <;> rfl
      | _ => rw [validateCTPlanFlat.eq_def, validateCTPlan.eq_def],
    fun plan vs' hΓ _ hmV _ hwf => by
      dsimp only [denote]
      rw [denoteArgs_eq_some_resolveEnvArgs hΓ hmV vs' hwf ctDflt]; dsimp only
      cases plan <;> rw [validateCTPlanFlat.eq_def, validateCTPlan.eq_def] <;> simp only,
    fun plan _ args hΓ _ hmV _ hwf => by
      dsimp only [denote]
      rw [denoteArgs_eq_some_resolveEnvArgs hΓ hmV args hwf ctDflt]; dsimp only
      cases plan <;> rw [validateCTPlanFlat.eq_def, validateCTPlan.eq_def] <;> simp only,
    fun plan _ _ _ _ _ => by
      dsimp only [denote]
      cases plan <;> rw [validateCTPlanFlat.eq_def, validateCTPlan.eq_def] <;> simp only,
    @fun sig _ Δ vs ls inVD outVD inLD outLD inVE inLE plan bodies k hΓ hΔ hmV hlr hwf ihB ihK => by
      obtain ⟨hb, hk⟩ := wf_group hwf
      dsimp only [denote]
      cases plan with
      | group acts pbs pk =>
        rw [validateCTPlanFlat.eq_def, validateCTPlan.eq_def]; simp only
        have hno := validTargetsFlat_match (rs := rs) acts sig
        have hbody := attachInlinesGen_match (fun _ => ValidLFlatMatch (rs := rs))
          (tryMakeValidInlineFlat inVD inVE _ _)
          (attachValidInlinesFlat inVD inVE _ _)
          (fun pbs _ _ _ _ => by cases pbs <;> (rw [attachValidInlinesFlat.eq_def]; rfl))
          (fun acts _ _ _ _ => by cases acts <;> (rw [attachValidInlinesFlat.eq_def]; rfl))
          (fun _ _ _ _ _ _ _ _ => rfl)
          (tryMakeValidInlineFlat_match hΓ (ctxTypes_pushTup_rev _ hΔ) hmV
            (TrieRelMatch.pushTup hno hlr.2))
          acts pbs bodies hno hb
        have hmBody := TrieRelMatch.pushTup hbody hlr.2
        have hΔ' := ctxTypes_pushTup_rev
          (attachInlines acts pbs (denoteB (Arg (CTOptV UnitV)) (ValidL rs) bodies vs
            (pushTup (validTargets acts sig) ls)) (validTargets acts sig)) hΔ
        rw [ihB (outLD' := outLD) (acts, pbs) hΔ' ⟨hΔ', hmBody⟩ hb,
          ihK (outLD' := outLD) pk hΔ' ⟨hΔ', hmBody⟩ hk]
      | _ => rw [validateCTPlanFlat.eq_def, validateCTPlan.eq_def],
    fun ⟨acts, pbs⟩ _ _ _ _ _ => by
      rw [validateCTBlocksFlat.eq_def, denoteB.eq_def, validateCTBlocks.eq_def]; simp only
      cases pbs <;> cases acts <;> rfl,
    @fun ts _ _ _ _ _ _ _ _ _ _ _ ⟨acts, pbs⟩ b bs hΓ _ hmV hlr hwf ih ihs => by
      obtain ⟨hb, hbs⟩ := wf_cons hwf
      cases pbs with
      | nil => rw [validateCTBlocksFlat.eq_def, denoteB.eq_def, validateCTBlocks.eq_def]; simp only
      | cons pb pbs' =>
        cases acts with
        | nil =>
          rw [validateCTBlocksFlat.eq_def, denoteB.eq_def, validateCTBlocks.eq_def]; simp only
        | cons a acts' =>
          rw [validateCTBlocksFlat.eq_def, denoteB.eq_def, validateCTBlocks.eq_def]; simp only
          have hrest := ihs (acts', pbs') hbs
          have hpb (args : Tup (Arg (CTOptV UnitV)) ts) :=
            ih (outVD' := 0) (outLD' := 0) pb (ctxTypes_pushTup_rev args hΓ)
              (trieCtxMatch_insertTupEnv hmV args) hlr hb
          cases a with
          | keep keepB _ =>
            cases keepB <;> simp only
            · rw [hrest]
            · rw [hpb _, hrest]
          | splitBool p _ _ _ _ _ =>
            simp only
            cases splitMember? p ts <;> simp only
            · rw [hpb _, hrest]
            · rw [hpb _, hpb _, hrest]⟩

/-! ## 4. `rewriteCTFlat` Equivalence -/

private theorem toTBlocks_append {rs : List Ty} :
    {s₁ s₂ : List (List Ty)} → (b₁ : Blocks K KL rs s₁) → (b₂ : Blocks K KL rs s₂) →
    (vd ld : Nat) →
    toTBlocks (blocksAppend b₁ b₂) vd ld =
      tblocksAppend (toTBlocks b₁ vd ld) (toTBlocks b₂ vd ld)
  | [], _, .nil, _, _, _ => rfl
  | _ :: _, _, .cons _ b₁, b₂, vd, ld => by
    dsimp only [blocksAppend, toTBlocks, tblocksAppend]
    exact congrArg (TBlocks.cons _) (toTBlocks_append b₁ b₂ vd ld)

private theorem toTBlocks_mkHltBlocks {rs : List Ty} :
    (sig : List (List Ty)) → (vd ld : Nat) →
    toTBlocks (mkHltBlocks (V := K) (L := KL) (rs := rs) sig) vd ld = mkHltTBlocks sig
  | [], _, _ => rfl
  | _ :: sig, vd, ld => by
    dsimp only [mkHltBlocks, toTBlocks, toTFlat, mkHltTBlocks]
    exact congrArg (TBlocks.cons .hlt) (toTBlocks_mkHltBlocks sig vd ld)

private theorem toTBlocks_condConsBlock {rs ts : List Ty} (b : Bool)
    (blk : Unit → Tup K ts → Expr K KL rs) {rest : List (List Ty)}
    (tl : Blocks K KL rs rest) (vd ld : Nat) :
    toTBlocks (condConsBlock b blk tl) vd ld =
      condConsTBlock b (fun () => toTFlat (blk () (Tup.levels ts vd)) (vd + ts.length) ld)
        (toTBlocks tl vd ld) := by
  cases b <;> rfl

private theorem toTBlocks_mkSplitBlocks {rs ts : List Ty} (m : Member .bool ts)
    (keepDisp keepT keepF : Bool) {lF : CTLabelFlat rs ts} {lP : CTLabel K KL rs ts}
    (htgt : lF.target = lP.target) (rwT rwF : Tup K (eraseMem m) → Expr K KL rs)
    (vd ld : Nat) :
    toTBlocks (mkSplitBlocks m keepDisp keepT keepF lP rwT rwF) vd ld =
      mkSplitBlocksFlat m keepDisp keepT keepF lF vd ld
        (toTFlat (rwT (Tup.levels (eraseMem m) vd)) (vd + (eraseMem m).length) ld)
        (toTFlat (rwF (Tup.levels (eraseMem m) vd)) (vd + (eraseMem m).length) ld) := by
  dsimp only [mkSplitBlocks, mkSplitBlocksFlat]
  rw [toTBlocks_condConsBlock, toTBlocks_condConsBlock, toTBlocks_condConsBlock]
  refine congrArg (condConsTBlock keepDisp · _) ?_
  funext (); rw [htgt]
  cases lP.target with
  | keep _ | dead => rfl
  | split _ lT? lF? _ => cases lT? <;> cases lF? <;> rfl

private theorem toTBlocks_mkSplitCurBlocks {rs ts : List Ty} (keepT keepF keepDisp : Bool)
    {lF : CTLabelFlat rs ts} {lP : CTLabel K KL rs ts} (htgt : lF.target = lP.target)
    (rwId : Tup K ts → Expr K KL rs)
    (rwSplit : (m : Member .bool ts) → Bool → Tup K (eraseMem m) → Expr K KL rs)
    (vd ld : Nat) :
    (sp : Option (Member .bool ts)) →
    toTBlocks (mkSplitCurBlocks keepT keepF keepDisp lP rwId rwSplit sp) vd ld =
      mkSplitCurBlocksFlat keepT keepF keepDisp lF vd ld
        (toTFlat (rwId (Tup.levels ts vd)) (vd + ts.length) ld)
        (fun m bVal => toTFlat (rwSplit m bVal (Tup.levels (eraseMem m) vd))
          (vd + (eraseMem m).length) ld) sp
  | none => rfl
  | some m => toTBlocks_mkSplitBlocks m keepDisp keepT keepF htgt _ _ vd ld

private theorem buildTargetsFlat_match {rs : List Ty} :
    (acts : List BlockAct) → (sig : List (List Ty)) → (Js : Tup KL (threadSig acts sig)) →
    TRel (fun _ => CTLabelFlatMatch (rs := rs))
      (buildTargetsFlat acts sig Js) (buildTargets acts sig Js)
  | _, [], () => .nil
  | [], _ :: sig, (_, js) =>
    .cons ⟨rfl, fun _ _ _ => trivial⟩ (buildTargetsFlat_match [] sig js)
  | _ :: acts, _ :: sig, js => by
    dsimp only [buildTargetsFlat, buildTargets]
    exact .cons ⟨rfl, fun _ _ _ => trivial⟩ (buildTargetsFlat_match acts sig _)

private theorem tryMakeInlineLabelFlat_match {rs ts : List Ty}
    {Γ : List Ty} {Δ : List (List Ty)}
    {vs : List ((t : Ty) × Arg (CTOptV K) t)}
    {ls : List ((ts' : List Ty) × CTLabel K KL rs ts')}
    {inVD inLD : Nat}
    {inVE : Trie ((t : Ty) × Arg (CTOptV K) t)}
    {inLE : Trie ((ts' : List Ty) × CTLabelFlat rs ts')}
    (hΓ : CtxTypes Γ vs) (hΔ : CtxTypes Δ ls) (hmV : TrieCtxMatch inVD inVE vs)
    (hmL : TrieRelMatch (fun _ => CTLabelFlatMatch (rs := rs)) inLD inLE ls)
    (act : BlockAct) (pb : CTPlan) (b : TFlat rs) (hb : b.wfCheck (pushTypes ts Γ) Δ = true)
    {lF : CTLabelFlat rs ts} {lP : CTLabel K KL rs ts} (hl : CTLabelFlatMatch lF lP) :
    CTLabelFlatMatch (tryMakeInlineLabelFlat inVD inVE inLD inLE act pb b lF)
      (tryMakeInlineLabel act pb (fun args => denote (Arg (CTOptV K)) (CTLabel K KL rs) b
        (pushTup args vs) ls) lP) := by
  have hJ : ∀ {ts' : List Ty} {jl : CTLabelFlat rs ts'} {j : CTLabel K KL rs ts'}
      {a : Tup (Arg (CTOptV K)) ts'},
      CTLabelFlatMatch jl j → (jl.target.canEmit a || (jl.inline? 0 0 a).isSome) =
        (j.target.canEmit a || (j.inline? a).isSome) :=
    fun hm => by rw [hm.1, orel_isSome (hm.2 0 0 _)]
  cases act with
  | keep _ bInl =>
    cases bInl with
    | false => exact hl
    | true =>
      refine ⟨hl.1, fun ovd old args => ?_⟩
      dsimp only [tryMakeInlineLabelFlat, tryMakeInlineLabel]
      obtain ⟨Γ', vs', hΓ', hmV', hwf', hpeel, hval⟩ := peelValidate_eq
        (fun _ => CTLabelFlatMatch (rs := rs)) _ hJ hΓ hΔ hmV hmL pb b hb args
        (fun res => if res then 8 else 3)
      rw [hval, hpeel]; dsimp only
      cases (validateInline _ _ _).isSome with
      | false => simp [ORel]
      | true =>
        simp only [↓reduceIte, ORel]
        exact (rewriteCTInlineFlat_eq _ _ hΓ' hΔ hmV' hmL hwf').symm
  | splitBool _ _ _ _ inlT inlF =>
    by_cases hInl : (inlT || inlF) = true
    · dsimp only [tryMakeInlineLabelFlat, tryMakeInlineLabel]
      simp only [hInl, ↓reduceIte]
      refine ⟨hl.1, fun ovd old args => ?_⟩
      dsimp only
      obtain ⟨Γ', vs', hΓ', hmV', hwf', hpeel, hval⟩ := peelValidate_eq
        (fun _ => CTLabelFlatMatch (rs := rs)) _ hJ hΓ hΔ hmV hmL pb b hb args (fun _ => 8)
      rw [hval, hpeel]; dsimp only
      cases (_ && (validateInline 8 _ _).isSome) with
      | false => simp [ORel]
      | true =>
        simp only [↓reduceIte, ORel]
        exact (rewriteCTInlineFlat_eq _ _ hΓ' hΔ hmV' hmL hwf').symm
    · dsimp only [tryMakeInlineLabelFlat, tryMakeInlineLabel]
      simp only [hInl, Bool.false_eq_true, ↓reduceIte]; exact hl

private theorem rewriteCTFlat_both {rs : List Ty} :
    (∀ (tf : TFlat rs) {Γ Δ vs ls inVD outVD inLD outLD inVE inLE} (plan : CTPlan),
      CtxTypes Γ vs → CtxTypes Δ ls → TrieCtxMatch inVD inVE vs →
      (CtxTypes Δ ls ∧
        TrieRelMatch (fun _ => CTLabelFlatMatch (rs := rs)) inLD inLE ls) →
      tf.wfCheck Γ Δ = true →
      toTFlat (rewriteCTAux plan (denote (Arg (CTOptV K)) (CTLabel K KL rs) tf vs ls))
          outVD outLD =
        rewriteCTFlat plan inVD inVE inLD inLE outVD outLD tf) ∧
    (∀ {sig : List (List Ty)} (tb : TBlocks rs sig)
      {Γ Δ vs ls inVD outVD inLD outLD inVE inLE} (sp : List BlockAct × CTPlanB),
      CtxTypes Γ vs → CtxTypes Δ ls → TrieCtxMatch inVD inVE vs →
      (CtxTypes Δ ls ∧
        TrieRelMatch (fun _ => CTLabelFlatMatch (rs := rs)) inLD inLE ls) →
      tb.wfCheck Γ Δ = true →
      ∀ {lsF : Tup (CTLabelFlat rs) sig} {lsP : Tup (CTLabel K KL rs) sig},
        TRel (fun _ => CTLabelFlatMatch (rs := rs)) lsF lsP →
        toTBlocks (rewriteCTBlocks sp.1 sp.2
            (denoteB (Arg (CTOptV K)) (CTLabel K KL rs) tb vs ls) lsP) outVD outLD =
          rewriteCTBlocksFlat sp.1 sp.2 inVD inVE inLD inLE outVD outLD tb lsF) := by
  refine relSim_mutual
    (LR := fun Δ inLD inLE ls =>
      CtxTypes Δ ls ∧ TrieRelMatch (fun _ => CTLabelFlatMatch (rs := rs)) inLD inLE ls)
    (ct_rw_rel rewriteCTAux.eq_def, rewriteCTFlat.eq_def,
      @fun _ _ _ _ _ inVD outVD _ outLD inVE _ plan j args hΓ _ hmV hlr hwf => by
        obtain ⟨hj, ha⟩ := wf_jump hwf
        obtain ⟨w₁, w₂, hres, hlk, hm⟩ := TrieRelMatch.resolveLabel_rel hlr.1 hlr.2 hj
        dsimp only [denote]
        rw [hlk, denoteArgs_eq_some_resolveEnvArgs hΓ hmV args ha ctDflt]; dsimp only
        cases plan with
        | jump tryInl =>
          rw [rewriteCTAux.eq_def, rewriteCTFlat.eq_def]; simp only; rw [hres]; simp only
          exact CTLabelFlat_emitJump_eq tryInl hm outVD outLD _
        | _ => rw [rewriteCTAux.eq_def, rewriteCTFlat.eq_def]; simp only; rfl,
      @fun sig _ Δ vs ls inVD outVD inLD outLD inVE inLE plan bodies k hΓ hΔ hmV hlr hwf
          ihB ihK => by
        obtain ⟨hb, hk⟩ := wf_group hwf
        dsimp only [denote]
        cases plan with
        | group acts pbs pk =>
          rw [rewriteCTAux.eq_def, rewriteCTFlat.eq_def]; simp only [toTFlat]
          have hno :=
            buildTargetsFlat_match (rs := rs) acts sig (Tup.levels (threadSig acts sig) outLD)
          have hbody := attachInlinesGen_match (fun _ => CTLabelFlatMatch (rs := rs))
            (tryMakeInlineLabelFlat inVD inVE _ _)
            (attachInlinesFlat inVD inVE _ _)
            (fun pbs _ _ _ _ => by cases pbs <;> (rw [attachInlinesFlat.eq_def]; rfl))
            (fun acts _ _ _ _ => by cases acts <;> (rw [attachInlinesFlat.eq_def]; rfl))
            (fun _ _ _ _ _ _ _ _ => rfl)
            (tryMakeInlineLabelFlat_match hΓ (ctxTypes_pushTup_rev _ hΔ) hmV
              (TrieRelMatch.pushTup hno hlr.2))
            acts pbs bodies hno hb
          have hmBody := TrieRelMatch.pushTup hbody hlr.2
          have hΔ' := ctxTypes_pushTup_rev
            (attachInlines acts pbs (denoteB (Arg (CTOptV K)) (CTLabel K KL rs) bodies vs
              (pushTup (buildTargets acts sig (Tup.levels (threadSig acts sig) outLD)) ls))
              (buildTargets acts sig (Tup.levels (threadSig acts sig) outLD))) hΔ
          have hb' := ihB (outLD' := outLD + (threadSig acts sig).length) (acts, pbs) hΔ'
            ⟨hΔ', hmBody⟩ hb hno
          have hk' := ihK (outLD' := outLD + (threadSig acts sig).length) pk hΔ'
            ⟨hΔ', hmBody⟩ hk
          rw [hb', hk']
        | _ => rw [rewriteCTAux.eq_def, rewriteCTFlat.eq_def]; simp only; rfl,
      @fun _ _ _ _ _ outVD _ outLD _ _ ⟨acts, _⟩ _ _ _ _ _ _ _ hrel => by
        cases hrel
        rw [rewriteCTBlocksFlat.eq_def, denoteB.eq_def, rewriteCTBlocks.eq_def]; simp only
        exact toTBlocks_mkHltBlocks (threadSig acts []) outVD outLD,
      @fun ts _ _ _ vs ls inVD outVD inLD outLD inVE inLE ⟨acts, pbs⟩ b bs
          hΓ _ hmV hlr hwf ih ihs lsF lsP hrel => by
        obtain ⟨hb, hbs⟩ := wf_cons hwf
        rcases hrel with ⟨⟩ | ⟨hl, hls⟩
        cases pbs with
        | nil =>
          cases acts <;> rw [rewriteCTBlocksFlat.eq_def, denoteB.eq_def, rewriteCTBlocks.eq_def] <;>
            simp only <;> exact toTBlocks_mkHltBlocks _ outVD outLD
        | cons pb pbs' =>
          cases acts with
          | nil =>
            rw [rewriteCTBlocksFlat.eq_def, denoteB.eq_def, rewriteCTBlocks.eq_def]; simp only
            exact toTBlocks_mkHltBlocks _ outVD outLD
          | cons a acts' =>
            rw [rewriteCTBlocksFlat.eq_def, denoteB.eq_def, rewriteCTBlocks.eq_def]; simp only
            rw [toTBlocks_append]
            refine congr (congrArg tblocksAppend ?_) (ihs (acts', pbs') hbs hls)
            cases a with
            | keep keepB _ =>
              cases keepB with
              | true =>
                dsimp only [actSig, toTBlocks]
                have hfresh := trieCtxMatch_insertFreshWith
                  (fun _ _ od => Arg.var (some od)) hmV ts outVD
                rw [mkFreshOptArg_eq_toOptArgTup] at hfresh
                exact congrArg (TBlocks.cons · .nil)
                  (ih (outVD' := outVD + ts.length) (outLD' := outLD) pb
                    (ctxTypes_pushTup_rev _ hΓ) hfresh hlr hb)
              | false => rfl
            | splitBool p keepT keepF keepDisp _ _ =>
              dsimp only
              have h1 := toTBlocks_mkSplitCurBlocks keepT keepF keepDisp hl.1
                (fun xs => rewriteCTAux pb (denote (Arg (CTOptV K)) (CTLabel K KL rs) b
                  (pushTup (toOptArgTup xs) vs) ls))
                (fun m bVal xs => rewriteCTAux pb (denote (Arg (CTOptV K)) (CTLabel K KL rs) b
                  (pushTup (insertTupMem m (.imm bVal) (toOptArgTup xs)) vs) ls))
                outVD outLD (splitMember? p ts)
              rw [h1]
              have hfresh := trieCtxMatch_insertFreshWith
                (fun _ _ od => Arg.var (some od)) hmV ts outVD
              rw [mkFreshOptArg_eq_toOptArgTup] at hfresh
              have hid := ih (outVD' := outVD + ts.length) (outLD' := outLD) pb
                (ctxTypes_pushTup_rev _ hΓ) hfresh hlr hb
              have hsp : (fun (m : Member .bool ts) (bVal : Bool) => toTFlat (rewriteCTAux pb
                    (denote (Arg (CTOptV K)) (CTLabel K KL rs) b
                      (pushTup (insertTupMem m (Arg.imm (V := CTOptV K) bVal)
                        (toOptArgTup (Tup.levels (eraseMem m) outVD))) vs) ls))
                    (outVD + (eraseMem m).length) outLD) =
                  (fun (m : Member .bool ts) (bVal : Bool) => rewriteCTFlat pb (inVD + ts.length)
                    (insertTupEnv inVD inVE
                      (insertTupMem m (Arg.imm (V := CTOptV K) bVal)
                        (toOptArgTup (Tup.levels (eraseMem m) outVD))))
                    inLD inLE (outVD + (eraseMem m).length) outLD b) := by
                funext m bVal
                exact ih (outVD' := outVD + (eraseMem m).length) (outLD' := outLD) pb
                  (ctxTypes_pushTup_rev _ hΓ) (trieCtxMatch_insertTupEnv hmV _) hlr hb
              rw [hid, hsp])

/-! ## 5. Public `condThreadPassFlat` Equivalence Theorems -/

/-- `condThreadWithPlanFlat as plan tf = reifyFunc (Func.condThreadWithPlan plan (denoteFunc tf))`
under `wfCheck = true`. -/
theorem condThreadWithPlanFlat_eq {as rs : List Ty} (plan : CTPlan) (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    condThreadWithPlanFlat as plan tf =
      reifyFunc (Func.condThreadWithPlan plan (denoteFunc (as := as) tf)) := by
  dsimp only [condThreadWithPlanFlat, Func.condThreadWithPlan, denoteFunc, reifyFunc]
  have hmUnit := trieCtxMatch_initEnv
    (fun {t} (_ : K t) _ => (Arg.var (some ()) : Arg (CTOptV UnitV) t)) as
  rw [tupFreshUnitOpt_eq] at hmUnit
  have hval := validateCTPlanFlat_both.1 tf plan
    (ctxTypes_pushTup_rev (toOptArgTup (Tup.units as)) .nil) .nil hmUnit
    ⟨.nil, TrieRelMatch.empty (fun _ => ValidLFlatMatch (rs := rs))⟩ hwf
    (_outVD := 0) (_outLD := 0)
  rw [hval]
  by_cases hval' : validateCTPlan plan (denote (Arg (CTOptV UnitV)) (ValidL rs) tf
      (pushTup (toOptArgTup (Tup.units as)) []) []) = true
  · simp only [hval', ↓reduceIte]
    have hmK := trieCtxMatch_initEnv
      (fun {t} (x : K t) _ => (Arg.var (some x) : Arg (CTOptV K) t)) as
    rw [tupFreshSomeOpt_eq] at hmK
    have hrw := rewriteCTFlat_both.1 tf plan
      (ctxTypes_pushTup_rev (toOptArgTup (Tup.levels as 0)) .nil) .nil hmK
      ⟨.nil, TrieRelMatch.empty (fun _ => CTLabelFlatMatch (rs := rs))⟩ hwf
      (outVD := as.length) (outLD := 0)
    exact hrw.symm
  · simp only [hval', Bool.false_eq_true, ↓reduceIte]
    exact (reifyFunc_denoteFunc_eq tf hwf).symm

/-- `condThreadPassFlat as tf = reifyFunc (Func.condThreadPass (denoteFunc tf))` under
`wfCheck = true`. -/
theorem condThreadPassFlat_eq {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    condThreadPassFlat as tf =
      reifyFunc (Func.condThreadPass (denoteFunc (as := as) tf)) := by
  dsimp only [condThreadPassFlat, Func.condThreadPass]
  rw [reifyFunc_denoteFunc_eq tf hwf]
  split
  · exact condThreadWithPlanFlat_eq _ tf hwf
  · exact (reifyFunc_denoteFunc_eq tf hwf).symm

flat_pass_corollaries condThreadPassFlat, Func.condThreadPass, Func.condThreadPass_wf,
  condThreadPassFlat_eq, denoteFunc_condThreadPassFlat, condThreadPassFlat_wfCheck,
  condThreadPassFlatFn, condThreadPassFlatFn_toFn, condThreadPassFlatFn_wfCheck

end OptFlatBranch
end LeanQbe.T