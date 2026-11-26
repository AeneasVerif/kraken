module

public import LeanQbe.T.OptFlatBranchLemmas0
import LeanQbe.T.FlatDirectLemmas
import LeanQbe.T.PassFlatKit
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
    dsimp only [CTTarget.emit, emitCTTargetFlat]
    cases toRealArgs? args <;> rfl
  | .dead => rfl
  | .split m lT? lF? lD? => by
    dsimp only [CTTarget.emit, emitCTTargetFlat]
    cases getTupMem m args with
    | imm b =>
      cases b with
      | true =>
        cases lT? with
        | none => rfl
        | some lT => cases toRealArgs? (dropTupMem m args) <;> rfl
      | false =>
        cases lF? with
        | none => rfl
        | some lF => cases toRealArgs? (dropTupMem m args) <;> rfl
    | var v? =>
      cases v? with
      | none => rfl
      | some v =>
        cases lD? with
        | some lD => cases toRealArgs? args <;> rfl
        | none =>
          cases lT? with
          | none => rfl
          | some lT =>
            cases lF? with
            | none => rfl
            | some lF => cases toRealArgs? (dropTupMem m args) <;> rfl

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
    dsimp only [tupFreshWith, toOptArgTup]
    rw [tupFreshSomeOpt_eq ts xs (n + 1)]

private theorem tupFreshUnitOpt_eq :
    (ts : List Ty) → (xs : Tup K ts) → (n : Nat) →
    tupFreshWith (fun _ _ => Arg.var (some ())) ts xs n = toOptArgTup (Tup.units ts)
  | [], (), _ => rfl
  | _ :: ts, (_, xs), n => by
    dsimp only [tupFreshWith, Tup.units, toOptArgTup]
    rw [tupFreshUnitOpt_eq ts xs (n + 1)]

/-! ## 2. `peelThreadHeadFlat`, `validateInlineFlat`, and `rewriteCTInlineFlat` Equivalence -/

private theorem peelThreadHead_not_let_node1 {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (fuel : Nat) (res : Bool) (pk : CTPlan) {e : Expr (Arg (CTOptV V)) (CTLabel V L rs) rs}
    (h : ∀ {ts} (op : Op (Arg (CTOptV V)) ts) k, e = .let_ op k → False) :
    peelThreadHead fuel res (.node1 pk) e = (res, .node1 pk, e) := by
  cases fuel with
  | zero => rfl
  | succ _ =>
    cases e with
    | let_ op k => exact False.elim (h op k rfl)
    | _ => rfl

private theorem peelThreadHead_not_jnz_node2 {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (fuel : Nat) (res : Bool) (pt pe : CTPlan) {e : Expr (Arg (CTOptV V)) (CTLabel V L rs) rs}
    (h : ∀ c t e', e = .jnz c t e' → False) :
    peelThreadHead fuel res (.node2 pt pe) e = (res, .node2 pt pe, e) := by
  cases fuel with
  | zero => rfl
  | succ _ =>
    cases e with
    | jnz c t e' => exact False.elim (h c t e' rfl)
    | _ => rfl

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

private theorem denote_not_let {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    {vs : List ((t : Ty) × V t)} {ls : List ((ts : List Ty) × L ts)} :
    {tf : TFlat rs} → (∀ {dts} (op : Op K dts) k, tf = .let_ op k → False) →
    ∀ {dts} (op : Op V dts) k, denote V L tf vs ls = .let_ op k → False
  | .let_ op k, h, _, _, _, _ => h op k rfl
  | .load _ a _, _, _, _, _, h => by
    dsimp only [denote] at h; cases hda : denoteArg vs a <;> rw [hda] at h <;> cases h
  | .store v a _, _, _, _, _, h => by
    dsimp only [denote] at h
    cases hdv : denoteArg vs v <;> rw [hdv] at h
    · cases h
    · cases hda : denoteArg vs a <;> rw [hda] at h <;> cases h
  | .call _ _ args _, _, _, _, _, h => by
    dsimp only [denote] at h; cases hda : denoteArgs vs args <;> rw [hda] at h <;> cases h
  | .jnz c _ _, _, _, _, _, h => by
    dsimp only [denote] at h; cases hdc : denoteArg vs c <;> rw [hdc] at h <;> cases h
  | .jump j args, _, _, _, _, h => by
    dsimp only [denote] at h
    cases hdl : lookupL ls _ j <;> rw [hdl] at h
    · cases h
    · cases hda : denoteArgs vs args <;> rw [hda] at h <;> cases h
  | .ret vs', _, _, _, _, h => by
    dsimp only [denote] at h; cases hdv : denoteArgs vs vs' <;> rw [hdv] at h <;> cases h
  | .exit _ args, _, _, _, _, h => by
    dsimp only [denote] at h; cases hda : denoteArgs vs args <;> rw [hda] at h <;> cases h
  | .hlt, _, _, _, _, h => by cases h
  | .group _ _, _, _, _, _, h => by cases h

private theorem denote_not_jnz {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    {vs : List ((t : Ty) × V t)} {ls : List ((ts : List Ty) × L ts)} :
    {tf : TFlat rs} → (∀ c t e', tf = .jnz c t e' → False) →
    ∀ c t e', denote V L tf vs ls = .jnz c t e' → False
  | .jnz c t e', h, _, _, _, _ => h c t e' rfl
  | .let_ op _, _, _, _, _, h => by
    dsimp only [denote] at h; cases hda : denoteArgs vs op.args <;> rw [hda] at h <;> cases h
  | .load _ a _, _, _, _, _, h => by
    dsimp only [denote] at h; cases hda : denoteArg vs a <;> rw [hda] at h <;> cases h
  | .store v a _, _, _, _, _, h => by
    dsimp only [denote] at h
    cases hdv : denoteArg vs v <;> rw [hdv] at h
    · cases h
    · cases hda : denoteArg vs a <;> rw [hda] at h <;> cases h
  | .call _ _ args _, _, _, _, _, h => by
    dsimp only [denote] at h; cases hda : denoteArgs vs args <;> rw [hda] at h <;> cases h
  | .jump j args, _, _, _, _, h => by
    dsimp only [denote] at h
    cases hdl : lookupL ls _ j <;> rw [hdl] at h
    · cases h
    · cases hda : denoteArgs vs args <;> rw [hda] at h <;> cases h
  | .ret vs', _, _, _, _, h => by
    dsimp only [denote] at h; cases hdv : denoteArgs vs vs' <;> rw [hdv] at h <;> cases h
  | .exit _ args, _, _, _, _, h => by
    dsimp only [denote] at h; cases hda : denoteArgs vs args <;> rw [hda] at h <;> cases h
  | .hlt, _, _, _, _, h => by cases h
  | .group _ _, _, _, _, _, h => by cases h

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
  | 0, res, p, tf, Γ, _, vs, _, _, _, hΓ, _, hmV, hwf =>
    ⟨Γ, vs, hΓ, hmV, hwf, rfl⟩
  | fuel + 1, res, p, tf, Γ, Δ, vs, ls, inVD, inVE, hΓ, hΔ, hmV, hwf => by
    cases p with
    | node1 pk =>
      cases tf with
      | let_ op k =>
        have hwf0 := hwf
        dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
        have hargs := denoteArgs_eq_some_resolveEnvArgs hΓ hmV op.args hwf.1 ctDflt
        rw [peelThreadHeadFlat.eq_def]; simp only
        let args' := flattenArgs (resolveEnvArgs inVD inVE op.args ctDflt)
        cases hev : evalThreadLet? op.code args' with
        | some out =>
          simp only
          dsimp only [denote]; rw [hargs]; dsimp only [peelThreadHead]; rw [hev]
          exact peelThreadHeadFlat_eq fuel res pk k
            (ctxTypes_pushTup_rev out hΓ) hΔ (trieCtxMatch_insertTupEnv hmV out) hwf.2
        | none =>
          simp only
          refine ⟨Γ, vs, hΓ, hmV, hwf0, ?_⟩
          dsimp only [denote]; rw [hargs]; dsimp only
          rw [peelThreadHead.eq_def]; dsimp only; rw [hev]
      | load _ _ _ | store _ _ _ | call _ _ _ _ | jnz _ _ _
      | jump _ _ | ret _ | exit _ _ | hlt | group _ _ =>
        rw [peelThreadHeadFlat.eq_def]; simp only
        refine ⟨Γ, vs, hΓ, hmV, hwf, ?_⟩
        refine peelThreadHead_not_let_node1 (fuel + 1) res pk ?_
        exact denote_not_let (fun _ _ h => by cases h)
    | node2 pt pe =>
      cases tf with
      | jnz c t e =>
        have hwf0 := hwf
        dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
        have hc := denoteArg_eq_some_resolveEnvArg hΓ hmV c hwf.1.1 ctDflt
        rw [peelThreadHeadFlat.eq_def]; simp only
        cases hc' : flattenArg (resolveEnvArg inVD inVE c ctDflt) with
        | imm b =>
          dsimp only [denote]; rw [hc]; dsimp only [peelThreadHead]; rw [hc']
          cases b with
          | true => exact peelThreadHeadFlat_eq fuel true pt t hΓ hΔ hmV hwf.1.2
          | false => exact peelThreadHeadFlat_eq fuel true pe e hΓ hΔ hmV hwf.2
        | var v =>
          simp only
          refine ⟨Γ, vs, hΓ, hmV, hwf0, ?_⟩
          dsimp only [denote]; rw [hc]; dsimp only
          rw [peelThreadHead.eq_def]; dsimp only; rw [hc']
      | let_ _ _ | load _ _ _ | store _ _ _ | call _ _ _ _
      | jump _ _ | ret _ | exit _ _ | hlt | group _ _ =>
        rw [peelThreadHeadFlat.eq_def]; simp only
        refine ⟨Γ, vs, hΓ, hmV, hwf, ?_⟩
        refine peelThreadHead_not_jnz_node2 (fuel + 1) res pt pe ?_
        exact denote_not_jnz (fun _ _ _ h => by cases h)
    | leaf =>
      rw [peelThreadHeadFlat.eq_def]; simp only
      exact ⟨Γ, vs, hΓ, hmV, hwf,
        peelThreadHead_other (fuel + 1) res .leaf _
          (fun _ h => nomatch h) (fun _ _ h => nomatch h)⟩
    | jump _ =>
      rw [peelThreadHeadFlat.eq_def]; simp only
      exact ⟨Γ, vs, hΓ, hmV, hwf,
        peelThreadHead_other (fuel + 1) res (.jump _) _
          (fun _ h => nomatch h) (fun _ _ h => nomatch h)⟩
    | group _ _ _ =>
      rw [peelThreadHeadFlat.eq_def]; simp only
      exact ⟨Γ, vs, hΓ, hmV, hwf,
        peelThreadHead_other (fuel + 1) res (.group _ _ _) _
          (fun _ h => nomatch h) (fun _ _ h => nomatch h)⟩

private theorem validateInlineFlat_eq {W : Ty → Type} {LFlat : List Ty → Type}
    {L : List Ty → Type} {rs : List Ty}
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
      validateInline budget plan (denote (Arg (CTOptV W)) (CTLabel W L rs) tf vs ls)
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by
    rw [validateInlineFlat.eq_def, validateInline.eq_def]
  | b + 1, plan, .let_ (ts := dts) ⟨code, args⟩ k, Γ, Δ, vs, ls, inVD, inLD, inVE, inLE,
      hΓ, hΔ, hmV, hmL, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denote]
    rw [denoteArgs_eq_some_resolveEnvArgs hΓ hmV args hwf.1 ctDflt]; dsimp only
    cases plan with
    | node1 pk =>
      rw [validateInlineFlat.eq_def, validateInline.eq_def]; simp only
      cases evalThreadLet? code (flattenArgs (resolveEnvArgs inVD inVE args ctDflt)) with
      | some out =>
        exact validateInlineFlat_eq R checkJ hJ (b + 1) pk k
          (ctxTypes_pushTup_rev out hΓ) hΔ (trieCtxMatch_insertTupEnv hmV out) hmL hwf.2
      | none =>
        rw [validateInlineFlat_eq R checkJ hJ b pk k
          (ctxTypes_pushTup_rev (noneArgTup dts) hΓ) hΔ
          (trieCtxMatch_insertTupEnv hmV (noneArgTup dts)) hmL hwf.2]
    | leaf | jump _ | node2 _ _ | group _ _ _ =>
      rw [validateInlineFlat.eq_def, validateInline.eq_def]
  | b + 1, plan, .load t a k, Γ, Δ, vs, ls, inVD, inLD, inVE, inLE,
      hΓ, hΔ, hmV, hmL, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denote]
    rw [denoteArg_eq_some_resolveEnvArg hΓ hmV a hwf.1 ctDflt]; dsimp only
    cases plan with
    | node1 pk =>
      rw [validateInlineFlat.eq_def, validateInline.eq_def]; simp only
      rw [validateInlineFlat_eq R checkJ hJ b pk k (.cons hΓ) hΔ
        (hmV.cons t (Arg.var none)) hmL hwf.2]
    | leaf | jump _ | node2 _ _ | group _ _ _ =>
      rw [validateInlineFlat.eq_def, validateInline.eq_def]
  | b + 1, plan, .store v a k, Γ, Δ, vs, ls, inVD, inLD, inVE, inLE,
      hΓ, hΔ, hmV, hmL, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denote]
    rw [denoteArg_eq_some_resolveEnvArg hΓ hmV v hwf.1.1 ctDflt,
      denoteArg_eq_some_resolveEnvArg hΓ hmV a hwf.1.2 ctDflt]; dsimp only
    cases plan with
    | node1 pk =>
      rw [validateInlineFlat.eq_def, validateInline.eq_def]; simp only
      rw [validateInlineFlat_eq R checkJ hJ b pk k hΓ hΔ hmV hmL hwf.2]
    | leaf | jump _ | node2 _ _ | group _ _ _ =>
      rw [validateInlineFlat.eq_def, validateInline.eq_def]
  | b + 1, plan, .call f bs args k, Γ, Δ, vs, ls, inVD, inLD, inVE, inLE,
      hΓ, hΔ, hmV, hmL, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denote]
    rw [denoteArgs_eq_some_resolveEnvArgs hΓ hmV args hwf.1 ctDflt]; dsimp only
    cases plan with
    | node1 pk =>
      rw [validateInlineFlat.eq_def, validateInline.eq_def]; simp only
      rw [validateInlineFlat_eq R checkJ hJ b pk k
        (ctxTypes_pushTup_rev (noneArgTup bs) hΓ) hΔ
        (trieCtxMatch_insertTupEnv hmV (noneArgTup bs)) hmL hwf.2]
    | leaf | jump _ | node2 _ _ | group _ _ _ =>
      rw [validateInlineFlat.eq_def, validateInline.eq_def]
  | b + 1, plan, .jnz c t e, Γ, Δ, vs, ls, inVD, inLD, inVE, inLE,
      hΓ, hΔ, hmV, hmL, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denote]
    rw [denoteArg_eq_some_resolveEnvArg hΓ hmV c hwf.1.1 ctDflt]; dsimp only
    cases plan with
    | node2 pt pe =>
      rw [validateInlineFlat.eq_def, validateInline.eq_def]; simp only
      cases flattenArg (resolveEnvArg inVD inVE c ctDflt) with
      | imm bVal =>
        cases bVal with
        | true => exact validateInlineFlat_eq R checkJ hJ (b + 1) pt t hΓ hΔ hmV hmL hwf.1.2
        | false => exact validateInlineFlat_eq R checkJ hJ (b + 1) pe e hΓ hΔ hmV hmL hwf.2
      | var _ =>
        dsimp only
        rw [validateInlineFlat_eq R checkJ hJ b pt t hΓ hΔ hmV hmL hwf.1.2]
        cases hst : validateInline b pt (denote (Arg (CTOptV W)) (CTLabel W L rs) t vs ls) with
        | none => rfl
        | some st =>
          dsimp only [Bind.bind, Option.bind]
          rw [validateInlineFlat_eq R checkJ hJ (b - st) pe e hΓ hΔ hmV hmL hwf.2]
    | leaf | jump _ | node1 _ | group _ _ _ =>
      rw [validateInlineFlat.eq_def, validateInline.eq_def]
  | _ + 1, plan, .jump (ts := ts) j args, Γ, Δ, vs, ls, inVD, inLD, inVE, inLE,
      hΓ, hΔ, hmV, hmL, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨w₁, w₂, hres, hlk, hm⟩ := TrieRelMatch.resolveLabel_rel hΔ hmL hwf.1
    dsimp only [denote]
    rw [hlk, denoteArgs_eq_some_resolveEnvArgs hΓ hmV args hwf.2 ctDflt]; dsimp only
    cases plan with
    | jump _ =>
      rw [validateInlineFlat.eq_def, validateInline.eq_def]; simp only
      rw [hres]; simp only [hJ hm]
    | leaf | node1 _ | node2 _ _ | group _ _ _ =>
      rw [validateInlineFlat.eq_def, validateInline.eq_def]
  | _ + 1, plan, .ret vs', Γ, _, vs, _, inVD, _, inVE, _, hΓ, _, hmV, _, hwf => by
    dsimp only [denote]
    rw [denoteArgs_eq_some_resolveEnvArgs hΓ hmV vs' hwf ctDflt]; dsimp only
    cases plan <;> rw [validateInlineFlat.eq_def, validateInline.eq_def] <;> simp only
  | _ + 1, plan, .exit f args, Γ, _, vs, _, inVD, _, inVE, _, hΓ, _, hmV, _, hwf => by
    dsimp only [denote]
    rw [denoteArgs_eq_some_resolveEnvArgs hΓ hmV args hwf ctDflt]; dsimp only
    cases plan <;> rw [validateInlineFlat.eq_def, validateInline.eq_def] <;> simp only
  | _ + 1, plan, .hlt, _, _, _, _, _, _, _, _, _, _, _, _, _ => by
    dsimp only [denote]
    cases plan <;> rw [validateInlineFlat.eq_def, validateInline.eq_def] <;> simp only
  | _ + 1, plan, .group _ _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by
    dsimp only [denote]
    cases plan <;> rw [validateInlineFlat.eq_def, validateInline.eq_def] <;> simp only
termination_by structural _ plan _ => plan

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
      rewriteCTInlineFlat inLD inLE plan inVD inVE outVD outLD tf
  | plan, .let_ (ts := dts) ⟨code, args⟩ k, Γ, Δ, vs, ls, inVD, inLD, outVD, outLD, inVE, inLE,
      hΓ, hΔ, hmV, hmL, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denote]
    rw [denoteArgs_eq_some_resolveEnvArgs hΓ hmV args hwf.1 ctDflt]; dsimp only
    cases plan with
    | node1 pk =>
      rw [rewriteCTInline.eq_def, rewriteCTInlineFlat.eq_def]; simp only
      cases evalThreadLet? code (flattenArgs (resolveEnvArgs inVD inVE args ctDflt)) with
      | some out =>
        exact rewriteCTInlineFlat_eq pk k (ctxTypes_pushTup_rev out hΓ) hΔ
          (trieCtxMatch_insertTupEnv hmV out) hmL hwf.2
      | none =>
        cases toRealArgs? (flattenArgs (resolveEnvArgs inVD inVE args ctDflt)) with
        | none => rfl
        | some rargs =>
          dsimp only [toTFlat]
          have hfresh := trieCtxMatch_insertFreshWith
            (fun _ _ od => Arg.var (some od)) hmV dts outVD
          rw [mkFreshOptArg_eq_toOptArgTup] at hfresh
          exact congrArg (TFlat.let_ _)
            (rewriteCTInlineFlat_eq pk k (ctxTypes_pushTup_rev _ hΓ) hΔ hfresh hmL hwf.2)
    | leaf | jump _ | node2 _ _ | group _ _ _ =>
      rw [rewriteCTInline.eq_def, rewriteCTInlineFlat.eq_def]; simp only; rfl
  | plan, .load t a k, Γ, Δ, vs, ls, inVD, inLD, outVD, outLD, inVE, inLE,
      hΓ, hΔ, hmV, hmL, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denote]
    rw [denoteArg_eq_some_resolveEnvArg hΓ hmV a hwf.1 ctDflt]; dsimp only
    cases plan with
    | node1 pk =>
      rw [rewriteCTInline.eq_def, rewriteCTInlineFlat.eq_def]; simp only
      cases toRealArg? (flattenArg (resolveEnvArg inVD inVE a ctDflt)) with
      | none => rfl
      | some ra =>
        dsimp only [toTFlat]
        exact congrArg (TFlat.load t _)
          (rewriteCTInlineFlat_eq pk k (.cons hΓ) hΔ (hmV.cons t (Arg.var (some outVD))) hmL hwf.2)
    | leaf | jump _ | node2 _ _ | group _ _ _ =>
      rw [rewriteCTInline.eq_def, rewriteCTInlineFlat.eq_def]; simp only; rfl
  | plan, .store v a k, Γ, Δ, vs, ls, inVD, inLD, outVD, outLD, inVE, inLE,
      hΓ, hΔ, hmV, hmL, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denote]
    rw [denoteArg_eq_some_resolveEnvArg hΓ hmV v hwf.1.1 ctDflt,
      denoteArg_eq_some_resolveEnvArg hΓ hmV a hwf.1.2 ctDflt]; dsimp only
    cases plan with
    | node1 pk =>
      rw [rewriteCTInline.eq_def, rewriteCTInlineFlat.eq_def]; simp only
      cases toRealArg? (flattenArg (resolveEnvArg inVD inVE v ctDflt)) with
      | none => rfl
      | some rv =>
        cases toRealArg? (flattenArg (resolveEnvArg inVD inVE a ctDflt)) with
        | none => rfl
        | some ra =>
          dsimp only [toTFlat]
          exact congrArg (TFlat.store _ _) (rewriteCTInlineFlat_eq pk k hΓ hΔ hmV hmL hwf.2)
    | leaf | jump _ | node2 _ _ | group _ _ _ =>
      rw [rewriteCTInline.eq_def, rewriteCTInlineFlat.eq_def]; simp only; rfl
  | plan, .call f bs args k, Γ, Δ, vs, ls, inVD, inLD, outVD, outLD, inVE, inLE,
      hΓ, hΔ, hmV, hmL, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denote]
    rw [denoteArgs_eq_some_resolveEnvArgs hΓ hmV args hwf.1 ctDflt]; dsimp only
    cases plan with
    | node1 pk =>
      rw [rewriteCTInline.eq_def, rewriteCTInlineFlat.eq_def]; simp only
      cases toRealArgs? (flattenArgs (resolveEnvArgs inVD inVE args ctDflt)) with
      | none => rfl
      | some rargs =>
        dsimp only [toTFlat]
        have hfresh := trieCtxMatch_insertFreshWith
          (fun _ _ od => Arg.var (some od)) hmV bs outVD
        rw [mkFreshOptArg_eq_toOptArgTup] at hfresh
        exact congrArg (TFlat.call f bs _)
          (rewriteCTInlineFlat_eq pk k (ctxTypes_pushTup_rev _ hΓ) hΔ hfresh hmL hwf.2)
    | leaf | jump _ | node2 _ _ | group _ _ _ =>
      rw [rewriteCTInline.eq_def, rewriteCTInlineFlat.eq_def]; simp only; rfl
  | plan, .jnz c t e, Γ, Δ, vs, ls, inVD, inLD, outVD, outLD, inVE, inLE,
      hΓ, hΔ, hmV, hmL, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denote]
    rw [denoteArg_eq_some_resolveEnvArg hΓ hmV c hwf.1.1 ctDflt]; dsimp only
    cases plan with
    | node2 pt pe =>
      rw [rewriteCTInline.eq_def, rewriteCTInlineFlat.eq_def]; simp only
      cases flattenArg (resolveEnvArg inVD inVE c ctDflt) with
      | imm b =>
        cases b with
        | true => exact rewriteCTInlineFlat_eq pt t hΓ hΔ hmV hmL hwf.1.2
        | false => exact rewriteCTInlineFlat_eq pe e hΓ hΔ hmV hmL hwf.2
      | var v? =>
        cases v? with
        | none => rfl
        | some v =>
          dsimp only [toTFlat]
          rw [rewriteCTInlineFlat_eq pt t hΓ hΔ hmV hmL hwf.1.2,
            rewriteCTInlineFlat_eq pe e hΓ hΔ hmV hmL hwf.2]
    | leaf | jump _ | node1 _ | group _ _ _ =>
      rw [rewriteCTInline.eq_def, rewriteCTInlineFlat.eq_def]; simp only; rfl
  | plan, .jump (ts := ts) j args, Γ, Δ, vs, ls, inVD, inLD, outVD, outLD, inVE, inLE,
      hΓ, hΔ, hmV, hmL, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨w₁, w₂, hres, hlk, hm⟩ := TrieRelMatch.resolveLabel_rel hΔ hmL hwf.1
    dsimp only [denote]
    rw [hlk, denoteArgs_eq_some_resolveEnvArgs hΓ hmV args hwf.2 ctDflt]; dsimp only
    cases plan with
    | jump _ =>
      rw [rewriteCTInline.eq_def, rewriteCTInlineFlat.eq_def]; simp only
      rw [hres]; simp only
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
    | leaf | node1 _ | node2 _ _ | group _ _ _ =>
      rw [rewriteCTInline.eq_def, rewriteCTInlineFlat.eq_def]; simp only; rfl
  | plan, .ret vs', Γ, _, vs, _, inVD, _, _, _, inVE, _, hΓ, _, hmV, _, hwf => by
    dsimp only [denote]
    rw [denoteArgs_eq_some_resolveEnvArgs hΓ hmV vs' hwf ctDflt]; dsimp only
    cases plan with
    | leaf =>
      rw [rewriteCTInline.eq_def, rewriteCTInlineFlat.eq_def]; simp only
      cases toRealArgs? (flattenArgs (resolveEnvArgs inVD inVE vs' ctDflt)) <;> rfl
    | jump _ | node1 _ | node2 _ _ | group _ _ _ =>
      rw [rewriteCTInline.eq_def, rewriteCTInlineFlat.eq_def]; simp only; rfl
  | plan, .exit f args, Γ, _, vs, _, inVD, _, _, _, inVE, _, hΓ, _, hmV, _, hwf => by
    dsimp only [denote]
    rw [denoteArgs_eq_some_resolveEnvArgs hΓ hmV args hwf ctDflt]; dsimp only
    cases plan with
    | leaf =>
      rw [rewriteCTInline.eq_def, rewriteCTInlineFlat.eq_def]; simp only
      cases toRealArgs? (flattenArgs (resolveEnvArgs inVD inVE args ctDflt)) <;> rfl
    | jump _ | node1 _ | node2 _ _ | group _ _ _ =>
      rw [rewriteCTInline.eq_def, rewriteCTInlineFlat.eq_def]; simp only; rfl
  | plan, .hlt, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by
    dsimp only [denote]
    cases plan <;> rw [rewriteCTInline.eq_def, rewriteCTInlineFlat.eq_def] <;> simp only <;> rfl
  | plan, .group _ _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by
    dsimp only [denote]
    cases plan <;> rw [rewriteCTInline.eq_def, rewriteCTInlineFlat.eq_def] <;> simp only <;> rfl
termination_by structural plan _ => plan

/-! ## 3. `validateCTPlanFlat` Equivalence -/

private theorem validTargetsFlat_match {rs : List Ty} :
    (acts : List BlockAct) → (sig : List (List Ty)) →
    TRel (fun _ => ValidLFlatMatch (rs := rs)) (validTargetsFlat acts sig) (validTargets acts sig)
  | _, [] => .nil
  | [], _ :: sig => .cons ⟨rfl, fun _ => rfl⟩ (validTargetsFlat_match [] sig)
  | _ :: acts, _ :: sig =>
    .cons ⟨rfl, fun _ => rfl⟩ (validTargetsFlat_match acts sig)

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
        (j.target.canEmit a || (j.inline? a).isSome) := by
    intro _ _ _ a hm; rw [hm.1, hm.2 a]
  cases act with
  | keep _ bInl =>
    cases bInl with
    | false => exact hl
    | true =>
      refine ⟨hl.1, fun args => ?_⟩
      dsimp only [tryMakeValidInlineFlat, tryMakeInlineLabel]
      have hp := peelThreadHeadFlat_eq 4 false pb b (ctxTypes_pushTup_rev args hΓ) hΔ
        (trieCtxMatch_insertTupEnv hmV args) hb
      obtain ⟨Γ', vs', hΓ', hmV', hwf', hpeel⟩ := hp
      cases hres :
          peelThreadHeadFlat 4 false pb (inVD + ts.length) (insertTupEnv inVD inVE args) b
      rw [hres] at hmV' hwf' hpeel
      dsimp only at hmV' hwf' hpeel
      rw [hpeel]
      dsimp only
      rw [validateInlineFlat_eq
        (fun _ => ValidLFlatMatch (rs := rs)) _ hJ _ _ _ hΓ' hΔ hmV' hmL hwf']
      cases (validateInline _ _ _).isSome <;> rfl
  | splitBool _ _ _ _ inlT inlF =>
    by_cases hInl : (inlT || inlF) = true
    · dsimp only [tryMakeValidInlineFlat, tryMakeInlineLabel]
      simp only [hInl, ↓reduceIte]
      refine ⟨hl.1, fun args => ?_⟩
      dsimp only
      have hp := peelThreadHeadFlat_eq 4 false pb b (ctxTypes_pushTup_rev args hΓ) hΔ
        (trieCtxMatch_insertTupEnv hmV args) hb
      obtain ⟨Γ', vs', hΓ', hmV', hwf', hpeel⟩ := hp
      cases hres :
          peelThreadHeadFlat 4 false pb (inVD + ts.length) (insertTupEnv inVD inVE args) b
      rw [hres] at hmV' hwf' hpeel
      dsimp only at hmV' hwf' hpeel
      rw [hpeel]
      dsimp only
      rw [validateInlineFlat_eq
        (fun _ => ValidLFlatMatch (rs := rs)) _ hJ 8 _ _ hΓ' hΔ hmV' hmL hwf']
      cases (_ && (validateInline 8 _ _).isSome) <;> rfl
    · dsimp only [tryMakeValidInlineFlat, tryMakeInlineLabel]
      simp only [hInl, Bool.false_eq_true, ↓reduceIte]
      exact hl

private theorem attachValidInlinesFlat_match {rs : List Ty}
    {Γ : List Ty} {Δ : List (List Ty)}
    {vs : List ((t : Ty) × Arg (CTOptV UnitV) t)}
    {ls : List ((ts' : List Ty) × ValidL rs ts')}
    {inVD inLD : Nat}
    {inVE : Trie ((t : Ty) × Arg (CTOptV UnitV) t)}
    {inLE : Trie ((ts' : List Ty) × ValidLFlat rs ts')}
    (hΓ : CtxTypes Γ vs) (hΔ : CtxTypes Δ ls) (hmV : TrieCtxMatch inVD inVE vs)
    (hmL : TrieRelMatch (fun _ => ValidLFlatMatch (rs := rs)) inLD inLE ls) :
    (acts : List BlockAct) → (pbs : CTPlanB) → {sig : List (List Ty)} → (tb : TBlocks rs sig) →
    {lsF : Tup (ValidLFlat rs) sig} → {lsP : Tup (ValidL rs) sig} →
    TRel (fun _ => ValidLFlatMatch (rs := rs)) lsF lsP → tb.wfCheck Γ Δ = true →
    TRel (fun _ => ValidLFlatMatch (rs := rs))
      (attachValidInlinesFlat inVD inVE inLD inLE acts pbs tb lsF)
      (attachInlines acts pbs (denoteB (Arg (CTOptV UnitV)) (ValidL rs) tb vs ls) lsP)
  | _, _, [], .nil, (), (), .nil, _ => .nil
  | [], _, _ :: _, .cons _ bs, (_, _), (_, _), .cons hl hls, hwf => by
    dsimp only [TBlocks.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    exact .cons hl (attachValidInlinesFlat_match hΓ hΔ hmV hmL [] .nil bs hls hwf.2)
  | _ :: _, .nil, _ :: _, .cons _ bs, (_, _), (_, _), .cons hl hls, hwf => by
    dsimp only [TBlocks.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    exact .cons hl (attachValidInlinesFlat_match hΓ hΔ hmV hmL [] .nil bs hls hwf.2)
  | a :: acts', .cons pb pbs', _ :: _, .cons b bs, (_, _), (_, _), .cons hl hls, hwf => by
    dsimp only [TBlocks.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [attachValidInlinesFlat, denoteB, attachInlines]
    exact .cons (tryMakeValidInlineFlat_match hΓ hΔ hmV hmL a pb b hwf.1 hl)
      (attachValidInlinesFlat_match hΓ hΔ hmV hmL acts' pbs' bs hls hwf.2)

mutual
private theorem validateCTPlanFlat_eq {rs : List Ty} :
    (plan : CTPlan) → (tf : TFlat rs) → {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × Arg (CTOptV UnitV) t)} →
    {ls : List ((ts : List Ty) × ValidL rs ts)} →
    {inVD inLD : Nat} →
    {inVE : Trie ((t : Ty) × Arg (CTOptV UnitV) t)} →
    {inLE : Trie ((ts : List Ty) × ValidLFlat rs ts)} →
    CtxTypes Γ vs → CtxTypes Δ ls → TrieCtxMatch inVD inVE vs →
    TrieRelMatch (fun _ => ValidLFlatMatch (rs := rs)) inLD inLE ls → tf.wfCheck Γ Δ = true →
    validateCTPlanFlat plan inVD inVE inLD inLE tf =
      validateCTPlan plan (denote (Arg (CTOptV UnitV)) (ValidL rs) tf vs ls)
  | plan, .let_ (ts := dts) ⟨code, args⟩ k, Γ, Δ, vs, ls, inVD, inLD, inVE, inLE,
      hΓ, hΔ, hmV, hmL, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denote]
    rw [denoteArgs_eq_some_resolveEnvArgs hΓ hmV args hwf.1 ctDflt]; dsimp only
    cases plan with
    | node1 pk =>
      rw [validateCTPlanFlat.eq_def, validateCTPlan.eq_def]; simp only
      cases evalThreadLet? code (flattenArgs (resolveEnvArgs inVD inVE args ctDflt)) with
      | some out =>
        exact validateCTPlanFlat_eq pk k (ctxTypes_pushTup_rev out hΓ) hΔ
          (trieCtxMatch_insertTupEnv hmV out) hmL hwf.2
      | none =>
        exact validateCTPlanFlat_eq pk k (ctxTypes_pushTup_rev _ hΓ) hΔ
          (trieCtxMatch_insertTupEnv hmV _) hmL hwf.2
    | leaf | jump _ | node2 _ _ | group _ _ _ =>
      rw [validateCTPlanFlat.eq_def, validateCTPlan.eq_def]
  | plan, .load t a k, Γ, Δ, vs, ls, inVD, inLD, inVE, inLE,
      hΓ, hΔ, hmV, hmL, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denote]
    rw [denoteArg_eq_some_resolveEnvArg hΓ hmV a hwf.1 ctDflt]; dsimp only
    cases plan with
    | node1 pk =>
      rw [validateCTPlanFlat.eq_def, validateCTPlan.eq_def]; simp only
      exact validateCTPlanFlat_eq pk k (.cons hΓ) hΔ (hmV.cons t (Arg.var (some ()))) hmL hwf.2
    | leaf | jump _ | node2 _ _ | group _ _ _ =>
      rw [validateCTPlanFlat.eq_def, validateCTPlan.eq_def]
  | plan, .store v a k, Γ, Δ, vs, ls, inVD, inLD, inVE, inLE,
      hΓ, hΔ, hmV, hmL, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denote]
    rw [denoteArg_eq_some_resolveEnvArg hΓ hmV v hwf.1.1 ctDflt,
      denoteArg_eq_some_resolveEnvArg hΓ hmV a hwf.1.2 ctDflt]; dsimp only
    cases plan with
    | node1 pk =>
      rw [validateCTPlanFlat.eq_def, validateCTPlan.eq_def]; simp only
      exact validateCTPlanFlat_eq pk k hΓ hΔ hmV hmL hwf.2
    | leaf | jump _ | node2 _ _ | group _ _ _ =>
      rw [validateCTPlanFlat.eq_def, validateCTPlan.eq_def]
  | plan, .call f bs args k, Γ, Δ, vs, ls, inVD, inLD, inVE, inLE,
      hΓ, hΔ, hmV, hmL, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denote]
    rw [denoteArgs_eq_some_resolveEnvArgs hΓ hmV args hwf.1 ctDflt]; dsimp only
    cases plan with
    | node1 pk =>
      rw [validateCTPlanFlat.eq_def, validateCTPlan.eq_def]; simp only
      exact validateCTPlanFlat_eq pk k (ctxTypes_pushTup_rev _ hΓ) hΔ
        (trieCtxMatch_insertTupEnv hmV _) hmL hwf.2
    | leaf | jump _ | node2 _ _ | group _ _ _ =>
      rw [validateCTPlanFlat.eq_def, validateCTPlan.eq_def]
  | plan, .jnz c t e, Γ, Δ, vs, ls, inVD, inLD, inVE, inLE,
      hΓ, hΔ, hmV, hmL, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denote]
    rw [denoteArg_eq_some_resolveEnvArg hΓ hmV c hwf.1.1 ctDflt]; dsimp only
    cases plan with
    | node2 pt pe =>
      rw [validateCTPlanFlat.eq_def, validateCTPlan.eq_def]; simp only
      cases flattenArg (resolveEnvArg inVD inVE c ctDflt) with
      | imm b =>
        cases b with
        | true => exact validateCTPlanFlat_eq pt t hΓ hΔ hmV hmL hwf.1.2
        | false => exact validateCTPlanFlat_eq pe e hΓ hΔ hmV hmL hwf.2
      | var _ =>
        dsimp only
        rw [validateCTPlanFlat_eq pt t hΓ hΔ hmV hmL hwf.1.2,
          validateCTPlanFlat_eq pe e hΓ hΔ hmV hmL hwf.2]
    | leaf | jump _ | node1 _ | group _ _ _ =>
      rw [validateCTPlanFlat.eq_def, validateCTPlan.eq_def]
  | plan, .jump (ts := ts) j args, Γ, Δ, vs, ls, inVD, inLD, inVE, inLE,
      hΓ, hΔ, hmV, hmL, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨w₁, w₂, hres, hlk, hm⟩ := TrieRelMatch.resolveLabel_rel hΔ hmL hwf.1
    dsimp only [denote]
    rw [hlk, denoteArgs_eq_some_resolveEnvArgs hΓ hmV args hwf.2 ctDflt]; dsimp only
    cases plan with
    | jump tryInl =>
      rw [validateCTPlanFlat.eq_def, validateCTPlan.eq_def]; simp only
      rw [hres]; simp only [hm.1]
      cases tryInl with
      | false => rfl
      | true =>
        have hi := hm.2 (flattenArgs (resolveEnvArgs inVD inVE args ctDflt))
        rw [hi]
        cases w₂.inline? (flattenArgs (resolveEnvArgs inVD inVE args ctDflt)) <;> rfl
    | leaf | node1 _ | node2 _ _ | group _ _ _ =>
      rw [validateCTPlanFlat.eq_def, validateCTPlan.eq_def]
  | plan, .ret vs', Γ, _, vs, _, inVD, _, inVE, _, hΓ, _, hmV, _, hwf => by
    dsimp only [denote]
    rw [denoteArgs_eq_some_resolveEnvArgs hΓ hmV vs' hwf ctDflt]; dsimp only
    cases plan <;> rw [validateCTPlanFlat.eq_def, validateCTPlan.eq_def] <;> simp only
  | plan, .exit f args, Γ, _, vs, _, inVD, _, inVE, _, hΓ, _, hmV, _, hwf => by
    dsimp only [denote]
    rw [denoteArgs_eq_some_resolveEnvArgs hΓ hmV args hwf ctDflt]; dsimp only
    cases plan <;> rw [validateCTPlanFlat.eq_def, validateCTPlan.eq_def] <;> simp only
  | plan, .hlt, _, _, _, _, _, _, _, _, _, _, _, _, _ => by
    dsimp only [denote]
    cases plan <;> rw [validateCTPlanFlat.eq_def, validateCTPlan.eq_def] <;> simp only
  | plan, .group (sig := sig) bodies k, Γ, Δ, vs, ls, inVD, inLD, inVE, inLE,
      hΓ, hΔ, hmV, hmL, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denote]
    cases plan with
    | group acts pbs pk =>
      rw [validateCTPlanFlat.eq_def, validateCTPlan.eq_def]; simp only
      have hno := validTargetsFlat_match (rs := rs) acts sig
      have hmNo := TrieRelMatch.pushTup hno hmL
      have hbody := attachValidInlinesFlat_match hΓ (ctxTypes_pushTup_rev _ hΔ) hmV hmNo
        acts pbs bodies hno hwf.1
      have hmBody := TrieRelMatch.pushTup hbody hmL
      have hΔ' := ctxTypes_pushTup_rev
        (attachInlines acts pbs (denoteB (Arg (CTOptV UnitV)) (ValidL rs) bodies vs
          (pushTup (validTargets acts sig) ls)) (validTargets acts sig)) hΔ
      have hb := validateCTBlocksFlat_eq acts pbs bodies hΓ hΔ' hmV hmBody hwf.1
      have hk := validateCTPlanFlat_eq pk k hΓ hΔ' hmV hmBody hwf.2
      rw [hb, hk]
    | leaf | jump _ | node1 _ | node2 _ _ =>
      rw [validateCTPlanFlat.eq_def, validateCTPlan.eq_def]
termination_by structural plan _ => plan

private theorem validateCTBlocksFlat_eq {rs : List Ty} :
    (acts : List BlockAct) → (pbs : CTPlanB) → {sig : List (List Ty)} → (tb : TBlocks rs sig) →
    {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × Arg (CTOptV UnitV) t)} →
    {ls : List ((ts : List Ty) × ValidL rs ts)} →
    {inVD inLD : Nat} →
    {inVE : Trie ((t : Ty) × Arg (CTOptV UnitV) t)} →
    {inLE : Trie ((ts : List Ty) × ValidLFlat rs ts)} →
    CtxTypes Γ vs → CtxTypes Δ ls → TrieCtxMatch inVD inVE vs →
    TrieRelMatch (fun _ => ValidLFlatMatch (rs := rs)) inLD inLE ls → tb.wfCheck Γ Δ = true →
    validateCTBlocksFlat acts pbs inVD inVE inLD inLE tb =
      validateCTBlocks acts pbs (denoteB (Arg (CTOptV UnitV)) (ValidL rs) tb vs ls)
  | acts, .nil, [], .nil, _, _, _, _, _, _, _, _, _, _, _, _, _ => by
    rw [validateCTBlocksFlat.eq_def, denoteB.eq_def, validateCTBlocks.eq_def]; simp only
    cases acts <;> rfl
  | _, .cons _ _, [], .nil, _, _, _, _, _, _, _, _, _, _, _, _, _ => by
    rw [validateCTBlocksFlat.eq_def, denoteB.eq_def, validateCTBlocks.eq_def]; simp only
  | acts, .nil, _ :: _, .cons _ _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by
    rw [validateCTBlocksFlat.eq_def, denoteB.eq_def, validateCTBlocks.eq_def]; simp only
  | [], .cons _ _, _ :: _, .cons _ _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by
    rw [validateCTBlocksFlat.eq_def, denoteB.eq_def, validateCTBlocks.eq_def]; simp only
  | a :: acts', .cons pb pbs', ts :: _, .cons b bs, Γ, Δ, vs, ls, inVD, inLD, inVE, inLE,
      hΓ, hΔ, hmV, hmL, hwf => by
    dsimp only [TBlocks.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    rw [validateCTBlocksFlat.eq_def, denoteB.eq_def, validateCTBlocks.eq_def]; simp only
    have hrest := validateCTBlocksFlat_eq acts' pbs' bs hΓ hΔ hmV hmL hwf.2
    cases a with
    | keep keepB _ =>
      cases keepB with
      | true =>
        simp only
        rw [validateCTPlanFlat_eq pb b (ctxTypes_pushTup_rev _ hΓ) hΔ
          (trieCtxMatch_insertTupEnv hmV _) hmL hwf.1, hrest]
      | false => simp only; rw [hrest]
    | splitBool p keepT keepF _ _ _ =>
      simp only
      cases splitMember? p ts with
      | none =>
        simp only
        rw [validateCTPlanFlat_eq pb b (ctxTypes_pushTup_rev _ hΓ) hΔ
          (trieCtxMatch_insertTupEnv hmV _) hmL hwf.1, hrest]
      | some m =>
        simp only
        rw [validateCTPlanFlat_eq pb b (ctxTypes_pushTup_rev _ hΓ) hΔ
          (trieCtxMatch_insertTupEnv hmV _) hmL hwf.1,
          validateCTPlanFlat_eq pb b (ctxTypes_pushTup_rev _ hΓ) hΔ
          (trieCtxMatch_insertTupEnv hmV _) hmL hwf.1, hrest]
termination_by structural _ pbs => pbs
end

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
  funext ()
  rw [htgt]
  cases lP.target with
  | keep _ | dead => rfl
  | split m' lT? lF? _ =>
    cases lT? <;> cases lF? <;> rfl

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
        (j.target.canEmit a || (j.inline? a).isSome) := by
    intro _ jl j a hm; rw [hm.1, orel_isSome (hm.2 0 0 a)]
  cases act with
  | keep _ bInl =>
    cases bInl with
    | false => exact hl
    | true =>
      refine ⟨hl.1, fun ovd old args => ?_⟩
      dsimp only [tryMakeInlineLabelFlat, tryMakeInlineLabel]
      have hp := peelThreadHeadFlat_eq 4 false pb b (ctxTypes_pushTup_rev args hΓ) hΔ
        (trieCtxMatch_insertTupEnv hmV args) hb
      obtain ⟨Γ', vs', hΓ', hmV', hwf', hpeel⟩ := hp
      cases hres :
          peelThreadHeadFlat 4 false pb (inVD + ts.length) (insertTupEnv inVD inVE args) b
      rw [hres] at hmV' hwf' hpeel
      dsimp only at hmV' hwf' hpeel
      rw [hpeel]
      dsimp only
      rw [validateInlineFlat_eq
        (fun _ => CTLabelFlatMatch (rs := rs)) _ hJ _ _ _ hΓ' hΔ hmV' hmL hwf']
      cases (validateInline _ _ _).isSome <;>
        simp only [Bool.false_eq_true, ↓reduceIte, ORel]
      exact (rewriteCTInlineFlat_eq _ _ hΓ' hΔ hmV' hmL hwf').symm
  | splitBool _ _ _ _ inlT inlF =>
    by_cases hInl : (inlT || inlF) = true
    · dsimp only [tryMakeInlineLabelFlat, tryMakeInlineLabel]
      simp only [hInl, ↓reduceIte]
      refine ⟨hl.1, fun ovd old args => ?_⟩
      dsimp only
      have hp := peelThreadHeadFlat_eq 4 false pb b (ctxTypes_pushTup_rev args hΓ) hΔ
        (trieCtxMatch_insertTupEnv hmV args) hb
      obtain ⟨Γ', vs', hΓ', hmV', hwf', hpeel⟩ := hp
      cases hres :
          peelThreadHeadFlat 4 false pb (inVD + ts.length) (insertTupEnv inVD inVE args) b
      rw [hres] at hmV' hwf' hpeel
      dsimp only at hmV' hwf' hpeel
      rw [hpeel]
      dsimp only
      rw [validateInlineFlat_eq
        (fun _ => CTLabelFlatMatch (rs := rs)) _ hJ 8 _ _ hΓ' hΔ hmV' hmL hwf']
      cases (_ && (validateInline 8 _ _).isSome) <;>
        simp only [Bool.false_eq_true, ↓reduceIte, ORel]
      exact (rewriteCTInlineFlat_eq _ _ hΓ' hΔ hmV' hmL hwf').symm
    · dsimp only [tryMakeInlineLabelFlat, tryMakeInlineLabel]
      simp only [hInl, Bool.false_eq_true, ↓reduceIte]
      exact hl

private theorem attachInlinesFlat_match {rs : List Ty}
    {Γ : List Ty} {Δ : List (List Ty)}
    {vs : List ((t : Ty) × Arg (CTOptV K) t)}
    {ls : List ((ts' : List Ty) × CTLabel K KL rs ts')}
    {inVD inLD : Nat}
    {inVE : Trie ((t : Ty) × Arg (CTOptV K) t)}
    {inLE : Trie ((ts' : List Ty) × CTLabelFlat rs ts')}
    (hΓ : CtxTypes Γ vs) (hΔ : CtxTypes Δ ls) (hmV : TrieCtxMatch inVD inVE vs)
    (hmL : TrieRelMatch (fun _ => CTLabelFlatMatch (rs := rs)) inLD inLE ls) :
    (acts : List BlockAct) → (pbs : CTPlanB) → {sig : List (List Ty)} → (tb : TBlocks rs sig) →
    {lsF : Tup (CTLabelFlat rs) sig} → {lsP : Tup (CTLabel K KL rs) sig} →
    TRel (fun _ => CTLabelFlatMatch (rs := rs)) lsF lsP → tb.wfCheck Γ Δ = true →
    TRel (fun _ => CTLabelFlatMatch (rs := rs))
      (attachInlinesFlat inVD inVE inLD inLE acts pbs tb lsF)
      (attachInlines acts pbs (denoteB (Arg (CTOptV K)) (CTLabel K KL rs) tb vs ls) lsP)
  | _, _, [], .nil, (), (), .nil, _ => .nil
  | [], _, _ :: _, .cons _ bs, (_, _), (_, _), .cons hl hls, hwf => by
    dsimp only [TBlocks.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    exact .cons hl (attachInlinesFlat_match hΓ hΔ hmV hmL [] .nil bs hls hwf.2)
  | _ :: _, .nil, _ :: _, .cons _ bs, (_, _), (_, _), .cons hl hls, hwf => by
    dsimp only [TBlocks.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    exact .cons hl (attachInlinesFlat_match hΓ hΔ hmV hmL [] .nil bs hls hwf.2)
  | a :: acts', .cons pb pbs', _ :: _, .cons b bs, (_, _), (_, _), .cons hl hls, hwf => by
    dsimp only [TBlocks.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [attachInlinesFlat, denoteB, attachInlines]
    exact .cons (tryMakeInlineLabelFlat_match hΓ hΔ hmV hmL a pb b hwf.1 hl)
      (attachInlinesFlat_match hΓ hΔ hmV hmL acts' pbs' bs hls hwf.2)

mutual
private theorem rewriteCTFlat_eq {rs : List Ty} :
    (plan : CTPlan) → (tf : TFlat rs) → {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × Arg (CTOptV K) t)} →
    {ls : List ((ts : List Ty) × CTLabel K KL rs ts)} →
    {inVD inLD outVD outLD : Nat} →
    {inVE : Trie ((t : Ty) × Arg (CTOptV K) t)} →
    {inLE : Trie ((ts : List Ty) × CTLabelFlat rs ts)} →
    CtxTypes Γ vs → CtxTypes Δ ls → TrieCtxMatch inVD inVE vs →
    TrieRelMatch (fun _ => CTLabelFlatMatch (rs := rs)) inLD inLE ls → tf.wfCheck Γ Δ = true →
    toTFlat (rewriteCTAux plan (denote (Arg (CTOptV K)) (CTLabel K KL rs) tf vs ls))
        outVD outLD =
      rewriteCTFlat plan inVD inVE inLD inLE outVD outLD tf
  | plan, .let_ (ts := dts) ⟨code, args⟩ k, Γ, Δ, vs, ls, inVD, inLD, outVD, outLD, inVE, inLE,
      hΓ, hΔ, hmV, hmL, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denote]
    rw [denoteArgs_eq_some_resolveEnvArgs hΓ hmV args hwf.1 ctDflt]; dsimp only
    cases plan with
    | node1 pk =>
      rw [rewriteCTAux.eq_def, rewriteCTFlat.eq_def]; simp only
      cases evalThreadLet? code (flattenArgs (resolveEnvArgs inVD inVE args ctDflt)) with
      | some out =>
        exact rewriteCTFlat_eq pk k (ctxTypes_pushTup_rev out hΓ) hΔ
          (trieCtxMatch_insertTupEnv hmV out) hmL hwf.2
      | none =>
        cases toRealArgs? (flattenArgs (resolveEnvArgs inVD inVE args ctDflt)) with
        | none => rfl
        | some rargs =>
          dsimp only [toTFlat]
          have hfresh := trieCtxMatch_insertFreshWith
            (fun _ _ od => Arg.var (some od)) hmV dts outVD
          rw [mkFreshOptArg_eq_toOptArgTup] at hfresh
          exact congrArg (TFlat.let_ _)
            (rewriteCTFlat_eq pk k (ctxTypes_pushTup_rev _ hΓ) hΔ hfresh hmL hwf.2)
    | leaf | jump _ | node2 _ _ | group _ _ _ =>
      rw [rewriteCTAux.eq_def, rewriteCTFlat.eq_def]; simp only; rfl
  | plan, .load t a k, Γ, Δ, vs, ls, inVD, inLD, outVD, outLD, inVE, inLE,
      hΓ, hΔ, hmV, hmL, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denote]
    rw [denoteArg_eq_some_resolveEnvArg hΓ hmV a hwf.1 ctDflt]; dsimp only
    cases plan with
    | node1 pk =>
      rw [rewriteCTAux.eq_def, rewriteCTFlat.eq_def]; simp only
      cases toRealArg? (flattenArg (resolveEnvArg inVD inVE a ctDflt)) with
      | none => rfl
      | some ra =>
        dsimp only [toTFlat]
        exact congrArg (TFlat.load t _)
          (rewriteCTFlat_eq pk k (.cons hΓ) hΔ (hmV.cons t (Arg.var (some outVD))) hmL hwf.2)
    | leaf | jump _ | node2 _ _ | group _ _ _ =>
      rw [rewriteCTAux.eq_def, rewriteCTFlat.eq_def]; simp only; rfl
  | plan, .store v a k, Γ, Δ, vs, ls, inVD, inLD, outVD, outLD, inVE, inLE,
      hΓ, hΔ, hmV, hmL, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denote]
    rw [denoteArg_eq_some_resolveEnvArg hΓ hmV v hwf.1.1 ctDflt,
      denoteArg_eq_some_resolveEnvArg hΓ hmV a hwf.1.2 ctDflt]; dsimp only
    cases plan with
    | node1 pk =>
      rw [rewriteCTAux.eq_def, rewriteCTFlat.eq_def]; simp only
      cases toRealArg? (flattenArg (resolveEnvArg inVD inVE v ctDflt)) with
      | none => rfl
      | some rv =>
        cases toRealArg? (flattenArg (resolveEnvArg inVD inVE a ctDflt)) with
        | none => rfl
        | some ra =>
          dsimp only [toTFlat]
          exact congrArg (TFlat.store _ _) (rewriteCTFlat_eq pk k hΓ hΔ hmV hmL hwf.2)
    | leaf | jump _ | node2 _ _ | group _ _ _ =>
      rw [rewriteCTAux.eq_def, rewriteCTFlat.eq_def]; simp only; rfl
  | plan, .call f bs args k, Γ, Δ, vs, ls, inVD, inLD, outVD, outLD, inVE, inLE,
      hΓ, hΔ, hmV, hmL, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denote]
    rw [denoteArgs_eq_some_resolveEnvArgs hΓ hmV args hwf.1 ctDflt]; dsimp only
    cases plan with
    | node1 pk =>
      rw [rewriteCTAux.eq_def, rewriteCTFlat.eq_def]; simp only
      cases toRealArgs? (flattenArgs (resolveEnvArgs inVD inVE args ctDflt)) with
      | none => rfl
      | some rargs =>
        dsimp only [toTFlat]
        have hfresh := trieCtxMatch_insertFreshWith
          (fun _ _ od => Arg.var (some od)) hmV bs outVD
        rw [mkFreshOptArg_eq_toOptArgTup] at hfresh
        exact congrArg (TFlat.call f bs _)
          (rewriteCTFlat_eq pk k (ctxTypes_pushTup_rev _ hΓ) hΔ hfresh hmL hwf.2)
    | leaf | jump _ | node2 _ _ | group _ _ _ =>
      rw [rewriteCTAux.eq_def, rewriteCTFlat.eq_def]; simp only; rfl
  | plan, .jnz c t e, Γ, Δ, vs, ls, inVD, inLD, outVD, outLD, inVE, inLE,
      hΓ, hΔ, hmV, hmL, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denote]
    rw [denoteArg_eq_some_resolveEnvArg hΓ hmV c hwf.1.1 ctDflt]; dsimp only
    cases plan with
    | node2 pt pe =>
      rw [rewriteCTAux.eq_def, rewriteCTFlat.eq_def]; simp only
      cases flattenArg (resolveEnvArg inVD inVE c ctDflt) with
      | imm b =>
        cases b with
        | true => exact rewriteCTFlat_eq pt t hΓ hΔ hmV hmL hwf.1.2
        | false => exact rewriteCTFlat_eq pe e hΓ hΔ hmV hmL hwf.2
      | var v? =>
        cases v? with
        | none => rfl
        | some v =>
          dsimp only [toTFlat]
          rw [rewriteCTFlat_eq pt t hΓ hΔ hmV hmL hwf.1.2,
            rewriteCTFlat_eq pe e hΓ hΔ hmV hmL hwf.2]
    | leaf | jump _ | node1 _ | group _ _ _ =>
      rw [rewriteCTAux.eq_def, rewriteCTFlat.eq_def]; simp only; rfl
  | plan, .jump (ts := ts) j args, Γ, Δ, vs, ls, inVD, inLD, outVD, outLD, inVE, inLE,
      hΓ, hΔ, hmV, hmL, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨w₁, w₂, hres, hlk, hm⟩ := TrieRelMatch.resolveLabel_rel hΔ hmL hwf.1
    dsimp only [denote]
    rw [hlk, denoteArgs_eq_some_resolveEnvArgs hΓ hmV args hwf.2 ctDflt]; dsimp only
    cases plan with
    | jump tryInl =>
      rw [rewriteCTAux.eq_def, rewriteCTFlat.eq_def]; simp only
      rw [hres]; simp only
      exact CTLabelFlat_emitJump_eq tryInl hm outVD outLD _
    | leaf | node1 _ | node2 _ _ | group _ _ _ =>
      rw [rewriteCTAux.eq_def, rewriteCTFlat.eq_def]; simp only; rfl
  | plan, .ret vs', Γ, _, vs, _, inVD, _, _, _, inVE, _, hΓ, _, hmV, _, hwf => by
    dsimp only [denote]
    rw [denoteArgs_eq_some_resolveEnvArgs hΓ hmV vs' hwf ctDflt]; dsimp only
    cases plan with
    | leaf =>
      rw [rewriteCTAux.eq_def, rewriteCTFlat.eq_def]; simp only
      cases toRealArgs? (flattenArgs (resolveEnvArgs inVD inVE vs' ctDflt)) <;> rfl
    | jump _ | node1 _ | node2 _ _ | group _ _ _ =>
      rw [rewriteCTAux.eq_def, rewriteCTFlat.eq_def]; simp only; rfl
  | plan, .exit f args, Γ, _, vs, _, inVD, _, _, _, inVE, _, hΓ, _, hmV, _, hwf => by
    dsimp only [denote]
    rw [denoteArgs_eq_some_resolveEnvArgs hΓ hmV args hwf ctDflt]; dsimp only
    cases plan with
    | leaf =>
      rw [rewriteCTAux.eq_def, rewriteCTFlat.eq_def]; simp only
      cases toRealArgs? (flattenArgs (resolveEnvArgs inVD inVE args ctDflt)) <;> rfl
    | jump _ | node1 _ | node2 _ _ | group _ _ _ =>
      rw [rewriteCTAux.eq_def, rewriteCTFlat.eq_def]; simp only; rfl
  | plan, .hlt, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by
    dsimp only [denote]
    cases plan <;> rw [rewriteCTAux.eq_def, rewriteCTFlat.eq_def] <;> simp only <;> rfl
  | plan, .group (sig := sig) bodies k, Γ, Δ, vs, ls,
      inVD, inLD, outVD, outLD, inVE, inLE, hΓ, hΔ, hmV, hmL, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denote]
    cases plan with
    | group acts pbs pk =>
      rw [rewriteCTAux.eq_def, rewriteCTFlat.eq_def]; simp only [toTFlat]
      have hno := buildTargetsFlat_match (rs := rs) acts sig (Tup.levels (threadSig acts sig) outLD)
      have hmNo := TrieRelMatch.pushTup hno hmL
      have hbody := attachInlinesFlat_match hΓ (ctxTypes_pushTup_rev _ hΔ) hmV hmNo
        acts pbs bodies hno hwf.1
      have hmBody := TrieRelMatch.pushTup hbody hmL
      have hΔ' := ctxTypes_pushTup_rev
        (attachInlines acts pbs (denoteB (Arg (CTOptV K)) (CTLabel K KL rs) bodies vs
          (pushTup (buildTargets acts sig (Tup.levels (threadSig acts sig) outLD)) ls))
          (buildTargets acts sig (Tup.levels (threadSig acts sig) outLD))) hΔ
      have hb := rewriteCTBlocksFlat_eq acts pbs bodies hΓ hΔ' hmV hmBody hno hwf.1
        (outVD := outVD) (outLD := outLD + (threadSig acts sig).length)
      have hk := rewriteCTFlat_eq pk k hΓ hΔ' hmV hmBody hwf.2
        (outVD := outVD) (outLD := outLD + (threadSig acts sig).length)
      rw [hb, hk]
    | leaf | jump _ | node1 _ | node2 _ _ =>
      rw [rewriteCTAux.eq_def, rewriteCTFlat.eq_def]; simp only; rfl
termination_by structural plan _ => plan

private theorem rewriteCTBlocksFlat_eq {rs : List Ty} :
    (acts : List BlockAct) → (pbs : CTPlanB) → {sig : List (List Ty)} → (tb : TBlocks rs sig) →
    {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × Arg (CTOptV K) t)} →
    {ls : List ((ts : List Ty) × CTLabel K KL rs ts)} →
    {inVD inLD outVD outLD : Nat} →
    {inVE : Trie ((t : Ty) × Arg (CTOptV K) t)} →
    {inLE : Trie ((ts : List Ty) × CTLabelFlat rs ts)} →
    {lsF : Tup (CTLabelFlat rs) sig} → {lsP : Tup (CTLabel K KL rs) sig} →
    CtxTypes Γ vs → CtxTypes Δ ls → TrieCtxMatch inVD inVE vs →
    TrieRelMatch (fun _ => CTLabelFlatMatch (rs := rs)) inLD inLE ls →
    TRel (fun _ => CTLabelFlatMatch (rs := rs)) lsF lsP → tb.wfCheck Γ Δ = true →
    toTBlocks (rewriteCTBlocks acts pbs (denoteB (Arg (CTOptV K)) (CTLabel K KL rs) tb vs ls) lsP)
        outVD outLD =
      rewriteCTBlocksFlat acts pbs inVD inVE inLD inLE outVD outLD tb lsF
  | acts, _, [], .nil, _, _, _, _, _, _, outVD, outLD, _, _, (), (), _, _, _, _, _, _ => by
    rw [rewriteCTBlocksFlat.eq_def, denoteB.eq_def, rewriteCTBlocks.eq_def]; simp only
    exact toTBlocks_mkHltBlocks (threadSig acts []) outVD outLD
  | [], _, _ :: sig', .cons _ _, _, _, _, _, _, _, outVD, outLD, _, _, _, _,
      _, _, _, _, _, _ => by
    rw [rewriteCTBlocksFlat.eq_def, denoteB.eq_def, rewriteCTBlocks.eq_def]; simp only
    exact toTBlocks_mkHltBlocks _ outVD outLD
  | a :: acts', .nil, _ :: sig', .cons _ _, _, _, _, _, _, _, outVD, outLD, _, _, _, _,
      _, _, _, _, _, _ => by
    rw [rewriteCTBlocksFlat.eq_def, denoteB.eq_def, rewriteCTBlocks.eq_def]; simp only
    exact toTBlocks_mkHltBlocks _ outVD outLD
  | a :: acts', .cons pb pbs', ts :: _, .cons b bs, Γ, Δ, vs, ls,
      inVD, inLD, outVD, outLD, inVE, inLE, (lF, lsF'), (lP, lsP'),
      hΓ, hΔ, hmV, hmL, hrel, hwf => by
    dsimp only [TBlocks.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    cases hrel with
    | cons hl hls =>
      rw [rewriteCTBlocksFlat.eq_def, denoteB.eq_def, rewriteCTBlocks.eq_def]; simp only
      rw [toTBlocks_append]
      have htl := rewriteCTBlocksFlat_eq acts' pbs' bs hΓ hΔ hmV hmL hls hwf.2
        (outVD := outVD) (outLD := outLD)
      refine congr (congrArg tblocksAppend ?_) htl
      cases a with
      | keep keepB _ =>
        cases keepB with
        | true =>
          dsimp only [actSig, toTBlocks]
          have hfresh := trieCtxMatch_insertFreshWith
            (fun _ _ od => Arg.var (some od)) hmV ts outVD
          rw [mkFreshOptArg_eq_toOptArgTup] at hfresh
          exact congrArg (TBlocks.cons · .nil)
            (rewriteCTFlat_eq pb b (ctxTypes_pushTup_rev _ hΓ) hΔ hfresh hmL hwf.1)
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
        have hid := rewriteCTFlat_eq pb b (ctxTypes_pushTup_rev _ hΓ) hΔ hfresh hmL hwf.1
          (outVD := outVD + ts.length) (outLD := outLD)
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
          exact rewriteCTFlat_eq pb b (ctxTypes_pushTup_rev _ hΓ) hΔ
            (trieCtxMatch_insertTupEnv hmV _) hmL hwf.1
        rw [hid, hsp]
termination_by structural _ pbs => pbs
end

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
  have hval : validateCTPlanFlat plan as.length
        (initEnv (fun _ _ => .var (some ())) as) 0 .empty tf =
      validateCTPlan plan (denote (Arg (CTOptV UnitV)) (ValidL rs) tf
        (pushTup (toOptArgTup (Tup.units as)) []) []) :=
    validateCTPlanFlat_eq plan tf (ctxTypes_pushTup_rev (toOptArgTup (Tup.units as)) .nil) .nil
      hmUnit (TrieRelMatch.empty (fun _ => ValidLFlatMatch (rs := rs))) hwf
  rw [hval]
  by_cases hval' : validateCTPlan plan (denote (Arg (CTOptV UnitV)) (ValidL rs) tf
      (pushTup (toOptArgTup (Tup.units as)) []) []) = true
  · simp only [hval', ↓reduceIte]
    have hmK := trieCtxMatch_initEnv
      (fun {t} (x : K t) _ => (Arg.var (some x) : Arg (CTOptV K) t)) as
    rw [tupFreshSomeOpt_eq] at hmK
    have hrw := rewriteCTFlat_eq plan tf
      (ctxTypes_pushTup_rev (toOptArgTup (Tup.levels as 0)) .nil) .nil hmK
      (TrieRelMatch.empty (fun _ => CTLabelFlatMatch (rs := rs))) hwf
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

/-- `denoteFunc (condThreadPassFlat as tf) = Func.condThreadPass (denoteFunc tf)` under
`wfCheck = true`. -/
theorem denoteFunc_condThreadPassFlat {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    denoteFunc (as := as) (condThreadPassFlat as tf) =
      Func.condThreadPass (denoteFunc (as := as) tf) := by
  rw [condThreadPassFlat_eq tf hwf]
  exact Func.renorm_eq_self (Func.condThreadPass_wf (Func.wf_of_denote tf rfl))

/-- `condThreadPassFlat` preserves `wfCheck`. -/
theorem condThreadPassFlat_wfCheck {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    (condThreadPassFlat as tf).wfCheck (pushTypes as []) [] = true := by
  rw [condThreadPassFlat_eq tf hwf]
  exact PassFlatKit.reifyFunc_wfCheck (Func.condThreadPass_wf (Func.wf_of_denote tf rfl))

/-- `(condThreadPassFlatFn f).toFn = ⟨f.name, f.as, f.rs, Func.condThreadPass f.toFn.body⟩`
under `wfCheck = true`. -/
theorem condThreadPassFlatFn_toFn (f : TFlatFn) (hwf : f.wfCheck = true) :
    (condThreadPassFlatFn f).toFn = ⟨f.name, f.as, f.rs, Func.condThreadPass f.toFn.body⟩ := by
  dsimp only [condThreadPassFlatFn, TFlatFn.toFn]
  rw [denoteFunc_condThreadPassFlat f.body hwf]

/-- `condThreadPassFlatFn` preserves `TFlatFn.wfCheck`. -/
theorem condThreadPassFlatFn_wfCheck (f : TFlatFn) (hwf : f.wfCheck = true) :
    (condThreadPassFlatFn f).wfCheck = true :=
  condThreadPassFlat_wfCheck f.body hwf

end OptFlatBranch
end LeanQbe.T
