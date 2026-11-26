module

public import LeanQbe.T.OptFlatBranch
import LeanQbe.T.FlatDirectLemmas
import LeanQbe.T.PassFlatKit
import LeanQbe.T.TailDupLemmas

/-!
# Tail-Duplication Equivalence Proofs (`OptFlatBranchLemmas0`)

Proves exact `=` correspondence (`std3` axioms only) between the native `TFlat` pass
`OptFlatBranch.tailDupFlat` and `Func.tailDup`:

* `OptFlatBranch.tailDupWithPlanFlat_eq`
* `OptFlatBranch.tailDupOnceFlat_eq`
* `OptFlatBranch.tailDupLoopFlat_eq`
* `OptFlatBranch.tailDupFlat_eq`
* `OptFlatBranch.denoteFunc_tailDupFlat`
* `OptFlatBranch.tailDupFlat_wfCheck`
* `OptFlatBranch.tailDupFlatFn_toFn` / `OptFlatBranch.tailDupFlatFn_wfCheck`
-/

set_option autoImplicit false

public section

namespace LeanQbe.T
namespace OptFlatBranch

open OptFlatPlanKit
open TailDup

/-! ## 1. `validateDupPlanFlat` Equivalence -/

mutual
private theorem validateDupPlanFlat_eq {rs : List Ty} :
    (plan : DupPlan) → (tf : TFlat rs) → {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × UnitV t)} → {ls : List ((ts : List Ty) × BoolL ts)} →
    {inLD : Nat} → {inLE : Trie ((ts : List Ty) × BoolL ts)} →
    CtxTypes Γ vs → CtxTypes Δ ls → TrieCtxMatch inLD inLE ls →
    tf.wfCheck Γ Δ = true →
    validateDupPlanFlat plan inLD inLE tf =
      validatePlan plan (denote UnitV BoolL tf vs ls)
  | plan, .let_ (ts := ts) op k, Γ, Δ, vs, ls, inLD, inLE, hΓ, hΔ, hmL, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨args', hargs⟩ := Option.isSome_iff_exists.1
      (denoteArgs_isSome_of_checkArgs hΓ hwf.1)
    dsimp only [denote]; rw [hargs]; dsimp only
    cases plan with
    | node1 pk =>
      rw [validateDupPlanFlat.eq_def, validatePlan.eq_def]; dsimp only
      exact validateDupPlanFlat_eq pk k (CtxTypes.push (Tup.units ts) hΓ) hΔ hmL hwf.2
    | leaf | node2 _ _ | group _ _ _ =>
      rw [validateDupPlanFlat.eq_def, validatePlan.eq_def]
  | plan, .load t a k, Γ, Δ, vs, ls, inLD, inLE, hΓ, hΔ, hmL, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨a', ha⟩ := Option.isSome_iff_exists.1
      (denoteArg_isSome_of_checkArg hΓ hwf.1)
    dsimp only [denote]; rw [ha]; dsimp only
    cases plan with
    | node1 pk =>
      rw [validateDupPlanFlat.eq_def, validatePlan.eq_def]; dsimp only
      exact validateDupPlanFlat_eq pk k (.cons hΓ) hΔ hmL hwf.2
    | leaf | node2 _ _ | group _ _ _ =>
      rw [validateDupPlanFlat.eq_def, validatePlan.eq_def]
  | plan, .store v a k, Γ, Δ, vs, ls, inLD, inLE, hΓ, hΔ, hmL, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨v', hv⟩ := Option.isSome_iff_exists.1
      (denoteArg_isSome_of_checkArg hΓ hwf.1.1)
    obtain ⟨a', ha⟩ := Option.isSome_iff_exists.1
      (denoteArg_isSome_of_checkArg hΓ hwf.1.2)
    dsimp only [denote]; rw [hv, ha]; dsimp only
    cases plan with
    | node1 pk =>
      rw [validateDupPlanFlat.eq_def, validatePlan.eq_def]; dsimp only
      exact validateDupPlanFlat_eq pk k hΓ hΔ hmL hwf.2
    | leaf | node2 _ _ | group _ _ _ =>
      rw [validateDupPlanFlat.eq_def, validatePlan.eq_def]
  | plan, .call f bs args k, Γ, Δ, vs, ls, inLD, inLE, hΓ, hΔ, hmL, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨args', hargs⟩ := Option.isSome_iff_exists.1
      (denoteArgs_isSome_of_checkArgs hΓ hwf.1)
    dsimp only [denote]; rw [hargs]; dsimp only
    cases plan with
    | node1 pk =>
      rw [validateDupPlanFlat.eq_def, validatePlan.eq_def]; dsimp only
      exact validateDupPlanFlat_eq pk k (CtxTypes.push (Tup.units bs) hΓ) hΔ hmL hwf.2
    | leaf | node2 _ _ | group _ _ _ =>
      rw [validateDupPlanFlat.eq_def, validatePlan.eq_def]
  | plan, .jnz c t e, Γ, Δ, vs, ls, inLD, inLE, hΓ, hΔ, hmL, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨c', hc⟩ := Option.isSome_iff_exists.1
      (denoteArg_isSome_of_checkArg hΓ hwf.1.1)
    dsimp only [denote]; rw [hc]; dsimp only
    cases plan with
    | node2 pt pe =>
      rw [validateDupPlanFlat.eq_def, validatePlan.eq_def]; dsimp only
      rw [validateDupPlanFlat_eq pt t hΓ hΔ hmL hwf.1.2,
        validateDupPlanFlat_eq pe e hΓ hΔ hmL hwf.2]
    | leaf | node1 _ | group _ _ _ =>
      rw [validateDupPlanFlat.eq_def, validatePlan.eq_def]
  | plan, .jump (ts := ts) j args, Γ, Δ, vs, ls, inLD, inLE, hΓ, hΔ, hmL, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨w, hlk, hres⟩ := lookupL_eq_some_resolveLabel hΔ hmL hwf.1
    obtain ⟨args', hargs⟩ := Option.isSome_iff_exists.1
      (denoteArgs_isSome_of_checkArgs hΓ hwf.2)
    dsimp only [denote]; rw [hlk, hargs]; dsimp only
    cases plan with
    | leaf =>
      rw [validateDupPlanFlat.eq_def, validatePlan.eq_def]; dsimp only; rw [hres]; rfl
    | node1 _ | node2 _ _ | group _ _ _ =>
      rw [validateDupPlanFlat.eq_def, validatePlan.eq_def]
  | plan, .ret vs', Γ, _, vs, _, _, _, hΓ, _, _, hwf => by
    obtain ⟨rvs, hr⟩ := Option.isSome_iff_exists.1
      (denoteArgs_isSome_of_checkArgs hΓ hwf)
    dsimp only [denote]; rw [hr]; dsimp only
    cases plan with
    | leaf => rw [validateDupPlanFlat.eq_def, validatePlan.eq_def]
    | node1 _ | node2 _ _ | group _ _ _ =>
      rw [validateDupPlanFlat.eq_def, validatePlan.eq_def]
  | plan, .exit f args, Γ, _, vs, _, _, _, hΓ, _, _, hwf => by
    obtain ⟨rargs, ha⟩ := Option.isSome_iff_exists.1
      (denoteArgs_isSome_of_checkArgs hΓ hwf)
    dsimp only [denote]; rw [ha]; dsimp only
    cases plan with
    | leaf => rw [validateDupPlanFlat.eq_def, validatePlan.eq_def]
    | node1 _ | node2 _ _ | group _ _ _ =>
      rw [validateDupPlanFlat.eq_def, validatePlan.eq_def]
  | plan, .hlt, _, _, _, _, _, _, _, _, _, _ => by
    dsimp only [denote]
    cases plan with
    | leaf => rw [validateDupPlanFlat.eq_def, validatePlan.eq_def]
    | node1 _ | node2 _ _ | group _ _ _ =>
      rw [validateDupPlanFlat.eq_def, validatePlan.eq_def]
  | plan, .group (sig := sig) bodies k, Γ, Δ, vs, ls, inLD, inLE, hΓ, hΔ, hmL, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denote]
    cases plan with
    | group acts pbs pk =>
      rw [validateDupPlanFlat.eq_def, validatePlan.eq_def]; dsimp only
      have hbNo := validateDupBlocksFlat_eq acts pbs bodies hΓ
        (ctxTypes_pushTup_rev (noDupBoolTup acts sig) hΔ)
        (trieCtxMatch_insertTupEnv hmL (noDupBoolTup acts sig)) hwf.1
      have hbYes := validateKeptBlocksFlat_eq acts pbs bodies hΓ
        (ctxTypes_pushTup_rev (dupBoolTup acts sig) hΔ)
        (trieCtxMatch_insertTupEnv hmL (dupBoolTup acts sig)) hwf.1
      have hk := validateDupPlanFlat_eq pk k hΓ
        (ctxTypes_pushTup_rev (dupBoolTup acts sig) hΔ)
        (trieCtxMatch_insertTupEnv hmL (dupBoolTup acts sig)) hwf.2
      rw [hbNo, hbYes, hk]
    | leaf | node1 _ | node2 _ _ =>
      rw [validateDupPlanFlat.eq_def, validatePlan.eq_def]
termination_by structural plan _ => plan

private theorem validateDupBlocksFlat_eq {rs : List Ty} :
    (acts : List DupAct) → (pbs : DupPlanB) → {sig : List (List Ty)} → (tb : TBlocks rs sig) →
    {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × UnitV t)} → {ls : List ((ts : List Ty) × BoolL ts)} →
    {inLD : Nat} → {inLE : Trie ((ts : List Ty) × BoolL ts)} →
    CtxTypes Γ vs → CtxTypes Δ ls → TrieCtxMatch inLD inLE ls →
    tb.wfCheck Γ Δ = true →
    validateDupBlocksFlat acts pbs inLD inLE tb =
      validateDupBlocks acts pbs (denoteB UnitV BoolL tb vs ls)
  | acts, .nil, [], .nil, _, _, _, _, _, _, _, _, _, _ => by
    rw [validateDupBlocksFlat.eq_def, validateDupBlocks.eq_def]
    cases acts <;> rfl
  | _, .cons _ _, [], .nil, _, _, _, _, _, _, _, _, _, _ => by
    rw [validateDupBlocksFlat.eq_def, validateDupBlocks.eq_def]; rfl
  | acts, .nil, _ :: _, .cons _ _, _, _, _, _, _, _, _, _, _, _ => by
    rw [validateDupBlocksFlat.eq_def, validateDupBlocks.eq_def]
    cases acts <;> simp only <;> rfl
  | [], .cons _ _, _ :: _, .cons _ _, _, _, _, _, _, _, _, _, _, _ => by
    rw [validateDupBlocksFlat.eq_def, validateDupBlocks.eq_def]; rfl
  | a :: acts', .cons pb pbs', ts :: _, .cons b bs, Γ, Δ, vs, ls, inLD, inLE,
      hΓ, hΔ, hmL, hwf => by
    dsimp only [TBlocks.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    rw [validateDupBlocksFlat.eq_def, denoteB.eq_def, validateDupBlocks.eq_def]; simp only
    cases a with
    | dup =>
      simp only
      rw [validateDupPlanFlat_eq pb b (ctxTypes_pushTup_rev _ hΓ) hΔ hmL hwf.1,
        validateDupBlocksFlat_eq acts' pbs' bs hΓ hΔ hmL hwf.2]
    | keep | drop =>
      exact validateDupBlocksFlat_eq acts' pbs' bs hΓ hΔ hmL hwf.2
termination_by structural _ pbs => pbs

private theorem validateKeptBlocksFlat_eq {rs : List Ty} :
    (acts : List DupAct) → (pbs : DupPlanB) → {sig : List (List Ty)} → (tb : TBlocks rs sig) →
    {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × UnitV t)} → {ls : List ((ts : List Ty) × BoolL ts)} →
    {inLD : Nat} → {inLE : Trie ((ts : List Ty) × BoolL ts)} →
    CtxTypes Γ vs → CtxTypes Δ ls → TrieCtxMatch inLD inLE ls →
    tb.wfCheck Γ Δ = true →
    validateKeptBlocksFlat acts pbs inLD inLE tb =
      validateKeptBlocks acts pbs (denoteB UnitV BoolL tb vs ls)
  | acts, .nil, [], .nil, _, _, _, _, _, _, _, _, _, _ => by
    rw [validateKeptBlocksFlat.eq_def, validateKeptBlocks.eq_def]
    cases acts <;> rfl
  | _, .cons _ _, [], .nil, _, _, _, _, _, _, _, _, _, _ => by
    rw [validateKeptBlocksFlat.eq_def, validateKeptBlocks.eq_def]; rfl
  | acts, .nil, _ :: _, .cons _ _, _, _, _, _, _, _, _, _, _, _ => by
    rw [validateKeptBlocksFlat.eq_def, validateKeptBlocks.eq_def]
    cases acts <;> simp only <;> rfl
  | [], .cons _ _, _ :: _, .cons _ _, _, _, _, _, _, _, _, _, _, _ => by
    rw [validateKeptBlocksFlat.eq_def, validateKeptBlocks.eq_def]; rfl
  | a :: acts', .cons pb pbs', ts :: _, .cons b bs, Γ, Δ, vs, ls, inLD, inLE,
      hΓ, hΔ, hmL, hwf => by
    dsimp only [TBlocks.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    rw [validateKeptBlocksFlat.eq_def, denoteB.eq_def, validateKeptBlocks.eq_def]; simp only
    cases a with
    | keep =>
      simp only
      rw [validateDupPlanFlat_eq pb b (ctxTypes_pushTup_rev _ hΓ) hΔ hmL hwf.1,
        validateKeptBlocksFlat_eq acts' pbs' bs hΓ hΔ hmL hwf.2]
    | dup | drop =>
      exact validateKeptBlocksFlat_eq acts' pbs' bs hΓ hΔ hmL hwf.2
termination_by structural _ pbs => pbs
end

/-! ## 2. `rewriteDupFlat` Equivalence -/

/-- Simulation relation linking `PlanLFlat` payloads to PHOAS `TailDup.DupL K KL`. -/
private def DupLFlatMatch {rs ts : List Ty} : PlanLFlat rs ts → DupL K KL rs ts → Prop
  | .keep l₁, .keep l₂ => l₁ = l₂
  | .dead, .dead => True
  | .splice fFlat, .dup fPhoas =>
    ∀ outVD outLD args, fFlat outVD outLD args = toTFlat (fPhoas args) outVD outLD
  | _, _ => False

private theorem deadTupDup_match {rs : List Ty} :
    (sig : List (List Ty)) →
    TRel (fun _ => DupLFlatMatch (rs := rs)) (deadTupFlat sig) (TailDup.deadTup sig)
  | [] => .nil
  | _ :: sig => .cons trivial (deadTupDup_match sig)

private theorem expandDupKeepFlat_match {rs : List Ty} :
    (acts : List DupAct) → (sig : List (List Ty)) → (Js : Tup KL (filterActsSig acts sig)) →
    TRel (fun _ => DupLFlatMatch (rs := rs))
      (expandDupKeepFlat acts sig Js) (expandKeepLabels acts sig Js)
  | _, [], () => .nil
  | [], _ :: sig, () => .cons trivial (deadTupDup_match sig)
  | .keep :: acts, _ :: sig, (_, js) => .cons rfl (expandDupKeepFlat_match acts sig js)
  | .dup :: acts, _ :: sig, js
  | .drop :: acts, _ :: sig, js => .cons trivial (expandDupKeepFlat_match acts sig js)

private theorem mkFreshVar_eq_toArgTup :
    (ts : List Ty) → (inVD outVD : Nat) →
    mkFreshTup (fun _ _ od => Arg.var od) ts inVD outVD = toArgTup (Tup.levels ts outVD)
  | [], _, _ => rfl
  | _ :: ts, inVD, outVD => by
    dsimp only [mkFreshTup, Tup.levels, toArgTup]
    rw [mkFreshVar_eq_toArgTup ts (inVD + 1) (outVD + 1)]

private theorem tupFreshVar_eq_toArgTup :
    (ts : List Ty) → (xs : Tup K ts) → (n : Nat) →
    tupFreshWith (fun x _ => Arg.var x) ts xs n = toArgTup xs
  | [], (), _ => rfl
  | _ :: ts, (_, xs), n => by
    dsimp only [tupFreshWith, toArgTup]
    rw [tupFreshVar_eq_toArgTup ts xs (n + 1)]

private theorem rewriteKeptBlocks_nil_eq {rs : List Ty} :
    (acts : List DupAct) → {sig : List (List Ty)} →
    (bs : Blocks (Arg K) (DupL K KL rs) rs sig) → (ovd old : Nat) →
    toTBlocks (rewriteKeptBlocks acts .nil bs) ovd old =
      mkHltTBlocks (filterActsSig acts sig)
  | _, _, .nil, _, _ => by
    rw [rewriteKeptBlocks.eq_def]; rfl
  | [], _ :: _, .cons _ _, _, _ => by
    rw [rewriteKeptBlocks.eq_def]; rfl
  | .keep :: acts', _ :: _, .cons _ bs, ovd, old => by
    rw [rewriteKeptBlocks.eq_def]; dsimp only [filterActsSig, toTBlocks, toTFlat, mkHltTBlocks]
    exact congrArg (TBlocks.cons .hlt) (rewriteKeptBlocks_nil_eq acts' bs ovd old)
  | .dup :: acts', _ :: _, .cons _ bs, ovd, old => by
    rw [rewriteKeptBlocks.eq_def]; dsimp only [filterActsSig]
    exact rewriteKeptBlocks_nil_eq acts' bs ovd old
  | .drop :: acts', _ :: _, .cons _ bs, ovd, old => by
    rw [rewriteKeptBlocks.eq_def]; dsimp only [filterActsSig]
    exact rewriteKeptBlocks_nil_eq acts' bs ovd old

mutual
private theorem rewriteDupFlat_eq {rs : List Ty} :
    (plan : DupPlan) → (tf : TFlat rs) → {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × Arg K t)} → {ls : List ((ts : List Ty) × DupL K KL rs ts)} →
    {inVD outVD outLD : Nat} →
    {inVE : Trie ((t : Ty) × Arg K t)} →
    {inLD : Nat} → {inLE : Trie ((ts : List Ty) × PlanLFlat rs ts)} →
    CtxTypes Γ vs → CtxTypes Δ ls → TrieCtxMatch inVD inVE vs →
    TrieRelMatch (fun _ => DupLFlatMatch (rs := rs)) inLD inLE ls → tf.wfCheck Γ Δ = true →
    toTFlat (rewriteExpr plan (denote (Arg K) (DupL K KL rs) tf vs ls)) outVD outLD =
      rewriteDupFlat plan inVD inVE inLD inLE outVD outLD tf
  | plan, .let_ (ts := ts) op k, Γ, Δ, vs, ls, inVD, outVD, outLD, inVE, inLD, inLE,
      hΓ, hΔ, hmV, hmL, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denote]
    rw [denoteArgs_eq_some_resolveEnvArgs hΓ hmV op.args hwf.1]; dsimp only
    cases plan with
    | node1 pk =>
      rw [rewriteExpr.eq_def, rewriteDupFlat.eq_def]; dsimp only [flattenOp, toTFlat]
      have hfresh := trieCtxMatch_insertFreshWith (fun _ _ od => Arg.var od) hmV ts outVD
      rw [mkFreshVar_eq_toArgTup] at hfresh
      exact congrArg (TFlat.let_ _)
        (rewriteDupFlat_eq pk k (ctxTypes_pushTup_rev _ hΓ) hΔ hfresh hmL hwf.2)
    | leaf | node2 _ _ | group _ _ _ =>
      rw [rewriteExpr.eq_def, rewriteDupFlat.eq_def]; rfl
  | plan, .load t a k, Γ, Δ, vs, ls, inVD, outVD, outLD, inVE, inLD, inLE,
      hΓ, hΔ, hmV, hmL, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denote]
    rw [denoteArg_eq_some_resolveEnvArg hΓ hmV a hwf.1]; dsimp only
    cases plan with
    | node1 pk =>
      rw [rewriteExpr.eq_def, rewriteDupFlat.eq_def]; dsimp only [toTFlat]
      exact congrArg (TFlat.load t _)
        (rewriteDupFlat_eq pk k (.cons hΓ) hΔ (hmV.cons t (Arg.var outVD)) hmL hwf.2)
    | leaf | node2 _ _ | group _ _ _ =>
      rw [rewriteExpr.eq_def, rewriteDupFlat.eq_def]; rfl
  | plan, .store v a k, Γ, Δ, vs, ls, inVD, outVD, outLD, inVE, inLD, inLE,
      hΓ, hΔ, hmV, hmL, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denote]
    rw [denoteArg_eq_some_resolveEnvArg hΓ hmV v hwf.1.1,
      denoteArg_eq_some_resolveEnvArg hΓ hmV a hwf.1.2]; dsimp only
    cases plan with
    | node1 pk =>
      rw [rewriteExpr.eq_def, rewriteDupFlat.eq_def]; dsimp only [toTFlat]
      exact congrArg (TFlat.store _ _) (rewriteDupFlat_eq pk k hΓ hΔ hmV hmL hwf.2)
    | leaf | node2 _ _ | group _ _ _ =>
      rw [rewriteExpr.eq_def, rewriteDupFlat.eq_def]; rfl
  | plan, .call f bs args k, Γ, Δ, vs, ls, inVD, outVD, outLD, inVE, inLD, inLE,
      hΓ, hΔ, hmV, hmL, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denote]
    rw [denoteArgs_eq_some_resolveEnvArgs hΓ hmV args hwf.1]; dsimp only
    cases plan with
    | node1 pk =>
      rw [rewriteExpr.eq_def, rewriteDupFlat.eq_def]; dsimp only [toTFlat]
      have hfresh := trieCtxMatch_insertFreshWith (fun _ _ od => Arg.var od) hmV bs outVD
      rw [mkFreshVar_eq_toArgTup] at hfresh
      exact congrArg (TFlat.call f bs _)
        (rewriteDupFlat_eq pk k (ctxTypes_pushTup_rev _ hΓ) hΔ hfresh hmL hwf.2)
    | leaf | node2 _ _ | group _ _ _ =>
      rw [rewriteExpr.eq_def, rewriteDupFlat.eq_def]; rfl
  | plan, .jnz c t e, Γ, Δ, vs, ls, inVD, outVD, outLD, inVE, inLD, inLE,
      hΓ, hΔ, hmV, hmL, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denote]
    rw [denoteArg_eq_some_resolveEnvArg hΓ hmV c hwf.1.1]; dsimp only
    cases plan with
    | node2 pt pe =>
      rw [rewriteExpr.eq_def, rewriteDupFlat.eq_def]; dsimp only [toTFlat]
      rw [rewriteDupFlat_eq pt t hΓ hΔ hmV hmL hwf.1.2,
        rewriteDupFlat_eq pe e hΓ hΔ hmV hmL hwf.2]
    | leaf | node1 _ | group _ _ _ =>
      rw [rewriteExpr.eq_def, rewriteDupFlat.eq_def]; rfl
  | plan, .jump (ts := ts) j args, Γ, Δ, vs, ls, inVD, outVD, outLD, inVE, inLD, inLE,
      hΓ, hΔ, hmV, hmL, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨w₁, w₂, hres, hlk, hm⟩ := TrieRelMatch.resolveLabel_rel hΔ hmL hwf.1
    dsimp only [denote]
    rw [hlk, denoteArgs_eq_some_resolveEnvArgs hΓ hmV args hwf.2]; dsimp only
    cases plan with
    | leaf =>
      rw [rewriteExpr.eq_def, rewriteDupFlat.eq_def]; dsimp only; rw [hres]
      cases w₁ with
      | keep l₁ =>
        cases w₂ with
        | keep l₂ => cases hm; rfl
        | dead => exact False.elim hm
        | dup _ => exact False.elim hm
      | dead =>
        cases w₂ with
        | keep _ => exact False.elim hm
        | dead => rfl
        | dup _ => exact False.elim hm
      | splice body₁ =>
        cases w₂ with
        | keep _ => exact False.elim hm
        | dead => exact False.elim hm
        | dup body₂ => exact (hm outVD outLD _).symm
    | node1 _ | node2 _ _ | group _ _ _ =>
      rw [rewriteExpr.eq_def, rewriteDupFlat.eq_def]; rfl
  | plan, .ret vs', Γ, _, vs, _, inVD, outVD, outLD, inVE, _, _,
      hΓ, _, hmV, _, hwf => by
    dsimp only [denote]
    rw [denoteArgs_eq_some_resolveEnvArgs hΓ hmV vs' hwf]; dsimp only
    cases plan with
    | leaf => rw [rewriteExpr.eq_def, rewriteDupFlat.eq_def]; rfl
    | node1 _ | node2 _ _ | group _ _ _ =>
      rw [rewriteExpr.eq_def, rewriteDupFlat.eq_def]; rfl
  | plan, .exit f args, Γ, _, vs, _, inVD, outVD, outLD, inVE, _, _,
      hΓ, _, hmV, _, hwf => by
    dsimp only [denote]
    rw [denoteArgs_eq_some_resolveEnvArgs hΓ hmV args hwf]; dsimp only
    cases plan with
    | leaf => rw [rewriteExpr.eq_def, rewriteDupFlat.eq_def]; rfl
    | node1 _ | node2 _ _ | group _ _ _ =>
      rw [rewriteExpr.eq_def, rewriteDupFlat.eq_def]; rfl
  | plan, .hlt, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by
    dsimp only [denote]
    cases plan with
    | leaf | node1 _ | node2 _ _ | group _ _ _ =>
      rw [rewriteExpr.eq_def, rewriteDupFlat.eq_def]; rfl
  | plan, .group (sig := sig) bodies k, Γ, Δ, vs, ls,
      inVD, outVD, outLD, inVE, inLD, inLE, hΓ, hΔ, hmV, hmL, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denote]
    cases plan with
    | group acts pbs pk =>
      rw [rewriteExpr.eq_def, rewriteDupFlat.eq_def]; dsimp only
      by_cases hkeep : acts.any (· == .keep) = true
      · simp only [hkeep, ↓reduceIte, toTFlat]
        have hno := expandDupKeepFlat_match (rs := rs) acts sig
          (Tup.levels (filterActsSig acts sig) outLD)
        have hmNo := TrieRelMatch.pushTup hno hmL
        have hdup := buildDupLabelsFlat_eq acts pbs bodies
          (expandDupKeepFlat acts sig (Tup.levels (filterActsSig acts sig) outLD))
          (expandKeepLabels acts sig (Tup.levels (filterActsSig acts sig) outLD))
          hΓ (ctxTypes_pushTup_rev _ hΔ) hmV hmNo hno hwf.1
        have hmDup := TrieRelMatch.pushTup hdup hmL
        have hΔ' := ctxTypes_pushTup_rev (buildDupLabels acts pbs
          (denoteB (Arg K) (DupL K KL rs) bodies vs
            (pushTup (expandKeepLabels acts sig (Tup.levels (filterActsSig acts sig) outLD)) ls))
          (expandKeepLabels acts sig (Tup.levels (filterActsSig acts sig) outLD))) hΔ
        have hb := rewriteDupKeptBlocksFlat_eq acts pbs bodies
          hΓ hΔ' hmV hmDup hwf.1
          (outVD := outVD) (outLD := outLD + (filterActsSig acts sig).length)
        have hk := rewriteDupFlat_eq pk k hΓ hΔ' hmV hmDup hwf.2
          (outVD := outVD) (outLD := outLD + (filterActsSig acts sig).length)
        rw [hb, hk]
      · simp only [hkeep, Bool.false_eq_true, ↓reduceIte]
        have hno := deadTupDup_match (rs := rs) sig
        have hmNo := TrieRelMatch.pushTup hno hmL
        have hdup := buildDupLabelsFlat_eq acts pbs bodies (deadTupFlat sig) (TailDup.deadTup sig)
          hΓ (ctxTypes_pushTup_rev _ hΔ) hmV hmNo hno hwf.1
        have hmDup := TrieRelMatch.pushTup hdup hmL
        have hΔ' := ctxTypes_pushTup_rev (buildDupLabels acts pbs
          (denoteB (Arg K) (DupL K KL rs) bodies vs (pushTup (TailDup.deadTup sig) ls))
          (TailDup.deadTup sig)) hΔ
        exact rewriteDupFlat_eq pk k hΓ hΔ' hmV hmDup hwf.2 (outVD := outVD) (outLD := outLD)
    | leaf | node1 _ | node2 _ _ =>
      rw [rewriteExpr.eq_def, rewriteDupFlat.eq_def]; rfl
termination_by structural plan _ => plan

private theorem buildDupLabelsFlat_eq {rs : List Ty} :
    (acts : List DupAct) → (pbs : DupPlanB) → {sig : List (List Ty)} → (tb : TBlocks rs sig) →
    (lsF : Tup (PlanLFlat rs) sig) → (lsP : Tup (DupL K KL rs) sig) →
    {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × Arg K t)} → {ls : List ((ts : List Ty) × DupL K KL rs ts)} →
    {inVD : Nat} → {inVE : Trie ((t : Ty) × Arg K t)} →
    {inLD : Nat} → {inLE : Trie ((ts : List Ty) × PlanLFlat rs ts)} →
    CtxTypes Γ vs → CtxTypes Δ ls → TrieCtxMatch inVD inVE vs →
    TrieRelMatch (fun _ => DupLFlatMatch (rs := rs)) inLD inLE ls →
    TRel (fun _ => DupLFlatMatch (rs := rs)) lsF lsP → tb.wfCheck Γ Δ = true →
    TRel (fun _ => DupLFlatMatch (rs := rs))
      (buildDupLabelsFlat acts pbs inVD inVE inLD inLE tb lsF)
      (buildDupLabels acts pbs (denoteB (Arg K) (DupL K KL rs) tb vs ls) lsP)
  | _, _, [], .nil, (), (), _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by
    rw [buildDupLabelsFlat.eq_def, denoteB.eq_def, buildDupLabels.eq_def]; exact .nil
  | acts, pbs, _ :: sig', .cons b bs, (lF, lsF), (lP, lsP), Γ, Δ, vs, ls,
      inVD, inVE, inLD, inLE, hΓ, hΔ, hmV, hmL, hrel, hwf => by
    dsimp only [TBlocks.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    cases hrel with
    | cons hl hls =>
      rw [buildDupLabelsFlat.eq_def, denoteB.eq_def, buildDupLabels.eq_def]; simp only
      cases acts with
      | nil => exact .cons trivial (deadTupDup_match sig')
      | cons a acts' =>
        cases pbs with
        | nil => simp only; exact .cons trivial (deadTupDup_match sig')
        | cons pb pbs' =>
          cases a with
          | dup =>
            simp only
            refine .cons ?_ (buildDupLabelsFlat_eq acts' pbs' bs lsF lsP
              hΓ hΔ hmV hmL hls hwf.2)
            intro ovd old args
            exact (rewriteDupFlat_eq pb b (ctxTypes_pushTup_rev args hΓ) hΔ
              (trieCtxMatch_insertTupEnv hmV args) hmL hwf.1).symm
          | keep =>
            exact .cons hl (buildDupLabelsFlat_eq acts' pbs' bs lsF lsP
              hΓ hΔ hmV hmL hls hwf.2)
          | drop =>
            exact .cons trivial (buildDupLabelsFlat_eq acts' pbs' bs lsF lsP
              hΓ hΔ hmV hmL hls hwf.2)
termination_by structural _ pbs => pbs

private theorem rewriteDupKeptBlocksFlat_eq {rs : List Ty} :
    (acts : List DupAct) → (pbs : DupPlanB) → {sig : List (List Ty)} → (tb : TBlocks rs sig) →
    {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × Arg K t)} → {ls : List ((ts : List Ty) × DupL K KL rs ts)} →
    {inVD outVD outLD : Nat} → {inVE : Trie ((t : Ty) × Arg K t)} →
    {inLD : Nat} → {inLE : Trie ((ts : List Ty) × PlanLFlat rs ts)} →
    CtxTypes Γ vs → CtxTypes Δ ls → TrieCtxMatch inVD inVE vs →
    TrieRelMatch (fun _ => DupLFlatMatch (rs := rs)) inLD inLE ls → tb.wfCheck Γ Δ = true →
    toTBlocks (rewriteKeptBlocks acts pbs (denoteB (Arg K) (DupL K KL rs) tb vs ls))
        outVD outLD =
      rewriteDupKeptBlocksFlat acts pbs inVD inVE inLD inLE outVD outLD tb
  | acts, pbs, [], .nil, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by
    rw [rewriteDupKeptBlocksFlat.eq_def, denoteB.eq_def, rewriteKeptBlocks.eq_def]; rfl
  | [], pbs, _ :: _, .cons _ _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by
    rw [rewriteDupKeptBlocksFlat.eq_def, denoteB.eq_def, rewriteKeptBlocks.eq_def]; rfl
  | a :: acts', .nil, _ :: _, .cons b bs, _, _, _, _, _, outVD, outLD, _, _, _, _,
      _, _, _, _ => by
    rw [rewriteDupKeptBlocksFlat.eq_def, denoteB.eq_def]
    exact rewriteKeptBlocks_nil_eq (a :: acts') (.cons _ _) outVD outLD
  | a :: acts', .cons pb pbs', ts :: _, .cons b bs, Γ, Δ, vs, ls,
      inVD, outVD, outLD, inVE, inLD, inLE, hΓ, hΔ, hmV, hmL, hwf => by
    dsimp only [TBlocks.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    rw [rewriteDupKeptBlocksFlat.eq_def, denoteB.eq_def, rewriteKeptBlocks.eq_def]
    cases a with
    | keep =>
      dsimp only [toTBlocks, filterActsSig]
      have hfresh := trieCtxMatch_insertFreshWith (fun _ _ od => Arg.var od) hmV ts outVD
      rw [mkFreshVar_eq_toArgTup] at hfresh
      exact congr (congrArg TBlocks.cons
        (rewriteDupFlat_eq pb b (ctxTypes_pushTup_rev _ hΓ) hΔ hfresh hmL hwf.1))
        (rewriteDupKeptBlocksFlat_eq acts' pbs' bs hΓ hΔ hmV hmL hwf.2)
    | dup | drop =>
      exact rewriteDupKeptBlocksFlat_eq acts' pbs' bs hΓ hΔ hmV hmL hwf.2
termination_by structural _ pbs => pbs
end

/-! ## 3. Public `tailDupFlat` Equivalence Theorems -/

/-- `tailDupWithPlanFlat as plan tf = reifyFunc (Func.tailDupWithPlan plan (denoteFunc tf))`
under `wfCheck = true`. -/
theorem tailDupWithPlanFlat_eq {as rs : List Ty} (plan : DupPlan) (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    tailDupWithPlanFlat as plan tf =
      reifyFunc (Func.tailDupWithPlan plan (denoteFunc (as := as) tf)) := by
  dsimp only [tailDupWithPlanFlat, Func.tailDupWithPlan, denoteFunc, reifyFunc]
  have hval : validateDupPlanFlat plan 0 .empty tf =
      validatePlan plan (denote UnitV BoolL tf (pushTup (Tup.units as) []) []) :=
    validateDupPlanFlat_eq plan tf (ctxTypes_pushTup_rev (Tup.units as) .nil) .nil
      TrieCtxMatch.empty hwf
  rw [hval]
  by_cases hval' : validatePlan plan (denote UnitV BoolL tf (pushTup (Tup.units as) []) []) = true
  · simp only [hval', ↓reduceIte]
    have hmV := trieCtxMatch_initEnv (fun x _ => Arg.var x) as
    rw [tupFreshVar_eq_toArgTup] at hmV
    have hrw := rewriteDupFlat_eq plan tf (ctxTypes_pushTup_rev _ .nil) .nil hmV
      (TrieRelMatch.empty (fun _ => DupLFlatMatch (rs := rs))) hwf
      (outVD := as.length) (outLD := 0)
    exact hrw.symm
  · simp only [hval', Bool.false_eq_true, ↓reduceIte]
    exact (reifyFunc_denoteFunc_eq tf hwf).symm

/-- `tailDupOnceFlat` agrees with `Func.tailDupOnce` on `changed` and reifies `.1`. -/
theorem tailDupOnceFlat_eq {as rs : List Ty} (tf : TFlat rs)
    (cfg : TailDupConfig := {}) (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    (tailDupOnceFlat as tf cfg).1 =
        reifyFunc (Func.tailDupOnce (denoteFunc (as := as) tf) cfg).1 ∧
      (tailDupOnceFlat as tf cfg).2 =
        (Func.tailDupOnce (denoteFunc (as := as) tf) cfg).2 := by
  dsimp only [tailDupOnceFlat, Func.tailDupOnce]
  rw [reifyFunc_denoteFunc_eq tf hwf]
  split
  · refine ⟨?_, rfl⟩
    exact tailDupWithPlanFlat_eq _ tf hwf
  · exact ⟨(reifyFunc_denoteFunc_eq tf hwf).symm, rfl⟩

/-- `tailDupLoopFlat` matches `reifyFunc ∘ Func.tailDupLoop` under `wfCheck = true`. -/
theorem tailDupLoopFlat_eq {as rs : List Ty} (cfg : TailDupConfig) :
    (fuel : Nat) → (tf : TFlat rs) → tf.wfCheck (pushTypes as []) [] = true →
    tailDupLoopFlat as cfg fuel tf =
      reifyFunc (Func.tailDupLoop cfg fuel (denoteFunc (as := as) tf))
  | 0, tf, hwf => (reifyFunc_denoteFunc_eq tf hwf).symm
  | fuel + 1, tf, hwf => by
    dsimp only [tailDupLoopFlat, Func.tailDupLoop]
    have h1 := tailDupOnceFlat_eq tf cfg hwf
    rw [h1.2]
    split
    · have hwf1 : (Func.tailDupOnce (denoteFunc (as := as) tf) cfg).1.Wf :=
        Func.tailDupOnce_wf cfg
      have hwfFlat : (tailDupOnceFlat as tf cfg).1.wfCheck (pushTypes as []) [] = true := by
        rw [h1.1]; exact PassFlatKit.reifyFunc_wfCheck hwf1
      rw [tailDupLoopFlat_eq cfg fuel (tailDupOnceFlat as tf cfg).1 hwfFlat, h1.1]
      exact congrArg reifyFunc (congrArg (Func.tailDupLoop cfg fuel) (Func.renorm_eq_self hwf1))
    · exact h1.1

/-- `tailDupFlat as tf cfg = reifyFunc (Func.tailDup (denoteFunc tf) cfg)` under
`wfCheck = true`. -/
theorem tailDupFlat_eq {as rs : List Ty} (tf : TFlat rs) (cfg : TailDupConfig := {})
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    tailDupFlat as tf cfg = reifyFunc (Func.tailDup (denoteFunc (as := as) tf) cfg) :=
  tailDupLoopFlat_eq cfg cfg.maxIters tf hwf

/-- `denoteFunc (tailDupFlat as tf cfg) = Func.tailDup (denoteFunc tf) cfg` under
`wfCheck = true`. -/
theorem denoteFunc_tailDupFlat {as rs : List Ty} (tf : TFlat rs) (cfg : TailDupConfig := {})
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    denoteFunc (as := as) (tailDupFlat as tf cfg) =
      Func.tailDup (denoteFunc (as := as) tf) cfg := by
  rw [tailDupFlat_eq tf cfg hwf]
  exact Func.renorm_eq_self (Func.tailDup_wf (Func.wf_of_denote tf rfl) cfg)

/-- `tailDupFlat` preserves `wfCheck`. -/
theorem tailDupFlat_wfCheck {as rs : List Ty} (tf : TFlat rs) (cfg : TailDupConfig := {})
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    (tailDupFlat as tf cfg).wfCheck (pushTypes as []) [] = true := by
  rw [tailDupFlat_eq tf cfg hwf]
  exact PassFlatKit.reifyFunc_wfCheck (Func.tailDup_wf (Func.wf_of_denote tf rfl) cfg)

/-- `(tailDupFlatFn f cfg).toFn = ⟨f.name, f.as, f.rs, Func.tailDup f.toFn.body cfg⟩` under
`wfCheck = true`. -/
theorem tailDupFlatFn_toFn (f : TFlatFn) (cfg : TailDupConfig := {}) (hwf : f.wfCheck = true) :
    (tailDupFlatFn f cfg).toFn = ⟨f.name, f.as, f.rs, Func.tailDup f.toFn.body cfg⟩ := by
  dsimp only [tailDupFlatFn, TFlatFn.toFn]
  rw [denoteFunc_tailDupFlat f.body cfg hwf]

/-- `tailDupFlatFn` preserves `TFlatFn.wfCheck`. -/
theorem tailDupFlatFn_wfCheck (f : TFlatFn) (cfg : TailDupConfig := {}) (hwf : f.wfCheck = true) :
    (tailDupFlatFn f cfg).wfCheck = true :=
  tailDupFlat_wfCheck f.body cfg hwf

end OptFlatBranch
end LeanQbe.T
