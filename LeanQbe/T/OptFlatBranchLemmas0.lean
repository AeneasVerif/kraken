module

public import LeanQbe.T.OptFlatBranch
import LeanQbe.T.FlatDirectLemmas
import LeanQbe.T.PassFlatKit
import LeanQbe.T.OptFlatSimKit
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
open OptFlatSimKit
open TailDup

/-! ## 1. `validateDupPlanFlat` Equivalence -/

local macro "dup_val_step" p:Lean.Parser.Tactic.elimTarget "," eq1:Lean.Parser.Tactic.rwRule ","
    eq2:Lean.Parser.Tactic.rwRule "," e:term "," next:tactic : tactic => `(tactic| (
  obtain ⟨_, h⟩ := Option.isSome_iff_exists.1 $e
  dsimp only [denote]; rw [h]; dsimp only
  cases $p with
  | node1 _ => rw [$eq1, $eq2]; dsimp only; $next
  | leaf | node2 _ _ | group _ _ _ => rw [$eq1, $eq2]))

local macro "dup_val_ret" eq1:Lean.Parser.Tactic.rwRule ","
    eq2:Lean.Parser.Tactic.rwRule : term =>
  `(fun plan vs' hΓ _ _ _ hwf => by
    obtain ⟨_, h⟩ := Option.isSome_iff_exists.1 (denoteArgs_isSome_of_checkArgs hΓ hwf)
    dsimp only [denote]; rw [h]; dsimp only
    cases plan <;> rw [$eq1, $eq2])

local macro "dup_val_exit" eq1:Lean.Parser.Tactic.rwRule ","
    eq2:Lean.Parser.Tactic.rwRule : term =>
  `(fun plan _ args hΓ _ _ _ hwf => by
    obtain ⟨_, h⟩ := Option.isSome_iff_exists.1 (denoteArgs_isSome_of_checkArgs hΓ hwf)
    dsimp only [denote]; rw [h]; dsimp only
    cases plan <;> rw [$eq1, $eq2])

private theorem validateDupPlanFlat_both {rs : List Ty} :
    (∀ (tf : TFlat rs) {Γ Δ vs ls inVD} {_outVD : Nat} {inLD} {_outLD : Nat} {inVE inLE}
      (plan : DupPlan),
      CtxTypes Γ vs → CtxTypes Δ ls → TrieCtxMatch inVD inVE vs →
      (CtxTypes Δ ls ∧ TrieCtxMatch inLD inLE ls) → tf.wfCheck Γ Δ = true →
      validateDupPlanFlat plan inLD inLE tf = validatePlan plan (denote UnitV BoolL tf vs ls)) ∧
    (∀ {sig : List (List Ty)} (tb : TBlocks rs sig)
      {Γ Δ vs ls inVD} {_outVD : Nat} {inLD} {_outLD : Nat} {inVE inLE}
      (sp : List DupAct × DupPlanB),
      CtxTypes Γ vs → CtxTypes Δ ls → TrieCtxMatch inVD inVE vs →
      (CtxTypes Δ ls ∧ TrieCtxMatch inLD inLE ls) → tb.wfCheck Γ Δ = true →
      validateDupBlocksFlat sp.1 sp.2 inLD inLE tb =
        validateDupBlocks sp.1 sp.2 (denoteB UnitV BoolL tb vs ls) ∧
      validateKeptBlocksFlat sp.1 sp.2 inLD inLE tb =
        validateKeptBlocks sp.1 sp.2 (denoteB UnitV BoolL tb vs ls)) := by
  refine relSim_mutual
    (LR := fun Δ inLD inLE ls => CtxTypes Δ ls ∧ TrieCtxMatch inLD inLE ls) ⟨
    fun plan op k hΓ _ hmV hlr hwf ih => by
      obtain ⟨ha, hk⟩ := wf_let hwf
      dup_val_step plan, validateDupPlanFlat.eq_def, validatePlan.eq_def,
        denoteArgs_isSome_of_checkArgs hΓ ha,
        (exact ih (outVD' := 0) (outLD' := 0) _ (CtxTypes.push (Tup.units _) hΓ)
          (trieCtxMatch_insertTupEnv hmV _) hlr hk),
    fun plan t a k hΓ _ hmV hlr hwf ih => by
      obtain ⟨ha, hk⟩ := wf_load hwf
      dup_val_step plan, validateDupPlanFlat.eq_def, validatePlan.eq_def,
        denoteArg_isSome_of_checkArg hΓ ha,
        (exact ih (outVD' := 0) (outLD' := 0) _ (.cons hΓ) (hmV.cons t ()) hlr hk),
    fun plan v a k hΓ _ hmV hlr hwf ih => by
      obtain ⟨hv, ha, hk⟩ := wf_store hwf
      obtain ⟨_, hv'⟩ := Option.isSome_iff_exists.1 (denoteArg_isSome_of_checkArg hΓ hv)
      obtain ⟨_, ha'⟩ := Option.isSome_iff_exists.1 (denoteArg_isSome_of_checkArg hΓ ha)
      dsimp only [denote]; rw [hv', ha']; dsimp only
      cases plan with
      | node1 _ =>
        rw [validateDupPlanFlat.eq_def, validatePlan.eq_def]; dsimp only
        exact ih (outVD' := 0) (outLD' := 0) _ hΓ hmV hlr hk
      | leaf | node2 _ _ | group _ _ _ => rw [validateDupPlanFlat.eq_def, validatePlan.eq_def],
    fun plan f bs args k hΓ _ hmV hlr hwf ih => by
      obtain ⟨ha, hk⟩ := wf_call hwf
      dup_val_step plan, validateDupPlanFlat.eq_def, validatePlan.eq_def,
        denoteArgs_isSome_of_checkArgs hΓ ha,
        (exact ih (outVD' := 0) (outLD' := 0) _ (CtxTypes.push (Tup.units bs) hΓ)
          (trieCtxMatch_insertTupEnv hmV _) hlr hk),
    fun plan c t e hΓ _ hmV _ hwf iht ihe => by
      obtain ⟨hc, ht, he⟩ := wf_jnz hwf
      obtain ⟨_, hc'⟩ := Option.isSome_iff_exists.1 (denoteArg_isSome_of_checkArg hΓ hc)
      dsimp only [denote]; rw [hc']; dsimp only
      cases plan with
      | node2 pt pe =>
        rw [validateDupPlanFlat.eq_def, validatePlan.eq_def]; dsimp only; rw [iht pt ht, ihe pe he]
      | leaf | node1 _ | group _ _ _ => rw [validateDupPlanFlat.eq_def, validatePlan.eq_def],
    fun plan j args hΓ _ hmV hlr hwf => by
      obtain ⟨hj, ha⟩ := wf_jump hwf
      obtain ⟨_, hlk, hres⟩ := lookupL_eq_some_resolveLabel hlr.1 hlr.2 hj
      obtain ⟨_, hargs⟩ := Option.isSome_iff_exists.1 (denoteArgs_isSome_of_checkArgs hΓ ha)
      dsimp only [denote]; rw [hlk, hargs]; dsimp only
      cases plan with
      | leaf => rw [validateDupPlanFlat.eq_def, validatePlan.eq_def]; dsimp only; rw [hres]; rfl
      | node1 _ | node2 _ _ | group _ _ _ => rw [validateDupPlanFlat.eq_def, validatePlan.eq_def],
    dup_val_ret validateDupPlanFlat.eq_def, validatePlan.eq_def,
    dup_val_exit validateDupPlanFlat.eq_def, validatePlan.eq_def,
    fun plan _ _ _ _ _ => by
      dsimp only [denote]; cases plan <;> rw [validateDupPlanFlat.eq_def, validatePlan.eq_def],
    @fun sig _ Δ _ _ inVD outVD inLD outLD inVE inLE plan bodies k _ hΔ _ hlr hwf ihB ihK => by
      obtain ⟨hb, hk⟩ := wf_group hwf
      dsimp only [denote]
      cases plan with
      | group acts pbs pk =>
        rw [validateDupPlanFlat.eq_def, validatePlan.eq_def]; dsimp only
        have hNo := ihB (outLD' := outLD) (acts, pbs)
          (ctxTypes_pushTup_rev (noDupBoolTup acts sig) hΔ)
          ⟨ctxTypes_pushTup_rev (noDupBoolTup acts sig) hlr.1,
           trieCtxMatch_insertTupEnv hlr.2 (noDupBoolTup acts sig)⟩ hb
        have hYes := ihB (outLD' := outLD) (acts, pbs)
          (ctxTypes_pushTup_rev (dupBoolTup acts sig) hΔ)
          ⟨ctxTypes_pushTup_rev (dupBoolTup acts sig) hlr.1,
           trieCtxMatch_insertTupEnv hlr.2 (dupBoolTup acts sig)⟩ hb
        have hk' := ihK (outLD' := outLD) pk (ctxTypes_pushTup_rev (dupBoolTup acts sig) hΔ)
          ⟨ctxTypes_pushTup_rev (dupBoolTup acts sig) hlr.1,
           trieCtxMatch_insertTupEnv hlr.2 (dupBoolTup acts sig)⟩ hk
        rw [hNo.1, hYes.2, hk']
      | leaf | node1 _ | node2 _ _ => rw [validateDupPlanFlat.eq_def, validatePlan.eq_def],
    fun ⟨acts, pbs⟩ _ _ _ _ _ => ⟨by
      rw [validateDupBlocksFlat.eq_def, validateDupBlocks.eq_def]
      cases pbs <;> cases acts <;> rfl,
    by
      rw [validateKeptBlocksFlat.eq_def, validateKeptBlocks.eq_def]
      cases pbs <;> cases acts <;> rfl⟩,
    fun ⟨acts, pbs⟩ b bs hΓ _ hmV hlr hwf ih ihs => by
      obtain ⟨hb, hbs⟩ := wf_cons hwf
      cases pbs with
      | nil =>
        exact ⟨by
            rw [validateDupBlocksFlat.eq_def, validateDupBlocks.eq_def]
            cases acts <;> simp only <;> rfl,
          by
            rw [validateKeptBlocksFlat.eq_def, validateKeptBlocks.eq_def]
            cases acts <;> simp only <;> rfl⟩
      | cons pb pbs' =>
        cases acts with
        | nil =>
          exact ⟨by rw [validateDupBlocksFlat.eq_def, validateDupBlocks.eq_def]; rfl,
                 by rw [validateKeptBlocksFlat.eq_def, validateKeptBlocks.eq_def]; rfl⟩
        | cons a acts' =>
          have htl := ihs (acts', pbs') hbs
          have hhd := ih (outVD' := 0) (outLD' := 0) (inLD' := _) (inLE' := _) pb
            (ctxTypes_pushTup_rev (Tup.units _) hΓ) (trieCtxMatch_insertTupEnv hmV _) hlr hb
          refine ⟨?_, ?_⟩
          · rw [validateDupBlocksFlat.eq_def, denoteB.eq_def, validateDupBlocks.eq_def]; simp only
            cases a <;> simp only [htl.1, hhd]
          · rw [validateKeptBlocksFlat.eq_def, denoteB.eq_def, validateKeptBlocks.eq_def]; simp only
            cases a <;> simp only [htl.2, hhd]⟩

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
    dsimp only [tupFreshWith, toArgTup]; rw [tupFreshVar_eq_toArgTup ts xs (n + 1)]

private theorem rewriteKeptBlocks_nil_eq {rs : List Ty} :
    (acts : List DupAct) → {sig : List (List Ty)} →
    (bs : Blocks (Arg K) (DupL K KL rs) rs sig) → (ovd old : Nat) →
    toTBlocks (rewriteKeptBlocks acts .nil bs) ovd old =
      mkHltTBlocks (filterActsSig acts sig)
  | _, _, .nil, _, _ => by rw [rewriteKeptBlocks.eq_def]; rfl
  | [], _ :: _, .cons _ _, _, _ => by rw [rewriteKeptBlocks.eq_def]; rfl
  | .keep :: acts', _ :: _, .cons _ bs, ovd, old => by
    rw [rewriteKeptBlocks.eq_def]; dsimp only [filterActsSig, toTBlocks, toTFlat, mkHltTBlocks]
    exact congrArg (TBlocks.cons .hlt) (rewriteKeptBlocks_nil_eq acts' bs ovd old)
  | .dup :: acts', _ :: _, .cons _ bs, ovd, old
  | .drop :: acts', _ :: _, .cons _ bs, ovd, old => by
    rw [rewriteKeptBlocks.eq_def]; dsimp only [filterActsSig]
    exact rewriteKeptBlocks_nil_eq acts' bs ovd old

local macro "dup_rw_step" p:Lean.Parser.Tactic.elimTarget "," eq1:Lean.Parser.Tactic.rwRule ","
    eq2:Lean.Parser.Tactic.rwRule "," rw_a:Lean.Parser.Tactic.rwRule "," ctor:term ","
    next:tactic : tactic => `(tactic| (
  dsimp only [denote]; rw [$rw_a]; dsimp only
  cases $p with
  | node1 _ =>
    rw [$eq1, $eq2]; dsimp only [flattenOp, toTFlat]
    refine congrArg $ctor ?_; $next
  | leaf | node2 _ _ | group _ _ _ => rw [$eq1, $eq2]; rfl))

local macro "dup_rw_ret" eq1:Lean.Parser.Tactic.rwRule ","
    eq2:Lean.Parser.Tactic.rwRule : term =>
  `(fun plan vs' hΓ _ hmV _ hwf => by
    dsimp only [denote]; rw [denoteArgs_eq_some_resolveEnvArgs hΓ hmV vs' hwf]; dsimp only
    cases plan <;> rw [$eq1, $eq2] <;> rfl)

local macro "dup_rw_exit" eq1:Lean.Parser.Tactic.rwRule ","
    eq2:Lean.Parser.Tactic.rwRule : term =>
  `(fun plan _ args hΓ _ hmV _ hwf => by
    dsimp only [denote]; rw [denoteArgs_eq_some_resolveEnvArgs hΓ hmV args hwf]; dsimp only
    cases plan <;> rw [$eq1, $eq2] <;> rfl)

private theorem rewriteDupFlat_both {rs : List Ty} :
    (∀ (tf : TFlat rs) {Γ Δ vs ls inVD outVD inLD outLD inVE inLE} (plan : DupPlan),
      CtxTypes Γ vs → CtxTypes Δ ls → TrieCtxMatch inVD inVE vs →
      TrieRelMatch (fun _ => DupLFlatMatch (rs := rs)) inLD inLE ls → tf.wfCheck Γ Δ = true →
      toTFlat (rewriteExpr plan (denote (Arg K) (DupL K KL rs) tf vs ls)) outVD outLD =
        rewriteDupFlat plan inVD inVE inLD inLE outVD outLD tf) ∧
    (∀ {sig : List (List Ty)} (tb : TBlocks rs sig)
      {Γ Δ vs ls inVD outVD inLD outLD inVE inLE} (sp : List DupAct × DupPlanB),
      CtxTypes Γ vs → CtxTypes Δ ls → TrieCtxMatch inVD inVE vs →
      TrieRelMatch (fun _ => DupLFlatMatch (rs := rs)) inLD inLE ls → tb.wfCheck Γ Δ = true →
      (∀ (lsF : Tup (PlanLFlat rs) sig) (lsP : Tup (DupL K KL rs) sig),
        TRel (fun _ => DupLFlatMatch (rs := rs)) lsF lsP →
        TRel (fun _ => DupLFlatMatch (rs := rs))
          (buildDupLabelsFlat sp.1 sp.2 inVD inVE inLD inLE tb lsF)
          (buildDupLabels sp.1 sp.2 (denoteB (Arg K) (DupL K KL rs) tb vs ls) lsP)) ∧
      toTBlocks (rewriteKeptBlocks sp.1 sp.2 (denoteB (Arg K) (DupL K KL rs) tb vs ls))
          outVD outLD =
        rewriteDupKeptBlocksFlat sp.1 sp.2 inVD inVE inLD inLE outVD outLD tb) := by
  refine relSim_mutual ⟨
    @fun ts _ Δ _ _ inVD outVD _ _ inVE _ plan op k hΓ _ hmV hmL hwf ih => by
      obtain ⟨ha, hk⟩ := wf_let hwf
      dup_rw_step plan, rewriteExpr.eq_def, rewriteDupFlat.eq_def,
        denoteArgs_eq_some_resolveEnvArgs hΓ hmV op.args ha, TFlat.let_ _, {
        have hfresh := trieCtxMatch_insertFreshWith (fun _ _ od => Arg.var od) hmV ts outVD
        rw [mkFreshVar_eq_toArgTup] at hfresh
        exact ih _ (ctxTypes_pushTup_rev _ hΓ) hfresh hmL hk },
    @fun _ Δ _ _ _ outVD _ _ _ _ plan t a k hΓ _ hmV hmL hwf ih => by
      obtain ⟨ha, hk⟩ := wf_load hwf
      dup_rw_step plan, rewriteExpr.eq_def, rewriteDupFlat.eq_def,
        denoteArg_eq_some_resolveEnvArg hΓ hmV a ha, TFlat.load t _,
        (exact ih _ (.cons hΓ) (hmV.cons t (Arg.var outVD)) hmL hk),
    fun plan v a k hΓ _ hmV hmL hwf ih => by
      obtain ⟨hv, ha, hk⟩ := wf_store hwf
      dsimp only [denote]
      rw [denoteArg_eq_some_resolveEnvArg hΓ hmV v hv,
        denoteArg_eq_some_resolveEnvArg hΓ hmV a ha]; dsimp only
      cases plan with
      | node1 _ =>
        rw [rewriteExpr.eq_def, rewriteDupFlat.eq_def]; dsimp only [toTFlat]
        exact congrArg (TFlat.store _ _) (ih _ hΓ hmV hmL hk)
      | leaf | node2 _ _ | group _ _ _ => rw [rewriteExpr.eq_def, rewriteDupFlat.eq_def]; rfl,
    @fun _ _ Δ _ _ inVD outVD _ _ inVE _ plan f bs args k hΓ _ hmV hmL hwf ih => by
      obtain ⟨ha, hk⟩ := wf_call hwf
      dup_rw_step plan, rewriteExpr.eq_def, rewriteDupFlat.eq_def,
        denoteArgs_eq_some_resolveEnvArgs hΓ hmV args ha, TFlat.call f bs _, {
        have hfresh := trieCtxMatch_insertFreshWith (fun _ _ od => Arg.var od) hmV bs outVD
        rw [mkFreshVar_eq_toArgTup] at hfresh
        exact ih _ (ctxTypes_pushTup_rev _ hΓ) hfresh hmL hk },
    fun plan c t e hΓ _ hmV _ hwf iht ihe => by
      obtain ⟨hc, ht, he⟩ := wf_jnz hwf
      dsimp only [denote]; rw [denoteArg_eq_some_resolveEnvArg hΓ hmV c hc]; dsimp only
      cases plan with
      | node2 pt pe =>
        rw [rewriteExpr.eq_def, rewriteDupFlat.eq_def]; dsimp only [toTFlat]
        rw [iht pt ht, ihe pe he]
      | leaf | node1 _ | group _ _ _ => rw [rewriteExpr.eq_def, rewriteDupFlat.eq_def]; rfl,
    fun plan j args hΓ hΔ hmV hmL hwf => by
      obtain ⟨hj, ha⟩ := wf_jump hwf
      obtain ⟨w₁, w₂, hres, hlk, hm⟩ := TrieRelMatch.resolveLabel_rel hΔ hmL hj
      dsimp only [denote]; rw [hlk, denoteArgs_eq_some_resolveEnvArgs hΓ hmV args ha]; dsimp only
      cases plan with
      | leaf =>
        rw [rewriteExpr.eq_def, rewriteDupFlat.eq_def]; dsimp only; rw [hres]
        cases w₁ with
        | keep l₁ =>
          cases w₂ with
          | keep l₂ => cases hm; rfl
          | dead | dup _ => exact False.elim hm
        | dead => cases w₂ with | keep _ | dup _ => exact False.elim hm | dead => rfl
        | splice _ =>
          cases w₂ with
          | keep _ | dead => exact False.elim hm
          | dup _ => exact (hm _ _ _).symm
      | node1 _ | node2 _ _ | group _ _ _ => rw [rewriteExpr.eq_def, rewriteDupFlat.eq_def]; rfl,
    dup_rw_ret rewriteExpr.eq_def, rewriteDupFlat.eq_def,
    dup_rw_exit rewriteExpr.eq_def, rewriteDupFlat.eq_def,
    fun plan _ _ _ _ _ => by
      dsimp only [denote]; cases plan <;> rw [rewriteExpr.eq_def, rewriteDupFlat.eq_def] <;> rfl,
    @fun sig _ Δ vs ls inVD outVD inLD outLD inVE inLE plan bodies k _ hΔ _ hmL hwf ihB ihK => by
      obtain ⟨hb, hk⟩ := wf_group hwf
      dsimp only [denote]
      cases plan with
      | group acts pbs pk =>
        rw [rewriteExpr.eq_def, rewriteDupFlat.eq_def]; dsimp only
        by_cases hkeep : acts.any (· == .keep) = true
        · simp only [hkeep, ↓reduceIte, toTFlat]
          have hno := expandDupKeepFlat_match (rs := rs) acts sig
            (Tup.levels (filterActsSig acts sig) outLD)
          have hdup := (ihB (outLD' := outLD) (acts, pbs) (ctxTypes_pushTup_rev _ hΔ)
            (TrieRelMatch.pushTup hno hmL) hb).1 _ _ hno
          have hΔ' := ctxTypes_pushTup_rev (buildDupLabels acts pbs
            (denoteB (Arg K) (DupL K KL rs) bodies vs
              (pushTup (expandKeepLabels acts sig (Tup.levels (filterActsSig acts sig) outLD)) ls))
            (expandKeepLabels acts sig (Tup.levels (filterActsSig acts sig) outLD))) hΔ
          have hb' := (ihB (outLD' := outLD + (filterActsSig acts sig).length) (acts, pbs)
            hΔ' (TrieRelMatch.pushTup hdup hmL) hb).2
          have hk' := ihK (outLD' := outLD + (filterActsSig acts sig).length) pk
            hΔ' (TrieRelMatch.pushTup hdup hmL) hk
          rw [hb', hk']
        · simp only [hkeep, Bool.false_eq_true, ↓reduceIte]
          have hno := deadTupDup_match (rs := rs) sig
          have hdup := (ihB (outLD' := outLD) (acts, pbs) (ctxTypes_pushTup_rev _ hΔ)
            (TrieRelMatch.pushTup hno hmL) hb).1 _ _ hno
          have hΔ' := ctxTypes_pushTup_rev (buildDupLabels acts pbs
            (denoteB (Arg K) (DupL K KL rs) bodies vs (pushTup (TailDup.deadTup sig) ls))
            (TailDup.deadTup sig)) hΔ
          exact ihK (outLD' := outLD) pk hΔ' (TrieRelMatch.pushTup hdup hmL) hk
      | leaf | node1 _ | node2 _ _ => rw [rewriteExpr.eq_def, rewriteDupFlat.eq_def]; rfl,
    fun ⟨acts, pbs⟩ _ _ _ _ _ => ⟨by
      intro lsF lsP hrel
      cases lsF; cases lsP; cases hrel
      rw [buildDupLabelsFlat.eq_def, denoteB.eq_def, buildDupLabels.eq_def]; exact .nil,
    by rw [rewriteDupKeptBlocksFlat.eq_def, denoteB.eq_def, rewriteKeptBlocks.eq_def]; rfl⟩,
    @fun ts sig' _ Δ _ _ inVD outVD inLD outLD inVE inLE ⟨acts, pbs⟩ b bs
        hΓ _ hmV hmL hwf ih ihs => by
      obtain ⟨hb, hbs⟩ := wf_cons hwf
      refine ⟨?_, ?_⟩
      · intro lsF lsP hrel
        rcases hrel with ⟨⟩ | ⟨hl, hls⟩
        rw [buildDupLabelsFlat.eq_def, denoteB.eq_def, buildDupLabels.eq_def]; simp only
        cases acts with
        | nil => simp only; exact .cons trivial (deadTupDup_match sig')
        | cons a acts' =>
          cases pbs with
          | nil => simp only; exact .cons trivial (deadTupDup_match sig')
          | cons pb pbs' =>
            have htl := (ihs (acts', pbs') hbs).1 _ _ hls
            cases a with
            | dup =>
              refine .cons (fun ovd old args => ?_) htl
              exact (ih (outVD' := ovd) (outLD' := old) pb
                (ctxTypes_pushTup_rev args hΓ) (trieCtxMatch_insertTupEnv hmV args) hmL hb).symm
            | keep => exact .cons hl htl
            | drop => exact .cons trivial htl
      · cases acts with
        | nil => rw [rewriteDupKeptBlocksFlat.eq_def, denoteB.eq_def, rewriteKeptBlocks.eq_def]; rfl
        | cons a acts' =>
          cases pbs with
          | nil =>
            rw [rewriteDupKeptBlocksFlat.eq_def, denoteB.eq_def]
            exact rewriteKeptBlocks_nil_eq (a :: acts') (.cons _ _) outVD outLD
          | cons pb pbs' =>
            rw [rewriteDupKeptBlocksFlat.eq_def, denoteB.eq_def, rewriteKeptBlocks.eq_def]
            cases a with
            | keep =>
              dsimp only [toTBlocks, filterActsSig]
              have hfresh := trieCtxMatch_insertFreshWith (fun _ _ od => Arg.var od) hmV ts outVD
              rw [mkFreshVar_eq_toArgTup] at hfresh
              exact congr (congrArg TBlocks.cons
                (ih (outVD' := outVD + ts.length) (outLD' := outLD) pb
                  (ctxTypes_pushTup_rev _ hΓ) hfresh hmL hb))
                ((ihs (acts', pbs') hbs).2)
            | dup | drop => exact (ihs (acts', pbs') hbs).2⟩

/-! ## 3. Public `tailDupFlat` Equivalence Theorems -/

/-- `tailDupWithPlanFlat as plan tf = reifyFunc (Func.tailDupWithPlan plan (denoteFunc tf))`
under `wfCheck = true`. -/
theorem tailDupWithPlanFlat_eq {as rs : List Ty} (plan : DupPlan) (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    tailDupWithPlanFlat as plan tf =
      reifyFunc (Func.tailDupWithPlan plan (denoteFunc (as := as) tf)) := by
  dsimp only [tailDupWithPlanFlat, Func.tailDupWithPlan, denoteFunc, reifyFunc]
  have hmU := trieCtxMatch_insertTupEnv (W := UnitV) .empty (Tup.units as)
  rw [Nat.zero_add] at hmU
  have hval := validateDupPlanFlat_both.1 tf plan
    (ctxTypes_pushTup_rev (Tup.units as) .nil) .nil hmU ⟨.nil, TrieCtxMatch.empty⟩ hwf
    (_outVD := 0) (_outLD := 0)
  rw [hval]
  by_cases hval' : validatePlan plan (denote UnitV BoolL tf (pushTup (Tup.units as) []) []) = true
  · simp only [hval', ↓reduceIte]
    have hmV := trieCtxMatch_initEnv (fun x _ => Arg.var x) as
    rw [tupFreshVar_eq_toArgTup] at hmV
    have hrw := rewriteDupFlat_both.1 tf plan (ctxTypes_pushTup_rev _ .nil) .nil hmV
      (TrieRelMatch.empty (fun _ => DupLFlatMatch (rs := rs))) hwf (outVD := as.length) (outLD := 0)
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
  · exact ⟨tailDupWithPlanFlat_eq _ tf hwf, rfl⟩
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
      Func.tailDup (denoteFunc (as := as) tf) cfg :=
  denoteFunc_of_flat_eq (fun hf => Func.tailDup_wf hf cfg) tf hwf (tailDupFlat_eq tf cfg hwf)

/-- `tailDupFlat` preserves `wfCheck`. -/
theorem tailDupFlat_wfCheck {as rs : List Ty} (tf : TFlat rs) (cfg : TailDupConfig := {})
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    (tailDupFlat as tf cfg).wfCheck (pushTypes as []) [] = true :=
  wfCheck_of_flat_eq (fun hf => Func.tailDup_wf hf cfg) tf hwf (tailDupFlat_eq tf cfg hwf)

/-- `(tailDupFlatFn f cfg).toFn = ⟨f.name, f.as, f.rs, Func.tailDup f.toFn.body cfg⟩` under
`wfCheck = true`. -/
theorem tailDupFlatFn_toFn (f : TFlatFn) (cfg : TailDupConfig := {}) (hwf : f.wfCheck = true) :
    (tailDupFlatFn f cfg).toFn = ⟨f.name, f.as, f.rs, Func.tailDup f.toFn.body cfg⟩ :=
  fn_toFn_of_denoteFunc (flatBody := fun as _ tf => tailDupFlat as tf cfg)
    (fun tf h => denoteFunc_tailDupFlat tf cfg h) f hwf

/-- `tailDupFlatFn` preserves `TFlatFn.wfCheck`. -/
theorem tailDupFlatFn_wfCheck (f : TFlatFn) (cfg : TailDupConfig := {}) (hwf : f.wfCheck = true) :
    (tailDupFlatFn f cfg).wfCheck = true :=
  tailDupFlat_wfCheck f.body cfg hwf

end OptFlatBranch
end LeanQbe.T