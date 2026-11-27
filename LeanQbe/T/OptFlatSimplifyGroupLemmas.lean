module

public import LeanQbe.T.OptFlatSimplifyGroup
import LeanQbe.T.FlatDirectLemmas
import LeanQbe.T.PassFlatKit
import LeanQbe.T.OptFlatSimKit
import LeanQbe.T.SimplifyGroupPlanLemmas

/-!
# Join-Group Simplification Equivalence Proofs (`OptFlatSimplifyGroupLemmas`)

Proves exact `=` correspondence (`std3` axioms only) between the native `TFlat` pass
`OptFlatSimplifyGroup.{simplifyGroupWithPlanFlat, simplifyGroupPlanFlat}` and
`Func.{simplifyGroupWithPlan, simplifyGroupPlan}`:

* `OptFlatSimplifyGroup.simplifyGroupWithPlanFlat_eq`
* `OptFlatSimplifyGroup.denoteFunc_simplifyGroupWithPlanFlat`
* `OptFlatSimplifyGroup.simplifyGroupWithPlanFlat_wfCheck`
* `OptFlatSimplifyGroup.simplifyGroupPlanFlat_eq`
* `OptFlatSimplifyGroup.denoteFunc_simplifyGroupPlanFlat`
* `OptFlatSimplifyGroup.simplifyGroupPlanFlat_wfCheck`
* `OptFlatSimplifyGroup.simplifyGroupPlanFlatFn_toFn` / `simplifyGroupPlanFlatFn_wfCheck`
-/

set_option autoImplicit false

public section

namespace LeanQbe.T
namespace OptFlatSimplifyGroup

open OptFlatPlanKit
open OptFlatSimKit
open SgpImpl

/-! ## 1. `validatePlanFlat` Equivalence -/

local macro "sgp_val_step" p:Lean.Parser.Tactic.elimTarget "," eq1:Lean.Parser.Tactic.rwRule ","
    eq2:Lean.Parser.Tactic.rwRule "," e:term "," next:tactic : tactic => `(tactic| (
  obtain ⟨_, h⟩ := Option.isSome_iff_exists.1 $e
  dsimp only [denote]; rw [h]; dsimp only
  cases $p with
  | node1 _ => rw [$eq1, $eq2]; dsimp only; $next
  | leaf | node2 _ _ | group _ _ _ => rw [$eq1, $eq2]))

local macro "sgp_val_ret" eq1:Lean.Parser.Tactic.rwRule ","
    eq2:Lean.Parser.Tactic.rwRule : term =>
  `(fun plan vs' hΓ _ _ _ hwf => by
    obtain ⟨_, h⟩ := Option.isSome_iff_exists.1 (denoteArgs_isSome_of_checkArgs hΓ hwf)
    dsimp only [denote]; rw [h]; dsimp only
    cases plan <;> rw [$eq1, $eq2])

local macro "sgp_val_exit" eq1:Lean.Parser.Tactic.rwRule ","
    eq2:Lean.Parser.Tactic.rwRule : term =>
  `(fun plan _ args hΓ _ _ _ hwf => by
    obtain ⟨_, h⟩ := Option.isSome_iff_exists.1 (denoteArgs_isSome_of_checkArgs hΓ hwf)
    dsimp only [denote]; rw [h]; dsimp only
    cases plan <;> rw [$eq1, $eq2])

private theorem validatePlanFlat_both {rs : List Ty} :
    (∀ (tf : TFlat rs) {Γ Δ vs ls inVD} {_outVD : Nat} {inLD} {_outLD : Nat} {inVE inLE}
      (plan : SimpPlan),
      CtxTypes Γ vs → CtxTypes Δ ls → TrieCtxMatch inVD inVE vs →
      (CtxTypes Δ ls ∧ TrieCtxMatch inLD inLE ls) → tf.wfCheck Γ Δ = true →
      validatePlanFlat plan inLD inLE tf = validatePlan plan (denote UnitV BoolL tf vs ls)) ∧
    (∀ {sig : List (List Ty)} (tb : TBlocks rs sig)
      {Γ Δ vs ls inVD} {_outVD : Nat} {inLD} {_outLD : Nat} {inVE inLE}
      (sp : (Nat × List Bool) × SimpPlanB),
      CtxTypes Γ vs → CtxTypes Δ ls → TrieCtxMatch inVD inVE vs →
      (CtxTypes Δ ls ∧ TrieCtxMatch inLD inLE ls) → tb.wfCheck Γ Δ = true →
      validateSpliceBlockFlat sp.1.1 sp.2 inLD inLE tb =
        validateSpliceBlock sp.1.1 sp.2 (denoteB UnitV BoolL tb vs ls) ∧
      validateFilteredBlocksFlat sp.1.2 sp.2 inLD inLE tb =
        validateFilteredBlocks sp.1.2 sp.2 (denoteB UnitV BoolL tb vs ls)) := by
  refine relSim_mutual
    (LR := fun Δ inLD inLE ls => CtxTypes Δ ls ∧ TrieCtxMatch inLD inLE ls) ⟨
    fun plan op k hΓ _ hmV hlr hwf ih => by
      obtain ⟨ha, hk⟩ := wf_let hwf
      sgp_val_step plan, validatePlanFlat.eq_def, validatePlan.eq_def,
        denoteArgs_isSome_of_checkArgs hΓ ha,
        (exact ih (outVD' := 0) (outLD' := 0) _ (CtxTypes.push (Tup.units _) hΓ)
          (trieCtxMatch_insertTupEnv hmV _) hlr hk),
    fun plan t a k hΓ _ hmV hlr hwf ih => by
      obtain ⟨ha, hk⟩ := wf_load hwf
      sgp_val_step plan, validatePlanFlat.eq_def, validatePlan.eq_def,
        denoteArg_isSome_of_checkArg hΓ ha,
        (exact ih (outVD' := 0) (outLD' := 0) _ (.cons hΓ) (hmV.cons t ()) hlr hk),
    fun plan v a k hΓ _ hmV hlr hwf ih => by
      obtain ⟨hv, ha, hk⟩ := wf_store hwf
      obtain ⟨_, hv'⟩ := Option.isSome_iff_exists.1 (denoteArg_isSome_of_checkArg hΓ hv)
      obtain ⟨_, ha'⟩ := Option.isSome_iff_exists.1 (denoteArg_isSome_of_checkArg hΓ ha)
      dsimp only [denote]; rw [hv', ha']; dsimp only
      cases plan with
      | node1 _ =>
        rw [validatePlanFlat.eq_def, validatePlan.eq_def]; dsimp only
        exact ih (outVD' := 0) (outLD' := 0) _ hΓ hmV hlr hk
      | leaf | node2 _ _ | group _ _ _ => rw [validatePlanFlat.eq_def, validatePlan.eq_def],
    fun plan f bs args k hΓ _ hmV hlr hwf ih => by
      obtain ⟨ha, hk⟩ := wf_call hwf
      sgp_val_step plan, validatePlanFlat.eq_def, validatePlan.eq_def,
        denoteArgs_isSome_of_checkArgs hΓ ha,
        (exact ih (outVD' := 0) (outLD' := 0) _ (CtxTypes.push (Tup.units bs) hΓ)
          (trieCtxMatch_insertTupEnv hmV _) hlr hk),
    fun plan c t e hΓ _ hmV _ hwf iht ihe => by
      obtain ⟨hc, ht, he⟩ := wf_jnz hwf
      obtain ⟨_, hc'⟩ := Option.isSome_iff_exists.1 (denoteArg_isSome_of_checkArg hΓ hc)
      dsimp only [denote]; rw [hc']; dsimp only
      cases plan with
      | node2 pt pe =>
        rw [validatePlanFlat.eq_def, validatePlan.eq_def]; dsimp only; rw [iht pt ht, ihe pe he]
      | leaf | node1 _ | group _ _ _ => rw [validatePlanFlat.eq_def, validatePlan.eq_def],
    fun plan j args hΓ _ _ hlr hwf => by
      obtain ⟨hj, ha⟩ := wf_jump hwf
      obtain ⟨_, hlk, hres⟩ := lookupL_eq_some_resolveLabel hlr.1 hlr.2 hj
      obtain ⟨_, hargs⟩ := Option.isSome_iff_exists.1 (denoteArgs_isSome_of_checkArgs hΓ ha)
      dsimp only [denote]; rw [hlk, hargs]; dsimp only
      cases plan with
      | leaf => rw [validatePlanFlat.eq_def, validatePlan.eq_def]; dsimp only; rw [hres]; rfl
      | node1 _ | node2 _ _ | group _ _ _ => rw [validatePlanFlat.eq_def, validatePlan.eq_def],
    sgp_val_ret validatePlanFlat.eq_def, validatePlan.eq_def,
    sgp_val_exit validatePlanFlat.eq_def, validatePlan.eq_def,
    fun plan _ _ _ _ _ => by
      dsimp only [denote]; cases plan <;> rw [validatePlanFlat.eq_def, validatePlan.eq_def],
    @fun sig _ Δ _ _ inVD outVD inLD outLD inVE inLE plan bodies k _ hΔ _ hlr hwf ihB ihK => by
      obtain ⟨hb, hk⟩ := wf_group hwf
      dsimp only [denote]
      cases plan with
      | group act pbs pk =>
        cases act with
        | unwrap =>
          rw [validatePlanFlat.eq_def, validatePlan.eq_def]; dsimp only
          exact ihK (outLD' := outLD) pk (ctxTypes_pushTup_rev (allFalse sig) hΔ)
            ⟨ctxTypes_pushTup_rev (allFalse sig) hlr.1,
             trieCtxMatch_insertTupEnv hlr.2 (allFalse sig)⟩ hk
        | splice idx =>
          rw [validatePlanFlat.eq_def, validatePlan.eq_def]; dsimp only
          have hsp := (ihB (outLD' := outLD) ((idx, []), pbs)
            (ctxTypes_pushTup_rev (allFalse sig) hΔ)
            ⟨ctxTypes_pushTup_rev (allFalse sig) hlr.1,
             trieCtxMatch_insertTupEnv hlr.2 (allFalse sig)⟩ hb).1
          have hk' := ihK (outLD' := outLD) pk (ctxTypes_pushTup_rev (oneTrue idx sig) hΔ)
            ⟨ctxTypes_pushTup_rev (oneTrue idx sig) hlr.1,
             trieCtxMatch_insertTupEnv hlr.2 (oneTrue idx sig)⟩ hk
          rw [hsp, hk']
        | filter keep =>
          rw [validatePlanFlat.eq_def, validatePlan.eq_def]; dsimp only
          have hfl := (ihB (outLD' := outLD) ((0, keep), pbs)
            (ctxTypes_pushTup_rev (boolTup keep sig) hΔ)
            ⟨ctxTypes_pushTup_rev (boolTup keep sig) hlr.1,
             trieCtxMatch_insertTupEnv hlr.2 (boolTup keep sig)⟩ hb).2
          have hk' := ihK (outLD' := outLD) pk (ctxTypes_pushTup_rev (boolTup keep sig) hΔ)
            ⟨ctxTypes_pushTup_rev (boolTup keep sig) hlr.1,
             trieCtxMatch_insertTupEnv hlr.2 (boolTup keep sig)⟩ hk
          rw [hfl, hk']
      | leaf | node1 _ | node2 _ _ => rw [validatePlanFlat.eq_def, validatePlan.eq_def],
    fun ⟨⟨idx, ks⟩, pbs⟩ _ _ _ _ _ => ⟨by
      rw [validateSpliceBlockFlat.eq_def, validateSpliceBlock.eq_def]; rfl,
    by
      rw [validateFilteredBlocksFlat.eq_def, validateFilteredBlocks.eq_def]
      cases pbs <;> cases ks <;> rfl⟩,
    fun ⟨⟨idx, ks⟩, pbs⟩ b bs hΓ _ hmV hlr hwf ih ihs => by
      obtain ⟨hb, hbs⟩ := wf_cons hwf
      cases pbs with
      | nil =>
        exact ⟨by
            rw [validateSpliceBlockFlat.eq_def, denoteB.eq_def, validateSpliceBlock.eq_def]
            cases idx <;> simp only <;> rfl,
          by
            rw [validateFilteredBlocksFlat.eq_def, denoteB.eq_def, validateFilteredBlocks.eq_def]
            cases ks <;> simp only <;> rfl⟩
      | cons pb pbs' =>
        refine ⟨?_, ?_⟩
        · rw [validateSpliceBlockFlat.eq_def, denoteB.eq_def, validateSpliceBlock.eq_def]
          cases idx with
          | zero =>
            exact ih (outVD' := 0) (outLD' := 0) (inLD' := _) (inLE' := _) pb
              (ctxTypes_pushTup_rev (Tup.units _) hΓ) (trieCtxMatch_insertTupEnv hmV _) hlr hb
          | succ idx' => exact (ihs ((idx', ks), pbs') hbs).1
        · rw [validateFilteredBlocksFlat.eq_def, denoteB.eq_def, validateFilteredBlocks.eq_def]
          cases ks with
          | nil => rfl
          | cons k ks' =>
            have htl := (ihs ((idx, ks'), pbs') hbs).2
            cases k
            · exact htl
            · have hhd := ih (outVD' := 0) (outLD' := 0) (inLD' := _) (inLE' := _) pb
                (ctxTypes_pushTup_rev (Tup.units _) hΓ) (trieCtxMatch_insertTupEnv hmV _) hlr hb
              simp only [hhd, htl]⟩

/-! ## 2. `rewriteExprFlat` Equivalence -/

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

private theorem rewriteFilteredBlocks_nil_eq {rs : List Ty} :
    (ks : List Bool) → {sig : List (List Ty)} →
    (bs : Blocks (Arg K) (PlanL K KL rs) rs sig) → (ovd old : Nat) →
    toTBlocks (rewriteFilteredBlocks ks .nil bs) ovd old =
      mkHltTBlocks (filterSig ks sig)
  | _, _, .nil, _, _ => by rw [rewriteFilteredBlocks.eq_def]; rfl
  | [], _ :: _, .cons _ _, _, _ => by rw [rewriteFilteredBlocks.eq_def]; rfl
  | true :: ks', _ :: _, .cons _ bs, ovd, old => by
    rw [rewriteFilteredBlocks.eq_def]; dsimp only [filterSig, toTBlocks, toTFlat, mkHltTBlocks]
    exact congrArg (TBlocks.cons .hlt) (rewriteFilteredBlocks_nil_eq ks' bs ovd old)
  | false :: ks', _ :: _, .cons _ bs, ovd, old => by
    rw [rewriteFilteredBlocks.eq_def]; dsimp only [filterSig]
    exact rewriteFilteredBlocks_nil_eq ks' bs ovd old

local macro "sgp_rw_step" p:Lean.Parser.Tactic.elimTarget "," eq1:Lean.Parser.Tactic.rwRule ","
    eq2:Lean.Parser.Tactic.rwRule "," rw_a:Lean.Parser.Tactic.rwRule "," ctor:term ","
    next:tactic : tactic => `(tactic| (
  dsimp only [denote]; rw [$rw_a]; dsimp only
  cases $p with
  | node1 _ =>
    rw [$eq1, $eq2]; dsimp only [flattenOp, toTFlat]
    refine congrArg $ctor ?_; $next
  | leaf | node2 _ _ | group _ _ _ => rw [$eq1, $eq2]; rfl))

local macro "sgp_rw_ret" eq1:Lean.Parser.Tactic.rwRule ","
    eq2:Lean.Parser.Tactic.rwRule : term =>
  `(fun plan vs' hΓ _ hmV _ hwf => by
    dsimp only [denote]; rw [denoteArgs_eq_some_resolveEnvArgs hΓ hmV vs' hwf]; dsimp only
    cases plan <;> rw [$eq1, $eq2] <;> rfl)

local macro "sgp_rw_exit" eq1:Lean.Parser.Tactic.rwRule ","
    eq2:Lean.Parser.Tactic.rwRule : term =>
  `(fun plan _ args hΓ _ hmV _ hwf => by
    dsimp only [denote]; rw [denoteArgs_eq_some_resolveEnvArgs hΓ hmV args hwf]; dsimp only
    cases plan <;> rw [$eq1, $eq2] <;> rfl)

private theorem rewriteExprFlat_both {rs : List Ty} :
    (∀ (tf : TFlat rs) {Γ Δ vs ls inVD outVD inLD outLD inVE inLE} (plan : SimpPlan),
      CtxTypes Γ vs → CtxTypes Δ ls → TrieCtxMatch inVD inVE vs →
      TrieRelMatch (fun _ => PlanLFlatMatch (rs := rs)) inLD inLE ls → tf.wfCheck Γ Δ = true →
      toTFlat (rewriteExpr plan (denote (Arg K) (PlanL K KL rs) tf vs ls)) outVD outLD =
        rewriteExprFlat plan inVD inVE inLD inLE outVD outLD tf) ∧
    (∀ {sig : List (List Ty)} (tb : TBlocks rs sig)
      {Γ Δ vs ls inVD outVD inLD outLD inVE inLE} (sp : (Nat × List Bool) × SimpPlanB),
      CtxTypes Γ vs → CtxTypes Δ ls → TrieCtxMatch inVD inVE vs →
      TrieRelMatch (fun _ => PlanLFlatMatch (rs := rs)) inLD inLE ls → tb.wfCheck Γ Δ = true →
      TRel (fun _ => PlanLFlatMatch (rs := rs))
        (rewriteSpliceLabelsFlat sp.1.1 sp.2 inVD inVE inLD inLE tb)
        (rewriteSpliceLabels sp.1.1 sp.2 (denoteB (Arg K) (PlanL K KL rs) tb vs ls)) ∧
      toTBlocks (rewriteFilteredBlocks sp.1.2 sp.2 (denoteB (Arg K) (PlanL K KL rs) tb vs ls))
          outVD outLD =
        rewriteFilteredBlocksFlat sp.1.2 sp.2 inVD inVE inLD inLE outVD outLD tb) := by
  refine relSim_mutual ⟨
    @fun ts _ Δ _ _ inVD outVD _ _ inVE _ plan op k hΓ _ hmV hmL hwf ih => by
      obtain ⟨ha, hk⟩ := wf_let hwf
      sgp_rw_step plan, rewriteExpr.eq_def, rewriteExprFlat.eq_def,
        denoteArgs_eq_some_resolveEnvArgs hΓ hmV op.args ha, TFlat.let_ _, {
        have hfresh := trieCtxMatch_insertFreshWith (fun _ _ od => Arg.var od) hmV ts outVD
        rw [mkFreshVar_eq_toArgTup] at hfresh
        exact ih _ (ctxTypes_pushTup_rev _ hΓ) hfresh hmL hk },
    @fun _ Δ _ _ _ outVD _ _ _ _ plan t a k hΓ _ hmV hmL hwf ih => by
      obtain ⟨ha, hk⟩ := wf_load hwf
      sgp_rw_step plan, rewriteExpr.eq_def, rewriteExprFlat.eq_def,
        denoteArg_eq_some_resolveEnvArg hΓ hmV a ha, TFlat.load t _,
        (exact ih _ (.cons hΓ) (hmV.cons t (Arg.var outVD)) hmL hk),
    fun plan v a k hΓ _ hmV hmL hwf ih => by
      obtain ⟨hv, ha, hk⟩ := wf_store hwf
      dsimp only [denote]
      rw [denoteArg_eq_some_resolveEnvArg hΓ hmV v hv,
        denoteArg_eq_some_resolveEnvArg hΓ hmV a ha]; dsimp only
      cases plan with
      | node1 _ =>
        rw [rewriteExpr.eq_def, rewriteExprFlat.eq_def]; dsimp only [toTFlat]
        exact congrArg (TFlat.store _ _) (ih _ hΓ hmV hmL hk)
      | leaf | node2 _ _ | group _ _ _ => rw [rewriteExpr.eq_def, rewriteExprFlat.eq_def]; rfl,
    @fun _ _ Δ _ _ inVD outVD _ _ inVE _ plan f bs args k hΓ _ hmV hmL hwf ih => by
      obtain ⟨ha, hk⟩ := wf_call hwf
      sgp_rw_step plan, rewriteExpr.eq_def, rewriteExprFlat.eq_def,
        denoteArgs_eq_some_resolveEnvArgs hΓ hmV args ha, TFlat.call f bs _, {
        have hfresh := trieCtxMatch_insertFreshWith (fun _ _ od => Arg.var od) hmV bs outVD
        rw [mkFreshVar_eq_toArgTup] at hfresh
        exact ih _ (ctxTypes_pushTup_rev _ hΓ) hfresh hmL hk },
    fun plan c t e hΓ _ hmV _ hwf iht ihe => by
      obtain ⟨hc, ht, he⟩ := wf_jnz hwf
      dsimp only [denote]; rw [denoteArg_eq_some_resolveEnvArg hΓ hmV c hc]; dsimp only
      cases plan with
      | node2 pt pe =>
        rw [rewriteExpr.eq_def, rewriteExprFlat.eq_def]; dsimp only [toTFlat]
        rw [iht pt ht, ihe pe he]
      | leaf | node1 _ | group _ _ _ => rw [rewriteExpr.eq_def, rewriteExprFlat.eq_def]; rfl,
    fun plan j args hΓ hΔ hmV hmL hwf => by
      obtain ⟨hj, ha⟩ := wf_jump hwf
      obtain ⟨w₁, w₂, hres, hlk, hm⟩ := TrieRelMatch.resolveLabel_rel hΔ hmL hj
      dsimp only [denote]; rw [hlk, denoteArgs_eq_some_resolveEnvArgs hΓ hmV args ha]; dsimp only
      cases plan with
      | leaf =>
        rw [rewriteExpr.eq_def, rewriteExprFlat.eq_def]; dsimp only; rw [hres]
        cases w₁ with
        | keep l₁ =>
          cases w₂ with
          | keep l₂ => cases hm; rfl
          | dead | splice _ => exact False.elim hm
        | dead => cases w₂ with | keep _ | splice _ => exact False.elim hm | dead => rfl
        | splice _ =>
          cases w₂ with
          | keep _ | dead => exact False.elim hm
          | splice _ => exact (hm _ _ _).symm
      | node1 _ | node2 _ _ | group _ _ _ => rw [rewriteExpr.eq_def, rewriteExprFlat.eq_def]; rfl,
    sgp_rw_ret rewriteExpr.eq_def, rewriteExprFlat.eq_def,
    sgp_rw_exit rewriteExpr.eq_def, rewriteExprFlat.eq_def,
    fun plan _ _ _ _ _ => by
      dsimp only [denote]; cases plan <;> rw [rewriteExpr.eq_def, rewriteExprFlat.eq_def] <;> rfl,
    @fun sig _ Δ vs ls inVD outVD inLD outLD inVE inLE plan bodies k _ hΔ _ hmL hwf ihB ihK => by
      obtain ⟨hb, hk⟩ := wf_group hwf
      dsimp only [denote]
      cases plan with
      | group act pbs pk =>
        cases act with
        | unwrap =>
          rw [rewriteExpr.eq_def, rewriteExprFlat.eq_def]; dsimp only
          have hdead := deadTupFlat_match (rs := rs) sig
          exact ihK (outLD' := outLD) pk (ctxTypes_pushTup_rev _ hΔ)
            (TrieRelMatch.pushTup hdead hmL) hk
        | splice idx =>
          rw [rewriteExpr.eq_def, rewriteExprFlat.eq_def]; dsimp only
          have hdead := deadTupFlat_match (rs := rs) sig
          have hsp := (ihB (outLD' := outLD) ((idx, []), pbs) (ctxTypes_pushTup_rev _ hΔ)
            (TrieRelMatch.pushTup hdead hmL) hb).1
          have hΔ' := ctxTypes_pushTup_rev
            (rewriteSpliceLabels idx pbs (denoteB (Arg K) (PlanL K KL rs) bodies vs
              (pushTup (deadTup sig) ls))) hΔ
          exact ihK (outLD' := outLD) pk hΔ' (TrieRelMatch.pushTup hsp hmL) hk
        | filter keep =>
          rw [rewriteExpr.eq_def, rewriteExprFlat.eq_def]; dsimp only [toTFlat]
          have hkeep := expandKeepFlat_match (rs := rs) keep sig
            (Tup.levels (filterSig keep sig) outLD)
          have hΔ' := ctxTypes_pushTup_rev
            (expandKeepLabels keep sig (Tup.levels (filterSig keep sig) outLD)) hΔ
          have hb' := (ihB (outLD' := outLD + (filterSig keep sig).length) ((0, keep), pbs)
            hΔ' (TrieRelMatch.pushTup hkeep hmL) hb).2
          have hk' := ihK (outLD' := outLD + (filterSig keep sig).length) pk
            hΔ' (TrieRelMatch.pushTup hkeep hmL) hk
          rw [hb', hk']
      | leaf | node1 _ | node2 _ _ => rw [rewriteExpr.eq_def, rewriteExprFlat.eq_def]; rfl,
    fun ⟨⟨_, ks⟩, _⟩ _ _ _ _ _ => ⟨by
      rw [rewriteSpliceLabelsFlat.eq_def, denoteB.eq_def, rewriteSpliceLabels.eq_def]; exact .nil,
    by
      rw [rewriteFilteredBlocksFlat.eq_def, denoteB.eq_def, rewriteFilteredBlocks.eq_def]; rfl⟩,
    @fun ts sig' _ Δ _ _ inVD outVD inLD outLD inVE inLE ⟨⟨idx, ks⟩, pbs⟩ b bs
        hΓ _ hmV hmL hwf ih ihs => by
      obtain ⟨hb, hbs⟩ := wf_cons hwf
      refine ⟨?_, ?_⟩
      · cases pbs with
        | nil =>
          rw [rewriteSpliceLabelsFlat.eq_def, denoteB.eq_def, rewriteSpliceLabels.eq_def]
          cases idx <;> exact .cons trivial (deadTupFlat_match sig')
        | cons pb pbs' =>
          rw [rewriteSpliceLabelsFlat.eq_def, denoteB.eq_def, rewriteSpliceLabels.eq_def]
          cases idx with
          | zero =>
            refine .cons (fun ovd old args => ?_) (deadTupFlat_match sig')
            exact (ih (outVD' := ovd) (outLD' := old) pb
              (ctxTypes_pushTup_rev args hΓ) (trieCtxMatch_insertTupEnv hmV args) hmL hb).symm
          | succ idx' => exact .cons trivial (ihs ((idx', ks), pbs') hbs).1
      · cases ks with
        | nil =>
          rw [rewriteFilteredBlocksFlat.eq_def, denoteB.eq_def, rewriteFilteredBlocks.eq_def]; rfl
        | cons k ks' =>
          cases pbs with
          | nil =>
            rw [rewriteFilteredBlocksFlat.eq_def, denoteB.eq_def]
            exact rewriteFilteredBlocks_nil_eq (k :: ks') (.cons _ _) outVD outLD
          | cons pb pbs' =>
            rw [rewriteFilteredBlocksFlat.eq_def, denoteB.eq_def, rewriteFilteredBlocks.eq_def]
            cases k with
            | true =>
              dsimp only [toTBlocks, filterSig]
              have hfresh := trieCtxMatch_insertFreshWith (fun _ _ od => Arg.var od) hmV ts outVD
              rw [mkFreshVar_eq_toArgTup] at hfresh
              exact congr (congrArg TBlocks.cons
                (ih (outVD' := outVD + ts.length) (outLD' := outLD) pb
                  (ctxTypes_pushTup_rev _ hΓ) hfresh hmL hb))
                ((ihs ((idx, ks'), pbs') hbs).2)
            | false => exact (ihs ((idx, ks'), pbs') hbs).2⟩

/-! ## 3. Public `simplifyGroupWithPlanFlat` and `simplifyGroupPlanFlat` Theorems -/

/-- `simplifyGroupWithPlanFlat as plan tf = reifyFunc (Func.simplifyGroupWithPlan plan (denoteFunc tf))`
under `wfCheck = true`. -/
theorem simplifyGroupWithPlanFlat_eq {as rs : List Ty} (plan : SimpPlan) (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    simplifyGroupWithPlanFlat as plan tf =
      reifyFunc (Func.simplifyGroupWithPlan plan (denoteFunc (as := as) tf)) := by
  dsimp only [simplifyGroupWithPlanFlat, Func.simplifyGroupWithPlan, denoteFunc, reifyFunc]
  have hmU := trieCtxMatch_insertTupEnv (W := UnitV) .empty (Tup.units as)
  rw [Nat.zero_add] at hmU
  have hval := validatePlanFlat_both.1 tf plan
    (ctxTypes_pushTup_rev (Tup.units as) .nil) .nil hmU ⟨.nil, TrieCtxMatch.empty⟩ hwf
    (_outVD := 0) (_outLD := 0)
  rw [hval]
  by_cases hval' : validatePlan plan (denote UnitV BoolL tf (pushTup (Tup.units as) []) []) = true
  · simp only [hval', ↓reduceIte]
    have hmV := trieCtxMatch_initEnv (fun x _ => Arg.var x) as
    rw [tupFreshVar_eq_toArgTup] at hmV
    have hrw := rewriteExprFlat_both.1 tf plan (ctxTypes_pushTup_rev _ .nil) .nil hmV
      (TrieRelMatch.empty (fun _ => PlanLFlatMatch (rs := rs))) hwf
      (outVD := as.length) (outLD := 0)
    exact hrw.symm
  · simp only [hval', Bool.false_eq_true, ↓reduceIte]
    exact (reifyFunc_denoteFunc_eq tf hwf).symm

/-- `denoteFunc (simplifyGroupWithPlanFlat as plan tf) =
Func.simplifyGroupWithPlan plan (denoteFunc tf)` under `wfCheck = true`. -/
theorem denoteFunc_simplifyGroupWithPlanFlat {as rs : List Ty} (plan : SimpPlan) (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    denoteFunc (as := as) (simplifyGroupWithPlanFlat as plan tf) =
      Func.simplifyGroupWithPlan plan (denoteFunc (as := as) tf) :=
  denoteFunc_of_flat_eq (fun hf => Func.simplifyGroupWithPlan_wf plan hf) tf hwf
    (simplifyGroupWithPlanFlat_eq plan tf hwf)

/-- `simplifyGroupWithPlanFlat` preserves `wfCheck`. -/
theorem simplifyGroupWithPlanFlat_wfCheck {as rs : List Ty} (plan : SimpPlan) (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    (simplifyGroupWithPlanFlat as plan tf).wfCheck (pushTypes as []) [] = true :=
  wfCheck_of_flat_eq (fun hf => Func.simplifyGroupWithPlan_wf plan hf) tf hwf
    (simplifyGroupWithPlanFlat_eq plan tf hwf)

/-- `simplifyGroupPlanFlat as tf = reifyFunc (Func.simplifyGroupPlan (denoteFunc tf))` under
`wfCheck = true`. -/
theorem simplifyGroupPlanFlat_eq {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    simplifyGroupPlanFlat as tf =
      reifyFunc (Func.simplifyGroupPlan (denoteFunc (as := as) tf)) := by
  dsimp only [simplifyGroupPlanFlat, Func.simplifyGroupPlan]
  rw [reifyFunc_denoteFunc_eq tf hwf]
  split
  · exact simplifyGroupWithPlanFlat_eq _ tf hwf
  · exact (reifyFunc_denoteFunc_eq tf hwf).symm

flat_pass_corollaries simplifyGroupPlanFlat, Func.simplifyGroupPlan,
  Func.simplifyGroupPlan_wf, simplifyGroupPlanFlat_eq,
  denoteFunc_simplifyGroupPlanFlat, simplifyGroupPlanFlat_wfCheck,
  simplifyGroupPlanFlatFn, simplifyGroupPlanFlatFn_toFn, simplifyGroupPlanFlatFn_wfCheck

end OptFlatSimplifyGroup
end LeanQbe.T
