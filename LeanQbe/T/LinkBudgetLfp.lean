module

public import LeanQbe.T.LinkLfp
import LeanQbe.T.WPLemmas
import LeanQbe.T.AbiLemmas

/-!
# Stack-Budget-Indexed `BudgetEnv.lfp` Fixed-Point Core (`PR-B1`)

Purely target-independent, additive fixed-point semantics over `BudgetEnv := Nat → Env`,
pairing `maxFrame` and `minEntry` directly on `BudgetFn` (zero external `frameOf : Sym → Nat`
tables in core semantics):
* `BudgetEnv`, `BudgetEnv.le`, `BudgetEnv.mono`, `BudgetEnv.lfp`, `BudgetEnv.lfp_le`,
  `BudgetEnv.lfp_closed`, `BudgetEnv.lfp_pre`, `BudgetEnv.lfp_post`, `BudgetEnv.lfp_fix`,
  `BudgetEnv.lfp_mono`.
* `BudgetEnv.IsBudgetMono`, `BudgetEnv.PreservesBudgetMono`, `BudgetEnv.lfp_budget_mono`,
  `BudgetEnv.belowEnv`, `BudgetEnv.lfp_wf`, `BudgetEnv.BudgetLocal`,
  `BudgetEnv.lfp_le_of_prefix_below`.
* `BudgetFn` (`toFn`, `maxFrame`, `minEntry := maxFrame`), `BudgetModule`, `BudgetEnv.extStep`,
  `BudgetEnv.sccStep`, `BudgetEnv.callSlot`, `BudgetEnv.tailSlot`, `BudgetEnv.mkSccOp`
  (parameterized by two-slot `evalFn` for trivial Stage-2 `wpSplit` generalization),
  `BudgetEnv.sccOp`, `BudgetEnv.semScc`, `BudgetEnv.semSccWith`, and `BudgetEnv.lfp_wf_mkSccOp`.
* Non-tail well-founded reduction `lfp_eq_wfRec_of_noTail`, legacy `ModuleOk` embedding
  `moduleOk_embeds_into_budget_semScc`, and single-shot `Target.FnSpec` machine bridge
  (`LowerOk`, `semScc_le_mach_single_shot`, `targetMachEnv`, `budget_semScc_to_target_fnSpec`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T

/-! ## 1. Stack-Budget-Indexed Environments and Knaster–Tarski `BudgetEnv.lfp` -/

/-- Stack-budget-indexed semantic environment: `G sb` holds contracts valid at entry
stack headroom `sb : Nat` (in bytes). -/
abbrev BudgetEnv : Type := Nat → Env

namespace BudgetEnv

/-- Pointwise implication ordering across all stack-budget levels `sb : Nat`. -/
@[expose] def le (G₁ G₂ : BudgetEnv) : Prop :=
  ∀ sb, Env.le (G₁ sb) (G₂ sb)

theorem le_refl (G : BudgetEnv) : le G G :=
  fun sb => Env.le_refl (G sb)

theorem le_trans {G₁ G₂ G₃ : BudgetEnv} (h12 : le G₁ G₂) (h23 : le G₂ G₃) : le G₁ G₃ :=
  fun sb => Env.le_trans (h12 sb) (h23 sb)

/-- Bottom `BudgetEnv`. -/
@[expose] def bot : BudgetEnv :=
  fun _ _ _ _ _ _ _ _ => False

/-- Top `BudgetEnv`. -/
@[expose] def top : BudgetEnv :=
  fun _ _ _ _ _ _ _ _ => True

theorem bot_le (G : BudgetEnv) : le bot G :=
  fun _ _ _ _ _ _ _ _ h => False.elim h

/-- Lift a budget-independent `Env` into a constant `BudgetEnv`. -/
@[expose] def const (Γ : Env) : BudgetEnv :=
  fun _ => Γ

/-- Monotonicity of a transformer `Φ : BudgetEnv → BudgetEnv` with respect to `BudgetEnv.le`. -/
@[expose] def mono (Φ : BudgetEnv → BudgetEnv) : Prop :=
  ∀ ⦃G₁ G₂ : BudgetEnv⦄, le G₁ G₂ → le (Φ G₁) (Φ G₂)

/-- Impredicative Knaster–Tarski least fixed point of `Φ : BudgetEnv → BudgetEnv`. -/
@[expose] def lfp (Φ : BudgetEnv → BudgetEnv) : BudgetEnv :=
  fun sb f as bs xs m Q X =>
    ∀ G : BudgetEnv, le (Φ G) G → G sb f as bs xs m Q X

/-- Elimination: `BudgetEnv.lfp Φ` lies below every pre-fixpoint `G` (`Φ G ≤ G`). -/
theorem lfp_le {Φ : BudgetEnv → BudgetEnv} {G : BudgetEnv} (h : le (Φ G) G) :
    le (lfp Φ) G :=
  fun _ _ _ _ _ _ _ _ hlfp => hlfp _ h

/-- Pre-fixpoint closure property: for monotone `Φ`, `Φ (lfp Φ) ≤ lfp Φ`. -/
theorem lfp_closed {Φ : BudgetEnv → BudgetEnv} (hm : mono Φ) :
    le (Φ (lfp Φ)) (lfp Φ) :=
  fun sb f as bs xs m Q X hΦ _ hG =>
    hG sb f as bs xs m Q X (hm (lfp_le hG) sb f as bs xs m Q X hΦ)

/-- Alias for `BudgetEnv.lfp_closed` matching `Env.lfp_pre`. -/
theorem lfp_pre {Φ : BudgetEnv → BudgetEnv} (hm : mono Φ) :
    le (Φ (lfp Φ)) (lfp Φ) :=
  lfp_closed hm

/-- Post-fixpoint property: for monotone `Φ`, `lfp Φ ≤ Φ (lfp Φ)`. -/
theorem lfp_post {Φ : BudgetEnv → BudgetEnv} (hm : mono Φ) :
    le (lfp Φ) (Φ (lfp Φ)) :=
  lfp_le (hm (lfp_closed hm))

/-- Fixed-point equation `BudgetEnv.lfp Φ = Φ (BudgetEnv.lfp Φ)` for monotone `Φ`. -/
theorem lfp_fix {Φ : BudgetEnv → BudgetEnv} (hm : mono Φ) :
    lfp Φ = Φ (lfp Φ) := by
  funext sb f as bs xs m Q X
  exact propext
    ⟨fun h => lfp_post hm sb f as bs xs m Q X h,
     fun h => lfp_closed hm sb f as bs xs m Q X h⟩

/-- Monotonicity of `BudgetEnv.lfp` in the operator `Φ`. -/
theorem lfp_mono {Φ₁ Φ₂ : BudgetEnv → BudgetEnv} (hm₂ : mono Φ₂)
    (hle : ∀ G, le (Φ₁ G) (Φ₂ G)) :
    le (lfp Φ₁) (lfp Φ₂) :=
  lfp_le (le_trans (hle (lfp Φ₂)) (lfp_closed hm₂))

/-! ## 2. Budget Monotonicity, Well-Founded Introduction, and Prefix Locality -/

/-- A `BudgetEnv` is budget-monotone when larger stack budgets include all smaller ones. -/
@[expose] def IsBudgetMono (G : BudgetEnv) : Prop :=
  ∀ ⦃sb₁ sb₂ : Nat⦄, sb₁ ≤ sb₂ → Env.le (G sb₁) (G sb₂)

/-- An operator `Φ` preserves budget monotonicity. -/
@[expose] def PreservesBudgetMono (Φ : BudgetEnv → BudgetEnv) : Prop :=
  ∀ ⦃G : BudgetEnv⦄, IsBudgetMono G → IsBudgetMono (Φ G)

/-- `BudgetEnv.lfp Φ` is budget-monotone whenever `Φ` is monotone and preserves it. -/
theorem lfp_budget_mono {Φ : BudgetEnv → BudgetEnv}
    (hm : mono Φ) (hbm : PreservesBudgetMono Φ) :
    IsBudgetMono (lfp Φ) := by
  let H : BudgetEnv := fun sb f as bs xs m Q X =>
    ∀ sb', sb ≤ sb' → lfp Φ sb' f as bs xs m Q X
  have hH_bm : IsBudgetMono H := fun _ _ hle _ _ _ _ _ _ _ h sb' hs =>
    h sb' (Nat.le_trans hle hs)
  have hH_le : le H (lfp Φ) := fun sb _ _ _ _ _ _ _ h => h sb (Nat.le_refl sb)
  have hΦH_bm : IsBudgetMono (Φ H) := hbm hH_bm
  have hΦH_pre : le (Φ H) H := fun sb f as bs xs m Q X hΦ sb' hle =>
    lfp_closed hm sb' f as bs xs m Q X
      (hm hH_le sb' f as bs xs m Q X (hΦH_bm hle f as bs xs m Q X hΦ))
  have hlfp_le_H : le (lfp Φ) H := lfp_le hΦH_pre
  intro sb₁ sb₂ hle f as bs xs m Q X h
  exact hlfp_le_H sb₁ f as bs xs m Q X h sb₂ hle

/-- Budget-filtered supremum strictly below `i` along `lt`, collecting predecessors `j` with
`lt j i ∧ reqBudget j ≤ sb`. -/
@[expose] def belowEnv {ι : Type} (lt : ι → ι → Prop) (reqBudget : ι → Nat)
    (P : ι → Env) (i : ι) : BudgetEnv :=
  fun sb f as bs xs m Q X =>
    ∃ j, lt j i ∧ reqBudget j ≤ sb ∧ P j f as bs xs m Q X

/-- Well-founded `(ι, lt)` introduction rule for `BudgetEnv.lfp`. -/
theorem lfp_wf {Φ : BudgetEnv → BudgetEnv} (hm : mono Φ)
    {ι : Type} {lt : ι → ι → Prop} (hwf : WellFounded lt)
    (reqBudget : ι → Nat) (P : ι → Env)
    (hstep : ∀ i sb, reqBudget i ≤ sb → Env.le (P i) (Φ (belowEnv lt reqBudget P i) sb)) :
    ∀ i sb, reqBudget i ≤ sb → Env.le (P i) (lfp Φ sb) := by
  intro i
  induction i using hwf.induction with
  | h i ih =>
      intro sb hsb f as bs xs m Q X hP
      have hbelow : le (belowEnv lt reqBudget P i) (lfp Φ) := by
        rintro sb' f' as' bs' xs' m' Q' X' ⟨j, hlt, hj, hPj⟩
        exact ih j hlt sb' hj f' as' bs' xs' m' Q' X' hPj
      exact lfp_closed hm sb f as bs xs m Q X
        (hm hbelow sb f as bs xs m Q X (hstep i sb hsb f as bs xs m Q X hP))

theorem edge_nonTail_budget {reqi reqj cost sb : Nat}
    (hsb : reqi ≤ sb) (hedge : reqj ≤ reqi - cost) :
    reqj ≤ sb - cost :=
  Nat.le_trans hedge (Nat.sub_le_sub_right hsb cost)

theorem edge_tail_budget {reqi reqj sb : Nat}
    (hsb : reqi ≤ sb) (hedge : reqj ≤ reqi) :
    reqj ≤ sb :=
  Nat.le_trans hedge hsb

/-- Prefix locality: `Φ G sb` only depends on `G` at stack budgets `sb' ≤ sb`. -/
@[expose] def BudgetLocal (Φ : BudgetEnv → BudgetEnv) : Prop :=
  ∀ (sb : Nat) ⦃G₁ G₂ : BudgetEnv⦄,
    (∀ sb', sb' ≤ sb → Env.le (G₁ sb') (G₂ sb')) → Env.le (Φ G₁ sb) (Φ G₂ sb)

/-- Single-shot bounded pre-fixpoint induction for prefix-local operators: any `Mach` closed
under `Φ` on `[0, cap]` bounds `lfp Φ` on `[0, cap]` without global bounds above `cap`. -/
theorem lfp_le_of_prefix_below {Φ : BudgetEnv → BudgetEnv} (hloc : BudgetLocal Φ)
    (cap : Nat) (Mach : BudgetEnv)
    (hpre : ∀ sb, sb ≤ cap → Env.le (Φ Mach sb) (Mach sb)) :
    ∀ sb, sb ≤ cap → Env.le (lfp Φ sb) (Mach sb) := by
  let Gcap : BudgetEnv := fun sb => if sb ≤ cap then Mach sb else top sb
  have hGcap : le (Φ Gcap) Gcap := by
    intro sb f as bs xs m Q X hΦ
    by_cases hle : sb ≤ cap
    · simp only [Gcap, hle, ↓reduceIte]
      have hag : ∀ sb', sb' ≤ sb → Env.le (Gcap sb') (Mach sb') := by
        intro sb' hs
        have hs' : sb' ≤ cap := Nat.le_trans hs hle
        simp only [Gcap, hs', ↓reduceIte]
        exact Env.le_refl _
      exact hpre sb hle f as bs xs m Q X (hloc sb hag f as bs xs m Q X hΦ)
    · simp only [Gcap, hle, ↓reduceIte, top]
  intro sb hle f as bs xs m Q X hlfp
  have h := lfp_le hGcap sb f as bs xs m Q X hlfp
  simpa [Gcap, hle] using h

end BudgetEnv

/-! ## 3. `BudgetFn`, `BudgetModule`, and Split-Slot Semantics (`BudgetEnv.semScc`) -/

/-- A typed IR function paired directly with its per-function stack-frame budget (`maxFrame`
covering `effFrame + raBytes` on target) and per-function entry headroom requirement
(`minEntry`, defaulting to `maxFrame` and absorbing any external callee or exit headroom). -/
structure BudgetFn where
  toFn : Fn
  maxFrame : Nat
  minEntry : Nat := maxFrame

/-- A target-independent module of stack-budgeted functions, externs, and exit symbols. -/
structure BudgetModule where
  fns : List BudgetFn
  externs : List Extern := []
  exits : List Sym := []

/-- Forget stack budgets to obtain the underlying `LeanQbe.T.Module`. -/
@[expose] def BudgetModule.toModule (M : BudgetModule) : Module :=
  { fns := M.fns.map BudgetFn.toFn, externs := M.externs, exits := M.exits }

/-- Function signatures declared in `M.fns`. -/
@[expose] def BudgetModule.fnSigs (M : BudgetModule) : List SigEntry :=
  M.fns.map (fun b => b.toFn.sig)

/-- External signatures declared in `M.externs`. -/
@[expose] def BudgetModule.extSigs (M : BudgetModule) : List SigEntry :=
  M.externs.map Extern.sig

/-- Lift a legacy `Module` by assigning each `Fn` its per-function frame budget. -/
@[expose] def BudgetModule.ofModule (frame : Fn → Nat) (M : Module) : BudgetModule :=
  { fns := M.fns.map (fun fn => { toFn := fn, maxFrame := frame fn }),
    externs := M.externs,
    exits := M.exits }

theorem BudgetModule.ofModule_toModule (frame : Fn → Nat) (M : Module) :
    (BudgetModule.ofModule frame M).toModule = M := by
  cases M
  simp [BudgetModule.ofModule, BudgetModule.toModule, List.map_map, Function.comp_def]

/-- Two-slot body evaluator monotonicity predicate (`Γcall` at non-tail `.call`, `Γtail` at
future Stage-2 `.tailCall`), decoupling fixed-point theory from `Expr.wp` / `wpSplit`. -/
@[expose] def BudgetFn.EvalMono
    (evalFn : Env → Env → (bfn : BudgetFn) → Spec bfn.toFn.as bfn.toFn.rs) : Prop :=
  ∀ (bfn : BudgetFn) ⦃C₁ C₂ T₁ T₂ : Env⦄,
    Env.le C₁ C₂ → Env.le T₁ T₂ →
    ∀ xs m Q X, evalFn C₁ T₁ bfn xs m Q X → evalFn C₂ T₂ bfn xs m Q X

private theorem funcWp_evalMono :
    BudgetFn.EvalMono (fun Γcall _ bfn => Func.wp Γcall bfn.toFn.body) :=
  fun bfn _ _ _ _ hC _ xs m _ _ hwp => wp_env_mono hC (bfn.toFn.body Val Cont xs) m hwp

namespace BudgetEnv

/-- External-only callee environment offering `M.externs` from `Γext`. -/
@[expose] def extStep (M : BudgetModule) (Γext : Env) : Env :=
  fun f as bs xs m Q X =>
    (f, as, bs) ∈ M.extSigs ∧ Γext f as bs xs m Q X

/-- Callee environment for `M` combining internal functions `M.fns` (from `Γ`) and externs
`M.externs` (from `Γext`). -/
@[expose] def sccStep (M : BudgetModule) (Γ Γext : Env) : Env :=
  fun f as bs xs m Q X =>
    ((f, as, bs) ∈ M.fnSigs ∧ Γ f as bs xs m Q X) ∨
    ((f, as, bs) ∈ M.extSigs ∧ Γext f as bs xs m Q X)

theorem extStep_le_sccStep (M : BudgetModule) (Γ Γext : Env) :
    Env.le (extStep M Γext) (sccStep M Γ Γext) :=
  fun _ _ _ _ _ _ _ h => Or.inr h

theorem sccStep_mono {M : BudgetModule} {Γ₁ Γ₂ Γext₁ Γext₂ : Env}
    (hΓ : Env.le Γ₁ Γ₂) (hext : Env.le Γext₁ Γext₂) :
    Env.le (sccStep M Γ₁ Γext₁) (sccStep M Γ₂ Γext₂) := by
  rintro f as bs xs m Q X (⟨hf, h1⟩ | ⟨he, h2⟩)
  · exact Or.inl ⟨hf, hΓ f as bs xs m Q X h1⟩
  · exact Or.inr ⟨he, hext f as bs xs m Q X h2⟩

/-- Non-tail call slot for caller `bfn` at entry budget `sb`: deducts `bfn.maxFrame`. -/
@[expose] def callSlot (M : BudgetModule) (bfn : BudgetFn)
    (Γext G : BudgetEnv) (sb : Nat) : Env :=
  sccStep M (G (sb - bfn.maxFrame)) (Γext (sb - bfn.maxFrame))

/-- Tail-call slot at entry budget `sb`: preserves full entry headroom `sb`. -/
@[expose] def tailSlot (M : BudgetModule) (Γext G : BudgetEnv) (sb : Nat) : Env :=
  sccStep M (G sb) (Γext sb)

/-- Parameterized two-slot module operator over `(callSlot, tailSlot)`, directly reusable
when Stage 2 upgrades `Func.wp` to `Func.wpSplit`. -/
@[expose] def mkSccOp (M : BudgetModule) (Γext : BudgetEnv)
    (evalFn : Env → Env → (bfn : BudgetFn) → Spec bfn.toFn.as bfn.toFn.rs)
    (G : BudgetEnv) (sb : Nat) : Env :=
  fun f as bs xs m Q X =>
    ∃ bfn ∈ M.fns, bfn.toFn.name = f ∧
      ∃ (ha : bfn.toFn.as = as) (hr : bfn.toFn.rs = bs),
        bfn.maxFrame ≤ sb ∧ bfn.minEntry ≤ sb ∧
        evalFn (callSlot M bfn Γext G sb) (tailSlot M Γext G sb)
          bfn (ha ▸ xs) m (hr ▸ Q) X

/-- Stage-1 budget-indexed module operator over `LeanQbe.T.Func.wp` and constant `Γext`. -/
@[expose] def sccOp (M : BudgetModule) (Γext : Env) : BudgetEnv → BudgetEnv :=
  mkSccOp M (const Γext) (fun Γcall _ bfn => Func.wp Γcall bfn.toFn.body)

/-- Canonical budget-indexed least-fixed-point semantics of `M` over constant `Γext`. -/
@[expose] def semScc (M : BudgetModule) (Γext : Env) : BudgetEnv :=
  lfp (sccOp M Γext)

/-- Budget-indexed least-fixed-point semantics of `M` over budget-indexed `Γext`. -/
@[expose] def semSccWith (M : BudgetModule) (Γext : BudgetEnv) : BudgetEnv :=
  lfp (mkSccOp M Γext (fun Γcall _ bfn => Func.wp Γcall bfn.toFn.body))

theorem mkSccOp_mono (M : BudgetModule) (Γext : BudgetEnv)
    {evalFn : Env → Env → (bfn : BudgetFn) → Spec bfn.toFn.as bfn.toFn.rs}
    (hm : BudgetFn.EvalMono evalFn) :
    mono (mkSccOp M Γext evalFn) := by
  rintro G₁ G₂ hle sb f as bs xs m Q X ⟨bfn, hmem, hname, ha, hr, hmax, hmin, heval⟩
  refine ⟨bfn, hmem, hname, ha, hr, hmax, hmin, ?_⟩
  exact hm bfn
    (sccStep_mono (hle (sb - bfn.maxFrame)) (Env.le_refl _))
    (sccStep_mono (hle sb) (Env.le_refl _))
    _ m _ _ heval

theorem mkSccOp_preserves_budgetMono (M : BudgetModule) (Γext : BudgetEnv)
    {evalFn : Env → Env → (bfn : BudgetFn) → Spec bfn.toFn.as bfn.toFn.rs}
    (hm : BudgetFn.EvalMono evalFn) (hext : IsBudgetMono Γext) :
    PreservesBudgetMono (mkSccOp M Γext evalFn) := by
  rintro G hG sb₁ sb₂ hle f as bs xs m Q X ⟨bfn, hmem, hname, ha, hr, hmax, hmin, heval⟩
  refine ⟨bfn, hmem, hname, ha, hr, Nat.le_trans hmax hle, Nat.le_trans hmin hle, ?_⟩
  have hsub : sb₁ - bfn.maxFrame ≤ sb₂ - bfn.maxFrame := Nat.sub_le_sub_right hle _
  exact hm bfn
    (sccStep_mono (hG hsub) (hext hsub))
    (sccStep_mono (hG hle) (hext hle))
    _ m _ _ heval

theorem mkSccOp_budgetLocal (M : BudgetModule) (Γext : BudgetEnv)
    {evalFn : Env → Env → (bfn : BudgetFn) → Spec bfn.toFn.as bfn.toFn.rs}
    (hm : BudgetFn.EvalMono evalFn) :
    BudgetLocal (mkSccOp M Γext evalFn) := by
  rintro sb G₁ G₂ hle f as bs xs m Q X ⟨bfn, hmem, hname, ha, hr, hmax, hmin, heval⟩
  refine ⟨bfn, hmem, hname, ha, hr, hmax, hmin, ?_⟩
  exact hm bfn
    (sccStep_mono (hle (sb - bfn.maxFrame) (Nat.sub_le _ _)) (Env.le_refl _))
    (sccStep_mono (hle sb (Nat.le_refl _)) (Env.le_refl _))
    _ m _ _ heval

theorem sccOp_mono (M : BudgetModule) (Γext : Env) : mono (sccOp M Γext) :=
  mkSccOp_mono M (const Γext) funcWp_evalMono

theorem semScc_fix (M : BudgetModule) (Γext : Env) :
    semScc M Γext = sccOp M Γext (semScc M Γext) :=
  lfp_fix (sccOp_mono M Γext)

theorem semSccWith_fix (M : BudgetModule) (Γext : BudgetEnv) :
    semSccWith M Γext =
      mkSccOp M Γext (fun Γcall _ bfn => Func.wp Γcall bfn.toFn.body) (semSccWith M Γext) :=
  lfp_fix (mkSccOp_mono M Γext funcWp_evalMono)

theorem semScc_budget_mono (M : BudgetModule) (Γext : Env) : IsBudgetMono (semScc M Γext) :=
  lfp_budget_mono (sccOp_mono M Γext)
    (mkSccOp_preserves_budgetMono M (const Γext) funcWp_evalMono
      (fun _ _ _ => Env.le_refl _))

theorem semSccWith_budget_mono (M : BudgetModule) {Γext : BudgetEnv}
    (hext : IsBudgetMono Γext) : IsBudgetMono (semSccWith M Γext) :=
  lfp_budget_mono (mkSccOp_mono M Γext funcWp_evalMono)
    (mkSccOp_preserves_budgetMono M Γext funcWp_evalMono hext)

/-- Well-founded two-slot introduction into `BudgetEnv.lfp (mkSccOp M Γext evalFn)`. -/
theorem lfp_wf_mkSccOp {ι : Type} {lt : ι → ι → Prop} (hwf : WellFounded lt)
    (reqBudget : ι → Nat) (M : BudgetModule) (Γext : BudgetEnv)
    {evalFn : Env → Env → (bfn : BudgetFn) → Spec bfn.toFn.as bfn.toFn.rs}
    (hm : BudgetFn.EvalMono evalFn) (S : ι → Env)
    (hstep : ∀ (i : ι) (sb : Nat), reqBudget i ≤ sb →
      ∀ (bfn : BudgetFn), bfn ∈ M.fns →
        ∀ (Γcall Γtail : Env),
          (∀ j, lt j i → reqBudget j ≤ sb - bfn.maxFrame →
            Env.le (Env.restrict (S j) M.fnSigs) Γcall) →
          Env.le (extStep M (Γext (sb - bfn.maxFrame))) Γcall →
          (∀ j, lt j i → reqBudget j ≤ sb →
            Env.le (Env.restrict (S j) M.fnSigs) Γtail) →
          Env.le (extStep M (Γext sb)) Γtail →
          ∀ xs m Q X,
            S i bfn.toFn.name bfn.toFn.as bfn.toFn.rs xs m Q X →
            bfn.maxFrame ≤ sb ∧ bfn.minEntry ≤ sb ∧ evalFn Γcall Γtail bfn xs m Q X) :
    ∀ i sb, reqBudget i ≤ sb →
      Env.le (Env.restrict (S i) M.fnSigs) (lfp (mkSccOp M Γext evalFn) sb) := by
  let S' : ι → Env := fun i => Env.restrict (S i) M.fnSigs
  refine lfp_wf (mkSccOp_mono M Γext hm) hwf reqBudget S' ?_
  intro i sb hsb f as bs xs m Q X hS'
  obtain ⟨bfn, hmem, hsig⟩ := List.mem_map.mp hS'.1
  rcases Prod.mk.inj hsig with ⟨rfl, hrest⟩
  rcases Prod.mk.inj hrest with ⟨rfl, rfl⟩
  have hres := hstep i sb hsb bfn hmem
    (callSlot M bfn Γext (belowEnv lt reqBudget S' i) sb)
    (tailSlot M Γext (belowEnv lt reqBudget S' i) sb)
    (fun j hlt hreq f' as' bs' xs' m' Q' X' hSj =>
      Or.inl ⟨hSj.1, j, hlt, hreq, hSj⟩)
    (extStep_le_sccStep M _ _)
    (fun j hlt hreq f' as' bs' xs' m' Q' X' hSj =>
      Or.inl ⟨hSj.1, j, hlt, hreq, hSj⟩)
    (extStep_le_sccStep M _ _)
    xs m Q X hS'.2
  exact ⟨bfn, hmem, rfl, rfl, rfl, hres.1, hres.2.1, hres.2.2⟩

end BudgetEnv

/-! ## 4. Non-Tail Well-Founded Reduction (`lfp_eq_wfRec_of_noTail`) -/

mutual
  /-- Syntactic absence of `.call` nodes in `Expr Val Cont rs`. -/
  inductive Expr.NoCall {rs : List Ty} : Expr Val Cont rs → Prop where
    | let_ {ts} (op : Op Val ts) (k : Tup Val ts → Expr Val Cont rs) :
        (∀ r, Expr.NoCall (k r)) → Expr.NoCall (.let_ op k)
    | load t a k : (∀ v, Expr.NoCall (k v)) → Expr.NoCall (.load t a k)
    | store {t} (v : Arg Val t) a k : Expr.NoCall k → Expr.NoCall (.store v a k)
    | jnz c t e : Expr.NoCall t → Expr.NoCall e → Expr.NoCall (.jnz c t e)
    | jump {ts} (j : Cont ts) args : Expr.NoCall (.jump j args)
    | ret vs : Expr.NoCall (.ret vs)
    | exit f {as} (args : Tup (Arg Val) as) : Expr.NoCall (.exit f args)
    | hlt : Expr.NoCall .hlt
    | group {sig} (bodies : Tup Cont sig → Blocks Val Cont rs sig) k :
        (∀ Js, Blocks.NoCall (bodies Js)) → (∀ Js, Expr.NoCall (k Js)) →
        Expr.NoCall (.group bodies k)

  /-- Syntactic absence of `.call` nodes in `Blocks Val Cont rs sig`. -/
  inductive Blocks.NoCall {rs : List Ty} :
      {sig : List (List Ty)} → Blocks Val Cont rs sig → Prop where
    | nil : Blocks.NoCall .nil
    | cons {ts sig} (b : Tup Val ts → Expr Val Cont rs) (bs : Blocks Val Cont rs sig) :
        (∀ xs, Expr.NoCall (b xs)) → Blocks.NoCall bs → Blocks.NoCall (.cons b bs)
end

mutual
  theorem wp_noCall_env_indep (Γ₁ Γ₂ : Env) {rs : List Ty} {Q : Post rs} {X : XPost}
      {e : Expr Val Cont rs} (hnc : e.NoCall) (m : Mem 64) :
      wp Γ₁ Q X e m ↔ wp Γ₂ Q X e m := by
    cases hnc with
    | let_ op k hk =>
        exact ⟨Op.wp_mono (fun r hr => (wp_noCall_env_indep Γ₁ Γ₂ (hk r) m).mp hr),
               Op.wp_mono (fun r hr => (wp_noCall_env_indep Γ₁ Γ₂ (hk r) m).mpr hr)⟩
    | load t a k hk =>
        constructor
        · rintro ⟨v, hv, h⟩
          exact ⟨v, hv, (wp_noCall_env_indep Γ₁ Γ₂ (hk v) m).mp h⟩
        · rintro ⟨v, hv, h⟩
          exact ⟨v, hv, (wp_noCall_env_indep Γ₁ Γ₂ (hk v) m).mpr h⟩
    | store v a k hk =>
        have ih := wp_noCall_env_indep Γ₁ Γ₂ (Q := Q) (X := X) hk (storeMem m _ a.val v.val)
        exact ⟨fun ⟨hs, h⟩ => ⟨hs, ih.mp h⟩, fun ⟨hs, h⟩ => ⟨hs, ih.mpr h⟩⟩
    | jnz c t e ht he =>
        have iht := wp_noCall_env_indep Γ₁ Γ₂ (Q := Q) (X := X) ht m
        have ihe := wp_noCall_env_indep Γ₁ Γ₂ (Q := Q) (X := X) he m
        exact ⟨fun ⟨h1, h2⟩ => ⟨fun hc => iht.mp (h1 hc), fun hc => ihe.mp (h2 hc)⟩,
               fun ⟨h1, h2⟩ => ⟨fun hc => iht.mpr (h1 hc), fun hc => ihe.mpr (h2 hc)⟩⟩
    | jump _ _ => exact Iff.rfl
    | ret _ => exact Iff.rfl
    | exit _ _ => exact Iff.rfl
    | hlt => exact Iff.rfl
    | group bodies k hbs hk =>
        constructor
        · intro h Js hcl
          have hcl' := (closed_noCall_env_indep Γ₁ Γ₂ (Q := Q) (X := X) (hbs Js) Js).mpr hcl
          exact (wp_noCall_env_indep Γ₁ Γ₂ (hk Js) m).mp (h Js hcl')
        · intro h Js hcl
          have hcl' := (closed_noCall_env_indep Γ₁ Γ₂ (Q := Q) (X := X) (hbs Js) Js).mp hcl
          exact (wp_noCall_env_indep Γ₁ Γ₂ (hk Js) m).mpr (h Js hcl')

  theorem closed_noCall_env_indep (Γ₁ Γ₂ : Env) {rs : List Ty} {Q : Post rs} {X : XPost}
      {sig : List (List Ty)} {bs : Blocks Val Cont rs sig} (hnc : bs.NoCall)
      (Js : Tup Cont sig) :
      Closed Γ₁ Q X bs Js ↔ Closed Γ₂ Q X bs Js := by
    cases hnc with
    | nil => exact Iff.rfl
    | cons b rest hb hrest =>
        have ihb := fun xs m => wp_noCall_env_indep Γ₁ Γ₂ (Q := Q) (X := X) (hb xs) m
        have ihr := closed_noCall_env_indep Γ₁ Γ₂ (Q := Q) (X := X) hrest Js.2
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨fun xs m hm => h1 xs m ((ihb xs m).mpr hm), ihr.mp h2⟩
        · rintro ⟨h1, h2⟩; exact ⟨fun xs m hm => h1 xs m ((ihb xs m).mp hm), ihr.mpr h2⟩
end

/-- A `BudgetModule` is strictly tail-call-free with positive call frames when every function
making a `.call` has `maxFrame > 0` (automatically satisfied when `maxFrame ≥ effFrame + ra`).
In Stage 2, this additionally requires `(bfn.toFn.body Val Cont xs).NoTail`. -/
@[expose] def StrictNoTailModule (M : BudgetModule) : Prop :=
  ∀ bfn ∈ M.fns, (∃ xs, ¬ (bfn.toFn.body Val Cont xs).NoCall) → bfn.maxFrame > 0

/-- Pure well-founded recursion step on `sb : Nat` for non-tail `BudgetModule`s. -/
@[expose] noncomputable def wfStep (M : BudgetModule) (Γext : BudgetEnv)
    (sb : Nat) (rec : ∀ sb', sb' < sb → Env) : Env :=
  fun f as bs xs m Q X =>
    ∃ bfn ∈ M.fns, bfn.toFn.name = f ∧
      ∃ (ha : bfn.toFn.as = as) (hr : bfn.toFn.rs = bs),
        bfn.maxFrame ≤ sb ∧ bfn.minEntry ≤ sb ∧
        Func.wp
          (BudgetEnv.sccStep M
            (if hlt : sb - bfn.maxFrame < sb then rec (sb - bfn.maxFrame) hlt else BudgetEnv.bot 0)
            (Γext (sb - bfn.maxFrame)))
          bfn.toFn.body (ha ▸ xs) m (hr ▸ Q) X

/-- Pure `Nat.strongRecOn` semantics for non-tail `BudgetModule`s. -/
@[expose] noncomputable def wfSem (M : BudgetModule) (Γext : BudgetEnv) : BudgetEnv :=
  fun sb => Nat.strongRecOn (motive := fun _ => Env) sb (wfStep M Γext)

theorem wfSem_eq (M : BudgetModule) (Γext : BudgetEnv) (sb : Nat) :
    wfSem M Γext sb = wfStep M Γext sb (fun sb' _ => wfSem M Γext sb') := by
  dsimp [wfSem]
  exact WellFounded.fix_eq Nat.lt_wfRel.wf (fun sb rec => wfStep M Γext sb rec) sb

/-- When every calling function in `M` has `bfn.maxFrame > 0`, `BudgetEnv.semSccWith M Γext`
agrees everywhere with pure `Nat.strongRecOn` well-founded recursion `wfSem M Γext`. -/
theorem lfp_eq_wfRec_of_noTail {M : BudgetModule} (Γext : BudgetEnv)
    (hsnt : StrictNoTailModule M) :
    ∀ sb, BudgetEnv.semSccWith M Γext sb = wfSem M Γext sb := by
  have h_wf_le : ∀ sb, Env.le (wfSem M Γext sb) (BudgetEnv.semSccWith M Γext sb) := by
    intro sb
    induction sb using Nat.strongRecOn with
    | ind sb ih =>
        rw [wfSem_eq]
        intro f as bs xs m Q X ⟨bfn, hmem, hname, ha, hr, hmax, hmin, hwp⟩
        refine BudgetEnv.lfp_closed (BudgetEnv.mkSccOp_mono M Γext funcWp_evalMono)
          sb f as bs xs m Q X ⟨bfn, hmem, hname, ha, hr, hmax, hmin, ?_⟩
        by_cases hnc : (bfn.toFn.body Val Cont (ha ▸ xs)).NoCall
        · exact (wp_noCall_env_indep _ _ hnc m).mp hwp
        · have hpos : bfn.maxFrame > 0 := hsnt bfn hmem ⟨_, hnc⟩
          have hlt : sb - bfn.maxFrame < sb := Nat.sub_lt (Nat.lt_of_lt_of_le hpos hmax) hpos
          have hwp0 : Func.wp
              (BudgetEnv.sccStep M (wfSem M Γext (sb - bfn.maxFrame)) (Γext (sb - bfn.maxFrame)))
              bfn.toFn.body (ha ▸ xs) m (hr ▸ Q) X := by
            simpa [dite_eq_left hlt] using hwp
          exact wp_env_mono
            (BudgetEnv.sccStep_mono (ih (sb - bfn.maxFrame) hlt) (Env.le_refl _)) _ m hwp0
  have h_lfp_le : BudgetEnv.le (BudgetEnv.semSccWith M Γext) (wfSem M Γext) := by
    apply BudgetEnv.lfp_le
    intro sb f as bs xs m Q X ⟨bfn, hmem, hname, ha, hr, hmax, hmin, hwp⟩
    rw [wfSem_eq]
    refine ⟨bfn, hmem, hname, ha, hr, hmax, hmin, ?_⟩
    by_cases hnc : (bfn.toFn.body Val Cont (ha ▸ xs)).NoCall
    · exact (wp_noCall_env_indep _ _ hnc m).mp hwp
    · have hpos : bfn.maxFrame > 0 := hsnt bfn hmem ⟨_, hnc⟩
      have hlt : sb - bfn.maxFrame < sb := Nat.sub_lt (Nat.lt_of_lt_of_le hpos hmax) hpos
      simpa [BudgetEnv.callSlot, dite_eq_left hlt] using hwp
  intro sb
  funext f as bs xs m Q X
  exact propext ⟨fun h => h_lfp_le sb f as bs xs m Q X h,
                 fun h => h_wf_le sb f as bs xs m Q X h⟩

theorem semScc_eq_wfRec_of_noTail {M : BudgetModule} (Γext : Env)
    (hsnt : StrictNoTailModule M) :
    ∀ sb, BudgetEnv.semScc M Γext sb = wfSem M (BudgetEnv.const Γext) sb :=
  lfp_eq_wfRec_of_noTail (BudgetEnv.const Γext) hsnt

/-! ## 5. Legacy `ModuleOk` Compatibility Bridge (`moduleOk_embeds_into_budget_semScc`) -/

/-- Sum of per-function entry headroom requirements across a `BudgetFn` list. -/
@[expose] def BudgetModule.sumEntryBound (bfns : List BudgetFn) : Nat :=
  bfns.foldr (fun bfn acc => max bfn.maxFrame bfn.minEntry + acc) 0

private theorem sumEntryBound_append (xs ys : List BudgetFn) :
    BudgetModule.sumEntryBound (xs ++ ys) =
      BudgetModule.sumEntryBound xs + BudgetModule.sumEntryBound ys := by
  induction xs with
  | nil => simp [BudgetModule.sumEntryBound]
  | cons x xs ih =>
      simp only [BudgetModule.sumEntryBound, List.cons_append, List.foldr_cons] at ih ⊢
      omega

/-- Any verified acyclic `LeanQbe.T.ModuleOk Γ BM.toModule` embeds directly into
`BudgetEnv.semScc BM Γ (BudgetModule.sumEntryBound BM.fns)`, leaving `Spec`, `ModuleOk`,
and `Target.FnSpec` unchanged. -/
theorem moduleOk_embeds_into_budget_semScc {Γ : Env} {BM : BudgetModule}
    (hM : ModuleOk Γ BM.toModule) :
    Env.le (Env.restrict Γ BM.fnSigs)
      (BudgetEnv.semScc BM Γ (BudgetModule.sumEntryBound BM.fns)) := by
  have hprefix : ∀ k, k ≤ BM.fns.length →
      ∀ bfn ∈ BM.fns.take k,
        ∀ xs m Q X, Γ bfn.toFn.name bfn.toFn.as bfn.toFn.rs xs m Q X →
          BudgetEnv.semScc BM Γ (BudgetModule.sumEntryBound (BM.fns.take k))
            bfn.toFn.name bfn.toFn.as bfn.toFn.rs xs m Q X := by
    intro k
    induction k with
    | zero =>
        intro _ bfn hmem
        simp at hmem
    | succ k ih =>
        intro hk bfn hmem xs m Q X hΓ
        have hklt : k < BM.fns.length := Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk
        have htake : BM.fns.take (k + 1) = BM.fns.take k ++ [BM.fns[k]] :=
          List.take_succ_eq_append_getElem hklt
        rw [htake] at hmem ⊢
        rcases List.mem_append.mp hmem with hmem_pre | hmem_cur
        · have ih_pre := ih (Nat.le_of_lt hklt) bfn hmem_pre xs m Q X hΓ
          have hmono_sb : BudgetModule.sumEntryBound (BM.fns.take k) ≤
              BudgetModule.sumEntryBound (BM.fns.take k ++ [BM.fns[k]]) := by
            rw [sumEntryBound_append]
            exact Nat.le_add_right _ _
          exact BudgetEnv.semScc_budget_mono BM Γ hmono_sb
            bfn.toFn.name bfn.toFn.as bfn.toFn.rs xs m Q X ih_pre
        · rw [List.mem_singleton] at hmem_cur
          subst hmem_cur
          let bcur := BM.fns[k]
          let bpre := BM.fns.take k
          let bpost := BM.fns.drop (k + 1)
          have hsplit_b : BM.fns = bpre ++ bcur :: bpost := by
            simp [bpre, bcur, bpost]
          have hsplit : BM.toModule.fns =
              bpre.map BudgetFn.toFn ++ bcur.toFn :: bpost.map BudgetFn.toFn := by
            simpa [BudgetModule.toModule, List.map_append, List.map_cons] using
              congrArg (List.map BudgetFn.toFn) hsplit_b
          have hfnOk := hM.fnsOk (bpre.map BudgetFn.toFn) bcur.toFn
            (bpost.map BudgetFn.toFn) hsplit
          have hwf : bcur.toFn.Wf := hfnOk.1
          have hcalls : bcur.toFn.callsOk
              ((bpre.map BudgetFn.toFn).map Fn.sig ++ BM.toModule.externs.map Extern.sig)
              BM.toModule.exits := hfnOk.2.1
          have hwp : wp Γ Q X (bcur.toFn.body Val Cont xs) m := hfnOk.2.2 xs m Q X hΓ
          let sb := BudgetModule.sumEntryBound (bpre ++ [bcur])
          have hsb_def : sb = BudgetModule.sumEntryBound bpre +
              max bcur.maxFrame bcur.minEntry := by
            dsimp [sb]
            rw [sumEntryBound_append]
            simp [BudgetModule.sumEntryBound]
          have hbound_pre : BudgetModule.sumEntryBound bpre ≤ sb - bcur.maxFrame := by
            rw [hsb_def]; omega
          have hmax_cur : bcur.maxFrame ≤ sb := by rw [hsb_def]; omega
          have hmin_cur : bcur.minEntry ≤ sb := by rw [hsb_def]; omega
          have hwp_call : wp (BudgetEnv.callSlot BM bcur (BudgetEnv.const Γ)
              (BudgetEnv.semScc BM Γ) sb) Q X (bcur.toFn.body Val Cont xs) m := by
            refine wp_env_agree_of_callsOk
              (hwf Val (fun _ => Unit) Cont (fun _ => Unit) xs (Tup.units bcur.toFn.as))
              hcalls ?_ m hwp
            intro g as' bs' hsig xs' m' P' E' hg
            rcases List.mem_append.mp hsig with h_pre | h_ext
            · rcases List.mem_map.mp h_pre with ⟨fn', hfn'_map, hfn'_sig⟩
              rcases List.mem_map.mp hfn'_map with ⟨bfn', hbfn'_mem, rfl⟩
              rcases Prod.mk.inj hfn'_sig with ⟨rfl, hrest⟩
              rcases Prod.mk.inj hrest with ⟨rfl, rfl⟩
              have hsem_pre := ih (Nat.le_of_lt hklt) bfn' hbfn'_mem xs' m' P' E' hg
              have hsem_sub := BudgetEnv.semScc_budget_mono BM Γ hbound_pre
                bfn'.toFn.name bfn'.toFn.as bfn'.toFn.rs xs' m' P' E' hsem_pre
              have hfnsig : bfn'.toFn.sig ∈ BM.fnSigs :=
                List.mem_map.mpr ⟨bfn', List.mem_of_mem_take hbfn'_mem, rfl⟩
              exact Or.inl ⟨hfnsig, hsem_sub⟩
            · exact Or.inr ⟨h_ext, hg⟩
          rw [BudgetEnv.semScc_fix]
          exact ⟨bcur, List.getElem_mem hklt, rfl, rfl, rfl, hmax_cur, hmin_cur, hwp_call⟩
  intro f as bs xs m Q X ⟨hsig, hΓ⟩
  rcases List.mem_map.mp hsig with ⟨bfn, hmem, hsig_eq⟩
  rcases Prod.mk.inj hsig_eq with ⟨rfl, hrest⟩
  rcases Prod.mk.inj hrest with ⟨rfl, rfl⟩
  have hres := hprefix BM.fns.length (Nat.le_refl _) bfn
    (by rw [List.take_length]; exact hmem) xs m Q X hΓ
  simpa [List.take_length] using hres

/-- Corollary lifting `ModuleOk Γ M` via `BudgetModule.ofModule frame M`. -/
theorem moduleOk_embeds_into_budget_semScc_ofModule {Γ : Env} {M : Module} (hM : ModuleOk Γ M)
    (frame : Fn → Nat) :
    Env.le (Env.restrict Γ (M.fns.map Fn.sig))
      (BudgetEnv.semScc (BudgetModule.ofModule frame M) Γ
        (BudgetModule.sumEntryBound (BudgetModule.ofModule frame M).fns)) := by
  have hM' : ModuleOk Γ (BudgetModule.ofModule frame M).toModule := by
    rwa [BudgetModule.ofModule_toModule]
  have hle := moduleOk_embeds_into_budget_semScc hM'
  intro f as bs xs m Q X ⟨hsig, hΓ⟩
  have hsig' : (f, as, bs) ∈ (BudgetModule.ofModule frame M).fnSigs := by
    simpa [BudgetModule.fnSigs, BudgetModule.ofModule, List.map_map, Function.comp_def] using hsig
  exact hle f as bs xs m Q X ⟨hsig', hΓ⟩

/-! ## 6. Single-Shot Machine Pre-Fixpoint & `Target.FnSpec` Bridge -/

/-- Parameterized single-shot machine pre-fixpoint obligation on `[0, cap]`. -/
@[expose] def LowerOkWith (M : BudgetModule) (Γext Mach : BudgetEnv)
    (evalFn : Env → Env → (bfn : BudgetFn) → Spec bfn.toFn.as bfn.toFn.rs)
    (cap : Nat) : Prop :=
  ∀ bfn ∈ M.fns, ∀ sb, sb ≤ cap → bfn.maxFrame ≤ sb → bfn.minEntry ≤ sb →
    ∀ xs m Q X,
      evalFn (BudgetEnv.callSlot M bfn Γext Mach sb) (BudgetEnv.tailSlot M Γext Mach sb)
        bfn xs m Q X →
      Mach sb bfn.toFn.name bfn.toFn.as bfn.toFn.rs xs m Q X

/-- Stage-1 single-shot machine pre-fixpoint obligation over `LeanQbe.T.Func.wp`. -/
@[expose] def LowerOk (M : BudgetModule) (Γext Mach : BudgetEnv) (cap : Nat) : Prop :=
  LowerOkWith M Γext Mach (fun Γcall _ bfn => Func.wp Γcall bfn.toFn.body) cap

theorem lfp_mkSccOp_le_mach_single_shot {M : BudgetModule} {Γext Mach : BudgetEnv}
    {evalFn : Env → Env → (bfn : BudgetFn) → Spec bfn.toFn.as bfn.toFn.rs}
    (hm : BudgetFn.EvalMono evalFn) {cap : Nat}
    (hlow : LowerOkWith M Γext Mach evalFn cap) :
    ∀ sb, sb ≤ cap → Env.le (BudgetEnv.lfp (BudgetEnv.mkSccOp M Γext evalFn) sb) (Mach sb) := by
  refine BudgetEnv.lfp_le_of_prefix_below (BudgetEnv.mkSccOp_budgetLocal M Γext hm) cap Mach ?_
  intro sb hcap f as bs xs m Q X ⟨bfn, hmem, hname, ha, hr, hmax, hmin, heval⟩
  subst hname; subst ha; subst hr
  exact hlow bfn hmem sb hcap hmax hmin xs m Q X heval

/-- Single-shot machine pre-fixpoint theorem: `BudgetEnv.semSccWith M Γext sb ≤ Mach sb`
directly at `n = sb`, with zero `base + d * step` induction. -/
theorem semScc_le_mach_single_shot {M : BudgetModule} {Γext Mach : BudgetEnv} {cap : Nat}
    (hlow : LowerOk M Γext Mach cap) :
    ∀ sb, sb ≤ cap → Env.le (BudgetEnv.semSccWith M Γext sb) (Mach sb) :=
  lfp_mkSccOp_le_mach_single_shot funcWp_evalMono hlow

theorem semScc_const_le_mach_single_shot {M : BudgetModule} {Γext : Env} {Mach : BudgetEnv}
    {cap : Nat} (hlow : LowerOk M (BudgetEnv.const Γext) Mach cap) :
    ∀ sb, sb ≤ cap → Env.le (BudgetEnv.semScc M Γext sb) (Mach sb) :=
  semScc_le_mach_single_shot hlow

theorem semScc_le_mach_unbounded {M : BudgetModule} {Γext Mach : BudgetEnv}
    (hpre : ∀ bfn ∈ M.fns, ∀ sb, bfn.maxFrame ≤ sb → bfn.minEntry ≤ sb →
      ∀ xs m Q X,
        Func.wp (BudgetEnv.callSlot M bfn Γext Mach sb) bfn.toFn.body xs m Q X →
        Mach sb bfn.toFn.name bfn.toFn.as bfn.toFn.rs xs m Q X) :
    BudgetEnv.le (BudgetEnv.semSccWith M Γext) Mach := by
  apply BudgetEnv.lfp_le
  intro sb f as bs xs m Q X ⟨bfn, hmem, hname, ha, hr, hmax, hmin, hwp⟩
  subst hname; subst ha; subst hr
  exact hpre bfn hmem sb hmax hmin xs m Q X hwp

/-- Real `LeanQbe.T.Target.FnSpec` lifted into `BudgetEnv`. -/
@[expose] def targetMachEnv (T : Target) (h : T.mach.Host) (nX : Nat) : BudgetEnv :=
  fun n f as bs xs m Q X => ∃ spec : Spec as bs, T.FnSpec h f spec n nX ∧ spec xs m Q X

theorem targetMachEnv_mono_below (T : Target) (h : T.mach.Host) (nX : Nat)
    {n₁ n₂ : Nat} (hle : n₁ ≤ n₂) (hbound : n₂ + T.frame.raBytes ≤ 2 ^ 64) :
    Env.le (targetMachEnv T h nX n₁) (targetMachEnv T h nX n₂) := by
  intro f as bs xs m Q X ⟨spec, hfn, hsp⟩
  exact ⟨spec, Target.FnSpec.mono_stack T hfn hle hbound, hsp⟩

theorem targetMachEnv_of_fnSpec (T : Target) (h : T.mach.Host) (nX n : Nat)
    {sym : Sym} {as bs : List Ty} {spec : Spec as bs} (hfn : T.FnSpec h sym spec n nX) :
    ∀ xs m Q X, spec xs m Q X → targetMachEnv T h nX n sym as bs xs m Q X :=
  fun _ _ _ _ hsp => ⟨spec, hfn, hsp⟩

theorem targetMachEnv_to_fnSpec (T : Target) (h : T.mach.Host) (nX n : Nat)
    {sym : Sym} {as bs : List Ty} {spec : Spec as bs}
    (hsub : ∀ xs m Q X, spec xs m Q X → targetMachEnv T h nX n sym as bs xs m Q X) :
    T.FnSpec h sym spec n nX := by
  intro args m Q X hsp
  rcases hsub args m Q X hsp with ⟨spec', hfn', hsp'⟩
  exact hfn' args m Q X hsp'

/-- Single-shot `Target.FnSpec` bridge: any `LowerOk` module on `[0, 2^64 - T.frame.raBytes]`
yields `T.FnSpec` directly for `BudgetEnv.semSccWith M Γext sb`. -/
theorem budget_semScc_to_target_fnSpec (T : Target) (h : T.mach.Host) (nX : Nat)
    {M : BudgetModule} {Γext : BudgetEnv}
    (hlow : LowerOk M Γext (targetMachEnv T h nX) (2 ^ 64 - T.frame.raBytes))
    {sb : Nat} (hsb : sb ≤ 2 ^ 64 - T.frame.raBytes)
    (sym : Sym) (as bs : List Ty) :
    T.FnSpec h sym (BudgetEnv.semSccWith M Γext sb sym as bs) sb nX :=
  targetMachEnv_to_fnSpec T h nX sb
    (fun xs m Q X hsem => semScc_le_mach_single_shot hlow sb hsb sym as bs xs m Q X hsem)

/-- Constant-`Γext` specialization of `budget_semScc_to_target_fnSpec` for `BudgetEnv.semScc`. -/
theorem budget_semScc_const_to_target_fnSpec (T : Target) (h : T.mach.Host) (nX : Nat)
    {M : BudgetModule} {Γext : Env}
    (hlow : LowerOk M (BudgetEnv.const Γext) (targetMachEnv T h nX) (2 ^ 64 - T.frame.raBytes))
    {sb : Nat} (hsb : sb ≤ 2 ^ 64 - T.frame.raBytes)
    (sym : Sym) (as bs : List Ty) :
    T.FnSpec h sym (BudgetEnv.semScc M Γext sb sym as bs) sb nX :=
  budget_semScc_to_target_fnSpec T h nX hlow hsb sym as bs

end LeanQbe.T
