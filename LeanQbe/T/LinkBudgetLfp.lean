module

public import LeanQbe.T.LinkParamEnv
import LeanQbe.T.WPLemmas
import LeanQbe.T.AbiLemmas

/-!
# Stack-Budget-Indexed `BudgetEnv.lfp` Fixed-Point Core

Purely target-independent, additive fixed-point semantics over `BudgetEnv := ParamEnv Nat`,
pairing `maxFrame` and `minEntry` directly on `BudgetFn`, backed by `LeanQbe.T.LinkParamEnv`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T

/-! ## 1. Stack-Budget-Indexed Environments and Knaster–Tarski `BudgetEnv.lfp` -/

abbrev BudgetEnv : Type := ParamEnv Nat

namespace BudgetEnv

abbrev le (G₁ G₂ : BudgetEnv) : Prop := ParamEnv.le G₁ G₂
theorem le_refl (G : BudgetEnv) : le G G := ParamEnv.le_refl G
theorem le_trans {G₁ G₂ G₃ : BudgetEnv} (h12 : le G₁ G₂) (h23 : le G₂ G₃) : le G₁ G₃ :=
  ParamEnv.le_trans h12 h23
abbrev bot : BudgetEnv := ParamEnv.bot
abbrev top : BudgetEnv := ParamEnv.top
theorem bot_le (G : BudgetEnv) : le bot G := ParamEnv.bot_le G
abbrev const (Γ : Env) : BudgetEnv := ParamEnv.const Γ
abbrev mono (Φ : BudgetEnv → BudgetEnv) : Prop := ParamEnv.mono Φ
abbrev lfp (Φ : BudgetEnv → BudgetEnv) : BudgetEnv := ParamEnv.lfp Φ

theorem lfp_le {Φ : BudgetEnv → BudgetEnv} {G : BudgetEnv} (h : le (Φ G) G) : le (lfp Φ) G :=
  ParamEnv.lfp_le h
theorem lfp_closed {Φ : BudgetEnv → BudgetEnv} (hm : mono Φ) : le (Φ (lfp Φ)) (lfp Φ) :=
  ParamEnv.lfp_closed hm
theorem lfp_pre {Φ : BudgetEnv → BudgetEnv} (hm : mono Φ) : le (Φ (lfp Φ)) (lfp Φ) :=
  ParamEnv.lfp_closed hm
theorem lfp_post {Φ : BudgetEnv → BudgetEnv} (hm : mono Φ) : le (lfp Φ) (Φ (lfp Φ)) :=
  ParamEnv.lfp_post hm
theorem lfp_fix {Φ : BudgetEnv → BudgetEnv} (hm : mono Φ) : lfp Φ = Φ (lfp Φ) :=
  ParamEnv.lfp_fix hm
theorem lfp_mono {Φ₁ Φ₂ : BudgetEnv → BudgetEnv} (hm₂ : mono Φ₂)
    (hle : ∀ G, le (Φ₁ G) (Φ₂ G)) : le (lfp Φ₁) (lfp Φ₂) := ParamEnv.lfp_mono hm₂ hle

/-! ## 2. Budget Monotonicity, Well-Founded Introduction, and Prefix Locality -/

abbrev IsBudgetMono (G : BudgetEnv) : Prop := ParamEnv.IsRelMono (· ≤ ·) G
abbrev PreservesBudgetMono (Φ : BudgetEnv → BudgetEnv) : Prop :=
  ParamEnv.PreservesRelMono (· ≤ ·) Φ

theorem lfp_budget_mono {Φ : BudgetEnv → BudgetEnv}
    (hm : mono Φ) (hbm : PreservesBudgetMono Φ) : IsBudgetMono (lfp Φ) :=
  ParamEnv.lfp_rel_mono (· ≤ ·) Nat.le_refl (fun _ _ _ => Nat.le_trans) hm hbm

abbrev belowEnv {ι : Type} (lt : ι → ι → Prop) (reqBudget : ι → Nat)
    (P : ι → Env) (i : ι) : BudgetEnv := ParamEnv.supBelow (· ≤ ·) lt reqBudget P i

theorem lfp_wf {Φ : BudgetEnv → BudgetEnv} (hm : mono Φ)
    {ι : Type} {lt : ι → ι → Prop} (hwf : WellFounded lt) (reqBudget : ι → Nat) (P : ι → Env)
    (hstep : ∀ i sb, reqBudget i ≤ sb → Env.le (P i) (Φ (belowEnv lt reqBudget P i) sb)) :
    ∀ i sb, reqBudget i ≤ sb → Env.le (P i) (lfp Φ sb) :=
  ParamEnv.lfp_wf_above (· ≤ ·) hwf reqBudget hm P hstep

theorem edge_nonTail_budget {reqi reqj cost sb : Nat}
    (hsb : reqi ≤ sb) (hedge : reqj ≤ reqi - cost) : reqj ≤ sb - cost :=
  Nat.le_trans hedge (Nat.sub_le_sub_right hsb cost)

theorem edge_tail_budget {reqi reqj sb : Nat}
    (hsb : reqi ≤ sb) (hedge : reqj ≤ reqi) : reqj ≤ sb := Nat.le_trans hedge hsb

abbrev BudgetLocal (Φ : BudgetEnv → BudgetEnv) : Prop := ParamEnv.PrefixLocal (· ≤ ·) Φ

theorem lfp_le_of_prefix_below {Φ : BudgetEnv → BudgetEnv} (hloc : BudgetLocal Φ)
    (cap : Nat) (Mach : BudgetEnv) (hpre : ∀ sb, sb ≤ cap → Env.le (Φ Mach sb) (Mach sb)) :
    ∀ sb, sb ≤ cap → Env.le (lfp Φ sb) (Mach sb) :=
  ParamEnv.lfp_le_of_prefix_below (· ≤ ·) (fun _ _ _ => Nat.le_trans) hloc cap Mach hpre

end BudgetEnv

/-! ## 3. `BudgetFn`, `BudgetModule`, and Split-Slot Semantics (`BudgetEnv.semScc`) -/

/-- A typed IR function paired with per-function `maxFrame` and entry headroom `minEntry`. -/
structure BudgetFn where
  toFn : Fn
  maxFrame : Nat
  minEntry : Nat := maxFrame

/-- A target-independent module of stack-budgeted functions, externs, and exit symbols. -/
structure BudgetModule where
  fns : List BudgetFn
  externs : List Extern := []
  exits : List Sym := []

@[expose] def BudgetModule.toModule (M : BudgetModule) : Module :=
  { fns := M.fns.map BudgetFn.toFn, externs := M.externs, exits := M.exits }

@[expose] def BudgetModule.fnSigs (M : BudgetModule) : List SigEntry := M.fns.map (·.toFn.sig)
@[expose] def BudgetModule.extSigs (M : BudgetModule) : List SigEntry := M.externs.map Extern.sig

@[expose] def BudgetModule.ofModule (frame : Fn → Nat) (M : Module) : BudgetModule :=
  { fns := M.fns.map (fun fn => { toFn := fn, maxFrame := frame fn }),
    externs := M.externs, exits := M.exits }

theorem BudgetModule.ofModule_toModule (frame : Fn → Nat) (M : Module) :
    (BudgetModule.ofModule frame M).toModule = M := by
  cases M; simp [BudgetModule.ofModule, BudgetModule.toModule, List.map_map, Function.comp_def]

@[expose] def BudgetFn.EvalMono
    (evalFn : Env → Env → (bfn : BudgetFn) → Spec bfn.toFn.as bfn.toFn.rs) : Prop :=
  ∀ (bfn : BudgetFn) ⦃C₁ C₂ T₁ T₂ : Env⦄, Env.le C₁ C₂ → Env.le T₁ T₂ →
    ∀ xs m Q X, evalFn C₁ T₁ bfn xs m Q X → evalFn C₂ T₂ bfn xs m Q X

private theorem funcWp_evalMono :
    BudgetFn.EvalMono (fun Γcall _ bfn => Func.wp Γcall bfn.toFn.body) :=
  fun bfn _ _ _ _ hC _ xs m _ _ hwp => wp_env_mono hC (bfn.toFn.body Val Cont xs) m hwp

namespace BudgetEnv

@[expose] def extStep (M : BudgetModule) (Γext : Env) : Env :=
  fun f as bs xs m Q X => (f, as, bs) ∈ M.extSigs ∧ Γext f as bs xs m Q X

@[expose] def sccStep (M : BudgetModule) (Γ Γext : Env) : Env :=
  fun f as bs xs m Q X =>
    ((f, as, bs) ∈ M.fnSigs ∧ Γ f as bs xs m Q X) ∨
    ((f, as, bs) ∈ M.extSigs ∧ Γext f as bs xs m Q X)

theorem extStep_le_sccStep (M : BudgetModule) (Γ Γext : Env) :
    Env.le (extStep M Γext) (sccStep M Γ Γext) := fun _ _ _ _ _ _ _ h => Or.inr h

theorem sccStep_mono {M : BudgetModule} {Γ₁ Γ₂ Γext₁ Γext₂ : Env}
    (hΓ : Env.le Γ₁ Γ₂) (hext : Env.le Γext₁ Γext₂) :
    Env.le (sccStep M Γ₁ Γext₁) (sccStep M Γ₂ Γext₂) := by
  rintro f as bs xs m Q X (⟨hf, h1⟩ | ⟨he, h2⟩)
  · exact Or.inl ⟨hf, hΓ f as bs xs m Q X h1⟩
  · exact Or.inr ⟨he, hext f as bs xs m Q X h2⟩

@[expose] def callSlot (M : BudgetModule) (bfn : BudgetFn) (Γext G : BudgetEnv) (sb : Nat) : Env :=
  sccStep M (G (sb - bfn.maxFrame)) (Γext (sb - bfn.maxFrame))

@[expose] def tailSlot (M : BudgetModule) (Γext G : BudgetEnv) (sb : Nat) : Env :=
  sccStep M (G sb) (Γext sb)

@[expose] def mkSccOp (M : BudgetModule) (Γext : BudgetEnv)
    (evalFn : Env → Env → (bfn : BudgetFn) → Spec bfn.toFn.as bfn.toFn.rs)
    (G : BudgetEnv) (sb : Nat) : Env :=
  fun f as bs xs m Q X =>
    ∃ bfn ∈ M.fns, bfn.toFn.name = f ∧ ∃ (ha : bfn.toFn.as = as) (hr : bfn.toFn.rs = bs),
      bfn.maxFrame ≤ sb ∧ bfn.minEntry ≤ sb ∧
      evalFn (callSlot M bfn Γext G sb) (tailSlot M Γext G sb) bfn (ha ▸ xs) m (hr ▸ Q) X

@[expose] def sccOp (M : BudgetModule) (Γext : Env) : BudgetEnv → BudgetEnv :=
  mkSccOp M (const Γext) (fun Γcall _ bfn => Func.wp Γcall bfn.toFn.body)

@[expose] def semScc (M : BudgetModule) (Γext : Env) : BudgetEnv := lfp (sccOp M Γext)

@[expose] def semSccWith (M : BudgetModule) (Γext : BudgetEnv) : BudgetEnv :=
  lfp (mkSccOp M Γext (fun Γcall _ bfn => Func.wp Γcall bfn.toFn.body))

theorem mkSccOp_mono (M : BudgetModule) (Γext : BudgetEnv)
    {evalFn : Env → Env → (bfn : BudgetFn) → Spec bfn.toFn.as bfn.toFn.rs}
    (hm : BudgetFn.EvalMono evalFn) : mono (mkSccOp M Γext evalFn) := by
  rintro G₁ G₂ hle sb f as bs xs m Q X ⟨bfn, hmem, hname, ha, hr, hmax, hmin, heval⟩
  exact ⟨bfn, hmem, hname, ha, hr, hmax, hmin, hm bfn
    (sccStep_mono (hle (sb - bfn.maxFrame)) (Env.le_refl _))
    (sccStep_mono (hle sb) (Env.le_refl _)) _ m _ _ heval⟩

theorem mkSccOp_preserves_budgetMono (M : BudgetModule) (Γext : BudgetEnv)
    {evalFn : Env → Env → (bfn : BudgetFn) → Spec bfn.toFn.as bfn.toFn.rs}
    (hm : BudgetFn.EvalMono evalFn) (hext : IsBudgetMono Γext) :
    PreservesBudgetMono (mkSccOp M Γext evalFn) := by
  rintro G hG sb₁ sb₂ hle f as bs xs m Q X ⟨bfn, hmem, hname, ha, hr, hmax, hmin, heval⟩
  have hsub := Nat.sub_le_sub_right hle bfn.maxFrame
  exact ⟨bfn, hmem, hname, ha, hr, Nat.le_trans hmax hle, Nat.le_trans hmin hle, hm bfn
    (sccStep_mono (hG hsub) (hext hsub)) (sccStep_mono (hG hle) (hext hle)) _ m _ _ heval⟩

theorem mkSccOp_budgetLocal (M : BudgetModule) (Γext : BudgetEnv)
    {evalFn : Env → Env → (bfn : BudgetFn) → Spec bfn.toFn.as bfn.toFn.rs}
    (hm : BudgetFn.EvalMono evalFn) : BudgetLocal (mkSccOp M Γext evalFn) := by
  rintro sb G₁ G₂ hle f as bs xs m Q X ⟨bfn, hmem, hname, ha, hr, hmax, hmin, heval⟩
  exact ⟨bfn, hmem, hname, ha, hr, hmax, hmin, hm bfn
    (sccStep_mono (hle (sb - bfn.maxFrame) (Nat.sub_le _ _)) (Env.le_refl _))
    (sccStep_mono (hle sb (Nat.le_refl _)) (Env.le_refl _)) _ m _ _ heval⟩

theorem sccOp_mono (M : BudgetModule) (Γext : Env) : mono (sccOp M Γext) :=
  mkSccOp_mono M (const Γext) funcWp_evalMono

theorem semScc_fix (M : BudgetModule) (Γext : Env) :
    semScc M Γext = sccOp M Γext (semScc M Γext) := lfp_fix (sccOp_mono M Γext)

theorem semSccWith_fix (M : BudgetModule) (Γext : BudgetEnv) :
    semSccWith M Γext =
      mkSccOp M Γext (fun Γcall _ bfn => Func.wp Γcall bfn.toFn.body) (semSccWith M Γext) :=
  lfp_fix (mkSccOp_mono M Γext funcWp_evalMono)

theorem semScc_budget_mono (M : BudgetModule) (Γext : Env) : IsBudgetMono (semScc M Γext) :=
  lfp_budget_mono (sccOp_mono M Γext)
    (mkSccOp_preserves_budgetMono M (const Γext) funcWp_evalMono fun _ _ _ => Env.le_refl _)

theorem semSccWith_budget_mono (M : BudgetModule) {Γext : BudgetEnv}
    (hext : IsBudgetMono Γext) : IsBudgetMono (semSccWith M Γext) :=
  lfp_budget_mono (mkSccOp_mono M Γext funcWp_evalMono)
    (mkSccOp_preserves_budgetMono M Γext funcWp_evalMono hext)

theorem lfp_wf_mkSccOp {ι : Type} {lt : ι → ι → Prop} (hwf : WellFounded lt)
    (reqBudget : ι → Nat) (M : BudgetModule) (Γext : BudgetEnv)
    {evalFn : Env → Env → (bfn : BudgetFn) → Spec bfn.toFn.as bfn.toFn.rs}
    (hm : BudgetFn.EvalMono evalFn) (S : ι → Env)
    (hstep : ∀ (i : ι) (sb : Nat), reqBudget i ≤ sb → ∀ (bfn : BudgetFn), bfn ∈ M.fns →
      ∀ (Γcall Γtail : Env),
        (∀ j, lt j i → reqBudget j ≤ sb - bfn.maxFrame →
          Env.le (Env.restrict (S j) M.fnSigs) Γcall) →
        Env.le (extStep M (Γext (sb - bfn.maxFrame))) Γcall →
        (∀ j, lt j i → reqBudget j ≤ sb → Env.le (Env.restrict (S j) M.fnSigs) Γtail) →
        Env.le (extStep M (Γext sb)) Γtail →
        ∀ xs m Q X, S i bfn.toFn.name bfn.toFn.as bfn.toFn.rs xs m Q X →
          bfn.maxFrame ≤ sb ∧ bfn.minEntry ≤ sb ∧ evalFn Γcall Γtail bfn xs m Q X) :
    ∀ i sb, reqBudget i ≤ sb →
      Env.le (Env.restrict (S i) M.fnSigs) (lfp (mkSccOp M Γext evalFn) sb) := by
  let S' : ι → Env := fun i => Env.restrict (S i) M.fnSigs
  refine lfp_wf (mkSccOp_mono M Γext hm) hwf reqBudget S' fun i sb hsb f as bs xs m Q X hS' => ?_
  obtain ⟨bfn, hmem, hsig⟩ := List.mem_map.mp hS'.1
  rcases Prod.mk.inj hsig with ⟨rfl, hrest⟩; rcases Prod.mk.inj hrest with ⟨rfl, rfl⟩
  have hres := hstep i sb hsb bfn hmem (callSlot M bfn Γext (belowEnv lt reqBudget S' i) sb)
    (tailSlot M Γext (belowEnv lt reqBudget S' i) sb)
    (fun j hlt hreq _ _ _ _ _ _ _ hSj => Or.inl ⟨hSj.1, j, hlt, hreq, hSj⟩)
    (extStep_le_sccStep M _ _)
    (fun j hlt hreq _ _ _ _ _ _ _ hSj => Or.inl ⟨hSj.1, j, hlt, hreq, hSj⟩)
    (extStep_le_sccStep M _ _) xs m Q X hS'.2
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
  private theorem wp_noCall_env_le (Γ₁ Γ₂ : Env) {rs : List Ty} {Q : Post rs} {X : XPost}
      {e : Expr Val Cont rs} (hnc : e.NoCall) (m : Mem 64) : wp Γ₁ Q X e m → wp Γ₂ Q X e m := by
    cases hnc with
    | let_ op k hk => exact Op.wp_mono (fun r hr => wp_noCall_env_le Γ₁ Γ₂ (hk r) m hr)
    | load t a k hk => exact fun ⟨v, hv, h⟩ => ⟨v, hv, wp_noCall_env_le Γ₁ Γ₂ (hk v) m h⟩
    | store v a k hk => exact fun ⟨hs, h⟩ => ⟨hs, wp_noCall_env_le Γ₁ Γ₂ hk _ h⟩
    | jnz c t e ht he => exact fun ⟨h1, h2⟩ =>
        ⟨fun hc => wp_noCall_env_le Γ₁ Γ₂ ht m (h1 hc),
         fun hc => wp_noCall_env_le Γ₁ Γ₂ he m (h2 hc)⟩
    | jump _ _ | ret _ | exit _ _ | hlt => exact id
    | group _ _ hbs hk =>
        exact fun h Js hcl => wp_noCall_env_le Γ₁ Γ₂ (hk Js) m
          (h Js (closed_noCall_env_le Γ₂ Γ₁ (hbs Js) Js hcl))

  private theorem closed_noCall_env_le (Γ₁ Γ₂ : Env) {rs : List Ty} {Q : Post rs} {X : XPost}
      {sig : List (List Ty)} {bs : Blocks Val Cont rs sig} (hnc : bs.NoCall)
      (Js : Tup Cont sig) : Closed Γ₁ Q X bs Js → Closed Γ₂ Q X bs Js := by
    cases hnc with
    | nil => exact id
    | cons b rest hb hrest => exact fun ⟨h1, h2⟩ =>
        ⟨fun xs m hm => h1 xs m (wp_noCall_env_le Γ₂ Γ₁ (hb xs) m hm),
         closed_noCall_env_le Γ₁ Γ₂ hrest Js.2 h2⟩
end

theorem wp_noCall_env_indep (Γ₁ Γ₂ : Env) {rs : List Ty} {Q : Post rs} {X : XPost}
    {e : Expr Val Cont rs} (hnc : e.NoCall) (m : Mem 64) : wp Γ₁ Q X e m ↔ wp Γ₂ Q X e m :=
  ⟨wp_noCall_env_le Γ₁ Γ₂ hnc m, wp_noCall_env_le Γ₂ Γ₁ hnc m⟩

theorem closed_noCall_env_indep (Γ₁ Γ₂ : Env) {rs : List Ty} {Q : Post rs} {X : XPost}
    {sig : List (List Ty)} {bs : Blocks Val Cont rs sig} (hnc : bs.NoCall)
    (Js : Tup Cont sig) : Closed Γ₁ Q X bs Js ↔ Closed Γ₂ Q X bs Js :=
  ⟨closed_noCall_env_le Γ₁ Γ₂ hnc Js, closed_noCall_env_le Γ₂ Γ₁ hnc Js⟩

@[expose] def StrictNoTailModule (M : BudgetModule) : Prop :=
  ∀ bfn ∈ M.fns, (∃ xs, ¬ (bfn.toFn.body Val Cont xs).NoCall) → bfn.maxFrame > 0

@[expose] noncomputable def wfStep (M : BudgetModule) (Γext : BudgetEnv)
    (sb : Nat) (rec : ∀ sb', sb' < sb → Env) : Env :=
  fun f as bs xs m Q X =>
    ∃ bfn ∈ M.fns, bfn.toFn.name = f ∧ ∃ (ha : bfn.toFn.as = as) (hr : bfn.toFn.rs = bs),
      bfn.maxFrame ≤ sb ∧ bfn.minEntry ≤ sb ∧
      Func.wp (BudgetEnv.sccStep M
        (if hlt : sb - bfn.maxFrame < sb then rec (sb - bfn.maxFrame) hlt else BudgetEnv.bot 0)
        (Γext (sb - bfn.maxFrame))) bfn.toFn.body (ha ▸ xs) m (hr ▸ Q) X

@[expose] noncomputable def wfSem (M : BudgetModule) (Γext : BudgetEnv) : BudgetEnv :=
  fun sb => Nat.strongRecOn (motive := fun _ => Env) sb (wfStep M Γext)

theorem wfSem_eq (M : BudgetModule) (Γext : BudgetEnv) (sb : Nat) :
    wfSem M Γext sb = wfStep M Γext sb (fun sb' _ => wfSem M Γext sb') :=
  WellFounded.fix_eq Nat.lt_wfRel.wf (fun sb rec => wfStep M Γext sb rec) sb

theorem lfp_eq_wfRec_of_noTail {M : BudgetModule} (Γext : BudgetEnv) (hsnt : StrictNoTailModule M) :
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
        · have hpos := hsnt bfn hmem ⟨_, hnc⟩
          have hlt : sb - bfn.maxFrame < sb := Nat.sub_lt (Nat.lt_of_lt_of_le hpos hmax) hpos
          have hwp0 : Func.wp
              (BudgetEnv.sccStep M (wfSem M Γext (sb - bfn.maxFrame)) (Γext (sb - bfn.maxFrame)))
              bfn.toFn.body (ha ▸ xs) m (hr ▸ Q) X := by simpa [dite_eq_left hlt] using hwp
          exact wp_env_mono (BudgetEnv.sccStep_mono (ih (sb - bfn.maxFrame) hlt) (Env.le_refl _))
            _ m hwp0
  have h_lfp_le : BudgetEnv.le (BudgetEnv.semSccWith M Γext) (wfSem M Γext) := by
    apply BudgetEnv.lfp_le
    intro sb f as bs xs m Q X ⟨bfn, hmem, hname, ha, hr, hmax, hmin, hwp⟩
    rw [wfSem_eq]; refine ⟨bfn, hmem, hname, ha, hr, hmax, hmin, ?_⟩
    by_cases hnc : (bfn.toFn.body Val Cont (ha ▸ xs)).NoCall
    · exact (wp_noCall_env_indep _ _ hnc m).mp hwp
    · have hpos := hsnt bfn hmem ⟨_, hnc⟩
      have hlt : sb - bfn.maxFrame < sb := Nat.sub_lt (Nat.lt_of_lt_of_le hpos hmax) hpos
      simpa [BudgetEnv.callSlot, dite_eq_left hlt] using hwp
  intro sb; funext f as bs xs m Q X
  exact propext ⟨fun h => h_lfp_le sb f as bs xs m Q X h, fun h => h_wf_le sb f as bs xs m Q X h⟩

theorem semScc_eq_wfRec_of_noTail {M : BudgetModule} (Γext : Env) (hsnt : StrictNoTailModule M) :
    ∀ sb, BudgetEnv.semScc M Γext sb = wfSem M (BudgetEnv.const Γext) sb :=
  lfp_eq_wfRec_of_noTail (BudgetEnv.const Γext) hsnt

/-! ## 5. Legacy `ModuleOk` Compatibility Bridge (`moduleOk_embeds_into_budget_semScc`) -/

@[expose] def BudgetModule.sumEntryBound (bfns : List BudgetFn) : Nat :=
  bfns.foldr (fun bfn acc => max bfn.maxFrame bfn.minEntry + acc) 0

private theorem sumEntryBound_append (xs ys : List BudgetFn) :
    BudgetModule.sumEntryBound (xs ++ ys) =
      BudgetModule.sumEntryBound xs + BudgetModule.sumEntryBound ys := by
  induction xs with
  | nil => simp [BudgetModule.sumEntryBound]
  | cons x xs ih =>
      simp only [BudgetModule.sumEntryBound, List.cons_append, List.foldr_cons] at ih ⊢; omega

theorem moduleOk_embeds_into_budget_semScc {Γ : Env} {BM : BudgetModule}
    (hM : ModuleOk Γ BM.toModule) :
    Env.le (Env.restrict Γ BM.fnSigs)
      (BudgetEnv.semScc BM Γ (BudgetModule.sumEntryBound BM.fns)) := by
  have hprefix : ∀ k, k ≤ BM.fns.length → ∀ bfn ∈ BM.fns.take k,
      ∀ xs m Q X, Γ bfn.toFn.name bfn.toFn.as bfn.toFn.rs xs m Q X →
        BudgetEnv.semScc BM Γ (BudgetModule.sumEntryBound (BM.fns.take k))
          bfn.toFn.name bfn.toFn.as bfn.toFn.rs xs m Q X := by
    intro k
    induction k with
    | zero => intro _ bfn hmem; simp at hmem
    | succ k ih =>
        intro hk bfn hmem xs m Q X hΓ
        have hklt : k < BM.fns.length := Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk
        rw [List.take_succ_eq_append_getElem hklt] at hmem ⊢
        rcases List.mem_append.mp hmem with hmem_pre | hmem_cur
        · exact BudgetEnv.semScc_budget_mono BM Γ (by rw [sumEntryBound_append]; omega)
            bfn.toFn.name bfn.toFn.as bfn.toFn.rs xs m Q X
            (ih (Nat.le_of_lt hklt) bfn hmem_pre xs m Q X hΓ)
        · rw [List.mem_singleton] at hmem_cur; subst hmem_cur
          let bcur := BM.fns[k]; let bpre := BM.fns.take k
          have hsplit : BM.toModule.fns = bpre.map BudgetFn.toFn ++ bcur.toFn ::
              (BM.fns.drop (k + 1)).map BudgetFn.toFn := by
            simpa [BudgetModule.toModule, List.map_append, List.map_cons] using
              congrArg (List.map BudgetFn.toFn)
                (show BM.fns = bpre ++ bcur :: BM.fns.drop (k + 1) by simp [bpre, bcur])
          have hfnOk := hM.fnsOk (bpre.map BudgetFn.toFn) bcur.toFn
            ((BM.fns.drop (k + 1)).map BudgetFn.toFn) hsplit
          let sb := BudgetModule.sumEntryBound (bpre ++ [bcur])
          have hsb_def :
              sb = BudgetModule.sumEntryBound bpre + max bcur.maxFrame bcur.minEntry := by
            dsimp [sb]; rw [sumEntryBound_append]; simp [BudgetModule.sumEntryBound]
          have hwp_call : wp (BudgetEnv.callSlot BM bcur (BudgetEnv.const Γ)
              (BudgetEnv.semScc BM Γ) sb) Q X (bcur.toFn.body Val Cont xs) m := by
            refine wp_env_agree_of_callsOk
              (hfnOk.1 Val (fun _ => Unit) Cont (fun _ => Unit) xs (Tup.units bcur.toFn.as))
              hfnOk.2.1 (fun g as' bs' hsig xs' m' P' E' hg => ?_) m (hfnOk.2.2 xs m Q X hΓ)
            rcases List.mem_append.mp hsig with h_pre | h_ext
            · rcases List.mem_map.mp h_pre with ⟨fn', hfn'_map, hfn'_sig⟩
              rcases List.mem_map.mp hfn'_map with ⟨bfn', hbfn'_mem, rfl⟩
              rcases Prod.mk.inj hfn'_sig with ⟨rfl, hrest⟩
              rcases Prod.mk.inj hrest with ⟨rfl, rfl⟩
              exact Or.inl ⟨List.mem_map.mpr ⟨bfn', List.mem_of_mem_take hbfn'_mem, rfl⟩,
                BudgetEnv.semScc_budget_mono BM Γ
                  (show BudgetModule.sumEntryBound bpre ≤ sb - bcur.maxFrame by rw [hsb_def]; omega)
                  _ _ _ xs' m' P' E' (ih (Nat.le_of_lt hklt) bfn' hbfn'_mem xs' m' P' E' hg)⟩
            · exact Or.inr ⟨h_ext, hg⟩
          rw [BudgetEnv.semScc_fix]
          exact ⟨bcur, List.getElem_mem hklt, rfl, rfl, rfl,
            show bcur.maxFrame ≤ sb by rw [hsb_def]; omega,
            show bcur.minEntry ≤ sb by rw [hsb_def]; omega, hwp_call⟩
  intro f as bs xs m Q X ⟨hsig, hΓ⟩
  rcases List.mem_map.mp hsig with ⟨bfn, hmem, hsig_eq⟩
  rcases Prod.mk.inj hsig_eq with ⟨rfl, hrest⟩; rcases Prod.mk.inj hrest with ⟨rfl, rfl⟩
  simpa [List.take_length] using hprefix BM.fns.length (Nat.le_refl _) bfn
    (by rw [List.take_length]; exact hmem) xs m Q X hΓ

theorem moduleOk_embeds_into_budget_semScc_ofModule {Γ : Env} {M : Module} (hM : ModuleOk Γ M)
    (frame : Fn → Nat) :
    Env.le (Env.restrict Γ (M.fns.map Fn.sig))
      (BudgetEnv.semScc (BudgetModule.ofModule frame M) Γ
        (BudgetModule.sumEntryBound (BudgetModule.ofModule frame M).fns)) := by
  have hle := moduleOk_embeds_into_budget_semScc
    (show ModuleOk Γ (BudgetModule.ofModule frame M).toModule by
      rwa [BudgetModule.ofModule_toModule])
  intro f as bs xs m Q X ⟨hsig, hΓ⟩
  exact hle f as bs xs m Q X ⟨by simpa [BudgetModule.fnSigs, BudgetModule.ofModule, List.map_map,
    Function.comp_def] using hsig, hΓ⟩

/-! ## 6. Single-Shot Machine Pre-Fixpoint & `Target.FnSpec` Bridge -/

@[expose] def LowerOkWith (M : BudgetModule) (Γext Mach : BudgetEnv)
    (evalFn : Env → Env → (bfn : BudgetFn) → Spec bfn.toFn.as bfn.toFn.rs) (cap : Nat) : Prop :=
  ∀ bfn ∈ M.fns, ∀ sb, sb ≤ cap → bfn.maxFrame ≤ sb → bfn.minEntry ≤ sb →
    ∀ xs m Q X, evalFn (BudgetEnv.callSlot M bfn Γext Mach sb) (BudgetEnv.tailSlot M Γext Mach sb)
      bfn xs m Q X → Mach sb bfn.toFn.name bfn.toFn.as bfn.toFn.rs xs m Q X

@[expose] def LowerOk (M : BudgetModule) (Γext Mach : BudgetEnv) (cap : Nat) : Prop :=
  LowerOkWith M Γext Mach (fun Γcall _ bfn => Func.wp Γcall bfn.toFn.body) cap

theorem lfp_mkSccOp_le_mach_single_shot {M : BudgetModule} {Γext Mach : BudgetEnv}
    {evalFn : Env → Env → (bfn : BudgetFn) → Spec bfn.toFn.as bfn.toFn.rs}
    (hm : BudgetFn.EvalMono evalFn) {cap : Nat} (hlow : LowerOkWith M Γext Mach evalFn cap) :
    ∀ sb, sb ≤ cap → Env.le (BudgetEnv.lfp (BudgetEnv.mkSccOp M Γext evalFn) sb) (Mach sb) := by
  refine BudgetEnv.lfp_le_of_prefix_below (BudgetEnv.mkSccOp_budgetLocal M Γext hm) cap Mach ?_
  intro sb hcap f as bs xs m Q X ⟨bfn, hmem, hname, ha, hr, hmax, hmin, heval⟩
  subst hname; subst ha; subst hr; exact hlow bfn hmem sb hcap hmax hmin xs m Q X heval

theorem semScc_le_mach_single_shot {M : BudgetModule} {Γext Mach : BudgetEnv} {cap : Nat}
    (hlow : LowerOk M Γext Mach cap) :
    ∀ sb, sb ≤ cap → Env.le (BudgetEnv.semSccWith M Γext sb) (Mach sb) :=
  lfp_mkSccOp_le_mach_single_shot funcWp_evalMono hlow

theorem semScc_const_le_mach_single_shot {M : BudgetModule} {Γext : Env} {Mach : BudgetEnv}
    {cap : Nat} (hlow : LowerOk M (BudgetEnv.const Γext) Mach cap) :
    ∀ sb, sb ≤ cap → Env.le (BudgetEnv.semScc M Γext sb) (Mach sb) :=
  semScc_le_mach_single_shot hlow

theorem semScc_le_mach_unbounded {M : BudgetModule} {Γext Mach : BudgetEnv}
    (hpre : ∀ bfn ∈ M.fns, ∀ sb, bfn.maxFrame ≤ sb → bfn.minEntry ≤ sb → ∀ xs m Q X,
      Func.wp (BudgetEnv.callSlot M bfn Γext Mach sb) bfn.toFn.body xs m Q X →
      Mach sb bfn.toFn.name bfn.toFn.as bfn.toFn.rs xs m Q X) :
    BudgetEnv.le (BudgetEnv.semSccWith M Γext) Mach := by
  apply BudgetEnv.lfp_le
  intro sb f as bs xs m Q X ⟨bfn, hmem, hname, ha, hr, hmax, hmin, hwp⟩
  subst hname; subst ha; subst hr; exact hpre bfn hmem sb hmax hmin xs m Q X hwp

@[expose] def targetMachEnv (T : Target) (h : T.mach.Host) (nX : Nat) : BudgetEnv :=
  fun n f as bs xs m Q X => ∃ spec : Spec as bs, T.FnSpec h f spec n nX ∧ spec xs m Q X

theorem targetMachEnv_mono_below (T : Target) (h : T.mach.Host) (nX : Nat)
    {n₁ n₂ : Nat} (hle : n₁ ≤ n₂) (hbound : n₂ + T.frame.raBytes ≤ 2 ^ 64) :
    Env.le (targetMachEnv T h nX n₁) (targetMachEnv T h nX n₂) :=
  fun _ _ _ _ _ _ _ ⟨spec, hfn, hsp⟩ => ⟨spec, Target.FnSpec.mono_stack T hfn hle hbound, hsp⟩

theorem targetMachEnv_of_fnSpec (T : Target) (h : T.mach.Host) (nX n : Nat)
    {sym : Sym} {as bs : List Ty} {spec : Spec as bs} (hfn : T.FnSpec h sym spec n nX) :
    ∀ xs m Q X, spec xs m Q X → targetMachEnv T h nX n sym as bs xs m Q X :=
  fun _ _ _ _ hsp => ⟨spec, hfn, hsp⟩

theorem targetMachEnv_to_fnSpec (T : Target) (h : T.mach.Host) (nX n : Nat)
    {sym : Sym} {as bs : List Ty} {spec : Spec as bs}
    (hsub : ∀ xs m Q X, spec xs m Q X → targetMachEnv T h nX n sym as bs xs m Q X) :
    T.FnSpec h sym spec n nX := fun args m Q X hsp =>
  match hsub args m Q X hsp with | ⟨_, hfn', hsp'⟩ => hfn' args m Q X hsp'

theorem budget_semScc_to_target_fnSpec (T : Target) (h : T.mach.Host) (nX : Nat)
    {M : BudgetModule} {Γext : BudgetEnv}
    (hlow : LowerOk M Γext (targetMachEnv T h nX) (2 ^ 64 - T.frame.raBytes))
    {sb : Nat} (hsb : sb ≤ 2 ^ 64 - T.frame.raBytes) (sym : Sym) (as bs : List Ty) :
    T.FnSpec h sym (BudgetEnv.semSccWith M Γext sb sym as bs) sb nX :=
  targetMachEnv_to_fnSpec T h nX sb
    (fun xs m Q X hsem => semScc_le_mach_single_shot hlow sb hsb sym as bs xs m Q X hsem)

theorem budget_semScc_const_to_target_fnSpec (T : Target) (h : T.mach.Host) (nX : Nat)
    {M : BudgetModule} {Γext : Env}
    (hlow : LowerOk M (BudgetEnv.const Γext) (targetMachEnv T h nX) (2 ^ 64 - T.frame.raBytes))
    {sb : Nat} (hsb : sb ≤ 2 ^ 64 - T.frame.raBytes) (sym : Sym) (as bs : List Ty) :
    T.FnSpec h sym (BudgetEnv.semScc M Γext sb sym as bs) sb nX :=
  budget_semScc_to_target_fnSpec T h nX hlow hsb sym as bs

end LeanQbe.T
