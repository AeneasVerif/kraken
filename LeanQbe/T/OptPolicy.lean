module

public import LeanQbe.T.Opt
public import LeanQbe.T.Legal
public import LeanQbe.T.Main
public import LeanQbe.T.LegalLemmas
import LeanQbe.T.OptLemmas
import LeanQbe.T.OptUtilLemmas
import LeanQbe.T.FoldLemmas
import LeanQbe.T.CanonLemmas
import LeanQbe.T.CopyLemmas
import LeanQbe.T.DceLemmas
import LeanQbe.T.DceParamLemmas
import LeanQbe.T.DivConstLemmas
import LeanQbe.T.MemLoadLemmas
import LeanQbe.T.PeelLemmas
import LeanQbe.T.IfOptLemmas
import LeanQbe.T.SimplifyGroupPlanLemmas
import LeanQbe.T.LicmLemmas
import LeanQbe.T.LoopRotateLemmas
import LeanQbe.T.ZeroPeelLemmas
import LeanQbe.T.AssumeBitsLemmas
import LeanQbe.T.WPLemmas
import LeanQbe.T.WfLemmas

/-!
# Policy-Scoped Mid-End Optimization (`SnippetOptPolicy`)

Purely additive Class `L` wrapper around the verified `Opt` and `Legal` passes, leaving all
existing `Func.{earlyOpt,lateOpt}` and `Fn.mid` definitions unchanged while enabling per-function
predictable codegen policies:

* `noIfOpt`: keep `.jnz` branches intact instead of if-converting via `ifOpt` / `ifOptBits`.
* `noSimplifyGrp`: preserve explicit `.group` join boundaries (`simplifyGroupFast`).
* `noPeel` / `noZeroPeel`: disable loop peeling and zero-fill loop widening.
* `noRotate`: disable CFG loop rotation (`loopRotate`).
* `noMergeRets`: preserve direct epilogue `.ret` leaves without merging (`mergeRets`).
* `noNormCmpImm`: skip `Fold`'s `normBitsCmpImm` (keeping e.g. `sgt x 0` instead of rewriting to
  `sge x 1`), running `Func.constFoldNoCmp` for pure constant folding and dead-branch pruning.
* `noHoistOut`: disable `licm` hoisting out of register-tight snippets.

All composed pipelines (`Func.earlyOptPolicy`, `Func.lateCorePrePolicy`, `Func.lateCorePostPolicy`,
`Func.lateCfgPrePolicy`, `Func.lateCfgPostPolicy`, `Func.lateLoopRotatePolicy`, `Func.lateOptPolicy`,
`Fn.midPolicy`) prove `*_wf` and `*_spec` cleanly using the underlying verified pass theorems.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

/-! ## Scoped optimization policy configuration -/

/-- Policy flags restricting mid-end transformations that alter control-flow shape, compare
immediates, epilogues, or live-range spans on `@predictable` / lifted snippets. -/
structure SnippetOptPolicy where
  noIfOpt       : Bool := false
  noRotate      : Bool := false
  noPeel        : Bool := false
  noZeroPeel    : Bool := false
  noMergeRets   : Bool := false
  noNormCmpImm  : Bool := false
  noHoistOut    : Bool := false
  noSimplifyGrp : Bool := false
  deriving DecidableEq, Repr, Inhabited, Lean.ToExpr

namespace SnippetOptPolicy

/-- Default optimization policy: runs every pass identical to `earlyOpt` / `lateOpt`. -/
def default : SnippetOptPolicy := {}

/-- Strict predictable policy for hand-tuned / lifted snippets (`inSp = 0`, CFG/cmp stability). -/
def predictable : SnippetOptPolicy :=
  { noIfOpt := true
    noRotate := true
    noPeel := true
    noZeroPeel := true
    noMergeRets := true
    noNormCmpImm := true
    noHoistOut := true
    noSimplifyGrp := true }

end SnippetOptPolicy

/-- Lookup table mapping function symbols to scoped `SnippetOptPolicy` values. -/
abbrev OptPolicyMap := List (Sym × SnippetOptPolicy)

/-- Resolve a function symbol against an `OptPolicyMap`, falling back to `fallback`. -/
def OptPolicyMap.lookup (m : OptPolicyMap) (sym : Sym)
    (fallback : SnippetOptPolicy := .default) : SnippetOptPolicy :=
  match m.find? (fun p => p.1 == sym) with
  | some p => p.2
  | none => fallback

/-! ## Comparison-preserving constant fold (`Func.constFoldNoCmp`) -/

/-- Convert a closed tuple of runtime `Val`s to immediate `Arg V` operands. -/
def valTupToArgs {V : Ty → Type} : {ts : List Ty} → Tup Val ts → Tup (Arg V) ts
  | [], () => ()
  | _ :: _, (v, vs) => (.imm v, valTupToArgs vs)

mutual
/-- Fold pure all-immediate `.let_` operations via `OpCode.eval?` and prune constant `.jnz`
branches without normalizing integer comparisons (`normBitsCmpImm`). -/
def constFoldExpr {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    Expr (Arg V) L rs → Expr V L rs
  | .let_ op k =>
    let op' := flattenOp op
    match tupImms? op'.args with
    | some imms =>
      match op'.code.eval? imms with
      | some res => constFoldExpr (k (valTupToArgs res))
      | none => .let_ op' fun xs => constFoldExpr (k (toArgTup xs))
    | none => .let_ op' fun xs => constFoldExpr (k (toArgTup xs))
  | .load t a k => .load t (flattenArg a) fun v => constFoldExpr (k (.var v))
  | .store v a k => .store (flattenArg v) (flattenArg a) (constFoldExpr k)
  | .call f args k => .call f (flattenArgs args) fun xs => constFoldExpr (k (toArgTup xs))
  | .jnz c t e =>
    match flattenArg c with
    | .imm b => if b then constFoldExpr t else constFoldExpr e
    | .var v => .jnz (.var v) (constFoldExpr t) (constFoldExpr e)
  | .jump j args => .jump j (flattenArgs args)
  | .ret vs => .ret (flattenArgs vs)
  | .exit f args => .exit f (flattenArgs args)
  | .hlt => .hlt
  | .group bodies k =>
    .group (fun Js => constFoldBlocks (bodies Js)) (fun Js => constFoldExpr (k Js))

/-- Block-list companion of `constFoldExpr`. -/
def constFoldBlocks {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    {sig : List (List Ty)} → Blocks (Arg V) L rs sig → Blocks V L rs sig
  | _, .nil => .nil
  | _, .cons b bs => .cons (fun xs => constFoldExpr (b (toArgTup xs))) (constFoldBlocks bs)
end

/-- Closed-function comparison-preserving constant fold (`constFoldExpr`). -/
def Func.constFoldNoCmp {as rs : List Ty} (f : Func as rs) : Func as rs :=
  fun V L xs => constFoldExpr (f (Arg V) L (toArgTup xs))

section ConstFoldProofs

private def CFRelG {V₁ V₂ : Ty → Type} (G₀ : Ctx (Arg V₁) (Arg V₂)) (G : Ctx V₁ V₂) : Prop :=
  ∀ p ∈ G₀, ArgRel G p.1 p.2.1 p.2.2 ∧ Arg.imm? p.2.1 = Arg.imm? p.2.2

private theorem CFRelG.weaken {V₁ V₂ : Ty → Type} {G₀ : Ctx (Arg V₁) (Arg V₂)}
    {G₁ G₂ : Ctx V₁ V₂} (hsub : ∀ p ∈ G₁, p ∈ G₂) (hG : CFRelG G₀ G₁) : CFRelG G₀ G₂ :=
  fun p hp => ⟨(hG p hp).1.weaken hsub, (hG p hp).2⟩

private theorem CFRelG.append {V₁ V₂ : Ty → Type} {H G₀ : Ctx (Arg V₁) (Arg V₂)}
    {G : Ctx V₁ V₂} (hH : CFRelG H G) (hG : CFRelG G₀ G) : CFRelG (H ++ G₀) G := by
  intro p hp
  rcases List.mem_append.1 hp with hp | hp
  · exact hH p hp
  · exact hG p hp

private theorem CFRelG.toArgTup {V₁ V₂ : Ty → Type} {G : Ctx V₁ V₂} :
    {ts : List Ty} → (xs₁ : Tup V₁ ts) → (xs₂ : Tup V₂ ts) →
    CFRelG (Tup.zip (toArgTup xs₁) (toArgTup xs₂)) (Tup.zip xs₁ xs₂ ++ G)
  | [], (), (), _, hp => nomatch hp
  | _ :: _, (_, xs₁), (_, xs₂), _, hp => by
    cases hp with
    | head => exact ⟨.var (List.mem_append_left _ List.mem_cons_self), rfl⟩
    | tail _ hp =>
      have ih := CFRelG.toArgTup (G := G) xs₁ xs₂ _ hp
      exact ⟨ih.1.weaken (fun _ hq => by
        rcases List.mem_append.1 hq with hq | hq
        · exact List.mem_append_left _ (List.mem_cons_of_mem _ hq)
        · exact List.mem_append_right _ hq), ih.2⟩

private theorem CFRelG.valTupToArgs {V₁ V₂ : Ty → Type} {G : Ctx V₁ V₂} :
    {ts : List Ty} → (xs : Tup Val ts) →
    CFRelG (Tup.zip (valTupToArgs (V := V₁) xs) (valTupToArgs (V := V₂) xs)) G
  | [], (), _, hp => nomatch hp
  | _ :: _, (_, xs), _, hp => by
    cases hp with
    | head => exact ⟨.imm _, rfl⟩
    | tail _ hp => exact CFRelG.valTupToArgs xs _ hp

private theorem CFRelG.singleVar {V₁ V₂ : Ty → Type} {G : Ctx V₁ V₂} {t : Ty}
    (v₁ : V₁ t) (v₂ : V₂ t) :
    CFRelG [⟨t, .var v₁, .var v₂⟩] (⟨t, v₁, v₂⟩ :: G) := by
  intro p hp
  cases hp with
  | head => exact ⟨.var List.mem_cons_self, rfl⟩
  | tail _ hp => nomatch hp

private theorem flattenArg_imm?_eq {V₁ V₂ : Ty → Type}
    {G₀ : Ctx (Arg V₁) (Arg V₂)} {G : Ctx V₁ V₂} (hG : CFRelG G₀ G)
    {t : Ty} {a₁ : Arg (Arg V₁) t} {a₂ : Arg (Arg V₂) t} (ha : ArgRel G₀ t a₁ a₂) :
    (flattenArg a₁).imm? = (flattenArg a₂).imm? := by
  cases ha with
  | var hm => exact (hG _ hm).2
  | imm _ => rfl

private theorem tupImms?_flattenArgs_eq {V₁ V₂ : Ty → Type}
    {G₀ : Ctx (Arg V₁) (Arg V₂)} {G : Ctx V₁ V₂} (hG : CFRelG G₀ G)
    {ts : List Ty} {as₁ : Tup (Arg (Arg V₁)) ts} {as₂ : Tup (Arg (Arg V₂)) ts}
    (has : TRel (ArgRel G₀) as₁ as₂) :
    tupImms? (flattenArgs as₁) = tupImms? (flattenArgs as₂) := by
  induction has with
  | nil => rfl
  | cons ha _ ih =>
    dsimp only [tupMapArg, tupImms?]
    rw [flattenArg_imm?_eq hG ha, ih]

private theorem valTupToArgs_zip_val :
    {ts : List Ty} → (xs : Tup Val ts) →
    ∀ p ∈ Tup.zip (valTupToArgs (V := Val) xs) xs, p.2.1.val = p.2.2
  | [], (), _, hp => nomatch hp
  | _ :: _, (_, xs), _, hp => by
    cases hp with
    | head => rfl
    | tail _ hp => exact valTupToArgs_zip_val xs _ hp

private theorem tupImms?_eq_vals :
    {ts : List Ty} → {args : Tup (Arg Val) ts} → {imms : Tup Val ts} →
    tupImms? args = some imms → vals args = imms
  | [], (), (), _ => rfl
  | _ :: _, (.var _, _), _, h => by simp [tupImms?, Arg.imm?] at h
  | _ :: _, (.imm _, as), (_, ims), h => by
    cases hta : tupImms? as with
    | none => simp [tupImms?, Arg.imm?, hta] at h
    | some tail =>
      simp only [tupImms?, Arg.imm?, hta, Option.pure_def] at h
      rcases h with ⟨rfl, rfl⟩
      exact Prod.ext rfl (tupImms?_eq_vals hta)

private theorem constFoldExpr_let_none {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    {sig ts : List Ty} {code : OpCode sig ts} {args : Tup (Arg (Arg V)) sig}
    {k : Tup (Arg V) ts → Expr (Arg V) L rs}
    (h : tupImms? (flattenArgs args) = none) :
    constFoldExpr (.let_ ⟨code, args⟩ k) =
      .let_ ⟨code, flattenArgs args⟩ (fun xs => constFoldExpr (k (toArgTup xs))) := by
  conv => lhs; unfold constFoldExpr
  simp only [flattenOp, h]

private theorem constFoldExpr_let_some_none {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    {sig ts : List Ty} {code : OpCode sig ts} {args : Tup (Arg (Arg V)) sig}
    {k : Tup (Arg V) ts → Expr (Arg V) L rs} {imms : Tup Val sig}
    (h1 : tupImms? (flattenArgs args) = some imms) (h2 : OpCode.eval? code imms = none) :
    constFoldExpr (.let_ ⟨code, args⟩ k) =
      .let_ ⟨code, flattenArgs args⟩ (fun xs => constFoldExpr (k (toArgTup xs))) := by
  conv => lhs; unfold constFoldExpr
  simp only [flattenOp, h1, h2]

private theorem constFoldExpr_let_some_some {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    {sig ts : List Ty} {code : OpCode sig ts} {args : Tup (Arg (Arg V)) sig}
    {k : Tup (Arg V) ts → Expr (Arg V) L rs} {imms : Tup Val sig} {res : Tup Val ts}
    (h1 : tupImms? (flattenArgs args) = some imms) (h2 : OpCode.eval? code imms = some res) :
    constFoldExpr (.let_ ⟨code, args⟩ k) = constFoldExpr (k (valTupToArgs res)) := by
  conv => lhs; unfold constFoldExpr
  simp only [flattenOp, h1, h2]

@[simp] private theorem constFoldBlocks_get {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    {sig : List (List Ty)} → {ts : List Ty} → (bs : Blocks (Arg V) L rs sig) →
    (i : Member ts sig) → (xs : Tup V ts) →
    (constFoldBlocks bs).get i xs = constFoldExpr (bs.get i (toArgTup xs))
  | _, _, .cons _ _, .here, _ => rfl
  | _, _, .cons _ bs, .there i, xs => constFoldBlocks_get bs i xs

private theorem constFoldExpr_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G₀ : Ctx (Arg V₁) (Arg V₂)} {D₀ : Ctx L₁ L₂}
    {e₁ : Expr (Arg V₁) L₁ rs} {e₂ : Expr (Arg V₂) L₂ rs}
    (hwf : Wf G₀ D₀ e₁ e₂) :
    ∀ {G : Ctx V₁ V₂}, CFRelG G₀ G →
      Wf G D₀ (constFoldExpr e₁) (constFoldExpr e₂) := by
  induction hwf using Wf.induct with
  | @let_ G₀ D₀ ts op₁ op₂ k₁ k₂ hop _ ih =>
    intro G hG
    cases hop with
    | mk code hargs =>
      rename_i args₁ args₂
      have hop' : OpRel G ⟨code, flattenArgs args₁⟩ ⟨code, flattenArgs args₂⟩ :=
        .mk code (TRel.flattenArgs (fun p hp => (hG p hp).1) hargs)
      have himms : tupImms? (flattenArgs args₁) = tupImms? (flattenArgs args₂) :=
        tupImms?_flattenArgs_eq hG hargs
      cases hti : tupImms? (flattenArgs args₁) with
      | none =>
        rw [constFoldExpr_let_none hti, constFoldExpr_let_none (himms ▸ hti)]
        exact .let_ hop' fun xs₁ xs₂ =>
          ih (toArgTup xs₁) (toArgTup xs₂)
            ((CFRelG.toArgTup xs₁ xs₂).append (hG.weaken fun _ hq => List.mem_append_right _ hq))
      | some imms =>
        cases hev : OpCode.eval? code imms with
        | none =>
          rw [constFoldExpr_let_some_none hti hev, constFoldExpr_let_some_none (himms ▸ hti) hev]
          exact .let_ hop' fun xs₁ xs₂ =>
            ih (toArgTup xs₁) (toArgTup xs₂)
              ((CFRelG.toArgTup xs₁ xs₂).append (hG.weaken fun _ hq => List.mem_append_right _ hq))
        | some res =>
          rw [constFoldExpr_let_some_some hti hev, constFoldExpr_let_some_some (himms ▸ hti) hev]
          exact ih (valTupToArgs res) (valTupToArgs res)
            ((CFRelG.valTupToArgs res).append hG)
  | @load G₀ D₀ t a₁ a₂ k₁ k₂ ha _ ih =>
    intro G hG
    dsimp only [constFoldExpr]
    exact .load t (ha.flattenArg (fun p hp => (hG p hp).1)) fun v₁ v₂ =>
      ih (.var v₁) (.var v₂)
        ((CFRelG.singleVar v₁ v₂).append (hG.weaken fun _ hq => List.mem_cons_of_mem _ hq))
  | store hv ha _ ih =>
    intro G hG
    dsimp only [constFoldExpr]
    exact .store (hv.flattenArg (fun p hp => (hG p hp).1))
      (ha.flattenArg (fun p hp => (hG p hp).1)) (ih hG)
  | call f hargs _ ih =>
    intro G hG
    dsimp only [constFoldExpr]
    exact .call f (TRel.flattenArgs (fun p hp => (hG p hp).1) hargs) fun xs₁ xs₂ =>
      ih (toArgTup xs₁) (toArgTup xs₂)
        ((CFRelG.toArgTup xs₁ xs₂).append (hG.weaken fun _ hq => List.mem_append_right _ hq))
  | @jnz G₀ D₀ c₁ c₂ t₁ t₂ e₁ e₂ hc _ _ iht ihe =>
    intro G hG
    have hc' : ArgRel G .bool (flattenArg c₁) (flattenArg c₂) :=
      hc.flattenArg (fun p hp => (hG p hp).1)
    dsimp only [constFoldExpr]
    generalize flattenArg c₁ = fc₁ at hc' ⊢
    generalize flattenArg c₂ = fc₂ at hc' ⊢
    cases hc' with
    | imm b =>
      cases b
      · exact ihe hG
      · exact iht hG
    | var hm =>
      exact .jnz (.var hm) (iht hG) (ihe hG)
  | jump hj hargs =>
    intro G hG
    exact .jump hj (TRel.flattenArgs (fun p hp => (hG p hp).1) hargs)
  | ret hvs =>
    intro G hG
    exact .ret (TRel.flattenArgs (fun p hp => (hG p hp).1) hvs)
  | exit f hargs =>
    intro G hG
    exact .exit f (TRel.flattenArgs (fun p hp => (hG p hp).1) hargs)
  | hlt => intro _ _; exact .hlt
  | @group G₀ D₀ sig b₁ b₂ k₁ k₂ _ _ ihb ihk =>
    intro G hG
    dsimp only [constFoldExpr]
    refine .group (fun Js₁ Js₂ => WfB.of_get fun i xs₁ xs₂ => ?_) (fun Js₁ Js₂ => ?_)
    · rw [constFoldBlocks_get, constFoldBlocks_get]
      exact ihb Js₁ Js₂ i (toArgTup xs₁) (toArgTup xs₂)
        ((CFRelG.toArgTup xs₁ xs₂).append (hG.weaken fun _ hq => List.mem_append_right _ hq))
    · exact ihk Js₁ Js₂ hG

private theorem constFoldExpr_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {G : Ctx (Arg Val) Val} {D : Ctx Cont Cont}
    {e₁ : Expr (Arg Val) Cont rs} {e₂ : Expr Val Cont rs} (hwf : Wf G D e₁ e₂) :
    ∀ m, (∀ p ∈ G, p.2.1.val = p.2.2) → (∀ p ∈ D, p.2.1 = p.2.2) →
      wp Γ Q X e₂ m → wp Γ Q X (constFoldExpr e₁) m := by
  induction hwf using Wf.induct with
  | @let_ G D ts op₁ op₂ k₁ k₂ hop _ ih =>
    intro m hG hD h
    cases hop with
    | mk code hargs =>
      rename_i args₁ args₂
      have hvals : vals (flattenArgs args₁) = vals args₂ :=
        flattenArgs_vals hG hargs
      dsimp only [wp, Op.wp] at h
      cases hti : tupImms? (flattenArgs args₁) with
      | none =>
        rw [constFoldExpr_let_none hti]
        dsimp only [wp, Op.wp]
        rw [hvals]
        exact OpCode.wp_mono _ _ (fun r hr =>
          ih (toArgTup r) r m (ctx_val_append (toArgTup_zip_val r) hG) hD hr) h
      | some imms =>
        cases hev : OpCode.eval? code imms with
        | none =>
          rw [constFoldExpr_let_some_none hti hev]
          dsimp only [wp, Op.wp]
          rw [hvals]
          exact OpCode.wp_mono _ _ (fun r hr =>
            ih (toArgTup r) r m (ctx_val_append (toArgTup_zip_val r) hG) hD hr) h
        | some res =>
          rw [constFoldExpr_let_some_some hti hev]
          have him : vals args₂ = imms := by rw [← hvals, tupImms?_eq_vals hti]
          rw [him] at h
          have hk : wp Γ Q X (k₂ res) m :=
            OpCode.eval?_sound code imms (fun r => wp Γ Q X (k₂ r) m) hev h
          exact ih (valTupToArgs res) res m (ctx_val_append (valTupToArgs_zip_val res) hG) hD hk
  | load _ ha _ ih =>
    intro m hG hD ⟨v, hv, h⟩
    dsimp only [constFoldExpr, wp]
    rw [flattenArg_val hG ha]
    exact ⟨v, hv, ih (.var v) v m (ctx_val_cons_var hG v) hD h⟩
  | store hv ha _ ih =>
    intro m hG hD ⟨hok, h⟩
    dsimp only [constFoldExpr, wp]
    rw [flattenArg_val hG ha, flattenArg_val hG hv]
    exact ⟨hok, ih _ hG hD h⟩
  | call f hargs _ ih =>
    intro m hG hD ⟨P, E, hcall, hP, hE⟩
    dsimp only [constFoldExpr, wp]
    rw [flattenArgs_vals hG hargs]
    exact ⟨P, E, hcall, fun r m' hr =>
      ih (toArgTup r) r m' (ctx_val_append (toArgTup_zip_val r) hG) hD (hP r m' hr), hE⟩
  | jnz hc _ _ iht ihe =>
    intro m hG hD ⟨ht, he⟩
    have hv := flattenArg_val hG hc
    dsimp only [constFoldExpr]
    cases hfa : flattenArg _ with
    | imm b =>
      rw [hfa] at hv
      cases b
      · exact ihe m hG hD (he (by simpa [Arg.val] using hv))
      · exact iht m hG hD (ht (by simpa [Arg.val] using hv))
    | var v =>
      dsimp only [wp]
      rw [← hfa, hv]
      exact ⟨fun h => iht m hG hD (ht h), fun h => ihe m hG hD (he h)⟩
  | jump hj hargs =>
    intro m hG hD h
    dsimp only [constFoldExpr, wp] at h ⊢
    rw [flattenArgs_vals hG hargs]
    have hj' := hD _ hj
    dsimp only at hj'
    rw [hj']
    exact h
  | ret hvs =>
    intro m hG _ h
    dsimp only [constFoldExpr, wp] at h ⊢
    rw [flattenArgs_vals hG hvs]
    exact h
  | exit f hargs =>
    intro m hG _ h
    dsimp only [constFoldExpr, wp] at h ⊢
    rw [flattenArgs_vals hG hargs]
    exact h
  | hlt => intro _ _ _ h; exact h
  | @group G' D' sig b₁ b₂ k₁ k₂ _ _ ihb ihk =>
    intro m hG hD h Js hcl
    dsimp only [constFoldExpr, wp]
    have hD' : ∀ p ∈ Tup.zip Js Js ++ D', p.2.1 = p.2.2 := by
      intro p hp
      rcases List.mem_append.1 hp with hp | hp
      · exact mem_zip_self Js p hp
      · exact hD p hp
    refine ihk Js Js m hG hD' (h Js ?_)
    rw [closed_iff] at hcl ⊢
    intro _ i xs m' hb
    exact hcl i xs m' (by
      rw [constFoldBlocks_get]
      exact ihb Js Js i (toArgTup xs) xs m'
        (ctx_val_append (toArgTup_zip_val xs) hG) hD' hb)
where
  mem_zip_self : {sig : List (List Ty)} → (Js : Tup Cont sig) →
      ∀ p ∈ Tup.zip Js Js, p.2.1 = p.2.2
    | [], (), _, hp => nomatch hp
    | _ :: _, (_, js), _, hp => by
      cases hp with
      | head => rfl
      | tail _ hp => exact mem_zip_self js _ hp
end ConstFoldProofs

/-- `Func.constFoldNoCmp` preserves relational well-formedness. -/
theorem Func.constFoldNoCmp_wf {as rs : List Ty} {f : Func as rs} (hf : f.Wf) :
    (Func.constFoldNoCmp f).Wf := by
  intro V₁ V₂ L₁ L₂ xs₁ xs₂
  exact constFoldExpr_wf (hf (Arg V₁) (Arg V₂) L₁ L₂ (toArgTup xs₁) (toArgTup xs₂))
    (by simpa using CFRelG.toArgTup (G := []) xs₁ xs₂)

/-- `Func.constFoldNoCmp` refines function contracts. -/
theorem Func.constFoldNoCmp_spec {as rs : List Ty} {f : Func as rs} (hf : f.Wf) {Γ : Env}
    {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Func.spec Γ f xs m Q X) : Func.spec Γ (Func.constFoldNoCmp f) xs m Q X :=
  constFoldExpr_wp (hf (Arg Val) Val Cont Cont (toArgTup xs) xs) m
    (toArgTup_zip_val xs) (fun _ hp => nomatch hp) h

/-! ## Generic conditional pass combinators -/

/-- Conditionally apply `pass` when `run = true`, otherwise return `f` unchanged. -/
def applyPassIf {as rs : List Ty} (run : Bool) (pass : Func as rs → Func as rs)
    (f : Func as rs) : Func as rs :=
  if run then pass f else f

theorem applyPassIf_wf {as rs : List Ty} (run : Bool) (pass : Func as rs → Func as rs)
    (hp : ∀ {g : Func as rs}, g.Wf → (pass g).Wf) {f : Func as rs} (hf : f.Wf) :
    (applyPassIf run pass f).Wf := by
  cases run
  · exact hf
  · exact hp hf

theorem applyPassIf_spec {as rs : List Ty} (run : Bool) (pass : Func as rs → Func as rs)
    (hp : ∀ {g : Func as rs}, g.Wf → ∀ {Γ : Env} {xs : Tup Val as} {m : Mem 64}
      {Q : Post rs} {X : XPost}, Func.spec Γ g xs m Q X → Func.spec Γ (pass g) xs m Q X)
    {f : Func as rs} (hf : f.Wf) {Γ : Env} {xs : Tup Val as} {m : Mem 64}
    {Q : Post rs} {X : XPost} (h : Func.spec Γ f xs m Q X) :
    Func.spec Γ (applyPassIf run pass f) xs m Q X := by
  cases run
  · exact h
  · exact hp hf h

/-! ## Policy-parameterized mid-end passes (`Func.*Policy`, `Fn.midPolicy`) -/

/-- Run `Func.fold` when `pol.noNormCmpImm = false`, or `Func.constFoldNoCmp` otherwise. -/
def Func.foldPolicy (pol : SnippetOptPolicy) {as rs : List Ty} (f : Func as rs) : Func as rs :=
  if pol.noNormCmpImm then Func.constFoldNoCmp f else Func.fold f

theorem Func.foldPolicy_wf (pol : SnippetOptPolicy) {as rs : List Ty} {f : Func as rs}
    (hf : f.Wf) : (Func.foldPolicy pol f).Wf := by
  dsimp only [Func.foldPolicy]
  split
  · exact Func.constFoldNoCmp_wf hf
  · exact Func.fold_wf hf

theorem Func.foldPolicy_spec (pol : SnippetOptPolicy) {as rs : List Ty} {f : Func as rs}
    (hf : f.Wf) {Γ : Env} {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Func.spec Γ f xs m Q X) : Func.spec Γ (Func.foldPolicy pol f) xs m Q X := by
  dsimp only [Func.foldPolicy]
  split
  · exact Func.constFoldNoCmp_spec hf h
  · exact Func.fold_spec hf h

/-- Policy-parameterized pre-`Legal` value core (`foldPolicy → canon → copy → gvn → copy →
foldPolicy`). -/
def Func.earlyCorePolicy (pol : SnippetOptPolicy) {as rs : List Ty} (f : Func as rs) :
    Func as rs :=
  Func.foldPolicy pol (Func.copy (Func.gvn (Func.copy (Func.canon (Func.foldPolicy pol f)))))

theorem Func.earlyCorePolicy_wf (pol : SnippetOptPolicy) {as rs : List Ty} {f : Func as rs}
    (hf : f.Wf) : (Func.earlyCorePolicy pol f).Wf :=
  Func.foldPolicy_wf pol (Func.copy_wf (Func.gvn_wf (Func.copy_wf
    (Func.canon_wf (Func.foldPolicy_wf pol hf)))))

theorem Func.earlyCorePolicy_spec (pol : SnippetOptPolicy) {as rs : List Ty} {f : Func as rs}
    (hf : f.Wf) {Γ : Env} {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Func.spec Γ f xs m Q X) : Func.spec Γ (Func.earlyCorePolicy pol f) xs m Q X := by
  have hf1 := Func.foldPolicy_wf pol hf
  have hs1 := Func.foldPolicy_spec pol hf h
  have hf2 := Func.canon_wf hf1
  have hs2 := Func.canon_spec hf1 hs1
  have hf3 := Func.copy_wf hf2
  have hs3 := Func.copy_spec hf2 hs2
  have hf4 := Func.gvn_wf hf3
  have hs4 := Func.gvn_spec hf3 hs3
  have hf5 := Func.copy_wf hf4
  have hs5 := Func.copy_spec hf4 hs4
  exact Func.foldPolicy_spec pol hf5 hs5

/-- Policy-parameterized pre-`Legal` mid-end pipeline, matching `Func.earlyOpt` when
`pol = .default`. -/
def Func.earlyOptPolicy (pol : SnippetOptPolicy) {as rs : List Ty} (f : Func as rs) :
    Func as rs :=
  let f1 := Func.earlyCorePolicy pol f
  let f2 := applyPassIf (!pol.noIfOpt) Func.ifOpt f1
  let f3 := applyPassIf (!pol.noSimplifyGrp) Func.simplifyGroupFast f2
  let f4 := applyPassIf (!pol.noPeel) (Func.peelFast · 24) f3
  let f5 := applyPassIf (!pol.noPeel && !pol.noZeroPeel)
    (Func.zeroPeelWith { peelBudget := 24 }) f4
  Func.renorm (Func.dceP (Func.foldPolicy pol (Func.copy f5)))

theorem Func.earlyOptPolicy_wf (pol : SnippetOptPolicy) {as rs : List Ty} {f : Func as rs}
    (_hf : f.Wf) : (Func.earlyOptPolicy pol f).Wf :=
  Func.renorm_wf _

theorem Func.earlyOptPolicy_spec (pol : SnippetOptPolicy) {as rs : List Ty} {f : Func as rs}
    (hf : f.Wf) {Γ : Env} {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Func.spec Γ f xs m Q X) : Func.spec Γ (Func.earlyOptPolicy pol f) xs m Q X := by
  dsimp only [Func.earlyOptPolicy]
  have hf1 := Func.earlyCorePolicy_wf pol hf
  have hs1 := Func.earlyCorePolicy_spec pol hf h
  have hf2 := applyPassIf_wf (!pol.noIfOpt) Func.ifOpt Func.ifOpt_wf hf1
  have hs2 := applyPassIf_spec (!pol.noIfOpt) Func.ifOpt Func.ifOpt_spec hf1 hs1
  have hf3 := applyPassIf_wf (!pol.noSimplifyGrp) Func.simplifyGroupFast
    (fun {g} _ => Func.simplifyGroupFast_wf g) hf2
  have hs3 := applyPassIf_spec (!pol.noSimplifyGrp) Func.simplifyGroupFast
    Func.simplifyGroupFast_spec hf2 hs2
  have hf4 := applyPassIf_wf (!pol.noPeel) (Func.peelFast · 24)
    (fun {g} _ => Func.peelFast_wf g 24) hf3
  have hs4 := applyPassIf_spec (!pol.noPeel) (Func.peelFast · 24)
    (fun hg => Func.peelFast_spec hg 24) hf3 hs3
  have hf5 := applyPassIf_wf (!pol.noPeel && !pol.noZeroPeel)
    (Func.zeroPeelWith { peelBudget := 24 }) (Func.zeroPeelWith_wf { peelBudget := 24 }) hf4
  have hs5 := applyPassIf_spec (!pol.noPeel && !pol.noZeroPeel)
    (Func.zeroPeelWith { peelBudget := 24 }) (Func.zeroPeelWith_spec { peelBudget := 24 }) hf4 hs4
  have hf6 := Func.copy_wf hf5
  have hs6 := Func.copy_spec hf5 hs5
  have hf7 := Func.foldPolicy_wf pol hf6
  have hs7 := Func.foldPolicy_spec pol hf6 hs6
  have hf8 := Func.dceP_wf hf7
  have hs8 := Func.dceP_spec hf7 hs7
  exact Func.renorm_spec hf8 hs8

/-- Policy-parameterized post-`Legal` pre-`renorm` value core. -/
def Func.lateCorePrePolicy (pol : SnippetOptPolicy) {as rs : List Ty} (f : Func as rs) :
    Func as rs :=
  Func.copy (Func.divConst (Func.canon (Func.foldPolicy pol f)))

theorem Func.lateCorePrePolicy_wf (pol : SnippetOptPolicy) {as rs : List Ty} {f : Func as rs}
    (hf : f.Wf) : (Func.lateCorePrePolicy pol f).Wf :=
  Func.copy_wf (Func.divConst_wf (Func.canon_wf (Func.foldPolicy_wf pol hf)))

theorem Func.lateCorePrePolicy_spec (pol : SnippetOptPolicy) {as rs : List Ty} {f : Func as rs}
    (hf : f.Wf) {Γ : Env} {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Func.spec Γ f xs m Q X) : Func.spec Γ (Func.lateCorePrePolicy pol f) xs m Q X := by
  have hf1 := Func.foldPolicy_wf pol hf
  have hs1 := Func.foldPolicy_spec pol hf h
  have hf2 := Func.canon_wf hf1
  have hs2 := Func.canon_spec hf1 hs1
  have hf3 := Func.divConst_wf hf2
  have hs3 := Func.divConst_spec hf2 hs2
  exact Func.copy_spec hf3 hs3

/-- Policy-parameterized post-`Legal` post-`renorm` memory/known-bits core. -/
def Func.lateCorePostPolicy (pol : SnippetOptPolicy) {as rs : List Ty} (f : Func as rs) :
    Func as rs :=
  Func.foldPolicy pol (Func.assumeBits (Func.gvn (Func.memLoad f)))

theorem Func.lateCorePostPolicy_wf (pol : SnippetOptPolicy) {as rs : List Ty} {f : Func as rs}
    (hf : f.Wf) : (Func.lateCorePostPolicy pol f).Wf :=
  Func.foldPolicy_wf pol (Func.assumeBits_wf (Func.gvn_wf (Func.memLoad_wf hf)))

theorem Func.lateCorePostPolicy_spec (pol : SnippetOptPolicy) {as rs : List Ty} {f : Func as rs}
    (hf : f.Wf) {Γ : Env} {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Func.spec Γ f xs m Q X) : Func.spec Γ (Func.lateCorePostPolicy pol f) xs m Q X := by
  have hf1 := Func.memLoad_wf hf
  have hs1 := Func.memLoad_spec hf h
  have hf2 := Func.gvn_wf hf1
  have hs2 := Func.gvn_spec hf1 hs1
  have hf3 := Func.assumeBits_wf hf2
  have hs3 := Func.assumeBits_spec hf2 hs2
  exact Func.foldPolicy_spec pol hf3 hs3

/-- Policy-parameterized post-`Legal` value/memory core. -/
def Func.lateCorePolicy (pol : SnippetOptPolicy) {as rs : List Ty} (f : Func as rs) :
    Func as rs :=
  Func.lateCorePostPolicy pol (Func.renorm (Func.lateCorePrePolicy pol f))

theorem Func.lateCorePolicy_wf (pol : SnippetOptPolicy) {as rs : List Ty} {f : Func as rs}
    (_hf : f.Wf) : (Func.lateCorePolicy pol f).Wf :=
  Func.lateCorePostPolicy_wf pol (Func.renorm_wf _)

theorem Func.lateCorePolicy_spec (pol : SnippetOptPolicy) {as rs : List Ty} {f : Func as rs}
    (hf : f.Wf) {Γ : Env} {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Func.spec Γ f xs m Q X) : Func.spec Γ (Func.lateCorePolicy pol f) xs m Q X :=
  Func.lateCorePostPolicy_spec pol (Func.renorm_wf _)
    (Func.renorm_spec (Func.lateCorePrePolicy_wf pol hf) (Func.lateCorePrePolicy_spec pol hf h))

/-- Policy-parameterized post-`Legal` pre-`licm` CFG/cleanup core. -/
def Func.lateCfgPrePolicy (pol : SnippetOptPolicy) {as rs : List Ty} (f : Func as rs) :
    Func as rs :=
  let f1 := applyPassIf (!pol.noIfOpt) Func.ifOptBits f
  let f2 := applyPassIf (!pol.noSimplifyGrp) Func.simplifyGroupFast f1
  Func.gvn (Func.foldPolicy pol (Func.assumeElim (Func.deadLoadElim f2)))

theorem Func.lateCfgPrePolicy_wf (pol : SnippetOptPolicy) {as rs : List Ty} {f : Func as rs}
    (hf : f.Wf) : (Func.lateCfgPrePolicy pol f).Wf := by
  dsimp only [Func.lateCfgPrePolicy]
  have hf1 := applyPassIf_wf (!pol.noIfOpt) Func.ifOptBits Func.ifOptBits_wf hf
  have hf2 := applyPassIf_wf (!pol.noSimplifyGrp) Func.simplifyGroupFast
    (fun {g} _ => Func.simplifyGroupFast_wf g) hf1
  exact Func.gvn_wf (Func.foldPolicy_wf pol (Func.assumeElim_wf (Func.deadLoadElim_wf hf2)))

theorem Func.lateCfgPrePolicy_spec (pol : SnippetOptPolicy) {as rs : List Ty} {f : Func as rs}
    (hf : f.Wf) {Γ : Env} {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Func.spec Γ f xs m Q X) : Func.spec Γ (Func.lateCfgPrePolicy pol f) xs m Q X := by
  dsimp only [Func.lateCfgPrePolicy]
  have hf1 := applyPassIf_wf (!pol.noIfOpt) Func.ifOptBits Func.ifOptBits_wf hf
  have hs1 := applyPassIf_spec (!pol.noIfOpt) Func.ifOptBits Func.ifOptBits_spec hf h
  have hf2 := applyPassIf_wf (!pol.noSimplifyGrp) Func.simplifyGroupFast
    (fun {g} _ => Func.simplifyGroupFast_wf g) hf1
  have hs2 := applyPassIf_spec (!pol.noSimplifyGrp) Func.simplifyGroupFast
    Func.simplifyGroupFast_spec hf1 hs1
  have hf3 := Func.deadLoadElim_wf hf2
  have hs3 := Func.deadLoadElim_spec hf2 hs2
  have hf4 := Func.assumeElim_wf hf3
  have hs4 := Func.assumeElim_spec hf3 hs3
  have hf5 := Func.foldPolicy_wf pol hf4
  have hs5 := Func.foldPolicy_spec pol hf4 hs4
  exact Func.gvn_spec hf5 hs5

/-- Policy-parameterized post-`licm` core (`noHoistOut` disables `licm`). -/
def Func.lateCfgPostPolicy (pol : SnippetOptPolicy) {as rs : List Ty} (f : Func as rs) :
    Func as rs :=
  Func.dceP (applyPassIf (!pol.noHoistOut) Func.licm f)

theorem Func.lateCfgPostPolicy_wf (pol : SnippetOptPolicy) {as rs : List Ty} {f : Func as rs}
    (hf : f.Wf) : (Func.lateCfgPostPolicy pol f).Wf :=
  Func.dceP_wf (applyPassIf_wf (!pol.noHoistOut) Func.licm Func.licm_wf hf)

theorem Func.lateCfgPostPolicy_spec (pol : SnippetOptPolicy) {as rs : List Ty} {f : Func as rs}
    (hf : f.Wf) {Γ : Env} {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Func.spec Γ f xs m Q X) : Func.spec Γ (Func.lateCfgPostPolicy pol f) xs m Q X :=
  Func.dceP_spec (applyPassIf_wf (!pol.noHoistOut) Func.licm Func.licm_wf hf)
    (applyPassIf_spec (!pol.noHoistOut) Func.licm Func.licm_spec hf h)

/-- Policy-parameterized loop-rotation + epilogue-merge tail (`noHoistOut`, `noRotate`,
`noMergeRets`). -/
def Func.lateLoopRotatePolicy (pol : SnippetOptPolicy) {as rs : List Ty} (f : Func as rs) :
    Func as rs :=
  let f1 := Func.lateCfgPostPolicy pol f
  let f2 := applyPassIf (!pol.noRotate) Func.loopRotate f1
  applyPassIf (!pol.noMergeRets) Func.mergeRets f2

theorem Func.lateLoopRotatePolicy_wf (pol : SnippetOptPolicy) {as rs : List Ty} {f : Func as rs}
    (hf : f.Wf) : (Func.lateLoopRotatePolicy pol f).Wf := by
  dsimp only [Func.lateLoopRotatePolicy]
  have hf1 := Func.lateCfgPostPolicy_wf pol hf
  have hf2 := applyPassIf_wf (!pol.noRotate) Func.loopRotate Func.loopRotate_wf hf1
  exact applyPassIf_wf (!pol.noMergeRets) Func.mergeRets Func.mergeRets_wf hf2

theorem Func.lateLoopRotatePolicy_spec (pol : SnippetOptPolicy) {as rs : List Ty} {f : Func as rs}
    (hf : f.Wf) {Γ : Env} {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Func.spec Γ f xs m Q X) : Func.spec Γ (Func.lateLoopRotatePolicy pol f) xs m Q X := by
  dsimp only [Func.lateLoopRotatePolicy]
  have hf1 := Func.lateCfgPostPolicy_wf pol hf
  have hs1 := Func.lateCfgPostPolicy_spec pol hf h
  have hf2 := applyPassIf_wf (!pol.noRotate) Func.loopRotate Func.loopRotate_wf hf1
  have hs2 := applyPassIf_spec (!pol.noRotate) Func.loopRotate
    (fun hg => Func.loopRotate_spec hg LoopRotate.defaultRotConfig) hf1 hs1
  exact applyPassIf_spec (!pol.noMergeRets) Func.mergeRets Func.mergeRets_spec hf2 hs2

/-- Policy-parameterized post-`Legal` pipeline, matching `Func.lateOpt` when `pol = .default`. -/
def Func.lateOptPolicy (pol : SnippetOptPolicy) {as rs : List Ty} (f : Func as rs) :
    Func as rs :=
  let s1 := Func.renorm (Func.lateCorePrePolicy pol f)
  let s2 := Func.renorm (Func.lateCorePostPolicy pol s1)
  let s3 := Func.renorm (Func.lateCfgPrePolicy pol s2)
  Func.renorm (Func.lateLoopRotatePolicy pol s3)

theorem Func.lateOptPolicy_wf (pol : SnippetOptPolicy) {as rs : List Ty} {f : Func as rs}
    (_hf : f.Wf) : (Func.lateOptPolicy pol f).Wf :=
  Func.renorm_wf _

theorem Func.lateOptPolicy_spec (pol : SnippetOptPolicy) {as rs : List Ty} {f : Func as rs}
    (hf : f.Wf) {Γ : Env} {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Func.spec Γ f xs m Q X) : Func.spec Γ (Func.lateOptPolicy pol f) xs m Q X := by
  dsimp only [Func.lateOptPolicy]
  have h1 := Func.renorm_spec (Func.lateCorePrePolicy_wf pol hf)
    (Func.lateCorePrePolicy_spec pol hf h)
  have h2 := Func.renorm_spec (Func.lateCorePostPolicy_wf pol (Func.renorm_wf _))
    (Func.lateCorePostPolicy_spec pol (Func.renorm_wf _) h1)
  have h3 := Func.renorm_spec (Func.lateCfgPrePolicy_wf pol (Func.renorm_wf _))
    (Func.lateCfgPrePolicy_spec pol (Func.renorm_wf _) h2)
  exact Func.renorm_spec (Func.lateLoopRotatePolicy_wf pol (Func.renorm_wf _))
    (Func.lateLoopRotatePolicy_spec pol (Func.renorm_wf _) h3)

/-! ## Named function stage wrappers (`Fn.earlyOptPolicy`, `Fn.midPolicy`) -/

/-- Run `Func.earlyOptPolicy pol` on a named function. -/
def Fn.earlyOptPolicy (pol : SnippetOptPolicy) (fn : Fn) : Fn :=
  ⟨fn.name, fn.as, fn.rs, Func.earlyOptPolicy pol fn.body⟩

/-- Run `Func.lateOptPolicy pol` on a named function. -/
def Fn.lateOptPolicy (pol : SnippetOptPolicy) (fn : Fn) : Fn :=
  ⟨fn.name, fn.as, fn.rs, Func.lateOptPolicy pol fn.body⟩

/-- Materialize `Func.lateOptPolicy pol` starting from a post-`earlyOptPolicy` function. -/
def Fn.midFromEarlyPolicy (lt : LegalTarget) (pol : SnippetOptPolicy) (ef : Fn) : Fn :=
  let lf := ef.legal lt
  ⟨ef.name, lt.legalSig ef.as, lt.legalSig ef.rs, Func.lateOptPolicy pol lf.body⟩

/-- Full staged mid-end pipeline (`earlyOptPolicy → legal lt → lateOptPolicy`) under `pol`. -/
def Fn.midPolicy (lt : LegalTarget) (pol : SnippetOptPolicy) (fn : Fn) : Fn :=
  Fn.midFromEarlyPolicy lt pol (fn.earlyOptPolicy pol)

/-- When `pol = .default`, `Func.earlyOptPolicy` equals `Func.earlyOpt`. -/
theorem Func.earlyOptPolicy_default_eq {as rs : List Ty} (f : Func as rs) :
    Func.earlyOptPolicy .default f = Func.earlyOpt f := by
  rw [Func.earlyOpt_eq, Func.earlyCore_eq]
  rfl

/-- When `pol = .default`, `Fn.midPolicy lt .default` equals `Fn.mid lt`. -/
private theorem Func.lateCorePrePolicy_default_eq {as rs : List Ty} (f : Func as rs) :
    Func.lateCorePrePolicy .default f = Func.lateCorePre f := by
  simp only [Func.lateCorePrePolicy, Func.foldPolicy, SnippetOptPolicy.default,
    Bool.false_eq_true, ite_false]
  rw [Func.lateCorePre_eq]

private theorem Func.lateCorePostPolicy_default_eq {as rs : List Ty} (f : Func as rs) :
    Func.lateCorePostPolicy .default f = Func.lateCorePost f := by
  simp only [Func.lateCorePostPolicy, Func.foldPolicy, SnippetOptPolicy.default,
    Bool.false_eq_true, ite_false]
  rw [Func.lateCorePost_eq]

private theorem Func.lateCfgPrePolicy_default_eq {as rs : List Ty} (f : Func as rs) :
    Func.lateCfgPrePolicy .default f = Func.lateCfgPre f := by
  simp only [Func.lateCfgPrePolicy, applyPassIf, SnippetOptPolicy.default, Bool.not_false,
    Bool.false_eq_true, ite_true, ite_false, Func.foldPolicy]
  rw [Func.lateCfgPre_eq]

private theorem Func.lateCfgPostPolicy_default_eq {as rs : List Ty} (f : Func as rs) :
    Func.lateCfgPostPolicy .default f = Func.lateCfgPost f := by
  simp only [Func.lateCfgPostPolicy, applyPassIf, SnippetOptPolicy.default, Bool.not_false,
    ite_true]
  rw [Func.lateCfgPost_eq]

private theorem Func.lateLoopRotatePolicy_default_eq {as rs : List Ty} (f : Func as rs) :
    Func.lateLoopRotatePolicy .default f = Func.lateLoopRotate f := by
  dsimp only [Func.lateLoopRotatePolicy]
  rw [Func.lateCfgPostPolicy_default_eq]
  simp only [applyPassIf, SnippetOptPolicy.default, Bool.not_false, ite_true]
  rw [Func.lateLoopRotate_eq]

theorem Fn.midPolicy_default_eq (lt : LegalTarget) (fn : Fn) :
    Fn.midPolicy lt .default fn = fn.mid lt := by
  dsimp only [Fn.midPolicy, Fn.midFromEarlyPolicy, Fn.mid, Fn.midFromEarly, Fn.earlyOptPolicy,
    Fn.earlyOpt]
  rw [Func.earlyOptPolicy_default_eq]
  dsimp only [Fn.legal]
  apply congrArg (Fn.mk fn.name (lt.legalSig fn.as) (lt.legalSig fn.rs))
  rw [Fn.midStage_eq]
  dsimp only [Func.lateOptPolicy]
  rw [Func.lateCorePrePolicy_default_eq, Func.lateCorePostPolicy_default_eq,
    Func.lateCfgPrePolicy_default_eq, Func.lateLoopRotatePolicy_default_eq]

/-- `Fn.midPolicy` unconditionally preserves `Fn.Wf`. -/
theorem Fn.midPolicy_wf (lt : LegalTarget) (pol : SnippetOptPolicy) {fn : Fn} (hwf : fn.Wf) :
    (fn.midPolicy lt pol).Wf := by
  have _ := hwf
  exact Func.lateOptPolicy_wf pol (Func.legal_wf lt (Func.earlyOptPolicy_wf pol hwf))

/-- End-to-end WP refinement across `Fn.midPolicy` (`earlyOptPolicy → legal lt → lateOptPolicy`). -/
theorem Fn.midPolicy_spec {lt : LegalTarget} {pol : SnippetOptPolicy} {fn : Fn} (hwf : fn.Wf)
    (hsupp : (fn.earlyOptPolicy pol).body.supportsSource lt = true) (Γ : Env)
    {xs : Tup Val fn.as} {xs' : Tup Val (lt.legalSig fn.as)} (hxs : encodeTup lt fn.as xs = xs')
    {m : Mem 64} {P : Post fn.rs} {E : XPost}
    {Q' : Post (lt.legalSig fn.rs)} {X' : XPost}
    (hQ : ∀ r m₁, legalPost lt P r m₁ → Q' r m₁)
    (hX : ∀ g cs ys m₁, legalXPost lt E g cs ys m₁ → X' g cs ys m₁)
    (hs : Func.spec Γ fn.body xs m P E) :
    Func.spec (legalEnv lt Γ) (fn.midPolicy lt pol).body xs' m Q' X' := by
  subst hxs
  have hwf1 := Func.earlyOptPolicy_wf pol hwf
  have hopt := Func.earlyOptPolicy_spec pol hwf hs
  have hleg := Func.legal_spec lt (Func.earlyOptPolicy pol fn.body) hwf1 hsupp Γ xs m P E hopt
  have hmono := Func.spec_mono (legalEnv lt Γ) (Func.legal lt (Func.earlyOptPolicy pol fn.body))
    (encodeTup lt fn.as xs) m (legalPost lt P) Q' (legalXPost lt E) X' hQ hX hleg
  exact Func.lateOptPolicy_spec pol (Func.legal_wf lt hwf1) hmono

end LeanQbe.T
