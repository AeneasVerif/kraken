module

public import LeanQbe.T.Inline
public import LeanQbe.T.Wf
public import LeanQbe.T.WP
import LeanQbe.T.OptUtilLemmas

/-!
# Correctness of Acyclic Small-Callee Inlining (`O-M1`)

* `lookupCallee_mem`: callee lookup witnesses matching `Fn` in candidate list.
* `spliceRet_wp`, `spliceRet_wf`, `spliceRet_callsOk`: soundness, well-formedness, and
  call/exit preservation of `.ret`-to-`.jump` splicing via `Wf.induct`.
* `inline_wp`, `inline_wf`, `inline_callsOk`: expression-level soundness, relational `Wf`, and
  `callsOk` preservation.
* `Func.inline_wf`, `Func.inline_spec`: closed-function specifications.
* `Module.inline_sigs`, `Module.inline_names`, `Module.inline_namesNodup`, and the flagship
  module theorem `Module.inline_ok`: `ModuleOk Γ M → ModuleOk Γ (M.inline maxSize)`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T

/-! ## Callee lookup and block-projection helpers -/

theorem lookupCallee_mem :
    ∀ {cands : List Fn} {f : Sym} {as bs : List Ty} {callee : Func as bs},
    lookupCallee cands f as bs = some callee →
    ∃ fn ∈ cands, fn.name = f ∧
      ∃ (ha : fn.as = as) (hr : fn.rs = bs), callee = (ha ▸ hr ▸ fn.body)
  | [], _, _, _, _, h => by dsimp only [lookupCallee] at h; cases h
  | fn :: rest, f, as, bs, callee, h => by
      dsimp only [lookupCallee] at h
      split at h
      · rename_i hname
        have hname' : fn.name = f := eq_of_beq hname
        cases ha_dec : listTyDecEq fn.as as with
        | isFalse _ =>
            rw [ha_dec] at h
            obtain ⟨g, hg, hgn, hga, hgr, hgb⟩ := lookupCallee_mem h
            exact ⟨g, List.mem_cons_of_mem _ hg, hgn, hga, hgr, hgb⟩
        | isTrue ha =>
            rw [ha_dec] at h
            cases hr_dec : listTyDecEq fn.rs bs with
            | isFalse _ =>
                rw [hr_dec] at h
                obtain ⟨g, hg, hgn, hga, hgr, hgb⟩ := lookupCallee_mem h
                exact ⟨g, List.mem_cons_of_mem _ hg, hgn, hga, hgr, hgb⟩
            | isTrue hr =>
                rw [hr_dec] at h
                injection h with hcal
                exact ⟨fn, List.mem_cons_self, hname', ha, hr, hcal.symm⟩
      · obtain ⟨g, hg, hgn, hga, hgr, hgb⟩ := lookupCallee_mem h
        exact ⟨g, List.mem_cons_of_mem _ hg, hgn, hga, hgr, hgb⟩

theorem spliceRetB_get {V : Ty → Type} {L : List Ty → Type} {calleeRs callerRs : List Ty}
    (joinLbl : L calleeRs) :
    {sig : List (List Ty)} → {bs : Blocks (Arg V) L calleeRs sig} →
    {ts : List Ty} → (i : Member ts sig) → (xs : Tup V ts) →
    (spliceRetB (callerRs := callerRs) joinLbl bs).get i xs =
      spliceRet joinLbl (bs.get i (toArgTup xs))
  | _, .cons _ _, _, Member.here, _ => rfl
  | _, .cons _ _, _, Member.there i, xs => spliceRetB_get joinLbl i xs

theorem inlineBlocks_get (cands : List Fn) {V : Ty → Type} {L : List Ty → Type}
    {rs : List Ty} :
    {sig : List (List Ty)} → {bs : Blocks V L rs sig} →
    {ts : List Ty} → (i : Member ts sig) → (xs : Tup V ts) →
    (inlineBlocks cands bs).get i xs = inlineExpr cands (bs.get i xs)
  | _, .cons _ _, _, Member.here, _ => rfl
  | _, .cons _ _, _, Member.there i, xs => inlineBlocks_get cands i xs

theorem Blocks.callsOk_of_get {allowed : List SigEntry} {exits : List Sym} {rs : List Ty} :
    {sig : List (List Ty)} → {bs : Blocks (fun _ => Unit) (fun _ => Unit) rs sig} →
    (∀ {ts} (i : Member ts sig), (bs.get i (Tup.units ts)).callsOk allowed exits) →
    bs.callsOk allowed exits
  | _, .nil, _ => trivial
  | _, .cons _ _, h => ⟨h .here, Blocks.callsOk_of_get fun i => h (.there i)⟩

theorem Expr.callsOk_mono {allowed allowed' : List SigEntry} {exits : List Sym}
    (hsub : ∀ s ∈ allowed, s ∈ allowed') {rs : List Ty}
    (e : Expr (fun _ => Unit) (fun _ => Unit) rs) :
    e.callsOk allowed exits → e.callsOk allowed' exits := by
  induction e using Expr.induct with
  | let_ _ _ ih => intro h; exact ih (Tup.units _) h
  | load _ _ _ ih => intro h; exact ih () h
  | store _ _ _ ih => intro h; exact ih h
  | call _ _ _ ih => intro ⟨hm, hk⟩; exact ⟨hsub _ hm, ih (Tup.units _) hk⟩
  | jnz _ _ _ iht ihe => intro ⟨ht, he⟩; exact ⟨iht ht, ihe he⟩
  | jump _ _ | ret _ | exit _ _ | hlt => intro h; exact h
  | group _ _ ihb ihk =>
      intro ⟨hb, hk⟩
      exact ⟨Blocks.callsOk_of_get fun i =>
          ihb (Tup.units _) i (Tup.units _) (Blocks.callsOk_get hb i),
        ihk (Tup.units _) hk⟩

theorem Fn.callsOk_mono {allowed allowed' : List SigEntry} {exits : List Sym}
    (hsub : ∀ s ∈ allowed, s ∈ allowed') {fn : Fn} :
    fn.callsOk allowed exits → fn.callsOk allowed' exits :=
  Expr.callsOk_mono hsub _

/-! ## Soundness, `Wf`, and `callsOk` of `spliceRet` -/

/-- Callee `.ret`-to-`.jump` splicing soundness: any `wp` of the callee body with return
postcondition `joinLbl` transfers to `wp` of `spliceRet joinLbl` under `Q`. -/
theorem spliceRet_wp {Γ : Env} {calleeRs callerRs : List Ty}
    {joinLbl : Cont calleeRs} {Q : Post callerRs} {X : XPost}
    {G : Ctx (Arg Val) Val} {D : Ctx Cont Cont}
    {e₁ : Expr (Arg Val) Cont calleeRs} {e₂ : Expr Val Cont calleeRs}
    (hwf : Wf G D e₁ e₂) :
    ∀ m, (∀ p ∈ G, p.2.1.val = p.2.2) → (∀ p ∈ D, p.2.1 = p.2.2) →
      wp Γ joinLbl X e₂ m → wp Γ Q X (spliceRet joinLbl e₁) m := by
  induction hwf using Wf.induct with
  | let_ hop _ ih =>
      intro m hG hD h
      cases hop with
      | mk code hargs =>
          dsimp only [spliceRet, wp, flattenOp, Op.wp] at h ⊢
          rw [flattenArgs_vals hG hargs]
          exact OpCode.wp_mono code (vals _)
            (fun r hr => ih (toArgTup r) r m (ctx_val_append (toArgTup_zip_val r) hG) hD hr) h
  | load t ha _ ih =>
      intro m hG hD ⟨v, hv, hk⟩
      dsimp only [spliceRet, wp]
      rw [flattenArg_val hG ha]
      exact ⟨v, hv, ih (.var v) v m (ctx_val_cons_var hG v) hD hk⟩
  | store hv ha _ ih =>
      intro m hG hD ⟨hok, hk⟩
      dsimp only [spliceRet, wp]
      rw [flattenArg_val hG hv, flattenArg_val hG ha]
      exact ⟨hok, ih _ hG hD hk⟩
  | call f hargs _ ih =>
      intro m hG hD ⟨P, E, hΓ, hP, hE⟩
      dsimp only [spliceRet, wp]
      rw [flattenArgs_vals hG hargs]
      exact ⟨P, E, hΓ,
        fun r m' hr =>
          ih (toArgTup r) r m' (ctx_val_append (toArgTup_zip_val r) hG) hD (hP r m' hr),
        hE⟩
  | jnz hc _ _ iht ihe =>
      intro m hG hD ⟨ht, he⟩
      dsimp only [spliceRet, wp]
      rw [flattenArg_val hG hc]
      exact ⟨fun h => iht m hG hD (ht h), fun h => ihe m hG hD (he h)⟩
  | jump hj hargs =>
      intro m hG hD h
      dsimp only [spliceRet, wp] at h ⊢
      have hj' := hD _ hj
      dsimp only at hj'
      rw [hj', flattenArgs_vals hG hargs]
      exact h
  | ret hvs =>
      intro m hG _ h
      dsimp only [spliceRet, wp] at h ⊢
      rw [flattenArgs_vals hG hvs]
      exact h
  | exit f hargs =>
      intro m hG _ h
      dsimp only [spliceRet, wp] at h ⊢
      rw [flattenArgs_vals hG hargs]
      exact h
  | hlt =>
      intro _ _ _ h
      exact h
  | group _ _ ihb ihk =>
      intro m hG hD h Js hc
      refine ihk Js Js m hG (tup_zip_self_eq hD Js) (h Js ?_)
      rw [closed_iff] at hc ⊢
      intro _ i xs m' hb
      exact hc i xs m' (by
        rw [spliceRetB_get]
        exact ihb Js Js i (toArgTup xs) xs m' (ctx_val_append (toArgTup_zip_val xs) hG)
          (tup_zip_self_eq hD Js) hb)

/-- `spliceRet` preserves relational well-formedness `Wf` whenever `join₁`, `join₂` are paired in
the caller label context `D`. -/
theorem spliceRet_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type}
    {calleeRs callerRs : List Ty}
    {join₁ : L₁ calleeRs} {join₂ : L₂ calleeRs}
    {G_body : Ctx (Arg V₁) (Arg V₂)} {D_body : Ctx L₁ L₂}
    {e₁ : Expr (Arg V₁) L₁ calleeRs} {e₂ : Expr (Arg V₂) L₂ calleeRs}
    (hwf : Wf G_body D_body e₁ e₂) :
    ∀ {G : Ctx V₁ V₂} {D : Ctx L₁ L₂},
      (∀ p ∈ G_body, ArgRel G p.1 p.2.1 p.2.2) →
      (∀ p ∈ D_body, p ∈ D) →
      ⟨calleeRs, join₁, join₂⟩ ∈ D →
      Wf G D (spliceRet (callerRs := callerRs) join₁ e₁)
             (spliceRet (callerRs := callerRs) join₂ e₂) := by
  induction hwf using Wf.induct with
  | let_ hop _ ih =>
      intro G D hG hD hjoin
      exact .let_ (hop.flattenOp hG) fun xs₁ xs₂ =>
        ih (toArgTup xs₁) (toArgTup xs₂)
          (ctx_argRel_append (mem_zip_toArgTup xs₁ xs₂) hG) hD hjoin
  | load t ha _ ih =>
      intro G D hG hD hjoin
      exact .load t (ha.flattenArg hG) fun v₁ v₂ =>
        ih (.var v₁) (.var v₂) (ctx_argRel_cons_var hG v₁ v₂) hD hjoin
  | store hv ha _ ih =>
      intro G D hG hD hjoin
      exact .store (hv.flattenArg hG) (ha.flattenArg hG) (ih hG hD hjoin)
  | call f hargs _ ih =>
      intro G D hG hD hjoin
      exact .call f (TRel.flattenArgs hG hargs) fun xs₁ xs₂ =>
        ih (toArgTup xs₁) (toArgTup xs₂)
          (ctx_argRel_append (mem_zip_toArgTup xs₁ xs₂) hG) hD hjoin
  | jnz hc _ _ iht ihe =>
      intro G D hG hD hjoin
      exact .jnz (hc.flattenArg hG) (iht hG hD hjoin) (ihe hG hD hjoin)
  | jump hj hargs =>
      intro G D hG hD _
      exact .jump (hD _ hj) (TRel.flattenArgs hG hargs)
  | ret hvs =>
      intro G D hG _ hjoin
      exact .jump hjoin (TRel.flattenArgs hG hvs)
  | exit f hargs =>
      intro G D hG _ _
      exact .exit f (TRel.flattenArgs hG hargs)
  | hlt =>
      intro _ _ _ _ _
      exact .hlt
  | group _ _ ihb ihk =>
      intro G D hG hD hjoin
      refine .group (fun Js₁ Js₂ => WfB.of_get fun i xs₁ xs₂ => ?_) (fun Js₁ Js₂ => ?_)
      · simp only [spliceRetB_get]
        exact ihb Js₁ Js₂ i (toArgTup xs₁) (toArgTup xs₂)
          (ctx_argRel_append (mem_zip_toArgTup xs₁ xs₂) hG)
          (append_sub_left _ hD) (List.mem_append_right _ hjoin)
      · exact ihk Js₁ Js₂ hG (append_sub_left _ hD) (List.mem_append_right _ hjoin)

/-- `spliceRet` preserves `Expr.callsOk` when the spliced callee body is `Wf`-related to its
unit-erased instantiation. -/
theorem spliceRet_callsOk {allowed : List SigEntry} {exits : List Sym}
    {calleeRs callerRs : List Ty}
    {G : Ctx (Arg (fun _ => Unit)) (fun _ => Unit)}
    {D : Ctx (fun _ => Unit) (fun _ => Unit)}
    {e₁ : Expr (Arg (fun _ => Unit)) (fun _ => Unit) calleeRs}
    {e₂ : Expr (fun _ => Unit) (fun _ => Unit) calleeRs}
    (hwf : Wf G D e₁ e₂) (hcalls : e₂.callsOk allowed exits) :
    (spliceRet (callerRs := callerRs) () e₁).callsOk allowed exits := by
  induction hwf using Wf.induct with
  | let_ _ _ ih => exact ih (toArgTup (Tup.units _)) (Tup.units _) hcalls
  | load _ _ _ ih => exact ih (.var ()) () hcalls
  | store _ _ _ ih => exact ih hcalls
  | call _ _ _ ih => exact ⟨hcalls.1, ih (toArgTup (Tup.units _)) (Tup.units _) hcalls.2⟩
  | jnz _ _ _ iht ihe => exact ⟨iht hcalls.1, ihe hcalls.2⟩
  | jump _ _ | ret _ | hlt => trivial
  | exit _ _ => exact hcalls
  | group _ _ ihb ihk =>
      refine ⟨Blocks.callsOk_of_get fun i => ?_, ihk (Tup.units _) (Tup.units _) hcalls.2⟩
      rw [spliceRetB_get]
      exact ihb (Tup.units _) (Tup.units _) i (toArgTup (Tup.units _)) (Tup.units _)
        (Blocks.callsOk_get hcalls.1 i)

/-! ## Expression- and function-level inlining correctness -/

/-- Candidate invariant needed for `inline_wp` and `Func.inline_spec`. -/
@[expose] def CandsWpOk (Γ : Env) (cands : List Fn) : Prop :=
  ∀ fn ∈ cands, fn.Wf ∧
    ∀ xs m Q X, Γ fn.name fn.as fn.rs xs m Q X → Func.wp Γ fn.body xs m Q X

/-- Candidate invariant needed for `inline_wf`. -/
@[expose] def CandsWfOk (cands : List Fn) : Prop :=
  ∀ fn ∈ cands, fn.Wf

/-- Candidate invariant needed for `inline_callsOk`. -/
@[expose] def CandsCallsOk (allowed : List SigEntry) (exits : List Sym) (cands : List Fn) : Prop :=
  ∀ fn ∈ cands, fn.Wf ∧ fn.callsOk allowed exits

theorem CandsWpOk.wfOk {Γ : Env} {cands : List Fn} (h : CandsWpOk Γ cands) : CandsWfOk cands :=
  fun fn hfn => (h fn hfn).1

/-- Expression-level WP soundness of `inlineExpr` under `CandsWpOk Γ cands`. -/
theorem inlineExpr_call (cands : List Fn) {V : Ty → Type} {L : List Ty → Type}
    {as bs rs : List Ty} (f : Sym) (args : Tup (Arg V) as) (k : Tup V bs → Expr V L rs) :
    inlineExpr cands (.call f args k) =
      match lookupCallee cands f as bs with
      | some callee =>
          .group (sig := [bs])
            (fun _ => .cons (fun xs => inlineExpr cands (k xs)) .nil)
            (fun Js => spliceRet Js.1 (callee (Arg V) L args))
      | none =>
          .call f args fun xs => inlineExpr cands (k xs) := by
  delta inlineExpr; dsimp only [Expr.brecOn, Expr.rec, inlineExpr._f]
  cases lookupCallee cands f as bs <;> rfl

theorem inline_wp {Γ : Env} {cands : List Fn} (hcands : CandsWpOk Γ cands)
    {rs : List Ty} {Q : Post rs} {X : XPost} (e : Expr Val Cont rs) :
    ∀ m, wp Γ Q X e m → wp Γ Q X (inlineExpr cands e) m := by
  induction e using Expr.induct with
  | let_ op k ih =>
      intro m h
      exact Op.wp_mono (fun r => ih r m) h
  | load t a k ih =>
      intro m ⟨v, hv, h⟩
      exact ⟨v, hv, ih v m h⟩
  | store v a k ih =>
      intro m ⟨hok, h⟩
      exact ⟨hok, ih _ h⟩
  | call f args k ih =>
      intro m ⟨P, E, hΓ, hP, hE⟩
      rw [inlineExpr_call]
      cases hlook : lookupCallee cands f _ _ with
      | none => exact ⟨P, E, hΓ, fun r m' hr => ih r m' (hP r m' hr), hE⟩
      | some callee =>
          obtain ⟨fn, hfn, rfl, ha, hr, rfl⟩ := lookupCallee_mem hlook
          subst ha; subst hr
          intro Js hc
          rcases Js with ⟨joinLbl, ⟨⟩⟩
          have hc := hc.1
          have ⟨hwf, hspec⟩ := hcands fn hfn
          have hbody : wp Γ joinLbl X (fn.body Val Cont (vals args)) m :=
            wp_mono (fun r m' hr => hc r m' (ih r m' (hP r m' hr))) hE
              (fn.body Val Cont (vals args)) m (hspec (vals args) m P E hΓ)
          exact spliceRet_wp (hwf (Arg Val) Val Cont Cont args (vals args)) m
            (ctx_zip_vals args) (fun _ hm => nomatch hm) hbody
  | jnz c t e iht ihe =>
      intro m h
      exact ⟨fun hc => iht m (h.1 hc), fun hc => ihe m (h.2 hc)⟩
  | jump _ _ | ret _ | exit _ _ | hlt =>
      intro _ h
      exact h
  | group bodies k ihb ihk =>
      intro m h Js hc
      refine ihk Js m (h Js ?_)
      rw [closed_iff] at hc ⊢
      intro _ i xs m' hb
      exact hc i xs m' (by rw [inlineBlocks_get]; exact ihb Js i xs m' hb)

/-- Relational well-formedness preservation for `inlineExpr`, proved via `Wf.induct`. -/
theorem inline_wf {cands : List Fn} (hcands : CandsWfOk cands)
    {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {e₁ : Expr V₁ L₁ rs} {e₂ : Expr V₂ L₂ rs}
    (hwf : Wf G D e₁ e₂) :
    Wf G D (inlineExpr cands e₁) (inlineExpr cands e₂) := by
  induction hwf using Wf.induct with
  | let_ hop _ ih => exact .let_ hop ih
  | load t ha _ ih => exact .load t ha ih
  | store hv ha _ ih => exact .store hv ha ih
  | call f hargs _ ih =>
      rw [inlineExpr_call, inlineExpr_call]
      cases hlook : lookupCallee cands f _ _ with
      | none => exact .call f hargs ih
      | some callee =>
          obtain ⟨fn, hfn, rfl, ha, hr, rfl⟩ := lookupCallee_mem hlook
          subst ha; subst hr
          refine .group
            (fun Js₁ Js₂ => WfB.cons (fun xs₁ xs₂ => (ih xs₁ xs₂).append_D) .nil)
            (fun Js₁ Js₂ => ?_)
          rcases Js₁ with ⟨j₁, ⟨⟩⟩; rcases Js₂ with ⟨j₂, ⟨⟩⟩
          exact spliceRet_wf (hcands fn hfn (Arg V₁) (Arg V₂) L₁ L₂ _ _)
            (fun _ hp => mem_zip_argRel hargs _ hp) (fun _ h => nomatch h) List.mem_cons_self
  | jnz hc _ _ iht ihe => exact .jnz hc iht ihe
  | jump hj hargs => exact .jump hj hargs
  | ret hvs => exact .ret hvs
  | exit f hargs => exact .exit f hargs
  | hlt => exact .hlt
  | group _ _ ihb ihk =>
      exact .group
        (fun Js₁ Js₂ => WfB.of_get fun i xs₁ xs₂ => by
          rw [inlineBlocks_get, inlineBlocks_get]
          exact ihb Js₁ Js₂ i xs₁ xs₂)
        ihk

/-- Call-signature and exit-target preservation for `inlineExpr`. -/
theorem inline_callsOk {allowed : List SigEntry} {exits : List Sym} {cands : List Fn}
    (hcands : CandsCallsOk allowed exits cands) {rs : List Ty}
    (e : Expr (fun _ => Unit) (fun _ => Unit) rs) :
    e.callsOk allowed exits → (inlineExpr cands e).callsOk allowed exits := by
  induction e using Expr.induct with
  | let_ _ _ ih => intro h; exact ih (Tup.units _) h
  | load _ _ _ ih => intro h; exact ih () h
  | store _ _ _ ih => intro h; exact ih h
  | call f args k ih =>
      intro ⟨hmem, hk⟩
      rw [inlineExpr_call]
      cases hlook : lookupCallee cands f _ _ with
      | none => exact ⟨hmem, ih (Tup.units _) hk⟩
      | some callee =>
          obtain ⟨fn, hfn, _, ha, hr, rfl⟩ := lookupCallee_mem hlook
          subst ha; subst hr
          dsimp only [Expr.callsOk, Blocks.callsOk]; simp only [and_true]
          have ⟨hwf, hcalls⟩ := hcands fn hfn
          exact ⟨ih (Tup.units _) hk,
            spliceRet_callsOk (hwf (Arg _) _ _ _ args (Tup.units fn.as)) hcalls⟩
  | jnz _ _ _ iht ihe => intro ⟨ht, he⟩; exact ⟨iht ht, ihe he⟩
  | jump _ _ | ret _ | exit _ _ | hlt => intro h; exact h
  | group _ _ ihb ihk =>
      intro ⟨hb, hk⟩
      exact ⟨Blocks.callsOk_of_get fun i => by
          rw [inlineBlocks_get]
          exact ihb (Tup.units _) i (Tup.units _) (Blocks.callsOk_get hb i),
        ihk (Tup.units _) hk⟩

/-- Closed-function well-formedness preservation for `Func.inline`. -/
theorem Func.inline_wf {cands : List Fn} (hcands : CandsWfOk cands)
    {as rs : List Ty} {f : Func as rs} (hf : f.Wf) : (Func.inline cands f).Wf :=
  fun V₁ V₂ L₁ L₂ xs₁ xs₂ => LeanQbe.T.inline_wf hcands (hf V₁ V₂ L₁ L₂ xs₁ xs₂)

/-- Closed-function WP refinement for `Func.inline`. -/
theorem Func.inline_spec {Γ : Env} {cands : List Fn} (hcands : CandsWpOk Γ cands)
    {as rs : List Ty} (f : Func as rs) {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Func.spec Γ f xs m Q X) : Func.spec Γ (Func.inline cands f) xs m Q X :=
  LeanQbe.T.inline_wp hcands (f Val Cont xs) m h

/-- Named-function well-formedness preservation for `Fn.inline`. -/
theorem Fn.inline_wf {cands : List Fn} (hcands : CandsWfOk cands) {fn : Fn} (hfn : fn.Wf) :
    (fn.inline cands).Wf :=
  Func.inline_wf hcands hfn

/-- Named-function WP refinement for `Fn.inline`. -/
theorem Fn.inline_spec {Γ : Env} {cands : List Fn} (hcands : CandsWpOk Γ cands) (fn : Fn)
    {xs : Tup Val fn.as} {m : Mem 64} {Q : Post fn.rs} {X : XPost}
    (h : Func.spec Γ fn.body xs m Q X) : Func.spec Γ (fn.inline cands).body xs m Q X :=
  Func.inline_spec hcands fn.body h

/-! ## Module signature, name uniqueness, and `Module.inlinePolicy_ok` -/

private theorem inlineFnsPolicy_map_sig (policy : InlinePolicy)
    (siteCounts loopCounts : List (Sym × Nat)) (extSigs : List SigEntry) (exits : List Sym) :
    ∀ seenSigs cands fns,
    (inlineFnsPolicy policy siteCounts loopCounts extSigs exits seenSigs cands fns).map Fn.sig =
      fns.map Fn.sig
  | _, _, [] => rfl
  | seenSigs, cands, fn :: rest => by
      dsimp only [inlineFnsPolicy, Fn.inline, Fn.sig]; simp only [List.map_cons]
      exact congrArg (_ :: ·)
        (inlineFnsPolicy_map_sig policy siteCounts loopCounts extSigs exits _ _ rest)

private theorem inlineFnsPolicy_map_name (policy : InlinePolicy)
    (siteCounts loopCounts : List (Sym × Nat)) (extSigs : List SigEntry) (exits : List Sym) :
    ∀ seenSigs cands fns,
    (inlineFnsPolicy policy siteCounts loopCounts extSigs exits seenSigs cands fns).map Fn.name =
      fns.map Fn.name
  | _, _, [] => rfl
  | seenSigs, cands, fn :: rest => by
      dsimp only [inlineFnsPolicy, Fn.inline]; simp only [List.map_cons]
      exact congrArg (_ :: ·)
        (inlineFnsPolicy_map_name policy siteCounts loopCounts extSigs exits _ _ rest)

theorem Module.inline_eq_inlinePolicy (M : Module) (maxSize : Nat := 40) :
    M.inline maxSize = M.inlinePolicy (InlinePolicy.const maxSize) :=
  rfl

theorem Module.inlinePolicy_sigs (M : Module) (policy : InlinePolicy := {}) :
    (M.inlinePolicy policy).sigs = M.sigs := by
  simp only [Module.sigs, Module.inlinePolicy, inlineFnsPolicy_map_sig]

theorem Module.inlinePolicy_names (M : Module) (policy : InlinePolicy := {}) :
    (M.inlinePolicy policy).names = M.names := by
  simp only [Module.names, Module.inlinePolicy, inlineFnsPolicy_map_name]

theorem Module.inlinePolicy_namesNodup (M : Module) (policy : InlinePolicy := {}) :
    (M.inlinePolicy policy).namesNodup = M.namesNodup := by
  simp only [Module.namesNodup, Module.inlinePolicy_names]

theorem Module.inlinePolicy_externs (M : Module) (policy : InlinePolicy := {}) :
    (M.inlinePolicy policy).externs = M.externs := rfl

theorem Module.inlinePolicy_exits (M : Module) (policy : InlinePolicy := {}) :
    (M.inlinePolicy policy).exits = M.exits := rfl

theorem Module.inline_sigs (M : Module) (maxSize : Nat := 40) :
    (M.inline maxSize).sigs = M.sigs :=
  Module.inlinePolicy_sigs M (InlinePolicy.const maxSize)

theorem Module.inline_names (M : Module) (maxSize : Nat := 40) :
    (M.inline maxSize).names = M.names :=
  Module.inlinePolicy_names M (InlinePolicy.const maxSize)

theorem Module.inline_namesNodup (M : Module) (maxSize : Nat := 40) :
    (M.inline maxSize).namesNodup = M.namesNodup :=
  Module.inlinePolicy_namesNodup M (InlinePolicy.const maxSize)

theorem Module.inline_externs (M : Module) (maxSize : Nat := 40) :
    (M.inline maxSize).externs = M.externs := rfl

theorem Module.inline_exits (M : Module) (maxSize : Nat := 40) :
    (M.inline maxSize).exits = M.exits := rfl

private theorem filterRelevantCands_mem (callerCalls : List (Sym × Nat)) (allowElevated : Bool)
    (budget : Sym → Nat) :
    ∀ (cs : List Fn) {p : Fn × Nat},
      p ∈ filterRelevantCands callerCalls allowElevated budget cs → p.1 ∈ cs
  | [], _, hp => by dsimp only [filterRelevantCands] at hp; cases hp
  | c :: cs, p, hp => by
      dsimp only [filterRelevantCands] at hp
      split at hp
      · exact List.mem_cons_of_mem _
          (filterRelevantCands_mem callerCalls allowElevated budget cs hp)
      · split at hp
        · rcases List.mem_cons.1 hp with rfl | hrest
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _
              (filterRelevantCands_mem callerCalls allowElevated budget cs hrest)
        · exact List.mem_cons_of_mem _
            (filterRelevantCands_mem callerCalls allowElevated budget cs hp)

private theorem insertPairBySize_mem (p : Fn × Nat) :
    ∀ (ps : List (Fn × Nat)) {q : Fn × Nat}, q ∈ insertPairBySize p ps → q = p ∨ q ∈ ps
  | [], q, hq => by
      dsimp only [insertPairBySize] at hq
      exact Or.inl (List.mem_singleton.mp hq)
  | a :: ps, q, hq => by
      dsimp only [insertPairBySize] at hq
      split at hq
      · rcases List.mem_cons.1 hq with rfl | hq
        · exact Or.inl rfl
        · exact Or.inr hq
      · rcases List.mem_cons.1 hq with rfl | hq
        · exact Or.inr List.mem_cons_self
        · rcases insertPairBySize_mem p ps hq with rfl | hrest
          · exact Or.inl rfl
          · exact Or.inr (List.mem_cons_of_mem _ hrest)

private theorem sortPairsBySize_mem :
    ∀ {ps : List (Fn × Nat)} {q : Fn × Nat}, q ∈ sortPairsBySize ps → q ∈ ps
  | [], _, hq => by dsimp only [sortPairsBySize] at hq; cases hq
  | p :: ps, q, hq => by
      dsimp only [sortPairsBySize] at hq
      rcases insertPairBySize_mem p (sortPairsBySize ps) hq with rfl | hrest
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (sortPairsBySize_mem hrest)

private theorem selectCandsAux_mem (callerCalls : List (Sym × Nat)) (maxSz : Nat) :
    ∀ (curSz : Nat) (ps : List (Fn × Nat)) {g : Fn},
      g ∈ selectCandsAux callerCalls maxSz curSz ps → ∃ n, (g, n) ∈ ps
  | _, [], _, hg => by dsimp only [selectCandsAux] at hg; cases hg
  | curSz, (c, csz) :: ps, g, hg => by
      dsimp only [selectCandsAux] at hg
      split at hg
      · rcases List.mem_cons.1 hg with rfl | hrest
        · exact ⟨csz, List.mem_cons_self⟩
        · obtain ⟨n, hn⟩ := selectCandsAux_mem callerCalls maxSz _ ps hrest
          exact ⟨n, List.mem_cons_of_mem _ hn⟩
      · obtain ⟨n, hn⟩ := selectCandsAux_mem callerCalls maxSz curSz ps hg
        exact ⟨n, List.mem_cons_of_mem _ hn⟩

theorem selectCandsForCaller_mem (policy : InlinePolicy) (cands : List Fn) (fn : Fn) :
    ∀ g ∈ selectCandsForCaller policy cands fn, g ∈ cands := by
  intro g hg
  dsimp only [selectCandsForCaller] at hg
  split at hg
  · exact hg
  · split at hg
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hg
      exact filterRelevantCands_mem _ _ _ cands hp
    · split at hg
      · cases hg
      · obtain ⟨n, hn⟩ := selectCandsAux_mem _ _ _ _ hg
        exact filterRelevantCands_mem _ _ _ cands (sortPairsBySize_mem hn)

theorem inlineFnsPolicy_preserve (P : Fn → Prop) (policy : InlinePolicy)
    (siteCounts loopCounts : List (Sym × Nat)) (extSigs : List SigEntry) (exits : List Sym)
    (hInl : ∀ (cands : List Fn) (fn : Fn),
      (∀ c ∈ cands, P c) → P fn → P (fn.inline cands)) :
    ∀ (seenSigs : List SigEntry) (cands rest : List Fn),
      (∀ c ∈ cands, P c) → (∀ f ∈ rest, P f) →
      ∀ f ∈ inlineFnsPolicy policy siteCounts loopCounts extSigs exits seenSigs cands rest, P f
  | _, _, [], _, _, _, hf => by dsimp only [inlineFnsPolicy] at hf; cases hf
  | seenSigs, cands, fn :: rest, hcands, hrest, f, hf => by
      dsimp only [inlineFnsPolicy] at hf
      let candsFn := selectCandsForCaller policy cands fn
      have hfn' : P (fn.inline candsFn) :=
        hInl candsFn fn (fun c hc => hcands c (selectCandsForCaller_mem policy cands fn c hc))
          (hrest fn List.mem_cons_self)
      rcases List.mem_cons.1 hf with rfl | htl
      · exact hfn'
      · have hcands' : ∀ c ∈
            (if inlineCandidateOkPolicy policy (lookupCallSite siteCounts (fn.inline candsFn).name)
                (lookupCallSite loopCounts (fn.inline candsFn).name)
                (seenSigs ++ extSigs) exits (fn.inline candsFn)
             then fn.inline candsFn :: cands else cands), P c := by
          intro c hc
          split at hc
          · rcases List.mem_cons.1 hc with rfl | hc'
            · exact hfn'
            · exact hcands c hc'
          · exact hcands c hc
        exact inlineFnsPolicy_preserve P policy siteCounts loopCounts extSigs exits hInl
          (seenSigs ++ [fn.sig]) _ rest hcands'
          (fun g hg => hrest g (List.mem_cons_of_mem _ hg)) f htl

private theorem inlineFnsPolicy_ok {Γ : Env} (policy : InlinePolicy)
    (siteCounts loopCounts : List (Sym × Nat)) (extSigs : List SigEntry) (exits : List Sym) :
    ∀ (seenSigs : List SigEntry) (cands rest : List Fn),
    CandsWpOk Γ cands →
    CandsCallsOk (seenSigs ++ extSigs) exits cands →
    (∀ pre fn post, rest = pre ++ fn :: post →
      fn.Wf ∧ fn.callsOk ((seenSigs ++ pre.map Fn.sig) ++ extSigs) exits ∧
      ∀ xs m Q X, Γ fn.name fn.as fn.rs xs m Q X → Func.wp Γ fn.body xs m Q X) →
    ∀ pre' fn' post',
      inlineFnsPolicy policy siteCounts loopCounts extSigs exits seenSigs cands rest =
        pre' ++ fn' :: post' →
      fn'.Wf ∧ fn'.callsOk ((seenSigs ++ pre'.map Fn.sig) ++ extSigs) exits ∧
      ∀ xs m Q X, Γ fn'.name fn'.as fn'.rs xs m Q X → Func.wp Γ fn'.body xs m Q X
  | _, _, [], _, _, _, pre', _, _, hsplit => by
      cases pre' <;> (dsimp only [inlineFnsPolicy] at hsplit; simp at hsplit)
  | seenSigs, cands, fn :: rest, hwp, hcalls, hrest, pre', fn', post', hsplit => by
      have ⟨hfn_wf, hfn_calls, hfn_spec⟩ := hrest [] fn rest rfl
      simp only [List.map_nil, List.append_nil] at hfn_calls
      let candsFn := selectCandsForCaller policy cands fn
      have hsubFn : ∀ g ∈ candsFn, g ∈ cands := selectCandsForCaller_mem policy cands fn
      have hwpFn : CandsWpOk Γ candsFn := fun g hg => hwp g (hsubFn g hg)
      have hcallsFn : CandsCallsOk (seenSigs ++ extSigs) exits candsFn :=
        fun g hg => hcalls g (hsubFn g hg)
      let fn0 := fn.inline candsFn
      have hfn0_wf : fn0.Wf := Func.inline_wf hwpFn.wfOk hfn_wf
      have hfn0_calls : fn0.callsOk (seenSigs ++ extSigs) exits :=
        inline_callsOk hcallsFn _ hfn_calls
      have hfn0_spec : ∀ xs m Q X, Γ fn0.name fn0.as fn0.rs xs m Q X →
          Func.wp Γ fn0.body xs m Q X :=
        fun xs m Q X hg => Func.inline_spec hwpFn fn.body (hfn_spec xs m Q X hg)
      let allowed := seenSigs ++ extSigs
      let sites := lookupCallSite siteCounts fn0.name
      let loopSites := lookupCallSite loopCounts fn0.name
      let cands' :=
        if inlineCandidateOkPolicy policy sites loopSites allowed exits fn0 then
          fn0 :: cands
        else
          cands
      have hwp' : CandsWpOk Γ cands' := by
        dsimp only [cands']
        split
        · intro g hg
          rcases List.mem_cons.1 hg with rfl | hg
          · exact ⟨hfn0_wf, hfn0_spec⟩
          · exact hwp g hg
        · exact hwp
      have hsub : ∀ s ∈ seenSigs ++ extSigs, s ∈ (seenSigs ++ [fn.sig]) ++ extSigs := by
        intro s hs
        rcases List.mem_append.1 hs with hs | hs
        · exact List.mem_append_left _ (List.mem_append_left _ hs)
        · exact List.mem_append_right _ hs
      have hcalls' : CandsCallsOk ((seenSigs ++ [fn.sig]) ++ extSigs) exits cands' := by
        dsimp only [cands']
        split
        · intro g hg
          rcases List.mem_cons.1 hg with rfl | hg
          · exact ⟨hfn0_wf, Fn.callsOk_mono hsub hfn0_calls⟩
          · exact ⟨(hcalls g hg).1, Fn.callsOk_mono hsub (hcalls g hg).2⟩
        · intro g hg
          exact ⟨(hcalls g hg).1, Fn.callsOk_mono hsub (hcalls g hg).2⟩
      have hrest' : ∀ pre fn2 post, rest = pre ++ fn2 :: post →
          fn2.Wf ∧
          fn2.callsOk (((seenSigs ++ [fn.sig]) ++ pre.map Fn.sig) ++ extSigs) exits ∧
          ∀ xs m Q X, Γ fn2.name fn2.as fn2.rs xs m Q X → Func.wp Γ fn2.body xs m Q X := by
        intro pre fn2 post hsp
        have h := hrest (fn :: pre) fn2 post (by simp [hsp])
        simpa [List.append_assoc] using h
      cases pre' with
      | nil =>
          dsimp only [inlineFnsPolicy] at hsplit
          simp only [List.nil_append, List.cons.injEq] at hsplit
          rcases hsplit with ⟨rfl, _⟩
          simpa [List.append_nil] using And.intro hfn0_wf (And.intro hfn0_calls hfn0_spec)
      | cons hd tl =>
          dsimp only [inlineFnsPolicy] at hsplit
          simp only [List.cons_append, List.cons.injEq] at hsplit
          rcases hsplit with ⟨rfl, htl⟩
          have hsig : (fn.inline (selectCandsForCaller policy cands fn)).sig = fn.sig := rfl
          have ih := inlineFnsPolicy_ok policy siteCounts loopCounts extSigs exits
            (seenSigs ++ [fn.sig]) cands' rest hwp' hcalls' hrest' tl fn' post' htl
          simpa [hsig, List.append_assoc] using ih

/-- Flagship module correctness theorem for policy-driven acyclic inlining. -/
theorem Module.inlinePolicy_ok {Γ : Env} {M : Module} (policy : InlinePolicy := {}) :
    ModuleOk Γ M → ModuleOk Γ (M.inlinePolicy policy) := fun hM => by
  refine ⟨(Module.inlinePolicy_namesNodup M policy).symm ▸ hM.nodup, fun pre fn post hsplit => ?_⟩
  let needSites := policy.singleSiteMax > 0 || policy.maxTotalDup > 0
  let siteCounts := if needSites then fnsCallSites M.fns else []
  let loopCounts := if policy.requireLoopSite then fnsLoopCallSites M.fns else []
  exact inlineFnsPolicy_ok policy siteCounts loopCounts
    (M.externs.map Extern.sig) M.exits [] [] M.fns
    (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun pre0 fn0 post0 hsp0 => by simpa using hM.fnsOk pre0 fn0 post0 hsp0)
    pre fn post hsplit

/-- Flagship module correctness theorem: acyclic small-callee inlining preserves `ModuleOk Γ`. -/
theorem Module.inline_ok {Γ : Env} {M : Module} (maxSize : Nat := 40) :
    ModuleOk Γ M → ModuleOk Γ (M.inline maxSize) :=
  Module.inlinePolicy_ok (InlinePolicy.const maxSize)

/-- `Module.inlinePolicy` preserves `Fn.Wf` for every function in `M`. -/
theorem Module.inlinePolicy_wf {Γ : Env} {M : Module} (policy : InlinePolicy := {})
    (hM : ModuleOk Γ M) : ∀ fn ∈ (M.inlinePolicy policy).fns, fn.Wf := by
  intro fn hfn
  obtain ⟨pre, post, hsp⟩ := List.mem_iff_append.mp hfn
  exact ((Module.inlinePolicy_ok policy hM).fnsOk pre fn post hsp).1

/-- `Module.inlinePolicy` preserves `Fn.callsOk` along the module function list. -/
theorem Module.inlinePolicy_callsOk {Γ : Env} {M : Module} (policy : InlinePolicy := {})
    (hM : ModuleOk Γ M) :
    ∀ pre fn post, (M.inlinePolicy policy).fns = pre ++ fn :: post →
      fn.callsOk (pre.map Fn.sig ++ M.externs.map Extern.sig) M.exits := by
  intro pre fn post hsp
  exact ((Module.inlinePolicy_ok policy hM).fnsOk pre fn post hsp).2.1

/-- `Module.inlinePolicy` preserves `Func.wp` contracts for every function in `M`. -/
theorem Module.inlinePolicy_spec {Γ : Env} {M : Module} (policy : InlinePolicy := {})
    (hM : ModuleOk Γ M) :
    ∀ fn ∈ (M.inlinePolicy policy).fns, ∀ xs m Q X,
      Γ fn.name fn.as fn.rs xs m Q X → Func.wp Γ fn.body xs m Q X := by
  intro fn hfn
  obtain ⟨pre, post, hsp⟩ := List.mem_iff_append.mp hfn
  exact ((Module.inlinePolicy_ok policy hM).fnsOk pre fn post hsp).2.2

private theorem Blocks.checkCallsOk_of_get {allowed : List SigEntry} {exits : List Sym}
    {rs : List Ty} :
    {sig : List (List Ty)} → {bs : Blocks (fun _ => Unit) (fun _ => Unit) rs sig} →
    (∀ {ts} (i : Member ts sig), (bs.get i (Tup.units ts)).checkCallsOk allowed exits = true) →
    bs.checkCallsOk allowed exits = true
  | _, .nil, _ => rfl
  | _, .cons _ _, h => by
      simp only [Blocks.checkCallsOk, Bool.and_eq_true]
      exact ⟨h .here, Blocks.checkCallsOk_of_get fun i => h (.there i)⟩

theorem Expr.checkCallsOk_of_callsOk {allowed : List SigEntry} {exits : List Sym}
    {rs : List Ty} (e : Expr (fun _ => Unit) (fun _ => Unit) rs) :
    e.callsOk allowed exits → e.checkCallsOk allowed exits = true := by
  induction e using Expr.induct with
  | let_ _ _ ih => intro h; exact ih (Tup.units _) h
  | load _ _ _ ih => intro h; exact ih () h
  | store _ _ _ ih => intro h; exact ih h
  | call f args _ ih =>
      intro ⟨hmem, hk⟩
      simp only [Expr.checkCallsOk, Bool.and_eq_true, List.any_eq_true, SigEntry.beq_iff_eq]
      exact ⟨⟨(f, _, _), hmem, rfl⟩, ih (Tup.units _) hk⟩
  | jnz _ _ _ iht ihe =>
      intro ⟨ht, he⟩
      simp only [Expr.checkCallsOk, Bool.and_eq_true]
      exact ⟨iht ht, ihe he⟩
  | jump _ _ | ret _ | hlt => intro _; rfl
  | exit f _ =>
      intro h
      simp only [Expr.checkCallsOk, List.any_eq_true, beq_iff_eq]
      exact ⟨f, h, rfl⟩
  | group _ _ ihb ihk =>
      intro ⟨hb, hk⟩
      simp only [Expr.checkCallsOk, Bool.and_eq_true]
      exact
        ⟨Blocks.checkCallsOk_of_get fun i =>
            ihb (Tup.units _) i (Tup.units _) (Blocks.callsOk_get hb i),
         ihk (Tup.units _) hk⟩

theorem checkFnsCallsOk_of_forall (exits : List Sym) (extSigs : List SigEntry) :
    ∀ (seenSigs : List SigEntry) (rest : List Fn),
    (∀ pre fn post, rest = pre ++ fn :: post →
      fn.callsOk ((seenSigs ++ pre.map Fn.sig) ++ extSigs) exits) →
    Module.checkFnsCallsOk exits extSigs seenSigs rest = true
  | _, [], _ => rfl
  | seenSigs, fn :: rest, h => by
      have hhd := h [] fn rest rfl
      simp only [List.map_nil, List.append_nil] at hhd
      have htl := checkFnsCallsOk_of_forall exits extSigs (seenSigs ++ [fn.sig]) rest
        fun pre f post hsp => by
          simpa [List.append_assoc] using h (fn :: pre) f post (by simp [hsp])
      simp only [Module.checkFnsCallsOk, Bool.and_eq_true]
      exact ⟨Expr.checkCallsOk_of_callsOk _ hhd, htl⟩

/-- `Module.inlinePolicy` preserves the decidable `Module.checkAcyclic` certificate when all
functions are well-formed. -/
theorem Module.inlinePolicy_checkAcyclic {M : Module} (policy : InlinePolicy := {})
    (hchk : M.checkAcyclic = true) (hwf : ∀ fn ∈ M.fns, fn.Wf) :
    (M.inlinePolicy policy).checkAcyclic = true := by
  have hm : ModuleOk (fun _ _ _ _ _ _ _ => False) (M.inlinePolicy policy) :=
    Module.inlinePolicy_ok policy
      (Module.moduleOk_of_checkAcyclic hchk hwf (fun _ _ _ _ _ _ h => h.elim))
  simp only [Module.checkAcyclic, Bool.and_eq_true]
  refine ⟨listNodup_iff.mpr hm.nodup, checkFnsCallsOk_of_forall _ _ [] _ fun pre fn post hsp => ?_⟩
  simpa using (hm.fnsOk pre fn post hsp).2.1

/-- `Module.inlinePolicy` preserves acyclicity (`checkAcyclic = true`). -/
theorem Module.inlinePolicy_acyclic {M : Module} (policy : InlinePolicy := {})
    (hchk : M.checkAcyclic = true) (hwf : ∀ fn ∈ M.fns, fn.Wf) :
    (M.inlinePolicy policy).checkAcyclic = true :=
  Module.inlinePolicy_checkAcyclic policy hchk hwf

/-- `Module.inline` preserves the decidable `Module.checkAcyclic` certificate when all functions
are well-formed. -/
theorem Module.inline_checkAcyclic {M : Module} (maxSize : Nat := 40)
    (hchk : M.checkAcyclic = true) (hwf : ∀ fn ∈ M.fns, fn.Wf) :
    (M.inline maxSize).checkAcyclic = true :=
  Module.inlinePolicy_checkAcyclic (InlinePolicy.const maxSize) hchk hwf

end LeanQbe.T
