module

public import LeanQbe.T.LegalMemLemmas1

/-!
# Legalization `legalExpr_wp`, `Func.legal_wp`, and `Func.legal_spec` (Part 4b)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T

section LegalWp

/-! ### Source support reification, `legalExpr_wp`, `Func.legal_wp`, `Func.legal_spec` -/

private inductive ExprSupports (target : LegalTarget) : {rs : List Ty} → Expr Val Cont rs → Prop
  | let_ {rs ts : List Ty} (op : Op Val ts) (k : Tup Val ts → Expr Val Cont rs) :
    target.supportsOpCode op.code = true →
    (∀ xs, ExprSupports target (k xs)) →
    ExprSupports target (.let_ op k)
  | load {rs : List Ty} (t : Ty) (a : Arg Val i64) (k : Val t → Expr Val Cont rs) :
    target.supportsTy t = true → t.bytes ≤ 2 ^ 64 →
    (∀ v, ExprSupports target (k v)) →
    ExprSupports target (.load t a k)
  | store {rs : List Ty} {t : Ty} (v : Arg Val t) (a : Arg Val i64) (k : Expr Val Cont rs) :
    target.supportsTy t = true → t.bytes ≤ 2 ^ 64 →
    ExprSupports target k →
    ExprSupports target (.store v a k)
  | call {rs as bs : List Ty} (f : Sym) (args : Tup (Arg Val) as)
      (k : Tup Val bs → Expr Val Cont rs) :
    as.all target.supportsTy = true → bs.all target.supportsTy = true →
    (∀ xs, ExprSupports target (k xs)) →
    ExprSupports target (.call f args k)
  | jnz {rs : List Ty} (c : Arg Val .bool) (t e : Expr Val Cont rs) :
    ExprSupports target t → ExprSupports target e →
    ExprSupports target (.jnz c t e)
  | jump {rs ts : List Ty} (j : Cont ts) (args : Tup (Arg Val) ts) :
    ts.all target.supportsTy = true →
    ExprSupports target (.jump j args)
  | ret {rs : List Ty} (vs : Tup (Arg Val) rs) :
    rs.all target.supportsTy = true →
    ExprSupports target (.ret vs)
  | exit {rs as : List Ty} (f : Sym) (args : Tup (Arg Val) as) :
    as.all target.supportsTy = true →
    ExprSupports target (.exit f args)
  | hlt {rs : List Ty} :
    ExprSupports target (.hlt (rs := rs))
  | group {rs : List Ty} {sig : List (List Ty)}
      (bodies : Tup Cont sig → Blocks Val Cont rs sig)
      (k : Tup Cont sig → Expr Val Cont rs) :
    (sig.all (·.all target.supportsTy)) = true →
    (∀ Js {ts} (i : Member ts sig) xs, ExprSupports target ((bodies Js).get i xs)) →
    (∀ Js, ExprSupports target (k Js)) →
    ExprSupports target (.group bodies k)

private theorem exprSupports_of_wf_toTFlat (target : LegalTarget) :
    {rs : List Ty} → {G : Ctx K Val} → {D : Ctx KL Cont} →
    {eK : Expr K KL rs} → {eV : Expr Val Cont rs} →
    Wf G D eK eV →
    ∀ nv nl, (toTFlat eK nv nl).supportsSource target = true → ExprSupports target eV := by
  intro rs G D eK eV hwf
  induction hwf using Wf.induct with
  | @let_ G D ts op₁ op₂ k₁ k₂ hop hk ih =>
    intro nv nl hs
    dsimp only [toTFlat, TFlat.supportsSource] at hs
    simp only [Bool.and_eq_true] at hs
    rcases hop with ⟨code, _⟩
    exact ExprSupports.let_ _ k₂ hs.1 fun xs =>
      ih (Tup.levels ts nv) xs (nv + ts.length) nl hs.2
  | @load G D t a₁ a₂ k₁ k₂ ha hk ih =>
    intro nv nl hs
    dsimp only [toTFlat, TFlat.supportsSource] at hs
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hs
    exact ExprSupports.load t a₂ k₂ hs.1.1 hs.1.2 fun v => ih nv v (nv + 1) nl hs.2
  | @store G D t v₁ v₂ a₁ a₂ k₁ k₂ hv ha hk ih =>
    intro nv nl hs
    dsimp only [toTFlat, TFlat.supportsSource] at hs
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hs
    exact ExprSupports.store v₂ a₂ k₂ hs.1.1 hs.1.2 (ih nv nl hs.2)
  | @call G D f as bs args₁ args₂ k₁ k₂ hargs hk ih =>
    intro nv nl hs
    dsimp only [toTFlat, TFlat.supportsSource] at hs
    simp only [Bool.and_eq_true] at hs
    exact ExprSupports.call f args₂ k₂ hs.1.1 hs.1.2 fun xs =>
      ih (Tup.levels bs nv) xs (nv + bs.length) nl hs.2
  | @jnz G D c₁ c₂ t₁ t₂ e₁ e₂ hc ht he iht ihe =>
    intro nv nl hs
    dsimp only [toTFlat, TFlat.supportsSource] at hs
    simp only [Bool.and_eq_true] at hs
    exact ExprSupports.jnz c₂ t₂ e₂ (iht nv nl hs.1) (ihe nv nl hs.2)
  | @jump G D ts j₁ j₂ args₁ args₂ hj hargs =>
    intro nv nl hs
    dsimp only [toTFlat, TFlat.supportsSource] at hs
    exact ExprSupports.jump (rs := rs) j₂ args₂ hs
  | @ret G D vs₁ vs₂ hvs =>
    intro nv nl hs
    dsimp only [toTFlat, TFlat.supportsSource] at hs
    exact ExprSupports.ret vs₂ hs
  | @exit G D f as args₁ args₂ hargs =>
    intro nv nl hs
    dsimp only [toTFlat, TFlat.supportsSource] at hs
    exact ExprSupports.exit (rs := rs) f args₂ hs
  | @hlt G D =>
    intro _ _ _
    exact ExprSupports.hlt
  | @group G D sig b₁ b₂ k₁ k₂ hb hk ihb ihk =>
    intro nv nl hs
    dsimp only [toTFlat, TFlat.supportsSource] at hs
    simp only [Bool.and_eq_true] at hs
    refine ExprSupports.group b₂ k₂ hs.1.1 (fun Js ts i xs => ?_) (fun Js => ?_)
    · have hget := toTBlocks_get target (b₁ (Tup.levels sig nl)) i nv (nl + sig.length) hs.1.2
      exact ihb (Tup.levels sig nl) Js i (Tup.levels ts nv) xs (nv + ts.length) (nl + sig.length)
        hget.2
    · exact ihk (Tup.levels sig nl) Js nv (nl + sig.length) hs.2

private theorem exprSupports_of_reify (target : LegalTarget) {as rs : List Ty} (f : Func as rs)
    (hf : f.Wf) (hsupp : f.supportsSource target = true) (xs : Tup Val as) :
    ExprSupports target (f Val Cont xs) := by
  simp only [Func.supportsSource, Bool.and_eq_true] at hsupp
  exact exprSupports_of_wf_toTFlat target (hf K Val KL Cont (Tup.levels as 0) xs) as.length 0
    hsupp.2

private theorem cast_legalArg_i64_val (target : LegalTarget) (_hv : target.valid = true)
    {G : Ctx Val (LVar target Val)} (hG : CGoodWp target G)
    {a₁ : Arg Val i64} {a₂ : Arg (LVar target Val) i64} (ha : ArgRel G i64 a₁ a₂)
    (h64 : target.widenWidth 64 = 64) :
    (castArgBits h64 (legalArg target a₂).fst).val = a₁.val := by
  have hval := valsTup_legalArg target hG ha
  dsimp only [encodeVal, LegalTarget.legalTys, valsTup, Tup.map] at hval
  have hfst : (legalArg target a₂).fst.val = a₁.val.setWidth (target.widenWidth 64) :=
    congrArg Prod.fst hval
  rw [val_castArgBits, cast_eq_setWidth h64, hfst, BitVec.setWidth_setWidth_of_le _ (by omega),
    BitVec.setWidth_eq]

private theorem legalExpr_wp (target : LegalTarget) (hv : target.valid = true)
    {Γsrc Γtgt : Env} (hEnv : EnvRefines target Γsrc Γtgt)
    {rs : List Ty} :
    ∀ {G : Ctx Val (LVar target Val)} {D : Ctx Cont (LLab target Cont)}
      {e₁ : Expr Val Cont rs} {e₂ : Expr (LVar target Val) (LLab target Cont) rs},
      Wf G D e₁ e₂ →
      CGoodWp target G → DGoodWp target D →
      ExprSupports target e₁ →
      ∀ {Q : Post rs} {X : XPost} {m : Mem 64},
        wp Γsrc Q X e₁ m →
        wp Γtgt (legalPost target Q) (legalXPost target X) (legalExpr target e₂) m := by
  intro G D e₁ e₂ hwf
  induction hwf using Wf.induct with
  | @let_ G D ts op₁ op₂ k₁ k₂ hop hk ih =>
    intro hG hD hSupp Q X m hwp
    rw [wp_let] at hwp
    dsimp only [legalExpr]
    cases hSupp with | let_ _ _ hs_op hs_k =>
    refine legalOp_wp target hv hG hop hs_op hwp fun r lr hrel hr => ?_
    exact ih r lr (CGoodWp.pushTRel target hG hrel) hD (hs_k r) hr
  | @load G D t a₁ a₂ k₁ k₂ ha hk ih =>
    intro hG hD hSupp Q X m hwp
    rw [wp_load] at hwp
    rcases hwp with ⟨v, hLoad, hwpk⟩
    cases hSupp with | load _ _ _ hst hble hs_k =>
    have h64mem : 64 ∈ target.bitWidths := by
      simp only [LegalTarget.valid, Bool.and_eq_true, decide_eq_true_eq] at hv
      exact hv.1.1.2
    have h64 : target.widenWidth 64 = 64 := widenWidth_eq_self_of_mem target h64mem
    dsimp only [legalExpr]
    rw [dite_eq_left h64]
    have hap : (castArgBits h64 (legalArg target a₂).fst).val = a₁.val :=
      cast_legalArg_i64_val target hv hG ha h64
    refine legalLoad_wp target hv t hst hble (ptr := castArgBits h64 (legalArg target a₂).fst)
      (by rwa [hap]) fun lr hlr => ?_
    refine ih v lr ?_ hD (hs_k v) hwpk
    intro t' x' lv' hm
    rcases List.mem_cons.1 hm with hhead | htail
    · cases hhead; exact hlr
    · exact hG _ _ _ htail
  | @store G D t v₁ v₂ a₁ a₂ k₁ k₂ hv_rel ha hk ih =>
    intro hG hD hSupp Q X m hwp
    rw [wp_store] at hwp
    rcases hwp with ⟨hOk, hwpk⟩
    cases hSupp with | store _ _ _ hst hble hs_k =>
    have h64mem : 64 ∈ target.bitWidths := by
      simp only [LegalTarget.valid, Bool.and_eq_true, decide_eq_true_eq] at hv
      exact hv.1.1.2
    have h64 : target.widenWidth 64 = 64 := widenWidth_eq_self_of_mem target h64mem
    dsimp only [legalExpr]
    rw [dite_eq_left h64]
    have hap : (castArgBits h64 (legalArg target a₂).fst).val = a₁.val :=
      cast_legalArg_i64_val target hv hG ha h64
    refine legalStore_wp target hv t hst hble (xs := legalArg target v₂)
      (ptr := castArgBits h64 (legalArg target a₂).fst) (v := v₁.val)
      (valsTup_legalArg target hG hv_rel) (by rwa [hap]) ?_
    rw [hap]
    exact ih hG hD hs_k hwpk
  | @call G D f as bs args₁ args₂ k₁ k₂ hargs hk ih =>
    intro hG hD hSupp Q X m hwp
    cases hSupp with | call _ _ _ _ _ hs_k =>
    dsimp only [legalExpr]
    dsimp only [wp, wp._f] at hwp ⊢
    rcases hwp with ⟨P, E, hCall, hPost, hExit⟩
    refine ⟨legalPost target P, legalXPost target E, ?_, ?_, ?_⟩
    · have hJoin := valsTup_joinArgs target hG hargs
      rw [valsTup_eq_vals] at hJoin
      rw [valsTup_eq_vals] at hJoin
      rw [hJoin]
      exact hEnv f as bs (vals args₁) m P E hCall
    · rintro ys m' ⟨xs, rfl, hP⟩
      exact ih xs (splitParams target bs (encodeTup target bs xs))
        (CGoodWp.pushSplit target hG bs xs) hD (hs_k xs) (hPost xs m' hP)
    · rintro g cs' ys m' ⟨cs, hcs, xs, rfl, hE⟩
      exact ⟨cs, hcs, xs, rfl, hExit g cs xs m' hE⟩
  | @jnz G D c₁ c₂ t₁ t₂ e₁ e₂ hc ht he iht ihe =>
    intro hG hD hSupp Q X m hwp
    cases hSupp with | jnz _ _ _ hst hse =>
    rw [wp_jnz] at hwp
    dsimp only [legalExpr]
    rw [wp_jnz]
    have hcv := valsTup_legalArg target hG hc
    dsimp only [encodeVal, LegalTarget.legalTys, valsTup, Tup.map] at hcv
    have hceq : (legalArg target c₂).fst.val = c₁.val := congrArg Prod.fst hcv
    rw [hceq]
    exact ⟨fun h => iht hG hD hst (hwp.1 h), fun h => ihe hG hD hse (hwp.2 h)⟩
  | @jump G D ts j₁ j₂ args₁ args₂ hj hargs =>
    intro hG hD _ Q X m hwp
    rw [wp_jump] at hwp
    dsimp only [legalExpr]
    rw [wp_jump]
    have hJoin := valsTup_joinArgs target hG hargs
    rw [valsTup_eq_vals, valsTup_eq_vals] at hJoin
    rw [hJoin]
    exact hD ts j₁ j₂ hj (vals args₁) m hwp
  | @ret G D vs₁ vs₂ hvs =>
    intro hG _ _ Q X m hwp
    rw [wp_ret] at hwp
    dsimp only [legalExpr]
    rw [wp_ret]
    have hJoin := valsTup_joinArgs target hG hvs
    rw [valsTup_eq_vals, valsTup_eq_vals] at hJoin
    exact ⟨vals vs₁, hJoin.symm, hwp⟩
  | @exit G D f as args₁ args₂ hargs =>
    intro hG _ _ Q X m hwp
    rw [wp_exit] at hwp
    dsimp only [legalExpr]
    rw [wp_exit]
    have hJoin := valsTup_joinArgs target hG hargs
    rw [valsTup_eq_vals, valsTup_eq_vals] at hJoin
    exact ⟨as, rfl, vals args₁, hJoin.symm, hwp⟩
  | @hlt G D =>
    intro _ _ _ _ _ _ hwp
    cases hwp
  | @group G D sig b₁ b₂ k₁ k₂ hb hk ihb ihk =>
    intro hG hD hSupp Q X m hwp
    cases hSupp with | group _ _ _ hs_b hs_k =>
    dsimp only [legalExpr]
    dsimp only [wp, wp._f] at hwp ⊢
    intro Js2 hClosed2
    have hD' :
      DGoodWp target
      (Tup.zip (unlegalTupCont target Js2) (tupLiftMap target.legalSig Cont Js2) ++ D) :=
      DGoodWp.pushUnlegal target hD Js2
    have hClosed1 : Closed Γsrc Q X (b₁ (unlegalTupCont target Js2)) (unlegalTupCont target Js2) :=
      by
      rw [closed_iff]
      intro ts i xs m' hbody1
      rw [unlegalTupCont_get]
      rw [closed_iff] at hClosed2
      apply hClosed2 (Member.map target.legalSig i) (encodeTup target ts xs) m'
      rw [legalBlocks_get]
      exact ihb (unlegalTupCont target Js2) (tupLiftMap target.legalSig Cont Js2) i xs
        (splitParams target ts (encodeTup target ts xs))
        (CGoodWp.pushSplit target hG ts xs) hD' (hs_b (unlegalTupCont target Js2) i xs) hbody1
    exact ihk (unlegalTupCont target Js2) (tupLiftMap target.legalSig Cont Js2)
      hG hD' (hs_k (unlegalTupCont target Js2)) (hwp (unlegalTupCont target Js2) hClosed1)

/-- `Func.legal` semantic preservation under any target environment refining `Γsrc`. -/
theorem Func.legal_wp_of_refines (target : LegalTarget) {as rs : List Ty} (f : Func as rs)
    (hf : f.Wf) (hsupp : f.supportsSource target = true)
    {Γsrc Γtgt : Env} (hEnv : EnvRefines target Γsrc Γtgt)
    (xs : Tup Val as) (m : Mem 64) (Q : Post rs) (X : XPost) :
    Func.wp Γsrc f xs m Q X →
    Func.wp Γtgt (f.legal target) (encodeTup target as xs) m (legalPost target Q)
      (legalXPost target X) := by
  intro hwp
  have hv : target.valid = true := by
    simp only [Func.supportsSource, Bool.and_eq_true] at hsupp
    exact hsupp.1.1.1
  dsimp only [Func.wp, Func.legal]
  exact legalExpr_wp target hv hEnv
    (hf Val (LVar target Val) Cont (LLab target Cont) xs
      (splitParams target as (encodeTup target as xs)))
    (by
      simpa using CGoodWp.pushSplit target
        (fun _ _ _ hm => False.elim (List.not_mem_nil hm)) as xs)
    (fun _ _ _ hm => False.elim (List.not_mem_nil hm))
    (exprSupports_of_reify target f hf hsupp xs)
    hwp

/-- Main legalization semantic preservation theorem for `Func.legal` with canonical `legalEnv`. -/
theorem Func.legal_wp (target : LegalTarget) {as rs : List Ty} (f : Func as rs)
    (hf : f.Wf) (hsupp : f.supportsSource target = true)
    (Γ : Env) (xs : Tup Val as) (m : Mem 64) (Q : Post rs) (X : XPost) :
    Func.wp Γ f xs m Q X →
    Func.wp (legalEnv target Γ) (f.legal target) (encodeTup target as xs) m
      (legalPost target Q) (legalXPost target X) :=
  Func.legal_wp_of_refines target f hf hsupp (envRefines_legalEnv target Γ) xs m Q X

/-- Specification-style consequence of `Func.legal_wp` in `Func.spec` form. -/
theorem Func.legal_spec (target : LegalTarget) {as rs : List Ty} (f : Func as rs)
    (hf : f.Wf) (hsupp : f.supportsSource target = true)
    (Γ : Env) (xs : Tup Val as) (m : Mem 64) (Q : Post rs) (X : XPost) :
    Func.spec Γ f xs m Q X →
    Func.spec (legalEnv target Γ) (f.legal target) (encodeTup target as xs) m
      (legalPost target Q) (legalXPost target X) :=
  Func.legal_wp target f hf hsupp Γ xs m Q X

/-- Specification preservation for closed `Fn` units via `Fn.legal`. -/
theorem Fn.legal_spec (target : LegalTarget) (fn : Fn)
    (hf : fn.body.Wf) (hsupp : fn.body.supportsSource target = true)
    (Γ : Env) (xs : Tup Val fn.as) (m : Mem 64) (Q : Post fn.rs) (X : XPost) :
    Func.spec Γ fn.body xs m Q X →
    Func.spec (legalEnv target Γ) (fn.legal target).body (encodeTup target fn.as xs) m
      (legalPost target Q) (legalXPost target X) :=
  Func.legal_wp target fn.body hf hsupp Γ xs m Q X

end LegalWp

end LeanQbe.T
