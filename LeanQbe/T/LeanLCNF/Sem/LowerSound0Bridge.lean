module

public import LeanQbe.T.LeanLCNF.Sem.LowerSound0

/-!
# Compositional Declaration Bridge & `lowerModule` Structure (`LowerSound0Bridge`)

Companion to `LowerSound0.lean` keeping both files cleanly `< 1,200` LOC:
1. **Fragment & `lowerModule` Structural Lemmas**:
   `isPrimName_of_isPhase1Prim`, `nodup_of_symsNodup`, `inFirstOrderFragment_no_closures`,
   `firstOrderLEnv`, `firstOrderLEnv_ok`, `lowerModule_firstOrder_decls`, `mapM_ok_mem`,
   `mapM_ok_mem_inv`.
2. **Compositional Bridge (`LExprSem.TFlatFn.wp_of_lExpr` ↔ `Sem.H.liftDeclSpec`/`liftSpec`)**:
   `finishFn_wp_of_lExpr`, `loadAt_wp`, `loadExtras_wp`, `lowerDecl_sig`, `HCodeSim`,
   `lowerDecl_of_body_sim` (acyclic & general recursive decls), `lowerDecl_loop_of_body_sim`
   (self-tail loop lfp induction), and their `liftSpec` specializations for `params.length ≤ 5`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.LeanLCNF.Sem

open LeanQbe.T
open LeanQbe.T.LeanLCNF
open LeanQbe.T.Frontend.C0
open Std.ExtHashMap

/-! ## 1. Fragment & `lowerModule` Structural Lemmas -/

theorem isPrimName_of_isPhase1Prim {name : String} {arity : Nat} {retTy : LcTy}
    (h : isPhase1Prim name arity retTy = true) : isPrimName name = true := by
  unfold isPhase1Prim at h
  unfold isPrimName
  generalize splitDot name = parts at h ⊢
  rcases parts with _ | ⟨p0, rest⟩
  · cases h
  · by_cases hstr : p0 = "String"
    · subst hstr; rfl
    · rcases rest with _ | ⟨p1, rest2⟩
      · by_cases hg : p0 = "getObjTagNat"
        · subst hg; rfl
        · simp [hstr, hg] at h
      · rcases rest2 with _ | ⟨p2, rest3⟩
        · by_cases hnat : p0 = "Nat"
          · subst hnat; rfl
          · by_cases harr : p0 = "Array"
            · subst harr; rfl
            · by_cases hba : p0 = "ByteArray"
              · subst hba; rfl
              · have hu' : (uintWidth? p0).isSome = true := by
                  cases hu : uintWidth? p0 with
                  | some _ => rfl
                  | none => simp [hu] at h
                by_cases hfl : p0 = "Float"
                · subst hfl; rfl
                · by_cases hch : p0 = "Char"
                  · subst hch; rfl
                  · by_cases hi : p0 = "Int"
                    · subst hi; rfl
                    · by_cases hi64 : p0 = "Int64"
                      · subst hi64; rfl
                      · have ho1 : p0 ≠ "outOfBounds" := fun e => by
                          subst e; simp [uintWidth?] at hu'
                        simp [ho1, hu']
        · rcases rest3 with _ | ⟨_, _⟩
          · by_cases hsys : p0 = "System" ∧ p1 = "Platform" ∧ p2 = "getNumBits"
            · rcases hsys with ⟨rfl, rfl, rfl⟩; rfl
            · by_cases h1 : p0 = "System"
              · subst h1
                by_cases h2 : p1 = "Platform"
                · subst h2
                  have h3 : p2 ≠ "getNumBits" := fun he => hsys ⟨rfl, rfl, he⟩
                  simp [h3] at h
                · simp [h2] at h
              · simp [hstr, h1] at h
          · simp [hstr] at h

theorem nodup_of_symsNodup : ∀ {xs : List String}, symsNodup xs = true → xs.Nodup
  | [], _ => List.nodup_nil
  | x :: xs, h => by
    simp only [symsNodup, Bool.and_eq_true, Bool.not_eq_true'] at h
    have hnot : x ∉ xs := by
      intro hmem
      have hc : xs.contains x = true := List.contains_iff_mem.mpr hmem
      rw [hc] at h
      cases h.1
    exact List.nodup_cons.mpr ⟨hnot, nodup_of_symsNodup h.2⟩

private theorem lookup_foldl_cons_of_nodup :
    ∀ (decls : List LcDecl) (acc : List (String × LcDecl)),
      (decls.map (·.name)).Nodup →
      (∀ d ∈ decls, ∀ p ∈ acc, d.name ≠ p.1) →
      (∀ f d, acc.lookup f = some d ↔ (f, d) ∈ acc) →
      ∀ f d, (decls.foldl (fun s x => (x.name, x) :: s) acc).lookup f = some d ↔
        (d ∈ decls ∧ d.name = f) ∨ (f, d) ∈ acc
  | [], acc, _, _, hacc, f, d => by
    simp [hacc]
  | x :: xs, acc, hnd, hdisj, hacc, f, d => by
    rcases List.nodup_cons.mp hnd with ⟨hxnot, hxsnd⟩
    have hdisj' : ∀ d' ∈ xs, ∀ p ∈ (x.name, x) :: acc, d'.name ≠ p.1 := by
      intro d' hd' p hp
      rcases List.mem_cons.mp hp with rfl | hp'
      · intro heq; exact hxnot (List.mem_map.mpr ⟨d', hd', heq⟩)
      · exact hdisj d' (List.mem_cons_of_mem _ hd') p hp'
    have hacc' : ∀ g d',
        ((x.name, x) :: acc).lookup g = some d' ↔ (g, d') ∈ (x.name, x) :: acc := by
      intro g d'
      dsimp only [List.lookup]
      cases hg : (g == x.name) with
      | true =>
        have heq : g = x.name := eq_of_beq hg
        subst heq
        simp only [Option.some.injEq, List.mem_cons, Prod.mk.injEq, true_and]
        constructor
        · intro h; exact Or.inl h.symm
        · rintro (rfl | hmem)
          · rfl
          · exact absurd rfl (hdisj x (List.mem_cons_self ..) (x.name, d') hmem)
      | false =>
        have hne : g ≠ x.name := by intro he; subst he; simp at hg
        simp only [hacc g d', List.mem_cons, Prod.mk.injEq, hne, false_and, false_or]
    have ih := lookup_foldl_cons_of_nodup xs ((x.name, x) :: acc) hxsnd hdisj' hacc' f d
    simp only [List.foldl_cons, ih, List.mem_cons, Prod.mk.injEq]
    constructor
    · rintro (⟨hmem, rfl⟩ | ⟨rfl, rfl⟩ | hmem)
      · exact Or.inl ⟨Or.inr hmem, rfl⟩
      · exact Or.inl ⟨Or.inl rfl, rfl⟩
      · exact Or.inr hmem
    · rintro (⟨rfl | hmem, rfl⟩ | hmem)
      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      · exact Or.inl ⟨hmem, rfl⟩
      · exact Or.inr (Or.inr hmem)

mutual
private theorem code_refs_no_clo {decls : List LcDecl} :
    ∀ {jps : List (Nat × List LcTy)} (c : LcCode),
      c.inFirstOrder decls jps = true → c.refs.2.1 = [] ∧ c.refs.2.2 = 0
  | jps, .let_ _ ty v k, h => by
    simp only [LcCode.inFirstOrder, Bool.and_eq_true] at h
    have ih := code_refs_no_clo k h.2
    cases v with
    | ap _ _ => simp [LcVal.inFirstOrder] at h
    | pap _ _ => simp [LcVal.inFirstOrder] at h
    | _ => simp [LcCode.refs, ih.1, ih.2]
  | jps, .jp j ps body k, h => by
    simp only [LcCode.inFirstOrder, Bool.and_eq_true] at h
    have ih1 := code_refs_no_clo body h.1
    have ih2 := code_refs_no_clo k h.2
    simp [LcCode.refs, ih1.1, ih1.2, ih2.1, ih2.2]
  | jps, .cases _ alts, h => alts_refs_no_clo alts h
  | _, .jmp _ _, _ => ⟨rfl, rfl⟩
  | _, .ret _, _ => ⟨rfl, rfl⟩
  | _, .unreach, _ => ⟨rfl, rfl⟩
  | jps, .inc _ _ _ k, h => by simpa [LcCode.refs] using code_refs_no_clo k h
  | jps, .dec _ _ _ k, h => by simpa [LcCode.refs] using code_refs_no_clo k h
  | _, .oset _ _ _ _, h => by simp [LcCode.inFirstOrder] at h
  | _, .uset _ _ _ _, h => by simp [LcCode.inFirstOrder] at h
  | _, .sset _ _ _ _ _ _, h => by simp [LcCode.inFirstOrder] at h
  | _, .setTag _ _ _, h => by simp [LcCode.inFirstOrder] at h
  | _, .del _ _, h => by simp [LcCode.inFirstOrder] at h

private theorem alts_refs_no_clo {decls : List LcDecl} :
    ∀ {jps : List (Nat × List LcTy)} (alts : List (LcPat × LcCode)),
      LcAlts.inFirstOrder decls jps alts = true →
      (LcCode.altsRefs alts).2.1 = [] ∧ (LcCode.altsRefs alts).2.2 = 0
  | _, [], _ => ⟨rfl, rfl⟩
  | jps, (_, b) :: rest, h => by
    simp only [LcAlts.inFirstOrder, Bool.and_eq_true] at h
    have ih1 := code_refs_no_clo b h.1.2
    have ih2 := alts_refs_no_clo rest h.2
    simp [LcCode.altsRefs, ih1.1, ih1.2, ih2.1, ih2.2]
end

theorem inFirstOrderFragment_no_closures {m : LcModule}
    (hfrag : m.inFirstOrderFragment = true) :
    m.papTargets = [] ∧ m.maxAp = 0 := by
  simp only [LcModule.inFirstOrderFragment, Bool.and_eq_true, List.all_eq_true] at hfrag
  have hall : ∀ d ∈ m.decls, d.body.refs.2.1 = [] ∧ d.body.refs.2.2 = 0 := by
    intro d hd
    have hdi := hfrag.2 d hd
    simp only [LcDecl.inFirstOrder, Bool.and_eq_true] at hdi
    exact code_refs_no_clo d.body hdi.2
  have hpap : m.decls.flatMap (fun d => d.body.refs.2.1) = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro s hs
    obtain ⟨d, hd, hmem⟩ := List.mem_flatMap.mp hs
    rw [(hall d hd).1] at hmem
    cases hmem
  have hmax : ∀ (ds : List LcDecl), (∀ d ∈ ds, d.body.refs.2.2 = 0) →
      ds.foldl (fun a d => Nat.max a d.body.refs.2.2) 0 = 0 := by
    intro ds hds
    induction ds with
    | nil => rfl
    | cons d ds ih =>
      simp only [List.foldl_cons, hds d (List.mem_cons_self ..), Nat.max_self]
      exact ih (fun d' hd' => hds d' (List.mem_cons_of_mem _ hd'))
  exact ⟨by simp [LcModule.papTargets, hpap, dedupStr], hmax m.decls (fun d hd => (hall d hd).2)⟩

/-- Canonical `LEnv` built by `lowerModule` for a Phase-1 first-order module (empty closure,
global, string-literal, and big-nat tables). -/
@[expose] def firstOrderLEnv (m : LcModule) : LEnv :=
  { decls := m.decls.foldl (fun s d => (d.name, d) :: s) []
    funIds := []
    globals := []
    strLits := []
    bigNatLits := [] }

theorem firstOrderLEnv_ok {m : LcModule} (hfrag : m.inFirstOrderFragment = true) :
    LEnvOk m (firstOrderLEnv m) := by
  simp only [LcModule.inFirstOrderFragment, Bool.and_eq_true] at hfrag
  have hnd := nodup_of_symsNodup hfrag.1.1
  intro f d
  have h := lookup_foldl_cons_of_nodup m.decls [] hnd (fun _ _ _ hp => by cases hp)
    (fun _ _ => by simp [List.lookup]) f d
  simpa [firstOrderLEnv] using h

mutual
private theorem code_lits_empty {decls : List LcDecl} :
    ∀ {jps : List (Nat × List LcTy)} (c : LcCode),
      c.inFirstOrder decls jps = true → c.lits = ([], [])
  | jps, .let_ _ ty v k, h => by
    simp only [LcCode.inFirstOrder, Bool.and_eq_true] at h
    have ih := code_lits_empty k h.2
    cases v with
    | lit l =>
      cases l with
      | nat n =>
        simp only [LcVal.inFirstOrder, Bool.and_eq_true, decide_eq_true_eq] at h
        simp [LcCode.lits, ih, h.1.1]
      | scalar _ => simp [LcCode.lits, ih]
      | str _ => simp [LcVal.inFirstOrder] at h
    | _ => simp [LcCode.lits, ih]
  | jps, .jp _ _ body k, h => by
    simp only [LcCode.inFirstOrder, Bool.and_eq_true] at h
    simp [LcCode.lits, code_lits_empty body h.1, code_lits_empty k h.2]
  | jps, .cases _ alts, h => alts_lits_empty alts h
  | _, .jmp _ _, _ => rfl
  | _, .ret _, _ => rfl
  | _, .unreach, _ => rfl
  | jps, .inc _ _ _ k, h => by simpa [LcCode.lits] using code_lits_empty k h
  | jps, .dec _ _ _ k, h => by simpa [LcCode.lits] using code_lits_empty k h
  | _, .oset _ _ _ _, h => by simp [LcCode.inFirstOrder] at h
  | _, .uset _ _ _ _, h => by simp [LcCode.inFirstOrder] at h
  | _, .sset _ _ _ _ _ _, h => by simp [LcCode.inFirstOrder] at h
  | _, .setTag _ _ _, h => by simp [LcCode.inFirstOrder] at h
  | _, .del _ _, h => by simp [LcCode.inFirstOrder] at h

private theorem alts_lits_empty {decls : List LcDecl} :
    ∀ {jps : List (Nat × List LcTy)} (alts : List (LcPat × LcCode)),
      LcAlts.inFirstOrder decls jps alts = true → LcCode.altsLits alts = ([], [])
  | _, [], _ => rfl
  | jps, (_, b) :: rest, h => by
    simp only [LcAlts.inFirstOrder, Bool.and_eq_true] at h
    simp [LcCode.altsLits, code_lits_empty b h.1.2, alts_lits_empty rest h.2]
end

/-- For a Phase-1 first-order module, `lowerModule m = .ok tfs` reduces directly to
`m.decls.mapM (lowerDecl (firstOrderLEnv m)) = .ok tfs` (no `lcnf_apply_k` functions, no
once-cell globals). -/
theorem lowerModule_firstOrder_decls {m : LcModule} {tfs : List Frontend.C0.TFlatFn}
    (hfrag : m.inFirstOrderFragment = true) (hlow : lowerModule m = .ok tfs) :
    m.decls.mapM (lowerDecl (firstOrderLEnv m)) = .ok tfs := by
  obtain ⟨hpap, hmax⟩ := inFirstOrderFragment_no_closures hfrag
  simp only [LcModule.inFirstOrderFragment, Bool.and_eq_true, List.all_eq_true] at hfrag
  have hconsts : (m.decls.filter fun d => d.params.isEmpty && !d.retTy.isScalar) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro d hd
    have hdi := hfrag.2 d hd
    simp only [LcDecl.inFirstOrder, Bool.and_eq_true, Bool.not_eq_true'] at hdi
    simpa using hdi.1.1.2
  have hlits1 : (m.decls.map (·.body.lits)).flatMap (·.1) = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro s hs
    obtain ⟨p, hp, hmem⟩ := List.mem_flatMap.mp hs
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hp
    have hdi := hfrag.2 d hd
    simp only [LcDecl.inFirstOrder, Bool.and_eq_true] at hdi
    rw [code_lits_empty d.body hdi.2] at hmem
    cases hmem
  have hlits2 : (m.decls.map (·.body.lits)).flatMap (·.2) = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro n hn
    obtain ⟨p, hp, hmem⟩ := List.mem_flatMap.mp hn
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hp
    have hdi := hfrag.2 d hd
    simp only [LcDecl.inFirstOrder, Bool.and_eq_true] at hdi
    rw [code_lits_empty d.body hdi.2] at hmem
    cases hmem
  have hclo : m.cloTargets = .ok [] := by
    simp [LcModule.cloTargets, hpap, Pure.pure, Except.pure]
  unfold lowerModule at hlow
  rw [hclo] at hlow
  simp only [Bind.bind, Except.bind, hconsts, hlits1, hlits2, hpap, hmax, dedupStr, dedupNat,
    List.zip_nil_left, List.foldl_nil, List.length_nil, List.isEmpty_nil, List.range_zero,
    List.mapM_nil, List.append_nil, ↓reduceIte, Pure.pure, Except.pure] at hlow
  have h0lt : ¬ (0 + 0 + 0 > rtGlobalSlots) := by decide
  rw [ite_eq_right h0lt] at hlow
  unfold firstOrderLEnv
  cases hmap : m.decls.mapM (lowerDecl
      { decls := m.decls.foldl (fun s d => (d.name, d) :: s) []
        funIds := [], globals := [], strLits := [], bigNatLits := [] }) with
  | error e => rw [hmap] at hlow; cases hlow
  | ok fns =>
    rw [hmap] at hlow
    dsimp only at hlow
    split at hlow
    · cases hlow
    · cases hlow; rfl

theorem mapM_ok_mem {α β ε : Type} {f : α → Except ε β} :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = .ok ys →
      ∀ x ∈ xs, ∃ y ∈ ys, f x = .ok y
  | [], _, _, _, hx => by cases hx
  | x :: xs, ys, h, z, hz => by
    simp only [List.mapM_cons] at h
    cases hfx : f x with
    | error e => simp [hfx, Bind.bind, Except.bind] at h
    | ok y =>
      cases hxs : xs.mapM f with
      | error e => simp [hfx, hxs, Bind.bind, Except.bind] at h
      | ok ys' =>
        simp only [hfx, hxs, Bind.bind, Except.bind, Pure.pure, Except.pure,
          Except.ok.injEq] at h
        subst h
        rcases List.mem_cons.mp hz with rfl | hz'
        · exact ⟨y, List.mem_cons_self .., hfx⟩
        · obtain ⟨y', hy', hfy'⟩ := mapM_ok_mem hxs z hz'
          exact ⟨y', List.mem_cons_of_mem _ hy', hfy'⟩

theorem mapM_ok_mem_inv {α β ε : Type} {f : α → Except ε β} :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = .ok ys →
      ∀ y ∈ ys, ∃ x ∈ xs, f x = .ok y
  | [], ys, h, y, hy => by
    simp only [List.mapM_nil, Pure.pure, Except.pure, Except.ok.injEq] at h
    subst h; cases hy
  | x :: xs, ys, h, y, hy => by
    simp only [List.mapM_cons] at h
    cases hfx : f x with
    | error e => simp [hfx, Bind.bind, Except.bind] at h
    | ok y0 =>
      cases hxs : xs.mapM f with
      | error e => simp [hfx, hxs, Bind.bind, Except.bind] at h
      | ok ys' =>
        simp only [hfx, hxs, Bind.bind, Except.bind, Pure.pure, Except.pure,
          Except.ok.injEq] at h
        subst h
        rcases List.mem_cons.mp hy with rfl | hy'
        · exact ⟨x, List.mem_cons_self .., hfx⟩
        · obtain ⟨x', hx', hfx'⟩ := mapM_ok_mem_inv hxs y hy'
          exact ⟨x', List.mem_cons_of_mem _ hx', hfx'⟩

/-! ## 2. Compositional Bridge: `finishFn`, `loadExtras`, `withParams`, & `lowerDecl` -/

/-- Direct bridge from `finishFn` + `LExpr.wp` to `Func.wp` of `TFlatFn.toFn.body`, via
`LExprSem.TFlatFn.wp_of_lExpr`. -/
theorem finishFn_wp_of_lExpr {nm : Sym} {ps : List Frontend.C0.LVar} {ret : Ty} {body : LExpr}
    {fn : Frontend.C0.TFlatFn} (hfin : finishFn nm ps ret body = .ok fn) :
    fn.name = nm ∧
    ∃ (ha : fn.toFn.as = ps.map (·.ty)) (hr : fn.toFn.rs = [ret]),
      ∀ (Γ : Env) (xs : Tup Val fn.toFn.as) (m : Mem 64) (Q : Post fn.toFn.rs) (X : XPost),
        LExpr.wp Γ (hr ▸ Q) X body
          (Frontend.C0.VEnv.empty.bind ps (ps.map (·.ty)) (ha ▸ xs)) JEnv.empty m →
        Func.wp Γ fn.toFn.body xs m Q X := by
  unfold finishFn at hfin
  cases htf : lExprToTFlat (({} : LFlatCtx).pushVars ps) [ret] body with
  | error e => simp [htf, Bind.bind, Except.bind] at hfin
  | ok tf =>
    simp only [htf, Bind.bind, Except.bind] at hfin
    split at hfin
    · simp only [Pure.pure, Except.pure, Except.ok.injEq] at hfin
      subst hfin
      exact ⟨rfl, rfl, rfl,
        fun Γ xs m Q X hwp => Frontend.C0.TFlatFn.wp_of_lExpr htf Γ xs m Q X hwp⟩
    · cases hfin

private theorem lm_bind_run {α β : Type} (x : LM α) (f : α → LM β) (n : Nat) :
    (x >>= f).run n =
      match x.run n with
      | Except.ok (a, n') => (f a).run n'
      | Except.error e => Except.error e := by
  simp only [Bind.bind, StateT.bind, StateT.run, Except.bind]
  cases x n <;> rfl

private theorem lm_pure_run {α : Type} (a : α) (n : Nat) :
    (pure a : LM α).run n = Except.ok (a, n) := rfl

/-- `loadAt` WP helper when the loaded value is known at `base + off`. -/
theorem loadAt_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {t : Ty} {x : LArg} {off : Nat} {k : LArg → LM LExpr} {n n' : Nat} {e : LExpr}
    {ρ : Frontend.C0.VEnv} {J : JEnv} {m : Mem 64} {base : BitVec 64} {val : Val t}
    (hrun : (loadAt t x off k).run n = .ok (e, n'))
    (hx : LArg.eval ρ i64 x = some base)
    (hload : loadVal m t (base + BitVec.ofNat 64 off) = some val)
    (hk : ∀ (lv : Frontend.C0.LVar) (ek : LExpr) (ρ' : Frontend.C0.VEnv),
      n ≤ lv.id → lv.ty = t →
      (k (vArg lv)).run (lv.id + 1) = .ok (ek, n') →
      LArg.eval ρ' t (vArg lv) = some val →
      (∀ a u, argIdsBelow a n → LArg.eval ρ' u a = LArg.eval ρ u a) →
      LExpr.wp Γ Q X ek ρ' J m) :
    LExpr.wp Γ Q X e ρ J m := by
  unfold loadAt addrOf at hrun
  by_cases hoff : (off == 0) = true
  · have hoff0 : off = 0 := by simpa using hoff
    subst hoff0
    simp only [beq_self_eq_true, ↓reduceIte, lm_bind_run, freshVar_run] at hrun
    cases hkr : (k (vArg { id := n, name := "", ty := t })).run (n + 1) with
    | error err => simp [hkr] at hrun
    | ok p =>
      rcases p with ⟨ek, nk⟩
      simp only [hkr, lm_pure_run, Except.ok.injEq, Prod.mk.injEq] at hrun
      rcases hrun with ⟨rfl, rfl⟩
      refine ⟨rfl, base, hx, val, by simpa using hload, ?_⟩
      exact hk { id := n, name := "", ty := t } ek (ρ.set n t val)
        (Nat.le_refl _) rfl hkr
        (LArg.eval_vArg_set_self ρ { id := n, name := "", ty := t } val)
        (fun a u ha => LArg.eval_set_of_ltBound ha (Nat.le_refl _))
  · simp only [hoff, Bool.false_eq_true, ↓reduceIte, add64, op1, lm_bind_run, freshVar_run] at hrun
    cases hkr : (k (vArg { id := n + 1, name := "", ty := t })).run (n + 2) with
    | error err => simp [hkr] at hrun
    | ok p =>
      rcases p with ⟨ek, nk⟩
      simp only [hkr, lm_pure_run, Except.ok.injEq, Prod.mk.injEq] at hrun
      rcases hrun with ⟨rfl, rfl⟩
      dsimp only [LExpr.wp, evalArgs, imm64, imm]
      rw [hx, LArg.eval_imm_self]
      refine ⟨rfl, (base, BitVec.ofNat 64 off, ()), rfl, ?_⟩
      dsimp only [OpCode.wp, Frontend.C0.VEnv.bind]
      refine ⟨rfl, base + BitVec.ofNat 64 off,
        LArg.eval_vArg_set_self ρ { id := n, name := "", ty := i64 } _, val, hload, ?_⟩
      exact hk { id := n + 1, name := "", ty := t } ek
        ((ρ.set n i64 (base + BitVec.ofNat 64 off)).set (n + 1) t val)
        (Nat.le_succ n) rfl hkr
        (LArg.eval_vArg_set_self _ { id := n + 1, name := "", ty := t } val)
        (fun a u ha => by
          rw [LArg.eval_set_of_ltBound ha (Nat.le_succ n),
            LArg.eval_set_of_ltBound ha (Nat.le_refl n)])

private theorem loadVal_extraArgs_bits {rt : BitVec 64} {σ : HState} {R : Mem 64 → Prop}
    {m : Mem 64} {i w : Nat}
    (hi : i < σ.st.extraArgs.length) (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64)
    (hm : (σ.mem rt ⋆ R) m) :
    loadVal m (.bits w) (rt + BitVec.ofNat 64 (rtExtraOff + 8 * i)) =
      some ((σ.st.extraArgs[i]'hi).setWidth w) := by
  have hm' : (array64 rt σ.st.extraArgs ⋆
      ((array64 (rt + BitVec.ofNat 64 rtGlobalsOff) σ.st.globals ⋆
        array64 (rt + 33024#64) σ.st.freeList ⋆
        LcnfC0Rt.At rt σ.st.hdr ⋆
        array64 σ.st.hdr.s_work σ.st.workBuf ⋆
        smallPoolsAt σ.st.freeList σ.st.smallPools rtNumClasses ⋆
        largeFreeList σ.st.hdr.s_large_free σ.st.largeNodes ⋆
        region σ.st.hdr.s_cur σ.st.rem) ⋆
       cell64 (rt + 33672#64) σ.scr ⋆
       cell64 (rt + 33680#64) (BitVec.ofNat 64 σ.scrLimbs.length) ⋆
       array64 σ.scr σ.scrLimbs ⋆
       lcnfHeap σ.objs ⋆ R)) m := by
    unfold HState.mem fullRtInv rtC0Inv at hm
    exact sep_cast hm (by ac_rfl)
  rw [array64_focus rt σ.st.extraArgs hi, sep_assoc] at hm'
  simpa [rtExtraOff] using loadVal_bits_of_cell64 hw hm'

private theorem lcTy_width_cases (t : LcTy) :
    t.width = 8 ∨ t.width = 16 ∨ t.width = 32 ∨ t.width = 64 := by
  cases t <;> simp [LcTy.width]

/-- `loadExtras` WP bridge: reloading spilled parameters `i..` from `rt->extra_args` succeeds
under `(σ.mem rt ⋆ R) m` and yields fresh `LArg`s matching `spilledWords (extraArgs.drop i) ts`.
-/
theorem loadExtras_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {rt : BitVec 64} {rtArg : LArg} {σ : HState} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (σ.mem rt ⋆ R) m) :
    ∀ (i : Nat) (lctys : List LcTy) (k : List LArg → LM LExpr) (n n' : Nat)
      (e : LExpr) (ρ : Frontend.C0.VEnv) (J : JEnv),
      (loadExtras rtArg i (lctys.map LcTy.toTTy) k).run n = .ok (e, n') →
      argIdsBelow rtArg n →
      LArg.eval ρ i64 rtArg = some rt →
      i + lctys.length ≤ σ.st.extraArgs.length →
      (∀ (extras : List LArg) (ek : LExpr) (ρ' : Frontend.C0.VEnv) (nk : Nat),
        n ≤ nk →
        (k extras).run nk = .ok (ek, n') →
        extras.length = lctys.length →
        (∀ a ∈ extras, argIdsBelow a nk) →
        (∀ a u, argIdsBelow a n → LArg.eval ρ' u a = LArg.eval ρ u a) →
        (∃ (xs : Tup Val (lctys.map LcTy.toTTy)),
          evalArgs ρ' (lctys.map LcTy.toTTy) extras = some xs ∧
          wordsOfTup xs = spilledWords (σ.st.extraArgs.drop i) (lctys.map LcTy.toTTy)) →
        LExpr.wp Γ Q X ek ρ' J m) →
      LExpr.wp Γ Q X e ρ J m
  | i, [], k, n, n', e, ρ, J, hrun, _, _, _, hk =>
    hk [] e ρ n (Nat.le_refl _) hrun rfl (fun _ h => by cases h) (fun _ _ _ => rfl)
      ⟨(), rfl, by simp [wordsOfTup, spilledWords]⟩
  | i, t :: ts, k, n, n', e, ρ, J, hrun, hrtLt, hrtEv, hlen, hk => by
    have hi : i < σ.st.extraArgs.length := by simp at hlen; omega
    have hload := loadVal_extraArgs_bits (w := t.width) hi (lcTy_width_cases t) hm
    refine loadAt_wp hrun hrtEv hload ?_
    intro lv ek1 ρ1 hlvGe hlvTy hrun1 hlvEv hpres1
    have hrtLt1 : argIdsBelow rtArg (lv.id + 1) := argIdsBelow_mono (by omega) hrtLt
    have hrtEv1 : LArg.eval ρ1 i64 rtArg = some rt := by rw [hpres1 rtArg i64 hrtLt]; exact hrtEv
    have hlen1 : (i + 1) + ts.length ≤ σ.st.extraArgs.length := by simp at hlen; omega
    refine loadExtras_wp hm (i + 1) ts (fun vs => k (vArg lv :: vs)) (lv.id + 1) n' ek1 ρ1 J
      hrun1 hrtLt1 hrtEv1 hlen1 ?_
    intro extras ek ρ2 nk hnk hrun2 hexLen hexLt hpres2 ⟨xs, hxsEv, hxsWords⟩
    refine hk (vArg lv :: extras) ek ρ2 nk (by omega) hrun2 (by simp [hexLen]) ?_ ?_ ?_
    · intro a ha
      rcases List.mem_cons.mp ha with rfl | ha'
      · exact argIdsBelow_mono hnk (argIdsBelow_vArg (Nat.lt_succ_self lv.id))
      · exact hexLt a ha'
    · intro a u ha
      rw [hpres2 a u (argIdsBelow_mono (by omega) ha), hpres1 a u ha]
    · have hdrop : σ.st.extraArgs.drop i = (σ.st.extraArgs[i]'hi) :: σ.st.extraArgs.drop (i + 1) :=
        List.drop_eq_getElem_cons hi
      have hlvEv2 : LArg.eval ρ2 t.toTTy (vArg lv) =
          some ((σ.st.extraArgs[i]'hi).setWidth t.width) := by
        rw [hpres2 (vArg lv) t.toTTy (argIdsBelow_vArg (Nat.lt_succ_self lv.id))]
        exact hlvEv
      refine ⟨((σ.st.extraArgs[i]'hi).setWidth t.width, xs), ?_, ?_⟩
      · show evalArgs ρ2 (t.toTTy :: ts.map LcTy.toTTy) (vArg lv :: extras) = _
        unfold evalArgs
        rw [hlvEv2, hxsEv]
      · rw [hdrop]
        change ⟨t.toTTy, (σ.st.extraArgs[i]'hi).setWidth t.width⟩ :: wordsOfTup xs =
          ⟨.bits t.width, (σ.st.extraArgs[i]'hi).setWidth t.width⟩ ::
            spilledWords (σ.st.extraArgs.drop (i + 1)) (ts.map LcTy.toTTy)
        rw [hxsWords]; rfl

private theorem withParams_run (tys : List Ty) (k : LArg → List LArg → LM LExpr)
    {ps : List Frontend.C0.LVar} {body : LExpr} {nEnd : Nat}
    (h : (withParams tys k).run 1 = .ok ((ps, body), nEnd)) :
    let rtV : Frontend.C0.LVar := { id := 1, name := "", ty := i64 }
    let regVs : List Frontend.C0.LVar := mkFreshVars (tys.take regArgs) 2
    ps = rtV :: regVs ∧
    (loadExtras (vArg rtV) 0 (tys.drop regArgs)
      (fun extras => k (vArg rtV) (regVs.map vArg ++ extras))).run
        (2 + (tys.take regArgs).length) = .ok (body, nEnd) := by
  unfold withParams at h
  simp only [lm_bind_run, freshVar_run, mapM_freshVar_run] at h
  dsimp only
  cases hle : (loadExtras (vArg { id := 1, name := "", ty := i64 }) 0 (tys.drop regArgs)
      (fun extras => k (vArg { id := 1, name := "", ty := i64 })
        ((mkFreshVars (tys.take regArgs) 2).map vArg ++ extras))).run
          (2 + (tys.take regArgs).length) with
  | error e =>
    have h1 : 1 + 1 = 2 := rfl
    rw [h1] at h
    rw [hle] at h
    cases h
  | ok p2 =>
    rcases p2 with ⟨b2, n2⟩
    have h1 : 1 + 1 = 2 := rfl
    rw [h1] at h
    rw [hle] at h
    simp only [lm_pure_run, Except.ok.injEq, Prod.mk.injEq] at h
    rcases h with ⟨⟨rfl, rfl⟩, rfl⟩
    exact ⟨rfl, rfl⟩

private theorem lowerDecl_unpack {env : LEnv} {d : LcDecl} {fn : Frontend.C0.TFlatFn}
    (hlow : lowerDecl env d = .ok fn) :
    ∃ (ps : List Frontend.C0.LVar) (body : LExpr) (nEnd : Nat),
      (withParams (d.params.map (·.ty.toTTy)) fun rt pargs => do
        let c0 : LCtx := { fn := d.name, rt, retTy := d.retTy, params := d.params.map (·.ty) }
        if hasSelfTail d.name d.params.length d.body then
          let lbl ← fresh
          let lvs ← (d.params.map (·.ty.toTTy)).mapM freshVar
          let b ← lowerCode env ({ c0 with loop? := some lbl }.bindAll d.params (lvs.map vArg))
            d.body
          pure (.group [(lbl, lvs, b)] (.jump lbl (d.params.map (·.ty.toTTy)) pargs))
        else lowerCode env (c0.bindAll d.params pargs) d.body).run 1 = .ok ((ps, body), nEnd) ∧
      finishFn (mangleLc d.name) ps d.retTy.toTTy body = .ok fn := by
  unfold lowerDecl at hlow
  simp only [Bind.bind, Except.bind] at hlow
  split at hlow
  · cases hlow
  · rename_i p hp
    rcases p with ⟨⟨ps, body⟩, nEnd⟩
    exact ⟨ps, body, nEnd, hp, hlow⟩

/-- Signature shape of every function produced by `lowerDecl`. -/
theorem lowerDecl_sig {env : LEnv} {d : LcDecl} {fn : Frontend.C0.TFlatFn}
    (hlow : lowerDecl env d = .ok fn) :
    fn.name = mangleLc d.name ∧
    fn.as = i64 :: (d.params.map (·.ty.toTTy)).take regArgs ∧
    fn.rs = [d.retTy.toTTy] := by
  obtain ⟨ps, body, nEnd, hact, hfin⟩ := lowerDecl_unpack hlow
  obtain ⟨hnm, ha, hr, _⟩ := finishFn_wp_of_lExpr hfin
  obtain ⟨rfl, _⟩ := withParams_run _ _ hact
  exact ⟨hnm, by simpa [Frontend.C0.TFlatFn.toFn, mkFreshVars_map_ty] using ha, hr⟩

private theorem paramsMatch_of_wordsOfTup :
    ∀ {ps : List LcParam} (xs : Tup Val (ps.map (·.ty.toTTy))),
      paramsMatch ps (wordsOfTup xs)
  | [], () => trivial
  | _ :: _, (_, xs) => ⟨rfl, paramsMatch_of_wordsOfTup xs⟩

private theorem evalArgs_append {ρ : Frontend.C0.VEnv} :
    ∀ {ts₁ ts₂ : List Ty} {as₁ as₂ : List LArg}
      {xs₁ : Tup Val ts₁} {xs₂ : Tup Val ts₂},
      evalArgs ρ ts₁ as₁ = some xs₁ → evalArgs ρ ts₂ as₂ = some xs₂ →
      ∃ xs : Tup Val (ts₁ ++ ts₂),
        evalArgs ρ (ts₁ ++ ts₂) (as₁ ++ as₂) = some xs ∧
        wordsOfTup xs = wordsOfTup xs₁ ++ wordsOfTup xs₂
  | [], _, [], _, (), xs₂, _, h2 => ⟨xs₂, h2, rfl⟩
  | [], _, _ :: _, _, _, _, h1, _ => by cases h1
  | _ :: _, _, [], _, _, _, h1, _ => by cases h1
  | t :: ts₁, ts₂, a :: as₁, as₂, (x, xs₁), xs₂, h1, h2 => by
    dsimp only [evalArgs] at h1
    cases ha : LArg.eval ρ t a with
    | none => simp [ha] at h1
    | some v =>
      cases has : evalArgs ρ ts₁ as₁ with
      | none => simp [ha, has] at h1
      | some vs =>
        simp only [ha, has, Option.some.injEq, Prod.mk.injEq] at h1
        rcases h1 with ⟨rfl, rfl⟩
        obtain ⟨xs, hev, hws⟩ := evalArgs_append has h2
        refine ⟨(v, xs), ?_, ?_⟩
        · simp [List.cons_append, evalArgs, ha, hev]
        · simp [wordsOfTup, hws]

private theorem evalArgs_cons_eq_some {ρ : Frontend.C0.VEnv} {t : Ty} {ts : List Ty}
    {a : LArg} {as : List LArg} {x : Val t} {xs : Tup Val ts}
    (h : evalArgs ρ (t :: ts) (a :: as) = some (x, xs)) :
    LArg.eval ρ t a = some x ∧ evalArgs ρ ts as = some xs := by
  unfold evalArgs at h
  cases ha : LArg.eval ρ t a with
  | none => rw [ha] at h; cases h
  | some v =>
    cases has : evalArgs ρ ts as with
    | none => rw [ha, has] at h; cases h
    | some vs => rw [ha, has] at h; cases h; exact ⟨rfl, rfl⟩

private theorem varRel_bindAll_of_evalArgs :
    ∀ {ps : List LcParam} {as : List LArg} {xs : Tup Val (ps.map (·.ty.toTTy))}
      {c : LCtx} {ρH : HValEnv} {ρL : Frontend.C0.VEnv},
      VarRel c ρH ρL → evalArgs ρL (ps.map (·.ty.toTTy)) as = some xs →
      VarRel (c.bindAll ps as) (ρH.bindAll ps (wordsOfTup xs)) ρL
  | [], [], (), _, _, _, hvr, _ => hvr
  | [], _ :: _, _, _, _, _, _, h => by cases h
  | _ :: _, [], _, _, _, _, _, h => by cases h
  | p :: ps, a :: as, (x, xs), c, ρH, ρL, hvr, h => by
    obtain ⟨ha, has⟩ := evalArgs_cons_eq_some (t := p.ty.toTTy) (ts := ps.map (·.ty.toTTy)) h
    simp only [LCtx.bindAll, List.zip_cons_cons, List.foldl_cons, HValEnv.bindAll, wordsOfTup]
    exact varRel_bindAll_of_evalArgs
      (hvr.bind_lcVar (x := p.id) (a := a) (ty := p.ty) (w := ⟨p.ty.toTTy, x⟩) rfl ha) has

private theorem evalArgs_cast {ρ : Frontend.C0.VEnv} {ts₁ ts₂ : List Ty} (h : ts₁ = ts₂)
    {as : List LArg} {xs : Tup Val ts₁} (he : evalArgs ρ ts₁ as = some xs) :
    evalArgs ρ ts₂ as = some (h ▸ xs) := by
  cases h; exact he

private theorem wordsOfTup_cast {ts₁ ts₂ : List Ty} (h : ts₁ = ts₂) (xs : Tup Val ts₁) :
    wordsOfTup (h ▸ xs) = wordsOfTup xs := by
  cases h; rfl

private theorem bind_cons_cast (ρ : Frontend.C0.VEnv) (v : Frontend.C0.LVar)
    (vs : List Frontend.C0.LVar) {t : Ty} {ts : List Ty} (ht : v.ty = t)
    (hts : vs.map (·.ty) = ts) (x : Val t) (xs : Tup Val ts)
    (h : (v :: vs).map (·.ty) = t :: ts) :
    ρ.bind (v :: vs) ((v :: vs).map (·.ty)) (h.symm ▸ ((x, xs) : Tup Val (t :: ts))) =
      (ρ.set v.id t x).bind vs ts xs := by
  cases ht; cases hts; rfl

private theorem jenv_bind_single_cast (lbl : Nat) {ts₁ ts₂ : List Ty} (h : ts₁ = ts₂)
    (k : Cont ts₁) :
    JEnv.empty.bind [lbl] [ts₁] (k, ()) = JEnv.empty.set lbl ts₂ (h ▸ k) := by
  cases h; rfl

private theorem cont_cast_apply {ts₁ ts₂ : List Ty} (h : ts₁ = ts₂) (k : Cont ts₁)
    (xs : Tup Val ts₂) (m : Mem 64) : (h ▸ k) xs m ↔ k (h.symm ▸ xs) m := by
  cases h; exact Iff.rfl

private theorem bindAll_meta (c : LCtx) (ps : List LcParam) (as : List LArg) :
    (c.bindAll ps as).fn = c.fn ∧
    (c.bindAll ps as).rt = c.rt ∧
    (c.bindAll ps as).retTy = c.retTy ∧
    (c.bindAll ps as).params = c.params ∧
    (c.bindAll ps as).jps = c.jps ∧
    (c.bindAll ps as).loop? = c.loop? := by
  induction ps generalizing c as with
  | nil => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | cons p ps ih =>
    cases as with
    | nil => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    | cons a as => exact ih (c.bind p.id a p.ty) as

private theorem lexpr_wp_cast_rs {Γ : Env} {rs₁ rs₂ : List Ty} (h : rs₁ = rs₂)
    {Q : Post rs₂} {X : XPost} {e : LExpr} {ρ : Frontend.C0.VEnv} {J : JEnv} {m : Mem 64}
    (hw : LExpr.wp Γ (h.symm ▸ Q) X e ρ J m) : LExpr.wp Γ Q X e ρ J m := by
  cases h; exact hw

private theorem hpostRel_cast {rt : BitVec 64} {t₁ t₂ : LcTy} (h : t₁ = t₂)
    {R : Mem 64 → Prop} {QH : HPost} {QT : Post [t₂.toTTy]}
    (hp : HPostRel rt t₂ R QH QT) :
    HPostRel rt t₁ R QH ((congrArg (fun t => [t.toTTy]) h).symm ▸ QT) := by
  cases h; exact hp

private theorem hwp_cast_retTy {Δ : HEnv} {rt : BitVec 64} {t₁ t₂ : LcTy} (h : t₁ = t₂)
    {J : HJEnv} {ρ : HValEnv} {Q : HPost} {X : HXPost} {code : LcCode} {σ : HState}
    (hw : HWp Δ rt t₂ J ρ Q X code σ) : HWp Δ rt t₁ J ρ Q X code σ := by
  cases h; exact hw

/-- Body-level simulation interface discharged once in Stage 2 (`lowerCode_sound`):
for any code `code` in the Phase-1 fragment, `HWp` under `HSimInv` implies `LExpr.wp` under any
`Γ` satisfying `HCallEnvOk m Δ Γ`. -/
@[expose] def HCodeSim (m : LcModule) (env : LEnv) : Prop :=
  ∀ (Δ : HEnv) (Γ : Env) (rt : BitVec 64) (R : Mem 64 → Prop)
    (c : LCtx) (n n' : Nat) (code : LcCode) (e : LExpr)
    (QH : HPost) (XH : HXPost) (QT : Post [c.retTy.toTTy]) (XT : XPost)
    (JH : HJEnv) (ρH : HValEnv) (ρL : Frontend.C0.VEnv) (JL : JEnv)
    (σ : HState) (mem : Mem 64),
    HCallEnvOk m Δ Γ →
    HEnv.RetTyped m Δ →
    code.inFirstOrder m.decls (c.jps.map fun p => (p.1, p.2.2)) = true →
    (lowerCode env c code).run n = .ok (e, n') →
    HSimInv Δ rt R c n QH XH QT XT JH ρH ρL JL →
    (∀ lbl, c.loop? = some lbl →
      ∃ d, m.decls.find? (·.name == c.fn) = some d ∧ c.params = d.params.map (·.ty)) →
    HInv rt σ →
    (σ.mem rt ⋆ R) mem →
    HWp Δ rt c.retTy JH ρH QH XH code σ →
    LExpr.wp Γ QT XT e ρL JL mem

/-- Generic `withParams` bridge: given `lowerDecl env d = .ok fn`, unpacks `liftDeclSpec` into
the lowered `withParams` body `LExpr.wp` with `rt` bound and all register + spilled parameters
evaluated into `pargs` matching `wordsOfTup xs ++ spilledWords σ.st.extraArgs spilled`. -/
private theorem withParams_decl_bridge {env : LEnv} {d : LcDecl} {fn : Frontend.C0.TFlatFn}
    (hlow : lowerDecl env d = .ok fn)
    {Γ : Env} {S : HSpec}
    {xs : Tup Val (i64 :: (d.params.map (·.ty.toTTy)).take regArgs)}
    {m : Mem 64} {Q : Post [d.retTy.toTTy]} {X : XPost}
    (hspec : liftDeclSpec S d.params d.retTy xs m Q X)
    (hbody : ∀ (rt : BitVec 64) (σ : HState) (R : Mem 64 → Prop)
      (pargs : List LArg) (n2 n3 : Nat) (e : LExpr) (ρL : Frontend.C0.VEnv)
      (allXs : Tup Val (d.params.map (·.ty.toTTy))),
      HInv rt σ → (σ.mem rt ⋆ R) m →
      S (wordsOfTup allXs) σ
        (fun r σ' =>
          ∃ h : r.1 = d.retTy.toTTy, ∀ m', HInv rt σ' → (σ'.mem rt ⋆ R) m' → Q (h ▸ r.2, ()) m')
        (fun c σ' =>
          ∀ m', (σ'.mem rt ⋆ R) m' → X "lcnf_panic" [i64, i64] (rt, c, ()) m') →
      argIdsBelow (vArg { id := 1, name := "", ty := i64 }) n2 →
      LArg.eval ρL i64 (vArg { id := 1, name := "", ty := i64 }) = some rt →
      (∀ a ∈ pargs, argIdsBelow a n2) →
      evalArgs ρL (d.params.map (·.ty.toTTy)) pargs = some allXs →
      (if hasSelfTail d.name d.params.length d.body then
        do
          let lbl ← fresh
          let lvs ← (d.params.map (·.ty.toTTy)).mapM freshVar
          let c0 : LCtx :=
            { fn := d.name, rt := vArg { id := 1, name := "", ty := i64 },
              retTy := d.retTy, params := d.params.map (·.ty) }
          let b ← lowerCode env ({ c0 with loop? := some lbl }.bindAll d.params (lvs.map vArg))
            d.body
          pure (.group [(lbl, lvs, b)] (.jump lbl (d.params.map (·.ty.toTTy)) pargs))
       else
        let c0 : LCtx :=
          { fn := d.name, rt := vArg { id := 1, name := "", ty := i64 },
            retTy := d.retTy, params := d.params.map (·.ty) }
        lowerCode env (c0.bindAll d.params pargs) d.body).run n2 = .ok (e, n3) →
      LExpr.wp Γ Q X e ρL JEnv.empty m) :
    ∀ (ha : fn.toFn.as = i64 :: (d.params.map (·.ty.toTTy)).take regArgs)
      (hr : fn.toFn.rs = [d.retTy.toTTy]),
      Func.wp Γ fn.toFn.body (ha.symm ▸ xs) m (hr.symm ▸ Q) X := by
  intro ha hr
  obtain ⟨ps, body, nEnd, hact, hfin⟩ := lowerDecl_unpack hlow
  obtain ⟨_, haFin, hrFin, hwpFin⟩ := finishFn_wp_of_lExpr hfin
  obtain ⟨rfl, hle⟩ := withParams_run _ _ hact
  let tys := d.params.map (·.ty.toTTy)
  let rtV : Frontend.C0.LVar := { id := 1, name := "", ty := i64 }
  let regVs : List Frontend.C0.LVar := mkFreshVars (tys.take regArgs) 2
  let n1 : Nat := 2 + (tys.take regArgs).length
  have hpsMap : (rtV :: regVs).map (·.ty) = i64 :: tys.take regArgs := by
    simp [rtV, regVs, mkFreshVars_map_ty]
  have hcast : haFin ▸ (ha.symm ▸ xs) = hpsMap.symm ▸ xs := by
    cases fn
    dsimp only [Frontend.C0.TFlatFn.toFn] at ha haFin ⊢
    subst ha
    have : haFin = hpsMap.symm := rfl
    rw [this]
  have hQeq : (hrFin ▸ (hr.symm ▸ Q)) = Q := by
    cases fn
    dsimp only [Frontend.C0.TFlatFn.toFn] at hr hrFin ⊢
    subst hr
    rfl
  refine hwpFin Γ (ha.symm ▸ xs) m (hr.symm ▸ Q) X ?_
  rw [hcast, hQeq]
  rcases xs with ⟨rt, regXs⟩
  rcases hspec with ⟨σ, R, hspLen, hinv, hm, hS⟩
  have hbindEq : Frontend.C0.VEnv.empty.bind (rtV :: regVs) ((rtV :: regVs).map (·.ty))
      (hpsMap.symm ▸ ((rt, regXs) : Tup Val (i64 :: tys.take regArgs))) =
      (Frontend.C0.VEnv.empty.set 1 i64 rt).bind regVs (tys.take regArgs) regXs :=
    bind_cons_cast Frontend.C0.VEnv.empty rtV regVs rfl (mkFreshVars_map_ty _ _) rt regXs hpsMap
  rw [hbindEq]
  let ρ0 := (Frontend.C0.VEnv.empty.set 1 i64 rt).bind regVs (tys.take regArgs) regXs
  have hrtEv0 : LArg.eval ρ0 i64 (vArg rtV) = some rt := by
    dsimp only [ρ0, regVs]
    rw [LArg.eval_bind_mkFreshVars_lt (a := vArg rtV) (n := 2)
      (by dsimp [rtV, argIdsBelow, vArg]; omega) regXs]
    exact LArg.eval_vArg_set_self Frontend.C0.VEnv.empty rtV rt
  have hregEv0 : evalArgs ρ0 (tys.take regArgs) (regVs.map vArg) = some regXs :=
    evalArgs_bind_mkFreshVars (tys.take regArgs) 2 (Frontend.C0.VEnv.empty.set 1 i64 rt) regXs
  have hdropMap : tys.drop regArgs =
      ((d.params.drop regArgs).map (·.ty)).map LcTy.toTTy := by
    simp [tys, List.map_drop, List.map_map, Function.comp_def]
  have hspLen' : 0 + ((d.params.drop regArgs).map (·.ty)).length ≤ σ.st.extraArgs.length := by
    simpa [tys, List.length_drop, List.length_map] using hspLen
  rw [hdropMap] at hle
  refine loadExtras_wp hm 0 ((d.params.drop regArgs).map (·.ty)) _ n1 nEnd body ρ0
    JEnv.empty hle (by dsimp [rtV, n1, argIdsBelow, vArg]; omega) hrtEv0 hspLen' ?_
  intro extras ek ρ2 nk hnk hrunBody _ hexLt hpres2 ⟨spXs, hspEv, hspWords⟩
  have hrtEv2 : LArg.eval ρ2 i64 (vArg rtV) = some rt := by
    rw [hpres2 (vArg rtV) i64 (by dsimp [rtV, n1, argIdsBelow, vArg]; omega)]; exact hrtEv0
  have hregLt1 : ∀ a ∈ regVs.map vArg, argIdsBelow a n1 := mkFreshVars_vArg_ltBound
  have hregEv2 : evalArgs ρ2 (tys.take regArgs) (regVs.map vArg) = some regXs := by
    have hcongr : ∀ {ts' : List Ty} {as' : List LArg},
        (∀ a ∈ as', argIdsBelow a n1) → evalArgs ρ2 ts' as' = evalArgs ρ0 ts' as' := by
      intro ts' as' has'
      induction ts' generalizing as' with
      | nil => cases as' <;> rfl
      | cons _ _ ih =>
        cases as' with
        | nil => rfl
        | cons a' as'' =>
          simp only [evalArgs, hpres2 a' _ (has' a' (List.mem_cons_self ..)),
            ih (fun b hb => has' b (List.mem_cons_of_mem _ hb))]
    rw [hcongr hregLt1]; exact hregEv0
  have hspEv' : evalArgs ρ2 (tys.drop regArgs) extras = some (hdropMap.symm ▸ spXs) :=
    evalArgs_cast hdropMap.symm hspEv
  obtain ⟨allXsRaw, hallEvRaw, hallWordsRaw⟩ := evalArgs_append hregEv2 hspEv'
  have hsplit : tys.take regArgs ++ tys.drop regArgs = tys := List.take_append_drop regArgs tys
  let allXs : Tup Val tys := hsplit ▸ allXsRaw
  have hallEv : evalArgs ρ2 tys (regVs.map vArg ++ extras) = some allXs :=
    evalArgs_cast hsplit hallEvRaw
  have hallWords : wordsOfTup allXs =
      wordsOfTup regXs ++ spilledWords σ.st.extraArgs (tys.drop regArgs) := by
    rw [wordsOfTup_cast hsplit allXsRaw, hallWordsRaw, wordsOfTup_cast hdropMap.symm spXs, hspWords]
    simp [hdropMap]
  have hpargsLt : ∀ a ∈ regVs.map vArg ++ extras, argIdsBelow a nk := by
    intro a ha
    rcases List.mem_append.mp ha with ha1 | ha2
    · exact argIdsBelow_mono hnk (hregLt1 a ha1)
    · exact hexLt a ha2
  rw [← hallWords] at hS
  exact hbody rt σ R (regVs.map vArg ++ extras) nk nEnd ek ρ2 allXs hinv hm hS
    (by dsimp [rtV, argIdsBelow, vArg]; omega) hrtEv2 hpargsLt hallEv hrunBody

/-- Compositional declaration bridge (non-self-tail declarations, env-parametric in arbitrary
`Γ` with `HCallEnvOk m Δ Γ`): lifts a body-level `HCodeSim` + Tier-H proof into
`Func.wp Γ fn.toFn.body` for `liftDeclSpec`. -/
theorem lowerDecl_of_body_sim {m : LcModule} {env : LEnv} {d : LcDecl} {fn : Frontend.C0.TFlatFn}
    {Δ : HEnv} {Γ : Env} {S : HSpec}
    (hsim : HCodeSim m env)
    (hΓ : HCallEnvOk m Δ Γ)
    (hret : HEnv.RetTyped m Δ)
    (hdFrag : d.body.inFirstOrder m.decls [] = true)
    (hnotTail : hasSelfTail d.name d.params.length d.body = false)
    (hlow : lowerDecl env d = .ok fn)
    (hS : ∀ rt as σ Q' X', HInv rt σ → paramsMatch d.params as → S as σ Q' X' →
      HWp Δ rt d.retTy HJEnv.empty (HValEnv.empty.bindAll d.params as) Q' X' d.body σ)
    {xs : Tup Val (i64 :: (d.params.map (·.ty.toTTy)).take regArgs)}
    {mem : Mem 64} {Q : Post [d.retTy.toTTy]} {X : XPost}
    (hspec : liftDeclSpec S d.params d.retTy xs mem Q X)
    (ha : fn.toFn.as = i64 :: (d.params.map (·.ty.toTTy)).take regArgs := (lowerDecl_sig hlow).2.1)
    (hr : fn.toFn.rs = [d.retTy.toTTy] := (lowerDecl_sig hlow).2.2) :
    Func.wp Γ fn.toFn.body (ha.symm ▸ xs) mem (hr.symm ▸ Q) X := by
  refine withParams_decl_bridge hlow hspec ?_ ha hr
  intro rt σ R pargs n2 n3 e ρL allXs hinv hm hSrun hrtLt hrtEv hpargsLt hallEv hrun
  simp only [hnotTail, Bool.false_eq_true, ↓reduceIte] at hrun
  let rtArg : LArg := vArg { id := 1, name := "", ty := i64 }
  let c0 : LCtx := { fn := d.name, rt := rtArg, retTy := d.retTy, params := d.params.map (·.ty) }
  let QH : HPost := fun r σ' =>
    ∃ h : r.1 = d.retTy.toTTy, ∀ m', HInv rt σ' → (σ'.mem rt ⋆ R) m' → Q (h ▸ r.2, ()) m'
  let XH : HXPost := fun c σ' =>
    ∀ m', (σ'.mem rt ⋆ R) m' → X "lcnf_panic" [i64, i64] (rt, c, ()) m'
  have hpm : paramsMatch d.params (wordsOfTup allXs) := paramsMatch_of_wordsOfTup allXs
  have hwpH := hS rt (wordsOfTup allXs) σ QH XH hinv hpm hSrun
  have hc0Ids : ctxIdsBelow c0 n2 :=
    ⟨hrtLt, fun _ h => (by cases h), fun _ h => (by cases h), fun _ h => (by cases h)⟩
  have hmeta := bindAll_meta c0 d.params pargs
  have hretEq : (c0.bindAll d.params pargs).retTy = d.retTy := hmeta.2.2.1
  have hQRel0 : HPostRel rt d.retTy R QH Q := fun r σ' ⟨h0, hk⟩ h m' hinv' hm' => by
    have : h = h0 := rfl; exact hk m' hinv' hm'
  have hinvSim : HSimInv Δ rt R (c0.bindAll d.params pargs) n2 QH XH
      ((congrArg (fun t => [t.toTTy]) hretEq).symm ▸ Q) X
      HJEnv.empty (HValEnv.empty.bindAll d.params (wordsOfTup allXs)) ρL JEnv.empty :=
    { idsOk := ctxIdsBelow_bindAll hc0Ids hpargsLt
      rtOk := by rw [hmeta.2.1]; exact hrtEv
      varRel := varRel_bindAll_of_evalArgs (VarRel.empty c0 ρL) hallEv
      jpRel := JpRel.empty rt R _ hmeta.2.2.2.2.1 HJEnv.empty JEnv.empty
      loopRel := LoopRel.none Δ rt R _ hmeta.2.2.2.2.2 QH XH JEnv.empty
      postRel := hpostRel_cast hretEq hQRel0
      xpostRel := fun code σ' hx m' hm' => hx m' hm' }
  have hdFrag' : d.body.inFirstOrder m.decls
      ((c0.bindAll d.params pargs).jps.map fun p => (p.1, p.2.2)) = true := by
    rw [hmeta.2.2.2.2.1]; exact hdFrag
  exact lexpr_wp_cast_rs (congrArg (fun t => [t.toTTy]) hretEq)
    (hsim Δ Γ rt R (c0.bindAll d.params pargs) n2 n3 d.body e QH XH
      ((congrArg (fun t => [t.toTTy]) hretEq).symm ▸ Q) X
      HJEnv.empty (HValEnv.empty.bindAll d.params (wordsOfTup allXs)) ρL JEnv.empty σ mem
      hΓ hret hdFrag' hrun hinvSim
      (fun _ hlbl => by rw [hmeta.2.2.2.2.2] at hlbl; cases hlbl)
      hinv hm (hwp_cast_retTy hretEq hwpH))

/-- Compositional self-tail loop declaration bridge (env-parametric in arbitrary `Γ`, discharging
the loop-header `.group` by lfp induction on the measure `k : Nat`): lifts `HCodeSim` +
measure-indexed `Δ : Nat → HEnv` into `Func.wp Γ fn.toFn.body` for `liftDeclSpec (Δ k d.name)`. -/
theorem lowerDecl_loop_of_body_sim {m : LcModule} {env : LEnv} {d : LcDecl}
    {fn : Frontend.C0.TFlatFn}
    {Δ : Nat → HEnv} {Γ : Env} {k : Nat}
    (hsim : HCodeSim m env)
    (hrt : Env.le rtCoreCallEnv Γ)
    (hΓ : ∀ j < k, HCallEnvOk m (Δ j) Γ)
    (hret : ∀ j < k, HEnv.RetTyped m (Δ j))
    (hdFrag : d.body.inFirstOrder m.decls [] = true)
    (hmFind : m.decls.find? (·.name == d.name) = some d)
    (hTail : hasSelfTail d.name d.params.length d.body = true)
    (hlow : lowerDecl env d = .ok fn)
    (hstep : ∀ j ≤ k, ∀ rt as σ Q' X', HInv rt σ → paramsMatch d.params as →
      Δ j d.name as σ Q' X' →
      HWp (match j with | 0 => HEnv.bot | j' + 1 => Δ j')
        rt d.retTy HJEnv.empty (HValEnv.empty.bindAll d.params as) Q' X' d.body σ)
    {xs : Tup Val (i64 :: (d.params.map (·.ty.toTTy)).take regArgs)}
    {mem : Mem 64} {Q : Post [d.retTy.toTTy]} {X : XPost}
    (hspec : liftDeclSpec (Δ k d.name) d.params d.retTy xs mem Q X)
    (ha : fn.toFn.as = i64 :: (d.params.map (·.ty.toTTy)).take regArgs := (lowerDecl_sig hlow).2.1)
    (hr : fn.toFn.rs = [d.retTy.toTTy] := (lowerDecl_sig hlow).2.2) :
    Func.wp Γ fn.toFn.body (ha.symm ▸ xs) mem (hr.symm ▸ Q) X := by
  refine withParams_decl_bridge hlow hspec ?_ ha hr
  intro rt σ0 R pargs n2 n3 e ρL initXs hinv0 hm0 hS0 hrtLt hrtEv hpargsLt hallEv hrun
  simp only [hTail, ↓reduceIte, lm_bind_run, fresh_run, mapM_freshVar_run] at hrun
  let tys := d.params.map (·.ty.toTTy)
  let rtArg : LArg := vArg { id := 1, name := "", ty := i64 }
  let c0 : LCtx := { fn := d.name, rt := rtArg, retTy := d.retTy, params := d.params.map (·.ty) }
  let lvs : List Frontend.C0.LVar := mkFreshVars tys (n2 + 1)
  let nBody : Nat := n2 + 1 + tys.length
  let cLoop : LCtx := ({ c0 with loop? := some n2 }).bindAll d.params (lvs.map vArg)
  cases hb : (lowerCode env cLoop d.body).run nBody with
  | error err =>
    rw [show (lowerCode env _ d.body).run (n2 + 1 + tys.length) = Except.error err from hb] at hrun
    cases hrun
  | ok p =>
    rcases p with ⟨bExpr, nEnd⟩
    rw [show (lowerCode env _ d.body).run (n2 + 1 + tys.length) =
        Except.ok (bExpr, nEnd) from hb] at hrun
    simp only [lm_pure_run, Except.ok.injEq, Prod.mk.injEq] at hrun
    rcases hrun with ⟨rfl, rfl⟩
    dsimp only [LExpr.wp]
    intro Js hcl
    rcases Js with ⟨kLoopRaw, ⟨⟩⟩
    have hlvsMap : lvs.map (·.ty) = tys := mkFreshVars_map_ty tys (n2 + 1)
    let kLoop : Cont tys := hlvsMap ▸ kLoopRaw
    have hbindJ : JEnv.empty.bind (lBlockIds [(n2, lvs, bExpr)])
        (lBlockSig [(n2, lvs, bExpr)]) (kLoopRaw, ()) = JEnv.empty.set n2 tys kLoop :=
      jenv_bind_single_cast n2 hlvsMap kLoopRaw
    have hclLoop : ∀ (xs' : Tup Val tys) (m' : Mem 64),
        LExpr.wp Γ Q X bExpr (ρL.bind lvs tys xs') (JEnv.empty.set n2 tys kLoop) m' →
        kLoop xs' m' := by
      intro xs' m' hwpB
      refine (cont_cast_apply hlvsMap kLoopRaw xs' m').mpr ?_
      have h1 := hcl.1 (hlvsMap.symm ▸ xs') m'
      rw [hbindJ] at h1
      have hbindEq : ρL.bind lvs (lvs.map (·.ty)) (hlvsMap.symm ▸ xs') = ρL.bind lvs tys xs' := by
        have haux : ∀ {ts₁ ts₂ : List Ty} (h : ts₁ = ts₂) (xs : Tup Val ts₂),
            ρL.bind lvs ts₁ (h.symm ▸ xs) = ρL.bind lvs ts₂ xs := by
          intro ts₁ ts₂ h xs; cases h; rfl
        exact haux hlvsMap xs'
      rw [hbindEq] at h1
      exact h1 hwpB
    have hloopInd : ∀ (j : Nat), j ≤ k →
        ∀ (ws : List Word) (σ : HState) (QH : HPost) (XH : HXPost),
          HInv rt σ →
          HPostRel rt d.retTy R QH Q →
          HXPostRel rt R XH X →
          Δ j d.name ws σ QH XH →
          ∀ (xs' : Tup Val tys), wordsOfTup xs' = ws →
            ∀ m', (σ.mem rt ⋆ R) m' → kLoop xs' m' := by
      intro j
      induction j with
      | zero =>
        intro hj ws σ QH XH hinv hQRel hXRel hΔ xs' hws m' hm'
        refine hclLoop xs' m' ?_
        have hpm : paramsMatch d.params ws := hws ▸ paramsMatch_of_wordsOfTup xs'
        have hwpH := hstep 0 hj rt ws σ QH XH hinv hpm hΔ
        have hevLvs := evalArgs_bind_mkFreshVars tys (n2 + 1) ρL xs'
        have hc0Ids : ctxIdsBelow { c0 with loop? := some n2 } nBody :=
          ⟨argIdsBelow_mono (by omega) hrtLt,
           fun _ h => (by cases h),
           fun _ h => (by cases h),
           fun _ h => (by cases h; omega)⟩
        have hmeta := bindAll_meta { c0 with loop? := some n2 } d.params (lvs.map vArg)
        have hretEq : cLoop.retTy = d.retTy := hmeta.2.2.1
        have hparamsEq : cLoop.params.map LcTy.toTTy = tys := by
          rw [hmeta.2.2.2.1]; simp [c0, tys, List.map_map, Function.comp_def]
        have hinvSim : HSimInv HEnv.bot rt R cLoop nBody QH XH
            ((congrArg (fun t => [t.toTTy]) hretEq).symm ▸ Q) X
            HJEnv.empty (HValEnv.empty.bindAll d.params ws) (ρL.bind lvs tys xs')
            (JEnv.empty.set n2 tys kLoop) :=
          { idsOk := ctxIdsBelow_bindAll hc0Ids mkFreshVars_vArg_ltBound
            rtOk := by
              rw [hmeta.2.1]
              exact (LArg.eval_bind_mkFreshVars_lt (a := rtArg)
                (argIdsBelow_mono (Nat.le_succ n2) hrtLt) xs').trans hrtEv
            varRel := by
              subst hws
              exact varRel_bindAll_of_evalArgs (VarRel.empty _ _) hevLvs
            jpRel := JpRel.empty rt R cLoop hmeta.2.2.2.2.1 HJEnv.empty _
            loopRel := fun lbl hlbl => by
              rw [hmeta.2.2.2.2.2] at hlbl
              cases hlbl
              refine ⟨hparamsEq.symm ▸ kLoop, ?_, fun _ _ _ _ hbot => False.elim hbot⟩
              have haux : ∀ {ts₁ ts₂ : List Ty} (h : ts₁ = ts₂) (k : Cont ts₂),
                  (JEnv.empty.set n2 ts₂ k).get n2 ts₁ = some (h.symm ▸ k) := by
                intro ts₁ ts₂ h k; cases h; exact JEnv.get_set_self JEnv.empty n2 ts₁ k
              exact haux hparamsEq kLoop
            postRel := hpostRel_cast hretEq hQRel
            xpostRel := hXRel }
        have hdFrag' :
            d.body.inFirstOrder m.decls (cLoop.jps.map fun p => (p.1, p.2.2)) = true := by
          rw [hmeta.2.2.2.2.1]; exact hdFrag
        exact lexpr_wp_cast_rs (congrArg (fun t => [t.toTTy]) hretEq)
          (hsim HEnv.bot Γ rt R cLoop nBody nEnd d.body bExpr QH XH
            ((congrArg (fun t => [t.toTTy]) hretEq).symm ▸ Q) X
            HJEnv.empty (HValEnv.empty.bindAll d.params ws) (ρL.bind lvs tys xs')
            (JEnv.empty.set n2 tys kLoop) σ m'
            (HCallEnvOk_bot hrt) (HEnv.RetTyped_bot m) hdFrag' hb hinvSim
            (fun _ _ => ⟨d, by rw [hmeta.1]; exact hmFind, hmeta.2.2.2.1⟩)
            hinv hm' (hwp_cast_retTy hretEq hwpH))
      | succ j' ih =>
        intro hj ws σ QH XH hinv hQRel hXRel hΔ xs' hws m' hm'
        refine hclLoop xs' m' ?_
        have hpm : paramsMatch d.params ws := hws ▸ paramsMatch_of_wordsOfTup xs'
        have hwpH := hstep (j' + 1) hj rt ws σ QH XH hinv hpm hΔ
        have hevLvs := evalArgs_bind_mkFreshVars tys (n2 + 1) ρL xs'
        have hc0Ids : ctxIdsBelow { c0 with loop? := some n2 } nBody :=
          ⟨argIdsBelow_mono (by omega) hrtLt,
           fun _ h => (by cases h),
           fun _ h => (by cases h),
           fun _ h => (by cases h; omega)⟩
        have hmeta := bindAll_meta { c0 with loop? := some n2 } d.params (lvs.map vArg)
        have hretEq : cLoop.retTy = d.retTy := hmeta.2.2.1
        have hparamsEq : cLoop.params.map LcTy.toTTy = tys := by
          rw [hmeta.2.2.2.1]; simp [c0, tys, List.map_map, Function.comp_def]
        have hloopRel : LoopRel (Δ j') rt R cLoop QH XH (JEnv.empty.set n2 tys kLoop) := by
          intro lbl hlbl
          rw [hmeta.2.2.2.2.2] at hlbl
          cases hlbl
          refine ⟨hparamsEq.symm ▸ kLoop, ?_, ?_⟩
          · have haux : ∀ {ts₁ ts₂ : List Ty} (h : ts₁ = ts₂) (k : Cont ts₂),
                (JEnv.empty.set n2 ts₂ k).get n2 ts₁ = some (h.symm ▸ k) := by
              intro ts₁ ts₂ h k; cases h; exact JEnv.get_set_self JEnv.empty n2 ts₁ k
            exact haux hparamsEq kLoop
          · intro ws1 σ1 P E hcall hinv1 hP hE xs1 hws1 m1 hm1
            rw [hmeta.1] at hcall
            rw [hretEq] at hP
            have hPRel : HPostRel rt d.retTy R P Q := by
              intro r σ2 hp hrTy m2 hinv2 hm2
              obtain ⟨r', hr', hqr'⟩ := hP r σ2 hp
              rcases r with ⟨rt1, rv1⟩
              dsimp only at hrTy hr'
              subst hrTy
              dsimp only [Word.toWidth, LcTy.toTTy] at hr'
              cases hr'
              have hsw : ∀ (w : Nat) (b : BitVec w), b.setWidth w = b :=
                fun _ _ => BitVec.eq_of_toNat_eq (by simp)
              rw [hsw d.retTy.width rv1] at hqr'
              exact hQRel ⟨d.retTy.toTTy, rv1⟩ σ2 hqr' rfl m2 hinv2 hm2
            have hERel : HXPostRel rt R E X := fun code σ2 he m2 hm2 =>
              hXRel code σ2 (hE code σ2 he) m2 hm2
            refine (cont_cast_apply hparamsEq.symm kLoop xs1 m1).mpr ?_
            have hws1' : wordsOfTup (hparamsEq ▸ xs1) = ws1 := by
              rw [wordsOfTup_cast hparamsEq xs1]; exact hws1
            exact ih (Nat.le_of_succ_le hj) ws1 σ1 P E hinv1 hPRel hERel hcall
              (hparamsEq ▸ xs1) hws1' m1 hm1
        have hinvSim : HSimInv (Δ j') rt R cLoop nBody QH XH
            ((congrArg (fun t => [t.toTTy]) hretEq).symm ▸ Q) X
            HJEnv.empty (HValEnv.empty.bindAll d.params ws) (ρL.bind lvs tys xs')
            (JEnv.empty.set n2 tys kLoop) :=
          { idsOk := ctxIdsBelow_bindAll hc0Ids mkFreshVars_vArg_ltBound
            rtOk := by
              rw [hmeta.2.1]
              exact (LArg.eval_bind_mkFreshVars_lt (a := rtArg)
                (argIdsBelow_mono (Nat.le_succ n2) hrtLt) xs').trans hrtEv
            varRel := by
              subst hws
              exact varRel_bindAll_of_evalArgs (VarRel.empty _ _) hevLvs
            jpRel := JpRel.empty rt R cLoop hmeta.2.2.2.2.1 HJEnv.empty _
            loopRel := hloopRel
            postRel := hpostRel_cast hretEq hQRel
            xpostRel := hXRel }
        have hdFrag' :
            d.body.inFirstOrder m.decls (cLoop.jps.map fun p => (p.1, p.2.2)) = true := by
          rw [hmeta.2.2.2.2.1]; exact hdFrag
        exact lexpr_wp_cast_rs (congrArg (fun t => [t.toTTy]) hretEq)
          (hsim (Δ j') Γ rt R cLoop nBody nEnd d.body bExpr QH XH
            ((congrArg (fun t => [t.toTTy]) hretEq).symm ▸ Q) X
            HJEnv.empty (HValEnv.empty.bindAll d.params ws) (ρL.bind lvs tys xs')
            (JEnv.empty.set n2 tys kLoop) σ m'
            (hΓ j' (Nat.lt_of_lt_of_le (Nat.lt_succ_self j') hj))
            (hret j' (Nat.lt_of_lt_of_le (Nat.lt_succ_self j') hj))
            hdFrag' hb hinvSim
            (fun _ _ => ⟨d, by rw [hmeta.1]; exact hmFind, hmeta.2.2.2.1⟩)
            hinv hm' (hwp_cast_retTy hretEq hwpH))
    dsimp only [LExpr.wp]
    rw [hbindJ]
    refine ⟨kLoop, initXs, JEnv.get_set_self JEnv.empty n2 tys kLoop, hallEv, ?_⟩
    exact hloopInd k (Nat.le_refl k) (wordsOfTup initXs) σ0 _ _ hinv0
      (fun r σ' ⟨h0, hk⟩ h m' hinv' hm' => by have : h = h0 := rfl; exact hk m' hinv' hm')
      (fun code σ' hx m' hm' => hx m' hm')
      hS0 initXs rfl mem hm0

/-- `liftSpec` specialization of `lowerDecl_of_body_sim` when `d.params.length ≤ regArgs` (`5`). -/
theorem lowerDecl_liftSpec_of_body_sim {m : LcModule} {env : LEnv} {d : LcDecl}
    {fn : Frontend.C0.TFlatFn}
    {Δ : HEnv} {Γ : Env} {S : HSpec}
    (hsim : HCodeSim m env) (hΓ : HCallEnvOk m Δ Γ) (hret : HEnv.RetTyped m Δ)
    (hdFrag : d.body.inFirstOrder m.decls [] = true)
    (hnotTail : hasSelfTail d.name d.params.length d.body = false)
    (hlen : d.params.length ≤ regArgs)
    (hlow : lowerDecl env d = .ok fn)
    (hS : ∀ rt as σ Q' X', HInv rt σ → paramsMatch d.params as → S as σ Q' X' →
      HWp Δ rt d.retTy HJEnv.empty (HValEnv.empty.bindAll d.params as) Q' X' d.body σ)
    {xs : Tup Val (i64 :: (d.params.map (·.ty.toTTy)).take regArgs)}
    {mem : Mem 64} {Q : Post [d.retTy.toTTy]} {X : XPost}
    (hspec : liftSpec S ((d.params.map (·.ty.toTTy)).take regArgs) d.retTy.toTTy xs mem Q X)
    (ha : fn.toFn.as = i64 :: (d.params.map (·.ty.toTTy)).take regArgs := (lowerDecl_sig hlow).2.1)
    (hr : fn.toFn.rs = [d.retTy.toTTy] := (lowerDecl_sig hlow).2.2) :
    Func.wp Γ fn.toFn.body (ha.symm ▸ xs) mem (hr.symm ▸ Q) X :=
  lowerDecl_of_body_sim hsim hΓ hret hdFrag hnotTail hlow hS
    ((liftDeclSpec_iff_liftSpec_of_le S d.params d.retTy hlen xs mem Q X).mpr hspec) ha hr

/-- `liftSpec` specialization of `lowerDecl_loop_of_body_sim` when `d.params.length ≤ regArgs`. -/
theorem lowerDecl_loop_liftSpec_of_body_sim {m : LcModule} {env : LEnv} {d : LcDecl}
    {fn : Frontend.C0.TFlatFn}
    {Δ : Nat → HEnv} {Γ : Env} {k : Nat}
    (hsim : HCodeSim m env) (hrt : Env.le rtCoreCallEnv Γ)
    (hΓ : ∀ j < k, HCallEnvOk m (Δ j) Γ) (hret : ∀ j < k, HEnv.RetTyped m (Δ j))
    (hdFrag : d.body.inFirstOrder m.decls [] = true)
    (hmFind : m.decls.find? (·.name == d.name) = some d)
    (hTail : hasSelfTail d.name d.params.length d.body = true)
    (hlen : d.params.length ≤ regArgs)
    (hlow : lowerDecl env d = .ok fn)
    (hstep : ∀ j ≤ k, ∀ rt as σ Q' X', HInv rt σ → paramsMatch d.params as →
      Δ j d.name as σ Q' X' →
      HWp (match j with | 0 => HEnv.bot | j' + 1 => Δ j')
        rt d.retTy HJEnv.empty (HValEnv.empty.bindAll d.params as) Q' X' d.body σ)
    {xs : Tup Val (i64 :: (d.params.map (·.ty.toTTy)).take regArgs)}
    {mem : Mem 64} {Q : Post [d.retTy.toTTy]} {X : XPost}
    (hspec : liftSpec (Δ k d.name) ((d.params.map (·.ty.toTTy)).take regArgs)
      d.retTy.toTTy xs mem Q X)
    (ha : fn.toFn.as = i64 :: (d.params.map (·.ty.toTTy)).take regArgs := (lowerDecl_sig hlow).2.1)
    (hr : fn.toFn.rs = [d.retTy.toTTy] := (lowerDecl_sig hlow).2.2) :
    Func.wp Γ fn.toFn.body (ha.symm ▸ xs) mem (hr.symm ▸ Q) X :=
  lowerDecl_loop_of_body_sim hsim hrt hΓ hret hdFrag hmFind hTail hlow hstep
    ((liftDeclSpec_iff_liftSpec_of_le (Δ k d.name) d.params d.retTy hlen xs mem Q X).mpr hspec)
    ha hr

end LeanQbe.T.LeanLCNF.Sem
