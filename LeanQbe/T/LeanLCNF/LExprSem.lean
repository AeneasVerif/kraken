module

public import LeanQbe.T.Frontend.C0.ToFlat
public import LeanQbe.T.FlatLemmas
public import LeanQbe.T.OpsLemmas

/-!
# Semantics of named-SSA `LExpr` and soundness of `lExprToTFlat`

`Frontend.C0.LExpr` is the named-SSA builder IR shared by the C0 frontend and the `LeanLCNF`
lowering (`Lower.lean` / `Lower1.lean`): variables and join labels are `Nat` ids, binders are
`LVar`s. `lExprToTFlat` scope-checks it into de Bruijn `TFlat`, whose meaning is `T.wp` of its
`denote`ation.

* `LExpr.wp Γ Q X e ρ J m` is the weakest precondition of `e` *directly on names*: `ρ : VEnv`
  maps variable ids to typed values, `J : JEnv` maps label ids to typed continuations. It has
  the shape of `T.wp` (`Env` for calls, `Post` for `ret`, `XPost` for `exit`, the lfp `group`
  rule with `LExpr.closed`). Ill-scoped or ill-typed code (unbound id, type mismatch, binder
  list not matching the result signature) has `wp = False`.
* `lExprToTFlat_sound`: if `lExprToTFlat c rs e = .ok tf` and the de Bruijn environments
  `vs`/`ls` realize `ρ`/`J` through the scope context `c` (`VOk` / `JOk`), then
  `LExpr.wp Γ Q X e ρ J m → T.wp Γ Q X (denote Val Cont tf vs ls) m`.
* `lExprToTFlat_func_sound`: the closed-function corollary against `Func.wp` of `denoteFunc`,
  i.e. of `TFlatFn.toFn` for every function produced by `finishFn` / `lFnToTFlatFn`.

So a proof about lowered code can be carried out on the named `LExpr` the builders produce
(no de Bruijn shifting, no fresh-id bookkeeping beyond the names themselves).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Frontend.C0

open LeanQbe.T

/-! ## Named environments -/

/-- Named value environment: variable id ↦ typed value. -/
@[expose] def VEnv : Type := Nat → Option ((t : Ty) × Val t)

/-- Named label environment: label id ↦ typed join continuation. -/
@[expose] def JEnv : Type := Nat → Option ((ts : List Ty) × Cont ts)

/-- The empty value environment. -/
@[expose] def VEnv.empty : VEnv := fun _ => none

/-- The empty label environment. -/
@[expose] def JEnv.empty : JEnv := fun _ => none

/-- Bind (or shadow) one variable. -/
@[expose] def VEnv.set (ρ : VEnv) (id : Nat) (t : Ty) (v : Val t) : VEnv :=
  fun i => if i = id then some ⟨t, v⟩ else ρ i

/-- Typed variable read. -/
@[expose] def VEnv.get (ρ : VEnv) (id : Nat) (t : Ty) : Option (Val t) :=
  match ρ id with
  | some ⟨u, v⟩ => castTy u t v
  | none => none

/-- Bind binders to a result tuple, left to right (a later binder shadows an earlier one with
the same id, as `LFlatCtx.pushVars`). -/
@[expose] def VEnv.bind (ρ : VEnv) : List LVar → (ts : List Ty) → Tup Val ts → VEnv
  | b :: bs, t :: ts, xs => VEnv.bind (ρ.set b.id t xs.1) bs ts xs.2
  | _, _, _ => ρ

/-- Bind (or shadow) one label. -/
@[expose] def JEnv.set (J : JEnv) (lid : Nat) (ts : List Ty) (k : Cont ts) : JEnv :=
  fun i => if i = lid then some ⟨ts, k⟩ else J i

/-- Typed label read. -/
@[expose] def JEnv.get (J : JEnv) (lid : Nat) (ts : List Ty) : Option (Cont ts) :=
  match J lid with
  | some ⟨us, k⟩ => castListTy us ts k
  | none => none

/-- Bind the labels of a group, left to right. -/
@[expose] def JEnv.bind (J : JEnv) : List Nat → (sig : List (List Ty)) → Tup Cont sig → JEnv
  | l :: ls, ts :: sig, ks => JEnv.bind (J.set l ts ks.1) ls sig ks.2
  | _, _, _ => J

/-- Signature of a block list (the index of `lBlocksToTBlocks`). -/
abbrev lBlockSig (blks : List (Nat × List LVar × LExpr)) : List (List Ty) :=
  blks.map fun (_, ps, _) => ps.map (·.ty)

/-- Label ids of a block list. -/
@[expose] def lBlockIds (blks : List (Nat × List LVar × LExpr)) : List Nat :=
  blks.map (·.1)

/-! ## Operands -/

/-- Value of an operand at expected type `t`. -/
@[expose] def LArg.eval (ρ : VEnv) (t : Ty) : LArg → Option (Val t)
  | .var id t' => if t' = t then ρ.get id t else none
  | .imm t' v => if h : t' = t then some (h ▸ v) else none

/-- Values of an operand list at signature `ts`. -/
@[expose] def evalArgs (ρ : VEnv) : (ts : List Ty) → List LArg → Option (Tup Val ts)
  | [], [] => some ()
  | t :: ts, a :: as =>
    match LArg.eval ρ t a, evalArgs ρ ts as with
    | some v, some vs => some (v, vs)
    | _, _ => none
  | _, _ => none

/-! ## Weakest precondition -/

mutual
/-- Weakest precondition of named-SSA `e` under value environment `ρ`, label environment `J`
and memory `m` (same contract shape as `T.wp`). -/
@[expose] def LExpr.wp (Γ : Env) {rs : List Ty} (Q : Post rs) (X : XPost) :
    LExpr → VEnv → JEnv → Mem 64 → Prop
  | .let_ op bs k, ρ, J, m =>
    bs.map (·.ty) = op.rs ∧ ∃ xs, evalArgs ρ op.sig op.args = some xs ∧
      op.code.wp xs fun r => LExpr.wp Γ Q X k (ρ.bind bs op.rs r) J m
  | .load t a b k, ρ, J, m =>
    b.ty = t ∧ ∃ p, LArg.eval ρ i64 a = some p ∧ ∃ v, loadVal m t p = some v ∧
      LExpr.wp Γ Q X k (ρ.set b.id t v) J m
  | .store t v a k, ρ, J, m =>
    ∃ x p, LArg.eval ρ t v = some x ∧ LArg.eval ρ i64 a = some p ∧
      storeOk m t p ∧ LExpr.wp Γ Q X k ρ J (storeMem m t p x)
  | .call f as bs args binders k, ρ, J, m =>
    binders.map (·.ty) = bs ∧ ∃ xs, evalArgs ρ as args = some xs ∧
      ∃ (P : Post bs) (E : XPost), Γ f as bs xs m P E ∧
        (∀ r m', P r m' → LExpr.wp Γ Q X k (ρ.bind binders bs r) J m') ∧
        (∀ g cs ys m', E g cs ys m' → X g cs ys m')
  | .jnz c t e, ρ, J, m =>
    ∃ b, LArg.eval ρ .bool c = some b ∧
      (b = true → LExpr.wp Γ Q X t ρ J m) ∧ (b = false → LExpr.wp Γ Q X e ρ J m)
  | .jump lid ts args, ρ, J, m =>
    ∃ k xs, J.get lid ts = some k ∧ evalArgs ρ ts args = some xs ∧ k xs m
  | .ret rs' args, ρ, _, m => rs' = rs ∧ ∃ xs, evalArgs ρ rs args = some xs ∧ Q xs m
  | .exit f as args, ρ, _, m => ∃ xs, evalArgs ρ as args = some xs ∧ X f as xs m
  | .hlt, _, _, _ => False
  | .group blocks k, ρ, J, m =>
    ∀ Js : Tup Cont (lBlockSig blocks),
      LExpr.closed Γ Q X blocks ρ (J.bind (lBlockIds blocks) (lBlockSig blocks) Js) Js →
      LExpr.wp Γ Q X k ρ (J.bind (lBlockIds blocks) (lBlockSig blocks) Js) m

/-- Every block of a group implies its join continuation in `Js` (the named `T.Closed`). -/
@[expose] def LExpr.closed (Γ : Env) {rs : List Ty} (Q : Post rs) (X : XPost) :
    (blks : List (Nat × List LVar × LExpr)) → VEnv → JEnv → Tup Cont (lBlockSig blks) → Prop
  | [], _, _, _ => True
  | (_, ps, b) :: rest, ρ, J, Js =>
    (∀ (xs : Tup Val (ps.map (·.ty))) (m : Mem 64),
      LExpr.wp Γ Q X b (ρ.bind ps (ps.map (·.ty)) xs) J m →
        (Js : Cont (ps.map (·.ty)) × Tup Cont (lBlockSig rest)).1 xs m) ∧
    LExpr.closed Γ Q X rest ρ J (Js : Cont (ps.map (·.ty)) × Tup Cont (lBlockSig rest)).2
end

/-! ## Scope contexts realized by de Bruijn environments -/

/-- The de Bruijn value environment `vs` realizes the named `ρ` through the scope context `c`. -/
@[expose] def VOk (c : LFlatCtx) (ρ : VEnv) (vs : List ((t : Ty) × Val t)) : Prop :=
  c.vdepth = vs.length ∧ ∀ id t v, ρ id = some ⟨t, v⟩ →
    ∃ lvl, c.vars.find? (fun p => p.1 == id) = some (id, lvl, t) ∧ lvl < c.vdepth ∧
      lookupV vs t (c.vdepth - 1 - lvl) = some v

/-- The de Bruijn label environment `ls` realizes the named `J` through the scope context `c`. -/
@[expose] def JOk (c : LFlatCtx) (J : JEnv) (ls : List ((ts : List Ty) × Cont ts)) : Prop :=
  c.ldepth = ls.length ∧ ∀ lid ts k, J lid = some ⟨ts, k⟩ →
    ∃ lvl, c.lbls.find? (fun p => p.1 == lid) = some (lid, lvl, ts) ∧ lvl < c.ldepth ∧
      lookupL ls ts (c.ldepth - 1 - lvl) = some k

/-! ## Cast and lookup lemmas -/

private theorem castTy_self {V : Ty → Type} : (t : Ty) → (v : V t) → castTy t t v = some v
  | .bool, _ => rfl
  | .bits _, _ => by dsimp only [castTy]; simp
  | .float _, _ => by dsimp only [castTy]; simp
  | .pair a b, v => by
    dsimp only [castTy]
    cases ha : tyDecEq a a with
    | isFalse hne => exact absurd rfl hne
    | isTrue ea =>
      cases hb : tyDecEq b b with
      | isFalse hne => exact absurd rfl hne
      | isTrue eb =>
        have ha' : ea = rfl := rfl
        have hb' : eb = rfl := rfl
        rw [ha', hb']

private theorem castListTy_self {L : List Ty → Type} (ts : List Ty) (l : L ts) :
    castListTy ts ts l = some l := by
  dsimp only [castListTy]
  cases h : listTyDecEq ts ts with
  | isFalse hne => exact absurd rfl hne
  | isTrue heq =>
    have h' : heq = rfl := rfl
    rw [h']

private theorem castTy_eq_some {V : Ty → Type} {u t : Ty} {v₀ : V u} {v : V t}
    (h : castTy u t v₀ = some v) : ∃ eq : u = t, eq ▸ v₀ = v := by
  cases u with
  | bool =>
    cases t <;> dsimp only [castTy] at h
    · cases h; exact ⟨rfl, rfl⟩
    all_goals cases h
  | bits m =>
    cases t <;> dsimp only [castTy] at h
    · cases h
    · rename_i n
      by_cases hm : m = n
      · subst hm; simp only [↓reduceDIte, Option.some.injEq] at h; subst h; exact ⟨rfl, rfl⟩
      · simp [hm] at h
    all_goals cases h
  | float f =>
    cases t <;> dsimp only [castTy] at h
    · cases h
    · cases h
    · rename_i g
      by_cases hf : f = g
      · subst hf; simp only [↓reduceDIte, Option.some.injEq] at h; subst h; exact ⟨rfl, rfl⟩
      · simp [hf] at h
    · cases h
  | pair a₁ b₁ =>
    cases t <;> dsimp only [castTy] at h
    · cases h
    · cases h
    · cases h
    · rename_i a₂ b₂
      cases ha : tyDecEq a₁ a₂ with
      | isFalse _ => simp [ha] at h
      | isTrue ea =>
        cases hb : tyDecEq b₁ b₂ with
        | isFalse _ => simp [ha, hb] at h
        | isTrue eb =>
          subst ea; subst eb
          simp only [ha, hb, Option.some.injEq] at h
          subst h
          exact ⟨rfl, rfl⟩

private theorem castListTy_eq_some {L : List Ty → Type} {us ts : List Ty} {k₀ : L us} {k : L ts}
    (h : castListTy us ts k₀ = some k) : ∃ eq : us = ts, eq ▸ k₀ = k := by
  dsimp only [castListTy] at h
  cases hd : listTyDecEq us ts with
  | isFalse _ => simp [hd] at h
  | isTrue eq =>
    subst eq
    simp only [hd, Option.some.injEq] at h
    subst h
    exact ⟨rfl, rfl⟩

private theorem lookupV_head {V : Ty → Type} (t : Ty) (v : V t) (vs : List ((u : Ty) × V u)) :
    lookupV (⟨t, v⟩ :: vs) t 0 = some v := by
  dsimp only [lookupV, listGet?]; exact castTy_self t v

private theorem lookupL_head {L : List Ty → Type} (ts : List Ty) (l : L ts)
    (ls : List ((us : List Ty) × L us)) :
    lookupL (⟨ts, l⟩ :: ls) ts 0 = some l := by
  dsimp only [lookupL, listGet?]; exact castListTy_self ts l

/-! ## Scope-invariant preservation (`VOk` and `JOk`) -/

theorem VOk.empty : VOk {} VEnv.empty [] :=
  ⟨rfl, fun _ _ _ h => by cases h⟩

theorem JOk.empty : JOk {} JEnv.empty [] :=
  ⟨rfl, fun _ _ _ h => by cases h⟩

theorem VOk.pushVar {c : LFlatCtx} {ρ : VEnv} {vs : List ((t : Ty) × Val t)}
    (h : VOk c ρ vs) (lv : LVar) {t : Ty} (ht : lv.ty = t) (v : Val t) :
    VOk (c.pushVar lv) (ρ.set lv.id t v) (⟨t, v⟩ :: vs) := by
  rcases h with ⟨hlen, hmem⟩
  refine ⟨by dsimp only [LFlatCtx.pushVar]; rw [List.length_cons, hlen], ?_⟩
  intro id u w hρ
  dsimp only [VEnv.set] at hρ
  by_cases hid : id = lv.id
  · subst hid
    simp only [↓reduceIte, Option.some.injEq] at hρ
    cases hρ
    refine ⟨c.vdepth, ?_, Nat.lt_succ_self _, ?_⟩
    · simp only [LFlatCtx.pushVar, List.find?_cons, beq_self_eq_true, ht]
    · simp only [LFlatCtx.pushVar, Nat.add_sub_cancel, Nat.sub_self]
      exact lookupV_head t v vs
  · simp only [hid, ↓reduceIte] at hρ
    obtain ⟨lvl, hfind, hlt, hlu⟩ := hmem id u w hρ
    refine ⟨lvl, ?_, Nat.lt_succ_of_lt hlt, ?_⟩
    · have hne : (lv.id == id) = false := beq_false_of_ne (Ne.symm hid)
      simp only [LFlatCtx.pushVar, List.find?_cons, hne, hfind]
    · have hidx : (c.pushVar lv).vdepth - 1 - lvl = (c.vdepth - 1 - lvl) + 1 := by
        dsimp only [LFlatCtx.pushVar]; omega
      rw [hidx]
      exact hlu

theorem VOk.pushVars :
    ∀ (bs : List LVar) (ts : List Ty) (xs : Tup Val ts)
      (c : LFlatCtx) (ρ : VEnv) (vs : List ((t : Ty) × Val t)),
      bs.map (·.ty) = ts → VOk c ρ vs →
      VOk (c.pushVars bs) (ρ.bind bs ts xs) (pushTup xs vs)
  | [], [], (), _, _, _, _, h => h
  | b :: bs, t :: ts, (x, xs), c, ρ, vs, hty, h => by
    simp only [List.map_cons, List.cons.injEq] at hty
    rcases hty with ⟨rfl, hts⟩
    dsimp only [LFlatCtx.pushVars, List.foldl_cons, VEnv.bind, pushTup]
    exact VOk.pushVars bs _ xs (c.pushVar b) (ρ.set b.id b.ty x) (⟨b.ty, x⟩ :: vs) hts
      (h.pushVar b rfl x)

theorem JOk.pushVar {c : LFlatCtx} {J : JEnv} {ls : List ((ts : List Ty) × Cont ts)}
    (h : JOk c J ls) (lv : LVar) : JOk (c.pushVar lv) J ls :=
  h

theorem JOk.pushVars (bs : List LVar) {c : LFlatCtx} {J : JEnv}
    {ls : List ((ts : List Ty) × Cont ts)} (h : JOk c J ls) :
    JOk (c.pushVars bs) J ls := by
  induction bs generalizing c with
  | nil => exact h
  | cons _ _ ih => exact ih h

theorem JOk.pushLbl {c : LFlatCtx} {J : JEnv} {ls : List ((ts : List Ty) × Cont ts)}
    (h : JOk c J ls) (lid : Nat) (ts : List Ty) (k : Cont ts) :
    JOk (c.pushLbl lid ts) (J.set lid ts k) (⟨ts, k⟩ :: ls) := by
  rcases h with ⟨hlen, hmem⟩
  refine ⟨by dsimp only [LFlatCtx.pushLbl]; rw [List.length_cons, hlen], ?_⟩
  intro lid' us k' hJ
  dsimp only [JEnv.set] at hJ
  by_cases hid : lid' = lid
  · subst hid
    simp only [↓reduceIte, Option.some.injEq] at hJ
    cases hJ
    refine ⟨c.ldepth, ?_, Nat.lt_succ_self _, ?_⟩
    · simp only [LFlatCtx.pushLbl, List.find?_cons, beq_self_eq_true]
    · simp only [LFlatCtx.pushLbl, Nat.add_sub_cancel, Nat.sub_self]
      exact lookupL_head ts k ls
  · simp only [hid, ↓reduceIte] at hJ
    obtain ⟨lvl, hfind, hlt, hlu⟩ := hmem lid' us k' hJ
    refine ⟨lvl, ?_, Nat.lt_succ_of_lt hlt, ?_⟩
    · have hne : (lid == lid') = false := beq_false_of_ne (Ne.symm hid)
      simp only [LFlatCtx.pushLbl, List.find?_cons, hne, hfind]
    · have hidx : (c.pushLbl lid ts).ldepth - 1 - lvl = (c.ldepth - 1 - lvl) + 1 := by
        dsimp only [LFlatCtx.pushLbl]; omega
      rw [hidx]
      exact hlu

private theorem VOk.pushLbls (blks : List (Nat × List LVar × LExpr))
    {c : LFlatCtx} {ρ : VEnv} {vs : List ((t : Ty) × Val t)} (h : VOk c ρ vs) :
    VOk (blks.foldl (fun acc (lid, ps, _) => acc.pushLbl lid (ps.map (·.ty))) c) ρ vs := by
  induction blks generalizing c with
  | nil => exact h
  | cons _ _ ih => exact ih h

private theorem JOk.pushLbls :
    ∀ (blks : List (Nat × List LVar × LExpr)) (Js : Tup Cont (lBlockSig blks))
      (c : LFlatCtx) (J : JEnv) (ls : List ((ts : List Ty) × Cont ts)),
      JOk c J ls →
      JOk (blks.foldl (fun acc (lid, ps, _) => acc.pushLbl lid (ps.map (·.ty))) c)
        (J.bind (lBlockIds blks) (lBlockSig blks) Js) (pushTup Js ls)
  | [], (), _, _, _, h => h
  | (lid, ps, _) :: rest, (k, Js), c, J, ls, h => by
    dsimp only [List.foldl_cons, lBlockIds, lBlockSig, JEnv.bind, pushTup]
    exact JOk.pushLbls rest Js (c.pushLbl lid (ps.map (·.ty))) (J.set lid _ k)
      (⟨ps.map (·.ty), k⟩ :: ls) (h.pushLbl lid _ k)

/-! ## Operand and label resolution soundness -/

private theorem toFlatArg_sound {c : LFlatCtx} {ρ : VEnv} {vs : List ((t : Ty) × Val t)}
    (hv : VOk c ρ vs) {t : Ty} {a : LArg} {fa : Arg K t} {v : Val t}
    (hflat : toFlatArg c t a = .ok fa) (heval : LArg.eval ρ t a = some v) :
    ∃ a' : Arg Val t, denoteArg vs fa = some a' ∧ a'.val = v := by
  cases a with
  | var id t' =>
    dsimp only [LArg.eval] at heval
    by_cases ht : t' = t
    · subst ht
      simp only [↓reduceIte, VEnv.get] at heval
      cases hρ : ρ id with
      | none => simp [hρ] at heval
      | some p =>
        rcases p with ⟨u, v₀⟩
        simp only [hρ] at heval
        rcases castTy_eq_some heval with ⟨eq, rfl⟩
        cases eq
        obtain ⟨lvl, hfind, _, hlu⟩ := hv.2 id _ v₀ hρ
        simp only [toFlatArg, beq_self_eq_true, ↓reduceIte, LFlatCtx.lookupVar, hfind,
          ↓reduceDIte, Pure.pure, Except.pure, Except.ok.injEq] at hflat
        subst hflat
        exact ⟨.var v₀, by dsimp only [denoteArg]; rw [hlu], rfl⟩
    · simp [ht] at heval
  | imm t' c₀ =>
    dsimp only [LArg.eval] at heval
    by_cases ht : t' = t
    · subst ht
      simp only [↓reduceDIte, Option.some.injEq] at heval
      subst heval
      simp only [toFlatArg, ↓reduceDIte, Pure.pure, Except.pure, Except.ok.injEq] at hflat
      subst hflat
      exact ⟨.imm c₀, rfl, rfl⟩
    · simp [ht] at heval

private theorem toFlatArgs_sound {c : LFlatCtx} {ρ : VEnv} {vs : List ((t : Ty) × Val t)}
    (hv : VOk c ρ vs) :
    ∀ {ts : List Ty} {as : List LArg} {fas : Tup (Arg K) ts} {xs : Tup Val ts},
      toFlatArgs c ts as = .ok fas → evalArgs ρ ts as = some xs →
      ∃ as' : Tup (Arg Val) ts, denoteArgs vs fas = some as' ∧ vals as' = xs
  | [], [], (), (), _, _ => ⟨(), rfl, rfl⟩
  | [], _ :: _, _, _, hflat, _ => by cases hflat
  | _ :: _, [], _, _, hflat, _ => by cases hflat
  | t :: ts, a :: as, fas, xs, hflat, heval => by
    dsimp only [toFlatArgs] at hflat
    cases ha : toFlatArg c t a with
    | error e =>
      simp [ha, Bind.bind, Except.bind] at hflat
    | ok fa =>
      cases has : toFlatArgs c ts as with
      | error e =>
        simp [ha, has, Bind.bind, Except.bind] at hflat
      | ok fas' =>
        simp only [ha, has, Bind.bind, Except.bind, Pure.pure, Except.pure,
          Except.ok.injEq] at hflat
        subst hflat
        dsimp only [evalArgs] at heval
        cases hva : LArg.eval ρ t a with
        | none => simp [hva] at heval
        | some v =>
          cases hvas : evalArgs ρ ts as with
          | none => simp [hva, hvas] at heval
          | some vs' =>
            simp only [hva, hvas, Option.some.injEq] at heval
            subst heval
            obtain ⟨a', hda, hva'⟩ := toFlatArg_sound hv ha hva
            obtain ⟨as', hdas, hvas'⟩ := toFlatArgs_sound hv has hvas
            exact ⟨(a', as'), by dsimp only [denoteArgs]; rw [hda, hdas],
              by dsimp only [vals]; rw [hva', hvas']⟩

private theorem lookupLbl_sound {c : LFlatCtx} {J : JEnv} {ls : List ((ts : List Ty) × Cont ts)}
    (hj : JOk c J ls) {lid : Nat} {ts : List Ty} {idx : Nat} {k : Cont ts}
    (hlbl : c.lookupLbl lid ts = .ok idx) (hget : J.get lid ts = some k) :
    lookupL ls ts idx = some k := by
  dsimp only [JEnv.get] at hget
  cases hJ : J lid with
  | none => simp [hJ] at hget
  | some p =>
    rcases p with ⟨us, k₀⟩
    simp only [hJ] at hget
    rcases castListTy_eq_some hget with ⟨eq, rfl⟩
    cases eq
    obtain ⟨lvl, hfind, _, hlu⟩ := hj.2 lid ts k₀ hJ
    simp only [LFlatCtx.lookupLbl, hfind, beq_self_eq_true, ↓reduceIte,
      Pure.pure, Except.pure, Except.ok.injEq] at hlbl
    subst hlbl
    exact hlu

/-! ## `lExprToTFlat` soundness -/

mutual
/-- Soundness of `lExprToTFlat`: if `e` lowers to `tf` under `c` and `(vs, ls)` realizes
`(ρ, J)` through `c`, then the named weakest precondition `LExpr.wp` implies `T.wp` of
`denote Val Cont tf vs ls`. -/
theorem lExprToTFlat_sound (Γ : Env) {rs : List Ty} (Q : Post rs) (X : XPost) :
    ∀ (e : LExpr) (c : LFlatCtx) (tf : TFlat rs),
      lExprToTFlat c rs e = .ok tf →
      ∀ (ρ : VEnv) (J : JEnv) (vs : List ((t : Ty) × Val t)) (ls : List ((ts : List Ty) × Cont ts)),
        VOk c ρ vs → JOk c J ls → ∀ m,
        LExpr.wp Γ Q X e ρ J m →
        wp Γ Q X (denote Val Cont tf vs ls) m
  | .let_ op bs k, c, tf, hflat, ρ, J, vs, ls, hv, hj, m, hsrc => by
    dsimp only [lExprToTFlat] at hflat
    cases hargs : toFlatArgs c op.sig op.args with
    | error err => simp [hargs, Bind.bind, Except.bind] at hflat
    | ok fargs =>
      cases hk : lExprToTFlat (c.pushVars bs) rs k with
      | error err =>
        simp [hargs, hk, Bind.bind, Except.bind] at hflat
      | ok tk =>
        simp only [hargs, hk, Bind.bind, Except.bind, Pure.pure,
          Except.pure, Except.ok.injEq] at hflat
        subst hflat
        rcases hsrc with ⟨hbs, xs, heval, hwp⟩
        obtain ⟨args', hda, hvals⟩ := toFlatArgs_sound hv hargs heval
        dsimp only [denote]; rw [hda]; dsimp only [wp, Op.wp]; rw [hvals]
        refine OpCode.wp_mono op.code xs (fun r hr => ?_) hwp
        exact lExprToTFlat_sound Γ Q X k (c.pushVars bs) tk hk
          (ρ.bind bs op.rs r) J (pushTup r vs) ls
          (VOk.pushVars bs op.rs r c ρ vs hbs hv) (hj.pushVars bs) m hr
  | .load t a b k, c, tf, hflat, ρ, J, vs, ls, hv, hj, m, hsrc => by
    dsimp only [lExprToTFlat] at hflat
    cases ha : toFlatArg c i64 a with
    | error err => simp [ha, Bind.bind, Except.bind] at hflat
    | ok fa =>
      cases hk : lExprToTFlat (c.pushVar b) rs k with
      | error err =>
        simp [ha, hk, Bind.bind, Except.bind] at hflat
      | ok tk =>
        simp only [ha, hk, Bind.bind, Except.bind, Pure.pure,
          Except.pure, Except.ok.injEq] at hflat
        subst hflat
        rcases hsrc with ⟨hbt, p, heval, v, hload, hwp⟩
        obtain ⟨a', hda, hva⟩ := toFlatArg_sound hv ha heval
        dsimp only [denote]; rw [hda]; dsimp only [wp]
        refine ⟨v, by rw [hva]; exact hload, ?_⟩
        exact lExprToTFlat_sound Γ Q X k (c.pushVar b) tk hk
          (ρ.set b.id t v) J (⟨t, v⟩ :: vs) ls (hv.pushVar b hbt v) (hj.pushVar b) m hwp
  | .store t v a k, c, tf, hflat, ρ, J, vs, ls, hv, hj, m, hsrc => by
    dsimp only [lExprToTFlat] at hflat
    cases hvarg : toFlatArg c t v with
    | error err => simp [hvarg, Bind.bind, Except.bind] at hflat
    | ok fv =>
      cases haarg : toFlatArg c i64 a with
      | error err => simp [hvarg, haarg, Bind.bind, Except.bind] at hflat
      | ok fa =>
        cases hk : lExprToTFlat c rs k with
        | error err =>
          simp [hvarg, haarg, hk, Bind.bind, Except.bind] at hflat
        | ok tk =>
          simp only [hvarg, haarg, hk, Bind.bind, Except.bind,
            Pure.pure, Except.pure, Except.ok.injEq] at hflat
          subst hflat
          rcases hsrc with ⟨x, p, hev, hea, hok, hwp⟩
          obtain ⟨v', hdv, hvv⟩ := toFlatArg_sound hv hvarg hev
          obtain ⟨a', hda, hva⟩ := toFlatArg_sound hv haarg hea
          dsimp only [denote]; rw [hdv, hda]; dsimp only [wp]
          refine ⟨by rw [hva]; exact hok, ?_⟩
          rw [hva, hvv]
          exact lExprToTFlat_sound Γ Q X k c tk hk ρ J vs ls hv hj (storeMem m t p x) hwp
  | .call f as bs args binders k, c, tf, hflat, ρ, J, vs, ls, hv, hj, m, hsrc => by
    dsimp only [lExprToTFlat] at hflat
    cases hargs : toFlatArgs c as args with
    | error err => simp [hargs, Bind.bind, Except.bind] at hflat
    | ok fargs =>
      cases hk : lExprToTFlat (c.pushVars binders) rs k with
      | error err =>
        simp [hargs, hk, Bind.bind, Except.bind] at hflat
      | ok tk =>
        simp only [hargs, hk, Bind.bind, Except.bind, Pure.pure,
          Except.pure, Except.ok.injEq] at hflat
        subst hflat
        rcases hsrc with ⟨hbs, xs, heval, P, E, hΓ, hP, hE⟩
        obtain ⟨args', hda, hvals⟩ := toFlatArgs_sound hv hargs heval
        dsimp only [denote]; rw [hda]; dsimp only [wp]; rw [hvals]
        refine ⟨P, E, hΓ, fun r m' hr => ?_, hE⟩
        exact lExprToTFlat_sound Γ Q X k (c.pushVars binders) tk hk
          (ρ.bind binders bs r) J (pushTup r vs) ls
          (VOk.pushVars binders bs r c ρ vs hbs hv) (hj.pushVars binders) m' (hP r m' hr)
  | .jnz cond t e, c, tf, hflat, ρ, J, vs, ls, hv, hj, m, hsrc => by
    dsimp only [lExprToTFlat] at hflat
    cases hc : toFlatArg c .bool cond with
    | error err => simp [hc, Bind.bind, Except.bind] at hflat
    | ok fc =>
      cases ht : lExprToTFlat c rs t with
      | error err => simp [hc, ht, Bind.bind, Except.bind] at hflat
      | ok tt =>
        cases he : lExprToTFlat c rs e with
        | error err =>
          simp [hc, ht, he, Bind.bind, Except.bind] at hflat
        | ok te =>
          simp only [hc, ht, he, Bind.bind, Except.bind, Pure.pure,
            Except.pure, Except.ok.injEq] at hflat
          subst hflat
          rcases hsrc with ⟨b, heval, htrue, hfalse⟩
          obtain ⟨c', hdc, hvc⟩ := toFlatArg_sound hv hc heval
          dsimp only [denote]; rw [hdc]; dsimp only [wp]; rw [hvc]
          exact ⟨fun hb => lExprToTFlat_sound Γ Q X t c tt ht ρ J vs ls hv hj m (htrue hb),
                 fun hb => lExprToTFlat_sound Γ Q X e c te he ρ J vs ls hv hj m (hfalse hb)⟩
  | .jump lid ts args, c, tf, hflat, ρ, J, vs, ls, hv, hj, m, hsrc => by
    dsimp only [lExprToTFlat] at hflat
    cases hlbl : c.lookupLbl lid ts with
    | error err => simp [hlbl, Bind.bind, Except.bind] at hflat
    | ok idx =>
      cases hargs : toFlatArgs c ts args with
      | error err =>
        simp [hlbl, hargs, Bind.bind, Except.bind] at hflat
      | ok fargs =>
        simp only [hlbl, hargs, Bind.bind, Except.bind, Pure.pure,
          Except.pure, Except.ok.injEq] at hflat
        subst hflat
        rcases hsrc with ⟨k, xs, hget, heval, hk⟩
        have hlu := lookupLbl_sound hj hlbl hget
        obtain ⟨args', hda, hvals⟩ := toFlatArgs_sound hv hargs heval
        dsimp only [denote]; rw [hlu, hda]; dsimp only [wp]; rw [hvals]; exact hk
  | .ret rs' args, c, tf, hflat, ρ, J, vs, ls, hv, _, m, hsrc => by
    rcases hsrc with ⟨rfl, xs, heval, hQ⟩
    dsimp only [lExprToTFlat] at hflat
    cases hargs : toFlatArgs c rs' args with
    | error err => simp [hargs, Bind.bind, Except.bind] at hflat
    | ok fargs =>
      simp only [hargs, ↓reduceDIte, Bind.bind, Except.bind, Pure.pure,
        Except.pure, Except.ok.injEq] at hflat
      subst hflat
      obtain ⟨args', hda, hvals⟩ := toFlatArgs_sound hv hargs heval
      dsimp only [denote]; rw [hda]; dsimp only [wp]; rw [hvals]; exact hQ
  | .exit f as args, c, tf, hflat, ρ, J, vs, ls, hv, _, m, hsrc => by
    dsimp only [lExprToTFlat] at hflat
    cases hargs : toFlatArgs c as args with
    | error err => simp [hargs, Bind.bind, Except.bind] at hflat
    | ok fargs =>
      simp only [hargs, Bind.bind, Except.bind, Pure.pure, Except.pure,
        Except.ok.injEq] at hflat
      subst hflat
      rcases hsrc with ⟨xs, heval, hX⟩
      obtain ⟨args', hda, hvals⟩ := toFlatArgs_sound hv hargs heval
      dsimp only [denote]; rw [hda]; dsimp only [wp]; rw [hvals]; exact hX
  | .hlt, c, tf, hflat, _, _, _, _, _, _, _, hsrc => False.elim hsrc
  | .group blocks k, c, tf, hflat, ρ, J, vs, ls, hv, hj, m, hsrc => by
    dsimp only [lExprToTFlat] at hflat
    let c' := blocks.foldl (fun acc (lid, ps, _) => acc.pushLbl lid (ps.map (·.ty))) c
    cases hblks : lBlocksToTBlocks c' rs blocks with
    | error err => simp [c', hblks, Bind.bind, Except.bind] at hflat
    | ok tbs =>
      cases hk : lExprToTFlat c' rs k with
      | error err =>
        simp [c', hblks, hk, Bind.bind, Except.bind] at hflat
      | ok tk =>
        simp only [c', hblks, hk, Bind.bind, Except.bind, Pure.pure,
          Except.pure, Except.ok.injEq] at hflat
        subst hflat
        dsimp only [denote, wp]
        intro Js hT
        have hv' : VOk c' ρ vs := hv.pushLbls blocks
        have hj' : JOk c' (J.bind (lBlockIds blocks) (lBlockSig blocks) Js) (pushTup Js ls) :=
          hj.pushLbls blocks Js
        have hcl : LExpr.closed Γ Q X blocks ρ
            (J.bind (lBlockIds blocks) (lBlockSig blocks) Js) Js :=
          lBlocksToTBlocks_sound Γ Q X blocks c' tbs hblks ρ
            (J.bind (lBlockIds blocks) (lBlockSig blocks) Js) vs (pushTup Js ls) hv' hj' Js hT
        exact lExprToTFlat_sound Γ Q X k c' tk hk ρ
          (J.bind (lBlockIds blocks) (lBlockSig blocks) Js) vs (pushTup Js ls) hv' hj' m
          (hsrc Js hcl)

/-- Soundness of `lBlocksToTBlocks` for a group's block list. -/
theorem lBlocksToTBlocks_sound (Γ : Env) {rs : List Ty} (Q : Post rs) (X : XPost) :
    ∀ (blks : List (Nat × List LVar × LExpr)) (c : LFlatCtx)
      (tbs : TBlocks rs (lBlockSig blks)),
      lBlocksToTBlocks c rs blks = .ok tbs →
      ∀ (ρ : VEnv) (J : JEnv) (vs : List ((t : Ty) × Val t)) (ls : List ((ts : List Ty) × Cont ts)),
        VOk c ρ vs → JOk c J ls →
        ∀ (Js : Tup Cont (lBlockSig blks)),
          Closed Γ Q X (denoteB Val Cont tbs vs ls) Js →
          LExpr.closed Γ Q X blks ρ J Js
  | [], _, .nil, _, _, _, _, _, _, _, _, _ => trivial
  | (lid, ps, b) :: rest, c, .cons tb tbs, htbs, ρ, J, vs, ls, hv, hj, (k, Js), hT => by
    dsimp only [lBlocksToTBlocks] at htbs
    cases hb : lExprToTFlat (c.pushVars ps) rs b with
    | error err => simp [hb, Bind.bind, Except.bind] at htbs
    | ok tb' =>
      cases hrest : lBlocksToTBlocks c rs rest with
      | error err =>
        simp [hb, hrest, Bind.bind, Except.bind] at htbs
      | ok tbs' =>
        simp only [hb, hrest, Bind.bind, Except.bind, Pure.pure,
          Except.pure, Except.ok.injEq] at htbs
        cases htbs
        dsimp only [denoteB, Closed] at hT
        dsimp only [LExpr.closed]
        refine ⟨fun xs m hwp => hT.1 xs m ?_, ?_⟩
        · exact lExprToTFlat_sound Γ Q X b (c.pushVars ps) tb hb
            (ρ.bind ps (ps.map (·.ty)) xs) J (pushTup xs vs) ls
            (VOk.pushVars ps (ps.map (·.ty)) xs c ρ vs rfl hv) (hj.pushVars ps) m hwp
        · exact lBlocksToTBlocks_sound Γ Q X rest c tbs hrest ρ J vs ls hv hj Js hT.2
end

/-- Closed-function soundness corollary for `denoteFunc`: `LExpr.wp` on parameter binders
implies `Func.wp` of the lowered `TFlat` function. -/
theorem lExprToTFlat_func_sound {ps : List LVar} {rs : List Ty} {body : LExpr} {tf : TFlat rs}
    (h : lExprToTFlat (({} : LFlatCtx).pushVars ps) rs body = .ok tf)
    (Γ : Env) (xs : Tup Val (ps.map (·.ty))) (m : Mem 64) (Q : Post rs) (X : XPost)
    (hwp : LExpr.wp Γ Q X body (VEnv.empty.bind ps (ps.map (·.ty)) xs) JEnv.empty m) :
    Func.wp Γ (denoteFunc (as := ps.map (·.ty)) tf) xs m Q X :=
  lExprToTFlat_sound Γ Q X body (({} : LFlatCtx).pushVars ps) tf h
    (VEnv.empty.bind ps (ps.map (·.ty)) xs) JEnv.empty (pushTup xs []) []
    (VOk.pushVars ps (ps.map (·.ty)) xs {} VEnv.empty [] rfl VOk.empty)
    (JOk.empty.pushVars ps) m hwp

/-- `TFlatFn.toFn` corollary for any `TFlatFn` built directly from `lExprToTFlat`. -/
theorem TFlatFn.wp_of_lExpr {nm : Sym} {ps : List LVar} {rs : List Ty} {body : LExpr}
    {tf : TFlat rs} (h : lExprToTFlat (({} : LFlatCtx).pushVars ps) rs body = .ok tf)
    (Γ : Env) (xs : Tup Val (ps.map (·.ty))) (m : Mem 64) (Q : Post rs) (X : XPost)
    (hwp : LExpr.wp Γ Q X body (VEnv.empty.bind ps (ps.map (·.ty)) xs) JEnv.empty m) :
    Func.wp Γ ({ name := nm, as := ps.map (·.ty), rs, flat := tf } : TFlatFn).toFn.body
      xs m Q X :=
  lExprToTFlat_func_sound h Γ xs m Q X hwp

end LeanQbe.T.Frontend.C0
