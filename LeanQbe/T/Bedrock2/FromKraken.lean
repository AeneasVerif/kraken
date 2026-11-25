module

public import LeanQbe.T.Bedrock2.FromKrakenCore

/-!
# Bidirectional `Kraken.Bedrock2.Exec ↔ LeanQbe.T.Func.wp` Agreement

Proves bidirectional `trCmd_wp_iff_exec` over all 10 `Kraken.Bedrock2.Cmd` constructors and
top-level `Func.fromKraken` soundness and equivalence theorems (`Func.fromKraken_wf`,
`Func.fromKraken_toFunc_wf`, `Func.fromKraken_wp_iff_exec`,
`Func.fromKraken_toFunc_wp_sound`, `Func.fromKraken_toFunc_wp_iff`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Bedrock2

open LeanQbe.T
open Kraken.Bedrock2 (AccessSize anybytes split)

/-! ## 6. Bidirectional `Cmd.wp ↔ Exec` Agreement (`BFlat.wp ↔ Kraken.Bedrock2.Exec`) -/

private theorem pushTup_len : {ts : List Ty} → (xs : Tup Val ts) →
    (vs : List ((t : Ty) × Val t)) →
    (pushTup xs vs).length = vs.length + ts.length
  | [], (), vs => rfl
  | _ :: ts, (x, xs), vs => by
      simp only [pushTup, List.length_cons, pushTup_len xs (⟨_, x⟩ :: vs)]
      omega

private theorem evalArgs_length {w : Nat} {m : Mem w} {l : Kraken.Bedrock2.Locals w} :
    {es : List Kraken.Bedrock2.Expr} → {vs : List (BitVec w)} →
    Kraken.Bedrock2.evalArgs m l es = some vs → vs.length = es.length
  | [], vs, h => by
      simp only [Kraken.Bedrock2.evalArgs, List.mapM_nil, Option.pure_def, Option.some.injEq] at h
      subst h; rfl
  | e :: es, vs, h => by
      simp only [Kraken.Bedrock2.evalArgs, List.mapM_cons, Option.bind_eq_bind,
        Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
      rcases h with ⟨v, _, rest, hrest, rfl⟩
      exact congrArg Nat.succ (evalArgs_length hrest)

private theorem whileLoopInvAux_spec (trBody : B2Ctx → Option CmdLowerRes) (deadLen : Nat) :
    ∀ (fuel : Nat) (inv0 inv : List String) (res : CmdLowerRes)
      (hsub : PLift (∀ x, x ∈ inv → x ∈ res.1)),
    inv0.length ≤ fuel →
    whileLoopInvAux trBody deadLen fuel inv0 = some ⟨inv, res, hsub⟩ →
    trBody (B2Ctx.bindMany inv (deadCtx deadLen)) = some res
  | 0, inv0, inv, res, hsub, hle, hw => by
      unfold whileLoopInvAux at hw
      cases htr : trBody (B2Ctx.bindMany inv0 (deadCtx deadLen)) with
      | none => simp [htr] at hw
      | some res' =>
          simp only [htr] at hw
          split at hw
          · next hlt =>
              have hle' := List.length_filter_le (· ∈ res'.1) inv0
              omega
          · simp only [Option.pure_def, Option.some.injEq] at hw
            rcases hw with ⟨rfl, rfl, _⟩
            exact htr
  | fuel + 1, inv0, inv, res, hsub, hle, hw => by
      unfold whileLoopInvAux at hw
      cases htr : trBody (B2Ctx.bindMany inv0 (deadCtx deadLen)) with
      | none => simp [htr] at hw
      | some res' =>
          simp only [htr] at hw
          split at hw
          next hlt =>
            have hle' : (inv0.filter (· ∈ res'.1)).length ≤ fuel := by omega
            exact whileLoopInvAux_spec trBody deadLen fuel (inv0.filter (· ∈ res'.1)) inv res
              hsub hle' hw
          next _ =>
            simp only [Option.pure_def, Option.some.injEq] at hw
            rcases hw with ⟨rfl, rfl, _⟩
            exact htr

private theorem whileLoopInv_spec (trBody : B2Ctx → Option CmdLowerRes) (deadLen : Nat)
    {inv0 inv : List String} {res : CmdLowerRes}
    (hsub : PLift (∀ x, x ∈ inv → x ∈ res.1))
    (hw : whileLoopInv trBody deadLen inv0 = some ⟨inv, res, hsub⟩) :
    trBody (B2Ctx.bindMany inv (deadCtx deadLen)) = some res :=
  whileLoopInvAux_spec trBody deadLen inv0.length inv0 inv res hsub (Nat.le_refl _) hw

private theorem exec_weaken {ext : Kraken.Bedrock2.ExtSpec 64} {e : Kraken.Bedrock2.Env} :
    {c : Kraken.Bedrock2.Cmd} → {B : Nat} → {t : Kraken.Bedrock2.Trace 64} →
    {m : Mem 64} → {l : Kraken.Bedrock2.Locals 64} →
    {P Q : Kraken.Bedrock2.Trace 64 → Mem 64 → Kraken.Bedrock2.Locals 64 → Prop} →
    Kraken.Bedrock2.Exec ext e B c t m l P →
    (∀ t' m' l', P t' m' l' → Q t' m' l') →
    Kraken.Bedrock2.Exec ext e B c t m l Q := by
  intro c B t m l P Q hex hPQ
  induction hex generalizing Q with
  | skip _ _ _ _ _ hp => exact .skip _ _ _ _ _ (hPQ _ _ _ hp)
  | set _ _ _ _ _ _ _ _ hev hp => exact .set _ _ _ _ _ _ _ _ hev (hPQ _ _ _ hp)
  | unset _ _ _ _ _ _ hp => exact .unset _ _ _ _ _ _ (hPQ _ _ _ hp)
  | store _ _ _ _ _ _ _ _ _ _ _ ha hv hs hp =>
      exact .store _ _ _ _ _ _ _ _ _ _ _ ha hv hs (hPQ _ _ _ hp)
  | stackalloc x n body B t mSmall l P hle hbody ih =>
      exact .stackalloc x n body B t mSmall l Q hle fun a mStack mComb hany hsp =>
        ih a mStack mComb hany hsp fun t' mComb' l' ⟨mSmall', mStack', ha', hs', hp⟩ =>
          ⟨mSmall', mStack', ha', hs', hPQ _ _ _ hp⟩
  | if_true _ _ _ _ _ _ _ _ _ hev hnz _ ih => exact .if_true _ _ _ _ _ _ _ _ _ hev hnz (ih hPQ)
  | if_false _ _ _ _ _ _ _ _ _ hev hz _ ih => exact .if_false _ _ _ _ _ _ _ _ _ hev hz (ih hPQ)
  | seq _ _ _ _ _ _ _ _ _ _ _ ih2 =>
      exact .seq _ _ _ _ _ _ _ _ (by assumption) fun t' m' l' hm => ih2 t' m' l' hm hPQ
  | while_false _ _ _ _ _ _ _ _ hev hz hp =>
      exact .while_false _ _ _ _ _ _ _ _ hev hz (hPQ _ _ _ hp)
  | while_true _ _ _ _ _ _ _ _ mid hev hnz _ _ _ ihw =>
      exact .while_true _ _ _ _ _ _ _ _ mid hev hnz (by assumption)
        fun t' m' l' hm => ihw t' m' l' hm hPQ
  | call _ _ _ _ _ _ _ _ f args lf mid hlk hargs hput _ hcont =>
      exact .call _ _ _ _ _ _ _ _ f args lf mid hlk hargs hput (by assumption)
        fun t' m' st1 hm =>
          let ⟨retvs, hget, l', hpl, hp⟩ := hcont t' m' st1 hm
          ⟨retvs, hget, l', hpl, hPQ _ _ _ hp⟩
  | interact _ _ _ _ _ _ _ _ _ mKeep mGive mid hsp hargs hext hcont =>
      exact .interact _ _ _ _ _ _ _ _ _ mKeep mGive mid hsp hargs hext
        fun mRec resvals hm =>
          let ⟨l', hpl, hp⟩ := hcont mRec resvals hm
          ⟨l', hpl, fun m' hsp' => hPQ _ _ _ (hp m' hsp')⟩

private theorem lookupV_skip1_i64 (h : (t : Ty) × Val t) (a : Val i64)
    (vs : List ((t' : Ty) × Val t')) :
    lookupV (h :: ⟨i64, a⟩ :: vs) i64 1 = some a :=
  lookupV_head_i64 a vs

private theorem lookupV_skip2_i64 (h1 h2 : (t : Ty) × Val t) (a : Val i64)
    (vs : List ((t' : Ty) × Val t')) :
    lookupV (h1 :: h2 :: ⟨i64, a⟩ :: vs) i64 2 = some a :=
  lookupV_head_i64 a vs

private theorem store_sub64_wp_to_exec {ext : Kraken.Bedrock2.ExtSpec 64}
    {e : Kraken.Bedrock2.Env} (sz : AccessSize) (ea ev : Kraken.Bedrock2.Expr)
    {ctx : B2Ctx} {res : CmdLowerRes} {bfA bfV : BFlat [i64]}
    {g : Tup (Arg K) (List.replicate ctx.liveVars.length i64)}
    (hg : gatherVars (none :: none :: none :: ctx) ctx.liveVars = some g)
    (hres : res = ⟨ctx.liveVars,
      .seq [i64] bfA (.seq [i64] bfV
        (.let_ ⟨.trunc 64 (8 * sz.bytes), (.var 0, ())⟩
          (.store (t := .bits (8 * sz.bytes)) (.var 0) (.var 2) (.ret g))))⟩)
    {B : Nat} {tb : TraceB} {t : Kraken.Bedrock2.Trace 64}
    {vs : List ((t : Ty) × Val t)} {m : Mem 64} {l : Kraken.Bedrock2.Locals 64}
    {Q : PostB (List.replicate res.1.length i64)}
    {post : Kraken.Bedrock2.Trace 64 → Mem 64 → Kraken.Bedrock2.Locals 64 → Prop}
    (htb : traceFromB? tb = some t) (hag : LocalsAgree ctx vs l)
    (ihA : ∀ (Q : PostB [i64]),
      (bfA.wp (extToB ext) (EnvB.ofKraken ext e) B Q vs tb m ↔
        ∃ v : BitVec 64, ea.eval m l = some v ∧ Q (v, ()) tb m))
    (ihV : ∀ (a : BitVec 64) (Q : PostB [i64]),
      (bfV.wp (extToB ext) (EnvB.ofKraken ext e) B Q (⟨i64, a⟩ :: vs) tb m ↔
        ∃ v : BitVec 64, ev.eval m l = some v ∧ Q (v, ()) tb m))
    (hQ : ∀ resTup t' tb' m' l', traceFromB? tb' = some t' →
      TupAgree res.1 resTup l' → Q resTup tb' m' → post t' m' l')
    (hwp : res.2.wp (extToB ext) (EnvB.ofKraken ext e) B Q vs tb m) :
    Kraken.Bedrock2.Exec ext e B (.store sz ea ev) t m l post := by
  subst hres
  dsimp only [BFlat.wp] at hwp
  rw [ihA] at hwp
  rcases hwp with ⟨a, ha, hseqV⟩
  dsimp only [pushTup] at hseqV
  rw [ihV a] at hseqV
  rcases hseqV with ⟨v, hv, htrc⟩
  dsimp only [pushTup] at htrc
  rw [denoteArgs_var1 (lookupV_head_i64 v _)] at htrc
  dsimp only [Op.wp, OpCode.wp, vals] at htrc
  rcases htrc with ⟨_, hst⟩
  rw [denoteArg_var (lookupV_head_bits _ _),
    denoteArg_var (lookupV_skip2_i64 _ _ a vs)] at hst
  rcases hst with ⟨hok, hret⟩
  dsimp only [Arg.val] at hok hret
  have hst? : Kraken.Bedrock2.store? sz m a v =
      some (storeMem m (accessTy sz) a (BitVec.setWidth (8 * sz.bytes) v)) :=
    (store?_iff_storeOk_storeMem sz m a v _).2 ⟨hok, rfl⟩
  obtain ⟨valArgs, hd, hta⟩ := gatherVars_denote
    (LocalsAgree_none (LocalsAgree_none (LocalsAgree_none hag i64 a) i64 v)
      (.bits (8 * sz.bytes)) (BitVec.setWidth (8 * sz.bytes) v)) hg
  rw [hd] at hret
  exact .store sz ea ev B t m l post a v _ ha hv hst?
    (hQ (vals valArgs) t tb _ l htb hta hret)

theorem trCmd_wp_to_exec {ext : Kraken.Bedrock2.ExtSpec 64} {e : Kraken.Bedrock2.Env} :
    (c : Kraken.Bedrock2.Cmd) → ∀ {ctx : B2Ctx} {res : CmdLowerRes},
    trCmd ctx c = some res →
    ∀ {B : Nat} {tb : TraceB} {t : Kraken.Bedrock2.Trace 64}
      {vs : List ((t : Ty) × Val t)} {m : Mem 64} {l : Kraken.Bedrock2.Locals 64}
      {Q : PostB (List.replicate res.1.length i64)}
      {post : Kraken.Bedrock2.Trace 64 → Mem 64 → Kraken.Bedrock2.Locals 64 → Prop},
    traceFromB? tb = some t →
    LocalsAgree ctx vs l →
    (∀ resTup t' tb' m' l', traceFromB? tb' = some t' →
      TupAgree res.1 resTup l' → Q resTup tb' m' → post t' m' l') →
    res.2.wp (extToB ext) (EnvB.ofKraken ext e) B Q vs tb m →
    Kraken.Bedrock2.Exec ext e B c t m l post
  | .skip, ctx, res, htr, B, tb, t, vs, m, l, Q, post, htb, hag, hQ, hwp => by
      simp only [trCmd, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at htr
      rcases htr with ⟨g, hg, rfl⟩
      dsimp only [BFlat.wp] at hwp
      obtain ⟨valArgs, hd, hta⟩ := gatherVars_denote hag hg
      rw [hd] at hwp
      exact .skip B t m l post (hQ (vals valArgs) t tb m l htb hta hwp)
  | .set x rhs, ctx, res, htr, B, tb, t, vs, m, l, Q, post, htb, hag, hQ, hwp => by
      simp only [trCmd, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at htr
      rcases htr with ⟨bfRhs, htrRhs, g, hg, rfl⟩
      dsimp only [BFlat.wp] at hwp
      rw [trExpr_wp_iff_eval rhs htrRhs hag] at hwp
      rcases hwp with ⟨v, hv, hret⟩
      obtain ⟨valArgs, hd, hta⟩ := gatherVars_denote (LocalsAgree_bind1 hag x v) hg
      dsimp only [pushTup] at hret
      rw [hd] at hret
      exact .set x rhs B t m l post v hv (hQ (vals valArgs) t tb m (l.insert x v) htb hta hret)
  | .unset x, ctx, res, htr, B, tb, t, vs, m, l, Q, post, htb, hag, hQ, hwp => by
      simp only [trCmd, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at htr
      rcases htr with ⟨g, hg, rfl⟩
      dsimp only [BFlat.wp] at hwp
      obtain ⟨valArgs, hd, hta⟩ := gatherVars_denote (LocalsAgree_shadow hag x) hg
      rw [hd] at hwp
      exact .unset x B t m l post (hQ (vals valArgs) t tb m (l.erase x) htb hta hwp)
  | .store sz ea ev, ctx, res, htr, B, tb, t, vs, m, l, Q, post, htb, hag, hQ, hwp => by
      simp only [trCmd, Option.bind_eq_bind, Option.bind_eq_some_iff] at htr
      rcases htr with ⟨bfA, htrA, bfV, htrV, hmatch⟩
      have ihA := trExpr_wp_iff_eval ea htrA (ext := extToB ext) (Γ := EnvB.ofKraken ext e)
        (B := B) (tb := tb) (m := m) (l := l) hag
      have ihV := fun a : BitVec 64 =>
        trExpr_wp_iff_eval ev htrV (ext := extToB ext) (Γ := EnvB.ofKraken ext e)
          (B := B) (tb := tb) (m := m) (l := l) (LocalsAgree_none hag i64 a)
      cases sz with
      | eight =>
          simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hmatch
          rcases hmatch with ⟨g, hg, rfl⟩
          dsimp only [BFlat.wp] at hwp
          rw [ihA] at hwp
          rcases hwp with ⟨a, ha, hseqV⟩
          dsimp only [pushTup] at hseqV
          rw [ihV a] at hseqV
          rcases hseqV with ⟨v, hv, hst⟩
          dsimp only [pushTup] at hst
          rw [denoteArg_var (lookupV_head_i64 v _),
            denoteArg_var (lookupV_skip1_i64 _ a vs)] at hst
          rcases hst with ⟨hok, hret⟩
          dsimp only [Arg.val] at hok hret
          have hst? : Kraken.Bedrock2.store? .eight m a v = some (storeMem m i64 a v) :=
            (store?_iff_storeOk_storeMem .eight m a v _).2 ⟨hok, rfl⟩
          obtain ⟨valArgs, hd, hta⟩ := gatherVars_denote
            (LocalsAgree_none (LocalsAgree_none hag i64 a) i64 v) hg
          rw [hd] at hret
          exact .store .eight ea ev B t m l post a v _ ha hv hst?
            (hQ (vals valArgs) t tb _ l htb hta hret)
      | one =>
          simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hmatch
          rcases hmatch with ⟨g, hg, hres⟩
          exact store_sub64_wp_to_exec .one ea ev hg hres.symm htb hag ihA ihV hQ hwp
      | two =>
          simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hmatch
          rcases hmatch with ⟨g, hg, hres⟩
          exact store_sub64_wp_to_exec .two ea ev hg hres.symm htb hag ihA ihV hQ hwp
      | four =>
          simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hmatch
          rcases hmatch with ⟨g, hg, hres⟩
          exact store_sub64_wp_to_exec .four ea ev hg hres.symm htb hag ihA ihV hQ hwp
  | .stackalloc x nbytes body, ctx, res, htr, B, tb, t, vs, mSmall, l, Q, post,
      htb, hag, hQ, hwp => by
      simp only [trCmd, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at htr
      rcases htr with ⟨⟨outB, bfB⟩, htrB, rfl⟩
      dsimp only [BFlat.wp] at hwp
      rcases hwp with ⟨hle, hbody⟩
      refine .stackalloc x nbytes body B t mSmall l post hle fun a mStack mComb hany hsp => ?_
      refine trCmd_wp_to_exec body htrB htb (LocalsAgree_bind1 hag x a) ?_
        (hbody a mStack mComb hany hsp)
      rintro resTup t' tb' mComb' l' htb' hta ⟨mSmall', mStack', ha', hs', hq⟩
      exact ⟨mSmall', mStack', ha', hs', hQ resTup t' tb' mSmall' l' htb' hta hq⟩
  | .seq c1 c2, ctx, res, htr, B, tb, t, vs, m, l, Q, post, htb, hag, hQ, hwp => by
      simp only [trCmd, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at htr
      rcases htr with ⟨⟨vars1, bf1⟩, htr1, ⟨vars2, bf2⟩, htr2, rfl⟩
      dsimp only [BFlat.wp] at hwp
      refine .seq c1 c2 B t m l post
        (fun t1 m1 l1 => Kraken.Bedrock2.Exec ext e B c2 t1 m1 l1 post) ?_ (fun _ _ _ h => h)
      refine trCmd_wp_to_exec c1 htr1 htb hag (fun res1 t1 tb1 m1 l1 htb1 hta1 hwp2 => ?_) hwp
      exact trCmd_wp_to_exec c2 htr2 htb1
        (LocalsAgree_bindMany_of_TupAgree (hag.1 ▸ LocalsAgree_dead l1) res1 hta1) hQ hwp2
  | .cond ec c1 c2, ctx, res, htr, B, tb, t, vs, m, l, Q, post, htb, hag, hQ, hwp => by
      simp only [trCmd, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at htr
      rcases htr with ⟨bfC, htrC, ⟨vars1, bf1⟩, htr1, ⟨vars2, bf2⟩, htr2,
        g1, hg1, g2, hg2, rfl⟩
      dsimp only [BFlat.wp] at hwp
      rw [trExpr_wp_iff_eval ec htrC hag] at hwp
      rcases hwp with ⟨vc, hvc, hlet⟩
      dsimp only [pushTup] at hlet
      rw [denoteArgs_var_imm i64 0#64 (lookupV_head_i64 vc vs)] at hlet
      dsimp only [Op.wp, OpCode.wp, vals, Arg.val, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte,
        liftCmp, CmpOp.evalBits, Ty.mask, pushTup] at hlet
      rw [denoteArg_var (lookupV_head_bool _ _)] at hlet
      rcases hlet with ⟨ht, hf⟩
      have hagBr : LocalsAgree (none :: none :: ctx)
          (⟨Ty.bool, decide (vc ≠ 0#64)⟩ :: ⟨i64, vc⟩ :: vs) l :=
        LocalsAgree_none (LocalsAgree_none hag i64 vc) .bool (decide (vc ≠ 0#64))
      have hlenBr := hagBr.1
      by_cases hcz : vc = 0#64
      · refine .if_false B t m l ec c1 c2 post vc hvc hcz ?_
        have hwp2 := hf (by simp [hcz])
        refine trCmd_wp_to_exec c2 htr2 htb hagBr (fun res2 t2 tb2 m2 l2 htb2 hta2 hret2 => ?_)
          hwp2
        obtain ⟨valArgs, hd, htaOut⟩ := gatherVars_denote
          (LocalsAgree_bindMany_of_TupAgree (hlenBr ▸ LocalsAgree_dead l2) res2 hta2) hg2
        rw [hd] at hret2
        exact hQ (vals valArgs) t2 tb2 m2 l2 htb2 htaOut hret2
      · refine .if_true B t m l ec c1 c2 post vc hvc hcz ?_
        have hwp1 := ht (decide_eq_true hcz)
        refine trCmd_wp_to_exec c1 htr1 htb hagBr (fun res1 t1 tb1 m1 l1 htb1 hta1 hret1 => ?_)
          hwp1
        obtain ⟨valArgs, hd, htaOut⟩ := gatherVars_denote
          (LocalsAgree_bindMany_of_TupAgree (hlenBr ▸ LocalsAgree_dead l1) res1 hta1) hg1
        rw [hd] at hret1
        exact hQ (vals valArgs) t1 tb1 m1 l1 htb1 htaOut hret1
  | .while ec body, ctx, res, htr, B, tb, t, vs, m, l, Q, post, htb, hag, hQ, hwp => by
      simp only [trCmd, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at htr
      rcases htr with
        ⟨w, hWhileInv, init, hInit, bfEc, htrEc, gBody, hgBody, gExit, hgExit, rfl⟩
      rcases w with ⟨inv, ⟨varsBody, bfBodyRaw⟩, hsub⟩
      have htrBody : trCmd (B2Ctx.bindMany inv (deadCtx ctx.length)) body =
          some ⟨varsBody, bfBodyRaw⟩ :=
        whileLoopInv_spec (fun c => trCmd c body) ctx.length hsub hWhileInv
      dsimp only [BFlat.wp] at hwp
      obtain ⟨valInit, hdInit, htaInit⟩ := gatherVars_denote hag hInit
      rw [hdInit] at hwp
      let I : Tup Val (List.replicate inv.length i64) → TraceB → Mem 64 → Prop :=
        fun s tb' m' => ∀ t' l', traceFromB? tb' = some t' → TupAgree inv s l' →
          Kraken.Bedrock2.Exec ext e B (Kraken.Bedrock2.Cmd.while ec body) t' m' l' post
      have hInv : ∀ s tb' m',
          BFlat.wp (extToB ext) (EnvB.ofKraken ext e) (rs := [.bool]) B
            (fun (b, ()) tb1 m1 =>
              (b = true → BFlat.wp (extToB ext) (EnvB.ofKraken ext e) B I
                (.seq (List.replicate varsBody.length i64) bfBodyRaw (.ret gBody))
                (pushTup s vs) tb1 m1) ∧
              (b = false → BFlat.wp (extToB ext) (EnvB.ofKraken ext e) B Q
                (.ret gExit) (pushTup s vs) tb1 m1))
            (.seq [i64] bfEc (.let_ ⟨.cmp .ne i64, (.var 0, .imm 0#64, ())⟩ (.ret (.var 0, ()))))
            (pushTup s vs) tb' m' →
          I s tb' m' := by
        intro s tb' m' htest t' l' htb' htaS
        have hagLoop : LocalsAgree (B2Ctx.bindMany inv (deadCtx ctx.length))
            (pushTup s vs) l' :=
          LocalsAgree_bindMany_of_TupAgree (hag.1 ▸ LocalsAgree_dead l') s htaS
        have hlenLoop := hagLoop.1
        dsimp only [BFlat.wp] at htest
        rw [trExpr_wp_iff_eval ec htrEc hagLoop] at htest
        rcases htest with ⟨vc, hvc, hlet⟩
        dsimp only [pushTup] at hlet
        rw [denoteArgs_var_imm i64 0#64 (lookupV_head_i64 vc _)] at hlet
        dsimp only [Op.wp, OpCode.wp, vals, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte,
          liftCmp, CmpOp.evalBits, Ty.mask, pushTup] at hlet
        rw [denoteArgs_var1 (lookupV_head_bool _ _)] at hlet
        rcases hlet with ⟨hT, hF⟩
        by_cases hcz : vc = 0#64
        · refine .while_false ec body B t' m' l' post vc hvc hcz ?_
          have hk := hF (by simp [hcz])
          obtain ⟨valExit, hdExit, htaExit⟩ := gatherVars_denote hagLoop hgExit
          rw [hdExit] at hk
          exact hQ (vals valExit) t' tb' m' l' htb' htaExit hk
        · have hb := hT (decide_eq_true hcz)
          refine .while_true ec body B t' m' l' post vc
            (fun t1 m1 l1 => Kraken.Bedrock2.Exec ext e B (.while ec body) t1 m1 l1 post)
            hvc hcz ?_ (fun _ _ _ h => h)
          refine trCmd_wp_to_exec body htrBody htb' hagLoop ?_ hb
          intro resBody t1 tb1 m1 l1 htb1 htaBody hretBody
          obtain ⟨valBody, hdBody, htaInv⟩ := gatherVars_denote
            (LocalsAgree_bindMany_of_TupAgree (hlenLoop ▸ LocalsAgree_dead l1) resBody htaBody)
            hgBody
          rw [hdBody] at hretBody
          exact hretBody t1 l1 htb1 htaInv
      exact hwp I hInv t l htb htaInit
  | .call binds fname arges, ctx, res, htr, B, tb, t, vs, m, l, Q, post,
      htb, hag, hQ, hwp => by
      simp only [trCmd, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at htr
      rcases htr with ⟨bfArgs, htrArgs, g, hg, rfl⟩
      dsimp only [BFlat.wp] at hwp
      rw [trArgs_wp_iff_evalArgs arges htrArgs hag] at hwp
      rcases hwp with ⟨argVals, hargs, argTup, hargTup, hcall⟩
      obtain ⟨valArgs, hdRev, hvRev⟩ := revVars_denote vs argTup
      rw [hdRev] at hcall
      dsimp only at hcall
      rw [hvRev] at hcall
      rcases hcall with ⟨P, hEnv, hCont⟩
      rcases hEnv with ⟨f, t0, argList, lf, mid, hlk, htb0, hExtArgs, hput, hexec, hPost⟩
      rw [htb, Option.some.injEq] at htb0
      subst htb0
      rw [extTupToList?_replicate, Option.some.injEq] at hExtArgs
      subst hExtArgs
      rw [hargTup] at hput
      refine .call binds fname arges B t m l post f argVals lf mid hlk hargs hput hexec ?_
      intro t' m' st1 hm
      obtain ⟨retvs, resTup, hget, hExtRet, hP⟩ := hPost t' m' st1 hm
      rw [extTupToList?_replicate, Option.some.injEq] at hExtRet
      have hlen : binds.length = retvs.length := by
        rw [← hExtRet, tupToList_length]
      refine ⟨retvs, hget, l.insertMany (binds.zip retvs), putManyZip_of_length_eq hlen, ?_⟩
      have hret := hCont resTup (traceToB t') m' hP
      have hagDead : LocalsAgree (deadCtx (ctx.length + arges.length)) (pushTup argTup vs) l := by
        have hdl : (pushTup argTup vs).length = ctx.length + arges.length := by
          rw [pushTup_len, List.length_replicate, hag.1]
        exact hdl ▸ LocalsAgree_dead l
      have hagAfter := hExtRet ▸ LocalsAgree_bindMany_insertMany hagDead resTup
      obtain ⟨outArgs, hdOut, htaOut⟩ := gatherVars_denote hagAfter hg
      rw [hdOut] at hret
      exact hQ (vals outArgs) t' (traceToB t') m' (l.insertMany (binds.zip retvs))
        (traceFromB?_traceToB t') htaOut hret
  | .interact binds action arges, ctx, res, htr, B, tb, t, vs, m, l, Q, post,
      htb, hag, hQ, hwp => by
      simp only [trCmd, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at htr
      rcases htr with ⟨bfArgs, htrArgs, g, hg, rfl⟩
      dsimp only [BFlat.wp] at hwp
      rw [trArgs_wp_iff_evalArgs arges htrArgs hag] at hwp
      rcases hwp with ⟨argVals, hargs, argTup, hargTup, hio⟩
      obtain ⟨valArgs, hdRev, hvRev⟩ := revVars_denote vs argTup
      rw [hdRev] at hio
      dsimp only at hio
      rw [hvRev] at hio
      rcases hio with ⟨mKeep, mGive, midB, hsp, hexB, hCont⟩
      rcases hexB with ⟨t0, argList, mid, htb0, hExtArgs, hex, hConv⟩
      rw [htb, Option.some.injEq] at htb0
      subst htb0
      rw [extTupToList?_replicate, Option.some.injEq] at hExtArgs
      subst hExtArgs
      rw [hargTup] at hex
      refine .interact binds action arges argVals B t m l post mKeep mGive mid hsp hargs hex ?_
      intro mRec resvals hm
      obtain ⟨resTup, hExtRet, hMidB⟩ := hConv mRec resvals hm
      rw [extTupToList?_replicate, Option.some.injEq] at hExtRet
      have hlen : binds.length = resvals.length := by
        rw [← hExtRet, tupToList_length]
      refine ⟨l.insertMany (binds.zip resvals), putManyZip_of_length_eq hlen, fun m' hsp' => ?_⟩
      have hret := hCont mRec resTup hMidB m' hsp'
      have hagDead : LocalsAgree (deadCtx (ctx.length + arges.length)) (pushTup argTup vs) l := by
        have hdl : (pushTup argTup vs).length = ctx.length + arges.length := by
          rw [pushTup_len, List.length_replicate, hag.1]
        exact hdl ▸ LocalsAgree_dead l
      have hagAfter := hExtRet ▸ LocalsAgree_bindMany_insertMany hagDead resTup
      obtain ⟨outArgs, hdOut, htaOut⟩ := gatherVars_denote hagAfter hg
      rw [hdOut] at hret
      have htb' : traceFromB?
          (⟨List.replicate arges.length i64, List.replicate binds.length i64,
            mGive, action, argTup, mRec, resTup⟩ :: tb) =
          some (((mGive, action, argVals), mRec, resvals) :: t) := by
        rw [traceFromB?_cons, logItemFromB?_mk, htb, hargTup, hExtRet]
        rfl
      exact hQ (vals outArgs) _ _ m' (l.insertMany (binds.zip resvals)) htb' htaOut hret

private theorem store_sub64_exec_to_wp {ext : Kraken.Bedrock2.ExtSpec 64}
    {e : Kraken.Bedrock2.Env} (sz : AccessSize) (ea ev : Kraken.Bedrock2.Expr)
    {ctx : B2Ctx} {res : CmdLowerRes} {bfA bfV : BFlat [i64]}
    {g : Tup (Arg K) (List.replicate ctx.liveVars.length i64)}
    (hg : gatherVars (none :: none :: none :: ctx) ctx.liveVars = some g)
    (hres : res = ⟨ctx.liveVars,
      .seq [i64] bfA (.seq [i64] bfV
        (.let_ ⟨.trunc 64 (8 * sz.bytes), (.var 0, ())⟩
          (.store (t := .bits (8 * sz.bytes)) (.var 0) (.var 2) (.ret g))))⟩)
    {B : Nat} {tb : TraceB} {t : Kraken.Bedrock2.Trace 64}
    {vs : List ((ty : Ty) × Val ty)} {m m' : Mem 64} {l : Kraken.Bedrock2.Locals 64}
    {a v : BitVec 64}
    {Q : PostB (List.replicate res.1.length i64)}
    {post : Kraken.Bedrock2.Trace 64 → Mem 64 → Kraken.Bedrock2.Locals 64 → Prop}
    (htb : traceFromB? tb = some t) (hag : LocalsAgree ctx vs l)
    (ha : ea.eval m l = some a) (hv : ev.eval m l = some v)
    (hst : Kraken.Bedrock2.store? sz m a v = some m') (hp : post t m' l)
    (ihA : ∀ (Q : PostB [i64]),
      (bfA.wp (extToB ext) (EnvB.ofKraken ext e) B Q vs tb m ↔
        ∃ v : BitVec 64, ea.eval m l = some v ∧ Q (v, ()) tb m))
    (ihV : ∀ (Q : PostB [i64]),
      (bfV.wp (extToB ext) (EnvB.ofKraken ext e) B Q (⟨i64, a⟩ :: vs) tb m ↔
        ∃ v : BitVec 64, ev.eval m l = some v ∧ Q (v, ()) tb m))
    (hQ : ∀ t' tb' m' l' resTup, traceFromB? tb' = some t' →
      TupAgree res.1 resTup l' → post t' m' l' → Q resTup tb' m') :
    res.2.wp (extToB ext) (EnvB.ofKraken ext e) B Q vs tb m := by
  subst hres
  have ⟨hok, hm'⟩ := (store?_iff_storeOk_storeMem sz m a v m').1 hst
  subst hm'
  dsimp only [BFlat.wp]
  rw [ihA]
  refine ⟨a, ha, ?_⟩
  dsimp only [pushTup]
  rw [ihV]
  refine ⟨v, hv, ?_⟩
  dsimp only [pushTup]
  rw [denoteArgs_var1 (lookupV_head_i64 v _)]
  dsimp only [Op.wp, OpCode.wp, vals]
  refine ⟨by cases sz <;> decide, ?_⟩
  rw [denoteArg_var (lookupV_head_bits _ _),
    denoteArg_var (lookupV_skip2_i64 _ _ a vs)]
  refine ⟨hok, ?_⟩
  obtain ⟨valArgs, hd, hta⟩ := gatherVars_denote
    (LocalsAgree_none (LocalsAgree_none (LocalsAgree_none hag i64 a) i64 v)
      (.bits (8 * sz.bytes)) (BitVec.setWidth (8 * sz.bytes) v)) hg
  dsimp only [Arg.val]
  rw [hd]
  exact hQ t tb _ l (vals valArgs) htb hta hp

theorem trCmd_exec_to_wp {ext : Kraken.Bedrock2.ExtSpec 64} {e : Kraken.Bedrock2.Env} :
    (c : Kraken.Bedrock2.Cmd) → ∀ {ctx : B2Ctx} {res : CmdLowerRes},
    trCmd ctx c = some res →
    ∀ {B : Nat} {tb : TraceB} {t : Kraken.Bedrock2.Trace 64}
      {vs : List ((ty : Ty) × Val ty)} {m : Mem 64} {l : Kraken.Bedrock2.Locals 64}
      {Q : PostB (List.replicate res.1.length i64)}
      {post : Kraken.Bedrock2.Trace 64 → Mem 64 → Kraken.Bedrock2.Locals 64 → Prop},
    traceFromB? tb = some t →
    LocalsAgree ctx vs l →
    (∀ t' tb' m' l' resTup, traceFromB? tb' = some t' →
      TupAgree res.1 resTup l' → post t' m' l' → Q resTup tb' m') →
    Kraken.Bedrock2.Exec ext e B c t m l post →
    res.2.wp (extToB ext) (EnvB.ofKraken ext e) B Q vs tb m
  | .skip, ctx, res, htr, B, tb, t, vs, m, l, Q, post, htb, hag, hQ, hex => by
      cases hex with
      | skip _ _ _ _ _ hp =>
          simp only [trCmd, Option.bind_eq_bind, Option.bind_eq_some_iff,
            Option.pure_def, Option.some.injEq] at htr
          rcases htr with ⟨g, hg, rfl⟩
          dsimp only [BFlat.wp]
          obtain ⟨valArgs, hd, hta⟩ := gatherVars_denote hag hg
          rw [hd]
          exact hQ t tb m l (vals valArgs) htb hta hp
  | .set x rhs, ctx, res, htr, B, tb, t, vs, m, l, Q, post, htb, hag, hQ, hex => by
      cases hex with
      | set _ _ _ _ _ _ _ v hv hp =>
          simp only [trCmd, Option.bind_eq_bind, Option.bind_eq_some_iff,
            Option.pure_def, Option.some.injEq] at htr
          rcases htr with ⟨bfRhs, htrRhs, g, hg, rfl⟩
          dsimp only [BFlat.wp]
          rw [trExpr_wp_iff_eval rhs htrRhs hag]
          refine ⟨v, hv, ?_⟩
          obtain ⟨valArgs, hd, hta⟩ := gatherVars_denote (LocalsAgree_bind1 hag x v) hg
          dsimp only [pushTup]
          rw [hd]
          exact hQ t tb m (l.insert x v) (vals valArgs) htb hta hp
  | .unset x, ctx, res, htr, B, tb, t, vs, m, l, Q, post, htb, hag, hQ, hex => by
      cases hex with
      | unset _ _ _ _ _ _ hp =>
          simp only [trCmd, Option.bind_eq_bind, Option.bind_eq_some_iff,
            Option.pure_def, Option.some.injEq] at htr
          rcases htr with ⟨g, hg, rfl⟩
          dsimp only [BFlat.wp]
          obtain ⟨valArgs, hd, hta⟩ := gatherVars_denote (LocalsAgree_shadow hag x) hg
          rw [hd]
          exact hQ t tb m (l.erase x) (vals valArgs) htb hta hp
  | .store sz ea ev, ctx, res, htr, B, tb, t, vs, m, l, Q, post, htb, hag, hQ, hex => by
      cases hex with
      | store _ _ _ _ _ _ _ _ a v m' ha hv hst hp =>
          simp only [trCmd, Option.bind_eq_bind, Option.bind_eq_some_iff] at htr
          rcases htr with ⟨bfA, htrA, bfV, htrV, hmatch⟩
          have ihA := trExpr_wp_iff_eval ea htrA (ext := extToB ext) (Γ := EnvB.ofKraken ext e)
            (B := B) (tb := tb) (m := m) (l := l) hag
          have ihV := trExpr_wp_iff_eval ev htrV (ext := extToB ext) (Γ := EnvB.ofKraken ext e)
            (B := B) (tb := tb) (m := m) (l := l) (LocalsAgree_none hag i64 a)
          cases sz with
          | eight =>
              have ⟨hok, hm'⟩ := (store?_iff_storeOk_storeMem .eight m a v m').1 hst
              subst hm'
              simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hmatch
              rcases hmatch with ⟨g, hg, rfl⟩
              dsimp only [BFlat.wp]
              rw [ihA]
              refine ⟨a, ha, ?_⟩
              dsimp only [pushTup]
              rw [ihV]
              refine ⟨v, hv, ?_⟩
              dsimp only [pushTup]
              rw [denoteArg_var (lookupV_head_i64 v _),
                denoteArg_var (lookupV_skip1_i64 _ a vs)]
              refine ⟨hok, ?_⟩
              obtain ⟨valArgs, hd, hta⟩ := gatherVars_denote
                (LocalsAgree_none (LocalsAgree_none hag i64 a) i64 v) hg
              rw [hd]
              exact hQ t tb _ l (vals valArgs) htb hta hp
          | one =>
              simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hmatch
              rcases hmatch with ⟨g, hg, hres⟩
              exact store_sub64_exec_to_wp .one ea ev hg hres.symm htb hag ha hv hst hp
                ihA ihV hQ
          | two =>
              simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hmatch
              rcases hmatch with ⟨g, hg, hres⟩
              exact store_sub64_exec_to_wp .two ea ev hg hres.symm htb hag ha hv hst hp
                ihA ihV hQ
          | four =>
              simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hmatch
              rcases hmatch with ⟨g, hg, hres⟩
              exact store_sub64_exec_to_wp .four ea ev hg hres.symm htb hag ha hv hst hp
                ihA ihV hQ
  | .stackalloc x nbytes body, ctx, res, htr, B, tb, t, vs, mSmall, l, Q, post,
      htb, hag, hQ, hex => by
      cases hex with
      | stackalloc _ _ _ _ _ _ _ _ hle hbody =>
          simp only [trCmd, Option.bind_eq_bind, Option.bind_eq_some_iff,
            Option.pure_def, Option.some.injEq] at htr
          rcases htr with ⟨⟨outB, bfB⟩, htrB, rfl⟩
          refine ⟨hle, fun a mStack mComb hany hsp => ?_⟩
          refine trCmd_exec_to_wp body htrB htb (LocalsAgree_bind1 hag x a) ?_
            (hbody a mStack mComb hany hsp)
          rintro t' tb' mComb' l' resTup htb' hta ⟨mSmall', mStack', ha', hs', hp⟩
          exact ⟨mSmall', mStack', ha', hs', hQ t' tb' mSmall' l' resTup htb' hta hp⟩
  | .seq c1 c2, ctx, res, htr, B, tb, t, vs, m, l, Q, post, htb, hag, hQ, hex => by
      cases hex with
      | seq _ _ _ _ _ _ _ mid hex1 hex2 =>
          simp only [trCmd, Option.bind_eq_bind, Option.bind_eq_some_iff,
            Option.pure_def, Option.some.injEq] at htr
          rcases htr with ⟨⟨vars1, bf1⟩, htr1, ⟨vars2, bf2⟩, htr2, rfl⟩
          dsimp only [BFlat.wp]
          refine trCmd_exec_to_wp c1 htr1 htb hag (fun t1 tb1 m1 l1 res1 htb1 hta1 hm1 => ?_) hex1
          exact trCmd_exec_to_wp c2 htr2 htb1
            (LocalsAgree_bindMany_of_TupAgree (hag.1 ▸ LocalsAgree_dead l1) res1 hta1)
            hQ (hex2 t1 m1 l1 hm1)
  | .cond ec c1 c2, ctx, res, htr, B, tb, t, vs, m, l, Q, post, htb, hag, hQ, hex => by
      simp only [trCmd, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at htr
      rcases htr with ⟨bfC, htrC, ⟨vars1, bf1⟩, htr1, ⟨vars2, bf2⟩, htr2,
        g1, hg1, g2, hg2, rfl⟩
      cases hex with
      | if_true _ _ _ _ _ _ _ _ vc hvc hnz hex1 =>
          dsimp only [BFlat.wp]
          rw [trExpr_wp_iff_eval ec htrC hag]
          refine ⟨vc, hvc, ?_⟩
          have hagBr : LocalsAgree (none :: none :: ctx)
              (⟨Ty.bool, decide (vc ≠ 0#64)⟩ :: ⟨i64, vc⟩ :: vs) l :=
            LocalsAgree_none (LocalsAgree_none hag i64 vc) .bool (decide (vc ≠ 0#64))
          have hlenBr := hagBr.1
          dsimp only [pushTup]
          rw [denoteArgs_var_imm i64 0#64 (lookupV_head_i64 vc vs)]
          dsimp only [Op.wp, OpCode.wp, vals, Arg.val, Ty.hasFloat, Bool.false_eq_true,
            ↓reduceIte, liftCmp, CmpOp.evalBits, Ty.mask, pushTup]
          rw [denoteArg_var (lookupV_head_bool _ _)]
          refine ⟨fun _ => ?_,
            fun hdec => absurd (Classical.not_not.mp (of_decide_eq_false hdec)) hnz⟩
          refine trCmd_exec_to_wp c1 htr1 htb hagBr ?_ hex1
          intro t1 tb1 m1 l1 res1 htb1 hta1 hp1
          obtain ⟨valArgs, hd, htaOut⟩ := gatherVars_denote
            (LocalsAgree_bindMany_of_TupAgree (hlenBr ▸ LocalsAgree_dead l1) res1 hta1) hg1
          rw [hd]
          exact hQ t1 tb1 m1 l1 (vals valArgs) htb1 htaOut hp1
      | if_false _ _ _ _ _ _ _ _ vc hvc hcz hex2 =>
          dsimp only [BFlat.wp]
          rw [trExpr_wp_iff_eval ec htrC hag]
          refine ⟨vc, hvc, ?_⟩
          have hagBr : LocalsAgree (none :: none :: ctx)
              (⟨Ty.bool, decide (vc ≠ 0#64)⟩ :: ⟨i64, vc⟩ :: vs) l :=
            LocalsAgree_none (LocalsAgree_none hag i64 vc) .bool (decide (vc ≠ 0#64))
          have hlenBr := hagBr.1
          dsimp only [pushTup]
          rw [denoteArgs_var_imm i64 0#64 (lookupV_head_i64 vc vs)]
          dsimp only [Op.wp, OpCode.wp, vals, Arg.val, Ty.hasFloat, Bool.false_eq_true,
            ↓reduceIte, liftCmp, CmpOp.evalBits, Ty.mask, pushTup]
          rw [denoteArg_var (lookupV_head_bool _ _)]
          refine ⟨fun hdec => absurd hcz (of_decide_eq_true hdec), fun _ => ?_⟩
          refine trCmd_exec_to_wp c2 htr2 htb hagBr ?_ hex2
          intro t2 tb2 m2 l2 res2 htb2 hta2 hp2
          obtain ⟨valArgs, hd, htaOut⟩ := gatherVars_denote
            (LocalsAgree_bindMany_of_TupAgree (hlenBr ▸ LocalsAgree_dead l2) res2 hta2) hg2
          rw [hd]
          exact hQ t2 tb2 m2 l2 (vals valArgs) htb2 htaOut hp2
  | .while ec body, ctx, res, htr, B, tb, t, vs, m, l, Q, post, htb, hag, hQ, hex => by
      simp only [trCmd, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at htr
      rcases htr with
        ⟨w, hWhileInv, init, hInit, bfEc, htrEc, gBody, hgBody, gExit, hgExit, rfl⟩
      rcases w with ⟨inv, ⟨varsBody, bfBodyRaw⟩, hsub⟩
      have htrBody : trCmd (B2Ctx.bindMany inv (deadCtx ctx.length)) body =
          some ⟨varsBody, bfBodyRaw⟩ :=
        whileLoopInv_spec (fun c => trCmd c body) ctx.length hsub hWhileInv
      dsimp only [BFlat.wp]
      obtain ⟨valInit, hdInit, htaInit⟩ := gatherVars_denote hag hInit
      rw [hdInit]
      intro I hClosed
      suffices hInd : ∀ {c' : Kraken.Bedrock2.Cmd} {t' : Kraken.Bedrock2.Trace 64}
          {m' : Mem 64} {l' : Kraken.Bedrock2.Locals 64}
          {post' : Kraken.Bedrock2.Trace 64 → Mem 64 → Kraken.Bedrock2.Locals 64 → Prop},
          Kraken.Bedrock2.Exec ext e B c' t' m' l' post' →
          c' = .while ec body →
          (∀ t2 tb2 m2 l2 res2, traceFromB? tb2 = some t2 → TupAgree inv res2 l2 →
            post' t2 m2 l2 → Q res2 tb2 m2) →
          ∀ tb' s', traceFromB? tb' = some t' → TupAgree inv s' l' → I s' tb' m' from
        hInd hex rfl hQ tb (vals valInit) htb htaInit
      intro c' t' m' l' post' hexw
      induction hexw with
      | while_false =>
          rename_i t₁ m₁ l₁ post₁ vc hvc hcz hp
          rintro ⟨⟩ hQw tb' s' htb' htaS
          have hagLoop : LocalsAgree (B2Ctx.bindMany inv (deadCtx ctx.length))
              (pushTup s' vs) l₁ :=
            LocalsAgree_bindMany_of_TupAgree (hag.1 ▸ LocalsAgree_dead l₁) s' htaS
          refine hClosed s' tb' m₁ ?_
          rw [trExpr_wp_iff_eval ec htrEc hagLoop]
          refine ⟨vc, hvc, ?_⟩
          dsimp only [pushTup]
          rw [denoteArgs_var_imm i64 0#64 (lookupV_head_i64 vc _)]
          dsimp only [Op.wp, OpCode.wp, vals, Arg.val, Ty.hasFloat, Bool.false_eq_true,
            ↓reduceIte, liftCmp, CmpOp.evalBits, Ty.mask, pushTup]
          rw [denoteArgs_var1 (lookupV_head_bool _ _)]
          refine ⟨fun hdec => absurd hcz (of_decide_eq_true hdec), fun _ => ?_⟩
          obtain ⟨valExit, hdExit, htaExit⟩ := gatherVars_denote hagLoop hgExit
          rw [hdExit]
          exact hQw t₁ tb' m₁ l₁ (vals valExit) htb' htaExit hp
      | while_true =>
          rename_i t₁ m₁ l₁ post₁ vc mid hvc hnz hexB _ _ ihW
          rintro ⟨⟩ hQw tb' s' htb' htaS
          have hagLoop : LocalsAgree (B2Ctx.bindMany inv (deadCtx ctx.length))
              (pushTup s' vs) l₁ :=
            LocalsAgree_bindMany_of_TupAgree (hag.1 ▸ LocalsAgree_dead l₁) s' htaS
          have hlenLoop := hagLoop.1
          refine hClosed s' tb' m₁ ?_
          rw [trExpr_wp_iff_eval ec htrEc hagLoop]
          refine ⟨vc, hvc, ?_⟩
          dsimp only [pushTup]
          rw [denoteArgs_var_imm i64 0#64 (lookupV_head_i64 vc _)]
          dsimp only [Op.wp, OpCode.wp, vals, Arg.val, Ty.hasFloat, Bool.false_eq_true,
            ↓reduceIte, liftCmp, CmpOp.evalBits, Ty.mask, pushTup]
          rw [denoteArgs_var1 (lookupV_head_bool _ _)]
          refine ⟨fun _ => ?_,
            fun hdec => absurd (Classical.not_not.mp (of_decide_eq_false hdec)) hnz⟩
          refine trCmd_exec_to_wp body htrBody htb' hagLoop ?_ hexB
          intro t2 tb2 m2 l2 resBody htb2 htaBody hm2
          obtain ⟨valBody, hdBody, htaInv⟩ := gatherVars_denote
            (LocalsAgree_bindMany_of_TupAgree (hlenLoop ▸ LocalsAgree_dead l2) resBody htaBody)
            hgBody
          rw [hdBody]
          exact ihW t2 m2 l2 hm2 hex hClosed rfl hQw tb2 (vals valBody) htb2 htaInv
      | _ => intro h; cases h
  | .call binds fname arges, ctx, res, htr, B, tb, t, vs, m, l, Q, post,
      htb, hag, hQ, hex => by
      cases hex with
      | call _ _ _ _ _ _ _ _ f argVals lf mid hlk hargs hput hexec hcont =>
          simp only [trCmd, Option.bind_eq_bind, Option.bind_eq_some_iff,
            Option.pure_def, Option.some.injEq] at htr
          rcases htr with ⟨bfArgs, htrArgs, g, hg, rfl⟩
          dsimp only [BFlat.wp]
          rw [trArgs_wp_iff_evalArgs arges htrArgs hag]
          obtain ⟨argTup, hargTup⟩ := exists_listToTup?_of_length (evalArgs_length hargs)
          have hargList := tupToList_listToTup? hargTup
          refine ⟨argVals, hargs, argTup, hargList, ?_⟩
          obtain ⟨valArgs, hdRev, hvRev⟩ := revVars_denote vs argTup
          rw [hdRev]
          dsimp only
          rw [hvRev]
          let P : PostB (List.replicate binds.length i64) :=
            fun resTup tb' m' => ∃ t' st1 retvs, tb' = traceToB t' ∧ mid t' m' st1 ∧
              Kraken.Bedrock2.getMany st1 f.rets = some retvs ∧ tupToList resTup = retvs
          refine ⟨P, ?_, ?_⟩
          · refine ⟨f, t, argVals, lf, mid, hlk, htb, by simp [hargList], hput, hexec, ?_⟩
            intro t' m' st1 hm
            obtain ⟨retvs, hget, l', hputBinds, _⟩ := hcont t' m' st1 hm
            have hlen : retvs.length = binds.length := by
              simp only [Kraken.Bedrock2.putManyZip] at hputBinds
              split at hputBinds
              next heql => exact heql.symm
              next => contradiction
            obtain ⟨resTup, hresTup⟩ := exists_listToTup?_of_length hlen
            have hretEq := tupToList_listToTup? hresTup
            exact ⟨retvs, resTup, hget, by simp [hretEq], t', st1, retvs, rfl, hm, hget, hretEq⟩
          · rintro resTup tb' m' ⟨t', st1, retvs, rfl, hm, hget, hretEq⟩
            obtain ⟨retvs', hget', l', hputBinds, hp⟩ := hcont t' m' st1 hm
            rw [hget] at hget'; cases hget'
            have hlen : binds.length = retvs.length := by
              rw [← hretEq, tupToList_length]
            rw [putManyZip_of_length_eq hlen, Option.some.injEq] at hputBinds
            subst hputBinds
            have hagDead :
                LocalsAgree (deadCtx (ctx.length + arges.length)) (pushTup argTup vs) l := by
              have hdl : (pushTup argTup vs).length = ctx.length + arges.length := by
                rw [pushTup_len, List.length_replicate, hag.1]
              exact hdl ▸ LocalsAgree_dead l
            have hagAfter := hretEq ▸ LocalsAgree_bindMany_insertMany hagDead resTup
            obtain ⟨outArgs, hdOut, htaOut⟩ := gatherVars_denote hagAfter hg
            rw [hdOut]
            exact hQ t' (traceToB t') m' (l.insertMany (binds.zip retvs)) (vals outArgs)
              (traceFromB?_traceToB t') htaOut hp
  | .interact binds action arges, ctx, res, htr, B, tb, t, vs, m, l, Q, post,
      htb, hag, hQ, hex => by
      cases hex with
      | interact _ _ _ argVals _ _ _ _ _ mKeep mGive mid hsp hargs hext hcont =>
          simp only [trCmd, Option.bind_eq_bind, Option.bind_eq_some_iff,
            Option.pure_def, Option.some.injEq] at htr
          rcases htr with ⟨bfArgs, htrArgs, g, hg, rfl⟩
          dsimp only [BFlat.wp]
          rw [trArgs_wp_iff_evalArgs arges htrArgs hag]
          obtain ⟨argTup, hargTup⟩ := exists_listToTup?_of_length (evalArgs_length hargs)
          have hargList := tupToList_listToTup? hargTup
          refine ⟨argVals, hargs, argTup, hargList, ?_⟩
          obtain ⟨valArgs, hdRev, hvRev⟩ := revVars_denote vs argTup
          rw [hdRev]
          dsimp only
          rw [hvRev]
          refine ⟨mKeep, mGive, fun mRec resTup => mid mRec (tupToList resTup), hsp, ?_, ?_⟩
          · refine ⟨t, argVals, mid, htb, by simp [hargList], hext, fun mRec resvals hm => ?_⟩
            obtain ⟨l', hputBinds, _⟩ := hcont mRec resvals hm
            have hlen : resvals.length = binds.length := by
              simp only [Kraken.Bedrock2.putManyZip] at hputBinds
              split at hputBinds
              next heql => exact heql.symm
              next => contradiction
            obtain ⟨resTup, hresTup⟩ := exists_listToTup?_of_length hlen
            have hretEq := tupToList_listToTup? hresTup
            exact ⟨resTup, by simp [hretEq], by dsimp only; rw [hretEq]; exact hm⟩
          · intro mRec resTup hm m' hsp'
            obtain ⟨l', hputBinds, hp⟩ := hcont mRec (tupToList resTup) hm
            have hlen : binds.length = (tupToList resTup).length := (tupToList_length resTup).symm
            rw [putManyZip_of_length_eq hlen, Option.some.injEq] at hputBinds
            subst hputBinds
            have hagDead :
                LocalsAgree (deadCtx (ctx.length + arges.length)) (pushTup argTup vs) l := by
              have hdl : (pushTup argTup vs).length = ctx.length + arges.length := by
                rw [pushTup_len, List.length_replicate, hag.1]
              exact hdl ▸ LocalsAgree_dead l
            have hagAfter := LocalsAgree_bindMany_insertMany hagDead resTup
            obtain ⟨outArgs, hdOut, htaOut⟩ := gatherVars_denote hagAfter hg
            rw [hdOut]
            have htb' : traceFromB?
                (⟨List.replicate arges.length i64, List.replicate binds.length i64,
                  mGive, action, argTup, mRec, resTup⟩ :: tb) =
                some (((mGive, action, argVals), mRec, tupToList resTup) :: t) := by
              rw [traceFromB?_cons, logItemFromB?_mk, htb, hargList]
              rfl
            exact hQ _ _ m' _ (vals outArgs) htb' htaOut (hp m' hsp')

theorem trCmd_wp_iff_exec {ext : Kraken.Bedrock2.ExtSpec 64} {e : Kraken.Bedrock2.Env}
    {c : Kraken.Bedrock2.Cmd} {ctx : B2Ctx} {res : CmdLowerRes}
    (htr : trCmd ctx c = some res)
    {B : Nat} {tb : TraceB} {t : Kraken.Bedrock2.Trace 64}
    {vs : List ((ty : Ty) × Val ty)} {m : Mem 64} {l : Kraken.Bedrock2.Locals 64}
    {Q : PostB (List.replicate res.1.length i64)}
    {post : Kraken.Bedrock2.Trace 64 → Mem 64 → Kraken.Bedrock2.Locals 64 → Prop}
    (htb : traceFromB? tb = some t)
    (hag : LocalsAgree ctx vs l)
    (hiff : ∀ resTup t' tb' m' l', traceFromB? tb' = some t' →
      TupAgree res.1 resTup l' → (Q resTup tb' m' ↔ post t' m' l')) :
    res.2.wp (extToB ext) (EnvB.ofKraken ext e) B Q vs tb m ↔
      Kraken.Bedrock2.Exec ext e B c t m l post :=
  ⟨trCmd_wp_to_exec c htr htb hag (fun resTup t' tb' m' l' htb' hta hq =>
      (hiff resTup t' tb' m' l' htb' hta).1 hq),
    trCmd_exec_to_wp c htr htb hag (fun t' tb' m' l' resTup htb' hta hp =>
      (hiff resTup t' tb' m' l' htb' hta).2 hp)⟩

/-! ## 7. Top-Level `Func.fromKraken` Soundness, Well-Formedness, and `ToFunc` Agreement -/

theorem Func.fromKraken_wf {f : Kraken.Bedrock2.Func}
    {fb : FuncB (List.replicate f.params.length i64) (List.replicate f.rets.length i64)}
    (h : Func.fromKraken f = some fb) : FuncB.Wf fb := by
  simp only [Func.fromKraken, Option.map_eq_some_iff] at h
  rcases h with ⟨bf, _, rfl⟩
  exact FuncB.wf_of_denote bf rfl

theorem Func.fromKraken_toFunc_wf {f : Kraken.Bedrock2.Func}
    {fb : FuncB (List.replicate f.params.length i64) (List.replicate f.rets.length i64)}
    (h : Func.fromKraken f = some fb) (cfg : LowerCfg := {}) :
    (fb.toFunc cfg).Wf :=
  FuncB.toFunc_wf (Func.fromKraken_wf h) cfg

theorem Func.fromKraken_wp_iff_exec {ext : Kraken.Bedrock2.ExtSpec 64}
    {e : Kraken.Bedrock2.Env} {f : Kraken.Bedrock2.Func}
    {fb : FuncB (List.replicate f.params.length i64) (List.replicate f.rets.length i64)}
    (htr : Func.fromKraken f = some fb)
    {B : Nat} {xs : Tup Val (List.replicate f.params.length i64)}
    {tb : TraceB} {t : Kraken.Bedrock2.Trace 64} {m : Mem 64}
    {Q : PostB (List.replicate f.rets.length i64)}
    {post : Kraken.Bedrock2.Trace 64 → Mem 64 → List (BitVec 64) → Prop}
    (htb : traceFromB? tb = some t)
    (hQ : ∀ resTup tb' t' m', traceFromB? tb' = some t' →
      (Q resTup tb' m' ↔ post t' m' (tupToList resTup))) :
    FuncB.wp (extToB ext) (EnvB.ofKraken ext e) fb B xs tb m Q ↔
      Kraken.Bedrock2.Exec ext e B f.body t m
        ((∅ : Kraken.Bedrock2.Locals 64).insertMany (f.params.zip (tupToList xs)))
        fun t' m' l' =>
          ∃ retvs, Kraken.Bedrock2.getMany l' f.rets = some retvs ∧ post t' m' retvs := by
  simp only [Func.fromKraken, Option.map_eq_some_iff, Func.toBFlat?,
    Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at htr
  rcases htr with ⟨bf, ⟨⟨outVars, bfBody⟩, htrBody, gRet, hgRet, rfl⟩, rfl⟩
  dsimp only [FuncB.wp, denoteFuncB]
  rw [← BFlat.wp_iff_denote_wp]
  dsimp only [BFlat.wp]
  have hag0 : LocalsAgree (B2Ctx.bindMany f.params []) (pushTup xs [])
      ((∅ : Kraken.Bedrock2.Locals 64).insertMany (f.params.zip (tupToList xs))) :=
    LocalsAgree_bindMany_insertMany ⟨rfl, fun _ _ h => by simp [listGet?] at h⟩ xs
  refine trCmd_wp_iff_exec htrBody htb hag0 ?_
  intro resTup t' tb' m' l' htb' hta
  have hagExit : LocalsAgree
      (B2Ctx.bindMany outVars (deadCtx (B2Ctx.bindMany f.params []).length))
      (pushTup resTup (pushTup xs [])) l' :=
    LocalsAgree_bindMany_of_TupAgree (hag0.1 ▸ LocalsAgree_dead l') resTup hta
  obtain ⟨retArgs, hdRet, htaRet⟩ := gatherVars_denote hagExit hgRet
  rw [hdRet]
  constructor
  · intro hq
    exact ⟨tupToList (vals retArgs), getMany_of_TupAgree (vals retArgs) htaRet,
      (hQ (vals retArgs) tb' t' m' htb').1 hq⟩
  · rintro ⟨retvs, hget, hp⟩
    have hget' := getMany_of_TupAgree (vals retArgs) htaRet
    rw [hget'] at hget
    cases hget
    exact (hQ (vals retArgs) tb' t' m' htb').2 hp

/-- End-to-end soundness from `Kraken.Bedrock2.Exec` all the way to `LeanQbe.T.Func.wp` on
`fb.toFunc cfg` (covering `stackalloc`, `interact`, `while`, `inlinetable`, etc.). -/
theorem Func.fromKraken_toFunc_wp_sound {ext : Kraken.Bedrock2.ExtSpec 64}
    {e : Kraken.Bedrock2.Env} {f : Kraken.Bedrock2.Func}
    {fb : FuncB (List.replicate f.params.length i64) (List.replicate f.rets.length i64)}
    (htr : Func.fromKraken f = some fb)
    {B : Nat} (hB : B < 2 ^ 64)
    {xs : Tup Val (List.replicate f.params.length i64)}
    {t : Kraken.Bedrock2.Trace 64} {m : Mem 64}
    {Q' : Post (List.replicate f.rets.length i64)} (X : XPost)
    {post : Kraken.Bedrock2.Trace 64 → Mem 64 → List (BitVec 64) → Prop}
    (hQ : ∀ resTup t' m', post t' m' (tupToList resTup) → Q' resTup m')
    (hex : Kraken.Bedrock2.Exec ext e B f.body t m
      ((∅ : Kraken.Bedrock2.Locals 64).insertMany (f.params.zip (tupToList xs)))
      fun t' m' l' =>
        ∃ retvs, Kraken.Bedrock2.getMany l' f.rets = some retvs ∧ post t' m' retvs)
    (cfg : LowerCfg := {}) :
    LeanQbe.T.Func.wp (Env.ofBedrock2Sound cfg (extToB ext) (EnvB.ofKraken ext e))
      (fb.toFunc cfg) xs m Q' X := by
  have hfb := (Func.fromKraken_wp_iff_exec htr (traceFromB?_traceToB t)
    (Q := fun resTup _ m' => Q' resTup m')
    (post := fun _ m' retvs => ∀ resTup, tupToList resTup = retvs → Q' resTup m')
    (fun resTup _ _ _ _ => ⟨fun h _ hEq => by cases tupToList_inj hEq; exact h,
      fun h => h resTup rfl⟩)).2
      (exec_weaken hex fun t' m' l' ⟨retvs, hget, hp⟩ =>
        ⟨retvs, hget, fun resTup hEq => hQ resTup t' m' (by rw [hEq]; exact hp)⟩)
  exact FuncB.toFunc_wp_sound (Q := fun resTup _ m' => Q' resTup m')
    hB xs (traceToB t) m X (fun _ _ _ h => h) hfb cfg

private theorem Cmd.wp_congr_env {ext1 ext2 : ExtSpecB} {Γ1 Γ2 : EnvB} {B1 B2 : Nat}
    (hΓ : ∀ sym as bs args t m P,
      Γ1 sym as bs B1 args t m P ↔ Γ2 sym as bs B2 args t m P) :
    {rs : List Ty} → (c : Cmd Val rs) → c.NoStackNoIO →
    ∀ Q t m, Cmd.wp ext1 Γ1 B1 Q c t m ↔ Cmd.wp ext2 Γ2 B2 Q c t m
  | _, .ret _, _, _, _, _ => Iff.rfl
  | _, .let_ _ k, h, Q, t, m => by
      cases h with | let_ hk =>
        exact ⟨Op.wp_mono fun r hr => (Cmd.wp_congr_env hΓ (k r) (hk r) Q t m).1 hr,
          Op.wp_mono fun r hr => (Cmd.wp_congr_env hΓ (k r) (hk r) Q t m).2 hr⟩
  | _, .load _ _ k, h, Q, t, m => by
      cases h with | load hk =>
        exact exists_congr fun v => and_congr_right fun _ =>
          Cmd.wp_congr_env hΓ (k v) (hk v) Q t m
  | _, .store _ _ k, h, Q, t, m => by
      cases h with | store hk =>
        exact and_congr_right fun _ => Cmd.wp_congr_env hΓ k hk Q t _
  | _, .call f args k, h, Q, t, m => by
      cases h with | call hk =>
        exact exists_congr fun P => and_congr (hΓ _ _ _ _ _ _ _)
          (forall₃_congr fun r t' m' => imp_congr_right fun _ =>
            Cmd.wp_congr_env hΓ (k r) (hk r) Q t' m')
  | _, .seq c1 c2, h, Q, t, m => by
      cases h with | seq h1 h2 =>
        dsimp only [Cmd.wp]
        rw [Cmd.wp_congr_env hΓ c1 h1 _ t m]
        exact ⟨Cmd.wp_mono (fun mid t' m' hm =>
            (Cmd.wp_congr_env hΓ (c2 mid) (h2 mid) Q t' m').1 hm) _ t m,
          Cmd.wp_mono (fun mid t' m' hm =>
            (Cmd.wp_congr_env hΓ (c2 mid) (h2 mid) Q t' m').2 hm) _ t m⟩
  | _, .cond _ tBr eBr, h, Q, t, m => by
      cases h with | cond ht he =>
        exact and_congr
          (imp_congr_right fun _ => Cmd.wp_congr_env hΓ tBr ht Q t m)
          (imp_congr_right fun _ => Cmd.wp_congr_env hΓ eBr he Q t m)
  | _, .while_ _ test body k, h, Q, t, m => by
      cases h with | while_ ht hb hk =>
        dsimp only [Cmd.wp]
        refine forall_congr' fun I => imp_congr_left <|
          forall₃_congr fun s t' m' => imp_congr_left ?_
        rw [Cmd.wp_congr_env hΓ (test s) (ht s) _ t' m']
        exact ⟨Cmd.wp_mono (fun (b, ()) t1 m1 ⟨h1, h2⟩ =>
            ⟨fun h => (Cmd.wp_congr_env hΓ (body s) (hb s) I t1 m1).1 (h1 h),
             fun h => (Cmd.wp_congr_env hΓ (k s) (hk s) Q t1 m1).1 (h2 h)⟩) _ t' m',
          Cmd.wp_mono (fun (b, ()) t1 m1 ⟨h1, h2⟩ =>
            ⟨fun h => (Cmd.wp_congr_env hΓ (body s) (hb s) I t1 m1).2 (h1 h),
             fun h => (Cmd.wp_congr_env hΓ (k s) (hk s) Q t1 m1).2 (h2 h)⟩) _ t' m'⟩
  | _, .hlt, _, _, _, _ => Iff.rfl

/-- Exact `↔` equivalence between `LeanQbe.T.Func.wp` and `Kraken.Bedrock2.Exec` for any
pure (`noStackNoIO = true`) `Kraken.Bedrock2` function when `EnvB.ofTEnv Γ X` agrees with
`EnvB.ofKraken ext e` (in particular, vacuously when the function makes no calls or `e`
matches `Γ`). -/
theorem Func.fromKraken_toFunc_wp_iff {ext : Kraken.Bedrock2.ExtSpec 64}
    {e : Kraken.Bedrock2.Env} {Γ : Env} {X : XPost} {f : Kraken.Bedrock2.Func}
    {bf : BFlat (List.replicate f.rets.length i64)}
    (htr : Func.toBFlat? f = some bf) (hnio : bf.noStackNoIO = true)
    (hEnv : ∀ sym as bs B args tb m P,
      EnvB.ofTEnv Γ X sym as bs B args tb m P ↔
        EnvB.ofKraken ext e sym as bs B args tb m P)
    {xs : Tup Val (List.replicate f.params.length i64)} {m : Mem 64}
    {Q : Post (List.replicate f.rets.length i64)}
    (cfg : LowerCfg := {}) :
    LeanQbe.T.Func.wp Γ
      ((denoteFuncB (as := List.replicate f.params.length i64) bf).toFunc cfg) xs m Q X ↔
      Kraken.Bedrock2.Exec ext e 0 f.body [] m
        ((∅ : Kraken.Bedrock2.Locals 64).insertMany (f.params.zip (tupToList xs)))
        fun _ m' l' =>
          ∃ retvs, Kraken.Bedrock2.getMany l' f.rets = some retvs ∧
            ∃ resTup, tupToList resTup = retvs ∧ Q resTup m' := by
  have hfb : Func.fromKraken f =
      some (denoteFuncB (as := List.replicate f.params.length i64) bf) := by
    simp [Func.fromKraken, htr]
  have hns : ∀ ys : Tup Val (List.replicate f.params.length i64),
      ((denoteFuncB (as := List.replicate f.params.length i64) bf) Val ys).NoStackNoIO :=
    fun ys => BFlat.noStackNoIO_denote bf hnio (pushTup ys [])
  rw [FuncB.toFunc_wp_iff (Γ := Γ) hns xs m Q X cfg]
  dsimp only [FuncB.wpPure, Cmd.wpPure]
  have hEx : (∃ B, Cmd.wp extEmpty (EnvB.ofTEnv Γ X) B (fun vs _ m' => Q vs m')
        (denoteFuncB (as := List.replicate f.params.length i64) bf Val xs) [] m) ↔
      Cmd.wp extEmpty (EnvB.ofTEnv Γ X) 0 (fun vs _ m' => Q vs m')
        (denoteFuncB (as := List.replicate f.params.length i64) bf Val xs) [] m :=
    ⟨fun ⟨B, h⟩ => (Cmd.wp_congr_env (ext1 := extEmpty) (ext2 := extEmpty) (B1 := B) (B2 := 0)
        (fun _ _ _ _ _ _ _ => Iff.rfl) _ (hns xs) _ [] m).1 h,
      fun h => ⟨0, h⟩⟩
  rw [hEx]
  rw [Cmd.wp_congr_env (ext1 := extEmpty) (ext2 := extToB ext) (B1 := 0) (B2 := 0)
    (fun sym as bs args t' m' P => hEnv sym as bs 0 args t' m' P) _ (hns xs) _ [] m]
  exact Func.fromKraken_wp_iff_exec hfb (traceFromB?_nil)
    (Q := fun resTup _ m' => Q resTup m')
    (post := fun _ m' retvs => ∃ resTup, tupToList resTup = retvs ∧ Q resTup m')
    (fun resTup _ _ m' _ =>
      ⟨fun hq => ⟨resTup, rfl, hq⟩,
       fun ⟨resTup', hEq, hq⟩ => by cases tupToList_inj hEq; exact hq⟩)

end LeanQbe.T.Bedrock2
