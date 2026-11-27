module

public import LeanQbe.T.LeanLCNF.Sem.LowerSound2d
import LeanQbe.T.Logic.MemLemmas

/-!
# Argument, Memory-Read, and Primitive Return-Width Helpers (`LowerSound3a`)

Companion to `LowerSound3.lean` containing:
1. `HSimInv` transfer across `VEnvAgreeBelow` / `JEnvAgreeBelow` (`hSimInv_agreeBelow`)
2. `LCtx.var`, `argAt`, `argOwn`, and `List.mapM` lowering correspondence lemmas
3. Heap-focus field and scalar object read helpers (`mem_load_lcnfObj_{field,scalar}`)
4. `HPrim.wp` return-width refinement (`hPrim_wp_retTy`)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.LeanLCNF.Sem

open LeanQbe.T
open LeanQbe.T.LeanLCNF
open LeanQbe.T.Frontend.C0
open Std.ExtHashMap

/-! ## 1. Context, `AgreeBelow`, and Argument-Lowering Helpers -/

theorem hSimInv_agreeBelow {Δ : HEnv} {rt : BitVec 64} {R : Mem 64 → Prop} {c : LCtx}
    {n nk : Nat} {QH : HPost} {XH : HXPost} {QT : Post [c.retTy.toTTy]} {XT : XPost}
    {JH : HJEnv} {ρH : HValEnv} {ρL ρ' : Frontend.C0.VEnv} {JL J' : JEnv}
    (hsim : HSimInv Δ rt R c n QH XH QT XT JH ρH ρL JL)
    (hnk : n ≤ nk) (hρ : VEnvAgreeBelow n ρ' ρL) (hJ : JEnvAgreeBelow n J' JL) :
    HSimInv Δ rt R c nk QH XH QT XT JH ρH ρ' J' where
  idsOk := ctxIdsBelow_mono hnk hsim.idsOk
  rtOk := (hρ c.rt i64 hsim.idsOk.1).trans hsim.rtOk
  varRel := fun x ty w hx => by
    obtain ⟨a, h, hlu, hev⟩ := hsim.varRel x ty w hx
    exact ⟨a, h, hlu, (hρ a ty.toTTy (ctxIdsBelow_lookup_var hsim.idsOk hlu)).trans hev⟩
  jpRel := fun j lbl ts hj => by
    obtain ⟨k, hk, hspec⟩ := hsim.jpRel j lbl ts hj
    exact ⟨k, (hJ lbl (ts.map LcTy.toTTy) (ctxIdsBelow_lookup_jp hsim.idsOk hj)).trans hk, hspec⟩
  loopRel := fun lbl hlbl => by
    obtain ⟨k, hk, hspec⟩ := hsim.loopRel lbl hlbl
    exact ⟨k, (hJ lbl (c.params.map LcTy.toTTy) (hsim.idsOk.2.2.2 lbl hlbl)).trans hk, hspec⟩
  postRel := hsim.postRel
  xpostRel := hsim.xpostRel

theorem eval_cast_ty {ρ : Frontend.C0.VEnv} {t₁ t₂ : Ty} (h : t₁ = t₂)
    {a : LArg} {v : Val t₁} (hev : LArg.eval ρ t₁ a = some v) :
    LArg.eval ρ t₂ a = some (h ▸ v) := by
  cases h; exact hev

theorem eqRec_trans {α : Type _} {P : α → Type _} {a b c : α}
    (h1 : a = b) (h2 : b = c) (v : P a) : h2 ▸ h1 ▸ v = (h1.trans h2) ▸ v := by
  subst h1; subst h2; rfl

theorem ctxVar_run_ok {c : LCtx} {x n n' : Nat} {p : LArg × LcTy}
    (h : (c.var x).run n = .ok (p, n')) :
    c.vars.lookup x = some p ∧ n' = n := by
  unfold LCtx.var at h
  cases hlu : c.vars.lookup x with
  | none => rw [hlu] at h; cases h
  | some q =>
    simp only [hlu, lm_pure_run, Except.ok.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    exact ⟨rfl, rfl⟩

theorem ctxVar_run_of_lookup {c : LCtx} {x n : Nat} {p : LArg × LcTy}
    (h : c.vars.lookup x = some p) :
    (c.var x).run n = .ok (p, n) := by
  simp only [LCtx.var, h]; rfl

theorem width_eq_64_of_not_isScalar {t : LcTy} (h : (!t.isScalar) = true) :
    t.width = 64 := by
  cases t <;> simp [LcTy.isScalar, LcTy.width] at h ⊢

theorem toTTy_bytes_eq (t : LcTy) : (t.width + 7) / 8 = t.toTTy.bytes := by
  cases t <;> rfl

theorem argBitsWidth_of_eval {ρ : Frontend.C0.VEnv} {rw : Nat} {la : LArg} {vr : BitVec rw}
    (h : LArg.eval ρ (.bits rw) la = some vr) :
    argBitsWidth la = rw := by
  cases la with
  | var _ t' =>
    dsimp only [LArg.eval] at h
    split at h
    · next heq => subst heq; rfl
    · cases h
  | imm t' _ =>
    dsimp only [LArg.eval] at h
    split at h
    · next heq => subst heq; rfl
    · cases h

theorem argAt_argIdsBelow {c : LCtx} {a : LcArg} {t : LcTy} {n n' : Nat} {la : LArg}
    (hc : ctxIdsBelow c n) (h : (argAt c a t).run n = .ok (la, n')) :
    n' = n ∧ argIdsBelow la n := by
  cases a with
  | erased =>
    simp only [argAt, lm_pure_run, Except.ok.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    exact ⟨rfl, argIdsBelow_imm _ _ _⟩
  | var x =>
    simp only [argAt, lm_bind_run] at h
    rcases h with ⟨⟨v, vt⟩, n1, hv, hrest⟩
    obtain ⟨hlu, rfl⟩ := ctxVar_run_ok hv
    dsimp only at hrest
    by_cases hw : (vt.width == t.width) = true
    · rw [ite_eq_left hw, lm_pure_run] at hrest
      injection hrest with hp
      have hla : v = la := congrArg Prod.fst hp
      have hn : n1 = n' := congrArg Prod.snd hp
      subst hla; subst hn
      exact ⟨rfl, ctxIdsBelow_lookup_var hc hlu⟩
    · rw [ite_eq_right hw] at hrest; cases hrest

theorem argOwn_argIdsBelow {c : LCtx} {a : LcArg} {n n' : Nat} {la : LArg}
    (hc : ctxIdsBelow c n) (h : (argOwn c a).run n = .ok (la, n')) :
    n' = n ∧ argIdsBelow la n := by
  cases a with
  | erased =>
    simp only [argOwn, lm_pure_run, Except.ok.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    exact ⟨rfl, argIdsBelow_imm _ _ _⟩
  | var x =>
    simp only [argOwn, lm_bind_run] at h
    rcases h with ⟨⟨v, vt⟩, n1, hv, hrest⟩
    obtain ⟨hlu, rfl⟩ := ctxVar_run_ok hv
    dsimp only at hrest
    rw [lm_pure_run] at hrest
    injection hrest with hp
    have hla : v = la := congrArg Prod.fst hp
    have hn : n1 = n' := congrArg Prod.snd hp
    subst hla; subst hn
    exact ⟨rfl, ctxIdsBelow_lookup_var hc hlu⟩

private theorem erased_arg_eval_of_not_isScalar (ρL : Frontend.C0.VEnv) {t : LcTy}
    (h : (!t.isScalar) = true) :
    ∃ hty : i64 = t.toTTy,
      LArg.eval ρL t.toTTy (imm t.width (if t.isScalar = true then 0 else 1)) =
        some (hty ▸ 1#64) := by
  cases t <;> simp [LcTy.isScalar] at h
  all_goals exact ⟨rfl, LArg.eval_imm_self ρL i64 1#64⟩

theorem argAt_eval_of_evalArgOwn {c : LCtx} {ρH : HValEnv} {ρL : Frontend.C0.VEnv}
    {a : LcArg} {t : LcTy} {w : Word} {n n' : Nat} {la : LArg}
    (hc : ctxIdsBelow c n) (hrel : VarRel c ρH ρL)
    (hw : ρH.evalArgOwn a = some w) (her : a = .erased → (!t.isScalar) = true)
    (hrun : (argAt c a t).run n = .ok (la, n')) :
    ∃ h : w.1 = t.toTTy, n' = n ∧ argIdsBelow la n ∧
      LArg.eval ρL t.toTTy la = some (h ▸ w.2) := by
  obtain ⟨hn, hId⟩ := argAt_argIdsBelow hc hrun
  subst hn
  cases a with
  | erased =>
    have hns := her rfl
    simp only [HValEnv.evalArgOwn, Option.some.injEq] at hw
    subst hw
    simp only [argAt, lm_pure_run, Except.ok.injEq, Prod.mk.injEq] at hrun
    rcases hrun with ⟨rfl, _⟩
    obtain ⟨hty, hev⟩ := erased_arg_eval_of_not_isScalar ρL hns
    exact ⟨hty, rfl, hId, hev⟩
  | var x =>
    simp only [HValEnv.evalArgOwn, Option.map_eq_some_iff] at hw
    rcases hw with ⟨⟨tx, wx⟩, hx, rfl⟩
    obtain ⟨la', hwx, hlu, hev⟩ := hrel x tx wx hx
    simp only [argAt, lm_bind_run] at hrun
    rw [ctxVar_run_of_lookup hlu] at hrun
    rcases hrun with ⟨p, n1, hp, hrest⟩
    injection hp with hpe
    have hp1 : (la', tx) = p := congrArg Prod.fst hpe
    subst hp1
    dsimp only at hrest
    by_cases hweq : (tx.width == t.width) = true
    · rw [ite_eq_left hweq, lm_pure_run] at hrest
      injection hrest with hp2
      have hla : la' = la := congrArg Prod.fst hp2
      subst hla
      have hweq' : tx.width = t.width := beq_iff_eq.mp hweq
      have htxEq : tx.toTTy = t.toTTy := congrArg Ty.bits hweq'
      have hty : wx.1 = t.toTTy := hwx.trans htxEq
      refine ⟨hty, rfl, hId, ?_⟩
      rw [← eqRec_trans hwx htxEq wx.2]
      exact eval_cast_ty htxEq hev
    · rw [ite_eq_right hweq] at hrest; cases hrest

private theorem evalObjArgs_cons_eq_some {ρH : HValEnv} {a : LcArg} {as : List LcArg}
    {vs : List (BitVec 64)} (h : ρH.evalObjArgs (a :: as) = some vs) :
    ∃ (w : Word) (v : BitVec 64) (vs' : List (BitVec 64)),
      vs = v :: vs' ∧ ρH.evalArgAt a .tobject = some w ∧ w.toBV64? = some v ∧
      ρH.evalObjArgs as = some vs' := by
  change (match (ρH.evalArgAt a .tobject).bind Word.toBV64?, ρH.evalObjArgs as with
    | some v, some ws => some (v :: ws)
    | _, _ => none) = some vs at h
  cases ha : ρH.evalArgAt a .tobject with
  | none => simp [ha] at h
  | some w =>
    cases hbv : w.toBV64? with
    | none => simp [ha, hbv] at h
    | some v =>
      cases hrest : ρH.evalObjArgs as with
      | none => simp [ha, hbv, hrest] at h
      | some vs' =>
        simp only [ha, hbv, hrest, Option.bind_some, Option.some.injEq] at h
        subst h
        exact ⟨w, v, vs', rfl, rfl, hbv, rfl⟩

private theorem evalArgsOwn_cons_eq_some {ρH : HValEnv} {a : LcArg} {as : List LcArg}
    {ws : List Word} (h : ρH.evalArgsOwn (a :: as) = some ws) :
    ∃ (w : Word) (ws' : List Word),
      ws = w :: ws' ∧ ρH.evalArgOwn a = some w ∧ ρH.evalArgsOwn as = some ws' := by
  change (match ρH.evalArgOwn a, ρH.evalArgsOwn as with
    | some w, some ws' => some (w :: ws')
    | _, _ => none) = some ws at h
  cases ha : ρH.evalArgOwn a with
  | none => simp [ha] at h
  | some w =>
    cases hrest : ρH.evalArgsOwn as with
    | none => simp [ha, hrest] at h
    | some ws' =>
      simp only [ha, hrest, Option.some.injEq] at h
      subst h
      exact ⟨w, ws', rfl, rfl, rfl⟩

theorem mapM_argAt_tobject_spec {c : LCtx} {ρH : HValEnv} {ρL : Frontend.C0.VEnv} :
    ∀ {as : List LcArg} {vs : List (BitVec 64)} {n n' : Nat} {vsArgs : List LArg},
      ctxIdsBelow c n → VarRel c ρH ρL →
      ρH.evalObjArgs as = some vs →
      (as.mapM (fun a => argAt c a .tobject)).run n = .ok (vsArgs, n') →
      n' = n ∧ vsArgs.length = vs.length ∧ (∀ a ∈ vsArgs, argIdsBelow a n) ∧
        (∀ pr ∈ vsArgs.zip vs, LArg.eval ρL i64 pr.1 = some pr.2)
  | [], vs, n, n', vsArgs, _, _, hobj, hrun => by
    change some [] = some vs at hobj
    cases hobj
    simp only [List.mapM_nil, lm_pure_run, Except.ok.injEq, Prod.mk.injEq] at hrun
    rcases hrun with ⟨rfl, rfl⟩
    exact ⟨rfl, rfl, (fun _ ha => False.elim (List.not_mem_nil ha)),
      (fun _ hp => False.elim (List.not_mem_nil hp))⟩
  | a :: as, vs, n, n', vsArgs, hc, hrel, hobj, hrun => by
    obtain ⟨w, v, vs', rfl, hev, hbv, hrest⟩ := evalObjArgs_cons_eq_some hobj
    simp only [List.mapM_cons, lm_bind_run] at hrun
    rcases hrun with ⟨la, n1, ha, hrest2⟩
    obtain ⟨rfl, hId⟩ := argAt_argIdsBelow hc ha
    rcases hrest2 with ⟨las, n2, htl, hpure⟩
    rw [lm_pure_run] at hpure
    injection hpure with hp
    have hvsEq : la :: las = vsArgs := congrArg Prod.fst hp
    have hnEq : n2 = n' := congrArg Prod.snd hp
    subst hvsEq; subst hnEq
    obtain ⟨rfl, hlen, hIds, hprs⟩ := mapM_argAt_tobject_spec hc hrel hrest htl
    obtain ⟨la', hEqTy, hrunLa, hEvLa⟩ := hrel.evalArgAt hev
    have haEq : la = la' := by
      rw [hrunLa _] at ha; cases ha; rfl
    subst haEq
    rcases w with ⟨wt, wv⟩
    dsimp only at hEqTy hbv
    subst hEqTy
    dsimp only [Word.toBV64?] at hbv
    cases hbv
    dsimp only at hEvLa
    refine ⟨rfl, by simp [hlen], ?_, ?_⟩
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact hId
      · exact hIds x hx'
    · intro pr hpr
      rcases List.mem_cons.mp hpr with rfl | hpr'
      · exact hEvLa
      · exact hprs pr hpr'

private theorem evalArgOwn_evalWordArg {c : LCtx} {ρH : HValEnv} {ρL : Frontend.C0.VEnv}
    {a : LcArg} {w : Word} {n n' : Nat} {la : LArg}
    (hrel : VarRel c ρH ρL) (hw : ρH.evalArgOwn a = some w)
    (hrun : (argOwn c a).run n = .ok (la, n')) :
    EvalWordArg ρL la w := by
  cases a with
  | erased =>
    simp only [HValEnv.evalArgOwn, Option.some.injEq] at hw
    subst hw
    simp only [argOwn, lm_pure_run, Except.ok.injEq, Prod.mk.injEq] at hrun
    rcases hrun with ⟨rfl, rfl⟩
    exact ⟨64, 1#64, rfl, rfl, LArg.eval_imm_self ρL i64 1#64⟩
  | var x =>
    simp only [HValEnv.evalArgOwn, Option.map_eq_some_iff] at hw
    rcases hw with ⟨⟨tx, wx⟩, hx, rfl⟩
    obtain ⟨la', hwx, hlu, hev⟩ := hrel x tx wx hx
    simp only [argOwn, lm_bind_run] at hrun
    rw [ctxVar_run_of_lookup hlu] at hrun
    rcases hrun with ⟨p, n1, hp, hpure⟩
    injection hp with hpe
    have hp1 : (la', tx) = p := congrArg Prod.fst hpe
    subst hp1
    rw [lm_pure_run] at hpure
    injection hpure with hpe2
    have hla : la' = la := congrArg Prod.fst hpe2
    subst hla
    rcases wx with ⟨wt, wv⟩
    dsimp only at hwx hev
    subst hwx
    exact ⟨tx.width, wv, (argBitsWidth_of_eval hev).symm, rfl, hev⟩

theorem mapM_argOwn_spec {c : LCtx} {ρH : HValEnv} {ρL : Frontend.C0.VEnv} :
    ∀ {as : List LcArg} {ws : List Word} {n n' : Nat} {las : List LArg},
      ctxIdsBelow c n → VarRel c ρH ρL →
      ρH.evalArgsOwn as = some ws →
      (as.mapM (argOwn c)).run n = .ok (las, n') →
      n' = n ∧ (∀ a ∈ las, argIdsBelow a n) ∧ EvalWordArgs ρL las ws
  | [], ws, n, n', las, _, _, hown, hrun => by
    change some [] = some ws at hown
    cases hown
    simp only [List.mapM_nil, lm_pure_run, Except.ok.injEq, Prod.mk.injEq] at hrun
    rcases hrun with ⟨rfl, rfl⟩
    exact ⟨rfl, (fun _ ha => False.elim (List.not_mem_nil ha)),
      ⟨rfl, fun _ hp => False.elim (List.not_mem_nil hp)⟩⟩
  | a :: as, ws, n, n', las, hc, hrel, hown, hrun => by
    obtain ⟨w, ws', rfl, hw, hrest⟩ := evalArgsOwn_cons_eq_some hown
    simp only [List.mapM_cons, lm_bind_run] at hrun
    rcases hrun with ⟨la, n1, ha, hrest2⟩
    obtain ⟨rfl, hId⟩ := argOwn_argIdsBelow hc ha
    rcases hrest2 with ⟨las', n2, htl, hpure⟩
    rw [lm_pure_run] at hpure
    injection hpure with hp
    have hlasEq : la :: las' = las := congrArg Prod.fst hp
    have hnEq : n2 = n' := congrArg Prod.snd hp
    subst hlasEq; subst hnEq
    obtain ⟨rfl, hIds, hlen, hEvs⟩ := mapM_argOwn_spec hc hrel hrest htl
    have hWord := evalArgOwn_evalWordArg hrel hw ha
    refine ⟨rfl, ?_, by simp [hlen], ?_⟩
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact hId
      · exact hIds x hx'
    · intro pr hpr
      rcases List.mem_cons.mp hpr with rfl | hpr'
      · exact hWord
      · exact hEvs pr hpr'

theorem argsOkForTys_length : ∀ {as : List LcArg} {ts : List LcTy},
    argsOkForTys as ts = true → as.length = ts.length
  | [], [], _ => rfl
  | .erased :: as, _ :: ts, h => by
    change (!_ && argsOkForTys as ts) = true at h
    simp only [Bool.and_eq_true] at h
    exact congrArg Nat.succ (argsOkForTys_length h.2)
  | .var _ :: as, _ :: ts, h => by
    change argsOkForTys as ts = true at h
    exact congrArg Nat.succ (argsOkForTys_length h)
  | [], _ :: _, h => by cases h
  | a :: _, [], h => by cases a <;> cases h

theorem mapM_argAt_tys_spec {c : LCtx} {ρH : HValEnv} {ρL : Frontend.C0.VEnv} :
    ∀ {as : List LcArg} {ts : List LcTy} {ws : List Word} {n n' : Nat} {las : List LArg},
      argsOkForTys as ts = true →
      ρH.evalArgsOwn as = some ws →
      ctxIdsBelow c n → VarRel c ρH ρL →
      ((as.zip ts).mapM (fun p => argAt c p.1 p.2)).run n = .ok (las, n') →
      n' = n ∧ (∀ a ∈ las, argIdsBelow a n) ∧
        ∃ xs : Tup Val (ts.map LcTy.toTTy),
          evalArgs ρL (ts.map LcTy.toTTy) las = some xs ∧ wordsOfTup xs = ws
  | [], [], ws, n, n', las, _, hown, _, _, hrun => by
    change some [] = some ws at hown
    cases hown
    simp only [List.zip_nil_left, List.mapM_nil, lm_pure_run,
      Except.ok.injEq, Prod.mk.injEq] at hrun
    rcases hrun with ⟨rfl, rfl⟩
    exact ⟨rfl, (fun _ ha => False.elim (List.not_mem_nil ha)), ⟨(), rfl, rfl⟩⟩
  | [], _ :: _, _, _, _, _, hok, _, _, _, _ => by cases hok
  | a :: _, [], _, _, _, _, hok, _, _, _, _ => by cases a <;> cases hok
  | a :: as, t :: ts, ws, n, n', las, hok, hown, hc, hrel, hrun => by
    have her : a = .erased → (!t.isScalar) = true := by
      intro ha; subst ha
      change (!t.isScalar && argsOkForTys as ts) = true at hok
      exact (Bool.and_eq_true .. |>.mp hok).1
    have hok' : argsOkForTys as ts = true := by
      cases a with
      | erased =>
        change (!t.isScalar && argsOkForTys as ts) = true at hok
        exact (Bool.and_eq_true .. |>.mp hok).2
      | var _ => exact hok
    obtain ⟨w, ws', rfl, hw, hrest⟩ := evalArgsOwn_cons_eq_some hown
    simp only [List.zip_cons_cons, List.mapM_cons, lm_bind_run] at hrun
    rcases hrun with ⟨la, n1, ha, hrest2⟩
    obtain ⟨hty, rfl, hId, hEv⟩ := argAt_eval_of_evalArgOwn hc hrel hw her ha
    rcases hrest2 with ⟨las', n2, htl, hpure⟩
    rw [lm_pure_run] at hpure
    injection hpure with hp
    have hlasEq : la :: las' = las := congrArg Prod.fst hp
    have hnEq : n2 = n' := congrArg Prod.snd hp
    subst hlasEq; subst hnEq
    obtain ⟨rfl, hIds, xs', hxsEv, hxsWords⟩ :=
      mapM_argAt_tys_spec hok' hrest hc hrel htl
    refine ⟨rfl, ?_, ⟨(hty ▸ w.2, xs'), ?_, ?_⟩⟩
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact hId
      · exact hIds x hx'
    · show evalArgs ρL (t.toTTy :: ts.map LcTy.toTTy) (la :: las') = some (hty ▸ w.2, xs')
      unfold evalArgs
      rw [hEv, hxsEv]
    · show ⟨t.toTTy, hty ▸ w.2⟩ :: wordsOfTup xs' = w :: ws'
      rcases w with ⟨wt, wv⟩
      dsimp only at hty
      subst hty
      rw [hxsWords]

theorem mapM_argAt_fap_run {c : LCtx} :
    ∀ (as : List LcArg) (ps : List LcParam) (n n' : Nat) (args : List (LArg × Ty)),
      ((as.zip ps).mapM fun ((a, p) : LcArg × LcParam) => do
        let la ← argAt c a p.ty
        pure (la, p.ty.toTTy)).run n = .ok (args, n') →
      n' = n ∧ args.map Prod.snd = (as.zip (ps.map (·.ty))).map (fun q => q.2.toTTy) ∧
        ((as.zip (ps.map (·.ty))).mapM fun q => argAt c q.1 q.2).run n =
          .ok (args.map Prod.fst, n)
  | [], _, n, n', args, h => by
    simp only [List.zip_nil_left, List.mapM_nil, lm_pure_run,
      Except.ok.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    exact ⟨rfl, rfl, rfl⟩
  | _ :: _, [], n, n', args, h => by
    simp only [List.zip_nil_right, List.mapM_nil, lm_pure_run,
      Except.ok.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    exact ⟨rfl, rfl, rfl⟩
  | a :: as, p :: ps, n, n', args, h => by
    simp only [List.zip_cons_cons, List.mapM_cons, lm_bind_run] at h
    rcases h with ⟨pair, n1, hpair, hrest⟩
    rcases hpair with ⟨la, n0, ha, hpurePair⟩
    rw [lm_pure_run] at hpurePair
    injection hpurePair with hp1
    have hpairEq : (la, p.ty.toTTy) = pair := congrArg Prod.fst hp1
    have hn0Eq : n0 = n1 := congrArg Prod.snd hp1
    subst hpairEq; subst hn0Eq
    have hnEq : n0 = n := by
      cases a with
      | erased => simp only [argAt] at ha; cases ha; rfl
      | var x =>
        simp only [argAt, lm_bind_run] at ha
        rcases ha with ⟨⟨v, vt⟩, n0', hv, hrestA⟩
        obtain ⟨_, rfl⟩ := ctxVar_run_ok hv
        dsimp only at hrestA
        by_cases hw : (vt.width == p.ty.width) = true
        · rw [ite_eq_left hw, lm_pure_run] at hrestA
          injection hrestA with hpa
          exact (congrArg Prod.snd hpa).symm
        · rw [ite_eq_right hw] at hrestA; cases hrestA
    subst hnEq
    rcases hrest with ⟨args', n2, htl, hpure⟩
    rw [lm_pure_run] at hpure
    injection hpure with hp2
    have hargsEq : (la, p.ty.toTTy) :: args' = args := congrArg Prod.fst hp2
    have hn2Eq : n2 = n' := congrArg Prod.snd hp2
    subst hargsEq; subst hn2Eq
    obtain ⟨rfl, hmap, hrunTl⟩ := mapM_argAt_fap_run as ps _ n2 args' htl
    refine ⟨rfl, by simp [hmap], ?_⟩
    simp only [List.map_cons, List.zip_cons_cons, List.mapM_cons, lm_bind_run]
    refine ⟨la, _, ha, args'.map Prod.fst, _, hrunTl, ?_⟩
    rw [lm_pure_run]

theorem map_snd_zip_map {as : List LcArg} {ps : List LcParam}
    (hlen : as.length = ps.length) :
    (as.zip (ps.map (·.ty))).map (fun q => q.2.toTTy) = ps.map (·.ty.toTTy) := by
  induction as generalizing ps with
  | nil =>
    cases ps with
    | nil => rfl
    | cons _ _ => cases hlen
  | cons a as ih =>
    cases ps with
    | nil => cases hlen
    | cons p ps =>
      simp only [List.length_cons, Nat.succ.injEq] at hlen
      simp [ih hlen]

/-! ## 2. Heap-Focus Object Read Helpers -/

theorem mem_load_lcnfObj_field {rt addr : BitVec 64} {σ : HState} {mem_f : Mem 64 → Prop}
    {mem : Mem 64} {o : LcnfObj} {i : Nat}
    (hmObj : o ∈ σ.objs) (htag : o.tag ≤ 244) (hi : i < o.fields.length)
    (haddr : o.addr = addr) (hm : (σ.mem rt ⋆ mem_f) mem) :
    loadVal mem i64 (addr + BitVec.ofNat 64 (8 + 8 * i)) = some (o.fields[i]'hi) := by
  obtain ⟨idx, hidx, rfl⟩ := List.mem_iff_getElem.mp hmObj
  have hm' : (lcnfObjMem σ.objs[idx] ⋆
      (lcnfHeap (σ.objs.take idx) ⋆ lcnfHeap (σ.objs.drop (idx + 1)) ⋆
        fullRtInv rt σ.st σ.scr σ.scrLimbs ⋆ mem_f)) mem := by
    rw [hstate_mem_unfold, lcnfHeap_focus σ.objs hidx] at hm
    dsimp only [fullRtInv]
    exact sep_cast hm (by ac_rfl)
  subst haddr
  exact lcnfObjMem_load_field htag hi hm'

theorem mem_load_lcnfObj_scalar {rt addr : BitVec 64} {σ : HState} {mem_f : Mem 64 → Prop}
    {mem : Mem 64} {o : LcnfObj} {bOff w : Nat}
    (hmObj : o ∈ σ.objs) (hwf : o.Wf) (htag : o.tag ≤ 244)
    (hoff : bOff + (w + 7) / 8 ≤ o.scalarData.length)
    (haddr : o.addr = addr) (hm : (σ.mem rt ⋆ mem_f) mem) :
    loadVal mem (.bits w) (addr + BitVec.ofNat 64 (8 + 8 * o.fields.length + bOff)) =
      some (readBitsLE w o.scalarData bOff) := by
  obtain ⟨idx, hidx, rfl⟩ := List.mem_iff_getElem.mp hmObj
  have hm' : (lcnfObjMem σ.objs[idx] ⋆
      (lcnfHeap (σ.objs.take idx) ⋆ lcnfHeap (σ.objs.drop (idx + 1)) ⋆
        fullRtInv rt σ.st σ.scr σ.scrLimbs ⋆ mem_f)) mem := by
    rw [hstate_mem_unfold, lcnfHeap_focus σ.objs hidx] at hm
    dsimp only [fullRtInv]
    exact sep_cast hm (by ac_rfl)
  subst haddr
  exact lcnfObjMem_load_scalar hwf htag hoff hm'

/-! ## 3. `HPrim.wp` Return-Width Refinement -/

private theorem natBinSlowInfo?_retTy {op : String} {arity : Nat} {retTy : LcTy}
    {code resW : Nat} {isBits : Bool}
    (hp : isPhase1NatPrim op arity retTy = true)
    (hi : natBinSlowInfo? op = some (code, resW, isBits)) :
    resW = retTy.width := by
  unfold natBinSlowInfo? at hi
  split at hi <;> cases hi
  all_goals
    rcases arity with _ | _ | _ | _ <;> simp only [isPhase1NatPrim] at hp
    all_goals first | cases hp | exact (beq_iff_eq.mp hp).symm

private theorem natBinFast?_retTy {op : String} {a b : BitVec 64} {w : Word}
    {code resW : Nat} {isBits : Bool}
    (hi : natBinSlowInfo? op = some (code, resW, isBits))
    (hf : natBinFast? op a b = some w) :
    w.1 = .bits resW := by
  unfold natBinSlowInfo? at hi
  split at hi <;> cases hi
  all_goals
    unfold natBinFast? at hf
    split at hf
    · cases hf
    · dsimp only at hf
      first
        | (cases hf; rfl; done)
        | (by_cases hc : (a - 1#64 + b < b) <;>
            simp [hc] at hf <;> first | (cases hf; rfl; done) | (rcases hf with ⟨_, rfl⟩; rfl))
        | (by_cases hc : ((a >>> 1).toNat * (b >>> 1).toNat < 2 ^ 63) <;>
            simp [hc] at hf <;> first | (cases hf; rfl; done) | (rcases hf with ⟨_, rfl⟩; rfl))
        | (by_cases hc : ((b >>> 1).toNat < 63 ∧ (a >>> 1).toNat <<< (b >>> 1).toNat < 2 ^ 63) <;>
            simp [hc] at hf <;> first | (cases hf; rfl; done) | (rcases hf with ⟨_, rfl⟩; rfl))

private theorem uintPure?_retTy {w : Nat} {op : String} {ws : List Word} {r : Word}
    {retTy : LcTy}
    (hp : isPhase1UintPrim w op ws.length retTy = true)
    (hu : uintPure? w op ws = some r) :
    r.1 = retTy.toTTy := by
  rcases ws with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
  · unfold uintPure? at hu; dsimp only at hu
    split at hu <;> try dsimp only at hu
    all_goals cases hu
  · unfold uintPure? at hu; dsimp only at hu
    split at hu <;> try dsimp only at hu
    all_goals
      first
        | (cases hu; done)
        | (simp only [isPhase1UintPrim, List.length] at hp
           cases ha : Word.toBits? w a <;> simp [ha] at hu
           subst hu
           exact congrArg Ty.bits (beq_iff_eq.mp hp).symm)
  · unfold uintPure? at hu; dsimp only at hu
    split at hu <;> try dsimp only at hu
    all_goals
      first
        | (cases hu; done)
        | (simp only [isPhase1UintPrim, List.length] at hp
           cases h1 : Word.toBits? w a <;> simp [h1] at hu
           cases h2 : Word.toBits? w b <;> simp [h2] at hu
           subst hu
           exact congrArg Ty.bits (beq_iff_eq.mp hp).symm)
  · unfold uintPure? at hu; dsimp only at hu
    split at hu <;> try dsimp only at hu
    all_goals cases hu

private theorem hNatPrimWp_retTy {rt : BitVec 64} {op : String} {ws : List Word}
    {retTy : LcTy} {K : HPost} {X : HXPost} {σ : HState}
    (hp : isPhase1NatPrim op ws.length retTy = true)
    (hwp : HNatPrimWp rt op ws K X σ) :
    HNatPrimWp rt op ws (fun r σ' => r.1 = retTy.toTTy ∧ K r σ') X σ := by
  unfold HNatPrimWp at hwp ⊢
  cases hinfo : natBinSlowInfo? op with
  | some info =>
    rcases info with ⟨code, resW, isBits⟩
    have hrw := natBinSlowInfo?_retTy hp hinfo
    simp only [hinfo] at hwp ⊢
    rcases ws with _ | ⟨wa, _ | ⟨wb, _ | _⟩⟩
    · exact False.elim hwp
    · exact False.elim hwp
    · cases hwa : wa.toBV64? with
      | none => simp [hwa] at hwp
      | some a => cases hwb : wb.toBV64? with
        | none => simp [hwa, hwb] at hwp
        | some b =>
          simp only [hwa, hwb] at hwp ⊢
          cases hfast : natBinFast? op a b with
          | some w =>
            simp only [hfast] at hwp ⊢
            have hw1 := natBinFast?_retTy hinfo hfast
            rw [hrw] at hw1
            exact ⟨hw1, hwp⟩
          | none =>
            simp only [hfast] at hwp ⊢
            by_cases hb : isBits = true
            · rw [ite_eq_left hb] at hwp ⊢
              rcases hwp with ⟨aVal, ha, hok, hk⟩
              exact ⟨aVal, ha, hok, fun res st' scr' objs' h1 h2 h3 h4 =>
                ⟨congrArg Ty.bits hrw, hk res st' scr' objs' h1 h2 h3 h4⟩⟩
            · rw [ite_eq_right hb] at hwp ⊢
              rcases hwp with ⟨aVal, bVal, ha, hb', hok, hk⟩
              exact ⟨aVal, bVal, ha, hb', hok, fun res st' scr' objs' h1 h2 h3 h4 =>
                ⟨congrArg Ty.bits hrw, hk res st' scr' objs' h1 h2 h3 h4⟩⟩
    · exact False.elim hwp
  | none =>
    simp only [hinfo] at hwp ⊢
    split at hwp
    · next wa =>
      simp only [isPhase1NatPrim, List.length] at hp
      have hw64 : retTy.width = 64 := beq_iff_eq.mp hp
      cases hwa : wa.toBV64? with
      | none => simp [hwa] at hwp
      | some a =>
        simp only [hwa] at hwp ⊢
        by_cases ha : (a &&& 1#64 != 0#64) = true
        · rw [ite_eq_left ha] at hwp ⊢
          exact ⟨congrArg Ty.bits hw64.symm, hwp⟩
        · rw [ite_eq_right ha] at hwp ⊢
          rcases hwp with ⟨aVal, bVal, ha', hb', hok, hk⟩
          exact ⟨aVal, bVal, ha', hb', hok, fun res st' scr' objs' h1 h2 h3 h4 =>
            ⟨congrArg Ty.bits hw64.symm, hk res st' scr' objs' h1 h2 h3 h4⟩⟩
    · next wa wb =>
      simp only [isPhase1NatPrim, List.length] at hp
      have hw64 : retTy.width = 64 := beq_iff_eq.mp hp
      cases hwa : wa.toBV64? with
      | none => simp [hwa] at hwp
      | some a => cases hwb : wb.toBV64? with
        | none => simp [hwa, hwb] at hwp
        | some b =>
          simp only [hwa, hwb] at hwp ⊢
          rcases hwp with ⟨aVal, bVal, ha, hb, hok, hk⟩
          exact ⟨aVal, bVal, ha, hb, hok, fun res st' scr' objs' h1 h2 h3 h4 h5 =>
            ⟨congrArg Ty.bits hw64.symm, hk res st' scr' objs' h1 h2 h3 h4 h5⟩⟩
    · next wa wb =>
      simp only [isPhase1NatPrim, List.length] at hp
      have hw64 : retTy.width = 64 := beq_iff_eq.mp hp
      cases hwa : wa.toBV64? with
      | none => simp [hwa] at hwp
      | some a => cases hwb : wb.toBV64? with
        | none => simp [hwa, hwb] at hwp
        | some b =>
          simp only [hwa, hwb] at hwp ⊢
          rcases hwp with ⟨aVal, bVal, ha, hb, hok, hk⟩
          exact ⟨aVal, bVal, ha, hb, hok, fun res st' scr' objs' h1 h2 h3 h4 h5 =>
            ⟨congrArg Ty.bits hw64.symm, hk res st' scr' objs' h1 h2 h3 h4 h5⟩⟩
    · next wa =>
      simp only [isPhase1NatPrim, List.length] at hp
      have hw64 : retTy.width = 64 := beq_iff_eq.mp hp
      cases hwa : wa.toBV64? with
      | none => simp [hwa] at hwp
      | some a =>
        simp only [hwa] at hwp ⊢
        rcases hwp with ⟨aVal, ha, hok, hk⟩
        exact ⟨aVal, ha, hok, fun res st' scr' objs' h1 h2 h3 h4 =>
          ⟨congrArg Ty.bits hw64.symm, hk res st' scr' objs' h1 h2 h3 h4⟩⟩
    · next wn =>
      simp only [isPhase1NatPrim, List.length] at hp
      have hw64 : retTy.width = 64 := beq_iff_eq.mp hp
      cases hwn : wn.toBV64? with
      | none => simp [hwn] at hwp
      | some n =>
        simp only [hwn] at hwp ⊢
        rcases hwp with ⟨val, hnih, hwf, hrest⟩
        refine ⟨val, hnih, hwf, ?_⟩
        dsimp only at hrest ⊢
        by_cases hsc : (n &&& 1#64) ≠ 0#64
        · rw [ite_eq_left hsc] at hrest ⊢
          exact ⟨hrest.1, fun s st' a1 a2 a3 a4 a5 =>
            ⟨congrArg Ty.bits hw64.symm, hrest.2 s st' a1 a2 a3 a4 a5⟩⟩
        · rw [ite_eq_right hsc] at hrest ⊢
          rcases hrest with ⟨nObj, hm, had, hc, hrc, hif⟩
          refine ⟨nObj, hm, had, hc, hrc, ?_⟩
          by_cases hcn : trimZeroLimbsLen nObj.limbs nObj.arrSize = 0
          · rw [ite_eq_left hcn] at hif ⊢
            exact ⟨hif.1, fun s st' objs' a1 a2 a3 a4 a5 a6 =>
              ⟨congrArg Ty.bits hw64.symm, hif.2 s st' objs' a1 a2 a3 a4 a5 a6⟩⟩
          · rw [ite_eq_right hcn] at hif ⊢
            by_cases hcap : mpzMaxLimbsNat < trimZeroLimbsLen nObj.limbs nObj.arrSize
            · rw [ite_eq_left hcap] at hif ⊢; exact hif
            · rw [ite_eq_right hcap] at hif ⊢
              exact ⟨hif.1, fun s st' objs' a1 a2 a3 a4 a5 a6 =>
                ⟨congrArg Ty.bits hw64.symm, hif.2 s st' objs' a1 a2 a3 a4 a5 a6⟩⟩
    · exact False.elim hwp

private theorem hUintOfNatWp_retTy {rt : BitVec 64} {w : Nat} {wa : Word} {decAfter : Bool}
    {retTy : LcTy} (hw : retTy.width = w) {K : HPost} {σ : HState}
    (hwp : HUintOfNatWp rt w wa decAfter K σ) :
    HUintOfNatWp rt w wa decAfter (fun r σ' => r.1 = retTy.toTTy ∧ K r σ') σ := by
  unfold HUintOfNatWp at hwp ⊢
  cases hwa : wa.toBV64? with
  | none => simp [hwa] at hwp
  | some a =>
    simp only [hwa] at hwp ⊢
    by_cases hsc : (a &&& 1#64 != 0#64) = true
    · rw [ite_eq_left hsc] at hwp ⊢
      by_cases hd : decAfter = true
      · rw [ite_eq_left hd] at hwp ⊢
        exact HDecN_mono (fun σ' hk => ⟨congrArg Ty.bits hw.symm, hk⟩) 1 σ hwp
      · rw [ite_eq_right hd] at hwp ⊢
        exact ⟨congrArg Ty.bits hw.symm, hwp⟩
    · rw [ite_eq_right hsc] at hwp ⊢
      rcases hwp with ⟨aVal, ha, hok, hk⟩
      refine ⟨aVal, ha, hok, fun res st' scr' objs' h1 h2 h3 h4 => ?_⟩
      have hbody := hk res st' scr' objs' h1 h2 h3 h4
      by_cases hd : decAfter = true
      · rw [ite_eq_left hd] at hbody ⊢
        exact HDecN_mono (fun σ' hk' => ⟨congrArg Ty.bits hw.symm, hk'⟩) 1 _ hbody
      · rw [ite_eq_right hd] at hbody ⊢
        exact ⟨congrArg Ty.bits hw.symm, hbody⟩

private theorem hUintPrimWp_retTy {rt : BitVec 64} {w : Nat} {op : String} {ws : List Word}
    {retTy : LcTy} {K : HPost} {σ : HState}
    (hp : isPhase1UintPrim w op ws.length retTy = true)
    (hwp : HUintPrimWp rt w op ws K σ) :
    HUintPrimWp rt w op ws (fun r σ' => r.1 = retTy.toTTy ∧ K r σ') σ := by
  unfold HUintPrimWp at hwp ⊢
  cases hu : uintPure? w op ws with
  | some r =>
    simp only [hu] at hwp ⊢
    exact ⟨uintPure?_retTy hp hu, hwp⟩
  | none =>
    simp only [hu] at hwp ⊢
    split at hwp
    · simp only [isPhase1UintPrim, List.length] at hp
      exact hUintOfNatWp_retTy (beq_iff_eq.mp hp) hwp
    · simp only [isPhase1UintPrim, List.length] at hp
      exact hUintOfNatWp_retTy (beq_iff_eq.mp hp) hwp
    · simp only [isPhase1UintPrim, List.length] at hp
      exact hUintOfNatWp_retTy (beq_iff_eq.mp hp) hwp
    · simp only [isPhase1UintPrim, List.length] at hp
      exact hUintOfNatWp_retTy (beq_iff_eq.mp hp) hwp
    · next a =>
      simp only [isPhase1UintPrim, List.length] at hp
      have hw64 : retTy.width = 64 := beq_iff_eq.mp hp
      cases hwa : Word.toBits? w a with
      | none => simp [hwa] at hwp
      | some av =>
        simp only [hwa] at hwp ⊢
        by_cases hsc : (decide (w < 64) || av.setWidth 64 >>> 63 == 0#64) = true
        · rw [ite_eq_left hsc] at hwp ⊢; exact ⟨congrArg Ty.bits hw64.symm, hwp⟩
        · rw [ite_eq_right hsc] at hwp ⊢
          rcases hwp with ⟨aVal, ha, hok, hk⟩
          exact ⟨aVal, ha, hok, fun res st' scr' objs' h1 h2 h3 h4 =>
            ⟨congrArg Ty.bits hw64.symm, hk res st' scr' objs' h1 h2 h3 h4⟩⟩
    · next a =>
      simp only [isPhase1UintPrim, List.length] at hp
      have hw64 : retTy.width = 64 := beq_iff_eq.mp hp
      cases hwa : Word.toBits? w a with
      | none => simp [hwa] at hwp
      | some av =>
        simp only [hwa] at hwp ⊢
        by_cases hsc : (decide (w < 64) || av.setWidth 64 >>> 63 == 0#64) = true
        · rw [ite_eq_left hsc] at hwp ⊢; exact ⟨congrArg Ty.bits hw64.symm, hwp⟩
        · rw [ite_eq_right hsc] at hwp ⊢
          rcases hwp with ⟨aVal, ha, hok, hk⟩
          exact ⟨aVal, ha, hok, fun res st' scr' objs' h1 h2 h3 h4 =>
            ⟨congrArg Ty.bits hw64.symm, hk res st' scr' objs' h1 h2 h3 h4⟩⟩
    · exact False.elim hwp

private theorem hStrLen_retTy {ws0 : Word} {retTy : LcTy} (hw64 : retTy.width = 64)
    {K : HPost} {σ : HState} {f : LcnfObj → BitVec 64}
    (hwp : match ws0.toBV64? with
      | some s => ∃ o, o ∈ σ.objs ∧ o.addr = s ∧ StrCanon o ∧ K (Word.i64 (f o)) σ
      | none => False) :
    match ws0.toBV64? with
    | some s =>
      ∃ o, o ∈ σ.objs ∧ o.addr = s ∧ StrCanon o ∧
        (Word.i64 (f o)).1 = retTy.toTTy ∧ K (Word.i64 (f o)) σ
    | none => False := by
  cases hws : ws0.toBV64? with
  | none => simp [hws] at hwp
  | some s =>
    simp only [hws] at hwp ⊢
    rcases hwp with ⟨o, hm, ha, hc, hk⟩
    exact ⟨o, hm, ha, hc, congrArg Ty.bits hw64.symm, hk⟩

private theorem hStrAppendWp_retTy {s1 s2 : BitVec 64} {retTy : LcTy} (hw64 : retTy.width = 64)
    {K : HPost} {X : HXPost} {σ : HState}
    (hwp : HStringAppendWp s1 s2 K X σ) :
    HStringAppendWp s1 s2 (fun r σ' => r.1 = retTy.toTTy ∧ K r σ') X σ := by
  unfold HStringAppendWp at hwp ⊢
  rcases hwp with ⟨o1, hm1, ha1, hc1, o2, hm2, ha2, hc2, hif⟩
  refine ⟨o1, hm1, ha1, hc1, o2, hm2, ha2, hc2, ?_⟩
  dsimp only at hif ⊢
  by_cases h0 : (strPayload o2).length = 0
  · rw [ite_eq_left h0] at hif ⊢
    exact ⟨hif.1, congrArg Ty.bits hw64.symm, hif.2⟩
  · rw [ite_eq_right h0] at hif ⊢
    by_cases hcap : strMaxCap ≤ (strPayload o1).length + (strPayload o2).length
    · rw [ite_eq_left hcap] at hif ⊢; exact hif
    · rw [ite_eq_right hcap] at hif ⊢
      exact ⟨hif.1, hif.2.1, fun r st' objs' a1 a2 a3 a4 a5 a6 =>
        ⟨congrArg Ty.bits hw64.symm, hif.2.2 r st' objs' a1 a2 a3 a4 a5 a6⟩⟩

private theorem hStringPrimWp_retTy {parts : List String} {ws : List Word}
    {retTy : LcTy} {K : HPost} {X : HXPost} {σ : HState}
    (hp : isPhase1StringPrim parts ws.length retTy = true)
    (hwp : HStringPrimWp parts ws K X σ) :
    HStringPrimWp parts ws (fun r σ' => r.1 = retTy.toTTy ∧ K r σ') X σ := by
  simp only [isPhase1StringPrim] at hp
  split at hp <;> unfold HStringPrimWp at hwp ⊢
  · rcases ws with _ | ⟨ws0, _ | _⟩ <;> simp at hwp ⊢
    exact hStrLen_retTy (beq_iff_eq.mp hp) hwp
  · rcases ws with _ | ⟨ws0, _ | _⟩ <;> simp at hwp ⊢
    exact hStrLen_retTy (beq_iff_eq.mp hp) hwp
  · rcases ws with _ | ⟨ws0, _ | _⟩ <;> simp at hwp ⊢
    exact hStrLen_retTy (beq_iff_eq.mp hp) hwp
  · rcases ws with _ | ⟨w0, _ | ⟨w1, _ | _⟩⟩ <;> simp at hwp ⊢
    exact ⟨hwp.1, hwp.1.trans (congrArg Ty.bits (beq_iff_eq.mp hp).symm), hwp.2⟩
  · rcases ws with _ | ⟨w1, _ | ⟨w2, _ | _⟩⟩ <;> try exact False.elim hwp
    dsimp only at hwp ⊢
    cases h1 : w1.toBV64? with
    | none => simp [h1] at hwp
    | some s1 => cases h2 : w2.toBV64? with
      | none => simp [h1, h2] at hwp
      | some s2 =>
        simp only [h1, h2] at hwp ⊢
        exact hStrAppendWp_retTy (beq_iff_eq.mp hp) hwp
  · rcases ws with _ | ⟨w1, _ | ⟨w2, _ | _⟩⟩ <;> try exact False.elim hwp
    dsimp only at hwp ⊢
    cases h1 : w1.toBV64? with
    | none => simp [h1] at hwp
    | some s1 => cases h2 : w2.toBV64? with
      | none => simp [h1, h2] at hwp
      | some s2 =>
        simp only [h1, h2] at hwp ⊢
        exact hStrAppendWp_retTy (beq_iff_eq.mp hp) hwp
  · rcases ws with _ | ⟨w1, _ | ⟨w2, _ | _⟩⟩ <;> simp at hwp ⊢
    cases h1 : w1.toBV64? with
    | none => simp [h1] at hwp
    | some s1 => cases h2 : w2.toBV64? with
      | none => simp [h1, h2] at hwp
      | some s2 =>
        simp only [h1, h2] at hwp ⊢
        by_cases hs : s1 = s2
        · rw [ite_eq_left hs] at hwp ⊢
          exact ⟨congrArg Ty.bits (beq_iff_eq.mp hp).symm, hwp⟩
        · rw [ite_eq_right hs] at hwp ⊢
          rcases hwp with ⟨o1, hm1, ha1, hc1, o2, hm2, ha2, hc2, hk⟩
          exact ⟨o1, hm1, ha1, hc1, o2, hm2, ha2, hc2,
            congrArg Ty.bits (beq_iff_eq.mp hp).symm, hk⟩
  · rcases ws with _ | ⟨w1, _ | ⟨w2, _ | _⟩⟩ <;> simp at hwp ⊢
    cases h1 : w1.toBV64? with
    | none => simp [h1] at hwp
    | some s1 => cases h2 : w2.toBV64? with
      | none => simp [h1, h2] at hwp
      | some s2 =>
        simp only [h1, h2] at hwp ⊢
        by_cases hs : s1 = s2
        · rw [ite_eq_left hs] at hwp ⊢
          exact ⟨congrArg Ty.bits (beq_iff_eq.mp hp).symm, hwp⟩
        · rw [ite_eq_right hs] at hwp ⊢
          rcases hwp with ⟨o1, hm1, ha1, hc1, o2, hm2, ha2, hc2, hk⟩
          exact ⟨o1, hm1, ha1, hc1, o2, hm2, ha2, hc2,
            congrArg Ty.bits (beq_iff_eq.mp hp).symm, hk⟩
  · cases hp

private theorem hByteArrayPrimWp_retTy {op : String} {ws : List Word}
    {retTy : LcTy} {K : HPost} {X : HXPost} {σ : HState}
    (hp : isPhase1ByteArrayPrim op ws.length retTy = true)
    (hwp : HByteArrayPrimWp op ws K X σ) :
    HByteArrayPrimWp op ws (fun r σ' => r.1 = retTy.toTTy ∧ K r σ') X σ := by
  simp only [isPhase1ByteArrayPrim] at hp
  split at hp <;> unfold HByteArrayPrimWp at hwp ⊢
  · rcases ws with _ | ⟨wba, _ | _⟩ <;> simp at hwp ⊢
    cases hba : wba.toBV64? with
    | none => simp [hba] at hwp
    | some ba =>
      simp only [hba] at hwp ⊢
      rcases hwp with ⟨o, hm, ha, hc, hk⟩
      exact ⟨o, hm, ha, hc, congrArg Ty.bits (beq_iff_eq.mp hp).symm, hk⟩
  · rcases ws with _ | ⟨wba, _ | _⟩ <;> simp at hwp ⊢
    cases hba : wba.toBV64? with
    | none => simp [hba] at hwp
    | some ba =>
      simp only [hba] at hwp ⊢
      rcases hwp with ⟨o, hm, ha, hc, hk⟩
      exact ⟨o, hm, ha, hc, congrArg Ty.bits (beq_iff_eq.mp hp).symm, hk⟩
  · rcases ws with _ | ⟨w0, _ | ⟨wb, _ | _⟩⟩ <;> simp at hwp ⊢
    exact ⟨hwp.1, hwp.1.trans (congrArg Ty.bits (beq_iff_eq.mp hp).symm), hwp.2⟩
  · rcases ws with _ | ⟨wba, _ | ⟨wb, _ | _⟩⟩ <;> simp at hwp ⊢
    cases hba : wba.toBV64? with
    | none => simp [hba] at hwp
    | some ba => cases hwb : wb.toBits? 8 with
      | none => simp [hba, hwb] at hwp
      | some b =>
        simp only [hba, hwb] at hwp ⊢
        rcases hwp with ⟨k, hk, ha, hc, hif⟩
        refine ⟨k, hk, ha, hc, ?_⟩
        by_cases hcap : (σ.objs[k]'hk).cap ≤ (σ.objs[k]'hk).arrSize ∧
            baMaxCap ≤ (σ.objs[k]'hk).cap
        · rw [ite_eq_left hcap] at hif ⊢; exact hif
        · rw [ite_eq_right hcap] at hif ⊢
          exact ⟨hif.1, fun r st' b1 b2 b3 b4 b5 b6 =>
            ⟨congrArg Ty.bits (beq_iff_eq.mp hp).symm, hif.2 r st' b1 b2 b3 b4 b5 b6⟩⟩
  · rcases ws with _ | ⟨wba, _ | ⟨wi, _ | _⟩⟩ <;> simp at hwp ⊢
    cases hba : wba.toBV64? with
    | none => simp [hba] at hwp
    | some ba => cases hi : wi.toBV64? with
      | none => simp [hba, hi] at hwp
      | some idx =>
        simp only [hba, hi] at hwp ⊢
        rcases hwp with ⟨o, hm, ha, hc, hk⟩
        exact ⟨o, hm, ha, hc, congrArg Ty.bits (beq_iff_eq.mp hp).symm, hk⟩
  · rcases ws with _ | ⟨wba, _ | ⟨wi, _ | ⟨w2, _ | _⟩⟩⟩ <;> simp at hwp ⊢
    cases hba : wba.toBV64? with
    | none => simp [hba] at hwp
    | some ba => cases hi : wi.toBV64? with
      | none => simp [hba, hi] at hwp
      | some idx =>
        simp only [hba, hi] at hwp ⊢
        rcases hwp with ⟨o, hm, ha, hc, hk⟩
        exact ⟨o, hm, ha, hc, congrArg Ty.bits (beq_iff_eq.mp hp).symm, hk⟩
  · cases hp

private theorem hArraySetWp_retTy {arr idx v : BitVec 64} {retTy : LcTy} (hw64 : retTy.width = 64)
    {K : HPost} {σ : HState} (hwp : HArraySetWp arr idx v K σ) :
    HArraySetWp arr idx v (fun r σ' => r.1 = retTy.toTTy ∧ K r σ') σ := by
  rcases hwp with ⟨k, hk, a1, a2, a3, hwf, hcl, hif⟩
  refine ⟨k, hk, a1, a2, a3, hwf, hcl, ?_⟩
  dsimp only at hif ⊢
  by_cases hlt :
      (if (idx &&& 1#64) ≠ 0#64 then (idx >>> 1).toNat else (σ.objs[k]'hk).fields.length) <
      (σ.objs[k]'hk).fields.length
  · rw [dite_eq_left hlt] at hif ⊢
    rcases hif with ⟨b1, b2, b3, hcont⟩
    exact ⟨b1, b2, b3, fun r st' objs' c1 c2 c3 c4 c5 rObj m1 m2 d1 d2 d3 d4 d5 =>
      ⟨congrArg Ty.bits hw64.symm, hcont r st' objs' c1 c2 c3 c4 c5 rObj m1 m2 d1 d2 d3 d4 d5⟩⟩
  · rw [dite_eq_right hlt] at hif ⊢
    exact ⟨hif.1, fun st' objs' c1 c2 c3 =>
      ⟨congrArg Ty.bits hw64.symm, hif.2 st' objs' c1 c2 c3⟩⟩

private theorem hArrSize_retTy {wa : Word} {retTy : LcTy} (hw64 : retTy.width = 64)
    {K : HPost} {σ : HState} {f : LcnfObj → BitVec 64}
    (hwp : match wa.toBV64? with
      | some arr => ∃ arrObj, arrObj ∈ σ.objs ∧ arrObj.addr = arr ∧ ArrCanon arrObj ∧
          K (Word.i64 (f arrObj)) σ
      | none => False) :
    match wa.toBV64? with
    | some arr => ∃ arrObj, arrObj ∈ σ.objs ∧ arrObj.addr = arr ∧ ArrCanon arrObj ∧
        (Word.i64 (f arrObj)).1 = retTy.toTTy ∧ K (Word.i64 (f arrObj)) σ
    | none => False := by
  cases ha : wa.toBV64? with
  | none => simp [ha] at hwp
  | some arr =>
    simp only [ha] at hwp ⊢
    rcases hwp with ⟨o, hm, ha', hc, hk⟩
    exact ⟨o, hm, ha', hc, congrArg Ty.bits hw64.symm, hk⟩

private theorem hArrMkEmpty_retTy {wa : Word} {retTy : LcTy} (hw64 : retTy.width = 64)
    {K : HPost} {X : HXPost} {σ : HState}
    (hwp : match wa.toBV64? with
      | none => False
      | some cap =>
        let c := if cap &&& 1#64 ≠ 0#64 then (cap >>> 1).toNat else 0
        if c ≤ arrMaxCap then
          canAllocBytesR0 σ.st (arrAllocBytes c) ∧
          ∀ p st', p ≠ 0#64 → p.toNat % 8 = 0 → st'.PreservesMeta σ.st → st'.rem ≤ σ.st.rem →
            let arrObj := mkArrObj p (1#32) c []
            ArrCanon arrObj →
            K (Word.i64 p)
              { st := st', objs := arrObj :: σ.objs, scr := σ.scr, scrLimbs := σ.scrLimbs }
        else X panicCapCode σ) :
    match wa.toBV64? with
    | none => False
    | some cap =>
      let c := if cap &&& 1#64 ≠ 0#64 then (cap >>> 1).toNat else 0
      if c ≤ arrMaxCap then
        canAllocBytesR0 σ.st (arrAllocBytes c) ∧
        ∀ p st', p ≠ 0#64 → p.toNat % 8 = 0 → st'.PreservesMeta σ.st → st'.rem ≤ σ.st.rem →
          let arrObj := mkArrObj p (1#32) c []
          ArrCanon arrObj →
          (Word.i64 p).1 = retTy.toTTy ∧ K (Word.i64 p)
            { st := st', objs := arrObj :: σ.objs, scr := σ.scr, scrLimbs := σ.scrLimbs }
      else X panicCapCode σ := by
  cases hc : wa.toBV64? with
  | none => simp [hc] at hwp
  | some cap =>
    simp only [hc] at hwp ⊢
    by_cases hle : (if cap &&& 1#64 ≠ 0#64 then (cap >>> 1).toNat else 0) ≤ arrMaxCap
    · rw [ite_eq_left hle] at hwp ⊢
      exact ⟨hwp.1, fun p st' a1 a2 a3 a4 a5 =>
        ⟨congrArg Ty.bits hw64.symm, hwp.2 p st' a1 a2 a3 a4 a5⟩⟩
    · rw [ite_eq_right hle] at hwp ⊢; exact hwp

private theorem hArrayPrimWp_retTy {op : String} {ws : List Word}
    {retTy : LcTy} {K : HPost} {X : HXPost} {σ : HState}
    (hp : isPhase1ArrayPrim op ws.length retTy = true)
    (hwp : HArrayPrimWp op ws K X σ) :
    HArrayPrimWp op ws (fun r σ' => r.1 = retTy.toTTy ∧ K r σ') X σ := by
  simp only [isPhase1ArrayPrim] at hp
  split at hp <;> unfold HArrayPrimWp at hwp ⊢
  · have hw64 : retTy.width = 64 := beq_iff_eq.mp hp
    rcases ws with _ | ⟨w0, _ | _⟩ <;> simp at hwp ⊢
    exact ⟨hwp.1, fun p st' a1 a2 a3 a4 a5 =>
      ⟨congrArg Ty.bits hw64.symm, hwp.2 p st' a1 a2 a3 a4 a5⟩⟩
  · have hw64 : retTy.width = 64 := beq_iff_eq.mp hp
    rcases ws with _ | ⟨w0, _ | ⟨wa, _ | _⟩⟩ <;> try exact False.elim hwp
    dsimp only at hwp ⊢; exact hArrSize_retTy hw64 hwp
  · have hw64 : retTy.width = 64 := beq_iff_eq.mp hp
    rcases ws with _ | ⟨w0, _ | ⟨wa, _ | _⟩⟩ <;> try exact False.elim hwp
    dsimp only at hwp ⊢; exact hArrSize_retTy hw64 hwp
  · have hw64 : retTy.width = 64 := beq_iff_eq.mp hp
    rcases ws with _ | ⟨w0, _ | ⟨wa, _ | _⟩⟩ <;> try exact False.elim hwp
    dsimp only at hwp ⊢; exact hArrMkEmpty_retTy hw64 hwp
  · have hw64 : retTy.width = 64 := beq_iff_eq.mp hp
    rcases ws with _ | ⟨w0, _ | ⟨wa, _ | _⟩⟩ <;> try exact False.elim hwp
    dsimp only at hwp ⊢; exact hArrMkEmpty_retTy hw64 hwp
  · have hw64 : retTy.width = 64 := beq_iff_eq.mp hp
    rcases ws with _ | ⟨w0, _ | ⟨wa, _ | ⟨wv, _ | _⟩⟩⟩ <;> simp at hwp ⊢
    cases ha : wa.toBV64? with
    | none => simp [ha] at hwp
    | some arr => cases hv : wv.toBV64? with
      | none => simp [ha, hv] at hwp
      | some v =>
        simp only [ha, hv] at hwp ⊢
        rcases hwp with ⟨k, hk, a1, a2, hwf, a3, hif⟩
        refine ⟨k, hk, a1, a2, hwf, a3, ?_⟩
        by_cases hcap : (σ.objs[k]'hk).cap ≤ (σ.objs[k]'hk).fields.length ∧
            arrMaxCap ≤ (σ.objs[k]'hk).cap
        · rw [ite_eq_left hcap] at hif ⊢; exact hif
        · rw [ite_eq_right hcap] at hif ⊢
          exact ⟨hif.1, fun r st' ch' b1 b2 b3 b4 b5 b6 b7 b8 =>
            ⟨congrArg Ty.bits hw64.symm, hif.2 r st' ch' b1 b2 b3 b4 b5 b6 b7 b8⟩⟩
  · have hw64 : retTy.width = 64 := beq_iff_eq.mp hp
    rcases ws with _ | ⟨w0, _ | ⟨w1, _ | ⟨w2, _ | ⟨w3, _ | _⟩⟩⟩⟩ <;> simp at hwp ⊢
    cases h1 : w1.toBV64? with
    | none => simp [h1] at hwp
    | some _ => cases h2 : w2.toBV64? with
      | none => simp [h1, h2] at hwp
      | some _ => cases h3 : w3.toBV64? with
        | none => simp [h1, h2, h3] at hwp
        | some _ =>
          simp only [h1, h2, h3] at hwp ⊢
          rcases hwp with ⟨o, hm, ha', hc, hwf, hpre, hk⟩
          exact ⟨o, hm, ha', hc, hwf, hpre, congrArg Ty.bits hw64.symm, hk⟩
  · have hw64 : retTy.width = 64 := beq_iff_eq.mp hp
    rcases ws with _ | ⟨w0, _ | ⟨w1, _ | ⟨w2, _ | ⟨w3, _ | _⟩⟩⟩⟩ <;> simp at hwp ⊢
    cases h1 : w1.toBV64? with
    | none => simp [h1] at hwp
    | some _ => cases h2 : w2.toBV64? with
      | none => simp [h1, h2] at hwp
      | some _ => cases h3 : w3.toBV64? with
        | none => simp [h1, h2, h3] at hwp
        | some _ =>
          simp only [h1, h2, h3] at hwp ⊢
          rcases hwp with ⟨o, hm, ha', hc, hwf, hk⟩
          exact ⟨o, hm, ha', hc, hwf, congrArg Ty.bits hw64.symm, hk⟩
  · have hw64 : retTy.width = 64 := beq_iff_eq.mp hp
    rcases ws with _ | ⟨w0, _ | ⟨w1, _ | ⟨w2, _ | ⟨w3, _ | _⟩⟩⟩⟩ <;> simp at hwp ⊢
    exact ⟨hwp.1, hwp.1.trans (congrArg Ty.bits hw64.symm), hwp.2⟩
  · have hw64 : retTy.width = 64 := beq_iff_eq.mp hp
    rcases ws with _ | ⟨w0, _ | ⟨wa, _ | ⟨wi, _ | ⟨wv, _ | _⟩⟩⟩⟩ <;> simp at hwp ⊢
    cases ha : wa.toBV64? with
    | none => simp [ha] at hwp
    | some _ => cases hi : wi.toBV64? with
      | none => simp [ha, hi] at hwp
      | some _ => cases hv : wv.toBV64? with
        | none => simp [ha, hi, hv] at hwp
        | some _ => simp only [ha, hi, hv] at hwp ⊢; exact hArraySetWp_retTy hw64 hwp
  · have hw64 : retTy.width = 64 := beq_iff_eq.mp hp
    rcases ws with _ | ⟨w0, _ | ⟨wa, _ | ⟨wi, _ | ⟨wv, _ | ⟨w4, _ | _⟩⟩⟩⟩⟩ <;> simp at hwp ⊢
    cases ha : wa.toBV64? with
    | none => simp [ha] at hwp
    | some _ => cases hi : wi.toBV64? with
      | none => simp [ha, hi] at hwp
      | some _ => cases hv : wv.toBV64? with
        | none => simp [ha, hi, hv] at hwp
        | some _ => simp only [ha, hi, hv] at hwp ⊢; exact hArraySetWp_retTy hw64 hwp
  · cases hp

private theorem uintWidth?_tags {ty : String} {w : Nat} (h : uintWidth? ty = some w) :
    ty = "UInt8" ∨ ty = "UInt16" ∨ ty = "UInt32" ∨ ty = "UInt64" ∨ ty = "USize" := by
  unfold uintWidth? at h
  split at h <;> simp at h ⊢

private theorem hPrim_uint_case {rt : BitVec 64} {name ty op : String} {ws : List Word}
    {retTy : LcTy} {K : HPost} {X : HXPost} {σ : HState}
    (hsp : splitDot name = [ty, op])
    (hp : (match uintWidth? ty with
      | some w => isPhase1UintPrim w op ws.length retTy
      | none => false) = true)
    (hwp : HPrim.wp rt name ws K X σ) :
    HPrim.wp rt name ws (fun r σ' => r.1 = retTy.toTTy ∧ K r σ') X σ := by
  cases hu : uintWidth? ty with
  | none => rw [hu] at hp; cases hp
  | some w =>
    rcases uintWidth?_tags hu with rfl | rfl | rfl | rfl | rfl
    all_goals
      dsimp only [uintWidth?] at hu
      cases hu
      unfold HPrim.wp at hwp ⊢
      rw [hsp] at hwp ⊢
      dsimp only [uintWidth?] at hp hwp ⊢
      exact hUintPrimWp_retTy hp hwp

theorem hPrim_wp_retTy {rt : BitVec 64} {name : String} {ws : List Word} {retTy : LcTy}
    {K : HPost} {X : HXPost} {σ : HState}
    (hp : isPhase1Prim name ws.length retTy = true)
    (hwp : HPrim.wp rt name ws K X σ) :
    HPrim.wp rt name ws (fun r σ' => r.1 = retTy.toTTy ∧ K r σ') X σ := by
  have hwp0 := hwp
  unfold isPhase1Prim at hp
  unfold HPrim.wp at hwp ⊢
  generalize hsp : splitDot name = parts at hp
  split at hp
  · rw [hsp] at hwp; dsimp only at hwp ⊢; exact hNatPrimWp_retTy hp hwp
  · rw [hsp] at hwp; dsimp only at hwp ⊢; exact hArrayPrimWp_retTy hp hwp
  · rw [hsp] at hwp; dsimp only at hwp ⊢; exact hStringPrimWp_retTy hp hwp
  · rw [hsp] at hwp; dsimp only at hwp ⊢; exact hByteArrayPrimWp_retTy hp hwp
  · rw [hsp] at hwp; dsimp only at hwp ⊢; exact ⟨congrArg Ty.bits (beq_iff_eq.mp hp).symm, hwp⟩
  · rw [hsp] at hwp; dsimp only at hwp ⊢
    have hw64 : retTy.width = 64 := by
      simp only [Bool.and_eq_true] at hp
      exact beq_iff_eq.mp hp.2
    rcases ws with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> try exact False.elim hwp
    · dsimp only [Option.bind] at hwp ⊢
      cases ha : a.toBV64? with
      | none => simp [ha] at hwp
      | some x =>
        simp only [ha] at hwp ⊢
        by_cases hsc : (x &&& 1#64) ≠ 0#64
        · rw [ite_eq_left hsc] at hwp ⊢; exact ⟨congrArg Ty.bits hw64.symm, hwp⟩
        · rw [ite_eq_right hsc] at hwp ⊢
          rcases hwp with ⟨o, hm, ha', hwf, hk⟩
          exact ⟨o, hm, ha', hwf, congrArg Ty.bits hw64.symm, hk⟩
    · dsimp only [Option.bind] at hwp ⊢
      cases hb : b.toBV64? with
      | none => simp [hb] at hwp
      | some x =>
        simp only [hb] at hwp ⊢
        by_cases hsc : (x &&& 1#64) ≠ 0#64
        · rw [ite_eq_left hsc] at hwp ⊢; exact ⟨congrArg Ty.bits hw64.symm, hwp⟩
        · rw [ite_eq_right hsc] at hwp ⊢
          rcases hwp with ⟨o, hm, ha', hwf, hk⟩
          exact ⟨o, hm, ha', hwf, congrArg Ty.bits hw64.symm, hk⟩
  · rw [← hsp]
    change HPrim.wp rt name ws (fun r σ' => r.1 = retTy.toTTy ∧ K r σ') X σ
    exact hPrim_uint_case hsp hp hwp0
  · cases hp

end LeanQbe.T.LeanLCNF.Sem
