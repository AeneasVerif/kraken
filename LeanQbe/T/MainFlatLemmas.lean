module

public import LeanQbe.T.MainFlat
public import LeanQbe.T.Main
import LeanQbe.T.FlatDirectLemmas
import LeanQbe.T.PassFlatKit
import LeanQbe.T.LegalFlat
import LeanQbe.T.RegaFlatLemmas
import LeanQbe.T.OptLemmas
import LeanQbe.T.LegalLemmas
import LeanQbe.T.OptFlatValueLemmas
import LeanQbe.T.OptFlatMemLemmas
import LeanQbe.T.OptFlatCfgLemmas
import LeanQbe.T.OptFlatAddrRangeLemmas
import LeanQbe.T.OptFlatPathCondLemmas
import LeanQbe.T.FoldLemmas
import LeanQbe.T.CopyLemmas
import LeanQbe.T.DceParamLemmas
import LeanQbe.T.PeelLemmas
import LeanQbe.T.SimplifyGroupPlanLemmas
import LeanQbe.T.LicmLemmas
import LeanQbe.T.LoopRotateLemmas
import LeanQbe.T.CondThreadOptLemmas
import LeanQbe.T.TailDupLemmas
import LeanQbe.T.ZeroPeelLemmas

/-!
# Simulation Proofs for `MainFlat` (`compileModule_of_compileModuleFlat`)

Establishes exact `=` correspondence (`std3` axioms only) between every pass and driver entry
point in `LeanQbe.T.MainFlat` and its PHOAS counterpart in `Opt` / `Main`:

* Generic `reifyFunc` / `Func.renorm` bridges (`wfCheck_reifyBridge`, `denoteFunc_reifyBridge`)
* Direct `TFlat` pass simulation: `assumeElimFlat_eq`, `mergeRetsFlat_eq`,
  `simplifyGroupFastFlat_eq`, `peelFastFlat_eq`, `licmFlat_eq`, `loopRotateFlat_eq`
* Staged mid-end simulation (`OptFlatValue` + `OptFlatMem` + `OptFlatCfg`): `earlyOptFlat_toFn`,
  `midStageFlat_toFn`
* End-to-end compilation parity: `compileFlatFn_eq_compileFn`, `compileModule_of_compileModuleFlat`
-/

set_option autoImplicit false

namespace LeanQbe.T

/-! ## Private `List` / `pushTypes` / `pushTup` Utilities -/

private theorem listGet?_append_left {α : Type} :
    (l₁ l₂ : List α) → (i : Nat) → i < l₁.length →
    listGet? (l₁ ++ l₂) i = listGet? l₁ i
  | [], _, _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, _, 0, _ => rfl
  | _ :: l₁, l₂, i + 1, h => by
    dsimp only [List.cons_append, listGet?]
    exact listGet?_append_left l₁ l₂ i (Nat.succ_lt_succ_iff.mp h)

private theorem listGet?_append_right {α : Type} :
    (l₁ l₂ : List α) → (k : Nat) →
    listGet? (l₁ ++ l₂) (k + l₁.length) = listGet? l₂ k
  | [], _, _ => rfl
  | _ :: l₁, l₂, k => by
    rw [List.length_cons, ← Nat.add_assoc]
    exact listGet?_append_right l₁ l₂ k

private theorem listGet?_append_self {α : Type} (l₁ : List α) (x : α) (l₂ : List α) :
    listGet? (l₁ ++ x :: l₂) l₁.length = some x := by
  have h := listGet?_append_right l₁ (x :: l₂) 0
  rw [Nat.zero_add] at h
  exact h

private theorem listGet?_lt_length {α : Type} :
    (l : List α) → {i : Nat} → {x : α} → listGet? l i = some x → i < l.length
  | [], _, _, h => nomatch h
  | _ :: _, 0, _, _ => Nat.zero_lt_succ _
  | _ :: xs, _ + 1, _, h => Nat.succ_lt_succ (listGet?_lt_length xs h)

private theorem listGet?_map {α β : Type} (f : α → β) :
    (l : List α) → (i : Nat) → listGet? (l.map f) i = (listGet? l i).map f
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: xs, i + 1 => listGet?_map f xs i

private theorem pushTup_append_right {α : Type} {f : α → Type} :
    {ts : List α} → (xs : Tup f ts) →
    (ls suf : List ((a : α) × f a)) →
    pushTup xs (ls ++ suf) = pushTup xs ls ++ suf
  | [], (), _, _ => rfl
  | _ :: _, (_, xs), _, suf => by
    dsimp only [pushTup]
    rw [← List.cons_append]
    exact pushTup_append_right xs _ suf

private def tupRevList {α : Type} {f : α → Type} :
    {ts : List α} → Tup f ts → List ((a : α) × f a)
  | [], () => []
  | a :: _, (x, xs) => tupRevList xs ++ [⟨a, x⟩]

private theorem tupRevList_length {α : Type} {f : α → Type} :
    {ts : List α} → (xs : Tup f ts) → (tupRevList xs).length = ts.length
  | [], () => rfl
  | _ :: _, (_, xs) => by
    dsimp only [tupRevList]
    rw [List.length_append, List.length_cons, List.length_nil, tupRevList_length xs]
    rfl

private theorem pushTup_eq_tupRevList_append {α : Type} {f : α → Type} :
    {ts : List α} → (xs : Tup f ts) → (acc : List ((a : α) × f a)) →
    pushTup xs acc = tupRevList xs ++ acc
  | [], (), _ => rfl
  | a :: _, (x, xs), acc => by
    dsimp only [pushTup, tupRevList]
    rw [pushTup_eq_tupRevList_append xs (⟨a, x⟩ :: acc), List.append_assoc]
    rfl

private theorem ctxTypes_pushTup_rev {α : Type} {f : α → Type} :
    {ts : List α} → (xs : Tup f ts) → {Γ : List α} → {vs : List ((a : α) × f a)} →
    CtxTypes Γ vs → CtxTypes (pushTypes ts Γ) (pushTup xs vs)
  | [], (), _, _, h => h
  | _ :: _, (_, xs), _, _, h => ctxTypes_pushTup_rev xs (.cons h)

private theorem checkArg_eq_true_var {Γ : List Ty} {t : Ty} {idx : Nat}
    (h : listGet? Γ idx = some t) : checkArg Γ t (.var idx) = true :=
  checkArg_eq_true_iff.mpr h

private theorem checkJump_eq_true_of {Δ : List (List Ty)} {ts : List Ty} {j : Nat}
    (h : listGet? Δ j = some ts) :
    (match listGet? Δ j with
     | some ts' => match listTyDecEq ts' ts with | isTrue _ => true | isFalse _ => false
     | none => false) = true :=
  checkJump_eq_true_iff.mpr h

/-! ## Private `assumeElim` Proofs -/

private theorem denote_isHlt_of_wf {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    {Γ : List Ty} {Δ : List (List Ty)}
    {vs : List ((t : Ty) × V t)} {ls : List ((ts : List Ty) × L ts)}
    (hΓ : CtxTypes Γ vs) (hΔ : CtxTypes Δ ls) :
    (tf : TFlat rs) → tf.wfCheck Γ Δ = true →
    (denote V L tf vs ls).isHlt = tf.isHlt
  | .let_ op k, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨args', ha⟩ := Option.isSome_iff_exists.1 (denoteArgs_isSome_of_checkArgs hΓ hwf.1)
    dsimp only [denote]; rw [ha]; rfl
  | .load t a k, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨a', ha⟩ := Option.isSome_iff_exists.1 (denoteArg_isSome_of_checkArg hΓ hwf.1)
    dsimp only [denote]; rw [ha]; rfl
  | .store v a k, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨v', hv⟩ := Option.isSome_iff_exists.1 (denoteArg_isSome_of_checkArg hΓ hwf.1.1)
    obtain ⟨a', ha⟩ := Option.isSome_iff_exists.1 (denoteArg_isSome_of_checkArg hΓ hwf.1.2)
    dsimp only [denote]; rw [hv, ha]; rfl
  | .call f bs args k, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨args', ha⟩ := Option.isSome_iff_exists.1 (denoteArgs_isSome_of_checkArgs hΓ hwf.1)
    dsimp only [denote]; rw [ha]; rfl
  | .jnz c t e, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨c', hc⟩ := Option.isSome_iff_exists.1 (denoteArg_isSome_of_checkArg hΓ hwf.1.1)
    dsimp only [denote]; rw [hc]; rfl
  | .jump (ts := ts) j args, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨j', hj⟩ := Option.isSome_iff_exists.1 (lookupL_isSome_of_check hΔ hwf.1)
    obtain ⟨args', ha⟩ := Option.isSome_iff_exists.1 (denoteArgs_isSome_of_checkArgs hΓ hwf.2)
    dsimp only [denote]; rw [hj, ha]; rfl
  | .ret vs', hwf => by
    obtain ⟨vs'', hv⟩ := Option.isSome_iff_exists.1 (denoteArgs_isSome_of_checkArgs hΓ hwf)
    dsimp only [denote]; rw [hv]; rfl
  | .exit f args, hwf => by
    obtain ⟨args', ha⟩ := Option.isSome_iff_exists.1 (denoteArgs_isSome_of_checkArgs hΓ hwf)
    dsimp only [denote]; rw [ha]; rfl
  | .hlt, _ => rfl
  | .group bodies k, _ => rfl

mutual
private theorem assumeElim_wfCheckAux {rs : List Ty} :
    (tf : TFlat rs) → {Γ : List Ty} → {Δ : List (List Ty)} →
    tf.wfCheck Γ Δ = true → tf.assumeElim.wfCheck Γ Δ = true
  | .let_ _ k, _, _, hwf => by
    dsimp only [TFlat.wfCheck, TFlat.assumeElim] at hwf ⊢
    simp only [Bool.and_eq_true] at hwf ⊢
    exact ⟨hwf.1, assumeElim_wfCheckAux k hwf.2⟩
  | .load _ _ k, _, _, hwf => by
    dsimp only [TFlat.wfCheck, TFlat.assumeElim] at hwf ⊢
    simp only [Bool.and_eq_true] at hwf ⊢
    exact ⟨hwf.1, assumeElim_wfCheckAux k hwf.2⟩
  | .store _ _ k, _, _, hwf => by
    dsimp only [TFlat.wfCheck, TFlat.assumeElim] at hwf ⊢
    simp only [Bool.and_eq_true] at hwf ⊢
    exact ⟨hwf.1, assumeElim_wfCheckAux k hwf.2⟩
  | .call _ _ _ k, _, _, hwf => by
    dsimp only [TFlat.wfCheck, TFlat.assumeElim] at hwf ⊢
    simp only [Bool.and_eq_true] at hwf ⊢
    exact ⟨hwf.1, assumeElim_wfCheckAux k hwf.2⟩
  | .jnz c t e, Γ, Δ, hwf => by
    dsimp only [TFlat.wfCheck, TFlat.assumeElim, TFlat.mkJnzAssume] at hwf ⊢
    simp only [Bool.and_eq_true] at hwf
    have ht := assumeElim_wfCheckAux t hwf.1.2
    have he := assumeElim_wfCheckAux e hwf.2
    by_cases hhe : e.assumeElim.isHlt = true
    · simp only [hhe, ↓reduceIte]; exact ht
    · by_cases hht : t.assumeElim.isHlt = true
      · simp only [hhe, hht, Bool.false_eq_true, ↓reduceIte]; exact he
      · simp only [hhe, hht, Bool.false_eq_true, ↓reduceIte, TFlat.wfCheck, Bool.and_eq_true]
        exact ⟨⟨hwf.1.1, ht⟩, he⟩
  | .jump _ _, _, _, hwf => hwf
  | .ret _, _, _, hwf => hwf
  | .exit _ _, _, _, hwf => hwf
  | .hlt, _, _, hwf => hwf
  | .group bodies k, _, _, hwf => by
    dsimp only [TFlat.wfCheck, TFlat.assumeElim] at hwf ⊢
    simp only [Bool.and_eq_true] at hwf ⊢
    exact ⟨assumeElimB_wfCheckAux bodies hwf.1, assumeElim_wfCheckAux k hwf.2⟩

private theorem assumeElimB_wfCheckAux {rs : List Ty} :
    {sig : List (List Ty)} → (tb : TBlocks rs sig) →
    {Γ : List Ty} → {Δ : List (List Ty)} →
    tb.wfCheck Γ Δ = true → tb.assumeElim.wfCheck Γ Δ = true
  | _, .nil, _, _, hwf => hwf
  | _, .cons b bs, _, _, hwf => by
    dsimp only [TBlocks.wfCheck, TBlocks.assumeElim] at hwf ⊢
    simp only [Bool.and_eq_true] at hwf ⊢
    exact ⟨assumeElim_wfCheckAux b hwf.1, assumeElimB_wfCheckAux bs hwf.2⟩
end

mutual
private theorem denote_assumeElim_eq {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    (tf : TFlat rs) → {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × V t)} → {ls : List ((ts : List Ty) × L ts)} →
    CtxTypes Γ vs → CtxTypes Δ ls → tf.wfCheck Γ Δ = true →
    denote V L tf.assumeElim vs ls = assumeElim (denote V L tf vs ls)
  | .let_ op k, _, _, vs, ls, hΓ, hΔ, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨args', ha⟩ := Option.isSome_iff_exists.1 (denoteArgs_isSome_of_checkArgs hΓ hwf.1)
    dsimp only [TFlat.assumeElim, denote, assumeElim]
    rw [ha]; dsimp only
    exact congrArg (Expr.let_ _) (funext fun xs =>
      denote_assumeElim_eq k (ctxTypes_pushTup_rev xs hΓ) hΔ hwf.2)
  | .load t a k, _, _, vs, ls, hΓ, hΔ, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨a', ha⟩ := Option.isSome_iff_exists.1 (denoteArg_isSome_of_checkArg hΓ hwf.1)
    dsimp only [TFlat.assumeElim, denote, assumeElim]
    rw [ha]; dsimp only
    exact congrArg (Expr.load t a') (funext fun v =>
      denote_assumeElim_eq k (.cons hΓ) hΔ hwf.2)
  | .store v a k, _, _, vs, ls, hΓ, hΔ, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨v', hv⟩ := Option.isSome_iff_exists.1 (denoteArg_isSome_of_checkArg hΓ hwf.1.1)
    obtain ⟨a', ha⟩ := Option.isSome_iff_exists.1 (denoteArg_isSome_of_checkArg hΓ hwf.1.2)
    dsimp only [TFlat.assumeElim, denote, assumeElim]
    rw [hv, ha]; dsimp only
    exact congrArg (Expr.store v' a') (denote_assumeElim_eq k hΓ hΔ hwf.2)
  | .call f bs args k, _, _, vs, ls, hΓ, hΔ, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨args', ha⟩ := Option.isSome_iff_exists.1 (denoteArgs_isSome_of_checkArgs hΓ hwf.1)
    dsimp only [TFlat.assumeElim, denote, assumeElim]
    rw [ha]; dsimp only
    exact congrArg (Expr.call f args') (funext fun xs =>
      denote_assumeElim_eq k (ctxTypes_pushTup_rev xs hΓ) hΔ hwf.2)
  | .jnz c t e, _, _, vs, ls, hΓ, hΔ, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨c', hc⟩ := Option.isSome_iff_exists.1 (denoteArg_isSome_of_checkArg hΓ hwf.1.1)
    have htw := assumeElim_wfCheckAux t hwf.1.2
    have hew := assumeElim_wfCheckAux e hwf.2
    have iht := denote_assumeElim_eq t hΓ hΔ hwf.1.2
    have ihe := denote_assumeElim_eq e hΓ hΔ hwf.2
    have hth : (assumeElim (denote V L t vs ls)).isHlt = t.assumeElim.isHlt := by
      rw [← iht]; exact denote_isHlt_of_wf hΓ hΔ t.assumeElim htw
    have heh : (assumeElim (denote V L e vs ls)).isHlt = e.assumeElim.isHlt := by
      rw [← ihe]; exact denote_isHlt_of_wf hΓ hΔ e.assumeElim hew
    dsimp only [TFlat.assumeElim, TFlat.mkJnzAssume, denote]
    rw [hc]; dsimp only
    unfold assumeElim
    dsimp only [mkJnzAssume]
    cases hhe : e.assumeElim.isHlt with
    | true =>
      have hhe' : (assumeElim (denote V L e vs ls)).isHlt = true := heh.trans hhe
      simp only [hhe', ↓reduceIte, iht]
    | false =>
      have hhe' : (assumeElim (denote V L e vs ls)).isHlt = false := heh.trans hhe
      cases hht : t.assumeElim.isHlt with
      | true =>
        have hht' : (assumeElim (denote V L t vs ls)).isHlt = true := hth.trans hht
        simp only [hhe', hht', Bool.false_eq_true, ↓reduceIte, ihe]
      | false =>
        have hht' : (assumeElim (denote V L t vs ls)).isHlt = false := hth.trans hht
        simp only [hhe', hht', Bool.false_eq_true, ↓reduceIte, denote, hc, iht, ihe]
  | .jump (ts := ts) j args, _, _, vs, ls, hΓ, hΔ, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨j', hj⟩ := Option.isSome_iff_exists.1 (lookupL_isSome_of_check hΔ hwf.1)
    obtain ⟨args', ha⟩ := Option.isSome_iff_exists.1 (denoteArgs_isSome_of_checkArgs hΓ hwf.2)
    dsimp only [TFlat.assumeElim, denote]; rw [hj, ha]; rfl
  | .ret vs', _, _, vs, _, hΓ, _, hwf => by
    obtain ⟨vs'', hv⟩ := Option.isSome_iff_exists.1 (denoteArgs_isSome_of_checkArgs hΓ hwf)
    dsimp only [TFlat.assumeElim, denote]; rw [hv]; rfl
  | .exit f args, _, _, vs, _, hΓ, _, hwf => by
    obtain ⟨args', ha⟩ := Option.isSome_iff_exists.1 (denoteArgs_isSome_of_checkArgs hΓ hwf)
    dsimp only [TFlat.assumeElim, denote]; rw [ha]; rfl
  | .hlt, _, _, _, _, _, _, _ => rfl
  | .group bodies k, _, _, vs, ls, hΓ, hΔ, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [TFlat.assumeElim, denote, assumeElim]
    refine congr (congrArg Expr.group (funext fun Js => ?_)) (funext fun Js => ?_)
    · exact denoteB_assumeElim_eq bodies hΓ (ctxTypes_pushTup_rev Js hΔ) hwf.1
    · exact denote_assumeElim_eq k hΓ (ctxTypes_pushTup_rev Js hΔ) hwf.2

private theorem denoteB_assumeElim_eq {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    {sig : List (List Ty)} → (tb : TBlocks rs sig) →
    {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × V t)} → {ls : List ((ts : List Ty) × L ts)} →
    CtxTypes Γ vs → CtxTypes Δ ls → tb.wfCheck Γ Δ = true →
    denoteB V L tb.assumeElim vs ls = assumeElimB (denoteB V L tb vs ls)
  | _, .nil, _, _, _, _, _, _, _ => rfl
  | _, .cons b bs, _, _, vs, ls, hΓ, hΔ, hwf => by
    dsimp only [TBlocks.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [TBlocks.assumeElim, denoteB, assumeElimB]
    refine congr (congrArg Blocks.cons (funext fun xs => ?_))
      (denoteB_assumeElim_eq bs hΓ hΔ hwf.2)
    exact denote_assumeElim_eq b (ctxTypes_pushTup_rev xs hΓ) hΔ hwf.1
end

/-! ## Private `mergeRets` Proofs -/

private theorem checkArgs_retIdxs_gen :
    (ts suf : List Ty) → checkArgs (ts.reverse ++ suf) (retIdxs ts) = true
  | [], _ => rfl
  | t :: ts, suf => by
    dsimp only [retIdxs, checkArgs]
    rw [List.reverse_cons, List.append_assoc, Bool.and_eq_true]
    refine ⟨checkArg_eq_true_var ?_, checkArgs_retIdxs_gen ts (t :: suf)⟩
    simpa [List.length_reverse] using listGet?_append_self ts.reverse t suf

private theorem denoteArgs_retIdxs_gen {V : Ty → Type} :
    {ts : List Ty} → (xs : Tup V ts) → (suf : List ((u : Ty) × V u)) →
    denoteArgs (pushTup xs suf) (retIdxs ts) = some (toArgTup xs)
  | [], (), _ => rfl
  | t :: ts, (x, xs), suf => by
    dsimp only [pushTup, retIdxs, denoteArgs, toArgTup]
    have hhead : denoteArg (pushTup xs (⟨t, x⟩ :: suf)) (.var ts.length) = some (.var x) := by
      dsimp only [denoteArg, lookupV]
      rw [pushTup_eq_tupRevList_append, ← tupRevList_length xs, listGet?_append_self]
      dsimp only
      rw [PassFlatKit.castTy_self]
    rw [hhead, denoteArgs_retIdxs_gen xs (⟨t, x⟩ :: suf)]

mutual
private theorem wfCheck_mergeRetsAux {rs : List Ty} :
    (tf : TFlat rs) → {Γ : List Ty} → {Δ Δ' : List (List Ty)} → (exitIdx : Nat) →
    tf.wfCheck Γ Δ = true → listGet? Δ' exitIdx = some rs →
    (∀ i us, i < Δ.length → listGet? Δ i = some us → listGet? Δ' i = some us) →
    (tf.mergeRetsAux exitIdx).wfCheck Γ Δ' = true
  | .let_ _ k, _, _, _, _, hwf, hex, hpre => by
    dsimp only [TFlat.wfCheck, TFlat.mergeRetsAux] at hwf ⊢
    simp only [Bool.and_eq_true] at hwf ⊢
    exact ⟨hwf.1, wfCheck_mergeRetsAux k _ hwf.2 hex hpre⟩
  | .load _ _ k, _, _, _, _, hwf, hex, hpre => by
    dsimp only [TFlat.wfCheck, TFlat.mergeRetsAux] at hwf ⊢
    simp only [Bool.and_eq_true] at hwf ⊢
    exact ⟨hwf.1, wfCheck_mergeRetsAux k _ hwf.2 hex hpre⟩
  | .store _ _ k, _, _, _, _, hwf, hex, hpre => by
    dsimp only [TFlat.wfCheck, TFlat.mergeRetsAux] at hwf ⊢
    simp only [Bool.and_eq_true] at hwf ⊢
    exact ⟨hwf.1, wfCheck_mergeRetsAux k _ hwf.2 hex hpre⟩
  | .call _ _ _ k, _, _, _, _, hwf, hex, hpre => by
    dsimp only [TFlat.wfCheck, TFlat.mergeRetsAux] at hwf ⊢
    simp only [Bool.and_eq_true] at hwf ⊢
    exact ⟨hwf.1, wfCheck_mergeRetsAux k _ hwf.2 hex hpre⟩
  | .jnz _ t e, _, _, _, _, hwf, hex, hpre => by
    dsimp only [TFlat.wfCheck, TFlat.mergeRetsAux] at hwf ⊢
    simp only [Bool.and_eq_true] at hwf ⊢
    exact ⟨⟨hwf.1.1, wfCheck_mergeRetsAux t _ hwf.1.2 hex hpre⟩,
      wfCheck_mergeRetsAux e _ hwf.2 hex hpre⟩
  | .jump (ts := ts) j args, _, _, _, _, hwf, _, hpre => by
    dsimp only [TFlat.wfCheck, TFlat.mergeRetsAux] at hwf ⊢
    simp only [Bool.and_eq_true] at hwf ⊢
    have hget := checkJump_eq_true_iff.mp hwf.1
    exact ⟨checkJump_eq_true_of (hpre j ts (listGet?_lt_length _ hget) hget), hwf.2⟩
  | .ret vs, _, _, _, _, hwf, hex, _ => by
    dsimp only [TFlat.wfCheck, TFlat.mergeRetsAux] at hwf ⊢
    simp only [Bool.and_eq_true]
    exact ⟨checkJump_eq_true_of hex, hwf⟩
  | .exit _ _, _, _, _, _, hwf, _, _ => hwf
  | .hlt, _, _, _, _, hwf, _, _ => hwf
  | .group (sig := sig) bodies k, Γ, Δ, Δ', exitIdx, hwf, hex, hpre => by
    dsimp only [TFlat.wfCheck, TFlat.mergeRetsAux] at hwf ⊢
    simp only [Bool.and_eq_true] at hwf ⊢
    have hex' : listGet? (pushTypes sig Δ') (exitIdx + sig.length) = some rs := by
      rw [pushTypes_eq_reverse_append, ← List.length_reverse (as := sig)]
      exact (listGet?_append_right sig.reverse Δ' exitIdx).trans hex
    have hpre' : ∀ i us, i < (pushTypes sig Δ).length →
        listGet? (pushTypes sig Δ) i = some us → listGet? (pushTypes sig Δ') i = some us := by
      intro i us hlt hget
      rw [pushTypes_eq_reverse_append] at hlt hget ⊢
      by_cases hi : i < sig.length
      · have hir : i < sig.reverse.length := by simpa [List.length_reverse] using hi
        rw [listGet?_append_left sig.reverse Δ i hir] at hget
        rw [listGet?_append_left sig.reverse Δ' i hir]
        exact hget
      · have hlen : sig.reverse.length ≤ i := by
          simpa [List.length_reverse] using Nat.le_of_not_lt hi
        have hlt' : i - sig.reverse.length < Δ.length := by
          rw [List.length_append] at hlt; omega
        have hi_eq : i = (i - sig.reverse.length) + sig.reverse.length := by omega
        rw [hi_eq, listGet?_append_right] at hget ⊢
        exact hpre (i - sig.reverse.length) us hlt' hget
    exact ⟨wfCheckB_mergeRetsAux bodies (exitIdx + sig.length) hwf.1 hex' hpre',
      wfCheck_mergeRetsAux k (exitIdx + sig.length) hwf.2 hex' hpre'⟩

private theorem wfCheckB_mergeRetsAux {rs : List Ty} :
    {sig : List (List Ty)} → (tb : TBlocks rs sig) →
    {Γ : List Ty} → {Δ Δ' : List (List Ty)} → (exitIdx : Nat) →
    tb.wfCheck Γ Δ = true → listGet? Δ' exitIdx = some rs →
    (∀ i us, i < Δ.length → listGet? Δ i = some us → listGet? Δ' i = some us) →
    (tb.mergeRetsAux exitIdx).wfCheck Γ Δ' = true
  | _, .nil, _, _, _, _, hwf, _, _ => hwf
  | _, .cons b bs, _, _, _, exitIdx, hwf, hex, hpre => by
    dsimp only [TBlocks.wfCheck, TBlocks.mergeRetsAux] at hwf ⊢
    simp only [Bool.and_eq_true] at hwf ⊢
    exact ⟨wfCheck_mergeRetsAux b exitIdx hwf.1 hex hpre,
      wfCheckB_mergeRetsAux bs exitIdx hwf.2 hex hpre⟩
end

mutual
private theorem denote_mergeRetsAux_eq {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (exit_lbl : L rs) :
    (tf : TFlat rs) → {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × V t)} → {ls : List ((ts : List Ty) × L ts)} →
    CtxTypes Γ vs → CtxTypes Δ ls → tf.wfCheck Γ Δ = true →
    denote V L (tf.mergeRetsAux ls.length) vs (ls ++ [⟨rs, exit_lbl⟩]) =
      (denote V L tf vs ls).mergeRets exit_lbl
  | .let_ op k, _, _, vs, ls, hΓ, hΔ, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨args', ha⟩ := Option.isSome_iff_exists.1 (denoteArgs_isSome_of_checkArgs hΓ hwf.1)
    dsimp only [TFlat.mergeRetsAux, denote, Expr.mergeRets]
    rw [ha]; dsimp only
    exact congrArg (Expr.let_ _) (funext fun xs => by
      simpa only [pushTup_length] using
        denote_mergeRetsAux_eq exit_lbl k (ctxTypes_pushTup_rev xs hΓ) hΔ hwf.2)
  | .load t a k, _, _, vs, ls, hΓ, hΔ, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨a', ha⟩ := Option.isSome_iff_exists.1 (denoteArg_isSome_of_checkArg hΓ hwf.1)
    dsimp only [TFlat.mergeRetsAux, denote, Expr.mergeRets]
    rw [ha]; dsimp only
    exact congrArg (Expr.load t a') (funext fun v =>
      denote_mergeRetsAux_eq exit_lbl k (.cons hΓ) hΔ hwf.2)
  | .store v a k, _, _, vs, ls, hΓ, hΔ, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨v', hv⟩ := Option.isSome_iff_exists.1 (denoteArg_isSome_of_checkArg hΓ hwf.1.1)
    obtain ⟨a', ha⟩ := Option.isSome_iff_exists.1 (denoteArg_isSome_of_checkArg hΓ hwf.1.2)
    dsimp only [TFlat.mergeRetsAux, denote, Expr.mergeRets]
    rw [hv, ha]; dsimp only
    exact congrArg (Expr.store v' a') (denote_mergeRetsAux_eq exit_lbl k hΓ hΔ hwf.2)
  | .call f bs args k, _, _, vs, ls, hΓ, hΔ, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨args', ha⟩ := Option.isSome_iff_exists.1 (denoteArgs_isSome_of_checkArgs hΓ hwf.1)
    dsimp only [TFlat.mergeRetsAux, denote, Expr.mergeRets]
    rw [ha]; dsimp only
    exact congrArg (Expr.call f args') (funext fun xs =>
      denote_mergeRetsAux_eq exit_lbl k (ctxTypes_pushTup_rev xs hΓ) hΔ hwf.2)
  | .jnz c t e, _, _, vs, ls, hΓ, hΔ, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨c', hc⟩ := Option.isSome_iff_exists.1 (denoteArg_isSome_of_checkArg hΓ hwf.1.1)
    dsimp only [TFlat.mergeRetsAux, denote]
    rw [hc]; dsimp only
    unfold Expr.mergeRets
    rw [denote_mergeRetsAux_eq exit_lbl t hΓ hΔ hwf.1.2,
      denote_mergeRetsAux_eq exit_lbl e hΓ hΔ hwf.2]
  | .jump (ts := ts) j args, _, _, vs, ls, hΓ, hΔ, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨l, hget, hlt⟩ := ctxTypes_listGet? hΔ (checkJump_eq_true_iff.mp hwf.1)
    have hlook₁ : lookupL (ls ++ [⟨rs, exit_lbl⟩]) ts j = some l := by
      dsimp only [lookupL]
      rw [listGet?_append_left ls _ j hlt, hget]
      dsimp only; rw [PassFlatKit.castListTy_self]
    have hlook₂ : lookupL ls ts j = some l := by
      dsimp only [lookupL]; rw [hget]; dsimp only; rw [PassFlatKit.castListTy_self]
    obtain ⟨args', ha⟩ := Option.isSome_iff_exists.1 (denoteArgs_isSome_of_checkArgs hΓ hwf.2)
    dsimp only [TFlat.mergeRetsAux, denote]
    rw [hlook₁, hlook₂, ha]; rfl
  | .ret vs', _, _, vs, ls, hΓ, _, hwf => by
    obtain ⟨vs'', hv⟩ := Option.isSome_iff_exists.1 (denoteArgs_isSome_of_checkArgs hΓ hwf)
    have hlook : lookupL (ls ++ [⟨rs, exit_lbl⟩]) rs ls.length = some exit_lbl := by
      dsimp only [lookupL]
      rw [listGet?_append_self]
      dsimp only; rw [PassFlatKit.castListTy_self]
    dsimp only [TFlat.mergeRetsAux, denote]
    rw [hlook, hv]; rfl
  | .exit f args, _, _, vs, _, hΓ, _, hwf => by
    obtain ⟨args', ha⟩ := Option.isSome_iff_exists.1 (denoteArgs_isSome_of_checkArgs hΓ hwf)
    dsimp only [TFlat.mergeRetsAux, denote]; rw [ha]; rfl
  | .hlt, _, _, _, _, _, _, _ => rfl
  | .group (sig := sig) bodies k, _, _, vs, ls, hΓ, hΔ, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [TFlat.mergeRetsAux, denote, Expr.mergeRets]
    refine congr (congrArg Expr.group (funext fun Js => ?_)) (funext fun Js => ?_)
    · rw [pushTup_append_right Js ls [⟨rs, exit_lbl⟩]]
      have hlen : (pushTup Js ls).length = ls.length + sig.length := by
        rw [pushTup_length, Nat.add_comm]
      rw [← hlen]
      exact denoteB_mergeRetsAux_eq exit_lbl bodies hΓ (ctxTypes_pushTup_rev Js hΔ) hwf.1
    · rw [pushTup_append_right Js ls [⟨rs, exit_lbl⟩]]
      have hlen : (pushTup Js ls).length = ls.length + sig.length := by
        rw [pushTup_length, Nat.add_comm]
      rw [← hlen]
      exact denote_mergeRetsAux_eq exit_lbl k hΓ (ctxTypes_pushTup_rev Js hΔ) hwf.2

private theorem denoteB_mergeRetsAux_eq {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (exit_lbl : L rs) :
    {sig : List (List Ty)} → (tb : TBlocks rs sig) →
    {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × V t)} → {ls : List ((ts : List Ty) × L ts)} →
    CtxTypes Γ vs → CtxTypes Δ ls → tb.wfCheck Γ Δ = true →
    denoteB V L (tb.mergeRetsAux ls.length) vs (ls ++ [⟨rs, exit_lbl⟩]) =
      (denoteB V L tb vs ls).mergeRets exit_lbl
  | _, .nil, _, _, _, _, _, _, _ => rfl
  | _, .cons b bs, _, _, vs, ls, hΓ, hΔ, hwf => by
    dsimp only [TBlocks.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [TBlocks.mergeRetsAux, denoteB, Blocks.mergeRets]
    refine congr (congrArg Blocks.cons (funext fun xs => ?_))
      (denoteB_mergeRetsAux_eq exit_lbl bs hΓ hΔ hwf.2)
    exact denote_mergeRetsAux_eq exit_lbl b (ctxTypes_pushTup_rev xs hΓ) hΔ hwf.1
end

/-! ## Public Pass-Level and End-to-End Simulation Theorems -/

public section

/-- Any relational-`Wf`-preserving PHOAS pass yields a `wfCheck`-valid reified `TFlat`. -/
theorem wfCheck_reifyBridge {as rs : List Ty} {f : Func as rs} (hf : f.Wf) :
    (reifyFunc f).wfCheck (pushTypes as []) [] = true :=
  PassFlatKit.reifyFunc_wfCheck hf

/-- Composing `denoteFunc ∘ reifyFunc ∘ P ∘ denoteFunc` equals `P ∘ denoteFunc` whenever `P`
preserves `Func.Wf`. -/
theorem denoteFunc_reifyBridge {as rs : List Ty} {P : Func as rs → Func as rs}
    (hP : ∀ {g : Func as rs}, g.Wf → (P g).Wf) (tf : TFlat rs) :
    denoteFunc (as := as) (reifyFunc (P (denoteFunc tf))) = P (denoteFunc (as := as) tf) :=
  Func.renorm_eq_self (hP (Func.wf_of_denote tf rfl))

private theorem reifyBridge_wfCheck {as rs : List Ty} {P : Func as rs → Func as rs}
    (hP : ∀ {g : Func as rs}, g.Wf → (P g).Wf) (tf : TFlat rs) :
    (reifyFunc (P (denoteFunc (as := as) tf))).wfCheck (pushTypes as []) [] = true :=
  wfCheck_reifyBridge (hP (Func.wf_of_denote tf rfl))

/-- `TFlat.assumeElim` preserves `wfCheck`. -/
theorem TFlat.wfCheck_assumeElim {rs : List Ty} {Γ : List Ty} {Δ : List (List Ty)}
    {tf : TFlat rs} (hwf : tf.wfCheck Γ Δ = true) :
    tf.assumeElim.wfCheck Γ Δ = true :=
  assumeElim_wfCheckAux tf hwf

/-- `denoteFunc (assumeElimFlat tf) = Func.assumeElim (denoteFunc tf)` under `wfCheck = true`. -/
theorem denoteFunc_assumeElimFlat {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    denoteFunc (as := as) (assumeElimFlat tf) = Func.assumeElim (denoteFunc (as := as) tf) := by
  funext V L xs
  dsimp only [assumeElimFlat, Func.assumeElim, denoteFunc]
  exact denote_assumeElim_eq tf (ctxTypes_pushTup_rev xs .nil) .nil hwf

/-- `assumeElimFlat tf = reifyFunc (Func.assumeElim (denoteFunc tf))` under `wfCheck = true`. -/
theorem assumeElimFlat_eq {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    assumeElimFlat tf = reifyFunc (Func.assumeElim (denoteFunc (as := as) tf)) := by
  rw [← denoteFunc_assumeElimFlat tf hwf]
  exact (reifyFunc_denoteFunc_eq (assumeElimFlat tf) (TFlat.wfCheck_assumeElim hwf)).symm

/-- `TFlat.mergeRets` preserves `wfCheck`. -/
theorem TFlat.wfCheck_mergeRets {rs : List Ty} {Γ : List Ty} {tf : TFlat rs}
    (hwf : tf.wfCheck Γ [] = true) :
    tf.mergeRets.wfCheck Γ [] = true := by
  dsimp only [TFlat.mergeRets]
  by_cases hc : tflatRets tf ≥ 2
  · simp only [hc, ↓reduceIte, TFlat.wfCheck, TBlocks.wfCheck, Bool.and_eq_true, Bool.and_true]
    refine ⟨?_, wfCheck_mergeRetsAux tf 0 hwf rfl (fun _ _ h => absurd h (Nat.not_lt_zero _))⟩
    rw [pushTypes_eq_reverse_append]
    exact checkArgs_retIdxs_gen rs Γ
  · simp only [hc, ↓reduceIte]; exact hwf

/-- `denoteFunc (mergeRetsFlat tf) = Func.mergeRets (denoteFunc tf)` under `wfCheck = true`. -/
theorem denoteFunc_mergeRetsFlat {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    denoteFunc (as := as) (mergeRetsFlat tf) = Func.mergeRets (denoteFunc (as := as) tf) := by
  rw [Func.mergeRets_eq, reifyFunc_denoteFunc_eq tf hwf]
  dsimp only [mergeRetsFlat, TFlat.mergeRets]
  by_cases hc : tflatRets tf ≥ 2
  · simp only [hc, ↓reduceIte]
    funext V L xs
    dsimp only [denoteFunc, denote]
    refine congr (congrArg (Expr.group (sig := [rs])) ?_) ?_
    · funext Js
      cases Js with
      | mk j u =>
        cases u
        refine congrArg (fun b => Blocks.cons b Blocks.nil) (funext fun r_params => ?_)
        dsimp only [denote]
        rw [denoteArgs_retIdxs_gen]
    · funext (exit_lbl, ())
      dsimp only [pushTup]
      simpa using denote_mergeRetsAux_eq exit_lbl tf (ctxTypes_pushTup_rev xs .nil) .nil hwf
  · simp only [hc, ↓reduceIte]

/-- `mergeRetsFlat tf = reifyFunc (Func.mergeRets (denoteFunc tf))` under `wfCheck = true`. -/
theorem mergeRetsFlat_eq {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    mergeRetsFlat tf = reifyFunc (Func.mergeRets (denoteFunc (as := as) tf)) := by
  rw [← denoteFunc_mergeRetsFlat tf hwf]
  exact (reifyFunc_denoteFunc_eq (mergeRetsFlat tf) (TFlat.wfCheck_mergeRets hwf)).symm

/-- `simplifyGroupFastFlat` preserves `wfCheck`. -/
theorem simplifyGroupFastFlat_wfCheck {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    (simplifyGroupFastFlat as tf).wfCheck (pushTypes as []) [] = true := by
  dsimp only [simplifyGroupFastFlat]
  by_cases hsg : hasSimpGroup (tflatLoops tf ≤ 1) tf = true
  · simp only [hsg, ↓reduceIte]
    by_cases hch : (SgpImpl.buildPlan 0 tf).2.changed = true
    · simp only [hch, ↓reduceIte]
      exact wfCheck_reifyBridge (Func.simplifyGroupWithPlan_wf _ (Func.wf_of_denote tf rfl))
    · simp only [hch, Bool.false_eq_true, ↓reduceIte]; exact hwf
  · simp only [hsg, Bool.false_eq_true, ↓reduceIte]; exact hwf

/-- `denoteFunc (simplifyGroupFastFlat as tf) = Func.simplifyGroupFast (denoteFunc tf)` under
`wfCheck = true`. -/
theorem denoteFunc_simplifyGroupFastFlat {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    denoteFunc (as := as) (simplifyGroupFastFlat as tf) =
      Func.simplifyGroupFast (denoteFunc (as := as) tf) := by
  rw [Func.simplifyGroupFast_eq, reifyFunc_denoteFunc_eq tf hwf]
  dsimp only [simplifyGroupFastFlat, Func.simplifyGroupPlan]
  rw [reifyFunc_denoteFunc_eq tf hwf]
  by_cases hsg : hasSimpGroup (tflatLoops tf ≤ 1) tf = true
  · simp only [hsg, ↓reduceIte]
    by_cases hch : (SgpImpl.buildPlan 0 tf).2.changed = true
    · simp only [hch, ↓reduceIte]; rfl
    · simp only [hch, Bool.false_eq_true, ↓reduceIte]
      exact (Func.renorm_denoteFunc tf hwf).symm
  · simp only [hsg, Bool.false_eq_true, ↓reduceIte]

/-- `simplifyGroupFastFlat as tf = reifyFunc (Func.simplifyGroupFast (denoteFunc tf))`. -/
theorem simplifyGroupFastFlat_eq {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    simplifyGroupFastFlat as tf =
      reifyFunc (Func.simplifyGroupFast (denoteFunc (as := as) tf)) := by
  rw [← denoteFunc_simplifyGroupFastFlat tf hwf,
    reifyFunc_denoteFunc_eq _ (simplifyGroupFastFlat_wfCheck tf hwf)]

/-- `peelFastFlat` preserves `wfCheck`. -/
theorem peelFastFlat_wfCheck {as rs : List Ty} (tf : TFlat rs) (budget : Nat := 24)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    (peelFastFlat as tf budget).wfCheck (pushTypes as []) [] = true := by
  dsimp only [peelFastFlat]
  split
  · exact wfCheck_reifyBridge (Func.peel_wf (Func.wf_of_denote tf rfl) budget)
  · exact hwf

/-- `denoteFunc (peelFastFlat as tf budget) = Func.peelFast (denoteFunc tf) budget` under
`wfCheck = true`. -/
theorem denoteFunc_peelFastFlat {as rs : List Ty} (tf : TFlat rs) (budget : Nat := 24)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    denoteFunc (as := as) (peelFastFlat as tf budget) =
      Func.peelFast (denoteFunc (as := as) tf) budget := by
  rw [Func.peelFast_eq _ budget, reifyFunc_denoteFunc_eq tf hwf]
  dsimp only [peelFastFlat]
  split <;> rfl

/-- `peelFastFlat as tf budget = reifyFunc (Func.peelFast (denoteFunc tf) budget)`. -/
theorem peelFastFlat_eq {as rs : List Ty} (tf : TFlat rs) (budget : Nat := 24)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    peelFastFlat as tf budget = reifyFunc (Func.peelFast (denoteFunc (as := as) tf) budget) := by
  rw [← denoteFunc_peelFastFlat tf budget hwf,
    reifyFunc_denoteFunc_eq _ (peelFastFlat_wfCheck tf budget hwf)]

/-- `licmFlat` preserves `wfCheck`. -/
theorem licmFlat_wfCheck {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    (licmFlat as tf).wfCheck (pushTypes as []) [] = true := by
  dsimp only [licmFlat]
  split
  · exact hwf
  · exact wfCheck_reifyBridge (Func.licm_wf (Func.wf_of_denote tf rfl))

/-- `denoteFunc (licmFlat as tf) = Func.licm (denoteFunc tf)` under `wfCheck = true`. -/
theorem denoteFunc_licmFlat {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    denoteFunc (as := as) (licmFlat as tf) = Func.licm (denoteFunc (as := as) tf) := by
  dsimp only [licmFlat]
  by_cases hskip : (!(Licm.buildHoistPlan as.length tf).hasHoists &&
      !(Licm.buildRoPlan as.length tf).hasChanges) = true
  · simp only [hskip, ↓reduceIte]
    rw [Bool.and_eq_true, Bool.not_eq_true', Bool.not_eq_true'] at hskip
    have hf1 : (denoteFunc (as := as) tf).licmPure = denoteFunc (as := as) tf := by
      dsimp only [Func.licmPure]
      rw [reifyFunc_denoteFunc_eq tf hwf, hskip.1]
      simp only [Bool.false_eq_true, ↓reduceIte]
    dsimp only [Func.licm]
    rw [hf1, reifyFunc_denoteFunc_eq tf hwf, hskip.2]
    simp only [Bool.false_eq_true, ↓reduceIte]
  · simp only [hskip, Bool.false_eq_true, ↓reduceIte]
    exact denoteFunc_reifyBridge (fun hg => Func.licm_wf hg) tf

/-- `licmFlat as tf = reifyFunc (Func.licm (denoteFunc tf))` under `wfCheck = true`. -/
theorem licmFlat_eq {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    licmFlat as tf = reifyFunc (Func.licm (denoteFunc (as := as) tf)) := by
  rw [← denoteFunc_licmFlat tf hwf, reifyFunc_denoteFunc_eq _ (licmFlat_wfCheck tf hwf)]

/-- `loopRotateFlat` preserves `wfCheck`. -/
theorem loopRotateFlat_wfCheck {as rs : List Ty} (tf : TFlat rs)
    (cfg : LoopRotate.RotConfig := LoopRotate.defaultRotConfig)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    (loopRotateFlat as tf cfg).wfCheck (pushTypes as []) [] = true := by
  dsimp only [loopRotateFlat]
  split
  · rename_i hrot
    have hwfRot : (Func.loopRotate (denoteFunc (as := as) tf) cfg).Wf :=
      Func.loopRotate_wf (Func.wf_of_denote tf rfl) cfg
    dsimp only [Func.loopRotate] at hwfRot
    rw [reifyFunc_denoteFunc_eq tf hwf] at hwfRot
    simp only [hrot, ↓reduceIte] at hwfRot
    exact wfCheck_reifyBridge hwfRot
  · exact hwf

/-- `denoteFunc (loopRotateFlat as tf cfg) = Func.loopRotate (denoteFunc tf) cfg` under
`wfCheck = true`. -/
theorem denoteFunc_loopRotateFlat {as rs : List Ty} (tf : TFlat rs)
    (cfg : LoopRotate.RotConfig := LoopRotate.defaultRotConfig)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    denoteFunc (as := as) (loopRotateFlat as tf cfg) =
      Func.loopRotate (denoteFunc (as := as) tf) cfg := by
  dsimp only [loopRotateFlat, Func.loopRotate]
  rw [reifyFunc_denoteFunc_eq tf hwf]
  by_cases hrot : (LoopRotate.buildRotPlan (as := as) cfg tf).hasRot = true
  · simp only [hrot, ↓reduceIte]
    have hwfRot : (Func.loopRotate (denoteFunc (as := as) tf) cfg).Wf :=
      Func.loopRotate_wf (Func.wf_of_denote tf rfl) cfg
    dsimp only [Func.loopRotate] at hwfRot
    rw [reifyFunc_denoteFunc_eq tf hwf] at hwfRot
    simp only [hrot, ↓reduceIte] at hwfRot
    exact Func.renorm_eq_self hwfRot
  · simp only [hrot, Bool.false_eq_true, ↓reduceIte]

/-- `loopRotateFlat as tf cfg = reifyFunc (Func.loopRotate (denoteFunc tf) cfg)`. -/
theorem loopRotateFlat_eq {as rs : List Ty} (tf : TFlat rs)
    (cfg : LoopRotate.RotConfig := LoopRotate.defaultRotConfig)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    loopRotateFlat as tf cfg = reifyFunc (Func.loopRotate (denoteFunc (as := as) tf) cfg) := by
  rw [← denoteFunc_loopRotateFlat tf cfg hwf,
    reifyFunc_denoteFunc_eq _ (loopRotateFlat_wfCheck tf cfg hwf)]

private theorem wfCheck_zeroPeel24 {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    (TFlat.zeroPeelWith { peelBudget := 24 } tf).wfCheck (pushTypes as []) [] = true :=
  TFlat.wfCheck_zeroPeelWith { peelBudget := 24 } hwf

private theorem denoteFunc_zeroPeel24 {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    denoteFunc (as := as) (TFlat.zeroPeelWith { peelBudget := 24 } tf) =
      Func.zeroPeelWith { peelBudget := 24 } (denoteFunc (as := as) tf) := by
  dsimp only [TFlat.zeroPeelWith, Func.zeroPeelWith]
  rw [reifyFunc_denoteFunc_eq tf hwf, hwf, Bool.true_and]
  by_cases hsz : ZeroPeel.zpSize tf < ({ peelBudget := 24 } : ZeroPeelConfig).maxFnSize
  · simp [hsz]
  · simp [hsz]

/-- `addrRangeOptFlat` preserves `wfCheck`. -/
theorem addrRangeOptFlat_wfCheck (as : List Ty) {rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    (addrRangeOptFlat as tf).wfCheck (pushTypes as []) [] = true :=
  OptFlatAddrRange.addrRangeOptFlat_wfCheck tf hwf

/-- `denoteFunc (addrRangeOptFlat as tf) = Func.addrRangeOpt (denoteFunc tf)` under
`wfCheck = true`. -/
theorem denoteFunc_addrRangeOptFlat (as : List Ty) {rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    denoteFunc (as := as) (addrRangeOptFlat as tf) =
      Func.addrRangeOpt (denoteFunc (as := as) tf) :=
  OptFlatAddrRange.denoteFunc_addrRangeOptFlat tf hwf

/-- `addrRangeOptFlat as tf = reifyFunc (Func.addrRangeOpt (denoteFunc tf))` under
`wfCheck = true`. -/
theorem addrRangeOptFlat_eq (as : List Ty) {rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    addrRangeOptFlat as tf = reifyFunc (Func.addrRangeOpt (denoteFunc (as := as) tf)) :=
  OptFlatAddrRange.addrRangeOptFlat_eq tf hwf

/-- `pathCondOptFlat` preserves `wfCheck`. -/
theorem pathCondOptFlat_wfCheck (as : List Ty) {rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    (pathCondOptFlat as tf).wfCheck (pushTypes as []) [] = true :=
  OptFlatPathCond.pathCondOptFlat_wfCheck tf hwf

/-- `denoteFunc (pathCondOptFlat as tf) = Func.pathCondOpt (denoteFunc tf)` under
`wfCheck = true`. -/
theorem denoteFunc_pathCondOptFlat (as : List Ty) {rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    denoteFunc (as := as) (pathCondOptFlat as tf) =
      Func.pathCondOpt (denoteFunc (as := as) tf) :=
  OptFlatPathCond.denoteFunc_pathCondOptFlat tf hwf

/-- `pathCondOptFlat as tf = reifyFunc (Func.pathCondOpt (denoteFunc tf))` under
`wfCheck = true`. -/
theorem pathCondOptFlat_eq (as : List Ty) {rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    pathCondOptFlat as tf = reifyFunc (Func.pathCondOpt (denoteFunc (as := as) tf)) :=
  OptFlatPathCond.pathCondOptFlat_eq tf hwf

/-- `condThreadPassFlat` preserves `wfCheck`. -/
theorem condThreadPassFlat_wfCheck (as : List Ty) {rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    (condThreadPassFlat as tf).wfCheck (pushTypes as []) [] = true := by
  dsimp only [condThreadPassFlat]
  split
  · exact wfCheck_reifyBridge (Func.condThreadWithPlan_wf _ (Func.wf_of_denote tf rfl))
  · exact hwf

/-- `denoteFunc (condThreadPassFlat as tf) = Func.condThreadPass (denoteFunc tf)` under
`wfCheck = true`. -/
theorem denoteFunc_condThreadPassFlat (as : List Ty) {rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    denoteFunc (as := as) (condThreadPassFlat as tf) =
      Func.condThreadPass (denoteFunc (as := as) tf) := by
  dsimp only [condThreadPassFlat, Func.condThreadPass]
  rw [reifyFunc_denoteFunc_eq tf hwf]
  split
  · exact Func.renorm_eq_self (Func.condThreadWithPlan_wf _ (Func.wf_of_denote tf rfl))
  · rfl

/-- `condThreadPassFlat as tf = reifyFunc (Func.condThreadPass (denoteFunc tf))` under
`wfCheck = true`. -/
theorem condThreadPassFlat_eq (as : List Ty) {rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    condThreadPassFlat as tf = reifyFunc (Func.condThreadPass (denoteFunc (as := as) tf)) := by
  rw [← denoteFunc_condThreadPassFlat as tf hwf,
    reifyFunc_denoteFunc_eq _ (condThreadPassFlat_wfCheck as tf hwf)]

/-- `condThreadLateOptFlat` preserves `wfCheck`. -/
theorem condThreadLateOptFlat_wfCheck (as : List Ty) {rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    (condThreadLateOptFlat as tf).wfCheck (pushTypes as []) [] = true :=
  condThreadPassFlat_wfCheck as _ (pathCondOptFlat_wfCheck as tf hwf)

/-- `denoteFunc (condThreadLateOptFlat as tf) = Func.condThreadLateOpt (denoteFunc tf)` under
`wfCheck = true`. -/
theorem denoteFunc_condThreadLateOptFlat (as : List Ty) {rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    denoteFunc (as := as) (condThreadLateOptFlat as tf) =
      Func.condThreadLateOpt (denoteFunc (as := as) tf) := by
  dsimp only [condThreadLateOptFlat, Func.condThreadLateOpt, Func.condThreadOpt]
  have hwf1 := pathCondOptFlat_wfCheck as tf hwf
  rw [denoteFunc_condThreadPassFlat as _ hwf1, denoteFunc_pathCondOptFlat as tf hwf]
  exact (Func.renorm_eq_self (Func.condThreadPass_wf
    (Func.pathCondOpt_wf (Func.wf_of_denote tf rfl)))).symm

/-- `condThreadLateOptFlat as tf = reifyFunc (Func.condThreadLateOpt (denoteFunc tf))` under
`wfCheck = true`. -/
theorem condThreadLateOptFlat_eq (as : List Ty) {rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    condThreadLateOptFlat as tf =
      reifyFunc (Func.condThreadLateOpt (denoteFunc (as := as) tf)) := by
  rw [← denoteFunc_condThreadLateOptFlat as tf hwf,
    reifyFunc_denoteFunc_eq _ (condThreadLateOptFlat_wfCheck as tf hwf)]

/-- `tailDupFlat` preserves `wfCheck`. -/
theorem tailDupFlat_wfCheck (as : List Ty) {rs : List Ty} (tf : TFlat rs)
    (cfg : TailDup.TailDupConfig := {})
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    (tailDupFlat as tf cfg).wfCheck (pushTypes as []) [] = true := by
  dsimp only [tailDupFlat]
  split
  · exact reifyBridge_wfCheck (fun hg => Func.tailDup_wf hg cfg) tf
  · exact hwf

/-- `denoteFunc (tailDupFlat as tf cfg) = Func.tailDup (denoteFunc tf) cfg` under
`wfCheck = true`. -/
theorem denoteFunc_tailDupFlat (as : List Ty) {rs : List Ty} (tf : TFlat rs)
    (cfg : TailDup.TailDupConfig := {})
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    denoteFunc (as := as) (tailDupFlat as tf cfg) =
      Func.tailDup (denoteFunc (as := as) tf) cfg := by
  dsimp only [tailDupFlat]
  by_cases hch : (TailDup.buildPlan cfg 0 tf).2.changed = true
  · simp only [hch, ↓reduceIte]
    exact denoteFunc_reifyBridge (fun hg => Func.tailDup_wf hg cfg) tf
  · simp only [hch, Bool.false_eq_true, ↓reduceIte]
    cases hmax : cfg.maxIters with
    | zero =>
      dsimp only [Func.tailDup]; rw [hmax]; rfl
    | succ n =>
      dsimp only [Func.tailDup]; rw [hmax]
      simp only [Func.tailDupLoop, Func.tailDupOnce, reifyFunc_denoteFunc_eq tf hwf,
        hch, Bool.false_eq_true, ↓reduceIte]

/-- `tailDupFlat as tf cfg = reifyFunc (Func.tailDup (denoteFunc tf) cfg)` under
`wfCheck = true`. -/
theorem tailDupFlat_eq (as : List Ty) {rs : List Ty} (tf : TFlat rs)
    (cfg : TailDup.TailDupConfig := {})
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    tailDupFlat as tf cfg = reifyFunc (Func.tailDup (denoteFunc (as := as) tf) cfg) := by
  rw [← denoteFunc_tailDupFlat as tf cfg hwf,
    reifyFunc_denoteFunc_eq _ (tailDupFlat_wfCheck as tf cfg hwf)]

section PipelineProofs

attribute [local irreducible]
  OptFlatValue.foldFlat OptFlatValue.copyFlat OptFlatValue.canonFlat OptFlatValue.gvnFlat
  OptFlatMem.memLoadFlat OptFlatMem.assumeBitsFlat OptFlatMem.divConstFlat
  OptFlatCfg.dcePFlat OptFlatCfg.deadLoadElimFlat OptFlatCfg.ifOptFlat
  simplifyGroupFastFlat peelFastFlat licmFlat loopRotateFlat TFlat.zeroPeelWith
  legalFlat addrRangeOptFlat condThreadLateOptFlat tailDupFlat

/-- `earlyOptFlat` preserves `TFlatFn.wfCheck`. -/
theorem earlyOptFlat_wfCheck (f : TFlatFn) (_hwf : f.wfCheck = true) :
    (earlyOptFlat f).wfCheck = true := by
  let tf0a := OptFlatValue.foldFlat f.as f.body
  let tf0b := OptFlatValue.canonFlat f.as tf0a
  let tf0c := OptFlatValue.copyFlat f.as tf0b
  let tf0d := OptFlatValue.gvnFlat f.as tf0c
  let tf0e := OptFlatValue.copyFlat f.as tf0d
  let tf0 := OptFlatValue.foldFlat f.as tf0e
  let tf1 := OptFlatCfg.ifOptFlat false f.as tf0
  let tf2 := simplifyGroupFastFlat f.as tf1
  let tf3 := peelFastFlat f.as tf2 24
  let tf4 := TFlat.zeroPeelWith { peelBudget := 24 } tf3
  let tf5a := OptFlatValue.copyFlat f.as tf4
  let tf5b := OptFlatValue.foldFlat f.as tf5a
  have h1 := OptFlatValue.foldFlat_wfCheck f.body _hwf
  have h2 := OptFlatValue.canonFlat_wfCheck tf0a h1
  have h3 := OptFlatValue.copyFlat_wfCheck tf0b h2
  have h4 := OptFlatValue.gvnFlat_wfCheck tf0c h3
  have h5 := OptFlatValue.copyFlat_wfCheck tf0d h4
  have h6 := OptFlatValue.foldFlat_wfCheck tf0e h5
  have h7 := OptFlatCfg.ifOptFlat_wfCheck false tf0 h6
  have h8 := simplifyGroupFastFlat_wfCheck tf1 h7
  have h9 := peelFastFlat_wfCheck tf2 24 h8
  have h10 := wfCheck_zeroPeel24 tf3 h9
  have h11 := OptFlatValue.copyFlat_wfCheck tf4 h10
  have h12 := OptFlatValue.foldFlat_wfCheck tf5a h11
  exact OptFlatCfg.dcePFlat_wfCheck tf5b h12

/-- `(earlyOptFlat f).toFn = f.toFn.earlyOpt` whenever `f.wfCheck = true`. -/
theorem earlyOptFlat_toFn (f : TFlatFn) (_hwf : f.wfCheck = true) :
    (earlyOptFlat f).toFn = f.toFn.earlyOpt := by
  let tf0a := OptFlatValue.foldFlat f.as f.body
  let tf0b := OptFlatValue.canonFlat f.as tf0a
  let tf0c := OptFlatValue.copyFlat f.as tf0b
  let tf0d := OptFlatValue.gvnFlat f.as tf0c
  let tf0e := OptFlatValue.copyFlat f.as tf0d
  let tf0 := OptFlatValue.foldFlat f.as tf0e
  let tf1 := OptFlatCfg.ifOptFlat false f.as tf0
  let tf2 := simplifyGroupFastFlat f.as tf1
  let tf3 := peelFastFlat f.as tf2 24
  let tf4 := TFlat.zeroPeelWith { peelBudget := 24 } tf3
  let tf5a := OptFlatValue.copyFlat f.as tf4
  let tf5b := OptFlatValue.foldFlat f.as tf5a
  have h1 := OptFlatValue.foldFlat_wfCheck f.body _hwf
  have h2 := OptFlatValue.canonFlat_wfCheck tf0a h1
  have h3 := OptFlatValue.copyFlat_wfCheck tf0b h2
  have h4 := OptFlatValue.gvnFlat_wfCheck tf0c h3
  have h5 := OptFlatValue.copyFlat_wfCheck tf0d h4
  have h6 := OptFlatValue.foldFlat_wfCheck tf0e h5
  have h7 := OptFlatCfg.ifOptFlat_wfCheck false tf0 h6
  have h8 := simplifyGroupFastFlat_wfCheck tf1 h7
  have h9 := peelFastFlat_wfCheck tf2 24 h8
  have h10 := wfCheck_zeroPeel24 tf3 h9
  have h11 := OptFlatValue.copyFlat_wfCheck tf4 h10
  have h12 := OptFlatValue.foldFlat_wfCheck tf5a h11
  dsimp only [TFlatFn.toFn, Fn.earlyOpt, earlyOptFlat]
  rw [Func.earlyOpt_eq, Func.earlyCore_eq]
  refine congrArg (Fn.mk f.name f.as f.rs) ?_
  rw [OptFlatCfg.denoteFunc_dcePFlat tf5b h12, OptFlatValue.denoteFunc_foldFlat tf5a h11,
    OptFlatValue.denoteFunc_copyFlat tf4 h10, denoteFunc_zeroPeel24 tf3 h9,
    denoteFunc_peelFastFlat tf2 24 h8, denoteFunc_simplifyGroupFastFlat tf1 h7,
    OptFlatCfg.denoteFunc_ifOptFlat_false tf0 h6, OptFlatValue.denoteFunc_foldFlat tf0e h5,
    OptFlatValue.denoteFunc_copyFlat tf0d h4, OptFlatValue.denoteFunc_gvnFlat tf0c h3,
    OptFlatValue.denoteFunc_copyFlat tf0b h2, OptFlatValue.denoteFunc_canonFlat tf0a h1,
    OptFlatValue.denoteFunc_foldFlat f.body _hwf]
  exact (Func.renorm_eq_self (Func.dceP_wf (Func.fold_wf (Func.copy_wf
    (Func.zeroPeelWith_wf _ (Func.peelFast_wf _ 24)))))).symm

/-- `midStageFlat` preserves `TFlatFn.wfCheck`. -/
theorem midStageFlat_wfCheck (lt : LegalTarget) (ef : TFlatFn) (hwf : ef.wfCheck = true) :
    (midStageFlat lt ef).wfCheck = true := by
  let as' := lt.legalSig ef.as
  let tf0 := legalFlat lt (as := ef.as) ef.body
  let tf1a := OptFlatValue.foldFlat as' tf0
  let tf1b := OptFlatValue.canonFlat as' tf1a
  let tf1c := OptFlatMem.divConstFlat as' tf1b
  let tf1 := OptFlatValue.copyFlat as' tf1c
  let tf2a := OptFlatMem.memLoadFlat as' tf1
  let tf2b := OptFlatValue.gvnFlat as' tf2a
  let tf2c := OptFlatMem.assumeBitsFlat as' tf2b
  let tf2 := OptFlatValue.foldFlat as' tf2c
  let tf3a := OptFlatCfg.ifOptFlat true as' tf2
  let tf3b := simplifyGroupFastFlat as' tf3a
  let tf3c := OptFlatCfg.deadLoadElimFlat as' tf3b
  let tf3d := assumeElimFlat tf3c
  let tf3e := OptFlatValue.foldFlat as' tf3d
  let tf3f := addrRangeOptFlat as' tf3e
  let tf3 := OptFlatValue.gvnFlat as' tf3f
  let tf4a := licmFlat as' tf3
  let tf4b := OptFlatCfg.dcePFlat as' tf4a
  let tf4 := loopRotateFlat as' tf4b
  let tf5a := condThreadLateOptFlat as' tf4
  let tf5b := OptFlatValue.foldFlat as' tf5a
  let tf5c := OptFlatCfg.dcePFlat as' tf5b
  let tf5d := tailDupFlat as' tf5c
  have h0 : tf0.wfCheck (pushTypes as' []) [] = true := by
    dsimp only [tf0]
    rw [legalFlat_eq lt ef.body hwf]
    exact wfCheck_reifyBridge (Func.legal_wf lt (Func.wf_of_denote ef.body rfl))
  have h1a := OptFlatValue.foldFlat_wfCheck tf0 h0
  have h1b := OptFlatValue.canonFlat_wfCheck tf1a h1a
  have h1c := OptFlatMem.divConstFlat_wfCheck tf1b h1b
  have h1 := OptFlatValue.copyFlat_wfCheck tf1c h1c
  have h2a := OptFlatMem.memLoadFlat_wfCheck tf1 h1
  have h2b := OptFlatValue.gvnFlat_wfCheck tf2a h2a
  have h2c := OptFlatMem.assumeBitsFlat_wfCheck tf2b h2b
  have h2 := OptFlatValue.foldFlat_wfCheck tf2c h2c
  have h3a := OptFlatCfg.ifOptFlat_wfCheck true tf2 h2
  have h3b := simplifyGroupFastFlat_wfCheck tf3a h3a
  have h3c := OptFlatCfg.deadLoadElimFlat_wfCheck tf3b h3b
  have h3d := TFlat.wfCheck_assumeElim h3c
  have h3e := OptFlatValue.foldFlat_wfCheck tf3d h3d
  have h3f := addrRangeOptFlat_wfCheck as' tf3e h3e
  have h3 := OptFlatValue.gvnFlat_wfCheck tf3f h3f
  have h4a := licmFlat_wfCheck tf3 h3
  have h4b := OptFlatCfg.dcePFlat_wfCheck tf4a h4a
  have h4 := loopRotateFlat_wfCheck tf4b LoopRotate.defaultRotConfig h4b
  have h5a := condThreadLateOptFlat_wfCheck as' tf4 h4
  have h5b := OptFlatValue.foldFlat_wfCheck tf5a h5a
  have h5c := OptFlatCfg.dcePFlat_wfCheck tf5b h5b
  have h5d := tailDupFlat_wfCheck as' tf5c {} h5c
  dsimp only [midStageFlat, TFlatFn.wfCheck]
  exact TFlat.wfCheck_mergeRets h5d

/-- `(midStageFlat lt ef).toFn = Fn.midFromEarly lt ef.toFn` whenever `ef.wfCheck = true`. -/
theorem midStageFlat_toFn (lt : LegalTarget) (ef : TFlatFn) (hwf : ef.wfCheck = true) :
    (midStageFlat lt ef).toFn = Fn.midFromEarly lt ef.toFn := by
  let as' := lt.legalSig ef.as
  let tf0 := legalFlat lt (as := ef.as) ef.body
  let tf1a := OptFlatValue.foldFlat as' tf0
  let tf1b := OptFlatValue.canonFlat as' tf1a
  let tf1c := OptFlatMem.divConstFlat as' tf1b
  let tf1 := OptFlatValue.copyFlat as' tf1c
  let tf2a := OptFlatMem.memLoadFlat as' tf1
  let tf2b := OptFlatValue.gvnFlat as' tf2a
  let tf2c := OptFlatMem.assumeBitsFlat as' tf2b
  let tf2 := OptFlatValue.foldFlat as' tf2c
  let tf3a := OptFlatCfg.ifOptFlat true as' tf2
  let tf3b := simplifyGroupFastFlat as' tf3a
  let tf3c := OptFlatCfg.deadLoadElimFlat as' tf3b
  let tf3d := assumeElimFlat tf3c
  let tf3e := OptFlatValue.foldFlat as' tf3d
  let tf3f := addrRangeOptFlat as' tf3e
  let tf3 := OptFlatValue.gvnFlat as' tf3f
  let tf4a := licmFlat as' tf3
  let tf4b := OptFlatCfg.dcePFlat as' tf4a
  let tf4 := loopRotateFlat as' tf4b
  let tf5a := condThreadLateOptFlat as' tf4
  let tf5b := OptFlatValue.foldFlat as' tf5a
  let tf5c := OptFlatCfg.dcePFlat as' tf5b
  let tf5d := tailDupFlat as' tf5c
  have h0 : tf0.wfCheck (pushTypes as' []) [] = true := by
    dsimp only [tf0]
    rw [legalFlat_eq lt ef.body hwf]
    exact wfCheck_reifyBridge (Func.legal_wf lt (Func.wf_of_denote ef.body rfl))
  have h1a := OptFlatValue.foldFlat_wfCheck tf0 h0
  have h1b := OptFlatValue.canonFlat_wfCheck tf1a h1a
  have h1c := OptFlatMem.divConstFlat_wfCheck tf1b h1b
  have h1 := OptFlatValue.copyFlat_wfCheck tf1c h1c
  have h2a := OptFlatMem.memLoadFlat_wfCheck tf1 h1
  have h2b := OptFlatValue.gvnFlat_wfCheck tf2a h2a
  have h2c := OptFlatMem.assumeBitsFlat_wfCheck tf2b h2b
  have h2 := OptFlatValue.foldFlat_wfCheck tf2c h2c
  have h3a := OptFlatCfg.ifOptFlat_wfCheck true tf2 h2
  have h3b := simplifyGroupFastFlat_wfCheck tf3a h3a
  have h3c := OptFlatCfg.deadLoadElimFlat_wfCheck tf3b h3b
  have h3d := TFlat.wfCheck_assumeElim h3c
  have h3e := OptFlatValue.foldFlat_wfCheck tf3d h3d
  have h3f := addrRangeOptFlat_wfCheck as' tf3e h3e
  have h3 := OptFlatValue.gvnFlat_wfCheck tf3f h3f
  have h4a := licmFlat_wfCheck tf3 h3
  have h4b := OptFlatCfg.dcePFlat_wfCheck tf4a h4a
  have h4 := loopRotateFlat_wfCheck tf4b LoopRotate.defaultRotConfig h4b
  have h5a := condThreadLateOptFlat_wfCheck as' tf4 h4
  have h5b := OptFlatValue.foldFlat_wfCheck tf5a h5a
  have h5c := OptFlatCfg.dcePFlat_wfCheck tf5b h5b
  have h5d := tailDupFlat_wfCheck as' tf5c {} h5c
  have d0 : denoteFunc (as := as') tf0 = Func.legal lt (denoteFunc (as := ef.as) ef.body) := by
    dsimp only [tf0]
    rw [legalFlat_eq lt ef.body hwf]
    exact Func.renorm_eq_self (Func.legal_wf lt (Func.wf_of_denote ef.body rfl))
  dsimp only [TFlatFn.toFn, Fn.midFromEarly, midStageFlat]
  rw [Fn.midStage_eq]
  refine congrArg (Fn.mk ef.name as' (lt.legalSig ef.rs)) ?_
  dsimp only [TFlatFn.toFn]
  have hwfLeg : (Func.legal lt (denoteFunc (as := ef.as) ef.body)).Wf :=
    Func.legal_wf lt (Func.wf_of_denote (as := ef.as) ef.body rfl)
  have hwf1 := Func.lateCorePre_wf hwfLeg
  have hwf2 := Func.lateCorePost_wf hwf1
  have hwf3 := Func.lateCfgPre_wf hwf2
  have hwf4 := Func.lateLoopRotate_wf hwf3
  have hwf5 := Func.lateCondThread_wf hwf4
  rw [Func.renorm_eq_self hwf1, Func.renorm_eq_self hwf2, Func.renorm_eq_self hwf3,
    Func.renorm_eq_self hwf4, Func.renorm_eq_self hwf5]
  rw [Func.lateCondThread_eq, Func.lateLoopRotate_eq, Func.lateCfgPost_eq, Func.lateCfgPre_eq,
    Func.lateCorePost_eq, Func.lateCorePre_eq]
  change denoteFunc (as := as') (mergeRetsFlat tf5d) = _
  rw [denoteFunc_mergeRetsFlat tf5d h5d, denoteFunc_tailDupFlat as' tf5c {} h5c,
    OptFlatCfg.denoteFunc_dcePFlat tf5b h5b, OptFlatValue.denoteFunc_foldFlat tf5a h5a,
    denoteFunc_condThreadLateOptFlat as' tf4 h4,
    denoteFunc_loopRotateFlat tf4b LoopRotate.defaultRotConfig h4b,
    OptFlatCfg.denoteFunc_dcePFlat tf4a h4a, denoteFunc_licmFlat tf3 h3,
    OptFlatValue.denoteFunc_gvnFlat tf3f h3f, denoteFunc_addrRangeOptFlat as' tf3e h3e,
    OptFlatValue.denoteFunc_foldFlat tf3d h3d, denoteFunc_assumeElimFlat tf3c h3c,
    OptFlatCfg.denoteFunc_deadLoadElimFlat tf3b h3b,
    denoteFunc_simplifyGroupFastFlat tf3a h3a,
    OptFlatCfg.denoteFunc_ifOptFlat_true tf2 h2, OptFlatValue.denoteFunc_foldFlat tf2c h2c,
    OptFlatMem.denoteFunc_assumeBitsFlat tf2b h2b, OptFlatValue.denoteFunc_gvnFlat tf2a h2a,
    OptFlatMem.denoteFunc_memLoadFlat tf1 h1, OptFlatValue.denoteFunc_copyFlat tf1c h1c,
    OptFlatMem.denoteFunc_divConstFlat tf1b h1b, OptFlatValue.denoteFunc_canonFlat tf1a h1a,
    OptFlatValue.denoteFunc_foldFlat tf0 h0, d0]

end PipelineProofs

section EndToEnd

attribute [local irreducible] earlyOptFlat midStageFlat

/-- `compileFlatFn I lt h f = compileFn I lt h f.toFn` whenever `f.wfCheck = true`. -/
theorem compileFlatFn_eq_compileFn (I : Isa) (lt : LegalTarget) (h : I.Hints)
    (f : TFlatFn) (hwf : f.wfCheck = true) :
    compileFlatFn I lt h f = compileFn I lt h f.toFn := by
  dsimp only [compileFlatFn, compileFn, Fn.mid]
  rw [hwf]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  have heowf := earlyOptFlat_wfCheck f hwf
  have heoto := earlyOptFlat_toFn f hwf
  have hmwf := midStageFlat_wfCheck lt (earlyOptFlat f) heowf
  have hmto := midStageFlat_toFn lt (earlyOptFlat f) heowf
  rw [← heoto, ← hmto, TFlat.ext_eq_fn_ext _ hmwf]
  exact Rega.lowerFlatFn_eq_lowerFn I h (Fn.ext (midStageFlat lt (earlyOptFlat f)).toFn)
    (midStageFlat lt (earlyOptFlat f)) hmwf

/-- Any successful `compileModuleFlat` run implies the exact same output on `compileModule` over
`fs.map TFlatFn.toFn` (`std3` axioms only). -/
theorem compileModule_of_compileModuleFlat (I : Isa) (lt : LegalTarget) (raBytes : Nat) :
    ∀ (extCallees : List (SigEntry × Nat)) (exits : List Sym) (nX : Nat)
      (fs : List TFlatFn) (hs : List I.Hints)
      (code : List I.Directive) (bounds : List (Sym × Nat)),
      compileModuleFlat I lt raBytes extCallees exits nX fs hs = .ok (code, bounds) →
      compileModule I lt raBytes extCallees exits nX (fs.map TFlatFn.toFn) hs =
        .ok (code, bounds)
  | _, _, _, [], [], _, _, h => h
  | _, _, _, [], _ :: _, _, _, h => by
    dsimp only [compileModuleFlat] at h; cases h
  | _, _, _, _ :: _, [], _, _, h => by
    dsimp only [compileModuleFlat] at h; cases h
  | extCallees, exits, nX, f :: fs, h :: hs, code, bounds, hok => by
    dsimp only [compileModuleFlat] at hok
    cases hwf : f.wfCheck
    · simp only [hwf, Bool.not_false, ↓reduceIte] at hok; cases hok
    · simp only [hwf, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hok
      have heowf := earlyOptFlat_wfCheck f hwf
      have heoto := earlyOptFlat_toFn f hwf
      have hsupp_eq : (f.toFn.earlyOpt).body.supportsSource lt =
          (earlyOptFlat f).supportsSource lt := by
        rw [← heoto]
        exact TFlatFn.supportsSource_eq lt (earlyOptFlat f) heowf
      cases hsup : (earlyOptFlat f).supportsSource lt
      · simp only [hsup, Bool.false_eq_true, ↓reduceIte] at hok; cases hok
      · simp only [hsup, ↓reduceIte] at hok
        have hmwf := midStageFlat_wfCheck lt (earlyOptFlat f) heowf
        have hmto := midStageFlat_toFn lt (earlyOptFlat f) heowf
        let ef := earlyOptFlat f
        let mf := midStageFlat lt ef
        have hext : TFlat.ext mf.body = Fn.ext (Fn.midFromEarly lt f.toFn.earlyOpt) := by
          rw [TFlat.ext_eq_fn_ext mf hmwf, hmto, heoto]
        have hlow : Rega.lowerFlatFn I h (TFlat.ext mf.body) mf =
            Rega.lowerFn I h (Fn.ext (Fn.midFromEarly lt f.toFn.earlyOpt))
              (Fn.midFromEarly lt f.toFn.earlyOpt) := by
          rw [hext]
          have h1 := Rega.lowerFlatFn_eq_lowerFn I h
            (Fn.ext (Fn.midFromEarly lt f.toFn.earlyOpt)) mf hmwf
          rwa [hmto, heoto] at h1
        have hsig : (mf.name, mf.as, mf.rs) = (Fn.midFromEarly lt f.toFn.earlyOpt).sig := by
          have h1 : mf.toFn = Fn.midFromEarly lt f.toFn.earlyOpt := by rw [hmto, heoto]
          exact congrArg Fn.sig h1
        dsimp only [List.map, compileModule]
        simp only [hsupp_eq, hsup, ↓reduceIte]
        rw [← hlow, ← hext]
        split at hok
        · rename_i c b hlowOk hcbOk
          split at hok
          · rename_i cs bs hrest
            rw [hlowOk, hcbOk]
            dsimp only
            rw [← hsig]
            have ih := compileModule_of_compileModuleFlat I lt raBytes
              (((mf.name, mf.as, mf.rs), b) :: extCallees) exits nX fs hs cs bs hrest
            rw [ih]
            exact hok
          · simp at hok
        · cases hok
        · cases hok

end EndToEnd

end

end LeanQbe.T
