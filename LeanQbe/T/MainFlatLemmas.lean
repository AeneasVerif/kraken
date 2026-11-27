module

public import LeanQbe.T.MainFlat
public import LeanQbe.T.Main
import LeanQbe.T.FlatDirectLemmas
import LeanQbe.T.PassFlatKit
import LeanQbe.T.LegalFlat
import LeanQbe.T.RegaFlatLemmas
import LeanQbe.T.OptLemmas
import LeanQbe.T.LegalLemmas
import LeanQbe.T.OptFlatSimKit
import LeanQbe.T.OptFlatPlanKit
import LeanQbe.T.OptFlatValueLemmas
import LeanQbe.T.OptFlatMemLemmas
import LeanQbe.T.OptFlatCfgLemmas
import LeanQbe.T.OptFlatAddrRangeLemmas
import LeanQbe.T.OptFlatPathCondLemmas
import LeanQbe.T.OptFlatBranchLemmas
import LeanQbe.T.OptFlatLoopLemmas
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

open PassFlatKit (listGet?_append_left listGet?_append_right pushTup_append)
open OptFlatSimKit
  (listGet?_append_self wf_let wf_load wf_store wf_call wf_jnz wf_jump wf_group wf_cons)
open OptFlatPlanKit (ctxTypes_pushTup_rev)

private theorem listGet?_lt_length {α : Type} :
    (l : List α) → {i : Nat} → {x : α} → listGet? l i = some x → i < l.length
  | [], _, _, h => nomatch h
  | _ :: _, 0, _, _ => Nat.zero_lt_succ _
  | _ :: xs, _ + 1, _, h => Nat.succ_lt_succ (listGet?_lt_length xs h)

/-! ## Private `assumeElim` Proofs -/

private theorem denoteArg_ex {V : Ty → Type} {Γ vs} (hΓ : CtxTypes Γ vs)
    {t : Ty} {a : Arg K t} (hc : checkArg Γ t a = true) :
    ∃ a' : Arg V t, denoteArg vs a = some a' :=
  Option.isSome_iff_exists.1 (denoteArg_isSome_of_checkArg hΓ hc)

private theorem denoteArgs_ex {V : Ty → Type} {Γ vs} (hΓ : CtxTypes Γ vs)
    {ts : List Ty} {args : Tup (Arg K) ts} (hc : checkArgs Γ args = true) :
    ∃ args' : Tup (Arg V) ts, denoteArgs vs args = some args' :=
  Option.isSome_iff_exists.1 (denoteArgs_isSome_of_checkArgs hΓ hc)

local macro "ishlt_a" hΓ:ident "," hc:term : tactic => `(tactic| (
  obtain ⟨_, ha⟩ := denoteArg_ex (V := _) $hΓ $hc; dsimp only [denote]; rw [ha]; rfl))

local macro "ishlt_as" hΓ:ident "," hc:term : tactic => `(tactic| (
  obtain ⟨_, ha⟩ := denoteArgs_ex (V := _) $hΓ $hc; dsimp only [denote]; rw [ha]; rfl))

private theorem denote_isHlt_of_wf {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    {Γ : List Ty} {Δ : List (List Ty)}
    {vs : List ((t : Ty) × V t)} {ls : List ((ts : List Ty) × L ts)}
    (hΓ : CtxTypes Γ vs) (hΔ : CtxTypes Δ ls) :
    (tf : TFlat rs) → tf.wfCheck Γ Δ = true → (denote V L tf vs ls).isHlt = tf.isHlt
  | .let_ _ _, hwf => by ishlt_as hΓ, (wf_let hwf).1
  | .call _ _ _ _, hwf => by ishlt_as hΓ, (wf_call hwf).1
  | .load _ _ _, hwf => by ishlt_a hΓ, (wf_load hwf).1
  | .store _ _ _, hwf => by
    have ⟨hv, ha, _⟩ := wf_store hwf
    obtain ⟨_, hv'⟩ := denoteArg_ex (V := V) hΓ hv; obtain ⟨_, ha'⟩ := denoteArg_ex (V := V) hΓ ha
    dsimp only [denote]; rw [hv', ha']; rfl
  | .jnz _ _ _, hwf => by ishlt_a hΓ, (wf_jnz hwf).1
  | .jump _ _, hwf => by
    have ⟨hj, ha⟩ := wf_jump hwf
    obtain ⟨_, hj'⟩ := Option.isSome_iff_exists.1 (lookupL_isSome_of_check hΔ hj)
    obtain ⟨_, ha'⟩ := denoteArgs_ex (V := V) hΓ ha; dsimp only [denote]; rw [hj', ha']; rfl
  | .ret _, hwf | .exit _ _, hwf => by ishlt_as hΓ, hwf
  | .hlt, _ | .group _ _, _ => rfl

mutual
private theorem assumeElim_wfCheckAux {rs : List Ty} :
    (tf : TFlat rs) → {Γ : List Ty} → {Δ : List (List Ty)} →
    tf.wfCheck Γ Δ = true → tf.assumeElim.wfCheck Γ Δ = true
  | .let_ _ k, _, _, hwf | .load _ _ k, _, _, hwf
  | .store _ _ k, _, _, hwf | .call _ _ _ k, _, _, hwf => by
    dsimp only [TFlat.wfCheck, TFlat.assumeElim] at hwf ⊢
    simp only [Bool.and_eq_true] at hwf ⊢
    exact ⟨hwf.1, assumeElim_wfCheckAux k hwf.2⟩
  | .jnz c t e, _, _, hwf => by
    have ⟨hc, ht0, he0⟩ := wf_jnz hwf
    have ht := assumeElim_wfCheckAux t ht0; have he := assumeElim_wfCheckAux e he0
    dsimp only [TFlat.assumeElim, TFlat.mkJnzAssume]
    by_cases hhe : e.assumeElim.isHlt = true
    · simp only [hhe, ↓reduceIte]; exact ht
    · by_cases hht : t.assumeElim.isHlt = true
      · simp only [hhe, hht, Bool.false_eq_true, ↓reduceIte]; exact he
      · simp only [hhe, hht, Bool.false_eq_true, ↓reduceIte, TFlat.wfCheck, Bool.and_eq_true]
        exact ⟨⟨hc, ht⟩, he⟩
  | .jump _ _, _, _, hwf | .ret _, _, _, hwf | .exit _ _, _, _, hwf | .hlt, _, _, hwf => hwf
  | .group bodies k, _, _, hwf => by
    have ⟨hb, hk⟩ := wf_group hwf
    simp only [TFlat.assumeElim, TFlat.wfCheck, Bool.and_eq_true]
    exact ⟨assumeElimB_wfCheckAux bodies hb, assumeElim_wfCheckAux k hk⟩

private theorem assumeElimB_wfCheckAux {rs : List Ty} :
    {sig : List (List Ty)} → (tb : TBlocks rs sig) →
    {Γ : List Ty} → {Δ : List (List Ty)} →
    tb.wfCheck Γ Δ = true → tb.assumeElim.wfCheck Γ Δ = true
  | _, .nil, _, _, hwf => hwf
  | _, .cons b bs, _, _, hwf => by
    have ⟨hb, hbs⟩ := wf_cons hwf
    simp only [TBlocks.assumeElim, TBlocks.wfCheck, Bool.and_eq_true]
    exact ⟨assumeElim_wfCheckAux b hb, assumeElimB_wfCheckAux bs hbs⟩
end

mutual
private theorem denote_assumeElim_eq {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    (tf : TFlat rs) → {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × V t)} → {ls : List ((ts : List Ty) × L ts)} →
    CtxTypes Γ vs → CtxTypes Δ ls → tf.wfCheck Γ Δ = true →
    denote V L tf.assumeElim vs ls = assumeElim (denote V L tf vs ls)
  | .let_ op k, _, _, vs, ls, hΓ, hΔ, hwf => by
    have ⟨ha, hk⟩ := wf_let hwf; obtain ⟨_, ha'⟩ := denoteArgs_ex (V := V) hΓ ha
    dsimp only [TFlat.assumeElim, denote, assumeElim]; rw [ha']; dsimp only
    exact congrArg (Expr.let_ _) (funext fun xs =>
      denote_assumeElim_eq k (ctxTypes_pushTup_rev xs hΓ) hΔ hk)
  | .load t a k, _, _, vs, ls, hΓ, hΔ, hwf => by
    have ⟨ha, hk⟩ := wf_load hwf; obtain ⟨_, ha'⟩ := denoteArg_ex (V := V) hΓ ha
    dsimp only [TFlat.assumeElim, denote, assumeElim]; rw [ha']; dsimp only
    exact congrArg (Expr.load t _) (funext fun v => denote_assumeElim_eq k (.cons hΓ) hΔ hk)
  | .store v a k, _, _, vs, ls, hΓ, hΔ, hwf => by
    have ⟨hv, ha, hk⟩ := wf_store hwf
    obtain ⟨_, hv'⟩ := denoteArg_ex (V := V) hΓ hv; obtain ⟨_, ha'⟩ := denoteArg_ex (V := V) hΓ ha
    dsimp only [TFlat.assumeElim, denote, assumeElim]; rw [hv', ha']; dsimp only
    exact congrArg (Expr.store _ _) (denote_assumeElim_eq k hΓ hΔ hk)
  | .call f bs args k, _, _, vs, ls, hΓ, hΔ, hwf => by
    have ⟨ha, hk⟩ := wf_call hwf; obtain ⟨_, ha'⟩ := denoteArgs_ex (V := V) hΓ ha
    dsimp only [TFlat.assumeElim, denote, assumeElim]; rw [ha']; dsimp only
    exact congrArg (Expr.call f _) (funext fun xs =>
      denote_assumeElim_eq k (ctxTypes_pushTup_rev xs hΓ) hΔ hk)
  | .jnz c t e, _, _, vs, ls, hΓ, hΔ, hwf => by
    have ⟨hc, ht, he⟩ := wf_jnz hwf; obtain ⟨_, hc'⟩ := denoteArg_ex (V := V) hΓ hc
    have iht := denote_assumeElim_eq t hΓ hΔ ht; have ihe := denote_assumeElim_eq e hΓ hΔ he
    have hth : (assumeElim (denote V L t vs ls)).isHlt = t.assumeElim.isHlt := by
      rw [← iht]; exact denote_isHlt_of_wf hΓ hΔ t.assumeElim (assumeElim_wfCheckAux t ht)
    have heh : (assumeElim (denote V L e vs ls)).isHlt = e.assumeElim.isHlt := by
      rw [← ihe]; exact denote_isHlt_of_wf hΓ hΔ e.assumeElim (assumeElim_wfCheckAux e he)
    dsimp only [TFlat.assumeElim, TFlat.mkJnzAssume, denote]; rw [hc']; dsimp only
    unfold assumeElim; dsimp only [mkJnzAssume]
    cases hhe : e.assumeElim.isHlt with
    | true => simp only [heh.trans hhe, ↓reduceIte, iht]
    | false =>
      cases hht : t.assumeElim.isHlt with
      | true => simp only [heh.trans hhe, hth.trans hht, Bool.false_eq_true, ↓reduceIte, ihe]
      | false =>
        simp only [heh.trans hhe, hth.trans hht, Bool.false_eq_true, ↓reduceIte, denote, hc', iht,
          ihe]
  | .jump (ts := ts) j args, _, _, vs, ls, hΓ, hΔ, hwf => by
    have ⟨hj, ha⟩ := wf_jump hwf
    obtain ⟨_, hj'⟩ := Option.isSome_iff_exists.1 (lookupL_isSome_of_check hΔ hj)
    obtain ⟨_, ha'⟩ := denoteArgs_ex (V := V) hΓ ha
    dsimp only [TFlat.assumeElim, denote]; rw [hj', ha']; rfl
  | .ret _, _, _, vs, _, hΓ, _, hwf | .exit _ _, _, _, vs, _, hΓ, _, hwf => by
    obtain ⟨_, ha'⟩ := denoteArgs_ex (V := V) hΓ hwf
    dsimp only [TFlat.assumeElim, denote]; rw [ha']; rfl
  | .hlt, _, _, _, _, _, _, _ => rfl
  | .group bodies k, _, _, vs, ls, hΓ, hΔ, hwf => by
    have ⟨hb, hk⟩ := wf_group hwf
    dsimp only [TFlat.assumeElim, denote, assumeElim]
    exact congr (congrArg Expr.group (funext fun Js =>
        denoteB_assumeElim_eq bodies hΓ (ctxTypes_pushTup_rev Js hΔ) hb))
      (funext fun Js => denote_assumeElim_eq k hΓ (ctxTypes_pushTup_rev Js hΔ) hk)

private theorem denoteB_assumeElim_eq {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    {sig : List (List Ty)} → (tb : TBlocks rs sig) →
    {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × V t)} → {ls : List ((ts : List Ty) × L ts)} →
    CtxTypes Γ vs → CtxTypes Δ ls → tb.wfCheck Γ Δ = true →
    denoteB V L tb.assumeElim vs ls = assumeElimB (denoteB V L tb vs ls)
  | _, .nil, _, _, _, _, _, _, _ => rfl
  | _, .cons b bs, _, _, vs, ls, hΓ, hΔ, hwf => by
    have ⟨hb, hbs⟩ := wf_cons hwf
    dsimp only [TBlocks.assumeElim, denoteB, assumeElimB]
    exact congr (congrArg Blocks.cons (funext fun xs =>
        denote_assumeElim_eq b (ctxTypes_pushTup_rev xs hΓ) hΔ hb))
      (denoteB_assumeElim_eq bs hΓ hΔ hbs)
end

/-! ## Private `mergeRets` Proofs -/

private theorem checkArgs_retIdxs_gen :
    (ts suf : List Ty) → checkArgs (ts.reverse ++ suf) (retIdxs ts) = true
  | [], _ => rfl
  | t :: ts, suf => by
    dsimp only [retIdxs, checkArgs]
    rw [List.reverse_cons, List.append_assoc, Bool.and_eq_true]
    refine ⟨checkArg_eq_true_iff.mpr ?_, checkArgs_retIdxs_gen ts (t :: suf)⟩
    simpa [List.length_reverse] using listGet?_append_self ts.reverse t suf

private theorem denoteArgs_retIdxs_gen {V : Ty → Type} :
    {ts : List Ty} → (xs : Tup V ts) → (suf : List ((u : Ty) × V u)) →
    denoteArgs (pushTup xs suf) (retIdxs ts) = some (toArgTup xs)
  | [], (), _ => rfl
  | t :: ts, (x, xs), suf => by
    dsimp only [pushTup, retIdxs, denoteArgs, toArgTup]
    have hhead : denoteArg (pushTup xs (⟨t, x⟩ :: suf)) (.var ts.length) = some (.var x) := by
      dsimp only [denoteArg, lookupV]
      have hpt : pushTup xs (⟨t, x⟩ :: suf) = pushTup xs [] ++ ⟨t, x⟩ :: suf :=
        pushTup_append xs [] (⟨t, x⟩ :: suf)
      have hget : listGet? (pushTup xs (⟨t, x⟩ :: suf)) ts.length = some ⟨t, x⟩ := by
        rw [hpt]
        simpa [pushTup_length] using listGet?_append_self (pushTup xs []) ⟨t, x⟩ suf
      rw [hget]; dsimp only
      rw [PassFlatKit.castTy_self]
    rw [hhead, denoteArgs_retIdxs_gen xs (⟨t, x⟩ :: suf)]

mutual
private theorem wfCheck_mergeRetsAux {rs : List Ty} :
    (tf : TFlat rs) → {Γ : List Ty} → {Δ Δ' : List (List Ty)} → (exitIdx : Nat) →
    tf.wfCheck Γ Δ = true → listGet? Δ' exitIdx = some rs →
    (∀ i us, i < Δ.length → listGet? Δ i = some us → listGet? Δ' i = some us) →
    (tf.mergeRetsAux exitIdx).wfCheck Γ Δ' = true
  | .let_ _ k, _, _, _, _, hwf, hex, hpre | .load _ _ k, _, _, _, _, hwf, hex, hpre
  | .store _ _ k, _, _, _, _, hwf, hex, hpre | .call _ _ _ k, _, _, _, _, hwf, hex, hpre => by
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
    exact ⟨checkJump_eq_true_iff.mpr (hpre j ts (listGet?_lt_length _ hget) hget), hwf.2⟩
  | .ret vs, _, _, _, _, hwf, hex, _ => by
    dsimp only [TFlat.wfCheck, TFlat.mergeRetsAux] at hwf ⊢
    simp only [Bool.and_eq_true]
    exact ⟨checkJump_eq_true_iff.mpr hex, hwf⟩
  | .exit _ _, _, _, _, _, hwf, _, _ => hwf
  | .hlt, _, _, _, _, hwf, _, _ => hwf
  | .group (sig := sig) bodies k, Γ, Δ, Δ', exitIdx, hwf, hex, hpre => by
    dsimp only [TFlat.wfCheck, TFlat.mergeRetsAux] at hwf ⊢
    simp only [Bool.and_eq_true] at hwf ⊢
    have hex' : listGet? (pushTypes sig Δ') (exitIdx + sig.length) = some rs := by
      rw [pushTypes_eq_reverse_append, ← List.length_reverse (as := sig), Nat.add_comm]
      exact (listGet?_append_right sig.reverse exitIdx).trans hex
    have hpre' : ∀ i us, i < (pushTypes sig Δ).length →
        listGet? (pushTypes sig Δ) i = some us → listGet? (pushTypes sig Δ') i = some us := by
      intro i us hlt hget
      rw [pushTypes_eq_reverse_append] at hlt hget ⊢
      by_cases hi : i < sig.length
      · have hir : i < sig.reverse.length := by simpa [List.length_reverse] using hi
        rw [listGet?_append_left hir] at hget ⊢; exact hget
      · have hlen : sig.reverse.length ≤ i := by
          simpa [List.length_reverse] using Nat.le_of_not_lt hi
        have hi_eq : i = sig.reverse.length + (i - sig.reverse.length) := by omega
        rw [hi_eq, listGet?_append_right] at hget ⊢
        exact hpre _ us (by rw [List.length_append] at hlt; omega) hget
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
    have ⟨ha, hk⟩ := wf_let hwf; obtain ⟨_, ha'⟩ := denoteArgs_ex (V := V) hΓ ha
    dsimp only [TFlat.mergeRetsAux, denote, Expr.mergeRets]; rw [ha']; dsimp only
    exact congrArg (Expr.let_ _) (funext fun xs => by
      simpa only [pushTup_length] using
        denote_mergeRetsAux_eq exit_lbl k (ctxTypes_pushTup_rev xs hΓ) hΔ hk)
  | .load t a k, _, _, vs, ls, hΓ, hΔ, hwf => by
    have ⟨ha, hk⟩ := wf_load hwf; obtain ⟨_, ha'⟩ := denoteArg_ex (V := V) hΓ ha
    dsimp only [TFlat.mergeRetsAux, denote, Expr.mergeRets]; rw [ha']; dsimp only
    exact congrArg (Expr.load t _)
      (funext fun v => denote_mergeRetsAux_eq exit_lbl k (.cons hΓ) hΔ hk)
  | .store v a k, _, _, vs, ls, hΓ, hΔ, hwf => by
    have ⟨hv, ha, hk⟩ := wf_store hwf
    obtain ⟨_, hv'⟩ := denoteArg_ex (V := V) hΓ hv; obtain ⟨_, ha'⟩ := denoteArg_ex (V := V) hΓ ha
    dsimp only [TFlat.mergeRetsAux, denote, Expr.mergeRets]; rw [hv', ha']; dsimp only
    exact congrArg (Expr.store _ _) (denote_mergeRetsAux_eq exit_lbl k hΓ hΔ hk)
  | .call f bs args k, _, _, vs, ls, hΓ, hΔ, hwf => by
    have ⟨ha, hk⟩ := wf_call hwf; obtain ⟨_, ha'⟩ := denoteArgs_ex (V := V) hΓ ha
    dsimp only [TFlat.mergeRetsAux, denote, Expr.mergeRets]; rw [ha']; dsimp only
    exact congrArg (Expr.call f _) (funext fun xs =>
      denote_mergeRetsAux_eq exit_lbl k (ctxTypes_pushTup_rev xs hΓ) hΔ hk)
  | .jnz c t e, _, _, vs, ls, hΓ, hΔ, hwf => by
    have ⟨hc, ht, he⟩ := wf_jnz hwf; obtain ⟨_, hc'⟩ := denoteArg_ex (V := V) hΓ hc
    dsimp only [TFlat.mergeRetsAux, denote]; rw [hc']; dsimp only; unfold Expr.mergeRets
    rw [denote_mergeRetsAux_eq exit_lbl t hΓ hΔ ht, denote_mergeRetsAux_eq exit_lbl e hΓ hΔ he]
  | .jump (ts := ts) j args, _, _, vs, ls, hΓ, hΔ, hwf => by
    have ⟨hj, ha⟩ := wf_jump hwf
    obtain ⟨l, hget, hlt⟩ := ctxTypes_listGet? hΔ (checkJump_eq_true_iff.mp hj)
    have hlook₁ : lookupL (ls ++ [⟨rs, exit_lbl⟩]) ts j = some l := by
      dsimp only [lookupL]; rw [listGet?_append_left hlt, hget]
      dsimp only; rw [PassFlatKit.castListTy_self]
    have hlook₂ : lookupL ls ts j = some l := by
      dsimp only [lookupL]; rw [hget]; dsimp only; rw [PassFlatKit.castListTy_self]
    obtain ⟨_, ha'⟩ := denoteArgs_ex (V := V) hΓ ha
    dsimp only [TFlat.mergeRetsAux, denote]; rw [hlook₁, hlook₂, ha']; rfl
  | .ret vs', _, _, vs, ls, hΓ, _, hwf => by
    obtain ⟨_, hv⟩ := denoteArgs_ex (V := V) hΓ hwf
    have hlook : lookupL (ls ++ [⟨rs, exit_lbl⟩]) rs ls.length = some exit_lbl := by
      dsimp only [lookupL]; rw [listGet?_append_self]; dsimp only; rw [PassFlatKit.castListTy_self]
    dsimp only [TFlat.mergeRetsAux, denote]; rw [hlook, hv]; rfl
  | .exit f args, _, _, vs, _, hΓ, _, hwf => by
    obtain ⟨_, ha⟩ := denoteArgs_ex (V := V) hΓ hwf
    dsimp only [TFlat.mergeRetsAux, denote]; rw [ha]; rfl
  | .hlt, _, _, _, _, _, _, _ => rfl
  | .group (sig := sig) bodies k, _, _, vs, ls, hΓ, hΔ, hwf => by
    have ⟨hb, hk⟩ := wf_group hwf
    dsimp only [TFlat.mergeRetsAux, denote, Expr.mergeRets]
    refine congr (congrArg Expr.group (funext fun Js => ?_)) (funext fun Js => ?_)
    · rw [pushTup_append Js ls [⟨rs, exit_lbl⟩],
        ← show (pushTup Js ls).length = ls.length + sig.length by rw [pushTup_length, Nat.add_comm]]
      exact denoteB_mergeRetsAux_eq exit_lbl bodies hΓ (ctxTypes_pushTup_rev Js hΔ) hb
    · rw [pushTup_append Js ls [⟨rs, exit_lbl⟩],
        ← show (pushTup Js ls).length = ls.length + sig.length by rw [pushTup_length, Nat.add_comm]]
      exact denote_mergeRetsAux_eq exit_lbl k hΓ (ctxTypes_pushTup_rev Js hΔ) hk

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
    have ⟨hb, hbs⟩ := wf_cons hwf
    dsimp only [TBlocks.mergeRetsAux, denoteB, Blocks.mergeRets]
    exact congr (congrArg Blocks.cons (funext fun xs =>
        denote_mergeRetsAux_eq exit_lbl b (ctxTypes_pushTup_rev xs hΓ) hΔ hb))
      (denoteB_mergeRetsAux_eq exit_lbl bs hΓ hΔ hbs)
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
  split
  · split
    · exact wfCheck_reifyBridge (Func.simplifyGroupWithPlan_wf _ (Func.wf_of_denote tf rfl))
    · exact hwf
  · exact hwf

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
  dsimp only [peelFastFlat]; split <;> rfl

/-- `peelFastFlat as tf budget = reifyFunc (Func.peelFast (denoteFunc tf) budget)`. -/
theorem peelFastFlat_eq {as rs : List Ty} (tf : TFlat rs) (budget : Nat := 24)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    peelFastFlat as tf budget = reifyFunc (Func.peelFast (denoteFunc (as := as) tf) budget) := by
  rw [← denoteFunc_peelFastFlat tf budget hwf,
    reifyFunc_denoteFunc_eq _ (peelFastFlat_wfCheck tf budget hwf)]

local macro "delegate_flat_pass" flat:ident phoas:ident
    twf:ident tden:ident teq:ident swf:ident sden:ident seq:ident : command => `(
  theorem $twf:ident (as : List Ty) {rs : List Ty} (tf : TFlat rs)
      (hwf : tf.wfCheck (pushTypes as []) [] = true) :
      ($flat as tf).wfCheck (pushTypes as []) [] = true := $swf tf hwf
  theorem $tden:ident (as : List Ty) {rs : List Ty} (tf : TFlat rs)
      (hwf : tf.wfCheck (pushTypes as []) [] = true) :
      denoteFunc (as := as) ($flat as tf) = $phoas (denoteFunc (as := as) tf) := $sden tf hwf
  theorem $teq:ident (as : List Ty) {rs : List Ty} (tf : TFlat rs)
      (hwf : tf.wfCheck (pushTypes as []) [] = true) :
      $flat as tf = reifyFunc ($phoas (denoteFunc (as := as) tf)) := $seq tf hwf)

local macro "delegate_flat_pass_cfg" flat:ident phoas:ident cfgTy:term "," dflt:term ","
    twf:ident tden:ident teq:ident swf:ident sden:ident seq:ident : command => `(
  theorem $twf:ident (as : List Ty) {rs : List Ty} (tf : TFlat rs) (cfg : $cfgTy := $dflt)
      (hwf : tf.wfCheck (pushTypes as []) [] = true) :
      ($flat as tf cfg).wfCheck (pushTypes as []) [] = true := $swf tf cfg hwf
  theorem $tden:ident (as : List Ty) {rs : List Ty} (tf : TFlat rs) (cfg : $cfgTy := $dflt)
      (hwf : tf.wfCheck (pushTypes as []) [] = true) :
      denoteFunc (as := as) ($flat as tf cfg) = $phoas (denoteFunc (as := as) tf) cfg :=
    $sden tf cfg hwf
  theorem $teq:ident (as : List Ty) {rs : List Ty} (tf : TFlat rs) (cfg : $cfgTy := $dflt)
      (hwf : tf.wfCheck (pushTypes as []) [] = true) :
      $flat as tf cfg = reifyFunc ($phoas (denoteFunc (as := as) tf) cfg) := $seq tf cfg hwf)

delegate_flat_pass licmFlat Func.licm
  licmFlat_wfCheck denoteFunc_licmFlat licmFlat_eq
  OptFlatLoop.licmFlat_wfCheck OptFlatLoop.denoteFunc_licmFlat OptFlatLoop.licmFlat_eq

delegate_flat_pass_cfg loopRotateFlat Func.loopRotate
  LoopRotate.RotConfig, LoopRotate.defaultRotConfig,
  loopRotateFlat_wfCheck denoteFunc_loopRotateFlat loopRotateFlat_eq
  OptFlatLoop.loopRotateFlat_wfCheck OptFlatLoop.denoteFunc_loopRotateFlat
  OptFlatLoop.loopRotateFlat_eq

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

delegate_flat_pass addrRangeOptFlat Func.addrRangeOpt
  addrRangeOptFlat_wfCheck denoteFunc_addrRangeOptFlat addrRangeOptFlat_eq
  OptFlatAddrRange.addrRangeOptFlat_wfCheck OptFlatAddrRange.denoteFunc_addrRangeOptFlat
  OptFlatAddrRange.addrRangeOptFlat_eq

delegate_flat_pass pathCondOptFlat Func.pathCondOpt
  pathCondOptFlat_wfCheck denoteFunc_pathCondOptFlat pathCondOptFlat_eq
  OptFlatPathCond.pathCondOptFlat_wfCheck OptFlatPathCond.denoteFunc_pathCondOptFlat
  OptFlatPathCond.pathCondOptFlat_eq

delegate_flat_pass condThreadPassFlat Func.condThreadPass
  condThreadPassFlat_wfCheck denoteFunc_condThreadPassFlat condThreadPassFlat_eq
  OptFlatBranch.condThreadPassFlat_wfCheck OptFlatBranch.denoteFunc_condThreadPassFlat
  OptFlatBranch.condThreadPassFlat_eq

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

delegate_flat_pass_cfg tailDupFlat Func.tailDup TailDup.TailDupConfig, {},
  tailDupFlat_wfCheck denoteFunc_tailDupFlat tailDupFlat_eq
  OptFlatBranch.tailDupFlat_wfCheck OptFlatBranch.denoteFunc_tailDupFlat
  OptFlatBranch.tailDupFlat_eq

section PipelineProofs

attribute [local irreducible]
  OptFlatValue.foldFlat OptFlatValue.copyFlat OptFlatValue.canonFlat OptFlatValue.gvnFlat
  OptFlatMem.memLoadFlat OptFlatMem.assumeBitsFlat OptFlatMem.divConstFlat
  OptFlatCfg.dcePFlat OptFlatCfg.deadLoadElimFlat OptFlatCfg.ifOptFlat
  simplifyGroupFastFlat peelFastFlat licmFlat loopRotateFlat TFlat.zeroPeelWith
  legalFlat addrRangeOptFlat condThreadLateOptFlat tailDupFlat

private abbrev mkFS {as rs : List Ty} (flat : TFlat rs → TFlat rs) (phoas : Func as rs → Func as rs)
    (wf : ∀ tf, tf.wfCheck (pushTypes as []) [] = true →
      (flat tf).wfCheck (pushTypes as []) [] = true)
    (den : ∀ tf, tf.wfCheck (pushTypes as []) [] = true →
      denoteFunc (as := as) (flat tf) = phoas (denoteFunc (as := as) tf)) :
    OptFlatSimKit.FlatStage as rs := ⟨flat, phoas, wf, den⟩

private abbrev fsFold (as rs : List Ty) : OptFlatSimKit.FlatStage as rs :=
  mkFS (OptFlatValue.foldFlat as) Func.fold
    OptFlatValue.foldFlat_wfCheck OptFlatValue.denoteFunc_foldFlat

private abbrev fsCanon (as rs : List Ty) : OptFlatSimKit.FlatStage as rs :=
  mkFS (OptFlatValue.canonFlat as) Func.canon
    OptFlatValue.canonFlat_wfCheck OptFlatValue.denoteFunc_canonFlat

private abbrev fsCopy (as rs : List Ty) : OptFlatSimKit.FlatStage as rs :=
  mkFS (OptFlatValue.copyFlat as) Func.copy
    OptFlatValue.copyFlat_wfCheck OptFlatValue.denoteFunc_copyFlat

private abbrev fsGvn (as rs : List Ty) : OptFlatSimKit.FlatStage as rs :=
  mkFS (OptFlatValue.gvnFlat as) Func.gvn
    OptFlatValue.gvnFlat_wfCheck OptFlatValue.denoteFunc_gvnFlat

private abbrev fsDceP (as rs : List Ty) : OptFlatSimKit.FlatStage as rs :=
  mkFS (OptFlatCfg.dcePFlat as) Func.dceP OptFlatCfg.dcePFlat_wfCheck OptFlatCfg.denoteFunc_dcePFlat

private abbrev earlyStages (as rs : List Ty) : List (OptFlatSimKit.FlatStage as rs) :=
  [ fsFold as rs, fsCanon as rs, fsCopy as rs, fsGvn as rs, fsCopy as rs, fsFold as rs,
    mkFS (OptFlatCfg.ifOptFlat false as) (Func.ifOptWith false)
      (OptFlatCfg.ifOptFlat_wfCheck false) OptFlatCfg.denoteFunc_ifOptFlat_false,
    mkFS (simplifyGroupFastFlat as) Func.simplifyGroupFast
      simplifyGroupFastFlat_wfCheck denoteFunc_simplifyGroupFastFlat,
    mkFS (peelFastFlat as · 24) (Func.peelFast · 24)
      (peelFastFlat_wfCheck · 24) (denoteFunc_peelFastFlat · 24),
    mkFS (TFlat.zeroPeelWith { peelBudget := 24 }) (Func.zeroPeelWith { peelBudget := 24 })
      wfCheck_zeroPeel24 denoteFunc_zeroPeel24,
    fsCopy as rs, fsFold as rs, fsDceP as rs ]

private abbrev midStages (as rs : List Ty) : List (OptFlatSimKit.FlatStage as rs) :=
  [ fsFold as rs, fsCanon as rs,
    mkFS (OptFlatMem.divConstFlat as) Func.divConst
      OptFlatMem.divConstFlat_wfCheck OptFlatMem.denoteFunc_divConstFlat,
    fsCopy as rs,
    mkFS (OptFlatMem.memLoadFlat as) Func.memLoad
      OptFlatMem.memLoadFlat_wfCheck OptFlatMem.denoteFunc_memLoadFlat,
    fsGvn as rs,
    mkFS (OptFlatMem.assumeBitsFlat as) Func.assumeBits
      OptFlatMem.assumeBitsFlat_wfCheck OptFlatMem.denoteFunc_assumeBitsFlat,
    fsFold as rs,
    mkFS (OptFlatCfg.ifOptFlat true as) (Func.ifOptWith true)
      (OptFlatCfg.ifOptFlat_wfCheck true) OptFlatCfg.denoteFunc_ifOptFlat_true,
    mkFS (simplifyGroupFastFlat as) Func.simplifyGroupFast
      simplifyGroupFastFlat_wfCheck denoteFunc_simplifyGroupFastFlat,
    mkFS (OptFlatCfg.deadLoadElimFlat as) Func.deadLoadElim
      OptFlatCfg.deadLoadElimFlat_wfCheck OptFlatCfg.denoteFunc_deadLoadElimFlat,
    mkFS assumeElimFlat Func.assumeElim
      (fun _ => TFlat.wfCheck_assumeElim) denoteFunc_assumeElimFlat,
    fsFold as rs,
    mkFS (addrRangeOptFlat as) Func.addrRangeOpt
      (addrRangeOptFlat_wfCheck as) (denoteFunc_addrRangeOptFlat as),
    fsGvn as rs,
    mkFS (licmFlat as) Func.licm (licmFlat_wfCheck as) (denoteFunc_licmFlat as),
    fsDceP as rs,
    mkFS (loopRotateFlat as · LoopRotate.defaultRotConfig)
      (Func.loopRotate · LoopRotate.defaultRotConfig)
      (loopRotateFlat_wfCheck as · LoopRotate.defaultRotConfig)
      (denoteFunc_loopRotateFlat as · LoopRotate.defaultRotConfig),
    mkFS (condThreadLateOptFlat as) Func.condThreadLateOpt
      (condThreadLateOptFlat_wfCheck as) (denoteFunc_condThreadLateOptFlat as),
    fsFold as rs, fsDceP as rs,
    mkFS (tailDupFlat as · {}) (Func.tailDup · {})
      (tailDupFlat_wfCheck as · {}) (denoteFunc_tailDupFlat as · {}),
    mkFS mergeRetsFlat Func.mergeRets (fun _ => TFlat.wfCheck_mergeRets) denoteFunc_mergeRetsFlat ]

/-- `earlyOptFlat` preserves `TFlatFn.wfCheck`. -/
theorem earlyOptFlat_wfCheck (f : TFlatFn) (_hwf : f.wfCheck = true) :
    (earlyOptFlat f).wfCheck = true := by
  dsimp only [earlyOptFlat, TFlatFn.wfCheck]
  exact OptFlatSimKit.FlatStage.run_wfCheck (earlyStages f.as f.rs) f.body _hwf

/-- `(earlyOptFlat f).toFn = f.toFn.earlyOpt` whenever `f.wfCheck = true`. -/
theorem earlyOptFlat_toFn (f : TFlatFn) (_hwf : f.wfCheck = true) :
    (earlyOptFlat f).toFn = f.toFn.earlyOpt := by
  dsimp only [TFlatFn.toFn, Fn.earlyOpt, earlyOptFlat]
  rw [Func.earlyOpt_eq, Func.earlyCore_eq]
  refine congrArg (Fn.mk f.name f.as f.rs) ?_
  change denoteFunc (as := f.as) (OptFlatSimKit.FlatStage.run (earlyStages f.as f.rs) f.body) = _
  rw [OptFlatSimKit.FlatStage.run_denoteFunc (earlyStages f.as f.rs) f.body _hwf]
  exact (Func.renorm_eq_self (Func.dceP_wf (Func.fold_wf (Func.copy_wf
    (Func.zeroPeelWith_wf _ (Func.peelFast_wf _ 24)))))).symm

/-- `midStageFlat` preserves `TFlatFn.wfCheck`. -/
theorem midStageFlat_wfCheck (lt : LegalTarget) (ef : TFlatFn) (hwf : ef.wfCheck = true) :
    (midStageFlat lt ef).wfCheck = true := by
  let as' := lt.legalSig ef.as
  let tf0 := legalFlat lt (as := ef.as) ef.body
  have h0 : tf0.wfCheck (pushTypes as' []) [] = true := by
    dsimp only [tf0]
    rw [legalFlat_eq lt ef.body hwf]
    exact wfCheck_reifyBridge (Func.legal_wf lt (Func.wf_of_denote ef.body rfl))
  dsimp only [midStageFlat, TFlatFn.wfCheck]
  exact OptFlatSimKit.FlatStage.run_wfCheck (midStages as' (lt.legalSig ef.rs)) tf0 h0

/-- `(midStageFlat lt ef).toFn = Fn.midFromEarly lt ef.toFn` whenever `ef.wfCheck = true`. -/
theorem midStageFlat_toFn (lt : LegalTarget) (ef : TFlatFn) (hwf : ef.wfCheck = true) :
    (midStageFlat lt ef).toFn = Fn.midFromEarly lt ef.toFn := by
  let as' := lt.legalSig ef.as
  let tf0 := legalFlat lt (as := ef.as) ef.body
  have h0 : tf0.wfCheck (pushTypes as' []) [] = true := by
    dsimp only [tf0]
    rw [legalFlat_eq lt ef.body hwf]
    exact wfCheck_reifyBridge (Func.legal_wf lt (Func.wf_of_denote ef.body rfl))
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
    Func.renorm_eq_self hwf4, Func.renorm_eq_self hwf5,
    Func.lateCondThread_eq, Func.lateLoopRotate_eq, Func.lateCfgPost_eq, Func.lateCfgPre_eq,
    Func.lateCorePost_eq, Func.lateCorePre_eq]
  change denoteFunc (as := as')
    (OptFlatSimKit.FlatStage.run (midStages as' (lt.legalSig ef.rs)) tf0) = _
  rw [OptFlatSimKit.FlatStage.run_denoteFunc (midStages as' (lt.legalSig ef.rs)) tf0 h0, d0]
  dsimp only [OptFlatSimKit.FlatStage.runPhoas, List.foldl]
  rfl

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
