module

public import LeanQbe.T.OptFlatValue
import LeanQbe.T.FlatDirectLemmas
import LeanQbe.T.PassFlatKit
import LeanQbe.T.FoldLemmas
import LeanQbe.T.CopyLemmas
import LeanQbe.T.CanonLemmas
import LeanQbe.T.GvnLemmas

/-!
# Equivalence Proofs for `OptFlatValue` (`foldFlat_eq`, `copyFlat_eq`, `canonFlat_eq`, `gvnFlat_eq`)

Proves exact `=` correspondence (`std3` axioms only) between every direct `TFlat` value pass in
`LeanQbe.T.OptFlatValue` and its PHOAS counterpart (`Func.fold`, `Func.copy`, `Func.canon`,
`Func.gvn`), matching `MainFlatLemmas` contracts:

* `OptFlatValue.foldFlat_eq`, `denoteFunc_foldFlat`, `foldFlat_wfCheck`, `foldFlatFn_toFn`
* `OptFlatValue.copyFlat_eq`, `denoteFunc_copyFlat`, `copyFlat_wfCheck`, `copyFlatFn_toFn`
* `OptFlatValue.canonFlat_eq`, `denoteFunc_canonFlat`, `canonFlat_wfCheck`, `canonFlatFn_toFn`
* `OptFlatValue.gvnFlat_eq`, `denoteFunc_gvnFlat`, `gvnFlat_wfCheck`, `gvnFlatFn_toFn`
-/

set_option autoImplicit false

public section

namespace LeanQbe.T
namespace OptFlatValue

/-! ## Shared `Trie` Environment & Operand Simulation Lemmas -/

private theorem insertTupEnv_eq_insertTupTrie {W : Ty → Type} :
    ∀ (depth : Nat) (env : Trie ((t : Ty) × W t)) {ts : List Ty} (xs : Tup W ts),
      insertTupEnv depth env xs = insertTupTrie depth env xs
  | _, _, [], () => rfl
  | depth, _env, _ :: _, (_, ws) => insertTupEnv_eq_insertTupTrie (depth + 1) _ ws

private theorem trieCtxMatch_insertTupEnv {W : Ty → Type} {inDepth : Nat}
    {inEnv : Trie ((t : Ty) × W t)} {vs : List ((t : Ty) × W t)}
    (hm : TrieCtxMatch inDepth inEnv vs) {ts : List Ty} (ws : Tup W ts) :
    TrieCtxMatch (inDepth + ts.length) (insertTupEnv inDepth inEnv ws) (pushTup ws vs) := by
  rw [insertTupEnv_eq_insertTupTrie]
  exact hm.pushTup ws

private theorem trieCtxMatch_initEnv {W : Ty → Type} (fresh : ∀ {t : Ty}, K t → Nat → W t)
    (as : List Ty) :
    TrieCtxMatch as.length (initEnv fresh as)
      (pushTup (tupFreshWith fresh as (Tup.levels as 0) 0) []) := by
  dsimp only [initEnv]
  rw [insertTupEnv_eq_insertTupTrie]
  simpa [Nat.zero_add] using
    TrieCtxMatch.pushTup (tupFreshWith fresh as (Tup.levels as 0) 0) TrieCtxMatch.empty

private theorem denoteArg_eq_some_resolveArg {Γ : List Ty} {W : Ty → Type} {inDepth : Nat}
    {inEnv : Trie ((t : Ty) × W t)} {vs : List ((t : Ty) × W t)}
    (hΓ : CtxTypes Γ vs) (hm : TrieCtxMatch inDepth inEnv vs)
    {t : Ty} (a : Arg K t) (hc : checkArg Γ t a = true) :
    denoteArg vs a = some (resolveArg inDepth inEnv a) := by
  cases a with
  | imm c => rfl
  | var idx =>
    obtain ⟨w, hgetvs, hlt⟩ := ctxTypes_listGet? hΓ (checkArg_eq_true_iff.mp hc)
    have hfind := hm.2 idx hlt
    rw [hgetvs] at hfind
    have hcast : castTy t t w = some w := PassFlatKit.castTy_self t w
    dsimp only [denoteArg, lookupV, resolveArg]
    rw [hgetvs, hfind]; dsimp only
    rw [hcast]

private theorem denoteArgs_eq_some_resolveArgs {Γ : List Ty} {W : Ty → Type} {inDepth : Nat}
    {inEnv : Trie ((t : Ty) × W t)} {vs : List ((t : Ty) × W t)}
    (hΓ : CtxTypes Γ vs) (hm : TrieCtxMatch inDepth inEnv vs) :
    {ts : List Ty} → (as : Tup (Arg K) ts) → checkArgs Γ as = true →
    denoteArgs vs as = some (resolveArgs inDepth inEnv as)
  | [], (), _ => rfl
  | _ :: _, (a, as), hc => by
    dsimp only [checkArgs] at hc; simp only [Bool.and_eq_true] at hc
    dsimp only [denoteArgs, resolveArgs]
    rw [denoteArg_eq_some_resolveArg hΓ hm a hc.1,
      denoteArgs_eq_some_resolveArgs hΓ hm as hc.2]

private theorem lookupL_jump_eq {Δ : List (List Ty)} {ls : List ((ts : List Ty) × KL ts)}
    (hΔ : CtxTypes Δ ls) (hll : CtxLevels ls) {ts : List Ty} {j : Nat}
    (hj : (match listGet? Δ j with
      | some ts' => match listTyDecEq ts' ts with | isTrue _ => true | isFalse _ => false
      | none => false) = true) :
    ∃ lvl, lookupL ls ts j = some lvl ∧
      (if lvl < ls.length then ls.length - 1 - lvl else ls.length) = j := by
  obtain ⟨lvl, hgetls, hlt⟩ := ctxTypes_listGet? hΔ (checkJump_eq_true_iff.mp hj)
  dsimp only [KL] at lvl
  have hlvl : lvl = ls.length - 1 - j := hll j ts lvl hgetls
  have hlk : lookupL ls ts j = some lvl := by
    dsimp only [lookupL]; rw [hgetls]; dsimp only; rw [PassFlatKit.castListTy_self]
  refine ⟨lvl, hlk, ?_⟩
  subst hlvl
  have hlt' : ls.length - 1 - j < ls.length := by omega
  have hinv : ls.length - 1 - (ls.length - 1 - j) = j := by omega
  simp [hlt', hinv]

/-! ## 1. `foldFlat` Simulation Proofs -/

private theorem fold_let_eq {V : Ty → Type} {L : List Ty → Type} {ts rs : List Ty}
    (next : Nat) (op : Op (FVal V) ts) (k : Tup (FVal V) ts → Expr (FVal V) L rs) :
    fold next (.let_ op k) =
      match op.simpAct with
      | some act => fold next (k (act.apply op.args))
      | none =>
        match op.simpProv? with
        | some res => fold next (k res)
        | none =>
          .let_ op.foldRewrite fun xs => fold (next + ts.length) (k (op.foldWrap next xs)) := by
  rw [fold.eq_def]
  dsimp only
  cases op.simpAct <;> cases op.simpProv? <;> rfl

private theorem fold_jnz_eq {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (next : Nat) (c : Arg (FVal V) .bool) (t e : Expr (FVal V) L rs) :
    fold next (.jnz c t e) =
      match c.fout with
      | .imm true => fold next t
      | .imm false => fold next e
      | .var v => .jnz (.var v) (fold next t) (fold next e) := by
  rw [fold.eq_def]
  dsimp only
  cases c.fout with
  | imm b => cases b <;> rfl
  | var _ => rfl

mutual
private theorem foldFlatAux_eq {rs : List Ty} :
    (tf : TFlat rs) → {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × FVal K t)} → {ls : List ((ts : List Ty) × KL ts)} →
    {inDepth outDepth : Nat} → {inEnv : Trie ((t : Ty) × FVal K t)} →
    CtxTypes Γ vs → CtxTypes Δ ls → CtxLevels ls →
    TrieCtxMatch inDepth inEnv vs → tf.wfCheck Γ Δ = true →
    toTFlat (fold outDepth (denote (FVal K) KL tf vs ls)) outDepth ls.length =
      foldFlatAux tf inDepth inEnv outDepth
  | .let_ (ts := ts) op k, Γ, Δ, vs, ls, inDepth, outDepth, inEnv, hΓ, hΔ, hll, hm, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    rw [foldFlatAux.eq_def]
    dsimp only [denote]
    rw [denoteArgs_eq_some_resolveArgs hΓ hm op.args hwf.1]
    dsimp only
    rw [fold_let_eq]
    dsimp only
    cases
      (⟨op.code, resolveArgs inDepth inEnv op.args⟩ : Op (FVal K) ts).simpAct with
    | some act =>
      dsimp only
      exact foldFlatAux_eq k (CtxTypes.push _ hΓ) hΔ hll (trieCtxMatch_insertTupEnv hm _) hwf.2
    | none =>
      dsimp only
      cases
        (⟨op.code, resolveArgs inDepth inEnv op.args⟩ : Op (FVal K) ts).simpProv? with
      | some res =>
        dsimp only
        exact foldFlatAux_eq k (CtxTypes.push _ hΓ) hΔ hll (trieCtxMatch_insertTupEnv hm _) hwf.2
      | none =>
        dsimp only [toTFlat]
        exact congrArg (TFlat.let_ _)
          (foldFlatAux_eq k (CtxTypes.push _ hΓ) hΔ hll (trieCtxMatch_insertTupEnv hm _) hwf.2)
  | .load t a k, Γ, Δ, vs, ls, inDepth, outDepth, inEnv, hΓ, hΔ, hll, hm, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [foldFlatAux, denote]
    rw [denoteArg_eq_some_resolveArg hΓ hm a hwf.1]
    dsimp only [fold, toTFlat]
    exact congrArg (TFlat.load t _)
      (foldFlatAux_eq k (.cons hΓ) hΔ hll (hm.cons t _) hwf.2)
  | .store v a k, Γ, Δ, vs, ls, inDepth, outDepth, inEnv, hΓ, hΔ, hll, hm, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [foldFlatAux, denote]
    rw [denoteArg_eq_some_resolveArg hΓ hm v hwf.1.1,
      denoteArg_eq_some_resolveArg hΓ hm a hwf.1.2]
    dsimp only [fold, toTFlat]
    exact congrArg (TFlat.store _ _) (foldFlatAux_eq k hΓ hΔ hll hm hwf.2)
  | .call f bs args k, Γ, Δ, vs, ls, inDepth, outDepth, inEnv, hΓ, hΔ, hll, hm, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [foldFlatAux, denote]
    rw [denoteArgs_eq_some_resolveArgs hΓ hm args hwf.1]
    dsimp only [fold, toTFlat]
    exact congrArg (TFlat.call f bs _)
      (foldFlatAux_eq k (CtxTypes.push _ hΓ) hΔ hll (trieCtxMatch_insertTupEnv hm _) hwf.2)
  | .jnz c t e, Γ, Δ, vs, ls, inDepth, outDepth, inEnv, hΓ, hΔ, hll, hm, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    rw [foldFlatAux.eq_def]
    dsimp only [denote]
    rw [denoteArg_eq_some_resolveArg hΓ hm c hwf.1.1]
    dsimp only
    rw [fold_jnz_eq]
    cases hc : (resolveArg inDepth inEnv c).fout with
    | imm b =>
      cases b with
      | true => exact foldFlatAux_eq t hΓ hΔ hll hm hwf.1.2
      | false => exact foldFlatAux_eq e hΓ hΔ hll hm hwf.2
    | var v =>
      dsimp only [toTFlat]
      rw [foldFlatAux_eq t hΓ hΔ hll hm hwf.1.2, foldFlatAux_eq e hΓ hΔ hll hm hwf.2]
  | .jump (ts := ts) j args, Γ, Δ, vs, ls, inDepth, outDepth, inEnv, hΓ, hΔ, hll, hm, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨lvl, hlk, hidx⟩ := lookupL_jump_eq hΔ hll hwf.1
    dsimp only [foldFlatAux, denote]
    rw [hlk, denoteArgs_eq_some_resolveArgs hΓ hm args hwf.2]
    dsimp only [fold, toTFlat]
    rw [hidx]
  | .ret vs', Γ, _, vs, ls, inDepth, outDepth, inEnv, hΓ, _, _, hm, hwf => by
    dsimp only [foldFlatAux, denote]
    rw [denoteArgs_eq_some_resolveArgs hΓ hm vs' hwf]
    rfl
  | .exit f args, Γ, _, vs, ls, inDepth, outDepth, inEnv, hΓ, _, _, hm, hwf => by
    dsimp only [foldFlatAux, denote]
    rw [denoteArgs_eq_some_resolveArgs hΓ hm args hwf]
    rfl
  | .hlt, _, _, _, _, _, _, _, _, _, _, _, _ => rfl
  | .group (sig := sig) bodies k, Γ, Δ, vs, ls, inDepth, outDepth, inEnv,
      hΓ, hΔ, hll, hm, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [foldFlatAux, denote, fold, toTFlat]
    have hb := foldFlatAuxB_eq bodies hΓ (CtxTypes.push (Tup.levels sig ls.length) hΔ)
      hll.pushTup hm hwf.1 (outDepth := outDepth)
    have hk := foldFlatAux_eq k hΓ (CtxTypes.push (Tup.levels sig ls.length) hΔ)
      hll.pushTup hm hwf.2 (outDepth := outDepth)
    rw [pushTup_length (Tup.levels sig ls.length) ls] at hb hk
    rw [hb, hk]

private theorem foldFlatAuxB_eq {rs : List Ty} :
    {sig : List (List Ty)} → (tb : TBlocks rs sig) →
    {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × FVal K t)} → {ls : List ((ts : List Ty) × KL ts)} →
    {inDepth outDepth : Nat} → {inEnv : Trie ((t : Ty) × FVal K t)} →
    CtxTypes Γ vs → CtxTypes Δ ls → CtxLevels ls →
    TrieCtxMatch inDepth inEnv vs → tb.wfCheck Γ Δ = true →
    toTBlocks (foldB outDepth (denoteB (FVal K) KL tb vs ls)) outDepth ls.length =
      foldFlatAuxB tb inDepth inEnv outDepth
  | _, .nil, _, _, _, _, _, _, _, _, _, _, _, _ => rfl
  | _, .cons (ts := ts) b bs, Γ, Δ, vs, ls, inDepth, outDepth, inEnv,
      hΓ, hΔ, hll, hm, hwf => by
    dsimp only [TBlocks.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [foldFlatAuxB, denoteB, foldB, toTBlocks]
    refine congr (congrArg TBlocks.cons ?_) ?_
    · exact foldFlatAux_eq b (CtxTypes.push _ hΓ) hΔ hll (trieCtxMatch_insertTupEnv hm _) hwf.1
    · exact foldFlatAuxB_eq bs hΓ hΔ hll hm hwf.2
end

/-- `foldFlat as tf = reifyFunc (Func.fold (denoteFunc tf))` under `wfCheck = true`. -/
theorem foldFlat_eq {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    foldFlat as tf = reifyFunc (Func.fold (denoteFunc (as := as) tf)) := by
  have h := foldFlatAux_eq tf (CtxTypes.push _ .nil) .nil CtxLevels.nil
    (trieCtxMatch_initEnv FVal.fresh as) hwf (outDepth := as.length)
  exact h.symm

/-- `denoteFunc (foldFlat as tf) = Func.fold (denoteFunc tf)` under `wfCheck = true`. -/
theorem denoteFunc_foldFlat {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    denoteFunc (as := as) (foldFlat as tf) = Func.fold (denoteFunc (as := as) tf) := by
  rw [foldFlat_eq tf hwf]
  exact Func.renorm_eq_self (Func.fold_wf (Func.wf_of_denote tf rfl))

/-- `foldFlat` preserves `wfCheck`. -/
theorem foldFlat_wfCheck {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    (foldFlat as tf).wfCheck (pushTypes as []) [] = true := by
  rw [foldFlat_eq tf hwf]
  exact PassFlatKit.reifyFunc_wfCheck (Func.fold_wf (Func.wf_of_denote tf rfl))

/-- `(foldFlatFn f).toFn = ⟨f.name, f.as, f.rs, Func.fold f.toFn.body⟩` under `wfCheck = true`. -/
theorem foldFlatFn_toFn (f : TFlatFn) (hwf : f.wfCheck = true) :
    (foldFlatFn f).toFn = ⟨f.name, f.as, f.rs, Func.fold f.toFn.body⟩ := by
  dsimp only [foldFlatFn, TFlatFn.toFn]
  rw [denoteFunc_foldFlat f.body hwf]

/-- `foldFlatFn` preserves `TFlatFn.wfCheck`. -/
theorem foldFlatFn_wfCheck (f : TFlatFn) (hwf : f.wfCheck = true) :
    (foldFlatFn f).wfCheck = true :=
  foldFlat_wfCheck f.body hwf

/-! ## 2. `copyFlat` Simulation Proofs -/

private theorem mkpairEmitStep_emit_next {V : Ty → Type} {b next' : Nat} {a b' : Ty}
    {cx : CVal V a} {cy : CVal V b'} {op' : Op V [.pair a b']}
    {wrap : Tup V [.pair a b'] → Tup (CVal V) [.pair a b']}
    (h : mkpairEmitStep b a b' cx cy = .emit op' next' wrap) :
    next' = b + ([Ty.pair a b']).length := by
  dsimp only [mkpairEmitStep] at h; cases h; rfl

private theorem mkpairProjStep_emit_next {V : Ty → Type} {b next' : Nat} {a b' : Ty}
    {cx : CVal V a} {cy : CVal V b'} {op' : Op V [.pair a b']}
    {wrap : Tup V [.pair a b'] → Tup (CVal V) [.pair a b']}
    (h : mkpairProjStep b a b' cx cy = .emit op' next' wrap) :
    next' = b + ([Ty.pair a b']).length := by
  dsimp only [mkpairProjStep] at h
  split at h
  · split at h
    · split at h
      · cases h
      · exact mkpairEmitStep_emit_next h
    · exact mkpairEmitStep_emit_next h
  · exact mkpairEmitStep_emit_next h

private theorem copyLet_emit_next {V : Ty → Type} {ts : List Ty} (op : Op (CVal V) ts)
    (b next' : Nat) (op' : Op V ts) (wrap : Tup V ts → Tup (CVal V) ts)
    (h : op.copyLet b = .emit op' next' wrap) :
    next' = b + ts.length := by
  rcases op with ⟨code, args⟩
  cases code with
  | copy _ => rcases args with ⟨_, ⟨⟩⟩; dsimp only [Op.copyLet] at h; cases h
  | unpair a b' =>
    rcases args with ⟨p, ⟨⟩⟩; dsimp only [Op.copyLet] at h
    cases hp : p.toCVal.parts <;> simp only [hp] at h
    · cases h; rfl
    · cases h
  | mkpair a b' =>
    rcases args with ⟨x, y, ⟨⟩⟩; dsimp only [Op.copyLet, mkpairStep] at h
    split at h
    · cases h
    · exact mkpairProjStep_emit_next h
  | _ =>
    all_goals (dsimp only [Op.copyLet] at h; cases h; rfl)

private theorem copy_let_eq {V : Ty → Type} {L : List Ty → Type} {ts rs : List Ty}
    (next : Nat) (op : Op (CVal V) ts) (k : Tup (CVal V) ts → Expr (CVal V) L rs) :
    copy next (.let_ op k) =
      match op.copyLet next with
      | .elim res => copy next (k res)
      | .emit op' next' wrap => .let_ op' fun xs => copy next' (k (wrap xs)) := by
  rw [copy.eq_def]
  dsimp only
  cases op.copyLet next <;> rfl

mutual
private theorem copyFlatAux_eq {rs : List Ty} :
    (tf : TFlat rs) → {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × CVal K t)} → {ls : List ((ts : List Ty) × KL ts)} →
    {inDepth outDepth : Nat} → {inEnv : Trie ((t : Ty) × CVal K t)} →
    CtxTypes Γ vs → CtxTypes Δ ls → CtxLevels ls →
    TrieCtxMatch inDepth inEnv vs → tf.wfCheck Γ Δ = true →
    toTFlat (copy outDepth (denote (CVal K) KL tf vs ls)) outDepth ls.length =
      copyFlatAux tf inDepth inEnv outDepth
  | .let_ (ts := ts) op k, Γ, Δ, vs, ls, inDepth, outDepth, inEnv, hΓ, hΔ, hll, hm, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    rw [copyFlatAux.eq_def]
    dsimp only [denote]
    rw [denoteArgs_eq_some_resolveArgs hΓ hm op.args hwf.1]
    dsimp only
    rw [copy_let_eq]
    cases hst :
      (⟨op.code, resolveArgs inDepth inEnv op.args⟩ : Op (CVal K) ts).copyLet outDepth with
    | elim res =>
      dsimp only
      exact copyFlatAux_eq k (CtxTypes.push _ hΓ) hΔ hll (trieCtxMatch_insertTupEnv hm _) hwf.2
    | emit op' next' wrap =>
      have hnext := copyLet_emit_next _ outDepth next' op' wrap hst
      dsimp only [toTFlat]
      rw [← hnext]
      exact congrArg (TFlat.let_ _)
        (copyFlatAux_eq k (CtxTypes.push _ hΓ) hΔ hll (trieCtxMatch_insertTupEnv hm _) hwf.2)
  | .load t a k, Γ, Δ, vs, ls, inDepth, outDepth, inEnv, hΓ, hΔ, hll, hm, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [copyFlatAux, denote]
    rw [denoteArg_eq_some_resolveArg hΓ hm a hwf.1]
    dsimp only [copy, toTFlat]
    exact congrArg (TFlat.load t _)
      (copyFlatAux_eq k (.cons hΓ) hΔ hll (hm.cons t _) hwf.2)
  | .store v a k, Γ, Δ, vs, ls, inDepth, outDepth, inEnv, hΓ, hΔ, hll, hm, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [copyFlatAux, denote]
    rw [denoteArg_eq_some_resolveArg hΓ hm v hwf.1.1,
      denoteArg_eq_some_resolveArg hΓ hm a hwf.1.2]
    dsimp only [copy, toTFlat]
    exact congrArg (TFlat.store _ _) (copyFlatAux_eq k hΓ hΔ hll hm hwf.2)
  | .call f bs args k, Γ, Δ, vs, ls, inDepth, outDepth, inEnv, hΓ, hΔ, hll, hm, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [copyFlatAux, denote]
    rw [denoteArgs_eq_some_resolveArgs hΓ hm args hwf.1]
    dsimp only [copy, toTFlat]
    exact congrArg (TFlat.call f bs _)
      (copyFlatAux_eq k (CtxTypes.push _ hΓ) hΔ hll (trieCtxMatch_insertTupEnv hm _) hwf.2)
  | .jnz c t e, Γ, Δ, vs, ls, inDepth, outDepth, inEnv, hΓ, hΔ, hll, hm, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [copyFlatAux, denote]
    rw [denoteArg_eq_some_resolveArg hΓ hm c hwf.1.1]
    dsimp only [copy, toTFlat]
    rw [copyFlatAux_eq t hΓ hΔ hll hm hwf.1.2, copyFlatAux_eq e hΓ hΔ hll hm hwf.2]
  | .jump (ts := ts) j args, Γ, Δ, vs, ls, inDepth, outDepth, inEnv, hΓ, hΔ, hll, hm, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨lvl, hlk, hidx⟩ := lookupL_jump_eq hΔ hll hwf.1
    dsimp only [copyFlatAux, denote]
    rw [hlk, denoteArgs_eq_some_resolveArgs hΓ hm args hwf.2]
    dsimp only [copy, toTFlat]
    rw [hidx]
  | .ret vs', Γ, _, vs, ls, inDepth, outDepth, inEnv, hΓ, _, _, hm, hwf => by
    dsimp only [copyFlatAux, denote]
    rw [denoteArgs_eq_some_resolveArgs hΓ hm vs' hwf]
    rfl
  | .exit f args, Γ, _, vs, ls, inDepth, outDepth, inEnv, hΓ, _, _, hm, hwf => by
    dsimp only [copyFlatAux, denote]
    rw [denoteArgs_eq_some_resolveArgs hΓ hm args hwf]
    rfl
  | .hlt, _, _, _, _, _, _, _, _, _, _, _, _ => rfl
  | .group (sig := sig) bodies k, Γ, Δ, vs, ls, inDepth, outDepth, inEnv,
      hΓ, hΔ, hll, hm, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [copyFlatAux, denote, copy, toTFlat]
    have hb := copyFlatAuxB_eq bodies hΓ (CtxTypes.push (Tup.levels sig ls.length) hΔ)
      hll.pushTup hm hwf.1 (outDepth := outDepth)
    have hk := copyFlatAux_eq k hΓ (CtxTypes.push (Tup.levels sig ls.length) hΔ)
      hll.pushTup hm hwf.2 (outDepth := outDepth)
    rw [pushTup_length (Tup.levels sig ls.length) ls] at hb hk
    rw [hb, hk]

private theorem copyFlatAuxB_eq {rs : List Ty} :
    {sig : List (List Ty)} → (tb : TBlocks rs sig) →
    {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × CVal K t)} → {ls : List ((ts : List Ty) × KL ts)} →
    {inDepth outDepth : Nat} → {inEnv : Trie ((t : Ty) × CVal K t)} →
    CtxTypes Γ vs → CtxTypes Δ ls → CtxLevels ls →
    TrieCtxMatch inDepth inEnv vs → tb.wfCheck Γ Δ = true →
    toTBlocks (copyB outDepth (denoteB (CVal K) KL tb vs ls)) outDepth ls.length =
      copyFlatAuxB tb inDepth inEnv outDepth
  | _, .nil, _, _, _, _, _, _, _, _, _, _, _, _ => rfl
  | _, .cons (ts := ts) b bs, Γ, Δ, vs, ls, inDepth, outDepth, inEnv,
      hΓ, hΔ, hll, hm, hwf => by
    dsimp only [TBlocks.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [copyFlatAuxB, denoteB, copyB, toTBlocks]
    refine congr (congrArg TBlocks.cons ?_) ?_
    · exact copyFlatAux_eq b (CtxTypes.push _ hΓ) hΔ hll (trieCtxMatch_insertTupEnv hm _) hwf.1
    · exact copyFlatAuxB_eq bs hΓ hΔ hll hm hwf.2
end

/-- `copyFlat as tf = reifyFunc (Func.copy (denoteFunc tf))` under `wfCheck = true`. -/
theorem copyFlat_eq {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    copyFlat as tf = reifyFunc (Func.copy (denoteFunc (as := as) tf)) := by
  have h := copyFlatAux_eq tf (CtxTypes.push _ .nil) .nil CtxLevels.nil
    (trieCtxMatch_initEnv CVal.fresh as) hwf (outDepth := as.length)
  exact h.symm

/-- `denoteFunc (copyFlat as tf) = Func.copy (denoteFunc tf)` under `wfCheck = true`. -/
theorem denoteFunc_copyFlat {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    denoteFunc (as := as) (copyFlat as tf) = Func.copy (denoteFunc (as := as) tf) := by
  rw [copyFlat_eq tf hwf]
  exact Func.renorm_eq_self (Func.copy_wf (Func.wf_of_denote tf rfl))

/-- `copyFlat` preserves `wfCheck`. -/
theorem copyFlat_wfCheck {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    (copyFlat as tf).wfCheck (pushTypes as []) [] = true := by
  rw [copyFlat_eq tf hwf]
  exact PassFlatKit.reifyFunc_wfCheck (Func.copy_wf (Func.wf_of_denote tf rfl))

/-- `(copyFlatFn f).toFn = ⟨f.name, f.as, f.rs, Func.copy f.toFn.body⟩` under `wfCheck = true`. -/
theorem copyFlatFn_toFn (f : TFlatFn) (hwf : f.wfCheck = true) :
    (copyFlatFn f).toFn = ⟨f.name, f.as, f.rs, Func.copy f.toFn.body⟩ := by
  dsimp only [copyFlatFn, TFlatFn.toFn]
  rw [denoteFunc_copyFlat f.body hwf]

/-- `copyFlatFn` preserves `TFlatFn.wfCheck`. -/
theorem copyFlatFn_wfCheck (f : TFlatFn) (hwf : f.wfCheck = true) :
    (copyFlatFn f).wfCheck = true :=
  copyFlat_wfCheck f.body hwf

/-! ## 3. `canonFlat` Simulation Proofs -/

mutual
private theorem canonFlatAux_eq {rs : List Ty} :
    (tf : TFlat rs) → {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × CanonVal K t)} → {ls : List ((ts : List Ty) × KL ts)} →
    {inDepth outDepth : Nat} → {inEnv : Trie ((t : Ty) × CanonVal K t)} →
    CtxTypes Γ vs → CtxTypes Δ ls → CtxLevels ls →
    TrieCtxMatch inDepth inEnv vs → tf.wfCheck Γ Δ = true →
    toTFlat (canon outDepth (denote (CanonVal K) KL tf vs ls)) outDepth ls.length =
      canonFlatAux tf inDepth inEnv outDepth
  | .let_ (ts := ts) op k, Γ, Δ, vs, ls, inDepth, outDepth, inEnv, hΓ, hΔ, hll, hm, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [canonFlatAux, denote]
    rw [denoteArgs_eq_some_resolveArgs hΓ hm op.args hwf.1]
    dsimp only [canon, toTFlat]
    exact congrArg (TFlat.let_ _)
      (canonFlatAux_eq k (CtxTypes.push _ hΓ) hΔ hll (trieCtxMatch_insertTupEnv hm _) hwf.2)
  | .load t a k, Γ, Δ, vs, ls, inDepth, outDepth, inEnv, hΓ, hΔ, hll, hm, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [canonFlatAux, denote]
    rw [denoteArg_eq_some_resolveArg hΓ hm a hwf.1]
    dsimp only [canon, toTFlat]
    exact congrArg (TFlat.load t _)
      (canonFlatAux_eq k (.cons hΓ) hΔ hll (hm.cons t _) hwf.2)
  | .store v a k, Γ, Δ, vs, ls, inDepth, outDepth, inEnv, hΓ, hΔ, hll, hm, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [canonFlatAux, denote]
    rw [denoteArg_eq_some_resolveArg hΓ hm v hwf.1.1,
      denoteArg_eq_some_resolveArg hΓ hm a hwf.1.2]
    dsimp only [canon, toTFlat]
    exact congrArg (TFlat.store _ _) (canonFlatAux_eq k hΓ hΔ hll hm hwf.2)
  | .call f bs args k, Γ, Δ, vs, ls, inDepth, outDepth, inEnv, hΓ, hΔ, hll, hm, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [canonFlatAux, denote]
    rw [denoteArgs_eq_some_resolveArgs hΓ hm args hwf.1]
    dsimp only [canon, toTFlat]
    exact congrArg (TFlat.call f bs _)
      (canonFlatAux_eq k (CtxTypes.push _ hΓ) hΔ hll (trieCtxMatch_insertTupEnv hm _) hwf.2)
  | .jnz c t e, Γ, Δ, vs, ls, inDepth, outDepth, inEnv, hΓ, hΔ, hll, hm, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [canonFlatAux, denote]
    rw [denoteArg_eq_some_resolveArg hΓ hm c hwf.1.1]
    dsimp only [canon, toTFlat]
    rw [canonFlatAux_eq t hΓ hΔ hll hm hwf.1.2, canonFlatAux_eq e hΓ hΔ hll hm hwf.2]
  | .jump (ts := ts) j args, Γ, Δ, vs, ls, inDepth, outDepth, inEnv, hΓ, hΔ, hll, hm, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨lvl, hlk, hidx⟩ := lookupL_jump_eq hΔ hll hwf.1
    dsimp only [canonFlatAux, denote]
    rw [hlk, denoteArgs_eq_some_resolveArgs hΓ hm args hwf.2]
    dsimp only [canon, toTFlat]
    rw [hidx]
  | .ret vs', Γ, _, vs, ls, inDepth, outDepth, inEnv, hΓ, _, _, hm, hwf => by
    dsimp only [canonFlatAux, denote]
    rw [denoteArgs_eq_some_resolveArgs hΓ hm vs' hwf]
    rfl
  | .exit f args, Γ, _, vs, ls, inDepth, outDepth, inEnv, hΓ, _, _, hm, hwf => by
    dsimp only [canonFlatAux, denote]
    rw [denoteArgs_eq_some_resolveArgs hΓ hm args hwf]
    rfl
  | .hlt, _, _, _, _, _, _, _, _, _, _, _, _ => rfl
  | .group (sig := sig) bodies k, Γ, Δ, vs, ls, inDepth, outDepth, inEnv,
      hΓ, hΔ, hll, hm, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [canonFlatAux, denote, canon, toTFlat]
    have hb := canonFlatAuxB_eq bodies hΓ (CtxTypes.push (Tup.levels sig ls.length) hΔ)
      hll.pushTup hm hwf.1 (outDepth := outDepth)
    have hk := canonFlatAux_eq k hΓ (CtxTypes.push (Tup.levels sig ls.length) hΔ)
      hll.pushTup hm hwf.2 (outDepth := outDepth)
    rw [pushTup_length (Tup.levels sig ls.length) ls] at hb hk
    rw [hb, hk]

private theorem canonFlatAuxB_eq {rs : List Ty} :
    {sig : List (List Ty)} → (tb : TBlocks rs sig) →
    {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × CanonVal K t)} → {ls : List ((ts : List Ty) × KL ts)} →
    {inDepth outDepth : Nat} → {inEnv : Trie ((t : Ty) × CanonVal K t)} →
    CtxTypes Γ vs → CtxTypes Δ ls → CtxLevels ls →
    TrieCtxMatch inDepth inEnv vs → tb.wfCheck Γ Δ = true →
    toTBlocks (canonB outDepth (denoteB (CanonVal K) KL tb vs ls)) outDepth ls.length =
      canonFlatAuxB tb inDepth inEnv outDepth
  | _, .nil, _, _, _, _, _, _, _, _, _, _, _, _ => rfl
  | _, .cons (ts := ts) b bs, Γ, Δ, vs, ls, inDepth, outDepth, inEnv,
      hΓ, hΔ, hll, hm, hwf => by
    dsimp only [TBlocks.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [canonFlatAuxB, denoteB, canonB, toTBlocks]
    refine congr (congrArg TBlocks.cons ?_) ?_
    · exact canonFlatAux_eq b (CtxTypes.push _ hΓ) hΔ hll (trieCtxMatch_insertTupEnv hm _) hwf.1
    · exact canonFlatAuxB_eq bs hΓ hΔ hll hm hwf.2
end

/-- `canonFlat as tf = reifyFunc (Func.canon (denoteFunc tf))` under `wfCheck = true`. -/
theorem canonFlat_eq {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    canonFlat as tf = reifyFunc (Func.canon (denoteFunc (as := as) tf)) := by
  have h := canonFlatAux_eq tf (CtxTypes.push _ .nil) .nil CtxLevels.nil
    (trieCtxMatch_initEnv CanonVal.fresh as) hwf (outDepth := as.length)
  exact h.symm

/-- `denoteFunc (canonFlat as tf) = Func.canon (denoteFunc tf)` under `wfCheck = true`. -/
theorem denoteFunc_canonFlat {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    denoteFunc (as := as) (canonFlat as tf) = Func.canon (denoteFunc (as := as) tf) := by
  rw [canonFlat_eq tf hwf]
  exact Func.renorm_eq_self (Func.canon_wf (Func.wf_of_denote tf rfl))

/-- `canonFlat` preserves `wfCheck`. -/
theorem canonFlat_wfCheck {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    (canonFlat as tf).wfCheck (pushTypes as []) [] = true := by
  rw [canonFlat_eq tf hwf]
  exact PassFlatKit.reifyFunc_wfCheck (Func.canon_wf (Func.wf_of_denote tf rfl))

/-- `(canonFlatFn f).toFn = ⟨f.name, f.as, f.rs, Func.canon f.toFn.body⟩` under `wfCheck = true`. -/
theorem canonFlatFn_toFn (f : TFlatFn) (hwf : f.wfCheck = true) :
    (canonFlatFn f).toFn = ⟨f.name, f.as, f.rs, Func.canon f.toFn.body⟩ := by
  dsimp only [canonFlatFn, TFlatFn.toFn]
  rw [denoteFunc_canonFlat f.body hwf]

/-- `canonFlatFn` preserves `TFlatFn.wfCheck`. -/
theorem canonFlatFn_wfCheck (f : TFlatFn) (hwf : f.wfCheck = true) :
    (canonFlatFn f).wfCheck = true :=
  canonFlat_wfCheck f.body hwf

/-! ## 4. `gvnFlat` Simulation Proofs -/

private theorem gvn_let_eq {V : Ty → Type} {L : List Ty → Type} {sig ts rs : List Ty}
    (next : Nat) (tbl : GvnTbl V) (code : OpCode sig ts) (args : Tup (Arg (GVal V)) sig)
    (k : Tup (GVal V) ts → Expr (GVal V) L rs) :
    gvn next tbl (.let_ ⟨code, args⟩ k) =
      match tbl.find sig ts code (tupGKey args) with
      | some cached => gvn next tbl (k cached)
      | none =>
        .let_ ⟨code, tupGOut args⟩ fun xs =>
          let gs := freshGVals ts xs next
          gvn (next + ts.length) (tbl.insert sig ts code (tupGKey args) gs) (k gs) := by
  rw [gvn.eq_def]
  dsimp only
  cases tbl.find sig ts code (tupGKey args) <;> rfl

mutual
private theorem gvnFlatAux_eq {rs : List Ty} :
    (tf : TFlat rs) → {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × GVal K t)} → {ls : List ((ts : List Ty) × KL ts)} →
    {inDepth outDepth : Nat} → {inEnv : Trie ((t : Ty) × GVal K t)} → {tbl : GvnTbl K} →
    CtxTypes Γ vs → CtxTypes Δ ls → CtxLevels ls →
    TrieCtxMatch inDepth inEnv vs → tf.wfCheck Γ Δ = true →
    toTFlat (gvn outDepth tbl (denote (GVal K) KL tf vs ls)) outDepth ls.length =
      gvnFlatAux tf inDepth inEnv outDepth tbl
  | .let_ (ts := ts) op k, Γ, Δ, vs, ls, inDepth, outDepth, inEnv, tbl,
      hΓ, hΔ, hll, hm, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    rw [gvnFlatAux.eq_def]
    dsimp only [denote]
    rw [denoteArgs_eq_some_resolveArgs hΓ hm op.args hwf.1]
    dsimp only
    rw [gvn_let_eq]
    dsimp only
    cases tbl.find op.sig ts op.code (tupGKey (resolveArgs inDepth inEnv op.args)) with
    | some cached =>
      dsimp only
      exact gvnFlatAux_eq k (CtxTypes.push _ hΓ) hΔ hll (trieCtxMatch_insertTupEnv hm _) hwf.2
    | none =>
      dsimp only [toTFlat]
      exact congrArg (TFlat.let_ _)
        (gvnFlatAux_eq k (CtxTypes.push _ hΓ) hΔ hll (trieCtxMatch_insertTupEnv hm _) hwf.2)
  | .load t a k, Γ, Δ, vs, ls, inDepth, outDepth, inEnv, tbl, hΓ, hΔ, hll, hm, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [gvnFlatAux, denote]
    rw [denoteArg_eq_some_resolveArg hΓ hm a hwf.1]
    dsimp only [gvn, toTFlat]
    exact congrArg (TFlat.load t _)
      (gvnFlatAux_eq k (.cons hΓ) hΔ hll (hm.cons t _) hwf.2)
  | .store v a k, Γ, Δ, vs, ls, inDepth, outDepth, inEnv, tbl, hΓ, hΔ, hll, hm, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [gvnFlatAux, denote]
    rw [denoteArg_eq_some_resolveArg hΓ hm v hwf.1.1,
      denoteArg_eq_some_resolveArg hΓ hm a hwf.1.2]
    dsimp only [gvn, toTFlat]
    exact congrArg (TFlat.store _ _) (gvnFlatAux_eq k hΓ hΔ hll hm hwf.2)
  | .call f bs args k, Γ, Δ, vs, ls, inDepth, outDepth, inEnv, tbl, hΓ, hΔ, hll, hm, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [gvnFlatAux, denote]
    rw [denoteArgs_eq_some_resolveArgs hΓ hm args hwf.1]
    dsimp only [gvn, toTFlat]
    exact congrArg (TFlat.call f bs _)
      (gvnFlatAux_eq k (CtxTypes.push _ hΓ) hΔ hll (trieCtxMatch_insertTupEnv hm _) hwf.2)
  | .jnz c t e, Γ, Δ, vs, ls, inDepth, outDepth, inEnv, tbl, hΓ, hΔ, hll, hm, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [gvnFlatAux, denote]
    rw [denoteArg_eq_some_resolveArg hΓ hm c hwf.1.1]
    dsimp only [gvn, toTFlat]
    rw [gvnFlatAux_eq t hΓ hΔ hll hm hwf.1.2, gvnFlatAux_eq e hΓ hΔ hll hm hwf.2]
  | .jump (ts := ts) j args, Γ, Δ, vs, ls, inDepth, outDepth, inEnv, _,
      hΓ, hΔ, hll, hm, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨lvl, hlk, hidx⟩ := lookupL_jump_eq hΔ hll hwf.1
    dsimp only [gvnFlatAux, denote]
    rw [hlk, denoteArgs_eq_some_resolveArgs hΓ hm args hwf.2]
    dsimp only [gvn, toTFlat]
    rw [hidx]
  | .ret vs', Γ, _, vs, ls, inDepth, outDepth, inEnv, _, hΓ, _, _, hm, hwf => by
    dsimp only [gvnFlatAux, denote]
    rw [denoteArgs_eq_some_resolveArgs hΓ hm vs' hwf]
    rfl
  | .exit f args, Γ, _, vs, ls, inDepth, outDepth, inEnv, _, hΓ, _, _, hm, hwf => by
    dsimp only [gvnFlatAux, denote]
    rw [denoteArgs_eq_some_resolveArgs hΓ hm args hwf]
    rfl
  | .hlt, _, _, _, _, _, _, _, _, _, _, _, _, _ => rfl
  | .group (sig := sig) bodies k, Γ, Δ, vs, ls, inDepth, outDepth, inEnv, tbl,
      hΓ, hΔ, hll, hm, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [gvnFlatAux, denote, gvn, toTFlat]
    have hb := gvnFlatAuxB_eq bodies hΓ (CtxTypes.push (Tup.levels sig ls.length) hΔ)
      hll.pushTup hm hwf.1 (outDepth := outDepth) (tbl := tbl)
    have hk := gvnFlatAux_eq k hΓ (CtxTypes.push (Tup.levels sig ls.length) hΔ)
      hll.pushTup hm hwf.2 (outDepth := outDepth) (tbl := tbl)
    rw [pushTup_length (Tup.levels sig ls.length) ls] at hb hk
    rw [hb, hk]

private theorem gvnFlatAuxB_eq {rs : List Ty} :
    {sig : List (List Ty)} → (tb : TBlocks rs sig) →
    {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × GVal K t)} → {ls : List ((ts : List Ty) × KL ts)} →
    {inDepth outDepth : Nat} → {inEnv : Trie ((t : Ty) × GVal K t)} → {tbl : GvnTbl K} →
    CtxTypes Γ vs → CtxTypes Δ ls → CtxLevels ls →
    TrieCtxMatch inDepth inEnv vs → tb.wfCheck Γ Δ = true →
    toTBlocks (gvnB outDepth tbl (denoteB (GVal K) KL tb vs ls)) outDepth ls.length =
      gvnFlatAuxB tb inDepth inEnv outDepth tbl
  | _, .nil, _, _, _, _, _, _, _, _, _, _, _, _, _ => rfl
  | _, .cons (ts := ts) b bs, Γ, Δ, vs, ls, inDepth, outDepth, inEnv, tbl,
      hΓ, hΔ, hll, hm, hwf => by
    dsimp only [TBlocks.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [gvnFlatAuxB, denoteB, gvnB, toTBlocks]
    refine congr (congrArg TBlocks.cons ?_) ?_
    · exact gvnFlatAux_eq b (CtxTypes.push _ hΓ) hΔ hll (trieCtxMatch_insertTupEnv hm _) hwf.1
    · exact gvnFlatAuxB_eq bs hΓ hΔ hll hm hwf.2
end

/-- `gvnFlat as tf = reifyFunc (Func.gvn (denoteFunc tf))` under `wfCheck = true`. -/
theorem gvnFlat_eq {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    gvnFlat as tf = reifyFunc (Func.gvn (denoteFunc (as := as) tf)) := by
  have h := gvnFlatAux_eq tf (CtxTypes.push _ .nil) .nil CtxLevels.nil
    (trieCtxMatch_initEnv (fun x next => (x, next)) as) hwf (outDepth := as.length) (tbl := .empty)
  exact h.symm

/-- `denoteFunc (gvnFlat as tf) = Func.gvn (denoteFunc tf)` under `wfCheck = true`. -/
theorem denoteFunc_gvnFlat {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    denoteFunc (as := as) (gvnFlat as tf) = Func.gvn (denoteFunc (as := as) tf) := by
  rw [gvnFlat_eq tf hwf]
  exact Func.renorm_eq_self (Func.gvn_wf (Func.wf_of_denote tf rfl))

/-- `gvnFlat` preserves `wfCheck`. -/
theorem gvnFlat_wfCheck {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    (gvnFlat as tf).wfCheck (pushTypes as []) [] = true := by
  rw [gvnFlat_eq tf hwf]
  exact PassFlatKit.reifyFunc_wfCheck (Func.gvn_wf (Func.wf_of_denote tf rfl))

/-- `(gvnFlatFn f).toFn = ⟨f.name, f.as, f.rs, Func.gvn f.toFn.body⟩` under `wfCheck = true`. -/
theorem gvnFlatFn_toFn (f : TFlatFn) (hwf : f.wfCheck = true) :
    (gvnFlatFn f).toFn = ⟨f.name, f.as, f.rs, Func.gvn f.toFn.body⟩ := by
  dsimp only [gvnFlatFn, TFlatFn.toFn]
  rw [denoteFunc_gvnFlat f.body hwf]

/-- `gvnFlatFn` preserves `TFlatFn.wfCheck`. -/
theorem gvnFlatFn_wfCheck (f : TFlatFn) (hwf : f.wfCheck = true) :
    (gvnFlatFn f).wfCheck = true :=
  gvnFlat_wfCheck f.body hwf

end OptFlatValue
end LeanQbe.T
