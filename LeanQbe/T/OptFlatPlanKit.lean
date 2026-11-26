module

public import LeanQbe.T.FlatDirectLemmas
public import LeanQbe.T.SimplifyGroupPlan

/-!
# Shared `Trie`-Env, `PlanLFlat`, and `BoolL` Validator Kit (`OptFlatPlanKit`)

Consolidates `Trie` environment helpers and `TrieCtxMatch` lemmas across `OptFlat*`, and exports
`PlanLFlat`, `PlanLFlatMatch`, `TrieRelMatch`, and generic `BoolL` validator simulation
(`validateBoolL_eq`) for plan-guided CFG splicing (`SimplifyGroupPlan`/`TailDup`/`JumpThread`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T
namespace OptFlatPlanKit

/-! ## 1. Shared `Trie` Environment & Operand/Label Resolution Helpers -/
/-- Insert a tuple of typed payloads into `env` starting at de Bruijn level `depth`. -/
@[expose] def insertTupEnv {α : Type} {W : α → Type} (depth : Nat)
    (env : Trie ((a : α) × W a)) : {ts : List α} → Tup W ts → Trie ((a : α) × W a)
  | [], () => env | a :: _, (w, ws) => insertTupEnv (depth + 1) (env.insert depth ⟨a, w⟩) ws
/-- Initial `Trie` variable environment populated with fresh parameter wrappers for `as`. -/
@[expose] def initEnv {W : Ty → Type} (fresh : ∀ {t : Ty}, K t → Nat → W t) (as : List Ty) :
    Trie ((t : Ty) × W t) := insertTupEnv 0 .empty (tupFreshWith fresh as (Tup.levels as 0) 0)
/-- Lookup a type-tagged payload at de Bruijn index `idx` under `(inDepth, env)`. -/
@[expose] def lookupEnv {W : Ty → Type} (inDepth : Nat) (env : Trie ((t : Ty) × W t))
    (t : Ty) (idx : Nat) : Option (W t) :=
  match env.find? (inDepth - 1 - idx) with | some ⟨t', w⟩ => castTy t' t w | none => none
/-- Insert `ts.length` fresh payloads `mk t (inD + i) (outD + i)` into `env`. -/
@[expose] def insertFreshWith {W : Ty → Type} (mk : (t : Ty) → Nat → Nat → W t) :
    Nat → Nat → List Ty → Trie ((t : Ty) × W t) → Trie ((t : Ty) × W t)
  | _, _, [], env => env
  | inD, outD, t :: ts, env =>
    insertFreshWith mk (inD + 1) (outD + 1) ts (env.insert inD ⟨t, mk t inD outD⟩)
/-- Resolve a `TFlat` operand in `env` with optional fallback `dflt` for out-of-scope indices. -/
@[expose] def resolveEnvArg {W : Ty → Type} (depth : Nat) (env : Trie ((t : Ty) × W t))
    {t : Ty} (a : Arg K t) (dflt : ∀ t, Arg W t := fun _ => .imm default) : Arg W t :=
  match a with
  | .imm c => .imm c
  | .var idx => match lookupEnv depth env t idx with | some w => .var w | none => dflt t
/-- Resolve a tuple of `TFlat` operands in `env` with optional fallback `dflt`. -/
@[expose] def resolveEnvArgs {W : Ty → Type} (depth : Nat) (env : Trie ((t : Ty) × W t))
    {ts : List Ty} (args : Tup (Arg K) ts)
    (dflt : ∀ t, Arg W t := fun _ => .imm default) : Tup (Arg W) ts :=
  match ts, args with
  | [], () => ()
  | _ :: _, (a, as) => (resolveEnvArg depth env a dflt, resolveEnvArgs depth env as dflt)
/-- Resolve a `TFlat` label index `j` at signature `ts` in a level-indexed `Trie` label env. -/
@[expose] def resolveLabel {W : List Ty → Type} (lDepth : Nat)
    (lEnv : Trie ((ts : List Ty) × W ts)) (ts : List Ty) (j : Nat) : Option (W ts) :=
  match lEnv.find? (lDepth - 1 - j) with | some ⟨ts', w⟩ => castListTy ts' ts w | none => none
/-- Convert an output de Bruijn label level `lbl` into a de Bruijn index at label depth `nl`. -/
@[expose] def idxLabel (nl lbl : Nat) : Nat := if lbl < nl then nl - 1 - lbl else nl
/-- Convert a `TFlat` de Bruijn index operand into a de Bruijn level operand at depth `b`. -/
@[expose] def levelArg (b : Nat) {t : Ty} : Arg K t → Arg K t
  | .var idx => .var (b - 1 - idx) | .imm c => .imm c
/-- Convert a tuple of `TFlat` de Bruijn index operands into de Bruijn level operands. -/
@[expose] def levelArgs (b : Nat) : {ts : List Ty} → Tup (Arg K) ts → Tup (Arg K) ts
  | [], () => () | _ :: _, (a, as) => (levelArg b a, levelArgs b as)

/-! ## 2. `PlanLFlat` & Generic `BoolL` Plan Validators -/
/-- Output-level-based `TFlat` label payload for zero-shift splicing and duplication. -/
inductive PlanLFlat (rs : List Ty) : List Ty → Type
  | keep {ts : List Ty} (outLbl : Nat) : PlanLFlat rs ts
  | dead {ts : List Ty} : PlanLFlat rs ts
  | splice {ts : List Ty} (body : Nat → Nat → Tup (Arg K) ts → TFlat rs) : PlanLFlat rs ts
/-- Tuple of `.dead` `PlanLFlat` labels matching `sig`. -/
@[expose] def deadTupFlat {rs : List Ty} : (sig : List (List Ty)) → Tup (PlanLFlat rs) sig
  | [] => () | _ :: sig => (.dead, deadTupFlat sig)
/-- Expand kept output label levels `Tup KL (SgpImpl.filterSig ks sig)` to `Tup (PlanLFlat rs)`. -/
@[expose] def expandKeepFlat {rs : List Ty} :
    (ks : List Bool) → (sig : List (List Ty)) → Tup KL (SgpImpl.filterSig ks sig) →
    Tup (PlanLFlat rs) sig
  | _, [], () => () | [], _ :: sig, () => (.dead, deadTupFlat sig)
  | true :: ks, _ :: sig, (j, js) => (.keep j, expandKeepFlat ks sig js)
  | false :: ks, _ :: sig, js => (.dead, expandKeepFlat ks sig js)
mutual
/-- Generic structural plan tree parameterized by `.group` metadata `α`. -/
inductive BoolLPlan (α : Type) : Type
  | leaf | node1 (k : BoolLPlan α) | node2 (t e : BoolLPlan α)
  | group (info : α) (bs : BoolLPlanB α) (k : BoolLPlan α)
/-- Block-list companion of `BoolLPlan`. -/
inductive BoolLPlanB (α : Type) : Type | nil | cons (b : BoolLPlan α) (bs : BoolLPlanB α)
end
/-- One group validation pass: evaluate blocks under `lMask` and check `bMask`-selected blocks. -/
structure BoolLPass : Type where
  lMask : List Bool
  bMask : List Bool
  deriving DecidableEq, Repr
/-- Per-group boolean-label validation spec: block validation passes plus continuation mask. -/
structure GroupBoolSpec : Type where
  passes : List BoolLPass
  kMask : List Bool
  deriving DecidableEq, Repr

mutual
/-- Validate each selected block of `TBlocks rs sig` against `bMask` and `pbs`. -/
@[expose] def validateBoolLBlocksFlat {rs : List Ty} (bMask : List Bool)
    (pbs : BoolLPlanB GroupBoolSpec) (inLD : Nat)
    (inLE : Trie ((ts : List Ty) × SgpImpl.BoolL ts)) :
    {sig : List (List Ty)} → TBlocks rs sig → Bool
  | [], .nil => match pbs, bMask with | .nil, [] => true | _, _ => false
  | _ :: _, .cons b bs => match pbs, bMask with
    | .cons pb pbs', true :: ms =>
      validateBoolLFlat pb inLD inLE b && validateBoolLBlocksFlat ms pbs' inLD inLE bs
    | .cons _ pbs', false :: ms => validateBoolLBlocksFlat ms pbs' inLD inLE bs
    | _, _ => false

/-- Generic `O(N)` `TFlat` `BoolL` plan validator matching `validateBoolLPhoas`. -/
@[expose] def validateBoolLFlat {rs : List Ty} (plan : BoolLPlan GroupBoolSpec)
    (inLD : Nat) (inLE : Trie ((ts : List Ty) × SgpImpl.BoolL ts)) : TFlat rs → Bool
  | .let_ _ k | .load _ _ k | .store _ _ k | .call _ _ _ k =>
    match plan with | .node1 pk => validateBoolLFlat pk inLD inLE k | _ => false
  | .jnz _ t e => match plan with
    | .node2 pt pe =>
      validateBoolLFlat pt inLD inLE t && validateBoolLFlat pe inLD inLE e
    | _ => false
  | .jump (ts := ts) j _ =>
    match plan with | .leaf => (resolveLabel inLD inLE ts j).getD false | _ => false
  | .ret _ | .exit _ _ | .hlt => match plan with | .leaf => true | _ => false
  | .group (sig := sig) bodies k => match plan with
    | .group spec pbs pk =>
      (spec.passes.all fun p => validateBoolLBlocksFlat p.bMask pbs (inLD + sig.length)
        (insertTupEnv inLD inLE (SgpImpl.boolTup p.lMask sig)) bodies) &&
      validateBoolLFlat pk (inLD + sig.length)
        (insertTupEnv inLD inLE (SgpImpl.boolTup spec.kMask sig)) k
    | _ => false
end

mutual
/-- Validate each selected block of `Blocks UnitV BoolL rs sig` against `bMask` and `pbs`. -/
@[expose] def validateBoolLBlocksPhoas {rs : List Ty} (bMask : List Bool)
    (pbs : BoolLPlanB GroupBoolSpec) :
    {sig : List (List Ty)} → Blocks SgpImpl.UnitV SgpImpl.BoolL rs sig → Bool
  | [], .nil => match pbs, bMask with | .nil, [] => true | _, _ => false
  | ts :: _, .cons b bs => match pbs, bMask with
    | .cons pb pbs', true :: ms =>
      validateBoolLPhoas pb (b (Tup.units ts)) && validateBoolLBlocksPhoas ms pbs' bs
    | .cons _ pbs', false :: ms => validateBoolLBlocksPhoas ms pbs' bs
    | _, _ => false

/-- Generic PHOAS `BoolL` plan validator matching `validateBoolLFlat`. -/
@[expose] def validateBoolLPhoas {rs : List Ty} (plan : BoolLPlan GroupBoolSpec) :
    Expr SgpImpl.UnitV SgpImpl.BoolL rs → Bool
  | .let_ (ts := ts) _ k =>
    match plan with | .node1 pk => validateBoolLPhoas pk (k (Tup.units ts)) | _ => false
  | .load _ _ k => match plan with | .node1 pk => validateBoolLPhoas pk (k ()) | _ => false
  | .store _ _ k => match plan with | .node1 pk => validateBoolLPhoas pk k | _ => false
  | .call _ (bs := bs) _ k =>
    match plan with | .node1 pk => validateBoolLPhoas pk (k (Tup.units bs)) | _ => false
  | .jnz _ t e => match plan with
    | .node2 pt pe => validateBoolLPhoas pt t && validateBoolLPhoas pe e | _ => false
  | .jump ok _ => match plan with | .leaf => ok | _ => false
  | .ret _ | .exit _ _ | .hlt => match plan with | .leaf => true | _ => false
  | .group (sig := sig) bodies k => match plan with
    | .group spec pbs pk =>
      (spec.passes.all fun p =>
        validateBoolLBlocksPhoas p.bMask pbs (bodies (SgpImpl.boolTup p.lMask sig))) &&
      validateBoolLPhoas pk (k (SgpImpl.boolTup spec.kMask sig))
    | _ => false
end
/-! ## 3. Shared `TrieCtxMatch` & Context Simulation Lemmas -/
theorem ctxTypes_pushTup_rev {α : Type} {f : α → Type} :
    {ts : List α} → (xs : Tup f ts) → {Γ : List α} → {vs : List ((a : α) × f a)} →
    CtxTypes Γ vs → CtxTypes (pushTypes ts Γ) (pushTup xs vs)
  | [], (), _, _, h => h | _ :: _, (_, xs), _, _, h => ctxTypes_pushTup_rev xs (.cons h)
theorem insertTupEnv_eq_insertTupTrie {α : Type} {W : α → Type} :
    ∀ (depth : Nat) (env : Trie ((a : α) × W a)) {ts : List α} (xs : Tup W ts),
      insertTupEnv depth env xs = insertTupTrie depth env xs
  | _, _, [], () => rfl
  | depth, _, _ :: _, (_, ws) => insertTupEnv_eq_insertTupTrie (depth + 1) _ ws
theorem trieCtxMatch_insertTupEnv {α : Type} {W : α → Type} {inDepth : Nat}
    {inEnv : Trie ((a : α) × W a)} {vs : List ((a : α) × W a)}
    (hm : TrieCtxMatch inDepth inEnv vs) {ts : List α} (ws : Tup W ts) :
    TrieCtxMatch (inDepth + ts.length) (insertTupEnv inDepth inEnv ws) (pushTup ws vs) := by
  rw [insertTupEnv_eq_insertTupTrie]; exact hm.pushTup ws
theorem trieCtxMatch_initEnv {W : Ty → Type} (fresh : ∀ {t : Ty}, K t → Nat → W t)
    (as : List Ty) : TrieCtxMatch as.length (initEnv fresh as)
      (pushTup (tupFreshWith fresh as (Tup.levels as 0) 0) []) := by
  dsimp only [initEnv]; rw [insertTupEnv_eq_insertTupTrie]
  simpa [Nat.zero_add] using
    TrieCtxMatch.pushTup (tupFreshWith fresh as (Tup.levels as 0) 0) TrieCtxMatch.empty
/-- Build a fresh tuple `Tup W ts` from `(inD, outD)` matching `insertFreshWith`. -/
@[expose] def mkFreshTup {W : Ty → Type} (mk : (t : Ty) → Nat → Nat → W t) :
    (ts : List Ty) → Nat → Nat → Tup W ts
  | [], _, _ => () | t :: ts, inD, outD => (mk t inD outD, mkFreshTup mk ts (inD + 1) (outD + 1))
theorem insertFreshWith_eq {W : Ty → Type} (mk : (t : Ty) → Nat → Nat → W t) :
    (ts : List Ty) → (inD outD : Nat) → (env : Trie ((t : Ty) × W t)) →
    insertFreshWith mk inD outD ts env = insertTupTrie inD env (mkFreshTup mk ts inD outD)
  | [], _, _, _ => rfl | _ :: ts, inD, outD, _ => insertFreshWith_eq mk ts (inD + 1) (outD + 1) _
theorem trieCtxMatch_insertFreshWith {W : Ty → Type}
    (mk : (t : Ty) → Nat → Nat → W t) {inDepth : Nat} {env : Trie ((t : Ty) × W t)}
    {vs : List ((t : Ty) × W t)} (hm : TrieCtxMatch inDepth env vs)
    (ts : List Ty) (outDepth : Nat) :
    TrieCtxMatch (inDepth + ts.length) (insertFreshWith mk inDepth outDepth ts env)
      (pushTup (mkFreshTup mk ts inDepth outDepth) vs) := by
  rw [insertFreshWith_eq]; exact TrieCtxMatch.pushTup (mkFreshTup mk ts inDepth outDepth) hm
theorem lookupEnv_eq {W : Ty → Type} {Γ : List Ty} {vs : List ((t : Ty) × W t)}
    {inDepth : Nat} {env : Trie ((t : Ty) × W t)} (hΓ : CtxTypes Γ vs)
    (hm : TrieCtxMatch inDepth env vs) {t : Ty} {idx : Nat} (hc : checkArg Γ t (.var idx) = true) :
    lookupEnv inDepth env t idx = lookupV vs t idx := TrieCtxMatch.lookupV_eq hΓ hm hc
theorem denoteArg_eq_some_resolveEnvArg {Γ : List Ty} {W : Ty → Type}
    {inDepth : Nat} {inEnv : Trie ((t : Ty) × W t)} {vs : List ((t : Ty) × W t)}
    (hΓ : CtxTypes Γ vs) (hm : TrieCtxMatch inDepth inEnv vs)
    {t : Ty} (a : Arg K t) (hc : checkArg Γ t a = true)
    (dflt : ∀ t, Arg W t := fun _ => .imm default) :
    denoteArg vs a = some (resolveEnvArg inDepth inEnv a dflt) := by
  cases a with
  | imm _ => rfl
  | var idx =>
    dsimp only [resolveEnvArg, denoteArg]; rw [lookupEnv_eq hΓ hm hc]
    obtain ⟨w, hget, _⟩ := ctxTypes_listGet? hΓ (checkArg_eq_true_iff.mp hc)
    rw [show lookupV vs t idx = some w from by
      dsimp only [lookupV]; rw [hget]; exact PassFlatKit.castTy_self t w]
theorem denoteArgs_eq_some_resolveEnvArgs {Γ : List Ty} {W : Ty → Type}
    {inDepth : Nat} {inEnv : Trie ((t : Ty) × W t)} {vs : List ((t : Ty) × W t)}
    (hΓ : CtxTypes Γ vs) (hm : TrieCtxMatch inDepth inEnv vs) :
    {ts : List Ty} → (as : Tup (Arg K) ts) → checkArgs Γ as = true →
    (dflt : ∀ t, Arg W t := fun _ => .imm default) →
    denoteArgs vs as = some (resolveEnvArgs inDepth inEnv as dflt)
  | [], (), _, _ => rfl
  | _ :: _, (a, as), hc, dflt => by
    simp only [checkArgs, Bool.and_eq_true] at hc; dsimp only [denoteArgs, resolveEnvArgs]
    rw [denoteArg_eq_some_resolveEnvArg hΓ hm a hc.1 dflt,
      denoteArgs_eq_some_resolveEnvArgs hΓ hm as hc.2 dflt]
theorem denoteArg_eq_some_levelArg {Γ : List Ty} {vs : List ((t : Ty) × K t)}
    (hΓ : CtxTypes Γ vs) (hvl : CtxLevels vs) {t : Ty} (a : Arg K t)
    (hc : checkArg Γ t a = true) : denoteArg vs a = some (levelArg vs.length a) := by
  cases a with
  | imm _ => rfl
  | var idx =>
    obtain ⟨lvl, hgetvs, _⟩ := ctxTypes_listGet? hΓ (checkArg_eq_true_iff.mp hc)
    dsimp only [denoteArg, lookupV, levelArg]; rw [hgetvs]; dsimp only
    rw [PassFlatKit.castTy_self, hvl idx t lvl hgetvs]
theorem denoteArgs_eq_some_levelArgs {Γ : List Ty} {vs : List ((t : Ty) × K t)}
    (hΓ : CtxTypes Γ vs) (hvl : CtxLevels vs) :
    {ts : List Ty} → (as : Tup (Arg K) ts) → checkArgs Γ as = true →
    denoteArgs vs as = some (levelArgs vs.length as)
  | [], (), _ => rfl
  | _ :: _, (a, as), hc => by
    simp only [checkArgs, Bool.and_eq_true] at hc; dsimp only [denoteArgs, levelArgs]
    rw [denoteArg_eq_some_levelArg hΓ hvl a hc.1, denoteArgs_eq_some_levelArgs hΓ hvl as hc.2]
theorem lookupL_jump_eq {Δ : List (List Ty)} {ls : List ((ts : List Ty) × KL ts)}
    (hΔ : CtxTypes Δ ls) (hll : CtxLevels ls) {ts : List Ty} {j : Nat}
    (hj : (match listGet? Δ j with
      | some ts' => match listTyDecEq ts' ts with | isTrue _ => true | isFalse _ => false
      | none => false) = true) : ∃ lvl, lookupL ls ts j = some lvl ∧
      (if lvl < ls.length then ls.length - 1 - lvl else ls.length) = j := by
  obtain ⟨lvl, hgetls, _⟩ := ctxTypes_listGet? hΔ (checkJump_eq_true_iff.mp hj)
  have hlvl : lvl = ls.length - 1 - j := hll j ts lvl hgetls
  refine ⟨lvl, by dsimp only [lookupL]; rw [hgetls]; exact PassFlatKit.castListTy_self ts lvl, ?_⟩
  subst hlvl; have hlt' : ls.length - 1 - j < ls.length := by omega
  have hinv : ls.length - 1 - (ls.length - 1 - j) = j := by omega
  simp [hlt', hinv]
theorem lookupL_eq_some_resolveLabel {Δ : List (List Ty)} {W : List Ty → Type}
    {inLD : Nat} {inLE : Trie ((ts : List Ty) × W ts)} {ls : List ((ts : List Ty) × W ts)}
    (hΔ : CtxTypes Δ ls) (hm : TrieCtxMatch inLD inLE ls) {ts : List Ty} {j : Nat}
    (hj : (match listGet? Δ j with
      | some ts' => match listTyDecEq ts' ts with | isTrue _ => true | isFalse _ => false
      | none => false) = true) :
    ∃ w, lookupL ls ts j = some w ∧ resolveLabel inLD inLE ts j = some w := by
  obtain ⟨w, hgetls, hlt⟩ := ctxTypes_listGet? hΔ (checkJump_eq_true_iff.mp hj)
  have hfind := hm.2 j hlt; rw [hgetls] at hfind
  have hcast : castListTy ts ts w = some w := PassFlatKit.castListTy_self ts w
  exact ⟨w, by dsimp only [lookupL]; rw [hgetls]; exact hcast,
    by dsimp only [resolveLabel]; rw [hfind]; exact hcast⟩
/-! ## 4. `PlanLFlatMatch`, `TrieRelMatch`, and `validateBoolL_eq` -/

/-- Simulation relation linking `TFlat` `PlanLFlat` payloads to PHOAS `SgpImpl.PlanL K KL`. -/
@[expose] def PlanLFlatMatch {rs : List Ty} {ts : List Ty} :
    PlanLFlat rs ts → SgpImpl.PlanL K KL rs ts → Prop
  | .keep l₁, .keep l₂ => l₁ = l₂
  | .dead, .dead => True
  | .splice fFlat, .splice fPhoas =>
    ∀ outVD outLD args, fFlat outVD outLD args = toTFlat (fPhoas args) outVD outLD
  | _, _ => False

theorem deadTupFlat_match {rs : List Ty} : (sig : List (List Ty)) →
    TRel (fun _ => PlanLFlatMatch (rs := rs)) (deadTupFlat sig) (SgpImpl.deadTup sig)
  | [] => .nil | _ :: sig => .cons trivial (deadTupFlat_match sig)
theorem expandKeepFlat_match {rs : List Ty} :
    (ks : List Bool) → (sig : List (List Ty)) → (Js : Tup KL (SgpImpl.filterSig ks sig)) →
    TRel (fun _ => PlanLFlatMatch (rs := rs))
      (expandKeepFlat ks sig Js) (SgpImpl.expandKeepLabels ks sig Js)
  | _, [], () => .nil | [], _ :: sig, () => .cons trivial (deadTupFlat_match sig)
  | true :: ks, _ :: sig, (_, js) => .cons rfl (expandKeepFlat_match ks sig js)
  | false :: ks, _ :: sig, js => .cons trivial (expandKeepFlat_match ks sig js)
/-- Generalized agreement between a de Bruijn level `Trie` and a de Bruijn index `List` context
via a type-indexed relation `R`. -/
@[expose] def TrieRelMatch {α : Type} {f₁ f₂ : α → Type} (R : (a : α) → f₁ a → f₂ a → Prop)
    (depth : Nat) (env : Trie ((a : α) × f₁ a)) (vs : List ((a : α) × f₂ a)) : Prop :=
  depth = vs.length ∧ ∀ idx, idx < vs.length → ∃ (a : α) (x₁ : f₁ a) (x₂ : f₂ a),
    env.find? (depth - 1 - idx) = some ⟨a, x₁⟩ ∧ listGet? vs idx = some ⟨a, x₂⟩ ∧ R a x₁ x₂
namespace TrieRelMatch
theorem empty {α : Type} {f₁ f₂ : α → Type} (R : (a : α) → f₁ a → f₂ a → Prop) :
    TrieRelMatch R 0 .empty [] := ⟨rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
theorem cons {α : Type} {f₁ f₂ : α → Type} {R : (a : α) → f₁ a → f₂ a → Prop}
    {depth : Nat} {env : Trie ((a : α) × f₁ a)} {vs : List ((a : α) × f₂ a)}
    (h : TrieRelMatch R depth env vs) {a : α} {x₁ : f₁ a} {x₂ : f₂ a} (hr : R a x₁ x₂) :
    TrieRelMatch R (depth + 1) (env.insert depth ⟨a, x₁⟩) (⟨a, x₂⟩ :: vs) := by
  refine ⟨by rw [h.1, List.length_cons], fun idx hidx => ?_⟩
  cases idx with
  | zero => rw [show depth + 1 - 1 - 0 = depth by omega, Trie.find?_insert_self]
            exact ⟨a, x₁, x₂, rfl, rfl, hr⟩
  | succ i =>
    simp only [List.length_cons, Nat.succ_lt_succ_iff] at hidx
    have hne : depth - 1 - i ≠ depth := by have := h.1; omega
    rw [show depth + 1 - 1 - (i + 1) = depth - 1 - i by omega, Trie.find?_insert_ne _ _ hne]
    exact h.2 i hidx
theorem pushTup {α : Type} {f₁ f₂ : α → Type} {R : (a : α) → f₁ a → f₂ a → Prop} :
    {ts : List α} → {xs₁ : Tup f₁ ts} → {xs₂ : Tup f₂ ts} → TRel R xs₁ xs₂ →
    {depth : Nat} → {env : Trie ((a : α) × f₁ a)} → {vs : List ((a : α) × f₂ a)} →
    TrieRelMatch R depth env vs →
    TrieRelMatch R (depth + ts.length) (insertTupEnv depth env xs₁) (LeanQbe.T.pushTup xs₂ vs)
  | [], (), (), .nil, _, _, _, h => h
  | a :: ts, (_, _), (_, _), .cons hr hrs, depth, _, _, h => by
    dsimp only [insertTupEnv, LeanQbe.T.pushTup]
    have h1 := TrieRelMatch.pushTup hrs (h.cons hr)
    have hlen : depth + (a :: ts).length = depth + 1 + ts.length := by
      simp only [List.length_cons]; omega
    rwa [hlen]
theorem mono {α : Type} {f₁ f₂ : α → Type} {R₁ R₂ : (a : α) → f₁ a → f₂ a → Prop}
    (hsub : ∀ {a x₁ x₂}, R₁ a x₁ x₂ → R₂ a x₁ x₂) {depth : Nat}
    {env : Trie ((a : α) × f₁ a)} {vs : List ((a : α) × f₂ a)}
    (h : TrieRelMatch R₁ depth env vs) : TrieRelMatch R₂ depth env vs :=
  ⟨h.1, fun idx hidx => let ⟨a, x₁, x₂, hf, hg, hr⟩ := h.2 idx hidx; ⟨a, x₁, x₂, hf, hg, hsub hr⟩⟩
theorem resolveLabel_rel {Δ : List (List Ty)} {W₁ W₂ : List Ty → Type}
    {R : (ts : List Ty) → W₁ ts → W₂ ts → Prop}
    {inLD : Nat} {inLE : Trie ((ts : List Ty) × W₁ ts)} {ls : List ((ts : List Ty) × W₂ ts)}
    (hΔ : CtxTypes Δ ls) (hm : TrieRelMatch R inLD inLE ls) {ts : List Ty} {j : Nat}
    (hj : (match listGet? Δ j with
      | some ts' => match listTyDecEq ts' ts with | isTrue _ => true | isFalse _ => false
      | none => false) = true) :
    ∃ (w₁ : W₁ ts) (w₂ : W₂ ts),
      resolveLabel inLD inLE ts j = some w₁ ∧ lookupL ls ts j = some w₂ ∧ R ts w₁ w₂ := by
  obtain ⟨w₂, hgetls, hlt⟩ := ctxTypes_listGet? hΔ (checkJump_eq_true_iff.mp hj)
  obtain ⟨_, x₁, _, hfind, hget', hr⟩ := hm.2 j hlt; rw [hgetls] at hget'; cases hget'
  exact ⟨x₁, w₂, by dsimp only [resolveLabel]; rw [hfind]; exact PassFlatKit.castListTy_self ts x₁,
    by dsimp only [lookupL]; rw [hgetls]; exact PassFlatKit.castListTy_self ts w₂, hr⟩
end TrieRelMatch

mutual
/-- Block-list companion of `validateBoolL_eq`. -/
theorem validateBoolLBlocks_eq {rs : List Ty} (bMask : List Bool)
    (pbs : BoolLPlanB GroupBoolSpec) :
    {sig : List (List Ty)} → (tb : TBlocks rs sig) →
    {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × SgpImpl.UnitV t)} → {ls : List ((ts : List Ty) × SgpImpl.BoolL ts)} →
    {inLD : Nat} → {inLE : Trie ((ts : List Ty) × SgpImpl.BoolL ts)} →
    CtxTypes Γ vs → CtxTypes Δ ls → TrieCtxMatch inLD inLE ls → tb.wfCheck Γ Δ = true →
    validateBoolLBlocksPhoas bMask pbs (denoteB SgpImpl.UnitV SgpImpl.BoolL tb vs ls) =
      validateBoolLBlocksFlat bMask pbs inLD inLE tb
  | [], .nil, _, _, _, _, _, _, _, _, _, _ => by
    dsimp only [denoteB]; cases pbs <;> cases bMask <;> rfl
  | _ :: _, .cons (ts := ts) b bs, _, _, _, _, _, _, hΓ, hΔ, hmL, hwf => by
    simp only [TBlocks.wfCheck, Bool.and_eq_true] at hwf; dsimp only [denoteB]
    cases pbs with
    | nil => rfl
    | cons pb pbs' =>
      cases bMask with
      | nil => rfl
      | cons m ms =>
        cases m
        · exact validateBoolLBlocks_eq ms pbs' bs hΓ hΔ hmL hwf.2
        · simp only [validateBoolLBlocksPhoas, validateBoolLBlocksFlat]
          rw [validateBoolL_eq pb b (ctxTypes_pushTup_rev (Tup.units ts) hΓ) hΔ hmL hwf.1,
            validateBoolLBlocks_eq ms pbs' bs hΓ hΔ hmL hwf.2]

/-- Generic `BoolL` validator simulation (`0` shifts). -/
theorem validateBoolL_eq {rs : List Ty} (plan : BoolLPlan GroupBoolSpec) :
    (tf : TFlat rs) → {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × SgpImpl.UnitV t)} → {ls : List ((ts : List Ty) × SgpImpl.BoolL ts)} →
    {inLD : Nat} → {inLE : Trie ((ts : List Ty) × SgpImpl.BoolL ts)} →
    CtxTypes Γ vs → CtxTypes Δ ls → TrieCtxMatch inLD inLE ls → tf.wfCheck Γ Δ = true →
    validateBoolLPhoas plan (denote SgpImpl.UnitV SgpImpl.BoolL tf vs ls) =
      validateBoolLFlat plan inLD inLE tf
  | .let_ (ts := ts) _ k, _, _, _, _, _, _, hΓ, hΔ, hmL, hwf => by
    simp only [TFlat.wfCheck, Bool.and_eq_true] at hwf
    obtain ⟨_, ha⟩ := Option.isSome_iff_exists.1 (denoteArgs_isSome_of_checkArgs hΓ hwf.1)
    cases plan <;> simp [denote, ha, validateBoolLPhoas, validateBoolLFlat]
    exact validateBoolL_eq _ k (ctxTypes_pushTup_rev (Tup.units ts) hΓ) hΔ hmL hwf.2
  | .load _ _ k, _, _, _, _, _, _, hΓ, hΔ, hmL, hwf => by
    simp only [TFlat.wfCheck, Bool.and_eq_true] at hwf
    obtain ⟨_, ha⟩ := Option.isSome_iff_exists.1 (denoteArg_isSome_of_checkArg hΓ hwf.1)
    cases plan <;> simp [denote, ha, validateBoolLPhoas, validateBoolLFlat]
    exact validateBoolL_eq _ k (.cons hΓ) hΔ hmL hwf.2
  | .store _ _ k, _, _, _, _, _, _, hΓ, hΔ, hmL, hwf => by
    simp only [TFlat.wfCheck, Bool.and_eq_true] at hwf
    obtain ⟨_, hv⟩ := Option.isSome_iff_exists.1 (denoteArg_isSome_of_checkArg hΓ hwf.1.1)
    obtain ⟨_, ha⟩ := Option.isSome_iff_exists.1 (denoteArg_isSome_of_checkArg hΓ hwf.1.2)
    cases plan <;> simp [denote, hv, ha, validateBoolLPhoas, validateBoolLFlat]
    exact validateBoolL_eq _ k hΓ hΔ hmL hwf.2
  | .call _ bs _ k, _, _, _, _, _, _, hΓ, hΔ, hmL, hwf => by
    simp only [TFlat.wfCheck, Bool.and_eq_true] at hwf
    obtain ⟨_, ha⟩ := Option.isSome_iff_exists.1 (denoteArgs_isSome_of_checkArgs hΓ hwf.1)
    cases plan <;> simp [denote, ha, validateBoolLPhoas, validateBoolLFlat]
    exact validateBoolL_eq _ k (ctxTypes_pushTup_rev (Tup.units bs) hΓ) hΔ hmL hwf.2
  | .jnz _ t e, _, _, _, _, _, _, hΓ, hΔ, hmL, hwf => by
    simp only [TFlat.wfCheck, Bool.and_eq_true] at hwf
    obtain ⟨_, hc⟩ := Option.isSome_iff_exists.1 (denoteArg_isSome_of_checkArg hΓ hwf.1.1)
    cases plan <;> simp [denote, hc, validateBoolLPhoas, validateBoolLFlat]
    rw [validateBoolL_eq _ t hΓ hΔ hmL hwf.1.2, validateBoolL_eq _ e hΓ hΔ hmL hwf.2]
  | .jump (ts := ts) j _, _, _, _, _, _, _, hΓ, hΔ, hmL, hwf => by
    simp only [TFlat.wfCheck, Bool.and_eq_true] at hwf
    obtain ⟨_, hlk, hres⟩ := lookupL_eq_some_resolveLabel hΔ hmL hwf.1
    obtain ⟨_, ha⟩ := Option.isSome_iff_exists.1 (denoteArgs_isSome_of_checkArgs hΓ hwf.2)
    cases plan <;> simp [denote, hlk, ha, hres, validateBoolLPhoas, validateBoolLFlat]
  | .ret _, _, _, _, _, _, _, hΓ, _, _, hwf => by
    obtain ⟨_, hv⟩ := Option.isSome_iff_exists.1 (denoteArgs_isSome_of_checkArgs hΓ hwf)
    cases plan <;> simp [denote, hv, validateBoolLPhoas, validateBoolLFlat]
  | .exit _ _, _, _, _, _, _, _, hΓ, _, _, hwf => by
    obtain ⟨_, ha⟩ := Option.isSome_iff_exists.1 (denoteArgs_isSome_of_checkArgs hΓ hwf)
    cases plan <;> simp [denote, ha, validateBoolLPhoas, validateBoolLFlat]
  | .hlt, _, _, _, _, _, _, _, _, _, _ => by cases plan <;> rfl
  | .group (sig := sig) bodies k, _, _, vs, ls, inLD, inLE, hΓ, hΔ, hmL, hwf => by
    simp only [TFlat.wfCheck, Bool.and_eq_true] at hwf
    cases plan <;> try rfl
    case group spec pbs pk =>
      dsimp only [denote, validateBoolLPhoas, validateBoolLFlat]
      have hpasses :
          (spec.passes.all fun p => validateBoolLBlocksPhoas p.bMask pbs
            (denoteB SgpImpl.UnitV SgpImpl.BoolL bodies vs
              (pushTup (SgpImpl.boolTup p.lMask sig) ls))) =
          (spec.passes.all fun p => validateBoolLBlocksFlat p.bMask pbs (inLD + sig.length)
            (insertTupEnv inLD inLE (SgpImpl.boolTup p.lMask sig)) bodies) := by
        induction spec.passes with
        | nil => rfl
        | cons p ps ihp =>
          simp only [List.all_cons, validateBoolLBlocks_eq p.bMask pbs bodies hΓ
            (ctxTypes_pushTup_rev (SgpImpl.boolTup p.lMask sig) hΔ)
            (trieCtxMatch_insertTupEnv hmL (SgpImpl.boolTup p.lMask sig)) hwf.1, ihp]
      rw [hpasses, validateBoolL_eq pk k hΓ
        (ctxTypes_pushTup_rev (SgpImpl.boolTup spec.kMask sig) hΔ)
        (trieCtxMatch_insertTupEnv hmL (SgpImpl.boolTup spec.kMask sig)) hwf.2]
end
/-- Closed-function corollary of `validateBoolL_eq`. -/
theorem validateBoolL_func_eq {as rs : List Ty} (plan : BoolLPlan GroupBoolSpec)
    (tf : TFlat rs) (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    validateBoolLPhoas plan (denoteFunc (as := as) tf SgpImpl.UnitV SgpImpl.BoolL
      (Tup.units as)) = validateBoolLFlat plan 0 .empty tf :=
  validateBoolL_eq plan tf (ctxTypes_pushTup_rev (Tup.units as) .nil) .nil
    TrieCtxMatch.empty hwf
end OptFlatPlanKit
end LeanQbe.T
