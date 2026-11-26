module

public import LeanQbe.T.OptFlatCfgLemmas0
public import LeanQbe.T.OptFlatCfg
import LeanQbe.T.FlatDirectLemmas
import LeanQbe.T.PassFlatKit
import LeanQbe.T.IfOptLemmas

/-!
# Equivalence Proofs for `OptFlatCfg` `ifOptFlat` (and Re-Exports of `OptFlatCfgLemmas0`)

Proves exact `=` correspondence (`std3` axioms only) between every direct `TFlat` pass in
`LeanQbe.T.OptFlatCfg` and its PHOAS counterpart:

* `OptFlatCfg.dceWithFlat_eq`, `dceFlat_eq`, `deadLoadElimFlat_eq`, `denoteFunc_deadLoadElimFlat`
* `OptFlatCfg.dcePWithFlat_eq`, `dcePFlat_eq`, `denoteFunc_dcePFlat`, `dcePFlatFn_toFn`
  (via `public import LeanQbe.T.OptFlatCfgLemmas0`)
* `OptFlatCfg.ifOptFlat_eq`, `ifOptFlat_false_eq`, `ifOptFlat_true_eq`, `denoteFunc_ifOptFlat`
-/

set_option autoImplicit false

public section

namespace LeanQbe.T
namespace OptFlatCfg

open OptFlatPlanKit

/-! ## `ifOptFlat` Simulation Proofs -/

section IfOptProofs
open IfOptImpl

private theorem findFirstJumpFlat_eq {rs : List Ty} :
    (fuel : Nat) → (tf : TFlat rs) → {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × IVal K t)} → {ls : List ((ts : List Ty) × JLabel KL ts)} →
    {inLD : Nat} → {inLE : Trie ((ts : List Ty) × JLabel KL ts)} →
    CtxTypes Γ vs → CtxTypes Δ ls → TrieCtxMatch inLD inLE ls → tf.wfCheck Γ Δ = true →
    findFirstJump fuel (denote (IVal K) (JLabel KL) tf vs ls) =
      findFirstJumpFlat fuel inLD inLE tf
  | 0, _, _, _, _, _, _, _, _, _, _, _ => rfl
  | fuel + 1, tf, Γ, Δ, vs, ls, inLD, inLE, hΓ, hΔ, hmL, hwf => by
    cases tf with
    | jump j args =>
      dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
      obtain ⟨jl, hlk, hres⟩ := lookupL_eq_some_resolveLabel hΔ hmL hwf.1
      obtain ⟨args', ha⟩ := Option.isSome_iff_exists.1 (denoteArgs_isSome_of_checkArgs hΓ hwf.2)
      dsimp only [denote]; rw [hlk, ha]
      dsimp only [findFirstJump, findFirstJumpFlat]; rw [hres]
      cases jl <;> rfl
    | let_ op k =>
      dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
      obtain ⟨args', ha⟩ := Option.isSome_iff_exists.1 (denoteArgs_isSome_of_checkArgs hΓ hwf.1)
      dsimp only [denote]; rw [ha]; dsimp only [findFirstJump, findFirstJumpFlat]
      exact findFirstJumpFlat_eq fuel k (CtxTypes.push _ hΓ) hΔ hmL hwf.2
    | jnz c t e =>
      dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
      obtain ⟨c', hc⟩ := Option.isSome_iff_exists.1 (denoteArg_isSome_of_checkArg hΓ hwf.1.1)
      dsimp only [denote]; rw [hc]; dsimp only [findFirstJump, findFirstJumpFlat]
      exact findFirstJumpFlat_eq fuel t hΓ hΔ hmL hwf.1.2
    | load t a k =>
      dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
      obtain ⟨a', ha⟩ := Option.isSome_iff_exists.1 (denoteArg_isSome_of_checkArg hΓ hwf.1)
      dsimp only [denote]; rw [ha]; rfl
    | store v a k =>
      dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
      obtain ⟨v', hv⟩ := Option.isSome_iff_exists.1 (denoteArg_isSome_of_checkArg hΓ hwf.1.1)
      obtain ⟨a', ha⟩ := Option.isSome_iff_exists.1 (denoteArg_isSome_of_checkArg hΓ hwf.1.2)
      dsimp only [denote]; rw [hv, ha]; rfl
    | call f bs args k =>
      dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
      obtain ⟨args', ha⟩ := Option.isSome_iff_exists.1 (denoteArgs_isSome_of_checkArgs hΓ hwf.1)
      dsimp only [denote]; rw [ha]; rfl
    | ret vs' =>
      obtain ⟨vs'', hv⟩ := Option.isSome_iff_exists.1 (denoteArgs_isSome_of_checkArgs hΓ hwf)
      dsimp only [denote]; rw [hv]; rfl
    | exit f args =>
      obtain ⟨args', ha⟩ := Option.isSome_iff_exists.1 (denoteArgs_isSome_of_checkArgs hΓ hwf)
      dsimp only [denote]; rw [ha]; rfl
    | hlt | group _ _ => rfl

private theorem findFirstJumpStoreFlat_eq {rs : List Ty} :
    (fuel : Nat) → (tf : TFlat rs) → {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × IVal K t)} → {ls : List ((ts : List Ty) × JLabel KL ts)} →
    {inLD : Nat} → {inLE : Trie ((ts : List Ty) × JLabel KL ts)} →
    CtxTypes Γ vs → CtxTypes Δ ls → TrieCtxMatch inLD inLE ls → tf.wfCheck Γ Δ = true →
    findFirstJumpStore fuel (denote (IVal K) (JLabel KL) tf vs ls) =
      findFirstJumpStoreFlat fuel inLD inLE tf
  | 0, _, _, _, _, _, _, _, _, _, _, _ => rfl
  | fuel + 1, tf, Γ, Δ, vs, ls, inLD, inLE, hΓ, hΔ, hmL, hwf => by
    cases tf with
    | jump j args =>
      dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
      obtain ⟨jl, hlk, hres⟩ := lookupL_eq_some_resolveLabel hΔ hmL hwf.1
      obtain ⟨args', ha⟩ := Option.isSome_iff_exists.1 (denoteArgs_isSome_of_checkArgs hΓ hwf.2)
      dsimp only [denote]; rw [hlk, ha]
      dsimp only [findFirstJumpStore, findFirstJumpStoreFlat]; rw [hres]
      cases jl <;> rfl
    | let_ op k =>
      dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
      obtain ⟨args', ha⟩ := Option.isSome_iff_exists.1 (denoteArgs_isSome_of_checkArgs hΓ hwf.1)
      dsimp only [denote]; rw [ha]; dsimp only [findFirstJumpStore, findFirstJumpStoreFlat]
      exact findFirstJumpStoreFlat_eq fuel k (CtxTypes.push _ hΓ) hΔ hmL hwf.2
    | load t a k =>
      dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
      obtain ⟨a', ha⟩ := Option.isSome_iff_exists.1 (denoteArg_isSome_of_checkArg hΓ hwf.1)
      dsimp only [denote]; rw [ha]; dsimp only [findFirstJumpStore, findFirstJumpStoreFlat]
      exact findFirstJumpStoreFlat_eq fuel k (.cons hΓ) hΔ hmL hwf.2
    | store v a k =>
      dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
      obtain ⟨v', hv⟩ := Option.isSome_iff_exists.1 (denoteArg_isSome_of_checkArg hΓ hwf.1.1)
      obtain ⟨a', ha⟩ := Option.isSome_iff_exists.1 (denoteArg_isSome_of_checkArg hΓ hwf.1.2)
      dsimp only [denote]; rw [hv, ha]; dsimp only [findFirstJumpStore, findFirstJumpStoreFlat]
      exact findFirstJumpStoreFlat_eq fuel k hΓ hΔ hmL hwf.2
    | jnz c t e =>
      dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
      obtain ⟨c', hc⟩ := Option.isSome_iff_exists.1 (denoteArg_isSome_of_checkArg hΓ hwf.1.1)
      dsimp only [denote]; rw [hc]; rfl
    | call f bs args k =>
      dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
      obtain ⟨args', ha⟩ := Option.isSome_iff_exists.1 (denoteArgs_isSome_of_checkArgs hΓ hwf.1)
      dsimp only [denote]; rw [ha]; rfl
    | ret vs' =>
      obtain ⟨vs'', hv⟩ := Option.isSome_iff_exists.1 (denoteArgs_isSome_of_checkArgs hΓ hwf)
      dsimp only [denote]; rw [hv]; rfl
    | exit f args =>
      obtain ⟨args', ha⟩ := Option.isSome_iff_exists.1 (denoteArgs_isSome_of_checkArgs hΓ hwf)
      dsimp only [denote]; rw [ha]; rfl
    | hlt | group _ _ => rfl

private theorem checkArmFlat_eq {rs : List Ty} (tgt : ArmTarget) :
    (tf : TFlat rs) → (jnzFuel letFuel next : Nat) →
    {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × IVal K t)} → {ls : List ((ts : List Ty) × JLabel KL ts)} →
    {inLD : Nat} → {inLE : Trie ((ts : List Ty) × JLabel KL ts)} →
    CtxTypes Γ vs → CtxTypes Δ ls → TrieCtxMatch inLD inLE ls → tf.wfCheck Γ Δ = true →
    checkArm tgt jnzFuel letFuel next (denote (IVal K) (JLabel KL) tf vs ls) =
      checkArmFlat tgt jnzFuel letFuel inLD inLE tf
  | .let_ (ts := ts) op k, jnzFuel, letFuel, next, Γ, Δ, vs, ls, inLD, inLE,
      hΓ, hΔ, hmL, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨args', ha⟩ := Option.isSome_iff_exists.1 (denoteArgs_isSome_of_checkArgs hΓ hwf.1)
    dsimp only [denote]; rw [ha]; dsimp only
    cases letFuel with
    | zero => dsimp only [checkArm, checkArmFlat]
    | succ letFuel' =>
      dsimp only [checkArm, checkArmFlat]
      cases isSafeOp op.code with
      | false => simp only [Bool.false_eq_true, ↓reduceIte]
      | true =>
        simp only [↓reduceIte]
        rw [checkArmFlat_eq tgt k jnzFuel letFuel' (next + ts.length)
          (CtxTypes.push _ hΓ) hΔ hmL hwf.2]
  | .jump (ts := ts) j args, _, letFuel, _, Γ, Δ, vs, ls, inLD, inLE, hΓ, hΔ, hmL, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨jl, hlk, hres⟩ := lookupL_eq_some_resolveLabel hΔ hmL hwf.1
    obtain ⟨args', ha⟩ := Option.isSome_iff_exists.1 (denoteArgs_isSome_of_checkArgs hΓ hwf.2)
    dsimp only [denote]; rw [hlk, ha]; dsimp only
    dsimp only [checkArm, checkArmFlat]; rw [hres]
    cases tgt <;> cases jl <;> rfl
  | .ret vs', _, _, _, Γ, _, vs, _, _, _, hΓ, _, _, hwf => by
    obtain ⟨vs'', hv⟩ := Option.isSome_iff_exists.1 (denoteArgs_isSome_of_checkArgs hΓ hwf)
    dsimp only [denote]; rw [hv]; dsimp only
    cases tgt with
    | ret => rfl
    | loc _ _ | tag _ _ => simp [checkArm, checkArmFlat]
  | .jnz c t e, jnzFuel, letFuel, next, Γ, Δ, vs, ls, inLD, inLE, hΓ, hΔ, hmL, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨c', hc⟩ := Option.isSome_iff_exists.1 (denoteArg_isSome_of_checkArg hΓ hwf.1.1)
    dsimp only [denote]; rw [hc]; dsimp only
    cases jnzFuel with
    | zero => simp [checkArm, checkArmFlat]
    | succ jnzFuel' =>
      dsimp only [checkArm, checkArmFlat, bind, Option.bind]
      rw [checkArmFlat_eq tgt t jnzFuel' letFuel next hΓ hΔ hmL hwf.1.2]
      cases checkArmFlat tgt jnzFuel' letFuel inLD inLE t with
      | none => rfl
      | some res =>
        rcases res with ⟨pT, rem1⟩
        dsimp only
        rw [checkArmFlat_eq tgt e jnzFuel' rem1 next hΓ hΔ hmL hwf.2]
  | .load t a k, _, _, _, Γ, _, vs, _, _, _, hΓ, _, _, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨a', ha⟩ := Option.isSome_iff_exists.1 (denoteArg_isSome_of_checkArg hΓ hwf.1)
    dsimp only [denote]; rw [ha]; simp [checkArm, checkArmFlat]
  | .store v a k, _, _, _, Γ, _, vs, _, _, _, hΓ, _, _, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨v', hv⟩ := Option.isSome_iff_exists.1 (denoteArg_isSome_of_checkArg hΓ hwf.1.1)
    obtain ⟨a', ha⟩ := Option.isSome_iff_exists.1 (denoteArg_isSome_of_checkArg hΓ hwf.1.2)
    dsimp only [denote]; rw [hv, ha]; simp [checkArm, checkArmFlat]
  | .call f bs args k, _, _, _, Γ, _, vs, _, _, _, hΓ, _, _, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨args', ha⟩ := Option.isSome_iff_exists.1 (denoteArgs_isSome_of_checkArgs hΓ hwf.1)
    dsimp only [denote]; rw [ha]; simp [checkArm, checkArmFlat]
  | .exit f args, _, _, _, Γ, _, vs, _, _, _, hΓ, _, _, hwf => by
    obtain ⟨args', ha⟩ := Option.isSome_iff_exists.1 (denoteArgs_isSome_of_checkArgs hΓ hwf)
    dsimp only [denote]; rw [ha]; simp [checkArm, checkArmFlat]
  | .hlt, _, _, _, _, _, _, _, _, _, _, _, _, _ => by
    dsimp only [denote]; simp [checkArm, checkArmFlat]
  | .group _ _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by
    dsimp only [denote]; simp [checkArm, checkArmFlat]

private theorem checkStoreTailFlat_eq {rs : List Ty} (tgt : ArmTarget) :
    (tf : TFlat rs) → (letFuel : Nat) →
    {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × IVal K t)} → {ls : List ((ts : List Ty) × JLabel KL ts)} →
    {inLD : Nat} → {inLE : Trie ((ts : List Ty) × JLabel KL ts)} →
    CtxTypes Γ vs → CtxTypes Δ ls → TrieCtxMatch inLD inLE ls → tf.wfCheck Γ Δ = true →
    checkStoreTail tgt letFuel (denote (IVal K) (JLabel KL) tf vs ls) =
      checkStoreTailFlat tgt letFuel inLD inLE tf
  | .let_ op k, letFuel, Γ, Δ, vs, ls, inLD, inLE, hΓ, hΔ, hmL, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨args', ha⟩ := Option.isSome_iff_exists.1 (denoteArgs_isSome_of_checkArgs hΓ hwf.1)
    dsimp only [denote]; rw [ha]; dsimp only
    unfold checkStoreTail checkStoreTailFlat; dsimp only
    cases isSafeOp op.code with
    | false => simp only [Bool.false_eq_true, ↓reduceIte]
    | true =>
      simp only [↓reduceIte]
      cases letFuel with
      | zero => rfl
      | succ letFuel' =>
        dsimp only
        rw [checkStoreTailFlat_eq tgt k letFuel' (CtxTypes.push _ hΓ) hΔ hmL hwf.2]
  | .jump (ts := ts) j args, _, Γ, Δ, vs, ls, inLD, inLE, hΓ, hΔ, hmL, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨jl, hlk, hres⟩ := lookupL_eq_some_resolveLabel hΔ hmL hwf.1
    obtain ⟨args', ha⟩ := Option.isSome_iff_exists.1 (denoteArgs_isSome_of_checkArgs hΓ hwf.2)
    dsimp only [denote]; rw [hlk, ha]; dsimp only
    unfold checkStoreTail checkStoreTailFlat; rw [hres]
    cases tgt <;> cases jl <;> rfl
  | .ret vs', _, Γ, _, vs, _, _, _, hΓ, _, _, hwf => by
    obtain ⟨vs'', hv⟩ := Option.isSome_iff_exists.1 (denoteArgs_isSome_of_checkArgs hΓ hwf)
    dsimp only [denote]; rw [hv]; dsimp only
    unfold checkStoreTail checkStoreTailFlat
    cases tgt <;> rfl
  | .jnz c t e, _, Γ, _, vs, _, _, _, hΓ, _, _, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨c', hc⟩ := Option.isSome_iff_exists.1 (denoteArg_isSome_of_checkArg hΓ hwf.1.1)
    dsimp only [denote]; rw [hc]; simp [checkStoreTail, checkStoreTailFlat]
  | .load t a k, _, Γ, _, vs, _, _, _, hΓ, _, _, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨a', ha⟩ := Option.isSome_iff_exists.1 (denoteArg_isSome_of_checkArg hΓ hwf.1)
    dsimp only [denote]; rw [ha]; simp [checkStoreTail, checkStoreTailFlat]
  | .store v a k, _, Γ, _, vs, _, _, _, hΓ, _, _, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨v', hv⟩ := Option.isSome_iff_exists.1 (denoteArg_isSome_of_checkArg hΓ hwf.1.1)
    obtain ⟨a', ha⟩ := Option.isSome_iff_exists.1 (denoteArg_isSome_of_checkArg hΓ hwf.1.2)
    dsimp only [denote]; rw [hv, ha]; simp [checkStoreTail, checkStoreTailFlat]
  | .call f bs args k, _, Γ, _, vs, _, _, _, hΓ, _, _, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨args', ha⟩ := Option.isSome_iff_exists.1 (denoteArgs_isSome_of_checkArgs hΓ hwf.1)
    dsimp only [denote]; rw [ha]; simp [checkStoreTail, checkStoreTailFlat]
  | .exit f args, _, Γ, _, vs, _, _, _, hΓ, _, _, hwf => by
    obtain ⟨args', ha⟩ := Option.isSome_iff_exists.1 (denoteArgs_isSome_of_checkArgs hΓ hwf)
    dsimp only [denote]; rw [ha]; simp [checkStoreTail, checkStoreTailFlat]
  | .hlt, _, _, _, _, _, _, _, _, _, _, _ => by
    dsimp only [denote]; simp [checkStoreTail, checkStoreTailFlat]
  | .group _ _, _, _, _, _, _, _, _, _, _, _, _ => by
    dsimp only [denote]; simp [checkStoreTail, checkStoreTailFlat]

private theorem checkStoreArmFlat_eq {rs : List Ty} (tgt : ArmTarget) (allowNewLoads : Bool) :
    (tf : TFlat rs) → (letFuel loadFuel : Nat) → (tbl : SymTbl) → (hits : List Nat) →
    {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × IVal K t)} → {ls : List ((ts : List Ty) × JLabel KL ts)} →
    {inVD inLD : Nat} →
    {inVE : Trie ((t : Ty) × IVal K t)} → {inLE : Trie ((ts : List Ty) × JLabel KL ts)} →
    CtxTypes Γ vs → CtxTypes Δ ls →
    TrieCtxMatch inVD inVE vs → TrieCtxMatch inLD inLE ls → tf.wfCheck Γ Δ = true →
    checkStoreArm tgt allowNewLoads letFuel loadFuel tbl hits
        (denote (IVal K) (JLabel KL) tf vs ls) =
      checkStoreArmFlat tgt allowNewLoads letFuel loadFuel tbl hits inVD inVE inLD inLE tf
  | .let_ (ts := ts) op k, letFuel, loadFuel, tbl, hits,
      Γ, Δ, vs, ls, inVD, inLD, inVE, inLE, hΓ, hΔ, hmV, hmL, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denote]
    rw [denoteArgs_eq_some_resolveEnvArgs hΓ hmV op.args hwf.1]
    unfold checkStoreArm checkStoreArmFlat; dsimp only
    cases isSafeOp op.code with
    | false => simp only [Bool.false_eq_true, ↓reduceIte]
    | true =>
      simp only [↓reduceIte]
      cases letFuel with
      | zero => rfl
      | succ letFuel' =>
        dsimp only
        rw [checkStoreArmFlat_eq tgt allowNewLoads k letFuel' loadFuel _ hits
          (CtxTypes.push _ hΓ) hΔ (trieCtxMatch_insertTupEnv hmV _) hmL hwf.2]
  | .load t a k, letFuel, loadFuel, tbl, hits,
      Γ, Δ, vs, ls, inVD, inLD, inVE, inLE, hΓ, hΔ, hmV, hmL, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denote]
    rw [denoteArg_eq_some_resolveEnvArg hΓ hmV a hwf.1]
    unfold checkStoreArm checkStoreArmFlat; dsimp only
    cases findSymLoad tbl.loads t (ikey (resolveEnvArg inVD inVE a)) with
    | some entry =>
      dsimp only
      rw [checkStoreArmFlat_eq tgt allowNewLoads k letFuel loadFuel tbl _
        (.cons hΓ) hΔ (hmV.cons t _) hmL hwf.2]
    | none =>
      cases allowNewLoads with
      | false => simp only [Bool.false_eq_true, ↓reduceIte]
      | true =>
        simp only [↓reduceIte]
        cases loadFuel with
        | zero => rfl
        | succ loadFuel' =>
          dsimp only
          rw [checkStoreArmFlat_eq tgt true k letFuel loadFuel' _ _
            (.cons hΓ) hΔ (hmV.cons t _) hmL hwf.2]
  | .store (t := st) v a tail, letFuel, _, tbl, hits,
      Γ, Δ, vs, ls, inVD, inLD, inVE, inLE, hΓ, hΔ, hmV, hmL, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denote]
    rw [denoteArg_eq_some_resolveEnvArg hΓ hmV v hwf.1.1,
      denoteArg_eq_some_resolveEnvArg hΓ hmV a hwf.1.2]
    unfold checkStoreArm checkStoreArmFlat; dsimp only
    rw [checkStoreTailFlat_eq tgt tail letFuel hΓ hΔ hmL hwf.2]
  | .jump (ts := ts) j args, _, _, _, _, Γ, Δ, vs, ls, _, _, inVE, _,
      hΓ, hΔ, hmV, _, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨j', hj⟩ := Option.isSome_iff_exists.1 (lookupL_isSome_of_check hΔ hwf.1)
    dsimp only [denote]
    rw [hj, denoteArgs_eq_some_resolveEnvArgs hΓ hmV args hwf.2]; rfl
  | .ret vs', _, _, _, _, Γ, _, vs, _, _, _, inVE, _, hΓ, _, hmV, _, hwf => by
    dsimp only [denote]
    rw [denoteArgs_eq_some_resolveEnvArgs hΓ hmV vs' hwf]; rfl
  | .jnz c t e, _, _, _, _, Γ, _, vs, _, _, _, inVE, _, hΓ, _, hmV, _, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denote]
    rw [denoteArg_eq_some_resolveEnvArg hΓ hmV c hwf.1.1]; rfl
  | .call f bs args k, _, _, _, _, Γ, _, vs, _, _, _, inVE, _, hΓ, _, hmV, _, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denote]
    rw [denoteArgs_eq_some_resolveEnvArgs hΓ hmV args hwf.1]; rfl
  | .exit f args, _, _, _, _, Γ, _, vs, _, _, _, inVE, _, hΓ, _, hmV, _, hwf => by
    dsimp only [denote]
    rw [denoteArgs_eq_some_resolveEnvArgs hΓ hmV args hwf]; rfl
  | .hlt, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => rfl
  | .group _ _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => rfl

private theorem checkStoreArmsFlat_eq {rs : List Ty} (bitsOnly : Bool) (tgt : ArmTarget)
    (t e : TFlat rs)
    {Γ : List Ty} {Δ : List (List Ty)}
    {vs : List ((t : Ty) × IVal K t)} {ls : List ((ts : List Ty) × JLabel KL ts)}
    {inVD inLD outVD : Nat}
    {inVE : Trie ((t : Ty) × IVal K t)} {inLE : Trie ((ts : List Ty) × JLabel KL ts)}
    (hΓ : CtxTypes Γ vs) (hΔ : CtxTypes Δ ls)
    (hmV : TrieCtxMatch inVD inVE vs) (hmL : TrieCtxMatch inLD inLE ls)
    (ht : t.wfCheck Γ Δ = true) (he : e.wfCheck Γ Δ = true) :
    checkStoreArms bitsOnly tgt outVD
        (denote (IVal K) (JLabel KL) t vs ls) (denote (IVal K) (JLabel KL) e vs ls) =
      checkStoreArmsFlat bitsOnly tgt inVD inVE inLD inLE outVD t e := by
  dsimp only [checkStoreArms, checkStoreArmsFlat, bind, Option.bind]
  rw [checkStoreArmFlat_eq tgt true t 12 2 ⟨outVD, [], []⟩ [] hΓ hΔ hmV hmL ht]
  cases checkStoreArmFlat tgt true 12 2 ⟨outVD, [], []⟩ [] inVD inVE inLD inLE t with
  | none => rfl
  | some res1 =>
    rcases res1 with ⟨apT, tbl1⟩
    dsimp only [guard]
    cases isSelectTyWith bitsOnly apT.storeTy with
    | false => simp [failure]
    | true =>
      simp only [↓reduceIte, Pure.pure]
      rw [checkStoreArmFlat_eq tgt false e 12 0 tbl1 [] hΓ hΔ hmV hmL he]
      rfl

private theorem checkDiamondFlat_eq (bitsOnly : Bool) (jId : Nat) (jTs : List Ty) {rs : List Ty} :
    (tf : TFlat rs) → (outVD : Nat) → {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × IVal K t)} → {ls : List ((ts : List Ty) × JLabel KL ts)} →
    {inVD inLD : Nat} →
    {inVE : Trie ((t : Ty) × IVal K t)} → {inLE : Trie ((ts : List Ty) × JLabel KL ts)} →
    CtxTypes Γ vs → CtxTypes Δ ls →
    TrieCtxMatch inVD inVE vs → TrieCtxMatch inLD inLE ls → tf.wfCheck Γ Δ = true →
    checkDiamondWith bitsOnly jId jTs outVD (denote (IVal K) (JLabel KL) tf vs ls) =
      checkDiamondFlat bitsOnly jId jTs inVD inVE inLD inLE outVD tf
  | .let_ (ts := ts) op k, outVD, Γ, Δ, vs, ls, inVD, inLD, inVE, inLE,
      hΓ, hΔ, hmV, hmL, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨args', ha⟩ := Option.isSome_iff_exists.1 (denoteArgs_isSome_of_checkArgs hΓ hwf.1)
    dsimp only [denote]; rw [ha]; dsimp only [checkDiamondWith, checkDiamondFlat]
    rw [checkDiamondFlat_eq bitsOnly jId jTs k (outVD + ts.length)
      (CtxTypes.push _ hΓ) hΔ (trieCtxMatch_insertTupEnv hmV _) hmL hwf.2]
  | .load t a k, outVD, Γ, Δ, vs, ls, inVD, inLD, inVE, inLE,
      hΓ, hΔ, hmV, hmL, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨a', ha⟩ := Option.isSome_iff_exists.1 (denoteArg_isSome_of_checkArg hΓ hwf.1)
    dsimp only [denote]; rw [ha]; dsimp only [checkDiamondWith, checkDiamondFlat]
    rw [checkDiamondFlat_eq bitsOnly jId jTs k (outVD + 1)
      (.cons hΓ) hΔ (hmV.cons t _) hmL hwf.2]
  | .store v a k, outVD, Γ, Δ, vs, ls, inVD, inLD, inVE, inLE,
      hΓ, hΔ, hmV, hmL, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨v', hv⟩ := Option.isSome_iff_exists.1 (denoteArg_isSome_of_checkArg hΓ hwf.1.1)
    obtain ⟨a', ha⟩ := Option.isSome_iff_exists.1 (denoteArg_isSome_of_checkArg hΓ hwf.1.2)
    dsimp only [denote]; rw [hv, ha]; dsimp only [checkDiamondWith, checkDiamondFlat]
    rw [checkDiamondFlat_eq bitsOnly jId jTs k outVD hΓ hΔ hmV hmL hwf.2]
  | .call f bs args k, outVD, Γ, Δ, vs, ls, inVD, inLD, inVE, inLE,
      hΓ, hΔ, hmV, hmL, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨args', ha⟩ := Option.isSome_iff_exists.1 (denoteArgs_isSome_of_checkArgs hΓ hwf.1)
    dsimp only [denote]; rw [ha]; dsimp only [checkDiamondWith, checkDiamondFlat]
    rw [checkDiamondFlat_eq bitsOnly jId jTs k (outVD + bs.length)
      (CtxTypes.push _ hΓ) hΔ (trieCtxMatch_insertTupEnv hmV _) hmL hwf.2]
  | .jnz c t e, outVD, Γ, Δ, vs, ls, inVD, inLD, inVE, inLE,
      hΓ, hΔ, hmV, hmL, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨c', hc⟩ := Option.isSome_iff_exists.1 (denoteArg_isSome_of_checkArg hΓ hwf.1.1)
    dsimp only [denote]; rw [hc]; dsimp only [checkDiamondWith, checkDiamondFlat]
    cases isSelectSigWith bitsOnly jTs with
    | false => simp only [Bool.false_eq_true, ↓reduceIte]
    | true =>
      simp only [↓reduceIte]
      rw [checkArmFlat_eq (.loc jId jTs) t 2 4 outVD hΓ hΔ hmL hwf.1.2,
        checkArmFlat_eq (.loc jId jTs) e 2 4 outVD hΓ hΔ hmL hwf.2,
        checkStoreArmsFlat_eq bitsOnly (.loc jId jTs) t e hΓ hΔ hmV hmL hwf.1.2 hwf.2]
      rfl
  | .jump (ts := ts) j args, _, Γ, Δ, vs, ls, _, _, _, _, hΓ, hΔ, _, _, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨j', hj⟩ := Option.isSome_iff_exists.1 (lookupL_isSome_of_check hΔ hwf.1)
    obtain ⟨args', ha⟩ := Option.isSome_iff_exists.1 (denoteArgs_isSome_of_checkArgs hΓ hwf.2)
    dsimp only [denote]; rw [hj, ha]; rfl
  | .ret vs', _, Γ, _, vs, _, _, _, _, _, hΓ, _, _, _, hwf => by
    obtain ⟨vs'', hv⟩ := Option.isSome_iff_exists.1 (denoteArgs_isSome_of_checkArgs hΓ hwf)
    dsimp only [denote]; rw [hv]; rfl
  | .exit f args, _, Γ, _, vs, _, _, _, _, _, hΓ, _, _, _, hwf => by
    obtain ⟨args', ha⟩ := Option.isSome_iff_exists.1 (denoteArgs_isSome_of_checkArgs hΓ hwf)
    dsimp only [denote]; rw [ha]; rfl
  | .hlt, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => rfl
  | .group _ _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => rfl

private theorem mkPairIValArgFlat_eq {rs : List Ty} {a b : Ty}
    (outVD outLD : Nat) (x : Arg (IVal K) a) (y : Arg (IVal K) b)
    {cont_p : Nat → Arg (IVal K) (.pair a b) → Expr K KL rs}
    {cont_f : Nat → Arg (IVal K) (.pair a b) → TFlat rs}
    (hcont : ∀ od p, toTFlat (cont_p od p) od outLD = cont_f od p) :
    toTFlat (mkPairIValArg outVD x y cont_p) outVD outLD =
      mkPairIValArgFlat outVD x y cont_f := by
  dsimp only [mkPairIValArg, mkPairIValArgFlat]
  cases hx : iout x <;> cases hy : iout y
  · dsimp only [toTFlat, op2, idxArgs, idxArg]
    exact congrArg (TFlat.let_ _) (hcont (outVD + 1) _)
  · dsimp only [toTFlat, op2, idxArgs, idxArg]
    exact congrArg (TFlat.let_ _) (hcont (outVD + 1) _)
  · dsimp only [toTFlat, op2, idxArgs, idxArg]
    exact congrArg (TFlat.let_ _) (hcont (outVD + 1) _)
  · exact hcont outVD _

private theorem splitPairIValFlat_eq {rs : List Ty} {a b : Ty}
    (outVD outLD : Nat) (p : Arg (IVal K) (.pair a b))
    {cont_p : Nat → Arg (IVal K) a → Arg (IVal K) b → Expr K KL rs}
    {cont_f : Nat → Arg (IVal K) a → Arg (IVal K) b → TFlat rs}
    (hcont : ∀ od p₁ p₂, toTFlat (cont_p od p₁ p₂) od outLD = cont_f od p₁ p₂) :
    toTFlat (splitPairIVal outVD p cont_p) outVD outLD =
      splitPairIValFlat outVD p cont_f := by
  dsimp only [splitPairIVal, splitPairIValFlat]
  cases hp : iout p with
  | imm c => exact hcont outVD (.imm c.1) (.imm c.2)
  | var v =>
    dsimp only [toTFlat, op1, idxArgs, idxArg]
    exact congrArg (TFlat.let_ _) (hcont (outVD + 2) _ _)

private theorem emitSelectTyIValFlat_eq {rs : List Ty} (c : Arg K .bool) :
    (t : Ty) → (outVD outLD : Nat) → (aT aE : Arg (IVal K) t) →
    {cont_p : Nat → Arg (IVal K) t → Expr K KL rs} →
    {cont_f : Nat → Arg (IVal K) t → TFlat rs} →
    (∀ od r, toTFlat (cont_p od r) od outLD = cont_f od r) →
    toTFlat (emitSelectTyIVal c t outVD aT aE cont_p) outVD outLD =
      emitSelectTyIValFlat c t outVD aT aE cont_f
  | .bool, outVD, outLD, aT, aE, _, _, hcont
  | .bits _, outVD, outLD, aT, aE, _, _, hcont => by
    dsimp only [emitSelectTyIVal, emitSelectTyIValFlat]
    by_cases hbeq : fKeyBeq (ikey aT) (ikey aE)
    · simp only [hbeq, ↓reduceIte]; exact hcont outVD aT
    · simp only [hbeq, Bool.false_eq_true, ↓reduceIte, toTFlat, op3, idxArgs]
      exact congrArg (TFlat.let_ _) (hcont (outVD + 1) _)
  | .float _, outVD, _, aT, _, _, _, hcont => hcont outVD aT
  | .pair a b, outVD, outLD, aT, aE, _, _, hcont => by
    dsimp only [emitSelectTyIVal, emitSelectTyIValFlat]
    by_cases hbeq : fKeyBeq (ikey aT) (ikey aE)
    · simp only [hbeq, ↓reduceIte]; exact hcont outVD aT
    · simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
      apply splitPairIValFlat_eq outVD outLD aT
      intro od₁ aT₁ aT₂
      apply splitPairIValFlat_eq od₁ outLD aE
      intro od₂ aE₁ aE₂
      apply emitSelectTyIValFlat_eq c a od₂ outLD aT₁ aE₁
      intro od₃ r₁
      apply emitSelectTyIValFlat_eq c b od₃ outLD aT₂ aE₂
      intro od₄ r₂
      exact mkPairIValArgFlat_eq od₄ outLD r₁ r₂ hcont

private theorem emitSelectTupIValFlat_eq {rs : List Ty} (c : Arg K .bool) :
    (ts : List Ty) → (outVD outLD : Nat) →
    (asT asE : Tup (Arg (IVal K)) ts) →
    {cont_p : Nat → Tup (Arg (IVal K)) ts → Expr K KL rs} →
    {cont_f : Nat → Tup (Arg (IVal K)) ts → TFlat rs} →
    (∀ od sel, toTFlat (cont_p od sel) od outLD = cont_f od sel) →
    toTFlat (emitSelectTupIVal c ts outVD asT asE cont_p) outVD outLD =
      emitSelectTupIValFlat c ts outVD asT asE cont_f
  | [], outVD, _, (), (), _, _, hcont => hcont outVD ()
  | t :: ts, outVD, outLD, (aT, asT), (aE, asE), _, _, hcont => by
    dsimp only [emitSelectTupIVal, emitSelectTupIValFlat]
    apply emitSelectTyIValFlat_eq c t outVD outLD aT aE
    intro od' r
    apply emitSelectTupIValFlat_eq c ts od' outLD asT asE
    intro od'' rs'
    exact hcont od'' (r, rs')

private theorem emitSelectTyFlat_eq {rs : List Ty} (c : Arg K .bool)
    (t : Ty) (outVD outLD : Nat) (aT aE : Arg (IVal K) t)
    {cont_p : Nat → Arg K t → Expr K KL rs}
    {cont_f : Nat → Arg K t → TFlat rs}
    (hcont : ∀ od r, toTFlat (cont_p od r) od outLD = cont_f od r) :
    toTFlat (emitSelectTy c t outVD aT aE cont_p) outVD outLD =
      emitSelectTyFlat c t outVD aT aE cont_f :=
  emitSelectTyIValFlat_eq c t outVD outLD aT aE fun od' r => hcont od' (iout r)

private theorem emitSelectTupFlat_eq {rs : List Ty} (c : Arg K .bool)
    (ts : List Ty) (outVD outLD : Nat) (asT asE : Tup (Arg (IVal K)) ts)
    {fin_p : Tup (Arg K) ts → Expr K KL rs}
    {fin_f : Nat → Tup (Arg K) ts → TFlat rs}
    (hfin : ∀ od sel, toTFlat (fin_p sel) od outLD = fin_f od sel) :
    toTFlat (emitSelectTup c ts outVD asT asE fin_p) outVD outLD =
      emitSelectTupFlat c ts outVD asT asE fin_f :=
  emitSelectTupIValFlat_eq c ts outVD outLD asT asE fun od' sel => hfin od' (tupIOut sel)

private theorem hoistArmFlat_eq {rs : List Ty} (jTs : List Ty) :
    (tf : TFlat rs) → (plan : ArmPlan) →
    {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × IVal K t)} → {ls : List ((ts : List Ty) × JLabel KL ts)} →
    {inVD outVD outLD : Nat} → {inVE : Trie ((t : Ty) × IVal K t)} →
    {cont_p : Nat → Tup (Arg (IVal K)) jTs → Expr K KL rs} →
    {cont_f : Nat → Tup (Arg (IVal K)) jTs → TFlat rs} →
    CtxTypes Γ vs → CtxTypes Δ ls → TrieCtxMatch inVD inVE vs → tf.wfCheck Γ Δ = true →
    (∀ od args, toTFlat (cont_p od args) od outLD = cont_f od args) →
    toTFlat (hoistArm jTs plan outVD (denote (IVal K) (JLabel KL) tf vs ls) cont_p)
      outVD outLD = hoistArmFlat jTs plan tf inVD inVE outVD cont_f
  | .jump (ts := ts) j args, plan, Γ, Δ, vs, ls, inVD, outVD, outLD, inVE,
      cont_p, cont_f, hΓ, hΔ, hmV, hwf, hcont => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨j', hj⟩ := Option.isSome_iff_exists.1 (lookupL_isSome_of_check hΔ hwf.1)
    dsimp only [denote]
    rw [hj, denoteArgs_eq_some_resolveEnvArgs hΓ hmV args hwf.2]
    cases plan <;> try rfl
    dsimp only [hoistArm, hoistArmFlat]
    cases listTyDecEq ts jTs with
    | isFalse _ => rfl
    | isTrue heq => exact hcont outVD _
  | .ret vs', plan, Γ, _, vs, _, inVD, outVD, outLD, inVE,
      cont_p, cont_f, hΓ, _, hmV, hwf, hcont => by
    dsimp only [denote]
    rw [denoteArgs_eq_some_resolveEnvArgs hΓ hmV vs' hwf]
    cases plan <;> try rfl
    dsimp only [hoistArm, hoistArmFlat]
    cases listTyDecEq rs jTs with
    | isFalse _ => rfl
    | isTrue heq => exact hcont outVD _
  | .let_ (ts := ts) op k, plan, Γ, Δ, vs, ls, inVD, outVD, outLD, inVE,
      cont_p, cont_f, hΓ, hΔ, hmV, hwf, hcont => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denote]
    rw [denoteArgs_eq_some_resolveEnvArgs hΓ hmV op.args hwf.1]
    cases plan with
    | let_ rest =>
      dsimp only [hoistArm, hoistArmFlat, toTFlat]
      exact congrArg (TFlat.let_ _)
        (hoistArmFlat_eq jTs k rest (CtxTypes.push _ hΓ) hΔ
          (trieCtxMatch_insertTupEnv hmV _) hwf.2 hcont)
    | jump | ret | jnz _ _ => rfl
  | .jnz c t e, plan, Γ, Δ, vs, ls, inVD, outVD, outLD, inVE,
      cont_p, cont_f, hΓ, hΔ, hmV, hwf, hcont => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denote]
    rw [denoteArg_eq_some_resolveEnvArg hΓ hmV c hwf.1.1]
    cases plan with
    | jnz pT pE =>
      dsimp only [hoistArm, hoistArmFlat]
      apply hoistArmFlat_eq jTs t pT hΓ hΔ hmV hwf.1.2
      intro od₁ argsT
      apply hoistArmFlat_eq jTs e pE hΓ hΔ hmV hwf.2
      intro od₂ argsE
      exact emitSelectTupIValFlat_eq _ jTs od₂ outLD argsT argsE hcont
    | jump | ret | let_ _ => rfl
  | .load t a k, plan, Γ, _, vs, _, _, _, _, inVE, _, _, hΓ, _, hmV, hwf, _ => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denote]
    rw [denoteArg_eq_some_resolveEnvArg hΓ hmV a hwf.1]
    cases plan <;> rfl
  | .store v a k, plan, Γ, _, vs, _, _, _, _, inVE, _, _, hΓ, _, hmV, hwf, _ => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denote]
    rw [denoteArg_eq_some_resolveEnvArg hΓ hmV v hwf.1.1,
      denoteArg_eq_some_resolveEnvArg hΓ hmV a hwf.1.2]
    cases plan <;> rfl
  | .call f bs args k, plan, Γ, _, vs, _, _, _, _, inVE, _, _, hΓ, _, hmV, hwf, _ => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denote]
    rw [denoteArgs_eq_some_resolveEnvArgs hΓ hmV args hwf.1]
    cases plan <;> rfl
  | .exit f args, plan, Γ, _, vs, _, _, _, _, inVE, _, _, hΓ, _, hmV, hwf, _ => by
    dsimp only [denote]
    rw [denoteArgs_eq_some_resolveEnvArgs hΓ hmV args hwf]
    cases plan <;> rfl
  | .hlt, plan, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by
    cases plan <;> rfl
  | .group _ _, plan, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by
    cases plan <;> rfl

private theorem hoistJnzArmsFlat_eq {rs : List Ty} (jTs : List Ty)
    (pT pE : ArmPlan) (c : Arg (IVal K) .bool) (t e : TFlat rs)
    {Γ : List Ty} {Δ : List (List Ty)}
    {vs : List ((t : Ty) × IVal K t)} {ls : List ((ts : List Ty) × JLabel KL ts)}
    {inVD outVD outLD : Nat} {inVE : Trie ((t : Ty) × IVal K t)}
    {fin_p : Tup (Arg K) jTs → Expr K KL rs}
    {fin_f : Nat → Tup (Arg K) jTs → TFlat rs}
    (hΓ : CtxTypes Γ vs) (hΔ : CtxTypes Δ ls) (hmV : TrieCtxMatch inVD inVE vs)
    (ht : t.wfCheck Γ Δ = true) (he : e.wfCheck Γ Δ = true)
    (hfin : ∀ od sel, toTFlat (fin_p sel) od outLD = fin_f od sel) :
    toTFlat (hoistJnzArms jTs pT pE outVD c (denote (IVal K) (JLabel KL) t vs ls)
        (denote (IVal K) (JLabel KL) e vs ls) fin_p) outVD outLD =
      hoistJnzArmsFlat jTs pT pE (iout c) t e inVD inVE outVD fin_f := by
  dsimp only [hoistJnzArms, hoistJnzArmsFlat]
  apply hoistArmFlat_eq jTs t pT hΓ hΔ hmV ht
  intro od₁ argsT
  apply hoistArmFlat_eq jTs e pE hΓ hΔ hmV he
  intro od₂ argsE
  exact emitSelectTupFlat_eq (iout c) jTs od₂ outLD argsT argsE hfin

private theorem hoistStoreTailFlat_eq {rs : List Ty} (jTs : List Ty) :
    (tf : TFlat rs) → (tail : StoreTail) →
    {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × IVal K t)} → {ls : List ((ts : List Ty) × JLabel KL ts)} →
    {inVD outVD outLD : Nat} → {inVE : Trie ((t : Ty) × IVal K t)} →
    {cont_p : Nat → Tup (Arg (IVal K)) jTs → Expr K KL rs} →
    {cont_f : Nat → Tup (Arg (IVal K)) jTs → TFlat rs} →
    CtxTypes Γ vs → CtxTypes Δ ls → TrieCtxMatch inVD inVE vs → tf.wfCheck Γ Δ = true →
    (∀ od args, toTFlat (cont_p od args) od outLD = cont_f od args) →
    toTFlat (hoistStoreTail jTs tail outVD (denote (IVal K) (JLabel KL) tf vs ls) cont_p)
      outVD outLD = hoistStoreTailFlat jTs tail tf inVD inVE outVD cont_f
  | .jump (ts := ts) j args, tail, Γ, Δ, vs, ls, inVD, outVD, outLD, inVE,
      cont_p, cont_f, hΓ, hΔ, hmV, hwf, hcont => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨j', hj⟩ := Option.isSome_iff_exists.1 (lookupL_isSome_of_check hΔ hwf.1)
    dsimp only [denote]
    rw [hj, denoteArgs_eq_some_resolveEnvArgs hΓ hmV args hwf.2]
    cases tail <;> try rfl
    dsimp only [hoistStoreTail, hoistStoreTailFlat]
    cases listTyDecEq ts jTs with
    | isFalse _ => rfl
    | isTrue _ => exact hcont outVD _
  | .ret vs', tail, Γ, _, vs, _, inVD, outVD, outLD, inVE,
      cont_p, cont_f, hΓ, _, hmV, hwf, hcont => by
    dsimp only [denote]
    rw [denoteArgs_eq_some_resolveEnvArgs hΓ hmV vs' hwf]
    cases tail <;> try rfl
    dsimp only [hoistStoreTail, hoistStoreTailFlat]
    cases listTyDecEq rs jTs with
    | isFalse _ => rfl
    | isTrue _ => exact hcont outVD _
  | .let_ (ts := ts) op k, tail, Γ, Δ, vs, ls, inVD, outVD, outLD, inVE,
      cont_p, cont_f, hΓ, hΔ, hmV, hwf, hcont => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denote]
    rw [denoteArgs_eq_some_resolveEnvArgs hΓ hmV op.args hwf.1]
    cases tail with
    | let_ rest =>
      dsimp only [hoistStoreTail, hoistStoreTailFlat, toTFlat]
      exact congrArg (TFlat.let_ _)
        (hoistStoreTailFlat_eq jTs k rest (CtxTypes.push _ hΓ) hΔ
          (trieCtxMatch_insertTupEnv hmV _) hwf.2 hcont)
    | jump | ret => rfl
  | .jnz c t e, tail, Γ, _, vs, _, _, _, _, inVE, _, _, hΓ, _, hmV, hwf, _ => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denote]
    rw [denoteArg_eq_some_resolveEnvArg hΓ hmV c hwf.1.1]
    cases tail <;> rfl
  | .load t a k, tail, Γ, _, vs, _, _, _, _, inVE, _, _, hΓ, _, hmV, hwf, _ => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denote]
    rw [denoteArg_eq_some_resolveEnvArg hΓ hmV a hwf.1]
    cases tail <;> rfl
  | .store v a k, tail, Γ, _, vs, _, _, _, _, inVE, _, _, hΓ, _, hmV, hwf, _ => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denote]
    rw [denoteArg_eq_some_resolveEnvArg hΓ hmV v hwf.1.1,
      denoteArg_eq_some_resolveEnvArg hΓ hmV a hwf.1.2]
    cases tail <;> rfl
  | .call f bs args k, tail, Γ, _, vs, _, _, _, _, inVE, _, _, hΓ, _, hmV, hwf, _ => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denote]
    rw [denoteArgs_eq_some_resolveEnvArgs hΓ hmV args hwf.1]
    cases tail <;> rfl
  | .exit f args, tail, Γ, _, vs, _, _, _, _, inVE, _, _, hΓ, _, hmV, hwf, _ => by
    dsimp only [denote]
    rw [denoteArgs_eq_some_resolveEnvArgs hΓ hmV args hwf]
    cases tail <;> rfl
  | .hlt, tail, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by cases tail <;> rfl
  | .group _ _, tail, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by cases tail <;> rfl

private theorem hoistStoreStepFlat_eq {rs : List Ty} (jTs : List Ty) (st : Ty) :
    (tf : TFlat rs) → (step : StoreStep) → (loads : List ((t : Ty) × IVal K t)) →
    {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × IVal K t)} → {ls : List ((ts : List Ty) × JLabel KL ts)} →
    {inVD outVD outLD : Nat} → {inVE : Trie ((t : Ty) × IVal K t)} →
    {cont_p : Nat → List ((t : Ty) × IVal K t) → Arg (IVal K) st → Arg (IVal K) i64 →
      Tup (Arg (IVal K)) jTs → Expr K KL rs} →
    {cont_f : Nat → List ((t : Ty) × IVal K t) → Arg (IVal K) st → Arg (IVal K) i64 →
      Tup (Arg (IVal K)) jTs → TFlat rs} →
    CtxTypes Γ vs → CtxTypes Δ ls → TrieCtxMatch inVD inVE vs → tf.wfCheck Γ Δ = true →
    (∀ od lds v a args, toTFlat (cont_p od lds v a args) od outLD = cont_f od lds v a args) →
    toTFlat (hoistStoreStep jTs st step outVD loads (denote (IVal K) (JLabel KL) tf vs ls) cont_p)
      outVD outLD = hoistStoreStepFlat jTs st step tf inVD inVE outVD loads cont_f
  | .let_ (ts := ts) op k, step, loads, Γ, Δ, vs, ls, inVD, outVD, outLD, inVE,
      cont_p, cont_f, hΓ, hΔ, hmV, hwf, hcont => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denote]
    rw [denoteArgs_eq_some_resolveEnvArgs hΓ hmV op.args hwf.1]
    cases step with
    | let_ rest =>
      dsimp only [hoistStoreStep, hoistStoreStepFlat, toTFlat]
      exact congrArg (TFlat.let_ _)
        (hoistStoreStepFlat_eq jTs st k rest loads (CtxTypes.push _ hΓ) hΔ
          (trieCtxMatch_insertTupEnv hmV _) hwf.2 hcont)
    | loadEmit _ | loadReuse _ _ | store _ => rfl
  | .load t a k, step, loads, Γ, Δ, vs, ls, inVD, outVD, outLD, inVE,
      cont_p, cont_f, hΓ, hΔ, hmV, hwf, hcont => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denote]
    rw [denoteArg_eq_some_resolveEnvArg hΓ hmV a hwf.1]
    cases step with
    | loadEmit rest =>
      dsimp only [hoistStoreStep, hoistStoreStepFlat, toTFlat]
      exact congrArg (TFlat.load t _)
        (hoistStoreStepFlat_eq jTs st k rest _ (.cons hΓ) hΔ (hmV.cons t _) hwf.2 hcont)
    | loadReuse slot rest =>
      dsimp only [hoistStoreStep, hoistStoreStepFlat]
      rcases loads[slot]? with _ | ⟨t', iv⟩
      · rfl
      · dsimp only
        cases tyDecEq t' t with
        | isFalse _ => rfl
        | isTrue _ =>
          exact hoistStoreStepFlat_eq jTs st k rest loads (.cons hΓ) hΔ (hmV.cons t _) hwf.2 hcont
    | let_ _ | store _ => rfl
  | .store (t := st') v a k, step, loads, Γ, Δ, vs, ls, inVD, outVD, outLD, inVE,
      cont_p, cont_f, hΓ, hΔ, hmV, hwf, hcont => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denote]
    rw [denoteArg_eq_some_resolveEnvArg hΓ hmV v hwf.1.1,
      denoteArg_eq_some_resolveEnvArg hΓ hmV a hwf.1.2]
    cases step with
    | store tail =>
      dsimp only [hoistStoreStep, hoistStoreStepFlat]
      cases tyDecEq st' st with
      | isFalse _ => rfl
      | isTrue _ =>
        exact hoistStoreTailFlat_eq jTs k tail hΓ hΔ hmV hwf.2 fun od' exitArgs =>
          hcont od' loads _ _ exitArgs
    | let_ _ | loadEmit _ | loadReuse _ _ => rfl
  | .jump (ts := ts) j args, step, _, Γ, Δ, vs, ls, _, _, _, inVE,
      _, _, hΓ, hΔ, hmV, hwf, _ => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨j', hj⟩ := Option.isSome_iff_exists.1 (lookupL_isSome_of_check hΔ hwf.1)
    dsimp only [denote]
    rw [hj, denoteArgs_eq_some_resolveEnvArgs hΓ hmV args hwf.2]
    cases step <;> rfl
  | .ret vs', step, _, Γ, _, vs, _, _, _, _, inVE, _, _, hΓ, _, hmV, hwf, _ => by
    dsimp only [denote]
    rw [denoteArgs_eq_some_resolveEnvArgs hΓ hmV vs' hwf]
    cases step <;> rfl
  | .jnz c t e, step, _, Γ, _, vs, _, _, _, _, inVE, _, _, hΓ, _, hmV, hwf, _ => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denote]
    rw [denoteArg_eq_some_resolveEnvArg hΓ hmV c hwf.1.1]
    cases step <;> rfl
  | .call f bs args k, step, _, Γ, _, vs, _, _, _, _, inVE, _, _, hΓ, _, hmV, hwf, _ => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denote]
    rw [denoteArgs_eq_some_resolveEnvArgs hΓ hmV args hwf.1]
    cases step <;> rfl
  | .exit f args, step, _, Γ, _, vs, _, _, _, _, inVE, _, _, hΓ, _, hmV, hwf, _ => by
    dsimp only [denote]
    rw [denoteArgs_eq_some_resolveEnvArgs hΓ hmV args hwf]
    cases step <;> rfl
  | .hlt, step, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by cases step <;> rfl
  | .group _ _, step, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by cases step <;> rfl

private theorem hoistStoreArmsFlat_eq {rs : List Ty} (jTs : List Ty)
    (sp : StoreDiamondPlan) (c : Arg (IVal K) .bool) (t e : TFlat rs)
    {Γ : List Ty} {Δ : List (List Ty)}
    {vs : List ((t : Ty) × IVal K t)} {ls : List ((ts : List Ty) × JLabel KL ts)}
    {inVD outVD outLD : Nat} {inVE : Trie ((t : Ty) × IVal K t)}
    {fin_p : Tup (Arg K) jTs → Expr K KL rs}
    {fin_f : Nat → Tup (Arg K) jTs → TFlat rs}
    (hΓ : CtxTypes Γ vs) (hΔ : CtxTypes Δ ls) (hmV : TrieCtxMatch inVD inVE vs)
    (ht : t.wfCheck Γ Δ = true) (he : e.wfCheck Γ Δ = true)
    (hfin : ∀ od sel, toTFlat (fin_p sel) od outLD = fin_f od sel) :
    toTFlat (hoistStoreArms jTs sp outVD c (denote (IVal K) (JLabel KL) t vs ls)
        (denote (IVal K) (JLabel KL) e vs ls) fin_p) outVD outLD =
      hoistStoreArmsFlat jTs sp (iout c) t e inVD inVE outVD fin_f := by
  dsimp only [hoistStoreArms, hoistStoreArmsFlat]
  apply hoistStoreStepFlat_eq jTs sp.storeTy t sp.armT [] hΓ hΔ hmV ht
  intro od₁ loads₁ vT aT argsT
  apply hoistStoreStepFlat_eq jTs sp.storeTy e sp.armE loads₁ hΓ hΔ hmV he
  intro od₂ _ vE _ argsE
  apply emitSelectTyFlat_eq (iout c) sp.storeTy od₂ outLD vT vE
  intro od₃ selVal
  dsimp only [toTFlat]
  exact congrArg (TFlat.store _ _) (emitSelectTupFlat_eq (iout c) jTs od₃ outLD argsT argsE hfin)

private theorem hoistDiamondFlat_eq {rs : List Ty} {jTs : List Ty} (jLbl : KL jTs) :
    (tf : TFlat rs) → (plan : DiamondPlan) →
    {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × IVal K t)} → {ls : List ((ts : List Ty) × JLabel KL ts)} →
    {inVD outVD outLD : Nat} → {inVE : Trie ((t : Ty) × IVal K t)} →
    CtxTypes Γ vs → CtxTypes Δ ls → TrieCtxMatch inVD inVE vs → tf.wfCheck Γ Δ = true →
    toTFlat (hoistDiamond jLbl plan outVD (denote (IVal K) (JLabel KL) tf vs ls)) outVD outLD =
      hoistDiamondFlat jLbl plan tf inVD inVE outVD outLD
  | .jnz c t e, plan, Γ, Δ, vs, ls, inVD, outVD, outLD, inVE, hΓ, hΔ, hmV, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denote]
    rw [denoteArg_eq_some_resolveEnvArg hΓ hmV c hwf.1.1]
    cases plan with
    | jnz pT pE =>
      dsimp only [hoistDiamond, hoistDiamondFlat]
      exact hoistJnzArmsFlat_eq jTs pT pE _ t e hΓ hΔ hmV hwf.1.2 hwf.2 fun _ _ => rfl
    | jnzStore sp =>
      dsimp only [hoistDiamond, hoistDiamondFlat]
      exact hoistStoreArmsFlat_eq jTs sp _ t e hΓ hΔ hmV hwf.1.2 hwf.2 fun _ _ => rfl
    | let_ _ | load _ | store _ | call _ => rfl
  | .let_ (ts := ts) op k, plan, Γ, Δ, vs, ls, inVD, outVD, outLD, inVE, hΓ, hΔ, hmV, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denote]
    rw [denoteArgs_eq_some_resolveEnvArgs hΓ hmV op.args hwf.1]
    cases plan with
    | let_ rest =>
      dsimp only [hoistDiamond, hoistDiamondFlat, toTFlat]
      exact congrArg (TFlat.let_ _)
        (hoistDiamondFlat_eq jLbl k rest (CtxTypes.push _ hΓ) hΔ
          (trieCtxMatch_insertTupEnv hmV _) hwf.2)
    | jnz _ _ | jnzStore _ | load _ | store _ | call _ => rfl
  | .load t a k, plan, Γ, Δ, vs, ls, inVD, outVD, outLD, inVE, hΓ, hΔ, hmV, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denote]
    rw [denoteArg_eq_some_resolveEnvArg hΓ hmV a hwf.1]
    cases plan with
    | load rest =>
      dsimp only [hoistDiamond, hoistDiamondFlat, toTFlat]
      exact congrArg (TFlat.load t _)
        (hoistDiamondFlat_eq jLbl k rest (.cons hΓ) hΔ (hmV.cons t _) hwf.2)
    | jnz _ _ | jnzStore _ | let_ _ | store _ | call _ => rfl
  | .store v a k, plan, Γ, Δ, vs, ls, inVD, outVD, outLD, inVE, hΓ, hΔ, hmV, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denote]
    rw [denoteArg_eq_some_resolveEnvArg hΓ hmV v hwf.1.1,
      denoteArg_eq_some_resolveEnvArg hΓ hmV a hwf.1.2]
    cases plan with
    | store rest =>
      dsimp only [hoistDiamond, hoistDiamondFlat, toTFlat]
      exact congrArg (TFlat.store _ _) (hoistDiamondFlat_eq jLbl k rest hΓ hΔ hmV hwf.2)
    | jnz _ _ | jnzStore _ | let_ _ | load _ | call _ => rfl
  | .call f bs args k, plan, Γ, Δ, vs, ls, inVD, outVD, outLD, inVE, hΓ, hΔ, hmV, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denote]
    rw [denoteArgs_eq_some_resolveEnvArgs hΓ hmV args hwf.1]
    cases plan with
    | call rest =>
      dsimp only [hoistDiamond, hoistDiamondFlat, toTFlat]
      exact congrArg (TFlat.call f bs _)
        (hoistDiamondFlat_eq jLbl k rest (CtxTypes.push _ hΓ) hΔ
          (trieCtxMatch_insertTupEnv hmV _) hwf.2)
    | jnz _ _ | jnzStore _ | let_ _ | load _ | store _ => rfl
  | .jump (ts := ts) j args, plan, Γ, Δ, vs, ls, _, _, _, inVE, hΓ, hΔ, hmV, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨j', hj⟩ := Option.isSome_iff_exists.1 (lookupL_isSome_of_check hΔ hwf.1)
    dsimp only [denote]
    rw [hj, denoteArgs_eq_some_resolveEnvArgs hΓ hmV args hwf.2]
    cases plan <;> rfl
  | .ret vs', plan, Γ, _, vs, _, _, _, _, inVE, hΓ, _, hmV, hwf => by
    dsimp only [denote]
    rw [denoteArgs_eq_some_resolveEnvArgs hΓ hmV vs' hwf]
    cases plan <;> rfl
  | .exit f args, plan, Γ, _, vs, _, _, _, _, inVE, hΓ, _, hmV, hwf => by
    dsimp only [denote]
    rw [denoteArgs_eq_some_resolveEnvArgs hΓ hmV args hwf]
    cases plan <;> rfl
  | .hlt, plan, _, _, _, _, _, _, _, _, _, _, _, _ => by cases plan <;> rfl
  | .group _ _, plan, _, _, _, _, _, _, _, _, _, _, _, _ => by cases plan <;> rfl

private theorem tryPureJnzDiamondFlat_eq {rs : List Ty} (bitsOnly : Bool)
    (c : Arg (IVal K) .bool) (t e : TFlat rs)
    {Γ : List Ty} {Δ : List (List Ty)}
    {vs : List ((t : Ty) × IVal K t)} {ls : List ((ts : List Ty) × JLabel KL ts)}
    {inVD inLD outVD outLD : Nat}
    {inVE : Trie ((t : Ty) × IVal K t)} {inLE : Trie ((ts : List Ty) × JLabel KL ts)}
    (hΓ : CtxTypes Γ vs) (hΔ : CtxTypes Δ ls)
    (hmV : TrieCtxMatch inVD inVE vs) (hmL : TrieCtxMatch inLD inLE ls)
    (ht : t.wfCheck Γ Δ = true) (he : e.wfCheck Γ Δ = true) :
    (tryPureJnzDiamond bitsOnly outVD c
        (denote (IVal K) (JLabel KL) t vs ls)
        (denote (IVal K) (JLabel KL) e vs ls)).map (fun ex => toTFlat ex outVD outLD) =
      tryPureJnzDiamondFlat bitsOnly (iout c) t e inVD inVE inLD inLE outVD outLD := by
  dsimp only [tryPureJnzDiamond, tryPureJnzDiamondFlat]
  rw [findFirstJumpFlat_eq 8 t hΓ hΔ hmL ht]
  cases findFirstJumpFlat 8 inLD inLE t with
  | none =>
    dsimp only
    cases isSelectSigWith bitsOnly rs
    · simp only [Bool.false_eq_true, ↓reduceIte, Option.map_none]
    · simp only [↓reduceIte]
      rw [checkArmFlat_eq .ret t 2 4 outVD hΓ hΔ hmL ht,
        checkArmFlat_eq .ret e 2 4 outVD hΓ hΔ hmL he]
      cases h1 : checkArmFlat .ret 2 4 inLD inLE t with
      | none => rfl
      | some resT =>
        cases h2 : checkArmFlat .ret 2 4 inLD inLE e with
        | none => rfl
        | some resE =>
          dsimp only [Option.map_some]
          exact congrArg some (hoistJnzArmsFlat_eq rs resT.1 resE.1 c t e hΓ hΔ hmV ht he
            fun _ _ => rfl)
  | some tgt =>
    rcases tgt with ⟨jTs, jId, jLbl⟩
    dsimp only
    cases isSelectSigWith bitsOnly jTs
    · simp only [Bool.false_eq_true, ↓reduceIte, Option.map_none]
    · simp only [↓reduceIte]
      rw [checkArmFlat_eq (.tag jId jTs) t 2 4 outVD hΓ hΔ hmL ht,
        checkArmFlat_eq (.tag jId jTs) e 2 4 outVD hΓ hΔ hmL he]
      cases h1 : checkArmFlat (.tag jId jTs) 2 4 inLD inLE t with
      | none => rfl
      | some resT =>
        cases h2 : checkArmFlat (.tag jId jTs) 2 4 inLD inLE e with
        | none => rfl
        | some resE =>
          dsimp only [Option.map_some]
          exact congrArg some (hoistJnzArmsFlat_eq jTs resT.1 resE.1 c t e hΓ hΔ hmV ht he
            fun _ _ => rfl)

private theorem tryStoreJnzDiamondFlat_eq {rs : List Ty} (bitsOnly : Bool)
    (c : Arg (IVal K) .bool) (t e : TFlat rs)
    {Γ : List Ty} {Δ : List (List Ty)}
    {vs : List ((t : Ty) × IVal K t)} {ls : List ((ts : List Ty) × JLabel KL ts)}
    {inVD inLD outVD outLD : Nat}
    {inVE : Trie ((t : Ty) × IVal K t)} {inLE : Trie ((ts : List Ty) × JLabel KL ts)}
    (hΓ : CtxTypes Γ vs) (hΔ : CtxTypes Δ ls)
    (hmV : TrieCtxMatch inVD inVE vs) (hmL : TrieCtxMatch inLD inLE ls)
    (ht : t.wfCheck Γ Δ = true) (he : e.wfCheck Γ Δ = true) :
    (tryStoreJnzDiamond bitsOnly outVD c
        (denote (IVal K) (JLabel KL) t vs ls)
        (denote (IVal K) (JLabel KL) e vs ls)).map (fun ex => toTFlat ex outVD outLD) =
      tryStoreJnzDiamondFlat bitsOnly (iout c) t e inVD inVE inLD inLE outVD outLD := by
  dsimp only [tryStoreJnzDiamond, tryStoreJnzDiamondFlat]
  rw [findFirstJumpStoreFlat_eq 16 t hΓ hΔ hmL ht]
  cases findFirstJumpStoreFlat 16 inLD inLE t with
  | none =>
    dsimp only
    cases isSelectSigWith bitsOnly rs
    · simp only [Bool.false_eq_true, ↓reduceIte, Option.map_none]
    · simp only [↓reduceIte]
      rw [checkStoreArmsFlat_eq bitsOnly .ret t e hΓ hΔ hmV hmL ht he]
      cases checkStoreArmsFlat bitsOnly .ret inVD inVE inLD inLE outVD t e with
      | none => rfl
      | some sp =>
        dsimp only [Option.map_some]
        exact congrArg some (hoistStoreArmsFlat_eq rs sp c t e hΓ hΔ hmV ht he fun _ _ => rfl)
  | some tgt =>
    rcases tgt with ⟨jTs, jId, jLbl⟩
    dsimp only
    cases isSelectSigWith bitsOnly jTs
    · simp only [Bool.false_eq_true, ↓reduceIte, Option.map_none]
    · simp only [↓reduceIte]
      rw [checkStoreArmsFlat_eq bitsOnly (.tag jId jTs) t e hΓ hΔ hmV hmL ht he]
      cases checkStoreArmsFlat bitsOnly (.tag jId jTs) inVD inVE inLD inLE outVD t e with
      | none => rfl
      | some sp =>
        dsimp only [Option.map_some]
        exact congrArg some (hoistStoreArmsFlat_eq jTs sp c t e hΓ hΔ hmV ht he fun _ _ => rfl)

private theorem tryJnzDiamondFlat_eq {rs : List Ty} (bitsOnly : Bool)
    (c : Arg (IVal K) .bool) (t e : TFlat rs)
    {Γ : List Ty} {Δ : List (List Ty)}
    {vs : List ((t : Ty) × IVal K t)} {ls : List ((ts : List Ty) × JLabel KL ts)}
    {inVD inLD outVD outLD : Nat}
    {inVE : Trie ((t : Ty) × IVal K t)} {inLE : Trie ((ts : List Ty) × JLabel KL ts)}
    (hΓ : CtxTypes Γ vs) (hΔ : CtxTypes Δ ls)
    (hmV : TrieCtxMatch inVD inVE vs) (hmL : TrieCtxMatch inLD inLE ls)
    (ht : t.wfCheck Γ Δ = true) (he : e.wfCheck Γ Δ = true) :
    (tryJnzDiamond bitsOnly outVD c
        (denote (IVal K) (JLabel KL) t vs ls)
        (denote (IVal K) (JLabel KL) e vs ls)).map (fun ex => toTFlat ex outVD outLD) =
      tryJnzDiamondFlat bitsOnly (iout c) t e inVD inVE inLD inLE outVD outLD := by
  dsimp only [tryJnzDiamond, tryJnzDiamondFlat]
  have hp := tryPureJnzDiamondFlat_eq bitsOnly c t e hΓ hΔ hmV hmL ht he
    (outVD := outVD) (outLD := outLD)
  cases hopt : tryPureJnzDiamond bitsOnly outVD c
      (denote (IVal K) (JLabel KL) t vs ls) (denote (IVal K) (JLabel KL) e vs ls) with
  | some ex =>
    rw [hopt, Option.map_some] at hp
    rw [← hp]
    rfl
  | none =>
    rw [hopt, Option.map_none] at hp
    rw [← hp]
    exact tryStoreJnzDiamondFlat_eq bitsOnly c t e hΓ hΔ hmV hmL ht he

private theorem ifOptGroupBitsTrue {rs : List Ty} {sig : List (List Ty)}
    (bodies : TBlocks rs sig) (k : TFlat rs) (depth : Nat)
    {vs : List ((t : Ty) × IVal K t)} {ls : List ((ts : List Ty) × JLabel KL ts)}
    {inVD outVD inLD outLD : Nat}
    {inVE : Trie ((t : Ty) × IVal K t)} {inLE : Trie ((ts : List Ty) × JLabel KL ts)}
    (hb : toTBlocks (ifOptBWith true (depth + sig.length) outVD
        (denoteB (IVal K) (JLabel KL) bodies vs
          (pushTup (tagLabels depth (Tup.levels sig outLD)) ls)))
        outVD (outLD + sig.length) =
      ifOptBWithFlat true (depth + sig.length) bodies inVD inVE
        (inLD + sig.length) (insertTupEnv inLD inLE (tagLabels depth (Tup.levels sig outLD)))
        outVD (outLD + sig.length))
    (hk : toTFlat (ifOptWith true (depth + sig.length) outVD
        (denote (IVal K) (JLabel KL) k vs
          (pushTup (tagLabels depth (Tup.levels sig outLD)) ls)))
        outVD (outLD + sig.length) =
      ifOptWithFlat true (depth + sig.length) k inVD inVE
        (inLD + sig.length) (insertTupEnv inLD inLE (tagLabels depth (Tup.levels sig outLD)))
        outVD (outLD + sig.length)) :
    toTFlat (ifOptWith true depth outVD
        (denote (IVal K) (JLabel KL) (TFlat.group bodies k) vs ls)) outVD outLD =
      ifOptWithFlat true depth (TFlat.group bodies k) inVD inVE inLD inLE outVD outLD := by
  dsimp only [denote]
  rw [ifOptWith.eq_def, ifOptWithFlat.eq_def]
  simp only [↓reduceIte, toTFlat]
  rw [hb, hk]

mutual
private theorem ifOptWithFlat_eq (bitsOnly : Bool) {rs : List Ty} :
    (tf : TFlat rs) → (depth : Nat) →
    {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × IVal K t)} → {ls : List ((ts : List Ty) × JLabel KL ts)} →
    {inVD outVD inLD outLD : Nat} →
    {inVE : Trie ((t : Ty) × IVal K t)} → {inLE : Trie ((ts : List Ty) × JLabel KL ts)} →
    CtxTypes Γ vs → CtxTypes Δ ls →
    TrieCtxMatch inVD inVE vs → TrieCtxMatch inLD inLE ls → tf.wfCheck Γ Δ = true →
    toTFlat (ifOptWith bitsOnly depth outVD (denote (IVal K) (JLabel KL) tf vs ls))
        outVD outLD =
      ifOptWithFlat bitsOnly depth tf inVD inVE inLD inLE outVD outLD
  | .let_ (ts := ts) op k, depth, Γ, Δ, vs, ls, inVD, outVD, inLD, outLD, inVE, inLE,
      hΓ, hΔ, hmV, hmL, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denote]
    rw [denoteArgs_eq_some_resolveEnvArgs hΓ hmV op.args hwf.1]
    dsimp only [ifOptWith, ifOptWithFlat, toTFlat]
    exact congrArg (TFlat.let_ _)
      (ifOptWithFlat_eq bitsOnly k depth (CtxTypes.push _ hΓ) hΔ
        (trieCtxMatch_insertTupEnv hmV _) hmL hwf.2)
  | .load t a k, depth, Γ, Δ, vs, ls, inVD, outVD, inLD, outLD, inVE, inLE,
      hΓ, hΔ, hmV, hmL, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denote]
    rw [denoteArg_eq_some_resolveEnvArg hΓ hmV a hwf.1]
    dsimp only [ifOptWith, ifOptWithFlat, toTFlat]
    exact congrArg (TFlat.load t _)
      (ifOptWithFlat_eq bitsOnly k depth (.cons hΓ) hΔ (hmV.cons t _) hmL hwf.2)
  | .store v a k, depth, Γ, Δ, vs, ls, inVD, outVD, inLD, outLD, inVE, inLE,
      hΓ, hΔ, hmV, hmL, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denote]
    rw [denoteArg_eq_some_resolveEnvArg hΓ hmV v hwf.1.1,
      denoteArg_eq_some_resolveEnvArg hΓ hmV a hwf.1.2]
    dsimp only [ifOptWith, ifOptWithFlat, toTFlat]
    exact congrArg (TFlat.store _ _)
      (ifOptWithFlat_eq bitsOnly k depth hΓ hΔ hmV hmL hwf.2)
  | .call f bs args k, depth, Γ, Δ, vs, ls, inVD, outVD, inLD, outLD, inVE, inLE,
      hΓ, hΔ, hmV, hmL, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denote]
    rw [denoteArgs_eq_some_resolveEnvArgs hΓ hmV args hwf.1]
    dsimp only [ifOptWith, ifOptWithFlat, toTFlat]
    exact congrArg (TFlat.call f bs _)
      (ifOptWithFlat_eq bitsOnly k depth (CtxTypes.push _ hΓ) hΔ
        (trieCtxMatch_insertTupEnv hmV _) hmL hwf.2)
  | .jnz c t e, depth, Γ, Δ, vs, ls, inVD, outVD, inLD, outLD, inVE, inLE,
      hΓ, hΔ, hmV, hmL, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denote]
    rw [denoteArg_eq_some_resolveEnvArg hΓ hmV c hwf.1.1]
    have ht := ifOptWithFlat_eq bitsOnly t depth hΓ hΔ hmV hmL hwf.1.2
      (outVD := outVD) (outLD := outLD)
    have he := ifOptWithFlat_eq bitsOnly e depth hΓ hΔ hmV hmL hwf.2
      (outVD := outVD) (outLD := outLD)
    dsimp only [ifOptWith, ifOptWithFlat]
    cases bitsOnly with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, toTFlat]
      rw [ht, he]
    | true =>
      have htry := tryJnzDiamondFlat_eq true (resolveEnvArg inVD inVE c) t e hΓ hΔ hmV hmL
        hwf.1.2 hwf.2 (outVD := outVD) (outLD := outLD)
      simp only [↓reduceIte]
      cases hopt : tryJnzDiamond true outVD (resolveEnvArg inVD inVE c)
          (denote (IVal K) (JLabel KL) t vs ls) (denote (IVal K) (JLabel KL) e vs ls) with
      | none =>
        rw [hopt, Option.map_none] at htry
        rw [← htry]
        dsimp only [Option.getD, toTFlat]
        rw [ht, he]
      | some ex =>
        rw [hopt, Option.map_some] at htry
        rw [← htry]
        rfl
  | .jump (ts := ts) j args, _, Γ, Δ, vs, ls, inVD, outVD, inLD, outLD, inVE, inLE,
      hΓ, hΔ, hmV, hmL, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨jl, hlk, hres⟩ := lookupL_eq_some_resolveLabel hΔ hmL hwf.1
    dsimp only [denote]
    rw [hlk, denoteArgs_eq_some_resolveEnvArgs hΓ hmV args hwf.2]
    dsimp only [ifOptWith, ifOptWithFlat]
    rw [hres]
    dsimp only
    cases unwrapJLabel jl <;> rfl
  | .ret vs', _, Γ, _, vs, _, inVD, outVD, _, _, inVE, _, hΓ, _, hmV, _, hwf => by
    dsimp only [denote]
    rw [denoteArgs_eq_some_resolveEnvArgs hΓ hmV vs' hwf]
    rfl
  | .exit f args, _, Γ, _, vs, _, inVD, outVD, _, _, inVE, _, hΓ, _, hmV, _, hwf => by
    dsimp only [denote]
    rw [denoteArgs_eq_some_resolveEnvArgs hΓ hmV args hwf]
    rfl
  | .hlt, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => rfl
  | .group (sig := []) bodies k, depth, Γ, Δ, vs, ls, inVD, outVD, inLD, outLD, inVE, inLE,
      hΓ, hΔ, hmV, hmL, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    cases bitsOnly with
    | true =>
      let tagged := tagLabels depth (Tup.levels [] outLD)
      have hb := ifOptBWithFlat_eq true bodies (depth + ([] : List (List Ty)).length) hΓ
        (CtxTypes.push tagged hΔ) hmV (trieCtxMatch_insertTupEnv hmL tagged) hwf.1
        (outVD := outVD) (outLD := outLD + ([] : List (List Ty)).length)
      have hk := ifOptWithFlat_eq true k (depth + ([] : List (List Ty)).length) hΓ
        (CtxTypes.push tagged hΔ) hmV (trieCtxMatch_insertTupEnv hmL tagged) hwf.2
        (outVD := outVD) (outLD := outLD + ([] : List (List Ty)).length)
      exact ifOptGroupBitsTrue bodies k depth hb hk
    | false =>
      simp only [denote, ifOptWith, ifOptWithFlat, Bool.false_eq_true, ↓reduceIte, toTFlat,
        List.length_nil, Nat.add_zero]
      dsimp only [Tup.levels, Tup.map, pushTup]
      rw [ifOptBWithFlat_eq false bodies depth hΓ hΔ hmV hmL hwf.1,
        ifOptWithFlat_eq false k depth hΓ hΔ hmV hmL hwf.2]
  | .group (sig := [ts]) bodies k, depth, Γ, Δ, vs, ls, inVD, outVD, inLD, outLD, inVE, inLE,
      hΓ, hΔ, hmV, hmL, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    cases bitsOnly with
    | true =>
      let tagged := tagLabels depth (Tup.levels [ts] outLD)
      have hb := ifOptBWithFlat_eq true bodies (depth + [ts].length) hΓ
        (CtxTypes.push tagged hΔ) hmV (trieCtxMatch_insertTupEnv hmL tagged) hwf.1
        (outVD := outVD) (outLD := outLD + [ts].length)
      have hk := ifOptWithFlat_eq true k (depth + [ts].length) hΓ
        (CtxTypes.push tagged hΔ) hmV (trieCtxMatch_insertTupEnv hmL tagged) hwf.2
        (outVD := outVD) (outLD := outLD + [ts].length)
      exact ifOptGroupBitsTrue bodies k depth hb hk
    | false =>
      simp only [denote, ifOptWith, ifOptWithFlat, Bool.false_eq_true, ↓reduceIte, toTFlat,
        List.length_cons, List.length_nil, Nat.zero_add]
      dsimp only [Tup.levels, Tup.map, pushTup]
      have hcd := checkDiamondFlat_eq false depth ts k outVD
        hΓ (.cons hΔ) hmV (hmL.cons ts (.loc depth)) hwf.2
      rw [hcd]
      have hb := ifOptBWithFlat_eq false bodies (depth + 1) hΓ (.cons hΔ)
        hmV (hmL.cons ts (.outer outLD)) hwf.1
        (outVD := outVD) (outLD := outLD + 1)
      rw [hb]
      cases hplan : checkDiamondFlat false depth ts inVD inVE (inLD + 1)
          (inLE.insert inLD ⟨ts, .loc depth⟩) outVD k with
      | none =>
        have hk := ifOptWithFlat_eq false k (depth + 1) hΓ (.cons hΔ)
          hmV (hmL.cons ts (.outer outLD)) hwf.2
          (outVD := outVD) (outLD := outLD + 1)
        rw [hk]
      | some plan =>
        have hk := hoistDiamondFlat_eq (jTs := ts) outLD k plan hΓ (.cons hΔ) hmV hwf.2
          (ls := ⟨ts, .outer outLD⟩ :: ls) (outVD := outVD) (outLD := outLD + 1)
        rw [hk]
  | .group (sig := ts :: ts₂ :: rest) bodies k, depth, Γ, Δ, vs, ls,
      inVD, outVD, inLD, outLD, inVE, inLE, hΓ, hΔ, hmV, hmL, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    cases bitsOnly with
    | true =>
      let tagged := tagLabels depth (Tup.levels (ts :: ts₂ :: rest) outLD)
      have hb := ifOptBWithFlat_eq true bodies (depth + (ts :: ts₂ :: rest).length) hΓ
        (CtxTypes.push tagged hΔ) hmV (trieCtxMatch_insertTupEnv hmL tagged) hwf.1
        (outVD := outVD) (outLD := outLD + (ts :: ts₂ :: rest).length)
      have hk := ifOptWithFlat_eq true k (depth + (ts :: ts₂ :: rest).length) hΓ
        (CtxTypes.push tagged hΔ) hmV (trieCtxMatch_insertTupEnv hmL tagged) hwf.2
        (outVD := outVD) (outLD := outLD + (ts :: ts₂ :: rest).length)
      exact ifOptGroupBitsTrue bodies k depth hb hk
    | false =>
      simp only [denote, ifOptWith, ifOptWithFlat, Bool.false_eq_true, ↓reduceIte, toTFlat]
      let outer := (Tup.levels (ts :: ts₂ :: rest) outLD).map fun _ l => JLabel.outer l
      have hb := ifOptBWithFlat_eq false bodies (depth + rest.length + 2) hΓ
        (CtxTypes.push outer hΔ) hmV (trieCtxMatch_insertTupEnv hmL outer) hwf.1
        (outVD := outVD) (outLD := outLD + (ts :: ts₂ :: rest).length)
      have hk := ifOptWithFlat_eq false k (depth + rest.length + 2) hΓ
        (CtxTypes.push outer hΔ) hmV (trieCtxMatch_insertTupEnv hmL outer) hwf.2
        (outVD := outVD) (outLD := outLD + (ts :: ts₂ :: rest).length)
      rw [hb, hk]

private theorem ifOptBWithFlat_eq (bitsOnly : Bool) {rs : List Ty} :
    {sig : List (List Ty)} → (tb : TBlocks rs sig) → (depth : Nat) →
    {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × IVal K t)} → {ls : List ((ts : List Ty) × JLabel KL ts)} →
    {inVD outVD inLD outLD : Nat} →
    {inVE : Trie ((t : Ty) × IVal K t)} → {inLE : Trie ((ts : List Ty) × JLabel KL ts)} →
    CtxTypes Γ vs → CtxTypes Δ ls →
    TrieCtxMatch inVD inVE vs → TrieCtxMatch inLD inLE ls → tb.wfCheck Γ Δ = true →
    toTBlocks (ifOptBWith bitsOnly depth outVD (denoteB (IVal K) (JLabel KL) tb vs ls))
        outVD outLD =
      ifOptBWithFlat bitsOnly depth tb inVD inVE inLD inLE outVD outLD
  | _, .nil, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => rfl
  | _, .cons (ts := ts) b bs, depth, Γ, Δ, vs, ls, inVD, outVD, inLD, outLD, inVE, inLE,
      hΓ, hΔ, hmV, hmL, hwf => by
    dsimp only [TBlocks.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denoteB, ifOptBWith, ifOptBWithFlat, toTBlocks]
    rw [ifOptWithFlat_eq bitsOnly b depth (CtxTypes.push _ hΓ) hΔ
        (trieCtxMatch_insertTupEnv hmV _) hmL hwf.1,
      ifOptBWithFlat_eq bitsOnly bs depth hΓ hΔ hmV hmL hwf.2]
end

/-- `ifOptFlat bitsOnly as tf = reifyFunc (Func.ifOptWith bitsOnly (denoteFunc tf))` under
`wfCheck = true`. -/
theorem ifOptFlat_eq (bitsOnly : Bool) {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    ifOptFlat bitsOnly as tf =
      reifyFunc (Func.ifOptWith bitsOnly (denoteFunc (as := as) tf)) := by
  have hm := trieCtxMatch_initEnv (W := IVal K) (fun x next => (.var x, .var next)) as
  have h := ifOptWithFlat_eq bitsOnly tf 0 (CtxTypes.push _ .nil) .nil hm TrieCtxMatch.empty hwf
    (outVD := as.length) (outLD := 0)
  dsimp only [ifOptFlat, Func.ifOptWith, reifyFunc, denoteFunc] at h ⊢
  exact h.symm

/-- `ifOptFlat false as tf = reifyFunc (Func.ifOpt (denoteFunc tf))` under `wfCheck = true`. -/
theorem ifOptFlat_false_eq {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    ifOptFlat false as tf = reifyFunc (Func.ifOpt (denoteFunc (as := as) tf)) :=
  ifOptFlat_eq false tf hwf

/-- `ifOptFlat true as tf = reifyFunc (Func.ifOptBits (denoteFunc tf))` under
`wfCheck = true`. -/
theorem ifOptFlat_true_eq {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    ifOptFlat true as tf = reifyFunc (Func.ifOptBits (denoteFunc (as := as) tf)) :=
  ifOptFlat_eq true tf hwf

/-- `denoteFunc (ifOptFlat bitsOnly as tf) = Func.ifOptWith bitsOnly (denoteFunc tf)` under
`wfCheck = true`. -/
theorem denoteFunc_ifOptFlat (bitsOnly : Bool) {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    denoteFunc (as := as) (ifOptFlat bitsOnly as tf) =
      Func.ifOptWith bitsOnly (denoteFunc (as := as) tf) := by
  rw [ifOptFlat_eq bitsOnly tf hwf]
  exact Func.renorm_eq_self (Func.ifOptWith_wf bitsOnly (Func.wf_of_denote tf rfl))

/-- `denoteFunc (ifOptFlat false as tf) = Func.ifOpt (denoteFunc tf)` under `wfCheck = true`. -/
theorem denoteFunc_ifOptFlat_false {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    denoteFunc (as := as) (ifOptFlat false as tf) = Func.ifOpt (denoteFunc (as := as) tf) :=
  denoteFunc_ifOptFlat false tf hwf

/-- `denoteFunc (ifOptFlat true as tf) = Func.ifOptBits (denoteFunc tf)` under
`wfCheck = true`. -/
theorem denoteFunc_ifOptFlat_true {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    denoteFunc (as := as) (ifOptFlat true as tf) = Func.ifOptBits (denoteFunc (as := as) tf) :=
  denoteFunc_ifOptFlat true tf hwf

/-- `ifOptFlat` preserves `wfCheck`. -/
theorem ifOptFlat_wfCheck (bitsOnly : Bool) {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    (ifOptFlat bitsOnly as tf).wfCheck (pushTypes as []) [] = true := by
  rw [ifOptFlat_eq bitsOnly tf hwf]
  exact PassFlatKit.reifyFunc_wfCheck (Func.ifOptWith_wf bitsOnly (Func.wf_of_denote tf rfl))

/-- `(ifOptFlatFn bitsOnly f).toFn = ⟨f.name, f.as, f.rs, Func.ifOptWith bitsOnly f.toFn.body⟩`
under `wfCheck = true`. -/
theorem ifOptFlatFn_toFn (bitsOnly : Bool) (f : TFlatFn) (hwf : f.wfCheck = true) :
    (ifOptFlatFn bitsOnly f).toFn =
      ⟨f.name, f.as, f.rs, Func.ifOptWith bitsOnly f.toFn.body⟩ := by
  dsimp only [ifOptFlatFn, TFlatFn.toFn]
  rw [denoteFunc_ifOptFlat bitsOnly f.body hwf]

/-- `ifOptFlatFn` preserves `TFlatFn.wfCheck`. -/
theorem ifOptFlatFn_wfCheck (bitsOnly : Bool) (f : TFlatFn) (hwf : f.wfCheck = true) :
    (ifOptFlatFn bitsOnly f).wfCheck = true :=
  ifOptFlat_wfCheck bitsOnly f.body hwf

end IfOptProofs

end OptFlatCfg
end LeanQbe.T
