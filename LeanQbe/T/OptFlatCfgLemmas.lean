/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanQbe Contributors
-/
module

public import LeanQbe.T.OptFlatCfgLemmas0
public import LeanQbe.T.OptFlatCfg
import LeanQbe.T.OptFlatSimKit
import LeanQbe.T.IfOptLemmas

/-!
# Equivalence Proofs for `OptFlatCfg` `ifOptFlat` (and Re-Exports of `OptFlatCfgLemmas0`)

Proves exact `=` correspondence (`std3` axioms only) between `OptFlatCfg.ifOptFlat` and
`Func.ifOptWith` via `OptFlatSimKit.relSim_mutual`, while re-exporting `OptFlatCfgLemmas0`.
-/

set_option autoImplicit false

namespace LeanQbe.T
namespace OptFlatCfg

open OptFlatPlanKit OptFlatSimKit

/-! ## `ifOptFlat` Simulation Proofs -/

section IfOptProofs
open IfOptImpl

private theorem ival_arg {V : Ty → Type} {Γ : List Ty} {vs : List ((t : Ty) × V t)}
    (hΓ : CtxTypes Γ vs) {t : Ty} {a : Arg K t} (hc : checkArg Γ t a = true) :
    ∃ a', denoteArg vs a = some a' :=
  Option.isSome_iff_exists.1 (denoteArg_isSome_of_checkArg hΓ hc)

private theorem ival_args {V : Ty → Type} {Γ : List Ty} {vs : List ((t : Ty) × V t)}
    (hΓ : CtxTypes Γ vs) {ts : List Ty} {args : Tup (Arg K) ts} (hc : checkArgs Γ args = true) :
    ∃ args', denoteArgs vs args = some args' :=
  Option.isSome_iff_exists.1 (denoteArgs_isSome_of_checkArgs hΓ hc)

local macro "ival_denote_close" hΓ:ident hΔ:ident hwf:ident
    rest:tacticSeq : tactic => `(tactic| first
  | (($rest); done)
  | (obtain ⟨ha, _⟩ := wf_load $hwf; obtain ⟨_, ha'⟩ := ival_arg $hΓ ha;
      dsimp only [denote]; rw [ha']; ($rest); done)
  | (obtain ⟨hv, ha, _⟩ := wf_store $hwf; obtain ⟨_, hv'⟩ := ival_arg $hΓ hv;
      obtain ⟨_, ha'⟩ := ival_arg $hΓ ha; dsimp only [denote]; rw [hv', ha']; ($rest); done)
  | (obtain ⟨ha, _⟩ := wf_call $hwf; obtain ⟨_, ha'⟩ := ival_args $hΓ ha;
      dsimp only [denote]; rw [ha']; ($rest); done)
  | (obtain ⟨hc, _⟩ := wf_jnz $hwf; obtain ⟨_, hc'⟩ := ival_arg $hΓ hc;
      dsimp only [denote]; rw [hc']; ($rest); done)
  | (obtain ⟨hj, ha⟩ := wf_jump $hwf;
      obtain ⟨_, hj'⟩ := Option.isSome_iff_exists.1 (lookupL_isSome_of_check $hΔ hj);
      obtain ⟨_, ha'⟩ := ival_args $hΓ ha; dsimp only [denote]; rw [hj', ha']; ($rest); done)
  | (obtain ⟨_, hv'⟩ := ival_args $hΓ $hwf; dsimp only [denote]; rw [hv']; ($rest); done))

local macro "env_denote_close" hΓ:ident hΔ:ident hmV:ident hwf:ident
    rest:tacticSeq : tactic => `(tactic| first
  | (($rest); done)
  | (dsimp only [denote]; rw [denoteArgs_eq_some_resolveEnvArgs $hΓ $hmV _ $hwf]; ($rest); done)
  | (obtain ⟨ha, _⟩ := wf_load $hwf; dsimp only [denote];
      rw [denoteArg_eq_some_resolveEnvArg $hΓ $hmV _ ha]; ($rest); done)
  | (obtain ⟨hv, ha, _⟩ := wf_store $hwf; dsimp only [denote];
      rw [denoteArg_eq_some_resolveEnvArg $hΓ $hmV _ hv,
          denoteArg_eq_some_resolveEnvArg $hΓ $hmV _ ha]; ($rest); done)
  | (obtain ⟨ha, _⟩ := wf_call $hwf; dsimp only [denote];
      rw [denoteArgs_eq_some_resolveEnvArgs $hΓ $hmV _ ha]; ($rest); done)
  | (obtain ⟨hc, _⟩ := wf_jnz $hwf; dsimp only [denote];
      rw [denoteArg_eq_some_resolveEnvArg $hΓ $hmV _ hc]; ($rest); done)
  | (obtain ⟨hj, ha⟩ := wf_jump $hwf;
      obtain ⟨_, hj'⟩ := Option.isSome_iff_exists.1 (lookupL_isSome_of_check $hΔ hj);
      dsimp only [denote];
      rw [hj', denoteArgs_eq_some_resolveEnvArgs $hΓ $hmV _ ha]; ($rest); done))

local macro "ffj_jump" hwf:ident "," hΓ:ident "," hΔ:ident "," hmL:ident ","
    f₁:Lean.Parser.Tactic.simpLemma "," f₂:Lean.Parser.Tactic.simpLemma : tactic => `(tactic| (
  obtain ⟨hj, ha⟩ := wf_jump $hwf
  obtain ⟨jl, hlk, hres⟩ := lookupL_eq_some_resolveLabel $hΔ $hmL hj
  obtain ⟨_, ha'⟩ := ival_args $hΓ ha
  dsimp only [denote]; rw [hlk, ha']; dsimp only [$f₁, $f₂]; rw [hres]; cases jl <;> rfl))

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
    | jump j args => ffj_jump hwf, hΓ, hΔ, hmL, findFirstJump, findFirstJumpFlat
    | let_ op k =>
      obtain ⟨ha, hk⟩ := wf_let hwf; obtain ⟨_, ha'⟩ := ival_args hΓ ha
      dsimp only [denote]; rw [ha']; dsimp only [findFirstJump, findFirstJumpFlat]
      exact findFirstJumpFlat_eq fuel k (CtxTypes.push _ hΓ) hΔ hmL hk
    | jnz c t e =>
      obtain ⟨hc, ht, _⟩ := wf_jnz hwf; obtain ⟨_, hc'⟩ := ival_arg hΓ hc
      dsimp only [denote]; rw [hc']; dsimp only [findFirstJump, findFirstJumpFlat]
      exact findFirstJumpFlat_eq fuel t hΓ hΔ hmL ht
    | _ => ival_denote_close hΓ hΔ hwf rfl

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
    | jump j args => ffj_jump hwf, hΓ, hΔ, hmL, findFirstJumpStore, findFirstJumpStoreFlat
    | let_ op k =>
      obtain ⟨ha, hk⟩ := wf_let hwf; obtain ⟨_, ha'⟩ := ival_args hΓ ha
      dsimp only [denote]; rw [ha']; dsimp only [findFirstJumpStore, findFirstJumpStoreFlat]
      exact findFirstJumpStoreFlat_eq fuel k (CtxTypes.push _ hΓ) hΔ hmL hk
    | load t a k =>
      obtain ⟨ha, hk⟩ := wf_load hwf; obtain ⟨_, ha'⟩ := ival_arg hΓ ha
      dsimp only [denote]; rw [ha']; dsimp only [findFirstJumpStore, findFirstJumpStoreFlat]
      exact findFirstJumpStoreFlat_eq fuel k (.cons hΓ) hΔ hmL hk
    | store v a k =>
      obtain ⟨hv, ha, hk⟩ := wf_store hwf
      obtain ⟨_, hv'⟩ := ival_arg hΓ hv; obtain ⟨_, ha'⟩ := ival_arg hΓ ha
      dsimp only [denote]; rw [hv', ha']; dsimp only [findFirstJumpStore, findFirstJumpStoreFlat]
      exact findFirstJumpStoreFlat_eq fuel k hΓ hΔ hmL hk
    | _ => ival_denote_close hΓ hΔ hwf rfl

private theorem checkArmFlat_eq {rs : List Ty} (tgt : ArmTarget)
    (tf : TFlat rs) (jnzFuel letFuel next : Nat)
    {Γ : List Ty} {Δ : List (List Ty)}
    {vs : List ((t : Ty) × IVal K t)} {ls : List ((ts : List Ty) × JLabel KL ts)}
    {inLD : Nat} {inLE : Trie ((ts : List Ty) × JLabel KL ts)}
    (hΓ : CtxTypes Γ vs) (hΔ : CtxTypes Δ ls)
    (hmL : TrieCtxMatch inLD inLE ls) (hwf : tf.wfCheck Γ Δ = true) :
    checkArm tgt jnzFuel letFuel next (denote (IVal K) (JLabel KL) tf vs ls) =
      checkArmFlat tgt jnzFuel letFuel inLD inLE tf := by
  cases tf with
  | let_ op k =>
    obtain ⟨ha, hk⟩ := wf_let hwf; obtain ⟨_, ha'⟩ := ival_args hΓ ha
    dsimp only [denote]; rw [ha']; dsimp only
    cases letFuel with
    | zero => dsimp only [checkArm, checkArmFlat]
    | succ letFuel' =>
      dsimp only [checkArm, checkArmFlat]
      cases isSafeOp op.code with
      | false => simp only [Bool.false_eq_true, ↓reduceIte]
      | true =>
        simp only [↓reduceIte]
        rw [checkArmFlat_eq tgt k jnzFuel letFuel' (next + _)
          (CtxTypes.push _ hΓ) hΔ hmL hk]
  | jump j args =>
    obtain ⟨hj, ha⟩ := wf_jump hwf
    obtain ⟨jl, hlk, hres⟩ := lookupL_eq_some_resolveLabel hΔ hmL hj
    obtain ⟨_, ha'⟩ := ival_args hΓ ha
    dsimp only [denote]; rw [hlk, ha']; dsimp only [checkArm, checkArmFlat]; rw [hres]
    cases tgt <;> cases jl <;> rfl
  | ret vs' =>
    obtain ⟨_, hv'⟩ := ival_args hΓ hwf
    dsimp only [denote]; rw [hv']; cases tgt <;> simp [checkArm, checkArmFlat]
  | jnz c t e =>
    obtain ⟨hc, ht, he⟩ := wf_jnz hwf; obtain ⟨_, hc'⟩ := ival_arg hΓ hc
    dsimp only [denote]; rw [hc']; dsimp only
    cases jnzFuel with
    | zero => simp [checkArm, checkArmFlat]
    | succ jnzFuel' =>
      dsimp only [checkArm, checkArmFlat, bind, Option.bind]
      rw [checkArmFlat_eq tgt t jnzFuel' letFuel next hΓ hΔ hmL ht]
      cases checkArmFlat tgt jnzFuel' letFuel inLD inLE t with
      | none => rfl
      | some res => dsimp only; rw [checkArmFlat_eq tgt e jnzFuel' res.2 next hΓ hΔ hmL he]
  | _ => ival_denote_close hΓ hΔ hwf (dsimp only [denote]; simp [checkArm, checkArmFlat])

private theorem checkStoreTailFlat_eq {rs : List Ty} (tgt : ArmTarget)
    (tf : TFlat rs) (letFuel : Nat)
    {Γ : List Ty} {Δ : List (List Ty)}
    {vs : List ((t : Ty) × IVal K t)} {ls : List ((ts : List Ty) × JLabel KL ts)}
    {inLD : Nat} {inLE : Trie ((ts : List Ty) × JLabel KL ts)}
    (hΓ : CtxTypes Γ vs) (hΔ : CtxTypes Δ ls)
    (hmL : TrieCtxMatch inLD inLE ls) (hwf : tf.wfCheck Γ Δ = true) :
    checkStoreTail tgt letFuel (denote (IVal K) (JLabel KL) tf vs ls) =
      checkStoreTailFlat tgt letFuel inLD inLE tf := by
  cases tf with
  | let_ op k =>
    obtain ⟨ha, hk⟩ := wf_let hwf; obtain ⟨_, ha'⟩ := ival_args hΓ ha
    dsimp only [denote]; rw [ha']; unfold checkStoreTail checkStoreTailFlat; dsimp only
    cases isSafeOp op.code with
    | false => simp only [Bool.false_eq_true, ↓reduceIte]
    | true =>
      simp only [↓reduceIte]
      cases letFuel with
      | zero => rfl
      | succ letFuel' =>
        dsimp only
        rw [checkStoreTailFlat_eq tgt k letFuel' (CtxTypes.push _ hΓ) hΔ hmL hk]
  | jump j args =>
    obtain ⟨hj, ha⟩ := wf_jump hwf
    obtain ⟨jl, hlk, hres⟩ := lookupL_eq_some_resolveLabel hΔ hmL hj
    obtain ⟨_, ha'⟩ := ival_args hΓ ha
    dsimp only [denote]; rw [hlk, ha']; unfold checkStoreTail checkStoreTailFlat; rw [hres]
    cases tgt <;> cases jl <;> rfl
  | ret vs' =>
    obtain ⟨_, hv'⟩ := ival_args hΓ hwf
    dsimp only [denote]; rw [hv']; unfold checkStoreTail checkStoreTailFlat; cases tgt <;> rfl
  | _ =>
    ival_denote_close hΓ hΔ hwf (dsimp only [denote]; simp [checkStoreTail, checkStoreTailFlat])

private theorem checkStoreArmFlat_eq {rs : List Ty} (tgt : ArmTarget) (allowNewLoads : Bool)
    (tf : TFlat rs) (letFuel loadFuel : Nat) (tbl : SymTbl) (hits : List Nat)
    {Γ : List Ty} {Δ : List (List Ty)}
    {vs : List ((t : Ty) × IVal K t)} {ls : List ((ts : List Ty) × JLabel KL ts)}
    {inVD inLD : Nat}
    {inVE : Trie ((t : Ty) × IVal K t)} {inLE : Trie ((ts : List Ty) × JLabel KL ts)}
    (hΓ : CtxTypes Γ vs) (hΔ : CtxTypes Δ ls)
    (hmV : TrieCtxMatch inVD inVE vs) (hmL : TrieCtxMatch inLD inLE ls)
    (hwf : tf.wfCheck Γ Δ = true) :
    checkStoreArm tgt allowNewLoads letFuel loadFuel tbl hits
        (denote (IVal K) (JLabel KL) tf vs ls) =
      checkStoreArmFlat tgt allowNewLoads letFuel loadFuel tbl hits inVD inVE inLD inLE tf := by
  cases tf with
  | let_ op k =>
    obtain ⟨ha, hk⟩ := wf_let hwf
    dsimp only [denote]; rw [denoteArgs_eq_some_resolveEnvArgs hΓ hmV op.args ha]
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
          (CtxTypes.push _ hΓ) hΔ (trieCtxMatch_insertTupEnv hmV _) hmL hk]
  | load t a k =>
    obtain ⟨ha, hk⟩ := wf_load hwf
    dsimp only [denote]; rw [denoteArg_eq_some_resolveEnvArg hΓ hmV a ha]
    unfold checkStoreArm checkStoreArmFlat; dsimp only
    cases findSymLoad tbl.loads t (ikey (resolveEnvArg inVD inVE a)) with
    | some _ =>
      dsimp only
      rw [checkStoreArmFlat_eq tgt allowNewLoads k letFuel loadFuel tbl _
        (.cons hΓ) hΔ (hmV.cons t _) hmL hk]
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
            (.cons hΓ) hΔ (hmV.cons t _) hmL hk]
  | store v a tail =>
    obtain ⟨hv, ha, hk⟩ := wf_store hwf
    dsimp only [denote]
    rw [denoteArg_eq_some_resolveEnvArg hΓ hmV v hv, denoteArg_eq_some_resolveEnvArg hΓ hmV a ha]
    unfold checkStoreArm checkStoreArmFlat; dsimp only
    rw [checkStoreTailFlat_eq tgt tail letFuel hΓ hΔ hmL hk]
  | _ => env_denote_close hΓ hΔ hmV hwf rfl

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
      rw [checkStoreArmFlat_eq tgt false e 12 0 tbl1 [] hΓ hΔ hmV hmL he]; rfl

private theorem checkDiamondFlat_eq (bitsOnly : Bool) (jId : Nat) (jTs : List Ty) {rs : List Ty}
    (tf : TFlat rs) (outVD : Nat) {Γ : List Ty} {Δ : List (List Ty)}
    {vs : List ((t : Ty) × IVal K t)} {ls : List ((ts : List Ty) × JLabel KL ts)}
    {inVD inLD : Nat}
    {inVE : Trie ((t : Ty) × IVal K t)} {inLE : Trie ((ts : List Ty) × JLabel KL ts)}
    (hΓ : CtxTypes Γ vs) (hΔ : CtxTypes Δ ls)
    (hmV : TrieCtxMatch inVD inVE vs) (hmL : TrieCtxMatch inLD inLE ls)
    (hwf : tf.wfCheck Γ Δ = true) :
    checkDiamondWith bitsOnly jId jTs outVD (denote (IVal K) (JLabel KL) tf vs ls) =
      checkDiamondFlat bitsOnly jId jTs inVD inVE inLD inLE outVD tf := by
  cases tf with
  | let_ op k =>
    obtain ⟨ha, hk⟩ := wf_let hwf; obtain ⟨_, ha'⟩ := ival_args hΓ ha
    dsimp only [denote]; rw [ha']; dsimp only [checkDiamondWith, checkDiamondFlat]
    rw [checkDiamondFlat_eq bitsOnly jId jTs k (outVD + _)
      (CtxTypes.push _ hΓ) hΔ (trieCtxMatch_insertTupEnv hmV _) hmL hk]
  | load t a k =>
    obtain ⟨ha, hk⟩ := wf_load hwf; obtain ⟨_, ha'⟩ := ival_arg hΓ ha
    dsimp only [denote]; rw [ha']; dsimp only [checkDiamondWith, checkDiamondFlat]
    rw [checkDiamondFlat_eq bitsOnly jId jTs k (outVD + 1) (.cons hΓ) hΔ (hmV.cons t _) hmL hk]
  | store v a k =>
    obtain ⟨hv, ha, hk⟩ := wf_store hwf
    obtain ⟨_, hv'⟩ := ival_arg hΓ hv; obtain ⟨_, ha'⟩ := ival_arg hΓ ha
    dsimp only [denote]; rw [hv', ha']; dsimp only [checkDiamondWith, checkDiamondFlat]
    rw [checkDiamondFlat_eq bitsOnly jId jTs k outVD hΓ hΔ hmV hmL hk]
  | call _ bs args k =>
    obtain ⟨ha, hk⟩ := wf_call hwf; obtain ⟨_, ha'⟩ := ival_args hΓ ha
    dsimp only [denote]; rw [ha']; dsimp only [checkDiamondWith, checkDiamondFlat]
    rw [checkDiamondFlat_eq bitsOnly jId jTs k (outVD + bs.length)
      (CtxTypes.push _ hΓ) hΔ (trieCtxMatch_insertTupEnv hmV _) hmL hk]
  | jnz c t e =>
    obtain ⟨hc, ht, he⟩ := wf_jnz hwf; obtain ⟨_, hc'⟩ := ival_arg hΓ hc
    dsimp only [denote]; rw [hc']; dsimp only [checkDiamondWith, checkDiamondFlat]
    cases isSelectSigWith bitsOnly jTs with
    | false => simp only [Bool.false_eq_true, ↓reduceIte]
    | true =>
      simp only [↓reduceIte]
      rw [checkArmFlat_eq (.loc jId jTs) t 2 4 outVD hΓ hΔ hmL ht,
        checkArmFlat_eq (.loc jId jTs) e 2 4 outVD hΓ hΔ hmL he,
        checkStoreArmsFlat_eq bitsOnly (.loc jId jTs) t e hΓ hΔ hmV hmL ht he]; rfl
  | _ => ival_denote_close hΓ hΔ hwf rfl

private theorem mkPairIValArgFlat_eq {rs : List Ty} {a b : Ty}
    (outVD outLD : Nat) (x : Arg (IVal K) a) (y : Arg (IVal K) b)
    {cont_p : Nat → Arg (IVal K) (.pair a b) → Expr K KL rs}
    {cont_f : Nat → Arg (IVal K) (.pair a b) → TFlat rs}
    (hcont : ∀ od p, toTFlat (cont_p od p) od outLD = cont_f od p) :
    toTFlat (mkPairIValArg outVD x y cont_p) outVD outLD =
      mkPairIValArgFlat outVD x y cont_f := by
  dsimp only [mkPairIValArg, mkPairIValArgFlat]
  cases hx : iout x <;> cases hy : iout y <;>
    first
    | exact hcont outVD _
    | (dsimp only [toTFlat, op2, idxArgs, idxArg]
       exact congrArg (TFlat.let_ _) (hcont (outVD + 1) _))

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
  | var _ =>
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
      refine splitPairIValFlat_eq outVD outLD aT fun _ aT₁ aT₂ =>
        splitPairIValFlat_eq _ outLD aE fun _ aE₁ aE₂ =>
        emitSelectTyIValFlat_eq c a _ outLD aT₁ aE₁ fun _ r₁ =>
        emitSelectTyIValFlat_eq c b _ outLD aT₂ aE₂ fun _ r₂ =>
        mkPairIValArgFlat_eq _ outLD r₁ r₂ hcont

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
    refine emitSelectTyIValFlat_eq c t outVD outLD aT aE fun _ r =>
      emitSelectTupIValFlat_eq c ts _ outLD asT asE fun od'' rs' => hcont od'' (r, rs')

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

local macro "hoist_leaf" hwf:ident "," hΓ:ident "," hΔ:ident "," hmV:ident ","
    plan:Lean.Parser.Tactic.elimTarget "," jTs:ident "," outVD:ident "," hcont:ident ","
    f₁:Lean.Parser.Tactic.simpLemma "," f₂:Lean.Parser.Tactic.simpLemma : tactic => `(tactic| (
  (first
    | (obtain ⟨hj, ha⟩ := wf_jump $hwf
       obtain ⟨_, hj'⟩ := Option.isSome_iff_exists.1 (lookupL_isSome_of_check $hΔ hj)
       dsimp only [denote]; rw [hj', denoteArgs_eq_some_resolveEnvArgs $hΓ $hmV _ ha])
    | (dsimp only [denote]; rw [denoteArgs_eq_some_resolveEnvArgs $hΓ $hmV _ $hwf]))
  cases $plan <;> try rfl
  dsimp only [$f₁, $f₂]
  cases listTyDecEq _ $jTs with | isFalse _ => rfl | isTrue _ => exact $hcont $outVD _))

private theorem hoistArmFlat_eq {rs : List Ty} (jTs : List Ty)
    (tf : TFlat rs) (plan : ArmPlan)
    {Γ : List Ty} {Δ : List (List Ty)}
    {vs : List ((t : Ty) × IVal K t)} {ls : List ((ts : List Ty) × JLabel KL ts)}
    {inVD outVD outLD : Nat} {inVE : Trie ((t : Ty) × IVal K t)}
    {cont_p : Nat → Tup (Arg (IVal K)) jTs → Expr K KL rs}
    {cont_f : Nat → Tup (Arg (IVal K)) jTs → TFlat rs}
    (hΓ : CtxTypes Γ vs) (hΔ : CtxTypes Δ ls) (hmV : TrieCtxMatch inVD inVE vs)
    (hwf : tf.wfCheck Γ Δ = true)
    (hcont : ∀ od args, toTFlat (cont_p od args) od outLD = cont_f od args) :
    toTFlat (hoistArm jTs plan outVD (denote (IVal K) (JLabel KL) tf vs ls) cont_p)
      outVD outLD = hoistArmFlat jTs plan tf inVD inVE outVD cont_f := by
  cases tf with
  | jump _ _ => hoist_leaf hwf, hΓ, hΔ, hmV, plan, jTs, outVD, hcont, hoistArm, hoistArmFlat
  | ret _ => hoist_leaf hwf, hΓ, hΔ, hmV, plan, jTs, outVD, hcont, hoistArm, hoistArmFlat
  | let_ op k =>
    obtain ⟨ha, hk⟩ := wf_let hwf
    dsimp only [denote]; rw [denoteArgs_eq_some_resolveEnvArgs hΓ hmV op.args ha]
    cases plan with
    | let_ rest =>
      dsimp only [hoistArm, hoistArmFlat, toTFlat]
      exact congrArg (TFlat.let_ _) (hoistArmFlat_eq jTs k rest (CtxTypes.push _ hΓ) hΔ
        (trieCtxMatch_insertTupEnv hmV _) hk hcont)
    | _ => rfl
  | jnz c t e =>
    obtain ⟨hc, ht, he⟩ := wf_jnz hwf
    dsimp only [denote]; rw [denoteArg_eq_some_resolveEnvArg hΓ hmV c hc]
    cases plan with
    | jnz pT pE =>
      dsimp only [hoistArm, hoistArmFlat]
      refine hoistArmFlat_eq jTs t pT hΓ hΔ hmV ht fun _ argsT =>
        hoistArmFlat_eq jTs e pE hΓ hΔ hmV he fun od₂ argsE =>
        emitSelectTupIValFlat_eq _ jTs od₂ outLD argsT argsE hcont
    | _ => rfl
  | _ => env_denote_close hΓ hΔ hmV hwf (cases plan <;> rfl)

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
  refine hoistArmFlat_eq jTs t pT hΓ hΔ hmV ht fun _ argsT =>
    hoistArmFlat_eq jTs e pE hΓ hΔ hmV he fun od₂ argsE =>
    emitSelectTupFlat_eq (iout c) jTs od₂ outLD argsT argsE hfin

private theorem hoistStoreTailFlat_eq {rs : List Ty} (jTs : List Ty)
    (tf : TFlat rs) (tail : StoreTail)
    {Γ : List Ty} {Δ : List (List Ty)}
    {vs : List ((t : Ty) × IVal K t)} {ls : List ((ts : List Ty) × JLabel KL ts)}
    {inVD outVD outLD : Nat} {inVE : Trie ((t : Ty) × IVal K t)}
    {cont_p : Nat → Tup (Arg (IVal K)) jTs → Expr K KL rs}
    {cont_f : Nat → Tup (Arg (IVal K)) jTs → TFlat rs}
    (hΓ : CtxTypes Γ vs) (hΔ : CtxTypes Δ ls) (hmV : TrieCtxMatch inVD inVE vs)
    (hwf : tf.wfCheck Γ Δ = true)
    (hcont : ∀ od args, toTFlat (cont_p od args) od outLD = cont_f od args) :
    toTFlat (hoistStoreTail jTs tail outVD (denote (IVal K) (JLabel KL) tf vs ls) cont_p)
      outVD outLD = hoistStoreTailFlat jTs tail tf inVD inVE outVD cont_f := by
  cases tf with
  | jump _ _ =>
    hoist_leaf hwf, hΓ, hΔ, hmV, tail, jTs, outVD, hcont, hoistStoreTail, hoistStoreTailFlat
  | ret _ =>
    hoist_leaf hwf, hΓ, hΔ, hmV, tail, jTs, outVD, hcont, hoistStoreTail, hoistStoreTailFlat
  | let_ op k =>
    obtain ⟨ha, hk⟩ := wf_let hwf
    dsimp only [denote]; rw [denoteArgs_eq_some_resolveEnvArgs hΓ hmV op.args ha]
    cases tail with
    | let_ rest =>
      dsimp only [hoistStoreTail, hoistStoreTailFlat, toTFlat]
      exact congrArg (TFlat.let_ _) (hoistStoreTailFlat_eq jTs k rest (CtxTypes.push _ hΓ) hΔ
        (trieCtxMatch_insertTupEnv hmV _) hk hcont)
    | _ => rfl
  | _ => env_denote_close hΓ hΔ hmV hwf (cases tail <;> rfl)

private theorem hoistStoreStepFlat_eq {rs : List Ty} (jTs : List Ty) (st : Ty)
    (tf : TFlat rs) (step : StoreStep) (loads : List ((t : Ty) × IVal K t))
    {Γ : List Ty} {Δ : List (List Ty)}
    {vs : List ((t : Ty) × IVal K t)} {ls : List ((ts : List Ty) × JLabel KL ts)}
    {inVD outVD outLD : Nat} {inVE : Trie ((t : Ty) × IVal K t)}
    {cont_p : Nat → List ((t : Ty) × IVal K t) → Arg (IVal K) st → Arg (IVal K) i64 →
      Tup (Arg (IVal K)) jTs → Expr K KL rs}
    {cont_f : Nat → List ((t : Ty) × IVal K t) → Arg (IVal K) st → Arg (IVal K) i64 →
      Tup (Arg (IVal K)) jTs → TFlat rs}
    (hΓ : CtxTypes Γ vs) (hΔ : CtxTypes Δ ls) (hmV : TrieCtxMatch inVD inVE vs)
    (hwf : tf.wfCheck Γ Δ = true)
    (hcont : ∀ od lds v a args,
      toTFlat (cont_p od lds v a args) od outLD = cont_f od lds v a args) :
    toTFlat (hoistStoreStep jTs st step outVD loads (denote (IVal K) (JLabel KL) tf vs ls) cont_p)
      outVD outLD = hoistStoreStepFlat jTs st step tf inVD inVE outVD loads cont_f := by
  cases tf with
  | let_ op k =>
    obtain ⟨ha, hk⟩ := wf_let hwf
    dsimp only [denote]; rw [denoteArgs_eq_some_resolveEnvArgs hΓ hmV op.args ha]
    cases step with
    | let_ rest =>
      dsimp only [hoistStoreStep, hoistStoreStepFlat, toTFlat]
      exact congrArg (TFlat.let_ _) (hoistStoreStepFlat_eq jTs st k rest loads
        (CtxTypes.push _ hΓ) hΔ (trieCtxMatch_insertTupEnv hmV _) hk hcont)
    | _ => rfl
  | load t a k =>
    obtain ⟨ha, hk⟩ := wf_load hwf
    dsimp only [denote]; rw [denoteArg_eq_some_resolveEnvArg hΓ hmV a ha]
    cases step with
    | loadEmit rest =>
      dsimp only [hoistStoreStep, hoistStoreStepFlat, toTFlat]
      exact congrArg (TFlat.load t _)
        (hoistStoreStepFlat_eq jTs st k rest _ (.cons hΓ) hΔ (hmV.cons t _) hk hcont)
    | loadReuse slot rest =>
      dsimp only [hoistStoreStep, hoistStoreStepFlat]
      rcases loads[slot]? with _ | ⟨t', _⟩
      · rfl
      · dsimp only
        cases tyDecEq t' t with
        | isFalse _ => rfl
        | isTrue _ =>
          exact hoistStoreStepFlat_eq jTs st k rest loads (.cons hΓ) hΔ (hmV.cons t _) hk hcont
    | _ => rfl
  | store v a k =>
    obtain ⟨hv, ha, hk⟩ := wf_store hwf; dsimp only [denote]
    rw [denoteArg_eq_some_resolveEnvArg hΓ hmV v hv, denoteArg_eq_some_resolveEnvArg hΓ hmV a ha]
    cases step with
    | store tail =>
      dsimp only [hoistStoreStep, hoistStoreStepFlat]
      cases tyDecEq _ st with
      | isFalse _ => rfl
      | isTrue _ =>
        exact hoistStoreTailFlat_eq jTs k tail hΓ hΔ hmV hk fun od' exitArgs =>
          hcont od' loads _ _ exitArgs
    | _ => rfl
  | _ => env_denote_close hΓ hΔ hmV hwf (cases step <;> rfl)

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
  refine hoistStoreStepFlat_eq jTs sp.storeTy t sp.armT [] hΓ hΔ hmV ht fun _ _ vT _ argsT =>
    hoistStoreStepFlat_eq jTs sp.storeTy e sp.armE _ hΓ hΔ hmV he fun _ _ vE _ argsE =>
    emitSelectTyFlat_eq (iout c) sp.storeTy _ outLD vT vE fun _ _ => by
    dsimp only [toTFlat]
    exact congrArg (TFlat.store _ _) (emitSelectTupFlat_eq (iout c) jTs _ outLD argsT argsE hfin)

local macro "hd_step" plan:Lean.Parser.Tactic.elimTarget "," ctor:ident "," rest:ident ","
    pre:tacticSeq "," body:tacticSeq : tactic => `(tactic| (
  ($pre); cases $plan with
  | $ctor $rest => dsimp only [hoistDiamond, hoistDiamondFlat, toTFlat]; ($body)
  | _ => rfl))

private theorem hoistDiamondFlat_eq {rs : List Ty} {jTs : List Ty} (jLbl : KL jTs)
    (tf : TFlat rs) (plan : DiamondPlan)
    {Γ : List Ty} {Δ : List (List Ty)}
    {vs : List ((t : Ty) × IVal K t)} {ls : List ((ts : List Ty) × JLabel KL ts)}
    {inVD outVD outLD : Nat} {inVE : Trie ((t : Ty) × IVal K t)}
    (hΓ : CtxTypes Γ vs) (hΔ : CtxTypes Δ ls) (hmV : TrieCtxMatch inVD inVE vs)
    (hwf : tf.wfCheck Γ Δ = true) :
    toTFlat (hoistDiamond jLbl plan outVD (denote (IVal K) (JLabel KL) tf vs ls)) outVD outLD =
      hoistDiamondFlat jLbl plan tf inVD inVE outVD outLD := by
  cases tf with
  | jnz c t e =>
    obtain ⟨hc, ht, he⟩ := wf_jnz hwf
    dsimp only [denote]; rw [denoteArg_eq_some_resolveEnvArg hΓ hmV c hc]
    cases plan with
    | jnz pT pE =>
      dsimp only [hoistDiamond, hoistDiamondFlat]
      exact hoistJnzArmsFlat_eq jTs pT pE _ t e hΓ hΔ hmV ht he fun _ _ => rfl
    | jnzStore sp =>
      dsimp only [hoistDiamond, hoistDiamondFlat]
      exact hoistStoreArmsFlat_eq jTs sp _ t e hΓ hΔ hmV ht he fun _ _ => rfl
    | _ => rfl
  | let_ op k =>
    hd_step plan, let_, rest,
      (obtain ⟨ha, hk⟩ := wf_let hwf
       dsimp only [denote]; rw [denoteArgs_eq_some_resolveEnvArgs hΓ hmV op.args ha]),
      exact congrArg (TFlat.let_ _) (hoistDiamondFlat_eq jLbl k rest (CtxTypes.push _ hΓ) hΔ
        (trieCtxMatch_insertTupEnv hmV _) hk)
  | load t a k =>
    hd_step plan, load, rest,
      (obtain ⟨ha, hk⟩ := wf_load hwf
       dsimp only [denote]; rw [denoteArg_eq_some_resolveEnvArg hΓ hmV a ha]),
      exact congrArg (TFlat.load t _)
        (hoistDiamondFlat_eq jLbl k rest (.cons hΓ) hΔ (hmV.cons t _) hk)
  | store v a k =>
    hd_step plan, store, rest,
      (obtain ⟨hv, ha, hk⟩ := wf_store hwf; dsimp only [denote]
       rw [denoteArg_eq_some_resolveEnvArg hΓ hmV v hv,
         denoteArg_eq_some_resolveEnvArg hΓ hmV a ha]),
      exact congrArg (TFlat.store _ _) (hoistDiamondFlat_eq jLbl k rest hΓ hΔ hmV hk)
  | call f bs args k =>
    hd_step plan, call, rest,
      (obtain ⟨ha, hk⟩ := wf_call hwf
       dsimp only [denote]; rw [denoteArgs_eq_some_resolveEnvArgs hΓ hmV args ha]),
      exact congrArg (TFlat.call f bs _) (hoistDiamondFlat_eq jLbl k rest (CtxTypes.push _ hΓ) hΔ
        (trieCtxMatch_insertTupEnv hmV _) hk)
  | _ => env_denote_close hΓ hΔ hmV hwf (cases plan <;> rfl)

local macro "pure_arm" tgt:term "," sig:term "," t:ident "," e:ident "," c:ident ","
    hΓ:ident "," hΔ:ident "," hmV:ident "," hmL:ident ","
    ht:ident "," he:ident : tactic => `(tactic| (
  cases isSelectSigWith _ $sig <;> simp only [Bool.false_eq_true, ↓reduceIte, Option.map_none]
  rw [checkArmFlat_eq $tgt $t 2 4 _ $hΓ $hΔ $hmL $ht,
    checkArmFlat_eq $tgt $e 2 4 _ $hΓ $hΔ $hmL $he]
  cases checkArmFlat $tgt 2 4 _ _ $t with
  | none => rfl
  | some resT =>
    cases checkArmFlat $tgt 2 4 _ _ $e with
    | none => rfl
    | some resE =>
      exact congrArg some
        (hoistJnzArmsFlat_eq $sig resT.1 resE.1 $c $t $e
          $hΓ $hΔ $hmV $ht $he fun _ _ => rfl)))

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
  | none => dsimp only; pure_arm .ret, rs, t, e, c, hΓ, hΔ, hmV, hmL, ht, he
  | some tgt =>
    rcases tgt with ⟨jTs, jId, _⟩; dsimp only
    pure_arm (.tag jId jTs), jTs, t, e, c, hΓ, hΔ, hmV, hmL, ht, he

local macro "store_arm" tgt:term "," sig:term "," t:ident "," e:ident "," c:ident ","
    bitsOnly:ident "," hΓ:ident "," hΔ:ident "," hmV:ident "," hmL:ident ","
    ht:ident "," he:ident : tactic => `(tactic| (
  cases isSelectSigWith $bitsOnly $sig <;>
    simp only [Bool.false_eq_true, ↓reduceIte, Option.map_none]
  rw [checkStoreArmsFlat_eq $bitsOnly $tgt $t $e $hΓ $hΔ $hmV $hmL $ht $he]
  cases checkStoreArmsFlat $bitsOnly $tgt _ _ _ _ _ $t $e with
  | none => rfl
  | some sp =>
    exact congrArg some
      (hoistStoreArmsFlat_eq $sig sp $c $t $e $hΓ $hΔ $hmV $ht $he fun _ _ => rfl)))

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
  | none => dsimp only; store_arm .ret, rs, t, e, c, bitsOnly, hΓ, hΔ, hmV, hmL, ht, he
  | some tgt =>
    rcases tgt with ⟨jTs, jId, _⟩; dsimp only
    store_arm (.tag jId jTs), jTs, t, e, c, bitsOnly, hΓ, hΔ, hmV, hmL, ht, he

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
  | some ex => rw [hopt, Option.map_some] at hp; rw [← hp]; rfl
  | none =>
    rw [hopt, Option.map_none] at hp; rw [← hp]
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
  dsimp only [denote]; rw [ifOptWith.eq_def, ifOptWithFlat.eq_def]
  simp only [↓reduceIte, toTFlat]; rw [hb, hk]

private theorem ifOptWithFlat_both (bitsOnly : Bool) {rs : List Ty} :
    (∀ (tf : TFlat rs) {Γ Δ vs ls inVD outVD inLD outLD inVE inLE} (depth : Nat),
      CtxTypes Γ vs → CtxTypes Δ ls →
      TrieCtxMatch inVD inVE vs → TrieCtxMatch inLD inLE ls → tf.wfCheck Γ Δ = true →
      toTFlat (ifOptWith bitsOnly depth outVD (denote (IVal K) (JLabel KL) tf vs ls))
          outVD outLD =
        ifOptWithFlat bitsOnly depth tf inVD inVE inLD inLE outVD outLD) ∧
    (∀ {sig : List (List Ty)} (tb : TBlocks rs sig)
      {Γ Δ vs ls inVD outVD inLD outLD inVE inLE} (depth : Nat),
      CtxTypes Γ vs → CtxTypes Δ ls →
      TrieCtxMatch inVD inVE vs → TrieCtxMatch inLD inLE ls → tb.wfCheck Γ Δ = true →
      toTBlocks (ifOptBWith bitsOnly depth outVD (denoteB (IVal K) (JLabel KL) tb vs ls))
          outVD outLD =
        ifOptBWithFlat bitsOnly depth tb inVD inVE inLD inLE outVD outLD) := by
  refine relSim_mutual ⟨
    fun depth op k hΓ _ hmV hmL hwf ih => by
      obtain ⟨ha, hk⟩ := wf_let hwf
      dsimp only [denote]; rw [denoteArgs_eq_some_resolveEnvArgs hΓ hmV op.args ha]
      dsimp only [ifOptWith, ifOptWithFlat, toTFlat]
      exact congrArg (TFlat.let_ _)
        (ih depth (ctxTypes_pushTup_rev _ hΓ) (trieCtxMatch_insertTupEnv hmV _) hmL hk),
    fun depth t a k hΓ _ hmV hmL hwf ih => by
      obtain ⟨ha, hk⟩ := wf_load hwf
      dsimp only [denote]; rw [denoteArg_eq_some_resolveEnvArg hΓ hmV a ha]
      dsimp only [ifOptWith, ifOptWithFlat, toTFlat]
      exact congrArg (TFlat.load t _) (ih depth (.cons hΓ) (trieCtxMatch_singleton hmV t _) hmL hk),
    fun depth v a k hΓ _ hmV hmL hwf ih => by
      obtain ⟨hv, ha, hk⟩ := wf_store hwf; dsimp only [denote]
      rw [denoteArg_eq_some_resolveEnvArg hΓ hmV v hv, denoteArg_eq_some_resolveEnvArg hΓ hmV a ha]
      dsimp only [ifOptWith, ifOptWithFlat, toTFlat]
      exact congrArg (TFlat.store _ _) (ih depth hΓ hmV hmL hk),
    fun depth f bs args k hΓ _ hmV hmL hwf ih => by
      obtain ⟨ha, hk⟩ := wf_call hwf
      dsimp only [denote]; rw [denoteArgs_eq_some_resolveEnvArgs hΓ hmV args ha]
      dsimp only [ifOptWith, ifOptWithFlat, toTFlat]
      exact congrArg (TFlat.call f bs _)
        (ih depth (ctxTypes_pushTup_rev _ hΓ) (trieCtxMatch_insertTupEnv hmV _) hmL hk),
    @fun _ _ _ _ inVD outVD inLD outLD inVE inLE depth c t e hΓ hΔ hmV hmL hwf iht ihe => by
      obtain ⟨hc, ht, he⟩ := wf_jnz hwf
      dsimp only [denote]; rw [denoteArg_eq_some_resolveEnvArg hΓ hmV c hc]
      have ht' := iht depth ht; have he' := ihe depth he
      dsimp only [ifOptWith, ifOptWithFlat]
      cases bitsOnly with
      | false => simp only [Bool.false_eq_true, ↓reduceIte, toTFlat]; rw [ht', he']
      | true =>
        have htry := tryJnzDiamondFlat_eq true (resolveEnvArg inVD inVE c) t e hΓ hΔ hmV hmL
          ht he (outVD := outVD) (outLD := outLD)
        simp only [↓reduceIte]
        cases hopt : tryJnzDiamond true outVD (resolveEnvArg inVD inVE c)
            (denote (IVal K) (JLabel KL) t _ _) (denote (IVal K) (JLabel KL) e _ _) with
        | none =>
          rw [hopt, Option.map_none] at htry; rw [← htry]
          dsimp only [Option.getD, toTFlat]; rw [ht', he']
        | some _ => rw [hopt, Option.map_some] at htry; rw [← htry]; rfl,
    fun _ j args hΓ hΔ hmV hmL hwf => by
      obtain ⟨hj, ha⟩ := wf_jump hwf
      obtain ⟨jl, hlk, hres⟩ := lookupL_eq_some_resolveLabel hΔ hmL hj
      dsimp only [denote]; rw [hlk, denoteArgs_eq_some_resolveEnvArgs hΓ hmV args ha]
      dsimp only [ifOptWith, ifOptWithFlat]; rw [hres]; dsimp only
      cases unwrapJLabel jl <;> rfl,
    fun _ vs' hΓ _ hmV _ hwf => by
      dsimp only [denote]; rw [denoteArgs_eq_some_resolveEnvArgs hΓ hmV vs' hwf]; rfl,
    fun _ f args hΓ _ hmV _ hwf => by
      dsimp only [denote]; rw [denoteArgs_eq_some_resolveEnvArgs hΓ hmV args hwf]; rfl,
    fun _ _ _ _ _ _ => rfl,
    @fun sig _ Δ _ ls inVD outVD inLD outLD inVE inLE depth bodies k hΓ hΔ hmV hmL hwf ihB ihK => by
      obtain ⟨hb, hk⟩ := wf_group hwf
      cases bitsOnly with
      | true =>
        let tagged := tagLabels depth (Tup.levels sig outLD)
        exact ifOptGroupBitsTrue bodies k depth
          (ihB (depth + sig.length) (ctxTypes_pushTup_rev _ hΔ)
            (trieCtxMatch_insertTupEnv hmL tagged) hb)
          (ihK (depth + sig.length) (ctxTypes_pushTup_rev _ hΔ)
            (trieCtxMatch_insertTupEnv hmL tagged) hk)
      | false =>
        cases sig with
        | nil =>
          simp only [denote, ifOptWith, ifOptWithFlat, Bool.false_eq_true, ↓reduceIte, toTFlat,
            List.length_nil, Nat.add_zero]
          dsimp only [Tup.levels, Tup.map, pushTup]
          rw [ihB depth hΔ hmL hb, ihK depth hΔ hmL hk]
        | cons ts rest =>
          cases rest with
          | nil =>
            simp only [denote, ifOptWith, ifOptWithFlat, Bool.false_eq_true, ↓reduceIte, toTFlat,
              List.length_cons, List.length_nil, Nat.zero_add]
            dsimp only [Tup.levels, Tup.map, pushTup]
            rw [checkDiamondFlat_eq false depth ts k outVD
              hΓ (.cons hΔ) hmV (trieCtxMatch_singleton hmL ts (.loc depth)) hk,
              ihB (outLD' := outLD + 1) (depth + 1) (CtxTypes.cons hΔ)
                (trieCtxMatch_singleton hmL ts (.outer outLD)) hb]
            cases checkDiamondFlat false depth ts inVD inVE (inLD + 1)
                (inLE.insert inLD ⟨ts, .loc depth⟩) outVD k with
            | none =>
              rw [ihK (depth + 1) (CtxTypes.cons hΔ)
                (trieCtxMatch_singleton hmL ts (.outer outLD)) hk]
            | some plan =>
              rw [hoistDiamondFlat_eq (jTs := ts) outLD k plan hΓ (.cons hΔ) hmV hk
                (ls := ⟨ts, .outer outLD⟩ :: ls) (outVD := outVD) (outLD := outLD + 1)]
          | cons ts₂ rest' =>
            simp only [denote, ifOptWith, ifOptWithFlat, Bool.false_eq_true, ↓reduceIte, toTFlat]
            let outer := (Tup.levels (ts :: ts₂ :: rest') outLD).map fun _ l => JLabel.outer l
            have hΔ' := ctxTypes_pushTup_rev outer hΔ
            have hm' := trieCtxMatch_insertTupEnv hmL outer
            rw [ihB (outLD' := outLD + (ts :: ts₂ :: rest').length)
                  (depth + rest'.length + 2) hΔ' hm' hb,
              ihK (outLD' := outLD + (ts :: ts₂ :: rest').length)
                (depth + rest'.length + 2) hΔ' hm' hk],
    fun _ _ _ _ _ _ => rfl,
    fun depth b bs hΓ _ hmV hmL hwf ihb ihbs => by
      obtain ⟨hb, hbs⟩ := wf_cons hwf
      dsimp only [denoteB, ifOptBWith, ifOptBWithFlat, toTBlocks]
      rw [ihb depth (ctxTypes_pushTup_rev _ hΓ) (trieCtxMatch_insertTupEnv hmV _) hmL hb,
        ihbs depth hbs]⟩

public section

theorem ifOptFlat_eq (bitsOnly : Bool) {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    ifOptFlat bitsOnly as tf =
      reifyFunc (Func.ifOptWith bitsOnly (denoteFunc (as := as) tf)) := by
  have hm := trieCtxMatch_initEnv (W := IVal K) (fun x next => (.var x, .var next)) as
  have h := (ifOptWithFlat_both bitsOnly).1 tf 0 (CtxTypes.push _ .nil) .nil hm
    TrieCtxMatch.empty hwf (outVD := as.length) (outLD := 0)
  dsimp only [ifOptFlat, Func.ifOptWith, reifyFunc, denoteFunc] at h ⊢
  exact h.symm

theorem ifOptFlat_false_eq {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    ifOptFlat false as tf = reifyFunc (Func.ifOpt (denoteFunc (as := as) tf)) :=
  ifOptFlat_eq false tf hwf

theorem ifOptFlat_true_eq {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    ifOptFlat true as tf = reifyFunc (Func.ifOptBits (denoteFunc (as := as) tf)) :=
  ifOptFlat_eq true tf hwf

theorem denoteFunc_ifOptFlat (bitsOnly : Bool) {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    denoteFunc (as := as) (ifOptFlat bitsOnly as tf) =
      Func.ifOptWith bitsOnly (denoteFunc (as := as) tf) :=
  denoteFunc_of_flat_eq (Func.ifOptWith_wf bitsOnly) tf hwf (ifOptFlat_eq bitsOnly tf hwf)

theorem denoteFunc_ifOptFlat_false {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    denoteFunc (as := as) (ifOptFlat false as tf) = Func.ifOpt (denoteFunc (as := as) tf) :=
  denoteFunc_ifOptFlat false tf hwf

theorem denoteFunc_ifOptFlat_true {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    denoteFunc (as := as) (ifOptFlat true as tf) = Func.ifOptBits (denoteFunc (as := as) tf) :=
  denoteFunc_ifOptFlat true tf hwf

theorem ifOptFlat_wfCheck (bitsOnly : Bool) {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    (ifOptFlat bitsOnly as tf).wfCheck (pushTypes as []) [] = true :=
  wfCheck_of_flat_eq (Func.ifOptWith_wf bitsOnly) tf hwf (ifOptFlat_eq bitsOnly tf hwf)

theorem ifOptFlatFn_toFn (bitsOnly : Bool) (f : TFlatFn) (hwf : f.wfCheck = true) :
    (ifOptFlatFn bitsOnly f).toFn =
      ⟨f.name, f.as, f.rs, Func.ifOptWith bitsOnly f.toFn.body⟩ :=
  fn_toFn_of_denoteFunc
    (flatBody := fun as _ tf => ifOptFlat bitsOnly as tf)
    (phoas := fun g => Func.ifOptWith bitsOnly g)
    (fun tf h => denoteFunc_ifOptFlat bitsOnly tf h) f hwf

theorem ifOptFlatFn_wfCheck (bitsOnly : Bool) (f : TFlatFn) (hwf : f.wfCheck = true) :
    (ifOptFlatFn bitsOnly f).wfCheck = true :=
  ifOptFlat_wfCheck bitsOnly f.body hwf

end

end IfOptProofs

end OptFlatCfg
end LeanQbe.T
