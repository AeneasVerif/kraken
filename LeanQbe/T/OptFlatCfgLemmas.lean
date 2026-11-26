module

public import LeanQbe.T.OptFlatCfg
import LeanQbe.T.FlatDirectLemmas
import LeanQbe.T.PassFlatKit
import LeanQbe.T.DceLemmas
import LeanQbe.T.DceParamLemmas
import LeanQbe.T.IfOptLemmas

/-!
# Equivalence Proofs for `OptFlatCfg` (`dcePFlat_eq`, `deadLoadElimFlat_eq`, `ifOptFlat_eq`)

Proves exact `=` correspondence (`std3` axioms only) between every direct `TFlat` CFG/cleanup
pass in `LeanQbe.T.OptFlatCfg` and its PHOAS counterpart (`Func.dce`, `Func.deadLoadElim`,
`Func.dceP`, `Func.ifOpt`, `Func.ifOptBits`), matching `MainFlatLemmas` contracts:

* `OptFlatCfg.dceWithFlat_eq`, `dceFlat_eq`, `deadLoadElimFlat_eq`, `denoteFunc_deadLoadElimFlat`
* `OptFlatCfg.dcePWithFlat_eq`, `dcePFlat_eq`, `denoteFunc_dcePFlat`, `dcePFlatFn_toFn`
* `OptFlatCfg.ifOptFlat_eq`, `ifOptFlat_false_eq`, `ifOptFlat_true_eq`, `denoteFunc_ifOptFlat`
-/

set_option autoImplicit false

public section

namespace LeanQbe.T
namespace OptFlatCfg

open OptFlatPlanKit

private theorem tupFreshWith_some_eq :
    {ts : List Ty} → (xs : Tup K ts) → (n : Nat) →
    tupFreshWith (fun x _ => some x) ts xs n = someTup ts xs
  | [], (), _ => rfl
  | _ :: _, (_, xs), n => by
    dsimp only [tupFreshWith, someTup]
    rw [tupFreshWith_some_eq xs (n + 1)]

/-! ## 1. `dceWithFlat`, `dceFlat`, `deadLoadElimFlat` Simulation Proofs -/

mutual
private theorem liveVarsFlat_eq (dl dld : Bool) {rs : List Ty} :
    (tf : TFlat rs) → {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × K t)} → {ls : List ((ts : List Ty) × KL0 ts)} →
    CtxTypes Γ vs → CtxLevels vs → CtxTypes Δ ls → tf.wfCheck Γ Δ = true →
    liveVarsWith dl dld vs.length (denote K KL0 tf vs ls) = liveVarsFlat dl dld vs.length tf
  | .let_ (ts := ts) op k, Γ, Δ, vs, ls, hΓ, hvl, hΔ, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denote]
    rw [denoteArgs_eq_some_levelArgs hΓ hvl op.args hwf.1]
    dsimp only [liveVarsWith, liveVarsFlat]
    have hk := liveVarsFlat_eq dl dld k (CtxTypes.push _ hΓ) hvl.pushTup hΔ hwf.2
    rw [pushTup_length] at hk
    rw [hk]
  | .load t a k, Γ, Δ, vs, ls, hΓ, hvl, hΔ, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denote]
    rw [denoteArg_eq_some_levelArg hΓ hvl a hwf.1]
    dsimp only [liveVarsWith, liveVarsFlat]
    have hk := liveVarsFlat_eq dl dld k (.cons hΓ) (hvl.cons t) hΔ hwf.2
    rw [List.length_cons] at hk
    rw [hk]
  | .store v a k, Γ, Δ, vs, ls, hΓ, hvl, hΔ, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denote]
    rw [denoteArg_eq_some_levelArg hΓ hvl v hwf.1.1,
      denoteArg_eq_some_levelArg hΓ hvl a hwf.1.2]
    dsimp only [liveVarsWith, liveVarsFlat]
    rw [liveVarsFlat_eq dl dld k hΓ hvl hΔ hwf.2]
  | .call f bs args k, Γ, Δ, vs, ls, hΓ, hvl, hΔ, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denote]
    rw [denoteArgs_eq_some_levelArgs hΓ hvl args hwf.1]
    dsimp only [liveVarsWith, liveVarsFlat]
    have hk := liveVarsFlat_eq dl dld k (CtxTypes.push _ hΓ) hvl.pushTup hΔ hwf.2
    rw [pushTup_length] at hk
    rw [hk]
  | .jnz c t e, Γ, Δ, vs, ls, hΓ, hvl, hΔ, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denote]
    rw [denoteArg_eq_some_levelArg hΓ hvl c hwf.1.1]
    dsimp only [liveVarsWith, liveVarsFlat]
    rw [liveVarsFlat_eq dl dld t hΓ hvl hΔ hwf.1.2,
      liveVarsFlat_eq dl dld e hΓ hvl hΔ hwf.2]
  | .jump (ts := ts) j args, Γ, Δ, vs, ls, hΓ, hvl, hΔ, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨j', hj⟩ := Option.isSome_iff_exists.1 (lookupL_isSome_of_check hΔ hwf.1)
    dsimp only [denote]
    rw [hj, denoteArgs_eq_some_levelArgs hΓ hvl args hwf.2]
    rfl
  | .ret vs', Γ, _, vs, _, hΓ, hvl, _, hwf => by
    dsimp only [denote]
    rw [denoteArgs_eq_some_levelArgs hΓ hvl vs' hwf]
    rfl
  | .exit f args, Γ, _, vs, _, hΓ, hvl, _, hwf => by
    dsimp only [denote]
    rw [denoteArgs_eq_some_levelArgs hΓ hvl args hwf]
    rfl
  | .hlt, _, _, _, _, _, _, _, _ => rfl
  | .group (sig := sig) bodies k, Γ, Δ, vs, ls, hΓ, hvl, hΔ, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denote, liveVarsWith, liveVarsFlat]
    rw [liveVarsBFlat_eq dl dld bodies hΓ hvl (CtxTypes.push _ hΔ) hwf.1,
      liveVarsFlat_eq dl dld k hΓ hvl (CtxTypes.push _ hΔ) hwf.2]

private theorem liveVarsBFlat_eq (dl dld : Bool) {rs : List Ty} :
    {sig : List (List Ty)} → (tb : TBlocks rs sig) → {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × K t)} → {ls : List ((ts : List Ty) × KL0 ts)} →
    CtxTypes Γ vs → CtxLevels vs → CtxTypes Δ ls → tb.wfCheck Γ Δ = true →
    liveVarsBWith dl dld vs.length (denoteB K KL0 tb vs ls) = liveVarsBFlat dl dld vs.length tb
  | _, .nil, _, _, _, _, _, _, _, _ => rfl
  | _, .cons (ts := ts) hd tl, Γ, Δ, vs, ls, hΓ, hvl, hΔ, hwf => by
    dsimp only [TBlocks.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denoteB, liveVarsBWith, liveVarsBFlat]
    have hh := liveVarsFlat_eq dl dld hd (CtxTypes.push _ hΓ) hvl.pushTup hΔ hwf.1
    rw [pushTup_length] at hh
    rw [hh, liveVarsBFlat_eq dl dld tl hΓ hvl hΔ hwf.2]
end

mutual
private theorem dceSweepFlat_eq {rs : List Ty} :
    (tf : TFlat rs) → (kt : KeepTree) → {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × OptV K t)} → {ls : List ((ts : List Ty) × KL ts)} →
    {inVD outVD : Nat} → {inVE : Trie ((t : Ty) × OptV K t)} →
    CtxTypes Γ vs → CtxTypes Δ ls → CtxLevels ls →
    TrieCtxMatch inVD inVE vs → tf.wfCheck Γ Δ = true →
    toTFlat (dceSweep kt (denote (OptV K) KL tf vs ls)) outVD ls.length =
      dceSweepFlat kt tf inVD inVE outVD
  | .let_ (ts := ts) op k, kt, Γ, Δ, vs, ls, inVD, outVD, inVE, hΓ, hΔ, hll, hm, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denote]
    rw [denoteArgs_eq_some_resolveEnvArgs hΓ hm op.args hwf.1]
    cases kt with
    | letNode keep kt' =>
      cases keep with
      | true =>
        dsimp only [dceSweep, dceSweepFlat, toTFlat]
        exact congrArg (TFlat.let_ _)
          (dceSweepFlat_eq k kt' (CtxTypes.push _ hΓ) hΔ hll
            (trieCtxMatch_insertTupEnv hm _) hwf.2)
      | false =>
        dsimp only [dceSweep, dceSweepFlat]
        exact dceSweepFlat_eq k kt' (CtxTypes.push _ hΓ) hΔ hll
          (trieCtxMatch_insertTupEnv hm _) hwf.2
    | leaf | node1 _ | node2 _ _ | groupNode _ _ => rfl
  | .load t a k, kt, Γ, Δ, vs, ls, inVD, outVD, inVE, hΓ, hΔ, hll, hm, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denote]
    rw [denoteArg_eq_some_resolveEnvArg hΓ hm a hwf.1]
    cases kt with
    | letNode keep kt' =>
      cases keep with
      | true =>
        dsimp only [dceSweep, dceSweepFlat, toTFlat]
        exact congrArg (TFlat.load t _)
          (dceSweepFlat_eq k kt' (.cons hΓ) hΔ hll (hm.cons t _) hwf.2)
      | false =>
        dsimp only [dceSweep, dceSweepFlat]
        exact dceSweepFlat_eq k kt' (.cons hΓ) hΔ hll (hm.cons t _) hwf.2
    | leaf | node1 _ | node2 _ _ | groupNode _ _ => rfl
  | .store v a k, kt, Γ, Δ, vs, ls, inVD, outVD, inVE, hΓ, hΔ, hll, hm, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denote]
    rw [denoteArg_eq_some_resolveEnvArg hΓ hm v hwf.1.1,
      denoteArg_eq_some_resolveEnvArg hΓ hm a hwf.1.2]
    cases kt with
    | node1 kt' =>
      dsimp only [dceSweep, dceSweepFlat, toTFlat]
      exact congrArg (TFlat.store _ _) (dceSweepFlat_eq k kt' hΓ hΔ hll hm hwf.2)
    | leaf | letNode _ _ | node2 _ _ | groupNode _ _ => rfl
  | .call f bs args k, kt, Γ, Δ, vs, ls, inVD, outVD, inVE, hΓ, hΔ, hll, hm, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denote]
    rw [denoteArgs_eq_some_resolveEnvArgs hΓ hm args hwf.1]
    cases kt with
    | node1 kt' =>
      dsimp only [dceSweep, dceSweepFlat, toTFlat]
      exact congrArg (TFlat.call f bs _)
        (dceSweepFlat_eq k kt' (CtxTypes.push _ hΓ) hΔ hll
          (trieCtxMatch_insertTupEnv hm _) hwf.2)
    | leaf | letNode _ _ | node2 _ _ | groupNode _ _ => rfl
  | .jnz c t e, kt, Γ, Δ, vs, ls, inVD, outVD, inVE, hΓ, hΔ, hll, hm, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denote]
    rw [denoteArg_eq_some_resolveEnvArg hΓ hm c hwf.1.1]
    cases kt with
    | node2 ktt kte =>
      dsimp only [dceSweep, dceSweepFlat, toTFlat]
      rw [dceSweepFlat_eq t ktt hΓ hΔ hll hm hwf.1.2,
        dceSweepFlat_eq e kte hΓ hΔ hll hm hwf.2]
    | leaf | node1 _ | letNode _ _ | groupNode _ _ => rfl
  | .jump (ts := ts) j args, _, Γ, Δ, vs, ls, inVD, outVD, inVE, hΓ, hΔ, hll, hm, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨lvl, hlk, hidx⟩ := lookupL_jump_eq hΔ hll hwf.1
    dsimp only [denote]
    rw [hlk, denoteArgs_eq_some_resolveEnvArgs hΓ hm args hwf.2]
    dsimp only [dceSweep, dceSweepFlat, toTFlat]
    rw [hidx]
  | .ret vs', _, Γ, _, vs, _, inVD, outVD, inVE, hΓ, _, _, hm, hwf => by
    dsimp only [denote]
    rw [denoteArgs_eq_some_resolveEnvArgs hΓ hm vs' hwf]
    rfl
  | .exit f args, _, Γ, _, vs, _, inVD, outVD, inVE, hΓ, _, _, hm, hwf => by
    dsimp only [denote]
    rw [denoteArgs_eq_some_resolveEnvArgs hΓ hm args hwf]
    rfl
  | .hlt, _, _, _, _, _, _, _, _, _, _, _, _, _ => rfl
  | .group (sig := sig) bodies k, kt, Γ, Δ, vs, ls, inVD, outVD, inVE,
      hΓ, hΔ, hll, hm, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    cases kt with
    | groupNode kbs ktk =>
      dsimp only [denote, dceSweep, dceSweepFlat, toTFlat]
      have hb := dceSweepBFlat_eq bodies kbs hΓ (CtxTypes.push _ hΔ) hll.pushTup hm hwf.1
        (outVD := outVD)
      have hk := dceSweepFlat_eq k ktk hΓ (CtxTypes.push _ hΔ) hll.pushTup hm hwf.2
        (outVD := outVD)
      rw [pushTup_length] at hb hk
      rw [hb, hk]
    | leaf | node1 _ | letNode _ _ | node2 _ _ => rfl

private theorem dceSweepBFlat_eq {rs : List Ty} :
    {sig : List (List Ty)} → (tb : TBlocks rs sig) → (kbs : KeepBlocks) →
    {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × OptV K t)} → {ls : List ((ts : List Ty) × KL ts)} →
    {inVD outVD : Nat} → {inVE : Trie ((t : Ty) × OptV K t)} →
    CtxTypes Γ vs → CtxTypes Δ ls → CtxLevels ls →
    TrieCtxMatch inVD inVE vs → tb.wfCheck Γ Δ = true →
    toTBlocks (dceSweepB kbs (denoteB (OptV K) KL tb vs ls)) outVD ls.length =
      dceSweepBFlat kbs tb inVD inVE outVD
  | _, .nil, _, _, _, _, _, _, _, _, _, _, _, _, _ => rfl
  | _, .cons (ts := ts) b bs, kbs, Γ, Δ, vs, ls, inVD, outVD, inVE,
      hΓ, hΔ, hll, hm, hwf => by
    dsimp only [TBlocks.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    cases kbs with
    | cons kh kt =>
      dsimp only [denoteB, dceSweepB, dceSweepBFlat, toTBlocks]
      rw [dceSweepFlat_eq b kh (CtxTypes.push _ hΓ) hΔ hll
          (trieCtxMatch_insertTupEnv hm _) hwf.1,
        dceSweepBFlat_eq bs kt hΓ hΔ hll hm hwf.2]
    | nil =>
      dsimp only [denoteB, dceSweepB, dceSweepBFlat, toTBlocks]
      exact congrArg (TBlocks.cons .hlt) (dceSweepBFlat_eq bs .nil hΓ hΔ hll hm hwf.2)
end

/-- `dceWithFlat dl dld as tf = reifyFunc (Func.dceWith dl dld (denoteFunc tf))` under
`wfCheck = true`. -/
theorem dceWithFlat_eq (dl dld : Bool) {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    dceWithFlat dl dld as tf = reifyFunc (Func.dceWith dl dld (denoteFunc (as := as) tf)) := by
  have hlen : (pushTup (Tup.levels as 0) []).length = as.length := by
    rw [pushTup_length]; simp
  have hlive := liveVarsFlat_eq dl dld tf (CtxTypes.push (Tup.levels as 0) .nil)
    (CtxLevels.pushTup CtxLevels.nil) .nil hwf
  rw [hlen] at hlive
  have hm := trieCtxMatch_initEnv (fun x _ => some x) as
  have hm' : TrieCtxMatch as.length (initEnv (fun x _ => some x) as)
      (pushTup (someTup as (Tup.levels as 0)) []) := by
    rwa [← tupFreshWith_some_eq (Tup.levels as 0) 0]
  have hsweep := dceSweepFlat_eq tf (liveVarsFlat dl dld as.length tf).2
    (CtxTypes.push _ .nil) .nil CtxLevels.nil hm' hwf (outVD := as.length)
  dsimp only [dceWithFlat, reifyFunc, Func.dceWith, denoteFunc] at hsweep ⊢
  rw [hlive]
  exact hsweep.symm

/-- `denoteFunc (dceWithFlat dl dld as tf) = Func.dceWith dl dld (denoteFunc tf)` under
`wfCheck = true`. -/
theorem denoteFunc_dceWithFlat (dl dld : Bool) {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    denoteFunc (as := as) (dceWithFlat dl dld as tf) =
      Func.dceWith dl dld (denoteFunc (as := as) tf) := by
  rw [dceWithFlat_eq dl dld tf hwf]
  exact Func.renorm_eq_self (Func.dceWith_wf dl dld (Func.wf_of_denote tf rfl))

/-- `dceWithFlat` preserves `wfCheck`. -/
theorem dceWithFlat_wfCheck (dl dld : Bool) {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    (dceWithFlat dl dld as tf).wfCheck (pushTypes as []) [] = true := by
  rw [dceWithFlat_eq dl dld tf hwf]
  exact PassFlatKit.reifyFunc_wfCheck (Func.dceWith_wf dl dld (Func.wf_of_denote tf rfl))

/-- `dceFlat as tf = reifyFunc (Func.dce (denoteFunc tf))` under `wfCheck = true`. -/
theorem dceFlat_eq {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    dceFlat as tf = reifyFunc (Func.dce (denoteFunc (as := as) tf)) :=
  dceWithFlat_eq true false tf hwf

/-- `denoteFunc (dceFlat as tf) = Func.dce (denoteFunc tf)` under `wfCheck = true`. -/
theorem denoteFunc_dceFlat {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    denoteFunc (as := as) (dceFlat as tf) = Func.dce (denoteFunc (as := as) tf) :=
  denoteFunc_dceWithFlat true false tf hwf

/-- `dceFlat` preserves `wfCheck`. -/
theorem dceFlat_wfCheck {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    (dceFlat as tf).wfCheck (pushTypes as []) [] = true :=
  dceWithFlat_wfCheck true false tf hwf

/-- `(dceFlatFn f).toFn = ⟨f.name, f.as, f.rs, Func.dce f.toFn.body⟩` under `wfCheck = true`. -/
theorem dceFlatFn_toFn (f : TFlatFn) (hwf : f.wfCheck = true) :
    (dceFlatFn f).toFn = ⟨f.name, f.as, f.rs, Func.dce f.toFn.body⟩ := by
  dsimp only [dceFlatFn, TFlatFn.toFn]
  rw [denoteFunc_dceFlat f.body hwf]

/-- `dceFlatFn` preserves `TFlatFn.wfCheck`. -/
theorem dceFlatFn_wfCheck (f : TFlatFn) (hwf : f.wfCheck = true) :
    (dceFlatFn f).wfCheck = true :=
  dceFlat_wfCheck f.body hwf

/-- `deadLoadElimFlat as tf = reifyFunc (Func.deadLoadElim (denoteFunc tf))` under
`wfCheck = true`. -/
theorem deadLoadElimFlat_eq {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    deadLoadElimFlat as tf = reifyFunc (Func.deadLoadElim (denoteFunc (as := as) tf)) :=
  dceWithFlat_eq false true tf hwf

/-- `denoteFunc (deadLoadElimFlat as tf) = Func.deadLoadElim (denoteFunc tf)` under
`wfCheck = true`. -/
theorem denoteFunc_deadLoadElimFlat {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    denoteFunc (as := as) (deadLoadElimFlat as tf) =
      Func.deadLoadElim (denoteFunc (as := as) tf) :=
  denoteFunc_dceWithFlat false true tf hwf

/-- `deadLoadElimFlat` preserves `wfCheck`. -/
theorem deadLoadElimFlat_wfCheck {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    (deadLoadElimFlat as tf).wfCheck (pushTypes as []) [] = true :=
  dceWithFlat_wfCheck false true tf hwf

/-- `(deadLoadElimFlatFn f).toFn = ⟨f.name, f.as, f.rs, Func.deadLoadElim f.toFn.body⟩`
under `wfCheck = true`. -/
theorem deadLoadElimFlatFn_toFn (f : TFlatFn) (hwf : f.wfCheck = true) :
    (deadLoadElimFlatFn f).toFn = ⟨f.name, f.as, f.rs, Func.deadLoadElim f.toFn.body⟩ := by
  dsimp only [deadLoadElimFlatFn, TFlatFn.toFn]
  rw [denoteFunc_deadLoadElimFlat f.body hwf]

/-- `deadLoadElimFlatFn` preserves `TFlatFn.wfCheck`. -/
theorem deadLoadElimFlatFn_wfCheck (f : TFlatFn) (hwf : f.wfCheck = true) :
    (deadLoadElimFlatFn f).wfCheck = true :=
  deadLoadElimFlat_wfCheck f.body hwf

/-! ## 2. `dcePWithFlat` and `dcePFlat` Simulation Proofs -/

section DceParamProofs
open DceParam

mutual
private theorem liveVarsPFlat_eq (dl dld : Bool) {rs : List Ty} :
    (g : PTree) → (tf : TFlat rs) → {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × K t)} → {ls : List ((ts : List Ty) × KLM ts)} →
    {inLD : Nat} → {inLE : Trie ((ts : List Ty) × Mask ts)} →
    CtxTypes Γ vs → CtxLevels vs → CtxTypes Δ ls → TrieCtxMatch inLD inLE ls →
    tf.wfCheck Γ Δ = true →
    liveVarsP dl dld g vs.length (denote K KLM tf vs ls) =
      liveVarsPFlat dl dld g vs.length inLD inLE tf
  | g, .let_ (ts := ts) op k, Γ, Δ, vs, ls, inLD, inLE, hΓ, hvl, hΔ, hmL, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denote]
    rw [denoteArgs_eq_some_levelArgs hΓ hvl op.args hwf.1]
    dsimp only [liveVarsP, liveVarsPFlat]
    have hk := liveVarsPFlat_eq dl dld g.sub1 k (CtxTypes.push _ hΓ) hvl.pushTup hΔ hmL hwf.2
    rw [pushTup_length] at hk
    rw [hk]
  | g, .load t a k, Γ, Δ, vs, ls, inLD, inLE, hΓ, hvl, hΔ, hmL, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denote]
    rw [denoteArg_eq_some_levelArg hΓ hvl a hwf.1]
    dsimp only [liveVarsP, liveVarsPFlat]
    have hk := liveVarsPFlat_eq dl dld g.sub1 k (.cons hΓ) (hvl.cons t) hΔ hmL hwf.2
    rw [List.length_cons] at hk
    rw [hk]
  | g, .store v a k, Γ, Δ, vs, ls, inLD, inLE, hΓ, hvl, hΔ, hmL, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denote]
    rw [denoteArg_eq_some_levelArg hΓ hvl v hwf.1.1,
      denoteArg_eq_some_levelArg hΓ hvl a hwf.1.2]
    dsimp only [liveVarsP, liveVarsPFlat]
    rw [liveVarsPFlat_eq dl dld g.sub1 k hΓ hvl hΔ hmL hwf.2]
  | g, .call f bs args k, Γ, Δ, vs, ls, inLD, inLE, hΓ, hvl, hΔ, hmL, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denote]
    rw [denoteArgs_eq_some_levelArgs hΓ hvl args hwf.1]
    dsimp only [liveVarsP, liveVarsPFlat]
    have hk := liveVarsPFlat_eq dl dld g.sub1 k (CtxTypes.push _ hΓ) hvl.pushTup hΔ hmL hwf.2
    rw [pushTup_length] at hk
    rw [hk]
  | g, .jnz c t e, Γ, Δ, vs, ls, inLD, inLE, hΓ, hvl, hΔ, hmL, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denote]
    rw [denoteArg_eq_some_levelArg hΓ hvl c hwf.1.1]
    dsimp only [liveVarsP, liveVarsPFlat]
    rw [liveVarsPFlat_eq dl dld g.subT t hΓ hvl hΔ hmL hwf.1.2,
      liveVarsPFlat_eq dl dld g.subE e hΓ hvl hΔ hmL hwf.2]
  | _, .jump (ts := ts) j args, Γ, Δ, vs, ls, inLD, inLE, hΓ, hvl, hΔ, hmL, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨m, hlk, hres⟩ := lookupL_eq_some_resolveLabel hΔ hmL hwf.1
    dsimp only [denote]
    rw [hlk, denoteArgs_eq_some_levelArgs hΓ hvl args hwf.2]
    dsimp only [liveVarsP, liveVarsPFlat]
    rw [hres]
  | _, .ret vs', Γ, _, vs, _, _, _, hΓ, hvl, _, _, hwf => by
    dsimp only [denote]
    rw [denoteArgs_eq_some_levelArgs hΓ hvl vs' hwf]
    rfl
  | _, .exit f args, Γ, _, vs, _, _, _, hΓ, hvl, _, _, hwf => by
    dsimp only [denote]
    rw [denoteArgs_eq_some_levelArgs hΓ hvl args hwf]
    rfl
  | _, .hlt, _, _, _, _, _, _, _, _, _, _, _ => rfl
  | g, .group (sig := sig) bodies k, Γ, Δ, vs, ls, inLD, inLE, hΓ, hvl, hΔ, hmL, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denote, liveVarsP, liveVarsPFlat]
    have hb := liveVarsBPFlat_eq dl dld g.subB bodies hΓ hvl
      (CtxTypes.push (g.subB.masksOf sig) hΔ)
      (trieCtxMatch_insertTupEnv hmL (g.subB.masksOf sig)) hwf.1
    have hk := liveVarsPFlat_eq dl dld g.subK k hΓ hvl
      (CtxTypes.push (g.subB.masksOf sig) hΔ)
      (trieCtxMatch_insertTupEnv hmL (g.subB.masksOf sig)) hwf.2
    rw [hb, hk]

private theorem liveVarsBPFlat_eq (dl dld : Bool) {rs : List Ty} :
    (g : PBlocks) → {sig : List (List Ty)} → (tb : TBlocks rs sig) →
    {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × K t)} → {ls : List ((ts : List Ty) × KLM ts)} →
    {inLD : Nat} → {inLE : Trie ((ts : List Ty) × Mask ts)} →
    CtxTypes Γ vs → CtxLevels vs → CtxTypes Δ ls → TrieCtxMatch inLD inLE ls →
    tb.wfCheck Γ Δ = true →
    liveVarsBP dl dld g vs.length (denoteB K KLM tb vs ls) =
      liveVarsBPFlat dl dld g vs.length inLD inLE tb
  | _, _, .nil, _, _, _, _, _, _, _, _, _, _, _ => rfl
  | g, _, .cons (ts := ts) hd tl, Γ, Δ, vs, ls, inLD, inLE, hΓ, hvl, hΔ, hmL, hwf => by
    dsimp only [TBlocks.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denoteB, liveVarsBP, liveVarsBPFlat]
    have hh := liveVarsPFlat_eq dl dld g.hd hd (CtxTypes.push _ hΓ) hvl.pushTup hΔ hmL hwf.1
    rw [pushTup_length] at hh
    rw [hh, liveVarsBPFlat_eq dl dld g.tl tl hΓ hvl hΔ hmL hwf.2]
end

private theorem iterN_liveVarsPFlat_eq (dl dld : Bool) {rs : List Ty} (tf : TFlat rs)
    {Γ : List Ty} {Δ : List (List Ty)}
    {vs : List ((t : Ty) × K t)} {ls : List ((ts : List Ty) × KLM ts)}
    {inLD : Nat} {inLE : Trie ((ts : List Ty) × Mask ts)}
    (hΓ : CtxTypes Γ vs) (hvl : CtxLevels vs) (hΔ : CtxTypes Δ ls)
    (hmL : TrieCtxMatch inLD inLE ls) (hwf : tf.wfCheck Γ Δ = true) :
    ∀ rounds g,
      iterN (fun p => (liveVarsP dl dld p vs.length (denote K KLM tf vs ls)).2.1) rounds g =
      iterN (fun p => (liveVarsPFlat dl dld p vs.length inLD inLE tf).2.1) rounds g
  | 0, _ => rfl
  | n + 1, g => by
    dsimp only [iterN]
    rw [liveVarsPFlat_eq dl dld g tf hΓ hvl hΔ hmL hwf]
    exact iterN_liveVarsPFlat_eq dl dld tf hΓ hvl hΔ hmL hwf n _

mutual
private theorem dceSweepPFlat_eq {rs : List Ty} :
    (tf : TFlat rs) → (kt : PTree) → {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × OptV K t)} → {ls : List ((ts : List Ty) × NLabel KL ts)} →
    {inVD outVD inLD outLD : Nat} →
    {inVE : Trie ((t : Ty) × OptV K t)} → {inLE : Trie ((ts : List Ty) × NLabel KL ts)} →
    CtxTypes Γ vs → CtxTypes Δ ls →
    TrieCtxMatch inVD inVE vs → TrieCtxMatch inLD inLE ls → tf.wfCheck Γ Δ = true →
    toTFlat (dceSweepP kt (denote (OptV K) (NLabel KL) tf vs ls)) outVD outLD =
      dceSweepPFlat kt tf inVD inVE inLD inLE outVD outLD
  | .let_ (ts := ts) op k, kt, Γ, Δ, vs, ls, inVD, outVD, inLD, outLD, inVE, inLE,
      hΓ, hΔ, hmV, hmL, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denote]
    rw [denoteArgs_eq_some_resolveEnvArgs hΓ hmV op.args hwf.1]
    cases kt with
    | letNode keep kt' =>
      cases keep with
      | true =>
        dsimp only [dceSweepP, dceSweepPFlat, toTFlat]
        exact congrArg (TFlat.let_ _)
          (dceSweepPFlat_eq k kt' (CtxTypes.push _ hΓ) hΔ
            (trieCtxMatch_insertTupEnv hmV _) hmL hwf.2)
      | false =>
        dsimp only [dceSweepP, dceSweepPFlat]
        exact dceSweepPFlat_eq k kt' (CtxTypes.push _ hΓ) hΔ
          (trieCtxMatch_insertTupEnv hmV _) hmL hwf.2
    | leaf | node1 _ | node2 _ _ | groupNode _ _ => rfl
  | .load t a k, kt, Γ, Δ, vs, ls, inVD, outVD, inLD, outLD, inVE, inLE,
      hΓ, hΔ, hmV, hmL, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denote]
    rw [denoteArg_eq_some_resolveEnvArg hΓ hmV a hwf.1]
    cases kt with
    | letNode keep kt' =>
      cases keep with
      | true =>
        dsimp only [dceSweepP, dceSweepPFlat, toTFlat]
        exact congrArg (TFlat.load t _)
          (dceSweepPFlat_eq k kt' (.cons hΓ) hΔ (hmV.cons t _) hmL hwf.2)
      | false =>
        dsimp only [dceSweepP, dceSweepPFlat]
        exact dceSweepPFlat_eq k kt' (.cons hΓ) hΔ (hmV.cons t _) hmL hwf.2
    | leaf | node1 _ | node2 _ _ | groupNode _ _ => rfl
  | .store v a k, kt, Γ, Δ, vs, ls, inVD, outVD, inLD, outLD, inVE, inLE,
      hΓ, hΔ, hmV, hmL, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denote]
    rw [denoteArg_eq_some_resolveEnvArg hΓ hmV v hwf.1.1,
      denoteArg_eq_some_resolveEnvArg hΓ hmV a hwf.1.2]
    cases kt with
    | node1 kt' =>
      dsimp only [dceSweepP, dceSweepPFlat, toTFlat]
      exact congrArg (TFlat.store _ _) (dceSweepPFlat_eq k kt' hΓ hΔ hmV hmL hwf.2)
    | leaf | letNode _ _ | node2 _ _ | groupNode _ _ => rfl
  | .call f bs args k, kt, Γ, Δ, vs, ls, inVD, outVD, inLD, outLD, inVE, inLE,
      hΓ, hΔ, hmV, hmL, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denote]
    rw [denoteArgs_eq_some_resolveEnvArgs hΓ hmV args hwf.1]
    cases kt with
    | node1 kt' =>
      dsimp only [dceSweepP, dceSweepPFlat, toTFlat]
      exact congrArg (TFlat.call f bs _)
        (dceSweepPFlat_eq k kt' (CtxTypes.push _ hΓ) hΔ
          (trieCtxMatch_insertTupEnv hmV _) hmL hwf.2)
    | leaf | letNode _ _ | node2 _ _ | groupNode _ _ => rfl
  | .jnz c t e, kt, Γ, Δ, vs, ls, inVD, outVD, inLD, outLD, inVE, inLE,
      hΓ, hΔ, hmV, hmL, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denote]
    rw [denoteArg_eq_some_resolveEnvArg hΓ hmV c hwf.1.1]
    cases kt with
    | node2 ktt kte =>
      dsimp only [dceSweepP, dceSweepPFlat, toTFlat]
      rw [dceSweepPFlat_eq t ktt hΓ hΔ hmV hmL hwf.1.2,
        dceSweepPFlat_eq e kte hΓ hΔ hmV hmL hwf.2]
    | leaf | node1 _ | letNode _ _ | groupNode _ _ => rfl
  | .jump (ts := ts) j args, _, Γ, Δ, vs, ls, inVD, outVD, inLD, outLD, inVE, inLE,
      hΓ, hΔ, hmV, hmL, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨nl, hlk, hres⟩ := lookupL_eq_some_resolveLabel hΔ hmL hwf.1
    dsimp only [denote]
    rw [hlk, denoteArgs_eq_some_resolveEnvArgs hΓ hmV args hwf.2]
    cases nl with
    | mk m l =>
      dsimp only [dceSweepP, dceSweepPFlat, toTFlat]
      rw [hres]; rfl
  | .ret vs', _, Γ, _, vs, _, inVD, outVD, _, _, inVE, _, hΓ, _, hmV, _, hwf => by
    dsimp only [denote]
    rw [denoteArgs_eq_some_resolveEnvArgs hΓ hmV vs' hwf]
    rfl
  | .exit f args, _, Γ, _, vs, _, inVD, outVD, _, _, inVE, _, hΓ, _, hmV, _, hwf => by
    dsimp only [denote]
    rw [denoteArgs_eq_some_resolveEnvArgs hΓ hmV args hwf]
    rfl
  | .hlt, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => rfl
  | .group (sig := sig) bodies k, kt, Γ, Δ, vs, ls, inVD, outVD, inLD, outLD, inVE, inLE,
      hΓ, hΔ, hmV, hmL, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    cases kt with
    | groupNode kbs ktk =>
      dsimp only [denote, dceSweepP, dceSweepPFlat, toTFlat]
      let wrappedL := DceParam.wrapLabels sig (kbs.masksOf sig)
        (Tup.levels (DceParam.narrowSig sig (kbs.masksOf sig)) outLD)
      have hb := dceSweepBPFlat_eq bodies kbs hΓ (CtxTypes.push wrappedL hΔ)
        hmV (trieCtxMatch_insertTupEnv hmL wrappedL) hwf.1
        (outVD := outVD) (outLD := outLD + (DceParam.narrowSig sig (kbs.masksOf sig)).length)
      have hk := dceSweepPFlat_eq k ktk hΓ (CtxTypes.push wrappedL hΔ)
        hmV (trieCtxMatch_insertTupEnv hmL wrappedL) hwf.2
        (outVD := outVD) (outLD := outLD + (DceParam.narrowSig sig (kbs.masksOf sig)).length)
      rw [hb, hk]
    | leaf | node1 _ | letNode _ _ | node2 _ _ => rfl

private theorem dceSweepBPFlat_eq {rs : List Ty} :
    {sig : List (List Ty)} → (tb : TBlocks rs sig) → (kbs : PBlocks) →
    {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × OptV K t)} → {ls : List ((ts : List Ty) × NLabel KL ts)} →
    {inVD outVD inLD outLD : Nat} →
    {inVE : Trie ((t : Ty) × OptV K t)} → {inLE : Trie ((ts : List Ty) × NLabel KL ts)} →
    CtxTypes Γ vs → CtxTypes Δ ls →
    TrieCtxMatch inVD inVE vs → TrieCtxMatch inLD inLE ls → tb.wfCheck Γ Δ = true →
    toTBlocks (dceSweepBP kbs (denoteB (OptV K) (NLabel KL) tb vs ls)) outVD outLD =
      dceSweepBPFlat kbs tb inVD inVE inLD inLE outVD outLD
  | _, .nil, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => rfl
  | _, .cons (ts := ts) b bs, kbs, Γ, Δ, vs, ls, inVD, outVD, inLD, outLD, inVE, inLE,
      hΓ, hΔ, hmV, hmL, hwf => by
    dsimp only [TBlocks.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denoteB, dceSweepBP, dceSweepBPFlat, toTBlocks]
    rw [dceSweepPFlat_eq b kbs.hd (CtxTypes.push _ hΓ) hΔ
        (trieCtxMatch_insertTupEnv hmV _) hmL hwf.1,
      dceSweepBPFlat_eq bs kbs.tl hΓ hΔ hmV hmL hwf.2,
      dceSweepBPFlat]
end

/-- `dcePWithFlat dl dld rounds as tf = reifyFunc (Func.dcePWith dl dld rounds (denoteFunc tf))`
under `wfCheck = true`. -/
theorem dcePWithFlat_eq (dl dld : Bool) (rounds : Nat := 0) {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    dcePWithFlat dl dld rounds as tf =
      reifyFunc (Func.dcePWith dl dld rounds (denoteFunc (as := as) tf)) := by
  have hΓ : CtxTypes (pushTypes as []) (pushTup (Tup.levels as 0) []) :=
    CtxTypes.push (Tup.levels as 0) .nil
  have hvl : CtxLevels (pushTup (Tup.levels as 0) []) := CtxLevels.pushTup CtxLevels.nil
  have hlen : (pushTup (Tup.levels as 0) []).length = as.length := by
    rw [pushTup_length]; simp
  have hiter := iterN_liveVarsPFlat_eq dl dld tf hΓ hvl .nil TrieCtxMatch.empty hwf rounds .leaf
  rw [hlen] at hiter
  have hr := liveVarsPFlat_eq dl dld
    (iterN (fun p => (liveVarsPFlat dl dld p as.length 0 .empty tf).2.1) rounds .leaf)
    tf hΓ hvl .nil TrieCtxMatch.empty hwf
  rw [hlen] at hr
  dsimp only [dcePWithFlat, Func.dcePWith, denoteFunc]
  simp only [hiter, hr]
  split
  · dsimp only [reifyFunc]
    have hm := trieCtxMatch_initEnv (fun x _ => some x) as
    have hm' : TrieCtxMatch as.length (initEnv (fun x _ => some x) as)
        (pushTup (someTup as (Tup.levels as 0)) []) := by
      rwa [← tupFreshWith_some_eq (Tup.levels as 0) 0]
    have hsweep := dceSweepPFlat_eq tf
      (liveVarsPFlat dl dld
        (iterN (fun p => (liveVarsPFlat dl dld p as.length 0 .empty tf).2.1) rounds .leaf)
        as.length 0 .empty tf).2.1
      (CtxTypes.push _ .nil) .nil hm' TrieCtxMatch.empty hwf
      (outVD := as.length) (outLD := 0)
    exact hsweep.symm
  · exact dceWithFlat_eq dl dld tf hwf

/-- `denoteFunc (dcePWithFlat dl dld rounds as tf) = Func.dcePWith dl dld rounds (denoteFunc tf)`
under `wfCheck = true`. -/
theorem denoteFunc_dcePWithFlat (dl dld : Bool) (rounds : Nat := 0) {as rs : List Ty}
    (tf : TFlat rs) (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    denoteFunc (as := as) (dcePWithFlat dl dld rounds as tf) =
      Func.dcePWith dl dld rounds (denoteFunc (as := as) tf) := by
  rw [dcePWithFlat_eq dl dld rounds tf hwf]
  exact Func.renorm_eq_self (Func.dcePWith_wf dl dld rounds (Func.wf_of_denote tf rfl))

/-- `dcePWithFlat` preserves `wfCheck`. -/
theorem dcePWithFlat_wfCheck (dl dld : Bool) (rounds : Nat := 0) {as rs : List Ty}
    (tf : TFlat rs) (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    (dcePWithFlat dl dld rounds as tf).wfCheck (pushTypes as []) [] = true := by
  rw [dcePWithFlat_eq dl dld rounds tf hwf]
  exact PassFlatKit.reifyFunc_wfCheck (Func.dcePWith_wf dl dld rounds (Func.wf_of_denote tf rfl))

/-- `dcePFlat as tf = reifyFunc (Func.dceP (denoteFunc tf))` under `wfCheck = true`. -/
theorem dcePFlat_eq {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    dcePFlat as tf = reifyFunc (Func.dceP (denoteFunc (as := as) tf)) :=
  dcePWithFlat_eq true false 0 tf hwf

/-- `denoteFunc (dcePFlat as tf) = Func.dceP (denoteFunc tf)` under `wfCheck = true`. -/
theorem denoteFunc_dcePFlat {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    denoteFunc (as := as) (dcePFlat as tf) = Func.dceP (denoteFunc (as := as) tf) :=
  denoteFunc_dcePWithFlat true false 0 tf hwf

/-- `dcePFlat` preserves `wfCheck`. -/
theorem dcePFlat_wfCheck {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    (dcePFlat as tf).wfCheck (pushTypes as []) [] = true :=
  dcePWithFlat_wfCheck true false 0 tf hwf

/-- `(dcePFlatFn f).toFn = ⟨f.name, f.as, f.rs, Func.dceP f.toFn.body⟩` under
`wfCheck = true`. -/
theorem dcePFlatFn_toFn (f : TFlatFn) (hwf : f.wfCheck = true) :
    (dcePFlatFn f).toFn = ⟨f.name, f.as, f.rs, Func.dceP f.toFn.body⟩ := by
  dsimp only [dcePFlatFn, TFlatFn.toFn]
  rw [denoteFunc_dcePFlat f.body hwf]

/-- `dcePFlatFn` preserves `TFlatFn.wfCheck`. -/
theorem dcePFlatFn_wfCheck (f : TFlatFn) (hwf : f.wfCheck = true) :
    (dcePFlatFn f).wfCheck = true :=
  dcePFlat_wfCheck f.body hwf

end DceParamProofs

/-! ## 3. `ifOptFlat` Simulation Proofs -/

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

private theorem checkDiamondFlat_eq (bitsOnly : Bool) (jId : Nat) (jTs : List Ty) {rs : List Ty} :
    (tf : TFlat rs) → (next : Nat) → {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × IVal K t)} → {ls : List ((ts : List Ty) × JLabel KL ts)} →
    {inLD : Nat} → {inLE : Trie ((ts : List Ty) × JLabel KL ts)} →
    CtxTypes Γ vs → CtxTypes Δ ls → TrieCtxMatch inLD inLE ls → tf.wfCheck Γ Δ = true →
    checkDiamondWith bitsOnly jId jTs next (denote (IVal K) (JLabel KL) tf vs ls) =
      checkDiamondFlat bitsOnly jId jTs inLD inLE tf
  | .let_ (ts := ts) op k, next, Γ, Δ, vs, ls, inLD, inLE, hΓ, hΔ, hmL, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨args', ha⟩ := Option.isSome_iff_exists.1 (denoteArgs_isSome_of_checkArgs hΓ hwf.1)
    dsimp only [denote]; rw [ha]; dsimp only [checkDiamondWith, checkDiamondFlat]
    rw [checkDiamondFlat_eq bitsOnly jId jTs k (next + ts.length)
      (CtxTypes.push _ hΓ) hΔ hmL hwf.2]
  | .load t a k, next, Γ, Δ, vs, ls, inLD, inLE, hΓ, hΔ, hmL, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨a', ha⟩ := Option.isSome_iff_exists.1 (denoteArg_isSome_of_checkArg hΓ hwf.1)
    dsimp only [denote]; rw [ha]; dsimp only [checkDiamondWith, checkDiamondFlat]
    rw [checkDiamondFlat_eq bitsOnly jId jTs k (next + 1) (.cons hΓ) hΔ hmL hwf.2]
  | .store v a k, next, Γ, Δ, vs, ls, inLD, inLE, hΓ, hΔ, hmL, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨v', hv⟩ := Option.isSome_iff_exists.1 (denoteArg_isSome_of_checkArg hΓ hwf.1.1)
    obtain ⟨a', ha⟩ := Option.isSome_iff_exists.1 (denoteArg_isSome_of_checkArg hΓ hwf.1.2)
    dsimp only [denote]; rw [hv, ha]; dsimp only [checkDiamondWith, checkDiamondFlat]
    rw [checkDiamondFlat_eq bitsOnly jId jTs k next hΓ hΔ hmL hwf.2]
  | .call f bs args k, next, Γ, Δ, vs, ls, inLD, inLE, hΓ, hΔ, hmL, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨args', ha⟩ := Option.isSome_iff_exists.1 (denoteArgs_isSome_of_checkArgs hΓ hwf.1)
    dsimp only [denote]; rw [ha]; dsimp only [checkDiamondWith, checkDiamondFlat]
    rw [checkDiamondFlat_eq bitsOnly jId jTs k (next + bs.length)
      (CtxTypes.push _ hΓ) hΔ hmL hwf.2]
  | .jnz c t e, next, Γ, Δ, vs, ls, inLD, inLE, hΓ, hΔ, hmL, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨c', hc⟩ := Option.isSome_iff_exists.1 (denoteArg_isSome_of_checkArg hΓ hwf.1.1)
    dsimp only [denote]; rw [hc]; dsimp only [checkDiamondWith, checkDiamondFlat]
    cases isSelectSigWith bitsOnly jTs with
    | false => simp only [Bool.false_eq_true, ↓reduceIte]
    | true =>
      simp only [↓reduceIte]
      rw [checkArmFlat_eq (.loc jId jTs) t 2 4 next hΓ hΔ hmL hwf.1.2,
        checkArmFlat_eq (.loc jId jTs) e 2 4 next hΓ hΔ hmL hwf.2]
      rfl
  | .jump (ts := ts) j args, _, Γ, Δ, vs, ls, _, _, hΓ, hΔ, _, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨j', hj⟩ := Option.isSome_iff_exists.1 (lookupL_isSome_of_check hΔ hwf.1)
    obtain ⟨args', ha⟩ := Option.isSome_iff_exists.1 (denoteArgs_isSome_of_checkArgs hΓ hwf.2)
    dsimp only [denote]; rw [hj, ha]; rfl
  | .ret vs', _, Γ, _, vs, _, _, _, hΓ, _, _, hwf => by
    obtain ⟨vs'', hv⟩ := Option.isSome_iff_exists.1 (denoteArgs_isSome_of_checkArgs hΓ hwf)
    dsimp only [denote]; rw [hv]; rfl
  | .exit f args, _, Γ, _, vs, _, _, _, hΓ, _, _, hwf => by
    obtain ⟨args', ha⟩ := Option.isSome_iff_exists.1 (denoteArgs_isSome_of_checkArgs hΓ hwf)
    dsimp only [denote]; rw [ha]; rfl
  | .hlt, _, _, _, _, _, _, _, _, _, _, _ => rfl
  | .group _ _, _, _, _, _, _, _, _, _, _, _, _ => rfl

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
    | jnz _ _ | load _ | store _ | call _ => rfl
  | .load t a k, plan, Γ, Δ, vs, ls, inVD, outVD, outLD, inVE, hΓ, hΔ, hmV, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denote]
    rw [denoteArg_eq_some_resolveEnvArg hΓ hmV a hwf.1]
    cases plan with
    | load rest =>
      dsimp only [hoistDiamond, hoistDiamondFlat, toTFlat]
      exact congrArg (TFlat.load t _)
        (hoistDiamondFlat_eq jLbl k rest (.cons hΓ) hΔ (hmV.cons t _) hwf.2)
    | jnz _ _ | let_ _ | store _ | call _ => rfl
  | .store v a k, plan, Γ, Δ, vs, ls, inVD, outVD, outLD, inVE, hΓ, hΔ, hmV, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denote]
    rw [denoteArg_eq_some_resolveEnvArg hΓ hmV v hwf.1.1,
      denoteArg_eq_some_resolveEnvArg hΓ hmV a hwf.1.2]
    cases plan with
    | store rest =>
      dsimp only [hoistDiamond, hoistDiamondFlat, toTFlat]
      exact congrArg (TFlat.store _ _) (hoistDiamondFlat_eq jLbl k rest hΓ hΔ hmV hwf.2)
    | jnz _ _ | let_ _ | load _ | call _ => rfl
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
    | jnz _ _ | let_ _ | load _ | store _ => rfl
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
        hΓ (.cons hΔ) (hmL.cons ts (.loc depth)) hwf.2
      rw [hcd]
      have hb := ifOptBWithFlat_eq false bodies (depth + 1) hΓ (.cons hΔ)
        hmV (hmL.cons ts (.outer outLD)) hwf.1
        (outVD := outVD) (outLD := outLD + 1)
      rw [hb]
      cases hplan : checkDiamondFlat false depth ts (inLD + 1)
          (inLE.insert inLD ⟨ts, .loc depth⟩) k with
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
