module

public import LeanQbe.T.OptFlatCfg
import LeanQbe.T.FlatDirectLemmas
import LeanQbe.T.PassFlatKit
import LeanQbe.T.DceLemmas
import LeanQbe.T.DceParamLemmas

/-!
# Equivalence Proofs for `OptFlatCfg` DCE / DLE Passes (`OptFlatCfgLemmas0`)

Proves exact `=` correspondence (`std3` axioms only) between the direct `TFlat` DCE, DLE, and
parameterized-DCE passes in `LeanQbe.T.OptFlatCfg` and their PHOAS counterparts (`Func.dce`,
`Func.deadLoadElim`, `Func.dceP`), re-exported by `LeanQbe.T.OptFlatCfgLemmas`:

* `OptFlatCfg.dceWithFlat_eq`, `dceFlat_eq`, `deadLoadElimFlat_eq`, `denoteFunc_deadLoadElimFlat`
* `OptFlatCfg.dcePWithFlat_eq`, `dcePFlat_eq`, `denoteFunc_dcePFlat`, `dcePFlatFn_toFn`
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


end OptFlatCfg
end LeanQbe.T
