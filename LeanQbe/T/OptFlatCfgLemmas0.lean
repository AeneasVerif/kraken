/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanQbe Contributors
-/
module

public import LeanQbe.T.OptFlatCfg
import LeanQbe.T.OptFlatSimKit
import LeanQbe.T.DceLemmas
import LeanQbe.T.DceParamLemmas

/-!
# Equivalence Proofs for `OptFlatCfg` DCE / DLE Passes (`OptFlatCfgLemmas0`)

Proves exact `=` correspondence (`std3` axioms only) between the direct `TFlat` DCE, DLE, and
parameterized-DCE passes in `LeanQbe.T.OptFlatCfg` and their PHOAS counterparts via
`OptFlatSimKit` (`scanSim_mutual`, `klSim_mutual`, `relSim_mutual`).
-/

set_option autoImplicit false

namespace LeanQbe.T
namespace OptFlatCfg

open OptFlatPlanKit OptFlatSimKit

private theorem tupFreshWith_some_eq :
    {ts : List Ty} → (xs : Tup K ts) → (n : Nat) →
    tupFreshWith (fun x _ => some x) ts xs n = someTup ts xs
  | [], (), _ => rfl
  | _ :: _, (_, xs), n => by
    dsimp only [tupFreshWith, someTup]
    rw [tupFreshWith_some_eq xs (n + 1)]

/-! ## 1. `dceWithFlat`, `dceFlat`, `deadLoadElimFlat` Simulation Proofs -/

local macro "lv_let" lvW:Lean.Parser.Tactic.simpLemma "," lvF:Lean.Parser.Tactic.simpLemma ","
    sub:term : term =>
  `(fun g op k hΓ hvl _ hwf ih => by
    obtain ⟨ha, _⟩ := wf_let hwf
    dsimp only [denote]; rw [denoteArgs_eq_some_levelArgs hΓ hvl op.args ha]
    dsimp only [$lvW, $lvF]; have hk := ih ($sub g); rw [pushTup_length] at hk; rw [hk])

local macro "lv_call" lvW:Lean.Parser.Tactic.simpLemma "," lvF:Lean.Parser.Tactic.simpLemma ","
    sub:term : term =>
  `(fun g _ _ args k hΓ hvl _ hwf ih => by
    obtain ⟨ha, _⟩ := wf_call hwf
    dsimp only [denote]; rw [denoteArgs_eq_some_levelArgs hΓ hvl args ha]
    dsimp only [$lvW, $lvF]; have hk := ih ($sub g); rw [pushTup_length] at hk; rw [hk])

local macro "lv_ret" : term =>
  `(fun _ vs' hΓ hvl _ hwf => by
    dsimp only [denote]; rw [denoteArgs_eq_some_levelArgs hΓ hvl vs' hwf]; rfl)

local macro "lv_exit" : term =>
  `(fun _ _ args hΓ hvl _ hwf => by
    dsimp only [denote]; rw [denoteArgs_eq_some_levelArgs hΓ hvl args hwf]; rfl)

private theorem liveVarsFlat_both (dl dld : Bool) :
    (∀ {rs : List Ty} (tf : TFlat rs) {Γ Δ vs ls} {_inLD : Nat}
      {_inLE : Trie ((ts : List Ty) × KL0 ts)} (_ : Unit),
      CtxTypes Γ vs → CtxLevels vs → CtxTypes Δ ls → tf.wfCheck Γ Δ = true →
      liveVarsWith dl dld vs.length (denote K KL0 tf vs ls) = liveVarsFlat dl dld vs.length tf) ∧
    (∀ {rs : List Ty} {sig : List (List Ty)} (tb : TBlocks rs sig) {Γ Δ vs ls} {_inLD : Nat}
      {_inLE : Trie ((ts : List Ty) × KL0 ts)} (_ : Unit),
      CtxTypes Γ vs → CtxLevels vs → CtxTypes Δ ls → tb.wfCheck Γ Δ = true →
      liveVarsBWith dl dld vs.length (denoteB K KL0 tb vs ls) =
        liveVarsBFlat dl dld vs.length tb) := by
  refine scanSim_mutual (L₁ := KL0) (L₂ := KL0) ⟨
    lv_let liveVarsWith, liveVarsFlat, (fun _ => ()),
    @fun _ _ _ vs _ _ _ _ t a k hΓ hvl _ hwf ih => by
      obtain ⟨ha, _⟩ := wf_load hwf
      dsimp only [denote]; rw [denoteArg_eq_some_levelArg hΓ hvl a ha]
      dsimp only [liveVarsWith, liveVarsFlat]
      have hk := ih (); rw [List.length_cons] at hk; rw [hk],
    fun _ v a k hΓ hvl _ hwf ih => by
      obtain ⟨hv, ha, _⟩ := wf_store hwf
      dsimp only [denote]
      rw [denoteArg_eq_some_levelArg hΓ hvl v hv, denoteArg_eq_some_levelArg hΓ hvl a ha]
      dsimp only [liveVarsWith, liveVarsFlat]; rw [ih ()],
    lv_call liveVarsWith, liveVarsFlat, (fun _ => ()),
    fun _ c t e hΓ hvl _ hwf iht ihe => by
      obtain ⟨hc, _, _⟩ := wf_jnz hwf
      dsimp only [denote]; rw [denoteArg_eq_some_levelArg hΓ hvl c hc]
      dsimp only [liveVarsWith, liveVarsFlat]; rw [iht (), ihe ()],
    fun _ j args hΓ hvl hΔ hwf => by
      obtain ⟨hj, ha⟩ := wf_jump hwf
      obtain ⟨_, hj'⟩ := Option.isSome_iff_exists.1 (lookupL_isSome_of_check hΔ hj)
      dsimp only [denote]; rw [hj', denoteArgs_eq_some_levelArgs hΓ hvl args ha]; rfl,
    lv_ret,
    lv_exit,
    fun _ _ _ _ _ => rfl,
    fun _ bodies k _ _ hΔ hwf ihB ihK => by
      obtain ⟨hb, hk⟩ := wf_group hwf
      dsimp only [denote, liveVarsWith, liveVarsFlat]
      rw [ihB (inLD' := 0) (inLE' := .empty) () (CtxTypes.push _ hΔ) hb,
        ihK (inLD' := 0) (inLE' := .empty) () (CtxTypes.push _ hΔ) hk],
    fun _ _ _ _ _ => rfl,
    fun _ _ _ _ _ _ _ ihh iht => by
      dsimp only [denoteB, liveVarsBWith, liveVarsBFlat]
      have hh := ihh (); rw [pushTup_length] at hh; rw [hh, iht ()]⟩

local macro "dce_keep" kt:Lean.Parser.Tactic.elimTarget "," d1:Lean.Parser.Tactic.simpLemma ","
    d2:Lean.Parser.Tactic.simpLemma "," ctor:term "," next:tactic : tactic => `(tactic| (
  cases $kt with
  | letNode keep _ =>
    cases keep with
    | true => dsimp only [$d1, $d2, toTFlat]; refine congrArg $ctor ?_; $next
    | false => dsimp only [$d1, $d2]; $next
  | _ => rfl))

local macro "dce_node1" kt:Lean.Parser.Tactic.elimTarget "," d1:Lean.Parser.Tactic.simpLemma ","
    d2:Lean.Parser.Tactic.simpLemma "," ctor:term "," next:tactic : tactic => `(tactic| (
  cases $kt with
  | node1 _ => dsimp only [$d1, $d2, toTFlat]; refine congrArg $ctor ?_; $next
  | _ => rfl))

private theorem dceSweepFlat_both :
    (∀ {rs : List Ty} (tf : TFlat rs) {Γ Δ vs ls inD outD inE} (kt : KeepTree),
      CtxTypes Γ vs → CtxTypes Δ ls → CtxLevels ls →
      TrieCtxMatch inD inE vs → tf.wfCheck Γ Δ = true →
      toTFlat (dceSweep kt (denote (OptV K) KL tf vs ls)) outD ls.length =
        dceSweepFlat kt tf inD inE outD) ∧
    (∀ {rs : List Ty} {sig : List (List Ty)} (tb : TBlocks rs sig) {Γ Δ vs ls inD outD inE}
      (kbs : KeepBlocks),
      CtxTypes Γ vs → CtxTypes Δ ls → CtxLevels ls →
      TrieCtxMatch inD inE vs → tb.wfCheck Γ Δ = true →
      toTBlocks (dceSweepB kbs (denoteB (OptV K) KL tb vs ls)) outD ls.length =
        dceSweepBFlat kbs tb inD inE outD) := by
  refine klSim_mutual ⟨
    fun kt op k hΓ _ _ hm hwf ih => by
      obtain ⟨ha, hk⟩ := wf_let hwf
      dsimp only [denote]; rw [denoteArgs_eq_some_resolveEnvArgs hΓ hm op.args ha]
      dce_keep kt, dceSweep, dceSweepFlat, TFlat.let_ _,
        (exact ih _ (ctxTypes_pushTup_rev _ hΓ) (trieCtxMatch_insertTupEnv hm _) hk),
    fun kt t a k hΓ _ _ hm hwf ih => by
      obtain ⟨ha, hk⟩ := wf_load hwf
      dsimp only [denote]; rw [denoteArg_eq_some_resolveEnvArg hΓ hm a ha]
      dce_keep kt, dceSweep, dceSweepFlat, TFlat.load t _,
        (exact ih _ (.cons hΓ) (trieCtxMatch_singleton hm t _) hk),
    fun kt v a k hΓ _ _ hm hwf ih => by
      obtain ⟨hv, ha, hk⟩ := wf_store hwf
      dsimp only [denote]
      rw [denoteArg_eq_some_resolveEnvArg hΓ hm v hv, denoteArg_eq_some_resolveEnvArg hΓ hm a ha]
      dce_node1 kt, dceSweep, dceSweepFlat, TFlat.store _ _, (exact ih _ hΓ hm hk),
    fun kt f bs args k hΓ _ _ hm hwf ih => by
      obtain ⟨ha, hk⟩ := wf_call hwf
      dsimp only [denote]; rw [denoteArgs_eq_some_resolveEnvArgs hΓ hm args ha]
      dce_node1 kt, dceSweep, dceSweepFlat, TFlat.call f bs _,
        (exact ih _ (ctxTypes_pushTup_rev _ hΓ) (trieCtxMatch_insertTupEnv hm _) hk),
    fun kt c t e hΓ _ _ hm hwf iht ihe => by
      obtain ⟨hc, ht, he⟩ := wf_jnz hwf
      dsimp only [denote]; rw [denoteArg_eq_some_resolveEnvArg hΓ hm c hc]
      cases kt with
      | node2 ktt kte => dsimp only [dceSweep, dceSweepFlat, toTFlat]; rw [iht ktt ht, ihe kte he]
      | _ => rfl,
    fun _ j args hΓ hΔ hll hm hwf => by
      obtain ⟨hj, ha⟩ := wf_jump hwf
      obtain ⟨_, hlk, hidx⟩ := lookupL_jump_eq hΔ hll hj
      dsimp only [denote]; rw [hlk, denoteArgs_eq_some_resolveEnvArgs hΓ hm args ha]
      dsimp only [dceSweep, dceSweepFlat, toTFlat]; rw [hidx],
    fun _ vs' hΓ _ _ hm hwf => by
      dsimp only [denote]; rw [denoteArgs_eq_some_resolveEnvArgs hΓ hm vs' hwf]; rfl,
    fun _ f args hΓ _ _ hm hwf => by
      dsimp only [denote]; rw [denoteArgs_eq_some_resolveEnvArgs hΓ hm args hwf]; rfl,
    fun _ _ _ _ _ _ => rfl,
    fun kt bodies k _ hΔ hll _ hwf ihB ihK => by
      obtain ⟨hb, hk⟩ := wf_group hwf
      cases kt with
      | groupNode kbs ktk =>
        dsimp only [denote, dceSweep, dceSweepFlat, toTFlat]
        have hb' := ihB kbs (ctxTypes_pushTup_rev _ hΔ) hll.pushTup hb
        have hk' := ihK ktk (ctxTypes_pushTup_rev _ hΔ) hll.pushTup hk
        rw [pushTup_length] at hb' hk'; rw [hb', hk']
      | _ => rfl,
    fun _ _ _ _ _ _ => rfl,
    fun kbs b bs hΓ _ _ hm hwf ihb ihbs => by
      obtain ⟨hb, hbs⟩ := wf_cons hwf
      cases kbs with
      | cons kh kt =>
        dsimp only [denoteB, dceSweepB, dceSweepBFlat, toTBlocks]
        rw [ihb kh (ctxTypes_pushTup_rev _ hΓ) (trieCtxMatch_insertTupEnv hm _) hb, ihbs kt hbs]
      | nil =>
        dsimp only [denoteB, dceSweepB, dceSweepBFlat, toTBlocks]
        exact congrArg (TBlocks.cons .hlt) (ihbs .nil hbs)⟩

public section

theorem dceWithFlat_eq (dl dld : Bool) {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    dceWithFlat dl dld as tf = reifyFunc (Func.dceWith dl dld (denoteFunc (as := as) tf)) := by
  have hlen : (pushTup (Tup.levels as 0) []).length = as.length := by
    rw [pushTup_length]; simp
  have hlive := (liveVarsFlat_both dl dld).1 (_inLD := 0) (_inLE := .empty) tf ()
    (CtxTypes.push (Tup.levels as 0) .nil) (CtxLevels.pushTup CtxLevels.nil) .nil hwf
  rw [hlen] at hlive
  have hm := trieCtxMatch_initEnv (fun x _ => some x) as
  have hm' : TrieCtxMatch as.length (initEnv (fun x _ => some x) as)
      (pushTup (someTup as (Tup.levels as 0)) []) := by
    rwa [← tupFreshWith_some_eq (Tup.levels as 0) 0]
  have hsweep := dceSweepFlat_both.1 tf (liveVarsFlat dl dld as.length tf).2
    (CtxTypes.push _ .nil) .nil CtxLevels.nil hm' hwf (outD := as.length)
  dsimp only [dceWithFlat, reifyFunc, Func.dceWith, denoteFunc] at hsweep ⊢
  rw [hlive]; exact hsweep.symm

theorem denoteFunc_dceWithFlat (dl dld : Bool) {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    denoteFunc (as := as) (dceWithFlat dl dld as tf) =
      Func.dceWith dl dld (denoteFunc (as := as) tf) :=
  denoteFunc_of_flat_eq (Func.dceWith_wf dl dld) tf hwf (dceWithFlat_eq dl dld tf hwf)

theorem dceWithFlat_wfCheck (dl dld : Bool) {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    (dceWithFlat dl dld as tf).wfCheck (pushTypes as []) [] = true :=
  wfCheck_of_flat_eq (Func.dceWith_wf dl dld) tf hwf (dceWithFlat_eq dl dld tf hwf)

theorem dceFlat_eq {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    dceFlat as tf = reifyFunc (Func.dce (denoteFunc (as := as) tf)) :=
  dceWithFlat_eq true false tf hwf

flat_pass_corollaries dceFlat, Func.dce, Func.dce_wf,
  dceFlat_eq, denoteFunc_dceFlat, dceFlat_wfCheck,
  dceFlatFn, dceFlatFn_toFn, dceFlatFn_wfCheck

theorem deadLoadElimFlat_eq {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    deadLoadElimFlat as tf = reifyFunc (Func.deadLoadElim (denoteFunc (as := as) tf)) :=
  dceWithFlat_eq false true tf hwf

flat_pass_corollaries deadLoadElimFlat, Func.deadLoadElim, Func.deadLoadElim_wf,
  deadLoadElimFlat_eq, denoteFunc_deadLoadElimFlat, deadLoadElimFlat_wfCheck,
  deadLoadElimFlatFn, deadLoadElimFlatFn_toFn, deadLoadElimFlatFn_wfCheck

end

/-! ## 2. `dcePWithFlat` and `dcePFlat` Simulation Proofs -/

section DceParamProofs
open DceParam

private theorem liveVarsPFlat_both (dl dld : Bool) :
    (∀ {rs : List Ty} (tf : TFlat rs) {Γ Δ vs ls inLD inLE} (g : PTree),
      CtxTypes Γ vs → CtxLevels vs → (CtxTypes Δ ls ∧ TrieCtxMatch inLD inLE ls) →
      tf.wfCheck Γ Δ = true →
      liveVarsP dl dld g vs.length (denote K KLM tf vs ls) =
        liveVarsPFlat dl dld g vs.length inLD inLE tf) ∧
    (∀ {rs : List Ty} {sig : List (List Ty)} (tb : TBlocks rs sig) {Γ Δ vs ls inLD inLE}
      (gb : PBlocks),
      CtxTypes Γ vs → CtxLevels vs → (CtxTypes Δ ls ∧ TrieCtxMatch inLD inLE ls) →
      tb.wfCheck Γ Δ = true →
      liveVarsBP dl dld gb vs.length (denoteB K KLM tb vs ls) =
        liveVarsBPFlat dl dld gb vs.length inLD inLE tb) := by
  refine scanSim_mutual (L₁ := Mask) (L₂ := KLM) ⟨
    lv_let liveVarsP, liveVarsPFlat, DceParam.PTree.sub1,
    fun g t a k hΓ hvl _ hwf ih => by
      obtain ⟨ha, _⟩ := wf_load hwf
      dsimp only [denote]; rw [denoteArg_eq_some_levelArg hΓ hvl a ha]
      dsimp only [liveVarsP, liveVarsPFlat]
      have hk := ih g.sub1; rw [List.length_cons] at hk; rw [hk],
    fun g v a k hΓ hvl _ hwf ih => by
      obtain ⟨hv, ha, _⟩ := wf_store hwf
      dsimp only [denote]
      rw [denoteArg_eq_some_levelArg hΓ hvl v hv, denoteArg_eq_some_levelArg hΓ hvl a ha]
      dsimp only [liveVarsP, liveVarsPFlat]; rw [ih g.sub1],
    lv_call liveVarsP, liveVarsPFlat, DceParam.PTree.sub1,
    fun g c t e hΓ hvl _ hwf iht ihe => by
      obtain ⟨hc, _, _⟩ := wf_jnz hwf
      dsimp only [denote]; rw [denoteArg_eq_some_levelArg hΓ hvl c hc]
      dsimp only [liveVarsP, liveVarsPFlat]; rw [iht g.subT, ihe g.subE],
    fun _ j args hΓ hvl hlr hwf => by
      obtain ⟨hj, ha⟩ := wf_jump hwf
      obtain ⟨_, hlk, hres⟩ := lookupL_eq_some_resolveLabel hlr.1 hlr.2 hj
      dsimp only [denote]; rw [hlk, denoteArgs_eq_some_levelArgs hΓ hvl args ha]
      dsimp only [liveVarsP, liveVarsPFlat]; rw [hres],
    lv_ret,
    lv_exit,
    fun _ _ _ _ _ => rfl,
    @fun _ sig _ _ _ _ _ _ g bodies k _ _ hlr hwf ihB ihK => by
      obtain ⟨hb, hk⟩ := wf_group hwf
      dsimp only [denote, liveVarsP, liveVarsPFlat]
      rw [ihB g.subB ⟨CtxTypes.push (g.subB.masksOf sig) hlr.1,
          trieCtxMatch_insertTupEnv hlr.2 (g.subB.masksOf sig)⟩ hb,
        ihK g.subK ⟨CtxTypes.push (g.subB.masksOf sig) hlr.1,
          trieCtxMatch_insertTupEnv hlr.2 (g.subB.masksOf sig)⟩ hk],
    fun _ _ _ _ _ => rfl,
    fun gb _ _ _ _ _ _ ihh iht => by
      dsimp only [denoteB, liveVarsBP, liveVarsBPFlat]
      have hh := ihh gb.hd; rw [pushTup_length] at hh; rw [hh, iht gb.tl]⟩

private theorem iterN_liveVarsPFlat_eq (dl dld : Bool) {rs : List Ty} (tf : TFlat rs)
    {Γ Δ vs ls inLD inLE}
    (hΓ : CtxTypes Γ vs) (hvl : CtxLevels vs) (hΔ : CtxTypes Δ ls)
    (hmL : TrieCtxMatch inLD inLE ls) (hwf : tf.wfCheck Γ Δ = true) :
    ∀ rounds g,
      iterN (fun p => (liveVarsP dl dld p vs.length (denote K KLM tf vs ls)).2.1) rounds g =
      iterN (fun p => (liveVarsPFlat dl dld p vs.length inLD inLE tf).2.1) rounds g
  | 0, _ => rfl
  | n + 1, g => by
    dsimp only [iterN]
    rw [(liveVarsPFlat_both dl dld).1 tf g hΓ hvl ⟨hΔ, hmL⟩ hwf]
    exact iterN_liveVarsPFlat_eq dl dld tf hΓ hvl hΔ hmL hwf n _

private theorem dceSweepPFlat_both {rs : List Ty} :
    (∀ (tf : TFlat rs) {Γ Δ vs ls inVD outVD inLD outLD inVE inLE} (kt : PTree),
      CtxTypes Γ vs → CtxTypes Δ ls →
      TrieCtxMatch inVD inVE vs → TrieCtxMatch inLD inLE ls → tf.wfCheck Γ Δ = true →
      toTFlat (dceSweepP kt (denote (OptV K) (NLabel KL) tf vs ls)) outVD outLD =
        dceSweepPFlat kt tf inVD inVE inLD inLE outVD outLD) ∧
    (∀ {sig : List (List Ty)} (tb : TBlocks rs sig)
      {Γ Δ vs ls inVD outVD inLD outLD inVE inLE} (kbs : PBlocks),
      CtxTypes Γ vs → CtxTypes Δ ls →
      TrieCtxMatch inVD inVE vs → TrieCtxMatch inLD inLE ls → tb.wfCheck Γ Δ = true →
      toTBlocks (dceSweepBP kbs (denoteB (OptV K) (NLabel KL) tb vs ls)) outVD outLD =
        dceSweepBPFlat kbs tb inVD inVE inLD inLE outVD outLD) := by
  refine relSim_mutual ⟨
    fun kt op k hΓ _ hmV hmL hwf ih => by
      obtain ⟨ha, hk⟩ := wf_let hwf
      dsimp only [denote]; rw [denoteArgs_eq_some_resolveEnvArgs hΓ hmV op.args ha]
      dce_keep kt, dceSweepP, dceSweepPFlat, TFlat.let_ _,
        (exact ih _ (ctxTypes_pushTup_rev _ hΓ) (trieCtxMatch_insertTupEnv hmV _) hmL hk),
    fun kt t a k hΓ _ hmV hmL hwf ih => by
      obtain ⟨ha, hk⟩ := wf_load hwf
      dsimp only [denote]; rw [denoteArg_eq_some_resolveEnvArg hΓ hmV a ha]
      dce_keep kt, dceSweepP, dceSweepPFlat, TFlat.load t _,
        (exact ih _ (.cons hΓ) (trieCtxMatch_singleton hmV t _) hmL hk),
    fun kt v a k hΓ _ hmV hmL hwf ih => by
      obtain ⟨hv, ha, hk⟩ := wf_store hwf
      dsimp only [denote]
      rw [denoteArg_eq_some_resolveEnvArg hΓ hmV v hv, denoteArg_eq_some_resolveEnvArg hΓ hmV a ha]
      dce_node1 kt, dceSweepP, dceSweepPFlat, TFlat.store _ _, (exact ih _ hΓ hmV hmL hk),
    fun kt f bs args k hΓ _ hmV hmL hwf ih => by
      obtain ⟨ha, hk⟩ := wf_call hwf
      dsimp only [denote]; rw [denoteArgs_eq_some_resolveEnvArgs hΓ hmV args ha]
      dce_node1 kt, dceSweepP, dceSweepPFlat, TFlat.call f bs _,
        (exact ih _ (ctxTypes_pushTup_rev _ hΓ) (trieCtxMatch_insertTupEnv hmV _) hmL hk),
    fun kt c t e hΓ _ hmV hmL hwf iht ihe => by
      obtain ⟨hc, ht, he⟩ := wf_jnz hwf
      dsimp only [denote]; rw [denoteArg_eq_some_resolveEnvArg hΓ hmV c hc]
      cases kt with
      | node2 ktt kte => dsimp only [dceSweepP, dceSweepPFlat, toTFlat]; rw [iht ktt ht, ihe kte he]
      | _ => rfl,
    fun _ j args hΓ hΔ hmV hmL hwf => by
      obtain ⟨hj, ha⟩ := wf_jump hwf
      obtain ⟨nl, hlk, hres⟩ := lookupL_eq_some_resolveLabel hΔ hmL hj
      dsimp only [denote]; rw [hlk, denoteArgs_eq_some_resolveEnvArgs hΓ hmV args ha]
      cases nl with | mk m l => dsimp only [dceSweepP, dceSweepPFlat, toTFlat]; rw [hres]; rfl,
    fun _ vs' hΓ _ hmV _ hwf => by
      dsimp only [denote]; rw [denoteArgs_eq_some_resolveEnvArgs hΓ hmV vs' hwf]; rfl,
    fun _ f args hΓ _ hmV _ hwf => by
      dsimp only [denote]; rw [denoteArgs_eq_some_resolveEnvArgs hΓ hmV args hwf]; rfl,
    fun _ _ _ _ _ _ => rfl,
    @fun sig _ Δ _ _ _ _ _ outLD _ _ kt bodies k _ hΔ _ hmL hwf ihB ihK => by
      obtain ⟨hb, hk⟩ := wf_group hwf
      cases kt with
      | groupNode kbs ktk =>
        dsimp only [denote, dceSweepP, dceSweepPFlat, toTFlat]
        let wrappedL := DceParam.wrapLabels sig (kbs.masksOf sig)
          (Tup.levels (DceParam.narrowSig sig (kbs.masksOf sig)) outLD)
        rw [ihB kbs (CtxTypes.push wrappedL hΔ) (trieCtxMatch_insertTupEnv hmL wrappedL) hb,
          ihK ktk (CtxTypes.push wrappedL hΔ) (trieCtxMatch_insertTupEnv hmL wrappedL) hk]
      | _ => rfl,
    fun _ _ _ _ _ _ => rfl,
    fun kbs b bs hΓ _ hmV hmL hwf ihb ihbs => by
      obtain ⟨hb, hbs⟩ := wf_cons hwf
      dsimp only [denoteB, dceSweepBP, dceSweepBPFlat, toTBlocks]
      rw [ihb kbs.hd (ctxTypes_pushTup_rev _ hΓ) (trieCtxMatch_insertTupEnv hmV _) hmL hb,
        ihbs kbs.tl hbs, dceSweepBPFlat]⟩

public section

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
  have hr := (liveVarsPFlat_both dl dld).1 tf
    (iterN (fun p => (liveVarsPFlat dl dld p as.length 0 .empty tf).2.1) rounds .leaf)
    hΓ hvl ⟨.nil, TrieCtxMatch.empty⟩ hwf
  rw [hlen] at hr
  dsimp only [dcePWithFlat, Func.dcePWith, denoteFunc]
  simp only [hiter, hr]
  split
  · dsimp only [reifyFunc]
    have hm := trieCtxMatch_initEnv (fun x _ => some x) as
    have hm' : TrieCtxMatch as.length (initEnv (fun x _ => some x) as)
        (pushTup (someTup as (Tup.levels as 0)) []) := by
      rwa [← tupFreshWith_some_eq (Tup.levels as 0) 0]
    have hsweep := dceSweepPFlat_both.1 tf
      (liveVarsPFlat dl dld
        (iterN (fun p => (liveVarsPFlat dl dld p as.length 0 .empty tf).2.1) rounds .leaf)
        as.length 0 .empty tf).2.1
      (CtxTypes.push _ .nil) .nil hm' TrieCtxMatch.empty hwf
      (outVD := as.length) (outLD := 0)
    exact hsweep.symm
  · exact dceWithFlat_eq dl dld tf hwf

theorem denoteFunc_dcePWithFlat (dl dld : Bool) (rounds : Nat := 0) {as rs : List Ty}
    (tf : TFlat rs) (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    denoteFunc (as := as) (dcePWithFlat dl dld rounds as tf) =
      Func.dcePWith dl dld rounds (denoteFunc (as := as) tf) :=
  denoteFunc_of_flat_eq (Func.dcePWith_wf dl dld rounds) tf hwf
    (dcePWithFlat_eq dl dld rounds tf hwf)

theorem dcePWithFlat_wfCheck (dl dld : Bool) (rounds : Nat := 0) {as rs : List Ty}
    (tf : TFlat rs) (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    (dcePWithFlat dl dld rounds as tf).wfCheck (pushTypes as []) [] = true :=
  wfCheck_of_flat_eq (Func.dcePWith_wf dl dld rounds) tf hwf
    (dcePWithFlat_eq dl dld rounds tf hwf)

theorem dcePFlat_eq {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    dcePFlat as tf = reifyFunc (Func.dceP (denoteFunc (as := as) tf)) :=
  dcePWithFlat_eq true false 0 tf hwf

flat_pass_corollaries dcePFlat, Func.dceP, Func.dceP_wf,
  dcePFlat_eq, denoteFunc_dcePFlat, dcePFlat_wfCheck,
  dcePFlatFn, dcePFlatFn_toFn, dcePFlatFn_wfCheck

end

end DceParamProofs

end OptFlatCfg
end LeanQbe.T
