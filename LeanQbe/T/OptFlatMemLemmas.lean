/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanQbe Contributors
-/
module

public import LeanQbe.T.OptFlatMem
public import LeanQbe.T.FlatDirect
import LeanQbe.T.OptFlatSimKit
import LeanQbe.T.OptUtilLemmas
import LeanQbe.T.MemLoadLemmas
import LeanQbe.T.AssumeBitsLemmas
import LeanQbe.T.DivConstLemmas

/-!
# Simulation Proofs for `OptFlatMem` (`memLoadFlat_eq`, `assumeBitsFlat_eq`, `divConstFlat_eq`)

Establishes exact `=` correspondence (`std3` axioms only) between every native `Trie`-env
`TFlat → TFlat` pass in `LeanQbe.T.OptFlatMem` and its PHOAS counterpart via
`OptFlatSimKit` (`scanSim_mutual`, `klSim_mutual`, `stdKLSim_mutual`).
-/

set_option autoImplicit false

namespace LeanQbe.T
namespace OptFlatMem

open OptFlatPlanKit OptFlatSimKit

/-! ## 1. `memLoadFlat` Simulation Proofs -/

private theorem analyzeMemFlat_both :
    (∀ {rs : List Ty} (tf : TFlat rs) {Γ Δ vs ls} {_inLD : Nat}
      {_inLE : Trie ((ts : List Ty) × KL ts)} (baseOff : BaseOffMap),
      CtxTypes Γ vs → CtxLevels vs → (CtxTypes Δ ls ∧ CtxLevels ls) →
      tf.wfCheck Γ Δ = true →
      analyzeMemFlat vs.length ls.length baseOff tf =
        analyzeMem vs.length ls.length baseOff (denote K KL tf vs ls)) ∧
    (∀ {rs : List Ty} {sig : List (List Ty)} (tb : TBlocks rs sig) {Γ Δ vs ls} {_inLD : Nat}
      {_inLE : Trie ((ts : List Ty) × KL ts)} (baseOff : BaseOffMap),
      CtxTypes Γ vs → CtxLevels vs → (CtxTypes Δ ls ∧ CtxLevels ls) →
      tb.wfCheck Γ Δ = true →
      analyzeMemBFlat vs.length ls.length baseOff tb =
        analyzeMemB vs.length ls.length baseOff (denoteB K KL tb vs ls)) := by
  refine scanSim_mutual (L₁ := KL) (L₂ := KL) ⟨
    @fun rs ts Γ Δ vs ls _ _ baseOff op k hΓ hvl _ hwf ih => by
      obtain ⟨ha, _⟩ := wf_let hwf
      dsimp only [analyzeMemFlat, denote]; rw [denoteArgs_eq_some_levelArgs hΓ hvl op.args ha]
      dsimp only [analyzeMem]
      have hk := ih (stepBaseOff vs.length baseOff op.code (lvlArgs vs.length op.args))
      rw [pushTup_length] at hk; rw [hk],
    fun baseOff t a k hΓ hvl _ hwf ih => by
      obtain ⟨ha, _⟩ := wf_load hwf
      dsimp only [analyzeMemFlat, denote]; rw [denoteArg_eq_some_levelArg hΓ hvl a ha]
      dsimp only [analyzeMem]; have hk := ih baseOff; rw [List.length_cons] at hk; rw [hk],
    fun baseOff v a k hΓ hvl _ hwf ih => by
      obtain ⟨hv, ha, _⟩ := wf_store hwf; dsimp only [analyzeMemFlat, denote]
      rw [denoteArg_eq_some_levelArg hΓ hvl v hv, denoteArg_eq_some_levelArg hΓ hvl a ha]
      dsimp only [analyzeMem]; rw [ih baseOff],
    fun baseOff f bs args k hΓ hvl _ hwf ih => by
      obtain ⟨ha, _⟩ := wf_call hwf
      dsimp only [analyzeMemFlat, denote]; rw [denoteArgs_eq_some_levelArgs hΓ hvl args ha]
      dsimp only [analyzeMem]; have hk := ih baseOff; rw [pushTup_length] at hk; rw [hk],
    fun baseOff c t e hΓ hvl _ hwf iht ihe => by
      obtain ⟨hc, _, _⟩ := wf_jnz hwf
      dsimp only [analyzeMemFlat, denote]; rw [denoteArg_eq_some_levelArg hΓ hvl c hc]
      dsimp only [analyzeMem]; rw [iht baseOff, ihe baseOff],
    @fun _ ts Γ Δ vs ls _ _ _ j args hΓ hvl hlr hwf => by
      obtain ⟨hj, ha⟩ := wf_jump hwf
      obtain ⟨lvl, hgetls, _⟩ := ctxTypes_listGet? hlr.1 (checkJump_eq_true_iff.mp hj)
      have hlvl : lvl = ls.length - 1 - j := hlr.2 j ts lvl hgetls
      have hlk : lookupL ls ts j = some (ls.length - 1 - j) := by
        dsimp only [lookupL]; rw [hgetls]; dsimp only; rw [PassFlatKit.castListTy_self, hlvl]
      dsimp only [analyzeMemFlat, denote]
      rw [hlk, denoteArgs_eq_some_levelArgs hΓ hvl args ha]; rfl,
    fun _ vs' hΓ hvl _ hwf => by
      dsimp only [analyzeMemFlat, denote]; rw [denoteArgs_eq_some_levelArgs hΓ hvl vs' hwf]; rfl,
    fun _ f args hΓ hvl _ hwf => by
      dsimp only [analyzeMemFlat, denote]; rw [denoteArgs_eq_some_levelArgs hΓ hvl args hwf]; rfl,
    fun _ _ _ _ _ => rfl,
    @fun rs sig Γ Δ vs ls _ _ baseOff bodies k _ _ hlr hwf ihB ihK => by
      obtain ⟨hb, hk⟩ := wf_group hwf; dsimp only [analyzeMemFlat, denote, analyzeMem]
      have hb' := ihB (inLD' := 0) (inLE' := .empty) baseOff
        ⟨CtxTypes.push _ hlr.1, hlr.2.pushTup⟩ hb
      have hk' := ihK (inLD' := 0) (inLE' := .empty) baseOff
        ⟨CtxTypes.push _ hlr.1, hlr.2.pushTup⟩ hk
      rw [pushTup_length] at hb' hk'; rw [hb', hk'],
    fun _ _ _ _ _ => rfl,
    fun baseOff _ _ _ _ _ _ ihh iht => by
      dsimp only [analyzeMemBFlat, denoteB, analyzeMemB]
      have hh := ihh baseOff; rw [pushTup_length] at hh; rw [hh, iht baseOff]⟩

private theorem resolveMVal_eq {Γ : List Ty} {vs : List ((t : Ty) × MVal K t)}
    {inDepth : Nat} {inEnv : Trie ((t : Ty) × MVal K t)}
    (hΓ : CtxTypes Γ vs) (hm : TrieCtxMatch inDepth inEnv vs)
    {t : Ty} (a : Arg K t) (hc : checkArg Γ t a = true) :
    ∃ a', denoteArg vs a = some a' ∧
      a'.mout = (resolveMVal inDepth inEnv a).out ∧
      a'.mkey = (resolveMVal inDepth inEnv a).key := by
  cases a with
  | imm c => exact ⟨.imm c, rfl, rfl, rfl⟩
  | var idx =>
    obtain ⟨m, hget, _⟩ := ctxTypes_listGet? hΓ (checkArg_eq_true_iff.mp hc)
    have hlk : lookupV vs t idx = some m := by
      dsimp only [lookupV]; rw [hget]; dsimp only; exact PassFlatKit.castTy_self t m
    have henv : lookupEnv inDepth inEnv t idx = some m := (lookupEnv_eq hΓ hm hc).trans hlk
    refine ⟨.var m, by dsimp only [denoteArg]; rw [hlk],
      by dsimp only [resolveMVal]; rw [henv]; rfl,
      by dsimp only [resolveMVal]; rw [henv]; rfl⟩

private theorem resolveMArgs_eq {Γ : List Ty} {vs : List ((t : Ty) × MVal K t)}
    {inDepth : Nat} {inEnv : Trie ((t : Ty) × MVal K t)}
    (hΓ : CtxTypes Γ vs) (hm : TrieCtxMatch inDepth inEnv vs) (outDepth : Nat) :
    {ts : List Ty} → (as : Tup (Arg K) ts) → checkArgs Γ as = true →
    ∃ as', denoteArgs vs as = some as' ∧
      idxArgs outDepth (tupMOut as') = resolveMOuts inDepth outDepth inEnv as ∧
      tupMKey as' = resolveMKeys inDepth inEnv as
  | [], (), _ => ⟨(), rfl, rfl, rfl⟩
  | _ :: _, (a, as), hc => by
    dsimp only [checkArgs] at hc; simp only [Bool.and_eq_true] at hc
    obtain ⟨a', ha, haout, hakey⟩ := resolveMVal_eq hΓ hm a hc.1
    obtain ⟨as', has, hasout, haskey⟩ := resolveMArgs_eq hΓ hm outDepth as hc.2
    refine ⟨(a', as'), by dsimp only [denoteArgs]; rw [ha, has],
      by dsimp only [tupMOut, tupMapArg, idxArgs, resolveMOuts]; rw [haout, hasout],
      by dsimp only [tupMKey, resolveMKeys]; rw [hakey, haskey]⟩

private theorem memLoadSweepFlat_both :
    (∀ {rs : List Ty} (tf : TFlat rs) {Γ Δ vs ls inD outD inE}
      (s : BaseOffMap × List (CacheEntry K) × MemSumTree),
      CtxTypes Γ vs → CtxTypes Δ ls → CtxLevels ls →
      TrieCtxMatch inD inE vs → tf.wfCheck Γ Δ = true →
      toTFlat (memLoadSweep inD s.1 s.2.1 s.2.2 (denote (MVal K) KL tf vs ls)) outD ls.length =
        memLoadSweepFlat inD outD s.1 s.2.1 s.2.2 tf inE) ∧
    (∀ {rs : List Ty} {sig : List (List Ty)} (tb : TBlocks rs sig) {Γ Δ vs ls inD outD inE}
      (sb : BaseOffMap × List (CacheEntry K) × MemSumBlocks),
      CtxTypes Γ vs → CtxTypes Δ ls → CtxLevels ls →
      TrieCtxMatch inD inE vs → tb.wfCheck Γ Δ = true →
      toTBlocks (memLoadSweepB inD sb.1 sb.2.1 sb.2.2 (denoteB (MVal K) KL tb vs ls))
          outD ls.length =
        memLoadSweepBFlat inD outD sb.1 sb.2.1 sb.2.2 tb inE) := by
  refine klSim_mutual ⟨
    @fun rs ts Γ Δ vs ls inD outD inE ⟨baseOff, cache, mst⟩ op k hΓ _ _ hm hwf ih => by
      obtain ⟨ha, hk⟩ := wf_let hwf
      obtain ⟨args', hda, houts, hkeys⟩ := resolveMArgs_eq hΓ hm outD op.args ha
      simp only [memLoadSweepFlat, denote]; rw [hda]; simp only [memLoadSweep, toTFlat]
      rw [houts, hkeys]
      have hm' := trieCtxMatch_insertFreshWith (fun t i o => @MVal.fresh K t o i) hm ts outD
      rw [← tupFreshWith_pair_eq_mkFreshTup (fun {t} x n => @MVal.fresh K t x n)
        (fun t i o => @MVal.fresh K t o i) (fun _ _ _ => rfl)] at hm'
      exact congrArg (TFlat.let_ _)
        (ih (stepBaseOff inD baseOff op.code (resolveMKeys inD inE op.args), cache,
          match mst with | .node1 kt' => kt' | _ => .leaf)
          (ctxTypes_pushTup_rev _ hΓ) hm' hk),
    @fun rs Γ Δ vs ls inD outD inE ⟨baseOff, cache, mst⟩ t a k hΓ _ _ hm hwf ih => by
      obtain ⟨ha, hk⟩ := wf_load hwf
      obtain ⟨a', hda, haout, hakey⟩ := resolveMVal_eq hΓ hm a ha
      simp only [memLoadSweepFlat, denote]; rw [hda, ← haout, ← hakey]
      unfold memLoadSweep; dsimp only
      let kt := match mst with | .node1 kt' => kt' | _ => .leaf
      cases hlook : lookupCache (resolveKey baseOff a'.mkey) t cache with
      | some cached =>
        exact ih (baseOff, cache, kt) (.cons hΓ) (trieCtxMatch_singleton hm t cached) hk
      | none =>
        simp only [toTFlat, idxArg]
        exact congrArg (TFlat.load t _)
          (ih (baseOff, ⟨resolveKey baseOff a'.mkey, t, .var outD, .var inD⟩ :: cache, kt)
            (.cons hΓ) (trieCtxMatch_singleton hm t _) hk),
    @fun rs t Γ Δ vs ls inD outD inE ⟨baseOff, cache, mst⟩ v a k hΓ _ _ hm hwf ih => by
      obtain ⟨hv, ha, hk⟩ := wf_store hwf
      obtain ⟨v', hdv, hvout, hvkey⟩ := resolveMVal_eq hΓ hm v hv
      obtain ⟨a', hda, haout, hakey⟩ := resolveMVal_eq hΓ hm a ha
      simp only [memLoadSweepFlat, denote]; rw [hdv, hda]; simp only [memLoadSweep, toTFlat]
      rw [← hvout, ← hvkey, ← haout, ← hakey]
      let kt := match mst with | .node1 kt' => kt' | _ => .leaf
      let kbase := filterCacheWrite (resolveKey baseOff a'.mkey) t.bytes cache
      by_cases hsz : t.bytes ≤ 2 ^ 64
      · simp only [hsz, ↓reduceIte]
        exact congrArg (TFlat.store _ _)
          (ih (baseOff, ⟨resolveKey baseOff a'.mkey, t, v'.mout, v'.mkey⟩ :: kbase, kt) hΓ hm hk)
      · simp only [hsz, ↓reduceIte]
        exact congrArg (TFlat.store _ _) (ih (baseOff, kbase, kt) hΓ hm hk),
    @fun rs as Γ Δ vs ls inD outD inE ⟨baseOff, _, mst⟩ f bs args k hΓ _ _ hm hwf ih => by
      obtain ⟨ha, hk⟩ := wf_call hwf
      obtain ⟨args', hda, houts, _⟩ := resolveMArgs_eq hΓ hm outD args ha
      simp only [memLoadSweepFlat, denote]; rw [hda]; simp only [memLoadSweep, toTFlat]
      rw [houts]
      have hm' := trieCtxMatch_insertFreshWith (fun t i o => @MVal.fresh K t o i) hm bs outD
      rw [← tupFreshWith_pair_eq_mkFreshTup (fun {t} x n => @MVal.fresh K t x n)
        (fun t i o => @MVal.fresh K t o i) (fun _ _ _ => rfl)] at hm'
      exact congrArg (TFlat.call f bs _)
        (ih (baseOff, [], match mst with | .node1 kt' => kt' | _ => .leaf)
          (ctxTypes_pushTup_rev _ hΓ) hm' hk),
    @fun rs Γ Δ vs ls inD outD inE ⟨baseOff, cache, mst⟩ c t e hΓ _ _ hm hwf iht ihe => by
      obtain ⟨hc, ht, he⟩ := wf_jnz hwf
      obtain ⟨c', hdc, hcout, _⟩ := resolveMVal_eq hΓ hm c hc
      simp only [memLoadSweepFlat, denote]; rw [hdc]
      simp only [memLoadSweep, toTFlat]; rw [← hcout]
      cases mst with
      | node2 ktt kte =>
        exact congr (congrArg (TFlat.jnz _) (iht (baseOff, cache, ktt) ht))
          (ihe (baseOff, cache, kte) he)
      | _ =>
        exact congr (congrArg (TFlat.jnz _) (iht (baseOff, cache, .leaf) ht))
          (ihe (baseOff, cache, .leaf) he),
    @fun rs ts Γ Δ vs ls inD outD inE _ j args hΓ hΔ hll hm hwf => by
      obtain ⟨hj, ha⟩ := wf_jump hwf
      obtain ⟨_, hlk, hinv⟩ := lookupL_jump_eq hΔ hll hj
      obtain ⟨args', hda, houts, _⟩ := resolveMArgs_eq hΓ hm outD args ha
      dsimp only [memLoadSweepFlat, denote]; rw [hlk, hda]; dsimp only [memLoadSweep, toTFlat]
      rw [hinv, houts],
    @fun rs Γ Δ vs ls inD outD inE _ vs' hΓ _ _ hm hwf => by
      obtain ⟨vs'', hdv, houts, _⟩ := resolveMArgs_eq hΓ hm outD vs' hwf
      dsimp only [memLoadSweepFlat, denote]; rw [hdv]
      dsimp only [memLoadSweep, toTFlat]; rw [houts],
    @fun rs as Γ Δ vs ls inD outD inE _ f args hΓ _ _ hm hwf => by
      obtain ⟨args', hda, houts, _⟩ := resolveMArgs_eq hΓ hm outD args hwf
      dsimp only [memLoadSweepFlat, denote]; rw [hda]
      dsimp only [memLoadSweep, toTFlat]; rw [houts],
    fun _ _ _ _ _ _ => rfl,
    fun ⟨baseOff, cache, mst⟩ bodies k _ hΔ hll _ hwf ihB ihK => by
      obtain ⟨hb, hk⟩ := wf_group hwf
      simp only [memLoadSweepFlat, denote, memLoadSweep, toTFlat]
      cases mst with
      | groupNode sum bsMST kMST =>
        have hb' := ihB (baseOff, filterCacheSummary sum cache, bsMST)
          (ctxTypes_pushTup_rev _ hΔ) hll.pushTup hb
        have hk' := ihK (baseOff, cache, kMST) (ctxTypes_pushTup_rev _ hΔ) hll.pushTup hk
        rw [pushTup_length] at hb' hk'; exact congr (congrArg TFlat.group hb') hk'
      | _ =>
        have hb' := ihB (baseOff, filterCacheSummary .unknown cache, .nil)
          (ctxTypes_pushTup_rev _ hΔ) hll.pushTup hb
        have hk' := ihK (baseOff, cache, .leaf) (ctxTypes_pushTup_rev _ hΔ) hll.pushTup hk
        rw [pushTup_length] at hb' hk'; exact congr (congrArg TFlat.group hb') hk',
    fun _ _ _ _ _ _ => rfl,
    @fun rs ts sig Γ Δ vs ls inD outD inE ⟨baseOff, cache, bsMST⟩ b bs hΓ _ _ hm hwf ihb ihbs => by
      obtain ⟨hb, hbs⟩ := wf_cons hwf
      simp only [memLoadSweepBFlat, denoteB, memLoadSweepB, toTBlocks]
      have hm' := trieCtxMatch_insertFreshWith (fun t i o => @MVal.fresh K t o i) hm ts outD
      rw [← tupFreshWith_pair_eq_mkFreshTup (fun {t} x n => @MVal.fresh K t x n)
        (fun t i o => @MVal.fresh K t o i) (fun _ _ _ => rfl)] at hm'
      cases bsMST with
      | cons kh kt =>
        exact congr (congrArg TBlocks.cons (ihb (baseOff, cache, kh)
          (ctxTypes_pushTup_rev _ hΓ) hm' hb)) (ihbs (baseOff, cache, kt) hbs)
      | nil =>
        exact congr (congrArg TBlocks.cons (ihb (baseOff, cache, .leaf)
          (ctxTypes_pushTup_rev _ hΓ) hm' hb)) (ihbs (baseOff, cache, .nil) hbs)⟩

public section

theorem memLoadFlat_eq {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    memLoadFlat as tf = reifyFunc (Func.memLoad (denoteFunc (as := as) tf)) := by
  dsimp only [memLoadFlat, reifyFunc, Func.memLoad, denoteFunc]
  have hmst := analyzeMemFlat_both.1 (_inLD := 0) (_inLE := .empty) tf .empty
    (ctxTypes_pushTup_rev (Tup.levels as 0) .nil) (CtxLevels.pushTup CtxLevels.nil)
    ⟨.nil, CtxLevels.nil⟩ hwf
  rw [pushTup_length, List.length_nil, Nat.zero_add] at hmst
  have hm := trieCtxMatch_insertFreshWith (fun t i o => @MVal.fresh K t o i)
    (TrieCtxMatch.empty (f := MVal K)) as 0
  rw [Nat.zero_add, ← tupFreshWith_pair_eq_mkFreshTup (fun {t} x n => @MVal.fresh K t x n)
    (fun t i o => @MVal.fresh K t o i) (fun _ _ _ => rfl)] at hm
  have hsw := memLoadSweepFlat_both.1 tf (.empty, [], (analyzeMemFlat as.length 0 .empty tf).2.2)
    (ctxTypes_pushTup_rev _ .nil) .nil CtxLevels.nil hm hwf (outD := as.length)
  rw [List.length_nil] at hsw hmst
  rw [← hsw, ← hmst]

end

/-! ## 2. `assumeBitsFlat` Simulation Proofs -/

private theorem tupAOut_eq :
    {ts : List Ty} → (args : Tup (Arg (ABVal K)) ts) → tupAOut args = mapArgTup Arg.abOut args
  | [], () => rfl
  | _ :: _, (_, as) => congrArg (_, ·) (tupAOut_eq as)

private theorem assumeBits_let_eq {V : Ty → Type} {L : List Ty → Type} {ts rs : List Ty}
    (next : Nat) (F : List BitFact) (op : Op (ABVal V) ts)
    (k : Tup (ABVal V) ts → Expr (ABVal V) L rs) :
    assumeBits next F (.let_ op k) =
      match op.abLet F next with
      | .elim res => assumeBits next F (k res)
      | .emit op' wrap =>
        .let_ op' fun xs => assumeBits (next + ts.length) F (k (wrap xs)) := by
  rw [assumeBits.eq_def]; dsimp only
  cases op.abLet F next <;> rfl

private abbrev assumeBitsSpec : SweepSim assumeBitsSweep where
  mkW t _ o := @ABVal.fresh K t o o
  bindSingle {t} d v := @ABVal.fresh K t v d
  bindTup ts d xs := freshABVals ts xs d
  mkW_eq _ _ _ := rfl
  bindSingle_eq _ _ _ := rfl
  bindTup_eq :=
    tupFreshWith_self_eq_mkFreshTup (fun {t} x n => @ABVal.fresh K t x n)
      (fun t _ o => @ABVal.fresh K t o o) (fun _ _ _ => rfl)
  freshTup_eq _ _ := rfl
  outArgs _ args := tupAOut args
  outArgs_eq _ {_} args := by dsimp only [assumeBitsSweep]; exact tupAOut_eq args
  phoasE F d e := assumeBits d F e
  phoasB F d b := assumeBitsB d F b
  hlt_p _ _ := by rw [assumeBits.eq_def]
  ret_p _ _ _ := by rw [assumeBits.eq_def]; simp only [assumeBitsSweep, tupAOut_eq]
  exit_p _ _ _ _ := by rw [assumeBits.eq_def]; simp only [assumeBitsSweep, tupAOut_eq]
  jump_p _ _ _ _ := by rw [assumeBits.eq_def]; simp only [assumeBitsSweep, tupAOut_eq]
  store_p _ _ _ _ _ := by rw [assumeBits.eq_def]; rfl
  load_p _ _ _ _ _ := by rw [assumeBits.eq_def]; rfl
  call_p _ _ _ _ _ := by rw [assumeBits.eq_def]
  group_p _ _ _ _ := by rw [assumeBits.eq_def]
  nil_p _ _ := by rw [assumeBitsB.eq_def]
  cons_p _ _ _ _ := by rw [assumeBitsB.eq_def]

private theorem assumeBitsGo_both :
    (∀ {rs : List Ty} (tf : TFlat rs) {Γ Δ vs ls inD outD inE} (F : List BitFact),
      CtxTypes Γ vs → CtxTypes Δ ls → CtxLevels ls →
      TrieCtxMatch inD inE vs → tf.wfCheck Γ Δ = true →
      toTFlat (assumeBits outD F (denote (ABVal K) KL tf vs ls)) outD ls.length =
        assumeBitsSweep.run tf inD inE outD F) ∧
    (∀ {rs : List Ty} {sig : List (List Ty)} (tb : TBlocks rs sig) {Γ Δ vs ls inD outD inE}
      (F : List BitFact),
      CtxTypes Γ vs → CtxTypes Δ ls → CtxLevels ls →
      TrieCtxMatch inD inE vs → tb.wfCheck Γ Δ = true →
      toTBlocks (assumeBitsB outD F (denoteB (ABVal K) KL tb vs ls)) outD ls.length =
        assumeBitsSweep.runB tb inD inE outD F) := by
  refine sweepKLSim_mutual assumeBitsSpec ?_ ?_
  · intro rs ts F op k Γ Δ vs ls inD outD inE hΓ _ _ hm hargs hk ih
    simp only [denote]
    rw [denoteArgs_eq_some_resolveEnvArgs hΓ hm op.args hargs (fun _ => .var ⟨.var 0, {}⟩)]
    dsimp only [SweepKL.run, assumeBitsSweep]
    rw [assumeBits_let_eq]
    let abOp : Op (ABVal K) ts :=
      ⟨op.code, resolveEnvArgs inD inE op.args (fun _ => .var ⟨.var 0, {}⟩)⟩
    cases hst : abOp.abLet F outD with
    | elim res =>
      dsimp only
      exact ih F (ctxTypes_pushTup_rev res hΓ) (trieCtxMatch_insertTupEnv hm res) hk
    | emit op' wrap =>
      simp only [toTFlat]
      exact congrArg (TFlat.let_ _)
        (ih F (ctxTypes_pushTup_rev _ hΓ) (trieCtxMatch_insertTupEnv hm _) hk)
  · intro rs F c t e Γ Δ vs ls inD outD inE hΓ _ _ hm hc ht he iht ihe
    simp only [denote]
    rw [denoteArg_eq_some_resolveEnvArg hΓ hm c hc (fun _ => .var ⟨.var 0, {}⟩)]
    dsimp only [SweepKL.run, assumeBitsSweep]
    rw [assumeBits.eq_def]
    simp only [toTFlat]
    rw [iht _ ht, ihe _ he]; rfl

public section

theorem assumeBitsFlat_eq {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    assumeBitsFlat as tf = reifyFunc (Func.assumeBits (denoteFunc (as := as) tf)) := by
  dsimp only [assumeBitsFlat, reifyFunc, Func.assumeBits, denoteFunc]
  have hm := trieCtxMatch_insertFreshWith (fun t _ o => @ABVal.fresh K t o o)
    (TrieCtxMatch.empty (f := ABVal K)) as 0
  rw [Nat.zero_add, ← tupFreshWith_self_eq_mkFreshTup (fun {t} x n => @ABVal.fresh K t x n)
    (fun t _ o => @ABVal.fresh K t o o) (fun _ _ _ => rfl)] at hm
  have h := assumeBitsGo_both.1 tf [] (ctxTypes_pushTup_rev _ .nil) .nil
    CtxLevels.nil hm hwf (outD := as.length)
  rw [List.length_nil] at h
  exact h.symm

end

/-! ## 3. `divConstFlat` Simulation Proofs (No-Div Fast-Path + Full `divConstGo`) -/

private def varLiftArg {V : Ty → Type} {t : Ty} : Arg V t → Arg (Arg V) t
  | .var v => .var (.var v)
  | .imm c => .imm c

private abbrev varLiftArgs {V : Ty → Type} {ts : List Ty} :
    Tup (Arg V) ts → Tup (Arg (Arg V)) ts :=
  tupMapArg fun _ => varLiftArg

private def liftEnv {V : Ty → Type} :
    List ((t : Ty) × V t) → List ((t : Ty) × Arg V t) :=
  List.map fun p => ⟨p.1, Arg.var p.2⟩

private theorem listGet?_map {α β : Type} (f : α → β) :
    (l : List α) → (i : Nat) → listGet? (l.map f) i = (listGet? l i).map f
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: xs, i + 1 => listGet?_map f xs i

private theorem liftEnv_pushTup {V : Ty → Type} :
    {ts : List Ty} → (xs : Tup V ts) → (vs : List ((t : Ty) × V t)) →
    pushTup (toArgTup xs) (liftEnv vs) = liftEnv (pushTup xs vs)
  | [], (), _ => rfl
  | t :: _, (x, xs), vs => liftEnv_pushTup xs (⟨t, x⟩ :: vs)

private theorem flattenArg_varLift {V : Ty → Type} {t : Ty} :
    (a : Arg V t) → flattenArg (varLiftArg a) = a
  | .var _ => rfl
  | .imm _ => rfl

private theorem flattenArgs_varLift {V : Ty → Type} :
    {ts : List Ty} → (as : Tup (Arg V) ts) → flattenArgs (varLiftArgs as) = as
  | [], () => rfl
  | _ :: _, (a, as) => by
    dsimp only [flattenArgs, varLiftArgs, tupMapArg]
    rw [flattenArg_varLift a]
    exact congrArg (_, ·) (flattenArgs_varLift as)

private theorem denoteArg_liftEnv {V : Ty → Type} {Γ : List Ty}
    {vs : List ((t : Ty) × V t)} (hΓ : CtxTypes Γ vs) {t : Ty} :
    (a : Arg K t) → checkArg Γ t a = true →
    ∃ a', denoteArg vs a = some a' ∧ denoteArg (liftEnv vs) a = some (varLiftArg a')
  | .imm c, _ => ⟨.imm c, rfl, rfl⟩
  | .var idx, hc => by
    obtain ⟨v, hget, _⟩ := ctxTypes_listGet? hΓ (checkArg_eq_true_iff.mp hc)
    have h1 : denoteArg vs (.var (t := t) idx) = some (.var v) := by
      dsimp only [denoteArg, lookupV]; rw [hget]; dsimp only; rw [PassFlatKit.castTy_self]
    have h2 : denoteArg (liftEnv vs) (.var (t := t) idx) = some (.var (.var v)) := by
      dsimp only [denoteArg, lookupV, liftEnv]; rw [listGet?_map, hget]
      simp only [Option.map_some]; rw [PassFlatKit.castTy_self]
    exact ⟨.var v, h1, h2⟩

private theorem denoteArgs_liftEnv {V : Ty → Type} {Γ : List Ty}
    {vs : List ((t : Ty) × V t)} (hΓ : CtxTypes Γ vs) :
    {ts : List Ty} → (as : Tup (Arg K) ts) → checkArgs Γ as = true →
    ∃ as', denoteArgs vs as = some as' ∧ denoteArgs (liftEnv vs) as = some (varLiftArgs as')
  | [], (), _ => ⟨(), rfl, rfl⟩
  | _ :: _, (a, as), hc => by
    dsimp only [checkArgs] at hc; simp only [Bool.and_eq_true] at hc
    obtain ⟨a', ha1, ha2⟩ := denoteArg_liftEnv hΓ a hc.1
    obtain ⟨as', has1, has2⟩ := denoteArgs_liftEnv hΓ as hc.2
    exact ⟨(a', as'), by dsimp only [denoteArgs]; rw [ha1, has1], by
      dsimp only [denoteArgs, varLiftArgs, tupMapArg]; rw [ha2, has2]⟩

private theorem divConstOp_eq_fallback {V : Ty → Type} {L : List Ty → Type} {rs ts : List Ty}
    (op : Op (Arg V) ts) (h : opCodeIsDivRem op.code = false)
    (k : Tup (Arg V) ts → Expr V L rs) :
    divConstOp op k = .let_ (flattenOp op) fun xs => k (toArgTup xs) := by
  rcases op with ⟨code, args⟩
  cases code <;> first | exact Bool.noConfusion h | rfl

local macro "div_no_tail" hΓ:ident "," hwf:ident "," a:ident : tactic => `(tactic| (
  obtain ⟨_, h1, h2⟩ := denoteArgs_liftEnv $hΓ $a $hwf
  dsimp only [denote, LeanQbe.T.divConst]; rw [h1, h2]; dsimp only [LeanQbe.T.divConst]
  rw [flattenArgs_varLift]))

mutual
private theorem denote_divConst_eq_of_noDivRem {V : Ty → Type} {L : List Ty → Type}
    {rs : List Ty} :
    (tf : TFlat rs) → {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × V t)} → {ls : List ((ts : List Ty) × L ts)} →
    CtxTypes Γ vs → CtxTypes Δ ls → tf.wfCheck Γ Δ = true → hasDivRem tf = false →
    LeanQbe.T.divConst (denote (Arg V) L tf (liftEnv vs) ls) = denote V L tf vs ls
  | .let_ op k, _, _, vs, ls, hΓ, hΔ, hwf, hdiv => by
    obtain ⟨ha, hk⟩ := wf_let hwf
    dsimp only [hasDivRem] at hdiv; simp only [Bool.or_eq_false_iff] at hdiv
    obtain ⟨args', h1, h2⟩ := denoteArgs_liftEnv hΓ op.args ha
    dsimp only [denote, LeanQbe.T.divConst]; rw [h1, h2]; dsimp only [LeanQbe.T.divConst]
    rw [divConstOp_eq_fallback ⟨op.code, varLiftArgs args'⟩ hdiv.1]
    have hfl : flattenOp ⟨op.code, varLiftArgs args'⟩ = ⟨op.code, args'⟩ := by
      dsimp only [flattenOp]; rw [flattenArgs_varLift]
    rw [hfl]
    refine congrArg (Expr.let_ _) (funext fun xs => ?_)
    rw [liftEnv_pushTup]
    exact denote_divConst_eq_of_noDivRem k (ctxTypes_pushTup_rev xs hΓ) hΔ hk hdiv.2
  | .load t a k, _, _, vs, ls, hΓ, hΔ, hwf, hdiv => by
    obtain ⟨ha, hk⟩ := wf_load hwf
    obtain ⟨a', h1, h2⟩ := denoteArg_liftEnv hΓ a ha
    dsimp only [denote, LeanQbe.T.divConst]; rw [h1, h2]; dsimp only [LeanQbe.T.divConst]
    rw [flattenArg_varLift]
    exact congrArg (Expr.load t a')
      (funext fun v => denote_divConst_eq_of_noDivRem k (.cons hΓ) hΔ hk hdiv)
  | .store v a k, _, _, vs, ls, hΓ, hΔ, hwf, hdiv => by
    obtain ⟨hv, ha, hk⟩ := wf_store hwf
    obtain ⟨v', hv1, hv2⟩ := denoteArg_liftEnv hΓ v hv
    obtain ⟨a', ha1, ha2⟩ := denoteArg_liftEnv hΓ a ha
    dsimp only [denote, LeanQbe.T.divConst]; rw [hv1, hv2, ha1, ha2]
    dsimp only [LeanQbe.T.divConst]; rw [flattenArg_varLift, flattenArg_varLift]
    exact congrArg (Expr.store v' a') (denote_divConst_eq_of_noDivRem k hΓ hΔ hk hdiv)
  | .call f bs args k, _, _, vs, ls, hΓ, hΔ, hwf, hdiv => by
    obtain ⟨ha, hk⟩ := wf_call hwf
    obtain ⟨args', h1, h2⟩ := denoteArgs_liftEnv hΓ args ha
    dsimp only [denote, LeanQbe.T.divConst]; rw [h1, h2]; dsimp only [LeanQbe.T.divConst]
    rw [flattenArgs_varLift]
    refine congrArg (Expr.call f args') (funext fun xs => ?_)
    rw [liftEnv_pushTup]
    exact denote_divConst_eq_of_noDivRem k (ctxTypes_pushTup_rev xs hΓ) hΔ hk hdiv
  | .jnz c t e, _, _, vs, ls, hΓ, hΔ, hwf, hdiv => by
    obtain ⟨hc, ht, he⟩ := wf_jnz hwf
    dsimp only [hasDivRem] at hdiv; simp only [Bool.or_eq_false_iff] at hdiv
    obtain ⟨_, h1, h2⟩ := denoteArg_liftEnv hΓ c hc
    dsimp only [denote, LeanQbe.T.divConst]; rw [h1, h2]; dsimp only [LeanQbe.T.divConst]
    rw [flattenArg_varLift, denote_divConst_eq_of_noDivRem t hΓ hΔ ht hdiv.1,
      denote_divConst_eq_of_noDivRem e hΓ hΔ he hdiv.2]
  | .jump (ts := ts) j args, _, _, vs, ls, hΓ, hΔ, hwf, _ => by
    obtain ⟨hj, ha⟩ := wf_jump hwf
    obtain ⟨_, hj'⟩ := Option.isSome_iff_exists.1 (lookupL_isSome_of_check hΔ hj)
    obtain ⟨_, h1, h2⟩ := denoteArgs_liftEnv hΓ args ha
    dsimp only [denote, LeanQbe.T.divConst]; rw [hj', h1, h2]; dsimp only [LeanQbe.T.divConst]
    rw [flattenArgs_varLift]
  | .ret vs', _, _, _, _, hΓ, _, hwf, _ => by div_no_tail hΓ, hwf, vs'
  | .exit _ args, _, _, _, _, hΓ, _, hwf, _ => by div_no_tail hΓ, hwf, args
  | .hlt, _, _, _, _, _, _, _, _ => rfl
  | .group bodies k, _, _, vs, ls, hΓ, hΔ, hwf, hdiv => by
    obtain ⟨hb, hk⟩ := wf_group hwf
    dsimp only [hasDivRem] at hdiv; simp only [Bool.or_eq_false_iff] at hdiv
    dsimp only [denote, LeanQbe.T.divConst]
    exact congr (congrArg Expr.group (funext fun Js =>
      denoteB_divConst_eq_of_noDivRem bodies hΓ (ctxTypes_pushTup_rev Js hΔ) hb hdiv.1))
      (funext fun Js =>
        denote_divConst_eq_of_noDivRem k hΓ (ctxTypes_pushTup_rev Js hΔ) hk hdiv.2)

private theorem denoteB_divConst_eq_of_noDivRem {V : Ty → Type} {L : List Ty → Type}
    {rs : List Ty} :
    {sig : List (List Ty)} → (tb : TBlocks rs sig) →
    {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × V t)} → {ls : List ((ts : List Ty) × L ts)} →
    CtxTypes Γ vs → CtxTypes Δ ls → tb.wfCheck Γ Δ = true → hasDivRemB tb = false →
    divConstB (denoteB (Arg V) L tb (liftEnv vs) ls) = denoteB V L tb vs ls
  | _, .nil, _, _, _, _, _, _, _, _ => rfl
  | _, .cons b bs, _, _, vs, ls, hΓ, hΔ, hwf, hdiv => by
    obtain ⟨hb, hbs⟩ := wf_cons hwf
    dsimp only [hasDivRemB] at hdiv; simp only [Bool.or_eq_false_iff] at hdiv
    dsimp only [denoteB, divConstB]
    exact congr (congrArg Blocks.cons (funext fun xs => by
      rw [liftEnv_pushTup]
      exact denote_divConst_eq_of_noDivRem b (ctxTypes_pushTup_rev xs hΓ) hΔ hb hdiv.1))
      (denoteB_divConst_eq_of_noDivRem bs hΓ hΔ hbs hdiv.2)
end

private def remKSub {rs : List Ty} (n : Nat) (x : Arg K (.bits n)) (d : BitVec n)
    (k₁ : Arg K (.bits n) → Expr K KL rs) : Arg K (.bits n) → Expr K KL rs := fun q =>
  .let_ (op2 (.mul (.bits n)) q (.imm d)) fun (p, ()) =>
  .let_ (op2 (.sub (.bits n)) x (.var p)) fun (r, ()) =>
  k₁ (.var r)

private theorem remFromDiv_wrap_eq {rs : List Ty} (n : Nat) (x : Arg K (.bits n)) (d : BitVec n)
    (outD nl : Nat) (k₁ : Arg K (.bits n) → Expr K KL rs)
    (dp : Option (DivEmit n)) (de : Option (Expr K KL rs))
    (h : match dp with
      | some p => ∃ e, de = some e ∧
          toTFlat e outD nl = p.wrap (toTFlat (remKSub n x d k₁ p.res) p.outDepth nl)
      | none => de = none) :
    match dp.map (fun p =>
        p.seq fun d1 q =>
        (emitOp2E d1 (.mul (.bits n)) q (.imm d)).seq fun d2 prod =>
        emitOp2E d2 (.sub (.bits n)) x prod) with
    | some p => ∃ e, de = some e ∧ toTFlat e outD nl = p.wrap (toTFlat (k₁ p.res) p.outDepth nl)
    | none => de = none := by
  cases dp with
  | none => exact h
  | some p =>
    obtain ⟨e, he, htf⟩ := h; refine ⟨e, he, ?_⟩
    simpa only [DivEmit.seq, emitOp2E, remKSub, toTFlat, idxArgs, Tup.levels, op2,
      List.length_cons, List.length_nil] using htf

local macro "div_guards" n:ident "," d:ident "," cond2:term "," base:tactic ","
    cont:tactic : tactic => `(tactic| (
  by_cases h1 : (!($n == 32 || $n == 64)) = true
  · simp only [h1, ↓reduceIte]
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    by_cases h2 : $cond2 = true
    · simp only [h2, ↓reduceIte]
    · simp only [h2, Bool.false_eq_true, ↓reduceIte]
      by_cases h3 : ($d == 1#$n) = true
      · simp only [h3, ↓reduceIte]; $base
      · simp only [h3, Bool.false_eq_true, ↓reduceIte]; $cont))

private theorem emitUDivConstPlan_eq {rs : List Ty}
    (n : Nat) (x : Arg K (.bits n)) (d : BitVec n) (outD nl : Nat)
    (k₁ : Arg K (.bits n) → Expr K KL rs) :
    match emitUDivConstPlan n x d outD with
    | some p => ∃ e, emitUDivConst n x d k₁ = some e ∧
        toTFlat e outD nl = p.wrap (toTFlat (k₁ p.res) p.outDepth nl)
    | none => emitUDivConst n x d k₁ = none := by
  dsimp only [emitUDivConstPlan, emitUDivConst]
  div_guards n, d, (d == 0#n), (exact ⟨k₁ x, rfl, rfl⟩), {
    cases findPow2Shift n d with
    | some m =>
      dsimp only
      by_cases hc : pow2ShiftCert n d m = true <;> simp only [hc, ↓reduceIte, Bool.false_eq_true]
      exact ⟨_, rfl, rfl⟩
    | none =>
      dsimp only
      cases findUMagic n d with
      | none => rfl
      | some val =>
        rcases val with ⟨M, s, addShift⟩
        cases addShift <;> dsimp only
        · by_cases hc : uNoAddCert n d M s = true <;>
            simp only [hc, ↓reduceIte, Bool.false_eq_true]; exact ⟨_, rfl, rfl⟩
        · by_cases hc : uAddShiftCert n d M s = true <;>
            simp only [hc, ↓reduceIte, Bool.false_eq_true]; exact ⟨_, rfl, rfl⟩ }

private theorem emitURemConstPlan_eq {rs : List Ty}
    (n : Nat) (x : Arg K (.bits n)) (d : BitVec n) (outD nl : Nat)
    (k₁ : Arg K (.bits n) → Expr K KL rs) :
    match emitURemConstPlan n x d outD with
    | some p => ∃ e, emitURemConst n x d k₁ = some e ∧
        toTFlat e outD nl = p.wrap (toTFlat (k₁ p.res) p.outDepth nl)
    | none => emitURemConst n x d k₁ = none := by
  dsimp only [emitURemConstPlan, emitURemConst]
  div_guards n, d, (d == 0#n), (exact ⟨k₁ (.imm 0#n), rfl, rfl⟩), {
    cases findPow2Shift n d with
    | some m =>
      dsimp only
      by_cases hc : pow2ShiftCert n d m = true <;> simp only [hc, ↓reduceIte, Bool.false_eq_true]
      exact ⟨_, rfl, rfl⟩
    | none =>
      exact remFromDiv_wrap_eq n x d outD nl k₁ _ _
        (emitUDivConstPlan_eq n x d outD nl (remKSub n x d k₁)) }

private theorem emitSDivConstPlan_eq {rs : List Ty}
    (n : Nat) (x : Arg K (.bits n)) (d : BitVec n) (outD nl : Nat)
    (k₁ : Arg K (.bits n) → Expr K KL rs) :
    match emitSDivConstPlan n x d outD with
    | some p => ∃ e, emitSDivConst n x d k₁ = some e ∧
        toTFlat e outD nl = p.wrap (toTFlat (k₁ p.res) p.outDepth nl)
    | none => emitSDivConst n x d k₁ = none := by
  dsimp only [emitSDivConstPlan, emitSDivConst]
  div_guards n, d, (d == 0#n || d == BitVec.allOnes n), (exact ⟨k₁ x, rfl, rfl⟩), {
    cases findSPow2Shift n d with
    | some m =>
      dsimp only
      by_cases hc : sPow2Cert n d m = true <;> simp only [hc, ↓reduceIte, Bool.false_eq_true]
      by_cases hm1 : (m == 1) = true <;> simp only [hm1, ↓reduceIte, Bool.false_eq_true] <;>
        exact ⟨_, rfl, rfl⟩
    | none =>
      dsimp only
      cases findSMagic n d with
      | none => rfl
      | some val =>
        rcases val with ⟨A, s⟩; dsimp only
        by_cases hc : sDivCert n d A s = true
        · simp only [hc, ↓reduceIte]
          let m : BitVec n := BitVec.ofInt n (if 0 < d.toInt then (A : Int) else -(A : Int))
          by_cases hs0 : (s == 0) = true <;>
            by_cases hc1 : (0 < d.toInt && m.toInt < 0) = true <;>
            by_cases hc2 : (d.toInt < 0 && 0 < m.toInt) = true <;>
            simp only [m, hs0, hc1, hc2, ↓reduceIte, Bool.false_eq_true] <;> exact ⟨_, rfl, rfl⟩
        · simp only [hc, Bool.false_eq_true, ↓reduceIte] }

private theorem emitSRemConstPlan_eq {rs : List Ty}
    (n : Nat) (x : Arg K (.bits n)) (d : BitVec n) (outD nl : Nat)
    (k₁ : Arg K (.bits n) → Expr K KL rs) :
    match emitSRemConstPlan n x d outD with
    | some p => ∃ e, emitSRemConst n x d k₁ = some e ∧
        toTFlat e outD nl = p.wrap (toTFlat (k₁ p.res) p.outDepth nl)
    | none => emitSRemConst n x d k₁ = none := by
  dsimp only [emitSRemConstPlan, emitSRemConst]
  div_guards n, d, (d == 0#n || d == BitVec.allOnes n), (exact ⟨k₁ (.imm 0#n), rfl, rfl⟩),
    (exact remFromDiv_wrap_eq n x d outD nl k₁ _ _
      (emitSDivConstPlan_eq n x d outD nl (remKSub n x d k₁)))

local macro "div_op_arm" b:ident "," d:ident "," hhTerm:term "," emitP:term : tactic => `(tactic| (
  dsimp only [flattenArgs, tupMapArg]
  cases hb : flattenArg $b with
  | var _ => dsimp only [divConstEmit]; rfl
  | imm $d =>
    dsimp only [divConstEmit]
    have hh := $hhTerm
    cases hpl : $emitP with
    | none => rw [hpl] at hh; rw [hh]; rfl
    | some _ => rw [hpl] at hh; obtain ⟨_, he, htf⟩ := hh; rw [he]; exact htf))

private theorem toTFlat_divConstOp_eq {rs : List Ty} :
    {ts : List Ty} → (op : Op (Arg K) ts) →
    (k₁ : Tup (Arg K) ts → Expr K KL rs) → (outD nl : Nat) →
    match divConstEmit op.code (flattenArgs op.args) outD with
    | some p => toTFlat (divConstOp op k₁) outD nl = p.wrap (toTFlat (k₁ p.res) p.outDepth nl)
    | none =>
      toTFlat (divConstOp op k₁) outD nl =
        .let_ ⟨op.code, idxArgs outD (flattenArgs op.args)⟩
          (toTFlat (k₁ (toArgTup (Tup.levels ts outD))) (outD + ts.length) nl)
  | _, ⟨code, args⟩, k₁, outD, nl => by
    dsimp only [divConstOp, flattenOp]
    cases code with
    | udiv n =>
      rcases args with ⟨a, b, ⟨⟩⟩
      div_op_arm b, d,
        emitUDivConstPlan_eq n (flattenArg a) d outD nl (fun res => k₁ (res, ())),
        emitUDivConstPlan n (flattenArg a) d outD
    | urem n =>
      rcases args with ⟨a, b, ⟨⟩⟩
      div_op_arm b, d,
        emitURemConstPlan_eq n (flattenArg a) d outD nl (fun res => k₁ (res, ())),
        emitURemConstPlan n (flattenArg a) d outD
    | sdiv n =>
      rcases args with ⟨a, b, ⟨⟩⟩
      div_op_arm b, d,
        emitSDivConstPlan_eq n (flattenArg a) d outD nl (fun res => k₁ (res, ())),
        emitSDivConstPlan n (flattenArg a) d outD
    | srem n =>
      rcases args with ⟨a, b, ⟨⟩⟩
      div_op_arm b, d,
        emitSRemConstPlan_eq n (flattenArg a) d outD nl (fun res => k₁ (res, ())),
        emitSRemConstPlan n (flattenArg a) d outD
    | _ => rfl

private theorem flattenArgs_eq :
    {ts : List Ty} → (args : Tup (Arg (Arg K)) ts) →
    flattenArgs args = mapArgTup flattenArg args
  | [], () => rfl
  | _ :: _, (_, as) => congrArg (_, ·) (flattenArgs_eq as)

private theorem toArgTup_levels_eq_mkFreshTup :
    ∀ (ts : List Ty) (inD outD : Nat),
      toArgTup (Tup.levels ts outD) =
        mkFreshTup (fun _ _ o => (.var o : Arg K _)) ts inD outD
  | [], _, _ => rfl
  | _ :: ts, inD, outD => by
    dsimp only [Tup.levels, toArgTup, mkFreshTup]
    exact congrArg (_, ·) (toArgTup_levels_eq_mkFreshTup ts (inD + 1) (outD + 1))

private abbrev divConstSpec : SweepSim divConstSweep where
  mkW _ _ o := .var o
  bindSingle _ v := .var v
  bindTup _ _ xs := toArgTup xs
  mkW_eq _ _ _ := rfl
  bindSingle_eq _ _ _ := rfl
  bindTup_eq := toArgTup_levels_eq_mkFreshTup
  freshTup_eq _ _ := rfl
  outArgs _ args := flattenArgs args
  outArgs_eq _ {_} args := by dsimp only [divConstSweep]; exact flattenArgs_eq args
  phoasE _ _ e := LeanQbe.T.divConst e
  phoasB _ _ b := divConstB b
  hlt_p _ _ := rfl
  ret_p _ _ _ := by dsimp only [divConstSweep, LeanQbe.T.divConst]; rw [flattenArgs_eq]
  exit_p _ _ _ _ := by dsimp only [divConstSweep, LeanQbe.T.divConst]; rw [flattenArgs_eq]
  jump_p _ _ _ _ := by dsimp only [divConstSweep, LeanQbe.T.divConst]; rw [flattenArgs_eq]
  store_p _ _ _ _ _ := rfl
  load_p _ _ _ _ _ := rfl
  call_p _ _ _ _ _ := rfl
  group_p _ _ _ _ := rfl
  nil_p _ _ := rfl
  cons_p _ _ _ _ := rfl

private theorem divConstGo_both :
    (∀ {rs : List Ty} (tf : TFlat rs) {Γ Δ vs ls inD outD inE} (_ : Unit),
      CtxTypes Γ vs → CtxTypes Δ ls → CtxLevels ls →
      TrieCtxMatch inD inE vs → tf.wfCheck Γ Δ = true →
      toTFlat (LeanQbe.T.divConst (denote (Arg K) KL tf vs ls)) outD ls.length =
        divConstSweep.run tf inD inE outD ()) ∧
    (∀ {rs : List Ty} {sig : List (List Ty)} (tb : TBlocks rs sig) {Γ Δ vs ls inD outD inE}
      (_ : Unit),
      CtxTypes Γ vs → CtxTypes Δ ls → CtxLevels ls →
      TrieCtxMatch inD inE vs → tb.wfCheck Γ Δ = true →
      toTBlocks (divConstB (denoteB (Arg K) KL tb vs ls)) outD ls.length =
        divConstSweep.runB tb inD inE outD ()) := by
  refine sweepKLSim_mutual divConstSpec ?_ ?_
  · intro rs ts _ op k Γ Δ vs ls inD outD inE hΓ _ _ hm hargs hk ih
    simp only [denote]
    rw [denoteArgs_eq_some_resolveEnvArgs hΓ hm op.args hargs (fun _ => .var (.var 0))]
    dsimp only [SweepKL.run, divConstSweep, LeanQbe.T.divConst]
    have hop := toTFlat_divConstOp_eq
      ⟨op.code, resolveEnvArgs inD inE op.args (fun _ => .var (.var 0))⟩
      (fun res => LeanQbe.T.divConst (denote (Arg K) KL k (pushTup res vs) ls)) outD ls.length
    cases hce : divConstEmit op.code
        (flattenArgs (resolveEnvArgs inD inE op.args (fun _ => .var (.var 0)))) outD with
    | some p =>
      rw [hce] at hop; dsimp only at hop ⊢; rw [hop]
      exact congrArg p.wrap
        (ih () (ctxTypes_pushTup_rev p.res hΓ) (trieCtxMatch_insertTupEnv hm p.res) hk)
    | none =>
      rw [hce] at hop; dsimp only at hop ⊢; rw [hop]
      exact congrArg (TFlat.let_ _)
        (ih () (ctxTypes_pushTup_rev _ hΓ) (trieCtxMatch_insertTupEnv hm _) hk)
  · intro rs _ c t e Γ Δ vs ls inD outD inE hΓ _ _ hm hc ht he iht ihe
    exact sweepKL_jnz_plain divConstSpec (fun _ _ => rfl) (fun _ _ _ _ _ => rfl)
      () c t e hΓ hm hc ht he iht ihe

public section

theorem divConstFlat_eq {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    divConstFlat as tf = reifyFunc (Func.divConst (denoteFunc (as := as) tf)) := by
  dsimp only [divConstFlat]
  by_cases hd : hasDivRem tf = true
  · simp only [hd, ↓reduceIte, reifyFunc, Func.divConst, denoteFunc]
    have hm := trieCtxMatch_insertFreshWith (fun _ _ o => (.var o : Arg K _))
      (TrieCtxMatch.empty (f := Arg K)) as 0
    rw [Nat.zero_add, ← toArgTup_levels_eq_mkFreshTup as 0 0] at hm
    have h := divConstGo_both.1 tf () (ctxTypes_pushTup_rev (toArgTup (Tup.levels as 0)) .nil)
      .nil CtxLevels.nil hm hwf (outD := as.length)
    rw [List.length_nil] at h
    exact h.symm
  · have hnd : hasDivRem tf = false := Bool.eq_false_iff.mpr hd
    simp only [hnd, Bool.false_eq_true, ↓reduceIte, reifyFunc, Func.divConst, denoteFunc]
    have hlift : pushTup (toArgTup (Tup.levels as 0)) [] =
        liftEnv (pushTup (Tup.levels as 0) []) := by
      simpa [liftEnv] using liftEnv_pushTup (Tup.levels as 0) []
    rw [hlift, denote_divConst_eq_of_noDivRem tf (ctxTypes_pushTup_rev (Tup.levels as 0) .nil)
      .nil hwf hnd]
    have hrt := toTFlat_denote_eq tf (CtxTypes.push (Tup.levels as 0) .nil) .nil
      (CtxLevels.pushTup CtxLevels.nil) CtxLevels.nil hwf
    simpa [pushTup_length] using hrt.symm

end

/-! ## 4. Shared Preservation & Congruence Corollaries -/

local macro "mem_pass_corollaries" flat:term "," phoas:term "," phoasWf:term ","
    eqThm:ident "," wfThm:ident "," denoteThm:ident "," toFnThm:ident : command => `(
  theorem $wfThm {as rs : List Ty} (tf : TFlat rs)
      (hwf : tf.wfCheck (pushTypes as []) [] = true) :
      ($flat as tf).wfCheck (pushTypes as []) [] = true :=
    wfCheck_of_flat_eq (fun hf => $phoasWf hf) tf hwf ($eqThm tf hwf)

  theorem $denoteThm {as rs : List Ty} (tf : TFlat rs)
      (hwf : tf.wfCheck (pushTypes as []) [] = true) :
      denoteFunc (as := as) ($flat as tf) = $phoas (denoteFunc (as := as) tf) :=
    denoteFunc_of_flat_eq (fun hf => $phoasWf hf) tf hwf ($eqThm tf hwf)

  theorem $toFnThm (f : TFlatFn) (hwf : f.wfCheck = true) :
      reifyFunc ($phoas f.toFn.body) = $flat f.as f.body :=
    ($eqThm f.body hwf).symm
)

public section

mem_pass_corollaries memLoadFlat, Func.memLoad, Func.memLoad_wf,
  memLoadFlat_eq, memLoadFlat_wfCheck, denoteFunc_memLoadFlat, memLoadFlat_toFn
mem_pass_corollaries assumeBitsFlat, Func.assumeBits, Func.assumeBits_wf,
  assumeBitsFlat_eq, assumeBitsFlat_wfCheck, denoteFunc_assumeBitsFlat, assumeBitsFlat_toFn
mem_pass_corollaries divConstFlat, Func.divConst, Func.divConst_wf,
  divConstFlat_eq, divConstFlat_wfCheck, denoteFunc_divConstFlat, divConstFlat_toFn

end

end OptFlatMem
end LeanQbe.T
