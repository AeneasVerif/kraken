module

public import LeanQbe.T.OptFlatMem
public import LeanQbe.T.FlatDirect
import LeanQbe.T.FlatDirectLemmas
import LeanQbe.T.PassFlatKit
import LeanQbe.T.OptUtilLemmas
import LeanQbe.T.MemLoadLemmas
import LeanQbe.T.AssumeBitsLemmas
import LeanQbe.T.DivConstLemmas

/-!
# Simulation Proofs for `OptFlatMem` (`memLoadFlat_eq`, `assumeBitsFlat_eq`, `divConstFlat_eq`)

Establishes exact `=` correspondence (`std3` axioms only) between every native `Trie`-env
`TFlat → TFlat` pass in `LeanQbe.T.OptFlatMem` and its PHOAS counterpart in
`MemLoad` / `AssumeBits` / `DivConst`:

* `OptFlatMem.memLoadFlat_eq`, `OptFlatMem.memLoadFlat_wfCheck`, `OptFlatMem.denoteFunc_memLoadFlat`
* `OptFlatMem.assumeBitsFlat_eq`, `OptFlatMem.assumeBitsFlat_wfCheck`,
  `OptFlatMem.denoteFunc_assumeBitsFlat`
* `OptFlatMem.divConstFlat_eq`, `OptFlatMem.divConstFlat_wfCheck`,
  `OptFlatMem.denoteFunc_divConstFlat`
-/

set_option autoImplicit false

public section

namespace LeanQbe.T
namespace OptFlatMem

/-! ## Shared Context, `Trie` Lookup, and Label Helpers -/

private theorem ctxTypes_pushTup_rev {α : Type} {f : α → Type} :
    {ts : List α} → (xs : Tup f ts) → {Γ : List α} → {vs : List ((a : α) × f a)} →
    CtxTypes Γ vs → CtxTypes (pushTypes ts Γ) (pushTup xs vs)
  | [], (), _, _, h => h
  | _ :: _, (_, xs), _, _, h => ctxTypes_pushTup_rev xs (.cons h)

private theorem insertTupEnv_eq {W : Ty → Type} (depth : Nat)
    (env : Trie ((t : Ty) × W t)) :
    {ts : List Ty} → (xs : Tup W ts) →
    insertTupEnv depth env xs = insertTupTrie depth env xs
  | [], () => rfl
  | _ :: _, (_, xs) => insertTupEnv_eq (depth + 1) _ xs

private def mkFreshTup {W : Ty → Type} (mk : (t : Ty) → Nat → Nat → W t) :
    (ts : List Ty) → Nat → Nat → Tup W ts
  | [], _, _ => ()
  | t :: ts, inD, outD => (mk t inD outD, mkFreshTup mk ts (inD + 1) (outD + 1))

private theorem insertFreshWith_eq {W : Ty → Type} (mk : (t : Ty) → Nat → Nat → W t) :
    (ts : List Ty) → (inD outD : Nat) → (env : Trie ((t : Ty) × W t)) →
    insertFreshWith mk inD outD ts env = insertTupTrie inD env (mkFreshTup mk ts inD outD)
  | [], _, _, _ => rfl
  | t :: ts, inD, outD, env => by
    dsimp only [insertFreshWith, mkFreshTup, insertTupTrie]
    exact insertFreshWith_eq mk ts (inD + 1) (outD + 1) _

private theorem mkFreshTup_mval :
    (ts : List Ty) → (inD outD : Nat) →
    mkFreshTup (fun _ i o => MVal.fresh o i) ts inD outD =
      freshMVals ts (Tup.levels ts outD) inD
  | [], _, _ => rfl
  | _ :: ts, inD, outD => by
    dsimp only [mkFreshTup, Tup.levels, freshMVals, tupFreshWith]
    exact congrArg (_, ·) (mkFreshTup_mval ts (inD + 1) (outD + 1))

private theorem mkFreshTup_abval :
    (ts : List Ty) → (inD outD : Nat) →
    mkFreshTup (fun _ _ o => ABVal.fresh o o) ts inD outD =
      freshABVals ts (Tup.levels ts outD) outD
  | [], _, _ => rfl
  | _ :: ts, inD, outD => by
    dsimp only [mkFreshTup, Tup.levels, freshABVals, tupFreshWith]
    exact congrArg (_, ·) (mkFreshTup_abval ts (inD + 1) (outD + 1))

private theorem mkFreshTup_arg :
    (ts : List Ty) → (inD outD : Nat) →
    mkFreshTup (fun _ _ o => (.var o : Arg K _)) ts inD outD =
      toArgTup (Tup.levels ts outD)
  | [], _, _ => rfl
  | _ :: ts, inD, outD => by
    dsimp only [mkFreshTup, Tup.levels, toArgTup]
    exact congrArg (_, ·) (mkFreshTup_arg ts (inD + 1) (outD + 1))

private theorem trieCtxMatch_insertTupEnv {W : Ty → Type}
    {inDepth : Nat} {env : Trie ((t : Ty) × W t)} {vs : List ((t : Ty) × W t)}
    (hm : TrieCtxMatch inDepth env vs) {ts : List Ty} (xs : Tup W ts) :
    TrieCtxMatch (inDepth + ts.length) (insertTupEnv inDepth env xs) (pushTup xs vs) := by
  rw [insertTupEnv_eq]
  exact TrieCtxMatch.pushTup xs hm

private theorem trieCtxMatch_insertFreshWith {W : Ty → Type}
    (mk : (t : Ty) → Nat → Nat → W t) {inDepth : Nat} {env : Trie ((t : Ty) × W t)}
    {vs : List ((t : Ty) × W t)} (hm : TrieCtxMatch inDepth env vs)
    (ts : List Ty) (outDepth : Nat) :
    TrieCtxMatch (inDepth + ts.length) (insertFreshWith mk inDepth outDepth ts env)
      (pushTup (mkFreshTup mk ts inDepth outDepth) vs) := by
  rw [insertFreshWith_eq]
  exact TrieCtxMatch.pushTup (mkFreshTup mk ts inDepth outDepth) hm

private theorem lookupEnv_eq {W : Ty → Type} {Γ : List Ty} {vs : List ((t : Ty) × W t)}
    {inDepth : Nat} {env : Trie ((t : Ty) × W t)}
    (hΓ : CtxTypes Γ vs) (hm : TrieCtxMatch inDepth env vs)
    {t : Ty} {idx : Nat} (hc : checkArg Γ t (.var idx) = true) :
    lookupEnv inDepth env t idx = lookupV vs t idx :=
  TrieCtxMatch.lookupV_eq hΓ hm hc

private theorem resolveArg_eq {W : Ty → Type} (dflt : ∀ t, Arg W t)
    {Γ : List Ty} {vs : List ((t : Ty) × W t)} {inDepth : Nat} {env : Trie ((t : Ty) × W t)}
    (hΓ : CtxTypes Γ vs) (hm : TrieCtxMatch inDepth env vs)
    {t : Ty} (a : Arg K t) (hc : checkArg Γ t a = true) :
    denoteArg vs a = some (resolveArg dflt inDepth env a) := by
  cases a with
  | imm c => rfl
  | var idx =>
    dsimp only [resolveArg, denoteArg]
    rw [lookupEnv_eq hΓ hm hc]
    obtain ⟨w, hget, _⟩ := ctxTypes_listGet? hΓ (checkArg_eq_true_iff.mp hc)
    have hlk : lookupV vs t idx = some w := by
      dsimp only [lookupV]; rw [hget]; dsimp only; exact PassFlatKit.castTy_self t w
    rw [hlk]

private theorem resolveArgs_eq {W : Ty → Type} (dflt : ∀ t, Arg W t)
    {Γ : List Ty} {vs : List ((t : Ty) × W t)} {inDepth : Nat} {env : Trie ((t : Ty) × W t)}
    (hΓ : CtxTypes Γ vs) (hm : TrieCtxMatch inDepth env vs) :
    {ts : List Ty} → (as : Tup (Arg K) ts) → checkArgs Γ as = true →
    denoteArgs vs as = some (resolveArgs dflt inDepth env as)
  | [], (), _ => rfl
  | _ :: _, (a, as), hc => by
    dsimp only [checkArgs] at hc; simp only [Bool.and_eq_true] at hc
    dsimp only [denoteArgs, resolveArgs]
    rw [resolveArg_eq dflt hΓ hm a hc.1, resolveArgs_eq dflt hΓ hm as hc.2]

private theorem lookupL_wf_eq {Δ : List (List Ty)} {ls : List ((ts : List Ty) × KL ts)}
    (hΔ : CtxTypes Δ ls) (hll : CtxLevels ls) {ts : List Ty} {j : Nat}
    (hj : (match listGet? Δ j with
           | some ts' => match listTyDecEq ts' ts with | isTrue _ => true | isFalse _ => false
           | none => false) = true) :
    ∃ l', lookupL ls ts j = some l' ∧
      (if l' < ls.length then ls.length - 1 - l' else ls.length) = j := by
  obtain ⟨lvl, hgetls, hlt⟩ := ctxTypes_listGet? hΔ (checkJump_eq_true_iff.mp hj)
  have hlvl : lvl = ls.length - 1 - j := hll j ts lvl hgetls
  refine ⟨lvl, ?_, ?_⟩
  · dsimp only [lookupL]; rw [hgetls]; dsimp only; exact PassFlatKit.castListTy_self ts lvl
  · subst hlvl
    have h1 : ls.length - 1 - j < ls.length := by omega
    have h2 : ls.length - 1 - (ls.length - 1 - j) = j := by omega
    simp [h1, h2]

/-! ## 1. `memLoadFlat` Simulation Proofs -/

private theorem denoteArg_lvlArg {Γ : List Ty} {vs : List ((t : Ty) × K t)}
    (hΓ : CtxTypes Γ vs) (hvl : CtxLevels vs) {t : Ty} (a : Arg K t)
    (hc : checkArg Γ t a = true) :
    denoteArg vs a = some (lvlArg vs.length a) := by
  cases a with
  | imm c => rfl
  | var idx =>
    obtain ⟨lvl, hgetvs, _⟩ := ctxTypes_listGet? hΓ (checkArg_eq_true_iff.mp hc)
    have hlvl : lvl = vs.length - 1 - idx := hvl idx t lvl hgetvs
    dsimp only [lvlArg, denoteArg, lookupV]
    rw [hgetvs]; dsimp only; rw [PassFlatKit.castTy_self, hlvl]

private theorem denoteArgs_lvlArgs {Γ : List Ty} {vs : List ((t : Ty) × K t)}
    (hΓ : CtxTypes Γ vs) (hvl : CtxLevels vs) :
    {ts : List Ty} → (as : Tup (Arg K) ts) → checkArgs Γ as = true →
    denoteArgs vs as = some (lvlArgs vs.length as)
  | [], (), _ => rfl
  | _ :: _, (a, as), hc => by
    dsimp only [checkArgs] at hc; simp only [Bool.and_eq_true] at hc
    dsimp only [denoteArgs, lvlArgs]
    rw [denoteArg_lvlArg hΓ hvl a hc.1, denoteArgs_lvlArgs hΓ hvl as hc.2]

mutual
private theorem analyzeMemFlat_eq {rs : List Ty} :
    (tf : TFlat rs) → {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × K t)} → {ls : List ((ts : List Ty) × KL ts)} →
    CtxTypes Γ vs → CtxTypes Δ ls → CtxLevels vs → CtxLevels ls →
    tf.wfCheck Γ Δ = true → ∀ (baseOff : BaseOffMap),
    analyzeMemFlat vs.length ls.length baseOff tf =
      analyzeMem vs.length ls.length baseOff (denote K KL tf vs ls)
  | .let_ (ts := ts) op k, _, _, vs, ls, hΓ, hΔ, hvl, hll, hwf, baseOff => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [analyzeMemFlat, denote]
    rw [denoteArgs_lvlArgs hΓ hvl op.args hwf.1]
    dsimp only [analyzeMem]
    have hk := analyzeMemFlat_eq k (CtxTypes.push (Tup.levels ts vs.length) hΓ) hΔ
      hvl.pushTup hll hwf.2 (stepBaseOff vs.length baseOff op.code (lvlArgs vs.length op.args))
    rw [pushTup_length] at hk
    rw [hk]
  | .load t a k, _, _, vs, ls, hΓ, hΔ, hvl, hll, hwf, baseOff => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [analyzeMemFlat, denote]
    rw [denoteArg_lvlArg hΓ hvl a hwf.1]
    dsimp only [analyzeMem]
    have hk := analyzeMemFlat_eq k (.cons hΓ) hΔ (hvl.cons t) hll hwf.2 baseOff
    rw [List.length_cons] at hk
    rw [hk]
  | .store v a k, _, _, vs, ls, hΓ, hΔ, hvl, hll, hwf, baseOff => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [analyzeMemFlat, denote]
    rw [denoteArg_lvlArg hΓ hvl v hwf.1.1, denoteArg_lvlArg hΓ hvl a hwf.1.2]
    dsimp only [analyzeMem]
    rw [analyzeMemFlat_eq k hΓ hΔ hvl hll hwf.2 baseOff]
  | .call f bs args k, _, _, vs, ls, hΓ, hΔ, hvl, hll, hwf, baseOff => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [analyzeMemFlat, denote]
    rw [denoteArgs_lvlArgs hΓ hvl args hwf.1]
    dsimp only [analyzeMem]
    have hk := analyzeMemFlat_eq k (CtxTypes.push (Tup.levels bs vs.length) hΓ) hΔ
      hvl.pushTup hll hwf.2 baseOff
    rw [pushTup_length] at hk
    rw [hk]
  | .jnz c t e, _, _, vs, ls, hΓ, hΔ, hvl, hll, hwf, baseOff => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [analyzeMemFlat, denote]
    rw [denoteArg_lvlArg hΓ hvl c hwf.1.1]
    dsimp only [analyzeMem]
    rw [analyzeMemFlat_eq t hΓ hΔ hvl hll hwf.1.2 baseOff,
      analyzeMemFlat_eq e hΓ hΔ hvl hll hwf.2 baseOff]
  | .jump (ts := ts) j args, _, _, vs, ls, hΓ, hΔ, hvl, hll, hwf, _ => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨lvl, hgetls, _⟩ := ctxTypes_listGet? hΔ (checkJump_eq_true_iff.mp hwf.1)
    have hlvl : lvl = ls.length - 1 - j := hll j ts lvl hgetls
    have hlk : lookupL ls ts j = some (ls.length - 1 - j) := by
      dsimp only [lookupL]; rw [hgetls]; dsimp only; rw [PassFlatKit.castListTy_self, hlvl]
    dsimp only [analyzeMemFlat, denote]
    rw [hlk, denoteArgs_lvlArgs hΓ hvl args hwf.2]
    rfl
  | .ret vs', _, _, vs, _, hΓ, _, hvl, _, hwf, _ => by
    dsimp only [analyzeMemFlat, denote]
    rw [denoteArgs_lvlArgs hΓ hvl vs' hwf]
    rfl
  | .exit f args, _, _, vs, _, hΓ, _, hvl, _, hwf, _ => by
    dsimp only [analyzeMemFlat, denote]
    rw [denoteArgs_lvlArgs hΓ hvl args hwf]
    rfl
  | .hlt, _, _, _, _, _, _, _, _, _, _ => rfl
  | .group (sig := sig) bodies k, _, _, vs, ls, hΓ, hΔ, hvl, hll, hwf, baseOff => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [analyzeMemFlat, denote, analyzeMem]
    have hb := analyzeMemBFlat_eq bodies hΓ (CtxTypes.push (Tup.levels sig ls.length) hΔ)
      hvl hll.pushTup hwf.1 baseOff
    have hk := analyzeMemFlat_eq k hΓ (CtxTypes.push (Tup.levels sig ls.length) hΔ)
      hvl hll.pushTup hwf.2 baseOff
    rw [pushTup_length] at hb hk
    rw [hb, hk]

private theorem analyzeMemBFlat_eq {rs : List Ty} :
    {sig : List (List Ty)} → (tb : TBlocks rs sig) →
    {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × K t)} → {ls : List ((ts : List Ty) × KL ts)} →
    CtxTypes Γ vs → CtxTypes Δ ls → CtxLevels vs → CtxLevels ls →
    tb.wfCheck Γ Δ = true → ∀ (baseOff : BaseOffMap),
    analyzeMemBFlat vs.length ls.length baseOff tb =
      analyzeMemB vs.length ls.length baseOff (denoteB K KL tb vs ls)
  | _, .nil, _, _, _, _, _, _, _, _, _, _ => rfl
  | _, .cons (ts := ts) hd tl, _, _, vs, ls, hΓ, hΔ, hvl, hll, hwf, baseOff => by
    dsimp only [TBlocks.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [analyzeMemBFlat, denoteB, analyzeMemB]
    have hh := analyzeMemFlat_eq hd (CtxTypes.push (Tup.levels ts vs.length) hΓ) hΔ
      hvl.pushTup hll hwf.1 baseOff
    rw [pushTup_length] at hh
    rw [hh, analyzeMemBFlat_eq tl hΓ hΔ hvl hll hwf.2 baseOff]
end

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
    refine ⟨.var m, ?_, ?_, ?_⟩
    · dsimp only [denoteArg]; rw [hlk]
    · dsimp only [resolveMVal]; rw [henv]; rfl
    · dsimp only [resolveMVal]; rw [henv]; rfl

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
    refine ⟨(a', as'), ?_, ?_, ?_⟩
    · dsimp only [denoteArgs]; rw [ha, has]
    · dsimp only [tupMOut, tupMapArg, idxArgs, resolveMOuts]; rw [haout, hasout]
    · dsimp only [tupMKey, resolveMKeys]; rw [hakey, haskey]

mutual
private theorem memLoadSweepFlat_eq {rs : List Ty} :
    (tf : TFlat rs) → {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × MVal K t)} → {ls : List ((ts : List Ty) × KL ts)} →
    {inDepth : Nat} → {inEnv : Trie ((t : Ty) × MVal K t)} →
    CtxTypes Γ vs → CtxTypes Δ ls → CtxLevels ls → TrieCtxMatch inDepth inEnv vs →
    tf.wfCheck Γ Δ = true →
    ∀ (outDepth : Nat) (baseOff : BaseOffMap) (cache : List (CacheEntry K)) (mst : MemSumTree),
      memLoadSweepFlat inDepth outDepth baseOff cache mst tf inEnv =
        toTFlat (memLoadSweep inDepth baseOff cache mst (denote (MVal K) KL tf vs ls))
          outDepth ls.length
  | .let_ (ts := ts) op k, _, _, vs, ls, inDepth, inEnv, hΓ, hΔ, hll, hm, hwf,
      outDepth, baseOff, cache, mst => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨args', hda, houts, hkeys⟩ := resolveMArgs_eq hΓ hm outDepth op.args hwf.1
    simp only [memLoadSweepFlat, denote]
    rw [hda]
    simp only [memLoadSweep, toTFlat]
    rw [houts, hkeys]
    have hk := memLoadSweepFlat_eq k
      (ctxTypes_pushTup_rev (freshMVals ts (Tup.levels ts outDepth) inDepth) hΓ) hΔ hll
      (by
        simpa only [mkFreshTup_mval] using
          trieCtxMatch_insertFreshWith (fun _ i o => MVal.fresh o i) hm ts outDepth)
      hwf.2 (outDepth + ts.length)
      (stepBaseOff inDepth baseOff op.code (resolveMKeys inDepth inEnv op.args)) cache
      (match mst with | .node1 kt' => kt' | _ => .leaf)
    exact congrArg (TFlat.let_ _) hk
  | .load t a k, _, _, vs, ls, inDepth, inEnv, hΓ, hΔ, hll, hm, hwf,
      outDepth, baseOff, cache, mst => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨a', hda, haout, hakey⟩ := resolveMVal_eq hΓ hm a hwf.1
    simp only [memLoadSweepFlat, denote]
    rw [hda]
    rw [← haout, ← hakey]
    unfold memLoadSweep
    dsimp only
    cases hlook : lookupCache (resolveKey baseOff a'.mkey) t cache with
    | some cached =>
      dsimp only
      exact memLoadSweepFlat_eq k (.cons hΓ) hΔ hll (hm.cons t cached) hwf.2
        outDepth baseOff cache (match mst with | .node1 kt' => kt' | _ => .leaf)
    | none =>
      simp only [toTFlat, idxArg]
      have hk := memLoadSweepFlat_eq k (.cons hΓ) hΔ hll (hm.cons t (MVal.fresh outDepth inDepth))
        hwf.2 (outDepth + 1) baseOff
        (⟨resolveKey baseOff a'.mkey, t, .var outDepth, .var inDepth⟩ :: cache)
        (match mst with | .node1 kt' => kt' | _ => .leaf)
      exact congrArg (TFlat.load t (idxArg outDepth a'.mout)) hk
  | .store (t := t) v a k, _, _, vs, ls, inDepth, inEnv, hΓ, hΔ, hll, hm, hwf,
      outDepth, baseOff, cache, mst => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨v', hdv, hvout, hvkey⟩ := resolveMVal_eq hΓ hm v hwf.1.1
    obtain ⟨a', hda, haout, hakey⟩ := resolveMVal_eq hΓ hm a hwf.1.2
    simp only [memLoadSweepFlat, denote]
    rw [hdv, hda]
    simp only [memLoadSweep, toTFlat]
    rw [← hvout, ← hvkey, ← haout, ← hakey]
    by_cases hsz : t.bytes ≤ 2 ^ 64
    · simp only [hsz, ↓reduceIte]
      have hk := memLoadSweepFlat_eq k hΓ hΔ hll hm hwf.2 outDepth baseOff
        (⟨resolveKey baseOff a'.mkey, t, v'.mout, v'.mkey⟩ ::
          filterCacheWrite (resolveKey baseOff a'.mkey) t.bytes cache)
        (match mst with | .node1 kt' => kt' | _ => .leaf)
      exact congrArg (TFlat.store (idxArg outDepth v'.mout) (idxArg outDepth a'.mout)) hk
    · simp only [hsz, ↓reduceIte]
      have hk := memLoadSweepFlat_eq k hΓ hΔ hll hm hwf.2 outDepth baseOff
        (filterCacheWrite (resolveKey baseOff a'.mkey) t.bytes cache)
        (match mst with | .node1 kt' => kt' | _ => .leaf)
      exact congrArg (TFlat.store (idxArg outDepth v'.mout) (idxArg outDepth a'.mout)) hk
  | .call f bs args k, _, _, vs, ls, inDepth, inEnv, hΓ, hΔ, hll, hm, hwf,
      outDepth, baseOff, _, mst => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨args', hda, houts, _⟩ := resolveMArgs_eq hΓ hm outDepth args hwf.1
    simp only [memLoadSweepFlat, denote]
    rw [hda]
    simp only [memLoadSweep, toTFlat]
    rw [houts]
    have hk := memLoadSweepFlat_eq k
      (ctxTypes_pushTup_rev (freshMVals bs (Tup.levels bs outDepth) inDepth) hΓ) hΔ hll
      (by
        simpa only [mkFreshTup_mval] using
          trieCtxMatch_insertFreshWith (fun _ i o => MVal.fresh o i) hm bs outDepth)
      hwf.2 (outDepth + bs.length) baseOff []
      (match mst with | .node1 kt' => kt' | _ => .leaf)
    exact congrArg (TFlat.call f bs _) hk
  | .jnz c t e, _, _, vs, ls, inDepth, inEnv, hΓ, hΔ, hll, hm, hwf,
      outDepth, baseOff, cache, mst => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨c', hdc, hcout, _⟩ := resolveMVal_eq hΓ hm c hwf.1.1
    cases mst with
    | node2 ktt kte =>
      simp only [memLoadSweepFlat, denote]
      rw [hdc]
      simp only [memLoadSweep, toTFlat]
      rw [← hcout]
      have ht := memLoadSweepFlat_eq t hΓ hΔ hll hm hwf.1.2 outDepth baseOff cache ktt
      have he := memLoadSweepFlat_eq e hΓ hΔ hll hm hwf.2 outDepth baseOff cache kte
      exact congr (congrArg (TFlat.jnz (idxArg outDepth c'.mout)) ht) he
    | _ =>
      simp only [memLoadSweepFlat, denote]
      rw [hdc]
      simp only [memLoadSweep, toTFlat]
      rw [← hcout]
      have ht := memLoadSweepFlat_eq t hΓ hΔ hll hm hwf.1.2 outDepth baseOff cache .leaf
      have he := memLoadSweepFlat_eq e hΓ hΔ hll hm hwf.2 outDepth baseOff cache .leaf
      exact congr (congrArg (TFlat.jnz (idxArg outDepth c'.mout)) ht) he
  | .jump (ts := ts) j args, _, _, vs, ls, inDepth, inEnv, hΓ, hΔ, hll, hm, hwf,
      outDepth, _, _, _ => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨l', hlk, hinv⟩ := lookupL_wf_eq hΔ hll hwf.1
    obtain ⟨args', hda, houts, _⟩ := resolveMArgs_eq hΓ hm outDepth args hwf.2
    dsimp only [memLoadSweepFlat, denote]
    rw [hlk, hda]
    dsimp only [memLoadSweep, toTFlat]
    rw [hinv, houts]
  | .ret vs', _, _, vs, _, inDepth, inEnv, hΓ, _, _, hm, hwf, outDepth, _, _, _ => by
    obtain ⟨vs'', hdv, houts, _⟩ := resolveMArgs_eq hΓ hm outDepth vs' hwf
    dsimp only [memLoadSweepFlat, denote]
    rw [hdv]
    dsimp only [memLoadSweep, toTFlat]
    rw [houts]
  | .exit f args, _, _, vs, _, inDepth, inEnv, hΓ, _, _, hm, hwf, outDepth, _, _, _ => by
    obtain ⟨args', hda, houts, _⟩ := resolveMArgs_eq hΓ hm outDepth args hwf
    dsimp only [memLoadSweepFlat, denote]
    rw [hda]
    dsimp only [memLoadSweep, toTFlat]
    rw [houts]
  | .hlt, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => rfl
  | .group (sig := sig) bodies k, _, _, vs, ls, inDepth, inEnv, hΓ, hΔ, hll, hm, hwf,
      outDepth, baseOff, cache, mst => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    simp only [memLoadSweepFlat, denote, memLoadSweep, toTFlat]
    cases mst with
    | groupNode sum bsMST kMST =>
      have hb := memLoadSweepBFlat_eq bodies hΓ (CtxTypes.push (Tup.levels sig ls.length) hΔ)
        hll.pushTup hm hwf.1 outDepth baseOff (filterCacheSummary sum cache) bsMST
      have hk := memLoadSweepFlat_eq k hΓ (CtxTypes.push (Tup.levels sig ls.length) hΔ)
        hll.pushTup hm hwf.2 outDepth baseOff cache kMST
      rw [pushTup_length] at hb hk
      exact congr (congrArg TFlat.group hb) hk
    | _ =>
      have hb := memLoadSweepBFlat_eq bodies hΓ (CtxTypes.push (Tup.levels sig ls.length) hΔ)
        hll.pushTup hm hwf.1 outDepth baseOff (filterCacheSummary .unknown cache) .nil
      have hk := memLoadSweepFlat_eq k hΓ (CtxTypes.push (Tup.levels sig ls.length) hΔ)
        hll.pushTup hm hwf.2 outDepth baseOff cache .leaf
      rw [pushTup_length] at hb hk
      exact congr (congrArg TFlat.group hb) hk

private theorem memLoadSweepBFlat_eq {rs : List Ty} :
    {sig : List (List Ty)} → (tb : TBlocks rs sig) →
    {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × MVal K t)} → {ls : List ((ts : List Ty) × KL ts)} →
    {inDepth : Nat} → {inEnv : Trie ((t : Ty) × MVal K t)} →
    CtxTypes Γ vs → CtxTypes Δ ls → CtxLevels ls → TrieCtxMatch inDepth inEnv vs →
    tb.wfCheck Γ Δ = true →
    ∀ (outDepth : Nat) (baseOff : BaseOffMap) (cache : List (CacheEntry K))
      (bsMST : MemSumBlocks),
      memLoadSweepBFlat inDepth outDepth baseOff cache bsMST tb inEnv =
        toTBlocks (memLoadSweepB inDepth baseOff cache bsMST (denoteB (MVal K) KL tb vs ls))
          outDepth ls.length
  | _, .nil, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => rfl
  | _, .cons (ts := ts) b bs, _, _, vs, ls, inDepth, inEnv, hΓ, hΔ, hll, hm, hwf,
      outDepth, baseOff, cache, bsMST => by
    dsimp only [TBlocks.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    simp only [memLoadSweepBFlat, denoteB, memLoadSweepB, toTBlocks]
    cases bsMST with
    | cons kh kt =>
      have hb := memLoadSweepFlat_eq b
        (ctxTypes_pushTup_rev (freshMVals ts (Tup.levels ts outDepth) inDepth) hΓ) hΔ hll
        (by
          simpa only [mkFreshTup_mval] using
            trieCtxMatch_insertFreshWith (fun _ i o => MVal.fresh o i) hm ts outDepth)
        hwf.1 (outDepth + ts.length) baseOff cache kh
      have hbs := memLoadSweepBFlat_eq bs hΓ hΔ hll hm hwf.2 outDepth baseOff cache kt
      exact congr (congrArg TBlocks.cons hb) hbs
    | nil =>
      have hb := memLoadSweepFlat_eq b
        (ctxTypes_pushTup_rev (freshMVals ts (Tup.levels ts outDepth) inDepth) hΓ) hΔ hll
        (by
          simpa only [mkFreshTup_mval] using
            trieCtxMatch_insertFreshWith (fun _ i o => MVal.fresh o i) hm ts outDepth)
        hwf.1 (outDepth + ts.length) baseOff cache .leaf
      have hbs := memLoadSweepBFlat_eq bs hΓ hΔ hll hm hwf.2 outDepth baseOff cache .nil
      exact congr (congrArg TBlocks.cons hb) hbs
end

/-- `memLoadFlat as tf = reifyFunc (Func.memLoad (denoteFunc tf))` under `wfCheck = true`. -/
theorem memLoadFlat_eq {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    memLoadFlat as tf = reifyFunc (Func.memLoad (denoteFunc (as := as) tf)) := by
  dsimp only [memLoadFlat, reifyFunc, Func.memLoad, denoteFunc]
  have hmst := analyzeMemFlat_eq tf
    (ctxTypes_pushTup_rev (Tup.levels as 0) .nil) .nil
    (CtxLevels.pushTup CtxLevels.nil) CtxLevels.nil hwf .empty
  rw [pushTup_length, List.length_nil, Nat.zero_add] at hmst
  have hm := trieCtxMatch_insertFreshWith (fun _ i o => MVal.fresh o i)
    (TrieCtxMatch.empty (f := MVal K)) as 0
  rw [Nat.zero_add, mkFreshTup_mval] at hm
  have hsw := memLoadSweepFlat_eq tf
    (ctxTypes_pushTup_rev (freshMVals as (Tup.levels as 0) 0) .nil) .nil
    CtxLevels.nil hm hwf as.length .empty []
    (analyzeMemFlat as.length 0 .empty tf).2.2
  rw [List.length_nil] at hsw hmst
  rw [hsw, ← hmst]

/-- `memLoadFlat` preserves `wfCheck`. -/
theorem memLoadFlat_wfCheck {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    (memLoadFlat as tf).wfCheck (pushTypes as []) [] = true := by
  rw [memLoadFlat_eq tf hwf]
  exact PassFlatKit.reifyFunc_wfCheck (Func.memLoad_wf (Func.wf_of_denote tf rfl))

/-- `denoteFunc (memLoadFlat as tf) = Func.memLoad (denoteFunc tf)` under `wfCheck = true`. -/
theorem denoteFunc_memLoadFlat {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    denoteFunc (as := as) (memLoadFlat as tf) = Func.memLoad (denoteFunc (as := as) tf) := by
  rw [memLoadFlat_eq tf hwf]
  exact Func.renorm_eq_self (Func.memLoad_wf (Func.wf_of_denote tf rfl))

/-! ## 2. `assumeBitsFlat` Simulation Proofs -/

private theorem resolveABArg_eq {Γ : List Ty} {vs : List ((t : Ty) × ABVal K t)}
    {inDepth : Nat} {inEnv : Trie ((t : Ty) × ABVal K t)}
    (hΓ : CtxTypes Γ vs) (hm : TrieCtxMatch inDepth inEnv vs)
    {t : Ty} (a : Arg K t) (hc : checkArg Γ t a = true) :
    denoteArg vs a = some (resolveABArg inDepth inEnv a) :=
  resolveArg_eq (fun _ => (.var ⟨.var 0, {}⟩ : Arg (ABVal K) _)) hΓ hm a hc

private theorem resolveABArgs_eq {Γ : List Ty} {vs : List ((t : Ty) × ABVal K t)}
    {inDepth : Nat} {inEnv : Trie ((t : Ty) × ABVal K t)}
    (hΓ : CtxTypes Γ vs) (hm : TrieCtxMatch inDepth inEnv vs) :
    {ts : List Ty} → (as : Tup (Arg K) ts) → checkArgs Γ as = true →
    denoteArgs vs as = some (resolveABArgs inDepth inEnv as) :=
  resolveArgs_eq (fun _ => (.var ⟨.var 0, {}⟩ : Arg (ABVal K) _)) hΓ hm

private theorem resolveAOuts_eq {inDepth outDepth : Nat} {inEnv : Trie ((t : Ty) × ABVal K t)} :
    {ts : List Ty} → (as : Tup (Arg K) ts) →
    idxArgs outDepth (tupAOut (resolveABArgs inDepth inEnv as)) =
      resolveAOuts inDepth outDepth inEnv as
  | [], () => rfl
  | _ :: _, (a, as) => by
    dsimp only [tupAOut, tupMapArg, idxArgs, resolveAOuts, resolveABArgs, resolveABArg]
    exact congrArg (_, ·) (resolveAOuts_eq as)

mutual
private theorem assumeBitsGo_eq {rs : List Ty} :
    (tf : TFlat rs) → {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × ABVal K t)} → {ls : List ((ts : List Ty) × KL ts)} →
    {inDepth : Nat} → {inEnv : Trie ((t : Ty) × ABVal K t)} →
    CtxTypes Γ vs → CtxTypes Δ ls → CtxLevels ls → TrieCtxMatch inDepth inEnv vs →
    tf.wfCheck Γ Δ = true →
    ∀ (outDepth : Nat) (F : List BitFact),
      assumeBitsGo inDepth outDepth F tf inEnv =
        toTFlat (assumeBits outDepth F (denote (ABVal K) KL tf vs ls)) outDepth ls.length
  | .let_ (ts := ts) op k, _, _, vs, ls, inDepth, inEnv, hΓ, hΔ, hll, hm, hwf, outDepth, F => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    simp only [assumeBitsGo, denote]
    rw [resolveABArgs_eq hΓ hm op.args hwf.1]
    simp only [assumeBits]
    cases hstep : ({ code := op.code, args := resolveABArgs inDepth inEnv op.args } :
        Op (ABVal K) ts).abLet F outDepth with
    | elim res =>
      dsimp only
      exact assumeBitsGo_eq k (ctxTypes_pushTup_rev res hΓ) hΔ hll
        (trieCtxMatch_insertTupEnv hm res) hwf.2 outDepth F
    | emit op' wrap =>
      simp only [toTFlat]
      have hk := assumeBitsGo_eq k
        (ctxTypes_pushTup_rev (wrap (Tup.levels ts outDepth)) hΓ) hΔ hll
        (trieCtxMatch_insertTupEnv hm (wrap (Tup.levels ts outDepth))) hwf.2
        (outDepth + ts.length) F
      exact congrArg (TFlat.let_ _) hk
  | .load t a k, _, _, vs, ls, inDepth, inEnv, hΓ, hΔ, hll, hm, hwf, outDepth, F => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [assumeBitsGo, denote]
    rw [resolveABArg_eq hΓ hm a hwf.1]
    dsimp only [assumeBits, toTFlat]
    have hk := assumeBitsGo_eq k (.cons hΓ) hΔ hll (hm.cons t (ABVal.fresh outDepth outDepth))
      hwf.2 (outDepth + 1) F
    rw [hk]
  | .store v a k, _, _, vs, ls, inDepth, inEnv, hΓ, hΔ, hll, hm, hwf, outDepth, F => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [assumeBitsGo, denote]
    rw [resolveABArg_eq hΓ hm v hwf.1.1, resolveABArg_eq hΓ hm a hwf.1.2]
    dsimp only [assumeBits, toTFlat]
    rw [assumeBitsGo_eq k hΓ hΔ hll hm hwf.2 outDepth F]
  | .call f bs args k, _, _, vs, ls, inDepth, inEnv, hΓ, hΔ, hll, hm, hwf, outDepth, F => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [assumeBitsGo, denote]
    rw [resolveABArgs_eq hΓ hm args hwf.1]
    dsimp only [assumeBits, toTFlat]
    rw [← resolveAOuts_eq args]
    have hk := assumeBitsGo_eq k
      (ctxTypes_pushTup_rev (freshABVals bs (Tup.levels bs outDepth) outDepth) hΓ) hΔ hll
      (by
        simpa only [mkFreshTup_abval] using
          trieCtxMatch_insertFreshWith (fun _ _ o => ABVal.fresh o o) hm bs outDepth)
      hwf.2 (outDepth + bs.length) F
    rw [hk]
  | .jnz c t e, _, _, vs, ls, inDepth, inEnv, hΓ, hΔ, hll, hm, hwf, outDepth, F => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [assumeBitsGo, denote]
    rw [resolveABArg_eq hΓ hm c hwf.1.1]
    dsimp only [assumeBits, toTFlat]
    rw [assumeBitsGo_eq t hΓ hΔ hll hm hwf.1.2 outDepth _,
      assumeBitsGo_eq e hΓ hΔ hll hm hwf.2 outDepth _]
  | .jump (ts := ts) j args, _, _, vs, ls, inDepth, inEnv, hΓ, hΔ, hll, hm, hwf, outDepth, _ => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨l', hlk, hinv⟩ := lookupL_wf_eq hΔ hll hwf.1
    dsimp only [assumeBitsGo, denote]
    rw [hlk, resolveABArgs_eq hΓ hm args hwf.2]
    dsimp only [assumeBits, toTFlat]
    rw [hinv, resolveAOuts_eq args]
  | .ret vs', _, _, vs, _, inDepth, inEnv, hΓ, _, _, hm, hwf, outDepth, _ => by
    dsimp only [assumeBitsGo, denote]
    rw [resolveABArgs_eq hΓ hm vs' hwf]
    dsimp only [assumeBits, toTFlat]
    rw [resolveAOuts_eq vs']
  | .exit f args, _, _, vs, _, inDepth, inEnv, hΓ, _, _, hm, hwf, outDepth, _ => by
    dsimp only [assumeBitsGo, denote]
    rw [resolveABArgs_eq hΓ hm args hwf]
    dsimp only [assumeBits, toTFlat]
    rw [resolveAOuts_eq args]
  | .hlt, _, _, _, _, _, _, _, _, _, _, _, _, _ => rfl
  | .group (sig := sig) bodies k, _, _, vs, ls, inDepth, inEnv, hΓ, hΔ, hll, hm, hwf,
      outDepth, F => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [assumeBitsGo, denote, assumeBits, toTFlat]
    have hb := assumeBitsBGo_eq bodies hΓ (CtxTypes.push (Tup.levels sig ls.length) hΔ)
      hll.pushTup hm hwf.1 outDepth F
    have hk := assumeBitsGo_eq k hΓ (CtxTypes.push (Tup.levels sig ls.length) hΔ)
      hll.pushTup hm hwf.2 outDepth F
    rw [pushTup_length] at hb hk
    rw [hb, hk]

private theorem assumeBitsBGo_eq {rs : List Ty} :
    {sig : List (List Ty)} → (tb : TBlocks rs sig) →
    {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × ABVal K t)} → {ls : List ((ts : List Ty) × KL ts)} →
    {inDepth : Nat} → {inEnv : Trie ((t : Ty) × ABVal K t)} →
    CtxTypes Γ vs → CtxTypes Δ ls → CtxLevels ls → TrieCtxMatch inDepth inEnv vs →
    tb.wfCheck Γ Δ = true →
    ∀ (outDepth : Nat) (F : List BitFact),
      assumeBitsBGo inDepth outDepth F tb inEnv =
        toTBlocks (assumeBitsB outDepth F (denoteB (ABVal K) KL tb vs ls)) outDepth ls.length
  | _, .nil, _, _, _, _, _, _, _, _, _, _, _, _, _ => rfl
  | _, .cons (ts := ts) b bs, _, _, vs, ls, inDepth, inEnv, hΓ, hΔ, hll, hm, hwf, outDepth, F => by
    dsimp only [TBlocks.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [assumeBitsBGo, denoteB, assumeBitsB, toTBlocks]
    have hb := assumeBitsGo_eq b
      (ctxTypes_pushTup_rev (freshABVals ts (Tup.levels ts outDepth) outDepth) hΓ) hΔ hll
      (by
        simpa only [mkFreshTup_abval] using
          trieCtxMatch_insertFreshWith (fun _ _ o => ABVal.fresh o o) hm ts outDepth)
      hwf.1 (outDepth + ts.length) F
    have hbs := assumeBitsBGo_eq bs hΓ hΔ hll hm hwf.2 outDepth F
    rw [hb, hbs]
end

/-- `assumeBitsFlat as tf = reifyFunc (Func.assumeBits (denoteFunc tf))` under `wfCheck = true`. -/
theorem assumeBitsFlat_eq {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    assumeBitsFlat as tf = reifyFunc (Func.assumeBits (denoteFunc (as := as) tf)) := by
  dsimp only [assumeBitsFlat, reifyFunc, Func.assumeBits, denoteFunc]
  have hm := trieCtxMatch_insertFreshWith (fun _ _ o => ABVal.fresh o o)
    (TrieCtxMatch.empty (f := ABVal K)) as 0
  rw [Nat.zero_add, mkFreshTup_abval] at hm
  have h := assumeBitsGo_eq tf
    (ctxTypes_pushTup_rev (freshABVals as (Tup.levels as 0) 0) .nil) .nil
    CtxLevels.nil hm hwf as.length []
  rw [List.length_nil] at h
  exact h

/-- `assumeBitsFlat` preserves `wfCheck`. -/
theorem assumeBitsFlat_wfCheck {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    (assumeBitsFlat as tf).wfCheck (pushTypes as []) [] = true := by
  rw [assumeBitsFlat_eq tf hwf]
  exact PassFlatKit.reifyFunc_wfCheck (Func.assumeBits_wf (Func.wf_of_denote tf rfl))

/-- `denoteFunc (assumeBitsFlat as tf) = Func.assumeBits (denoteFunc tf)` under `wfCheck`. -/
theorem denoteFunc_assumeBitsFlat {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    denoteFunc (as := as) (assumeBitsFlat as tf) = Func.assumeBits (denoteFunc (as := as) tf) := by
  rw [assumeBitsFlat_eq tf hwf]
  exact Func.renorm_eq_self (Func.assumeBits_wf (Func.wf_of_denote tf rfl))

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
  | t :: _, (x, xs), vs => by
    dsimp only [toArgTup, pushTup]
    exact liftEnv_pushTup xs (⟨t, x⟩ :: vs)

private theorem flattenArg_varLift {V : Ty → Type} {t : Ty} (a : Arg V t) :
    flattenArg (varLiftArg a) = a := by
  cases a <;> rfl

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

mutual
private theorem denote_divConst_eq_of_noDivRem {V : Ty → Type} {L : List Ty → Type}
    {rs : List Ty} :
    (tf : TFlat rs) → {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × V t)} → {ls : List ((ts : List Ty) × L ts)} →
    CtxTypes Γ vs → CtxTypes Δ ls → tf.wfCheck Γ Δ = true → hasDivRem tf = false →
    LeanQbe.T.divConst (denote (Arg V) L tf (liftEnv vs) ls) = denote V L tf vs ls
  | .let_ op k, _, _, vs, ls, hΓ, hΔ, hwf, hdiv => by
    dsimp only [TFlat.wfCheck, hasDivRem] at hwf hdiv
    simp only [Bool.and_eq_true, Bool.or_eq_false_iff] at hwf hdiv
    obtain ⟨args', hda1, hda2⟩ := denoteArgs_liftEnv hΓ op.args hwf.1
    dsimp only [denote, LeanQbe.T.divConst]
    rw [hda1, hda2]; dsimp only [LeanQbe.T.divConst]
    rw [divConstOp_eq_fallback ⟨op.code, varLiftArgs args'⟩ hdiv.1]
    have hfl : flattenOp ⟨op.code, varLiftArgs args'⟩ = ⟨op.code, args'⟩ := by
      dsimp only [flattenOp]; rw [flattenArgs_varLift]
    rw [hfl]
    refine congrArg (Expr.let_ _) (funext fun xs => ?_)
    rw [liftEnv_pushTup]
    exact denote_divConst_eq_of_noDivRem k (ctxTypes_pushTup_rev xs hΓ) hΔ hwf.2 hdiv.2
  | .load t a k, _, _, vs, ls, hΓ, hΔ, hwf, hdiv => by
    dsimp only [TFlat.wfCheck, hasDivRem] at hwf hdiv
    simp only [Bool.and_eq_true] at hwf
    obtain ⟨a', hda1, hda2⟩ := denoteArg_liftEnv hΓ a hwf.1
    dsimp only [denote, LeanQbe.T.divConst]
    rw [hda1, hda2]; dsimp only [LeanQbe.T.divConst]
    rw [flattenArg_varLift]
    refine congrArg (Expr.load t a') (funext fun v => ?_)
    change LeanQbe.T.divConst (denote (Arg V) L k (liftEnv (⟨t, v⟩ :: vs)) ls) =
      denote V L k (⟨t, v⟩ :: vs) ls
    exact denote_divConst_eq_of_noDivRem k (.cons hΓ) hΔ hwf.2 hdiv
  | .store v a k, _, _, vs, ls, hΓ, hΔ, hwf, hdiv => by
    dsimp only [TFlat.wfCheck, hasDivRem] at hwf hdiv
    simp only [Bool.and_eq_true] at hwf
    obtain ⟨v', hdv1, hdv2⟩ := denoteArg_liftEnv hΓ v hwf.1.1
    obtain ⟨a', hda1, hda2⟩ := denoteArg_liftEnv hΓ a hwf.1.2
    dsimp only [denote, LeanQbe.T.divConst]
    rw [hdv1, hdv2, hda1, hda2]; dsimp only [LeanQbe.T.divConst]
    rw [flattenArg_varLift, flattenArg_varLift]
    exact congrArg (Expr.store v' a') (denote_divConst_eq_of_noDivRem k hΓ hΔ hwf.2 hdiv)
  | .call f bs args k, _, _, vs, ls, hΓ, hΔ, hwf, hdiv => by
    dsimp only [TFlat.wfCheck, hasDivRem] at hwf hdiv
    simp only [Bool.and_eq_true] at hwf
    obtain ⟨args', hda1, hda2⟩ := denoteArgs_liftEnv hΓ args hwf.1
    dsimp only [denote, LeanQbe.T.divConst]
    rw [hda1, hda2]; dsimp only [LeanQbe.T.divConst]
    rw [flattenArgs_varLift]
    refine congrArg (Expr.call f args') (funext fun xs => ?_)
    rw [liftEnv_pushTup]
    exact denote_divConst_eq_of_noDivRem k (ctxTypes_pushTup_rev xs hΓ) hΔ hwf.2 hdiv
  | .jnz c t e, _, _, vs, ls, hΓ, hΔ, hwf, hdiv => by
    dsimp only [TFlat.wfCheck, hasDivRem] at hwf hdiv
    simp only [Bool.and_eq_true, Bool.or_eq_false_iff] at hwf hdiv
    obtain ⟨c', hdc1, hdc2⟩ := denoteArg_liftEnv hΓ c hwf.1.1
    dsimp only [denote, LeanQbe.T.divConst]
    rw [hdc1, hdc2]; dsimp only [LeanQbe.T.divConst]
    rw [flattenArg_varLift]
    rw [denote_divConst_eq_of_noDivRem t hΓ hΔ hwf.1.2 hdiv.1,
      denote_divConst_eq_of_noDivRem e hΓ hΔ hwf.2 hdiv.2]
  | .jump (ts := ts) j args, _, _, vs, ls, hΓ, hΔ, hwf, _ => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨j', hj⟩ := Option.isSome_iff_exists.1 (lookupL_isSome_of_check hΔ hwf.1)
    obtain ⟨args', hda1, hda2⟩ := denoteArgs_liftEnv hΓ args hwf.2
    dsimp only [denote, LeanQbe.T.divConst]
    rw [hj, hda1, hda2]; dsimp only [LeanQbe.T.divConst]
    rw [flattenArgs_varLift]
  | .ret vs', _, _, vs, _, hΓ, _, hwf, _ => by
    obtain ⟨vs'', hdv1, hdv2⟩ := denoteArgs_liftEnv hΓ vs' hwf
    dsimp only [denote, LeanQbe.T.divConst]
    rw [hdv1, hdv2]; dsimp only [LeanQbe.T.divConst]
    rw [flattenArgs_varLift]
  | .exit f args, _, _, vs, _, hΓ, _, hwf, _ => by
    obtain ⟨args', hda1, hda2⟩ := denoteArgs_liftEnv hΓ args hwf
    dsimp only [denote, LeanQbe.T.divConst]
    rw [hda1, hda2]; dsimp only [LeanQbe.T.divConst]
    rw [flattenArgs_varLift]
  | .hlt, _, _, _, _, _, _, _, _ => rfl
  | .group bodies k, _, _, vs, ls, hΓ, hΔ, hwf, hdiv => by
    dsimp only [TFlat.wfCheck, hasDivRem] at hwf hdiv
    simp only [Bool.and_eq_true, Bool.or_eq_false_iff] at hwf hdiv
    dsimp only [denote, LeanQbe.T.divConst]
    refine congr (congrArg Expr.group (funext fun Js => ?_)) (funext fun Js => ?_)
    · exact denoteB_divConst_eq_of_noDivRem bodies hΓ (ctxTypes_pushTup_rev Js hΔ) hwf.1 hdiv.1
    · exact denote_divConst_eq_of_noDivRem k hΓ (ctxTypes_pushTup_rev Js hΔ) hwf.2 hdiv.2

private theorem denoteB_divConst_eq_of_noDivRem {V : Ty → Type} {L : List Ty → Type}
    {rs : List Ty} :
    {sig : List (List Ty)} → (tb : TBlocks rs sig) →
    {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × V t)} → {ls : List ((ts : List Ty) × L ts)} →
    CtxTypes Γ vs → CtxTypes Δ ls → tb.wfCheck Γ Δ = true → hasDivRemB tb = false →
    divConstB (denoteB (Arg V) L tb (liftEnv vs) ls) = denoteB V L tb vs ls
  | _, .nil, _, _, _, _, _, _, _, _ => rfl
  | _, .cons b bs, _, _, vs, ls, hΓ, hΔ, hwf, hdiv => by
    dsimp only [TBlocks.wfCheck, hasDivRemB] at hwf hdiv
    simp only [Bool.and_eq_true, Bool.or_eq_false_iff] at hwf hdiv
    dsimp only [denoteB, divConstB]
    refine congr (congrArg Blocks.cons (funext fun xs => ?_))
      (denoteB_divConst_eq_of_noDivRem bs hΓ hΔ hwf.2 hdiv.2)
    rw [liftEnv_pushTup]
    exact denote_divConst_eq_of_noDivRem b (ctxTypes_pushTup_rev xs hΓ) hΔ hwf.1 hdiv.1
end

private theorem emitUDivConstPlan_eq {rs : List Ty}
    (n : Nat) (x : Arg K (.bits n)) (d : BitVec n) (outD nl : Nat)
    (k₁ : Arg K (.bits n) → Expr K KL rs) :
    match emitUDivConstPlan n x d outD with
    | some p => ∃ e, emitUDivConst n x d k₁ = some e ∧
        toTFlat e outD nl = p.wrap (toTFlat (k₁ p.res) p.outDepth nl)
    | none => emitUDivConst n x d k₁ = none := by
  dsimp only [emitUDivConstPlan, emitUDivConst]
  by_cases h1 : (!(n == 32 || n == 64)) = true
  · simp only [h1, ↓reduceIte]
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    by_cases h2 : (d == 0#n) = true
    · simp only [h2, ↓reduceIte]
    · simp only [h2, Bool.false_eq_true, ↓reduceIte]
      by_cases h3 : (d == 1#n) = true
      · simp only [h3, ↓reduceIte]; exact ⟨k₁ x, rfl, rfl⟩
      · simp only [h3, Bool.false_eq_true, ↓reduceIte]
        cases findPow2Shift n d with
        | some m =>
          dsimp only
          by_cases hc : pow2ShiftCert n d m = true <;>
            simp only [hc, ↓reduceIte, Bool.false_eq_true]
          exact ⟨_, rfl, rfl⟩
        | none =>
          dsimp only
          cases findUMagic n d with
          | none => rfl
          | some val =>
            rcases val with ⟨M, s, addShift⟩
            cases addShift <;> dsimp only
            · by_cases hc : uNoAddCert n d M s = true <;>
                simp only [hc, ↓reduceIte, Bool.false_eq_true]
              exact ⟨_, rfl, rfl⟩
            · by_cases hc : uAddShiftCert n d M s = true <;>
                simp only [hc, ↓reduceIte, Bool.false_eq_true]
              exact ⟨_, rfl, rfl⟩

private theorem emitURemConstPlan_eq {rs : List Ty}
    (n : Nat) (x : Arg K (.bits n)) (d : BitVec n) (outD nl : Nat)
    (k₁ : Arg K (.bits n) → Expr K KL rs) :
    match emitURemConstPlan n x d outD with
    | some p => ∃ e, emitURemConst n x d k₁ = some e ∧
        toTFlat e outD nl = p.wrap (toTFlat (k₁ p.res) p.outDepth nl)
    | none => emitURemConst n x d k₁ = none := by
  dsimp only [emitURemConstPlan, emitURemConst]
  by_cases h1 : (!(n == 32 || n == 64)) = true
  · simp only [h1, ↓reduceIte]
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    by_cases h2 : (d == 0#n) = true
    · simp only [h2, ↓reduceIte]
    · simp only [h2, Bool.false_eq_true, ↓reduceIte]
      by_cases h3 : (d == 1#n) = true
      · simp only [h3, ↓reduceIte]; exact ⟨k₁ (.imm 0#n), rfl, rfl⟩
      · simp only [h3, Bool.false_eq_true, ↓reduceIte]
        cases findPow2Shift n d with
        | some m =>
          dsimp only
          by_cases hc : pow2ShiftCert n d m = true <;>
            simp only [hc, ↓reduceIte, Bool.false_eq_true]
          exact ⟨_, rfl, rfl⟩
        | none =>
          dsimp only
          let kSub : Arg K (.bits n) → Expr K KL rs := fun q =>
            .let_ (op2 (.mul (.bits n)) q (.imm d)) fun (p, ()) =>
            .let_ (op2 (.sub (.bits n)) x (.var p)) fun (r, ()) =>
            k₁ (.var r)
          have hu := emitUDivConstPlan_eq n x d outD nl kSub
          cases hplan : emitUDivConstPlan n x d outD with
          | none => rw [hplan] at hu; exact hu
          | some p =>
            rw [hplan] at hu
            obtain ⟨e, he, htf⟩ := hu
            refine ⟨e, he, ?_⟩
            simpa only [DivEmit.seq, emitOp2E, kSub, toTFlat, idxArgs, Tup.levels,
              op2, List.length_cons, List.length_nil] using htf

private theorem emitSDivConstPlan_eq {rs : List Ty}
    (n : Nat) (x : Arg K (.bits n)) (d : BitVec n) (outD nl : Nat)
    (k₁ : Arg K (.bits n) → Expr K KL rs) :
    match emitSDivConstPlan n x d outD with
    | some p => ∃ e, emitSDivConst n x d k₁ = some e ∧
        toTFlat e outD nl = p.wrap (toTFlat (k₁ p.res) p.outDepth nl)
    | none => emitSDivConst n x d k₁ = none := by
  dsimp only [emitSDivConstPlan, emitSDivConst]
  by_cases h1 : (!(n == 32 || n == 64)) = true
  · simp only [h1, ↓reduceIte]
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    by_cases h2 : (d == 0#n || d == BitVec.allOnes n) = true
    · simp only [h2, ↓reduceIte]
    · simp only [h2, Bool.false_eq_true, ↓reduceIte]
      by_cases h3 : (d == 1#n) = true
      · simp only [h3, ↓reduceIte]; exact ⟨k₁ x, rfl, rfl⟩
      · simp only [h3, Bool.false_eq_true, ↓reduceIte]
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
            rcases val with ⟨A, s⟩
            dsimp only
            by_cases hc : sDivCert n d A s = true
            · simp only [hc, ↓reduceIte]
              let m : BitVec n := BitVec.ofInt n (if 0 < d.toInt then (A : Int) else -(A : Int))
              by_cases hs0 : (s == 0) = true <;>
                by_cases hc1 : (0 < d.toInt && m.toInt < 0) = true <;>
                by_cases hc2 : (d.toInt < 0 && 0 < m.toInt) = true <;>
                simp only [m, hs0, hc1, hc2, ↓reduceIte, Bool.false_eq_true] <;>
                exact ⟨_, rfl, rfl⟩
            · simp only [hc, Bool.false_eq_true, ↓reduceIte]

private theorem emitSRemConstPlan_eq {rs : List Ty}
    (n : Nat) (x : Arg K (.bits n)) (d : BitVec n) (outD nl : Nat)
    (k₁ : Arg K (.bits n) → Expr K KL rs) :
    match emitSRemConstPlan n x d outD with
    | some p => ∃ e, emitSRemConst n x d k₁ = some e ∧
        toTFlat e outD nl = p.wrap (toTFlat (k₁ p.res) p.outDepth nl)
    | none => emitSRemConst n x d k₁ = none := by
  dsimp only [emitSRemConstPlan, emitSRemConst]
  by_cases h1 : (!(n == 32 || n == 64)) = true
  · simp only [h1, ↓reduceIte]
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    by_cases h2 : (d == 0#n || d == BitVec.allOnes n) = true
    · simp only [h2, ↓reduceIte]
    · simp only [h2, Bool.false_eq_true, ↓reduceIte]
      by_cases h3 : (d == 1#n) = true
      · simp only [h3, ↓reduceIte]; exact ⟨k₁ (.imm 0#n), rfl, rfl⟩
      · simp only [h3, Bool.false_eq_true, ↓reduceIte]
        let kSub : Arg K (.bits n) → Expr K KL rs := fun q =>
          .let_ (op2 (.mul (.bits n)) q (.imm d)) fun (p, ()) =>
          .let_ (op2 (.sub (.bits n)) x (.var p)) fun (r, ()) =>
          k₁ (.var r)
        have hs := emitSDivConstPlan_eq n x d outD nl kSub
        cases hplan : emitSDivConstPlan n x d outD with
        | none => rw [hplan] at hs; exact hs
        | some p =>
          rw [hplan] at hs
          obtain ⟨e, he, htf⟩ := hs
          refine ⟨e, he, ?_⟩
          simpa only [DivEmit.seq, emitOp2E, kSub, toTFlat, idxArgs, Tup.levels,
            op2, List.length_cons, List.length_nil] using htf

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
      dsimp only [flattenArgs, tupMapArg]
      cases hb : flattenArg b with
      | var _ => dsimp only [divConstEmit]; rfl
      | imm d =>
        dsimp only [divConstEmit]
        have hu := emitUDivConstPlan_eq n (flattenArg a) d outD nl (fun res => k₁ (res, ()))
        cases hpl : emitUDivConstPlan n (flattenArg a) d outD with
        | none => rw [hpl] at hu; rw [hu]; rfl
        | some p =>
          rw [hpl] at hu; obtain ⟨e, he, htf⟩ := hu
          rw [he]; exact htf
    | urem n =>
      rcases args with ⟨a, b, ⟨⟩⟩
      dsimp only [flattenArgs, tupMapArg]
      cases hb : flattenArg b with
      | var _ => dsimp only [divConstEmit]; rfl
      | imm d =>
        dsimp only [divConstEmit]
        have hu := emitURemConstPlan_eq n (flattenArg a) d outD nl (fun res => k₁ (res, ()))
        cases hpl : emitURemConstPlan n (flattenArg a) d outD with
        | none => rw [hpl] at hu; rw [hu]; rfl
        | some p =>
          rw [hpl] at hu; obtain ⟨e, he, htf⟩ := hu
          rw [he]; exact htf
    | sdiv n =>
      rcases args with ⟨a, b, ⟨⟩⟩
      dsimp only [flattenArgs, tupMapArg]
      cases hb : flattenArg b with
      | var _ => dsimp only [divConstEmit]; rfl
      | imm d =>
        dsimp only [divConstEmit]
        have hs := emitSDivConstPlan_eq n (flattenArg a) d outD nl (fun res => k₁ (res, ()))
        cases hpl : emitSDivConstPlan n (flattenArg a) d outD with
        | none => rw [hpl] at hs; rw [hs]; rfl
        | some p =>
          rw [hpl] at hs; obtain ⟨e, he, htf⟩ := hs
          rw [he]; exact htf
    | srem n =>
      rcases args with ⟨a, b, ⟨⟩⟩
      dsimp only [flattenArgs, tupMapArg]
      cases hb : flattenArg b with
      | var _ => dsimp only [divConstEmit]; rfl
      | imm d =>
        dsimp only [divConstEmit]
        have hs := emitSRemConstPlan_eq n (flattenArg a) d outD nl (fun res => k₁ (res, ()))
        cases hpl : emitSRemConstPlan n (flattenArg a) d outD with
        | none => rw [hpl] at hs; rw [hs]; rfl
        | some p =>
          rw [hpl] at hs; obtain ⟨e, he, htf⟩ := hs
          rw [he]; exact htf
    | _ => rfl

private theorem resolveFlatArg_eq {Γ : List Ty} {vs : List ((t : Ty) × Arg K t)}
    {inDepth : Nat} {inEnv : Trie ((t : Ty) × Arg K t)}
    (hΓ : CtxTypes Γ vs) (hm : TrieCtxMatch inDepth inEnv vs)
    {t : Ty} (a : Arg K t) (hc : checkArg Γ t a = true) :
    ∃ a', denoteArg vs a = some a' ∧ flattenArg a' = resolveFlatArg inDepth inEnv a := by
  cases a with
  | imm c => exact ⟨.imm c, rfl, rfl⟩
  | var idx =>
    obtain ⟨v, hget, _⟩ := ctxTypes_listGet? hΓ (checkArg_eq_true_iff.mp hc)
    have hlk : lookupV vs t idx = some v := by
      dsimp only [lookupV]; rw [hget]; dsimp only; exact PassFlatKit.castTy_self t v
    have henv : lookupEnv inDepth inEnv t idx = some v := (lookupEnv_eq hΓ hm hc).trans hlk
    refine ⟨.var v, ?_, ?_⟩
    · dsimp only [denoteArg]; rw [hlk]
    · dsimp only [resolveFlatArg]; rw [henv]; rfl

private theorem resolveFlatArgs_eq {Γ : List Ty} {vs : List ((t : Ty) × Arg K t)}
    {inDepth : Nat} {inEnv : Trie ((t : Ty) × Arg K t)}
    (hΓ : CtxTypes Γ vs) (hm : TrieCtxMatch inDepth inEnv vs) :
    {ts : List Ty} → (as : Tup (Arg K) ts) → checkArgs Γ as = true →
    ∃ as', denoteArgs vs as = some as' ∧ flattenArgs as' = resolveFlatArgs inDepth inEnv as
  | [], (), _ => ⟨(), rfl, rfl⟩
  | _ :: _, (a, as), hc => by
    dsimp only [checkArgs] at hc; simp only [Bool.and_eq_true] at hc
    obtain ⟨a', ha, hfa⟩ := resolveFlatArg_eq hΓ hm a hc.1
    obtain ⟨as', has, hfas⟩ := resolveFlatArgs_eq hΓ hm as hc.2
    refine ⟨(a', as'), ?_, ?_⟩
    · dsimp only [denoteArgs]; rw [ha, has]
    · dsimp only [flattenArgs, tupMapArg] at hfas ⊢; dsimp only [resolveFlatArgs]; rw [hfa, hfas]

mutual
private theorem divConstGo_eq {rs : List Ty} :
    (tf : TFlat rs) → {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × Arg K t)} → {ls : List ((ts : List Ty) × KL ts)} →
    {inDepth : Nat} → {inEnv : Trie ((t : Ty) × Arg K t)} →
    CtxTypes Γ vs → CtxTypes Δ ls → CtxLevels ls → TrieCtxMatch inDepth inEnv vs →
    tf.wfCheck Γ Δ = true →
    ∀ (outDepth : Nat),
      divConstGo inDepth outDepth tf inEnv =
        toTFlat (LeanQbe.T.divConst (denote (Arg K) KL tf vs ls)) outDepth ls.length
  | .let_ (ts := ts) op k, _, _, vs, ls, inDepth, inEnv, hΓ, hΔ, hll, hm, hwf, outDepth => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨args', hda, hflat⟩ := resolveFlatArgs_eq hΓ hm op.args hwf.1
    dsimp only [divConstGo, denote]
    rw [hda]
    dsimp only [LeanQbe.T.divConst]
    have hop := toTFlat_divConstOp_eq ⟨op.code, args'⟩
      (fun res => LeanQbe.T.divConst (denote (Arg K) KL k (pushTup res vs) ls)) outDepth ls.length
    rw [hflat] at hop
    cases hce : divConstEmit op.code (resolveFlatArgs inDepth inEnv op.args) outDepth with
    | some p =>
      rw [hce] at hop
      dsimp only
      rw [hop]
      have hk := divConstGo_eq k (ctxTypes_pushTup_rev p.res hΓ) hΔ hll
        (trieCtxMatch_insertTupEnv hm p.res) hwf.2 p.outDepth
      exact congrArg p.wrap hk
    | none =>
      rw [hce] at hop
      dsimp only
      rw [hop]
      have hk := divConstGo_eq k (ctxTypes_pushTup_rev (toArgTup (Tup.levels ts outDepth)) hΓ)
        hΔ hll
        (by
          simpa only [mkFreshTup_arg] using
            trieCtxMatch_insertFreshWith (fun _ _ o => (.var o : Arg K _)) hm ts outDepth)
        hwf.2 (outDepth + ts.length)
      exact congrArg (TFlat.let_ _) hk
  | .load t a k, _, _, vs, ls, inDepth, inEnv, hΓ, hΔ, hll, hm, hwf, outDepth => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨a', hda, hflat⟩ := resolveFlatArg_eq hΓ hm a hwf.1
    dsimp only [divConstGo, denote]
    rw [hda]
    dsimp only [LeanQbe.T.divConst, toTFlat]
    rw [hflat]
    have hk := divConstGo_eq k (.cons hΓ) hΔ hll (hm.cons t (.var outDepth)) hwf.2 (outDepth + 1)
    exact congrArg (TFlat.load t (idxArg outDepth (resolveFlatArg inDepth inEnv a))) hk
  | .store v a k, _, _, vs, ls, inDepth, inEnv, hΓ, hΔ, hll, hm, hwf, outDepth => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨v', hdv, hfv⟩ := resolveFlatArg_eq hΓ hm v hwf.1.1
    obtain ⟨a', hda, hfa⟩ := resolveFlatArg_eq hΓ hm a hwf.1.2
    dsimp only [divConstGo, denote]
    rw [hdv, hda]
    dsimp only [LeanQbe.T.divConst, toTFlat]
    rw [hfv, hfa, divConstGo_eq k hΓ hΔ hll hm hwf.2 outDepth]
  | .call f bs args k, _, _, vs, ls, inDepth, inEnv, hΓ, hΔ, hll, hm, hwf, outDepth => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨args', hda, hflat⟩ := resolveFlatArgs_eq hΓ hm args hwf.1
    dsimp only [divConstGo, denote]
    rw [hda]
    dsimp only [LeanQbe.T.divConst, toTFlat]
    rw [hflat]
    have hk := divConstGo_eq k (ctxTypes_pushTup_rev (toArgTup (Tup.levels bs outDepth)) hΓ)
      hΔ hll
      (by
        simpa only [mkFreshTup_arg] using
          trieCtxMatch_insertFreshWith (fun _ _ o => (.var o : Arg K _)) hm bs outDepth)
      hwf.2 (outDepth + bs.length)
    exact congrArg (TFlat.call f bs (idxArgs outDepth (resolveFlatArgs inDepth inEnv args))) hk
  | .jnz c t e, _, _, vs, ls, inDepth, inEnv, hΓ, hΔ, hll, hm, hwf, outDepth => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨c', hdc, hfc⟩ := resolveFlatArg_eq hΓ hm c hwf.1.1
    dsimp only [divConstGo, denote]
    rw [hdc]
    dsimp only [LeanQbe.T.divConst, toTFlat]
    rw [hfc, divConstGo_eq t hΓ hΔ hll hm hwf.1.2 outDepth,
      divConstGo_eq e hΓ hΔ hll hm hwf.2 outDepth]
  | .jump (ts := ts) j args, _, _, vs, ls, inDepth, inEnv, hΓ, hΔ, hll, hm, hwf, outDepth => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨l', hlk, hinv⟩ := lookupL_wf_eq hΔ hll hwf.1
    obtain ⟨args', hda, hflat⟩ := resolveFlatArgs_eq hΓ hm args hwf.2
    dsimp only [divConstGo, denote]
    rw [hlk, hda]
    dsimp only [LeanQbe.T.divConst, toTFlat]
    rw [hinv, hflat]
  | .ret vs', _, _, vs, _, inDepth, inEnv, hΓ, _, _, hm, hwf, outDepth => by
    obtain ⟨vs'', hdv, hflat⟩ := resolveFlatArgs_eq hΓ hm vs' hwf
    dsimp only [divConstGo, denote]
    rw [hdv]
    dsimp only [LeanQbe.T.divConst, toTFlat]
    rw [hflat]
  | .exit f args, _, _, vs, _, inDepth, inEnv, hΓ, _, _, hm, hwf, outDepth => by
    obtain ⟨args', hda, hflat⟩ := resolveFlatArgs_eq hΓ hm args hwf
    dsimp only [divConstGo, denote]
    rw [hda]
    dsimp only [LeanQbe.T.divConst, toTFlat]
    rw [hflat]
  | .hlt, _, _, _, _, _, _, _, _, _, _, _, _ => rfl
  | .group (sig := sig) bodies k, _, _, vs, ls, inDepth, inEnv, hΓ, hΔ, hll, hm, hwf, outDepth => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [divConstGo, denote, LeanQbe.T.divConst, toTFlat]
    have hb := divConstBGo_eq bodies hΓ (CtxTypes.push (Tup.levels sig ls.length) hΔ)
      hll.pushTup hm hwf.1 outDepth
    have hk := divConstGo_eq k hΓ (CtxTypes.push (Tup.levels sig ls.length) hΔ)
      hll.pushTup hm hwf.2 outDepth
    rw [pushTup_length] at hb hk
    rw [hb, hk]

private theorem divConstBGo_eq {rs : List Ty} :
    {sig : List (List Ty)} → (tb : TBlocks rs sig) →
    {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × Arg K t)} → {ls : List ((ts : List Ty) × KL ts)} →
    {inDepth : Nat} → {inEnv : Trie ((t : Ty) × Arg K t)} →
    CtxTypes Γ vs → CtxTypes Δ ls → CtxLevels ls → TrieCtxMatch inDepth inEnv vs →
    tb.wfCheck Γ Δ = true →
    ∀ (outDepth : Nat),
      divConstBGo inDepth outDepth tb inEnv =
        toTBlocks (divConstB (denoteB (Arg K) KL tb vs ls)) outDepth ls.length
  | _, .nil, _, _, _, _, _, _, _, _, _, _, _, _ => rfl
  | _, .cons (ts := ts) b bs, _, _, vs, ls, inDepth, inEnv, hΓ, hΔ, hll, hm, hwf, outDepth => by
    dsimp only [TBlocks.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [divConstBGo, denoteB, divConstB, toTBlocks]
    have hb := divConstGo_eq b (ctxTypes_pushTup_rev (toArgTup (Tup.levels ts outDepth)) hΓ)
      hΔ hll
      (by
        simpa only [mkFreshTup_arg] using
          trieCtxMatch_insertFreshWith (fun _ _ o => (.var o : Arg K _)) hm ts outDepth)
      hwf.1 (outDepth + ts.length)
    have hbs := divConstBGo_eq bs hΓ hΔ hll hm hwf.2 outDepth
    rw [hb, hbs]
end

/-- `divConstFlat as tf = reifyFunc (Func.divConst (denoteFunc tf))` under `wfCheck = true`. -/
theorem divConstFlat_eq {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    divConstFlat as tf = reifyFunc (Func.divConst (denoteFunc (as := as) tf)) := by
  dsimp only [divConstFlat]
  by_cases hd : hasDivRem tf = true
  · simp only [hd, ↓reduceIte, reifyFunc, Func.divConst, denoteFunc]
    have hm := trieCtxMatch_insertFreshWith (fun _ _ o => (.var o : Arg K _))
      (TrieCtxMatch.empty (f := Arg K)) as 0
    rw [Nat.zero_add, mkFreshTup_arg] at hm
    have h := divConstGo_eq tf
      (ctxTypes_pushTup_rev (toArgTup (Tup.levels as 0)) .nil) .nil
      CtxLevels.nil hm hwf as.length
    rw [List.length_nil] at h
    exact h
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

/-- `divConstFlat` preserves `wfCheck`. -/
theorem divConstFlat_wfCheck {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    (divConstFlat as tf).wfCheck (pushTypes as []) [] = true := by
  rw [divConstFlat_eq tf hwf]
  exact PassFlatKit.reifyFunc_wfCheck (Func.divConst_wf (Func.wf_of_denote tf rfl))

/-- `denoteFunc (divConstFlat as tf) = Func.divConst (denoteFunc tf)` under `wfCheck = true`. -/
theorem denoteFunc_divConstFlat {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    denoteFunc (as := as) (divConstFlat as tf) = Func.divConst (denoteFunc (as := as) tf) := by
  rw [divConstFlat_eq tf hwf]
  exact Func.renorm_eq_self (Func.divConst_wf (Func.wf_of_denote tf rfl))

/-! ## 4. `TFlatFn` Compatibility Helpers -/

/-- `reifyFunc (Func.memLoad f.toFn.body) = memLoadFlat f.as f.body` under `f.wfCheck`. -/
theorem memLoadFlat_toFn (f : TFlatFn) (hwf : f.wfCheck = true) :
    reifyFunc (Func.memLoad f.toFn.body) = memLoadFlat f.as f.body :=
  (memLoadFlat_eq f.body hwf).symm

/-- `reifyFunc (Func.assumeBits f.toFn.body) = assumeBitsFlat f.as f.body` under `f.wfCheck`. -/
theorem assumeBitsFlat_toFn (f : TFlatFn) (hwf : f.wfCheck = true) :
    reifyFunc (Func.assumeBits f.toFn.body) = assumeBitsFlat f.as f.body :=
  (assumeBitsFlat_eq f.body hwf).symm

/-- `reifyFunc (Func.divConst f.toFn.body) = divConstFlat f.as f.body` under `f.wfCheck`. -/
theorem divConstFlat_toFn (f : TFlatFn) (hwf : f.wfCheck = true) :
    reifyFunc (Func.divConst f.toFn.body) = divConstFlat f.as f.body :=
  (divConstFlat_eq f.body hwf).symm

end OptFlatMem
end LeanQbe.T
