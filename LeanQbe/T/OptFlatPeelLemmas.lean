module

public import LeanQbe.T.OptFlatPeel
import LeanQbe.T.FlatDirectLemmas
import LeanQbe.T.PassFlatKit
import LeanQbe.T.OptFlatSimKit
import LeanQbe.T.PeelLemmas

/-!
# Bounded Loop Peeling Equivalence Proofs (`OptFlatPeelLemmas`)

Proves exact `=` correspondence (`std3` axioms only) between the native `TFlat` pass
`OptFlatPeel.peelFlat` and `Func.peel`:

* `OptFlatPeel.peelFlat_eq`
* `OptFlatPeel.denoteFunc_peelFlat`
* `OptFlatPeel.peelFlat_wfCheck`
* `OptFlatPeel.peelFlatFn_toFn` / `OptFlatPeel.peelFlatFn_wfCheck`
-/

set_option autoImplicit false

public section

namespace LeanQbe.T
namespace OptFlatPeel

open OptFlatPlanKit
open OptFlatSimKit
open Peel

/-! ## 1. Label Match Relation and `peelMetricsFlat` Equivalence -/

/-- Simulation relation linking `PeelLFlat` payloads to PHOAS `Peel.PeelL K KL`. -/
private def PeelLFlatMatch {rs ts : List Ty} : PeelLFlat rs ts → PeelL K KL rs ts → Prop
  | .outer l₁, .outer l₂ => l₁ = l₂
  | .subst id₁ f₁, .subst id₂ f₂ =>
    id₁ = id₂ ∧ ∀ ovd old args, f₁ ovd old args = toTFlat (f₂ args) ovd old
  | .probe id₁, .probe id₂ => id₁ = id₂
  | _, _ => False

private theorem toOuterTupFlat_match {rs : List Ty} :
    {sig : List (List Ty)} → (ls : Tup KL sig) →
    TRel (fun _ => PeelLFlatMatch (rs := rs)) (toOuterTupFlat ls) (toOuterTup ls)
  | [], () => .nil
  | _ :: _, (_, ls) => .cons rfl (toOuterTupFlat_match ls)

private theorem probeTupFlat_match {rs : List Ty} :
    (sig : List (List Ty)) → (n : Nat) →
    TRel (fun _ => PeelLFlatMatch (rs := rs)) (probeTupFlat sig n) (probeTup sig n)
  | [], _ => .nil
  | _ :: sig, n => .cons rfl (probeTupFlat_match sig (n + 1))

private theorem denoteArg_ex {V : Ty → Type} {Γ vs} (hΓ : CtxTypes Γ vs)
    {t : Ty} {a : Arg K t} (hc : checkArg Γ t a = true) :
    ∃ a' : Arg V t, denoteArg vs a = some a' :=
  Option.isSome_iff_exists.1 (denoteArg_isSome_of_checkArg hΓ hc)

private theorem denoteArgs_ex {V : Ty → Type} {Γ vs} (hΓ : CtxTypes Γ vs)
    {ts : List Ty} {args : Tup (Arg K) ts} (hc : checkArgs Γ args = true) :
    ∃ args' : Tup (Arg V) ts, denoteArgs vs args = some args' :=
  Option.isSome_iff_exists.1 (denoteArgs_isSome_of_checkArgs hΓ hc)

mutual
private theorem peelMetricsFlat_eq {rs : List Ty} :
    (tf : TFlat rs) → {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × Arg K t)} → {ls : List ((ts : List Ty) × PeelL K KL rs ts)} →
    {inLD : Nat} → {inLE : Trie ((ts : List Ty) × PeelLFlat rs ts)} →
    (targetId nextId : Nat) →
    CtxTypes Γ vs → CtxTypes Δ ls →
    TrieRelMatch (fun _ => PeelLFlatMatch (rs := rs)) inLD inLE ls →
    tf.wfCheck Γ Δ = true →
    peelMetricsFlat targetId nextId inLD inLE tf =
      peelMetrics targetId nextId (denote (Arg K) (PeelL K KL rs) tf vs ls)
  | .let_ (ts := ts) _ k, _, _, _, _, _, _, _, _, hΓ, hΔ, hmL, hwf => by
    have ⟨ha, hk⟩ := wf_let hwf
    obtain ⟨_, ha'⟩ := denoteArgs_ex (V := Arg K) hΓ ha
    dsimp only [peelMetricsFlat, denote]; rw [ha']; dsimp only [peelMetrics]
    rw [peelMetricsFlat_eq k _ _ (ctxTypes_pushTup_rev (immDefaults K ts) hΓ) hΔ hmL hk]
  | .load t _ k, _, _, _, _, _, _, _, _, hΓ, hΔ, hmL, hwf => by
    have ⟨ha, hk⟩ := wf_load hwf
    obtain ⟨_, ha'⟩ := denoteArg_ex (V := Arg K) hΓ ha
    dsimp only [peelMetricsFlat, denote]; rw [ha']; dsimp only [peelMetrics]
    rw [peelMetricsFlat_eq k _ _ (.cons hΓ) hΔ hmL hk]
  | .store _ _ k, _, _, _, _, _, _, _, _, hΓ, hΔ, hmL, hwf => by
    have ⟨hv, ha, hk⟩ := wf_store hwf
    obtain ⟨_, hv'⟩ := denoteArg_ex (V := Arg K) hΓ hv
    obtain ⟨_, ha'⟩ := denoteArg_ex (V := Arg K) hΓ ha
    dsimp only [peelMetricsFlat, denote]; rw [hv', ha']; dsimp only [peelMetrics]
    rw [peelMetricsFlat_eq k _ _ hΓ hΔ hmL hk]
  | .call _ bs _ k, _, _, _, _, _, _, _, _, hΓ, hΔ, hmL, hwf => by
    have ⟨ha, hk⟩ := wf_call hwf
    obtain ⟨_, ha'⟩ := denoteArgs_ex (V := Arg K) hΓ ha
    dsimp only [peelMetricsFlat, denote]; rw [ha']; dsimp only [peelMetrics]
    rw [peelMetricsFlat_eq k _ _ (ctxTypes_pushTup_rev (immDefaults K bs) hΓ) hΔ hmL hk]
  | .jnz _ t e, _, _, _, _, _, _, _, _, hΓ, hΔ, hmL, hwf => by
    have ⟨hc, ht, he⟩ := wf_jnz hwf
    obtain ⟨_, hc'⟩ := denoteArg_ex (V := Arg K) hΓ hc
    dsimp only [peelMetricsFlat, denote]; rw [hc']; dsimp only [peelMetrics]
    rw [peelMetricsFlat_eq t _ _ hΓ hΔ hmL ht, peelMetricsFlat_eq e _ _ hΓ hΔ hmL he]
  | .jump j _, _, _, _, _, _, _, targetId, _, hΓ, hΔ, hmL, hwf => by
    have ⟨hj, ha⟩ := wf_jump hwf
    obtain ⟨w₁, w₂, hres, hlk, hm⟩ := TrieRelMatch.resolveLabel_rel hΔ hmL hj
    obtain ⟨_, ha'⟩ := denoteArgs_ex (V := Arg K) hΓ ha
    dsimp only [peelMetricsFlat, denote]; rw [hlk, ha', hres]; dsimp only [peelMetrics]
    cases w₁ <;> cases w₂ <;> simp only [PeelLFlatMatch] at hm <;> try contradiction
    · rfl
    · rfl
    · subst hm; rfl
  | .ret _, _, _, _, _, _, _, _, _, hΓ, _, _, hwf => by
    obtain ⟨_, ha'⟩ := denoteArgs_ex (V := Arg K) hΓ hwf
    dsimp only [peelMetricsFlat, denote]; rw [ha']; rfl
  | .exit _ _, _, _, _, _, _, _, _, _, hΓ, _, _, hwf => by
    obtain ⟨_, ha'⟩ := denoteArgs_ex (V := Arg K) hΓ hwf
    dsimp only [peelMetricsFlat, denote]; rw [ha']; rfl
  | .hlt, _, _, _, _, _, _, _, _, _, _, _, _ => rfl
  | .group (sig := sig) bodies k, _, _, _, _, _, _, targetId, nextId, hΓ, hΔ, hmL, hwf => by
    have ⟨hb, hk⟩ := wf_group hwf
    dsimp only [peelMetricsFlat, denote, peelMetrics]
    have hps := probeTupFlat_match (rs := rs) sig nextId
    have hΔ' := ctxTypes_pushTup_rev (probeTup (V := K) (L := KL) (rs := rs) sig nextId) hΔ
    have hmL' := TrieRelMatch.pushTup hps hmL
    rw [peelMetricsBFlat_eq bodies targetId (nextId + sig.length) hΓ hΔ' hmL' hb,
      peelMetricsFlat_eq k targetId (nextId + sig.length) hΓ hΔ' hmL' hk]

private theorem peelMetricsBFlat_eq {rs : List Ty} :
    {sig : List (List Ty)} → (tb : TBlocks rs sig) → {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × Arg K t)} → {ls : List ((ts : List Ty) × PeelL K KL rs ts)} →
    {inLD : Nat} → {inLE : Trie ((ts : List Ty) × PeelLFlat rs ts)} →
    (targetId nextId : Nat) →
    CtxTypes Γ vs → CtxTypes Δ ls →
    TrieRelMatch (fun _ => PeelLFlatMatch (rs := rs)) inLD inLE ls →
    tb.wfCheck Γ Δ = true →
    peelMetricsBFlat targetId nextId inLD inLE tb =
      peelMetricsB targetId nextId (denoteB (Arg K) (PeelL K KL rs) tb vs ls)
  | _, .nil, _, _, _, _, _, _, _, _, _, _, _, _ => rfl
  | _, .cons (ts := ts) b bs, _, _, _, _, _, _, targetId, nextId, hΓ, hΔ, hmL, hwf => by
    have ⟨hb, hbs⟩ := wf_cons hwf
    dsimp only [peelMetricsBFlat, denoteB, peelMetricsB]
    rw [peelMetricsFlat_eq b targetId nextId (ctxTypes_pushTup_rev (immDefaults K ts) hΓ)
        hΔ hmL hb,
      peelMetricsBFlat_eq bs targetId nextId hΓ hΔ hmL hbs]
end

/-! ## 2. `peelAuxFlat` Equivalence -/

private theorem mkFreshVar_eq_toArgTup :
    (ts : List Ty) → (inVD outVD : Nat) →
    mkFreshTup (fun _ _ od => Arg.var od) ts inVD outVD = toArgTup (Tup.levels ts outVD)
  | [], _, _ => rfl
  | _ :: ts, inVD, outVD => by
    dsimp only [mkFreshTup, Tup.levels, toArgTup]
    rw [mkFreshVar_eq_toArgTup ts (inVD + 1) (outVD + 1)]

private theorem tupFreshVar_eq_toArgTup :
    (ts : List Ty) → (xs : Tup K ts) → (n : Nat) →
    tupFreshWith (fun x _ => Arg.var x) ts xs n = toArgTup xs
  | [], (), _ => rfl
  | _ :: ts, (_, xs), n => by
    dsimp only [tupFreshWith, toArgTup]; rw [tupFreshVar_eq_toArgTup ts xs (n + 1)]

local macro "peel_step" eq1:Lean.Parser.Tactic.rwRule "," eq2:Lean.Parser.Tactic.rwRule ","
    rw_a:Lean.Parser.Tactic.rwRule "," ctor:term "," next:tactic : tactic => `(tactic| (
  dsimp only [denote]; rw [$rw_a]; dsimp only
  rw [$eq1, $eq2]; dsimp only [flattenOp, toTFlat]
  refine congrArg $ctor ?_; $next))

private def PeelSingleBlock {rs : List Ty} (sb : Nat × Nat)
    (vs : List ((t : Ty) × Arg K t)) (ls : List ((ts : List Ty) × PeelL K KL rs ts))
    (inVD : Nat) (inVE : Trie ((t : Ty) × Arg K t))
    (inLD : Nat) (inLE : Trie ((ts : List Ty) × PeelLFlat rs ts)) :
    {sig : List (List Ty)} → TBlocks rs sig → Prop
  | [ts], .cons b .nil =>
    ∀ (ovd old : Nat) (args : Tup (Arg K) ts),
      toTFlat ((peelArgBAux sb.1 sb.2
        (denoteB (Arg K) (PeelL K KL rs) (.cons b .nil) vs ls)).1 args) ovd old =
        peelAuxFlat sb.1 sb.2 b (inVD + ts.length) (insertTupEnv inVD inVE args)
          inLD inLE ovd old
  | _, _ => True

private abbrev PeelPB {rs : List Ty} {sig : List (List Ty)} (sb : Nat × Nat)
    (tb : TBlocks rs sig) (_Γ : List Ty) (_Δ : List (List Ty))
    (vs : List ((t : Ty) × Arg K t)) (ls : List ((ts : List Ty) × PeelL K KL rs ts))
    (inVD : Nat) (inVE : Trie ((t : Ty) × Arg K t))
    (inLD : Nat) (inLE : Trie ((ts : List Ty) × PeelLFlat rs ts))
    (_outVD _outLD : Nat) : Prop :=
  (∀ ovd old,
    toTBlocks (peelBAux sb.1 sb.2 (denoteB (Arg K) (PeelL K KL rs) tb vs ls)) ovd old =
      peelBAuxFlat sb.1 sb.2 tb inVD inVE inLD inLE ovd old) ∧
  PeelSingleBlock sb vs ls inVD inVE inLD inLE tb

private theorem peelAuxFlat_both {rs : List Ty} :
    (∀ (tf : TFlat rs) {Γ Δ vs ls inVD outVD inLD outLD inVE inLE} (s : Nat × Nat),
      CtxTypes Γ vs → CtxTypes Δ ls → TrieCtxMatch inVD inVE vs →
      TrieRelMatch (fun _ => PeelLFlatMatch (rs := rs)) inLD inLE ls → tf.wfCheck Γ Δ = true →
      toTFlat (peelAux s.1 s.2 (denote (Arg K) (PeelL K KL rs) tf vs ls)) outVD outLD =
        peelAuxFlat s.1 s.2 tf inVD inVE inLD inLE outVD outLD) ∧
    (∀ {sig : List (List Ty)} (tb : TBlocks rs sig)
      {Γ Δ vs ls inVD outVD inLD outLD inVE inLE} (sb : Nat × Nat),
      CtxTypes Γ vs → CtxTypes Δ ls → TrieCtxMatch inVD inVE vs →
      TrieRelMatch (fun _ => PeelLFlatMatch (rs := rs)) inLD inLE ls → tb.wfCheck Γ Δ = true →
      PeelPB sb tb Γ Δ vs ls inVD inVE inLD inLE outVD outLD) := by
  refine relSim_mutual ⟨
    @fun ts _ Δ _ _ inVD outVD _ _ inVE _ s op k hΓ _ hmV hmL hwf ih => by
      obtain ⟨ha, hk⟩ := wf_let hwf
      peel_step peelAux.eq_def, peelAuxFlat.eq_def,
        denoteArgs_eq_some_resolveEnvArgs hΓ hmV op.args ha, TFlat.let_ _, {
        have hfresh := trieCtxMatch_insertFreshWith (fun _ _ od => Arg.var od) hmV ts outVD
        rw [mkFreshVar_eq_toArgTup] at hfresh
        exact ih s (ctxTypes_pushTup_rev _ hΓ) hfresh hmL hk },
    @fun _ Δ _ _ _ outVD _ _ _ _ s t a k hΓ _ hmV hmL hwf ih => by
      obtain ⟨ha, hk⟩ := wf_load hwf
      peel_step peelAux.eq_def, peelAuxFlat.eq_def,
        denoteArg_eq_some_resolveEnvArg hΓ hmV a ha, TFlat.load t _,
        (exact ih s (.cons hΓ) (hmV.cons t (Arg.var outVD)) hmL hk),
    fun s v a k hΓ _ hmV hmL hwf ih => by
      obtain ⟨hv, ha, hk⟩ := wf_store hwf
      dsimp only [denote]
      rw [denoteArg_eq_some_resolveEnvArg hΓ hmV v hv,
        denoteArg_eq_some_resolveEnvArg hΓ hmV a ha]; dsimp only
      rw [peelAux.eq_def, peelAuxFlat.eq_def]; dsimp only [toTFlat]
      exact congrArg (TFlat.store _ _) (ih s hΓ hmV hmL hk),
    @fun _ _ Δ _ _ inVD outVD _ _ inVE _ s f bs args k hΓ _ hmV hmL hwf ih => by
      obtain ⟨ha, hk⟩ := wf_call hwf
      peel_step peelAux.eq_def, peelAuxFlat.eq_def,
        denoteArgs_eq_some_resolveEnvArgs hΓ hmV args ha, TFlat.call f bs _, {
        have hfresh := trieCtxMatch_insertFreshWith (fun _ _ od => Arg.var od) hmV bs outVD
        rw [mkFreshVar_eq_toArgTup] at hfresh
        exact ih s (ctxTypes_pushTup_rev _ hΓ) hfresh hmL hk },
    fun s c t e hΓ _ hmV _ hwf iht ihe => by
      obtain ⟨hc, ht, he⟩ := wf_jnz hwf
      dsimp only [denote]; rw [denoteArg_eq_some_resolveEnvArg hΓ hmV c hc]; dsimp only
      rw [peelAux.eq_def, peelAuxFlat.eq_def]; dsimp only [toTFlat]
      rw [iht s ht, ihe s he],
    fun s j args hΓ hΔ hmV hmL hwf => by
      obtain ⟨hj, ha⟩ := wf_jump hwf
      obtain ⟨w₁, w₂, hres, hlk, hm⟩ := TrieRelMatch.resolveLabel_rel hΔ hmL hj
      dsimp only [denote]; rw [hlk, denoteArgs_eq_some_resolveEnvArgs hΓ hmV args ha]; dsimp only
      rw [peelAux.eq_def, peelAuxFlat.eq_def]; dsimp only; rw [hres]
      cases w₁ with
      | outer l₁ =>
        cases w₂ with
        | outer l₂ => cases hm; rfl
        | subst _ _ | probe _ => exact False.elim hm
      | subst _ _ =>
        cases w₂ with
        | outer _ | probe _ => exact False.elim hm
        | subst _ _ => exact (hm.2 _ _ _).symm
      | probe _ =>
        cases w₂ with
        | outer _ | subst _ _ => exact False.elim hm
        | probe _ => rfl,
    fun s vs' hΓ _ hmV _ hwf => by
      dsimp only [denote]; rw [denoteArgs_eq_some_resolveEnvArgs hΓ hmV vs' hwf]
      dsimp only [peelAux, peelAuxFlat, toTFlat],
    fun s _ args hΓ _ hmV _ hwf => by
      dsimp only [denote]; rw [denoteArgs_eq_some_resolveEnvArgs hΓ hmV args hwf]
      dsimp only [peelAux, peelAuxFlat, toTFlat],
    fun _ _ _ _ _ _ => rfl,
    @fun sig Γ Δ vs ls inVD outVD inLD outLD inVE inLE s bodies k hΓ hΔ hmV hmL hwf ihB ihK => by
      obtain ⟨hb, hk⟩ := wf_group hwf
      dsimp only [denote]
      rcases s with ⟨budget, depth⟩
      cases sig with
      | nil =>
        rw [peelAux.eq_def, peelAuxFlat.eq_def]; dsimp only [toTFlat]
        have houter := toOuterTupFlat_match (rs := rs) (Tup.levels [] outLD)
        have hΔ' := ctxTypes_pushTup_rev (toOuterTup (Tup.levels [] outLD)) hΔ
        have hmL' := TrieRelMatch.pushTup houter hmL
        rw [(ihB (outLD' := 0) (budget, depth) hΔ' hmL' hb).1 outVD (outLD + [].length),
          ihK (outLD' := outLD + [].length) (budget, depth) hΔ' hmL' hk]
      | cons ts sig' =>
        cases sig' with
        | cons hd tl =>
          rw [peelAux.eq_def, peelAuxFlat.eq_def]; dsimp only [toTFlat]
          have houter := toOuterTupFlat_match (rs := rs) (Tup.levels (ts :: hd :: tl) outLD)
          have hΔ' := ctxTypes_pushTup_rev (toOuterTup (Tup.levels (ts :: hd :: tl) outLD)) hΔ
          have hmL' := TrieRelMatch.pushTup houter hmL
          rw [(ihB (outLD' := 0) (budget, depth) hΔ' hmL' hb).1 outVD
              (outLD + (ts :: hd :: tl).length),
            ihK (outLD' := outLD + (ts :: hd :: tl).length) (budget, depth) hΔ' hmL' hk]
        | nil =>
          cases bodies with
          | cons b bs =>
            cases bs
            have hcons : (TBlocks.cons (ts := ts) b .nil).wfCheck Γ (pushTypes [ts] Δ) = true :=
              hb
            have hbwf := (wf_cons hcons).1
            have hmProbe : TrieRelMatch (fun _ => PeelLFlatMatch (rs := rs))
                (inLD + 1) (inLE.insert inLD ⟨ts, .probe 0⟩) (⟨ts, .probe 0⟩ :: ls) :=
              hmL.cons (a := ts) (x₁ := PeelLFlat.probe 0) (x₂ := PeelL.probe 0) rfl
            have hΔProbe : CtxTypes (pushTypes [ts] Δ)
                (⟨ts, (PeelL.probe 0 : PeelL K KL rs ts)⟩ :: ls) := .cons hΔ
            have hmb : peelMetricsFlat 0 1 (inLD + 1) (inLE.insert inLD ⟨ts, .probe 0⟩) b =
                loopBlockMetrics (denoteB (Arg K) (PeelL K KL rs) (.cons (ts := ts) b .nil) vs
                  (pushTup (as := [ts]) ((PeelL.probe 0 : PeelL K KL rs ts), ()) ls)) := by
              rw [loopBlockMetrics_eq]
              exact peelMetricsFlat_eq b 0 1 (ctxTypes_pushTup_rev (immDefaults K ts) hΓ)
                hΔProbe hmProbe hbwf
            have hme : peelMetricsFlat 0 1 (inLD + 1) (inLE.insert inLD ⟨ts, .probe 0⟩) k =
                peelMetrics 0 1 (denote (Arg K) (PeelL K KL rs) k vs
                  (pushTup (as := [ts]) ((PeelL.probe 0 : PeelL K KL rs ts), ()) ls)) :=
              peelMetricsFlat_eq k 0 1 hΓ hΔProbe hmProbe hk
            rw [peelAux.eq_def, peelAuxFlat.eq_def]; dsimp only
            rw [← hmb, ← hme]
            by_cases hcan : canPeel budget
                (peelMetricsFlat 0 1 (inLD + 1) (inLE.insert inLD ⟨ts, .probe 0⟩) b)
                (peelMetricsFlat 0 1 (inLD + 1) (inLE.insert inLD ⟨ts, .probe 0⟩) k) = true
            · simp only [hcan, ↓reduceIte]
              let remB := (budget - (peelMetricsFlat 0 1 (inLD + 1)
                (inLE.insert inLD ⟨ts, .probe 0⟩) b).size) / 2
              let remIter2F : Nat → Nat → Tup (Arg K) ts → TFlat rs := fun ovd2 old2 backArgs =>
                .group (sig := [ts])
                  (peelBAuxFlat remB (depth + 1) (.cons (ts := ts) b .nil) inVD inVE (inLD + 1)
                    (inLE.insert inLD ⟨ts, .outer old2⟩) ovd2 (old2 + 1))
                  (.jump 0 (idxArgs ovd2 backArgs))
              let remIter2P : Tup (Arg K) ts → Expr K KL rs := fun backArgs =>
                .group (sig := [ts])
                  (fun Js => peelBAux remB (depth + 1)
                    (denoteB (Arg K) (PeelL K KL rs) (.cons (ts := ts) b .nil) vs
                      (pushTup (toOuterTup Js) ls)))
                  (fun Js => .jump Js.1 backArgs)
              have hRem : ∀ (ovd2 old2 : Nat) (backArgs : Tup (Arg K) ts),
                  remIter2F ovd2 old2 backArgs = toTFlat (remIter2P backArgs) ovd2 old2 := by
                intro ovd2 old2 backArgs
                dsimp only [remIter2F, remIter2P, toTFlat, Tup.levels, toOuterTup, pushTup]
                simp only [List.length_cons, List.length_nil, Nat.zero_add]
                have hmOut : TrieRelMatch (fun _ => PeelLFlatMatch (rs := rs))
                    (inLD + 1) (inLE.insert inLD ⟨ts, .outer old2⟩) (⟨ts, .outer old2⟩ :: ls) :=
                  hmL.cons (a := ts) (x₁ := PeelLFlat.outer old2) (x₂ := PeelL.outer old2) rfl
                have hΔOut : CtxTypes (pushTypes [ts] Δ) (⟨ts, .outer old2⟩ :: ls) :=
                  .cons hΔ
                have hbRem :=
                  (ihB (outLD' := 0) (remB, depth + 1) hΔOut hmOut hcons).1 ovd2 (old2 + 1)
                dsimp only [pushTup] at hbRem
                have hzero : (if old2 < old2 + 1 then old2 + 1 - 1 - old2 else old2 + 1) = 0 := by
                  simp
                rw [hbRem, hzero]
              have hmSubRem : TrieRelMatch (fun _ => PeelLFlatMatch (rs := rs))
                  (inLD + 1) (inLE.insert inLD ⟨ts, .subst (2 * depth) remIter2F⟩)
                  (⟨ts, .subst (2 * depth) remIter2P⟩ :: ls) :=
                hmL.cons (a := ts) ⟨rfl, hRem⟩
              let iter1F : Nat → Nat → Tup (Arg K) ts → TFlat rs := fun ovd1 old1 args1 =>
                peelAuxFlat remB (depth + 1) b (inVD + ts.length) (insertTupEnv inVD inVE args1)
                  (inLD + 1) (inLE.insert inLD ⟨ts, .subst (2 * depth) remIter2F⟩) ovd1 old1
              let iter1P : Tup (Arg K) ts → Expr K KL rs :=
                (peelArgBAux remB (depth + 1)
                  (denoteB (Arg K) (PeelL K KL rs) (.cons (ts := ts) b .nil) vs
                    (⟨ts, .subst (2 * depth) remIter2P⟩ :: ls))).1
              have hIter1 : ∀ (ovd1 old1 : Nat) (args1 : Tup (Arg K) ts),
                  iter1F ovd1 old1 args1 = toTFlat (iter1P args1) ovd1 old1 := by
                intro ovd1 old1 args1
                exact ((ihB (outLD' := 0) (remB, depth + 1) (.cons hΔ) hmSubRem hcons).2
                  ovd1 old1 args1).symm
              have hmSubIter : TrieRelMatch (fun _ => PeelLFlatMatch (rs := rs))
                  (inLD + 1) (inLE.insert inLD ⟨ts, .subst (2 * depth + 1) iter1F⟩)
                  (⟨ts, .subst (2 * depth + 1) iter1P⟩ :: ls) :=
                hmL.cons (a := ts) ⟨rfl, hIter1⟩
              exact ihK (budget, depth + 1) (.cons hΔ) hmSubIter hk
            · simp only [hcan, Bool.false_eq_true, ↓reduceIte, toTFlat]
              have houter := toOuterTupFlat_match (rs := rs) (Tup.levels [ts] outLD)
              have hΔ' := ctxTypes_pushTup_rev (toOuterTup (Tup.levels [ts] outLD)) hΔ
              have hmL' := TrieRelMatch.pushTup houter hmL
              simp only [List.length_cons, List.length_nil, Nat.zero_add] at hmL' ⊢
              rw [(ihB (outLD' := 0) (budget, depth) hΔ' hmL' hcons).1 outVD (outLD + 1),
                ihK (outLD' := outLD + 1) (budget, depth) hΔ' hmL' hk],
    fun sb _ _ _ _ _ => ⟨by
      intro ovd old
      rw [denoteB.eq_def, peelBAux.eq_def, peelBAuxFlat.eq_def]; rfl,
    trivial⟩,
    @fun ts sig' _ Δ _ _ inVD outVD inLD outLD inVE inLE sb b bs
        hΓ _ hmV hmL hwf ih ihs => by
      obtain ⟨hb, hbs⟩ := wf_cons hwf
      refine ⟨?_, ?_⟩
      · intro ovd old
        rw [denoteB.eq_def, peelBAux.eq_def, peelBAuxFlat.eq_def]
        dsimp only [toTBlocks]
        have hfresh := trieCtxMatch_insertFreshWith (fun _ _ od => Arg.var od) hmV ts ovd
        rw [mkFreshVar_eq_toArgTup] at hfresh
        exact congr (congrArg TBlocks.cons
          (ih (outVD' := ovd + ts.length) (outLD' := old) sb
            (ctxTypes_pushTup_rev _ hΓ) hfresh hmL hb))
          ((ihs sb hbs).1 ovd old)
      · cases bs with
        | cons _ _ => exact trivial
        | nil =>
          intro ovd old args
          dsimp only [denoteB, peelArgBAux]
          exact ih (outVD' := ovd) (outLD' := old) sb
            (ctxTypes_pushTup_rev args hΓ) (trieCtxMatch_insertTupEnv hmV args) hmL hb⟩

/-! ## 3. Public `peelFlat` Equivalence Theorems -/

/-- `peelFlat as tf budget = reifyFunc (Func.peel (denoteFunc tf) budget)` under `wfCheck = true`. -/
theorem peelFlat_eq {as rs : List Ty} (tf : TFlat rs) (budget : Nat := 40)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    peelFlat as tf budget = reifyFunc (Func.peel (denoteFunc (as := as) tf) budget) := by
  dsimp only [peelFlat, Func.peel, peel, denoteFunc, reifyFunc]
  have hmV := trieCtxMatch_initEnv (fun x _ => Arg.var x) as
  rw [tupFreshVar_eq_toArgTup] at hmV
  have haux := peelAuxFlat_both.1 tf (budget, 0) (ctxTypes_pushTup_rev _ .nil) .nil hmV
    (TrieRelMatch.empty (fun _ => PeelLFlatMatch (rs := rs))) hwf
    (outVD := as.length) (outLD := 0)
  exact haux.symm

/-- `denoteFunc (peelFlat as tf budget) = Func.peel (denoteFunc tf) budget` under `wfCheck = true`. -/
theorem denoteFunc_peelFlat {as rs : List Ty} (tf : TFlat rs) (budget : Nat := 40)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    denoteFunc (as := as) (peelFlat as tf budget) =
      Func.peel (denoteFunc (as := as) tf) budget :=
  denoteFunc_of_flat_eq (flat := fun tf => peelFlat as tf budget)
    (phoas := fun g => Func.peel g budget)
    (fun hf => Func.peel_wf hf budget) tf hwf (peelFlat_eq tf budget hwf)

/-- `peelFlat` preserves `wfCheck`. -/
theorem peelFlat_wfCheck {as rs : List Ty} (tf : TFlat rs) (budget : Nat := 40)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    (peelFlat as tf budget).wfCheck (pushTypes as []) [] = true :=
  wfCheck_of_flat_eq (flat := fun tf => peelFlat as tf budget)
    (phoas := fun g => Func.peel g budget)
    (fun hf => Func.peel_wf hf budget) tf hwf (peelFlat_eq tf budget hwf)

/-- `(peelFlatFn f budget).toFn = ⟨f.name, f.as, f.rs, Func.peel f.toFn.body budget⟩` under
`wfCheck = true`. -/
theorem peelFlatFn_toFn (f : TFlatFn) (budget : Nat := 40) (hwf : f.wfCheck = true) :
    (peelFlatFn f budget).toFn = ⟨f.name, f.as, f.rs, Func.peel f.toFn.body budget⟩ :=
  fn_toFn_of_denoteFunc (flatBody := fun as _ tf => peelFlat as tf budget)
    (phoas := fun g => Func.peel g budget)
    (fun tf h => denoteFunc_peelFlat tf budget h) f hwf

/-- `peelFlatFn` preserves `TFlatFn.wfCheck`. -/
theorem peelFlatFn_wfCheck (f : TFlatFn) (budget : Nat := 40) (hwf : f.wfCheck = true) :
    (peelFlatFn f budget).wfCheck = true :=
  peelFlat_wfCheck f.body budget hwf

end OptFlatPeel
end LeanQbe.T
