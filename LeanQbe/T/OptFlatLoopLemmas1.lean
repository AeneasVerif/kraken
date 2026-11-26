module

public import LeanQbe.T.OptFlatLoop
import LeanQbe.T.FlatDirectLemmas
import LeanQbe.T.PassFlatKit
import LeanQbe.T.LoopRotateLemmas

/-!
# Validator Equivalence Proofs for `OptFlatLoop` (`validateRotPlanFlat_eq`)

Proves `=` correspondence (`std3` axioms only) between native `TFlat`
`OptFlatLoop.validateLeafFlat` / `validateHdrFlat` / `validateRotPlanWithFlat`
and `LoopRotate.validateLeaf` / `validateHdr` / `validateRotPlanWith`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T
namespace OptFlatLoop

open OptFlatPlanKit
open LoopRotate

private theorem CtxLevels_cons_k {t : Ty} {vs : List ((t : Ty) × K t)}
    (hvl : CtxLevels vs) : CtxLevels (⟨t, vs.length⟩ :: vs) :=
  CtxLevels.cons hvl t

private theorem CtxLevels_pushTup_k {ts : List Ty} {vs : List ((t : Ty) × K t)}
    (hvl : CtxLevels vs) : CtxLevels (pushTup (Tup.levels ts vs.length) vs) :=
  CtxLevels.pushTup hvl

mutual
private theorem validateLeafFlat_eq {rs : List Ty} :
    (tf : TFlat rs) → {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × K t)} → {ls : List ((ts : List Ty) × BoolL ts)} →
    {inLD : Nat} → {inLE : Trie ((ts : List Ty) × BoolL ts)} →
    CtxTypes Γ vs → CtxLevels vs → CtxTypes Δ ls → TrieCtxMatch inLD inLE ls →
    tf.wfCheck Γ Δ = true →
    validateLeaf (denote K BoolL tf vs ls) vs.length = validateLeafFlat tf vs.length inLD inLE
  | .let_ (ts := ts) op k, Γ, Δ, vs, ls, inLD, inLE, hΓ, hvl, hΔ, hlm, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    have hargs := denoteArgs_eq_some_levelArgs hΓ hvl op.args hwf.1
    dsimp only [denote, validateLeafFlat]
    rw [hargs]
    dsimp only [validateLeaf, addArgsSet]
    have hk := validateLeafFlat_eq k (CtxTypes.push _ hΓ) (CtxLevels_pushTup_k hvl)
      hΔ hlm hwf.2
    rw [pushTup_length (Tup.levels ts vs.length) vs] at hk
    rw [hk]
  | .load _ a k, Γ, Δ, vs, ls, inLD, inLE, hΓ, hvl, hΔ, hlm, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    have ha := denoteArg_eq_some_levelArg hΓ hvl a hwf.1
    dsimp only [denote, validateLeafFlat]
    rw [ha]
    dsimp only [validateLeaf]
    have hk := validateLeafFlat_eq k (.cons hΓ) (CtxLevels_cons_k hvl) hΔ hlm hwf.2
    dsimp only [List.length] at hk
    rw [hk]
  | .store v a k, Γ, Δ, vs, ls, inLD, inLE, hΓ, hvl, hΔ, hlm, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    have hv := denoteArg_eq_some_levelArg hΓ hvl v hwf.1.1
    have ha := denoteArg_eq_some_levelArg hΓ hvl a hwf.1.2
    dsimp only [denote, validateLeafFlat]
    rw [hv, ha]
    dsimp only [validateLeaf]
    rw [validateLeafFlat_eq k hΓ hvl hΔ hlm hwf.2]
  | .call _ bs args k, Γ, Δ, vs, ls, inLD, inLE, hΓ, hvl, hΔ, hlm, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    have hargs := denoteArgs_eq_some_levelArgs hΓ hvl args hwf.1
    dsimp only [denote, validateLeafFlat]
    rw [hargs]
    dsimp only [validateLeaf, addArgsSet]
    have hk := validateLeafFlat_eq k (CtxTypes.push _ hΓ) (CtxLevels_pushTup_k hvl)
      hΔ hlm hwf.2
    rw [pushTup_length (Tup.levels bs vs.length) vs] at hk
    rw [hk]
  | .jnz c t e, Γ, Δ, vs, ls, inLD, inLE, hΓ, hvl, hΔ, hlm, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    have hc := denoteArg_eq_some_levelArg hΓ hvl c hwf.1.1
    dsimp only [denote, validateLeafFlat]
    rw [hc]
    dsimp only [validateLeaf]
    rw [validateLeafFlat_eq t hΓ hvl hΔ hlm hwf.1.2,
      validateLeafFlat_eq e hΓ hvl hΔ hlm hwf.2]
  | .jump (ts := ts) j args, Γ, Δ, vs, ls, inLD, inLE, hΓ, hvl, hΔ, hlm, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨b, hlk, hres⟩ := lookupL_eq_some_resolveLabel hΔ hlm hwf.1
    have hargs := denoteArgs_eq_some_levelArgs hΓ hvl args hwf.2
    dsimp only [denote, validateLeafFlat]
    rw [hlk, hargs, hres]
    dsimp only [validateLeaf, addArgsSet]
    cases b <;> rfl
  | .ret vs', Γ, _, vs, ls, _, _, hΓ, hvl, _, _, hwf => by
    have hvs := denoteArgs_eq_some_levelArgs hΓ hvl vs' hwf
    dsimp only [denote, validateLeafFlat]
    rw [hvs]
    rfl
  | .exit f args, Γ, _, vs, ls, _, _, hΓ, hvl, _, _, hwf => by
    have hargs := denoteArgs_eq_some_levelArgs hΓ hvl args hwf
    dsimp only [denote, validateLeafFlat]
    rw [hargs]
    rfl
  | .hlt, _, _, _, _, _, _, _, _, _, _, _ => rfl
  | .group (sig := sig) bs k, Γ, Δ, vs, ls, inLD, inLE, hΓ, hvl, hΔ, hlm, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denote, validateLeafFlat, validateLeaf]
    have hb := validateLeafBFlat_eq bs hΓ hvl (CtxTypes.push _ hΔ)
      (trieCtxMatch_insertTupEnv hlm (trueLabels sig)) hwf.1
    have hk := validateLeafFlat_eq k hΓ hvl (CtxTypes.push _ hΔ)
      (trieCtxMatch_insertTupEnv hlm (trueLabels sig)) hwf.2
    rw [hb, hk]

private theorem validateLeafBFlat_eq {rs : List Ty} :
    {sig : List (List Ty)} → (tb : TBlocks rs sig) →
    {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × K t)} → {ls : List ((ts : List Ty) × BoolL ts)} →
    {inLD : Nat} → {inLE : Trie ((ts : List Ty) × BoolL ts)} →
    CtxTypes Γ vs → CtxLevels vs → CtxTypes Δ ls → TrieCtxMatch inLD inLE ls →
    tb.wfCheck Γ Δ = true →
    validateLeaf.validateLeafB (denoteB K BoolL tb vs ls) vs.length =
      validateLeafBFlat tb vs.length inLD inLE
  | _, .nil, _, _, _, _, _, _, _, _, _, _, _ => rfl
  | _, .cons (ts := ts) b bs, Γ, Δ, vs, ls, inLD, inLE, hΓ, hvl, hΔ, hlm, hwf => by
    dsimp only [TBlocks.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denoteB, validateLeafBFlat, validateLeaf.validateLeafB]
    have hb := validateLeafFlat_eq b (CtxTypes.push _ hΓ) (CtxLevels_pushTup_k hvl)
      hΔ hlm hwf.1
    rw [pushTup_length (Tup.levels ts vs.length) vs] at hb
    rw [hb, validateLeafBFlat_eq bs hΓ hvl hΔ hlm hwf.2]
end

private def hdrΓ : HdrPlan → List Ty → List Ty
  | [], Γ => Γ
  | .let_ dts :: ss, Γ => hdrΓ ss (pushTypes dts Γ)
  | .load t :: ss, Γ => hdrΓ ss (t :: Γ)

private def hdrVs : HdrPlan → List ((t : Ty) × K t) → List ((t : Ty) × K t)
  | [], vs => vs
  | .let_ dts :: ss, vs => hdrVs ss (pushTup (Tup.levels dts vs.length) vs)
  | .load t :: ss, vs => hdrVs ss (⟨t, vs.length⟩ :: vs)

private theorem validateHdr_nil_none {rs : List Ty} (nv : Nat) :
    {e : Expr K BoolL rs} → (match e with | .jnz _ _ _ => False | _ => True) →
    validateHdr [] e nv = none
  | .jnz _ _ _, h => False.elim h
  | .let_ _ _, _ | .load _ _ _, _ | .store _ _ _, _ | .call _ _ _, _
  | .jump _ _, _ | .ret _, _ | .exit _ _, _ | .hlt, _ | .group _ _, _ => rfl

private theorem validateHdr_let_none {rs : List Ty} (dts : List Ty) (ss : HdrPlan) (nv : Nat) :
    {e : Expr K BoolL rs} → (match e with | .let_ _ _ => False | _ => True) →
    validateHdr (.let_ dts :: ss) e nv = none
  | .let_ _ _, h => False.elim h
  | .jnz _ _ _, _ | .load _ _ _, _ | .store _ _ _, _ | .call _ _ _, _
  | .jump _ _, _ | .ret _, _ | .exit _ _, _ | .hlt, _ | .group _ _, _ => rfl

private theorem validateHdr_load_none {rs : List Ty} (t : Ty) (ss : HdrPlan) (nv : Nat) :
    {e : Expr K BoolL rs} → (match e with | .load _ _ _ => False | _ => True) →
    validateHdr (.load t :: ss) e nv = none
  | .load _ _ _, h => False.elim h
  | .jnz _ _ _, _ | .let_ _ _, _ | .store _ _ _, _ | .call _ _ _, _
  | .jump _ _, _ | .ret _, _ | .exit _ _, _ | .hlt, _ | .group _ _, _ => rfl

private inductive ValidateHdrSpec {rs : List Ty} (hdr : HdrPlan) (tf : TFlat rs)
    (Γ : List Ty) (Δ : List (List Ty)) (vs : List ((t : Ty) × K t)) :
    Option (Trie Unit × TFlat rs × TFlat rs × Nat) → Prop
  | isNone :
    (∀ {ls : List ((ts : List Ty) × BoolL ts)}, CtxTypes Δ ls →
      validateHdr hdr (denote K BoolL tf vs ls) vs.length = none) →
    ValidateHdrSpec hdr tf Γ Δ vs none
  | isSome (sh : Trie Unit) (tF eF : TFlat rs) (nv' : Nat) :
    nv' = vs.length + hdrStepCount hdr →
    CtxTypes (hdrΓ hdr Γ) (hdrVs hdr vs) →
    CtxLevels (hdrVs hdr vs) →
    (hdrVs hdr vs).length = vs.length + hdrStepCount hdr →
    tF.wfCheck (hdrΓ hdr Γ) Δ = true →
    eF.wfCheck (hdrΓ hdr Γ) Δ = true →
    (∀ {ls : List ((ts : List Ty) × BoolL ts)}, CtxTypes Δ ls →
      validateHdr hdr (denote K BoolL tf vs ls) vs.length =
        some (sh, denote K BoolL tF (hdrVs hdr vs) ls, denote K BoolL eF (hdrVs hdr vs) ls, nv')) →
    ValidateHdrSpec hdr tf Γ Δ vs (some (sh, tF, eF, nv'))

private theorem validateHdrFlat_spec {rs : List Ty} :
    (hdr : HdrPlan) → (tf : TFlat rs) → {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × K t)} →
    CtxTypes Γ vs → CtxLevels vs → tf.wfCheck Γ Δ = true →
    ValidateHdrSpec hdr tf Γ Δ vs (validateHdrFlat hdr tf vs.length)
  | [], tf, Γ, Δ, vs, hΓ, hvl, hwf => by
    cases tf with
    | jnz c t e =>
      dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
      refine ValidateHdrSpec.isSome (addArgKey (levelArg vs.length c) .empty) t e vs.length
        rfl hΓ hvl rfl hwf.1.2 hwf.2 ?_
      intro ls _
      have hc := denoteArg_eq_some_levelArg hΓ hvl c hwf.1.1
      dsimp only [denote]
      rw [hc]
      rfl
    | _ =>
      refine ValidateHdrSpec.isNone fun _ => ?_
      dsimp only [denote]
      repeat (first | split | (apply validateHdr_nil_none; trivial))
  | .let_ dts :: ss, tf, Γ, Δ, vs, hΓ, hvl, hwf => by
    cases tf with
    | let_ op k =>
      rename_i dts'
      dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
      dsimp only [validateHdrFlat]
      cases hdec : tysDecEq dts dts' with
      | isFalse _ =>
        refine ValidateHdrSpec.isNone ?_
        intro ls _
        have hargs := denoteArgs_eq_some_levelArgs hΓ hvl op.args hwf.1
        dsimp only [denote]
        rw [hargs]
        dsimp only [validateHdr]
        rw [hdec]
      | isTrue heq =>
        subst heq
        have ih := validateHdrFlat_spec ss k (CtxTypes.push _ hΓ) (CtxLevels_pushTup_k hvl) hwf.2
        have hlen : (pushTup (Tup.levels dts vs.length) vs).length = vs.length + dts.length :=
          pushTup_length _ vs
        rw [hlen] at ih
        cases hvh : validateHdrFlat ss k (vs.length + dts.length) with
        | none =>
          rw [hvh] at ih
          refine ValidateHdrSpec.isNone ?_
          intro ls hΔ
          have hargs := denoteArgs_eq_some_levelArgs hΓ hvl op.args hwf.1
          dsimp only [denote]
          rw [hargs]
          dsimp only [validateHdr]
          rw [hdec]
          cases ih with
          | isNone hnone =>
            have hsub := hnone hΔ
            rw [hlen] at hsub
            dsimp only
            rw [hsub]
            rfl
        | some val =>
          rcases val with ⟨sh, tF, eF, nv'⟩
          rw [hvh] at ih
          cases ih with
          | isSome _ _ _ _ hnv hΓ' hvl' hl' htF heF hsome =>
            have hnv' : nv' = vs.length + hdrStepCount (.let_ dts :: ss) := by
              dsimp only [hdrStepCount, HdrStep.tys]; omega
            have hl'' : (hdrVs (.let_ dts :: ss) vs).length =
                vs.length + hdrStepCount (.let_ dts :: ss) := by
              dsimp only [hdrVs, hdrStepCount, HdrStep.tys]; omega
            refine ValidateHdrSpec.isSome (addArgKeys (levelArgs vs.length op.args) sh) tF eF nv'
              hnv' hΓ' hvl' hl'' htF heF ?_
            intro ls hΔ
            have hargs := denoteArgs_eq_some_levelArgs hΓ hvl op.args hwf.1
            dsimp only [denote]
            rw [hargs]
            dsimp only [validateHdr, addArgsSet]
            rw [hdec]
            have hsub := hsome hΔ
            rw [hlen] at hsub
            dsimp only
            rw [hsub]
            rfl
    | _ =>
      refine ValidateHdrSpec.isNone fun _ => ?_
      dsimp only [denote]
      repeat (first | split | (apply validateHdr_let_none; trivial))
  | .load t :: ss, tf, Γ, Δ, vs, hΓ, hvl, hwf => by
    cases tf with
    | load t' a k =>
      dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
      dsimp only [validateHdrFlat]
      cases hdec : tyDecEq t t' with
      | isFalse _ =>
        refine ValidateHdrSpec.isNone ?_
        intro ls _
        have ha := denoteArg_eq_some_levelArg hΓ hvl a hwf.1
        dsimp only [denote]
        rw [ha]
        dsimp only [validateHdr]
        rw [hdec]
      | isTrue heq =>
        subst heq
        have ih := validateHdrFlat_spec ss k (.cons hΓ) (CtxLevels_cons_k hvl) hwf.2
        dsimp only [List.length] at ih
        cases hvh : validateHdrFlat ss k (vs.length + 1) with
        | none =>
          rw [hvh] at ih
          refine ValidateHdrSpec.isNone ?_
          intro ls hΔ
          have ha := denoteArg_eq_some_levelArg hΓ hvl a hwf.1
          dsimp only [denote]
          rw [ha]
          dsimp only [validateHdr]
          rw [hdec]
          cases ih with
          | isNone hnone =>
            have hsub := hnone hΔ
            dsimp only [List.length] at hsub
            dsimp only
            rw [hsub]
            rfl
        | some val =>
          rcases val with ⟨sh, tF, eF, nv'⟩
          rw [hvh] at ih
          cases ih with
          | isSome _ _ _ _ hnv hΓ' hvl' hl' htF heF hsome =>
            dsimp only [hdrStepCount, HdrStep.tys, List.length] at hnv hl' ⊢
            have hnv' : nv' = vs.length + (1 + hdrStepCount ss) := by omega
            have hl'' : (hdrVs (.load t :: ss) vs).length = vs.length + (1 + hdrStepCount ss) := by
              dsimp only [hdrVs, List.length]
              rw [hl']; omega
            refine ValidateHdrSpec.isSome (addArgKey (levelArg vs.length a) sh) tF eF nv'
              hnv' hΓ' hvl' hl'' htF heF ?_
            intro ls hΔ
            have ha := denoteArg_eq_some_levelArg hΓ hvl a hwf.1
            dsimp only [denote]
            rw [ha]
            dsimp only [validateHdr]
            rw [hdec]
            have hsub := hsome hΔ
            dsimp only [List.length] at hsub
            dsimp only
            rw [hsub]
            rfl
    | _ =>
      refine ValidateHdrSpec.isNone fun _ => ?_
      dsimp only [denote]
      repeat (first | split | (apply validateHdr_load_none; trivial))

mutual
theorem validateRotPlanWithFlat_eq {rs : List Ty} (allowHdr : Bool) :
    (plan : RotPlan) → (tf : TFlat rs) → {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × K t)} → {ls : List ((ts : List Ty) × BoolL ts)} →
    {inLD : Nat} → {inLE : Trie ((ts : List Ty) × BoolL ts)} →
    CtxTypes Γ vs → CtxLevels vs → CtxTypes Δ ls → TrieCtxMatch inLD inLE ls →
    tf.wfCheck Γ Δ = true →
    validateRotPlanWith allowHdr plan (denote K BoolL tf vs ls) vs.length =
      validateRotPlanWithFlat allowHdr plan tf vs.length inLD inLE
  | .leaf, tf, Γ, Δ, vs, ls, inLD, inLE, hΓ, hvl, hΔ, hlm, hwf => by
    rw [validateRotPlanWith.eq_1]
    exact validateLeafFlat_eq tf hΓ hvl hΔ hlm hwf
  | .letP p, tf, Γ, Δ, vs, ls, inLD, inLE, hΓ, hvl, hΔ, hlm, hwf => by
    cases tf with
    | let_ op k =>
      rename_i ts
      dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
      have hargs := denoteArgs_eq_some_levelArgs hΓ hvl op.args hwf.1
      dsimp only [denote, validateRotPlanWithFlat]
      rw [hargs, validateRotPlanWith.eq_2]
      dsimp only [addArgsSet]
      have hk := validateRotPlanWithFlat_eq allowHdr p k (CtxTypes.push _ hΓ)
        (CtxLevels_pushTup_k hvl) hΔ hlm hwf.2
      rw [pushTup_length (Tup.levels ts vs.length) vs] at hk
      rw [hk]
    | _ =>
      dsimp only [denote, validateRotPlanWithFlat]
      repeat split
      all_goals rw [validateRotPlanWith.eq_def]
  | .loadP p, tf, Γ, Δ, vs, ls, inLD, inLE, hΓ, hvl, hΔ, hlm, hwf => by
    cases tf with
    | load _ a k =>
      dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
      have ha := denoteArg_eq_some_levelArg hΓ hvl a hwf.1
      dsimp only [denote, validateRotPlanWithFlat]
      rw [ha, validateRotPlanWith.eq_3]
      have hk := validateRotPlanWithFlat_eq allowHdr p k (.cons hΓ)
        (CtxLevels_cons_k hvl) hΔ hlm hwf.2
      dsimp only [List.length] at hk
      rw [hk]
    | _ =>
      dsimp only [denote, validateRotPlanWithFlat]
      repeat split
      all_goals rw [validateRotPlanWith.eq_def]
  | .storeP p, tf, Γ, Δ, vs, ls, inLD, inLE, hΓ, hvl, hΔ, hlm, hwf => by
    cases tf with
    | store v a k =>
      dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
      have hv := denoteArg_eq_some_levelArg hΓ hvl v hwf.1.1
      have ha := denoteArg_eq_some_levelArg hΓ hvl a hwf.1.2
      dsimp only [denote, validateRotPlanWithFlat]
      rw [hv, ha, validateRotPlanWith.eq_4]
      rw [validateRotPlanWithFlat_eq allowHdr p k hΓ hvl hΔ hlm hwf.2]
    | _ =>
      dsimp only [denote, validateRotPlanWithFlat]
      repeat split
      all_goals rw [validateRotPlanWith.eq_def]
  | .callP p, tf, Γ, Δ, vs, ls, inLD, inLE, hΓ, hvl, hΔ, hlm, hwf => by
    cases tf with
    | call _ bs args k =>
      dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
      have hargs := denoteArgs_eq_some_levelArgs hΓ hvl args hwf.1
      dsimp only [denote, validateRotPlanWithFlat]
      rw [hargs, validateRotPlanWith.eq_5]
      dsimp only [addArgsSet]
      have hk := validateRotPlanWithFlat_eq allowHdr p k (CtxTypes.push _ hΓ)
        (CtxLevels_pushTup_k hvl) hΔ hlm hwf.2
      rw [pushTup_length (Tup.levels bs vs.length) vs] at hk
      rw [hk]
    | _ =>
      dsimp only [denote, validateRotPlanWithFlat]
      repeat split
      all_goals rw [validateRotPlanWith.eq_def]
  | .jnzP tp ep, tf, Γ, Δ, vs, ls, inLD, inLE, hΓ, hvl, hΔ, hlm, hwf => by
    cases tf with
    | jnz c t e =>
      dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
      have hc := denoteArg_eq_some_levelArg hΓ hvl c hwf.1.1
      dsimp only [denote, validateRotPlanWithFlat]
      rw [hc, validateRotPlanWith.eq_6]
      rw [validateRotPlanWithFlat_eq allowHdr tp t hΓ hvl hΔ hlm hwf.1.2,
        validateRotPlanWithFlat_eq allowHdr ep e hΓ hvl hΔ hlm hwf.2]
    | jump j args =>
      rename_i ts
      cases tp with
      | leaf =>
        cases ep with
        | leaf =>
          dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
          obtain ⟨b, hlk, hres⟩ := lookupL_eq_some_resolveLabel hΔ hlm hwf.1
          have hargs := denoteArgs_eq_some_levelArgs hΓ hvl args hwf.2
          dsimp only [denote, validateRotPlanWithFlat]
          rw [hlk, hargs, hres, validateRotPlanWith.eq_7]
          dsimp only [addArgsSet]
          cases allowHdr <;> cases b <;> rfl
        | _ =>
          dsimp only [denote, validateRotPlanWithFlat]
          repeat split
          all_goals rw [validateRotPlanWith.eq_def]
      | _ =>
        dsimp only [denote, validateRotPlanWithFlat]
        repeat split
        all_goals rw [validateRotPlanWith.eq_def]
    | _ =>
      dsimp only [denote, validateRotPlanWithFlat]
      repeat split
      all_goals rw [validateRotPlanWith.eq_def]
  | .groupKeep bsP kP, tf, Γ, Δ, vs, ls, inLD, inLE, hΓ, hvl, hΔ, hlm, hwf => by
    cases tf with
    | group bs k =>
      rename_i sig
      dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
      dsimp only [denote, validateRotPlanWithFlat]
      rw [validateRotPlanWith.eq_8]
      dsimp only
      have hb := validateKeepBFlat_eq allowHdr bsP bs hΓ hvl (CtxTypes.push _ hΔ)
        (trieCtxMatch_insertTupEnv hlm (trueLabels sig)) hwf.1
      have hk := validateRotPlanWithFlat_eq allowHdr kP k hΓ hvl (CtxTypes.push _ hΔ)
        (trieCtxMatch_insertTupEnv hlm (trueLabels sig)) hwf.2
      rw [hb, hk]
    | _ =>
      dsimp only [denote, validateRotPlanWithFlat]
      repeat split
      all_goals rw [validateRotPlanWith.eq_def]
  | .groupRot dir hdr contMasks exitMode contP exitP entryP, tf,
      Γ, Δ, vs, ls, inLD, inLE, hΓ, hvl, hΔ, hlm, hwf => by
    cases tf with
    | group bs k =>
      rename_i sig
      cases sig with
      | nil =>
        cases bs
        dsimp only [denote, validateRotPlanWithFlat]
        rw [validateRotPlanWith.eq_10] <;> simp
      | cons ts sig' =>
        cases sig' with
        | cons _ _ =>
          cases bs
          rename_i bs'
          cases bs'
          dsimp only [denote, validateRotPlanWithFlat]
          rw [validateRotPlanWith.eq_10] <;> simp
        | nil =>
          cases bs with
          | cons b bs' =>
            cases bs'
            dsimp only [TFlat.wfCheck, TBlocks.wfCheck] at hwf
            simp only [Bool.and_eq_true] at hwf
            dsimp only [denote, denoteB, validateRotPlanWithFlat]
            rw [validateRotPlanWith.eq_9]
            simp only [Blocks.get]
            have hspec := validateHdrFlat_spec hdr b (CtxTypes.push _ hΓ)
              (CtxLevels_pushTup_k hvl) hwf.1.1
            have hlen : (pushTup (Tup.levels ts vs.length) vs).length =
                vs.length + ts.length := pushTup_length _ vs
            rw [hlen] at hspec
            cases hvh : validateHdrFlat hdr b (vs.length + ts.length) with
            | none =>
              rw [hvh] at hspec
              cases hspec with
              | isNone hnone =>
                have hT := hnone (CtxTypes.push ((true, ()) : Tup BoolL [ts]) hΔ)
                rw [hlen] at hT
                rw [hT]
                simp only [Bind.bind, Option.bind]
            | some val =>
              rcases val with ⟨sh, tF, eF, nv'⟩
              rw [hvh] at hspec
              cases hspec with
              | isSome _ _ _ _ hnv hΓ' hvl' hl' htF heF hsome =>
                have hT := hsome (CtxTypes.push ((true, ()) : Tup BoolL [ts]) hΔ)
                have hF := hsome (CtxTypes.push ((false, ()) : Tup BoolL [ts]) hΔ)
                rw [hlen] at hT hF
                rw [hT, hF]
                simp only [Bind.bind, Option.bind]
                have hsc := validateRotPlanWithFlat_eq (allowHdr || isPartialMasks hdr contMasks)
                  contP (if dir then tF else eF) hΓ' hvl'
                  (CtxTypes.push ((true, ()) : Tup BoolL [ts]) hΔ)
                  (trieCtxMatch_insertTupEnv (ts := [ts]) hlm ((true, ()) : Tup BoolL [ts]))
                  (by cases dir <;> assumption)
                have hsx := validateRotPlanWithFlat_eq allowHdr exitP (if dir then eF else tF)
                  hΓ' hvl' (CtxTypes.push ((false, ()) : Tup BoolL [ts]) hΔ)
                  (trieCtxMatch_insertTupEnv (ts := [ts]) hlm ((false, ()) : Tup BoolL [ts]))
                  (by cases dir <;> assumption)
                have hse := validateRotPlanWithFlat_eq allowHdr entryP k hΓ hvl
                  (CtxTypes.push ((true, ()) : Tup BoolL [ts]) hΔ)
                  (trieCtxMatch_insertTupEnv (ts := [ts]) hlm ((true, ()) : Tup BoolL [ts]))
                  hwf.2
                rw [hl', hlen] at hsc hsx
                have hle_t : insertTupEnv (ts := [ts]) inLD inLE (true, ()) =
                    inLE.insert inLD ⟨ts, true⟩ := rfl
                have hle_f : insertTupEnv (ts := [ts]) inLD inLE (false, ()) =
                    inLE.insert inLD ⟨ts, false⟩ := rfl
                dsimp only [pushTup, List.length] at hsc hsx hse ⊢
                rw [hle_t] at hsc hse
                rw [hle_f] at hsx
                simp only [Nat.zero_add] at hsc hsx hse
                cases dir <;> simp only [Bool.false_eq_true, ↓reduceIte] at hsc hsx ⊢ <;>
                  (rw [hsc, hsx, hse]; rfl)
    | _ =>
      dsimp only [denote, validateRotPlanWithFlat]
      repeat split
      all_goals rw [validateRotPlanWith.eq_def]

theorem validateKeepBFlat_eq {rs : List Ty} (allowHdr : Bool) :
    (ps : List RotPlan) → {sig : List (List Ty)} → (tb : TBlocks rs sig) →
    {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × K t)} → {ls : List ((ts : List Ty) × BoolL ts)} →
    {inLD : Nat} → {inLE : Trie ((ts : List Ty) × BoolL ts)} →
    CtxTypes Γ vs → CtxLevels vs → CtxTypes Δ ls → TrieCtxMatch inLD inLE ls →
    tb.wfCheck Γ Δ = true →
    validateRotPlanWith.validateKeepB allowHdr ps (denoteB K BoolL tb vs ls) vs.length =
      validateRotPlanWithFlat.validateKeepBFlat allowHdr ps tb vs.length inLD inLE
  | [], _, .nil, _, _, _, _, _, _, _, _, _, _, _ => by
    dsimp only [denoteB, validateRotPlanWithFlat.validateKeepBFlat]
    rw [validateRotPlanWith.validateKeepB.eq_1]
  | [], _, .cons _ _, _, _, _, _, _, _, _, _, _, _, _ => by
    dsimp only [denoteB, validateRotPlanWithFlat.validateKeepBFlat]
    rw [validateRotPlanWith.validateKeepB.eq_def]
  | _ :: _, _, .nil, _, _, _, _, _, _, _, _, _, _, _ => by
    dsimp only [denoteB, validateRotPlanWithFlat.validateKeepBFlat]
    rw [validateRotPlanWith.validateKeepB.eq_def]
  | p :: ps, _, .cons (ts := ts) b bs, Γ, Δ, vs, ls, inLD, inLE,
      hΓ, hvl, hΔ, hlm, hwf => by
    dsimp only [TBlocks.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denoteB, validateRotPlanWithFlat.validateKeepBFlat]
    rw [validateRotPlanWith.validateKeepB.eq_def]
    dsimp only
    have hb := validateRotPlanWithFlat_eq allowHdr p b (CtxTypes.push _ hΓ)
      (CtxLevels_pushTup_k hvl) hΔ hlm hwf.1
    rw [pushTup_length (Tup.levels ts vs.length) vs] at hb
    rw [hb, validateKeepBFlat_eq allowHdr ps bs hΓ hvl hΔ hlm hwf.2]
end

end OptFlatLoop
end LeanQbe.T
