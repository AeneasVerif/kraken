module

public import LeanQbe.T.OptFlatLoop
import LeanQbe.T.FlatDirectLemmas
import LeanQbe.T.PassFlatKit
import LeanQbe.T.OptFlatSimKit
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
open OptFlatSimKit
open LoopRotate

private theorem CtxLevels_cons_k {t : Ty} {vs : List ((t : Ty) × K t)}
    (hvl : CtxLevels vs) : CtxLevels (⟨t, vs.length⟩ :: vs) :=
  CtxLevels.cons hvl t

private theorem CtxLevels_pushTup_k {ts : List Ty} {vs : List ((t : Ty) × K t)}
    (hvl : CtxLevels vs) : CtxLevels (pushTup (Tup.levels ts vs.length) vs) :=
  CtxLevels.pushTup hvl

private theorem validateLeafFlat_both :
    (∀ {rs : List Ty} (tf : TFlat rs) {Γ Δ vs ls inLD inLE} (_ : Unit),
      CtxTypes Γ vs → CtxLevels vs → (CtxTypes Δ ls ∧ TrieCtxMatch inLD inLE ls) →
      tf.wfCheck Γ Δ = true →
      validateLeaf (denote K BoolL tf vs ls) vs.length = validateLeafFlat tf vs.length inLD inLE) ∧
    (∀ {rs : List Ty} {sig : List (List Ty)} (tb : TBlocks rs sig) {Γ Δ vs ls inLD inLE}
      (_ : Unit),
      CtxTypes Γ vs → CtxLevels vs → (CtxTypes Δ ls ∧ TrieCtxMatch inLD inLE ls) →
      tb.wfCheck Γ Δ = true →
      validateLeaf.validateLeafB (denoteB K BoolL tb vs ls) vs.length =
        validateLeafBFlat tb vs.length inLD inLE) := by
  refine scanSim_mutual ⟨
    fun _ op _ hΓ hvl _ hwf ih => by
      obtain ⟨ha, _⟩ := wf_let hwf
      have hargs := denoteArgs_eq_some_levelArgs hΓ hvl op.args ha
      dsimp only [denote, validateLeafFlat]; rw [hargs]; dsimp only [validateLeaf, addArgsSet]
      have hk := ih (); rw [pushTup_length _ _] at hk; rw [hk],
    fun _ _ a _ hΓ hvl _ hwf ih => by
      obtain ⟨ha, _⟩ := wf_load hwf
      have ha' := denoteArg_eq_some_levelArg hΓ hvl a ha
      dsimp only [denote, validateLeafFlat]; rw [ha']; dsimp only [validateLeaf]
      have hk := ih (); dsimp only [List.length] at hk; rw [hk],
    fun _ v a _ hΓ hvl _ hwf ih => by
      obtain ⟨hv, ha, _⟩ := wf_store hwf
      have hv' := denoteArg_eq_some_levelArg hΓ hvl v hv
      have ha' := denoteArg_eq_some_levelArg hΓ hvl a ha
      dsimp only [denote, validateLeafFlat]; rw [hv', ha']; dsimp only [validateLeaf]; rw [ih ()],
    fun _ _ _ args _ hΓ hvl _ hwf ih => by
      obtain ⟨ha, _⟩ := wf_call hwf
      have hargs := denoteArgs_eq_some_levelArgs hΓ hvl args ha
      dsimp only [denote, validateLeafFlat]; rw [hargs]; dsimp only [validateLeaf, addArgsSet]
      have hk := ih (); rw [pushTup_length _ _] at hk; rw [hk],
    fun _ c _ _ hΓ hvl _ hwf iht ihe => by
      obtain ⟨hc, _, _⟩ := wf_jnz hwf
      have hc' := denoteArg_eq_some_levelArg hΓ hvl c hc
      dsimp only [denote, validateLeafFlat]; rw [hc']; dsimp only [validateLeaf]
      rw [iht (), ihe ()],
    fun _ j args hΓ hvl hlr hwf => by
      obtain ⟨hj, ha⟩ := wf_jump hwf
      obtain ⟨b, hlk, hres⟩ := lookupL_eq_some_resolveLabel hlr.1 hlr.2 hj
      have hargs := denoteArgs_eq_some_levelArgs hΓ hvl args ha
      dsimp only [denote, validateLeafFlat]; rw [hlk, hargs, hres]
      dsimp only [validateLeaf, addArgsSet]; cases b <;> rfl,
    fun _ vs' hΓ hvl _ hwf => by
      have hvs := denoteArgs_eq_some_levelArgs hΓ hvl vs' hwf
      dsimp only [denote, validateLeafFlat]; rw [hvs]; rfl,
    fun _ _ args hΓ hvl _ hwf => by
      have hargs := denoteArgs_eq_some_levelArgs hΓ hvl args hwf
      dsimp only [denote, validateLeafFlat]; rw [hargs]; rfl,
    fun _ _ _ _ _ => rfl,
    @fun _ sig _ Δ vs _ _ _ _ bodies k _ _ hlr hwf ihB ihK => by
      obtain ⟨hb, hk⟩ := wf_group hwf
      dsimp only [denote, validateLeafFlat, validateLeaf]
      have hlr' : CtxTypes (pushTypes sig Δ) (pushTup (trueLabels sig) _) ∧
          TrieCtxMatch (_ + sig.length) (insertTupEnv _ _ (trueLabels sig))
            (pushTup (trueLabels sig) _) :=
        ⟨ctxTypes_pushTup_rev _ hlr.1, trieCtxMatch_insertTupEnv hlr.2 (trueLabels sig)⟩
      rw [ihB () hlr' hb, ihK () hlr' hk],
    fun _ _ _ _ _ => rfl,
    fun _ _ _ _ _ _ _ ih ihs => by
      dsimp only [denoteB, validateLeafBFlat, validateLeaf.validateLeafB]
      have hb := ih (); rw [pushTup_length _ _] at hb; rw [hb, ihs ()]⟩

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
  | .let_ _ _, _ | .load _ _ _, _ | .store _ _ _, _ | .call _ _ _, _ | .jump _ _, _ | .ret _, _
  | .exit _ _, _ | .hlt, _ | .group _ _, _ => rfl

private theorem validateHdr_let_none {rs : List Ty} (dts : List Ty) (ss : HdrPlan) (nv : Nat) :
    {e : Expr K BoolL rs} → (match e with | .let_ _ _ => False | _ => True) →
    validateHdr (.let_ dts :: ss) e nv = none
  | .let_ _ _, h => False.elim h
  | .jnz _ _ _, _ | .load _ _ _, _ | .store _ _ _, _ | .call _ _ _, _ | .jump _ _, _ | .ret _, _
  | .exit _ _, _ | .hlt, _ | .group _ _, _ => rfl

private theorem validateHdr_load_none {rs : List Ty} (t : Ty) (ss : HdrPlan) (nv : Nat) :
    {e : Expr K BoolL rs} → (match e with | .load _ _ _ => False | _ => True) →
    validateHdr (.load t :: ss) e nv = none
  | .load _ _ _, h => False.elim h
  | .jnz _ _ _, _ | .let_ _ _, _ | .store _ _ _, _ | .call _ _ _, _ | .jump _ _, _ | .ret _, _
  | .exit _ _, _ | .hlt, _ | .group _ _, _ => rfl

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

local macro "vh_miss" h:ident : tactic => `(tactic| (
  refine ValidateHdrSpec.isNone fun _ => ?_
  dsimp only [denote]; repeat (first | split | (apply $h; trivial))))

private theorem validateHdrFlat_spec {rs : List Ty} :
    (hdr : HdrPlan) → (tf : TFlat rs) → {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × K t)} →
    CtxTypes Γ vs → CtxLevels vs → tf.wfCheck Γ Δ = true →
    ValidateHdrSpec hdr tf Γ Δ vs (validateHdrFlat hdr tf vs.length)
  | [], tf, Γ, Δ, vs, hΓ, hvl, hwf => by
    cases tf with
    | jnz c t e =>
      obtain ⟨hc, ht, he⟩ := wf_jnz hwf
      refine ValidateHdrSpec.isSome (addArgKey (levelArg vs.length c) .empty) t e vs.length
        rfl hΓ hvl rfl ht he fun _ => ?_
      dsimp only [denote]; rw [denoteArg_eq_some_levelArg hΓ hvl c hc]; rfl
    | _ => vh_miss validateHdr_nil_none
  | .let_ dts :: ss, tf, Γ, Δ, vs, hΓ, hvl, hwf => by
    cases tf with
    | let_ op k =>
      rename_i dts'
      obtain ⟨ha, hk⟩ := wf_let hwf
      dsimp only [validateHdrFlat]
      cases hdec : tysDecEq dts dts' with
      | isFalse _ =>
        refine ValidateHdrSpec.isNone fun _ => ?_
        dsimp only [denote]; rw [denoteArgs_eq_some_levelArgs hΓ hvl op.args ha]
        dsimp only [validateHdr]; rw [hdec]
      | isTrue heq =>
        subst heq
        cases hsafe : isSafeHdrOp op.code with
        | false =>
          refine ValidateHdrSpec.isNone fun _ => ?_
          dsimp only [denote]; rw [denoteArgs_eq_some_levelArgs hΓ hvl op.args ha]
          dsimp only [validateHdr]; rw [hdec]; simp [hsafe]
        | true =>
          have ih := validateHdrFlat_spec ss k (CtxTypes.push _ hΓ) (CtxLevels_pushTup_k hvl) hk
          have hlen : (pushTup (Tup.levels dts vs.length) vs).length = vs.length + dts.length :=
            pushTup_length _ vs
          rw [hlen] at ih
          cases hvh : validateHdrFlat ss k (vs.length + dts.length) with
          | none =>
            rw [hvh] at ih
            refine ValidateHdrSpec.isNone fun hΔ => ?_
            dsimp only [denote]; rw [denoteArgs_eq_some_levelArgs hΓ hvl op.args ha]
            dsimp only [validateHdr]; rw [hdec]
            cases ih with | isNone hnone =>
              have hsub := hnone hΔ; rw [hlen] at hsub
              simp only [hsafe, ↓reduceIte]; rw [hsub]; rfl
          | some val =>
            rcases val with ⟨sh, tF, eF, nv'⟩; rw [hvh] at ih
            cases ih with | isSome _ _ _ _ hnv hΓ' hvl' hl' htF heF hsome =>
              simp only [↓reduceIte]
              refine ValidateHdrSpec.isSome (addArgKeys (levelArgs vs.length op.args) sh) tF eF nv'
                (by dsimp only [hdrStepCount, HdrStep.tys]; omega) hΓ' hvl'
                (by dsimp only [hdrVs, hdrStepCount, HdrStep.tys]; omega) htF heF fun hΔ => ?_
              dsimp only [denote]; rw [denoteArgs_eq_some_levelArgs hΓ hvl op.args ha]
              dsimp only [validateHdr, addArgsSet]; rw [hdec]
              have hsub := hsome hΔ; rw [hlen] at hsub
              simp only [hsafe, ↓reduceIte]; rw [hsub]; rfl
    | _ => vh_miss validateHdr_let_none
  | .load t :: ss, tf, Γ, Δ, vs, hΓ, hvl, hwf => by
    cases tf with
    | load t' a k =>
      obtain ⟨ha, hk⟩ := wf_load hwf
      dsimp only [validateHdrFlat]
      cases hdec : tyDecEq t t' with
      | isFalse _ =>
        refine ValidateHdrSpec.isNone fun _ => ?_
        dsimp only [denote]; rw [denoteArg_eq_some_levelArg hΓ hvl a ha]
        dsimp only [validateHdr]; rw [hdec]
      | isTrue heq =>
        subst heq
        have ih := validateHdrFlat_spec ss k (.cons hΓ) (CtxLevels_cons_k hvl) hk
        dsimp only [List.length] at ih
        cases hvh : validateHdrFlat ss k (vs.length + 1) with
        | none =>
          rw [hvh] at ih
          refine ValidateHdrSpec.isNone fun hΔ => ?_
          dsimp only [denote]; rw [denoteArg_eq_some_levelArg hΓ hvl a ha]
          dsimp only [validateHdr]; rw [hdec]
          cases ih with | isNone hnone =>
            have hsub := hnone hΔ; dsimp only [List.length] at hsub; dsimp only; rw [hsub]; rfl
        | some val =>
          rcases val with ⟨sh, tF, eF, nv'⟩; rw [hvh] at ih
          cases ih with | isSome _ _ _ _ hnv hΓ' hvl' hl' htF heF hsome =>
            dsimp only [hdrStepCount, HdrStep.tys, List.length] at hnv hl' ⊢
            refine ValidateHdrSpec.isSome (addArgKey (levelArg vs.length a) sh) tF eF nv'
              (by dsimp only [hdrStepCount, HdrStep.tys, List.length]; omega) hΓ' hvl'
              (by dsimp only [hdrVs, hdrStepCount, HdrStep.tys, List.length]; rw [hl']; omega)
              htF heF fun hΔ => ?_
            dsimp only [denote]; rw [denoteArg_eq_some_levelArg hΓ hvl a ha]
            dsimp only [validateHdr]; rw [hdec]
            have hsub := hsome hΔ; dsimp only [List.length] at hsub; dsimp only; rw [hsub]; rfl
    | _ => vh_miss validateHdr_load_none

local macro "val_rot_mismatch" : tactic => `(tactic| (
  dsimp only [denote, validateRotPlanWithFlat]; repeat split
  all_goals rw [validateRotPlanWith.eq_def]))

mutual
theorem validateRotPlanWithFlat_eq {rs : List Ty} (allowHdr : Bool) :
    (plan : RotPlan) → (tf : TFlat rs) → {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × K t)} → {ls : List ((ts : List Ty) × BoolL ts)} →
    {inLD : Nat} → {inLE : Trie ((ts : List Ty) × BoolL ts)} →
    CtxTypes Γ vs → CtxLevels vs → CtxTypes Δ ls → TrieCtxMatch inLD inLE ls →
    tf.wfCheck Γ Δ = true →
    validateRotPlanWith allowHdr plan (denote K BoolL tf vs ls) vs.length =
      validateRotPlanWithFlat allowHdr plan tf vs.length inLD inLE
  | .leaf, tf, _, _, _, _, _, _, hΓ, hvl, hΔ, hlm, hwf => by
    rw [validateRotPlanWith.eq_1]; exact validateLeafFlat_both.1 tf () hΓ hvl ⟨hΔ, hlm⟩ hwf
  | .letP p, tf, Γ, Δ, vs, ls, inLD, inLE, hΓ, hvl, hΔ, hlm, hwf => by
    cases tf with
    | let_ op k =>
      rename_i ts; obtain ⟨ha, hk⟩ := wf_let hwf
      dsimp only [denote, validateRotPlanWithFlat]
      rw [denoteArgs_eq_some_levelArgs hΓ hvl op.args ha, validateRotPlanWith.eq_2]
      dsimp only [addArgsSet]
      have hk' := validateRotPlanWithFlat_eq allowHdr p k (CtxTypes.push _ hΓ)
        (CtxLevels_pushTup_k hvl) hΔ hlm hk
      rw [pushTup_length (Tup.levels ts vs.length) vs] at hk'; rw [hk']
    | _ => val_rot_mismatch
  | .loadP p, tf, Γ, Δ, vs, ls, inLD, inLE, hΓ, hvl, hΔ, hlm, hwf => by
    cases tf with
    | load _ a k =>
      obtain ⟨ha, hk⟩ := wf_load hwf
      dsimp only [denote, validateRotPlanWithFlat]
      rw [denoteArg_eq_some_levelArg hΓ hvl a ha, validateRotPlanWith.eq_3]
      have hk' := validateRotPlanWithFlat_eq allowHdr p k (.cons hΓ)
        (CtxLevels_cons_k hvl) hΔ hlm hk
      dsimp only [List.length] at hk'; rw [hk']
    | _ => val_rot_mismatch
  | .storeP p, tf, Γ, Δ, vs, ls, inLD, inLE, hΓ, hvl, hΔ, hlm, hwf => by
    cases tf with
    | store v a k =>
      obtain ⟨hv, ha, hk⟩ := wf_store hwf
      dsimp only [denote, validateRotPlanWithFlat]
      rw [denoteArg_eq_some_levelArg hΓ hvl v hv, denoteArg_eq_some_levelArg hΓ hvl a ha,
        validateRotPlanWith.eq_4]
      rw [validateRotPlanWithFlat_eq allowHdr p k hΓ hvl hΔ hlm hk]
    | _ => val_rot_mismatch
  | .callP p, tf, Γ, Δ, vs, ls, inLD, inLE, hΓ, hvl, hΔ, hlm, hwf => by
    cases tf with
    | call _ bs args k =>
      obtain ⟨ha, hk⟩ := wf_call hwf
      dsimp only [denote, validateRotPlanWithFlat]
      rw [denoteArgs_eq_some_levelArgs hΓ hvl args ha, validateRotPlanWith.eq_5]
      dsimp only [addArgsSet]
      have hk' := validateRotPlanWithFlat_eq allowHdr p k (CtxTypes.push _ hΓ)
        (CtxLevels_pushTup_k hvl) hΔ hlm hk
      rw [pushTup_length (Tup.levels bs vs.length) vs] at hk'; rw [hk']
    | _ => val_rot_mismatch
  | .jnzP tp ep, tf, Γ, Δ, vs, ls, inLD, inLE, hΓ, hvl, hΔ, hlm, hwf => by
    cases tf with
    | jnz c t e =>
      obtain ⟨hc, ht, he⟩ := wf_jnz hwf
      dsimp only [denote, validateRotPlanWithFlat]
      rw [denoteArg_eq_some_levelArg hΓ hvl c hc, validateRotPlanWith.eq_6,
        validateRotPlanWithFlat_eq allowHdr tp t hΓ hvl hΔ hlm ht,
        validateRotPlanWithFlat_eq allowHdr ep e hΓ hvl hΔ hlm he]
    | jump j args =>
      cases tp with
      | leaf =>
        cases ep with
        | leaf =>
          obtain ⟨hj, ha⟩ := wf_jump hwf
          obtain ⟨b, hlk, hres⟩ := lookupL_eq_some_resolveLabel hΔ hlm hj
          dsimp only [denote, validateRotPlanWithFlat]
          rw [hlk, denoteArgs_eq_some_levelArgs hΓ hvl args ha, hres, validateRotPlanWith.eq_7]
          dsimp only [addArgsSet]; cases allowHdr <;> cases b <;> rfl
        | _ => val_rot_mismatch
      | _ => val_rot_mismatch
    | _ => val_rot_mismatch
  | .groupKeep bsP kP, tf, Γ, Δ, vs, ls, inLD, inLE, hΓ, hvl, hΔ, hlm, hwf => by
    cases tf with
    | group bs k =>
      rename_i sig; obtain ⟨hb, hk⟩ := wf_group hwf
      dsimp only [denote, validateRotPlanWithFlat]; rw [validateRotPlanWith.eq_8]; dsimp only
      rw [validateKeepBFlat_eq allowHdr bsP bs hΓ hvl (CtxTypes.push _ hΔ)
          (trieCtxMatch_insertTupEnv hlm (trueLabels sig)) hb,
        validateRotPlanWithFlat_eq allowHdr kP k hΓ hvl (CtxTypes.push _ hΔ)
          (trieCtxMatch_insertTupEnv hlm (trueLabels sig)) hk]
    | _ => val_rot_mismatch
  | .groupRot dir hdr contMasks _ contP exitP entryP, tf,
      Γ, Δ, vs, ls, inLD, inLE, hΓ, hvl, hΔ, hlm, hwf => by
    cases tf with
    | group bs k =>
      rename_i sig
      cases sig with
      | nil => cases bs; val_rot_mismatch
      | cons ts sig' =>
        cases sig' with
        | cons _ _ => cases bs; rename_i bs'; cases bs'; val_rot_mismatch
        | nil =>
          cases bs with
          | cons b bs' =>
            cases bs'
            obtain ⟨hb0, hk0⟩ := wf_group hwf; obtain ⟨hb1, _⟩ := wf_cons hb0
            dsimp only [denote, denoteB, validateRotPlanWithFlat]
            rw [validateRotPlanWith.eq_9]; simp only [Blocks.get]
            have hspec := validateHdrFlat_spec hdr b (CtxTypes.push _ hΓ)
              (CtxLevels_pushTup_k hvl) hb1
            have hlen : (pushTup (Tup.levels ts vs.length) vs).length =
                vs.length + ts.length := pushTup_length _ vs
            rw [hlen] at hspec
            cases hvh : validateHdrFlat hdr b (vs.length + ts.length) with
            | none =>
              rw [hvh] at hspec
              cases hspec with | isNone hnone =>
                have hT := hnone (CtxTypes.push ((true, ()) : Tup BoolL [ts]) hΔ)
                rw [hlen] at hT; rw [hT]; simp only [Bind.bind, Option.bind]
            | some val =>
              rcases val with ⟨sh, tF, eF, nv'⟩; rw [hvh] at hspec
              cases hspec with | isSome _ _ _ _ hnv hΓ' hvl' hl' htF heF hsome =>
                have hT := hsome (CtxTypes.push ((true, ()) : Tup BoolL [ts]) hΔ)
                have hF := hsome (CtxTypes.push ((false, ()) : Tup BoolL [ts]) hΔ)
                rw [hlen] at hT hF; rw [hT, hF]; simp only [Bind.bind, Option.bind]
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
                  (trieCtxMatch_insertTupEnv (ts := [ts]) hlm ((true, ()) : Tup BoolL [ts])) hk0
                rw [hl', hlen] at hsc hsx
                dsimp only [pushTup, List.length] at hsc hsx hse ⊢
                have hle_t : insertTupEnv (ts := [ts]) inLD inLE (true, ()) =
                    inLE.insert inLD ⟨ts, true⟩ := rfl
                have hle_f : insertTupEnv (ts := [ts]) inLD inLE (false, ()) =
                    inLE.insert inLD ⟨ts, false⟩ := rfl
                rw [hle_t] at hsc hse; rw [hle_f] at hsx; simp only [Nat.zero_add] at hsc hsx hse
                cases dir <;> simp only [Bool.false_eq_true, ↓reduceIte] at hsc hsx ⊢ <;>
                  (rw [hsc, hsx, hse]; rfl)
    | _ => val_rot_mismatch

theorem validateKeepBFlat_eq {rs : List Ty} (allowHdr : Bool) :
    (ps : List RotPlan) → {sig : List (List Ty)} → (tb : TBlocks rs sig) →
    {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × K t)} → {ls : List ((ts : List Ty) × BoolL ts)} →
    {inLD : Nat} → {inLE : Trie ((ts : List Ty) × BoolL ts)} →
    CtxTypes Γ vs → CtxLevels vs → CtxTypes Δ ls → TrieCtxMatch inLD inLE ls →
    tb.wfCheck Γ Δ = true →
    validateRotPlanWith.validateKeepB allowHdr ps (denoteB K BoolL tb vs ls) vs.length =
      validateRotPlanWithFlat.validateKeepBFlat allowHdr ps tb vs.length inLD inLE
  | [], _, .nil, _, _, _, _, _, _, _, _, _, _, _
  | [], _, .cons _ _, _, _, _, _, _, _, _, _, _, _, _
  | _ :: _, _, .nil, _, _, _, _, _, _, _, _, _, _, _ => by
    dsimp only [denoteB, validateRotPlanWithFlat.validateKeepBFlat]
    rw [validateRotPlanWith.validateKeepB.eq_def]
  | p :: ps, _, .cons (ts := ts) b bs, Γ, Δ, vs, ls, inLD, inLE,
      hΓ, hvl, hΔ, hlm, hwf => by
    obtain ⟨hb0, hbs0⟩ := wf_cons hwf
    dsimp only [denoteB, validateRotPlanWithFlat.validateKeepBFlat]
    rw [validateRotPlanWith.validateKeepB.eq_def]; dsimp only
    have hb := validateRotPlanWithFlat_eq allowHdr p b (CtxTypes.push _ hΓ)
      (CtxLevels_pushTup_k hvl) hΔ hlm hb0
    rw [pushTup_length (Tup.levels ts vs.length) vs] at hb
    rw [hb, validateKeepBFlat_eq allowHdr ps bs hΓ hvl hΔ hlm hbs0]
end

end OptFlatLoop
end LeanQbe.T