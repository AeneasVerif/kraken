module

public import LeanQbe.T.Dce
public import LeanQbe.T.OptUtilLemmas

/-!
# Soundness and Relational Well-Formedness of Dead-Code Elimination (`T6`, `O-M2`)

* `OpCode.wp_exists`: any satisfied `OpCode.wp` guarantees existence of output tuples (exhibiting
  the canonical quiet NaN witness via `isFloatNaN_packedNaN` when quantifiers arise from NaNs,
  and discharging undefined behavior by `False.elim`).
* `dceWith_wp` and `dceWith_wf`, both proved via `Wf.induct`, with `dce_wp` / `dce_wf`
  specialized to `(true, false)`.
* `Func.dceWith_wf` / `Func.dceWith_spec`, plus `Func.dce_wf`, `Func.dce_spec`,
  `Func.deadLoadElim_wf`, and `Func.deadLoadElim_spec` for closed functions.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T

/-! ## Shared `NoneDead` / `Arg.InSet` transport helpers -/

theorem NoneDead.append_some_addArgKeys {V : Ty → Type} {s : Trie Unit}
    {Gk : Ctx K (OptV V)} {sig ts : List Ty} (argsk : Tup (Arg K) sig) (b : Nat)
    (xs : Tup V ts) (hnd : NoneDead (addArgKeys argsk s) Gk) :
    NoneDead s (Tup.zip (Tup.levels ts b) (someTup ts xs) ++ Gk) :=
  NoneDead.append_some (NoneDead.sub (TrieSub.addArgKeys argsk _) hnd) (Tup.levels ts b) xs

theorem NoneDead.append_none_of_not_keep {V : Ty → Type} {dl : Bool} {s : Trie Unit}
    {Gk : Ctx K (OptV V)} {ts : List Ty} (b : Nat)
    (hkeep : (!dl || anyLive b ts.length s) = false) (hnd : NoneDead s Gk) :
    NoneDead s (Tup.zip (Tup.levels ts b) (noneTup (V := V) ts) ++ Gk) := by
  have hal : anyLive b ts.length s = false := by cases dl <;> simp at hkeep ⊢; exact hkeep
  intro _ _ _ hm ho
  exact NoneDead.append_none hnd b (anyLive_eq_false ts.length b _ hal) hm ho

theorem NoneDead.cons_some_addArgKey {V : Ty → Type} {s : Trie Unit}
    {Gk : Ctx K (OptV V)} {sig : Ty} (ak : Arg K sig) {t : Ty} (b : Nat) (v : V t)
    (hnd : NoneDead (addArgKey ak s) Gk) :
    NoneDead s (⟨t, b, some v⟩ :: Gk) :=
  NoneDead.cons_some (NoneDead.sub (TrieSub.addArgKey ak _) hnd) b v

theorem NoneDead.cons_none_of_not_keep {V : Ty → Type} {dld : Bool} {s : Trie Unit}
    {Gk : Ctx K (OptV V)} {t : Ty} (b : Nat)
    (hkeep : (!dld || (s.find? b).isSome) = false) (hnd : NoneDead s Gk) :
    NoneDead s (⟨t, b, none⟩ :: Gk) := by
  have hmem : (s.find? b).isSome = false := by cases dld <;> simp at hkeep ⊢; exact hkeep
  intro _ _ _ hm ho
  exact NoneDead.cons_none hnd b hmem hm ho

theorem NoneDead.sub_addArgKey2 {V : Ty → Type} {s : Trie Unit} {Gk : Ctx K (OptV V)}
    {t u : Ty} (vk : Arg K t) (ak : Arg K u)
    (hnd : NoneDead (addArgKey vk (addArgKey ak s)) Gk) :
    NoneDead s Gk :=
  hnd.sub (TrieSub.trans (TrieSub.addArgKey ak _) (TrieSub.addArgKey vk _))

theorem Arg.InSet.addArgKey2 {t u : Ty} (vk : Arg K t) (ak : Arg K u) (s : Trie Unit) :
    ak.InSet (LeanQbe.T.addArgKey vk (LeanQbe.T.addArgKey ak s)) :=
  Arg.InSet.mono (TrieSub.addArgKey vk (LeanQbe.T.addArgKey ak s)) (Arg.InSet.addArgKey ak s)

theorem NoneDead.sub_union_left_addArgKey {V : Ty → Type} {s₁ s₂ : Trie Unit}
    {Gk : Ctx K (OptV V)} (ck : Arg K .bool)
    (hnd : NoneDead (addArgKey ck (trieUnion s₁ s₂)) Gk) :
    NoneDead s₁ Gk :=
  hnd.sub (TrieSub.trans (TrieSub.union_left _ _) (TrieSub.addArgKey ck _))

theorem NoneDead.sub_union_right_addArgKey {V : Ty → Type} {s₁ s₂ : Trie Unit}
    {Gk : Ctx K (OptV V)} (ck : Arg K .bool)
    (hnd : NoneDead (addArgKey ck (trieUnion s₁ s₂)) Gk) :
    NoneDead s₂ Gk :=
  hnd.sub (TrieSub.trans (TrieSub.union_right _ _) (TrieSub.addArgKey ck _))

theorem NoneDead.fresh_nil {V : Ty → Type} (s : Trie Unit) {as : List Ty} (xs : Tup V as) :
    NoneDead s (Tup.zip (Tup.levels as 0) (someTup as xs)) := by
  rw [← List.append_nil (Tup.zip (Tup.levels as 0) (someTup as xs))]
  exact NoneDead.append_some (Gk := []) (fun {_ _ _} hm => nomatch hm) (Tup.levels as 0) xs

theorem SomeEq.fresh_nil {as : List Ty} (xs : Tup Val as) :
    SomeEq (Tup.zip (someTup as xs) xs) := by
  rw [← List.append_nil (Tup.zip (someTup as xs) xs)]
  exact SomeEq.append_some (G := []) (fun {_ _ _} hm => nomatch hm) xs

theorem DceRel.fresh_nil {V₁ V₂ : Ty → Type} {as : List Ty} (xs₁ : Tup V₁ as) (xs₂ : Tup V₂ as) :
    DceRel (Tup.zip (someTup as xs₁) (someTup as xs₂)) (Tup.zip xs₁ xs₂) := by
  rw [← List.append_nil (Tup.zip (someTup as xs₁) (someTup as xs₂)),
      ← List.append_nil (Tup.zip xs₁ xs₂)]
  exact DceRel.append_some (G := []) (G' := []) (fun {_ _ _} hm => nomatch hm) xs₁ xs₂

/-! ## Block liveness and sweep access lemmas -/

theorem liveVarsBWith_sub (dropLets dropLoads : Bool) {rs : List Ty} (b : Nat) :
    {sig : List (List Ty)} → (bk : Blocks K KL0 rs sig) → {ts : List Ty} → (i : Member ts sig) →
    TrieSub (liveVarsWith dropLets dropLoads (b + ts.length) (bk.get i (Tup.levels ts b))).1
      (liveVarsBWith dropLets dropLoads b bk).1
  | _ :: _, .cons _ _, _, .here =>
    TrieSub.union_left _ _
  | _ :: _, .cons _ tl, _, .there i =>
    TrieSub.trans (liveVarsBWith_sub dropLets dropLoads b tl i) (TrieSub.union_right _ _)

theorem dceSweepB_liveVarsBWith_get (dropLets dropLoads : Bool)
    {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} (b : Nat) :
    {sig : List (List Ty)} → (bk : Blocks K KL0 rs sig) → (bs : Blocks (OptV V) L rs sig) →
    ∀ {ts : List Ty} (i : Member ts sig) (xs : Tup V ts),
    (dceSweepB (liveVarsBWith dropLets dropLoads b bk).2 bs).get i xs =
      dceSweep (liveVarsWith dropLets dropLoads (b + ts.length) (bk.get i (Tup.levels ts b))).2
        (bs.get i (someTup ts xs))
  | _ :: _, .cons _ _, .cons _ _, _, .here, _ => rfl
  | _ :: _, .cons _ bkt, .cons _ bst, _, .there i', xs =>
    dceSweepB_liveVarsBWith_get dropLets dropLoads b bkt bst i' xs

/-! ## `dceWith_wp` and `dceWith_wf` via `Wf.induct` -/

/-- Weakest-precondition preservation for `dceSweep`, proved via `Wf.induct`. -/
theorem dceWith_wp (dropLets dropLoads : Bool) {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {G : Ctx (OptV Val) Val} {D : Ctx Cont Cont}
    {e₁ : Expr (OptV Val) Cont rs} {e₂ : Expr Val Cont rs}
    (hwf : Wf G D e₁ e₂) :
    (∀ p ∈ D, p.2.1 = p.2.2) →
    SomeEq G →
    ∀ {Gk : Ctx K (OptV Val)} {Dk : Ctx KL0 Cont} (b : Nat) (ek : Expr K KL0 rs),
      Wf Gk Dk ek e₁ → NoneDead (liveVarsWith dropLets dropLoads b ek).1 Gk →
      ∀ m, wp Γ Q X e₂ m →
        wp Γ Q X (dceSweep (liveVarsWith dropLets dropLoads b ek).2 e₁) m := by
  induction hwf using Wf.induct with
  | @let_ G D ts op₁ op₂ k₁ k₂ hop₁₂ _ ih =>
    intro hD hG Gk Dk b ek hwk hnd m hw
    rcases hwk.rhs_let with ⟨opk, kk, rfl, hopk, hkk⟩
    cases hop₁₂ with
    | @mk sig _ code args₁ args₂ hargs₁₂ =>
      cases hopk with
      | @mk _ _ _ argsk _ hargsk =>
        dsimp only [liveVarsWith] at hnd ⊢
        cases hkeep : (!dropLets || anyLive b ts.length
            (liveVarsWith dropLets dropLoads (b + ts.length) (kk (Tup.levels ts b))).1) with
        | true =>
          simp only [hkeep, ↓reduceIte] at hnd ⊢
          dsimp only [dceSweep, wp, Op.wp] at hw ⊢
          have hvals : vals (argsSweep args₁) = vals args₂ :=
            argsSweep_vals_of_inSet hnd hG hargsk hargs₁₂
              (ArgsInSet.addArgKeys argsk _)
          rw [hvals]
          refine OpCode.wp_mono code (vals args₂) (fun xs hkx => ?_) hw
          exact ih (someTup ts xs) xs hD (SomeEq.append_some hG xs)
            (b + ts.length) (kk (Tup.levels ts b))
            (hkk (Tup.levels ts b) (someTup ts xs))
            (NoneDead.append_some_addArgKeys argsk b xs hnd) m hkx
        | false =>
          simp only [hkeep, Bool.false_eq_true, ↓reduceIte] at hnd ⊢
          dsimp only [dceSweep]
          dsimp only [wp, Op.wp] at hw
          obtain ⟨xs₂, hxs₂⟩ := OpCode.wp_exists code (vals args₂) hw
          exact ih (noneTup ts) xs₂ hD (SomeEq.append_none hG xs₂)
            (b + ts.length) (kk (Tup.levels ts b))
            (hkk (Tup.levels ts b) (noneTup ts))
            (NoneDead.append_none_of_not_keep b hkeep hnd) m hxs₂
  | load t ha _ ih =>
    intro hD hG Gk Dk b ek hwk hnd m hw
    rcases hwk.rhs_load with ⟨ak, kk, rfl, hak, hkk⟩
    dsimp only [liveVarsWith] at hnd ⊢
    rcases hw with ⟨v, hv, hk⟩
    cases hkeep : (!dropLoads ||
        ((liveVarsWith dropLets dropLoads (b + 1) (kk b)).1.find? b).isSome) with
    | true =>
      simp only [hkeep, ↓reduceIte] at hnd ⊢
      dsimp only [dceSweep, wp]
      have hval := argSweep_val_of_inSet hnd hG hak ha (Arg.InSet.addArgKey ak _)
      rw [hval]
      refine ⟨v, hv, ?_⟩
      exact ih (some v) v hD (SomeEq.cons_some hG v) (b + 1) (kk b) (hkk b (some v))
        (NoneDead.cons_some_addArgKey ak b v hnd) m hk
    | false =>
      simp only [hkeep, Bool.false_eq_true, ↓reduceIte] at hnd ⊢
      dsimp only [dceSweep]
      exact ih none v hD (SomeEq.cons_none hG v) (b + 1) (kk b) (hkk b none)
        (NoneDead.cons_none_of_not_keep b hkeep hnd) m hk
  | store hv ha _ ih =>
    intro hD hG Gk Dk b ek hwk hnd m hw
    rcases hwk.rhs_store with ⟨vk, ak, kk, rfl, hvk, hak, hkk⟩
    dsimp only [liveVarsWith] at hnd ⊢
    dsimp only [dceSweep, wp] at hw ⊢
    have hvval := argSweep_val_of_inSet hnd hG hvk hv (Arg.InSet.addArgKey vk _)
    have haval := argSweep_val_of_inSet hnd hG hak ha (Arg.InSet.addArgKey2 vk ak _)
    rw [hvval, haval]
    exact ⟨hw.1, ih hD hG b kk hkk (NoneDead.sub_addArgKey2 vk ak hnd) _ hw.2⟩
  | @call _ _ f _ bs _ _ _ _ hargs _ ih =>
    intro hD hG Gk Dk b ek hwk hnd m hw
    rcases hwk.rhs_call with ⟨argsk, kk, rfl, hargsk, hkk⟩
    dsimp only [liveVarsWith] at hnd ⊢
    dsimp only [dceSweep, wp] at hw ⊢
    rcases hw with ⟨P, E, hΓ, hP, hE⟩
    have hvals := argsSweep_vals_of_inSet hnd hG hargsk hargs (ArgsInSet.addArgKeys argsk _)
    rw [hvals]
    refine ⟨P, E, hΓ, fun r m' hp => ?_, hE⟩
    exact ih (someTup bs r) r hD (SomeEq.append_some hG r) (b + bs.length) (kk (Tup.levels bs b))
      (hkk (Tup.levels bs b) (someTup bs r))
      (NoneDead.append_some_addArgKeys argsk b r hnd) m' (hP r m' hp)
  | jnz hc _ _ iht ihe =>
    intro hD hG Gk Dk b ek hwk hnd m hw
    rcases hwk.rhs_jnz with ⟨ck, tk, ek', rfl, hck, htk, hek⟩
    dsimp only [liveVarsWith] at hnd ⊢
    dsimp only [dceSweep, wp] at hw ⊢
    have hval := argSweep_val_of_inSet hnd hG hck hc (Arg.InSet.addArgKey ck _)
    rw [hval]
    exact ⟨fun h => iht hD hG b tk htk (NoneDead.sub_union_left_addArgKey ck hnd) m (hw.1 h),
           fun h => ihe hD hG b ek' hek (NoneDead.sub_union_right_addArgKey ck hnd) m (hw.2 h)⟩
  | jump hj hargs =>
    intro hD hG Gk Dk b ek hwk hnd m hw
    rcases hwk.rhs_jump with ⟨jk, argsk, rfl, _, hargsk⟩
    have hj' := hD _ hj; dsimp only at hj'
    dsimp only [liveVarsWith] at hnd ⊢
    dsimp only [dceSweep, wp] at hw ⊢
    have hvals := argsSweep_vals_of_inSet hnd hG hargsk hargs (ArgsInSet.addArgKeys argsk _)
    rw [hj', hvals]
    exact hw
  | ret hvs =>
    intro _ hG Gk Dk b ek hwk hnd m hw
    rcases hwk.rhs_ret with ⟨vsk, rfl, hvsk⟩
    dsimp only [liveVarsWith] at hnd ⊢
    dsimp only [dceSweep, wp] at hw ⊢
    have hvals := argsSweep_vals_of_inSet hnd hG hvsk hvs (ArgsInSet.addArgKeys vsk _)
    rw [hvals]
    exact hw
  | exit f hargs =>
    intro _ hG Gk Dk b ek hwk hnd m hw
    rcases hwk.rhs_exit with ⟨argsk, rfl, hargsk⟩
    dsimp only [liveVarsWith] at hnd ⊢
    dsimp only [dceSweep, wp] at hw ⊢
    have hvals := argsSweep_vals_of_inSet hnd hG hargsk hargs (ArgsInSet.addArgKeys argsk _)
    rw [hvals]
    exact hw
  | hlt =>
    intro _ _ _ _ _ _ hwk _ _ hw
    rw [hwk.rhs_hlt]
    exact hw
  | @group G D sig b₁ b₂ k₁ k₂ _ _ ihb ihk =>
    intro hD hG Gk Dk b ek hwk hnd m hw
    rcases hwk.rhs_group with ⟨bk, kk, rfl, hbk, hkk⟩
    dsimp only [liveVarsWith] at hnd ⊢
    dsimp only [dceSweep, wp] at hw ⊢
    intro Js hclosed
    have hsub_k : TrieSub (liveVarsWith dropLets dropLoads b (kk (Tup.units sig))).1
        (trieUnion (liveVarsBWith dropLets dropLoads b (bk (Tup.units sig))).1
          (liveVarsWith dropLets dropLoads b (kk (Tup.units sig))).1) :=
      TrieSub.union_right _ _
    refine ihk Js Js (tup_zip_self_eq hD Js) hG b (kk (Tup.units sig)) (hkk (Tup.units sig) Js)
      (hnd.sub hsub_k) m (hw Js ?_)
    rw [closed_iff] at hclosed ⊢
    intro ts i xs m' hb'
    apply hclosed i xs m'
    rw [dceSweepB_liveVarsBWith_get dropLets dropLoads b (bk (Tup.units sig)) (b₁ Js) i xs]
    have hsub_b :
        TrieSub (liveVarsWith dropLets dropLoads (b + ts.length)
            ((bk (Tup.units sig)).get i (Tup.levels ts b))).1
          (trieUnion (liveVarsBWith dropLets dropLoads b (bk (Tup.units sig))).1
            (liveVarsWith dropLets dropLoads b (kk (Tup.units sig))).1) :=
      TrieSub.trans (liveVarsBWith_sub dropLets dropLoads b (bk (Tup.units sig)) i)
        (TrieSub.union_left _ _)
    exact ihb Js Js i (someTup ts xs) xs (tup_zip_self_eq hD Js) (SomeEq.append_some hG xs)
      (b + ts.length) ((bk (Tup.units sig)).get i (Tup.levels ts b))
      ((hbk (Tup.units sig) Js).get i (Tup.levels ts b) (someTup ts xs))
      (NoneDead.append_some (NoneDead.sub hsub_b hnd) (Tup.levels ts b) xs) m' hb'

/-- Well-formedness preservation for `dceSweep`, proved via `Wf.induct`. -/
theorem dceWith_wf (dropLets dropLoads : Bool)
    {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx (OptV V₁) (OptV V₂)} {D : Ctx L₁ L₂}
    {e₁ : Expr (OptV V₁) L₁ rs} {e₂ : Expr (OptV V₂) L₂ rs}
    (hwf : Wf G D e₁ e₂) :
    ∀ {G' : Ctx V₁ V₂}, DceRel G G' →
    ∀ {Gk : Ctx K (OptV V₁)} {Dk : Ctx KL0 L₁} (b : Nat) (ek : Expr K KL0 rs),
      Wf Gk Dk ek e₁ → NoneDead (liveVarsWith dropLets dropLoads b ek).1 Gk →
      Wf G' D (dceSweep (liveVarsWith dropLets dropLoads b ek).2 e₁)
        (dceSweep (liveVarsWith dropLets dropLoads b ek).2 e₂) := by
  induction hwf using Wf.induct with
  | @let_ G D ts op₁ op₂ k₁ k₂ hop₁₂ _ ih =>
    intro G' hrel Gk Dk b ek hwk hnd
    rcases hwk.rhs_let with ⟨opk, kk, rfl, hopk, hkk⟩
    cases hop₁₂ with
    | @mk sig _ code args₁ args₂ hargs₁₂ =>
      cases hopk with
      | @mk _ _ _ argsk _ hargsk =>
        dsimp only [liveVarsWith] at hnd ⊢
        cases hkeep : (!dropLets || anyLive b ts.length
            (liveVarsWith dropLets dropLoads (b + ts.length) (kk (Tup.levels ts b))).1) with
        | true =>
          simp only [hkeep, ↓reduceIte] at hnd ⊢
          dsimp only [dceSweep]
          refine .let_ (.mk code (TRel.argsSweep_of_inSet hnd hrel hargsk hargs₁₂
            (ArgsInSet.addArgKeys argsk _))) fun xs₁ xs₂ => ?_
          exact ih (someTup ts xs₁) (someTup ts xs₂) (DceRel.append_some hrel xs₁ xs₂)
            (b + ts.length) (kk (Tup.levels ts b))
            (hkk (Tup.levels ts b) (someTup ts xs₁))
            (NoneDead.append_some_addArgKeys argsk b xs₁ hnd)
        | false =>
          simp only [hkeep, Bool.false_eq_true, ↓reduceIte] at hnd ⊢
          dsimp only [dceSweep]
          exact ih (noneTup ts) (noneTup ts) (DceRel.append_none hrel)
            (b + ts.length) (kk (Tup.levels ts b))
            (hkk (Tup.levels ts b) (noneTup ts))
            (NoneDead.append_none_of_not_keep b hkeep hnd)
  | load t ha _ ih =>
    intro G' hrel Gk Dk b ek hwk hnd
    rcases hwk.rhs_load with ⟨ak, kk, rfl, hak, hkk⟩
    dsimp only [liveVarsWith] at hnd ⊢
    cases hkeep : (!dropLoads ||
        ((liveVarsWith dropLets dropLoads (b + 1) (kk b)).1.find? b).isSome) with
    | true =>
      simp only [hkeep, ↓reduceIte] at hnd ⊢
      dsimp only [dceSweep]
      refine .load t (argSweep_rel_of_inSet hnd hrel hak ha (Arg.InSet.addArgKey ak _))
        fun v₁ v₂ => ?_
      exact ih (some v₁) (some v₂) (DceRel.cons_some hrel v₁ v₂) (b + 1) (kk b)
        (hkk b (some v₁)) (NoneDead.cons_some_addArgKey ak b v₁ hnd)
    | false =>
      simp only [hkeep, Bool.false_eq_true, ↓reduceIte] at hnd ⊢
      dsimp only [dceSweep]
      exact ih none none (DceRel.cons_none hrel) (b + 1) (kk b) (hkk b none)
        (NoneDead.cons_none_of_not_keep b hkeep hnd)
  | store hv ha _ ih =>
    intro G' hrel Gk Dk b ek hwk hnd
    rcases hwk.rhs_store with ⟨vk, ak, kk, rfl, hvk, hak, hkk⟩
    dsimp only [liveVarsWith] at hnd ⊢
    dsimp only [dceSweep]
    exact .store (argSweep_rel_of_inSet hnd hrel hvk hv (Arg.InSet.addArgKey vk _))
      (argSweep_rel_of_inSet hnd hrel hak ha (Arg.InSet.addArgKey2 vk ak _))
      (ih hrel b kk hkk (NoneDead.sub_addArgKey2 vk ak hnd))
  | @call _ _ f _ bs _ _ _ _ hargs _ ih =>
    intro G' hrel Gk Dk b ek hwk hnd
    rcases hwk.rhs_call with ⟨argsk, kk, rfl, hargsk, hkk⟩
    dsimp only [liveVarsWith] at hnd ⊢
    dsimp only [dceSweep]
    refine .call f (TRel.argsSweep_of_inSet hnd hrel hargsk hargs (ArgsInSet.addArgKeys argsk _))
      fun xs₁ xs₂ => ?_
    exact ih (someTup bs xs₁) (someTup bs xs₂) (DceRel.append_some hrel xs₁ xs₂)
      (b + bs.length) (kk (Tup.levels bs b)) (hkk (Tup.levels bs b) (someTup bs xs₁))
      (NoneDead.append_some_addArgKeys argsk b xs₁ hnd)
  | jnz hc _ _ iht ihe =>
    intro G' hrel Gk Dk b ek hwk hnd
    rcases hwk.rhs_jnz with ⟨ck, tk, ek', rfl, hck, htk, hek⟩
    dsimp only [liveVarsWith] at hnd ⊢
    dsimp only [dceSweep]
    exact .jnz (argSweep_rel_of_inSet hnd hrel hck hc (Arg.InSet.addArgKey ck _))
      (iht hrel b tk htk (NoneDead.sub_union_left_addArgKey ck hnd))
      (ihe hrel b ek' hek (NoneDead.sub_union_right_addArgKey ck hnd))
  | jump hj hargs =>
    intro G' hrel Gk Dk b ek hwk hnd
    rcases hwk.rhs_jump with ⟨jk, argsk, rfl, _, hargsk⟩
    dsimp only [liveVarsWith] at hnd ⊢
    dsimp only [dceSweep]
    exact .jump hj (TRel.argsSweep_of_inSet hnd hrel hargsk hargs (ArgsInSet.addArgKeys argsk _))
  | ret hvs =>
    intro G' hrel Gk Dk b ek hwk hnd
    rcases hwk.rhs_ret with ⟨vsk, rfl, hvsk⟩
    dsimp only [liveVarsWith] at hnd ⊢
    dsimp only [dceSweep]
    exact .ret (TRel.argsSweep_of_inSet hnd hrel hvsk hvs (ArgsInSet.addArgKeys vsk _))
  | exit f hargs =>
    intro G' hrel Gk Dk b ek hwk hnd
    rcases hwk.rhs_exit with ⟨argsk, rfl, hargsk⟩
    dsimp only [liveVarsWith] at hnd ⊢
    dsimp only [dceSweep]
    exact .exit f (TRel.argsSweep_of_inSet hnd hrel hargsk hargs (ArgsInSet.addArgKeys argsk _))
  | hlt =>
    intro _ _ _ _ _ ek hwk _
    rw [hwk.rhs_hlt]
    exact .hlt
  | @group G D sig b₁ b₂ k₁ k₂ _ _ ihb ihk =>
    intro G' hrel Gk Dk b ek hwk hnd
    rcases hwk.rhs_group with ⟨bk, kk, rfl, hbk, hkk⟩
    dsimp only [liveVarsWith] at hnd ⊢
    dsimp only [dceSweep]
    have hsub_k : TrieSub (liveVarsWith dropLets dropLoads b (kk (Tup.units sig))).1
        (trieUnion (liveVarsBWith dropLets dropLoads b (bk (Tup.units sig))).1
          (liveVarsWith dropLets dropLoads b (kk (Tup.units sig))).1) :=
      TrieSub.union_right _ _
    refine .group (fun Js₁ Js₂ => WfB.of_get fun {ts} i xs₁ xs₂ => ?_)
      (fun Js₁ Js₂ => ihk Js₁ Js₂ hrel b (kk (Tup.units sig)) (hkk (Tup.units sig) Js₁)
        (hnd.sub hsub_k))
    rw [dceSweepB_liveVarsBWith_get dropLets dropLoads b (bk (Tup.units sig)) (b₁ Js₁) i xs₁,
        dceSweepB_liveVarsBWith_get dropLets dropLoads b (bk (Tup.units sig)) (b₂ Js₂) i xs₂]
    have hsub_b :
        TrieSub (liveVarsWith dropLets dropLoads (b + ts.length)
            ((bk (Tup.units sig)).get i (Tup.levels ts b))).1
          (trieUnion (liveVarsBWith dropLets dropLoads b (bk (Tup.units sig))).1
            (liveVarsWith dropLets dropLoads b (kk (Tup.units sig))).1) :=
      TrieSub.trans (liveVarsBWith_sub dropLets dropLoads b (bk (Tup.units sig)) i)
        (TrieSub.union_left _ _)
    exact ihb Js₁ Js₂ i (someTup ts xs₁) (someTup ts xs₂) (DceRel.append_some hrel xs₁ xs₂)
      (b + ts.length) ((bk (Tup.units sig)).get i (Tup.levels ts b))
      ((hbk (Tup.units sig) Js₁).get i (Tup.levels ts b) (someTup ts xs₁))
      (NoneDead.append_some (NoneDead.sub hsub_b hnd) _ _)

theorem dce_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {G : Ctx (OptV Val) Val} {D : Ctx Cont Cont}
    {e₁ : Expr (OptV Val) Cont rs} {e₂ : Expr Val Cont rs}
    (hwf : Wf G D e₁ e₂) :
    (∀ p ∈ D, p.2.1 = p.2.2) →
    SomeEq G →
    ∀ {Gk : Ctx K (OptV Val)} {Dk : Ctx KL0 Cont} (b : Nat) (ek : Expr K KL0 rs),
      Wf Gk Dk ek e₁ → NoneDead (liveVarsWith true false b ek).1 Gk →
      ∀ m, wp Γ Q X e₂ m → wp Γ Q X (dceSweep (liveVarsWith true false b ek).2 e₁) m :=
  dceWith_wp true false hwf

theorem dce_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx (OptV V₁) (OptV V₂)} {D : Ctx L₁ L₂}
    {e₁ : Expr (OptV V₁) L₁ rs} {e₂ : Expr (OptV V₂) L₂ rs}
    (hwf : Wf G D e₁ e₂) :
    ∀ {G' : Ctx V₁ V₂}, DceRel G G' →
    ∀ {Gk : Ctx K (OptV V₁)} {Dk : Ctx KL0 L₁} (b : Nat) (ek : Expr K KL0 rs),
      Wf Gk Dk ek e₁ → NoneDead (liveVarsWith true false b ek).1 Gk →
      Wf G' D (dceSweep (liveVarsWith true false b ek).2 e₁)
        (dceSweep (liveVarsWith true false b ek).2 e₂) :=
  dceWith_wf true false hwf

/-! ## Closed functions -/

theorem Func.dceWith_wf (dropLets dropLoads : Bool) {as rs : List Ty} {f : Func as rs}
    (hf : f.Wf) : (Func.dceWith dropLets dropLoads f).Wf := by
  intro V₁ V₂ L₁ L₂ xs₁ xs₂
  exact LeanQbe.T.dceWith_wf dropLets dropLoads
    (hf (OptV V₁) (OptV V₂) L₁ L₂ (someTup as xs₁) (someTup as xs₂))
    (DceRel.fresh_nil xs₁ xs₂) as.length (f K KL0 (Tup.levels as 0))
    (hf K (OptV V₁) KL0 L₁ (Tup.levels as 0) (someTup as xs₁)) (NoneDead.fresh_nil _ xs₁)

theorem Func.dceWith_spec (dropLets dropLoads : Bool) {as rs : List Ty} {f : Func as rs}
    (hf : f.Wf) {Γ : Env} {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Func.spec Γ f xs m Q X) : Func.spec Γ (Func.dceWith dropLets dropLoads f) xs m Q X :=
  LeanQbe.T.dceWith_wp dropLets dropLoads
    (hf (OptV Val) Val Cont Cont (someTup as xs) xs)
    (fun _ hm => nomatch hm) (SomeEq.fresh_nil xs) as.length (f K KL0 (Tup.levels as 0))
    (hf K (OptV Val) KL0 Cont (Tup.levels as 0) (someTup as xs)) (NoneDead.fresh_nil _ xs) m h

theorem Func.dce_wf {as rs : List Ty} {f : Func as rs} (hf : f.Wf) : (Func.dce f).Wf :=
  Func.dceWith_wf true false hf

/-- DCE refines function contracts: any source contract holds on `Func.dce f`. -/
theorem Func.dce_spec {as rs : List Ty} {f : Func as rs} (hf : f.Wf) {Γ : Env}
    {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Func.spec Γ f xs m Q X) : Func.spec Γ (Func.dce f) xs m Q X :=
  Func.dceWith_spec true false hf h

theorem Func.deadLoadElim_wf {as rs : List Ty} {f : Func as rs} (hf : f.Wf) :
    (Func.deadLoadElim f).Wf :=
  Func.dceWith_wf false true hf

/-- Dead-load elimination refines function contracts: any source contract holds on
`Func.deadLoadElim f`. -/
theorem Func.deadLoadElim_spec {as rs : List Ty} {f : Func as rs} (hf : f.Wf) {Γ : Env}
    {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Func.spec Γ f xs m Q X) : Func.spec Γ (Func.deadLoadElim f) xs m Q X :=
  Func.dceWith_spec false true hf h

end LeanQbe.T

