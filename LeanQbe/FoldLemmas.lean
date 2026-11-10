module

public import LeanQbe.Fold
public import LeanQbe.WfLemmas
import LeanQbe.OpsLemmas

/-!
# Correctness of `fold` (constant folding and copy propagation)

* `fold_wp`: the source `wp` implies the `wp` of the output. Read the input at `V' := Arg Val` next to
  the source at `Val`, related by `Wf` with `Good G` (every input variable denotes an operand whose value
  is the source variable's value) and equal labels.
* `fold_wf`: `Wf` is preserved; so the output can be fed to the next pass or to the lowering.
* `Func.fold_spec`, `Func.fold_wf`: the same for closed functions.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe

/-! ## Operands and operations -/

section
variable {V₁ V₂ : Type}

theorem ArgRel.imm?_eq {G : List (V₁ × V₂)} {a₁ : Arg V₁} {a₂ : Arg V₂} :
    ArgRel G a₁ a₂ → a₁.imm? = a₂.imm?
  | .var _ => rfl
  | .imm _ => rfl

theorem OpRel.toImm?_eq {G : List (V₁ × V₂)} {o₁ : Op V₁} {o₂ : Op V₂} (h : OpRel G o₁ o₂) :
    o₁.toImm? = o₂.toImm? := by
  cases h with
  | bin k o ha hb => simp only [Op.toImm?, ha.imm?_eq, hb.imm?_eq]
  | cmp k o ha hb => simp only [Op.toImm?, ha.imm?_eq, hb.imm?_eq]
  | ext k s sg ha => simp only [Op.toImm?, ha.imm?_eq]
  | copy k ha => simp only [Op.toImm?, ha.imm?_eq]

theorem OpRel.constVal?_eq {G : List (V₁ × V₂)} {o₁ : Op V₁} {o₂ : Op V₂} (h : OpRel G o₁ o₂) :
    o₁.constVal? = o₂.constVal? := by
  simp only [Op.constVal?, h.toImm?_eq]

theorem OpRel.copyL? {G : List (V₁ × V₂)} {o₁ : Op V₁} {o₂ : Op V₂} (h : OpRel G o₁ o₂) :
    (o₁.copyL? = none ∧ o₂.copyL? = none) ∨
      ∃ a₁ a₂, o₁.copyL? = some a₁ ∧ o₂.copyL? = some a₂ ∧ ArgRel G a₁ a₂ := by
  cases h with
  | copy k ha => cases k <;> simp_all [Op.copyL?]
  | _ => simp [Op.copyL?]

/-- Joining preserves relatedness, for a context `G` of operands related in `G'`. -/
theorem ArgRel.join {G : List (Arg V₁ × Arg V₂)} {G' : List (V₁ × V₂)}
    (hG : ∀ p ∈ G, ArgRel G' p.1 p.2) {a₁ : Arg (Arg V₁)} {a₂ : Arg (Arg V₂)} :
    ArgRel G a₁ a₂ → ArgRel G' a₁.join a₂.join
  | .var h => hG _ h
  | .imm c => .imm c

theorem Forall₂.join {G : List (Arg V₁ × Arg V₂)} {G' : List (V₁ × V₂)}
    (hG : ∀ p ∈ G, ArgRel G' p.1 p.2) :
    ∀ {as₁ as₂}, Forall₂ (ArgRel G) as₁ as₂ → Forall₂ (ArgRel G') (as₁.map Arg.join) (as₂.map Arg.join)
  | _, _, .nil => .nil
  | _, _, .cons h hs => .cons (h.join hG) (Forall₂.join hG hs)

theorem OpRel.join {G : List (Arg V₁ × Arg V₂)} {G' : List (V₁ × V₂)}
    (hG : ∀ p ∈ G, ArgRel G' p.1 p.2) {o₁ : Op (Arg V₁)} {o₂ : Op (Arg V₂)} :
    OpRel G o₁ o₂ → OpRel G' o₁.join o₂.join
  | .bin k o ha hb => .bin k o (ha.join hG) (hb.join hG)
  | .cmp k o ha hb => .cmp k o (ha.join hG) (hb.join hG)
  | .ext k s sg ha => .ext k s sg (ha.join hG)
  | .copy k ha => .copy k (ha.join hG)

end

/-- Every input variable denotes an operand with the value of the source variable. -/
def Good (G : List (Arg Val × Val)) : Prop := ∀ p ∈ G, p.1.val = p.2

theorem Good.cons {G : List (Arg Val × Val)} (hG : Good G) {a : Arg Val} {v : Val} (h : a.val = v) :
    Good ((a, v) :: G) := by
  intro p hp
  cases hp with
  | head => exact h
  | tail _ hp => exact hG p hp

theorem ArgRel.join_val {G : List (Arg Val × Val)} (hG : Good G) {a₁ : Arg (Arg Val)} {a₂ : Arg Val} :
    ArgRel G a₁ a₂ → a₁.join.val = a₂.val
  | .var h => hG _ h
  | .imm _ => rfl

theorem Forall₂.join_vals {G : List (Arg Val × Val)} (hG : Good G) :
    ∀ {as₁ : List (Arg (Arg Val))} {as₂ : List (Arg Val)}, Forall₂ (ArgRel G) as₁ as₂ →
      (as₁.map Arg.join).map Arg.val = as₂.map Arg.val
  | _, _, .nil => rfl
  | _, _, .cons h hs => by
    simp only [List.map_cons, h.join_val hG, Forall₂.join_vals hG hs]

theorem OpRel.join_eval {G : List (Arg Val × Val)} (hG : Good G) {o₁ : Op (Arg Val)} {o₂ : Op Val}
    (h : OpRel G o₁ o₂) : o₁.join.eval = o₂.eval := by
  cases h with
  | bin k o ha hb =>
    cases k <;> simp only [Op.join, Op.mapArgs, Op.eval, ha.join_val hG, hb.join_val hG]
  | cmp k o ha hb =>
    cases k <;> simp only [Op.join, Op.mapArgs, Op.eval, ha.join_val hG, hb.join_val hG]
  | ext k s sg ha => simp only [Op.join, Op.mapArgs, Op.eval, ha.join_val hG]
  | copy k ha => simp only [Op.join, Op.mapArgs, Op.eval, ha.join_val hG]

theorem Op.constVal?_eval {o : Op Val} {c : Val} (h : o.constVal? = some c) : o.eval = some c := by
  cases o with
  | bin k o a b => cases a <;> cases b <;> simp_all [Op.constVal?, Op.toImm?, Arg.imm?]
  | cmp k o a b => cases a <;> cases b <;> simp_all [Op.constVal?, Op.toImm?, Arg.imm?]
  | ext k s sg a => cases a <;> simp_all [Op.constVal?, Op.toImm?, Arg.imm?]
  | copy k a => cases a <;> simp_all [Op.constVal?, Op.toImm?, Arg.imm?]

theorem Op.copyL?_eval {o : Op Val} {a : Arg Val} (h : o.copyL? = some a) : o.eval = some a.val := by
  cases o with
  | copy k a' => cases k <;> simp_all [Op.copyL?, Op.eval, Cls.trunc]
  | _ => simp [Op.copyL?] at h

/-! ## `wp` preservation -/

theorem fold_wp {Γ : Env} {Q : Post} {X : XPost} :
    ∀ {G : List (Arg Val × Val)} {D : List (Cont × Cont)} {e₁ : Expr (Arg Val) Cont}
      {e₂ : Expr Val Cont}, Wf G D e₁ e₂ → Good G → (∀ p ∈ D, p.1 = p.2) →
    ∀ n args acc m, acc.length = n → wp Γ Q X e₂ args acc m → wp Γ Q X (fold n e₁) args acc m := by
  intro G D e₁ e₂ h
  induction h with
  | @let_ G D op₁ op₂ k₁ k₂ ho _ ih =>
    intro hG hD n args acc m hn hw
    simp only [wp, Op.wp] at hw
    obtain ⟨rfl, v, hv, hk⟩ := hw
    have he := ho.join_eval hG
    unfold fold
    split
    · next hn0 =>
      subst hn0
      have : acc = [] := List.eq_nil_of_length_eq_zero hn
      subst this
      split
      · next c hc =>
        have hvc : v = c := by
          rw [Op.constVal?_eval hc] at he; exact (Option.some.inj (he.trans hv)).symm
        subst hvc
        exact ih (.imm v) v (hG.cons rfl) hD 0 [] [] m rfl hk
      · split
        · next a ha =>
          have hva : v = a.val := by
            rw [Op.copyL?_eval ha] at he; exact (Option.some.inj (he.trans hv)).symm
          subst hva
          exact ih a a.val (hG.cons rfl) hD 0 [] [] m rfl hk
        · exact ⟨rfl, v, he ▸ hv, ih (.var v) v (hG.cons rfl) hD 0 [] [] m rfl hk⟩
    · exact ⟨rfl, v, he ▸ hv, ih (.var v) v (hG.cons rfl) hD 0 [] [] m rfl hk⟩
  | load c s sg ha _ ih =>
    intro hG hD n args acc m _ hw
    simp only [wp, fold] at hw ⊢
    obtain ⟨rfl, v, hv, hk⟩ := hw
    exact ⟨rfl, v, ha.join_val hG ▸ hv, ih (.var v) v (hG.cons rfl) hD 0 [] [] m rfl hk⟩
  | store s hv ha _ ih =>
    intro hG hD n args acc m _ hw
    simp only [wp, fold] at hw ⊢
    obtain ⟨rfl, hok, hk⟩ := hw
    rw [ha.join_val hG, hv.join_val hG]
    exact ⟨rfl, hok, ih hG hD 0 [] [] _ rfl hk⟩
  | call f has _ ih =>
    intro hG hD n args acc m _ hw
    simp only [wp, fold] at hw ⊢
    obtain ⟨rfl, P, E, hΓ, hP, hE⟩ := hw
    rw [has.join_vals hG]
    exact ⟨rfl, P, E, hΓ, fun rs m' hp => ih hG hD 0 rs [] m' rfl (hP rs m' hp), hE⟩
  | @jnz G D c₁ c₂ t₁ t₂ e₁ e₂ hc _ _ iht ihe =>
    intro hG hD n args acc m hn hw
    simp only [wp] at hw
    obtain ⟨rfl, ht, he⟩ := hw
    have hcv := hc.join_val hG
    unfold fold
    split
    · next hn0 =>
      subst hn0
      have : acc = [] := List.eq_nil_of_length_eq_zero hn
      subst this
      split
      · next c hcj =>
        rw [hcj] at hcv
        have hc2 : c = c₂.val := hcv
        subst hc2
        by_cases htr : Truthy c₂.val
        · simp only [htr, ↓reduceIte]; exact iht hG hD 0 [] [] m rfl (ht htr)
        · simp only [htr, ↓reduceIte]; exact ihe hG hD 0 [] [] m rfl (he htr)
      · next v hcj =>
        have hcv' : (Arg.var v : Arg Val).val = c₂.val := hcj ▸ hcv
        exact ⟨rfl, fun h => iht hG hD 0 [] [] m rfl (ht (hcv' ▸ h)),
          fun h => ihe hG hD 0 [] [] m rfl (he (hcv' ▸ h))⟩
    · exact ⟨rfl, fun h => iht hG hD 0 [] [] m rfl (ht (hcv ▸ h)),
        fun h => ihe hG hD 0 [] [] m rfl (he (hcv ▸ h))⟩
  | jump hj has =>
    intro hG hD n args acc m _ hw
    simp only [wp, fold] at hw ⊢
    have hj' := hD _ hj
    simp only at hj'
    subst hj'
    rw [has.join_vals hG]
    exact hw
  | ret has =>
    intro hG _ n args acc m _ hw
    simp only [wp, fold] at hw ⊢
    rw [has.join_vals hG]
    exact hw
  | exit f has =>
    intro hG _ n args acc m _ hw
    simp only [wp, fold] at hw ⊢
    rw [has.join_vals hG]
    exact hw
  | hlt => intro _ _ _ _ _ _ _ hw; simp only [wp] at hw
  | param _ ih =>
    intro hG hD n args acc m _ hw
    cases args with
    | nil => simp only [wp] at hw
    | cons a as =>
      simp only [wp, fold] at hw ⊢
      exact ih (.var a) a (hG.cons rfl) hD 0 as [] m rfl hw
  | label _ ih =>
    intro hG hD n args acc m hn hw
    simp only [wp, fold] at hw ⊢
    refine ⟨hw.1, fun J => ih J J hG ?_ (n + 1) [] (acc ++ [J]) m (by simp [hn]) (hw.2 J)⟩
    intro p hp
    cases hp with
    | head => rfl
    | tail _ hp => exact hD p hp
  | block _ _ ihb ihr =>
    intro hG hD n args acc m hn hw
    cases acc with
    | nil => simp only [wp, and_false] at hw
    | cons J acc' =>
      simp only [wp, fold] at hw ⊢
      refine ⟨hw.1, fun hJ => ihr hG hD (n - 1) [] acc' m (by simp at hn; omega) (hw.2 ?_)⟩
      exact fun as m' hb => hJ as m' (ihb hG hD 0 as [] m' rfl hb)

/-! ## `Wf` preservation -/

private theorem cons_rel {V₁ V₂ : Type} {G : List (Arg V₁ × Arg V₂)} {G' : List (V₁ × V₂)}
    (hG : ∀ p ∈ G, ArgRel G' p.1 p.2) {a₁ : Arg V₁} {a₂ : Arg V₂} (h : ArgRel G' a₁ a₂) :
    ∀ p ∈ (a₁, a₂) :: G, ArgRel G' p.1 p.2 := by
  intro p hp
  cases hp with
  | head => exact h
  | tail _ hp => exact hG p hp

private theorem cons_var {V₁ V₂ : Type} {G : List (Arg V₁ × Arg V₂)} {G' : List (V₁ × V₂)}
    (hG : ∀ p ∈ G, ArgRel G' p.1 p.2) (v₁ : V₁) (v₂ : V₂) :
    ∀ p ∈ (Arg.var v₁, Arg.var v₂) :: G, ArgRel ((v₁, v₂) :: G') p.1 p.2 := by
  intro p hp
  cases hp with
  | head => exact .var (List.Mem.head _)
  | tail _ hp => exact (hG p hp).weaken fun q hq => List.Mem.tail _ hq

theorem fold_wf {V₁ V₂ L₁ L₂ : Type} :
    ∀ {G : List (Arg V₁ × Arg V₂)} {D : List (L₁ × L₂)} {e₁ : Expr (Arg V₁) L₁}
      {e₂ : Expr (Arg V₂) L₂}, Wf G D e₁ e₂ →
    ∀ {G' : List (V₁ × V₂)}, (∀ p ∈ G, ArgRel G' p.1 p.2) → ∀ n, Wf G' D (fold n e₁) (fold n e₂) := by
  intro G D e₁ e₂ h
  induction h with
  | @let_ G D op₁ op₂ k₁ k₂ ho _ ih =>
    intro G' hG n
    have ho' := ho.join hG
    have hc := ho'.constVal?_eq
    simp only [fold]
    rw [hc]
    split
    · rcases ho'.copyL? with ⟨h1, h2⟩ | ⟨a₁, a₂, h1, h2, ha⟩
      · rw [h1, h2]
        cases op₂.join.constVal? with
        | some c => exact ih _ _ (cons_rel hG (.imm c)) 0
        | none => exact .let_ ho' fun v₁ v₂ => ih _ _ (cons_var hG v₁ v₂) 0
      · rw [h1, h2]
        cases op₂.join.constVal? with
        | some c => exact ih _ _ (cons_rel hG (.imm c)) 0
        | none => exact ih _ _ (cons_rel hG ha) 0
    · exact .let_ ho' fun v₁ v₂ => ih _ _ (cons_var hG v₁ v₂) 0
  | load c s sg ha _ ih =>
    intro G' hG n
    exact .load c s sg (ha.join hG) fun v₁ v₂ => ih _ _ (cons_var hG v₁ v₂) 0
  | store s hv ha _ ih => intro G' hG n; exact .store s (hv.join hG) (ha.join hG) (ih hG 0)
  | call f has _ ih => intro G' hG n; exact .call f (has.join hG) (ih hG 0)
  | @jnz G D c₁ c₂ t₁ t₂ e₁ e₂ hc _ _ iht ihe =>
    intro G' hG n
    have hc' := hc.join hG
    simp only [fold]
    split
    · cases hc with
      | var h =>
        have h' := hG _ h
        simp only [Arg.join] at h' ⊢
        cases h' with
        | var h'' => exact .jnz (.var h'') (iht hG 0) (ihe hG 0)
        | imm c => dsimp only; split <;> first | exact iht hG 0 | exact ihe hG 0
      | imm c => dsimp only [Arg.join]; split <;> first | exact iht hG 0 | exact ihe hG 0
    · exact .jnz hc' (iht hG 0) (ihe hG 0)
  | jump hj has => intro G' hG n; exact .jump hj (has.join hG)
  | ret has => intro G' hG n; exact .ret (has.join hG)
  | exit f has => intro G' hG n; exact .exit f (has.join hG)
  | hlt => intro _ _ _; exact .hlt
  | param _ ih => intro G' hG n; exact .param fun v₁ v₂ => ih _ _ (cons_var hG v₁ v₂) 0
  | label _ ih => intro G' hG n; exact .label fun j₁ j₂ => ih j₁ j₂ hG (n + 1)
  | block _ _ ihb ihr => intro G' hG n; exact .block (ihb hG 0) (ihr hG (n - 1))

/-! ## Closed functions -/

theorem Func.fold_wf {f : Func} (hf : f.Wf) : (Func.fold f).Wf :=
  fun V₁ V₂ L₁ L₂ => LeanQbe.fold_wf (hf (Arg V₁) (Arg V₂) L₁ L₂) (fun _ hp => nomatch hp) 0

/-- Folding refines the contract: every run of the source satisfying `Q` / `X` is matched. -/
theorem Func.fold_spec {f : Func} (hf : f.Wf) {Γ : Env} {args : List Val} {m : Mem 64}
    {Q : Post} {X : XPost} (h : Func.spec Γ f args m Q X) : Func.spec Γ (Func.fold f) args m Q X :=
  LeanQbe.fold_wp (hf (Arg Val) Val Cont Cont) (fun _ hp => nomatch hp) (fun _ hp => nomatch hp) 0 args [] m
    rfl h

end LeanQbe
