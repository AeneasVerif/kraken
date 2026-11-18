module

public import LeanQbe.T.Wf
public import LeanQbe.T.TyLemmas

/-!
# Lemmas about `LeanQbe.T.Wf`

* Context inclusion helpers and weakening (`ArgRel.weaken`, `OpRel.weaken`, `Wf.weaken`,
  `WfB.weaken`).
* Positional block access and reconstruction (`WfB.get`, `WfB.of_get`).
* Dependent one-motive induction principle `Wf.induct` / `WfB.induct_get`, usable via
  `induction hwf using Wf.induct`.
* Symmetry (`ArgRel.symm`, `OpRel.symm`, `Wf.symm`, `WfB.symm`) and inversion / congruence helpers.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

/-! ## Context inclusion helpers -/

theorem cons_sub {α : Type} {p : α} {G G' : List α} (h : ∀ q ∈ G, q ∈ G') :
    ∀ q ∈ p :: G, q ∈ p :: G' := by
  intro q hq
  rcases List.mem_cons.1 hq with rfl | hq
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ (h q hq)

theorem append_sub_left {α : Type} (H : List α) {G G' : List α} (h : ∀ q ∈ G, q ∈ G') :
    ∀ q ∈ H ++ G, q ∈ H ++ G' := by
  intro q hq
  rcases List.mem_append.1 hq with hq | hq
  · exact List.mem_append_left _ hq
  · exact List.mem_append_right _ (h q hq)

/-! ## Weakening of `ArgRel` and `OpRel` -/

section
variable {V₁ V₂ : Ty → Type} {G G' : Ctx V₁ V₂}

theorem ArgRel.weaken (hG : ∀ p ∈ G, p ∈ G') {t : Ty} {a₁ : Arg V₁ t} {a₂ : Arg V₂ t} :
    ArgRel G t a₁ a₂ → ArgRel G' t a₁ a₂
  | .var hm => .var (hG _ hm)
  | .imm c => .imm c

theorem TRel.argRel_weaken (hG : ∀ p ∈ G, p ∈ G') {ts : List Ty}
    {as₁ : Tup (Arg V₁) ts} {as₂ : Tup (Arg V₂) ts} :
    TRel (ArgRel G) as₁ as₂ → TRel (ArgRel G') as₁ as₂ :=
  TRel.mono fun _ _ _ h => h.weaken hG

theorem OpRel.weaken (hG : ∀ p ∈ G, p ∈ G') {rs : List Ty} {op₁ : Op V₁ rs} {op₂ : Op V₂ rs} :
    OpRel G op₁ op₂ → OpRel G' op₁ op₂
  | .mk code hargs => .mk code (TRel.argRel_weaken hG hargs)

end

/-! ## Positional block access and reconstruction for `WfB` -/

/-- Project the well-formedness derivation for block `i` in a `WfB` derivation. -/
theorem WfB.get {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} :
    {sig : List (List Ty)} → {bs₁ : Blocks V₁ L₁ rs sig} → {bs₂ : Blocks V₂ L₂ rs sig} →
    WfB G D bs₁ bs₂ → ∀ {ts} (i : Member ts sig) (xs₁ : Tup V₁ ts) (xs₂ : Tup V₂ ts),
      Wf (Tup.zip xs₁ xs₂ ++ G) D (bs₁.get i xs₁) (bs₂.get i xs₂)
  | _, _, _, .cons hb _, _, .here, xs₁, xs₂ => hb xs₁ xs₂
  | _, _, _, .cons _ hbs, _, .there i, xs₁, xs₂ => WfB.get hbs i xs₁ xs₂

/-- Reconstruct `WfB G D bs₁ bs₂` from positional `Wf` derivations for every block index `i`. -/
theorem WfB.of_get {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} :
    {sig : List (List Ty)} → {bs₁ : Blocks V₁ L₁ rs sig} → {bs₂ : Blocks V₂ L₂ rs sig} →
    (∀ {ts} (i : Member ts sig) (xs₁ : Tup V₁ ts) (xs₂ : Tup V₂ ts),
      Wf (Tup.zip xs₁ xs₂ ++ G) D (bs₁.get i xs₁) (bs₂.get i xs₂)) →
    WfB G D bs₁ bs₂
  | [], .nil, .nil, _ => .nil
  | _ :: _, .cons _ _, .cons _ _, h =>
    .cons (fun xs₁ xs₂ => h .here xs₁ xs₂) (WfB.of_get (fun i => h (.there i)))

/-! ## Dependent one-motive induction principle `Wf.induct` -/

section
set_option linter.unusedSectionVars false
variable {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
  {motive : (G : Ctx V₁ V₂) → (D : Ctx L₁ L₂) → (e₁ : Expr V₁ L₁ rs) → (e₂ : Expr V₂ L₂ rs) →
    Wf G D e₁ e₂ → Prop}
  (let_ : ∀ {G D ts} {op₁ : Op V₁ ts} {op₂ : Op V₂ ts}
    {k₁ : Tup V₁ ts → Expr V₁ L₁ rs} {k₂ : Tup V₂ ts → Expr V₂ L₂ rs}
    (hop : OpRel G op₁ op₂)
    (hk : ∀ xs₁ xs₂, Wf (Tup.zip xs₁ xs₂ ++ G) D (k₁ xs₁) (k₂ xs₂)),
    (∀ xs₁ xs₂, motive _ _ _ _ (hk xs₁ xs₂)) →
    motive G D (.let_ op₁ k₁) (.let_ op₂ k₂) (.let_ hop hk))
  (load : ∀ {G D} (t : Ty) {a₁ a₂} {k₁ : V₁ t → Expr V₁ L₁ rs} {k₂ : V₂ t → Expr V₂ L₂ rs}
    (ha : ArgRel G i64 a₁ a₂)
    (hk : ∀ v₁ v₂, Wf (⟨t, v₁, v₂⟩ :: G) D (k₁ v₁) (k₂ v₂)),
    (∀ v₁ v₂, motive _ _ _ _ (hk v₁ v₂)) →
    motive G D (.load t a₁ k₁) (.load t a₂ k₂) (.load t ha hk))
  (store : ∀ {G D t} {v₁ : Arg V₁ t} {v₂ : Arg V₂ t} {a₁ a₂ k₁ k₂}
    (hv : ArgRel G t v₁ v₂) (ha : ArgRel G i64 a₁ a₂) (hk : Wf G D k₁ k₂),
    motive G D k₁ k₂ hk →
    motive G D (.store v₁ a₁ k₁) (.store v₂ a₂ k₂) (.store hv ha hk))
  (call : ∀ {G D} (f : Sym) {as bs args₁ args₂}
    {k₁ : Tup V₁ bs → Expr V₁ L₁ rs} {k₂ : Tup V₂ bs → Expr V₂ L₂ rs}
    (hargs : TRel (ArgRel G) args₁ args₂)
    (hk : ∀ xs₁ xs₂, Wf (Tup.zip xs₁ xs₂ ++ G) D (k₁ xs₁) (k₂ xs₂)),
    (∀ xs₁ xs₂, motive _ _ _ _ (hk xs₁ xs₂)) →
    motive G D (.call f (as := as) (bs := bs) args₁ k₁) (.call f args₂ k₂) (.call f hargs hk))
  (jnz : ∀ {G D c₁ c₂ t₁ t₂ e₁ e₂} (hc : ArgRel G .bool c₁ c₂)
    (ht : Wf G D t₁ t₂) (he : Wf G D e₁ e₂),
    motive G D t₁ t₂ ht → motive G D e₁ e₂ he →
    motive G D (.jnz c₁ t₁ e₁) (.jnz c₂ t₂ e₂) (.jnz hc ht he))
  (jump : ∀ {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {ts} {j₁ : L₁ ts} {j₂ : L₂ ts} {args₁ args₂}
    (hj : ⟨ts, j₁, j₂⟩ ∈ D) (hargs : TRel (ArgRel G) args₁ args₂),
    motive G D (.jump j₁ args₁) (.jump j₂ args₂) (.jump hj hargs))
  (ret : ∀ {G D vs₁ vs₂} (hvs : TRel (ArgRel G) vs₁ vs₂),
    motive G D (.ret vs₁) (.ret vs₂) (.ret hvs))
  (exit : ∀ {G D} (f : Sym) {as args₁ args₂} (hargs : TRel (ArgRel G) args₁ args₂),
    motive G D (.exit f (as := as) args₁) (.exit f args₂) (.exit f hargs))
  (hlt : ∀ {G D}, motive G D .hlt .hlt .hlt)
  (group : ∀ {G D sig} {b₁ : Tup L₁ sig → Blocks V₁ L₁ rs sig} {b₂ : Tup L₂ sig → Blocks V₂ L₂ rs sig}
    {k₁ : Tup L₁ sig → Expr V₁ L₁ rs} {k₂ : Tup L₂ sig → Expr V₂ L₂ rs}
    (hb : ∀ Js₁ Js₂, WfB G (Tup.zip Js₁ Js₂ ++ D) (b₁ Js₁) (b₂ Js₂))
    (hk : ∀ Js₁ Js₂, Wf G (Tup.zip Js₁ Js₂ ++ D) (k₁ Js₁) (k₂ Js₂)),
    (∀ Js₁ Js₂ {ts} (i : Member ts sig) xs₁ xs₂, motive _ _ _ _ ((hb Js₁ Js₂).get i xs₁ xs₂)) →
    (∀ Js₁ Js₂, motive _ _ _ _ (hk Js₁ Js₂)) →
    motive G D (.group (sig := sig) b₁ k₁) (.group b₂ k₂) (.group hb hk))

include let_ load store call jnz jump ret exit hlt group

mutual
/-- Dependent one-motive induction on `Wf`, usable with `induction hwf using Wf.induct`. -/
theorem Wf.induct : {G : Ctx V₁ V₂} → {D : Ctx L₁ L₂} → {e₁ : Expr V₁ L₁ rs} → {e₂ : Expr V₂ L₂ rs} →
    (h : Wf G D e₁ e₂) → motive G D e₁ e₂ h
  | _, _, _, _, .let_ hop hk => let_ hop hk fun xs₁ xs₂ => Wf.induct (hk xs₁ xs₂)
  | _, _, _, _, .load t ha hk => load t ha hk fun v₁ v₂ => Wf.induct (hk v₁ v₂)
  | _, _, _, _, .store hv ha hk => store hv ha hk (Wf.induct hk)
  | _, _, _, _, .call f hargs hk => call f hargs hk fun xs₁ xs₂ => Wf.induct (hk xs₁ xs₂)
  | _, _, _, _, .jnz hc ht he => jnz hc ht he (Wf.induct ht) (Wf.induct he)
  | _, _, _, _, .jump hj hargs => jump hj hargs
  | _, _, _, _, .ret hvs => ret hvs
  | _, _, _, _, .exit f hargs => exit f hargs
  | _, _, _, _, .hlt => hlt
  | _, _, _, _, .group hb hk => group hb hk
      (fun Js₁ Js₂ _ i xs₁ xs₂ => WfB.induct_get (hb Js₁ Js₂) i xs₁ xs₂)
      (fun Js₁ Js₂ => Wf.induct (hk Js₁ Js₂))

/-- Mutual helper for `Wf.induct`: induction on a block accessed by position `i`. -/
theorem WfB.induct_get : {G : Ctx V₁ V₂} → {D : Ctx L₁ L₂} → {sig : List (List Ty)} →
    {bs₁ : Blocks V₁ L₁ rs sig} → {bs₂ : Blocks V₂ L₂ rs sig} → (hbs : WfB G D bs₁ bs₂) →
    ∀ {ts} (i : Member ts sig) xs₁ xs₂, motive _ _ _ _ (hbs.get i xs₁ xs₂)
  | _, _, _, _, _, .cons hb _, _, .here, xs₁, xs₂ => Wf.induct (hb xs₁ xs₂)
  | _, _, _, _, _, .cons _ hbs, _, .there i, xs₁, xs₂ => WfB.induct_get hbs i xs₁ xs₂
end
end

/-! ## Weakening of `Wf` and `WfB` -/

/-- Weakening: `Wf` is preserved by enlarging both value and label contexts. -/
theorem Wf.weaken {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {e₁ : Expr V₁ L₁ rs} {e₂ : Expr V₂ L₂ rs}
    (h : Wf G D e₁ e₂) :
    ∀ {G' D'}, (∀ p ∈ G, p ∈ G') → (∀ p ∈ D, p ∈ D') → Wf G' D' e₁ e₂ := by
  induction h using Wf.induct with
  | let_ hop _ ih =>
    intro G' D' hG hD
    exact .let_ (hop.weaken hG) fun xs₁ xs₂ => ih xs₁ xs₂ (append_sub_left _ hG) hD
  | load t ha _ ih =>
    intro G' D' hG hD
    exact .load t (ha.weaken hG) fun v₁ v₂ => ih v₁ v₂ (cons_sub hG) hD
  | store hv ha _ ih =>
    intro G' D' hG hD
    exact .store (hv.weaken hG) (ha.weaken hG) (ih hG hD)
  | call f hargs _ ih =>
    intro G' D' hG hD
    exact .call f (TRel.argRel_weaken hG hargs) fun xs₁ xs₂ => ih xs₁ xs₂ (append_sub_left _ hG) hD
  | jnz hc _ _ iht ihe =>
    intro G' D' hG hD
    exact .jnz (hc.weaken hG) (iht hG hD) (ihe hG hD)
  | jump hj hargs =>
    intro G' D' hG hD
    exact .jump (hD _ hj) (TRel.argRel_weaken hG hargs)
  | ret hvs =>
    intro G' D' hG _
    exact .ret (TRel.argRel_weaken hG hvs)
  | exit f hargs =>
    intro G' D' hG _
    exact .exit f (TRel.argRel_weaken hG hargs)
  | hlt =>
    intro _ _ _ _
    exact .hlt
  | group _ _ ihb ihk =>
    intro G' D' hG hD
    exact .group
      (fun Js₁ Js₂ => WfB.of_get fun i xs₁ xs₂ =>
        ihb Js₁ Js₂ i xs₁ xs₂ (append_sub_left _ hG) (append_sub_left _ hD))
      (fun Js₁ Js₂ => ihk Js₁ Js₂ hG (append_sub_left _ hD))

/-- Weakening for `WfB`. -/
theorem WfB.weaken {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {sig : List (List Ty)}
    {bs₁ : Blocks V₁ L₁ rs sig} {bs₂ : Blocks V₂ L₂ rs sig}
    (hbs : WfB G D bs₁ bs₂) {G' D'} (hG : ∀ p ∈ G, p ∈ G') (hD : ∀ p ∈ D, p ∈ D') :
    WfB G' D' bs₁ bs₂ :=
  WfB.of_get fun i xs₁ xs₂ => (hbs.get i xs₁ xs₂).weaken (append_sub_left _ hG) hD

theorem Wf.weaken_G {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G G' : Ctx V₁ V₂} {D : Ctx L₁ L₂} {e₁ : Expr V₁ L₁ rs} {e₂ : Expr V₂ L₂ rs}
    (h : Wf G D e₁ e₂) (hG : ∀ p ∈ G, p ∈ G') : Wf G' D e₁ e₂ :=
  h.weaken hG fun _ hp => hp

theorem Wf.weaken_D {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D D' : Ctx L₁ L₂} {e₁ : Expr V₁ L₁ rs} {e₂ : Expr V₂ L₂ rs}
    (h : Wf G D e₁ e₂) (hD : ∀ p ∈ D, p ∈ D') : Wf G D' e₁ e₂ :=
  h.weaken (fun _ hp => hp) hD

theorem Wf.cons_G {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {e₁ : Expr V₁ L₁ rs} {e₂ : Expr V₂ L₂ rs}
    (p : (t : Ty) × V₁ t × V₂ t) (h : Wf G D e₁ e₂) : Wf (p :: G) D e₁ e₂ :=
  h.weaken_G fun _ hq => List.mem_cons_of_mem _ hq

theorem Wf.append_G {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G H : Ctx V₁ V₂} {D : Ctx L₁ L₂} {e₁ : Expr V₁ L₁ rs} {e₂ : Expr V₂ L₂ rs}
    (h : Wf G D e₁ e₂) : Wf (H ++ G) D e₁ e₂ :=
  h.weaken_G fun _ hq => List.mem_append_right H hq

theorem Wf.append_D {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D H : Ctx L₁ L₂} {e₁ : Expr V₁ L₁ rs} {e₂ : Expr V₂ L₂ rs}
    (h : Wf G D e₁ e₂) : Wf G (H ++ D) e₁ e₂ :=
  h.weaken_D fun _ hq => List.mem_append_right H hq

theorem Wf.congr {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G G' : Ctx V₁ V₂} {D D' : Ctx L₁ L₂} {e₁ : Expr V₁ L₁ rs} {e₂ : Expr V₂ L₂ rs}
    (hG : ∀ p, p ∈ G ↔ p ∈ G') (hD : ∀ p, p ∈ D ↔ p ∈ D') :
    Wf G D e₁ e₂ ↔ Wf G' D' e₁ e₂ :=
  ⟨fun h => h.weaken (fun p hp => (hG p).1 hp) (fun p hp => (hD p).1 hp),
   fun h => h.weaken (fun p hp => (hG p).2 hp) (fun p hp => (hD p).2 hp)⟩

theorem WfB.congr {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G G' : Ctx V₁ V₂} {D D' : Ctx L₁ L₂} {sig : List (List Ty)}
    {bs₁ : Blocks V₁ L₁ rs sig} {bs₂ : Blocks V₂ L₂ rs sig}
    (hG : ∀ p, p ∈ G ↔ p ∈ G') (hD : ∀ p, p ∈ D ↔ p ∈ D') :
    WfB G D bs₁ bs₂ ↔ WfB G' D' bs₁ bs₂ :=
  ⟨fun h => h.weaken (fun p hp => (hG p).1 hp) (fun p hp => (hD p).1 hp),
   fun h => h.weaken (fun p hp => (hG p).2 hp) (fun p hp => (hD p).2 hp)⟩

/-! ## Tuple & operation mapping congruence helpers -/

theorem TRel.cons_iff {α : Type} {f g : α → Type} {R : ∀ a, f a → g a → Prop}
    {a : α} {as : List α} {x : f a} {y : g a} {xs : Tup f as} {ys : Tup g as} :
    TRel R (as := a :: as) (x, xs) (y, ys) ↔ R a x y ∧ TRel R xs ys :=
  ⟨fun h => by cases h with | cons hx hxs => exact ⟨hx, hxs⟩, fun ⟨hx, hxs⟩ => .cons hx hxs⟩

theorem TRel.map {α : Type} {f₁ f₂ g₁ g₂ : α → Type}
    {R : ∀ a, f₁ a → f₂ a → Prop} {S : ∀ a, g₁ a → g₂ a → Prop}
    (m₁ : ∀ a, f₁ a → g₁ a) (m₂ : ∀ a, f₂ a → g₂ a)
    (hm : ∀ a x₁ x₂, R a x₁ x₂ → S a (m₁ a x₁) (m₂ a x₂)) :
    {as : List α} → {xs₁ : Tup f₁ as} → {xs₂ : Tup f₂ as} →
    TRel R xs₁ xs₂ → TRel S (xs₁.map m₁) (xs₂.map m₂)
  | [], (), (), .nil => .nil
  | _ :: _, (_, _), (_, _), .cons hx hxs => .cons (hm _ _ _ hx) (TRel.map m₁ m₂ hm hxs)

theorem ArgRel.mapV {V₁ V₂ W₁ W₂ : Ty → Type}
    {G : Ctx V₁ V₂} {G' : Ctx W₁ W₂}
    (m₁ : ∀ t, V₁ t → Arg W₁ t) (m₂ : ∀ t, V₂ t → Arg W₂ t)
    (hm : ∀ t v₁ v₂, ⟨t, v₁, v₂⟩ ∈ G → ArgRel G' t (m₁ t v₁) (m₂ t v₂))
    {t : Ty} {a₁ : Arg V₁ t} {a₂ : Arg V₂ t} :
    ArgRel G t a₁ a₂ → ArgRel G' t (match a₁ with | .var v => m₁ t v | .imm c => .imm c)
      (match a₂ with | .var v => m₂ t v | .imm c => .imm c)
  | .var h => hm _ _ _ h
  | .imm c => .imm c

theorem OpRel.mapV {V₁ V₂ W₁ W₂ : Ty → Type}
    {G : Ctx V₁ V₂} {G' : Ctx W₁ W₂}
    (m₁ : ∀ t, V₁ t → W₁ t) (m₂ : ∀ t, V₂ t → W₂ t)
    (hm : ∀ t v₁ v₂, ⟨t, v₁, v₂⟩ ∈ G → ⟨t, m₁ t v₁, m₂ t v₂⟩ ∈ G')
    {rs : List Ty} {op₁ : Op V₁ rs} {op₂ : Op V₂ rs} :
    OpRel G op₁ op₂ → OpRel G' (op₁.mapV m₁) (op₂.mapV m₂)
  | .mk code hargs =>
    .mk code (TRel.map (fun _ a => a.mapV m₁) (fun _ a => a.mapV m₂)
      (fun _ _ _ ha => match ha with
        | .var h => .var (hm _ _ _ h)
        | .imm c => .imm c) hargs)

/-! ## Symmetry and inversion / congruence lemmas -/

/-- Flip every pair in a relational context. -/
def Ctx.flip {α : Type} {f g : α → Type} (G : Ctx f g) : Ctx g f :=
  G.map fun ⟨a, x, y⟩ => ⟨a, y, x⟩

theorem mem_ctx_flip {α : Type} {f g : α → Type} {G : Ctx f g} {a : α} {x : f a} {y : g a}
    (h : ⟨a, x, y⟩ ∈ G) : ⟨a, y, x⟩ ∈ G.flip :=
  List.mem_map.2 ⟨⟨a, x, y⟩, h, rfl⟩

theorem Tup.zip_flip {α : Type} {f g : α → Type} :
    {as : List α} → (xs₁ : Tup f as) → (xs₂ : Tup g as) →
    (Tup.zip xs₁ xs₂).flip = Tup.zip xs₂ xs₁
  | [], _, _ => rfl
  | _ :: _, xs₁, xs₂ => congrArg (_ :: ·) (Tup.zip_flip xs₁.2 xs₂.2)

theorem Ctx.flip_append {α : Type} {f g : α → Type} (G H : Ctx f g) :
    (G ++ H).flip = G.flip ++ H.flip :=
  List.map_append ..

section
variable {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type}

theorem ArgRel.symm {G : Ctx V₁ V₂} {t : Ty} {a₁ : Arg V₁ t} {a₂ : Arg V₂ t} :
    ArgRel G t a₁ a₂ → ArgRel G.flip t a₂ a₁
  | .var hm => .var (mem_ctx_flip hm)
  | .imm c => .imm c

theorem TRel.argRel_symm {G : Ctx V₁ V₂} :
    {ts : List Ty} → {as₁ : Tup (Arg V₁) ts} → {as₂ : Tup (Arg V₂) ts} →
    TRel (ArgRel G) as₁ as₂ → TRel (ArgRel G.flip) as₂ as₁
  | [], _, _, .nil => .nil
  | _ :: _, (_, _), (_, _), .cons h hs => .cons h.symm (TRel.argRel_symm hs)

theorem OpRel.symm {G : Ctx V₁ V₂} {rs : List Ty} {op₁ : Op V₁ rs} {op₂ : Op V₂ rs} :
    OpRel G op₁ op₂ → OpRel G.flip op₂ op₁
  | .mk code hargs => .mk code (TRel.argRel_symm hargs)

theorem Wf.symm {rs : List Ty} {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
    {e₁ : Expr V₁ L₁ rs} {e₂ : Expr V₂ L₂ rs} (h : Wf G D e₁ e₂) :
    Wf G.flip D.flip e₂ e₁ := by
  induction h using Wf.induct with
  | let_ hop _ ih =>
    exact .let_ hop.symm fun xs₂ xs₁ => by
      simpa [Ctx.flip_append, Tup.zip_flip] using ih xs₁ xs₂
  | load t ha _ ih =>
    exact .load t ha.symm fun v₂ v₁ => ih v₁ v₂
  | store hv ha _ ih =>
    exact .store hv.symm ha.symm ih
  | call f hargs _ ih =>
    exact .call f (TRel.argRel_symm hargs) fun xs₂ xs₁ => by
      simpa [Ctx.flip_append, Tup.zip_flip] using ih xs₁ xs₂
  | jnz hc _ _ iht ihe =>
    exact .jnz hc.symm iht ihe
  | jump hj hargs =>
    exact .jump (mem_ctx_flip hj) (TRel.argRel_symm hargs)
  | ret hvs =>
    exact .ret (TRel.argRel_symm hvs)
  | exit f hargs =>
    exact .exit f (TRel.argRel_symm hargs)
  | hlt =>
    exact .hlt
  | group _ _ ihb ihk =>
    exact .group
      (fun Js₂ Js₁ => WfB.of_get fun i xs₂ xs₁ => by
        simpa [Ctx.flip_append, Tup.zip_flip] using ihb Js₁ Js₂ i xs₁ xs₂)
      (fun Js₂ Js₁ => by
        simpa [Ctx.flip_append, Tup.zip_flip] using ihk Js₁ Js₂)

theorem WfB.symm {rs : List Ty} {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {sig : List (List Ty)}
    {bs₁ : Blocks V₁ L₁ rs sig} {bs₂ : Blocks V₂ L₂ rs sig} (hbs : WfB G D bs₁ bs₂) :
    WfB G.flip D.flip bs₂ bs₁ :=
  WfB.of_get fun i xs₂ xs₁ => by
    simpa [Ctx.flip_append, Tup.zip_flip] using (hbs.get i xs₁ xs₂).symm

end

/-- A well-formed closed function relates any instantiation to itself at identical inputs. -/
theorem Func.Wf.refl {as rs : List Ty} {f : Func as rs} (hwf : f.Wf)
    (V : Ty → Type) (L : List Ty → Type) (xs : Tup V as) :
    _root_.LeanQbe.T.Wf (Tup.zip xs xs) ([] : Ctx L L) (f V L xs) (f V L xs) :=
  hwf V V L L xs xs

theorem Wf.let_inv {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs ts : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {op₁ : Op V₁ ts} {op₂ : Op V₂ ts}
    {k₁ : Tup V₁ ts → Expr V₁ L₁ rs} {k₂ : Tup V₂ ts → Expr V₂ L₂ rs}
    (h : Wf G D (.let_ op₁ k₁) (.let_ op₂ k₂)) :
    OpRel G op₁ op₂ ∧ ∀ xs₁ xs₂, Wf (Tup.zip xs₁ xs₂ ++ G) D (k₁ xs₁) (k₂ xs₂) := by
  cases h with
  | let_ hop hk => exact ⟨hop, hk⟩

theorem Wf.load_inv {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {t : Ty} {a₁ : Arg V₁ i64} {a₂ : Arg V₂ i64}
    {k₁ : V₁ t → Expr V₁ L₁ rs} {k₂ : V₂ t → Expr V₂ L₂ rs}
    (h : Wf G D (.load t a₁ k₁) (.load t a₂ k₂)) :
    ArgRel G i64 a₁ a₂ ∧ ∀ v₁ v₂, Wf (⟨t, v₁, v₂⟩ :: G) D (k₁ v₁) (k₂ v₂) := by
  cases h with
  | load _ ha hk => exact ⟨ha, hk⟩

theorem Wf.store_inv {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {t : Ty} {v₁ : Arg V₁ t} {v₂ : Arg V₂ t}
    {a₁ : Arg V₁ i64} {a₂ : Arg V₂ i64} {k₁ : Expr V₁ L₁ rs} {k₂ : Expr V₂ L₂ rs}
    (h : Wf G D (.store v₁ a₁ k₁) (.store v₂ a₂ k₂)) :
    ArgRel G t v₁ v₂ ∧ ArgRel G i64 a₁ a₂ ∧ Wf G D k₁ k₂ := by
  cases h with
  | store hv ha hk => exact ⟨hv, ha, hk⟩

theorem Wf.jnz_inv {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {c₁ : Arg V₁ .bool} {c₂ : Arg V₂ .bool}
    {t₁ e₁ : Expr V₁ L₁ rs} {t₂ e₂ : Expr V₂ L₂ rs}
    (h : Wf G D (.jnz c₁ t₁ e₁) (.jnz c₂ t₂ e₂)) :
    ArgRel G .bool c₁ c₂ ∧ Wf G D t₁ t₂ ∧ Wf G D e₁ e₂ := by
  cases h with
  | jnz hc ht he => exact ⟨hc, ht, he⟩

theorem Wf.group_inv {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {sig : List (List Ty)}
    {b₁ : Tup L₁ sig → Blocks V₁ L₁ rs sig} {b₂ : Tup L₂ sig → Blocks V₂ L₂ rs sig}
    {k₁ : Tup L₁ sig → Expr V₁ L₁ rs} {k₂ : Tup L₂ sig → Expr V₂ L₂ rs}
    (h : Wf G D (.group b₁ k₁) (.group b₂ k₂)) :
    (∀ Js₁ Js₂, WfB G (Tup.zip Js₁ Js₂ ++ D) (b₁ Js₁) (b₂ Js₂)) ∧
    (∀ Js₁ Js₂, Wf G (Tup.zip Js₁ Js₂ ++ D) (k₁ Js₁) (k₂ Js₂)) := by
  cases h with
  | group hb hk => exact ⟨hb, hk⟩

theorem ArgRel.var_iff {V₁ V₂ : Ty → Type} {G : Ctx V₁ V₂} {t : Ty} {v₁ : V₁ t} {v₂ : V₂ t} :
    ArgRel G t (.var v₁) (.var v₂) ↔ ⟨t, v₁, v₂⟩ ∈ G :=
  ⟨fun h => by cases h with | var hm => exact hm, .var⟩

theorem ArgRel.imm_iff {V₁ V₂ : Ty → Type} {G : Ctx V₁ V₂} {t : Ty} {c₁ c₂ : Val t} :
    ArgRel G t (.imm c₁) (.imm c₂) ↔ c₁ = c₂ :=
  ⟨fun h => by cases h; rfl, fun h => h ▸ .imm c₁⟩

theorem OpRel.mk_iff {V₁ V₂ : Ty → Type} {G : Ctx V₁ V₂} {sig rs : List Ty}
    {code : OpCode sig rs} {args₁ : Tup (Arg V₁) sig} {args₂ : Tup (Arg V₂) sig} :
    OpRel G ⟨code, args₁⟩ ⟨code, args₂⟩ ↔ TRel (ArgRel G) args₁ args₂ :=
  ⟨fun h => by cases h with | mk _ ha => exact ha, .mk code⟩

theorem Wf.call_inv {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {f : Sym} {as bs : List Ty}
    {args₁ : Tup (Arg V₁) as} {args₂ : Tup (Arg V₂) as}
    {k₁ : Tup V₁ bs → Expr V₁ L₁ rs} {k₂ : Tup V₂ bs → Expr V₂ L₂ rs}
    (h : Wf G D (.call f args₁ k₁) (.call f args₂ k₂)) :
    TRel (ArgRel G) args₁ args₂ ∧
    ∀ xs₁ xs₂, Wf (Tup.zip xs₁ xs₂ ++ G) D (k₁ xs₁) (k₂ xs₂) := by
  cases h with
  | call _ hargs hk => exact ⟨hargs, hk⟩

theorem Wf.jump_inv {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs ts : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {j₁ : L₁ ts} {j₂ : L₂ ts}
    {args₁ : Tup (Arg V₁) ts} {args₂ : Tup (Arg V₂) ts}
    (h : Wf (rs := rs) G D (.jump j₁ args₁) (.jump j₂ args₂)) :
    ⟨ts, j₁, j₂⟩ ∈ D ∧ TRel (ArgRel G) args₁ args₂ := by
  cases h with
  | jump hj hargs => exact ⟨hj, hargs⟩

theorem Wf.ret_inv {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {vs₁ : Tup (Arg V₁) rs} {vs₂ : Tup (Arg V₂) rs}
    (h : Wf G D (.ret vs₁) (.ret vs₂)) : TRel (ArgRel G) vs₁ vs₂ := by
  cases h with
  | ret hvs => exact hvs

theorem Wf.exit_inv {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {f : Sym} {as : List Ty}
    {args₁ : Tup (Arg V₁) as} {args₂ : Tup (Arg V₂) as}
    (h : Wf (rs := rs) G D (.exit f args₁) (.exit f args₂)) : TRel (ArgRel G) args₁ args₂ := by
  cases h with
  | exit _ hargs => exact hargs

theorem WfB.cons_inv {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {ts : List Ty} {sig : List (List Ty)}
    {b₁ : Tup V₁ ts → Expr V₁ L₁ rs} {b₂ : Tup V₂ ts → Expr V₂ L₂ rs}
    {bs₁ : Blocks V₁ L₁ rs sig} {bs₂ : Blocks V₂ L₂ rs sig}
    (h : WfB G D (.cons b₁ bs₁) (.cons b₂ bs₂)) :
    (∀ xs₁ xs₂, Wf (Tup.zip xs₁ xs₂ ++ G) D (b₁ xs₁) (b₂ xs₂)) ∧ WfB G D bs₁ bs₂ := by
  cases h with
  | cons hb hbs => exact ⟨hb, hbs⟩

/-! ## `Wf` right-hand-side inversion helpers -/

section
variable {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}

theorem Wf.rhs_let {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {ts : List Ty}
    {e₁ : Expr V₁ L₁ rs} {op₂ : Op V₂ ts} {k₂ : Tup V₂ ts → Expr V₂ L₂ rs}
    (h : Wf G D e₁ (.let_ op₂ k₂)) :
    ∃ op₁ k₁, e₁ = .let_ op₁ k₁ ∧ OpRel G op₁ op₂ ∧
      ∀ xs₁ xs₂, Wf (Tup.zip xs₁ xs₂ ++ G) D (k₁ xs₁) (k₂ xs₂) := by
  cases h with
  | let_ hop hk => exact ⟨_, _, rfl, hop, hk⟩

theorem Wf.rhs_load {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {t : Ty}
    {e₁ : Expr V₁ L₁ rs} {a₂ : Arg V₂ i64} {k₂ : V₂ t → Expr V₂ L₂ rs}
    (h : Wf G D e₁ (.load t a₂ k₂)) :
    ∃ a₁ k₁, e₁ = .load t a₁ k₁ ∧ ArgRel G i64 a₁ a₂ ∧
      ∀ v₁ v₂, Wf (⟨t, v₁, v₂⟩ :: G) D (k₁ v₁) (k₂ v₂) := by
  cases h with
  | load _ ha hk => exact ⟨_, _, rfl, ha, hk⟩

theorem Wf.rhs_store {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {t : Ty}
    {e₁ : Expr V₁ L₁ rs} {v₂ : Arg V₂ t} {a₂ : Arg V₂ i64} {k₂ : Expr V₂ L₂ rs}
    (h : Wf G D e₁ (.store v₂ a₂ k₂)) :
    ∃ v₁ a₁ k₁, e₁ = .store v₁ a₁ k₁ ∧ ArgRel G t v₁ v₂ ∧ ArgRel G i64 a₁ a₂ ∧ Wf G D k₁ k₂ := by
  cases h with
  | store hv ha hk => exact ⟨_, _, _, rfl, hv, ha, hk⟩

theorem Wf.rhs_call {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {f : Sym} {as bs : List Ty}
    {e₁ : Expr V₁ L₁ rs} {args₂ : Tup (Arg V₂) as} {k₂ : Tup V₂ bs → Expr V₂ L₂ rs}
    (h : Wf G D e₁ (.call f args₂ k₂)) :
    ∃ args₁ k₁, e₁ = .call f args₁ k₁ ∧ TRel (ArgRel G) args₁ args₂ ∧
      ∀ xs₁ xs₂, Wf (Tup.zip xs₁ xs₂ ++ G) D (k₁ xs₁) (k₂ xs₂) := by
  cases h with
  | call _ hargs hk => exact ⟨_, _, rfl, hargs, hk⟩

theorem Wf.rhs_jnz {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
    {e₁ : Expr V₁ L₁ rs} {c₂ : Arg V₂ .bool} {t₂ e₂ : Expr V₂ L₂ rs}
    (h : Wf G D e₁ (.jnz c₂ t₂ e₂)) :
    ∃ c₁ t₁ e₁', e₁ = .jnz c₁ t₁ e₁' ∧ ArgRel G .bool c₁ c₂ ∧ Wf G D t₁ t₂ ∧ Wf G D e₁' e₂ := by
  cases h with
  | jnz hc ht he => exact ⟨_, _, _, rfl, hc, ht, he⟩

theorem Wf.rhs_jump {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {ts : List Ty}
    {e₁ : Expr V₁ L₁ rs} {j₂ : L₂ ts} {args₂ : Tup (Arg V₂) ts}
    (h : Wf G D e₁ (.jump j₂ args₂)) :
    ∃ j₁ args₁, e₁ = .jump j₁ args₁ ∧ ⟨ts, j₁, j₂⟩ ∈ D ∧ TRel (ArgRel G) args₁ args₂ := by
  cases h with
  | jump hj hargs => exact ⟨_, _, rfl, hj, hargs⟩

theorem Wf.rhs_ret {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
    {e₁ : Expr V₁ L₁ rs} {vs₂ : Tup (Arg V₂) rs}
    (h : Wf G D e₁ (.ret vs₂)) :
    ∃ vs₁, e₁ = .ret vs₁ ∧ TRel (ArgRel G) vs₁ vs₂ := by
  cases h with
  | ret hvs => exact ⟨_, rfl, hvs⟩

theorem Wf.rhs_exit {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {f : Sym} {as : List Ty}
    {e₁ : Expr V₁ L₁ rs} {args₂ : Tup (Arg V₂) as}
    (h : Wf G D e₁ (.exit f args₂)) :
    ∃ args₁, e₁ = .exit f args₁ ∧ TRel (ArgRel G) args₁ args₂ := by
  cases h with
  | exit _ hargs => exact ⟨_, rfl, hargs⟩

theorem Wf.rhs_hlt {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {e₁ : Expr V₁ L₁ rs}
    (h : Wf G D e₁ .hlt) : e₁ = .hlt := by
  cases h; rfl

theorem Wf.rhs_group {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {sig : List (List Ty)}
    {e₁ : Expr V₁ L₁ rs} {b₂ : Tup L₂ sig → Blocks V₂ L₂ rs sig}
    {k₂ : Tup L₂ sig → Expr V₂ L₂ rs}
    (h : Wf G D e₁ (.group b₂ k₂)) :
    ∃ (b₁ : Tup L₁ sig → Blocks V₁ L₁ rs sig) (k₁ : Tup L₁ sig → Expr V₁ L₁ rs),
      e₁ = .group b₁ k₁ ∧
      (∀ Js₁ Js₂, WfB G (Tup.zip Js₁ Js₂ ++ D) (b₁ Js₁) (b₂ Js₂)) ∧
      (∀ Js₁ Js₂, Wf G (Tup.zip Js₁ Js₂ ++ D) (k₁ Js₁) (k₂ Js₂)) := by
  cases h with
  | group hb hk => exact ⟨_, _, rfl, hb, hk⟩

end

end LeanQbe.T
