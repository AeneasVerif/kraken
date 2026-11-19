module

public import LeanQbe.T.Peel
public import LeanQbe.T.WPLemmas
public import LeanQbe.T.WfLemmas

/-!
# Correctness of Bounded 1-Iteration Loop Peeling (`O-M2`)

Style-A PHOAS soundness and relational well-formedness for `LeanQbe.T.Peel`:

* `Peel.peelMetrics_eq`: `Wf`-related expressions yield identical `peelMetrics` (when label
  constructors agree), ensuring `canPeel` agrees across any two instantiations.
* `peel_wf`: relational `Wf` preservation via `Wf.induct`.
* `Peel.wp_right_mono`: label-monotonicity across two `Wf`-related right-hand instantiations
  sharing a left-hand `Expr`, avoiding extra `Wf.trans` machinery.
* `peel_wp`: source `wp` implies peeled `wp` via `Wf.induct` and direct `wp` group unrolling
  (without pulling `Logic/Rules`).
* `Func.peel_wf`, `Func.peel_spec`, `Fn.peel_wf`, `Fn.peel_spec`: closed-function specifications.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

namespace Peel

/-! ## Operand flattening and context transport helpers -/

theorem flattenArg_val {G : Ctx (Arg Val) Val} (hG : ∀ p ∈ G, p.2.1.val = p.2.2)
    {t : Ty} {a₁ : Arg (Arg Val) t} {a₂ : Arg Val t} (ha : ArgRel G t a₁ a₂) :
    (flattenArg a₁).val = a₂.val := by
  cases ha with
  | var hm => exact hG _ hm
  | imm _ => rfl

theorem flattenArgs_vals {G : Ctx (Arg Val) Val} (hG : ∀ p ∈ G, p.2.1.val = p.2.2)
    {ts : List Ty} {as₁ : Tup (Arg (Arg Val)) ts} {as₂ : Tup (Arg Val) ts}
    (h : TRel (ArgRel G) as₁ as₂) : vals (flattenArgs as₁) = vals as₂ :=
  TRel.tupMapArg_vals (fun _ => flattenArg) (fun ha => flattenArg_val hG ha) h

theorem toArgTup_zip_val :
    {ts : List Ty} → (xs : Tup Val ts) → ∀ p ∈ Tup.zip (toArgTup xs) xs, p.2.1.val = p.2.2
  | [], (), _, hp => nomatch hp
  | _ :: _, (_, xs), _, hp => by
    cases hp with
    | head => rfl
    | tail _ hp => exact toArgTup_zip_val xs _ hp

theorem ctx_zip_vals :
    {ts : List Ty} → (args : Tup (Arg Val) ts) → ∀ p ∈ Tup.zip args (vals args), p.2.1.val = p.2.2
  | [], (), _, hp => nomatch hp
  | _ :: _, (_, args), _, hp => by
    cases hp with
    | head => rfl
    | tail _ hp => exact ctx_zip_vals args _ hp

theorem ctx_val_append {H G : Ctx (Arg Val) Val}
    (hH : ∀ p ∈ H, p.2.1.val = p.2.2) (hG : ∀ p ∈ G, p.2.1.val = p.2.2) :
    ∀ p ∈ H ++ G, p.2.1.val = p.2.2 := by
  intro p hp
  rcases List.mem_append.1 hp with hp | hp
  · exact hH p hp
  · exact hG p hp

theorem ctx_val_cons_var {G : Ctx (Arg Val) Val} (hG : ∀ p ∈ G, p.2.1.val = p.2.2)
    {t : Ty} (v : Val t) : ∀ p ∈ (⟨t, .var v, v⟩ :: G), p.2.1.val = p.2.2 := by
  intro p hp
  cases hp with
  | head => rfl
  | tail _ hp => exact hG p hp

theorem argRel_flattenArg {V₁ V₂ : Ty → Type}
    {G_body : Ctx (Arg V₁) (Arg V₂)} {G : Ctx V₁ V₂}
    (hG : ∀ p ∈ G_body, ArgRel G p.1 p.2.1 p.2.2)
    {t : Ty} {a₁ : Arg (Arg V₁) t} {a₂ : Arg (Arg V₂) t} :
    ArgRel G_body t a₁ a₂ → ArgRel G t (flattenArg a₁) (flattenArg a₂)
  | .var hm => hG _ hm
  | .imm c => .imm c

theorem trel_flattenArgs {V₁ V₂ : Ty → Type}
    {G_body : Ctx (Arg V₁) (Arg V₂)} {G : Ctx V₁ V₂}
    (hG : ∀ p ∈ G_body, ArgRel G p.1 p.2.1 p.2.2)
    {ts : List Ty} {as₁ : Tup (Arg (Arg V₁)) ts} {as₂ : Tup (Arg (Arg V₂)) ts} :
    TRel (ArgRel G_body) as₁ as₂ →
    TRel (ArgRel G) (flattenArgs as₁) (flattenArgs as₂) :=
  TRel.tupMapArg_rel (fun _ => flattenArg) (fun _ => flattenArg)
    (fun ha => argRel_flattenArg hG ha)

theorem opRel_flattenOp {V₁ V₂ : Ty → Type}
    {G_body : Ctx (Arg V₁) (Arg V₂)} {G : Ctx V₁ V₂}
    (hG : ∀ p ∈ G_body, ArgRel G p.1 p.2.1 p.2.2)
    {rs : List Ty} {op₁ : Op (Arg V₁) rs} {op₂ : Op (Arg V₂) rs} :
    OpRel G_body op₁ op₂ → OpRel G (flattenOp op₁) (flattenOp op₂)
  | .mk code hargs => .mk code (trel_flattenArgs hG hargs)

theorem mem_zip_toArgTup {V₁ V₂ : Ty → Type} :
    {ts : List Ty} → (xs₁ : Tup V₁ ts) → (xs₂ : Tup V₂ ts) →
    ∀ p ∈ Tup.zip (toArgTup xs₁) (toArgTup xs₂), ArgRel (Tup.zip xs₁ xs₂) p.1 p.2.1 p.2.2
  | [], (), (), _, hp => nomatch hp
  | _ :: _, (_, _), (_, _), _, hp => by
    cases hp with
    | head => exact .var List.mem_cons_self
    | tail _ hp =>
      exact (mem_zip_toArgTup _ _ _ hp).weaken (fun _ hq => List.mem_cons_of_mem _ hq)

theorem ctx_argRel_append {V₁ V₂ : Ty → Type}
    {H : Ctx (Arg V₁) (Arg V₂)} {G_body : Ctx (Arg V₁) (Arg V₂)}
    {G₁ G₂ : Ctx V₁ V₂}
    (hH : ∀ p ∈ H, ArgRel G₁ p.1 p.2.1 p.2.2)
    (hG : ∀ p ∈ G_body, ArgRel G₂ p.1 p.2.1 p.2.2) :
    ∀ p ∈ H ++ G_body, ArgRel (G₁ ++ G₂) p.1 p.2.1 p.2.2 := by
  intro p hp
  rcases List.mem_append.1 hp with hp | hp
  · exact (hH p hp).weaken (fun _ hq => List.mem_append_left _ hq)
  · exact (hG p hp).weaken (fun _ hq => List.mem_append_right _ hq)

theorem ctx_argRel_append_same {V₁ V₂ : Ty → Type}
    {H G_body : Ctx (Arg V₁) (Arg V₂)} {G' : Ctx V₁ V₂}
    (hH : ∀ p ∈ H, ArgRel G' p.1 p.2.1 p.2.2)
    (hG : ∀ p ∈ G_body, ArgRel G' p.1 p.2.1 p.2.2) :
    ∀ p ∈ H ++ G_body, ArgRel G' p.1 p.2.1 p.2.2 := by
  intro p hp
  rcases List.mem_append.1 hp with hp | hp
  · exact hH p hp
  · exact hG p hp

theorem ctx_argRel_cons_var {V₁ V₂ : Ty → Type}
    {G_body : Ctx (Arg V₁) (Arg V₂)} {G : Ctx V₁ V₂}
    (hG : ∀ p ∈ G_body, ArgRel G p.1 p.2.1 p.2.2)
    {t : Ty} (v₁ : V₁ t) (v₂ : V₂ t) :
    ∀ p ∈ (⟨t, .var v₁, .var v₂⟩ :: G_body),
      ArgRel (⟨t, v₁, v₂⟩ :: G) p.1 p.2.1 p.2.2 := by
  intro p hp
  cases hp with
  | head => exact .var List.mem_cons_self
  | tail _ hp => exact (hG p hp).weaken (fun _ hq => List.mem_cons_of_mem _ hq)

theorem mem_zip_argRel {V₁ V₂ : Ty → Type} {G : Ctx V₁ V₂} :
    {ts : List Ty} → {as₁ : Tup (Arg V₁) ts} → {as₂ : Tup (Arg V₂) ts} →
    TRel (ArgRel G) as₁ as₂ → ∀ p ∈ Tup.zip as₁ as₂, ArgRel G p.1 p.2.1 p.2.2
  | [], (), (), .nil, _, hp => nomatch hp
  | _ :: _, (_, _), (_, _), .cons h hs, _, hp => by
    cases hp with
    | head => exact h
    | tail _ hp => exact mem_zip_argRel hs _ hp

/-! ## Block-access and `peelAux` reduction helpers -/

@[simp] theorem peelBAux_get (budget depth : Nat) {V : Ty → Type} {L : List Ty → Type}
    {rs : List Ty} :
    {sig : List (List Ty)} → {bs : Blocks (Arg V) (PeelL V L rs) rs sig} →
    {ts : List Ty} → (i : Member ts sig) → (xs : Tup V ts) →
    (peelBAux budget depth bs).get i xs = peelAux budget depth (bs.get i (toArgTup xs))
  | _, .cons _ _, _, .here, _ => rfl
  | _, .cons _ _, _, .there i, xs => peelBAux_get budget depth i xs

theorem peelArgBAux_fst {budget depth : Nat} {V : Ty → Type} {L : List Ty → Type}
    {rs ts : List Ty} (bs : Blocks (Arg V) (PeelL V L rs) rs [ts]) (args : Tup (Arg V) ts) :
    (peelArgBAux budget depth bs).1 args = peelAux budget depth (bs.get .here args) := by
  cases bs with | cons b bs => cases bs; rfl

theorem loopBlockMetrics_eq {V : Ty → Type} {L : List Ty → Type} {rs ts : List Ty}
    (bs : Blocks (Arg V) (PeelL V L rs) rs [ts]) :
    loopBlockMetrics bs = peelMetrics 0 1 (bs.get .here (immDefaults V ts)) := by
  cases bs with | cons b _ => rfl

/-! ## Metrics equivalence under `Wf` -/

/-- Label-constructor compatibility relation for `peelMetrics_eq`. -/
def PeelLabelMatch {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty} :
    (ts : List Ty) → PeelL V₁ L₁ rs ts → PeelL V₂ L₂ rs ts → Prop
  | _, .outer _, .outer _ => True
  | _, .subst _ _, .subst _ _ => True
  | _, .probe id₁, .probe id₂ => id₁ = id₂
  | _, _, _ => False

theorem mem_zip_probeTup_match {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty} :
    (sig : List (List Ty)) → (n : Nat) →
    ∀ p ∈ Tup.zip (probeTup (V := V₁) (L := L₁) (rs := rs) sig n)
                  (probeTup (V := V₂) (L := L₂) (rs := rs) sig n),
      PeelLabelMatch p.1 p.2.1 p.2.2
  | [], _, _, hp => nomatch hp
  | _ :: sig, n, _, hp => by
    cases hp with
    | head => exact rfl
    | tail _ hp => exact mem_zip_probeTup_match sig (n + 1) _ hp

private theorem peelMetricsB_eq_of_get {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    (targetId nextId : Nat) :
    {sig : List (List Ty)} →
    {bs₁ : Blocks (Arg V₁) (PeelL V₁ L₁ rs) rs sig} →
    {bs₂ : Blocks (Arg V₂) (PeelL V₂ L₂ rs) rs sig} →
    (∀ {ts} (i : Member ts sig),
      peelMetrics targetId nextId (bs₁.get i (immDefaults V₁ ts)) =
      peelMetrics targetId nextId (bs₂.get i (immDefaults V₂ ts))) →
    peelMetricsB targetId nextId bs₁ = peelMetricsB targetId nextId bs₂
  | _, .nil, .nil, _ => rfl
  | _, .cons b₁ _, .cons b₂ _, h => by
    have h0 : peelMetrics targetId nextId (b₁ (immDefaults V₁ _)) =
        peelMetrics targetId nextId (b₂ (immDefaults V₂ _)) := h .here
    simp only [peelMetricsB, h0, peelMetricsB_eq_of_get targetId nextId fun i => h (.there i)]

theorem peelMetrics_eq {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G₀ : Ctx (Arg V₁) (Arg V₂)} {D₀ : Ctx (PeelL V₁ L₁ rs) (PeelL V₂ L₂ rs)}
    {e₁ : Expr (Arg V₁) (PeelL V₁ L₁ rs) rs} {e₂ : Expr (Arg V₂) (PeelL V₂ L₂ rs) rs}
    (hwf : Wf G₀ D₀ e₁ e₂) :
    (∀ p ∈ D₀, PeelLabelMatch p.1 p.2.1 p.2.2) →
    ∀ targetId nextId, peelMetrics targetId nextId e₁ = peelMetrics targetId nextId e₂ := by
  induction hwf using Wf.induct with
  | let_ _ _ ih =>
    intro hD targetId nextId
    simp only [peelMetrics]
    rw [ih (immDefaults V₁ _) (immDefaults V₂ _) hD targetId nextId]
  | load _ _ _ ih =>
    intro hD targetId nextId
    simp only [peelMetrics]
    rw [ih (.imm default) (.imm default) hD targetId nextId]
  | store _ _ _ ih =>
    intro hD targetId nextId
    simp only [peelMetrics]
    rw [ih hD targetId nextId]
  | call _ _ _ ih =>
    intro hD targetId nextId
    simp only [peelMetrics]
    rw [ih (immDefaults V₁ _) (immDefaults V₂ _) hD targetId nextId]
  | jnz _ _ _ iht ihe =>
    intro hD targetId nextId
    simp only [peelMetrics]
    rw [iht hD targetId nextId, ihe hD targetId nextId]
  | @jump _ _ _ j₁ j₂ _ _ hj _ =>
    intro hD targetId _
    have hm := hD _ hj
    cases j₁ <;> cases j₂ <;> simp_all [PeelLabelMatch, peelMetrics]
  | ret _ | exit _ _ | hlt =>
    intro _ _ _
    rfl
  | @group _ D sig b₁ b₂ _ _ _ _ ihb ihk =>
    intro hD targetId nextId
    simp only [peelMetrics]
    have hD' : ∀ p ∈ Tup.zip (probeTup (V := V₁) (L := L₁) (rs := rs) sig nextId)
          (probeTup (V := V₂) (L := L₂) (rs := rs) sig nextId) ++ D,
        PeelLabelMatch p.1 p.2.1 p.2.2 := by
      intro p hp
      rcases List.mem_append.1 hp with hp | hp
      · exact mem_zip_probeTup_match sig nextId p hp
      · exact hD p hp
    have hbm : peelMetricsB targetId (nextId + sig.length) (b₁ (probeTup sig nextId)) =
        peelMetricsB targetId (nextId + sig.length) (b₂ (probeTup sig nextId)) :=
      peelMetricsB_eq_of_get targetId (nextId + sig.length) fun i =>
        ihb (probeTup sig nextId) (probeTup sig nextId) i (immDefaults V₁ _) (immDefaults V₂ _)
          hD' targetId (nextId + sig.length)
    have hkm := ihk (probeTup sig nextId) (probeTup sig nextId) hD' targetId (nextId + sig.length)
    rw [hbm, hkm]

/-! ## Relational well-formedness invariant for `peel_wf` -/

/-- Label-context invariant for `peel_wf`: `.outer` labels are paired in `D'`, and `.subst`
continuations preserve `Wf` across any valid context extension `(G'', D'')`. -/
def PeelLabelWf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    (G' : Ctx V₁ V₂) (D' : Ctx L₁ L₂) :
    (ts : List Ty) → PeelL V₁ L₁ rs ts → PeelL V₂ L₂ rs ts → Prop
  | ts, .outer l₁, .outer l₂ => ⟨ts, l₁, l₂⟩ ∈ D'
  | ts, .subst id₁ k₁, .subst id₂ k₂ =>
    id₁ = id₂ ∧
    ∀ (G'' : Ctx V₁ V₂) (D'' : Ctx L₁ L₂),
      (∀ p ∈ G', p ∈ G'') → (∀ p ∈ D', p ∈ D'') →
      ∀ (args₁ : Tup (Arg V₁) ts) (args₂ : Tup (Arg V₂) ts),
        TRel (ArgRel G'') args₁ args₂ → Wf G'' D'' (k₁ args₁) (k₂ args₂)
  | _, _, _ => False

theorem PeelLabelWf.toMatch {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G' : Ctx V₁ V₂} {D' : Ctx L₁ L₂} {ts : List Ty}
    {j₁ : PeelL V₁ L₁ rs ts} {j₂ : PeelL V₂ L₂ rs ts}
    (h : PeelLabelWf G' D' ts j₁ j₂) : PeelLabelMatch ts j₁ j₂ := by
  cases j₁ <;> cases j₂ <;> first | exact h | exact False.elim h | trivial

theorem PeelLabelWf.weaken {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G₁ G₂ : Ctx V₁ V₂} {D₁ D₂ : Ctx L₁ L₂}
    (hG : ∀ p ∈ G₁, p ∈ G₂) (hD : ∀ p ∈ D₁, p ∈ D₂)
    {ts : List Ty} {j₁ : PeelL V₁ L₁ rs ts} {j₂ : PeelL V₂ L₂ rs ts} :
    PeelLabelWf G₁ D₁ ts j₁ j₂ → PeelLabelWf G₂ D₂ ts j₁ j₂ := by
  cases j₁ <;> cases j₂ <;> intro h
  · exact hD _ h
  · exact False.elim h
  · exact False.elim h
  · exact False.elim h
  · exact ⟨h.1, fun G₃ D₃ hG23 hD23 =>
      h.2 G₃ D₃ (fun _ hp => hG23 _ (hG _ hp)) (fun _ hp => hD23 _ (hD _ hp))⟩
  · exact False.elim h
  · exact False.elim h
  · exact False.elim h
  · exact False.elim h

theorem mem_zip_toOuterTup_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    (G' : Ctx V₁ V₂) (D' : Ctx L₁ L₂) :
    {sig : List (List Ty)} → (Js₁ : Tup L₁ sig) → (Js₂ : Tup L₂ sig) →
    ∀ p ∈ Tup.zip (toOuterTup (V := V₁) (rs := rs) Js₁)
                  (toOuterTup (V := V₂) (rs := rs) Js₂),
      PeelLabelWf G' (Tup.zip Js₁ Js₂ ++ D') p.1 p.2.1 p.2.2
  | [], (), (), _, hp => nomatch hp
  | _ :: _, (_, _), (_, _), _, hp => by
    cases hp with
    | head => exact List.mem_cons_self
    | tail _ hp =>
      exact (mem_zip_toOuterTup_wf G' D' _ _ _ hp).weaken (fun _ hq => hq)
        (fun _ hq => List.mem_cons_of_mem _ hq)

theorem PeelLabelWf.append_outer {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G' : Ctx V₁ V₂} {D' : Ctx L₁ L₂} {D : Ctx (PeelL V₁ L₁ rs) (PeelL V₂ L₂ rs)}
    (hD : ∀ p ∈ D, PeelLabelWf G' D' p.1 p.2.1 p.2.2)
    {sig : List (List Ty)} (Js₁ : Tup L₁ sig) (Js₂ : Tup L₂ sig) :
    ∀ p ∈ Tup.zip (toOuterTup (V := V₁) (rs := rs) Js₁)
                  (toOuterTup (V := V₂) (rs := rs) Js₂) ++ D,
      PeelLabelWf G' (Tup.zip Js₁ Js₂ ++ D') p.1 p.2.1 p.2.2 := by
  intro p hp
  rcases List.mem_append.1 hp with hp | hp
  · exact mem_zip_toOuterTup_wf G' D' Js₁ Js₂ p hp
  · exact (hD p hp).weaken (fun _ hq => hq) (fun _ hq => List.mem_append_right _ hq)

theorem PeelLabelWf.cons_subst {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G' : Ctx V₁ V₂} {D' : Ctx L₁ L₂} {D : Ctx (PeelL V₁ L₁ rs) (PeelL V₂ L₂ rs)}
    (hD : ∀ p ∈ D, PeelLabelWf G' D' p.1 p.2.1 p.2.2)
    {ts : List Ty} {id : Nat} {k₁ : Tup (Arg V₁) ts → Expr V₁ L₁ rs}
    {k₂ : Tup (Arg V₂) ts → Expr V₂ L₂ rs}
    (hk : PeelLabelWf G' D' ts (.subst id k₁) (.subst id k₂)) :
    ∀ p ∈ (⟨ts, .subst id k₁, .subst id k₂⟩ :: D), PeelLabelWf G' D' p.1 p.2.1 p.2.2 := by
  intro p hp
  cases hp with
  | head => exact hk
  | tail _ hp => exact hD p hp

/-! ## Right-hand `Wf` monotonicity helper for `peel_wp` -/

theorem vals_eq_of_argRel_left {G : Ctx (Arg Val) Val} (hG : ∀ p ∈ G, p.2.1.val = p.2.2)
    {ts : List Ty} {as₁ : Tup (Arg (Arg Val)) ts} {as₂ as₂' : Tup (Arg Val) ts}
    (h1 : TRel (ArgRel G) as₁ as₂) (h2 : TRel (ArgRel G) as₁ as₂') :
    vals as₂ = vals as₂' := by
  rw [← flattenArgs_vals hG h1, flattenArgs_vals hG h2]

theorem arg_val_eq_of_argRel_left {G : Ctx (Arg Val) Val} (hG : ∀ p ∈ G, p.2.1.val = p.2.2)
    {t : Ty} {a₁ : Arg (Arg Val) t} {a₂ a₂' : Arg Val t}
    (h1 : ArgRel G t a₁ a₂) (h2 : ArgRel G t a₁ a₂') :
    a₂.val = a₂'.val := by
  rw [← flattenArg_val hG h1, flattenArg_val hG h2]

/-- Label-constructor watermark: no `.probe k` with `k ≥ n` appears in `D`. -/
def NoProbeGE {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (n : Nat) (D : Ctx (PeelL V L rs) Cont) : Prop :=
  ∀ {ts : List Ty} {k : Nat} {j₂ : Cont ts}, ⟨ts, .probe k, j₂⟩ ∈ D → k < n

private theorem mem_zip_probeTup_ge {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    (sig : List (List Ty)) → (n : Nat) → (Js : Tup Cont sig) →
    ∀ {ts} {j₁ : PeelL V L rs ts} {j₂ : Cont ts},
      ⟨ts, j₁, j₂⟩ ∈ Tup.zip (probeTup (V := V) (L := L) (rs := rs) sig n) Js →
      ∃ k, j₁ = .probe k ∧ n ≤ k ∧ k < n + sig.length
  | [], _, (), _, _, _, hp => nomatch hp
  | _ :: sig, n, (_, Js), _, _, _, hp => by
    cases hp with
    | head => exact ⟨n, rfl, Nat.le_refl _, by simp⟩
    | tail _ hp =>
      obtain ⟨k, rfl, h1, h2⟩ := mem_zip_probeTup_ge sig (n + 1) Js hp
      exact ⟨k, rfl, by omega, by simp; omega⟩

private theorem mem_zip_probeTup_det {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    (sig : List (List Ty)) → (n : Nat) → (Js : Tup Cont sig) →
    ∀ {ts} {j₁ : PeelL V L rs ts} {j₂ j₂' : Cont ts},
      ⟨ts, j₁, j₂⟩ ∈ Tup.zip (probeTup (V := V) (L := L) (rs := rs) sig n) Js →
      ⟨ts, j₁, j₂'⟩ ∈ Tup.zip (probeTup (V := V) (L := L) (rs := rs) sig n) Js →
      j₂ = j₂'
  | [], _, (), _, _, _, _, h1, _ => nomatch h1
  | _ :: sig, n, (_, Js), _, _, _, _, h1, h2 => by
    cases h1 with
    | head =>
      cases h2 with
      | head => rfl
      | tail _ h2 =>
        obtain ⟨k, hk, hge, _⟩ := mem_zip_probeTup_ge sig (n + 1) Js h2
        injection hk with hk'
        cases hk'
        omega
    | tail _ h1 =>
      cases h2 with
      | head =>
        obtain ⟨k, hk, hge, _⟩ := mem_zip_probeTup_ge sig (n + 1) Js h1
        injection hk with hk'
        cases hk'
        omega
      | tail _ h2 => exact mem_zip_probeTup_det sig (n + 1) Js h1 h2

private theorem noProbeGE_append_probeTup {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    {n : Nat} {D : Ctx (PeelL V L rs) Cont} (hn : NoProbeGE n D)
    (sig : List (List Ty)) (Js : Tup Cont sig) :
    NoProbeGE (n + sig.length)
      (Tup.zip (probeTup (V := V) (L := L) (rs := rs) sig n) Js ++ D) := by
  intro ts k j₂ hmem
  rcases List.mem_append.1 hmem with h | h
  · obtain ⟨k', hk', _, hlt⟩ := mem_zip_probeTup_ge sig n Js h
    injection hk' with hk''
    cases hk''
    exact hlt
  · exact Nat.lt_of_lt_of_le (hn h) (Nat.le_add_right n sig.length)

/-- If two `Cont`-instantiated expressions `e₂`, `e₂'` are `Wf`-related to the same left-hand
witness `e₁`, and every paired label in `D₀`, `D₂` is monotone (`j₂ → j₂'`), then `wp` transfers
from `e₂` to `e₂'`. -/
theorem wp_right_mono {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {G₀ : Ctx (Arg Val) Val} {D₀ : Ctx (PeelL Val Cont rs) Cont}
    {e₁ : Expr (Arg Val) (PeelL Val Cont rs) rs} {e₂ : Expr Val Cont rs}
    (h1 : Wf G₀ D₀ e₁ e₂) :
    ∀ {D₂ : Ctx (PeelL Val Cont rs) Cont} {e₂' : Expr Val Cont rs} (n : Nat),
      (∀ p ∈ G₀, p.2.1.val = p.2.2) →
      NoProbeGE n D₀ → NoProbeGE n D₂ →
      (∀ {ts} {j₁ : PeelL Val Cont rs ts} {j₂ j₂' : Cont ts},
        ⟨ts, j₁, j₂⟩ ∈ D₀ → ⟨ts, j₁, j₂'⟩ ∈ D₂ → ∀ xs m, j₂ xs m → j₂' xs m) →
      Wf G₀ D₂ e₁ e₂' → ∀ m, wp Γ Q X e₂ m → wp Γ Q X e₂' m := by
  induction h1 using Wf.induct with
  | let_ hop₁ _ ih =>
    intro D₂ e₂' n hG hn1 hn2 hD h2 m h
    cases h2 with
    | let_ hop₂ hk₂ =>
      cases hop₁ with | mk code hargs₁ =>
      cases hop₂ with | mk _ hargs₂ =>
      simp only [wp, Op.wp] at h ⊢
      rw [← vals_eq_of_argRel_left hG hargs₁ hargs₂]
      exact OpCode.wp_mono code (vals _)
        (fun r hr => ih (toArgTup r) r n (ctx_val_append (toArgTup_zip_val r) hG) hn1 hn2 hD
          (hk₂ (toArgTup r) r) m hr) h
  | load t ha₁ _ ih =>
    intro D₂ e₂' n hG hn1 hn2 hD h2 m ⟨v, hv, h⟩
    cases h2 with
    | load _ ha₂ hk₂ =>
      simp only [wp]
      rw [← arg_val_eq_of_argRel_left hG ha₁ ha₂]
      exact ⟨v, hv, ih (.var v) v n (ctx_val_cons_var hG v) hn1 hn2 hD (hk₂ (.var v) v) m h⟩
  | store hv₁ ha₁ _ ih =>
    intro D₂ e₂' n hG hn1 hn2 hD h2 m ⟨hok, h⟩
    cases h2 with
    | store hv₂ ha₂ hk₂ =>
      simp only [wp]
      rw [← arg_val_eq_of_argRel_left hG hv₁ hv₂, ← arg_val_eq_of_argRel_left hG ha₁ ha₂]
      exact ⟨hok, ih n hG hn1 hn2 hD hk₂ _ h⟩
  | call f hargs₁ _ ih =>
    intro D₂ e₂' n hG hn1 hn2 hD h2 m ⟨P, E, hΓ, hP, hE⟩
    cases h2 with
    | call _ hargs₂ hk₂ =>
      simp only [wp]
      rw [← vals_eq_of_argRel_left hG hargs₁ hargs₂]
      exact ⟨P, E, hΓ, fun r m' hr =>
        ih (toArgTup r) r n (ctx_val_append (toArgTup_zip_val r) hG) hn1 hn2 hD
          (hk₂ (toArgTup r) r) m' (hP r m' hr), hE⟩
  | jnz hc₁ _ _ iht ihe =>
    intro D₂ e₂' n hG hn1 hn2 hD h2 m ⟨ht, he⟩
    cases h2 with
    | jnz hc₂ ht₂ he₂ =>
      simp only [wp]
      rw [← arg_val_eq_of_argRel_left hG hc₁ hc₂]
      exact ⟨fun h => iht n hG hn1 hn2 hD ht₂ m (ht h),
             fun h => ihe n hG hn1 hn2 hD he₂ m (he h)⟩
  | jump hj₁ hargs₁ =>
    intro D₂ e₂' _ hG _ _ hD h2 m h
    cases h2 with
    | jump hj₂ hargs₂ =>
      simp only [wp] at h ⊢
      rw [← vals_eq_of_argRel_left hG hargs₁ hargs₂]
      exact hD hj₁ hj₂ _ m h
  | ret hvs₁ =>
    intro D₂ e₂' _ hG _ _ _ h2 m h
    cases h2 with
    | ret hvs₂ =>
      simp only [wp] at h ⊢
      rw [← vals_eq_of_argRel_left hG hvs₁ hvs₂]
      exact h
  | exit f hargs₁ =>
    intro D₂ e₂' _ hG _ _ _ h2 m h
    cases h2 with
    | exit _ hargs₂ =>
      simp only [wp] at h ⊢
      rw [← vals_eq_of_argRel_left hG hargs₁ hargs₂]
      exact h
  | hlt =>
    intro _ e₂' _ _ _ _ _ h2 m h
    cases h2
    exact h
  | @group _ D sig _ b₂ _ k₂ _ _ ihb ihk =>
    intro D₂ e₂' n hG hn1 hn2 hD h2 m h
    cases h2 with
    | group hb₂ hk₂ =>
      intro Js' hc'
      simp only [wp] at h
      have hD' : ∀ {ts} {j₁ : PeelL Val Cont rs ts} {j₂ j₂' : Cont ts},
          ⟨ts, j₁, j₂⟩ ∈ Tup.zip (probeTup sig n) Js' ++ D →
          ⟨ts, j₁, j₂'⟩ ∈ Tup.zip (probeTup sig n) Js' ++ D₂ →
          ∀ xs m, j₂ xs m → j₂' xs m := by
        intro ts j₁ j₂ j₂' hm1 hm2 xs m' hj
        rcases List.mem_append.1 hm1 with hm1 | hm1 <;>
          rcases List.mem_append.1 hm2 with hm2 | hm2
        · rw [← mem_zip_probeTup_det sig n Js' hm1 hm2]; exact hj
        · obtain ⟨k, hk, hge, _⟩ := mem_zip_probeTup_ge sig n Js' hm1
          subst hk
          exact absurd (hn2 hm2) (Nat.not_lt.2 hge)
        · obtain ⟨k, hk, hge, _⟩ := mem_zip_probeTup_ge sig n Js' hm2
          subst hk
          exact absurd (hn1 hm1) (Nat.not_lt.2 hge)
        · exact hD hm1 hm2 xs m' hj
      have hn1' : NoProbeGE (n + sig.length)
          (Tup.zip (probeTup (V := Val) (L := Cont) (rs := rs) sig n) Js' ++ D) :=
        noProbeGE_append_probeTup hn1 sig Js'
      have hn2' : NoProbeGE (n + sig.length)
          (Tup.zip (probeTup (V := Val) (L := Cont) (rs := rs) sig n) Js' ++ D₂) :=
        noProbeGE_append_probeTup hn2 sig Js'
      refine ihk (probeTup sig n) Js' (n + sig.length) hG hn1' hn2' hD'
        (hk₂ (probeTup sig n) Js') m (h Js' ?_)
      rw [closed_iff] at hc' ⊢
      intro _ i xs m' hb
      exact hc' i xs m' (ihb (probeTup sig n) Js' i (toArgTup xs) xs (n + sig.length)
        (ctx_val_append (toArgTup_zip_val xs) hG) hn1' hn2' hD'
        ((hb₂ (probeTup sig n) Js').get i (toArgTup xs) xs) m' hb)

/-! ## Label-context invariant for `peel_wp` -/

/-- Semantic label-context invariant for `peel_wp`, tracking `.outer` equality, `.subst`
soundness, and unique `.subst` identifiers `< bound`. -/
def PeelLabelWp (Γ : Env) {rs : List Ty} (Q : Post rs) (X : XPost) (bound : Nat) :
    (ts : List Ty) → PeelL Val Cont rs ts → Cont ts → Prop
  | _, .outer l, j₂ => l = j₂
  | ts, .subst id k, j₂ =>
    id < bound ∧
    ∀ (args : Tup (Arg Val) ts) (m : Mem 64), j₂ (vals args) m → wp Γ Q X (k args) m
  | _, .probe _, _ => False

theorem PeelLabelWp.weakenBound {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {b₁ b₂ : Nat} (hb : b₁ ≤ b₂) {ts : List Ty} {j₁ : PeelL Val Cont rs ts} {j₂ : Cont ts} :
    PeelLabelWp Γ Q X b₁ ts j₁ j₂ → PeelLabelWp Γ Q X b₂ ts j₁ j₂ := by
  cases j₁ with
  | outer _ => exact id
  | subst _ _ => exact fun ⟨hlt, hk⟩ => ⟨Nat.lt_of_lt_of_le hlt hb, hk⟩
  | probe _ => exact False.elim

theorem PeelLabelWp.noProbeGE {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {bound : Nat}
    {D : Ctx (PeelL Val Cont rs) Cont}
    (hD : ∀ p ∈ D, PeelLabelWp Γ Q X bound p.1 p.2.1 p.2.2) : NoProbeGE 0 D := by
  intro ts k j₂ hm
  exact False.elim (hD _ hm)

theorem mem_zip_toOuterTup_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} (bound : Nat) :
    {sig : List (List Ty)} → (Js : Tup Cont sig) →
    ∀ p ∈ Tup.zip (toOuterTup (V := Val) (rs := rs) Js) Js,
      PeelLabelWp Γ Q X bound p.1 p.2.1 p.2.2
  | [], (), _, hp => nomatch hp
  | _ :: _, (_, _), _, hp => by
    cases hp with
    | head => exact rfl
    | tail _ hp => exact mem_zip_toOuterTup_wp bound _ _ hp

theorem PeelLabelWp.append_outer {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {bound : Nat} {D : Ctx (PeelL Val Cont rs) Cont}
    (hD : ∀ p ∈ D, PeelLabelWp Γ Q X bound p.1 p.2.1 p.2.2)
    {sig : List (List Ty)} (Js : Tup Cont sig) :
    ∀ p ∈ Tup.zip (toOuterTup (V := Val) (rs := rs) Js) Js ++ D,
      PeelLabelWp Γ Q X bound p.1 p.2.1 p.2.2 := by
  intro p hp
  rcases List.mem_append.1 hp with hp | hp
  · exact mem_zip_toOuterTup_wp bound Js p hp
  · exact hD p hp

theorem PeelLabelWp.cons_subst {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {b₁ b₂ : Nat} (hb : b₁ ≤ b₂) {D : Ctx (PeelL Val Cont rs) Cont}
    (hD : ∀ p ∈ D, PeelLabelWp Γ Q X b₁ p.1 p.2.1 p.2.2)
    {ts : List Ty} {id : Nat} {k : Tup (Arg Val) ts → Expr Val Cont rs} {j₂ : Cont ts}
    (hk : PeelLabelWp Γ Q X b₂ ts (.subst id k) j₂) :
    ∀ p ∈ (⟨ts, .subst id k, j₂⟩ :: D), PeelLabelWp Γ Q X b₂ p.1 p.2.1 p.2.2 := by
  intro p hp
  cases hp with
  | head => exact hk
  | tail _ hp => exact (hD p hp).weakenBound hb

/-- Label-uniqueness invariant on `D`: distinct entries with the same `j₁` agree on `j₂`. -/
def PeelDFun {rs : List Ty} (D : Ctx (PeelL Val Cont rs) Cont) : Prop :=
  ∀ {ts} {j₁ : PeelL Val Cont rs ts} {j₂ j₂' : Cont ts},
    ⟨ts, j₁, j₂⟩ ∈ D → ⟨ts, j₁, j₂'⟩ ∈ D → j₂ = j₂'

private theorem mem_zip_toOuterTup_eq {rs : List Ty} :
    {sig : List (List Ty)} → (Js : Tup Cont sig) →
    ∀ {ts} {j₁ : PeelL Val Cont rs ts} {j₂ : Cont ts},
      ⟨ts, j₁, j₂⟩ ∈ Tup.zip (toOuterTup (V := Val) (rs := rs) Js) Js →
      ∃ l : Cont ts, j₁ = .outer l ∧ l = j₂
  | [], (), _, _, _, hm => nomatch hm
  | _ :: _, (_, Js), _, _, _, hm => by
    cases hm with
    | head => exact ⟨_, rfl, rfl⟩
    | tail _ hm => exact mem_zip_toOuterTup_eq Js hm

theorem peelDFun_append_outer {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {bound : Nat}
    {D : Ctx (PeelL Val Cont rs) Cont}
    (hD : ∀ p ∈ D, PeelLabelWp Γ Q X bound p.1 p.2.1 p.2.2) (hfun : PeelDFun D)
    {sig : List (List Ty)} (Js : Tup Cont sig) :
    PeelDFun (Tup.zip (toOuterTup (V := Val) (rs := rs) Js) Js ++ D) := by
  intro ts j₁ j₂ j₂' hm1 hm2
  rcases List.mem_append.1 hm1 with hm1 | hm1 <;> rcases List.mem_append.1 hm2 with hm2 | hm2
  · obtain ⟨l₁, rfl, rfl⟩ := mem_zip_toOuterTup_eq Js hm1
    obtain ⟨l₂, h, rfl⟩ := mem_zip_toOuterTup_eq Js hm2
    cases h; rfl
  · obtain ⟨l₁, rfl, rfl⟩ := mem_zip_toOuterTup_eq Js hm1
    exact hD _ hm2
  · obtain ⟨l₂, rfl, rfl⟩ := mem_zip_toOuterTup_eq Js hm2
    exact (hD _ hm1).symm
  · exact hfun hm1 hm2

theorem peelDFun_cons_subst {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {bound : Nat}
    {D : Ctx (PeelL Val Cont rs) Cont}
    (hD : ∀ p ∈ D, PeelLabelWp Γ Q X bound p.1 p.2.1 p.2.2) (hfun : PeelDFun D)
    {ts : List Ty} {id : Nat} (hid : bound ≤ id)
    (k : Tup (Arg Val) ts → Expr Val Cont rs) (j₂ : Cont ts) :
    PeelDFun (⟨ts, .subst id k, j₂⟩ :: D) := by
  intro ts' j₁ ja jb h1 h2
  cases h1 with
  | head =>
    cases h2 with
    | head => rfl
    | tail _ h2 =>
      have ⟨hlt, _⟩ := hD _ h2
      omega
  | tail _ h1 =>
    cases h2 with
    | head =>
      have ⟨hlt, _⟩ := hD _ h1
      omega
    | tail _ h2 => exact hfun h1 h2

/-! ## Depth-indexed helper proofs for `peel_wf` and `peel_wp` -/

theorem peelAux_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G₀ : Ctx (Arg V₁) (Arg V₂)} {D₀ : Ctx (PeelL V₁ L₁ rs) (PeelL V₂ L₂ rs)}
    {e₁ : Expr (Arg V₁) (PeelL V₁ L₁ rs) rs}
    {e₂ : Expr (Arg V₂) (PeelL V₂ L₂ rs) rs}
    (hwf : Wf G₀ D₀ e₁ e₂) :
    ∀ {G' : Ctx V₁ V₂} {D' : Ctx L₁ L₂},
      (∀ p ∈ G₀, ArgRel G' p.1 p.2.1 p.2.2) →
      (∀ p ∈ D₀, PeelLabelWf G' D' p.1 p.2.1 p.2.2) →
      ∀ budget depth, Wf G' D' (peelAux budget depth e₁) (peelAux budget depth e₂) := by
  induction hwf using Wf.induct with
  | let_ hop _ ih =>
    intro G' D' hG hD budget depth
    exact .let_ (opRel_flattenOp hG hop) fun xs₁ xs₂ =>
      ih (toArgTup xs₁) (toArgTup xs₂)
        (ctx_argRel_append (mem_zip_toArgTup xs₁ xs₂) hG)
        (fun p hp => (hD p hp).weaken
          (fun _ hq => List.mem_append_right _ hq) (fun _ hq => hq))
        budget depth
  | load t ha _ ih =>
    intro G' D' hG hD budget depth
    exact .load t (argRel_flattenArg hG ha) fun v₁ v₂ =>
      ih (.var v₁) (.var v₂) (ctx_argRel_cons_var hG v₁ v₂)
        (fun p hp => (hD p hp).weaken
          (fun _ hq => List.mem_cons_of_mem _ hq) (fun _ hq => hq))
        budget depth
  | store hv ha _ ih =>
    intro G' D' hG hD budget depth
    exact .store (argRel_flattenArg hG hv) (argRel_flattenArg hG ha)
      (ih hG hD budget depth)
  | call f hargs _ ih =>
    intro G' D' hG hD budget depth
    exact .call f (trel_flattenArgs hG hargs) fun xs₁ xs₂ =>
      ih (toArgTup xs₁) (toArgTup xs₂)
        (ctx_argRel_append (mem_zip_toArgTup xs₁ xs₂) hG)
        (fun p hp => (hD p hp).weaken
          (fun _ hq => List.mem_append_right _ hq) (fun _ hq => hq))
        budget depth
  | jnz hc _ _ iht ihe =>
    intro G' D' hG hD budget depth
    exact .jnz (argRel_flattenArg hG hc) (iht hG hD budget depth) (ihe hG hD budget depth)
  | @jump _ _ ts j₁ j₂ _ _ hj hargs =>
    intro G' D' hG hD _ _
    have hlbl := hD _ hj
    have hargs' := trel_flattenArgs hG hargs
    cases j₁ <;> cases j₂
    · exact .jump hlbl hargs'
    · exact False.elim hlbl
    · exact False.elim hlbl
    · exact False.elim hlbl
    · exact hlbl.2 G' D' (fun _ hq => hq) (fun _ hq => hq) _ _ hargs'
    · exact False.elim hlbl
    · exact False.elim hlbl
    · exact False.elim hlbl
    · exact False.elim hlbl
  | ret hvs =>
    intro G' _ hG _ _ _
    exact .ret (trel_flattenArgs hG hvs)
  | exit f hargs =>
    intro G' _ hG _ _ _
    exact .exit f (trel_flattenArgs hG hargs)
  | hlt =>
    intro _ _ _ _ _ _
    exact .hlt
  | @group _ D sig b₁ b₂ k₁ k₂ hb hk ihb ihk =>
    intro G' D' hG hD budget depth
    have hkeep :
        Wf G' D'
          (.group (fun Js => peelBAux budget depth (b₁ (toOuterTup Js)))
                  (fun Js => peelAux budget depth (k₁ (toOuterTup Js))))
          (.group (fun Js => peelBAux budget depth (b₂ (toOuterTup Js)))
                  (fun Js => peelAux budget depth (k₂ (toOuterTup Js)))) :=
      .group
        (fun Js₁ Js₂ => WfB.of_get fun i xs₁ xs₂ => by
          rw [peelBAux_get, peelBAux_get]
          exact ihb (toOuterTup Js₁) (toOuterTup Js₂) i
            (toArgTup xs₁) (toArgTup xs₂)
            (ctx_argRel_append (mem_zip_toArgTup xs₁ xs₂) hG)
            (PeelLabelWf.append_outer (fun p hp =>
              (hD p hp).weaken (fun _ hq => List.mem_append_right _ hq) (fun _ hq => hq))
              Js₁ Js₂)
            budget depth)
        (fun Js₁ Js₂ => ihk (toOuterTup Js₁) (toOuterTup Js₂) hG
          (PeelLabelWf.append_outer hD Js₁ Js₂) budget depth)
    rcases sig with _ | ⟨ts, sig⟩
    · simp only [peelAux]
      exact hkeep
    · rcases sig with _ | ⟨ts', sig'⟩
      · have hMatchD : ∀ p ∈ D, PeelLabelMatch p.1 p.2.1 p.2.2 :=
          fun p hp => (hD p hp).toMatch
        have hMatchD' :
            ∀ p ∈ Tup.zip (probeTup (V := V₁) (L := L₁) (rs := rs) [ts] 0)
                          (probeTup (V := V₂) (L := L₂) (rs := rs) [ts] 0) ++ D,
              PeelLabelMatch p.1 p.2.1 p.2.2 := by
          intro p hp
          rcases List.mem_append.1 hp with hp | hp
          · exact mem_zip_probeTup_match [ts] 0 p hp
          · exact hMatchD p hp
        have hmb_eq :
            peelMetrics 0 1 ((b₁ (.probe 0, ())).get .here (immDefaults V₁ ts)) =
            peelMetrics 0 1 ((b₂ (.probe 0, ())).get .here (immDefaults V₂ ts)) :=
          peelMetrics_eq
            ((hb (.probe 0, ()) (.probe 0, ())).get .here
              (immDefaults V₁ ts) (immDefaults V₂ ts))
            hMatchD' 0 1
        have hme_eq :
            peelMetrics 0 1 (k₁ (.probe 0, ())) =
            peelMetrics 0 1 (k₂ (.probe 0, ())) :=
          peelMetrics_eq (hk (.probe 0, ()) (.probe 0, ())) hMatchD' 0 1
        simp only [peelAux]
        rw [loopBlockMetrics_eq (b₁ (.probe 0, ())),
            loopBlockMetrics_eq (b₂ (.probe 0, ())), hmb_eq, hme_eq]
        cases hcan : canPeel budget
            (peelMetrics 0 1 ((b₂ (.probe 0, ())).get .here (immDefaults V₂ ts)))
            (peelMetrics 0 1 (k₂ (.probe 0, ())))
        · simp only [Bool.false_eq_true, ↓reduceIte]
          exact hkeep
        · simp only [↓reduceIte]
          let remBudget :=
            (budget - (peelMetrics 0 1
              ((b₂ (.probe 0, ())).get .here (immDefaults V₂ ts))).size) / 2
          let remIter2₁ : Tup (Arg V₁) ts → Expr V₁ L₁ rs := fun backArgs =>
            .group (sig := [ts])
              (fun Js => peelBAux remBudget (depth + 1) (b₁ (toOuterTup Js)))
              (fun Js => .jump Js.1 backArgs)
          let remIter2₂ : Tup (Arg V₂) ts → Expr V₂ L₂ rs := fun backArgs =>
            .group (sig := [ts])
              (fun Js => peelBAux remBudget (depth + 1) (b₂ (toOuterTup Js)))
              (fun Js => .jump Js.1 backArgs)
          have hRem : PeelLabelWf G' D' ts
              (.subst (2 * depth) remIter2₁) (.subst (2 * depth) remIter2₂) := by
            refine ⟨rfl, fun G'' D'' hGsub hDsub backArgs₁ backArgs₂ hback => ?_⟩
            refine .group (fun Js₁ Js₂ => WfB.of_get fun i xs₁ xs₂ => ?_) (fun Js₁ Js₂ => ?_)
            · rw [peelBAux_get, peelBAux_get]
              exact ihb (toOuterTup Js₁) (toOuterTup Js₂) i
                (toArgTup xs₁) (toArgTup xs₂)
                (ctx_argRel_append (mem_zip_toArgTup xs₁ xs₂)
                  (fun p hp => (hG p hp).weaken hGsub))
                (PeelLabelWf.append_outer (fun p hp =>
                  (hD p hp).weaken (fun _ hq => List.mem_append_right _ (hGsub _ hq)) hDsub)
                  Js₁ Js₂)
                remBudget (depth + 1)
            · exact .jump List.mem_cons_self hback
          let iter1₁ : Tup (Arg V₁) ts → Expr V₁ L₁ rs :=
            (peelArgBAux remBudget (depth + 1) (b₁ (.subst (2 * depth) remIter2₁, ()))).1
          let iter1₂ : Tup (Arg V₂) ts → Expr V₂ L₂ rs :=
            (peelArgBAux remBudget (depth + 1) (b₂ (.subst (2 * depth) remIter2₂, ()))).1
          have hIter1 : PeelLabelWf G' D' ts
              (.subst (2 * depth + 1) iter1₁) (.subst (2 * depth + 1) iter1₂) := by
            refine ⟨rfl, fun G'' D'' hGsub hDsub initArgs₁ initArgs₂ hinit => ?_⟩
            dsimp only [iter1₁, iter1₂]
            rw [peelArgBAux_fst, peelArgBAux_fst]
            exact ihb (.subst (2 * depth) remIter2₁, ()) (.subst (2 * depth) remIter2₂, ()) .here
              initArgs₁ initArgs₂
              (ctx_argRel_append_same (mem_zip_argRel hinit) (fun p hp => (hG p hp).weaken hGsub))
              (PeelLabelWf.cons_subst (fun p hp => (hD p hp).weaken hGsub hDsub)
                (hRem.weaken hGsub hDsub))
              remBudget (depth + 1)
          exact ihk (.subst (2 * depth + 1) iter1₁, ()) (.subst (2 * depth + 1) iter1₂, ()) hG
            (PeelLabelWf.cons_subst hD hIter1) budget (depth + 1)
      · simp only [peelAux]
        exact hkeep

theorem peelAux_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {G₀ : Ctx (Arg Val) Val} {D₀ : Ctx (PeelL Val Cont rs) Cont}
    {e₁ : Expr (Arg Val) (PeelL Val Cont rs) rs} {e₂ : Expr Val Cont rs}
    (hwf : Wf G₀ D₀ e₁ e₂) :
    ∀ m budget depth, (∀ p ∈ G₀, p.2.1.val = p.2.2) →
      (∀ p ∈ D₀, PeelLabelWp Γ Q X (2 * depth) p.1 p.2.1 p.2.2) →
      PeelDFun D₀ →
      wp Γ Q X e₂ m → wp Γ Q X (peelAux budget depth e₁) m := by
  induction hwf using Wf.induct with
  | let_ hop _ ih =>
    intro m budget depth hG hD hfun h
    cases hop with
    | mk code hargs =>
      simp only [peelAux, wp, flattenOp, Op.wp] at h ⊢
      rw [flattenArgs_vals hG hargs]
      exact OpCode.wp_mono code (vals _)
        (fun r hr => ih (toArgTup r) r m budget depth
          (ctx_val_append (toArgTup_zip_val r) hG) hD hfun hr) h
  | load t ha _ ih =>
    intro m budget depth hG hD hfun ⟨v, hv, hk⟩
    simp only [peelAux, wp]
    rw [flattenArg_val hG ha]
    exact ⟨v, hv, ih (.var v) v m budget depth (ctx_val_cons_var hG v) hD hfun hk⟩
  | store hv ha _ ih =>
    intro m budget depth hG hD hfun ⟨hok, hk⟩
    simp only [peelAux, wp]
    rw [flattenArg_val hG hv, flattenArg_val hG ha]
    exact ⟨hok, ih _ budget depth hG hD hfun hk⟩
  | call f hargs _ ih =>
    intro m budget depth hG hD hfun ⟨P, E, hΓ, hP, hE⟩
    simp only [peelAux, wp]
    rw [flattenArgs_vals hG hargs]
    exact ⟨P, E, hΓ,
      fun r m' hr => ih (toArgTup r) r m' budget depth
        (ctx_val_append (toArgTup_zip_val r) hG) hD hfun (hP r m' hr),
      hE⟩
  | jnz hc _ _ iht ihe =>
    intro m budget depth hG hD hfun ⟨ht, he⟩
    simp only [peelAux, wp]
    rw [flattenArg_val hG hc]
    exact ⟨fun h => iht m budget depth hG hD hfun (ht h),
           fun h => ihe m budget depth hG hD hfun (he h)⟩
  | @jump _ _ ts j₁ j₂ _ _ hj hargs =>
    intro m _ _ hG hD _ h
    have hlbl := hD _ hj
    simp only [wp] at h
    rw [← flattenArgs_vals hG hargs] at h
    cases j₁ with
    | outer l => simp only [peelAux, wp]; rw [hlbl]; exact h
    | subst _ k => exact hlbl.2 _ m h
    | probe _ => exact False.elim hlbl
  | ret hvs =>
    intro m _ _ hG _ _ h
    simp only [peelAux, wp] at h ⊢
    rw [flattenArgs_vals hG hvs]
    exact h
  | exit f hargs =>
    intro m _ _ hG _ _ h
    simp only [peelAux, wp] at h ⊢
    rw [flattenArgs_vals hG hargs]
    exact h
  | hlt =>
    intro _ _ _ _ _ _ h
    exact h
  | @group _ D sig b₁ b₂ k₁ _ hb _ ihb ihk =>
    intro m budget depth hG hD hfun h
    have hkeep :
        wp Γ Q X
          (.group (fun Js => peelBAux budget depth (b₁ (toOuterTup Js)))
                  (fun Js => peelAux budget depth (k₁ (toOuterTup Js)))) m := by
      simp only [wp]
      intro Js hc
      refine ihk (toOuterTup Js) Js m budget depth hG (PeelLabelWp.append_outer hD Js)
        (peelDFun_append_outer hD hfun Js) (h Js ?_)
      rw [closed_iff] at hc ⊢
      intro _ i xs m' hbi
      exact hc i xs m' (by
        rw [peelBAux_get]
        exact ihb (toOuterTup Js) Js i (toArgTup xs) xs m' budget depth
          (ctx_val_append (toArgTup_zip_val xs) hG)
          (PeelLabelWp.append_outer hD Js) (peelDFun_append_outer hD hfun Js) hbi)
    rcases sig with _ | ⟨ts, sig⟩
    · simp only [peelAux]
      exact hkeep
    · rcases sig with _ | ⟨ts', sig'⟩
      · simp only [peelAux]
        rw [loopBlockMetrics_eq (b₁ (.probe 0, ()))]
        cases hcan : canPeel budget
            (peelMetrics 0 1 ((b₁ (.probe 0, ())).get .here (immDefaults Val ts)))
            (peelMetrics 0 1 (k₁ (.probe 0, ())))
        · simp only [Bool.false_eq_true, ↓reduceIte]
          exact hkeep
        · simp only [↓reduceIte]
          let mb := peelMetrics 0 1
            ((b₁ (.probe 0, ())).get .here (immDefaults Val ts))
          let remBudget := (budget - mb.size) / 2
          let remIter2 : Tup (Arg Val) ts → Expr Val Cont rs := fun backArgs =>
            .group (sig := [ts])
              (fun Js => peelBAux remBudget (depth + 1) (b₁ (toOuterTup Js)))
              (fun Js => .jump Js.1 backArgs)
          let iter1 : Tup (Arg Val) ts → Expr Val Cont rs :=
            (peelArgBAux remBudget (depth + 1) (b₁ (.subst (2 * depth) remIter2, ()))).1
          let J_src : Cont ts := fun xs m' =>
            ∀ Js : Tup Cont [ts], Closed Γ Q X (b₂ Js) Js → Js.1 xs m'
          have hno : NoProbeGE 0 D := PeelLabelWp.noProbeGE hD
          have hno0 : ∀ (J : Cont ts), NoProbeGE 1 (⟨ts, .probe 0, J⟩ :: D) := by
            intro J ts' k' j₂ hm
            cases hm with
            | head => omega
            | tail _ hm => exact Nat.lt_trans (hno hm) Nat.zero_lt_one
          have liftProbe :
              ∀ {Ja Jb : Cont ts},
                (∀ ys m'', Ja ys m'' → Jb ys m'') →
                ∀ {xs m'},
                  wp Γ Q X ((b₂ (Ja, ())).get .here xs) m' →
                  wp Γ Q X ((b₂ (Jb, ())).get .here xs) m' := by
            intro Ja Jb hJ xs m' hbi
            refine wp_right_mono
              ((hb (.probe 0, ()) (Ja, ())).get .here (toArgTup xs) xs)
              1 (ctx_val_append (toArgTup_zip_val xs) hG)
              (hno0 Ja) (hno0 Jb)
              (fun hm1 hm2 ys m'' hj => by
                dsimp only [Tup.zip, List.cons_append, List.nil_append] at hm1 hm2
                cases hm1 with
                | head =>
                  cases hm2 with
                  | head => exact hJ ys m'' hj
                  | tail _ hm2 => exact absurd (hno hm2) (Nat.not_lt_zero _)
                | tail _ hm1 =>
                  cases hm2 with
                  | head => exact absurd (hno hm1) (Nat.not_lt_zero _)
                  | tail _ hm2 => rw [← hfun hm1 hm2]; exact hj)
              ((hb (.probe 0, ()) (Jb, ())).get .here (toArgTup xs) xs) m' hbi
          have hclosed_src : Closed Γ Q X (b₂ (J_src, ())) (J_src, ()) := by
            rw [closed_iff]
            intro _ i xs m' hbi
            cases i with
            | here =>
              intro Js hcJs
              have hmono := liftProbe (fun ys m'' hj => hj Js hcJs) hbi
              rw [closed_iff] at hcJs
              exact hcJs .here xs m' hmono
            | there i => exact nomatch i
          have hRem : PeelLabelWp Γ Q X (2 * (depth + 1)) ts
              (.subst (2 * depth) remIter2) J_src := by
            refine ⟨by omega, fun backArgs m' hjsrc Js hc_rem => ?_⟩
            apply hjsrc Js
            rw [closed_iff]
            intro _ i xs m'' hbi
            rw [closed_iff] at hc_rem
            exact hc_rem i xs m'' (by
              rw [peelBAux_get]
              exact ihb (toOuterTup Js) Js i (toArgTup xs) xs m'' remBudget (depth + 1)
                (ctx_val_append (toArgTup_zip_val xs) hG)
                (fun p hp => (PeelLabelWp.append_outer hD Js p hp).weakenBound (by omega))
                (peelDFun_append_outer hD hfun Js) hbi)
          let J_step : Cont ts := fun xs m' =>
            wp Γ Q X ((b₂ (J_src, ())).get .here xs) m'
          have hclosed_step : Closed Γ Q X (b₂ (J_step, ())) (J_step, ()) := by
            rw [closed_iff]
            intro _ i xs m' hbi
            cases i with
            | here =>
              exact liftProbe (fun ys m'' hj => by
                rw [closed_iff] at hclosed_src
                exact hclosed_src .here ys m'' hj) hbi
            | there i => exact nomatch i
          have hIter1 : PeelLabelWp Γ Q X (2 * (depth + 1)) ts
              (.subst (2 * depth + 1) iter1) J_src := by
            refine ⟨by omega, fun initArgs m' hjsrc => ?_⟩
            have hstep : wp Γ Q X ((b₂ (J_src, ())).get .here (vals initArgs)) m' :=
              hjsrc (J_step, ()) hclosed_step
            dsimp only [iter1]
            rw [peelArgBAux_fst]
            exact ihb (.subst (2 * depth) remIter2, ()) (J_src, ()) .here initArgs (vals initArgs)
              m' remBudget (depth + 1)
              (ctx_val_append (ctx_zip_vals initArgs) hG)
              (PeelLabelWp.cons_subst (by omega) hD hRem)
              (peelDFun_cons_subst hD hfun (by omega) remIter2 J_src)
              hstep
          exact ihk (.subst (2 * depth + 1) iter1, ()) (J_src, ()) m budget (depth + 1) hG
            (PeelLabelWp.cons_subst (by omega) hD hIter1)
            (peelDFun_cons_subst hD hfun (by omega) iter1 J_src)
            (h (J_src, ()) hclosed_src)
      · simp only [peelAux]
        exact hkeep

end Peel

/-! ## Main Style-A soundness and well-formedness theorems -/

/-- Expression-level relational well-formedness preservation for `peel`, proved via `Wf.induct`. -/
theorem peel_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G₀ : Ctx (Arg V₁) (Arg V₂)} {D₀ : Ctx (Peel.PeelL V₁ L₁ rs) (Peel.PeelL V₂ L₂ rs)}
    {e₁ : Expr (Arg V₁) (Peel.PeelL V₁ L₁ rs) rs}
    {e₂ : Expr (Arg V₂) (Peel.PeelL V₂ L₂ rs) rs}
    (hwf : Wf G₀ D₀ e₁ e₂) :
    ∀ {G' : Ctx V₁ V₂} {D' : Ctx L₁ L₂},
      (∀ p ∈ G₀, ArgRel G' p.1 p.2.1 p.2.2) →
      (∀ p ∈ D₀, Peel.PeelLabelWf G' D' p.1 p.2.1 p.2.2) →
      ∀ budget, Wf G' D' (peel budget e₁) (peel budget e₂) :=
  fun hG hD budget => Peel.peelAux_wf hwf hG hD budget 0

/-- Expression-level WP soundness for `peel`, proved via `Wf.induct` and direct `wp` group
unrolling. -/
theorem peel_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {G₀ : Ctx (Arg Val) Val} {D₀ : Ctx (Peel.PeelL Val Cont rs) Cont}
    {e₁ : Expr (Arg Val) (Peel.PeelL Val Cont rs) rs} {e₂ : Expr Val Cont rs}
    (hwf : Wf G₀ D₀ e₁ e₂) :
    ∀ m budget, (∀ p ∈ G₀, p.2.1.val = p.2.2) →
      (∀ p ∈ D₀, Peel.PeelLabelWp Γ Q X 0 p.1 p.2.1 p.2.2) →
      Peel.PeelDFun D₀ →
      wp Γ Q X e₂ m → wp Γ Q X (peel budget e₁) m :=
  fun m budget hG hD hfun h => Peel.peelAux_wp hwf m budget 0 hG hD hfun h

/-- Closed-function well-formedness preservation for `Func.peel`. -/
theorem Func.peel_wf {as rs : List Ty} {f : Func as rs} (hf : f.Wf)
    (maxLoopSize : Nat := 40) : (Func.peel f maxLoopSize).Wf := by
  intro V₁ V₂ L₁ L₂ xs₁ xs₂
  have hwf := hf (Arg V₁) (Arg V₂) (Peel.PeelL V₁ L₁ rs) (Peel.PeelL V₂ L₂ rs)
    (Peel.toArgTup xs₁) (Peel.toArgTup xs₂)
  exact LeanQbe.T.peel_wf hwf (Peel.mem_zip_toArgTup xs₁ xs₂)
    (fun _ hp => nomatch hp) maxLoopSize

/-- Closed-function WP refinement for `Func.peel`. -/
theorem Func.peel_spec {as rs : List Ty} {f : Func as rs} (hf : f.Wf)
    (maxLoopSize : Nat := 40) {Γ : Env} {xs : Tup Val as} {m : Mem 64}
    {Q : Post rs} {X : XPost} (h : Func.spec Γ f xs m Q X) :
    Func.spec Γ (Func.peel f maxLoopSize) xs m Q X := by
  have hwf := hf (Arg Val) Val (Peel.PeelL Val Cont rs) Cont (Peel.toArgTup xs) xs
  exact LeanQbe.T.peel_wp hwf m maxLoopSize (Peel.toArgTup_zip_val xs)
    (fun _ hp => nomatch hp) (fun hm _ => nomatch hm) h

/-- Named-function well-formedness preservation for `Fn.peel`. -/
theorem Fn.peel_wf {fn : Fn} (hfn : fn.Wf) (maxLoopSize : Nat := 40) :
    (fn.peel maxLoopSize).Wf :=
  Func.peel_wf hfn maxLoopSize

/-- Named-function WP refinement for `Fn.peel`. -/
theorem Fn.peel_spec (fn : Fn) (hfn : fn.Wf) (maxLoopSize : Nat := 40)
    {Γ : Env} {xs : Tup Val fn.as} {m : Mem 64} {Q : Post fn.rs} {X : XPost}
    (h : Func.spec Γ fn.body xs m Q X) :
    Func.spec Γ (fn.peel maxLoopSize).body xs m Q X :=
  Func.peel_spec hfn maxLoopSize h

end LeanQbe.T
