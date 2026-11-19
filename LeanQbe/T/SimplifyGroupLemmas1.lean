module

public import LeanQbe.T.SimplifyGroup
public import LeanQbe.T.OptUtil
public import LeanQbe.T.WfLemmas

/-!
# Correctness Proofs for `SimplifyGroup` (`O-M2`)

Proves static shape congruence, reachability-fixpoint closure, relational well-formedness
preservation, and weakest-precondition refinement for PHOAS join-group simplification:

* `OuterWf (chk : Bool)`: unified label-capture-free structural equivalence (`chk = false`) and
  value-carrying well-formedness (`chk = true`) over `OptV` and `JLabel`.
* `reachLoop_spec`: fixed-point reachability closure for `reachLoop adj (sig.length + 1) init`.
* `simplifyGroup_wf` / `Func.simplifyGroup_wf`: `Wf` preservation across dead-group unwrap,
  dead-block elimination, and single-use join-block splicing.
* `simplifyGroup_wp` / `Func.simplifyGroup_spec`: `wp` and `Func.spec` refinement.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

namespace SgImpl

/-! ## Small Nat / List helpers and `OuterWf` compatibility predicates -/

theorem add_eq {a b c d : Nat} (h1 : a = c) (h2 : b = d) : a + b = c + d := by rw [h1, h2]

/-- Remove the first occurrence of `y` from `xs` (for elementary `Nodup` counting). -/
def rmNat (y : Nat) : List Nat → List Nat
  | [] => []
  | x :: xs => if x == y then xs else x :: rmNat y xs

theorem rmNat_mem {x y : Nat} : ∀ {xs : List Nat}, x ∈ rmNat y xs → x ∈ xs
  | [], h => nomatch h
  | z :: zs, h => by
    simp only [rmNat] at h; split at h
    · exact .tail _ h
    · exact (List.mem_cons.1 h).elim (· ▸ List.mem_cons_self) (fun h => .tail _ (rmNat_mem h))

theorem rmNat_ne {x y : Nat} : ∀ {xs : List Nat}, xs.Nodup → x ∈ rmNat y xs → x ≠ y
  | [], _, h => nomatch h
  | z :: zs, hnd, hx => by
    rcases List.nodup_cons.1 hnd with ⟨hz, hzs⟩
    simp only [rmNat] at hx; split at hx
    · rename_i heq; have hzy : z = y := beq_iff_eq.1 heq
      intro hxy; exact hz (hzy ▸ hxy ▸ hx)
    · rename_i hne
      rcases List.mem_cons.1 hx with rfl | hx
      · exact fun h => hne (beq_iff_eq.2 h)
      · exact rmNat_ne hzs hx

theorem rmNat_nodup {y : Nat} : ∀ {xs : List Nat}, xs.Nodup → (rmNat y xs).Nodup
  | [], h => h
  | _ :: zs, hnd => by
    rcases List.nodup_cons.1 hnd with ⟨hz, hzs⟩
    simp only [rmNat]; split
    · exact hzs
    · exact List.nodup_cons.2 ⟨fun hm => hz (rmNat_mem hm), rmNat_nodup hzs⟩

theorem rmNat_length {y : Nat} : ∀ {xs : List Nat}, y ∈ xs → (rmNat y xs).length + 1 = xs.length
  | [], h => nomatch h
  | z :: zs, h => by
    simp only [rmNat]; split
    · simp
    · rename_i hne
      have hzs : y ∈ zs := (List.mem_cons.1 h).elim (fun e => by simp [e] at hne) id
      simp [rmNat_length hzs]

/-- Whether a `JLabel L ts` is an un-instantiated local `.loc` binder. -/
def isLocLbl {L : List Ty → Type} {ts : List Ty} : JLabel L ts → Bool
  | .loc _ => true
  | .outer _ | .probe => false

theorem isLocLbl_probe {L₁ L₂ : List Ty → Type} : (sig : List (List Ty)) →
    ∀ p ∈ Tup.zip (probeLabels (L := L₁) sig) (probeLabels (L := L₂) sig),
      isLocLbl p.2.1 = false ∧ isLocLbl p.2.2 = false
  | [], _, hp => nomatch hp
  | _ :: _, _, .head _ => ⟨rfl, rfl⟩
  | _ :: sig, p, .tail _ hp => isLocLbl_probe sig p hp

theorem isLocLbl_outer {L₁ L₂ : List Ty → Type} :
    {sig : List (List Ty)} → (Js₁ : Tup L₁ sig) → (Js₂ : Tup L₂ sig) →
    ∀ p ∈ Tup.zip (Js₁.map fun _ l => JLabel.outer l) (Js₂.map fun _ l => JLabel.outer l),
      isLocLbl p.2.1 = false ∧ isLocLbl p.2.2 = false
  | [], (), (), _, hp => nomatch hp
  | _ :: _, (_, _), (_, _), _, .head _ => ⟨rfl, rfl⟩
  | _ :: _, (_, Js₁), (_, Js₂), p, .tail _ hp => isLocLbl_outer Js₁ Js₂ p hp

theorem isLocLbl_probe_outer {L₁ L₂ : List Ty → Type} :
    {sig : List (List Ty)} → (Js : Tup L₂ sig) →
    ∀ p ∈ Tup.zip (probeLabels (L := L₁) sig) (Js.map fun _ l => JLabel.outer l),
      isLocLbl p.2.1 = false ∧ isLocLbl p.2.2 = false
  | [], (), _, hp => nomatch hp
  | _ :: _, (_, _), _, .head _ => ⟨rfl, rfl⟩
  | _ :: _, (_, Js), p, .tail _ hp => isLocLbl_probe_outer Js p hp

theorem isLocLbl_zip_probe {L₁ L₂ : List Ty → Type} :
    {sig : List (List Ty)} → (Js₁ : Tup (JLabel L₁) sig) → (Js₂ : Tup (JLabel L₂) sig) →
    (∀ p ∈ Tup.zip Js₁ Js₂, isLocLbl p.2.1 = false ∧ isLocLbl p.2.2 = false) →
    ∀ p ∈ Tup.zip Js₁ (probeLabels (L := L₂) sig),
      isLocLbl p.2.1 = false ∧ isLocLbl p.2.2 = false
  | [], (), (), _, _, hp => nomatch hp
  | _ :: _, (_, _), (_, _), hno, _, .head _ => ⟨(hno _ List.mem_cons_self).1, rfl⟩
  | _ :: _, (_, Js₁), (_, Js₂), hno, p, .tail _ hp =>
    isLocLbl_zip_probe Js₁ Js₂ (fun q hq => hno q (.tail _ hq)) p hp

/-- Label-context compatibility ensuring static analyzers agree across `OuterWf false`. -/
def LblCompat {L₁ L₂ : List Ty → Type} (D : Ctx (JLabel L₁) (JLabel L₂)) : Prop :=
  ∀ p ∈ D, match p.2.1, p.2.2 with
    | .loc d₁, .loc d₂ => d₁ = d₂
    | j₁, j₂ => isLocLbl j₁ = false ∧ isLocLbl j₂ = false

theorem LblCompat.append_noLoc {L₁ L₂ : List Ty → Type} {D : Ctx (JLabel L₁) (JLabel L₂)}
    {sig : List (List Ty)} {Js₁ : Tup (JLabel L₁) sig} {Js₂ : Tup (JLabel L₂) sig}
    (hD : LblCompat D)
    (hno : ∀ p ∈ Tup.zip Js₁ Js₂, isLocLbl p.2.1 = false ∧ isLocLbl p.2.2 = false) :
    LblCompat (Tup.zip Js₁ Js₂ ++ D) := fun p hp => by
  rcases List.mem_append.1 hp with hp | hp
  · have := hno p hp; cases h1 : p.2.1 <;> cases h2 : p.2.2 <;> simp_all [isLocLbl]
  · exact hD p hp

theorem LblCompat.append_probe {L₁ L₂ : List Ty → Type} {D : Ctx (JLabel L₁) (JLabel L₂)}
    (hD : LblCompat D) (sig : List (List Ty)) :
    LblCompat (Tup.zip (probeLabels (L := L₁) sig) (probeLabels (L := L₂) sig) ++ D) :=
  hD.append_noLoc (isLocLbl_probe sig)

def BoundedD (depth : Nat) {L₁ L₂ : List Ty → Type}
    (D : Ctx (JLabel L₁) (JLabel L₂)) : Prop :=
  ∀ p ∈ D, match p.2.1, p.2.2 with
    | .loc d₁, .loc d₂ => d₁ = d₂ ∧ d₁ < depth
    | j₁, j₂ => isLocLbl j₁ = false ∧ isLocLbl j₂ = false

theorem boundedD_lblCompat {depth : Nat} {L₁ L₂ : List Ty → Type}
    {D : Ctx (JLabel L₁) (JLabel L₂)} (h : BoundedD depth D) : LblCompat D := fun p hp => by
  have := h p hp; cases h1 : p.2.1 <;> cases h2 : p.2.2 <;> simp_all

theorem boundedD_append_loc {L₁ L₂ : List Ty → Type} :
    (sig : List (List Ty)) → (d depth : Nat) → d ≥ depth →
    {D : Ctx (JLabel L₁) (JLabel L₂)} → BoundedD depth D →
    BoundedD (d + sig.length)
      (Tup.zip (locLabels (L := L₁) sig d) (locLabels (L := L₂) sig d) ++ D)
  | [], _, _, _, _, hD, p, hp => by
    have := hD p hp; cases h1 : p.2.1 <;> cases h2 : p.2.2 <;> simp_all <;> omega
  | _ :: sig, d, depth, hd, _, hD, p, hp => by
    simp only [locLabels, Tup.zip, List.cons_append, List.length_cons] at hp ⊢
    cases hp with
    | head => exact ⟨rfl, by omega⟩
    | tail _ hp =>
      have ih := boundedD_append_loc sig (d + 1) depth (by omega) hD p hp
      rw [show d + 1 + sig.length = d + (sig.length + 1) by omega] at ih
      exact ih

theorem locLabels_mem_le {L₁ L₂ : List Ty → Type} {ts : List Ty} {q : Nat} :
    ∀ (s : List (List Ty)) (d : Nat),
      ⟨ts, JLabel.loc q, JLabel.loc q⟩ ∈
        Tup.zip (locLabels (L := L₁) s d) (locLabels (L := L₂) s d) → d ≤ q
  | [], _, h => nomatch h
  | _ :: _, _, .head _ => Nat.le_refl _
  | _ :: s, d, .tail _ h => Nat.le_trans (Nat.le_succ _) (locLabels_mem_le s (d + 1) h)

/-! ## Unified `OuterWf (chk : Bool)` and `OuterWfS` relation -/

mutual
/-- Unified shape congruence (`chk = false`) and outer-binder well-formedness (`chk = true`)
over `Expr (OptV V) (JLabel L) rs`, forbidding `.loc` capture on `.group` binders. -/
inductive OuterWf (chk : Bool) {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty} :
    Ctx (OptV V₁) (OptV V₂) → Ctx (JLabel L₁) (JLabel L₂) →
    Expr (OptV V₁) (JLabel L₁) rs → Expr (OptV V₂) (JLabel L₂) rs → Prop
  | let_ {G D ts op₁ op₂ k₁ k₂} :
      (chk = true → OpRel G op₁ op₂) →
      (∀ (xs₁ : Tup (OptV V₁) ts) (xs₂ : Tup (OptV V₂) ts),
        (chk = true → ∃ y₁ y₂, xs₁ = someTup ts y₁ ∧ xs₂ = someTup ts y₂) →
        OuterWf chk (Tup.zip xs₁ xs₂ ++ G) D (k₁ xs₁) (k₂ xs₂)) →
      OuterWf chk G D (.let_ (ts := ts) op₁ k₁) (.let_ op₂ k₂)
  | load {G D} (t : Ty) {a₁ a₂ k₁ k₂} :
      (chk = true → ArgRel G i64 a₁ a₂) →
      (∀ (v₁ : OptV V₁ t) (v₂ : OptV V₂ t),
        (chk = true → ∃ u₁ u₂, v₁ = some u₁ ∧ v₂ = some u₂) →
        OuterWf chk (⟨t, v₁, v₂⟩ :: G) D (k₁ v₁) (k₂ v₂)) →
      OuterWf chk G D (.load t a₁ k₁) (.load t a₂ k₂)
  | store {G D t v₁ v₂ a₁ a₂ k₁ k₂} :
      (chk = true → ArgRel G t v₁ v₂) → (chk = true → ArgRel G i64 a₁ a₂) →
      OuterWf chk G D k₁ k₂ →
      OuterWf chk G D (.store (t := t) v₁ a₁ k₁) (.store v₂ a₂ k₂)
  | call {G D} (f : Sym) {as bs args₁ args₂ k₁ k₂} :
      (chk = true → TRel (ArgRel G) args₁ args₂) →
      (∀ (xs₁ : Tup (OptV V₁) bs) (xs₂ : Tup (OptV V₂) bs),
        (chk = true → ∃ y₁ y₂, xs₁ = someTup bs y₁ ∧ xs₂ = someTup bs y₂) →
        OuterWf chk (Tup.zip xs₁ xs₂ ++ G) D (k₁ xs₁) (k₂ xs₂)) →
      OuterWf chk G D (.call f (as := as) (bs := bs) args₁ k₁) (.call f args₂ k₂)
  | jnz {G D c₁ c₂ t₁ t₂ e₁ e₂} :
      (chk = true → ArgRel G .bool c₁ c₂) →
      OuterWf chk G D t₁ t₂ → OuterWf chk G D e₁ e₂ →
      OuterWf chk G D (.jnz c₁ t₁ e₁) (.jnz c₂ t₂ e₂)
  | jump {G D ts j₁ j₂ args₁ args₂} :
      ⟨ts, j₁, j₂⟩ ∈ D → (chk = true → TRel (ArgRel G) args₁ args₂) →
      OuterWf chk G D (.jump (ts := ts) j₁ args₁) (.jump j₂ args₂)
  | ret {G D vs₁ vs₂} :
      (chk = true → TRel (ArgRel G) vs₁ vs₂) → OuterWf chk G D (.ret vs₁) (.ret vs₂)
  | exit {G D} (f : Sym) {as args₁ args₂} :
      (chk = true → TRel (ArgRel G) args₁ args₂) →
      OuterWf chk G D (.exit f (as := as) args₁) (.exit f args₂)
  | hlt {G D} : OuterWf chk G D .hlt .hlt
  | group {G D sig b₁ b₂ k₁ k₂} :
      (∀ (Js₁ : Tup (JLabel L₁) sig) (Js₂ : Tup (JLabel L₂) sig),
        (∀ p ∈ Tup.zip Js₁ Js₂, isLocLbl p.2.1 = false ∧ isLocLbl p.2.2 = false) →
        OuterWfB chk G (Tup.zip Js₁ Js₂ ++ D) (b₁ Js₁) (b₂ Js₂)) →
      (∀ (Js₁ : Tup (JLabel L₁) sig) (Js₂ : Tup (JLabel L₂) sig),
        (∀ p ∈ Tup.zip Js₁ Js₂, isLocLbl p.2.1 = false ∧ isLocLbl p.2.2 = false) →
        OuterWf chk G (Tup.zip Js₁ Js₂ ++ D) (k₁ Js₁) (k₂ Js₂)) →
      OuterWf chk G D (.group (sig := sig) b₁ k₁) (.group b₂ k₂)

inductive OuterWfB (chk : Bool) {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty} :
    Ctx (OptV V₁) (OptV V₂) → Ctx (JLabel L₁) (JLabel L₂) → {sig : List (List Ty)} →
    Blocks (OptV V₁) (JLabel L₁) rs sig → Blocks (OptV V₂) (JLabel L₂) rs sig → Prop
  | nil {G D} : OuterWfB chk G D .nil .nil
  | cons {G D ts sig b₁ b₂ bs₁ bs₂} :
      (∀ (xs₁ : Tup (OptV V₁) ts) (xs₂ : Tup (OptV V₂) ts),
        (chk = true → ∃ y₁ y₂, xs₁ = someTup ts y₁ ∧ xs₂ = someTup ts y₂) →
        OuterWf chk (Tup.zip xs₁ xs₂ ++ G) D (b₁ xs₁) (b₂ xs₂)) →
      OuterWfB chk G D bs₁ bs₂ →
      OuterWfB chk G D (.cons (ts := ts) (sig := sig) b₁ bs₁) (.cons b₂ bs₂)
end

inductive OuterWfS (chk : Bool) {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty} :
    Ctx (OptV V₁) (OptV V₂) → Ctx (JLabel L₁) (JLabel L₂) → {sig : List (List Ty)} →
    SBlocks (OptV V₁) (JLabel L₁) rs sig → SBlocks (OptV V₂) (JLabel L₂) rs sig → Prop
  | nil {G D} : OuterWfS chk G D .nil .nil
  | cons {G D ts sig b₁ b₂ bs₁ bs₂} :
      (∀ {G'} (a₁ : Tup (Arg (OptV V₁)) ts) (a₂ : Tup (Arg (OptV V₂)) ts),
        (∀ p ∈ G, p ∈ G') → (chk = true → TRel (ArgRel G') a₁ a₂) →
        OuterWf chk G' D (b₁ a₁) (b₂ a₂)) →
      OuterWfS chk G D bs₁ bs₂ →
      OuterWfS chk G D (.cons (ts := ts) (sig := sig) b₁ bs₁) (.cons b₂ bs₂)

theorem TRel.toArgTup_mem {V₁ V₂ : Ty → Type} {G : Ctx V₁ V₂} :
    {ts : List Ty} → (xs₁ : Tup V₁ ts) → (xs₂ : Tup V₂ ts) →
    TRel (ArgRel (Tup.zip xs₁ xs₂ ++ G)) (toArgTup xs₁) (toArgTup xs₂)
  | [], (), () => .nil
  | _ :: _, (_, xs₁), (_, xs₂) =>
    .cons (.var List.mem_cons_self)
      ((TRel.toArgTup_mem xs₁ xs₂).argRel_weaken fun _ h => .tail _ h)

theorem OuterWfS.to_blocks {chk : Bool} {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type}
    {rs : List Ty} {G : Ctx (OptV V₁) (OptV V₂)} {D : Ctx (JLabel L₁) (JLabel L₂)} :
    {sig : List (List Ty)} →
    {bs₁ : SBlocks (OptV V₁) (JLabel L₁) rs sig} →
    {bs₂ : SBlocks (OptV V₂) (JLabel L₂) rs sig} →
    OuterWfS chk G D bs₁ bs₂ → OuterWfB chk G D (sblocksToBlocks bs₁) (sblocksToBlocks bs₂)
  | _, _, _, .nil => .nil
  | _, _, _, .cons hb hbs =>
    .cons (fun xs₁ xs₂ _ =>
        hb (toArgTup xs₁) (toArgTup xs₂) (fun _ hp => List.mem_append_right _ hp)
          fun _ => TRel.toArgTup_mem xs₁ xs₂)
      hbs.to_blocks

mutual
theorem OuterWf.weaken_D {chk : Bool} {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty} :
    {G : Ctx (OptV V₁) (OptV V₂)} → {D₁ D₂ : Ctx (JLabel L₁) (JLabel L₂)} →
    (∀ p ∈ D₁, p ∈ D₂) →
    {e₁ : Expr (OptV V₁) (JLabel L₁) rs} → {e₂ : Expr (OptV V₂) (JLabel L₂) rs} →
    OuterWf chk G D₁ e₁ e₂ → OuterWf chk G D₂ e₁ e₂
  | _, _, _, hsub, _, _, .let_ hop hk => .let_ hop fun xs₁ xs₂ hx => (hk xs₁ xs₂ hx).weaken_D hsub
  | _, _, _, hsub, _, _, .load t ha hk => .load t ha fun v₁ v₂ hv => (hk v₁ v₂ hv).weaken_D hsub
  | _, _, _, hsub, _, _, .store hv ha hk => .store hv ha (hk.weaken_D hsub)
  | _, _, _, hsub, _, _, .call f hargs hk =>
    .call f hargs fun xs₁ xs₂ hx => (hk xs₁ xs₂ hx).weaken_D hsub
  | _, _, _, hsub, _, _, .jnz hc ht he => .jnz hc (ht.weaken_D hsub) (he.weaken_D hsub)
  | _, _, _, hsub, _, _, .jump hj hargs => .jump (hsub _ hj) hargs
  | _, _, _, _, _, _, .ret hvs => .ret hvs
  | _, _, _, _, _, _, .exit f hargs => .exit f hargs
  | _, _, _, _, _, _, .hlt => .hlt
  | _, _, _, hsub, _, _, .group hb hk =>
    .group (fun Js₁ Js₂ hno => (hb Js₁ Js₂ hno).weaken_D (append_sub_left _ hsub))
           (fun Js₁ Js₂ hno => (hk Js₁ Js₂ hno).weaken_D (append_sub_left _ hsub))

theorem OuterWfB.weaken_D {chk : Bool} {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type}
    {rs : List Ty} :
    {G : Ctx (OptV V₁) (OptV V₂)} → {D₁ D₂ : Ctx (JLabel L₁) (JLabel L₂)} →
    (∀ p ∈ D₁, p ∈ D₂) → {sig : List (List Ty)} →
    {bs₁ : Blocks (OptV V₁) (JLabel L₁) rs sig} → {bs₂ : Blocks (OptV V₂) (JLabel L₂) rs sig} →
    OuterWfB chk G D₁ bs₁ bs₂ → OuterWfB chk G D₂ bs₁ bs₂
  | _, _, _, _, _, _, _, .nil => .nil
  | _, _, _, hsub, _, _, _, .cons hb hbs =>
    .cons (fun xs₁ xs₂ hx => (hb xs₁ xs₂ hx).weaken_D hsub) (hbs.weaken_D hsub)
end

/-! ## Analyzer invariance under `OuterWf false` -/

theorem outerWf_isJumpTo {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx (OptV V₁) (OptV V₂)} {D : Ctx (JLabel L₁) (JLabel L₂)}
    {e₁ : Expr (OptV V₁) (JLabel L₁) rs} {e₂ : Expr (OptV V₂) (JLabel L₂) rs}
    (hD : LblCompat D) (hsh : OuterWf false G D e₁ e₂) (targetId : Nat) (targetTs : List Ty) :
    isJumpTo targetId targetTs e₁ = isJumpTo targetId targetTs e₂ := by
  cases hsh with
  | @jump _ _ _ j₁ j₂ _ _ hj _ =>
    have hc := hD _ hj; cases j₁ <;> cases j₂ <;> simp_all [isJumpTo, isLocLbl]
  | _ => rfl

mutual
theorem outerWf_countJumps {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    (targetId : Nat) :
    {G : Ctx (OptV V₁) (OptV V₂)} → {D : Ctx (JLabel L₁) (JLabel L₂)} → LblCompat D →
    {e₁ : Expr (OptV V₁) (JLabel L₁) rs} → {e₂ : Expr (OptV V₂) (JLabel L₂) rs} →
    OuterWf false G D e₁ e₂ → countJumps targetId e₁ = countJumps targetId e₂
  | _, _, hD, _, _, .let_ _ hk => by
    simp only [countJumps]
    exact outerWf_countJumps targetId hD (hk (noneTup _) (noneTup _) (fun h => by cases h))
  | _, _, hD, _, _, .load _ _ hk => by
    simp only [countJumps]
    exact outerWf_countJumps targetId hD (hk none none (fun h => by cases h))
  | _, _, hD, _, _, .store _ _ hk => by
    simp only [countJumps]; exact outerWf_countJumps targetId hD hk
  | _, _, hD, _, _, .call _ (bs := bs) _ hk => by
    simp only [countJumps]
    exact outerWf_countJumps targetId hD (hk (noneTup bs) (noneTup bs) (fun h => by cases h))
  | _, _, hD, _, _, .jnz _ ht he =>
    add_eq (outerWf_countJumps targetId hD ht) (outerWf_countJumps targetId hD he)
  | _, _, hD, _, _, .jump (j₁ := j₁) (j₂ := j₂) hj _ => by
    have hc := hD _ hj; cases j₁ <;> cases j₂ <;> simp_all [countJumps, isLocLbl]
  | _, _, _, _, _, .ret _ | _, _, _, _, _, .exit _ _ | _, _, _, _, _, .hlt => rfl
  | _, _, hD, _, _, .group (sig := sig) hb hk => by
    simp only [countJumps]
    exact add_eq
      (outerWfB_countJumpsB targetId (hD.append_probe sig)
        (hb (probeLabels sig) (probeLabels sig) (isLocLbl_probe sig)))
      (outerWf_countJumps targetId (hD.append_probe sig)
        (hk (probeLabels sig) (probeLabels sig) (isLocLbl_probe sig)))

theorem outerWfB_countJumpsB {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    (targetId : Nat) :
    {G : Ctx (OptV V₁) (OptV V₂)} → {D : Ctx (JLabel L₁) (JLabel L₂)} → LblCompat D →
    {sig : List (List Ty)} →
    {bs₁ : Blocks (OptV V₁) (JLabel L₁) rs sig} → {bs₂ : Blocks (OptV V₂) (JLabel L₂) rs sig} →
    OuterWfB false G D bs₁ bs₂ → countJumpsB targetId bs₁ = countJumpsB targetId bs₂
  | _, _, _, _, _, _, .nil => rfl
  | _, _, hD, _, _, _, .cons hb hbs =>
    add_eq (outerWf_countJumps targetId hD (hb (noneTup _) (noneTup _) (fun h => by cases h)))
      (outerWfB_countJumpsB targetId hD hbs)
end

mutual
theorem outerWf_exprSizeJ {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty} :
    {G : Ctx (OptV V₁) (OptV V₂)} → {D : Ctx (JLabel L₁) (JLabel L₂)} →
    {e₁ : Expr (OptV V₁) (JLabel L₁) rs} → {e₂ : Expr (OptV V₂) (JLabel L₂) rs} →
    OuterWf false G D e₁ e₂ → exprSizeJ e₁ = exprSizeJ e₂
  | _, _, _, _, .let_ _ hk =>
    congrArg (1 + ·) (outerWf_exprSizeJ (hk (noneTup _) (noneTup _) (fun h => by cases h)))
  | _, _, _, _, .load _ _ hk =>
    congrArg (1 + ·) (outerWf_exprSizeJ (hk none none (fun h => by cases h)))
  | _, _, _, _, .store _ _ hk => congrArg (1 + ·) (outerWf_exprSizeJ hk)
  | _, _, _, _, .call _ _ hk =>
    congrArg (1 + ·) (outerWf_exprSizeJ (hk (noneTup _) (noneTup _) (fun h => by cases h)))
  | _, _, _, _, .jnz _ ht he => by
    simp only [exprSizeJ]; rw [outerWf_exprSizeJ ht, outerWf_exprSizeJ he]
  | _, _, _, _, .jump _ _ | _, _, _, _, .ret _ | _, _, _, _, .exit _ _ | _, _, _, _, .hlt => rfl
  | _, _, _, _, .group (sig := sig) hb hk => by
    simp only [exprSizeJ]
    rw [outerWfB_blocksSizeJ (hb (probeLabels sig) (probeLabels sig) (isLocLbl_probe sig)),
      outerWf_exprSizeJ (hk (probeLabels sig) (probeLabels sig) (isLocLbl_probe sig))]

theorem outerWfB_blocksSizeJ {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty} :
    {G : Ctx (OptV V₁) (OptV V₂)} → {D : Ctx (JLabel L₁) (JLabel L₂)} →
    {sig : List (List Ty)} →
    {bs₁ : Blocks (OptV V₁) (JLabel L₁) rs sig} → {bs₂ : Blocks (OptV V₂) (JLabel L₂) rs sig} →
    OuterWfB false G D bs₁ bs₂ → blocksSizeJ bs₁ = blocksSizeJ bs₂
  | _, _, _, _, _, .nil => rfl
  | _, _, _, _, _, .cons hb hbs =>
    add_eq (outerWf_exprSizeJ (hb (noneTup _) (noneTup _) (fun h => by cases h)))
      (outerWfB_blocksSizeJ hbs)
end

mutual
theorem outerWf_collectJumps {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    (lo hi : Nat) :
    {G : Ctx (OptV V₁) (OptV V₂)} → {D : Ctx (JLabel L₁) (JLabel L₂)} → LblCompat D →
    {e₁ : Expr (OptV V₁) (JLabel L₁) rs} → {e₂ : Expr (OptV V₂) (JLabel L₂) rs} →
    OuterWf false G D e₁ e₂ → (acc : List Nat) →
    collectJumps lo hi e₁ acc = collectJumps lo hi e₂ acc
  | _, _, hD, _, _, .let_ _ hk, acc =>
    outerWf_collectJumps lo hi hD (hk (noneTup _) (noneTup _) (fun h => by cases h)) acc
  | _, _, hD, _, _, .load _ _ hk, acc =>
    outerWf_collectJumps lo hi hD (hk none none (fun h => by cases h)) acc
  | _, _, hD, _, _, .store _ _ hk, acc => outerWf_collectJumps lo hi hD hk acc
  | _, _, hD, _, _, .call _ _ hk, acc =>
    outerWf_collectJumps lo hi hD (hk (noneTup _) (noneTup _) (fun h => by cases h)) acc
  | _, _, hD, _, _, .jnz _ ht he, acc => by
    simp only [collectJumps]
    rw [outerWf_collectJumps lo hi hD ht acc, outerWf_collectJumps lo hi hD he]
  | _, _, hD, _, _, .jump (j₁ := j₁) (j₂ := j₂) hj _, acc => by
    have hc := hD _ hj; cases j₁ <;> cases j₂ <;> simp_all [collectJumps, isLocLbl]
  | _, _, _, _, _, .ret _, _ | _, _, _, _, _, .exit _ _, _ | _, _, _, _, _, .hlt, _ => rfl
  | _, _, hD, _, _, .group (sig := sig) hb hk, acc => by
    simp only [collectJumps]
    rw [outerWfB_collectJumpsB lo hi (hD.append_probe sig)
      (hb (probeLabels sig) (probeLabels sig) (isLocLbl_probe sig)) acc]
    exact outerWf_collectJumps lo hi (hD.append_probe sig)
      (hk (probeLabels sig) (probeLabels sig) (isLocLbl_probe sig)) _

theorem outerWfB_collectJumpsB {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    (lo hi : Nat) :
    {G : Ctx (OptV V₁) (OptV V₂)} → {D : Ctx (JLabel L₁) (JLabel L₂)} → LblCompat D →
    {sig : List (List Ty)} →
    {bs₁ : Blocks (OptV V₁) (JLabel L₁) rs sig} → {bs₂ : Blocks (OptV V₂) (JLabel L₂) rs sig} →
    OuterWfB false G D bs₁ bs₂ → (acc : List Nat) →
    collectJumpsB lo hi bs₁ acc = collectJumpsB lo hi bs₂ acc
  | _, _, _, _, _, _, .nil, _ => rfl
  | _, _, hD, _, _, _, .cons hb hbs, acc => by
    simp only [collectJumpsB]
    rw [outerWf_collectJumps lo hi hD (hb (noneTup _) (noneTup _) (fun h => by cases h)) acc]
    exact outerWfB_collectJumpsB lo hi hD hbs _
end

theorem outerWfS_blockAdj {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    (lo hi : Nat) :
    {G : Ctx (OptV V₁) (OptV V₂)} → {D : Ctx (JLabel L₁) (JLabel L₂)} → LblCompat D →
    (id : Nat) → {sig : List (List Ty)} →
    {bs₁ : SBlocks (OptV V₁) (JLabel L₁) rs sig} → {bs₂ : SBlocks (OptV V₂) (JLabel L₂) rs sig} →
    OuterWfS false G D bs₁ bs₂ → blockAdj lo hi id bs₁ = blockAdj lo hi id bs₂
  | _, _, _, _, _, _, _, .nil => rfl
  | _, _, hD, id, _ :: _, _, _, .cons hb hbs => by
    simp only [blockAdj]
    rw [outerWf_collectJumps lo hi hD
      (hb (dummyArgOptTup _) (dummyArgOptTup _) (fun _ hp => hp) (fun h => by cases h)) [],
      outerWfS_blockAdj lo hi hD (id + 1) hbs]

/-! ## `collectJumps`, `reachLoop`, and `filterSBlocks` soundness -/

theorem insertUnique_mem (x y : Nat) (xs : List Nat) :
    y ∈ insertUnique x xs ↔ y = x ∨ y ∈ xs := by
  simp only [insertUnique]; split
  · exact ⟨Or.inr, fun h => h.elim (· ▸ List.contains_iff_mem.1 ‹_›) id⟩
  · simp [List.mem_cons]

theorem insertUnique_nodup (x : Nat) {xs : List Nat} (h : xs.Nodup) :
    (insertUnique x xs).Nodup := by
  simp only [insertUnique]; split
  · exact h
  · rename_i hc; exact List.nodup_cons.2 ⟨fun hm => hc (List.contains_iff_mem.2 hm), h⟩

mutual
theorem mem_collectJumps_iff {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} (lo hi : Nat) :
    (e : Expr (OptV V) (JLabel L) rs) → (acc : List Nat) → (x : Nat) →
    (x ∈ collectJumps lo hi e acc ↔ x ∈ acc ∨ x ∈ collectJumps lo hi e [])
  | .let_ _ k, acc, x => mem_collectJumps_iff lo hi (k (noneTup _)) acc x
  | .load _ _ k, acc, x => mem_collectJumps_iff lo hi (k none) acc x
  | .store _ _ k, acc, x => mem_collectJumps_iff lo hi k acc x
  | .call _ _ k, acc, x => mem_collectJumps_iff lo hi (k (noneTup _)) acc x
  | .jnz _ t e, acc, x => by
    simp only [collectJumps]
    rw [mem_collectJumps_iff lo hi e _ x, mem_collectJumps_iff lo hi t acc x,
      mem_collectJumps_iff lo hi e (collectJumps lo hi t []) x, mem_collectJumps_iff lo hi t [] x]
    simp only [or_assoc]
  | .jump (.loc id) _, acc, x => by
    simp only [collectJumps]; split
    · simp only [insertUnique_mem, List.not_mem_nil, or_false]; exact or_comm
    · simp
  | .jump (.outer _) _, acc, x | .jump .probe _, acc, x
  | .ret _, acc, x | .exit _ _, acc, x | .hlt, acc, x => by simp [collectJumps]
  | .group (sig := sig) bodies k, acc, x => by
    simp only [collectJumps]
    rw [mem_collectJumps_iff lo hi (k (probeLabels sig))
        (collectJumpsB lo hi (bodies (probeLabels sig)) acc) x,
      mem_collectJumpsB_iff lo hi (bodies (probeLabels sig)) acc x,
      mem_collectJumps_iff lo hi (k (probeLabels sig))
        (collectJumpsB lo hi (bodies (probeLabels sig)) []) x,
      mem_collectJumpsB_iff lo hi (bodies (probeLabels sig)) [] x]
    simp only [List.not_mem_nil, false_or, or_assoc]

theorem mem_collectJumpsB_iff {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} (lo hi : Nat) :
    {sig : List (List Ty)} → (bs : Blocks (OptV V) (JLabel L) rs sig) → (acc : List Nat) →
    (x : Nat) → (x ∈ collectJumpsB lo hi bs acc ↔ x ∈ acc ∨ x ∈ collectJumpsB lo hi bs [])
  | _, .nil, acc, x => by simp [collectJumpsB]
  | _, .cons b bs, acc, x => by
    simp only [collectJumpsB]
    rw [mem_collectJumpsB_iff lo hi bs (collectJumps lo hi (b (noneTup _)) acc) x,
      mem_collectJumps_iff lo hi (b (noneTup _)) acc x,
      mem_collectJumpsB_iff lo hi bs (collectJumps lo hi (b (noneTup _)) []) x,
      mem_collectJumps_iff lo hi (b (noneTup _)) [] x]
    simp only [or_assoc]
end

mutual
theorem collectJumps_bounds {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} (lo hi : Nat) :
    (e : Expr (OptV V) (JLabel L) rs) → {acc : List Nat} →
    (∀ x ∈ acc, lo ≤ x ∧ x < hi) → ∀ x ∈ collectJumps lo hi e acc, lo ≤ x ∧ x < hi
  | .let_ _ k, _, h, x, hx => collectJumps_bounds lo hi (k (noneTup _)) h x hx
  | .load _ _ k, _, h, x, hx => collectJumps_bounds lo hi (k none) h x hx
  | .store _ _ k, _, h, x, hx => collectJumps_bounds lo hi k h x hx
  | .call _ _ k, _, h, x, hx => collectJumps_bounds lo hi (k (noneTup _)) h x hx
  | .jnz _ t e, _, h, x, hx => collectJumps_bounds lo hi e (collectJumps_bounds lo hi t h) x hx
  | .jump (.loc id) _, acc, h, x, hx => by
    simp only [collectJumps] at hx; split at hx
    · rename_i hcond
      rcases (insertUnique_mem id x acc).1 hx with rfl | hx
      · simpa [Bool.and_eq_true] using hcond
      · exact h x hx
    · exact h x hx
  | .jump (.outer _) _, _, h, x, hx | .jump .probe _, _, h, x, hx
  | .ret _, _, h, x, hx | .exit _ _, _, h, x, hx | .hlt, _, h, x, hx => h x hx
  | .group (sig := sig) bodies k, _, h, x, hx =>
    collectJumps_bounds lo hi (k (probeLabels sig))
      (collectJumpsB_bounds lo hi (bodies (probeLabels sig)) h) x hx

theorem collectJumpsB_bounds {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} (lo hi : Nat) :
    {sig : List (List Ty)} → (bs : Blocks (OptV V) (JLabel L) rs sig) → {acc : List Nat} →
    (∀ x ∈ acc, lo ≤ x ∧ x < hi) → ∀ x ∈ collectJumpsB lo hi bs acc, lo ≤ x ∧ x < hi
  | _, .nil, _, h, x, hx => h x hx
  | _, .cons b bs, _, h, x, hx =>
    collectJumpsB_bounds lo hi bs (collectJumps_bounds lo hi (b (noneTup _)) h) x hx
end

mutual
theorem collectJumps_nodup {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} (lo hi : Nat) :
    (e : Expr (OptV V) (JLabel L) rs) → {acc : List Nat} →
    acc.Nodup → (collectJumps lo hi e acc).Nodup
  | .let_ _ k, _, h => collectJumps_nodup lo hi (k (noneTup _)) h
  | .load _ _ k, _, h => collectJumps_nodup lo hi (k none) h
  | .store _ _ k, _, h => collectJumps_nodup lo hi k h
  | .call _ _ k, _, h => collectJumps_nodup lo hi (k (noneTup _)) h
  | .jnz _ t e, _, h => collectJumps_nodup lo hi e (collectJumps_nodup lo hi t h)
  | .jump (.loc id) _, _, h => by
    simp only [collectJumps]; split
    · exact insertUnique_nodup id h
    · exact h
  | .jump (.outer _) _, _, h | .jump .probe _, _, h
  | .ret _, _, h | .exit _ _, _, h | .hlt, _, h => h
  | .group (sig := sig) bodies k, _, h =>
    collectJumps_nodup lo hi (k (probeLabels sig))
      (collectJumpsB_nodup lo hi (bodies (probeLabels sig)) h)

theorem collectJumpsB_nodup {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} (lo hi : Nat) :
    {sig : List (List Ty)} → (bs : Blocks (OptV V) (JLabel L) rs sig) → {acc : List Nat} →
    acc.Nodup → (collectJumpsB lo hi bs acc).Nodup
  | _, .nil, _, h => h
  | _, .cons b bs, _, h =>
    collectJumpsB_nodup lo hi bs (collectJumps_nodup lo hi (b (noneTup _)) h)
end

theorem blockAdj_bounds {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} (lo hi : Nat) :
    (id : Nat) → {sig : List (List Ty)} → (bs : SBlocks (OptV V) (JLabel L) rs sig) →
    ∀ p ∈ blockAdj lo hi id bs, ∀ s ∈ p.2, lo ≤ s ∧ s < hi
  | _, _, .nil, _, hp => nomatch hp
  | id, ts :: _, .cons b bs, p, hp => by
    rcases List.mem_cons.1 hp with rfl | hp
    · exact fun s hs =>
        collectJumps_bounds lo hi (b (dummyArgOptTup ts)) (fun _ h => (by cases h)) s hs
    · exact blockAdj_bounds lo hi (id + 1) bs p hp

theorem unionChanged_eq_of_false (acc succs : List Nat)
    (h : (unionChanged acc succs).2 = false) : (unionChanged acc succs).1 = acc := by
  induction succs generalizing acc with
  | nil => rfl
  | cons s ss ih =>
    simp only [unionChanged] at h ⊢
    cases hc : acc.contains s with
    | true => simp only [hc, ↓reduceIte] at h ⊢; exact ih acc h
    | false => simp only [hc, Bool.false_eq_true, ↓reduceIte] at h; cases h

theorem unionChanged_spec (acc succs : List Nat) :
    (∀ x, x ∈ (unionChanged acc succs).1 ↔ x ∈ acc ∨ x ∈ succs) ∧
    (∀ x ∈ acc, x ∈ (unionChanged acc succs).1) ∧
    (acc.Nodup → (unionChanged acc succs).1.Nodup) ∧
    ((unionChanged acc succs).2 = false → ∀ s ∈ succs, s ∈ acc) ∧
    acc.length ≤ (unionChanged acc succs).1.length ∧
    ((unionChanged acc succs).2 = true → acc.length < (unionChanged acc succs).1.length) := by
  induction succs generalizing acc with
  | nil =>
    refine ⟨fun _ => ?_, fun _ h => h, fun h => h, fun _ _ h => ?_, Nat.le_refl _, fun h => ?_⟩
    · simp [unionChanged]
    · cases h
    · simp [unionChanged] at h
  | cons s ss ih =>
    simp only [unionChanged]
    cases hc : acc.contains s with
    | true =>
      simp only [↓reduceIte]
      have hin : s ∈ acc := List.contains_iff_mem.1 hc
      rcases ih acc with ⟨hmem, hsub, hnd, hfalse, hlen, hlt⟩
      refine ⟨fun x => ?_, hsub, hnd, fun hff y hy => ?_, hlen, hlt⟩
      · rw [hmem x, List.mem_cons]
        exact ⟨fun h => h.elim Or.inl (fun hs => Or.inr (Or.inr hs)),
          fun h => h.elim Or.inl (fun hr => hr.elim (fun he => Or.inl (he ▸ hin)) Or.inr)⟩
      · exact (List.mem_cons.1 hy).elim (· ▸ hin) (hfalse hff y)
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hnotin : s ∉ acc := fun hm => by simp at hc; exact hc hm
      rcases ih (s :: acc) with ⟨hmem, _, hnd, _, hlen, _⟩
      refine ⟨fun x => ?_, fun x hx => (hmem x).2 (Or.inl (.tail _ hx)),
        fun h => hnd (List.nodup_cons.2 ⟨hnotin, h⟩), fun h => (by cases h),
        Nat.le_trans (Nat.le_succ _) hlen, fun _ => Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hlen⟩
      rw [hmem x, List.mem_cons, List.mem_cons]
      exact ⟨fun h => h.elim (fun hs => hs.elim (fun he => Or.inr (Or.inl he)) Or.inl)
          (fun hx => Or.inr (Or.inr hx)),
        fun h => h.elim (fun hx => Or.inl (Or.inr hx))
          (fun hr => hr.elim (fun he => Or.inl (Or.inl he)) Or.inr)⟩

theorem reachStep_fold_spec (reach : List Nat) (lo hi : Nat) :
    ∀ (adj : List (Nat × List Nat)), (∀ p ∈ adj, ∀ s ∈ p.2, lo ≤ s ∧ s < hi) →
    ∀ (acc : List Nat) (ch : Bool),
      (∀ x ∈ acc, lo ≤ x ∧ x < hi) → acc.Nodup → (res : List Nat × Bool) →
      res = adj.foldl (fun (a, c) (id, succs) =>
        if reach.contains id then
          let (a', c') := unionChanged a succs
          (a', c || c')
        else (a, c)) (acc, ch) →
      (∀ x ∈ acc, x ∈ res.1) ∧ (∀ x ∈ res.1, lo ≤ x ∧ x < hi) ∧ res.1.Nodup ∧
      acc.length ≤ res.1.length ∧ (ch = true → res.2 = true) ∧
      (res.2 = true → ch = true ∨ acc.length < res.1.length) ∧
      (ch = false → res.2 = false →
        res.1 = acc ∧ ∀ p ∈ adj, p.1 ∈ reach → ∀ s ∈ p.2, s ∈ res.1)
  | [], _, acc, ch, hbd, hnd, res, hres => by
    subst hres
    exact ⟨fun _ h => h, hbd, hnd, Nat.le_refl _, id, Or.inl,
      fun _ _ => ⟨rfl, fun _ h => nomatch h⟩⟩
  | hd :: tl, hadj, acc, ch, hbd, hnd, res, hres => by
    have hhd_bd := hadj hd List.mem_cons_self
    have htl_bd : ∀ p ∈ tl, ∀ s ∈ p.2, lo ≤ s ∧ s < hi := fun p hp => hadj p (.tail _ hp)
    simp only [List.foldl_cons] at hres
    cases hc : reach.contains hd.1 <;> rw [hc] at hres
    · simp only [Bool.false_eq_true, ↓reduceIte] at hres
      rcases reachStep_fold_spec reach lo hi tl htl_bd acc ch hbd hnd res hres with
        ⟨hsub, hbd', hnd', hlen, hmon, htrue, hfalse⟩
      refine ⟨hsub, hbd', hnd', hlen, hmon, htrue, fun hcf hrf => ?_⟩
      rcases hfalse hcf hrf with ⟨heq, hcl⟩
      exact ⟨heq, fun p hp hmem => (List.mem_cons.1 hp).elim
        (fun h => by subst h; simp [hmem] at hc) (fun hp => hcl p hp hmem)⟩
    · simp only [↓reduceIte] at hres
      rcases unionChanged_spec acc hd.2 with ⟨hu_mem, hu_sub, hu_nd, hu_false, hu_le, hu_lt⟩
      have hbd1 : ∀ x ∈ (unionChanged acc hd.2).1, lo ≤ x ∧ x < hi :=
        fun x hx => ((hu_mem x).1 hx).elim (hbd x) (hhd_bd x)
      rcases reachStep_fold_spec reach lo hi tl htl_bd _ (ch || (unionChanged acc hd.2).2)
          hbd1 (hu_nd hnd) res hres with
        ⟨hsub, hbd', hnd', hlen, hmon, htrue, hfalse⟩
      refine ⟨fun x hx => hsub x (hu_sub x hx), hbd', hnd', Nat.le_trans hu_le hlen,
        fun hct => hmon (by simp [hct]), fun hrt => ?_, fun _ hrf => ?_⟩
      · rcases htrue hrt with hor | hlt
        · cases ch
          · simp only [Bool.false_or] at hor; exact Or.inr (Nat.lt_of_lt_of_le (hu_lt hor) hlen)
          · exact Or.inl rfl
        · exact Or.inr (Nat.lt_of_le_of_lt hu_le hlt)
      · have hb : (ch || (unionChanged acc hd.2).2) = false := by
          cases h1 : ch || (unionChanged acc hd.2).2 with
          | false => rfl
          | true => exact absurd (hmon h1) (by rw [hrf]; decide)
        have hch2 : (unionChanged acc hd.2).2 = false := by cases ch <;> simp_all
        rcases hfalse hb hrf with ⟨heq, hcl⟩
        refine ⟨heq.trans (unionChanged_eq_of_false acc hd.2 hch2), fun p hp hmem =>
          (List.mem_cons.1 hp).elim
            (fun h s hs => by subst h; exact hsub s (hu_sub s (hu_false hch2 s hs)))
            (fun hp => hcl p hp hmem)⟩

theorem nodup_range_length_le : ∀ (n lo : Nat) (xs : List Nat),
    xs.Nodup → (∀ x ∈ xs, lo ≤ x ∧ x < lo + n) → xs.length ≤ n
  | 0, _, xs, _, hbd => by
    cases xs with | nil => exact Nat.le_refl 0 | cons x _ => have := hbd x List.mem_cons_self; omega
  | n + 1, lo, xs, hnd, hbd => by
    by_cases hmem : lo + n ∈ xs
    · have hih := nodup_range_length_le n lo (rmNat (lo + n) xs) (rmNat_nodup hnd) fun x hx =>
        have hne := rmNat_ne hnd hx
        have := hbd x (rmNat_mem hx); by omega
      have := rmNat_length hmem; omega
    · exact Nat.le_trans (nodup_range_length_le n lo xs hnd fun x hx =>
        have := hbd x hx; by have hne : x ≠ lo + n := fun e => hmem (e ▸ hx); omega)
        (Nat.le_succ n)

theorem reachLoop_spec (adj : List (Nat × List Nat)) (lo n : Nat)
    (hadj : ∀ p ∈ adj, ∀ s ∈ p.2, lo ≤ s ∧ s < lo + n) :
    ∀ (fuel : Nat) (reach : List Nat),
      (∀ x ∈ reach, lo ≤ x ∧ x < lo + n) → reach.Nodup → n < reach.length + fuel →
      (∀ x ∈ reach, x ∈ reachLoop adj fuel reach) ∧
      (∀ p ∈ adj, p.1 ∈ reachLoop adj fuel reach → ∀ s ∈ p.2, s ∈ reachLoop adj fuel reach)
  | 0, reach, hbd, hnd, hlen => by have := nodup_range_length_le n lo reach hnd hbd; omega
  | fuel + 1, reach, hbd, hnd, hlen => by
    simp only [reachLoop]
    rcases reachStep_fold_spec reach lo (lo + n) adj hadj reach false hbd hnd
      (reachStep adj reach) rfl with ⟨hsub, hbd', hnd', _, _, htrue, hfalse⟩
    cases hch : (reachStep adj reach).2
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rcases hfalse rfl hch with ⟨heq, hcl⟩
      exact ⟨fun _ h => h, fun p hp hmem s hs => heq ▸ hcl p hp hmem s hs⟩
    · simp only [↓reduceIte]
      have hlt' : reach.length < (reachStep adj reach).1.length :=
        (htrue hch).elim (by intro h; cases h) id
      have hih := reachLoop_spec adj lo n hadj fuel _ hbd' hnd' (by omega)
      exact ⟨fun x hx => hih.1 x (hsub x hx), hih.2⟩

def SBlocksClosed {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (reach : List Nat) (lo hi : Nat) :
    Nat → {sig : List (List Ty)} → SBlocks (OptV V) (JLabel L) rs sig → Prop
  | _, _, .nil => True
  | id, ts :: _, .cons b bs =>
    (id ∈ reach → ∀ x ∈ collectJumps lo hi (b (dummyArgOptTup ts)) [], x ∈ reach) ∧
      SBlocksClosed reach lo hi (id + 1) bs

theorem sblocksClosed_of_adj {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (reach : List Nat) (lo hi : Nat) :
    (id : Nat) → {sig : List (List Ty)} → (bs : SBlocks (OptV V) (JLabel L) rs sig) →
    (∀ p ∈ blockAdj lo hi id bs, p.1 ∈ reach → ∀ s ∈ p.2, s ∈ reach) →
    SBlocksClosed reach lo hi id bs
  | _, _, .nil, _ => trivial
  | id, _ :: _, .cons _ bs, h =>
    ⟨h _ List.mem_cons_self,
      sblocksClosed_of_adj reach lo hi (id + 1) bs fun p hp => h p (.tail _ hp)⟩

theorem filterSBlocks_cons_true {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    {keep : Nat → Bool} {ts : List Ty} {sig : List (List Ty)}
    {b : Tup (Arg V) ts → Expr V (JLabel L) rs} {bs : SBlocks V (JLabel L) rs sig} {id : Nat}
    (hk : keep id = true) :
    filterSBlocks keep (ts :: sig) (.cons b bs) id =
      ⟨ts :: (filterSBlocks keep sig bs (id + 1)).sig,
       id :: (filterSBlocks keep sig bs (id + 1)).ids,
       .cons b (filterSBlocks keep sig bs (id + 1)).blocks,
       fun (j, js) => (id, ⟨ts, j⟩) :: (filterSBlocks keep sig bs (id + 1)).mkEnv js⟩ := by
  simp [filterSBlocks, hk]

theorem filterSBlocks_cons_false {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    {keep : Nat → Bool} {ts : List Ty} {sig : List (List Ty)}
    {b : Tup (Arg V) ts → Expr V (JLabel L) rs} {bs : SBlocks V (JLabel L) rs sig} {id : Nat}
    (hk : keep id = false) :
    filterSBlocks keep (ts :: sig) (.cons b bs) id = filterSBlocks keep sig bs (id + 1) := by
  simp [filterSBlocks, hk]

theorem filterSBlocks_ids_spec {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (keep : Nat → Bool) :
    (sig : List (List Ty)) → (bs : SBlocks V (JLabel L) rs sig) → (id : Nat) →
    (∀ x ∈ (filterSBlocks keep sig bs id).ids, id ≤ x ∧ x < id + sig.length ∧ keep x = true) ∧
    ((filterSBlocks keep sig bs id).sig = [] → ∀ x, id ≤ x → x < id + sig.length → keep x = false) ∧
    (∀ jTs jId, (filterSBlocks keep sig bs id).sig = [jTs] →
      (filterSBlocks keep sig bs id).ids = [jId] →
      id ≤ jId ∧ jId < id + sig.length ∧ keep jId = true ∧
      (∀ x, id ≤ x → x < id + sig.length → keep x = true → x = jId))
  | [], .nil, id =>
    ⟨fun _ h => (by cases h), fun _ x h1 h2 => by simp at h2; omega, fun _ _ h _ => (by cases h)⟩
  | ts :: sig, .cons b bs, id => by
    rcases filterSBlocks_ids_spec keep sig bs (id + 1) with ⟨hbd, hnil, hone⟩
    simp only [List.length_cons]
    cases hk : keep id
    · rw [filterSBlocks_cons_false hk]
      refine ⟨fun x hx => ?_,
        fun hn x h1 h2 => (Nat.eq_or_lt_of_le h1).elim (· ▸ hk) (fun h => hnil hn x h (by omega)),
        fun jTs jId hs hi => by
          rcases hone jTs jId hs hi with ⟨h1, h2, h3, h4⟩
          exact ⟨by omega, by omega, h3, fun x hx1 hx2 hkx =>
            (Nat.eq_or_lt_of_le hx1).elim (fun h => by rw [← h, hk] at hkx; cases hkx)
              (fun h => h4 x h (by omega) hkx)⟩⟩
      have hx' := hbd x hx; exact ⟨by omega, by omega, hx'.2.2⟩
    · rw [filterSBlocks_cons_true hk]
      refine ⟨fun x hx => (List.mem_cons.1 hx).elim
          (fun h => by subst h; exact ⟨Nat.le_refl _, by omega, hk⟩)
          (fun hx => by have hx' := hbd x hx; exact ⟨by omega, by omega, hx'.2.2⟩),
        fun h => (by cases h), fun jTs jId hs hi => by
          simp only [List.cons.injEq] at hs hi; rcases hi with ⟨rfl, _⟩
          exact ⟨Nat.le_refl _, by omega, hk, fun x hx1 hx2 hkx =>
            (Nat.eq_or_lt_of_le hx1).elim (·.symm) fun h => by
              have hne := hnil hs.2 x h (by omega); simp [hkx] at hne⟩⟩

theorem filterSBlocks_ids_len {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (keep : Nat → Bool) :
    (sig : List (List Ty)) → (bs : SBlocks V (JLabel L) rs sig) → (id : Nat) →
    (filterSBlocks keep sig bs id).ids.length = (filterSBlocks keep sig bs id).sig.length
  | [], .nil, _ => rfl
  | _ :: sig, .cons _ bs, id => by
    simp only [filterSBlocks]; cases keep id <;> simp [filterSBlocks_ids_len keep sig bs (id + 1)]

private theorem tup_fst_cast {L : List Ty → Type} {ts : List Ty} :
    ∀ {s₁ s₂ : List (List Ty)} (h : ts :: s₁ = ts :: s₂) (xs : Tup L (ts :: s₂)),
      (h ▸ xs).1 = xs.1
  | _, _, rfl, _ => rfl

private theorem sblocks_head_eq {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    {ts₀ ts : List Ty} :
    ∀ {sig₁ : List (List Ty)} (h : ts₀ :: sig₁ = [ts])
      {b₀ : Tup (Arg V) ts₀ → Expr V (JLabel L) rs} {bs₀ : SBlocks V (JLabel L) rs sig₁}
      {b : Tup (Arg V) ts → Expr V (JLabel L) rs} {bs' : SBlocks V (JLabel L) rs []},
      (h ▸ SBlocks.cons b₀ bs₀) = SBlocks.cons b bs' →
      ∃ (heq : ts₀ = ts), (heq ▸ b₀) = b
  | [], rfl, _, _, _, _, h => by cases h; exact ⟨rfl, rfl⟩

theorem filterSBlocks_sig_eq {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    (keep : Nat → Bool) :
    (sig : List (List Ty)) → (bs₁ : SBlocks (OptV V₁) (JLabel L₁) rs sig) →
    (bs₂ : SBlocks (OptV V₂) (JLabel L₂) rs sig) → (id : Nat) →
    (filterSBlocks keep sig bs₁ id).sig = (filterSBlocks keep sig bs₂ id).sig ∧
    (filterSBlocks keep sig bs₁ id).ids = (filterSBlocks keep sig bs₂ id).ids
  | [], .nil, .nil, _ => ⟨rfl, rfl⟩
  | _ :: sig, .cons _ bs₁, .cons _ bs₂, id => by
    rcases filterSBlocks_sig_eq keep sig bs₁ bs₂ (id + 1) with ⟨hsig, hids⟩
    cases hk : keep id
    · rw [filterSBlocks_cons_false hk, filterSBlocks_cons_false hk]; exact ⟨hsig, hids⟩
    · rw [filterSBlocks_cons_true hk, filterSBlocks_cons_true hk]
      exact ⟨by simp [hsig], by simp [hids]⟩

theorem filterSBlocks_outerWfS {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    (keep : Nat → Bool) :
    (sig : List (List Ty)) → (bs₁ : SBlocks (OptV V₁) (JLabel L₁) rs sig) →
    (bs₂ : SBlocks (OptV V₂) (JLabel L₂) rs sig) → (id : Nat) →
    {chk : Bool} → (G : Ctx (OptV V₁) (OptV V₂)) → (D : Ctx (JLabel L₁) (JLabel L₂)) →
    OuterWfS chk G D bs₁ bs₂ →
    ∀ (hsig : (filterSBlocks keep sig bs₁ id).sig = (filterSBlocks keep sig bs₂ id).sig),
      OuterWfS chk G D (filterSBlocks keep sig bs₁ id).blocks
        (hsig ▸ (filterSBlocks keep sig bs₂ id).blocks)
  | [], .nil, .nil, _, _, _, _, _, _ => .nil
  | ts :: sig, .cons _ bs₁, .cons _ bs₂, id, chk, G, D, h, hsig => by
    cases hk : keep id
    · revert hsig; rw [filterSBlocks_cons_false hk, filterSBlocks_cons_false hk]; intro hsig
      cases h with | cons _ hbs =>
        exact filterSBlocks_outerWfS keep sig bs₁ bs₂ (id + 1) G D hbs hsig
    · have ih := filterSBlocks_outerWfS keep sig bs₁ bs₂ (id + 1) (chk := chk) G D
      revert hsig; rw [filterSBlocks_cons_true hk, filterSBlocks_cons_true hk]; intro hsig
      have hcast : ∀ {s₁ s₂ : List (List Ty)} (hs : ts :: s₁ = ts :: s₂)
          {b : Tup (Arg (OptV V₂)) ts → Expr (OptV V₂) (JLabel L₂) rs}
          {x₁ : SBlocks (OptV V₁) (JLabel L₁) rs s₁} {x₂ : SBlocks (OptV V₂) (JLabel L₂) rs s₂}
          {b₁},
          OuterWfS chk G D x₁ ((List.cons.inj hs).2 ▸ x₂) →
          (∀ {G'} a₁ a₂, (∀ p ∈ G, p ∈ G') → (chk = true → TRel (ArgRel G') a₁ a₂) →
            OuterWf chk G' D (b₁ a₁) (b a₂)) →
          OuterWfS chk G D (.cons b₁ x₁) (hs ▸ SBlocks.cons b x₂)
        | _, _, rfl, _, _, _, _, hx, hb => .cons hb hx
      cases h with | cons hb hbs => exact hcast hsig (ih hbs (List.cons.inj hsig).2) hb

theorem filterSBlocks_mkEnv_lt_none {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (keep : Nat → Bool) :
    (sig : List (List Ty)) → (bs : SBlocks V (JLabel L) rs sig) → (id : Nat) →
    (Js : Tup (JLabel L) (filterSBlocks keep sig bs id).sig) →
    ∀ q ts, q < id → lookupLblEnv ((filterSBlocks keep sig bs id).mkEnv Js) q ts = none
  | [], .nil, _, (), _, _, _ => rfl
  | _ :: sig, .cons _ bs, id, Js, q, ts, hq => by
    cases hk : keep id
    · revert Js; rw [filterSBlocks_cons_false hk]; intro Js
      exact filterSBlocks_mkEnv_lt_none keep sig bs (id + 1) Js q ts (by omega)
    · revert Js; rw [filterSBlocks_cons_true hk]; intro Js
      have hne : (q == id) = false := by simp only [beq_eq_false_iff_ne]; omega
      simp only [lookupLblEnv, hne, Bool.false_eq_true, ↓reduceIte]
      exact filterSBlocks_mkEnv_lt_none keep sig bs (id + 1) Js.2 q ts (by omega)

theorem filterSBlocks_mkEnv_lookup {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    (keep : Nat → Bool) :
    (sig : List (List Ty)) → (bs₁ : SBlocks V₁ (JLabel L₁) rs sig) →
    (bs₂ : SBlocks V₂ (JLabel L₂) rs sig) → (id : Nat) →
    ∀ {ts' : List Ty} {q : Nat}, id ≤ q → q < id + sig.length →
    ⟨ts', .loc q, .loc q⟩ ∈ Tup.zip (locLabels (L := L₁) sig id) (locLabels (L := L₂) sig id) →
    keep q = true →
    ∀ (Js₁ : Tup (JLabel L₁) (filterSBlocks keep sig bs₁ id).sig)
      (Js₂ : Tup (JLabel L₂) (filterSBlocks keep sig bs₂ id).sig)
      (heq : (filterSBlocks keep sig bs₁ id).sig = (filterSBlocks keep sig bs₂ id).sig),
      ∃ j₁ j₂,
        lookupLblEnv ((filterSBlocks keep sig bs₁ id).mkEnv Js₁) q ts' = some j₁ ∧
        lookupLblEnv ((filterSBlocks keep sig bs₂ id).mkEnv Js₂) q ts' = some j₂ ∧
        ⟨ts', j₁, j₂⟩ ∈ Tup.zip Js₁ (heq ▸ Js₂)
  | [], .nil, .nil, id, _, _, _, h2, _, _ => by simp at h2; omega
  | ts :: sig, .cons _ bs₁, .cons _ bs₂, id, ts', q, h1, h2, hmem, hkq => by
    intro Js₁ Js₂ heq; simp only [locLabels, Tup.zip] at hmem
    cases hmem with
    | head =>
      revert Js₁ Js₂ heq; rw [filterSBlocks_cons_true hkq, filterSBlocks_cons_true hkq]
      intro Js₁ Js₂ heq
      refine ⟨Js₁.1, Js₂.1, ?_, ?_, ?_⟩
      · simp only [lookupLblEnv, beq_self_eq_true, ↓reduceIte]
        cases listTyDecEq ts ts with | isFalse h => exact absurd rfl h | isTrue _ => rfl
      · simp only [lookupLblEnv, beq_self_eq_true, ↓reduceIte]
        cases listTyDecEq ts ts with | isFalse h => exact absurd rfl h | isTrue _ => rfl
      · rw [← tup_fst_cast heq Js₂]; exact List.mem_cons_self
    | tail _ hmem =>
      have ih := filterSBlocks_mkEnv_lookup keep sig bs₁ bs₂ (id + 1)
        (locLabels_mem_le sig (id + 1) hmem) (by simp at h2; omega) hmem hkq
      cases hk : keep id
      · revert Js₁ Js₂ heq; rw [filterSBlocks_cons_false hk, filterSBlocks_cons_false hk]
        exact ih
      · revert Js₁ Js₂ heq; rw [filterSBlocks_cons_true hk, filterSBlocks_cons_true hk]
        intro Js₁ Js₂ heq
        have hne : (q == id) = false := by
          simp only [beq_eq_false_iff_ne]; intro e; subst e
          exact absurd (locLabels_mem_le sig (q + 1) hmem) (Nat.not_le_of_gt (Nat.lt_succ_self _))
        simp only [lookupLblEnv, hne, Bool.false_eq_true, ↓reduceIte]
        have heq' := (List.cons.inj heq).2
        have tup_cons_mem : ∀ {s₁ s₂ : List (List Ty)} (h : ts :: s₁ = ts :: s₂)
            (p₁ : Tup (JLabel L₁) (ts :: s₁)) (p₂ : Tup (JLabel L₂) (ts :: s₂)) {p},
            p ∈ p₁.2.zip ((List.cons.inj h).2 ▸ p₂.2) → p ∈ Tup.zip p₁ (h ▸ p₂)
          | _, _, rfl, _, _, _, hp => .tail _ hp
        rcases ih Js₁.2 Js₂.2 heq' with ⟨j₁, j₂, hj₁, hj₂, hm⟩
        exact ⟨j₁, j₂, hj₁, hj₂, tup_cons_mem heq Js₁ Js₂ hm⟩

theorem filterSBlocks_single_ts {V : Ty → Type} {L L₁ L₂ : List Ty → Type} {rs : List Ty}
    (keep : Nat → Bool) :
    (sig : List (List Ty)) → (bs : SBlocks V (JLabel L) rs sig) → (id : Nat) →
    {jTs ts' : List Ty} → {jId : Nat} →
    (filterSBlocks keep sig bs id).sig = [jTs] →
    (filterSBlocks keep sig bs id).ids = [jId] →
    ⟨ts', .loc jId, .loc jId⟩ ∈ Tup.zip (locLabels (L := L₁) sig id) (locLabels (L := L₂) sig id) →
    ts' = jTs
  | [], .nil, _, _, _, _, h, _, _ => by cases h
  | ts :: sig, .cons b bs, id, jTs, ts', jId, hs, hi, hmem => by
    simp only [locLabels, Tup.zip] at hmem
    cases hk : keep id
    · rw [filterSBlocks_cons_false hk] at hs hi
      cases hmem with
      | head => have := (filterSBlocks_ids_spec keep sig bs (id + 1)).1 id (by simp [hi]); omega
      | tail _ hmem => exact filterSBlocks_single_ts keep sig bs (id + 1) hs hi hmem
    · rw [filterSBlocks_cons_true hk] at hs hi
      simp only [List.cons.injEq] at hs hi; rcases hi with ⟨rfl, _⟩
      cases hmem with
      | head => exact hs.1
      | tail _ hmem =>
        exact absurd (locLabels_mem_le sig (id + 1) hmem) (Nat.not_le_of_gt (Nat.lt_succ_self _))

theorem filterSBlocks_head_closed {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (reach : List Nat) (lo hi : Nat) :
    (sig : List (List Ty)) → (bs : SBlocks (OptV V) (JLabel L) rs sig) → (id : Nat) →
    SBlocksClosed reach lo hi id bs →
    ∀ {ts} {jId : Nat} {b : Tup (Arg (OptV V)) ts → Expr (OptV V) (JLabel L) rs} {bs'},
    (h : (filterSBlocks (fun x => reach.contains x) sig bs id).sig = [ts]) →
    (filterSBlocks (fun x => reach.contains x) sig bs id).ids = [jId] →
    (h ▸ (filterSBlocks (fun x => reach.contains x) sig bs id).blocks) = .cons b bs' →
    jId ∈ reach ∧ ∀ x ∈ collectJumps lo hi (b (dummyArgOptTup ts)) [], x ∈ reach
  | [], .nil, _, _, _, _, _, _, hs, _, _ => by cases hs
  | ts₀ :: sig, .cons b₀ bs, id, ⟨hb₀, hbs⟩, ts, jId, b, bs', hs, hi', hblk => by
    cases hk : reach.contains id
    · revert hs hi' hblk; rw [filterSBlocks_cons_false hk]; intro hs hi' hblk
      exact filterSBlocks_head_closed reach lo hi sig bs (id + 1) hbs hs hi' hblk
    · revert hs hi' hblk; rw [filterSBlocks_cons_true hk]; intro hs hi' hblk
      simp only [List.cons.injEq] at hi'; rcases hi' with ⟨rfl, _⟩
      rcases sblocks_head_eq hs hblk with ⟨rfl, rfl⟩
      exact ⟨List.contains_iff_mem.1 hk, hb₀ (List.contains_iff_mem.1 hk)⟩

theorem collectJumps_jump_mem {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (lo hi id : Nat) (ts : List Ty) (args : Tup (Arg (OptV V)) ts) (hlo : lo ≤ id) (hhi : id < hi) :
    id ∈ collectJumps (rs := rs) lo hi (.jump (L := JLabel L) (.loc id) args) [] := by
  simp [collectJumps, hlo, hhi, insertUnique_mem]

theorem collectJumps_count_pos {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (lo hi x : Nat) : (e : Expr (OptV V) (JLabel L) rs) →
    x ∈ collectJumps lo hi e [] → countJumps x e ≠ 0
  | .let_ _ k, hx => collectJumps_count_pos lo hi x (k (noneTup _)) hx
  | .load _ _ k, hx => collectJumps_count_pos lo hi x (k none) hx
  | .store _ _ k, hx => collectJumps_count_pos lo hi x k hx
  | .call _ _ k, hx => collectJumps_count_pos lo hi x (k (noneTup _)) hx
  | .jnz _ t e, hx => by
    simp only [collectJumps] at hx
    rcases (mem_collectJumps_iff lo hi e _ x).1 hx with ht | he
    · have := collectJumps_count_pos lo hi x t ht; simp [countJumps]; omega
    · have := collectJumps_count_pos lo hi x e he; simp [countJumps]; omega
  | .jump (.loc id) _, hx => by
    simp only [collectJumps] at hx; split at hx
    · rcases (insertUnique_mem id x []).1 hx with rfl | h
      · simp [countJumps]
      · exact nomatch h
    · exact nomatch hx
  | .jump (.outer _) _, hx | .jump .probe _, hx
  | .ret _, hx | .exit _ _, hx | .hlt, hx => by simp [collectJumps] at hx
  | .group (sig := sig) bodies k, hx => by
    simp only [collectJumps] at hx
    rcases (mem_collectJumps_iff lo hi (k (probeLabels sig)) _ x).1 hx with hb | hk
    · have := collectJumpsB_count_pos (bodies (probeLabels sig)) hb
      simp [countJumps]; omega
    · have := collectJumps_count_pos lo hi x (k (probeLabels sig)) hk
      simp [countJumps]; omega
where
  collectJumpsB_count_pos : {sig : List (List Ty)} → (bs : Blocks (OptV V) (JLabel L) rs sig) →
      x ∈ collectJumpsB lo hi bs [] → countJumpsB x bs ≠ 0
    | _, .nil, hx => by simp [collectJumpsB] at hx
    | _, .cons b bs, hx => by
      simp only [collectJumpsB] at hx
      rcases (mem_collectJumpsB_iff lo hi bs _ x).1 hx with h1 | h2
      · have := collectJumps_count_pos lo hi x (b (noneTup _)) h1; simp [countJumpsB]; omega
      · have := collectJumpsB_count_pos bs h2; simp [countJumpsB]; omega

/-! ## `OuterWf` transformations: `substLabels`, `spliceBlock`, `restrict` -/

def SubstCov {L₁ L₂ : List Ty → Type}
    (env₁ : List (Nat × ((ts : List Ty) × JLabel L₁ ts)))
    (env₂ : List (Nat × ((ts : List Ty) × JLabel L₂ ts)))
    (D D' : Ctx (JLabel L₁) (JLabel L₂)) : Prop :=
  ∀ p ∈ D, match p.2.1, p.2.2 with
    | .loc id₁, .loc id₂ => id₁ = id₂ ∧
      match lookupLblEnv env₁ id₁ p.1, lookupLblEnv env₂ id₂ p.1 with
      | some j₁', some j₂' => ⟨p.1, j₁', j₂'⟩ ∈ D'
      | none, none => ⟨p.1, .loc id₁, .loc id₂⟩ ∈ D'
      | _, _ => False
    | j₁, j₂ => isLocLbl j₁ = false ∧ isLocLbl j₂ = false ∧ p ∈ D'

theorem substCov_append {L₁ L₂ : List Ty → Type}
    {env₁ : List (Nat × ((ts : List Ty) × JLabel L₁ ts))}
    {env₂ : List (Nat × ((ts : List Ty) × JLabel L₂ ts))}
    {D D' : Ctx (JLabel L₁) (JLabel L₂)} (hcov : SubstCov env₁ env₂ D D')
    {sig : List (List Ty)} {Js₁ : Tup (JLabel L₁) sig} {Js₂ : Tup (JLabel L₂) sig}
    (hno : ∀ p ∈ Tup.zip Js₁ Js₂, isLocLbl p.2.1 = false ∧ isLocLbl p.2.2 = false) :
    SubstCov env₁ env₂ (Tup.zip Js₁ Js₂ ++ D) (Tup.zip Js₁ Js₂ ++ D') := fun p hp => by
  rcases List.mem_append.1 hp with hp | hp
  · have h := hno p hp
    cases h1 : p.2.1 <;> cases h2 : p.2.2 <;> simp_all [isLocLbl]
    all_goals exact List.mem_append_left _ hp
  · have h := hcov p hp
    cases h1 : p.2.1 <;> cases h2 : p.2.2 <;> simp_all
    rcases h with ⟨heq_id, hm⟩; cases heq_id
    cases h1l : lookupLblEnv env₁ _ p.1 <;> cases h2l : lookupLblEnv env₂ _ p.1 <;>
      rw [h1l, h2l] at hm <;> dsimp only at hm ⊢ <;>
      first | exact False.elim hm | exact Or.inr hm

mutual
theorem outerWf_substLabels {chk : Bool} {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    (env₁ : List (Nat × ((ts : List Ty) × JLabel L₁ ts)))
    (env₂ : List (Nat × ((ts : List Ty) × JLabel L₂ ts))) :
    {G : Ctx (OptV V₁) (OptV V₂)} → {D D' : Ctx (JLabel L₁) (JLabel L₂)} →
    SubstCov env₁ env₂ D D' →
    {e₁ : Expr (OptV V₁) (JLabel L₁) rs} → {e₂ : Expr (OptV V₂) (JLabel L₂) rs} →
    OuterWf chk G D e₁ e₂ → OuterWf chk G D' (substLabels env₁ e₁) (substLabels env₂ e₂)
  | _, _, _, hcov, _, _, .let_ hop hk =>
    .let_ hop fun xs₁ xs₂ hx => outerWf_substLabels env₁ env₂ hcov (hk xs₁ xs₂ hx)
  | _, _, _, hcov, _, _, .load t ha hk =>
    .load t ha fun v₁ v₂ hv => outerWf_substLabels env₁ env₂ hcov (hk v₁ v₂ hv)
  | _, _, _, hcov, _, _, .store hv ha hk =>
    .store hv ha (outerWf_substLabels env₁ env₂ hcov hk)
  | _, _, _, hcov, _, _, .call f hargs hk =>
    .call f hargs fun xs₁ xs₂ hx => outerWf_substLabels env₁ env₂ hcov (hk xs₁ xs₂ hx)
  | _, _, _, hcov, _, _, .jnz hc ht he =>
    .jnz hc (outerWf_substLabels env₁ env₂ hcov ht) (outerWf_substLabels env₁ env₂ hcov he)
  | _, _, _, hcov, _, _, .jump (ts := ts) (j₁ := j₁) (j₂ := j₂) hj hargs => by
    have h := hcov _ hj
    cases j₁ <;> cases j₂ <;> simp only [substLabels, isLocLbl] at h ⊢
    all_goals first
      | exact .jump h.2.2 hargs
      | (have hf : true = false := h.1; cases hf)
      | (have hf : true = false := h.2.1; cases hf)
      | (rcases h with ⟨rfl, hm⟩
         cases h1 : lookupLblEnv env₁ _ ts <;> cases h2 : lookupLblEnv env₂ _ ts <;>
           rw [h1, h2] at hm
         · exact .jump hm hargs
         · exact False.elim hm
         · exact False.elim hm
         · exact .jump hm hargs)
  | _, _, _, _, _, _, .ret hvs => .ret hvs
  | _, _, _, _, _, _, .exit f hargs => .exit f hargs
  | _, _, _, _, _, _, .hlt => .hlt
  | _, _, _, hcov, _, _, .group hb hk =>
    .group
      (fun Js₁ Js₂ hno =>
        outerWfB_substLabels env₁ env₂ (substCov_append hcov hno) (hb Js₁ Js₂ hno))
      (fun Js₁ Js₂ hno =>
        outerWf_substLabels env₁ env₂ (substCov_append hcov hno) (hk Js₁ Js₂ hno))

theorem outerWfB_substLabels {chk : Bool} {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type}
    {rs : List Ty}
    (env₁ : List (Nat × ((ts : List Ty) × JLabel L₁ ts)))
    (env₂ : List (Nat × ((ts : List Ty) × JLabel L₂ ts))) :
    {G : Ctx (OptV V₁) (OptV V₂)} → {D D' : Ctx (JLabel L₁) (JLabel L₂)} →
    SubstCov env₁ env₂ D D' → {sig : List (List Ty)} →
    {bs₁ : Blocks (OptV V₁) (JLabel L₁) rs sig} → {bs₂ : Blocks (OptV V₂) (JLabel L₂) rs sig} →
    OuterWfB chk G D bs₁ bs₂ → OuterWfB chk G D' (substLabelsB env₁ bs₁) (substLabelsB env₂ bs₂)
  | _, _, _, _, _, _, _, .nil => .nil
  | _, _, _, hcov, _, _, _, .cons hb hbs =>
    .cons (fun xs₁ xs₂ hx => outerWf_substLabels env₁ env₂ hcov (hb xs₁ xs₂ hx))
      (outerWfB_substLabels env₁ env₂ hcov hbs)
end

def SpliceCov {L₁ L₂ : List Ty → Type} (targetId : Nat) (targetTs : List Ty)
    (D D' : Ctx (JLabel L₁) (JLabel L₂)) : Prop :=
  ∀ p ∈ D, match p.2.1, p.2.2 with
    | .loc id₁, .loc id₂ => id₁ = id₂ ∧
      if id₁ == targetId then p.1 = targetTs else ⟨p.1, .loc id₁, .loc id₂⟩ ∈ D'
    | j₁, j₂ => isLocLbl j₁ = false ∧ isLocLbl j₂ = false ∧ p ∈ D'

theorem spliceCov_append {L₁ L₂ : List Ty → Type} {targetId : Nat} {targetTs : List Ty}
    {D D' : Ctx (JLabel L₁) (JLabel L₂)} (hcov : SpliceCov targetId targetTs D D')
    {sig : List (List Ty)} {Js₁ : Tup (JLabel L₁) sig} {Js₂ : Tup (JLabel L₂) sig}
    (hno : ∀ p ∈ Tup.zip Js₁ Js₂, isLocLbl p.2.1 = false ∧ isLocLbl p.2.2 = false) :
    SpliceCov targetId targetTs (Tup.zip Js₁ Js₂ ++ D) (Tup.zip Js₁ Js₂ ++ D') := fun p hp => by
  rcases List.mem_append.1 hp with hp | hp
  · have h := hno p hp
    cases h1 : p.2.1 <;> cases h2 : p.2.2 <;> simp_all [isLocLbl]
    all_goals exact List.mem_append_left _ hp
  · have h := hcov p hp
    cases h1 : p.2.1 <;> cases h2 : p.2.2 <;> simp_all
    rcases h with ⟨rfl, hm⟩; split <;> simp_all

mutual
theorem outerWf_spliceBlock {chk : Bool} {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    (targetId : Nat) (targetTs : List Ty)
    (b₁ : Tup (Arg (OptV V₁)) targetTs → Expr (OptV V₁) (JLabel L₁) rs)
    (b₂ : Tup (Arg (OptV V₂)) targetTs → Expr (OptV V₂) (JLabel L₂) rs)
    {G₀ : Ctx (OptV V₁) (OptV V₂)} {D' : Ctx (JLabel L₁) (JLabel L₂)}
    (hb : ∀ {G'} a₁ a₂, (∀ p ∈ G₀, p ∈ G') → (chk = true → TRel (ArgRel G') a₁ a₂) →
      OuterWf chk G' D' (b₁ a₁) (b₂ a₂)) :
    {G : Ctx (OptV V₁) (OptV V₂)} → (∀ p ∈ G₀, p ∈ G) →
    {D : Ctx (JLabel L₁) (JLabel L₂)} → SpliceCov targetId targetTs D D' →
    {e₁ : Expr (OptV V₁) (JLabel L₁) rs} → {e₂ : Expr (OptV V₂) (JLabel L₂) rs} →
    OuterWf chk G D e₁ e₂ → OuterWf chk G D' (spliceBlock targetId targetTs b₁ e₁)
                                          (spliceBlock targetId targetTs b₂ e₂)
  | _, hsub, _, hcov, _, _, .let_ hop hk =>
    .let_ hop fun xs₁ xs₂ hx =>
      outerWf_spliceBlock targetId targetTs b₁ b₂ hb
        (fun _ hp => List.mem_append_right _ (hsub _ hp)) hcov (hk xs₁ xs₂ hx)
  | _, hsub, _, hcov, _, _, .load t ha hk =>
    .load t ha fun v₁ v₂ hv =>
      outerWf_spliceBlock targetId targetTs b₁ b₂ hb
        (fun _ hp => List.mem_cons_of_mem _ (hsub _ hp)) hcov (hk v₁ v₂ hv)
  | _, hsub, _, hcov, _, _, .store hv ha hk =>
    .store hv ha (outerWf_spliceBlock targetId targetTs b₁ b₂ hb hsub hcov hk)
  | _, hsub, _, hcov, _, _, .call f hargs hk =>
    .call f hargs fun xs₁ xs₂ hx =>
      outerWf_spliceBlock targetId targetTs b₁ b₂ hb
        (fun _ hp => List.mem_append_right _ (hsub _ hp)) hcov (hk xs₁ xs₂ hx)
  | _, hsub, _, hcov, _, _, .jnz hc ht he =>
    .jnz hc (outerWf_spliceBlock targetId targetTs b₁ b₂ hb hsub hcov ht)
      (outerWf_spliceBlock targetId targetTs b₁ b₂ hb hsub hcov he)
  | _, hsub, _, hcov, _, _, .jump (ts := ts) (j₁ := j₁) (j₂ := j₂) hj hargs => by
    have h := hcov _ hj
    cases j₁ <;> cases j₂ <;> simp only [spliceBlock, isLocLbl] at h ⊢
    all_goals first
      | exact .jump h.2.2 hargs
      | (have hf : true = false := h.1; cases hf)
      | (have hf : true = false := h.2.1; cases hf)
      | (rcases h with ⟨rfl, hm⟩
         cases heq : (_ == targetId) <;> rw [heq] at hm
         · simp only [Bool.false_eq_true, ↓reduceIte] at hm ⊢; exact .jump hm hargs
         · simp only [↓reduceIte] at hm ⊢; subst hm
           cases listTyDecEq ts ts with
           | isFalse hne => exact absurd rfl hne
           | isTrue _ => exact hb _ _ hsub hargs)
  | _, _, _, _, _, _, .ret hvs => .ret hvs
  | _, _, _, _, _, _, .exit f hargs => .exit f hargs
  | _, _, _, _, _, _, .hlt => .hlt
  | _, hsub, _, hcov, _, _, .group hbb hkb =>
    .group
      (fun Js₁ Js₂ hno =>
        outerWfB_spliceBlock targetId targetTs b₁ b₂
          (fun a₁ a₂ hG ha => (hb a₁ a₂ hG ha).weaken_D (fun _ hp => List.mem_append_right _ hp))
          hsub (spliceCov_append hcov hno) (hbb Js₁ Js₂ hno))
      (fun Js₁ Js₂ hno =>
        outerWf_spliceBlock targetId targetTs b₁ b₂
          (fun a₁ a₂ hG ha => (hb a₁ a₂ hG ha).weaken_D (fun _ hp => List.mem_append_right _ hp))
          hsub (spliceCov_append hcov hno) (hkb Js₁ Js₂ hno))

theorem outerWfB_spliceBlock {chk : Bool} {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type}
    {rs : List Ty} (targetId : Nat) (targetTs : List Ty)
    (b₁ : Tup (Arg (OptV V₁)) targetTs → Expr (OptV V₁) (JLabel L₁) rs)
    (b₂ : Tup (Arg (OptV V₂)) targetTs → Expr (OptV V₂) (JLabel L₂) rs)
    {G₀ : Ctx (OptV V₁) (OptV V₂)} {D' : Ctx (JLabel L₁) (JLabel L₂)}
    (hb : ∀ {G'} a₁ a₂, (∀ p ∈ G₀, p ∈ G') → (chk = true → TRel (ArgRel G') a₁ a₂) →
      OuterWf chk G' D' (b₁ a₁) (b₂ a₂)) :
    {G : Ctx (OptV V₁) (OptV V₂)} → (∀ p ∈ G₀, p ∈ G) →
    {D : Ctx (JLabel L₁) (JLabel L₂)} → SpliceCov targetId targetTs D D' → {sig : List (List Ty)} →
    {bs₁ : Blocks (OptV V₁) (JLabel L₁) rs sig} → {bs₂ : Blocks (OptV V₂) (JLabel L₂) rs sig} →
    OuterWfB chk G D bs₁ bs₂ → OuterWfB chk G D' (spliceBlockB targetId targetTs b₁ bs₁)
                                              (spliceBlockB targetId targetTs b₂ bs₂)
  | _, _, _, _, _, _, _, .nil => .nil
  | _, hsub, _, hcov, _, _, _, .cons hbh hbs =>
    .cons (fun xs₁ xs₂ hx =>
        outerWf_spliceBlock targetId targetTs b₁ b₂ hb
          (fun _ hp => List.mem_append_right _ (hsub _ hp)) hcov (hbh xs₁ xs₂ hx))
      (outerWfB_spliceBlock targetId targetTs b₁ b₂ hb hsub hcov hbs)
end

private theorem collect_let_eq {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs ts : List Ty}
    (lo hi : Nat) {D : Ctx (JLabel L₁) (JLabel L₂)} (hD : LblCompat D)
    {G₀ : Ctx (OptV V₁) (OptV V₂)}
    {k₁ : Tup (OptV V₁) ts → Expr (OptV V₁) (JLabel L₁) rs}
    {k₂ : Tup (OptV V₂) ts → Expr (OptV V₂) (JLabel L₂) rs}
    (hk : ∀ xs₁ xs₂, (false = true → ∃ y₁ y₂, xs₁ = someTup ts y₁ ∧ xs₂ = someTup ts y₂) →
      OuterWf false (Tup.zip xs₁ xs₂ ++ G₀) D (k₁ xs₁) (k₂ xs₂))
    (xs₁ : Tup (OptV V₁) ts) :
    collectJumps lo hi (k₁ xs₁) [] = collectJumps lo hi (k₁ (noneTup ts)) [] :=
  (outerWf_collectJumps lo hi hD (hk xs₁ (noneTup _) (fun h => by cases h)) []).trans
    (outerWf_collectJumps lo hi hD (hk (noneTup _) (noneTup _) (fun h => by cases h)) []).symm

private theorem collect_load_eq {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty} {t : Ty}
    (lo hi : Nat) {D : Ctx (JLabel L₁) (JLabel L₂)} (hD : LblCompat D)
    {G₀ : Ctx (OptV V₁) (OptV V₂)}
    {k₁ : OptV V₁ t → Expr (OptV V₁) (JLabel L₁) rs}
    {k₂ : OptV V₂ t → Expr (OptV V₂) (JLabel L₂) rs}
    (hk : ∀ v₁ v₂, (false = true → ∃ u₁ u₂, v₁ = some u₁ ∧ v₂ = some u₂) →
      OuterWf false (⟨t, v₁, v₂⟩ :: G₀) D (k₁ v₁) (k₂ v₂))
    (v₁ : OptV V₁ t) :
    collectJumps lo hi (k₁ v₁) [] = collectJumps lo hi (k₁ none) [] :=
  (outerWf_collectJumps lo hi hD (hk v₁ none (fun h => by cases h)) []).trans
    (outerWf_collectJumps lo hi hD (hk none none (fun h => by cases h)) []).symm

def RestSub (lo hi : Nat) {L₁ L₂ : List Ty → Type} (D D' : Ctx (JLabel L₁) (JLabel L₂)) : Prop :=
  ∀ p ∈ D, match p.2.1, p.2.2 with
    | .loc d₁, .loc d₂ => d₁ = d₂ ∧ ((lo ≤ d₁ ∧ d₁ < hi) ∨ p ∈ D')
    | j₁, j₂ => isLocLbl j₁ = false ∧ isLocLbl j₂ = false ∧ p ∈ D'

theorem restSub_append (lo hi : Nat) {L₁ L₂ : List Ty → Type}
    {D D' : Ctx (JLabel L₁) (JLabel L₂)} (hsub : RestSub lo hi D D')
    {sig : List (List Ty)} {Js₁ : Tup (JLabel L₁) sig} {Js₂ : Tup (JLabel L₂) sig}
    (hno : ∀ p ∈ Tup.zip Js₁ Js₂, isLocLbl p.2.1 = false ∧ isLocLbl p.2.2 = false) :
    RestSub lo hi (Tup.zip Js₁ Js₂ ++ D) (Tup.zip Js₁ Js₂ ++ D') := fun p hp => by
  rcases List.mem_append.1 hp with hp | hp
  · have h := hno p hp
    cases h1 : p.2.1 <;> cases h2 : p.2.2 <;> simp_all [isLocLbl]
    all_goals exact List.mem_append_left _ hp
  · have h := hsub p hp
    cases h1 : p.2.1 <;> cases h2 : p.2.2 <;> simp_all
    rcases h with ⟨rfl, hm⟩; exact hm.elim Or.inl (fun hp' => Or.inr (Or.inr hp'))

mutual
theorem outerWf_restrict_of_collect {chk : Bool} {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type}
    {rs : List Ty} (lo hi : Nat) :
    {G G₀ : Ctx (OptV V₁) (OptV V₂)} → {D D' : Ctx (JLabel L₁) (JLabel L₂)} → LblCompat D →
    RestSub lo hi D D' →
    {e₁ : Expr (OptV V₁) (JLabel L₁) rs} → {e₂ : Expr (OptV V₂) (JLabel L₂) rs} →
    OuterWf false G₀ D e₁ e₂ → OuterWf chk G D e₁ e₂ →
    (∀ x ∈ collectJumps lo hi e₁ [], ∀ {ts}, ⟨ts, JLabel.loc x, JLabel.loc x⟩ ∈ D →
      ⟨ts, JLabel.loc x, JLabel.loc x⟩ ∈ D') →
    OuterWf chk G D' e₁ e₂
  | _, _, _, _, hD, hsub, _, _, .let_ _ hk0, .let_ hop hk, hcov =>
    .let_ hop fun xs₁ xs₂ hx =>
      outerWf_restrict_of_collect lo hi hD hsub (hk0 xs₁ xs₂ (fun h => by cases h)) (hk xs₁ xs₂ hx)
        fun x hx' => hcov x (collect_let_eq lo hi hD hk0 xs₁ ▸ hx')
  | _, _, _, _, hD, hsub, _, _, .load t _ hk0, .load _ ha hk, hcov =>
    .load t ha fun v₁ v₂ hv =>
      outerWf_restrict_of_collect lo hi hD hsub (hk0 v₁ v₂ (fun h => by cases h)) (hk v₁ v₂ hv)
        fun x hx' => hcov x (collect_load_eq lo hi hD hk0 v₁ ▸ hx')
  | _, _, _, _, hD, hsub, _, _, .store _ _ hk0, .store hv ha hk, hcov =>
    .store hv ha (outerWf_restrict_of_collect lo hi hD hsub hk0 hk hcov)
  | _, _, _, _, hD, hsub, _, _, .call _ _ hk0, .call f hargs hk, hcov =>
    .call f hargs fun xs₁ xs₂ hx =>
      outerWf_restrict_of_collect lo hi hD hsub (hk0 xs₁ xs₂ (fun h => by cases h)) (hk xs₁ xs₂ hx)
        fun x hx' => hcov x (collect_let_eq lo hi hD hk0 xs₁ ▸ hx')
  | _, _, _, _, hD, hsub, _, _, .jnz (t₁ := t₁) (e₁ := e₁') _ ht0 he0, .jnz hc ht he, hcov =>
    .jnz hc
      (outerWf_restrict_of_collect lo hi hD hsub ht0 ht fun x hx =>
        hcov x ((mem_collectJumps_iff lo hi e₁' _ x).2 (Or.inl hx)))
      (outerWf_restrict_of_collect lo hi hD hsub he0 he fun x hx =>
        hcov x ((mem_collectJumps_iff lo hi e₁' _ x).2 (Or.inr hx)))
  | _, _, _, _, _, hsub, _, _, .jump _ _, .jump (ts := ts) (j₁ := j₁) (j₂ := j₂) hj hargs,
      hcov => by
    have hs := hsub _ hj
    cases j₁ <;> cases j₂ <;> simp only [isLocLbl] at hs
    all_goals first
      | exact .jump hs.2.2 hargs
      | (have hf : true = false := hs.1; cases hf)
      | (have hf : true = false := hs.2.1; cases hf)
      | (rcases hs with ⟨rfl, hlo | hin⟩
         · exact .jump (hcov _ (collectJumps_jump_mem lo hi _ ts _ hlo.1 hlo.2) hj) hargs
         · exact .jump hin hargs)
  | _, _, _, _, _, _, _, _, .ret _, .ret hvs, _ => .ret hvs
  | _, _, _, _, _, _, _, _, .exit _ _, .exit f hargs, _ => .exit f hargs
  | _, _, _, _, _, _, _, _, .hlt, .hlt, _ => .hlt
  | _, _, _, _, hD, hsub, _, _, .group (sig := sig) (b₁ := b₁) (k₁ := k₁) hb0 hk0,
      .group hb hk, hcov => by
    refine .group (fun Js₁ Js₂ hno => ?_) (fun Js₁ Js₂ hno => ?_)
    · refine outerWfB_restrict_of_collect lo hi (hD.append_noLoc hno)
        (restSub_append lo hi hsub hno) (hb0 Js₁ Js₂ hno) (hb Js₁ Js₂ hno)
        fun x hx {ts'} hmem => ?_
      have heq : collectJumpsB lo hi (b₁ Js₁) [] = collectJumpsB lo hi (b₁ (probeLabels sig)) [] :=
        (outerWfB_collectJumpsB lo hi (hD.append_noLoc (isLocLbl_zip_probe Js₁ Js₂ hno))
          (hb0 Js₁ (probeLabels sig) (isLocLbl_zip_probe Js₁ Js₂ hno)) []).trans
        (outerWfB_collectJumpsB lo hi (hD.append_probe sig)
          (hb0 (probeLabels sig) (probeLabels sig) (isLocLbl_probe sig)) []).symm
      rw [heq] at hx
      rcases List.mem_append.1 hmem with hmem | hmem
      · exact False.elim (by have := (hno _ hmem).1; simp [isLocLbl] at this)
      · exact List.mem_append_right _
          (hcov x ((mem_collectJumps_iff lo hi (k₁ (probeLabels sig)) _ x).2 (Or.inl hx)) hmem)
    · refine outerWf_restrict_of_collect lo hi (hD.append_noLoc hno) (restSub_append lo hi hsub hno)
        (hk0 Js₁ Js₂ hno) (hk Js₁ Js₂ hno) fun x hx {ts'} hmem => ?_
      have heq : collectJumps lo hi (k₁ Js₁) [] = collectJumps lo hi (k₁ (probeLabels sig)) [] :=
        (outerWf_collectJumps lo hi (hD.append_noLoc (isLocLbl_zip_probe Js₁ Js₂ hno))
          (hk0 Js₁ (probeLabels sig) (isLocLbl_zip_probe Js₁ Js₂ hno)) []).trans
        (outerWf_collectJumps lo hi (hD.append_probe sig)
          (hk0 (probeLabels sig) (probeLabels sig) (isLocLbl_probe sig)) []).symm
      rw [heq] at hx
      rcases List.mem_append.1 hmem with hmem | hmem
      · exact False.elim (by have := (hno _ hmem).1; simp [isLocLbl] at this)
      · exact List.mem_append_right _
          (hcov x ((mem_collectJumps_iff lo hi (k₁ (probeLabels sig)) _ x).2 (Or.inr hx)) hmem)

theorem outerWfB_restrict_of_collect {chk : Bool} {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type}
    {rs : List Ty} (lo hi : Nat) :
    {G G₀ : Ctx (OptV V₁) (OptV V₂)} → {D D' : Ctx (JLabel L₁) (JLabel L₂)} → LblCompat D →
    RestSub lo hi D D' → {sig : List (List Ty)} →
    {bs₁ : Blocks (OptV V₁) (JLabel L₁) rs sig} → {bs₂ : Blocks (OptV V₂) (JLabel L₂) rs sig} →
    OuterWfB false G₀ D bs₁ bs₂ → OuterWfB chk G D bs₁ bs₂ →
    (∀ x ∈ collectJumpsB lo hi bs₁ [], ∀ {ts}, ⟨ts, JLabel.loc x, JLabel.loc x⟩ ∈ D →
      ⟨ts, JLabel.loc x, JLabel.loc x⟩ ∈ D') →
    OuterWfB chk G D' bs₁ bs₂
  | _, _, _, _, _, _, _, _, _, .nil, .nil, _ => .nil
  | _, _, _, _, hD, hsub, _, _, _, .cons (b₁ := b₁) hb0 hbs0, .cons hb hbs, hcov =>
    .cons (fun xs₁ xs₂ hx =>
      outerWf_restrict_of_collect lo hi hD hsub (hb0 xs₁ xs₂ (fun h => by cases h)) (hb xs₁ xs₂ hx)
        fun x hx' {ts'} hmem =>
          have h1 : x ∈ collectJumps lo hi (b₁ (noneTup _)) [] :=
            collect_let_eq lo hi hD hb0 xs₁ ▸ hx'
          hcov x ((mem_collectJumpsB_iff lo hi _ (collectJumps lo hi (b₁ (noneTup _)) []) x).2
            (Or.inl h1)) hmem)
      (outerWfB_restrict_of_collect lo hi hD hsub hbs0 hbs fun x hx' {ts'} hmem =>
        hcov x ((mem_collectJumpsB_iff lo hi _ (collectJumps lo hi (b₁ (noneTup _)) []) x).2
          (Or.inr hx')) hmem)
end

theorem filterSBlocks_kept_closed {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (reach : List Nat) (lo hi : Nat) :
    (sig : List (List Ty)) → (bs : SBlocks (OptV V) (JLabel L) rs sig) → (id : Nat) →
    SBlocksClosed reach lo hi id bs →
    ∀ {ts} (i : Member ts (filterSBlocks (fun x => reach.contains x) sig bs id).sig),
    ∀ x ∈ collectJumps lo hi
      ((sblocksToBlocks (filterSBlocks (fun x => reach.contains x) sig bs id).blocks).get i
        (noneTup ts)) [], x ∈ reach
  | [], .nil, _, _, _, i => nomatch i
  | ts₀ :: sig, .cons b₀ bs, id, ⟨hb₀, hbs⟩, ts, i => by
    cases hk : reach.contains id
    · revert i; rw [filterSBlocks_cons_false hk]; intro i
      exact filterSBlocks_kept_closed reach lo hi sig bs (id + 1) hbs i
    · revert i; rw [filterSBlocks_cons_true hk]; intro i
      cases i with
      | here =>
        intro x hx
        have heq : collectJumps lo hi (b₀ (toArgTup (noneTup ts₀))) [] =
            collectJumps lo hi (b₀ (dummyArgOptTup ts₀)) [] := rfl
        exact hb₀ (List.contains_iff_mem.1 hk) x (heq ▸ hx)
      | there i => exact filterSBlocks_kept_closed reach lo hi sig bs (id + 1) hbs i

theorem collectJumpsB_mem_exists {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (lo hi x : Nat) : {sig : List (List Ty)} → (bs : Blocks (OptV V) (JLabel L) rs sig) →
    x ∈ collectJumpsB lo hi bs [] →
    ∃ ts, ∃ i : Member ts sig, x ∈ collectJumps lo hi (bs.get i (noneTup ts)) []
  | _, .nil, hx => by simp [collectJumpsB] at hx
  | _, .cons b bs, hx => by
    simp only [collectJumpsB] at hx
    rcases (mem_collectJumpsB_iff lo hi bs (collectJumps lo hi (b (noneTup _)) []) x).1 hx
      with h1 | h2
    · exact ⟨_, .here, h1⟩
    · rcases collectJumpsB_mem_exists lo hi x bs h2 with ⟨ts, i, hi⟩; exact ⟨ts, .there i, hi⟩

theorem mem_locLabels_zip {L₁ L₂ : List Ty → Type} :
    ∀ (sig : List (List Ty)) (d : Nat) {p},
      p ∈ Tup.zip (locLabels (L := L₁) sig d) (locLabels (L := L₂) sig d) →
      ∃ id, p.2.1 = .loc id ∧ p.2.2 = .loc id ∧ d ≤ id ∧ id < d + sig.length
  | _ :: _, d, _, .head _ => ⟨d, rfl, rfl, Nat.le_refl _, by simp⟩
  | _ :: sig, d, _, .tail _ h => by
    rcases mem_locLabels_zip sig (d + 1) h with ⟨i, h1, h2, hle, hhi⟩
    exact ⟨i, h1, h2, by omega, by simp; omega⟩

theorem locLabels_zip_ge {L : List Ty → Type} {K : List Ty → Type} :
    ∀ (s : List (List Ty)) (d : Nat) (js : Tup K s) {ts} {id : Nat} {j₂ : K ts},
      ⟨ts, .loc id, j₂⟩ ∈ Tup.zip (locLabels (L := L) s d) js → d ≤ id
  | [], _, (), _, _, _, h => nomatch h
  | _ :: _, _, (_, _), _, _, _, .head _ => Nat.le_refl _
  | _ :: s, d, (_, js), _, _, _, .tail _ h =>
    Nat.le_trans (Nat.le_succ _) (locLabels_zip_ge s (d + 1) js h)

theorem restSub_loc_drop {L₁ L₂ : List Ty → Type} (sig : List (List Ty)) (depth : Nat)
    {D D' : Ctx (JLabel L₁) (JLabel L₂)}
    (hD : BoundedD depth D) (hsub : ∀ p ∈ D, p ∈ D') :
    RestSub depth (depth + sig.length)
      (Tup.zip (locLabels sig depth) (locLabels sig depth) ++ D) D' := fun p hp => by
  rcases List.mem_append.1 hp with hp | hp
  · rcases mem_locLabels_zip sig depth hp with ⟨id, h1, h2, hle, hhi⟩
    rcases p with ⟨ts', j₁, j₂⟩; simp only at h1 h2; subst h1 h2; exact ⟨rfl, Or.inl ⟨hle, hhi⟩⟩
  · have h := hD p hp
    rcases p with ⟨ts', j₁, j₂⟩; cases j₁ <;> cases j₂ <;> simp only [isLocLbl] at h ⊢
    · exact ⟨trivial, trivial, hsub _ hp⟩
    · cases h.2
    · exact ⟨trivial, trivial, hsub _ hp⟩
    · cases h.1
    · exact ⟨h.1, Or.inr (hsub _ hp)⟩
    · cases h.1
    · exact ⟨trivial, trivial, hsub _ hp⟩
    · cases h.2
    · exact ⟨trivial, trivial, hsub _ hp⟩

theorem outerWfS_cast {chk : Bool} {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type}
    {rs : List Ty} {G : Ctx (OptV V₁) (OptV V₂)} {D : Ctx (JLabel L₁) (JLabel L₂)}
    {sig₁' ids₁' bs₁'' mkEnv₁} {sig₂' ids₂' bs₂'' mkEnv₂}
    (heq : sig₁' = sig₂') :
    ∀ (r₁ : FilterRes (OptV V₁) L₁ rs) (r₂ : FilterRes (OptV V₂) L₂ rs)
      (hs : r₁.sig = r₂.sig),
      r₁ = ⟨sig₁', ids₁', bs₁'', mkEnv₁⟩ → r₂ = ⟨sig₂', ids₂', bs₂'', mkEnv₂⟩ →
      OuterWfS chk G D r₁.blocks (hs ▸ r₂.blocks) →
      OuterWfS chk G D bs₁'' (heq ▸ bs₂'')
  | _, _, _, rfl, rfl, h => h

theorem filterSBlocks_mkEnv_lookup_eq {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    (keep : Nat → Bool) (sig : List (List Ty))
    (bs₁ : SBlocks (OptV V₁) (JLabel L₁) rs sig)
    (bs₂ : SBlocks (OptV V₂) (JLabel L₂) rs sig) (id : Nat)
    {ts' : List Ty} {q : Nat} (hq₁ : id ≤ q) (hq₂ : q < id + sig.length)
    (hm : ⟨ts', .loc q, .loc q⟩ ∈ Tup.zip (locLabels (L := L₁) sig id)
      (locLabels (L := L₂) sig id)) (hkq : keep q = true)
    {sig' ids₁' bs₁'' mkEnv₁ ids₂' bs₂'' mkEnv₂}
    (Js₁ : Tup (JLabel L₁) sig') (Js₂ : Tup (JLabel L₂) sig')
    (hr₁ : filterSBlocks keep sig bs₁ id = ⟨sig', ids₁', bs₁'', mkEnv₁⟩)
    (hr₂ : filterSBlocks keep sig bs₂ id = ⟨sig', ids₂', bs₂'', mkEnv₂⟩) :
    ∃ j₁ j₂, lookupLblEnv (mkEnv₁ Js₁) q ts' = some j₁ ∧
      lookupLblEnv (mkEnv₂ Js₂) q ts' = some j₂ ∧ ⟨ts', j₁, j₂⟩ ∈ Tup.zip Js₁ Js₂ :=
  let rec go : ∀ (r₁ : FilterRes (OptV V₁) L₁ rs) (r₂ : FilterRes (OptV V₂) L₂ rs),
      ⟨sig', ids₁', bs₁'', mkEnv₁⟩ = r₁ → ⟨sig', ids₂', bs₂'', mkEnv₂⟩ = r₂ →
      (∀ (j₁ : Tup (JLabel L₁) r₁.sig) (j₂ : Tup (JLabel L₂) r₂.sig) (hs : r₁.sig = r₂.sig),
        ∃ l₁ l₂, lookupLblEnv (r₁.mkEnv j₁) q ts' = some l₁ ∧
          lookupLblEnv (r₂.mkEnv j₂) q ts' = some l₂ ∧
          ⟨ts', l₁, l₂⟩ ∈ Tup.zip j₁ (hs ▸ j₂)) →
      ∃ j₁ j₂, lookupLblEnv (mkEnv₁ Js₁) q ts' = some j₁ ∧
        lookupLblEnv (mkEnv₂ Js₂) q ts' = some j₂ ∧ ⟨ts', j₁, j₂⟩ ∈ Tup.zip Js₁ Js₂
    | _, _, rfl, rfl, H => H Js₁ Js₂ rfl
  go _ _ hr₁.symm hr₂.symm fun j₁ j₂ hs =>
    filterSBlocks_mkEnv_lookup keep sig bs₁ bs₂ id hq₁ hq₂ hm hkq j₁ j₂ hs

theorem filterSBlocks_mkEnv_lt_none_eq {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (keep : Nat → Bool) (sig : List (List Ty))
    (bs : SBlocks (OptV V) (JLabel L) rs sig) (id q : Nat) (ts : List Ty) (hq : q < id)
    {sig' ids' bs' mkEnv'} (Js : Tup (JLabel L) sig')
    (hr : filterSBlocks keep sig bs id = ⟨sig', ids', bs', mkEnv'⟩) :
    lookupLblEnv (mkEnv' Js) q ts = none :=
  let rec go : ∀ (r : FilterRes (OptV V) L rs), ⟨sig', ids', bs', mkEnv'⟩ = r →
      (∀ (j : Tup (JLabel L) r.sig), lookupLblEnv (r.mkEnv j) q ts = none) →
      lookupLblEnv (mkEnv' Js) q ts = none
    | _, rfl, H => H Js
  go _ hr.symm fun j => filterSBlocks_mkEnv_lt_none keep sig bs id j q ts hq

theorem filterSBlocks_head_closed_eq {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (reach : List Nat) (lo hi : Nat) (sig : List (List Ty))
    (bs : SBlocks (OptV V) (JLabel L) rs sig) (id : Nat)
    (hsbc : SBlocksClosed reach lo hi id bs) {ts : List Ty} {jId : Nat} {b mkEnv}
    (hr : filterSBlocks (fun x => reach.contains x) sig bs id =
      ⟨[ts], [jId], .cons b .nil, mkEnv⟩) :
    jId ∈ reach ∧ ∀ x ∈ collectJumps lo hi (b (dummyArgOptTup ts)) [], x ∈ reach :=
  let rec go : ∀ r : FilterRes (OptV V) L rs, ⟨[ts], [jId], .cons b .nil, mkEnv⟩ = r →
      (∀ (h1 : r.sig = [ts]) (_ : r.ids = [jId]) (_ : (h1 ▸ r.blocks) = .cons b .nil),
        jId ∈ reach ∧ ∀ x ∈ collectJumps lo hi (b (dummyArgOptTup ts)) [], x ∈ reach) →
      jId ∈ reach ∧ ∀ x ∈ collectJumps lo hi (b (dummyArgOptTup ts)) [], x ∈ reach
    | _, rfl, H => H rfl rfl rfl
  go _ hr.symm fun h1 h2 h3 => filterSBlocks_head_closed reach lo hi sig bs id hsbc h1 h2 h3

theorem filterSBlocks_single_ts_eq {V : Ty → Type} {L L₁ L₂ : List Ty → Type} {rs : List Ty}
    (keep : Nat → Bool) (sig : List (List Ty)) (bs : SBlocks V (JLabel L) rs sig) (id : Nat)
    {jTs ts' : List Ty} {jId : Nat} {b mkEnv}
    (hr : filterSBlocks keep sig bs id = ⟨[jTs], [jId], .cons b .nil, mkEnv⟩)
    (hmem : ⟨ts', .loc jId, .loc jId⟩ ∈
      Tup.zip (locLabels (L := L₁) sig id) (locLabels (L := L₂) sig id)) : ts' = jTs :=
  let rec go : ∀ r : FilterRes V L rs, ⟨[jTs], [jId], .cons b .nil, mkEnv⟩ = r →
      (r.sig = [jTs] → r.ids = [jId] → ts' = jTs) → ts' = jTs
    | _, rfl, H => H rfl rfl
  go _ hr.symm fun hs hi => filterSBlocks_single_ts keep sig bs id hs hi hmem

end SgImpl

end LeanQbe.T
