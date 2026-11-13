module

public import LeanQbe.Gvn
public import LeanQbe.WfLemmas

/-!
# Correctness of `gvn` (common-subexpression elimination)

* `gvn_wp`: the source `wp` implies the `wp` of the output. Besides `Wf` between the input (at
  `Arg Val × Key`) and the source (at `Val`), the invariant is a valuation `ρ : Nat → Val` of the keys
  below the counter `b`: every input variable's operand and key both evaluate to the source value
  (`GoodG`), and every table entry's operation evaluates, under `ρ`, to its operand (`GoodT`).
* `gvn_wf`: `Wf` is preserved (both instantiations compute the same keys and the same table shape).
* `Func.gvn_spec`, `Func.gvn_wf`: closed functions.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe

/-! ## Keys -/

def Arg.ev (ρ : Nat → Val) : Key → Val
  | .var i => ρ i
  | .imm c => c

def Arg.Lt (b : Nat) : Key → Prop
  | .var i => i < b
  | .imm _ => True

def Op.args {V : Type} : Op V → List (Arg V)
  | .bin _ _ a b => [a, b]
  | .cmp _ _ a b => [a, b]
  | .ext _ _ _ a => [a]
  | .copy _ a => [a]

def Op.KeysLt (b : Nat) (o : Op Nat) : Prop := ∀ κ ∈ o.args, κ.Lt b

/-- Extend a valuation with the value of key `b`. -/
def upd (ρ : Nat → Val) (b : Nat) (v : Val) : Nat → Val := fun i => if i = b then v else ρ i

theorem Arg.val_map (ρ : Nat → Val) (κ : Key) : (Arg.map ρ κ).val = κ.ev ρ := by
  cases κ <;> rfl

theorem Arg.Lt.mono {b : Nat} {κ : Key} (h : κ.Lt b) : κ.Lt (b + 1) := by
  cases κ with
  | var i => exact Nat.lt_succ_of_lt h
  | imm _ => trivial

theorem Arg.ev_upd {ρ : Nat → Val} {b : Nat} {v : Val} {κ : Key} (h : κ.Lt b) :
    κ.ev (upd ρ b v) = κ.ev ρ := by
  cases κ with
  | var i => simp only [Arg.ev, upd, Nat.ne_of_lt h, ↓reduceIte]
  | imm _ => rfl

theorem Op.KeysLt.mono {b : Nat} {o : Op Nat} (h : o.KeysLt b) : o.KeysLt (b + 1) :=
  fun κ hκ => (h κ hκ).mono

theorem Op.map_upd {ρ : Nat → Val} {b : Nat} {v : Val} {o : Op Nat} (h : o.KeysLt b) :
    o.map (upd ρ b v) = o.map ρ := by
  have ha : ∀ a : Key, a.Lt b → Arg.map (upd ρ b v) a = Arg.map ρ a := by
    intro a ha
    cases a with
    | var i => simp only [Arg.map, upd, Nat.ne_of_lt ha, ↓reduceIte]
    | imm _ => rfl
  cases o with
  | bin k o a c =>
    have h1 := ha a (h a (by simp [Op.args]))
    have h2 := ha c (h c (by simp [Op.args]))
    simp only [Op.map, h1, h2]
  | cmp k o a c =>
    have h1 := ha a (h a (by simp [Op.args]))
    have h2 := ha c (h c (by simp [Op.args]))
    simp only [Op.map, h1, h2]
  | ext k s sg a =>
    have h1 := ha a (h a (by simp [Op.args]))
    simp only [Op.map, h1]
  | copy k a =>
    have h1 := ha a (h a (by simp [Op.args]))
    simp only [Op.map, h1]

theorem Tbl.find_mem {V : Type} {ko : Op Nat} :
    ∀ {t : Tbl V} {r : Arg V × Key}, t.find ko = some r → (ko, r) ∈ t
  | [], _, h => by simp [Tbl.find] at h
  | (o, r') :: t, r, h => by
    simp only [Tbl.find] at h
    split at h
    · next ho => subst ho; cases h; exact List.Mem.head _
    · exact List.Mem.tail _ (Tbl.find_mem h)

/-! ## The invariant -/

/-- Every input variable denotes an operand and a key with the source value. -/
def GoodG (ρ : Nat → Val) (b : Nat) (G : List ((Arg Val × Key) × Val)) : Prop :=
  ∀ p ∈ G, p.1.1.val = p.2 ∧ p.1.2.ev ρ = p.2 ∧ p.1.2.Lt b

/-- Every table entry's operation evaluates to its operand. -/
def GoodT (ρ : Nat → Val) (b : Nat) (t : Tbl Val) : Prop :=
  ∀ e ∈ t, (e.1.map ρ).eval = some e.2.1.val ∧ e.2.2.ev ρ = e.2.1.val ∧ e.2.2.Lt b ∧ e.1.KeysLt b

theorem GoodG.cons {ρ : Nat → Val} {b : Nat} {G : List ((Arg Val × Key) × Val)} (hG : GoodG ρ b G)
    {r : Arg Val × Key} {v : Val} (h1 : r.1.val = v) (h2 : r.2.ev ρ = v) (h3 : r.2.Lt b) :
    GoodG ρ b ((r, v) :: G) := by
  intro p hp
  cases hp with
  | head => exact ⟨h1, h2, h3⟩
  | tail _ hp => exact hG p hp

theorem GoodG.upd {ρ : Nat → Val} {b : Nat} {G : List ((Arg Val × Key) × Val)} (hG : GoodG ρ b G)
    (v : Val) : GoodG (LeanQbe.upd ρ b v) (b + 1) G := by
  intro p hp
  obtain ⟨h1, h2, h3⟩ := hG p hp
  exact ⟨h1, (Arg.ev_upd h3).trans h2, h3.mono⟩

theorem GoodT.upd {ρ : Nat → Val} {b : Nat} {t : Tbl Val} (hT : GoodT ρ b t) (v : Val) :
    GoodT (LeanQbe.upd ρ b v) (b + 1) t := by
  intro e he
  obtain ⟨h1, h2, h3, h4⟩ := hT e he
  refine ⟨?_, (Arg.ev_upd h3).trans h2, h3.mono, h4.mono⟩
  rw [Op.map_upd h4]; exact h1

/-- The fresh variable `v` with key `b`. -/
theorem GoodG.fresh {ρ : Nat → Val} {b : Nat} {G : List ((Arg Val × Key) × Val)} (hG : GoodG ρ b G)
    (v : Val) : GoodG (LeanQbe.upd ρ b v) (b + 1) (((.var v, .var b), v) :: G) :=
  (hG.upd v).cons rfl (by simp [Arg.ev, LeanQbe.upd]) (Nat.lt_succ_self b)

section
variable {G : List ((Arg Val × Key) × Val)} {ρ : Nat → Val} {b : Nat}

theorem ArgRel.out_val (hG : GoodG ρ b G) {a₁ : Arg (Arg Val × Key)} {a₂ : Arg Val} :
    ArgRel G a₁ a₂ → a₁.out.val = a₂.val
  | .var h => (hG _ h).1
  | .imm _ => rfl

theorem ArgRel.key_ev (hG : GoodG ρ b G) {a₁ : Arg (Arg Val × Key)} {a₂ : Arg Val} :
    ArgRel G a₁ a₂ → a₁.key.ev ρ = a₂.val
  | .var h => (hG _ h).2.1
  | .imm _ => rfl

theorem ArgRel.key_lt (hG : GoodG ρ b G) {a₁ : Arg (Arg Val × Key)} {a₂ : Arg Val} :
    ArgRel G a₁ a₂ → a₁.key.Lt b
  | .var h => (hG _ h).2.2
  | .imm _ => trivial

theorem Forall₂.out_vals (hG : GoodG ρ b G) :
    ∀ {as₁ : List (Arg (Arg Val × Key))} {as₂ : List (Arg Val)}, Forall₂ (ArgRel G) as₁ as₂ →
      (as₁.map Arg.out).map Arg.val = as₂.map Arg.val
  | _, _, .nil => rfl
  | _, _, .cons h hs => by simp only [List.map_cons, h.out_val hG, Forall₂.out_vals hG hs]

theorem OpRel.out_eval (hG : GoodG ρ b G) {o₁ : Op (Arg Val × Key)} {o₂ : Op Val} (h : OpRel G o₁ o₂) :
    (o₁.mapArgs Arg.out).eval = o₂.eval := by
  cases h with
  | bin k o ha hb => cases k <;> simp only [Op.mapArgs, Op.eval, ha.out_val hG, hb.out_val hG]
  | cmp k o ha hb => cases k <;> simp only [Op.mapArgs, Op.eval, ha.out_val hG, hb.out_val hG]
  | ext k s sg ha => simp only [Op.mapArgs, Op.eval, ha.out_val hG]
  | copy k ha => simp only [Op.mapArgs, Op.eval, ha.out_val hG]

theorem OpRel.key_eval (hG : GoodG ρ b G) {o₁ : Op (Arg Val × Key)} {o₂ : Op Val} (h : OpRel G o₁ o₂) :
    ((o₁.mapArgs Arg.key).map ρ).eval = o₂.eval := by
  cases h with
  | bin k o ha hb =>
    cases k <;> simp only [Op.mapArgs, Op.map, Op.eval, Arg.val_map, ha.key_ev hG, hb.key_ev hG]
  | cmp k o ha hb =>
    cases k <;> simp only [Op.mapArgs, Op.map, Op.eval, Arg.val_map, ha.key_ev hG, hb.key_ev hG]
  | ext k s sg ha => simp only [Op.mapArgs, Op.map, Op.eval, Arg.val_map, ha.key_ev hG]
  | copy k ha => simp only [Op.mapArgs, Op.map, Op.eval, Arg.val_map, ha.key_ev hG]

theorem OpRel.keys_lt (hG : GoodG ρ b G) {o₁ : Op (Arg Val × Key)} {o₂ : Op Val} (h : OpRel G o₁ o₂) :
    (o₁.mapArgs Arg.key).KeysLt b := by
  intro κ hκ
  cases h with
  | bin k o ha hb =>
    simp only [Op.mapArgs, Op.args, List.mem_cons, List.not_mem_nil, or_false] at hκ
    rcases hκ with rfl | rfl
    · exact ha.key_lt hG
    · exact hb.key_lt hG
  | cmp k o ha hb =>
    simp only [Op.mapArgs, Op.args, List.mem_cons, List.not_mem_nil, or_false] at hκ
    rcases hκ with rfl | rfl
    · exact ha.key_lt hG
    · exact hb.key_lt hG
  | ext k s sg ha =>
    simp only [Op.mapArgs, Op.args, List.mem_cons, List.not_mem_nil, or_false] at hκ
    subst hκ; exact ha.key_lt hG
  | copy k ha =>
    simp only [Op.mapArgs, Op.args, List.mem_cons, List.not_mem_nil, or_false] at hκ
    subst hκ; exact ha.key_lt hG

end

/-! ## `wp` preservation -/

theorem gvn_wp {Γ : Env} {Q : Post} {X : XPost} :
    ∀ {G : List ((Arg Val × Key) × Val)} {D : List (Cont × Cont)} {e₁ : Expr (Arg Val × Key) Cont}
      {e₂ : Expr Val Cont}, Wf G D e₁ e₂ → (∀ p ∈ D, p.1 = p.2) →
    ∀ n b tbl ρ, GoodG ρ b G → GoodT ρ b tbl →
    ∀ args acc m, acc.length = n → wp Γ Q X e₂ args acc m → wp Γ Q X (gvn n b tbl e₁) args acc m := by
  intro G D e₁ e₂ h
  induction h with
  | @let_ G D op₁ op₂ k₁ k₂ ho _ ih =>
    intro hD n b tbl ρ hG hT args acc m hn hw
    obtain ⟨rfl, v, hv, hk⟩ := hw
    have hout := ho.out_eval hG
    have hkey := ho.key_eval hG
    have hlt := ho.keys_lt hG
    -- the miss case, shared by `n ≠ 0` and a table miss
    have miss : wp Γ Q X (.let_ (op₁.mapArgs Arg.out) fun v' =>
        gvn 0 (b + 1) ((op₁.mapArgs Arg.key, .var v', .var b) :: tbl) (k₁ (.var v', .var b))) [] acc m := by
      refine ⟨rfl, v, hout ▸ hv, ?_⟩
      refine ih (.var v, .var b) v hD 0 (b + 1) _ (upd ρ b v) (hG.fresh v) ?_ [] [] m rfl hk
      intro e he
      cases he with
      | head =>
        refine ⟨?_, by simp [Arg.ev, LeanQbe.upd, Arg.val], Nat.lt_succ_self b, hlt.mono⟩
        rw [Op.map_upd hlt, hkey, hv]; rfl
      | tail _ he => exact hT.upd v e he
    unfold gvn
    split
    · next hn0 =>
      subst hn0
      have : acc = [] := List.eq_nil_of_length_eq_zero hn
      subst this
      dsimp only
      split
      · next r hr =>
        obtain ⟨h1, h2, h3, _⟩ := hT _ (Tbl.find_mem hr)
        have hvr : v = r.1.val := by
          grind
        subst hvr
        exact ih r r.1.val hD 0 b tbl ρ (hG.cons rfl h2 h3) hT [] [] m rfl hk
      · exact miss
    · exact miss
  | load c s sg ha _ ih =>
    intro hD n b tbl ρ hG hT args acc m _ hw
    simp only [wp, gvn] at hw ⊢
    obtain ⟨rfl, v, hv, hk⟩ := hw
    exact ⟨rfl, v, ha.out_val hG ▸ hv,
      ih (.var v, .var b) v hD 0 (b + 1) tbl (upd ρ b v) (hG.fresh v) (hT.upd v) [] [] m rfl hk⟩
  | store s hv ha _ ih =>
    intro hD n b tbl ρ hG hT args acc m _ hw
    simp only [wp, gvn] at hw ⊢
    obtain ⟨rfl, hok, hk⟩ := hw
    rw [ha.out_val hG, hv.out_val hG]
    exact ⟨rfl, hok, ih hD 0 b tbl ρ hG hT [] [] _ rfl hk⟩
  | call f has _ ih =>
    intro hD n b tbl ρ hG hT args acc m _ hw
    simp only [wp, gvn] at hw ⊢
    obtain ⟨rfl, P, E, hΓ, hP, hE⟩ := hw
    rw [has.out_vals hG]
    exact ⟨rfl, P, E, hΓ, fun rs m' hp => ih hD 0 b tbl ρ hG hT rs [] m' rfl (hP rs m' hp), hE⟩
  | jnz hc _ _ iht ihe =>
    intro hD n b tbl ρ hG hT args acc m _ hw
    simp only [wp, gvn] at hw ⊢
    obtain ⟨rfl, ht, he⟩ := hw
    rw [hc.out_val hG]
    grind
  | jump hj has =>
    intro hD n b tbl ρ hG hT args acc m _ hw
    simp only [wp, gvn] at hw ⊢
    have hj' := hD _ hj
    simp only at hj'
    subst hj'
    rw [has.out_vals hG]
    exact hw
  | ret has =>
    intro hD n b tbl ρ hG hT args acc m _ hw
    simp only [wp, gvn] at hw ⊢
    rw [has.out_vals hG]
    exact hw
  | exit f has =>
    intro hD n b tbl ρ hG hT args acc m _ hw
    simp only [wp, gvn] at hw ⊢
    rw [has.out_vals hG]
    exact hw
  | hlt => intro _ _ _ _ _ _ _ _ _ _ _ hw; simp only [wp] at hw
  | param _ ih =>
    intro hD n b tbl ρ hG hT args acc m _ hw
    cases args with
    | nil => simp only [wp] at hw
    | cons a as =>
      simp only [wp, gvn] at hw ⊢
      exact ih (.var a, .var b) a hD 0 (b + 1) tbl (upd ρ b a) (hG.fresh a) (hT.upd a) as [] m rfl hw
  | label _ ih =>
    intro hD n b tbl ρ hG hT args acc m hn hw
    simp only [wp, gvn] at hw ⊢
    grind
  | block _ _ ihb ihr =>
    intro hD n b tbl ρ hG hT args acc m hn hw
    cases acc with
    | nil => simp only [wp, and_false] at hw
    | cons J acc' =>
      simp only [wp, gvn] at hw ⊢
      grind

/-! ## `Wf` preservation -/

section
variable {V₁ V₂ : Type}

/-- The two instantiations agree on keys and have related operands. -/
def RelG (G' : List (V₁ × V₂)) (G : List ((Arg V₁ × Key) × (Arg V₂ × Key))) : Prop :=
  ∀ p ∈ G, ArgRel G' p.1.1 p.2.1 ∧ p.1.2 = p.2.2

def RelT (G' : List (V₁ × V₂)) (t₁ : Tbl V₁) (t₂ : Tbl V₂) : Prop :=
  Forall₂ (fun e₁ e₂ => e₁.1 = e₂.1 ∧ ArgRel G' e₁.2.1 e₂.2.1 ∧ e₁.2.2 = e₂.2.2) t₁ t₂

variable {G' : List (V₁ × V₂)} {G : List ((Arg V₁ × Key) × (Arg V₂ × Key))}

theorem RelG.cons (hG : RelG G' G) {r₁ : Arg V₁ × Key} {r₂ : Arg V₂ × Key} (h1 : ArgRel G' r₁.1 r₂.1)
    (h2 : r₁.2 = r₂.2) : RelG G' ((r₁, r₂) :: G) := by
  intro p hp
  cases hp with
  | head => exact ⟨h1, h2⟩
  | tail _ hp => exact hG p hp

theorem RelG.fresh (hG : RelG G' G) (v₁ : V₁) (v₂ : V₂) (b : Nat) :
    RelG ((v₁, v₂) :: G') (((.var v₁, .var b), (.var v₂, .var b)) :: G) := by
  intro p hp
  cases hp with
  | head => exact ⟨.var (List.Mem.head _), rfl⟩
  | tail _ hp =>
    obtain ⟨h1, h2⟩ := hG p hp
    exact ⟨h1.weaken fun _ hq => List.Mem.tail _ hq, h2⟩

theorem RelT.weaken {t₁ : Tbl V₁} {t₂ : Tbl V₂} (hT : RelT G' t₁ t₂) (v₁ : V₁) (v₂ : V₂) :
    RelT ((v₁, v₂) :: G') t₁ t₂ :=
  hT.imp fun _ _ ⟨h1, h2, h3⟩ => ⟨h1, h2.weaken fun _ hq => List.Mem.tail _ hq, h3⟩

theorem RelT.find {ko : Op Nat} :
    ∀ {t₁ : Tbl V₁} {t₂ : Tbl V₂}, RelT G' t₁ t₂ →
      (t₁.find ko = none ∧ t₂.find ko = none) ∨
        ∃ r₁ r₂, t₁.find ko = some r₁ ∧ t₂.find ko = some r₂ ∧ ArgRel G' r₁.1 r₂.1 ∧ r₁.2 = r₂.2
  | _, _, .nil => .inl ⟨rfl, rfl⟩
  | (o₁, r₁) :: _, (o₂, r₂) :: _, .cons ⟨h1, h2, h3⟩ hs => by
    simp only at h1
    subst h1
    simp only [Tbl.find]
    split
    · exact .inr ⟨r₁, r₂, rfl, rfl, h2, h3⟩
    · exact RelT.find hs

theorem ArgRel.key_eq (hG : RelG G' G) {a₁ : Arg (Arg V₁ × Key)} {a₂ : Arg (Arg V₂ × Key)} :
    ArgRel G a₁ a₂ → a₁.key = a₂.key
  | .var h => (hG _ h).2
  | .imm _ => rfl

theorem ArgRel.out (hG : RelG G' G) {a₁ : Arg (Arg V₁ × Key)} {a₂ : Arg (Arg V₂ × Key)} :
    ArgRel G a₁ a₂ → ArgRel G' a₁.out a₂.out
  | .var h => (hG _ h).1
  | .imm c => .imm c

theorem Forall₂.out (hG : RelG G' G) :
    ∀ {as₁ as₂}, Forall₂ (ArgRel G) as₁ as₂ → Forall₂ (ArgRel G') (as₁.map Arg.out) (as₂.map Arg.out)
  | _, _, .nil => .nil
  | _, _, .cons h hs => .cons (h.out hG) (Forall₂.out hG hs)

theorem OpRel.key_eq (hG : RelG G' G) {o₁ : Op (Arg V₁ × Key)} {o₂ : Op (Arg V₂ × Key)}
    (h : OpRel G o₁ o₂) : o₁.mapArgs Arg.key = o₂.mapArgs Arg.key := by
  cases h with
  | bin k o ha hb => simp only [Op.mapArgs, ha.key_eq hG, hb.key_eq hG]
  | cmp k o ha hb => simp only [Op.mapArgs, ha.key_eq hG, hb.key_eq hG]
  | ext k s sg ha => simp only [Op.mapArgs, ha.key_eq hG]
  | copy k ha => simp only [Op.mapArgs, ha.key_eq hG]

theorem OpRel.out (hG : RelG G' G) {o₁ : Op (Arg V₁ × Key)} {o₂ : Op (Arg V₂ × Key)} :
    OpRel G o₁ o₂ → OpRel G' (o₁.mapArgs Arg.out) (o₂.mapArgs Arg.out)
  | .bin k o ha hb => .bin k o (ha.out hG) (hb.out hG)
  | .cmp k o ha hb => .cmp k o (ha.out hG) (hb.out hG)
  | .ext k s sg ha => .ext k s sg (ha.out hG)
  | .copy k ha => .copy k (ha.out hG)

end

theorem gvn_wf {V₁ V₂ L₁ L₂ : Type} :
    ∀ {G : List ((Arg V₁ × Key) × (Arg V₂ × Key))} {D : List (L₁ × L₂)}
      {e₁ : Expr (Arg V₁ × Key) L₁} {e₂ : Expr (Arg V₂ × Key) L₂}, Wf G D e₁ e₂ →
    ∀ n b (t₁ : Tbl V₁) (t₂ : Tbl V₂) (G' : List (V₁ × V₂)), RelG G' G → RelT G' t₁ t₂ →
      Wf G' D (gvn n b t₁ e₁) (gvn n b t₂ e₂) := by
  intro G D e₁ e₂ h
  induction h with
  | @let_ G D op₁ op₂ k₁ k₂ ho _ ih =>
    intro n b t₁ t₂ G' hG hT
    have hko := ho.key_eq hG
    have hout := ho.out hG
    have miss : Wf G' D
        (.let_ (op₁.mapArgs Arg.out) fun v =>
          gvn 0 (b + 1) ((op₁.mapArgs Arg.key, .var v, .var b) :: t₁) (k₁ (.var v, .var b)))
        (.let_ (op₂.mapArgs Arg.out) fun v =>
          gvn 0 (b + 1) ((op₂.mapArgs Arg.key, .var v, .var b) :: t₂) (k₂ (.var v, .var b))) := by
      refine .let_ hout fun v₁ v₂ => ih _ _ 0 (b + 1) _ _ _ (hG.fresh v₁ v₂ b) ?_
      exact .cons ⟨hko, .var (List.Mem.head _), rfl⟩ (hT.weaken v₁ v₂)
    simp only [gvn]
    by_cases hn : n = 0
    · simp only [hn, ↓reduceIte]
      rw [hko] at miss ⊢
      rcases hT.find (ko := op₂.mapArgs Arg.key) with ⟨h1, h2⟩ | ⟨r₁, r₂, h1, h2, hr1, hr2⟩
      · rw [h1, h2]; exact miss
      · rw [h1, h2]; exact ih r₁ r₂ 0 b t₁ t₂ G' (hG.cons hr1 hr2) hT
    · grind
  | load c s sg ha _ ih =>
    intro n b t₁ t₂ G' hG hT
    exact .load c s sg (ha.out hG) fun v₁ v₂ =>
      ih _ _ 0 (b + 1) t₁ t₂ _ (hG.fresh v₁ v₂ b) (hT.weaken v₁ v₂)
  | store s hv ha _ ih =>
    intro n b t₁ t₂ G' hG hT; exact .store s (hv.out hG) (ha.out hG) (ih 0 b t₁ t₂ G' hG hT)
  | call f has _ ih => intro n b t₁ t₂ G' hG hT; exact .call f (has.out hG) (ih 0 b t₁ t₂ G' hG hT)
  | jnz hc _ _ iht ihe =>
    intro n b t₁ t₂ G' hG hT
    exact .jnz (hc.out hG) (iht 0 b t₁ t₂ G' hG hT) (ihe 0 b t₁ t₂ G' hG hT)
  | jump hj has => intro n b t₁ t₂ G' hG hT; exact .jump hj (has.out hG)
  | ret has => intro n b t₁ t₂ G' hG hT; exact .ret (has.out hG)
  | exit f has => intro n b t₁ t₂ G' hG hT; exact .exit f (has.out hG)
  | hlt => intro _ _ _ _ _ _ _; exact .hlt
  | param _ ih =>
    intro n b t₁ t₂ G' hG hT
    exact .param fun v₁ v₂ => ih _ _ 0 (b + 1) t₁ t₂ _ (hG.fresh v₁ v₂ b) (hT.weaken v₁ v₂)
  | label _ ih =>
    intro n b t₁ t₂ G' hG hT; exact .label fun j₁ j₂ => ih j₁ j₂ (n + 1) b t₁ t₂ G' hG hT
  | block _ _ ihb ihr =>
    intro n b t₁ t₂ G' hG hT
    exact .block (ihb 0 b t₁ t₂ G' hG hT) (ihr (n - 1) b t₁ t₂ G' hG hT)

/-! ## Closed functions -/

theorem Func.gvn_wf {f : Func} (hf : f.Wf) : (Func.gvn f).Wf :=
  fun V₁ V₂ L₁ L₂ => LeanQbe.gvn_wf (hf (Arg V₁ × Key) (Arg V₂ × Key) L₁ L₂) 0 0 [] [] []
    (fun _ hp => nomatch hp) .nil

theorem Func.gvn_spec {f : Func} (hf : f.Wf) {Γ : Env} {args : List Val} {m : Mem 64}
    {Q : Post} {X : XPost} (h : Func.spec Γ f args m Q X) : Func.spec Γ (Func.gvn f) args m Q X :=
  LeanQbe.gvn_wp (hf (Arg Val × Key) Val Cont Cont) (fun _ hp => nomatch hp) 0 0 [] (fun _ => 0)
    (fun _ hp => nomatch hp) (fun _ hp => nomatch hp) args [] m rfl h

end LeanQbe
