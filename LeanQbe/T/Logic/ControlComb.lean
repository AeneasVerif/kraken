module

public import LeanQbe.T.Logic.Rules

/-!
# State-indexed PHOAS control combinators (`ControlComb`)

Pure tuple-free combinators for `LeanQbe.T.wp`:
* **Branch elimination**: `jnz_decide`, `wp_jnz_decide`, `jnz_not_decide`, `wp_jnz_not_decide`,
  `jnz_iff`, `wp_jnz_iff`, `jnz_bool`, `wp_jnz_bool`, `jnz_true`, `wp_jnz_true`,
  `jnz_false`, `wp_jnz_false`.
* **State-indexed join rules**: `wp_join_state`, `wp_join_state0`, `wp_join_state1`,
  `wp_join_state_pure`, `wp_join0`.
* **State-indexed loop rules**: `wp_while_state`, `wp_while_state0`, `wp_while_state1`,
  `wp_while_state_pure`, `wp_while_break_state`.
* **Jump helpers**: `wp_jump_state`, `cont_of_eq`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

section ControlComb

/-! ## Branch elimination (`jnz`) -/

/-- Eliminate a post-`wp_unfold` `jnz` conjunction whose condition equals `decide P`, splitting
`(b = true → A) ∧ (b = false → B)` into `P → A` and `¬P → B`. -/
theorem jnz_decide {b : Bool} {A B : Prop} (P : Prop) [Decidable P]
    (hb : b = decide P) (ht : P → A) (hf : ¬P → B) :
    (b = true → A) ∧ (b = false → B) :=
  ⟨fun h => ht (of_decide_eq_true (hb ▸ h)),
   fun h => hf (of_decide_eq_false (hb ▸ h))⟩

/-- Eliminate a post-`wp_unfold` `jnz` conjunction whose condition equals `!(decide P)`. -/
theorem jnz_not_decide {b : Bool} {A B : Prop} (P : Prop) [Decidable P]
    (hb : b = !(decide P)) (ht : ¬P → A) (hf : P → B) :
    (b = true → A) ∧ (b = false → B) :=
  ⟨fun h => ht (by rw [hb] at h; simpa using h),
   fun h => hf (by rw [hb] at h; simpa using h)⟩

/-- Eliminate a post-`wp_unfold` `jnz` conjunction via an equivalence `b = true ↔ P`. -/
theorem jnz_iff {b : Bool} {A B : Prop} (P : Prop)
    (hb : b = true ↔ P) (ht : P → A) (hf : ¬P → B) :
    (b = true → A) ∧ (b = false → B) :=
  ⟨fun h => ht (hb.mp h),
   fun h => hf fun hp => Bool.false_ne_true (h.symm.trans (hb.mpr hp))⟩

/-- Eliminate a post-`wp_unfold` `jnz` conjunction by normalizing `b = b'`. -/
theorem jnz_bool {b : Bool} {A B : Prop} (b' : Bool)
    (hb : b = b') (ht : b' = true → A) (hf : b' = false → B) :
    (b = true → A) ∧ (b = false → B) :=
  ⟨fun h => ht (hb ▸ h), fun h => hf (hb ▸ h)⟩

/-- Discharge a post-`wp_unfold` `jnz` conjunction when the condition is `true`. -/
theorem jnz_true {b : Bool} {A B : Prop} (hb : b = true) (ht : A) :
    (b = true → A) ∧ (b = false → B) :=
  ⟨fun _ => ht, fun h => Bool.noConfusion (hb.symm.trans h)⟩

/-- Discharge a post-`wp_unfold` `jnz` conjunction when the condition is `false`. -/
theorem jnz_false {b : Bool} {A B : Prop} (hb : b = false) (hf : B) :
    (b = true → A) ∧ (b = false → B) :=
  ⟨fun h => Bool.noConfusion (hb.symm.trans h), fun _ => hf⟩

/-- Eliminate a `jnz` whose boolean condition equals `decide P`, splitting into `P` and `¬P`. -/
theorem wp_jnz_decide {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {c : Arg Val .bool} {e₁ e₂ : Expr Val Cont rs} (P : Prop) [Decidable P]
    (hc : c.val = decide P)
    (ht : P → wp Γ Q X e₁ m) (hf : ¬P → wp Γ Q X e₂ m) :
    wp Γ Q X (.jnz c e₁ e₂) m :=
  jnz_decide P hc ht hf

/-- Eliminate a `jnz` whose boolean condition equals `!(decide P)`, splitting into `¬P` and
`P`. -/
theorem wp_jnz_not_decide {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {c : Arg Val .bool} {e₁ e₂ : Expr Val Cont rs} (P : Prop) [Decidable P]
    (hc : c.val = !(decide P))
    (ht : ¬P → wp Γ Q X e₁ m) (hf : P → wp Γ Q X e₂ m) :
    wp Γ Q X (.jnz c e₁ e₂) m :=
  jnz_not_decide P hc ht hf

/-- Eliminate a `jnz` via an equivalence `c.val = true ↔ P`, splitting into `P` and `¬P`. -/
theorem wp_jnz_iff {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {c : Arg Val .bool} {e₁ e₂ : Expr Val Cont rs} (P : Prop)
    (hc : c.val = true ↔ P)
    (ht : P → wp Γ Q X e₁ m) (hf : ¬P → wp Γ Q X e₂ m) :
    wp Γ Q X (.jnz c e₁ e₂) m :=
  jnz_iff P hc ht hf

/-- Eliminate a `jnz` by normalizing `c.val = b` for a boolean expression `b`. -/
theorem wp_jnz_bool {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {c : Arg Val .bool} {e₁ e₂ : Expr Val Cont rs} (b : Bool) (hc : c.val = b)
    (ht : b = true → wp Γ Q X e₁ m) (hf : b = false → wp Γ Q X e₂ m) :
    wp Γ Q X (.jnz c e₁ e₂) m :=
  jnz_bool b hc ht hf

/-- Discharge a `jnz` when the condition is known to be `true`. -/
theorem wp_jnz_true {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {c : Arg Val .bool} {e₁ e₂ : Expr Val Cont rs}
    (hc : c.val = true) (ht : wp Γ Q X e₁ m) :
    wp Γ Q X (.jnz c e₁ e₂) m :=
  jnz_true hc ht

/-- Discharge a `jnz` when the condition is known to be `false`. -/
theorem wp_jnz_false {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {c : Arg Val .bool} {e₁ e₂ : Expr Val Cont rs}
    (hc : c.val = false) (hf : wp Γ Q X e₂ m) :
    wp Γ Q X (.jnz c e₁ e₂) m :=
  jnz_false hc hf

/-! ## Tuple-free join combinators -/

/-- State-indexed join-point combinator eliminating existential `Tup Val ts` packing/unpacking.
Parameterizes the join invariant over a logical state `α` and projection `proj : α → Tup Val ts`.
-/
theorem wp_join_state {Γ : Env} {rs ts : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {bodies : Tup Cont [ts] → Blocks Val Cont rs [ts]}
    {entry : Tup Cont [ts] → Expr Val Cont rs}
    {α : Type _} (proj : α → Tup Val ts) (Inv : α → Mem 64 → Prop)
    (hbody : ∀ (J : Cont ts) (st : α) (m' : Mem 64), Inv st m' →
      wp Γ Q X (Blocks.get (bodies (J, ())) .here (proj st)) m')
    (hentry : ∀ (J : Cont ts), (∀ st m', Inv st m' → J (proj st) m') →
      wp Γ Q X (entry (J, ())) m) :
    wp Γ Q X (.group (sig := [ts]) bodies entry) m :=
  wp_join_group (fun xs m' => ∃ st : α, proj st = xs ∧ Inv st m')
    (fun J _ m' ⟨st, hEq, hInv⟩ => hEq ▸ hbody J st m' hInv)
    (fun J hJ => hentry J fun st m' hInv => hJ (proj st) m' ⟨st, rfl, hInv⟩)

/-- Specialization of `wp_join_state` to 0-ary join blocks (`ts = []`). -/
theorem wp_join_state0 {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {bodies : Tup Cont [[]] → Blocks Val Cont rs [[]]}
    {entry : Tup Cont [[]] → Expr Val Cont rs}
    {α : Type _} (Inv : α → Mem 64 → Prop)
    (hbody : ∀ (J : Cont []) (st : α) (m' : Mem 64), Inv st m' →
      wp Γ Q X (Blocks.get (bodies (J, ())) .here ()) m')
    (hentry : ∀ (J : Cont []), (∀ st m', Inv st m' → J () m') →
      wp Γ Q X (entry (J, ())) m) :
    wp Γ Q X (.group (sig := [[]]) bodies entry) m :=
  wp_join_state (fun _ : α => ()) Inv hbody hentry

/-- Specialization of `wp_join_state` to 1-argument join blocks (`ts = [t]`). -/
theorem wp_join_state1 {Γ : Env} {rs : List Ty} {t : Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {bodies : Tup Cont [[t]] → Blocks Val Cont rs [[t]]}
    {entry : Tup Cont [[t]] → Expr Val Cont rs}
    {α : Type _} (proj : α → Val t) (Inv : α → Mem 64 → Prop)
    (hbody : ∀ (J : Cont [t]) (st : α) (m' : Mem 64), Inv st m' →
      wp Γ Q X (Blocks.get (bodies (J, ())) .here (proj st, ())) m')
    (hentry : ∀ (J : Cont [t]), (∀ st m', Inv st m' → J (proj st, ()) m') →
      wp Γ Q X (entry (J, ())) m) :
    wp Γ Q X (.group (sig := [[t]]) bodies entry) m :=
  wp_join_state (fun st => (proj st, ())) Inv hbody hentry

/-- Specialization of `wp_join_state` for read-only / pure joins where memory `m` is unchanged. -/
theorem wp_join_state_pure {Γ : Env} {rs ts : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {bodies : Tup Cont [ts] → Blocks Val Cont rs [ts]}
    {entry : Tup Cont [ts] → Expr Val Cont rs}
    {α : Type _} (proj : α → Tup Val ts) (Inv : α → Prop)
    (hbody : ∀ (J : Cont ts) (st : α), Inv st →
      wp Γ Q X (Blocks.get (bodies (J, ())) .here (proj st)) m)
    (hentry : ∀ (J : Cont ts), (∀ st, Inv st → J (proj st) m) →
      wp Γ Q X (entry (J, ())) m) :
    wp Γ Q X (.group (sig := [ts]) bodies entry) m :=
  wp_join_state proj (fun st m' => Inv st ∧ m' = m)
    (fun J st _ ⟨hInv, hmEq⟩ => hmEq ▸ hbody J st hInv)
    (fun J hJ => hentry J fun st hInv => hJ st m ⟨hInv, rfl⟩)

/-- Specialization of `wp_join_group` to 0-ary join blocks (`ts = []`) with no logical state. -/
theorem wp_join0 {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {bodies : Tup Cont [[]] → Blocks Val Cont rs [[]]}
    {entry : Tup Cont [[]] → Expr Val Cont rs}
    (P : Mem 64 → Prop)
    (hbody : ∀ (J : Cont []) (m' : Mem 64), P m' →
      wp Γ Q X (Blocks.get (bodies (J, ())) .here ()) m')
    (hentry : ∀ (J : Cont []), (∀ m', P m' → J () m') →
      wp Γ Q X (entry (J, ())) m) :
    wp Γ Q X (.group (sig := [[]]) bodies entry) m :=
  wp_join_group (fun _ m' => P m') (fun J _ m' hp => hbody J m' hp)
    (fun J hJ => hentry J fun m' hp => hJ () m' hp)

/-! ## Tuple-free loop combinators -/

/-- State-indexed loop combinator eliminating existential `Tup Val ts` packing and measure
equality boilerplate. Parameterizes the loop over logical state `α`, projection
`proj : α → Tup Val ts`, and termination measure `μ : α → Nat`. -/
theorem wp_while_state {Γ : Env} {rs ts : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {bodies : Tup Cont [ts] → Blocks Val Cont rs [ts]}
    {entry : Tup Cont [ts] → Expr Val Cont rs}
    {α : Type _} (proj : α → Tup Val ts) (μ : α → Nat) (Inv : α → Mem 64 → Prop)
    (hentry : ∀ (J : Cont ts), (∀ st m', Inv st m' → J (proj st) m') →
      wp Γ Q X (entry (J, ())) m)
    (hbody : ∀ (J : Cont ts) (st : α) (m' : Mem 64), Inv st m' →
      (∀ st' m'', μ st' < μ st → Inv st' m'' → J (proj st') m'') →
      wp Γ Q X (Blocks.get (bodies (J, ())) .here (proj st)) m') :
    wp Γ Q X (.group (sig := [ts]) bodies entry) m :=
  wp_loop_group (fun n xs m' => ∃ st : α, proj st = xs ∧ μ st = n ∧ Inv st m')
    (fun J _ _ m' ih ⟨st, hEq, hμ, hInv⟩ =>
      hEq ▸ hbody J st m' hInv fun st' m'' hlt hInv' =>
        ih (μ st') (proj st') m'' (hμ ▸ hlt) ⟨st', rfl, rfl, hInv'⟩)
    (fun J hJ => hentry J fun st m' hInv => hJ (μ st) (proj st) m' ⟨st, rfl, rfl, hInv⟩)

/-- Specialization of `wp_while_state` to 0-ary loop blocks (`ts = []`). -/
theorem wp_while_state0 {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {bodies : Tup Cont [[]] → Blocks Val Cont rs [[]]}
    {entry : Tup Cont [[]] → Expr Val Cont rs}
    {α : Type _} (μ : α → Nat) (Inv : α → Mem 64 → Prop)
    (hentry : ∀ (J : Cont []), (∀ st m', Inv st m' → J () m') →
      wp Γ Q X (entry (J, ())) m)
    (hbody : ∀ (J : Cont []) (st : α) (m' : Mem 64), Inv st m' →
      (∀ st' m'', μ st' < μ st → Inv st' m'' → J () m'') →
      wp Γ Q X (Blocks.get (bodies (J, ())) .here ()) m') :
    wp Γ Q X (.group (sig := [[]]) bodies entry) m :=
  wp_while_state (fun _ : α => ()) μ Inv hentry hbody

/-- Specialization of `wp_while_state` to 1-argument loop blocks (`ts = [t]`). -/
theorem wp_while_state1 {Γ : Env} {rs : List Ty} {t : Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {bodies : Tup Cont [[t]] → Blocks Val Cont rs [[t]]}
    {entry : Tup Cont [[t]] → Expr Val Cont rs}
    {α : Type _} (proj : α → Val t) (μ : α → Nat) (Inv : α → Mem 64 → Prop)
    (hentry : ∀ (J : Cont [t]), (∀ st m', Inv st m' → J (proj st, ()) m') →
      wp Γ Q X (entry (J, ())) m)
    (hbody : ∀ (J : Cont [t]) (st : α) (m' : Mem 64), Inv st m' →
      (∀ st' m'', μ st' < μ st → Inv st' m'' → J (proj st', ()) m'') →
      wp Γ Q X (Blocks.get (bodies (J, ())) .here (proj st, ())) m') :
    wp Γ Q X (.group (sig := [[t]]) bodies entry) m :=
  wp_while_state (fun st => (proj st, ())) μ Inv hentry hbody

/-- Specialization of `wp_while_state` for read-only loops where memory `m` is unchanged. -/
theorem wp_while_state_pure {Γ : Env} {rs ts : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {bodies : Tup Cont [ts] → Blocks Val Cont rs [ts]}
    {entry : Tup Cont [ts] → Expr Val Cont rs}
    {α : Type _} (proj : α → Tup Val ts) (μ : α → Nat) (Inv : α → Prop)
    (hentry : ∀ (J : Cont ts), (∀ st, Inv st → J (proj st) m) →
      wp Γ Q X (entry (J, ())) m)
    (hbody : ∀ (J : Cont ts) (st : α), Inv st →
      (∀ st', μ st' < μ st → Inv st' → J (proj st') m) →
      wp Γ Q X (Blocks.get (bodies (J, ())) .here (proj st)) m) :
    wp Γ Q X (.group (sig := [ts]) bodies entry) m :=
  wp_while_state proj μ (fun st m' => Inv st ∧ m' = m)
    (fun J hJ => hentry J fun st hInv => hJ st m ⟨hInv, rfl⟩)
    (fun J st _ ⟨hInv, hmEq⟩ ih =>
      hmEq ▸ hbody J st hInv fun st' hlt hInv' => ih st' m hlt ⟨hInv', rfl⟩)

/-- State-indexed loop-with-break combinator matching `wp_loop_break_group` without existential
tuple repacking on either the break continuation `B` or the loop continuation `L`. -/
theorem wp_while_break_state {Γ : Env} {rs brkTs lpTs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64}
    {outerBodies : Tup Cont [brkTs] → Blocks Val Cont rs [brkTs]}
    {innerBodies : Tup Cont [brkTs] → Tup Cont [lpTs] → Blocks Val Cont rs [lpTs]}
    {innerEntry : Tup Cont [brkTs] → Tup Cont [lpTs] → Expr Val Cont rs}
    {β α : Type _} (projBrk : β → Tup Val brkTs) (BrkPost : β → Mem 64 → Prop)
    (projLp : α → Tup Val lpTs) (μ : α → Nat) (Inv : α → Mem 64 → Prop)
    (hafter : ∀ (B : Cont brkTs) (bst : β) (m' : Mem 64), BrkPost bst m' →
      wp Γ Q X (Blocks.get (outerBodies (B, ())) .here (projBrk bst)) m')
    (hbody : ∀ (B : Cont brkTs) (L : Cont lpTs) (st : α) (m' : Mem 64),
      (∀ bst m'', BrkPost bst m'' → B (projBrk bst) m'') →
      (∀ st' m'', μ st' < μ st → Inv st' m'' → L (projLp st') m'') →
      Inv st m' →
      wp Γ Q X (Blocks.get (innerBodies (B, ()) (L, ())) .here (projLp st)) m')
    (hentry : ∀ (B : Cont brkTs) (L : Cont lpTs),
      (∀ bst m', BrkPost bst m' → B (projBrk bst) m') →
      (∀ st m', Inv st m' → L (projLp st) m') →
      wp Γ Q X (innerEntry (B, ()) (L, ())) m) :
    wp Γ Q X (.group (sig := [brkTs]) outerBodies
      (fun oJs => .group (sig := [lpTs]) (innerBodies oJs) (innerEntry oJs))) m :=
  wp_loop_break_group
    (fun xs m' => ∃ bst : β, projBrk bst = xs ∧ BrkPost bst m')
    (fun n xs m' => ∃ st : α, projLp st = xs ∧ μ st = n ∧ Inv st m')
    (fun B _ m' ⟨bst, hEq, hBrk⟩ => hEq ▸ hafter B bst m' hBrk)
    (fun B L _ _ m' hB hL ⟨st, hEq, hμ, hInv⟩ =>
      hEq ▸ hbody B L st m'
        (fun bst m'' hBrk => hB (projBrk bst) m'' ⟨bst, rfl, hBrk⟩)
        (fun st' m'' hlt hInv' => hL (μ st') (projLp st') m'' (hμ ▸ hlt) ⟨st', rfl, rfl, hInv'⟩)
        hInv)
    (fun B L hB hL =>
      hentry B L
        (fun bst m' hBrk => hB (projBrk bst) m' ⟨bst, rfl, hBrk⟩)
        (fun st m' hInv => hL (μ st) (projLp st) m' ⟨st, rfl, rfl, hInv⟩))

/-! ## Jump helpers -/

/-- Transport a continuation predicate along a tuple equality `xs = proj st`. -/
theorem cont_of_eq {ts : List Ty} {J : Cont ts} {α : Type _} {proj : α → Tup Val ts}
    {xs : Tup Val ts} {m : Mem 64} (st : α) (h : xs = proj st) (hJ : J (proj st) m) :
    J xs m :=
  h ▸ hJ

/-- Discharge a `.jump J args` goal via `vals args = proj st`. -/
theorem wp_jump_state {Γ : Env} {rs ts : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {J : Cont ts} {args : Tup (Arg Val) ts} {α : Type _} {proj : α → Tup Val ts}
    (st : α) (h : vals args = proj st) (hJ : J (proj st) m) :
    wp Γ Q X (.jump J args) m :=
  show J (vals args) m from h ▸ hJ

end ControlComb

end LeanQbe.T
