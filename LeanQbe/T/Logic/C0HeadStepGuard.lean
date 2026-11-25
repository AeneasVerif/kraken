module

public import LeanQbe.T.Logic.Rules

/-!
# `C0HeadStepGuard`: Guard-Exit Head Lemmas, `wp_while_record`, & `C0JoinTree` Combinators

Lightweight pure-logic (`Rules`-only) extensions for `C0HeadStep`:

1. **Early-return / guard head lemmas (`LeanQbe.T.C0HeadStep.head_wp_guard_*`)**:
   Single-step lemmas for `Expr.jnz c (.ret ...)` / `(.exit ...)` / `(.jump ...)` guard chains.
2. **Record-state while-loop combinators (`wp_while_record*`, `wp_jump_record`)**:
   Arbitrary-signature `[ts]` structured record loop rules decoupling pure `Inv : α → Prop`,
   memory predicates `MemPred : α → Mem 64 → Prop`, and caller frame `R`.
3. **Multi-arm join & DAG combinators (`wp_join_dag`, `wp_join_multi`, `wp_join{2,3,4}`,
   `wp_join_ite`, `wp_join_seq`, `C0JoinTree`, `wp_join_tree`)**:
   Flatten nested `wp_join_group` / `jnz` decision trees and multi-block DAGs cleanly (`std3` only).
-/

set_option autoImplicit false

namespace LeanQbe.T

/-! ## 1. Early-Return Guard Head Lemmas (`LeanQbe.T.C0HeadStep`) -/

namespace C0HeadStep

public section

theorem head_wp_guard_true {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {c : Arg Val .bool} {vc : Bool} {eExit eLive : Expr Val Cont rs}
    (hc : c.val = vc) (hexit : vc = true → wp Γ Q X eExit m)
    (hlive : vc = false → wp Γ Q X eLive m) :
    wp Γ Q X (.jnz c eExit eLive) m :=
  ⟨fun h => hexit (hc ▸ h), fun h => hlive (hc ▸ h)⟩

theorem head_wp_guard_false {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {c : Arg Val .bool} {vc : Bool} {eLive eExit : Expr Val Cont rs}
    (hc : c.val = vc) (hlive : vc = true → wp Γ Q X eLive m)
    (hexit : vc = false → wp Γ Q X eExit m) :
    wp Γ Q X (.jnz c eLive eExit) m :=
  ⟨fun h => hlive (hc ▸ h), fun h => hexit (hc ▸ h)⟩

theorem head_wp_guard_ret_true {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {c : Arg Val .bool} {vc : Bool} {args : Tup (Arg Val) rs} {vs : Tup Val rs}
    {eLive : Expr Val Cont rs}
    (hc : c.val = vc) (hvs : vals args = vs) (hret : vc = true → Q vs m)
    (hlive : vc = false → wp Γ Q X eLive m) :
    wp Γ Q X (.jnz c (.ret args) eLive) m := by
  subst hc; subst hvs; exact ⟨hret, hlive⟩

theorem head_wp_guard_ret_false {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {c : Arg Val .bool} {vc : Bool} {eLive : Expr Val Cont rs} {args : Tup (Arg Val) rs}
    {vs : Tup Val rs}
    (hc : c.val = vc) (hvs : vals args = vs) (hlive : vc = true → wp Γ Q X eLive m)
    (hret : vc = false → Q vs m) :
    wp Γ Q X (.jnz c eLive (.ret args)) m := by
  subst hc; subst hvs; exact ⟨hlive, hret⟩

theorem head_wp_guard_exit_true {Γ : Env} {rs as : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {c : Arg Val .bool} {vc : Bool} {f : Sym} {args : Tup (Arg Val) as}
    {vs : Tup Val as} {eLive : Expr Val Cont rs}
    (hc : c.val = vc) (hvs : vals args = vs) (hexit : vc = true → X f as vs m)
    (hlive : vc = false → wp Γ Q X eLive m) :
    wp Γ Q X (.jnz c (.exit f args) eLive) m := by
  subst hc; subst hvs; exact ⟨hexit, hlive⟩

theorem head_wp_guard_exit_false {Γ : Env} {rs as : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {c : Arg Val .bool} {vc : Bool} {eLive : Expr Val Cont rs} {f : Sym}
    {args : Tup (Arg Val) as} {vs : Tup Val as}
    (hc : c.val = vc) (hvs : vals args = vs) (hlive : vc = true → wp Γ Q X eLive m)
    (hexit : vc = false → X f as vs m) :
    wp Γ Q X (.jnz c eLive (.exit f args)) m := by
  subst hc; subst hvs; exact ⟨hlive, hexit⟩

theorem head_wp_guard_jump_true {Γ : Env} {rs ts : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {c : Arg Val .bool} {vc : Bool} {J : Cont ts} {args : Tup (Arg Val) ts}
    {vs : Tup Val ts} {eLive : Expr Val Cont rs}
    (hc : c.val = vc) (hvs : vals args = vs) (hjump : vc = true → J vs m)
    (hlive : vc = false → wp Γ Q X eLive m) :
    wp Γ Q X (.jnz c (.jump J args) eLive) m := by
  subst hc; subst hvs; exact ⟨hjump, hlive⟩

theorem head_wp_guard_jump_false {Γ : Env} {rs ts : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {c : Arg Val .bool} {vc : Bool} {eLive : Expr Val Cont rs} {J : Cont ts}
    {args : Tup (Arg Val) ts} {vs : Tup Val ts}
    (hc : c.val = vc) (hvs : vals args = vs) (hlive : vc = true → wp Γ Q X eLive m)
    (hjump : vc = false → J vs m) :
    wp Γ Q X (.jnz c eLive (.jump J args)) m := by
  subst hc; subst hvs; exact ⟨hlive, hjump⟩

theorem head_wp_guard_skip_false {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {c : Arg Val .bool} {e₁ e₂ : Expr Val Cont rs}
    (hc : c.val = false) (hlive : wp Γ Q X e₂ m) :
    wp Γ Q X (.jnz c e₁ e₂) m :=
  ⟨fun h => Bool.noConfusion (hc.symm.trans h), fun _ => hlive⟩

theorem head_wp_guard_skip_true {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {c : Arg Val .bool} {e₁ e₂ : Expr Val Cont rs}
    (hc : c.val = true) (hlive : wp Γ Q X e₁ m) :
    wp Γ Q X (.jnz c e₁ e₂) m :=
  ⟨fun _ => hlive, fun h => Bool.noConfusion (hc.symm.trans h)⟩

end

end C0HeadStep

/-! ## 2. Record-State While-Loop Combinators (`wp_while_record*`) -/

public section

/-- Structured record-state loop rule for arbitrary signature `sig := [ts]`, separating pure
record invariant `Inv : α → Prop`, heap predicate `MemPred : α → Mem 64 → Prop`, and caller
frame `R` from loop termination measure `μ : α → Nat`. -/
theorem wp_while_record {Γ : Env} {rs ts : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {bodies : Tup Cont [ts] → Blocks Val Cont rs [ts]}
    {entry : Tup Cont [ts] → Expr Val Cont rs}
    {α : Type _} (proj : α → Tup Val ts) (μ : α → Nat)
    (Inv : α → Prop) (MemPred : α → Mem 64 → Prop) (R : Mem 64 → Prop)
    (hentry : ∀ J : Cont ts,
      (∀ st ml, Inv st → (MemPred st ⋆ R) ml → J (proj st) ml) →
      wp Γ Q X (entry (J, ())) m)
    (hbody : ∀ (J : Cont ts) (st : α) (ml : Mem 64),
      Inv st → (MemPred st ⋆ R) ml →
      (∀ st' ml', μ st' < μ st → Inv st' → (MemPred st' ⋆ R) ml' → J (proj st') ml') →
      wp Γ Q X (Blocks.get (bodies (J, ())) .here (proj st)) ml) :
    wp Γ Q X (.group (sig := [ts]) bodies entry) m := by
  refine wp_loop_group (fun n xs ml => ∃ st : α, proj st = xs ∧ μ st = n ∧ Inv st ∧
      (MemPred st ⋆ R) ml) ?_ ?_
  · intro J _ _ ml ih ⟨st, hEq, hμ, hi, hm⟩
    refine hEq ▸ hbody J st ml hi hm fun st' ml' hlt hi' hm' => ?_
    exact ih (μ st') (proj st') ml' (hμ ▸ hlt) ⟨st', rfl, rfl, hi', hm'⟩
  · intro J hJ
    exact hentry J fun st ml hi hm => hJ (μ st) (proj st) ml ⟨st, rfl, rfl, hi, hm⟩

/-- Initialized variant of `wp_while_record` taking an initial record `st₀` whose invariant and
separated heap predicate `(MemPred st₀ ⋆ R) m` hold at loop entry. -/
theorem wp_while_record_init {Γ : Env} {rs ts : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {bodies : Tup Cont [ts] → Blocks Val Cont rs [ts]}
    {entry : Tup Cont [ts] → Expr Val Cont rs}
    {α : Type _} (st₀ : α) (proj : α → Tup Val ts) (μ : α → Nat)
    (Inv : α → Prop) (MemPred : α → Mem 64 → Prop) (R : Mem 64 → Prop)
    (hinv₀ : Inv st₀) (hm₀ : (MemPred st₀ ⋆ R) m)
    (hentry : ∀ J : Cont ts,
      Inv st₀ → (MemPred st₀ ⋆ R) m →
      (∀ st ml, Inv st → (MemPred st ⋆ R) ml → J (proj st) ml) →
      wp Γ Q X (entry (J, ())) m)
    (hbody : ∀ (J : Cont ts) (st : α) (ml : Mem 64),
      Inv st → (MemPred st ⋆ R) ml →
      (∀ st' ml', μ st' < μ st → Inv st' → (MemPred st' ⋆ R) ml' → J (proj st') ml') →
      wp Γ Q X (Blocks.get (bodies (J, ())) .here (proj st)) ml) :
    wp Γ Q X (.group (sig := [ts]) bodies entry) m :=
  wp_while_record proj μ Inv MemPred R (fun J hJ => hentry J hinv₀ hm₀ hJ) hbody

/-- Single-predicate variant of `wp_while_record` when spatial and pure state are bundled into one
`Inv : α → Mem 64 → Prop`. -/
theorem wp_while_record_mem {Γ : Env} {rs ts : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {bodies : Tup Cont [ts] → Blocks Val Cont rs [ts]}
    {entry : Tup Cont [ts] → Expr Val Cont rs}
    {α : Type _} (proj : α → Tup Val ts) (μ : α → Nat) (Inv : α → Mem 64 → Prop)
    (hentry : ∀ J : Cont ts, (∀ st ml, Inv st ml → J (proj st) ml) →
      wp Γ Q X (entry (J, ())) m)
    (hbody : ∀ (J : Cont ts) (st : α) (ml : Mem 64), Inv st ml →
      (∀ st' ml', μ st' < μ st → Inv st' ml' → J (proj st') ml') →
      wp Γ Q X (Blocks.get (bodies (J, ())) .here (proj st)) ml) :
    wp Γ Q X (.group (sig := [ts]) bodies entry) m := by
  refine wp_loop_group (fun n xs ml => ∃ st : α, proj st = xs ∧ μ st = n ∧ Inv st ml) ?_ ?_
  · intro J _ _ ml ih ⟨st, hEq, hμ, hi⟩
    exact hEq ▸ hbody J st ml hi fun st' ml' hlt hi' =>
      ih (μ st') (proj st') ml' (hμ ▸ hlt) ⟨st', rfl, rfl, hi'⟩
  · intro J hJ
    exact hentry J fun st ml hi => hJ (μ st) (proj st) ml ⟨st, rfl, rfl, hi⟩

/-- Pure / read-only variant of `wp_while_record` where `Mem 64` stays identically `m`. -/
theorem wp_while_record_pure {Γ : Env} {rs ts : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {bodies : Tup Cont [ts] → Blocks Val Cont rs [ts]}
    {entry : Tup Cont [ts] → Expr Val Cont rs}
    {α : Type _} (proj : α → Tup Val ts) (μ : α → Nat) (Inv : α → Prop)
    (hentry : ∀ J : Cont ts, (∀ st, Inv st → J (proj st) m) →
      wp Γ Q X (entry (J, ())) m)
    (hbody : ∀ (J : Cont ts) (st : α), Inv st →
      (∀ st', μ st' < μ st → Inv st' → J (proj st') m) →
      wp Γ Q X (Blocks.get (bodies (J, ())) .here (proj st)) m) :
    wp Γ Q X (.group (sig := [ts]) bodies entry) m :=
  wp_while_record_mem proj μ (fun st ml => Inv st ∧ ml = m)
    (fun J hJ => hentry J fun st hi => hJ st m ⟨hi, rfl⟩)
    (fun J st _ ⟨hi, hm⟩ ih =>
      hm ▸ hbody J st hi fun st' hlt hi' => ih st' m hlt ⟨hi', rfl⟩)

/-- Record-state loop-with-break combinator matching `outerBodies`/`innerBodies` groups with
separated break and loop invariants sharing frame `R`. -/
theorem wp_while_record_break {Γ : Env} {rs brkTs lpTs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64}
    {outerBodies : Tup Cont [brkTs] → Blocks Val Cont rs [brkTs]}
    {innerBodies : Tup Cont [brkTs] → Tup Cont [lpTs] → Blocks Val Cont rs [lpTs]}
    {innerEntry : Tup Cont [brkTs] → Tup Cont [lpTs] → Expr Val Cont rs}
    {β α : Type _} (projBrk : β → Tup Val brkTs)
    (BrkInv : β → Prop) (BrkMem : β → Mem 64 → Prop)
    (projLp : α → Tup Val lpTs) (μ : α → Nat)
    (Inv : α → Prop) (MemPred : α → Mem 64 → Prop) (R : Mem 64 → Prop)
    (hafter : ∀ (B : Cont brkTs) (bst : β) (ml : Mem 64),
      BrkInv bst → (BrkMem bst ⋆ R) ml →
      wp Γ Q X (Blocks.get (outerBodies (B, ())) .here (projBrk bst)) ml)
    (hbody : ∀ (B : Cont brkTs) (L : Cont lpTs) (st : α) (ml : Mem 64),
      (∀ bst ml', BrkInv bst → (BrkMem bst ⋆ R) ml' → B (projBrk bst) ml') →
      (∀ st' ml', μ st' < μ st → Inv st' → (MemPred st' ⋆ R) ml' → L (projLp st') ml') →
      Inv st → (MemPred st ⋆ R) ml →
      wp Γ Q X (Blocks.get (innerBodies (B, ()) (L, ())) .here (projLp st)) ml)
    (hentry : ∀ (B : Cont brkTs) (L : Cont lpTs),
      (∀ bst ml', BrkInv bst → (BrkMem bst ⋆ R) ml' → B (projBrk bst) ml') →
      (∀ st ml', Inv st → (MemPred st ⋆ R) ml' → L (projLp st) ml') →
      wp Γ Q X (innerEntry (B, ()) (L, ())) m) :
    wp Γ Q X (.group (sig := [brkTs]) outerBodies
      (fun oJs => .group (sig := [lpTs]) (innerBodies oJs) (innerEntry oJs))) m :=
  wp_join_group (fun xs ml => ∃ bst : β, projBrk bst = xs ∧ BrkInv bst ∧ (BrkMem bst ⋆ R) ml)
    (fun B _ ml ⟨bst, hEq, hbi, hbm⟩ => hEq ▸ hafter B bst ml hbi hbm)
    fun B hB =>
      wp_while_record projLp μ Inv MemPred R
        (fun L hL => hentry B L (fun bst _ml hbi hbm => hB _ _ ⟨bst, rfl, hbi, hbm⟩) hL)
        fun L st ml hi hm ih =>
          hbody B L st ml (fun bst _ml hbi hbm => hB _ _ ⟨bst, rfl, hbi, hbm⟩) ih hi hm

/-- Discharge a `.jump J args` obligation into a `wp_while_record` continuation hypothesis. -/
theorem wp_jump_record {Γ : Env} {rs ts : List Ty} {Q : Post rs} {X : XPost} {ml : Mem 64}
    {J : Cont ts} {args : Tup (Arg Val) ts} {α : Type _} {proj : α → Tup Val ts}
    {Inv : α → Prop} {MemPred : α → Mem 64 → Prop} {R : Mem 64 → Prop}
    (st : α) (hargs : vals args = proj st) (hi : Inv st) (hm : (MemPred st ⋆ R) ml)
    (hJ : ∀ st' ml', Inv st' → (MemPred st' ⋆ R) ml' → J (proj st') ml') :
    wp Γ Q X (.jump J args) ml :=
  show J (vals args) ml from hargs ▸ hJ st ml hi hm

/-! ## 3. Multi-Arm & `C0JoinTree` Join Combinators -/

/-- General DAG join combinator over arbitrary block list `sig : List (List Ty)` with acyclic
block rank `rank`. Earlier/lower-ranked blocks become available as continuations in higher-ranked
blocks without manually nesting `wp_join_group`. -/
theorem wp_join_dag {Γ : Env} {rs : List Ty} {sig : List (List Ty)} {Q : Post rs} {X : XPost}
    {m : Mem 64} {bodies : Tup Cont sig → Blocks Val Cont rs sig}
    {entry : Tup Cont sig → Expr Val Cont rs}
    (Specs : Tup Cont sig) (rank : ∀ {ts}, Member ts sig → Nat)
    (hblocks : ∀ (Js : Tup Cont sig) {ts} (i : Member ts sig),
      (∀ {ts'} (j : Member ts' sig), rank j < rank i →
        ∀ xs' ml', Specs.get j xs' ml' → Js.get j xs' ml') →
      ∀ xs ml, Specs.get i xs ml →
        wp Γ Q X (Blocks.get (bodies Js) i xs) ml)
    (hentry : ∀ (Js : Tup Cont sig),
      (∀ {ts} (i : Member ts sig) xs ml, Specs.get i xs ml → Js.get i xs ml) →
      wp Γ Q X (entry Js) m) :
    wp Γ Q X (.group (sig := sig) bodies entry) m := by
  simp only [wp]
  intro Js hc
  rw [closed_iff] at hc
  refine hentry Js ?_
  suffices hrec : ∀ r {ts} (i : Member ts sig), rank i = r →
      ∀ xs ml, Specs.get i xs ml → Js.get i xs ml from
    fun {ts} i xs ml hs => hrec (rank i) i rfl xs ml hs
  intro r
  induction r using Nat.strongRecOn with
  | _ r ih =>
    intro ts i hri xs ml hs
    refine hc i xs ml (hblocks Js i ?_ xs ml hs)
    intro ts' j hlt xs' ml' hs'
    exact ih (rank j) (hri ▸ hlt) j rfl xs' ml' hs'

/-- Independent multi-block join rule (all blocks in `sig` mutually independent, e.g. join arms
returning or exiting independently). -/
theorem wp_join_multi {Γ : Env} {rs : List Ty} {sig : List (List Ty)} {Q : Post rs} {X : XPost}
    {m : Mem 64} {bodies : Tup Cont sig → Blocks Val Cont rs sig}
    {entry : Tup Cont sig → Expr Val Cont rs}
    (Specs : Tup Cont sig)
    (hblocks : ∀ (Js : Tup Cont sig) {ts} (i : Member ts sig) xs ml,
      Specs.get i xs ml → wp Γ Q X (Blocks.get (bodies Js) i xs) ml)
    (hentry : ∀ (Js : Tup Cont sig),
      (∀ {ts} (i : Member ts sig) xs ml, Specs.get i xs ml → Js.get i xs ml) →
      wp Γ Q X (entry Js) m) :
    wp Γ Q X (.group (sig := sig) bodies entry) m :=
  wp_join_dag Specs (fun _ => 0)
    (fun Js {_} i _ xs ml hs => hblocks Js i xs ml hs) hentry

/-- Specialized 2-block join rule (`sig := [ts₁, ts₂]`), eliminating `Member` unpacking. -/
theorem wp_join2 {Γ : Env} {rs ts₁ ts₂ : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {bodies : Tup Cont [ts₁, ts₂] → Blocks Val Cont rs [ts₁, ts₂]}
    {entry : Tup Cont [ts₁, ts₂] → Expr Val Cont rs}
    (P₁ : Cont ts₁) (P₂ : Cont ts₂)
    (hb₁ : ∀ (J₁ : Cont ts₁) (J₂ : Cont ts₂) xs ml, P₁ xs ml →
      wp Γ Q X (Blocks.get (bodies (J₁, J₂, ())) .here xs) ml)
    (hb₂ : ∀ (J₁ : Cont ts₁) (J₂ : Cont ts₂) xs ml, P₂ xs ml →
      wp Γ Q X (Blocks.get (bodies (J₁, J₂, ())) (.there .here) xs) ml)
    (hentry : ∀ (J₁ : Cont ts₁) (J₂ : Cont ts₂),
      (∀ xs ml, P₁ xs ml → J₁ xs ml) → (∀ xs ml, P₂ xs ml → J₂ xs ml) →
      wp Γ Q X (entry (J₁, J₂, ())) m) :
    wp Γ Q X (.group (sig := [ts₁, ts₂]) bodies entry) m := by
  refine wp_join_multi (P₁, P₂, ()) ?_ ?_
  · rintro ⟨J₁, J₂, ⟨⟩⟩ ts i xs ml hs
    cases i with
    | here => exact hb₁ J₁ J₂ xs ml hs
    | there i =>
      cases i with
      | here => exact hb₂ J₁ J₂ xs ml hs
      | there i => cases i
  · rintro ⟨J₁, J₂, ⟨⟩⟩ hJs
    exact hentry J₁ J₂ (hJs .here) (hJs (.there .here))

/-- Specialized 3-block join rule (`sig := [ts₁, ts₂, ts₃]`), eliminating `Member` unpacking. -/
theorem wp_join3 {Γ : Env} {rs ts₁ ts₂ ts₃ : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {bodies : Tup Cont [ts₁, ts₂, ts₃] → Blocks Val Cont rs [ts₁, ts₂, ts₃]}
    {entry : Tup Cont [ts₁, ts₂, ts₃] → Expr Val Cont rs}
    (P₁ : Cont ts₁) (P₂ : Cont ts₂) (P₃ : Cont ts₃)
    (hb₁ : ∀ (J₁ : Cont ts₁) (J₂ : Cont ts₂) (J₃ : Cont ts₃) xs ml, P₁ xs ml →
      wp Γ Q X (Blocks.get (bodies (J₁, J₂, J₃, ())) .here xs) ml)
    (hb₂ : ∀ (J₁ : Cont ts₁) (J₂ : Cont ts₂) (J₃ : Cont ts₃) xs ml, P₂ xs ml →
      wp Γ Q X (Blocks.get (bodies (J₁, J₂, J₃, ())) (.there .here) xs) ml)
    (hb₃ : ∀ (J₁ : Cont ts₁) (J₂ : Cont ts₂) (J₃ : Cont ts₃) xs ml, P₃ xs ml →
      wp Γ Q X (Blocks.get (bodies (J₁, J₂, J₃, ())) (.there (.there .here)) xs) ml)
    (hentry : ∀ (J₁ : Cont ts₁) (J₂ : Cont ts₂) (J₃ : Cont ts₃),
      (∀ xs ml, P₁ xs ml → J₁ xs ml) → (∀ xs ml, P₂ xs ml → J₂ xs ml) →
      (∀ xs ml, P₃ xs ml → J₃ xs ml) →
      wp Γ Q X (entry (J₁, J₂, J₃, ())) m) :
    wp Γ Q X (.group (sig := [ts₁, ts₂, ts₃]) bodies entry) m := by
  refine wp_join_multi (P₁, P₂, P₃, ()) ?_ ?_
  · rintro ⟨J₁, J₂, J₃, ⟨⟩⟩ ts i xs ml hs
    cases i with
    | here => exact hb₁ J₁ J₂ J₃ xs ml hs
    | there i =>
      cases i with
      | here => exact hb₂ J₁ J₂ J₃ xs ml hs
      | there i =>
        cases i with
        | here => exact hb₃ J₁ J₂ J₃ xs ml hs
        | there i => cases i
  · rintro ⟨J₁, J₂, J₃, ⟨⟩⟩ hJs
    exact hentry J₁ J₂ J₃ (hJs .here) (hJs (.there .here)) (hJs (.there (.there .here)))

/-- Specialized 4-block join rule (`sig := [ts₁, ts₂, ts₃, ts₄]`). -/
theorem wp_join4 {Γ : Env} {rs ts₁ ts₂ ts₃ ts₄ : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {bodies : Tup Cont [ts₁, ts₂, ts₃, ts₄] → Blocks Val Cont rs [ts₁, ts₂, ts₃, ts₄]}
    {entry : Tup Cont [ts₁, ts₂, ts₃, ts₄] → Expr Val Cont rs}
    (P₁ : Cont ts₁) (P₂ : Cont ts₂) (P₃ : Cont ts₃) (P₄ : Cont ts₄)
    (hb₁ : ∀ J₁ J₂ J₃ J₄ xs ml, P₁ xs ml →
      wp Γ Q X (Blocks.get (bodies (J₁, J₂, J₃, J₄, ())) .here xs) ml)
    (hb₂ : ∀ J₁ J₂ J₃ J₄ xs ml, P₂ xs ml →
      wp Γ Q X (Blocks.get (bodies (J₁, J₂, J₃, J₄, ())) (.there .here) xs) ml)
    (hb₃ : ∀ J₁ J₂ J₃ J₄ xs ml, P₃ xs ml →
      wp Γ Q X (Blocks.get (bodies (J₁, J₂, J₃, J₄, ())) (.there (.there .here)) xs) ml)
    (hb₄ : ∀ J₁ J₂ J₃ J₄ xs ml, P₄ xs ml →
      wp Γ Q X (Blocks.get (bodies (J₁, J₂, J₃, J₄, ()))
        (.there (.there (.there .here))) xs) ml)
    (hentry : ∀ J₁ J₂ J₃ J₄,
      (∀ xs ml, P₁ xs ml → J₁ xs ml) → (∀ xs ml, P₂ xs ml → J₂ xs ml) →
      (∀ xs ml, P₃ xs ml → J₃ xs ml) → (∀ xs ml, P₄ xs ml → J₄ xs ml) →
      wp Γ Q X (entry (J₁, J₂, J₃, J₄, ())) m) :
    wp Γ Q X (.group (sig := [ts₁, ts₂, ts₃, ts₄]) bodies entry) m := by
  refine wp_join_multi (P₁, P₂, P₃, P₄, ()) ?_ ?_
  · rintro ⟨J₁, J₂, J₃, J₄, ⟨⟩⟩ ts i xs ml hs
    cases i with
    | here => exact hb₁ J₁ J₂ J₃ J₄ xs ml hs
    | there i =>
      cases i with
      | here => exact hb₂ J₁ J₂ J₃ J₄ xs ml hs
      | there i =>
        cases i with
        | here => exact hb₃ J₁ J₂ J₃ J₄ xs ml hs
        | there i =>
          cases i with
          | here => exact hb₄ J₁ J₂ J₃ J₄ xs ml hs
          | there i => cases i
  · rintro ⟨J₁, J₂, J₃, J₄, ⟨⟩⟩ hJs
    exact hentry J₁ J₂ J₃ J₄ (hJs .here) (hJs (.there .here))
      (hJs (.there (.there .here))) (hJs (.there (.there (.there .here))))

/-- Direct if-then-else join combinator matching `Expr.group (fun Js => .jnz c ...)` without
manual `wp_join_group` + branch unfolding boilerplate. -/
theorem wp_join_ite {Γ : Env} {rs ts : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {bodies : Tup Cont [ts] → Blocks Val Cont rs [ts]}
    {e₁ e₂ : Tup Cont [ts] → Expr Val Cont rs} {c : Arg Val .bool}
    (P : Tup Val ts → Mem 64 → Prop)
    (hbody : ∀ (J : Cont ts) xs ml, P xs ml →
      wp Γ Q X (Blocks.get (bodies (J, ())) .here xs) ml)
    (ht : ∀ (J : Cont ts), (∀ xs ml, P xs ml → J xs ml) →
      c.val = true → wp Γ Q X (e₁ (J, ())) m)
    (hf : ∀ (J : Cont ts), (∀ xs ml, P xs ml → J xs ml) →
      c.val = false → wp Γ Q X (e₂ (J, ())) m) :
    wp Γ Q X (.group (sig := [ts]) bodies (fun Js => .jnz c (e₁ Js) (e₂ Js))) m :=
  wp_join_group P hbody fun J hJ => ⟨fun hc => ht J hJ hc, fun hc => hf J hJ hc⟩

/-- Sequential 2-join flattening combinator: when the join body of the first `Expr.group` begins
immediately with a second `Expr.group` (two consecutive C0 `if` blocks), discharges both joins
declaratively with postconditions `P₁` and `P₂`. -/
theorem wp_join_seq {Γ : Env} {rs ts₁ ts₂ : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {b₁ : Tup Cont [ts₁] → Tup Val ts₁ → Tup Cont [ts₂] → Blocks Val Cont rs [ts₂]}
    {k₁ : Tup Cont [ts₁] → Tup Val ts₁ → Tup Cont [ts₂] → Expr Val Cont rs}
    {entry₁ : Tup Cont [ts₁] → Expr Val Cont rs}
    (P₁ : Tup Val ts₁ → Mem 64 → Prop)
    (P₂ : Tup Val ts₁ → Tup Val ts₂ → Mem 64 → Prop)
    (htail : ∀ (J₁ : Cont ts₁) (xs₁ : Tup Val ts₁) (J₂ : Cont ts₂) xs₂ m₂, P₂ xs₁ xs₂ m₂ →
      wp Γ Q X (Blocks.get (b₁ (J₁, ()) xs₁ (J₂, ())) .here xs₂) m₂)
    (hmid : ∀ (J₁ : Cont ts₁) (J₂ : Cont ts₂) xs₁ m₁,
      (∀ xs₂ m₂, P₂ xs₁ xs₂ m₂ → J₂ xs₂ m₂) → P₁ xs₁ m₁ →
      wp Γ Q X (k₁ (J₁, ()) xs₁ (J₂, ())) m₁)
    (hentry₁ : ∀ (J₁ : Cont ts₁), (∀ xs₁ m₁, P₁ xs₁ m₁ → J₁ xs₁ m₁) →
      wp Γ Q X (entry₁ (J₁, ())) m) :
    wp Γ Q X (.group (sig := [ts₁])
      (fun oJs => Blocks.cons (fun xs₁ => .group (sig := [ts₂]) (b₁ oJs xs₁) (k₁ oJs xs₁)) .nil)
      entry₁) m :=
  wp_join_group P₁
    (fun J₁ xs₁ m₁ hp₁ => by
      simp only [Blocks.get_here]
      exact wp_join_group (P₂ xs₁) (fun J₂ => htail J₁ xs₁ J₂)
        fun J₂ hJ₂ => hmid J₁ J₂ xs₁ m₁ hJ₂ hp₁)
    hentry₁

end

/-! ### Declarative `C0JoinTree` Decision-Tree Combinator -/

@[expose] public section

/-- Declarative multi-arm join tree for `Expr.group (sig := [ts])` capturing arbitrary-depth
`jnz` branches, inner `Expr.group` joins, `.jump`, `.ret`, `.exit`, and custom `leaf` steps
sharing join invariant `P : Tup Val ts → Mem 64 → Prop`. -/
inductive C0JoinTree (Γ : Env) {rs ts : List Ty} (Q : Post rs) (X : XPost)
    (P : Tup Val ts → Mem 64 → Prop) (J : Cont ts) :
    Expr Val Cont rs → Mem 64 → Prop where
  | leaf {e : Expr Val Cont rs} {ml : Mem 64}
      (h : (∀ xs m', P xs m' → J xs m') → wp Γ Q X e ml) :
      C0JoinTree Γ Q X P J e ml
  | jump {args : Tup (Arg Val) ts} {ml : Mem 64}
      (hp : P (vals args) ml) :
      C0JoinTree Γ Q X P J (.jump J args) ml
  | ret {args : Tup (Arg Val) rs} {ml : Mem 64}
      (hq : Q (vals args) ml) :
      C0JoinTree Γ Q X P J (.ret args) ml
  | exit {as : List Ty} {f : Sym} {args : Tup (Arg Val) as} {ml : Mem 64}
      (hx : X f as (vals args) ml) :
      C0JoinTree Γ Q X P J (.exit f args) ml
  | branch {c : Arg Val .bool} {e₁ e₂ : Expr Val Cont rs} {ml : Mem 64}
      (ht : c.val = true → C0JoinTree Γ Q X P J e₁ ml)
      (hf : c.val = false → C0JoinTree Γ Q X P J e₂ ml) :
      C0JoinTree Γ Q X P J (.jnz c e₁ e₂) ml
  | group {ts' : List Ty} {bodies' : Tup Cont [ts'] → Blocks Val Cont rs [ts']}
      {entry' : Tup Cont [ts'] → Expr Val Cont rs} {ml : Mem 64}
      (P' : Tup Val ts' → Mem 64 → Prop)
      (hbody' : ∀ (J' : Cont ts') xs m', P' xs m' →
        C0JoinTree Γ Q X P J (Blocks.get (bodies' (J', ())) .here xs) m')
      (hentry' : ∀ (J' : Cont ts'), (∀ xs m', P' xs m' → J' xs m') →
        C0JoinTree Γ Q X P J (entry' (J', ())) ml) :
      C0JoinTree Γ Q X P J (.group (sig := [ts']) bodies' entry') ml

end

public section

theorem C0JoinTree.wp {Γ : Env} {rs ts : List Ty} {Q : Post rs} {X : XPost}
    {P : Tup Val ts → Mem 64 → Prop} {J : Cont ts} {e : Expr Val Cont rs} {m : Mem 64}
    (hJ : ∀ xs m', P xs m' → J xs m') (htree : C0JoinTree Γ Q X P J e m) :
    LeanQbe.T.wp Γ Q X e m := by
  induction htree with
  | leaf h => exact h hJ
  | jump hp => exact hJ _ _ hp
  | ret hq => exact hq
  | exit hx => exact hx
  | branch _ _ iht ihf => exact ⟨fun hc => iht hc, fun hc => ihf hc⟩
  | group P' _ _ ihbody ihentry =>
    exact wp_join_group P' ihbody ihentry

/-- Flatten arbitrary multi-arm / nested `Expr.group` joins into a declarative `C0JoinTree`. -/
theorem wp_join_tree {Γ : Env} {rs ts : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {bodies : Tup Cont [ts] → Blocks Val Cont rs [ts]}
    {entry : Tup Cont [ts] → Expr Val Cont rs}
    (P : Tup Val ts → Mem 64 → Prop)
    (hbody : ∀ (J : Cont ts) xs ml, P xs ml →
      wp Γ Q X (Blocks.get (bodies (J, ())) .here xs) ml)
    (hentry : ∀ (J : Cont ts), C0JoinTree Γ Q X P J (entry (J, ())) m) :
    wp Γ Q X (.group (sig := [ts]) bodies entry) m :=
  wp_join_group P hbody fun J hJ => C0JoinTree.wp hJ (hentry J)

end

end LeanQbe.T
