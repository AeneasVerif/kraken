module

public import LeanQbe.T.IL

/-!
# Well-formedness: relational equivalence of two PHOAS instantiations

`Wf G D e₁ e₂` (mutually with `WfB G D bs₁ bs₂`) relates two instantiations
`e₁ : Expr V₁ L₁ rs` and `e₂ : Expr V₂ L₂ rs` under typed value context `G : Ctx V₁ V₂`
and typed label context `D : Ctx L₁ L₂` (newest binders first).

A closed function `f : Func as rs` is well-formed (`Func.Wf f`) when every two instantiations
at related parameter tuples `xs₁ : Tup V₁ as`, `xs₂ : Tup V₂ as` are `Wf`-related under
`Tup.zip xs₁ xs₂` and `[]`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

section
variable {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type}

/-- Two operands are related iff they are the same immediate or paired variables in `G`. -/
inductive ArgRel (G : Ctx V₁ V₂) : (t : Ty) → Arg V₁ t → Arg V₂ t → Prop
  | var {t : Ty} {v₁ : V₁ t} {v₂ : V₂ t} : ⟨t, v₁, v₂⟩ ∈ G → ArgRel G t (.var v₁) (.var v₂)
  | imm {t : Ty} (c : Val t) : ArgRel G t (.imm c) (.imm c)

/-- Two operations are related iff they carry the same `OpCode` and pointwise `ArgRel` operands. -/
inductive OpRel (G : Ctx V₁ V₂) : {rs : List Ty} → Op V₁ rs → Op V₂ rs → Prop
  | mk {sig rs : List Ty} (code : OpCode sig rs)
      {args₁ : Tup (Arg V₁) sig} {args₂ : Tup (Arg V₂) sig} :
      TRel (ArgRel G) args₁ args₂ → OpRel G ⟨code, args₁⟩ ⟨code, args₂⟩

mutual
/-- Two typed expressions are related under value context `G` and label context `D`. -/
inductive Wf {rs : List Ty} : Ctx V₁ V₂ → Ctx L₁ L₂ → Expr V₁ L₁ rs → Expr V₂ L₂ rs → Prop
  | let_ {G D ts op₁ op₂ k₁ k₂} :
      OpRel G op₁ op₂ →
      (∀ (xs₁ : Tup V₁ ts) (xs₂ : Tup V₂ ts),
        Wf (Tup.zip xs₁ xs₂ ++ G) D (k₁ xs₁) (k₂ xs₂)) →
      Wf G D (.let_ (ts := ts) op₁ k₁) (.let_ op₂ k₂)
  | load {G D} (t : Ty) {a₁ a₂ k₁ k₂} :
      ArgRel G i64 a₁ a₂ →
      (∀ (v₁ : V₁ t) (v₂ : V₂ t), Wf (⟨t, v₁, v₂⟩ :: G) D (k₁ v₁) (k₂ v₂)) →
      Wf G D (.load t a₁ k₁) (.load t a₂ k₂)
  | store {G D t v₁ v₂ a₁ a₂ k₁ k₂} :
      ArgRel G t v₁ v₂ → ArgRel G i64 a₁ a₂ → Wf G D k₁ k₂ →
      Wf G D (.store (t := t) v₁ a₁ k₁) (.store v₂ a₂ k₂)
  | call {G D} (f : Sym) {as bs args₁ args₂ k₁ k₂} :
      TRel (ArgRel G) args₁ args₂ →
      (∀ (xs₁ : Tup V₁ bs) (xs₂ : Tup V₂ bs),
        Wf (Tup.zip xs₁ xs₂ ++ G) D (k₁ xs₁) (k₂ xs₂)) →
      Wf G D (.call f (as := as) (bs := bs) args₁ k₁) (.call f args₂ k₂)
  | jnz {G D c₁ c₂ t₁ t₂ e₁ e₂} :
      ArgRel G .bool c₁ c₂ → Wf G D t₁ t₂ → Wf G D e₁ e₂ →
      Wf G D (.jnz c₁ t₁ e₁) (.jnz c₂ t₂ e₂)
  | jump {G D ts j₁ j₂ args₁ args₂} :
      ⟨ts, j₁, j₂⟩ ∈ D → TRel (ArgRel G) args₁ args₂ →
      Wf G D (.jump j₁ args₁) (.jump j₂ args₂)
  | ret {G D vs₁ vs₂} :
      TRel (ArgRel G) vs₁ vs₂ →
      Wf G D (.ret vs₁) (.ret vs₂)
  | exit {G D} (f : Sym) {as args₁ args₂} :
      TRel (ArgRel G) args₁ args₂ →
      Wf G D (.exit f (as := as) args₁) (.exit f args₂)
  | hlt {G D} : Wf G D .hlt .hlt
  | group {G D sig b₁ b₂ k₁ k₂} :
      (∀ (Js₁ : Tup L₁ sig) (Js₂ : Tup L₂ sig),
        WfB G (Tup.zip Js₁ Js₂ ++ D) (b₁ Js₁) (b₂ Js₂)) →
      (∀ (Js₁ : Tup L₁ sig) (Js₂ : Tup L₂ sig),
        Wf G (Tup.zip Js₁ Js₂ ++ D) (k₁ Js₁) (k₂ Js₂)) →
      Wf G D (.group (sig := sig) b₁ k₁) (.group b₂ k₂)

/-- Two block lists of the same signature `sig` are related under `G` and `D`. -/
inductive WfB {rs : List Ty} : Ctx V₁ V₂ → Ctx L₁ L₂ → {sig : List (List Ty)} →
    Blocks V₁ L₁ rs sig → Blocks V₂ L₂ rs sig → Prop
  | nil {G D} : WfB G D .nil .nil
  | cons {G D ts sig b₁ b₂} {bs₁ : Blocks V₁ L₁ rs sig} {bs₂ : Blocks V₂ L₂ rs sig} :
      (∀ (xs₁ : Tup V₁ ts) (xs₂ : Tup V₂ ts),
        Wf (Tup.zip xs₁ xs₂ ++ G) D (b₁ xs₁) (b₂ xs₂)) →
      WfB G D bs₁ bs₂ →
      WfB G D (.cons b₁ bs₁) (.cons b₂ bs₂)
end

end

/-- Every two instantiations of a closed function at related arguments are `Wf`-related. -/
def Func.Wf {as rs : List Ty} (f : Func as rs) : Prop :=
  ∀ (V₁ V₂ : Ty → Type) (L₁ L₂ : List Ty → Type) (xs₁ : Tup V₁ as) (xs₂ : Tup V₂ as),
    _root_.LeanQbe.T.Wf (Tup.zip xs₁ xs₂) ([] : Ctx L₁ L₂) (f V₁ L₁ xs₁) (f V₂ L₂ xs₂)

/-- A named function is well-formed when its body is well-formed. -/
def Fn.Wf (fn : Fn) : Prop := Func.Wf fn.body

/-- Helper for `t_wf_tac`: `TRel` at `[]` without tuple pattern-matching unification issues. -/
theorem TRel.nil' {α : Type} {f g : α → Type} {R : ∀ a, f a → g a → Prop}
    {xs : Tup f []} {ys : Tup g []} : TRel R xs ys := .nil

/-- Helper for `t_wf_tac`: `TRel` at `a :: as` avoiding `Prod.mk` type-index unification issues. -/
theorem TRel.cons' {α : Type} {f g : α → Type} {R : ∀ a, f a → g a → Prop}
    {a : α} {as : List α} {xs : Tup f (a :: as)} {ys : Tup g (a :: as)}
    (hx : R a xs.1 ys.1) (hxs : TRel R xs.2 ys.2) : TRel R xs ys := .cons hx hxs

/-- Syntax-directed tactic for small or type-parametric `Func.Wf` goals (for concrete closed
functions, prefer `t_wf_reify` from `LeanQbe.T.FlatLemmas`). -/
scoped macro "t_wf_tac" : tactic =>
  `(tactic| (
    (try intro _ _ _ _ _ _)
    repeat (
      first
        | intro _ _
        | exact TRel.nil'
        | apply TRel.cons'
        | ((try dsimp only); exact ArgRel.imm _)
        | ((try dsimp only); refine ArgRel.var ?_; simp [Tup.zip])
        | (focus (simp [Tup.zip]; done))
        | refine Wf.let_ ?_ ?_
        | refine Wf.load _ ?_ ?_
        | refine Wf.store ?_ ?_ ?_
        | refine Wf.call _ ?_ ?_
        | refine Wf.jnz ?_ ?_ ?_
        | refine Wf.jump ?_ ?_
        | refine Wf.ret ?_
        | refine Wf.exit _ ?_
        | exact Wf.hlt
        | refine Wf.group ?_ ?_
        | exact WfB.nil
        | refine WfB.cons ?_ ?_
        | refine OpRel.mk _ ?_)))

end LeanQbe.T
