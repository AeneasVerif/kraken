module

public import LeanQbe.T.LegalWfBaseLemmas

/-!
# Legalization well-formedness preservation (`Func.legal_wf`, Part 2)
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

section LegalWf

variable (target : LegalTarget)

theorem legalUnaryTree_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    (mkCode : (u : Ty) → OpCode [u] [u]) (vecSupported : (u : Ty) → Bool)
    {onBool₁ : Arg V₁ .bool → (Arg V₁ .bool → Expr V₁ L₁ rs) → Expr V₁ L₁ rs}
    {onBool₂ : Arg V₂ .bool → (Arg V₂ .bool → Expr V₂ L₂ rs) → Expr V₂ L₂ rs}
    {onBits₁ : (n : Nat) → Arg V₁ (.bits (target.widenWidth n)) →
      (Arg V₁ (.bits (target.widenWidth n)) → Expr V₁ L₁ rs) → Expr V₁ L₁ rs}
    {onBits₂ : (n : Nat) → Arg V₂ (.bits (target.widenWidth n)) →
      (Arg V₂ (.bits (target.widenWidth n)) → Expr V₂ L₂ rs) → Expr V₂ L₂ rs}
    {onFloat₁ : (f : Fmt) → Arg V₁ (.float f) → (Arg V₁ (.float f) → Expr V₁ L₁ rs) → Expr V₁ L₁ rs}
    {onFloat₂ : (f : Fmt) → Arg V₂ (.float f) → (Arg V₂ (.float f) → Expr V₂ L₂ rs) → Expr V₂ L₂ rs}
    (hb : ∀ {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {x₁ x₂ cont₁ cont₂}, ArgRel G .bool x₁ x₂ →
      (∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, ArgRel G' .bool y₁ y₂ → Wf G' D (cont₁ y₁) (cont₂ y₂)) →
      Wf G D (onBool₁ x₁ cont₁) (onBool₂ x₂ cont₂))
    (hn : ∀ (n : Nat) {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {x₁ x₂ cont₁ cont₂},
      ArgRel G (.bits (target.widenWidth n)) x₁ x₂ →
      (∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, ArgRel G' (.bits (target.widenWidth n)) y₁ y₂ → Wf G' D (cont₁ y₁) (cont₂ y₂)) →
      Wf G D (onBits₁ n x₁ cont₁) (onBits₂ n x₂ cont₂))
    (hf : ∀ (f : Fmt) {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {x₁ x₂ cont₁ cont₂},
      ArgRel G (.float f) x₁ x₂ →
      (∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, ArgRel G' (.float f) y₁ y₂ → Wf G' D (cont₁ y₁) (cont₂ y₂)) →
      Wf G D (onFloat₁ f x₁ cont₁) (onFloat₂ f x₂ cont₂)) :
    ∀ (t : Ty) {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
      {xs₁ : Tup (Arg V₁) (target.legalTys t)} {xs₂ : Tup (Arg V₂) (target.legalTys t)},
      TRel (ArgRel G) xs₁ xs₂ →
      ∀ {k₁ : Tup (Arg V₁) (target.legalTys t) → Expr V₁ L₁ rs}
        {k₂ : Tup (Arg V₂) (target.legalTys t) → Expr V₂ L₂ rs},
      (∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, TRel (ArgRel G') y₁ y₂ → Wf G' D (k₁ y₁) (k₂ y₂)) →
      Wf G D (legalUnaryTree target mkCode vecSupported onBool₁ onBits₁ onFloat₁ t xs₁ k₁)
             (legalUnaryTree target mkCode vecSupported onBool₂ onBits₂ onFloat₂ t xs₂ k₂)
  | .bool, _, _, xs₁, xs₂, hxs, _, _, hk => by
    rcases xs₁ with ⟨x₁, ⟨⟩⟩; rcases xs₂ with ⟨x₂, ⟨⟩⟩
    cases hxs with | cons hx _ =>
    exact hb hx fun hG' y₁ y₂ hy => hk hG' _ _ (TRel.single hy)
  | .bits n, _, _, xs₁, xs₂, hxs, _, _, hk => by
    rcases xs₁ with ⟨x₁, ⟨⟩⟩; rcases xs₂ with ⟨x₂, ⟨⟩⟩
    cases hxs with | cons hx _ =>
    exact hn n hx fun hG' y₁ y₂ hy => hk hG' _ _ (TRel.single hy)
  | .float f, _, _, xs₁, xs₂, hxs, _, _, hk => by
    rcases xs₁ with ⟨x₁, ⟨⟩⟩; rcases xs₂ with ⟨x₂, ⟨⟩⟩
    cases hxs with | cons hx _ =>
    exact hf f hx fun hG' y₁ y₂ hy => hk hG' _ _ (TRel.single hy)
  | .pair t1 t2, G, D, xs₁, xs₂, hxs, k₁, k₂, hk => by
    simp only [legalUnaryTree]
    split
    · next h =>
      obtain ⟨h1, _⟩ := TRel.cons_iff.1 (packedToTup_rel h hxs)
      split
      · exact Wf.let1 (mkCode (.pair t1 t2)) h1 fun hG' r₁ r₂ hr =>
          hk hG' _ _ (tupToPacked_rel h (.cons hr .nil))
      · refine splitLegalToLeaves_wf target (.pair t1 t2) hxs fun hG1 fx₁ fx₂ hfx => ?_
        have hgoS : ∀ (u : Ty) {G' : Ctx V₁ V₂} {fxu₁ : Tup (Arg V₁) (target.leafTys u)} {fxu₂ : Tup (Arg V₂) (target.leafTys u)},
            TRel (ArgRel G') fxu₁ fxu₂ →
            ∀ {c₁ : Tup (Arg V₁) (target.leafTys u) → Expr V₁ L₁ rs}
              {c₂ : Tup (Arg V₂) (target.leafTys u) → Expr V₂ L₂ rs},
            (∀ {G''}, (∀ p ∈ G', p ∈ G'') → ∀ y₁ y₂, TRel (ArgRel G'') y₁ y₂ → Wf G'' D (c₁ y₁) (c₂ y₂)) →
            Wf G' D
              (legalUnaryTree.goS target onBool₁ onBits₁ onFloat₁ u fxu₁ c₁)
              (legalUnaryTree.goS target onBool₂ onBits₂ onFloat₂ u fxu₂ c₂) := by
          intro u
          induction u with
          | bool =>
            intro G' (_, ()) (_, ()) hfu c₁ c₂ hc; cases hfu with | cons hu _ =>
              exact hb hu fun hG' y₁ y₂ hy => hc hG' _ _ (TRel.single hy)
          | bits n =>
            intro G' xs1 xs2 hfu c₁ c₂ hc
            rcases xs1 with ⟨u1, ⟨⟩⟩; rcases xs2 with ⟨u2, ⟨⟩⟩
            cases hfu with | cons hu _ =>
              exact hn n hu fun hG' y₁ y₂ hy => hc hG' _ _ (TRel.single hy)
          | float f =>
            intro G' (_, ()) (_, ()) hfu c₁ c₂ hc; cases hfu with | cons hu _ =>
              exact hf f hu fun hG' y₁ y₂ hy => hc hG' _ _ (TRel.single hy)
          | pair u1 u2 ih1 ih2 =>
            intro G' fxu₁ fxu₂ hfu c₁ c₂ hc
            obtain ⟨hu1, hu2⟩ := TRel_tupSplit hfu
            exact ih1 hu1 fun hGa r1₁ r1₂ hr1 =>
              ih2 (TRel_argRel_weaken' hGa hu2) fun hGb r2₁ r2₂ hr2 =>
                hc (sub_trans hGa hGb) _ _ (TRel_tupAppend (TRel_argRel_weaken' hGb hr1) hr2)
        refine hgoS (.pair t1 t2) hfx fun hG2 fr₁ fr₂ hfr =>
          packLeavesToLegal_wf target (.pair t1 t2) hfr fun hG3 y₁ y₂ hy =>
            hk (sub_trans hG1 (sub_trans hG2 hG3)) y₁ y₂ hy
    · next h =>
      obtain ⟨h1, h2⟩ := TRel_tupSplit (splitToTup_rel (Bool.eq_false_iff.mpr h) hxs)
      refine legalUnaryTree_wf mkCode vecSupported hb hn hf t1 h1 fun hG1 r1₁ r1₂ hr1 =>
        legalUnaryTree_wf mkCode vecSupported hb hn hf t2 (TRel_argRel_weaken' hG1 h2) fun hG2 r2₁ r2₂ hr2 =>
          hk (sub_trans hG1 hG2) _ _
            (tupToSplit_rel (Bool.eq_false_iff.mpr h) (TRel_tupAppend (TRel_argRel_weaken' hG2 hr1) hr2))

theorem legalBswapTree_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty} :
    ∀ (t : Ty) {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
      {xs₁ : Tup (Arg V₁) (target.legalTys t)} {xs₂ : Tup (Arg V₂) (target.legalTys t)},
      TRel (ArgRel G) xs₁ xs₂ →
      ∀ {k₁ : Tup (Arg V₁) (target.legalTys t) → Expr V₁ L₁ rs}
        {k₂ : Tup (Arg V₂) (target.legalTys t) → Expr V₂ L₂ rs},
      (∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, TRel (ArgRel G') y₁ y₂ → Wf G' D (k₁ y₁) (k₂ y₂)) →
      Wf G D (legalBswapTree target t xs₁ k₁) (legalBswapTree target t xs₂ k₂) := by
  intro t G D xs₁ xs₂ hxs k₁ k₂ hk
  simp only [legalBswapTree]
  split
  · exact .hlt
  · refine legalUnaryTree_wf target .bswap (fun _ => false)
      (fun {_ _ _ _ _ _} _ _ => .hlt)
      ?_
      (fun _ {_ _ _ _ _ _} _ _ => .hlt)
      t hxs hk
    intro n G' D' x₁ x₂ c₁ c₂ hx hc
    split
    · exact hc (fun _ p => p) _ _ (.imm _)
    · split
      · exact hc (fun _ p => p) _ _ hx
      · split
        · exact Wf.let1 _ hx hc
        · split
          · exact Wf.let1 _ hx fun h1 bw₁ bw₂ hbw =>
              Wf.let2 _ hbw (.imm _) fun h2 r₁ r₂ hr =>
                hc (sub_trans h1 h2) r₁ r₂ hr
          · exact .hlt

theorem legalTernaryTree_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    (mkCode : (u : Ty) → OpCode [u, u, u] [u]) (vecSupported : (u : Ty) → Bool)
    {onBool₁ : Arg V₁ .bool → Arg V₁ .bool → Arg V₁ .bool → (Arg V₁ .bool → Expr V₁ L₁ rs) → Expr V₁ L₁ rs}
    {onBool₂ : Arg V₂ .bool → Arg V₂ .bool → Arg V₂ .bool → (Arg V₂ .bool → Expr V₂ L₂ rs) → Expr V₂ L₂ rs}
    {onBits₁ : (n : Nat) → Arg V₁ (.bits (target.widenWidth n)) → Arg V₁ (.bits (target.widenWidth n)) →
      Arg V₁ (.bits (target.widenWidth n)) → (Arg V₁ (.bits (target.widenWidth n)) → Expr V₁ L₁ rs) → Expr V₁ L₁ rs}
    {onBits₂ : (n : Nat) → Arg V₂ (.bits (target.widenWidth n)) → Arg V₂ (.bits (target.widenWidth n)) →
      Arg V₂ (.bits (target.widenWidth n)) → (Arg V₂ (.bits (target.widenWidth n)) → Expr V₂ L₂ rs) → Expr V₂ L₂ rs}
    {onFloat₁ : (f : Fmt) → Arg V₁ (.float f) → Arg V₁ (.float f) → Arg V₁ (.float f) →
      (Arg V₁ (.float f) → Expr V₁ L₁ rs) → Expr V₁ L₁ rs}
    {onFloat₂ : (f : Fmt) → Arg V₂ (.float f) → Arg V₂ (.float f) → Arg V₂ (.float f) →
      (Arg V₂ (.float f) → Expr V₂ L₂ rs) → Expr V₂ L₂ rs}
    (hb : ∀ {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {a₁ b₁ c₁ a₂ b₂ c₂ cont₁ cont₂},
      ArgRel G .bool a₁ a₂ → ArgRel G .bool b₁ b₂ → ArgRel G .bool c₁ c₂ →
      (∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, ArgRel G' .bool y₁ y₂ → Wf G' D (cont₁ y₁) (cont₂ y₂)) →
      Wf G D (onBool₁ a₁ b₁ c₁ cont₁) (onBool₂ a₂ b₂ c₂ cont₂))
    (hn : ∀ (n : Nat) {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {a₁ b₁ c₁ a₂ b₂ c₂ cont₁ cont₂},
      ArgRel G (.bits (target.widenWidth n)) a₁ a₂ → ArgRel G (.bits (target.widenWidth n)) b₁ b₂ →
      ArgRel G (.bits (target.widenWidth n)) c₁ c₂ →
      (∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, ArgRel G' (.bits (target.widenWidth n)) y₁ y₂ → Wf G' D (cont₁ y₁) (cont₂ y₂)) →
      Wf G D (onBits₁ n a₁ b₁ c₁ cont₁) (onBits₂ n a₂ b₂ c₂ cont₂))
    (hf : ∀ (f : Fmt) {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {a₁ b₁ c₁ a₂ b₂ c₂ cont₁ cont₂},
      ArgRel G (.float f) a₁ a₂ → ArgRel G (.float f) b₁ b₂ → ArgRel G (.float f) c₁ c₂ →
      (∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, ArgRel G' (.float f) y₁ y₂ → Wf G' D (cont₁ y₁) (cont₂ y₂)) →
      Wf G D (onFloat₁ f a₁ b₁ c₁ cont₁) (onFloat₂ f a₂ b₂ c₂ cont₂)) :
    ∀ (t : Ty) {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
      {xs₁ : Tup (Arg V₁) (target.legalTys t)} {xs₂ : Tup (Arg V₂) (target.legalTys t)}
      {ys₁ : Tup (Arg V₁) (target.legalTys t)} {ys₂ : Tup (Arg V₂) (target.legalTys t)}
      {zs₁ : Tup (Arg V₁) (target.legalTys t)} {zs₂ : Tup (Arg V₂) (target.legalTys t)},
      TRel (ArgRel G) xs₁ xs₂ → TRel (ArgRel G) ys₁ ys₂ → TRel (ArgRel G) zs₁ zs₂ →
      ∀ {k₁ : Tup (Arg V₁) (target.legalTys t) → Expr V₁ L₁ rs}
        {k₂ : Tup (Arg V₂) (target.legalTys t) → Expr V₂ L₂ rs},
      (∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, TRel (ArgRel G') y₁ y₂ → Wf G' D (k₁ y₁) (k₂ y₂)) →
      Wf G D (legalTernaryTree target mkCode vecSupported onBool₁ onBits₁ onFloat₁ t xs₁ ys₁ zs₁ k₁)
             (legalTernaryTree target mkCode vecSupported onBool₂ onBits₂ onFloat₂ t xs₂ ys₂ zs₂ k₂)
  | .bool, _, _, xs₁, xs₂, ys₁, ys₂, zs₁, zs₂, hxs, hys, hzs, _, _, hk => by
    rcases xs₁ with ⟨a₁, ⟨⟩⟩; rcases xs₂ with ⟨a₂, ⟨⟩⟩
    rcases ys₁ with ⟨b₁, ⟨⟩⟩; rcases ys₂ with ⟨b₂, ⟨⟩⟩
    rcases zs₁ with ⟨c₁, ⟨⟩⟩; rcases zs₂ with ⟨c₂, ⟨⟩⟩
    cases hxs with | cons ha _ => cases hys with | cons hb' _ => cases hzs with | cons hc _ =>
    exact hb ha hb' hc fun hG' y₁ y₂ hy => hk hG' _ _ (TRel.single hy)
  | .bits n, _, _, xs₁, xs₂, ys₁, ys₂, zs₁, zs₂, hxs, hys, hzs, _, _, hk => by
    rcases xs₁ with ⟨a₁, ⟨⟩⟩; rcases xs₂ with ⟨a₂, ⟨⟩⟩
    rcases ys₁ with ⟨b₁, ⟨⟩⟩; rcases ys₂ with ⟨b₂, ⟨⟩⟩
    rcases zs₁ with ⟨c₁, ⟨⟩⟩; rcases zs₂ with ⟨c₂, ⟨⟩⟩
    cases hxs with | cons ha _ => cases hys with | cons hb' _ => cases hzs with | cons hc _ =>
    exact hn n ha hb' hc fun hG' y₁ y₂ hy => hk hG' _ _ (TRel.single hy)
  | .float f, _, _, xs₁, xs₂, ys₁, ys₂, zs₁, zs₂, hxs, hys, hzs, _, _, hk => by
    rcases xs₁ with ⟨a₁, ⟨⟩⟩; rcases xs₂ with ⟨a₂, ⟨⟩⟩
    rcases ys₁ with ⟨b₁, ⟨⟩⟩; rcases ys₂ with ⟨b₂, ⟨⟩⟩
    rcases zs₁ with ⟨c₁, ⟨⟩⟩; rcases zs₂ with ⟨c₂, ⟨⟩⟩
    cases hxs with | cons ha _ => cases hys with | cons hb' _ => cases hzs with | cons hc _ =>
    exact hf f ha hb' hc fun hG' y₁ y₂ hy => hk hG' _ _ (TRel.single hy)
  | .pair t1 t2, G, D, xs₁, xs₂, ys₁, ys₂, zs₁, zs₂, hxs, hys, hzs, k₁, k₂, hk => by
    simp only [legalTernaryTree]
    split
    · next h =>
      obtain ⟨hx1, _⟩ := TRel.cons_iff.1 (packedToTup_rel h hxs)
      obtain ⟨hy1, _⟩ := TRel.cons_iff.1 (packedToTup_rel h hys)
      obtain ⟨hz1, _⟩ := TRel.cons_iff.1 (packedToTup_rel h hzs)
      split
      · exact Wf.let3 (mkCode (.pair t1 t2)) hx1 hy1 hz1 fun hG' r₁ r₂ hr =>
          hk hG' _ _ (tupToPacked_rel h (.cons hr .nil))
      · refine splitLegalToLeaves_wf target (.pair t1 t2) hxs fun hG1 fx₁ fx₂ hfx =>
          splitLegalToLeaves_wf target (.pair t1 t2) (TRel_argRel_weaken' hG1 hys) fun hG2 fy₁ fy₂ hfy =>
            splitLegalToLeaves_wf target (.pair t1 t2) (TRel_argRel_weaken' (sub_trans hG1 hG2) hzs) fun hG3 fz₁ fz₂ hfz => ?_
        have hgoS : ∀ (u : Ty) {G' : Ctx V₁ V₂}
            {fxu₁ : Tup (Arg V₁) (target.leafTys u)} {fxu₂ : Tup (Arg V₂) (target.leafTys u)}
            {fyu₁ : Tup (Arg V₁) (target.leafTys u)} {fyu₂ : Tup (Arg V₂) (target.leafTys u)}
            {fzu₁ : Tup (Arg V₁) (target.leafTys u)} {fzu₂ : Tup (Arg V₂) (target.leafTys u)},
            TRel (ArgRel G') fxu₁ fxu₂ → TRel (ArgRel G') fyu₁ fyu₂ → TRel (ArgRel G') fzu₁ fzu₂ →
            ∀ {c₁ : Tup (Arg V₁) (target.leafTys u) → Expr V₁ L₁ rs}
              {c₂ : Tup (Arg V₂) (target.leafTys u) → Expr V₂ L₂ rs},
            (∀ {G''}, (∀ p ∈ G', p ∈ G'') → ∀ y₁ y₂, TRel (ArgRel G'') y₁ y₂ → Wf G'' D (c₁ y₁) (c₂ y₂)) →
            Wf G' D
              (legalTernaryTree.goS target onBool₁ onBits₁ onFloat₁ u fxu₁ fyu₁ fzu₁ c₁)
              (legalTernaryTree.goS target onBool₂ onBits₂ onFloat₂ u fxu₂ fyu₂ fzu₂ c₂) := by
          intro u
          induction u with
          | bool =>
            intro G' (_, ()) (_, ()) (_, ()) (_, ()) (_, ()) (_, ()) hx hy hz c₁ c₂ hc
            cases hx with | cons hx _ => cases hy with | cons hy _ => cases hz with | cons hz _ =>
              exact hb hx hy hz fun hG' y₁ y₂ hr => hc hG' _ _ (TRel.single hr)
          | bits n =>
            intro G' xs1 xs2 ys1 ys2 zs1 zs2 hx hy hz c₁ c₂ hc
            rcases xs1 with ⟨u1, ⟨⟩⟩; rcases xs2 with ⟨u2, ⟨⟩⟩
            rcases ys1 with ⟨v1, ⟨⟩⟩; rcases ys2 with ⟨v2, ⟨⟩⟩
            rcases zs1 with ⟨w1, ⟨⟩⟩; rcases zs2 with ⟨w2, ⟨⟩⟩
            cases hx with | cons hx _ => cases hy with | cons hy _ => cases hz with | cons hz _ =>
              exact hn n hx hy hz fun hG' y₁ y₂ hr => hc hG' _ _ (TRel.single hr)
          | float f =>
            intro G' (_, ()) (_, ()) (_, ()) (_, ()) (_, ()) (_, ()) hx hy hz c₁ c₂ hc
            cases hx with | cons hx _ => cases hy with | cons hy _ => cases hz with | cons hz _ =>
              exact hf f hx hy hz fun hG' y₁ y₂ hr => hc hG' _ _ (TRel.single hr)
          | pair u1 u2 ih1 ih2 =>
            intro G' _ _ _ _ _ _ hx hy hz c₁ c₂ hc
            obtain ⟨hx1, hx2⟩ := TRel_tupSplit hx
            obtain ⟨hy1, hy2⟩ := TRel_tupSplit hy
            obtain ⟨hz1, hz2⟩ := TRel_tupSplit hz
            exact ih1 hx1 hy1 hz1 fun hGa r1₁ r1₂ hr1 =>
              ih2 (TRel_argRel_weaken' hGa hx2) (TRel_argRel_weaken' hGa hy2) (TRel_argRel_weaken' hGa hz2)
                fun hGb r2₁ r2₂ hr2 => hc (sub_trans hGa hGb) _ _
                  (TRel_tupAppend (TRel_argRel_weaken' hGb hr1) hr2)
        refine hgoS (.pair t1 t2) (TRel_argRel_weaken' (sub_trans hG2 hG3) hfx)
          (TRel_argRel_weaken' hG3 hfy) hfz fun hG4 fr₁ fr₂ hfr =>
          packLeavesToLegal_wf target (.pair t1 t2) hfr fun hG5 y₁ y₂ hy =>
            hk (sub_trans hG1 (sub_trans hG2 (sub_trans hG3 (sub_trans hG4 hG5)))) y₁ y₂ hy
    · next h =>
      have hff := Bool.eq_false_iff.mpr h
      obtain ⟨hx1, hx2⟩ := TRel_tupSplit (splitToTup_rel hff hxs)
      obtain ⟨hy1, hy2⟩ := TRel_tupSplit (splitToTup_rel hff hys)
      obtain ⟨hz1, hz2⟩ := TRel_tupSplit (splitToTup_rel hff hzs)
      refine legalTernaryTree_wf mkCode vecSupported hb hn hf t1 hx1 hy1 hz1 fun hG1 r1₁ r1₂ hr1 =>
        legalTernaryTree_wf mkCode vecSupported hb hn hf t2
          (TRel_argRel_weaken' hG1 hx2) (TRel_argRel_weaken' hG1 hy2) (TRel_argRel_weaken' hG1 hz2)
          fun hG2 r2₁ r2₂ hr2 =>
            hk (sub_trans hG1 hG2) _ _ (tupToSplit_rel hff (TRel_tupAppend (TRel_argRel_weaken' hG2 hr1) hr2))

def OptRhsRel {V₁ V₂ : Ty → Type} (LG : Ctx (LVar target V₁) (LVar target V₂)) (t : Ty) :
    Option (Arg (LVar target V₁) t) → Option (Arg (LVar target V₂) t) → Prop
  | none, none => True
  | some r₁, some r₂ => ArgRel LG t r₁ r₂
  | _, _ => False

private theorem checkUniformImmShift_rel {V₁ V₂ : Ty → Type} {G : Ctx V₁ V₂}
    {as bs : List Ty} (u : Ty) (code : OpCode as bs) {x₁ : Arg V₁ u} {x₂ : Arg V₂ u}
    (hx : ArgRel G u x₁ x₂) :
    checkUniformImmShift u code x₁ = checkUniformImmShift u code x₂ := by
  cases hx <;> rfl

theorem legalBinTree_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    (mkCode : (u : Ty) → OpCode [u, u] [u]) (vecSupported : (u : Ty) → Bool → Bool)
    {onBool₁ : Arg V₁ .bool → Arg V₁ .bool → (Arg V₁ .bool → Expr V₁ L₁ rs) → Expr V₁ L₁ rs}
    {onBool₂ : Arg V₂ .bool → Arg V₂ .bool → (Arg V₂ .bool → Expr V₂ L₂ rs) → Expr V₂ L₂ rs}
    {onBits₁ : (n : Nat) → Arg V₁ (.bits (target.widenWidth n)) → Arg V₁ (.bits (target.widenWidth n)) →
      (Arg V₁ (.bits (target.widenWidth n)) → Expr V₁ L₁ rs) → Expr V₁ L₁ rs}
    {onBits₂ : (n : Nat) → Arg V₂ (.bits (target.widenWidth n)) → Arg V₂ (.bits (target.widenWidth n)) →
      (Arg V₂ (.bits (target.widenWidth n)) → Expr V₂ L₂ rs) → Expr V₂ L₂ rs}
    {onFloat₁ : (f : Fmt) → Arg V₁ (.float f) → Arg V₁ (.float f) →
      (Arg V₁ (.float f) → Expr V₁ L₁ rs) → Expr V₁ L₁ rs}
    {onFloat₂ : (f : Fmt) → Arg V₂ (.float f) → Arg V₂ (.float f) →
      (Arg V₂ (.float f) → Expr V₂ L₂ rs) → Expr V₂ L₂ rs}
    (uniformImmRhs₁ : (u : Ty) → Arg (LVar target V₁) u → Bool)
    (uniformImmRhs₂ : (u : Ty) → Arg (LVar target V₂) u → Bool)
    (hunif : ∀ u {LG' : Ctx (LVar target V₁) (LVar target V₂)} {r₁ r₂},
      ArgRel LG' u r₁ r₂ → uniformImmRhs₁ u r₁ = uniformImmRhs₂ u r₂)
    (hb : ∀ {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {a₁ b₁ a₂ b₂ cont₁ cont₂},
      ArgRel G .bool a₁ a₂ → ArgRel G .bool b₁ b₂ →
      (∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, ArgRel G' .bool y₁ y₂ → Wf G' D (cont₁ y₁) (cont₂ y₂)) →
      Wf G D (onBool₁ a₁ b₁ cont₁) (onBool₂ a₂ b₂ cont₂))
    (hn : ∀ (n : Nat) {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {a₁ b₁ a₂ b₂ cont₁ cont₂},
      ArgRel G (.bits (target.widenWidth n)) a₁ a₂ → ArgRel G (.bits (target.widenWidth n)) b₁ b₂ →
      (∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, ArgRel G' (.bits (target.widenWidth n)) y₁ y₂ → Wf G' D (cont₁ y₁) (cont₂ y₂)) →
      Wf G D (onBits₁ n a₁ b₁ cont₁) (onBits₂ n a₂ b₂ cont₂))
    (hf : ∀ (f : Fmt) {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {a₁ b₁ a₂ b₂ cont₁ cont₂},
      ArgRel G (.float f) a₁ a₂ → ArgRel G (.float f) b₁ b₂ →
      (∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, ArgRel G' (.float f) y₁ y₂ → Wf G' D (cont₁ y₁) (cont₂ y₂)) →
      Wf G D (onFloat₁ f a₁ b₁ cont₁) (onFloat₂ f a₂ b₂ cont₂)) :
    ∀ (t : Ty) {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {LG : Ctx (LVar target V₁) (LVar target V₂)}
      {xs₁ : Tup (Arg V₁) (target.legalTys t)} {xs₂ : Tup (Arg V₂) (target.legalTys t)}
      {ys₁ : Tup (Arg V₁) (target.legalTys t)} {ys₂ : Tup (Arg V₂) (target.legalTys t)}
      {rhs₁ : Option (Arg (LVar target V₁) t)} {rhs₂ : Option (Arg (LVar target V₂) t)},
      TRel (ArgRel G) xs₁ xs₂ → TRel (ArgRel G) ys₁ ys₂ → OptRhsRel target LG t rhs₁ rhs₂ →
      ∀ {k₁ : Tup (Arg V₁) (target.legalTys t) → Expr V₁ L₁ rs}
        {k₂ : Tup (Arg V₂) (target.legalTys t) → Expr V₂ L₂ rs},
      (∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, TRel (ArgRel G') y₁ y₂ → Wf G' D (k₁ y₁) (k₂ y₂)) →
      Wf G D (legalBinTree target mkCode vecSupported onBool₁ onBits₁ onFloat₁ uniformImmRhs₁ t xs₁ ys₁ rhs₁ k₁)
             (legalBinTree target mkCode vecSupported onBool₂ onBits₂ onFloat₂ uniformImmRhs₂ t xs₂ ys₂ rhs₂ k₂)
  | .bool, _, _, _, xs₁, xs₂, ys₁, ys₂, _, _, hxs, hys, _, _, _, hk => by
    rcases xs₁ with ⟨a₁, ⟨⟩⟩; rcases xs₂ with ⟨a₂, ⟨⟩⟩
    rcases ys₁ with ⟨b₁, ⟨⟩⟩; rcases ys₂ with ⟨b₂, ⟨⟩⟩
    cases hxs with | cons ha _ => cases hys with | cons hb' _ =>
    exact hb ha hb' fun hG' y₁ y₂ hy => hk hG' _ _ (TRel.single hy)
  | .bits n, _, _, _, xs₁, xs₂, ys₁, ys₂, _, _, hxs, hys, _, _, _, hk => by
    rcases xs₁ with ⟨a₁, ⟨⟩⟩; rcases xs₂ with ⟨a₂, ⟨⟩⟩
    rcases ys₁ with ⟨b₁, ⟨⟩⟩; rcases ys₂ with ⟨b₂, ⟨⟩⟩
    cases hxs with | cons ha _ => cases hys with | cons hb' _ =>
    exact hn n ha hb' fun hG' y₁ y₂ hy => hk hG' _ _ (TRel.single hy)
  | .float f, _, _, _, xs₁, xs₂, ys₁, ys₂, _, _, hxs, hys, _, _, _, hk => by
    rcases xs₁ with ⟨a₁, ⟨⟩⟩; rcases xs₂ with ⟨a₂, ⟨⟩⟩
    rcases ys₁ with ⟨b₁, ⟨⟩⟩; rcases ys₂ with ⟨b₂, ⟨⟩⟩
    cases hxs with | cons ha _ => cases hys with | cons hb' _ =>
    exact hf f ha hb' fun hG' y₁ y₂ hy => hk hG' _ _ (TRel.single hy)
  | .pair t1 t2, G, D, LG, xs₁, xs₂, ys₁, ys₂, rhs₁, rhs₂, hxs, hys, hrhs, k₁, k₂, hk => by
    dsimp only [legalBinTree]
    split
    · next h =>
      have hxs' := packedToTup_rel h hxs
      have hys' := packedToTup_rel h hys
      obtain ⟨hx1, _⟩ := TRel.cons_iff.1 hxs'
      obtain ⟨hy1, _⟩ := TRel.cons_iff.1 hys'
      have hscalar :
          Wf G D
            (splitLegalToLeaves target (.pair t1 t2) xs₁ fun fx =>
             splitLegalToLeaves target (.pair t1 t2) ys₁ fun fy =>
             legalBinTree.goS target onBool₁ onBits₁ onFloat₁ (.pair t1 t2) fx fy fun fres =>
               packLeavesToLegal target (.pair t1 t2) fres k₁)
            (splitLegalToLeaves target (.pair t1 t2) xs₂ fun fx =>
             splitLegalToLeaves target (.pair t1 t2) ys₂ fun fy =>
             legalBinTree.goS target onBool₂ onBits₂ onFloat₂ (.pair t1 t2) fx fy fun fres =>
               packLeavesToLegal target (.pair t1 t2) fres k₂) := by
        refine splitLegalToLeaves_wf target (.pair t1 t2) hxs fun hG1 fx₁ fx₂ hfx =>
          splitLegalToLeaves_wf target (.pair t1 t2) (TRel_argRel_weaken' hG1 hys) fun hG2 fy₁ fy₂ hfy => ?_
        have hgoS : ∀ (u : Ty) {G' : Ctx V₁ V₂}
            {fxu₁ : Tup (Arg V₁) (target.leafTys u)} {fxu₂ : Tup (Arg V₂) (target.leafTys u)}
            {fyu₁ : Tup (Arg V₁) (target.leafTys u)} {fyu₂ : Tup (Arg V₂) (target.leafTys u)},
            TRel (ArgRel G') fxu₁ fxu₂ → TRel (ArgRel G') fyu₁ fyu₂ →
            ∀ {c₁ : Tup (Arg V₁) (target.leafTys u) → Expr V₁ L₁ rs}
              {c₂ : Tup (Arg V₂) (target.leafTys u) → Expr V₂ L₂ rs},
            (∀ {G''}, (∀ p ∈ G', p ∈ G'') → ∀ y₁ y₂, TRel (ArgRel G'') y₁ y₂ → Wf G'' D (c₁ y₁) (c₂ y₂)) →
            Wf G' D
              (legalBinTree.goS target onBool₁ onBits₁ onFloat₁ u fxu₁ fyu₁ c₁)
              (legalBinTree.goS target onBool₂ onBits₂ onFloat₂ u fxu₂ fyu₂ c₂) := by
          intro u
          induction u with
          | bool =>
            intro G' (_, ()) (_, ()) (_, ()) (_, ()) hx hy c₁ c₂ hc
            cases hx with | cons hx _ => cases hy with | cons hy _ =>
              exact hb hx hy fun hG' y₁ y₂ hr => hc hG' _ _ (TRel.single hr)
          | bits n =>
            intro G' xs1 xs2 ys1 ys2 hx hy c₁ c₂ hc
            rcases xs1 with ⟨u1, ⟨⟩⟩; rcases xs2 with ⟨u2, ⟨⟩⟩
            rcases ys1 with ⟨v1, ⟨⟩⟩; rcases ys2 with ⟨v2, ⟨⟩⟩
            cases hx with | cons hx _ => cases hy with | cons hy _ =>
              exact hn n hx hy fun hG' y₁ y₂ hr => hc hG' _ _ (TRel.single hr)
          | float f =>
            intro G' (_, ()) (_, ()) (_, ()) (_, ()) hx hy c₁ c₂ hc
            cases hx with | cons hx _ => cases hy with | cons hy _ =>
              exact hf f hx hy fun hG' y₁ y₂ hr => hc hG' _ _ (TRel.single hr)
          | pair u1 u2 ih1 ih2 =>
            intro G' _ _ _ _ hx hy c₁ c₂ hc
            obtain ⟨hx1, hx2⟩ := TRel_tupSplit hx
            obtain ⟨hy1, hy2⟩ := TRel_tupSplit hy
            exact ih1 hx1 hy1 fun hGa r1₁ r1₂ hr1 =>
              ih2 (TRel_argRel_weaken' hGa hx2) (TRel_argRel_weaken' hGa hy2) fun hGb r2₁ r2₂ hr2 =>
                hc (sub_trans hGa hGb) _ _ (TRel_tupAppend (TRel_argRel_weaken' hGb hr1) hr2)
        exact hgoS (.pair t1 t2) (TRel_argRel_weaken' hG2 hfx) hfy fun hG3 fr₁ fr₂ hfr =>
          packLeavesToLegal_wf target (.pair t1 t2) hfr fun hG4 y₁ y₂ hy =>
            hk (sub_trans hG1 (sub_trans hG2 (sub_trans hG3 hG4))) y₁ y₂ hy
      have hyu : checkUniformImmShift (.pair t1 t2) (mkCode (.pair t1 t2)) (packedToTup h ys₁).1 =
          checkUniformImmShift (.pair t1 t2) (mkCode (.pair t1 t2)) (packedToTup h ys₂).1 :=
        checkUniformImmShift_rel (.pair t1 t2) (mkCode (.pair t1 t2)) hy1
      cases rhs₁ with
      | none =>
        cases rhs₂ with
        | some _ => exact False.elim hrhs
        | none =>
          have hu := congrArg (vecSupported (.pair t1 t2)) hyu
          by_cases hvs : vecSupported (.pair t1 t2)
              (checkUniformImmShift (.pair t1 t2) (mkCode (.pair t1 t2)) (packedToTup h ys₁).1) = true
          · have hvs₂ := hu ▸ hvs
            rw [ite_eq_left hvs, ite_eq_left hvs₂]
            exact Wf.let2 (mkCode (.pair t1 t2)) hx1 hy1 fun hG' r₁ r₂ hr =>
              hk hG' _ _ (tupToPacked_rel h (.cons hr .nil))
          · have hvs₂ : ¬ (vecSupported (.pair t1 t2)
                (checkUniformImmShift (.pair t1 t2) (mkCode (.pair t1 t2)) (packedToTup h ys₂).1) = true) := hu ▸ hvs
            rw [ite_eq_right hvs, ite_eq_right hvs₂]
            cases mkCode (.pair t1 t2) <;> (try dsimp only) <;> exact hscalar
      | some r1 =>
        cases rhs₂ with
        | none => exact False.elim hrhs
        | some r2 =>
          have hu := congrArg (vecSupported (.pair t1 t2)) hyu
          by_cases hvs : vecSupported (.pair t1 t2)
              (checkUniformImmShift (.pair t1 t2) (mkCode (.pair t1 t2)) (packedToTup h ys₁).1) = true
          · have hvs₂ := hu ▸ hvs
            rw [ite_eq_left hvs, ite_eq_left hvs₂]
            exact Wf.let2 (mkCode (.pair t1 t2)) hx1 hy1 fun hG' r₁ r₂ hr =>
              hk hG' _ _ (tupToPacked_rel h (.cons hr .nil))
          · have hvs₂ : ¬ (vecSupported (.pair t1 t2)
                (checkUniformImmShift (.pair t1 t2) (mkCode (.pair t1 t2)) (packedToTup h ys₂).1) = true) := hu ▸ hvs
            rw [ite_eq_right hvs, ite_eq_right hvs₂]
            cases hrhs with
            | var _ => cases mkCode (.pair t1 t2) <;> (try dsimp only) <;> exact hscalar
            | imm c =>
              cases mkCode (.pair t1 t2) <;> (try dsimp only [opShiftKind])
              all_goals first
                | exact hscalar
                | (cases uniformShiftLeaf? (.pair t1 t2) c with
                   | none => exact hscalar
                   | some p =>
                     dsimp only
                     by_cases hs0 : (p.2 == 0) = true
                     · rw [ite_eq_left hs0, ite_eq_left hs0]; dsimp only
                       exact hk (fun _ q => q) _ _ (tupToPacked_rel h hxs')
                     · rw [ite_eq_right hs0, ite_eq_right hs0]
                       first
                       | (by_cases hsup : target.vecIntOpSupported (.rotr (.pair t1 t2)) (.pair t1 t2) true = true
                          · rw [ite_eq_left hsup, ite_eq_left hsup]; dsimp only
                            exact Wf.let2 (.rotr (.pair t1 t2)) hx1 (.imm _) fun h1 rt₁ rt₂ hrt =>
                              hk h1 _ _ (tupToPacked_rel h (.cons hrt .nil))
                          · rw [ite_eq_right hsup, ite_eq_right hsup]; dsimp only
                            exact hscalar)
                       | (by_cases hsup : (target.vecIntOpSupported (.rotr (.pair t1 t2)) (.pair t1 t2) true &&
                                          target.vecIntOpSupported (.and (.pair t1 t2)) (.pair t1 t2) false) = true
                          · rw [ite_eq_left hsup, ite_eq_left hsup]; dsimp only
                            exact Wf.let2 (.rotr (.pair t1 t2)) hx1 (.imm _) fun h1 rt₁ rt₂ hrt =>
                              Wf.let2 (.and (.pair t1 t2)) hrt (.imm _) fun h2 r₁ r₂ hr =>
                                hk (sub_trans h1 h2) _ _ (tupToPacked_rel h (.cons hr .nil))
                          · rw [ite_eq_right hsup, ite_eq_right hsup]; dsimp only
                            exact hscalar))
    · next h =>
      have hff := Bool.eq_false_iff.mpr h
      obtain ⟨hx1, hx2⟩ := TRel_tupSplit (splitToTup_rel hff hxs)
      obtain ⟨hy1, hy2⟩ := TRel_tupSplit (splitToTup_rel hff hys)
      exact legalBinTree_wf mkCode vecSupported uniformImmRhs₁ uniformImmRhs₂ hunif hb hn hf
        t1 (LG := LG) hx1 hy1 (rhs₁ := none) (rhs₂ := none) trivial fun hG1 r1₁ r1₂ hr1 =>
        legalBinTree_wf mkCode vecSupported uniformImmRhs₁ uniformImmRhs₂ hunif hb hn hf
          t2 (LG := LG) (TRel_argRel_weaken' hG1 hx2) (TRel_argRel_weaken' hG1 hy2) (rhs₁ := none) (rhs₂ := none) trivial
          fun hG2 r2₁ r2₂ hr2 =>
            hk (sub_trans hG1 hG2) _ _ (tupToSplit_rel hff (TRel_tupAppend (TRel_argRel_weaken' hG2 hr1) hr2))

theorem legalBitsArith_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} (n : Nat) (code : OpCode [.bits n, .bits n] [.bits n])
    {a₁ b₁ : Arg V₁ (.bits (target.widenWidth n))} {a₂ b₂ : Arg V₂ (.bits (target.widenWidth n))}
    (ha : ArgRel G (.bits (target.widenWidth n)) a₁ a₂)
    (hb : ArgRel G (.bits (target.widenWidth n)) b₁ b₂)
    {k₁ : Arg V₁ (.bits (target.widenWidth n)) → Expr V₁ L₁ rs}
    {k₂ : Arg V₂ (.bits (target.widenWidth n)) → Expr V₂ L₂ rs}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂,
      ArgRel G' (.bits (target.widenWidth n)) y₁ y₂ → Wf G' D (k₁ y₁) (k₂ y₂)) :
    Wf G D (legalBitsArith target n code a₁ b₁ k₁) (legalBitsArith target n code a₂ b₂ k₂) := by
  simp only [legalBitsArith]
  split
  · exact hk (fun _ p => p) _ _ (.imm _)
  · cases code <;> simp only
    all_goals first
    | exact .hlt
    | exact Wf.let2 _ ha hb fun h1 r₁ r₂ hr =>
        emitMaskToN_wf n (target.widenWidth n) hr fun h2 y₁ y₂ hy => hk (sub_trans h1 h2) y₁ y₂ hy
    | exact Wf.let2 _ ha hb hk
    | (split
       · exact Wf.let2 _ ha hb hk
       · first
         | exact emitCountMod_wf n (target.widenWidth n) hb fun h1 c₁ c₂ hc =>
             Wf.let2 _ (ha.weaken h1) hc fun h2 r₁ r₂ hr =>
               emitMaskToN_wf n (target.widenWidth n) hr fun h3 y₁ y₂ hy =>
                 hk (sub_trans h1 (sub_trans h2 h3)) y₁ y₂ hy
         | exact emitCountMod_wf n (target.widenWidth n) hb fun h1 c₁ c₂ hc =>
             Wf.let2 _ (ha.weaken h1) hc fun h2 r₁ r₂ hr => hk (sub_trans h1 h2) r₁ r₂ hr
         | exact emitCountMod_wf n (target.widenWidth n) hb fun h1 c₁ c₂ hc =>
             emitSextToW_wf n (target.widenWidth n) (ha.weaken h1) fun h2 sa₁ sa₂ hsa =>
               Wf.let2 _ hsa (hc.weaken h2) fun h3 r₁ r₂ hr =>
                 emitMaskToN_wf n (target.widenWidth n) hr fun h4 y₁ y₂ hy =>
                   hk (sub_trans h1 (sub_trans h2 (sub_trans h3 h4))) y₁ y₂ hy
         | exact emitCountMod_wf n (target.widenWidth n) hb fun h1 c₁ c₂ hc =>
             Wf.let2 _ (.imm _) hc fun h2 nc₁ nc₂ hnc =>
               have s12 := sub_trans h1 h2
               Wf.let2 _ (ha.weaken s12) (hc.weaken h2) fun h3 lo₁ lo₂ hlo =>
                 have s123 := sub_trans s12 h3
                 Wf.let2 _ (ha.weaken s123) (hnc.weaken h3) fun h4 hi₁ hi₂ hhi =>
                   Wf.let2 _ (hlo.weaken h4) hhi fun h5 cb₁ cb₂ hcb =>
                     emitMaskToN_wf n (target.widenWidth n) hcb fun h6 y₁ y₂ hy =>
                       hk (sub_trans s123 (sub_trans h4 (sub_trans h5 h6))) y₁ y₂ hy)

theorem legalCmpTree_goMask_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    (o : CmpOp) :
    ∀ (u : Ty) {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
      {fx₁ : Tup (Arg V₁) (target.leafTys u)} {fx₂ : Tup (Arg V₂) (target.leafTys u)}
      {fy₁ : Tup (Arg V₁) (target.leafTys u)} {fy₂ : Tup (Arg V₂) (target.leafTys u)},
      TRel (ArgRel G) fx₁ fx₂ → TRel (ArgRel G) fy₁ fy₂ →
      ∀ {c₁ : Tup (Arg V₁) (target.leafTys u.mask) → Expr V₁ L₁ rs}
        {c₂ : Tup (Arg V₂) (target.leafTys u.mask) → Expr V₂ L₂ rs},
      (∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, TRel (ArgRel G') y₁ y₂ → Wf G' D (c₁ y₁) (c₂ y₂)) →
      Wf G D (legalCmpTree.goMask target o u fx₁ fy₁ c₁)
             (legalCmpTree.goMask target o u fx₂ fy₂ c₂)
  | .bool, _, _, fx₁, fx₂, fy₁, fy₂, hfx, hfy, _, _, hc => by
    rcases fx₁ with ⟨a₁, ⟨⟩⟩; rcases fx₂ with ⟨a₂, ⟨⟩⟩
    rcases fy₁ with ⟨b₁, ⟨⟩⟩; rcases fy₂ with ⟨b₂, ⟨⟩⟩
    cases hfx with | cons ha _ => cases hfy with | cons hb _ =>
    simp only [legalCmpTree.goMask]
    split
    · exact Wf.let2 _ ha hb fun h1 r₁ r₂ hr => hc h1 _ _ (TRel.single hr)
    · exact emitBoolCmp_wf o ha hb fun hG' r₁ r₂ hr => hc hG' _ _ (TRel.single hr)
  | .bits n, _, _, fx₁, fx₂, fy₁, fy₂, hfx, hfy, _, _, hc => by
    rcases fx₁ with ⟨a₁, ⟨⟩⟩; rcases fx₂ with ⟨a₂, ⟨⟩⟩
    rcases fy₁ with ⟨b₁, ⟨⟩⟩; rcases fy₂ with ⟨b₂, ⟨⟩⟩
    cases hfx with | cons ha _ => cases hfy with | cons hb _ =>
    simp only [legalCmpTree.goMask]
    split
    · exact hc (fun _ p => p) _ _ (TRel.single (ArgRel.imm _))
    · split
      · exact Wf.let2 _ ha hb fun h1 r₁ r₂ hr => hc h1 _ _ (TRel.single hr)
      · cases o <;> dsimp only
        all_goals first
          | exact Wf.let2 _ ha hb fun h1 r₁ r₂ hr => hc h1 _ _ (TRel.single hr)
          | exact emitSextToW_wf n (target.widenWidth n) ha fun h1 sa₁ sa₂ hsa =>
              emitSextToW_wf n (target.widenWidth n) (hb.weaken h1) fun h2 sb₁ sb₂ hsb =>
                Wf.let2 _ (hsa.weaken h2) hsb fun h3 r₁ r₂ hr =>
                  hc (sub_trans h1 (sub_trans h2 h3)) _ _ (TRel.single hr)
  | .float _, _, _, _, _, _, _, _, _, _, _, _ => .hlt
  | .pair u1 u2, _, _, fx₁, fx₂, fy₁, fy₂, hfx, hfy, c₁, c₂, hc => by
    simp only [legalCmpTree.goMask]
    obtain ⟨hx1, hx2⟩ := TRel_tupSplit hfx
    obtain ⟨hy1, hy2⟩ := TRel_tupSplit hfy
    refine legalCmpTree_goMask_wf o u1 hx1 hy1 fun h1 m1₁ m1₂ hm1 => ?_
    refine legalCmpTree_goMask_wf o u2 (TRel_argRel_weaken' h1 hx2) (TRel_argRel_weaken' h1 hy2)
      fun h2 m2₁ m2₂ hm2 =>
        hc (sub_trans h1 h2) _ _ (TRel_tupAppend (TRel_argRel_weaken' h2 hm1) hm2)

theorem legalCmpTree_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    (o : CmpOp) :
    ∀ (t : Ty) {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
      {xs₁ : Tup (Arg V₁) (target.legalTys t)} {xs₂ : Tup (Arg V₂) (target.legalTys t)}
      {ys₁ : Tup (Arg V₁) (target.legalTys t)} {ys₂ : Tup (Arg V₂) (target.legalTys t)},
      TRel (ArgRel G) xs₁ xs₂ → TRel (ArgRel G) ys₁ ys₂ →
      ∀ {k₁ : Tup (Arg V₁) (target.legalTys t.mask) → Expr V₁ L₁ rs}
        {k₂ : Tup (Arg V₂) (target.legalTys t.mask) → Expr V₂ L₂ rs},
      (∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, TRel (ArgRel G') y₁ y₂ → Wf G' D (k₁ y₁) (k₂ y₂)) →
      Wf G D (legalCmpTree target o t xs₁ ys₁ k₁) (legalCmpTree target o t xs₂ ys₂ k₂)
  | .bool, _, _, xs₁, xs₂, ys₁, ys₂, hxs, hys, _, _, hk => by
    rcases xs₁ with ⟨a₁, ⟨⟩⟩; rcases xs₂ with ⟨a₂, ⟨⟩⟩
    rcases ys₁ with ⟨b₁, ⟨⟩⟩; rcases ys₂ with ⟨b₂, ⟨⟩⟩
    cases hxs with | cons ha _ => cases hys with | cons hb _ =>
    simp only [legalCmpTree]
    split
    · exact Wf.let2 _ ha hb fun h1 r₁ r₂ hr => hk h1 _ _ (TRel.single hr)
    · exact emitBoolCmp_wf o ha hb fun hG' r₁ r₂ hr => hk hG' _ _ (TRel.single hr)
  | .bits n, _, _, xs₁, xs₂, ys₁, ys₂, hxs, hys, _, _, hk => by
    rcases xs₁ with ⟨a₁, ⟨⟩⟩; rcases xs₂ with ⟨a₂, ⟨⟩⟩
    rcases ys₁ with ⟨b₁, ⟨⟩⟩; rcases ys₂ with ⟨b₂, ⟨⟩⟩
    cases hxs with | cons ha _ => cases hys with | cons hb _ =>
    simp only [legalCmpTree]
    split
    · exact hk (fun _ p => p) _ _ (TRel.single (ArgRel.imm _))
    · split
      · exact Wf.let2 _ ha hb fun h1 r₁ r₂ hr => hk h1 _ _ (TRel.single hr)
      · cases o <;> dsimp only
        all_goals first
          | exact Wf.let2 _ ha hb fun h1 r₁ r₂ hr => hk h1 _ _ (TRel.single hr)
          | exact emitSextToW_wf n (target.widenWidth n) ha fun h1 sa₁ sa₂ hsa =>
              emitSextToW_wf n (target.widenWidth n) (hb.weaken h1) fun h2 sb₁ sb₂ hsb =>
                Wf.let2 _ (hsa.weaken h2) hsb fun h3 r₁ r₂ hr =>
                  hk (sub_trans h1 (sub_trans h2 h3)) _ _ (TRel.single hr)
  | .float _, _, _, _, _, _, _, _, _, _, _, _ => .hlt
  | .pair t1 t2, _, _, xs₁, xs₂, ys₁, ys₂, hxs, hys, k₁, k₂, hk =>
    splitLegalToLeaves_wf target (.pair t1 t2) hxs fun hG1 fx₁ fx₂ hfx =>
    splitLegalToLeaves_wf target (.pair t1 t2) (TRel_argRel_weaken' hG1 hys) fun hG2 fy₁ fy₂ hfy =>
    legalCmpTree_goMask_wf target o (.pair t1 t2) (TRel_argRel_weaken' hG2 hfx) hfy fun hG3 mr₁ mr₂ hmr =>
    packLeavesToLegal_wf target (Ty.mask (.pair t1 t2)) hmr fun hG4 y₁ y₂ hy =>
      hk (sub_trans hG1 (sub_trans hG2 (sub_trans hG3 hG4))) y₁ y₂ hy

theorem legalSelectTree_goSel_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty} :
    ∀ (u : Ty) {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {c₁ : Arg V₁ .bool} {c₂ : Arg V₂ .bool}
      {fx₁ : Tup (Arg V₁) (target.leafTys u)} {fx₂ : Tup (Arg V₂) (target.leafTys u)}
      {fy₁ : Tup (Arg V₁) (target.leafTys u)} {fy₂ : Tup (Arg V₂) (target.leafTys u)},
      ArgRel G .bool c₁ c₂ → TRel (ArgRel G) fx₁ fx₂ → TRel (ArgRel G) fy₁ fy₂ →
      ∀ {k₁ : Tup (Arg V₁) (target.leafTys u) → Expr V₁ L₁ rs}
        {k₂ : Tup (Arg V₂) (target.leafTys u) → Expr V₂ L₂ rs},
      (∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, TRel (ArgRel G') y₁ y₂ → Wf G' D (k₁ y₁) (k₂ y₂)) →
      Wf G D (legalSelectTree.goSel target c₁ u fx₁ fy₁ k₁)
             (legalSelectTree.goSel target c₂ u fx₂ fy₂ k₂)
  | .bool, _, _, _, _, fx₁, fx₂, fy₁, fy₂, hc, hfx, hfy, _, _, hk => by
    rcases fx₁ with ⟨a₁, ⟨⟩⟩; rcases fx₂ with ⟨a₂, ⟨⟩⟩
    rcases fy₁ with ⟨b₁, ⟨⟩⟩; rcases fy₂ with ⟨b₂, ⟨⟩⟩
    cases hfx with | cons ha _ => cases hfy with | cons hb _ =>
    simp only [legalSelectTree.goSel]
    split
    · exact Wf.let3 _ hc ha hb fun h1 r₁ r₂ hr => hk h1 _ _ (TRel.single hr)
    · exact emitBoolSelect_wf hc ha hb fun hG' r₁ r₂ hr => hk hG' _ _ (TRel.single hr)
  | .bits _, _, _, _, _, fx₁, fx₂, fy₁, fy₂, hc, hfx, hfy, _, _, hk => by
    rcases fx₁ with ⟨a₁, ⟨⟩⟩; rcases fx₂ with ⟨a₂, ⟨⟩⟩
    rcases fy₁ with ⟨b₁, ⟨⟩⟩; rcases fy₂ with ⟨b₂, ⟨⟩⟩
    cases hfx with | cons ha _ => cases hfy with | cons hb _ =>
    exact Wf.let3 _ hc ha hb fun h1 r₁ r₂ hr => hk h1 _ _ (TRel.single hr)
  | .float _, _, _, _, _, fx₁, fx₂, fy₁, fy₂, hc, hfx, hfy, _, _, hk => by
    rcases fx₁ with ⟨a₁, ⟨⟩⟩; rcases fx₂ with ⟨a₂, ⟨⟩⟩
    rcases fy₁ with ⟨b₁, ⟨⟩⟩; rcases fy₂ with ⟨b₂, ⟨⟩⟩
    cases hfx with | cons ha _ => cases hfy with | cons hb _ =>
    exact Wf.let3 _ hc ha hb fun h1 r₁ r₂ hr => hk h1 _ _ (TRel.single hr)
  | .pair u1 u2, _, _, c₁, c₂, fx₁, fx₂, fy₁, fy₂, hc, hfx, hfy, k₁, k₂, hk => by
    obtain ⟨hx1, hx2⟩ := TRel_tupSplit hfx
    obtain ⟨hy1, hy2⟩ := TRel_tupSplit hfy
    refine legalSelectTree_goSel_wf u1 hc hx1 hy1 fun hG1 r1₁ r1₂ hr1 => ?_
    refine legalSelectTree_goSel_wf u2 (hc.weaken hG1)
      (TRel_argRel_weaken' hG1 hx2) (TRel_argRel_weaken' hG1 hy2) fun hG2 r2₁ r2₂ hr2 =>
      hk (sub_trans hG1 hG2) _ _ (TRel_tupAppend (TRel_argRel_weaken' hG2 hr1) hr2)

theorem legalSelectTree_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {c₁ : Arg V₁ .bool} {c₂ : Arg V₂ .bool} (hc : ArgRel G .bool c₁ c₂) :
    ∀ (t : Ty) {xs₁ : Tup (Arg V₁) (target.legalTys t)} {xs₂ : Tup (Arg V₂) (target.legalTys t)}
      {ys₁ : Tup (Arg V₁) (target.legalTys t)} {ys₂ : Tup (Arg V₂) (target.legalTys t)},
      TRel (ArgRel G) xs₁ xs₂ → TRel (ArgRel G) ys₁ ys₂ →
      ∀ {k₁ : Tup (Arg V₁) (target.legalTys t) → Expr V₁ L₁ rs}
        {k₂ : Tup (Arg V₂) (target.legalTys t) → Expr V₂ L₂ rs},
      (∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, TRel (ArgRel G') y₁ y₂ → Wf G' D (k₁ y₁) (k₂ y₂)) →
      Wf G D (legalSelectTree target c₁ t xs₁ ys₁ k₁) (legalSelectTree target c₂ t xs₂ ys₂ k₂)
  | .bool, xs₁, xs₂, ys₁, ys₂, hxs, hys, _, _, hk => by
    rcases xs₁ with ⟨a₁, ⟨⟩⟩; rcases xs₂ with ⟨a₂, ⟨⟩⟩
    rcases ys₁ with ⟨b₁, ⟨⟩⟩; rcases ys₂ with ⟨b₂, ⟨⟩⟩
    cases hxs with | cons ha _ => cases hys with | cons hb _ =>
    simp only [legalSelectTree]
    split
    · exact Wf.let3 _ hc ha hb fun h1 r₁ r₂ hr => hk h1 _ _ (TRel.single hr)
    · exact emitBoolSelect_wf hc ha hb fun hG' r₁ r₂ hr => hk hG' _ _ (TRel.single hr)
  | .bits _, xs₁, xs₂, ys₁, ys₂, hxs, hys, _, _, hk => by
    rcases xs₁ with ⟨a₁, ⟨⟩⟩; rcases xs₂ with ⟨a₂, ⟨⟩⟩
    rcases ys₁ with ⟨b₁, ⟨⟩⟩; rcases ys₂ with ⟨b₂, ⟨⟩⟩
    cases hxs with | cons ha _ => cases hys with | cons hb _ =>
    exact Wf.let3 _ hc ha hb fun h1 r₁ r₂ hr => hk h1 _ _ (TRel.single hr)
  | .float _, xs₁, xs₂, ys₁, ys₂, hxs, hys, _, _, hk => by
    rcases xs₁ with ⟨a₁, ⟨⟩⟩; rcases xs₂ with ⟨a₂, ⟨⟩⟩
    rcases ys₁ with ⟨b₁, ⟨⟩⟩; rcases ys₂ with ⟨b₂, ⟨⟩⟩
    cases hxs with | cons ha _ => cases hys with | cons hb _ =>
    exact Wf.let3 _ hc ha hb fun h1 r₁ r₂ hr => hk h1 _ _ (TRel.single hr)
  | .pair t1 t2, xs₁, xs₂, ys₁, ys₂, hxs, hys, k₁, k₂, hk =>
    splitLegalToLeaves_wf target (.pair t1 t2) hxs fun hG1 fx₁ fx₂ hfx =>
    splitLegalToLeaves_wf target (.pair t1 t2) (TRel_argRel_weaken' hG1 hys) fun hG2 fy₁ fy₂ hfy =>
    legalSelectTree_goSel_wf target (.pair t1 t2) (hc.weaken (sub_trans hG1 hG2))
      (TRel_argRel_weaken' hG2 hfx) hfy fun hG3 fr₁ fr₂ hfr =>
    packLeavesToLegal_wf target (.pair t1 t2) hfr fun hG4 y₁ y₂ hy =>
      hk (sub_trans hG1 (sub_trans hG2 (sub_trans hG3 hG4))) y₁ y₂ hy

theorem legalBlendTree_goBlend_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty} :
    ∀ (u : Ty) {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
      {fm₁ : Tup (Arg V₁) (target.leafTys u.mask)} {fm₂ : Tup (Arg V₂) (target.leafTys u.mask)}
      {fx₁ : Tup (Arg V₁) (target.leafTys u)} {fx₂ : Tup (Arg V₂) (target.leafTys u)}
      {fy₁ : Tup (Arg V₁) (target.leafTys u)} {fy₂ : Tup (Arg V₂) (target.leafTys u)},
      TRel (ArgRel G) fm₁ fm₂ → TRel (ArgRel G) fx₁ fx₂ → TRel (ArgRel G) fy₁ fy₂ →
      ∀ {k₁ : Tup (Arg V₁) (target.leafTys u) → Expr V₁ L₁ rs}
        {k₂ : Tup (Arg V₂) (target.leafTys u) → Expr V₂ L₂ rs},
      (∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, TRel (ArgRel G') y₁ y₂ → Wf G' D (k₁ y₁) (k₂ y₂)) →
      Wf G D (legalBlendTree.goBlend target u fm₁ fx₁ fy₁ k₁)
             (legalBlendTree.goBlend target u fm₂ fx₂ fy₂ k₂)
  | .bool, _, _, fm₁, fm₂, fx₁, fx₂, fy₁, fy₂, hfm, hfx, hfy, _, _, hk => by
    rcases fm₁ with ⟨c₁, ⟨⟩⟩; rcases fm₂ with ⟨c₂, ⟨⟩⟩
    rcases fx₁ with ⟨a₁, ⟨⟩⟩; rcases fx₂ with ⟨a₂, ⟨⟩⟩
    rcases fy₁ with ⟨b₁, ⟨⟩⟩; rcases fy₂ with ⟨b₂, ⟨⟩⟩
    cases hfm with | cons hc _ => cases hfx with | cons ha _ => cases hfy with | cons hb _ =>
    simp only [legalBlendTree.goBlend]
    split
    · exact Wf.let3 _ hc ha hb fun h1 r₁ r₂ hr => hk h1 _ _ (TRel.single hr)
    · exact emitBoolSelect_wf hc ha hb fun hG' r₁ r₂ hr => hk hG' _ _ (TRel.single hr)
  | .bits _, _, _, fm₁, fm₂, fx₁, fx₂, fy₁, fy₂, hfm, hfx, hfy, _, _, hk => by
    rcases fm₁ with ⟨c₁, ⟨⟩⟩; rcases fm₂ with ⟨c₂, ⟨⟩⟩
    rcases fx₁ with ⟨a₁, ⟨⟩⟩; rcases fx₂ with ⟨a₂, ⟨⟩⟩
    rcases fy₁ with ⟨b₁, ⟨⟩⟩; rcases fy₂ with ⟨b₂, ⟨⟩⟩
    cases hfm with | cons hc _ => cases hfx with | cons ha _ => cases hfy with | cons hb _ =>
    exact Wf.let3 _ hc ha hb fun h1 r₁ r₂ hr => hk h1 _ _ (TRel.single hr)
  | .float _, _, _, fm₁, fm₂, fx₁, fx₂, fy₁, fy₂, hfm, hfx, hfy, _, _, hk => by
    rcases fm₁ with ⟨c₁, ⟨⟩⟩; rcases fm₂ with ⟨c₂, ⟨⟩⟩
    rcases fx₁ with ⟨a₁, ⟨⟩⟩; rcases fx₂ with ⟨a₂, ⟨⟩⟩
    rcases fy₁ with ⟨b₁, ⟨⟩⟩; rcases fy₂ with ⟨b₂, ⟨⟩⟩
    cases hfm with | cons hc _ => cases hfx with | cons ha _ => cases hfy with | cons hb _ =>
    exact Wf.let3 _ hc ha hb fun h1 r₁ r₂ hr => hk h1 _ _ (TRel.single hr)
  | .pair u1 u2, _, _, fm₁, fm₂, fx₁, fx₂, fy₁, fy₂, hfm, hfx, hfy, k₁, k₂, hk => by
    obtain ⟨hm1, hm2⟩ := TRel_tupSplit hfm
    obtain ⟨hx1, hx2⟩ := TRel_tupSplit hfx
    obtain ⟨hy1, hy2⟩ := TRel_tupSplit hfy
    refine legalBlendTree_goBlend_wf u1 hm1 hx1 hy1 fun hG1 r1₁ r1₂ hr1 => ?_
    refine legalBlendTree_goBlend_wf u2 (TRel_argRel_weaken' hG1 hm2)
      (TRel_argRel_weaken' hG1 hx2) (TRel_argRel_weaken' hG1 hy2) fun hG2 r2₁ r2₂ hr2 =>
      hk (sub_trans hG1 hG2) _ _ (TRel_tupAppend (TRel_argRel_weaken' hG2 hr1) hr2)

theorem legalBlendTree_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty} :
    ∀ (t : Ty) {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
      {ms₁ : Tup (Arg V₁) (target.legalTys t.mask)} {ms₂ : Tup (Arg V₂) (target.legalTys t.mask)}
      {xs₁ : Tup (Arg V₁) (target.legalTys t)} {xs₂ : Tup (Arg V₂) (target.legalTys t)}
      {ys₁ : Tup (Arg V₁) (target.legalTys t)} {ys₂ : Tup (Arg V₂) (target.legalTys t)},
      TRel (ArgRel G) ms₁ ms₂ → TRel (ArgRel G) xs₁ xs₂ → TRel (ArgRel G) ys₁ ys₂ →
      ∀ {k₁ : Tup (Arg V₁) (target.legalTys t) → Expr V₁ L₁ rs}
        {k₂ : Tup (Arg V₂) (target.legalTys t) → Expr V₂ L₂ rs},
      (∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, TRel (ArgRel G') y₁ y₂ → Wf G' D (k₁ y₁) (k₂ y₂)) →
      Wf G D (legalBlendTree target t ms₁ xs₁ ys₁ k₁) (legalBlendTree target t ms₂ xs₂ ys₂ k₂)
  | .bool, _, _, ms₁, ms₂, xs₁, xs₂, ys₁, ys₂, hms, hxs, hys, _, _, hk => by
    rcases ms₁ with ⟨c₁, ⟨⟩⟩; rcases ms₂ with ⟨c₂, ⟨⟩⟩
    rcases xs₁ with ⟨a₁, ⟨⟩⟩; rcases xs₂ with ⟨a₂, ⟨⟩⟩
    rcases ys₁ with ⟨b₁, ⟨⟩⟩; rcases ys₂ with ⟨b₂, ⟨⟩⟩
    cases hms with | cons hc _ => cases hxs with | cons ha _ => cases hys with | cons hb _ =>
    simp only [legalBlendTree]
    split
    · exact Wf.let3 _ hc ha hb fun h1 r₁ r₂ hr => hk h1 _ _ (TRel.single hr)
    · exact emitBoolSelect_wf hc ha hb fun hG' r₁ r₂ hr => hk hG' _ _ (TRel.single hr)
  | .bits _, _, _, ms₁, ms₂, xs₁, xs₂, ys₁, ys₂, hms, hxs, hys, _, _, hk => by
    rcases ms₁ with ⟨c₁, ⟨⟩⟩; rcases ms₂ with ⟨c₂, ⟨⟩⟩
    rcases xs₁ with ⟨a₁, ⟨⟩⟩; rcases xs₂ with ⟨a₂, ⟨⟩⟩
    rcases ys₁ with ⟨b₁, ⟨⟩⟩; rcases ys₂ with ⟨b₂, ⟨⟩⟩
    cases hms with | cons hc _ => cases hxs with | cons ha _ => cases hys with | cons hb _ =>
    exact Wf.let3 _ hc ha hb fun h1 r₁ r₂ hr => hk h1 _ _ (TRel.single hr)
  | .float _, _, _, ms₁, ms₂, xs₁, xs₂, ys₁, ys₂, hms, hxs, hys, _, _, hk => by
    rcases ms₁ with ⟨c₁, ⟨⟩⟩; rcases ms₂ with ⟨c₂, ⟨⟩⟩
    rcases xs₁ with ⟨a₁, ⟨⟩⟩; rcases xs₂ with ⟨a₂, ⟨⟩⟩
    rcases ys₁ with ⟨b₁, ⟨⟩⟩; rcases ys₂ with ⟨b₂, ⟨⟩⟩
    cases hms with | cons hc _ => cases hxs with | cons ha _ => cases hys with | cons hb _ =>
    exact Wf.let3 _ hc ha hb fun h1 r₁ r₂ hr => hk h1 _ _ (TRel.single hr)
  | .pair t1 t2, _, _, ms₁, ms₂, xs₁, xs₂, ys₁, ys₂, hms, hxs, hys, k₁, k₂, hk =>
    splitLegalToLeaves_wf target (Ty.mask (.pair t1 t2)) hms fun hG1 fm₁ fm₂ hfm =>
    splitLegalToLeaves_wf target (.pair t1 t2) (TRel_argRel_weaken' hG1 hxs) fun hG2 fx₁ fx₂ hfx =>
    splitLegalToLeaves_wf target (.pair t1 t2) (TRel_argRel_weaken' (sub_trans hG1 hG2) hys) fun hG3 fy₁ fy₂ hfy =>
    legalBlendTree_goBlend_wf target (.pair t1 t2)
      (TRel_argRel_weaken' (sub_trans hG2 hG3) hfm)
      (TRel_argRel_weaken' hG3 hfx) hfy fun hG4 fr₁ fr₂ hfr =>
    packLeavesToLegal_wf target (.pair t1 t2) hfr fun hG5 y₁ y₂ hy =>
      hk (sub_trans hG1 (sub_trans hG2 (sub_trans hG3 (sub_trans hG4 hG5)))) y₁ y₂ hy

theorem legalFCmpTree_goFCmp_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    (o : FCmpOp) :
    ∀ (u : Ty) {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
      {fx₁ : Tup (Arg V₁) (target.leafTys u)} {fx₂ : Tup (Arg V₂) (target.leafTys u)}
      {fy₁ : Tup (Arg V₁) (target.leafTys u)} {fy₂ : Tup (Arg V₂) (target.leafTys u)},
      TRel (ArgRel G) fx₁ fx₂ → TRel (ArgRel G) fy₁ fy₂ →
      ∀ {k₁ : Tup (Arg V₁) (target.leafTys u.mask) → Expr V₁ L₁ rs}
        {k₂ : Tup (Arg V₂) (target.leafTys u.mask) → Expr V₂ L₂ rs},
      (∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, TRel (ArgRel G') y₁ y₂ → Wf G' D (k₁ y₁) (k₂ y₂)) →
      Wf G D (legalFCmpTree.goFCmp target o u fx₁ fy₁ k₁)
             (legalFCmpTree.goFCmp target o u fx₂ fy₂ k₂)
  | .bool, _, _, _, _, _, _, _, _, _, _, _ => .hlt
  | .bits _, _, _, _, _, _, _, _, _, _, _, _ => .hlt
  | .float _, _, _, fx₁, fx₂, fy₁, fy₂, hfx, hfy, _, _, hk => by
    rcases fx₁ with ⟨a₁, ⟨⟩⟩; rcases fx₂ with ⟨a₂, ⟨⟩⟩
    rcases fy₁ with ⟨b₁, ⟨⟩⟩; rcases fy₂ with ⟨b₂, ⟨⟩⟩
    cases hfx with | cons ha _ => cases hfy with | cons hb _ =>
    exact Wf.let2 _ ha hb fun h1 r₁ r₂ hr => hk h1 _ _ (TRel.single hr)
  | .pair u1 u2, _, _, fx₁, fx₂, fy₁, fy₂, hfx, hfy, k₁, k₂, hk => by
    obtain ⟨hx1, hx2⟩ := TRel_tupSplit hfx
    obtain ⟨hy1, hy2⟩ := TRel_tupSplit hfy
    refine legalFCmpTree_goFCmp_wf o u1 hx1 hy1 fun hG1 m1₁ m1₂ hm1 => ?_
    refine legalFCmpTree_goFCmp_wf o u2 (TRel_argRel_weaken' hG1 hx2) (TRel_argRel_weaken' hG1 hy2)
      fun hG2 m2₁ m2₂ hm2 =>
        hk (sub_trans hG1 hG2) _ _ (TRel_tupAppend (TRel_argRel_weaken' hG2 hm1) hm2)

theorem legalFCmpTree_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    (o : FCmpOp) :
    ∀ (t : Ty) {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
      {xs₁ : Tup (Arg V₁) (target.legalTys t)} {xs₂ : Tup (Arg V₂) (target.legalTys t)}
      {ys₁ : Tup (Arg V₁) (target.legalTys t)} {ys₂ : Tup (Arg V₂) (target.legalTys t)},
      TRel (ArgRel G) xs₁ xs₂ → TRel (ArgRel G) ys₁ ys₂ →
      ∀ {k₁ : Tup (Arg V₁) (target.legalTys t.mask) → Expr V₁ L₁ rs}
        {k₂ : Tup (Arg V₂) (target.legalTys t.mask) → Expr V₂ L₂ rs},
      (∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, TRel (ArgRel G') y₁ y₂ → Wf G' D (k₁ y₁) (k₂ y₂)) →
      Wf G D (legalFCmpTree target o t xs₁ ys₁ k₁) (legalFCmpTree target o t xs₂ ys₂ k₂)
  | .bool, _, _, _, _, _, _, _, _, _, _, _ => .hlt
  | .bits _, _, _, _, _, _, _, _, _, _, _, _ => .hlt
  | .float _, _, _, fx₁, fx₂, fy₁, fy₂, hfx, hfy, _, _, hk => by
    rcases fx₁ with ⟨a₁, ⟨⟩⟩; rcases fx₂ with ⟨a₂, ⟨⟩⟩
    rcases fy₁ with ⟨b₁, ⟨⟩⟩; rcases fy₂ with ⟨b₂, ⟨⟩⟩
    cases hfx with | cons ha _ => cases hfy with | cons hb _ =>
    exact Wf.let2 _ ha hb fun h1 r₁ r₂ hr => hk h1 _ _ (TRel.single hr)
  | .pair t1 t2, _, _, xs₁, xs₂, ys₁, ys₂, hxs, hys, k₁, k₂, hk =>
    splitLegalToLeaves_wf target (.pair t1 t2) hxs fun hG1 fx₁ fx₂ hfx =>
    splitLegalToLeaves_wf target (.pair t1 t2) (TRel_argRel_weaken' hG1 hys) fun hG2 fy₁ fy₂ hfy =>
    legalFCmpTree_goFCmp_wf target o (.pair t1 t2) (TRel_argRel_weaken' hG2 hfx) hfy fun hG3 mr₁ mr₂ hmr =>
    packLeavesToLegal_wf target (Ty.mask (.pair t1 t2)) hmr fun hG4 y₁ y₂ hy =>
      hk (sub_trans hG1 (sub_trans hG2 (sub_trans hG3 hG4))) y₁ y₂ hy

private theorem legalSimdScalar128_go_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {on128₁ : Arg V₁ i32 → Arg V₁ i32 → Arg V₁ i32 → Arg V₁ i32 →
              Arg V₁ i32 → Arg V₁ i32 → Arg V₁ i32 → Arg V₁ i32 →
              (Arg V₁ i32 → Arg V₁ i32 → Arg V₁ i32 → Arg V₁ i32 → Expr V₁ L₁ rs) → Expr V₁ L₁ rs}
    {on128₂ : Arg V₂ i32 → Arg V₂ i32 → Arg V₂ i32 → Arg V₂ i32 →
              Arg V₂ i32 → Arg V₂ i32 → Arg V₂ i32 → Arg V₂ i32 →
              (Arg V₂ i32 → Arg V₂ i32 → Arg V₂ i32 → Arg V₂ i32 → Expr V₂ L₂ rs) → Expr V₂ L₂ rs}
    (hon : ∀ {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
      {a0₁ a1₁ a2₁ a3₁ b0₁ b1₁ b2₁ b3₁ : Arg V₁ i32}
      {a0₂ a1₂ a2₂ a3₂ b0₂ b1₂ b2₂ b3₂ : Arg V₂ i32}
      {cont₁ : Arg V₁ i32 → Arg V₁ i32 → Arg V₁ i32 → Arg V₁ i32 → Expr V₁ L₁ rs}
      {cont₂ : Arg V₂ i32 → Arg V₂ i32 → Arg V₂ i32 → Arg V₂ i32 → Expr V₂ L₂ rs},
      ArgRel G i32 a0₁ a0₂ → ArgRel G i32 a1₁ a1₂ → ArgRel G i32 a2₁ a2₂ → ArgRel G i32 a3₁ a3₂ →
      ArgRel G i32 b0₁ b0₂ → ArgRel G i32 b1₁ b1₂ → ArgRel G i32 b2₁ b2₂ → ArgRel G i32 b3₁ b3₂ →
      (∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ r0₁ r1₁ r2₁ r3₁ r0₂ r1₂ r2₂ r3₂,
        ArgRel G' i32 r0₁ r0₂ → ArgRel G' i32 r1₁ r1₂ → ArgRel G' i32 r2₁ r2₂ → ArgRel G' i32 r3₁ r3₂ →
        Wf G' D (cont₁ r0₁ r1₁ r2₁ r3₁) (cont₂ r0₂ r1₂ r2₂ r3₂)) →
      Wf G D (on128₁ a0₁ a1₁ a2₁ a3₁ b0₁ b1₁ b2₁ b3₁ cont₁)
             (on128₂ a0₂ a1₂ a2₂ a3₂ b0₂ b1₂ b2₂ b3₂ cont₂))
    (t : Ty) {G0 : Ctx V₁ V₂} {D : Ctx L₁ L₂}
    {k₁ : Tup (Arg V₁) (target.legalTys t) → Expr V₁ L₁ rs}
    {k₂ : Tup (Arg V₂) (target.legalTys t) → Expr V₂ L₂ rs}
    (hk : ∀ {G'}, (∀ p ∈ G0, p ∈ G') → ∀ y₁ y₂, TRel (ArgRel G') y₁ y₂ → Wf G' D (k₁ y₁) (k₂ y₂)) :
    ∀ (wx'₁ : List (Arg V₁ i64)) {G' : Ctx V₁ V₂} {wx'₂ : List (Arg V₂ i64)}
      {wy'₁ : List (Arg V₁ i64)} {wy'₂ : List (Arg V₂ i64)}
      {acc₁ : List (Arg V₁ i64)} {acc₂ : List (Arg V₂ i64)},
      ListRel (ArgRel G' i64) wx'₁ wx'₂ →
      ListRel (ArgRel G' i64) wy'₁ wy'₂ →
      ListRel (ArgRel G' i64) acc₁ acc₂ →
      (∀ p ∈ G0, p ∈ G') →
      Wf G' D
        (legalSimdScalar128.goWords target on128₁ t k₁ wx'₁ wy'₁ acc₁)
        (legalSimdScalar128.goWords target on128₂ t k₂ wx'₂ wy'₂ acc₂)
  | [], _, _, _, _, _, _, .nil, _, hacc, hsub =>
    unpackWords64ToLeaves_wf target t hacc 0 fun hG5 _ _ hfr =>
      packLeavesToLegal_wf target t hfr fun hG6 y₁ y₂ hy =>
        hk (sub_trans hsub (sub_trans hG5 hG6)) y₁ y₂ hy
  | [_], _, _, _, _, _, _, .cons _ .nil, _, hacc, hsub =>
    unpackWords64ToLeaves_wf target t hacc 0 fun hG5 _ _ hfr =>
      packLeavesToLegal_wf target t hfr fun hG6 y₁ y₂ hy =>
        hk (sub_trans hsub (sub_trans hG5 hG6)) y₁ y₂ hy
  | _ :: _ :: rx₁, _G', _ :: _ :: _rx₂, wy'₁, wy'₂, _acc₁, _acc₂,
      .cons hx0 (.cons hx1 hrest), hwy', hacc, hsub =>
    match wy'₁, wy'₂, hwy' with
    | [], _, .nil =>
      unpackWords64ToLeaves_wf target t hacc 0 fun hG5 _ _ hfr =>
        packLeavesToLegal_wf target t hfr fun hG6 y₁ y₂ hy =>
          hk (sub_trans hsub (sub_trans hG5 hG6)) y₁ y₂ hy
    | [_], _, .cons _ .nil =>
      unpackWords64ToLeaves_wf target t hacc 0 fun hG5 _ _ hfr =>
        packLeavesToLegal_wf target t hfr fun hG6 y₁ y₂ hy =>
          hk (sub_trans hsub (sub_trans hG5 hG6)) y₁ y₂ hy
    | _ :: _ :: _, _ :: _ :: _, .cons hy0 (.cons hy1 hwyrest) =>
      words2ToDwords4_wf hx0 hx1 fun hGa _a0₁ _a1₁ _a2₁ _a3₁ _a0₂ _a1₂ _a2₂ _a3₂ ha0 ha1 ha2 ha3 =>
      words2ToDwords4_wf (hy0.weaken hGa) (hy1.weaken hGa) fun hGb _b0₁ _b1₁ _b2₁ _b3₁ _b0₂ _b1₂ _b2₂ _b3₂ hb0 hb1 hb2 hb3 =>
      hon (ha0.weaken hGb) (ha1.weaken hGb) (ha2.weaken hGb) (ha3.weaken hGb) hb0 hb1 hb2 hb3
        fun hGc _r0₁ _r1₁ _r2₁ _r3₁ _r0₂ _r1₂ _r2₂ _r3₂ hr0 hr1 hr2 hr3 =>
      dwords4ToWords2_wf hr0 hr1 hr2 hr3 fun hGd _w0₁ _w1₁ _w0₂ _w1₂ hw0 hw1 =>
      have hsd := sub_trans hGa (sub_trans hGb (sub_trans hGc hGd))
      legalSimdScalar128_go_wf hon t hk rx₁
        (listRel_weaken hsd hrest) (listRel_weaken hsd hwyrest)
        ((listRel_weaken hsd hacc).append (.cons hw0 (.cons hw1 .nil)))
        (sub_trans hsub hsd)

theorem legalSimdScalar128_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {on128₁ : Arg V₁ i32 → Arg V₁ i32 → Arg V₁ i32 → Arg V₁ i32 →
              Arg V₁ i32 → Arg V₁ i32 → Arg V₁ i32 → Arg V₁ i32 →
              (Arg V₁ i32 → Arg V₁ i32 → Arg V₁ i32 → Arg V₁ i32 → Expr V₁ L₁ rs) → Expr V₁ L₁ rs}
    {on128₂ : Arg V₂ i32 → Arg V₂ i32 → Arg V₂ i32 → Arg V₂ i32 →
              Arg V₂ i32 → Arg V₂ i32 → Arg V₂ i32 → Arg V₂ i32 →
              (Arg V₂ i32 → Arg V₂ i32 → Arg V₂ i32 → Arg V₂ i32 → Expr V₂ L₂ rs) → Expr V₂ L₂ rs}
    (hon : ∀ {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
      {a0₁ a1₁ a2₁ a3₁ b0₁ b1₁ b2₁ b3₁ : Arg V₁ i32}
      {a0₂ a1₂ a2₂ a3₂ b0₂ b1₂ b2₂ b3₂ : Arg V₂ i32}
      {cont₁ : Arg V₁ i32 → Arg V₁ i32 → Arg V₁ i32 → Arg V₁ i32 → Expr V₁ L₁ rs}
      {cont₂ : Arg V₂ i32 → Arg V₂ i32 → Arg V₂ i32 → Arg V₂ i32 → Expr V₂ L₂ rs},
      ArgRel G i32 a0₁ a0₂ → ArgRel G i32 a1₁ a1₂ → ArgRel G i32 a2₁ a2₂ → ArgRel G i32 a3₁ a3₂ →
      ArgRel G i32 b0₁ b0₂ → ArgRel G i32 b1₁ b1₂ → ArgRel G i32 b2₁ b2₂ → ArgRel G i32 b3₁ b3₂ →
      (∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ r0₁ r1₁ r2₁ r3₁ r0₂ r1₂ r2₂ r3₂,
        ArgRel G' i32 r0₁ r0₂ → ArgRel G' i32 r1₁ r1₂ → ArgRel G' i32 r2₁ r2₂ → ArgRel G' i32 r3₁ r3₂ →
        Wf G' D (cont₁ r0₁ r1₁ r2₁ r3₁) (cont₂ r0₂ r1₂ r2₂ r3₂)) →
      Wf G D (on128₁ a0₁ a1₁ a2₁ a3₁ b0₁ b1₁ b2₁ b3₁ cont₁)
             (on128₂ a0₂ a1₂ a2₂ a3₂ b0₂ b1₂ b2₂ b3₂ cont₂))
    (t : Ty) {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
    {xs₁ : Tup (Arg V₁) (target.legalTys t)} {xs₂ : Tup (Arg V₂) (target.legalTys t)}
    {ys₁ : Tup (Arg V₁) (target.legalTys t)} {ys₂ : Tup (Arg V₂) (target.legalTys t)}
    (hxs : TRel (ArgRel G) xs₁ xs₂) (hys : TRel (ArgRel G) ys₁ ys₂)
    {k₁ : Tup (Arg V₁) (target.legalTys t) → Expr V₁ L₁ rs}
    {k₂ : Tup (Arg V₂) (target.legalTys t) → Expr V₂ L₂ rs}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, TRel (ArgRel G') y₁ y₂ → Wf G' D (k₁ y₁) (k₂ y₂)) :
    Wf G D (legalSimdScalar128 target on128₁ t xs₁ ys₁ k₁)
           (legalSimdScalar128 target on128₂ t xs₂ ys₂ k₂) := by
  refine splitLegalToLeaves_wf target t hxs fun hG1 fx₁ fx₂ hfx =>
    splitLegalToLeaves_wf target t (TRel_argRel_weaken' hG1 hys) fun hG2 fy₁ fy₂ hfy =>
      packLeavesToWords64_wf target t (TRel_argRel_weaken' hG2 hfx) fun hG3 wx₁ wx₂ hwx =>
        packLeavesToWords64_wf target t (TRel_argRel_weaken' hG3 hfy) fun hG4 wy₁ wy₂ hwy =>
          legalSimdScalar128_go_wf target hon t hk _ (listRel_weaken hG4 hwx) hwy .nil
            (sub_trans hG1 (sub_trans hG2 (sub_trans hG3 hG4)))

theorem legalShufd_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    (imm : BitVec 8) :
    ∀ (t : Ty) {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
      {xs₁ : Tup (Arg V₁) (target.legalTys t)} {xs₂ : Tup (Arg V₂) (target.legalTys t)},
      TRel (ArgRel G) xs₁ xs₂ →
      ∀ {k₁ : Tup (Arg V₁) (target.legalTys t) → Expr V₁ L₁ rs}
        {k₂ : Tup (Arg V₂) (target.legalTys t) → Expr V₂ L₂ rs},
      (∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, TRel (ArgRel G') y₁ y₂ → Wf G' D (k₁ y₁) (k₂ y₂)) →
      Wf G D (legalShufd target imm t xs₁ k₁) (legalShufd target imm t xs₂ k₂) := by
  have h128 : ∀ {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
      {a0₁ a1₁ a2₁ a3₁ b0₁ b1₁ b2₁ b3₁ : Arg V₁ i32}
      {a0₂ a1₂ a2₂ a3₂ b0₂ b1₂ b2₂ b3₂ : Arg V₂ i32}
      {cont₁ : Arg V₁ i32 → Arg V₁ i32 → Arg V₁ i32 → Arg V₁ i32 → Expr V₁ L₁ rs}
      {cont₂ : Arg V₂ i32 → Arg V₂ i32 → Arg V₂ i32 → Arg V₂ i32 → Expr V₂ L₂ rs},
      ArgRel G i32 a0₁ a0₂ → ArgRel G i32 a1₁ a1₂ → ArgRel G i32 a2₁ a2₂ → ArgRel G i32 a3₁ a3₂ →
      ArgRel G i32 b0₁ b0₂ → ArgRel G i32 b1₁ b1₂ → ArgRel G i32 b2₁ b2₂ → ArgRel G i32 b3₁ b3₂ →
      (∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ r0₁ r1₁ r2₁ r3₁ r0₂ r1₂ r2₂ r3₂,
        ArgRel G' i32 r0₁ r0₂ → ArgRel G' i32 r1₁ r1₂ → ArgRel G' i32 r2₁ r2₂ → ArgRel G' i32 r3₁ r3₂ →
        Wf G' D (cont₁ r0₁ r1₁ r2₁ r3₁) (cont₂ r0₂ r1₂ r2₂ r3₂)) →
      Wf G D (let (r0, r1, r2, r3) := scalarShufd128 imm a0₁ a1₁ a2₁ a3₁; cont₁ r0 r1 r2 r3)
             (let (r0, r1, r2, r3) := scalarShufd128 imm a0₂ a1₂ a2₂ a3₂; cont₂ r0 r1 r2 r3) := by
    intro G D a0₁ a1₁ a2₁ a3₁ _ _ _ _ a0₂ a1₂ a2₂ a3₂ _ _ _ _ cont₁ cont₂ ha0 ha1 ha2 ha3 _ _ _ _ hcont
    exact hcont (fun _ p => p) _ _ _ _ _ _ _ _
      (by dsimp only; split <;> assumption)
      (by dsimp only; split <;> assumption)
      (by dsimp only; split <;> assumption)
      (by dsimp only; split <;> assumption)
  intro t G D xs₁ xs₂ hxs k₁ k₂ hk
  induction t generalizing G with
  | bool | bits _ | float _ =>
    simp only [legalShufd]
    split
    · exact .hlt
    · exact legalSimdScalar128_wf target h128 _ hxs hxs hk
  | pair a b iha ihb =>
    simp only [legalShufd]
    split
    · exact .hlt
    · split
      · next h =>
        obtain ⟨hx1, _⟩ := TRel.cons_iff.1 (packedToTup_rel h hxs)
        split
        · exact Wf.let1 (.shufd (.pair a b) imm) hx1 fun hG' r₁ r₂ hr =>
            hk hG' _ _ (tupToPacked_rel h (.cons hr .nil))
        · exact legalSimdScalar128_wf target h128 (.pair a b) hxs hxs hk
      · next h =>
        split
        · have hff := Bool.eq_false_iff.mpr h
          obtain ⟨xa, xb⟩ := TRel_tupSplit (splitToTup_rel hff hxs)
          exact iha xa fun hG1 ra₁ ra₂ hra =>
            ihb (TRel_argRel_weaken' hG1 xb) fun hG2 rb₁ rb₂ hrb =>
              hk (sub_trans hG1 hG2) _ _
                (tupToSplit_rel hff (TRel_tupAppend (TRel_argRel_weaken' hG2 hra) hrb))
        · exact legalSimdScalar128_wf target h128 (.pair a b) hxs hxs hk

theorem legalBlendw_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    (imm : BitVec 8) :
    ∀ (t : Ty) {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
      {xs₁ : Tup (Arg V₁) (target.legalTys t)} {xs₂ : Tup (Arg V₂) (target.legalTys t)}
      {ys₁ : Tup (Arg V₁) (target.legalTys t)} {ys₂ : Tup (Arg V₂) (target.legalTys t)},
      TRel (ArgRel G) xs₁ xs₂ → TRel (ArgRel G) ys₁ ys₂ →
      ∀ {k₁ : Tup (Arg V₁) (target.legalTys t) → Expr V₁ L₁ rs}
        {k₂ : Tup (Arg V₂) (target.legalTys t) → Expr V₂ L₂ rs},
      (∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, TRel (ArgRel G') y₁ y₂ → Wf G' D (k₁ y₁) (k₂ y₂)) →
      Wf G D (legalBlendw target imm t xs₁ ys₁ k₁) (legalBlendw target imm t xs₂ ys₂ k₂) := by
  intro t G D xs₁ xs₂ ys₁ ys₂ hxs hys k₁ k₂ hk
  induction t generalizing G with
  | bool | bits _ | float _ =>
    simp only [legalBlendw]
    split
    · exact .hlt
    · exact legalSimdScalar128_wf target (fun ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 cont =>
        scalarBlendw128_wf imm ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 cont) _ hxs hys hk
  | pair a b iha ihb =>
    simp only [legalBlendw]
    split
    · exact .hlt
    · split
      · next h =>
        obtain ⟨hx1, _⟩ := TRel.cons_iff.1 (packedToTup_rel h hxs)
        obtain ⟨hy1, _⟩ := TRel.cons_iff.1 (packedToTup_rel h hys)
        split
        · exact Wf.let2 (.blendw (.pair a b) imm) hx1 hy1 fun hG' r₁ r₂ hr =>
            hk hG' _ _ (tupToPacked_rel h (.cons hr .nil))
        · exact legalSimdScalar128_wf target (fun ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 cont =>
            scalarBlendw128_wf imm ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 cont) (.pair a b) hxs hys hk
      · next h =>
        split
        · have hff := Bool.eq_false_iff.mpr h
          obtain ⟨xa, xb⟩ := TRel_tupSplit (splitToTup_rel hff hxs)
          obtain ⟨ya, yb⟩ := TRel_tupSplit (splitToTup_rel hff hys)
          exact iha xa ya fun hG1 ra₁ ra₂ hra =>
            ihb (TRel_argRel_weaken' hG1 xb) (TRel_argRel_weaken' hG1 yb) fun hG2 rb₁ rb₂ hrb =>
              hk (sub_trans hG1 hG2) _ _
                (tupToSplit_rel hff (TRel_tupAppend (TRel_argRel_weaken' hG2 hra) hrb))
        · exact legalSimdScalar128_wf target (fun ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 cont =>
            scalarBlendw128_wf imm ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 cont) (.pair a b) hxs hys hk

theorem legalAlignr_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    (imm : BitVec 8) :
    ∀ (t : Ty) {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
      {xs₁ : Tup (Arg V₁) (target.legalTys t)} {xs₂ : Tup (Arg V₂) (target.legalTys t)}
      {ys₁ : Tup (Arg V₁) (target.legalTys t)} {ys₂ : Tup (Arg V₂) (target.legalTys t)},
      TRel (ArgRel G) xs₁ xs₂ → TRel (ArgRel G) ys₁ ys₂ →
      ∀ {k₁ : Tup (Arg V₁) (target.legalTys t) → Expr V₁ L₁ rs}
        {k₂ : Tup (Arg V₂) (target.legalTys t) → Expr V₂ L₂ rs},
      (∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, TRel (ArgRel G') y₁ y₂ → Wf G' D (k₁ y₁) (k₂ y₂)) →
      Wf G D (legalAlignr target imm t xs₁ ys₁ k₁) (legalAlignr target imm t xs₂ ys₂ k₂) := by
  intro t G D xs₁ xs₂ ys₁ ys₂ hxs hys k₁ k₂ hk
  induction t generalizing G with
  | bool | bits _ | float _ =>
    simp only [legalAlignr]
    split
    · exact .hlt
    · exact legalSimdScalar128_wf target (fun hh0 hh1 hh2 hh3 hl0 hl1 hl2 hl3 cont =>
        scalarAlignr128_wf imm hh0 hh1 hh2 hh3 hl0 hl1 hl2 hl3 cont) _ hxs hys hk
  | pair a b iha ihb =>
    simp only [legalAlignr]
    split
    · exact .hlt
    · split
      · next h =>
        obtain ⟨hx1, _⟩ := TRel.cons_iff.1 (packedToTup_rel h hxs)
        obtain ⟨hy1, _⟩ := TRel.cons_iff.1 (packedToTup_rel h hys)
        split
        · exact Wf.let2 (.alignr (.pair a b) imm) hx1 hy1 fun hG' r₁ r₂ hr =>
            hk hG' _ _ (tupToPacked_rel h (.cons hr .nil))
        · exact legalSimdScalar128_wf target (fun hh0 hh1 hh2 hh3 hl0 hl1 hl2 hl3 cont =>
            scalarAlignr128_wf imm hh0 hh1 hh2 hh3 hl0 hl1 hl2 hl3 cont) (.pair a b) hxs hys hk
      · next h =>
        split
        · have hff := Bool.eq_false_iff.mpr h
          obtain ⟨xa, xb⟩ := TRel_tupSplit (splitToTup_rel hff hxs)
          obtain ⟨ya, yb⟩ := TRel_tupSplit (splitToTup_rel hff hys)
          exact iha xa ya fun hG1 ra₁ ra₂ hra =>
            ihb (TRel_argRel_weaken' hG1 xb) (TRel_argRel_weaken' hG1 yb) fun hG2 rb₁ rb₂ hrb =>
              hk (sub_trans hG1 hG2) _ _
                (tupToSplit_rel hff (TRel_tupAppend (TRel_argRel_weaken' hG2 hra) hrb))
        · exact legalSimdScalar128_wf target (fun hh0 hh1 hh2 hh3 hl0 hl1 hl2 hl3 cont =>
            scalarAlignr128_wf imm hh0 hh1 hh2 hh3 hl0 hl1 hl2 hl3 cont) (.pair a b) hxs hys hk

theorem legalShufb_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty} :
    ∀ (t : Ty) {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
      {xs₁ : Tup (Arg V₁) (target.legalTys t)} {xs₂ : Tup (Arg V₂) (target.legalTys t)}
      {ys₁ : Tup (Arg V₁) (target.legalTys t)} {ys₂ : Tup (Arg V₂) (target.legalTys t)},
      TRel (ArgRel G) xs₁ xs₂ → TRel (ArgRel G) ys₁ ys₂ →
      ∀ {k₁ : Tup (Arg V₁) (target.legalTys t) → Expr V₁ L₁ rs}
        {k₂ : Tup (Arg V₂) (target.legalTys t) → Expr V₂ L₂ rs},
      (∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, TRel (ArgRel G') y₁ y₂ → Wf G' D (k₁ y₁) (k₂ y₂)) →
      Wf G D (legalShufb target t xs₁ ys₁ k₁) (legalShufb target t xs₂ ys₂ k₂) := by
  intro t G D xs₁ xs₂ ys₁ ys₂ hxs hys k₁ k₂ hk
  induction t generalizing G with
  | bool | bits _ | float _ =>
    simp only [legalShufb]
    split
    · exact .hlt
    · exact legalSimdScalar128_wf target (fun ha0 ha1 ha2 ha3 hm0 hm1 hm2 hm3 cont =>
        scalarShufb128_wf ha0 ha1 ha2 ha3 hm0 hm1 hm2 hm3 cont) _ hxs hys hk
  | pair a b iha ihb =>
    simp only [legalShufb]
    split
    · exact .hlt
    · split
      · next h =>
        obtain ⟨hx1, _⟩ := TRel.cons_iff.1 (packedToTup_rel h hxs)
        obtain ⟨hy1, _⟩ := TRel.cons_iff.1 (packedToTup_rel h hys)
        split
        · exact Wf.let2 (.shufb (.pair a b)) hx1 hy1 fun hG' r₁ r₂ hr =>
            hk hG' _ _ (tupToPacked_rel h (.cons hr .nil))
        · exact legalSimdScalar128_wf target (fun ha0 ha1 ha2 ha3 hm0 hm1 hm2 hm3 cont =>
            scalarShufb128_wf ha0 ha1 ha2 ha3 hm0 hm1 hm2 hm3 cont) (.pair a b) hxs hys hk
      · next h =>
        split
        · have hff := Bool.eq_false_iff.mpr h
          obtain ⟨xa, xb⟩ := TRel_tupSplit (splitToTup_rel hff hxs)
          obtain ⟨ya, yb⟩ := TRel_tupSplit (splitToTup_rel hff hys)
          exact iha xa ya fun hG1 ra₁ ra₂ hra =>
            ihb (TRel_argRel_weaken' hG1 xb) (TRel_argRel_weaken' hG1 yb) fun hG2 rb₁ rb₂ hrb =>
              hk (sub_trans hG1 hG2) _ _
                (tupToSplit_rel hff (TRel_tupAppend (TRel_argRel_weaken' hG2 hra) hrb))
        · exact legalSimdScalar128_wf target (fun ha0 ha1 ha2 ha3 hm0 hm1 hm2 hm3 cont =>
            scalarShufb128_wf ha0 ha1 ha2 ha3 hm0 hm1 hm2 hm3 cont) (.pair a b) hxs hys hk

theorem legalFloatBit2_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
    (mkOp : (w : Nat) → OpCode [.bits w, .bits w] [.bits w])
    (mkFOp : (f : Fmt) → OpCode [.float f, .float f] [.float f])
    (f : Fmt) {x₁ y₁ : Arg V₁ (.float f)} {x₂ y₂ : Arg V₂ (.float f)}
    (hx : ArgRel G (.float f) x₁ x₂) (hy : ArgRel G (.float f) y₁ y₂)
    {k₁ : Arg V₁ (.float f) → Expr V₁ L₁ rs} {k₂ : Arg V₂ (.float f) → Expr V₂ L₂ rs}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ r₁ r₂, ArgRel G' (.float f) r₁ r₂ → Wf G' D (k₁ r₁) (k₂ r₂)) :
    Wf G D (legalFloatBit2 target mkOp mkFOp f x₁ y₁ k₁)
           (legalFloatBit2 target mkOp mkFOp f x₂ y₂ k₂) := by
  simp only [legalFloatBit2]
  split
  · exact Wf.let2 (mkFOp f) hx hy hk
  · exact Wf.let1 _ hx fun h1 bx₁ bx₂ hbx =>
      Wf.let1 _ (hy.weaken h1) fun h2 by₁ by₂ hby =>
        Wf.let2 (mkOp f.width) (hbx.weaken h2) hby fun h3 br₁ br₂ hbr =>
          Wf.let1 _ hbr fun h4 r₁ r₂ hr =>
            hk (sub_trans h1 (sub_trans h2 (sub_trans h3 h4))) r₁ r₂ hr

private theorem sha256rnds2_scalar_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
    {lc₁ la₁ lw₁ : Tup (Arg V₁) (target.legalTys v4i32)}
    {lc₂ la₂ lw₂ : Tup (Arg V₂) (target.legalTys v4i32)}
    (hlc : TRel (ArgRel G) lc₁ lc₂) (hla : TRel (ArgRel G) la₁ la₂) (hlw : TRel (ArgRel G) lw₁ lw₂)
    {c₁ : Tup (Arg V₁) (target.legalTys v4i32) → Expr V₁ L₁ rs}
    {c₂ : Tup (Arg V₂) (target.legalTys v4i32) → Expr V₂ L₂ rs}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, TRel (ArgRel G') y₁ y₂ → Wf G' D (c₁ y₁) (c₂ y₂)) :
    Wf G D
      (splitLegalToLeaves target v4i32 lc₁ fun fc =>
       splitLegalToLeaves target v4i32 la₁ fun fa =>
       splitLegalToLeaves target v4i32 lw₁ fun fw =>
       packLeavesToWords64 target v4i32 fc fun wc =>
       packLeavesToWords64 target v4i32 fa fun wa =>
       packLeavesToWords64 target v4i32 fw fun ww =>
       words2ToDwords4 (wc.getD 0 (.imm 0#64)) (wc.getD 1 (.imm 0#64)) fun cd0 cd1 cd2 cd3 =>
       words2ToDwords4 (wa.getD 0 (.imm 0#64)) (wa.getD 1 (.imm 0#64)) fun ab0 ab1 ab2 ab3 =>
       words2ToDwords4 (ww.getD 0 (.imm 0#64)) (ww.getD 1 (.imm 0#64)) fun wk0 wk1 wk2 wk3 =>
       scalarSha256rnds2 cd0 cd1 cd2 cd3 ab0 ab1 ab2 ab3 wk0 wk1 wk2 wk3 fun r0 r1 r2 r3 =>
       dwords4ToWords2 r0 r1 r2 r3 fun w0 w1 =>
       unpackWords64ToLeaves target [w0, w1] 0 v4i32 fun fres =>
       packLeavesToLegal target v4i32 fres c₁)
      (splitLegalToLeaves target v4i32 lc₂ fun fc =>
       splitLegalToLeaves target v4i32 la₂ fun fa =>
       splitLegalToLeaves target v4i32 lw₂ fun fw =>
       packLeavesToWords64 target v4i32 fc fun wc =>
       packLeavesToWords64 target v4i32 fa fun wa =>
       packLeavesToWords64 target v4i32 fw fun ww =>
       words2ToDwords4 (wc.getD 0 (.imm 0#64)) (wc.getD 1 (.imm 0#64)) fun cd0 cd1 cd2 cd3 =>
       words2ToDwords4 (wa.getD 0 (.imm 0#64)) (wa.getD 1 (.imm 0#64)) fun ab0 ab1 ab2 ab3 =>
       words2ToDwords4 (ww.getD 0 (.imm 0#64)) (ww.getD 1 (.imm 0#64)) fun wk0 wk1 wk2 wk3 =>
       scalarSha256rnds2 cd0 cd1 cd2 cd3 ab0 ab1 ab2 ab3 wk0 wk1 wk2 wk3 fun r0 r1 r2 r3 =>
       dwords4ToWords2 r0 r1 r2 r3 fun w0 w1 =>
       unpackWords64ToLeaves target [w0, w1] 0 v4i32 fun fres =>
       packLeavesToLegal target v4i32 fres c₂) :=
  splitLegalToLeaves_wf target v4i32 hlc fun p0 _fc₁ _fc₂ hfc =>
  splitLegalToLeaves_wf target v4i32 (TRel_argRel_weaken' p0 hla) fun p1 _fa₁ _fa₂ hfa =>
  splitLegalToLeaves_wf target v4i32 (TRel_argRel_weaken' (sub_trans p0 p1) hlw) fun p2 _fw₁ _fw₂ hfw =>
  packLeavesToWords64_wf target v4i32 (TRel_argRel_weaken' (sub_trans p1 p2) hfc) fun p3 _wc₁ _wc₂ hwc =>
  packLeavesToWords64_wf target v4i32 (TRel_argRel_weaken' (sub_trans p2 p3) hfa) fun p4 _wa₁ _wa₂ hwa =>
  packLeavesToWords64_wf target v4i32 (TRel_argRel_weaken' (sub_trans p3 p4) hfw) fun p5 _ww₁ _ww₂ hww =>
  have q5 := sub_trans p0 (sub_trans p1 (sub_trans p2 (sub_trans p3 (sub_trans p4 p5))))
  words2ToDwords4_wf ((listRel_weaken (sub_trans p4 p5) hwc).getD (ArgRel.imm (G := _) (0#64)) 0)
    ((listRel_weaken (sub_trans p4 p5) hwc).getD (ArgRel.imm (G := _) (0#64)) 1) fun p6 _cd0₁ _cd1₁ _cd2₁ _cd3₁ _cd0₂ _cd1₂ _cd2₂ _cd3₂ hcd0 hcd1 hcd2 hcd3 =>
  words2ToDwords4_wf ((listRel_weaken (sub_trans p5 p6) hwa).getD (ArgRel.imm (G := _) (0#64)) 0)
    ((listRel_weaken (sub_trans p5 p6) hwa).getD (ArgRel.imm (G := _) (0#64)) 1) fun p7 _ab0₁ _ab1₁ _ab2₁ _ab3₁ _ab0₂ _ab1₂ _ab2₂ _ab3₂ hab0 hab1 hab2 hab3 =>
  words2ToDwords4_wf ((listRel_weaken (sub_trans p6 p7) hww).getD (ArgRel.imm (G := _) (0#64)) 0)
    ((listRel_weaken (sub_trans p6 p7) hww).getD (ArgRel.imm (G := _) (0#64)) 1) fun p8 _wk0₁ _wk1₁ _wk2₁ _wk3₁ _wk0₂ _wk1₂ _wk2₂ _wk3₂ hwk0 hwk1 _hwk2 _hwk3 =>
  have q8 := sub_trans q5 (sub_trans p6 (sub_trans p7 p8))
  scalarSha256rnds2_wf (hcd0.weaken (sub_trans p7 p8)) (hcd1.weaken (sub_trans p7 p8))
    (hcd2.weaken (sub_trans p7 p8)) (hcd3.weaken (sub_trans p7 p8))
    (hab0.weaken p8) (hab1.weaken p8) (hab2.weaken p8) (hab3.weaken p8) hwk0 hwk1
    fun p9 _r0₁ _r1₁ _r2₁ _r3₁ _r0₂ _r1₂ _r2₂ _r3₂ hr0 hr1 hr2 hr3 =>
  dwords4ToWords2_wf hr0 hr1 hr2 hr3 fun pa _w0₁ _w1₁ _w0₂ _w1₂ hw0 hw1 =>
  unpackWords64ToLeaves_wf target v4i32 (.cons hw0 (.cons hw1 .nil)) 0 fun pb _fres₁ _fres₂ hfres =>
  packLeavesToLegal_wf target v4i32 hfres fun pc y₁ y₂ hy =>
    hk (sub_trans q8 (sub_trans p9 (sub_trans pa (sub_trans pb pc)))) y₁ y₂ hy

private theorem sha256msg1_scalar_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
    {la₁ lb₁ : Tup (Arg V₁) (target.legalTys v4i32)}
    {la₂ lb₂ : Tup (Arg V₂) (target.legalTys v4i32)}
    (hla : TRel (ArgRel G) la₁ la₂) (hlb : TRel (ArgRel G) lb₁ lb₂)
    {c₁ : Tup (Arg V₁) (target.legalTys v4i32) → Expr V₁ L₁ rs}
    {c₂ : Tup (Arg V₂) (target.legalTys v4i32) → Expr V₂ L₂ rs}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, TRel (ArgRel G') y₁ y₂ → Wf G' D (c₁ y₁) (c₂ y₂)) :
    Wf G D
      (splitLegalToLeaves target v4i32 la₁ fun fa =>
       splitLegalToLeaves target v4i32 lb₁ fun fb =>
       packLeavesToWords64 target v4i32 fa fun wa =>
       packLeavesToWords64 target v4i32 fb fun wb =>
       words2ToDwords4 (wa.getD 0 (.imm 0#64)) (wa.getD 1 (.imm 0#64)) fun a0 a1 a2 a3 =>
       words2ToDwords4 (wb.getD 0 (.imm 0#64)) (wb.getD 1 (.imm 0#64)) fun b0 b1 b2 b3 =>
       scalarSha256msg1 a0 a1 a2 a3 b0 b1 b2 b3 fun r0 r1 r2 r3 =>
       dwords4ToWords2 r0 r1 r2 r3 fun w0 w1 =>
       unpackWords64ToLeaves target [w0, w1] 0 v4i32 fun fres =>
       packLeavesToLegal target v4i32 fres c₁)
      (splitLegalToLeaves target v4i32 la₂ fun fa =>
       splitLegalToLeaves target v4i32 lb₂ fun fb =>
       packLeavesToWords64 target v4i32 fa fun wa =>
       packLeavesToWords64 target v4i32 fb fun wb =>
       words2ToDwords4 (wa.getD 0 (.imm 0#64)) (wa.getD 1 (.imm 0#64)) fun a0 a1 a2 a3 =>
       words2ToDwords4 (wb.getD 0 (.imm 0#64)) (wb.getD 1 (.imm 0#64)) fun b0 b1 b2 b3 =>
       scalarSha256msg1 a0 a1 a2 a3 b0 b1 b2 b3 fun r0 r1 r2 r3 =>
       dwords4ToWords2 r0 r1 r2 r3 fun w0 w1 =>
       unpackWords64ToLeaves target [w0, w1] 0 v4i32 fun fres =>
       packLeavesToLegal target v4i32 fres c₂) :=
  splitLegalToLeaves_wf target v4i32 hla fun p0 _fa₁ _fa₂ hfa =>
  splitLegalToLeaves_wf target v4i32 (TRel_argRel_weaken' p0 hlb) fun p1 _fb₁ _fb₂ hfb =>
  packLeavesToWords64_wf target v4i32 (TRel_argRel_weaken' p1 hfa) fun p2 _wa₁ _wa₂ hwa =>
  packLeavesToWords64_wf target v4i32 (TRel_argRel_weaken' p2 hfb) fun p3 _wb₁ _wb₂ hwb =>
  have q3 := sub_trans p0 (sub_trans p1 (sub_trans p2 p3))
  words2ToDwords4_wf ((listRel_weaken p3 hwa).getD (ArgRel.imm (G := _) (0#64)) 0)
    ((listRel_weaken p3 hwa).getD (ArgRel.imm (G := _) (0#64)) 1) fun p4 _a0₁ _a1₁ _a2₁ _a3₁ _a0₂ _a1₂ _a2₂ _a3₂ ha0 ha1 ha2 ha3 =>
  words2ToDwords4_wf ((listRel_weaken p4 hwb).getD (ArgRel.imm (G := _) (0#64)) 0)
    ((listRel_weaken p4 hwb).getD (ArgRel.imm (G := _) (0#64)) 1) fun p5 _b0₁ _b1₁ _b2₁ _b3₁ _b0₂ _b1₂ _b2₂ _b3₂ hb0 _hb1 _hb2 _hb3 =>
  scalarSha256msg1_wf (ha0.weaken p5) (ha1.weaken p5) (ha2.weaken p5) (ha3.weaken p5) hb0
    fun p6 _r0₁ _r1₁ _r2₁ _r3₁ _r0₂ _r1₂ _r2₂ _r3₂ hr0 hr1 hr2 hr3 =>
  dwords4ToWords2_wf hr0 hr1 hr2 hr3 fun p7 _w0₁ _w1₁ _w0₂ _w1₂ hw0 hw1 =>
  unpackWords64ToLeaves_wf target v4i32 (.cons hw0 (.cons hw1 .nil)) 0 fun p8 _fres₁ _fres₂ hfres =>
  packLeavesToLegal_wf target v4i32 hfres fun p9 y₁ y₂ hy =>
    hk (sub_trans q3 (sub_trans p4 (sub_trans p5 (sub_trans p6 (sub_trans p7 (sub_trans p8 p9)))))) y₁ y₂ hy

private theorem sha256msg2_scalar_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
    {la₁ lb₁ : Tup (Arg V₁) (target.legalTys v4i32)}
    {la₂ lb₂ : Tup (Arg V₂) (target.legalTys v4i32)}
    (hla : TRel (ArgRel G) la₁ la₂) (hlb : TRel (ArgRel G) lb₁ lb₂)
    {c₁ : Tup (Arg V₁) (target.legalTys v4i32) → Expr V₁ L₁ rs}
    {c₂ : Tup (Arg V₂) (target.legalTys v4i32) → Expr V₂ L₂ rs}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, TRel (ArgRel G') y₁ y₂ → Wf G' D (c₁ y₁) (c₂ y₂)) :
    Wf G D
      (splitLegalToLeaves target v4i32 la₁ fun fa =>
       splitLegalToLeaves target v4i32 lb₁ fun fb =>
       packLeavesToWords64 target v4i32 fa fun wa =>
       packLeavesToWords64 target v4i32 fb fun wb =>
       words2ToDwords4 (wa.getD 0 (.imm 0#64)) (wa.getD 1 (.imm 0#64)) fun s0 s1 s2 s3 =>
       words2ToDwords4 (wb.getD 0 (.imm 0#64)) (wb.getD 1 (.imm 0#64)) fun w0 w1 w2 w3 =>
       scalarSha256msg2 s0 s1 s2 s3 w0 w1 w2 w3 fun r0 r1 r2 r3 =>
       dwords4ToWords2 r0 r1 r2 r3 fun wr0 wr1 =>
       unpackWords64ToLeaves target [wr0, wr1] 0 v4i32 fun fres =>
       packLeavesToLegal target v4i32 fres c₁)
      (splitLegalToLeaves target v4i32 la₂ fun fa =>
       splitLegalToLeaves target v4i32 lb₂ fun fb =>
       packLeavesToWords64 target v4i32 fa fun wa =>
       packLeavesToWords64 target v4i32 fb fun wb =>
       words2ToDwords4 (wa.getD 0 (.imm 0#64)) (wa.getD 1 (.imm 0#64)) fun s0 s1 s2 s3 =>
       words2ToDwords4 (wb.getD 0 (.imm 0#64)) (wb.getD 1 (.imm 0#64)) fun w0 w1 w2 w3 =>
       scalarSha256msg2 s0 s1 s2 s3 w0 w1 w2 w3 fun r0 r1 r2 r3 =>
       dwords4ToWords2 r0 r1 r2 r3 fun wr0 wr1 =>
       unpackWords64ToLeaves target [wr0, wr1] 0 v4i32 fun fres =>
       packLeavesToLegal target v4i32 fres c₂) :=
  splitLegalToLeaves_wf target v4i32 hla fun p0 _fa₁ _fa₂ hfa =>
  splitLegalToLeaves_wf target v4i32 (TRel_argRel_weaken' p0 hlb) fun p1 _fb₁ _fb₂ hfb =>
  packLeavesToWords64_wf target v4i32 (TRel_argRel_weaken' p1 hfa) fun p2 _wa₁ _wa₂ hwa =>
  packLeavesToWords64_wf target v4i32 (TRel_argRel_weaken' p2 hfb) fun p3 _wb₁ _wb₂ hwb =>
  have q3 := sub_trans p0 (sub_trans p1 (sub_trans p2 p3))
  words2ToDwords4_wf ((listRel_weaken p3 hwa).getD (ArgRel.imm (G := _) (0#64)) 0)
    ((listRel_weaken p3 hwa).getD (ArgRel.imm (G := _) (0#64)) 1) fun p4 _s0₁ _s1₁ _s2₁ _s3₁ _s0₂ _s1₂ _s2₂ _s3₂ hs0 hs1 hs2 hs3 =>
  words2ToDwords4_wf ((listRel_weaken p4 hwb).getD (ArgRel.imm (G := _) (0#64)) 0)
    ((listRel_weaken p4 hwb).getD (ArgRel.imm (G := _) (0#64)) 1) fun p5 _w0₁ _w1₁ _w2₁ _w3₁ _w0₂ _w1₂ _w2₂ _w3₂ _hw0 _hw1 hw2 hw3 =>
  scalarSha256msg2_wf (hs0.weaken p5) (hs1.weaken p5) (hs2.weaken p5) (hs3.weaken p5) hw2 hw3
    fun p6 _r0₁ _r1₁ _r2₁ _r3₁ _r0₂ _r1₂ _r2₂ _r3₂ hr0 hr1 hr2 hr3 =>
  dwords4ToWords2_wf hr0 hr1 hr2 hr3 fun p7 _wr0₁ _wr1₁ _wr0₂ _wr1₂ hwr0 hwr1 =>
  unpackWords64ToLeaves_wf target v4i32 (.cons hwr0 (.cons hwr1 .nil)) 0 fun p8 _fres₁ _fres₂ hfres =>
  packLeavesToLegal_wf target v4i32 hfres fun p9 y₁ y₂ hy =>
    hk (sub_trans q3 (sub_trans p4 (sub_trans p5 (sub_trans p6 (sub_trans p7 (sub_trans p8 p9)))))) y₁ y₂ hy

theorem TRel.singleL {V₁ V₂ : Ty → Type} {G : Ctx V₁ V₂} {t : Ty}
    {x₁ : LVar target V₁ t} {x₂ : LVar target V₂ t} (h : TRel (ArgRel G) x₁ x₂) :
    TRel (fun _ a₁ a₂ => TRel (ArgRel G) a₁ a₂) (as := [t]) (x₁, PUnit.unit) (x₂, PUnit.unit) :=
  .cons h .nil

theorem TRel.pairL {V₁ V₂ : Ty → Type} {G : Ctx V₁ V₂} {t u : Ty}
    {x₁ : LVar target V₁ t} {x₂ : LVar target V₂ t}
    {y₁ : LVar target V₁ u} {y₂ : LVar target V₂ u}
    (hx : TRel (ArgRel G) x₁ x₂) (hy : TRel (ArgRel G) y₁ y₂) :
    TRel (fun _ a₁ a₂ => TRel (ArgRel G) a₁ a₂) (as := [t, u])
      (x₁, y₁, PUnit.unit) (x₂, y₂, PUnit.unit) :=
  .cons hx (.cons hy .nil)

private theorem trelBitsImmZero {V₁ V₂ : Ty → Type} {G : Ctx V₁ V₂} (n : Nat) :
    TRel (f := LVar target V₁) (g := LVar target V₂) (fun _ a₁ a₂ => TRel (ArgRel G) a₁ a₂) (as := [Ty.bits n])
      ((Arg.imm (0#(target.widenWidth n)), PUnit.unit), PUnit.unit)
      ((Arg.imm (0#(target.widenWidth n)), PUnit.unit), PUnit.unit) := by
  dsimp only [LVar]
  exact @TRel.singleL target V₁ V₂ G (.bits n) (Arg.imm (0#(target.widenWidth n)), PUnit.unit) _
    (TRel.single (ArgRel.imm _))

private theorem trelSingleBits {V₁ V₂ : Ty → Type} {G : Ctx V₁ V₂} (n : Nat)
    {x₁ : Arg V₁ (.bits (target.widenWidth n))} {x₂ : Arg V₂ (.bits (target.widenWidth n))}
    (h : ArgRel G (.bits (target.widenWidth n)) x₁ x₂) :
    TRel (f := LVar target V₁) (g := LVar target V₂) (fun _ a₁ a₂ => TRel (ArgRel G) a₁ a₂) (as := [Ty.bits n])
      ((x₁, PUnit.unit), PUnit.unit) ((x₂, PUnit.unit), PUnit.unit) := by
  dsimp only [LVar]
  exact @TRel.singleL target V₁ V₂ G (.bits n) (x₁, PUnit.unit) (x₂, PUnit.unit) (TRel.single h)

private theorem trelPairBits {V₁ V₂ : Ty → Type} {G : Ctx V₁ V₂} (n : Nat)
    {x₁ : Arg V₁ (.bits (target.widenWidth n))} {x₂ : Arg V₂ (.bits (target.widenWidth n))}
    {y₁ : Arg V₁ (.bits (target.widenWidth n))} {y₂ : Arg V₂ (.bits (target.widenWidth n))}
    (hx : ArgRel G (.bits (target.widenWidth n)) x₁ x₂)
    (hy : ArgRel G (.bits (target.widenWidth n)) y₁ y₂) :
    TRel (f := LVar target V₁) (g := LVar target V₂) (fun _ a₁ a₂ => TRel (ArgRel G) a₁ a₂) (as := [Ty.bits n, Ty.bits n])
      ((x₁, PUnit.unit), (y₁, PUnit.unit), PUnit.unit)
      ((x₂, PUnit.unit), (y₂, PUnit.unit), PUnit.unit) := by
  dsimp only [LVar]
  exact @TRel.pairL target V₁ V₂ G (.bits n) (.bits n) (x₁, PUnit.unit) (x₂, PUnit.unit)
    (y₁, PUnit.unit) (y₂, PUnit.unit) (TRel.single hx) (TRel.single hy)

private theorem trelPairBitsBool {V₁ V₂ : Ty → Type} {G : Ctx V₁ V₂} (n : Nat)
    {x₁ : Arg V₁ (.bits (target.widenWidth n))} {x₂ : Arg V₂ (.bits (target.widenWidth n))}
    {y₁ : Arg V₁ .bool} {y₂ : Arg V₂ .bool}
    (hx : ArgRel G (.bits (target.widenWidth n)) x₁ x₂)
    (hy : ArgRel G .bool y₁ y₂) :
    TRel (f := LVar target V₁) (g := LVar target V₂) (fun _ a₁ a₂ => TRel (ArgRel G) a₁ a₂) (as := [Ty.bits n, Ty.bool])
      ((x₁, PUnit.unit), (y₁, PUnit.unit), PUnit.unit)
      ((x₂, PUnit.unit), (y₂, PUnit.unit), PUnit.unit) := by
  dsimp only [LVar]
  exact @TRel.pairL target V₁ V₂ G (.bits n) .bool (x₁, PUnit.unit) (x₂, PUnit.unit)
    (y₁, PUnit.unit) (y₂, PUnit.unit) (TRel.single hx) (TRel.single hy)

private theorem legalArg_bits_fst_rel {V₁ V₂ : Ty → Type} {G : Ctx V₁ V₂}
    {LG : Ctx (LVar target V₁) (LVar target V₂)} (hc : CGood target G LG) {n : Nat}
    {a₁ : Arg (LVar target V₁) (.bits n)} {a₂ : Arg (LVar target V₂) (.bits n)}
    (ha : ArgRel LG (.bits n) a₁ a₂) :
    ArgRel G (.bits (target.widenWidth n)) (legalArg target a₁).fst (legalArg target a₂).fst := by
  have r := legalArg_rel target hc ha
  simp only [LegalTarget.legalTys] at r
  exact (TRel.cons_iff.1 r).1

private theorem legalArg_bool_fst_rel {V₁ V₂ : Ty → Type} {G : Ctx V₁ V₂}
    {LG : Ctx (LVar target V₁) (LVar target V₂)} (hc : CGood target G LG)
    {a₁ : Arg (LVar target V₁) .bool} {a₂ : Arg (LVar target V₂) .bool}
    (ha : ArgRel LG .bool a₁ a₂) :
    ArgRel G .bool (legalArg target a₁).fst (legalArg target a₂).fst := by
  have r := legalArg_rel target hc ha
  simp only [LegalTarget.legalTys] at r
  exact (TRel.cons_iff.1 r).1

private theorem legalArg_bits_rel {V₁ V₂ : Ty → Type} {G : Ctx V₁ V₂}
    {LG : Ctx (LVar target V₁) (LVar target V₂)} (hc : CGood target G LG) {n : Nat}
    {a₁ : Arg (LVar target V₁) (.bits n)} {a₂ : Arg (LVar target V₂) (.bits n)}
    (ha : ArgRel LG (.bits n) a₁ a₂)
    {a₁' : Arg V₁ (.bits (target.widenWidth n))} {a₂' : Arg V₂ (.bits (target.widenWidth n))}
    (h₁ : legalArg target a₁ = (a₁', PUnit.unit)) (h₂ : legalArg target a₂ = (a₂', PUnit.unit)) :
    ArgRel G (.bits (target.widenWidth n)) a₁' a₂' := by
  have r := legalArg_rel target hc ha
  rw [h₁, h₂] at r
  simp only [LegalTarget.legalTys] at r
  cases r with | cons h _ => exact h

private theorem legalArg_bool_rel {V₁ V₂ : Ty → Type} {G : Ctx V₁ V₂}
    {LG : Ctx (LVar target V₁) (LVar target V₂)} (hc : CGood target G LG)
    {a₁ : Arg (LVar target V₁) .bool} {a₂ : Arg (LVar target V₂) .bool}
    (ha : ArgRel LG .bool a₁ a₂)
    {a₁' : Arg V₁ .bool} {a₂' : Arg V₂ .bool}
    (h₁ : legalArg target a₁ = (a₁', PUnit.unit)) (h₂ : legalArg target a₂ = (a₂', PUnit.unit)) :
    ArgRel G .bool a₁' a₂' := by
  have r := legalArg_rel target hc ha
  rw [h₁, h₂] at r
  simp only [LegalTarget.legalTys] at r
  cases r with | cons h _ => exact h

private theorem legalArg_float_rel {V₁ V₂ : Ty → Type} {G : Ctx V₁ V₂}
    {LG : Ctx (LVar target V₁) (LVar target V₂)} (hc : CGood target G LG) {f : Fmt}
    {a₁ : Arg (LVar target V₁) (.float f)} {a₂ : Arg (LVar target V₂) (.float f)}
    (ha : ArgRel LG (.float f) a₁ a₂)
    {a₁' : Arg V₁ (.float f)} {a₂' : Arg V₂ (.float f)}
    (h₁ : legalArg target a₁ = (a₁', PUnit.unit)) (h₂ : legalArg target a₂ = (a₂', PUnit.unit)) :
    ArgRel G (.float f) a₁' a₂' := by
  have r := legalArg_rel target hc ha
  rw [h₁, h₂] at r
  simp only [LegalTarget.legalTys] at r
  cases r with | cons h _ => exact h

private theorem opRel_elim {V₁ V₂ : Ty → Type} {G : Ctx V₁ V₂} {rs : List Ty}
    {op₁ : Op V₁ rs} {op₂ : Op V₂ rs} (hop : OpRel G op₁ op₂)
    (P : Op V₁ rs → Op V₂ rs → Prop)
    (h : ∀ {sig} (code : OpCode sig rs) (args₁ : Tup (Arg V₁) sig) (args₂ : Tup (Arg V₂) sig),
      TRel (ArgRel G) args₁ args₂ → P { code := code, args := args₁ } { code := code, args := args₂ }) :
    P op₁ op₂ := by
  cases hop; exact h _ _ _ ‹_›

private def unifShiftRhs (V : Ty → Type) (target : LegalTarget) (u : Ty) (rhs : Arg (LVar target V) u) : Bool :=
  match rhs with
  | .imm c => (uniformShiftLeaf? u c).isSome
  | _ => false

private theorem unifShiftRhs_eq {V₁ V₂ : Ty → Type} (target : LegalTarget) :
    ∀ (u : Ty) {LG : Ctx (LVar target V₁) (LVar target V₂)} {r₁ r₂},
      ArgRel LG u r₁ r₂ → unifShiftRhs V₁ target u r₁ = unifShiftRhs V₂ target u r₂
  | u, _, _, _, h => by cases h <;> rfl

private theorem legalTys_of_isNativeTy (x : Ty)
    (hx : (target.isLegalTy x && match x with | .bits n => target.widenWidth n == n | _ => true) = true) :
    target.legalTys x = [x] := by
  cases x with
  | bool => rfl
  | bits n =>
    simp only [Bool.and_eq_true, beq_iff_eq] at hx
    simp [LegalTarget.legalTys, hx.2]
  | float _ => rfl
  | pair _ _ =>
    simp only [Bool.and_true, LegalTarget.isLegalTy] at hx
    simp [LegalTarget.legalTys, hx]

private theorem TRel_cast_singleton {V₁ V₂ : Ty → Type} {G : Ctx V₁ V₂} {ts : List Ty} {t : Ty}
    (heq : ts = [t]) {xs₁ : Tup (Arg V₁) ts} {xs₂ : Tup (Arg V₂) ts}
    (h : TRel (ArgRel G) xs₁ xs₂) :
    ArgRel G t (cast (by rw [heq]) xs₁ : Tup (Arg V₁) [t]).1
               (cast (by rw [heq]) xs₂ : Tup (Arg V₂) [t]).1 := by
  subst heq; cases h with | cons ha _ => exact ha

private theorem TRel_cast_single_eq {V₁ V₂ : Ty → Type} {G : Ctx V₁ V₂} {u : Ty}
    {ts : List Ty} (heq : [u] = ts) {r₁ : Arg V₁ u} {r₂ : Arg V₂ u}
    (hr : ArgRel G u r₁ r₂) :
    TRel (ArgRel G) (cast (by rw [heq]) (show Tup (Arg V₁) [u] from (r₁, ())) : Tup (Arg V₁) ts)
                    (cast (by rw [heq]) (show Tup (Arg V₂) [u] from (r₂, ())) : Tup (Arg V₂) ts) := by
  subst heq; exact TRel.single hr

theorem legalOp_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {outRs rs' : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {LG : Ctx (LVar target V₁) (LVar target V₂)}
    (hc : CGood target G LG) {op₁ : Op (LVar target V₁) rs'} {op₂ : Op (LVar target V₂) rs'}
    (hop : OpRel LG op₁ op₂)
    {k₁ : Tup (LVar target V₁) rs' → Expr V₁ L₁ outRs}
    {k₂ : Tup (LVar target V₂) rs' → Expr V₂ L₂ outRs}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂,
      TRel (fun _t x₁ x₂ => TRel (ArgRel G') x₁ x₂) y₁ y₂ → Wf G' D (k₁ y₁) (k₂ y₂)) :
    Wf G D (legalOp target op₁ k₁) (legalOp target op₂ k₂) := by
  refine opRel_elim hop (fun o₁ o₂ => Wf G D (legalOp target o₁ k₁) (legalOp target o₂ k₂)) ?_
  intro _sig code args₁ args₂ hargs
  cases code with
  | copy t =>
    rcases hargs with _ | ⟨ha, _⟩
    exact hk (fun _ p => p) _ _ (TRel.singleL target (legalArg_rel target hc ha))
  | add t =>
    rcases hargs with _ | ⟨ha, hargs⟩; rcases hargs with _ | ⟨hb, _⟩
    dsimp only [legalOp]
    split
    · exact .hlt
    · refine legalBinTree_wf target .add (fun u unif => target.vecIntOpSupported (.add u) u unif)
        (fun _ _ => false) (fun _ _ => false) (fun _ {_ _ _} _ => rfl) ?_ ?_ ?_
        t (legalArg_rel target hc ha) (legalArg_rel target hc hb)
        (show OptRhsRel target LG t none none from trivial)
        fun hG' y₁ y₂ hy => hk hG' _ _ (TRel.singleL target hy)
      · intro _ _ _ _ _ _ _ _ h1 h2 c; exact Wf.let2M _ h1 h2 c
      · intro n _ _ _ _ _ _ _ _ h1 h2 c; exact legalBitsArith_wf target n (.add (.bits n)) h1 h2 c
      · intro _ _ _ _ _ _ _ _ _ _ _ _; exact .hlt
  | sub t =>
    rcases hargs with _ | ⟨ha, hargs⟩; rcases hargs with _ | ⟨hb, _⟩
    dsimp only [legalOp]
    split
    · exact .hlt
    · refine legalBinTree_wf target .sub (fun u unif => target.vecIntOpSupported (.sub u) u unif)
        (fun _ _ => false) (fun _ _ => false) (fun _ {_ _ _} _ => rfl) ?_ ?_ ?_
        t (legalArg_rel target hc ha) (legalArg_rel target hc hb)
        (show OptRhsRel target LG t none none from trivial)
        fun hG' y₁ y₂ hy => hk hG' _ _ (TRel.singleL target hy)
      · intro _ _ _ _ _ _ _ _ h1 h2 c; exact Wf.let2M _ h1 h2 c
      · intro n _ _ _ _ _ _ _ _ h1 h2 c; exact legalBitsArith_wf target n (.sub (.bits n)) h1 h2 c
      · intro _ _ _ _ _ _ _ _ _ _ _ _; exact .hlt
  | mul t =>
    rcases hargs with _ | ⟨ha, hargs⟩; rcases hargs with _ | ⟨hb, _⟩
    dsimp only [legalOp]
    split
    · exact .hlt
    · refine legalBinTree_wf target .mul (fun u unif => target.vecIntOpSupported (.mul u) u unif)
        (fun _ _ => false) (fun _ _ => false) (fun _ {_ _ _} _ => rfl) ?_ ?_ ?_
        t (legalArg_rel target hc ha) (legalArg_rel target hc hb)
        (show OptRhsRel target LG t none none from trivial)
        fun hG' y₁ y₂ hy => hk hG' _ _ (TRel.singleL target hy)
      · intro _ _ _ _ _ _ _ _ h1 h2 c; exact Wf.let2M _ h1 h2 c
      · intro n _ _ _ _ _ _ _ _ h1 h2 c; exact legalBitsArith_wf target n (.mul (.bits n)) h1 h2 c
      · intro _ _ _ _ _ _ _ _ _ _ _ _; exact .hlt
  | neg t =>
    rcases hargs with _ | ⟨ha, _⟩
    dsimp only [legalOp]
    split
    · exact .hlt
    · refine legalUnaryTree_wf target .neg (fun u => target.vecIntOpSupported (.neg u) u false)
        (fun {_ _ _ _ _ _} h1 c => c (fun _ p => p) _ _ h1)
        ?_
        (fun _ {_ _ _ _ _ _} _ _ => .hlt)
        t (legalArg_rel target hc ha) fun hG' y₁ y₂ hy => hk hG' _ _ (TRel.singleL target hy)
      intro n G' D' x₁ x₂ cont₁ cont₂ hx hc'
      split
      · exact hc' (fun _ p => p) _ _ (.imm _)
      · exact Wf.let1M _ hx fun h2 r₁ r₂ hr =>
          emitMaskToN_wf n (target.widenWidth n) hr fun h3 y₁ y₂ hy =>
            hc' (sub_trans h2 h3) y₁ y₂ hy
  | and t =>
    rcases hargs with _ | ⟨ha, hargs⟩; rcases hargs with _ | ⟨hb, _⟩
    dsimp only [legalOp]
    refine legalBinTree_wf target .and (fun u unif => target.vecIntOpSupported (.and u) u unif)
      (fun _ _ => false) (fun _ _ => false) (fun _ {_ _ _} _ => rfl) ?_ ?_ ?_
      t (legalArg_rel target hc ha) (legalArg_rel target hc hb)
      (show OptRhsRel target LG t none none from trivial)
      fun hG' y₁ y₂ hy => hk hG' _ _ (TRel.singleL target hy)
    · intro _ _ _ _ _ _ _ _ h1 h2 c; exact Wf.let2M _ h1 h2 c
    · intro n _ _ _ _ _ _ _ _ h1 h2 c; exact legalBitsArith_wf target n (.and (.bits n)) h1 h2 c
    · intro f _ _ _ _ _ _ _ _ h1 h2 c; exact legalFloatBit2_wf target _ _ f h1 h2 c
  | or t =>
    rcases hargs with _ | ⟨ha, hargs⟩; rcases hargs with _ | ⟨hb, _⟩
    dsimp only [legalOp]
    refine legalBinTree_wf target .or (fun u unif => target.vecIntOpSupported (.or u) u unif)
      (fun _ _ => false) (fun _ _ => false) (fun _ {_ _ _} _ => rfl) ?_ ?_ ?_
      t (legalArg_rel target hc ha) (legalArg_rel target hc hb)
      (show OptRhsRel target LG t none none from trivial)
      fun hG' y₁ y₂ hy => hk hG' _ _ (TRel.singleL target hy)
    · intro _ _ _ _ _ _ _ _ h1 h2 c; exact Wf.let2M _ h1 h2 c
    · intro n _ _ _ _ _ _ _ _ h1 h2 c; exact legalBitsArith_wf target n (.or (.bits n)) h1 h2 c
    · intro f _ _ _ _ _ _ _ _ h1 h2 c; exact legalFloatBit2_wf target _ _ f h1 h2 c
  | xor t =>
    rcases hargs with _ | ⟨ha, hargs⟩; rcases hargs with _ | ⟨hb, _⟩
    dsimp only [legalOp]
    refine legalBinTree_wf target .xor (fun u unif => target.vecIntOpSupported (.xor u) u unif)
      (fun _ _ => false) (fun _ _ => false) (fun _ {_ _ _} _ => rfl) ?_ ?_ ?_
      t (legalArg_rel target hc ha) (legalArg_rel target hc hb)
      (show OptRhsRel target LG t none none from trivial)
      fun hG' y₁ y₂ hy => hk hG' _ _ (TRel.singleL target hy)
    · intro _ _ _ _ _ _ _ _ h1 h2 c; exact Wf.let2M _ h1 h2 c
    · intro n _ _ _ _ _ _ _ _ h1 h2 c; exact legalBitsArith_wf target n (.xor (.bits n)) h1 h2 c
    · intro f _ _ _ _ _ _ _ _ h1 h2 c; exact legalFloatBit2_wf target _ _ f h1 h2 c
  | not t =>
    rcases hargs with _ | ⟨ha, _⟩
    refine legalUnaryTree_wf target .not (fun u => target.vecIntOpSupported (.not u) u false)
      (fun {_ _ _ _ _ _} h1 c => Wf.let1M _ h1 c)
      ?_ ?_
      t (legalArg_rel target hc ha) fun hG' y₁ y₂ hy => hk hG' _ _ (TRel.singleL target hy)
    · intro n G' D' x₁ x₂ cont₁ cont₂ hx hc'
      dsimp only; split
      · exact hc' (fun _ p => p) _ _ (.imm _)
      · split
        · exact Wf.let1M _ hx hc'
        · exact Wf.let1M _ hx fun h2 r₁ r₂ hr =>
            emitMaskToN_wf n (target.widenWidth n) hr fun h3 y₁ y₂ hy =>
              hc' (sub_trans h2 h3) y₁ y₂ hy
    · intro f G' D' x₁ x₂ cont₁ cont₂ hx hc'
      dsimp only; split
      · exact Wf.let1M _ hx hc'
      · exact Wf.let1M _ hx fun h2 bx₁ bx₂ hbx =>
          Wf.let1M _ hbx fun h3 br₁ br₂ hbr =>
            Wf.let1M _ hbr fun h4 r₁ r₂ hr =>
              hc' (sub_trans h2 (sub_trans h3 h4)) r₁ r₂ hr
  | ternlog t imm =>
    rcases hargs with _ | ⟨ha, hargs⟩; rcases hargs with _ | ⟨hb, hargs⟩; rcases hargs with _ | ⟨hc', _⟩
    refine legalTernaryTree_wf target (fun u => .ternlog u imm)
      (fun u => target.vecIntOpSupported (.ternlog u imm) u false)
      (fun {_ _ _ _ _ _ _ _ _ _} h1 h2 h3 c => emitTernlogBool_wf h1 h2 h3 imm c)
      ?_ ?_
      t (legalArg_rel target hc ha) (legalArg_rel target hc hb) (legalArg_rel target hc hc')
      fun hG' y₁ y₂ hy => hk hG' _ _ (TRel.singleL target hy)
    · intro n G' D' x₁ x₂ y₁ y₂ z₁ z₂ cont₁ cont₂ hx hy hz hc''
      dsimp only; split
      · exact hc'' (fun _ p => p) _ _ (.imm _)
      · split
        · exact Wf.let3M _ hx hy hz fun h4 r₁ r₂ hr =>
            emitMaskToN_wf n (target.widenWidth n) hr fun h5 y₁ y₂ hy =>
              hc'' (sub_trans h4 h5) y₁ y₂ hy
        · exact emitTernlogBits_wf (target.widenWidth n) hx hy hz imm fun h4 r₁ r₂ hr =>
            emitMaskToN_wf n (target.widenWidth n) hr fun h5 y₁ y₂ hy =>
              hc'' (sub_trans h4 h5) y₁ y₂ hy
    · intro f G' D' x₁ x₂ y₁ y₂ z₁ z₂ cont₁ cont₂ hx hy hz hc''
      dsimp only; split
      · exact Wf.let3M _ hx hy hz hc''
      · cases htern : target.scalarTernlog
        · simp only [Bool.false_eq_true, ↓reduceIte]
          exact Wf.let1 _ hx fun p1 bx₁ bx₂ hbx =>
            Wf.let1 _ (hy.weaken p1) fun p2 by₁ by₂ hby =>
              Wf.let1 _ (hz.weaken (sub_trans p1 p2)) fun p3 bz₁ bz₂ hbz =>
                have q3 := sub_trans p1 (sub_trans p2 p3)
                emitTernlogBits_wf f.width (hbx.weaken (sub_trans p2 p3)) (hby.weaken p3) hbz imm
                  fun p4 br₁ br₂ hbr =>
                    Wf.let1 _ hbr fun p5 r₁ r₂ hr =>
                      hc'' (sub_trans q3 (sub_trans p4 p5)) r₁ r₂ hr
        · simp only [↓reduceIte]
          exact Wf.let1 _ hx fun p1 bx₁ bx₂ hbx =>
            Wf.let1 _ (hy.weaken p1) fun p2 by₁ by₂ hby =>
              Wf.let1 _ (hz.weaken (sub_trans p1 p2)) fun p3 bz₁ bz₂ hbz =>
                have q3 := sub_trans p1 (sub_trans p2 p3)
                Wf.let3 _ (hbx.weaken (sub_trans p2 p3)) (hby.weaken p3) hbz fun p4 br₁ br₂ hbr =>
                  Wf.let1 _ hbr fun p5 r₁ r₂ hr =>
                    hc'' (sub_trans q3 (sub_trans p4 p5)) r₁ r₂ hr
  | shl t =>
    rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, hargs⟩; rcases hargs with _ | ⟨hb, _⟩
    dsimp only [legalOp]
    split
    · exact .hlt
    · refine legalBinTree_wf target .shl (fun u unif => target.vecIntOpSupported (.shl u) u unif)
        _ _ ?_ ?_ ?_ ?_
        t (legalArg_rel target hc ha) (legalArg_rel target hc hb)
        (show OptRhsRel target LG t (some b₁) (some b₂) from hb)
        fun hG' y₁ y₂ hy => hk hG' _ _ (TRel.singleL target hy)
      · intro u _ r₁ r₂ hr; cases hr <;> rfl
      · intro _ _ _ _ _ _ _ _ h1 _ c; exact c (fun _ p => p) _ _ h1
      · intro n _ _ _ _ _ _ _ _ h1 h2 c; exact legalBitsArith_wf target n (.shl (.bits n)) h1 h2 c
      · intro _ _ _ _ _ _ _ _ _ _ _ _; exact .hlt
  | lshr t =>
    rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, hargs⟩; rcases hargs with _ | ⟨hb, _⟩
    dsimp only [legalOp]
    split
    · exact .hlt
    · refine legalBinTree_wf target .lshr (fun u unif => target.vecIntOpSupported (.lshr u) u unif)
        _ _ ?_ ?_ ?_ ?_
        t (legalArg_rel target hc ha) (legalArg_rel target hc hb)
        (show OptRhsRel target LG t (some b₁) (some b₂) from hb)
        fun hG' y₁ y₂ hy => hk hG' _ _ (TRel.singleL target hy)
      · intro u _ r₁ r₂ hr; cases hr <;> rfl
      · intro _ _ _ _ _ _ _ _ h1 _ c; exact c (fun _ p => p) _ _ h1
      · intro n _ _ _ _ _ _ _ _ h1 h2 c; exact legalBitsArith_wf target n (.lshr (.bits n)) h1 h2 c
      · intro _ _ _ _ _ _ _ _ _ _ _ _; exact .hlt
  | ashr t =>
    rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, hargs⟩; rcases hargs with _ | ⟨hb, _⟩
    dsimp only [legalOp]
    split
    · exact .hlt
    · refine legalBinTree_wf target .ashr (fun u unif => target.vecIntOpSupported (.ashr u) u unif)
        _ _ ?_ ?_ ?_ ?_
        t (legalArg_rel target hc ha) (legalArg_rel target hc hb)
        (show OptRhsRel target LG t (some b₁) (some b₂) from hb)
        fun hG' y₁ y₂ hy => hk hG' _ _ (TRel.singleL target hy)
      · intro u _ r₁ r₂ hr; cases hr <;> rfl
      · intro _ _ _ _ _ _ _ _ h1 _ c; exact c (fun _ p => p) _ _ h1
      · intro n _ _ _ _ _ _ _ _ h1 h2 c; exact legalBitsArith_wf target n (.ashr (.bits n)) h1 h2 c
      · intro _ _ _ _ _ _ _ _ _ _ _ _; exact .hlt
  | rotl t =>
    rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, hargs⟩; rcases hargs with _ | ⟨hb, _⟩
    dsimp only [legalOp]
    split
    · exact .hlt
    · refine legalBinTree_wf target .rotl (fun u unif => target.vecIntOpSupported (.rotl u) u unif)
        _ _ ?_ ?_ ?_ ?_
        t (legalArg_rel target hc ha) (legalArg_rel target hc hb)
        (show OptRhsRel target LG t (some b₁) (some b₂) from hb)
        fun hG' y₁ y₂ hy => hk hG' _ _ (TRel.singleL target hy)
      · intro u _ r₁ r₂ hr; cases hr <;> rfl
      · intro _ _ _ _ _ _ _ _ h1 _ c; exact c (fun _ p => p) _ _ h1
      · intro n _ _ _ _ _ _ _ _ h1 h2 c; exact legalBitsArith_wf target n (.rotl (.bits n)) h1 h2 c
      · intro _ _ _ _ _ _ _ _ _ _ _ _; exact .hlt
  | rotr t =>
    rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, hargs⟩; rcases hargs with _ | ⟨hb, _⟩
    dsimp only [legalOp]
    split
    · exact .hlt
    · refine legalBinTree_wf target .rotr (fun u unif => target.vecIntOpSupported (.rotr u) u unif)
        _ _ ?_ ?_ ?_ ?_
        t (legalArg_rel target hc ha) (legalArg_rel target hc hb)
        (show OptRhsRel target LG t (some b₁) (some b₂) from hb)
        fun hG' y₁ y₂ hy => hk hG' _ _ (TRel.singleL target hy)
      · intro u _ r₁ r₂ hr; cases hr <;> rfl
      · intro _ _ _ _ _ _ _ _ h1 _ c; exact c (fun _ p => p) _ _ h1
      · intro n _ _ _ _ _ _ _ _ h1 h2 c; exact legalBitsArith_wf target n (.rotr (.bits n)) h1 h2 c
      · intro _ _ _ _ _ _ _ _ _ _ _ _; exact .hlt
  | fshl n =>
    rcases args₁ with ⟨a₁, b₁, c₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, c₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, hargs⟩; rcases hargs with _ | ⟨hb, hargs⟩; rcases hargs with _ | ⟨hc', _⟩
    dsimp only [legalOp]
    rcases ha1 : legalArg target a₁ with ⟨a₁', ⟨⟩⟩; rcases ha2 : legalArg target a₂ with ⟨a₂', ⟨⟩⟩
    rcases hb1 : legalArg target b₁ with ⟨b₁', ⟨⟩⟩; rcases hb2 : legalArg target b₂ with ⟨b₂', ⟨⟩⟩
    rcases hc1 : legalArg target c₁ with ⟨c₁', ⟨⟩⟩; rcases hc2 : legalArg target c₂ with ⟨c₂', ⟨⟩⟩
    have ha' := legalArg_bits_rel target hc ha ha1 ha2
    have hb' := legalArg_bits_rel target hc hb hb1 hb2
    have hc'' := legalArg_bits_rel target hc hc' hc1 hc2
    dsimp only
    split
    · exact hk (fun _ p => p) _ _ (trelBitsImmZero target n)
    · split
      · exact Wf.let3M _ ha' hb' hc'' fun h1 r₁ r₂ hr =>
          hk h1 _ _ (TRel.singleL target (TRel.single hr))
      · exact emitCountMod_wf n (target.widenWidth n) hc'' fun p1 cm₁ cm₂ hcm =>
          Wf.let2M _ (.imm _) hcm fun p2 nc₁ nc₂ hnc =>
            have q2 := sub_trans p1 p2
            Wf.let2M _ (ha'.weaken q2) (hcm.weaken p2) fun p3 lo₁ lo₂ hlo =>
              have q3 := sub_trans q2 p3
              Wf.let2M _ (hb'.weaken q3) (hnc.weaken p3) fun p4 hi₁ hi₂ hhi =>
                Wf.let2M _ (hlo.weaken p4) hhi fun p5 cb₁ cb₂ hcb =>
                  emitMaskToN_wf n (target.widenWidth n) hcb fun p6 y₁ y₂ hy =>
                    hk (sub_trans q3 (sub_trans p4 (sub_trans p5 p6))) _ _
                      (TRel.singleL target (TRel.single hy))
  | fshr n =>
    rcases args₁ with ⟨a₁, b₁, c₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, c₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, hargs⟩; rcases hargs with _ | ⟨hb, hargs⟩; rcases hargs with _ | ⟨hc', _⟩
    dsimp only [legalOp]
    rcases ha1 : legalArg target a₁ with ⟨a₁', ⟨⟩⟩; rcases ha2 : legalArg target a₂ with ⟨a₂', ⟨⟩⟩
    rcases hb1 : legalArg target b₁ with ⟨b₁', ⟨⟩⟩; rcases hb2 : legalArg target b₂ with ⟨b₂', ⟨⟩⟩
    rcases hc1 : legalArg target c₁ with ⟨c₁', ⟨⟩⟩; rcases hc2 : legalArg target c₂ with ⟨c₂', ⟨⟩⟩
    have ha' := legalArg_bits_rel target hc ha ha1 ha2
    have hb' := legalArg_bits_rel target hc hb hb1 hb2
    have hc'' := legalArg_bits_rel target hc hc' hc1 hc2
    dsimp only
    split
    · exact hk (fun _ p => p) _ _ (trelBitsImmZero target n)
    · split
      · exact Wf.let3M _ ha' hb' hc'' fun h1 r₁ r₂ hr =>
          hk h1 _ _ (TRel.singleL target (TRel.single hr))
      · exact emitCountMod_wf n (target.widenWidth n) hc'' fun p1 cm₁ cm₂ hcm =>
          Wf.let2M _ (.imm _) hcm fun p2 nc₁ nc₂ hnc =>
            have q2 := sub_trans p1 p2
            Wf.let2M _ (hb'.weaken q2) (hcm.weaken p2) fun p3 lo₁ lo₂ hlo =>
              have q3 := sub_trans q2 p3
              Wf.let2M _ (ha'.weaken q3) (hnc.weaken p3) fun p4 hi₁ hi₂ hhi =>
                Wf.let2M _ (hlo.weaken p4) hhi fun p5 cb₁ cb₂ hcb =>
                  emitMaskToN_wf n (target.widenWidth n) hcb fun p6 y₁ y₂ hy =>
                    hk (sub_trans q3 (sub_trans p4 (sub_trans p5 p6))) _ _
                      (TRel.singleL target (TRel.single hy))
  | bswap t =>
    rcases hargs with _ | ⟨ha, _⟩
    exact legalBswapTree_wf target t (legalArg_rel target hc ha) fun hG' y₁ y₂ hy =>
      hk hG' _ _ (TRel.singleL target hy)
  | clz n =>
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, _⟩
    dsimp only [legalOp]
    rcases ha1 : legalArg target a₁ with ⟨a₁', ⟨⟩⟩; rcases ha2 : legalArg target a₂ with ⟨a₂', ⟨⟩⟩
    have ha' := legalArg_bits_rel target hc ha ha1 ha2
    dsimp only
    split
    · exact hk (fun _ p => p) _ _ (trelBitsImmZero target n)
    · split
      · exact Wf.let1M _ ha' fun h1 r₁ r₂ hr =>
          hk h1 _ _ (TRel.singleL target (TRel.single hr))
      · exact Wf.let1M _ ha' fun h1 cw₁ cw₂ hcw =>
          Wf.let2M _ hcw (.imm _) fun h2 r₁ r₂ hr =>
            hk (sub_trans h1 h2) _ _ (TRel.singleL target (TRel.single hr))
  | cls n =>
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, _⟩
    dsimp only [legalOp]
    rcases ha1 : legalArg target a₁ with ⟨a₁', ⟨⟩⟩; rcases ha2 : legalArg target a₂ with ⟨a₂', ⟨⟩⟩
    have ha' := legalArg_bits_rel target hc ha ha1 ha2
    dsimp only
    split
    · exact hk (fun _ p => p) _ _ (trelBitsImmZero target n)
    · split
      · exact Wf.let1M _ ha' fun h1 r₁ r₂ hr =>
          hk h1 _ _ (TRel.singleL target (TRel.single hr))
      · exact emitSextToW_wf n (target.widenWidth n) ha' fun h1 sa₁ sa₂ hsa =>
          Wf.let1M _ hsa fun h2 cw₁ cw₂ hcw =>
            Wf.let2M _ hcw (.imm _) fun h3 r₁ r₂ hr =>
              hk (sub_trans h1 (sub_trans h2 h3)) _ _ (TRel.singleL target (TRel.single hr))
  | rbit n =>
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, _⟩
    dsimp only [legalOp]
    rcases ha1 : legalArg target a₁ with ⟨a₁', ⟨⟩⟩; rcases ha2 : legalArg target a₂ with ⟨a₂', ⟨⟩⟩
    have ha' := legalArg_bits_rel target hc ha ha1 ha2
    dsimp only
    split
    · exact hk (fun _ p => p) _ _ (trelBitsImmZero target n)
    · split
      · exact Wf.let1M _ ha' fun h1 r₁ r₂ hr =>
          hk h1 _ _ (TRel.singleL target (TRel.single hr))
      · exact Wf.let1M _ ha' fun h1 rw₁ rw₂ hrw =>
          Wf.let2M _ hrw (.imm _) fun h2 r₁ r₂ hr =>
            hk (sub_trans h1 h2) _ _ (TRel.singleL target (TRel.single hr))
  | ctz n =>
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, _⟩
    dsimp only [legalOp]
    rcases ha1 : legalArg target a₁ with ⟨a₁', ⟨⟩⟩; rcases ha2 : legalArg target a₂ with ⟨a₂', ⟨⟩⟩
    have ha' := legalArg_bits_rel target hc ha ha1 ha2
    dsimp only
    split
    · exact hk (fun _ p => p) _ _ (trelBitsImmZero target n)
    · split
      · exact Wf.let1M _ ha' fun h1 r₁ r₂ hr =>
          hk h1 _ _ (TRel.singleL target (TRel.single hr))
      · exact Wf.let2M _ ha' (.imm _) fun h1 ao₁ ao₂ hao =>
          Wf.let1M _ hao fun h2 r₁ r₂ hr =>
            hk (sub_trans h1 h2) _ _ (TRel.singleL target (TRel.single hr))
  | popcnt n =>
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, _⟩
    dsimp only [legalOp]
    rcases ha1 : legalArg target a₁ with ⟨a₁', ⟨⟩⟩; rcases ha2 : legalArg target a₂ with ⟨a₂', ⟨⟩⟩
    have ha' := legalArg_bits_rel target hc ha ha1 ha2
    dsimp only
    split
    · exact hk (fun _ p => p) _ _ (trelBitsImmZero target n)
    · exact Wf.let1M _ ha' fun h1 r₁ r₂ hr =>
        hk h1 _ _ (TRel.singleL target (TRel.single hr))
  | cmp o t m h =>
    subst h
    rcases hargs with _ | ⟨ha, hargs⟩; rcases hargs with _ | ⟨hb, _⟩
    dsimp only [legalOp]
    split
    · exact .hlt
    · exact legalCmpTree_wf target o t (legalArg_rel target hc ha) (legalArg_rel target hc hb)
        fun hG' y₁ y₂ hy => hk hG' _ _ (TRel.singleL target hy)
  | select t =>
    rcases args₁ with ⟨c₁, a₁, b₁, ⟨⟩⟩; rcases args₂ with ⟨c₂, a₂, b₂, ⟨⟩⟩
    rcases hargs with _ | ⟨hc', hargs⟩; rcases hargs with _ | ⟨ha, hargs⟩; rcases hargs with _ | ⟨hb, _⟩
    dsimp only [legalOp]
    rcases hc1 : legalArg target c₁ with ⟨c₁', ⟨⟩⟩; rcases hc2 : legalArg target c₂ with ⟨c₂', ⟨⟩⟩
    have hc'' := legalArg_bool_rel target hc hc' hc1 hc2
    dsimp only
    exact legalSelectTree_wf target hc'' t (legalArg_rel target hc ha) (legalArg_rel target hc hb)
      fun hG' y₁ y₂ hy => hk hG' _ _ (TRel.singleL target hy)
  | blend t m h =>
    subst h
    rcases hargs with _ | ⟨hc', hargs⟩; rcases hargs with _ | ⟨ha, hargs⟩; rcases hargs with _ | ⟨hb, _⟩
    exact legalBlendTree_wf target t (legalArg_rel target hc hc')
      (legalArg_rel target hc ha) (legalArg_rel target hc hb)
      fun hG' y₁ y₂ hy => hk hG' _ _ (TRel.singleL target hy)
  | zext m n =>
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, _⟩
    dsimp only [legalOp]
    rcases ha1 : legalArg target a₁ with ⟨a₁', ⟨⟩⟩; rcases ha2 : legalArg target a₂ with ⟨a₂', ⟨⟩⟩
    have ha' := legalArg_bits_rel target hc ha ha1 ha2
    dsimp only
    split
    · exact .hlt
    · split
      · exact hk (fun _ p => p) _ _ (trelBitsImmZero target n)
      · split
        · next h => exact hk (fun _ p => p) _ _ (trelSingleBits target n (castArgBits_rel h ha'))
        · split
          · exact Wf.let1M _ ha' fun h1 r₁ r₂ hr =>
              hk h1 _ _ (TRel.singleL target (TRel.single hr))
          · exact .hlt
  | sext m n =>
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, _⟩
    dsimp only [legalOp]
    rcases ha1 : legalArg target a₁ with ⟨a₁', ⟨⟩⟩; rcases ha2 : legalArg target a₂ with ⟨a₂', ⟨⟩⟩
    have ha' := legalArg_bits_rel target hc ha ha1 ha2
    dsimp only
    split
    · exact .hlt
    · split
      · exact hk (fun _ p => p) _ _ (trelBitsImmZero target n)
      · refine emitSextToW_wf m (target.widenWidth m) ha' fun h1 sx₁ sx₂ hsx => ?_
        by_cases heq : target.widenWidth m = target.widenWidth n
        · simp only [heq, ↓reduceDIte]
          exact emitMaskToN_wf n (target.widenWidth n) (castArgBits_rel heq hsx) fun h2 rm₁ rm₂ hrm =>
            hk (sub_trans h1 h2) _ _ (trelSingleBits target n hrm)
        · by_cases hlt : target.widenWidth m < target.widenWidth n
          · simp only [heq, ↓reduceDIte, hlt, ↓reduceIte]
            exact Wf.let1M _ hsx fun h2 r₁ r₂ hr =>
              emitMaskToN_wf n (target.widenWidth n) hr fun h3 rm₁ rm₂ hrm =>
                hk (sub_trans h1 (sub_trans h2 h3)) _ _ (trelSingleBits target n hrm)
          · simp only [heq, ↓reduceDIte, hlt, ↓reduceIte]; exact .hlt
  | trunc m n =>
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, _⟩
    dsimp only [legalOp]
    rcases ha1 : legalArg target a₁ with ⟨a₁', ⟨⟩⟩; rcases ha2 : legalArg target a₂ with ⟨a₂', ⟨⟩⟩
    have ha' := legalArg_bits_rel target hc ha ha1 ha2
    dsimp only
    split
    · exact .hlt
    · split
      · exact hk (fun _ p => p) _ _ (trelBitsImmZero target n)
      · by_cases heq : target.widenWidth n = target.widenWidth m
        · simp only [heq, ↓reduceDIte]
          exact emitMaskToN_wf n (target.widenWidth n) (castArgBits_rel heq.symm ha') fun h1 rm₁ rm₂ hrm =>
            hk h1 _ _ (trelSingleBits target n hrm)
        · by_cases hlt : target.widenWidth n < target.widenWidth m
          · simp only [heq, ↓reduceDIte, hlt, ↓reduceIte]
            exact Wf.let1M _ ha' fun h1 r₁ r₂ hr =>
              emitMaskToN_wf n (target.widenWidth n) hr fun h2 rm₁ rm₂ hrm =>
                hk (sub_trans h1 h2) _ _ (trelSingleBits target n hrm)
          · simp only [heq, ↓reduceDIte, hlt, ↓reduceIte]; exact .hlt
  | ofBool n =>
    rcases args₁ with ⟨c₁, ⟨⟩⟩; rcases args₂ with ⟨c₂, ⟨⟩⟩
    rcases hargs with _ | ⟨hc', _⟩
    dsimp only [legalOp]
    rcases hc1 : legalArg target c₁ with ⟨c₁', ⟨⟩⟩; rcases hc2 : legalArg target c₂ with ⟨c₂', ⟨⟩⟩
    have hc'' := legalArg_bool_rel target hc hc' hc1 hc2
    dsimp only
    split
    · exact hk (fun _ p => p) _ _ (trelBitsImmZero target n)
    · exact Wf.let1M _ hc'' fun h1 r₁ r₂ hr =>
        hk h1 _ _ (TRel.singleL target (TRel.single hr))
  | addc n =>
    rcases args₁ with ⟨a₁, b₁, c₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, c₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, hargs⟩; rcases hargs with _ | ⟨hb, hargs⟩; rcases hargs with _ | ⟨hc', _⟩
    dsimp only [legalOp]
    rcases ha1 : legalArg target a₁ with ⟨a₁', ⟨⟩⟩; rcases ha2 : legalArg target a₂ with ⟨a₂', ⟨⟩⟩
    rcases hb1 : legalArg target b₁ with ⟨b₁', ⟨⟩⟩; rcases hb2 : legalArg target b₂ with ⟨b₂', ⟨⟩⟩
    rcases hc1 : legalArg target c₁ with ⟨c₁', ⟨⟩⟩; rcases hc2 : legalArg target c₂ with ⟨c₂', ⟨⟩⟩
    have ha' := legalArg_bits_rel target hc ha ha1 ha2
    have hb' := legalArg_bits_rel target hc hb hb1 hb2
    have hc'' := legalArg_bool_rel target hc hc' hc1 hc2
    dsimp only
    split
    · exact hk (fun _ p => p) _ _ (trelPairBitsBool target n (ArgRel.imm _) hc'')
    · split
      · refine .let_ (.mk (.addc (target.widenWidth n)) (.cons ha' (.cons hb' (.cons hc'' .nil))))
          fun r₁ r₂ => ?_
        rcases r₁ with ⟨s₁, co₁, ⟨⟩⟩; rcases r₂ with ⟨s₂, co₂, ⟨⟩⟩
        dsimp only [Tup.zip, List.append]
        exact hk (fun _ p => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ p)) _ _
          (trelPairBitsBool target n (.var List.mem_cons_self) (.var (List.mem_cons_of_mem _ List.mem_cons_self)))
      · exact Wf.let1 _ hc'' fun p1 cw₁ cw₂ hcw =>
          Wf.let2 _ (ha'.weaken p1) (hb'.weaken p1) fun p2 ab₁ ab₂ hab =>
            Wf.let2 _ hab (hcw.weaken p2) fun p3 sw₁ sw₂ hsw =>
              emitMaskToN_wf n (target.widenWidth n) hsw fun p4 s₁ s₂ hs =>
                Wf.let2 _ (.imm _) (hsw.weaken p4) fun p5 co₁ co₂ hco =>
                  hk (sub_trans p1 (sub_trans p2 (sub_trans p3 (sub_trans p4 p5)))) _ _
                    (trelPairBitsBool target n (hs.weaken p5) hco)
  | subb n =>
    rcases args₁ with ⟨a₁, b₁, c₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, c₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, hargs⟩; rcases hargs with _ | ⟨hb, hargs⟩; rcases hargs with _ | ⟨hc', _⟩
    dsimp only [legalOp]
    rcases ha1 : legalArg target a₁ with ⟨a₁', ⟨⟩⟩; rcases ha2 : legalArg target a₂ with ⟨a₂', ⟨⟩⟩
    rcases hb1 : legalArg target b₁ with ⟨b₁', ⟨⟩⟩; rcases hb2 : legalArg target b₂ with ⟨b₂', ⟨⟩⟩
    rcases hc1 : legalArg target c₁ with ⟨c₁', ⟨⟩⟩; rcases hc2 : legalArg target c₂ with ⟨c₂', ⟨⟩⟩
    have ha' := legalArg_bits_rel target hc ha ha1 ha2
    have hb' := legalArg_bits_rel target hc hb hb1 hb2
    have hc'' := legalArg_bool_rel target hc hc' hc1 hc2
    dsimp only
    split
    · exact hk (fun _ p => p) _ _ (trelPairBitsBool target n (ArgRel.imm _) hc'')
    · split
      · refine .let_ (.mk (.subb (target.widenWidth n)) (.cons ha' (.cons hb' (.cons hc'' .nil))))
          fun r₁ r₂ => ?_
        rcases r₁ with ⟨d₁, bo₁, ⟨⟩⟩; rcases r₂ with ⟨d₂, bo₂, ⟨⟩⟩
        dsimp only [Tup.zip, List.append]
        exact hk (fun _ p => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ p)) _ _
          (trelPairBitsBool target n (.var List.mem_cons_self) (.var (List.mem_cons_of_mem _ List.mem_cons_self)))
      · refine .let_ (.mk (.subb (target.widenWidth n)) (.cons ha' (.cons hb' (.cons hc'' .nil))))
          fun r₁ r₂ => ?_
        rcases r₁ with ⟨dw₁, bo₁, ⟨⟩⟩; rcases r₂ with ⟨dw₂, bo₂, ⟨⟩⟩
        dsimp only [Tup.zip, List.append]
        exact emitMaskToN_wf n (target.widenWidth n) (.var List.mem_cons_self)
          fun hG1 d₁ d₂ hd =>
            hk (fun _ p => hG1 _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ p))) _ _
              (trelPairBitsBool target n hd (.var (hG1 _ (List.mem_cons_of_mem _ List.mem_cons_self))))
  | umulw n =>
    rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, hargs⟩; rcases hargs with _ | ⟨hb, _⟩
    dsimp only [legalOp]
    rcases ha1 : legalArg target a₁ with ⟨a₁', ⟨⟩⟩; rcases ha2 : legalArg target a₂ with ⟨a₂', ⟨⟩⟩
    rcases hb1 : legalArg target b₁ with ⟨b₁', ⟨⟩⟩; rcases hb2 : legalArg target b₂ with ⟨b₂', ⟨⟩⟩
    have ha' := legalArg_bits_rel target hc ha ha1 ha2
    have hb' := legalArg_bits_rel target hc hb hb1 hb2
    dsimp only
    split
    · exact hk (fun _ p => p) _ _ (trelPairBits target n (ArgRel.imm _) (ArgRel.imm _))
    · split
      · refine .let_ (.mk (.umulw (target.widenWidth n)) (.cons ha' (.cons hb' .nil)))
          fun r₁ r₂ => ?_
        rcases r₁ with ⟨lo₁, hi₁, ⟨⟩⟩; rcases r₂ with ⟨lo₂, hi₂, ⟨⟩⟩
        dsimp only [Tup.zip, List.append]
        exact hk (fun _ p => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ p)) _ _
          (trelPairBits target n (.var List.mem_cons_self) (.var (List.mem_cons_of_mem _ List.mem_cons_self)))
      · refine .let_ (.mk (.umulw (target.widenWidth n)) (.cons ha' (.cons hb' .nil)))
          fun r₁ r₂ => ?_
        rcases r₁ with ⟨loW₁, hiW₁, ⟨⟩⟩; rcases r₂ with ⟨loW₂, hiW₂, ⟨⟩⟩
        dsimp only [Tup.zip, List.append]
        refine emitMaskToN_wf n (target.widenWidth n) (.var List.mem_cons_self)
          fun hG1 lo₁ lo₂ hlo => ?_
        have hloW : ArgRel _ (.bits (target.widenWidth n)) (.var loW₁) (.var loW₂) :=
          .var (hG1 _ List.mem_cons_self)
        have hhiW : ArgRel _ (.bits (target.widenWidth n)) (.var hiW₁) (.var hiW₂) :=
          .var (hG1 _ (List.mem_cons_of_mem _ List.mem_cons_self))
        exact Wf.let2M _ hloW (.imm _) fun p1 pv1₁ pv1₂ hp1 =>
          Wf.let2M _ (hhiW.weaken p1) (.imm _) fun p2 pv2₁ pv2₂ hp2 =>
            Wf.let2M _ (hp1.weaken p2) hp2 fun p3 hcb₁ hcb₂ hcb =>
              emitMaskToN_wf n (target.widenWidth n) hcb fun p4 hi₁ hi₂ hhi =>
                have q4 := sub_trans p1 (sub_trans p2 (sub_trans p3 p4))
                hk (fun _ p => q4 _ (hG1 _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ p)))) _ _
                  (trelPairBits target n (hlo.weaken q4) hhi)
  | smulw n =>
    rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, hargs⟩; rcases hargs with _ | ⟨hb, _⟩
    dsimp only [legalOp]
    rcases ha1 : legalArg target a₁ with ⟨a₁', ⟨⟩⟩; rcases ha2 : legalArg target a₂ with ⟨a₂', ⟨⟩⟩
    rcases hb1 : legalArg target b₁ with ⟨b₁', ⟨⟩⟩; rcases hb2 : legalArg target b₂ with ⟨b₂', ⟨⟩⟩
    have ha' := legalArg_bits_rel target hc ha ha1 ha2
    have hb' := legalArg_bits_rel target hc hb hb1 hb2
    dsimp only
    split
    · exact hk (fun _ p => p) _ _ (trelPairBits target n (ArgRel.imm _) (ArgRel.imm _))
    · split
      · refine .let_ (.mk (.smulw (target.widenWidth n)) (.cons ha' (.cons hb' .nil)))
          fun r₁ r₂ => ?_
        rcases r₁ with ⟨lo₁, hi₁, ⟨⟩⟩; rcases r₂ with ⟨lo₂, hi₂, ⟨⟩⟩
        dsimp only [Tup.zip, List.append]
        exact hk (fun _ p => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ p)) _ _
          (trelPairBits target n (.var List.mem_cons_self) (.var (List.mem_cons_of_mem _ List.mem_cons_self)))
      · refine emitSextToW_wf n (target.widenWidth n) ha' fun p1 sa₁ sa₂ hsa =>
          emitSextToW_wf n (target.widenWidth n) (hb'.weaken p1) fun p2 sb₁ sb₂ hsb => ?_
        refine .let_ (.mk (.smulw (target.widenWidth n)) (.cons (hsa.weaken p2) (.cons hsb .nil)))
          fun r₁ r₂ => ?_
        rcases r₁ with ⟨loW₁, hiW₁, ⟨⟩⟩; rcases r₂ with ⟨loW₂, hiW₂, ⟨⟩⟩
        dsimp only [Tup.zip, List.append]
        refine emitMaskToN_wf n (target.widenWidth n) (.var List.mem_cons_self)
          fun p3 lo₁ lo₂ hlo => ?_
        have hloW : ArgRel _ (.bits (target.widenWidth n)) (.var loW₁) (.var loW₂) :=
          .var (p3 _ List.mem_cons_self)
        have hhiW : ArgRel _ (.bits (target.widenWidth n)) (.var hiW₁) (.var hiW₂) :=
          .var (p3 _ (List.mem_cons_of_mem _ List.mem_cons_self))
        exact Wf.let2M _ hloW (.imm _) fun p4 pv1₁ pv1₂ hp1 =>
          Wf.let2M _ (hhiW.weaken p4) (.imm _) fun p5 pv2₁ pv2₂ hp2 =>
            Wf.let2M _ (hp1.weaken p5) hp2 fun p6 hcb₁ hcb₂ hcb =>
              emitMaskToN_wf n (target.widenWidth n) hcb fun p7 hi₁ hi₂ hhi =>
                have q7 := sub_trans p4 (sub_trans p5 (sub_trans p6 p7))
                hk (fun _ p => q7 _ (p3 _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (p2 _ (p1 _ p)))))) _ _
                  (trelPairBits target n (hlo.weaken q7) hhi)
  | udiv n =>
    rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, hargs⟩; rcases hargs with _ | ⟨hb, _⟩
    dsimp only [legalOp]
    rcases ha1 : legalArg target a₁ with ⟨a₁', ⟨⟩⟩; rcases ha2 : legalArg target a₂ with ⟨a₂', ⟨⟩⟩
    rcases hb1 : legalArg target b₁ with ⟨b₁', ⟨⟩⟩; rcases hb2 : legalArg target b₂ with ⟨b₂', ⟨⟩⟩
    have ha' := legalArg_bits_rel target hc ha ha1 ha2
    have hb' := legalArg_bits_rel target hc hb hb1 hb2
    dsimp only
    split
    · exact .hlt
    · exact Wf.let2M _ ha' hb' fun h1 r₁ r₂ hr =>
        hk h1 _ _ (TRel.singleL target (TRel.single hr))
  | urem n =>
    rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, hargs⟩; rcases hargs with _ | ⟨hb, _⟩
    dsimp only [legalOp]
    rcases ha1 : legalArg target a₁ with ⟨a₁', ⟨⟩⟩; rcases ha2 : legalArg target a₂ with ⟨a₂', ⟨⟩⟩
    rcases hb1 : legalArg target b₁ with ⟨b₁', ⟨⟩⟩; rcases hb2 : legalArg target b₂ with ⟨b₂', ⟨⟩⟩
    have ha' := legalArg_bits_rel target hc ha ha1 ha2
    have hb' := legalArg_bits_rel target hc hb hb1 hb2
    dsimp only
    split
    · exact .hlt
    · exact Wf.let2M _ ha' hb' fun h1 r₁ r₂ hr =>
        hk h1 _ _ (TRel.singleL target (TRel.single hr))
  | sdiv n =>
    rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, hargs⟩; rcases hargs with _ | ⟨hb, _⟩
    dsimp only [legalOp]
    rcases ha1 : legalArg target a₁ with ⟨a₁', ⟨⟩⟩; rcases ha2 : legalArg target a₂ with ⟨a₂', ⟨⟩⟩
    rcases hb1 : legalArg target b₁ with ⟨b₁', ⟨⟩⟩; rcases hb2 : legalArg target b₂ with ⟨b₂', ⟨⟩⟩
    have ha' := legalArg_bits_rel target hc ha ha1 ha2
    have hb' := legalArg_bits_rel target hc hb hb1 hb2
    dsimp only
    split
    · exact .hlt
    · split
      · exact Wf.let2M _ ha' hb' fun h1 r₁ r₂ hr =>
          hk h1 _ _ (TRel.singleL target (TRel.single hr))
      · exact emitSextToW_wf n (target.widenWidth n) ha' fun h1 sa₁ sa₂ hsa =>
          emitSextToW_wf n (target.widenWidth n) (hb'.weaken h1) fun h2 sb₁ sb₂ hsb =>
            Wf.let2M _ (hsa.weaken h2) hsb fun h3 r₁ r₂ hr =>
              emitMaskToN_wf n (target.widenWidth n) hr fun h4 rm₁ rm₂ hrm =>
                hk (sub_trans h1 (sub_trans h2 (sub_trans h3 h4))) _ _
                  (TRel.singleL target (TRel.single hrm))
  | srem n =>
    rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, hargs⟩; rcases hargs with _ | ⟨hb, _⟩
    dsimp only [legalOp]
    rcases ha1 : legalArg target a₁ with ⟨a₁', ⟨⟩⟩; rcases ha2 : legalArg target a₂ with ⟨a₂', ⟨⟩⟩
    rcases hb1 : legalArg target b₁ with ⟨b₁', ⟨⟩⟩; rcases hb2 : legalArg target b₂ with ⟨b₂', ⟨⟩⟩
    have ha' := legalArg_bits_rel target hc ha ha1 ha2
    have hb' := legalArg_bits_rel target hc hb hb1 hb2
    dsimp only
    split
    · exact .hlt
    · split
      · exact Wf.let2M _ ha' hb' fun h1 r₁ r₂ hr =>
          hk h1 _ _ (TRel.singleL target (TRel.single hr))
      · exact emitSextToW_wf n (target.widenWidth n) ha' fun h1 sa₁ sa₂ hsa =>
          emitSextToW_wf n (target.widenWidth n) (hb'.weaken h1) fun h2 sb₁ sb₂ hsb =>
            Wf.let2M _ (hsa.weaken h2) hsb fun h3 r₁ r₂ hr =>
              emitMaskToN_wf n (target.widenWidth n) hr fun h4 rm₁ rm₂ hrm =>
                hk (sub_trans h1 (sub_trans h2 (sub_trans h3 h4))) _ _
                  (TRel.singleL target (TRel.single hrm))
  | udiv0 n =>
    rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, hargs⟩; rcases hargs with _ | ⟨hb, _⟩
    dsimp only [legalOp]
    rcases ha1 : legalArg target a₁ with ⟨a₁', ⟨⟩⟩; rcases ha2 : legalArg target a₂ with ⟨a₂', ⟨⟩⟩
    rcases hb1 : legalArg target b₁ with ⟨b₁', ⟨⟩⟩; rcases hb2 : legalArg target b₂ with ⟨b₂', ⟨⟩⟩
    have ha' := legalArg_bits_rel target hc ha ha1 ha2
    have hb' := legalArg_bits_rel target hc hb hb1 hb2
    dsimp only
    split
    · exact hk (fun _ p => p) _ _ (trelBitsImmZero target n)
    · exact Wf.let2M _ ha' hb' fun h1 r₁ r₂ hr =>
        hk h1 _ _ (TRel.singleL target (TRel.single hr))
  | sdiv0 n =>
    rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, hargs⟩; rcases hargs with _ | ⟨hb, _⟩
    dsimp only [legalOp]
    rcases ha1 : legalArg target a₁ with ⟨a₁', ⟨⟩⟩; rcases ha2 : legalArg target a₂ with ⟨a₂', ⟨⟩⟩
    rcases hb1 : legalArg target b₁ with ⟨b₁', ⟨⟩⟩; rcases hb2 : legalArg target b₂ with ⟨b₂', ⟨⟩⟩
    have ha' := legalArg_bits_rel target hc ha ha1 ha2
    have hb' := legalArg_bits_rel target hc hb hb1 hb2
    dsimp only
    split
    · exact hk (fun _ p => p) _ _ (trelBitsImmZero target n)
    · split
      · exact Wf.let2M _ ha' hb' fun h1 r₁ r₂ hr =>
          hk h1 _ _ (TRel.singleL target (TRel.single hr))
      · exact emitSextToW_wf n (target.widenWidth n) ha' fun h1 sa₁ sa₂ hsa =>
          emitSextToW_wf n (target.widenWidth n) (hb'.weaken h1) fun h2 sb₁ sb₂ hsb =>
            Wf.let2M _ (hsa.weaken h2) hsb fun h3 r₁ r₂ hr =>
              emitMaskToN_wf n (target.widenWidth n) hr fun h4 rm₁ rm₂ hrm =>
                hk (sub_trans h1 (sub_trans h2 (sub_trans h3 h4))) _ _
                  (TRel.singleL target (TRel.single hrm))
  | mkpair a b =>
    rcases hargs with _ | ⟨ha, hargs⟩; rcases hargs with _ | ⟨hb, _⟩
    have hla := legalArg_rel target hc ha
    have hlb := legalArg_rel target hc hb
    dsimp only [legalOp]
    split
    · next h =>
      exact packFromLegal_wf target a hla fun h1 pa₁ pa₂ hpa =>
        packFromLegal_wf target b (TRel_argRel_weaken' h1 hlb) fun h2 pb₁ pb₂ hpb =>
          Wf.let2M (.mkpair a b) (hpa.weaken h2) hpb fun h3 p₁ p₂ hp =>
            hk (sub_trans h1 (sub_trans h2 h3)) _ _
              (TRel.singleL target (tupToPacked_rel h (TRel.single hp)))
    · next h =>
      exact hk (fun _ q => q) _ _
        (TRel.singleL target (tupToSplit_rel (Bool.eq_false_iff.mpr h) (TRel_tupAppend hla hlb)))
  | unpair a b =>
    rcases hargs with _ | ⟨hp, _⟩
    have hlp := legalArg_rel target hc hp
    dsimp only [legalOp]
    split
    · next h =>
      obtain ⟨h1, _⟩ := TRel.cons_iff.1 (packedToTup_rel h hlp)
      have hunpair : ∀ {px₁ : Arg V₁ (.pair a b)} {px₂ : Arg V₂ (.pair a b)},
          ArgRel G (.pair a b) px₁ px₂ →
          Wf G D
            (match px₁ with
             | .imm c => k₁ (encodeImm target a c.1, encodeImm target b c.2, ())
             | .var v => .let_ (.mk (.unpair a b) (.var v, ())) fun p =>
                 unpackToLegal target a (.var p.1) fun la =>
                   unpackToLegal target b (.var p.2.1) fun lb => k₁ (la, lb, ()))
            (match px₂ with
             | .imm c => k₂ (encodeImm target a c.1, encodeImm target b c.2, ())
             | .var v => .let_ (.mk (.unpair a b) (.var v, ())) fun p =>
                 unpackToLegal target a (.var p.1) fun la =>
                   unpackToLegal target b (.var p.2.1) fun lb => k₂ (la, lb, ())) := by
        intro px₁ px₂ hpx
        cases hpx with
        | imm c =>
          exact hk (fun _ q => q) _ _ (TRel.pairL target (encodeImm_rel target a c.1) (encodeImm_rel target b c.2))
        | var hm =>
          refine .let_ (.mk (.unpair a b) (.cons (.var hm) .nil)) fun p₁ p₂ => ?_
          rcases p₁ with ⟨va₁, vb₁, ⟨⟩⟩; rcases p₂ with ⟨va₂, vb₂, ⟨⟩⟩
          exact unpackToLegal_wf target a (.var List.mem_cons_self) fun h1 la₁ la₂ hla =>
            unpackToLegal_wf target b (.var (h1 _ (List.mem_cons_of_mem _ List.mem_cons_self))) fun h2 lb₁ lb₂ hlb =>
              hk (fun _ q => h2 _ (h1 _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ q))))
                _ _ (TRel.pairL target (TRel_argRel_weaken' h2 hla) hlb)
      exact hunpair h1
    · next h =>
      obtain ⟨hla, hlb⟩ := TRel_tupSplit (splitToTup_rel (Bool.eq_false_iff.mpr h) hlp)
      exact hk (fun _ q => q) _ _ (TRel.pairL target hla hlb)
  | bitcast t u h =>
    rcases hargs with _ | ⟨ha, _⟩
    have hla := legalArg_rel target hc ha
    dsimp only [legalOp]
    split
    · next heq => subst heq; exact hk (fun _ q => q) _ _ (TRel.singleL target hla)
    · have hsplit := splitLegalToLeaves_wf target t hla fun h1 fx₁ fx₂ hfx =>
        packLeavesToWords64_wf target t hfx fun h2 w₁ w₂ hw =>
          unpackWords64ToLeaves_wf target u hw 0 fun h3 fu₁ fu₂ hfu =>
            packLeavesToLegal_wf target u hfu fun h4 y₁ y₂ hy =>
              hk (sub_trans h1 (sub_trans h2 (sub_trans h3 h4))) _ _ (TRel.singleL target hy)
      cases t <;> dsimp only <;> split
      all_goals first
        | exact hsplit
        | (next ht =>
          cases u <;> dsimp only <;> split <;> first
            | exact hsplit
            | contradiction
            | next hu =>
              exact Wf.let1 (.bitcast _ _ h)
                (TRel_cast_singleton (legalTys_of_isNativeTy target _ ht) hla)
                fun h1 r₁ r₂ hr =>
                  hk h1 _ _ (TRel.singleL target
                    (TRel_cast_single_eq (legalTys_of_isNativeTy target _ hu).symm hr)))
  | shufd t imm =>
    rcases hargs with _ | ⟨ha, _⟩
    exact legalShufd_wf target imm t (legalArg_rel target hc ha) fun hG' y₁ y₂ hy =>
      hk hG' _ _ (TRel.singleL target hy)
  | shufb t =>
    rcases hargs with _ | ⟨ha, hargs⟩; rcases hargs with _ | ⟨hm, _⟩
    exact legalShufb_wf target t (legalArg_rel target hc ha) (legalArg_rel target hc hm)
      fun hG' y₁ y₂ hy => hk hG' _ _ (TRel.singleL target hy)
  | alignr t imm =>
    rcases hargs with _ | ⟨hi, hargs⟩; rcases hargs with _ | ⟨lo, _⟩
    exact legalAlignr_wf target imm t (legalArg_rel target hc hi) (legalArg_rel target hc lo)
      fun hG' y₁ y₂ hy => hk hG' _ _ (TRel.singleL target hy)
  | blendw t imm =>
    rcases hargs with _ | ⟨ha, hargs⟩; rcases hargs with _ | ⟨hb, _⟩
    exact legalBlendw_wf target imm t (legalArg_rel target hc ha) (legalArg_rel target hc hb)
      fun hG' y₁ y₂ hy => hk hG' _ _ (TRel.singleL target hy)
  | sha256rnds2 =>
    rcases hargs with _ | ⟨hc', hargs⟩; rcases hargs with _ | ⟨ha, hargs⟩; rcases hargs with _ | ⟨hw, _⟩
    have hlc := legalArg_rel target hc hc'
    have hla := legalArg_rel target hc ha
    have hlw := legalArg_rel target hc hw
    dsimp only [legalOp]
    split
    · next hk_and =>
      have hkp : target.keepsPacked v4i32 = true := ((Bool.and_eq_true _ _).mp hk_and).1
      have hl : target.legalTys v4i32 = [v4i32] := by simp [LegalTarget.legalTys, hkp]
      exact Wf.let3 .sha256rnds2 (TRel_cast_singleton hl hlc)
        (TRel_cast_singleton hl hla) (TRel_cast_singleton hl hlw) fun h1 r₁ r₂ hr =>
        hk h1 _ _ (TRel.singleL target (TRel_cast_single_eq hl.symm hr))
    · exact sha256rnds2_scalar_wf target hlc hla hlw fun hG' y₁ y₂ hy => hk hG' _ _ (TRel.singleL target hy)
  | sha256msg1 =>
    rcases hargs with _ | ⟨ha, hargs⟩; rcases hargs with _ | ⟨hb, _⟩
    have hla := legalArg_rel target hc ha
    have hlb := legalArg_rel target hc hb
    dsimp only [legalOp]
    split
    · next hk_and =>
      have hkp : target.keepsPacked v4i32 = true := ((Bool.and_eq_true _ _).mp hk_and).1
      have hl : target.legalTys v4i32 = [v4i32] := by simp [LegalTarget.legalTys, hkp]
      exact Wf.let2 .sha256msg1 (TRel_cast_singleton hl hla)
        (TRel_cast_singleton hl hlb) fun h1 r₁ r₂ hr =>
        hk h1 _ _ (TRel.singleL target (TRel_cast_single_eq hl.symm hr))
    · exact sha256msg1_scalar_wf target hla hlb fun hG' y₁ y₂ hy => hk hG' _ _ (TRel.singleL target hy)
  | sha256msg2 =>
    rcases hargs with _ | ⟨ha, hargs⟩; rcases hargs with _ | ⟨hb, _⟩
    have hla := legalArg_rel target hc ha
    have hlb := legalArg_rel target hc hb
    dsimp only [legalOp]
    split
    · next hk_and =>
      have hkp : target.keepsPacked v4i32 = true := ((Bool.and_eq_true _ _).mp hk_and).1
      have hl : target.legalTys v4i32 = [v4i32] := by simp [LegalTarget.legalTys, hkp]
      exact Wf.let2 .sha256msg2 (TRel_cast_singleton hl hla)
        (TRel_cast_singleton hl hlb) fun h1 r₁ r₂ hr =>
        hk h1 _ _ (TRel.singleL target (TRel_cast_single_eq hl.symm hr))
    · exact sha256msg2_scalar_wf target hla hlb fun hG' y₁ y₂ hy => hk hG' _ _ (TRel.singleL target hy)
  | fadd t =>
    rcases hargs with _ | ⟨ha, hargs⟩; rcases hargs with _ | ⟨hb, _⟩
    dsimp only [legalOp]
    split
    · exact .hlt
    · refine legalBinTree_wf target .fadd (fun u _ => target.vecFloatOpSupported (.fadd u) u)
        (fun _ _ => false) (fun _ _ => false) (fun _ {_ _ _} _ => rfl) ?_ ?_ ?_
        t (legalArg_rel target hc ha) (legalArg_rel target hc hb)
        (show OptRhsRel target LG t none none from trivial)
        fun hG' y₁ y₂ hy => hk hG' _ _ (TRel.singleL target hy)
      · intro _ _ _ _ _ _ _ _ _ _ _; exact .hlt
      · intro _ _ _ _ _ _ _ _ _ _ _ _; exact .hlt
      · intro f _ _ _ _ _ _ _ _ h1 h2 c; exact Wf.let2M _ h1 h2 c
  | fsub t =>
    rcases hargs with _ | ⟨ha, hargs⟩; rcases hargs with _ | ⟨hb, _⟩
    dsimp only [legalOp]
    split
    · exact .hlt
    · refine legalBinTree_wf target .fsub (fun u _ => target.vecFloatOpSupported (.fsub u) u)
        (fun _ _ => false) (fun _ _ => false) (fun _ {_ _ _} _ => rfl) ?_ ?_ ?_
        t (legalArg_rel target hc ha) (legalArg_rel target hc hb)
        (show OptRhsRel target LG t none none from trivial)
        fun hG' y₁ y₂ hy => hk hG' _ _ (TRel.singleL target hy)
      · intro _ _ _ _ _ _ _ _ _ _ _; exact .hlt
      · intro _ _ _ _ _ _ _ _ _ _ _ _; exact .hlt
      · intro f _ _ _ _ _ _ _ _ h1 h2 c; exact Wf.let2M _ h1 h2 c
  | fmul t =>
    rcases hargs with _ | ⟨ha, hargs⟩; rcases hargs with _ | ⟨hb, _⟩
    dsimp only [legalOp]
    split
    · exact .hlt
    · refine legalBinTree_wf target .fmul (fun u _ => target.vecFloatOpSupported (.fmul u) u)
        (fun _ _ => false) (fun _ _ => false) (fun _ {_ _ _} _ => rfl) ?_ ?_ ?_
        t (legalArg_rel target hc ha) (legalArg_rel target hc hb)
        (show OptRhsRel target LG t none none from trivial)
        fun hG' y₁ y₂ hy => hk hG' _ _ (TRel.singleL target hy)
      · intro _ _ _ _ _ _ _ _ _ _ _; exact .hlt
      · intro _ _ _ _ _ _ _ _ _ _ _ _; exact .hlt
      · intro f _ _ _ _ _ _ _ _ h1 h2 c; exact Wf.let2M _ h1 h2 c
  | fdiv t =>
    rcases hargs with _ | ⟨ha, hargs⟩; rcases hargs with _ | ⟨hb, _⟩
    dsimp only [legalOp]
    split
    · exact .hlt
    · refine legalBinTree_wf target .fdiv (fun u _ => target.vecFloatOpSupported (.fdiv u) u)
        (fun _ _ => false) (fun _ _ => false) (fun _ {_ _ _} _ => rfl) ?_ ?_ ?_
        t (legalArg_rel target hc ha) (legalArg_rel target hc hb)
        (show OptRhsRel target LG t none none from trivial)
        fun hG' y₁ y₂ hy => hk hG' _ _ (TRel.singleL target hy)
      · intro _ _ _ _ _ _ _ _ _ _ _; exact .hlt
      · intro _ _ _ _ _ _ _ _ _ _ _ _; exact .hlt
      · intro f _ _ _ _ _ _ _ _ h1 h2 c; exact Wf.let2M _ h1 h2 c
  | ffma t =>
    rcases hargs with _ | ⟨ha, hargs⟩; rcases hargs with _ | ⟨hb, hargs⟩; rcases hargs with _ | ⟨hc', _⟩
    dsimp only [legalOp]
    split
    · exact .hlt
    · exact legalTernaryTree_wf target .ffma (fun u => target.vecFloatOpSupported (.ffma u) u)
        (fun {_ _ _ _ _ _ _ _ _ _} _ _ _ _ => .hlt) (fun _ {_ _ _ _ _ _ _ _ _ _} _ _ _ _ => .hlt)
        (fun f {_ _ _ _ _ _ _ _ _ _} h1 h2 h3 c => Wf.let3M _ h1 h2 h3 c)
        t (legalArg_rel target hc ha) (legalArg_rel target hc hb) (legalArg_rel target hc hc')
        fun hG' y₁ y₂ hy => hk hG' _ _ (TRel.singleL target hy)
  | fsqrt t =>
    rcases hargs with _ | ⟨ha, _⟩
    dsimp only [legalOp]
    split
    · exact .hlt
    · exact legalUnaryTree_wf target .fsqrt (fun u => target.vecFloatOpSupported (.fsqrt u) u)
        (fun {_ _ _ _ _ _} _ _ => .hlt) (fun _ {_ _ _ _ _ _} _ _ => .hlt)
        (fun f {_ _ _ _ _ _} h1 c => Wf.let1M _ h1 c)
        t (legalArg_rel target hc ha) fun hG' y₁ y₂ hy => hk hG' _ _ (TRel.singleL target hy)
  | fneg t =>
    rcases hargs with _ | ⟨ha, _⟩
    dsimp only [legalOp]
    split
    · exact .hlt
    · exact legalUnaryTree_wf target .fneg (fun u => target.vecFloatOpSupported (.fneg u) u)
        (fun {_ _ _ _ _ _} _ _ => .hlt) (fun _ {_ _ _ _ _ _} _ _ => .hlt)
        (fun f {_ _ _ _ _ _} h1 c => Wf.let1M _ h1 c)
        t (legalArg_rel target hc ha) fun hG' y₁ y₂ hy => hk hG' _ _ (TRel.singleL target hy)
  | fabs t =>
    rcases hargs with _ | ⟨ha, _⟩
    dsimp only [legalOp]
    split
    · exact .hlt
    · exact legalUnaryTree_wf target .fabs (fun u => target.vecFloatOpSupported (.fabs u) u)
        (fun {_ _ _ _ _ _} _ _ => .hlt) (fun _ {_ _ _ _ _ _} _ _ => .hlt)
        (fun f {_ _ _ _ _ _} h1 c => Wf.let1M _ h1 c)
        t (legalArg_rel target hc ha) fun hG' y₁ y₂ hy => hk hG' _ _ (TRel.singleL target hy)
  | fcmp o t m h =>
    subst h
    rcases hargs with _ | ⟨ha, hargs⟩; rcases hargs with _ | ⟨hb, _⟩
    dsimp only [legalOp]
    split
    · exact .hlt
    · exact legalFCmpTree_wf target o t (legalArg_rel target hc ha) (legalArg_rel target hc hb)
        fun hG' y₁ y₂ hy => hk hG' _ _ (TRel.singleL target hy)
  | fptoui f n =>
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, _⟩
    dsimp only [legalOp]
    rcases ha1 : legalArg target a₁ with ⟨a₁', ⟨⟩⟩; rcases ha2 : legalArg target a₂ with ⟨a₂', ⟨⟩⟩
    have ha' := legalArg_float_rel target hc ha ha1 ha2
    dsimp only
    split
    · exact Wf.let1M _ ha' fun h1 _ _ _ =>
        hk h1 _ _ (TRel.singleL target (TRel.single (ArgRel.imm _)))
    · exact Wf.let1M _ ha' fun h1 r₁ r₂ hr =>
        hk h1 _ _ (TRel.singleL target (TRel.single hr))
  | fptosi f n =>
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, _⟩
    dsimp only [legalOp]
    rcases ha1 : legalArg target a₁ with ⟨a₁', ⟨⟩⟩; rcases ha2 : legalArg target a₂ with ⟨a₂', ⟨⟩⟩
    have ha' := legalArg_float_rel target hc ha ha1 ha2
    dsimp only
    split
    · exact .hlt
    · split
      · exact Wf.let1M _ ha' fun h1 r₁ r₂ hr =>
          hk h1 _ _ (TRel.singleL target (TRel.single hr))
      · exact Wf.let1M _ ha' fun h1 r₁ r₂ hr =>
          emitMaskToN_wf n (target.widenWidth n) hr fun h2 rm₁ rm₂ hrm =>
            hk (sub_trans h1 h2) _ _ (TRel.singleL target (TRel.single hrm))
  | uitofp n f =>
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, _⟩
    dsimp only [legalOp]
    rcases ha1 : legalArg target a₁ with ⟨a₁', ⟨⟩⟩; rcases ha2 : legalArg target a₂ with ⟨a₂', ⟨⟩⟩
    have ha' := legalArg_bits_rel target hc ha ha1 ha2
    dsimp only
    split
    · exact Wf.let1M _ (.imm _) fun h1 r₁ r₂ hr =>
        hk h1 _ _ (TRel.singleL target (TRel.single hr))
    · exact Wf.let1M _ ha' fun h1 r₁ r₂ hr =>
        hk h1 _ _ (TRel.singleL target (TRel.single hr))
  | sitofp n f =>
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, _⟩
    dsimp only [legalOp]
    rcases ha1 : legalArg target a₁ with ⟨a₁', ⟨⟩⟩; rcases ha2 : legalArg target a₂ with ⟨a₂', ⟨⟩⟩
    have ha' := legalArg_bits_rel target hc ha ha1 ha2
    dsimp only
    split
    · exact Wf.let1M _ (.imm _) fun h1 r₁ r₂ hr =>
        hk h1 _ _ (TRel.singleL target (TRel.single hr))
    · exact emitSextToW_wf n (target.widenWidth n) ha' fun h1 sa₁ sa₂ hsa =>
        Wf.let1M _ hsa fun h2 r₁ r₂ hr =>
          hk (sub_trans h1 h2) _ _ (TRel.singleL target (TRel.single hr))
  | fcvt f g =>
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, _⟩
    dsimp only [legalOp]
    rcases ha1 : legalArg target a₁ with ⟨a₁', ⟨⟩⟩; rcases ha2 : legalArg target a₂ with ⟨a₂', ⟨⟩⟩
    have ha' := legalArg_float_rel target hc ha ha1 ha2
    dsimp only
    exact Wf.let1M _ ha' fun h1 r₁ r₂ hr =>
      hk h1 _ _ (TRel.singleL target (TRel.single hr))

theorem legalLoad_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty} :
    ∀ (t : Ty) {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {p₁ : Arg V₁ i64} {p₂ : Arg V₂ i64},
      ArgRel G i64 p₁ p₂ →
      ∀ {k₁ : LVar target V₁ t → Expr V₁ L₁ rs} {k₂ : LVar target V₂ t → Expr V₂ L₂ rs},
      (∀ {G'}, (∀ q ∈ G, q ∈ G') → ∀ y₁ y₂, TRel (ArgRel G') y₁ y₂ → Wf G' D (k₁ y₁) (k₂ y₂)) →
      Wf G D (legalLoad target t p₁ k₁) (legalLoad target t p₂ k₂)
  | .bool, _, _, _, _, hp, _, _, hk =>
    Wf.load1 .bool hp fun h1 y₁ y₂ hy =>
      hk h1 _ _ (TRel.single hy)
  | .bits n, _, _, _, _, hp, _, _, hk => by
    simp only [legalLoad]
    split
    · exact Wf.load1 (.bits (target.widenWidth n)) hp fun h1 y₁ y₂ hy =>
        hk h1 _ _ (TRel.single hy)
    · exact emitLoadBits_wf target.bitWidths n (target.widenWidth n) hp fun hG' r₁ r₂ hr =>
        hk hG' _ _ (TRel.single hr)
  | .float f, _, _, _, _, hp, _, _, hk =>
    Wf.load1 (.float f) hp fun h1 y₁ y₂ hy =>
      hk h1 _ _ (TRel.single hy)
  | .pair a b, G, D, p₁, p₂, hp, k₁, k₂, hk => by
    simp only [legalLoad]
    split
    · next h =>
      exact Wf.load1 (.pair a b) hp fun h1 v₁ v₂ hv =>
        hk h1 _ _ (tupToPacked_rel h (.cons hv .nil))
    · next h =>
      split
      · refine legalLoad_wf a hp fun {G1} h1 la₁ la₂ hla => ?_
        have hstep2 : ∀ {G2 : Ctx V₁ V₂} {hG1 : ∀ q ∈ G1, q ∈ G2} {ptr2₁ : Arg V₁ i64} {ptr2₂ : Arg V₂ i64},
            ArgRel G2 i64 ptr2₁ ptr2₂ →
            Wf G2 D
              (legalLoad target b ptr2₁ fun lb => k₁ (tupToSplit (Bool.eq_false_iff.mpr h) (tupAppend la₁ lb)))
              (legalLoad target b ptr2₂ fun lb => k₂ (tupToSplit (Bool.eq_false_iff.mpr h) (tupAppend la₂ lb))) := by
          intro G2 hG1 ptr2₁ ptr2₂ hptr
          exact legalLoad_wf b hptr fun h2 lb₁ lb₂ hlb =>
            hk (sub_trans h1 (sub_trans hG1 h2)) _ _
              (tupToSplit_rel (Bool.eq_false_iff.mpr h)
                (TRel_tupAppend (TRel_argRel_weaken' (sub_trans hG1 h2) hla) hlb))
        by_cases ha0 : a.bytes == 0
        · simp only [ha0, ↓reduceIte]
          exact hstep2 (hG1 := fun _ p => p) (hp.weaken h1)
        · simp only [ha0, Bool.false_eq_true, ↓reduceIte]
          exact Wf.let2 _ (hp.weaken h1) (.imm _) fun h2 p2₁ p2₂ hp2 =>
            hstep2 (hG1 := h2) hp2
      · split
        · exact unpackWords64ToLeaves_wf target (a.pair b) .nil 0 fun h1 fres₁ fres₂ hfres =>
            packLeavesToLegal_wf target (a.pair b) hfres fun h2 res₁ res₂ hres =>
              hk (sub_trans h1 h2) res₁ res₂ hres
        · exact loadByteChunksToWords64_wf (chunkBytes target.bitWidths (Ty.pair a b).bytes) hp 0 .nil (.imm _) 0
            fun h1 ws₁ ws₂ hws =>
              unpackWords64ToLeaves_wf target (a.pair b) hws 0 fun h2 fres₁ fres₂ hfres =>
                packLeavesToLegal_wf target (a.pair b) hfres fun h3 res₁ res₂ hres =>
                  hk (sub_trans h1 (sub_trans h2 h3)) res₁ res₂ hres

theorem legalStore_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty} :
    ∀ (t : Ty) {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
      {xs₁ : LVar target V₁ t} {xs₂ : LVar target V₂ t} {p₁ : Arg V₁ i64} {p₂ : Arg V₂ i64},
      TRel (ArgRel G) xs₁ xs₂ → ArgRel G i64 p₁ p₂ →
      {k₁ : Expr V₁ L₁ rs} → {k₂ : Expr V₂ L₂ rs} →
      (∀ {G'}, (∀ q ∈ G, q ∈ G') → Wf G' D k₁ k₂) →
      Wf G D (legalStore target t xs₁ p₁ k₁) (legalStore target t xs₂ p₂ k₂)
  | .bool, _, _, xs₁, xs₂, _, _, hxs, hp, _, _, hk => by
    rcases xs₁ with ⟨v₁, ⟨⟩⟩; rcases xs₂ with ⟨v₂, ⟨⟩⟩
    cases hxs with | cons hv _ => exact .store hv hp (hk (fun _ q => q))
  | .bits n, _, _, xs₁, xs₂, _, _, hxs, hp, _, _, hk => by
    rcases xs₁ with ⟨v₁, ⟨⟩⟩; rcases xs₂ with ⟨v₂, ⟨⟩⟩
    cases hxs with | cons hv _ =>
    simp only [legalStore]
    split
    · exact .store hv hp (hk (fun _ q => q))
    · exact emitStoreBits_wf target.bitWidths n (target.widenWidth n) hv hp hk
  | .float _, _, _, xs₁, xs₂, _, _, hxs, hp, _, _, hk => by
    rcases xs₁ with ⟨v₁, ⟨⟩⟩; rcases xs₂ with ⟨v₂, ⟨⟩⟩
    cases hxs with | cons hv _ => exact .store hv hp (hk (fun _ q => q))
  | .pair a b, G, D, xs₁, xs₂, p₁, p₂, hxs, hp, k₁, k₂, hk => by
    simp only [legalStore]
    split
    · next h =>
      obtain ⟨h1, _⟩ := TRel.cons_iff.1 (packedToTup_rel h hxs)
      exact .store h1 hp (hk (fun _ q => q))
    · next h =>
      split
      · obtain ⟨ha, hb⟩ := TRel_tupSplit (splitToTup_rel (Bool.eq_false_iff.mpr h) hxs)
        refine legalStore_wf a ha hp fun hG1 => ?_
        by_cases ha0 : a.bytes == 0
        · simp only [ha0, ↓reduceIte]
          exact legalStore_wf b (TRel_argRel_weaken' hG1 hb) (hp.weaken hG1)
            fun hG2 => hk (sub_trans hG1 hG2)
        · simp only [ha0, Bool.false_eq_true, ↓reduceIte]
          exact Wf.let2 _ (hp.weaken hG1) (.imm _) fun hG2 p2₁ p2₂ hp2 =>
            legalStore_wf b (TRel_argRel_weaken' (sub_trans hG1 hG2) hb) hp2
              fun hG3 => hk (sub_trans hG1 (sub_trans hG2 hG3))
      · split
        · exact hk (fun _ q => q)
        · exact splitLegalToLeaves_wf target (.pair a b) hxs fun hG1 fx₁ fx₂ hfx =>
            packLeavesToWords64_wf target (.pair a b) hfx fun hG2 ws₁ ws₂ hws =>
              storeByteChunksFromWords64_wf (chunkBytes target.bitWidths (Ty.pair a b).bytes) hws
                (hp.weaken (sub_trans hG1 hG2)) 0
                fun hG3 => hk (sub_trans hG1 (sub_trans hG2 hG3))

theorem CGood.cons {V₁ V₂ : Ty → Type} {G : Ctx V₁ V₂}
    {LG : Ctx (LVar target V₁) (LVar target V₂)} (hc : CGood target G LG)
    {t : Ty} {x₁ : LVar target V₁ t} {x₂ : LVar target V₂ t} (hx : TRel (ArgRel G) x₁ x₂) :
    CGood target G (⟨t, x₁, x₂⟩ :: LG) := by
  intro t' lv₁ lv₂ hm
  rcases List.mem_cons.1 hm with hhead | htail
  · cases hhead; exact hx
  · exact hc t' lv₁ lv₂ htail

theorem CGood.pushTRel {V₁ V₂ : Ty → Type} {G : Ctx V₁ V₂}
    {LG : Ctx (LVar target V₁) (LVar target V₂)} (hc : CGood target G LG) :
    {ts : List Ty} → {xs₁ : Tup (LVar target V₁) ts} → {xs₂ : Tup (LVar target V₂) ts} →
      TRel (fun _ x₁ x₂ => TRel (ArgRel G) x₁ x₂) xs₁ xs₂ →
      CGood target G (Tup.zip xs₁ xs₂ ++ LG)
  | [], (), (), .nil => hc
  | _ :: _, (_, _), (_, _), .cons hx hxs =>
    CGood.cons target (CGood.pushTRel hc hxs) hx

theorem legalBlocks_wf_aux {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty} :
    ∀ {sig : List (List Ty)}
      {b₁ : Blocks (LVar target V₁) (LLab target L₁) rs sig}
      {b₂ : Blocks (LVar target V₂) (LLab target L₂) rs sig}
      {G : Ctx V₁ V₂} {D : Ctx L₁ L₂},
      (∀ {ts} (i : Member ts sig) (ys₁ : Tup V₁ (target.legalSig ts)) (ys₂ : Tup V₂ (target.legalSig ts)),
        Wf (ys₁.zip ys₂ ++ G) D
          (legalExpr target (b₁.get i (splitParams target ts ys₁)))
          (legalExpr target (b₂.get i (splitParams target ts ys₂)))) →
      WfB G D (legalBlocks target b₁) (legalBlocks target b₂)
  | [], .nil, .nil, _, _, _ => .nil
  | _ :: _, .cons _ _, .cons _ _, _, _, ih => by
    simp only [legalBlocks]
    exact .cons (fun ys₁ ys₂ => ih .here ys₁ ys₂)
      (legalBlocks_wf_aux fun i ys₁ ys₂ => ih (.there i) ys₁ ys₂)

theorem legalExpr_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {LG : Ctx (LVar target V₁) (LVar target V₂)} {LD : Ctx (LLab target L₁) (LLab target L₂)}
    {e₁ : Expr (LVar target V₁) (LLab target L₁) rs}
    {e₂ : Expr (LVar target V₂) (LLab target L₂) rs}
    (hwf : Wf LG LD e₁ e₂) :
    ∀ {G : Ctx V₁ V₂} {D : Ctx L₁ L₂},
      CGood target G LG → DGood target D LD →
      Wf G D (legalExpr target e₁) (legalExpr target e₂) := by
  refine Wf.induct (motive := fun LG' LD' e₁' e₂' _ =>
    ∀ {G : Ctx V₁ V₂} {D : Ctx L₁ L₂},
      CGood target G LG' → DGood target D LD' →
      Wf G D (legalExpr target e₁') (legalExpr target e₂')) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hwf
  · intro LG LD ts op₁ op₂ k₁ k₂ hop hk ihk G D hc hd
    simp only [legalExpr]
    exact legalOp_wf target hc hop fun hG' y₁ y₂ hy =>
      ihk y₁ y₂ (CGood.pushTRel target (CGood.weaken target hG' hc) hy) hd
  · intro LG LD t a₁ a₂ k₁ k₂ ha hk ihk G D hc hd
    simp only [legalExpr]
    split
    · next h64 =>
      refine legalLoad_wf target t (castArgBits_rel h64 (legalArg_bits_fst_rel target hc ha))
        fun hG' y₁ y₂ hy => ihk y₁ y₂ (CGood.cons target (CGood.weaken target hG' hc) hy) hd
    · exact .hlt
  · intro LG LD t v₁ v₂ a₁ a₂ k₁ k₂ hv ha hk ihk G D hc hd
    simp only [legalExpr]
    split
    · next h64 =>
      exact legalStore_wf target t (legalArg_rel target hc hv)
        (castArgBits_rel h64 (legalArg_bits_fst_rel target hc ha))
        fun hG' => ihk (CGood.weaken target hG' hc) hd
    · exact .hlt
  · intro LG LD f as bs args₁ args₂ k₁ k₂ hargs hk ihk G D hc hd
    simp only [legalExpr]
    exact .call f (joinArgs_rel target hc hargs) fun res₁ res₂ =>
      ihk (splitParams target bs res₁) (splitParams target bs res₂) (CGood.pushSplit target hc bs res₁ res₂) hd
  · intro LG LD c₁ c₂ t₁ t₂ e₁ e₂ hcd ht he iht ihe G D hc hd
    simp only [legalExpr]
    exact .jnz (legalArg_bool_fst_rel target hc hcd) (iht hc hd) (ihe hc hd)
  · intro LG LD ts j₁ j₂ args₁ args₂ hj hargs G D hc hd
    simp only [legalExpr]
    exact .jump (hd ts j₁ j₂ hj) (joinArgs_rel target hc hargs)
  · intro LG LD vs₁ vs₂ hvs G D hc hd
    simp only [legalExpr]
    exact .ret (joinArgs_rel target hc hvs)
  · intro LG LD f as args₁ args₂ hargs G D hc hd
    simp only [legalExpr]
    exact .exit f (joinArgs_rel target hc hargs)
  · intro LG LD G D _ _
    simp only [legalExpr]
    exact .hlt
  · intro LG LD sig b₁ b₂ k₁ k₂ hb hk ihb ihk G D hc hd
    simp only [legalExpr]
    refine .group (fun Js₁ Js₂ => legalBlocks_wf_aux target fun i ys₁ ys₂ =>
      ihb (tupLiftMap target.legalSig _ Js₁) (tupLiftMap target.legalSig _ Js₂) i
        (splitParams target _ ys₁) (splitParams target _ ys₂)
        (CGood.pushSplit target hc _ ys₁ ys₂) (DGood.pushLiftMap target hd Js₁ Js₂)) fun Js₁ Js₂ =>
      ihk (tupLiftMap target.legalSig _ Js₁) (tupLiftMap target.legalSig _ Js₂)
        hc (DGood.pushLiftMap target hd Js₁ Js₂)

end LegalWf

theorem Func.legal_wf (target : LegalTarget) {as rs : List Ty} {f : Func as rs} (hf : f.Wf) :
    (f.legal target).Wf := by
  intro V₁ V₂ L₁ L₂ xs₁ xs₂
  have hc0 : CGood target (Tup.zip xs₁ xs₂) [] := fun _ _ _ hm => by cases hm
  have hc1 := CGood.pushSplit target hc0 as xs₁ xs₂
  have hc : CGood target (Tup.zip xs₁ xs₂)
      (Tup.zip (splitParams target as xs₁) (splitParams target as xs₂)) := by
    intro t lv₁ lv₂ hm
    have hmem : ⟨t, lv₁, lv₂⟩ ∈ Tup.zip (splitParams target as xs₁) (splitParams target as xs₂) ++ [] := by
      simp only [List.append_nil]; exact hm
    exact TRel_argRel_weaken' (fun p hp => by rcases List.mem_append.1 hp with h | h <;> exact h) (hc1 t lv₁ lv₂ hmem)
  have hd : DGood target ([] : Ctx L₁ L₂) ([] : Ctx (LLab target L₁) (LLab target L₂)) :=
    fun _ _ _ hm => by cases hm
  exact legalExpr_wf target (hf (LVar target V₁) (LVar target V₂) (LLab target L₁) (LLab target L₂)
    (splitParams target as xs₁) (splitParams target as xs₂)) hc hd

theorem Fn.legal_wf (target : LegalTarget) {fn : Fn} (hfn : fn.Wf) :
    (fn.legal target).Wf :=
  Func.legal_wf target hfn

end LeanQbe.T
