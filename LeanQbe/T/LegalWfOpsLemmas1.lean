module

public import LeanQbe.T.LegalWfBaseLemmas

/-!
# Legalization well-formedness preservation (`Func.legal_wf`, Part 2)
-/

set_option autoImplicit false

public section

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
      (∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, ArgRel G' (.bits (target.widenWidth n)) y₁ y₂ →
        Wf G' D (cont₁ y₁) (cont₂ y₂)) →
      Wf G D (onBits₁ n x₁ cont₁) (onBits₂ n x₂ cont₂))
    (hf : ∀ (f : Fmt) {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {x₁ x₂ cont₁ cont₂},
      ArgRel G (.float f) x₁ x₂ →
      (∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, ArgRel G' (.float f) y₁ y₂ →
        Wf G' D (cont₁ y₁) (cont₂ y₂)) →
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
    dsimp only [legalUnaryTree]
    split
    · next h =>
      obtain ⟨h1, _⟩ := TRel.cons_iff.1 (packedToTup_rel h hxs)
      split
      · exact Wf.let1 (mkCode (.pair t1 t2)) h1 fun hG' r₁ r₂ hr =>
          hk hG' _ _ (tupToPacked_rel h (.cons hr .nil))
      · refine splitLegalToLeaves_wf target (.pair t1 t2) hxs fun hG1 fx₁ fx₂ hfx => ?_
        have hgoS :
          ∀ (u : Ty) {G' : Ctx V₁ V₂} {fxu₁ : Tup (Arg V₁) (target.leafTys u)}
          {fxu₂ : Tup (Arg V₂) (target.leafTys u)},
            TRel (ArgRel G') fxu₁ fxu₂ →
            ∀ {c₁ : Tup (Arg V₁) (target.leafTys u) → Expr V₁ L₁ rs}
              {c₂ : Tup (Arg V₂) (target.leafTys u) → Expr V₂ L₂ rs},
            (∀ {G''}, (∀ p ∈ G', p ∈ G'') → ∀ y₁ y₂, TRel (ArgRel G'') y₁ y₂ →
              Wf G'' D (c₁ y₁) (c₂ y₂)) →
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
        legalUnaryTree_wf mkCode vecSupported hb hn hf t2 (TRel_argRel_weaken' hG1 h2) fun hG2 r2₁
          r2₂ hr2 =>
          hk (sub_trans hG1 hG2) _ _
            (tupToSplit_rel (Bool.eq_false_iff.mpr h)
              (TRel_tupAppend (TRel_argRel_weaken' hG2 hr1) hr2))

theorem legalBswapTree_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty} :
    ∀ (t : Ty) {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
      {xs₁ : Tup (Arg V₁) (target.legalTys t)} {xs₂ : Tup (Arg V₂) (target.legalTys t)},
      TRel (ArgRel G) xs₁ xs₂ →
      ∀ {k₁ : Tup (Arg V₁) (target.legalTys t) → Expr V₁ L₁ rs}
        {k₂ : Tup (Arg V₂) (target.legalTys t) → Expr V₂ L₂ rs},
      (∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, TRel (ArgRel G') y₁ y₂ → Wf G' D (k₁ y₁) (k₂ y₂)) →
      Wf G D (legalBswapTree target t xs₁ k₁) (legalBswapTree target t xs₂ k₂) := by
  intro t G D xs₁ xs₂ hxs k₁ k₂ hk
  dsimp only [legalBswapTree]
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
    {onBool₁ : Arg V₁ .bool → Arg V₁ .bool → Arg V₁ .bool → (Arg V₁ .bool → Expr V₁ L₁ rs) →
      Expr V₁ L₁ rs}
    {onBool₂ : Arg V₂ .bool → Arg V₂ .bool → Arg V₂ .bool → (Arg V₂ .bool → Expr V₂ L₂ rs) →
      Expr V₂ L₂ rs}
    {onBits₁ : (n : Nat) → Arg V₁ (.bits (target.widenWidth n)) →
      Arg V₁ (.bits (target.widenWidth n)) →
      Arg V₁ (.bits (target.widenWidth n)) →
        (Arg V₁ (.bits (target.widenWidth n)) → Expr V₁ L₁ rs) → Expr V₁ L₁ rs}
    {onBits₂ : (n : Nat) → Arg V₂ (.bits (target.widenWidth n)) →
      Arg V₂ (.bits (target.widenWidth n)) →
      Arg V₂ (.bits (target.widenWidth n)) →
        (Arg V₂ (.bits (target.widenWidth n)) → Expr V₂ L₂ rs) → Expr V₂ L₂ rs}
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
      (∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, ArgRel G' (.bits (target.widenWidth n)) y₁ y₂ →
        Wf G' D (cont₁ y₁) (cont₂ y₂)) →
      Wf G D (onBits₁ n a₁ b₁ c₁ cont₁) (onBits₂ n a₂ b₂ c₂ cont₂))
    (hf : ∀ (f : Fmt) {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {a₁ b₁ c₁ a₂ b₂ c₂ cont₁ cont₂},
      ArgRel G (.float f) a₁ a₂ → ArgRel G (.float f) b₁ b₂ → ArgRel G (.float f) c₁ c₂ →
      (∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, ArgRel G' (.float f) y₁ y₂ →
        Wf G' D (cont₁ y₁) (cont₂ y₂)) →
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
    dsimp only [legalTernaryTree]
    split
    · next h =>
      obtain ⟨hx1, _⟩ := TRel.cons_iff.1 (packedToTup_rel h hxs)
      obtain ⟨hy1, _⟩ := TRel.cons_iff.1 (packedToTup_rel h hys)
      obtain ⟨hz1, _⟩ := TRel.cons_iff.1 (packedToTup_rel h hzs)
      split
      · exact Wf.let3 (mkCode (.pair t1 t2)) hx1 hy1 hz1 fun hG' r₁ r₂ hr =>
          hk hG' _ _ (tupToPacked_rel h (.cons hr .nil))
      · refine splitLegalToLeaves_wf target (.pair t1 t2) hxs fun hG1 fx₁ fx₂ hfx =>
          splitLegalToLeaves_wf target (.pair t1 t2) (TRel_argRel_weaken' hG1 hys) fun hG2 fy₁ fy₂
            hfy =>
            splitLegalToLeaves_wf target (.pair t1 t2) (TRel_argRel_weaken' (sub_trans hG1 hG2) hzs)
              fun hG3 fz₁ fz₂ hfz => ?_
        have hgoS : ∀ (u : Ty) {G' : Ctx V₁ V₂}
            {fxu₁ : Tup (Arg V₁) (target.leafTys u)} {fxu₂ : Tup (Arg V₂) (target.leafTys u)}
            {fyu₁ : Tup (Arg V₁) (target.leafTys u)} {fyu₂ : Tup (Arg V₂) (target.leafTys u)}
            {fzu₁ : Tup (Arg V₁) (target.leafTys u)} {fzu₂ : Tup (Arg V₂) (target.leafTys u)},
            TRel (ArgRel G') fxu₁ fxu₂ → TRel (ArgRel G') fyu₁ fyu₂ → TRel (ArgRel G') fzu₁ fzu₂ →
            ∀ {c₁ : Tup (Arg V₁) (target.leafTys u) → Expr V₁ L₁ rs}
              {c₂ : Tup (Arg V₂) (target.leafTys u) → Expr V₂ L₂ rs},
            (∀ {G''}, (∀ p ∈ G', p ∈ G'') → ∀ y₁ y₂, TRel (ArgRel G'') y₁ y₂ →
              Wf G'' D (c₁ y₁) (c₂ y₂)) →
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
              ih2 (TRel_argRel_weaken' hGa hx2) (TRel_argRel_weaken' hGa hy2)
                (TRel_argRel_weaken' hGa hz2)
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
            hk (sub_trans hG1 hG2) _ _
              (tupToSplit_rel hff (TRel_tupAppend (TRel_argRel_weaken' hG2 hr1) hr2))

@[expose]
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
    {onBits₁ : (n : Nat) → Arg V₁ (.bits (target.widenWidth n)) →
      Arg V₁ (.bits (target.widenWidth n)) →
      (Arg V₁ (.bits (target.widenWidth n)) → Expr V₁ L₁ rs) → Expr V₁ L₁ rs}
    {onBits₂ : (n : Nat) → Arg V₂ (.bits (target.widenWidth n)) →
      Arg V₂ (.bits (target.widenWidth n)) →
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
      (∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, ArgRel G' (.bits (target.widenWidth n)) y₁ y₂ →
        Wf G' D (cont₁ y₁) (cont₂ y₂)) →
      Wf G D (onBits₁ n a₁ b₁ cont₁) (onBits₂ n a₂ b₂ cont₂))
    (hf : ∀ (f : Fmt) {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {a₁ b₁ a₂ b₂ cont₁ cont₂},
      ArgRel G (.float f) a₁ a₂ → ArgRel G (.float f) b₁ b₂ →
      (∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, ArgRel G' (.float f) y₁ y₂ →
        Wf G' D (cont₁ y₁) (cont₂ y₂)) →
      Wf G D (onFloat₁ f a₁ b₁ cont₁) (onFloat₂ f a₂ b₂ cont₂)) :
    ∀ (t : Ty) {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {LG : Ctx (LVar target V₁) (LVar target V₂)}
      {xs₁ : Tup (Arg V₁) (target.legalTys t)} {xs₂ : Tup (Arg V₂) (target.legalTys t)}
      {ys₁ : Tup (Arg V₁) (target.legalTys t)} {ys₂ : Tup (Arg V₂) (target.legalTys t)}
      {rhs₁ : Option (Arg (LVar target V₁) t)} {rhs₂ : Option (Arg (LVar target V₂) t)},
      TRel (ArgRel G) xs₁ xs₂ → TRel (ArgRel G) ys₁ ys₂ → OptRhsRel target LG t rhs₁ rhs₂ →
      ∀ {k₁ : Tup (Arg V₁) (target.legalTys t) → Expr V₁ L₁ rs}
        {k₂ : Tup (Arg V₂) (target.legalTys t) → Expr V₂ L₂ rs},
      (∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂, TRel (ArgRel G') y₁ y₂ → Wf G' D (k₁ y₁) (k₂ y₂)) →
      Wf G D (legalBinTree target mkCode vecSupported onBool₁ onBits₁ onFloat₁ uniformImmRhs₁ t xs₁
        ys₁ rhs₁ k₁)
             (legalBinTree target mkCode vecSupported onBool₂ onBits₂ onFloat₂ uniformImmRhs₂ t xs₂
               ys₂ rhs₂ k₂)
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
          splitLegalToLeaves_wf target (.pair t1 t2) (TRel_argRel_weaken' hG1 hys) fun hG2 fy₁ fy₂
            hfy => ?_
        have hgoS : ∀ (u : Ty) {G' : Ctx V₁ V₂}
            {fxu₁ : Tup (Arg V₁) (target.leafTys u)} {fxu₂ : Tup (Arg V₂) (target.leafTys u)}
            {fyu₁ : Tup (Arg V₁) (target.leafTys u)} {fyu₂ : Tup (Arg V₂) (target.leafTys u)},
            TRel (ArgRel G') fxu₁ fxu₂ → TRel (ArgRel G') fyu₁ fyu₂ →
            ∀ {c₁ : Tup (Arg V₁) (target.leafTys u) → Expr V₁ L₁ rs}
              {c₂ : Tup (Arg V₂) (target.leafTys u) → Expr V₂ L₂ rs},
            (∀ {G''}, (∀ p ∈ G', p ∈ G'') → ∀ y₁ y₂, TRel (ArgRel G'') y₁ y₂ →
              Wf G'' D (c₁ y₁) (c₂ y₂)) →
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
              (checkUniformImmShift (.pair t1 t2) (mkCode (.pair t1 t2)) (packedToTup h ys₁).1) =
                true
          · have hvs₂ := hu ▸ hvs
            rw [ite_eq_left hvs, ite_eq_left hvs₂]
            exact Wf.let2 (mkCode (.pair t1 t2)) hx1 hy1 fun hG' r₁ r₂ hr =>
              hk hG' _ _ (tupToPacked_rel h (.cons hr .nil))
          · have hvs₂ : ¬ (vecSupported (.pair t1 t2)
                (checkUniformImmShift (.pair t1 t2) (mkCode (.pair t1 t2)) (packedToTup h ys₂).1) =
                  true) := hu ▸ hvs
            rw [ite_eq_right hvs, ite_eq_right hvs₂]
            cases mkCode (.pair t1 t2) <;> (try dsimp only) <;> exact hscalar
      | some r1 =>
        cases rhs₂ with
        | none => exact False.elim hrhs
        | some r2 =>
          have hu := congrArg (vecSupported (.pair t1 t2)) hyu
          by_cases hvs : vecSupported (.pair t1 t2)
              (checkUniformImmShift (.pair t1 t2) (mkCode (.pair t1 t2)) (packedToTup h ys₁).1) =
                true
          · have hvs₂ := hu ▸ hvs
            rw [ite_eq_left hvs, ite_eq_left hvs₂]
            exact Wf.let2 (mkCode (.pair t1 t2)) hx1 hy1 fun hG' r₁ r₂ hr =>
              hk hG' _ _ (tupToPacked_rel h (.cons hr .nil))
          · have hvs₂ : ¬ (vecSupported (.pair t1 t2)
                (checkUniformImmShift (.pair t1 t2) (mkCode (.pair t1 t2)) (packedToTup h ys₂).1) =
                  true) := hu ▸ hvs
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
                       | (by_cases hsup :
                           target.vecIntOpSupported (.rotr (.pair t1 t2)) (.pair t1 t2) true = true
                          · rw [ite_eq_left hsup, ite_eq_left hsup]; dsimp only
                            exact Wf.let2 (.rotr (.pair t1 t2)) hx1 (.imm _) fun h1 rt₁ rt₂ hrt =>
                              hk h1 _ _ (tupToPacked_rel h (.cons hrt .nil))
                          · rw [ite_eq_right hsup, ite_eq_right hsup]; dsimp only
                            exact hscalar)
                       | (by_cases hsup :
                           (target.vecIntOpSupported (.rotr (.pair t1 t2)) (.pair t1 t2) true &&
                                          target.vecIntOpSupported (.and (.pair t1 t2))
                                            (.pair t1 t2) false) = true
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
          t2 (LG := LG) (TRel_argRel_weaken' hG1 hx2) (TRel_argRel_weaken' hG1 hy2) (rhs₁ := none)
            (rhs₂ := none) trivial
          fun hG2 r2₁ r2₂ hr2 =>
            hk (sub_trans hG1 hG2) _ _
              (tupToSplit_rel hff (TRel_tupAppend (TRel_argRel_weaken' hG2 hr1) hr2))

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
  dsimp only [legalBitsArith]
  split
  · exact hk (fun _ p => p) _ _ (.imm _)
  · cases code
    all_goals first
    | exact .hlt
    | exact Wf.let2 _ ha hb fun h1 r₁ r₂ hr =>
        emitMaskToN_wf n (target.widenWidth n) hr fun h2 y₁ y₂ hy => hk (sub_trans h1 h2) y₁ y₂ hy
    | exact Wf.let2 _ ha hb hk
    | (simp only; split
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
    dsimp only [legalCmpTree.goMask]
    split
    · exact Wf.let2 _ ha hb fun h1 r₁ r₂ hr => hc h1 _ _ (TRel.single hr)
    · exact emitBoolCmp_wf o ha hb fun hG' r₁ r₂ hr => hc hG' _ _ (TRel.single hr)
  | .bits n, _, _, fx₁, fx₂, fy₁, fy₂, hfx, hfy, _, _, hc => by
    rcases fx₁ with ⟨a₁, ⟨⟩⟩; rcases fx₂ with ⟨a₂, ⟨⟩⟩
    rcases fy₁ with ⟨b₁, ⟨⟩⟩; rcases fy₂ with ⟨b₂, ⟨⟩⟩
    cases hfx with | cons ha _ => cases hfy with | cons hb _ =>
    dsimp only [legalCmpTree.goMask]
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
    dsimp only [legalCmpTree.goMask]
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
    dsimp only [legalCmpTree]
    split
    · exact Wf.let2 _ ha hb fun h1 r₁ r₂ hr => hk h1 _ _ (TRel.single hr)
    · exact emitBoolCmp_wf o ha hb fun hG' r₁ r₂ hr => hk hG' _ _ (TRel.single hr)
  | .bits n, _, _, xs₁, xs₂, ys₁, ys₂, hxs, hys, _, _, hk => by
    rcases xs₁ with ⟨a₁, ⟨⟩⟩; rcases xs₂ with ⟨a₂, ⟨⟩⟩
    rcases ys₁ with ⟨b₁, ⟨⟩⟩; rcases ys₂ with ⟨b₂, ⟨⟩⟩
    cases hxs with | cons ha _ => cases hys with | cons hb _ =>
    dsimp only [legalCmpTree]
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
    legalCmpTree_goMask_wf target o (.pair t1 t2) (TRel_argRel_weaken' hG2 hfx) hfy fun hG3 mr₁ mr₂
      hmr =>
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
    dsimp only [legalSelectTree.goSel]
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
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {c₁ : Arg V₁ .bool} {c₂ : Arg V₂ .bool}
      (hc : ArgRel G .bool c₁ c₂) :
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
    dsimp only [legalSelectTree]
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
    dsimp only [legalBlendTree.goBlend]
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
    dsimp only [legalBlendTree]
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
    splitLegalToLeaves_wf target (.pair t1 t2) (TRel_argRel_weaken' (sub_trans hG1 hG2) hys) fun hG3
      fy₁ fy₂ hfy =>
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
    legalFCmpTree_goFCmp_wf target o (.pair t1 t2) (TRel_argRel_weaken' hG2 hfx) hfy fun hG3 mr₁ mr₂
      hmr =>
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
        ArgRel G' i32 r0₁ r0₂ → ArgRel G' i32 r1₁ r1₂ → ArgRel G' i32 r2₁ r2₂ →
          ArgRel G' i32 r3₁ r3₂ →
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
      words2ToDwords4_wf (hy0.weaken hGa) (hy1.weaken hGa) fun hGb _b0₁ _b1₁ _b2₁ _b3₁ _b0₂ _b1₂
        _b2₂ _b3₂ hb0 hb1 hb2 hb3 =>
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
        ArgRel G' i32 r0₁ r0₂ → ArgRel G' i32 r1₁ r1₂ → ArgRel G' i32 r2₁ r2₂ →
          ArgRel G' i32 r3₁ r3₂ →
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
        ArgRel G' i32 r0₁ r0₂ → ArgRel G' i32 r1₁ r1₂ → ArgRel G' i32 r2₁ r2₂ →
          ArgRel G' i32 r3₁ r3₂ →
        Wf G' D (cont₁ r0₁ r1₁ r2₁ r3₁) (cont₂ r0₂ r1₂ r2₂ r3₂)) →
      Wf G D (let (r0, r1, r2, r3) := scalarShufd128 imm a0₁ a1₁ a2₁ a3₁; cont₁ r0 r1 r2 r3)
             (let (r0, r1, r2, r3) := scalarShufd128 imm a0₂ a1₂ a2₂ a3₂; cont₂ r0 r1 r2 r3) := by
    intro G D a0₁ a1₁ a2₁ a3₁ _ _ _ _ a0₂ a1₂ a2₂ a3₂ _ _ _ _ cont₁ cont₂ ha0 ha1 ha2 ha3 _ _ _ _
      hcont
    exact hcont (fun _ p => p) _ _ _ _ _ _ _ _
      (by dsimp only; split <;> assumption)
      (by dsimp only; split <;> assumption)
      (by dsimp only; split <;> assumption)
      (by dsimp only; split <;> assumption)
  intro t G D xs₁ xs₂ hxs k₁ k₂ hk
  induction t generalizing G with
  | bool | bits _ | float _ =>
    dsimp only [legalShufd]
    split
    · exact .hlt
    · exact legalSimdScalar128_wf target h128 _ hxs hxs hk
  | pair a b iha ihb =>
    dsimp only [legalShufd]
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
    dsimp only [legalBlendw]
    split
    · exact .hlt
    · exact legalSimdScalar128_wf target (fun ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 cont =>
        scalarBlendw128_wf imm ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 cont) _ hxs hys hk
  | pair a b iha ihb =>
    dsimp only [legalBlendw]
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
    dsimp only [legalAlignr]
    split
    · exact .hlt
    · exact legalSimdScalar128_wf target (fun hh0 hh1 hh2 hh3 hl0 hl1 hl2 hl3 cont =>
        scalarAlignr128_wf imm hh0 hh1 hh2 hh3 hl0 hl1 hl2 hl3 cont) _ hxs hys hk
  | pair a b iha ihb =>
    dsimp only [legalAlignr]
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
    dsimp only [legalShufb]
    split
    · exact .hlt
    · exact legalSimdScalar128_wf target (fun ha0 ha1 ha2 ha3 hm0 hm1 hm2 hm3 cont =>
        scalarShufb128_wf ha0 ha1 ha2 ha3 hm0 hm1 hm2 hm3 cont) _ hxs hys hk
  | pair a b iha ihb =>
    dsimp only [legalShufb]
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
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ r₁ r₂, ArgRel G' (.float f) r₁ r₂ → Wf G' D (k₁ r₁) (k₂ r₂))
      :
    Wf G D (legalFloatBit2 target mkOp mkFOp f x₁ y₁ k₁)
           (legalFloatBit2 target mkOp mkFOp f x₂ y₂ k₂) := by
  dsimp only [legalFloatBit2]
  split
  · exact Wf.let2 (mkFOp f) hx hy hk
  · exact Wf.let1 _ hx fun h1 bx₁ bx₂ hbx =>
      Wf.let1 _ (hy.weaken h1) fun h2 by₁ by₂ hby =>
        Wf.let2 (mkOp f.width) (hbx.weaken h2) hby fun h3 br₁ br₂ hbr =>
          Wf.let1 _ hbr fun h4 r₁ r₂ hr =>
            hk (sub_trans h1 (sub_trans h2 (sub_trans h3 h4))) r₁ r₂ hr

theorem sha256rnds2_scalar_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
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
  splitLegalToLeaves_wf target v4i32 (TRel_argRel_weaken' (sub_trans p0 p1) hlw) fun p2 _fw₁ _fw₂
    hfw =>
  packLeavesToWords64_wf target v4i32 (TRel_argRel_weaken' (sub_trans p1 p2) hfc) fun p3 _wc₁ _wc₂
    hwc =>
  packLeavesToWords64_wf target v4i32 (TRel_argRel_weaken' (sub_trans p2 p3) hfa) fun p4 _wa₁ _wa₂
    hwa =>
  packLeavesToWords64_wf target v4i32 (TRel_argRel_weaken' (sub_trans p3 p4) hfw) fun p5 _ww₁ _ww₂
    hww =>
  have q5 := sub_trans p0 (sub_trans p1 (sub_trans p2 (sub_trans p3 (sub_trans p4 p5))))
  words2ToDwords4_wf ((listRel_weaken (sub_trans p4 p5) hwc).getD (ArgRel.imm (G := _) (0#64)) 0)
    ((listRel_weaken (sub_trans p4 p5) hwc).getD (ArgRel.imm (G := _) (0#64)) 1) fun p6 _cd0₁ _cd1₁
      _cd2₁ _cd3₁ _cd0₂ _cd1₂ _cd2₂ _cd3₂ hcd0 hcd1 hcd2 hcd3 =>
  words2ToDwords4_wf ((listRel_weaken (sub_trans p5 p6) hwa).getD (ArgRel.imm (G := _) (0#64)) 0)
    ((listRel_weaken (sub_trans p5 p6) hwa).getD (ArgRel.imm (G := _) (0#64)) 1) fun p7 _ab0₁ _ab1₁
      _ab2₁ _ab3₁ _ab0₂ _ab1₂ _ab2₂ _ab3₂ hab0 hab1 hab2 hab3 =>
  words2ToDwords4_wf ((listRel_weaken (sub_trans p6 p7) hww).getD (ArgRel.imm (G := _) (0#64)) 0)
    ((listRel_weaken (sub_trans p6 p7) hww).getD (ArgRel.imm (G := _) (0#64)) 1) fun p8 _wk0₁ _wk1₁
      _wk2₁ _wk3₁ _wk0₂ _wk1₂ _wk2₂ _wk3₂ hwk0 hwk1 _hwk2 _hwk3 =>
  have q8 := sub_trans q5 (sub_trans p6 (sub_trans p7 p8))
  scalarSha256rnds2_wf (hcd0.weaken (sub_trans p7 p8)) (hcd1.weaken (sub_trans p7 p8))
    (hcd2.weaken (sub_trans p7 p8)) (hcd3.weaken (sub_trans p7 p8))
    (hab0.weaken p8) (hab1.weaken p8) (hab2.weaken p8) (hab3.weaken p8) hwk0 hwk1
    fun p9 _r0₁ _r1₁ _r2₁ _r3₁ _r0₂ _r1₂ _r2₂ _r3₂ hr0 hr1 hr2 hr3 =>
  dwords4ToWords2_wf hr0 hr1 hr2 hr3 fun pa _w0₁ _w1₁ _w0₂ _w1₂ hw0 hw1 =>
  unpackWords64ToLeaves_wf target v4i32 (.cons hw0 (.cons hw1 .nil)) 0 fun pb _fres₁ _fres₂ hfres =>
  packLeavesToLegal_wf target v4i32 hfres fun pc y₁ y₂ hy =>
    hk (sub_trans q8 (sub_trans p9 (sub_trans pa (sub_trans pb pc)))) y₁ y₂ hy

theorem sha256msg1_scalar_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
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
    ((listRel_weaken p3 hwa).getD (ArgRel.imm (G := _) (0#64)) 1) fun p4 _a0₁ _a1₁ _a2₁ _a3₁ _a0₂
      _a1₂ _a2₂ _a3₂ ha0 ha1 ha2 ha3 =>
  words2ToDwords4_wf ((listRel_weaken p4 hwb).getD (ArgRel.imm (G := _) (0#64)) 0)
    ((listRel_weaken p4 hwb).getD (ArgRel.imm (G := _) (0#64)) 1) fun p5 _b0₁ _b1₁ _b2₁ _b3₁ _b0₂
      _b1₂ _b2₂ _b3₂ hb0 _hb1 _hb2 _hb3 =>
  scalarSha256msg1_wf (ha0.weaken p5) (ha1.weaken p5) (ha2.weaken p5) (ha3.weaken p5) hb0
    fun p6 _r0₁ _r1₁ _r2₁ _r3₁ _r0₂ _r1₂ _r2₂ _r3₂ hr0 hr1 hr2 hr3 =>
  dwords4ToWords2_wf hr0 hr1 hr2 hr3 fun p7 _w0₁ _w1₁ _w0₂ _w1₂ hw0 hw1 =>
  unpackWords64ToLeaves_wf target v4i32 (.cons hw0 (.cons hw1 .nil)) 0 fun p8 _fres₁ _fres₂ hfres =>
  packLeavesToLegal_wf target v4i32 hfres fun p9 y₁ y₂ hy =>
    hk (sub_trans q3 (sub_trans p4 (sub_trans p5 (sub_trans p6 (sub_trans p7 (sub_trans p8 p9))))))
      y₁ y₂ hy

theorem sha256msg2_scalar_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
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
    ((listRel_weaken p3 hwa).getD (ArgRel.imm (G := _) (0#64)) 1) fun p4 _s0₁ _s1₁ _s2₁ _s3₁ _s0₂
      _s1₂ _s2₂ _s3₂ hs0 hs1 hs2 hs3 =>
  words2ToDwords4_wf ((listRel_weaken p4 hwb).getD (ArgRel.imm (G := _) (0#64)) 0)
    ((listRel_weaken p4 hwb).getD (ArgRel.imm (G := _) (0#64)) 1) fun p5 _w0₁ _w1₁ _w2₁ _w3₁ _w0₂
      _w1₂ _w2₂ _w3₂ _hw0 _hw1 hw2 hw3 =>
  scalarSha256msg2_wf (hs0.weaken p5) (hs1.weaken p5) (hs2.weaken p5) (hs3.weaken p5) hw2 hw3
    fun p6 _r0₁ _r1₁ _r2₁ _r3₁ _r0₂ _r1₂ _r2₂ _r3₂ hr0 hr1 hr2 hr3 =>
  dwords4ToWords2_wf hr0 hr1 hr2 hr3 fun p7 _wr0₁ _wr1₁ _wr0₂ _wr1₂ hwr0 hwr1 =>
  unpackWords64ToLeaves_wf target v4i32 (.cons hwr0 (.cons hwr1 .nil)) 0 fun p8 _fres₁ _fres₂
    hfres =>
  packLeavesToLegal_wf target v4i32 hfres fun p9 y₁ y₂ hy =>
    hk (sub_trans q3 (sub_trans p4 (sub_trans p5 (sub_trans p6 (sub_trans p7 (sub_trans p8 p9))))))
      y₁ y₂ hy


end LegalWf

end LeanQbe.T
