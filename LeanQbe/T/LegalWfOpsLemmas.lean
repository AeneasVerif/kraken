module

public import LeanQbe.T.LegalWfOpsLemmas1

/-!
# Legalization well-formedness preservation (`Func.legal_wf`, Part 2b)
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

section LegalWf

variable (target : LegalTarget)

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
    TRel (f := LVar target V₁) (g := LVar target V₂) (fun _ a₁ a₂ => TRel (ArgRel G) a₁ a₂)
      (as := [Ty.bits n])
      ((Arg.imm (0#(target.widenWidth n)), PUnit.unit), PUnit.unit)
      ((Arg.imm (0#(target.widenWidth n)), PUnit.unit), PUnit.unit) := by
  dsimp only [LVar]
  exact @TRel.singleL target V₁ V₂ G (.bits n) (Arg.imm (0#(target.widenWidth n)), PUnit.unit) _
    (TRel.single (ArgRel.imm _))

private theorem trelSingleBits {V₁ V₂ : Ty → Type} {G : Ctx V₁ V₂} (n : Nat)
    {x₁ : Arg V₁ (.bits (target.widenWidth n))} {x₂ : Arg V₂ (.bits (target.widenWidth n))}
    (h : ArgRel G (.bits (target.widenWidth n)) x₁ x₂) :
    TRel (f := LVar target V₁) (g := LVar target V₂) (fun _ a₁ a₂ => TRel (ArgRel G) a₁ a₂)
      (as := [Ty.bits n])
      ((x₁, PUnit.unit), PUnit.unit) ((x₂, PUnit.unit), PUnit.unit) := by
  dsimp only [LVar]
  exact @TRel.singleL target V₁ V₂ G (.bits n) (x₁, PUnit.unit) (x₂, PUnit.unit) (TRel.single h)

private theorem trelPairBits {V₁ V₂ : Ty → Type} {G : Ctx V₁ V₂} (n : Nat)
    {x₁ : Arg V₁ (.bits (target.widenWidth n))} {x₂ : Arg V₂ (.bits (target.widenWidth n))}
    {y₁ : Arg V₁ (.bits (target.widenWidth n))} {y₂ : Arg V₂ (.bits (target.widenWidth n))}
    (hx : ArgRel G (.bits (target.widenWidth n)) x₁ x₂)
    (hy : ArgRel G (.bits (target.widenWidth n)) y₁ y₂) :
    TRel (f := LVar target V₁) (g := LVar target V₂) (fun _ a₁ a₂ => TRel (ArgRel G) a₁ a₂)
      (as := [Ty.bits n, Ty.bits n])
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
    TRel (f := LVar target V₁) (g := LVar target V₂) (fun _ a₁ a₂ => TRel (ArgRel G) a₁ a₂)
      (as := [Ty.bits n, Ty.bool])
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
      TRel (ArgRel G) args₁ args₂ →
        P { code := code, args := args₁ } { code := code, args := args₂ }) :
    P op₁ op₂ := by
  cases hop; exact h _ _ _ ‹_›

private def unifShiftRhs (V : Ty → Type) (target : LegalTarget) (u : Ty)
  (rhs : Arg (LVar target V) u) : Bool :=
  match rhs with
  | .imm c => (uniformShiftLeaf? u c).isSome
  | _ => false

private theorem unifShiftRhs_eq {V₁ V₂ : Ty → Type} (target : LegalTarget) :
    ∀ (u : Ty) {LG : Ctx (LVar target V₁) (LVar target V₂)} {r₁ r₂},
      ArgRel LG u r₁ r₂ → unifShiftRhs V₁ target u r₁ = unifShiftRhs V₂ target u r₂
  | u, _, _, _, h => by cases h <;> rfl

private theorem legalTys_of_isNativeTy (x : Ty)
    (hx : (target.isLegalTy x && match x with | .bits n => target.widenWidth n == n | _ => true) =
      true) :
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
                    (cast (by rw [heq]) (show Tup (Arg V₂) [u] from (r₂, ())) : Tup (Arg V₂) ts) :=
                      by
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
    rcases hargs with _ | ⟨ha, hargs⟩; rcases hargs with _ | ⟨hb, hargs⟩;
      rcases hargs with _ | ⟨hc', _⟩
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
    rcases hargs with _ | ⟨ha, hargs⟩; rcases hargs with _ | ⟨hb, hargs⟩;
      rcases hargs with _ | ⟨hc', _⟩
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
    rcases hargs with _ | ⟨ha, hargs⟩; rcases hargs with _ | ⟨hb, hargs⟩;
      rcases hargs with _ | ⟨hc', _⟩
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
    rcases hargs with _ | ⟨hc', hargs⟩; rcases hargs with _ | ⟨ha, hargs⟩;
      rcases hargs with _ | ⟨hb, _⟩
    dsimp only [legalOp]
    rcases hc1 : legalArg target c₁ with ⟨c₁', ⟨⟩⟩; rcases hc2 : legalArg target c₂ with ⟨c₂', ⟨⟩⟩
    have hc'' := legalArg_bool_rel target hc hc' hc1 hc2
    dsimp only
    exact legalSelectTree_wf target hc'' t (legalArg_rel target hc ha) (legalArg_rel target hc hb)
      fun hG' y₁ y₂ hy => hk hG' _ _ (TRel.singleL target hy)
  | blend t m h =>
    subst h
    rcases hargs with _ | ⟨hc', hargs⟩; rcases hargs with _ | ⟨ha, hargs⟩;
      rcases hargs with _ | ⟨hb, _⟩
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
          exact emitMaskToN_wf n (target.widenWidth n) (castArgBits_rel heq hsx) fun h2 rm₁ rm₂
            hrm =>
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
          exact emitMaskToN_wf n (target.widenWidth n) (castArgBits_rel heq.symm ha') fun h1 rm₁ rm₂
            hrm =>
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
    rcases hargs with _ | ⟨ha, hargs⟩; rcases hargs with _ | ⟨hb, hargs⟩;
      rcases hargs with _ | ⟨hc', _⟩
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
          (trelPairBitsBool target n (.var List.mem_cons_self)
            (.var (List.mem_cons_of_mem _ List.mem_cons_self)))
      · exact Wf.let1 _ hc'' fun p1 cw₁ cw₂ hcw =>
          Wf.let2 _ (ha'.weaken p1) (hb'.weaken p1) fun p2 ab₁ ab₂ hab =>
            Wf.let2 _ hab (hcw.weaken p2) fun p3 sw₁ sw₂ hsw =>
              emitMaskToN_wf n (target.widenWidth n) hsw fun p4 s₁ s₂ hs =>
                Wf.let2 _ (.imm _) (hsw.weaken p4) fun p5 co₁ co₂ hco =>
                  hk (sub_trans p1 (sub_trans p2 (sub_trans p3 (sub_trans p4 p5)))) _ _
                    (trelPairBitsBool target n (hs.weaken p5) hco)
  | subb n =>
    rcases args₁ with ⟨a₁, b₁, c₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, c₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, hargs⟩; rcases hargs with _ | ⟨hb, hargs⟩;
      rcases hargs with _ | ⟨hc', _⟩
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
          (trelPairBitsBool target n (.var List.mem_cons_self)
            (.var (List.mem_cons_of_mem _ List.mem_cons_self)))
      · refine .let_ (.mk (.subb (target.widenWidth n)) (.cons ha' (.cons hb' (.cons hc'' .nil))))
          fun r₁ r₂ => ?_
        rcases r₁ with ⟨dw₁, bo₁, ⟨⟩⟩; rcases r₂ with ⟨dw₂, bo₂, ⟨⟩⟩
        dsimp only [Tup.zip, List.append]
        exact emitMaskToN_wf n (target.widenWidth n) (.var List.mem_cons_self)
          fun hG1 d₁ d₂ hd =>
            hk (fun _ p => hG1 _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ p))) _ _
              (trelPairBitsBool target n hd
                (.var (hG1 _ (List.mem_cons_of_mem _ List.mem_cons_self))))
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
          (trelPairBits target n (.var List.mem_cons_self)
            (.var (List.mem_cons_of_mem _ List.mem_cons_self)))
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
          (trelPairBits target n (.var List.mem_cons_self)
            (.var (List.mem_cons_of_mem _ List.mem_cons_self)))
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
                hk (fun _ p =>
                  q7 _ (p3 _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (p2 _ (p1 _ p)))))) _ _
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
          exact hk (fun _ q => q) _ _
            (TRel.pairL target (encodeImm_rel target a c.1) (encodeImm_rel target b c.2))
        | var hm =>
          refine .let_ (.mk (.unpair a b) (.cons (.var hm) .nil)) fun p₁ p₂ => ?_
          rcases p₁ with ⟨va₁, vb₁, ⟨⟩⟩; rcases p₂ with ⟨va₂, vb₂, ⟨⟩⟩
          exact unpackToLegal_wf target a (.var List.mem_cons_self) fun h1 la₁ la₂ hla =>
            unpackToLegal_wf target b (.var (h1 _ (List.mem_cons_of_mem _ List.mem_cons_self)))
              fun h2 lb₁ lb₂ hlb =>
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
    rcases hargs with _ | ⟨hc', hargs⟩; rcases hargs with _ | ⟨ha, hargs⟩;
      rcases hargs with _ | ⟨hw, _⟩
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
    · exact sha256rnds2_scalar_wf target hlc hla hlw fun hG' y₁ y₂ hy =>
        hk hG' _ _ (TRel.singleL target hy)
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
    · exact sha256msg1_scalar_wf target hla hlb fun hG' y₁ y₂ hy =>
        hk hG' _ _ (TRel.singleL target hy)
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
    · exact sha256msg2_scalar_wf target hla hlb fun hG' y₁ y₂ hy =>
        hk hG' _ _ (TRel.singleL target hy)
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
    rcases hargs with _ | ⟨ha, hargs⟩; rcases hargs with _ | ⟨hb, hargs⟩;
      rcases hargs with _ | ⟨hc', _⟩
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
        have hstep2 :
          ∀ {G2 : Ctx V₁ V₂} {hG1 : ∀ q ∈ G1, q ∈ G2} {ptr2₁ : Arg V₁ i64} {ptr2₂ : Arg V₂ i64},
            ArgRel G2 i64 ptr2₁ ptr2₂ →
            Wf G2 D
              (legalLoad target b ptr2₁ fun lb =>
                k₁ (tupToSplit (Bool.eq_false_iff.mpr h) (tupAppend la₁ lb)))
              (legalLoad target b ptr2₂ fun lb =>
                k₂ (tupToSplit (Bool.eq_false_iff.mpr h) (tupAppend la₂ lb))) := by
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
        · exact loadByteChunksToWords64_wf (chunkBytes target.bitWidths (Ty.pair a b).bytes) hp 0
            .nil (.imm _) 0
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
      (∀ {ts} (i : Member ts sig) (ys₁ : Tup V₁ (target.legalSig ts))
        (ys₂ : Tup V₂ (target.legalSig ts)),
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
      ihk (splitParams target bs res₁) (splitParams target bs res₂)
        (CGood.pushSplit target hc bs res₁ res₂) hd
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
    have hmem :
      ⟨t, lv₁, lv₂⟩ ∈ Tup.zip (splitParams target as xs₁) (splitParams target as xs₂) ++ [] := by
      simp only [List.append_nil]; exact hm
    exact TRel_argRel_weaken' (fun p hp => by rcases List.mem_append.1 hp with h | h <;> exact h)
      (hc1 t lv₁ lv₂ hmem)
  have hd : DGood target ([] : Ctx L₁ L₂) ([] : Ctx (LLab target L₁) (LLab target L₂)) :=
    fun _ _ _ hm => by cases hm
  exact legalExpr_wf target (hf (LVar target V₁) (LVar target V₂) (LLab target L₁) (LLab target L₂)
    (splitParams target as xs₁) (splitParams target as xs₂)) hc hd

theorem Fn.legal_wf (target : LegalTarget) {fn : Fn} (hfn : fn.Wf) :
    (fn.legal target).Wf :=
  Func.legal_wf target hfn

end LeanQbe.T
