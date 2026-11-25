module

public import LeanQbe.T.LegalWfOpsLemmas1

/-!
# Legalization well-formedness preservation (`Func.legal_wf`, Part 2b)
-/

set_option autoImplicit false

public section

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

section Helpers

variable {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {outRs : List Ty}
variable {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {LG : Ctx (LVar target V₁) (LVar target V₂)}

private abbrev WArg (V : Ty → Type) (n : Nat) := Arg V (.bits (target.widenWidth n))

private theorem trelBitsImmZero (n : Nat) :
    TRel (f := LVar target V₁) (g := LVar target V₂) (fun _ a₁ a₂ => TRel (ArgRel G) a₁ a₂)
      (as := [Ty.bits n])
      ((Arg.imm (0#(target.widenWidth n)), PUnit.unit), PUnit.unit)
      ((Arg.imm (0#(target.widenWidth n)), PUnit.unit), PUnit.unit) := by
  dsimp only [LVar]
  exact @TRel.singleL target V₁ V₂ G (.bits n) (Arg.imm (0#(target.widenWidth n)), PUnit.unit) _
    (TRel.single (ArgRel.imm _))

private theorem trelSingleBits (n : Nat) {x₁ : WArg target V₁ n} {x₂ : WArg target V₂ n}
    (h : ArgRel G (.bits (target.widenWidth n)) x₁ x₂) :
    TRel (f := LVar target V₁) (g := LVar target V₂) (fun _ a₁ a₂ => TRel (ArgRel G) a₁ a₂)
      (as := [Ty.bits n])
      ((x₁, PUnit.unit), PUnit.unit) ((x₂, PUnit.unit), PUnit.unit) := by
  dsimp only [LVar]
  exact @TRel.singleL target V₁ V₂ G (.bits n) (x₁, PUnit.unit) (x₂, PUnit.unit) (TRel.single h)

private theorem trelPairBits (n : Nat)
    {x₁ y₁ : WArg target V₁ n} {x₂ y₂ : WArg target V₂ n}
    (hx : ArgRel G (.bits (target.widenWidth n)) x₁ x₂)
    (hy : ArgRel G (.bits (target.widenWidth n)) y₁ y₂) :
    TRel (f := LVar target V₁) (g := LVar target V₂) (fun _ a₁ a₂ => TRel (ArgRel G) a₁ a₂)
      (as := [Ty.bits n, Ty.bits n])
      ((x₁, PUnit.unit), (y₁, PUnit.unit), PUnit.unit)
      ((x₂, PUnit.unit), (y₂, PUnit.unit), PUnit.unit) := by
  dsimp only [LVar]
  exact @TRel.pairL target V₁ V₂ G (.bits n) (.bits n) (x₁, PUnit.unit) (x₂, PUnit.unit)
    (y₁, PUnit.unit) (y₂, PUnit.unit) (TRel.single hx) (TRel.single hy)

private theorem trelPairBitsBool (n : Nat)
    {x₁ : WArg target V₁ n} {x₂ : WArg target V₂ n} {y₁ : Arg V₁ .bool} {y₂ : Arg V₂ .bool}
    (hx : ArgRel G (.bits (target.widenWidth n)) x₁ x₂) (hy : ArgRel G .bool y₁ y₂) :
    TRel (f := LVar target V₁) (g := LVar target V₂) (fun _ a₁ a₂ => TRel (ArgRel G) a₁ a₂)
      (as := [Ty.bits n, Ty.bool])
      ((x₁, PUnit.unit), (y₁, PUnit.unit), PUnit.unit)
      ((x₂, PUnit.unit), (y₂, PUnit.unit), PUnit.unit) := by
  dsimp only [LVar]
  exact @TRel.pairL target V₁ V₂ G (.bits n) .bool (x₁, PUnit.unit) (x₂, PUnit.unit)
    (y₁, PUnit.unit) (y₂, PUnit.unit) (TRel.single hx) (TRel.single hy)

private theorem TRel_cast_singleton {ts : List Ty} {t : Ty}
    (heq : ts = [t]) {xs₁ : Tup (Arg V₁) ts} {xs₂ : Tup (Arg V₂) ts}
    (h : TRel (ArgRel G) xs₁ xs₂) :
    ArgRel G t (cast (by rw [heq]) xs₁ : Tup (Arg V₁) [t]).1
               (cast (by rw [heq]) xs₂ : Tup (Arg V₂) [t]).1 := by
  subst heq; cases h with | cons ha _ => exact ha

private theorem TRel_cast_single_eq {u : Ty} {ts : List Ty} (heq : [u] = ts)
    {r₁ : Arg V₁ u} {r₂ : Arg V₂ u} (hr : ArgRel G u r₁ r₂) :
    TRel (ArgRel G) (cast (by rw [heq]) (show Tup (Arg V₁) [u] from (r₁, ())) : Tup (Arg V₁) ts)
                    (cast (by rw [heq]) (show Tup (Arg V₂) [u] from (r₂, ())) : Tup (Arg V₂) ts) :=
                      by
  subst heq; exact TRel.single hr

private theorem legalArg_cons_rel (hc : CGood target G LG) {t u : Ty}
    {a₁ : Arg (LVar target V₁) t} {a₂ : Arg (LVar target V₂) t} (ha : ArgRel LG t a₁ a₂)
    (ht : target.legalTys t = [u])
    {x₁ : Tup (Arg V₁) (target.legalTys t)} {x₂ : Tup (Arg V₂) (target.legalTys t)}
    (h₁ : legalArg target a₁ = x₁) (h₂ : legalArg target a₂ = x₂) :
    ArgRel G u (cast (by rw [ht]) x₁ : Tup (Arg V₁) [u]).1
               (cast (by rw [ht]) x₂ : Tup (Arg V₂) [u]).1 := by
  have r := legalArg_rel target hc ha; rw [h₁, h₂] at r; exact TRel_cast_singleton ht r

private theorem opRel_elim {rs : List Ty} {op₁ : Op V₁ rs} {op₂ : Op V₂ rs}
    (hop : OpRel G op₁ op₂) (P : Op V₁ rs → Op V₂ rs → Prop)
    (h : ∀ {sig} (code : OpCode sig rs) (args₁ : Tup (Arg V₁) sig) (args₂ : Tup (Arg V₂) sig),
      TRel (ArgRel G) args₁ args₂ →
        P { code := code, args := args₁ } { code := code, args := args₂ }) :
    P op₁ op₂ := by
  cases hop; exact h _ _ _ ‹_›

private theorem legalTys_of_isNativeTy (x : Ty)
    (hx : (target.isLegalTy x &&
      match x with | .bits n => target.widenWidth n == n | _ => true) = true) :
    target.legalTys x = [x] := by
  cases x with
  | bool => rfl
  | bits n => simp only [Bool.and_eq_true, beq_iff_eq] at hx; simp [LegalTarget.legalTys, hx.2]
  | float _ => rfl
  | pair _ _ =>
    simp only [Bool.and_true, LegalTarget.isLegalTy] at hx; simp [LegalTarget.legalTys, hx]

/-! ### Parametric step helpers for `legalOp_wf` -/

private theorem let1BitsRet_wf {s : Ty} (n : Nat) {c : OpCode [s] [.bits (target.widenWidth n)]}
    {a₁ : Arg V₁ s} {a₂ : Arg V₂ s} (ha : ArgRel G s a₁ a₂)
    {k₁ : Tup (LVar target V₁) [.bits n] → Expr V₁ L₁ outRs}
    {k₂ : Tup (LVar target V₂) [.bits n] → Expr V₂ L₂ outRs}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂,
      TRel (fun _t x₁ x₂ => TRel (ArgRel G') x₁ x₂) y₁ y₂ → Wf G' D (k₁ y₁) (k₂ y₂)) :
    Wf G D (.let_ (op1 c a₁) fun (r, ()) => k₁ ((.var r, ()), ()))
           (.let_ (op1 c a₂) fun (r, ()) => k₂ ((.var r, ()), ())) :=
  Wf.let1M _ ha fun h1 _ _ hr => hk h1 _ _ (trelSingleBits target n hr)

private theorem let1FloatRet_wf {s : Ty} (f : Fmt) {c : OpCode [s] [.float f]}
    {a₁ : Arg V₁ s} {a₂ : Arg V₂ s} (ha : ArgRel G s a₁ a₂)
    {k₁ : Tup (LVar target V₁) [.float f] → Expr V₁ L₁ outRs}
    {k₂ : Tup (LVar target V₂) [.float f] → Expr V₂ L₂ outRs}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂,
      TRel (fun _t x₁ x₂ => TRel (ArgRel G') x₁ x₂) y₁ y₂ → Wf G' D (k₁ y₁) (k₂ y₂)) :
    Wf G D (.let_ (op1 c a₁) fun (r, ()) => k₁ ((.var r, ()), ()))
           (.let_ (op1 c a₂) fun (r, ()) => k₂ ((.var r, ()), ())) :=
  Wf.let1M _ ha fun h1 _ _ hr =>
    hk h1 _ _ (@TRel.singleL target _ _ _ (.float f) _ _ (TRel.single hr))

private theorem emitMaskRet_wf (n : Nat) {a₁ : WArg target V₁ n} {a₂ : WArg target V₂ n}
    (ha : ArgRel G (.bits (target.widenWidth n)) a₁ a₂)
    {k₁ : Tup (LVar target V₁) [.bits n] → Expr V₁ L₁ outRs}
    {k₂ : Tup (LVar target V₂) [.bits n] → Expr V₂ L₂ outRs}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂,
      TRel (fun _t x₁ x₂ => TRel (ArgRel G') x₁ x₂) y₁ y₂ → Wf G' D (k₁ y₁) (k₂ y₂)) :
    Wf G D (emitMaskToN n (target.widenWidth n) a₁ fun r => k₁ ((r, ()), ()))
           (emitMaskToN n (target.widenWidth n) a₂ fun r => k₂ ((r, ()), ())) :=
  emitMaskToN_wf n (target.widenWidth n) ha fun h1 _ _ hr => hk h1 _ _ (trelSingleBits target n hr)

private theorem ternlogFloat_aux (f : Fmt)
    {x₁ y₁ z₁ : Arg V₁ (.float f)} {x₂ y₂ z₂ : Arg V₂ (.float f)}
    (hx : ArgRel G (.float f) x₁ x₂) (hy : ArgRel G (.float f) y₁ y₂)
    (hz : ArgRel G (.float f) z₁ z₂)
    {e₁ : Arg V₁ (.bits f.width) → Arg V₁ (.bits f.width) →
      Arg V₁ (.bits f.width) → Expr V₁ L₁ outRs}
    {e₂ : Arg V₂ (.bits f.width) → Arg V₂ (.bits f.width) →
      Arg V₂ (.bits f.width) → Expr V₂ L₂ outRs}
    (he : ∀ {G' ax₁ ay₁ az₁ ax₂ ay₂ az₂}, (∀ p ∈ G, p ∈ G') →
      ArgRel G' (.bits f.width) ax₁ ax₂ → ArgRel G' (.bits f.width) ay₁ ay₂ →
      ArgRel G' (.bits f.width) az₁ az₂ → Wf G' D (e₁ ax₁ ay₁ az₁) (e₂ ax₂ ay₂ az₂)) :
    Wf G D
      (.let_ (op1 (.bitcast (.float f) (.bits f.width) rfl) x₁) fun (bx, ()) =>
       .let_ (op1 (.bitcast (.float f) (.bits f.width) rfl) y₁) fun (by', ()) =>
       .let_ (op1 (.bitcast (.float f) (.bits f.width) rfl) z₁) fun (bz, ()) =>
         e₁ (.var bx) (.var by') (.var bz))
      (.let_ (op1 (.bitcast (.float f) (.bits f.width) rfl) x₂) fun (bx, ()) =>
       .let_ (op1 (.bitcast (.float f) (.bits f.width) rfl) y₂) fun (by', ()) =>
       .let_ (op1 (.bitcast (.float f) (.bits f.width) rfl) z₂) fun (bz, ()) =>
         e₂ (.var bx) (.var by') (.var bz)) :=
  Wf.let1 _ hx fun p1 _ _ hbx =>
    Wf.let1 _ (hy.weaken p1) fun p2 _ _ hby =>
      Wf.let1 _ (hz.weaken (sub_trans p1 p2)) fun p3 _ _ hbz =>
        he (sub_trans p1 (sub_trans p2 p3))
          (hbx.weaken (sub_trans p2 p3)) (hby.weaken p3) hbz

private theorem legalTernlog_step (hc : CGood target G LG) (t : Ty) (imm : BitVec 8)
    {args₁ : Tup (Arg (LVar target V₁)) [t, t, t]}
    {args₂ : Tup (Arg (LVar target V₂)) [t, t, t]}
    (hargs : TRel (ArgRel LG) args₁ args₂)
    {k₁ : Tup (LVar target V₁) [t] → Expr V₁ L₁ outRs}
    {k₂ : Tup (LVar target V₂) [t] → Expr V₂ L₂ outRs}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂,
      TRel (fun _t x₁ x₂ => TRel (ArgRel G') x₁ x₂) y₁ y₂ → Wf G' D (k₁ y₁) (k₂ y₂)) :
    Wf G D (legalOp target { code := .ternlog t imm, args := args₁ } k₁)
           (legalOp target { code := .ternlog t imm, args := args₂ } k₂) := by
  rcases hargs with _ | ⟨ha, _ | ⟨hb, _ | ⟨hc', _⟩⟩⟩
  refine legalTernaryTree_wf target (fun u => .ternlog u imm)
    (fun u => target.vecIntOpSupported (.ternlog u imm) u false)
    (fun {_ _ _ _ _ _ _ _ _ _} h1 h2 h3 c => emitTernlogBool_wf h1 h2 h3 imm c) ?_ ?_ t
    (legalArg_rel target hc ha) (legalArg_rel target hc hb) (legalArg_rel target hc hc')
    fun hG' _ _ hy => hk hG' _ _ (TRel.singleL target hy)
  · intro n _ _ _ _ _ _ _ _ _ _ hx hy hz hc''; dsimp only; split
    · exact hc'' (fun _ p => p) _ _ (.imm _)
    · split
      · exact Wf.let3M _ hx hy hz fun h4 _ _ hr =>
          emitMaskToN_wf n (target.widenWidth n) hr fun h5 => hc'' (sub_trans h4 h5)
      · exact emitTernlogBits_wf (target.widenWidth n) hx hy hz imm fun h4 _ _ hr =>
          emitMaskToN_wf n (target.widenWidth n) hr fun h5 => hc'' (sub_trans h4 h5)
  · intro f _ _ _ _ _ _ _ _ _ _ hx hy hz hc''; dsimp only; split
    · exact Wf.let3M _ hx hy hz hc''
    · cases htern : target.scalarTernlog
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact ternlogFloat_aux f hx hy hz fun q3 hbx hby hbz =>
          emitTernlogBits_wf f.width hbx hby hbz imm fun p4 _ _ hbr =>
            Wf.let1 _ hbr fun p5 => hc'' (sub_trans q3 (sub_trans p4 p5))
      · simp only [↓reduceIte]
        exact ternlogFloat_aux f hx hy hz fun q3 hbx hby hbz =>
          Wf.let3 _ hbx hby hbz fun p4 _ _ hbr =>
            Wf.let1 _ hbr fun p5 => hc'' (sub_trans q3 (sub_trans p4 p5))

private theorem legalFsh_else_wf (n : Nat)
    (mkOpLo mkOpHi : (w : Nat) → OpCode [.bits w, .bits w] [.bits w])
    {x₁ y₁ c₁ : WArg target V₁ n} {x₂ y₂ c₂ : WArg target V₂ n}
    (hx : ArgRel G (.bits (target.widenWidth n)) x₁ x₂)
    (hy : ArgRel G (.bits (target.widenWidth n)) y₁ y₂)
    (hc : ArgRel G (.bits (target.widenWidth n)) c₁ c₂)
    {k₁ : Tup (LVar target V₁) [.bits n] → Expr V₁ L₁ outRs}
    {k₂ : Tup (LVar target V₂) [.bits n] → Expr V₂ L₂ outRs}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂,
      TRel (fun _t x₁ x₂ => TRel (ArgRel G') x₁ x₂) y₁ y₂ → Wf G' D (k₁ y₁) (k₂ y₂)) :
    Wf G D
      (emitCountMod n (target.widenWidth n) c₁ fun cm =>
       .let_ (op2 (.sub (.bits (target.widenWidth n))) (.imm (BitVec.ofNat _ n)) cm) fun (nc, ()) =>
       .let_ (op2 (mkOpLo (target.widenWidth n)) x₁ cm) fun (lo, ()) =>
       .let_ (op2 (mkOpHi (target.widenWidth n)) y₁ (.var nc)) fun (hi, ()) =>
       .let_ (op2 (.or (.bits (target.widenWidth n))) (.var lo) (.var hi)) fun (comb, ()) =>
       emitMaskToN n (target.widenWidth n) (.var comb) fun r => k₁ ((r, ()), ()))
      (emitCountMod n (target.widenWidth n) c₂ fun cm =>
       .let_ (op2 (.sub (.bits (target.widenWidth n))) (.imm (BitVec.ofNat _ n)) cm) fun (nc, ()) =>
       .let_ (op2 (mkOpLo (target.widenWidth n)) x₂ cm) fun (lo, ()) =>
       .let_ (op2 (mkOpHi (target.widenWidth n)) y₂ (.var nc)) fun (hi, ()) =>
       .let_ (op2 (.or (.bits (target.widenWidth n))) (.var lo) (.var hi)) fun (comb, ()) =>
       emitMaskToN n (target.widenWidth n) (.var comb) fun r => k₂ ((r, ()), ())) :=
  emitCountMod_wf n (target.widenWidth n) hc fun p1 _ _ hcm =>
  Wf.let2M _ (.imm _) hcm fun p2 _ _ hnc =>
  have q2 := sub_trans p1 p2
  Wf.let2M _ (hx.weaken q2) (hcm.weaken p2) fun p3 _ _ hlo =>
  have q3 := sub_trans q2 p3
  Wf.let2M _ (hy.weaken q3) (hnc.weaken p3) fun p4 _ _ hhi =>
  Wf.let2M _ (hlo.weaken p4) hhi fun p5 _ _ hcb =>
  emitMaskRet_wf target n hcb fun h6 =>
    hk (sub_trans q3 (sub_trans p4 (sub_trans p5 h6)))

private theorem legalBitsUnaryNW_step (hc : CGood target G LG) (n : Nat)
    {args₁ : Tup (Arg (LVar target V₁)) [.bits n]}
    {args₂ : Tup (Arg (LVar target V₂)) [.bits n]}
    (hargs : TRel (ArgRel LG) args₁ args₂) (mkOp : (w : Nat) → OpCode [.bits w] [.bits w])
    {e₁ : WArg target V₁ n → Expr V₁ L₁ outRs} {e₂ : WArg target V₂ n → Expr V₂ L₂ outRs}
    {k₁ : Tup (LVar target V₁) [.bits n] → Expr V₁ L₁ outRs}
    {k₂ : Tup (LVar target V₂) [.bits n] → Expr V₂ L₂ outRs}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂,
      TRel (fun _t x₁ x₂ => TRel (ArgRel G') x₁ x₂) y₁ y₂ → Wf G' D (k₁ y₁) (k₂ y₂))
    (he : ∀ {a₁' : WArg target V₁ n} {a₂' : WArg target V₂ n},
      ArgRel G (.bits (target.widenWidth n)) a₁' a₂' →
      (∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ {r₁ r₂},
        ArgRel G' (.bits (target.widenWidth n)) r₁ r₂ →
        Wf G' D (k₁ ((r₁, ()), ())) (k₂ ((r₂, ()), ()))) →
      Wf G D (e₁ a₁') (e₂ a₂')) :
    Wf G D
      (let (a, ()) := args₁; let (a', ()) := legalArg target a; let w := target.widenWidth n
       if n == 0 then k₁ ((.imm 0#w, ()), ())
       else if n == w then .let_ (op1 (mkOp w) a') fun (r, ()) => k₁ ((.var r, ()), ())
       else e₁ a')
      (let (a, ()) := args₂; let (a', ()) := legalArg target a; let w := target.widenWidth n
       if n == 0 then k₂ ((.imm 0#w, ()), ())
       else if n == w then .let_ (op1 (mkOp w) a') fun (r, ()) => k₂ ((.var r, ()), ())
       else e₂ a') := by
  rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩
  rcases hargs with _ | ⟨ha, _⟩; dsimp only
  rcases ha1 : legalArg target a₁ with ⟨a₁', ⟨⟩⟩; rcases ha2 : legalArg target a₂ with ⟨a₂', ⟨⟩⟩
  have ha' := legalArg_cons_rel target hc ha rfl ha1 ha2
  dsimp only; split
  · exact hk (fun _ p => p) _ _ (trelBitsImmZero target n)
  · split
    · exact let1BitsRet_wf target n ha' hk
    · exact he ha' fun hG' _ _ hr => hk hG' _ _ (trelSingleBits target n hr)

private theorem legalMulw_tail_wf (n : Nat)
    {loW₁ hiW₁ : V₁ (.bits (target.widenWidth n))} {loW₂ hiW₂ : V₂ (.bits (target.widenWidth n))}
    (hloW : ArgRel G (.bits (target.widenWidth n)) (.var loW₁) (.var loW₂))
    (hhiW : ArgRel G (.bits (target.widenWidth n)) (.var hiW₁) (.var hiW₂))
    {k₁ : Tup (LVar target V₁) [.bits n, .bits n] → Expr V₁ L₁ outRs}
    {k₂ : Tup (LVar target V₂) [.bits n, .bits n] → Expr V₂ L₂ outRs}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂,
      TRel (fun _t x₁ x₂ => TRel (ArgRel G') x₁ x₂) y₁ y₂ → Wf G' D (k₁ y₁) (k₂ y₂)) :
    Wf G D
      (emitMaskToN n (target.widenWidth n) (.var loW₁) fun lo =>
       .let_ (op2 (.lshr (.bits (target.widenWidth n))) (.var loW₁) (.imm (BitVec.ofNat _ n)))
         fun (p1, ()) =>
       .let_ (op2 (.shl (.bits (target.widenWidth n))) (.var hiW₁)
         (.imm (BitVec.ofNat _ (target.widenWidth n - n)))) fun (p2, ()) =>
       .let_ (op2 (.or (.bits (target.widenWidth n))) (.var p1) (.var p2)) fun (hiComb, ()) =>
       emitMaskToN n (target.widenWidth n) (.var hiComb) fun hi => k₁ ((lo, ()), (hi, ()), ()))
      (emitMaskToN n (target.widenWidth n) (.var loW₂) fun lo =>
       .let_ (op2 (.lshr (.bits (target.widenWidth n))) (.var loW₂) (.imm (BitVec.ofNat _ n)))
         fun (p1, ()) =>
       .let_ (op2 (.shl (.bits (target.widenWidth n))) (.var hiW₂)
         (.imm (BitVec.ofNat _ (target.widenWidth n - n)))) fun (p2, ()) =>
       .let_ (op2 (.or (.bits (target.widenWidth n))) (.var p1) (.var p2)) fun (hiComb, ()) =>
       emitMaskToN n (target.widenWidth n) (.var hiComb) fun hi =>
         k₂ ((lo, ()), (hi, ()), ())) := by
  refine emitMaskToN_wf n (target.widenWidth n) hloW fun hG1 _ _ hlo => ?_
  exact Wf.let2M _ (hloW.weaken hG1) (.imm _) fun p1 _ _ hp1 =>
    Wf.let2M _ ((hhiW.weaken hG1).weaken p1) (.imm _) fun p2 _ _ hp2 =>
      Wf.let2M _ (hp1.weaken p2) hp2 fun p3 _ _ hcb =>
        emitMaskToN_wf n (target.widenWidth n) hcb fun p4 _ _ hhi =>
          have q4 := sub_trans p1 (sub_trans p2 (sub_trans p3 p4))
          hk (sub_trans hG1 q4) _ _ (trelPairBits target n (hlo.weaken q4) hhi)

private theorem legalSextBin_wf (n : Nat)
    (mkOp : (w : Nat) → OpCode [.bits w, .bits w] [.bits w])
    {a₁ b₁ : WArg target V₁ n} {a₂ b₂ : WArg target V₂ n}
    (ha : ArgRel G (.bits (target.widenWidth n)) a₁ a₂)
    (hb : ArgRel G (.bits (target.widenWidth n)) b₁ b₂)
    {k₁ : Tup (LVar target V₁) [.bits n] → Expr V₁ L₁ outRs}
    {k₂ : Tup (LVar target V₂) [.bits n] → Expr V₂ L₂ outRs}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂,
      TRel (fun _t x₁ x₂ => TRel (ArgRel G') x₁ x₂) y₁ y₂ → Wf G' D (k₁ y₁) (k₂ y₂)) :
    Wf G D
      (emitSextToW n (target.widenWidth n) a₁ fun sa =>
       emitSextToW n (target.widenWidth n) b₁ fun sb =>
       .let_ (op2 (mkOp (target.widenWidth n)) sa sb) fun (r, ()) =>
       emitMaskToN n (target.widenWidth n) (.var r) fun rm => k₁ ((rm, ()), ()))
      (emitSextToW n (target.widenWidth n) a₂ fun sa =>
       emitSextToW n (target.widenWidth n) b₂ fun sb =>
       .let_ (op2 (mkOp (target.widenWidth n)) sa sb) fun (r, ()) =>
       emitMaskToN n (target.widenWidth n) (.var r) fun rm => k₂ ((rm, ()), ())) :=
  emitSextToW_wf n (target.widenWidth n) ha fun h1 _ _ hsa =>
  emitSextToW_wf n (target.widenWidth n) (hb.weaken h1) fun h2 _ _ hsb =>
  Wf.let2M _ (hsa.weaken h2) hsb fun h3 _ _ hr =>
  emitMaskRet_wf target n hr fun h4 => hk (sub_trans h1 (sub_trans h2 (sub_trans h3 h4)))

private theorem legalUnpair_step (hc : CGood target G LG) (a b : Ty)
    {args₁ : Tup (Arg (LVar target V₁)) [.pair a b]}
    {args₂ : Tup (Arg (LVar target V₂)) [.pair a b]}
    (hargs : TRel (ArgRel LG) args₁ args₂)
    {k₁ : Tup (LVar target V₁) [a, b] → Expr V₁ L₁ outRs}
    {k₂ : Tup (LVar target V₂) [a, b] → Expr V₂ L₂ outRs}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂,
      TRel (fun _t x₁ x₂ => TRel (ArgRel G') x₁ x₂) y₁ y₂ → Wf G' D (k₁ y₁) (k₂ y₂)) :
    Wf G D (legalOp target { code := .unpair a b, args := args₁ } k₁)
           (legalOp target { code := .unpair a b, args := args₂ } k₂) := by
  rcases hargs with _ | ⟨hp, _⟩
  have hlp := legalArg_rel target hc hp; dsimp only [legalOp]; split
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
        rcases p₁ with ⟨_, _, ⟨⟩⟩; rcases p₂ with ⟨_, _, ⟨⟩⟩
        exact unpackToLegal_wf target a (.var List.mem_cons_self) fun h1 _ _ hla =>
          unpackToLegal_wf target b (.var (h1 _ (List.mem_cons_of_mem _ List.mem_cons_self)))
            fun h2 _ _ hlb =>
            hk (fun _ q => h2 _ (h1 _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ q))))
              _ _ (TRel.pairL target (TRel_argRel_weaken' h2 hla) hlb)
    exact hunpair h1
  · next h =>
    obtain ⟨hla, hlb⟩ := TRel_tupSplit (splitToTup_rel (Bool.eq_false_iff.mpr h) hlp)
    exact hk (fun _ q => q) _ _ (TRel.pairL target hla hlb)

private theorem legalBitcast_step (hc : CGood target G LG) (t u : Ty) (h : t.size = u.size)
    {args₁ : Tup (Arg (LVar target V₁)) [t]} {args₂ : Tup (Arg (LVar target V₂)) [t]}
    (hargs : TRel (ArgRel LG) args₁ args₂)
    {k₁ : Tup (LVar target V₁) [u] → Expr V₁ L₁ outRs}
    {k₂ : Tup (LVar target V₂) [u] → Expr V₂ L₂ outRs}
    (hk : ∀ {G'}, (∀ p ∈ G, p ∈ G') → ∀ y₁ y₂,
      TRel (fun _t x₁ x₂ => TRel (ArgRel G') x₁ x₂) y₁ y₂ → Wf G' D (k₁ y₁) (k₂ y₂)) :
    Wf G D (legalOp target { code := .bitcast t u h, args := args₁ } k₁)
           (legalOp target { code := .bitcast t u h, args := args₂ } k₂) := by
  rcases hargs with _ | ⟨ha, _⟩
  have hla := legalArg_rel target hc ha; dsimp only [legalOp]; split
  · next heq => subst heq; exact hk (fun _ q => q) _ _ (TRel.singleL target hla)
  · have hsplit := splitLegalToLeaves_wf target t hla fun h1 _ _ hfx =>
      packLeavesToWords64_wf target t hfx fun h2 _ _ hw =>
        unpackWords64ToLeaves_wf target u hw 0 fun h3 _ _ hfu =>
          packLeavesToLegal_wf target u hfu fun h4 _ _ hy =>
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
              fun h1 _ _ hr =>
                hk h1 _ _ (TRel.singleL target
                  (TRel_cast_single_eq (legalTys_of_isNativeTy target _ hu).symm hr)))

end Helpers

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
  | add t | sub t | mul t =>
    rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩; dsimp only [legalOp]; split
    · exact .hlt
    · refine legalBinTree_wf target _ _ (fun _ _ => false) (fun _ _ => false)
        (fun _ {_ _ _} _ => rfl) ?_ ?_ ?_ t (legalArg_rel target hc ha)
        (legalArg_rel target hc hb) (show OptRhsRel target LG t none none from trivial)
        fun hG' _ _ hy => hk hG' _ _ (TRel.singleL target hy)
      · intro _ _ _ _ _ _ _ _ h1 h2 c; exact Wf.let2M _ h1 h2 c
      · intro n _ _ _ _ _ _ _ _ h1 h2 c; exact legalBitsArith_wf target n _ h1 h2 c
      · intro _ _ _ _ _ _ _ _ _ _ _ _; exact .hlt
  | neg t =>
    rcases hargs with _ | ⟨ha, _⟩; dsimp only [legalOp]; split
    · exact .hlt
    · refine legalUnaryTree_wf target .neg (fun u => target.vecIntOpSupported (.neg u) u false)
        (fun {_ _ _ _ _ _} h1 c => c (fun _ p => p) _ _ h1) ?_
        (fun _ {_ _ _ _ _ _} _ _ => .hlt) t (legalArg_rel target hc ha)
        fun hG' _ _ hy => hk hG' _ _ (TRel.singleL target hy)
      intro n _ _ _ _ _ _ hx hc'; split
      · exact hc' (fun _ p => p) _ _ (.imm _)
      · exact Wf.let1M _ hx fun h2 _ _ hr =>
          emitMaskToN_wf n (target.widenWidth n) hr fun h3 => hc' (sub_trans h2 h3)
  | and t | or t | xor t =>
    rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩; dsimp only [legalOp]
    refine legalBinTree_wf target _ _ (fun _ _ => false) (fun _ _ => false)
      (fun _ {_ _ _} _ => rfl) ?_ ?_ ?_ t (legalArg_rel target hc ha)
      (legalArg_rel target hc hb) (show OptRhsRel target LG t none none from trivial)
      fun hG' _ _ hy => hk hG' _ _ (TRel.singleL target hy)
    · intro _ _ _ _ _ _ _ _ h1 h2 c; exact Wf.let2M _ h1 h2 c
    · intro n _ _ _ _ _ _ _ _ h1 h2 c; exact legalBitsArith_wf target n _ h1 h2 c
    · intro f _ _ _ _ _ _ _ _ h1 h2 c; exact legalFloatBit2_wf target _ _ f h1 h2 c
  | not t =>
    rcases hargs with _ | ⟨ha, _⟩
    refine legalUnaryTree_wf target .not (fun u => target.vecIntOpSupported (.not u) u false)
      (fun {_ _ _ _ _ _} h1 c => Wf.let1M _ h1 c) ?_ ?_ t (legalArg_rel target hc ha)
      fun hG' _ _ hy => hk hG' _ _ (TRel.singleL target hy)
    · intro n _ _ _ _ _ _ hx hc'; dsimp only; split
      · exact hc' (fun _ p => p) _ _ (.imm _)
      · split
        · exact Wf.let1M _ hx hc'
        · exact Wf.let1M _ hx fun h2 _ _ hr =>
            emitMaskToN_wf n (target.widenWidth n) hr fun h3 => hc' (sub_trans h2 h3)
    · intro f _ _ _ _ _ _ hx hc'; dsimp only; split
      · exact Wf.let1M _ hx hc'
      · exact Wf.let1M _ hx fun h2 _ _ hbx =>
          Wf.let1M _ hbx fun h3 _ _ hbr =>
            Wf.let1M _ hbr fun h4 => hc' (sub_trans h2 (sub_trans h3 h4))
  | ternlog t imm => exact legalTernlog_step target hc t imm hargs hk
  | shl t | lshr t | ashr t | rotl t | rotr t =>
    rcases args₁ with ⟨_, b₁, ⟨⟩⟩; rcases args₂ with ⟨_, b₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩; dsimp only [legalOp]; split
    · exact .hlt
    · refine legalBinTree_wf target _ _ _ _ (fun u {_ _ _} hr => by cases hr <;> rfl) ?_ ?_ ?_ t
        (legalArg_rel target hc ha) (legalArg_rel target hc hb)
        (show OptRhsRel target LG t (some b₁) (some b₂) from hb)
        fun hG' _ _ hy => hk hG' _ _ (TRel.singleL target hy)
      · intro _ _ _ _ _ _ _ _ h1 _ c; exact c (fun _ p => p) _ _ h1
      · intro n _ _ _ _ _ _ _ _ h1 h2 c; exact legalBitsArith_wf target n _ h1 h2 c
      · intro _ _ _ _ _ _ _ _ _ _ _ _; exact .hlt
  | fshl n | fshr n =>
    rcases args₁ with ⟨a₁, b₁, c₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, c₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, _ | ⟨hb, _ | ⟨hc', _⟩⟩⟩; dsimp only [legalOp]
    rcases ha1 : legalArg target a₁ with ⟨a₁', ⟨⟩⟩; rcases ha2 : legalArg target a₂ with ⟨a₂', ⟨⟩⟩
    rcases hb1 : legalArg target b₁ with ⟨b₁', ⟨⟩⟩; rcases hb2 : legalArg target b₂ with ⟨b₂', ⟨⟩⟩
    rcases hc1 : legalArg target c₁ with ⟨c₁', ⟨⟩⟩; rcases hc2 : legalArg target c₂ with ⟨c₂', ⟨⟩⟩
    have ha' := legalArg_cons_rel target hc ha rfl ha1 ha2
    have hb' := legalArg_cons_rel target hc hb rfl hb1 hb2
    have hc'' := legalArg_cons_rel target hc hc' rfl hc1 hc2
    dsimp only; split
    · exact hk (fun _ p => p) _ _ (trelBitsImmZero target n)
    · split
      · exact Wf.let3M _ ha' hb' hc'' fun h1 _ _ hr => hk h1 _ _ (trelSingleBits target n hr)
      · first
        | exact legalFsh_else_wf target n (fun w => .shl (.bits w)) (fun w => .lshr (.bits w))
            ha' hb' hc'' hk
        | exact legalFsh_else_wf target n (fun w => .lshr (.bits w)) (fun w => .shl (.bits w))
            hb' ha' hc'' hk
  | bswap t =>
    rcases hargs with _ | ⟨ha, _⟩
    exact legalBswapTree_wf target t (legalArg_rel target hc ha) fun hG' _ _ hy =>
      hk hG' _ _ (TRel.singleL target hy)
  | clz n | rbit n =>
    exact legalBitsUnaryNW_step target hc n hargs _ hk fun ha' hk' =>
      Wf.let1M _ ha' fun h1 _ _ hw => Wf.let2M _ hw (.imm _) fun h2 _ _ hr =>
        hk' (sub_trans h1 h2) hr
  | cls n =>
    exact legalBitsUnaryNW_step target hc n hargs .cls hk fun ha' hk' =>
      emitSextToW_wf n (target.widenWidth n) ha' fun h1 _ _ hsa =>
        Wf.let1M _ hsa fun h2 _ _ hcw =>
          Wf.let2M _ hcw (.imm _) fun h3 _ _ hr => hk' (sub_trans h1 (sub_trans h2 h3)) hr
  | ctz n =>
    exact legalBitsUnaryNW_step target hc n hargs .ctz hk fun ha' hk' =>
      Wf.let2M _ ha' (.imm _) fun h1 _ _ hao =>
        Wf.let1M _ hao fun h2 _ _ hr => hk' (sub_trans h1 h2) hr
  | popcnt n =>
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, _⟩; dsimp only [legalOp]
    rcases ha1 : legalArg target a₁ with ⟨a₁', ⟨⟩⟩; rcases ha2 : legalArg target a₂ with ⟨a₂', ⟨⟩⟩
    have ha' := legalArg_cons_rel target hc ha rfl ha1 ha2
    dsimp only; split
    · exact hk (fun _ p => p) _ _ (trelBitsImmZero target n)
    · exact let1BitsRet_wf target n ha' hk
  | cmp o t m h =>
    subst h; rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩; dsimp only [legalOp]; split
    · exact .hlt
    · exact legalCmpTree_wf target o t (legalArg_rel target hc ha) (legalArg_rel target hc hb)
        fun hG' _ _ hy => hk hG' _ _ (TRel.singleL target hy)
  | select t =>
    rcases args₁ with ⟨c₁, _, _, ⟨⟩⟩; rcases args₂ with ⟨c₂, _, _, ⟨⟩⟩
    rcases hargs with _ | ⟨hc', _ | ⟨ha, _ | ⟨hb, _⟩⟩⟩; dsimp only [legalOp]
    rcases hc1 : legalArg target c₁ with ⟨c₁', ⟨⟩⟩; rcases hc2 : legalArg target c₂ with ⟨c₂', ⟨⟩⟩
    exact legalSelectTree_wf target (legalArg_cons_rel target hc hc' rfl hc1 hc2) t
      (legalArg_rel target hc ha) (legalArg_rel target hc hb)
      fun hG' _ _ hy => hk hG' _ _ (TRel.singleL target hy)
  | blend t m h =>
    subst h; rcases hargs with _ | ⟨hc', _ | ⟨ha, _ | ⟨hb, _⟩⟩⟩
    exact legalBlendTree_wf target t (legalArg_rel target hc hc')
      (legalArg_rel target hc ha) (legalArg_rel target hc hb)
      fun hG' _ _ hy => hk hG' _ _ (TRel.singleL target hy)
  | zext m n =>
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, _⟩; dsimp only [legalOp]
    rcases ha1 : legalArg target a₁ with ⟨a₁', ⟨⟩⟩; rcases ha2 : legalArg target a₂ with ⟨a₂', ⟨⟩⟩
    have ha' := legalArg_cons_rel target hc ha rfl ha1 ha2
    dsimp only; split
    · exact .hlt
    · split
      · exact hk (fun _ p => p) _ _ (trelBitsImmZero target n)
      · split
        · next h => exact hk (fun _ p => p) _ _ (trelSingleBits target n (castArgBits_rel h ha'))
        · split
          · exact let1BitsRet_wf target n ha' hk
          · exact .hlt
  | sext m n =>
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, _⟩; dsimp only [legalOp]
    rcases ha1 : legalArg target a₁ with ⟨a₁', ⟨⟩⟩; rcases ha2 : legalArg target a₂ with ⟨a₂', ⟨⟩⟩
    have ha' := legalArg_cons_rel target hc ha rfl ha1 ha2
    dsimp only; split
    · exact .hlt
    · split
      · exact hk (fun _ p => p) _ _ (trelBitsImmZero target n)
      · refine emitSextToW_wf m (target.widenWidth m) ha' fun h1 _ _ hsx => ?_
        split
        · next heq =>
          exact emitMaskRet_wf target n (castArgBits_rel heq hsx) fun h2 => hk (sub_trans h1 h2)
        · split
          · exact Wf.let1M _ hsx fun h2 _ _ hr =>
              emitMaskRet_wf target n hr fun h3 => hk (sub_trans h1 (sub_trans h2 h3))
          · exact .hlt
  | trunc m n =>
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, _⟩; dsimp only [legalOp]
    rcases ha1 : legalArg target a₁ with ⟨a₁', ⟨⟩⟩; rcases ha2 : legalArg target a₂ with ⟨a₂', ⟨⟩⟩
    have ha' := legalArg_cons_rel target hc ha rfl ha1 ha2
    dsimp only; split
    · exact .hlt
    · split
      · exact hk (fun _ p => p) _ _ (trelBitsImmZero target n)
      · split
        · next heq => exact emitMaskRet_wf target n (castArgBits_rel heq.symm ha') hk
        · split
          · exact Wf.let1M _ ha' fun h1 _ _ hr =>
              emitMaskRet_wf target n hr fun h2 => hk (sub_trans h1 h2)
          · exact .hlt
  | ofBool n =>
    rcases args₁ with ⟨c₁, ⟨⟩⟩; rcases args₂ with ⟨c₂, ⟨⟩⟩
    rcases hargs with _ | ⟨hc', _⟩; dsimp only [legalOp]
    rcases hc1 : legalArg target c₁ with ⟨c₁', ⟨⟩⟩; rcases hc2 : legalArg target c₂ with ⟨c₂', ⟨⟩⟩
    have hc'' := legalArg_cons_rel target hc hc' rfl hc1 hc2
    dsimp only; split
    · exact hk (fun _ p => p) _ _ (trelBitsImmZero target n)
    · exact let1BitsRet_wf target n hc'' hk
  | addc n =>
    rcases args₁ with ⟨a₁, b₁, c₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, c₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, _ | ⟨hb, _ | ⟨hc', _⟩⟩⟩; dsimp only [legalOp]
    rcases ha1 : legalArg target a₁ with ⟨a₁', ⟨⟩⟩; rcases ha2 : legalArg target a₂ with ⟨a₂', ⟨⟩⟩
    rcases hb1 : legalArg target b₁ with ⟨b₁', ⟨⟩⟩; rcases hb2 : legalArg target b₂ with ⟨b₂', ⟨⟩⟩
    rcases hc1 : legalArg target c₁ with ⟨c₁', ⟨⟩⟩; rcases hc2 : legalArg target c₂ with ⟨c₂', ⟨⟩⟩
    have ha' := legalArg_cons_rel target hc ha rfl ha1 ha2
    have hb' := legalArg_cons_rel target hc hb rfl hb1 hb2
    have hc'' := legalArg_cons_rel target hc hc' rfl hc1 hc2
    dsimp only; split
    · exact hk (fun _ p => p) _ _ (trelPairBitsBool target n (ArgRel.imm _) hc'')
    · split
      · refine .let_ (.mk _ (.cons ha' (.cons hb' (.cons hc'' .nil)))) fun r₁ r₂ => ?_
        rcases r₁ with ⟨_, _, ⟨⟩⟩; rcases r₂ with ⟨_, _, ⟨⟩⟩; dsimp only [Tup.zip, List.append]
        exact hk (fun _ p => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ p)) _ _
          (trelPairBitsBool target n (.var List.mem_cons_self)
            (.var (List.mem_cons_of_mem _ List.mem_cons_self)))
      · exact Wf.let1 _ hc'' fun p1 _ _ hcw =>
          Wf.let2 _ (ha'.weaken p1) (hb'.weaken p1) fun p2 _ _ hab =>
            Wf.let2 _ hab (hcw.weaken p2) fun p3 _ _ hsw =>
              emitMaskToN_wf n (target.widenWidth n) hsw fun p4 _ _ hs =>
                Wf.let2 _ (.imm _) (hsw.weaken p4) fun p5 _ _ hco =>
                  hk (sub_trans p1 (sub_trans p2 (sub_trans p3 (sub_trans p4 p5)))) _ _
                    (trelPairBitsBool target n (hs.weaken p5) hco)
  | subb n =>
    rcases args₁ with ⟨a₁, b₁, c₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, c₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, _ | ⟨hb, _ | ⟨hc', _⟩⟩⟩; dsimp only [legalOp]
    rcases ha1 : legalArg target a₁ with ⟨a₁', ⟨⟩⟩; rcases ha2 : legalArg target a₂ with ⟨a₂', ⟨⟩⟩
    rcases hb1 : legalArg target b₁ with ⟨b₁', ⟨⟩⟩; rcases hb2 : legalArg target b₂ with ⟨b₂', ⟨⟩⟩
    rcases hc1 : legalArg target c₁ with ⟨c₁', ⟨⟩⟩; rcases hc2 : legalArg target c₂ with ⟨c₂', ⟨⟩⟩
    have ha' := legalArg_cons_rel target hc ha rfl ha1 ha2
    have hb' := legalArg_cons_rel target hc hb rfl hb1 hb2
    have hc'' := legalArg_cons_rel target hc hc' rfl hc1 hc2
    dsimp only; split
    · exact hk (fun _ p => p) _ _ (trelPairBitsBool target n (ArgRel.imm _) hc'')
    · split
      · refine .let_ (.mk _ (.cons ha' (.cons hb' (.cons hc'' .nil)))) fun r₁ r₂ => ?_
        rcases r₁ with ⟨_, _, ⟨⟩⟩; rcases r₂ with ⟨_, _, ⟨⟩⟩; dsimp only [Tup.zip, List.append]
        exact hk (fun _ p => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ p)) _ _
          (trelPairBitsBool target n (.var List.mem_cons_self)
            (.var (List.mem_cons_of_mem _ List.mem_cons_self)))
      · refine .let_ (.mk (.subb (target.widenWidth n)) (.cons ha' (.cons hb' (.cons hc'' .nil))))
          fun r₁ r₂ => ?_
        rcases r₁ with ⟨_, _, ⟨⟩⟩; rcases r₂ with ⟨_, _, ⟨⟩⟩; dsimp only [Tup.zip, List.append]
        exact emitMaskToN_wf n (target.widenWidth n) (.var List.mem_cons_self) fun hG1 _ _ hd =>
          hk (fun _ p => hG1 _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ p))) _ _
            (trelPairBitsBool target n hd
              (.var (hG1 _ (List.mem_cons_of_mem _ List.mem_cons_self))))
  | umulw n =>
    rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩; dsimp only [legalOp]
    rcases ha1 : legalArg target a₁ with ⟨a₁', ⟨⟩⟩; rcases ha2 : legalArg target a₂ with ⟨a₂', ⟨⟩⟩
    rcases hb1 : legalArg target b₁ with ⟨b₁', ⟨⟩⟩; rcases hb2 : legalArg target b₂ with ⟨b₂', ⟨⟩⟩
    have ha' := legalArg_cons_rel target hc ha rfl ha1 ha2
    have hb' := legalArg_cons_rel target hc hb rfl hb1 hb2
    dsimp only; split
    · exact hk (fun _ p => p) _ _ (trelPairBits target n (ArgRel.imm _) (ArgRel.imm _))
    · split
      · refine .let_ (.mk _ (.cons ha' (.cons hb' .nil))) fun r₁ r₂ => ?_
        rcases r₁ with ⟨_, _, ⟨⟩⟩; rcases r₂ with ⟨_, _, ⟨⟩⟩; dsimp only [Tup.zip, List.append]
        exact hk (fun _ p => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ p)) _ _
          (trelPairBits target n (.var List.mem_cons_self)
            (.var (List.mem_cons_of_mem _ List.mem_cons_self)))
      · refine .let_ (.mk (.umulw (target.widenWidth n)) (.cons ha' (.cons hb' .nil)))
          fun r₁ r₂ => ?_
        rcases r₁ with ⟨_, _, ⟨⟩⟩; rcases r₂ with ⟨_, _, ⟨⟩⟩; dsimp only [Tup.zip, List.append]
        exact legalMulw_tail_wf target n (.var List.mem_cons_self)
          (.var (List.mem_cons_of_mem _ List.mem_cons_self))
          (fun hG' _ _ hy => hk (fun _ p => hG' _ (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ p))) _ _ hy)
  | smulw n =>
    rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩; dsimp only [legalOp]
    rcases ha1 : legalArg target a₁ with ⟨a₁', ⟨⟩⟩; rcases ha2 : legalArg target a₂ with ⟨a₂', ⟨⟩⟩
    rcases hb1 : legalArg target b₁ with ⟨b₁', ⟨⟩⟩; rcases hb2 : legalArg target b₂ with ⟨b₂', ⟨⟩⟩
    have ha' := legalArg_cons_rel target hc ha rfl ha1 ha2
    have hb' := legalArg_cons_rel target hc hb rfl hb1 hb2
    dsimp only; split
    · exact hk (fun _ p => p) _ _ (trelPairBits target n (ArgRel.imm _) (ArgRel.imm _))
    · split
      · refine .let_ (.mk _ (.cons ha' (.cons hb' .nil))) fun r₁ r₂ => ?_
        rcases r₁ with ⟨_, _, ⟨⟩⟩; rcases r₂ with ⟨_, _, ⟨⟩⟩; dsimp only [Tup.zip, List.append]
        exact hk (fun _ p => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ p)) _ _
          (trelPairBits target n (.var List.mem_cons_self)
            (.var (List.mem_cons_of_mem _ List.mem_cons_self)))
      · refine emitSextToW_wf n (target.widenWidth n) ha' fun p1 _ _ hsa =>
          emitSextToW_wf n (target.widenWidth n) (hb'.weaken p1) fun p2 _ _ hsb => ?_
        refine .let_ (.mk (.smulw (target.widenWidth n))
          (.cons (hsa.weaken p2) (.cons hsb .nil))) fun r₁ r₂ => ?_
        rcases r₁ with ⟨_, _, ⟨⟩⟩; rcases r₂ with ⟨_, _, ⟨⟩⟩; dsimp only [Tup.zip, List.append]
        exact legalMulw_tail_wf target n (.var List.mem_cons_self)
          (.var (List.mem_cons_of_mem _ List.mem_cons_self))
          (fun hG' _ _ hy => hk (fun _ p => hG' _ (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ (p2 _ (p1 _ p))))) _ _ hy)
  | udiv n | urem n | udiv0 n =>
    rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩; dsimp only [legalOp]
    rcases ha1 : legalArg target a₁ with ⟨a₁', ⟨⟩⟩; rcases ha2 : legalArg target a₂ with ⟨a₂', ⟨⟩⟩
    rcases hb1 : legalArg target b₁ with ⟨b₁', ⟨⟩⟩; rcases hb2 : legalArg target b₂ with ⟨b₂', ⟨⟩⟩
    have ha' := legalArg_cons_rel target hc ha rfl ha1 ha2
    have hb' := legalArg_cons_rel target hc hb rfl hb1 hb2
    dsimp only; split
    · first | exact .hlt | exact hk (fun _ p => p) _ _ (trelBitsImmZero target n)
    · exact Wf.let2M _ ha' hb' fun h1 _ _ hr => hk h1 _ _ (trelSingleBits target n hr)
  | sdiv n | srem n | sdiv0 n =>
    rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩; dsimp only [legalOp]
    rcases ha1 : legalArg target a₁ with ⟨a₁', ⟨⟩⟩; rcases ha2 : legalArg target a₂ with ⟨a₂', ⟨⟩⟩
    rcases hb1 : legalArg target b₁ with ⟨b₁', ⟨⟩⟩; rcases hb2 : legalArg target b₂ with ⟨b₂', ⟨⟩⟩
    have ha' := legalArg_cons_rel target hc ha rfl ha1 ha2
    have hb' := legalArg_cons_rel target hc hb rfl hb1 hb2
    dsimp only; split
    · first | exact .hlt | exact hk (fun _ p => p) _ _ (trelBitsImmZero target n)
    · split
      · exact Wf.let2M _ ha' hb' fun h1 _ _ hr => hk h1 _ _ (trelSingleBits target n hr)
      · exact legalSextBin_wf target n _ ha' hb' hk
  | mkpair a b =>
    rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩
    have hla := legalArg_rel target hc ha; have hlb := legalArg_rel target hc hb
    dsimp only [legalOp]; split
    · next h =>
      exact packFromLegal_wf target a hla fun h1 _ _ hpa =>
        packFromLegal_wf target b (TRel_argRel_weaken' h1 hlb) fun h2 _ _ hpb =>
          Wf.let2M (.mkpair a b) (hpa.weaken h2) hpb fun h3 _ _ hp =>
            hk (sub_trans h1 (sub_trans h2 h3)) _ _
              (TRel.singleL target (tupToPacked_rel h (TRel.single hp)))
    · next h =>
      exact hk (fun _ q => q) _ _
        (TRel.singleL target (tupToSplit_rel (Bool.eq_false_iff.mpr h) (TRel_tupAppend hla hlb)))
  | unpair a b => exact legalUnpair_step target hc a b hargs hk
  | bitcast t u h => exact legalBitcast_step target hc t u h hargs hk
  | shufd t imm =>
    rcases hargs with _ | ⟨ha, _⟩
    exact legalShufd_wf target imm t (legalArg_rel target hc ha) fun hG' _ _ hy =>
      hk hG' _ _ (TRel.singleL target hy)
  | shufb t =>
    rcases hargs with _ | ⟨ha, _ | ⟨hm, _⟩⟩
    exact legalShufb_wf target t (legalArg_rel target hc ha) (legalArg_rel target hc hm)
      fun hG' _ _ hy => hk hG' _ _ (TRel.singleL target hy)
  | alignr t imm =>
    rcases hargs with _ | ⟨hi, _ | ⟨lo, _⟩⟩
    exact legalAlignr_wf target imm t (legalArg_rel target hc hi) (legalArg_rel target hc lo)
      fun hG' _ _ hy => hk hG' _ _ (TRel.singleL target hy)
  | blendw t imm =>
    rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩
    exact legalBlendw_wf target imm t (legalArg_rel target hc ha) (legalArg_rel target hc hb)
      fun hG' _ _ hy => hk hG' _ _ (TRel.singleL target hy)
  | sha256rnds2 =>
    rcases hargs with _ | ⟨hc', _ | ⟨ha, _ | ⟨hw, _⟩⟩⟩
    have hlc := legalArg_rel target hc hc'
    have hla := legalArg_rel target hc ha; have hlw := legalArg_rel target hc hw
    dsimp only [legalOp]; split
    · next hk_and =>
      have hkp : target.keepsPacked v4i32 = true := ((Bool.and_eq_true _ _).mp hk_and).1
      have hl : target.legalTys v4i32 = [v4i32] := by simp [LegalTarget.legalTys, hkp]
      exact Wf.let3 .sha256rnds2 (TRel_cast_singleton hl hlc)
        (TRel_cast_singleton hl hla) (TRel_cast_singleton hl hlw) fun h1 _ _ hr =>
        hk h1 _ _ (TRel.singleL target (TRel_cast_single_eq hl.symm hr))
    · exact sha256rnds2_scalar_wf target hlc hla hlw fun hG' _ _ hy =>
        hk hG' _ _ (TRel.singleL target hy)
  | sha256msg1 =>
    rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩
    have hla := legalArg_rel target hc ha; have hlb := legalArg_rel target hc hb
    dsimp only [legalOp]; split
    · next hk_and =>
      have hkp : target.keepsPacked v4i32 = true := ((Bool.and_eq_true _ _).mp hk_and).1
      have hl : target.legalTys v4i32 = [v4i32] := by simp [LegalTarget.legalTys, hkp]
      exact Wf.let2 .sha256msg1 (TRel_cast_singleton hl hla) (TRel_cast_singleton hl hlb)
        fun h1 _ _ hr => hk h1 _ _ (TRel.singleL target (TRel_cast_single_eq hl.symm hr))
    · exact sha256msg1_scalar_wf target hla hlb fun hG' _ _ hy =>
        hk hG' _ _ (TRel.singleL target hy)
  | sha256msg2 =>
    rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩
    have hla := legalArg_rel target hc ha; have hlb := legalArg_rel target hc hb
    dsimp only [legalOp]; split
    · next hk_and =>
      have hkp : target.keepsPacked v4i32 = true := ((Bool.and_eq_true _ _).mp hk_and).1
      have hl : target.legalTys v4i32 = [v4i32] := by simp [LegalTarget.legalTys, hkp]
      exact Wf.let2 .sha256msg2 (TRel_cast_singleton hl hla) (TRel_cast_singleton hl hlb)
        fun h1 _ _ hr => hk h1 _ _ (TRel.singleL target (TRel_cast_single_eq hl.symm hr))
    · exact sha256msg2_scalar_wf target hla hlb fun hG' _ _ hy =>
        hk hG' _ _ (TRel.singleL target hy)
  | fadd t | fsub t | fmul t | fdiv t =>
    rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩; dsimp only [legalOp]; split
    · exact .hlt
    · exact legalBinTree_wf target _ _ (fun _ _ => false) (fun _ _ => false)
        (fun _ {_ _ _} _ => rfl) (fun {_ _ _ _ _ _ _ _} _ _ _ => .hlt)
        (fun _ {_ _ _ _ _ _ _ _} _ _ _ => .hlt)
        (fun f {_ _ _ _ _ _ _ _} h1 h2 c => Wf.let2M _ h1 h2 c) t (legalArg_rel target hc ha)
        (legalArg_rel target hc hb) (show OptRhsRel target LG t none none from trivial)
        fun hG' _ _ hy => hk hG' _ _ (TRel.singleL target hy)
  | ffma t =>
    rcases hargs with _ | ⟨ha, _ | ⟨hb, _ | ⟨hc', _⟩⟩⟩; dsimp only [legalOp]; split
    · exact .hlt
    · exact legalTernaryTree_wf target .ffma (fun u => target.vecFloatOpSupported (.ffma u) u)
        (fun {_ _ _ _ _ _ _ _ _ _} _ _ _ _ => .hlt) (fun _ {_ _ _ _ _ _ _ _ _ _} _ _ _ _ => .hlt)
        (fun f {_ _ _ _ _ _ _ _ _ _} h1 h2 h3 c => Wf.let3M _ h1 h2 h3 c)
        t (legalArg_rel target hc ha) (legalArg_rel target hc hb) (legalArg_rel target hc hc')
        fun hG' _ _ hy => hk hG' _ _ (TRel.singleL target hy)
  | fsqrt t | fneg t | fabs t =>
    rcases hargs with _ | ⟨ha, _⟩; dsimp only [legalOp]; split
    · exact .hlt
    · exact legalUnaryTree_wf target _ _ (fun {_ _ _ _ _ _} _ _ => .hlt)
        (fun _ {_ _ _ _ _ _} _ _ => .hlt) (fun f {_ _ _ _ _ _} h1 c => Wf.let1M _ h1 c)
        t (legalArg_rel target hc ha) fun hG' _ _ hy => hk hG' _ _ (TRel.singleL target hy)
  | fcmp o t m h =>
    subst h; rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩; dsimp only [legalOp]; split
    · exact .hlt
    · exact legalFCmpTree_wf target o t (legalArg_rel target hc ha) (legalArg_rel target hc hb)
        fun hG' _ _ hy => hk hG' _ _ (TRel.singleL target hy)
  | fptoui f n =>
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, _⟩; dsimp only [legalOp]
    rcases ha1 : legalArg target a₁ with ⟨a₁', ⟨⟩⟩; rcases ha2 : legalArg target a₂ with ⟨a₂', ⟨⟩⟩
    have ha' := legalArg_cons_rel target hc ha rfl ha1 ha2
    dsimp only; split
    · exact Wf.let1M _ ha' fun h1 _ _ _ =>
        hk h1 _ _ (TRel.singleL target (TRel.single (ArgRel.imm _)))
    · exact let1BitsRet_wf target n ha' hk
  | fptosi f n =>
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, _⟩; dsimp only [legalOp]
    rcases ha1 : legalArg target a₁ with ⟨a₁', ⟨⟩⟩; rcases ha2 : legalArg target a₂ with ⟨a₂', ⟨⟩⟩
    have ha' := legalArg_cons_rel target hc ha rfl ha1 ha2
    dsimp only; split
    · exact .hlt
    · split
      · exact let1BitsRet_wf target n ha' hk
      · exact Wf.let1M _ ha' fun h1 _ _ hr =>
          emitMaskRet_wf target n hr fun h2 => hk (sub_trans h1 h2)
  | uitofp n f | sitofp n f =>
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, _⟩; dsimp only [legalOp]
    rcases ha1 : legalArg target a₁ with ⟨a₁', ⟨⟩⟩; rcases ha2 : legalArg target a₂ with ⟨a₂', ⟨⟩⟩
    have ha' := legalArg_cons_rel target hc ha rfl ha1 ha2
    dsimp only; split
    · exact let1FloatRet_wf target f (ArgRel.imm _) hk
    · first
      | exact let1FloatRet_wf target f ha' hk
      | exact emitSextToW_wf n (target.widenWidth n) ha' fun h1 _ _ hsa =>
          Wf.let1M _ hsa fun h2 _ _ hr =>
            hk (sub_trans h1 h2) _ _ (TRel.singleL target (TRel.single hr))
  | fcvt f g =>
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, _⟩; dsimp only [legalOp]
    rcases ha1 : legalArg target a₁ with ⟨a₁', ⟨⟩⟩; rcases ha2 : legalArg target a₂ with ⟨a₂', ⟨⟩⟩
    exact let1FloatRet_wf target g (legalArg_cons_rel target hc ha rfl ha1 ha2) hk

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
    dsimp only [legalLoad]
    split
    · exact Wf.load1 (.bits (target.widenWidth n)) hp fun h1 y₁ y₂ hy =>
        hk h1 _ _ (TRel.single hy)
    · exact emitLoadBits_wf target.bitWidths n (target.widenWidth n) hp fun hG' r₁ r₂ hr =>
        hk hG' _ _ (TRel.single hr)
  | .float f, _, _, _, _, hp, _, _, hk =>
    Wf.load1 (.float f) hp fun h1 y₁ y₂ hy =>
      hk h1 _ _ (TRel.single hy)
  | .pair a b, G, D, p₁, p₂, hp, k₁, k₂, hk => by
    dsimp only [legalLoad]
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
    dsimp only [legalStore]
    split
    · exact .store hv hp (hk (fun _ q => q))
    · exact emitStoreBits_wf target.bitWidths n (target.widenWidth n) hv hp hk
  | .float _, _, _, xs₁, xs₂, _, _, hxs, hp, _, _, hk => by
    rcases xs₁ with ⟨v₁, ⟨⟩⟩; rcases xs₂ with ⟨v₂, ⟨⟩⟩
    cases hxs with | cons hv _ => exact .store hv hp (hk (fun _ q => q))
  | .pair a b, G, D, xs₁, xs₂, p₁, p₂, hxs, hp, k₁, k₂, hk => by
    dsimp only [legalStore]
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
    dsimp only [legalBlocks]
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
    dsimp only [legalExpr]
    exact legalOp_wf target hc hop fun hG' y₁ y₂ hy =>
      ihk y₁ y₂ (CGood.pushTRel target (CGood.weaken target hG' hc) hy) hd
  · intro LG LD t a₁ a₂ k₁ k₂ ha hk ihk G D hc hd
    dsimp only [legalExpr]
    split
    · next h64 =>
      refine legalLoad_wf target t
        (castArgBits_rel h64 (legalArg_cons_rel target hc ha rfl rfl rfl))
        fun hG' y₁ y₂ hy => ihk y₁ y₂ (CGood.cons target (CGood.weaken target hG' hc) hy) hd
    · exact .hlt
  · intro LG LD t v₁ v₂ a₁ a₂ k₁ k₂ hv ha hk ihk G D hc hd
    dsimp only [legalExpr]
    split
    · next h64 =>
      exact legalStore_wf target t (legalArg_rel target hc hv)
        (castArgBits_rel h64 (legalArg_cons_rel target hc ha rfl rfl rfl))
        fun hG' => ihk (CGood.weaken target hG' hc) hd
    · exact .hlt
  · intro LG LD f as bs args₁ args₂ k₁ k₂ hargs hk ihk G D hc hd
    dsimp only [legalExpr]
    exact .call f (joinArgs_rel target hc hargs) fun res₁ res₂ =>
      ihk (splitParams target bs res₁) (splitParams target bs res₂)
        (CGood.pushSplit target hc bs res₁ res₂) hd
  · intro LG LD c₁ c₂ t₁ t₂ e₁ e₂ hcd ht he iht ihe G D hc hd
    dsimp only [legalExpr]
    exact .jnz (legalArg_cons_rel target hc hcd rfl rfl rfl) (iht hc hd) (ihe hc hd)
  · intro LG LD ts j₁ j₂ args₁ args₂ hj hargs G D hc hd
    dsimp only [legalExpr]
    exact .jump (hd ts j₁ j₂ hj) (joinArgs_rel target hc hargs)
  · intro LG LD vs₁ vs₂ hvs G D hc hd
    dsimp only [legalExpr]
    exact .ret (joinArgs_rel target hc hvs)
  · intro LG LD f as args₁ args₂ hargs G D hc hd
    dsimp only [legalExpr]
    exact .exit f (joinArgs_rel target hc hargs)
  · intro LG LD G D _ _
    dsimp only [legalExpr]
    exact .hlt
  · intro LG LD sig b₁ b₂ k₁ k₂ hb hk ihb ihk G D hc hd
    dsimp only [legalExpr]
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