module

public import LeanQbe.T.LegalCheck2a

/-!
# Target legality proofs for `LeanQbe.T.Legal` (Part 2b: Tree Lifters & 128-bit SIMD)
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

section LegalIsLegal

/-! ### Tree lifters & explicit 128-bit SIMD legality -/

private theorem isUniformImmShift_idxArgs_eq_aux {as bs : List Ty} (code : OpCode as bs) :
    ∀ {u : Ty} (h : as = [u, u]) (nv : Nat) (x y : Arg K u),
      isUniformImmShift code (cast (congrArg (Tup (Arg K)) h.symm)
        (show Tup (Arg K) [u, u] from (idxArg nv x, idxArg nv y, ()))) =
        checkUniformImmShift u code y := by
  intro u h nv x y
  cases code <;> (try cases h) <;> cases y <;> rfl

theorem isUniformImmShift_idxArgs_eq (u : Ty) (code : OpCode [u, u] [u])
    (nv : Nat) (x y : Arg K u) :
    isUniformImmShift code (idxArg nv x, idxArg nv y, ()) = checkUniformImmShift u code y :=
  isUniformImmShift_idxArgs_eq_aux code rfl nv x y

theorem legalUnaryTree_isLegal (target : LegalTarget) {Δ : List (List Ty)} {rs : List Ty}
    (P : Ty → Prop) (hP_pair : ∀ a b, P (.pair a b) → P a ∧ P b)
    (mkCode : (u : Ty) → OpCode [u] [u])
    (vecSupported : (u : Ty) → Bool)
    (hmkNe : ∀ u, (mkCode u).isPackBridge = false)
    (hvecOp : ∀ a b, P (.pair a b) → target.keepsPacked (.pair a b) = true →
      vecSupported (.pair a b) = true → target.isLegalOp (mkCode (.pair a b)) false = true)
    (onBool : Arg K .bool → (Arg K .bool → Expr K KL rs) → Expr K KL rs)
    (onBits : (n : Nat) → Arg K (.bits (target.widenWidth n)) →
      (Arg K (.bits (target.widenWidth n)) → Expr K KL rs) → Expr K KL rs)
    (onFloat : (f : Fmt) → Arg K (.float f) → (Arg K (.float f) → Expr K KL rs) → Expr K KL rs)
    (hB : P .bool → ∀ {Γ'} (x : Arg K .bool) (cont : Arg K .bool → Expr K KL rs),
      ArgNormal target Γ' .bool x →
        IsLegalCont target Γ' Δ (fun Γ'' r => ArgNormal target Γ'' .bool r) cont →
      (toTFlat (onBool x cont) Γ'.length Δ.length).isLegal target Γ' Δ = true)
    (hBi : ∀ n, P (.bits n) → ∀ {Γ'} (x : Arg K (.bits (target.widenWidth n)))
        (cont : Arg K (.bits (target.widenWidth n)) → Expr K KL rs),
      ArgNormal target Γ' (.bits (target.widenWidth n)) x →
      IsLegalCont target Γ' Δ (fun Γ'' r => ArgNormal target Γ'' (.bits (target.widenWidth n)) r)
        cont →
      (toTFlat (onBits n x cont) Γ'.length Δ.length).isLegal target Γ' Δ = true)
    (hF : ∀ f, P (.float f) →
      ∀ {Γ'} (x : Arg K (.float f)) (cont : Arg K (.float f) → Expr K KL rs),
      ArgNormal target Γ' (.float f) x →
      IsLegalCont target Γ' Δ (fun Γ'' r => ArgNormal target Γ'' (.float f) r) cont →
      (toTFlat (onFloat f x cont) Γ'.length Δ.length).isLegal target Γ' Δ = true) :
    ∀ (t : Ty) {Γ : List (Ty × VarKind)}, P t →
      (xs : Tup (Arg K) (target.legalTys t)) → ArgsNormal target Γ xs →
      {k : Tup (Arg K) (target.legalTys t) → Expr K KL rs} →
      IsLegalCont target Γ Δ (fun Γ' res => ArgsNormal target Γ' res) k →
      (toTFlat (legalUnaryTree target mkCode vecSupported onBool onBits onFloat t xs k) Γ.length
        Δ.length).isLegal target Γ Δ = true
  | .bool, Γ, hP, (x, ()), hxs, k, hk =>
    hB hP x _ hxs.1 fun Γ' r hExt hr => hk Γ' (r, ()) hExt ⟨hr, trivial⟩
  | .bits n, Γ, hP, (x, ()), hxs, k, hk =>
    hBi n hP x _ hxs.1 fun Γ' r hExt hr => hk Γ' (r, ()) hExt ⟨hr, trivial⟩
  | .float f, Γ, hP, (x, ()), hxs, k, hk =>
    hF f hP x _ hxs.1 fun Γ' r hExt hr => hk Γ' (r, ()) hExt ⟨hr, trivial⟩
  | .pair t1 t2, Γ, hP, xs, hxs, k, hk => by
    obtain ⟨hP1, hP2⟩ := hP_pair t1 t2 hP
    simp only [legalUnaryTree]
    split
    · next hp =>
      by_cases hvs : vecSupported (.pair t1 t2) = true
      · simp only [hvs, ↓reduceIte]
        have hxs' := ArgsNormal_packedToTup hp hxs
        have hunif :
          isUniformImmShift (mkCode (.pair t1 t2)) (idxArg Γ.length (packedToTup hp xs).1, ()) =
          false := by
          cases mkCode (.pair t1 t2) <;> rfl
        have hcode : target.isLegalOp (mkCode (.pair t1 t2)) false = true := hvecOp t1 t2 hP hp hvs
        refine isLegal_let_op1_normal target (mkCode (.pair t1 t2)) (packedToTup hp xs).1 _
          (hmkNe _) hcode hxs'.1 hp ?_
        exact hk _ (tupToPacked hp (.var Γ.length, ())) (CtxExtends.cons _ _)
          (ArgsNormal_tupToPacked hp ⟨ArgNormal.head target Γ hp, trivial⟩)
      · have hvsf : vecSupported (.pair t1 t2) = false := Bool.eq_false_iff.mpr hvs
        simp only [hvsf, Bool.false_eq_true, ↓reduceIte]
        refine splitLegalToLeaves_isLegal target (.pair t1 t2) xs hxs fun Γ1 fx hExt1 hfx => ?_
        have hgoS : ∀ (u : Ty) {Γ' : List (Ty × VarKind)}, P u →
            (fxu : Tup (Arg K) (target.leafTys u)) → ArgsNormal target Γ' fxu →
            ∀ {cont : Tup (Arg K) (target.leafTys u) → Expr K KL rs},
            IsLegalCont target Γ' Δ (fun Γ'' res => ArgsNormal target Γ'' res) cont →
            (toTFlat (legalUnaryTree.goS target onBool onBits onFloat u fxu cont) Γ'.length
              Δ.length).isLegal target Γ' Δ = true := by
          intro u
          induction u with
          | bool =>
            intro Γ' hPu (a, ()) ha cont hcont
            exact hB hPu a _ ha.1 fun Γ'' r hExt hr => hcont Γ'' (r, ()) hExt ⟨hr, trivial⟩
          | bits n =>
            intro Γ' hPu (a, ()) ha cont hcont
            exact hBi n hPu a _ ha.1 fun Γ'' r hExt hr => hcont Γ'' (r, ()) hExt ⟨hr, trivial⟩
          | float f =>
            intro Γ' hPu (a, ()) ha cont hcont
            exact hF f hPu a _ ha.1 fun Γ'' r hExt hr => hcont Γ'' (r, ()) hExt ⟨hr, trivial⟩
          | pair u1 u2 ih1 ih2 =>
            intro Γ' hPu fxu hfxu cont hcont
            obtain ⟨hPu1, hPu2⟩ := hP_pair u1 u2 hPu
            obtain ⟨hx1, hx2⟩ := ArgsNormal_tupSplit hfxu
            refine ih1 hPu1 _ hx1 fun Γa r1 hExta hr1 => ?_
            exact ih2 hPu2 _ (hx2.mono hExta) fun Γb r2 hExtb hr2 =>
              hcont Γb (tupAppend r1 r2) (hExta.trans hExtb)
                (ArgsNormal_tupAppend (hr1.mono hExtb) hr2)
        refine hgoS (.pair t1 t2) hP fx hfx fun Γ2 fres hExt2 hfres => ?_
        exact packLeavesToLegal_isLegal target (.pair t1 t2) fres hfres
          fun Γ3 res hExt3 hres => hk Γ3 res ((hExt1.trans hExt2).trans hExt3) hres
    · next hnp =>
      have hf := Bool.eq_false_iff.mpr hnp
      obtain ⟨hx1, hx2⟩ := ArgsNormal_tupSplit (ArgsNormal_splitToTup hf hxs)
      refine legalUnaryTree_isLegal target P hP_pair mkCode vecSupported hmkNe hvecOp
        onBool onBits onFloat hB hBi hF t1 hP1 _ hx1 fun Γ1 r1 hExt1 hr1 => ?_
      refine legalUnaryTree_isLegal target P hP_pair mkCode vecSupported hmkNe hvecOp
        onBool onBits onFloat hB hBi hF t2 hP2 _ (hx2.mono hExt1) fun Γ2 r2 hExt2 hr2 => ?_
      exact hk Γ2 (tupToSplit hf (tupAppend r1 r2)) (hExt1.trans hExt2)
        (ArgsNormal_tupToSplit hf (ArgsNormal_tupAppend (hr1.mono hExt2) hr2))

theorem Ty.bswapOk_pair (a b : Ty) : (a.pair b).bswapOk = true → a.bswapOk = true ∧
  b.bswapOk = true := by
  simp [Ty.bswapOk, Bool.and_eq_true]

theorem legalBswapTree_isLegal (target : LegalTarget) {Δ : List (List Ty)} {rs : List Ty}
    (hv : target.valid = true) :
    ∀ (t : Ty) {Γ : List (Ty × VarKind)}, target.supportsTy t = true →
      (xs : Tup (Arg K) (target.legalTys t)) → ArgsNormal target Γ xs →
      {k : Tup (Arg K) (target.legalTys t) → Expr K KL rs} →
      IsLegalCont target Γ Δ (fun Γ' res => ArgsNormal target Γ' res) k →
      (toTFlat (legalBswapTree target t xs k) Γ.length Δ.length).isLegal target Γ Δ = true := by
  intro t Γ hsupp xs hxs k hk
  have h64 := valid_mem64 hv
  simp only [legalBswapTree]
  by_cases hbs : t.bswapOk = true
  · simp only [hbs, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    refine legalUnaryTree_isLegal target (fun u => target.supportsTy u = true ∧ u.bswapOk = true)
      (fun a b h => by
        simp only [LegalTarget.supportsTy, Ty.bswapOk, Bool.and_eq_true] at h
        exact ⟨⟨h.1.1, h.2.1⟩, ⟨h.1.2, h.2.2⟩⟩)
      .bswap (fun _ => false) (fun _ => rfl) (fun _ _ _ _ hf => by cases hf)
      _ _ _ (fun h => by have h2 := h.2; simp [Ty.bswapOk] at h2) ?_
      (fun f h => by have h2 := h.2; simp [Ty.bswapOk] at h2)
      t ⟨hsupp, hbs⟩ xs hxs hk
    intro n hPn Γ' x cont hx hcont
    have hw := widenWidth_mem_of_supports hPn.1
    have hwle := le_widenWidth_of_supports hPn.1
    have ⟨_, hw8, _⟩ := valid_bitWidth_spec hv hw
    have hn8 : n % 8 = 0 := by simpa [Ty.bswapOk] using hPn.2
    have hlegW : target.isLegalTy (.bits (target.widenWidth n)) = true := by
      simpa [LegalTarget.isLegalTy] using hw
    by_cases hn0 : (n == 0) = true
    · simp only [hn0, ↓reduceIte]; exact hcont Γ' (.imm 0#_) (CtxExtends.refl Γ') hlegW
    · simp only [hn0, Bool.false_eq_true, ↓reduceIte]
      by_cases hn8' : (n == 8) = true
      · simp only [hn8', ↓reduceIte]; exact hcont Γ' x (CtxExtends.refl Γ') hx
      · simp only [hn8', Bool.false_eq_true, ↓reduceIte]
        have hn16 : 16 ≤ n := by
          have hne0 : n ≠ 0 := by simpa using hn0
          have hne8 : n ≠ 8 := by simpa using hn8'
          omega
        have hw8gt : 8 < target.widenWidth n := by omega
        by_cases hnw : (n == target.widenWidth n) = true
        · simp only [hnw, ↓reduceIte]
          refine isLegal_let_op1_normal target (.bswap (.bits (target.widenWidth n))) x _ rfl
            (by simp [LegalTarget.isLegalOp, hw, hw8, hw8gt]) hx hlegW ?_
          exact hcont _ (.var Γ'.length) (CtxExtends.cons _ _) (ArgNormal.head target Γ' hlegW)
        · simp only [hnw, Bool.false_eq_true, ↓reduceIte, hw8, beq_iff_eq, ↓reduceIte]
          refine isLegal_let_op1_normal target (.bswap (.bits (target.widenWidth n))) x _ rfl
            (by simp [LegalTarget.isLegalOp, hw, hw8, hw8gt]) hx hlegW ?_
          let Γ1 := (.bits (target.widenWidth n), VarKind.normal) :: Γ'
          refine isLegal_let_op2_normal target (.lshr (.bits (target.widenWidth n)))
            (.var Γ'.length) (.imm _) _ rfl
            (by simp [LegalTarget.isLegalOp, hw]) (ArgNormal.head target Γ' hlegW) hlegW hlegW ?_
          let Γ2 := (.bits (target.widenWidth n), VarKind.normal) :: Γ1
          exact hcont Γ2 (.var Γ1.length) ((CtxExtends.cons _ _).trans (CtxExtends.cons _ _))
            (ArgNormal.head target Γ1 hlegW)
  · have hbsf : t.bswapOk = false := Bool.eq_false_iff.mpr hbs
    simp [hbsf, toTFlat_hlt]

theorem legalTernaryTree_isLegal (target : LegalTarget) {Δ : List (List Ty)} {rs : List Ty}
    (P : Ty → Prop) (hP_pair : ∀ a b, P (.pair a b) → P a ∧ P b)
    (mkCode : (u : Ty) → OpCode [u, u, u] [u])
    (vecSupported : (u : Ty) → Bool)
    (hmkNe : ∀ u, (mkCode u).isPackBridge = false)
    (hvecOp : ∀ a b, P (.pair a b) → target.keepsPacked (.pair a b) = true →
      vecSupported (.pair a b) = true → target.isLegalOp (mkCode (.pair a b)) false = true)
    (onBool : Arg K .bool → Arg K .bool → Arg K .bool → (Arg K .bool → Expr K KL rs) → Expr K KL rs)
    (onBits : (n : Nat) → Arg K (.bits (target.widenWidth n)) →
      Arg K (.bits (target.widenWidth n)) →
      Arg K (.bits (target.widenWidth n)) → (Arg K (.bits (target.widenWidth n)) → Expr K KL rs) →
        Expr K KL rs)
    (onFloat : (f : Fmt) → Arg K (.float f) → Arg K (.float f) → Arg K (.float f) →
      (Arg K (.float f) → Expr K KL rs) → Expr K KL rs)
    (hB : P .bool → ∀ {Γ'} (a b c : Arg K .bool) (cont : Arg K .bool → Expr K KL rs),
      ArgNormal target Γ' .bool a → ArgNormal target Γ' .bool b → ArgNormal target Γ' .bool c →
      IsLegalCont target Γ' Δ (fun Γ'' r => ArgNormal target Γ'' .bool r) cont →
      (toTFlat (onBool a b c cont) Γ'.length Δ.length).isLegal target Γ' Δ = true)
    (hBi : ∀ n, P (.bits n) → ∀ {Γ'} (a b c : Arg K (.bits (target.widenWidth n)))
        (cont : Arg K (.bits (target.widenWidth n)) → Expr K KL rs),
      ArgNormal target Γ' (.bits (target.widenWidth n)) a →
        ArgNormal target Γ' (.bits (target.widenWidth n)) b →
      ArgNormal target Γ' (.bits (target.widenWidth n)) c →
      IsLegalCont target Γ' Δ (fun Γ'' r => ArgNormal target Γ'' (.bits (target.widenWidth n)) r)
        cont →
      (toTFlat (onBits n a b c cont) Γ'.length Δ.length).isLegal target Γ' Δ = true)
    (hF : ∀ f, P (.float f) →
      ∀ {Γ'} (a b c : Arg K (.float f)) (cont : Arg K (.float f) → Expr K KL rs),
      ArgNormal target Γ' (.float f) a → ArgNormal target Γ' (.float f) b →
        ArgNormal target Γ' (.float f) c →
      IsLegalCont target Γ' Δ (fun Γ'' r => ArgNormal target Γ'' (.float f) r) cont →
      (toTFlat (onFloat f a b c cont) Γ'.length Δ.length).isLegal target Γ' Δ = true) :
    ∀ (t : Ty) {Γ : List (Ty × VarKind)}, P t →
      (xs ys zs : Tup (Arg K) (target.legalTys t)) →
      ArgsNormal target Γ xs → ArgsNormal target Γ ys → ArgsNormal target Γ zs →
      {k : Tup (Arg K) (target.legalTys t) → Expr K KL rs} →
      IsLegalCont target Γ Δ (fun Γ' res => ArgsNormal target Γ' res) k →
      (toTFlat (legalTernaryTree target mkCode vecSupported onBool onBits onFloat t xs ys zs k)
        Γ.length Δ.length).isLegal target Γ Δ = true
  | .bool, Γ, hP, (a, ()), (b, ()), (c, ()), hxs, hys, hzs, k, hk =>
    hB hP a b c _ hxs.1 hys.1 hzs.1 fun Γ' r hExt hr => hk Γ' (r, ()) hExt ⟨hr, trivial⟩
  | .bits n, Γ, hP, (a, ()), (b, ()), (c, ()), hxs, hys, hzs, k, hk =>
    hBi n hP a b c _ hxs.1 hys.1 hzs.1 fun Γ' r hExt hr => hk Γ' (r, ()) hExt ⟨hr, trivial⟩
  | .float f, Γ, hP, (a, ()), (b, ()), (c, ()), hxs, hys, hzs, k, hk =>
    hF f hP a b c _ hxs.1 hys.1 hzs.1 fun Γ' r hExt hr => hk Γ' (r, ()) hExt ⟨hr, trivial⟩
  | .pair t1 t2, Γ, hP, xs, ys, zs, hxs, hys, hzs, k, hk => by
    obtain ⟨hP1, hP2⟩ := hP_pair t1 t2 hP
    simp only [legalTernaryTree]
    split
    · next hp =>
      by_cases hvs : vecSupported (.pair t1 t2) = true
      · simp only [hvs, ↓reduceIte]
        have hxs' := ArgsNormal_packedToTup hp hxs
        have hys' := ArgsNormal_packedToTup hp hys
        have hzs' := ArgsNormal_packedToTup hp hzs
        have hcode : target.isLegalOp (mkCode (.pair t1 t2)) false = true := hvecOp t1 t2 hP hp hvs
        refine isLegal_let_op3_normal target (mkCode (.pair t1 t2))
          (packedToTup hp xs).1 (packedToTup hp ys).1 (packedToTup hp zs).1 _
          (hmkNe _) hcode hxs'.1 hys'.1 hzs'.1 hp ?_
        exact hk _ (tupToPacked hp (.var Γ.length, ())) (CtxExtends.cons _ _)
          (ArgsNormal_tupToPacked hp ⟨ArgNormal.head target Γ hp, trivial⟩)
      · have hvsf : vecSupported (.pair t1 t2) = false := Bool.eq_false_iff.mpr hvs
        simp only [hvsf, Bool.false_eq_true, ↓reduceIte]
        refine splitLegalToLeaves_isLegal target (.pair t1 t2) xs hxs fun Γ1 fx hExt1 hfx => ?_
        refine splitLegalToLeaves_isLegal target (.pair t1 t2) ys (hys.mono hExt1) fun Γ2 fy hExt2
          hfy => ?_
        have h12 := hExt1.trans hExt2
        refine splitLegalToLeaves_isLegal target (.pair t1 t2) zs (hzs.mono h12) fun Γ3 fz hExt3
          hfz => ?_
        have h13 := h12.trans hExt3
        have hgoS : ∀ (u : Ty) {Γ' : List (Ty × VarKind)}, P u →
            (fxu fyu fzu : Tup (Arg K) (target.leafTys u)) →
            ArgsNormal target Γ' fxu → ArgsNormal target Γ' fyu → ArgsNormal target Γ' fzu →
            ∀ {cont : Tup (Arg K) (target.leafTys u) → Expr K KL rs},
            IsLegalCont target Γ' Δ (fun Γ'' res => ArgsNormal target Γ'' res) cont →
            (toTFlat (legalTernaryTree.goS target onBool onBits onFloat u fxu fyu fzu cont)
              Γ'.length Δ.length).isLegal target Γ' Δ = true := by
          intro u
          induction u with
          | bool =>
            intro Γ' hPu (a, ()) (b, ()) (c, ()) ha hb hc cont hcont
            exact hB hPu a b c _ ha.1 hb.1 hc.1 fun Γ'' r hExt hr =>
              hcont Γ'' (r, ()) hExt ⟨hr, trivial⟩
          | bits n =>
            intro Γ' hPu (a, ()) (b, ()) (c, ()) ha hb hc cont hcont
            exact hBi n hPu a b c _ ha.1 hb.1 hc.1 fun Γ'' r hExt hr =>
              hcont Γ'' (r, ()) hExt ⟨hr, trivial⟩
          | float f =>
            intro Γ' hPu (a, ()) (b, ()) (c, ()) ha hb hc cont hcont
            exact hF f hPu a b c _ ha.1 hb.1 hc.1 fun Γ'' r hExt hr =>
              hcont Γ'' (r, ()) hExt ⟨hr, trivial⟩
          | pair u1 u2 ih1 ih2 =>
            intro Γ' hPu fxu fyu fzu hfxu hfyu hfzu cont hcont
            obtain ⟨hPu1, hPu2⟩ := hP_pair u1 u2 hPu
            obtain ⟨hx1, hx2⟩ := ArgsNormal_tupSplit hfxu
            obtain ⟨hy1, hy2⟩ := ArgsNormal_tupSplit hfyu
            obtain ⟨hz1, hz2⟩ := ArgsNormal_tupSplit hfzu
            refine ih1 hPu1 _ _ _ hx1 hy1 hz1 fun Γa r1 hExta hr1 => ?_
            exact ih2 hPu2 _ _ _ (hx2.mono hExta) (hy2.mono hExta) (hz2.mono hExta)
              fun Γb r2 hExtb hr2 =>
                hcont Γb (tupAppend r1 r2) (hExta.trans hExtb)
                (ArgsNormal_tupAppend (hr1.mono hExtb) hr2)
        refine hgoS (.pair t1 t2) hP fx fy fz (hfx.mono (hExt2.trans hExt3)) (hfy.mono hExt3) hfz
          fun Γ4 fres hExt4 hfres => ?_
        exact packLeavesToLegal_isLegal target (.pair t1 t2) fres hfres
          fun Γ5 res hExt5 hres => hk Γ5 res ((h13.trans hExt4).trans hExt5) hres
    · next hnp =>
      have hf := Bool.eq_false_iff.mpr hnp
      obtain ⟨hx1, hx2⟩ := ArgsNormal_tupSplit (ArgsNormal_splitToTup hf hxs)
      obtain ⟨hy1, hy2⟩ := ArgsNormal_tupSplit (ArgsNormal_splitToTup hf hys)
      obtain ⟨hz1, hz2⟩ := ArgsNormal_tupSplit (ArgsNormal_splitToTup hf hzs)
      refine legalTernaryTree_isLegal target P hP_pair mkCode vecSupported hmkNe hvecOp
        onBool onBits onFloat hB hBi hF t1 hP1 _ _ _ hx1 hy1 hz1 fun Γ1 r1 hExt1 hr1 => ?_
      refine legalTernaryTree_isLegal target P hP_pair mkCode vecSupported hmkNe hvecOp
        onBool onBits onFloat hB hBi hF t2 hP2 _ _ _ (hx2.mono hExt1) (hy2.mono hExt1)
          (hz2.mono hExt1)
        fun Γ2 r2 hExt2 hr2 => ?_
      exact hk Γ2 (tupToSplit hf (tupAppend r1 r2)) (hExt1.trans hExt2)
        (ArgsNormal_tupToSplit hf (ArgsNormal_tupAppend (hr1.mono hExt2) hr2))

theorem legalBinTree_isLegal (target : LegalTarget) {Δ : List (List Ty)} {rs : List Ty}
    (P : Ty → Prop) (hP_pair : ∀ a b, P (.pair a b) → P a ∧ P b)
    (mkCode : (u : Ty) → OpCode [u, u] [u])
    (vecSupported : (u : Ty) → Bool → Bool)
    (hmkNe : ∀ u, (mkCode u).isPackBridge = false)
    (hvecOp : ∀ a b unif, P (.pair a b) → target.keepsPacked (.pair a b) = true →
      vecSupported (.pair a b) unif = true → target.isLegalOp (mkCode (.pair a b)) unif = true)
    (onBool : Arg K .bool → Arg K .bool → (Arg K .bool → Expr K KL rs) → Expr K KL rs)
    (onBits : (n : Nat) → Arg K (.bits (target.widenWidth n)) →
      Arg K (.bits (target.widenWidth n)) →
      (Arg K (.bits (target.widenWidth n)) → Expr K KL rs) → Expr K KL rs)
    (onFloat : (f : Fmt) → Arg K (.float f) → Arg K (.float f) → (Arg K (.float f) → Expr K KL rs) →
      Expr K KL rs)
    (uniformImmRhs : (u : Ty) → Arg (LVar target K) u → Bool)
    (hB : P .bool → ∀ {Γ'} (a b : Arg K .bool) (cont : Arg K .bool → Expr K KL rs),
      ArgNormal target Γ' .bool a → ArgNormal target Γ' .bool b →
      IsLegalCont target Γ' Δ (fun Γ'' r => ArgNormal target Γ'' .bool r) cont →
      (toTFlat (onBool a b cont) Γ'.length Δ.length).isLegal target Γ' Δ = true)
    (hBi : ∀ n, P (.bits n) → ∀ {Γ'} (a b : Arg K (.bits (target.widenWidth n)))
        (cont : Arg K (.bits (target.widenWidth n)) → Expr K KL rs),
      ArgNormal target Γ' (.bits (target.widenWidth n)) a →
        ArgNormal target Γ' (.bits (target.widenWidth n)) b →
      IsLegalCont target Γ' Δ (fun Γ'' r => ArgNormal target Γ'' (.bits (target.widenWidth n)) r)
        cont →
      (toTFlat (onBits n a b cont) Γ'.length Δ.length).isLegal target Γ' Δ = true)
    (hF : ∀ f, P (.float f) →
      ∀ {Γ'} (a b : Arg K (.float f)) (cont : Arg K (.float f) → Expr K KL rs),
      ArgNormal target Γ' (.float f) a → ArgNormal target Γ' (.float f) b →
      IsLegalCont target Γ' Δ (fun Γ'' r => ArgNormal target Γ'' (.float f) r) cont →
      (toTFlat (onFloat f a b cont) Γ'.length Δ.length).isLegal target Γ' Δ = true) :
    ∀ (t : Ty) {Γ : List (Ty × VarKind)}, P t →
      (xs ys : Tup (Arg K) (target.legalTys t)) → (rawRhs : Option (Arg (LVar target K) t)) →
      ArgsNormal target Γ xs → ArgsNormal target Γ ys →
      {k : Tup (Arg K) (target.legalTys t) → Expr K KL rs} →
      IsLegalCont target Γ Δ (fun Γ' res => ArgsNormal target Γ' res) k →
      (toTFlat
        (legalBinTree target mkCode vecSupported onBool onBits onFloat uniformImmRhs t xs ys rawRhs
        k)
        Γ.length Δ.length).isLegal target Γ Δ = true
  | .bool, Γ, hP, (a, ()), (b, ()), _, hxs, hys, k, hk =>
    hB hP a b _ hxs.1 hys.1 fun Γ' r hExt hr => hk Γ' (r, ()) hExt ⟨hr, trivial⟩
  | .bits n, Γ, hP, (a, ()), (b, ()), _, hxs, hys, k, hk =>
    hBi n hP a b _ hxs.1 hys.1 fun Γ' r hExt hr => hk Γ' (r, ()) hExt ⟨hr, trivial⟩
  | .float f, Γ, hP, (a, ()), (b, ()), _, hxs, hys, k, hk =>
    hF f hP a b _ hxs.1 hys.1 fun Γ' r hExt hr => hk Γ' (r, ()) hExt ⟨hr, trivial⟩
  | .pair t1 t2, Γ, hP, xs, ys, rawRhs, hxs, hys, k, hk => by
    obtain ⟨hP1, hP2⟩ := hP_pair t1 t2 hP
    simp only [legalBinTree]
    split
    · next hp =>
      have hxs' := ArgsNormal_packedToTup hp hxs
      have hys' := ArgsNormal_packedToTup hp hys
      have hscalar : (toTFlat (
          splitLegalToLeaves target (.pair t1 t2) xs fun fx =>
          splitLegalToLeaves target (.pair t1 t2) ys fun fy =>
          legalBinTree.goS target onBool onBits onFloat (.pair t1 t2) fx fy fun fres =>
            packLeavesToLegal target (.pair t1 t2) fres k) Γ.length Δ.length).isLegal target Γ Δ =
              true := by
        refine splitLegalToLeaves_isLegal target (.pair t1 t2) xs hxs fun Γ1 fx hExt1 hfx => ?_
        refine splitLegalToLeaves_isLegal target (.pair t1 t2) ys (hys.mono hExt1) fun Γ2 fy hExt2
          hfy => ?_
        have h12 := hExt1.trans hExt2
        have hgoS : ∀ (u : Ty) {Γ' : List (Ty × VarKind)}, P u →
            (fxu fyu : Tup (Arg K) (target.leafTys u)) →
            ArgsNormal target Γ' fxu → ArgsNormal target Γ' fyu →
            ∀ {cont : Tup (Arg K) (target.leafTys u) → Expr K KL rs},
            IsLegalCont target Γ' Δ (fun Γ'' res => ArgsNormal target Γ'' res) cont →
            (toTFlat (legalBinTree.goS target onBool onBits onFloat u fxu fyu cont) Γ'.length
              Δ.length).isLegal target Γ' Δ = true := by
          intro u
          induction u with
          | bool =>
            intro Γ' hPu (a, ()) (b, ()) ha hb cont hcont
            exact hB hPu a b _ ha.1 hb.1 fun Γ'' r hExt hr => hcont Γ'' (r, ()) hExt ⟨hr, trivial⟩
          | bits n =>
            intro Γ' hPu (a, ()) (b, ()) ha hb cont hcont
            exact hBi n hPu a b _ ha.1 hb.1 fun Γ'' r hExt hr =>
              hcont Γ'' (r, ()) hExt ⟨hr, trivial⟩
          | float f =>
            intro Γ' hPu (a, ()) (b, ()) ha hb cont hcont
            exact hF f hPu a b _ ha.1 hb.1 fun Γ'' r hExt hr =>
              hcont Γ'' (r, ()) hExt ⟨hr, trivial⟩
          | pair u1 u2 ih1 ih2 =>
            intro Γ' hPu fxu fyu hfxu hfyu cont hcont
            obtain ⟨hPu1, hPu2⟩ := hP_pair u1 u2 hPu
            obtain ⟨hx1, hx2⟩ := ArgsNormal_tupSplit hfxu
            obtain ⟨hy1, hy2⟩ := ArgsNormal_tupSplit hfyu
            refine ih1 hPu1 _ _ hx1 hy1 fun Γa r1 hExta hr1 => ?_
            exact ih2 hPu2 _ _ (hx2.mono hExta) (hy2.mono hExta) fun Γb r2 hExtb hr2 =>
              hcont Γb (tupAppend r1 r2) (hExta.trans hExtb)
                (ArgsNormal_tupAppend (hr1.mono hExtb) hr2)
        refine hgoS (.pair t1 t2) hP fx fy (hfx.mono hExt2) hfy fun Γ3 fres hExt3 hfres => ?_
        exact packLeavesToLegal_isLegal target (.pair t1 t2) fres hfres
          fun Γ4 res hExt4 hres => hk Γ4 res ((h12.trans hExt3).trans hExt4) hres
      by_cases hvs :
        vecSupported (.pair t1 t2)
        (checkUniformImmShift (.pair t1 t2) (mkCode (.pair t1 t2)) (packedToTup hp ys).1) = true
      · simp only [hvs, ↓reduceIte]
        have hunif : isUniformImmShift (mkCode (.pair t1 t2))
            (idxArg Γ.length (packedToTup hp xs).1, idxArg Γ.length (packedToTup hp ys).1, ()) =
            checkUniformImmShift (.pair t1 t2) (mkCode (.pair t1 t2)) (packedToTup hp ys).1 :=
          isUniformImmShift_idxArgs_eq (.pair t1 t2) (mkCode (.pair t1 t2)) Γ.length _ _
        have hcode : target.isLegalOp (mkCode (.pair t1 t2))
            (isUniformImmShift (mkCode (.pair t1 t2))
              (idxArg Γ.length (packedToTup hp xs).1, idxArg Γ.length (packedToTup hp ys).1, ())) =
              true := by
          rw [hunif]; exact hvecOp t1 t2 _ hP hp hvs
        refine isLegal_let_op2_normal target (mkCode (.pair t1 t2)) (packedToTup hp xs).1
          (packedToTup hp ys).1 _
          (hmkNe _) hcode hxs'.1 hys'.1 hp ?_
        exact hk _ (tupToPacked hp (.var Γ.length, ())) (CtxExtends.cons _ _)
          (ArgsNormal_tupToPacked hp ⟨ArgNormal.head target Γ hp, trivial⟩)
      · have hvsf :
          vecSupported (.pair t1 t2)
          (checkUniformImmShift (.pair t1 t2) (mkCode (.pair t1 t2)) (packedToTup hp ys).1) =
          false :=
          Bool.eq_false_iff.mpr hvs
        simp only [hvsf, Bool.false_eq_true, ↓reduceIte]
        cases opShiftKind (mkCode (.pair t1 t2)) with
        | none => dsimp only; exact hscalar
        | some b =>
          cases hrr : rawRhs with
          | none => cases b <;> (dsimp only; exact hscalar)
          | some r =>
            cases r with
            | var _ => cases b <;> (dsimp only; exact hscalar)
            | imm c =>
              cases b with
              | true =>
                dsimp only
                cases hus : uniformShiftLeaf? (.pair t1 t2) c with
                | none => dsimp only; exact hscalar
                | some p =>
                  rcases p with ⟨w, s⟩
                  dsimp only
                  by_cases hs0 : (s == 0) = true
                  · simp only [hs0, ↓reduceIte]
                    exact hk Γ (tupToPacked hp (packedToTup hp xs)) (CtxExtends.refl Γ)
                      (ArgsNormal_tupToPacked hp hxs')
                  · have hs0f : (s == 0) = false := Bool.eq_false_iff.mpr hs0
                    simp only [hs0f, Bool.false_eq_true, ↓reduceIte]
                    by_cases hsup :
                      target.vecIntOpSupported (.rotr (.pair t1 t2)) (.pair t1 t2) true = true
                    · simp only [hsup, ↓reduceIte]
                      have husR :=
                        uniformShiftLeaf?_splatBits (.pair t1 t2) c (BitVec.ofNat w (w - s)) hus
                      have hunifR : isUniformImmShift (.rotr (.pair t1 t2))
                          (idxArg Γ.length (packedToTup hp xs).1,
                            idxArg Γ.length
                            (.imm (splatBits w (BitVec.ofNat w (w - s)) (.pair t1 t2))),
                            ()) = true := by
                        simp [idxArg, isUniformImmShift, husR]
                      refine isLegal_let_op2_normal target (.rotr (.pair t1 t2))
                        (packedToTup hp xs).1 (.imm _) _ rfl
                        (by rw [hunifR]; simp [LegalTarget.isLegalOp, hp, hsup]) hxs'.1 hp hp ?_
                      exact hk _ (tupToPacked hp (.var Γ.length, ())) (CtxExtends.cons _ _)
                        (ArgsNormal_tupToPacked hp ⟨ArgNormal.head target Γ hp, trivial⟩)
                    · have hsupf :
                        target.vecIntOpSupported (.rotr (.pair t1 t2)) (.pair t1 t2) true = false :=
                        Bool.eq_false_iff.mpr hsup
                      simp only [hsupf, Bool.false_eq_true, ↓reduceIte]
                      exact hscalar
              | false =>
                dsimp only
                cases hus : uniformShiftLeaf? (.pair t1 t2) c with
                | none => dsimp only; exact hscalar
                | some p =>
                  rcases p with ⟨w, s⟩
                  dsimp only
                  by_cases hs0 : (s == 0) = true
                  · simp only [hs0, ↓reduceIte]
                    exact hk Γ (tupToPacked hp (packedToTup hp xs)) (CtxExtends.refl Γ)
                      (ArgsNormal_tupToPacked hp hxs')
                  · have hs0f : (s == 0) = false := Bool.eq_false_iff.mpr hs0
                    simp only [hs0f, Bool.false_eq_true, ↓reduceIte]
                    by_cases hsup :
                      (target.vecIntOpSupported (.rotr (.pair t1 t2)) (.pair t1 t2) true &&
                          target.vecIntOpSupported (.and (.pair t1 t2)) (.pair t1 t2) false) = true
                    · simp only [hsup, ↓reduceIte]
                      have hsup' := (Bool.and_eq_true _ _).mp hsup
                      have husR :=
                        uniformShiftLeaf?_splatBits (.pair t1 t2) c (BitVec.ofNat w (w - s)) hus
                      have hunifR : isUniformImmShift (.rotr (.pair t1 t2))
                          (idxArg Γ.length (packedToTup hp xs).1,
                            idxArg Γ.length
                            (.imm (splatBits w (BitVec.ofNat w (w - s)) (.pair t1 t2))),
                            ()) = true := by
                        simp [idxArg, isUniformImmShift, husR]
                      refine isLegal_let_op2_normal target (.rotr (.pair t1 t2))
                        (packedToTup hp xs).1 (.imm _) _ rfl
                        (by rw [hunifR]; simp [LegalTarget.isLegalOp, hp, hsup'.1]) hxs'.1 hp hp ?_
                      let Γ1 := (.pair t1 t2, VarKind.normal) :: Γ
                      refine isLegal_let_op2_normal target (.and (.pair t1 t2)) (.var Γ.length)
                        (.imm _) _ rfl
                        (by simp [LegalTarget.isLegalOp, isUniformImmShift, hp, hsup'.2])
                          (ArgNormal.head target Γ hp) hp hp ?_
                      let Γ2 := (.pair t1 t2, VarKind.normal) :: Γ1
                      exact hk Γ2 (tupToPacked hp (.var Γ1.length, ()))
                        ((CtxExtends.cons _ _).trans (CtxExtends.cons _ _))
                        (ArgsNormal_tupToPacked hp ⟨ArgNormal.head target Γ1 hp, trivial⟩)
                    · have hsupf :
                        (target.vecIntOpSupported (.rotr (.pair t1 t2)) (.pair t1 t2) true &&
                          target.vecIntOpSupported (.and (.pair t1 t2)) (.pair t1 t2) false) =
                            false := Bool.eq_false_iff.mpr hsup
                      simp only [hsupf, Bool.false_eq_true, ↓reduceIte]
                      exact hscalar
    · next hnp =>
      have hf := Bool.eq_false_iff.mpr hnp
      obtain ⟨hx1, hx2⟩ := ArgsNormal_tupSplit (ArgsNormal_splitToTup hf hxs)
      obtain ⟨hy1, hy2⟩ := ArgsNormal_tupSplit (ArgsNormal_splitToTup hf hys)
      refine legalBinTree_isLegal target P hP_pair mkCode vecSupported hmkNe hvecOp
        onBool onBits onFloat uniformImmRhs hB hBi hF t1 hP1 _ _ none hx1 hy1 fun Γ1 r1 hExt1 hr1 =>
          ?_
      refine legalBinTree_isLegal target P hP_pair mkCode vecSupported hmkNe hvecOp
        onBool onBits onFloat uniformImmRhs hB hBi hF t2 hP2 _ _ none (hx2.mono hExt1)
          (hy2.mono hExt1) fun Γ2 r2 hExt2 hr2 => ?_
      exact hk Γ2 (tupToSplit hf (tupAppend r1 r2)) (hExt1.trans hExt2)
        (ArgsNormal_tupToSplit hf (ArgsNormal_tupAppend (hr1.mono hExt2) hr2))

theorem legalCmpTree_isLegal (target : LegalTarget) {Δ : List (List Ty)} {rs : List Ty}
    (hv : target.valid = true) (o : CmpOp) :
    ∀ (t : Ty) {Γ : List (Ty × VarKind)}, target.supportsTy t = true →
      (xs ys : Tup (Arg K) (target.legalTys t)) → ArgsNormal target Γ xs → ArgsNormal target Γ ys →
      {k : Tup (Arg K) (target.legalTys t.mask) → Expr K KL rs} →
      IsLegalCont target Γ Δ (fun Γ' res => ArgsNormal target Γ' res) k →
      (toTFlat (legalCmpTree target o t xs ys k) Γ.length Δ.length).isLegal target Γ Δ = true := by
  intro t Γ hsupp xs ys hxs hys k hk
  have leafBool :
    ∀ {Γ' : List (Ty × VarKind)} (a b : Arg K .bool) {cont : Arg K .bool → Expr K KL rs},
      ArgNormal target Γ' .bool a → ArgNormal target Γ' .bool b →
      IsLegalCont target Γ' Δ (fun Γ'' r => ArgNormal target Γ'' .bool r) cont →
      (toTFlat (if target.boolCmp then .let_ (op2 (.cmp o .bool) a b) fun (r, ()) => cont (.var r)
        else emitBoolCmp o a b cont) Γ'.length Δ.length).isLegal target Γ' Δ = true := by
    intro Γ' a b cont ha hb hcont
    by_cases hbc : target.boolCmp = true
    · simp only [hbc, ↓reduceIte]
      refine isLegal_let_op2_normal target (.cmp o .bool) a b _ rfl
        (by simp [LegalTarget.isLegalOp, hbc]) ha hb rfl ?_
      exact hcont _ (.var Γ'.length) (CtxExtends.cons _ _) (ArgNormal.head target Γ' rfl)
    · have hbcf : target.boolCmp = false := Bool.eq_false_iff.mpr hbc
      simp only [hbcf, Bool.false_eq_true, ↓reduceIte]
      exact emitBoolCmp_isLegal target o a b ha hb hcont
  have leafBits : ∀ (n : Nat) {Γ' : List (Ty × VarKind)} (a b : Arg K (.bits (target.widenWidth n)))
      {cont : Arg K .bool → Expr K KL rs},
      target.supportsTy (.bits n) = true →
      ArgNormal target Γ' (.bits (target.widenWidth n)) a →
        ArgNormal target Γ' (.bits (target.widenWidth n)) b →
      IsLegalCont target Γ' Δ (fun Γ'' r => ArgNormal target Γ'' .bool r) cont →
      (toTFlat (let w := target.widenWidth n
        if n == 0 then cont (.imm (o.evalBits 0#0 0#0))
        else if n == w then .let_ (op2 (.cmp o (.bits w)) a b) fun (r, ()) => cont (.var r)
        else if (match o with | .slt | .sle | .sgt | .sge => true | _ => false) then
          emitSextToW n w a fun sa => emitSextToW n w b fun sb =>
            .let_ (op2 (.cmp o (.bits w)) sa sb) fun (r, ()) => cont (.var r)
        else .let_ (op2 (.cmp o (.bits w)) a b) fun (r, ()) =>
          cont (.var r)) Γ'.length Δ.length).isLegal target Γ' Δ = true := by
    intro n Γ' a b cont hsuppb ha hb hcont
    have hw := widenWidth_mem_of_supports hsuppb
    have hwpos : 0 < target.widenWidth n := (valid_bitWidth_spec hv hw).1
    dsimp only
    by_cases hn0 : (n == 0) = true
    · simp only [hn0, ↓reduceIte]; exact hcont Γ' (.imm _) (CtxExtends.refl Γ') rfl
    · simp only [hn0, Bool.false_eq_true, ↓reduceIte]
      by_cases hnw : (n == target.widenWidth n) = true
      · simp only [hnw, ↓reduceIte]
        refine isLegal_let_op2_normal target (.cmp o (.bits (target.widenWidth n))) a b _ rfl
          (by simp [LegalTarget.isLegalOp, hw, hwpos]) ha hb rfl ?_
        exact hcont _ (.var Γ'.length) (CtxExtends.cons _ _) (ArgNormal.head target Γ' rfl)
      · simp only [hnw, Bool.false_eq_true, ↓reduceIte]
        have huns :
          (toTFlat
          (.let_ (op2 (.cmp o (.bits (target.widenWidth n))) a b) fun (r, ()) => cont (.var r))
            Γ'.length Δ.length).isLegal target Γ' Δ = true := by
          refine isLegal_let_op2_normal target (.cmp o (.bits (target.widenWidth n))) a b _ rfl
            (by simp [LegalTarget.isLegalOp, hw, hwpos]) ha hb rfl ?_
          exact hcont _ (.var Γ'.length) (CtxExtends.cons _ _) (ArgNormal.head target Γ' rfl)
        have hsgn : (toTFlat (emitSextToW n (target.widenWidth n) a fun sa =>
            emitSextToW n (target.widenWidth n) b fun sb =>
            .let_ (op2 (.cmp o (.bits (target.widenWidth n))) sa sb) fun (r, ()) => cont (.var r))
            Γ'.length Δ.length).isLegal target Γ' Δ = true := by
          refine emitSextToW_isLegal target hw a ha fun Γ1 sa hExt1 hsa => ?_
          refine emitSextToW_isLegal target hw b (hb.mono hExt1) fun Γ2 sb hExt2 hsb => ?_
          refine isLegal_let_op2_normal target (.cmp o (.bits (target.widenWidth n))) sa sb _ rfl
            (by simp [LegalTarget.isLegalOp, hw, hwpos]) (hsa.mono hExt2) hsb rfl ?_
          exact hcont _ (.var Γ2.length) ((hExt1.trans hExt2).trans (CtxExtends.cons _ _))
            (ArgNormal.head target Γ2 rfl)
        cases o <;> simp only [↓reduceIte, Bool.false_eq_true]
        · exact huns
        · exact huns
        · exact huns
        · exact huns
        · exact huns
        · exact huns
        · exact hsgn
        · exact hsgn
        · exact hsgn
        · exact hsgn
  cases t with
  | bool =>
    rcases xs with ⟨a, ⟨⟩⟩; rcases ys with ⟨b, ⟨⟩⟩
    simp only [legalCmpTree]
    exact leafBool a b hxs.1 hys.1 fun Γ' r hExt hr => hk Γ' (r, ()) hExt ⟨hr, trivial⟩
  | bits n =>
    rcases xs with ⟨a, ⟨⟩⟩; rcases ys with ⟨b, ⟨⟩⟩
    simp only [legalCmpTree]
    exact leafBits n a b hsupp hxs.1 hys.1 fun Γ' r hExt hr => hk Γ' (r, ()) hExt ⟨hr, trivial⟩
  | float _ => simp [legalCmpTree, toTFlat_hlt]
  | pair t1 t2 =>
    simp only [legalCmpTree]
    refine splitLegalToLeaves_isLegal target (.pair t1 t2) xs hxs fun Γ1 fx hExt1 hfx => ?_
    refine splitLegalToLeaves_isLegal target (.pair t1 t2) ys (hys.mono hExt1) fun Γ2 fy hExt2
      hfy => ?_
    have h12 := hExt1.trans hExt2
    have hgoMask : ∀ (u : Ty) {Γ' : List (Ty × VarKind)}, target.supportsTy u = true →
        (fxu fyu : Tup (Arg K) (target.leafTys u)) → ArgsNormal target Γ' fxu →
          ArgsNormal target Γ' fyu →
        ∀ {cont : Tup (Arg K) (target.leafTys u.mask) → Expr K KL rs},
        IsLegalCont target Γ' Δ (fun Γ'' res => ArgsNormal target Γ'' res) cont →
        (toTFlat (legalCmpTree.goMask target o u fxu fyu cont) Γ'.length Δ.length).isLegal target Γ'
          Δ = true := by
      intro u
      induction u with
      | bool =>
        intro Γ' _ (a, ()) (b, ()) ha hb cont hcont
        exact leafBool a b ha.1 hb.1 fun Γ'' r hExt hr => hcont Γ'' (r, ()) hExt ⟨hr, trivial⟩
      | bits n =>
        intro Γ' hPu (a, ()) (b, ()) ha hb cont hcont
        exact leafBits n a b hPu ha.1 hb.1 fun Γ'' r hExt hr => hcont Γ'' (r, ()) hExt ⟨hr, trivial⟩
      | float _ => intro _ _ _ _ _ _ _ _; simp [legalCmpTree.goMask, toTFlat_hlt]
      | pair u1 u2 ih1 ih2 =>
        intro Γ' hPu fxu fyu hfxu hfyu cont hcont
        simp only [LegalTarget.supportsTy, Bool.and_eq_true] at hPu
        obtain ⟨hx1, hx2⟩ := ArgsNormal_tupSplit hfxu
        obtain ⟨hy1, hy2⟩ := ArgsNormal_tupSplit hfyu
        refine ih1 hPu.1 _ _ hx1 hy1 fun Γa m1 hExta hm1 => ?_
        exact ih2 hPu.2 _ _ (hx2.mono hExta) (hy2.mono hExta) fun Γb m2 hExtb hm2 =>
          hcont Γb (tupAppend m1 m2) (hExta.trans hExtb) (ArgsNormal_tupAppend (hm1.mono hExtb) hm2)
    refine hgoMask (.pair t1 t2) hsupp fx fy (hfx.mono hExt2) hfy fun Γ3 mres hExt3 hmres => ?_
    exact packLeavesToLegal_isLegal target (Ty.mask (.pair t1 t2)) mres hmres
      fun Γ4 res hExt4 hres => hk Γ4 res ((h12.trans hExt3).trans hExt4) hres

theorem legalFCmpTree_isLegal (target : LegalTarget) {Δ : List (List Ty)} {rs : List Ty}
    (o : FCmpOp) :
    ∀ (t : Ty) {Γ : List (Ty × VarKind)}, target.supportsTy t = true →
      (xs ys : Tup (Arg K) (target.legalTys t)) → ArgsNormal target Γ xs → ArgsNormal target Γ ys →
      {k : Tup (Arg K) (target.legalTys t.mask) → Expr K KL rs} →
      IsLegalCont target Γ Δ (fun Γ' res => ArgsNormal target Γ' res) k →
      (toTFlat (legalFCmpTree target o t xs ys k) Γ.length Δ.length).isLegal target Γ Δ = true := by
  intro t Γ hsupp xs ys hxs hys k hk
  cases t with
  | bool => simp [legalFCmpTree, toTFlat_hlt]
  | bits _ => simp [legalFCmpTree, toTFlat_hlt]
  | float f =>
    rcases xs with ⟨a, ⟨⟩⟩; rcases ys with ⟨b, ⟨⟩⟩
    have hf : f ∈ target.floatFmts :=
      (by simpa [LegalTarget.supportsTy] using hsupp : f ∈ target.floatFmts ∧ f.width ≤ 64).1
    simp only [legalFCmpTree]
    refine isLegal_let_op2_normal target (.fcmp o (.float f)) a b _ rfl
      (by simp [LegalTarget.isLegalOp, hf]) hxs.1 hys.1 rfl ?_
    exact hk _ (.var Γ.length, ()) (CtxExtends.cons _ _) ⟨ArgNormal.head target Γ rfl, trivial⟩
  | pair t1 t2 =>
    simp only [legalFCmpTree]
    refine splitLegalToLeaves_isLegal target (.pair t1 t2) xs hxs fun Γ1 fx hExt1 hfx => ?_
    refine splitLegalToLeaves_isLegal target (.pair t1 t2) ys (hys.mono hExt1) fun Γ2 fy hExt2
      hfy => ?_
    have h12 := hExt1.trans hExt2
    have hgoFCmp : ∀ (u : Ty) {Γ' : List (Ty × VarKind)}, target.supportsTy u = true →
        (fxu fyu : Tup (Arg K) (target.leafTys u)) → ArgsNormal target Γ' fxu →
          ArgsNormal target Γ' fyu →
        ∀ {cont : Tup (Arg K) (target.leafTys u.mask) → Expr K KL rs},
        IsLegalCont target Γ' Δ (fun Γ'' res => ArgsNormal target Γ'' res) cont →
        (toTFlat (legalFCmpTree.goFCmp target o u fxu fyu cont) Γ'.length Δ.length).isLegal target
          Γ' Δ = true := by
      intro u
      induction u with
      | bool => intro _ _ _ _ _ _ _ _; simp [legalFCmpTree.goFCmp, toTFlat_hlt]
      | bits _ => intro _ _ _ _ _ _ _ _; simp [legalFCmpTree.goFCmp, toTFlat_hlt]
      | float f =>
        intro Γ' hPu (a, ()) (b, ()) ha hb cont hcont
        have hfp : f ∈ target.floatFmts :=
          (by simpa [LegalTarget.supportsTy] using hPu : f ∈ target.floatFmts ∧ f.width ≤ 64).1
        simp only [legalFCmpTree.goFCmp]
        refine isLegal_let_op2_normal target (.fcmp o (.float f)) a b _ rfl
          (by simp [LegalTarget.isLegalOp, hfp]) ha.1 hb.1 rfl ?_
        exact hcont _ (.var Γ'.length, ()) (CtxExtends.cons _ _)
          ⟨ArgNormal.head target Γ' rfl, trivial⟩
      | pair u1 u2 ih1 ih2 =>
        intro Γ' hPu fxu fyu hfxu hfyu cont hcont
        simp only [LegalTarget.supportsTy, Bool.and_eq_true] at hPu
        obtain ⟨hx1, hx2⟩ := ArgsNormal_tupSplit hfxu
        obtain ⟨hy1, hy2⟩ := ArgsNormal_tupSplit hfyu
        refine ih1 hPu.1 _ _ hx1 hy1 fun Γa m1 hExta hm1 => ?_
        exact ih2 hPu.2 _ _ (hx2.mono hExta) (hy2.mono hExta) fun Γb m2 hExtb hm2 =>
          hcont Γb (tupAppend m1 m2) (hExta.trans hExtb) (ArgsNormal_tupAppend (hm1.mono hExtb) hm2)
    refine hgoFCmp (.pair t1 t2) hsupp fx fy (hfx.mono hExt2) hfy fun Γ3 mres hExt3 hmres => ?_
    exact packLeavesToLegal_isLegal target (Ty.mask (.pair t1 t2)) mres hmres
      fun Γ4 res hExt4 hres => hk Γ4 res ((h12.trans hExt3).trans hExt4) hres

theorem legalSelectTree_isLegal (target : LegalTarget) {Δ : List (List Ty)} {rs : List Ty}
    {Γ : List (Ty × VarKind)} (c : Arg K .bool) (hc : ArgNormal target Γ .bool c) :
    ∀ (t : Ty), target.supportsTy t = true →
      (xs ys : Tup (Arg K) (target.legalTys t)) → ArgsNormal target Γ xs → ArgsNormal target Γ ys →
      {k : Tup (Arg K) (target.legalTys t) → Expr K KL rs} →
      IsLegalCont target Γ Δ (fun Γ' res => ArgsNormal target Γ' res) k →
      (toTFlat (legalSelectTree target c t xs ys k) Γ.length Δ.length).isLegal target Γ Δ = true :=
        by
  intro t hsupp xs ys hxs hys k hk
  have leafBool :
    ∀ {Γ' : List (Ty × VarKind)} (c' a b : Arg K .bool) {cont : Arg K .bool → Expr K KL rs},
      ArgNormal target Γ' .bool c' → ArgNormal target Γ' .bool a → ArgNormal target Γ' .bool b →
      IsLegalCont target Γ' Δ (fun Γ'' r => ArgNormal target Γ'' .bool r) cont →
      (toTFlat
        (if target.boolSelect then .let_ (op3 (.select .bool) c' a b) fun (r, ()) => cont (.var r)
        else emitBoolSelect c' a b cont) Γ'.length Δ.length).isLegal target Γ' Δ = true := by
    intro Γ' c' a b cont hc' ha hb hcont
    by_cases hbs : target.boolSelect = true
    · simp only [hbs, ↓reduceIte]
      refine isLegal_let_op3_normal target (.select .bool) c' a b _ rfl
        (by simp [LegalTarget.isLegalOp, hbs]) hc' ha hb rfl ?_
      exact hcont _ (.var Γ'.length) (CtxExtends.cons _ _) (ArgNormal.head target Γ' rfl)
    · have hbsf : target.boolSelect = false := Bool.eq_false_iff.mpr hbs
      simp only [hbsf, Bool.false_eq_true, ↓reduceIte]
      exact emitBoolSelect_isLegal target c' a b hc' ha hb hcont
  cases t with
  | bool =>
    rcases xs with ⟨a, ⟨⟩⟩; rcases ys with ⟨b, ⟨⟩⟩
    simp only [legalSelectTree]
    exact leafBool c a b hc hxs.1 hys.1 fun Γ' r hExt hr => hk Γ' (r, ()) hExt ⟨hr, trivial⟩
  | bits n =>
    rcases xs with ⟨a, ⟨⟩⟩; rcases ys with ⟨b, ⟨⟩⟩
    have hw := widenWidth_mem_of_supports hsupp
    have hlegW : target.isLegalTy (.bits (target.widenWidth n)) = true := by
      simpa [LegalTarget.isLegalTy] using hw
    simp only [legalSelectTree]
    refine isLegal_let_op3_normal target (.select (.bits (target.widenWidth n))) c a b _ rfl
      (by simp [LegalTarget.isLegalOp, hw]) hc hxs.1 hys.1 hlegW ?_
    exact hk _ (.var Γ.length, ()) (CtxExtends.cons _ _) ⟨ArgNormal.head target Γ hlegW, trivial⟩
  | float f =>
    rcases xs with ⟨a, ⟨⟩⟩; rcases ys with ⟨b, ⟨⟩⟩
    have hf : f ∈ target.floatFmts :=
      (by simpa [LegalTarget.supportsTy] using hsupp : f ∈ target.floatFmts ∧ f.width ≤ 64).1
    have hlegF : target.isLegalTy (.float f) = true := by simpa [LegalTarget.isLegalTy] using hf
    simp only [legalSelectTree]
    refine isLegal_let_op3_normal target (.select (.float f)) c a b _ rfl
      (by simp [LegalTarget.isLegalOp, hf]) hc hxs.1 hys.1 hlegF ?_
    exact hk _ (.var Γ.length, ()) (CtxExtends.cons _ _) ⟨ArgNormal.head target Γ hlegF, trivial⟩
  | pair t1 t2 =>
    simp only [legalSelectTree]
    refine splitLegalToLeaves_isLegal target (.pair t1 t2) xs hxs fun Γ1 fx hExt1 hfx => ?_
    refine splitLegalToLeaves_isLegal target (.pair t1 t2) ys (hys.mono hExt1) fun Γ2 fy hExt2
      hfy => ?_
    have h12 := hExt1.trans hExt2
    have hgoSel : ∀ (u : Ty) {Γ' : List (Ty × VarKind)}, target.supportsTy u = true →
        CtxExtends Γ Γ' →
        (fxu fyu : Tup (Arg K) (target.leafTys u)) → ArgsNormal target Γ' fxu →
          ArgsNormal target Γ' fyu →
        ∀ {cont : Tup (Arg K) (target.leafTys u) → Expr K KL rs},
        IsLegalCont target Γ' Δ (fun Γ'' res => ArgsNormal target Γ'' res) cont →
        (toTFlat (legalSelectTree.goSel target c u fxu fyu cont) Γ'.length Δ.length).isLegal target
          Γ' Δ = true := by
      intro u
      induction u with
      | bool =>
        intro Γ' _ hExt' (a, ()) (b, ()) ha hb cont hcont
        exact leafBool c a b (hc.mono hExt') ha.1 hb.1 fun Γ'' r hExt hr =>
          hcont Γ'' (r, ()) hExt ⟨hr, trivial⟩
      | bits n =>
        intro Γ' hPu hExt' (a, ()) (b, ()) ha hb cont hcont
        have hw := widenWidth_mem_of_supports hPu
        have hlegW : target.isLegalTy (.bits (target.widenWidth n)) = true := by
          simpa [LegalTarget.isLegalTy] using hw
        simp only [legalSelectTree.goSel]
        refine isLegal_let_op3_normal target (.select (.bits (target.widenWidth n))) c a b _ rfl
          (by simp [LegalTarget.isLegalOp, hw]) (hc.mono hExt') ha.1 hb.1 hlegW ?_
        exact hcont _ (.var Γ'.length, ()) (CtxExtends.cons _ _)
          ⟨ArgNormal.head target Γ' hlegW, trivial⟩
      | float f =>
        intro Γ' hPu hExt' (a, ()) (b, ()) ha hb cont hcont
        have hf : f ∈ target.floatFmts :=
          (by simpa [LegalTarget.supportsTy] using hPu : f ∈ target.floatFmts ∧ f.width ≤ 64).1
        have hlegF : target.isLegalTy (.float f) = true := by simpa [LegalTarget.isLegalTy] using hf
        simp only [legalSelectTree.goSel]
        refine isLegal_let_op3_normal target (.select (.float f)) c a b _ rfl
          (by simp [LegalTarget.isLegalOp, hf]) (hc.mono hExt') ha.1 hb.1 hlegF ?_
        exact hcont _ (.var Γ'.length, ()) (CtxExtends.cons _ _)
          ⟨ArgNormal.head target Γ' hlegF, trivial⟩
      | pair u1 u2 ih1 ih2 =>
        intro Γ' hPu hExt' fxu fyu hfxu hfyu cont hcont
        simp only [LegalTarget.supportsTy, Bool.and_eq_true] at hPu
        obtain ⟨hx1, hx2⟩ := ArgsNormal_tupSplit hfxu
        obtain ⟨hy1, hy2⟩ := ArgsNormal_tupSplit hfyu
        refine ih1 hPu.1 hExt' _ _ hx1 hy1 fun Γa r1 hExta hr1 => ?_
        exact ih2 hPu.2 (hExt'.trans hExta) _ _ (hx2.mono hExta) (hy2.mono hExta) fun Γb r2 hExtb
          hr2 =>
          hcont Γb (tupAppend r1 r2) (hExta.trans hExtb) (ArgsNormal_tupAppend (hr1.mono hExtb) hr2)
    refine hgoSel (.pair t1 t2) hsupp h12 fx fy (hfx.mono hExt2) hfy fun Γ3 fres hExt3 hfres => ?_
    exact packLeavesToLegal_isLegal target (.pair t1 t2) fres hfres
      fun Γ4 res hExt4 hres => hk Γ4 res ((h12.trans hExt3).trans hExt4) hres

theorem legalBlendTree_isLegal (target : LegalTarget) {Δ : List (List Ty)} {rs : List Ty} :
    ∀ (t : Ty) {Γ : List (Ty × VarKind)}, target.supportsTy t = true →
      (ms : Tup (Arg K) (target.legalTys t.mask)) → (xs ys : Tup (Arg K) (target.legalTys t)) →
      ArgsNormal target Γ ms → ArgsNormal target Γ xs → ArgsNormal target Γ ys →
      {k : Tup (Arg K) (target.legalTys t) → Expr K KL rs} →
      IsLegalCont target Γ Δ (fun Γ' res => ArgsNormal target Γ' res) k →
      (toTFlat (legalBlendTree target t ms xs ys k) Γ.length Δ.length).isLegal target Γ Δ = true :=
        by
  intro t Γ hsupp ms xs ys hms hxs hys k hk
  have leafBool :
    ∀ {Γ' : List (Ty × VarKind)} (c' a b : Arg K .bool) {cont : Arg K .bool → Expr K KL rs},
      ArgNormal target Γ' .bool c' → ArgNormal target Γ' .bool a → ArgNormal target Γ' .bool b →
      IsLegalCont target Γ' Δ (fun Γ'' r => ArgNormal target Γ'' .bool r) cont →
      (toTFlat
        (if target.boolSelect then .let_ (op3 (.select .bool) c' a b) fun (r, ()) => cont (.var r)
        else emitBoolSelect c' a b cont) Γ'.length Δ.length).isLegal target Γ' Δ = true := by
    intro Γ' c' a b cont hc' ha hb hcont
    by_cases hbs : target.boolSelect = true
    · simp only [hbs, ↓reduceIte]
      refine isLegal_let_op3_normal target (.select .bool) c' a b _ rfl
        (by simp [LegalTarget.isLegalOp, hbs]) hc' ha hb rfl ?_
      exact hcont _ (.var Γ'.length) (CtxExtends.cons _ _) (ArgNormal.head target Γ' rfl)
    · have hbsf : target.boolSelect = false := Bool.eq_false_iff.mpr hbs
      simp only [hbsf, Bool.false_eq_true, ↓reduceIte]
      exact emitBoolSelect_isLegal target c' a b hc' ha hb hcont
  cases t with
  | bool =>
    rcases ms with ⟨c, ⟨⟩⟩; rcases xs with ⟨a, ⟨⟩⟩; rcases ys with ⟨b, ⟨⟩⟩
    simp only [legalBlendTree]
    exact leafBool c a b hms.1 hxs.1 hys.1 fun Γ' r hExt hr => hk Γ' (r, ()) hExt ⟨hr, trivial⟩
  | bits n =>
    rcases ms with ⟨c, ⟨⟩⟩; rcases xs with ⟨a, ⟨⟩⟩; rcases ys with ⟨b, ⟨⟩⟩
    have hw := widenWidth_mem_of_supports hsupp
    have hlegW : target.isLegalTy (.bits (target.widenWidth n)) = true := by
      simpa [LegalTarget.isLegalTy] using hw
    simp only [legalBlendTree]
    refine isLegal_let_op3_normal target (.select (.bits (target.widenWidth n))) c a b _ rfl
      (by simp [LegalTarget.isLegalOp, hw]) hms.1 hxs.1 hys.1 hlegW ?_
    exact hk _ (.var Γ.length, ()) (CtxExtends.cons _ _) ⟨ArgNormal.head target Γ hlegW, trivial⟩
  | float f =>
    rcases ms with ⟨c, ⟨⟩⟩; rcases xs with ⟨a, ⟨⟩⟩; rcases ys with ⟨b, ⟨⟩⟩
    have hf : f ∈ target.floatFmts :=
      (by simpa [LegalTarget.supportsTy] using hsupp : f ∈ target.floatFmts ∧ f.width ≤ 64).1
    have hlegF : target.isLegalTy (.float f) = true := by simpa [LegalTarget.isLegalTy] using hf
    simp only [legalBlendTree]
    refine isLegal_let_op3_normal target (.select (.float f)) c a b _ rfl
      (by simp [LegalTarget.isLegalOp, hf]) hms.1 hxs.1 hys.1 hlegF ?_
    exact hk _ (.var Γ.length, ()) (CtxExtends.cons _ _) ⟨ArgNormal.head target Γ hlegF, trivial⟩
  | pair t1 t2 =>
    simp only [legalBlendTree]
    refine splitLegalToLeaves_isLegal target (Ty.mask (.pair t1 t2)) ms hms fun Γ1 fm hExt1 hfm =>
      ?_
    refine splitLegalToLeaves_isLegal target (.pair t1 t2) xs (hxs.mono hExt1) fun Γ2 fx hExt2
      hfx => ?_
    have h12 := hExt1.trans hExt2
    refine splitLegalToLeaves_isLegal target (.pair t1 t2) ys (hys.mono h12) fun Γ3 fy hExt3 hfy =>
      ?_
    have h13 := h12.trans hExt3
    have hgoBlend : ∀ (u : Ty) {Γ' : List (Ty × VarKind)}, target.supportsTy u = true →
        (fmu : Tup (Arg K) (target.leafTys u.mask)) → (fxu fyu : Tup (Arg K) (target.leafTys u)) →
        ArgsNormal target Γ' fmu → ArgsNormal target Γ' fxu → ArgsNormal target Γ' fyu →
        ∀ {cont : Tup (Arg K) (target.leafTys u) → Expr K KL rs},
        IsLegalCont target Γ' Δ (fun Γ'' res => ArgsNormal target Γ'' res) cont →
        (toTFlat (legalBlendTree.goBlend target u fmu fxu fyu cont) Γ'.length Δ.length).isLegal
          target Γ' Δ = true := by
      intro u
      induction u with
      | bool =>
        intro Γ' _ (c, ()) (a, ()) (b, ()) hc ha hb cont hcont
        exact leafBool c a b hc.1 ha.1 hb.1 fun Γ'' r hExt hr =>
          hcont Γ'' (r, ()) hExt ⟨hr, trivial⟩
      | bits n =>
        intro Γ' hPu (c, ()) (a, ()) (b, ()) hc ha hb cont hcont
        have hw := widenWidth_mem_of_supports hPu
        have hlegW : target.isLegalTy (.bits (target.widenWidth n)) = true := by
          simpa [LegalTarget.isLegalTy] using hw
        simp only [legalBlendTree.goBlend]
        refine isLegal_let_op3_normal target (.select (.bits (target.widenWidth n))) c a b _ rfl
          (by simp [LegalTarget.isLegalOp, hw]) hc.1 ha.1 hb.1 hlegW ?_
        exact hcont _ (.var Γ'.length, ()) (CtxExtends.cons _ _)
          ⟨ArgNormal.head target Γ' hlegW, trivial⟩
      | float f =>
        intro Γ' hPu (c, ()) (a, ()) (b, ()) hc ha hb cont hcont
        have hf : f ∈ target.floatFmts :=
          (by simpa [LegalTarget.supportsTy] using hPu : f ∈ target.floatFmts ∧ f.width ≤ 64).1
        have hlegF : target.isLegalTy (.float f) = true := by simpa [LegalTarget.isLegalTy] using hf
        simp only [legalBlendTree.goBlend]
        refine isLegal_let_op3_normal target (.select (.float f)) c a b _ rfl
          (by simp [LegalTarget.isLegalOp, hf]) hc.1 ha.1 hb.1 hlegF ?_
        exact hcont _ (.var Γ'.length, ()) (CtxExtends.cons _ _)
          ⟨ArgNormal.head target Γ' hlegF, trivial⟩
      | pair u1 u2 ih1 ih2 =>
        intro Γ' hPu fmu fxu fyu hfmu hfxu hfyu cont hcont
        simp only [LegalTarget.supportsTy, Bool.and_eq_true] at hPu
        obtain ⟨hm1, hm2⟩ := ArgsNormal_tupSplit hfmu
        obtain ⟨hx1, hx2⟩ := ArgsNormal_tupSplit hfxu
        obtain ⟨hy1, hy2⟩ := ArgsNormal_tupSplit hfyu
        refine ih1 hPu.1 _ _ _ hm1 hx1 hy1 fun Γa r1 hExta hr1 => ?_
        exact ih2 hPu.2 _ _ _ (hm2.mono hExta) (hx2.mono hExta) (hy2.mono hExta) fun Γb r2 hExtb
          hr2 =>
          hcont Γb (tupAppend r1 r2) (hExta.trans hExtb) (ArgsNormal_tupAppend (hr1.mono hExtb) hr2)
    refine hgoBlend (.pair t1 t2) hsupp fm fx fy
      (hfm.mono (hExt2.trans hExt3)) (hfx.mono hExt3) hfy fun Γ4 fres hExt4 hfres => ?_
    exact packLeavesToLegal_isLegal target (.pair t1 t2) fres hfres
      fun Γ5 res hExt5 hres => hk Γ5 res ((h13.trans hExt4).trans hExt5) hres

theorem legalShufd_isLegal (target : LegalTarget) {Δ : List (List Ty)} {rs : List Ty}
    (hv : target.valid = true) (h32 : 32 ∈ target.bitWidths) (imm : BitVec 8) :
    ∀ (t : Ty) {Γ : List (Ty × VarKind)}, target.supportsTy t = true →
      (xs : Tup (Arg K) (target.legalTys t)) → ArgsNormal target Γ xs →
      {k : Tup (Arg K) (target.legalTys t) → Expr K KL rs} →
      IsLegalCont target Γ Δ (fun Γ' res => ArgsNormal target Γ' res) k →
      (toTFlat (legalShufd target imm t xs k) Γ.length Δ.length).isLegal target Γ Δ = true
  | t, Γ, ht, xs, hxs, k, hk => by
    have h8 := valid_mem8 hv
    have hsc : ∀ {Γ' : List (Ty × VarKind)} (ys : Tup (Arg K) (target.legalTys t)),
        ArgsNormal target Γ' ys →
          IsLegalCont target Γ' Δ (fun Γ'' res => ArgsNormal target Γ'' res) k →
        (toTFlat (legalSimdScalar128 target (fun a0 a1 a2 a3 _ _ _ _ cont =>
          let (r0, r1, r2, r3) := scalarShufd128 imm a0 a1 a2 a3; cont r0 r1 r2 r3) t ys ys k)
            Γ'.length Δ.length).isLegal target Γ' Δ = true := by
      intro Γ' ys hys hk'
      refine legalSimdScalar128_isLegal target hv h32 _
        (fun {Γa} a0 a1 a2 a3 _ _ _ _ cont ha0 ha1 ha2 ha3 _ _ _ _ hcont => ?_)
        t ht ys ys hys hys hk'
      have ⟨hr0, hr1, hr2, hr3⟩ := ArgNormal_scalarShufd128 target imm a0 a1 a2 a3 ha0 ha1 ha2 ha3
      exact hcont Γa _ _ _ _ (CtxExtends.refl Γa) hr0 hr1 hr2 hr3
    rw [legalShufd.eq_def]
    by_cases hsz : (t.size == 0 || t.size % 128 != 0) = true
    · simp [hsz, toTFlat_hlt]
    · have hszf : (t.size == 0 || t.size % 128 != 0) = false := Bool.eq_false_iff.mpr hsz
      simp only [hszf, Bool.false_eq_true, ↓reduceIte]
      have ⟨hsz0, hmod⟩ : (t.size != 0) = true ∧ (t.size % 128 == 0) = true := by
        simpa [Bool.or_eq_false_iff, Bool.not_eq_true', bne_iff_ne] using hszf
      cases t with
      | bool => exact hsc xs hxs hk
      | bits _ => exact hsc xs hxs hk
      | float _ => exact hsc xs hxs hk
      | pair a b =>
        dsimp only
        split
        · next hp =>
          by_cases hsup : target.vecIntOpSupported (.shufd (.pair a b) imm) (.pair a b) false = true
          · simp only [hsup, ↓reduceIte]
            have hxs' := ArgsNormal_packedToTup hp hxs
            refine isLegal_let_op1_normal target (.shufd (.pair a b) imm) (packedToTup hp xs).1 _
              rfl
              (by simp [LegalTarget.isLegalOp, hp, hsz0, hmod, hsup]) hxs'.1 hp ?_
            exact hk _ (tupToPacked hp (.var Γ.length, ())) (CtxExtends.cons _ _)
              (ArgsNormal_tupToPacked hp ⟨ArgNormal.head target Γ hp, trivial⟩)
          · have hsupf :
              target.vecIntOpSupported (.shufd (.pair a b) imm) (.pair a b) false = false :=
              Bool.eq_false_iff.mpr hsup
            simp only [hsupf, Bool.false_eq_true, ↓reduceIte]
            exact hsc xs hxs hk
        · next hnp =>
          have hf := Bool.eq_false_iff.mpr hnp
          by_cases hab :
            (a.size != 0 && a.size % 128 == 0 && b.size != 0 && b.size % 128 == 0) = true
          · simp only [hab, ↓reduceIte]
            simp only [LegalTarget.supportsTy, Bool.and_eq_true] at ht
            obtain ⟨xa, xb⟩ := ArgsNormal_tupSplit (ArgsNormal_splitToTup hf hxs)
            refine legalShufd_isLegal target hv h32 imm a ht.1 _ xa fun Γ1 ra hExt1 hra => ?_
            refine legalShufd_isLegal target hv h32 imm b ht.2 _ (xb.mono hExt1) fun Γ2 rb hExt2
              hrb => ?_
            exact hk Γ2 (tupToSplit hf (tupAppend ra rb)) (hExt1.trans hExt2)
              (ArgsNormal_tupToSplit hf (ArgsNormal_tupAppend (hra.mono hExt2) hrb))
          · have habf :
              (a.size != 0 && a.size % 128 == 0 && b.size != 0 && b.size % 128 == 0) = false :=
              Bool.eq_false_iff.mpr hab
            simp only [habf, Bool.false_eq_true, ↓reduceIte]
            exact hsc xs hxs hk

theorem legalBlendw_isLegal (target : LegalTarget) {Δ : List (List Ty)} {rs : List Ty}
    (hv : target.valid = true) (h32 : 32 ∈ target.bitWidths) (imm : BitVec 8) :
    ∀ (t : Ty) {Γ : List (Ty × VarKind)}, target.supportsTy t = true →
      (xs ys : Tup (Arg K) (target.legalTys t)) → ArgsNormal target Γ xs → ArgsNormal target Γ ys →
      {k : Tup (Arg K) (target.legalTys t) → Expr K KL rs} →
      IsLegalCont target Γ Δ (fun Γ' res => ArgsNormal target Γ' res) k →
      (toTFlat (legalBlendw target imm t xs ys k) Γ.length Δ.length).isLegal target Γ Δ = true
  | t, Γ, ht, xs, ys, hxs, hys, k, hk => by
    have hsc : ∀ {Γ' : List (Ty × VarKind)} (ys1 ys2 : Tup (Arg K) (target.legalTys t)),
        ArgsNormal target Γ' ys1 → ArgsNormal target Γ' ys2 →
        IsLegalCont target Γ' Δ (fun Γ'' res => ArgsNormal target Γ'' res) k →
        (toTFlat (legalSimdScalar128 target (scalarBlendw128 imm) t ys1 ys2 k)
            Γ'.length Δ.length).isLegal target Γ' Δ = true := by
      intro Γ' ys1 ys2 h1 h2 hk'
      refine legalSimdScalar128_isLegal target hv h32 _
        (fun {Γa} a0 a1 a2 a3 b0 b1 b2 b3 cont ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hcont => ?_)
        t ht ys1 ys2 h1 h2 hk'
      exact scalarBlendw128_isLegal target h32 imm a0 a1 a2 a3 b0 b1 b2 b3 ha0 ha1 ha2 ha3 hb0 hb1
        hb2 hb3 hcont
    rw [legalBlendw.eq_def]
    by_cases hsz : (t.size == 0 || t.size % 128 != 0) = true
    · simp [hsz, toTFlat_hlt]
    · have hszf : (t.size == 0 || t.size % 128 != 0) = false := Bool.eq_false_iff.mpr hsz
      simp only [hszf, Bool.false_eq_true, ↓reduceIte]
      have ⟨hsz0, hmod⟩ : (t.size != 0) = true ∧ (t.size % 128 == 0) = true := by
        simpa [Bool.or_eq_false_iff, Bool.not_eq_true', bne_iff_ne] using hszf
      cases t with
      | bool => exact hsc xs ys hxs hys hk
      | bits _ => exact hsc xs ys hxs hys hk
      | float _ => exact hsc xs ys hxs hys hk
      | pair a b =>
        dsimp only
        split
        · next hp =>
          by_cases hsup :
            target.vecIntOpSupported (.blendw (.pair a b) imm) (.pair a b) false = true
          · simp only [hsup, ↓reduceIte]
            have hxs' := ArgsNormal_packedToTup hp hxs
            have hys' := ArgsNormal_packedToTup hp hys
            refine isLegal_let_op2_normal target (.blendw (.pair a b) imm)
              (packedToTup hp xs).1 (packedToTup hp ys).1 _ rfl
              (by simp [LegalTarget.isLegalOp, hp, hsz0, hmod, hsup]) hxs'.1 hys'.1 hp ?_
            exact hk _ (tupToPacked hp (.var Γ.length, ())) (CtxExtends.cons _ _)
              (ArgsNormal_tupToPacked hp ⟨ArgNormal.head target Γ hp, trivial⟩)
          · have hsupf :
              target.vecIntOpSupported (.blendw (.pair a b) imm) (.pair a b) false = false :=
              Bool.eq_false_iff.mpr hsup
            simp only [hsupf, Bool.false_eq_true, ↓reduceIte]
            exact hsc xs ys hxs hys hk
        · next hnp =>
          have hf := Bool.eq_false_iff.mpr hnp
          by_cases hab :
            (a.size != 0 && a.size % 128 == 0 && b.size != 0 && b.size % 128 == 0) = true
          · simp only [hab, ↓reduceIte]
            simp only [LegalTarget.supportsTy, Bool.and_eq_true] at ht
            obtain ⟨xa, xb⟩ := ArgsNormal_tupSplit (ArgsNormal_splitToTup hf hxs)
            obtain ⟨ya, yb⟩ := ArgsNormal_tupSplit (ArgsNormal_splitToTup hf hys)
            refine legalBlendw_isLegal target hv h32 imm a ht.1 _ _ xa ya fun Γ1 ra hExt1 hra => ?_
            refine legalBlendw_isLegal target hv h32 imm b ht.2 _ _ (xb.mono hExt1) (yb.mono hExt1)
              fun Γ2 rb hExt2 hrb => ?_
            exact hk Γ2 (tupToSplit hf (tupAppend ra rb)) (hExt1.trans hExt2)
              (ArgsNormal_tupToSplit hf (ArgsNormal_tupAppend (hra.mono hExt2) hrb))
          · have habf :
              (a.size != 0 && a.size % 128 == 0 && b.size != 0 && b.size % 128 == 0) = false :=
              Bool.eq_false_iff.mpr hab
            simp only [habf, Bool.false_eq_true, ↓reduceIte]
            exact hsc xs ys hxs hys hk

theorem legalAlignr_isLegal (target : LegalTarget) {Δ : List (List Ty)} {rs : List Ty}
    (hv : target.valid = true) (h32 : 32 ∈ target.bitWidths) (imm : BitVec 8) :
    ∀ (t : Ty) {Γ : List (Ty × VarKind)}, target.supportsTy t = true →
      (xs ys : Tup (Arg K) (target.legalTys t)) → ArgsNormal target Γ xs → ArgsNormal target Γ ys →
      {k : Tup (Arg K) (target.legalTys t) → Expr K KL rs} →
      IsLegalCont target Γ Δ (fun Γ' res => ArgsNormal target Γ' res) k →
      (toTFlat (legalAlignr target imm t xs ys k) Γ.length Δ.length).isLegal target Γ Δ = true
  | t, Γ, ht, xs, ys, hxs, hys, k, hk => by
    have h8 := valid_mem8 hv
    have hsc : ∀ {Γ' : List (Ty × VarKind)} (ys1 ys2 : Tup (Arg K) (target.legalTys t)),
        ArgsNormal target Γ' ys1 → ArgsNormal target Γ' ys2 →
        IsLegalCont target Γ' Δ (fun Γ'' res => ArgsNormal target Γ'' res) k →
        (toTFlat (legalSimdScalar128 target (scalarAlignr128 imm) t ys1 ys2 k)
            Γ'.length Δ.length).isLegal target Γ' Δ = true := by
      intro Γ' ys1 ys2 h1 h2 hk'
      refine legalSimdScalar128_isLegal target hv h32 _
        (fun {Γa} a0 a1 a2 a3 b0 b1 b2 b3 cont ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hcont => ?_)
        t ht ys1 ys2 h1 h2 hk'
      exact scalarAlignr128_isLegal target h8 h32 imm a0 a1 a2 a3 b0 b1 b2 b3 ha0 ha1 ha2 ha3 hb0
        hb1 hb2 hb3 hcont
    rw [legalAlignr.eq_def]
    by_cases hsz : (t.size == 0 || t.size % 128 != 0) = true
    · simp [hsz, toTFlat_hlt]
    · have hszf : (t.size == 0 || t.size % 128 != 0) = false := Bool.eq_false_iff.mpr hsz
      simp only [hszf, Bool.false_eq_true, ↓reduceIte]
      have ⟨hsz0, hmod⟩ : (t.size != 0) = true ∧ (t.size % 128 == 0) = true := by
        simpa [Bool.or_eq_false_iff, Bool.not_eq_true', bne_iff_ne] using hszf
      cases t with
      | bool => exact hsc xs ys hxs hys hk
      | bits _ => exact hsc xs ys hxs hys hk
      | float _ => exact hsc xs ys hxs hys hk
      | pair a b =>
        dsimp only
        split
        · next hp =>
          by_cases hsup :
            target.vecIntOpSupported (.alignr (.pair a b) imm) (.pair a b) false = true
          · simp only [hsup, ↓reduceIte]
            have hxs' := ArgsNormal_packedToTup hp hxs
            have hys' := ArgsNormal_packedToTup hp hys
            refine isLegal_let_op2_normal target (.alignr (.pair a b) imm)
              (packedToTup hp xs).1 (packedToTup hp ys).1 _ rfl
              (by simp [LegalTarget.isLegalOp, hp, hsz0, hmod, hsup]) hxs'.1 hys'.1 hp ?_
            exact hk _ (tupToPacked hp (.var Γ.length, ())) (CtxExtends.cons _ _)
              (ArgsNormal_tupToPacked hp ⟨ArgNormal.head target Γ hp, trivial⟩)
          · have hsupf :
              target.vecIntOpSupported (.alignr (.pair a b) imm) (.pair a b) false = false :=
              Bool.eq_false_iff.mpr hsup
            simp only [hsupf, Bool.false_eq_true, ↓reduceIte]
            exact hsc xs ys hxs hys hk
        · next hnp =>
          have hf := Bool.eq_false_iff.mpr hnp
          by_cases hab :
            (a.size != 0 && a.size % 128 == 0 && b.size != 0 && b.size % 128 == 0) = true
          · simp only [hab, ↓reduceIte]
            simp only [LegalTarget.supportsTy, Bool.and_eq_true] at ht
            obtain ⟨xa, xb⟩ := ArgsNormal_tupSplit (ArgsNormal_splitToTup hf hxs)
            obtain ⟨ya, yb⟩ := ArgsNormal_tupSplit (ArgsNormal_splitToTup hf hys)
            refine legalAlignr_isLegal target hv h32 imm a ht.1 _ _ xa ya fun Γ1 ra hExt1 hra => ?_
            refine legalAlignr_isLegal target hv h32 imm b ht.2 _ _ (xb.mono hExt1) (yb.mono hExt1)
              fun Γ2 rb hExt2 hrb => ?_
            exact hk Γ2 (tupToSplit hf (tupAppend ra rb)) (hExt1.trans hExt2)
              (ArgsNormal_tupToSplit hf (ArgsNormal_tupAppend (hra.mono hExt2) hrb))
          · have habf :
              (a.size != 0 && a.size % 128 == 0 && b.size != 0 && b.size % 128 == 0) = false :=
              Bool.eq_false_iff.mpr hab
            simp only [habf, Bool.false_eq_true, ↓reduceIte]
            exact hsc xs ys hxs hys hk

theorem legalShufb_isLegal (target : LegalTarget) {Δ : List (List Ty)} {rs : List Ty}
    (hv : target.valid = true) (h32 : 32 ∈ target.bitWidths) :
    ∀ (t : Ty) {Γ : List (Ty × VarKind)}, target.supportsTy t = true →
      (xs ys : Tup (Arg K) (target.legalTys t)) → ArgsNormal target Γ xs → ArgsNormal target Γ ys →
      {k : Tup (Arg K) (target.legalTys t) → Expr K KL rs} →
      IsLegalCont target Γ Δ (fun Γ' res => ArgsNormal target Γ' res) k →
      (toTFlat (legalShufb target t xs ys k) Γ.length Δ.length).isLegal target Γ Δ = true
  | t, Γ, ht, xs, ys, hxs, hys, k, hk => by
    have h8 := valid_mem8 hv
    have hsc : ∀ {Γ' : List (Ty × VarKind)} (ys1 ys2 : Tup (Arg K) (target.legalTys t)),
        ArgsNormal target Γ' ys1 → ArgsNormal target Γ' ys2 →
        IsLegalCont target Γ' Δ (fun Γ'' res => ArgsNormal target Γ'' res) k →
        (toTFlat (legalSimdScalar128 target scalarShufb128 t ys1 ys2 k)
            Γ'.length Δ.length).isLegal target Γ' Δ = true := by
      intro Γ' ys1 ys2 h1 h2 hk'
      refine legalSimdScalar128_isLegal target hv h32 _
        (fun {Γa} a0 a1 a2 a3 b0 b1 b2 b3 cont ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hcont => ?_)
        t ht ys1 ys2 h1 h2 hk'
      exact scalarShufb128_isLegal target h8 h32 a0 a1 a2 a3 b0 b1 b2 b3 ha0 ha1 ha2 ha3 hb0 hb1 hb2
        hb3 hcont
    rw [legalShufb.eq_def]
    by_cases hsz : (t.size == 0 || t.size % 128 != 0) = true
    · simp [hsz, toTFlat_hlt]
    · have hszf : (t.size == 0 || t.size % 128 != 0) = false := Bool.eq_false_iff.mpr hsz
      simp only [hszf, Bool.false_eq_true, ↓reduceIte]
      have ⟨hsz0, hmod⟩ : (t.size != 0) = true ∧ (t.size % 128 == 0) = true := by
        simpa [Bool.or_eq_false_iff, Bool.not_eq_true', bne_iff_ne] using hszf
      cases t with
      | bool => exact hsc xs ys hxs hys hk
      | bits _ => exact hsc xs ys hxs hys hk
      | float _ => exact hsc xs ys hxs hys hk
      | pair a b =>
        dsimp only
        split
        · next hp =>
          by_cases hsup : target.vecIntOpSupported (.shufb (.pair a b)) (.pair a b) false = true
          · simp only [hsup, ↓reduceIte]
            have hxs' := ArgsNormal_packedToTup hp hxs
            have hys' := ArgsNormal_packedToTup hp hys
            refine isLegal_let_op2_normal target (.shufb (.pair a b))
              (packedToTup hp xs).1 (packedToTup hp ys).1 _ rfl
              (by simp [LegalTarget.isLegalOp, hp, hsz0, hmod, hsup]) hxs'.1 hys'.1 hp ?_
            exact hk _ (tupToPacked hp (.var Γ.length, ())) (CtxExtends.cons _ _)
              (ArgsNormal_tupToPacked hp ⟨ArgNormal.head target Γ hp, trivial⟩)
          · have hsupf : target.vecIntOpSupported (.shufb (.pair a b)) (.pair a b) false = false :=
              Bool.eq_false_iff.mpr hsup
            simp only [hsupf, Bool.false_eq_true, ↓reduceIte]
            exact hsc xs ys hxs hys hk
        · next hnp =>
          have hf := Bool.eq_false_iff.mpr hnp
          by_cases hab :
            (a.size != 0 && a.size % 128 == 0 && b.size != 0 && b.size % 128 == 0) = true
          · simp only [hab, ↓reduceIte]
            simp only [LegalTarget.supportsTy, Bool.and_eq_true] at ht
            obtain ⟨xa, xb⟩ := ArgsNormal_tupSplit (ArgsNormal_splitToTup hf hxs)
            obtain ⟨ya, yb⟩ := ArgsNormal_tupSplit (ArgsNormal_splitToTup hf hys)
            refine legalShufb_isLegal target hv h32 a ht.1 _ _ xa ya fun Γ1 ra hExt1 hra => ?_
            refine legalShufb_isLegal target hv h32 b ht.2 _ _ (xb.mono hExt1) (yb.mono hExt1)
              fun Γ2 rb hExt2 hrb => ?_
            exact hk Γ2 (tupToSplit hf (tupAppend ra rb)) (hExt1.trans hExt2)
              (ArgsNormal_tupToSplit hf (ArgsNormal_tupAppend (hra.mono hExt2) hrb))
          · have habf :
              (a.size != 0 && a.size % 128 == 0 && b.size != 0 && b.size % 128 == 0) = false :=
              Bool.eq_false_iff.mpr hab
            simp only [habf, Bool.false_eq_true, ↓reduceIte]
            exact hsc xs ys hxs hys hk


end LegalIsLegal

end LeanQbe.T
