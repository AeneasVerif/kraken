module

public import LeanQbe.T.Fold
public import LeanQbe.T.OptUtilLemmas
import LeanQbe.T.OpsLemmas

/-!
# Correctness of `fold`

* `OpCode.eval?_sound`: evaluating an immediate `OpCode` refines `OpCode.wp` (using `canonNaN` and
  `isFloatNaN_packedNaN` for nondeterministic float NaNs).
* `Op.rewrite_wp`: strength reductions (`mul → shl`, `udiv → lshr`, `urem → and`) refine `Op.wp`.
* `fold_wp`: source `wp` implies folded `wp`, proved via `Wf.induct`.
* `fold_wf`: `Wf` is preserved, proved via `Wf.induct`.
* `Func.fold_spec`, `Func.fold_wf`: closed-function specifications.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T

/-! ## Soundness of `OpCode.eval?` -/

theorem evalFloatLeaf_sound (f : Fmt) (res : Float.Model.UnpackedFloat)
    {post : BitVec f.width → Prop} (hw : floatResultWp f res post) :
    post (if res.isNaN then canonNaN f else packFloat f res) := by
  simp only [floatResultWp] at hw
  split <;> rename_i hnan
  · simp only [hnan, ↓reduceIte] at hw
    exact hw (canonNaN f) (isFloatNaN_packedNaN f)
  · simp only [hnan, Bool.false_eq_true, ↓reduceIte] at hw
    exact hw

theorem evalFloat1_sound
    (op : Float.Model.Format → Float.Model.UnpackedFloat → Float.Model.UnpackedFloat)
    (t : Ty) (a r : Val t) (post : Val t → Prop)
    (hev : evalFloat1 op t a = some r) (hw : liftFloatRel1 op t a post) : post r := by
  refine liftFloatRel1_pred op (fun t a P => ∀ r, evalFloat1 op t a = some r → P r)
    (fun _ _ _ _ h hp r hr => h r (hp r hr))
    (fun f a _ hw r hr => by
      dsimp only [evalFloat1] at hr; simp only [Option.some.injEq] at hr; subst hr
      exact evalFloatLeaf_sound f _ hw)
    (fun s u a₁ a₂ _ hm r hr => by
      dsimp only [evalFloat1] at hr
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at hr
      rcases hr with ⟨r1, hr1, r2, hr2, rfl⟩
      exact hm r1 hr1 r2 hr2)
    t a post hw r hev

theorem evalFloat2_sound
    (op : Float.Model.Format → Float.Model.UnpackedFloat →
      Float.Model.UnpackedFloat → Float.Model.UnpackedFloat)
    (t : Ty) (a b r : Val t) (post : Val t → Prop)
    (hev : evalFloat2 op t a b = some r) (hw : liftFloatRel2 op t a b post) : post r := by
  refine liftFloatRel2_pred op (fun t a b P => ∀ r, evalFloat2 op t a b = some r → P r)
    (fun _ _ _ _ _ h hp r hr => h r (hp r hr))
    (fun f a b _ hw r hr => by
      dsimp only [evalFloat2] at hr; simp only [Option.some.injEq] at hr; subst hr
      exact evalFloatLeaf_sound f _ hw)
    (fun s u a₁ a₂ b₁ b₂ _ hm r hr => by
      dsimp only [evalFloat2] at hr
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at hr
      rcases hr with ⟨r1, hr1, r2, hr2, rfl⟩
      exact hm r1 hr1 r2 hr2)
    t a b post hw r hev

theorem evalFloat3_sound
    (op : Float.Model.Format → Float.Model.UnpackedFloat →
      Float.Model.UnpackedFloat → Float.Model.UnpackedFloat → Float.Model.UnpackedFloat)
    (t : Ty) (a b c r : Val t) (post : Val t → Prop)
    (hev : evalFloat3 op t a b c = some r) (hw : liftFloatRel3 op t a b c post) : post r := by
  refine liftFloatRel3_pred op (fun t a b c P => ∀ r, evalFloat3 op t a b c = some r → P r)
    (fun _ _ _ _ _ _ h hp r hr => h r (hp r hr))
    (fun f a b c _ hw r hr => by
      dsimp only [evalFloat3] at hr; simp only [Option.some.injEq] at hr; subst hr
      exact evalFloatLeaf_sound f _ hw)
    (fun s u a₁ a₂ b₁ b₂ c₁ c₂ _ hm r hr => by
      dsimp only [evalFloat3] at hr
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at hr
      rcases hr with ⟨r1, hr1, r2, hr2, rfl⟩
      exact hm r1 hr1 r2 hr2)
    t a b c post hw r hev

theorem evalConvertFloat_sound (src dst : Fmt) (b : BitVec src.width)
    {post : BitVec dst.width → Prop} (hw : convertFloat src dst b post) :
    post (evalConvertFloat src dst b) := by
  simp only [convertFloat] at hw
  dsimp only [evalConvertFloat]
  cases hu : unpackFloat src b with
  | notANumber =>
    simp only [hu] at hw
    exact hw (canonNaN dst) (isFloatNaN_packedNaN dst)
  | finite s m e _ => simp only [hu] at hw; exact hw
  | infinity s => simp only [hu] at hw; exact hw
  | zero s => simp only [hu] at hw; exact hw

theorem OpCode.eval?_sound : {sig rs : List Ty} → (c : OpCode sig rs) → (args : Tup Val sig) →
    {res : Tup Val rs} → (post : Tup Val rs → Prop) →
    c.eval? args = some res → c.wp args post → post res
  | _, _, .copy _, (_, ()), _, _, h, hw | _, _, .not _, (_, ()), _, _, h, hw
  | _, _, .clz _, (_, ()), _, _, h, hw | _, _, .cls _, (_, ()), _, _, h, hw
  | _, _, .rbit _, (_, ()), _, _, h, hw | _, _, .ctz _, (_, ()), _, _, h, hw
  | _, _, .popcnt _, (_, ()), _, _, h, hw | _, _, .ofBool _, (_, ()), _, _, h, hw
  | _, _, .unpair _ _, (_, ()), _, _, h, hw | _, _, .bitcast _ _ _, (_, ()), _, _, h, hw
  | _, _, .uitofp _ _, (_, ()), _, _, h, hw | _, _, .sitofp _ _, (_, ()), _, _, h, hw => by
    dsimp only [OpCode.eval?] at h; simp only [Option.some.injEq] at h; subst h; exact hw
  | _, _, .and _, (_, _, ()), _, _, h, hw | _, _, .or _, (_, _, ()), _, _, h, hw
  | _, _, .xor _, (_, _, ()), _, _, h, hw | _, _, .umulw _, (_, _, ()), _, _, h, hw
  | _, _, .smulw _, (_, _, ()), _, _, h, hw | _, _, .udiv0 _, (_, _, ()), _, _, h, hw
  | _, _, .sdiv0 _, (_, _, ()), _, _, h, hw | _, _, .mkpair _ _, (_, _, ()), _, _, h, hw
  | _, _, .sha256msg1, (_, _, ()), _, _, h, hw | _, _, .sha256msg2, (_, _, ()), _, _, h, hw => by
    dsimp only [OpCode.eval?] at h; simp only [Option.some.injEq] at h; subst h; exact hw
  | _, _, .ternlog _ _, (_, _, _, ()), _, _, h, hw | _, _, .fshl _, (_, _, _, ()), _, _, h, hw
  | _, _, .fshr _, (_, _, _, ()), _, _, h, hw | _, _, .select _, (_, _, _, ()), _, _, h, hw
  | _, _, .addc _, (_, _, _, ()), _, _, h, hw | _, _, .subb _, (_, _, _, ()), _, _, h, hw
  | _, _, .sha256rnds2, (_, _, _, ()), _, _, h, hw => by
    dsimp only [OpCode.eval?] at h; simp only [Option.some.injEq] at h; subst h; exact hw
  | _, _, .neg _, (_, ()), _, _, h, hw | _, _, .bswap _, (_, ()), _, _, h, hw
  | _, _, .zext _ _, (_, ()), _, _, h, hw | _, _, .sext _ _, (_, ()), _, _, h, hw
  | _, _, .trunc _ _, (_, ()), _, _, h, hw | _, _, .shufd _ _, (_, ()), _, _, h, hw
  | _, _, .fneg _, (_, ()), _, _, h, hw | _, _, .fabs _, (_, ()), _, _, h, hw => by
    dsimp only [OpCode.eval?] at h; dsimp only [OpCode.wp] at hw; split at h <;> simp_all
  | _, _, .add _, (_, _, ()), _, _, h, hw | _, _, .sub _, (_, _, ()), _, _, h, hw
  | _, _, .mul _, (_, _, ()), _, _, h, hw | _, _, .shl _, (_, _, ()), _, _, h, hw
  | _, _, .lshr _, (_, _, ()), _, _, h, hw | _, _, .ashr _, (_, _, ()), _, _, h, hw
  | _, _, .rotl _, (_, _, ()), _, _, h, hw | _, _, .rotr _, (_, _, ()), _, _, h, hw
  | _, _, .udiv _, (_, _, ()), _, _, h, hw | _, _, .sdiv _, (_, _, ()), _, _, h, hw
  | _, _, .urem _, (_, _, ()), _, _, h, hw | _, _, .srem _, (_, _, ()), _, _, h, hw
  | _, _, .shufb _, (_, _, ()), _, _, h, hw | _, _, .alignr _ _, (_, _, ()), _, _, h, hw
  | _, _, .blendw _ _, (_, _, ()), _, _, h, hw => by
    dsimp only [OpCode.eval?] at h; dsimp only [OpCode.wp] at hw; split at h <;> simp_all
  | _, _, .cmp _ _ _ h', (_, _, ()), _, _, h, hw => by
    subst h'; dsimp only [OpCode.eval?] at h; simp only [cast_eq] at h
    split at h <;> simp_all [OpCode.wp_cmp]
  | _, _, .blend _ _ h', (_, _, _, ()), _, _, h, hw => by
    subst h'; dsimp only [OpCode.eval?] at h; simp only [cast_eq, Option.some.injEq] at h
    subst h; exact hw
  | _, _, .fcmp _ _ _ h', (_, _, ()), _, _, h, hw => by
    subst h'; dsimp only [OpCode.eval?] at h; simp only [cast_eq] at h
    split at h <;> simp_all [OpCode.wp_fcmp]
  | _, _, .fadd t, (a, b, ()), _, post, h, hw | _, _, .fsub t, (a, b, ()), _, post, h, hw
  | _, _, .fmul t, (a, b, ()), _, post, h, hw | _, _, .fdiv t, (a, b, ()), _, post, h, hw => by
    dsimp only [OpCode.eval?] at h; simp only [Option.map_eq_some_iff] at h
    rcases h with ⟨r, hr, rfl⟩
    by_cases hf : !t.isFloatTree
    · dsimp only [OpCode.wp] at hw; simp_all
    · dsimp only [OpCode.wp] at hw; simp only [hf, Bool.false_eq_true, ↓reduceIte] at hw
      exact evalFloat2_sound _ t a b r (fun x => post (x, ())) hr hw
  | _, _, .ffma t, (a, b, c, ()), _, post, h, hw => by
    dsimp only [OpCode.eval?] at h; simp only [Option.map_eq_some_iff] at h
    rcases h with ⟨r, hr, rfl⟩
    by_cases hf : !t.isFloatTree
    · simp only [OpCode.wp_ffma, hf, ↓reduceIte] at hw
    · simp only [OpCode.wp_ffma, hf, Bool.false_eq_true, ↓reduceIte] at hw
      exact evalFloat3_sound _ t a b c r (fun x => post (x, ())) hr hw
  | _, _, .fsqrt t, (a, ()), _, post, h, hw => by
    dsimp only [OpCode.eval?] at h; simp only [Option.map_eq_some_iff] at h
    rcases h with ⟨r, hr, rfl⟩
    by_cases hf : !t.isFloatTree
    · simp only [OpCode.wp_fsqrt, hf, ↓reduceIte] at hw
    · simp only [OpCode.wp_fsqrt, hf, Bool.false_eq_true, ↓reduceIte] at hw
      exact evalFloat1_sound _ t a r (fun x => post (x, ())) hr hw
  | _, _, .fptoui f n, (a, ()), _, _, h, hw => by
    dsimp only [OpCode.eval?] at h; simp only [Option.bind_eq_some_iff] at h
    simp only [OpCode.wp_fptoui] at hw
    rcases h with ⟨z, hz, hr⟩; simp only [hz] at hw
    split at hr
    · simp only [Option.some.injEq] at hr; subst hr; exact hw.2.2
    · cases hr
  | _, _, .fptosi f n, (a, ()), _, _, h, hw => by
    dsimp only [OpCode.eval?] at h; simp only [OpCode.wp_fptosi] at hw
    split at h
    · simp only [Option.bind_eq_some_iff] at h; rcases h with ⟨z, hz, hr⟩; simp only [hz] at hw
      split at hr
      · simp only [Option.some.injEq] at hr; subst hr; exact hw.2.2.2
      · cases hr
    · cases h
  | _, _, .fcvt f g, (a, ()), _, _, h, hw => by
    dsimp only [OpCode.eval?] at h; simp only [Option.some.injEq] at h; subst h
    exact evalConvertFloat_sound f g a hw

/-! ## Algebraic identities, annihilators, and strength reduction lemmas -/

theorem isZeroVal_eq : ∀ (t : Ty) (v : Val t), isZeroVal t v = true → v = zeroVal t
  | .bool, v, h => by cases v <;> simp [isZeroVal, zeroVal] at h ⊢
  | .bits _, v, h => by simpa [isZeroVal, zeroVal] using h
  | .float _, v, h => by simpa [isZeroVal, zeroVal] using h
  | .pair a b, (v1, v2), h => by
    simp only [isZeroVal, Bool.and_eq_true] at h
    exact Prod.ext (isZeroVal_eq a v1 h.1) (isZeroVal_eq b v2 h.2)

theorem isOnesVal_eq : ∀ (t : Ty) (v : Val t), isOnesVal t v = true → v = onesVal t
  | .bool, v, h => by cases v <;> simp [isOnesVal, onesVal] at h ⊢
  | .bits _, v, h => by simpa [isOnesVal, onesVal] using h
  | .float _, v, h => by simpa [isOnesVal, onesVal] using h
  | .pair a b, (v1, v2), h => by
    simp only [isOnesVal, Bool.and_eq_true] at h
    exact Prod.ext (isOnesVal_eq a v1 h.1) (isOnesVal_eq b v2 h.2)

theorem isOneVal_eq : ∀ (t : Ty) (v : Val t), isOneVal t v = true → v = oneVal t
  | .bool, v, h => by cases v <;> simp [isOneVal, oneVal] at h ⊢
  | .bits _, v, h => by simpa [isOneVal, oneVal] using h
  | .float _, _, h => by simp [isOneVal] at h
  | .pair a b, (v1, v2), h => by
    simp only [isOneVal, Bool.and_eq_true] at h
    exact Prod.ext (isOneVal_eq a v1 h.1) (isOneVal_eq b v2 h.2)

theorem isZeroArg?_eq {t : Ty} {a : Arg Val t} (h : isZeroArg? a = true) : a.val = zeroVal t :=
  match a with | .imm c => isZeroVal_eq t c h | .var _ => by simp [isZeroArg?, Arg.imm?] at h

theorem isOnesArg?_eq {t : Ty} {a : Arg Val t} (h : isOnesArg? a = true) : a.val = onesVal t :=
  match a with | .imm c => isOnesVal_eq t c h | .var _ => by simp [isOnesArg?, Arg.imm?] at h

theorem isOneArg?_eq {t : Ty} {a : Arg Val t} (h : isOneArg? a = true) : a.val = oneVal t :=
  match a with | .imm c => isOneVal_eq t c h | .var _ => by simp [isOneArg?, Arg.imm?] at h

private theorem lift2_law (allowFlt : Bool) (fbv : ∀ {n}, BitVec n → BitVec n → BitVec n)
    (fbool : Bool → Bool → Bool) (g h k : (t : Ty) → Val t → Val t) :
    ∀ (t : Ty), (allowFlt = false → t.hasFloat = false) → ∀ (x : Val t),
      (hbv : ∀ {n} (x : BitVec n), fbv (g (.bits n) x) (h (.bits n) x) = k (.bits n) x := by
        intros; simp [zeroVal, oneVal, onesVal]) →
      (hflt : ∀ {f : Fmt} (x : BitVec f.width), allowFlt = true →
        fbv (g (.float f) x) (h (.float f) x) = k (.float f) x := by
        intro _ _ h; cases h) →
      (hbool : ∀ x, fbool (g .bool x) (h .bool x) = k .bool x := by intro x; cases x <;> rfl) →
      (hg : ∀ s u x₁ x₂, g (.pair s u) (x₁, x₂) = (g s x₁, g u x₂) := by intros; rfl) →
      (hh : ∀ s u x₁ x₂, h (.pair s u) (x₁, x₂) = (h s x₁, h u x₂) := by intros; rfl) →
      (hk : ∀ s u x₁ x₂, k (.pair s u) (x₁, x₂) = (k s x₁, k u x₂) := by intros; rfl) →
      lift2 fbv fbool t (g t x) (h t x) = k t x
  | .bool, _, x, _, _, hbool, _, _, _ => hbool x
  | .bits _, _, x, hbv, _, _, _, _, _ => hbv x
  | .float _, hnf, x, _, hflt, _, _, _, _ =>
    match allowFlt, hnf, hflt with
    | false, hnf, _ => False.elim (by simp [Ty.hasFloat] at hnf)
    | true, _, hflt => hflt x rfl
  | .pair s u, hnf, (x₁, x₂), hbv, hflt, hbool, hg, hh, hk => by
    simp only [Ty.hasFloat, Bool.or_eq_false_iff] at hnf
    rw [hg, hh, hk]
    exact Prod.ext
      (lift2_law allowFlt fbv fbool g h k s (fun h => (hnf h).1) x₁ hbv hflt hbool hg hh hk)
      (lift2_law allowFlt fbv fbool g h k u (fun h => (hnf h).2) x₂ hbv hflt hbool hg hh hk)

theorem cmpOp_evalBits_self {n : Nat} (o : CmpOp) (v : BitVec n) :
    o.evalBits v v = o.isRefl := by
  cases o <;> simp [CmpOp.evalBits, CmpOp.isRefl, BitVec.ult, BitVec.ule, BitVec.slt, BitVec.sle]

theorem cmpOp_evalBool_self (o : CmpOp) (v : Bool) :
    o.evalBool v v = o.isRefl := by
  cases o <;> cases v <;> rfl

theorem liftCmp_self : ∀ (o : CmpOp) (t : Ty) (v : Val t),
    t.hasFloat = false → liftCmp o.evalBits o.evalBool t v v = splatMaskVal t o.isRefl
  | o, .bool, v, _ => cmpOp_evalBool_self o v
  | o, .bits _, v, _ => cmpOp_evalBits_self o v
  | _, .float _, _, h => by simp [Ty.hasFloat] at h
  | o, .pair a b, (v1, v2), h => by
    simp only [Ty.hasFloat, Bool.or_eq_false_iff] at h
    exact Prod.ext (liftCmp_self o a v1 h.1) (liftCmp_self o b v2 h.2)

theorem blendV_splatMask_true : ∀ (t : Ty) (a b : Val t),
    blendV t (splatMaskVal t true) a b = a
  | .bool, _, _ => rfl
  | .bits _, _, _ => rfl
  | .float _, _, _ => rfl
  | .pair s u, a, b => Prod.ext (blendV_splatMask_true s a.1 b.1) (blendV_splatMask_true u a.2 b.2)

theorem blendV_splatMask_false : ∀ (t : Ty) (a b : Val t),
    blendV t (splatMaskVal t false) a b = b
  | .bool, _, _ => rfl
  | .bits _, _, _ => rfl
  | .float _, _, _ => rfl
  | .pair s u, a, b =>
    Prod.ext (blendV_splatMask_false s a.1 b.1) (blendV_splatMask_false u a.2 b.2)

theorem blendV_self : ∀ (t : Ty) (c : Val t.mask) (a : Val t),
    blendV t c a a = a
  | .bool, c, _ => by cases c <;> rfl
  | .bits _, c, _ => by cases c <;> rfl
  | .float _, c, _ => by cases c <;> rfl
  | .pair s u, c, (a1, a2) => Prod.ext (blendV_self s c.1 a1) (blendV_self u c.2 a2)

private theorem pick_getElem {w : Nat} (bit : Bool) (v : BitVec w) {i : Nat} (_hi : i < w) :
    (if bit then v else ~~~v)[i] = (bit == v[i]) := by
  cases bit <;> simp [BitVec.getElem_not]

private theorem ternaryLogic_foldl_getElem {w : Nat} (a b c : BitVec w) (imm : BitVec 8)
    {i : Nat} (hi : i < w) (ks : List Nat) (acc : BitVec w) :
    (ks.foldl (fun acc k =>
      if imm.getLsbD k then
        acc ||| ((if (k / 4 % 2 == 1) then a else ~~~a) &&&
          (if (k / 2 % 2 == 1) then b else ~~~b) &&&
          (if (k % 2 == 1) then c else ~~~c))
      else acc) acc)[i] =
    ks.foldl (fun accB k =>
      accB || (imm.getLsbD k &&
        ((k / 4 % 2 == 1) == a[i]) && ((k / 2 % 2 == 1) == b[i]) && ((k % 2 == 1) == c[i])))
      acc[i] := by
  induction ks generalizing acc with
  | nil => rfl
  | cons k ks ih =>
    simp only [List.foldl_cons]
    rw [ih]
    congr 1
    cases hbit : imm.getLsbD k
    · simp
    · simp only [↓reduceIte, BitVec.getElem_or, BitVec.getElem_and,
        pick_getElem _ _ hi, Bool.true_and, Bool.and_assoc]

theorem ternaryLogic_getElem {w : Nat} (a b c : BitVec w) (imm : BitVec 8) (i : Nat) (hi : i < w) :
    (ternaryLogic a b c imm)[i] = ternaryLogicBool a[i] b[i] c[i] imm := by
  rw [ternaryLogic, ternaryLogic_foldl_getElem a b c imm hi]
  have hr : List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] := rfl
  rw [hr]
  simp only [ternaryLogicBool, BitVec.getElem_zero, List.foldl_cons, List.foldl_nil]
  cases a[i] <;> cases b[i] <;> cases c[i] <;> simp

private theorem ternlog_simp_eq (imm c : BitVec 8) (himm : (imm == c) = true)
    (k : (t : Ty) → Val t → Val t → Val t → Val t) :
    ∀ (t : Ty) (a b d : Val t),
      (hbv : ∀ {w} (x y z : BitVec w) i (_ : i < w),
        (k (.bits w) x y z)[i] = ternaryLogicBool x[i] y[i] z[i] c := by
        intro _ x y z i _
        cases x[i] <;> cases y[i] <;> cases z[i] <;> simp [zeroVal, onesVal, ternaryLogicBool]) →
      (hflt : ∀ {f} (x y z : BitVec f.width) i (_ : i < f.width),
        (k (.float f) x y z)[i] = ternaryLogicBool x[i] y[i] z[i] c := by
        intro _ x y z i _
        cases x[i] <;> cases y[i] <;> cases z[i] <;> simp [zeroVal, onesVal, ternaryLogicBool]) →
      (hbool : ∀ x y z : Bool, ternaryLogicBool x y z c = k .bool x y z := by
        intro x y z; cases x <;> cases y <;> cases z <;> rfl) →
      (hk : ∀ s u a b d, k (.pair s u) a b d = (k s a.1 b.1 d.1, k u a.2 b.2 d.2) := by
        intros; rfl) →
      lift3 (fun x y z => ternaryLogic x y z imm)
        (fun x y z => ternaryLogicBool x y z imm) t a b d = k t a b d
  | .bool, a, b, d, _, _, hbool, _ => eq_of_beq himm ▸ hbool a b d
  | .bits _, a, b, d, hbv, _, _, _ => by
    obtain rfl := eq_of_beq himm
    ext i hi; simp only [lift3]; rw [ternaryLogic_getElem _ _ _ _ i hi, hbv a b d i hi]
  | .float _, a, b, d, _, hflt, _, _ => by
    obtain rfl := eq_of_beq himm
    ext i hi; simp only [lift3]; rw [ternaryLogic_getElem _ _ _ _ i hi, hflt a b d i hi]
  | .pair s u, a, b, d, hbv, hflt, hbool, hk => by
    rw [hk]
    exact Prod.ext (ternlog_simp_eq imm c himm k s a.1 b.1 d.1 hbv hflt hbool hk)
      (ternlog_simp_eq imm c himm k u a.2 b.2 d.2 hbv hflt hbool hk)

private theorem ternlog_simp_wp {t : Ty} {P : Tup Val [t] → Prop} {a b d : Val t}
    (imm c : BitVec 8) (himm : (imm == c) = true) (k : (t : Ty) → Val t → Val t → Val t → Val t)
    (hw : P (lift3 (fun x y z => ternaryLogic x y z imm)
      (fun x y z => ternaryLogicBool x y z imm) t a b d, ()))
    (hbv : ∀ {w} (x y z : BitVec w) i (_ : i < w),
      (k (.bits w) x y z)[i] = ternaryLogicBool x[i] y[i] z[i] c := by
      intro _ x y z i _
      cases x[i] <;> cases y[i] <;> cases z[i] <;> simp [zeroVal, onesVal, ternaryLogicBool])
    (hflt : ∀ {f} (x y z : BitVec f.width) i (_ : i < f.width),
      (k (.float f) x y z)[i] = ternaryLogicBool x[i] y[i] z[i] c := by
      intro _ x y z i _
      cases x[i] <;> cases y[i] <;> cases z[i] <;> simp [zeroVal, onesVal, ternaryLogicBool])
    (hbool : ∀ x y z : Bool, ternaryLogicBool x y z c = k .bool x y z := by
      intro x y z; cases x <;> cases y <;> cases z <;> rfl)
    (hk : ∀ s u a b d, k (.pair s u) a b d = (k s a.1 b.1 d.1, k u a.2 b.2 d.2) := by
      intros; rfl) :
    P (k t a b d, ()) :=
  ternlog_simp_eq imm c himm k t a b d hbv hflt hbool hk ▸ hw

theorem signExtend_self {n : Nat} (a : BitVec n) : a.signExtend n = a := by
  ext i hi
  simp only [BitVec.getElem_signExtend]
  have : ¬ n ≤ i := by omega
  simp [hi]

private theorem one_toNat_of_pos {n : Nat} (hn : 0 < n) : (1#n : BitVec n).toNat = 1 := by
  simpa [BitVec.toNat_ofNat] using Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))

theorem div_one_of_pos {n : Nat} (_hn : 0 < n) (a : BitVec n) : a / 1#n = a := by simp

theorem mod_one_of_pos {n : Nat} (_hn : 0 < n) (a : BitVec n) : a % 1#n = 0#n := by simp

theorem one_ne_zero_of_pos {n : Nat} (hn : 0 < n) : (1#n : BitVec n) ≠ 0#n := by
  intro h; have := congrArg BitVec.toNat h; simp [one_toNat_of_pos hn] at this

private theorem one_toInt_of_one_lt {n : Nat} (hn : 1 < n) : (1#n : BitVec n).toInt = 1 := by
  have hpowN : 4 ≤ 2 ^ n :=
    calc 4 = 2 ^ 2 := by decide
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hn
  have hpowI : (4 : Int) ≤ ((2 ^ n : Nat) : Int) := by exact_mod_cast hpowN
  have hmod : (1 : Int) % ((2 ^ n : Nat) : Int) = 1 := Int.emod_eq_of_lt (by omega) (by omega)
  have h1 : (1#n : BitVec n) = BitVec.ofInt n 1 := by
    apply BitVec.eq_of_toNat_eq; rw [one_toNat_of_pos (by omega), BitVec.toNat_ofInt]
    exact_mod_cast hmod.symm
  rw [h1, BitVec.toInt_ofInt]; unfold Int.bmod; rw [hmod]; dsimp only; split <;> omega

theorem sdiv_one_of_one_lt {n : Nat} (hn : 1 < n) (a : BitVec n) : a.sdiv 1#n = a := by
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_sdiv, one_toInt_of_one_lt hn, Int.tdiv_one, ← BitVec.toInt_ofInt,
    BitVec.ofInt_toInt]

theorem srem_one_of_one_lt {n : Nat} (_hn : 1 < n) (a : BitVec n) : a.srem 1#n = 0#n := by simp

/-! ## Strength reduction soundness (`Op.rewrite_wp`) -/

theorem findPow2_spec {w : Nat} {x : BitVec w} :
    ∀ {limit m : Nat}, findPow2 w x limit = some m → m < limit ∧ x = BitVec.twoPow w m
  | 0, _, h => nomatch h
  | l + 1, _, h => by
    simp only [findPow2] at h
    split at h
    · next hx => cases h; exact ⟨Nat.lt_succ_self l, hx⟩
    · obtain ⟨hm, hx⟩ := findPow2_spec h
      exact ⟨Nat.lt_succ_of_lt hm, hx⟩

private theorem lt_two_pow_self (n : Nat) : n < 2 ^ n := by
  induction n with
  | zero => decide
  | succ k ih =>
    have hp : 1 ≤ 2 ^ k := Nat.one_le_pow _ _ (by decide)
    rw [Nat.pow_succ]
    omega

theorem leafPow2Shift?_mul_r : ∀ (t : Ty) (a c s : Val t),
    t.hasFloat = false → leafPow2Shift? t c = some s →
    lift2 (fun {n} x y => x <<< (y.toNat % n)) (fun x _ => x) t a s =
      lift2 (· * ·) (· && ·) t a c
  | .bits n, a, c, s, _, hs => by
    simp only [leafPow2Shift?, Option.map_eq_some_iff] at hs
    rcases hs with ⟨m, hm, rfl⟩
    obtain ⟨hlt, hpow⟩ := findPow2_spec hm
    have hm2 : m < 2 ^ n := Nat.lt_trans hlt (lt_two_pow_self n)
    have hs' : (BitVec.ofNat n m).toNat % n = m := by
      simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm2, Nat.mod_eq_of_lt hlt]
    simp only [lift2, hs', hpow, BitVec.shiftLeft_eq_mul_twoPow]
  | .pair t1 t2, (a1, a2), (c1, c2), (s1, s2), hf, hs => by
    simp only [Ty.hasFloat, Bool.or_eq_false_iff] at hf
    simp only [leafPow2Shift?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq, Prod.mk.injEq] at hs
    rcases hs with ⟨x1, hx1, x2, hx2, rfl, rfl⟩
    exact Prod.ext (leafPow2Shift?_mul_r t1 a1 c1 x1 hf.1 hx1)
      (leafPow2Shift?_mul_r t2 a2 c2 x2 hf.2 hx2)
  | .bool, _, _, _, _, hs => by simp [leafPow2Shift?] at hs
  | .float _, _, _, _, hf, _ => by simp [Ty.hasFloat] at hf

theorem leafPow2Shift?_mul_l (t : Ty) (a c s : Val t)
    (hf : t.hasFloat = false) (hs : leafPow2Shift? t c = some s) :
    lift2 (fun {n} x y => x <<< (y.toNat % n)) (fun x _ => x) t a s =
      lift2 (· * ·) (· && ·) t c a := by
  rw [leafPow2Shift?_mul_r t a c s hf hs,
    lift2_comm (· * ·) (· && ·) BitVec.mul_comm Bool.and_comm t a c]

theorem twoPow_ne_zero {n m : Nat} (hm : m < n) : BitVec.twoPow n m ≠ 0#n := by
  intro h
  have := congrArg BitVec.toNat h
  have hlt : 2 ^ m < 2 ^ n := Nat.pow_lt_pow_right (by decide) hm
  simp [BitVec.toNat_twoPow, Nat.mod_eq_of_lt hlt] at this

theorem udiv_twoPow {n m : Nat} (hm : m < n) (a : BitVec n) :
    a >>> ((BitVec.ofNat n m).toNat % n) = a / BitVec.twoPow n m := by
  have hm2 : m < 2 ^ n := Nat.lt_trans hm (lt_two_pow_self n)
  have hlt : 2 ^ m < 2 ^ n := Nat.pow_lt_pow_right (by decide) hm
  have hmod : (BitVec.ofNat n m).toNat % n = m := by
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm2, Nat.mod_eq_of_lt hm]
  apply BitVec.eq_of_toNat_eq
  rw [hmod]
  simp [BitVec.toNat_ushiftRight, BitVec.toNat_udiv, BitVec.toNat_twoPow,
    Nat.mod_eq_of_lt hlt, Nat.shiftRight_eq_div_pow]

theorem urem_twoPow {n m : Nat} (hm : m < n) (a : BitVec n) :
    a &&& (BitVec.twoPow n m - 1#n) = a % BitVec.twoPow n m := by
  have hlt : 2 ^ m < 2 ^ n := Nat.pow_lt_pow_right (by decide) hm
  have h1 := one_toNat_of_pos (by omega : 0 < n)
  have hpow : (BitVec.twoPow n m).toNat = 2 ^ m := by
    simp [BitVec.toNat_twoPow, Nat.mod_eq_of_lt hlt]
  have hp1 : 1 ≤ 2 ^ m := Nat.one_le_pow _ _ (by decide)
  have hsub : (BitVec.twoPow n m - 1#n).toNat = 2 ^ m - 1 := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hpow, h1]; exact hp1), hpow, h1]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_umod, hpow, hsub, Nat.and_two_pow_sub_one_eq_mod]

private theorem Op.rewrite_mul_a_wp {t : Ty} (hf0 : t.hasFloat = false)
    (a b : Arg Val t) {P : Tup Val [t] → Prop}
    (hw : (⟨.mul t, (a, b, ())⟩ : Op Val [t]).wp P) :
    (match a.imm?.bind (leafPow2Shift? t) with
      | some s => op2 (.shl t) b (.imm s)
      | none => op2 (.mul t) a b).wp P := by
  cases a with
  | var _ => simpa [Arg.imm?, Op.wp, op2] using hw
  | imm ca =>
    simp only [Arg.imm?, Option.bind_some]
    cases hs : leafPow2Shift? t ca with
    | none => simpa [Op.wp, op2] using hw
    | some s =>
      simpa [Op.wp, op2, OpCode.wp_shl, OpCode.wp_mul, hf0, vals,
        leafPow2Shift?_mul_l t b.val ca s hf0 hs] using hw

theorem Op.rewrite_wp {rs : List Ty} (op : Op Val rs) (P : Tup Val rs → Prop) :
    op.wp P → op.rewrite.wp P := by
  rcases op with ⟨code, args⟩
  cases code with
  | mul t =>
    rcases args with ⟨a, b, ⟨⟩⟩; intro hw; dsimp only [Op.rewrite]
    by_cases hf : t.hasFloat
    · simp [hf]; exact hw
    · have hf0 : t.hasFloat = false := Bool.eq_false_iff.mpr hf
      simp only [hf, Bool.false_eq_true, ↓reduceIte]
      cases b with
      | var _ => simp only [Arg.imm?, Option.bind_none]; exact Op.rewrite_mul_a_wp hf0 a _ hw
      | imm cb =>
        simp only [Arg.imm?, Option.bind_some]
        cases hsb : leafPow2Shift? t cb with
        | some s =>
          simpa [Op.wp, op2, OpCode.wp_shl, OpCode.wp_mul, hf0, vals,
            leafPow2Shift?_mul_r t a.val cb s hf0 hsb] using hw
        | none => exact Op.rewrite_mul_a_wp hf0 a (.imm cb) hw
  | udiv n | urem n =>
    rcases args with ⟨a, b, ⟨⟩⟩; intro hw; dsimp only [Op.rewrite]
    cases b with
    | var _ => simp [Arg.imm?]; exact hw
    | imm cb =>
      simp only [Arg.imm?, Option.bind_some]
      cases hfm : findPow2 n cb n with
      | none => simp; exact hw
      | some m =>
        obtain ⟨hm, hpow⟩ := findPow2_spec hfm; subst hpow
        first
        | (simp only [Op.wp, OpCode.wp_udiv, op2, OpCode.wp_lshr, Ty.hasFloat,
            Bool.false_eq_true, ↓reduceIte, lift2, vals, Arg.val_imm] at hw ⊢
           rw [udiv_twoPow hm]; exact hw.2)
        | (simp only [Op.wp, OpCode.wp_urem, op2, OpCode.wp_and, lift2, vals, Arg.val_imm] at hw ⊢
           rw [urem_twoPow hm]; exact hw.2)
  | _ => exact fun hw => hw

/-! ## Comparison bound, normalization, and extension-narrowing lemmas -/

private theorem two_pow_eq_double {n : Nat} (hn : 0 < n) : 2 ^ n = 2 * 2 ^ (n - 1) := by
  cases n with
  | zero => omega
  | succ k => simp [Nat.pow_succ, Nat.mul_comm]

private theorem bvIntMin_toNat {n : Nat} (hn : 0 < n) :
    (BitVec.intMin n).toNat = 2 ^ (n - 1) := by
  simp only [BitVec.toNat_intMin]
  exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) (by omega))

private theorem bvIntMax_toNat {n : Nat} (hn : 0 < n) :
    (bvIntMax n).toNat = 2 ^ (n - 1) - 1 := by
  have hmin := bvIntMin_toNat hn
  have hpow := two_pow_eq_double hn
  simp only [bvIntMax, BitVec.toNat_not, hmin]
  omega

private theorem bvIntMin_toInt {n : Nat} (hn : 0 < n) :
    (BitVec.intMin n).toInt = -(2 ^ (n - 1) : Int) := by
  have hmin := bvIntMin_toNat hn
  have hpow := two_pow_eq_double hn
  unfold BitVec.toInt
  rw [hmin]
  have hlt : ¬ (2 * 2 ^ (n - 1) < 2 ^ n) := by omega
  simp only [hlt, ↓reduceIte]
  have hpowI : ((2 ^ n : Nat) : Int) = 2 * ((2 ^ (n - 1) : Nat) : Int) := by exact_mod_cast hpow
  push_cast at hpowI ⊢
  omega

private theorem bvIntMax_toInt {n : Nat} (hn : 0 < n) :
    (bvIntMax n).toInt = (2 ^ (n - 1) : Int) - 1 := by
  have hmax := bvIntMax_toNat hn
  have hpos : 1 ≤ 2 ^ (n - 1) := Nat.one_le_pow _ _ (by decide)
  have hpow := two_pow_eq_double hn
  unfold BitVec.toInt
  rw [hmax]
  have hlt : 2 * (2 ^ (n - 1) - 1) < 2 ^ n := by omega
  simp only [hlt, ↓reduceIte]
  have hsub : ((2 ^ (n - 1) - 1 : Nat) : Int) = ((2 ^ (n - 1) : Nat) : Int) - 1 := by omega
  rw [hsub]
  push_cast
  rfl

private theorem add_one_toNat_of_ne_allOnes {n : Nat} {c : BitVec n}
    (hne : c ≠ BitVec.allOnes n) : (c + 1#n).toNat = c.toNat + 1 := by
  have hn : 0 < n := by
    cases n with
    | zero => exact False.elim (hne (Subsingleton.elim _ _))
    | succ _ => omega
  have hneNat : c.toNat ≠ 2 ^ n - 1 := by
    intro h
    apply hne
    apply BitVec.eq_of_toNat_eq
    simpa [BitVec.toNat_allOnes] using h
  have hlt : c.toNat + 1 < 2 ^ n := by have := c.isLt; omega
  rw [BitVec.toNat_add, one_toNat_of_pos hn, Nat.mod_eq_of_lt hlt]

private theorem add_one_toInt_of_ne_intMax {n : Nat} {c : BitVec n}
    (hne : c ≠ bvIntMax n) : (c + 1#n).toInt = c.toInt + 1 := by
  have hn : 0 < n := by
    cases n with
    | zero => exact False.elim (hne (Subsingleton.elim _ _))
    | succ _ => omega
  have hpow := two_pow_eq_double hn
  have hmax := bvIntMax_toNat hn
  have hneNat : c.toNat ≠ 2 ^ (n - 1) - 1 := fun h =>
    hne (BitVec.eq_of_toNat_eq (h.trans hmax.symm))
  have h1 := one_toNat_of_pos hn
  have hpos : 1 ≤ 2 ^ (n - 1) := Nat.one_le_pow _ _ (by decide)
  have hc := c.isLt
  unfold BitVec.toInt
  rw [BitVec.toNat_add, h1]
  by_cases hwrap : c.toNat + 1 < 2 ^ n
  · rw [Nat.mod_eq_of_lt hwrap]
    split <;> split <;> omega
  · have hmod : (c.toNat + 1) % 2 ^ n = 0 := by
      have heq : c.toNat + 1 = 2 ^ n := by omega
      rw [heq, Nat.mod_self]
    rw [hmod]
    split <;> split <;> omega

theorem cmpImmBound?_sound {n : Nat} (o : CmpOp) (x c : BitVec n) {res : Bool}
    (h : cmpImmBound? o n c = some res) : o.evalBits x c = res := by
  cases o <;> simp only [cmpImmBound?] at h
  · cases h
  · cases h
  · split at h
    · rename_i heq; cases h; obtain rfl := eq_of_beq heq
      simp [CmpOp.evalBits, BitVec.ult]
    · cases h
  · split at h
    · rename_i heq; cases h; obtain rfl := eq_of_beq heq
      have hx := x.isLt
      simp [CmpOp.evalBits, BitVec.ule, BitVec.toNat_allOnes]; omega
    · cases h
  · split at h
    · rename_i heq; cases h; obtain rfl := eq_of_beq heq
      have hx := x.isLt
      simp [CmpOp.evalBits, BitVec.ult, BitVec.toNat_allOnes]; omega
    · cases h
  · split at h
    · rename_i heq; cases h; obtain rfl := eq_of_beq heq
      simp [CmpOp.evalBits, BitVec.ule]
    · cases h
  · split at h
    · rename_i heq; cases h; obtain rfl := eq_of_beq heq
      cases n with
      | zero => rw [Subsingleton.elim x 0#0]; decide
      | succ k =>
        have hlo := x.le_toInt
        simp only [Nat.add_sub_cancel] at hlo
        simp [CmpOp.evalBits, BitVec.slt, bvIntMin_toInt (Nat.succ_pos k)]
        omega
    · cases h
  · split at h
    · rename_i heq; cases h; obtain rfl := eq_of_beq heq
      cases n with
      | zero => rw [Subsingleton.elim x 0#0]; decide
      | succ k =>
        have hhi := x.toInt_lt
        simp only [Nat.add_sub_cancel] at hhi
        simp [CmpOp.evalBits, BitVec.sle, bvIntMax_toInt (Nat.succ_pos k)]
        omega
    · cases h
  · split at h
    · rename_i heq; cases h; obtain rfl := eq_of_beq heq
      cases n with
      | zero => rw [Subsingleton.elim x 0#0]; decide
      | succ k =>
        have hhi := x.toInt_lt
        simp only [Nat.add_sub_cancel] at hhi
        simp [CmpOp.evalBits, BitVec.slt, bvIntMax_toInt (Nat.succ_pos k)]
        omega
    · cases h
  · split at h
    · rename_i heq; cases h; obtain rfl := eq_of_beq heq
      cases n with
      | zero => rw [Subsingleton.elim x 0#0]; decide
      | succ k =>
        have hlo := x.le_toInt
        simp only [Nat.add_sub_cancel] at hlo
        simp [CmpOp.evalBits, BitVec.sle, bvIntMin_toInt (Nat.succ_pos k)]
        omega
    · cases h

theorem normBitsCmpImm_eval {n : Nat} (o : CmpOp) (x c : BitVec n) :
    (normBitsCmpImm o n c).1.evalBits x (normBitsCmpImm o n c).2 = o.evalBits x c := by
  cases o with
  | ule =>
    simp only [normBitsCmpImm]
    split
    · rename_i h0; obtain rfl := eq_of_beq h0
      apply Bool.eq_iff_iff.2
      simp [CmpOp.evalBits, BitVec.ule]
      exact ⟨fun hx => by subst hx; rfl, fun hle => BitVec.eq_of_toNat_eq (by simp; omega)⟩
    · split
      · rename_i hne
        have hne' : c ≠ BitVec.allOnes n := by simpa using hne
        simp only [CmpOp.evalBits, BitVec.ult, BitVec.ule,
          add_one_toNat_of_ne_allOnes hne', decide_eq_decide]
        omega
      · rfl
  | ugt =>
    simp only [normBitsCmpImm]
    split
    · rename_i h0; obtain rfl := eq_of_beq h0
      apply Bool.eq_iff_iff.2
      simp [CmpOp.evalBits, BitVec.ult]
      exact ⟨fun hne => by
        have : x.toNat ≠ 0 := fun h => hne (BitVec.eq_of_toNat_eq (by simpa using h))
        omega,
        fun hlt heq => by subst heq; simp at hlt⟩
    · split
      · rename_i hne
        have hne' : c ≠ BitVec.allOnes n := by simpa using hne
        simp only [CmpOp.evalBits, BitVec.ult, BitVec.ule,
          add_one_toNat_of_ne_allOnes hne', decide_eq_decide]
        omega
      · rfl
  | sle =>
    simp only [normBitsCmpImm]
    split
    · rename_i hne
      have hne' : c ≠ bvIntMax n := by simpa using hne
      simp only [CmpOp.evalBits, BitVec.slt, BitVec.sle,
        add_one_toInt_of_ne_intMax hne', decide_eq_decide]
      omega
    · rfl
  | sgt =>
    simp only [normBitsCmpImm]
    split
    · rename_i hne
      have hne' : c ≠ bvIntMax n := by simpa using hne
      simp only [CmpOp.evalBits, BitVec.slt, BitVec.sle,
        add_one_toInt_of_ne_intMax hne', decide_eq_decide]
      omega
    · rfl
  | _ => rfl

private theorem setWidth_signExtend_of_le {m n : Nat} (hle : m ≤ n) (x : BitVec m) :
    (x.signExtend n).setWidth m = x := by
  ext i hi
  simp [BitVec.getElem_signExtend, Nat.lt_of_lt_of_le hi hle, hi]

private theorem toNat_signExtend_of_le {m n : Nat} (hle : m ≤ n) (x : BitVec m) :
    (x.signExtend n).toNat =
      if 2 * x.toNat < 2 ^ m then x.toNat else x.toNat + 2 ^ n - 2 ^ m := by
  have hti : (x.signExtend n).toInt = x.toInt := BitVec.toInt_signExtend_of_le hle
  have hpow : 2 ^ m ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hle
  have hx := x.isLt
  have hxs := (x.signExtend n).isLt
  unfold BitVec.toInt at hti
  split at hti <;> split at hti <;> split <;> omega

theorem cmpOp_evalBits_signExtend {m n : Nat} (hlt : m < n) (o : CmpOp) (x y : BitVec m) :
    o.evalBits (x.signExtend n) (y.signExtend n) = o.evalBits x y := by
  have hle : m ≤ n := Nat.le_of_lt hlt
  have hinj : (x.signExtend n = y.signExtend n) ↔ (x = y) :=
    ⟨fun h => by rw [← setWidth_signExtend_of_le hle x, ← setWidth_signExtend_of_le hle y, h],
     congrArg _⟩
  have hpow : 2 ^ m ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hle
  have hxi : (x.signExtend n).toInt = x.toInt := BitVec.toInt_signExtend_of_le hle
  have hyi : (y.signExtend n).toInt = y.toInt := BitVec.toInt_signExtend_of_le hle
  have hxn := toNat_signExtend_of_le hle x
  have hyn := toNat_signExtend_of_le hle y
  have hx := x.isLt; have hy := y.isLt
  cases o
  · simp [CmpOp.evalBits, hinj]
  · simp [CmpOp.evalBits, hinj]
  · simp only [CmpOp.evalBits, BitVec.ult, hxn, hyn, decide_eq_decide]
    split <;> split <;> omega
  · simp only [CmpOp.evalBits, BitVec.ule, hxn, hyn, decide_eq_decide]
    split <;> split <;> omega
  · simp only [CmpOp.evalBits, BitVec.ult, hxn, hyn, decide_eq_decide]
    split <;> split <;> omega
  · simp only [CmpOp.evalBits, BitVec.ule, hxn, hyn, decide_eq_decide]
    split <;> split <;> omega
  · simp [CmpOp.evalBits, BitVec.slt, hxi, hyi]
  · simp [CmpOp.evalBits, BitVec.sle, hxi, hyi]
  · simp [CmpOp.evalBits, BitVec.slt, hxi, hyi]
  · simp [CmpOp.evalBits, BitVec.sle, hxi, hyi]

theorem cmpOp_evalBits_setWidth {m n : Nat} (hlt : m < n) (o : CmpOp) (x y : BitVec m) :
    o.evalBits (x.setWidth n) (y.setWidth n) = o.toUnsigned.evalBits x y := by
  have hpow : 2 * 2 ^ m ≤ 2 ^ n := by
    rw [← Nat.pow_succ']; exact Nat.pow_le_pow_right (by decide) hlt
  have hx := x.isLt; have hy := y.isLt
  have hxn : (x.setWidth n).toNat = x.toNat := by
    simp [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega : x.toNat < 2 ^ n)]
  have hyn : (y.setWidth n).toNat = y.toNat := by
    simp [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega : y.toNat < 2 ^ n)]
  have hxi : (x.setWidth n).toInt = x.toNat := by
    unfold BitVec.toInt; rw [hxn]; simp [show 2 * x.toNat < 2 ^ n by omega]
  have hyi : (y.setWidth n).toInt = y.toNat := by
    unfold BitVec.toInt; rw [hyn]; simp [show 2 * y.toNat < 2 ^ n by omega]
  have hinj : (x.setWidth n = y.setWidth n) ↔ (x = y) :=
    ⟨fun h => BitVec.eq_of_toNat_eq (by rw [← hxn, ← hyn, h]), congrArg _⟩
  cases o <;>
    simp [CmpOp.evalBits, CmpOp.toUnsigned, BitVec.ult, BitVec.ule, BitVec.slt, BitVec.sle,
      hxn, hyn, hxi, hyi, hinj]

/-! ## Unary involution and extension-chain bitvector lemmas -/

private theorem lift1_not_not : ∀ (t : Ty) (x : Val t),
    lift1 (~~~ ·) (! ·) t (lift1 (~~~ ·) (! ·) t x) = x
  | .bool, x => Bool.not_not x
  | .bits _, _ | .float _, _ => by simp [lift1]
  | .pair s u, (x₁, x₂) => Prod.ext (lift1_not_not s x₁) (lift1_not_not u x₂)

private theorem bswapBits_go_getLsbD {w : Nat} (x : BitVec w) :
    ∀ (m i : Nat), i < 8 * m → 8 * m ≤ w →
      (bswapBits.go x m).getLsbD i = x.getLsbD (8 * (m - 1 - i / 8) + i % 8)
  | 0, _, hi, _ => by omega
  | m + 1, i, hi, hm => by
    have hd : i / 8 < m + 1 := Nat.div_lt_of_lt_mul hi
    simp only [bswapBits.go, BitVec.getLsbD_cast, BitVec.getLsbD_append]
    by_cases hlt : i < 8
    · have hdiv : i / 8 = 0 := Nat.div_eq_of_lt hlt
      have hmod : i % 8 = i := Nat.mod_eq_of_lt hlt
      simp [hlt, hdiv, hmod, show 8 * m + i < w by omega]
    · have ih := bswapBits_go_getLsbD x m (i - 8) (by omega) (by omega)
      have hdiv : (i - 8) / 8 + 1 = i / 8 := by omega
      have hmod : (i - 8) % 8 = i % 8 := by omega
      simp [hlt, ih]
      congr 1
      omega

private theorem bswapBits_getLsbD {w : Nat} (hw : w % 8 = 0) (x : BitVec w) {i : Nat}
    (hi : i < w) :
    (bswapBits x).getLsbD i = x.getLsbD (8 * (w / 8 - 1 - i / 8) + i % 8) := by
  have hmul : 8 * (w / 8) = w := by omega
  dsimp only [bswapBits]
  simp only [BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and]
  exact bswapBits_go_getLsbD x (w / 8) i (by omega) (by omega)

theorem bswapBits_bswapBits {w : Nat} (hw : w % 8 = 0) (x : BitVec w) :
    bswapBits (bswapBits x) = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hdiv : i / 8 < w / 8 := Nat.div_lt_of_lt_mul (by omega)
  have hmod : i % 8 < 8 := Nat.mod_lt i (by decide)
  have hj : 8 * (w / 8 - 1 - i / 8) + i % 8 < w := by omega
  rw [bswapBits_getLsbD hw (bswapBits x) hi, bswapBits_getLsbD hw x hj]
  have hdj : (8 * (w / 8 - 1 - i / 8) + i % 8) / 8 = w / 8 - 1 - i / 8 := by
    rw [Nat.mul_add_div (by decide), Nat.div_eq_of_lt hmod]; omega
  have hmj : (8 * (w / 8 - 1 - i / 8) + i % 8) % 8 = i % 8 := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hmod]
  rw [hdj, hmj]
  have hsub : w / 8 - 1 - (w / 8 - 1 - i / 8) = i / 8 := by omega
  rw [hsub, Nat.div_add_mod i 8]

private theorem lift1_bswap_bswap : ∀ (t : Ty), t.bswapOk = true →
    ∀ (x : Val t), lift1 bswapBits id t (lift1 bswapBits id t x) = x
  | .bool, h, _ | .float _, h, _ => by simp [Ty.bswapOk] at h
  | .bits _, h, x => bswapBits_bswapBits (eq_of_beq h) x
  | .pair s u, h, (x₁, x₂) => by
    simp only [Ty.bswapOk, Bool.and_eq_true] at h
    exact Prod.ext (lift1_bswap_bswap s h.1 x₁) (lift1_bswap_bswap u h.2 x₂)

private theorem reverse_reverse {n : Nat} (x : BitVec n) : x.reverse.reverse = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _hi
  simp

theorem setWidth_setWidth_le {w m n : Nat} (hnm : n ≤ m) (x : BitVec w) :
    (x.setWidth m).setWidth n = x.setWidth n := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, hi, show i < m by omega, decide_true, Bool.true_and]

theorem setWidth_setWidth_trans {w m n : Nat} (hwm : w ≤ m) (_hmn : m ≤ n)
    (x : BitVec w) : (x.setWidth m).setWidth n = x.setWidth n := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases hw : i < w
  · simp only [BitVec.getLsbD_setWidth, hi, show i < m by omega, decide_true, Bool.true_and]
  · rw [← BitVec.setWidth_eq x]
    simp only [BitVec.getLsbD_setWidth, hi, hw, decide_false, Bool.false_and, Bool.and_false]

theorem setWidth_signExtend_of_narrow {w m n : Nat} (hnw : n ≤ w) (hwm : w ≤ m)
    (x : BitVec w) : (x.signExtend m).setWidth n = x.setWidth n := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_signExtend, hi,
    show i < m by omega, show i < w by omega, decide_true, Bool.true_and, ↓reduceIte]

theorem setWidth_signExtend_of_mid {w m n : Nat} (_hwn : w ≤ n) (hnm : n ≤ m)
    (x : BitVec w) : (x.signExtend m).setWidth n = x.signExtend n := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_signExtend, hi,
    show i < m by omega, decide_true, Bool.true_and]

private theorem signExtend_signExtend_of_le {w m n : Nat} (hpos : 0 < w) (hwm : w ≤ m)
    (_hmn : m ≤ n) (x : BitVec w) : (x.signExtend m).signExtend n = x.signExtend n := by
  have hmsb : (x.signExtend m).msb = x.msb := by
    rw [BitVec.msb_eq_getLsbD_last, BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_signExtend]
    simp only [show m - 1 < m by omega, decide_true, Bool.true_and]
    split
    · simp only [show m - 1 = w - 1 by omega]
    · exact BitVec.msb_eq_getLsbD_last x
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_signExtend, hi, decide_true, Bool.true_and, hmsb]
  by_cases hm : i < m
  · simp only [hm, decide_true, Bool.true_and, ↓reduceIte]
  · simp only [hm, show ¬ i < w by omega, ↓reduceIte]

/-! ## Context invariants and `SimpAct` soundness -/

/-- Operation matching an `InvKind`. -/
def invOpVal : InvKind → (t : Ty) → Val t → Val t
  | .not_, t, x => lift1 (~~~ ·) (! ·) t x
  | .bswap, t, x => lift1 bswapBits id t x
  | .rbit, .bits _, x => x.reverse
  | .rbit, _, x => x

/-- Well-formedness side condition for `InvKind` at type `t`. -/
def invOpOk : InvKind → Ty → Prop
  | .not_, _ => True
  | .bswap, t => t.bswapOk = true
  | .rbit, _ => True

/-- Semantic invariant for extension provenance `BitsExt Val n`. -/
def BitsExtGood (ρ : (t : Ty) → Nat → Val t) (b : Nat) {n : Nat}
    (e : BitsExt Val n) (v : BitVec n) : Prop :=
  (match e.kind with
   | .sext => v = e.src.val.signExtend n
   | .zext => v = e.src.val.setWidth n) ∧
  e.srcKey.fev ρ = e.src.val ∧ e.srcKey.FLt b

/-- Semantic invariant for extension provenance `ExtDef Val t`. -/
def ExtDefGood (ρ : (t : Ty) → Nat → Val t) (b : Nat) :
    {t : Ty} → ExtDef Val t → Val t → Prop
  | .bits _, some e, v => BitsExtGood ρ b e v
  | .bits _, none, _ => True
  | .bool, _, _ | .float _, _, _ | .pair _ _, _, _ => True

/-- Semantic invariant for unary-involution provenance `Option (UnInv Val t)`. -/
def UnInvOptGood (ρ : (t : Ty) → Nat → Val t) (b : Nat) {t : Ty} :
    Option (UnInv Val t) → Val t → Prop
  | some iv, v =>
    invOpOk iv.kind t ∧ v = invOpVal iv.kind t iv.src.val ∧
    iv.srcKey.fev ρ = iv.src.val ∧ iv.srcKey.FLt b
  | none, _ => True

theorem ExtDefGood.none {ρ : (t : Ty) → Nat → Val t} {b : Nat} {t : Ty} {v : Val t} :
    ExtDefGood ρ b (ExtDef.none (t := t)) v := by
  cases t <;> trivial

theorem ExtDefGood.upd_all {ρ : (t : Ty) → Nat → Val t} {b : Nat} {ts : List Ty} (xs : Tup Val ts)
    {t : Ty} {e : ExtDef Val t} {v : Val t} (he : ExtDefGood ρ b e v) :
    ExtDefGood (fupdTup ρ b xs) (b + ts.length) e v := by
  cases t with
  | bits n =>
    cases e with
    | none => trivial
    | some e => exact ⟨he.1, (FKey.fev_fupdTup xs he.2.2).trans he.2.1, he.2.2.add⟩
  | bool | float _ | pair _ _ => trivial

theorem UnInvOptGood.upd_all {ρ : (t : Ty) → Nat → Val t} {b : Nat} {ts : List Ty} (xs : Tup Val ts)
    {t : Ty} {iv : Option (UnInv Val t)} {v : Val t} (hi : UnInvOptGood ρ b iv v) :
    UnInvOptGood (fupdTup ρ b xs) (b + ts.length) iv v := by
  cases iv with
  | none => trivial
  | some _ => exact ⟨hi.1, hi.2.1, (FKey.fev_fupdTup xs hi.2.2.2).trans hi.2.2.1, hi.2.2.2.add⟩

/-- Value invariant for one `FVal Val t` entry in `FGood`. -/
def FValGood (ρ : (t : Ty) → Nat → Val t) (b : Nat) {t : Ty} (r : FVal Val t) (v : Val t) : Prop :=
  r.out.val = v ∧ r.key.fev ρ = v ∧ r.key.FLt b ∧
  ExtDefGood ρ b r.ext v ∧ UnInvOptGood ρ b r.inv v

/-- Every input variable in `G` satisfies `FValGood`. -/
def FGood (ρ : (t : Ty) → Nat → Val t) (b : Nat) (G : Ctx (FVal Val) Val) : Prop :=
  ∀ p ∈ G, FValGood ρ b p.2.1 p.2.2

theorem FGood.cons {ρ : (t : Ty) → Nat → Val t} {b : Nat} {G : Ctx (FVal Val) Val}
    (hG : FGood ρ b G) {t : Ty} {r : FVal Val t} {v : Val t}
    (hr : FValGood ρ b r v) :
    FGood ρ b (⟨t, r, v⟩ :: G)
  | _, .head _ => hr
  | _, .tail _ hp => hG _ hp

theorem FGood.upd_all {ρ : (t : Ty) → Nat → Val t} {b : Nat} {G : Ctx (FVal Val) Val}
    (hG : FGood ρ b G) {ts : List Ty} (xs : Tup Val ts) :
    FGood (fupdTup ρ b xs) (b + ts.length) G := fun p hp =>
  let ⟨h1, h2, h3, h4, h5⟩ := hG p hp
  ⟨h1, (FKey.fev_fupdTup xs h3).trans h2, h3.add, h4.upd_all xs, h5.upd_all xs⟩

theorem FGood.append {ρ : (t : Ty) → Nat → Val t} {b : Nat} {G₁ G₂ : Ctx (FVal Val) Val}
    (h1 : FGood ρ b G₁) (h2 : FGood ρ b G₂) : FGood ρ b (G₁ ++ G₂) := fun p hp =>
  (List.mem_append.1 hp).elim (h1 p) (h2 p)

private theorem FGood.freshFVals_only (ρ : (t : Ty) → Nat → Val t) :
    {ts : List Ty} → (xs : Tup Val ts) → (b : Nat) →
    FGood (fupdTup ρ b xs) (b + ts.length) (Tup.zip (freshFVals ts xs b) xs)
  | [], (), _ => fun _ hp => nomatch hp
  | t :: ts, (x, xs), b => by
    simp only [freshFVals, tupFreshWith, Tup.zip, fupdTup, List.length_cons]
    intro p hp
    cases hp with
    | head =>
      refine ⟨rfl, ?_, by simp [FVal.fresh, FKey.FLt], ExtDefGood.none, trivial⟩
      simp only [FVal.fresh, FKey.fev]
      rw [fupdTup_lt (fupd ρ b x) xs (by omega), fupd_eq]
    | tail _ hp =>
      have ih := FGood.freshFVals_only (fupd ρ b x) xs (b + 1) p hp
      rw [show b + 1 + ts.length = b + (ts.length + 1) by omega] at ih
      exact ih

theorem FGood.freshFVals {ρ : (t : Ty) → Nat → Val t} {b : Nat} {G : Ctx (FVal Val) Val}
    (hG : FGood ρ b G) {ts : List Ty} (xs : Tup Val ts) :
    FGood (fupdTup ρ b xs) (b + ts.length) (Tup.zip (freshFVals ts xs b) xs ++ G) :=
  (FGood.freshFVals_only ρ xs b).append (hG.upd_all xs)

theorem FGood.freshOne {ρ : (t : Ty) → Nat → Val t} {b : Nat} {G : Ctx (FVal Val) Val}
    (hG : FGood ρ b G) {t : Ty} (v : Val t) :
    FGood (fupd ρ b v) (b + 1) (⟨t, FVal.fresh v b, v⟩ :: G) :=
  (hG.upd_all (ts := [t]) (v, ())).cons
    ⟨rfl, by simp [FVal.fresh, FKey.fev, fupdTup, fupd_eq],
      Nat.lt_succ_self b, ExtDefGood.none, trivial⟩

def SimpAct.vals {sig : List Ty} (vs : Tup Val sig) :
    {rs : List Ty} → SimpAct sig rs → Tup Val rs
  | [], () => ()
  | _ :: _, (.imm c, act) => (c, SimpAct.vals vs act)
  | _ :: _, (.arg i, act) => (vs.get i, SimpAct.vals vs act)

theorem vals_get : {sig : List Ty} → (as : Tup (Arg Val) sig) → {u : Ty} → (i : Member u sig) →
    (vals as).get i = (as.get i).val
  | _ :: _, (_, _), _, .here => rfl
  | _ :: _, (_, bs), _, .there i => vals_get bs i

theorem ArgRel.fout_val {G : Ctx (FVal Val) Val} {ρ : (t : Ty) → Nat → Val t} {b : Nat}
    (hG : FGood ρ b G) {t : Ty} {a₁ : Arg (FVal Val) t} {a₂ : Arg Val t} :
    ArgRel G t a₁ a₂ → a₁.fout.val = a₂.val
  | .var h => (hG _ h).1
  | .imm _ => rfl

theorem ArgRel.fkey_ev {G : Ctx (FVal Val) Val} {ρ : (t : Ty) → Nat → Val t} {b : Nat}
    (hG : FGood ρ b G) {t : Ty} {a₁ : Arg (FVal Val) t} {a₂ : Arg Val t} :
    ArgRel G t a₁ a₂ → a₁.fkey.fev ρ = a₂.val
  | .var h => (hG _ h).2.1
  | .imm _ => rfl

theorem TRel.fout_vals {G : Ctx (FVal Val) Val} {ρ : (t : Ty) → Nat → Val t} {b : Nat}
    (hG : FGood ρ b G) {ts : List Ty} {as₁ : Tup (Arg (FVal Val)) ts} {as₂ : Tup (Arg Val) ts}
    (h : TRel (ArgRel G) as₁ as₂) : vals (tupMapArg (fun _ => Arg.fout) as₁) = vals as₂ :=
  TRel.tupMapArg_vals (fun _ => Arg.fout) (fun ha => ha.fout_val hG) h

theorem OpRel.fout_wp {G : Ctx (FVal Val) Val} {ρ : (t : Ty) → Nat → Val t} {b : Nat}
    (hG : FGood ρ b G) {rs : List Ty} {op₁ : Op (FVal Val) rs} {op₂ : Op Val rs}
    (ho : OpRel G op₁ op₂) {P : Tup Val rs → Prop} (hw : op₂.wp P) :
    (⟨op₁.code, tupMapArg (fun _ => Arg.fout) op₁.args⟩ : Op Val rs).wp P := by
  cases ho with
  | mk code hargs =>
    simpa only [Op.wp, TRel.fout_vals hG hargs] using hw

theorem ArgRel.fkey_FLt {G : Ctx (FVal Val) Val} {ρ : (t : Ty) → Nat → Val t} {b : Nat}
    (hG : FGood ρ b G) {t : Ty} {a₁ : Arg (FVal Val) t} {a₂ : Arg Val t} :
    ArgRel G t a₁ a₂ → a₁.fkey.FLt b
  | .var h => (hG _ h).2.2.1
  | .imm _ => trivial

theorem ArgRel.fext_good {G : Ctx (FVal Val) Val} {ρ : (t : Ty) → Nat → Val t} {b : Nat}
    (hG : FGood ρ b G) {t : Ty} {a₁ : Arg (FVal Val) t} {a₂ : Arg Val t} :
    ArgRel G t a₁ a₂ → ExtDefGood ρ b a₁.fext a₂.val
  | .var h => (hG _ h).2.2.2.1
  | .imm _ => ExtDefGood.none

theorem ArgRel.finv_good {G : Ctx (FVal Val) Val} {ρ : (t : Ty) → Nat → Val t} {b : Nat}
    (hG : FGood ρ b G) {t : Ty} {a₁ : Arg (FVal Val) t} {a₂ : Arg Val t} :
    ArgRel G t a₁ a₂ → UnInvOptGood ρ b a₁.finv a₂.val
  | .var h => (hG _ h).2.2.2.2
  | .imm _ => trivial

private theorem ArgRel.fpair_good {G : Ctx (FVal Val) Val} {ρ : (t : Ty) → Nat → Val t} {b : Nat}
    (hG : FGood ρ b G) {t : Ty} {a₁ : Arg (FVal Val) t} {a₂ : Arg Val t} :
    ArgRel G t a₁ a₂ → FValGood ρ b a₁.fpair a₂.val
  | .var hmem => hG _ hmem
  | .imm _ => ⟨rfl, rfl, trivial, ExtDefGood.none, trivial⟩

theorem FGood.apply_simpAct {G : Ctx (FVal Val) Val} {ρ : (t : Ty) → Nat → Val t} {b : Nat}
    (hG : FGood ρ b G) {sig : List Ty} {as₁ : Tup (Arg (FVal Val)) sig}
    {as₂ : Tup (Arg Val) sig} (has : TRel (ArgRel G) as₁ as₂) :
    {rs : List Ty} → (act : SimpAct sig rs) →
    FGood ρ b (Tup.zip (act.apply as₁) (SimpAct.vals (vals as₂) act) ++ G)
  | [], () => by simpa [SimpAct.apply, SimpAct.vals, Tup.zip] using hG
  | r :: rs, (elem, act) => by
    have ih := FGood.apply_simpAct hG has act
    cases elem with
    | imm c =>
      intro p hp
      cases hp with
      | head => exact ⟨rfl, rfl, trivial, ExtDefGood.none, trivial⟩
      | tail _ hp => exact ih p hp
    | arg i =>
      have hi : ArgRel G r (as₁.get i) (as₂.get i) := TRel.get i has
      intro p hp
      cases hp with
      | head =>
        simpa [SimpAct.apply, SimpAct.vals, vals_get] using hi.fpair_good hG
      | tail _ hp => exact ih p hp

theorem ArgRel.isZero {G : Ctx (FVal Val) Val} {ρ : (t : Ty) → Nat → Val t} {b : Nat}
    (hG : FGood ρ b G) {t : Ty} {a₁ : Arg (FVal Val) t} {a₂ : Arg Val t}
    (ha : ArgRel G t a₁ a₂) (hz : isZeroArg? a₁.fout = true) : a₂.val = zeroVal t :=
  (ha.fout_val hG).symm.trans (isZeroArg?_eq hz)

theorem ArgRel.isOnes {G : Ctx (FVal Val) Val} {ρ : (t : Ty) → Nat → Val t} {b : Nat}
    (hG : FGood ρ b G) {t : Ty} {a₁ : Arg (FVal Val) t} {a₂ : Arg Val t}
    (ha : ArgRel G t a₁ a₂) (ho : isOnesArg? a₁.fout = true) : a₂.val = onesVal t :=
  (ha.fout_val hG).symm.trans (isOnesArg?_eq ho)

theorem ArgRel.isOne {G : Ctx (FVal Val) Val} {ρ : (t : Ty) → Nat → Val t} {b : Nat}
    (hG : FGood ρ b G) {t : Ty} {a₁ : Arg (FVal Val) t} {a₂ : Arg Val t}
    (ha : ArgRel G t a₁ a₂) (ho : isOneArg? a₁.fout = true) : a₂.val = oneVal t :=
  (ha.fout_val hG).symm.trans (isOneArg?_eq ho)

theorem ArgRel.fout_imm?_val {G : Ctx (FVal Val) Val} {ρ : (t : Ty) → Nat → Val t} {b : Nat}
    (hG : FGood ρ b G) {t : Ty} {a₁ : Arg (FVal Val) t} {a₂ : Arg Val t}
    (ha : ArgRel G t a₁ a₂) {c : Val t} (hc : a₁.fout.imm? = some c) : a₂.val = c := by
  have hv : a₁.fout.val = c := by cases h : a₁.fout <;> simp_all [Arg.imm?]
  exact (ha.fout_val hG).symm.trans hv

theorem ArgRel.fkey_beq_val {G : Ctx (FVal Val) Val} {ρ : (t : Ty) → Nat → Val t} {b : Nat}
    (hG : FGood ρ b G) {t : Ty} {a₁ b₁ : Arg (FVal Val) t} {a₂ b₂ : Arg Val t}
    (ha : ArgRel G t a₁ a₂) (hb : ArgRel G t b₁ b₂) (heq : (a₁.fkey == b₁.fkey) = true) :
    a₂.val = b₂.val :=
  (ha.fkey_ev hG).symm.trans
    ((eq_of_beq (α := FKey t) heq ▸ rfl : a₁.fkey.fev ρ = b₁.fkey.fev ρ).trans (hb.fkey_ev hG))

private theorem SimpAct.vals_simpImms {sig : List Ty} (vs : Tup Val sig) :
    {rs : List Ty} → (res : Tup Val rs) →
    SimpAct.vals vs (simpImms (sig := sig) res) = res
  | [], () => rfl
  | _ :: _, (_, res) => congrArg (_, ·) (SimpAct.vals_simpImms vs res)

private theorem simpAct_shift_zero {G : Ctx (FVal Val) Val} {ρ : (t : Ty) → Nat → Val t}
    {b : Nat} (hG : FGood ρ b G) {t : Ty} {a₁ b₁ : Arg (FVal Val) t} {a₂ b₂ : Arg Val t}
    (ha : ArgRel G t a₁ a₂) (hb : ArgRel G t b₁ b₂)
    (f : ∀ {n}, BitVec n → BitVec n → BitVec n)
    (hf : ∀ {n} (x : BitVec n), f x 0#n = x) (hf0 : ∀ {n} (y : BitVec n), f 0#n y = 0#n)
    {act : SimpAct [t, t] [t]}
    (hact : (if t.hasFloat then none
      else if isZeroArg? b₁.fout then some (.arg .here, ())
      else if isZeroArg? a₁.fout then some (.imm (zeroVal t), ()) else none) = some act)
    {P : Tup Val [t] → Prop}
    (hw : if t.hasFloat then False else P (lift2 f (fun x _ => x) t a₂.val b₂.val, ())) :
    P (SimpAct.vals (vals (a₂, b₂, ())) act) := by
  split at hact
  · cases hact
  · next hnf =>
    have hnf0 : t.hasFloat = false := Bool.eq_false_iff.mpr hnf
    split at hact
    · cases hact; next hbz =>
      have hsh := lift2_law false f (fun x _ => x) (fun _ x => x) (fun t _ => zeroVal t)
        (fun _ x => x) t (fun _ => hnf0) a₂.val (fun x => hf x) (hbool := fun _ => rfl)
      simpa [SimpAct.vals, Tup.get, hnf0, vals, hb.isZero hG hbz, hsh] using hw
    · split at hact
      · cases hact; next haz =>
        have hsh := lift2_law false f (fun x _ => x) (fun t _ => zeroVal t) (fun _ x => x)
          (fun t _ => zeroVal t) t (fun _ => hnf0) b₂.val (fun y => hf0 y)
          (hbool := fun _ => rfl)
        simpa [SimpAct.vals, hnf0, vals, ha.isZero hG haz, hsh] using hw
      · cases hact

private theorem simpAct_bin_zero_add {G : Ctx (FVal Val) Val} {ρ : (t : Ty) → Nat → Val t}
    {b : Nat} (hG : FGood ρ b G) {t : Ty} {a₁ b₁ : Arg (FVal Val) t} {a₂ b₂ : Arg Val t}
    (ha : ArgRel G t a₁ a₂) (hb : ArgRel G t b₁ b₂) (fbv : ∀ {n}, BitVec n → BitVec n → BitVec n)
    (fbool : Bool → Bool → Bool) (allowFlt : Bool) (hnf : allowFlt = false → t.hasFloat = false)
    {act : SimpAct [t, t] [t]}
    (hact : (if isZeroArg? b₁.fout then some (.arg .here, ())
      else if isZeroArg? a₁.fout then some (.arg (.there .here), ()) else none) = some act)
    {P : Tup Val [t] → Prop} (hw : P (lift2 fbv fbool t a₂.val b₂.val, ()))
    (hbvr : ∀ {n} (x : BitVec n), fbv x 0#n = x := by intro; simp)
    (hbvl : ∀ {n} (x : BitVec n), fbv 0#n x = x := by intro; simp)
    (hboolr : ∀ x, fbool x false = x := by intro x; cases x <;> rfl)
    (hbooll : ∀ x, fbool false x = x := by intro x; cases x <;> rfl)
    (hfltr : ∀ {f : Fmt} (x : BitVec f.width), allowFlt = true → fbv x 0#f.width = x := by
      intro _ _ h; cases h)
    (hfltl : ∀ {f : Fmt} (x : BitVec f.width), allowFlt = true → fbv 0#f.width x = x := by
      intro _ _ h; cases h) :
    P (SimpAct.vals (vals (a₂, b₂, ())) act) := by
  split at hact
  · cases hact; next hbz =>
    have h := lift2_law allowFlt fbv fbool (fun _ x => x) (fun t _ => zeroVal t) (fun _ x => x)
      t hnf a₂.val (by intros; exact hbvr _) hfltr hboolr
    simpa [SimpAct.vals, Tup.get, vals, hb.isZero hG hbz, h] using hw
  · split at hact
    · cases hact; next haz =>
      have h := lift2_law allowFlt fbv fbool (fun t _ => zeroVal t) (fun _ x => x) (fun _ x => x)
        t hnf b₂.val (by intros; exact hbvl _) hfltl hbooll
      simpa [SimpAct.vals, Tup.get, vals, ha.isZero hG haz, h] using hw
    · cases hact

private theorem simpAct_bitwise {G : Ctx (FVal Val) Val} {ρ : (t : Ty) → Nat → Val t} {b : Nat}
    (hG : FGood ρ b G) {t : Ty} {a₁ b₁ : Arg (FVal Val) t} {a₂ b₂ : Arg Val t}
    (ha : ArgRel G t a₁ a₂) (hb : ArgRel G t b₁ b₂)
    (fbv : ∀ {n}, BitVec n → BitVec n → BitVec n) (fbool : Bool → Bool → Bool)
    (pArg qArg : Arg Val t → Bool) (kVal : (u : Ty) → Val u)
    (hpEq : ∀ {a : Arg Val t}, pArg a = true → a.val = kVal t)
    (hqEq : ∀ {a : Arg Val t},
      qArg a = true → a.val = (if kVal .bool then zeroVal t else onesVal t))
    (hpL : ∀ x : Val t, lift2 fbv fbool t (kVal t) x = kVal t)
    (hpR : ∀ x : Val t, lift2 fbv fbool t x (kVal t) = kVal t)
    (hqR : ∀ x : Val t, lift2 fbv fbool t x (if kVal .bool then zeroVal t else onesVal t) = x)
    (hqL : ∀ x : Val t, lift2 fbv fbool t (if kVal .bool then zeroVal t else onesVal t) x = x)
    (hself : ∀ x : Val t, lift2 fbv fbool t x x = x)
    {act : SimpAct [t, t] [t]}
    (hact : (if pArg a₁.fout || pArg b₁.fout then some (.imm (kVal t), ())
      else if qArg b₁.fout then some (.arg .here, ())
      else if qArg a₁.fout then some (.arg (.there .here), ())
      else if a₁.fkey == b₁.fkey then some (.arg .here, ()) else none) = some act)
    {P : Tup Val [t] → Prop} (hw : P (lift2 fbv fbool t a₂.val b₂.val, ())) :
    P (SimpAct.vals (vals (a₂, b₂, ())) act) := by
  split at hact
  · rename_i hor; cases hact
    rcases Bool.or_eq_true_iff.1 hor with haz | hbz
    · simpa [SimpAct.vals, vals, (ha.fout_val hG).symm.trans (hpEq haz), hpL] using hw
    · simpa [SimpAct.vals, vals, (hb.fout_val hG).symm.trans (hpEq hbz), hpR] using hw
  · split at hact
    · cases hact; next hbo =>
      simpa [SimpAct.vals, Tup.get, vals, (hb.fout_val hG).symm.trans (hqEq hbo), hqR] using hw
    · split at hact
      · cases hact; next hao =>
        simpa [SimpAct.vals, Tup.get, vals, (ha.fout_val hG).symm.trans (hqEq hao), hqL] using hw
      · split at hact
        · cases hact; next heq =>
          simpa [SimpAct.vals, Tup.get, vals, ha.fkey_beq_val hG hb heq, hself] using hw
        · cases hact

private theorem simpAct_mulw_zero {G : Ctx (FVal Val) Val} {ρ : (t : Ty) → Nat → Val t}
    {b : Nat} (hG : FGood ρ b G) {n : Nat} {a₁ b₁ : Arg (FVal Val) (.bits n)}
    {a₂ b₂ : Arg Val (.bits n)} (ha : ArgRel G (.bits n) a₁ a₂) (hb : ArgRel G (.bits n) b₁ b₂)
    {act : SimpAct [.bits n, .bits n] [.bits n, .bits n]}
    (hact : (if isZeroArg? a₁.fout || isZeroArg? b₁.fout then some (.imm 0#n, .imm 0#n, ())
      else none) = some act)
    (hi : BitVec n → BitVec n → BitVec n)
    (hhi0l : ∀ y, hi 0#n y = 0#n) (hhi0r : ∀ x, hi x 0#n = 0#n)
    {P : Tup Val [.bits n, .bits n] → Prop}
    (hw : P (a₂.val * b₂.val, hi a₂.val b₂.val, ())) :
    P (SimpAct.vals (vals (a₂, b₂, ())) act) := by
  split at hact
  · rename_i hor; cases hact
    rcases Bool.or_eq_true_iff.1 hor with haz | hbz
    · simpa [SimpAct.vals, vals, ha.isZero hG haz, zeroVal, hhi0l] using hw
    · simpa [SimpAct.vals, vals, hb.isZero hG hbz, zeroVal, hhi0r] using hw
  · cases hact

private theorem simpAct_div_one {G : Ctx (FVal Val) Val} {ρ : (t : Ty) → Nat → Val t}
    {b : Nat} (hG : FGood ρ b G) {n k : Nat} {b₁ : Arg (FVal Val) (.bits n)}
    {a₂ b₂ : Arg Val (.bits n)} (hb : ArgRel G (.bits n) b₁ b₂)
    {act : SimpAct [.bits n, .bits n] [.bits n]} {res : SimpElem (.bits n) [.bits n, .bits n]}
    (hact : (if k < n && (b₁.fout.imm? == some 1#n) then some (res, ()) else none) = some act)
    (op : BitVec n → BitVec n → BitVec n)
    (hop : k < n →
      (op a₂.val 1#n, ()) = SimpAct.vals (rs := [.bits n]) (vals (a₂, b₂, ())) (res, ()))
    {P : Tup Val [.bits n] → Prop} (hw : P (op a₂.val b₂.val, ())) :
    P (SimpAct.vals (vals (a₂, b₂, ())) act) := by
  split at hact
  · rename_i hc; cases hact; simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
    rw [hb.fout_imm?_val hG hc.2, hop hc.1] at hw; exact hw
  · cases hact

private theorem CmpOp.isRefl_swap (o : CmpOp) : o.swap.isRefl = o.isRefl := by
  cases o <;> rfl

private theorem CmpOp.isRefl_toUnsigned (o : CmpOp) : o.toUnsigned.isRefl = o.isRefl := by
  cases o <;> rfl

private def NarrowCmpOk (ρ : (t : Ty) → Nat → Val t) {n : Nat} (o : CmpOp)
    (a₂ b₂ : Arg Val (.bits n)) (nc : NarrowCmp Val) : Prop :=
  nc.op.evalBits nc.lhs.val nc.rhs.val = o.evalBits a₂.val b₂.val ∧
  nc.lhsKey.fev ρ = nc.lhs.val ∧ nc.rhsKey.fev ρ = nc.rhs.val ∧ nc.op.isRefl = o.isRefl

private theorem narrowCmpCore_sound {G : Ctx (FVal Val) Val} {ρ : (t : Ty) → Nat → Val t} {b : Nat}
    (hG : FGood ρ b G) {n : Nat} (o : CmpOp)
    {a₁ b₁ : Arg (FVal Val) (.bits n)} {a₂ b₂ : Arg Val (.bits n)}
    (ha : ArgRel G (.bits n) a₁ a₂) (hb : ArgRel G (.bits n) b₁ b₂) :
    NarrowCmpOk ρ o a₂ b₂ (narrowCmpCore o n a₁ b₁) := by
  have hbase : NarrowCmpOk ρ o a₂ b₂ ⟨n, o, a₁.fout, b₁.fout, a₁.fkey, b₁.fkey⟩ := by
    dsimp only [NarrowCmpOk]
    rw [ha.fout_val hG, hb.fout_val hG, ha.fkey_ev hG, hb.fkey_ev hG]
    exact ⟨rfl, rfl, rfl, rfl⟩
  have hea := ha.fext_good hG
  have heb := hb.fext_good hG
  dsimp only [narrowCmpCore]
  cases hfa : a₁.fext with
  | none => exact hbase
  | some ea =>
    rw [hfa] at hea
    rcases ea with ⟨ka, ma, hposa, hlta, sxa, ska⟩
    cases himmb : b₁.fout.imm? with
    | some c =>
      have hbc := hb.fout_imm?_val hG himmb
      cases ka with
      | sext =>
        dsimp only [BitsExtGood, ExtDefGood] at hea ⊢
        split
        · rename_i hfit
          have hceq : (c.setWidth ma).signExtend n = c := eq_of_beq hfit
          refine ⟨?_, hea.2.1, rfl, rfl⟩
          simp only [Arg.val_imm]
          rw [hea.1, hbc, ← (cmpOp_evalBits_signExtend hlta o sxa.val (c.setWidth ma)), hceq]
        · exact hbase
      | zext =>
        dsimp only [BitsExtGood, ExtDefGood] at hea ⊢
        split
        · rename_i hfit
          have hceq : (c.setWidth ma).setWidth n = c := eq_of_beq hfit
          refine ⟨?_, hea.2.1, rfl, CmpOp.isRefl_toUnsigned o⟩
          simp only [Arg.val_imm]
          rw [hea.1, hbc, ← (cmpOp_evalBits_setWidth hlta o sxa.val (c.setWidth ma)), hceq]
        · exact hbase
    | none =>
      cases hfb : b₁.fext with
      | none => exact hbase
      | some eb =>
        rw [hfb] at heb
        rcases eb with ⟨kb, mb, hposb, hltb, syb, skb⟩
        cases ka <;> cases kb
        · dsimp only [BitsExtGood, ExtDefGood] at hea heb ⊢
          split
          · rename_i hm; subst hm
            refine ⟨?_, hea.2.1, heb.2.1, rfl⟩
            rw [hea.1, heb.1, cmpOp_evalBits_signExtend hlta]
          · exact hbase
        · exact hbase
        · exact hbase
        · dsimp only [BitsExtGood, ExtDefGood] at hea heb ⊢
          split
          · rename_i hm; subst hm
            refine ⟨?_, hea.2.1, heb.2.1, CmpOp.isRefl_toUnsigned o⟩
            rw [hea.1, heb.1, cmpOp_evalBits_setWidth hlta]
          · exact hbase

theorem narrowCmp_sound {G : Ctx (FVal Val) Val} {ρ : (t : Ty) → Nat → Val t} {b : Nat}
    (hG : FGood ρ b G) {n : Nat} (o : CmpOp)
    {a₁ b₁ : Arg (FVal Val) (.bits n)} {a₂ b₂ : Arg Val (.bits n)}
    (ha : ArgRel G (.bits n) a₁ a₂) (hb : ArgRel G (.bits n) b₁ b₂) :
    let nc := narrowCmp o n a₁ b₁
    nc.op.evalBits nc.lhs.val nc.rhs.val = o.evalBits a₂.val b₂.val ∧
    nc.lhsKey.fev ρ = nc.lhs.val ∧ nc.rhsKey.fev ρ = nc.rhs.val ∧ nc.op.isRefl = o.isRefl := by
  dsimp only [narrowCmp]
  cases a₁.fout.imm? <;> cases b₁.fout.imm?
  · exact narrowCmpCore_sound hG o ha hb
  · exact narrowCmpCore_sound hG o ha hb
  · obtain ⟨hev, hlk, hrk, hrefl⟩ := narrowCmpCore_sound hG o.swap hb ha
    exact ⟨hev.trans (CmpOp.swap_evalBits o a₂.val b₂.val), hlk, hrk,
      hrefl.trans (CmpOp.isRefl_swap o)⟩
  · exact narrowCmpCore_sound hG o ha hb

private theorem arg_imm?_val {t : Ty} {a : Arg Val t} {c : Val t}
    (h : a.imm? = some c) : a.val = c := by
  cases a <;> simp_all [Arg.imm?]

theorem OpRel.simpAct_sound {G : Ctx (FVal Val) Val} {ρ : (t : Ty) → Nat → Val t} {b : Nat}
    (hG : FGood ρ b G) {sig rs : List Ty} {code : OpCode sig rs}
    {args₁ : Tup (Arg (FVal Val)) sig} {args₂ : Tup (Arg Val) sig}
    (hargs : TRel (ArgRel G) args₁ args₂) {act : SimpAct sig rs}
    (hact : ({ code := code, args := args₁ } : Op (FVal Val) rs).simpAct = some act)
    {P : Tup Val rs → Prop} (hw : code.wp (vals args₂) P) :
    P (SimpAct.vals (vals args₂) act) ∧
      FGood ρ b (Tup.zip (act.apply args₁) (SimpAct.vals (vals args₂) act) ++ G) := by
  have hfg := FGood.apply_simpAct hG hargs act
  refine ⟨?_, hfg⟩
  delta Op.simpAct at hact
  dsimp only at hact
  cases hconst : (tupImms? (tupMapArg (fun _ => Arg.fout) args₁)).bind code.eval? with
    | some res =>
      rw [hconst] at hact; cases hact
      simp only [Option.bind_eq_some_iff] at hconst
      rcases hconst with ⟨cs, hcs, hev⟩
      have hvals : vals args₂ = cs := (TRel.fout_vals hG hargs).symm.trans (tupImms?_vals hcs)
      rw [SimpAct.vals_simpImms]
      exact code.eval?_sound (vals args₂) P (by rw [hvals]; exact hev) hw
    | none =>
      rw [hconst] at hact; dsimp only at hact
      cases code with
      | copy _ => rcases hargs with _ | ⟨ha, _⟩; cases hact; exact hw
      | add t =>
        rcases args₂ with ⟨a₂, b₂, ⟨⟩⟩; rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩; dsimp only at hact
        split at hact
        · cases hact
        · rename_i hnf; have hf0 : t.hasFloat = false := Bool.eq_false_iff.mpr hnf
          exact simpAct_bin_zero_add hG ha hb (· + ·) (· ^^ ·) false (fun _ => hf0) hact
            (by simpa [OpCode.wp_add, hf0, vals] using hw)
      | sub t =>
        rcases args₂ with ⟨a₂, b₂, ⟨⟩⟩; rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩; dsimp only at hact
        split at hact
        · cases hact
        · rename_i hnf; have hf0 : t.hasFloat = false := Bool.eq_false_iff.mpr hnf
          split at hact
          · cases hact; next heq =>
            have h := lift2_law false (· - ·) (· ^^ ·) (fun _ x => x) (fun _ x => x)
              (fun t _ => zeroVal t) t (fun _ => hf0) b₂.val
            simpa [SimpAct.vals, OpCode.wp_sub, hf0, vals, ha.fkey_beq_val hG hb heq, h] using hw
          · split at hact
            · cases hact; next hbz =>
              have h := lift2_law false (· - ·) (· ^^ ·) (fun _ x => x) (fun t _ => zeroVal t)
                (fun _ x => x) t (fun _ => hf0) a₂.val
              simpa [SimpAct.vals, Tup.get, OpCode.wp_sub, hf0, vals, hb.isZero hG hbz, h] using hw
            · cases hact
      | mul t =>
        rcases args₂ with ⟨a₂, b₂, ⟨⟩⟩; rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩; dsimp only at hact
        split at hact
        · cases hact
        · rename_i hnf; have hf0 : t.hasFloat = false := Bool.eq_false_iff.mpr hnf
          split at hact
          · rename_i hor0; cases hact
            rcases Bool.or_eq_true_iff.1 hor0 with haz | hbz
            · have h := lift2_law false (· * ·) (· && ·) (fun t _ => zeroVal t) (fun _ x => x)
                (fun t _ => zeroVal t) t (fun _ => hf0) b₂.val
              simpa [SimpAct.vals, OpCode.wp_mul, hf0, vals, ha.isZero hG haz, h] using hw
            · have h := lift2_law false (· * ·) (· && ·) (fun _ x => x) (fun t _ => zeroVal t)
                (fun t _ => zeroVal t) t (fun _ => hf0) a₂.val
              simpa [SimpAct.vals, OpCode.wp_mul, hf0, vals, hb.isZero hG hbz, h] using hw
          · split at hact
            · cases hact; next hbo =>
              have h := lift2_law false (· * ·) (· && ·) (fun _ x => x) (fun t _ => oneVal t)
                (fun _ x => x) t (fun _ => hf0) a₂.val
              simpa [SimpAct.vals, Tup.get, OpCode.wp_mul, hf0, vals, hb.isOne hG hbo, h] using hw
            · split at hact
              · cases hact; next hao =>
                have h := lift2_law false (· * ·) (· && ·) (fun t _ => oneVal t) (fun _ x => x)
                  (fun _ x => x) t (fun _ => hf0) b₂.val
                simpa [SimpAct.vals, Tup.get, OpCode.wp_mul, hf0, vals, ha.isOne hG hao, h] using hw
              · cases hact
      | neg t =>
        cases t with | bool => rcases hargs with _ | ⟨_, _⟩; cases hact; exact hw | _ => cases hact
      | and t =>
        rcases args₂ with ⟨a₂, b₂, ⟨⟩⟩; rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩; dsimp only at hact
        exact simpAct_bitwise hG ha hb (· &&& ·) (· && ·) isZeroArg? isOnesArg? zeroVal
          isZeroArg?_eq isOnesArg?_eq
          (fun x => lift2_law true (· &&& ·) (· && ·) (fun t _ => zeroVal t) (fun _ y => y)
            (fun t _ => zeroVal t) t (fun h => by cases h) x (hflt := fun _ _ => by simp [zeroVal]))
          (fun x => lift2_law true (· &&& ·) (· && ·) (fun _ y => y) (fun t _ => zeroVal t)
            (fun t _ => zeroVal t) t (fun h => by cases h) x (hflt := fun _ _ => by simp [zeroVal]))
          (fun x => lift2_law true (· &&& ·) (· && ·) (fun _ y => y) (fun t _ => onesVal t)
            (fun _ y => y) t (fun h => by cases h) x (hflt := fun _ _ => by simp [onesVal]))
          (fun x => lift2_law true (· &&& ·) (· && ·) (fun t _ => onesVal t) (fun _ y => y)
            (fun _ y => y) t (fun h => by cases h) x (hflt := fun _ _ => by simp [onesVal]))
          (fun x => lift2_law true (· &&& ·) (· && ·) (fun _ y => y) (fun _ y => y)
            (fun _ y => y) t (fun h => by cases h) x (hflt := fun _ _ => by simp))
          hact (by simpa [OpCode.wp_and, vals] using hw)
      | or t =>
        rcases args₂ with ⟨a₂, b₂, ⟨⟩⟩; rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩; dsimp only at hact
        exact simpAct_bitwise hG ha hb (· ||| ·) (· || ·) isOnesArg? isZeroArg? onesVal
          isOnesArg?_eq isZeroArg?_eq
          (fun x => lift2_law true (· ||| ·) (· || ·) (fun t _ => onesVal t) (fun _ y => y)
            (fun t _ => onesVal t) t (fun h => by cases h) x (hflt := fun _ _ => by simp [onesVal]))
          (fun x => lift2_law true (· ||| ·) (· || ·) (fun _ y => y) (fun t _ => onesVal t)
            (fun t _ => onesVal t) t (fun h => by cases h) x (hflt := fun _ _ => by simp [onesVal]))
          (fun x => lift2_law true (· ||| ·) (· || ·) (fun _ y => y) (fun t _ => zeroVal t)
            (fun _ y => y) t (fun h => by cases h) x (hflt := fun _ _ => by simp [zeroVal]))
          (fun x => lift2_law true (· ||| ·) (· || ·) (fun t _ => zeroVal t) (fun _ y => y)
            (fun _ y => y) t (fun h => by cases h) x (hflt := fun _ _ => by simp [zeroVal]))
          (fun x => lift2_law true (· ||| ·) (· || ·) (fun _ y => y) (fun _ y => y)
            (fun _ y => y) t (fun h => by cases h) x (hflt := fun _ _ => by simp))
          hact (by simpa [OpCode.wp_or, vals] using hw)
      | xor t =>
        rcases args₂ with ⟨a₂, b₂, ⟨⟩⟩; rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩; dsimp only at hact
        split at hact
        · cases hact; next heq =>
          have h := lift2_law true (· ^^^ ·) (· ^^ ·) (fun _ x => x) (fun _ x => x)
            (fun t _ => zeroVal t) t (fun h => by cases h) b₂.val
            (hflt := fun _ _ => by simp [zeroVal])
          simpa [SimpAct.vals, OpCode.wp_xor, vals, ha.fkey_beq_val hG hb heq, h] using hw
        · exact simpAct_bin_zero_add hG ha hb (· ^^^ ·) (· ^^ ·) true (fun h => by cases h) hact
            (by simpa [OpCode.wp_xor, vals] using hw)
            (hfltr := fun _ _ => by simp) (hfltl := fun _ _ => by simp)
      | ternlog t imm =>
        rcases args₂ with ⟨a₂, b₂, c₂, ⟨⟩⟩
        rcases hargs with _ | ⟨ha, _ | ⟨hb, _ | ⟨hc, _⟩⟩⟩; dsimp only at hact
        have hw' : P (lift3 (fun x y z => ternaryLogic x y z imm)
            (fun x y z => ternaryLogicBool x y z imm) t a₂.val b₂.val c₂.val, ()) := by
          simpa [OpCode.wp_ternlog, vals] using hw
        split at hact
        · next h => cases hact; exact ternlog_simp_wp imm 0#8 h (fun t _ _ _ => zeroVal t) hw'
        · split at hact
          · next h => cases hact; exact ternlog_simp_wp imm 0xff#8 h (fun t _ _ _ => onesVal t) hw'
          · split at hact
            · next h => cases hact; exact ternlog_simp_wp imm 0xf0#8 h (fun _ a _ _ => a) hw'
            · split at hact
              · next h => cases hact; exact ternlog_simp_wp imm 0xcc#8 h (fun _ _ b _ => b) hw'
              · split at hact
                · next h => cases hact; exact ternlog_simp_wp imm 0xaa#8 h (fun _ _ _ c => c) hw'
                · cases hact
      | shl t =>
        rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩; dsimp only at hact
        exact simpAct_shift_zero hG ha hb (fun {n} x y => x <<< (y.toNat % n))
          (fun x => by simp) (fun y => by simp)
          hact (by simpa [OpCode.wp_shl, vals] using hw)
      | lshr t =>
        rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩; dsimp only at hact
        exact simpAct_shift_zero hG ha hb (fun {n} x y => x >>> (y.toNat % n))
          (fun x => by simp) (fun y => by simp)
          hact (by simpa [OpCode.wp_lshr, vals] using hw)
      | ashr t =>
        rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩; dsimp only at hact
        exact simpAct_shift_zero hG ha hb (fun {n} x y => x.sshiftRight (y.toNat % n))
          (fun x => by simp) (fun y => by simp [BitVec.zero_sshiftRight])
          hact (by simpa [OpCode.wp_ashr, vals] using hw)
      | rotl t =>
        rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩; dsimp only at hact
        exact simpAct_shift_zero hG ha hb (fun {n} x y => x.rotateLeft (y.toNat % n))
          (fun x => by ext i _; simp [BitVec.rotateLeft, BitVec.rotateLeftAux])
          (fun y => by ext i _; simp [BitVec.rotateLeft, BitVec.rotateLeftAux])
          hact (by simpa [OpCode.wp_rotl, vals] using hw)
      | rotr t =>
        rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩; dsimp only at hact
        exact simpAct_shift_zero hG ha hb (fun {n} x y => x.rotateRight (y.toNat % n))
          (fun x => by ext i _; simp [BitVec.rotateRight, BitVec.rotateRightAux])
          (fun y => by ext i _; simp [BitVec.rotateRight, BitVec.rotateRightAux])
          hact (by simpa [OpCode.wp_rotr, vals] using hw)
      | cmp o t _ h =>
        subst h
        rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, ⟨⟩⟩
        rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩
        cases t with
        | bits n =>
          obtain ⟨hev, hlk, hrk, hrefl⟩ := narrowCmp_sound hG o ha hb
          dsimp only at hact hev hlk hrk hrefl
          split at hact
          · rename_i heq; cases hact
            have hveq : (narrowCmp o n a₁ b₁).lhs.val = (narrowCmp o n a₁ b₁).rhs.val :=
              hlk.symm.trans ((congrArg (FKey.fev ρ) (eq_of_beq heq)).trans hrk)
            simp only [SimpAct.vals, OpCode.wp_cmp, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte,
              liftCmp, vals, cast_eq] at hw ⊢
            rw [← hev, hveq, cmpOp_evalBits_self, hrefl] at hw
            exact hw
          · cases hbd : (narrowCmp o n a₁ b₁).rhs.imm?.bind
                (cmpImmBound? (narrowCmp o n a₁ b₁).op (narrowCmp o n a₁ b₁).w) with
            | none => rw [hbd] at hact; cases hact
            | some res =>
              rw [hbd] at hact; cases hact
              simp only [Option.bind_eq_some_iff] at hbd
              rcases hbd with ⟨c, hc, hres⟩
              have hrv := arg_imm?_val hc
              simp only [SimpAct.vals, OpCode.wp_cmp, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte,
                liftCmp, vals, cast_eq] at hw ⊢
              rw [← hev, hrv, cmpImmBound?_sound _ _ _ hres] at hw
              exact hw
        | float _ =>
          simp [OpCode.wp_cmp, Ty.hasFloat] at hw
        | bool =>
          dsimp only at hact
          split at hact
          · rename_i heq; cases hact
            have hveq := ha.fkey_beq_val hG hb heq
            simpa [SimpAct.vals, OpCode.wp_cmp, Ty.hasFloat, vals, hveq,
              liftCmp_self o .bool _ rfl] using hw
          · cases hact
        | pair _ _ =>
          dsimp only at hact
          split at hact
          · rename_i hcond; cases hact
            simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcond
            have hveq := ha.fkey_beq_val hG hb hcond.2
            simpa [SimpAct.vals, Tup.get, OpCode.wp_cmp, hcond.1, vals, hveq,
              liftCmp_self o _ _ hcond.1] using hw
          · cases hact
      | select t =>
        rcases args₁ with ⟨c₁, a₁, b₁, ⟨⟩⟩; rcases args₂ with ⟨c₂, a₂, b₂, ⟨⟩⟩
        rcases hargs with _ | ⟨hc, _ | ⟨ha, _ | ⟨hb, _⟩⟩⟩; dsimp only at hact
        cases hci : c₁.fout.imm? with
        | some b =>
          rw [hci] at hact
          have hcv := hc.fout_imm?_val hG hci
          cases b <;> cases hact <;>
            simpa [SimpAct.vals, Tup.get, OpCode.wp_select, vals, hcv] using hw
        | none =>
          rw [hci] at hact; dsimp only at hact
          split at hact
          · rename_i heq; cases hact
            have hveq := ha.fkey_beq_val hG hb heq
            simpa [SimpAct.vals, Tup.get, OpCode.wp_select, vals, hveq] using hw
          · cases t with
            | bool =>
              dsimp only at hact
              split at hact
              · rename_i htf; cases hact
                simp only [Bool.and_eq_true, beq_iff_eq] at htf
                have hav := ha.fout_imm?_val hG htf.1
                have hbv := hb.fout_imm?_val hG htf.2
                simpa [SimpAct.vals, Tup.get, OpCode.wp_select, vals, hav, hbv] using hw
              · cases hact
            | _ => cases hact
      | blend t _ h =>
        subst h; rcases args₁ with ⟨c₁, a₁, b₁, ⟨⟩⟩; rcases args₂ with ⟨c₂, a₂, b₂, ⟨⟩⟩
        rcases hargs with _ | ⟨hc, _ | ⟨ha, _ | ⟨hb, _⟩⟩⟩; dsimp only at hact
        cases hci : c₁.fout.imm? with
        | some mc =>
          rw [hci] at hact; dsimp only at hact
          have hcv := hc.fout_imm?_val hG hci
          split at hact
          · rename_i ht; cases hact; have hm := eq_of_beq ht; simp only [cast_eq] at hm
            simpa [SimpAct.vals, Tup.get, OpCode.wp_blend, vals, hcv, hm,
              blendV_splatMask_true] using hw
          · split at hact
            · rename_i hf; cases hact; have hm := eq_of_beq hf; simp only [cast_eq] at hm
              simpa [SimpAct.vals, Tup.get, OpCode.wp_blend, vals, hcv, hm,
                blendV_splatMask_false] using hw
            · split at hact
              · rename_i heq; cases hact
                have hveq := ha.fkey_beq_val hG hb heq
                simpa [SimpAct.vals, Tup.get, OpCode.wp_blend, vals, hveq, blendV_self] using hw
              · cases hact
        | none =>
          rw [hci] at hact; dsimp only at hact
          split at hact
          · rename_i heq; cases hact
            have hveq := ha.fkey_beq_val hG hb heq
            simpa [SimpAct.vals, Tup.get, OpCode.wp_blend, vals, hveq, blendV_self] using hw
          · cases hact
      | zext m n | trunc m n =>
        rcases hargs with _ | ⟨ha, _⟩; dsimp only at hact
        split at hact
        · rename_i hmn; subst hmn; cases hact
          dsimp only [OpCode.wp] at hw
          simp only [SimpAct.vals, Tup.get, vals, cast_eq, BitVec.setWidth_eq] at hw ⊢
          exact hw.2
        · cases hact
      | sext m n =>
        rcases hargs with _ | ⟨ha, _⟩; dsimp only at hact
        split at hact
        · rename_i hmn; subst hmn; cases hact
          simp only [SimpAct.vals, Tup.get, OpCode.wp_sext, vals, cast_eq,
            signExtend_self] at hw ⊢
          exact hw.2
        · cases hact
      | addc n =>
        rcases hargs with _ | ⟨ha, _ | ⟨hb, _ | ⟨hc, _⟩⟩⟩; dsimp only at hact
        split at hact
        · rename_i hcf
          have hc0 := hc.fout_imm?_val hG (eq_of_beq hcf)
          split at hact
          · rename_i hbz; cases hact
            have hb0 := hb.isZero hG hbz
            simp only [SimpAct.vals, Tup.get, OpCode.wp_addc, vals, hc0, hb0, zeroVal,
              Bool.toNat_false, BitVec.add_zero, BitVec.toNat_ofNat,
              Nat.zero_mod, Nat.add_zero] at hw ⊢
            simpa [Nat.not_le_of_lt (BitVec.isLt _)] using hw
          · split at hact
            · rename_i haz; cases hact
              have ha0 := ha.isZero hG haz
              simp only [SimpAct.vals, Tup.get, OpCode.wp_addc, vals, hc0, ha0, zeroVal,
                Bool.toNat_false, BitVec.zero_add, BitVec.add_zero,
                BitVec.toNat_ofNat, Nat.zero_mod, Nat.zero_add, Nat.add_zero] at hw ⊢
              simpa [Nat.not_le_of_lt (BitVec.isLt _)] using hw
            · cases hact
        · cases hact
      | subb n =>
        rcases hargs with _ | ⟨ha, _ | ⟨hb, _ | ⟨hc, _⟩⟩⟩; dsimp only at hact
        split at hact
        · rename_i hcf
          have hc0 := hc.fout_imm?_val hG (eq_of_beq hcf)
          split at hact
          · rename_i hbz; cases hact
            have hb0 := hb.isZero hG hbz
            simpa [SimpAct.vals, Tup.get, OpCode.wp_subb, vals, hc0, hb0, zeroVal] using hw
          · split at hact
            · rename_i heq; cases hact
              have hveq := ha.fkey_beq_val hG hb heq
              simpa [SimpAct.vals, Tup.get, OpCode.wp_subb, vals, hc0, hveq] using hw
            · cases hact
        · cases hact
      | umulw n =>
        rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩; dsimp only at hact
        exact simpAct_mulw_zero hG ha hb hact
          (fun x y => BitVec.ofNat n (x.toNat * y.toNat / 2 ^ n))
          (fun _ => by simp) (fun _ => by simp)
          (by simpa [OpCode.wp_umulw, vals] using hw)
      | smulw n =>
        rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩; dsimp only at hact
        exact simpAct_mulw_zero hG ha hb hact
          (fun x y => (BitVec.ofInt (n + n) (x.toInt * y.toInt)).extractLsb' n n)
          (fun _ => by simp [BitVec.toInt_zero]) (fun _ => by simp [BitVec.toInt_zero])
          (by simpa [OpCode.wp_smulw, vals] using hw)
      | udiv n =>
        rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩; dsimp only at hact
        exact simpAct_div_one hG hb hact (· / ·)
          (fun hk => by simp [SimpAct.vals, Tup.get, vals, div_one_of_pos hk])
          (by simpa [OpCode.wp_udiv, vals] using hw.2)
      | sdiv n =>
        rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩; dsimp only at hact
        exact simpAct_div_one hG hb hact BitVec.sdiv
          (fun hk => by simp [SimpAct.vals, Tup.get, vals, sdiv_one_of_one_lt hk])
          (by simpa [OpCode.wp_sdiv, vals] using hw.2)
      | urem n =>
        rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩; dsimp only at hact
        exact simpAct_div_one hG hb hact (· % ·)
          (fun hk => by simp [SimpAct.vals, mod_one_of_pos hk])
          (by simpa [OpCode.wp_urem, vals] using hw.2)
      | srem n =>
        rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩; dsimp only at hact
        exact simpAct_div_one hG hb hact BitVec.srem
          (fun hk => by simp [SimpAct.vals, srem_one_of_one_lt hk])
          (by simpa [OpCode.wp_srem, vals] using hw.2)
      | udiv0 n =>
        rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩; dsimp only at hact
        split at hact
        · rename_i hbz; cases hact
          have hb0 := hb.fout_imm?_val hG (eq_of_beq hbz)
          simpa [SimpAct.vals, Tup.get, OpCode.wp_udiv0, vals, hb0] using hw
        · exact simpAct_div_one hG hb hact (fun x y => if y = 0 then 0 else x / y)
            (fun hk => by
              simp [one_ne_zero_of_pos hk, div_one_of_pos hk, SimpAct.vals, Tup.get, vals])
            (by simpa [OpCode.wp_udiv0, vals] using hw)
      | sdiv0 n =>
        rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩; dsimp only at hact
        split at hact
        · rename_i hbz; cases hact
          have hb0 := hb.fout_imm?_val hG (eq_of_beq hbz)
          simpa [SimpAct.vals, Tup.get, OpCode.wp_sdiv0, vals, hb0] using hw
        · exact simpAct_div_one hG hb hact (fun x y => if y = 0 then 0 else x.sdiv y)
            (fun hk => by
              simp [one_ne_zero_of_pos (by omega : 0 < n), sdiv_one_of_one_lt hk,
                SimpAct.vals, Tup.get, vals])
            (by simpa [OpCode.wp_sdiv0, vals] using hw)
      | bitcast t u h =>
        rcases hargs with _ | ⟨ha, _⟩; dsimp only at hact
        cases hdec : tyDecEq t u with
        | isFalse _ => simp [hdec] at hact
        | isTrue htu =>
          subst htu; simp only [hdec, cast_eq] at hact; cases hact
          simpa [SimpAct.vals, Tup.get, OpCode.wp_bitcast, vals, ofBits_toBits] using hw
      | _ => cases hact

theorem OpRel.simpProv?_sound {G : Ctx (FVal Val) Val} {ρ : (t : Ty) → Nat → Val t} {b : Nat}
    (hG : FGood ρ b G) {sig ts : List Ty} {code : OpCode sig ts}
    {args₁ : Tup (Arg (FVal Val)) sig} {args₂ : Tup (Arg Val) sig}
    (hargs : TRel (ArgRel G) args₁ args₂) {res : Tup (FVal Val) ts}
    (hprov : ({ code := code, args := args₁ } : Op (FVal Val) ts).simpProv? = some res)
    {P : Tup Val ts → Prop} (hw : code.wp (vals args₂) P) :
    ∃ xs, P xs ∧ FGood ρ b (Tup.zip res xs ++ G) := by
  cases code with
  | not t =>
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, _⟩
    dsimp only [Op.simpProv?] at hprov
    cases hinv : a₁.finv with
    | none => simp [hinv] at hprov
    | some iv =>
      simp only [hinv] at hprov
      split at hprov
      · rename_i hkind; cases hprov
        have hgood := ha.finv_good hG
        rw [hinv] at hgood
        obtain ⟨_, hv, hsk, hflt⟩ := hgood
        have hke : iv.kind = .not_ := eq_of_beq hkind
        have hv' : lift1 (~~~ ·) (! ·) t a₂.val = iv.src.val := by
          rw [hv, hke]; exact lift1_not_not t iv.src.val
        refine ⟨(lift1 (~~~ ·) (! ·) t a₂.val, ()), ?_, ?_⟩
        · simpa [OpCode.wp_not, vals] using hw
        · exact hG.cons ⟨hv'.symm, hv' ▸ hsk, hflt, ExtDefGood.none, trivial⟩
      · cases hprov
  | bswap t =>
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, _⟩
    dsimp only [Op.simpProv?] at hprov
    split at hprov
    · rename_i hok
      cases hinv : a₁.finv with
      | none => simp [hinv] at hprov
      | some iv =>
        simp only [hinv] at hprov
        split at hprov
        · rename_i hkind; cases hprov
          have hgood := ha.finv_good hG
          rw [hinv] at hgood
          obtain ⟨_, hv, hsk, hflt⟩ := hgood
          have hke : iv.kind = .bswap := eq_of_beq hkind
          have hv' : lift1 bswapBits id t a₂.val = iv.src.val := by
            rw [hv, hke]; exact lift1_bswap_bswap t hok iv.src.val
          refine ⟨(lift1 bswapBits id t a₂.val, ()), ?_, ?_⟩
          · simpa [OpCode.wp_bswap, hok, vals] using hw
          · exact hG.cons ⟨hv'.symm, hv' ▸ hsk, hflt, ExtDefGood.none, trivial⟩
        · cases hprov
    · cases hprov
  | rbit n =>
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, _⟩
    dsimp only [Op.simpProv?] at hprov
    cases hinv : a₁.finv with
    | none => simp [hinv] at hprov
    | some iv =>
      simp only [hinv] at hprov
      split at hprov
      · rename_i hkind; cases hprov
        have hgood := ha.finv_good hG
        rw [hinv] at hgood
        obtain ⟨_, hv, hsk, hflt⟩ := hgood
        have hke : iv.kind = .rbit := eq_of_beq hkind
        have hv' : a₂.val.reverse = iv.src.val := by
          rw [hv, hke]; exact reverse_reverse iv.src.val
        refine ⟨(a₂.val.reverse, ()), ?_, ?_⟩
        · simpa [OpCode.wp_rbit, vals] using hw
        · exact hG.cons ⟨hv'.symm, hv' ▸ hsk, hflt, ExtDefGood.none, trivial⟩
      · cases hprov
  | trunc m n =>
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, _⟩
    dsimp only [Op.simpProv?] at hprov
    cases hf : a₁.fext with
    | none => simp [hf] at hprov
    | some e =>
      simp only [hf] at hprov
      split at hprov
      · rename_i hm; rcases e with ⟨ek, em, hpos, hlt, esrc, eskey⟩
        dsimp only at hm; cases hm; cases hprov
        have hgood := ha.fext_good hG
        rw [hf] at hgood
        obtain ⟨hv, hsk, hflt⟩ := hgood
        have hv' : a₂.val.setWidth n = esrc.val := by
          cases ek <;> dsimp only at hv <;> rw [hv]
          · exact setWidth_signExtend_of_le (Nat.le_of_lt hlt) esrc.val
          · rw [setWidth_setWidth_le (Nat.le_of_lt hlt) esrc.val, BitVec.setWidth_eq]
        refine ⟨(a₂.val.setWidth n, ()), ?_, ?_⟩
        · simpa [OpCode.wp_trunc, vals] using hw.2
        · exact hG.cons ⟨hv'.symm, hv' ▸ hsk, hflt, ExtDefGood.none, trivial⟩
      · cases hprov
  | _ => cases hprov

private theorem extTarget_good {G : Ctx (FVal Val) Val} {ρ : (t : Ty) → Nat → Val t} {b : Nat}
    (hG : FGood ρ b G) (k : ExtKind) {m n : Nat} {a₁ : Arg (FVal Val) (.bits m)}
    {a₂ : Arg Val (.bits m)} (ha : ArgRel G (.bits m) a₁ a₂) {tg : BitsExt Val n}
    (htg : extTarget (n := n) k a₁ = some tg) :
    tg.kind = k ∧ tg.srcKey.fev ρ = tg.src.val ∧ tg.srcKey.FLt b ∧
    (k = .sext → tg.src.val.signExtend n = a₂.val.signExtend n) ∧
    (k = .zext → tg.src.val.setWidth n = a₂.val.setWidth n) := by
  dsimp only [extTarget] at htg
  split at htg
  · rename_i hm
    cases hf : a₁.fext with
    | none =>
      rw [hf] at htg; dsimp only at htg
      split at htg
      · cases htg
        exact ⟨rfl, (ha.fkey_ev hG).trans (ha.fout_val hG).symm, ha.fkey_FLt hG,
          fun _ => congrArg (BitVec.signExtend n) (ha.fout_val hG),
          fun _ => congrArg (BitVec.setWidth n) (ha.fout_val hG)⟩
      · cases htg
    | some e =>
      rw [hf] at htg; dsimp only at htg
      split at htg
      · rename_i heq; cases htg
        have hk : e.kind = k := eq_of_beq heq
        have hgood := ha.fext_good hG; rw [hf] at hgood
        obtain ⟨hev, hsk, hflt⟩ := hgood
        refine ⟨rfl, hsk, hflt, fun hks => ?_, fun hkz => ?_⟩
        · have hek : e.kind = .sext := hk.trans hks
          rw [hek] at hev; dsimp only at hev; rw [hev]
          exact (signExtend_signExtend_of_le e.hpos (Nat.le_of_lt e.hlt) (Nat.le_of_lt hm)
            e.src.val).symm
        · have hek : e.kind = .zext := hk.trans hkz
          rw [hek] at hev; dsimp only at hev; rw [hev]
          exact (setWidth_setWidth_trans (Nat.le_of_lt e.hlt) (Nat.le_of_lt hm)
            e.src.val).symm
      · split at htg
        · cases htg
          exact ⟨rfl, (ha.fkey_ev hG).trans (ha.fout_val hG).symm, ha.fkey_FLt hG,
            fun _ => congrArg (BitVec.signExtend n) (ha.fout_val hG),
            fun _ => congrArg (BitVec.setWidth n) (ha.fout_val hG)⟩
        · cases htg
  · cases htg

theorem OpRel.foldRewrite_wp {G : Ctx (FVal Val) Val} {ρ : (t : Ty) → Nat → Val t} {b : Nat}
    (hG : FGood ρ b G) {sig ts : List Ty} {code : OpCode sig ts}
    {args₁ : Tup (Arg (FVal Val)) sig} {args₂ : Tup (Arg Val) sig}
    (hargs : TRel (ArgRel G) args₁ args₂)
    {P : Tup Val ts → Prop} (hw : code.wp (vals args₂) P) :
    let op₁ : Op (FVal Val) ts := ⟨code, args₁⟩
    op₁.foldRewrite.wp fun xs =>
      P xs ∧ FGood (fupdTup ρ b xs) (b + ts.length) (Tup.zip (op₁.foldWrap b xs) xs ++ G) := by
  have hdef : ∀ (op' : Op Val ts),
      op'.wp P →
      op'.wp fun xs =>
        P xs ∧ FGood (fupdTup ρ b xs) (b + ts.length) (Tup.zip (freshFVals ts xs b) xs ++ G) :=
    fun op' hwp => Op.wp_mono (fun xs hxs => ⟨hxs, hG.freshFVals xs⟩) hwp
  cases code with
  | cmp o t m h =>
    subst h
    rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩
    refine hdef _ ?_
    cases t with
    | bits n =>
      obtain ⟨hev, _, _, _⟩ := narrowCmp_sound hG o ha hb
      dsimp only [Op.foldRewrite]
      cases himm : (narrowCmp o n a₁ b₁).rhs.imm? with
      | some c =>
        have hrv := arg_imm?_val himm
        simp only [Op.wp, op2, OpCode.wp_cmp, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte,
          liftCmp, vals, Arg.val_imm, cast_eq, normBitsCmpImm_eval] at hw ⊢
        rw [← hrv, hev]; exact hw
      | none =>
        simp only [Op.wp, op2, OpCode.wp_cmp, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte,
          liftCmp, vals, cast_eq] at hw ⊢
        rw [hev]; exact hw
    | float _ =>
      simp [OpCode.wp_cmp, Ty.hasFloat] at hw
    | bool =>
      dsimp only [Op.foldRewrite]
      split
      · simpa only [Op.wp, op2, OpCode.wp_cmp, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte,
          vals, cast_eq, ha.fout_val hG, hb.fout_val hG, liftCmp_swap] using hw
      · simpa only [Op.wp, op2, vals, ha.fout_val hG, hb.fout_val hG] using hw
    | pair _ _ =>
      dsimp only [Op.foldRewrite]
      split
      · rename_i hcond
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcond
        simpa only [Op.wp, op2, OpCode.wp_cmp, hcond.1.1, Bool.false_eq_true, ↓reduceIte,
          vals, cast_eq, ha.fout_val hG, hb.fout_val hG, liftCmp_swap] using hw
      · simpa only [Op.wp, op2, vals, ha.fout_val hG, hb.fout_val hG] using hw
  | select t =>
    cases t with
    | bool =>
      rcases args₁ with ⟨c₁, a₁, b₁, ⟨⟩⟩; rcases args₂ with ⟨c₂, a₂, b₂, ⟨⟩⟩
      rcases hargs with _ | ⟨hc, _ | ⟨ha, _ | ⟨hb, _⟩⟩⟩
      dsimp only [Op.foldRewrite, Op.foldWrap]
      split
      · rename_i hft
        simp only [Bool.and_eq_true, beq_iff_eq] at hft
        have hav := ha.fout_imm?_val hG hft.1
        have hbv := hb.fout_imm?_val hG hft.2
        simp only [Op.wp, op1, OpCode.wp_not, OpCode.wp_select, vals,
          hc.fout_val hG, hav, hbv] at hw ⊢
        have hnot : (if c₂.val then false else true) = lift1 (~~~ ·) (! ·) .bool c₂.val := by
          cases c₂.val <;> rfl
        refine ⟨hnot ▸ hw, ?_⟩
        refine (hG.upd_all (ts := [.bool]) (lift1 (~~~ ·) (! ·) .bool c₂.val, ())).cons ?_
        refine ⟨rfl, ?_, Nat.lt_succ_self b, ExtDefGood.none, trivial, ?_, ?_, ?_⟩
        · simp [FKey.fev, fupdTup, fupd_eq]
        · rw [hc.fout_val hG]; rfl
        · rw [FKey.fev_fupdTup _ (hc.fkey_FLt hG), hc.fkey_ev hG, hc.fout_val hG]
        · exact (hc.fkey_FLt hG).add
      · refine hdef _ ?_
        simpa [Op.wp, op3, OpCode.wp_select, vals, hc.fout_val hG, ha.fout_val hG,
          hb.fout_val hG] using hw
    | _ =>
      exact hdef _ (Op.rewrite_wp _ _ ((OpRel.mk _ hargs).fout_wp hG hw))
  | sext m n =>
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, _⟩
    cases htg : extTarget (n := n) .sext a₁ with
    | none =>
      dsimp only [Op.foldRewrite, Op.foldWrap]
      rw [htg]
      exact hdef _ (by simpa [Op.wp, op1, vals, ha.fout_val hG] using hw)
    | some tg =>
      obtain ⟨hk, hsk, hflt, hs, _⟩ := extTarget_good hG .sext ha htg
      dsimp only [Op.foldRewrite, Op.foldWrap]
      rw [htg]
      dsimp only [Op.wp, op1, vals]
      simp only [OpCode.wp_sext] at hw ⊢
      refine ⟨Nat.le_of_lt tg.hlt, ?_, ?_⟩
      · rw [hs rfl]; exact hw.2
      · refine (hG.upd_all (ts := [.bits n]) (tg.src.val.signExtend n, ())).cons ?_
        refine ⟨rfl, by simp [FKey.fev, fupdTup, fupd_eq], Nat.lt_succ_self b, ?_, trivial⟩
        refine ⟨by rw [hk], (FKey.fev_fupdTup _ hflt).trans hsk, hflt.add⟩
  | zext m n =>
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, _⟩
    cases htg : extTarget (n := n) .zext a₁ with
    | none =>
      dsimp only [Op.foldRewrite, Op.foldWrap]
      rw [htg]
      exact hdef _ (by simpa [Op.wp, op1, vals, ha.fout_val hG] using hw)
    | some tg =>
      obtain ⟨hk, hsk, hflt, _, hz⟩ := extTarget_good hG .zext ha htg
      dsimp only [Op.foldRewrite, Op.foldWrap]
      rw [htg]
      dsimp only [Op.wp, op1, vals]
      simp only [OpCode.wp_zext] at hw ⊢
      refine ⟨Nat.le_of_lt tg.hlt, ?_, ?_⟩
      · rw [hz rfl]; exact hw.2
      · refine (hG.upd_all (ts := [.bits n]) (tg.src.val.setWidth n, ())).cons ?_
        refine ⟨rfl, by simp [FKey.fev, fupdTup, fupd_eq], Nat.lt_succ_self b, ?_, trivial⟩
        refine ⟨by rw [hk], (FKey.fev_fupdTup _ hflt).trans hsk, hflt.add⟩
  | trunc m n =>
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, _⟩
    dsimp only [Op.foldRewrite, Op.foldWrap]
    cases htg : truncTarget? m n a₁ with
    | none =>
      exact hdef _ (Op.rewrite_wp _ _ ((OpRel.mk _ (.cons ha .nil)).fout_wp hG hw))
    | some tgt =>
      dsimp only [truncTarget?] at htg
      split at htg
      · rename_i hnm
        cases hf : a₁.fext with
        | none => simp [hf] at htg
        | some e =>
          have hgood := ha.fext_good hG; rw [hf] at hgood
          obtain ⟨hv, hsk, hflt⟩ := hgood
          rw [hf] at htg; dsimp only at htg
          split at htg
          · rename_i hle; cases htg
            dsimp only [Op.wp, op1, OpCode.wp_trunc, vals] at hw ⊢
            have hsw : e.src.val.setWidth n = a₂.val.setWidth n := by
              cases ek : e.kind <;> rw [ek] at hv <;> dsimp only at hv <;> rw [hv]
              · exact (setWidth_signExtend_of_narrow hle (Nat.le_of_lt e.hlt) e.src.val).symm
              · exact (setWidth_setWidth_le (Nat.le_of_lt hnm) e.src.val).symm
            exact ⟨hle, hsw ▸ hw.2, hG.freshFVals _⟩
          · rename_i hnle; cases htg
            have hlt : e.m < n := Nat.lt_of_not_ge hnle
            cases ek : e.kind <;> dsimp only [ExtKind.toOpCode, Op.wp, op1, vals]
            · rw [ek] at hv; dsimp only at hv
              simp only [OpCode.wp_trunc, OpCode.wp_sext] at hw ⊢
              have hsw : e.src.val.signExtend n = a₂.val.setWidth n := by
                rw [hv]; exact (setWidth_signExtend_of_mid (Nat.le_of_lt hlt)
                  (Nat.le_of_lt hnm) e.src.val).symm
              refine ⟨Nat.le_of_lt hlt, hsw ▸ hw.2, ?_⟩
              refine (hG.upd_all (ts := [.bits n]) (e.src.val.signExtend n, ())).cons ?_
              refine ⟨rfl, by simp [FKey.fev, fupdTup, fupd_eq], Nat.lt_succ_self b, ?_, trivial⟩
              refine ⟨rfl, (FKey.fev_fupdTup _ hflt).trans hsk, hflt.add⟩
            · rw [ek] at hv; dsimp only at hv
              simp only [OpCode.wp_trunc, OpCode.wp_zext] at hw ⊢
              have hsw : e.src.val.setWidth n = a₂.val.setWidth n := by
                rw [hv]; exact (setWidth_setWidth_le (Nat.le_of_lt hnm) e.src.val).symm
              refine ⟨Nat.le_of_lt hlt, hsw ▸ hw.2, ?_⟩
              refine (hG.upd_all (ts := [.bits n]) (e.src.val.setWidth n, ())).cons ?_
              refine ⟨rfl, by simp [FKey.fev, fupdTup, fupd_eq], Nat.lt_succ_self b, ?_, trivial⟩
              refine ⟨rfl, (FKey.fev_fupdTup _ hflt).trans hsk, hflt.add⟩
      · cases htg
  | not t =>
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, _⟩
    dsimp only [Op.foldRewrite, Op.rewrite, Op.foldWrap, Op.wp, tupMapArg, vals]
    simp only [OpCode.wp_not, ha.fout_val hG] at hw ⊢
    refine ⟨hw, ?_⟩
    refine (hG.upd_all (ts := [t]) (lift1 (~~~ ·) (! ·) t a₂.val, ())).cons ?_
    refine ⟨rfl, by simp [FKey.fev, fupdTup, fupd_eq], Nat.lt_succ_self b, ExtDefGood.none, ?_⟩
    refine ⟨trivial, by rw [ha.fout_val hG]; rfl, ?_, (ha.fkey_FLt hG).add⟩
    rw [FKey.fev_fupdTup _ (ha.fkey_FLt hG), ha.fkey_ev hG, ha.fout_val hG]
  | bswap t =>
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, _⟩
    dsimp only [Op.foldRewrite, Op.rewrite, Op.foldWrap, Op.wp, tupMapArg, vals]
    simp only [OpCode.wp_bswap, ha.fout_val hG] at hw ⊢
    split at hw
    · cases hw
    · rename_i hnok
      have hok : t.bswapOk = true := by cases h : t.bswapOk <;> simp_all
      simp only [hok, ↓reduceIte, Bool.not_true, Bool.false_eq_true]
      refine ⟨hw, ?_⟩
      refine (hG.upd_all (ts := [t]) (lift1 bswapBits id t a₂.val, ())).cons ?_
      refine ⟨rfl, by simp [FKey.fev, fupdTup, fupd_eq], Nat.lt_succ_self b, ExtDefGood.none, ?_⟩
      refine ⟨hok, by rw [ha.fout_val hG]; rfl, ?_, (ha.fkey_FLt hG).add⟩
      rw [FKey.fev_fupdTup _ (ha.fkey_FLt hG), ha.fkey_ev hG, ha.fout_val hG]
  | rbit n =>
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, _⟩
    dsimp only [Op.foldRewrite, Op.rewrite, Op.foldWrap, Op.wp, tupMapArg, vals]
    simp only [OpCode.wp_rbit, ha.fout_val hG] at hw ⊢
    refine ⟨hw, ?_⟩
    refine (hG.upd_all (ts := [.bits n]) (a₂.val.reverse, ())).cons ?_
    refine ⟨rfl, by simp [FKey.fev, fupdTup, fupd_eq], Nat.lt_succ_self b, ExtDefGood.none, ?_⟩
    refine ⟨trivial, by rw [ha.fout_val hG]; rfl, ?_, (ha.fkey_FLt hG).add⟩
    rw [FKey.fev_fupdTup _ (ha.fkey_FLt hG), ha.fkey_ev hG, ha.fout_val hG]
  | _ =>
    all_goals
      exact hdef _ (Op.rewrite_wp _ _ ((OpRel.mk _ hargs).fout_wp hG hw))

/-! ## `Wf` relations for `fold` -/

section
variable {V₁ V₂ : Ty → Type}

/-- Relational invariant for `BitsExt`. -/
inductive BitsExtRel (G' : Ctx V₁ V₂) {n : Nat} : BitsExt V₁ n → BitsExt V₂ n → Prop
  | mk (kind : ExtKind) {m : Nat} (hpos : 0 < m) (hlt : m < n)
      {s₁ : Arg V₁ (.bits m)} {s₂ : Arg V₂ (.bits m)} {sk : FKey (.bits m)}
      (hs : ArgRel G' (.bits m) s₁ s₂) :
      BitsExtRel G' ⟨kind, m, hpos, hlt, s₁, sk⟩ ⟨kind, m, hpos, hlt, s₂, sk⟩

/-- Relational invariant for extension provenance `ExtDef`. -/
def ExtDefRel (G' : Ctx V₁ V₂) : {t : Ty} → ExtDef V₁ t → ExtDef V₂ t → Prop
  | .bits _, none, none => True
  | .bits _, some e₁, some e₂ => BitsExtRel G' e₁ e₂
  | .bits _, _, _ => False
  | .bool, _, _ | .float _, _, _ | .pair _ _, _, _ => True

theorem ExtDefRel.none {G' : Ctx V₁ V₂} {t : Ty} :
    ExtDefRel G' (t := t) ExtDef.none ExtDef.none := by
  cases t <;> trivial

theorem ExtDefRel.weaken {G₁ G₂ : Ctx V₁ V₂} (hsub : ∀ p ∈ G₁, p ∈ G₂) :
    {t : Ty} → {e₁ : ExtDef V₁ t} → {e₂ : ExtDef V₂ t} →
    ExtDefRel G₁ e₁ e₂ → ExtDefRel G₂ e₁ e₂
  | .bits _, Option.none, Option.none, _ => trivial
  | .bits _, some _, some _, .mk kind hpos hlt hs => .mk kind hpos hlt (hs.weaken hsub)
  | .bits _, some _, Option.none, h | .bits _, Option.none, some _, h => False.elim h
  | .bool, _, _, _ | .float _, _, _, _ | .pair _ _, _, _, _ => trivial

/-- Relational invariant for unary-involution provenance `UnInv`. -/
inductive UnInvRel (G' : Ctx V₁ V₂) {t : Ty} : UnInv V₁ t → UnInv V₂ t → Prop
  | mk (kind : InvKind) {s₁ : Arg V₁ t} {s₂ : Arg V₂ t} {sk : FKey t}
      (hs : ArgRel G' t s₁ s₂) :
      UnInvRel G' ⟨kind, s₁, sk⟩ ⟨kind, s₂, sk⟩

theorem UnInvRel.weaken {G₁ G₂ : Ctx V₁ V₂} (hsub : ∀ p ∈ G₁, p ∈ G₂) {t : Ty}
    {iv₁ : UnInv V₁ t} {iv₂ : UnInv V₂ t} : UnInvRel G₁ iv₁ iv₂ → UnInvRel G₂ iv₁ iv₂
  | .mk kind hs => .mk kind (hs.weaken hsub)

/-- Relational invariant for `Option (UnInv V t)`. -/
def UnInvOptRel (G' : Ctx V₁ V₂) {t : Ty} :
    Option (UnInv V₁ t) → Option (UnInv V₂ t) → Prop
  | none, none => True
  | some iv₁, some iv₂ => UnInvRel G' iv₁ iv₂
  | _, _ => False

theorem UnInvOptRel.weaken {G₁ G₂ : Ctx V₁ V₂} (hsub : ∀ p ∈ G₁, p ∈ G₂) {t : Ty} :
    {iv₁ : Option (UnInv V₁ t)} → {iv₂ : Option (UnInv V₂ t)} →
    UnInvOptRel G₁ iv₁ iv₂ → UnInvOptRel G₂ iv₁ iv₂
  | Option.none, Option.none, _ => trivial
  | some _, some _, h => UnInvRel.weaken hsub h
  | some _, Option.none, h | Option.none, some _, h => False.elim h

/-- Value relation for `FVal` entries in `FRelG`. -/
def FValRel (G' : Ctx V₁ V₂) {t : Ty} (w₁ : FVal V₁ t) (w₂ : FVal V₂ t) : Prop :=
  ArgRel G' t w₁.out w₂.out ∧ w₁.key = w₂.key ∧
  ExtDefRel G' w₁.ext w₂.ext ∧ UnInvOptRel G' w₁.inv w₂.inv

theorem FValRel.weaken {G₁ G₂ : Ctx V₁ V₂} (hsub : ∀ p ∈ G₁, p ∈ G₂)
    {t : Ty} {w₁ : FVal V₁ t} {w₂ : FVal V₂ t} (h : FValRel G₁ w₁ w₂) :
    FValRel G₂ w₁ w₂ :=
  ⟨h.1.weaken hsub, h.2.1, h.2.2.1.weaken hsub, h.2.2.2.weaken hsub⟩

/-- Two `FVal` contexts are related when output operands, keys, and provenances match. -/
def FRelG (G' : Ctx V₁ V₂) (G : Ctx (FVal V₁) (FVal V₂)) : Prop :=
  ∀ p ∈ G, FValRel G' p.2.1 p.2.2

variable {G' : Ctx V₁ V₂} {G : Ctx (FVal V₁) (FVal V₂)}

theorem FRelG.cons (hG : FRelG G' G) {t : Ty} {w₁ : FVal V₁ t} {w₂ : FVal V₂ t}
    (hw : FValRel G' w₁ w₂) : FRelG G' (⟨t, w₁, w₂⟩ :: G)
  | _, .head _ => hw
  | _, .tail _ hp => hG _ hp

theorem FRelG.append (h1 : FRelG G' G) {H : Ctx (FVal V₁) (FVal V₂)} (h2 : FRelG G' H) :
    FRelG G' (H ++ G) := fun p hp => (List.mem_append.1 hp).elim (h2 p) (h1 p)

theorem FRelG.weaken (hG : FRelG G' G) {G'' : Ctx V₁ V₂} (hsub : ∀ p ∈ G', p ∈ G'') :
    FRelG G'' G := fun p hp => (hG p hp).weaken hsub

private theorem FRelG.freshFVals_only {ts : List Ty} (xs₁ : Tup V₁ ts) (xs₂ : Tup V₂ ts)
    (b : Nat) :
    FRelG (Tup.zip xs₁ xs₂) (Tup.zip (freshFVals ts xs₁ b) (freshFVals ts xs₂ b)) :=
  mem_tup_zip_tupFreshWith (fun {t} x n => FVal.fresh (t := t) x n)
    (fun {t} x n => FVal.fresh (t := t) x n)
    (P := fun G' _ w₁ w₂ => FValRel G' w₁ w₂)
    (fun hsub _ _ _ h => h.weaken hsub)
    (fun _ _ _ => ⟨.var List.mem_cons_self, rfl, ExtDefRel.none, trivial⟩)
    xs₁ xs₂ b

theorem FRelG.freshFVals (hG : FRelG G' G) {ts : List Ty} (xs₁ : Tup V₁ ts) (xs₂ : Tup V₂ ts)
    (b : Nat) :
    FRelG (Tup.zip xs₁ xs₂ ++ G') (Tup.zip (freshFVals ts xs₁ b) (freshFVals ts xs₂ b) ++ G) :=
  (hG.weaken fun _ hq => List.mem_append_right _ hq).append
    ((FRelG.freshFVals_only xs₁ xs₂ b).weaken fun _ hq => List.mem_append_left G' hq)

theorem FRelG.freshOne (hG : FRelG G' G) {t : Ty} (v₁ : V₁ t) (v₂ : V₂ t) (b : Nat) :
    FRelG (⟨t, v₁, v₂⟩ :: G') (⟨t, FVal.fresh v₁ b, FVal.fresh v₂ b⟩ :: G)
  | _, .head _ => ⟨.var List.mem_cons_self, rfl, ExtDefRel.none, trivial⟩
  | p, .tail _ hp => (hG p hp).weaken fun _ hq => List.mem_cons_of_mem _ hq

theorem ArgRel.imm?_eq {t : Ty} {a₁ : Arg V₁ t} {a₂ : Arg V₂ t} :
    ArgRel G' t a₁ a₂ → a₁.imm? = a₂.imm?
  | .var _ | .imm _ => rfl

theorem ArgRel.isZero_eq {t : Ty} {a₁ : Arg V₁ t} {a₂ : Arg V₂ t} (h : ArgRel G' t a₁ a₂) :
    isZeroArg? a₁ = isZeroArg? a₂ := by simp [isZeroArg?, h.imm?_eq]

theorem ArgRel.isOnes_eq {t : Ty} {a₁ : Arg V₁ t} {a₂ : Arg V₂ t} (h : ArgRel G' t a₁ a₂) :
    isOnesArg? a₁ = isOnesArg? a₂ := by simp [isOnesArg?, h.imm?_eq]

theorem ArgRel.isOne_eq {t : Ty} {a₁ : Arg V₁ t} {a₂ : Arg V₂ t} (h : ArgRel G' t a₁ a₂) :
    isOneArg? a₁ = isOneArg? a₂ := by simp [isOneArg?, h.imm?_eq]

theorem ArgRel.fout (hG : FRelG G' G) {t : Ty} {a₁ : Arg (FVal V₁) t} {a₂ : Arg (FVal V₂) t} :
    ArgRel G t a₁ a₂ → ArgRel G' t a₁.fout a₂.fout
  | .var h => (hG _ h).1 | .imm c => .imm c

theorem ArgRel.fkey_eq (hG : FRelG G' G) {t : Ty} {a₁ : Arg (FVal V₁) t} {a₂ : Arg (FVal V₂) t} :
    ArgRel G t a₁ a₂ → a₁.fkey = a₂.fkey
  | .var h => (hG _ h).2.1 | .imm _ => rfl

theorem ArgRel.fext_rel (hG : FRelG G' G) {t : Ty} {a₁ : Arg (FVal V₁) t} {a₂ : Arg (FVal V₂) t} :
    ArgRel G t a₁ a₂ → ExtDefRel G' a₁.fext a₂.fext
  | .var h => (hG _ h).2.2.1 | .imm _ => ExtDefRel.none

theorem ArgRel.finv_rel (hG : FRelG G' G) {t : Ty} {a₁ : Arg (FVal V₁) t} {a₂ : Arg (FVal V₂) t} :
    ArgRel G t a₁ a₂ → UnInvOptRel G' a₁.finv a₂.finv
  | .var h => (hG _ h).2.2.2 | .imm _ => trivial

/-- Relational invariant for `narrowCmp`. -/
inductive NarrowCmpRel (G' : Ctx V₁ V₂) : NarrowCmp V₁ → NarrowCmp V₂ → Prop
  | mk {w : Nat} {o : CmpOp} {l₁ r₁ : Arg V₁ (.bits w)} {l₂ r₂ : Arg V₂ (.bits w)}
      {lk rk : FKey (.bits w)}
      (hl : ArgRel G' (.bits w) l₁ l₂) (hr : ArgRel G' (.bits w) r₁ r₂) :
      NarrowCmpRel G' ⟨w, o, l₁, r₁, lk, rk⟩ ⟨w, o, l₂, r₂, lk, rk⟩

private theorem narrowCmpCore_rel (hG : FRelG G' G) {n : Nat} (o : CmpOp)
    {a₁ b₁ : Arg (FVal V₁) (.bits n)} {a₂ b₂ : Arg (FVal V₂) (.bits n)}
    (ha : ArgRel G (.bits n) a₁ a₂) (hb : ArgRel G (.bits n) b₁ b₂) :
    NarrowCmpRel G' (narrowCmpCore o n a₁ b₁) (narrowCmpCore o n a₂ b₂) := by
  have hbase : NarrowCmpRel G' ⟨n, o, a₁.fout, b₁.fout, a₁.fkey, b₁.fkey⟩
      ⟨n, o, a₂.fout, b₂.fout, a₂.fkey, b₂.fkey⟩ := by
    rw [ha.fkey_eq hG, hb.fkey_eq hG]
    exact .mk (ha.fout hG) (hb.fout hG)
  have hfa := ha.fext_rel hG
  have hfb := hb.fext_rel hG
  have hbi : b₁.fout.imm? = b₂.fout.imm? := (hb.fout hG).imm?_eq
  dsimp only [narrowCmpCore]
  rw [hbi]
  cases ha₁e : a₁.fext with
  | none =>
    cases ha₂e : a₂.fext with
    | none => exact hbase
    | some _ => rw [ha₁e, ha₂e] at hfa; exact False.elim hfa
  | some ea₁ =>
    cases ha₂e : a₂.fext with
    | none => rw [ha₁e, ha₂e] at hfa; exact False.elim hfa
    | some ea₂ =>
      rw [ha₁e, ha₂e] at hfa
      cases hfa with
      | mk ka hposa hlta hsa =>
        cases b₂.fout.imm? with
        | some c =>
          cases ka with
          | sext =>
            dsimp only; split
            · exact .mk hsa (.imm _)
            · exact hbase
          | zext =>
            dsimp only; split
            · exact .mk hsa (.imm _)
            · exact hbase
        | none =>
          cases hb₁e : b₁.fext with
          | none =>
            cases hb₂e : b₂.fext with
            | none => exact hbase
            | some _ => rw [hb₁e, hb₂e] at hfb; exact False.elim hfb
          | some eb₁ =>
            cases hb₂e : b₂.fext with
            | none => rw [hb₁e, hb₂e] at hfb; exact False.elim hfb
            | some eb₂ =>
              rw [hb₁e, hb₂e] at hfb
              cases hfb with
              | mk kb hposb hltb hsb =>
                cases ka <;> cases kb
                · dsimp only; split
                  · rename_i hm; subst hm; exact .mk hsa hsb
                  · exact hbase
                · exact hbase
                · exact hbase
                · dsimp only; split
                  · rename_i hm; subst hm; exact .mk hsa hsb
                  · exact hbase

theorem narrowCmp_rel (hG : FRelG G' G) {n : Nat} (o : CmpOp)
    {a₁ b₁ : Arg (FVal V₁) (.bits n)} {a₂ b₂ : Arg (FVal V₂) (.bits n)}
    (ha : ArgRel G (.bits n) a₁ a₂) (hb : ArgRel G (.bits n) b₁ b₂) :
    NarrowCmpRel G' (narrowCmp o n a₁ b₁) (narrowCmp o n a₂ b₂) := by
  dsimp only [narrowCmp]
  rw [(ha.fout hG).imm?_eq, (hb.fout hG).imm?_eq]
  cases a₂.fout.imm? <;> cases b₂.fout.imm?
  · exact narrowCmpCore_rel hG o ha hb
  · exact narrowCmpCore_rel hG o ha hb
  · exact narrowCmpCore_rel hG o.swap hb ha
  · exact narrowCmpCore_rel hG o ha hb

theorem TRel.fout (hG : FRelG G' G) {ts : List Ty} {as₁ : Tup (Arg (FVal V₁)) ts}
    {as₂ : Tup (Arg (FVal V₂)) ts} (h : TRel (ArgRel G) as₁ as₂) :
    TRel (ArgRel G') (tupMapArg (fun _ => Arg.fout) as₁) (tupMapArg (fun _ => Arg.fout) as₂) :=
  TRel.tupMapArg_rel (fun _ => Arg.fout) (fun _ => Arg.fout) (fun ha => ha.fout hG) h

theorem TRel.imm?_eq {ts : List Ty} {as₁ : Tup (Arg V₁) ts} {as₂ : Tup (Arg V₂) ts}
    (h : TRel (ArgRel G') as₁ as₂) : tupImms? as₁ = tupImms? as₂ :=
  TRel.tupImms?_eq (fun ha => ha.imm?_eq) h

theorem OpRel.simpAct_eq (hG : FRelG G' G) :
    ∀ {sig rs : List Ty} {code : OpCode sig rs}
      {args₁ : Tup (Arg (FVal V₁)) sig} {args₂ : Tup (Arg (FVal V₂)) sig},
      TRel (ArgRel G) args₁ args₂ →
      ({ code := code, args := args₁ } : Op (FVal V₁) rs).simpAct =
      ({ code := code, args := args₂ } : Op (FVal V₂) rs).simpAct := by
  intro sig rs code args₁ args₂ hargs
  delta Op.simpAct
  dsimp only
  have himm : tupImms? (tupMapArg (fun _ => Arg.fout) args₁) =
      tupImms? (tupMapArg (fun _ => Arg.fout) args₂) :=
    TRel.imm?_eq (TRel.fout hG hargs)
  rw [himm]
  cases (tupImms? (tupMapArg (fun _ => Arg.fout) args₂)).bind code.eval? with
  | some _ => rfl
  | none =>
    dsimp only
    cases code with
    | copy _ => rfl
    | neg t => cases t <;> rfl
    | add _ | sub _ | mul _ | and _ | or _ | xor _ | shl _ | lshr _ | ashr _ | rotl _ | rotr _
    | udiv _ | sdiv _ | urem _ | srem _ | udiv0 _ | sdiv0 _
    | umulw _ | smulw _ =>
      rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩
      have ha' := ha.fout hG
      have hb' := hb.fout hG
      simp only [ha'.isZero_eq, hb'.isZero_eq, ha'.isOnes_eq, hb'.isOnes_eq,
        ha'.isOne_eq, hb'.isOne_eq, hb'.imm?_eq, ha.fkey_eq hG, hb.fkey_eq hG]
    | cmp o t _ h =>
      subst h
      rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, ⟨⟩⟩
      rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩
      cases t with
      | bits n =>
        dsimp only
        have hnc := narrowCmp_rel hG o ha hb
        generalize h1 : narrowCmp o n a₁ b₁ = nc₁ at hnc ⊢
        generalize h2 : narrowCmp o n a₂ b₂ = nc₂ at hnc ⊢
        cases hnc with
        | mk _ hr => simp only [hr.imm?_eq]
      | _ =>
        simp only [ha.fkey_eq hG, hb.fkey_eq hG]
    | select t =>
      rcases hargs with _ | ⟨ha, _ | ⟨hb, _ | ⟨hc, _⟩⟩⟩
      have ha' := ha.fout hG; have hb' := hb.fout hG; have hc' := hc.fout hG
      cases t <;> simp only [ha'.imm?_eq, hb'.imm?_eq, hc'.imm?_eq,
        hb.fkey_eq hG, hc.fkey_eq hG]
    | blend _ _ _ | addc _ | subb _ =>
      rcases hargs with _ | ⟨ha, _ | ⟨hb, _ | ⟨hc, _⟩⟩⟩
      have ha' := ha.fout hG
      have hb' := hb.fout hG
      have hc' := hc.fout hG
      simp only [ha'.isZero_eq, hb'.isZero_eq, ha'.imm?_eq, hc'.imm?_eq,
        ha.fkey_eq hG, hb.fkey_eq hG, hc.fkey_eq hG]
    | _ => rfl

private theorem ArgRel.fpair_rel (hG : FRelG G' G) {t : Ty}
    {a₁ : Arg (FVal V₁) t} {a₂ : Arg (FVal V₂) t} :
    ArgRel G t a₁ a₂ → FValRel G' a₁.fpair a₂.fpair
  | .var hmem => hG _ hmem
  | .imm c => ⟨.imm c, rfl, ExtDefRel.none, trivial⟩

theorem FRelG.apply_simpAct (hG : FRelG G' G) :
    {sig rs : List Ty} → {as₁ : Tup (Arg (FVal V₁)) sig} → {as₂ : Tup (Arg (FVal V₂)) sig} →
    TRel (ArgRel G) as₁ as₂ → (act : SimpAct sig rs) →
    FRelG G' (Tup.zip (act.apply as₁) (act.apply as₂) ++ G)
  | sig, [], _, _, _, () => by simpa [SimpAct.apply, Tup.zip] using hG
  | sig, r :: rs, as₁, as₂, has, (elem, act) => by
    have ih := FRelG.apply_simpAct hG has act
    cases elem with
    | imm c =>
      intro p hp
      cases hp with
      | head => exact ⟨.imm c, rfl, ExtDefRel.none, trivial⟩
      | tail _ hp => exact ih p hp
    | arg i =>
      have hi : ArgRel G r (as₁.get i) (as₂.get i) := TRel.get i has
      intro p hp
      cases hp with
      | head => exact hi.fpair_rel hG
      | tail _ hp => exact ih p hp

private theorem OpRel.rewrite_mul_a {t : Ty} {a₁ b₁ : Arg V₁ t} {a₂ b₂ : Arg V₂ t}
    (ha : ArgRel G' t a₁ a₂) (hb : ArgRel G' t b₁ b₂) :
    OpRel G'
      (match a₁.imm?.bind (leafPow2Shift? t) with
        | some s => op2 (.shl t) b₁ (.imm s)
        | none => op2 (.mul t) a₁ b₁)
      (match a₂.imm?.bind (leafPow2Shift? t) with
        | some s => op2 (.shl t) b₂ (.imm s)
        | none => op2 (.mul t) a₂ b₂) := by
  cases ha with
  | @var _ _ hma => exact .mk (.mul t) (.cons (.var hma) (.cons hb .nil))
  | imm ca =>
    simp only [Arg.imm?, Option.bind_some]
    cases leafPow2Shift? t ca with
    | some s => exact .mk (.shl t) (.cons hb (.cons (.imm s) .nil))
    | none => exact .mk (.mul t) (.cons (.imm ca) (.cons hb .nil))

theorem OpRel.rewrite {rs : List Ty} {o₁ : Op V₁ rs} {o₂ : Op V₂ rs} (ho : OpRel G' o₁ o₂) :
    OpRel G' o₁.rewrite o₂.rewrite := by
  cases ho with
  | mk code hargs =>
    cases code with
    | mul t =>
      rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩; dsimp only [Op.rewrite]
      split
      · exact .mk (.mul t) (.cons ha (.cons hb .nil))
      · cases hb with
        | @var _ _ hmb => exact OpRel.rewrite_mul_a ha (.var hmb)
        | imm cb =>
          simp only [Arg.imm?, Option.bind_some]
          cases leafPow2Shift? t cb with
          | some s => exact .mk (.shl t) (.cons ha (.cons (.imm s) .nil))
          | none => exact OpRel.rewrite_mul_a ha (.imm cb)
    | udiv n | urem n =>
      rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩; dsimp only [Op.rewrite]
      cases hb with
      | @var _ _ hmb => exact .mk _ (.cons ha (.cons (.var hmb) .nil))
      | imm cb =>
        simp only [Arg.imm?, Option.bind_some]
        cases findPow2 n cb n with
        | some m => exact .mk _ (.cons ha (.cons (.imm _) .nil))
        | none => exact .mk _ (.cons ha (.cons (.imm cb) .nil))
    | _ => exact .mk _ hargs

private theorem extTarget_rel (hG : FRelG G' G) (k : ExtKind) {m n : Nat}
    {a₁ : Arg (FVal V₁) (.bits m)} {a₂ : Arg (FVal V₂) (.bits m)}
    (ha : ArgRel G (.bits m) a₁ a₂) :
    ExtDefRel G' (t := .bits n) (extTarget (n := n) k a₁) (extTarget (n := n) k a₂) := by
  dsimp only [extTarget]
  split
  · rename_i hm
    have hf := ha.fext_rel hG
    cases hf₁ : a₁.fext with
    | none =>
      cases hf₂ : a₂.fext with
      | none =>
        dsimp only; split
        · rw [ha.fkey_eq hG]; exact .mk k _ hm (ha.fout hG)
        · trivial
      | some _ => rw [hf₁, hf₂] at hf; exact False.elim hf
    | some e₁ =>
      cases hf₂ : a₂.fext with
      | none => rw [hf₁, hf₂] at hf; exact False.elim hf
      | some e₂ =>
        rw [hf₁, hf₂] at hf
        cases hf with
        | mk ek hpos hlt hs =>
          dsimp only; split
          · exact .mk k hpos (Nat.lt_trans hlt hm) hs
          · split
            · rw [ha.fkey_eq hG]; exact .mk k _ hm (ha.fout hG)
            · trivial
  · trivial

private inductive TruncTargetRel (G' : Ctx V₁ V₂) {m n : Nat} :
    Option (TruncTarget V₁ m n) → Option (TruncTarget V₂ m n) → Prop
  | none : TruncTargetRel G' Option.none Option.none
  | narrow (w : Nat) (hle : n ≤ w) {s₁ : Arg V₁ (.bits w)} {s₂ : Arg V₂ (.bits w)}
      (hs : ArgRel G' (.bits w) s₁ s₂) :
      TruncTargetRel G' (some (.narrow w hle s₁)) (some (.narrow w hle s₂))
  | lift {t₁ : BitsExt V₁ n} {t₂ : BitsExt V₂ n} (ht : BitsExtRel G' t₁ t₂) :
      TruncTargetRel G' (some (.lift t₁)) (some (.lift t₂))

private theorem truncTarget?_rel (hG : FRelG G' G) (m n : Nat)
    {a₁ : Arg (FVal V₁) (.bits m)} {a₂ : Arg (FVal V₂) (.bits m)}
    (ha : ArgRel G (.bits m) a₁ a₂) :
    TruncTargetRel G' (truncTarget? m n a₁) (truncTarget? m n a₂) := by
  dsimp only [truncTarget?]
  split
  · have hf := ha.fext_rel hG
    cases hf₁ : a₁.fext with
    | none =>
      cases hf₂ : a₂.fext with
      | none => exact .none
      | some _ => rw [hf₁, hf₂] at hf; exact False.elim hf
    | some e₁ =>
      cases hf₂ : a₂.fext with
      | none => rw [hf₁, hf₂] at hf; exact False.elim hf
      | some e₂ =>
        rw [hf₁, hf₂] at hf
        cases hf with
        | mk ek hpos hlt hs =>
          dsimp only; split
          · exact .narrow _ _ hs
          · exact .lift (.mk ek hpos _ hs)
  · exact .none

theorem OpRel.simpProv?_rel (hG : FRelG G' G) :
    ∀ {sig ts : List Ty} {code : OpCode sig ts}
      {args₁ : Tup (Arg (FVal V₁)) sig} {args₂ : Tup (Arg (FVal V₂)) sig},
      TRel (ArgRel G) args₁ args₂ →
      match ({ code := code, args := args₁ } : Op (FVal V₁) ts).simpProv?,
            ({ code := code, args := args₂ } : Op (FVal V₂) ts).simpProv? with
      | some res₁, some res₂ => FRelG G' (Tup.zip res₁ res₂ ++ G)
      | none, none => True
      | _, _ => False := by
  intro sig ts code args₁ args₂ hargs
  cases code with
  | not _ =>
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, _⟩
    dsimp only [Op.simpProv?]; have hi := ha.finv_rel hG
    cases hi₁ : a₁.finv with
    | none =>
      cases hi₂ : a₂.finv with
      | none => trivial
      | some _ => rw [hi₁, hi₂] at hi; exact False.elim hi
    | some _ =>
      cases hi₂ : a₂.finv with
      | none => rw [hi₁, hi₂] at hi; exact False.elim hi
      | some _ =>
        rw [hi₁, hi₂] at hi; dsimp only
        cases hi with
        | mk kind hs =>
          dsimp only
          by_cases hk : (kind == .not_) = true
          · simp only [hk, ↓reduceIte]; exact hG.cons ⟨hs, rfl, ExtDefRel.none, trivial⟩
          · simp only [hk, Bool.false_eq_true, ↓reduceIte]
  | bswap t =>
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, _⟩
    dsimp only [Op.simpProv?]
    by_cases hok : t.bswapOk = true
    · simp only [hok, ↓reduceIte]; have hi := ha.finv_rel hG
      cases hi₁ : a₁.finv with
      | none =>
        cases hi₂ : a₂.finv with
        | none => trivial
        | some _ => rw [hi₁, hi₂] at hi; exact False.elim hi
      | some _ =>
        cases hi₂ : a₂.finv with
        | none => rw [hi₁, hi₂] at hi; exact False.elim hi
        | some _ =>
          rw [hi₁, hi₂] at hi; dsimp only
          cases hi with
          | mk kind hs =>
            dsimp only
            by_cases hk : (kind == .bswap) = true
            · simp only [hk, ↓reduceIte]; exact hG.cons ⟨hs, rfl, ExtDefRel.none, trivial⟩
            · simp only [hk, Bool.false_eq_true, ↓reduceIte]
    · simp only [hok, Bool.false_eq_true, ↓reduceIte]
  | rbit _ =>
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, _⟩
    dsimp only [Op.simpProv?]; have hi := ha.finv_rel hG
    cases hi₁ : a₁.finv with
    | none =>
      cases hi₂ : a₂.finv with
      | none => trivial
      | some _ => rw [hi₁, hi₂] at hi; exact False.elim hi
    | some _ =>
      cases hi₂ : a₂.finv with
      | none => rw [hi₁, hi₂] at hi; exact False.elim hi
      | some _ =>
        rw [hi₁, hi₂] at hi; dsimp only
        cases hi with
        | mk kind hs =>
          dsimp only
          by_cases hk : (kind == .rbit) = true
          · simp only [hk, ↓reduceIte]; exact hG.cons ⟨hs, rfl, ExtDefRel.none, trivial⟩
          · simp only [hk, Bool.false_eq_true, ↓reduceIte]
  | trunc _ n =>
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, _⟩
    dsimp only [Op.simpProv?]
    have hf := ha.fext_rel hG
    cases hf₁ : a₁.fext with
    | none =>
      cases hf₂ : a₂.fext with
      | none => trivial
      | some _ => rw [hf₁, hf₂] at hf; exact False.elim hf
    | some e₁ =>
      cases hf₂ : a₂.fext with
      | none => rw [hf₁, hf₂] at hf; exact False.elim hf
      | some e₂ =>
        rw [hf₁, hf₂] at hf
        cases hf with
        | mk ek hpos hlt hs =>
          rename_i m' _ _ _
          dsimp only
          by_cases hm : m' = n
          · cases hm
            simp only [↓reduceDIte]
            exact hG.cons ⟨hs, rfl, ExtDefRel.none, trivial⟩
          · simp [hm]
  | _ => all_goals trivial

theorem OpRel.foldRewrite_rel (hG : FRelG G' G) {sig rs : List Ty} {code : OpCode sig rs}
    {args₁ : Tup (Arg (FVal V₁)) sig} {args₂ : Tup (Arg (FVal V₂)) sig}
    (hargs : TRel (ArgRel G) args₁ args₂) :
    OpRel G'
      (({ code := code, args := args₁ } : Op (FVal V₁) rs).foldRewrite)
      (({ code := code, args := args₂ } : Op (FVal V₂) rs).foldRewrite) := by
  cases code with
  | cmp o t m h =>
    subst h
    rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩
    cases t with
    | bits n =>
      have hnc := narrowCmp_rel hG o ha hb
      dsimp only [Op.foldRewrite]
      generalize h1 : narrowCmp o n a₁ b₁ = nc₁ at hnc ⊢
      generalize h2 : narrowCmp o n a₂ b₂ = nc₂ at hnc ⊢
      cases hnc with
      | mk hl hr =>
        cases hr with
        | var hm => exact .mk _ (.cons hl (.cons (.var hm) .nil))
        | imm c => exact .mk _ (.cons hl (.cons (.imm _) .nil))
    | _ =>
      have ha' := ha.fout hG; have hb' := hb.fout hG
      dsimp only [Op.foldRewrite]; rw [ha'.imm?_eq, hb'.imm?_eq]
      split
      · exact .mk _ (.cons hb' (.cons ha' .nil))
      · exact .mk _ (.cons ha' (.cons hb' .nil))
  | select t =>
    cases t with
    | bool =>
      rcases args₁ with ⟨c₁, a₁, b₁, ⟨⟩⟩; rcases args₂ with ⟨c₂, a₂, b₂, ⟨⟩⟩
      rcases hargs with _ | ⟨hc, _ | ⟨ha, _ | ⟨hb, _⟩⟩⟩
      have hc' := hc.fout hG; have ha' := ha.fout hG; have hb' := hb.fout hG
      dsimp only [Op.foldRewrite]; rw [ha'.imm?_eq, hb'.imm?_eq]
      split
      · exact .mk _ (.cons hc' .nil)
      · exact .mk _ (.cons hc' (.cons ha' (.cons hb' .nil)))
    | _ =>
      dsimp only [Op.foldRewrite]
      exact OpRel.rewrite (.mk _ (TRel.fout hG hargs))
  | sext m n =>
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, _⟩
    dsimp only [Op.foldRewrite]
    have htg := extTarget_rel hG .sext (n := n) ha
    cases h₁ : extTarget (n := n) .sext a₁ with
    | none =>
      cases h₂ : extTarget (n := n) .sext a₂ with
      | none => exact .mk _ (.cons (ha.fout hG) .nil)
      | some _ => rw [h₁, h₂] at htg; exact False.elim htg
    | some tg₁ =>
      cases h₂ : extTarget (n := n) .sext a₂ with
      | none => rw [h₁, h₂] at htg; exact False.elim htg
      | some tg₂ =>
        rw [h₁, h₂] at htg
        cases htg with
        | mk _ _ _ hs => exact .mk _ (.cons hs .nil)
  | zext m n =>
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, _⟩
    dsimp only [Op.foldRewrite]
    have htg := extTarget_rel hG .zext (n := n) ha
    cases h₁ : extTarget (n := n) .zext a₁ with
    | none =>
      cases h₂ : extTarget (n := n) .zext a₂ with
      | none => exact .mk _ (.cons (ha.fout hG) .nil)
      | some _ => rw [h₁, h₂] at htg; exact False.elim htg
    | some tg₁ =>
      cases h₂ : extTarget (n := n) .zext a₂ with
      | none => rw [h₁, h₂] at htg; exact False.elim htg
      | some tg₂ =>
        rw [h₁, h₂] at htg
        cases htg with
        | mk _ _ _ hs => exact .mk _ (.cons hs .nil)
  | trunc m n =>
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, _⟩
    dsimp only [Op.foldRewrite]
    have ht := truncTarget?_rel hG m n ha
    cases h₁ : truncTarget? m n a₁ <;> cases h₂ : truncTarget? m n a₂ <;> rw [h₁, h₂] at ht
    · exact .mk _ (.cons (ha.fout hG) .nil)
    · cases ht
    · cases ht
    · cases ht with
      | narrow _ _ hs => exact .mk _ (.cons hs .nil)
      | lift hte =>
        cases hte with
        | mk _ _ _ hs => exact .mk _ (.cons hs .nil)
  | _ =>
    all_goals
      (dsimp only [Op.foldRewrite]
       exact OpRel.rewrite (.mk _ (TRel.fout hG hargs)))

theorem FRelG.foldWrap (hG : FRelG G' G) {sig ts : List Ty} {code : OpCode sig ts}
    {args₁ : Tup (Arg (FVal V₁)) sig} {args₂ : Tup (Arg (FVal V₂)) sig}
    (hargs : TRel (ArgRel G) args₁ args₂) (b : Nat) (xs₁ : Tup V₁ ts) (xs₂ : Tup V₂ ts) :
    FRelG (Tup.zip xs₁ xs₂ ++ G')
      (Tup.zip (({ code := code, args := args₁ } : Op (FVal V₁) ts).foldWrap b xs₁)
               (({ code := code, args := args₂ } : Op (FVal V₂) ts).foldWrap b xs₂) ++ G) := by
  have hsub : ∀ {u : Ty} {r₁ : V₁ u} {r₂ : V₂ u},
      ∀ p ∈ G', p ∈ (Tup.zip (as := [u]) (r₁, ()) (r₂, ()) ++ G') :=
    fun _ hq => List.mem_cons_of_mem _ hq
  cases code with
  | sext m n =>
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, _⟩
    rcases xs₁ with ⟨r₁, ⟨⟩⟩; rcases xs₂ with ⟨r₂, ⟨⟩⟩
    dsimp only [Op.foldWrap]
    have htg := extTarget_rel hG .sext (n := n) ha
    cases h₁ : extTarget (n := n) .sext a₁ with
    | none =>
      cases h₂ : extTarget (n := n) .sext a₂ with
      | none => exact hG.freshFVals (ts := [.bits n]) (r₁, ()) (r₂, ()) b
      | some _ => rw [h₁, h₂] at htg; exact False.elim htg
    | some tg₁ =>
      cases h₂ : extTarget (n := n) .sext a₂ with
      | none => rw [h₁, h₂] at htg; exact False.elim htg
      | some tg₂ =>
        rw [h₁, h₂] at htg
        exact (hG.weaken hsub).cons
          ⟨.var List.mem_cons_self, rfl, ExtDefRel.weaken hsub htg, trivial⟩
  | zext m n =>
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, _⟩
    rcases xs₁ with ⟨r₁, ⟨⟩⟩; rcases xs₂ with ⟨r₂, ⟨⟩⟩
    dsimp only [Op.foldWrap]
    have htg := extTarget_rel hG .zext (n := n) ha
    cases h₁ : extTarget (n := n) .zext a₁ with
    | none =>
      cases h₂ : extTarget (n := n) .zext a₂ with
      | none => exact hG.freshFVals (ts := [.bits n]) (r₁, ()) (r₂, ()) b
      | some _ => rw [h₁, h₂] at htg; exact False.elim htg
    | some tg₁ =>
      cases h₂ : extTarget (n := n) .zext a₂ with
      | none => rw [h₁, h₂] at htg; exact False.elim htg
      | some tg₂ =>
        rw [h₁, h₂] at htg
        exact (hG.weaken hsub).cons
          ⟨.var List.mem_cons_self, rfl, ExtDefRel.weaken hsub htg, trivial⟩
  | trunc m n =>
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, _⟩
    rcases xs₁ with ⟨r₁, ⟨⟩⟩; rcases xs₂ with ⟨r₂, ⟨⟩⟩
    dsimp only [Op.foldWrap]
    have ht := truncTarget?_rel hG m n ha
    cases h₁ : truncTarget? m n a₁ <;> cases h₂ : truncTarget? m n a₂ <;> rw [h₁, h₂] at ht
    · exact hG.freshFVals (ts := [.bits n]) (r₁, ()) (r₂, ()) b
    · cases ht
    · cases ht
    · cases ht with
      | narrow _ _ _ => exact hG.freshFVals (ts := [.bits n]) (r₁, ()) (r₂, ()) b
      | lift hte =>
        exact (hG.weaken hsub).cons
          ⟨.var List.mem_cons_self, rfl, ExtDefRel.weaken hsub hte, trivial⟩
  | not t =>
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, _⟩
    rcases xs₁ with ⟨r₁, ⟨⟩⟩; rcases xs₂ with ⟨r₂, ⟨⟩⟩
    dsimp only [Op.foldWrap]
    refine (hG.weaken hsub).cons ⟨.var List.mem_cons_self, rfl, ExtDefRel.none, ?_⟩
    rw [ha.fkey_eq hG]
    exact .mk .not_ ((ha.fout hG).weaken hsub)
  | bswap t =>
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, _⟩
    rcases xs₁ with ⟨r₁, ⟨⟩⟩; rcases xs₂ with ⟨r₂, ⟨⟩⟩
    dsimp only [Op.foldWrap]
    split
    · refine (hG.weaken hsub).cons ⟨.var List.mem_cons_self, rfl, ExtDefRel.none, ?_⟩
      rw [ha.fkey_eq hG]
      exact .mk .bswap ((ha.fout hG).weaken hsub)
    · exact hG.freshFVals (ts := [t]) (r₁, ()) (r₂, ()) b
  | rbit n =>
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, _⟩
    rcases xs₁ with ⟨r₁, ⟨⟩⟩; rcases xs₂ with ⟨r₂, ⟨⟩⟩
    dsimp only [Op.foldWrap]
    refine (hG.weaken hsub).cons ⟨.var List.mem_cons_self, rfl, ExtDefRel.none, ?_⟩
    rw [ha.fkey_eq hG]
    exact .mk .rbit ((ha.fout hG).weaken hsub)
  | select t =>
    cases t with
    | bool =>
      rcases args₁ with ⟨c₁, a₁, b₁, ⟨⟩⟩; rcases args₂ with ⟨c₂, a₂, b₂, ⟨⟩⟩
      rcases hargs with _ | ⟨hc, _ | ⟨ha, _ | ⟨hb, _⟩⟩⟩
      rcases xs₁ with ⟨r₁, ⟨⟩⟩; rcases xs₂ with ⟨r₂, ⟨⟩⟩
      have ha' := ha.fout hG; have hb' := hb.fout hG
      dsimp only [Op.foldWrap]; rw [ha'.imm?_eq, hb'.imm?_eq]
      split
      · refine (hG.weaken hsub).cons ⟨.var List.mem_cons_self, rfl, ExtDefRel.none, ?_⟩
        rw [hc.fkey_eq hG]
        exact .mk .not_ ((hc.fout hG).weaken hsub)
      · exact hG.freshFVals (ts := [.bool]) (r₁, ()) (r₂, ()) b
    | _ =>
      dsimp only [Op.foldWrap]
      exact hG.freshFVals xs₁ xs₂ b
  | _ =>
    all_goals
      (dsimp only [Op.foldWrap]
       exact hG.freshFVals xs₁ xs₂ b)

end

/-! ## Block projection helper and `Wf.induct` correctness proofs -/

theorem foldB_get {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} (b : Nat) :
    {sig : List (List Ty)} → {ts : List Ty} → (bs : Blocks (FVal V) L rs sig) →
    (i : Member ts sig) → (xs : Tup V ts) →
    (foldB b bs).get i xs = fold (b + ts.length) (bs.get i (freshFVals ts xs b))
  | _, _, .cons _ _, .here, _ => rfl
  | _, _, .cons _ bs, .there i, xs => foldB_get b bs i xs

/-- Weakest-precondition preservation for `fold`, proved via `Wf.induct`. -/
private theorem fold_let {V : Ty → Type} {L : List Ty → Type} {ts rs : List Ty}
    (next : Nat) (op : Op (FVal V) ts) (k : Tup (FVal V) ts → Expr (FVal V) L rs) :
    fold next (.let_ op k) =
      match op.simpAct with
      | some act => fold next (k (act.apply op.args))
      | none =>
        match op.simpProv? with
        | some res => fold next (k res)
        | none =>
          .let_ op.foldRewrite fun xs => fold (next + ts.length) (k (op.foldWrap next xs)) := by
  delta fold; dsimp only [Expr.brecOn, Expr.rec, fold._f]
  cases op.simpAct <;> cases op.simpProv? <;> rfl

theorem fold_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {G : Ctx (FVal Val) Val} {D : Ctx Cont Cont}
    {e₁ : Expr (FVal Val) Cont rs} {e₂ : Expr Val Cont rs}
    (hwf : Wf G D e₁ e₂) :
    (∀ p ∈ D, p.2.1 = p.2.2) →
    ∀ b ρ, FGood ρ b G → ∀ m, wp Γ Q X e₂ m → wp Γ Q X (fold b e₁) m := by
  induction hwf using Wf.induct with
  | @let_ G D ts op₁ op₂ k₁ k₂ hop _ ih =>
    intro hD b ρ hG m hw
    dsimp only [wp] at hw
    cases hop with
    | @mk sig _ code args₁ args₂ hargs =>
      rw [fold_let]
      cases hact : ({ code := code, args := args₁ } : Op (FVal Val) ts).simpAct with
      | some act =>
        obtain ⟨hk2, hfg⟩ := OpRel.simpAct_sound hG hargs hact hw
        exact ih (act.apply args₁) (SimpAct.vals (vals args₂) act) hD b ρ hfg m hk2
      | none =>
        cases hprov : ({ code := code, args := args₁ } : Op (FVal Val) ts).simpProv? with
        | some res =>
          obtain ⟨xs, hk2, hfg⟩ := OpRel.simpProv?_sound hG hargs hprov hw
          exact ih res xs hD b ρ hfg m hk2
        | none =>
          dsimp only [wp]
          have hw' := OpRel.foldRewrite_wp hG hargs hw
          exact Op.wp_mono (fun xs ⟨hxs, hG'⟩ =>
            ih _ xs hD (b + ts.length) (fupdTup ρ b xs) hG' m hxs) hw'
  | load t ha _ ih =>
    intro hD b ρ hG m hw; dsimp only [wp, fold] at hw ⊢; rcases hw with ⟨v, hv, hk⟩
    exact ⟨v, ha.fout_val hG ▸ hv,
      ih (FVal.fresh v b) v hD (b + 1) (fupd ρ b v) (hG.freshOne v) m hk⟩
  | store hv ha _ ih =>
    intro hD b ρ hG m hw; dsimp only [wp, fold] at hw ⊢; rw [ha.fout_val hG, hv.fout_val hG]
    exact ⟨hw.1, ih hD b ρ hG _ hw.2⟩
  | call f hargs _ ih =>
    intro hD b ρ hG m hw; dsimp only [wp, fold] at hw ⊢; rcases hw with ⟨P, E, hΓ, hP, hE⟩
    rw [hargs.fout_vals hG]
    exact ⟨P, E, hΓ, fun r m' hp =>
      ih (freshFVals _ r b) r hD (b + _) (fupdTup ρ b r) (hG.freshFVals r) m' (hP r m' hp), hE⟩
  | @jnz G D c₁ c₂ t₁ t₂ e₁ e₂ hc _ _ iht ihe =>
    intro hD b ρ hG m hw; dsimp only [wp] at hw; have hcv := hc.fout_val hG; dsimp only [fold]
    cases hcf : c₁.fout with
    | imm bv =>
      rw [hcf] at hcv
      cases bv
      · exact ihe hD b ρ hG m (hw.2 hcv.symm)
      · exact iht hD b ρ hG m (hw.1 hcv.symm)
    | var _ =>
      rw [hcf] at hcv; dsimp only [wp]
      exact ⟨fun h => iht hD b ρ hG m (hw.1 (hcv ▸ h)), fun h => ihe hD b ρ hG m (hw.2 (hcv ▸ h))⟩
  | jump hj hargs =>
    intro hD b ρ hG m hw; have hj' := hD _ hj; dsimp only at hj'
    dsimp only [wp, fold] at hw ⊢; rw [hj', hargs.fout_vals hG]; exact hw
  | ret hvs | exit _ hvs =>
    intro _ b ρ hG m hw; dsimp only [wp, fold] at hw ⊢; rw [hvs.fout_vals hG]; exact hw
  | hlt => intro _ _ _ _ _ hw; exact hw
  | @group G D sig b₁ b₂ k₁ k₂ _ _ ihb ihk =>
    intro hD b ρ hG m hw; dsimp only [wp, fold] at hw ⊢; intro Js hclosed
    refine ihk Js Js (tup_zip_self_eq hD Js) b ρ hG m (hw Js ?_)
    rw [closed_iff] at hclosed ⊢; intro ts i xs m' hb
    have hfold := ihb Js Js i (freshFVals ts xs b) xs (tup_zip_self_eq hD Js)
      (b + ts.length) (fupdTup ρ b xs) (hG.freshFVals xs) m' hb
    rw [← foldB_get b (b₁ Js) i xs] at hfold; exact hclosed i xs m' hfold

/-- Well-formedness preservation for `fold`, proved via `Wf.induct`. -/
theorem fold_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx (FVal V₁) (FVal V₂)} {D : Ctx L₁ L₂}
    {e₁ : Expr (FVal V₁) L₁ rs} {e₂ : Expr (FVal V₂) L₂ rs}
    (hwf : Wf G D e₁ e₂) :
    ∀ {G' : Ctx V₁ V₂}, FRelG G' G → ∀ b, Wf G' D (fold b e₁) (fold b e₂) := by
  induction hwf using Wf.induct with
  | @let_ G D ts op₁ op₂ k₁ k₂ hop _ ih =>
    intro G' hG b
    cases hop with
    | @mk sig _ code args₁ args₂ hargs =>
      rw [fold_let, fold_let, OpRel.simpAct_eq hG hargs (code := code)]
      cases hact : ({ code := code, args := args₂ } : Op (FVal V₂) ts).simpAct with
      | some act => exact ih _ _ (hG.apply_simpAct hargs act) b
      | none =>
        have hpr := OpRel.simpProv?_rel hG hargs (code := code)
        cases hp₁ : ({ code := code, args := args₁ } : Op (FVal V₁) ts).simpProv? with
        | some res₁ =>
          cases hp₂ : ({ code := code, args := args₂ } : Op (FVal V₂) ts).simpProv? with
          | some res₂ => rw [hp₁, hp₂] at hpr; exact ih res₁ res₂ hpr b
          | none => rw [hp₁, hp₂] at hpr; exact False.elim hpr
        | none =>
          cases hp₂ : ({ code := code, args := args₂ } : Op (FVal V₂) ts).simpProv? with
          | some res₂ => rw [hp₁, hp₂] at hpr; exact False.elim hpr
          | none =>
            exact .let_ (OpRel.foldRewrite_rel hG hargs) fun xs₁ xs₂ =>
              ih _ _ (hG.foldWrap hargs b xs₁ xs₂) (b + ts.length)
  | load t ha _ ih =>
    intro _ hG b; exact .load t (ha.fout hG) fun v₁ v₂ => ih _ _ (hG.freshOne v₁ v₂ b) (b + 1)
  | store hv ha _ ih => intro _ hG b; exact .store (hv.fout hG) (ha.fout hG) (ih hG b)
  | call f hargs _ ih =>
    intro _ hG b
    exact .call f (TRel.fout hG hargs) fun xs₁ xs₂ => ih _ _ (hG.freshFVals xs₁ xs₂ b) (b + _)
  | @jnz G D c₁ c₂ t₁ t₂ e₁ e₂ hc _ _ iht ihe =>
    intro _ hG b; dsimp only [fold]
    cases hc with
    | @var v₁ v₂ h =>
      rcases v₁ with ⟨a₁, κ₁, ex₁, iv₁⟩; rcases v₂ with ⟨a₂, κ₂, ex₂, iv₂⟩
      obtain ⟨h', _, _, _⟩ := hG _ h; dsimp only at h' ⊢
      cases h' with
      | var hm => exact .jnz (.var hm) (iht hG b) (ihe hG b)
      | imm bv => cases bv <;> first | exact iht hG b | exact ihe hG b
    | imm bv => cases bv <;> first | exact iht hG b | exact ihe hG b
  | jump hj hargs => intro _ hG _; exact .jump hj (TRel.fout hG hargs)
  | ret hvs => intro _ hG _; exact .ret (TRel.fout hG hvs)
  | exit f hargs => intro _ hG _; exact .exit f (TRel.fout hG hargs)
  | hlt => intro _ _ _; exact .hlt
  | @group G D sig b₁ b₂ k₁ k₂ _ _ ihb ihk =>
    intro _ hG b
    refine .group (fun Js₁ Js₂ => WfB.of_get fun i xs₁ xs₂ => ?_) (fun Js₁ Js₂ => ihk Js₁ Js₂ hG b)
    simpa [foldB_get] using ihb Js₁ Js₂ i _ _ (hG.freshFVals xs₁ xs₂ b) (b + _)

/-! ## Closed functions -/

theorem Func.fold_wf {as rs : List Ty} {f : Func as rs} (hf : f.Wf) : (Func.fold f).Wf := by
  intro V₁ V₂ L₁ L₂ xs₁ xs₂
  have hwf := hf (FVal V₁) (FVal V₂) L₁ L₂ (freshFVals as xs₁ 0) (freshFVals as xs₂ 0)
  have hrel : FRelG (Tup.zip xs₁ xs₂)
      (Tup.zip (freshFVals as xs₁ 0) (freshFVals as xs₂ 0)) := by
    simpa using FRelG.freshFVals (G := []) (G' := []) (fun _ hp => nomatch hp) xs₁ xs₂ 0
  exact LeanQbe.T.fold_wf hwf hrel as.length

/-- Folding refines function contracts: any source contract holds on `Func.fold f`. -/
theorem Func.fold_spec {as rs : List Ty} {f : Func as rs} (hf : f.Wf) {Γ : Env}
    {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Func.spec Γ f xs m Q X) : Func.spec Γ (Func.fold f) xs m Q X := by
  have hwf := hf (FVal Val) Val Cont Cont (freshFVals as xs 0) xs
  have hgood : FGood (fupdTup (fun _ _ => default) 0 xs) as.length
      (Tup.zip (freshFVals as xs 0) xs) := by
    simpa using FGood.freshFVals (ρ := fun _ _ => default) (b := 0) (G := [])
      (fun _ hp => nomatch hp) xs
  exact LeanQbe.T.fold_wp hwf (fun _ hp => nomatch hp) as.length _ hgood m h

end LeanQbe.T


