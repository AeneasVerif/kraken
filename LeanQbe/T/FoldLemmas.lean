module

public import LeanQbe.T.Fold
public import LeanQbe.T.WPLemmas
public import LeanQbe.T.WfLemmas
public import LeanQbe.T.OpsLemmas

/-!
# Correctness of `fold` (`T6`)

* `OpCode.eval?_sound`: evaluating an immediate `OpCode` refines `OpCode.wp` (using `canonNaN` and
  `isFloatNaN_packedNaN` for nondeterministic float NaNs).
* `Op.rewrite_wp`: strength reductions (`mul → shl`, `udiv → lshr`, `urem → and`) refine `Op.wp`.
* `fold_wp`: source `wp` implies folded `wp`, proved via `Wf.induct`.
* `fold_wf`: `Wf` is preserved, proved via `Wf.induct`.
* `Func.fold_spec`, `Func.fold_wf`: closed-function specifications.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

/-! ## Valuation updates and key bounds -/

def FKey.fev (ρ : (t : Ty) → Nat → Val t) : {t : Ty} → FKey t → Val t
  | t, .var i => ρ t i
  | _, .imm c => c

def FKey.FLt (b : Nat) : {t : Ty} → FKey t → Prop
  | _, .var i => i < b
  | _, .imm _ => True

def fupd (ρ : (t : Ty) → Nat → Val t) {t : Ty} (b : Nat) (v : Val t) :
    (t' : Ty) → Nat → Val t' :=
  fun t' i => if i = b then match tyDecEq t t' with | isTrue h => h ▸ v | isFalse _ => ρ t' i
    else ρ t' i

def fupdTup (ρ : (t : Ty) → Nat → Val t) (b : Nat) :
    {ts : List Ty} → Tup Val ts → (t' : Ty) → Nat → Val t'
  | [], (), t', i => ρ t' i
  | _ :: _, (x, xs), t', i => fupdTup (fupd ρ b x) (b + 1) xs t' i

theorem fupd_eq (ρ : (t : Ty) → Nat → Val t) {t : Ty} (b : Nat) (v : Val t) :
    fupd ρ b v t b = v := by
  simp only [fupd, ↓reduceIte]
  cases h : tyDecEq t t with
  | isTrue _ => rfl
  | isFalse hne => exact absurd rfl hne

theorem fupd_ne (ρ : (t : Ty) → Nat → Val t) {t t' : Ty} {b i : Nat} (v : Val t) (h : i ≠ b) :
    fupd ρ b v t' i = ρ t' i := by
  simp [fupd, h]

theorem fupdTup_lt (ρ : (t : Ty) → Nat → Val t) :
    {ts : List Ty} → (xs : Tup Val ts) → {b : Nat} → {t' : Ty} → {i : Nat} →
    i < b → fupdTup ρ b xs t' i = ρ t' i
  | [], (), _, _, _, _ => rfl
  | _ :: _, (x, xs), b, t', i, hi => by
    simp only [fupdTup]
    rw [fupdTup_lt (fupd ρ b x) xs (by omega)]
    exact fupd_ne ρ x (by omega)

theorem FKey.FLt.mono {b : Nat} {t : Ty} {κ : FKey t} (h : κ.FLt b) : κ.FLt (b + 1) := by
  cases κ with
  | var i => exact Nat.lt_succ_of_lt h
  | imm _ => trivial

theorem FKey.FLt.add {b k : Nat} {t : Ty} {κ : FKey t} (h : κ.FLt b) : κ.FLt (b + k) := by
  cases κ with
  | var i => exact Nat.lt_of_lt_of_le h (Nat.le_add_right b k)
  | imm _ => trivial

theorem FKey.fev_fupd {ρ : (t : Ty) → Nat → Val t} {b : Nat} {u : Ty} (v : Val u)
    {t : Ty} {κ : FKey t} (h : κ.FLt b) :
    κ.fev (fupd ρ b v) = κ.fev ρ := by
  cases κ with
  | var i => exact fupd_ne ρ v (Nat.ne_of_lt h)
  | imm _ => rfl

theorem FKey.fev_fupdTup {ρ : (t : Ty) → Nat → Val t} {b : Nat}
    {ts : List Ty} (xs : Tup Val ts) {t : Ty} {κ : FKey t} (h : κ.FLt b) :
    κ.fev (fupdTup ρ b xs) = κ.fev ρ := by
  cases κ with
  | var i => exact fupdTup_lt ρ xs h
  | imm _ => rfl

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
      simp only [evalFloat1, Option.some.injEq] at hr; subst hr
      exact evalFloatLeaf_sound f _ hw)
    (fun s u a₁ a₂ _ hm r hr => by
      simp only [evalFloat1, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
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
      simp only [evalFloat2, Option.some.injEq] at hr; subst hr
      exact evalFloatLeaf_sound f _ hw)
    (fun s u a₁ a₂ b₁ b₂ _ hm r hr => by
      simp only [evalFloat2, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
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
      simp only [evalFloat3, Option.some.injEq] at hr; subst hr
      exact evalFloatLeaf_sound f _ hw)
    (fun s u a₁ a₂ b₁ b₂ c₁ c₂ _ hm r hr => by
      simp only [evalFloat3, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at hr
      rcases hr with ⟨r1, hr1, r2, hr2, rfl⟩
      exact hm r1 hr1 r2 hr2)
    t a b c post hw r hev

theorem evalConvertFloat_sound (src dst : Fmt) (b : BitVec src.width)
    {post : BitVec dst.width → Prop} (hw : convertFloat src dst b post) :
    post (evalConvertFloat src dst b) := by
  simp only [convertFloat] at hw
  simp only [evalConvertFloat]
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
  | _, _, .copy _, (_, ()), _, _, hev, hw
  | _, _, .not _, (_, ()), _, _, hev, hw
  | _, _, .clz _, (_, ()), _, _, hev, hw
  | _, _, .cls _, (_, ()), _, _, hev, hw
  | _, _, .rbit _, (_, ()), _, _, hev, hw
  | _, _, .ctz _, (_, ()), _, _, hev, hw
  | _, _, .popcnt _, (_, ()), _, _, hev, hw
  | _, _, .ofBool _, (_, ()), _, _, hev, hw
  | _, _, .unpair _ _, (_, ()), _, _, hev, hw
  | _, _, .bitcast _ _ _, (_, ()), _, _, hev, hw
  | _, _, .uitofp _ _, (_, ()), _, _, hev, hw
  | _, _, .sitofp _ _, (_, ()), _, _, hev, hw => by
    simp only [OpCode.eval?, Option.some.injEq] at hev; subst hev; exact hw
  | _, _, .and _, (_, _, ()), _, _, hev, hw
  | _, _, .or _, (_, _, ()), _, _, hev, hw
  | _, _, .xor _, (_, _, ()), _, _, hev, hw
  | _, _, .umulw _, (_, _, ()), _, _, hev, hw
  | _, _, .smulw _, (_, _, ()), _, _, hev, hw
  | _, _, .udiv0 _, (_, _, ()), _, _, hev, hw
  | _, _, .sdiv0 _, (_, _, ()), _, _, hev, hw
  | _, _, .mkpair _ _, (_, _, ()), _, _, hev, hw
  | _, _, .sha256msg1, (_, _, ()), _, _, hev, hw
  | _, _, .sha256msg2, (_, _, ()), _, _, hev, hw => by
    simp only [OpCode.eval?, Option.some.injEq] at hev; subst hev; exact hw
  | _, _, .ternlog _ _, (_, _, _, ()), _, _, hev, hw
  | _, _, .fshl _, (_, _, _, ()), _, _, hev, hw
  | _, _, .fshr _, (_, _, _, ()), _, _, hev, hw
  | _, _, .select _, (_, _, _, ()), _, _, hev, hw
  | _, _, .addc _, (_, _, _, ()), _, _, hev, hw
  | _, _, .subb _, (_, _, _, ()), _, _, hev, hw
  | _, _, .sha256rnds2, (_, _, _, ()), _, _, hev, hw => by
    simp only [OpCode.eval?, Option.some.injEq] at hev; subst hev; exact hw
  | _, _, .neg _, (_, ()), _, _, hev, hw
  | _, _, .bswap _, (_, ()), _, _, hev, hw
  | _, _, .zext _ _, (_, ()), _, _, hev, hw
  | _, _, .sext _ _, (_, ()), _, _, hev, hw
  | _, _, .trunc _ _, (_, ()), _, _, hev, hw
  | _, _, .shufd _ _, (_, ()), _, _, hev, hw
  | _, _, .fneg _, (_, ()), _, _, hev, hw
  | _, _, .fabs _, (_, ()), _, _, hev, hw => by
    simp only [OpCode.eval?] at hev; split at hev <;> simp_all [OpCode.wp]
  | _, _, .add _, (_, _, ()), _, _, hev, hw
  | _, _, .sub _, (_, _, ()), _, _, hev, hw
  | _, _, .mul _, (_, _, ()), _, _, hev, hw
  | _, _, .shl _, (_, _, ()), _, _, hev, hw
  | _, _, .lshr _, (_, _, ()), _, _, hev, hw
  | _, _, .ashr _, (_, _, ()), _, _, hev, hw
  | _, _, .rotl _, (_, _, ()), _, _, hev, hw
  | _, _, .rotr _, (_, _, ()), _, _, hev, hw
  | _, _, .udiv _, (_, _, ()), _, _, hev, hw
  | _, _, .sdiv _, (_, _, ()), _, _, hev, hw
  | _, _, .urem _, (_, _, ()), _, _, hev, hw
  | _, _, .srem _, (_, _, ()), _, _, hev, hw
  | _, _, .shufb _, (_, _, ()), _, _, hev, hw
  | _, _, .alignr _ _, (_, _, ()), _, _, hev, hw
  | _, _, .blendw _ _, (_, _, ()), _, _, hev, hw => by
    simp only [OpCode.eval?] at hev; split at hev <;> simp_all [OpCode.wp]
  | _, _, .cmp _ t _ h, (_, _, ()), _, _, hev, hw => by
    subst h; simp only [OpCode.eval?, cast_eq] at hev; split at hev <;> simp_all [OpCode.wp_cmp]
  | _, _, .blend _ _ h, (_, _, _, ()), _, _, hev, hw => by
    subst h; simp only [OpCode.eval?, cast_eq, Option.some.injEq] at hev; subst hev; exact hw
  | _, _, .fcmp _ t _ h, (_, _, ()), _, _, hev, hw => by
    subst h; simp only [OpCode.eval?, cast_eq] at hev; split at hev <;> simp_all [OpCode.wp_fcmp]
  | _, _, .fadd t, (a, b, ()), _, post, hev, hw
  | _, _, .fsub t, (a, b, ()), _, post, hev, hw
  | _, _, .fmul t, (a, b, ()), _, post, hev, hw
  | _, _, .fdiv t, (a, b, ()), _, post, hev, hw => by
    simp only [OpCode.eval?, Option.map_eq_some_iff] at hev
    rcases hev with ⟨r, hr, rfl⟩
    by_cases hf : !t.isFloatTree
    · simp_all [OpCode.wp]
    · simp only [OpCode.wp, hf, Bool.false_eq_true, ↓reduceIte] at hw
      exact evalFloat2_sound _ t a b r (fun x => post (x, ())) hr hw
  | _, _, .ffma t, (a, b, c, ()), _, post, hev, hw => by
    simp only [OpCode.eval?, Option.map_eq_some_iff] at hev
    rcases hev with ⟨r, hr, rfl⟩
    by_cases hf : !t.isFloatTree
    · simp only [OpCode.wp_ffma, hf, ↓reduceIte] at hw
    · simp only [OpCode.wp_ffma, hf, Bool.false_eq_true, ↓reduceIte] at hw
      exact evalFloat3_sound _ t a b c r (fun x => post (x, ())) hr hw
  | _, _, .fsqrt t, (a, ()), _, post, hev, hw => by
    simp only [OpCode.eval?, Option.map_eq_some_iff] at hev
    rcases hev with ⟨r, hr, rfl⟩
    by_cases hf : !t.isFloatTree
    · simp only [OpCode.wp_fsqrt, hf, ↓reduceIte] at hw
    · simp only [OpCode.wp_fsqrt, hf, Bool.false_eq_true, ↓reduceIte] at hw
      exact evalFloat1_sound _ t a r (fun x => post (x, ())) hr hw
  | _, _, .fptoui f n, (a, ()), _, _, hev, hw => by
    simp only [OpCode.eval?, Option.bind_eq_some_iff] at hev
    simp only [OpCode.wp_fptoui] at hw
    rcases hev with ⟨z, hz, hres⟩
    simp only [hz] at hw
    split at hres
    · simp only [Option.some.injEq] at hres; subst hres; exact hw.2.2
    · cases hres
  | _, _, .fptosi f n, (a, ()), _, _, hev, hw => by
    simp only [OpCode.eval?] at hev
    simp only [OpCode.wp_fptosi] at hw
    split at hev
    · simp only [Option.bind_eq_some_iff] at hev
      rcases hev with ⟨z, hz, hres⟩
      simp only [hz] at hw
      split at hres
      · simp only [Option.some.injEq] at hres; subst hres; exact hw.2.2.2
      · cases hres
    · cases hev
  | _, _, .fcvt f g, (a, ()), _, _, hev, hw => by
    simp only [OpCode.eval?, Option.some.injEq] at hev
    subst hev
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

theorem isZeroArg?_eq {t : Ty} {a : Arg Val t} (h : isZeroArg? a = true) :
    a.val = zeroVal t := by
  cases a with
  | var _ => simp [isZeroArg?, Arg.imm?] at h
  | imm c => exact isZeroVal_eq t c h

theorem isOnesArg?_eq {t : Ty} {a : Arg Val t} (h : isOnesArg? a = true) :
    a.val = onesVal t := by
  cases a with
  | var _ => simp [isOnesArg?, Arg.imm?] at h
  | imm c => exact isOnesVal_eq t c h

theorem isOneArg?_eq {t : Ty} {a : Arg Val t} (h : isOneArg? a = true) :
    a.val = oneVal t := by
  cases a with
  | var _ => simp [isOneArg?, Arg.imm?] at h
  | imm c => exact isOneVal_eq t c h

private theorem lift2_nf (fbv : ∀ {n}, BitVec n → BitVec n → BitVec n)
    (fbool : Bool → Bool → Bool) (g h k : (t : Ty) → Val t → Val t) :
    ∀ (t : Ty), t.hasFloat = false → ∀ (x : Val t),
      (hbv : ∀ {n} (x : BitVec n), fbv (g (.bits n) x) (h (.bits n) x) = k (.bits n) x := by
        intros; simp [zeroVal, oneVal, onesVal]) →
      (hbool : ∀ x, fbool (g .bool x) (h .bool x) = k .bool x := by intro x; cases x <;> rfl) →
      (hg : ∀ s u x₁ x₂, g (.pair s u) (x₁, x₂) = (g s x₁, g u x₂) := by intros; rfl) →
      (hh : ∀ s u x₁ x₂, h (.pair s u) (x₁, x₂) = (h s x₁, h u x₂) := by intros; rfl) →
      (hk : ∀ s u x₁ x₂, k (.pair s u) (x₁, x₂) = (k s x₁, k u x₂) := by intros; rfl) →
      lift2 fbv fbool t (g t x) (h t x) = k t x
  | .bool, _, x, _, hbool, _, _, _ => hbool x
  | .bits _, _, x, hbv, _, _, _, _ => hbv x
  | .float _, hf, _, _, _, _, _, _ => by simp [Ty.hasFloat] at hf
  | .pair s u, hf, (x₁, x₂), hbv, hbool, hg, hh, hk => by
    simp only [Ty.hasFloat, Bool.or_eq_false_iff] at hf
    rw [hg, hh, hk]
    exact Prod.ext (lift2_nf fbv fbool g h k s hf.1 x₁ hbv hbool hg hh hk)
      (lift2_nf fbv fbool g h k u hf.2 x₂ hbv hbool hg hh hk)

private theorem lift2_eq (fbv : ∀ {n}, BitVec n → BitVec n → BitVec n)
    (fbool : Bool → Bool → Bool) (g h k : (t : Ty) → Val t → Val t) :
    ∀ (t : Ty) (x : Val t),
      (hbv : ∀ {n} (x : BitVec n), fbv (g (.bits n) x) (h (.bits n) x) = k (.bits n) x := by
        intros; simp [zeroVal, oneVal, onesVal]) →
      (hflt : ∀ {f} (x : BitVec f.width),
        fbv (g (.float f) x) (h (.float f) x) = k (.float f) x := by
        intros; simp [zeroVal, oneVal, onesVal]) →
      (hbool : ∀ x, fbool (g .bool x) (h .bool x) = k .bool x := by intro x; cases x <;> rfl) →
      (hg : ∀ s u x₁ x₂, g (.pair s u) (x₁, x₂) = (g s x₁, g u x₂) := by intros; rfl) →
      (hh : ∀ s u x₁ x₂, h (.pair s u) (x₁, x₂) = (h s x₁, h u x₂) := by intros; rfl) →
      (hk : ∀ s u x₁ x₂, k (.pair s u) (x₁, x₂) = (k s x₁, k u x₂) := by intros; rfl) →
      lift2 fbv fbool t (g t x) (h t x) = k t x
  | .bool, x, _, _, hbool, _, _, _ => hbool x
  | .bits _, x, hbv, _, _, _, _, _ => hbv x
  | .float _, x, _, hflt, _, _, _, _ => hflt x
  | .pair s u, (x₁, x₂), hbv, hflt, hbool, hg, hh, hk => by
    rw [hg, hh, hk]
    exact Prod.ext (lift2_eq fbv fbool g h k s x₁ hbv hflt hbool hg hh hk)
      (lift2_eq fbv fbool g h k u x₂ hbv hflt hbool hg hh hk)

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
        intro w x y z i _
        cases x[i] <;> cases y[i] <;> cases z[i] <;> simp [zeroVal, onesVal, ternaryLogicBool]) →
      (hflt : ∀ {f} (x y z : BitVec f.width) i (_ : i < f.width),
        (k (.float f) x y z)[i] = ternaryLogicBool x[i] y[i] z[i] c := by
        intro f x y z i _
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

theorem signExtend_self {n : Nat} (a : BitVec n) : a.signExtend n = a := by
  ext i hi
  simp only [BitVec.getElem_signExtend]
  have : ¬ n ≤ i := by omega
  simp [hi]

private theorem one_toNat_of_pos {n : Nat} (hn : 0 < n) : (1#n : BitVec n).toNat = 1 := by
  have hp : 1 < 2 ^ n := Nat.one_lt_two_pow (by omega)
  simpa [BitVec.toNat_ofNat] using Nat.mod_eq_of_lt hp

theorem div_one_of_pos {n : Nat} (_hn : 0 < n) (a : BitVec n) : a / 1#n = a := by
  simp

theorem mod_one_of_pos {n : Nat} (_hn : 0 < n) (a : BitVec n) : a % 1#n = 0#n := by
  simp

theorem one_ne_zero_of_pos {n : Nat} (hn : 0 < n) : (1#n : BitVec n) ≠ 0#n := by
  intro h
  have := congrArg BitVec.toNat h
  simp [one_toNat_of_pos hn] at this

theorem sdivDefined_one_of_one_lt {n : Nat} (hn : 1 < n) (a : BitVec n) :
    sdivDefined a 1#n = true := by
  have hne0 : (1#n : BitVec n) ≠ 0#n := one_ne_zero_of_pos (by omega)
  have hneAll : (1#n : BitVec n) ≠ BitVec.allOnes n := by
    intro h
    have h1 : (1#n : BitVec n).toNat = 1 := one_toNat_of_pos (by omega)
    have hall : (BitVec.allOnes n).toNat = 2 ^ n - 1 := BitVec.toNat_allOnes
    have hpow : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by decide
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hn
    have hnat := congrArg BitVec.toNat h
    rw [h1, hall] at hnat
    omega
  simp [sdivDefined, hne0, hneAll]

private theorem one_toInt_of_one_lt {n : Nat} (hn : 1 < n) : (1#n : BitVec n).toInt = 1 := by
  have hpowN : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by decide
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hn
  have hpowI : (4 : Int) ≤ ((2 ^ n : Nat) : Int) := by exact_mod_cast hpowN
  have h1nat : (1#n : BitVec n).toNat = 1 := one_toNat_of_pos (by omega)
  have hmod : (1 : Int) % ((2 ^ n : Nat) : Int) = 1 := Int.emod_eq_of_lt (by omega) (by omega)
  have h1 : (1#n : BitVec n) = BitVec.ofInt n 1 := by
    apply BitVec.eq_of_toNat_eq
    rw [h1nat, BitVec.toNat_ofInt]
    exact_mod_cast hmod.symm
  rw [h1, BitVec.toInt_ofInt]
  unfold Int.bmod
  rw [hmod]
  dsimp only
  split <;> omega

theorem sdiv_one_of_one_lt {n : Nat} (hn : 1 < n) (a : BitVec n) : a.sdiv 1#n = a := by
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_sdiv, one_toInt_of_one_lt hn, Int.tdiv_one, ← BitVec.toInt_ofInt,
    BitVec.ofInt_toInt]

theorem srem_one_of_one_lt {n : Nat} (_hn : 1 < n) (a : BitVec n) : a.srem 1#n = 0#n := by
  simp

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

theorem lift2_mul_comm : ∀ (t : Ty) (a b : Val t),
    t.hasFloat = false → lift2 (· * ·) (· && ·) t a b = lift2 (· * ·) (· && ·) t b a
  | .bool, a, b, _ => Bool.and_comm a b
  | .bits _, a, b, _ => BitVec.mul_comm a b
  | .float _, _, _, hf => by simp [Ty.hasFloat] at hf
  | .pair t1 t2, (a1, a2), (b1, b2), hf => by
    simp only [Ty.hasFloat, Bool.or_eq_false_iff] at hf
    exact Prod.ext (lift2_mul_comm t1 a1 b1 hf.1) (lift2_mul_comm t2 a2 b2 hf.2)

theorem leafPow2Shift?_mul_l (t : Ty) (a c s : Val t)
    (hf : t.hasFloat = false) (hs : leafPow2Shift? t c = some s) :
    lift2 (fun {n} x y => x <<< (y.toNat % n)) (fun x _ => x) t a s =
      lift2 (· * ·) (· && ·) t c a := by
  rw [leafPow2Shift?_mul_r t a c s hf hs, lift2_mul_comm t a c hf]

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
    rcases args with ⟨a, b, ⟨⟩⟩; intro hw; simp only [Op.rewrite]
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
    rcases args with ⟨a, b, ⟨⟩⟩; intro hw; simp only [Op.rewrite]
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

/-! ## Context invariants and `SimpAct` soundness -/

/-- Every input variable in `G` has an output operand and key evaluating to the source value. -/
def FGood (ρ : (t : Ty) → Nat → Val t) (b : Nat) (G : Ctx (FVal Val) Val) : Prop :=
  ∀ p ∈ G, p.2.1.1.val = p.2.2 ∧ p.2.1.2.fev ρ = p.2.2 ∧ p.2.1.2.FLt b

theorem FGood.cons {ρ : (t : Ty) → Nat → Val t} {b : Nat} {G : Ctx (FVal Val) Val}
    (hG : FGood ρ b G) {t : Ty} {r : FVal Val t} {v : Val t}
    (h1 : r.1.val = v) (h2 : r.2.fev ρ = v) (h3 : r.2.FLt b) :
    FGood ρ b (⟨t, r, v⟩ :: G)
  | _, .head _ => ⟨h1, h2, h3⟩
  | _, .tail _ hp => hG _ hp

theorem FGood.upd_all {ρ : (t : Ty) → Nat → Val t} {b : Nat} {G : Ctx (FVal Val) Val}
    (hG : FGood ρ b G) {ts : List Ty} (xs : Tup Val ts) :
    FGood (fupdTup ρ b xs) (b + ts.length) G := by
  intro p hp
  obtain ⟨h1, h2, h3⟩ := hG p hp
  exact ⟨h1, (FKey.fev_fupdTup xs h3).trans h2, h3.add⟩

theorem FGood.append {ρ : (t : Ty) → Nat → Val t} {b : Nat} {G₁ G₂ : Ctx (FVal Val) Val}
    (h1 : FGood ρ b G₁) (h2 : FGood ρ b G₂) : FGood ρ b (G₁ ++ G₂) := by
  intro p hp
  rcases List.mem_append.1 hp with hp | hp
  · exact h1 p hp
  · exact h2 p hp

private theorem FGood.freshFVals_only (ρ : (t : Ty) → Nat → Val t) :
    {ts : List Ty} → (xs : Tup Val ts) → (b : Nat) →
    FGood (fupdTup ρ b xs) (b + ts.length) (Tup.zip (freshFVals ts xs b) xs)
  | [], (), _ => fun _ hp => nomatch hp
  | t :: ts, (x, xs), b => by
    simp only [freshFVals, tupFreshWith, Tup.zip, fupdTup, List.length_cons]
    intro p hp
    cases hp with
    | head =>
      refine ⟨rfl, ?_, by simp [FKey.FLt]⟩
      simp only [FKey.fev]
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
    FGood (fupd ρ b v) (b + 1) (⟨t, (.var v, .var b), v⟩ :: G) :=
  (hG.upd_all (ts := [t]) (v, ())).cons rfl
    (by simp [FKey.fev, fupdTup, fupd_eq]) (Nat.lt_succ_self b)

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
  | .var h => (hG _ h).2.2
  | .imm _ => trivial

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
      | head => exact ⟨rfl, rfl, trivial⟩
      | tail _ hp => exact ih p hp
    | arg i =>
      have hi : ArgRel G r (as₁.get i) (as₂.get i) := TRel.get i has
      intro p hp
      cases hp with
      | head =>
        refine ⟨?_, ?_, ?_⟩
        · simpa [SimpAct.apply, SimpAct.vals, Arg.fpair, vals_get] using hi.fout_val hG
        · simpa [SimpAct.apply, SimpAct.vals, Arg.fpair, vals_get] using hi.fkey_ev hG
        · simpa [SimpAct.apply, SimpAct.vals, Arg.fpair] using hi.fkey_FLt hG
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
    {b : Nat} (hG : FGood ρ b G) {t : Ty} {b₁ : Arg (FVal Val) t} {a₂ b₂ : Arg Val t}
    (hb : ArgRel G t b₁ b₂) (f : ∀ {n}, BitVec n → BitVec n → BitVec n)
    (hf : ∀ {n} (x : BitVec n), f x 0#n = x)
    {act : SimpAct [t, t] [t]}
    (hact : (if !t.hasFloat && isZeroArg? b₁.fout then some (.arg .here, ()) else none) =
      some act)
    {P : Tup Val [t] → Prop}
    (hw : if t.hasFloat then False else P (lift2 f (fun x _ => x) t a₂.val b₂.val, ())) :
    P (SimpAct.vals (vals (a₂, b₂, ())) act) := by
  split at hact
  · rename_i hcond; cases hact
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcond
    have hz := hb.isZero hG hcond.2
    have hsh := lift2_nf f (fun x _ => x) (fun _ x => x) (fun t _ => zeroVal t)
      (fun _ x => x) t hcond.1 a₂.val (fun x => hf x) (fun _ => rfl)
    simpa [SimpAct.vals, Tup.get, hcond.1, vals, hz, hsh] using hw
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
    · have ha0 := ha.isZero hG haz
      simpa [SimpAct.vals, vals, ha0, zeroVal, hhi0l] using hw
    · have hb0 := hb.isZero hG hbz
      simpa [SimpAct.vals, vals, hb0, zeroVal, hhi0r] using hw
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
  · rename_i hcond; cases hact
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hcond
    rw [hb.fout_imm?_val hG hcond.2, hop hcond.1] at hw
    exact hw
  · cases hact

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
  unfold Op.simpAct at hact
  dsimp only at hact
  cases hconst : (tupImms? (tupMapArg (fun _ => Arg.fout) args₁)).bind code.eval? with
    | some res =>
      rw [hconst] at hact; cases hact
      simp only [Option.bind_eq_some_iff] at hconst
      rcases hconst with ⟨cs, hcs, hev⟩
      have hvals : vals args₂ = cs :=
        (TRel.fout_vals hG hargs).symm.trans (tupImms?_vals hcs)
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
          split at hact
          · rename_i hbz; cases hact
            have h := lift2_nf (· + ·) (· ^^ ·) (fun _ x => x) (fun t _ => zeroVal t)
              (fun _ x => x) t hf0 a₂.val
            simpa [SimpAct.vals, Tup.get, OpCode.wp_add, hf0, vals, hb.isZero hG hbz, h] using hw
          · split at hact
            · rename_i haz; cases hact
              have h := lift2_nf (· + ·) (· ^^ ·) (fun t _ => zeroVal t) (fun _ x => x)
                (fun _ x => x) t hf0 b₂.val
              simpa [SimpAct.vals, Tup.get, OpCode.wp_add, hf0, vals, ha.isZero hG haz, h] using hw
            · cases hact
      | sub t =>
        rcases args₂ with ⟨a₂, b₂, ⟨⟩⟩; rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩; dsimp only at hact
        split at hact
        · cases hact
        · rename_i hnf; have hf0 : t.hasFloat = false := Bool.eq_false_iff.mpr hnf
          split at hact
          · rename_i heq; cases hact
            have hveq := ha.fkey_beq_val hG hb heq
            have h := lift2_nf (· - ·) (· ^^ ·) (fun _ x => x) (fun _ x => x)
              (fun t _ => zeroVal t) t hf0 b₂.val
            simpa [SimpAct.vals, Tup.get, OpCode.wp_sub, hf0, vals, hveq, h] using hw
          · split at hact
            · rename_i hbz; cases hact
              have h := lift2_nf (· - ·) (· ^^ ·) (fun _ x => x) (fun t _ => zeroVal t)
                (fun _ x => x) t hf0 a₂.val
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
            · have h := lift2_nf (· * ·) (· && ·) (fun t _ => zeroVal t) (fun _ x => x)
                (fun t _ => zeroVal t) t hf0 b₂.val
              simpa [SimpAct.vals, Tup.get, OpCode.wp_mul, hf0, vals, ha.isZero hG haz, h] using hw
            · have h := lift2_nf (· * ·) (· && ·) (fun _ x => x) (fun t _ => zeroVal t)
                (fun t _ => zeroVal t) t hf0 a₂.val
              simpa [SimpAct.vals, Tup.get, OpCode.wp_mul, hf0, vals, hb.isZero hG hbz, h] using hw
          · split at hact
            · rename_i hbo; cases hact
              have h := lift2_nf (· * ·) (· && ·) (fun _ x => x) (fun t _ => oneVal t)
                (fun _ x => x) t hf0 a₂.val
              simpa [SimpAct.vals, Tup.get, OpCode.wp_mul, hf0, vals, hb.isOne hG hbo, h] using hw
            · split at hact
              · rename_i hao; cases hact
                have h := lift2_nf (· * ·) (· && ·) (fun t _ => oneVal t) (fun _ x => x)
                  (fun _ x => x) t hf0 b₂.val
                simpa [SimpAct.vals, Tup.get, OpCode.wp_mul, hf0, vals, ha.isOne hG hao, h] using hw
              · cases hact
      | neg t =>
        cases t with
        | bool => rcases hargs with _ | ⟨ha, _⟩; cases hact; exact hw
        | _ => cases hact
      | and t =>
        rcases args₂ with ⟨a₂, b₂, ⟨⟩⟩; rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩; dsimp only at hact
        split at hact
        · rename_i hor0; cases hact
          rcases Bool.or_eq_true_iff.1 hor0 with haz | hbz
          · have h := lift2_eq (· &&& ·) (· && ·) (fun t _ => zeroVal t) (fun _ x => x)
              (fun t _ => zeroVal t) t b₂.val
            simpa [SimpAct.vals, Tup.get, OpCode.wp_and, vals, ha.isZero hG haz, h] using hw
          · have h := lift2_eq (· &&& ·) (· && ·) (fun _ x => x) (fun t _ => zeroVal t)
              (fun t _ => zeroVal t) t a₂.val
            simpa [SimpAct.vals, Tup.get, OpCode.wp_and, vals, hb.isZero hG hbz, h] using hw
        · split at hact
          · rename_i hbo; cases hact
            have h := lift2_eq (· &&& ·) (· && ·) (fun _ x => x) (fun t _ => onesVal t)
              (fun _ x => x) t a₂.val
            simpa [SimpAct.vals, Tup.get, OpCode.wp_and, vals, hb.isOnes hG hbo, h] using hw
          · split at hact
            · rename_i hao; cases hact
              have h := lift2_eq (· &&& ·) (· && ·) (fun t _ => onesVal t) (fun _ x => x)
                (fun _ x => x) t b₂.val
              simpa [SimpAct.vals, Tup.get, OpCode.wp_and, vals, ha.isOnes hG hao, h] using hw
            · split at hact
              · rename_i heq; cases hact
                have hveq := ha.fkey_beq_val hG hb heq
                have h := lift2_eq (· &&& ·) (· && ·) (fun _ x => x) (fun _ x => x)
                  (fun _ x => x) t b₂.val
                simpa [SimpAct.vals, Tup.get, OpCode.wp_and, vals, hveq, h] using hw
              · cases hact
      | or t =>
        rcases args₂ with ⟨a₂, b₂, ⟨⟩⟩; rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩; dsimp only at hact
        split at hact
        · rename_i hor0; cases hact
          rcases Bool.or_eq_true_iff.1 hor0 with hao | hbo
          · have h := lift2_eq (· ||| ·) (· || ·) (fun t _ => onesVal t) (fun _ x => x)
              (fun t _ => onesVal t) t b₂.val
            simpa [SimpAct.vals, Tup.get, OpCode.wp_or, vals, ha.isOnes hG hao, h] using hw
          · have h := lift2_eq (· ||| ·) (· || ·) (fun _ x => x) (fun t _ => onesVal t)
              (fun t _ => onesVal t) t a₂.val
            simpa [SimpAct.vals, Tup.get, OpCode.wp_or, vals, hb.isOnes hG hbo, h] using hw
        · split at hact
          · rename_i hbz; cases hact
            have h := lift2_eq (· ||| ·) (· || ·) (fun _ x => x) (fun t _ => zeroVal t)
              (fun _ x => x) t a₂.val
            simpa [SimpAct.vals, Tup.get, OpCode.wp_or, vals, hb.isZero hG hbz, h] using hw
          · split at hact
            · rename_i haz; cases hact
              have h := lift2_eq (· ||| ·) (· || ·) (fun t _ => zeroVal t) (fun _ x => x)
                (fun _ x => x) t b₂.val
              simpa [SimpAct.vals, Tup.get, OpCode.wp_or, vals, ha.isZero hG haz, h] using hw
            · split at hact
              · rename_i heq; cases hact
                have hveq := ha.fkey_beq_val hG hb heq
                have h := lift2_eq (· ||| ·) (· || ·) (fun _ x => x) (fun _ x => x)
                  (fun _ x => x) t b₂.val
                simpa [SimpAct.vals, Tup.get, OpCode.wp_or, vals, hveq, h] using hw
              · cases hact
      | xor t =>
        rcases args₂ with ⟨a₂, b₂, ⟨⟩⟩; rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩; dsimp only at hact
        split at hact
        · rename_i heq; cases hact
          have hveq := ha.fkey_beq_val hG hb heq
          have h := lift2_eq (· ^^^ ·) (· ^^ ·) (fun _ x => x) (fun _ x => x)
            (fun t _ => zeroVal t) t b₂.val
          simpa [SimpAct.vals, Tup.get, OpCode.wp_xor, vals, hveq, h] using hw
        · split at hact
          · rename_i hbz; cases hact
            have h := lift2_eq (· ^^^ ·) (· ^^ ·) (fun _ x => x) (fun t _ => zeroVal t)
              (fun _ x => x) t a₂.val
            simpa [SimpAct.vals, Tup.get, OpCode.wp_xor, vals, hb.isZero hG hbz, h] using hw
          · split at hact
            · rename_i haz; cases hact
              have h := lift2_eq (· ^^^ ·) (· ^^ ·) (fun t _ => zeroVal t) (fun _ x => x)
                (fun _ x => x) t b₂.val
              simpa [SimpAct.vals, Tup.get, OpCode.wp_xor, vals, ha.isZero hG haz, h] using hw
            · cases hact
      | ternlog t imm =>
        rcases args₂ with ⟨a₂, b₂, c₂, ⟨⟩⟩
        rcases hargs with _ | ⟨ha, _ | ⟨hb, _ | ⟨hc, _⟩⟩⟩; dsimp only at hact
        split at hact
        · rename_i himm; cases hact
          have h := ternlog_simp_eq imm 0#8 himm (fun t _ _ _ => zeroVal t) t a₂.val b₂.val c₂.val
          simpa [SimpAct.vals, Tup.get, OpCode.wp_ternlog, vals, h] using hw
        · split at hact
          · rename_i himm; cases hact
            have h := ternlog_simp_eq imm 0xff#8 himm (fun t _ _ _ => onesVal t)
              t a₂.val b₂.val c₂.val
            simpa [SimpAct.vals, Tup.get, OpCode.wp_ternlog, vals, h] using hw
          · split at hact
            · rename_i himm; cases hact
              have h := ternlog_simp_eq imm 0xf0#8 himm (fun _ a _ _ => a) t a₂.val b₂.val c₂.val
              simpa [SimpAct.vals, Tup.get, OpCode.wp_ternlog, vals, h] using hw
            · split at hact
              · rename_i himm; cases hact
                have h := ternlog_simp_eq imm 0xcc#8 himm (fun _ _ b _ => b)
                  t a₂.val b₂.val c₂.val
                simpa [SimpAct.vals, Tup.get, OpCode.wp_ternlog, vals, h] using hw
              · split at hact
                · rename_i himm; cases hact
                  have h := ternlog_simp_eq imm 0xaa#8 himm (fun _ _ _ c => c)
                    t a₂.val b₂.val c₂.val
                  simpa [SimpAct.vals, Tup.get, OpCode.wp_ternlog, vals, h] using hw
                · cases hact
      | shl t =>
        rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩; dsimp only at hact
        exact simpAct_shift_zero hG hb (fun {n} x y => x <<< (y.toNat % n)) (fun x => by simp)
          hact (by simpa [OpCode.wp_shl, vals] using hw)
      | lshr t =>
        rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩; dsimp only at hact
        exact simpAct_shift_zero hG hb (fun {n} x y => x >>> (y.toNat % n)) (fun x => by simp)
          hact (by simpa [OpCode.wp_lshr, vals] using hw)
      | ashr t =>
        rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩; dsimp only at hact
        exact simpAct_shift_zero hG hb (fun {n} x y => x.sshiftRight (y.toNat % n))
          (fun x => by simp) hact (by simpa [OpCode.wp_ashr, vals] using hw)
      | rotl t =>
        rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩; dsimp only at hact
        exact simpAct_shift_zero hG hb (fun {n} x y => x.rotateLeft (y.toNat % n))
          (fun x => by ext i _; simp [BitVec.rotateLeft, BitVec.rotateLeftAux])
          hact (by simpa [OpCode.wp_rotl, vals] using hw)
      | rotr t =>
        rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩; dsimp only at hact
        exact simpAct_shift_zero hG hb (fun {n} x y => x.rotateRight (y.toNat % n))
          (fun x => by ext i _; simp [BitVec.rotateRight, BitVec.rotateRightAux])
          hact (by simpa [OpCode.wp_rotr, vals] using hw)
      | cmp o t _ h =>
        subst h; rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩; dsimp only at hact
        split at hact
        · rename_i hcond; cases hact
          simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcond
          have hveq := ha.fkey_beq_val hG hb hcond.2
          simpa [SimpAct.vals, Tup.get, OpCode.wp_cmp, hcond.1, vals, hveq,
            liftCmp_self o t _ hcond.1] using hw
        · cases hact
      | select _ =>
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
          · cases hact
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
          simp only [SimpAct.vals, Tup.get, OpCode.wp, vals, cast_eq, BitVec.setWidth_eq] at hw ⊢
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

/-! ## `Wf` relations for `fold` -/

section
variable {V₁ V₂ : Ty → Type}

/-- Two `FVal` contexts are related when output operands satisfy `ArgRel G'` and keys match. -/
def FRelG (G' : Ctx V₁ V₂) (G : Ctx (FVal V₁) (FVal V₂)) : Prop :=
  ∀ p ∈ G, ArgRel G' p.1 p.2.1.1 p.2.2.1 ∧ p.2.1.2 = p.2.2.2

variable {G' : Ctx V₁ V₂} {G : Ctx (FVal V₁) (FVal V₂)}

theorem FRelG.append (h1 : FRelG G' G) {H : Ctx (FVal V₁) (FVal V₂)} (h2 : FRelG G' H) :
    FRelG G' (H ++ G) := by
  intro p hp
  rcases List.mem_append.1 hp with hp | hp
  · exact h2 p hp
  · exact h1 p hp

theorem FRelG.weaken (hG : FRelG G' G) {G'' : Ctx V₁ V₂} (hsub : ∀ p ∈ G', p ∈ G'') :
    FRelG G'' G :=
  fun p hp => ⟨(hG p hp).1.weaken hsub, (hG p hp).2⟩

private theorem FRelG.freshFVals_only {ts : List Ty} (xs₁ : Tup V₁ ts) (xs₂ : Tup V₂ ts)
    (b : Nat) :
    FRelG (Tup.zip xs₁ xs₂) (Tup.zip (freshFVals ts xs₁ b) (freshFVals ts xs₂ b)) :=
  mem_tup_zip_tupFreshWith
    (fun {t} x n => ((.var x, .var n) : FVal V₁ t))
    (fun {t} x n => ((.var x, .var n) : FVal V₂ t))
    (P := fun G' _ w₁ w₂ => ArgRel G' _ w₁.1 w₂.1 ∧ w₁.2 = w₂.2)
    (fun hsub _ _ _ h => ⟨h.1.weaken hsub, h.2⟩)
    (fun _ _ _ => ⟨.var List.mem_cons_self, rfl⟩)
    xs₁ xs₂ b

theorem FRelG.freshFVals (hG : FRelG G' G) {ts : List Ty} (xs₁ : Tup V₁ ts) (xs₂ : Tup V₂ ts)
    (b : Nat) :
    FRelG (Tup.zip xs₁ xs₂ ++ G') (Tup.zip (freshFVals ts xs₁ b) (freshFVals ts xs₂ b) ++ G) :=
  (hG.weaken fun _ hq => List.mem_append_right _ hq).append
    ((FRelG.freshFVals_only xs₁ xs₂ b).weaken fun _ hq => List.mem_append_left G' hq)

theorem FRelG.freshOne (hG : FRelG G' G) {t : Ty} (v₁ : V₁ t) (v₂ : V₂ t) (b : Nat) :
    FRelG (⟨t, v₁, v₂⟩ :: G') (⟨t, (.var v₁, .var b), (.var v₂, .var b)⟩ :: G) := by
  intro p hp
  cases hp with
  | head => exact ⟨.var List.mem_cons_self, rfl⟩
  | tail _ hp => exact ⟨(hG p hp).1.weaken fun _ hq => List.mem_cons_of_mem _ hq, (hG p hp).2⟩

theorem ArgRel.imm?_eq {t : Ty} {a₁ : Arg V₁ t} {a₂ : Arg V₂ t} :
    ArgRel G' t a₁ a₂ → a₁.imm? = a₂.imm?
  | .var _ | .imm _ => rfl

theorem ArgRel.isZero_eq {t : Ty} {a₁ : Arg V₁ t} {a₂ : Arg V₂ t} (h : ArgRel G' t a₁ a₂) :
    isZeroArg? a₁ = isZeroArg? a₂ := by
  simp [isZeroArg?, h.imm?_eq]

theorem ArgRel.isOnes_eq {t : Ty} {a₁ : Arg V₁ t} {a₂ : Arg V₂ t} (h : ArgRel G' t a₁ a₂) :
    isOnesArg? a₁ = isOnesArg? a₂ := by
  simp [isOnesArg?, h.imm?_eq]

theorem ArgRel.isOne_eq {t : Ty} {a₁ : Arg V₁ t} {a₂ : Arg V₂ t} (h : ArgRel G' t a₁ a₂) :
    isOneArg? a₁ = isOneArg? a₂ := by
  simp [isOneArg?, h.imm?_eq]

theorem ArgRel.fout (hG : FRelG G' G) {t : Ty} {a₁ : Arg (FVal V₁) t} {a₂ : Arg (FVal V₂) t} :
    ArgRel G t a₁ a₂ → ArgRel G' t a₁.fout a₂.fout
  | .var h => (hG _ h).1
  | .imm c => .imm c

theorem ArgRel.fkey_eq (hG : FRelG G' G) {t : Ty} {a₁ : Arg (FVal V₁) t} {a₂ : Arg (FVal V₂) t} :
    ArgRel G t a₁ a₂ → a₁.fkey = a₂.fkey
  | .var h => (hG _ h).2
  | .imm _ => rfl

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
  unfold Op.simpAct
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
    | cmp _ _ _ _ | udiv _ | sdiv _ | urem _ | srem _ | udiv0 _ | sdiv0 _
    | umulw _ | smulw _ =>
      rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩
      have ha' := ha.fout hG
      have hb' := hb.fout hG
      simp only [ha'.isZero_eq, hb'.isZero_eq, ha'.isOnes_eq, hb'.isOnes_eq,
        ha'.isOne_eq, hb'.isOne_eq, hb'.imm?_eq, ha.fkey_eq hG, hb.fkey_eq hG]
    | select _ | blend _ _ _ | addc _ | subb _ =>
      rcases hargs with _ | ⟨ha, _ | ⟨hb, _ | ⟨hc, _⟩⟩⟩
      have ha' := ha.fout hG
      have hb' := hb.fout hG
      have hc' := hc.fout hG
      simp only [ha'.isZero_eq, hb'.isZero_eq, ha'.imm?_eq, hc'.imm?_eq,
        ha.fkey_eq hG, hb.fkey_eq hG, hc.fkey_eq hG]
    | _ => rfl

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
      | head => exact ⟨.imm c, rfl⟩
      | tail _ hp => exact ih p hp
    | arg i =>
      have hi : ArgRel G r (as₁.get i) (as₂.get i) := TRel.get i has
      intro p hp
      cases hp with
      | head => exact ⟨hi.fout hG, hi.fkey_eq hG⟩
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
      rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩; simp only [Op.rewrite]
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
      rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩; simp only [Op.rewrite]
      cases hb with
      | @var _ _ hmb => exact .mk _ (.cons ha (.cons (.var hmb) .nil))
      | imm cb =>
        simp only [Arg.imm?, Option.bind_some]
        cases findPow2 n cb n with
        | some m => exact .mk _ (.cons ha (.cons (.imm _) .nil))
        | none => exact .mk _ (.cons ha (.cons (.imm cb) .nil))
    | _ => exact .mk _ hargs

end

/-! ## Block projection helper and `Wf.induct` correctness proofs -/

theorem foldB_get {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} (b : Nat) :
    {sig : List (List Ty)} → {ts : List Ty} → (bs : Blocks (FVal V) L rs sig) →
    (i : Member ts sig) → (xs : Tup V ts) →
    (foldB b bs).get i xs = fold (b + ts.length) (bs.get i (freshFVals ts xs b))
  | _, _, .cons _ _, .here, _ => rfl
  | _, _, .cons _ bs, .there i, xs => foldB_get b bs i xs

/-- Weakest-precondition preservation for `fold`, proved via `Wf.induct`. -/
theorem fold_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {G : Ctx (FVal Val) Val} {D : Ctx Cont Cont}
    {e₁ : Expr (FVal Val) Cont rs} {e₂ : Expr Val Cont rs}
    (hwf : Wf G D e₁ e₂) :
    (∀ p ∈ D, p.2.1 = p.2.2) →
    ∀ b ρ, FGood ρ b G → ∀ m, wp Γ Q X e₂ m → wp Γ Q X (fold b e₁) m := by
  induction hwf using Wf.induct with
  | @let_ G D ts op₁ op₂ k₁ k₂ hop _ ih =>
    intro hD b ρ hG m hw
    simp only [wp] at hw
    cases hop with
    | @mk sig _ code args₁ args₂ hargs =>
      simp only [fold]
      cases hact : ({ code := code, args := args₁ } : Op (FVal Val) ts).simpAct with
      | some act =>
        obtain ⟨hk2, hfg⟩ := OpRel.simpAct_sound hG hargs hact hw
        exact ih (act.apply args₁) (SimpAct.vals (vals args₂) act) hD b ρ hfg m hk2
      | none =>
        simp only [wp]
        have hw' : (⟨code, tupMapArg (fun _ => Arg.fout) args₁⟩ : Op Val ts).rewrite.wp
            (fun xs => wp Γ Q X (k₂ xs) m) :=
          Op.rewrite_wp _ _ ((OpRel.mk code hargs).fout_wp hG hw)
        exact Op.wp_mono (fun xs hxs =>
          ih (freshFVals ts xs b) xs hD (b + ts.length) (fupdTup ρ b xs)
            (hG.freshFVals xs) m hxs) hw'
  | load t ha _ ih =>
    intro hD b ρ hG m hw
    simp only [wp, fold] at hw ⊢
    rcases hw with ⟨v, hv, hk⟩
    exact ⟨v, ha.fout_val hG ▸ hv,
      ih (.var v, .var b) v hD (b + 1) (fupd ρ b v) (hG.freshOne v) m hk⟩
  | store hv ha _ ih =>
    intro hD b ρ hG m hw
    simp only [wp, fold] at hw ⊢
    rw [ha.fout_val hG, hv.fout_val hG]
    exact ⟨hw.1, ih hD b ρ hG _ hw.2⟩
  | call f hargs _ ih =>
    intro hD b ρ hG m hw
    simp only [wp, fold] at hw ⊢
    rcases hw with ⟨P, E, hΓ, hP, hE⟩
    rw [hargs.fout_vals hG]
    exact ⟨P, E, hΓ, fun r m' hp =>
      ih (freshFVals _ r b) r hD (b + _) (fupdTup ρ b r) (hG.freshFVals r) m' (hP r m' hp), hE⟩
  | @jnz G D c₁ c₂ t₁ t₂ e₁ e₂ hc _ _ iht ihe =>
    intro hD b ρ hG m hw
    simp only [wp] at hw
    have hcv := hc.fout_val hG
    simp only [fold]
    cases hcf : c₁.fout with
    | imm bv =>
      rw [hcf] at hcv
      cases bv
      · exact ihe hD b ρ hG m (hw.2 hcv.symm)
      · exact iht hD b ρ hG m (hw.1 hcv.symm)
    | var v =>
      rw [hcf] at hcv
      simp only [wp]
      exact ⟨fun h => iht hD b ρ hG m (hw.1 (hcv ▸ h)), fun h => ihe hD b ρ hG m (hw.2 (hcv ▸ h))⟩
  | jump hj hargs =>
    intro hD b ρ hG m hw
    have hj' := hD _ hj; dsimp only at hj'
    simp only [wp, fold] at hw ⊢
    rw [hj', hargs.fout_vals hG]
    exact hw
  | ret hvs =>
    intro _ b ρ hG m hw
    simp only [wp, fold] at hw ⊢
    rw [hvs.fout_vals hG]
    exact hw
  | exit f hargs =>
    intro _ b ρ hG m hw
    simp only [wp, fold] at hw ⊢
    rw [hargs.fout_vals hG]
    exact hw
  | hlt =>
    intro _ _ _ _ _ hw
    exact hw
  | @group G D sig b₁ b₂ k₁ k₂ _ _ ihb ihk =>
    intro hD b ρ hG m hw
    simp only [wp, fold] at hw ⊢
    intro Js hclosed
    refine ihk Js Js (tup_zip_self_eq hD Js) b ρ hG m (hw Js ?_)
    rw [closed_iff] at hclosed ⊢
    intro ts i xs m' hb
    have hfold := ihb Js Js i (freshFVals ts xs b) xs (tup_zip_self_eq hD Js)
      (b + ts.length) (fupdTup ρ b xs) (hG.freshFVals xs) m' hb
    rw [← foldB_get b (b₁ Js) i xs] at hfold
    exact hclosed i xs m' hfold

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
      have hop' : OpRel G' ⟨code, tupMapArg (fun _ => Arg.fout) args₁⟩
          ⟨code, tupMapArg (fun _ => Arg.fout) args₂⟩ :=
        .mk code (TRel.fout hG hargs)
      have hact_eq := OpRel.simpAct_eq hG hargs (code := code)
      simp only [fold]
      rw [hact_eq]
      cases hact : ({ code := code, args := args₂ } : Op (FVal V₂) ts).simpAct with
      | some act =>
        exact ih _ _ (hG.apply_simpAct hargs act) b
      | none =>
        exact .let_ hop'.rewrite fun xs₁ xs₂ => ih _ _ (hG.freshFVals xs₁ xs₂ b) (b + ts.length)
  | load t ha _ ih =>
    intro G' hG b
    exact .load t (ha.fout hG) fun v₁ v₂ => ih _ _ (hG.freshOne v₁ v₂ b) (b + 1)
  | store hv ha _ ih =>
    intro G' hG b
    exact .store (hv.fout hG) (ha.fout hG) (ih hG b)
  | call f hargs _ ih =>
    intro G' hG b
    exact .call f (TRel.fout hG hargs) fun xs₁ xs₂ =>
      ih _ _ (hG.freshFVals xs₁ xs₂ b) (b + _)
  | @jnz G D c₁ c₂ t₁ t₂ e₁ e₂ hc _ _ iht ihe =>
    intro G' hG b
    simp only [fold]
    cases hc with
    | @var v₁ v₂ h =>
      rcases v₁ with ⟨a₁, κ₁⟩
      rcases v₂ with ⟨a₂, κ₂⟩
      obtain ⟨h', _⟩ := hG _ h
      dsimp only at h' ⊢
      cases h' with
      | var hm => exact .jnz (.var hm) (iht hG b) (ihe hG b)
      | imm bv => cases bv <;> first | exact iht hG b | exact ihe hG b
    | imm bv => cases bv <;> first | exact iht hG b | exact ihe hG b
  | jump hj hargs =>
    intro G' hG _
    exact .jump hj (TRel.fout hG hargs)
  | ret hvs =>
    intro G' hG _
    exact .ret (TRel.fout hG hvs)
  | exit f hargs =>
    intro G' hG _
    exact .exit f (TRel.fout hG hargs)
  | hlt =>
    intro _ _ _
    exact .hlt
  | @group G D sig b₁ b₂ k₁ k₂ _ _ ihb ihk =>
    intro G' hG b
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


