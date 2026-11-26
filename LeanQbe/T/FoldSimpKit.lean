module

public import LeanQbe.T.Fold
public import LeanQbe.T.OptUtilLemmas
import LeanQbe.T.OpsLemmas
import LeanQbe.T.PassEnvKit

/-!
# Fold Proof Simplification Kit

Standalone float, algebraic (`AlgebraicSimpKit`), bitvector, extension-chain (`ExtKind`),
comparison-bound (`CmpShapeLaw`), and `SimpAct` context-predicate helpers used privately by
`LeanQbe.T.FoldLemmas`. Zero exposed proof lemmas.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T

/-! ## Float evaluation helpers -/

theorem evalFloatLeaf_core (f : Fmt) (res : Float.Model.UnpackedFloat)
    {post : BitVec f.width → Prop} (hw : floatResultWp f res post) :
    post (if res.isNaN then canonNaN f else packFloat f res) := by
  simp only [floatResultWp] at hw
  split <;> rename_i hnan
  · simp only [hnan, ↓reduceIte] at hw; exact hw (canonNaN f) (isFloatNaN_packedNaN f)
  · simp only [hnan, Bool.false_eq_true, ↓reduceIte] at hw; exact hw

theorem evalFloat1_core
    (op : Float.Model.Format → Float.Model.UnpackedFloat → Float.Model.UnpackedFloat)
    (t : Ty) (a r : Val t) (post : Val t → Prop)
    (hev : evalFloat1 op t a = some r) (hw : liftFloatRel1 op t a post) : post r := by
  refine liftFloatRel1_pred op (fun t a P => ∀ r, evalFloat1 op t a = some r → P r)
    (fun _ _ _ _ h hp r hr => h r (hp r hr))
    (fun f a _ hw r hr => by
      dsimp only [evalFloat1] at hr; simp only [Option.some.injEq] at hr; subst hr
      exact evalFloatLeaf_core f _ hw)
    (fun s u a₁ a₂ _ hm r hr => by
      dsimp only [evalFloat1, Option.bind_eq_bind] at hr
      simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hr
      rcases hr with ⟨r1, hr1, r2, hr2, rfl⟩; exact hm r1 hr1 r2 hr2)
    t a post hw r hev

theorem evalFloat2_core
    (op : Float.Model.Format → Float.Model.UnpackedFloat →
      Float.Model.UnpackedFloat → Float.Model.UnpackedFloat)
    (t : Ty) (a b r : Val t) (post : Val t → Prop)
    (hev : evalFloat2 op t a b = some r) (hw : liftFloatRel2 op t a b post) : post r := by
  refine liftFloatRel2_pred op (fun t a b P => ∀ r, evalFloat2 op t a b = some r → P r)
    (fun _ _ _ _ _ h hp r hr => h r (hp r hr))
    (fun f a b _ hw r hr => by
      dsimp only [evalFloat2] at hr; simp only [Option.some.injEq] at hr; subst hr
      exact evalFloatLeaf_core f _ hw)
    (fun s u a₁ a₂ b₁ b₂ _ hm r hr => by
      dsimp only [evalFloat2, Option.bind_eq_bind] at hr
      simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hr
      rcases hr with ⟨r1, hr1, r2, hr2, rfl⟩; exact hm r1 hr1 r2 hr2)
    t a b post hw r hev

theorem evalFloat3_core
    (op : Float.Model.Format → Float.Model.UnpackedFloat →
      Float.Model.UnpackedFloat → Float.Model.UnpackedFloat → Float.Model.UnpackedFloat)
    (t : Ty) (a b c r : Val t) (post : Val t → Prop)
    (hev : evalFloat3 op t a b c = some r) (hw : liftFloatRel3 op t a b c post) : post r := by
  refine liftFloatRel3_pred op (fun t a b c P => ∀ r, evalFloat3 op t a b c = some r → P r)
    (fun _ _ _ _ _ _ h hp r hr => h r (hp r hr))
    (fun f a b c _ hw r hr => by
      dsimp only [evalFloat3] at hr; simp only [Option.some.injEq] at hr; subst hr
      exact evalFloatLeaf_core f _ hw)
    (fun s u a₁ a₂ b₁ b₂ c₁ c₂ _ hm r hr => by
      dsimp only [evalFloat3, Option.bind_eq_bind] at hr
      simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hr
      rcases hr with ⟨r1, hr1, r2, hr2, rfl⟩; exact hm r1 hr1 r2 hr2)
    t a b c post hw r hev

theorem evalConvertFloat_core (src dst : Fmt) (b : BitVec src.width)
    {post : BitVec dst.width → Prop} (hw : convertFloat src dst b post) :
    post (evalConvertFloat src dst b) := by
  simp only [convertFloat] at hw; dsimp only [evalConvertFloat]
  cases hu : unpackFloat src b with
  | notANumber => simp only [hu] at hw; exact hw (canonNaN dst) (isFloatNaN_packedNaN dst)
  | finite _ _ _ _ | infinity _ | zero _ => simp only [hu] at hw; exact hw

theorem float_eval?_sound {t : Ty} {res : Tup Val [t]} {post : Tup Val [t] → Prop}
    (ev : Option (Val t)) (h : ev.map (·, ()) = some res)
    (hguard : if !t.isFloatTree then False else ∀ r, ev = some r → post (r, ())) :
    post res := by
  simp only [Option.map_eq_some_iff] at h; rcases h with ⟨r, hr, rfl⟩
  by_cases hf : !t.isFloatTree
  · simp [hf] at hguard
  · simp only [hf, Bool.false_eq_true, ↓reduceIte] at hguard; exact hguard r hr

/-! ## `AlgebraicSimpKit`: tree lifting, ternlog, and strength reduction -/

theorem lift2_law (allowFlt : Bool) (fbv : ∀ {n}, BitVec n → BitVec n → BitVec n)
    (fbool : Bool → Bool → Bool) (g h k : (t : Ty) → Val t → Val t) :
    ∀ (t : Ty), (allowFlt = false → t.hasFloat = false) → ∀ (x : Val t),
      (hbv : ∀ {n} (x : BitVec n), fbv (g (.bits n) x) (h (.bits n) x) = k (.bits n) x := by
        intros; simp [zeroVal, oneVal, onesVal]) →
      (hflt : ∀ {f : Fmt} (x : BitVec f.width), allowFlt = true →
        fbv (g (.float f) x) (h (.float f) x) = k (.float f) x := by
        intro _ _ e; cases e) →
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
    simp only [Ty.hasFloat, Bool.or_eq_false_iff] at hnf; rw [hg, hh, hk]
    exact Prod.ext
      (lift2_law allowFlt fbv fbool g h k s (fun e => (hnf e).1) x₁ hbv hflt hbool hg hh hk)
      (lift2_law allowFlt fbv fbool g h k u (fun e => (hnf e).2) x₂ hbv hflt hbool hg hh hk)

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
    simp only [List.foldl_cons]; rw [ih]; congr 1
    cases hbit : imm.getLsbD k
    · simp
    · simp only [↓reduceIte, BitVec.getElem_or, BitVec.getElem_and,
        pick_getElem _ _ hi, Bool.true_and, Bool.and_assoc]

theorem ternaryLogic_getElem_core {w : Nat} (a b c : BitVec w) (imm : BitVec 8)
    (i : Nat) (hi : i < w) :
    (ternaryLogic a b c imm)[i] = ternaryLogicBool a[i] b[i] c[i] imm := by
  rw [ternaryLogic, ternaryLogic_foldl_getElem a b c imm hi]
  have hr : List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] := rfl
  rw [hr]; simp only [ternaryLogicBool, BitVec.getElem_zero, List.foldl_cons, List.foldl_nil]
  cases a[i] <;> cases b[i] <;> cases c[i] <;> simp

theorem ternlog_simp_eq (imm c : BitVec 8) (himm : (imm == c) = true)
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
    ext i hi; simp only [lift3]; rw [ternaryLogic_getElem_core _ _ _ _ i hi, hbv a b d i hi]
  | .float _, a, b, d, _, hflt, _, _ => by
    obtain rfl := eq_of_beq himm
    ext i hi; simp only [lift3]; rw [ternaryLogic_getElem_core _ _ _ _ i hi, hflt a b d i hi]
  | .pair s u, a, b, d, hbv, hflt, hbool, hk => by
    rw [hk]
    exact Prod.ext (ternlog_simp_eq imm c himm k s a.1 b.1 d.1 hbv hflt hbool hk)
      (ternlog_simp_eq imm c himm k u a.2 b.2 d.2 hbv hflt hbool hk)

theorem signExtend_self_core {n : Nat} (a : BitVec n) : a.signExtend n = a := by
  ext i hi; simp

theorem one_toNat_of_pos {n : Nat} (hn : 0 < n) : (1#n : BitVec n).toNat = 1 := by
  simpa [BitVec.toNat_ofNat] using Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))

theorem one_ne_zero_of_pos_core {n : Nat} (hn : 0 < n) : (1#n : BitVec n) ≠ 0#n := by
  intro h; have := congrArg BitVec.toNat h; simp [one_toNat_of_pos hn] at this

private theorem one_toInt_of_one_lt {n : Nat} (hn : 1 < n) : (1#n : BitVec n).toInt = 1 := by
  have hpowN : 4 ≤ 2 ^ n := Nat.le_trans (by decide) (Nat.pow_le_pow_right (by decide) hn)
  have hpowI : (4 : Int) ≤ ((2 ^ n : Nat) : Int) := by exact_mod_cast hpowN
  have hmod : (1 : Int) % ((2 ^ n : Nat) : Int) = 1 := Int.emod_eq_of_lt (by omega) (by omega)
  have h1 : (1#n : BitVec n) = BitVec.ofInt n 1 := by
    apply BitVec.eq_of_toNat_eq; rw [one_toNat_of_pos (by omega), BitVec.toNat_ofInt]
    exact_mod_cast hmod.symm
  rw [h1, BitVec.toInt_ofInt]; unfold Int.bmod; rw [hmod]; dsimp only; split <;> omega

theorem sdiv_one_of_one_lt_core {n : Nat} (hn : 1 < n) (a : BitVec n) : a.sdiv 1#n = a := by
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_sdiv, one_toInt_of_one_lt hn, Int.tdiv_one, ← BitVec.toInt_ofInt,
    BitVec.ofInt_toInt]

theorem findPow2_spec_core {w : Nat} {x : BitVec w} :
    ∀ {limit m : Nat}, findPow2 w x limit = some m → m < limit ∧ x = BitVec.twoPow w m
  | 0, _, h => nomatch h
  | l + 1, _, h => by
    simp only [findPow2] at h; split at h
    · next hx => cases h; exact ⟨Nat.lt_succ_self l, hx⟩
    · obtain ⟨hm, hx⟩ := findPow2_spec_core h; exact ⟨Nat.lt_succ_of_lt hm, hx⟩

private theorem lt_two_pow_self (n : Nat) : n < 2 ^ n := by
  induction n with
  | zero => decide
  | succ k ih => have hp : 1 ≤ 2 ^ k := Nat.one_le_pow _ _ (by decide); rw [Nat.pow_succ]; omega

theorem leafPow2Shift?_mul_r_core : ∀ (t : Ty) (a c s : Val t),
    t.hasFloat = false → leafPow2Shift? t c = some s →
    lift2 (fun {n} x y => x <<< (y.toNat % n)) (fun x _ => x) t a s =
      lift2 (· * ·) (· && ·) t a c
  | .bits n, a, c, s, _, hs => by
    simp only [leafPow2Shift?, Option.map_eq_some_iff] at hs
    rcases hs with ⟨m, hm, rfl⟩; obtain ⟨hlt, hpow⟩ := findPow2_spec_core hm
    have hs' : (BitVec.ofNat n m).toNat % n = m := by
      simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans hlt (lt_two_pow_self n)),
        Nat.mod_eq_of_lt hlt]
    simp only [lift2, hs', hpow, BitVec.shiftLeft_eq_mul_twoPow]
  | .pair t1 t2, (a1, a2), (c1, c2), (s1, s2), hf, hs => by
    simp only [Ty.hasFloat, Bool.or_eq_false_iff] at hf
    simp only [leafPow2Shift?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq, Prod.mk.injEq] at hs
    rcases hs with ⟨x1, hx1, x2, hx2, rfl, rfl⟩
    exact Prod.ext (leafPow2Shift?_mul_r_core t1 a1 c1 x1 hf.1 hx1)
      (leafPow2Shift?_mul_r_core t2 a2 c2 x2 hf.2 hx2)
  | .bool, _, _, _, _, hs => by simp [leafPow2Shift?] at hs
  | .float _, _, _, _, hf, _ => by simp [Ty.hasFloat] at hf

theorem leafPow2Shift?_mul_l_core (t : Ty) (a c s : Val t)
    (hf : t.hasFloat = false) (hs : leafPow2Shift? t c = some s) :
    lift2 (fun {n} x y => x <<< (y.toNat % n)) (fun x _ => x) t a s =
      lift2 (· * ·) (· && ·) t c a := by
  rw [leafPow2Shift?_mul_r_core t a c s hf hs,
    lift2_comm (· * ·) (· && ·) BitVec.mul_comm Bool.and_comm t a c]

theorem twoPow_ne_zero_core {n m : Nat} (hm : m < n) : BitVec.twoPow n m ≠ 0#n := by
  intro h; have hnat := congrArg BitVec.toNat h
  have hlt : 2 ^ m < 2 ^ n := Nat.pow_lt_pow_right (by decide : 1 < 2) hm
  have hp : 1 ≤ 2 ^ m := Nat.one_le_pow m 2 (by decide)
  simp only [BitVec.toNat_twoPow, Nat.mod_eq_of_lt hlt, BitVec.toNat_ofNat, Nat.zero_mod] at hnat
  omega

theorem udiv_twoPow_core {n m : Nat} (hm : m < n) (a : BitVec n) :
    a >>> ((BitVec.ofNat n m).toNat % n) = a / BitVec.twoPow n m := by
  have hm2 : m < 2 ^ n := Nat.lt_trans hm (lt_two_pow_self n)
  have hlt : 2 ^ m < 2 ^ n := Nat.pow_lt_pow_right (by decide : 1 < 2) hm
  have hmod : (BitVec.ofNat n m).toNat % n = m := by
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm2, Nat.mod_eq_of_lt hm]
  apply BitVec.eq_of_toNat_eq; rw [hmod]
  simp [BitVec.toNat_ushiftRight, BitVec.toNat_udiv, BitVec.toNat_twoPow,
    Nat.mod_eq_of_lt hlt, Nat.shiftRight_eq_div_pow]

theorem urem_twoPow_core {n m : Nat} (hm : m < n) (a : BitVec n) :
    a &&& (BitVec.twoPow n m - 1#n) = a % BitVec.twoPow n m := by
  have hlt : 2 ^ m < 2 ^ n := Nat.pow_lt_pow_right (by decide : 1 < 2) hm
  have h1 := one_toNat_of_pos (by omega : 0 < n)
  have hpow : (BitVec.twoPow n m).toNat = 2 ^ m := by
    simp [BitVec.toNat_twoPow, Nat.mod_eq_of_lt hlt]
  have hle : 1#n ≤ BitVec.twoPow n m := by
    rw [BitVec.le_def, hpow, h1]; exact Nat.one_le_pow m 2 (by decide)
  have hsub : (BitVec.twoPow n m - 1#n).toNat = 2 ^ m - 1 := by
    rw [BitVec.toNat_sub_of_le hle, hpow, h1]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_umod, hpow, hsub, Nat.and_two_pow_sub_one_eq_mod]

private theorem Op.rewrite_mul_a_wp {t : Ty} (hf0 : t.hasFloat = false)
    (a b : Arg Val t) {P : Tup Val [t] → Prop}
    (hw : (⟨.mul t, (a, b, ())⟩ : Op Val [t]).wp P) :
    (match a.imm?.bind (leafPow2Shift? t) with
      | some s => op2 (.shl t) b (.imm s) | none => op2 (.mul t) a b).wp P := by
  cases a with
  | var _ => simpa [Arg.imm?, Op.wp, op2] using hw
  | imm ca =>
    simp only [Arg.imm?, Option.bind_some]
    cases hs : leafPow2Shift? t ca with
    | none => simpa [Op.wp, op2] using hw
    | some s =>
      simpa [Op.wp, op2, OpCode.wp_shl, OpCode.wp_mul, hf0, vals,
        leafPow2Shift?_mul_l_core t b.val ca s hf0 hs] using hw

theorem Op.rewrite_wp_core {rs : List Ty} (op : Op Val rs) (P : Tup Val rs → Prop) :
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
            leafPow2Shift?_mul_r_core t a.val cb s hf0 hsb] using hw
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
        obtain ⟨hm, hpow⟩ := findPow2_spec_core hfm; subst hpow
        first
        | (simp only [Op.wp, OpCode.wp_udiv, op2, OpCode.wp_lshr, Ty.hasFloat,
            Bool.false_eq_true, ↓reduceIte, lift2, vals, Arg.val_imm] at hw ⊢
           rw [udiv_twoPow_core hm]; exact hw.2)
        | (simp only [Op.wp, OpCode.wp_urem, op2, OpCode.wp_and, lift2, vals, Arg.val_imm] at hw ⊢
           rw [urem_twoPow_core hm]; exact hw.2)
  | _ => exact fun hw => hw

/-! ## `CmpShapeLaw` & `ExtKind`: comparisons, involutions, and width chains -/

private theorem two_pow_eq_double {n : Nat} (hn : 0 < n) : 2 ^ n = 2 * 2 ^ (n - 1) := by
  cases n with | zero => omega | succ k => simp [Nat.pow_succ, Nat.mul_comm]

private theorem bvIntMin_toNat {n : Nat} (hn : 0 < n) :
    (BitVec.intMin n).toNat = 2 ^ (n - 1) := by
  simp only [BitVec.toNat_intMin]
  exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega))

private theorem bvIntMax_toNat {n : Nat} (hn : 0 < n) :
    (bvIntMax n).toNat = 2 ^ (n - 1) - 1 := by
  have hmin := bvIntMin_toNat hn; have hpow := two_pow_eq_double hn
  simp only [bvIntMax, BitVec.toNat_not, hmin]; omega

private theorem bvIntMin_toInt {n : Nat} (hn : 0 < n) :
    (BitVec.intMin n).toInt = -(2 ^ (n - 1) : Int) := by
  have hmin := bvIntMin_toNat hn; have hpow := two_pow_eq_double hn
  unfold BitVec.toInt; rw [hmin]
  have hlt : ¬ (2 * 2 ^ (n - 1) < 2 ^ n) := by omega
  simp only [hlt, ↓reduceIte]
  have hpowI : ((2 ^ n : Nat) : Int) = 2 * ((2 ^ (n - 1) : Nat) : Int) := by exact_mod_cast hpow
  push_cast at hpowI ⊢; omega

private theorem bvIntMax_toInt {n : Nat} (hn : 0 < n) :
    (bvIntMax n).toInt = (2 ^ (n - 1) : Int) - 1 := by
  have hmax := bvIntMax_toNat hn; have hpos : 1 ≤ 2 ^ (n - 1) := Nat.one_le_pow _ _ (by decide)
  have hpow := two_pow_eq_double hn; unfold BitVec.toInt; rw [hmax]
  have hlt : 2 * (2 ^ (n - 1) - 1) < 2 ^ n := by omega
  simp only [hlt, ↓reduceIte]
  have hsub : ((2 ^ (n - 1) - 1 : Nat) : Int) = ((2 ^ (n - 1) : Nat) : Int) - 1 := by omega
  rw [hsub]; push_cast; rfl

private theorem add_one_toNat_of_ne_allOnes {n : Nat} {c : BitVec n}
    (hne : c ≠ BitVec.allOnes n) : (c + 1#n).toNat = c.toNat + 1 := by
  have hn : 0 < n := by
    cases n with | zero => exact False.elim (hne (Subsingleton.elim _ _)) | succ _ => omega
  have hneNat : c.toNat ≠ 2 ^ n - 1 := fun h =>
    hne (BitVec.eq_of_toNat_eq (by simpa [BitVec.toNat_allOnes] using h))
  have hlt : c.toNat + 1 < 2 ^ n := by have := c.isLt; omega
  rw [BitVec.toNat_add, one_toNat_of_pos hn, Nat.mod_eq_of_lt hlt]

private theorem add_one_toInt_of_ne_intMax {n : Nat} {c : BitVec n}
    (hne : c ≠ bvIntMax n) : (c + 1#n).toInt = c.toInt + 1 := by
  have hn : 0 < n := by
    cases n with | zero => exact False.elim (hne (Subsingleton.elim _ _)) | succ _ => omega
  have hpow := two_pow_eq_double hn; have hmax := bvIntMax_toNat hn
  have hneNat : c.toNat ≠ 2 ^ (n - 1) - 1 := fun h =>
    hne (BitVec.eq_of_toNat_eq (h.trans hmax.symm))
  have h1 := one_toNat_of_pos hn; have hpos : 1 ≤ 2 ^ (n - 1) := Nat.one_le_pow _ _ (by decide)
  have hc := c.isLt; unfold BitVec.toInt; rw [BitVec.toNat_add, h1]
  by_cases hwrap : c.toNat + 1 < 2 ^ n
  · rw [Nat.mod_eq_of_lt hwrap]; split <;> split <;> omega
  · have hmod : (c.toNat + 1) % 2 ^ n = 0 := by
      have heq : c.toNat + 1 = 2 ^ n := by omega
      rw [heq, Nat.mod_self]
    rw [hmod]; split <;> split <;> omega

theorem cmpImmBound?_core {n : Nat} (o : CmpOp) (x c : BitVec n) {res : Bool}
    (h : cmpImmBound? o n c = some res) : o.evalBits x c = res := by
  cases o with
  | eq | ne => simp [cmpImmBound?] at h
  | ult | uge | ugt | ule =>
    dsimp only [cmpImmBound?] at h; split at h
    · rename_i heq; cases h; obtain rfl := eq_of_beq heq
      have hx := x.isLt
      simp only [CmpOp.evalBits, BitVec.ult, BitVec.ule, BitVec.toNat_allOnes, BitVec.toNat_zero]
      simp [decide_eq_false_iff_not]; all_goals omega
    · cases h
  | slt | sge | sgt | sle =>
    dsimp only [cmpImmBound?] at h; split at h
    · rename_i heq; cases h; obtain rfl := eq_of_beq heq
      cases n with
      | zero => rw [Subsingleton.elim x 0#0]; decide
      | succ k =>
        have hlo := x.le_toInt; have hhi := x.toInt_lt; simp only [Nat.add_sub_cancel] at hlo hhi
        simp only [CmpOp.evalBits, BitVec.slt, BitVec.sle,
          bvIntMin_toInt (Nat.succ_pos k), bvIntMax_toInt (Nat.succ_pos k), Nat.succ_sub_one]
        simp [decide_eq_false_iff_not]; all_goals omega
    · cases h

theorem normBitsCmpImm_core {n : Nat} (o : CmpOp) (x c : BitVec n) :
    (normBitsCmpImm o n c).1.evalBits x (normBitsCmpImm o n c).2 = o.evalBits x c := by
  cases o with
  | eq | ne | ult | uge | slt | sge => rfl
  | ugt =>
    dsimp only [normBitsCmpImm]; split
    · rename_i h0; obtain rfl := eq_of_beq h0
      simp only [CmpOp.evalBits, BitVec.ult, BitVec.toNat_zero]; apply decide_eq_decide.2
      exact ⟨fun hne => Nat.pos_of_ne_zero (fun h =>
          hne (BitVec.eq_of_toNat_eq (by simpa using h))),
        fun hlt heq => by subst heq; simp at hlt⟩
    · split
      · rename_i hne; have hne' : c ≠ BitVec.allOnes n := by simpa using hne
        simp only [CmpOp.evalBits, BitVec.ult, BitVec.ule, add_one_toNat_of_ne_allOnes hne',
          decide_eq_decide]; omega
      · rfl
  | ule =>
    dsimp only [normBitsCmpImm]; split
    · rename_i h0; obtain rfl := eq_of_beq h0
      simp only [CmpOp.evalBits, BitVec.ule, BitVec.toNat_zero]; apply decide_eq_decide.2
      exact ⟨fun hx => by subst hx; simp,
        fun hle => BitVec.eq_of_toNat_eq (by simp; omega)⟩
    · split
      · rename_i hne; have hne' : c ≠ BitVec.allOnes n := by simpa using hne
        simp only [CmpOp.evalBits, BitVec.ult, BitVec.ule, add_one_toNat_of_ne_allOnes hne',
          decide_eq_decide]; omega
      · rfl
  | sgt | sle =>
    dsimp only [normBitsCmpImm]; split
    · rename_i hne; have hne' : c ≠ bvIntMax n := by simpa using hne
      simp only [CmpOp.evalBits, BitVec.slt, BitVec.sle, add_one_toInt_of_ne_intMax hne',
        decide_eq_decide]; omega
    · rfl

private theorem setWidth_signExtend_of_le {m n : Nat} (hle : m ≤ n) (x : BitVec m) :
    (x.signExtend n).setWidth m = x := by
  ext i hi; simp [BitVec.getElem_signExtend, Nat.lt_of_lt_of_le hi hle, hi]

private theorem toNat_signExtend_of_le {m n : Nat} (hle : m ≤ n) (x : BitVec m) :
    (x.signExtend n).toNat =
      if 2 * x.toNat < 2 ^ m then x.toNat else x.toNat + 2 ^ n - 2 ^ m := by
  have hti : (x.signExtend n).toInt = x.toInt := BitVec.toInt_signExtend_of_le hle
  have hpow : 2 ^ m ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hle
  have hx := x.isLt; have hxs := (x.signExtend n).isLt
  unfold BitVec.toInt at hti; split at hti <;> split at hti <;> split <;> omega

theorem cmpOp_evalBits_signExtend_core {m n : Nat} (hlt : m < n) (o : CmpOp) (x y : BitVec m) :
    o.evalBits (x.signExtend n) (y.signExtend n) = o.evalBits x y := by
  have hle : m ≤ n := Nat.le_of_lt hlt
  have hinj : (x.signExtend n = y.signExtend n) ↔ (x = y) :=
    ⟨fun h => by rw [← setWidth_signExtend_of_le hle x, ← setWidth_signExtend_of_le hle y, h],
     congrArg _⟩
  have hpow : 2 ^ m ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hle
  have hxi := BitVec.toInt_signExtend_of_le hle (x := x)
  have hyi := BitVec.toInt_signExtend_of_le hle (x := y)
  have hxn := toNat_signExtend_of_le hle x; have hyn := toNat_signExtend_of_le hle y
  have hx := x.isLt; have hy := y.isLt
  cases o
  · simp [CmpOp.evalBits, hinj]
  · simp [CmpOp.evalBits, hinj]
  · simp only [CmpOp.evalBits, BitVec.ult, hxn, hyn, decide_eq_decide]; split <;> split <;> omega
  · simp only [CmpOp.evalBits, BitVec.ule, hxn, hyn, decide_eq_decide]; split <;> split <;> omega
  · simp only [CmpOp.evalBits, BitVec.ult, hxn, hyn, decide_eq_decide]; split <;> split <;> omega
  · simp only [CmpOp.evalBits, BitVec.ule, hxn, hyn, decide_eq_decide]; split <;> split <;> omega
  · simp [CmpOp.evalBits, BitVec.slt, hxi, hyi]
  · simp [CmpOp.evalBits, BitVec.sle, hxi, hyi]
  · simp [CmpOp.evalBits, BitVec.slt, hxi, hyi]
  · simp [CmpOp.evalBits, BitVec.sle, hxi, hyi]

theorem cmpOp_evalBits_setWidth_core {m n : Nat} (hlt : m < n) (o : CmpOp) (x y : BitVec m) :
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

theorem lift1_not_not : ∀ (t : Ty) (x : Val t),
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
    · simp [hlt, Nat.div_eq_of_lt hlt, Nat.mod_eq_of_lt hlt, show 8 * m + i < w by omega]
    · have ih := bswapBits_go_getLsbD x m (i - 8) (by omega) (by omega)
      have hdiv : (i - 8) / 8 + 1 = i / 8 := by omega
      have hmod : (i - 8) % 8 = i % 8 := by omega
      simp [hlt, ih]; congr 1; omega

private theorem bswapBits_getLsbD {w : Nat} (hw : w % 8 = 0) (x : BitVec w) {i : Nat}
    (hi : i < w) :
    (bswapBits x).getLsbD i = x.getLsbD (8 * (w / 8 - 1 - i / 8) + i % 8) := by
  have hmul : 8 * (w / 8) = w := by omega
  dsimp only [bswapBits]; simp only [BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and]
  exact bswapBits_go_getLsbD x (w / 8) i (by omega) (by omega)

theorem bswapBits_bswapBits_core {w : Nat} (hw : w % 8 = 0) (x : BitVec w) :
    bswapBits (bswapBits x) = x := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have hdiv : i / 8 < w / 8 := Nat.div_lt_of_lt_mul (by omega)
  have hmod : i % 8 < 8 := Nat.mod_lt i (by decide)
  have hj : 8 * (w / 8 - 1 - i / 8) + i % 8 < w := by omega
  rw [bswapBits_getLsbD hw (bswapBits x) hi, bswapBits_getLsbD hw x hj]
  have hdj : (8 * (w / 8 - 1 - i / 8) + i % 8) / 8 = w / 8 - 1 - i / 8 := by
    rw [Nat.mul_add_div (by decide), Nat.div_eq_of_lt hmod]; omega
  have hmj : (8 * (w / 8 - 1 - i / 8) + i % 8) % 8 = i % 8 := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hmod]
  rw [hdj, hmj, show w / 8 - 1 - (w / 8 - 1 - i / 8) = i / 8 by omega, Nat.div_add_mod i 8]

theorem lift1_bswap_bswap : ∀ (t : Ty), t.bswapOk = true →
    ∀ (x : Val t), lift1 bswapBits id t (lift1 bswapBits id t x) = x
  | .bool, h, _ | .float _, h, _ => by simp [Ty.bswapOk] at h
  | .bits _, h, x => bswapBits_bswapBits_core (eq_of_beq h) x
  | .pair s u, h, (x₁, x₂) => by
    simp only [Ty.bswapOk, Bool.and_eq_true] at h
    exact Prod.ext (lift1_bswap_bswap s h.1 x₁) (lift1_bswap_bswap u h.2 x₂)

theorem reverse_reverse {n : Nat} (x : BitVec n) : x.reverse.reverse = x := by
  apply BitVec.eq_of_getLsbD_eq; intro i _hi; simp

theorem setWidth_setWidth_le_core {w m n : Nat} (hnm : n ≤ m) (x : BitVec w) :
    (x.setWidth m).setWidth n = x.setWidth n := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_setWidth, hi, show i < m by omega, decide_true, Bool.true_and]

theorem setWidth_setWidth_trans_core {w m n : Nat} (hwm : w ≤ m) (_hmn : m ≤ n)
    (x : BitVec w) : (x.setWidth m).setWidth n = x.setWidth n := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  by_cases hw : i < w
  · simp only [BitVec.getLsbD_setWidth, hi, show i < m by omega, decide_true, Bool.true_and]
  · rw [← BitVec.setWidth_eq x]
    simp only [BitVec.getLsbD_setWidth, hi, hw, decide_false, Bool.false_and, Bool.and_false]

theorem setWidth_signExtend_of_narrow_core {w m n : Nat} (hnw : n ≤ w) (hwm : w ≤ m)
    (x : BitVec w) : (x.signExtend m).setWidth n = x.setWidth n := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_signExtend, hi,
    show i < m by omega, show i < w by omega, decide_true, Bool.true_and, ↓reduceIte]

theorem setWidth_signExtend_of_mid_core {w m n : Nat} (_hwn : w ≤ n) (hnm : n ≤ m)
    (x : BitVec w) : (x.signExtend m).setWidth n = x.signExtend n := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
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
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_signExtend, hi, decide_true, Bool.true_and, hmsb]
  by_cases hm : i < m
  · simp only [hm, decide_true, Bool.true_and, ↓reduceIte]
  · simp only [hm, show ¬ i < w by omega, ↓reduceIte]

@[expose] def ExtKind.eval (k : ExtKind) (n : Nat) {m : Nat} (x : BitVec m) : BitVec n :=
  match k with | .sext => x.signExtend n | .zext => x.setWidth n

theorem ExtKind.eval_sext (n : Nat) {m : Nat} (x : BitVec m) :
    ExtKind.eval .sext n x = x.signExtend n := rfl

theorem ExtKind.eval_zext (n : Nat) {m : Nat} (x : BitVec m) :
    ExtKind.eval .zext n x = x.setWidth n := rfl

@[expose] def ExtKind.cmpOp (k : ExtKind) (o : CmpOp) : CmpOp :=
  match k with | .sext => o | .zext => o.toUnsigned

theorem ExtKind.cmpOp_sext (o : CmpOp) : ExtKind.cmpOp .sext o = o := rfl
theorem ExtKind.cmpOp_zext (o : CmpOp) : ExtKind.cmpOp .zext o = o.toUnsigned := rfl

theorem CmpOp.isRefl_swap (o : CmpOp) : o.swap.isRefl = o.isRefl := by cases o <;> rfl
theorem CmpOp.isRefl_toUnsigned (o : CmpOp) : o.toUnsigned.isRefl = o.isRefl := by cases o <;> rfl

theorem ExtKind.cmpOp_isRefl (k : ExtKind) (o : CmpOp) : (k.cmpOp o).isRefl = o.isRefl := by
  cases k <;> simp [ExtKind.cmpOp, CmpOp.isRefl_toUnsigned]

theorem ExtKind.cmpOp_evalBits {m n : Nat} (hlt : m < n) (k : ExtKind) (o : CmpOp)
    (x y : BitVec m) : (k.cmpOp o).evalBits x y = o.evalBits (k.eval n x) (k.eval n y) := by
  cases k
  · exact (cmpOp_evalBits_signExtend_core hlt o x y).symm
  · exact (cmpOp_evalBits_setWidth_core hlt o x y).symm

theorem ExtKind.setWidth_eval_narrow {w m n : Nat} (k : ExtKind)
    (hnw : n ≤ w) (hwm : w ≤ m) (x : BitVec w) : (k.eval m x).setWidth n = x.setWidth n := by
  cases k
  · exact setWidth_signExtend_of_narrow_core hnw hwm x
  · exact setWidth_setWidth_le_core (by omega) x

theorem ExtKind.setWidth_eval_mid {w m n : Nat} (k : ExtKind)
    (hwn : w ≤ n) (hnm : n ≤ m) (x : BitVec w) : (k.eval m x).setWidth n = k.eval n x := by
  cases k
  · exact setWidth_signExtend_of_mid_core hwn hnm x
  · exact setWidth_setWidth_le_core hnm x

theorem ExtKind.eval_eval_le {w m n : Nat} (k : ExtKind)
    (hpos : 0 < w) (hwm : w ≤ m) (hmn : m ≤ n) (x : BitVec w) :
    k.eval n (k.eval m x) = k.eval n x := by
  cases k
  · exact signExtend_signExtend_of_le hpos hwm hmn x
  · exact setWidth_setWidth_trans_core hwm hmn x

end LeanQbe.T
