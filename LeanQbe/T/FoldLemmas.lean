module

public import LeanQbe.T.Fold
public import LeanQbe.T.OptUtilLemmas
import LeanQbe.T.OpsLemmas
import LeanQbe.T.PassEnvKit
import LeanQbe.T.FoldSimpKit

/-!
# Correctness of `fold`

* `OpCode.eval?_sound`: evaluating an immediate `OpCode` refines `OpCode.wp`.
* `Op.rewrite_wp`: strength reductions (`mul → shl`, `udiv → lshr`, `urem → and`) refine `Op.wp`.
* `fold_wp`: source `wp` implies folded `wp`, proved via `Wf.induct`.
* `fold_wf`: `Wf` is preserved, proved via `Wf.induct`.
* `Func.fold_spec`, `Func.fold_wf`: closed-function specifications.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T

/-! ## Soundness of `OpCode.eval?` and leaf algebraic/bitvector theorems -/

theorem evalFloatLeaf_sound (f : Fmt) (res : Float.Model.UnpackedFloat)
    {post : BitVec f.width → Prop} (hw : floatResultWp f res post) :
    post (if res.isNaN then canonNaN f else packFloat f res) :=
  evalFloatLeaf_core f res hw

theorem evalFloat1_sound
    (op : Float.Model.Format → Float.Model.UnpackedFloat → Float.Model.UnpackedFloat)
    (t : Ty) (a r : Val t) (post : Val t → Prop)
    (hev : evalFloat1 op t a = some r) (hw : liftFloatRel1 op t a post) : post r :=
  evalFloat1_core op t a r post hev hw

theorem evalFloat2_sound
    (op : Float.Model.Format → Float.Model.UnpackedFloat →
      Float.Model.UnpackedFloat → Float.Model.UnpackedFloat)
    (t : Ty) (a b r : Val t) (post : Val t → Prop)
    (hev : evalFloat2 op t a b = some r) (hw : liftFloatRel2 op t a b post) : post r :=
  evalFloat2_core op t a b r post hev hw

theorem evalFloat3_sound
    (op : Float.Model.Format → Float.Model.UnpackedFloat →
      Float.Model.UnpackedFloat → Float.Model.UnpackedFloat → Float.Model.UnpackedFloat)
    (t : Ty) (a b c r : Val t) (post : Val t → Prop)
    (hev : evalFloat3 op t a b c = some r) (hw : liftFloatRel3 op t a b c post) : post r :=
  evalFloat3_core op t a b c r post hev hw

theorem evalConvertFloat_sound (src dst : Fmt) (b : BitVec src.width)
    {post : BitVec dst.width → Prop} (hw : convertFloat src dst b post) :
    post (evalConvertFloat src dst b) :=
  evalConvertFloat_core src dst b hw

theorem OpCode.eval?_sound : {sig rs : List Ty} → (c : OpCode sig rs) → (args : Tup Val sig) →
    {res : Tup Val rs} → (post : Tup Val rs → Prop) →
    c.eval? args = some res → c.wp args post → post res
  | _, _, .copy _, (_, ()), _, _, h, hw | _, _, .not _, (_, ()), _, _, h, hw
  | _, _, .clz _, (_, ()), _, _, h, hw | _, _, .cls _, (_, ()), _, _, h, hw
  | _, _, .rbit _, (_, ()), _, _, h, hw | _, _, .ctz _, (_, ()), _, _, h, hw
  | _, _, .popcnt _, (_, ()), _, _, h, hw | _, _, .ofBool _, (_, ()), _, _, h, hw
  | _, _, .unpair _ _, (_, ()), _, _, h, hw | _, _, .bitcast _ _ _, (_, ()), _, _, h, hw
  | _, _, .uitofp _ _, (_, ()), _, _, h, hw | _, _, .sitofp _ _, (_, ()), _, _, h, hw
  | _, _, .and _, (_, _, ()), _, _, h, hw | _, _, .or _, (_, _, ()), _, _, h, hw
  | _, _, .xor _, (_, _, ()), _, _, h, hw | _, _, .umulw _, (_, _, ()), _, _, h, hw
  | _, _, .smulw _, (_, _, ()), _, _, h, hw | _, _, .udiv0 _, (_, _, ()), _, _, h, hw
  | _, _, .sdiv0 _, (_, _, ()), _, _, h, hw | _, _, .mkpair _ _, (_, _, ()), _, _, h, hw
  | _, _, .sha256msg1, (_, _, ()), _, _, h, hw | _, _, .sha256msg2, (_, _, ()), _, _, h, hw
  | _, _, .ternlog _ _, (_, _, _, ()), _, _, h, hw | _, _, .fshl _, (_, _, _, ()), _, _, h, hw
  | _, _, .fshr _, (_, _, _, ()), _, _, h, hw | _, _, .select _, (_, _, _, ()), _, _, h, hw
  | _, _, .addc _, (_, _, _, ()), _, _, h, hw | _, _, .subb _, (_, _, _, ()), _, _, h, hw
  | _, _, .sha256rnds2, (_, _, _, ()), _, _, h, hw => by
    dsimp only [OpCode.eval?] at h; simp only [Option.some.injEq] at h; subst h; exact hw
  | _, _, .neg _, (_, ()), _, _, h, hw | _, _, .bswap _, (_, ()), _, _, h, hw
  | _, _, .zext _ _, (_, ()), _, _, h, hw | _, _, .sext _ _, (_, ()), _, _, h, hw
  | _, _, .trunc _ _, (_, ()), _, _, h, hw | _, _, .shufd _ _, (_, ()), _, _, h, hw
  | _, _, .fneg _, (_, ()), _, _, h, hw | _, _, .fabs _, (_, ()), _, _, h, hw
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
  | _, _, .fadd t, (_, _, ()), _, _, h, hw | _, _, .fsub t, (_, _, ()), _, _, h, hw
  | _, _, .fmul t, (_, _, ()), _, _, h, hw | _, _, .fdiv t, (_, _, ()), _, _, h, hw => by
    dsimp only [OpCode.eval?] at h; dsimp only [OpCode.wp] at hw
    exact float_eval?_sound _ h (by
      by_cases hf : !t.isFloatTree
      · simp [hf] at hw ⊢
      · simp only [hf, Bool.false_eq_true, ↓reduceIte] at hw ⊢
        exact fun _ hr => evalFloat2_sound _ _ _ _ _ _ hr hw)
  | _, _, .ffma t, (_, _, _, ()), _, _, h, hw => by
    dsimp only [OpCode.eval?] at h; simp only [OpCode.wp_ffma] at hw
    exact float_eval?_sound _ h (by
      by_cases hf : !t.isFloatTree
      · simp [hf] at hw ⊢
      · simp only [hf, Bool.false_eq_true, ↓reduceIte] at hw ⊢
        exact fun _ hr => evalFloat3_sound _ _ _ _ _ _ _ hr hw)
  | _, _, .fsqrt t, (_, ()), _, _, h, hw => by
    dsimp only [OpCode.eval?] at h; simp only [OpCode.wp_fsqrt] at hw
    exact float_eval?_sound _ h (by
      by_cases hf : !t.isFloatTree
      · simp [hf] at hw ⊢
      · simp only [hf, Bool.false_eq_true, ↓reduceIte] at hw ⊢
        exact fun _ hr => evalFloat1_sound _ _ _ _ _ hr hw)
  | _, _, .fptoui f n, (_, ()), _, _, h, hw => by
    dsimp only [OpCode.eval?] at h; simp only [Option.bind_eq_some_iff, OpCode.wp_fptoui] at h hw
    rcases h with ⟨z, hz, hr⟩; simp only [hz] at hw
    split at hr
    · simp only [Option.some.injEq] at hr; subst hr; exact hw.2.2
    · cases hr
  | _, _, .fptosi f n, (_, ()), _, _, h, hw => by
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

theorem isZeroVal_eq : ∀ (t : Ty) (v : Val t), isZeroVal t v = true → v = zeroVal t
  | .bool, v, h => by cases v <;> simp [isZeroVal, zeroVal] at h ⊢
  | .bits _, v, h | .float _, v, h => by simpa [isZeroVal, zeroVal] using h
  | .pair a b, (v1, v2), h => by
    simp only [isZeroVal, Bool.and_eq_true] at h
    exact Prod.ext (isZeroVal_eq a v1 h.1) (isZeroVal_eq b v2 h.2)

theorem isOnesVal_eq : ∀ (t : Ty) (v : Val t), isOnesVal t v = true → v = onesVal t
  | .bool, v, h => by cases v <;> simp [isOnesVal, onesVal] at h ⊢
  | .bits _, v, h | .float _, v, h => by simpa [isOnesVal, onesVal] using h
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

theorem cmpOp_evalBits_self {n : Nat} (o : CmpOp) (v : BitVec n) : o.evalBits v v = o.isRefl := by
  cases o <;> simp [CmpOp.evalBits, CmpOp.isRefl, BitVec.ult, BitVec.ule, BitVec.slt, BitVec.sle]

theorem cmpOp_evalBool_self (o : CmpOp) (v : Bool) : o.evalBool v v = o.isRefl := by
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
  | .bool, _, _ | .bits _, _, _ | .float _, _, _ => rfl
  | .pair s u, a, b => Prod.ext (blendV_splatMask_true s a.1 b.1) (blendV_splatMask_true u a.2 b.2)

theorem blendV_splatMask_false : ∀ (t : Ty) (a b : Val t),
    blendV t (splatMaskVal t false) a b = b
  | .bool, _, _ | .bits _, _, _ | .float _, _, _ => rfl
  | .pair s u, a, b =>
    Prod.ext (blendV_splatMask_false s a.1 b.1) (blendV_splatMask_false u a.2 b.2)

theorem blendV_self : ∀ (t : Ty) (c : Val t.mask) (a : Val t), blendV t c a a = a
  | .bool, c, _ | .bits _, c, _ | .float _, c, _ => by cases c <;> rfl
  | .pair s u, c, (a1, a2) => Prod.ext (blendV_self s c.1 a1) (blendV_self u c.2 a2)

theorem ternaryLogic_getElem {w : Nat} (a b c : BitVec w) (imm : BitVec 8) (i : Nat) (hi : i < w) :
    (ternaryLogic a b c imm)[i] = ternaryLogicBool a[i] b[i] c[i] imm :=
  ternaryLogic_getElem_core a b c imm i hi

theorem signExtend_self {n : Nat} (a : BitVec n) : a.signExtend n = a := signExtend_self_core a
theorem div_one_of_pos {n : Nat} (_hn : 0 < n) (a : BitVec n) : a / 1#n = a := by simp
theorem mod_one_of_pos {n : Nat} (_hn : 0 < n) (a : BitVec n) : a % 1#n = 0#n := by simp

theorem one_ne_zero_of_pos {n : Nat} (hn : 0 < n) : (1#n : BitVec n) ≠ 0#n :=
  one_ne_zero_of_pos_core hn

theorem sdiv_one_of_one_lt {n : Nat} (hn : 1 < n) (a : BitVec n) : a.sdiv 1#n = a :=
  sdiv_one_of_one_lt_core hn a

theorem srem_one_of_one_lt {n : Nat} (_hn : 1 < n) (a : BitVec n) : a.srem 1#n = 0#n := by simp

theorem findPow2_spec {w : Nat} {x : BitVec w} :
    ∀ {limit m : Nat}, findPow2 w x limit = some m → m < limit ∧ x = BitVec.twoPow w m :=
  findPow2_spec_core

theorem leafPow2Shift?_mul_r : ∀ (t : Ty) (a c s : Val t),
    t.hasFloat = false → leafPow2Shift? t c = some s →
    lift2 (fun {n} x y => x <<< (y.toNat % n)) (fun x _ => x) t a s =
      lift2 (· * ·) (· && ·) t a c :=
  leafPow2Shift?_mul_r_core

theorem leafPow2Shift?_mul_l (t : Ty) (a c s : Val t)
    (hf : t.hasFloat = false) (hs : leafPow2Shift? t c = some s) :
    lift2 (fun {n} x y => x <<< (y.toNat % n)) (fun x _ => x) t a s =
      lift2 (· * ·) (· && ·) t c a :=
  leafPow2Shift?_mul_l_core t a c s hf hs

theorem twoPow_ne_zero {n m : Nat} (hm : m < n) : BitVec.twoPow n m ≠ 0#n :=
  twoPow_ne_zero_core hm

theorem udiv_twoPow {n m : Nat} (hm : m < n) (a : BitVec n) :
    a >>> ((BitVec.ofNat n m).toNat % n) = a / BitVec.twoPow n m :=
  udiv_twoPow_core hm a

theorem urem_twoPow {n m : Nat} (hm : m < n) (a : BitVec n) :
    a &&& (BitVec.twoPow n m - 1#n) = a % BitVec.twoPow n m :=
  urem_twoPow_core hm a

theorem Op.rewrite_wp {rs : List Ty} (op : Op Val rs) (P : Tup Val rs → Prop) :
    op.wp P → op.rewrite.wp P :=
  Op.rewrite_wp_core op P

theorem cmpImmBound?_sound {n : Nat} (o : CmpOp) (x c : BitVec n) {res : Bool}
    (h : cmpImmBound? o n c = some res) : o.evalBits x c = res :=
  cmpImmBound?_core o x c h

theorem normBitsCmpImm_eval {n : Nat} (o : CmpOp) (x c : BitVec n) :
    (normBitsCmpImm o n c).1.evalBits x (normBitsCmpImm o n c).2 = o.evalBits x c :=
  normBitsCmpImm_core o x c

theorem cmpOp_evalBits_signExtend {m n : Nat} (hlt : m < n) (o : CmpOp) (x y : BitVec m) :
    o.evalBits (x.signExtend n) (y.signExtend n) = o.evalBits x y :=
  cmpOp_evalBits_signExtend_core hlt o x y

theorem cmpOp_evalBits_setWidth {m n : Nat} (hlt : m < n) (o : CmpOp) (x y : BitVec m) :
    o.evalBits (x.setWidth n) (y.setWidth n) = o.toUnsigned.evalBits x y :=
  cmpOp_evalBits_setWidth_core hlt o x y

theorem bswapBits_bswapBits {w : Nat} (hw : w % 8 = 0) (x : BitVec w) :
    bswapBits (bswapBits x) = x :=
  bswapBits_bswapBits_core hw x

theorem setWidth_setWidth_le {w m n : Nat} (hnm : n ≤ m) (x : BitVec w) :
    (x.setWidth m).setWidth n = x.setWidth n :=
  setWidth_setWidth_le_core hnm x

theorem setWidth_setWidth_trans {w m n : Nat} (hwm : w ≤ m) (hmn : m ≤ n) (x : BitVec w) :
    (x.setWidth m).setWidth n = x.setWidth n :=
  setWidth_setWidth_trans_core hwm hmn x

theorem setWidth_signExtend_of_narrow {w m n : Nat} (hnw : n ≤ w) (hwm : w ≤ m) (x : BitVec w) :
    (x.signExtend m).setWidth n = x.setWidth n :=
  setWidth_signExtend_of_narrow_core hnw hwm x

theorem setWidth_signExtend_of_mid {w m n : Nat} (hwn : w ≤ n) (hnm : n ≤ m) (x : BitVec w) :
    (x.signExtend m).setWidth n = x.signExtend n :=
  setWidth_signExtend_of_mid_core hwn hnm x

/-! ## Context invariants and `SimpAct` soundness -/

/-- Operation matching an `InvKind`. -/
def invOpVal : InvKind → (t : Ty) → Val t → Val t
  | .not_, t, x => lift1 (~~~ ·) (! ·) t x
  | .bswap, t, x => lift1 bswapBits id t x
  | .rbit, .bits _, x => x.reverse
  | .rbit, _, x => x

/-- Well-formedness side condition for `InvKind` at type `t`. -/
def invOpOk : InvKind → Ty → Prop
  | .not_, _ => True | .bswap, t => t.bswapOk = true | .rbit, _ => True

private theorem invOpVal_invol : ∀ (k : InvKind) (t : Ty), invOpOk k t →
    ∀ (x : Val t), invOpVal k t (invOpVal k t x) = x
  | .not_, t, _, x => lift1_not_not t x
  | .bswap, t, h, x => lift1_bswap_bswap t h x
  | .rbit, .bits _, _, x => reverse_reverse x
  | .rbit, .bool, _, _ | .rbit, .float _, _, _ | .rbit, .pair _ _, _, _ => rfl

/-- Semantic invariant for extension provenance `BitsExt Val n`. -/
def BitsExtGood (ρ : (t : Ty) → Nat → Val t) (b : Nat) {n : Nat}
    (e : BitsExt Val n) (v : BitVec n) : Prop :=
  (match e.kind with | .sext => v = e.src.val.signExtend n | .zext => v = e.src.val.setWidth n) ∧
  e.srcKey.fev ρ = e.src.val ∧ e.srcKey.FLt b

private theorem BitsExtGood.eval_eq {ρ : FEnv} {b n : Nat} {e : BitsExt Val n} {v : BitVec n}
    (h : BitsExtGood ρ b e v) : v = e.kind.eval n e.src.val := by
  rcases e with ⟨k, _, _, _, _, _⟩
  cases k; simpa [ExtKind.eval_sext] using h.1; simpa [ExtKind.eval_zext] using h.1

/-- Semantic invariant for extension provenance `ExtDef Val t`. -/
def ExtDefGood (ρ : (t : Ty) → Nat → Val t) (b : Nat) : {t : Ty} → ExtDef Val t → Val t → Prop
  | .bits _, some e, v => BitsExtGood ρ b e v
  | .bits _, none, _ | .bool, _, _ | .float _, _, _ | .pair _ _, _, _ => True

/-- Semantic invariant for unary-involution provenance `Option (UnInv Val t)`. -/
def UnInvOptGood (ρ : (t : Ty) → Nat → Val t) (b : Nat) {t : Ty} :
    Option (UnInv Val t) → Val t → Prop
  | some iv, v =>
    invOpOk iv.kind t ∧ v = invOpVal iv.kind t iv.src.val ∧
    iv.srcKey.fev ρ = iv.src.val ∧ iv.srcKey.FLt b
  | none, _ => True

theorem ExtDefGood.none {ρ : (t : Ty) → Nat → Val t} {b : Nat} {t : Ty} {v : Val t} :
    ExtDefGood ρ b (ExtDef.none (t := t)) v := by cases t <;> trivial

theorem ExtDefGood.upd_all {ρ : (t : Ty) → Nat → Val t} {b : Nat} {ts : List Ty} (xs : Tup Val ts)
    {t : Ty} {e : ExtDef Val t} {v : Val t} (he : ExtDefGood ρ b e v) :
    ExtDefGood (fupdTup ρ b xs) (b + ts.length) e v := by
  cases t with
  | bits _ =>
    cases e with
    | none => trivial
    | some _ => exact ⟨he.1, (FKey.fev_fupdTup xs he.2.2).trans he.2.1, he.2.2.add⟩
  | bool | float _ | pair _ _ => trivial

theorem UnInvOptGood.upd_all {ρ : (t : Ty) → Nat → Val t} {b : Nat} {ts : List Ty} (xs : Tup Val ts)
    {t : Ty} {iv : Option (UnInv Val t)} {v : Val t} (hi : UnInvOptGood ρ b iv v) :
    UnInvOptGood (fupdTup ρ b xs) (b + ts.length) iv v := by
  cases iv with
  | none => trivial
  | some _ => exact ⟨hi.1, hi.2.1, (FKey.fev_fupdTup xs hi.2.2.2).trans hi.2.2.1, hi.2.2.2.add⟩

/-- Value invariant for one `FVal Val t` entry in `FGood`. -/
def FValGood (ρ : (t : Ty) → Nat → Val t) (b : Nat) {t : Ty} (r : FVal Val t) (v : Val t) : Prop :=
  r.out.val = v ∧ r.key.fev ρ = v ∧ r.key.FLt b ∧ ExtDefGood ρ b r.ext v ∧ UnInvOptGood ρ b r.inv v

/-- Every input variable in `G` satisfies `FValGood`. -/
def FGood (ρ : (t : Ty) → Nat → Val t) (b : Nat) (G : Ctx (FVal Val) Val) : Prop :=
  ∀ p ∈ G, FValGood ρ b p.2.1 p.2.2

theorem FGood.cons {ρ : (t : Ty) → Nat → Val t} {b : Nat} {G : Ctx (FVal Val) Val}
    (hG : FGood ρ b G) {t : Ty} {r : FVal Val t} {v : Val t} (hr : FValGood ρ b r v) :
    FGood ρ b (⟨t, r, v⟩ :: G) := CtxPred.cons hr hG

theorem FGood.upd_all {ρ : (t : Ty) → Nat → Val t} {b : Nat} {G : Ctx (FVal Val) Val}
    (hG : FGood ρ b G) {ts : List Ty} (xs : Tup Val ts) :
    FGood (fupdTup ρ b xs) (b + ts.length) G :=
  CtxPred.mono (fun h => ⟨h.1, (FKey.fev_fupdTup xs h.2.2.1).trans h.2.1, h.2.2.1.add,
    h.2.2.2.1.upd_all xs, h.2.2.2.2.upd_all xs⟩) hG

theorem FGood.append {ρ : (t : Ty) → Nat → Val t} {b : Nat} {G₁ G₂ : Ctx (FVal Val) Val}
    (h1 : FGood ρ b G₁) (h2 : FGood ρ b G₂) : FGood ρ b (G₁ ++ G₂) := CtxPred.append h1 h2

private theorem FGood.freshFVals_only (ρ : FEnv) :
    {ts : List Ty} → (xs : Tup Val ts) → (b : Nat) →
    FGood (fupdTup ρ b xs) (b + ts.length) (Tup.zip (freshFVals ts xs b) xs)
  | [], (), _ => CtxPred.nil _
  | _ :: ts, (x, xs), b => by
    simp only [freshFVals, tupFreshWith, Tup.zip, fupdTup, List.length_cons]
    refine CtxPred.cons ⟨rfl, ?_, by simp [FVal.fresh, FKey.FLt], ExtDefGood.none, trivial⟩ ?_
    · simp only [FVal.fresh, FKey.fev]; rw [fupdTup_lt (fupd ρ b x) xs (by omega), fupd_eq]
    · have ih := FGood.freshFVals_only (fupd ρ b x) xs (b + 1)
      rwa [show b + 1 + ts.length = b + (ts.length + 1) by omega] at ih

theorem FGood.freshFVals {ρ : (t : Ty) → Nat → Val t} {b : Nat} {G : Ctx (FVal Val) Val}
    (hG : FGood ρ b G) {ts : List Ty} (xs : Tup Val ts) :
    FGood (fupdTup ρ b xs) (b + ts.length) (Tup.zip (freshFVals ts xs b) xs ++ G) :=
  (FGood.freshFVals_only ρ xs b).append (hG.upd_all xs)

theorem FGood.freshOne {ρ : (t : Ty) → Nat → Val t} {b : Nat} {G : Ctx (FVal Val) Val}
    (hG : FGood ρ b G) {t : Ty} (v : Val t) :
    FGood (fupd ρ b v) (b + 1) (⟨t, FVal.fresh v b, v⟩ :: G) :=
  hG.freshFVals (ts := [t]) (v, ())

private theorem FGood.cons_ext {ρ : FEnv} {b n : Nat} {G : Ctx (FVal Val) Val}
    (hG : FGood ρ b G) (k : ExtKind) {m : Nat} (hpos : 0 < m) (hlt : m < n)
    {src : Arg Val (.bits m)} {srcKey : FKey (.bits m)}
    (hsk : srcKey.fev ρ = src.val) (hflt : srcKey.FLt b) :
    let v := k.eval n src.val
    FGood (fupdTup ρ b (ts := [.bits n]) (v, ())) (b + 1)
      (⟨.bits n, ⟨.var v, .var b, some ⟨k, m, hpos, hlt, src, srcKey⟩, none⟩, v⟩ :: G) := by
  refine (hG.upd_all (ts := [.bits n]) (k.eval n src.val, ())).cons ?_
  refine ⟨rfl, by simp [FKey.fev, fupdTup, fupd_eq], Nat.lt_succ_self b, ?_, trivial⟩
  refine ⟨?_, (FKey.fev_fupdTup _ hflt).trans hsk, hflt.add⟩
  cases k <;> simp [ExtKind.eval_sext, ExtKind.eval_zext]

private theorem FGood.cons_inv {ρ : FEnv} {b : Nat} {G : Ctx (FVal Val) Val}
    (hG : FGood ρ b G) (k : InvKind) {t : Ty} (hok : invOpOk k t)
    {src : Arg Val t} {srcKey : FKey t} {v : Val t}
    (hv : v = invOpVal k t src.val) (hsk : srcKey.fev ρ = src.val) (hflt : srcKey.FLt b) :
    FGood (fupdTup ρ b (ts := [t]) (v, ())) (b + 1)
      (⟨t, ⟨.var v, .var b, .none, some ⟨k, src, srcKey⟩⟩, v⟩ :: G) :=
  (hG.upd_all (ts := [t]) (v, ())).cons ⟨rfl, by simp [FKey.fev, fupdTup, fupd_eq],
    Nat.lt_succ_self b, ExtDefGood.none, hok, hv, (FKey.fev_fupdTup _ hflt).trans hsk, hflt.add⟩

def SimpAct.vals {sig : List Ty} (vs : Tup Val sig) : {rs : List Ty} → SimpAct sig rs → Tup Val rs
  | [], () => ()
  | _ :: _, (.imm c, act) => (c, SimpAct.vals vs act)
  | _ :: _, (.arg i, act) => (vs.get i, SimpAct.vals vs act)

theorem vals_get : {sig : List Ty} → (as : Tup (Arg Val) sig) → {u : Ty} → (i : Member u sig) →
    (vals as).get i = (as.get i).val
  | _ :: _, (_, _), _, .here => rfl
  | _ :: _, (_, bs), _, .there i => vals_get bs i

theorem ArgRel.fout_val {G : Ctx (FVal Val) Val} {ρ : (t : Ty) → Nat → Val t} {b : Nat}
    (hG : FGood ρ b G) {t : Ty} {a₁ : Arg (FVal Val) t} {a₂ : Arg Val t} :
    ArgRel G t a₁ a₂ → a₁.fout.val = a₂.val | .var h => (hG _ h).1 | .imm _ => rfl

theorem ArgRel.fkey_ev {G : Ctx (FVal Val) Val} {ρ : (t : Ty) → Nat → Val t} {b : Nat}
    (hG : FGood ρ b G) {t : Ty} {a₁ : Arg (FVal Val) t} {a₂ : Arg Val t} :
    ArgRel G t a₁ a₂ → a₁.fkey.fev ρ = a₂.val | .var h => (hG _ h).2.1 | .imm _ => rfl

theorem TRel.fout_vals {G : Ctx (FVal Val) Val} {ρ : (t : Ty) → Nat → Val t} {b : Nat}
    (hG : FGood ρ b G) {ts : List Ty} {as₁ : Tup (Arg (FVal Val)) ts} {as₂ : Tup (Arg Val) ts}
    (h : TRel (ArgRel G) as₁ as₂) : vals (tupMapArg (fun _ => Arg.fout) as₁) = vals as₂ :=
  TRel.tupMapArg_vals (fun _ => Arg.fout) (fun ha => ha.fout_val hG) h

theorem OpRel.fout_wp {G : Ctx (FVal Val) Val} {ρ : (t : Ty) → Nat → Val t} {b : Nat}
    (hG : FGood ρ b G) {rs : List Ty} {op₁ : Op (FVal Val) rs} {op₂ : Op Val rs}
    (ho : OpRel G op₁ op₂) {P : Tup Val rs → Prop} (hw : op₂.wp P) :
    (⟨op₁.code, tupMapArg (fun _ => Arg.fout) op₁.args⟩ : Op Val rs).wp P := by
  cases ho with | mk _ hargs => simpa only [Op.wp, TRel.fout_vals hG hargs] using hw

theorem ArgRel.fkey_FLt {G : Ctx (FVal Val) Val} {ρ : (t : Ty) → Nat → Val t} {b : Nat}
    (hG : FGood ρ b G) {t : Ty} {a₁ : Arg (FVal Val) t} {a₂ : Arg Val t} :
    ArgRel G t a₁ a₂ → a₁.fkey.FLt b | .var h => (hG _ h).2.2.1 | .imm _ => trivial

theorem ArgRel.fext_good {G : Ctx (FVal Val) Val} {ρ : (t : Ty) → Nat → Val t} {b : Nat}
    (hG : FGood ρ b G) {t : Ty} {a₁ : Arg (FVal Val) t} {a₂ : Arg Val t} :
    ArgRel G t a₁ a₂ → ExtDefGood ρ b a₁.fext a₂.val
  | .var h => (hG _ h).2.2.2.1 | .imm _ => ExtDefGood.none

theorem ArgRel.finv_good {G : Ctx (FVal Val) Val} {ρ : (t : Ty) → Nat → Val t} {b : Nat}
    (hG : FGood ρ b G) {t : Ty} {a₁ : Arg (FVal Val) t} {a₂ : Arg Val t} :
    ArgRel G t a₁ a₂ → UnInvOptGood ρ b a₁.finv a₂.val
  | .var h => (hG _ h).2.2.2.2 | .imm _ => trivial

private theorem ArgRel.fpair_good {G : Ctx (FVal Val) Val} {ρ : FEnv} {b : Nat}
    (hG : FGood ρ b G) {t : Ty} {a₁ : Arg (FVal Val) t} {a₂ : Arg Val t} :
    ArgRel G t a₁ a₂ → FValGood ρ b a₁.fpair a₂.val
  | .var h => hG _ h | .imm _ => ⟨rfl, rfl, trivial, ExtDefGood.none, trivial⟩

private def applySimpActRhs {sig : List Ty} {W : Ty → Type}
    (fImm : ∀ {t : Ty}, Val t → W t) (fArg : ∀ {t : Ty}, Member t sig → W t) :
    {rs : List Ty} → SimpAct sig rs → Tup W rs
  | [], () => ()
  | _ :: _, (.imm c, act) => (fImm c, applySimpActRhs fImm fArg act)
  | _ :: _, (.arg i, act) => (fArg i, applySimpActRhs fImm fArg act)

private theorem CtxPred.apply_simpAct {V₁ W : Ty → Type}
    {R : (t : Ty) → FVal V₁ t → W t → Prop} {G : Ctx (FVal V₁) W} (hG : CtxPred R G)
    {sig : List Ty} {as₁ : Tup (Arg (FVal V₁)) sig}
    (fImm : ∀ {t : Ty}, Val t → W t) (fArg : ∀ {t : Ty}, Member t sig → W t)
    (hImm : ∀ {t : Ty} (c : Val t), R t (fimm c) (fImm c))
    (hArg : ∀ {t : Ty} (i : Member t sig), R t (as₁.get i).fpair (fArg i)) :
    {rs : List Ty} → (act : SimpAct sig rs) →
    CtxPred R (Tup.zip (act.apply as₁) (applySimpActRhs fImm fArg act) ++ G)
  | [], () => hG
  | _ :: _, (.imm c, act) =>
    CtxPred.cons (hImm c) (CtxPred.apply_simpAct hG fImm fArg hImm hArg act)
  | _ :: _, (.arg i, act) =>
    CtxPred.cons (hArg i) (CtxPred.apply_simpAct hG fImm fArg hImm hArg act)

private theorem applySimpActRhs_vals {sig : List Ty} (vs : Tup Val sig) :
    {rs : List Ty} → (act : SimpAct sig rs) →
    applySimpActRhs (fun c => c) (fun i => vs.get i) act = SimpAct.vals vs act
  | [], () => rfl
  | _ :: _, (.imm _, act) => congrArg (_, ·) (applySimpActRhs_vals vs act)
  | _ :: _, (.arg _, act) => congrArg (_, ·) (applySimpActRhs_vals vs act)

theorem FGood.apply_simpAct {G : Ctx (FVal Val) Val} {ρ : (t : Ty) → Nat → Val t} {b : Nat}
    (hG : FGood ρ b G) {sig : List Ty} {as₁ : Tup (Arg (FVal Val)) sig}
    {as₂ : Tup (Arg Val) sig} (has : TRel (ArgRel G) as₁ as₂) :
    {rs : List Ty} → (act : SimpAct sig rs) →
    FGood ρ b (Tup.zip (act.apply as₁) (SimpAct.vals (vals as₂) act) ++ G) := by
  intro rs act; rw [← applySimpActRhs_vals (vals as₂) act]
  exact CtxPred.apply_simpAct hG (fun c => c) (fun i => (vals as₂).get i)
    (fun _ => ⟨rfl, rfl, trivial, ExtDefGood.none, trivial⟩)
    (fun i => by rw [vals_get]; exact (TRel.get i has).fpair_good hG) act

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
    (ha : ArgRel G t a₁ a₂) {c : Val t} (hc : a₁.fout.imm? = some c) : a₂.val = c :=
  (ha.fout_val hG).symm.trans (imm?_eq_some_val hc)

theorem ArgRel.fkey_beq_val {G : Ctx (FVal Val) Val} {ρ : (t : Ty) → Nat → Val t} {b : Nat}
    (hG : FGood ρ b G) {t : Ty} {a₁ b₁ : Arg (FVal Val) t} {a₂ b₂ : Arg Val t}
    (ha : ArgRel G t a₁ a₂) (hb : ArgRel G t b₁ b₂) (heq : (a₁.fkey == b₁.fkey) = true) :
    a₂.val = b₂.val :=
  (ha.fkey_ev hG).symm.trans
    ((eq_of_beq (α := FKey t) heq ▸ rfl : a₁.fkey.fev ρ = b₁.fkey.fev ρ).trans (hb.fkey_ev hG))

private theorem SimpAct.vals_simpImms {sig : List Ty} (vs : Tup Val sig) :
    {rs : List Ty} → (res : Tup Val rs) → SimpAct.vals vs (simpImms (sig := sig) res) = res
  | [], () => rfl
  | _ :: _, (_, res) => congrArg (_, ·) (SimpAct.vals_simpImms vs res)

/-! ## `BinOpLaw` dispatchers and `OpRel.simpAct_sound` -/

private theorem simpAct_shift_zero {G : Ctx (FVal Val) Val} {ρ : FEnv} {b : Nat}
    (hG : FGood ρ b G) {t : Ty} {a₁ b₁ : Arg (FVal Val) t} {a₂ b₂ : Arg Val t}
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
  split at hact; · cases hact
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
          (fun t _ => zeroVal t) t (fun _ => hnf0) b₂.val (fun y => hf0 y) (hbool := fun _ => rfl)
        simpa [SimpAct.vals, hnf0, vals, ha.isZero hG haz, hsh] using hw
      · cases hact

private theorem simpAct_bin_zero_add {G : Ctx (FVal Val) Val} {ρ : FEnv} {b : Nat}
    (hG : FGood ρ b G) {t : Ty} {a₁ b₁ : Arg (FVal Val) t} {a₂ b₂ : Arg Val t}
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

private theorem simpAct_ann_id {G : Ctx (FVal Val) Val} {ρ : FEnv} {b : Nat} (hG : FGood ρ b G)
    {t : Ty} {a₁ b₁ : Arg (FVal Val) t} {a₂ b₂ : Arg Val t}
    (ha : ArgRel G t a₁ a₂) (hb : ArgRel G t b₁ b₂)
    (fbv : ∀ {n}, BitVec n → BitVec n → BitVec n) (fbool : Bool → Bool → Bool)
    (allowFlt hasIdem : Bool) (hnf : allowFlt = false → t.hasFloat = false)
    (pArg qArg : Arg Val t → Bool) (kVal qVal : (u : Ty) → Val u)
    (hpEq : ∀ {a : Arg Val t}, pArg a = true → a.val = kVal t)
    (hqEq : ∀ {a : Arg Val t}, qArg a = true → a.val = qVal t) {act : SimpAct [t, t] [t]}
    (hact : (if pArg a₁.fout || pArg b₁.fout then some (.imm (kVal t), ())
      else if qArg b₁.fout then some (.arg .here, ())
      else if qArg a₁.fout then some (.arg (.there .here), ())
      else if hasIdem && (a₁.fkey == b₁.fkey) then some (.arg .here, ()) else none) = some act)
    {P : Tup Val [t] → Prop} (hw : P (lift2 fbv fbool t a₂.val b₂.val, ()))
    (hbv_pl : ∀ {n} (x : BitVec n), fbv (kVal (.bits n)) x = kVal (.bits n) := by
      intros; simp [zeroVal, oneVal, onesVal])
    (hbv_pr : ∀ {n} (x : BitVec n), fbv x (kVal (.bits n)) = kVal (.bits n) := by
      intros; simp [zeroVal, oneVal, onesVal])
    (hbv_qr : ∀ {n} (x : BitVec n), fbv x (qVal (.bits n)) = x := by
      intros; simp [zeroVal, oneVal, onesVal])
    (hbv_ql : ∀ {n} (x : BitVec n), fbv (qVal (.bits n)) x = x := by
      intros; simp [zeroVal, oneVal, onesVal])
    (hbv_id : ∀ {n} (x : BitVec n), hasIdem = true → fbv x x = x := by intro _ _ h; cases h)
    (hflt_pl : ∀ {f : Fmt} (x : BitVec f.width), allowFlt = true →
      fbv (kVal (.float f)) x = kVal (.float f) := by intro _ _ h; cases h)
    (hflt_pr : ∀ {f : Fmt} (x : BitVec f.width), allowFlt = true →
      fbv x (kVal (.float f)) = kVal (.float f) := by intro _ _ h; cases h)
    (hflt_qr : ∀ {f : Fmt} (x : BitVec f.width), allowFlt = true →
      fbv x (qVal (.float f)) = x := by intro _ _ h; cases h)
    (hflt_ql : ∀ {f : Fmt} (x : BitVec f.width), allowFlt = true →
      fbv (qVal (.float f)) x = x := by intro _ _ h; cases h)
    (hflt_id : ∀ {f : Fmt} (x : BitVec f.width), allowFlt = true →
      fbv x x = x := by intro _ _ h; cases h)
    (hbool_pl : ∀ x, fbool (kVal .bool) x = kVal .bool := by intro x; cases x <;> rfl)
    (hbool_pr : ∀ x, fbool x (kVal .bool) = kVal .bool := by intro x; cases x <;> rfl)
    (hbool_qr : ∀ x, fbool x (qVal .bool) = x := by intro x; cases x <;> rfl)
    (hbool_ql : ∀ x, fbool (qVal .bool) x = x := by intro x; cases x <;> rfl)
    (hbool_id : ∀ x, hasIdem = true → fbool x x = x := by intro _ h; cases h)
    (hk : ∀ s u, kVal (.pair s u) = (kVal s, kVal u) := by intros; rfl)
    (hq : ∀ s u, qVal (.pair s u) = (qVal s, qVal u) := by intros; rfl) :
    P (SimpAct.vals (vals (a₂, b₂, ())) act) := by
  split at hact
  · rename_i hor; cases hact
    rcases Bool.or_eq_true_iff.1 hor with haz | hbz
    · have h := lift2_law allowFlt fbv fbool (fun t _ => kVal t) (fun _ y => y)
        (fun t _ => kVal t) t hnf b₂.val hbv_pl hflt_pl hbool_pl
        (fun s u _ _ => hk s u) (fun _ _ _ _ => rfl) (fun s u _ _ => hk s u)
      simpa [SimpAct.vals, vals, (ha.fout_val hG).symm.trans (hpEq haz), h] using hw
    · have h := lift2_law allowFlt fbv fbool (fun _ y => y) (fun t _ => kVal t)
        (fun t _ => kVal t) t hnf a₂.val hbv_pr hflt_pr hbool_pr
        (fun _ _ _ _ => rfl) (fun s u _ _ => hk s u) (fun s u _ _ => hk s u)
      simpa [SimpAct.vals, vals, (hb.fout_val hG).symm.trans (hpEq hbz), h] using hw
  · split at hact
    · cases hact; next hbo =>
      have h := lift2_law allowFlt fbv fbool (fun _ y => y) (fun t _ => qVal t)
        (fun _ y => y) t hnf a₂.val hbv_qr hflt_qr hbool_qr
        (fun _ _ _ _ => rfl) (fun s u _ _ => hq s u) (fun _ _ _ _ => rfl)
      simpa [SimpAct.vals, Tup.get, vals, (hb.fout_val hG).symm.trans (hqEq hbo), h] using hw
    · split at hact
      · cases hact; next hao =>
        have h := lift2_law allowFlt fbv fbool (fun t _ => qVal t) (fun _ y => y)
          (fun _ y => y) t hnf b₂.val hbv_ql hflt_ql hbool_ql
          (fun s u _ _ => hq s u) (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
        simpa [SimpAct.vals, Tup.get, vals, (ha.fout_val hG).symm.trans (hqEq hao), h] using hw
      · split at hact
        · rename_i hid; cases hact; simp only [Bool.and_eq_true] at hid
          have h := lift2_law allowFlt fbv fbool (fun _ y => y) (fun _ y => y)
            (fun _ y => y) t hnf b₂.val (fun x => hbv_id x hid.1) hflt_id
            (fun x => hbool_id x hid.1)
          simpa [SimpAct.vals, Tup.get, vals, ha.fkey_beq_val hG hb hid.2, h] using hw
        · cases hact

private theorem simpAct_mulw_zero {G : Ctx (FVal Val) Val} {ρ : FEnv} {b : Nat} (hG : FGood ρ b G)
    {n : Nat} {a₁ b₁ : Arg (FVal Val) (.bits n)} {a₂ b₂ : Arg Val (.bits n)}
    (ha : ArgRel G (.bits n) a₁ a₂) (hb : ArgRel G (.bits n) b₁ b₂)
    {act : SimpAct [.bits n, .bits n] [.bits n, .bits n]}
    (hact : (if isZeroArg? a₁.fout || isZeroArg? b₁.fout then some (.imm 0#n, .imm 0#n, ())
      else none) = some act)
    (hi : BitVec n → BitVec n → BitVec n) (hhi0l : ∀ y, hi 0#n y = 0#n)
    (hhi0r : ∀ x, hi x 0#n = 0#n) {P : Tup Val [.bits n, .bits n] → Prop}
    (hw : P (a₂.val * b₂.val, hi a₂.val b₂.val, ())) :
    P (SimpAct.vals (vals (a₂, b₂, ())) act) := by
  split at hact
  · rename_i hor; cases hact; rcases Bool.or_eq_true_iff.1 hor with haz | hbz
    · simpa [SimpAct.vals, vals, ha.isZero hG haz, zeroVal, hhi0l] using hw
    · simpa [SimpAct.vals, vals, hb.isZero hG hbz, zeroVal, hhi0r] using hw
  · cases hact

private theorem simpAct_div_one {G : Ctx (FVal Val) Val} {ρ : FEnv} {b : Nat} (hG : FGood ρ b G)
    {n k : Nat} {b₁ : Arg (FVal Val) (.bits n)} {a₂ b₂ : Arg Val (.bits n)}
    (hb : ArgRel G (.bits n) b₁ b₂) {act : SimpAct [.bits n, .bits n] [.bits n]}
    {res : SimpElem (.bits n) [.bits n, .bits n]}
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

private theorem simpAct_div0 {G : Ctx (FVal Val) Val} {ρ : FEnv} {b : Nat} (hG : FGood ρ b G)
    {n k : Nat} {b₁ : Arg (FVal Val) (.bits n)} {a₂ b₂ : Arg Val (.bits n)}
    (hb : ArgRel G (.bits n) b₁ b₂) {act : SimpAct [.bits n, .bits n] [.bits n]}
    (hact : (if b₁.fout.imm? == some 0#n then some (.imm 0#n, ())
      else if k < n && (b₁.fout.imm? == some 1#n) then some (.arg .here, ()) else none) = some act)
    (op : BitVec n → BitVec n → BitVec n) (hop1 : k < n → op a₂.val 1#n = a₂.val)
    {P : Tup Val [.bits n] → Prop} (hw : P (if b₂.val = 0 then 0 else op a₂.val b₂.val, ())) :
    P (SimpAct.vals (vals (a₂, b₂, ())) act) := by
  split at hact
  · rename_i hbz; cases hact
    simpa [SimpAct.vals, Tup.get, vals, hb.fout_imm?_val hG (eq_of_beq hbz)] using hw
  · exact simpAct_div_one hG hb hact (fun x y => if y = 0 then 0 else op x y)
      (fun hk => by
        have hne : (1#n : BitVec n) ≠ 0 := by simpa using one_ne_zero_of_pos (by omega)
        simp only [hne, ↓reduceIte, hop1 hk, SimpAct.vals, Tup.get, vals]) hw

private def NarrowCmpOk (ρ : FEnv) {n : Nat} (o : CmpOp)
    (a₂ b₂ : Arg Val (.bits n)) (nc : NarrowCmp Val) : Prop :=
  nc.op.evalBits nc.lhs.val nc.rhs.val = o.evalBits a₂.val b₂.val ∧
  nc.lhsKey.fev ρ = nc.lhs.val ∧ nc.rhsKey.fev ρ = nc.rhs.val ∧ nc.op.isRefl = o.isRefl

private theorem narrowCmpCore_sound {G : Ctx (FVal Val) Val} {ρ : FEnv} {b : Nat} (hG : FGood ρ b G)
    {n : Nat} (o : CmpOp) {a₁ b₁ : Arg (FVal Val) (.bits n)} {a₂ b₂ : Arg Val (.bits n)}
    (ha : ArgRel G (.bits n) a₁ a₂) (hb : ArgRel G (.bits n) b₁ b₂) :
    NarrowCmpOk ρ o a₂ b₂ (narrowCmpCore o n a₁ b₁) := by
  have hbase : NarrowCmpOk ρ o a₂ b₂ ⟨n, o, a₁.fout, b₁.fout, a₁.fkey, b₁.fkey⟩ := by
    dsimp only [NarrowCmpOk]
    rw [ha.fout_val hG, hb.fout_val hG, ha.fkey_ev hG, hb.fkey_ev hG]; exact ⟨rfl, rfl, rfl, rfl⟩
  have hea := ha.fext_good hG; have heb := hb.fext_good hG
  dsimp only [narrowCmpCore]
  cases hfa : a₁.fext with
  | none => exact hbase
  | some ea =>
    rw [hfa] at hea; rcases ea with ⟨ka, ma, hposa, hlta, sxa, ska⟩
    have hae : a₂.val = ka.eval n sxa.val := hea.eval_eq
    cases himmb : b₁.fout.imm? with
    | some c =>
      have hbc := hb.fout_imm?_val hG himmb
      cases ka <;> (dsimp only; split)
      · rename_i hfit
        have hceq : ExtKind.eval .sext n (c.setWidth ma) = c := by
          simpa [ExtKind.eval_sext] using eq_of_beq hfit
        refine ⟨?_, hea.2.1, rfl, ExtKind.cmpOp_isRefl .sext o⟩
        have hc := ExtKind.cmpOp_evalBits hlta .sext o sxa.val (c.setWidth ma)
        simp only [hceq, ExtKind.cmpOp_sext] at hc
        simp only [Arg.val_imm]; rw [hae, hbc, ← hc]
      · exact hbase
      · rename_i hfit
        have hceq : ExtKind.eval .zext n (c.setWidth ma) = c := by
          simpa [ExtKind.eval_zext] using eq_of_beq hfit
        refine ⟨?_, hea.2.1, rfl, ExtKind.cmpOp_isRefl .zext o⟩
        have hc := ExtKind.cmpOp_evalBits hlta .zext o sxa.val (c.setWidth ma)
        simp only [hceq, ExtKind.cmpOp_zext] at hc
        simp only [Arg.val_imm]; rw [hae, hbc, ← hc]
      · exact hbase
    | none =>
      cases hfb : b₁.fext with
      | none => exact hbase
      | some eb =>
        rw [hfb] at heb; rcases eb with ⟨kb, mb, hposb, hltb, syb, skb⟩
        have hbe : b₂.val = kb.eval n syb.val := heb.eval_eq
        dsimp only
        cases ka <;> cases kb <;> dsimp only
        · split
          · rename_i hm; subst hm
            refine ⟨?_, hea.2.1, heb.2.1, ExtKind.cmpOp_isRefl .sext o⟩
            rw [hae, hbe, ← ExtKind.cmpOp_evalBits hlta .sext o, ExtKind.cmpOp_sext]
          · exact hbase
        · exact hbase
        · exact hbase
        · split
          · rename_i hm; subst hm
            refine ⟨?_, hea.2.1, heb.2.1, ExtKind.cmpOp_isRefl .zext o⟩
            rw [hae, hbe, ← ExtKind.cmpOp_evalBits hlta .zext o]; rfl
          · exact hbase

theorem narrowCmp_sound {G : Ctx (FVal Val) Val} {ρ : (t : Ty) → Nat → Val t} {b : Nat}
    (hG : FGood ρ b G) {n : Nat} (o : CmpOp)
    {a₁ b₁ : Arg (FVal Val) (.bits n)} {a₂ b₂ : Arg Val (.bits n)}
    (ha : ArgRel G (.bits n) a₁ a₂) (hb : ArgRel G (.bits n) b₁ b₂) :
    let nc := narrowCmp o n a₁ b₁
    nc.op.evalBits nc.lhs.val nc.rhs.val = o.evalBits a₂.val b₂.val ∧
    nc.lhsKey.fev ρ = nc.lhs.val ∧ nc.rhsKey.fev ρ = nc.rhs.val ∧ nc.op.isRefl = o.isRefl := by
  dsimp only [narrowCmp]; cases a₁.fout.imm? <;> cases b₁.fout.imm?
  · exact narrowCmpCore_sound hG o ha hb
  · exact narrowCmpCore_sound hG o ha hb
  · obtain ⟨hev, hlk, hrk, hrefl⟩ := narrowCmpCore_sound hG o.swap hb ha
    exact ⟨hev.trans (CmpOp.swap_evalBits o a₂.val b₂.val), hlk, hrk,
      hrefl.trans (CmpOp.isRefl_swap o)⟩
  · exact narrowCmpCore_sound hG o ha hb

theorem OpRel.simpAct_sound {G : Ctx (FVal Val) Val} {ρ : (t : Ty) → Nat → Val t} {b : Nat}
    (hG : FGood ρ b G) {sig rs : List Ty} {code : OpCode sig rs}
    {args₁ : Tup (Arg (FVal Val)) sig} {args₂ : Tup (Arg Val) sig}
    (hargs : TRel (ArgRel G) args₁ args₂) {act : SimpAct sig rs}
    (hact : ({ code := code, args := args₁ } : Op (FVal Val) rs).simpAct = some act)
    {P : Tup Val rs → Prop} (hw : code.wp (vals args₂) P) :
    P (SimpAct.vals (vals args₂) act) ∧
      FGood ρ b (Tup.zip (act.apply args₁) (SimpAct.vals (vals args₂) act) ++ G) := by
  refine ⟨?_, FGood.apply_simpAct hG hargs act⟩
  delta Op.simpAct at hact; dsimp only at hact
  cases hconst : (tupImms? (tupMapArg (fun _ => Arg.fout) args₁)).bind code.eval? with
  | some res =>
    rw [hconst] at hact; cases hact; simp only [Option.bind_eq_some_iff] at hconst
    rcases hconst with ⟨cs, hcs, hev⟩
    have hvals : vals args₂ = cs := (TRel.fout_vals hG hargs).symm.trans (tupImms?_vals hcs)
    rw [SimpAct.vals_simpImms]
    exact code.eval?_sound (vals args₂) P (by rw [hvals]; exact hev) hw
  | none =>
    rw [hconst] at hact; dsimp only at hact
    cases code with
    | copy _ => rcases hargs with _ | ⟨_, _⟩; cases hact; exact hw
    | neg t =>
      cases t with | bool => rcases hargs with _ | ⟨_, _⟩; cases hact; exact hw | _ => cases hact
    | add t =>
      rcases args₂ with ⟨a₂, b₂, ⟨⟩⟩; rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩; dsimp only at hact
      split at hact; · cases hact
      · next hnf =>
        have hf0 : t.hasFloat = false := Bool.eq_false_iff.mpr hnf
        exact simpAct_bin_zero_add hG ha hb (· + ·) (· ^^ ·) false (fun _ => hf0) hact
          (by simpa [OpCode.wp_add, hf0, vals] using hw)
    | sub t =>
      rcases args₂ with ⟨a₂, b₂, ⟨⟩⟩; rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩; dsimp only at hact
      split at hact; · cases hact
      · next hnf =>
        have hf0 : t.hasFloat = false := Bool.eq_false_iff.mpr hnf
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
      rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, ⟨⟩⟩
      rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩; dsimp only at hact
      split at hact; · cases hact
      · next hnf =>
        have hf0 : t.hasFloat = false := Bool.eq_false_iff.mpr hnf
        have hact' : (if isZeroArg? a₁.fout || isZeroArg? b₁.fout then some (.imm (zeroVal t), ())
          else if isOneArg? b₁.fout then some (.arg .here, ())
          else if isOneArg? a₁.fout then some (.arg (.there .here), ())
          else if false && (a₁.fkey == b₁.fkey) then some (.arg .here, ()) else none) = some act :=
          by simpa using hact
        exact simpAct_ann_id hG ha hb (· * ·) (· && ·) false false (fun _ => hf0)
          isZeroArg? isOneArg? zeroVal oneVal isZeroArg?_eq isOneArg?_eq hact'
          (by simpa [OpCode.wp_mul, hf0, vals] using hw)
    | and t =>
      rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, ⟨⟩⟩
      rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩; dsimp only at hact
      have hact' : (if isZeroArg? a₁.fout || isZeroArg? b₁.fout then some (.imm (zeroVal t), ())
        else if isOnesArg? b₁.fout then some (.arg .here, ())
        else if isOnesArg? a₁.fout then some (.arg (.there .here), ())
        else if true && (a₁.fkey == b₁.fkey) then some (.arg .here, ()) else none) = some act :=
        by simpa using hact
      exact simpAct_ann_id hG ha hb (· &&& ·) (· && ·) true true (fun h => by cases h)
        isZeroArg? isOnesArg? zeroVal onesVal isZeroArg?_eq isOnesArg?_eq hact'
        (by simpa [OpCode.wp_and, vals] using hw)
        (hbv_id := fun _ _ => by simp) (hflt_pl := fun _ _ => by simp [zeroVal])
        (hflt_pr := fun _ _ => by simp [zeroVal]) (hflt_qr := fun _ _ => by simp [onesVal])
        (hflt_ql := fun _ _ => by simp [onesVal]) (hflt_id := fun _ _ => by simp)
        (hbool_id := fun _ _ => Bool.and_self _)
    | or t =>
      rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, ⟨⟩⟩
      rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩; dsimp only at hact
      have hact' : (if isOnesArg? a₁.fout || isOnesArg? b₁.fout then some (.imm (onesVal t), ())
        else if isZeroArg? b₁.fout then some (.arg .here, ())
        else if isZeroArg? a₁.fout then some (.arg (.there .here), ())
        else if true && (a₁.fkey == b₁.fkey) then some (.arg .here, ()) else none) = some act :=
        by simpa using hact
      exact simpAct_ann_id hG ha hb (· ||| ·) (· || ·) true true (fun h => by cases h)
        isOnesArg? isZeroArg? onesVal zeroVal isOnesArg?_eq isZeroArg?_eq hact'
        (by simpa [OpCode.wp_or, vals] using hw)
        (hbv_id := fun _ _ => by simp) (hflt_pl := fun _ _ => by simp [onesVal])
        (hflt_pr := fun _ _ => by simp [onesVal]) (hflt_qr := fun _ _ => by simp [zeroVal])
        (hflt_ql := fun _ _ => by simp [zeroVal]) (hflt_id := fun _ _ => by simp)
        (hbool_id := fun _ _ => Bool.or_self _)
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
      · next h =>
        cases hact
        have he := ternlog_simp_eq imm 0#8 h (fun t _ _ _ => zeroVal t) t a₂.val b₂.val c₂.val
        simpa [SimpAct.vals, he] using hw'
      · split at hact
        · next h =>
          cases hact
          have he := ternlog_simp_eq imm 0xff#8 h (fun t _ _ _ => onesVal t) t a₂.val b₂.val c₂.val
          simpa [SimpAct.vals, he] using hw'
        · split at hact
          · next h =>
            cases hact
            have he := ternlog_simp_eq imm 0xf0#8 h (fun _ a _ _ => a) t a₂.val b₂.val c₂.val
            simpa [SimpAct.vals, Tup.get, vals, he] using hw'
          · split at hact
            · next h =>
              cases hact
              have he := ternlog_simp_eq imm 0xcc#8 h (fun _ _ b _ => b) t a₂.val b₂.val c₂.val
              simpa [SimpAct.vals, Tup.get, vals, he] using hw'
            · split at hact
              · next h =>
                cases hact
                have he := ternlog_simp_eq imm 0xaa#8 h (fun _ _ _ c => c) t a₂.val b₂.val c₂.val
                simpa [SimpAct.vals, Tup.get, vals, he] using hw'
              · cases hact
    | shl _ =>
      rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩; dsimp only at hact
      exact simpAct_shift_zero hG ha hb (fun {n} x y => x <<< (y.toNat % n))
        (fun x => by simp) (fun y => by simp) hact (by simpa [OpCode.wp_shl, vals] using hw)
    | lshr _ =>
      rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩; dsimp only at hact
      exact simpAct_shift_zero hG ha hb (fun {n} x y => x >>> (y.toNat % n))
        (fun x => by simp) (fun y => by simp) hact (by simpa [OpCode.wp_lshr, vals] using hw)
    | ashr _ =>
      rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩; dsimp only at hact
      exact simpAct_shift_zero hG ha hb (fun {n} x y => x.sshiftRight (y.toNat % n))
        (fun x => by simp) (fun y => by simp [BitVec.zero_sshiftRight])
        hact (by simpa [OpCode.wp_ashr, vals] using hw)
    | rotl _ =>
      rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩; dsimp only at hact
      exact simpAct_shift_zero hG ha hb (fun {n} x y => x.rotateLeft (y.toNat % n))
        (fun x => by ext i _; simp [BitVec.rotateLeft, BitVec.rotateLeftAux])
        (fun y => by ext i _; simp [BitVec.rotateLeft, BitVec.rotateLeftAux])
        hact (by simpa [OpCode.wp_rotl, vals] using hw)
    | rotr _ =>
      rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩; dsimp only at hact
      exact simpAct_shift_zero hG ha hb (fun {n} x y => x.rotateRight (y.toNat % n))
        (fun x => by ext i _; simp [BitVec.rotateRight, BitVec.rotateRightAux])
        (fun y => by ext i _; simp [BitVec.rotateRight, BitVec.rotateRightAux])
        hact (by simpa [OpCode.wp_rotr, vals] using hw)
    | cmp o t _ h =>
      subst h; rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, ⟨⟩⟩
      rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩
      cases t with
      | bits n =>
        obtain ⟨hev, hlk, hrk, hrefl⟩ := narrowCmp_sound hG o ha hb
        dsimp only at hact hev hlk hrk hrefl
        split at hact
        · next heq =>
          cases hact
          have hveq : (narrowCmp o n a₁ b₁).lhs.val = (narrowCmp o n a₁ b₁).rhs.val :=
            hlk.symm.trans ((congrArg (FKey.fev ρ) (eq_of_beq heq)).trans hrk)
          simp only [SimpAct.vals, OpCode.wp_cmp, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte,
            liftCmp, vals, cast_eq] at hw ⊢
          rw [← hev, hveq, cmpOp_evalBits_self, hrefl] at hw; exact hw
        · cases hbd : (narrowCmp o n a₁ b₁).rhs.imm?.bind
              (cmpImmBound? (narrowCmp o n a₁ b₁).op (narrowCmp o n a₁ b₁).w) with
          | none => rw [hbd] at hact; cases hact
          | some res =>
            rw [hbd] at hact; cases hact; simp only [Option.bind_eq_some_iff] at hbd
            rcases hbd with ⟨c, hc, hres⟩
            simp only [SimpAct.vals, OpCode.wp_cmp, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte,
              liftCmp, vals, cast_eq] at hw ⊢
            rw [← hev, imm?_eq_some_val hc, cmpImmBound?_sound _ _ _ hres] at hw; exact hw
      | float _ => simp [OpCode.wp_cmp, Ty.hasFloat] at hw
      | bool =>
        dsimp only at hact; split at hact
        · next heq =>
          cases hact
          simpa [SimpAct.vals, Tup.get, OpCode.wp_cmp, liftCmp, splatMaskVal, vals,
            ha.fkey_beq_val hG hb heq, cmpOp_evalBool_self] using hw
        · cases hact
      | pair _ _ =>
        dsimp only at hact; split at hact
        · next hcond =>
          cases hact; simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcond
          simpa [SimpAct.vals, Tup.get, OpCode.wp_cmp, hcond.1, vals,
            ha.fkey_beq_val hG hb hcond.2, liftCmp_self _ _ _ hcond.1] using hw
        · cases hact
    | select t =>
      rcases args₁ with ⟨c₁, a₁, b₁, ⟨⟩⟩; rcases args₂ with ⟨c₂, a₂, b₂, ⟨⟩⟩
      rcases hargs with _ | ⟨hc, _ | ⟨ha, _ | ⟨hb, _⟩⟩⟩; dsimp only at hact
      cases hci : c₁.fout.imm? with
      | some b =>
        rw [hci] at hact; have hcv := hc.fout_imm?_val hG hci
        cases b <;> cases hact <;>
          simpa [SimpAct.vals, Tup.get, OpCode.wp_select, vals, hcv] using hw
      | none =>
        rw [hci] at hact; dsimp only at hact; split at hact
        · next heq =>
          cases hact; simpa [SimpAct.vals, Tup.get, OpCode.wp_select, vals,
            ha.fkey_beq_val hG hb heq] using hw
        · cases t with
          | bool =>
            dsimp only at hact; split at hact
            · next htf =>
              cases hact; simp only [Bool.and_eq_true, beq_iff_eq] at htf
              simpa [SimpAct.vals, Tup.get, OpCode.wp_select, vals,
                ha.fout_imm?_val hG htf.1, hb.fout_imm?_val hG htf.2] using hw
            · cases hact
          | _ => cases hact
    | blend t _ h =>
      subst h; rcases args₁ with ⟨c₁, a₁, b₁, ⟨⟩⟩; rcases args₂ with ⟨c₂, a₂, b₂, ⟨⟩⟩
      rcases hargs with _ | ⟨hc, _ | ⟨ha, _ | ⟨hb, _⟩⟩⟩; dsimp only at hact
      cases hci : c₁.fout.imm? with
      | some mc =>
        rw [hci] at hact; dsimp only at hact; have hcv := hc.fout_imm?_val hG hci
        split at hact
        · next ht =>
          cases hact; have hm := eq_of_beq ht; simp only [cast_eq] at hm
          simpa [SimpAct.vals, Tup.get, OpCode.wp_blend, vals, hcv, hm,
            blendV_splatMask_true] using hw
        · split at hact
          · next hf =>
            cases hact; have hm := eq_of_beq hf; simp only [cast_eq] at hm
            simpa [SimpAct.vals, Tup.get, OpCode.wp_blend, vals, hcv, hm,
              blendV_splatMask_false] using hw
          · split at hact
            · next heq =>
              cases hact; simpa [SimpAct.vals, Tup.get, OpCode.wp_blend, vals,
                ha.fkey_beq_val hG hb heq, blendV_self] using hw
            · cases hact
      | none =>
        rw [hci] at hact; dsimp only at hact; split at hact
        · next heq =>
          cases hact; simpa [SimpAct.vals, Tup.get, OpCode.wp_blend, vals,
            ha.fkey_beq_val hG hb heq, blendV_self] using hw
        · cases hact
    | zext m n | trunc m n =>
      rcases hargs with _ | ⟨_, _⟩; dsimp only at hact; split at hact
      · next hmn =>
        subst hmn; cases hact; dsimp only [OpCode.wp] at hw
        simp only [SimpAct.vals, Tup.get, vals, cast_eq, BitVec.setWidth_eq] at hw ⊢; exact hw.2
      · cases hact
    | sext m n =>
      rcases hargs with _ | ⟨_, _⟩; dsimp only at hact; split at hact
      · next hmn =>
        subst hmn; cases hact
        simp only [SimpAct.vals, Tup.get, OpCode.wp_sext, vals, cast_eq, signExtend_self] at hw ⊢
        exact hw.2
      · cases hact
    | addc n =>
      rcases hargs with _ | ⟨ha, _ | ⟨hb, _ | ⟨hc, _⟩⟩⟩; dsimp only at hact
      split at hact
      · next hcf =>
        have hc0 := hc.fout_imm?_val hG (eq_of_beq hcf); split at hact
        · next hbz =>
          cases hact
          simp only [SimpAct.vals, Tup.get, OpCode.wp_addc, vals, hc0, hb.isZero hG hbz, zeroVal,
            Bool.toNat_false, BitVec.add_zero, BitVec.toNat_ofNat,
            Nat.zero_mod, Nat.add_zero] at hw ⊢
          simpa [Nat.not_le_of_lt (BitVec.isLt _)] using hw
        · split at hact
          · next haz =>
            cases hact
            simp only [SimpAct.vals, Tup.get, OpCode.wp_addc, vals, hc0, ha.isZero hG haz, zeroVal,
              Bool.toNat_false, BitVec.zero_add, BitVec.add_zero, BitVec.toNat_ofNat,
              Nat.zero_mod, Nat.zero_add, Nat.add_zero] at hw ⊢
            simpa [Nat.not_le_of_lt (BitVec.isLt _)] using hw
          · cases hact
      · cases hact
    | subb n =>
      rcases hargs with _ | ⟨ha, _ | ⟨hb, _ | ⟨hc, _⟩⟩⟩; dsimp only at hact
      split at hact
      · next hcf =>
        have hc0 := hc.fout_imm?_val hG (eq_of_beq hcf); split at hact
        · next hbz =>
          cases hact; simpa [SimpAct.vals, Tup.get, OpCode.wp_subb, vals, hc0,
            hb.isZero hG hbz, zeroVal] using hw
        · split at hact
          · next heq =>
            cases hact; simpa [SimpAct.vals, Tup.get, OpCode.wp_subb, vals, hc0,
              ha.fkey_beq_val hG hb heq] using hw
          · cases hact
      · cases hact
    | umulw n =>
      rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩; dsimp only at hact
      exact simpAct_mulw_zero hG ha hb hact (fun x y => BitVec.ofNat n (x.toNat * y.toNat / 2 ^ n))
        (fun _ => by simp) (fun _ => by simp) (by simpa [OpCode.wp_umulw, vals] using hw)
    | smulw n =>
      rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩; dsimp only at hact
      exact simpAct_mulw_zero hG ha hb hact
        (fun x y => (BitVec.ofInt (n + n) (x.toInt * y.toInt)).extractLsb' n n)
        (fun _ => by simp [BitVec.toInt_zero]) (fun _ => by simp [BitVec.toInt_zero])
        (by simpa [OpCode.wp_smulw, vals] using hw)
    | udiv _ =>
      rcases hargs with _ | ⟨_, _ | ⟨hb, _⟩⟩; dsimp only at hact
      exact simpAct_div_one hG hb hact (· / ·)
        (fun hk => by simp [SimpAct.vals, Tup.get, vals, div_one_of_pos hk])
        (by simpa [OpCode.wp_udiv, vals] using hw.2)
    | sdiv _ =>
      rcases hargs with _ | ⟨_, _ | ⟨hb, _⟩⟩; dsimp only at hact
      exact simpAct_div_one hG hb hact BitVec.sdiv
        (fun hk => by simp [SimpAct.vals, Tup.get, vals, sdiv_one_of_one_lt hk])
        (by simpa [OpCode.wp_sdiv, vals] using hw.2)
    | urem _ =>
      rcases hargs with _ | ⟨_, _ | ⟨hb, _⟩⟩; dsimp only at hact
      exact simpAct_div_one hG hb hact (· % ·)
        (fun hk => by simp [SimpAct.vals, mod_one_of_pos hk])
        (by simpa [OpCode.wp_urem, vals] using hw.2)
    | srem _ =>
      rcases hargs with _ | ⟨_, _ | ⟨hb, _⟩⟩; dsimp only at hact
      exact simpAct_div_one hG hb hact BitVec.srem
        (fun hk => by simp [SimpAct.vals, srem_one_of_one_lt hk])
        (by simpa [OpCode.wp_srem, vals] using hw.2)
    | udiv0 _ =>
      rcases hargs with _ | ⟨_, _ | ⟨hb, _⟩⟩; dsimp only at hact
      exact simpAct_div0 hG hb hact (· / ·) (fun hn => div_one_of_pos hn _)
        (by simpa [OpCode.wp_udiv0, vals] using hw)
    | sdiv0 _ =>
      rcases hargs with _ | ⟨_, _ | ⟨hb, _⟩⟩; dsimp only at hact
      exact simpAct_div0 hG hb hact BitVec.sdiv (fun hn => sdiv_one_of_one_lt hn _)
        (by simpa [OpCode.wp_sdiv0, vals] using hw)
    | bitcast t u _ =>
      rcases hargs with _ | ⟨_, _⟩; dsimp only at hact
      cases hdec : tyDecEq t u with
      | isFalse _ => simp [hdec] at hact
      | isTrue htu =>
        subst htu; simp only [hdec, cast_eq] at hact; cases hact
        simpa [SimpAct.vals, Tup.get, OpCode.wp_bitcast, vals, ofBits_toBits] using hw
    | _ => cases hact

/-! ## Provenance elimination (`Op.simpProv?`) and rewrite soundness (`Op.foldRewrite`) -/

private theorem simpProv_inv_sound {G : Ctx (FVal Val) Val} {ρ : FEnv} {b : Nat} (hG : FGood ρ b G)
    {t : Ty} (k : InvKind) (hok : invOpOk k t) {a₁ : Arg (FVal Val) t} {a₂ : Arg Val t}
    (ha : ArgRel G t a₁ a₂) {iv : UnInv Val t} (hinv : a₁.finv = some iv)
    (hk : (iv.kind == k) = true) {P : Tup Val [t] → Prop} (hw : P (invOpVal k t a₂.val, ())) :
    ∃ xs, P xs ∧ FGood ρ b (Tup.zip (⟨iv.src, iv.srcKey, .none, none⟩, ()) xs ++ G) := by
  have hgood := ha.finv_good hG; rw [hinv] at hgood
  obtain ⟨_, hv, hsk, hflt⟩ := hgood
  have hv' : invOpVal k t a₂.val = iv.src.val := by
    rw [hv, eq_of_beq hk]; exact invOpVal_invol k t hok iv.src.val
  exact ⟨(invOpVal k t a₂.val, ()), hw,
    hG.cons ⟨hv'.symm, hv' ▸ hsk, hflt, ExtDefGood.none, trivial⟩⟩

theorem OpRel.simpProv?_sound {G : Ctx (FVal Val) Val} {ρ : (t : Ty) → Nat → Val t} {b : Nat}
    (hG : FGood ρ b G) {sig ts : List Ty} {code : OpCode sig ts}
    {args₁ : Tup (Arg (FVal Val)) sig} {args₂ : Tup (Arg Val) sig}
    (hargs : TRel (ArgRel G) args₁ args₂) {res : Tup (FVal Val) ts}
    (hprov : ({ code := code, args := args₁ } : Op (FVal Val) ts).simpProv? = some res)
    {P : Tup Val ts → Prop} (hw : code.wp (vals args₂) P) :
    ∃ xs, P xs ∧ FGood ρ b (Tup.zip res xs ++ G) := by
  cases code with
  | not _ =>
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩; rcases hargs with _ | ⟨ha, _⟩
    dsimp only [Op.simpProv?] at hprov
    cases hf : a₁.finv with
    | none => simp [hf] at hprov
    | some iv =>
      simp only [hf] at hprov; split at hprov
      · next hk =>
        cases hprov
        exact simpProv_inv_sound hG .not_ trivial ha hf hk
          (by simpa [OpCode.wp_not, invOpVal, vals] using hw)
      · cases hprov
  | bswap _ =>
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩; rcases hargs with _ | ⟨ha, _⟩
    dsimp only [Op.simpProv?] at hprov; split at hprov
    · next hok =>
      cases hf : a₁.finv with
      | none => simp [hf] at hprov
      | some iv =>
        simp only [hf] at hprov; split at hprov
        · next hk =>
          cases hprov
          exact simpProv_inv_sound hG .bswap hok ha hf hk
            (by simpa [OpCode.wp_bswap, hok, invOpVal, vals] using hw)
        · cases hprov
    · cases hprov
  | rbit _ =>
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩; rcases hargs with _ | ⟨ha, _⟩
    dsimp only [Op.simpProv?] at hprov
    cases hf : a₁.finv with
    | none => simp [hf] at hprov
    | some iv =>
      simp only [hf] at hprov; split at hprov
      · next hk =>
        cases hprov
        exact simpProv_inv_sound hG .rbit trivial ha hf hk
          (by simpa [OpCode.wp_rbit, invOpVal, vals] using hw)
      · cases hprov
  | trunc m n =>
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩; rcases hargs with _ | ⟨ha, _⟩
    dsimp only [Op.simpProv?] at hprov
    cases hf : a₁.fext with
    | none => simp [hf] at hprov
    | some e =>
      have hgood := ha.fext_good hG; rw [hf] at hgood
      have hgood' : BitsExtGood ρ b e a₂.val := hgood
      have hev := BitsExtGood.eval_eq hgood'
      rcases e with ⟨ek, em, hpos, hlt, esrc, eskey⟩
      simp only [hf] at hprov; split at hprov
      · rename_i hm; subst hm; cases hprov
        obtain ⟨_, hsk, hflt⟩ := hgood'
        have hv' : a₂.val.setWidth em = esrc.val := by
          rw [hev, ek.setWidth_eval_mid (Nat.le_refl _) (Nat.le_of_lt hlt)]
          cases ek <;> simp [ExtKind.eval_sext, ExtKind.eval_zext, BitVec.setWidth_eq]
        exact ⟨(a₂.val.setWidth em, ()), by simpa [OpCode.wp_trunc, vals] using hw.2,
          hG.cons ⟨hv'.symm, hv' ▸ hsk, hflt, ExtDefGood.none, trivial⟩⟩
      · cases hprov
  | _ => cases hprov

private theorem extTarget_good {G : Ctx (FVal Val) Val} {ρ : FEnv} {b : Nat} (hG : FGood ρ b G)
    (k : ExtKind) {m n : Nat} {a₁ : Arg (FVal Val) (.bits m)} {a₂ : Arg Val (.bits m)}
    (ha : ArgRel G (.bits m) a₁ a₂) {tg : BitsExt Val n} (htg : extTarget (n := n) k a₁ = some tg) :
    tg.kind = k ∧ tg.srcKey.fev ρ = tg.src.val ∧ tg.srcKey.FLt b ∧
    k.eval n tg.src.val = k.eval n a₂.val := by
  dsimp only [extTarget] at htg
  split at htg
  · next hm =>
    cases hf : a₁.fext with
    | none =>
      rw [hf] at htg; dsimp only at htg; split at htg <;> cases htg
      exact ⟨rfl, (ha.fkey_ev hG).trans (ha.fout_val hG).symm, ha.fkey_FLt hG,
        congrArg (k.eval n) (ha.fout_val hG)⟩
    | some e =>
      have hgood := ha.fext_good hG; rw [hf] at hgood
      have hgood' : BitsExtGood ρ b e a₂.val := hgood
      have hev := BitsExtGood.eval_eq hgood'
      rw [hf] at htg; dsimp only at htg; split at htg
      · next heq =>
        cases htg; have hk : e.kind = k := eq_of_beq heq
        obtain ⟨_, hsk, hflt⟩ := hgood'
        refine ⟨rfl, hsk, hflt, ?_⟩
        rw [hev, hk, k.eval_eval_le e.hpos (Nat.le_of_lt e.hlt) (Nat.le_of_lt hm)]
      · split at htg <;> cases htg
        exact ⟨rfl, (ha.fkey_ev hG).trans (ha.fout_val hG).symm, ha.fkey_FLt hG,
          congrArg (k.eval n) (ha.fout_val hG)⟩
  · cases htg

private theorem foldRewrite_ext_wp {G : Ctx (FVal Val) Val} {ρ : FEnv} {b : Nat} (hG : FGood ρ b G)
    (k : ExtKind) {m n : Nat} {a₁ : Arg (FVal Val) (.bits m)} {a₂ : Arg Val (.bits m)}
    (ha : ArgRel G (.bits m) a₁ a₂) {P : Tup Val [.bits n] → Prop}
    (hw : m ≤ n ∧ P (k.eval n a₂.val, ())) :
    let op₁ : Op (FVal Val) [.bits n] := ⟨k.toOpCode m n, (a₁, ())⟩
    op₁.foldRewrite.wp fun xs =>
      P xs ∧ FGood (fupdTup ρ b xs) (b + 1) (Tup.zip (op₁.foldWrap b xs) xs ++ G) := by
  cases k
  · cases htg : extTarget (n := n) .sext a₁ with
    | none =>
      dsimp only [ExtKind.toOpCode, Op.foldRewrite, Op.foldWrap]; rw [htg]
      exact Op.wp_mono (fun xs hxs => ⟨hxs, hG.freshFVals xs⟩) (by
        dsimp only [Op.wp, op1, vals]; simp only [OpCode.wp_sext, ha.fout_val hG]
        simpa [ExtKind.eval_sext] using hw)
    | some tg =>
      obtain ⟨hk, hsk, hflt, hev⟩ := extTarget_good hG .sext ha htg
      dsimp only [ExtKind.toOpCode, Op.foldRewrite, Op.foldWrap]; rw [htg]
      rcases tg with ⟨tk, tm, thpos, thlt, tsrc, tsk⟩; dsimp only at hk; subst hk
      dsimp only [Op.wp, op1, vals]; simp only [OpCode.wp_sext]
      simp only [ExtKind.eval_sext] at hev hw
      exact ⟨Nat.le_of_lt thlt, hev ▸ hw.2, by
        simpa [ExtKind.eval_sext, Tup.zip, List.cons_append, List.nil_append] using
          hG.cons_ext .sext thpos thlt hsk hflt⟩
  · cases htg : extTarget (n := n) .zext a₁ with
    | none =>
      dsimp only [ExtKind.toOpCode, Op.foldRewrite, Op.foldWrap]; rw [htg]
      exact Op.wp_mono (fun xs hxs => ⟨hxs, hG.freshFVals xs⟩) (by
        dsimp only [Op.wp, op1, vals]; simp only [OpCode.wp_zext, ha.fout_val hG]
        simpa [ExtKind.eval_zext] using hw)
    | some tg =>
      obtain ⟨hk, hsk, hflt, hev⟩ := extTarget_good hG .zext ha htg
      dsimp only [ExtKind.toOpCode, Op.foldRewrite, Op.foldWrap]; rw [htg]
      rcases tg with ⟨tk, tm, thpos, thlt, tsrc, tsk⟩; dsimp only at hk; subst hk
      dsimp only [Op.wp, op1, vals]; simp only [OpCode.wp_zext]
      simp only [ExtKind.eval_zext] at hev hw
      exact ⟨Nat.le_of_lt thlt, hev ▸ hw.2, by
        simpa [ExtKind.eval_zext, Tup.zip, List.cons_append, List.nil_append] using
          hG.cons_ext .zext thpos thlt hsk hflt⟩

private theorem foldRewrite_inv_wp {G : Ctx (FVal Val) Val} {ρ : FEnv} {b : Nat} (hG : FGood ρ b G)
    {t : Ty} (k : InvKind) (hok : invOpOk k t) {a₁ : Arg (FVal Val) t} {a₂ : Arg Val t}
    (ha : ArgRel G t a₁ a₂) {P : Tup Val [t] → Prop} (hw : P (invOpVal k t a₂.val, ())) :
    P (invOpVal k t a₁.fout.val, ()) ∧
    FGood (fupdTup ρ b (ts := [t]) (invOpVal k t a₁.fout.val, ())) (b + 1)
      (⟨t, ⟨.var (invOpVal k t a₁.fout.val), .var b, .none, some ⟨k, a₁.fout, a₁.fkey⟩⟩,
        invOpVal k t a₁.fout.val⟩ :: G) :=
  ⟨by rw [ha.fout_val hG]; exact hw,
    hG.cons_inv k hok rfl ((ha.fkey_ev hG).trans (ha.fout_val hG).symm) (ha.fkey_FLt hG)⟩

theorem OpRel.foldRewrite_wp {G : Ctx (FVal Val) Val} {ρ : (t : Ty) → Nat → Val t} {b : Nat}
    (hG : FGood ρ b G) {sig ts : List Ty} {code : OpCode sig ts}
    {args₁ : Tup (Arg (FVal Val)) sig} {args₂ : Tup (Arg Val) sig}
    (hargs : TRel (ArgRel G) args₁ args₂) {P : Tup Val ts → Prop} (hw : code.wp (vals args₂) P) :
    let op₁ : Op (FVal Val) ts := ⟨code, args₁⟩
    op₁.foldRewrite.wp fun xs =>
      P xs ∧ FGood (fupdTup ρ b xs) (b + ts.length) (Tup.zip (op₁.foldWrap b xs) xs ++ G) := by
  have hdef : ∀ (op' : Op Val ts), op'.wp P →
      op'.wp fun xs =>
        P xs ∧ FGood (fupdTup ρ b xs) (b + ts.length) (Tup.zip (freshFVals ts xs b) xs ++ G) :=
    fun _ hwp => Op.wp_mono (fun xs hxs => ⟨hxs, hG.freshFVals xs⟩) hwp
  cases code with
  | cmp o t _ h =>
    subst h; rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩; refine hdef _ ?_
    cases t with
    | bits n =>
      obtain ⟨hev, _, _, _⟩ := narrowCmp_sound hG o ha hb; dsimp only [Op.foldRewrite]
      cases himm : (narrowCmp o n a₁ b₁).rhs.imm? with
      | some c =>
        simp only [Op.wp, op2, OpCode.wp_cmp, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte,
          liftCmp, vals, Arg.val_imm, cast_eq, normBitsCmpImm_eval] at hw ⊢
        rw [← imm?_eq_some_val himm, hev]; exact hw
      | none =>
        simp only [Op.wp, op2, OpCode.wp_cmp, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte,
          liftCmp, vals, cast_eq] at hw ⊢
        rw [hev]; exact hw
    | float _ => simp [OpCode.wp_cmp, Ty.hasFloat] at hw
    | bool | pair _ _ =>
      dsimp only [Op.foldRewrite]; split
      · simpa only [Op.wp, op2, OpCode.wp_cmp, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte,
          vals, cast_eq, ha.fout_val hG, hb.fout_val hG, liftCmp_swap] using hw
      · simpa only [Op.wp, op2, vals, ha.fout_val hG, hb.fout_val hG] using hw
  | select t =>
    cases t with
    | bool =>
      rcases args₁ with ⟨c₁, a₁, b₁, ⟨⟩⟩; rcases args₂ with ⟨c₂, a₂, b₂, ⟨⟩⟩
      rcases hargs with _ | ⟨hc, _ | ⟨ha, _ | ⟨hb, _⟩⟩⟩; dsimp only [Op.foldRewrite, Op.foldWrap]
      split
      · next hft =>
        simp only [Bool.and_eq_true, beq_iff_eq] at hft
        simp only [Op.wp, op1, OpCode.wp_not, OpCode.wp_select, vals,
          ha.fout_imm?_val hG hft.1, hb.fout_imm?_val hG hft.2] at hw ⊢
        have hnot : (if c₂.val then false else true) = invOpVal .not_ .bool c₂.val := by
          cases c₂.val <;> rfl
        exact foldRewrite_inv_wp hG .not_ trivial hc (hnot ▸ hw)
      · split
        · next htr =>
          have hav := ha.fout_imm?_val hG (eq_of_beq htr); refine hdef _ ?_
          cases hcv : c₂.val <;> simp [Op.wp, op2, OpCode.wp_or, OpCode.wp_select, vals,
            hc.fout_val hG, hav, hb.fout_val hG, lift2, hcv] at hw ⊢ <;> exact hw
        · split
          · next hfl =>
            have hbv := hb.fout_imm?_val hG (eq_of_beq hfl); refine hdef _ ?_
            cases hcv : c₂.val <;> simp [Op.wp, op2, OpCode.wp_and, OpCode.wp_select, vals,
              hc.fout_val hG, ha.fout_val hG, hbv, lift2, hcv] at hw ⊢ <;> exact hw
          · refine hdef _ ?_
            simpa [Op.wp, op3, OpCode.wp_select, vals, hc.fout_val hG, ha.fout_val hG,
              hb.fout_val hG] using hw
    | bits n =>
      rcases args₁ with ⟨c₁, a₁, b₁, ⟨⟩⟩; rcases args₂ with ⟨c₂, a₂, b₂, ⟨⟩⟩
      rcases hargs with _ | ⟨hc, _ | ⟨ha, _ | ⟨hb, _⟩⟩⟩
      dsimp only [Op.foldRewrite, Op.foldWrap]; split
      · next h10 =>
        simp only [Bool.and_eq_true, beq_iff_eq] at h10; refine hdef _ ?_
        cases hcv : c₂.val <;> simp [Op.wp, op1, OpCode.wp_ofBool, OpCode.wp_select, vals,
          hc.fout_val hG, ha.fout_imm?_val hG h10.1.2, hb.fout_imm?_val hG h10.2, hcv] at hw ⊢ <;>
          exact hw
      · refine hdef _ ?_
        simpa [Op.wp, op3, OpCode.wp_select, vals, hc.fout_val hG, ha.fout_val hG,
          hb.fout_val hG] using hw
    | _ => exact hdef _ (Op.rewrite_wp _ _ ((OpRel.mk _ hargs).fout_wp hG hw))
  | sext m n =>
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩; rcases hargs with _ | ⟨ha, _⟩
    exact foldRewrite_ext_wp hG .sext ha
      (by simpa [OpCode.wp_sext, ExtKind.eval_sext, vals] using hw)
  | zext m n =>
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩; rcases hargs with _ | ⟨ha, _⟩
    exact foldRewrite_ext_wp hG .zext ha
      (by simpa [OpCode.wp_zext, ExtKind.eval_zext, vals] using hw)
  | trunc m n =>
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩; rcases hargs with _ | ⟨ha, _⟩
    dsimp only [Op.foldRewrite, Op.foldWrap]
    cases htg : truncTarget? m n a₁ with
    | none => exact hdef _ (Op.rewrite_wp _ _ ((OpRel.mk _ (.cons ha .nil)).fout_wp hG hw))
    | some _ =>
      dsimp only [truncTarget?] at htg; split at htg
      · next hnm =>
        cases hf : a₁.fext with
        | none => simp [hf] at htg
        | some e =>
          have hgood := ha.fext_good hG; rw [hf] at hgood
          have hgood' : BitsExtGood ρ b e a₂.val := hgood
          have hev := BitsExtGood.eval_eq hgood'
          obtain ⟨_, hsk, hflt⟩ := hgood'; rw [hf] at htg; dsimp only at htg
          split at htg
          · next hle =>
            cases htg; dsimp only [Op.wp, op1, OpCode.wp_trunc, vals] at hw ⊢
            have hsw : e.src.val.setWidth n = a₂.val.setWidth n := by
              rw [hev]; exact (e.kind.setWidth_eval_narrow hle (Nat.le_of_lt e.hlt) e.src.val).symm
            exact ⟨hle, hsw ▸ hw.2, hG.freshFVals _⟩
          · next hnle =>
            cases htg; have hlt : e.m < n := Nat.lt_of_not_ge hnle
            have hsw : e.kind.eval n e.src.val = a₂.val.setWidth n := by
              rw [hev]
              exact (e.kind.setWidth_eval_mid (Nat.le_of_lt hlt) (Nat.le_of_lt hnm) e.src.val).symm
            rcases e with ⟨ek, em, hpos, hlt0, esrc, eskey⟩
            cases ek <;> dsimp only [ExtKind.toOpCode, Op.wp, op1, vals] <;>
              simp only [OpCode.wp_trunc, OpCode.wp_sext, OpCode.wp_zext] at hw ⊢
            · simp only [ExtKind.eval_sext] at hsw
              exact ⟨Nat.le_of_lt hlt, hsw ▸ hw.2, by
                simpa [ExtKind.eval_sext, Tup.zip, List.cons_append, List.nil_append] using
                  hG.cons_ext .sext hpos hlt hsk hflt⟩
            · simp only [ExtKind.eval_zext] at hsw
              exact ⟨Nat.le_of_lt hlt, hsw ▸ hw.2, by
                simpa [ExtKind.eval_zext, Tup.zip, List.cons_append, List.nil_append] using
                  hG.cons_ext .zext hpos hlt hsk hflt⟩
      · cases htg
  | not _ =>
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩; rcases hargs with _ | ⟨ha, _⟩
    dsimp only [Op.foldRewrite, Op.rewrite, Op.foldWrap, Op.wp, tupMapArg, vals]
    exact foldRewrite_inv_wp hG .not_ trivial ha (by simpa [OpCode.wp_not, invOpVal, vals] using hw)
  | bswap t =>
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩; rcases hargs with _ | ⟨ha, _⟩
    dsimp only [Op.foldRewrite, Op.rewrite, Op.foldWrap, Op.wp, tupMapArg, vals]
    simp only [OpCode.wp_bswap] at hw ⊢
    split at hw; · cases hw
    · next hnok =>
      have hok : t.bswapOk = true := by cases h : t.bswapOk <;> simp_all
      simp only [hok, ↓reduceIte, Bool.not_true, Bool.false_eq_true]
      exact foldRewrite_inv_wp hG .bswap hok ha (by simpa [invOpVal, vals] using hw)
  | rbit _ =>
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩; rcases hargs with _ | ⟨ha, _⟩
    dsimp only [Op.foldRewrite, Op.rewrite, Op.foldWrap, Op.wp, tupMapArg, vals]
    exact foldRewrite_inv_wp hG .rbit trivial ha
      (by simpa [OpCode.wp_rbit, invOpVal, vals] using hw)
  | _ => all_goals exact hdef _ (Op.rewrite_wp _ _ ((OpRel.mk _ hargs).fout_wp hG hw))

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
  | .bits _, some e₁, some e₂ => BitsExtRel G' e₁ e₂
  | .bits _, none, none => True
  | .bits _, _, _ => False
  | .bool, _, _ | .float _, _, _ | .pair _ _, _, _ => True

/-- Relational invariant for unary-involution provenance `UnInv`. -/
inductive UnInvRel (G' : Ctx V₁ V₂) {t : Ty} : UnInv V₁ t → UnInv V₂ t → Prop
  | mk (kind : InvKind) {s₁ : Arg V₁ t} {s₂ : Arg V₂ t} {sk : FKey t}
      (hs : ArgRel G' t s₁ s₂) : UnInvRel G' ⟨kind, s₁, sk⟩ ⟨kind, s₂, sk⟩

/-- Relational invariant for optional unary-involution provenance `Option (UnInv V t)`. -/
def UnInvOptRel (G' : Ctx V₁ V₂) {t : Ty} : Option (UnInv V₁ t) → Option (UnInv V₂ t) → Prop
  | some iv₁, some iv₂ => UnInvRel G' iv₁ iv₂
  | none, none => True
  | _, _ => False

theorem ExtDefRel.none {G' : Ctx V₁ V₂} {t : Ty} :
    ExtDefRel G' (ExtDef.none (t := t)) (ExtDef.none (t := t)) := by cases t <;> trivial

theorem ExtDefRel.weaken {G₁ G₂ : Ctx V₁ V₂} (hsub : ∀ p ∈ G₁, p ∈ G₂)
    {t : Ty} {e₁ : ExtDef V₁ t} {e₂ : ExtDef V₂ t} (h : ExtDefRel G₁ e₁ e₂) :
    ExtDefRel G₂ e₁ e₂ := by
  cases t with
  | bits _ =>
    cases e₁ <;> cases e₂
    · trivial
    · exact False.elim h
    · exact False.elim h
    · cases h with | mk k hpos hlt hs => exact .mk k hpos hlt (ArgRel.weaken hsub hs)
  | bool | float _ | pair _ _ => trivial

theorem UnInvRel.weaken {G₁ G₂ : Ctx V₁ V₂} (hsub : ∀ p ∈ G₁, p ∈ G₂)
    {t : Ty} {iv₁ : UnInv V₁ t} {iv₂ : UnInv V₂ t} : UnInvRel G₁ iv₁ iv₂ → UnInvRel G₂ iv₁ iv₂
  | .mk k hs => .mk k (ArgRel.weaken hsub hs)

theorem UnInvOptRel.weaken {G₁ G₂ : Ctx V₁ V₂} (hsub : ∀ p ∈ G₁, p ∈ G₂)
    {t : Ty} {iv₁ : Option (UnInv V₁ t)} {iv₂ : Option (UnInv V₂ t)} :
    UnInvOptRel G₁ iv₁ iv₂ → UnInvOptRel G₂ iv₁ iv₂ := by
  cases iv₁ <;> cases iv₂ <;> intro h <;> first | exact h | exact UnInvRel.weaken hsub h

/-- Value relation for `FVal` entries in `FRelG`. -/
def FValRel (G' : Ctx V₁ V₂) {t : Ty} (w₁ : FVal V₁ t) (w₂ : FVal V₂ t) : Prop :=
  ArgRel G' t w₁.out w₂.out ∧ w₁.key = w₂.key ∧
  ExtDefRel G' w₁.ext w₂.ext ∧ UnInvOptRel G' w₁.inv w₂.inv

theorem FValRel.weaken {G₁ G₂ : Ctx V₁ V₂} (hsub : ∀ p ∈ G₁, p ∈ G₂)
    {t : Ty} {w₁ : FVal V₁ t} {w₂ : FVal V₂ t} (h : FValRel G₁ w₁ w₂) : FValRel G₂ w₁ w₂ :=
  ⟨ArgRel.weaken hsub h.1, h.2.1, h.2.2.1.weaken hsub, h.2.2.2.weaken hsub⟩

/-- Two `FVal` contexts are related when output operands, keys, and provenances match. -/
def FRelG (G' : Ctx V₁ V₂) (G : Ctx (FVal V₁) (FVal V₂)) : Prop :=
  ∀ p ∈ G, FValRel G' p.2.1 p.2.2

private def fRelKit : RelKit FVal where
  out w := w.out
  fresh v b := FVal.fresh v b
  rel G' _ w₁ w₂ := FValRel G' w₁ w₂
  rel_weaken hsub _ _ _ h := h.weaken hsub
  rel_out h := h.1
  rel_fresh _ hmem := ⟨.var hmem, rfl, ExtDefRel.none, trivial⟩

theorem FRelG.cons {G' : Ctx V₁ V₂} {G : Ctx (FVal V₁) (FVal V₂)} (hG : FRelG G' G)
    {t : Ty} {w₁ : FVal V₁ t} {w₂ : FVal V₂ t} (hw : FValRel G' w₁ w₂) :
    FRelG G' (⟨t, w₁, w₂⟩ :: G) := fRelKit.relG_cons hw hG

theorem FRelG.append {G' : Ctx V₁ V₂} {G : Ctx (FVal V₁) (FVal V₂)} (hG : FRelG G' G)
    {H : Ctx (FVal V₁) (FVal V₂)} (hH : FRelG G' H) : FRelG G' (H ++ G) :=
  fRelKit.relG_append hH hG

theorem FRelG.weaken {G' : Ctx V₁ V₂} {G : Ctx (FVal V₁) (FVal V₂)} (hG : FRelG G' G)
    {G'' : Ctx V₁ V₂} (hsub : ∀ p ∈ G', p ∈ G'') : FRelG G'' G :=
  fRelKit.relG_weaken hsub hG

theorem FRelG.freshFVals {G' : Ctx V₁ V₂} {G : Ctx (FVal V₁) (FVal V₂)} (hG : FRelG G' G)
    {ts : List Ty} (xs₁ : Tup V₁ ts) (xs₂ : Tup V₂ ts) (b : Nat) :
    FRelG (Tup.zip xs₁ xs₂ ++ G')
      (Tup.zip (freshFVals ts xs₁ b) (freshFVals ts xs₂ b) ++ G) := by
  intro p hp
  exact fRelKit.relG_freshTup (ts := ts) xs₁ xs₂ b hG p (by simpa [freshFVals, fRelKit] using hp)

theorem FRelG.freshOne {G' : Ctx V₁ V₂} {G : Ctx (FVal V₁) (FVal V₂)} (hG : FRelG G' G)
    {t : Ty} (v₁ : V₁ t) (v₂ : V₂ t) (b : Nat) :
    FRelG (⟨t, v₁, v₂⟩ :: G') (⟨t, FVal.fresh v₁ b, FVal.fresh v₂ b⟩ :: G) :=
  fRelKit.relG_freshOne v₁ v₂ b hG

private theorem FRelG.cons_ext {G' : Ctx V₁ V₂} {G : Ctx (FVal V₁) (FVal V₂)} (hG : FRelG G' G)
    {n : Nat} {r₁ : V₁ (.bits n)} {r₂ : V₂ (.bits n)} {b : Nat}
    {e₁ : BitsExt V₁ n} {e₂ : BitsExt V₂ n} (he : BitsExtRel G' e₁ e₂) :
    FRelG (Tup.zip (as := [.bits n]) (r₁, ()) (r₂, ()) ++ G')
      (⟨.bits n, ⟨.var r₁, .var b, some e₁, none⟩,
                 ⟨.var r₂, .var b, some e₂, none⟩⟩ :: G) :=
  (hG.weaken (fun _ hp => List.mem_cons_of_mem _ hp)).cons
    ⟨.var List.mem_cons_self, rfl,
      ExtDefRel.weaken (fun _ hp => List.mem_cons_of_mem _ hp) he, trivial⟩

private theorem FRelG.cons_inv {G' : Ctx V₁ V₂} {G : Ctx (FVal V₁) (FVal V₂)} (hG : FRelG G' G)
    {t : Ty} {r₁ : V₁ t} {r₂ : V₂ t} {b : Nat} (k : InvKind)
    {s₁ : Arg V₁ t} {s₂ : Arg V₂ t} (hs : ArgRel G' t s₁ s₂) {sk : FKey t} :
    FRelG (Tup.zip (as := [t]) (r₁, ()) (r₂, ()) ++ G')
      (⟨t, ⟨.var r₁, .var b, .none, some ⟨k, s₁, sk⟩⟩,
           ⟨.var r₂, .var b, .none, some ⟨k, s₂, sk⟩⟩⟩ :: G) :=
  (hG.weaken (fun _ hp => List.mem_cons_of_mem _ hp)).cons
    ⟨.var List.mem_cons_self, rfl, ExtDefRel.none,
      .mk k (ArgRel.weaken (fun _ hp => List.mem_cons_of_mem _ hp) hs)⟩

variable {G' : Ctx V₁ V₂} {G : Ctx (FVal V₁) (FVal V₂)}

theorem ArgRel.imm?_eq {t : Ty} {a₁ : Arg V₁ t} {a₂ : Arg V₂ t} :
    ArgRel G' t a₁ a₂ → a₁.imm? = a₂.imm? := argRel_imm?_eq

theorem ArgRel.isZero_eq {t : Ty} {a₁ : Arg V₁ t} {a₂ : Arg V₂ t} (h : ArgRel G' t a₁ a₂) :
    isZeroArg? a₁ = isZeroArg? a₂ := by simp only [isZeroArg?, h.imm?_eq]

theorem ArgRel.isOnes_eq {t : Ty} {a₁ : Arg V₁ t} {a₂ : Arg V₂ t} (h : ArgRel G' t a₁ a₂) :
    isOnesArg? a₁ = isOnesArg? a₂ := by simp only [isOnesArg?, h.imm?_eq]

theorem ArgRel.isOne_eq {t : Ty} {a₁ : Arg V₁ t} {a₂ : Arg V₂ t} (h : ArgRel G' t a₁ a₂) :
    isOneArg? a₁ = isOneArg? a₂ := by simp only [isOneArg?, h.imm?_eq]

theorem ArgRel.fout (hG : FRelG G' G) {t : Ty} {a₁ : Arg (FVal V₁) t} {a₂ : Arg (FVal V₂) t} :
    ArgRel G t a₁ a₂ → ArgRel G' t a₁.fout a₂.fout
  | .var h => (hG _ h).1 | .imm _ => .imm _

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
      {lk rk : FKey (.bits w)} (hl : ArgRel G' (.bits w) l₁ l₂)
      (hr : ArgRel G' (.bits w) r₁ r₂) :
      NarrowCmpRel G' ⟨w, o, l₁, r₁, lk, rk⟩ ⟨w, o, l₂, r₂, lk, rk⟩

private theorem narrowCmpCore_rel (hG : FRelG G' G) {n : Nat} (o : CmpOp)
    {a₁ b₁ : Arg (FVal V₁) (.bits n)} {a₂ b₂ : Arg (FVal V₂) (.bits n)}
    (ha : ArgRel G (.bits n) a₁ a₂) (hb : ArgRel G (.bits n) b₁ b₂) :
    NarrowCmpRel G' (narrowCmpCore o n a₁ b₁) (narrowCmpCore o n a₂ b₂) := by
  have hbase : NarrowCmpRel G' ⟨n, o, a₁.fout, b₁.fout, a₁.fkey, b₁.fkey⟩
      ⟨n, o, a₂.fout, b₂.fout, a₂.fkey, b₂.fkey⟩ := by
    rw [ha.fkey_eq hG, hb.fkey_eq hG]; exact .mk (ha.fout hG) (hb.fout hG)
  have hfeA := ha.fext_rel hG; have hfeB := hb.fext_rel hG
  dsimp only [narrowCmpCore]; rw [(hb.fout hG).imm?_eq]
  cases ha₁ : a₁.fext <;> cases ha₂ : a₂.fext <;> rw [ha₁, ha₂] at hfeA
  · exact hbase
  · exact False.elim hfeA
  · exact False.elim hfeA
  · cases hfeA with
    | @mk ka m₁ hposa hlta _ _ _ hsa =>
      cases b₂.fout.imm? with
      | some c =>
        dsimp only; cases ka
        · by_cases hfit : ((c.setWidth m₁).signExtend n == c) = true
          · simp only [hfit, ↓reduceIte]; exact .mk hsa (.imm _)
          · simp only [hfit, Bool.false_eq_true, ↓reduceIte]; exact hbase
        · by_cases hfit : ((c.setWidth m₁).setWidth n == c) = true
          · simp only [hfit, ↓reduceIte]; exact .mk hsa (.imm _)
          · simp only [hfit, Bool.false_eq_true, ↓reduceIte]; exact hbase
      | none =>
        dsimp only
        cases hb₁ : b₁.fext <;> cases hb₂ : b₂.fext <;> rw [hb₁, hb₂] at hfeB
        · exact hbase
        · exact False.elim hfeB
        · exact False.elim hfeB
        · cases hfeB with
          | @mk kb m₂ hposb hltb _ _ _ hsb =>
            dsimp only; cases ka <;> cases kb <;> dsimp only
            · by_cases hm : m₁ = m₂
              · simp only [hm, ↓reduceDIte]; subst hm; exact .mk hsa hsb
              · simp only [hm, ↓reduceDIte]; exact hbase
            · exact hbase
            · exact hbase
            · by_cases hm : m₁ = m₂
              · simp only [hm, ↓reduceDIte]; subst hm; exact .mk hsa hsb
              · simp only [hm, ↓reduceDIte]; exact hbase

theorem narrowCmp_rel (hG : FRelG G' G) {n : Nat} (o : CmpOp)
    {a₁ b₁ : Arg (FVal V₁) (.bits n)} {a₂ b₂ : Arg (FVal V₂) (.bits n)}
    (ha : ArgRel G (.bits n) a₁ a₂) (hb : ArgRel G (.bits n) b₁ b₂) :
    NarrowCmpRel G' (narrowCmp o n a₁ b₁) (narrowCmp o n a₂ b₂) := by
  dsimp only [narrowCmp]; rw [(ha.fout hG).imm?_eq, (hb.fout hG).imm?_eq]
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
  delta Op.simpAct; dsimp only
  rw [TRel.imm?_eq (TRel.fout hG hargs)]
  cases (tupImms? (tupMapArg (fun _ => Arg.fout) args₂)).bind code.eval? with
  | some _ => rfl
  | none =>
    dsimp only
    cases code with
    | copy _ => rfl
    | neg t => cases t <;> rfl
    | add _ | sub _ | mul _ | and _ | or _ | xor _ | shl _ | lshr _ | ashr _ | rotl _ | rotr _
    | udiv _ | sdiv _ | urem _ | srem _ | udiv0 _ | sdiv0 _ | umulw _ | smulw _ =>
      rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩
      have ha' := ha.fout hG; have hb' := hb.fout hG
      simp only [ha'.isZero_eq, hb'.isZero_eq, ha'.isOnes_eq, hb'.isOnes_eq,
        ha'.isOne_eq, hb'.isOne_eq, hb'.imm?_eq, ha.fkey_eq hG, hb.fkey_eq hG]
    | cmp o t _ h =>
      subst h; rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, ⟨⟩⟩
      rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩
      cases t with
      | bits n =>
        dsimp only; have hnc := narrowCmp_rel hG o ha hb
        generalize narrowCmp o n a₁ b₁ = nc₁ at hnc ⊢
        generalize narrowCmp o n a₂ b₂ = nc₂ at hnc ⊢
        cases hnc with | mk _ hr => simp only [hr.imm?_eq]
      | _ => simp only [ha.fkey_eq hG, hb.fkey_eq hG]
    | select t =>
      rcases hargs with _ | ⟨ha, _ | ⟨hb, _ | ⟨hc, _⟩⟩⟩
      have ha' := ha.fout hG; have hb' := hb.fout hG; have hc' := hc.fout hG
      cases t <;> simp only [ha'.imm?_eq, hb'.imm?_eq, hc'.imm?_eq, hb.fkey_eq hG, hc.fkey_eq hG]
    | blend _ _ _ | addc _ | subb _ =>
      rcases hargs with _ | ⟨ha, _ | ⟨hb, _ | ⟨hc, _⟩⟩⟩
      have ha' := ha.fout hG; have hb' := hb.fout hG; have hc' := hc.fout hG
      simp only [ha'.isZero_eq, hb'.isZero_eq, ha'.imm?_eq, hc'.imm?_eq,
        ha.fkey_eq hG, hb.fkey_eq hG, hc.fkey_eq hG]
    | _ => rfl

private theorem ArgRel.fpair_rel (hG : FRelG G' G) {t : Ty}
    {a₁ : Arg (FVal V₁) t} {a₂ : Arg (FVal V₂) t} :
    ArgRel G t a₁ a₂ → FValRel G' a₁.fpair a₂.fpair
  | .var hmem => hG _ hmem | .imm c => ⟨.imm c, rfl, ExtDefRel.none, trivial⟩

private theorem applySimpActRhs_fpair {sig : List Ty} (as₂ : Tup (Arg (FVal V₂)) sig) :
    {rs : List Ty} → (act : SimpAct sig rs) →
    applySimpActRhs fimm (fun i => (as₂.get i).fpair) act = act.apply as₂
  | [], () => rfl
  | _ :: _, (.imm _, act) => congrArg (_, ·) (applySimpActRhs_fpair as₂ act)
  | _ :: _, (.arg _, act) => congrArg (_, ·) (applySimpActRhs_fpair as₂ act)

theorem FRelG.apply_simpAct (hG : FRelG G' G) :
    {sig rs : List Ty} → {as₁ : Tup (Arg (FVal V₁)) sig} → {as₂ : Tup (Arg (FVal V₂)) sig} →
    TRel (ArgRel G) as₁ as₂ → (act : SimpAct sig rs) →
    FRelG G' (Tup.zip (act.apply as₁) (act.apply as₂) ++ G) := by
  intro sig rs as₁ as₂ has act; rw [← applySimpActRhs_fpair as₂ act]
  exact CtxPred.apply_simpAct hG fimm (fun i => (as₂.get i).fpair)
    (fun c => ⟨.imm c, rfl, ExtDefRel.none, trivial⟩)
    (fun i => (TRel.get i has).fpair_rel hG) act

private theorem OpRel.rewrite_mul_a {t : Ty} {a₁ b₁ : Arg V₁ t} {a₂ b₂ : Arg V₂ t}
    (ha : ArgRel G' t a₁ a₂) (hb : ArgRel G' t b₁ b₂) :
    OpRel G'
      (match a₁.imm?.bind (leafPow2Shift? t) with
        | some s => op2 (.shl t) b₁ (.imm s) | none => op2 (.mul t) a₁ b₁)
      (match a₂.imm?.bind (leafPow2Shift? t) with
        | some s => op2 (.shl t) b₂ (.imm s) | none => op2 (.mul t) a₂ b₂) := by
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
      rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩; dsimp only [Op.rewrite]; split
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
        | some _ => exact .mk _ (.cons ha (.cons (.imm _) .nil))
        | none => exact .mk _ (.cons ha (.cons (.imm cb) .nil))
    | _ => exact .mk _ hargs

private theorem extTarget_rel (hG : FRelG G' G) (k : ExtKind) {m n : Nat}
    {a₁ : Arg (FVal V₁) (.bits m)} {a₂ : Arg (FVal V₂) (.bits m)}
    (ha : ArgRel G (.bits m) a₁ a₂) :
    ExtDefRel G' (t := .bits n) (extTarget (n := n) k a₁) (extTarget (n := n) k a₂) := by
  have hfe := ha.fext_rel hG
  dsimp only [extTarget]; split
  · next hm =>
    cases h₁ : a₁.fext <;> cases h₂ : a₂.fext <;> rw [h₁, h₂] at hfe
    · dsimp only; split; · rw [ha.fkey_eq hG]; exact .mk k _ hm (ha.fout hG)
      · trivial
    · exact False.elim hfe
    · exact False.elim hfe
    · cases hfe with | mk ek hpos hlt hs =>
      dsimp only; split; · exact .mk k hpos (Nat.lt_trans hlt hm) hs
      · split; · rw [ha.fkey_eq hG]; exact .mk k _ hm (ha.fout hG)
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
  have hfe := ha.fext_rel hG
  dsimp only [truncTarget?]; split
  · cases h₁ : a₁.fext <;> cases h₂ : a₂.fext <;> rw [h₁, h₂] at hfe
    · exact .none
    · exact False.elim hfe
    · exact False.elim hfe
    · cases hfe with | mk ek hpos _ hs =>
      dsimp only; split; exact .narrow _ _ hs; exact .lift (.mk ek hpos _ hs)
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
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩; rcases hargs with _ | ⟨ha, _⟩
    have hfi := ha.finv_rel hG; dsimp only [Op.simpProv?]
    cases h₁ : a₁.finv <;> cases h₂ : a₂.finv <;> rw [h₁, h₂] at hfi
    · trivial
    · exact False.elim hfi
    · exact False.elim hfi
    · cases hfi with | mk kind hs =>
      dsimp only; by_cases hk : (kind == .not_) = true
      · simp only [hk, ↓reduceIte]; exact hG.cons ⟨hs, rfl, ExtDefRel.none, trivial⟩
      · simp only [hk, Bool.false_eq_true, ↓reduceIte]
  | bswap t =>
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩; rcases hargs with _ | ⟨ha, _⟩
    have hfi := ha.finv_rel hG; dsimp only [Op.simpProv?]
    by_cases hok : t.bswapOk = true
    · simp only [hok, ↓reduceIte]
      cases h₁ : a₁.finv <;> cases h₂ : a₂.finv <;> rw [h₁, h₂] at hfi
      · trivial
      · exact False.elim hfi
      · exact False.elim hfi
      · cases hfi with | mk kind hs =>
        dsimp only; by_cases hk : (kind == .bswap) = true
        · simp only [hk, ↓reduceIte]; exact hG.cons ⟨hs, rfl, ExtDefRel.none, trivial⟩
        · simp only [hk, Bool.false_eq_true, ↓reduceIte]
    · simp only [hok, Bool.false_eq_true, ↓reduceIte]
  | rbit _ =>
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩; rcases hargs with _ | ⟨ha, _⟩
    have hfi := ha.finv_rel hG; dsimp only [Op.simpProv?]
    cases h₁ : a₁.finv <;> cases h₂ : a₂.finv <;> rw [h₁, h₂] at hfi
    · trivial
    · exact False.elim hfi
    · exact False.elim hfi
    · cases hfi with | mk kind hs =>
      dsimp only; by_cases hk : (kind == .rbit) = true
      · simp only [hk, ↓reduceIte]; exact hG.cons ⟨hs, rfl, ExtDefRel.none, trivial⟩
      · simp only [hk, Bool.false_eq_true, ↓reduceIte]
  | trunc _ n =>
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩; rcases hargs with _ | ⟨ha, _⟩
    have hfe := ha.fext_rel hG; dsimp only [Op.simpProv?]
    cases h₁ : a₁.fext <;> cases h₂ : a₂.fext <;> rw [h₁, h₂] at hfe
    · trivial
    · exact False.elim hfe
    · exact False.elim hfe
    · cases hfe with | @mk _ m' _ _ _ _ _ hs =>
      dsimp only
      by_cases hm : m' = n
      · subst hm; simp only [↓reduceDIte]; exact hG.cons ⟨hs, rfl, ExtDefRel.none, trivial⟩
      · simp only [hm, ↓reduceDIte]
  | _ => all_goals trivial

private theorem foldRewrite_ext_rel (hG : FRelG G' G) (k : ExtKind) {m n : Nat}
    {a₁ : Arg (FVal V₁) (.bits m)} {a₂ : Arg (FVal V₂) (.bits m)}
    (ha : ArgRel G (.bits m) a₁ a₂) :
    OpRel G'
      (({ code := k.toOpCode m n, args := (a₁, ()) } : Op (FVal V₁) [.bits n]).foldRewrite)
      (({ code := k.toOpCode m n, args := (a₂, ()) } : Op (FVal V₂) [.bits n]).foldRewrite) := by
  have htg := extTarget_rel hG k (n := n) ha
  cases k <;> (
    dsimp only [ExtKind.toOpCode, Op.foldRewrite]
    cases h₁ : extTarget (n := n) _ a₁ <;> cases h₂ : extTarget (n := n) _ a₂ <;>
      rw [h₁, h₂] at htg
    · exact .mk _ (.cons (ha.fout hG) .nil)
    · exact False.elim htg
    · exact False.elim htg
    · cases htg with | mk _ _ _ hs => exact .mk _ (.cons hs .nil))

theorem OpRel.foldRewrite_rel (hG : FRelG G' G) {sig rs : List Ty} {code : OpCode sig rs}
    {args₁ : Tup (Arg (FVal V₁)) sig} {args₂ : Tup (Arg (FVal V₂)) sig}
    (hargs : TRel (ArgRel G) args₁ args₂) :
    OpRel G'
      (({ code := code, args := args₁ } : Op (FVal V₁) rs).foldRewrite)
      (({ code := code, args := args₂ } : Op (FVal V₂) rs).foldRewrite) := by
  cases code with
  | cmp o t m h =>
    subst h; rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩
    cases t with
    | bits n =>
      have hnc := narrowCmp_rel hG o ha hb; dsimp only [Op.foldRewrite]
      generalize narrowCmp o n a₁ b₁ = nc₁ at hnc ⊢
      generalize narrowCmp o n a₂ b₂ = nc₂ at hnc ⊢
      cases hnc with | mk hl hr => cases hr with
        | var hm => exact .mk _ (.cons hl (.cons (.var hm) .nil))
        | imm _ => exact .mk _ (.cons hl (.cons (.imm _) .nil))
    | _ =>
      have ha' := ha.fout hG; have hb' := hb.fout hG
      dsimp only [Op.foldRewrite]; rw [ha'.imm?_eq, hb'.imm?_eq]; split
      · exact .mk _ (.cons hb' (.cons ha' .nil))
      · exact .mk _ (.cons ha' (.cons hb' .nil))
  | select t =>
    cases t with
    | bool =>
      rcases args₁ with ⟨c₁, a₁, b₁, ⟨⟩⟩; rcases args₂ with ⟨c₂, a₂, b₂, ⟨⟩⟩
      rcases hargs with _ | ⟨hc, _ | ⟨ha, _ | ⟨hb, _⟩⟩⟩
      have hc' := hc.fout hG; have ha' := ha.fout hG; have hb' := hb.fout hG
      dsimp only [Op.foldRewrite]; rw [ha'.imm?_eq, hb'.imm?_eq]; split
      · exact .mk _ (.cons hc' .nil)
      · split
        · exact .mk _ (.cons hc' (.cons hb' .nil))
        · split
          · exact .mk _ (.cons hc' (.cons ha' .nil))
          · exact .mk _ (.cons hc' (.cons ha' (.cons hb' .nil)))
    | bits n =>
      rcases args₁ with ⟨c₁, a₁, b₁, ⟨⟩⟩; rcases args₂ with ⟨c₂, a₂, b₂, ⟨⟩⟩
      rcases hargs with _ | ⟨hc, _ | ⟨ha, _ | ⟨hb, _⟩⟩⟩
      have hc' := hc.fout hG; have ha' := ha.fout hG; have hb' := hb.fout hG
      dsimp only [Op.foldRewrite]; rw [ha'.imm?_eq, hb'.imm?_eq]; split
      · exact .mk _ (.cons hc' .nil)
      · exact .mk _ (.cons hc' (.cons ha' (.cons hb' .nil)))
    | _ => dsimp only [Op.foldRewrite]; exact OpRel.rewrite (.mk _ (TRel.fout hG hargs))
  | sext m n =>
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩; rcases hargs with _ | ⟨ha, _⟩
    exact foldRewrite_ext_rel hG .sext ha
  | zext m n =>
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩; rcases hargs with _ | ⟨ha, _⟩
    exact foldRewrite_ext_rel hG .zext ha
  | trunc m n =>
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩; rcases hargs with _ | ⟨ha, _⟩
    dsimp only [Op.foldRewrite]; have ht := truncTarget?_rel hG m n ha
    cases h₁ : truncTarget? m n a₁ <;> cases h₂ : truncTarget? m n a₂ <;> rw [h₁, h₂] at ht
    · exact .mk _ (.cons (ha.fout hG) .nil)
    · cases ht
    · cases ht
    · cases ht with
      | narrow _ _ hs => exact .mk _ (.cons hs .nil)
      | lift hte => cases hte with | mk _ _ _ hs => exact .mk _ (.cons hs .nil)
  | _ => all_goals (dsimp only [Op.foldRewrite]; exact OpRel.rewrite (.mk _ (TRel.fout hG hargs)))

private theorem foldWrap_ext_rel (hG : FRelG G' G) (k : ExtKind) {m n : Nat}
    {a₁ : Arg (FVal V₁) (.bits m)} {a₂ : Arg (FVal V₂) (.bits m)}
    (ha : ArgRel G (.bits m) a₁ a₂) (b : Nat) (r₁ : V₁ (.bits n)) (r₂ : V₂ (.bits n)) :
    FRelG (Tup.zip (as := [.bits n]) (r₁, ()) (r₂, ()) ++ G')
      (Tup.zip (({ code := k.toOpCode m n, args := (a₁, ()) } :
          Op (FVal V₁) [.bits n]).foldWrap b (r₁, ()))
        (({ code := k.toOpCode m n, args := (a₂, ()) } :
          Op (FVal V₂) [.bits n]).foldWrap b (r₂, ())) ++ G) := by
  have htg := extTarget_rel hG k (n := n) ha
  cases k <;> (
    dsimp only [ExtKind.toOpCode, Op.foldWrap]
    cases h₁ : extTarget (n := n) _ a₁ <;> cases h₂ : extTarget (n := n) _ a₂ <;>
      rw [h₁, h₂] at htg
    · exact hG.freshFVals (ts := [.bits n]) (r₁, ()) (r₂, ()) b
    · exact False.elim htg
    · exact False.elim htg
    · exact hG.cons_ext htg)

theorem FRelG.foldWrap (hG : FRelG G' G) {sig ts : List Ty} {code : OpCode sig ts}
    {args₁ : Tup (Arg (FVal V₁)) sig} {args₂ : Tup (Arg (FVal V₂)) sig}
    (hargs : TRel (ArgRel G) args₁ args₂) (b : Nat) (xs₁ : Tup V₁ ts) (xs₂ : Tup V₂ ts) :
    FRelG (Tup.zip xs₁ xs₂ ++ G')
      (Tup.zip (({ code := code, args := args₁ } : Op (FVal V₁) ts).foldWrap b xs₁)
               (({ code := code, args := args₂ } : Op (FVal V₂) ts).foldWrap b xs₂) ++ G) := by
  cases code with
  | sext _ _ =>
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩; rcases hargs with _ | ⟨ha, _⟩
    rcases xs₁ with ⟨r₁, ⟨⟩⟩; rcases xs₂ with ⟨r₂, ⟨⟩⟩; exact foldWrap_ext_rel hG .sext ha b r₁ r₂
  | zext _ _ =>
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩; rcases hargs with _ | ⟨ha, _⟩
    rcases xs₁ with ⟨r₁, ⟨⟩⟩; rcases xs₂ with ⟨r₂, ⟨⟩⟩; exact foldWrap_ext_rel hG .zext ha b r₁ r₂
  | trunc m n =>
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩; rcases hargs with _ | ⟨ha, _⟩
    rcases xs₁ with ⟨r₁, ⟨⟩⟩; rcases xs₂ with ⟨r₂, ⟨⟩⟩
    dsimp only [Op.foldWrap]; have ht := truncTarget?_rel hG m n ha
    cases h₁ : truncTarget? m n a₁ <;> cases h₂ : truncTarget? m n a₂ <;> rw [h₁, h₂] at ht
    · exact hG.freshFVals (ts := [.bits n]) (r₁, ()) (r₂, ()) b
    · cases ht
    · cases ht
    · cases ht with
      | narrow _ _ _ => exact hG.freshFVals (ts := [.bits n]) (r₁, ()) (r₂, ()) b
      | lift hte => exact hG.cons_ext hte
  | not _ =>
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩; rcases hargs with _ | ⟨ha, _⟩
    rcases xs₁ with ⟨r₁, ⟨⟩⟩; rcases xs₂ with ⟨r₂, ⟨⟩⟩
    dsimp only [Op.foldWrap]; rw [ha.fkey_eq hG]; exact hG.cons_inv .not_ (ha.fout hG)
  | bswap _ =>
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩; rcases hargs with _ | ⟨ha, _⟩
    rcases xs₁ with ⟨r₁, ⟨⟩⟩; rcases xs₂ with ⟨r₂, ⟨⟩⟩
    dsimp only [Op.foldWrap]; split
    · rw [ha.fkey_eq hG]; exact hG.cons_inv .bswap (ha.fout hG)
    · exact hG.freshFVals (ts := [_]) (r₁, ()) (r₂, ()) b
  | rbit _ =>
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩; rcases hargs with _ | ⟨ha, _⟩
    rcases xs₁ with ⟨r₁, ⟨⟩⟩; rcases xs₂ with ⟨r₂, ⟨⟩⟩
    dsimp only [Op.foldWrap]; rw [ha.fkey_eq hG]; exact hG.cons_inv .rbit (ha.fout hG)
  | select t =>
    cases t with
    | bool =>
      rcases args₁ with ⟨c₁, a₁, b₁, ⟨⟩⟩; rcases args₂ with ⟨c₂, a₂, b₂, ⟨⟩⟩
      rcases hargs with _ | ⟨hc, _ | ⟨ha, _ | ⟨hb, _⟩⟩⟩
      rcases xs₁ with ⟨r₁, ⟨⟩⟩; rcases xs₂ with ⟨r₂, ⟨⟩⟩
      have ha' := ha.fout hG; have hb' := hb.fout hG
      dsimp only [Op.foldWrap]; rw [ha'.imm?_eq, hb'.imm?_eq]; split
      · rw [hc.fkey_eq hG]; exact hG.cons_inv .not_ (hc.fout hG)
      · exact hG.freshFVals (ts := [.bool]) (r₁, ()) (r₂, ()) b
    | _ => dsimp only [Op.foldWrap]; exact hG.freshFVals xs₁ xs₂ b
  | _ => all_goals (dsimp only [Op.foldWrap]; exact hG.freshFVals xs₁ xs₂ b)

end

/-! ## Block projection helper and `Wf.induct` correctness proofs -/

theorem foldB_get {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} (b : Nat) :
    {sig : List (List Ty)} → {ts : List Ty} → (bs : Blocks (FVal V) L rs sig) →
    (i : Member ts sig) → (xs : Tup V ts) →
    (foldB b bs).get i xs = fold (b + ts.length) (bs.get i (freshFVals ts xs b))
  | _, _, .cons _ _, .here, _ => rfl
  | _, _, .cons _ bs, .there i, xs => foldB_get b bs i xs

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

/-- Weakest-precondition preservation for `fold`, proved via `Wf.induct`. -/
theorem fold_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {G : Ctx (FVal Val) Val} {D : Ctx Cont Cont}
    {e₁ : Expr (FVal Val) Cont rs} {e₂ : Expr Val Cont rs} (hwf : Wf G D e₁ e₂) :
    (∀ p ∈ D, p.2.1 = p.2.2) →
    ∀ b ρ, FGood ρ b G → ∀ m, wp Γ Q X e₂ m → wp Γ Q X (fold b e₁) m := by
  induction hwf using Wf.induct with
  | @let_ G D ts op₁ op₂ k₁ k₂ hop _ ih =>
    intro hD b ρ hG m hw; dsimp only [wp] at hw
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
          exact Op.wp_mono (fun xs ⟨hxs, hG'⟩ =>
            ih _ xs hD (b + ts.length) (fupdTup ρ b xs) hG' m hxs)
            (OpRel.foldRewrite_wp hG hargs hw)
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
    {e₁ : Expr (FVal V₁) L₁ rs} {e₂ : Expr (FVal V₂) L₂ rs} (hwf : Wf G D e₁ e₂) :
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
        cases hp₁ : ({ code := code, args := args₁ } : Op (FVal V₁) ts).simpProv? <;>
          cases hp₂ : ({ code := code, args := args₂ } : Op (FVal V₂) ts).simpProv? <;>
          rw [hp₁, hp₂] at hpr
        · exact .let_ (OpRel.foldRewrite_rel hG hargs) fun xs₁ xs₂ =>
            ih _ _ (hG.foldWrap hargs b xs₁ xs₂) (b + ts.length)
        · exact False.elim hpr
        · exact False.elim hpr
        · exact ih _ _ hpr b
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
