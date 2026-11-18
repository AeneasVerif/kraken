module

public import LeanQbe.T.Ops
public import LeanQbe.T.TyLemmas
import all Kraken.Mem

/-!
# Lemmas about `LeanQbe.T.Ops`

* Operand evaluation (`Arg.val_var`, `Arg.val_imm`) and `OpCode.wp_mono` / `Op.wp_mono`.
* Non-vacuity of NaN quantification (`isFloatNaN_packedNaN`).
* Arithmetic facts for `addc`, `subb`, and `umulw`.
* Balanced vector lane lemmas (`lane_lift2`, `lane_lift1`).
* Store-load round-trip on `Kraken.Mem 64` (`loadVal_storeMem`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

/-! ## Operands -/

@[simp] theorem Arg.val_var {t : Ty} (v : Val t) : (Arg.var v).val = v := rfl
@[simp] theorem Arg.val_imm {t : Ty} (c : Val t) : (Arg.imm c : Arg Val t).val = c := rfl

/-! ## Monotonicity of `OpCode.wp` and `Op.wp` -/

theorem floatResultWp_mono (f : Fmt) (res : Float.Model.UnpackedFloat)
    {p q : BitVec f.width → Prop} (h : ∀ r, p r → q r) :
    floatResultWp f res p → floatResultWp f res q := by
  unfold floatResultWp
  split
  · exact fun hp r hr => h r (hp r hr)
  · exact h _

theorem liftFloatRel1_mono (op : Float.Model.Format → Float.Model.UnpackedFloat →
      Float.Model.UnpackedFloat) :
    ∀ (t : Ty) (a : Val t) (p q : Val t → Prop), (∀ r, p r → q r) →
      liftFloatRel1 op t a p → liftFloatRel1 op t a q
  | .float f, _, _, _, h, hp => floatResultWp_mono f _ h hp
  | .pair s u, a, _, _, h, hp =>
      liftFloatRel1_mono op s a.1 _ _
        (fun r1 => liftFloatRel1_mono op u a.2 _ _ (fun r2 => h (r1, r2))) hp
  | .bool, _, _, _, _, hp => hp
  | .bits _, _, _, _, _, hp => hp

theorem liftFloatRel2_mono (op : Float.Model.Format → Float.Model.UnpackedFloat →
      Float.Model.UnpackedFloat → Float.Model.UnpackedFloat) :
    ∀ (t : Ty) (a b : Val t) (p q : Val t → Prop), (∀ r, p r → q r) →
      liftFloatRel2 op t a b p → liftFloatRel2 op t a b q
  | .float f, _, _, _, _, h, hp => floatResultWp_mono f _ h hp
  | .pair s u, a, b, _, _, h, hp =>
      liftFloatRel2_mono op s a.1 b.1 _ _
        (fun r1 => liftFloatRel2_mono op u a.2 b.2 _ _ (fun r2 => h (r1, r2))) hp
  | .bool, _, _, _, _, _, hp => hp
  | .bits _, _, _, _, _, _, hp => hp

theorem liftFloatRel3_mono (op : Float.Model.Format → Float.Model.UnpackedFloat →
      Float.Model.UnpackedFloat → Float.Model.UnpackedFloat → Float.Model.UnpackedFloat) :
    ∀ (t : Ty) (a b c : Val t) (p q : Val t → Prop), (∀ r, p r → q r) →
      liftFloatRel3 op t a b c p → liftFloatRel3 op t a b c q
  | .float f, _, _, _, _, _, h, hp => floatResultWp_mono f _ h hp
  | .pair s u, a, b, c, _, _, h, hp =>
      liftFloatRel3_mono op s a.1 b.1 c.1 _ _
        (fun r1 => liftFloatRel3_mono op u a.2 b.2 c.2 _ _ (fun r2 => h (r1, r2))) hp
  | .bool, _, _, _, _, _, _, hp => hp
  | .bits _, _, _, _, _, _, _, hp => hp

theorem convertFloat_mono (src dst : Fmt) (b : BitVec src.width)
    {p q : BitVec dst.width → Prop} (h : ∀ r, p r → q r) :
    convertFloat src dst b p → convertFloat src dst b q := by
  unfold convertFloat
  split
  · exact fun hp r hr => h r (hp r hr)
  · exact h _
  · exact h _

private theorem cond_false_mono {b : Bool} {p q : Prop} (h : p → q) :
    (if b then False else p) → (if b then False else q) := by
  cases b
  · exact h
  · exact False.elim

theorem OpCode.wp_mono : {as rs : List Ty} → (c : OpCode as rs) → (args : Tup Val as) →
    {p q : Tup Val rs → Prop} → (∀ r, p r → q r) → c.wp args p → c.wp args q
  | _, _, .copy _, (_, ()), _, _, h, hp => h _ hp
  | _, _, .add _, (_, _, ()), _, _, h, hp => cond_false_mono (h _) hp
  | _, _, .sub _, (_, _, ()), _, _, h, hp => cond_false_mono (h _) hp
  | _, _, .mul _, (_, _, ()), _, _, h, hp => cond_false_mono (h _) hp
  | _, _, .neg _, (_, ()), _, _, h, hp => cond_false_mono (h _) hp
  | _, _, .and _, (_, _, ()), _, _, h, hp => h _ hp
  | _, _, .or _, (_, _, ()), _, _, h, hp => h _ hp
  | _, _, .xor _, (_, _, ()), _, _, h, hp => h _ hp
  | _, _, .not _, (_, ()), _, _, h, hp => h _ hp
  | _, _, .ternlog _ _, (_, _, _, ()), _, _, h, hp => h _ hp
  | _, _, .shl _, (_, _, ()), _, _, h, hp => cond_false_mono (h _) hp
  | _, _, .lshr _, (_, _, ()), _, _, h, hp => cond_false_mono (h _) hp
  | _, _, .ashr _, (_, _, ()), _, _, h, hp => cond_false_mono (h _) hp
  | _, _, .rotl _, (_, _, ()), _, _, h, hp => cond_false_mono (h _) hp
  | _, _, .rotr _, (_, _, ()), _, _, h, hp => cond_false_mono (h _) hp
  | _, _, .fshl _, (_, _, _, ()), _, _, h, hp => h _ hp
  | _, _, .fshr _, (_, _, _, ()), _, _, h, hp => h _ hp
  | _, _, .bswap _, (_, ()), _, _, h, hp => cond_false_mono (h _) hp
  | _, _, .clz _, (_, ()), _, _, h, hp => h _ hp
  | _, _, .cls _, (_, ()), _, _, h, hp => h _ hp
  | _, _, .rbit _, (_, ()), _, _, h, hp => h _ hp
  | _, _, .ctz _, (_, ()), _, _, h, hp => h _ hp
  | _, _, .popcnt _, (_, ()), _, _, h, hp => h _ hp
  | _, _, .cmp _ _ _ rfl, (_, _, ()), _, _, h, hp => cond_false_mono (h _) hp
  | _, _, .select _, (_, _, _, ()), _, _, h, hp => h _ hp
  | _, _, .blend _ _ rfl, (_, _, _, ()), _, _, h, hp => h _ hp
  | _, _, .zext _ _, (_, ()), _, _, h, hp => ⟨hp.1, h _ hp.2⟩
  | _, _, .sext _ _, (_, ()), _, _, h, hp => ⟨hp.1, h _ hp.2⟩
  | _, _, .trunc _ _, (_, ()), _, _, h, hp => ⟨hp.1, h _ hp.2⟩
  | _, _, .ofBool _, (_, ()), _, _, h, hp => h _ hp
  | _, _, .addc _, (_, _, _, ()), _, _, h, hp => h _ hp
  | _, _, .subb _, (_, _, _, ()), _, _, h, hp => h _ hp
  | _, _, .umulw _, (_, _, ()), _, _, h, hp => h _ hp
  | _, _, .smulw _, (_, _, ()), _, _, h, hp => h _ hp
  | _, _, .udiv _, (_, _, ()), _, _, h, hp => ⟨hp.1, h _ hp.2⟩
  | _, _, .sdiv _, (_, _, ()), _, _, h, hp => ⟨hp.1, h _ hp.2⟩
  | _, _, .urem _, (_, _, ()), _, _, h, hp => ⟨hp.1, h _ hp.2⟩
  | _, _, .srem _, (_, _, ()), _, _, h, hp => ⟨hp.1, h _ hp.2⟩
  | _, _, .udiv0 _, (_, _, ()), _, _, h, hp => h _ hp
  | _, _, .sdiv0 _, (_, _, ()), _, _, h, hp => h _ hp
  | _, _, .mkpair _ _, (_, _, ()), _, _, h, hp => h _ hp
  | _, _, .unpair _ _, (_, ()), _, _, h, hp => h _ hp
  | _, _, .bitcast _ _ _, (_, ()), _, _, h, hp => h _ hp
  | _, _, .shufd _ _, (_, ()), _, _, h, hp => ⟨hp.1, hp.2.1, h _ hp.2.2⟩
  | _, _, .shufb _, (_, _, ()), _, _, h, hp => ⟨hp.1, hp.2.1, h _ hp.2.2⟩
  | _, _, .alignr _ _, (_, _, ()), _, _, h, hp => ⟨hp.1, hp.2.1, h _ hp.2.2⟩
  | _, _, .blendw _ _, (_, _, ()), _, _, h, hp => ⟨hp.1, hp.2.1, h _ hp.2.2⟩
  | _, _, .sha256rnds2, (_, _, _, ()), _, _, h, hp => h _ hp
  | _, _, .sha256msg1, (_, _, ()), _, _, h, hp => h _ hp
  | _, _, .sha256msg2, (_, _, ()), _, _, h, hp => h _ hp
  | _, _, .fadd t, (a, b, ()), _, _, h, hp =>
      cond_false_mono (liftFloatRel2_mono _ t a b _ _ fun _ => h _) hp
  | _, _, .fsub t, (a, b, ()), _, _, h, hp =>
      cond_false_mono (liftFloatRel2_mono _ t a b _ _ fun _ => h _) hp
  | _, _, .fmul t, (a, b, ()), _, _, h, hp =>
      cond_false_mono (liftFloatRel2_mono _ t a b _ _ fun _ => h _) hp
  | _, _, .fdiv t, (a, b, ()), _, _, h, hp =>
      cond_false_mono (liftFloatRel2_mono _ t a b _ _ fun _ => h _) hp
  | _, _, .ffma t, (a, b, c, ()), _, _, h, hp =>
      cond_false_mono (liftFloatRel3_mono _ t a b c _ _ fun _ => h _) hp
  | _, _, .fsqrt t, (a, ()), _, _, h, hp =>
      cond_false_mono (liftFloatRel1_mono _ t a _ _ fun _ => h _) hp
  | _, _, .fneg _, (_, ()), _, _, h, hp => cond_false_mono (h _) hp
  | _, _, .fabs _, (_, ()), _, _, h, hp => cond_false_mono (h _) hp
  | _, _, .fcmp _ _ _ rfl, (_, _, ()), _, _, h, hp => cond_false_mono (h _) hp
  | _, _, .fptoui f n, (a, ()), _, _, h, hp => by
      simp only [OpCode.wp] at hp ⊢
      cases htr : truncToInt (unpackFloat f a) with
      | none => simp only [htr] at hp
      | some z => simp only [htr] at hp ⊢; exact ⟨hp.1, hp.2.1, h _ hp.2.2⟩
  | _, _, .fptosi f n, (a, ()), _, _, h, hp => by
      simp only [OpCode.wp] at hp ⊢
      refine ⟨hp.1, ?_⟩
      have hp2 := hp.2
      cases htr : truncToInt (unpackFloat f a) with
      | none => simp only [htr] at hp2
      | some z => simp only [htr] at hp2 ⊢; exact ⟨hp2.1, hp2.2.1, h _ hp2.2.2⟩
  | _, _, .uitofp _ _, (_, ()), _, _, h, hp => h _ hp
  | _, _, .sitofp _ _, (_, ()), _, _, h, hp => h _ hp
  | _, _, .fcvt f g, (a, ()), _, _, h, hp =>
      convertFloat_mono f g a (fun _ => h _) hp

theorem Op.wp_mono {rs : List Ty} {op : Op Val rs} {p q : Tup Val rs → Prop}
    (h : ∀ r, p r → q r) : op.wp p → op.wp q :=
  OpCode.wp_mono op.code (vals op.args) h

/-! ## Non-vacuity of float NaN quantification -/

/-- The canonical packed NaN satisfies `isFloatNaN f _ = true`. -/
theorem isFloatNaN_packedNaN (f : Fmt) :
    isFloatNaN f ((Float.Model.UnpackedFloat.packedNaN f.format).cast (Fmt.format_numBits f)) =
      true := by
  cases f <;> decide

/-! ## Simplification lemmas for `OpCode.wp` -/

@[simp] theorem OpCode.wp_copy (t : Ty) (args : Tup Val [t]) (post : Tup Val [t] → Prop) :
    OpCode.wp (.copy t) args post = post (args.1, ()) := rfl

@[simp] theorem OpCode.wp_add (t : Ty) (args : Tup Val [t, t]) (post : Tup Val [t] → Prop) :
    OpCode.wp (.add t) args post =
      (if t.hasFloat then False else post (lift2 (· + ·) (· ^^ ·) t args.1 args.2.1, ())) := rfl

@[simp] theorem OpCode.wp_sub (t : Ty) (args : Tup Val [t, t]) (post : Tup Val [t] → Prop) :
    OpCode.wp (.sub t) args post =
      (if t.hasFloat then False else post (lift2 (· - ·) (· ^^ ·) t args.1 args.2.1, ())) := rfl

@[simp] theorem OpCode.wp_mul (t : Ty) (args : Tup Val [t, t]) (post : Tup Val [t] → Prop) :
    OpCode.wp (.mul t) args post =
      (if t.hasFloat then False else post (lift2 (· * ·) (· && ·) t args.1 args.2.1, ())) := rfl

@[simp] theorem OpCode.wp_neg (t : Ty) (args : Tup Val [t]) (post : Tup Val [t] → Prop) :
    OpCode.wp (.neg t) args post =
      (if t.hasFloat then False else post (lift1 (- ·) id t args.1, ())) := rfl

@[simp] theorem OpCode.wp_and (t : Ty) (args : Tup Val [t, t]) (post : Tup Val [t] → Prop) :
    OpCode.wp (.and t) args post = post (lift2 (· &&& ·) (· && ·) t args.1 args.2.1, ()) := rfl

@[simp] theorem OpCode.wp_or (t : Ty) (args : Tup Val [t, t]) (post : Tup Val [t] → Prop) :
    OpCode.wp (.or t) args post = post (lift2 (· ||| ·) (· || ·) t args.1 args.2.1, ()) := rfl

@[simp] theorem OpCode.wp_xor (t : Ty) (args : Tup Val [t, t]) (post : Tup Val [t] → Prop) :
    OpCode.wp (.xor t) args post = post (lift2 (· ^^^ ·) (· ^^ ·) t args.1 args.2.1, ()) := rfl

@[simp] theorem OpCode.wp_not (t : Ty) (args : Tup Val [t]) (post : Tup Val [t] → Prop) :
    OpCode.wp (.not t) args post = post (lift1 (~~~ ·) (! ·) t args.1, ()) := rfl

@[simp] theorem OpCode.wp_ternlog (t : Ty) (imm : BitVec 8) (args : Tup Val [t, t, t])
    (post : Tup Val [t] → Prop) :
    OpCode.wp (.ternlog t imm) args post =
      post (lift3 (fun x y z => ternaryLogic x y z imm)
        (fun x y z => ternaryLogicBool x y z imm) t args.1 args.2.1 args.2.2.1, ()) := rfl

@[simp] theorem OpCode.wp_shl (t : Ty) (args : Tup Val [t, t]) (post : Tup Val [t] → Prop) :
    OpCode.wp (.shl t) args post =
      (if t.hasFloat then False
       else post (lift2 (fun {n} x y => x <<< (y.toNat % n)) (fun x _ => x) t
         args.1 args.2.1, ())) := rfl

@[simp] theorem OpCode.wp_lshr (t : Ty) (args : Tup Val [t, t]) (post : Tup Val [t] → Prop) :
    OpCode.wp (.lshr t) args post =
      (if t.hasFloat then False
       else post (lift2 (fun {n} x y => x >>> (y.toNat % n)) (fun x _ => x) t
         args.1 args.2.1, ())) := rfl

@[simp] theorem OpCode.wp_ashr (t : Ty) (args : Tup Val [t, t]) (post : Tup Val [t] → Prop) :
    OpCode.wp (.ashr t) args post =
      (if t.hasFloat then False
       else post (lift2 (fun {n} x y => x.sshiftRight (y.toNat % n)) (fun x _ => x) t
         args.1 args.2.1, ())) := rfl

@[simp] theorem OpCode.wp_rotl (t : Ty) (args : Tup Val [t, t]) (post : Tup Val [t] → Prop) :
    OpCode.wp (.rotl t) args post =
      (if t.hasFloat then False
       else post (lift2 (fun {n} x y => x.rotateLeft (y.toNat % n)) (fun x _ => x) t
         args.1 args.2.1, ())) := rfl

@[simp] theorem OpCode.wp_rotr (t : Ty) (args : Tup Val [t, t]) (post : Tup Val [t] → Prop) :
    OpCode.wp (.rotr t) args post =
      (if t.hasFloat then False
       else post (lift2 (fun {n} x y => x.rotateRight (y.toNat % n)) (fun x _ => x) t
         args.1 args.2.1, ())) := rfl

@[simp] theorem OpCode.wp_fshl (n : Nat) (args : Tup Val [.bits n, .bits n, .bits n])
    (post : Tup Val [.bits n] → Prop) :
    OpCode.wp (.fshl n) args post =
      post ((((args.1 ++ args.2.1) <<< (args.2.2.1.toNat % n)).extractLsb' n n), ()) := rfl

@[simp] theorem OpCode.wp_fshr (n : Nat) (args : Tup Val [.bits n, .bits n, .bits n])
    (post : Tup Val [.bits n] → Prop) :
    OpCode.wp (.fshr n) args post =
      post ((((args.1 ++ args.2.1) >>> (args.2.2.1.toNat % n)).extractLsb' 0 n), ()) := rfl

@[simp] theorem OpCode.wp_bswap (t : Ty) (args : Tup Val [t]) (post : Tup Val [t] → Prop) :
    OpCode.wp (.bswap t) args post =
      (if !t.bswapOk then False else post (lift1 bswapBits id t args.1, ())) := rfl

@[simp] theorem OpCode.wp_clz (n : Nat) (args : Tup Val [.bits n])
    (post : Tup Val [.bits n] → Prop) :
    OpCode.wp (.clz n) args post = post (args.1.clz, ()) := rfl

@[simp] theorem OpCode.wp_cls (n : Nat) (args : Tup Val [.bits n])
    (post : Tup Val [.bits n] → Prop) :
    OpCode.wp (.cls n) args post =
      post ((if args.1.msb then (~~~args.1).clz else args.1.clz) - 1#n, ()) := rfl

@[simp] theorem OpCode.wp_rbit (n : Nat) (args : Tup Val [.bits n])
    (post : Tup Val [.bits n] → Prop) :
    OpCode.wp (.rbit n) args post = post (args.1.reverse, ()) := rfl

@[simp] theorem OpCode.wp_ctz (n : Nat) (args : Tup Val [.bits n])
    (post : Tup Val [.bits n] → Prop) :
    OpCode.wp (.ctz n) args post = post (args.1.reverse.clz, ()) := rfl

@[simp] theorem OpCode.wp_popcnt (n : Nat) (args : Tup Val [.bits n])
    (post : Tup Val [.bits n] → Prop) :
    OpCode.wp (.popcnt n) args post = post (args.1.cpop, ()) := rfl

@[simp] theorem OpCode.wp_cmp (o : CmpOp) (t : Ty) {m : Ty} (h : m = t.mask)
    (args : Tup Val [t, t]) (post : Tup Val [m] → Prop) :
    OpCode.wp (.cmp o t m h) args post =
      (if t.hasFloat then False
       else post (cast (congrArg (fun u => Tup Val [u]) h.symm)
              (liftCmp o.evalBits o.evalBool t args.1 args.2.1, ()))) := by
  subst h; rfl

@[simp] theorem OpCode.wp_select (t : Ty) (args : Tup Val [.bool, t, t])
    (post : Tup Val [t] → Prop) :
    OpCode.wp (.select t) args post = post (if args.1 then args.2.1 else args.2.2.1, ()) := rfl

@[simp] theorem OpCode.wp_blend (t : Ty) {m : Ty} (h : m = t.mask)
    (args : Tup Val [m, t, t]) (post : Tup Val [t] → Prop) :
    OpCode.wp (.blend t m h) args post =
      post (blendV t (cast (congrArg Val h) args.1) args.2.1 args.2.2.1, ()) := by
  subst h; rfl

@[simp] theorem OpCode.wp_zext (m n : Nat) (args : Tup Val [.bits m])
    (post : Tup Val [.bits n] → Prop) :
    OpCode.wp (.zext m n) args post = (m ≤ n ∧ post (args.1.setWidth n, ())) := rfl

@[simp] theorem OpCode.wp_sext (m n : Nat) (args : Tup Val [.bits m])
    (post : Tup Val [.bits n] → Prop) :
    OpCode.wp (.sext m n) args post = (m ≤ n ∧ post (args.1.signExtend n, ())) := rfl

@[simp] theorem OpCode.wp_trunc (m n : Nat) (args : Tup Val [.bits m])
    (post : Tup Val [.bits n] → Prop) :
    OpCode.wp (.trunc m n) args post = (n ≤ m ∧ post (args.1.setWidth n, ())) := rfl

@[simp] theorem OpCode.wp_ofBool (n : Nat) (args : Tup Val [.bool])
    (post : Tup Val [.bits n] → Prop) :
    OpCode.wp (.ofBool n) args post = post (BitVec.ofNat n args.1.toNat, ()) := rfl

@[simp] theorem OpCode.wp_addc (n : Nat) (args : Tup Val [.bits n, .bits n, .bool])
    (post : Tup Val [.bits n, .bool] → Prop) :
    OpCode.wp (.addc n) args post =
      post (args.1 + args.2.1 + BitVec.ofNat n args.2.2.1.toNat,
        decide (2 ^ n ≤ args.1.toNat + args.2.1.toNat + args.2.2.1.toNat), ()) := rfl

@[simp] theorem OpCode.wp_subb (n : Nat) (args : Tup Val [.bits n, .bits n, .bool])
    (post : Tup Val [.bits n, .bool] → Prop) :
    OpCode.wp (.subb n) args post =
      post (args.1 - args.2.1 - BitVec.ofNat n args.2.2.1.toNat,
        decide (args.1.toNat < args.2.1.toNat + args.2.2.1.toNat), ()) := rfl

@[simp] theorem OpCode.wp_umulw (n : Nat) (args : Tup Val [.bits n, .bits n])
    (post : Tup Val [.bits n, .bits n] → Prop) :
    OpCode.wp (.umulw n) args post =
      post (args.1 * args.2.1, BitVec.ofNat n (args.1.toNat * args.2.1.toNat / 2 ^ n), ()) := rfl

@[simp] theorem OpCode.wp_smulw (n : Nat) (args : Tup Val [.bits n, .bits n])
    (post : Tup Val [.bits n, .bits n] → Prop) :
    OpCode.wp (.smulw n) args post =
      post (args.1 * args.2.1,
        (BitVec.ofInt (n + n) (args.1.toInt * args.2.1.toInt)).extractLsb' n n, ()) := rfl

@[simp] theorem OpCode.wp_udiv (n : Nat) (args : Tup Val [.bits n, .bits n])
    (post : Tup Val [.bits n] → Prop) :
    OpCode.wp (.udiv n) args post = (args.2.1 ≠ 0 ∧ post (args.1 / args.2.1, ())) := rfl

@[simp] theorem OpCode.wp_sdiv (n : Nat) (args : Tup Val [.bits n, .bits n])
    (post : Tup Val [.bits n] → Prop) :
    OpCode.wp (.sdiv n) args post =
      (sdivDefined args.1 args.2.1 = true ∧ post (args.1.sdiv args.2.1, ())) := rfl

@[simp] theorem OpCode.wp_urem (n : Nat) (args : Tup Val [.bits n, .bits n])
    (post : Tup Val [.bits n] → Prop) :
    OpCode.wp (.urem n) args post = (args.2.1 ≠ 0 ∧ post (args.1 % args.2.1, ())) := rfl

@[simp] theorem OpCode.wp_srem (n : Nat) (args : Tup Val [.bits n, .bits n])
    (post : Tup Val [.bits n] → Prop) :
    OpCode.wp (.srem n) args post =
      (sdivDefined args.1 args.2.1 = true ∧ post (args.1.srem args.2.1, ())) := rfl

@[simp] theorem OpCode.wp_udiv0 (n : Nat) (args : Tup Val [.bits n, .bits n])
    (post : Tup Val [.bits n] → Prop) :
    OpCode.wp (.udiv0 n) args post =
      post (if args.2.1 = 0 then 0 else args.1 / args.2.1, ()) := rfl

@[simp] theorem OpCode.wp_sdiv0 (n : Nat) (args : Tup Val [.bits n, .bits n])
    (post : Tup Val [.bits n] → Prop) :
    OpCode.wp (.sdiv0 n) args post =
      post (if args.2.1 = 0 then 0 else args.1.sdiv args.2.1, ()) := rfl

@[simp] theorem OpCode.wp_mkpair (a b : Ty) (args : Tup Val [a, b])
    (post : Tup Val [.pair a b] → Prop) :
    OpCode.wp (.mkpair a b) args post = post ((args.1, args.2.1), ()) := rfl

@[simp] theorem OpCode.wp_unpair (a b : Ty) (args : Tup Val [.pair a b])
    (post : Tup Val [a, b] → Prop) :
    OpCode.wp (.unpair a b) args post = post (args.1.1, args.1.2, ()) := rfl

@[simp] theorem OpCode.wp_bitcast (t u : Ty) (h : t.size = u.size) (args : Tup Val [t])
    (post : Tup Val [u] → Prop) :
    OpCode.wp (.bitcast t u h) args post = post (ofBits u ((toBits t args.1).cast h), ()) := rfl

@[simp] theorem OpCode.wp_shufd (t : Ty) (imm : BitVec 8) (args : Tup Val [t])
    (post : Tup Val [t] → Prop) :
    OpCode.wp (.shufd t imm) args post =
      (t.size ≠ 0 ∧ t.size % 128 = 0 ∧
        post (ofBits t (shuffleDwords (toBits t args.1) imm), ())) := rfl

@[simp] theorem OpCode.wp_shufb (t : Ty) (args : Tup Val [t, t]) (post : Tup Val [t] → Prop) :
    OpCode.wp (.shufb t) args post =
      (t.size ≠ 0 ∧ t.size % 128 = 0 ∧
        post (ofBits t (shuffleBytes (toBits t args.1) (toBits t args.2.1)), ())) := rfl

@[simp] theorem OpCode.wp_alignr (t : Ty) (imm : BitVec 8) (args : Tup Val [t, t])
    (post : Tup Val [t] → Prop) :
    OpCode.wp (.alignr t imm) args post =
      (t.size ≠ 0 ∧ t.size % 128 = 0 ∧
        post (ofBits t (alignBytes (toBits t args.1) (toBits t args.2.1) imm), ())) := rfl

@[simp] theorem OpCode.wp_blendw (t : Ty) (imm : BitVec 8) (args : Tup Val [t, t])
    (post : Tup Val [t] → Prop) :
    OpCode.wp (.blendw t imm) args post =
      (t.size ≠ 0 ∧ t.size % 128 = 0 ∧
        post (ofBits t (blendWords (toBits t args.1) (toBits t args.2.1) imm), ())) := rfl

@[simp] theorem OpCode.wp_sha256rnds2 (args : Tup Val [v4i32, v4i32, v4i32])
    (post : Tup Val [v4i32] → Prop) :
    OpCode.wp .sha256rnds2 args post =
      post (ofBits v4i32
        (Sha256.rounds2 (toBits v4i32 args.1) (toBits v4i32 args.2.1)
          (toBits v4i32 args.2.2.1)), ()) := rfl

@[simp] theorem OpCode.wp_sha256msg1 (args : Tup Val [v4i32, v4i32])
    (post : Tup Val [v4i32] → Prop) :
    OpCode.wp .sha256msg1 args post =
      post (ofBits v4i32 (Sha256.msg1 (toBits v4i32 args.1) (toBits v4i32 args.2.1)), ()) := rfl

@[simp] theorem OpCode.wp_sha256msg2 (args : Tup Val [v4i32, v4i32])
    (post : Tup Val [v4i32] → Prop) :
    OpCode.wp .sha256msg2 args post =
      post (ofBits v4i32 (Sha256.msg2 (toBits v4i32 args.1) (toBits v4i32 args.2.1)), ()) := rfl

@[simp] theorem OpCode.wp_fadd (t : Ty) (args : Tup Val [t, t]) (post : Tup Val [t] → Prop) :
    OpCode.wp (.fadd t) args post =
      (if !t.isFloatTree then False
       else liftFloatRel2 Float.Model.UnpackedFloat.add t args.1 args.2.1
         fun r => post (r, ())) := rfl

@[simp] theorem OpCode.wp_fsub (t : Ty) (args : Tup Val [t, t]) (post : Tup Val [t] → Prop) :
    OpCode.wp (.fsub t) args post =
      (if !t.isFloatTree then False
       else liftFloatRel2 Float.Model.UnpackedFloat.sub t args.1 args.2.1
         fun r => post (r, ())) := rfl

@[simp] theorem OpCode.wp_fmul (t : Ty) (args : Tup Val [t, t]) (post : Tup Val [t] → Prop) :
    OpCode.wp (.fmul t) args post =
      (if !t.isFloatTree then False
       else liftFloatRel2 Float.Model.UnpackedFloat.mul t args.1 args.2.1
         fun r => post (r, ())) := rfl

@[simp] theorem OpCode.wp_fdiv (t : Ty) (args : Tup Val [t, t]) (post : Tup Val [t] → Prop) :
    OpCode.wp (.fdiv t) args post =
      (if !t.isFloatTree then False
       else liftFloatRel2 Float.Model.UnpackedFloat.div t args.1 args.2.1
         fun r => post (r, ())) := rfl

@[simp] theorem OpCode.wp_ffma (t : Ty) (args : Tup Val [t, t, t])
    (post : Tup Val [t] → Prop) :
    OpCode.wp (.ffma t) args post =
      (if !t.isFloatTree then False
       else liftFloatRel3 Float.Model.UnpackedFloat.fma t args.1 args.2.1 args.2.2.1
         fun r => post (r, ())) := rfl

@[simp] theorem OpCode.wp_fsqrt (t : Ty) (args : Tup Val [t]) (post : Tup Val [t] → Prop) :
    OpCode.wp (.fsqrt t) args post =
      (if !t.isFloatTree then False
       else liftFloatRel1 Float.Model.UnpackedFloat.sqrt t args.1
         fun r => post (r, ())) := rfl

@[simp] theorem OpCode.wp_fneg (t : Ty) (args : Tup Val [t]) (post : Tup Val [t] → Prop) :
    OpCode.wp (.fneg t) args post =
      (if !t.isFloatTree then False
       else post (lift1 (fun {n} x => x ^^^ (1#n <<< (n - 1))) id t args.1, ())) := rfl

@[simp] theorem OpCode.wp_fabs (t : Ty) (args : Tup Val [t]) (post : Tup Val [t] → Prop) :
    OpCode.wp (.fabs t) args post =
      (if !t.isFloatTree then False
       else post (lift1 (fun {n} x => x &&& ~~~(1#n <<< (n - 1))) id t args.1, ())) := rfl

@[simp] theorem OpCode.wp_fcmp (o : FCmpOp) (t : Ty) {m : Ty} (h : m = t.mask)
    (args : Tup Val [t, t]) (post : Tup Val [m] → Prop) :
    OpCode.wp (.fcmp o t m h) args post =
      (if !t.isFloatTree then False
       else post (cast (congrArg (fun u => Tup Val [u]) h.symm)
              (liftFCmp o t args.1 args.2.1, ()))) := by
  subst h; rfl

@[simp] theorem OpCode.wp_fptoui (f : Fmt) (n : Nat) (args : Tup Val [.float f])
    (post : Tup Val [.bits n] → Prop) :
    OpCode.wp (.fptoui f n) args post =
      (match truncToInt (unpackFloat f args.1) with
       | some z => 0 ≤ z ∧ z < 2 ^ n ∧ post (BitVec.ofInt n z, ())
       | none => False) := rfl

@[simp] theorem OpCode.wp_fptosi (f : Fmt) (n : Nat) (args : Tup Val [.float f])
    (post : Tup Val [.bits n] → Prop) :
    OpCode.wp (.fptosi f n) args post =
      (n ≠ 0 ∧ match truncToInt (unpackFloat f args.1) with
       | some z => -(2 ^ (n - 1) : Int) ≤ z ∧ z < 2 ^ (n - 1) ∧ post (BitVec.ofInt n z, ())
       | none => False) := rfl

@[simp] theorem OpCode.wp_uitofp (n : Nat) (f : Fmt) (args : Tup Val [.bits n])
    (post : Tup Val [.float f] → Prop) :
    OpCode.wp (.uitofp n f) args post =
      post (packFloat f (Float.Model.UnpackedFloat.ofInt f.format args.1.toNat), ()) := rfl

@[simp] theorem OpCode.wp_sitofp (n : Nat) (f : Fmt) (args : Tup Val [.bits n])
    (post : Tup Val [.float f] → Prop) :
    OpCode.wp (.sitofp n f) args post =
      post (packFloat f (Float.Model.UnpackedFloat.ofInt f.format args.1.toInt), ()) := rfl

@[simp] theorem OpCode.wp_fcvt (f g : Fmt) (args : Tup Val [.float f])
    (post : Tup Val [.float g] → Prop) :
    OpCode.wp (.fcvt f g) args post = convertFloat f g args.1 fun r => post (r, ()) := rfl

/-! ## Multi-result arithmetic lemmas -/

theorem addc_toNat {n : Nat} (a b : BitVec n) (c : Bool) :
    (decide (2 ^ n ≤ a.toNat + b.toNat + c.toNat)).toNat * 2 ^ n +
      (a + b + BitVec.ofNat n c.toNat).toNat =
      a.toNat + b.toNat + c.toNat := by
  have ha := a.isLt; have hb := b.isLt; have hc := Bool.toNat_le c
  have key : (a + b + BitVec.ofNat n c.toNat).toNat = (a.toNat + b.toNat + c.toNat) % 2 ^ n := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.add_mod_mod, Nat.mod_add_mod]
  rw [key]
  by_cases h : 2 ^ n ≤ a.toNat + b.toNat + c.toNat
  · have h2 : a.toNat + b.toNat + c.toNat - 2 ^ n < 2 ^ n := by omega
    rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt h2]
    simp [h]
  · rw [Nat.mod_eq_of_lt (by omega)]
    simp [h]

theorem subb_toNat {n : Nat} (a b : BitVec n) (c : Bool) :
    (a - b - BitVec.ofNat n c.toNat).toNat + b.toNat + c.toNat =
      a.toNat + (decide (a.toNat < b.toNat + c.toNat)).toNat * 2 ^ n := by
  have ha := a.isLt; have hb := b.isLt; have hc := Bool.toNat_le c
  by_cases hn : n = 0
  · subst hn
    have ha0 : a.toNat = 0 := by omega
    have hb0 : b.toNat = 0 := by omega
    have hsub0 : (a - b - BitVec.ofNat 0 c.toNat).toNat = 0 := by omega
    simp only [hsub0, ha0, hb0, Nat.pow_zero, Nat.mul_one]
    cases c <;> simp
  · have hpow : 1 < 2 ^ n := Nat.one_lt_two_pow hn
    have hcb : (BitVec.ofNat n c.toNat).toNat = c.toNat := by
      simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
    have hsub1 : (a - b).toNat = if b.toNat ≤ a.toNat then a.toNat - b.toNat
        else 2 ^ n + a.toNat - b.toNat := by
      rw [BitVec.toNat_sub]
      split <;> rename_i h
      · have : 2 ^ n - b.toNat + a.toNat = 2 ^ n + (a.toNat - b.toNat) := by omega
        rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
      · rw [Nat.mod_eq_of_lt (by omega)]; omega
    have hsub2 : (a - b - BitVec.ofNat n c.toNat).toNat =
        if c.toNat ≤ (a - b).toNat then (a - b).toNat - c.toNat
        else 2 ^ n + (a - b).toNat - c.toNat := by
      rw [BitVec.toNat_sub, hcb]
      split <;> rename_i h
      · have : 2 ^ n - c.toNat + (a - b).toNat = 2 ^ n + ((a - b).toNat - c.toNat) := by omega
        rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt (by have := (a - b).isLt; omega)]
      · have := (a - b).isLt
        rw [Nat.mod_eq_of_lt (by omega)]; omega
    rw [hsub2, hsub1]
    by_cases hlt : a.toNat < b.toNat + c.toNat
    · simp only [hlt, decide_true, Bool.toNat_true, Nat.one_mul]
      split <;> split <;> omega
    · simp only [hlt, decide_false, Bool.toNat_false, Nat.zero_mul, Nat.add_zero]
      split <;> split <;> omega

theorem umulw_toNat {n : Nat} (a b : BitVec n) :
    (a * b).toNat + 2 ^ n * (BitVec.ofNat n (a.toNat * b.toNat / 2 ^ n)).toNat =
      a.toNat * b.toNat ∧
    (BitVec.ofNat n (a.toNat * b.toNat / 2 ^ n)).toNat = a.toNat * b.toNat / 2 ^ n := by
  have hlt : a.toNat * b.toNat / 2 ^ n < 2 ^ n :=
    Nat.div_lt_of_lt_mul (Nat.mul_lt_mul_of_lt_of_lt a.isLt b.isLt)
  have hhi : (BitVec.ofNat n (a.toNat * b.toNat / 2 ^ n)).toNat = a.toNat * b.toNat / 2 ^ n := by
    simp [Nat.mod_eq_of_lt hlt]
  refine ⟨?_, hhi⟩
  rw [hhi, BitVec.toNat_mul]
  exact Nat.mod_add_div _ _

/-! ## Balanced vector lane lemmas -/

theorem lane_lift2 (f : ∀ {n}, BitVec n → BitVec n → BitVec n) (g : Bool → Bool → Bool) (t : Ty) :
    ∀ (k : Nat) (a b : Val (Ty.vec k t)) (i : Nat),
      lane k (lift2 f g (Ty.vec k t) a b) i = lift2 f g t (lane k a i) (lane k b i)
  | 0, _, _, _ => rfl
  | k + 1, a, b, i => by
    simp only [lane, lift2]
    split <;> exact lane_lift2 f g t k _ _ _

theorem lane_lift1 (f : ∀ {n}, BitVec n → BitVec n) (g : Bool → Bool) (t : Ty) :
    ∀ (k : Nat) (a : Val (Ty.vec k t)) (i : Nat),
      lane k (lift1 f g (Ty.vec k t) a) i = lift1 f g t (lane k a i)
  | 0, _, _ => rfl
  | k + 1, a, i => by
    simp only [lane, lift1]
    split <;> exact lane_lift1 f g t k _ _

/-! ## Memory round-trip on `Kraken.Mem 64` -/

private theorem get?_union_at {w : Nat} (m : Mem w) (bs : List UInt8) (a : BitVec w)
    (i : Nat) (hi : i < bs.length) (hw : bs.length ≤ 2 ^ w) :
    (m.union (bs.At a)).get? (a + BitVec.ofNat w i) = some bs[i] := by
  rw [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.union_eq, Std.ExtHashMap.getElem?_union]
  have hAt : (bs.At a)[a + BitVec.ofNat w i]? = some bs[i] := by
    rw [← Std.ExtHashMap.get?_eq_getElem?, get?_At_idx bs a i (Nat.lt_of_lt_of_le hi hw) hw,
      List.getElem?_eq_getElem hi]
  rw [hAt]
  cases m[a + BitVec.ofNat w i]? <;> rfl

private theorem ofInt_setWidth_eq (t : Ty) (i : Int) :
    BitVec.ofInt t.size i = (BitVec.ofInt (8 * t.bytes) i).setWidth t.size := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofInt, BitVec.toNat_setWidth]
  have hdvd : (2 ^ t.size : Int) ∣ (2 ^ (8 * t.bytes) : Int) := by
    have hle := Ty.size_le_eight_bytes t
    refine ⟨(2 ^ (8 * t.bytes - t.size) : Int), ?_⟩
    rw [← Int.pow_add, Nat.add_sub_cancel' hle]
  have hmod : (i % (2 : Int) ^ (8 * t.bytes)) % (2 : Int) ^ t.size = i % (2 : Int) ^ t.size :=
    Int.emod_emod_of_dvd i hdvd
  have hnn : 0 ≤ i % (2 : Int) ^ (8 * t.bytes) :=
    Int.emod_nonneg i (Int.ne_of_gt (Int.pow_pos (by decide)))
  have hnn2 : 0 ≤ i % (2 : Int) ^ t.size :=
    Int.emod_nonneg i (Int.ne_of_gt (Int.pow_pos (by decide)))
  have hcast1 : ((i % (2 : Int) ^ t.size).toNat : Int) = i % (2 : Int) ^ t.size :=
    Int.toNat_of_nonneg hnn2
  have hcast2 : (((i % (2 : Int) ^ (8 * t.bytes)).toNat % 2 ^ t.size : Nat) : Int) =
      (i % (2 : Int) ^ (8 * t.bytes)) % (2 : Int) ^ t.size := by
    push_cast
    rw [Int.toNat_of_nonneg hnn]
  exact Int.ofNat.inj (by
    show ((i % (2 : Int) ^ t.size).toNat : Int) =
      (((i % (2 : Int) ^ (8 * t.bytes)).toNat % 2 ^ t.size : Nat) : Int)
    rw [hcast1, hcast2, hmod])

/-- Reading from the empty partial memory `∅` fails whenever at least one byte is requested. -/
theorem loadInt_empty {w : Nat} (a : BitVec w) {n : Nat} (hn : 0 < n) :
    (∅ : Mem w).loadInt a n = none := by
  cases n with
  | zero => omega
  | succ k => simp [Mem.loadInt, Mem.loadBytes, List.range_succ_eq_map,
      Std.ExtHashMap.get?_eq_getElem?]

/-- Storing into the empty partial memory `∅` is UB whenever `0 < t.bytes`. -/
theorem storeOk_empty (t : Ty) (a : BitVec 64) (hb : 0 < t.bytes) :
    ¬ storeOk (∅ : Mem 64) t a := by
  rintro ⟨i, hi⟩
  rw [loadInt_empty a hb] at hi
  cases hi

/-- Reading back a stored value from `storeMem m t a v` yields `v`, provided `t.bytes ≤ 2 ^ 64`. -/
theorem loadVal_storeMem (m : Mem 64) (t : Ty) (a : BitVec 64) (v : Val t)
    (hb : t.bytes ≤ 2 ^ 64) :
    loadVal (storeMem m t a v) t a = some v := by
  let bs := Int.toBytes t.bytes ((toBits t v).setWidth (8 * t.bytes)).toInt
  have hlen : bs.length = t.bytes := Int.toBytes_length _ _
  have hget : ∀ i (hi : i < t.bytes),
      ((m.union (bs.At a)).get? (a + BitVec.ofNat 64 i)) =
        some (bs.get ⟨i, hlen ▸ hi⟩) := by
    intro i hi
    exact get?_union_at m bs a i (hlen ▸ hi) (hlen ▸ hb)
  have hloadBytes : (storeMem m t a v).loadBytes a t.bytes = some bs := by
    simp only [storeMem, Mem.storeInt, Mem.storeBytes, Mem.loadBytes]
    have hmap : (List.range t.bytes).map (fun i => (m.union (bs.At a)).get? (a + BitVec.ofNat 64 i)) =
        bs.map some := by
      apply List.ext_getElem
      · simp [hlen]
      · intro i hi1 hi2
        simp only [List.length_map, List.length_range] at hi1
        simp only [List.getElem_map, List.getElem_range]
        exact hget i hi1
    rw [hmap]
    simpa using List.mapM_pure (m := Option) (f := id) (l := bs)
  have hloadInt : (storeMem m t a v).loadInt a t.bytes = some (Int.ofBytes bs) := by
    simp [Mem.loadInt, hloadBytes]
  simp only [loadVal, hloadInt, Option.bind_some]
  have hbv : BitVec.ofInt (8 * t.bytes) (Int.ofBytes bs) = (toBits t v).setWidth (8 * t.bytes) :=
    BitVec.ofInt_ofBytes_toBytes (8 * t.bytes) t.bytes rfl _
  cases t with
  | bool =>
    cases v
    · have hi0 : Int.ofBytes bs = 0 := by dsimp only [bs, toBits, Ty.bytes, Ty.size]; decide
      simp [hi0]
    · have hi1 : Int.ofBytes bs = 1 := by dsimp only [bs, toBits, Ty.bytes, Ty.size]; decide
      simp [hi1]
  | bits _ =>
    simp only [Option.some.injEq]
    rw [ofInt_setWidth_eq (.bits _) (Int.ofBytes bs), hbv, setWidth_bytes_size, ofBits_toBits]
  | float _ =>
    simp only [Option.some.injEq]
    rw [ofInt_setWidth_eq (.float _) (Int.ofBytes bs), hbv, setWidth_bytes_size, ofBits_toBits]
  | pair _ _ =>
    simp only [Option.some.injEq]
    rw [ofInt_setWidth_eq (.pair _ _) (Int.ofBytes bs), hbv, setWidth_bytes_size, ofBits_toBits]

private theorem mapM_id_eq_some_mem {α : Type} {xs : List (Option α)} {ys : List α}
    (h : xs.mapM id = some ys) {x : Option α} (hx : x ∈ xs) : x.isSome := by
  induction xs generalizing ys with
  | nil => cases hx
  | cons a as ih =>
    simp only [List.mapM_cons, id_eq, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at h
    rcases h with ⟨y, ha, ys', has, rfl⟩
    rcases List.mem_cons.1 hx with rfl | hx'
    · simp [ha]
    · exact ih has hx'

private theorem mapM_id_isSome {α : Type} : ∀ (xs : List (Option α)),
    (∀ x ∈ xs, x.isSome) → ∃ ys, xs.mapM id = some ys
  | [], _ => ⟨[], rfl⟩
  | a :: as, h => by
    have ha := h a List.mem_cons_self
    rcases Option.isSome_iff_exists.1 ha with ⟨v, rfl⟩
    obtain ⟨vs, hvs⟩ := mapM_id_isSome as (fun x hx => h x (List.mem_cons_of_mem _ hx))
    exact ⟨v :: vs, by simp [hvs]⟩

/-- If any byte in `[a, a + n)` is unmapped, `loadBytes` returns `none`. -/
theorem loadBytes_eq_none_of_unmapped {w : Nat} (m : Mem w) (a : BitVec w) (n : Nat)
    (h : ∃ i < n, m.get? (a + BitVec.ofNat w i) = none) :
    m.loadBytes a n = none := by
  rcases h with ⟨i, hi, hnone⟩
  cases hres : m.loadBytes a n with
  | none => rfl
  | some bs =>
    have hs := mapM_id_eq_some_mem hres (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩)
    rw [hnone] at hs
    cases hs

/-- Loading fails if any byte in `[a, a + t.bytes)` is unmapped (partial-overlap UB). -/
theorem loadVal_of_unmapped (m : Mem 64) (t : Ty) (a : BitVec 64)
    (h : ∃ i < t.bytes, m.get? (a + BitVec.ofNat 64 i) = none) :
    loadVal m t a = none := by
  simp only [loadVal, Mem.loadInt, loadBytes_eq_none_of_unmapped m a t.bytes h, Option.map_none,
    Option.bind_none]

/-- Loading `.bool` from a byte outside `{0, 1}` fails (`none`, i.e. UB). -/
theorem loadVal_bool_invalid (m : Mem 64) (a : BitVec 64) (b : UInt8)
    (hget : m.get? a = some b) (hgt : 1 < b.toNat) :
    loadVal m .bool a = none := by
  have hload : m.loadInt a Ty.bool.bytes = some (b.toNat : Int) := by
    rw [Std.ExtHashMap.get?_eq_getElem?] at hget
    simp [Ty.bytes, Ty.size, Mem.loadInt, Mem.loadBytes, List.range_succ, hget, Int.ofBytes]
  simp only [loadVal, hload, Option.bind_some]
  have h0 : ((b.toNat : Int) == 0) = false := beq_false_of_ne (by omega)
  have h1 : ((b.toNat : Int) == 1) = false := beq_false_of_ne (by omega)
  simp [h0, h1]

/-- Storing fails (`¬ storeOk`) if any byte in `[a, a + t.bytes)` is unmapped. -/
theorem not_storeOk_of_unmapped (m : Mem 64) (t : Ty) (a : BitVec 64)
    (h : ∃ i < t.bytes, m.get? (a + BitVec.ofNat 64 i) = none) :
    ¬ storeOk m t a := by
  rintro ⟨i, hi⟩
  simp only [Mem.loadInt, loadBytes_eq_none_of_unmapped m a t.bytes h, Option.map_none] at hi
  cases hi

/-- Storing to `[a, a + na)` leaves `loadBytes` at disjoint `[b, b + nb)` unchanged. -/
theorem loadBytes_storeInt_disjoint (m : Mem 64) (a b : BitVec 64) (na nb : Nat) (v : Int)
    (hdisj : ∀ i j, i < na → j < nb → b + BitVec.ofNat 64 j ≠ a + BitVec.ofNat 64 i) :
    (m.storeInt a na v).loadBytes b nb = m.loadBytes b nb := by
  simp only [Mem.loadBytes, Mem.storeInt, Mem.storeBytes]
  congr 1
  apply List.map_congr_left
  intro j hj
  rw [List.mem_range] at hj
  have hnotmem : b + BitVec.ofNat 64 j ∉ (Int.toBytes na v).At a := by
    rw [mem_At_iff, Int.toBytes_length]
    rintro ⟨i, hi, heq⟩
    exact hdisj i j hi hj heq
  have hnone : ((Int.toBytes na v).At a)[b + BitVec.ofNat 64 j]? = none :=
    Std.ExtHashMap.getElem?_eq_none hnotmem
  rw [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.get?_eq_getElem?,
    Std.ExtHashMap.union_eq, Std.ExtHashMap.getElem?_union, hnone]
  cases m[b + BitVec.ofNat 64 j]? <;> rfl

/-- Disjoint-address frame preservation: `storeMem` at `a` preserves `loadVal` at `b`. -/
theorem loadVal_storeMem_disjoint (m : Mem 64) (t u : Ty) (a b : BitVec 64) (v : Val t)
    (hdisj : ∀ i j, i < t.bytes → j < u.bytes → b + BitVec.ofNat 64 j ≠ a + BitVec.ofNat 64 i) :
    loadVal (storeMem m t a v) u b = loadVal m u b := by
  simp only [loadVal, storeMem, Mem.loadInt, loadBytes_storeInt_disjoint m a b t.bytes u.bytes _ hdisj]

/-- Disjoint-address preservation of `storeOk` across `storeMem`. -/
theorem storeOk_storeMem_disjoint (m : Mem 64) (t u : Ty) (a b : BitVec 64) (v : Val t)
    (hdisj : ∀ i j, i < t.bytes → j < u.bytes → b + BitVec.ofNat 64 j ≠ a + BitVec.ofNat 64 i) :
    storeOk (storeMem m t a v) u b ↔ storeOk m u b := by
  simp only [storeOk, storeMem, Mem.loadInt, loadBytes_storeInt_disjoint m a b t.bytes u.bytes _ hdisj]

/-- Storing never unmaps bytes: `storeOk` is preserved across any `storeMem`. -/
theorem storeOk_storeMem (m : Mem 64) (t u : Ty) (a b : BitVec 64) (v : Val t)
    (hok : storeOk m u b) : storeOk (storeMem m t a v) u b := by
  rcases hok with ⟨k, hk⟩
  simp only [Mem.loadInt, Option.map_eq_some_iff] at hk
  rcases hk with ⟨bs, hbs, _⟩
  have hsome : ∀ x ∈ (List.range u.bytes).map (fun j =>
      (storeMem m t a v).get? (b + BitVec.ofNat 64 j)), x.isSome := by
    intro x hx
    rw [List.mem_map] at hx
    rcases hx with ⟨j, hj, rfl⟩
    have hmj := mapM_id_eq_some_mem hbs (List.mem_map.2 ⟨j, hj, rfl⟩)
    rcases Option.isSome_iff_exists.1 hmj with ⟨byte, hbyte⟩
    simp only [storeMem, Mem.storeInt, Mem.storeBytes, Std.ExtHashMap.get?_eq_getElem?,
      Std.ExtHashMap.union_eq, Std.ExtHashMap.getElem?_union] at hbyte ⊢
    rw [hbyte]
    cases ((Int.toBytes t.bytes ((toBits t v).setWidth (8 * t.bytes)).toInt).At a)[b + BitVec.ofNat 64 j]? <;>
      simp
  obtain ⟨bs', hbs'⟩ := mapM_id_isSome _ hsome
  refine ⟨Int.ofBytes bs', ?_⟩
  simp only [Mem.loadInt, Mem.loadBytes, hbs', Option.map_some]

end LeanQbe.T
