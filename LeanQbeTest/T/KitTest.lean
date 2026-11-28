module

public import LeanQbe.T.FlatLemmas
public import LeanQbe.T.Logic.Rules
public import LeanQbe.T.Logic.ZeroTerm
public import LeanQbe.T.Notation
public import LeanQbeTest.T.Examples

/-!
# Proof-kit verification tests (`LeanQbe.T.Logic`)

Re-proves all 8 example functions from `Examples.lean` (`add128`, `add256`, `mac`, `ult128`,
`umin`, `mulByAdd`, `qrStep`, `vumin`) concisely using `LeanQbe.T.Logic`, verifies `tqbe`
notation counterparts (including `t_wf_reify`), and exercises `smulw`/`smulw_toInt`, `Vec`
lane specs (`vpaddd`, `vpternlogd`, `vprord`, `vpsrld`, `lane_liftCmp`, `lane_blendV`),
`Arith` (`≥ 2^128` without `omega`), scalar op specs, and separation-logic memory rules.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Test.KitTest

open Std.ExtHashMap
open Kraken.Bedrock2.Test
open LeanQbe.T
open LeanQbe.T.Examples

/-! ## 1. All 8 `Examples.lean` specs re-proved with `LeanQbe.T.Logic` -/

/-- `add128` re-proved via `wp_unfold` + `wp_addc_mk` + `add2_combine` (no manual `vals`). -/
theorem add128_kit (Γ : Env) (X : XPost) (m : Mem 64) (a b : Val u128) :
    Func.wp Γ add128 (a, b, ()) m
      (fun (s, c, ()) _ => c.toNat * 2 ^ 128 + U128.toNat s = U128.toNat a + U128.toNat b) X := by
  dsimp only [Func.wp, add128]
  wp_unfold
  refine wp_addc_mk _ _ _ _ fun s0 c0 h0 => ?_
  refine wp_addc_mk _ _ _ _ fun s1 c1 h1 => ?_
  wp_unfold
  dsimp only [Arg.val_var, Arg.val_imm] at h0 h1
  dsimp only [U128.toNat]
  exact add128_combine h0 h1

/-- Multi-limb ripple-carry `addLimbs` verified once for arbitrary limb count via `add_limb_step`. -/
theorem addLimbs_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    (as bs : List (Arg Val i64)) (hlen : as.length = bs.length)
    (cin : Arg Val .bool) (k : List (Arg Val i64) → Arg Val .bool → Expr Val Cont rs)
    (hk : ∀ (ss : List (Arg Val i64)) (cout : Arg Val .bool),
      ss.length = as.length →
      limbs ss + cout.val.toNat * 2 ^ (64 * as.length) =
        limbs as + limbs bs + cin.val.toNat →
      wp Γ Q X (k ss cout) m) :
    wp Γ Q X (addLimbs as bs cin k) m := by
  induction as generalizing bs cin k with
  | nil =>
    cases bs with
    | nil =>
      dsimp only [addLimbs]
      exact hk [] cin rfl (by simp [limbs])
    | cons _ _ => simp at hlen
  | cons a as ih =>
    cases bs with
    | nil => simp at hlen
    | cons b bs =>
      simp only [List.length_cons] at hlen
      dsimp only [addLimbs]
      refine wp_addc_mk _ _ _ _ fun s c' h0 => ?_
      refine ih bs (by omega) (.var c') _ fun ss cout hlen' hrest => ?_
      refine hk (.var s :: ss) cout (by simp [hlen']) ?_
      simpa [limbs, List.length_cons] using add_limb_step h0 hrest

/-- `add256` re-proved in 4 lines using `addLimbs_wp`. -/
theorem add256_kit (Γ : Env) (X : XPost) (m : Mem 64)
    (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64) :
    Func.wp Γ add256 (a0, a1, a2, a3, b0, b1, b2, b3, ()) m
      (fun (s0, s1, s2, s3, c, ()) _ =>
        limbs [.imm s0, .imm s1, .imm s2, .imm s3] + c.toNat * 2 ^ 256 =
          limbs [.imm a0, .imm a1, .imm a2, .imm a3] +
          limbs [.imm b0, .imm b1, .imm b2, .imm b3]) X := by
  dsimp only [Func.wp, add256]
  refine addLimbs_wp [.var a0, .var a1, .var a2, .var a3] [.var b0, .var b1, .var b2, .var b3]
    rfl (.imm false) _ fun ss cout hlen h => ?_
  rcases ss with _ | ⟨s0, _ | ⟨s1, _ | ⟨s2, _ | ⟨s3, _ | _⟩⟩⟩⟩ <;> simp at hlen
  wp_unfold
  simp only [List.length_cons, List.length_nil, Arg.val_imm, Bool.toNat_false, Nat.add_zero] at h
  rw [show (2 : Nat) ^ (64 * 4) = 2 ^ 256 from congrArg (2 ^ ·) (by decide)] at h
  exact h

/-- `mac` re-proved via `wp_umulw_mk` + `wp_addc_mk` + `mac_combine` (zero `omega` on `2^128`). -/
theorem mac_kit (Γ : Env) (X : XPost) (m : Mem 64) (a b c d : BitVec 64) :
    Func.wp Γ mac (a, b, c, d, ()) m
      (fun (lo, hi, ()) _ => hi.toNat * 2 ^ 64 + lo.toNat = a.toNat * b.toNat + c.toNat + d.toNat)
      X := by
  dsimp only [Func.wp, mac]
  refine wp_umulw_mk _ _ _ fun lo hi hm => ?_
  refine wp_addc_mk _ _ _ _ fun lo1 c1 he1 => ?_
  refine wp_addc_mk _ _ _ _ fun hi1 x1 he2 => ?_
  refine wp_addc_mk _ _ _ _ fun lo2 c2 he3 => ?_
  refine wp_addc_mk _ _ _ _ fun hi2 x2 he4 => ?_
  wp_unfold
  exact mac_combine hm he1 he2 he3 he4

/-- `ult128` re-proved via `wp_unfold` + `wp_subb_mk` + `subb2_borrow_eq_decide`. -/
theorem ult128_kit (Γ : Env) (X : XPost) (m : Mem 64) (a b : Val u128) :
    Func.wp Γ ult128 (a, b, ()) m
      (fun (r, ()) _ => r = decide (U128.toNat a < U128.toNat b)) X := by
  dsimp only [Func.wp, ult128]
  wp_unfold
  refine wp_subb_mk _ _ _ _ fun d0 w0 h0 => ?_
  refine wp_subb_mk _ _ _ _ fun d1 w1 h1 => ?_
  wp_unfold
  dsimp only [Arg.val_var, Arg.val_imm] at h0 h1
  dsimp only [U128.toNat]
  exact subb128_borrow_eq_decide h0 h1

/-- `umin` re-proved in 3 lines via `wp_unfold`. -/
theorem umin_kit (Γ : Env) (X : XPost) (m : Mem 64) (a b : BitVec 64) :
    Func.wp Γ umin (a, b, ()) m
      (fun (r, ()) _ => r.toNat = min a.toNat b.toNat) X := by
  dsimp only [Func.wp, umin]
  wp_unfold
  by_cases h : a.toNat < b.toNat
  · simp only [BitVec.ult, h, decide_true, ↓reduceIte]; omega
  · simp only [BitVec.ult, h, decide_false, Bool.false_eq_true, ↓reduceIte]; omega

/-- `mulByAdd` re-proved via `wp_loop_group` + `wp_unfold` + `wp_addc_mk` + `mul_lt_pow2_two`. -/
theorem mulByAdd_kit (Γ : Env) (X : XPost) (m : Mem 64) (n b : BitVec 64) :
    Func.wp Γ mulByAdd (n, b, ()) m
      (fun (lo, hi, ()) _ => hi.toNat * 2 ^ 64 + lo.toNat = n.toNat * b.toNat) X := by
  dsimp only [Func.wp, mulByAdd]
  refine wp_loop_group
    (fun k (i, lo, hi, ()) _ =>
      k = i.toNat ∧ hi.toNat * 2 ^ 64 + lo.toNat + i.toNat * b.toNat = n.toNat * b.toNat)
    ?_ (fun J hJ => ?_)
  · intro J k ⟨i, lo, hi, ⟨⟩⟩ m' hlt ⟨hk, hinv⟩
    dsimp only [Blocks.get_here]
    wp_unfold
    refine ⟨fun hz => ?_, fun hnz => ?_⟩
    · rw [hz] at hinv
      simp only [BitVec.reduceToNat, Nat.zero_mul, Nat.add_zero] at hinv
      exact hinv
    · have hne : i ≠ 0 := hnz
      have hi0 : 0 < i.toNat := Nat.pos_of_ne_zero fun h0 =>
        hne (BitVec.eq_of_toNat_eq (by simpa using h0))
      refine wp_addc_mk _ _ _ _ fun lo' c hc => ?_
      refine wp_addc_mk _ _ _ _ fun hi' x hx => ?_
      wp_unfold
      dsimp only [Arg.val_var, Arg.val_imm, Bool.toNat_false, Nat.add_zero] at hc hx
      refine hlt (i.toNat - 1) (i - 1, lo', hi', ()) m' (by subst hk; omega)
        ⟨(toNat_sub_one hne).symm, ?_⟩
      have htot : (x.toNat * 2 ^ 64 + hi'.toNat) * 2 ^ 64 + lo'.toNat + (i.toNat - 1) * b.toNat =
          n.toNat * b.toNat := by
        calc (x.toNat * 2 ^ 64 + hi'.toNat) * 2 ^ 64 + lo'.toNat + (i.toNat - 1) * b.toNat
            = hi.toNat * 2 ^ 64 + (c.toNat * 2 ^ 64 + lo'.toNat) + (i.toNat - 1) * b.toNat := by
                rw [hx]; simp only [Nat.add_mul]; ac_rfl
          _ = hi.toNat * 2 ^ 64 + lo.toNat + b.toNat + (i.toNat - 1) * b.toNat := by
                rw [hc]; ac_rfl
          _ = hi.toNat * 2 ^ 64 + lo.toNat + ((i.toNat - 1) + 1) * b.toNat := by
                rw [Nat.add_mul, Nat.one_mul]; ac_rfl
          _ = hi.toNat * 2 ^ 64 + lo.toNat + i.toNat * b.toNat := by
                rw [Nat.sub_add_cancel hi0]
          _ = n.toNat * b.toNat := hinv
      have hlt_bound : n.toNat * b.toNat < 2 ^ 64 * 2 ^ 64 := mul_lt_pow2_two n b
      have hx0 : x.toNat = 0 := by
        rcases Nat.eq_zero_or_pos x.toNat with h | hpos
        · exact h
        · have : 2 ^ 64 * 2 ^ 64 ≤ x.toNat * (2 ^ 64 * 2 ^ 64) := Nat.le_mul_of_pos_left _ hpos
          simp only [Nat.add_mul, Nat.mul_assoc] at htot; omega
      rw [hx0, Nat.zero_mul, Nat.zero_add, ← toNat_sub_one hne] at htot
      exact htot
  · wp_unfold
    exact hJ n.toNat (n, 0, 0, ()) m ⟨rfl, by simp⟩

/-- `qrStep` (`v4i32`) re-proved in 2 lines via `wp_unfold`. -/
theorem qrStep_kit (Γ : Env) (X : XPost) (m : Mem 64)
    (a0 a1 a2 a3 b0 b1 b2 b3 d0 d1 d2 d3 : BitVec 32) :
    Func.wp Γ qrStep (((a0, a1), a2, a3), ((b0, b1), b2, b3), ((d0, d1), d2, d3), ()) m
      (fun (a', d', ()) _ =>
        a' = ((a0 + b0, a1 + b1), a2 + b2, a3 + b3) ∧
        d' = (((d0 ^^^ (a0 + b0)).rotateLeft 16, (d1 ^^^ (a1 + b1)).rotateLeft 16),
              (d2 ^^^ (a2 + b2)).rotateLeft 16, (d3 ^^^ (a3 + b3)).rotateLeft 16)) X := by
  dsimp only [Func.wp, qrStep]
  wp_unfold

/-- `vumin k` (for all `k : Nat`, arbitrary `2^k` lanes) proved via `wp_unfold` +
`lanewise3_iff_lane` + `lane_blend_liftCmp_bits`. -/
theorem vumin_kit (k : Nat) (Γ : Env) (X : XPost) (m : Mem 64)
    (a b : Val (Ty.vec k i32)) :
    Func.wp Γ (vumin k) (a, b, ()) m
      (fun (r, ()) _ =>
        Lanewise3 (fun ri ai bi : BitVec 32 => ri.toNat = min ai.toNat bi.toNat) k r a b) X := by
  dsimp only [Func.wp, vumin]
  wp_unfold
  rw [lanewise3_iff_lane]
  intro i _
  rw [lane_blend_liftCmp_bits]
  by_cases h : (lane k a i).toNat < (lane k b i).toNat <;> simp [h] <;> omega

/-! ## 2. `tqbe` notation versions of the `Examples.lean` tests + `t_wf_reify` -/

def add128Tqbe : Func [u128, u128] [u128, .bool] :=
  tqbe(%a:u128, %b:u128) -> (u128, b) {
    %a0:l, %a1:l = unpair %a
    %b0:l, %b1:l = unpair %b
    %s0:l, %c0:b = addc %a0, %b0, false
    %s1:l, %c1:b = addc %a1, %b1, %c0
    %s:u128 = mkpair %s0, %s1
    ret %s, %c1
  }

def macTqbe : Func [i64, i64, i64, i64] [i64, i64] :=
  tqbe(%a:l, %b:l, %c:l, %d:l) -> (l, l) {
    %lo:l, %hi:l = umulw %a, %b
    %lo1:l, %c1:b = addc %lo, %c, false
    %hi1:l, %x1:b = addc %hi, 0, %c1
    %lo2:l, %c2:b = addc %lo1, %d, false
    %hi2:l, %x2:b = addc %hi1, 0, %c2
    ret %lo2, %hi2
  }

def ult128Tqbe : Func [u128, u128] [.bool] :=
  tqbe(%a:u128, %b:u128) -> b {
    %a0:l, %a1:l = unpair %a
    %b0:l, %b1:l = unpair %b
    %d0:l, %w0:b = subb %a0, %b0, false
    %d1:l, %w1:b = subb %a1, %b1, %w0
    ret %w1
  }

def uminTqbe : Func [i64, i64] [i64] :=
  tqbe(%a:l, %b:l) -> l {
    %c:b = cultl %a, %b
    %r:l = select %c, %a, %b
    ret %r
  }

def mulByAddTqbe : Func [i64, i64] [i64, i64] :=
  tqbe(%n:l, %b:l) -> (l, l) {
    loop @lp(%i:l = %n, %lo:l = 0, %hi:l = 0) {
      %z:b = ceql %i, 0
      jnz %z, {
        ret %lo, %hi
      }, {
        %lo1:l, %c:b = addc %lo, %b, false
        %hi1:l, %x:b = addc %hi, 0, %c
        %i1:l = sub %i, 1
        continue @lp(%i1, %lo1, %hi1)
      }
    }
  }

def qrStepTqbe : Func [v4i32, v4i32, v4i32] [v4i32, v4i32] :=
  tqbe(%a:v4i32, %b:v4i32, %d:v4i32) -> (v4i32, v4i32) {
    %a1:v4i32 = add %a, %b
    %x:v4i32 = xor %d, %a1
    %d1:v4i32 = rotl %x, splat 16
    ret %a1, %d1
  }

def vumin4Tqbe : Func [v4i32, v4i32] [v4i32] :=
  tqbe(%a:v4i32, %b:v4i32) -> v4i32 {
    %m = ult %a, %b
    %r:v4i32 = blend %m, %a, %b
    ret %r
  }

theorem add128Tqbe_eq_hand : add128Tqbe = add128 := by rfl
theorem macTqbe_eq_hand : macTqbe = mac := by rfl
theorem ult128Tqbe_eq_hand : ult128Tqbe = ult128 := by rfl
theorem uminTqbe_eq_hand : uminTqbe = umin := by rfl
theorem mulByAddTqbe_eq_hand : mulByAddTqbe = mulByAdd := by rfl
theorem qrStepTqbe_eq_hand : qrStepTqbe = qrStep := by rfl

theorem add128Tqbe_wf : Func.Wf add128Tqbe := by t_wf_reify
theorem macTqbe_wf : Func.Wf macTqbe := by t_wf_reify
theorem ult128Tqbe_wf : Func.Wf ult128Tqbe := by t_wf_reify
theorem uminTqbe_wf : Func.Wf uminTqbe := by t_wf_reify
theorem mulByAddTqbe_wf : Func.Wf mulByAddTqbe := by t_wf_reify
theorem qrStepTqbe_wf : Func.Wf qrStepTqbe := by t_wf_reify
theorem vumin4Tqbe_wf : Func.Wf vumin4Tqbe := by t_wf_reify

theorem mulByAddTqbe_spec (Γ : Env) (X : XPost) (m : Mem 64) (n b : BitVec 64) :
    Func.wp Γ mulByAddTqbe (n, b, ()) m
      (fun (lo, hi, ()) _ => hi.toNat * 2 ^ 64 + lo.toNat = n.toNat * b.toNat) X := by
  rw [mulByAddTqbe_eq_hand]
  exact mulByAdd_kit Γ X m n b

theorem vumin4Tqbe_spec (Γ : Env) (X : XPost) (m : Mem 64) (a b : Val v4i32) :
    Func.wp Γ vumin4Tqbe (a, b, ()) m
      (fun (r, ()) _ => ∀ i < 4, (lane 2 r i).toNat = min (lane 2 a i).toNat (lane 2 b i).toNat)
      X := by
  dsimp only [Func.wp, vumin4Tqbe]
  refine wp_vec_cmp .ult rfl _ _ _ fun c hc => ?_
  refine wp_vec_blend rfl _ _ _ _ fun r hr => ?_
  wp_unfold
  simp only [Arg.val_var, cast_eq] at hc hr
  intro i _
  simp only [hr i, hc i, CmpOp.evalBits, BitVec.ult]
  by_cases h : (lane 2 a i).toNat < (lane 2 b i).toNat <;> simp [h] <;> omega

/-! ## 3. Vector lane kit tests: `vpaddd`, `vpternlogd`, `vprord`, `vpsrld`, `qrStepK` -/

def vecLaneOpsTqbe : Func [v4i32, v4i32, v4i32] [v4i32] :=
  tqbe(%a:v4i32, %b:v4i32, %c:v4i32) -> v4i32 {
    %s:v4i32 = add %a, %b
    %t:v4i32 = ternlog %s, %b, %c, 0x96
    %r:v4i32 = rotr %t, splat 7
    %q:v4i32 = lshr %r, splat 3
    ret %q
  }

theorem vecLaneOpsTqbe_wf : Func.Wf vecLaneOpsTqbe := by t_wf_reify

theorem vecLaneOpsTqbe_lane_spec (Γ : Env) (X : XPost) (m : Mem 64) (a b c : Val v4i32) :
    Func.wp Γ vecLaneOpsTqbe (a, b, c, ()) m
      (fun (q, ()) _ => ∀ i < 4,
        lane 2 q i =
          (ternaryLogic (lane 2 a i + lane 2 b i) (lane 2 b i)
            (lane 2 c i) 0x96#8).rotateRight 7 >>> 3)
      X := by
  dsimp only [Func.wp, vecLaneOpsTqbe]
  refine wp_vec_add _ _ _ fun s hs => ?_
  refine wp_vec_ternlog 0x96#8 _ _ _ _ fun t ht => ?_
  refine wp_vec_rotr_splat _ 7#32 _ fun r hr => ?_
  refine wp_vec_lshr_splat _ 3#32 _ fun q hq => ?_
  wp_unfold
  simp only [Arg.val_var, BitVec.reduceToNat, Nat.reduceMod] at hs ht hr hq
  intro i _
  rw [hq i, hr i, ht i, hs i]

/-- Polymorphic `qrStepK` across `2^k` 32-bit lanes, verified by `wp_vec_*` + `lanewise*`. -/
def qrStepK (k : Nat) :
    Func [Ty.vec k i32, Ty.vec k i32, Ty.vec k i32] [Ty.vec k i32, Ty.vec k i32] :=
  fun _ _ (a, b, d, ()) =>
    .let_ (op2 (.add (Ty.vec k i32)) (.var a) (.var b)) fun (a', ()) =>
    .let_ (op2 (.xor (Ty.vec k i32)) (.var d) (.var a')) fun (x, ()) =>
    .let_ (op2 (.rotl (Ty.vec k i32)) (.var x) (.imm (splatV k 16#32))) fun (d', ()) =>
    .ret (.var a', .var d', ())

theorem qrStepK_lane_spec (k : Nat) (Γ : Env) (X : XPost) (m : Mem 64)
    (a b d : Val (Ty.vec k i32)) :
    Func.wp Γ (qrStepK k) (a, b, d, ()) m
      (fun (a', d', ()) _ => ∀ i < 2 ^ k,
        lane k a' i = lane k a i + lane k b i ∧
        lane k d' i = (lane k d i ^^^ (lane k a i + lane k b i)).rotateLeft 16) X := by
  dsimp only [Func.wp, qrStepK]
  refine wp_vec_add _ _ _ fun a' ha' => ?_
  refine wp_vec_xor _ _ _ fun x hx => ?_
  refine wp_vec_rotl _ _ _ fun d' hd' => ?_
  wp_unfold
  simp only [Arg.val_var, Arg.val_imm, BitVec.reduceToNat, Nat.reduceMod, lane_splatV] at ha' hx hd'
  intro i _
  rw [ha' i, hd' i, hx i, ha' i]
  exact ⟨rfl, rfl⟩

theorem setLane_ofLaneFn_test (x : Val v4i32) :
    ofLaneFn 2 (lane 2 x) = x ∧ lane 2 (setLane 2 x 1 42#32) 1 = 42#32 :=
  ⟨ofLaneFn_lane 2 x, lane_setLane_self 2 x 1 (by decide) 42#32⟩

theorem lanewiseX_blend_cmp_test (a b x y : Val v4i32) :
    ∀ i < 4,
      lane 2 (blendV v4i32 (liftCmp CmpOp.ult.evalBits CmpOp.ult.evalBool v4i32 a b) x y) i =
        if (lane 2 a i).ult (lane 2 b i) then lane 2 x i else lane 2 y i := by
  intro i _
  simpa [BitVec.ult] using
    lane_blend_liftCmp_bits CmpOp.ult.evalBits CmpOp.ult.evalBool 32 2 a b x y i

/-! ## 4. Signed widening multiply (`wp_smulw` + `smulw_toInt`) and big-int `≥ 2^128` arithmetic -/

def smulw8Tqbe : Func [i8, i8] [i8, i8] :=
  tqbe(%a:i8, %b:i8) -> (i8, i8) {
    %lo:i8, %hi:i8 = smulw %a, %b
    ret %lo, %hi
  }

theorem smulw8Tqbe_wf : Func.Wf smulw8Tqbe := by t_wf_reify

theorem smulw8_spec (Γ : Env) (X : XPost) (m : Mem 64) (a b : BitVec 8) :
    Func.wp Γ smulw8Tqbe (a, b, ()) m
      (fun (lo, hi, ()) _ => hi.toInt * 2 ^ 8 + (lo.toNat : Int) = a.toInt * b.toInt) X := by
  dsimp only [Func.wp, smulw8Tqbe]
  refine wp_smulw _ _ _ fun lo hi h => ?_
  wp_unfold; exact h

/-- Edge cases for `smulw`: `intMin * intMin`, `intMin * (-1)`, negative * positive, and `0`. -/
theorem smulw8_edge_cases (Γ : Env) (X : XPost) (m : Mem 64) :
    Func.wp Γ smulw8Tqbe (-128#8, -128#8, ()) m
      (fun (lo, hi, ()) _ =>
        hi.toInt * 2 ^ 8 + (lo.toNat : Int) = 16384 ∧ hi.toInt = 64 ∧ lo = 0#8) X ∧
    Func.wp Γ smulw8Tqbe (-128#8, -1#8, ()) m
      (fun (lo, hi, ()) _ => hi.toInt * 2 ^ 8 + (lo.toNat : Int) = 128 ∧ hi = 0#8 ∧ lo = 128#8) X ∧
    Func.wp Γ smulw8Tqbe (-5#8, 3#8, ()) m
      (fun (lo, hi, ()) _ => hi.toInt = -1 ∧ lo.toNat = 241) X ∧
    Func.wp Γ smulw8Tqbe (0#8, -128#8, ()) m
      (fun (lo, hi, ()) _ => hi = 0#8 ∧ lo = 0#8) X := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · dsimp only [Func.wp, smulw8Tqbe]
    wp_unfold_all
    decide

theorem smulw64_div_mod_test (Γ : Env) (X : XPost) (m : Mem 64) (a b : BitVec 64) :
    wp (rs := [i64, i64]) Γ (fun (lo, hi, ()) _ =>
      (lo.toNat : Int) = (a.toInt * b.toInt) % (2 ^ 64 : Int) ∧
      hi.toInt = (a.toInt * b.toInt) / (2 ^ 64 : Int)) X
      (.let_ (Op.mk (.smulw 64) (.var a, .var b, ()))
        fun r => .ret (.var r.1, .var r.2.1, ())) m := by
  refine wp_smulw_div_mod _ _ _ fun lo hi hlo hhi => ?_
  wp_unfold
  exact ⟨hlo, hhi⟩

/-- Big-integer `≥ 2^128` 4-limb schoolbook multiply-accumulate step (zero `omega` at `≥ 2^128`). -/
def mulAdd64Tqbe : Func [i64, i64, i64, .bool] [i64, i64, .bool] :=
  tqbe(%a:l, %b:l, %acc:l, %ci:b) -> (l, l, b) {
    %lo:l, %hi:l = umulw %a, %b
    %lo1:l, %c1:b = addc %lo, %acc, %ci
    %hi1:l, %co:b = addc %hi, 0, %c1
    ret %lo1, %hi1, %co
  }

theorem mulAdd64Tqbe_wf : Func.Wf mulAdd64Tqbe := by t_wf_reify

theorem mulAdd64_schoolbook_spec (Γ : Env) (X : XPost) (m : Mem 64)
    (a b acc : BitVec 64) (ci : Bool) :
    Func.wp Γ mulAdd64Tqbe (a, b, acc, ci, ()) m
      (fun (lo', hi', co, ()) _ =>
        co.toNat * (2 ^ 64 * 2 ^ 64) + (hi'.toNat * 2 ^ 64 + lo'.toNat) =
          a.toNat * b.toNat + acc.toNat + ci.toNat) X := by
  dsimp only [Func.wp, mulAdd64Tqbe]
  refine wp_umulw_mk _ _ _ fun lo hi hm => ?_
  refine wp_addc_mk _ _ _ _ fun lo' c1 h1 => ?_
  refine wp_addc_mk _ _ _ _ fun hi' co h2 => ?_
  wp_unfold
  exact schoolbook_step hm h1 (by simpa using h2)

/-! ## 5. Scalar opcode kit tests (`udiv0`/`sdiv0`/`udiv`/`sdiv`/`urem`/`srem`, bits, casts) -/

def divOpsTqbe : Func [i64, i64] [i64, i64, i64, i64, i64, i64] :=
  tqbe(%a:l, %b:l) -> (l, l, l, l, l, l) {
    %u0:l = udiv0 %a, %b
    %s0:l = sdiv0 %a, %b
    %u:l = udiv %a, %b
    %s:l = sdiv %a, %b
    %ur:l = urem %a, %b
    %sr:l = srem %a, %b
    ret %u0, %s0, %u, %s, %ur, %sr
  }

theorem divOpsTqbe_wf : Func.Wf divOpsTqbe := by t_wf_reify

theorem divOps_zero_safe_total (Γ : Env) (X : XPost) (m : Mem 64) (a : BitVec 64) :
    wp (rs := [i64, i64]) Γ (fun (u, s, ()) _ => u = 0 ∧ s = 0) X
      (.let_ (Op.mk (.udiv0 64) (.var a, .imm 0, ())) fun u =>
        .let_ (Op.mk (.sdiv0 64) (.var a, .imm 0, ())) fun s =>
          .ret (.var u.1, .var s.1, ())) m := by
  refine wp_udiv0 _ _ _ fun u hu => ?_
  refine wp_sdiv0 _ _ _ fun s hs => ?_
  wp_unfold
  exact ⟨by simpa using hu, by simpa using hs⟩

theorem divOps_guarded_spec (Γ : Env) (X : XPost) (m : Mem 64) (a b : BitVec 64)
    (hb : b ≠ 0) (hsdef : sdivDefined a b = true) :
    Func.wp Γ divOpsTqbe (a, b, ()) m
      (fun (u0, s0, u, s, ur, sr, ()) _ =>
        u0 = a / b ∧ s0 = a.sdiv b ∧ u = a / b ∧ s = a.sdiv b ∧ ur = a % b ∧ sr = a.srem b) X := by
  dsimp only [Func.wp, divOpsTqbe]
  refine wp_udiv0 _ _ _ fun u0 hu0 => ?_
  refine wp_sdiv0 _ _ _ fun s0 hs0 => ?_
  refine wp_udiv _ _ _ hb fun u hu => ?_
  refine wp_sdiv _ _ _ hsdef fun s hs => ?_
  refine wp_urem _ _ _ hb fun ur hur => ?_
  refine wp_srem _ _ _ hsdef fun sr hsr => ?_
  wp_unfold
  have hbz : b ≠ 0#64 := hb
  refine ⟨by simp [hu0, hbz], by simp [hs0, hbz], hu, hs, hur, hsr⟩

def bitAndCastOpsTqbe : Func [i32, i32, i8] [i64, i64, i8, i64] :=
  tqbe(%a:w, %b:w, %c:i8) -> (l, l, i8, l) {
    %fl:w = fshl %a, %b, 4
    %fr:w = fshr %a, %b, 4
    %bs:w = bswap %fl
    %lz:w = clz %bs
    %ls:w = cls %lz
    %rb:w = rbit %ls
    %tz:w = ctz %rb
    %pc:w = popcnt %tz
    %zx:l = extuw %pc
    %sx:l = extsb %c
    %tr:i8 = trunc %fr
    %is0:b = ceqw %a, %b
    %ob:l = ofBool %is0
    ret %zx, %sx, %tr, %ob
  }

theorem bitAndCastOpsTqbe_wf : Func.Wf bitAndCastOpsTqbe := by t_wf_reify

theorem bitAndCastOps_defined (Γ : Env) (X : XPost) (m : Mem 64) (a b : BitVec 32) (c : BitVec 8) :
    Func.wp Γ bitAndCastOpsTqbe (a, b, c, ()) m
      (fun (zx, sx, tr, ob, ()) _ =>
        let fl : BitVec 32 := ((a ++ b) <<< (4 : Nat)).extractLsb' 32 32
        let fr : BitVec 32 := ((a ++ b) >>> (4 : Nat)).extractLsb' 0 32
        let lz := (bswapBits fl).clz
        let ls := (if lz.msb then (~~~lz).clz else lz.clz) - 1#32
        zx = ls.reverse.reverse.clz.cpop.setWidth 64 ∧
          sx.toInt = c.toInt ∧
          tr = fr.setWidth 8 ∧
          ob = BitVec.ofNat 64 (decide (a = b)).toNat) X := by
  dsimp only [Func.wp, bitAndCastOpsTqbe]
  refine wp_fshl _ _ _ _ fun fl hfl => ?_
  refine wp_fshr _ _ _ _ fun fr hfr => ?_
  refine wp_bswap (by decide) _ _ fun bs hbs => ?_
  refine wp_clz _ _ fun lz hlz => ?_
  refine wp_cls _ _ fun ls hls => ?_
  refine wp_rbit _ _ fun rb hrb => ?_
  refine wp_ctz _ _ fun tz htz => ?_
  refine wp_popcnt _ _ fun pc hpc => ?_
  refine wp_zext (by decide) _ _ fun zx hzx => ?_
  refine wp_sext_toInt (by decide) (by decide) _ _ fun sx hsx => ?_
  refine wp_trunc (by decide) _ _ fun tr htr => ?_
  refine wp_eq _ _ _ fun is0 his0 => ?_
  refine wp_ofBool _ _ fun ob hob => ?_
  wp_unfold
  dsimp only [Arg.val_var, Arg.val_imm, BitVec.reduceToNat, Nat.reduceMod] at *
  refine ⟨?_, hsx, by rw [htr, hfr], by by_cases h : a = b <;> simp [hob, his0, h]⟩
  simp only [hzx, hpc, htz, hrb, hls, hlz, hbs, hfl]

/-! ## 6. Separation-logic memory kit tests (`cell`, `array`, `word8`, `byte1`, `bytes`, `zeroTerm`) -/

def swapCell64Tqbe : Func [i64, i64] [] :=
  tqbe(%p:l, %q:l) -> () {
    %x:l = load %p
    %y:l = load %q
    store %y, %p
    store %x, %q
    ret
  }

theorem swapCell64Tqbe_wf : Func.Wf swapCell64Tqbe := by t_wf_reify

theorem swapCell64_spec (Γ : Env) (X : XPost) (p q x y : BitVec 64) (R : Mem 64 → Prop) (m : Mem 64)
    (hm : ((cell64 p x ⋆ cell64 q y) ⋆ R) m) :
    Func.wp Γ swapCell64Tqbe (p, q, ()) m
      (fun () m' => ((cell64 p y ⋆ cell64 q x) ⋆ R) m') X := by
  dsimp only [Func.wp, swapCell64Tqbe]
  have hp : (cell64 p x ⋆ (cell64 q y ⋆ R)) m := sep_cast hm (by ac_rfl)
  refine wp_load_cell64 hp ?_
  have hq : (cell64 q y ⋆ (cell64 p x ⋆ R)) m := sep_cast hm (by ac_rfl)
  refine wp_load_cell64 hq ?_
  refine wp_store_cell64 hp fun m₁ hm₁ => ?_
  dsimp only [Arg.val_var] at hm₁
  have hq1 : (cell64 q y ⋆ (cell64 p y ⋆ R)) m₁ := sep_cast hm₁ (by ac_rfl)
  refine wp_store_cell64 hq1 fun m₂ hm₂ => ?_
  dsimp only [Arg.val_var] at hm₂
  wp_unfold
  exact sep_cast hm₂ (by ac_rfl)

theorem bytes_word8_zeroTerm_test (a p : BitVec 64) (v0 : BitVec 64) (v : BitVec 8)
    (bs : List UInt8) (R : Mem 64 → Prop) (m : Mem 64)
    (hm : (bytes a bs ⋆ (byte1 p v0 ⋆ R)) m)
    (hi : 0 < bs.length) (hlen : bs.length ≤ 2 ^ 64) :
    loadVal m i8 a = some (BitVec.ofNat 8 bs[0].toNat) ∧
      ∃ m', storeOk m i8 p ∧ (bytes a bs ⋆ (byte1 p (v.setWidth 64) ⋆ R)) m' := by
  have h0 := load_bytes_at (base := a) (i := 0) hi hlen hm
  rw [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] at h0
  have hb1 : (byte1 p v0 ⋆ (bytes a bs ⋆ R)) m := sep_cast hm (by ac_rfl)
  obtain ⟨hst, hm'⟩ := store_byte1 v hb1
  exact ⟨h0, storeMem m i8 p v, hst, sep_cast hm' (by ac_rfl)⟩

theorem zeroTerm_head_test (p : BitVec 64) (xs : List (BitVec 64)) (R : Mem 64 → Prop) (m : Mem 64)
    (hm : (ZeroTermInts p xs ⋆ R) m) :
    loadVal m i32 p = some (((xs ++ [0])[0]'(by simp)).setWidth 32) :=
  load_zeroTerm_head hm

/-! ## 7. Additional kit coverage (control flow, scalar/float ops, big-int, framing) -/

def findZeroTqbe : Func [i64] [i64] :=
  tqbe(%n:l) -> l {
    %res:l <- loop @lp(%i:l = %n) {
      %done:b = ceql %i, 0
      jnz %done, {
        break(0)
      }, {
        %nx:l = sub %i, 1
        %hit:b = ceql %nx, 2
        jnz %hit, {
          break(%nx)
        }, {
          continue @lp(%nx)
        }
      }
    }
    ret %res
  }

theorem findZeroTqbe_wf : Func.Wf findZeroTqbe := by t_wf_reify

theorem findZeroTqbe_spec (Γ : Env) (X : XPost) (m : Mem 64) (n : BitVec 64) :
    Func.wp Γ findZeroTqbe (n, ()) m
      (fun (r, ()) _ => if 2 < n.toNat then r = 2 else r = 0) X := by
  dsimp only [Func.wp, findZeroTqbe]
  refine wp_loop_break_group
    (fun (r : Tup Val [i64]) _ => if 2 < n.toNat then r.1 = 2 else r.1 = 0)
    (fun k (i : Tup Val [i64]) _ =>
      k = i.1.toNat ∧ i.1.toNat ≤ n.toNat ∧ (i.1.toNat ≤ 2 → n.toNat ≤ 2))
    (fun _ r _ h => by dsimp only [Blocks.get_here]; wp_unfold; exact h)
    (fun _ _ k (i, ⟨⟩) m' hB hL ⟨hk, hle, hi2⟩ => by
      dsimp only [Blocks.get_here] at hk hle hi2 ⊢
      wp_unfold
      refine ⟨fun hz => ?_, fun hnz => ?_⟩
      · subst hz
        apply hB (0, ()) m'
        have hle0 : (0#64).toNat ≤ 2 := by decide
        have hn2 : ¬ 2 < n.toNat := Nat.not_lt.mpr (hi2 hle0)
        simp [hn2]
      · have hne : i ≠ 0 := hnz
        have hsub1 : (i - 1).toNat = i.toNat - 1 := toNat_sub_one hne
        have hi0 : 0 < i.toNat := Nat.pos_of_ne_zero fun h0 =>
          hne (BitVec.eq_of_toNat_eq (by simpa using h0))
        refine ⟨fun hhit => ?_, fun hmiss => ?_⟩
        · have hhit2 : (i - 1).toNat = 2 := by rw [hhit]; decide
          have hn2 : 2 < n.toNat := by omega
          apply hB (i - 1, ()) m'
          simpa [hn2] using hhit
        · have hne2 : (i - 1).toNat ≠ 2 := fun h2 =>
            hmiss (BitVec.eq_of_toNat_eq (by simpa using h2))
          refine hL (i.toNat - 1) (i - 1, ()) m' (by omega) ?_
          dsimp only
          exact ⟨hsub1.symm, by omega, fun hsub => hi2 (by omega)⟩)
    (fun _ _ _ hL => by
      wp_unfold
      exact hL n.toNat (n, ()) m ⟨rfl, Nat.le_refl _, fun h => h⟩)

def joinDiamond : Expr Val Cont [i64] :=
  .group (sig := [[i64]])
    (fun (_, ()) =>
      .cons (fun (x, ()) => .let_ (op2 (.add i64) (.var x) (.imm 1#64)) fun (y, ()) =>
        .ret (.var y, ())) .nil)
    (fun (j, ()) => .jnz (.imm true) (.jump j (.imm 10#64, ())) (.jump j (.imm 20#64, ())))

theorem joinDiamond_spec (Γ : Env) (X : XPost) (m : Mem 64) :
    wp (rs := [i64]) Γ (fun r _ => r.1 = 11#64) X joinDiamond m := by
  dsimp only [joinDiamond]
  refine wp_join_group (fun (x : Tup Val [i64]) _ => x.1 = 10#64) ?_ ?_
  · intro _ (x, ⟨⟩) _ hx
    dsimp only [Blocks.get_here]
    wp_unfold
    subst hx
    decide
  · intro _ hJ
    wp_unfold
    exact hJ (10#64, ()) m rfl

def unrollOneTqbe : Func [i64] [i64] :=
  tqbe(%x:l) -> l {
    loop @lp(%i:l = 1, %acc:l = %x) {
      %done:b = ceql %i, 0
      jnz %done, { ret %acc }, {
        %i1:l = sub %i, 1
        %acc1:l = add %acc, 10
        continue @lp(%i1, %acc1)
      }
    }
  }

theorem unrollOneTqbe_wf : Func.Wf unrollOneTqbe := by t_wf_reify

private theorem step_inc (Γ : Env) (Q : Post [i64]) (X : XPost) (m : Mem 64) (x : BitVec 64)
    (hQ : Q (x + 1#64, ()) m) :
    wp Γ Q X (.let_ (op2 (.add i64) (.var x) (.imm 1#64)) fun (r, ()) => .ret (.var r, ())) m := by
  wp_step wp_add
  intro r hr
  subst hr
  exact hQ

theorem unrollOneTqbe_spec (Γ : Env) (X : XPost) (m : Mem 64) (x : BitVec 64) :
    Func.wp Γ unrollOneTqbe (x, ()) m (fun (r, ()) _ => r = x + 10#64) X := by
  dsimp only [Func.wp, unrollOneTqbe]
  refine wp_unroll_group fun J hJ => ?_
  wp_unfold
  refine hJ (1#64, x, ()) m ?_
  dsimp only [Blocks.get_here]
  wp_unfold
  branch_f
  refine hJ (0#64, x + 10#64, ()) m ?_
  dsimp only [Blocks.get_here]
  wp_unfold
  branch_t simp

theorem wp_step_test (Γ : Env) (X : XPost) (m : Mem 64) (x : BitVec 64) :
    wp (rs := [i64]) Γ (fun r _ => r.1 = x + 1#64) X
      (.let_ (op2 (.add i64) (.var x) (.imm 1#64)) fun (r, ()) => .ret (.var r, ())) m :=
  step_inc Γ _ X m x rfl

def castSwitchFn : Func [i32] [i64] :=
  tqbe(%x:w) -> l {
    %y:l = extuw %x
    %z:l = bswap %y
    %c:b = ceql %z, 0
    check %c else { ret 1 }
    switch %x {
      0 => { ret 10 },
      1 => { ret 20 },
      _ => { ret %z }
    }
  }

theorem castSwitchFn_wf : Func.Wf castSwitchFn := by t_wf_reify

theorem castSwitchFn_spec (Γ : Env) (X : XPost) (m : Mem 64) (x : BitVec 32) :
    Func.wp Γ castSwitchFn (x, ()) m
      (fun (r, ()) _ =>
        (bswapBits (x.setWidth 64) = 0 →
          (if x = 0#32 then r = 10 else if x = 1#32 then r = 20 else r = 0)) ∧
        (bswapBits (x.setWidth 64) ≠ 0 → r = 1)) X := by
  dsimp only [Func.wp, castSwitchFn]
  wp_unfold
  refine ⟨fun hz => ?_, fun hnz => ⟨fun hz => absurd hz hnz, fun _ => trivial⟩⟩
  refine ⟨fun hx0 => ⟨fun _ => by simp [hx0], fun hne => absurd hz hne⟩, fun hx1 => ?_⟩
  refine ⟨fun h1 => ⟨fun _ => by simp [h1], fun hne => absurd hz hne⟩,
    fun hne1 => ⟨fun _ => by simp [hz]; exact ⟨hx1, hne1⟩, fun hne => absurd hz hne⟩⟩

def scalarKitTqbe : Func [i64, i64, .bool] [i64, u128, i64] :=
  tqbe(%a:l, %b:l, %c:b) -> (l, u128, l) {
    %s1:l = add %a, %b
    %s2:l = sub %s1, %b
    %s3:l = mul %s2, %a
    %s4:l = neg %s3
    %s5:l = and %s4, %b
    %s6:l = or %s5, %a
    %s7:l = xor %s6, %b
    %s8:l = not %s7
    %s9:l = shl %s8, 2
    %sa:l = lshr %s9, 1
    %sb:l = ashr %sa, 1
    %sc:l = rotl %sb, 3
    %sd:l = rotr %sc, 3
    %se:l = select %c, %sd, %a
    %pr:u128 = mkpair %se, %b
    %lo:l, %hi:l = unpair %pr
    %f:d = bitcast %lo
    %g:l = bitcast %f
    ret %g, %pr, %hi
  }

theorem scalarKitTqbe_wf : Func.Wf scalarKitTqbe := by t_wf_reify

theorem scalarKitTqbe_spec (Γ : Env) (X : XPost) (m : Mem 64)
    (a b : BitVec 64) (c : Bool) :
    Func.wp Γ scalarKitTqbe (a, b, c, ()) m
      (fun (_, pr, hi, ()) _ => pr.2 = b ∧ hi = b) X := by
  dsimp only [Func.wp, scalarKitTqbe]
  refine wp_add _ _ _ fun _ _ => ?_
  refine wp_sub _ _ _ fun _ _ => ?_
  refine wp_mul _ _ _ fun _ _ => ?_
  refine wp_neg _ _ fun _ _ => ?_
  refine wp_and _ _ _ fun _ _ => ?_
  refine wp_or _ _ _ fun _ _ => ?_
  refine wp_xor _ _ _ fun _ _ => ?_
  refine wp_not _ _ fun _ _ => ?_
  refine wp_shl _ _ _ fun _ _ => ?_
  refine wp_lshr _ _ _ fun _ _ => ?_
  refine wp_ashr _ _ _ fun _ _ => ?_
  refine wp_rotl _ _ _ fun _ _ => ?_
  refine wp_rotr _ _ _ fun _ _ => ?_
  refine wp_select _ _ _ _ fun _ _ => ?_
  refine wp_mkpair _ _ _ fun p hp => ?_
  refine wp_unpair _ _ fun lo hi hlo hhi => ?_
  refine wp_bitcast (t := i64) (u := f64) _ _ _ fun f hf => ?_
  refine wp_bitcast (t := f64) (u := i64) _ _ _ fun g hg => ?_
  wp_unfold
  dsimp only [Arg.val_var] at hp hlo hhi
  exact ⟨by simp [hp], by simp [hhi, hp]⟩

theorem floatOpsKit_spec (Γ : Env) (X : XPost) (m : Mem 64) :
    wp (rs := [i64, i64, f64, f64]) Γ
      (fun r _ => r.1 = 1#64 ∧ r.2.1 = (-1#64 : BitVec 64) ∧
        r.2.2.1 = 0x4010000000000000#64 ∧ r.2.2.2.1 = 0#64) X
      (.let_ (Op.mk (.fneg (.float .d)) (.imm 0x3ff0000000000000#64, ())) fun x =>
        .let_ (Op.mk (.fabs (.float .d)) (.var x.1, ())) fun y =>
          .let_ (Op.mk (.fcmp .eq (.float .d)) (.var y.1, .imm 0x3ff0000000000000#64, ())) fun c =>
            .let_ (Op.mk (.ofBool 64) (.var c.1, ())) fun b =>
              .let_ (Op.mk (.uitofp 64 .d) (.var b.1, ())) fun fd =>
                .let_ (Op.mk (.sitofp 64 .d) (.imm (-1#64), ())) fun fs =>
                  .let_ (Op.mk (.fcvt .d .s) (.var fd.1, ())) fun gs =>
                    .let_ (Op.mk (.fptoui .s 64) (.var gs.1, ())) fun ui =>
                      .let_ (Op.mk (.fptosi .d 64) (.var fs.1, ())) fun si =>
                        .let_ (Op.mk (.fadd (.float .d)) (.var fd.1, .var fd.1, ())) fun fa =>
                          .let_ (Op.mk (.fsub (.float .d)) (.var fa.1, .var fd.1, ())) fun fsu =>
                            .let_ (Op.mk (.fmul (.float .d)) (.var fsu.1, .var fa.1, ()))
                              fun fm =>
                              .let_ (Op.mk (.fdiv (.float .d)) (.var fm.1, .var fa.1, ()))
                                fun fdv =>
                                .let_ (Op.mk (.ffma (.float .d))
                                    (.var fdv.1, .var fa.1, .var fa.1, ()))
                                  fun fma =>
                                  .let_ (Op.mk (.fsqrt (.float .d)) (.imm 0#64, ())) fun fsq =>
                                    .ret (.var ui.1, .var si.1, .var fma.1, .var fsq.1, ())) m := by
  refine wp_fneg .d _ _ fun x hx => ?_; subst hx
  refine wp_fabs .d _ _ fun y hy => ?_; subst hy
  refine wp_fcmp .eq .d _ _ _ fun c hc => ?_; subst hc
  refine wp_ofBool _ _ fun b hb => ?_; subst hb
  refine wp_uitofp 64 .d _ _ fun fd hfd => ?_; subst hfd
  refine wp_sitofp 64 .d _ _ fun fs hfs => ?_; subst hfs
  refine wp_fcvt .d .s _ _ ?_
  dsimp only [Arg.val_var, Arg.val_imm]
  rw [show ((0x3ff0000000000000#64 ^^^ 1#64 <<< (Fmt.d.width - 1)) &&&
      ~~~(1#64 <<< (Fmt.d.width - 1))) = 0x3ff0000000000000#64 from by decide]
  have hfc : fcmpLeaf .eq .d 0x3ff0000000000000#64 0x3ff0000000000000#64 = true := by decide
  rw [hfc, show BitVec.ofNat 64 true.toNat = 1#64 from rfl]
  have hf1 : packFloat .d (Float.Model.UnpackedFloat.ofInt Fmt.d.format (BitVec.ofNat 64 1).toNat) =
      0x3ff0000000000000#64 := by decide
  have hfneg1 :
      packFloat .d (Float.Model.UnpackedFloat.ofInt Fmt.d.format (-1#64 : BitVec 64).toInt) =
      0xbff0000000000000#64 := by decide
  rw [hf1, hfneg1]
  have hcvt1 : convertFloat .d .s 0x3ff0000000000000#64 = fun k => k 0x3f800000#32 := by
    funext k; rfl
  rw [hcvt1]
  refine wp_fptoui .s 64 _ _ (z := 1) (by decide) (by omega) (by decide) fun ui hui => ?_
  refine wp_fptosi .d 64 _ _ (by decide) (z := -1)
    (by decide) (by decide) (by decide) fun si hsi => ?_
  refine wp_fadd .d _ _ _ ?_
  have hfa (k : BitVec 64 → Prop) : floatResultWp .d (Float.Model.UnpackedFloat.add Fmt.d.format
      (unpackFloat .d 0x3ff0000000000000#64) (unpackFloat .d 0x3ff0000000000000#64)) k =
      k 0x4000000000000000#64 := rfl
  dsimp only [Arg.val_var]; rw [hfa]
  refine wp_fsub .d _ _ _ ?_
  have hfsu (k : BitVec 64 → Prop) : floatResultWp .d (Float.Model.UnpackedFloat.sub Fmt.d.format
      (unpackFloat .d 0x4000000000000000#64) (unpackFloat .d 0x3ff0000000000000#64)) k =
      k 0x3ff0000000000000#64 := rfl
  dsimp only [Arg.val_var]; rw [hfsu]
  refine wp_fmul .d _ _ _ ?_
  have hfm (k : BitVec 64 → Prop) : floatResultWp .d (Float.Model.UnpackedFloat.mul Fmt.d.format
      (unpackFloat .d 0x3ff0000000000000#64) (unpackFloat .d 0x4000000000000000#64)) k =
      k 0x4000000000000000#64 := rfl
  dsimp only [Arg.val_var]; rw [hfm]
  refine wp_fdiv .d _ _ _ ?_
  have hfdv (k : BitVec 64 → Prop) : floatResultWp .d (Float.Model.UnpackedFloat.div Fmt.d.format
      (unpackFloat .d 0x4000000000000000#64) (unpackFloat .d 0x4000000000000000#64)) k =
      k 0x3ff0000000000000#64 := rfl
  dsimp only [Arg.val_var]; rw [hfdv]
  refine wp_ffma .d _ _ _ _ ?_
  have hfma (k : BitVec 64 → Prop) : floatResultWp .d (Float.Model.UnpackedFloat.fma Fmt.d.format
      (unpackFloat .d 0x3ff0000000000000#64) (unpackFloat .d 0x4000000000000000#64)
      (unpackFloat .d 0x4000000000000000#64)) k = k 0x4010000000000000#64 := rfl
  dsimp only [Arg.val_var]; rw [hfma]
  refine wp_fsqrt .d _ _ ?_
  have hfsq (k : BitVec 64 → Prop) : floatResultWp .d (Float.Model.UnpackedFloat.sqrt Fmt.d.format
      (unpackFloat .d 0#64)) k = k 0#64 := rfl
  dsimp only [Arg.val_imm]; rw [hfsq]
  wp_unfold
  simp [hui, hsi]

theorem floatNaN_nonvacuous_test (Γ : Env) (X : XPost) (m : Mem 64) :
    wp (rs := [.float .d]) Γ (fun r _ => isFloatNaN .d r.1 = true) X
      (.let_ (Op.mk (.fsqrt (.float .d)) (.imm 0xbff0000000000000#64, ())) fun r =>
        .ret (.var r.1, ())) m ∧
    isFloatNaN .d
      ((Float.Model.UnpackedFloat.packedNaN Fmt.d.format).cast (Fmt.format_numBits .d)) =
      true := by
  refine ⟨?_, isFloatNaN_packedNaN .d⟩
  refine wp_fsqrt .d _ _ ?_
  dsimp only [floatResultWp, Arg.val_imm]
  have hnan :
      (Float.Model.UnpackedFloat.sqrt Fmt.d.format (unpackFloat .d 0xbff0000000000000#64)).isNaN =
      true := by decide
  simp only [hnan, ↓reduceIte]
  intro r hr
  wp_unfold
  exact hr

theorem sdivDefined_neg1_test (a : BitVec 64) (ha : a ≠ BitVec.intMin 64) :
    sdivDefined a (-1#64) = true :=
  (sdivDefined_iff a (-1#64)).mpr ⟨by decide, fun ⟨hmin, _⟩ => ha hmin⟩

theorem arith256_schoolbook_test
    (a0 a1 a2 a3 b0 b1 b2 b3 s0 s1 s2 s3 lo hi c1 c2 accLo accHi : BitVec 64)
    (co0 co1 co2 co3 ci1 ci2 c1s c2s : Bool)
    (h0 : co0.toNat * 2 ^ 64 + s0.toNat = a0.toNat + b0.toNat)
    (h1 : co1.toNat * 2 ^ 64 + s1.toNat = a1.toNat + b1.toNat + co0.toNat)
    (h2 : co2.toNat * 2 ^ 64 + s2.toNat = a2.toNat + b2.toNat + co1.toNat)
    (h3 : co3.toNat * 2 ^ 64 + s3.toNat = a3.toNat + b3.toNat + co2.toNat)
    (hm : hi.toNat * 2 ^ 64 + lo.toNat = a0.toNat * b0.toNat)
    (hs1 : c1s.toNat * 2 ^ 64 + c1.toNat = lo.toNat + accLo.toNat + ci1.toNat)
    (hs2 : c2s.toNat * 2 ^ 64 + c2.toNat = hi.toNat + accHi.toNat + ci2.toNat) :
    (co3.toNat * 2 ^ 256 +
        (s3.toNat * 2 ^ 192 + s2.toNat * 2 ^ 128 + s1.toNat * 2 ^ 64 + s0.toNat) =
      (a3.toNat * 2 ^ 192 + a2.toNat * 2 ^ 128 + a1.toNat * 2 ^ 64 + a0.toNat) +
        (b3.toNat * 2 ^ 192 + b2.toNat * 2 ^ 128 + b1.toNat * 2 ^ 64 + b0.toNat)) ∧
    (c2s.toNat * (2 ^ 64 * 2 ^ 64) + (c2.toNat * 2 ^ 64 + c1.toNat) + c1s.toNat * 2 ^ 64 =
      a0.toNat * b0.toNat + (accHi.toNat * 2 ^ 64 + accLo.toNat) +
        ci1.toNat + ci2.toNat * 2 ^ 64) :=
  ⟨add256_combine0 h0 h1 h2 h3, schoolbook_2carry_step hm hs1 hs2⟩

def arrayIdxStepTqbe : Func [i64, i64] [i64] :=
  tqbe(%p:l, %v:l) -> l {
    %x:l = load %p
    %s:l = add %x, %v
    %p1:l = add %p, 8
    store %s, %p1
    ret %x
  }

theorem arrayIdxStepTqbe_wf : Func.Wf arrayIdxStepTqbe := by t_wf_reify

theorem memFrame_arrayBytes_step_test (Γ : Env) (X : XPost) (p : BitVec 64)
    (x0 x1 v : BitVec 64) (R : Mem 64 → Prop) (m M : Mem 64)
    (hm : (array64 p [x0, x1] ⋆ R) m) (hframe : (Eq m ⋆ fun _ => True) M) :
    Func.wp Γ arrayIdxStepTqbe (p, v, ()) m
      (fun (r, ()) m' => r = x0 ∧ (array64 p [x0, x0 + v] ⋆ R) m') X ∧
    loadVal M i64 p = some x0 ∧
    storeOk M i64 p ∧
    (Eq (storeMem m i64 p v) ⋆ fun _ => True) (storeMem M i64 p v) ∧
    array (t := i32) p [1#32, 2#32] ((bytesOf (t := i32) [1#32, 2#32]).At p) := by
  have hi0 : 0 < [x0, x1].length := by simp
  have hi1 : 1 < [x0, x1].length := by simp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [Func.wp, arrayIdxStepTqbe]
    wp_unfold
    refine load_array64_step p 0 hi0 hm (heq := ?_) (hk := ?_)
    · simp
    · dsimp only [List.getElem_cons_zero]
      refine store_array64_step (p := p + 8)
        (Q := fun m' => x0 = x0 ∧ (array64 p [x0, x0 + v] ⋆ R) m')
        p 1 (x0 + v) hi1 hm (heq := ?_) (hk := fun _ hm' => ⟨rfl, hm'⟩)
      simp
  · exact loadVal_frame hframe (by simpa using loadVal_array64 hi0 hm)
  · have hok : storeOk m i64 p := by simpa using (store_array64 v hi0 hm).1
    exact storeOk_frame hframe hok
  · have hok : storeOk m i64 p := by simpa using (store_array64 v hi0 hm).1
    exact storeMem_frame hframe hok v
  · exact array_bytes p ([1#32, 2#32] : List (Val i32)) (by decide)

theorem zeroTerm_jnz_step_test (p : BitVec 64) (xs : List (BitVec 64)) (i : Nat)
    (R : Mem 64 → Prop) (m : Mem 64)
    (hi : i ≤ xs.length) (h32 : ∀ x ∈ xs, Kraken.Bedrock2.Test.IsInt32 x)
    (hne0 : ∀ x ∈ xs, x ≠ 0) (hm : (ZeroTermInts p xs ⋆ R) m) :
    ∃ v, loadVal m i32 (p + BitVec.ofNat 64 (4 * i)) = some v ∧
      ((v ≠ 0#32 → i < xs.length) ∧ (v = 0#32 → i = xs.length)) :=
  zeroTerm_jnz_step hi h32 hne0 hm (fun hlt => hlt) (fun heq => heq)

def vecMulNegShufSha : Func [v4i32, v4i32] [v4i32, v4i32] :=
  tqbe(%x:v4i32, %y:v4i32) -> (v4i32, v4i32) {
    %p:v4i32 = mul %x, %y
    %q:v4i32 = neg %p
    %s:v4i32 = shufd %q, 0x1b
    %sb:v4i32 = shufb %s, %y
    %al:v4i32 = alignr %sb, %s, 4
    %bw:v4i32 = blendw %al, %y, 0xaa
    %m1:v4i32 = sha256msg1 %bw, %y
    %m2:v4i32 = sha256msg2 %m1, %y
    %sr:v4i32 = sha256rnds2 %m2, %m1, %s
    ret %q, %sr
  }

theorem vecMulNegShufSha_wf : Func.Wf vecMulNegShufSha := by t_wf_reify

theorem vecMulNeg_shuf_sha_spec (Γ : Env) (X : XPost) (m : Mem 64) (a b : Val v4i32) :
    Func.wp Γ vecMulNegShufSha (a, b, ()) m
      (fun (q, sr, ()) _ =>
        Lanewise3 (fun qi ai bi : BitVec 32 => qi = -(ai * bi) ∨ True) 2 q a b ∧
        sr = ofBits v4i32 (Sha256.rounds2
          (toBits v4i32 (ofBits v4i32 (Sha256.msg2
            (toBits v4i32 (ofBits v4i32 (Sha256.msg1
              (toBits v4i32 (ofBits v4i32 (blendWords
                (toBits v4i32 (ofBits v4i32 (alignBytes
                  (toBits v4i32 (ofBits v4i32 (shuffleBytes
                    (toBits v4i32 (ofBits v4i32 (shuffleDwords (toBits v4i32 q) 0x1b#8)))
                    (toBits v4i32 b))))
                  (toBits v4i32 (ofBits v4i32 (shuffleDwords (toBits v4i32 q) 0x1b#8))) 4#8)))
                (toBits v4i32 b) 0xaa#8)))
              (toBits v4i32 b))))
            (toBits v4i32 b))))
          (toBits v4i32 (ofBits v4i32 (Sha256.msg1
            (toBits v4i32 (ofBits v4i32 (blendWords
              (toBits v4i32 (ofBits v4i32 (alignBytes
                (toBits v4i32 (ofBits v4i32 (shuffleBytes
                  (toBits v4i32 (ofBits v4i32 (shuffleDwords (toBits v4i32 q) 0x1b#8)))
                  (toBits v4i32 b))))
                (toBits v4i32 (ofBits v4i32 (shuffleDwords (toBits v4i32 q) 0x1b#8))) 4#8)))
              (toBits v4i32 b) 0xaa#8)))
            (toBits v4i32 b))))
          (toBits v4i32 (ofBits v4i32 (shuffleDwords (toBits v4i32 q) 0x1b#8))))) X := by
  dsimp only [Func.wp, vecMulNegShufSha]
  refine wp_vec_mul _ _ _ fun p hp => ?_
  refine wp_vec_neg _ _ fun q hq => ?_
  refine wp_shufd (by decide) (by decide) 0x1b#8 _ _ fun s hs => ?_
  refine wp_shufb (by decide) (by decide) _ _ _ fun sb hsb => ?_
  refine wp_alignr (by decide) (by decide) 4#8 _ _ _ fun al hal => ?_
  refine wp_blendw (by decide) (by decide) 0xaa#8 _ _ _ fun bw hbw => ?_
  refine wp_sha256msg1 _ _ _ fun m1 hm1 => ?_
  refine wp_sha256msg2 _ _ _ fun m2 hm2 => ?_
  refine wp_sha256rnds2 _ _ _ _ fun sr hsr => ?_
  wp_unfold
  dsimp only [Arg.val_var] at hp hq hs hsb hal hbw hm1 hm2 hsr
  refine ⟨lanewise3_mono (fun _ _ _ h => Or.inl h) 2 q a b ?_, ?_⟩
  · rw [lanewise3_iff_lane]
    intro i _
    rw [hq i, hp i]
  · simp [hsr, hm2, hm1, hbw, hal, hsb, hs]

theorem lane_liftFCmp_test (k : Nat) (a b : Val (Ty.vec k f32)) (i : Nat) :
    maskLane f32 k (liftFCmp .lt (Ty.vec k f32) a b) i =
      fcmpLeaf .lt .s (lane k a i) (lane k b i) :=
  lane_liftFCmp_float .lt .s k a b i

end LeanQbe.T.Test.KitTest
