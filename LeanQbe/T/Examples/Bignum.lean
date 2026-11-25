module

public import LeanQbe.T.Notation
public import LeanQbe.T.Module
public import LeanQbe.T.Logic.Rules
public import LeanQbe.T.WfLemmas
public import LeanQbe.T.Examples.BignumProg
import LeanQbe.T.FlatLemmas

/-!
# Curve25519 4×4-limb Bignum Multiply and Modular Add/Sub mod `2^255 - 19`

100%-PHOAS typed IR programs and `wp` proofs against `Nat` (`mul4x4`, `addMod25519`, `subMod25519`).
-/

set_option autoImplicit false
namespace LeanQbe.T.Examples.Bignum
open Std.ExtHashMap LeanQbe.T.ProofUtil

@[expose] public section

def p25519 : Nat := 2 ^ 255 - 19

def mul4x4Spec : Spec [i64, i64, i64] [] := fun (out, pa, pb, ()) m Q _ =>
  ∃ (as bs out0 : List (BitVec 64)) (R : Mem 64 → Prop),
    as.length = 4 ∧ bs.length = 4 ∧ out0.length = 8 ∧
    (array64 out out0 ⋆ array64 pa as ⋆ array64 pb bs ⋆ R) m ∧
    ∀ (rs : List (BitVec 64)) m', rs.length = 8 → limbsVal rs = limbsVal as * limbsVal bs →
      (array64 out rs ⋆ array64 pa as ⋆ array64 pb bs ⋆ R) m' → Q () m'

def addMod25519Spec : Spec [i64, i64, i64] [] := fun (out, pa, pb, ()) m Q _ =>
  ∃ (as bs out0 : List (BitVec 64)) (R : Mem 64 → Prop),
    as.length = 4 ∧ bs.length = 4 ∧ out0.length = 4 ∧
    limbsVal as < p25519 ∧ limbsVal bs < p25519 ∧
    (array64 out out0 ⋆ array64 pa as ⋆ array64 pb bs ⋆ R) m ∧
    ∀ (rs : List (BitVec 64)) m',
      rs.length = 4 → limbsVal rs = (limbsVal as + limbsVal bs) % p25519 →
      limbsVal rs < p25519 → (array64 out rs ⋆ array64 pa as ⋆ array64 pb bs ⋆ R) m' → Q () m'

def subMod25519Spec : Spec [i64, i64, i64] [] := fun (out, pa, pb, ()) m Q _ =>
  ∃ (as bs out0 : List (BitVec 64)) (R : Mem 64 → Prop),
    as.length = 4 ∧ bs.length = 4 ∧ out0.length = 4 ∧
    limbsVal as < p25519 ∧ limbsVal bs < p25519 ∧
    (array64 out out0 ⋆ array64 pa as ⋆ array64 pb bs ⋆ R) m ∧
    ∀ (rs : List (BitVec 64)) m', rs.length = 4 →
      limbsVal rs = (if limbsVal bs ≤ limbsVal as then limbsVal as - limbsVal bs
                     else limbsVal as + p25519 - limbsVal bs) →
      limbsVal rs < p25519 → (array64 out rs ⋆ array64 pa as ⋆ array64 pb bs ⋆ R) m' → Q () m'

def mul4x4Module : Module := ⟨[mul4x4Fn], [], []⟩
def addMod25519Module : Module := ⟨[addMod25519Fn], [], []⟩
def subMod25519Module : Module := ⟨[subMod25519Fn], [], []⟩

def bignumEnv : Env
  | "mul4x4",      [.bits 64, .bits 64, .bits 64], [] => mul4x4Spec
  | "addMod25519", [.bits 64, .bits 64, .bits 64], [] => addMod25519Spec
  | "subMod25519", [.bits 64, .bits 64, .bits 64], [] => subMod25519Spec
  | _, _, _ => fun _ _ _ _ => False

end

/-! ## Algebraic lemmas and shared `LimbSchoolbookKit` -/

public section

theorem limbsVal4_lt_pow256 (x0 x1 x2 x3 : BitVec 64) : limbsVal [x0, x1, x2, x3] < 2 ^ 256 :=
  (congrArg (2 ^ ·) (rfl : 64 * ([x0, x1, x2, x3] : List (BitVec 64)).length = 256)) ▸
    limbsVal_lt_pow [x0, x1, x2, x3]

theorem limbsVal4_eq (x0 x1 x2 x3 : BitVec 64) : limbsVal [x0, x1, x2, x3] =
    x0.toNat + 2 ^ 64 * (x1.toNat + 2 ^ 64 * (x2.toNat + 2 ^ 64 * x3.toNat)) := by simp [limbsVal]
theorem limbsVal5_eq (x0 x1 x2 x3 x4 : BitVec 64) : limbsVal [x0, x1, x2, x3, x4] =
    x0.toNat + 2 ^ 64 * (x1.toNat + 2 ^ 64 * (x2.toNat +
      2 ^ 64 * (x3.toNat + 2 ^ 64 * x4.toNat))) := by simp [limbsVal]
private theorem pow64_tel {k m : Nat} (hk : k ≤ 2 ^ 64) (hm : 1 ≤ 2 ^ m) :
    (2 ^ 64 - k) + 2 ^ 64 * (2 ^ m - 1) = 2 ^ (64 + m) - k := by
  rw [Nat.mul_sub_left_distrib, Nat.mul_one, ← Nat.pow_add]
  have hle : 2 ^ 64 ≤ 2 ^ 64 * 2 ^ m := Nat.le_mul_of_pos_right _ hm
  rw [← Nat.pow_add] at hle; omega

theorem limbsVal_p25519 : limbsVal [p0, p1, p2, p3] = p25519 := by
  have hp : p0.toNat = 2 ^ 64 - 19 ∧ p1.toNat = 2 ^ 64 - 1 ∧
      p2.toNat = 2 ^ 64 - 1 ∧ p3.toNat = 2 ^ 63 - 1 := by decide
  rw [limbsVal4_eq, hp.1, hp.2.1, hp.2.2.1, hp.2.2.2,
    pow64_tel (Nat.one_le_pow _ _ (by decide)) (Nat.one_le_pow 63 2 (by decide)),
    pow64_tel (Nat.one_le_pow _ _ (by decide)) (Nat.one_le_pow 127 2 (by decide)),
    pow64_tel (by decide : 19 ≤ 2 ^ 64) (Nat.one_le_pow 191 2 (by decide))]; rfl

theorem two_p25519_lt : 2 * p25519 < 2 ^ 256 := by
  have h19 : 19 ≤ (2 : Nat) ^ 255 :=
    Nat.le_trans (by decide : 19 ≤ 2 ^ 64) (Nat.pow_le_pow_right (by decide) (by decide))
  rw [show (2 : Nat) ^ 256 = 2 * 2 ^ 255 by
    rw [show (256 : Nat) = 1 + 255 from rfl, Nat.pow_add, Nat.pow_one], p25519]
  generalize (2 : Nat) ^ 255 = K at h19 ⊢; omega

local macro "step_limbs" : tactic => `(tactic| (
  repeat (first
    | refine wp_umulw_mk _ _ _ fun _ _ _ => ?_
    | refine wp_addc_mk _ _ _ _ fun _ _ _ => ?_
    | refine wp_subb_mk _ _ _ _ fun _ _ _ => ?_)
  simp only [Arg.val, Bool.toNat_false, Nat.add_zero] at *))

private theorem B4_eq_pow256 : (2 : Nat) ^ 64 * (2 ^ 64 * (2 ^ 64 * 2 ^ 64)) = 2 ^ 256 := by
  rw [← Nat.pow_add, ← Nat.pow_add, ← Nat.pow_add]

private theorem list4_eq {α : Type} {xs : List α} (h : xs.length = 4) :
    ∃ x0 x1 x2 x3, xs = [x0, x1, x2, x3] := by
  rcases xs with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, _ | ⟨x3, _ | _⟩⟩⟩⟩ <;> simp at h
  exact ⟨x0, x1, x2, x3, rfl⟩

private theorem mulRowAcc_eq {a0 a1 a2 a3 bj acc0 acc1 acc2 acc3 o0 o1 o2 o3 o4 : BitVec 64}
    {l0 h0 l1 h1 l2 h2 l3 h3 u1 u2 u3 u4 : Nat} {cx0 cx1 cx2 cx3 cx4 ox0 ox1 ox2 ox3 : Bool}
    (hm0 : h0 * 2 ^ 64 + l0 = a0.toNat * bj.toNat) (hm1 : h1 * 2 ^ 64 + l1 = a1.toNat * bj.toNat)
    (hm2 : h2 * 2 ^ 64 + l2 = a2.toNat * bj.toNat) (hm3 : h3 * 2 ^ 64 + l3 = a3.toNat * bj.toNat)
    (hcx0 : cx0.toNat * 2 ^ 64 + o0.toNat = acc0.toNat + l0)
    (hox0 : ox0.toNat * 2 ^ 64 + u1 = acc1.toNat + h0)
    (hcx1 : cx1.toNat * 2 ^ 64 + o1.toNat = u1 + l1 + cx0.toNat)
    (hox1 : ox1.toNat * 2 ^ 64 + u2 = acc2.toNat + h1 + ox0.toNat)
    (hcx2 : cx2.toNat * 2 ^ 64 + o2.toNat = u2 + l2 + cx1.toNat)
    (hox2 : ox2.toNat * 2 ^ 64 + u3 = acc3.toNat + h2 + ox1.toNat)
    (hcx3 : cx3.toNat * 2 ^ 64 + o3.toNat = u3 + l3 + cx2.toNat)
    (hox3 : ox3.toNat * 2 ^ 64 + u4 = h3 + ox2.toNat)
    (hcx4 : cx4.toNat * 2 ^ 64 + o4.toNat = u4 + cx3.toNat) :
    limbsVal [o0, o1, o2, o3, o4] =
      limbsVal [a0, a1, a2, a3] * bj.toNat + limbsVal [acc0, acc1, acc2, acc3] := by
  let B : Nat := 2 ^ 64
  have hox := add4_base (B := B) (a0 := acc1.toNat) (a1 := acc2.toNat) (a2 := acc3.toNat)
    (a3 := 0) (b0 := h0) (b1 := h1) (b2 := h2) (b3 := h3) hox0 hox1 hox2 (by simpa using hox3)
  have hcx := add4_base (B := B) (a0 := u1 + cx0.toNat) (a1 := u2) (a2 := u3) (a3 := u4)
    (b0 := l1) (b1 := l2) (b2 := l3) (b3 := 0) (by rw [hcx1]; ac_rfl) hcx2 hcx3 (by
      simpa using hcx4)
  have halg : (ox3.toNat + cx4.toNat) * (B * (B * (B * (B * B)))) +
      (o0.toNat + B * (o1.toNat + B * (o2.toNat + B * (o3.toNat + B * o4.toNat)))) =
      (a0.toNat + B * (a1.toNat + B * (a2.toNat + B * a3.toNat))) * bj.toNat +
      (acc0.toNat + B * (acc1.toNat + B * (acc2.toNat + B * acc3.toNat))) := by
    calc (ox3.toNat + cx4.toNat) * (B * (B * (B * (B * B)))) +
          (o0.toNat + B * (o1.toNat + B * (o2.toNat + B * (o3.toNat + B * o4.toNat))))
        = o0.toNat + B * (cx4.toNat * (B * (B * (B * B))) + (o1.toNat + B * (o2.toNat + B *
            (o3.toNat + B * o4.toNat)))) + B * (ox3.toNat * (B * (B * (B * B)))) := by
              simp only [Nat.add_mul, Nat.mul_add, ← Nat.mul_assoc]; ac_rfl
      _ = (cx0.toNat * B + o0.toNat) + B * (ox3.toNat * (B * (B * (B * B))) +
            (u1 + B * (u2 + B * (u3 + B * u4)))) + B * (l1 + B * (l2 + B * (l3 + B * 0))) := by
              rw [hcx]; simp only [Nat.mul_add]; ac_rfl
      _ = ((h0 * B + l0) + B * ((h1 * B + l1) + B * ((h2 * B + l2) + B * (h3 * B + l3)))) +
            (acc0.toNat + B * (acc1.toNat + B * (acc2.toNat + B * acc3.toNat))) := by
              rw [hcx0, hox]; simp only [Nat.mul_add, Nat.mul_zero, Nat.add_zero]; ac_rfl
      _ = _ := by rw [hm0, hm1, hm2, hm3]; simp only [Nat.add_mul, Nat.mul_assoc]
  have hlt1 := Nat.add_lt_add_of_le_of_lt (Nat.mul_le_mul_right bj.toNat
    (Nat.le_of_lt (limbsVal4_lt_pow256 a0 a1 a2 a3))) (limbsVal4_lt_pow256 acc0 acc1 acc2 acc3)
  have hlt2 : 2 ^ 256 * bj.toNat + 2 ^ 256 ≤ B * (B * (B * (B * B))) := by
    rw [← Nat.mul_succ, ← B4_eq_pow256, show B * (B * (B * (B * B))) = B * (B * (B * B)) * B by
      ac_rfl]; exact Nat.mul_le_mul_left _ bj.isLt
  rw [limbsVal5_eq, limbsVal4_eq, limbsVal4_eq]
  exact drop_high_carry halg (by simpa only [limbsVal4_eq] using Nat.lt_of_lt_of_le hlt1 hlt2)

private theorem add4_limbs {a0 a1 a2 a3 b0 b1 b2 b3 s0 s1 s2 s3 : BitVec 64} {c0 c1 c2 c3 : Bool}
    (h0 : c0.toNat * 2 ^ 64 + s0.toNat = a0.toNat + b0.toNat)
    (h1 : c1.toNat * 2 ^ 64 + s1.toNat = a1.toNat + b1.toNat + c0.toNat)
    (h2 : c2.toNat * 2 ^ 64 + s2.toNat = a2.toNat + b2.toNat + c1.toNat)
    (h3 : c3.toNat * 2 ^ 64 + s3.toNat = a3.toNat + b3.toNat + c2.toNat) :
    c3.toNat * 2 ^ 256 + limbsVal [s0, s1, s2, s3] =
      limbsVal [a0, a1, a2, a3] + limbsVal [b0, b1, b2, b3] := by
  have h := add4_base h0 h1 h2 h3; rw [B4_eq_pow256] at h; simpa [limbsVal4_eq] using h
private theorem sub4_limbs {a0 a1 a2 a3 b0 b1 b2 b3 d0 d1 d2 d3 : BitVec 64} {w0 w1 w2 w3 : Bool}
    (h0 : d0.toNat + b0.toNat = a0.toNat + w0.toNat * 2 ^ 64)
    (h1 : d1.toNat + b1.toNat + w0.toNat = a1.toNat + w1.toNat * 2 ^ 64)
    (h2 : d2.toNat + b2.toNat + w1.toNat = a2.toNat + w2.toNat * 2 ^ 64)
    (h3 : d3.toNat + b3.toNat + w2.toNat = a3.toNat + w3.toNat * 2 ^ 64) :
    limbsVal [d0, d1, d2, d3] + limbsVal [b0, b1, b2, b3] =
      limbsVal [a0, a1, a2, a3] + w3.toNat * 2 ^ 256 := by
  have h := sub4_base h0 h1 h2 h3; rw [B4_eq_pow256] at h; simpa [limbsVal4_eq] using h
private theorem mul4x4_combine {B A b0 b1 b2 b3 r0 r1 r2 t u v w : Nat}
    (e0 : r0 + B * t = A * b0) (e1 : r1 + B * u = A * b1 + t)
    (e2 : r2 + B * v = A * b2 + u) (e3 : w = A * b3 + v) :
    r0 + B * (r1 + B * (r2 + B * w)) = A * (b0 + B * (b1 + B * (b2 + B * b3))) := by
  rw [show r2 + B * w = A * b2 + u + B * (A * b3) by rw [e3, ← e2]; simp [Nat.mul_add]; ac_rfl,
    show r1 + B * (A * b2 + u + B * (A * b3)) =
      A * b1 + t + B * (A * b2 + B * (A * b3)) by rw [← e1]; simp [Nat.mul_add]; ac_rfl,
    show r0 + B * (A * b1 + t + B * (A * b2 + B * (A * b3))) =
      (r0 + B * t) + B * (A * b1 + B * (A * b2 + B * (A * b3))) by simp [Nat.mul_add]; ac_rfl,
    e0]; simp [Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm B A]

theorem load4K_spec {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {p : BitVec 64} (x0 x1 x2 x3 : BitVec 64) {R : Mem 64 → Prop}
    {k : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Expr Val Cont rs}
    (hm : (array64 p [x0, x1, x2, x3] ⋆ R) m) (hk : wp Γ Q X (k x0 x1 x2 x3) m) :
    wp Γ Q X (load4K p k) m := by
  unfold load4K; wp_unfold
  exact ⟨x0, by simpa using loadVal_array64 (i := 0) (by simp) hm, x1, by
    simpa using loadVal_array64 (i := 1) (by simp) hm, x2, by
    simpa using loadVal_array64 (i := 2) (by simp) hm, x3, by
    simpa using loadVal_array64 (i := 3) (by simp) hm, hk⟩
theorem store4K_spec {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {p : BitVec 64} {old : List (BitVec 64)} {x0 x1 x2 x3 : BitVec 64} {R : Mem 64 → Prop}
    {k : Expr Val Cont rs} (hlen : old.length = 4) (hm : (array64 p old ⋆ R) m)
    (hk : ∀ m', (array64 p [x0, x1, x2, x3] ⋆ R) m' → wp Γ Q X k m') :
    wp Γ Q X (store4K p x0 x1 x2 x3 k) m := by
  obtain ⟨o0, o1, o2, o3, rfl⟩ := list4_eq hlen; unfold store4K; wp_unfold
  obtain ⟨h0, hm⟩ := store_array64 x0 (i := 0) (by simp) hm
  rw [show p + BitVec.ofNat 64 (8 * 0) = p by simp] at h0 hm
  obtain ⟨h1, hm⟩ := store_array64 x1 (i := 1) (by simp) hm
  obtain ⟨h2, hm⟩ := store_array64 x2 (i := 2) (by simp) hm
  obtain ⟨h3, hm⟩ := store_array64 x3 (i := 3) (by simp) hm
  exact ⟨h0, h1, h2, h3, hk _ (by simpa using hm)⟩
theorem store8K_spec {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {p : BitVec 64} {old : List (BitVec 64)} {r0 r1 r2 r3 r4 r5 r6 r7 : BitVec 64}
    {R : Mem 64 → Prop} {k : Expr Val Cont rs} (hlen : old.length = 8) (hm : (array64 p old ⋆ R) m)
    (hk : ∀ m', (array64 p [r0, r1, r2, r3, r4, r5, r6, r7] ⋆ R) m' → wp Γ Q X k m') :
    wp Γ Q X (store8K p r0 r1 r2 r3 r4 r5 r6 r7 k) m := by
  unfold store8K
  rw [← List.take_append_drop 4 old, array64_append, List.length_take_of_le (by omega)] at hm
  refine store4K_spec (old := old.take 4) (R := array64 (p + 32) (old.drop 4) ⋆ R)
    (by simp [hlen]) (sep_ac hm) fun _ hm1 => ?_; wp_unfold
  refine store4K_spec (old := old.drop 4) (R := array64 p [r0, r1, r2, r3] ⋆ R)
    (by simp [hlen]) (sep_ac hm1) fun m2 hm2 => hk m2 ?_
  rw [show [r0, r1, r2, r3, r4, r5, r6, r7] = [r0, r1, r2, r3] ++ [r4, r5, r6, r7] from rfl,
    array64_append]; exact sep_ac hm2
theorem mulRow0K_spec {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    (a0 a1 a2 a3 b0 : BitVec 64)
    (k : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Expr Val Cont rs)
    (hk : ∀ r0 r1 r2 r3 r4 : BitVec 64,
      limbsVal [r0, r1, r2, r3, r4] = limbsVal [a0, a1, a2, a3] * b0.toNat →
      wp Γ Q X (k r0 r1 r2 r3 r4) m) : wp Γ Q X (mulRow0K a0 a1 a2 a3 b0 k) m := by
  unfold mulRow0K; step_limbs
  rename_i r0 h0 hm0 l1 h1 hm1 r1 c0 ha0 l2 h2 hm2 r2 c1 ha1 l3 h3 hm3 r3 c2 ha2 r4 c3 ha3
  refine hk r0 r1 r2 r3 r4 ?_
  simpa using mulRowAcc_eq (acc0 := 0#64) (acc1 := 0#64) (acc2 := 0#64) (acc3 := 0#64)
    (u1 := h0.toNat) (u2 := h1.toNat) (u3 := h2.toNat) (u4 := h3.toNat)
    (cx0 := false) (ox0 := false) (ox1 := false) (ox2 := false) (ox3 := false)
    hm0 hm1 hm2 hm3 (by simp) (by simp) ha0 (by simp) ha1 (by simp) ha2 (by simp)
    (by simpa [show (0 : BitVec 64).toNat = 0 from rfl] using ha3)
theorem mulRowAccK_spec {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    (a0 a1 a2 a3 bj acc0 acc1 acc2 acc3 : BitVec 64)
    (k : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Expr Val Cont rs)
    (hk : ∀ o0 o1 o2 o3 o4 : BitVec 64, limbsVal [o0, o1, o2, o3, o4] =
      limbsVal [a0, a1, a2, a3] * bj.toNat + limbsVal [acc0, acc1, acc2, acc3] →
      wp Γ Q X (k o0 o1 o2 o3 o4) m) :
    wp Γ Q X (mulRowAccK a0 a1 a2 a3 bj acc0 acc1 acc2 acc3 k) m := by
  unfold mulRowAccK; step_limbs
  rename_i l0 h0 hm0 o0 cx0 hcx0 l1 h1 hm1 u1 ox0 hox0 o1 cx1 hcx1 l2 h2 hm2 u2 ox1 hox1
    o2 cx2 hcx2 l3 h3 hm3 u3 ox2 hox2 o3 cx3 hcx3 u4 ox3 hox3 o4 cx4 hcx4
  exact hk o0 o1 o2 o3 o4
    (mulRowAcc_eq hm0 hm1 hm2 hm3 hcx0 hox0 hcx1 hox1 hcx2 hox2 hcx3 hox3 hcx4)
theorem add4K_spec {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64)
    (k : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Bool → Expr Val Cont rs)
    (hk : ∀ (s0 s1 s2 s3 : BitVec 64) (c3 : Bool), c3.toNat * 2 ^ 256 + limbsVal [s0, s1, s2, s3] =
      limbsVal [a0, a1, a2, a3] + limbsVal [b0, b1, b2, b3] → wp Γ Q X (k s0 s1 s2 s3 c3) m) :
    wp Γ Q X (add4K a0 a1 a2 a3 b0 b1 b2 b3 k) m := by
  unfold add4K; step_limbs; rename_i s0 c0 h0 s1 c1 h1 s2 c2 h2 s3 c3 h3
  exact hk s0 s1 s2 s3 c3 (add4_limbs h0 h1 h2 h3)
theorem sub4K_spec {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64)
    (k : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Bool → Expr Val Cont rs)
    (hk : ∀ (d0 d1 d2 d3 : BitVec 64) (w3 : Bool), limbsVal [d0, d1, d2, d3] +
      limbsVal [b0, b1, b2, b3] = limbsVal [a0, a1, a2, a3] + w3.toNat * 2 ^ 256 →
      wp Γ Q X (k d0 d1 d2 d3 w3) m) : wp Γ Q X (sub4K a0 a1 a2 a3 b0 b1 b2 b3 k) m := by
  unfold sub4K; step_limbs; rename_i d0 w0 h0 d1 w1 h1 d2 w2 h2 d3 w3 h3
  exact hk d0 d1 d2 d3 w3 (sub4_limbs h0 h1 h2 h3)
theorem addImm4K_spec {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    (d0 d1 d2 d3 q0 q1 q2 q3 : BitVec 64)
    (k : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Bool → Expr Val Cont rs)
    (hk : ∀ (s0 s1 s2 s3 : BitVec 64) (c3 : Bool), c3.toNat * 2 ^ 256 + limbsVal [s0, s1, s2, s3] =
      limbsVal [d0, d1, d2, d3] + limbsVal [q0, q1, q2, q3] → wp Γ Q X (k s0 s1 s2 s3 c3) m) :
    wp Γ Q X (addImm4K d0 d1 d2 d3 q0 q1 q2 q3 k) m := by
  unfold addImm4K; step_limbs; rename_i s0 c0 h0 s1 c1 h1 s2 c2 h2 s3 c3 h3
  exact hk s0 s1 s2 s3 c3 (add4_limbs h0 h1 h2 h3)
theorem select4K_spec {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    (c : Bool) (x0 x1 x2 x3 y0 y1 y2 y3 : BitVec 64)
    (k : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Expr Val Cont rs)
    (hk : wp Γ Q X (if c then k x0 x1 x2 x3 else k y0 y1 y2 y3) m) :
    wp Γ Q X (select4K c x0 x1 x2 x3 y0 y1 y2 y3 k) m := by
  unfold select4K; wp_unfold; cases c <;> exact hk

/-! ## Top-level `wp`, `Func.Wf`, and `ModuleOk` proofs -/

private theorem load2x4_spec {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {out pa pb : BitVec 64} {as bs out0 : List (BitVec 64)} {R : Mem 64 → Prop}
    {k : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 →
         BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Expr Val Cont rs}
    (has : as.length = 4) (hbs : bs.length = 4)
    (hm : (array64 out out0 ⋆ array64 pa as ⋆ array64 pb bs ⋆ R) m)
    (hk : ∀ a0 a1 a2 a3 b0 b1 b2 b3, as = [a0, a1, a2, a3] → bs = [b0, b1, b2, b3] →
      wp Γ Q X (k a0 a1 a2 a3 b0 b1 b2 b3) m) : wp Γ Q X
      (load4K pa fun a0 a1 a2 a3 => load4K pb fun b0 b1 b2 b3 => k a0 a1 a2 a3 b0 b1 b2 b3) m := by
  obtain ⟨a0, a1, a2, a3, rfl⟩ := list4_eq has; obtain ⟨b0, b1, b2, b3, rfl⟩ := list4_eq hbs
  refine load4K_spec a0 a1 a2 a3 (R := array64 out out0 ⋆ array64 pb _ ⋆ R) (sep_ac hm) ?_
  refine load4K_spec b0 b1 b2 b3 (R := array64 out out0 ⋆ array64 pa _ ⋆ R) (sep_ac hm)
    (hk a0 a1 a2 a3 b0 b1 b2 b3 rfl rfl)
private theorem mod25519_finish {Γ : Env} {Q : Post []} {X : XPost} {m : Mem 64}
    {out pa pb : BitVec 64} {as bs out0 : List (BitVec 64)} {R : Mem 64 → Prop}
    (hout : out0.length = 4) (hm : (array64 out out0 ⋆ array64 pa as ⋆ array64 pb bs ⋆ R) m)
    (w3 : Bool) (s0 s1 s2 s3 d0 d1 d2 d3 : BitVec 64) {target : Nat}
    (hres : (w3 = false → limbsVal [d0, d1, d2, d3] = target ∧ limbsVal [d0, d1, d2, d3] < p25519) ∧
      (w3 = true → limbsVal [s0, s1, s2, s3] = target ∧ limbsVal [s0, s1, s2, s3] < p25519))
    (hQ : ∀ rs m', rs.length = 4 → limbsVal rs = target → limbsVal rs < p25519 →
      (array64 out rs ⋆ array64 pa as ⋆ array64 pb bs ⋆ R) m' → Q () m') :
    wp Γ Q X (select4K w3 s0 s1 s2 s3 d0 d1 d2 d3 fun r0 r1 r2 r3 =>
      store4K out r0 r1 r2 r3 (.ret ())) m := by
  refine select4K_spec w3 s0 s1 s2 s3 d0 d1 d2 d3 _ ?_
  cases w3 <;> refine store4K_spec hout (R := array64 pa as ⋆ array64 pb bs ⋆ R) (sep_ac hm)
    fun m' hm' => ?_ <;> (wp_unfold; first
      | exact hQ _ m' rfl (hres.1 rfl).1 (hres.1 rfl).2 (sep_ac hm')
      | exact hQ _ m' rfl (hres.2 rfl).1 (hres.2 rfl).2 (sep_ac hm'))
private theorem addMod_arith {A B S D P M : Nat} {c w : Bool}
    (hA : A < P) (hB : B < P) (h2P : 2 * P < M) (hD : D < M)
    (hadd : c.toNat * M + S = A + B) (hsub : D + P = S + w.toNat * M) :
    (w = false → D = (A + B) % P ∧ D < P) ∧ (w = true → S = (A + B) % P ∧ S < P) := by
  have hS : S = A + B := drop_high_carry hadd (by omega)
  cases w <;> simp [hS] at hsub ⊢
  · exact ⟨by rw [← hsub, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)], by omega⟩
  · exact ⟨(Nat.mod_eq_of_lt (by omega)).symm, by omega⟩
private theorem subMod_arith {A B D S P M : Nat} {w c : Bool}
    (hA : A < P) (hB : B < P) (hD : D < M) (hS : S < M)
    (hsub : D + B = A + w.toNat * M) (hadd : c.toNat * M + S = D + P) :
    (w = false → D = (if B ≤ A then A - B else A + P - B) ∧ D < P) ∧
    (w = true → S = (if B ≤ A then A - B else A + P - B) ∧ S < P) := by
  cases w <;> simp at hsub ⊢
  · have hle : B ≤ A := by omega
    simp only [hle, ↓reduceIte]; omega
  · have hgt : ¬ B ≤ A := by omega
    cases c <;> simp at hadd
    · omega
    simp only [hgt, ↓reduceIte]; omega
theorem mul4x4_correct (Γ : Env) :
    ∀ args m Q X, mul4x4Spec args m Q X → Func.spec Γ mul4x4 args m Q X := by
  rintro ⟨out, pa, pb, ⟨⟩⟩ m Q X ⟨as, bs, out0, R, has, hbs, hout, hm, hQ⟩
  dsimp only [Func.spec, Func.wp, mul4x4]
  refine load2x4_spec has hbs hm fun a0 a1 a2 a3 b0 b1 b2 b3 hA hB => ?_; subst hA hB
  refine mulRow0K_spec a0 a1 a2 a3 b0 _ fun r0 t1 t2 t3 t4 hr0 => ?_
  refine mulRowAccK_spec a0 a1 a2 a3 b1 t1 t2 t3 t4 _ fun r1 u2 u3 u4 u5 hr1 => ?_
  refine mulRowAccK_spec a0 a1 a2 a3 b2 u2 u3 u4 u5 _ fun r2 v3 v4 v5 v6 hr2 => ?_
  refine mulRowAccK_spec a0 a1 a2 a3 b3 v3 v4 v5 v6 _ fun r3 r4 r5 r6 r7 hr3 => ?_
  refine store8K_spec hout (R := array64 pa [a0, a1, a2, a3] ⋆ array64 pb [b0, b1, b2, b3] ⋆ R)
    (sep_ac hm) fun m' hm' => ?_; wp_unfold; refine hQ _ m' rfl ?_ (sep_ac hm')
  simpa [limbsVal4_eq, limbsVal] using mul4x4_combine (B := 2 ^ 64) (A := limbsVal [a0, a1, a2, a3])
    (by simpa [limbsVal] using hr0) (by simpa [limbsVal] using hr1)
    (by simpa [limbsVal] using hr2) hr3
theorem addMod25519_correct (Γ : Env) :
    ∀ args m Q X, addMod25519Spec args m Q X → Func.spec Γ addMod25519 args m Q X := by
  rintro ⟨out, pa, pb, ⟨⟩⟩ m Q X ⟨as, bs, out0, R, has, hbs, hout, hAlt, hBlt, hm, hQ⟩
  dsimp only [Func.spec, Func.wp, addMod25519]
  refine load2x4_spec has hbs hm fun a0 a1 a2 a3 b0 b1 b2 b3 hA hB => ?_; subst hA hB
  refine add4K_spec a0 a1 a2 a3 b0 b1 b2 b3 _ fun s0 s1 s2 s3 c3 hsum => ?_
  step_limbs; rename_i d0 w0 hw0 d1 w1 hw1 d2 w2 hw2 d3 w3 hw3
  have hsub := sub4_limbs hw0 hw1 hw2 hw3; rw [limbsVal_p25519] at hsub
  exact mod25519_finish hout hm w3 s0 s1 s2 s3 d0 d1 d2 d3
    (addMod_arith hAlt hBlt two_p25519_lt (limbsVal4_lt_pow256 d0 d1 d2 d3) hsum hsub) hQ
theorem subMod25519_correct (Γ : Env) :
    ∀ args m Q X, subMod25519Spec args m Q X → Func.spec Γ subMod25519 args m Q X := by
  rintro ⟨out, pa, pb, ⟨⟩⟩ m Q X ⟨as, bs, out0, R, has, hbs, hout, hAlt, hBlt, hm, hQ⟩
  dsimp only [Func.spec, Func.wp, subMod25519]
  refine load2x4_spec has hbs hm fun a0 a1 a2 a3 b0 b1 b2 b3 hA hB => ?_; subst hA hB
  refine sub4K_spec a0 a1 a2 a3 b0 b1 b2 b3 _ fun d0 d1 d2 d3 w3 hsub => ?_
  refine addImm4K_spec d0 d1 d2 d3 p0 p1 p2 p3 _ fun s0 s1 s2 s3 c3 hadd => ?_
  rw [limbsVal_p25519] at hadd; exact mod25519_finish hout hm w3 s0 s1 s2 s3 d0 d1 d2 d3
    (subMod_arith hAlt hBlt (limbsVal4_lt_pow256 d0 d1 d2 d3) (limbsVal4_lt_pow256 s0 s1 s2 s3)
      hsub hadd) hQ
theorem mul4x4_wf : Func.Wf mul4x4 := by t_wf_reify
theorem addMod25519_wf : Func.Wf addMod25519 := by t_wf_reify
theorem subMod25519_wf : Func.Wf subMod25519 := by t_wf_reify
theorem mul4x4Module_checkAcyclic : mul4x4Module.checkAcyclic = true := by rfl
theorem addMod25519Module_checkAcyclic : addMod25519Module.checkAcyclic = true := by rfl
theorem subMod25519Module_checkAcyclic : subMod25519Module.checkAcyclic = true := by rfl
private theorem single_moduleOk {fn : Fn}
    (hacyc : ({ fns := [fn], externs := [], exits := [] } : Module).checkAcyclic = true)
    (hwf : fn.Wf) (hcorr : ∀ xs m Q X,
      bignumEnv fn.name fn.as fn.rs xs m Q X → Func.wp bignumEnv fn.body xs m Q X) :
    ModuleOk bignumEnv ⟨[fn], [], []⟩ := Module.moduleOk_of_checkAcyclic hacyc
  (fun _ h => by simp at h; subst h; exact hwf) (fun _ h => by simp at h; subst h; exact hcorr)
theorem mul4x4_moduleOk : ModuleOk bignumEnv mul4x4Module :=
  single_moduleOk mul4x4Module_checkAcyclic mul4x4_wf (mul4x4_correct bignumEnv)
theorem addMod25519_moduleOk : ModuleOk bignumEnv addMod25519Module :=
  single_moduleOk addMod25519Module_checkAcyclic addMod25519_wf (addMod25519_correct bignumEnv)
theorem subMod25519_moduleOk : ModuleOk bignumEnv subMod25519Module :=
  single_moduleOk subMod25519Module_checkAcyclic subMod25519_wf (subMod25519_correct bignumEnv)

end
end LeanQbe.T.Examples.Bignum
