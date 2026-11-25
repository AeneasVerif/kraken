module

public import LeanQbe.T.Notation
public import LeanQbe.T.Module
public import LeanQbe.T.Logic.Rules
public import LeanQbe.T.WfLemmas
public import LeanQbe.T.Examples.BignumProg
import LeanQbe.T.FlatLemmas

/-!
# Curve25519 4×4-limb Bignum Multiply and Modular Add/Sub mod `2^255 - 19`

100%-PHOAS typed IR programs and `wp` proofs against `Nat` (straight-line fixed-width limbs,
constant-time `select` with zero secret-dependent branches):

* `mul4x4`: 4×4-limb schoolbook multiply (`umulw` + interleaved dual `addc` chains matching x64
  `mulx` + `adcx`/`adox`).
* `addMod25519`: constant-time 4-limb modular addition mod `2^255 - 19`.
* `subMod25519`: constant-time 4-limb modular subtraction mod `2^255 - 19`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Bignum

open Std.ExtHashMap
open LeanQbe.T.ProofUtil

/-! ## Curve25519 prime `p = 2^255 - 19` -/

def p25519 : Nat := 2 ^ 255 - 19

/-! ## Public specifications -/

def mul4x4Spec : Spec [i64, i64, i64] [] := fun (out, pa, pb, ()) m Q _ =>
  ∃ (as bs out0 : List (BitVec 64)) (R : Mem 64 → Prop),
    as.length = 4 ∧ bs.length = 4 ∧ out0.length = 8 ∧
    (array64 out out0 ⋆ array64 pa as ⋆ array64 pb bs ⋆ R) m ∧
    ∀ (rs : List (BitVec 64)) m',
      rs.length = 8 →
      limbsVal rs = limbsVal as * limbsVal bs →
      (array64 out rs ⋆ array64 pa as ⋆ array64 pb bs ⋆ R) m' →
      Q () m'

def addMod25519Spec : Spec [i64, i64, i64] [] := fun (out, pa, pb, ()) m Q _ =>
  ∃ (as bs out0 : List (BitVec 64)) (R : Mem 64 → Prop),
    as.length = 4 ∧ bs.length = 4 ∧ out0.length = 4 ∧
    limbsVal as < p25519 ∧ limbsVal bs < p25519 ∧
    (array64 out out0 ⋆ array64 pa as ⋆ array64 pb bs ⋆ R) m ∧
    ∀ (rs : List (BitVec 64)) m',
      rs.length = 4 →
      limbsVal rs = (limbsVal as + limbsVal bs) % p25519 →
      limbsVal rs < p25519 →
      (array64 out rs ⋆ array64 pa as ⋆ array64 pb bs ⋆ R) m' →
      Q () m'

def subMod25519Spec : Spec [i64, i64, i64] [] := fun (out, pa, pb, ()) m Q _ =>
  ∃ (as bs out0 : List (BitVec 64)) (R : Mem 64 → Prop),
    as.length = 4 ∧ bs.length = 4 ∧ out0.length = 4 ∧
    limbsVal as < p25519 ∧ limbsVal bs < p25519 ∧
    (array64 out out0 ⋆ array64 pa as ⋆ array64 pb bs ⋆ R) m ∧
    ∀ (rs : List (BitVec 64)) m',
      rs.length = 4 →
      limbsVal rs = (if limbsVal bs ≤ limbsVal as then limbsVal as - limbsVal bs
                     else limbsVal as + p25519 - limbsVal bs) →
      limbsVal rs < p25519 →
      (array64 out rs ⋆ array64 pa as ⋆ array64 pb bs ⋆ R) m' →
      Q () m'

/-! ## Algebraic lemmas (no `omega` on `≥ 2^128` or kernel `2^320` reduction) -/

theorem limbsVal4_lt_pow256 (x0 x1 x2 x3 : BitVec 64) : limbsVal [x0, x1, x2, x3] < 2 ^ 256 :=
  (congrArg (2 ^ ·) (rfl : 64 * ([x0, x1, x2, x3] : List (BitVec 64)).length = 256)) ▸
    limbsVal_lt_pow [x0, x1, x2, x3]

theorem limbsVal4_eq (x0 x1 x2 x3 : BitVec 64) :
    limbsVal [x0, x1, x2, x3] =
      x0.toNat + 2 ^ 64 * (x1.toNat + 2 ^ 64 * (x2.toNat + 2 ^ 64 * x3.toNat)) := by
  simp [limbsVal]

theorem limbsVal5_eq (x0 x1 x2 x3 x4 : BitVec 64) :
    limbsVal [x0, x1, x2, x3, x4] =
      x0.toNat + 2 ^ 64 * (x1.toNat + 2 ^ 64 * (x2.toNat +
        2 ^ 64 * (x3.toNat + 2 ^ 64 * x4.toNat))) := by
  simp [limbsVal]

private theorem pow64_tel {k m : Nat} (hk : k ≤ 2 ^ 64) (hm : 1 ≤ 2 ^ m) :
    (2 ^ 64 - k) + 2 ^ 64 * (2 ^ m - 1) = 2 ^ (64 + m) - k := by
  rw [Nat.mul_sub_left_distrib, Nat.mul_one, ← Nat.pow_add]
  have hle : 2 ^ 64 ≤ 2 ^ 64 * 2 ^ m := Nat.le_mul_of_pos_right _ hm
  rw [← Nat.pow_add] at hle; omega

theorem limbsVal_p25519 : limbsVal [p0, p1, p2, p3] = p25519 := by
  have hp : p0.toNat = 2 ^ 64 - 19 ∧ p1.toNat = 2 ^ 64 - 1 ∧
      p2.toNat = 2 ^ 64 - 1 ∧ p3.toNat = 2 ^ 63 - 1 := by decide
  have s1 := pow64_tel (Nat.one_le_pow _ _ (by decide)) (Nat.one_le_pow 63 2 (by decide))
  have s2 := pow64_tel (Nat.one_le_pow _ _ (by decide)) (Nat.one_le_pow 127 2 (by decide))
  have s3 := pow64_tel (by decide : 19 ≤ 2 ^ 64) (Nat.one_le_pow 191 2 (by decide))
  rw [limbsVal4_eq, hp.1, hp.2.1, hp.2.2.1, hp.2.2.2, s1, s2, s3]; rfl

theorem two_p25519_lt : 2 * p25519 < 2 ^ 256 := by
  have h19 : 19 ≤ (2 : Nat) ^ 255 :=
    Nat.le_trans (by decide : 19 ≤ 2 ^ 64) (Nat.pow_le_pow_right (by decide) (by decide))
  rw [show (2 : Nat) ^ 256 = 2 * 2 ^ 255 by
    rw [show (256 : Nat) = 1 + 255 from rfl, Nat.pow_add, Nat.pow_one], p25519]
  generalize (2 : Nat) ^ 255 = K at h19 ⊢; omega

private theorem B4_eq_pow256 : (2 : Nat) ^ 64 * (2 ^ 64 * (2 ^ 64 * 2 ^ 64)) = 2 ^ 256 := by
  rw [← Nat.pow_add, ← Nat.pow_add, ← Nat.pow_add]

local macro "step_limbs" : tactic => `(tactic| (
  repeat (first
    | refine wp_umulw_mk _ _ _ fun _ _ _ => ?_
    | refine wp_addc_mk _ _ _ _ fun _ _ _ => ?_
    | refine wp_subb_mk _ _ _ _ fun _ _ _ => ?_)
  simp only [Arg.val, Bool.toNat_false, Nat.add_zero] at *))

/-! ## `LimbSchoolbookKit`: shared 4-limb algebraic, memory, and WP combinators -/

section LimbSchoolbookKit

private theorem list4_eq {α : Type} {xs : List α} (h : xs.length = 4) :
    ∃ x0 x1 x2 x3, xs = [x0, x1, x2, x3] := by
  rcases xs with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, _ | ⟨x3, _ | _⟩⟩⟩⟩ <;> simp at h
  exact ⟨x0, x1, x2, x3, rfl⟩

private theorem mulRowAcc_alg
    {B a0 a1 a2 a3 bj acc0 acc1 acc2 acc3 l0 h0 l1 h1 l2 h2 l3 h3 u1 u2 u3 u4 o0 o1 o2 o3 o4 : Nat}
    {cx0 cx1 cx2 cx3 cx4 ox0 ox1 ox2 ox3 : Bool}
    (hm0 : h0 * B + l0 = a0 * bj) (hm1 : h1 * B + l1 = a1 * bj)
    (hm2 : h2 * B + l2 = a2 * bj) (hm3 : h3 * B + l3 = a3 * bj)
    (hcx0 : cx0.toNat * B + o0 = acc0 + l0) (hox0 : ox0.toNat * B + u1 = acc1 + h0)
    (hcx1 : cx1.toNat * B + o1 = u1 + l1 + cx0.toNat)
    (hox1 : ox1.toNat * B + u2 = acc2 + h1 + ox0.toNat)
    (hcx2 : cx2.toNat * B + o2 = u2 + l2 + cx1.toNat)
    (hox2 : ox2.toNat * B + u3 = acc3 + h2 + ox1.toNat)
    (hcx3 : cx3.toNat * B + o3 = u3 + l3 + cx2.toNat) (hox3 : ox3.toNat * B + u4 = h3 + ox2.toNat)
    (hcx4 : cx4.toNat * B + o4 = u4 + cx3.toNat) :
    (ox3.toNat + cx4.toNat) * (B * (B * (B * (B * B)))) +
      (o0 + B * (o1 + B * (o2 + B * (o3 + B * o4)))) =
      (a0 + B * (a1 + B * (a2 + B * a3))) * bj +
      (acc0 + B * (acc1 + B * (acc2 + B * acc3))) := by
  calc (ox3.toNat + cx4.toNat) * (B * (B * (B * (B * B)))) +
        (o0 + B * (o1 + B * (o2 + B * (o3 + B * o4))))
      = o0 + B * (o1 + B * (o2 + B * (o3 + B * ((cx4.toNat * B + o4) + ox3.toNat * B)))) := by
          simp only [Nat.add_mul, Nat.mul_add, ← Nat.mul_assoc]; ac_rfl
    _ = o0 + B * (o1 + B * (o2 + B * ((cx3.toNat * B + o3) + B * (ox3.toNat * B + u4)))) := by
          rw [hcx4]; simp only [Nat.mul_add]; ac_rfl
    _ = o0 + B * (o1 + B * (o2 + B * ((ox2.toNat * B + u3) + l3 + cx2.toNat + B * h3))) := by
          rw [hcx3, hox3]; simp only [Nat.mul_add]; ac_rfl
    _ = o0 + B * (o1 + B * ((cx2.toNat * B + o2) +
        B * (acc3 + h2 + ox1.toNat + (l3 + B * h3)))) := by
          rw [hox2]; simp only [Nat.mul_add]; ac_rfl
    _ = o0 + B * (o1 + B * ((ox1.toNat * B + u2) + l2 + cx1.toNat +
        B * (acc3 + h2 + (l3 + B * h3)))) := by
          rw [hcx2]; simp only [Nat.mul_add]; ac_rfl
    _ = o0 + B * ((cx1.toNat * B + o1) + B * (acc2 + h1 + ox0.toNat + l2 +
        B * (acc3 + h2 + (l3 + B * h3)))) := by
          rw [hox1]; simp only [Nat.mul_add]; ac_rfl
    _ = o0 + B * ((ox0.toNat * B + u1) + l1 + cx0.toNat + B * (acc2 + h1 + l2 +
        B * (acc3 + h2 + (l3 + B * h3)))) := by
          rw [hcx1]; simp only [Nat.mul_add]; ac_rfl
    _ = (cx0.toNat * B + o0) + B * (acc1 + h0 + l1 + B * (acc2 + h1 + l2 +
        B * (acc3 + h2 + (l3 + B * h3)))) := by
          rw [hox0]; simp only [Nat.mul_add]; ac_rfl
    _ = ((l0 + B * h0) + B * ((l1 + B * h1) + B * ((l2 + B * h2) + B * (l3 + B * h3)))) +
        (acc0 + B * (acc1 + B * (acc2 + B * acc3))) := by
          rw [hcx0]; simp only [Nat.mul_add]; ac_rfl
    _ = (a0 + B * (a1 + B * (a2 + B * a3))) * bj +
        (acc0 + B * (acc1 + B * (acc2 + B * acc3))) := by
          rw [Nat.add_comm l0, Nat.mul_comm B h0, hm0, Nat.add_comm l1, Nat.mul_comm B h1, hm1,
              Nat.add_comm l2, Nat.mul_comm B h2, hm2, Nat.add_comm l3, Nat.mul_comm B h3, hm3]
          simp only [Nat.add_mul, Nat.mul_assoc]

private theorem mulRow0_alg {B a0 a1 a2 a3 b0 r0 h0 l1 h1 r1 l2 h2 r2 l3 h3 r3 r4 : Nat}
    {c0 c1 c2 c3 : Bool}
    (hm0 : h0 * B + r0 = a0 * b0) (hm1 : h1 * B + l1 = a1 * b0)
    (hm2 : h2 * B + l2 = a2 * b0) (hm3 : h3 * B + l3 = a3 * b0)
    (ha0 : c0.toNat * B + r1 = h0 + l1) (ha1 : c1.toNat * B + r2 = h1 + l2 + c0.toNat)
    (ha2 : c2.toNat * B + r3 = h2 + l3 + c1.toNat) (ha3 : c3.toNat * B + r4 = h3 + c2.toNat) :
    c3.toNat * (B * (B * (B * (B * B)))) +
      (r0 + B * (r1 + B * (r2 + B * (r3 + B * r4)))) =
      (a0 + B * (a1 + B * (a2 + B * a3))) * b0 := by
  have h := mulRowAcc_alg (B := B) (a0 := a0) (a1 := a1) (a2 := a2) (a3 := a3) (bj := b0)
    (acc0 := 0) (acc1 := 0) (acc2 := 0) (acc3 := 0) (l0 := r0) (h0 := h0) (l1 := l1) (h1 := h1)
    (l2 := l2) (h2 := h2) (l3 := l3) (h3 := h3) (u1 := h0) (u2 := h1) (u3 := h2) (u4 := h3)
    (o0 := r0) (o1 := r1) (o2 := r2) (o3 := r3) (o4 := r4)
    (cx0 := false) (cx1 := c0) (cx2 := c1) (cx3 := c2) (cx4 := c3)
    (ox0 := false) (ox1 := false) (ox2 := false) (ox3 := false)
    hm0 hm1 hm2 hm3 (by simp) (by simp) (by simpa using ha0) (by simp)
    (by simpa using ha1) (by simp) (by simpa using ha2) (by simp) (by simpa using ha3)
  simpa using h

private theorem mulRowAcc_bound {B A acc b : Nat}
    (hA : A < B * (B * (B * B))) (hacc : acc < B * (B * (B * B))) (hb : b < B) :
    A * b + acc < B * (B * (B * (B * B))) := by
  let B4 := B * (B * (B * B))
  have h1 : A * b + acc < A * b + B4 := Nat.add_lt_add_left hacc _
  have h2 : A * b + B4 ≤ B4 * b + B4 :=
    Nat.add_le_add_right (Nat.mul_le_mul_right _ (Nat.le_of_lt hA)) _
  have h3 : B4 * b + B4 = B4 * (b + 1) := by rw [Nat.mul_add, Nat.mul_one]
  have h4 : B4 * (b + 1) ≤ B4 * B := Nat.mul_le_mul_left _ hb
  have h5 : B4 * B = B * (B * (B * (B * B))) := by dsimp only [B4]; ac_rfl
  exact Nat.lt_of_lt_of_le h1 (Nat.le_trans h2 (h3 ▸ h5 ▸ h4))

/-! ## Fragment `wp` lemmas -/

theorem load4K_spec {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {p : BitVec 64} (x0 x1 x2 x3 : BitVec 64) {R : Mem 64 → Prop}
    {k : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Expr Val Cont rs}
    (hm : (array64 p [x0, x1, x2, x3] ⋆ R) m)
    (hk : wp Γ Q X (k x0 x1 x2 x3) m) :
    wp Γ Q X (load4K p k) m := by
  unfold load4K; wp_unfold
  exact ⟨x0, by simpa using loadVal_array64 (i := 0) (by simp) hm,
         x1, by simpa using loadVal_array64 (i := 1) (by simp) hm,
         x2, by simpa using loadVal_array64 (i := 2) (by simp) hm,
         x3, by simpa using loadVal_array64 (i := 3) (by simp) hm, hk⟩

theorem store4K_spec {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {p : BitVec 64} {old : List (BitVec 64)} {x0 x1 x2 x3 : BitVec 64} {R : Mem 64 → Prop}
    {k : Expr Val Cont rs}
    (hlen : old.length = 4) (hm : (array64 p old ⋆ R) m)
    (hk : ∀ m', (array64 p [x0, x1, x2, x3] ⋆ R) m' → wp Γ Q X k m') :
    wp Γ Q X (store4K p x0 x1 x2 x3 k) m := by
  obtain ⟨o0, o1, o2, o3, rfl⟩ := list4_eq hlen
  unfold store4K; wp_unfold
  obtain ⟨ok0, hm0⟩ := store_array64 (i := 0) x0 (by simp) hm
  obtain ⟨ok1, hm1⟩ := store_array64 (i := 1) x1 (by simp) hm0
  obtain ⟨ok2, hm2⟩ := store_array64 (i := 2) x2 (by simp) hm1
  obtain ⟨ok3, hm3⟩ := store_array64 (i := 3) x3 (by simp) hm2
  exact ⟨by simpa using ok0, by simpa using ok1, by simpa using ok2,
    by simpa using ok3, hk _ (by simpa using hm3)⟩

theorem store8K_spec {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {p : BitVec 64} {old : List (BitVec 64)} {r0 r1 r2 r3 r4 r5 r6 r7 : BitVec 64}
    {R : Mem 64 → Prop} {k : Expr Val Cont rs}
    (hlen : old.length = 8) (hm : (array64 p old ⋆ R) m)
    (hk : ∀ m', (array64 p [r0, r1, r2, r3, r4, r5, r6, r7] ⋆ R) m' → wp Γ Q X k m') :
    wp Γ Q X (store8K p r0 r1 r2 r3 r4 r5 r6 r7 k) m := by
  rcases old with
    _ | ⟨o0, _ | ⟨o1, _ | ⟨o2, _ | ⟨o3, _ | ⟨o4, _ | ⟨o5, _ | ⟨o6, _ | ⟨o7, _ | _⟩⟩⟩⟩⟩⟩⟩⟩
    <;> simp at hlen
  have hsplit : array64 p [o0, o1, o2, o3, o4, o5, o6, o7] =
      (array64 p [o0, o1, o2, o3] ⋆ array64 (p + 32) [o4, o5, o6, o7]) :=
    array64_append p [o0, o1, o2, o3] [o4, o5, o6, o7]
  rw [hsplit] at hm
  unfold store8K
  refine store4K_spec (old := [o0, o1, o2, o3]) (R := array64 (p + 32) [o4, o5, o6, o7] ⋆ R)
    rfl (sep_ac hm) fun m1 hm1 => ?_
  wp_unfold
  refine store4K_spec (old := [o4, o5, o6, o7]) (R := array64 p [r0, r1, r2, r3] ⋆ R)
    rfl (sep_ac hm1) fun m2 hm2 => hk m2 ?_
  have hjoin : array64 p [r0, r1, r2, r3, r4, r5, r6, r7] =
      (array64 p [r0, r1, r2, r3] ⋆ array64 (p + 32) [r4, r5, r6, r7]) :=
    array64_append p [r0, r1, r2, r3] [r4, r5, r6, r7]
  rw [hjoin]; exact sep_ac hm2

theorem mulRow0K_spec {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    (a0 a1 a2 a3 b0 : BitVec 64)
    (k : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Expr Val Cont rs)
    (hk : ∀ r0 r1 r2 r3 r4 : BitVec 64,
      limbsVal [r0, r1, r2, r3, r4] = limbsVal [a0, a1, a2, a3] * b0.toNat →
      wp Γ Q X (k r0 r1 r2 r3 r4) m) :
    wp Γ Q X (mulRow0K a0 a1 a2 a3 b0 k) m := by
  unfold mulRow0K; step_limbs
  rename_i r0 h0 hm0 l1 h1 hm1 r1 c0 ha0 l2 h2 hm2 r2 c1 ha1 l3 h3 hm3 r3 c2 ha2 r4 c3 ha3
  refine hk r0 r1 r2 r3 r4 ?_
  have halg := mulRow0_alg hm0 hm1 hm2 hm3 ha0 ha1 ha2 ha3
  have hA : limbsVal [a0, a1, a2, a3] < 2 ^ 64 * (2 ^ 64 * (2 ^ 64 * 2 ^ 64)) := by
    rw [B4_eq_pow256]; exact limbsVal_lt_pow _
  have hlt := mulRowAcc_bound hA (Nat.mul_pos (Nat.two_pow_pos _) (Nat.mul_pos (Nat.two_pow_pos _)
    (Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _)))) b0.isLt
  rw [limbsVal5_eq, limbsVal4_eq]
  exact drop_high_carry halg (by simpa [limbsVal4_eq] using hlt)

theorem mulRowAccK_spec {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    (a0 a1 a2 a3 bj acc0 acc1 acc2 acc3 : BitVec 64)
    (k : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Expr Val Cont rs)
    (hk : ∀ o0 o1 o2 o3 o4 : BitVec 64,
      limbsVal [o0, o1, o2, o3, o4] =
        limbsVal [a0, a1, a2, a3] * bj.toNat + limbsVal [acc0, acc1, acc2, acc3] →
      wp Γ Q X (k o0 o1 o2 o3 o4) m) :
    wp Γ Q X (mulRowAccK a0 a1 a2 a3 bj acc0 acc1 acc2 acc3 k) m := by
  unfold mulRowAccK; step_limbs
  rename_i l0 h0 hm0 o0 cx0 hcx0 l1 h1 hm1 u1 ox0 hox0 o1 cx1 hcx1 l2 h2 hm2 u2 ox1 hox1
    o2 cx2 hcx2 l3 h3 hm3 u3 ox2 hox2 o3 cx3 hcx3 u4 ox3 hox3 o4 cx4 hcx4
  refine hk o0 o1 o2 o3 o4 ?_
  have halg := mulRowAcc_alg hm0 hm1 hm2 hm3 hcx0 hox0 hcx1 hox1 hcx2 hox2 hcx3 hox3 hcx4
  have hA : limbsVal [a0, a1, a2, a3] < 2 ^ 64 * (2 ^ 64 * (2 ^ 64 * 2 ^ 64)) := by
    rw [B4_eq_pow256]; exact limbsVal_lt_pow _
  have hacc : limbsVal [acc0, acc1, acc2, acc3] < 2 ^ 64 * (2 ^ 64 * (2 ^ 64 * 2 ^ 64)) := by
    rw [B4_eq_pow256]; exact limbsVal_lt_pow _
  rw [limbsVal5_eq, limbsVal4_eq, limbsVal4_eq]
  exact drop_high_carry halg (by simpa [limbsVal4_eq] using mulRowAcc_bound hA hacc bj.isLt)

theorem add4K_spec {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64)
    (k : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Bool → Expr Val Cont rs)
    (hk : ∀ (s0 s1 s2 s3 : BitVec 64) (c3 : Bool),
      c3.toNat * 2 ^ 256 + limbsVal [s0, s1, s2, s3] =
        limbsVal [a0, a1, a2, a3] + limbsVal [b0, b1, b2, b3] →
      wp Γ Q X (k s0 s1 s2 s3 c3) m) :
    wp Γ Q X (add4K a0 a1 a2 a3 b0 b1 b2 b3 k) m := by
  unfold add4K; step_limbs; rename_i s0 c0 h0 s1 c1 h1 s2 c2 h2 s3 c3 h3
  refine hk s0 s1 s2 s3 c3 ?_
  have halg := add4_base h0 h1 h2 h3; rw [B4_eq_pow256] at halg; simpa [limbsVal4_eq] using halg

theorem sub4K_spec {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64)
    (k : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Bool → Expr Val Cont rs)
    (hk : ∀ (d0 d1 d2 d3 : BitVec 64) (w3 : Bool),
      limbsVal [d0, d1, d2, d3] + limbsVal [b0, b1, b2, b3] =
        limbsVal [a0, a1, a2, a3] + w3.toNat * 2 ^ 256 →
      wp Γ Q X (k d0 d1 d2 d3 w3) m) :
    wp Γ Q X (sub4K a0 a1 a2 a3 b0 b1 b2 b3 k) m := by
  unfold sub4K; step_limbs; rename_i d0 w0 h0 d1 w1 h1 d2 w2 h2 d3 w3 h3
  refine hk d0 d1 d2 d3 w3 ?_
  have halg := sub4_base h0 h1 h2 h3; rw [B4_eq_pow256] at halg; simpa [limbsVal4_eq] using halg

theorem addImm4K_spec {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    (d0 d1 d2 d3 q0 q1 q2 q3 : BitVec 64)
    (k : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Bool → Expr Val Cont rs)
    (hk : ∀ (s0 s1 s2 s3 : BitVec 64) (c3 : Bool),
      c3.toNat * 2 ^ 256 + limbsVal [s0, s1, s2, s3] =
        limbsVal [d0, d1, d2, d3] + limbsVal [q0, q1, q2, q3] →
      wp Γ Q X (k s0 s1 s2 s3 c3) m) :
    wp Γ Q X (addImm4K d0 d1 d2 d3 q0 q1 q2 q3 k) m := by
  unfold addImm4K; step_limbs; rename_i s0 c0 hc0 s1 c1 hc1 s2 c2 hc2 s3 c3 hc3
  refine hk s0 s1 s2 s3 c3 ?_
  have halg := add4_base hc0 hc1 hc2 hc3; rw [B4_eq_pow256] at halg; simpa [limbsVal4_eq] using halg

theorem select4K_spec {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    (c : Bool) (x0 x1 x2 x3 y0 y1 y2 y3 : BitVec 64)
    (k : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Expr Val Cont rs)
    (hk : wp Γ Q X (if c then k x0 x1 x2 x3 else k y0 y1 y2 y3) m) :
    wp Γ Q X (select4K c x0 x1 x2 x3 y0 y1 y2 y3 k) m := by
  unfold select4K; wp_unfold; cases c <;> exact hk

private theorem load2x4_spec {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {out pa pb : BitVec 64} {as bs out0 : List (BitVec 64)} {R : Mem 64 → Prop}
    {k : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 →
         BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Expr Val Cont rs}
    (has : as.length = 4) (hbs : bs.length = 4)
    (hm : (array64 out out0 ⋆ array64 pa as ⋆ array64 pb bs ⋆ R) m)
    (hk : ∀ a0 a1 a2 a3 b0 b1 b2 b3, as = [a0, a1, a2, a3] → bs = [b0, b1, b2, b3] →
      wp Γ Q X (k a0 a1 a2 a3 b0 b1 b2 b3) m) :
    wp Γ Q X (load4K pa fun a0 a1 a2 a3 => load4K pb fun b0 b1 b2 b3 =>
      k a0 a1 a2 a3 b0 b1 b2 b3) m := by
  obtain ⟨a0, a1, a2, a3, rfl⟩ := list4_eq has
  obtain ⟨b0, b1, b2, b3, rfl⟩ := list4_eq hbs
  refine load4K_spec a0 a1 a2 a3 (R := array64 out out0 ⋆ array64 pb _ ⋆ R) (sep_ac hm) ?_
  refine load4K_spec b0 b1 b2 b3 (R := array64 out out0 ⋆ array64 pa _ ⋆ R) (sep_ac hm) ?_
  exact hk a0 a1 a2 a3 b0 b1 b2 b3 rfl rfl

private theorem select4_store4_spec {Γ : Env} {Q : Post []} {X : XPost} {m : Mem 64}
    {out pa pb : BitVec 64} {as bs out0 : List (BitVec 64)} {R : Mem 64 → Prop}
    (hout : out0.length = 4) (hm : (array64 out out0 ⋆ array64 pa as ⋆ array64 pb bs ⋆ R) m)
    (c : Bool) (x0 x1 x2 x3 y0 y1 y2 y3 : BitVec 64)
    (hk : ∀ m', (array64 out (if c then [x0, x1, x2, x3] else [y0, y1, y2, y3]) ⋆
      array64 pa as ⋆ array64 pb bs ⋆ R) m' → Q () m') :
    wp Γ Q X (select4K c x0 x1 x2 x3 y0 y1 y2 y3 fun r0 r1 r2 r3 =>
      store4K out r0 r1 r2 r3 (.ret ())) m := by
  refine select4K_spec c x0 x1 x2 x3 y0 y1 y2 y3 _ ?_
  cases c <;> refine store4K_spec hout (R := array64 pa as ⋆ array64 pb bs ⋆ R)
    (sep_ac hm) fun m' hm' => by wp_unfold; exact hk m' (sep_ac hm')

private theorem mul4x4_combine {B A b0 b1 b2 b3 r0 r1 r2 t u v w : Nat}
    (e0 : r0 + B * t = A * b0) (e1 : r1 + B * u = A * b1 + t)
    (e2 : r2 + B * v = A * b2 + u) (e3 : w = A * b3 + v) :
    r0 + B * (r1 + B * (r2 + B * w)) = A * (b0 + B * (b1 + B * (b2 + B * b3))) := by
  calc r0 + B * (r1 + B * (r2 + B * w))
      = r0 + B * (r1 + B * ((r2 + B * v) + B * (A * b3))) := by
        rw [e3]; simp only [Nat.mul_add]; ac_rfl
    _ = r0 + B * ((r1 + B * u) + B * (A * b2 + B * (A * b3))) := by
      rw [e2]; simp only [Nat.mul_add]; ac_rfl
    _ = (r0 + B * t) + B * (A * b1 + B * (A * b2 + B * (A * b3))) := by
      rw [e1]; simp only [Nat.mul_add]; ac_rfl
    _ = A * b0 + B * (A * b1 + B * (A * b2 + B * (A * b3))) := by rw [e0]
    _ = A * (b0 + B * (b1 + B * (b2 + B * b3))) := by
          simp only [Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm B A]

private theorem mul4x4_rows_spec {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64)
    (k : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 →
         BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Expr Val Cont rs)
    (hk : ∀ r0 r1 r2 r3 r4 r5 r6 r7 : BitVec 64,
      limbsVal [r0, r1, r2, r3, r4, r5, r6, r7] =
        limbsVal [a0, a1, a2, a3] * limbsVal [b0, b1, b2, b3] →
      wp Γ Q X (k r0 r1 r2 r3 r4 r5 r6 r7) m) :
    wp Γ Q X
      (mulRow0K a0 a1 a2 a3 b0 fun r0 t1 t2 t3 t4 =>
       mulRowAccK a0 a1 a2 a3 b1 t1 t2 t3 t4 fun r1 u2 u3 u4 u5 =>
       mulRowAccK a0 a1 a2 a3 b2 u2 u3 u4 u5 fun r2 v3 v4 v5 v6 =>
       mulRowAccK a0 a1 a2 a3 b3 v3 v4 v5 v6 fun r3 r4 r5 r6 r7 =>
       k r0 r1 r2 r3 r4 r5 r6 r7) m := by
  refine mulRow0K_spec a0 a1 a2 a3 b0 _ fun r0 t1 t2 t3 t4 hr0 => ?_
  refine mulRowAccK_spec a0 a1 a2 a3 b1 t1 t2 t3 t4 _ fun r1 u2 u3 u4 u5 hr1 => ?_
  refine mulRowAccK_spec a0 a1 a2 a3 b2 u2 u3 u4 u5 _ fun r2 v3 v4 v5 v6 hr2 => ?_
  refine mulRowAccK_spec a0 a1 a2 a3 b3 v3 v4 v5 v6 _ fun r3 r4 r5 r6 r7 hr3 => ?_
  refine hk r0 r1 r2 r3 r4 r5 r6 r7 ?_
  have hcomb := mul4x4_combine (B := 2 ^ 64) (A := limbsVal [a0, a1, a2, a3])
    (by simpa [limbsVal] using hr0) (by simpa [limbsVal] using hr1)
    (by simpa [limbsVal] using hr2) hr3
  simpa [limbsVal4_eq, limbsVal] using hcomb

end LimbSchoolbookKit

/-! ## Top-level `wp` correctness proofs -/

theorem mul4x4_correct (Γ : Env) :
    ∀ args m Q X, mul4x4Spec args m Q X → Func.spec Γ mul4x4 args m Q X := by
  rintro ⟨out, pa, pb, ⟨⟩⟩ m Q X ⟨as, bs, out0, R, has, hbs, hout, hm, hQ⟩
  dsimp only [Func.spec, Func.wp, mul4x4]
  refine load2x4_spec has hbs hm fun a0 a1 a2 a3 b0 b1 b2 b3 has_eq hbs_eq => ?_
  subst has_eq; subst hbs_eq
  refine mul4x4_rows_spec a0 a1 a2 a3 b0 b1 b2 b3 _ fun r0 r1 r2 r3 r4 r5 r6 r7 hval => ?_
  refine store8K_spec hout (R := array64 pa [a0, a1, a2, a3] ⋆ array64 pb [b0, b1, b2, b3] ⋆ R)
    (sep_ac hm) fun m' hm' => by wp_unfold; exact hQ _ m' rfl hval (sep_ac hm')

theorem addMod25519_correct (Γ : Env) :
    ∀ args m Q X, addMod25519Spec args m Q X → Func.spec Γ addMod25519 args m Q X := by
  rintro ⟨out, pa, pb, ⟨⟩⟩ m Q X ⟨as, bs, out0, R, has, hbs, hout, hAlt, hBlt, hm, hQ⟩
  dsimp only [Func.spec, Func.wp, addMod25519]
  refine load2x4_spec has hbs hm fun a0 a1 a2 a3 b0 b1 b2 b3 has_eq hbs_eq => ?_
  subst has_eq; subst hbs_eq
  refine add4K_spec a0 a1 a2 a3 b0 b1 b2 b3 _ fun s0 s1 s2 s3 c3 hsum => ?_
  have hSlt : limbsVal [a0, a1, a2, a3] + limbsVal [b0, b1, b2, b3] < 2 ^ 256 := by
    have h2 := two_p25519_lt
    generalize (2 : Nat) ^ 256 = M at h2 ⊢; generalize p25519 = P at hAlt hBlt h2; omega
  have hS := drop_high_carry hsum hSlt
  step_limbs; rename_i d0 w0 hw0 d1 w1 hw1 d2 w2 hw2 d3 w3 hw3
  have hsub : limbsVal [d0, d1, d2, d3] + p25519 =
      limbsVal [s0, s1, s2, s3] + w3.toNat * 2 ^ 256 := by
    have h := sub4_base hw0 hw1 hw2 hw3; rw [B4_eq_pow256] at h
    rw [← limbsVal_p25519, limbsVal4_eq, limbsVal4_eq, limbsVal4_eq]; exact h
  clear hw0 hw1 hw2 hw3 hsum hSlt
  have hDlt := limbsVal4_lt_pow256 d0 d1 d2 d3
  refine select4_store4_spec hout hm w3 s0 s1 s2 s3 d0 d1 d2 d3 fun m' hm' => ?_
  generalize (2 : Nat) ^ 256 = M at hsub hDlt; generalize p25519 = P at hAlt hBlt hsub hQ
  cases w3
  · simp only [Bool.false_eq_true, ↓reduceIte, Bool.toNat_false, Nat.zero_mul, Nat.add_zero]
      at hsub hm' ⊢
    have hDltP : limbsVal [d0, d1, d2, d3] < P := by omega
    have hmod : limbsVal [d0, d1, d2, d3] =
        (limbsVal [a0, a1, a2, a3] + limbsVal [b0, b1, b2, b3]) % P := by
      rw [← hS, ← hsub, Nat.add_mod_right, Nat.mod_eq_of_lt hDltP]
    exact hQ _ m' rfl hmod hDltP hm'
  · simp only [↓reduceIte, Bool.toNat_true, Nat.one_mul] at hsub hm' ⊢
    have hSltP : limbsVal [s0, s1, s2, s3] < P := by omega
    have hmod : limbsVal [s0, s1, s2, s3] =
        (limbsVal [a0, a1, a2, a3] + limbsVal [b0, b1, b2, b3]) % P := by
      rw [← hS, Nat.mod_eq_of_lt hSltP]
    exact hQ _ m' rfl hmod hSltP hm'

private theorem subMod_arith {A B D S P M : Nat} {w c : Bool}
    (hA : A < P) (hB : B < P) (hD : D < M) (hS : S < M)
    (hsub : D + B = A + w.toNat * M) (hadd : c.toNat * M + S = D + P) :
    (w = false → D = (if B ≤ A then A - B else A + P - B) ∧ D < P) ∧
    (w = true → S = (if B ≤ A then A - B else A + P - B) ∧ S < P) := by
  constructor
  · intro hw; subst hw; simp only [Bool.toNat_false, Nat.zero_mul, Nat.add_zero] at hsub
    have hle : B ≤ A := by omega
    simp only [hle, ↓reduceIte]; omega
  · intro hw; subst hw; simp only [Bool.toNat_true, Nat.one_mul] at hsub
    have hgt : ¬ B ≤ A := by omega
    cases c
    · simp only [Bool.toNat_false, Nat.zero_mul, Nat.zero_add] at hadd; omega
    · simp only [Bool.toNat_true, Nat.one_mul] at hadd; simp only [hgt, ↓reduceIte]; omega

theorem subMod25519_correct (Γ : Env) :
    ∀ args m Q X, subMod25519Spec args m Q X → Func.spec Γ subMod25519 args m Q X := by
  rintro ⟨out, pa, pb, ⟨⟩⟩ m Q X ⟨as, bs, out0, R, has, hbs, hout, hAlt, hBlt, hm, hQ⟩
  dsimp only [Func.spec, Func.wp, subMod25519]
  refine load2x4_spec has hbs hm fun a0 a1 a2 a3 b0 b1 b2 b3 has_eq hbs_eq => ?_
  subst has_eq; subst hbs_eq
  refine sub4K_spec a0 a1 a2 a3 b0 b1 b2 b3 _ fun d0 d1 d2 d3 w3 hsub => ?_
  refine addImm4K_spec d0 d1 d2 d3 p0 p1 p2 p3 _ fun s0 s1 s2 s3 c3 hadd => ?_
  rw [limbsVal_p25519] at hadd
  have ⟨hf, ht⟩ := subMod_arith hAlt hBlt (limbsVal4_lt_pow256 d0 d1 d2 d3)
    (limbsVal4_lt_pow256 s0 s1 s2 s3) hsub hadd
  refine select4_store4_spec hout hm w3 s0 s1 s2 s3 d0 d1 d2 d3 fun m' hm' => ?_
  cases w3
  · simp only [Bool.false_eq_true, ↓reduceIte] at hm'
    exact hQ _ m' rfl (hf rfl).1 (hf rfl).2 hm'
  · simp only [↓reduceIte] at hm'
    exact hQ _ m' rfl (ht rfl).1 (ht rfl).2 hm'

/-! ## `Func.Wf` proofs (`t_wf_reify`) -/

theorem mul4x4_wf : Func.Wf mul4x4 := by t_wf_reify
theorem addMod25519_wf : Func.Wf addMod25519 := by t_wf_reify
theorem subMod25519_wf : Func.Wf subMod25519 := by t_wf_reify

/-! ## `Module`, `Env`, and `ModuleOk` bundles -/

def mul4x4Module : Module := ⟨[mul4x4Fn], [], []⟩
def addMod25519Module : Module := ⟨[addMod25519Fn], [], []⟩
def subMod25519Module : Module := ⟨[subMod25519Fn], [], []⟩

def bignumEnv : Env
  | "mul4x4",      [.bits 64, .bits 64, .bits 64], [] => mul4x4Spec
  | "addMod25519", [.bits 64, .bits 64, .bits 64], [] => addMod25519Spec
  | "subMod25519", [.bits 64, .bits 64, .bits 64], [] => subMod25519Spec
  | _, _, _ => fun _ _ _ _ => False

theorem mul4x4Module_checkAcyclic : mul4x4Module.checkAcyclic = true := by rfl
theorem addMod25519Module_checkAcyclic : addMod25519Module.checkAcyclic = true := by rfl
theorem subMod25519Module_checkAcyclic : subMod25519Module.checkAcyclic = true := by rfl

private theorem single_moduleOk {fn : Fn}
    (hacyc : ({ fns := [fn], externs := [], exits := [] } : Module).checkAcyclic = true)
    (hwf : fn.Wf)
    (hcorr : ∀ xs m Q X,
      bignumEnv fn.name fn.as fn.rs xs m Q X → Func.wp bignumEnv fn.body xs m Q X) :
    ModuleOk bignumEnv ⟨[fn], [], []⟩ :=
  Module.moduleOk_of_checkAcyclic hacyc
    (fun f h => by simp at h; subst h; exact hwf)
    (fun f h => by simp at h; subst h; exact hcorr)

theorem mul4x4_moduleOk : ModuleOk bignumEnv mul4x4Module :=
  single_moduleOk mul4x4Module_checkAcyclic mul4x4_wf (mul4x4_correct bignumEnv)

theorem addMod25519_moduleOk : ModuleOk bignumEnv addMod25519Module :=
  single_moduleOk addMod25519Module_checkAcyclic addMod25519_wf (addMod25519_correct bignumEnv)

theorem subMod25519_moduleOk : ModuleOk bignumEnv subMod25519Module :=
  single_moduleOk subMod25519Module_checkAcyclic subMod25519_wf (subMod25519_correct bignumEnv)

end LeanQbe.T.Examples.Bignum