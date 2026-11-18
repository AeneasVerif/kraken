module

public import LeanQbe.T.Notation
public import LeanQbe.T.Logic.Rules
public import LeanQbe.T.WfLemmas

/-!
# T13: 4×4-limb Bignum Multiply and Modular Add/Sub mod `2^255 - 19` (`K1b`)

100%-PHOAS typed IR programs and `wp` proofs against `Nat` (no `TFlat` dependencies, no n-limb
loops per G10, constant-time `select` with zero secret-dependent branches per G2):

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

def p0 : BitVec 64 := 0xffffffffffffffed#64
def p1 : BitVec 64 := 0xffffffffffffffff#64
def p2 : BitVec 64 := 0xffffffffffffffff#64
def p3 : BitVec 64 := 0x7fffffffffffffff#64

/-! ## PHOAS IR building blocks and top-level functions -/

def load4K {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} (p : V i64)
    (k : V i64 → V i64 → V i64 → V i64 → Expr V L rs) : Expr V L rs :=
  tqbe {
    %x0:l = load %p
    %p1:l = add %p, 8
    %x1:l = load %p1
    %p2:l = add %p, 16
    %x2:l = load %p2
    %p3:l = add %p, 24
    %x3:l = load %p3
    ⟨k x0 x1 x2 x3⟩
  }

def store4K {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (p x0 x1 x2 x3 : V i64) (k : Expr V L rs) : Expr V L rs :=
  tqbe {
    store %x0, %p
    %p1:l = add %p, 8
    store %x1, %p1
    %p2:l = add %p, 16
    store %x2, %p2
    %p3:l = add %p, 24
    store %x3, %p3
    ⟨k⟩
  }

def store8K {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (p r0 r1 r2 r3 r4 r5 r6 r7 : V i64) (k : Expr V L rs) : Expr V L rs :=
  tqbe {
    use store4K(%p, %r0, %r1, %r2, %r3)
    %hi:l = add %p, 32
    use store4K(%hi, %r4, %r5, %r6, %r7)
    ⟨k⟩
  }

/-- Row 0 of 4×4 schoolbook multiply: `a[0..3] * b0` (4 `umulw` + 4 `addc`). -/
def mulRow0K {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (a0 a1 a2 a3 b0 : V i64)
    (k : V i64 → V i64 → V i64 → V i64 → V i64 → Expr V L rs) : Expr V L rs :=
  tqbe {
    %r0:l, %h0:l = umulw %a0, %b0
    %l1:l, %h1:l = umulw %a1, %b0
    %r1:l, %c0:b = addc %h0, %l1, false
    %l2:l, %h2:l = umulw %a2, %b0
    %r2:l, %c1:b = addc %h1, %l2, %c0
    %l3:l, %h3:l = umulw %a3, %b0
    %r3:l, %c2:b = addc %h2, %l3, %c1
    %r4:l, %_:b  = addc %h3, 0, %c2
    ⟨k r0 r1 r2 r3 r4⟩
  }

/-- Rows 1..3 of 4×4 schoolbook multiply: `a[0..3] * bj + acc[0..3]` using `umulw` and two
independent carry chains (`%cx*` for `adcx`, `%ox*` for `adox`). -/
def mulRowAccK {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (a0 a1 a2 a3 bj acc0 acc1 acc2 acc3 : V i64)
    (k : V i64 → V i64 → V i64 → V i64 → V i64 → Expr V L rs) : Expr V L rs :=
  tqbe {
    %l0:l, %h0:l = umulw %a0, %bj
    %o0:l, %cx0:b = addc %acc0, %l0, false
    %l1:l, %h1:l = umulw %a1, %bj
    %u1:l, %ox0:b = addc %acc1, %h0, false
    %o1:l, %cx1:b = addc %u1, %l1, %cx0
    %l2:l, %h2:l = umulw %a2, %bj
    %u2:l, %ox1:b = addc %acc2, %h1, %ox0
    %o2:l, %cx2:b = addc %u2, %l2, %cx1
    %l3:l, %h3:l = umulw %a3, %bj
    %u3:l, %ox2:b = addc %acc3, %h2, %ox1
    %o3:l, %cx3:b = addc %u3, %l3, %cx2
    %u4:l, %_:b   = addc %h3, 0, %ox2
    %o4:l, %_:b   = addc %u4, 0, %cx3
    ⟨k o0 o1 o2 o3 o4⟩
  }

/-- 4-limb addition with carry out. -/
def add4K {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (a0 a1 a2 a3 b0 b1 b2 b3 : V i64)
    (k : V i64 → V i64 → V i64 → V i64 → V .bool → Expr V L rs) : Expr V L rs :=
  tqbe {
    %s0:l, %c0:b = addc %a0, %b0, false
    %s1:l, %c1:b = addc %a1, %b1, %c0
    %s2:l, %c2:b = addc %a2, %b2, %c1
    %s3:l, %c3:b = addc %a3, %b3, %c2
    ⟨k s0 s1 s2 s3 c3⟩
  }

/-- 4-limb subtraction with borrow out. -/
def sub4K {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (a0 a1 a2 a3 b0 b1 b2 b3 : V i64)
    (k : V i64 → V i64 → V i64 → V i64 → V .bool → Expr V L rs) : Expr V L rs :=
  tqbe {
    %d0:l, %w0:b = subb %a0, %b0, false
    %d1:l, %w1:b = subb %a1, %b1, %w0
    %d2:l, %w2:b = subb %a2, %b2, %w1
    %d3:l, %w3:b = subb %a3, %b3, %w2
    ⟨k d0 d1 d2 d3 w3⟩
  }

/-- Constant-time 4-limb conditional select (`cmovcc`/`CSEL`, no branch). -/
def select4K {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (c : V .bool) (x0 x1 x2 x3 y0 y1 y2 y3 : V i64)
    (k : V i64 → V i64 → V i64 → V i64 → Expr V L rs) : Expr V L rs :=
  tqbe {
    %r0:l = select %c, %x0, %y0
    %r1:l = select %c, %x1, %y1
    %r2:l = select %c, %x2, %y2
    %r3:l = select %c, %x3, %y3
    ⟨k r0 r1 r2 r3⟩
  }

/-- `mul4x4(out, a, b)`: 4×4-limb schoolbook multiply (`out[0..7] := a[0..3] * b[0..3]`). -/
def mul4x4 : Func [i64, i64, i64] [] :=
  tqbe(%out:l, %pa:l, %pb:l) -> () {
    %a0:l, %a1:l, %a2:l, %a3:l <- load4K(%pa)
    %b0:l, %b1:l, %b2:l, %b3:l <- load4K(%pb)
    %r0:l, %t1:l, %t2:l, %t3:l, %t4:l <- mulRow0K(%a0, %a1, %a2, %a3, %b0)
    %r1:l, %u2:l, %u3:l, %u4:l, %u5:l <- mulRowAccK(%a0, %a1, %a2, %a3, %b1, %t1, %t2, %t3, %t4)
    %r2:l, %v3:l, %v4:l, %v5:l, %v6:l <- mulRowAccK(%a0, %a1, %a2, %a3, %b2, %u2, %u3, %u4, %u5)
    %r3:l, %r4:l, %r5:l, %r6:l, %r7:l <- mulRowAccK(%a0, %a1, %a2, %a3, %b3, %v3, %v4, %v5, %v6)
    use store8K(%out, %r0, %r1, %r2, %r3, %r4, %r5, %r6, %r7)
    ret
  }

/-- `addMod25519(out, a, b)`: constant-time 4-limb `(a + b) mod (2^255 - 19)`. -/
def addMod25519 : Func [i64, i64, i64] [] :=
  tqbe(%out:l, %pa:l, %pb:l) -> () {
    %a0:l, %a1:l, %a2:l, %a3:l <- load4K(%pa)
    %b0:l, %b1:l, %b2:l, %b3:l <- load4K(%pb)
    %s0:l, %s1:l, %s2:l, %s3:l, %_:b <- add4K(%a0, %a1, %a2, %a3, %b0, %b1, %b2, %b3)
    %d0:l, %w0:b = subb %s0, imm ⟨p0⟩, false
    %d1:l, %w1:b = subb %s1, imm ⟨p1⟩, %w0
    %d2:l, %w2:b = subb %s2, imm ⟨p2⟩, %w1
    %d3:l, %w3:b = subb %s3, imm ⟨p3⟩, %w2
    %r0:l, %r1:l, %r2:l, %r3:l <- select4K(%w3, %s0, %s1, %s2, %s3, %d0, %d1, %d2, %d3)
    use store4K(%out, %r0, %r1, %r2, %r3)
    ret
  }

/-- 4-limb addition by immediate 64-bit limbs `q0..q3` with carry out. -/
def addImm4K {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (d0 d1 d2 d3 : V i64) (q0 q1 q2 q3 : BitVec 64)
    (k : V i64 → V i64 → V i64 → V i64 → V .bool → Expr V L rs) : Expr V L rs :=
  tqbe {
    %s0:l, %c0:b = addc %d0, imm ⟨q0⟩, false
    %s1:l, %c1:b = addc %d1, imm ⟨q1⟩, %c0
    %s2:l, %c2:b = addc %d2, imm ⟨q2⟩, %c1
    %s3:l, %c3:b = addc %d3, imm ⟨q3⟩, %c2
    ⟨k s0 s1 s2 s3 c3⟩
  }

/-- `subMod25519(out, a, b)`: constant-time 4-limb `(a - b) mod (2^255 - 19)`. -/
def subMod25519 : Func [i64, i64, i64] [] :=
  tqbe(%out:l, %pa:l, %pb:l) -> () {
    %a0:l, %a1:l, %a2:l, %a3:l <- load4K(%pa)
    %b0:l, %b1:l, %b2:l, %b3:l <- load4K(%pb)
    %d0:l, %d1:l, %d2:l, %d3:l, %w3:b <- sub4K(%a0, %a1, %a2, %a3, %b0, %b1, %b2, %b3)
    %s0:l, %s1:l, %s2:l, %s3:l, %_:b <- addImm4K(%d0, %d1, %d2, %d3, ⟨p0⟩, ⟨p1⟩, ⟨p2⟩, ⟨p3⟩)
    %r0:l, %r1:l, %r2:l, %r3:l <- select4K(%w3, %s0, %s1, %s2, %s3, %d0, %d1, %d2, %d3)
    use store4K(%out, %r0, %r1, %r2, %r3)
    ret
  }

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

theorem limbsVal_lt_pow {n : Nat} : ∀ (xs : List (BitVec n)), limbsVal xs < 2 ^ (n * xs.length)
  | [] => by simp
  | x :: xs => by
    simp only [limbsVal_cons, List.length_cons]
    have hx : x.toNat < 2 ^ n := x.isLt
    have hxs : limbsVal xs < 2 ^ (n * xs.length) := limbsVal_lt_pow xs
    have h2 : 2 ^ n * (limbsVal xs + 1) ≤ 2 ^ n * 2 ^ (n * xs.length) := Nat.mul_le_mul_left _ hxs
    rw [Nat.mul_add, Nat.mul_one] at h2
    rw [show n * (xs.length + 1) = n + n * xs.length by rw [Nat.mul_succ, Nat.add_comm], Nat.pow_add]
    exact Nat.lt_of_lt_of_le (Nat.add_lt_add_right hx _) (Nat.add_comm (2 ^ n) _ ▸ h2)

theorem limbsVal4_lt_pow256 (x0 x1 x2 x3 : BitVec 64) : limbsVal [x0, x1, x2, x3] < 2 ^ 256 := by
  have h := limbsVal_lt_pow [x0, x1, x2, x3]
  have he : (2 : Nat) ^ (64 * ([x0, x1, x2, x3] : List (BitVec 64)).length) = 2 ^ 256 :=
    congrArg (2 ^ ·) rfl
  rwa [he] at h

theorem limbsVal4_eq (x0 x1 x2 x3 : BitVec 64) :
    limbsVal [x0, x1, x2, x3] =
      x0.toNat + 2 ^ 64 * (x1.toNat + 2 ^ 64 * (x2.toNat + 2 ^ 64 * x3.toNat)) := by
  simp [limbsVal]

theorem limbsVal5_eq (x0 x1 x2 x3 x4 : BitVec 64) :
    limbsVal [x0, x1, x2, x3, x4] =
      x0.toNat + 2 ^ 64 * (x1.toNat + 2 ^ 64 * (x2.toNat + 2 ^ 64 * (x3.toNat + 2 ^ 64 * x4.toNat))) := by
  simp [limbsVal]

private theorem subk_telescope {k x y : Nat} (hx : k ≤ x) (hy : 1 ≤ y) :
    (x - k) + x * (y - 1) = x * y - k := by
  rw [Nat.mul_sub_left_distrib, Nat.mul_one]
  have hle : x ≤ x * y := Nat.le_mul_of_pos_right x hy
  omega

theorem limbsVal_p25519 : limbsVal [p0, p1, p2, p3] = p25519 := by
  have hp0 : p0.toNat = 2 ^ 64 - 19 := by decide
  have hp1 : p1.toNat = 2 ^ 64 - 1 := by decide
  have hp2 : p2.toNat = 2 ^ 64 - 1 := by decide
  have hp3 : p3.toNat = 2 ^ 63 - 1 := by decide
  have s1 : (2 ^ 64 - 1) + 2 ^ 64 * (2 ^ 63 - 1) = 2 ^ 127 - 1 := by
    rw [subk_telescope (Nat.one_le_pow _ _ (by decide)) (Nat.one_le_pow _ _ (by decide)), ← Nat.pow_add]
  have s2 : (2 ^ 64 - 1) + 2 ^ 64 * (2 ^ 127 - 1) = 2 ^ 191 - 1 := by
    rw [subk_telescope (Nat.one_le_pow _ _ (by decide)) (Nat.one_le_pow _ _ (by decide)), ← Nat.pow_add]
  have s3 : (2 ^ 64 - 19) + 2 ^ 64 * (2 ^ 191 - 1) = 2 ^ 255 - 19 := by
    rw [subk_telescope (by decide : 19 ≤ 2 ^ 64) (Nat.one_le_pow _ _ (by decide)), ← Nat.pow_add]
  rw [limbsVal4_eq, hp0, hp1, hp2, hp3, s1, s2, s3]; rfl

theorem two_p25519_lt : 2 * p25519 < 2 ^ 256 := by
  have h256 : (2 : Nat) ^ 256 = 2 * 2 ^ 255 := by
    rw [show (256 : Nat) = 1 + 255 from rfl, Nat.pow_add, Nat.pow_one]
  unfold p25519
  have h19 : 19 ≤ (2 : Nat) ^ 255 := Nat.le_trans (by decide : 19 ≤ 2 ^ 64)
    (Nat.pow_le_pow_right (by decide) (by decide))
  rw [h256]
  generalize (2 : Nat) ^ 255 = K at h19 ⊢
  omega

private theorem add4_base {B a0 a1 a2 a3 b0 b1 b2 b3 s0 s1 s2 s3 : Nat} {c0 c1 c2 c3 : Bool}
    (h0 : c0.toNat * B + s0 = a0 + b0)
    (h1 : c1.toNat * B + s1 = a1 + b1 + c0.toNat)
    (h2 : c2.toNat * B + s2 = a2 + b2 + c1.toNat)
    (h3 : c3.toNat * B + s3 = a3 + b3 + c2.toNat) :
    c3.toNat * (B * (B * (B * B))) + (s0 + B * (s1 + B * (s2 + B * s3))) =
      (a0 + B * (a1 + B * (a2 + B * a3))) + (b0 + B * (b1 + B * (b2 + B * b3))) := by
  calc c3.toNat * (B * (B * (B * B))) + (s0 + B * (s1 + B * (s2 + B * s3)))
      = s0 + B * (s1 + B * (s2 + B * (c3.toNat * B + s3))) := by
          simp only [Nat.mul_add, ← Nat.mul_assoc]; ac_rfl
    _ = s0 + B * (s1 + B * ((c2.toNat * B + s2) + B * (a3 + b3))) := by
          rw [h3]; simp only [Nat.mul_add]; ac_rfl
    _ = s0 + B * ((c1.toNat * B + s1) + B * ((a2 + b2) + B * (a3 + b3))) := by
          rw [h2]; simp only [Nat.mul_add]; ac_rfl
    _ = (c0.toNat * B + s0) + B * ((a1 + b1) + B * ((a2 + b2) + B * (a3 + b3))) := by
          rw [h1]; simp only [Nat.mul_add]; ac_rfl
    _ = (a0 + b0) + B * ((a1 + b1) + B * ((a2 + b2) + B * (a3 + b3))) := by rw [h0]
    _ = (a0 + B * (a1 + B * (a2 + B * a3))) + (b0 + B * (b1 + B * (b2 + B * b3))) := by
          simp only [Nat.mul_add]; ac_rfl

private theorem sub4_base {B a0 a1 a2 a3 b0 b1 b2 b3 d0 d1 d2 d3 : Nat} {w0 w1 w2 w3 : Bool}
    (h0 : d0 + b0 = a0 + w0.toNat * B)
    (h1 : d1 + b1 + w0.toNat = a1 + w1.toNat * B)
    (h2 : d2 + b2 + w1.toNat = a2 + w2.toNat * B)
    (h3 : d3 + b3 + w2.toNat = a3 + w3.toNat * B) :
    (d0 + B * (d1 + B * (d2 + B * d3))) + (b0 + B * (b1 + B * (b2 + B * b3))) =
      (a0 + B * (a1 + B * (a2 + B * a3))) + w3.toNat * (B * (B * (B * B))) := by
  calc (d0 + B * (d1 + B * (d2 + B * d3))) + (b0 + B * (b1 + B * (b2 + B * b3)))
      = (d0 + b0) + B * ((d1 + b1) + B * ((d2 + b2) + B * (d3 + b3))) := by
          simp only [Nat.mul_add]; ac_rfl
    _ = a0 + B * ((d1 + b1 + w0.toNat) + B * ((d2 + b2) + B * (d3 + b3))) := by
          rw [h0]; simp only [Nat.mul_add]; ac_rfl
    _ = a0 + B * (a1 + B * ((d2 + b2 + w1.toNat) + B * (d3 + b3))) := by
          rw [h1]; simp only [Nat.mul_add]; ac_rfl
    _ = a0 + B * (a1 + B * (a2 + B * (d3 + b3 + w2.toNat))) := by
          rw [h2]; simp only [Nat.mul_add]; ac_rfl
    _ = a0 + B * (a1 + B * (a2 + B * (a3 + w3.toNat * B))) := by rw [h3]
    _ = (a0 + B * (a1 + B * (a2 + B * a3))) + w3.toNat * (B * (B * (B * B))) := by
          simp only [Nat.mul_add, ← Nat.mul_assoc]; ac_rfl

private theorem B4_eq_pow256 : (2 : Nat) ^ 64 * (2 ^ 64 * (2 ^ 64 * 2 ^ 64)) = 2 ^ 256 := by
  rw [← Nat.pow_add, ← Nat.pow_add, ← Nat.pow_add]

private theorem mulRow0_alg {B a0 a1 a2 a3 b0 r0 h0 l1 h1 r1 l2 h2 r2 l3 h3 r3 r4 : Nat}
    {c0 c1 c2 c3 : Bool}
    (hm0 : h0 * B + r0 = a0 * b0) (hm1 : h1 * B + l1 = a1 * b0)
    (hm2 : h2 * B + l2 = a2 * b0) (hm3 : h3 * B + l3 = a3 * b0)
    (ha0 : c0.toNat * B + r1 = h0 + l1)
    (ha1 : c1.toNat * B + r2 = h1 + l2 + c0.toNat)
    (ha2 : c2.toNat * B + r3 = h2 + l3 + c1.toNat)
    (ha3 : c3.toNat * B + r4 = h3 + c2.toNat) :
    c3.toNat * (B * (B * (B * (B * B)))) +
      (r0 + B * (r1 + B * (r2 + B * (r3 + B * r4)))) =
      (a0 + B * (a1 + B * (a2 + B * a3))) * b0 := by
  calc c3.toNat * (B * (B * (B * (B * B)))) + (r0 + B * (r1 + B * (r2 + B * (r3 + B * r4))))
      = r0 + B * (r1 + B * (r2 + B * (r3 + B * (c3.toNat * B + r4)))) := by
          simp only [Nat.mul_add, ← Nat.mul_assoc]; ac_rfl
    _ = r0 + B * (r1 + B * (r2 + B * ((c2.toNat * B + r3) + B * h3))) := by
          rw [ha3]; simp only [Nat.mul_add]; ac_rfl
    _ = r0 + B * (r1 + B * ((c1.toNat * B + r2) + B * (h2 + (l3 + B * h3)))) := by
          rw [ha2]; simp only [Nat.mul_add]; ac_rfl
    _ = r0 + B * ((c0.toNat * B + r1) + B * (h1 + l2 + B * (h2 + (l3 + B * h3)))) := by
          rw [ha1]; simp only [Nat.mul_add]; ac_rfl
    _ = (r0 + B * h0) + B * ((l1 + B * h1) + B * ((l2 + B * h2) + B * (l3 + B * h3))) := by
          rw [ha0]; simp only [Nat.mul_add]; ac_rfl
    _ = a0 * b0 + B * (a1 * b0 + B * (a2 * b0 + B * (a3 * b0))) := by
          rw [Nat.add_comm r0, Nat.mul_comm B h0, hm0,
              Nat.add_comm l1, Nat.mul_comm B h1, hm1,
              Nat.add_comm l2, Nat.mul_comm B h2, hm2,
              Nat.add_comm l3, Nat.mul_comm B h3, hm3]
    _ = (a0 + B * (a1 + B * (a2 + B * a3))) * b0 := by
          simp only [Nat.add_mul, Nat.mul_assoc]

private theorem mulRowAcc_alg
    {B a0 a1 a2 a3 bj acc0 acc1 acc2 acc3 l0 h0 l1 h1 l2 h2 l3 h3 u1 u2 u3 u4 o0 o1 o2 o3 o4 : Nat}
    {cx0 cx1 cx2 cx3 cx4 ox0 ox1 ox2 ox3 : Bool}
    (hm0 : h0 * B + l0 = a0 * bj) (hm1 : h1 * B + l1 = a1 * bj)
    (hm2 : h2 * B + l2 = a2 * bj) (hm3 : h3 * B + l3 = a3 * bj)
    (hcx0 : cx0.toNat * B + o0 = acc0 + l0)
    (hox0 : ox0.toNat * B + u1 = acc1 + h0)
    (hcx1 : cx1.toNat * B + o1 = u1 + l1 + cx0.toNat)
    (hox1 : ox1.toNat * B + u2 = acc2 + h1 + ox0.toNat)
    (hcx2 : cx2.toNat * B + o2 = u2 + l2 + cx1.toNat)
    (hox2 : ox2.toNat * B + u3 = acc3 + h2 + ox1.toNat)
    (hcx3 : cx3.toNat * B + o3 = u3 + l3 + cx2.toNat)
    (hox3 : ox3.toNat * B + u4 = h3 + ox2.toNat)
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
    _ = o0 + B * (o1 + B * ((cx2.toNat * B + o2) + B * (acc3 + h2 + ox1.toNat + (l3 + B * h3)))) := by
          rw [hox2]; simp only [Nat.mul_add]; ac_rfl
    _ = o0 + B * (o1 + B * ((ox1.toNat * B + u2) + l2 + cx1.toNat + B * (acc3 + h2 + (l3 + B * h3)))) := by
          rw [hcx2]; simp only [Nat.mul_add]; ac_rfl
    _ = o0 + B * ((cx1.toNat * B + o1) + B * (acc2 + h1 + ox0.toNat + l2 + B * (acc3 + h2 + (l3 + B * h3)))) := by
          rw [hox1]; simp only [Nat.mul_add]; ac_rfl
    _ = o0 + B * ((ox0.toNat * B + u1) + l1 + cx0.toNat + B * (acc2 + h1 + l2 + B * (acc3 + h2 + (l3 + B * h3)))) := by
          rw [hcx1]; simp only [Nat.mul_add]; ac_rfl
    _ = (cx0.toNat * B + o0) + B * (acc1 + h0 + l1 + B * (acc2 + h1 + l2 + B * (acc3 + h2 + (l3 + B * h3)))) := by
          rw [hox0]; simp only [Nat.mul_add]; ac_rfl
    _ = ((l0 + B * h0) + B * ((l1 + B * h1) + B * ((l2 + B * h2) + B * (l3 + B * h3)))) +
        (acc0 + B * (acc1 + B * (acc2 + B * acc3))) := by
          rw [hcx0]; simp only [Nat.mul_add]; ac_rfl
    _ = (a0 * bj + B * (a1 * bj + B * (a2 * bj + B * (a3 * bj)))) +
        (acc0 + B * (acc1 + B * (acc2 + B * acc3))) := by
          rw [Nat.add_comm l0, Nat.mul_comm B h0, hm0,
              Nat.add_comm l1, Nat.mul_comm B h1, hm1,
              Nat.add_comm l2, Nat.mul_comm B h2, hm2,
              Nat.add_comm l3, Nat.mul_comm B h3, hm3]
    _ = (a0 + B * (a1 + B * (a2 + B * a3))) * bj +
        (acc0 + B * (acc1 + B * (acc2 + B * acc3))) := by
          simp only [Nat.add_mul, Nat.mul_assoc]

private theorem mulRowAcc_bound {B A acc b : Nat}
    (hA : A < B * (B * (B * B))) (hacc : acc < B * (B * (B * B))) (hb : b < B) :
    A * b + acc < B * (B * (B * (B * B))) := by
  let B4 := B * (B * (B * B))
  have h1 : A * b + acc < A * b + B4 := Nat.add_lt_add_left hacc _
  have h2 : A * b + B4 ≤ B4 * b + B4 := Nat.add_le_add_right (Nat.mul_le_mul_right _ (Nat.le_of_lt hA)) _
  have h3 : B4 * b + B4 = B4 * (b + 1) := by rw [Nat.mul_add, Nat.mul_one]
  have h4 : B4 * (b + 1) ≤ B4 * B := Nat.mul_le_mul_left _ hb
  have h5 : B4 * B = B * (B * (B * (B * B))) := by dsimp only [B4]; ac_rfl
  exact Nat.lt_of_lt_of_le h1 (Nat.le_trans h2 (h3 ▸ h5 ▸ h4))

private theorem drop_high_carry {k B s rhs : Nat} (h : k * B + s = rhs) (hlt : rhs < B) : s = rhs := by
  cases k with
  | zero => simpa using h
  | succ k' =>
    have hge : B ≤ (k' + 1) * B := Nat.le_mul_of_pos_left B (Nat.succ_pos k')
    omega

/-! ## Fragment `wp` lemmas -/

theorem load4K_spec {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {p : BitVec 64} (x0 x1 x2 x3 : BitVec 64) {R : Mem 64 → Prop}
    {k : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Expr Val Cont rs}
    (hm : (array64 p [x0, x1, x2, x3] ⋆ R) m)
    (hk : wp Γ Q X (k x0 x1 x2 x3) m) :
    wp Γ Q X (load4K p k) m := by
  unfold load4K; wp_unfold
  refine ⟨x0, by simpa using loadVal_array64 (i := 0) (by simp) hm, ?_⟩
  refine ⟨x1, by simpa using loadVal_array64 (i := 1) (by simp) hm, ?_⟩
  refine ⟨x2, by simpa using loadVal_array64 (i := 2) (by simp) hm, ?_⟩
  refine ⟨x3, by simpa using loadVal_array64 (i := 3) (by simp) hm, hk⟩

theorem store4K_spec {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {p : BitVec 64} {old : List (BitVec 64)} {x0 x1 x2 x3 : BitVec 64} {R : Mem 64 → Prop}
    {k : Expr Val Cont rs}
    (hlen : old.length = 4) (hm : (array64 p old ⋆ R) m)
    (hk : ∀ m', (array64 p [x0, x1, x2, x3] ⋆ R) m' → wp Γ Q X k m') :
    wp Γ Q X (store4K p x0 x1 x2 x3 k) m := by
  rcases old with _ | ⟨o0, _ | ⟨o1, _ | ⟨o2, _ | ⟨o3, _ | _⟩⟩⟩⟩ <;> simp at hlen
  unfold store4K; wp_unfold
  obtain ⟨ok0, hm0⟩ := store_array64 (i := 0) x0 (by simp) hm
  refine ⟨by simpa using ok0, ?_⟩
  obtain ⟨ok1, hm1⟩ := store_array64 (i := 1) x1 (by simp) hm0
  refine ⟨by simpa using ok1, ?_⟩
  obtain ⟨ok2, hm2⟩ := store_array64 (i := 2) x2 (by simp) hm1
  refine ⟨by simpa using ok2, ?_⟩
  obtain ⟨ok3, hm3⟩ := store_array64 (i := 3) x3 (by simp) hm2
  exact ⟨by simpa using ok3, hk _ (by simpa using hm3)⟩

theorem store8K_spec {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {p : BitVec 64} {old : List (BitVec 64)} {r0 r1 r2 r3 r4 r5 r6 r7 : BitVec 64}
    {R : Mem 64 → Prop} {k : Expr Val Cont rs}
    (hlen : old.length = 8) (hm : (array64 p old ⋆ R) m)
    (hk : ∀ m', (array64 p [r0, r1, r2, r3, r4, r5, r6, r7] ⋆ R) m' → wp Γ Q X k m') :
    wp Γ Q X (store8K p r0 r1 r2 r3 r4 r5 r6 r7 k) m := by
  rcases old with _ | ⟨o0, _ | ⟨o1, _ | ⟨o2, _ | ⟨o3, _ | ⟨o4, _ | ⟨o5, _ | ⟨o6, _ | ⟨o7, _ | _⟩⟩⟩⟩⟩⟩⟩⟩ <;> simp at hlen
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
  unfold mulRow0K
  refine wp_umulw_mk _ _ _ fun r0 h0 hm0 => ?_
  refine wp_umulw_mk _ _ _ fun l1 h1 hm1 => ?_
  refine wp_addc_mk _ _ _ _ fun r1 c0 ha0 => ?_
  refine wp_umulw_mk _ _ _ fun l2 h2 hm2 => ?_
  refine wp_addc_mk _ _ _ _ fun r2 c1 ha1 => ?_
  refine wp_umulw_mk _ _ _ fun l3 h3 hm3 => ?_
  refine wp_addc_mk _ _ _ _ fun r3 c2 ha2 => ?_
  refine wp_addc_mk _ _ _ _ fun r4 c3 ha3 => ?_
  simp only [Arg.val, Bool.toNat_false, Nat.add_zero] at ha0 ha1 ha2 ha3 hm0 hm1 hm2 hm3
  refine hk r0 r1 r2 r3 r4 ?_
  have halg := mulRow0_alg hm0 hm1 hm2 hm3 ha0 ha1 ha2 ha3
  have hA : limbsVal [a0, a1, a2, a3] < 2 ^ 64 * (2 ^ 64 * (2 ^ 64 * 2 ^ 64)) := by
    rw [B4_eq_pow256]; exact limbsVal_lt_pow [a0, a1, a2, a3]
  have hlt : limbsVal [a0, a1, a2, a3] * b0.toNat < 2 ^ 64 * (2 ^ 64 * (2 ^ 64 * (2 ^ 64 * 2 ^ 64))) := by
    simpa using mulRowAcc_bound hA (Nat.mul_pos (Nat.two_pow_pos _) (Nat.mul_pos (Nat.two_pow_pos _)
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
  unfold mulRowAccK
  refine wp_umulw_mk _ _ _ fun l0 h0 hm0 => ?_
  refine wp_addc_mk _ _ _ _ fun o0 cx0 hcx0 => ?_
  refine wp_umulw_mk _ _ _ fun l1 h1 hm1 => ?_
  refine wp_addc_mk _ _ _ _ fun u1 ox0 hox0 => ?_
  refine wp_addc_mk _ _ _ _ fun o1 cx1 hcx1 => ?_
  refine wp_umulw_mk _ _ _ fun l2 h2 hm2 => ?_
  refine wp_addc_mk _ _ _ _ fun u2 ox1 hox1 => ?_
  refine wp_addc_mk _ _ _ _ fun o2 cx2 hcx2 => ?_
  refine wp_umulw_mk _ _ _ fun l3 h3 hm3 => ?_
  refine wp_addc_mk _ _ _ _ fun u3 ox2 hox2 => ?_
  refine wp_addc_mk _ _ _ _ fun o3 cx3 hcx3 => ?_
  refine wp_addc_mk _ _ _ _ fun u4 ox3 hox3 => ?_
  refine wp_addc_mk _ _ _ _ fun o4 cx4 hcx4 => ?_
  simp only [Arg.val, Bool.toNat_false, Nat.add_zero]
    at hm0 hm1 hm2 hm3 hcx0 hox0 hcx1 hox1 hcx2 hox2 hcx3 hox3 hcx4
  refine hk o0 o1 o2 o3 o4 ?_
  have halg := mulRowAcc_alg hm0 hm1 hm2 hm3 hcx0 hox0 hcx1 hox1 hcx2 hox2 hcx3 hox3 hcx4
  have hA : limbsVal [a0, a1, a2, a3] < 2 ^ 64 * (2 ^ 64 * (2 ^ 64 * 2 ^ 64)) := by
    rw [B4_eq_pow256]; exact limbsVal_lt_pow [a0, a1, a2, a3]
  have hacc : limbsVal [acc0, acc1, acc2, acc3] < 2 ^ 64 * (2 ^ 64 * (2 ^ 64 * 2 ^ 64)) := by
    rw [B4_eq_pow256]; exact limbsVal_lt_pow [acc0, acc1, acc2, acc3]
  have hlt := mulRowAcc_bound hA hacc bj.isLt
  rw [limbsVal5_eq, limbsVal4_eq, limbsVal4_eq]
  exact drop_high_carry halg (by simpa [limbsVal4_eq] using hlt)

theorem add4K_spec {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64)
    (k : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Bool → Expr Val Cont rs)
    (hk : ∀ (s0 s1 s2 s3 : BitVec 64) (c3 : Bool),
      c3.toNat * 2 ^ 256 + limbsVal [s0, s1, s2, s3] =
        limbsVal [a0, a1, a2, a3] + limbsVal [b0, b1, b2, b3] →
      wp Γ Q X (k s0 s1 s2 s3 c3) m) :
    wp Γ Q X (add4K a0 a1 a2 a3 b0 b1 b2 b3 k) m := by
  unfold add4K
  refine wp_addc_mk _ _ _ _ fun s0 c0 h0 => ?_
  refine wp_addc_mk _ _ _ _ fun s1 c1 h1 => ?_
  refine wp_addc_mk _ _ _ _ fun s2 c2 h2 => ?_
  refine wp_addc_mk _ _ _ _ fun s3 c3 h3 => ?_
  simp only [Arg.val, Bool.toNat_false, Nat.add_zero] at h0 h1 h2 h3
  refine hk s0 s1 s2 s3 c3 ?_
  have halg := add4_base h0 h1 h2 h3
  rw [B4_eq_pow256] at halg
  simpa [limbsVal4_eq] using halg

theorem sub4K_spec {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64)
    (k : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Bool → Expr Val Cont rs)
    (hk : ∀ (d0 d1 d2 d3 : BitVec 64) (w3 : Bool),
      limbsVal [d0, d1, d2, d3] + limbsVal [b0, b1, b2, b3] =
        limbsVal [a0, a1, a2, a3] + w3.toNat * 2 ^ 256 →
      wp Γ Q X (k d0 d1 d2 d3 w3) m) :
    wp Γ Q X (sub4K a0 a1 a2 a3 b0 b1 b2 b3 k) m := by
  unfold sub4K
  refine wp_subb_mk _ _ _ _ fun d0 w0 h0 => ?_
  refine wp_subb_mk _ _ _ _ fun d1 w1 h1 => ?_
  refine wp_subb_mk _ _ _ _ fun d2 w2 h2 => ?_
  refine wp_subb_mk _ _ _ _ fun d3 w3 h3 => ?_
  simp only [Arg.val, Bool.toNat_false, Nat.add_zero] at h0 h1 h2 h3
  refine hk d0 d1 d2 d3 w3 ?_
  have halg := sub4_base h0 h1 h2 h3
  rw [B4_eq_pow256] at halg
  simpa [limbsVal4_eq] using halg

theorem select4K_spec {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    (c : Bool) (x0 x1 x2 x3 y0 y1 y2 y3 : BitVec 64)
    (k : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Expr Val Cont rs)
    (hk : wp Γ Q X (if c then k x0 x1 x2 x3 else k y0 y1 y2 y3) m) :
    wp Γ Q X (select4K c x0 x1 x2 x3 y0 y1 y2 y3 k) m := by
  unfold select4K; wp_unfold
  cases c <;> exact hk

/-! ## Top-level `wp` correctness proofs -/

private theorem mul4x4_combine {B A b0 b1 b2 b3 r0 r1 r2 t u v w : Nat}
    (e0 : r0 + B * t = A * b0)
    (e1 : r1 + B * u = A * b1 + t)
    (e2 : r2 + B * v = A * b2 + u)
    (e3 : w = A * b3 + v) :
    r0 + B * (r1 + B * (r2 + B * w)) = A * (b0 + B * (b1 + B * (b2 + B * b3))) := by
  calc r0 + B * (r1 + B * (r2 + B * w))
      = r0 + B * (r1 + B * ((r2 + B * v) + B * (A * b3))) := by rw [e3]; simp only [Nat.mul_add]; ac_rfl
    _ = r0 + B * ((r1 + B * u) + B * (A * b2 + B * (A * b3))) := by rw [e2]; simp only [Nat.mul_add]; ac_rfl
    _ = (r0 + B * t) + B * (A * b1 + B * (A * b2 + B * (A * b3))) := by rw [e1]; simp only [Nat.mul_add]; ac_rfl
    _ = A * b0 + B * (A * b1 + B * (A * b2 + B * (A * b3))) := by rw [e0]
    _ = A * (b0 + B * (b1 + B * (b2 + B * b3))) := by
          simp only [Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm B A]

theorem mul4x4_correct (Γ : Env) :
    ∀ args m Q X, mul4x4Spec args m Q X → Func.spec Γ mul4x4 args m Q X := by
  rintro ⟨out, pa, pb, ⟨⟩⟩ m Q X ⟨as, bs, out0, R, has, hbs, hout, hm, hQ⟩
  rcases as with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | _⟩⟩⟩⟩ <;> simp at has
  rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | _⟩⟩⟩⟩ <;> simp at hbs
  dsimp only [Func.spec, Func.wp, mul4x4]
  refine load4K_spec a0 a1 a2 a3 (R := array64 out out0 ⋆ array64 pb [b0, b1, b2, b3] ⋆ R) (sep_ac hm) ?_
  refine load4K_spec b0 b1 b2 b3 (R := array64 out out0 ⋆ array64 pa [a0, a1, a2, a3] ⋆ R) (sep_ac hm) ?_
  refine mulRow0K_spec a0 a1 a2 a3 b0 _ fun r0 t1 t2 t3 t4 hr0 => ?_
  refine mulRowAccK_spec a0 a1 a2 a3 b1 t1 t2 t3 t4 _ fun r1 u2 u3 u4 u5 hr1 => ?_
  refine mulRowAccK_spec a0 a1 a2 a3 b2 u2 u3 u4 u5 _ fun r2 v3 v4 v5 v6 hr2 => ?_
  refine mulRowAccK_spec a0 a1 a2 a3 b3 v3 v4 v5 v6 _ fun r3 r4 r5 r6 r7 hr3 => ?_
  refine store8K_spec hout (R := array64 pa [a0, a1, a2, a3] ⋆ array64 pb [b0, b1, b2, b3] ⋆ R)
    (sep_ac hm) fun m' hm' => ?_
  wp_unfold
  refine hQ [r0, r1, r2, r3, r4, r5, r6, r7] m' rfl ?_ (sep_ac hm')
  have hcomb := mul4x4_combine (B := 2 ^ 64) (A := limbsVal [a0, a1, a2, a3])
    (by simpa [limbsVal] using hr0) (by simpa [limbsVal] using hr1)
    (by simpa [limbsVal] using hr2) hr3
  simpa [limbsVal4_eq, limbsVal] using hcomb

theorem addMod25519_correct (Γ : Env) :
    ∀ args m Q X, addMod25519Spec args m Q X → Func.spec Γ addMod25519 args m Q X := by
  rintro ⟨out, pa, pb, ⟨⟩⟩ m Q X ⟨as, bs, out0, R, has, hbs, hout, hAlt, hBlt, hm, hQ⟩
  rcases as with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | _⟩⟩⟩⟩ <;> simp at has
  rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | _⟩⟩⟩⟩ <;> simp at hbs
  dsimp only [Func.spec, Func.wp, addMod25519]
  refine load4K_spec a0 a1 a2 a3 (R := array64 out out0 ⋆ array64 pb [b0, b1, b2, b3] ⋆ R) (sep_ac hm) ?_
  refine load4K_spec b0 b1 b2 b3 (R := array64 out out0 ⋆ array64 pa [a0, a1, a2, a3] ⋆ R) (sep_ac hm) ?_
  refine add4K_spec a0 a1 a2 a3 b0 b1 b2 b3 _ fun s0 s1 s2 s3 c3 hsum => ?_
  have hSlt : limbsVal [a0, a1, a2, a3] + limbsVal [b0, b1, b2, b3] < 2 ^ 256 := by
    have h2 := two_p25519_lt
    generalize (2 : Nat) ^ 256 = M at h2 ⊢
    generalize p25519 = P at hAlt hBlt h2
    omega
  have hS : limbsVal [s0, s1, s2, s3] = limbsVal [a0, a1, a2, a3] + limbsVal [b0, b1, b2, b3] :=
    drop_high_carry hsum hSlt
  refine wp_subb_mk _ _ _ _ fun d0 w0 hw0 => ?_
  refine wp_subb_mk _ _ _ _ fun d1 w1 hw1 => ?_
  refine wp_subb_mk _ _ _ _ fun d2 w2 hw2 => ?_
  refine wp_subb_mk _ _ _ _ fun d3 w3 hw3 => ?_
  simp only [Arg.val, Bool.toNat_false, Nat.add_zero] at hw0 hw1 hw2 hw3
  have hsub : limbsVal [d0, d1, d2, d3] + p25519 = limbsVal [s0, s1, s2, s3] + w3.toNat * 2 ^ 256 := by
    have h := sub4_base hw0 hw1 hw2 hw3
    rw [B4_eq_pow256] at h
    rw [← limbsVal_p25519, limbsVal4_eq, limbsVal4_eq, limbsVal4_eq]
    exact h
  clear hw0 hw1 hw2 hw3 hsum hSlt
  have hDlt : limbsVal [d0, d1, d2, d3] < 2 ^ 256 := limbsVal4_lt_pow256 d0 d1 d2 d3
  refine select4K_spec w3 s0 s1 s2 s3 d0 d1 d2 d3 _ ?_
  generalize (2 : Nat) ^ 256 = M at hsub hDlt
  generalize p25519 = P at hAlt hBlt hsub hQ
  cases w3
  · simp only [Bool.false_eq_true, ↓reduceIte, Bool.toNat_false, Nat.zero_mul, Nat.add_zero] at hsub ⊢
    refine store4K_spec hout (R := array64 pa [a0, a1, a2, a3] ⋆ array64 pb [b0, b1, b2, b3] ⋆ R)
      (sep_ac hm) fun m' hm' => ?_
    wp_unfold
    have hDltP : limbsVal [d0, d1, d2, d3] < P := by omega
    have hmod : limbsVal [d0, d1, d2, d3] = (limbsVal [a0, a1, a2, a3] + limbsVal [b0, b1, b2, b3]) % P := by
      rw [← hS, ← hsub, Nat.add_mod_right, Nat.mod_eq_of_lt hDltP]
    exact hQ [d0, d1, d2, d3] m' rfl hmod hDltP (sep_ac hm')
  · simp only [↓reduceIte, Bool.toNat_true, Nat.one_mul] at hsub ⊢
    refine store4K_spec hout (R := array64 pa [a0, a1, a2, a3] ⋆ array64 pb [b0, b1, b2, b3] ⋆ R)
      (sep_ac hm) fun m' hm' => ?_
    wp_unfold
    have hSltP : limbsVal [s0, s1, s2, s3] < P := by omega
    have hmod : limbsVal [s0, s1, s2, s3] = (limbsVal [a0, a1, a2, a3] + limbsVal [b0, b1, b2, b3]) % P := by
      rw [← hS, Nat.mod_eq_of_lt hSltP]
    exact hQ [s0, s1, s2, s3] m' rfl hmod hSltP (sep_ac hm')

private theorem subMod_arith {A B D S P M : Nat} {w c : Bool}
    (hA : A < P) (hB : B < P) (hD : D < M) (hS : S < M)
    (hsub : D + B = A + w.toNat * M) (hadd : c.toNat * M + S = D + P) :
    (w = false → D = (if B ≤ A then A - B else A + P - B) ∧ D < P) ∧
    (w = true → S = (if B ≤ A then A - B else A + P - B) ∧ S < P) := by
  constructor
  · intro hw; subst hw
    simp only [Bool.toNat_false, Nat.zero_mul, Nat.add_zero] at hsub
    have hle : B ≤ A := by omega
    simp only [hle, ↓reduceIte]; omega
  · intro hw; subst hw
    simp only [Bool.toNat_true, Nat.one_mul] at hsub
    have hgt : ¬ B ≤ A := by omega
    cases c
    · simp only [Bool.toNat_false, Nat.zero_mul, Nat.zero_add] at hadd; omega
    · simp only [Bool.toNat_true, Nat.one_mul] at hadd
      simp only [hgt, ↓reduceIte]; omega

theorem addImm4K_spec {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    (d0 d1 d2 d3 q0 q1 q2 q3 : BitVec 64)
    (k : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Bool → Expr Val Cont rs)
    (hk : ∀ (s0 s1 s2 s3 : BitVec 64) (c3 : Bool),
      c3.toNat * 2 ^ 256 + limbsVal [s0, s1, s2, s3] =
        limbsVal [d0, d1, d2, d3] + limbsVal [q0, q1, q2, q3] →
      wp Γ Q X (k s0 s1 s2 s3 c3) m) :
    wp Γ Q X (addImm4K d0 d1 d2 d3 q0 q1 q2 q3 k) m := by
  unfold addImm4K
  refine wp_addc_mk _ _ _ _ fun s0 c0 hc0 => ?_
  refine wp_addc_mk _ _ _ _ fun s1 c1 hc1 => ?_
  refine wp_addc_mk _ _ _ _ fun s2 c2 hc2 => ?_
  refine wp_addc_mk _ _ _ _ fun s3 c3 hc3 => ?_
  simp only [Arg.val, Bool.toNat_false, Nat.add_zero] at hc0 hc1 hc2 hc3
  refine hk s0 s1 s2 s3 c3 ?_
  have halg := add4_base hc0 hc1 hc2 hc3
  rw [B4_eq_pow256] at halg
  simpa [limbsVal4_eq] using halg

theorem subMod25519_correct (Γ : Env) :
    ∀ args m Q X, subMod25519Spec args m Q X → Func.spec Γ subMod25519 args m Q X := by
  rintro ⟨out, pa, pb, ⟨⟩⟩ m Q X ⟨as, bs, out0, R, has, hbs, hout, hAlt, hBlt, hm, hQ⟩
  rcases as with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | _⟩⟩⟩⟩ <;> simp at has
  rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | _⟩⟩⟩⟩ <;> simp at hbs
  dsimp only [Func.spec, Func.wp, subMod25519]
  refine load4K_spec a0 a1 a2 a3 (R := array64 out out0 ⋆ array64 pb [b0, b1, b2, b3] ⋆ R) (sep_ac hm) ?_
  refine load4K_spec b0 b1 b2 b3 (R := array64 out out0 ⋆ array64 pa [a0, a1, a2, a3] ⋆ R) (sep_ac hm) ?_
  refine sub4K_spec a0 a1 a2 a3 b0 b1 b2 b3 _ fun d0 d1 d2 d3 w3 hsub => ?_
  refine addImm4K_spec d0 d1 d2 d3 p0 p1 p2 p3 _ fun s0 s1 s2 s3 c3 hadd => ?_
  rw [limbsVal_p25519] at hadd
  have ⟨hf, ht⟩ := subMod_arith hAlt hBlt (limbsVal4_lt_pow256 d0 d1 d2 d3)
    (limbsVal4_lt_pow256 s0 s1 s2 s3) hsub hadd
  refine select4K_spec w3 s0 s1 s2 s3 d0 d1 d2 d3 _ ?_
  cases w3
  · simp only [Bool.false_eq_true, ↓reduceIte]
    refine store4K_spec hout (R := array64 pa [a0, a1, a2, a3] ⋆ array64 pb [b0, b1, b2, b3] ⋆ R)
      (sep_ac hm) fun m' hm' => ?_
    wp_unfold
    exact hQ [d0, d1, d2, d3] m' rfl (hf rfl).1 (hf rfl).2 (sep_ac hm')
  · simp only [↓reduceIte]
    refine store4K_spec hout (R := array64 pa [a0, a1, a2, a3] ⋆ array64 pb [b0, b1, b2, b3] ⋆ R)
      (sep_ac hm) fun m' hm' => ?_
    wp_unfold
    exact hQ [s0, s1, s2, s3] m' rfl (ht rfl).1 (ht rfl).2 (sep_ac hm')

/-! ## 100%-PHOAS `Func.Wf` proofs (no `TFlat`) -/

local macro "wf_ctx_tac" : tactic =>
  `(tactic| (
    repeat (
      first
        | intro _ _
        | exact TRel.nil'
        | apply TRel.cons'
        | ((try dsimp only); exact ArgRel.imm _)
        | ((try dsimp only); refine ArgRel.var ?_; simp [Tup.zip, *])
        | refine Wf.let_ ?_ ?_
        | refine Wf.load _ ?_ ?_
        | refine Wf.store ?_ ?_ ?_
        | refine Wf.ret ?_
        | refine OpRel.mk _ ?_)))

private theorem load4K_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {p₁ : V₁ i64} {p₂ : V₂ i64}
    {k₁ : V₁ i64 → V₁ i64 → V₁ i64 → V₁ i64 → Expr V₁ L₁ rs}
    {k₂ : V₂ i64 → V₂ i64 → V₂ i64 → V₂ i64 → Expr V₂ L₂ rs}
    (hp : ⟨i64, p₁, p₂⟩ ∈ G)
    (hk : ∀ x0₁ x0₂ x1₁ x1₂ x2₁ x2₂ x3₁ x3₂,
      Wf (⟨i64, x3₁, x3₂⟩ :: ⟨i64, x2₁, x2₂⟩ :: ⟨i64, x1₁, x1₂⟩ :: ⟨i64, x0₁, x0₂⟩ :: G) D
        (k₁ x0₁ x1₁ x2₁ x3₁) (k₂ x0₂ x1₂ x2₂ x3₂)) :
    Wf G D (load4K p₁ k₁) (load4K p₂ k₂) := by
  unfold load4K; wf_ctx_tac
  refine (hk _ _ _ _ _ _ _ _).weaken_G fun q hq => by simp [Tup.zip] at hq ⊢; grind

private theorem store4K_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {p₁ x0₁ x1₁ x2₁ x3₁ : V₁ i64} {p₂ x0₂ x1₂ x2₂ x3₂ : V₂ i64}
    {k₁ : Expr V₁ L₁ rs} {k₂ : Expr V₂ L₂ rs}
    (hp : ⟨i64, p₁, p₂⟩ ∈ G) (hx0 : ⟨i64, x0₁, x0₂⟩ ∈ G) (hx1 : ⟨i64, x1₁, x1₂⟩ ∈ G)
    (hx2 : ⟨i64, x2₁, x2₂⟩ ∈ G) (hx3 : ⟨i64, x3₁, x3₂⟩ ∈ G)
    (hk : Wf G D k₁ k₂) : Wf G D (store4K p₁ x0₁ x1₁ x2₁ x3₁ k₁) (store4K p₂ x0₂ x1₂ x2₂ x3₂ k₂) := by
  unfold store4K; wf_ctx_tac
  exact hk.weaken_G fun q hq => by simp [Tup.zip, hq]

private theorem store8K_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
    {p₁ r0₁ r1₁ r2₁ r3₁ r4₁ r5₁ r6₁ r7₁ : V₁ i64} {p₂ r0₂ r1₂ r2₂ r3₂ r4₂ r5₂ r6₂ r7₂ : V₂ i64}
    {k₁ : Expr V₁ L₁ rs} {k₂ : Expr V₂ L₂ rs}
    (hp : ⟨i64, p₁, p₂⟩ ∈ G)
    (hr0 : ⟨i64, r0₁, r0₂⟩ ∈ G) (hr1 : ⟨i64, r1₁, r1₂⟩ ∈ G)
    (hr2 : ⟨i64, r2₁, r2₂⟩ ∈ G) (hr3 : ⟨i64, r3₁, r3₂⟩ ∈ G)
    (hr4 : ⟨i64, r4₁, r4₂⟩ ∈ G) (hr5 : ⟨i64, r5₁, r5₂⟩ ∈ G)
    (hr6 : ⟨i64, r6₁, r6₂⟩ ∈ G) (hr7 : ⟨i64, r7₁, r7₂⟩ ∈ G)
    (hk : Wf G D k₁ k₂) :
    Wf G D (store8K p₁ r0₁ r1₁ r2₁ r3₁ r4₁ r5₁ r6₁ r7₁ k₁)
           (store8K p₂ r0₂ r1₂ r2₂ r3₂ r4₂ r5₂ r6₂ r7₂ k₂) := by
  unfold store8K
  refine store4K_wf hp hr0 hr1 hr2 hr3 ?_
  refine .let_ (.mk _ (.cons (.var hp) (.cons (.imm _) .nil))) fun _ _ => ?_
  refine store4K_wf (by simp [Tup.zip]) (by simp [Tup.zip, hr4]) (by simp [Tup.zip, hr5])
    (by simp [Tup.zip, hr6]) (by simp [Tup.zip, hr7]) (hk.weaken_G fun _ hq => by simp [Tup.zip, hq])

private theorem mulRow0K_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {a0₁ a1₁ a2₁ a3₁ b0₁ : V₁ i64} {a0₂ a1₂ a2₂ a3₂ b0₂ : V₂ i64}
    {k₁ : V₁ i64 → V₁ i64 → V₁ i64 → V₁ i64 → V₁ i64 → Expr V₁ L₁ rs}
    {k₂ : V₂ i64 → V₂ i64 → V₂ i64 → V₂ i64 → V₂ i64 → Expr V₂ L₂ rs}
    (ha0 : ⟨i64, a0₁, a0₂⟩ ∈ G) (ha1 : ⟨i64, a1₁, a1₂⟩ ∈ G)
    (ha2 : ⟨i64, a2₁, a2₂⟩ ∈ G) (ha3 : ⟨i64, a3₁, a3₂⟩ ∈ G) (hb0 : ⟨i64, b0₁, b0₂⟩ ∈ G)
    (hk : ∀ r0₁ r0₂ r1₁ r1₂ r2₁ r2₂ r3₁ r3₂ r4₁ r4₂,
      Wf (⟨i64, r4₁, r4₂⟩ :: ⟨i64, r3₁, r3₂⟩ :: ⟨i64, r2₁, r2₂⟩ :: ⟨i64, r1₁, r1₂⟩ :: ⟨i64, r0₁, r0₂⟩ :: G) D
        (k₁ r0₁ r1₁ r2₁ r3₁ r4₁) (k₂ r0₂ r1₂ r2₂ r3₂ r4₂)) :
    Wf G D (mulRow0K a0₁ a1₁ a2₁ a3₁ b0₁ k₁) (mulRow0K a0₂ a1₂ a2₂ a3₂ b0₂ k₂) := by
  unfold mulRow0K; wf_ctx_tac
  refine (hk _ _ _ _ _ _ _ _ _ _).weaken_G fun q hq => by simp [Tup.zip] at hq ⊢; grind

private theorem mulRowAccK_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
    {a0₁ a1₁ a2₁ a3₁ bj₁ acc0₁ acc1₁ acc2₁ acc3₁ : V₁ i64}
    {a0₂ a1₂ a2₂ a3₂ bj₂ acc0₂ acc1₂ acc2₂ acc3₂ : V₂ i64}
    {k₁ : V₁ i64 → V₁ i64 → V₁ i64 → V₁ i64 → V₁ i64 → Expr V₁ L₁ rs}
    {k₂ : V₂ i64 → V₂ i64 → V₂ i64 → V₂ i64 → V₂ i64 → Expr V₂ L₂ rs}
    (ha0 : ⟨i64, a0₁, a0₂⟩ ∈ G) (ha1 : ⟨i64, a1₁, a1₂⟩ ∈ G)
    (ha2 : ⟨i64, a2₁, a2₂⟩ ∈ G) (ha3 : ⟨i64, a3₁, a3₂⟩ ∈ G) (hbj : ⟨i64, bj₁, bj₂⟩ ∈ G)
    (hc0 : ⟨i64, acc0₁, acc0₂⟩ ∈ G) (hc1 : ⟨i64, acc1₁, acc1₂⟩ ∈ G)
    (hc2 : ⟨i64, acc2₁, acc2₂⟩ ∈ G) (hc3 : ⟨i64, acc3₁, acc3₂⟩ ∈ G)
    (hk : ∀ o0₁ o0₂ o1₁ o1₂ o2₁ o2₂ o3₁ o3₂ o4₁ o4₂,
      Wf (⟨i64, o4₁, o4₂⟩ :: ⟨i64, o3₁, o3₂⟩ :: ⟨i64, o2₁, o2₂⟩ :: ⟨i64, o1₁, o1₂⟩ :: ⟨i64, o0₁, o0₂⟩ :: G) D
        (k₁ o0₁ o1₁ o2₁ o3₁ o4₁) (k₂ o0₂ o1₂ o2₂ o3₂ o4₂)) :
    Wf G D (mulRowAccK a0₁ a1₁ a2₁ a3₁ bj₁ acc0₁ acc1₁ acc2₁ acc3₁ k₁)
           (mulRowAccK a0₂ a1₂ a2₂ a3₂ bj₂ acc0₂ acc1₂ acc2₂ acc3₂ k₂) := by
  unfold mulRowAccK; wf_ctx_tac
  refine (hk _ _ _ _ _ _ _ _ _ _).weaken_G fun q hq => by simp [Tup.zip] at hq ⊢; grind

private theorem add4K_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
    {a0₁ a1₁ a2₁ a3₁ b0₁ b1₁ b2₁ b3₁ : V₁ i64} {a0₂ a1₂ a2₂ a3₂ b0₂ b1₂ b2₂ b3₂ : V₂ i64}
    {k₁ : V₁ i64 → V₁ i64 → V₁ i64 → V₁ i64 → V₁ .bool → Expr V₁ L₁ rs}
    {k₂ : V₂ i64 → V₂ i64 → V₂ i64 → V₂ i64 → V₂ .bool → Expr V₂ L₂ rs}
    (ha0 : ⟨i64, a0₁, a0₂⟩ ∈ G) (ha1 : ⟨i64, a1₁, a1₂⟩ ∈ G)
    (ha2 : ⟨i64, a2₁, a2₂⟩ ∈ G) (ha3 : ⟨i64, a3₁, a3₂⟩ ∈ G)
    (hb0 : ⟨i64, b0₁, b0₂⟩ ∈ G) (hb1 : ⟨i64, b1₁, b1₂⟩ ∈ G)
    (hb2 : ⟨i64, b2₁, b2₂⟩ ∈ G) (hb3 : ⟨i64, b3₁, b3₂⟩ ∈ G)
    (hk : ∀ s0₁ s0₂ s1₁ s1₂ s2₁ s2₂ s3₁ s3₂ c3₁ c3₂,
      Wf (⟨.bool, c3₁, c3₂⟩ :: ⟨i64, s3₁, s3₂⟩ :: ⟨i64, s2₁, s2₂⟩ :: ⟨i64, s1₁, s1₂⟩ :: ⟨i64, s0₁, s0₂⟩ :: G) D
        (k₁ s0₁ s1₁ s2₁ s3₁ c3₁) (k₂ s0₂ s1₂ s2₂ s3₂ c3₂)) :
    Wf G D (add4K a0₁ a1₁ a2₁ a3₁ b0₁ b1₁ b2₁ b3₁ k₁) (add4K a0₂ a1₂ a2₂ a3₂ b0₂ b1₂ b2₂ b3₂ k₂) := by
  unfold add4K; wf_ctx_tac
  refine (hk _ _ _ _ _ _ _ _ _ _).weaken_G fun q hq => by simp [Tup.zip] at hq ⊢; grind

private theorem sub4K_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂}
    {a0₁ a1₁ a2₁ a3₁ b0₁ b1₁ b2₁ b3₁ : V₁ i64} {a0₂ a1₂ a2₂ a3₂ b0₂ b1₂ b2₂ b3₂ : V₂ i64}
    {k₁ : V₁ i64 → V₁ i64 → V₁ i64 → V₁ i64 → V₁ .bool → Expr V₁ L₁ rs}
    {k₂ : V₂ i64 → V₂ i64 → V₂ i64 → V₂ i64 → V₂ .bool → Expr V₂ L₂ rs}
    (ha0 : ⟨i64, a0₁, a0₂⟩ ∈ G) (ha1 : ⟨i64, a1₁, a1₂⟩ ∈ G)
    (ha2 : ⟨i64, a2₁, a2₂⟩ ∈ G) (ha3 : ⟨i64, a3₁, a3₂⟩ ∈ G)
    (hb0 : ⟨i64, b0₁, b0₂⟩ ∈ G) (hb1 : ⟨i64, b1₁, b1₂⟩ ∈ G)
    (hb2 : ⟨i64, b2₁, b2₂⟩ ∈ G) (hb3 : ⟨i64, b3₁, b3₂⟩ ∈ G)
    (hk : ∀ d0₁ d0₂ d1₁ d1₂ d2₁ d2₂ d3₁ d3₂ w3₁ w3₂,
      Wf (⟨.bool, w3₁, w3₂⟩ :: ⟨i64, d3₁, d3₂⟩ :: ⟨i64, d2₁, d2₂⟩ :: ⟨i64, d1₁, d1₂⟩ :: ⟨i64, d0₁, d0₂⟩ :: G) D
        (k₁ d0₁ d1₁ d2₁ d3₁ w3₁) (k₂ d0₂ d1₂ d2₂ d3₂ w3₂)) :
    Wf G D (sub4K a0₁ a1₁ a2₁ a3₁ b0₁ b1₁ b2₁ b3₁ k₁) (sub4K a0₂ a1₂ a2₂ a3₂ b0₂ b1₂ b2₂ b3₂ k₂) := by
  unfold sub4K; wf_ctx_tac
  refine (hk _ _ _ _ _ _ _ _ _ _).weaken_G fun q hq => by simp [Tup.zip] at hq ⊢; grind

theorem mul4x4_wf : Func.Wf mul4x4 := by
  intro V₁ V₂ L₁ L₂ xs₁ xs₂
  dsimp only [mul4x4]
  refine load4K_wf (by simp [Tup.zip]) fun _ _ _ _ _ _ _ _ => ?_
  refine load4K_wf (by simp [Tup.zip]) fun _ _ _ _ _ _ _ _ => ?_
  refine mulRow0K_wf (by simp) (by simp) (by simp) (by simp) (by simp) fun _ _ _ _ _ _ _ _ _ _ => ?_
  refine mulRowAccK_wf (by simp) (by simp) (by simp) (by simp) (by simp)
    (by simp) (by simp) (by simp) (by simp) fun _ _ _ _ _ _ _ _ _ _ => ?_
  refine mulRowAccK_wf (by simp) (by simp) (by simp) (by simp) (by simp)
    (by simp) (by simp) (by simp) (by simp) fun _ _ _ _ _ _ _ _ _ _ => ?_
  refine mulRowAccK_wf (by simp) (by simp) (by simp) (by simp) (by simp)
    (by simp) (by simp) (by simp) (by simp) fun _ _ _ _ _ _ _ _ _ _ => ?_
  refine store8K_wf (by simp [Tup.zip]) (by simp) (by simp) (by simp) (by simp)
    (by simp) (by simp) (by simp) (by simp) (.ret .nil)

theorem addMod25519_wf : Func.Wf addMod25519 := by
  intro V₁ V₂ L₁ L₂ xs₁ xs₂
  dsimp only [addMod25519]
  refine load4K_wf (by simp [Tup.zip]) fun _ _ _ _ _ _ _ _ => ?_
  refine load4K_wf (by simp [Tup.zip]) fun _ _ _ _ _ _ _ _ => ?_
  refine add4K_wf (by simp) (by simp) (by simp) (by simp)
    (by simp) (by simp) (by simp) (by simp) fun _ _ _ _ _ _ _ _ _ _ => ?_
  wf_ctx_tac

theorem subMod25519_wf : Func.Wf subMod25519 := by
  intro V₁ V₂ L₁ L₂ xs₁ xs₂
  dsimp only [subMod25519]
  refine load4K_wf (by simp [Tup.zip]) fun _ _ _ _ _ _ _ _ => ?_
  refine load4K_wf (by simp [Tup.zip]) fun _ _ _ _ _ _ _ _ => ?_
  refine sub4K_wf (by simp) (by simp) (by simp) (by simp)
    (by simp) (by simp) (by simp) (by simp) fun _ _ _ _ _ _ _ _ _ _ => ?_
  wf_ctx_tac


end LeanQbe.T.Examples.Bignum
