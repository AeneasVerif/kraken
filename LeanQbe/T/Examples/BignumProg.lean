module

public import LeanQbe.T.Notation

/-!
# Pure AST Definitions for Curve25519 Arithmetic (`BignumProg`)
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Bignum

open LeanQbe.T

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

/-! ## Top-level `Fn` wrappers -/

def mul4x4Fn : Fn := ⟨"mul4x4", [i64, i64, i64], [], mul4x4⟩
def addMod25519Fn : Fn := ⟨"addMod25519", [i64, i64, i64], [], addMod25519⟩
def subMod25519Fn : Fn := ⟨"subMod25519", [i64, i64, i64], [], subMod25519⟩

end LeanQbe.T.Examples.Bignum
