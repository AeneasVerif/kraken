module

public import LeanQbe.T.Notation

/-!
# Pure AST Definitions for ChaCha20 (`ChaChaProg`)
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.ChaCha

open LeanQbe.T

/-! ## 128-bit `v4i32` row-SIMD PHOAS IR -/

/-- 4-wide vectorized ChaCha quarter round across four `v4i32` rows. -/
def vecQrK {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (a b c d : V v4i32)
    (k : V v4i32 → V v4i32 → V v4i32 → V v4i32 → Expr V L rs) : Expr V L rs :=
  tqbe {
    %a1:v4i32 = add %a, %b
    %d1:v4i32 = xor %d, %a1
    %d2:v4i32 = rotl %d1, splat 16
    %c1:v4i32 = add %c, %d2
    %b1:v4i32 = xor %b, %c1
    %b2:v4i32 = rotl %b1, splat 12
    %a2:v4i32 = add %a1, %b2
    %d3:v4i32 = xor %d2, %a2
    %d4:v4i32 = rotl %d3, splat 8
    %c2:v4i32 = add %c1, %d4
    %b3:v4i32 = xor %b2, %c2
    %b4:v4i32 = rotl %b3, splat 7
    ⟨k a2 b4 c2 d4⟩
  }

/-- One ChaCha20 double round (`inner_block`) on four 128-bit `v4i32` rows using `shufd`
(`0x39` = rotl 1 lane, `0x4e` = rotl 2 lanes, `0x93` = rotl 3 lanes). -/
def doubleRoundK {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (r0 r1 r2 r3 : V v4i32)
    (k : V v4i32 → V v4i32 → V v4i32 → V v4i32 → Expr V L rs) : Expr V L rs :=
  tqbe {
    %c0:v4i32, %c1:v4i32, %c2:v4i32, %c3:v4i32 <- vecQrK(%r0, %r1, %r2, %r3)
    %s1:v4i32 = shufd %c1, 0x39
    %s2:v4i32 = shufd %c2, 0x4e
    %s3:v4i32 = shufd %c3, 0x93
    %d0:v4i32, %d1:v4i32, %d2:v4i32, %d3:v4i32 <- vecQrK(%c0, %s1, %s2, %s3)
    %u1:v4i32 = shufd %d1, 0x93
    %u2:v4i32 = shufd %d2, 0x4e
    %u3:v4i32 = shufd %d3, 0x39
    ⟨k d0 u1 u2 u3⟩
  }

/-- `chacha20Block(out, inp)`: load 4 `v4i32` rows from `inp`, run 10 double rounds in a loop,
add initial rows back, and store 4 `v4i32` rows to `out`. -/
def chacha20Block : Func [i64, i64] [] :=
  tqbe(%out:l, %inp:l) -> () {
    %i0:v4i32 = load %inp
    %p1:l = add %inp, 16
    %i1:v4i32 = load %p1
    %p2:l = add %inp, 32
    %i2:v4i32 = load %p2
    %p3:l = add %inp, 48
    %i3:v4i32 = load %p3
    loop @lp(%r0:v4i32 = %i0, %r1:v4i32 = %i1, %r2:v4i32 = %i2, %r3:v4i32 = %i3, %cnt:w = 10)
        -> @done(%o0:v4i32, %o1:v4i32, %o2:v4i32, %o3:v4i32) {
      %n0:v4i32, %n1:v4i32, %n2:v4i32, %n3:v4i32 <- doubleRoundK(%r0, %r1, %r2, %r3)
      %cnt1:w = sub %cnt, 1
      %more:b = cnew %cnt1, 0
      jnz %more, continue @lp(%n0, %n1, %n2, %n3, %cnt1), break @done(%n0, %n1, %n2, %n3)
    }
    %f0:v4i32 = add %o0, %i0
    %f1:v4i32 = add %o1, %i1
    %f2:v4i32 = add %o2, %i2
    %f3:v4i32 = add %o3, %i3
    store %f0, %out
    %q1:l = add %out, 16
    store %f1, %q1
    %q2:l = add %out, 32
    store %f2, %q2
    %q3:l = add %out, 48
    store %f3, %q3
    ret
  }

/-! ## Top-level `Fn` wrapper -/

def chacha20Fn : Fn := ⟨"chacha20Block", [i64, i64], [], chacha20Block⟩

end LeanQbe.T.Examples.ChaCha
