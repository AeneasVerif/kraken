module

public import LeanQbe.T.Notation

/-!
# Pure AST Definitions for Litmus Programs (`LitmusProgsProg`)
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Litmus

open LeanQbe.T
open LeanQbe.T.Notation
/-- The tracer function: `x = a + b; store x, p; ret x`. -/
def tracer : Fn := tqbe $tracer(%a:l, %b:l, %p:l) -> l {
  %x =l add %a, %b
  store l %x, %p
  ret %x
}

/-- `lo32 a ≠ 0 ? a + b : b - a`. -/
def ifelse : Fn := tqbe $ifelse(%a:l, %b:l) -> l {
  %w =w trunc %a
  %c =b cnew %w, 0
  jnz %c, {
    %x =l add %a, %b
    ret %x
  }, {
    %x =l sub %b, %a
    ret %x
  }
}

/-- `1 + 2 + … + n` (for `n < 2^32`). -/
def sumto : Fn := tqbe $sumto(%n:l) -> l {
  loop @loop(%i:l = %n, %s:l = 0) {
    %w =w trunc %i
    %c =b cnew %w, 0
    jnz %c, {
      %s' =l add %s, %i
      %i' =l sub %i, 1
      continue @loop(%i', %s')
    }, {
      ret %s
    }
  }
}

/-- `1` if `n` is even, else `0` (for `n < 2^32`): two mutually recursive join points. -/
def evenodd : Fn := tqbe $evenodd(%n:l) -> l {
  @even(%x:l) {
    %w =w trunc %x
    %c =b cnew %w, 0
    jnz %c, {
      %x' =l sub %x, 1
      jmp @odd(%x')
    }, {
      ret 1
    }
  }
  @odd(%x:l) {
    %w =w trunc %x
    %c =b cnew %w, 0
    jnz %c, {
      %x' =l sub %x, 1
      jmp @even(%x')
    }, {
      ret 0
    }
  }
  {
    jmp @even(%n)
  }
}

/-- `Σ_{i=1..n} Σ_{j=1..m} (k + i)`: `m` and `k` live across both loops,
`i` across the inner one. -/
def nested : Fn := tqbe $nested(%n:l, %m:l, %k:l) -> l {
  loop @outer(%i:l = %n, %t:l = 0) {
    %wi =w trunc %i
    %ci =b cnew %wi, 0
    jnz %ci, {
      loop @inner(%j:l = %m, %u:l = %t) {
        %wj =w trunc %j
        %cj =b cnew %wj, 0
        jnz %cj, {
          %u1 =l add %u, %k
          %u2 =l add %u1, %i
          %j' =l sub %j, 1
          continue @inner(%j', %u2)
        }, {
          %i' =l sub %i, 1
          continue @outer(%i', %u)
        }
      }
    }, {
      ret %t
    }
  }
}

/-- `a` if `n` is even, else `b`: the loop swaps its two parameters (a move cycle). -/
def swap : Fn := tqbe $swap(%n:l, %a:l, %b:l) -> l {
  loop @loop(%i:l = %n, %x:l = %a, %y:l = %b) {
    %w =w trunc %i
    %c =b cnew %w, 0
    jnz %c, {
      %i' =l sub %i, 1
      continue @loop(%i', %y, %x)
    }, {
      ret %x
    }
  }
}

/-- `inc(a) = a + 1` (a leaf callee). -/
def inc : Fn := tqbe $inc(%a:l) -> l {
  %x =l add %a, 1
  ret %x
}

/-- `callinc(a, b) = inc(a) + b`: `b` is live across the call. -/
def callinc : Fn := tqbe $callinc(%a:l, %b:l) -> l {
  %r =l call $inc(%a)
  %x =l add %r, %b
  ret %x
}

/-- `check(a)`: exits to `fail(a)` if the low 32 bits of `a` are zero, else returns `a`. -/
def check : Fn := tqbe $check(%a:l) -> l {
  %w =w trunc %a
  %c =b cnew %w, 0
  jnz %c, {
    ret %a
  }, {
    exit $fail(%a)
  }
}

/-- `twice(a, b) = check(a) + check(b)`: an exit in either call propagates. -/
def twice : Fn := tqbe $twice(%a:l, %b:l) -> l {
  %x =l call $check(%a)
  %y =l call $check(%b)
  %z =l add %x, %y
  ret %z
}

/-- Ten values live at once, plus `b`: `spill10(a, b) = (a+1) ^ (a+2) ^ … ^ (a+10) ^ b`. -/
def spill10 : Fn := tqbe $spill10(%a:l, %b:l) -> l {
  %x1 =l add %a, 1
  %x2 =l add %a, 2
  %x3 =l add %a, 3
  %x4 =l add %a, 4
  %x5 =l add %a, 5
  %x6 =l add %a, 6
  %x7 =l add %a, 7
  %x8 =l add %a, 8
  %x9 =l add %a, 9
  %x10 =l add %a, 10
  %y1 =l xor %x1, %x2
  %y2 =l xor %y1, %x3
  %y3 =l xor %y2, %x4
  %y4 =l xor %y3, %x5
  %y5 =l xor %y4, %x6
  %y6 =l xor %y5, %x7
  %y7 =l xor %y6, %x8
  %y8 =l xor %y7, %x9
  %y9 =l xor %y8, %x10
  %y10 =l xor %y9, %b
  ret %y10
}

/-- A loop with a call in its body: `sumcall(n, b) = Σ_{i=1..n} inc(i) + b`. -/
def sumcall : Fn := tqbe $sumcall(%n:l, %b:l) -> l {
  loop @loop(%i:l = %n, %s:l = 0) {
    %w =w trunc %i
    %c =b cnew %w, 0
    jnz %c, {
      %r =l call $inc(%i)
      %s' =l add %s, %r
      %i' =l sub %i, 1
      continue @loop(%i', %s')
    }, {
      %t =l add %s, %b
      ret %t
    }
  }
}

/-- All 12 litmus functions. -/
def allFns : List Fn :=
  [tracer, ifelse, sumto, evenodd, nested, swap, inc, callinc, check, twice, spill10, sumcall]

end LeanQbe.T.Examples.Litmus
