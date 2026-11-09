module

public import Kraken.Bedrock2.Syntax
public import Kraken.Bedrock2.Test.Examples.Swap
public import Kraken.Bedrock2.Test.Examples.SetBytes
public import Kraken.Bedrock2.Test.Examples.Stackalloc
public import Kraken.Bedrock2.Test.Examples.StackSlotReuse
import Kraken.Bedrock2.Notation
meta import Kraken.Bedrock2.Notation

@[expose] public section

namespace Kraken.Bedrock2.Test

inductive Arg
  | word (v : Int)
  | buf (bytes : List UInt8)
  deriving Repr, Inhabited

structure Case where
  name : String
  funcs : List (String × Func)
  funcsAt : Nat → List (String × Func) := fun _ => funcs
  entry : String
  args : List Arg
  fuel : Nat := 100000
  deriving Inhabited

def Case.buffers (c : Case) : List (List UInt8) :=
  c.args.filterMap fun | .buf bs => some bs | .word _ => none

def bytesOf (n : Nat) (f : Nat → Nat) : List UInt8 :=
  (List.range n).map fun i => (f i).toUInt8

def sum := bedrock2:(fn sum(p, n) -> (s) {
  s = 0;
  i = 0;
  while i < n {
    s = s + load4(p + (i << 2));
    i = i + 1
  }
})

def stackNested := bedrock2:(fn stack_nested(x) -> (r) {
  stackalloc 8 as a {
    store8(a, x);
    stackalloc 4 as b {
      store4(b, load4(a) + 1);
      r = load4(b) * 3 + load1(a + 7)
    }
  }
})

def stackLoop := bedrock2:(fn stack_loop(n) -> (s) {
  s = 0;
  i = 0;
  while i < n {
    stackalloc 4 as t {
      store4(t, i * i);
      s = s + load4(t)
    };
    i = i + 1
  }
})

def divmod := bedrock2:(fn divmod(x, y) -> (q, r) {
  q = x / y;
  r = x % y
})

def useDivmod := bedrock2:(fn use_divmod(x, y) -> (s, t) {
  q, r = divmod(x, y);
  s = q * 1000 + r;
  t = r
})

def shifts := bedrock2:(fn shifts(x, n) -> (a, b, c, d, e, f, g, h) {
  a = x << n;
  b = x >> n;
  c = x .>> n;
  d = x << 40;
  e = x .>> 63;
  f = x >> 100;
  g = x << (n + 32);
  h = 1 << 31
})

def divZero := bedrock2:(fn div_zero(x, z) -> (a, b, c, d) {
  a = x / 0;
  b = x % 0;
  c = x / z;
  d = x % z
})

def mulh := bedrock2:(fn mulh(x, y) -> (h, l) {
  h = mulhuu(x, y);
  l = x * y
})

def wide := bedrock2:(fn wide(p, q) -> (r) {
  x = load8(p);
  store8(q, x);
  store8(p + 8, -x);
  r = load8(q) == x
})

def table := bedrock2:(fn table(i) -> (a, b, c) {
  a = inlinetable1([3, 1, 4, 1, 5, 9, 2, 6], i);
  b = inlinetable2([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16], i << 1);
  c = inlinetable4([0xff, 0, 0, 0x80, 1, 2, 3, 4], (i & 1) << 2) +
    inlinetable8([1, 2, 3, 4, 5, 6, 7, 0xf8, 9, 10, 11, 12, 13, 14, 15, 16], (i & 1) << 3)
})

def absdiff := bedrock2:(fn absdiff(x, y) -> (r, s) {
  r = x < y ? y - x : x - y;
  s = x == y ? 7 : x .< y ? 8 : 9
})

def signed := bedrock2:(fn signed_ops(x, y) -> (a, b, c, d, e) {
  a = x .< y;
  b = x < y;
  c = x .>> 3;
  d = -x .< 0;
  e = ~x .>> y
})

def fib := bedrock2:(fn fib(n) -> (r) {
  if n < 2 {
    r = n
  } else {
    a = fib(n - 1);
    b = fib(n - 2);
    r = a + b
  }
})

def cases : List Case := [
  { name := "swap", funcs := [Examples.swap 64], funcsAt := fun w => [Examples.swap w],
    entry := "swap", args := [.buf (bytesOf 8 (· + 1)), .buf (bytesOf 8 (· + 0xf0))] },
  { name := "swap_swap", funcs := [Examples.swap_swap, Examples.swap 64],
    funcsAt := fun w => [Examples.swap_swap, Examples.swap w], entry := "swap_swap",
    args := [.buf (bytesOf 8 (· * 3)), .buf (bytesOf 8 (255 - ·))] },
  { name := "sum", funcs := [sum], entry := "sum",
    args := [.buf (bytesOf 32 (· * 37 + 200)), .word 8] },
  { name := "sum_empty", funcs := [sum], entry := "sum", args := [.buf [], .word 0] },
  { name := "set_bytes", funcs := [Examples.set_bytes], entry := "set_bytes",
    args := [.buf (bytesOf 13 id), .word 11, .word 0x1ab] },
  { name := "set_bytes_empty", funcs := [Examples.set_bytes], entry := "set_bytes",
    args := [.buf [], .word 0, .word 7] },
  { name := "stackalloc_set_bytes", funcs := [Examples.stackalloc_set_bytes, Examples.set_bytes],
    entry := "stackalloc_set_bytes", args := [.word 0x5c] },
  { name := "stackalloc_set_bytes_wide",
    funcs := [Examples.stackalloc_set_bytes, Examples.set_bytes],
    entry := "stackalloc_set_bytes", args := [.word 0xfedcba9876543210] },
  { name := "stack_nested", funcs := [stackNested], entry := "stack_nested",
    args := [.word 0x8070605040302010] },
  { name := "stack_loop", funcs := [stackLoop], entry := "stack_loop", args := [.word 10] },
  { name := "divmod", funcs := [divmod], entry := "divmod", args := [.word 1234567, .word 1000] },
  { name := "use_divmod", funcs := [useDivmod, divmod], entry := "use_divmod",
    args := [.word 987654321, .word 77] },
  { name := "shifts", funcs := [shifts], entry := "shifts",
    args := [.word 0x8000000000000081, .word 37] },
  { name := "shifts_big", funcs := [shifts], entry := "shifts",
    args := [.word 0xdeadbeefcafef00d, .word (-1)] },
  { name := "div_zero", funcs := [divZero], entry := "div_zero", args := [.word 12345, .word 0] },
  { name := "mulh", funcs := [mulh], entry := "mulh",
    args := [.word 0xfedcba9876543210, .word 0x0123456789abcdef] },
  { name := "mulh_max", funcs := [mulh], entry := "mulh", args := [.word (-1), .word (-1)] },
  { name := "wide", funcs := [wide], entry := "wide",
    args := [.buf (bytesOf 16 (0xf0 + ·)), .buf (bytesOf 8 (fun _ => 0x11))] },
  { name := "table", funcs := [table], entry := "table", args := [.word 3] },
  { name := "table0", funcs := [table], entry := "table", args := [.word 0] },
  { name := "absdiff", funcs := [absdiff], entry := "absdiff", args := [.word 5, .word (-3)] },
  { name := "absdiff_eq", funcs := [absdiff], entry := "absdiff", args := [.word 9, .word 9] },
  { name := "signed", funcs := [signed], entry := "signed_ops", args := [.word (-100), .word 7] },
  { name := "signed_var_shift", funcs := [signed], entry := "signed_ops",
    args := [.word 0x7fffffff, .word 0x123] },
  { name := "fib", funcs := [fib], entry := "fib", args := [.word 15] },
  { name := "same_slot", funcs := [Examples.same_slot, Examples.addrs], entry := "same_slot",
    args := [] }
]

end Kraken.Bedrock2.Test
