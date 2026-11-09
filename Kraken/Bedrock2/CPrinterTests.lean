module

import Kraken.Bedrock2.CPrinter
meta import Kraken.Bedrock2.CPrinter

open Kraken.Bedrock2

private def out (r : Except String String) : IO Unit :=
  match r with
  | .ok s => IO.print s
  | .error e => IO.println s!"error: {e}"

private def modOut (r : Except String String) (testHooks : Bool := false) : IO Unit :=
  match r with
  | .ok s =>
    if s.startsWith (cPrelude testHooks ++ "\n") then
      IO.print (String.ofList (s.toList.drop (cPrelude testHooks ++ "\n").length))
    else IO.println "missing prelude"
  | .error e => IO.println s!"error: {e}"

private def v (x : String) : Expr := .var x
private def lit (n : Int) : Expr := .literal n

private def swap : Func :=
  ⟨["a", "b"], [],
    .seq (.set "t" (.load .eight (v "b")))
      (.seq (.store .eight (v "b") (.load .eight (v "a"))) (.store .eight (v "a") (v "t")))⟩

private def swapSwap : Func :=
  ⟨["a", "b"], [], .seq (.call [] "swap" [v "a", v "b"]) (.call [] "swap" [v "a", v "b"])⟩

/--
info: void swap(br_word_t a, br_word_t b) {
  br_word_t t;
  t = _br_load8(b);
  _br_store8(b, _br_load8(a));
  _br_store8(a, t);
}
-/
#guard_msgs in
#eval out (cFunc "swap" swap)

/--
info: void swap_swap(br_word_t a, br_word_t b);
static void swap(br_word_t a, br_word_t b);

void swap_swap(br_word_t a, br_word_t b) {
  swap(a, b);
  swap(a, b);
}

static void swap(br_word_t a, br_word_t b) {
  br_word_t t;
  t = _br_load8(b);
  _br_store8(b, _br_load8(a));
  _br_store8(a, t);
}
-/
#guard_msgs in
#eval modOut (cModule [("swap_swap", swapSwap)] [("swap", swap)])

/--
info: void swap_swap(br_word_t a, br_word_t b);
void swap(br_word_t a, br_word_t b);

void swap_swap(br_word_t a, br_word_t b) {
  swap(a, b);
  swap(a, b);
}

void swap(br_word_t a, br_word_t b) {
  br_word_t t;
  t = _br_load8(b);
  _br_store8(b, _br_load8(a));
  _br_store8(a, t);
}
-/
#guard_msgs in
#eval modOut (cModule [("swap_swap", swapSwap), ("swap", swap)] [])

#guard (cModule [("swap_swap", swapSwap)] [("swap", swap)]).toOption.any (·.startsWith (cPrelude false))

private def divmod : Func :=
  ⟨["x", "y"], ["q", "r"],
    .seq (.set "q" (.op .divu (v "x") (v "y"))) (.set "r" (.op .remu (v "x") (v "y")))⟩

private def useDivmod : Func :=
  ⟨["x"], ["s"],
    .seq (.call ["a", "b"] "divmod" [v "x", lit 10]) (.set "s" (.op .add (v "a") (v "b")))⟩

/--
info: br_word_t divmod(br_word_t x, br_word_t y, br_word_t* _q) {
  br_word_t q, r;
  q = _br_divu(x, y);
  r = _br_remu(x, y);
  *_q = q;
  return r;
}
-/
#guard_msgs in
#eval out (cFunc "divmod" divmod)

/--
info: br_word_t use_divmod(br_word_t x);
static br_word_t divmod(br_word_t x, br_word_t y, br_word_t* _q);

br_word_t use_divmod(br_word_t x) {
  br_word_t s, a, b;
  b = divmod(x, (br_word_t)10, &a);
  s = a+b;
  return s;
}

static br_word_t divmod(br_word_t x, br_word_t y, br_word_t* _q) {
  br_word_t q, r;
  q = _br_divu(x, y);
  r = _br_remu(x, y);
  *_q = q;
  return r;
}
-/
#guard_msgs in
#eval modOut (cModule [("use_divmod", useDivmod)] [("divmod", divmod)])

private def alloc : Func :=
  ⟨["v"], ["r"],
    .stackalloc "buf" 16
      (.seq (.store .four (v "buf") (v "v")) (.set "r" (.load .two (v "buf"))))⟩

/--
info: br_word_t alloc(br_word_t v) {
  br_word_t r, buf;
  uint8_t _br_stackalloc_buf[16] = {0}; buf = (br_word_t)&_br_stackalloc_buf;
  _br_store4(buf, v);
  r = _br_load2(buf);
  return r;
}
-/
#guard_msgs in
#eval out (cFunc "alloc" alloc)

/--
info: br_word_t alloc(br_word_t v) {
  br_word_t r, buf;
  uint8_t _br_stackalloc_buf[16] = {0}; buf = (br_word_t)&_br_stackalloc_buf;
  _br_test_stackalloc(buf, 16);
  _br_store4(buf, v);
  r = _br_load2(buf);
  return r;
}
-/
#guard_msgs in
#eval out (cFunc "alloc" alloc (testHooks := true))

/--
info: br_word_t alloc(br_word_t v);

br_word_t alloc(br_word_t v) {
  br_word_t r, buf;
  uint8_t _br_stackalloc_buf[16] = {0}; buf = (br_word_t)&_br_stackalloc_buf;
  _br_test_stackalloc(buf, 16);
  _br_store4(buf, v);
  r = _br_load2(buf);
  return r;
}
-/
#guard_msgs in
#eval modOut (cModule [("alloc", alloc)] [] (testHooks := true)) (testHooks := true)

#guard (cPrelude true).endsWith "\nvoid _br_test_stackalloc(br_word_t addr, br_word_t n);\n"

/--
info: br_word_t alloc0(void) {
  br_word_t p;
  uint8_t _br_stackalloc_p[1] = {0}; p = (br_word_t)&_br_stackalloc_p;
  /*skip*/
  return p;
}
-/
#guard_msgs in
#eval out (cFunc "alloc0" ⟨[], ["p"], .stackalloc "p" 0 .skip⟩)

/--
info: 0|(br_word_t)0|x+0|
254|(br_word_t)254|x+254|
0xff|(br_word_t)0xff|x+0xff|
0xffffffffffffffff|(br_word_t)0xffffffffffffffff|x+(br_word_t)0xffffffffffffffff|
5|(br_word_t)5|x+5|
0x123456789abcdef0|(br_word_t)0x123456789abcdef0|x+(br_word_t)0x123456789abcdef0|
0x10e |(br_word_t)0x10e |x+0x10e |
0x80000000|(br_word_t)0x80000000|x+0x80000000|
0x100000000|(br_word_t)0x100000000|x+(br_word_t)0x100000000|
-/
#guard_msgs in
#eval IO.println ("\n".intercalate
  ([0, 0xfe, 0xff, -1, 2 ^ 64 + 5, 0x123456789abcdef0, 2 ^ 100 + 0x10e, 0x80000000, 2 ^ 32].map
    fun n => cLit n ++ "|" ++ cExpr (lit n) ++ "|" ++ cExpr (.op .add (v "x") (lit n)) ++ "|"))

/--
info: x<<0  x>>0  (br_word_t)((br_signed_t)x>>0)
x<<3  x>>3  (br_word_t)((br_signed_t)x>>3)
x<<31  x>>31  (br_word_t)((br_signed_t)x>>31)
x<<((br_word_t)32&(sizeof(br_word_t)*8-1))  x>>((br_word_t)32&(sizeof(br_word_t)*8-1))  (br_word_t)((br_signed_t)x>>((br_word_t)32&(sizeof(br_word_t)*8-1)))
x<<((br_word_t)63&(sizeof(br_word_t)*8-1))  x>>((br_word_t)63&(sizeof(br_word_t)*8-1))  (br_word_t)((br_signed_t)x>>((br_word_t)63&(sizeof(br_word_t)*8-1)))
x<<((br_word_t)0xffffffffffffffff&(sizeof(br_word_t)*8-1))  x>>((br_word_t)0xffffffffffffffff&(sizeof(br_word_t)*8-1))  (br_word_t)((br_signed_t)x>>((br_word_t)0xffffffffffffffff&(sizeof(br_word_t)*8-1)))
x<<3  x>>3  (br_word_t)((br_signed_t)x>>3)
x<<(n&(sizeof(br_word_t)*8-1))  x>>(n&(sizeof(br_word_t)*8-1))  (br_word_t)((br_signed_t)x>>(n&(sizeof(br_word_t)*8-1)))
x<<((n+1)&(sizeof(br_word_t)*8-1))  x>>((n+1)&(sizeof(br_word_t)*8-1))  (br_word_t)((br_signed_t)x>>((n+1)&(sizeof(br_word_t)*8-1)))
-/
#guard_msgs in
#eval IO.println ("\n".intercalate
  ([lit 0, lit 3, lit 31, lit 32, lit 63, lit (-1), lit (2 ^ 64 + 3), v "n", .op .add (v "n") (lit 1)].map
    fun e => cExpr (.op .slu (v "x") e) ++ "  " ++ cExpr (.op .sru (v "x") e) ++ "  " ++
      cExpr (.op .srs (v "x") e)))

/--
info: (br_word_t)3-x
_br_mulhuu(x, (br_word_t)3)
(br_word_t)(x<(br_word_t)3)
(br_word_t)((br_signed_t)x<(br_signed_t)(br_word_t)0xfffffffffffffffd)
(br_word_t)((_br_load1(p))==(br_word_t)0)
~(br_word_t)0
0u-(x^y)
c ? (br_word_t)1 : (x&0xff)
(x|y)*(0u-z)
-/
#guard_msgs in
#eval IO.println ("\n".intercalate
  ([.op .sub (lit 3) (v "x"), .op .mulhuu (v "x") (lit 3), .op .ltu (v "x") (lit 3),
    .op .lts (v "x") (lit (-3)), .op .eq (.load .one (v "p")) (lit 0), .op1 .not (lit 0),
    .op1 .opp (.op .xor (v "x") (v "y")), .ite (v "c") (lit 1) (.op .and (v "x") (lit 0xff)),
    .op .mul (.op .or (v "x") (v "y")) (.op1 .opp (v "z"))].map cExpr))

private def table : Func :=
  ⟨["i"], ["r"],
    .seq (.set "r" (.inlinetable .two [0, 1, 0xfe, 0xff] (v "i")))
      (.set "r" (.op .add (v "r") (.inlinetable .one [7, 8] (lit 1))))⟩

/--
info: br_word_t table(br_word_t i) {
  br_word_t r;
  { static const uint8_t _inlinetable[4] = {0x0, 0x1, 0xfe, 0xff}; r = _br_load2((br_word_t)&_inlinetable[i]); }
  r = r+(({ static const uint8_t _inlinetable[2] = {0x7, 0x8};_br_load1((br_word_t)&_inlinetable[(br_word_t)1]); }));
  return r;
}
-/
#guard_msgs in
#eval out (cFunc "table" table)

/--
info: br_word_t control(br_word_t n) {
  br_word_t acc, tmp;
  acc = (br_word_t)0;
  while (n) {
    if (n&1) {
      acc = acc+n;
    } else {
      // unset tmp
    }
    n = n-1;
    /*skip*/
  }
  return acc;
}
-/
#guard_msgs in
#eval out (cFunc "control" ⟨["n"], ["acc"],
  .seq (.set "acc" (lit 0))
    (.while (v "n")
      (.seq (.cond (.op .and (v "n") (lit 1)) (.set "acc" (.op .add (v "acc") (v "n"))) (.unset "tmp"))
        (.seq (.set "n" (.op .sub (v "n") (lit 1))) .skip)))⟩)

/--
info: br_word_t act(br_word_t x) {
  br_word_t z, y;
  y = MMIOREAD(x, &z);
  return y;
}
-/
#guard_msgs in
#eval out (cFunc "act" ⟨["x"], ["y"], .interact ["z", "y"] "MMIOREAD" [v "x"]⟩)

/--
info: error: invalid identifier 'x y'
-/
#guard_msgs in
#eval out (cFunc "f" ⟨["x y"], [], .skip⟩)
/--
info: error: invalid identifier '1x'
-/
#guard_msgs in
#eval out (cFunc "f" ⟨["1x"], [], .skip⟩)
/--
info: error: invalid identifier ''
-/
#guard_msgs in
#eval out (cFunc "f" ⟨[], [], .set "" (lit 0)⟩)
/--
info: error: invalid identifier 'f g'
-/
#guard_msgs in
#eval out (cFunc "f g" ⟨[], [], .skip⟩)
/--
info: error: reserved identifier 'int'
-/
#guard_msgs in
#eval out (cFunc "f" ⟨["int"], [], .skip⟩)
/--
info: error: reserved identifier 'nullptr'
-/
#guard_msgs in
#eval out (cFunc "f" ⟨[], [], .set "nullptr" (lit 0)⟩)
/--
info: error: reserved identifier 'while'
-/
#guard_msgs in
#eval out (cFunc "while" ⟨[], [], .skip⟩)
/--
info: error: reserved identifier '_br_x'
-/
#guard_msgs in
#eval out (cFunc "f" ⟨[], [], .set "_br_x" (lit 0)⟩)
/--
info: error: reserved identifier '__x'
-/
#guard_msgs in
#eval out (cFunc "f" ⟨[], [], .set "__x" (lit 0)⟩)
/--
info: error: reserved identifier '_X'
-/
#guard_msgs in
#eval out (cFunc "f" ⟨[], [], .set "_X" (lit 0)⟩)
/--
info: error: reserved identifier 'br_word_t'
-/
#guard_msgs in
#eval out (cFunc "f" ⟨[], [], .set "br_word_t" (lit 0)⟩)
/--
info: error: reserved identifier 'UINT64_MAX'
-/
#guard_msgs in
#eval out (cFunc "f" ⟨[], [], .set "UINT64_MAX" (lit 0)⟩)
/--
info: error: reserved identifier '_f'
-/
#guard_msgs in
#eval out (cFunc "_f" ⟨[], [], .skip⟩)
/--
info: error: reserved identifier 'memset'
-/
#guard_msgs in
#eval out (cFunc "memset" ⟨[], [], .skip⟩)
/--
info: error: reserved identifier 'main'
-/
#guard_msgs in
#eval out (cFunc "main" ⟨[], [], .skip⟩)
/--
info: error: reserved identifier '_br_load1'
-/
#guard_msgs in
#eval out (cFunc "f" ⟨[], [], .call [] "_br_load1" []⟩)
/--
info: error: rename_away_from 'a' = '_a' collides
-/
#guard_msgs in
#eval out (cFunc "f" ⟨[], ["a", "b"], .seq (.set "_a" (lit 0)) (.set "b" (v "a"))⟩)
/--
info: error: rename_away_from 'a' = '_a' collides
-/
#guard_msgs in
#eval out (cFunc "f" ⟨["_a"], ["a", "b"], .skip⟩)
/--
info: error: rename_away_from 'Ab': reserved identifier '_Ab'
-/
#guard_msgs in
#eval out (cFunc "f" ⟨[], ["Ab", "b"], .skip⟩)
/--
info: error: rename_away_from 'r' = '_r' collides
-/
#guard_msgs in
#eval out (cFunc "f" ⟨[], ["r", "r", "s"], .skip⟩)
/--
info: error: duplicate parameter 'a' in 'f'
-/
#guard_msgs in
#eval out (cFunc "f" ⟨["a", "a"], [], .skip⟩)
/--
info: error: duplicate stackalloc of 'p' in one block of 'f'
-/
#guard_msgs in
#eval out (cFunc "f" ⟨[], [], .stackalloc "p" 8 (.stackalloc "p" 8 .skip)⟩)
/--
info: void f(void) {
  br_word_t p;
  if ((br_word_t)1) {
    uint8_t _br_stackalloc_p[8] = {0}; p = (br_word_t)&_br_stackalloc_p;
    /*skip*/
  } else {
    uint8_t _br_stackalloc_p[8] = {0}; p = (br_word_t)&_br_stackalloc_p;
    /*skip*/
  }
}
-/
#guard_msgs in
#eval out (cFunc "f" ⟨[], [], .cond (lit 1) (.stackalloc "p" 8 .skip) (.stackalloc "p" 8 .skip)⟩)
/--
info: error: duplicate function 'swap'
-/
#guard_msgs in
#eval out (cModule [("swap", swap)] [("swap", swapSwap)])
/--
info: error: duplicate function 'swap'
-/
#guard_msgs in
#eval out (cModule [("swap", swap), ("swap", swap)] [])
/--
info: error: duplicate function 'f'
-/
#guard_msgs in
#eval out (cModule [("f", ⟨[], [], .skip⟩)] [("f", ⟨[], [], .skip⟩)])
/--
info: error: call to undefined function 'swap' in 'swap_swap'
-/
#guard_msgs in
#eval out (cModule [("swap_swap", swapSwap)] [])
/--
info: error: call to 'swap' in 'swap_swap' has wrong arity
-/
#guard_msgs in
#eval out (cModule [("swap_swap", swapSwap)] [("swap", ⟨["a"], [], .skip⟩)])
/--
info: error: call to 'swap' in 'g' has wrong arity
-/
#guard_msgs in
#eval out (cModule [("g", ⟨["x"], [], .call ["x"] "swap" [v "x", v "x"]⟩)] [("swap", swap)])
/--
info: error: variable 'swap' in 'g' shadows a function
-/
#guard_msgs in
#eval out (cModule [("g", ⟨["swap"], [], .skip⟩)] [("swap", swap)])

/--
info: error: stackalloc of 18446744073709551624 bytes in 'big'
-/
#guard_msgs in
#eval out (cFunc "big" ⟨[], ["p"], .stackalloc "p" (2 ^ 64 + 8) .skip⟩ (testHooks := true))
/--
info: error: stackalloc of 18446744073709551616 bytes in 'big'
-/
#guard_msgs in
#eval out (cModule [("big", ⟨[], ["p"], .seq .skip (.stackalloc "p" 1 (.stackalloc "q" (2 ^ 64) .skip))⟩)] [])
/--
info: br_word_t big(void) {
  br_word_t p;
  uint8_t _br_stackalloc_p[18446744073709551615] = {0}; p = (br_word_t)&_br_stackalloc_p;
  /*skip*/
  return p;
}
-/
#guard_msgs in
#eval out (cFunc "big" ⟨[], ["p"], .stackalloc "p" (2 ^ 64 - 1) .skip⟩)
/--
info: br_word_t big(void) {
  br_word_t p;
  uint8_t _br_stackalloc_p[4294967296] = {0}; p = (br_word_t)&_br_stackalloc_p;
  /*skip*/
  return p;
}
-/
#guard_msgs in
#eval out (cFunc "big" ⟨[], ["p"], .stackalloc "p" (2 ^ 32) .skip⟩)
/--
info: error: interact action 'swap' in 'g' names a function
-/
#guard_msgs in
#eval out (cModule [("g", ⟨["x"], [], .interact [] "swap" [v "x", v "x"]⟩)] [("swap", swap)])
/--
info: error: interact action 'g' in 'g' names a function
-/
#guard_msgs in
#eval out (cModule [("g", ⟨[], [], .interact [] "g" []⟩)] [])
/--
info: error: interact action 'h' in 'g' names a function
-/
#guard_msgs in
#eval out (cModule [("g", ⟨[], [], .interact [] "h" []⟩), ("h", ⟨[], [], .skip⟩)] [])
/--
info: error: variable 'act' in 'f' shadows an interact action
-/
#guard_msgs in
#eval out (cFunc "f" ⟨["act"], [], .interact [] "act" [v "act"]⟩)
/--
info: error: variable 'act' in 'f' shadows an interact action
-/
#guard_msgs in
#eval out (cFunc "f" ⟨[], ["act"], .interact [] "act" []⟩)
/--
info: error: variable 'act' in 'f' shadows an interact action
-/
#guard_msgs in
#eval out (cFunc "f" ⟨[], [], .seq (.interact [] "act" []) (.set "act" (lit 0))⟩)
/--
info: error: variable 'act' in 'f' shadows an interact action
-/
#guard_msgs in
#eval out (cFunc "f" ⟨[], [], .stackalloc "act" 8 (.interact [] "act" [])⟩)
/--
info: error: variable 'act' in 'f' shadows an interact action
-/
#guard_msgs in
#eval out (cFunc "f" ⟨[], [], .interact ["act"] "act" []⟩)
/--
info: error: variable 'act' in 'g' shadows an interact action
-/
#guard_msgs in
#eval out (cModule [("g", ⟨[], [], .while (lit 0) (.interact ["act"] "act" [])⟩)] [])
/--
info: error: inlinetable of length 0 in 'f'
-/
#guard_msgs in
#eval out (cFunc "f" ⟨[], ["r"], .set "r" (.inlinetable .one [] (lit 0))⟩)
/--
info: error: inlinetable of length 0 in 'f'
-/
#guard_msgs in
#eval out (cFunc "f" ⟨[], [], .store .one (lit 0) (.op .add (lit 1) (.inlinetable .one [1] (.inlinetable .one [] (lit 0))))⟩)
/--
info: error: inlinetable of length 0 in 'g'
-/
#guard_msgs in
#eval out (cModule [("g", ⟨["x"], [], .cond (v "x") .skip (.interact [] "act" [.inlinetable .one [] (v "x")])⟩)] [])
/--
info: error: reserved identifier 'CHAR_BIT'
-/
#guard_msgs in
#eval out (cFunc "f" ⟨[], [], .set "CHAR_BIT" (lit 0)⟩)
/--
info: error: reserved external identifier 'free'
-/
#guard_msgs in
#eval out (cModule [("free", ⟨[], [], .skip⟩)] [])
/--
info: error: reserved external identifier 'printf'
-/
#guard_msgs in
#eval out (cModule [("f", ⟨[], [], .skip⟩), ("printf", ⟨[], [], .skip⟩)] [])
/--
info: void f(void);
static void free(void);

void f(void) {
  free();
}

static void free(void) {
  /*skip*/
}
-/
#guard_msgs in
#eval modOut (cModule [("f", ⟨[], [], .call [] "free" []⟩)] [("free", ⟨[], [], .skip⟩)])
/--
info: error: reserved identifier 'memcpy'
-/
#guard_msgs in
#eval out (cModule [("f", ⟨[], [], .skip⟩)] [("memcpy", ⟨[], [], .skip⟩)])
/--
info: error: reserved identifier 'strlen'
-/
#guard_msgs in
#eval out (cModule [("f", ⟨[], [], .skip⟩)] [("strlen", ⟨[], [], .skip⟩)])
/--
info: error: reserved identifier 'memset_explicit'
-/
#guard_msgs in
#eval out (cModule [("f", ⟨[], [], .skip⟩)] [("memset_explicit", ⟨[], [], .skip⟩)])

#guard ["exit", "abort", "malloc", "puts", "time", "signal", "errno", "setjmp", "longjmp", "sqrtf",
    "logd64", "csinl", "d32addd64", "isalpha", "isx", "tolower", "strtol", "memx", "wcslen", "feof",
    "atomic_load", "thrd_create", "cr_exp", "stdc_x", "call_once", "printf_s"].all
  (cExternalNameError? · |>.isSome)
#guard ["f", "is", "is_x", "isX", "to", "to_x", "st", "stx", "atomic_X", "cr", "my_free", "ff",
    "swap", "alloc", "control"].all (cExternalNameError? · |>.isNone)
#guard ["free", "exit", "printf", "time", "sqrt", "isx", "tolower"].all (cIdentError? true · |>.isNone)

/--
info: #include <stdint.h>
#if UINTPTR_MAX != 0xFFFFFFFFu
#error "this module requires 32-bit words"
#endif
-/
#guard_msgs in
#eval out (cWidthGuard 32)
/--
info: #include <stdint.h>
#if UINTPTR_MAX != 0xFFFFFFFFFFFFFFFFu
#error "this module requires 64-bit words"
#endif
-/
#guard_msgs in
#eval out (cWidthGuard 64)
/--
info: error: unsupported word width 48
-/
#guard_msgs in
#eval out (cModuleForWidth 48 [("g", ⟨[], [], .skip⟩)] [])
#guard (cModuleForWidth 64 [("g", ⟨[], [], .skip⟩)] []).toOption ==
  (return (← cWidthGuard 64) ++ (← cModule [("g", ⟨[], [], .skip⟩)] []) : Except String String).toOption
/--
info: error: duplicate function 'g'
-/
#guard_msgs in
#eval out (cModuleForWidth 32 [("g", ⟨[], [], .skip⟩), ("g", ⟨[], [], .skip⟩)] [])
