module

import Kraken.Bedrock2.Notation
meta import Kraken.Bedrock2.Notation

open Kraken.Bedrock2

/--
info: bedrock2:(fn swap(a, b) {
    t = load8(b);
    store8(b, load8(a));
    store8(a, t)
  }) : String × Func
-/
#guard_msgs in #check bedrock2:(fn swap(a, b) { t = load8(b); store8(b, load8(a)); store8(a, t) })

/--
info: bedrock2:(fn swap_swap(a, b) {
    swap(a, b);
    swap(a, b)
  }) : String × Func
-/
#guard_msgs in #check bedrock2:(fn swap_swap(a, b) { swap(a, b); swap(a, b) })

/--
info: bedrock2:(fn divmod(x, y) -> (q, r) {
    q = x / y;
    r = x % y
  }) : String × Func
-/
#guard_msgs in #check bedrock2:(fn divmod(x, y) -> (q, r) {
  q = x / y;
  r = x % y
})

/--
info: bedrock2:(fn sum(p, n) -> (s) {
    s = 0;
    i = 0;
    while i < n {
      s = s + load4(p + (i << 2));
      i = i + 1
    }
  }) : String × Func
-/
#guard_msgs in #check bedrock2:(fn sum(p, n) -> (s) {
  s = 0;
  i = 0;
  while i < n {
    s = s + load4(p + (i << 2));
    i = i + 1
  }
})

/--
info: bedrock2:(fn misc(x) -> (y, z) {
    stackalloc 16 as buf {
      store1(buf, x & 255);
      y, z = divmod(load1(buf), 3)
    };
    if x == 0 {
      y = 1
    } else {
      unset z;
      z = -x
    };
    if ~x .< 0 {
      skip
    };
    y = mulhuu(x, x) ^ inlinetable2([1, 2, 3, 4], x & 1) ? 2 : 3;
    interact out(y);
    y = interact read()
  }) : String × Func
-/
#guard_msgs in #check bedrock2:(fn misc(x) -> (y, z) {
  stackalloc 16 as buf {
    store1(buf, x & 0xff);
    y, z = divmod(load1(buf), 3)
  };
  if x == 0 { y = 1 } else { unset z; z = -x };
  if ~x .< 0 { skip };
  y = mulhuu(x, x) ^ inlinetable2([1, 2, 3, 4], x & 1) ? 2 : 3;
  interact out(y);
  y = interact read()
})

#guard bedrock2:(fn swap(a, b) { t = load8(b); store8(b, load8(a)); store8(a, t) }) == ("swap", ⟨["a", "b"], [], .seq (.set "t" (.load .eight (.var "b")))
  (.seq (.store .eight (.var "b") (.load .eight (.var "a"))) (.store .eight (.var "a") (.var "t")))⟩)

#guard bedrock2_expr:(a + b * c - d) == .op .sub (.op .add (.var "a") (.op .mul (.var "b") (.var "c"))) (.var "d")
#guard bedrock2_expr:(a - (b - c)) == .op .sub (.var "a") (.op .sub (.var "b") (.var "c"))
#guard bedrock2_expr:(a & b + c) == .op .and (.var "a") (.op .add (.var "b") (.var "c"))
#guard bedrock2_expr:(x << 2 < n) == .op .ltu (.op .slu (.var "x") (.literal 2)) (.var "n")
#guard bedrock2_expr:(a & b & c) == .op .and (.op .and (.var "a") (.var "b")) (.var "c")
#guard bedrock2_expr:(-a * b) == .op .mul (.op1 .opp (.var "a")) (.var "b")
#guard bedrock2_expr:(a ? b : c ? d : e) == .ite (.var "a") (.var "b") (.ite (.var "c") (.var "d") (.var "e"))

/-- info: bedrock2_expr:((a + b) * c) : Expr -/
#guard_msgs in #check Expr.op .mul (.op .add (.var "a") (.var "b")) (.var "c")

/-- info: bedrock2_expr:(a + (b + c)) : Expr -/
#guard_msgs in #check Expr.op .add (.var "a") (.op .add (.var "b") (.var "c"))

/-- info: bedrock2_expr:((a << 1) + b) : Expr -/
#guard_msgs in #check Expr.op .add (.op .slu (.var "a") (.literal 1)) (.var "b")

/-- info: bedrock2_expr:(a << (1 + b)) : Expr -/
#guard_msgs in #check Expr.op .slu (.var "a") (.op .add (.literal 1) (.var "b"))

/-- info: bedrock2_expr:((a & b) | c) : Expr -/
#guard_msgs in #check Expr.op .or (.op .and (.var "a") (.var "b")) (.var "c")

/-- info: bedrock2_expr:((a & b) == c) : Expr -/
#guard_msgs in #check Expr.op .eq (.op .and (.var "a") (.var "b")) (.var "c")

/-- info: bedrock2_expr:(a & (b == c)) : Expr -/
#guard_msgs in #check Expr.op .and (.var "a") (.op .eq (.var "b") (.var "c"))

/-- info: bedrock2_expr:((a < b) == c) : Expr -/
#guard_msgs in #check Expr.op .eq (.op .ltu (.var "a") (.var "b")) (.var "c")

/-- info: bedrock2_expr:((a ? b : c) + d) : Expr -/
#guard_msgs in #check Expr.op .add (.ite (.var "a") (.var "b") (.var "c")) (.var "d")

/-- info: bedrock2_expr:(-(a + b)) : Expr -/
#guard_msgs in #check Expr.op1 .opp (.op .add (.var "a") (.var "b"))

/-- info: bedrock2_cmd:({
    a = 1;
    b = 2
  };
  c = 3) : Cmd
-/
#guard_msgs in #check Cmd.seq (.seq (.set "a" (.literal 1)) (.set "b" (.literal 2))) (.set "c" (.literal 3))

#guard bedrock2_cmd:({ a = 1; b = 2 }; c = 3) ==
  .seq (.seq (.set "a" (.literal 1)) (.set "b" (.literal 2))) (.set "c" (.literal 3))
#guard bedrock2_expr:((a << 1) + b) == .op .add (.op .slu (.var "a") (.literal 1)) (.var "b")
#guard bedrock2_expr:((a & b) | c) == .op .or (.op .and (.var "a") (.var "b")) (.var "c")
#guard bedrock2_expr:((a ? b : c) + d) == .op .add (.ite (.var "a") (.var "b") (.var "c")) (.var "d")

/-- info: fun x => bedrock2_expr:(%❰x❱ + 1) : Expr → Expr -/
#guard_msgs in #check fun x : Expr => bedrock2_expr:(%❰x❱ + 1)

/-- info: fun x => bedrock2_expr:(%❰Expr.var x❱ + 1) : String → Expr -/
#guard_msgs in #check fun x : String => Expr.op .add (.var x) (.literal 1)

/--
info: fun c =>
  bedrock2_cmd:(while 1 {
      %❰c❱
    }) : Cmd → Cmd
-/
#guard_msgs in #check fun c : Cmd => bedrock2_cmd:(while 1 { %❰c❱ })

/-- info: bedrock2_expr:(%❰Expr.literal (-1)❱ + 1) : Expr -/
#guard_msgs in #check Expr.op .add (.literal (-1)) (.literal 1)

set_option pp.kraken.bedrock2 false in
/-- info: Expr.op BinOp.add (Expr.var "a") (Expr.literal 1) : Expr -/
#guard_msgs in #check bedrock2_expr:(a + 1)

/-- error: precedence differs between Lean and C: add parentheses -/
#guard_msgs in #check bedrock2_expr:(a << 1 + b)

/-- error: precedence differs between Lean and C: add parentheses -/
#guard_msgs in #check bedrock2_expr:(a + b << 1)

/-- error: precedence differs between Lean and C: add parentheses -/
#guard_msgs in #check bedrock2_expr:(a * b << 1)

/--
error: C compilers warn about mixing bitwise operators without parentheses (-Wbitwise-op-parentheses): add parentheses
-/
#guard_msgs in #check bedrock2_expr:(a & b | c)

/-- error: precedence differs between Lean and C: add parentheses -/
#guard_msgs in #check bedrock2_expr:(a ^ b & c)

/-- error: precedence differs between Lean and C: add parentheses -/
#guard_msgs in #check bedrock2_expr:(a & b == c)

/-- error: precedence differs between Lean and C: add parentheses -/
#guard_msgs in #check bedrock2_expr:(a == b & c)

/-- error: bedrock2 identifiers must be atomic -/
#guard_msgs in #check bedrock2_expr:(a.b)

/--
info: bedrock2:(fn swap(a, b) {
    t = load8(b);
    store8(b, load8(a));
    store8(a, t)
  }) : String × Func
-/
#guard_msgs in #check bedrock2:(fn swap(a, b) {
    t = load8(b);
    store8(b, load8(a));
    store8(a, t)
  })

/-- info: [bedrock2_cmd:(skip)] : List Cmd -/
#guard_msgs in #check [Cmd.skip]

/-- info: Cmd.call [] "store8" [bedrock2_expr:(a), bedrock2_expr:(b)] : Cmd -/
#guard_msgs in #check Cmd.call [] "store8" [.var "a", .var "b"]

#guard bedrock2_cmd:(store8(a, b)) == .store .eight (.var "a") (.var "b")
#guard bedrock2_cmd:(x = f(a)) == .call ["x"] "f" [.var "a"]
#guard bedrock2_cmd:(x = f) == .set "x" (.var "f")

/-- error: inlinetable entries must be less than 256 -/
#guard_msgs in #check bedrock2_expr:(inlinetable1([1, 256, 2], 0))

/-- error: inlinetable entries must be less than 256 -/
#guard_msgs in #check bedrock2_expr:(inlinetable8([0x100], 0))

#guard bedrock2_expr:(inlinetable1([0, 255], i)) == .inlinetable .one [0, 255] (.var "i")

/-- info: Expr.inlinetable AccessSize.one [300] bedrock2_expr:(0) : Expr -/
#guard_msgs in #check Expr.inlinetable .one [(300 : UInt8)] (.literal 0)

/-- info: bedrock2_expr:(%❰Expr.inlinetable AccessSize.one [300] (Expr.literal 0)❱ + 1) : Expr -/
#guard_msgs in #check Expr.op .add (.inlinetable .one [(300 : UInt8)] (.literal 0)) (.literal 1)

/-- info: bedrock2_expr:(inlinetable1([255, 0], 0)) : Expr -/
#guard_msgs in #check Expr.inlinetable .one [255, 0] (.literal 0)

/--
info: fun o =>
  bedrock2_expr:(%❰Expr.op1 o
          (Expr.op1 o
            (Expr.op1 o
              (Expr.op1 o
                (Expr.op1 o
                  (Expr.op1 o
                    (Expr.op1 o
                      (Expr.op1 o
                        (Expr.op1 o
                          (Expr.op1 o
                            (Expr.op1 o
                              (Expr.op1 o
                                (Expr.op1 o
                                  (Expr.op1 o
                                    (Expr.op1 o (Expr.op1 o (Expr.op1 Op1.not (Expr.var "x")))))))))))))))))❱ +
      1) : Op1 → Expr
-/
#guard_msgs in #check fun o : Op1 =>
  Expr.op .add (.op1 o (.op1 o (.op1 o (.op1 o (.op1 o (.op1 o (.op1 o (.op1 o (.op1 o (.op1 o (.op1 o
  (.op1 o (.op1 o (.op1 o (.op1 o (.op1 o (.op1 .not (.var "x")))))))))))))))))) (.literal 1)

/--
info: fun o =>
  Expr.op o
    (Expr.op o
      (Expr.op o
        (Expr.op o
          (Expr.op o
            (Expr.op o
              (Expr.op o
                (Expr.op o
                  (Expr.op o
                    (Expr.op o
                      (Expr.op o
                        (Expr.op o
                          (Expr.op o
                            (Expr.op o (Expr.op o (Expr.op o bedrock2_expr:(a) bedrock2_expr:(b)) bedrock2_expr:(b))
                              bedrock2_expr:(b))
                            bedrock2_expr:(b))
                          bedrock2_expr:(b))
                        bedrock2_expr:(b))
                      bedrock2_expr:(b))
                    bedrock2_expr:(b))
                  bedrock2_expr:(b))
                bedrock2_expr:(b))
              bedrock2_expr:(b))
            bedrock2_expr:(b))
          bedrock2_expr:(b))
        bedrock2_expr:(b))
      bedrock2_expr:(b))
    bedrock2_expr:(b) : BinOp → Expr
-/
#guard_msgs in #check fun o : BinOp =>
  Expr.op o (.op o (.op o (.op o (.op o (.op o (.op o (.op o (.op o (.op o (.op o (.op o (.op o
  (.op o (.op o (.op o (.var "a") (.var "b")) (.var "b")) (.var "b")) (.var "b")) (.var "b"))
  (.var "b")) (.var "b")) (.var "b")) (.var "b")) (.var "b")) (.var "b")) (.var "b")) (.var "b"))
  (.var "b")) (.var "b")) (.var "b")

/--
info: fun sz =>
  bedrock2_cmd:(%❰Cmd.store sz (Expr.var "a") (Expr.var "b")❱;
    skip) : AccessSize → Cmd
-/
#guard_msgs in #check fun sz : AccessSize => Cmd.seq (.store sz (.var "a") (.var "b")) .skip

/-- error: 'load1' is reserved in bedrock2 notation and cannot name a function or action -/
#guard_msgs in #check bedrock2_cmd:(load1(a))

/-- error: 'store8' is reserved in bedrock2 notation and cannot name a function or action -/
#guard_msgs in #check bedrock2_cmd:(store8(a, b, c))

/-- error: 'load1' is reserved in bedrock2 notation and cannot name a function or action -/
#guard_msgs in #check bedrock2_cmd:(x, y = load1(a))

/-- error: 'mulhuu' is reserved in bedrock2 notation and cannot name a function or action -/
#guard_msgs in #check bedrock2_cmd:(x = mulhuu(a))

/-- error: 'inlinetable2' is reserved in bedrock2 notation and cannot name a function or action -/
#guard_msgs in #check bedrock2_cmd:(inlinetable2(a))

/-- error: 'skip' is reserved in bedrock2 notation and cannot name a function or action -/
#guard_msgs in #check bedrock2_cmd:(skip())

/-- error: 'load4' is reserved in bedrock2 notation and cannot name a function or action -/
#guard_msgs in #check bedrock2_cmd:(interact load4(a))

/-- error: 'store1' is reserved in bedrock2 notation and cannot name a function or action -/
#guard_msgs in #check bedrock2_cmd:(x = interact store1(a))

#guard bedrock2_cmd:(x = load1(a)) == .set "x" (.load .one (.var "a"))
#guard bedrock2_cmd:(load1 = f(a)) == .call ["load1"] "f" [.var "a"]

/-- info: Cmd.interact [] "load1" [bedrock2_expr:(a)] : Cmd -/
#guard_msgs in #check Cmd.interact [] "load1" [.var "a"]

macro "b2_incr " x:ident : term => `(bedrock2_cmd:($x:ident = $x:ident + 1; y = f($x:ident); z = w))

#guard b2_incr a == .seq (.set "a" (.op .add (.var "a") (.literal 1)))
  (.seq (.call ["y"] "f" [.var "a"]) (.set "z" (.var "w")))

/-- info: bedrock2_expr:(%❰Expr.var "_"❱ + 1) : Expr -/
#guard_msgs in #check Expr.op .add (.var "_") (.literal 1)

/-- info: Cmd.set "_" bedrock2_expr:(1) : Cmd -/
#guard_msgs in #check Cmd.set "_" (.literal 1)

/--
error: C compilers warn about mixing bitwise operators without parentheses (-Wbitwise-op-parentheses): add parentheses
-/
#guard_msgs in #check bedrock2_expr:(a | b & c)

/--
error: C compilers warn about mixing bitwise operators without parentheses (-Wbitwise-op-parentheses): add parentheses
-/
#guard_msgs in #check bedrock2_expr:(a ^ b | c)

/--
error: C compilers warn about mixing bitwise operators without parentheses (-Wbitwise-op-parentheses): add parentheses
-/
#guard_msgs in #check bedrock2_expr:(a & b ^ c)

/-- error: precedence differs between Lean and C: add parentheses -/
#guard_msgs in #check bedrock2_expr:(a ^ b & c)

/-- error: precedence differs between Lean and C: add parentheses -/
#guard_msgs in #check bedrock2_expr:(a | b == c)
