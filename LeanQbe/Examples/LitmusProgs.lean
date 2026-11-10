module

public import LeanQbe.IL

/-!
# Litmus programs (generic: no architecture imported)

The source programs of the litmus tests, shared by the x64 (`LeanQbe/Examples/Litmus*.lean`) and
AArch64 (`LeanQbe/Arm64/Litmus*.lean`) instances: the tracer (plan step 1), and the control-flow
programs of step 2a: if/else, a counting loop, an even/odd group of two mutually recursive join
points, nested loops with values live across both loops, and a loop that swaps its parameters
(a parallel-move cycle).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.Litmus

/-- The tracer function (plan step 1): `x = add a b; storel x, p; ret x`. -/
def tracer : Fn where
  name := "tracer"
  body := fun _ _ =>
    .param fun a => .param fun b => .param fun p =>
    .let_ (.bin .l .add (.var a) (.var b)) fun x =>
    .store .l (.var x) (.var p) (.ret [.var x])

/-- `a ≠ 0 ? a + b : b - a` (`jnz` tests the low 32 bits). -/
def ifelse : Fn where
  name := "ifelse"
  body := fun _ _ => .param fun a => .param fun b =>
    .jnz (.var a)
      (.let_ (.bin .l .add (.var a) (.var b)) fun x => .ret [.var x])
      (.let_ (.bin .l .sub (.var b) (.var a)) fun x => .ret [.var x])

/-- `1 + 2 + … + n` (for `n < 2^32`). -/
def sumto : Fn where
  name := "sumto"
  body := fun _ _ => .param fun n =>
    .label fun loop =>
    .block (.param fun i => .param fun s =>
        .jnz (.var i)
          (.let_ (.bin .l .add (.var s) (.var i)) fun s' =>
           .let_ (.bin .l .sub (.var i) (.imm 1)) fun i' =>
           .jump loop [.var i', .var s'])
          (.ret [.var s]))
      (.jump loop [.var n, .imm 0])

/-- `1` if `n` is even, else `0` (for `n < 2^32`): two mutually recursive join points. -/
def evenodd : Fn where
  name := "evenodd"
  body := fun _ _ => .param fun n =>
    .label fun even => .label fun odd =>
    .block (.param fun x =>
        .jnz (.var x) (.let_ (.bin .l .sub (.var x) (.imm 1)) fun x' => .jump odd [.var x'])
          (.ret [.imm 1])) <|
    .block (.param fun x =>
        .jnz (.var x) (.let_ (.bin .l .sub (.var x) (.imm 1)) fun x' => .jump even [.var x'])
          (.ret [.imm 0])) <|
    .jump even [.var n]

/-- `Σ_{i=1..n} Σ_{j=1..m} (k + i)`: `m` and `k` live across both loops, `i` across the inner one. -/
def nested : Fn where
  name := "nested"
  body := fun _ _ => .param fun n => .param fun m => .param fun k =>
    .label fun outer =>
    .block (.param fun i => .param fun t =>
        .jnz (.var i)
          (.label fun inner =>
           .block (.param fun j => .param fun u =>
               .jnz (.var j)
                 (.let_ (.bin .l .add (.var u) (.var k)) fun u1 =>
                  .let_ (.bin .l .add (.var u1) (.var i)) fun u2 =>
                  .let_ (.bin .l .sub (.var j) (.imm 1)) fun j' =>
                  .jump inner [.var j', .var u2])
                 (.let_ (.bin .l .sub (.var i) (.imm 1)) fun i' =>
                  .jump outer [.var i', .var u]))
             (.jump inner [.var m, .var t]))
          (.ret [.var t]))
      (.jump outer [.var n, .imm 0])

/-- `a` if `n` is even, else `b`: the loop swaps its two parameters (a move cycle). -/
def swap : Fn where
  name := "swap"
  body := fun _ _ => .param fun n => .param fun a => .param fun b =>
    .label fun loop =>
    .block (.param fun i => .param fun x => .param fun y =>
        .jnz (.var i)
          (.let_ (.bin .l .sub (.var i) (.imm 1)) fun i' => .jump loop [.var i', .var y, .var x])
          (.ret [.var x]))
      (.jump loop [.var n, .var a, .var b])

/-! ## Calls, exits, spills (plan step 3) -/

/-- `inc(a) = a + 1` (a leaf callee). -/
def inc : Fn where
  name := "inc"
  body := fun _ _ => .param fun a => .let_ (.bin .l .add (.var a) (.imm 1)) fun x => .ret [.var x]

/-- `callinc(a, b) = inc(a) + b`: `b` is live across the call. -/
def callinc : Fn where
  name := "callinc"
  body := fun _ _ => .param fun a => .param fun b =>
    .call "inc" [.var a] <| .param fun r =>
    .let_ (.bin .l .add (.var r) (.var b)) fun x => .ret [.var x]

/-- `check(a)`: exits to `fail(a)` if the low 32 bits of `a` are zero, else returns `a`. -/
def check : Fn where
  name := "check"
  body := fun _ _ => .param fun a => .jnz (.var a) (.ret [.var a]) (.exit "fail" [.var a])

/-- `twice(a, b) = check(a) + check(b)`: an exit in either call propagates. -/
def twice : Fn where
  name := "twice"
  body := fun _ _ => .param fun a => .param fun b =>
    .call "check" [.var a] <| .param fun x =>
    .call "check" [.var b] <| .param fun y =>
    .let_ (.bin .l .add (.var x) (.var y)) fun z => .ret [.var z]

/-- Ten values live at once (more than x64's seven allocatable registers), plus `b`:
`spill10(a, b) = (a+1) ^ (a+2) ^ … ^ (a+10) ^ b` with every `a+i` computed before the first `^`. -/
def spill10 : Fn where
  name := "spill10"
  body := fun _ _ => .param fun a => .param fun b =>
    .let_ (.bin .l .add (.var a) (.imm 1)) fun x1 =>
    .let_ (.bin .l .add (.var a) (.imm 2)) fun x2 =>
    .let_ (.bin .l .add (.var a) (.imm 3)) fun x3 =>
    .let_ (.bin .l .add (.var a) (.imm 4)) fun x4 =>
    .let_ (.bin .l .add (.var a) (.imm 5)) fun x5 =>
    .let_ (.bin .l .add (.var a) (.imm 6)) fun x6 =>
    .let_ (.bin .l .add (.var a) (.imm 7)) fun x7 =>
    .let_ (.bin .l .add (.var a) (.imm 8)) fun x8 =>
    .let_ (.bin .l .add (.var a) (.imm 9)) fun x9 =>
    .let_ (.bin .l .add (.var a) (.imm 10)) fun x10 =>
    .let_ (.bin .l .xor (.var x1) (.var x2)) fun y1 =>
    .let_ (.bin .l .xor (.var y1) (.var x3)) fun y2 =>
    .let_ (.bin .l .xor (.var y2) (.var x4)) fun y3 =>
    .let_ (.bin .l .xor (.var y3) (.var x5)) fun y4 =>
    .let_ (.bin .l .xor (.var y4) (.var x6)) fun y5 =>
    .let_ (.bin .l .xor (.var y5) (.var x7)) fun y6 =>
    .let_ (.bin .l .xor (.var y6) (.var x8)) fun y7 =>
    .let_ (.bin .l .xor (.var y7) (.var x9)) fun y8 =>
    .let_ (.bin .l .xor (.var y8) (.var x10)) fun y9 =>
    .let_ (.bin .l .xor (.var y9) (.var b)) fun y10 =>
    .ret [.var y10]

/-- A loop with a call in its body: `sumcall(n, b) = Σ_{i=1..n} inc(i) + b` (`b` and the running sum
live across the call). -/
def sumcall : Fn where
  name := "sumcall"
  body := fun _ _ => .param fun n => .param fun b =>
    .label fun loop =>
    .block (.param fun i => .param fun s =>
        .jnz (.var i)
          (.call "inc" [.var i] <| .param fun r =>
           .let_ (.bin .l .add (.var s) (.var r)) fun s' =>
           .let_ (.bin .l .sub (.var i) (.imm 1)) fun i' =>
           .jump loop [.var i', .var s'])
          (.let_ (.bin .l .add (.var s) (.var b)) fun t => .ret [.var t]))
      (.jump loop [.var n, .imm 0])

end LeanQbe.Litmus
